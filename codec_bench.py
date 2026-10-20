#!/usr/bin/env python3
"""codec_bench: measure ClickHouse column codecs on a sample of a MergeTree table. See SPEC.md.

Phase 0 (dry run), Phase 1 (sample table), Phase 2 per column: sizes, read and write benchmark and (optional)
stability check, Phase 3: markdown report on stdout.
"""
import argparse
import math
import os
import re
import secrets
import signal
import statistics
import sys
import time

PREFIX = "_codec_bench_"
SCRATCH_NAME = re.compile(r"^_codec_bench_[0-9a-z_]+$")
HASH_BUCKETS = 1_000_000
SCRATCH_DB_ENGINES = ("Atomic", "Ordinary")  # Replicated/Shared would copy every CREATE to other nodes
# CREATE only: relax checks the source table already passed
CREATE_SETTINGS = {s: 1 for s in ("allow_suspicious_low_cardinality_types", "allow_suspicious_fixed_string_types",
                                  "allow_suspicious_variant_types", "allow_suspicious_primary_key",
                                  "allow_suspicious_codecs")}
WIDE_PARTS = ["min_bytes_for_wide_part = 0", "min_rows_for_wide_part = 0"]

GENERAL = ["NONE", "LZ4", "LZ4HC(3)", "LZ4HC(9)", "LZ4HC(12)",
           "ZSTD(1)", "ZSTD(3)", "ZSTD(6)", "ZSTD(9)", "ZSTD(15)", "ZSTD(19)"]
INT_PRE = ["Delta", "DoubleDelta", "GCD", "T64", "GCD, Delta", "Gorilla"]
FLOAT_PRE = ["Gorilla", "FPC(4)", "FPC(12)", "FPC(20)", "Delta"]

INT_TYPES = re.compile(r"^(U?Int(8|16|32|64|128|256)|Bool|Date|Date32|DateTime|DateTime64|Decimal\d*|Enum8|Enum16|IPv4)$")
FLOAT_TYPES = re.compile(r"^(Float32|Float64|BFloat16)$")

VARIANT = "__cb_v{}"  # variant columns in a column table; v0 = the column as declared
# Phase 2 fill: ~80 copies of one column per block, so keep blocks small
FILL_SETTINGS = {"max_block_size": 65536, "max_insert_block_size": 65536, "min_insert_block_size_rows": 65536,
                 "min_insert_block_size_bytes": 64 * 1024 ** 2, "max_partitions_per_insert_block": 0}
# Server errors that stop the whole run instead of skipping one column
FATAL_CODES = {243: "NOT_ENOUGH_SPACE", 394: "QUERY_WAS_CANCELLED"}
COLUMN_SIZES = ("SELECT name, compression_codec, data_compressed_bytes AS compressed, "
                "data_uncompressed_bytes AS uncompressed FROM system.columns "
                "WHERE database = {db:String} AND table = {t:String}")

# Read benchmark: one thread, no caches above the OS page cache, every run logged (also the fast ones)
READ_SETTINGS = {"max_threads": 1, "use_uncompressed_cache": 0, "use_query_cache": 0, "log_queries": 1,
                 "log_queries_min_type": "QUERY_FINISH", "log_queries_min_query_duration_ms": 0}
# Write benchmark: one block = one part per INSERT, so every codec gets the whole column in one go
ONE_BLOCK = {"max_insert_block_size": 10 ** 9, "min_insert_block_size_rows": 10 ** 9,
             "min_insert_block_size_bytes": 10 ** 12}
WRITE_SETTINGS = {**READ_SETTINGS, "max_insert_threads": 1, **ONE_BLOCK}
WRITE_COL = "__cb_w"  # the only column of the write benchmark tables
WRITE_SLOW_S = 10     # a codec whose warm-up INSERT takes longer is measured once (the warm-up is its run)
# cpu: user + system time of all query threads (Linux only, per-thread rusage);
# wall: query start to finish, µs resolution, always there
QUERY_TIMES = ("SELECT query_id, dateDiff('microsecond', query_start_time_microseconds, event_time_microseconds) "
               "AS wall_us, ProfileEvents['UserTimeMicroseconds'] + ProfileEvents['SystemTimeMicroseconds'] AS cpu_us "
               "FROM system.query_log WHERE event_date >= yesterday() AND type = 'QueryFinish' "
               "AND startsWith(query_id, {p:String})")
QUERY_LOG_TIMEOUT = 60  # s; the server flushes query_log every 7.5 s by default
QUERY_TIMEOUT = 3600    # s; server max_execution_time per statement
CLIENT_TIMEOUT = QUERY_TIMEOUT + 300  # s; HTTP read timeout. Single-block INSERTs and OPTIMIZE send nothing
                                      # until done, so it must outlast the server limit
QUERY_LOG_POLL = 2
STABILITY_PP = 2.0          # max shift of "vs smallest" between the two halves, in percentage points
STABILITY_CONTENDER = 10.0  # only codecs within this % of the smallest (in either half) can flag a column

MIN_SERIES = 100
DISK_HEADROOM = 2.0  # merges/OPTIMIZE FINAL temporarily need about double
LOAD_WARN = 0.7      # load1 per CPU


# ---------------------------------------------------------------- logging

def log(msg):
    print(time.strftime("%Y-%m-%d %H:%M:%S"), msg, flush=True)


def human_bytes(n):
    n = float(n)
    for unit in ("B", "KiB", "MiB", "GiB", "TiB"):
        if abs(n) < 1024 or unit == "TiB":
            return f"{n:.1f} {unit}" if unit != "B" else f"{int(n)} B"
        n /= 1024


# ---------------------------------------------------------------- SQL text helpers

def quote_ident(name):
    return "`" + name.replace("\\", "\\\\").replace("`", "\\`") + "`"


def quote_str(s):
    return "'" + s.replace("\\", "\\\\").replace("'", "\\'") + "'"


def _scan(s):
    """Yield (index, char, depth) for characters outside quotes; depth counts () and []."""
    depth, i, n = 0, 0, len(s)
    while i < n:
        c = s[i]
        if c in "'`\"":
            j = i + 1
            while j < n and s[j] != c:
                j += 2 if s[j] == "\\" else 1
            i = j + 1
            continue
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        yield i, c, depth
        i += 1


def split_top_level(s, sep=","):
    """Split on `sep` at bracket depth 0, ignoring quoted text."""
    parts, start = [], 0
    for i, c, depth in _scan(s):
        if c == sep and depth == 0:
            parts.append(s[start:i].strip())
            start = i + 1
    tail = s[start:].strip()
    if tail or parts:
        parts.append(tail)
    return parts


def split_type(t):
    """'Nullable(Float64)' -> ('Nullable', ['Float64']); 'UInt8' -> ('UInt8', [])."""
    t = t.strip()
    p = t.find("(")
    if p < 0 or not t.endswith(")"):
        return t, []
    return t[:p], split_top_level(t[p + 1:-1])


_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*")


def column_refs(expr, column_names):
    """Column names referenced in `expr`, ignoring string literals and function names."""
    names, found = set(column_names), set()
    i, n = 0, len(expr)
    while i < n:
        c = expr[i]
        if c in "'\"":
            j = i + 1
            while j < n and expr[j] != c:
                j += 2 if expr[j] == "\\" else 1
            i = j + 1
        elif c == "`":
            j = i + 1
            buf = []
            while j < n and expr[j] != "`":
                if expr[j] == "\\" and j + 1 < n:
                    j += 1
                buf.append(expr[j])
                j += 1
            if "".join(buf) in names:
                found.add("".join(buf))
            i = j + 1
        else:
            m = _IDENT.match(expr, i) if (c.isalpha() or c == "_") and (i == 0 or not (expr[i - 1].isalnum() or expr[i - 1] == "_")) else None
            if not m:
                i += 1
                continue
            word, i = m.group(0), m.end()
            if expr[i:].lstrip().startswith("("):
                continue  # function name
            if word in names:
                found.add(word)
            elif word.split(".")[0] in names:  # tuple element access
                found.add(word.split(".")[0])
    return found


# ---------------------------------------------------------------- engine / table

def parse_engine(engine_full):
    """'ReplacingMergeTree(v, d) PARTITION BY ...' -> ('ReplacingMergeTree', ['v', 'd'], 'PARTITION BY ...')."""
    m = re.match(r"\s*(\w+)", engine_full)
    name, rest = m.group(1), engine_full[m.end():]
    args = []
    if rest.startswith("("):
        for i, c, depth in _scan(rest):
            if c == ")" and depth == 0:
                args = split_top_level(rest[1:i])
                rest = rest[i + 1:]
                break
    return name, args, rest.strip()


def engine_supported(table_row):
    engine = table_row["engine"]
    if not engine.endswith("MergeTree"):
        return False, f"engine {engine} is not MergeTree-family"
    return True, ""


def scratch_engine(engine_full):
    """Engine clause for scratch tables: Replicated prefix and its path/replica literals removed."""
    name, args, _ = parse_engine(engine_full)
    if name.startswith("Replicated"):
        name = name[len("Replicated"):]
        if len(args) >= 2 and all(a.startswith("'") for a in args[:2]):
            args = args[2:]
    return f"{name}({', '.join(args)})" if args else name


CLAUSES = ("PARTITION BY", "PRIMARY KEY", "ORDER BY", "SAMPLE BY", "TTL", "SETTINGS")


def parse_clauses(engine_full):
    """{'ORDER BY': '(id, ts)', 'SETTINGS': '...', ...} from engine_full, exactly as the server prints them."""
    marks = []
    for i, c, depth in _scan(engine_full):
        if depth == 0 and c == " ":
            for kw in CLAUSES:
                if engine_full.startswith(f" {kw} ", i):
                    marks.append((i, kw))
    out = {}
    for n, (i, kw) in enumerate(marks):
        end = marks[n + 1][0] if n + 1 < len(marks) else len(engine_full)
        out[kw] = engine_full[i + len(kw) + 2:end].strip()
    return out


def parse_settings(engine_full):
    """['index_granularity = 8192', ...] from the SETTINGS clause of engine_full."""
    return split_top_level(parse_clauses(engine_full).get("SETTINGS", ""))


def tuple_elements(expr):
    """'(a, f(b))' -> ['a', 'f(b)']; 'tuple()' -> []; 'a' -> ['a']."""
    expr = expr.strip()
    if expr in ("", "tuple()"):
        return []
    if expr.startswith("("):
        for i, c, depth in _scan(expr):
            if c == ")" and depth == 0:
                if i == len(expr) - 1:
                    return split_top_level(expr[1:-1])
                break
    return [expr]


def default_series_key(order_by, column_names):
    """Drop the last ORDER BY element, then trailing elements that only reference dropped columns.

    `order_by` is the ORDER BY clause as written (from engine_full), not system.tables.sorting_key:
    the latter has the version column of VersionedCollapsingMergeTree appended."""
    elems = tuple_elements(order_by)
    if not elems:
        return []
    dropped = set(column_refs(elems[-1], column_names))
    key = elems[:-1]
    while key:
        refs = column_refs(key[-1], column_names)
        if refs and refs <= dropped:
            dropped |= refs
            key.pop()
        else:
            break
    return key or elems[:1]


# ---------------------------------------------------------------- columns / codecs

def base_type(t):
    """Innermost stored type: unwrap Nullable, LowCardinality, Array, SimpleAggregateFunction."""
    while True:
        name, args = split_type(t)
        if name in ("Nullable", "LowCardinality", "Array") and args:
            t = args[0]
        elif name == "SimpleAggregateFunction" and len(args) == 2:
            t = args[1]
        else:
            return name


def type_class(t):
    b = base_type(t)
    if INT_TYPES.match(b):
        return "int"
    if FLOAT_TYPES.match(b):
        return "float"
    return "other"


def codec_candidates(t):
    """Codec chains to try for a column type. The server decides validity in the real run."""
    pre = {"int": INT_PRE, "float": FLOAT_PRE}.get(type_class(t), [])
    out = list(GENERAL)
    for p in pre:
        out.append(p)
        out += [f"{p}, {g}" for g in GENERAL if g != "NONE"]
    return out


def benchable(col):
    """(True, '') if the column stores data and can carry a codec."""
    if col["default_kind"] in ("ALIAS", "EPHEMERAL"):
        return False, f"{col['default_kind']} column, not stored"
    return True, ""


def select_columns(cols, wanted=None):
    """-> (bench, skipped [(name, reason)], unknown names)."""
    by_name = {c["name"]: c for c in cols}
    names = wanted if wanted else [c["name"] for c in cols]
    unknown = [n for n in names if n not in by_name]
    bench, skipped = [], []
    for n in names:
        if n in by_name:
            ok, why = benchable(by_name[n])
            (bench.append(by_name[n]) if ok else skipped.append((n, why)))
    return bench, skipped, unknown


# ---------------------------------------------------------------- estimates

def estimate_rows(explain_rows):
    return sum(int(r["rows"]) for r in explain_rows)


def sample_fraction(max_rows, scan_rows):
    return 1.0 if scan_rows <= max_rows else max_rows / scan_rows


def free_bytes(policy_rows, disk_rows):
    """Free space on the first volume of the table's policy: the smallest disk counts."""
    disks = set(policy_rows[0]["disks"]) if policy_rows else {d["name"] for d in disk_rows}
    free = [int(d["free_space"]) - int(d["keep_free_space"]) for d in disk_rows if d["name"] in disks]
    return min(free) if free else 0


def disk_need(table_row, cols, bench, key_cols, sample_rows, sample_cols=None, write=False):
    """Bytes for the sample table plus the largest per-column table (rough upper estimate);
    with `write`, plus the write benchmark's uncompressed copy and one filled write table (at most uncompressed)."""
    total_rows = int(table_row["total_rows"] or 0)
    if not total_rows:
        return 0, 0
    per_row = {c["name"]: (int(c["data_compressed_bytes"]) / total_rows,
                           int(c["data_uncompressed_bytes"]) / total_rows) for c in cols}
    names = [c["name"] for c in (sample_cols if sample_cols is not None else cols)]
    sample = sum(per_row[n][0] for n in names if n in per_row) * sample_rows
    key = sum(per_row[k][0] for k in key_cols if k in per_row)
    worst = 0.0
    for c in bench:
        comp, uncomp = per_row[c["name"]]
        n = len(codec_candidates(c["type"])) + 1  # + current codec
        worst = max(worst, (key + uncomp + (n - 1) * comp + (2 * uncomp if write else 0)) * sample_rows)
    return int(sample), int(worst)


# ---------------------------------------------------------------- sample table (Phase 1)

def sample_columns(cols, bench, table_row, extra_refs=(), all_columns=False):
    """Stored columns the sample needs: measured ones + key/partition/engine columns. Source order."""
    stored = [c for c in cols if benchable(c)[0]]
    if all_columns:
        return stored
    names = [c["name"] for c in cols]
    need = {c["name"] for c in bench} | set(extra_refs)
    clauses = parse_clauses(table_row["engine_full"])
    for kw in ("PARTITION BY", "PRIMARY KEY", "ORDER BY", "SAMPLE BY"):
        need |= column_refs(clauses.get(kw, ""), names)
    for arg in parse_engine(scratch_engine(table_row["engine_full"]))[1]:
        need |= column_refs(arg, names)
    return [c for c in stored if c["name"] in need]


def table_body(table_row, sample_cols):
    """(columns DDL, engine DDL) for the sample table: same engine minus Replicated, same keys and
    settings, wide parts forced. Left out: TTL, skip indexes, projections, defaults, comments."""
    col_ddl = ", ".join(f"{quote_ident(c['name'])} {c['type']}" + (f" {c['compression_codec']}" if c["compression_codec"] else "")
                        for c in sample_cols)
    clauses = parse_clauses(table_row["engine_full"])
    parts = [scratch_engine(table_row["engine_full"])]
    for kw in ("PARTITION BY", "PRIMARY KEY", "ORDER BY", "SAMPLE BY"):
        if kw in clauses:
            parts.append(f"{kw} {clauses[kw]}")
    if "ORDER BY" not in clauses:
        parts.append("ORDER BY tuple()")
    wide = {w.split("=")[0].strip() for w in WIDE_PARTS}
    settings = [x for x in split_top_level(clauses.get("SETTINGS", "")) if x.split("=")[0].strip() not in wide]
    parts.append("SETTINGS " + ", ".join(settings + WIDE_PARTS))
    return col_ddl, " ".join(parts)


def column_table_body(table_row, cols, col):
    """(columns DDL, engine DDL) for one column's table: same engine, keys and settings as the sample table;
    key/partition/engine columns plus variant 0 = `col` with its current codec. Other variants are added by ALTER."""
    if any(c["name"].startswith(VARIANT.format("")) for c in cols):
        raise ValueError(f"source has a column starting with {VARIANT.format('')!r}; variant names would clash")
    return table_body(table_row, sample_columns(cols, [], table_row) + [dict(col, name=VARIANT.format(0))])


def write_table_body(table_row, col_type, codec):
    """(columns DDL, engine DDL) for a write benchmark table: only the column, plain MergeTree without keys
    (nothing to sort), the source's table settings (granularity, compress block sizes), wide parts.
    codec = text inside CODEC(...), or '' for the server default."""
    _, engine = table_body(table_row, [])
    settings = engine[engine.index(" SETTINGS "):]
    return (f"{quote_ident(WRITE_COL)} {col_type}" + (f" CODEC({codec})" if codec else ""),
            f"MergeTree ORDER BY tuple(){settings}")


def sort_order(table_row):
    """ORDER BY list that reads a column table the way its parts store it: partition, then sorting key."""
    return ", ".join(x for x in (table_row["partition_key"], table_row["sorting_key"]) if x)


_SERVER_ERROR = re.compile(r"Code: (\d+)\. DB::Exception: ([^\n]*)")
_VERSION_SUFFIX = re.compile(r"\s*\(version [^()]*(\([^()]*\))?[^()]*\)\s*$")  # "(version 25.12.1.1 (official build))"


def server_error(e):
    """(code, message) if `e` carries a ClickHouse server error, else None (connection problems, own errors)."""
    m = _SERVER_ERROR.search(str(e))
    return (int(m.group(1)), _VERSION_SUFFIX.sub("", m.group(2)).strip()[:300]) if m else None


def column_failure(e):
    """(code, message) for errors that only skip the current column; None means: stop the run."""
    err = server_error(e)
    return err if err and err[0] not in FATAL_CODES else None


def hash_filter(key, fraction):
    """WHERE condition keeping whole series; '' when everything is taken."""
    if fraction >= 1:
        return ""
    k = max(1, math.ceil(fraction * HASH_BUCKETS))
    return f"sipHash64({', '.join(key)}) % {HASH_BUCKETS} < {k}"


def where_clause(*conds):
    conds = [c for c in conds if c]
    return "WHERE " + " AND ".join(f"({c})" for c in conds) if conds else ""


def new_run_id():
    return time.strftime("%Y%m%d_%H%M%S") + "_" + secrets.token_hex(2)


# ---------------------------------------------------------------- ClickHouse access

class Reader:
    """Read-only query access; rows come back as dicts."""

    def __init__(self, client):
        self.client = client

    def rows(self, sql, params=None):
        r = self.client.query(sql, parameters=params or {})
        return [dict(zip(r.column_names, row)) for row in r.result_rows]

    def run_logged(self, sql, query_id, settings):
        """A SELECT whose result is discarded (FORMAT Null); timings are looked up later by query_id."""
        self.client.command(sql, settings={**settings, "query_id": query_id})


def connect(a):
    import clickhouse_connect  # imported here so unit tests run without it
    client = clickhouse_connect.get_client(
        host=a.host, port=a.port, username=a.user, password=os.environ.get("CLICKHOUSE_PASSWORD", ""),
        send_receive_timeout=CLIENT_TIMEOUT,
        # no HTTP session: after a client-side error the statement keeps running on the server and would lock the
        # session, so every later statement (cleanup included) would fail with SESSION_IS_LOCKED
        autogenerate_session_id=False,
        settings={
            "max_threads": a.threads,
            "max_insert_threads": 1,
            "max_memory_usage": int(a.max_memory_gb * 1024 ** 3),
            "max_execution_time": QUERY_TIMEOUT,
            "priority": 10,
        })
    return Reader(client)


class UnsafeWrite(Exception):
    pass


class Interrupted(Exception):
    pass


class Writer:
    """The only code path that writes. Accepts only `_codec_bench_*` table names in the scratch database,
    builds every statement itself and checks before each write that it still talks to the dry-run host."""

    def __init__(self, client, database, host, run_id, kill_client=None):
        self.client, self.database, self.host, self.run_id = client, database, host, run_id
        self.kill_client = kill_client  # callable -> fresh client, for KILL QUERY while `client` is busy
        self.created = []

    def _target(self, name):
        if not SCRATCH_NAME.match(name):
            raise UnsafeWrite(f"refusing to write to {name!r}: not a {PREFIX}* name")
        return f"{quote_ident(self.database)}.{quote_ident(name)}"

    def _run(self, name, build_sql, settings=None):
        target = self._target(name)
        host = self.client.query("SELECT hostName()").result_rows[0][0]
        if host != self.host:
            raise UnsafeWrite(f"connected to {host}, expected {self.host}; refusing to write")
        t0 = time.time()
        self.client.command(build_sql(target), settings=settings or {})
        return time.time() - t0

    def table(self, name):
        return f"{PREFIX}{self.run_id}_{name}"

    def create_table(self, name, col_ddl, engine_ddl):
        self.created.append(name)
        return self._run(name, lambda t: f"CREATE TABLE {t} ({col_ddl}) ENGINE = {engine_ddl}", CREATE_SETTINGS)

    def create_as(self, name, source):
        """Same columns, codecs and engine as our own table `source`."""
        src = self._target(source)
        self.created.append(name)
        return self._run(name, lambda t: f"CREATE TABLE {t} AS {src}", CREATE_SETTINGS)

    def insert_select(self, name, col_names, source, where, settings=None, exprs=None):
        cols = ", ".join(quote_ident(c) for c in col_names)
        select = ", ".join(exprs) if exprs else cols
        return self._run(name, lambda t: f"INSERT INTO {t} ({cols}) SELECT {select} FROM {source} {where}", settings)

    def add_column(self, name, col, col_type, codec):
        return self._run(name, lambda t: f"ALTER TABLE {t} ADD COLUMN {quote_ident(col)} {col_type} CODEC({codec})",
                         CREATE_SETTINGS)

    def drop_column(self, name, col):
        return self._run(name, lambda t: f"ALTER TABLE {t} DROP COLUMN {quote_ident(col)}")

    def optimize_final(self, name):
        return self._run(name, lambda t: f"OPTIMIZE TABLE {t} FINAL")

    def truncate(self, name):
        return self._run(name, lambda t: f"TRUNCATE TABLE {t} SYNC")

    def drop(self, name):
        secs = self._run(name, lambda t: f"DROP TABLE IF EXISTS {t} SYNC")
        if name in self.created:
            self.created.remove(name)
        return secs

    def kill_running(self):
        """KILL our still-running statements (they all mention the run id)."""
        client = self.kill_client() if self.kill_client else self.client
        client.command(f"KILL QUERY WHERE position(query, {quote_str(PREFIX + self.run_id)}) > 0 "
                       f"AND query NOT LIKE 'KILL QUERY%' SYNC")

    def leftovers(self):
        r = self.client.query("SELECT name FROM system.tables WHERE database = {db:String} "
                              "AND startsWith(name, {p:String}) ORDER BY name",
                              parameters={"db": self.database, "p": PREFIX})
        return [row[0] for row in r.result_rows]


def _raise_interrupted(signum, _frame):
    raise Interrupted(signal.Signals(signum).name)


def install_signal_handlers():
    """Returns the previous handlers for restore_signal_handlers()."""
    return {sig: signal.signal(sig, _raise_interrupted) for sig in (signal.SIGTERM, signal.SIGINT)}


def restore_signal_handlers(previous):
    for sig, handler in previous.items():
        signal.signal(sig, handler)


def ignore_signals():
    """During cleanup: a second Ctrl-C/SIGTERM must not abort the drops."""
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, signal.SIG_IGN)


# ---------------------------------------------------------------- Phase 0

class Checks:
    def __init__(self):
        self.failed = False

    def ok(self, what, detail=""):
        log(f"[OK]   {what}{': ' + detail if detail else ''}")

    def warn(self, what, detail):
        log(f"[WARN] {what}: {detail}")

    def fail(self, what, detail):
        self.failed = True
        log(f"[FAIL] {what}: {detail}")

    def info(self, what, detail):
        log(f"       {what}: {detail}")


def dry_run(db, a):
    """Phase 0. Returns (ok, plan dict)."""
    ch = Checks()
    target = f"{quote_ident(a.database)}.{quote_ident(a.table)}"
    where = f"WHERE {a.where}" if a.where else ""

    srv = db.rows("SELECT hostName() AS host, version() AS version")[0]
    ch.info("server", f"host={srv['host']} version={srv['version']}")

    scratch_db = a.scratch_database or a.database
    d = db.rows("SELECT engine FROM system.databases WHERE name = {d:String}", {"d": scratch_db})
    if not d:
        ch.fail("scratch database", f"{scratch_db} not found")
        return False, None
    if d[0]["engine"] not in SCRATCH_DB_ENGINES:
        ch.fail("scratch database", f"{scratch_db} has engine {d[0]['engine']}: CREATE would reach other nodes; "
                                    f"use --scratch-database with an Atomic database")
        return False, None
    ch.ok("scratch database", f"{scratch_db} ({d[0]['engine']})")

    p = {"db": a.database, "t": a.table}
    t = db.rows("SELECT * FROM system.tables WHERE database = {db:String} AND name = {t:String}", p)
    if not t:
        ch.fail("table", f"{a.database}.{a.table} not found")
        return False, None
    t = t[0]
    ok, why = engine_supported(t)
    if not ok:
        ch.fail("engine", why)
        return False, None
    ch.ok("engine", f"{t['engine']} -> scratch: {scratch_engine(t['engine_full'])}")
    ch.info("partition by", t["partition_key"] or "-")
    ch.info("order by", t["sorting_key"])
    settings = parse_settings(t["engine_full"])
    ch.info("settings", ", ".join(settings) or "-")
    ch.info("rows / size", f"{int(t['total_rows'] or 0):,} rows, {human_bytes(t['total_bytes'] or 0)}")

    cols = db.rows("SELECT * FROM system.columns WHERE database = {db:String} AND table = {t:String} ORDER BY position", p)
    bench, skipped, unknown = select_columns(cols, a.columns)
    if unknown:
        ch.fail("columns", f"unknown: {', '.join(unknown)}")
    for name, why in skipped:
        ch.info("skip column", f"{name} ({why})")
    if not bench:
        ch.fail("columns", "nothing to measure")
        return False, None

    names = [c["name"] for c in cols]
    order_by = parse_clauses(t["engine_full"]).get("ORDER BY", "")
    key = split_top_level(a.sample_by) if a.sample_by else default_series_key(order_by, names)
    ch.ok("series key", f"({', '.join(key)})" + (" [--sample-by]" if a.sample_by else " [default from ORDER BY]"))

    scan = estimate_rows(db.rows(f"EXPLAIN ESTIMATE SELECT {', '.join(key)} FROM {target} {where}"))
    if scan == 0:
        ch.fail("scan estimate", "0 rows match")
        return False, None
    if scan > a.max_scan_rows:
        ch.fail("scan estimate", f"{scan:,} rows > --max-scan-rows {a.max_scan_rows:,}; narrow --where")
        return False, None
    ch.ok("scan estimate", f"{scan:,} rows (limit {a.max_scan_rows:,})")

    frac = sample_fraction(a.max_rows, scan)
    sample_rows = int(scan * frac)
    ch.info("sample", f"fraction {frac:.4%} of series, ~{sample_rows:,} rows (varies with series lengths)")

    series = int(db.rows(f"SELECT uniq({', '.join(key)}) AS series FROM {target} {where}")[0]["series"])
    in_sample = series * frac
    msg = f"{series:,} series in scan, ~{in_sample:,.0f} in sample"
    if in_sample < MIN_SERIES:
        ch.warn("series", msg + f" (< {MIN_SERIES}); consider a narrower --where")
    else:
        ch.ok("series", msg)

    key_cols = set()
    for k in key:
        key_cols |= column_refs(k, names)
    sample_cols = sample_columns(cols, bench, t, key_cols, a.sample_all_columns)
    ch.info("sample columns", ", ".join(c["name"] for c in sample_cols))
    sample_b, worst_b = disk_need(t, cols, bench, sorted(key_cols), sample_rows, sample_cols, a.write_runs > 0)
    if a.stability:
        worst_b = int(worst_b * 1.5)  # + one half at a time
    policy = db.rows("SELECT policy_name, volume_name, disks FROM system.storage_policies "
                     "WHERE policy_name = {p:String} ORDER BY volume_priority", {"p": t["storage_policy"]})
    free = free_bytes(policy, db.rows("SELECT name, free_space, keep_free_space FROM system.disks"))
    need = (sample_b + worst_b) * DISK_HEADROOM
    msg = (f"need ~{human_bytes(need)} (sample {human_bytes(sample_b)} + largest column table "
           f"{'incl. stability half ' if a.stability else ''}{human_bytes(worst_b)}, x{DISK_HEADROOM:g}), "
           f"free {human_bytes(free)}")
    (ch.ok if need <= free else ch.fail)("disk", msg)

    m = {r["metric"]: float(r["value"]) for r in db.rows(
        "SELECT metric, value FROM system.asynchronous_metrics WHERE metric IN ('LoadAverage1', 'CGroupMaxCPU')")}
    act = db.rows("SELECT (SELECT count() FROM system.merges) AS merges, "
                  "(SELECT count() FROM system.processes) - 1 AS queries")[0]
    load, cpus = m.get("LoadAverage1"), m.get("CGroupMaxCPU") or 0
    msg = f"load1={load if load is not None else '?'} cpus={cpus or '?'} merges={act['merges']} queries={act['queries']}"
    (ch.warn if load is not None and cpus and load / cpus > LOAD_WARN else ch.ok)("node", msg)

    total = 0
    for c in bench:
        n = len(codec_candidates(c["type"])) + 1
        total += n
        ch.info("candidates", f"{c['name']} {c['type']} {c['compression_codec'] or '(default)'}: {n}")
    ch.info("candidates", f"{total} in total over {len(bench)} columns (validated by the server in the real run)")
    ch.info("per column", (f"read benchmark: 1 warm-up + {a.read_runs} runs per codec" if a.read_runs
                           else "read benchmark: off")
            + (f"; write benchmark: 1 warm-up + {a.write_runs} runs per codec (1 if the warm-up takes > "
               f"{WRITE_SLOW_S}s)" if a.write_runs else "; write benchmark: off")
            + "; stability check: " + ("on (halves A/B)" if a.stability else "off"))

    plan = {"host": srv["host"], "version": srv["version"], "scratch_db": scratch_db, "table": t, "columns": cols, "bench": bench,
            "sample_cols": sample_cols, "key": key, "scan_rows": scan, "fraction": frac,
            "sample_rows": sample_rows, "settings": settings}
    return not ch.failed, plan


# ---------------------------------------------------------------- Phase 1

def drop_leftovers(w):
    for name in w.leftovers():
        w.drop(name)
        log(f"dropped leftover {w.database}.{name}")


def build_sample(db, w, a, plan):
    """Phase 1: create the sample table, fill it with whole series, OPTIMIZE FINAL. Returns (name, rows, series)."""
    name = w.table("sample")
    target = f"{quote_ident(w.database)}.{quote_ident(name)}"
    col_ddl, engine_ddl = table_body(plan["table"], plan["sample_cols"])
    w.create_table(name, col_ddl, engine_ddl)
    log(f"created {w.database}.{name}: ENGINE = {engine_ddl}")

    source = f"{quote_ident(a.database)}.{quote_ident(a.table)}"
    where = where_clause(a.where, hash_filter(plan["key"], plan["fraction"]))
    secs = w.insert_select(name, [c["name"] for c in plan["sample_cols"]], source, where,
                           {"max_rows_to_read": a.max_scan_rows, "max_partitions_per_insert_block": 0})
    stats = lambda: db.rows(f"SELECT count() AS rows, uniq({', '.join(plan['key'])}) AS series FROM {target}")[0]
    before = stats()
    log(f"inserted {int(before['rows']):,} rows / {int(before['series']):,} series in {secs:.1f}s ({where or 'no filter'})")

    secs = w.optimize_final(name)
    after = stats()
    parts = db.rows("SELECT count() AS parts, sum(bytes_on_disk) AS bytes FROM system.parts "
                    "WHERE active AND database = {db:String} AND table = {t:String}",
                    {"db": w.database, "t": name})[0]
    log(f"OPTIMIZE FINAL in {secs:.1f}s: {int(before['rows']):,} -> {int(after['rows']):,} rows, "
        f"{int(after['series']):,} series, {int(parts['parts'])} parts, {human_bytes(parts['bytes'] or 0)}")
    if int(after["series"]) < MIN_SERIES:
        log(f"[WARN] only {int(after['series'])} series in the sample (< {MIN_SERIES}); consider a narrower --where")
    return name, int(after["rows"]), int(after["series"])


# ---------------------------------------------------------------- Phase 2

def measure_column(db, w, plan, col, name, sample, sample_rows, read_runs=0, stability=False, write_runs=0):
    """Sizes (and read/write times, stability) of every codec the server accepts for `col`,
    measured in table `name` filled from the sample."""
    target = f"{quote_ident(w.database)}.{quote_ident(name)}"
    p = {"db": w.database, "t": name}
    current = f"current {col['compression_codec'] or '(server default)'}"
    res = {"column": col["name"], "type": col["type"], "current": col["compression_codec"],
           "rejected": [], "duplicates": [], "variants": [], "rows": 0, "stability": None, "warnings": [], "error": None}

    def warn(msg):
        res["warnings"].append(msg)
        log(f"  [WARN] {col['name']}: {msg}")


    col_ddl, engine_ddl = column_table_body(plan["table"], plan["columns"], col)
    w.create_table(name, col_ddl, engine_ddl)
    labels = {VARIANT.format(0): current}
    for i, codec in enumerate(codec_candidates(col["type"]), 1):
        try:
            w.add_column(name, VARIANT.format(i), col["type"], codec)
            labels[VARIANT.format(i)] = codec
        except Exception as e:
            err = column_failure(e)
            if err is None:
                raise
            res["rejected"].append((codec, err[1]))
            log(f"  [REJECTED] {col['name']} CODEC({codec}): {err[1]}")

    # duplicates by the server's own spelling (e.g. Delta -> Delta(8)); v0 without a codec matches nothing
    canon = {r["name"]: r["compression_codec"] for r in db.rows(COLUMN_SIZES, p)}
    seen = {canon[VARIANT.format(0)]: current} if col["compression_codec"] else {}
    for v, label in list(labels.items())[1:]:
        if canon[v] in seen:
            w.drop_column(name, v)
            del labels[v]
            res["duplicates"].append((label, seen[canon[v]]))
            log(f"  [SAME] {col['name']} CODEC({label}) = {seen[canon[v]]}")
        else:
            seen[canon[v]] = label

    keys = [c["name"] for c in sample_columns(plan["columns"], [], plan["table"])]
    fill_args = (keys + list(labels), f"{quote_ident(w.database)}.{quote_ident(sample)}")
    fill_exprs = [quote_ident(k) for k in keys] + [quote_ident(col["name"])] * len(labels)
    fill = w.insert_select(name, *fill_args, "", FILL_SETTINGS, exprs=fill_exprs)
    opt = w.optimize_final(name)
    res["rows"] = rows = int(db.rows(f"SELECT count() AS rows FROM {target}")[0]["rows"])
    sizes = {r["name"]: r for r in db.rows(COLUMN_SIZES, p)}
    res["variants"] = sorted(({"codec": label, "current": v == VARIANT.format(0),
                               "compressed": int(sizes[v]["compressed"]), "uncompressed": int(sizes[v]["uncompressed"])}
                              for v, label in labels.items()), key=lambda x: (x["compressed"], not x["current"]))
    log(f"  {col['name']}: {len(labels)} variants ({len(res['rejected'])} rejected, {len(res['duplicates'])} same), "
        f"{rows:,} rows, fill {fill:.1f}s, optimize {opt:.1f}s")
    if rows != sample_rows:
        warn(f"column table has {rows:,} rows, sample {sample_rows:,} (engine merge); "
             f"variants compare with each other, not 1:1 with the sample")
    if len({x["uncompressed"] for x in res["variants"]}) > 1:
        warn("uncompressed size differs between variants")

    by_label = {x["codec"]: x for x in res["variants"]}

    def timed(what, times, basis, got, want):
        res["basis"] = "wall" if "wall" in (basis, res.get("basis")) else "cpu"
        if got < want:
            warn(f"query_log has {got}/{want} {what} runs after {QUERY_LOG_TIMEOUT}s; medians use what is there")
        for v, t in times.items():
            by_label[labels[v]].update(t)

    if read_runs:
        timed("read", *read_benchmark(db, w.database, name, labels, read_runs))
    if write_runs:
        try:
            times, slow = write_benchmark(db, w, plan, col, name, labels, write_runs)
        except Exception as e:
            err = column_failure(e)
            if err is None:
                raise
            res["write_error"] = f"code {err[0]}: {err[1]}"
            log(f"  [FAIL] {col['name']}: write benchmark: code {err[0]}: {err[1]}; sizes and read times kept")
        else:
            timed("write", *times)
            res["write_slow"] = [labels[v] for v in labels if v in slow]
            if slow:
                log(f"  {col['name']}: measured once (warm-up > {WRITE_SLOW_S}s): {', '.join(res['write_slow'])}")
    if stability:
        try:
            res["stability"] = st = stability_check(db, w, plan, name, labels, fill_args, fill_exprs, sample)
        except Exception as e:
            err = column_failure(e)
            if err is None:
                raise
            res["stability"] = {"error": f"code {err[0]}: {err[1]}"}
            log(f"  [FAIL] {col['name']}: stability check: code {err[0]}: {err[1]}; sizes and read times kept")
        else:
            for label, pp in st["shift"].items():
                by_label[label]["shift"] = pp
            log(f"  {col['name']}: stability {stability_summary(st)}")
            if st["unstable"]:
                log(f"  [UNSTABLE] {col['name']}: " + "; ".join(st["reasons"]))
    for line in size_lines(res["variants"], rows, res.get("basis") or "cpu"):
        log("    " + line)
    return res


def timing_cells(x, what):
    """(ms, spread, MB/s) of one variant for "read" or "write": ms = median CPU (or wall) time,
    MB/s = uncompressed bytes / median wall time."""
    ms, wall = x.get(f"{what}_ms"), x.get(f"{what}_wall_ms")
    if not ms:
        return "-", "-", "-"
    spread = f"{(x[f'{what}_max'] - x[f'{what}_min']) / ms:.0%}" if x.get(f"{what}_runs", 0) > 1 else "1 run"
    mbs = f"{x['uncompressed'] / wall / 1000:.0f}" if wall else "-"  # bytes per ms / 1000 = MB/s
    return f"{ms:.1f}", spread, mbs


def timed_kinds(variants):
    return [k for k in ("read", "write") if any(f"{k}_ms" in x for x in variants)]


def size_lines(variants, rows, basis="cpu"):
    """Table of the variants; read/write columns only when measured, A/B shift only with the stability check."""
    cur = next((x["compressed"] for x in variants if x["current"]), 0)
    kinds = timed_kinds(variants)
    shifts = any("shift" in x for x in variants)
    head = f"{'compressed':>12} {'bytes/row':>10} {'ratio':>8} {'vs current':>11}"
    for k in kinds:
        head += f" {k + ' ' + basis + ' ms':>14} {'spread':>7} {k + ' MB/s':>10}"
    head += f" {'A/B pp':>7}" if shifts else ""
    out = [head + "  codec"]
    for x in variants:
        ratio = f"{x['uncompressed'] / x['compressed']:.2f}x" if x["compressed"] else "-"
        delta = f"{(x['compressed'] - cur) / cur:+.1%}" if cur else "-"
        per_row = f"{x['compressed'] / rows:.3f}" if rows else "-"
        line = f"{human_bytes(x['compressed']):>12} {per_row:>10} {ratio:>8} {delta:>11}"
        for k in kinds:
            ms, spread, mbs = timing_cells(x, k)
            line += f" {ms:>14} {spread:>7} {mbs:>10}"
        if shifts:
            line += f" {x['shift']:>7.1f}" if x.get("shift") is not None else f" {'-':>7}"
        out.append(f"{line}  {'[' + x['codec'] + ']' if x['current'] else x['codec']}")
    return out


def query_times(db, prefix, labels, runs, what, single=()):
    """Timings of our logged runs from system.query_log, polled (no SYSTEM FLUSH LOGS). Query ids are
    <prefix><variant>_r<run>; run 0 is the warm-up and not counted, except for variants in `single`
    (only run 0 was run).
    Returns ({variant: {<what>_ms, _min, _max (CPU time; wall time if the server reports no CPU time, e.g. macOS),
    <what>_wall_ms, <what>_runs}}, basis "cpu"/"wall" (None if no run was found), runs found, expected)."""
    want = (len(labels) - len(single)) * runs + len(single)
    deadline = time.monotonic() + QUERY_LOG_TIMEOUT
    found = {}
    while True:
        try:
            rows = db.rows(QUERY_TIMES, {"p": prefix})
        except Exception as e:
            err = column_failure(e)
            if err is None:
                raise
            log(f"  [WARN] query_log not readable: code {err[0]}: {err[1]}")
            break
        found = {}
        for x in rows:
            v, r = x["query_id"][len(prefix):].rsplit("_r", 1)
            if v in labels and (r != "0" or v in single):
                found[(v, r)] = x  # one row per run, even if query_log repeats one
        if len(found) >= want or time.monotonic() >= deadline:
            break
        time.sleep(QUERY_LOG_POLL)

    basis = None if not found else "cpu" if all(int(x["cpu_us"]) > 0 for x in found.values()) else "wall"
    times = {}
    for v in labels:
        runs_v = [x for (fv, _), x in found.items() if fv == v]
        ms = [int(x[f"{basis}_us"]) / 1000 for x in runs_v]
        if ms:
            times[v] = {f"{what}_ms": statistics.median(ms), f"{what}_min": min(ms), f"{what}_max": max(ms),
                        f"{what}_wall_ms": statistics.median(int(x["wall_us"]) / 1000 for x in runs_v),
                        f"{what}_runs": len(ms)}
    return times, basis, len(found), want


def read_benchmark(db, database, name, labels, runs):
    """`SELECT v FORMAT Null` per variant: one warm-up, then `runs` runs, interleaved over the variants so that
    load changes on the node hit all codecs alike. Returns query_times(..., "read")."""
    target = f"{quote_ident(database)}.{quote_ident(name)}"
    prefix = f"{name}_read_"  # the run id in the table name makes query ids unique
    for r in range(runs + 1):
        for v in labels:
            db.run_logged(f"SELECT {quote_ident(v)} FROM {target} FORMAT Null", f"{prefix}{v}_r{r}", READ_SETTINGS)
    return query_times(db, prefix, labels, runs, "read")


def write_table(name, v):
    return f"{name}_w{v[len(VARIANT.format('')):]}"


def write_benchmark(db, w, plan, col, name, labels, runs):
    """`INSERT … SELECT` of the column alone, per variant into its own table (only that column with that codec,
    no keys). The source is an uncompressed copy of the column in the column table's storage order, so every codec
    compresses exactly the data it stores, and reading the source costs the same for all of them.
    One block = one part per INSERT; TRUNCATE after each run. One warm-up, then `runs` runs, interleaved over the
    variants like the reads; a variant whose warm-up takes longer than WRITE_SLOW_S is not run again and its warm-up
    is its only run (high levels of LZ4HC/ZSTD can take minutes; compression dominates such a run, not caching).
    Returns (query_times(..., "write"), slow variants)."""
    t = plan["table"]
    src = f"{name}_wsrc"
    w.create_table(src, *write_table_body(t, col["type"], "NONE"))
    order = sort_order(t)
    w.insert_select(src, [WRITE_COL], f"{quote_ident(w.database)}.{quote_ident(name)}",
                    f"ORDER BY {order}" if order else "", ONE_BLOCK, exprs=[quote_ident(VARIANT.format(0))])
    current = (col["compression_codec"] or "")[len("CODEC("):-1]
    for v, label in labels.items():
        w.create_table(write_table(name, v), *write_table_body(t, col["type"], current if v == VARIANT.format(0) else label))
    source = f"{quote_ident(w.database)}.{quote_ident(src)}"
    prefix = f"{name}_write_"
    slow = set()
    for r in range(runs + 1):
        for v in labels:
            if v in slow:
                continue
            wt = write_table(name, v)
            secs = w.insert_select(wt, [WRITE_COL], source, "", {**WRITE_SETTINGS, "query_id": f"{prefix}{v}_r{r}"})
            w.truncate(wt)
            if r == 0 and secs > WRITE_SLOW_S:
                slow.add(v)
    for n in [src] + [write_table(name, v) for v in labels]:
        w.drop(n)
    return query_times(db, prefix, labels, runs, "write", slow), slow


def half_table(name, half):
    return f"{name}_{'ab'[half]}"


def stability_check(db, w, plan, name, labels, fill_args, fill_exprs, sample):
    """Sizes on two disjoint halves of the sample (whole series, cityHash64 of the series key, independent of the
    sipHash64 sampling). One half table at a time. Compares "vs smallest" per codec between the halves."""
    halves = []
    for half in (0, 1):
        hname = half_table(name, half)
        w.create_as(hname, name)
        w.insert_select(hname, *fill_args, f"WHERE cityHash64({', '.join(plan['key'])}) % 2 = {half}",
                        FILL_SETTINGS, exprs=fill_exprs)
        w.optimize_final(hname)
        rows = int(db.rows(f"SELECT count() AS rows FROM {quote_ident(w.database)}.{quote_ident(hname)}")[0]["rows"])
        sizes = {r["name"]: int(r["compressed"]) for r in db.rows(COLUMN_SIZES, {"db": w.database, "t": hname})}
        w.drop(hname)
        halves.append((rows, {v: sizes[v] for v in labels}))
    return compare_halves(labels, *halves)


def compare_halves(labels, a, b):
    """a, b = (rows, {variant: compressed}). Per half, each codec's size vs the smallest codec of that half (%).
    Contenders (within STABILITY_CONTENDER % of the smallest in either half) get shift = |A - B| in percentage points;
    any shift > STABILITY_PP flags the column. This also catches a different winner, but not a meaningless swap."""
    (rows_a, sa), (rows_b, sb) = a, b
    st = {"rows": (rows_a, rows_b), "shift": {}, "max_shift": None, "smallest": None, "unstable": False, "reasons": []}
    min_a, min_b = min(sa.values()), min(sb.values())
    if not (min_a and min_b):
        st["reasons"].append("a half is empty; not comparable")
        st["unstable"] = True
        return st
    order = list(labels)
    st["smallest"] = tuple(labels[min((v for v in labels if s[v] == m), key=order.index)]
                           for s, m in ((sa, min_a), (sb, min_b)))
    for v, label in labels.items():
        vs_a, vs_b = (sa[v] / min_a - 1) * 100, (sb[v] / min_b - 1) * 100
        if min(vs_a, vs_b) <= STABILITY_CONTENDER:
            st["shift"][label] = abs(vs_a - vs_b)
    st["max_shift"] = max(((pp, label) for label, pp in st["shift"].items()), key=lambda x: x[0])
    if st["max_shift"][0] > STABILITY_PP:
        st["reasons"].append(f"{st['max_shift'][1]} moves {st['max_shift'][0]:.1f} pp vs the smallest codec between "
                             f"halves (> {STABILITY_PP:g}); smallest A: {st['smallest'][0]}, B: {st['smallest'][1]}")
    st["unstable"] = bool(st["reasons"])
    return st


def stability_summary(st):
    msg = f"halves A {st['rows'][0]:,} / B {st['rows'][1]:,} rows"
    if st["max_shift"]:
        msg += (f"; {len(st['shift'])} contenders (within {STABILITY_CONTENDER:g}% of the smallest), largest shift "
                f"{st['max_shift'][0]:.1f} pp ({st['max_shift'][1]}); smallest A: {st['smallest'][0]}, "
                f"B: {st['smallest'][1]}")
    return msg


def phase2(db, w, plan, sample, sample_rows, read_runs=0, stability=False, results=None, write_runs=0):
    """Phase 2, one column at a time. Column-specific server errors skip the column; everything else stops.
    Results are appended to `results` as they come, so a caller still has them after an abort."""
    results = [] if results is None else results
    warned_basis = False
    for i, col in enumerate(plan["bench"], 1):
        name = w.table(f"col{i}")
        log(f"Phase 2: column {i}/{len(plan['bench'])} {col['name']} {col['type']} "
            f"{col['compression_codec'] or '(server default)'}")
        try:
            results.append(measure_column(db, w, plan, col, name, sample, sample_rows, read_runs, stability,
                                          write_runs))
            if results[-1].get("basis") == "wall" and not warned_basis:
                warned_basis = True
                log("[WARN] CPU time not reported by the server; read/write times are wall-clock time")
        except Exception as e:
            err = column_failure(e)
            if err is None:
                raise
            log(f"[FAIL] {col['name']}: code {err[0]}: {err[1]}; column skipped")
            results.append({"column": col["name"], "type": col["type"], "error": f"code {err[0]}: {err[1]}"})
        for n in [n for n in w.created if n.startswith(name + "_")] + [name]:  # halves, write tables, column table
            if n in w.created:
                w.drop(n)
    return results


# ---------------------------------------------------------------- Phase 3: report

REPORT_TOP = 10  # per column the report shows the smallest N, the Pareto codecs and the current one


def report_meta(w, a, plan):
    t = plan["table"]
    return {"run_id": w.run_id, "started": time.time(), "host": plan["host"], "version": plan.get("version", "?"),
            "database": a.database, "table": a.table, "engine": t["engine"], "where": a.where, "key": plan["key"],
            "fraction": plan["fraction"], "read_runs": a.read_runs, "write_runs": a.write_runs,
            "stability": a.stability,
            "planned": len(plan["bench"]), "source_rows": int(t["total_rows"] or 0),
            "source_bytes": {c["name"]: int(c["data_compressed_bytes"] or 0) for c in plan["columns"]},
            "sample_rows": 0, "series": 0, "aborted": None}


def pareto(variants):
    """Codecs that no other codec beats on size and every measured time (median read / write CPU time) at once:
    at least as good on all, better on one. Only codecs with all measured times take part."""
    keys = ["compressed"] + [f"{k}_ms" for k in timed_kinds(variants)]
    if len(keys) == 1:
        return set()
    timed = [x for x in variants if all(x.get(k) for k in keys[1:])]
    return {x["codec"] for x in timed if not any(
        all(y[k] <= x[k] for k in keys) and any(y[k] < x[k] for k in keys) for y in timed)}


def compact_rows(variants, front):
    """Variants (sorted by size) the report shows: the smallest REPORT_TOP, the Pareto codecs, the current one."""
    return [x for i, x in enumerate(variants) if i < REPORT_TOP or x["current"] or x["codec"] in front]


def group_rejected(rejected):
    """[(codec, reason)] -> [(reason, [codecs])], in first-seen order."""
    groups = {}
    for codec, reason in rejected:
        groups.setdefault(reason, []).append(codec)
    return list(groups.items())


def md(text):
    return str(text).replace("|", "\\|").replace("\n", " ")


def duration(secs):
    secs = int(secs)
    return f"{secs // 3600}h {secs % 3600 // 60:02d}m {secs % 60:02d}s" if secs >= 3600 else f"{secs // 60}m {secs % 60:02d}s"


def render_report(meta, results, now=None):
    """The markdown report as lines (no log prefix). Only measured facts; no rating, no recommendation."""
    now = time.time() if now is None else now
    ok = [r for r in results if not r.get("error")]
    basis = "wall" if any(r.get("basis") == "wall" for r in ok) else "cpu"
    kinds = [k for k in ("read", "write") if any(k in timed_kinds(r["variants"]) for r in ok)]
    ms_head = {k: f"{k} {basis} ms" for k in ("read", "write")}
    out = [f"===== codec_bench report {meta['run_id']} begin =====", "",
           f"# codec_bench: `{md(meta['database'])}.{md(meta['table'])}`", ""]

    failed = len(results) - len(ok)
    status = (f"complete: {len(ok)} of {meta['planned']} columns measured" if not meta["aborted"] else
              f"**INCOMPLETE** (aborted: {md(meta['aborted'])}): {len(ok)} of {meta['planned']} columns measured")
    status += f", {failed} failed" if failed else ""
    time_basis = ("median CPU time (user + system); MB/s from median wall-clock time" if basis == "cpu" else
                  "median wall-clock time (the server reports no CPU time)")
    reads = (f"1 warm-up + {meta['read_runs']} runs per codec, single-threaded `SELECT … FORMAT Null`; {time_basis}"
             if meta["read_runs"] else "off")
    writes = (f"1 warm-up + {meta['write_runs']} runs per codec (1 run if the warm-up takes > {WRITE_SLOW_S} s), "
              f"single-threaded `INSERT` of the column alone; {time_basis}" if meta.get("write_runs") else "off")
    out += ["| | |", "|---|---|",
            f"| status | {status} |",
            f"| run | `{meta['run_id']}`, started {time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime(meta['started']))}, "
            f"took {duration(now - meta['started'])} |",
            f"| server | {md(meta['host'])}, ClickHouse {md(meta['version'])} |",
            f"| table | `{md(meta['database'])}.{md(meta['table'])}`, {md(meta['engine'])}, {meta['source_rows']:,} rows |",
            f"| filter | {'`' + md(meta['where']) + '`' if meta['where'] else 'none (whole table)'} |",
            f"| series key | `{md(', '.join(meta['key']))}` |",
            f"| sample | {meta['sample_rows']:,} rows, {meta['series']:,} series "
            f"({min(meta['fraction'], 1):.4%} of the series in the filter) |",
            f"| read benchmark | {reads} |",
            f"| write benchmark | {writes} |",
            f"| stability check | {'on (two disjoint halves of the sample)' if meta['stability'] else 'off'} |", ""]

    out += ["## Summary", "",
            "Sizes per row in the sample. *est. with smallest* is an extrapolation (see Method), not a measurement.", "",
            "| column | type | current codec | current B/row | smallest codec | B/row | vs current | "
            + "".join(f"{ms_head[k]} current | {ms_head[k]} smallest | " for k in kinds)
            + "on disk now | est. with smallest | flags |",
            "|---|---|---|--:|---|--:|--:|" + "--:|--:|" * len(kinds) + "--:|--:|---|"]
    for r in results:
        name, typ = md(r["column"]), md(r["type"])
        if r.get("error"):
            out.append(f"| `{name}` | `{typ}` |" + " |" * (7 + 2 * len(kinds)) + " FAILED |")
            continue
        cur = next(x for x in r["variants"] if x["current"])
        best = r["variants"][0]
        rows = r["rows"] or 0
        per_row = lambda x: f"{x['compressed'] / rows:.3f}" if rows else "-"
        ms = lambda x, k: f"{x[k + '_ms']:.1f}" if x.get(k + "_ms") else "-"
        src = meta["source_bytes"].get(r["column"], 0)
        est = human_bytes(src * best["compressed"] / cur["compressed"]) if src and cur["compressed"] else "-"
        delta = f"{(best['compressed'] - cur['compressed']) / cur['compressed']:+.1%}" if cur["compressed"] else "-"
        st = r.get("stability") or {}
        flags = (["UNSTABLE"] if st.get("unstable") else []) + (["stability check failed"] if st.get("error") else [])
        flags += ["write benchmark failed"] if r.get("write_error") else []
        flags += [f"{len(r['warnings'])} warning(s)"] if r.get("warnings") else []
        smallest = "(current)" if best["current"] else f"`{md(best['codec'])}`"
        out.append(f"| `{name}` | `{typ}` | `{md(r['current'] or '(server default)')}` | {per_row(cur)} | {smallest} "
                   f"| {per_row(best)} | {delta} | " + "".join(f"{ms(cur, k)} | {ms(best, k)} | " for k in kinds)
                   + f"{human_bytes(src) if src else '-'} | {est} | {', '.join(flags)} |")
    out.append("")

    for r in results:
        out += [f"## `{md(r['column'])}` {md(r['type'])}", ""]
        if r.get("error"):
            out += [f"**FAILED**: {md(r['error'])}", ""]
            continue
        variants, rows = r["variants"], r["rows"] or 0
        front = pareto(variants)
        shown = compact_rows(variants, front)
        shifts = any("shift" in x for x in variants)
        out.append(f"Current codec: `{md(r['current'] or '(server default)')}`. {len(variants)} codecs measured "
                   f"on {rows:,} rows, {len(r['rejected'])} rejected by the server, "
                   f"{len(r['duplicates'])} identical to another one.")
        out.append("")
        head = "| codec | compressed | B/row | ratio | vs current |"
        align = "|---|--:|--:|--:|--:|"
        for k in kinds:
            head += f" {ms_head[k]} | {k} spread | {k} MB/s |"
            align += "--:|--:|--:|"
        if kinds:
            head += " Pareto |"
            align += ":-:|"
        if shifts:
            head += " A/B pp |"
            align += "--:|"
        out += [head, align]
        cur = next(x["compressed"] for x in variants if x["current"])
        for x in shown:
            label = f"**current** `{md(x['codec'][len('current '):])}`" if x["current"] else f"`{md(x['codec'])}`"
            ratio = f"{x['uncompressed'] / x['compressed']:.2f}x" if x["compressed"] else "-"
            delta = f"{(x['compressed'] - cur) / cur:+.1%}" if cur else "-"
            line = (f"| {label} | {human_bytes(x['compressed'])} | {x['compressed'] / rows if rows else 0:.3f} "
                    f"| {ratio} | {delta} |")
            for k in kinds:
                line += " " + " | ".join(timing_cells(x, k)) + " |"
            if kinds:
                line += f" {'✓' if x['codec'] in front else ''} |"
            if shifts:
                line += f" {x['shift']:.1f} |" if x.get("shift") is not None else " - |"
            out.append(line)
        if len(shown) < len(variants):
            more = len(variants) - len(shown)
            out += ["", f"{more} more codec{'s' if more > 1 else ''} in the log above (size table of "
                        f"`{md(r['column'])}`)."]
        out.append("")
        if r["duplicates"]:
            out.append("Identical to another codec (same server spelling), not measured twice: "
                       + "; ".join(f"`{md(a)}` = `{md(b)}`" for a, b in r["duplicates"]) + ".")
            out.append("")
        if r["rejected"]:
            out.append(f"Rejected by the server ({len(r['rejected'])}):")
            out += [f"- {', '.join('`' + md(c) + '`' for c in codecs)}: {md(reason)}"
                    for reason, codecs in group_rejected(r["rejected"])]
            out.append("")
        if r.get("write_error"):
            out += [f"Write benchmark failed: {md(r['write_error'])}", ""]
        if r.get("write_slow"):
            out += [f"Write measured once (warm-up > {WRITE_SLOW_S} s): "
                    + ", ".join(f"`{md(c)}`" for c in r["write_slow"]) + ".", ""]
        st = r.get("stability")
        if st and st.get("error"):
            out += [f"Stability check failed: {md(st['error'])}", ""]
        elif st:
            verdict = "**UNSTABLE**: " + md("; ".join(st["reasons"])) if st["unstable"] else "Stable."
            out += [f"Stability: {md(stability_summary(st))}. {verdict}", ""]
        if r.get("warnings"):
            out += ["Warnings:"] + [f"- {md(w)}" for w in r["warnings"]] + [""]

    out += ["## Method", "",
            "- **Sample**: whole series picked by `sipHash64(<series key>)`, copied into a table with the same engine, "
            "ORDER BY, PARTITION BY and settings, then `OPTIMIZE FINAL`.",
            "- **Sizes**: per column one table with the key columns and one copy of the column per codec, filled from "
            "the sample, `OPTIMIZE FINAL`, sizes from `system.columns`. *vs current* compares with the current codec, "
            "measured the same way on the same rows.",
            "- **Read**: `SELECT <copy> FORMAT Null` with `max_threads = 1`, uncompressed and query cache off; the "
            "data is in the OS page cache, so this measures decompression, not disk.",
            "- **Write**: per codec a table with only this column and codec (plain MergeTree, no keys, the source's "
            "table settings), `INSERT … SELECT` of the column from an uncompressed copy in the order the column "
            "table stores it, `max_threads = 1`, one block = one part, `TRUNCATE` after each run. Reading the copy, "
            "squashing and writing the part cost the same for every codec (the `NONE` row shows that base); the "
            "difference between codecs is compression. Merges are not measured: they decompress and recompress "
            "each column again, plus work that is the same for every codec.",
            "- **Times**: *CPU ms* = median user + system CPU time of the query, what the codec costs the node "
            "(sums over its threads; with one thread close to busy time). *MB/s* = uncompressed bytes / median "
            "wall-clock time of the query, the speed a client sees; it also contains waiting (I/O, scheduler), so "
            "it is noisier on a busy node. Medians after one warm-up; *spread* = (max − min) / median of the "
            "CPU times. Without CPU time from the server (e.g. macOS) both use wall-clock time.",
            "- **Pareto ✓**: no other codec is at least as small and at least as fast on every measured time "
            "(median read and write CPU ms) and better on one; inherits the noise of the times.",
            "- **est. with smallest**: the column's compressed size in the source table × (smallest / current) in "
            "the sample. An extrapolation from the sample, not a measurement. *-* when the server keeps no "
            "per-column sizes for the source (compact parts).",
            "- **Stability** (if on): sizes on two disjoint halves of the sample (whole series, `cityHash64`). "
            f"Contenders = within {STABILITY_CONTENDER:g} % of the smallest codec in either half; *A/B pp* = how far "
            "a contender's size vs the smallest moves between the halves. UNSTABLE if any moves more than "
            f"{STABILITY_PP:g} pp.",
            "- Not tried: codecs the server rejected (listed per column).", "",
            f"===== codec_bench report {meta['run_id']} end ====="]
    return out


def print_report(meta, results):
    """Plain print (no timestamps) so the block between the markers is clean markdown."""
    sys.stdout.write("\n".join(render_report(meta, results)) + "\n")
    sys.stdout.flush()


def run(db, w, a, plan):
    """Everything after the dry run. Own tables are always dropped; on interrupt the running query is killed first."""
    previous = install_signal_handlers()
    meta = report_meta(w, a, plan)
    results = []
    try:
        drop_leftovers(w)
        sample, meta["sample_rows"], meta["series"] = build_sample(db, w, a, plan)
        phase2(db, w, plan, sample, meta["sample_rows"], a.read_runs, a.stability, results, a.write_runs)
        failed = [r["column"] for r in results if r.get("error")]
        unstable = [r["column"] for r in results if (r.get("stability") or {}).get("unstable")]
        log(f"Phase 2 done: {len(results) - len(failed)}/{len(results)} columns measured"
            + (f", failed: {', '.join(failed)}" if failed else "")
            + (f", unstable: {', '.join(unstable)}" if unstable else ""))
        print_report(meta, results)
        return 0
    except BaseException as e:
        ignore_signals()
        log(f"aborting: {type(e).__name__}: {e}")
        try:
            w.kill_running()
        except Exception as k:  # cleanup must go on
            log(f"KILL QUERY failed: {k}")
        if results:
            try:
                meta["aborted"] = f"{type(e).__name__}: {e}"
                print_report(meta, results)
            except Exception as r:  # a report bug must not stop the cleanup
                log(f"[WARN] partial report failed: {type(r).__name__}: {r}")
        return 130 if isinstance(e, (Interrupted, KeyboardInterrupt)) else 1
    finally:
        ignore_signals()
        for name in list(w.created):
            try:
                w.drop(name)
                log(f"dropped {w.database}.{name}")
            except Exception as e:
                log(f"[WARN] could not drop {w.database}.{name}: {e}; run --cleanup")
        restore_signal_handlers(previous)


# ---------------------------------------------------------------- CLI

def parse_args(argv=None):
    ap = argparse.ArgumentParser(description="Measure ClickHouse column codecs on a sample of a MergeTree table.")
    ap.add_argument("--host", required=True)
    ap.add_argument("--port", type=int, default=8123)
    ap.add_argument("--user", default="default")
    ap.add_argument("--database", required=True)
    ap.add_argument("--table", help="required unless --cleanup")
    ap.add_argument("--scratch-database", default="", help="where scratch tables go (default: --database)")
    ap.add_argument("--columns", type=lambda s: [x.strip() for x in s.split(",") if x.strip()])
    ap.add_argument("--where", default="")
    ap.add_argument("--sample-by", default="")
    ap.add_argument("--sample-all-columns", action="store_true",
                    help="copy all stored columns into the sample, not only the measured and key columns")
    ap.add_argument("--max-rows", type=int, default=2_000_000)
    ap.add_argument("--max-scan-rows", type=int, default=200_000_000)
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--max-memory-gb", type=float, default=8)
    ap.add_argument("--read-runs", type=int, default=3, help="read benchmark runs per codec after 1 warm-up; 0 = off")
    ap.add_argument("--write-runs", type=int, default=3,
                    help=f"write benchmark runs per codec after 1 warm-up (1 run if the warm-up takes > "
                         f"{WRITE_SLOW_S}s); 0 = off")
    ap.add_argument("--stability", action="store_true",
                    help="also measure sizes on two disjoint halves of the sample and flag unstable columns")
    ap.add_argument("--yes", action="store_true", help="run for real (default: dry run)")
    ap.add_argument("--cleanup", action="store_true", help="only drop leftover scratch tables, then exit")
    a = ap.parse_args(argv)
    if not a.cleanup and not a.table:
        ap.error("--table is required")
    if a.read_runs < 0:
        ap.error("--read-runs must be >= 0")
    if a.write_runs < 0:
        ap.error("--write-runs must be >= 0")
    return a


def main(argv=None):
    a = parse_args(argv)
    db = connect(a)
    if a.cleanup:
        host = db.rows("SELECT hostName() AS h")[0]["h"]
        w = Writer(db.client, a.scratch_database or a.database, host, run_id="cleanup")
        names = w.leftovers()
        drop_leftovers(w)
        log(f"cleanup: dropped {len(names)} table(s) on {host}")
        return 0
    log(f"Phase 0: dry run for {a.database}.{a.table}" + (f" WHERE {a.where}" if a.where else ""))
    ok, plan = dry_run(db, a)
    if not ok:
        log("dry run failed, nothing written")
        return 1
    if not a.yes:
        log("dry run OK; nothing written. Re-run with --yes to measure.")
        return 0
    run_id = new_run_id()
    log(f"run {run_id}: Phase 1 (sample) on {plan['host']}")
    w = Writer(db.client, plan["scratch_db"], plan["host"], run_id, kill_client=lambda: connect(a).client)
    return run(db, w, a, plan)


if __name__ == "__main__":
    sys.exit(main())
