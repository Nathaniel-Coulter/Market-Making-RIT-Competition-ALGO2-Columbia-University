"""
algo3_competition_engine.py
Nathaniel Coulter / Columbia MATHGR5490
RIT ALGO3 Smart Order Routing - competition engine

Purpose
-------
Race-first, full-block, cross-venue tender execution for the RIT classroom
ALGO3 simulation. This implementation is grounded in the preceding read-only
probe and one-tender write calibration rather than in untested assumptions.

Calibrated live facts used by the design
----------------------------------------
* THOR_M and THOR_A are mirrored representations of one underlying inventory.
  Never sum their position fields as independent exposures.
* Runtime limits observed in the class demo: net 100,000, gross 200,000.
  Values are rediscovered at startup and refreshed during the round.
* Main taker fee 0.010/share; Alternative taker fee 0.005/share; Alternative
  maker rebate 0.0075/share. Live security fields remain the source of truth.
* Max order size 25,000; advertised API order rate 100/s; execution delay 0 ms.
* Tender action BUY creates positive inventory and requires a SELL hedge;
  tender action SELL creates negative inventory and requires a BUY hedge. The
  booking gate still derives the hedge from the observed position sign.
* Tender inventory became stably visible about 0.31 s after acceptance in the
  calibration heat. Order detail/position reporting lagged market-order POSTs by
  roughly 0.10 s, so the competition engine DOES NOT wait between child orders.
* A reservation ledger authorizes the full hedge before the burst, preventing
  late-fill overshoot while retaining the speed advantage.
* The calibrated burst filled at the refreshed-book predicted VWAP.

Competition policy
------------------
* Continuously reevaluate each fixed tender during its decision window.
* Trigger on FULL-BLOCK, cross-venue, after-fee executable edge. Default NORMAL
  threshold is +0.05/share; ATTACK and PROTECT presets are available.
* Re-read both books immediately before irreversible acceptance.
* Wait for the actual mirrored tender inventory to book.
* Refresh the books and immediately submit the entire reducing hedge as a
  reservation-protected, price-priority, venue-aware MARKET burst.
* Reconcile afterward. Never blindly replay an ambiguous write, never increase
  tender-created exposure, and never cross through flat.
* Participant/trader_id and TAS telemetry are recorded, but unvalidated
  participant heuristics are NOT allowed to veto a valid tender or create
  independent speculative trades.

Intentional non-features in this version
----------------------------------------
* No independent cross-venue arbitrage from flat. Practice evidence suggests
  speculative-volume fines may exist.
* No passive Alternative tail and no live maker-rebate strategy yet. We did not
  calibrate post-only/partial-fill semantics.
* No ML model and no ES-trained microstructure thresholds.
* No adaptive inventory tail by default. The calibrated edge is secured first.

Safety / scope
--------------
This is for the RIT classroom simulator only. It is not production broker code.
Live writes require BOTH --live and --confirmed. GETs may retry; POST/DELETE
writes are attempted exactly once and are never blindly replayed.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import queue
import signal
import sqlite3
import statistics
import sys
import threading
import time
import uuid
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Deque, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

import requests


VERSION = "ALGO3-COMP-1.1-SHADOW"
EXPECTED_MAIN = "THOR_M"
EXPECTED_ALT = "THOR_A"
DEFAULT_PORTS = (9999, 20000)
MODE_EDGES = {"attack": 0.03, "normal": 0.05, "protect": 0.08}
DEFAULT_MIN_EDGE = MODE_EDGES["normal"]
DEFAULT_PRETRIGGER_MARGIN = 0.010
DEFAULT_MIN_SECONDS_TO_EXPIRY = 1.0
DEFAULT_MIN_SECONDS_TO_ROUND_END = 3.0
DEFAULT_MAX_ORDER = 25_000
DEFAULT_BOOK_REFRESH_S = 0.050
DEFAULT_TENDER_POLL_S = 0.050
DEFAULT_TAS_POLL_S = 0.200
DEFAULT_IDLE_POLL_S = 0.100
DEFAULT_BOOKING_POLL_S = 0.020
DEFAULT_RECONCILE_POLL_S = 0.030
DEFAULT_BOOKING_TIMEOUT_S = 3.0
DEFAULT_RECONCILE_TIMEOUT_S = 4.0
DEFAULT_ACCOUNTING_SETTLE_S = 0.30
DEFAULT_CONFIG_REFRESH_S = 1.0
DEFAULT_TRADER_REFRESH_S = 0.50
DEFAULT_MAX_REPAIR_ROUNDS = 3
DEFAULT_MAX_BOOK_AGE_S = 0.150
DEFAULT_REVALIDATE_COOLDOWN_S = 0.150
SHADOW_HORIZONS_S = (0.25, 0.50, 1.0, 2.0, 5.0, 10.0, 15.0, 20.0)
SHADOW_EDGE_LEVELS = (0.00, 0.02, 0.03, 0.05, 0.08, 0.10)
POSITION_TOLERANCE = 0

stop_requested = threading.Event()
execution_in_progress = threading.Event()


# =============================================================================
# GENERIC HELPERS
# =============================================================================

def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def run_stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def mono_ns() -> int:
    return time.perf_counter_ns()


def safe_float(x: Any) -> Optional[float]:
    try:
        if x is None:
            return None
        v = float(x)
        return v if math.isfinite(v) else None
    except (TypeError, ValueError, OverflowError):
        return None


def safe_int(x: Any) -> Optional[int]:
    try:
        if x is None:
            return None
        return int(round(float(x)))
    except (TypeError, ValueError, OverflowError):
        return None


def as_int(x: Any, default: int = 0) -> int:
    v = safe_int(x)
    return default if v is None else v


def as_float(x: Any, default: float = 0.0) -> float:
    v = safe_float(x)
    return default if v is None else v


def safe_div(a: Any, b: Any) -> Optional[float]:
    aa = safe_float(a); bb = safe_float(b)
    if aa is None or bb is None or abs(bb) < 1e-15:
        return None
    return aa / bb


def canonical_json(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str)


def pretty_money(x: Optional[float]) -> str:
    if x is None:
        return "N/A"
    return f"${x:,.2f}"


def percentile(values: Sequence[float], q: float) -> Optional[float]:
    vals = sorted(float(v) for v in values if v is not None and math.isfinite(float(v)))
    if not vals:
        return None
    if len(vals) == 1:
        return vals[0]
    pos = (len(vals) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return vals[lo]
    w = pos - lo
    return vals[lo] * (1.0 - w) + vals[hi] * w


def mean_or_none(values: Sequence[float]) -> Optional[float]:
    vals = [float(v) for v in values if v is not None and math.isfinite(float(v))]
    return statistics.fmean(vals) if vals else None


def opposite(action: str) -> str:
    a = str(action).upper()
    if a == "BUY":
        return "SELL"
    if a == "SELL":
        return "BUY"
    raise ValueError(f"Unknown action: {action!r}")


def locate_algo3_root() -> Path:
    here = Path(__file__).resolve().parent
    if here.name.lower() in {"src", "pipeline"}:
        return here.parent
    for p in [here] + list(here.parents):
        if (p / "outputs").exists() and ((p / "src").exists() or (p / "pipeline").exists()):
            return p
    return here.parent


def parse_retry_after(resp: requests.Response) -> float:
    raw = resp.headers.get("Retry-After")
    v = safe_float(raw)
    if v is not None and v > 0:
        return min(v, 2.0)
    try:
        body = resp.json()
        for k in ("wait", "retry_after", "retryAfter"):
            v = safe_float(body.get(k)) if isinstance(body, Mapping) else None
            if v is not None and v > 0:
                return min(v, 2.0)
    except Exception:
        pass
    return 0.10


def content_json_or_text(resp: requests.Response) -> Any:
    if not resp.content:
        return {}
    try:
        return resp.json()
    except Exception:
        try:
            return resp.text
        except Exception:
            return None


def visible_order_status(order: Mapping[str, Any]) -> str:
    return str(order.get("status") or order.get("state") or "").upper()


def order_is_terminal(order: Mapping[str, Any]) -> bool:
    return visible_order_status(order) in {
        "TRANSACTED", "FILLED", "CANCELLED", "CANCELED", "REJECTED", "EXPIRED"
    }


def order_requested_qty(order: Mapping[str, Any]) -> int:
    for k in ("quantity", "quantity_requested", "original_quantity"):
        v = safe_int(order.get(k))
        if v is not None:
            return max(0, v)
    return 0


def order_filled_qty(order: Mapping[str, Any]) -> int:
    for k in ("quantity_filled", "filled", "filled_quantity", "quantityFilled"):
        v = safe_int(order.get(k))
        if v is not None:
            return max(0, v)
    # Some RIT versions expose remaining quantity instead.
    req = order_requested_qty(order)
    for k in ("quantity_remaining", "remaining", "remaining_quantity"):
        rem = safe_int(order.get(k))
        if rem is not None and req > 0:
            return max(0, req - rem)
    return req if visible_order_status(order) in {"TRANSACTED", "FILLED"} else 0


def order_vwap(order: Mapping[str, Any]) -> Optional[float]:
    for k in ("vwap", "average_price", "avg_price", "fill_price", "price"):
        v = safe_float(order.get(k))
        if v is not None:
            return v
    return None


# =============================================================================
# SINGLE-INSTANCE LOCK
# =============================================================================

class InstanceLock:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.fp = None

    def acquire(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.fp = open(self.path, "a+b")
        self.fp.seek(0)
        self.fp.write(b"0")
        self.fp.flush()
        if os.name == "nt":
            import msvcrt
            self.fp.seek(0)
            try:
                msvcrt.locking(self.fp.fileno(), msvcrt.LK_NBLCK, 1)
            except OSError as exc:
                raise RuntimeError(
                    f"Another ALGO3 write-capable process appears to hold {self.path}. "
                    "Run only one write-capable process."
                ) from exc
        else:
            import fcntl
            try:
                fcntl.flock(self.fp.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError as exc:
                raise RuntimeError(
                    f"Another ALGO3 write-capable process appears to hold {self.path}."
                ) from exc
        self.fp.seek(0)
        self.fp.truncate()
        self.fp.write(f"pid={os.getpid()} started={utc_now()}\n".encode())
        self.fp.flush()

    def release(self) -> None:
        if self.fp is None:
            return
        try:
            if os.name == "nt":
                import msvcrt
                self.fp.seek(0)
                try:
                    msvcrt.locking(self.fp.fileno(), msvcrt.LK_UNLCK, 1)
                except OSError:
                    pass
            else:
                import fcntl
                try:
                    fcntl.flock(self.fp.fileno(), fcntl.LOCK_UN)
                except OSError:
                    pass
        finally:
            try:
                self.fp.close()
            except Exception:
                pass
            self.fp = None


# =============================================================================
# BACKGROUND JOURNAL
# =============================================================================

SCHEMA = """
PRAGMA journal_mode=WAL;
PRAGMA synchronous=NORMAL;

CREATE TABLE IF NOT EXISTS metadata (
    key TEXT PRIMARY KEY,
    value_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    mono_ns INTEGER NOT NULL,
    kind TEXT NOT NULL,
    tick INTEGER,
    tender_id INTEGER,
    order_id INTEGER,
    payload_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS http_samples (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    mono_ns INTEGER NOT NULL,
    method TEXT NOT NULL,
    endpoint TEXT NOT NULL,
    status_code INTEGER,
    latency_ms REAL,
    response_bytes INTEGER,
    ambiguous INTEGER NOT NULL,
    error TEXT
);

CREATE TABLE IF NOT EXISTS books (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    mono_ns INTEGER NOT NULL,
    tick INTEGER,
    phase TEXT NOT NULL,
    ticker TEXT NOT NULL,
    best_bid REAL,
    best_ask REAL,
    raw_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS position_samples (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    mono_ns INTEGER NOT NULL,
    tick INTEGER,
    phase TEXT NOT NULL,
    position_m INTEGER,
    position_a INTEGER,
    realized_m REAL,
    realized_a REAL,
    unrealized_m REAL,
    unrealized_a REAL,
    nlv REAL,
    fines REAL,
    limits_json TEXT,
    securities_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS order_events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    mono_ns INTEGER NOT NULL,
    tick INTEGER,
    phase TEXT NOT NULL,
    order_id INTEGER,
    ticker TEXT,
    action TEXT,
    requested_qty INTEGER,
    filled_qty INTEGER,
    status TEXT,
    vwap REAL,
    submit_latency_ms REAL,
    raw_json TEXT
);

CREATE TABLE IF NOT EXISTS tender_evaluations (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    mono_ns INTEGER NOT NULL,
    round_index INTEGER NOT NULL,
    tick INTEGER,
    tender_id INTEGER NOT NULL,
    tender_action TEXT,
    hedge_action TEXT,
    quantity INTEGER,
    tender_price REAL,
    seconds_to_expiry REAL,
    source TEXT NOT NULL,
    full_coverage INTEGER NOT NULL,
    filled_qty INTEGER,
    edge_per_share REAL,
    modeled_profit REAL,
    route_participant_share REAL,
    raw_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS market_features (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    mono_ns INTEGER NOT NULL,
    round_index INTEGER NOT NULL,
    tick INTEGER,
    ticker TEXT NOT NULL,
    side TEXT NOT NULL,
    best_price REAL,
    total_qty INTEGER,
    participant_qty INTEGER,
    anon_qty INTEGER,
    unknown_qty INTEGER,
    participant_share REAL,
    participant_orders INTEGER,
    anon_orders INTEGER,
    median_participant_age_ms REAL,
    median_anon_age_ms REAL,
    raw_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS tas_trades (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    mono_ns INTEGER NOT NULL,
    round_index INTEGER NOT NULL,
    ticker TEXT NOT NULL,
    trade_key TEXT NOT NULL,
    price REAL,
    quantity REAL,
    action TEXT,
    raw_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS shadow_paths (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    mono_ns INTEGER NOT NULL,
    round_index INTEGER NOT NULL,
    tick INTEGER,
    tender_id INTEGER NOT NULL,
    horizon_s REAL NOT NULL,
    elapsed_s REAL NOT NULL,
    edge_per_share REAL,
    modeled_profit REAL,
    full_coverage INTEGER NOT NULL,
    route_participant_share REAL,
    best_global_bid REAL,
    best_global_ask REAL,
    raw_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS trade_summaries (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id TEXT NOT NULL,
    ts_utc TEXT NOT NULL,
    round_index INTEGER NOT NULL,
    tender_id INTEGER NOT NULL,
    tender_action TEXT,
    hedge_action TEXT,
    quantity INTEGER,
    tender_price REAL,
    trigger_edge REAL,
    trigger_profit REAL,
    prehedge_edge REAL,
    prehedge_profit REAL,
    accept_latency_ms REAL,
    booking_ms REAL,
    burst_orders INTEGER,
    burst_submit_span_ms REAL,
    repairs INTEGER,
    final_position INTEGER,
    realized_delta REAL,
    nlv_delta REAL,
    fines_delta REAL,
    success INTEGER NOT NULL,
    reason TEXT,
    payload_json TEXT NOT NULL
);
"""


class Journal:
    def __init__(self, out_dir: Path, run_id: str) -> None:
        self.out_dir = out_dir
        self.run_id = run_id
        self.sqlite_path = out_dir / "algo3_competition.sqlite"
        self.jsonl_path = out_dir / "algo3_competition.jsonl"
        self.q: queue.Queue = queue.Queue(maxsize=200_000)
        self.stop_evt = threading.Event()
        self.thread = threading.Thread(target=self._worker, daemon=True, name="journal-writer")
        self.thread.start()

    def put(self, table: str, row: Mapping[str, Any], jsonl: bool = True) -> None:
        item = (table, dict(row), jsonl)
        try:
            self.q.put_nowait(item)
        except queue.Full:
            # Calibration data should never silently disappear. Block briefly rather
            # than dropping write-path observations.
            self.q.put(item, timeout=1.0)

    def event(
        self,
        kind: str,
        payload: Mapping[str, Any],
        *,
        tick: Optional[int] = None,
        tender_id: Optional[int] = None,
        order_id: Optional[int] = None,
    ) -> None:
        self.put(
            "events",
            {
                "run_id": self.run_id,
                "ts_utc": utc_now(),
                "mono_ns": mono_ns(),
                "kind": kind,
                "tick": tick,
                "tender_id": tender_id,
                "order_id": order_id,
                "payload_json": canonical_json(payload),
            },
            jsonl=True,
        )

    def close(self) -> None:
        self.stop_evt.set()
        self.thread.join(timeout=10.0)

    def _worker(self) -> None:
        self.out_dir.mkdir(parents=True, exist_ok=True)
        con = sqlite3.connect(self.sqlite_path, timeout=30.0)
        con.executescript(SCHEMA)
        con.commit()
        jf = open(self.jsonl_path, "a", encoding="utf-8")
        batch = 0
        try:
            while not self.stop_evt.is_set() or not self.q.empty():
                try:
                    table, row, mirror = self.q.get(timeout=0.10)
                except queue.Empty:
                    if batch:
                        con.commit()
                        batch = 0
                    continue

                cols = list(row.keys())
                vals = [row[c] for c in cols]
                placeholders = ",".join("?" for _ in cols)
                con.execute(
                    f"INSERT INTO {table} ({','.join(cols)}) VALUES ({placeholders})",
                    vals,
                )
                batch += 1

                if mirror:
                    jf.write(canonical_json({"table": table, "row": row}) + "\n")
                    jf.flush()

                if batch >= 100:
                    con.commit()
                    batch = 0
        finally:
            try:
                con.commit()
            finally:
                con.close()
                jf.close()


# =============================================================================
# HTTP CLIENT: SAFE GET RETRY, NO BLIND WRITE RETRY
# =============================================================================

@dataclass
class WriteResult:
    response: Optional[requests.Response]
    body: Any
    latency_ms: Optional[float]
    ambiguous: bool
    error: Optional[str]


class RITClient:
    def __init__(self, base_url: str, api_key: str, journal: Journal, timeout_s: float = 1.5) -> None:
        self.base_url = base_url.rstrip("/")
        self.api_key = api_key
        self.journal = journal
        self.timeout_s = timeout_s
        self.local = threading.local()
        self.write_lock = threading.Lock()

    def _session(self) -> requests.Session:
        s = getattr(self.local, "session", None)
        if s is None:
            s = requests.Session()
            s.trust_env = False
            s.headers.update({"X-API-Key": self.api_key})
            self.local.session = s
        return s

    def _log_http(
        self,
        method: str,
        endpoint: str,
        status: Optional[int],
        latency_ms: Optional[float],
        nbytes: int,
        ambiguous: bool,
        error: Optional[str],
    ) -> None:
        self.journal.put(
            "http_samples",
            {
                "run_id": self.journal.run_id,
                "ts_utc": utc_now(),
                "mono_ns": mono_ns(),
                "method": method,
                "endpoint": endpoint,
                "status_code": status,
                "latency_ms": latency_ms,
                "response_bytes": nbytes,
                "ambiguous": int(bool(ambiguous)),
                "error": error,
            },
            jsonl=False,
        )

    def get(
        self,
        path: str,
        params: Optional[Mapping[str, Any]] = None,
        retries: int = 4,
        allow_404: bool = False,
    ) -> Tuple[Any, requests.Response, float]:
        last_exc: Optional[Exception] = None
        for attempt in range(max(1, retries)):
            started = time.perf_counter()
            try:
                r = self._session().get(
                    self.base_url + path,
                    params=dict(params or {}),
                    timeout=self.timeout_s,
                )
                latency = (time.perf_counter() - started) * 1000.0
                self._log_http("GET", path, r.status_code, latency, len(r.content or b""), False, None)
                if r.status_code == 429:
                    time.sleep(parse_retry_after(r))
                    continue
                if r.status_code == 401:
                    raise RuntimeError("401 Unauthorized: refresh/set RIT_API_KEY from the RIT API panel.")
                if r.status_code == 404 and allow_404:
                    return None, r, latency
                r.raise_for_status()
                return content_json_or_text(r), r, latency
            except RuntimeError:
                raise
            except requests.RequestException as exc:
                latency = (time.perf_counter() - started) * 1000.0
                self._log_http("GET", path, None, latency, 0, False, f"{type(exc).__name__}: {exc}")
                last_exc = exc
                time.sleep(min(0.02 * (2 ** attempt), 0.20))
        raise RuntimeError(f"GET {path} failed after retries: {last_exc}")

    def write_once(
        self,
        method: str,
        path: str,
        params: Optional[Mapping[str, Any]] = None,
    ) -> WriteResult:
        """Exactly one network write attempt. Never retries automatically."""
        method = method.upper()
        if method not in {"POST", "DELETE"}:
            raise ValueError("write_once supports POST or DELETE only")
        started = time.perf_counter()
        with self.write_lock:
            try:
                if method == "POST":
                    r = self._session().post(
                        self.base_url + path,
                        params=dict(params or {}),
                        timeout=self.timeout_s,
                    )
                else:
                    r = self._session().delete(
                        self.base_url + path,
                        params=dict(params or {}),
                        timeout=self.timeout_s,
                    )
                latency = (time.perf_counter() - started) * 1000.0
                body = content_json_or_text(r)
                # HTTP response exists => not transport-ambiguous, even if rejected.
                self._log_http(method, path, r.status_code, latency, len(r.content or b""), False, None)
                return WriteResult(r, body, latency, False, None)
            except requests.RequestException as exc:
                latency = (time.perf_counter() - started) * 1000.0
                err = f"{type(exc).__name__}: {exc}"
                self._log_http(method, path, None, latency, 0, True, err)
                return WriteResult(None, None, latency, True, err)


# =============================================================================
# CASE / SECURITY / BOOK HELPERS
# =============================================================================

@dataclass(frozen=True)
class PriceLevel:
    price: float
    quantity: int
    raw_rows: Tuple[Dict[str, Any], ...] = field(default_factory=tuple)


@dataclass
class ParsedBook:
    ticker: str
    bids: List[PriceLevel]
    asks: List[PriceLevel]
    raw: Dict[str, Any]
    observed_ns: int
    latency_ms: float


def available_qty(row: Mapping[str, Any]) -> int:
    # RIT book rows normally expose quantity and quantity_filled. Be defensive.
    q = safe_float(row.get("quantity"))
    if q is None:
        q = safe_float(row.get("size"))
    if q is None:
        q = safe_float(row.get("volume"))
    if q is None:
        return 0
    filled = safe_float(row.get("quantity_filled"))
    if filled is None:
        filled = safe_float(row.get("filled")) or 0.0
    return max(0, int(round(q - filled)))


def aggregate_rows_by_price(rows: Sequence[Mapping[str, Any]], reverse: bool) -> List[PriceLevel]:
    qty_by_price: Dict[float, int] = defaultdict(int)
    raw_by_price: Dict[float, List[Dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if not isinstance(row, Mapping):
            continue
        p = safe_float(row.get("price"))
        q = available_qty(row)
        if p is None or q <= 0:
            continue
        qty_by_price[p] += q
        raw_by_price[p].append(dict(row))
    return [
        PriceLevel(price=p, quantity=qty_by_price[p], raw_rows=tuple(raw_by_price[p]))
        for p in sorted(qty_by_price, reverse=reverse)
    ]


def parse_book(ticker: str, raw: Any, observed_ns: int, latency_ms: float) -> ParsedBook:
    d = dict(raw) if isinstance(raw, Mapping) else {}
    return ParsedBook(
        ticker=ticker,
        bids=aggregate_rows_by_price(d.get("bids") or [], reverse=True),
        asks=aggregate_rows_by_price(d.get("asks") or [], reverse=False),
        raw=d,
        observed_ns=observed_ns,
        latency_ms=latency_ms,
    )


def security_map(raw: Any) -> Dict[str, Dict[str, Any]]:
    out: Dict[str, Dict[str, Any]] = {}
    if isinstance(raw, Sequence) and not isinstance(raw, (str, bytes)):
        for row in raw:
            if isinstance(row, Mapping) and row.get("ticker"):
                out[str(row["ticker"])] = dict(row)
    return out


def positions_from_securities(raw: Any) -> Dict[str, int]:
    sm = security_map(raw)
    return {
        EXPECTED_MAIN: as_int(sm.get(EXPECTED_MAIN, {}).get("position"), 0),
        EXPECTED_ALT: as_int(sm.get(EXPECTED_ALT, {}).get("position"), 0),
    }


def realized_from_security(sec: Mapping[str, Any]) -> Optional[float]:
    for k in ("realized", "realized_pl", "realized_pnl"):
        v = safe_float(sec.get(k))
        if v is not None:
            return v
    return None


def unrealized_from_security(sec: Mapping[str, Any]) -> Optional[float]:
    for k in ("unrealized", "unrealized_pl", "unrealized_pnl"):
        v = safe_float(sec.get(k))
        if v is not None:
            return v
    return None


def trader_nlv(raw: Any) -> Optional[float]:
    if not isinstance(raw, Mapping):
        return None
    for k in ("nlv", "net_liquidation", "net_liquidation_value"):
        v = safe_float(raw.get(k))
        if v is not None:
            return v
    return None


def trader_fines(raw: Any) -> Optional[float]:
    if not isinstance(raw, Mapping):
        return None
    for k in ("fines", "fine"):
        v = safe_float(raw.get(k))
        if v is not None:
            return v
    return None


def security_fee(sec: Mapping[str, Any]) -> Optional[float]:
    for k in ("trading_fee", "fee", "market_order_fee", "take_fee"):
        v = safe_float(sec.get(k))
        if v is not None:
            return v
    return None


def security_rebate(sec: Mapping[str, Any]) -> Optional[float]:
    for k in ("limit_order_rebate", "rebate", "maker_rebate"):
        v = safe_float(sec.get(k))
        if v is not None:
            return v
    return None


def security_max_order(sec: Mapping[str, Any]) -> Optional[int]:
    for k in ("max_trade_size", "max_order_size", "maximum_order_size"):
        v = safe_int(sec.get(k))
        if v is not None:
            return v
    return None


def security_api_rate(sec: Mapping[str, Any]) -> Optional[float]:
    for k in ("api_orders_per_second", "api_rate", "order_rate_limit"):
        v = safe_float(sec.get(k))
        if v is not None:
            return v
    return None


def security_exec_delay_ms(sec: Mapping[str, Any]) -> Optional[float]:
    for k in ("execution_delay_ms", "execution_delay", "exec_delay_ms"):
        v = safe_float(sec.get(k))
        if v is not None:
            return v
    return None


def is_open_order(order: Mapping[str, Any]) -> bool:
    st = visible_order_status(order)
    return st in {"OPEN", "PENDING", "PARTIAL", "PARTIALLY_FILLED"}


def open_thor_orders(raw: Any) -> List[Dict[str, Any]]:
    if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes)):
        return []
    out = []
    for row in raw:
        if not isinstance(row, Mapping):
            continue
        if str(row.get("ticker") or "") not in {EXPECTED_MAIN, EXPECTED_ALT}:
            continue
        if is_open_order(row):
            out.append(dict(row))
    return out


def raw_best(book: ParsedBook) -> Tuple[Optional[float], Optional[float]]:
    bid = book.bids[0].price if book.bids else None
    ask = book.asks[0].price if book.asks else None
    return bid, ask


def record_book(journal: Journal, book: ParsedBook, tick: Optional[int], phase: str) -> None:
    bid, ask = raw_best(book)
    journal.put(
        "books",
        {
            "run_id": journal.run_id,
            "ts_utc": utc_now(),
            "mono_ns": book.observed_ns,
            "tick": tick,
            "phase": phase,
            "ticker": book.ticker,
            "best_bid": bid,
            "best_ask": ask,
            "raw_json": canonical_json(book.raw),
        },
        jsonl=False,
    )


def fetch_book(client: RITClient, ticker: str) -> ParsedBook:
    raw, _, lat = client.get("/securities/book", {"ticker": ticker, "limit": 100})
    return parse_book(ticker, raw, mono_ns(), lat)


def fetch_book_pair(client: RITClient) -> Dict[str, ParsedBook]:
    # Near-synchronous reads. RIT probe showed ~1-2 ms book RTT; separate thread-local
    # sessions avoid sharing requests.Session concurrently.
    with ThreadPoolExecutor(max_workers=2) as ex:
        fm = ex.submit(fetch_book, client, EXPECTED_MAIN)
        fa = ex.submit(fetch_book, client, EXPECTED_ALT)
        bm = fm.result()
        ba = fa.result()
    return {EXPECTED_MAIN: bm, EXPECTED_ALT: ba}


# =============================================================================
# GLOBAL SOR / TENDER ECONOMICS
# =============================================================================

def route_entries(books: Mapping[str, ParsedBook], hedge_action: str, fees: Mapping[str, float]) -> List[Tuple[float, int, str]]:
    buying = hedge_action.upper() == "BUY"
    rows: List[Tuple[float, int, str]] = []
    for ticker, book in books.items():
        levels = book.asks if buying else book.bids
        for lv in levels:
            rows.append((lv.price, lv.quantity, ticker))
    # Case brief/skeleton intent: respect raw NBBO first; fee breaks raw-price ties.
    if buying:
        rows.sort(key=lambda x: (x[0], fees.get(x[2], 0.0), x[2]))
    else:
        rows.sort(key=lambda x: (-x[0], fees.get(x[2], 0.0), x[2]))
    return rows


def walk_route(
    books: Mapping[str, ParsedBook],
    qty: int,
    hedge_action: str,
    fees: Mapping[str, float],
) -> Dict[str, Any]:
    buying = hedge_action.upper() == "BUY"
    remaining = int(qty)
    raw_notional = 0.0
    effective_notional = 0.0
    plan: List[Dict[str, Any]] = []
    per_market: Dict[str, int] = defaultdict(int)

    for price, available, ticker in route_entries(books, hedge_action, fees):
        if remaining <= 0:
            break
        take = min(remaining, int(available))
        if take <= 0:
            continue
        fee = float(fees.get(ticker, 0.0))
        effective = price + fee if buying else price - fee
        raw_notional += price * take
        effective_notional += effective * take
        per_market[ticker] += take
        plan.append(
            {
                "ticker": ticker,
                "action": hedge_action.upper(),
                "price": price,
                "available": int(available),
                "take": int(take),
                "fee": fee,
                "effective_price": effective,
            }
        )
        remaining -= take

    filled = qty - remaining
    raw_vwap = raw_notional / filled if filled else None
    eff_vwap = effective_notional / filled if filled else None
    return {
        "action": hedge_action.upper(),
        "requested_qty": int(qty),
        "filled_qty": int(filled),
        "residual_qty": int(remaining),
        "full_coverage": remaining == 0,
        "raw_vwap": raw_vwap,
        "effective_vwap": eff_vwap,
        "per_market": dict(per_market),
        "plan": plan,
    }


def tender_economics(tender: Mapping[str, Any], route: Mapping[str, Any]) -> Dict[str, Any]:
    tender_price = as_float(tender.get("price"))
    hedge_action = str(route.get("action") or "").upper()
    eff = safe_float(route.get("effective_vwap"))
    edge = None
    if eff is not None:
        if hedge_action == "SELL":
            # We bought tender inventory and sell it back to market.
            edge = eff - tender_price
        elif hedge_action == "BUY":
            # We sold tender inventory and buy it back from market.
            edge = tender_price - eff
    qty = as_int(tender.get("quantity"))
    return {
        **dict(route),
        "tender_id": as_int(tender.get("tender_id")),
        "tender_action": str(tender.get("action") or "").upper(),
        "tender_price": tender_price,
        "edge_per_share": edge,
        "modeled_profit": edge * qty if edge is not None and route.get("full_coverage") else None,
    }


def compress_global_plan(plan: Sequence[Mapping[str, Any]], max_order: int) -> List[Dict[str, Any]]:
    """
    Preserve the global route's price/venue sequence while compressing consecutive
    same-venue segments into the fewest legal children. We intentionally do NOT merge
    same-venue segments separated by a better-priced level on the other venue.
    """
    out: List[Dict[str, Any]] = []
    current: Optional[Dict[str, Any]] = None

    def flush() -> None:
        nonlocal current
        if current is not None and current["quantity"] > 0:
            out.append(current)
        current = None

    for level in plan:
        ticker = str(level["ticker"])
        action = str(level["action"]).upper()
        qty = int(level["take"])
        price = float(level["price"])
        while qty > 0:
            if current is None or current["ticker"] != ticker or current["action"] != action:
                flush()
                current = {
                    "ticker": ticker,
                    "action": action,
                    "quantity": 0,
                    "planned_best_price": price,
                    "planned_worst_price": price,
                }
            room = max_order - int(current["quantity"])
            if room <= 0:
                flush()
                continue
            take = min(qty, room)
            current["quantity"] += take
            current["planned_worst_price"] = price
            qty -= take
            if current["quantity"] >= max_order:
                flush()
    flush()
    return out


# =============================================================================
# REQUEST / STATE SAMPLING
# =============================================================================

@dataclass
class PositionSnapshot:
    ts_ns: int
    tick: Optional[int]
    m: int
    a: int
    realized_m: Optional[float]
    realized_a: Optional[float]
    unrealized_m: Optional[float]
    unrealized_a: Optional[float]
    nlv: Optional[float]
    fines: Optional[float]
    limits: Any
    securities: Any


def get_case(client: RITClient) -> Dict[str, Any]:
    raw, _, _ = client.get("/case")
    return dict(raw) if isinstance(raw, Mapping) else {}


def get_tenders(client: RITClient) -> List[Dict[str, Any]]:
    raw, _, _ = client.get("/tenders")
    if isinstance(raw, Sequence) and not isinstance(raw, (str, bytes)):
        return [dict(x) for x in raw if isinstance(x, Mapping)]
    return []


def get_securities(client: RITClient) -> List[Dict[str, Any]]:
    raw, _, _ = client.get("/securities")
    if isinstance(raw, Sequence) and not isinstance(raw, (str, bytes)):
        return [dict(x) for x in raw if isinstance(x, Mapping)]
    return []


def get_orders(client: RITClient) -> List[Dict[str, Any]]:
    raw, _, _ = client.get("/orders")
    if isinstance(raw, Sequence) and not isinstance(raw, (str, bytes)):
        return [dict(x) for x in raw if isinstance(x, Mapping)]
    return []


def get_limits(client: RITClient) -> Any:
    raw, _, _ = client.get("/limits")
    return raw


def get_trader(client: RITClient) -> Dict[str, Any]:
    raw, _, _ = client.get("/trader")
    return dict(raw) if isinstance(raw, Mapping) else {}


def get_order_detail(client: RITClient, order_id: int) -> Optional[Dict[str, Any]]:
    raw, resp, _ = client.get(f"/orders/{int(order_id)}", allow_404=True, retries=2)
    if resp.status_code == 404:
        return None
    return dict(raw) if isinstance(raw, Mapping) else None


def sample_position(client: RITClient, journal: Journal, phase: str, include_limits: bool = False) -> PositionSnapshot:
    sec = get_securities(client)
    sm = security_map(sec)
    trader = get_trader(client)
    limits = get_limits(client) if include_limits else None
    case = get_case(client)
    snap = PositionSnapshot(
        ts_ns=mono_ns(),
        tick=safe_int(case.get("tick")),
        m=as_int(sm.get(EXPECTED_MAIN, {}).get("position"), 0),
        a=as_int(sm.get(EXPECTED_ALT, {}).get("position"), 0),
        realized_m=realized_from_security(sm.get(EXPECTED_MAIN, {})),
        realized_a=realized_from_security(sm.get(EXPECTED_ALT, {})),
        unrealized_m=unrealized_from_security(sm.get(EXPECTED_MAIN, {})),
        unrealized_a=unrealized_from_security(sm.get(EXPECTED_ALT, {})),
        nlv=trader_nlv(trader),
        fines=trader_fines(trader),
        limits=limits,
        securities=sec,
    )
    journal.put(
        "position_samples",
        {
            "run_id": journal.run_id,
            "ts_utc": utc_now(),
            "mono_ns": snap.ts_ns,
            "tick": snap.tick,
            "phase": phase,
            "position_m": snap.m,
            "position_a": snap.a,
            "realized_m": snap.realized_m,
            "realized_a": snap.realized_a,
            "unrealized_m": snap.unrealized_m,
            "unrealized_a": snap.unrealized_a,
            "nlv": snap.nlv,
            "fines": snap.fines,
            "limits_json": canonical_json(limits) if limits is not None else None,
            "securities_json": canonical_json(sec),
        },
        jsonl=False,
    )
    return snap


def sample_position_fast(
    client: RITClient,
    journal: Journal,
    phase: str,
    tick: Optional[int] = None,
) -> PositionSnapshot:
    """High-frequency position sampler: ONE GET (/securities) per observation.

    During booking/fill calibration we deliberately do not call /trader or /case on
    every 20-30 ms poll; that would multiply request load and distort the very latency
    we are trying to measure. Full accounting snapshots are taken before/after.
    """
    sec = get_securities(client)
    sm = security_map(sec)
    snap = PositionSnapshot(
        ts_ns=mono_ns(),
        tick=tick,
        m=as_int(sm.get(EXPECTED_MAIN, {}).get("position"), 0),
        a=as_int(sm.get(EXPECTED_ALT, {}).get("position"), 0),
        realized_m=realized_from_security(sm.get(EXPECTED_MAIN, {})),
        realized_a=realized_from_security(sm.get(EXPECTED_ALT, {})),
        unrealized_m=unrealized_from_security(sm.get(EXPECTED_MAIN, {})),
        unrealized_a=unrealized_from_security(sm.get(EXPECTED_ALT, {})),
        nlv=None,
        fines=None,
        limits=None,
        securities=sec,
    )
    journal.put(
        "position_samples",
        {
            "run_id": journal.run_id, "ts_utc": utc_now(), "mono_ns": snap.ts_ns,
            "tick": tick, "phase": phase, "position_m": snap.m, "position_a": snap.a,
            "realized_m": snap.realized_m, "realized_a": snap.realized_a,
            "unrealized_m": snap.unrealized_m, "unrealized_a": snap.unrealized_a,
            "nlv": None, "fines": None, "limits_json": None,
            "securities_json": canonical_json(sec),
        },
        jsonl=False,
    )
    return snap


# =============================================================================
# PREFLIGHT / DISCOVERY
# =============================================================================

def discover_base_url(api_key: str) -> str:
    errors = []
    for port in DEFAULT_PORTS:
        url = f"http://localhost:{port}/v1"
        try:
            s = requests.Session()
            s.trust_env = False
            s.headers.update({"X-API-Key": api_key})
            r = s.get(url + "/case", timeout=0.50)
            if r.status_code == 200:
                return url
            errors.append(f"{url}: HTTP {r.status_code}")
        except Exception as exc:
            errors.append(f"{url}: {type(exc).__name__}: {exc}")
    raise RuntimeError("Could not locate local RIT REST API. " + " | ".join(errors))


@dataclass
class RuntimeConfig:
    fees: Dict[str, float]
    rebates: Dict[str, float]
    max_order: int
    api_rate: Optional[float]
    exec_delay_ms: Optional[float]
    gross_limit: Optional[int]
    net_limit: Optional[int]
    securities: Dict[str, Dict[str, Any]]


def discover_runtime_config(client: RITClient) -> RuntimeConfig:
    sec_raw = get_securities(client)
    sm = security_map(sec_raw)
    missing = {EXPECTED_MAIN, EXPECTED_ALT} - set(sm)
    if missing:
        raise RuntimeError(f"Expected THOR securities missing: {sorted(missing)}; got {sorted(sm)}")

    fees = {
        EXPECTED_MAIN: security_fee(sm[EXPECTED_MAIN]),
        EXPECTED_ALT: security_fee(sm[EXPECTED_ALT]),
    }
    # Fail if live fee fields are unavailable rather than silently guessing for a write test.
    if fees[EXPECTED_MAIN] is None or fees[EXPECTED_ALT] is None:
        raise RuntimeError(f"Live fee fields unavailable: {fees}")
    fee_map = {k: float(v) for k, v in fees.items() if v is not None}
    rebates = {
        EXPECTED_MAIN: security_rebate(sm[EXPECTED_MAIN]) or 0.0,
        EXPECTED_ALT: security_rebate(sm[EXPECTED_ALT]) or 0.0,
    }

    max_candidates = [security_max_order(sm[t]) for t in (EXPECTED_MAIN, EXPECTED_ALT)]
    max_candidates = [x for x in max_candidates if x is not None]
    max_order = min(max_candidates) if max_candidates else DEFAULT_MAX_ORDER

    rate_candidates = [security_api_rate(sm[t]) for t in (EXPECTED_MAIN, EXPECTED_ALT)]
    rate_candidates = [x for x in rate_candidates if x is not None]
    api_rate = min(rate_candidates) if rate_candidates else None

    delay_candidates = [security_exec_delay_ms(sm[t]) for t in (EXPECTED_MAIN, EXPECTED_ALT)]
    delay_candidates = [x for x in delay_candidates if x is not None]
    exec_delay = max(delay_candidates) if delay_candidates else None

    limits = get_limits(client)
    gross_lim = None
    net_lim = None
    if isinstance(limits, Sequence) and not isinstance(limits, (str, bytes)):
        for row in limits:
            if isinstance(row, Mapping):
                g = safe_int(row.get("gross_limit"))
                n = safe_int(row.get("net_limit"))
                if g is not None:
                    gross_lim = g if gross_lim is None else min(gross_lim, g)
                if n is not None:
                    net_lim = n if net_lim is None else min(net_lim, n)

    return RuntimeConfig(
        fees=fee_map,
        rebates={k: float(v) for k, v in rebates.items()},
        max_order=int(max_order),
        api_rate=api_rate,
        exec_delay_ms=exec_delay,
        gross_limit=gross_lim,
        net_limit=net_lim,
        securities=sm,
    )


def validate_clean_start(client: RITClient, cfg: RuntimeConfig) -> Tuple[PositionSnapshot, List[Dict[str, Any]]]:
    # Dummy journal-free snapshot equivalent for preflight.
    sec = get_securities(client)
    pos = positions_from_securities(sec)
    orders = get_orders(client)
    opens = open_thor_orders(orders)
    if pos[EXPECTED_MAIN] != 0 or pos[EXPECTED_ALT] != 0:
        raise RuntimeError(f"Calibration requires flat start. Positions: {pos}")
    if opens:
        raise RuntimeError(f"Calibration requires no open THOR orders. Found {len(opens)}")
    trader = get_trader(client)
    case = get_case(client)
    sm = security_map(sec)
    snap = PositionSnapshot(
        ts_ns=mono_ns(), tick=safe_int(case.get("tick")),
        m=pos[EXPECTED_MAIN], a=pos[EXPECTED_ALT],
        realized_m=realized_from_security(sm[EXPECTED_MAIN]),
        realized_a=realized_from_security(sm[EXPECTED_ALT]),
        unrealized_m=unrealized_from_security(sm[EXPECTED_MAIN]),
        unrealized_a=unrealized_from_security(sm[EXPECTED_ALT]),
        nlv=trader_nlv(trader), fines=trader_fines(trader),
        limits=get_limits(client), securities=sec,
    )
    return snap, opens


# =============================================================================
# TENDER TRIGGER / BOOKING CALIBRATION
# =============================================================================

def tender_expected_delta(tender: Mapping[str, Any]) -> int:
    # Current ALGO3 raw captions observed in the demo:
    # action BUY  => institution sells to us => we BUY tender => +inventory.
    # action SELL => institution buys from us => we SELL tender => -inventory.
    q = as_int(tender.get("quantity"))
    a = str(tender.get("action") or "").upper()
    if a == "BUY":
        return q
    if a == "SELL":
        return -q
    return 0


def expiry_seconds_remaining(tender: Mapping[str, Any], case: Mapping[str, Any]) -> Optional[float]:
    exp = safe_float(tender.get("expires"))
    tick = safe_float(case.get("tick"))
    if exp is None or tick is None:
        return None
    return exp - tick


def evaluate_tender(
    tender: Mapping[str, Any],
    books: Mapping[str, ParsedBook],
    fees: Mapping[str, float],
) -> Dict[str, Any]:
    tender_action = str(tender.get("action") or "").upper()
    if tender_action not in {"BUY", "SELL"}:
        return {"eligible": False, "reason": "unknown_action"}
    hedge_action = opposite(tender_action)
    qty = as_int(tender.get("quantity"))
    if qty <= 0:
        return {"eligible": False, "reason": "nonpositive_qty"}
    route = walk_route(books, qty, hedge_action, fees)
    econ = tender_economics(tender, route)
    return {
        "eligible": bool(route["full_coverage"]),
        "reason": "ok" if route["full_coverage"] else "insufficient_visible_coverage",
        "hedge_action_from_caption": hedge_action,
        "route": route,
        "economics": econ,
    }


def accept_tender_once(client: RITClient, tender: Mapping[str, Any]) -> WriteResult:
    tid = as_int(tender.get("tender_id"))
    price = as_float(tender.get("price"))
    return client.write_once("POST", f"/tenders/{tid}", {"price": price})


@dataclass
class BookingResult:
    success: bool
    reason: str
    first_change_ms: Optional[float]
    main_target_ms: Optional[float]
    alt_target_ms: Optional[float]
    both_target_ms: Optional[float]
    stable_ms: Optional[float]
    observed_delta_m: int
    observed_delta_a: int
    booked_delta: Optional[int]
    mirrored: Optional[bool]
    samples: List[PositionSnapshot]


def monitor_booking(
    client: RITClient,
    journal: Journal,
    before: PositionSnapshot,
    tender: Mapping[str, Any],
    accept_start_ns: int,
    timeout_s: float,
    poll_s: float,
) -> BookingResult:
    """Observe the actual tender-created inventory without assuming its sign.

    We know the tender quantity, but the point of this calibration is to establish the
    simulator's action semantics empirically. Authorization therefore requires BOTH
    THOR position fields to agree on a stable non-zero delta whose ABSOLUTE magnitude
    equals the tender quantity. The sign is learned from the observation.
    """
    expected = tender_expected_delta(tender)
    qty = abs(as_int(tender.get("quantity")))
    deadline = time.monotonic() + timeout_s
    first_change_ms = None
    main_target_ms = None
    alt_target_ms = None
    both_target_ms = None
    stable_ms = None
    last_pair: Optional[Tuple[int, int]] = None
    stable_count = 0
    samples: List[PositionSnapshot] = []

    while time.monotonic() < deadline and ((not stop_requested.is_set()) or execution_in_progress.is_set()):
        snap = sample_position_fast(client, journal, "booking")
        samples.append(snap)
        dm = snap.m - before.m
        da = snap.a - before.a
        elapsed_ms = (snap.ts_ns - accept_start_ns) / 1e6

        if first_change_ms is None and (dm != 0 or da != 0):
            first_change_ms = elapsed_ms
        if main_target_ms is None and abs(dm) == qty:
            main_target_ms = elapsed_ms
        if alt_target_ms is None and abs(da) == qty:
            alt_target_ms = elapsed_ms
        if both_target_ms is None and dm == da and abs(dm) == qty:
            both_target_ms = elapsed_ms

        pair = (dm, da)
        if pair == last_pair and pair != (0, 0):
            stable_count += 1
        else:
            stable_count = 1
            last_pair = pair

        if dm == da and abs(dm) == qty and stable_count >= 2:
            stable_ms = elapsed_ms
            return BookingResult(
                True, "both_positions_equal_exact_quantity_and_stable",
                first_change_ms, main_target_ms, alt_target_ms, both_target_ms, stable_ms,
                dm, da, dm, True, samples,
            )

        time.sleep(poll_s)

    last = samples[-1] if samples else before
    dm = last.m - before.m
    da = last.a - before.a
    mirrored = (dm == da and dm != 0) if (dm != 0 or da != 0) else None
    return BookingResult(
        False, "booking_not_stably_confirmed_before_timeout",
        first_change_ms, main_target_ms, alt_target_ms, both_target_ms, stable_ms,
        dm, da, None, mirrored, samples,
    )


# =============================================================================
# ORDER SUBMISSION / RESERVATION / RECONCILIATION
# =============================================================================

@dataclass
class SubmittedOrder:
    order_id: Optional[int]
    ticker: str
    action: str
    requested_qty: int
    submit_ns: int
    submit_latency_ms: Optional[float]
    response_body: Any
    ambiguous: bool
    error: Optional[str]
    terminal: bool = False
    filled_qty: int = 0
    status: str = ""
    vwap: Optional[float] = None


class ReservationLedger:
    def __init__(self, authorized_qty: int) -> None:
        self.authorized_qty = int(authorized_qty)
        self.submitted_qty = 0

    def can_submit(self, qty: int) -> bool:
        return qty > 0 and self.submitted_qty + int(qty) <= self.authorized_qty

    def reserve(self, qty: int) -> None:
        qty = int(qty)
        if not self.can_submit(qty):
            raise RuntimeError(
                f"Reservation would exceed authorized hedge: submitted={self.submitted_qty}, "
                f"new={qty}, authorized={self.authorized_qty}"
            )
        self.submitted_qty += qty


def submit_market_once(
    client: RITClient,
    journal: Journal,
    ticker: str,
    action: str,
    qty: int,
    tick: Optional[int],
    phase: str,
) -> SubmittedOrder:
    submit_ns = mono_ns()
    wr = client.write_once(
        "POST",
        "/orders",
        {"ticker": ticker, "type": "MARKET", "quantity": int(qty), "action": action},
    )
    body = wr.body if isinstance(wr.body, Mapping) else {}
    oid = safe_int(body.get("order_id")) if isinstance(body, Mapping) else None
    so = SubmittedOrder(
        order_id=oid,
        ticker=ticker,
        action=action,
        requested_qty=int(qty),
        submit_ns=submit_ns,
        submit_latency_ms=wr.latency_ms,
        response_body=wr.body,
        ambiguous=wr.ambiguous,
        error=wr.error,
        terminal=(order_is_terminal(body) if isinstance(body, Mapping) else False),
        filled_qty=(order_filled_qty(body) if isinstance(body, Mapping) else 0),
        status=(visible_order_status(body) if isinstance(body, Mapping) else ""),
        vwap=(order_vwap(body) if isinstance(body, Mapping) else None),
    )
    journal.put(
        "order_events",
        {
            "run_id": journal.run_id, "ts_utc": utc_now(), "mono_ns": submit_ns,
            "tick": tick, "phase": phase, "order_id": oid, "ticker": ticker,
            "action": action, "requested_qty": int(qty), "filled_qty": 0,
            "status": "AMBIGUOUS" if wr.ambiguous else "SUBMITTED",
            "vwap": None, "submit_latency_ms": wr.latency_ms,
            "raw_json": canonical_json(wr.body),
        },
        jsonl=True,
    )
    return so


def refresh_order_state(client: RITClient, so: SubmittedOrder) -> Optional[Dict[str, Any]]:
    if so.order_id is None:
        return None
    detail = get_order_detail(client, so.order_id)
    if detail is None:
        # Fallback to /orders list if detail endpoint isn't available/visible yet.
        for row in get_orders(client):
            if safe_int(row.get("order_id")) == so.order_id:
                detail = row
                break
    if detail is None:
        return None
    so.status = visible_order_status(detail)
    so.filled_qty = order_filled_qty(detail)
    so.vwap = order_vwap(detail)
    so.terminal = order_is_terminal(detail)
    return detail


def wait_single_order_resolution(
    client: RITClient,
    journal: Journal,
    so: SubmittedOrder,
    baseline: PositionSnapshot,
    booked_delta: int,
    timeout_s: float,
    poll_s: float,
) -> Dict[str, Any]:
    """Resolve BOTH order state and the corresponding mirrored position update.

    A terminal order record alone is not enough to authorize the next burst. We wait
    until position reporting reflects the known fill, preserving the LT3 booking/fill
    synchronization lesson and preventing a stale-position oversubmission.
    """
    start = time.monotonic()
    first_detail_ms = None
    first_fill_ms = None
    first_position_ms = None
    last_detail = None
    pos_samples = 0
    position_confirmed = False
    expected_remaining = None

    while time.monotonic() - start < timeout_s and not stop_requested.is_set():
        if so.order_id is not None:
            detail = refresh_order_state(client, so)
            if detail is not None:
                last_detail = detail
                elapsed = (mono_ns() - so.submit_ns) / 1e6
                if first_detail_ms is None:
                    first_detail_ms = elapsed
                if so.filled_qty > 0 and first_fill_ms is None:
                    first_fill_ms = elapsed
                journal.put(
                    "order_events",
                    {
                        "run_id": journal.run_id, "ts_utc": utc_now(), "mono_ns": mono_ns(),
                        "tick": None, "phase": "first_child_poll", "order_id": so.order_id,
                        "ticker": so.ticker, "action": so.action,
                        "requested_qty": so.requested_qty, "filled_qty": so.filled_qty,
                        "status": so.status, "vwap": so.vwap,
                        "submit_latency_ms": so.submit_latency_ms,
                        "raw_json": canonical_json(detail),
                    }, jsonl=False,
                )

        snap = sample_position_fast(client, journal, "first_child_fill")
        pos_samples += 1
        dm = snap.m - baseline.m
        da = snap.a - baseline.a

        known_fill = min(so.requested_qty, max(0, so.filled_qty))
        if known_fill > 0:
            sign = 1 if booked_delta > 0 else -1
            expected_remaining = booked_delta - sign * known_fill
            if dm == da == expected_remaining:
                position_confirmed = True
                if first_position_ms is None:
                    first_position_ms = (snap.ts_ns - so.submit_ns) / 1e6

        # If RIT says a market order is fully terminal and the position delta reflects
        # exactly the known fill, the single-child lifecycle is conclusively resolved.
        if so.terminal and known_fill >= so.requested_qty and position_confirmed:
            break

        # Ambiguous POSTs never authorize another write. We still observe in case an
        # order record and matching position transition eventually resolve it.
        time.sleep(poll_s)

    return {
        "first_order_detail_ms": first_detail_ms,
        "first_fill_visible_ms": first_fill_ms,
        "first_position_update_ms": first_position_ms,
        "terminal": so.terminal,
        "filled_qty": so.filled_qty,
        "status": so.status,
        "vwap": so.vwap,
        "position_confirmed": position_confirmed,
        "expected_remaining_delta": expected_remaining,
        "last_detail": last_detail,
        "position_samples": pos_samples,
    }


def cancel_order_once(client: RITClient, journal: Journal, order_id: int, reason: str) -> WriteResult:
    wr = client.write_once("DELETE", f"/orders/{int(order_id)}")
    journal.event("cancel_attempt", {"reason": reason, "result": wr.body, "ambiguous": wr.ambiguous}, order_id=order_id)
    return wr


def unresolved_orders(orders: Sequence[SubmittedOrder]) -> List[SubmittedOrder]:
    return [o for o in orders if not o.terminal and (o.order_id is None or not o.terminal)]


def update_all_order_states(client: RITClient, journal: Journal, orders: Sequence[SubmittedOrder], phase: str) -> None:
    all_rows = get_orders(client)
    by_id = {
        safe_int(r.get("order_id")): r
        for r in all_rows if isinstance(r, Mapping) and safe_int(r.get("order_id")) is not None
    }
    for so in orders:
        if so.order_id is None:
            continue
        row = by_id.get(so.order_id)
        if row is None:
            row = get_order_detail(client, so.order_id)
        if row is None:
            continue
        so.status = visible_order_status(row)
        so.filled_qty = order_filled_qty(row)
        so.vwap = order_vwap(row)
        so.terminal = order_is_terminal(row)
        journal.put(
            "order_events",
            {
                "run_id": journal.run_id, "ts_utc": utc_now(), "mono_ns": mono_ns(),
                "tick": None, "phase": phase, "order_id": so.order_id,
                "ticker": so.ticker, "action": so.action,
                "requested_qty": so.requested_qty, "filled_qty": so.filled_qty,
                "status": so.status, "vwap": so.vwap,
                "submit_latency_ms": so.submit_latency_ms,
                "raw_json": canonical_json(row),
            }, jsonl=False,
        )


# =============================================================================
# COMPETITION MARKET-DATA PLANE / PARTICIPANT TELEMETRY
# =============================================================================

@dataclass
class SideParticipantMetrics:
    side: str
    best_price: Optional[float]
    total_qty: int
    participant_qty: int
    anon_qty: int
    unknown_qty: int
    participant_share: Optional[float]
    participant_orders: int
    anon_orders: int
    median_participant_age_ms: Optional[float]
    median_anon_age_ms: Optional[float]


class OrderAgeTracker:
    """Tracks current visible L2 order age by order_id.

    This is descriptive telemetry only. We intentionally do not hard-code individual
    trader IDs or turn these ages into an acceptance veto in COMP-1.0.
    """
    def __init__(self) -> None:
        self._first_seen: Dict[Tuple[str, str, int], int] = {}
        self._lock = threading.Lock()

    def reset(self) -> None:
        with self._lock:
            self._first_seen.clear()

    @staticmethod
    def _row_order_id(row: Mapping[str, Any]) -> Optional[int]:
        for k in ("order_id", "id", "orderId"):
            v = safe_int(row.get(k))
            if v is not None:
                return v
        return None

    def update_and_measure(self, ticker: str, raw: Mapping[str, Any], now_ns: int) -> Dict[str, SideParticipantMetrics]:
        out: Dict[str, SideParticipantMetrics] = {}
        with self._lock:
            live_keys: set[Tuple[str, str, int]] = set()
            for side_name, raw_key, want_max in (("BID", "bids", True), ("ASK", "asks", False)):
                rows = raw.get(raw_key) or []
                participant_qty = anon_qty = unknown_qty = 0
                participant_orders = anon_orders = 0
                participant_ages: List[float] = []
                anon_ages: List[float] = []
                best_price: Optional[float] = None
                total_qty = 0

                for row in rows:
                    if not isinstance(row, Mapping):
                        continue
                    q = available_qty(row)
                    p = safe_float(row.get("price"))
                    if q <= 0 or p is None:
                        continue
                    total_qty += q
                    best_price = p if best_price is None else (max(best_price, p) if want_max else min(best_price, p))
                    trader = str(row.get("trader_id") or "").strip()
                    oid = self._row_order_id(row)
                    age_ms = None
                    if oid is not None:
                        key = (ticker, side_name, oid)
                        live_keys.add(key)
                        first = self._first_seen.setdefault(key, now_ns)
                        age_ms = (now_ns - first) / 1e6

                    if trader.upper() == "ANON":
                        anon_qty += q
                        anon_orders += 1
                        if age_ms is not None:
                            anon_ages.append(age_ms)
                    elif trader:
                        participant_qty += q
                        participant_orders += 1
                        if age_ms is not None:
                            participant_ages.append(age_ms)
                    else:
                        unknown_qty += q

                share = safe_div(participant_qty, total_qty)
                out[side_name] = SideParticipantMetrics(
                    side=side_name,
                    best_price=best_price,
                    total_qty=total_qty,
                    participant_qty=participant_qty,
                    anon_qty=anon_qty,
                    unknown_qty=unknown_qty,
                    participant_share=share,
                    participant_orders=participant_orders,
                    anon_orders=anon_orders,
                    median_participant_age_ms=(statistics.median(participant_ages) if participant_ages else None),
                    median_anon_age_ms=(statistics.median(anon_ages) if anon_ages else None),
                )

            # Drop vanished orders so IDs reused in later heats do not inherit old ages.
            for key in list(self._first_seen):
                if key[0] == ticker and key not in live_keys:
                    del self._first_seen[key]
        return out


class MarketDataCache:
    def __init__(
        self,
        client: RITClient,
        journal: Journal,
        base_interval_s: float,
        execution_evt: threading.Event,
    ) -> None:
        self.client = client
        self.journal = journal
        self.base_interval_s = max(0.02, float(base_interval_s))
        self.execution_evt = execution_evt
        self.stop_evt = threading.Event()
        self.lock = threading.RLock()
        self.books: Dict[str, ParsedBook] = {}
        self.metrics: Dict[str, Dict[str, SideParticipantMetrics]] = {}
        self.round_index = 0
        self.tick_hint: Optional[int] = None
        self.age_tracker = OrderAgeTracker()
        self.threads: List[threading.Thread] = []

    def set_round(self, round_index: int, tick: Optional[int]) -> None:
        with self.lock:
            self.round_index = int(round_index)
            self.tick_hint = tick
            self.books.clear()
            self.metrics.clear()
            self.age_tracker.reset()

    def set_tick_hint(self, tick: Optional[int]) -> None:
        with self.lock:
            self.tick_hint = tick

    def start(self) -> None:
        if self.threads:
            return
        for ticker in (EXPECTED_MAIN, EXPECTED_ALT):
            th = threading.Thread(target=self._loop, args=(ticker,), daemon=True, name=f"book-{ticker}")
            self.threads.append(th)
            th.start()

    def stop(self) -> None:
        self.stop_evt.set()
        for th in self.threads:
            th.join(timeout=3.0)

    def _loop(self, ticker: str) -> None:
        while not self.stop_evt.is_set():
            started = time.monotonic()
            try:
                book = fetch_book(self.client, ticker)
                with self.lock:
                    tick = self.tick_hint
                    round_index = self.round_index
                metrics = self.age_tracker.update_and_measure(ticker, book.raw, book.observed_ns)
                with self.lock:
                    self.books[ticker] = book
                    self.metrics[ticker] = metrics
                record_book(self.journal, book, tick, "cache")
                for side, m in metrics.items():
                    self.journal.put(
                        "market_features",
                        {
                            "run_id": self.journal.run_id,
                            "ts_utc": utc_now(),
                            "mono_ns": book.observed_ns,
                            "round_index": round_index,
                            "tick": tick,
                            "ticker": ticker,
                            "side": side,
                            "best_price": m.best_price,
                            "total_qty": m.total_qty,
                            "participant_qty": m.participant_qty,
                            "anon_qty": m.anon_qty,
                            "unknown_qty": m.unknown_qty,
                            "participant_share": m.participant_share,
                            "participant_orders": m.participant_orders,
                            "anon_orders": m.anon_orders,
                            "median_participant_age_ms": m.median_participant_age_ms,
                            "median_anon_age_ms": m.median_anon_age_ms,
                            "raw_json": canonical_json({
                                "participant_share": m.participant_share,
                                "participant_qty": m.participant_qty,
                                "anon_qty": m.anon_qty,
                            }),
                        },
                        jsonl=False,
                    )
            except Exception as exc:
                self.journal.event("book_cache_error", {"ticker": ticker, "error": f"{type(exc).__name__}: {exc}"})
            # During execution, slow background reads because booking/reconciliation
            # already consume API capacity and a fresh pair is fetched on demand.
            interval = max(self.base_interval_s, 0.10) if self.execution_evt.is_set() else self.base_interval_s
            elapsed = time.monotonic() - started
            self.stop_evt.wait(max(0.0, interval - elapsed))

    def latest_pair(self, max_age_s: float) -> Tuple[Optional[Dict[str, ParsedBook]], Dict[str, float]]:
        now = mono_ns()
        with self.lock:
            if EXPECTED_MAIN not in self.books or EXPECTED_ALT not in self.books:
                return None, {}
            pair = {EXPECTED_MAIN: self.books[EXPECTED_MAIN], EXPECTED_ALT: self.books[EXPECTED_ALT]}
        ages = {k: (now - b.observed_ns) / 1e9 for k, b in pair.items()}
        if any(age > max_age_s for age in ages.values()):
            return None, ages
        return pair, ages

    def inject_fresh_pair(self, pair: Mapping[str, ParsedBook], tick: Optional[int], phase: str) -> None:
        for ticker, book in pair.items():
            metrics = self.age_tracker.update_and_measure(ticker, book.raw, book.observed_ns)
            with self.lock:
                self.books[ticker] = book
                self.metrics[ticker] = metrics
            record_book(self.journal, book, tick, phase)

    def route_participant_context(self, route: Mapping[str, Any], books: Mapping[str, ParsedBook]) -> Dict[str, Any]:
        """Descriptive proxy: participant share among displayed quantities at levels used by the route."""
        participant = anon = unknown = level_total = 0.0
        per_venue: Dict[str, Dict[str, float]] = defaultdict(lambda: {"participant": 0.0, "anon": 0.0, "unknown": 0.0, "level_total": 0.0})
        for leg in route.get("plan") or []:
            ticker = str(leg.get("ticker"))
            price = safe_float(leg.get("price"))
            take = as_int(leg.get("take"))
            if ticker not in books or price is None or take <= 0:
                continue
            side_levels = books[ticker].asks if str(route.get("action")).upper() == "BUY" else books[ticker].bids
            lv = next((x for x in side_levels if abs(x.price - price) < 1e-9), None)
            if lv is None or lv.quantity <= 0:
                continue
            pq = aq = uq = 0
            for row in lv.raw_rows:
                q = available_qty(row)
                tr = str(row.get("trader_id") or "").strip()
                if tr.upper() == "ANON":
                    aq += q
                elif tr:
                    pq += q
                else:
                    uq += q
            # We do not claim queue ordering; scale the displayed composition to the
            # quantity this route intends to consume at the level.
            scale = min(1.0, take / max(1, lv.quantity))
            pp = pq * scale; aa = aq * scale; uu = uq * scale; tt = lv.quantity * scale
            participant += pp; anon += aa; unknown += uu; level_total += tt
            pv = per_venue[ticker]
            pv["participant"] += pp; pv["anon"] += aa; pv["unknown"] += uu; pv["level_total"] += tt
        return {
            "participant_qty_proxy": participant,
            "anon_qty_proxy": anon,
            "unknown_qty_proxy": unknown,
            "level_qty_proxy": level_total,
            "participant_share_proxy": safe_div(participant, level_total),
            "per_venue": dict(per_venue),
        }


class TASPoller:
    def __init__(self, client: RITClient, journal: Journal, interval_s: float, execution_evt: threading.Event) -> None:
        self.client = client
        self.journal = journal
        self.interval_s = max(0.05, float(interval_s))
        self.execution_evt = execution_evt
        self.stop_evt = threading.Event()
        self.lock = threading.Lock()
        self.round_index = 0
        self.seen: set[Tuple[int, str, str]] = set()
        self.thread: Optional[threading.Thread] = None

    def set_round(self, round_index: int) -> None:
        with self.lock:
            self.round_index = int(round_index)
            self.seen.clear()  # Important: RIT trade IDs reset across heats.

    def start(self) -> None:
        if self.thread is None:
            self.thread = threading.Thread(target=self._loop, daemon=True, name="tas-poller")
            self.thread.start()

    def stop(self) -> None:
        self.stop_evt.set()
        if self.thread:
            self.thread.join(timeout=3.0)

    @staticmethod
    def _trade_key(row: Mapping[str, Any], idx: int) -> str:
        for k in ("id", "trade_id", "tradeId"):
            if row.get(k) is not None:
                return f"id:{row.get(k)}"
        return f"fallback:{row.get('tick')}:{row.get('price')}:{row.get('quantity')}:{row.get('action')}:{idx}"

    def _loop(self) -> None:
        while not self.stop_evt.is_set():
            if self.execution_evt.is_set():
                self.stop_evt.wait(self.interval_s)
                continue
            started = time.monotonic()
            for ticker in (EXPECTED_MAIN, EXPECTED_ALT):
                try:
                    raw, _, _ = self.client.get("/securities/tas", {"ticker": ticker})
                    rows = raw if isinstance(raw, Sequence) and not isinstance(raw, (str, bytes)) else []
                    with self.lock:
                        ri = self.round_index
                    for idx, row in enumerate(rows):
                        if not isinstance(row, Mapping):
                            continue
                        key = self._trade_key(row, idx)
                        skey = (ri, ticker, key)
                        with self.lock:
                            if skey in self.seen:
                                continue
                            self.seen.add(skey)
                        self.journal.put(
                            "tas_trades",
                            {
                                "run_id": self.journal.run_id,
                                "ts_utc": utc_now(),
                                "mono_ns": mono_ns(),
                                "round_index": ri,
                                "ticker": ticker,
                                "trade_key": key,
                                "price": safe_float(row.get("price")),
                                "quantity": safe_float(row.get("quantity") or row.get("volume")),
                                "action": str(row.get("action") or row.get("side") or ""),
                                "raw_json": canonical_json(row),
                            },
                            jsonl=False,
                        )
                except Exception as exc:
                    self.journal.event("tas_error", {"ticker": ticker, "error": f"{type(exc).__name__}: {exc}"})
            elapsed = time.monotonic() - started
            self.stop_evt.wait(max(0.0, self.interval_s - elapsed))


# =============================================================================
# COMPETITION POLICY / STATE
# =============================================================================

def tender_id(t: Mapping[str, Any]) -> int:
    return as_int(t.get("tender_id"), -1)


def active_tender_by_id(client: RITClient, tid: int) -> Optional[Dict[str, Any]]:
    for t in get_tenders(client):
        if tender_id(t) == tid:
            return dict(t)
    return None


@dataclass
class TenderTrack:
    round_index: int
    tender_id: int
    raw: Dict[str, Any]
    first_seen_ns: int
    max_edge: Optional[float] = None
    max_profit: Optional[float] = None
    first_threshold_ns: Optional[int] = None
    accepted: bool = False
    shadow_triggered: bool = False
    last_edge: Optional[float] = None
    first_edge: Optional[float] = None
    min_edge: Optional[float] = None
    trigger_edge: Optional[float] = None
    trigger_profit: Optional[float] = None
    trigger_ns: Optional[int] = None
    last_revalidate_ns: int = 0
    shadow_horizons_done: set[float] = field(default_factory=set)
    edge_crossings_ns: Dict[float, int] = field(default_factory=dict)
    eval_count: int = 0
    last_eval_log_ns: int = 0


@dataclass
class TradeRecord:
    round_index: int
    tender: Dict[str, Any]
    baseline: PositionSnapshot
    trigger_eval: Dict[str, Any]
    trigger_context: Dict[str, Any]
    accept_latency_ms: Optional[float] = None
    booking: Optional[BookingResult] = None
    prehedge_eval: Optional[Dict[str, Any]] = None
    prehedge_context: Dict[str, Any] = field(default_factory=dict)
    orders: List[SubmittedOrder] = field(default_factory=list)
    repairs: int = 0
    burst_submit_span_ms: Optional[float] = None
    success: bool = False
    reason: str = ""
    final: Optional[PositionSnapshot] = None
    realized_delta: Optional[float] = None
    nlv_delta: Optional[float] = None
    fines_delta: Optional[float] = None
    started_ns: int = field(default_factory=mono_ns)
    finished_ns: Optional[int] = None


@dataclass
class EngineState:
    tenders: Dict[Tuple[int, int], TenderTrack] = field(default_factory=dict)
    trades: List[TradeRecord] = field(default_factory=list)
    halt_new_tenders: bool = False
    halt_reason: Optional[str] = None
    baseline_fines: Optional[float] = None
    account_start: Optional[PositionSnapshot] = None
    account_end: Optional[PositionSnapshot] = None
    round_index: int = 0
    rounds_completed: int = 0
    config_changes: int = 0
    http_429_seen: int = 0


def risk_admissible(tender: Mapping[str, Any], cfg: RuntimeConfig, baseline_position: int = 0) -> Tuple[bool, str]:
    qty = as_int(tender.get("quantity"))
    if qty <= 0:
        return False, "invalid_qty"
    delta = tender_expected_delta(tender)
    projected = baseline_position + delta
    if cfg.net_limit is not None and abs(projected) > cfg.net_limit:
        return False, f"net_limit:{abs(projected)}>{cfg.net_limit}"
    # Calibration proved THOR_M/A are mirror fields and /limits gross counts the
    # underlying exposure ONCE. Do not double mirrored positions here.
    if cfg.gross_limit is not None and abs(projected) > cfg.gross_limit:
        return False, f"gross_limit:{abs(projected)}>{cfg.gross_limit}"
    return True, "ok"


def round_seconds_remaining(case: Mapping[str, Any]) -> Optional[float]:
    tick = safe_float(case.get("tick"))
    total = safe_float(case.get("ticks_per_period"))
    if tick is None or total is None:
        return None
    return max(0.0, total - tick)


def runtime_config_dict(cfg: RuntimeConfig) -> Dict[str, Any]:
    return {
        "fees": dict(cfg.fees), "rebates": dict(cfg.rebates), "max_order": cfg.max_order,
        "api_rate": cfg.api_rate, "exec_delay_ms": cfg.exec_delay_ms,
        "gross_limit": cfg.gross_limit, "net_limit": cfg.net_limit,
    }


def config_materially_changed(a: RuntimeConfig, b: RuntimeConfig) -> bool:
    return runtime_config_dict(a) != runtime_config_dict(b)


def resolve_threshold(args: argparse.Namespace) -> float:
    if args.min_edge is not None:
        return float(args.min_edge)
    return MODE_EDGES[args.mode]


def global_best_prices(books: Mapping[str, ParsedBook]) -> Tuple[Optional[float], Optional[float]]:
    bids = [b.bids[0].price for b in books.values() if b.bids]
    asks = [b.asks[0].price for b in books.values() if b.asks]
    return (max(bids) if bids else None, min(asks) if asks else None)


def record_shadow_path(
    journal: Journal,
    round_index: int,
    tick: Optional[int],
    tender: Mapping[str, Any],
    horizon_s: float,
    elapsed_s: float,
    ev: Mapping[str, Any],
    pc: Mapping[str, Any],
    books: Mapping[str, ParsedBook],
) -> None:
    econ = ev.get("economics") or {}
    route = ev.get("route") or {}
    bid, ask = global_best_prices(books)
    journal.put(
        "shadow_paths",
        {
            "run_id": journal.run_id,
            "ts_utc": utc_now(),
            "mono_ns": mono_ns(),
            "round_index": round_index,
            "tick": tick,
            "tender_id": as_int(tender.get("tender_id")),
            "horizon_s": float(horizon_s),
            "elapsed_s": float(elapsed_s),
            "edge_per_share": safe_float(econ.get("edge_per_share")),
            "modeled_profit": safe_float(econ.get("modeled_profit")),
            "full_coverage": int(bool(route.get("full_coverage"))),
            "route_participant_share": safe_float(pc.get("participant_share_proxy")),
            "best_global_bid": bid,
            "best_global_ask": ask,
            "raw_json": canonical_json({"evaluation": ev, "participant_context": pc}),
        },
        jsonl=False,
    )


def record_tender_eval(
    journal: Journal,
    round_index: int,
    tender: Mapping[str, Any],
    ev: Mapping[str, Any],
    source: str,
    seconds_to_expiry: Optional[float],
    participant_context: Optional[Mapping[str, Any]] = None,
    tick: Optional[int] = None,
) -> None:
    econ = ev.get("economics") or {}
    route = ev.get("route") or {}
    journal.put(
        "tender_evaluations",
        {
            "run_id": journal.run_id, "ts_utc": utc_now(), "mono_ns": mono_ns(),
            "round_index": round_index, "tick": tick,
            "tender_id": as_int(tender.get("tender_id")),
            "tender_action": str(tender.get("action") or "").upper(),
            "hedge_action": str(ev.get("hedge_action_from_caption") or ""),
            "quantity": as_int(tender.get("quantity")),
            "tender_price": safe_float(tender.get("price")),
            "seconds_to_expiry": seconds_to_expiry,
            "source": source,
            "full_coverage": int(bool(route.get("full_coverage"))),
            "filled_qty": as_int(route.get("filled_qty")),
            "edge_per_share": safe_float(econ.get("edge_per_share")),
            "modeled_profit": safe_float(econ.get("modeled_profit")),
            "route_participant_share": safe_float((participant_context or {}).get("participant_share_proxy")),
            "raw_json": canonical_json({"evaluation": ev, "participant_context": participant_context or {}}),
        },
        jsonl=False,
    )


def submit_market_checked(
    client: RITClient,
    journal: Journal,
    ticker: str,
    action: str,
    qty: int,
    tick: Optional[int],
    phase: str,
) -> SubmittedOrder:
    so = submit_market_once(client, journal, ticker, action, qty, tick, phase)
    response = so.response_body
    # A transport response without order_id is a conclusive rejection if HTTP was
    # non-success. submit_market_once logs raw response; here we normalize the state.
    if not so.ambiguous and so.order_id is None:
        so.status = "REJECTED_OR_NO_ID"
        so.terminal = True
        so.error = so.error or f"no_order_id_response:{response!r}"
    return so


def preaccept_revalidate_competition(
    client: RITClient,
    journal: Journal,
    market: MarketDataCache,
    tender: Mapping[str, Any],
    cfg: RuntimeConfig,
    threshold: float,
    args: argparse.Namespace,
    round_index: int,
) -> Tuple[bool, str, Optional[Dict[str, ParsedBook]], Optional[Dict[str, Any]], Dict[str, Any], Dict[str, Any]]:
    case = get_case(client)
    if str(case.get("status") or "").upper() != "ACTIVE":
        return False, "case_not_active", None, None, case, {}
    current = active_tender_by_id(client, as_int(tender.get("tender_id")))
    if current is None:
        return False, "tender_no_longer_active", None, None, case, {}
    if not bool(current.get("is_fixed_bid", True)):
        return False, "non_fixed_tender", None, None, case, {}
    if (as_int(current.get("quantity")) != as_int(tender.get("quantity")) or
        abs(as_float(current.get("price")) - as_float(tender.get("price"))) > 1e-9 or
        str(current.get("action") or "").upper() != str(tender.get("action") or "").upper()):
        return False, "tender_changed", None, None, case, {}

    to_exp = expiry_seconds_remaining(current, case)
    if to_exp is not None and to_exp < args.min_seconds_to_expiry:
        return False, f"insufficient_tender_time:{to_exp:.3f}s", None, None, case, {}
    to_end = round_seconds_remaining(case)
    if to_end is not None and to_end < args.min_seconds_to_round_end:
        return False, f"insufficient_round_time:{to_end:.3f}s", None, None, case, {}

    sec = get_securities(client)
    pos = positions_from_securities(sec)
    if pos[EXPECTED_MAIN] != pos[EXPECTED_ALT]:
        return False, f"mirror_disagreement_before_accept:{pos}", None, None, case, {}
    if pos[EXPECTED_MAIN] != 0:
        return False, f"nonflat_before_accept:{pos}", None, None, case, {}
    opens = open_thor_orders(get_orders(client))
    if opens:
        return False, f"open_orders_before_accept:{len(opens)}", None, None, case, {}
    ok_risk, why = risk_admissible(current, cfg, baseline_position=0)
    if not ok_risk:
        return False, why, None, None, case, {}

    books = fetch_book_pair(client)
    market.inject_fresh_pair(books, safe_int(case.get("tick")), "preaccept_refresh")
    ev = evaluate_tender(current, books, cfg.fees)
    pc = market.route_participant_context(ev.get("route") or {}, books)
    record_tender_eval(journal, round_index, current, ev, "preaccept", to_exp, pc, safe_int(case.get("tick")))
    if not ev.get("eligible"):
        return False, str(ev.get("reason")), books, ev, case, pc
    edge = safe_float((ev.get("economics") or {}).get("edge_per_share"))
    if edge is None or edge < threshold:
        return False, f"edge_revalidation_failed:{edge}", books, ev, case, pc
    return True, "ok", books, ev, case, pc


# =============================================================================
# BURST EXECUTION / RECONCILIATION
# =============================================================================

def burst_submit_route(
    client: RITClient,
    journal: Journal,
    children: Sequence[Mapping[str, Any]],
    hedge_action: str,
    authorized_qty: int,
    tick: Optional[int],
    phase: str,
    api_order_rate: Optional[float] = None,
) -> Tuple[List[SubmittedOrder], Optional[float], bool, str]:
    ledger = ReservationLedger(authorized_qty)
    orders: List[SubmittedOrder] = []
    first_ns: Optional[int] = None
    last_done_ns: Optional[int] = None
    last_submit_start_ns: Optional[int] = None
    # Stay just inside the advertised order-rate ceiling. In the calibrated
    # environment HTTP latency itself was ~12 ms/order, so this usually adds no
    # delay, but it prevents a faster localhost response from causing 429s.
    min_gap_s = 0.0
    if api_order_rate is not None and api_order_rate > 0:
        min_gap_s = 1.0 / max(1.0, api_order_rate * 0.95)
    for ch in children:
        q = int(ch.get("quantity") or 0)
        if q <= 0:
            continue
        if not ledger.can_submit(q):
            return orders, None, False, "reservation_guard_blocked"
        ledger.reserve(q)  # reserve BEFORE the write; lost responses remain spoken for.
        if last_submit_start_ns is not None and min_gap_s > 0:
            target_ns = last_submit_start_ns + int(min_gap_s * 1e9)
            wait_ns = target_ns - mono_ns()
            if wait_ns > 0:
                time.sleep(wait_ns / 1e9)
        if first_ns is None:
            first_ns = mono_ns()
        so = submit_market_checked(client, journal, str(ch["ticker"]), hedge_action, q, tick, phase)
        last_submit_start_ns = so.submit_ns
        last_done_ns = mono_ns()
        orders.append(so)
        print(
            f"[{phase.upper()}] {hedge_action} {q:,} {ch['ticker']} MARKET "
            f"id={so.order_id} latency={so.submit_latency_ms:.3f}ms "
            f"ambiguous={so.ambiguous} status={so.status or 'SUBMITTED'}"
        )
        if so.ambiguous:
            return orders, ((last_done_ns-first_ns)/1e6 if first_ns else None), False, "ambiguous_write"
        if so.order_id is None:
            return orders, ((last_done_ns-first_ns)/1e6 if first_ns else None), False, "order_rejected_or_no_id"
    span = (last_done_ns - first_ns) / 1e6 if first_ns is not None and last_done_ns is not None else None
    if ledger.submitted_qty != sum(int(ch.get("quantity") or 0) for ch in children):
        return orders, span, False, "ledger_quantity_mismatch"
    return orders, span, True, "ok"


def known_filled_qty(orders: Sequence[SubmittedOrder]) -> int:
    return sum(min(o.requested_qty, max(0, o.filled_qty)) for o in orders)


def has_ambiguous_order(orders: Sequence[SubmittedOrder]) -> bool:
    return any(o.ambiguous for o in orders)


def reconcile_to_baseline(
    client: RITClient,
    journal: Journal,
    cfg: RuntimeConfig,
    baseline: PositionSnapshot,
    hedge_qty: int,
    orders: List[SubmittedOrder],
    args: argparse.Namespace,
    round_index: int,
) -> Tuple[bool, str, int, PositionSnapshot]:
    """Reconcile without ever replaying an unknown write or crossing through flat."""
    repair_rounds = 0
    deadline = time.monotonic() + args.reconcile_timeout
    stable_pair: Optional[Tuple[int, int]] = None
    stable_count = 0
    last_snap = sample_position_fast(client, journal, "reconcile_start")

    while time.monotonic() < deadline:
        update_all_order_states(client, journal, orders, "reconcile")
        snap = sample_position_fast(client, journal, "reconcile")
        last_snap = snap
        dm = snap.m - baseline.m
        da = snap.a - baseline.a
        pair = (dm, da)
        if pair == stable_pair:
            stable_count += 1
        else:
            stable_pair = pair
            stable_count = 1

        try:
            opens = open_thor_orders(get_orders(client))
        except Exception:
            opens = []

        # Ambiguous write means transaction state is not provable. Do NOT repair.
        if has_ambiguous_order(orders):
            if dm == 0 and da == 0 and not opens and stable_count >= 3:
                return False, "flat_but_ambiguous_write_halt_round", repair_rounds, snap
            time.sleep(args.reconcile_poll)
            continue

        unresolved = [o for o in orders if not o.terminal]
        if dm == 0 and da == 0 and not opens and not unresolved:
            return True, "flat_all_orders_terminal", repair_rounds, snap

        if dm != da:
            time.sleep(args.reconcile_poll)
            continue
        if unresolved or opens:
            time.sleep(args.reconcile_poll)
            continue

        filled = known_filled_qty(orders)
        residual_by_fills = max(0, hedge_qty - filled)
        residual_by_position = abs(dm)
        if residual_by_fills == 0:
            # All authorized hedge shares are known filled; position is lagging.
            time.sleep(args.reconcile_poll)
            continue
        if stable_count < 2 or residual_by_position != residual_by_fills:
            time.sleep(args.reconcile_poll)
            continue
        if repair_rounds >= args.max_repair_rounds:
            return False, "repair_round_limit", repair_rounds, snap

        repair_action = "SELL" if dm > 0 else "BUY"
        books = fetch_book_pair(client)
        rr = walk_route(books, residual_by_position, repair_action, cfg.fees)
        visible = min(residual_by_position, as_int(rr.get("filled_qty")))
        if visible <= 0:
            time.sleep(args.reconcile_poll)
            continue
        children = compress_global_plan(rr.get("plan") or [], cfg.max_order)
        # Trim children exactly to currently visible authorized residual.
        trimmed: List[Dict[str, Any]] = []
        remain = visible
        for ch in children:
            if remain <= 0:
                break
            q = min(remain, int(ch.get("quantity") or 0))
            if q > 0:
                c = dict(ch); c["quantity"] = q; trimmed.append(c); remain -= q
        journal.event("repair_route", {"round_index": round_index, "route": rr, "children": trimmed})
        new_orders, _, ok, why = burst_submit_route(
            client, journal, trimmed, repair_action, visible, snap.tick, f"repair_{repair_rounds+1}",
            api_order_rate=cfg.api_rate,
        )
        orders.extend(new_orders)
        repair_rounds += 1
        stable_count = 0
        if not ok:
            if why == "ambiguous_write":
                # Continue observation only; no more writes will be authorized.
                continue
            return False, f"repair_submit_failed:{why}", repair_rounds, snap
        time.sleep(args.reconcile_poll)

    return False, "reconcile_timeout", repair_rounds, last_snap


def accounting_delta(before: PositionSnapshot, after: PositionSnapshot) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    # Mirrored realized values must not be doubled. Use Main if available, otherwise Alt.
    rb = before.realized_m if before.realized_m is not None else before.realized_a
    ra = after.realized_m if after.realized_m is not None else after.realized_a
    realized = (ra - rb) if (ra is not None and rb is not None) else None
    nlv = (after.nlv - before.nlv) if (after.nlv is not None and before.nlv is not None) else None
    fines = (after.fines - before.fines) if (after.fines is not None and before.fines is not None) else None
    return realized, nlv, fines


def execute_competition_tender(
    client: RITClient,
    journal: Journal,
    market: MarketDataCache,
    cfg: RuntimeConfig,
    tender: Mapping[str, Any],
    trigger_eval: Mapping[str, Any],
    trigger_context: Mapping[str, Any],
    args: argparse.Namespace,
    round_index: int,
) -> TradeRecord:
    execution_in_progress.set()
    baseline = sample_position(client, journal, "trade_baseline", include_limits=True)
    tr = TradeRecord(
        round_index=round_index,
        tender=dict(tender),
        baseline=baseline,
        trigger_eval=dict(trigger_eval),
        trigger_context=dict(trigger_context),
    )
    tid = as_int(tender.get("tender_id"))
    qty = as_int(tender.get("quantity"))
    accept_start_ns = mono_ns()
    try:
        print(
            f"\n[ACCEPT] tender={tid} {tender.get('action')} {qty:,} @ {as_float(tender.get('price')):.4f} "
            f"edge={as_float((trigger_eval.get('economics') or {}).get('edge_per_share')):+.4f}/sh "
            f"profit={pretty_money(safe_float((trigger_eval.get('economics') or {}).get('modeled_profit')))}"
        )
        wr = accept_tender_once(client, tender)
        tr.accept_latency_ms = wr.latency_ms
        journal.event(
            "tender_accept_result",
            {"body": wr.body, "ambiguous": wr.ambiguous, "error": wr.error, "latency_ms": wr.latency_ms},
            tender_id=tid,
        )
        if wr.response is not None and not wr.response.ok:
            tr.reason = f"accept_http_{wr.response.status_code}"
            return tr

        # Even a transport-ambiguous acceptance can be resolved by the actual booked
        # position. Never re-POST the tender.
        booking = monitor_booking(
            client, journal, baseline, tender, accept_start_ns,
            timeout_s=args.booking_timeout, poll_s=args.booking_poll,
        )
        tr.booking = booking
        if not booking.success or booking.booked_delta is None:
            tr.reason = f"booking_failed:{booking.reason}"
            return tr

        booked_delta = int(booking.booked_delta)
        inferred_hedge = "SELL" if booked_delta > 0 else "BUY"
        expected_hedge = opposite(str(tender.get("action") or "").upper())
        if inferred_hedge != expected_hedge:
            journal.event(
                "tender_semantic_anomaly",
                {"expected_hedge": expected_hedge, "inferred_hedge": inferred_hedge, "booked_delta": booked_delta},
                tender_id=tid,
            )
            print(f"[WARN] Tender semantics differ from calibration: expected {expected_hedge}, observed {inferred_hedge}")

        # Fresh books AFTER liability is truly booked. Calibration showed this is the
        # decisive point: do not insert an order-detail confirmation delay here.
        case_now = get_case(client)
        pre_books = fetch_book_pair(client)
        market.inject_fresh_pair(pre_books, safe_int(case_now.get("tick")), "prehedge_refresh")
        route = walk_route(pre_books, abs(booked_delta), inferred_hedge, cfg.fees)
        econ = tender_economics(tender, route)
        tr.prehedge_eval = {
            "eligible": bool(route.get("full_coverage")),
            "reason": "ok" if route.get("full_coverage") else "partial_visible_route",
            "hedge_action_from_caption": expected_hedge,
            "route": route,
            "economics": econ,
        }
        tr.prehedge_context = market.route_participant_context(route, pre_books)
        journal.event(
            "prehedge_route",
            {"evaluation": tr.prehedge_eval, "participant_context": tr.prehedge_context},
            tick=safe_int(case_now.get("tick")), tender_id=tid,
        )
        visible = min(abs(booked_delta), as_int(route.get("filled_qty")))
        if visible <= 0:
            tr.reason = "no_visible_hedge_liquidity_after_booking"
            return tr

        children = compress_global_plan(route.get("plan") or [], cfg.max_order)
        trimmed: List[Dict[str, Any]] = []
        remain = visible
        for ch in children:
            if remain <= 0:
                break
            q = min(remain, int(ch.get("quantity") or 0))
            if q > 0:
                c = dict(ch); c["quantity"] = q; trimmed.append(c); remain -= q
        print(
            f"[ROUTE] booked={abs(booked_delta):,} visible={visible:,} "
            f"children={len(trimmed)} participantShare≈{safe_float(tr.prehedge_context.get('participant_share_proxy'))}"
        )
        print(f"[ROUTE] {[(c['ticker'], c['quantity'], c['planned_best_price'], c['planned_worst_price']) for c in trimmed]}")

        new_orders, span_ms, ok, why = burst_submit_route(
            client, journal, trimmed, inferred_hedge, visible,
            safe_int(case_now.get("tick")), "burst_submit",
            api_order_rate=cfg.api_rate,
        )
        tr.orders.extend(new_orders)
        tr.burst_submit_span_ms = span_ms
        if not ok and why != "ambiguous_write":
            # A conclusive rejected child still allows careful reconciliation of what
            # did fill. Never submit an immediate replacement until states resolve.
            journal.event("burst_incomplete", {"reason": why}, tender_id=tid)

        rec_ok, rec_reason, repairs, final_snap = reconcile_to_baseline(
            client, journal, cfg, baseline, abs(booked_delta), tr.orders,
            args, round_index,
        )
        tr.repairs = repairs
        tr.final = final_snap
        tr.success = rec_ok
        tr.reason = rec_reason

        # Short accounting settle. Position/order state, not P&L display latency,
        # controls readiness for the next tender.
        if args.accounting_settle > 0:
            time.sleep(args.accounting_settle)
        try:
            final_accounting = sample_position(client, journal, "trade_final", include_limits=True)
            tr.final = final_accounting
        except Exception:
            pass
        if tr.final is not None:
            tr.realized_delta, tr.nlv_delta, tr.fines_delta = accounting_delta(baseline, tr.final)
        tr.finished_ns = mono_ns()
        return tr
    finally:
        execution_in_progress.clear()


# =============================================================================
# ROUND ENGINE
# =============================================================================

def refresh_config_if_due(
    client: RITClient,
    journal: Journal,
    cfg: RuntimeConfig,
    state: EngineState,
) -> RuntimeConfig:
    try:
        new_cfg = discover_runtime_config(client)
        if config_materially_changed(cfg, new_cfg):
            state.config_changes += 1
            journal.event("runtime_config_change", {"before": runtime_config_dict(cfg), "after": runtime_config_dict(new_cfg)})
            print(f"[CONFIG] runtime change: {runtime_config_dict(cfg)} -> {runtime_config_dict(new_cfg)}")
        return new_cfg
    except Exception as exc:
        journal.event("runtime_config_refresh_error", {"error": f"{type(exc).__name__}: {exc}"})
        return cfg


def current_fines(client: RITClient) -> Optional[float]:
    try:
        return trader_fines(get_trader(client))
    except Exception:
        return None


def clean_flat_state(client: RITClient) -> Tuple[bool, str, Optional[PositionSnapshot]]:
    try:
        sec = get_securities(client)
        pos = positions_from_securities(sec)
        if pos[EXPECTED_MAIN] != pos[EXPECTED_ALT]:
            return False, f"mirror_disagreement:{pos}", None
        if pos[EXPECTED_MAIN] != 0:
            return False, f"nonflat:{pos}", None
        opens = open_thor_orders(get_orders(client))
        if opens:
            return False, f"open_orders:{len(opens)}", None
        return True, "ok", None
    except Exception as exc:
        return False, f"state_check_error:{type(exc).__name__}:{exc}", None


def run_one_round(
    client: RITClient,
    journal: Journal,
    market: MarketDataCache,
    tas: TASPoller,
    cfg: RuntimeConfig,
    args: argparse.Namespace,
    state: EngineState,
) -> RuntimeConfig:
    threshold = resolve_threshold(args)
    saw_active = False
    last_config_refresh = 0.0
    last_trader_refresh = 0.0
    baseline_fines = current_fines(client)
    if state.baseline_fines is None:
        state.baseline_fines = baseline_fines

    # Wait for a fresh ACTIVE transition.
    print("[WAIT] Waiting for next ACTIVE ALGO3 heat...")
    while not stop_requested.is_set():
        case = get_case(client)
        status = str(case.get("status") or "").upper()
        if status == "ACTIVE":
            saw_active = True
            state.round_index += 1
            ri = state.round_index
            market.set_round(ri, safe_int(case.get("tick")))
            tas.set_round(ri)
            journal.event("round_start", {"round_index": ri, "case": case}, tick=safe_int(case.get("tick")))
            print(f"\n=== ROUND {ri} ACTIVE tick={case.get('tick')} threshold={threshold:.4f}/sh mode={args.mode.upper()} ===")
            break
        time.sleep(args.idle_poll)
    if not saw_active:
        return cfg

    ri = state.round_index
    shadow_triggered: set[int] = set()
    while not stop_requested.is_set():
        loop_start = time.monotonic()
        case = get_case(client)
        status = str(case.get("status") or "").upper()
        tick = safe_int(case.get("tick"))
        market.set_tick_hint(tick)
        if status != "ACTIVE":
            state.rounds_completed += 1
            journal.event("round_end", {"round_index": ri, "case": case}, tick=tick)
            print(f"=== ROUND {ri} ENDED tick={tick} ===")
            return cfg

        now = time.monotonic()
        if now - last_config_refresh >= args.config_refresh:
            cfg = refresh_config_if_due(client, journal, cfg, state)
            last_config_refresh = now
        if now - last_trader_refresh >= args.trader_refresh:
            f = current_fines(client)
            last_trader_refresh = now
            if f is not None and baseline_fines is not None and f > baseline_fines + 1e-9:
                state.halt_new_tenders = True
                state.halt_reason = f"fine_increase:{baseline_fines}->{f}"
                journal.event("fine_increase", {"before": baseline_fines, "after": f}, tick=tick)
                print(f"[HALT NEW TENDERS] fines increased {baseline_fines} -> {f}")

        try:
            tenders = get_tenders(client)
        except Exception as exc:
            journal.event("tender_poll_error", {"error": f"{type(exc).__name__}: {exc}"}, tick=tick)
            time.sleep(args.tender_poll)
            continue

        pair, ages = market.latest_pair(args.max_book_age)
        if pair is None and tenders:
            try:
                pair = fetch_book_pair(client)
                market.inject_fresh_pair(pair, tick, "cache_miss_refresh")
                ages = {k: 0.0 for k in pair}
            except Exception as exc:
                journal.event("book_pair_refresh_error", {"error": f"{type(exc).__name__}: {exc}"}, tick=tick)
                pair = None

        active_ids = set()
        for tender in tenders:
            if not isinstance(tender, Mapping):
                continue
            tid = as_int(tender.get("tender_id"), -1)
            if tid < 0:
                continue
            active_ids.add(tid)
            key = (ri, tid)
            if key not in state.tenders:
                state.tenders[key] = TenderTrack(ri, tid, dict(tender), mono_ns())
                journal.event("tender_new", dict(tender), tick=tick, tender_id=tid)
                print(
                    f"[TENDER] tick={tick} id={tid} {tender.get('action')} "
                    f"{as_int(tender.get('quantity')):,} @ {as_float(tender.get('price')):.4f} "
                    f"expires={tender.get('expires')}"
                )
            track = state.tenders[key]
            if track.accepted:
                continue
            if pair is None:
                continue

            ev = evaluate_tender(tender, pair, cfg.fees)
            pc = market.route_participant_context(ev.get("route") or {}, pair)
            edge = safe_float((ev.get("economics") or {}).get("edge_per_share"))
            profit = safe_float((ev.get("economics") or {}).get("modeled_profit"))
            to_exp = expiry_seconds_remaining(tender, case)
            track.eval_count += 1
            track.last_edge = edge
            if edge is not None:
                if track.first_edge is None:
                    track.first_edge = edge
                if track.min_edge is None or edge < track.min_edge:
                    track.min_edge = edge
                if track.max_edge is None or edge > track.max_edge:
                    track.max_edge = edge; track.max_profit = profit
            now_ns = mono_ns()

            # Record first causal crossings of economically interesting thresholds.
            if edge is not None:
                for lvl in SHADOW_EDGE_LEVELS:
                    if edge >= lvl and lvl not in track.edge_crossings_ns:
                        track.edge_crossings_ns[lvl] = now_ns
                        journal.event(
                            "edge_crossing",
                            {"level": lvl, "edge": edge, "profit": profit,
                             "elapsed_from_first_seen_s": (now_ns-track.first_seen_ns)/1e9},
                            tick=tick, tender_id=tid,
                        )

            # After a shadow trigger, explicitly snapshot the path at fixed horizons.
            # This makes tail-policy research trivial and does not affect live decisions.
            if (not args.live and track.trigger_ns is not None):
                elapsed_shadow = (now_ns - track.trigger_ns) / 1e9
                for horizon in SHADOW_HORIZONS_S:
                    if horizon not in track.shadow_horizons_done and elapsed_shadow >= horizon:
                        record_shadow_path(journal, ri, tick, tender, horizon, elapsed_shadow, ev, pc, pair)
                        track.shadow_horizons_done.add(horizon)
            if (now_ns - track.last_eval_log_ns >= 100_000_000 or
                (edge is not None and track.max_edge == edge)):
                record_tender_eval(journal, ri, tender, ev, "cache", to_exp, pc, tick)
                track.last_eval_log_ns = now_ns

            if state.halt_new_tenders:
                continue
            if not args.live and tid in shadow_triggered:
                # Continue cheap cached telemetry/max-edge tracking, but do not spend
                # extra fresh-book requests repeatedly after the first shadow trigger.
                continue
            ok_risk, risk_reason = risk_admissible(tender, cfg, 0)
            if not ok_risk:
                journal.event("tender_risk_reject", {"reason": risk_reason}, tick=tick, tender_id=tid)
                continue
            if not ev.get("eligible"):
                continue
            if edge is None or edge < threshold - args.pretrigger_margin:
                continue

            # Avoid hammering fresh-book revalidation when a tender oscillates just
            # below the trigger. Cached 50 ms telemetry continues uninterrupted.
            if track.last_revalidate_ns and (now_ns - track.last_revalidate_ns) / 1e9 < args.revalidate_cooldown:
                continue
            track.last_revalidate_ns = now_ns

            # Near/through threshold: perform fresh two-book revalidation. This is the
            # race boundary; the cached books are discovery, not authorization.
            ok, reason, fresh_books, fresh_ev, fresh_case, fresh_pc = preaccept_revalidate_competition(
                client, journal, market, tender, cfg, threshold, args, ri
            )
            if not ok:
                if args.verbose_revalidation:
                    print(f"[REVALIDATE] tender={tid} no: {reason}")
                continue
            fresh_edge = safe_float((fresh_ev.get("economics") or {}).get("edge_per_share"))
            if track.first_threshold_ns is None:
                track.first_threshold_ns = mono_ns()
            print(
                f"[TRIGGER] tick={safe_int(fresh_case.get('tick'))} tender={tid} "
                f"edge={fresh_edge:+.4f}/sh profit={pretty_money(safe_float((fresh_ev.get('economics') or {}).get('modeled_profit')))} "
                f"routeParticipant≈{safe_float(fresh_pc.get('participant_share_proxy'))}"
            )

            if not args.live:
                if tid not in shadow_triggered:
                    shadow_triggered.add(tid)
                    track.shadow_triggered = True
                    track.trigger_ns = mono_ns()
                    track.trigger_edge = fresh_edge
                    track.trigger_profit = safe_float((fresh_ev.get("economics") or {}).get("modeled_profit"))
                    journal.event("shadow_trigger", {"evaluation": fresh_ev, "participant_context": fresh_pc}, tick=tick, tender_id=tid)
                    if fresh_books is not None:
                        record_shadow_path(journal, ri, safe_int(fresh_case.get("tick")), tender, 0.0, 0.0,
                                           fresh_ev, fresh_pc, fresh_books)
                        track.shadow_horizons_done.add(0.0)
                continue

            clean, clean_reason, _ = clean_flat_state(client)
            if not clean:
                state.halt_new_tenders = True
                state.halt_reason = f"pretrade_clean_state_failed:{clean_reason}"
                print(f"[HALT NEW TENDERS] {state.halt_reason}")
                continue

            tr = execute_competition_tender(client, journal, market, cfg, tender, fresh_ev, fresh_pc, args, ri)
            state.trades.append(tr)
            track.accepted = True
            if tr.final is not None and tr.fines_delta is not None and tr.fines_delta > 0:
                state.halt_new_tenders = True
                state.halt_reason = f"trade_fine_delta:{tr.fines_delta}"
            if not tr.success:
                state.halt_new_tenders = True
                state.halt_reason = f"trade_failure:{tr.reason}"
                print(f"[HALT NEW TENDERS] {state.halt_reason}")
            else:
                print(
                    f"[TRADE COMPLETE] tender={tid} realized={pretty_money(tr.realized_delta)} "
                    f"NLVΔ={pretty_money(tr.nlv_delta)} orders={len(tr.orders)} repairs={tr.repairs}"
                )
            # Dynamic config may have changed during the transaction; refresh once flat.
            cfg = refresh_config_if_due(client, journal, cfg, state)
            if args.max_trades > 0 and len(state.trades) >= args.max_trades:
                state.halt_new_tenders = True
                journal.event("max_trades_reached", {"max_trades": args.max_trades}, tick=tick)
                print(f"[HALT NEW TENDERS] max_trades_reached:{args.max_trades}")

        elapsed = time.monotonic() - loop_start
        time.sleep(max(0.0, args.tender_poll - elapsed))

    return cfg


# =============================================================================
# OUTPUTS / SUMMARY
# =============================================================================

def trade_to_payload(tr: TradeRecord) -> Dict[str, Any]:
    trigger_econ = tr.trigger_eval.get("economics") or {}
    pre_econ = (tr.prehedge_eval or {}).get("economics") or {}
    final_pos = None
    if tr.final is not None:
        final_pos = tr.final.m - tr.baseline.m
    return {
        "round_index": tr.round_index,
        "tender_id": as_int(tr.tender.get("tender_id")),
        "tender_action": str(tr.tender.get("action") or "").upper(),
        "hedge_action": opposite(str(tr.tender.get("action") or "").upper()),
        "quantity": as_int(tr.tender.get("quantity")),
        "tender_price": safe_float(tr.tender.get("price")),
        "trigger_edge": safe_float(trigger_econ.get("edge_per_share")),
        "trigger_profit": safe_float(trigger_econ.get("modeled_profit")),
        "prehedge_edge": safe_float(pre_econ.get("edge_per_share")),
        "prehedge_profit": safe_float(pre_econ.get("modeled_profit")),
        "accept_latency_ms": tr.accept_latency_ms,
        "booking_ms": (tr.booking.stable_ms if tr.booking else None),
        "burst_orders": len([o for o in tr.orders if True]),
        "burst_submit_span_ms": tr.burst_submit_span_ms,
        "repairs": tr.repairs,
        "final_position": final_pos,
        "realized_delta": tr.realized_delta,
        "nlv_delta": tr.nlv_delta,
        "fines_delta": tr.fines_delta,
        "success": tr.success,
        "reason": tr.reason,
        "participant_share_trigger": safe_float(tr.trigger_context.get("participant_share_proxy")),
        "participant_share_prehedge": safe_float(tr.prehedge_context.get("participant_share_proxy")),
        "duration_ms": ((tr.finished_ns - tr.started_ns)/1e6 if tr.finished_ns is not None else None),
    }


def persist_trade_summary(journal: Journal, tr: TradeRecord) -> None:
    p = trade_to_payload(tr)
    journal.put(
        "trade_summaries",
        {
            "run_id": journal.run_id, "ts_utc": utc_now(),
            "round_index": p["round_index"], "tender_id": p["tender_id"],
            "tender_action": p["tender_action"], "hedge_action": p["hedge_action"],
            "quantity": p["quantity"], "tender_price": p["tender_price"],
            "trigger_edge": p["trigger_edge"], "trigger_profit": p["trigger_profit"],
            "prehedge_edge": p["prehedge_edge"], "prehedge_profit": p["prehedge_profit"],
            "accept_latency_ms": p["accept_latency_ms"], "booking_ms": p["booking_ms"],
            "burst_orders": p["burst_orders"], "burst_submit_span_ms": p["burst_submit_span_ms"],
            "repairs": p["repairs"], "final_position": p["final_position"],
            "realized_delta": p["realized_delta"], "nlv_delta": p["nlv_delta"],
            "fines_delta": p["fines_delta"], "success": int(bool(p["success"])),
            "reason": p["reason"], "payload_json": canonical_json(p),
        }, jsonl=True,
    )


def export_outputs(out_dir: Path, state: EngineState) -> None:
    tender_rows = []
    for key, t in sorted(state.tenders.items()):
        tender_rows.append({
            "round_index": t.round_index,
            "tender_id": t.tender_id,
            "action": t.raw.get("action"),
            "quantity": t.raw.get("quantity"),
            "price": t.raw.get("price"),
            "expires": t.raw.get("expires"),
            "first_edge": t.first_edge,
            "min_edge": t.min_edge,
            "max_edge": t.max_edge,
            "max_profit": t.max_profit,
            "trigger_edge": t.trigger_edge,
            "trigger_profit": t.trigger_profit,
            "edge_crossings_s": canonical_json({
                f"{lvl:.2f}": ((ns - t.first_seen_ns)/1e9) for lvl, ns in sorted(t.edge_crossings_ns.items())
            }),
            "shadow_horizons_done": canonical_json(sorted(t.shadow_horizons_done)),
            "eval_count": t.eval_count,
            "accepted": int(t.accepted),
            "shadow_triggered": int(t.shadow_triggered),
        })
    if tender_rows:
        with open(out_dir / "tenders.csv", "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=list(tender_rows[0].keys())); w.writeheader(); w.writerows(tender_rows)

    trade_rows = [trade_to_payload(t) for t in state.trades]
    if trade_rows:
        with open(out_dir / "trades.csv", "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=list(trade_rows[0].keys())); w.writeheader(); w.writerows(trade_rows)

    order_rows = []
    for tr in state.trades:
        for o in tr.orders:
            order_rows.append({
                "round_index": tr.round_index, "tender_id": as_int(tr.tender.get("tender_id")),
                "order_id": o.order_id, "ticker": o.ticker, "action": o.action,
                "requested_qty": o.requested_qty, "filled_qty": o.filled_qty,
                "status": o.status, "vwap": o.vwap, "submit_latency_ms": o.submit_latency_ms,
                "ambiguous": int(o.ambiguous), "error": o.error,
            })
    if order_rows:
        with open(out_dir / "orders.csv", "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=list(order_rows[0].keys())); w.writeheader(); w.writerows(order_rows)


def build_summary(state: EngineState, cfg: RuntimeConfig, args: argparse.Namespace, run_id: str) -> Dict[str, Any]:
    trades = [trade_to_payload(t) for t in state.trades]
    successful = [t for t in trades if t["success"]]
    account_nlv_delta = None
    account_realized_delta = None
    account_fines_delta = None
    if state.account_start is not None and state.account_end is not None:
        account_realized_delta, account_nlv_delta, account_fines_delta = accounting_delta(state.account_start, state.account_end)
    return {
        "version": VERSION,
        "run_id": run_id,
        "mode": "live" if args.live else "shadow",
        "policy_mode": args.mode,
        "threshold_edge_per_share": resolve_threshold(args),
        "runtime_config_final": runtime_config_dict(cfg),
        "rounds_completed": state.rounds_completed,
        "tenders_seen": len(state.tenders),
        "trades_attempted": len(trades),
        "trades_successful": len(successful),
        "halt_new_tenders": state.halt_new_tenders,
        "halt_reason": state.halt_reason,
        "config_changes": state.config_changes,
        "shadow_horizons_s": list(SHADOW_HORIZONS_S),
        "shadow_edge_levels": list(SHADOW_EDGE_LEVELS),
        "total_realized_delta": sum(t["realized_delta"] or 0.0 for t in successful),
        "total_nlv_delta": sum(t["nlv_delta"] or 0.0 for t in successful),
        "total_fines_delta": sum(t["fines_delta"] or 0.0 for t in trades),
        "account_nlv_delta_authoritative": account_nlv_delta,
        "account_realized_delta_authoritative": account_realized_delta,
        "account_fines_delta_authoritative": account_fines_delta,
        "mean_accept_latency_ms": mean_or_none([t["accept_latency_ms"] for t in trades if t["accept_latency_ms"] is not None]),
        "mean_booking_ms": mean_or_none([t["booking_ms"] for t in trades if t["booking_ms"] is not None]),
        "mean_burst_span_ms": mean_or_none([t["burst_submit_span_ms"] for t in trades if t["burst_submit_span_ms"] is not None]),
        "trades": trades,
        "intentional_nonfeatures": [
            "no_independent_cross_venue_arb",
            "no_passive_alt_tail",
            "no_unvalidated_limit_order_execution",
            "no_ml_or_es_thresholds",
            "no_live_participant_veto",
        ],
    }


# =============================================================================
# SELF TEST
# =============================================================================

def _mock_book(ticker: str, bids: Sequence[Tuple[float, int]], asks: Sequence[Tuple[float, int]]) -> ParsedBook:
    raw = {
        "bids": [{"price": p, "quantity": q, "quantity_filled": 0, "trader_id": "ANON", "order_id": i+1}
                 for i, (p, q) in enumerate(bids)],
        "asks": [{"price": p, "quantity": q, "quantity_filled": 0, "trader_id": "ANON", "order_id": 100+i+1}
                 for i, (p, q) in enumerate(asks)],
    }
    return parse_book(ticker, raw, mono_ns(), 0.1)


def self_test() -> None:
    # Published ALGO3 20k buy route regression used throughout development.
    # Chosen levels reproduce the course example allocation: Main 10,500 / Alt 9,500.
    books = {
        EXPECTED_MAIN: _mock_book(
            EXPECTED_MAIN,
            [(19.97, 6_700), (19.96, 5_400)],
            [(19.98, 7_400), (19.99, 5_400), (20.00, 5_600),
             (20.01, 5_300), (20.02, 5_300), (20.03, 6_300)],
        ),
        EXPECTED_ALT: _mock_book(
            EXPECTED_ALT,
            [(19.97, 9_000), (19.95, 8_300)],
            [(19.98, 9_500), (20.00, 9_700), (20.02, 9_000),
             (20.04, 7_200), (20.06, 8_100), (20.08, 8_500)],
        ),
    }
    fees = {EXPECTED_MAIN: 0.010, EXPECTED_ALT: 0.005}
    r = walk_route(books, 20_000, "BUY", fees)
    assert r["full_coverage"] and r["per_market"] == {EXPECTED_MAIN: 10_500, EXPECTED_ALT: 9_500}, r
    assert abs(r["raw_vwap"] - 19.98155) < 1e-9, r["raw_vwap"]
    assert abs(r["effective_vwap"] - 19.989175) < 1e-9, r["effective_vwap"]

    # Mirrored risk accounting counts the underlying once.
    cfg = RuntimeConfig(fees=fees, rebates={EXPECTED_MAIN: 0.0, EXPECTED_ALT: 0.0075}, max_order=25_000,
                        api_rate=100, exec_delay_ms=0, gross_limit=200_000, net_limit=100_000, securities={})
    ok, why = risk_admissible({"action": "BUY", "quantity": 89_000}, cfg, 0)
    assert ok, why
    ok, _ = risk_admissible({"action": "BUY", "quantity": 101_000}, cfg, 0)
    assert not ok

    # Reservation blocks overshoot.
    led = ReservationLedger(76_000)
    for q in (25_000, 25_000, 25_000, 1_000): led.reserve(q)
    assert led.submitted_qty == 76_000 and not led.can_submit(1)

    # Tender semantics: BUY tender => +inventory => SELL hedge.
    assert tender_expected_delta({"action": "BUY", "quantity": 76_000}) == 76_000
    assert opposite("BUY") == "SELL" and opposite("SELL") == "BUY"

    print("ALGO3 COMPETITION ENGINE SELF-TEST: PASS")
    print(f"Case-example raw VWAP:       {r['raw_vwap']:.6f}")
    print(f"Fee-adjusted VWAP:           {r['effective_vwap']:.6f}")
    print(f"Route: Main={r['per_market'][EXPECTED_MAIN]:,} Alt={r['per_market'][EXPECTED_ALT]:,}")
    print("Mirrored-risk regression:    89k admissible under net=100k/gross=200k")
    print("Reservation regression:      exact 76k authorized; overshoot blocked")


# =============================================================================
# CLI / MAIN
# =============================================================================

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="RIT ALGO3 race-first competition engine")
    p.add_argument("--self-test", action="store_true", help="offline deterministic tests only")
    p.add_argument("--preflight", action="store_true", help="read-only environment/clean-state check then exit")
    p.add_argument("--live", action="store_true", help="enable writes; also requires --confirmed")
    p.add_argument("--confirmed", action="store_true", help="explicit acknowledgement for simulated competition trading")
    p.add_argument("--mode", choices=sorted(MODE_EDGES), default="normal", help="edge policy preset")
    p.add_argument("--min-edge", type=float, default=None, help="override edge/share in dollars (0.05 = 5 cents)")
    p.add_argument("--pretrigger-margin", type=float, default=DEFAULT_PRETRIGGER_MARGIN)
    p.add_argument("--revalidate-cooldown", type=float, default=DEFAULT_REVALIDATE_COOLDOWN_S,
                   help="minimum seconds between fresh preaccept revalidations for the same tender")
    p.add_argument("--min-seconds-to-expiry", type=float, default=DEFAULT_MIN_SECONDS_TO_EXPIRY)
    p.add_argument("--min-seconds-to-round-end", type=float, default=DEFAULT_MIN_SECONDS_TO_ROUND_END)
    p.add_argument("--max-book-age", type=float, default=DEFAULT_MAX_BOOK_AGE_S)
    p.add_argument("--book-interval", type=float, default=DEFAULT_BOOK_REFRESH_S)
    p.add_argument("--tender-poll", type=float, default=DEFAULT_TENDER_POLL_S)
    p.add_argument("--tas-poll", type=float, default=DEFAULT_TAS_POLL_S)
    p.add_argument("--idle-poll", type=float, default=DEFAULT_IDLE_POLL_S)
    p.add_argument("--booking-poll", type=float, default=DEFAULT_BOOKING_POLL_S)
    p.add_argument("--reconcile-poll", type=float, default=DEFAULT_RECONCILE_POLL_S)
    p.add_argument("--booking-timeout", type=float, default=DEFAULT_BOOKING_TIMEOUT_S)
    p.add_argument("--reconcile-timeout", type=float, default=DEFAULT_RECONCILE_TIMEOUT_S)
    p.add_argument("--accounting-settle", type=float, default=DEFAULT_ACCOUNTING_SETTLE_S)
    p.add_argument("--config-refresh", type=float, default=DEFAULT_CONFIG_REFRESH_S)
    p.add_argument("--trader-refresh", type=float, default=DEFAULT_TRADER_REFRESH_S)
    p.add_argument("--max-repair-rounds", type=int, default=DEFAULT_MAX_REPAIR_ROUNDS)
    p.add_argument("--max-trades", type=int, default=5, help="hard cap across this process; 0 = unlimited")
    p.add_argument("--rounds", type=int, default=1, help="number of heats to observe/trade before exiting")
    p.add_argument("--verbose-revalidation", action="store_true")
    return p.parse_args()


def get_api_key() -> str:
    key = os.getenv("RIT_API_KEY", "").strip()
    if not key:
        raise RuntimeError("RIT_API_KEY is not set. Open RIT's API panel and set the current key in PowerShell.")
    return key


def install_signal_handlers() -> None:
    def handler(signum, frame):
        print(f"\n[SIGNAL] received {signum}; no new tenders will be accepted. Active reconciliation will continue.")
        stop_requested.set()
    signal.signal(signal.SIGINT, handler)
    if hasattr(signal, "SIGTERM"):
        signal.signal(signal.SIGTERM, handler)


def print_preflight(base_url: str, case: Mapping[str, Any], cfg: RuntimeConfig, before: PositionSnapshot, opens: Sequence[Mapping[str, Any]], threshold: float) -> None:
    print("\n=== ALGO3 COMPETITION PREFLIGHT ===")
    print(f"Base URL:        {base_url}")
    print(f"Case:            {case.get('name')} status={case.get('status')} tick={case.get('tick')}")
    print(f"Positions:       Main={before.m:,} Alt={before.a:,} (must mirror; flat required at startup)")
    print(f"Open THOR ords:  {len(opens)}")
    print(f"Fees:            Main={cfg.fees.get(EXPECTED_MAIN)} Alt={cfg.fees.get(EXPECTED_ALT)}")
    print(f"ALT rebate:      {cfg.rebates.get(EXPECTED_ALT)} (telemetry only; passive tail disabled)")
    print(f"Max order:       {cfg.max_order:,}")
    print(f"API rate hint:   {cfg.api_rate}")
    print(f"Exec delay ms:   {cfg.exec_delay_ms}")
    print(f"Limits:          gross={cfg.gross_limit:,} net={cfg.net_limit:,}")
    print(f"Trigger edge:    {threshold:.4f}/share")
    print("Write policy:    no blind retries; booking gate; full reservation-protected burst; reconcile after")


def main() -> int:
    args = parse_args()
    if args.self_test:
        self_test(); return 0
    if args.live != args.confirmed:
        raise SystemExit("LIVE writes require BOTH --live and --confirmed. Use neither for shadow mode.")
    threshold = resolve_threshold(args)
    if not (-1.0 <= threshold <= 5.0):
        raise SystemExit("edge threshold units are dollars/share; e.g. 0.05 = 5 cents")
    if args.pretrigger_margin < 0 or args.pretrigger_margin > 0.10:
        raise SystemExit("--pretrigger-margin should be between 0 and 0.10")
    if args.revalidate_cooldown < 0 or args.revalidate_cooldown > 2.0:
        raise SystemExit("--revalidate-cooldown should be between 0 and 2 seconds")
    if args.rounds < 1:
        raise SystemExit("--rounds must be >=1")

    api_key = get_api_key()
    base_url = discover_base_url(api_key)
    algo3_root = locate_algo3_root()
    out_root = algo3_root / "outputs"
    run_id = f"{run_stamp()}-{uuid.uuid4().hex[:8]}"
    out_dir = out_root / f"algo3_competition_{run_id}"
    out_dir.mkdir(parents=True, exist_ok=False)
    lock = InstanceLock(algo3_root / "algo3_write.lock")
    journal = Journal(out_dir, run_id)
    install_signal_handlers()
    market: Optional[MarketDataCache] = None
    tas: Optional[TASPoller] = None
    state = EngineState()
    cfg: Optional[RuntimeConfig] = None

    try:
        lock.acquire()
        client = RITClient(base_url, api_key, journal)
        cfg = discover_runtime_config(client)
        case = get_case(client)
        before, opens = validate_clean_start(client, cfg)
        state.account_start = before
        print_preflight(base_url, case, cfg, before, opens, threshold)

        manifest = {
            "version": VERSION, "run_id": run_id, "created_utc": utc_now(), "base_url": base_url,
            "mode": "live" if args.live else "shadow", "args": vars(args),
            "runtime_config_start": runtime_config_dict(cfg), "case_at_start": case,
            "calibrated_design": {
                "default_edge": 0.05, "booking_gate": True, "isolated_first_child": False,
                "full_reservation_burst": True, "mirrored_inventory_counted_once": True,
                "independent_speculation": False, "passive_tail": False,
            },
        }
        (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
        journal.event("startup", manifest, tick=safe_int(case.get("tick")))

        if args.preflight:
            summary = {"preflight_only": True, "runtime_config": runtime_config_dict(cfg), "case": case}
            (out_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
            return 0

        market = MarketDataCache(client, journal, args.book_interval, execution_in_progress)
        tas = TASPoller(client, journal, args.tas_poll, execution_in_progress)
        market.start(); tas.start()

        print("\n=== ALGO3 COMPETITION ENGINE STARTING ===")
        print(f"Run ID:          {run_id}")
        print(f"Output:          {out_dir}")
        print(f"Mode:            {'LIVE' if args.live else 'SHADOW'} / {args.mode.upper()}")
        print(f"Threshold:       {threshold:.4f}/share")
        print(f"Book interval:   {args.book_interval:.3f}s per venue")
        print(f"Tender interval: {args.tender_poll:.3f}s")
        print(f"Reval cooldown:  {args.revalidate_cooldown:.3f}s")
        print(f"Shadow horizons: {', '.join(str(x) for x in SHADOW_HORIZONS_S)} s")
        print("Participant/TAS telemetry is recorded; it does not create speculative orders.")

        for _ in range(args.rounds):
            if stop_requested.is_set():
                break
            cfg = run_one_round(client, journal, market, tas, cfg, args, state)
            if state.halt_new_tenders and args.live:
                # A transaction-state or fine failure is process-fatal for live writes.
                break

        # Final clean-state check. Do not silently leave inventory behind.
        try:
            state.account_end = sample_position(client, journal, "run_final", include_limits=True)
            pos = {EXPECTED_MAIN: state.account_end.m, EXPECTED_ALT: state.account_end.a}
            opens_final = open_thor_orders(get_orders(client))
            if pos[EXPECTED_MAIN] != 0 or pos[EXPECTED_ALT] != 0 or opens_final:
                state.halt_new_tenders = True
                state.halt_reason = state.halt_reason or f"nonclean_final_state:pos={pos},opens={len(opens_final)}"
                print(f"[WARNING] Final state not clean: {state.halt_reason}")
        except Exception as exc:
            print(f"[WARNING] Could not verify final state: {exc}")

        export_outputs(out_dir, state)
        summary = build_summary(state, cfg, args, run_id)
        (out_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
        print("\n=== FINAL SUMMARY ===")
        print(f"Rounds completed: {summary['rounds_completed']}")
        print(f"Tenders seen:     {summary['tenders_seen']}")
        print(f"Trades:           {summary['trades_successful']}/{summary['trades_attempted']} successful")
        print(f"Realized delta:   {pretty_money(summary['total_realized_delta'])}")
        if summary.get("account_nlv_delta_authoritative") is not None:
            print(f"Account NLV Δ:    {pretty_money(summary['account_nlv_delta_authoritative'])}")
        print(f"Fines delta:      {pretty_money(summary['total_fines_delta'])}")
        print(f"Output:           {out_dir}")
        return 0 if not state.halt_reason else 2

    except KeyboardInterrupt:
        stop_requested.set()
        return 130
    except Exception as exc:
        try:
            journal.event("fatal_error", {"error": f"{type(exc).__name__}: {exc}"})
        except Exception:
            pass
        print(f"\n[FATAL] {type(exc).__name__}: {exc}")
        return 1
    finally:
        if market is not None:
            market.stop()
        if tas is not None:
            tas.stop()
        # Persist partial output even after a failure.
        try:
            if not args.preflight:
                for tr in state.trades:
                    persist_trade_summary(journal, tr)
                export_outputs(out_dir, state)
                if cfg is not None:
                    (out_dir / "summary.json").write_text(json.dumps(build_summary(state, cfg, args, run_id), indent=2), encoding="utf-8")
        except Exception:
            pass
        journal.close()
        lock.release()


if __name__ == "__main__":
    raise SystemExit(main())
