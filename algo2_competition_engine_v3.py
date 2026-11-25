#Note: These are not my personal comments, I've been having chatgpt do this on all the scripts I submit for class. 

"""
algo2_competition
on_engine_v3.py

RIT ALGO2 single-stock market-making engine.

Design basis
------------
ALGO2 V3 is a throughput-first passive rebate harvester for the RIT classroom
simulator.  Live Columbia metadata showed a $0.010/share trading fee and
$0.015/share LIMIT rebate, so a passive fill has +$0.005/share of mechanical
incentive before spread/mark-to-market P&L.  The first live aggressive heat
made +$689 on ~90k passive shares while the class leaders were visibly
generating far more order/turnover.  V3 therefore optimizes queue presence,
replenishment and paired turnover rather than forecast sophistication.

Core behavior:
  * RANGE / 1c spread: reserve nearly the full safe inventory envelope on BOTH
    touches with stacked passive clips and replenish fills continuously.
  * RANGE / 2c spread: lead one side by one tick (still passive) to become the
    inside market; after inventory appears, the reducing side gets the inside
    priority.  This creates a passive rebate "ping-pong" instead of waiting at
    the back of six-figure classroom queues.
  * RANGE / >=3c spread: improve both sides one tick while remaining passive.
  * INVENTORY: size/capacity controls do the work; V3 does not price-skew good
    quotes away from the touch merely because inventory is non-zero.
  * TREND: retained as a tail-risk circuit breaker so a one-way graded heat
    cannot make the bot endlessly short a rally or buy a collapse.
  * ENDGAME: stop adding late and market-flatten the residual before tick 300.

Startup/restart policy:
  * V3 uses its OWN recovery file (algo2_v3_state.json); stale v1/v1.2 files are
    ignored completely.
  * A flat account with zero live ALGO orders is treated as authoritative after
    a short stability certification, even during an ACTIVE heat.
  * Continuous heats are the default; no manual restart is required.

The program is dry-run/read-only unless BOTH --live and --confirmed are supplied.
It is intended only for the Rotman Interactive Trader classroom simulator.
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
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Deque, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

import requests


VERSION = "ALGO2-COMP-3.0"
TICKER = "ALGO"
TICK_SIZE = 0.01
BASE_URL_CANDIDATES = (
    "http://localhost:9999/v1",
    "http://localhost:7238/v1",
    "http://localhost:20000/v1",
)
TERMINAL_STATUSES = {"TRANSACTED", "FILLED", "CANCELLED", "CANCELED", "REJECTED", "EXPIRED"}
OPEN_STATUSES = {"OPEN", "PENDING", "PARTIAL", "PARTIALLY_FILLED"}
STOP_REQUESTED = threading.Event()


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class StrategyConfig:
    mode: str = "volume"
    base_size: int = 5000
    operational_limit: int = 24000
    soft_limit: int = 20000
    panic_limit: int = 24000
    trend_target: int = 5000
    max_drawdown: float = 10000.0

    loop_s: float = 0.06
    book_depth: int = 60
    min_quote_life_s: float = 0.08
    reducing_quote_life_s: float = 0.05
    reprice_ticks: int = 1
    dangerous_drift_ticks: int = 1
    size_reprice_fraction: float = 0.20
    quote_layers: int = 5
    min_replenish_qty: int = 1000

    trend_lookback_ticks: int = 10
    trend_enter: float = 0.06
    trend_exit: float = 0.03
    trend_strong: float = 0.10
    adverse_stop_floor: float = 0.10
    adverse_stop_vol_mult: float = 5.0
    max_inventory_skew: float = 0.0
    shares_per_skew_tick: int = 100000

    improve_if_spread: float = 0.03
    high_vol_per_tick: float = 0.010
    reduce_only_tick: int = 290
    passive_unwind_tick: int = 292
    market_flatten_tick: int = 294
    end_tick: int = 300

    visibility_grace_s: float = 0.30
    missing_timeout_s: float = 3.0
    cancel_retry_s: float = 0.20
    state_poll_s: float = 0.05
    heartbeat_s: float = 1.0
    snapshot_log_s: float = 0.20
    config_refresh_s: float = 5.0
    trader_refresh_s: float = 0.50

    default_order_rate: float = 5.0
    default_max_order: int = 5000
    default_position_limit: int = 25000
    default_fee: float = 0.01
    default_rebate: float = 0.005

    @classmethod
    def preset(cls, mode: str) -> "StrategyConfig":
        mode = mode.lower()
        if mode == "normal":
            return cls(mode=mode, base_size=5000, operational_limit=22000,
                       soft_limit=17000, panic_limit=21500, quote_layers=4,
                       max_drawdown=6000.0, min_quote_life_s=0.20,
                       visibility_grace_s=0.40, reduce_only_tick=288,
                       market_flatten_tick=295)
        if mode in {"volume", "turbo", "max"}:
            # V3 competition default: saturate the safe passive inventory envelope.
            return cls(mode="volume")
        raise ValueError(f"unknown mode {mode!r}")


@dataclass
class RuntimeConfig:
    max_order: int
    position_limit: int
    operational_limit: int
    order_rate: float
    fee: float
    rebate: float
    execution_delay_ms: float
    raw_security: Dict[str, Any] = field(default_factory=dict)
    raw_limits: Any = None


@dataclass
class MarketState:
    tick: int
    bid: float
    ask: float
    mid: float
    spread: float
    microprice: float
    bid_qty: int
    ask_qty: int
    volatility: float
    trend_move: float
    trend_regime: str
    trend_strength: float
    fair: float


@dataclass
class QuoteTarget:
    buy_price: Optional[float]
    buy_qty: int
    sell_price: Optional[float]
    sell_qty: int
    reason: str


@dataclass
class WriteResult:
    response: Optional[requests.Response]
    body: Any
    latency_ms: Optional[float]
    ambiguous: bool
    error: Optional[str]


# =============================================================================
# SMALL HELPERS
# =============================================================================

def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def run_stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def mono() -> float:
    return time.monotonic()


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


def first_number(row: Mapping[str, Any], *names: str, default: Optional[float] = None) -> Optional[float]:
    for name in names:
        if row.get(name) is not None:
            v = safe_float(row.get(name))
            if v is not None:
                return v
    return default


def first_int(row: Mapping[str, Any], *names: str, default: Optional[int] = None) -> Optional[int]:
    v = first_number(row, *names, default=None)
    return int(round(v)) if v is not None else default


def canonical(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str)


def floor_tick(x: float) -> float:
    return round(math.floor((x + 1e-10) / TICK_SIZE) * TICK_SIZE, 2)


def ceil_tick(x: float) -> float:
    return round(math.ceil((x - 1e-10) / TICK_SIZE) * TICK_SIZE, 2)


def round_tick(x: float) -> float:
    return round(round(float(x) / TICK_SIZE) * TICK_SIZE, 2)


def clamp(x: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, x))


def order_remaining(o: Mapping[str, Any]) -> int:
    q = first_int(o, "quantity", "original_quantity", default=0) or 0
    f = first_int(o, "quantity_filled", "filled", "filled_quantity", default=0) or 0
    return max(0, q - f)


def order_status(o: Mapping[str, Any]) -> str:
    return str(o.get("status") or o.get("state") or "").upper()


def pretty_money(x: Optional[float]) -> str:
    return "N/A" if x is None else f"${x:,.2f}"


def locate_algo2_root() -> Path:
    here = Path(__file__).resolve().parent
    if here.name.lower() in {"src", "pipeline"} and here.parent.name.lower() == "algo2":
        return here.parent
    if here.name.lower() == "algo2":
        return here
    for p in [here] + list(here.parents):
        if p.name.lower() == "algo2":
            return p
    return here


# =============================================================================
# SINGLE INSTANCE LOCK
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
                raise RuntimeError(f"Another ALGO2 engine appears to hold {self.path}") from exc
        else:
            import fcntl
            try:
                fcntl.flock(self.fp.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError as exc:
                raise RuntimeError(f"Another ALGO2 engine appears to hold {self.path}") from exc
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
            self.fp.close()
            self.fp = None


# =============================================================================
# TELEMETRY
# =============================================================================

SCHEMA = """
PRAGMA journal_mode=WAL;
PRAGMA synchronous=NORMAL;
CREATE TABLE IF NOT EXISTS events(
 id INTEGER PRIMARY KEY AUTOINCREMENT, ts_utc TEXT, mono_ns INTEGER, kind TEXT,
 tick INTEGER, payload_json TEXT);
CREATE TABLE IF NOT EXISTS snapshots(
 id INTEGER PRIMARY KEY AUTOINCREMENT, ts_utc TEXT, mono_ns INTEGER, tick INTEGER,
 position INTEGER, vwap REAL, realized REAL, unrealized REAL, nlv REAL, fines REAL,
 bid REAL, ask REAL, mid REAL, spread REAL, microprice REAL, bid_qty INTEGER,
 ask_qty INTEGER, volatility REAL, trend_move REAL, trend_regime TEXT,
 trend_strength REAL, fair REAL, target_buy REAL, target_buy_qty INTEGER,
 target_sell REAL, target_sell_qty INTEGER, raw_book_json TEXT, raw_security_json TEXT);
CREATE TABLE IF NOT EXISTS order_events(
 id INTEGER PRIMARY KEY AUTOINCREMENT, ts_utc TEXT, mono_ns INTEGER, tick INTEGER,
 phase TEXT, order_id INTEGER, action TEXT, otype TEXT, price REAL,
 requested_qty INTEGER, filled_qty INTEGER, status TEXT, latency_ms REAL,
 payload_json TEXT);
CREATE TABLE IF NOT EXISTS http_samples(
 id INTEGER PRIMARY KEY AUTOINCREMENT, ts_utc TEXT, method TEXT, endpoint TEXT,
 status_code INTEGER, latency_ms REAL, ambiguous INTEGER, error TEXT);
CREATE TABLE IF NOT EXISTS book_orders(
 id INTEGER PRIMARY KEY AUTOINCREMENT, ts_utc TEXT, mono_ns INTEGER, tick INTEGER,
 side TEXT, trader_id TEXT, order_id INTEGER, price REAL, remaining INTEGER,
 distance_from_mid REAL, is_self INTEGER);
"""


class Journal:
    def __init__(self, out_dir: Path) -> None:
        self.out_dir = out_dir
        self.db_path = out_dir / "algo2_v3_engine.sqlite"
        self.jsonl_path = out_dir / "algo2_v3_events.jsonl"
        self.q: queue.Queue = queue.Queue(maxsize=100000)
        self.stop_evt = threading.Event()
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def put(self, table: str, row: Mapping[str, Any], mirror: bool = False) -> None:
        self.q.put((table, dict(row), mirror))

    def event(self, kind: str, payload: Mapping[str, Any], tick: Optional[int] = None) -> None:
        self.put("events", {
            "ts_utc": utc_now(), "mono_ns": mono_ns(), "kind": kind,
            "tick": tick, "payload_json": canonical(payload)
        }, mirror=True)

    def close(self) -> None:
        self.stop_evt.set()
        self.thread.join(timeout=10)

    def _run(self) -> None:
        self.out_dir.mkdir(parents=True, exist_ok=True)
        con = sqlite3.connect(self.db_path, timeout=30)
        con.executescript(SCHEMA)
        con.commit()
        jf = open(self.jsonl_path, "a", encoding="utf-8")
        batch = 0
        try:
            while not self.stop_evt.is_set() or not self.q.empty():
                try:
                    table, row, mirror = self.q.get(timeout=0.1)
                except queue.Empty:
                    if batch:
                        con.commit(); batch = 0
                    continue
                cols = list(row)
                con.execute(
                    f"INSERT INTO {table} ({','.join(cols)}) VALUES ({','.join('?' for _ in cols)})",
                    [row[c] for c in cols],
                )
                batch += 1
                if mirror:
                    jf.write(canonical({"table": table, "row": row}) + "\n")
                    jf.flush()
                if batch >= 100:
                    con.commit(); batch = 0
        finally:
            con.commit(); con.close(); jf.close()


# =============================================================================
# API WRAPPER
# =============================================================================

class RITAPI:
    def __init__(self, base_url: str, api_key: str, journal: Journal, order_rate: float) -> None:
        self.base = base_url.rstrip("/")
        self.s = requests.Session()
        self.s.trust_env = False
        self.s.headers.update({"X-API-Key": api_key})
        self.journal = journal
        self.set_order_rate(order_rate)
        self.next_write = 0.0

    def set_order_rate(self, rate: float) -> None:
        self.order_rate = max(0.5, float(rate))
        self.write_gap = 1.0 / (self.order_rate * 0.98)

    def _http_log(self, method: str, path: str, status: Optional[int], latency: float,
                  ambiguous: bool = False, error: Optional[str] = None) -> None:
        self.journal.put("http_samples", {
            "ts_utc": utc_now(), "method": method, "endpoint": path,
            "status_code": status, "latency_ms": latency,
            "ambiguous": int(ambiguous), "error": error
        })

    def get(self, path: str, params: Optional[Mapping[str, Any]] = None,
            retries: int = 3, allow_404: bool = False) -> Any:
        last = None
        for i in range(retries):
            t0 = time.perf_counter()
            try:
                r = self.s.get(self.base + path, params=dict(params or {}), timeout=(0.5, 1.5))
                lat = (time.perf_counter() - t0) * 1000
                self._http_log("GET", path, r.status_code, lat)
                if r.status_code == 401:
                    raise RuntimeError("401 Unauthorized: RIT_API_KEY does not match the RIT client")
                if r.status_code == 429:
                    wait = 0.15
                    try: wait = float(r.json().get("wait", wait))
                    except Exception: pass
                    time.sleep(min(1.0, max(0.05, wait)))
                    continue
                if r.status_code == 404 and allow_404:
                    return None
                r.raise_for_status()
                return r.json() if r.content else {}
            except RuntimeError:
                raise
            except requests.RequestException as exc:
                lat = (time.perf_counter() - t0) * 1000
                self._http_log("GET", path, None, lat, error=f"{type(exc).__name__}: {exc}")
                last = exc
                time.sleep(0.03 * (i + 1))
        raise RuntimeError(f"GET {path} failed: {last}")

    def write_once(self, method: str, path: str,
                   params: Optional[Mapping[str, Any]] = None) -> WriteResult:
        wait = self.next_write - mono()
        if wait > 0:
            time.sleep(wait)
        self.next_write = mono() + self.write_gap
        t0 = time.perf_counter()
        try:
            r = self.s.request(method, self.base + path, params=dict(params or {}), timeout=(0.5, 1.5))
            lat = (time.perf_counter() - t0) * 1000
            self._http_log(method, path, r.status_code, lat)
            body = None
            try: body = r.json() if r.content else {}
            except Exception: body = r.text
            if r.status_code == 429:
                # Explicit rejection: do not replay. Slow future writes using the
                # server hint and a conservative rate reduction.
                wait_hint = 0.25
                try:
                    if isinstance(body, Mapping):
                        wait_hint = float(body.get("wait", body.get("retry_after", wait_hint)))
                except Exception:
                    pass
                self.next_write = max(self.next_write, mono() + max(0.05, min(2.0, wait_hint)))
                self.set_order_rate(max(0.5, self.order_rate * 0.85))
            # Explicit HTTP response is not transport-ambiguous.
            return WriteResult(r, body, lat, False, None)
        except requests.RequestException as exc:
            lat = (time.perf_counter() - t0) * 1000
            err = f"{type(exc).__name__}: {exc}"
            self._http_log(method, path, None, lat, ambiguous=True, error=err)
            return WriteResult(None, None, lat, True, err)

    def case(self) -> Dict[str, Any]:
        x = self.get("/case")
        return dict(x) if isinstance(x, Mapping) else {}

    def securities(self) -> List[Dict[str, Any]]:
        x = self.get("/securities")
        return [dict(v) for v in x] if isinstance(x, list) else []

    def security(self) -> Dict[str, Any]:
        rows = self.get("/securities", {"ticker": TICKER})
        if isinstance(rows, list):
            for row in rows:
                if row.get("ticker") == TICKER:
                    return dict(row)
        raise RuntimeError(f"Security {TICKER} not returned by /securities")

    def limits(self) -> Any:
        return self.get("/limits")

    def trader(self) -> Dict[str, Any]:
        x = self.get("/trader")
        return dict(x) if isinstance(x, Mapping) else {}

    def book(self, limit: int = 50) -> Dict[str, Any]:
        x = self.get("/securities/book", {"ticker": TICKER, "limit": limit})
        return dict(x) if isinstance(x, Mapping) else {"bids": [], "asks": []}

    def open_orders(self) -> List[Dict[str, Any]]:
        x = self.get("/orders", {"status": "OPEN"})
        if not isinstance(x, list):
            return []
        return [dict(o) for o in x if o.get("ticker") == TICKER]

    def orders_by_status(self, status: str) -> List[Dict[str, Any]]:
        x = self.get("/orders", {"status": status})
        if not isinstance(x, list):
            return []
        return [dict(o) for o in x if o.get("ticker") == TICKER]

    def order_detail(self, oid: int) -> Optional[Dict[str, Any]]:
        x = self.get(f"/orders/{oid}", allow_404=True, retries=2)
        return dict(x) if isinstance(x, Mapping) else None


# =============================================================================
# RUNTIME DISCOVERY
# =============================================================================

def discover_base_url(key: str) -> str:
    env = os.getenv("RIT_BASE_URL", "").strip()
    candidates = ([env] if env else []) + list(BASE_URL_CANDIDATES)
    seen = set()
    for base in candidates:
        if not base or base in seen: continue
        seen.add(base)
        try:
            s = requests.Session(); s.trust_env = False
            s.headers["X-API-Key"] = key
            r = s.get(base.rstrip("/") + "/case", timeout=0.5)
            if r.status_code == 200:
                return base.rstrip("/")
        except Exception:
            pass
    raise RuntimeError("Could not locate the local RIT REST API; check RIT client/API panel")


def parse_runtime(sec: Mapping[str, Any], limits: Any, cfg: StrategyConfig) -> RuntimeConfig:
    max_order = first_int(sec, "max_trade_size", "max_order_size", default=cfg.default_max_order) or cfg.default_max_order
    rate = first_number(sec, "api_orders_per_second", "api_rate", "order_rate_limit", default=cfg.default_order_rate) or cfg.default_order_rate
    fee = first_number(sec, "fee", "trading_fee", "market_order_fee", default=cfg.default_fee) or 0.0
    rebate = first_number(sec, "limit_order_rebate", "rebate", "maker_rebate", default=cfg.default_rebate) or 0.0
    delay = first_number(sec, "execution_delay_ms", "execution_delay", default=0.0) or 0.0
    pos_limit = cfg.default_position_limit
    if isinstance(limits, list):
        vals = []
        for row in limits:
            if isinstance(row, Mapping):
                for k in ("net_limit", "gross_limit"):
                    v = safe_int(row.get(k))
                    if v is not None and v > 0: vals.append(v)
        if vals: pos_limit = min(vals)
    buffer = 1000 if cfg.mode == "volume" else 3000
    op_limit = min(cfg.operational_limit, max(1000, pos_limit - buffer))
    return RuntimeConfig(int(max_order), int(pos_limit), int(op_limit), float(rate), float(fee), float(rebate), float(delay), dict(sec), limits)


def runtime_signature(r: RuntimeConfig) -> Tuple[Any, ...]:
    """Only fields that alter trading mechanics; exclude live price/position metadata."""
    return (
        r.max_order, r.position_limit, r.operational_limit,
        round(r.order_rate, 8), round(r.fee, 8), round(r.rebate, 8),
        round(r.execution_delay_ms, 8),
    )


def adapt_strategy_to_runtime(cfg: StrategyConfig, r: RuntimeConfig) -> None:
    """Keep all strategy thresholds inside whatever limit the live case advertises."""
    cfg.operational_limit = min(cfg.operational_limit, r.operational_limit)
    cfg.base_size = min(cfg.base_size, r.max_order)
    if cfg.mode == "volume":
        # TURBO intentionally uses most of the legal inventory envelope; outstanding
        # orders are still reserved by capacity(), so this does not permit a 25k breach.
        cfg.soft_limit = min(cfg.soft_limit, max(1000, int(0.80 * r.position_limit)),
                             cfg.operational_limit)
        cfg.panic_limit = min(cfg.panic_limit, max(cfg.soft_limit + 1000, int(0.96 * r.position_limit)),
                              cfg.operational_limit)
    else:
        cfg.soft_limit = min(cfg.soft_limit, max(1000, int(0.50 * r.position_limit)),
                             cfg.operational_limit)
        cfg.panic_limit = min(cfg.panic_limit, max(cfg.soft_limit + 1000, int(0.82 * r.position_limit)),
                              cfg.operational_limit)
    cfg.trend_target = min(cfg.trend_target, cfg.base_size, max(500, cfg.soft_limit // 2))


# =============================================================================
# BOOK / SIGNALS
# =============================================================================

def aggregate_external(book: Mapping[str, Any], my_trader: Optional[str], my_ids: set[int]) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    out = []
    for key in ("bids", "asks"):
        rows = []
        for raw in book.get(key, []) or []:
            if not isinstance(raw, Mapping): continue
            q = order_remaining(raw)
            p = safe_float(raw.get("price"))
            if q <= 0 or p is None: continue
            oid = safe_int(raw.get("order_id"))
            trader = str(raw.get("trader_id") or "")
            if (oid is not None and oid in my_ids) or (my_trader and trader == my_trader):
                continue
            row = dict(raw); row["_remaining"] = q; row["_price"] = p
            rows.append(row)
        rows.sort(key=lambda x: x["_price"], reverse=(key == "bids"))
        out.append(rows)
    return out[0], out[1]


def top_level_qty(rows: Sequence[Mapping[str, Any]]) -> int:
    if not rows: return 0
    p = float(rows[0]["_price"])
    return sum(int(r["_remaining"]) for r in rows if abs(float(r["_price"]) - p) < 1e-9)


def microprice(bids: Sequence[Mapping[str, Any]], asks: Sequence[Mapping[str, Any]]) -> Optional[float]:
    if not bids or not asks: return None
    bp, ap = float(bids[0]["_price"]), float(asks[0]["_price"])
    bq, aq = top_level_qty(bids), top_level_qty(asks)
    if bq + aq <= 0: return (bp + ap) / 2
    return (bp * aq + ap * bq) / (bq + aq)


class SignalEngine:
    def __init__(self, cfg: StrategyConfig) -> None:
        self.cfg = cfg
        self.history: Deque[Tuple[int, float]] = deque(maxlen=80)
        self.regime = "RANGE"

    def observe(self, tick: int, mid: float) -> None:
        if not self.history or self.history[-1][0] != tick:
            self.history.append((tick, mid))
        else:
            self.history[-1] = (tick, mid)

    def _past_mid(self, tick: int, lookback: int) -> float:
        target = tick - lookback
        candidates = [m for t, m in self.history if t <= target]
        return candidates[-1] if candidates else self.history[0][1]

    def values(self, tick: int) -> Tuple[float, float, str, float]:
        if len(self.history) < 2:
            return 0.0, 0.0, self.regime, 0.0
        mids = [m for _, m in self.history]
        changes = [b-a for a,b in zip(mids, mids[1:])]
        # Risk-speed proxy: standard deviation catches chop, while mean absolute
        # tick travel catches a fast market whose moves are too steady to have
        # much statistical variance. The latter is the failure mode documented
        # in several 2026 ALGO2 graded runs.
        if len(changes) >= 3:
            recent = changes[-20:]
            vol = max(statistics.pstdev(recent), statistics.fmean(abs(x) for x in recent[-10:]))
        else:
            vol = statistics.fmean(abs(x) for x in changes) if changes else 0.0
        past = self._past_mid(tick, self.cfg.trend_lookback_ticks)
        move = mids[-1] - past

        # Hysteresis: enter at 4c/10 ticks, leave only after dropping below 2c.
        if self.regime == "RANGE":
            if move >= self.cfg.trend_enter:
                self.regime = "UP"
            elif move <= -self.cfg.trend_enter:
                self.regime = "DOWN"
        elif self.regime == "UP":
            if move <= -self.cfg.trend_enter:
                self.regime = "DOWN"
            elif abs(move) <= self.cfg.trend_exit:
                self.regime = "RANGE"
        elif self.regime == "DOWN":
            if move >= self.cfg.trend_enter:
                self.regime = "UP"
            elif abs(move) <= self.cfg.trend_exit:
                self.regime = "RANGE"
        strength = abs(move) / max(self.cfg.trend_enter, 1e-9)
        return vol, move, self.regime, strength


# =============================================================================
# STATE / ORDER RECONCILIATION
# =============================================================================

class PersistentState:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.expected_position = 0
        self.records: Dict[str, Dict[str, Any]] = {}
        self.unknown = False
        self._last = None

    def load(self) -> None:
        if not self.path.exists(): return
        d = json.loads(self.path.read_text(encoding="utf-8"))
        self.expected_position = int(d.get("expected_position", 0))
        self.records = dict(d.get("records", {}))
        self.unknown = bool(d.get("unknown", False))

    def save(self) -> None:
        snap = canonical({"expected_position": self.expected_position, "records": self.records,
                          "unknown": self.unknown, "ticker": TICKER})
        if snap == self._last and self.path.exists(): return
        tmp = self.path.with_suffix(self.path.suffix + ".tmp")
        with tmp.open("w", encoding="utf-8") as f:
            f.write(snap); f.flush(); os.fsync(f.fileno())
        os.replace(tmp, self.path)
        self._last = snap

    def clean(self) -> bool:
        return not self.unknown and not self.records and self.expected_position == 0


def certify_flat_midheat_recovery(
    api: "RITAPI",
    state: PersistentState,
    journal: "Journal",
    cfg: StrategyConfig,
    case: Mapping[str, Any],
) -> Tuple[bool, str]:
    """Certify that an unresolved *local* recovery file is stale.

    This is intentionally stronger than simply deleting algo2_state.json.  It is
    used only at startup, before any new write is allowed.  The live RIT server is
    treated as authoritative after we establish all of the following:

      1. Current ALGO position is exactly flat.
      2. There are no live/open ALGO orders.
      3. Any persisted order IDs that still exist are terminal, never OPEN.
      4. Flat/no-open state remains unchanged for a window longer than the normal
         RIT publication grace period.  This covers the prior-run failure mode in
         which a POST response was lost before its order_id was persisted.

    If any evidence of current exposure/order uncertainty appears, certification
    fails and the original fail-closed behavior remains in force.
    """
    if state.clean():
        return True, "already_clean"

    # First resolve every persisted ID we can see in the server's order history.
    order_index: Dict[str, Dict[str, Any]] = {}
    try:
        for status in ("OPEN", "TRANSACTED", "CANCELLED"):
            for o in api.orders_by_status(status):
                if o.get("order_id") is not None:
                    order_index[str(o.get("order_id"))] = dict(o)
    except Exception as exc:
        return False, f"order_history_unavailable:{type(exc).__name__}:{exc}"

    resolved_terminal = 0
    missing_ids: List[str] = []
    for oid, rec in state.records.items():
        o = order_index.get(str(oid))
        if o is None:
            try:
                o = api.order_detail(int(oid))
            except Exception:
                o = None
        if o is None:
            missing_ids.append(str(oid))
            continue
        st = order_status(o)
        if st not in TERMINAL_STATUSES:
            return False, f"persisted_order_still_live:{oid}:{st}"
        # If RIT re-used an ID and the payload no longer matches our persisted
        # intent, do not pretend it proves anything; the stability window below
        # still has to certify a clean account.
        act = str(o.get("action") or "").upper()
        qty = first_int(o, "quantity", default=None)
        if act and act != str(rec.get("action") or "").upper():
            missing_ids.append(str(oid))
            continue
        if qty is not None and int(qty) != int(rec.get("quantity", qty)):
            missing_ids.append(str(oid))
            continue
        resolved_terminal += 1

    # Unknown=True means a previous process persisted uncertainty immediately
    # before a write and may have died before learning the order ID.  The only
    # safe automatic resolution is to observe a stable flat/no-open server state
    # for substantially longer than the expected publication delay.
    stability_s = max(1.0, float(cfg.visibility_grace_s) * 3.0)
    poll_s = 0.20
    deadline = mono() + stability_s
    samples = 0
    start_status = str(case.get("status") or "").upper()
    start_tick = safe_int(case.get("tick"))

    while mono() < deadline:
        try:
            live_case = api.case()
            sec = api.security()
            opens = api.open_orders()
        except Exception as exc:
            return False, f"recovery_probe_failed:{type(exc).__name__}:{exc}"
        pos = first_int(sec, "position", default=0) or 0
        if pos != 0:
            return False, f"position_changed_during_recovery:{pos}"
        if opens:
            ids = [o.get("order_id") for o in opens[:5]]
            return False, f"open_orders_appeared_during_recovery:{ids}"
        status = str(live_case.get("status") or "").upper()
        # A heat transition while certifying invalidates the observation window;
        # let normal startup/round-reset logic handle the new state instead.
        if status != start_status:
            return False, f"case_status_changed:{start_status}->{status}"
        samples += 1
        time.sleep(poll_s)

    # One final authoritative check after the stability window.
    sec = api.security(); opens = api.open_orders()
    pos = first_int(sec, "position", default=0) or 0
    if pos != 0 or opens:
        return False, f"final_recovery_check_failed:position={pos},open_orders={len(opens)}"

    before = {
        "expected_position": state.expected_position,
        "unknown": state.unknown,
        "record_ids": sorted(state.records.keys()),
        "resolved_terminal": resolved_terminal,
        "missing_or_stale_ids": missing_ids,
        "case_status": start_status,
        "case_tick": start_tick,
        "stability_s": stability_s,
        "samples": samples,
    }
    state.expected_position = 0
    state.records = {}
    state.unknown = False
    state.save()
    journal.event("persistent_state_certified_flat", before, start_tick)
    return True, "certified_flat_stable_no_open_orders"


class OrderManager:
    def __init__(self, api: RITAPI, journal: Journal, cfg: StrategyConfig,
                 runtime: RuntimeConfig, live: bool, state_path: Path) -> None:
        self.api, self.journal, self.cfg, self.runtime, self.live = api, journal, cfg, runtime, live
        self.state = PersistentState(state_path)
        self.state.load()
        self.my_trader: Optional[str] = None
        self.last_cancel: Dict[str, float] = {}
        self.submitted = 0
        self.cancelled = 0
        self.market_orders = 0
        self.limit_orders = 0
        self.fill_shares = 0
        self.active_shares = 0

    def initialize(self, trader: Mapping[str, Any], sec: Mapping[str, Any],
                   allow_round_reset: bool = False) -> None:
        self.my_trader = str(trader.get("trader_id") or trader.get("id") or "") or None
        actual = first_int(sec, "position", default=0) or 0
        opens = self.api.open_orders()
        if self.live:
            # A newly started simulator heat authoritatively resets prior-period
            # positions/orders.  We may clear old terminal bookkeeping only when
            # the new heat is visibly flat, has no open orders, and no transport-
            # ambiguous write is outstanding.
            if allow_round_reset and actual == 0 and not opens:
                # A fresh simulator heat is authoritative. Even if the previous
                # process/heat died after an ambiguous transport response, RIT has
                # now reset the case and is visibly flat with no live orders. Clear
                # bookkeeping from the prior heat; do NOT do this mid-heat.
                self.state.expected_position = 0
                self.state.records = {}
                self.state.unknown = False
                self.state.save()
            if self.state.unknown or self.state.records or self.state.expected_position != 0:
                raise RuntimeError("Persistent ALGO2 state is unresolved from a previous run. Reconcile RIT manually before live restart.")
            if actual != 0 or opens:
                raise RuntimeError(f"Live start requires flat/no orders. position={actual}, open_orders={len(opens)}")
        # Shadow/preflight observation must NEVER overwrite a persistent live
        # recovery state. In live mode, a clean file is initialized to the
        # observed flat position. In shadow, state exists only in memory.
        self.state.expected_position = actual
        self.state.records = {}
        self.state.unknown = False
        if self.live:
            self.state.save()

    def my_ids(self) -> set[int]:
        return {int(k) for k in self.state.records if str(k).isdigit()}

    def _find_order_anywhere(self, oid: str) -> Optional[Dict[str, Any]]:
        detail = self.api.order_detail(int(oid))
        if detail is not None: return detail
        for status in ("OPEN", "TRANSACTED", "CANCELLED"):
            try:
                for o in self.api.orders_by_status(status):
                    if str(o.get("order_id")) == str(oid): return o
            except Exception:
                pass
        return None

    def reconcile(self) -> Tuple[int, List[Dict[str, Any]]]:
        if self.state.unknown:
            raise RuntimeError("Unknown POST outcome; new writes blocked")
        now = mono()
        provisional: List[Dict[str, Any]] = []

        # Fetch the live order set once.  Only records that disappeared from OPEN
        # need an individual detail lookup, which keeps GET load roughly constant
        # even when TURBO has 6-8 quotes resting simultaneously.
        opened_api = self.api.open_orders()
        open_by_id: Dict[str, Dict[str,Any]] = {
            str(o.get("order_id")): dict(o) for o in opened_api if o.get("order_id") is not None
        }

        for oid, rec in list(self.state.records.items()):
            o = open_by_id.get(str(oid))
            if o is None:
                o = self.api.order_detail(int(oid))
            if o is None:
                age = now - float(rec.get("created", now))
                if age <= self.cfg.visibility_grace_s:
                    p = dict(rec); p.update(order_id=int(oid), ticker=TICKER,
                                            quantity_filled=rec.get("filled",0), status="PROVISIONAL")
                    provisional.append(p)
                    continue
                # Rare fallback for RIT builds where detail publication lags the
                # status-list endpoint longer than expected.
                o = self._find_order_anywhere(oid)
            if o is None:
                missing = rec.setdefault("missing_since", now)
                self.state.save()
                if now - missing > self.cfg.missing_timeout_s:
                    raise RuntimeError(f"Order {oid} missing beyond timeout; writes blocked")
                raise RuntimeError(f"Order {oid} awaiting publication/reconciliation")

            rec.pop("missing_since", None)
            rec["seen"] = True
            if str(o.get("action")) != rec["action"] or int(o.get("quantity",0)) != int(rec["quantity"]):
                raise RuntimeError(f"Order {oid} record mismatch")
            filled = first_int(o, "quantity_filled", "filled", default=0) or 0
            if not int(rec.get("filled",0)) <= filled <= int(rec["quantity"]):
                raise RuntimeError(f"Invalid cumulative fill for order {oid}")
            delta = filled - int(rec.get("filled",0))
            if delta:
                sign = 1 if rec["action"] == "BUY" else -1
                self.state.expected_position += sign * delta
                self.fill_shares += delta
                if rec.get("price") is None:
                    self.active_shares += delta
                rec["filled"] = filled
                self.journal.event("fill", {"order_id":int(oid), "action":rec["action"],
                                            "delta":delta, "cumulative":filled,
                                            "expected_position":self.state.expected_position,
                                            "price":rec.get("price")})
            st = order_status(o)
            rec["status"] = st
            self.state.save()

        actual = first_int(self.api.security(), "position", default=0) or 0
        if actual != self.state.expected_position:
            raise RuntimeError(f"Position publication mismatch expected={self.state.expected_position} actual={actual}")

        known_ids = set(self.state.records)
        if any(str(o.get("order_id")) not in known_ids for o in opened_api):
            raise RuntimeError("External/manual ALGO order detected")
        open_ids = {str(o.get("order_id")) for o in opened_api}
        for oid in list(self.state.records):
            if self.state.records[oid].get("status") in TERMINAL_STATUSES and oid not in open_ids:
                del self.state.records[oid]
        self.state.save()
        opened = list(opened_api)
        opened.extend(provisional)
        return actual, opened

    def capacity(self, position: int, opened: Sequence[Mapping[str, Any]]) -> Tuple[int,int]:
        buys = sum(order_remaining(o) for o in opened if o.get("action") == "BUY")
        sells = sum(order_remaining(o) for o in opened if o.get("action") == "SELL")
        lim = self.runtime.operational_limit
        return max(0, lim - position - buys), max(0, lim + position - sells)

    def submit(self, action: str, qty: int, price: Optional[float], tick: int) -> Optional[int]:
        if not self.live: return None
        position, opened = self.reconcile()
        # Multiple same-side passive clips are permitted.  Capacity() reserves
        # every outstanding share, so stacking cannot breach the operational
        # envelope even if all same-side quotes fill before the other side.
        case = self.api.case()
        if case.get("status") != "ACTIVE" or int(case.get("tick",300)) >= self.cfg.end_tick:
            return None
        maxq = min(self.runtime.max_order, self.cfg.base_size if price is not None else self.runtime.max_order)
        qty = min(int(qty), maxq)
        buycap, sellcap = self.capacity(position, opened)
        qty = min(qty, buycap if action == "BUY" else sellcap)
        if price is None:  # market orders may only reduce existing exposure
            if (action == "BUY" and position >= 0) or (action == "SELL" and position <= 0):
                return None
            qty = min(qty, abs(position))
        if qty <= 0: return None

        # Fresh passivity check for LIMIT orders immediately before irreversible POST.
        if price is not None:
            book = self.api.book(self.cfg.book_depth)
            bids, asks = aggregate_external(book, self.my_trader, self.my_ids())
            if not bids or not asks: return None
            best_bid, best_ask = float(bids[0]["_price"]), float(asks[0]["_price"])
            if action == "BUY" and price >= best_ask: return None
            if action == "SELL" and price <= best_bid: return None

        latest = self.api.case()
        if latest.get("status") != "ACTIVE" or int(latest.get("tick",300)) >= self.cfg.end_tick:
            return None

        params = {"ticker":TICKER, "action":action, "quantity":qty,
                  "type":"LIMIT" if price is not None else "MARKET"}
        if price is not None: params["price"] = round(float(price),2)

        # Persist uncertainty BEFORE transmitting. A lost response is never replayed.
        self.state.unknown = True; self.state.save()
        wr = self.api.write_once("POST", "/orders", params)
        self.journal.put("order_events", {
            "ts_utc":utc_now(), "mono_ns":mono_ns(), "tick":tick, "phase":"submit",
            "order_id": safe_int(wr.body.get("order_id")) if isinstance(wr.body,Mapping) else None,
            "action":action, "otype":params["type"], "price":price,
            "requested_qty":qty, "filled_qty":0,
            "status":"AMBIGUOUS" if wr.ambiguous else (str(wr.body.get("status","")) if isinstance(wr.body,Mapping) else ""),
            "latency_ms":wr.latency_ms, "payload_json":canonical(wr.body)
        }, mirror=True)

        if wr.ambiguous:
            raise RuntimeError(f"Ambiguous POST outcome: {wr.error}")
        if wr.response is None:
            raise RuntimeError("Order POST produced no response")
        if not wr.response.ok:
            self.state.unknown = False; self.state.save()
            return None
        if not isinstance(wr.body, Mapping) or wr.body.get("order_id") is None:
            raise RuntimeError("Successful order POST missing order_id")
        oid = int(wr.body["order_id"])
        filled = first_int(wr.body, "quantity_filled", default=0) or 0
        status = order_status(wr.body) or "OPEN"
        self.state.records[str(oid)] = {
            "action":action, "quantity":qty, "filled":0, "status":status,
            "price":price, "created":mono(), "seen":False,
        }
        self.state.unknown = False; self.state.save()
        self.submitted += 1
        if price is None:
            self.market_orders += 1
        else:
            self.limit_orders += 1
        return oid

    def cancel(self, oid: int) -> bool:
        if not self.live: return True
        key = str(oid)
        rec = self.state.records.get(key)
        if rec is None or rec.get("status") in TERMINAL_STATUSES: return True
        now = mono()
        if now - self.last_cancel.get(key,0) < self.cfg.cancel_retry_s: return False
        # Newly acknowledged-but-unpublished order: don't hammer DELETE into the visibility gap.
        if not rec.get("seen") and now - float(rec.get("created",now)) < self.cfg.visibility_grace_s:
            return False
        self.last_cancel[key] = now
        wr = self.api.write_once("DELETE", f"/orders/{oid}")
        self.journal.event("cancel_request", {"order_id":oid,"ambiguous":wr.ambiguous,
                                              "status":wr.response.status_code if wr.response else None})
        if wr.ambiguous:
            raise RuntimeError(f"Ambiguous DELETE outcome for order {oid}")
        self.cancelled += 1
        return bool(wr.response is not None and (wr.response.ok or wr.response.status_code == 404))

    def cancel_side(self, action: str) -> None:
        for oid, rec in list(self.state.records.items()):
            if rec.get("action") == action and rec.get("status") not in TERMINAL_STATUSES:
                self.cancel(int(oid))

    def cancel_all_known(self) -> None:
        for oid, rec in list(self.state.records.items()):
            if rec.get("status") not in TERMINAL_STATUSES:
                self.cancel(int(oid))


# =============================================================================
# QUOTE POLICY
# =============================================================================

def compute_target(ms: MarketState, position: int, avg_cost: Optional[float], opened: Sequence[Mapping[str, Any]],
                   om: OrderManager, cfg: StrategyConfig, runtime: RuntimeConfig) -> QuoteTarget:
    buycap, sellcap = om.capacity(position, opened)
    spread = ms.spread

    # Base competitive prices. In a tight market join the touch and keep queue.
    # When competitors leave >=3c, improve by one tick but remain strictly passive.
    if spread >= cfg.improve_if_spread:
        bid0 = min(ms.bid + TICK_SIZE, ms.ask - TICK_SIZE)
        ask0 = max(ms.ask - TICK_SIZE, ms.bid + TICK_SIZE)
    else:
        bid0, ask0 = ms.bid, ms.ask

    # In fast/noisy conditions stop penny-jumping and let others be first to adverse flow.
    if ms.volatility >= cfg.high_vol_per_tick:
        bid0, ask0 = ms.bid, ms.ask

    # Inventory center shift: long -> quotes down; short -> quotes up.
    skew_ticks = min(int(abs(position) / max(1,cfg.shares_per_skew_tick)),
                     int(round(cfg.max_inventory_skew / TICK_SIZE)))
    skew = (-1 if position > 0 else 1 if position < 0 else 0) * skew_ticks * TICK_SIZE
    buy_px = floor_tick(bid0 + skew)
    sell_px = ceil_tick(ask0 + skew)

    # Passive clamps relative to external book.
    buy_px = min(buy_px, floor_tick(ms.ask - TICK_SIZE))
    sell_px = max(sell_px, ceil_tick(ms.bid + TICK_SIZE))
    if sell_px <= buy_px:
        buy_px, sell_px = ms.bid, ms.ask

    # Size skew: adding side shrinks, reducing side grows.
    inv_frac = min(1.0, abs(position) / max(1,cfg.soft_limit))
    buy_qty = cfg.base_size
    sell_qty = cfg.base_size
    if position > 0:
        buy_qty = int(cfg.base_size * max(0.0, 1.0 - inv_frac))
        sell_qty = int(cfg.base_size * (1.0 + 0.35*inv_frac))
    elif position < 0:
        sell_qty = int(cfg.base_size * max(0.0, 1.0 - inv_frac))
        buy_qty = int(cfg.base_size * (1.0 + 0.35*inv_frac))
    buy_qty = min(runtime.max_order, buycap, max(0,buy_qty))
    sell_qty = min(runtime.max_order, sellcap, max(0,sell_qty))

    reason = "RANGE"
    if abs(position) >= cfg.soft_limit:
        if position > 0: buy_qty = 0; sell_qty = min(runtime.max_order, sellcap, max(cfg.base_size, abs(position)))
        else: sell_qty = 0; buy_qty = min(runtime.max_order, buycap, max(cfg.base_size, abs(position)))
        reason = "SOFT_LIMIT_REDUCE"

    # Trend defense. Do not keep manufacturing inventory against the move.
    if ms.trend_regime == "UP":
        reason = "TREND_UP"
        # Never add shorts in an uptrend. Sell only to reduce a long.
        if position <= 0:
            sell_qty = 0
        else:
            # Reducing quote is capped at current long inventory: in a trend
            # regime we refuse to let a "flattening" fill overshoot through zero
            # and manufacture a new short.
            sell_qty = min(runtime.max_order, sellcap, abs(position))
            sell_px = max(ms.bid + TICK_SIZE, min(sell_px, ms.ask))
        # Modest trend-aligned passive target, not an unrestricted directional bet.
        if position >= cfg.trend_target:
            buy_qty = 0
        else:
            buy_qty = min(buycap, runtime.max_order, max(0, min(cfg.base_size, cfg.trend_target-position)))
            buy_px = min(ms.bid, ms.ask-TICK_SIZE)
    elif ms.trend_regime == "DOWN":
        reason = "TREND_DOWN"
        if position >= 0:
            buy_qty = 0
        else:
            buy_qty = min(runtime.max_order, buycap, abs(position))
            buy_px = min(ms.ask-TICK_SIZE, max(buy_px, ms.bid))
        if position <= -cfg.trend_target:
            sell_qty = 0
        else:
            sell_qty = min(sellcap, runtime.max_order, max(0, min(cfg.base_size, cfg.trend_target+position)))
            sell_px = max(ms.ask, ms.bid+TICK_SIZE)

    # Late case: reducing side only. Work the touch passively before resorting to market.
    if ms.tick >= cfg.reduce_only_tick:
        reason = "END_REDUCE_ONLY"
        if position > 0:
            buy_qty = 0
            sell_qty = min(runtime.max_order, sellcap, abs(position))
            sell_px = ms.ask if ms.tick < cfg.passive_unwind_tick else max(ms.bid+TICK_SIZE, min(ms.ask, sell_px))
        elif position < 0:
            sell_qty = 0
            buy_qty = min(runtime.max_order, buycap, abs(position))
            buy_px = ms.bid if ms.tick < cfg.passive_unwind_tick else min(ms.ask-TICK_SIZE, max(ms.bid, buy_px))
        else:
            buy_qty = sell_qty = 0

    buy_qty = int(max(0,buy_qty)); sell_qty = int(max(0,sell_qty))
    return QuoteTarget(buy_px if buy_qty else None, buy_qty,
                       sell_px if sell_qty else None, sell_qty, reason)


def adverse_stop(position: int, avg_cost: Optional[float], ms: MarketState, cfg: StrategyConfig) -> Tuple[bool,str]:
    if position == 0: return False, "flat"
    # A confirmed trend against inventory is the exact failure mode observed in public graded runs.
    if position < 0 and ms.trend_regime == "UP" and ms.trend_strength >= 1.0:
        return True, "short_against_uptrend"
    if position > 0 and ms.trend_regime == "DOWN" and ms.trend_strength >= 1.0:
        return True, "long_against_downtrend"
    if avg_cost is None: return False, "no_cost"
    stop_dist = max(cfg.adverse_stop_floor, cfg.adverse_stop_vol_mult * ms.volatility)
    if position > 0 and ms.mid <= avg_cost - stop_dist:
        return True, f"long_stop_{stop_dist:.3f}"
    if position < 0 and ms.mid >= avg_cost + stop_dist:
        return True, f"short_stop_{stop_dist:.3f}"
    return False, "ok"


def current_by_side(opened: Sequence[Mapping[str,Any]]) -> Dict[str, Mapping[str,Any]]:
    out = {}
    for side in ("BUY","SELL"):
        rows = [o for o in opened if o.get("action") == side and order_remaining(o)>0]
        if rows:
            rows.sort(key=lambda o: float(o.get("price") or 0), reverse=(side=="BUY"))
            out[side] = rows[0]
    return out


def needs_replace(order: Optional[Mapping[str,Any]], target_price: Optional[float], target_qty: int,
                  reducing: bool, risk_off: bool, cfg: StrategyConfig,
                  records: Mapping[str,Mapping[str,Any]]) -> bool:
    if order is None: return target_qty > 0 and target_price is not None
    if target_qty <= 0 or target_price is None: return True
    oid = str(order.get("order_id"))
    rec = records.get(oid, {})
    age = mono() - float(rec.get("created", mono()))
    drift_ticks = abs(float(order.get("price")) - float(target_price)) / TICK_SIZE
    rem = order_remaining(order)

    # If this quote adds risk in a regime that now forbids it, cancel immediately.
    if risk_off: return True
    # Dangerously stale quote gets pulled even if young.
    if drift_ticks >= cfg.dangerous_drift_ticks: return True
    # Reducing quote gets extra queue patience.
    min_life = cfg.reducing_quote_life_s if reducing else cfg.min_quote_life_s
    if age < min_life: return False
    if drift_ticks >= cfg.reprice_ticks: return True
    if target_qty > 0 and abs(rem-target_qty) > cfg.size_reprice_fraction*target_qty: return True
    return False


# =============================================================================
# ENGINE
# =============================================================================

class Algo2Engine:
    def __init__(self, api: RITAPI, journal: Journal, cfg: StrategyConfig,
                 runtime: RuntimeConfig, live: bool, state_path: Path,
                 out_dir: Path) -> None:
        self.api, self.journal, self.cfg, self.runtime, self.live = api,journal,cfg,runtime,live
        self.out_dir = out_dir
        self.om = OrderManager(api,journal,cfg,runtime,live,state_path)
        self.signals = SignalEngine(cfg)
        self.started = False
        self.closing = False
        self.last_heartbeat = 0.0
        self.last_snapshot_log = 0.0
        self.last_config = 0.0
        self.last_trader = 0.0
        self.last_tick = -1
        self.start_nlv: Optional[float] = None
        self.end_nlv: Optional[float] = None
        self.start_fines: Optional[float] = None
        self.end_fines: Optional[float] = None
        self.max_abs_position = 0
        self.peak_nlv: Optional[float] = None
        self.drawdown_halt = False
        self.fine_halt = False
        self.regime_counts = defaultdict(int)
        self.next_submit_side = "BUY"
        self.inside_lead_side = "BUY"
        self.inside_lead_initialized = False
        self.last_position_for_lead = 0
        self.heat_index = 0
        self.trader_stats: Dict[str, Dict[str,Any]] = defaultdict(lambda:{"sizes":[],"dists":[],"ids":set(),"snaps":0,"last_ids":set(),"changes":0})
        self.heat_start_mono: Optional[float] = None
        self.occupancy_obs = 0
        self.buy_touch_obs = 0
        self.sell_touch_obs = 0
        self.buy_inside_obs = 0
        self.sell_inside_obs = 0

    def refresh_runtime(self) -> None:
        sec = self.api.security(); lim = self.api.limits()
        new = parse_runtime(sec, lim, self.cfg)
        if runtime_signature(new) != runtime_signature(self.runtime):
            self.journal.event("runtime_change", {
                "before": runtime_signature(self.runtime),
                "after": runtime_signature(new),
            })
            self.runtime = new
            self.om.runtime = new
            self.api.set_order_rate(new.order_rate)
            adapt_strategy_to_runtime(self.cfg, new)

    def observe_book_stats(self, tick: int, book: Mapping[str,Any], mid: float) -> None:
        ids_by = defaultdict(set)
        for side in ("bids","asks"):
            for o in book.get(side,[]) or []:
                if not isinstance(o,Mapping): continue
                p=safe_float(o.get("price")); q=order_remaining(o)
                if p is None or q<=0: continue
                tr=str(o.get("trader_id") or "")
                oid=safe_int(o.get("order_id")); self_flag=int((oid in self.om.my_ids() if oid is not None else False) or (self.om.my_trader and tr==self.om.my_trader))
                self.journal.put("book_orders", {"ts_utc":utc_now(),"mono_ns":mono_ns(),"tick":tick,"side":side,
                    "trader_id":tr,"order_id":oid,"price":p,"remaining":q,"distance_from_mid":abs(p-mid),"is_self":self_flag})
                if tr and not self_flag:
                    st=self.trader_stats[tr]; st["sizes"].append(q); st["dists"].append(abs(p-mid)); st["ids"].add(oid); ids_by[tr].add(oid)
        for tr,ids in ids_by.items():
            st=self.trader_stats[tr]; st["snaps"]+=1
            if st["last_ids"] and ids!=st["last_ids"]: st["changes"]+=1
            st["last_ids"]=set(ids)

    def market_state(self, tick:int, book:Mapping[str,Any], sec:Mapping[str,Any]) -> Optional[MarketState]:
        bids,asks=aggregate_external(book,self.om.my_trader,self.om.my_ids())
        if not bids or not asks: return None
        bid,ask=float(bids[0]["_price"]),float(asks[0]["_price"])
        if bid<=0 or ask<=bid: return None
        mid=(bid+ask)/2; mp=microprice(bids,asks) or mid
        self.signals.observe(tick,mid)
        vol,move,regime,strength=self.signals.values(tick)
        # Microprice is useful but intentionally only a small lean; no black-box forecast.
        fair=mid+clamp(0.50*(mp-mid),-0.01,0.01)
        return MarketState(tick,bid,ask,mid,ask-bid,mp,top_level_qty(bids),top_level_qty(asks),vol,move,regime,strength,fair)

    def volume_target(self, ms: MarketState, position: int, avg_cost: Optional[float],
                      opened: Sequence[Mapping[str,Any]]) -> QuoteTarget:
        """Throughput-first target with a one-sided inside lead on a 2c spread.

        At a 1c market we stack both touches.  At exactly 2c there is one empty
        price level: one side leads that level while the other remains at the
        external touch.  Inventory immediately gives inside priority to the
        reducing side.  When flat again, the lead flips so turnover ping-pongs
        rather than accumulating a persistent directional position.
        """
        target = compute_target(ms, position, avg_cost, opened, self.om, self.cfg, self.runtime)
        if self.cfg.mode != "volume" or not target.reason.startswith("RANGE"):
            self.last_position_for_lead = position
            return target

        prev = self.last_position_for_lead
        if position > 0:
            self.inside_lead_side = "SELL"
        elif position < 0:
            self.inside_lead_side = "BUY"
        elif prev > 0:
            self.inside_lead_side = "BUY"
        elif prev < 0:
            self.inside_lead_side = "SELL"
        elif not self.inside_lead_initialized:
            self.inside_lead_side = "SELL" if ms.microprice >= ms.mid else "BUY"
            self.inside_lead_initialized = True
        self.last_position_for_lead = position

        # Exactly one empty tick between touch prices: own the inside on one side.
        if 0.019 <= ms.spread < 0.029:
            inside = round_tick(ms.bid + TICK_SIZE)
            if self.inside_lead_side == "BUY":
                target.buy_price = inside if target.buy_qty > 0 else None
                target.sell_price = ms.ask if target.sell_qty > 0 else None
                target.reason = "RANGE_INSIDE_BUY"
            else:
                target.buy_price = ms.bid if target.buy_qty > 0 else None
                target.sell_price = inside if target.sell_qty > 0 else None
                target.reason = "RANGE_INSIDE_SELL"
        return target

    def log_snapshot(self, ms:MarketState, sec:Mapping[str,Any], book:Mapping[str,Any], target:QuoteTarget, trader:Mapping[str,Any]) -> None:
        now=mono()
        if now-self.last_snapshot_log < self.cfg.snapshot_log_s: return
        self.last_snapshot_log=now
        pos=first_int(sec,"position",default=0) or 0
        self.journal.put("snapshots", {"ts_utc":utc_now(),"mono_ns":mono_ns(),"tick":ms.tick,
            "position":pos,"vwap":first_number(sec,"vwap","average_cost"),"realized":first_number(sec,"realized","realized_pl","realized_pnl"),
            "unrealized":first_number(sec,"unrealized","unrealized_pl","unrealized_pnl"),"nlv":first_number(trader,"nlv"),"fines":first_number(trader,"fines","fine"),
            "bid":ms.bid,"ask":ms.ask,"mid":ms.mid,"spread":ms.spread,"microprice":ms.microprice,"bid_qty":ms.bid_qty,"ask_qty":ms.ask_qty,
            "volatility":ms.volatility,"trend_move":ms.trend_move,"trend_regime":ms.trend_regime,"trend_strength":ms.trend_strength,"fair":ms.fair,
            "target_buy":target.buy_price,"target_buy_qty":target.buy_qty,"target_sell":target.sell_price,"target_sell_qty":target.sell_qty,
            "raw_book_json":canonical(book),"raw_security_json":canonical(sec)})
        self.observe_book_stats(ms.tick,book,ms.mid)

    def heartbeat(self, ms:MarketState, position:int, target:QuoteTarget, trader:Mapping[str,Any]) -> None:
        now=mono()
        if now-self.last_heartbeat<self.cfg.heartbeat_s: return
        self.last_heartbeat=now
        nlv=first_number(trader,"nlv"); fines=first_number(trader,"fines","fine")
        print(f"[{ms.tick:3d}] {ms.bid:.2f}/{ms.ask:.2f} mid={ms.mid:.3f} trend={ms.trend_move:+.3f} {ms.trend_regime:5s} pos={position:+6d} "
              f"q=({target.buy_qty}@{target.buy_price},{target.sell_qty}@{target.sell_price}) NLV={nlv} fines={fines}")

    def risk_flatten_step(self, tick:int, position:int, reason:str) -> None:
        if not self.live: return
        self.om.cancel_all_known()
        try:
            p,opened=self.om.reconcile()
        except RuntimeError:
            return
        if opened: return
        if p==0: return
        action="SELL" if p>0 else "BUY"
        qty=min(abs(p),self.runtime.max_order)
        oid=self.om.submit(action,qty,None,tick)
        if oid is not None:
            self.journal.event("risk_flatten", {"reason":reason,"position":p,"action":action,"quantity":qty},tick)

    def _desired_total(self, side: str, position: int, target: QuoteTarget) -> int:
        """Desired aggregate resting quantity for one side.

        RANGE mode can stack several clips.  Risk/trend/endgame states instead
        cap aggregate reducing quantity to the exposure that is actually meant
        to be reduced, preventing a multi-order overshoot through flat.
        """
        per = target.buy_qty if side == "BUY" else target.sell_qty
        if per <= 0:
            return 0
        reason = target.reason
        if reason.startswith("RANGE"):
            cap = (self.runtime.operational_limit - position
                   if side == "BUY"
                   else self.runtime.operational_limit + position)
            return int(max(0, min(cap, per * max(1, self.cfg.quote_layers))))
        if reason in {"SOFT_LIMIT_REDUCE", "END_REDUCE_ONLY"}:
            if position > 0 and side == "SELL":
                return int(min(abs(position), self.runtime.operational_limit + position))
            if position < 0 and side == "BUY":
                return int(min(abs(position), self.runtime.operational_limit - position))
            return 0
        if reason == "TREND_UP":
            if side == "SELL":
                return int(max(0, position))  # only reduce an existing long
            return int(max(0, min(self.cfg.trend_target - position,
                                  self.runtime.operational_limit - position)))
        if reason == "TREND_DOWN":
            if side == "BUY":
                return int(max(0, -position))  # only reduce an existing short
            return int(max(0, min(self.cfg.trend_target + position,
                                  self.runtime.operational_limit + position)))
        return int(per)

    def _stack_order_needs_cancel(self, order: Mapping[str,Any], target_price: Optional[float],
                                  reducing: bool, risk_off: bool) -> bool:
        if risk_off or target_price is None:
            return True
        rec = self.om.state.records.get(str(order.get("order_id")), {})
        age = mono() - float(rec.get("created", mono()))
        px = safe_float(order.get("price"))
        if px is None:
            return True
        drift_ticks = abs(px - float(target_price)) / TICK_SIZE
        if drift_ticks >= self.cfg.dangerous_drift_ticks:
            return True
        min_life = self.cfg.reducing_quote_life_s if reducing else self.cfg.min_quote_life_s
        if age < min_life:
            return False
        return drift_ticks >= self.cfg.reprice_ticks

    def manage_quotes(self, tick:int, position:int, opened:Sequence[Mapping[str,Any]], target:QuoteTarget) -> None:
        """Maintain reserved multi-clip passive stacks without exceeding risk limits.

        Only one write is initiated per engine iteration; RITAPI additionally
        enforces the advertised server write rate.  Partially-filled quotes are
        kept at the correct price for queue priority while fresh clips replenish
        aggregate displayed quantity.
        """
        by_side = {
            side: [o for o in opened if o.get("action") == side and order_remaining(o) > 0]
            for side in ("BUY", "SELL")
        }
        desired = {
            "BUY": self._desired_total("BUY", position, target),
            "SELL": self._desired_total("SELL", position, target),
        }
        prices = {"BUY": target.buy_price, "SELL": target.sell_price}

        # First remove one forbidden/stale clip.  Risk-adding side is inspected
        # first when inventory is non-zero; otherwise alternate to avoid bias.
        if position > 0:
            cancel_order = ["BUY", "SELL"]
        elif position < 0:
            cancel_order = ["SELL", "BUY"]
        else:
            cancel_order = [self.next_submit_side, "SELL" if self.next_submit_side == "BUY" else "BUY"]

        for side in cancel_order:
            reducing = (position > 0 and side == "SELL") or (position < 0 and side == "BUY")
            risk_off = ms_regime_forbid(side, position, target.reason) or desired[side] <= 0
            stale = [
                o for o in by_side[side]
                if self._stack_order_needs_cancel(o, prices[side], reducing, risk_off)
            ]
            if stale:
                # Cancel the farthest quote first; for ties, oldest known record.
                def score(o: Mapping[str,Any]) -> Tuple[float,float]:
                    px = safe_float(o.get("price")) or 0.0
                    tgt = prices[side] if prices[side] is not None else px
                    drift = abs(px - float(tgt))
                    rec = self.om.state.records.get(str(o.get("order_id")), {})
                    age = mono() - float(rec.get("created", mono()))
                    return (drift, age)
                victim = max(stale, key=score)
                self.om.cancel(int(victim["order_id"]))
                return

        # Replenish aggregate quantity.  Reducing inventory gets priority;
        # otherwise alternate sides so a fresh heat builds both stacks together.
        if position > 0:
            sequence = ["SELL", "BUY"]
        elif position < 0:
            sequence = ["BUY", "SELL"]
        else:
            sequence = [self.next_submit_side, "SELL" if self.next_submit_side == "BUY" else "BUY"]

        for side in sequence:
            px = prices[side]
            if px is None or desired[side] <= 0:
                continue
            # Do not count wrong-price clips toward the desired touch stack.
            correct = [
                o for o in by_side[side]
                if safe_float(o.get("price")) is not None
                and abs(float(o.get("price")) - float(px)) < 1e-9
            ]
            resting = sum(order_remaining(o) for o in correct)
            deficit = desired[side] - resting
            if deficit < self.cfg.min_replenish_qty:
                continue

            # Never create an own crossed/locked pair when the 2c inside lead flips.
            # Clear the conflicting opposite quote first, then replenish next loop.
            opp = "SELL" if side == "BUY" else "BUY"
            conflicts = []
            for o in by_side[opp]:
                opx = safe_float(o.get("price"))
                if opx is None:
                    continue
                if (side == "BUY" and float(px) >= opx) or (side == "SELL" and float(px) <= opx):
                    conflicts.append(o)
            if conflicts:
                victim = min(conflicts, key=lambda o: int(o.get("order_id") or 0))
                self.om.cancel(int(victim["order_id"]))
                return

            qty = min(self.cfg.base_size, self.runtime.max_order, deficit)
            if qty <= 0:
                continue
            oid = self.om.submit(side, int(qty), px, tick)
            if oid is not None and position == 0:
                self.next_submit_side = "SELL" if side == "BUY" else "BUY"
            return

    def observe_own_occupancy(self, ms: MarketState, opened: Sequence[Mapping[str,Any]]) -> None:
        self.occupancy_obs += 1
        buys=[o for o in opened if o.get("action")=="BUY" and order_remaining(o)>0 and safe_float(o.get("price")) is not None]
        sells=[o for o in opened if o.get("action")=="SELL" and order_remaining(o)>0 and safe_float(o.get("price")) is not None]
        if any(float(o.get("price")) >= ms.bid-1e-9 for o in buys): self.buy_touch_obs += 1
        if any(float(o.get("price")) <= ms.ask+1e-9 for o in sells): self.sell_touch_obs += 1
        if any(float(o.get("price")) > ms.bid+1e-9 for o in buys): self.buy_inside_obs += 1
        if any(float(o.get("price")) < ms.ask-1e-9 for o in sells): self.sell_inside_obs += 1

    def write_trader_profiles(self) -> None:
        rows=[]
        for tr,st in sorted(self.trader_stats.items(), key=lambda kv:-kv[1]["snaps"]):
            rows.append([tr,st["snaps"],len(st["ids"]),
                         statistics.median(st["sizes"]) if st["sizes"] else None,
                         statistics.median(st["dists"]) if st["dists"] else None,
                         st["changes"]/st["snaps"] if st["snaps"] else None])
        header=["trader_id","snapshots","unique_order_ids","median_size","median_distance","requote_change_fraction"]
        paths=[self.out_dir/"trader_profiles.csv",
               self.out_dir/f"trader_profiles_heat_{self.heat_index:02d}.csv"]
        for path in paths:
            with path.open("w",newline="",encoding="utf-8") as f:
                w=csv.writer(f); w.writerow(header); w.writerows(rows)

    def run(self, heat_index: int = 1) -> Dict[str,Any]:
        self.heat_index = heat_index
        print(f"[WAIT] Heat {heat_index}: waiting for ALGO2 to become ACTIVE...")
        while not STOP_REQUESTED.is_set():
            case=self.api.case()
            if case.get("status")=="ACTIVE": break
            time.sleep(0.25)
        if STOP_REQUESTED.is_set(): return {}

        sec=self.api.security(); trader=self.api.trader()
        self.om.initialize(trader,sec,allow_round_reset=(heat_index>1))
        self.started=True
        self.heat_start_mono=mono()
        self.start_nlv=first_number(trader,"nlv"); self.start_fines=first_number(trader,"fines","fine",default=0.0)
        self.peak_nlv=self.start_nlv
        print(f"[START] HEAT {heat_index} ALGO2 ACTIVE tick={case.get('tick')} mode={self.cfg.mode.upper()} live={self.live}")
        self.journal.event("heat_start", {"heat_index":heat_index,"mode":self.cfg.mode,"live":self.live}, safe_int(case.get("tick")))
        print(f"[RUNTIME] order_max={self.runtime.max_order} position_limit={self.runtime.position_limit} operational={self.runtime.operational_limit} rate={self.runtime.order_rate}/s fee={self.runtime.fee} rebate={self.runtime.rebate}")

        while True:
            try:
                case=self.api.case(); status=str(case.get("status") or "")
                tick=int(case.get("tick",0))
                if status!="ACTIVE":
                    print(f"[STOP] case status={status} tick={tick}")
                    break
                if STOP_REQUESTED.is_set(): self.closing=True
                if mono()-self.last_config>=self.cfg.config_refresh_s:
                    self.refresh_runtime(); self.last_config=mono()

                # Reconcile first so inventory/capacity reflects real fills before new decisions.
                try:
                    position,opened=self.om.reconcile() if self.live else (first_int(self.api.security(),"position",default=0) or 0, self.api.open_orders())
                except RuntimeError as exc:
                    self.journal.event("reconcile_wait", {"error":str(exc)}, tick)
                    time.sleep(self.cfg.state_poll_s); continue

                sec=self.api.security(); position=first_int(sec,"position",default=position) or position
                self.max_abs_position=max(self.max_abs_position,abs(position))
                book=self.api.book(self.cfg.book_depth)
                ms=self.market_state(tick,book,sec)
                if ms is None:
                    time.sleep(self.cfg.loop_s); continue
                self.regime_counts[ms.trend_regime]+=1
                avg_cost=first_number(sec,"vwap","average_cost")
                trader=self.api.trader() if mono()-self.last_trader>=self.cfg.trader_refresh_s else {}
                if trader:
                    self.last_trader=mono()
                    nlv=first_number(trader,"nlv")
                    fines=first_number(trader,"fines","fine",default=0.0)
                    if nlv is not None:
                        self.peak_nlv=nlv if self.peak_nlv is None else max(self.peak_nlv,nlv)
                        if self.live and self.peak_nlv-nlv >= self.cfg.max_drawdown:
                            self.drawdown_halt=True; self.closing=True
                            self.journal.event("drawdown_halt", {"peak_nlv":self.peak_nlv,"nlv":nlv,"drawdown":self.peak_nlv-nlv},tick)
                            print(f"[HALT] drawdown {self.peak_nlv-nlv:,.2f} >= {self.cfg.max_drawdown:,.2f}; flattening and stopping")
                    if self.live and fines is not None and self.start_fines is not None and fines > self.start_fines + 1e-9:
                        self.fine_halt=True; self.closing=True
                        self.journal.event("fine_halt", {"start_fines":self.start_fines,"fines":fines},tick)
                        print(f"[HALT] fines increased {self.start_fines} -> {fines}; flattening and stopping")

                target=self.volume_target(ms,position,avg_cost,opened)
                self.observe_own_occupancy(ms, opened)
                self.log_snapshot(ms,sec,book,target,trader)
                self.heartbeat(ms,position,target,trader)

                # End-of-case hard flatten takes precedence over everything.
                if self.closing or tick>=self.cfg.market_flatten_tick:
                    self.risk_flatten_step(tick,position,"shutdown" if self.closing else "end_of_round")
                    if position==0:
                        try: self.om.cancel_all_known()
                        except Exception: pass
                        if self.closing: break
                    time.sleep(self.cfg.loop_s); continue

                stop,stop_reason=adverse_stop(position,avg_cost,ms,self.cfg)
                if abs(position)>=self.cfg.panic_limit:
                    stop=True; stop_reason="panic_limit"
                if stop:
                    self.risk_flatten_step(tick,position,stop_reason)
                    time.sleep(self.cfg.loop_s); continue

                if self.live:
                    self.manage_quotes(tick,position,opened,target)
                # shadow mode is deliberately read-only; targets/telemetry are still logged.

            except requests.RequestException as exc:
                self.journal.event("api_error", {"error":f"{type(exc).__name__}: {exc}"})
                time.sleep(0.3)
            except RuntimeError as exc:
                self.journal.event("runtime_error", {"error":str(exc)})
                if self.live and self.om.state.unknown:
                    print(f"[HALT] {exc}")
                    break
                time.sleep(0.25)
            except Exception as exc:
                self.journal.event("unexpected_error", {"error":f"{type(exc).__name__}: {exc}"})
                print(f"[ERROR] {type(exc).__name__}: {exc}")
                time.sleep(0.25)
            time.sleep(self.cfg.loop_s)

        # Best effort clean exit if still active and live.
        try:
            case=self.api.case()
            if self.live and case.get("status")=="ACTIVE":
                deadline=mono()+5.0
                while mono()<deadline:
                    try: p,_=self.om.reconcile()
                    except Exception: p=first_int(self.api.security(),"position",default=0) or 0
                    if p==0: break
                    self.risk_flatten_step(int(case.get("tick",0)),p,"final_cleanup")
                    time.sleep(0.15)
        except Exception: pass

        trader=self.api.trader()
        self.end_nlv=first_number(trader,"nlv"); self.end_fines=first_number(trader,"fines","fine",default=0.0)
        sec=self.api.security(); final_pos=first_int(sec,"position",default=0) or 0
        self.write_trader_profiles()
        duration_s=max(1e-9, mono()-(self.heat_start_mono or mono()))
        nlv_delta=(self.end_nlv-self.start_nlv) if self.start_nlv is not None and self.end_nlv is not None else None
        passive_shares=max(0, self.om.fill_shares-self.om.active_shares)
        maker_net_per_share=self.runtime.rebate-self.runtime.fee
        summary = {
            "version":VERSION,"heat_index":heat_index,"mode":self.cfg.mode,"live":self.live,
            "start_nlv":self.start_nlv,"end_nlv":self.end_nlv,
            "nlv_delta":nlv_delta,
            "start_fines":self.start_fines,"end_fines":self.end_fines,
            "fines_delta":(self.end_fines-self.start_fines) if self.start_fines is not None and self.end_fines is not None else None,
            "final_position":final_pos,"max_abs_position":self.max_abs_position,
            "peak_nlv":self.peak_nlv,"drawdown_halt":self.drawdown_halt,"fine_halt":self.fine_halt,
            "orders_submitted":self.om.submitted,"limit_orders":self.om.limit_orders,"market_orders":self.om.market_orders,
            "cancels":self.om.cancelled,"fill_shares_observed":self.om.fill_shares,
            "active_fill_shares_observed":self.om.active_shares,
            "passive_fill_shares_observed":passive_shares,
            "passive_fill_fraction_observed":(passive_shares/self.om.fill_shares if self.om.fill_shares else None),
            "wall_duration_s":duration_s,
            "fill_shares_per_minute":self.om.fill_shares/duration_s*60.0,
            "passive_shares_per_minute":passive_shares/duration_s*60.0,
            "orders_per_minute":self.om.submitted/duration_s*60.0,
            "maker_net_per_share":maker_net_per_share,
            "maker_incentive_estimate":passive_shares*maker_net_per_share,
            "nlv_per_fill_share":(nlv_delta/self.om.fill_shares if nlv_delta is not None and self.om.fill_shares else None),
            "buy_touch_occupancy":(self.buy_touch_obs/self.occupancy_obs if self.occupancy_obs else None),
            "sell_touch_occupancy":(self.sell_touch_obs/self.occupancy_obs if self.occupancy_obs else None),
            "buy_inside_occupancy":(self.buy_inside_obs/self.occupancy_obs if self.occupancy_obs else None),
            "sell_inside_occupancy":(self.sell_inside_obs/self.occupancy_obs if self.occupancy_obs else None),
            "regime_observations":dict(self.regime_counts),"runtime":asdict(self.runtime),
        }
        self.journal.event("heat_end", summary, safe_int(self.api.case().get("tick")))
        return summary


def ms_regime_forbid(side:str, position:int, reason:str) -> bool:
    if reason=="TREND_UP" and side=="SELL" and position<=0: return True
    if reason=="TREND_DOWN" and side=="BUY" and position>=0: return True
    if reason in {"SOFT_LIMIT_REDUCE","END_REDUCE_ONLY"}:
        if position>0 and side=="BUY": return True
        if position<0 and side=="SELL": return True
        if position==0: return True
    return False


# =============================================================================
# PREFLIGHT / SELF TEST
# =============================================================================

def self_test() -> None:
    cfg=StrategyConfig.preset("normal")
    # Trend hysteresis.
    s=SignalEngine(cfg)
    for t in range(1,16): s.observe(t,20.00+0.008*t)
    vol,move,reg,strength=s.values(15)
    assert reg=="UP" and move>=0.04
    # Book microprice.
    b=[{"_price":20.00,"_remaining":1000}]; a=[{"_price":20.02,"_remaining":3000}]
    mp=microprice(b,a); assert mp is not None and 20.00<mp<20.02
    # Capacity independently reserves each side.
    class Dummy: pass
    om=Dummy(); om.runtime=RuntimeConfig(5000,25000,22000,5,0.01,0.005,0,{},None)
    om.capacity=lambda p,o: OrderManager.capacity(om,p,o)
    opened=[{"action":"BUY","quantity":4000,"quantity_filled":0},{"action":"SELL","quantity":3000,"quantity_filled":0}]
    assert om.capacity(10000,opened)==(8000,29000)
    # Range target and trend direction protections.
    ms=MarketState(50,20.00,20.03,20.015,0.03,20.015,5000,5000,0,0,"RANGE",0,20.015)
    class OM2:
        runtime=om.runtime
        def capacity(self,p,o): return (12000,22000)
    qt=compute_target(ms,0,None,[],OM2(),cfg,om.runtime)
    assert qt.buy_price==20.01 and qt.sell_price==20.02 and qt.buy_qty>0 and qt.sell_qty>0
    ms.trend_regime="UP"; ms.trend_move=.08; ms.trend_strength=2
    qt=compute_target(ms,0,None,[],OM2(),cfg,om.runtime)
    assert qt.sell_qty==0 and qt.buy_qty>0
    qt_long=compute_target(ms,1500,None,[],OM2(),cfg,om.runtime)
    assert qt_long.sell_qty<=1500, qt_long
    ms.trend_regime="DOWN"; ms.trend_move=-.08
    qt=compute_target(ms,0,None,[],OM2(),cfg,om.runtime)
    assert qt.buy_qty==0 and qt.sell_qty>0
    qt_short=compute_target(ms,-1500,None,[],OM2(),cfg,om.runtime)
    assert qt_short.buy_qty<=1500, qt_short
    # Runtime adaptation remains inside live limits/order caps.
    cfg_small=StrategyConfig.preset("normal")
    rt_small=RuntimeConfig(2000,10000,7000,3,0.01,0.005,0,{},None)
    adapt_strategy_to_runtime(cfg_small,rt_small)
    assert cfg_small.base_size<=2000 and cfg_small.soft_limit<=5000 and cfg_small.panic_limit<=7000
    # Against-trend inventory stops.
    ms.trend_regime="UP"; ms.trend_strength=2
    assert adverse_stop(-2500,20.0,ms,cfg)[0]
    # V3 VOLUME stack budget: 24k per side at flat, inside the 25k legal envelope.
    turbo=StrategyConfig.preset("volume")
    rt=RuntimeConfig(5000,25000,24000,5,0.01,0.015,0,{},None)
    adapt_strategy_to_runtime(turbo,rt)
    class StackDummy:
        cfg=turbo; runtime=rt
    sd=StackDummy()
    flat_target=QuoteTarget(20.00,5000,20.01,5000,"RANGE")
    assert Algo2Engine._desired_total(sd,"BUY",0,flat_target)==24000
    assert Algo2Engine._desired_total(sd,"SELL",0,flat_target)==24000
    trend_target=QuoteTarget(20.00,5000,None,0,"TREND_UP")
    assert Algo2Engine._desired_total(sd,"BUY",-4000,trend_target)<=9000
    # V3 2c-spread lead: one side owns the inside while the opposite stays at touch.
    class LeadDummy:
        cfg=turbo; runtime=rt; om=OM2(); inside_lead_side="BUY"; inside_lead_initialized=True
        last_position_for_lead=0
    ld=LeadDummy()
    ms2=MarketState(60,20.00,20.02,20.01,0.02,20.01,5000,5000,0,0,"RANGE",0,20.01)
    lead=Algo2Engine.volume_target(ld,ms2,0,None,[])
    assert lead.buy_price==20.01 and lead.sell_price==20.02 and lead.reason=="RANGE_INSIDE_BUY", lead
    print("ALGO2 COMPETITION ENGINE SELF-TEST: PASS")
    print(f"Trend detector: {reg}, 10-tick move={move:+.4f}")
    print(f"Microprice test: {mp:.4f}")
    print("Range quote test: 20.01 / 20.02")
    print("Trend guard test: UP suppresses/never overshoots into short; DOWN suppresses/never overshoots into long")
    print("Runtime adaptation: order/position thresholds stay inside live server limits")
    print("V3 volume stack regression:  24k/side reserved at flat; 2c market gets one-sided inside lead")


def print_preflight(base:str, case:Mapping[str,Any], sec:Mapping[str,Any], limits:Any,
                    trader:Mapping[str,Any], runtime:RuntimeConfig, cfg:StrategyConfig,
                    opens:Sequence[Mapping[str,Any]], persistent_clean: bool) -> None:
    print("\n=== ALGO2 COMPETITION PREFLIGHT ===")
    print(f"Base URL:          {base}")
    print(f"Case:              {case.get('name')} status={case.get('status')} tick={case.get('tick')}")
    print(f"Security:          {sec.get('ticker')} position={sec.get('position')} last={sec.get('last')}")
    print(f"Position limit:    {runtime.position_limit:,}")
    print(f"Operating limit:   {runtime.operational_limit:,}")
    print(f"Max order:         {runtime.max_order:,}")
    print(f"Order rate hint:   {runtime.order_rate}/s")
    print(f"Fee field:         {runtime.fee:.4f}/share")
    print(f"Limit rebate:      {runtime.rebate:.4f}/share")
    print(f"Net passive edge:  {runtime.rebate-runtime.fee:+.4f}/share before price P&L")
    print(f"Execution delay:   {runtime.execution_delay_ms} ms")
    print(f"Open ALGO orders:  {len(opens)}")
    print(f"Persistent state:  {'CLEAN' if persistent_clean else 'UNRESOLVED'}")
    print(f"Trader NLV/Fines:  {trader.get('nlv')} / {trader.get('fines')}")
    print(f"Strategy mode:     {cfg.mode.upper()} base_size={cfg.base_size:,} layers={cfg.quote_layers} soft={cfg.soft_limit:,} panic={cfg.panic_limit:,}")
    print(f"Flat stack target: ~{min(runtime.operational_limit, cfg.base_size*cfg.quote_layers):,} shares per side")
    print(f"Drawdown kill:     {cfg.max_drawdown:,.0f}")
    print(f"Trend guard:       {cfg.trend_enter:.2f} move over {cfg.trend_lookback_ticks} ticks; off below {cfg.trend_exit:.2f}")
    print(f"Endgame:           reduce-only @{cfg.reduce_only_tick}, market flatten @{cfg.market_flatten_tick}")


# =============================================================================
# CLI
# =============================================================================

def parse_args() -> argparse.Namespace:
    p=argparse.ArgumentParser(description="RIT ALGO2 V3 volume/rebate competition engine")
    p.add_argument("--self-test",action="store_true")
    p.add_argument("--preflight",action="store_true")
    p.add_argument("--live",action="store_true")
    p.add_argument("--confirmed",action="store_true")
    p.add_argument("--mode",choices=["normal","volume","turbo","max"],default="volume")
    p.add_argument("--size", type=int, default=None, help="override base quote size")
    p.add_argument("--heats", type=int, default=0,
                   help="number of heats to run; 0 (default) = keep running until Ctrl+C")
    p.add_argument("--base-url",default=None)
    return p.parse_args()


def install_signals() -> None:
    def h(signum,frame):
        print("\n[SIGNAL] graceful shutdown requested; no new exposure, attempting flat cleanup")
        STOP_REQUESTED.set()
    signal.signal(signal.SIGINT,h)
    if hasattr(signal,"SIGTERM"): signal.signal(signal.SIGTERM,h)


def main() -> int:
    args=parse_args()
    if args.self_test:
        self_test(); return 0
    if args.live != args.confirmed:
        raise SystemExit("Live trading requires BOTH --live and --confirmed. Omit both for shadow/read-only mode.")
    key=os.getenv("RIT_API_KEY","").strip()
    if not key: raise SystemExit("Set RIT_API_KEY to the key shown in the RIT API panel")
    cfg=StrategyConfig.preset(args.mode)
    if args.size is not None:
        if not 100<=args.size<=5000: raise SystemExit("--size must be between 100 and 5000")
        cfg.base_size=args.size

    base=(args.base_url or os.getenv("RIT_BASE_URL") or discover_base_url(key)).rstrip("/")
    root=locate_algo2_root(); outroot=root/"outputs"; outroot.mkdir(parents=True,exist_ok=True)
    run_id=f"{run_stamp()}-{uuid.uuid4().hex[:8]}"; out=outroot/f"algo2_v3_volume_{run_id}"; out.mkdir(parents=True)
    journal=Journal(out); lock=InstanceLock(root/"algo2_write.lock"); lock.acquire(); install_signals()
    try:
        # Temporary default rate until live metadata is read.
        api=RITAPI(base,key,journal,cfg.default_order_rate)
        case=api.case(); secs=api.securities()
        tickers=[str(s.get("ticker")) for s in secs]
        if TICKER not in tickers:
            raise RuntimeError(f"This is not ALGO2: expected security {TICKER!r}, got {tickers}")
        sec=next(s for s in secs if s.get("ticker")==TICKER)
        limits=api.limits(); trader=api.trader(); opens=api.open_orders()
        runtime=parse_runtime(sec,limits,cfg)
        adapt_strategy_to_runtime(cfg, runtime)
        api.set_order_rate(runtime.order_rate)
        ps_check=PersistentState(root/"algo2_v3_state.json"); ps_check.load()
        persistent_clean=ps_check.clean()
        print_preflight(base,case,sec,limits,trader,runtime,cfg,opens,persistent_clean)
        if cfg.mode == "volume" and runtime.rebate <= runtime.fee:
            print("[WARNING] Live maker rebate is not greater than the fee; VOLUME economics are weaker than calibrated.")
        manifest={"version":VERSION,"run_id":run_id,"created_utc":utc_now(),"base_url":base,
                  "live":args.live,"strategy":asdict(cfg),"runtime":asdict(runtime),"case":case}
        (out/"manifest.json").write_text(json.dumps(manifest,indent=2,default=str),encoding="utf-8")
        journal.event("startup",manifest,safe_int(case.get("tick")))
        if args.preflight:
            (out/"summary.json").write_text(json.dumps({"preflight_only":True,"manifest":manifest},indent=2,default=str),encoding="utf-8")
            print(f"Output: {out}")
            return 0
        if args.live and not persistent_clean:
            # Fast path at a true simulator reset boundary.
            status = str(case.get("status") or "").upper()
            tick0 = int(case.get("tick", -1) or 0) == 0
            flat0 = (first_int(sec, "position", default=0) or 0) == 0
            no_opens = len(opens) == 0
            if status == "STOPPED" and tick0 and flat0 and no_opens:
                print("[RECOVERY] RIT is STOPPED/tick=0, flat, with no open ALGO orders; clearing stale prior-heat bookkeeping.")
                ps_check.expected_position = 0
                ps_check.records = {}
                ps_check.unknown = False
                ps_check.save()
                persistent_clean = True
            elif flat0 and no_opens:
                # Mid-heat restart: do NOT simply trust a single flat snapshot.
                # Resolve old IDs where possible and require a multi-second stable
                # flat/no-open window before clearing local bookkeeping.
                print("[RECOVERY] Mid-heat flat/no-open account with unresolved local state; certifying against live RIT history...")
                ok, why = certify_flat_midheat_recovery(api, ps_check, journal, cfg, case)
                if ok:
                    persistent_clean = True
                    print(f"[RECOVERY] PASS: {why}. Stale local bookkeeping cleared; live trading may start.")
                else:
                    raise RuntimeError(
                        "Live persistent state could not be certified safe mid-heat: " + why
                    )
            else:
                raise RuntimeError(
                    f"Live persistent state unresolved with current exposure/orders: "
                    f"position={first_int(sec,'position',default=0)}, open_orders={len(opens)}"
                )
        if args.live and (first_int(sec,"position",default=0) or 0)!=0:
            raise RuntimeError("Live mode requires flat starting position")
        if args.live and opens:
            raise RuntimeError("Live mode requires no existing ALGO orders")
        print("\n=== ALGO2 ENGINE STARTING ===")
        print(f"Mode: {'LIVE' if args.live else 'SHADOW'} / {cfg.mode.upper()}")
        print(f"Output: {out}")
        print(f"Heats: {'CONTINUOUS until Ctrl+C' if args.heats == 0 else args.heats}")
        heat_summaries=[]
        heat_index=0
        while not STOP_REQUESTED.is_set() and (args.heats == 0 or heat_index < args.heats):
            heat_index += 1
            engine=Algo2Engine(api,journal,cfg,runtime,args.live,root/"algo2_v3_state.json",out)
            summary=engine.run(heat_index=heat_index)
            if not summary:
                break
            heat_summaries.append(summary)
            combined={
                "version":VERSION,"mode":cfg.mode,"live":args.live,
                "heats_completed":len(heat_summaries),
                "cumulative_nlv_delta":sum((h.get("nlv_delta") or 0.0) for h in heat_summaries),
                "cumulative_fines_delta":sum((h.get("fines_delta") or 0.0) for h in heat_summaries),
                "heat_summaries":heat_summaries,
                "runtime":asdict(engine.runtime),
            }
            (out/"summary.json").write_text(json.dumps(combined,indent=2,default=str),encoding="utf-8")
            print(f"\n=== HEAT {heat_index} SUMMARY ===")
            print(f"NLV Δ:          {pretty_money(summary.get('nlv_delta'))}")
            print(f"Final position: {summary.get('final_position')}")
            print(f"Max |position|: {summary.get('max_abs_position')}")
            print(f"Orders:         {summary.get('orders_submitted')} ({summary.get('limit_orders')} limit / {summary.get('market_orders')} market)")
            pf = summary.get("passive_fill_fraction_observed")
            if pf is not None:
                print(f"Passive fills:  {100*pf:.1f}% of reconciled fill shares")
            print(f"Fill volume:    {summary.get('fill_shares_observed',0):,.0f} shares ({summary.get('fill_shares_per_minute',0):,.0f}/min)")
            print(f"Maker floor:    {pretty_money(summary.get('maker_incentive_estimate'))} from net rebate/fee")
            print(f"Touch occupancy B/S: {100*(summary.get('buy_touch_occupancy') or 0):.1f}% / {100*(summary.get('sell_touch_occupancy') or 0):.1f}%")
            print(f"Fines Δ:        {pretty_money(summary.get('fines_delta'))}")
            if STOP_REQUESTED.is_set() or (args.heats and heat_index >= args.heats):
                break
            print("[NEXT] Waiting automatically for the next heat; no manual restart required.")
            # Do not burn the STOPPED interval trying to force-clear old records.
            # The next engine waits on the ACTIVE transition; initialize(...,
            # allow_round_reset=True) clears prior-period bookkeeping only after
            # the new heat itself authoritatively reports flat/no open orders.
        if heat_summaries:
            combined={
                "version":VERSION,"mode":cfg.mode,"live":args.live,
                "heats_completed":len(heat_summaries),
                "cumulative_nlv_delta":sum((h.get("nlv_delta") or 0.0) for h in heat_summaries),
                "cumulative_fines_delta":sum((h.get("fines_delta") or 0.0) for h in heat_summaries),
                "heat_summaries":heat_summaries,
            }
            (out/"summary.json").write_text(json.dumps(combined,indent=2,default=str),encoding="utf-8")
            print("\n=== SESSION SUMMARY ===")
            print(f"Heats completed: {len(heat_summaries)}")
            print(f"Sum heat NLV Δ: {pretty_money(combined['cumulative_nlv_delta'])}")
            print(f"Sum fines Δ:    {pretty_money(combined['cumulative_fines_delta'])}")
        print(f"Output:         {out}")
        return 0
    finally:
        journal.close(); lock.release()


if __name__=="__main__":
    raise SystemExit(main())
