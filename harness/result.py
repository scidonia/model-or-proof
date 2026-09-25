"""Result rows and cost accounting for both routes (docs/protocol.md §6)."""

from __future__ import annotations

import json
from pathlib import Path

# Stated host rate for the compute component of Route A and Route B (docs/protocol.md §6).
HOST_RATE_USD_PER_H = 0.20

COST_BASIS = f"compute@{HOST_RATE_USD_PER_H:g} USD/h, tokens at list price"


def compute_cost_usd(wall_clock_s: float, rate_usd_per_h: float = HOST_RATE_USD_PER_H) -> float:
    """The compute component of a run's cost, in dollars."""
    return round(wall_clock_s / 3600.0 * rate_usd_per_h, 8)


def append_row(results_dir: Path | str, route: str, row: dict) -> Path:
    """Append one result row to results/<route>.jsonl and return the file's path."""
    results_dir = Path(results_dir)
    results_dir.mkdir(parents=True, exist_ok=True)
    path = results_dir / f"{route}.jsonl"
    with path.open("a") as handle:
        handle.write(json.dumps(row, sort_keys=True) + "\n")
    return path
