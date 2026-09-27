"""Result rows and cost accounting for both routes (docs/protocol.md §6)."""

from __future__ import annotations

import json
import os
from pathlib import Path

# Stated host rate for the compute component of Route A and Route B (docs/protocol.md §6).
HOST_RATE_USD_PER_H = 0.20

COST_BASIS = f"compute@{HOST_RATE_USD_PER_H:g} USD/h, tokens at list price"


def compute_cost_usd(wall_clock_s: float, rate_usd_per_h: float = HOST_RATE_USD_PER_H) -> float:
    """The compute component of a run's cost, in dollars."""
    return round(wall_clock_s / 3600.0 * rate_usd_per_h, 8)


def compute_basis(wall_clock_s: float) -> str:
    """The compute component of a run's cost basis (protocol §6): the rate, what it was applied to,
    and the dollars it produced — the evidence behind the row's ``compute_usd``.
    """
    return (
        f"compute {wall_clock_s:.3f}s @ {HOST_RATE_USD_PER_H:g} USD/h "
        f"= ${compute_cost_usd(wall_clock_s):.8f}"
    )


def append_row(results_dir: Path | str, route: str, row: dict, *, load_before=None) -> Path:
    """Append one result row to results/<route>.jsonl and return the file's path.

    The row carries the host load pair (the planner's ruling). D10 requires measurement rows on an
    unloaded host and nothing enforced or evidenced it: two overlapping runs inflate both cells and the
    inflation presents as ordinary spread, which is a wrong row no reader can detect. The pair makes a
    load-affected row *detectable* — evidence, not enforcement, so D10 stays the rule and the row says
    what a reader needs to judge it.

    ``before`` comes from the caller, which knows when the run began; ``after`` is sampled here, at the
    one point every route passes through. ``None`` in either slot means *not recorded* — a row written
    before the field existed — and never "no load".
    """
    row.setdefault(
        "load",
        {"before": load_before, "after": [round(value, 2) for value in os.getloadavg()]},
    )
    results_dir = Path(results_dir)
    results_dir.mkdir(parents=True, exist_ok=True)
    path = results_dir / f"{route}.jsonl"
    with path.open("a") as handle:
        handle.write(json.dumps(row, sort_keys=True) + "\n")
    return path
