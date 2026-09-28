"""Behavior scenarios for the boundary watch's stream parser (tests/outside-watch-contract.md)."""

from pathlib import Path

import pytest

from harness.outside_watch import OutsideWatch


class _LineStream:
    """A process whose stdout is a fixed line stream, so the parser can be driven deterministically.

    The contract's subject is how the instrument's one stream is classified, and a real `inotifywait`
    would make the scenario neither deterministic nor fast.
    """

    def __init__(self, lines):
        self.stdout = iter(lines)


def watch_over(tmp_path, lines):
    """A watch whose parser has consumed `lines`, with `<tmp>/pkg/.runs` as the allowed path."""
    root = tmp_path / "pkg"
    allowed = root / ".runs"
    allowed.mkdir(parents=True)
    watch = OutsideWatch(root, allowed)
    watch._process = _LineStream(lines)
    watch._read()
    return watch


HANDSHAKE = [
    "Setting up watches.  Beware: since -r was given, this may take a while!",
    "Watches established.",
]


def test_instrument_announcement_is_serving_not_blindness(tmp_path):
    """Scenario 1: a subdirectory inside the allowed prefix must not blind the watch."""
    root = tmp_path / "pkg"
    watch = watch_over(
        tmp_path,
        HANDSHAKE
        + [
            f"Watching new directory {root}/probe/",
            f"CREATE,ISDIR {root}/probe",
            f"CREATE {root}/probe/scratch.lean",
            f"CREATE {root}/.runs/Paxos-r1.lean",
        ],
    )

    assert watch.blind is None, watch.blind
    assert watch.events == [f"CREATE,ISDIR {root}/probe", f"CREATE {root}/probe/scratch.lean"]


@pytest.mark.parametrize(
    "line",
    [
        "inotifywait: a diagnostic the contract does not name",
        "CREATE,OVERFLOW /somewhere/outside.lean",
    ],
)
def test_unreadable_lines_remain_blindness(tmp_path, line):
    """Scenario 2: a gap in the stream is never certified, whatever the announcement rule becomes."""
    root = tmp_path / "pkg"
    watch = watch_over(tmp_path, HANDSHAKE + [line, f"CREATE {root}/outside.lean"])

    assert watch.blind is not None
    assert line in watch.blind
