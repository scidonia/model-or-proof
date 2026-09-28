"""Behavior scenarios for the boundary watch's stream parser (tests/outside-watch-contract.md)."""

import io

import pytest

from harness.outside_watch import OutsideWatch


class _Stream:
    """A process whose stdout is a fixed text stream.

    A stream rather than a list of lines, because one CSV record may legitimately span several physical
    lines when a path contains a newline — which is the case this contract is about.
    """

    def __init__(self, text):
        self.stdout = io.StringIO(text)


def watch_over(tmp_path, text):
    """A watch whose parser has consumed `text`, with `<tmp>/pkg/.runs` as the allowed path."""
    root = tmp_path / "pkg"
    allowed = root / ".runs"
    allowed.mkdir(parents=True)
    watch = OutsideWatch(root, allowed)
    watch._process = _Stream(text)
    watch._read()
    return watch


def test_a_newline_in_a_path_does_not_split_a_record(tmp_path):
    """Scenario 1: the adversarial case — a filename chosen to contain a newline."""
    root = tmp_path / "pkg"
    watch = watch_over(
        tmp_path,
        f'{root}/,CREATE,".runs\newline-not-a-separator"\n'
        f"{root}/,CREATE,outside.lean\n",
    )

    assert watch.blind is None, watch.blind
    assert watch.events == [
        f"CREATE {root}/.runs\newline-not-a-separator",
        f"CREATE {root}/outside.lean",
    ]


def test_a_bare_fragment_is_not_a_record(tmp_path):
    """Scenario 2: the un-delimited shape must degrade into blindness, never into a silent pass."""
    root = tmp_path / "pkg"
    watch = watch_over(
        tmp_path,
        f"CREATE,ISDIR {root}/.runs\n"
        "Watching new directory xyz\n"
        f"CREATE {root}/outside.lean\n",
    )

    assert watch.blind is not None
    assert "Watching new directory xyz" in watch.blind


@pytest.mark.parametrize(
    "line",
    [
        "inotifywait: a diagnostic the contract does not name",
        "{root}/,OVERFLOW,",
    ],
)
def test_unreadable_records_remain_blindness(tmp_path, line):
    """Scenario 3: a gap in the stream is never certified, whatever the grammar becomes."""
    root = tmp_path / "pkg"
    rendered = line.format(root=root)
    watch = watch_over(tmp_path, rendered + f"\nCREATE {root}/outside.lean\n")

    assert watch.blind is not None
    assert rendered in watch.blind
