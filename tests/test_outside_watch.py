"""Behavior scenarios for the boundary watch's read layer (tests/outside-watch-contract.md)."""

import io

import pytest

from harness.outside_watch import OutsideWatch


def text_stream(text):
    """A process whose stdout is a text stream with `newline=""`, as the read layer requires."""
    return type("_Process", (), {"stdout": io.StringIO(text)})()  # StringIO does not translate newlines


def byte_stream(payload: bytes):
    """A process whose stdout is a byte pipe decoded strictly, so the decode layer is exercised.

    A `StringIO` cannot reproduce a decode failure: it hands over already-decoded text. The wrapper here
    decodes exactly as the current code does — strictly — so a name that is not valid UTF-8 fails here
    the way it fails in the harness.
    """
    wrapper = io.TextIOWrapper(io.BytesIO(payload), encoding="utf-8", newline="")
    return type("_Process", (), {"stdout": wrapper})()


def watch_over(tmp_path, process):
    """A watch whose read layer has consumed `process`'s stream, allowed path `<tmp>/pkg/.runs`."""
    root = tmp_path / "pkg"
    (root / ".runs").mkdir(parents=True)
    watch = OutsideWatch(root, root / ".runs")
    watch._process = process
    watch._read()
    return watch


def test_an_undecodable_filename_is_a_path_not_a_dead_watcher(tmp_path):
    """Scenario 1: an invalid UTF-8 byte in a name must not silently kill the reader."""
    root = tmp_path / "pkg"
    payload = b"%s/,CREATE,outside\xff.lean\n%s/,CREATE,after.lean\n" % (str(root).encode(), str(root).encode())

    watch = watch_over(tmp_path, byte_stream(payload))

    assert watch.blind is None, watch.blind
    assert watch.events == [
        "CREATE " + str(root) + "/outside\udcff.lean",
        "CREATE " + str(root) + "/after.lean",
    ]


def test_a_lone_carriage_return_degrades_to_blindness(tmp_path):
    """Scenario 2: a CR is not quoted, so its record splits — blindness, never certification."""
    root = tmp_path / "pkg"
    watch = watch_over(tmp_path, text_stream(f"{root}/,CREATE,.runs\rxyz\n"))

    assert watch.blind is not None
    assert "xyz" in watch.blind


def test_the_quoted_forms_do_not_split_a_record(tmp_path):
    """Scenario 3: newline, comma, doubled quote and CRLF inside a name each stay one record."""
    root = tmp_path / "pkg"
    watch = watch_over(
        tmp_path,
        text_stream(
            f'{root}/,CREATE,"nl\nin-name"\n'
            f'{root}/,CREATE,"comma,in-name"\n'
            f'{root}/,CREATE,"quote""in-name"\n'
            f'{root}/,CREATE,"crlf\r\nin-name"\n'
        ),
    )

    assert watch.blind is None, watch.blind
    assert watch.events == [
        f"CREATE {root}/nl\nin-name",
        f"CREATE {root}/comma,in-name",
        f'CREATE {root}/quote"in-name',
        f"CREATE {root}/crlf\r\nin-name",
    ]


@pytest.mark.parametrize(
    "line",
    [
        "a diagnostic the contract does not name",
        "{root}/,NOT_AN_EVENT,outside.lean",
    ],
)
def test_a_record_that_is_not_a_recognised_event_is_blindness(tmp_path, line):
    """Scenario 4: three fields is not evidence of an event, and an unknown record is blind."""
    root = tmp_path / "pkg"
    rendered = line.format(root=root)
    watch = watch_over(tmp_path, text_stream(rendered + f"\n{root}/,CREATE,outside.lean\n"))

    assert watch.blind is not None
    assert rendered in watch.blind
