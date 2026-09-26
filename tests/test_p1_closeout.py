"""Behavior scenarios for the P1 close-out manifests and Bakery configs (tests/p1-closeout-contract.md)."""

import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]

from harness.tlc_run import read_cfg  # noqa: E402

TOKEN_RING = REPO / "tasks" / "token-ring.json"
BAKERY = REPO / "tasks" / "bakery.json"


def load(path):
    return json.loads(path.read_text())


def test_token_ring_n0_is_recorded_and_runnable():
    """Scenario 1: token-ring n0 == 23, a matching N=23 instance exists, and N=3 remains."""
    manifest = load(TOKEN_RING)
    assert manifest["n0"] == 23, manifest["n0"]

    instances = {i["param_N"]: i for i in manifest["instances"]}
    assert 3 in instances, instances  # the fast instance the runner scenarios select
    assert 23 in instances, instances

    cfg = read_cfg(REPO / instances[23]["config"])
    assert cfg == {"param_N": 23, "property": "Mutex"}, cfg


def test_bakery_manifest_is_complete_and_calibrated():
    """Scenario 2: the bakery manifest is complete and its n0 matches a shipped instance."""
    manifest = load(BAKERY)
    assert manifest["name"] == "bakery", manifest
    assert manifest["spec"] == "specs/tla/bakery/Bakery.tla", manifest
    assert manifest["property"]["name"] == "MutualExclusion", manifest["property"]
    assert manifest["property"]["kind"] == "safety", manifest["property"]

    mutant = manifest["mutant"]
    assert mutant["spec"].endswith("BakeryMutant.tla"), mutant
    assert mutant["config"].endswith("BakeryMutant.cfg"), mutant

    n0 = manifest["n0"]
    assert isinstance(n0, int) and n0 >= 2, n0
    assert any(i["param_N"] == n0 for i in manifest["instances"]), (n0, manifest["instances"])


def test_bakery_configs_parse():
    """Scenario 3: the bakery configs parse to their N and property MutualExclusion."""
    manifest = load(BAKERY)
    for inst in manifest["instances"]:
        cfg = read_cfg(REPO / inst["config"])
        assert cfg["param_N"] == inst["param_N"], (inst, cfg)
        assert cfg["property"] == "MutualExclusion", (inst, cfg)

    mutant = read_cfg(REPO / manifest["mutant"]["config"])
    assert mutant["property"] == "MutualExclusion", mutant
