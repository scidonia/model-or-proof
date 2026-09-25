# Provenance: the `repl` binary (Route B's prover, plan D2)

Route B speaks the `lean-repl` JSON protocol (plan D2), which is served by the `repl` executable from
[`leanprover-community/repl`](https://github.com/leanprover-community/repl). That executable is in
neither nixpkgs nor `elan`, so it is built here once, pinned, and recorded. This file is the record.

## Pin

| | |
| --- | --- |
| Repository | `https://github.com/leanprover-community/repl` |
| Commit | `6eb53f487a3c8603c88afe625fad56e0ac7f0d4f` |
| Commit subject | `chore: bump toolchain to v4.35.0-rc3 (#171)` |
| Toolchain | `leanprover/lean4:v4.35.0-rc3` (the commit's own `lean-toolchain`) |
| Upstream dependencies | none — the commit's `lake-manifest.json` has `"packages": []` |
| Upstream license | Apache-2.0 (`LICENSE`, kept verbatim at `tools/repl/LICENSE`) |
| Built binary | `tools/repl/.lake/build/bin/repl` (a gitignored build artifact: the repository root
`.gitignore` ignores `.lake/`) |
| Provisioned | 2026-09-25, on this host, via `nix develop -c` |

### Why this commit

The pin is not chosen by date or by proximity — it is **the commit whose `lean-toolchain` is
byte-identical to this project's**, `proofs/lean/token-ring/lean-toolchain`:

```
$ cat lean-toolchain          # in the repl checkout
leanprover/lean4:v4.35.0-rc3
$ cat proofs/lean/token-ring/lean-toolchain
leanprover/lean4:v4.35.0-rc3
```

It is the newest commit on `main` at provisioning time, and it is itself the *toolchain-bump* commit
for `v4.35.0-rc3` (`#171`), i.e. the upstream act of adopting our exact pin. That matters because the
REPL elaborates the artifact the loop is closing and reports its goal states: a repl built on a
different Lean would either refuse the model's oleans (`.olean` format/hash mismatch) or, worse,
elaborate against a different frontend and hand the model goal states that do not correspond to the
theorem being proved. Matching the toolchain is what makes the reported goals the model's actual
obligations. `leanprover/lean4:v4.35.0-rc3` is in turn Mathlib's release pin, which
`proofs/lean/token-ring/lakefile.toml` requires at `rev = "v4.35.0-rc3"`.

## Vendored sources

`tools/repl/` holds the upstream tree at that commit, extracted with `git archive HEAD` (no `.git`,
and the upstream `.github/`, `.vscode/`, and `.gitignore` dropped as repository metadata that has no
part in the build). Every file here other than this one is upstream's, verbatim. The versions of the
sources the binary was built from are pinned by these digests (sha256):

```
b843c1ebb1192522f3a64aca4b32168ddbd365b30a1914538a53ba010aa5d954  REPL.lean
042fe4709f4ba3bdd2a6b218ab66cbb23ec6e456cd05621979cea18c2012050d  REPL/Frontend.lean
f4f37d31381cff6ac626c414187f610fee59a50e8a4f778f167e3c9cf432d6d6  REPL/JSON.lean
8ebd5796e09ec1b4434640a211450bd4bd6d60c8670614c34b615c109ac3221e  REPL/Lean/ContextInfo.lean
da91570c1672569ccd3fff49b3b44db858f1ca0a58b9e5556ede56760d0493db  REPL/Lean/Environment.lean
e07de90958f3e858009391bf1751ee0ca4290782079030b5667355b831fae6b4  REPL/Lean/InfoTree.lean
b22dceafb6a1fa516cd5f995d934f3bf63bcb90d375855e413601760bc9d445f  REPL/Lean/InfoTree/ToJson.lean
b5127e93848f95231ff1ea1541166136f4c95a7303463c610b4fe5005240d339  REPL/Lean/Replay.lean
76bb41cfe02340968d85575741ebfc487f77baa5064ad71d5540325552068c8f  REPL/Main.lean
fbfdb8d7cb6cc6f7569368aaa7a6deb26e52cad786a304f2a34e20c0b28eab40  REPL/Snapshots.lean
4ef291a8c1b763e1ee5750d46dcd6bc6f9be5a89c6a9f7b577814ad61193b161  REPL/Util/Path.lean
7d4ba5908d5ee3a17aa9d6bb7a6063529b7c6c179a5aa90743ba06e7d4eef955  REPL/Util/Pickle.lean
a6128cbc7a0546d6b6fb30551be46ebddcd85a358114e43566ee12377970295c  lakefile.toml
df64a2adec5f117751de744108958c5159460ab17369dafabf92e2742650e946  lake-manifest.json
bc84812c94489d1e3e191baa1dc10d5eb684382d7fe9d2a5ab085e72c1c67e47  lean-toolchain
b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1  LICENSE
33711c7ba3bf51820978212de61d4b8d8859e8a2e1c41ffc7f45708b56383896  README.md
```

`README.md` is kept because it is the protocol's documentation — the README of the pinned commit is
the specification of the JSON the driver speaks. *Not* vendored: `Test.lean`, `test/`, and `test.sh`,
the upstream test suite (and `.github/`, `.vscode/`, `.gitignore`, repository metadata that has no part
in the build). They are upstream files of the pinned commit and are reproduced by the recipe below,
but they are not needed to build `repl`, they are never run here, and `test/Mathlib/` is a whole
nested lake package that has no business inside this repository. Consequence, stated so it is not a
surprise: the vendored `lakefile.toml` still names a `test` executable and a `testDriver`, so
`lake test` is unavailable in `tools/repl`; only the `repl` target (the package's `defaultTargets`) is
built and used.

## The pin is compatible with this project's oleans

The pin's whole point is that the REPL elaborates the artifact at the same Lean as the model. Observed
2026-09-25, from `proofs/lean/token-ring` (so `lake env` supplies the package's `LEAN_PATH`, Mathlib
included), the binary importing Mathlib and elaborating a command that uses Mathlib's `Finset`:

```
$ nix develop -c bash -c 'cd proofs/lean/token-ring && lake env ../../../tools/repl/.lake/build/bin/repl < /tmp/repl-fintype.in'
{"env": 0}                                     # import Mathlib
{"env": 1}                                     # inductive P … deriving DecidableEq, Fintype → error (below)
{"env": 2}                                     # the explicit Fintype instance → accepted
```

The middle response carries a genuine error, which is worth recording because it is a property of the
toolchain rather than of the driver: at this pin `deriving Fintype` on an inductive emits a `Finset`
construction that does not type-check against Mathlib's `Finset`
(`Tactic 'rewrite' failed … { val := ↑P.enumList, nodup := P.enumList_nodup }`). The model therefore
spells `Phase`'s `Fintype` instance out by hand, and a driver that generates `deriving Fintype` should
not. The Mathlib checkout here is exactly the one `lake-manifest.json` pins
(`c55e6e786f49471c72fbddbec5415808896aec1e`, clean tree, its own `lean-toolchain` equal to ours), so
this is not a stale-olean artefact.

## Build recipe

From a clean checkout, with the toolchain available (the dev shell provides `elan`, `git`, `curl`),
run from the repository root:

```sh
# 1. the pinned sources into tools/repl (the only file added afterwards is PROVENANCE.md)
nix develop -c git clone https://github.com/leanprover-community/repl.git /tmp/repl-src
nix develop -c git -C /tmp/repl-src checkout 6eb53f487a3c8603c88afe625fad56e0ac7f0d4f
nix develop -c bash -c 'git -C /tmp/repl-src archive HEAD | tar -x -C tools/repl'
# drop the metadata and the upstream test suite (see "Vendored sources")
rm -rf tools/repl/.github tools/repl/.vscode tools/repl/.gitignore tools/repl/Test.lean \
       tools/repl/test tools/repl/test.sh
# the digests above are the check that this reproduces the sources the binary was built from:
# paste that block into a file and run `sha256sum -c` on it

# 2. build against that same toolchain — `elan` reads tools/repl/lean-toolchain (v4.35.0-rc3)
nix develop -c bash -c 'cd tools/repl && lake build'
```

Observed build (2026-09-25), no Mathlib and no `lake exe cache get` are involved — the upstream
manifest has no dependencies, so the build is bare Lean core:

```
✔ [22/24] Built REPL.Main (1.4s)
✔ [23/24] Built REPL.Main:c.o (4.5s)
✔ [24/24] Built repl:exe (7.3s)
Build completed successfully (24 jobs).
```

## Observed run

The binary lands at `tools/repl/.lake/build/bin/repl` — the path `harness.route_b`'s `DEFAULT_REPL_BIN`
names and `--repl-bin` defaults to. Protocol check: a goal with a `sorry` is sent in command mode
(which returns the goal and its `proofState` label), then `rfl` is applied to that proof state in
tactic mode.

Exact stdin bytes:

```
7b22 636d 6422 3a20 2265 7861 6d70 6c65 203a 2031 202b 2031 203d 2032 203a 3d20
6279 2073 6f72 7279 227d 0a0a 7b22 7461 6374 6963 223a 2022 7266 6c22 2c20 2270
726f 6f66 5374 6174 6522 3a20 307d 0a0a
```

i.e.

```
{"cmd": "example : 1 + 1 = 2 := by sorry"}

{"tactic": "rfl", "proofState": 0}

```

Exact stdout bytes (exit status 0; the ASCII art is the repl's own line-wrapped JSON):

```
{"sorries":
 [{"proofState": 0,
   "pos": {"line": 1, "column": 26},
   "goal": "⊢ 1 + 1 = 2",
   "endPos": {"line": 1, "column": 31}}],
 "messages":
 [{"severity": "warning",
   "pos": {"line": 1, "column": 0},
   "endPos": {"line": 1, "column": 7},
   "data": "declaration uses `sorry`"}],
 "env": 0}

{"proofStatus": "Completed", "proofState": 1, "goals": []}
```

The first response is the command-mode reply: it names the one `sorry`, the goal it left as
`"⊢ 1 + 1 = 2"`, and the `proofState` label `0` for that goal. The second is the tactic-mode reply to
`rfl`: `"proofStatus": "Completed"` with `"goals": []` — the empty-goals response
`harness.lean_repl.parse_goals` reads as closure (plan step 4, `tests/lean-driver-contract.md` S2).

Invocation used (from the repository root):

```sh
nix develop -c bash -c 'tools/repl/.lake/build/bin/repl < /tmp/repl-in.txt'
```
