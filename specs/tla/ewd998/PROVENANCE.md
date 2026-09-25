# Provenance — EWD998 (ISoLA 2022 "TLA+ Trifecta")

Every `.tla`/`.cfg` file in this directory is imported **byte-for-byte** from a pinned upstream commit.
Nothing here was edited after import; attribution is by this file, never by modifying the sources.
The byte size, line count and **git blob SHA-1** recorded per file were measured against the pinned
commit and can be re-checked with `git hash-object <file>`.

Upstream sources:

| Source | Repository | Commit | Ref | License |
| --- | --- | --- | --- | --- |
| Spec, configs, proof | `https://github.com/tlaplus/Examples` | `3dfe0087a36ccfc6f8aae7de6621c68e06fab955` | `ISoLA2022` | MIT (`LICENSE.md`) |
| Standard-module dependencies | `https://github.com/tlaplus/CommunityModules` | `9aae8ea1318b3ded4629abdccec2c4754b528d70` | default branch | MIT (`LICENSE`) |

Files were fetched from the pinned raw URL form
`https://raw.githubusercontent.com/<repo>/<commit>/<path>` (never a branch name, so the import cannot
drift). Re-import with:

```bash
EX=3dfe0087a36ccfc6f8aae7de6621c68e06fab955
CM=9aae8ea1318b3ded4629abdccec2c4754b528d70
curl -o EWD998.tla "https://raw.githubusercontent.com/tlaplus/Examples/$EX/specifications/ewd998/EWD998.tla"
curl -o SequencesExt.tla "https://raw.githubusercontent.com/tlaplus/CommunityModules/$CM/modules/SequencesExt.tla"
```

## tlaplus/Examples @ `3dfe0087…` — `specifications/ewd998/` (MIT)

| File | Upstream path | Bytes | Lines | Blob SHA-1 |
| --- | --- | --- | --- | --- |
| `EWD998.tla` | `specifications/ewd998/EWD998.tla` | 8644 | 216 | `12523dc428948aaeee881e7be3869bb00e769afb` |
| `EWD998.cfg` | `specifications/ewd998/EWD998.cfg` | 210 | 21 | `c0caebdb1fef51a199cb076de779a6cdba5b2c38` |
| `EWD998Small.cfg` | `specifications/ewd998/EWD998Small.cfg` | 210 | 21 | `0d664ddb9553cecf4194701526ea37b4d3084be5` |
| `AsyncTerminationDetection.tla` | `specifications/ewd998/AsyncTerminationDetection.tla` | 4783 | 123 | `a28c7e84c7606ac4df30b0f9f1bc9f89129f27dc` |
| `EWD998_proof.tla` | `specifications/ewd998/EWD998_proof.tla` | 37228 | 863 | `603b36ad2e93de2854ef220a60e8cced7616b140` |
| `AsyncTerminationDetection_proof.tla` | `specifications/ewd998/AsyncTerminationDetection_proof.tla` | 5134 | 123 | `2d2f5031666349e4d31da610d703ab0d432b70eb` |

- **`EWD998.tla`** — Safra's termination detection on a ring; `EXTENDS Integers, FiniteSets,
  Functions, SequencesExt, Randomization`; `TD == INSTANCE AsyncTerminationDetection`. Carries the
  paper's TLC table in its trailing comment: `| 3 | 60 | 1.3m | 10.1m | 42 s |` and
  `| 4 | 105 | 219m | 2.3b | 50 m |`.
- **`EWD998Small.cfg`** — **the paper's instance**: `CONSTANTS N = 3`, `CONSTRAINTS StateConstraint`
  (K = C = 3, Q = 9; `EWD998.tla:117-121`), `INVARIANT TerminationDetection, Inv, TypeOK`,
  `CHECK_DEADLOCK FALSE`. This is the config `tasks/ewd998.json` calibrates against.
- **`EWD998.cfg`** — the branch's own config, `N = 4`. Imported so the two instances sit side by side
  and are told apart by filename; it is *not* the calibrated instance.
- **`EWD998_proof.tla`**, **`AsyncTerminationDetection_proof.tla`** — the human TLAPS proofs
  (`EXTENDS EWD998, FiniteSetTheorems, TLAPS`). Imported **as text with provenance** and **not
  machine-checked here**: `tlapm` is not in the dev shell and is not invoked anywhere in this
  repository. `results/human.jsonl` marks these records `machine_checked: false`.

Every file in this directory is imported; nothing here is repository-authored. TLC needs no
library-path plumbing to use them: SANY resolves the four vendored CommunityModules modules from the
root module's own directory, which the calibration logs show (all four are parsed from
`specs/tla/ewd998/`, while the jar's standard modules come from its own extraction directory). The
**publication-era** revision of the same system — the one that reproduces the paper's published TLC
figures, and therefore the one to read for the calibration — is committed beside this directory in
`specs/tla/ewd998-paper/` with its own `PROVENANCE.md`. The measured comparison between the two
revisions is in `docs/human-baseline.md` and on the `ewd998` record of `results/human.jsonl`.

## tlaplus/CommunityModules @ `9aae8ea…` — `modules/` (MIT), vendored

`tlaplus-1.7.4`'s `tla2tools.jar` has `Integers, FiniteSets, Naturals, Sequences, Bags, TLC,
Randomization` in `tla2sany/StandardModules/`, but **not** `SequencesExt`, `FiniteSetsExt`, `Folds`,
`Functions`. These four are CommunityModules, so they are vendored flat into this directory where
SANY's "root module's directory" rule resolves them — no `-DTLA-Library`, no `-D` plumbing (the
nixpkgs `tlc` wrapper does not forward `-D` to the JVM anyway). The transitive closure of `EWD998.tla`
is exactly these four.

| File | Upstream path | Bytes | Lines | Blob SHA-1 |
| --- | --- | --- | --- | --- |
| `SequencesExt.tla` | `modules/SequencesExt.tla` | 30449 | 546 | `2183f309d649f322d3403e21b5f75d7a9a6709e0` |
| `FiniteSetsExt.tla` | `modules/FiniteSetsExt.tla` | 10499 | 166 | `1b077f743c170c41d68d13693c9aea67b9eccd73` |
| `Folds.tla` | `modules/Folds.tla` | 2753 | 41 | `4b74814a3bcb7434946c9751e2a18e60f3179c6e` |
| `Functions.tla` | `modules/Functions.tla` | 11385 | 177 | `f80d28db1a125ce5223697fada2f87f4b38fa512` |

`EWD998.tla` defines `Sum(f, S) == FoldFunctionOnSet(+, 0, f, S)` and uses it for `B` and for `Inv`.
`FoldFunctionOnSet` is a pure TLA+ recursive definition in `Functions.tla` (via `MapThenFoldSet` in
`Folds.tla`) — no Java override is needed, only these `.tla` files on the parse path. The
CommunityModules `tlc2/overrides/*.java` classes are **not** vendored (they back operators EWD998 never
calls).

## License notices

### tlaplus/Examples — `LICENSE.md` @ `3dfe0087…` (MIT)

> All these TLA+ examples are licensed under the MIT License.
>
> Copyright (c) 2016: The TLA+ project and other contributors:
> https://github.com/tlaplus/Examples/graphs/contributors
>
> Permission is hereby granted, free of charge, to any person obtaining
> a copy of this software and associated documentation files (the
> "Software"), to deal in the Software without restriction, including
> without limitation the rights to use, copy, modify, merge, publish,
> distribute, sublicense, and/or sell copies of the Software, and to
> permit persons to whom the Software is furnished to do so, subject to
> the following conditions:
>
> The above copyright notice and this permission notice shall be
> included in all copies or substantial portions of the Software.
>
> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
> EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
> MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
> NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
> LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
> OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
> WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

### tlaplus/CommunityModules — `LICENSE` @ `9aae8ea…` (MIT)

> MIT License
>
> Copyright (c) 2019 TLA+
>
> Permission is hereby granted, free of charge, to any person obtaining a copy
> of this software and associated documentation files (the "Software"), to deal
> in the Software without restriction, including without limitation the rights
> to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
> copies of the Software, and to permit persons to whom the Software is
> furnished to do so, subject to the following conditions:
>
> The above copyright notice and this permission notice shall be included in all
> copies or substantial portions of the Software.
>
> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
> IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
> FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
> AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
> LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
> OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
> SOFTWARE.

No per-file license headers exist upstream; this file is the attribution.

## The published human baseline

The experiments these artifacts come from are recorded as cited data — person-days, proof lines, TLC
state counts and the published-vs-artifact line-count disagreement — in `results/human.jsonl` and
`docs/human-baseline.md`. They are **published evidence carried as data** (`kind:
"human_prior_art"`, `machine_checked: false`), never a measured row of this experiment.
