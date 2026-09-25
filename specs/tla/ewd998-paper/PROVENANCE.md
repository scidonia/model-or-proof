# Provenance — EWD998, publication-era (pre-widening) revision

**This is not the pinned branch head.** It is the *publication-era* revision of EWD998: the last
upstream revision before commit `dafe1e5c8a74` (2023-07-28) widened `Init`, which is why the figures the
ISoLA 2022 paper and the spec's own embedded table report (1.3 M distinct states, diameter 60) are
reproducible here and not at the pin. `specs/tla/ewd998/` holds the pinned branch head
(`3dfe0087a36ccfc6f8aae7de6621c68e06fab955`); this directory exists so the calibration can reproduce a
published number and so the drift is *measured* rather than asserted.

The imported files here are byte-for-byte from:

| Source | Repository | Commit | License |
| --- | --- | --- | --- |
| `EWD998.tla`, `AsyncTerminationDetection.tla` | `https://github.com/tlaplus/Examples` | `75f2a7a7369da8b8221232cb936c62d8c0b131f7` (2023-01-25, "No need to include pending in terminationDetection") | MIT (`LICENSE.md`) |
| `SequencesExt.tla`, `FiniteSetsExt.tla`, `Folds.tla`, `Functions.tla` | `https://github.com/tlaplus/CommunityModules` | `9aae8ea1318b3ded4629abdccec2c4754b528d70` | MIT (`LICENSE`) |
| `EWD998Small.cfg` | `https://github.com/tlaplus/Examples` | `d0ca8f0e0678ed1c72ec2ce5c4723059a15a298b` (2024-01-14, "Use CHECK_DEADLOCK config file parameter") | MIT (`LICENSE.md`) |

| File | Upstream path | Bytes | Lines | Blob SHA-1 |
| --- | --- | --- | --- | --- |
| `EWD998.tla` | `specifications/ewd998/EWD998.tla` @ `75f2a7a7…` | 8541 | 215 | `e9561192f1271b6bbcb527b4ea597cc70484421d` |
| `AsyncTerminationDetection.tla` | `specifications/ewd998/AsyncTerminationDetection.tla` @ `75f2a7a7…` | 4783 | 123 | `a28c7e84c7606ac4df30b0f9f1bc9f89129f27dc` |
| `SequencesExt.tla` | `modules/SequencesExt.tla` @ `9aae8ea1…` | 30449 | 546 | `2183f309d649f322d3403e21b5f75d7a9a6709e0` |
| `FiniteSetsExt.tla` | `modules/FiniteSetsExt.tla` @ `9aae8ea1…` | 10499 | 166 | `1b077f743c170c41d68d13693c9aea67b9eccd73` |
| `Folds.tla` | `modules/Folds.tla` @ `9aae8ea1…` | 2753 | 41 | `4b74814a3bcb7434946c9751e2a18e60f3179c6e` |
| `Functions.tla` | `modules/Functions.tla` @ `9aae8ea1…` | 11385 | 177 | `f80d28db1a125ce5223697fada2f87f4b38fa512` |
| `EWD998Small.cfg` | `specifications/ewd998/EWD998Small.cfg` @ `d0ca8f0e0678ed1c72ec2ce5c4723059a15a298b` | 210 | 21 | `0d664ddb9553cecf4194701526ea37b4d3084be5` |

The four CommunityModules modules are byte-identical copies of the ones already vendored in
`specs/tla/ewd998/` (same pin), copied rather than linked so this directory is self-contained for SANY's
"root module's directory" rule.

**`EWD998Small.cfg` is not from the publication-era commit.** It is imported from
`https://github.com/tlaplus/Examples`, path `specifications/ewd998/EWD998Small.cfg`, at commit
`d0ca8f0e0678ed1c72ec2ce5c4723059a15a298b` (2024-01-14, "Use CHECK_DEADLOCK config file parameter"),
under the MIT license (`LICENSE.md`). That commit is the newest upstream commit that touches the file,
and its bytes are byte-identical to the file at the pin `3dfe0087a36ccfc6f8aae7de6621c68e06fab955`
(verified both ways), so either commit yields the same 210 bytes, 21 lines, blob
`0d664ddb9553cecf4194701526ea37b4d3084be5`. No upstream commit after
`d0ca8f0e0678ed1c72ec2ce5c4723059a15a298b` modifies the file. Upstream added `EWD998Small.cfg` in
`4d227cd0d84afc722686e64bb9f2523a7179e906` (2023-02-15) — after the publication-era revision
`75f2a7a7369da8b8221232cb936c62d8c0b131f7` — which is why it cannot come from that commit. It is a copy
of the committed `specs/tla/ewd998/EWD998Small.cfg`: the paper's instance
(`CONSTANTS N = 3`, `CONSTRAINTS StateConstraint`, `INVARIANT TerminationDetection, Inv, TypeOK`) paired
with the publication-era modules. Pairing it here is safe because nothing else in the run differs:

- `StateConstraint` (`counter[i] <= 3`, `pending[i] <= 3`, `token.q <= 9`) is **identical** in both
  revisions — so the instance bound is the paper's K = C = 3, Q = 9 either way. The *only* state-space
  difference between the two revisions is the `Init` widening below.
- `CHECK_DEADLOCK FALSE` cannot change the set of reachable states; it only suppresses deadlock reports.

## Difference from the pinned branch head

`diff specs/tla/ewd998-paper/EWD998.tla specs/tla/ewd998/EWD998.tla` is exactly two hunks:

- `Init`, the state space: `dafe1e5c8a74` (2023-07-28) changed `token \in [ pos: {0}, … ]` to
  `token \in [ pos: Node, … ]` — *"The token may be at any node of the ring initially"* — which enlarges
  the reachable set. This is the whole measured drift.
- `Inv`, a comment line only, added by `51b9c62ba461` (2024-03-25, "Update comment in EWD998.tla").

## License notice

MIT, as in the upstream repositories.

### tlaplus/Examples — `LICENSE.md` (MIT)

> All these TLA+ examples are licensed under the MIT License.
>
> Copyright (c) 2016: The TLA+ project and other contributors:
> https://github.com/tlaplus/Examples/graphs/contributors
>
> Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
> associated documentation files (the "Software"), to deal in the Software without restriction,
> including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense,
> and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so,
> subject to the following conditions:
>
> The above copyright notice and this permission notice shall be included in all copies or substantial
> portions of the Software.
>
> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
> NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
> NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES
> OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
> CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

### tlaplus/CommunityModules — `LICENSE` (MIT)

> MIT License
>
> Copyright (c) 2019 TLA+
>
> Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
> associated documentation files (the "Software"), to deal in the Software without restriction,
> including without limitation the rights to use, copy, modify, merge, publish, distribute,
> sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
> furnished to do so, subject to the following conditions:
>
> The above copyright notice and this permission notice shall be included in all copies or substantial
> portions of the Software.
>
> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
> NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
> NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES
> OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
> CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

The pinned branch head and its own provenance are in `specs/tla/ewd998/PROVENANCE.md`; the measured
comparison between the two revisions is in `docs/human-baseline.md` and, machine-readable, on the
`ewd998` record in `results/human.jsonl`.
