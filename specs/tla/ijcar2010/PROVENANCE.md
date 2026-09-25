# Provenance — IJCAR 2010 trio (Peterson / Bakery / Paxos)

The four `.tla` files here are imported **byte-for-byte** from `tlaplus/tlapm` at
`7824dab55e0c346e913404d59d0bbdeebce73cc1` (BSD-2-Clause). They are the specification and proof
artifacts of:

> Kaustuv Chaudhuri, Damien Doligez, Leslie Lamport, Stephan Merz, *Verifying Safety Properties With
> the TLA+ Proof System*, IJCAR 2010 — <https://members.loria.fr/SMerz/papers/ijcar2010.pdf>

Nothing was edited after import; attribution is by this file. Byte sizes, line counts and git blob
SHA-1s were measured against the pinned commit and can be re-checked with `git hash-object <file>`.
Files were fetched from the pinned raw form
`https://raw.githubusercontent.com/tlaplus/tlapm/7824dab55e0c346e913404d59d0bbdeebce73cc1/<path>`.

| File | Upstream path | Bytes | Lines | Blob SHA-1 |
| --- | --- | --- | --- | --- |
| `peterson/Peterson.tla` | `examples/Peterson.tla` | 6363 | 199 | `4b4f6012ceddbbbbfa7af84266ca8aa37ed46d9b` |
| `bakery/Bakery.tla` | `examples/Bakery.tla` | 17551 | 383 | `35f6accfb86049521d71b6f5a5742e3b0a40ac31` |
| `paxos/Paxos.tla` | `examples/paxos/Paxos.tla` | 25552 | 530 | `bdec77b86eb79d31069f33df725e8cce14acc18c` |
| `paxos/Consensus.tla` | `examples/paxos/Consensus.tla` | 934 | 22 | `41be40c6a8e11f92bcedd1cc715a8e7d36d5ca41` |

- `Peterson.tla` — two-process mutual exclusion (`EXTENDS TLAPS`).
- `Bakery.tla` — Lamport's bakery algorithm plus a TLAPS-checked mutual-exclusion proof
  (`EXTENDS Naturals, TLAPS`).
- `paxos/Paxos.tla` — Paxos consensus (`EXTENDS Integers, TLAPS, TLC`), with
  `C == INSTANCE Consensus WITH chosen <- chosenBar`.
- `paxos/Consensus.tla` — the trivial consensus specification instantiated by `Paxos.tla`.

## Not machine-checked here

The proofs in these modules are TLAPS proof scripts (`EXTENDS TLAPS`). They are imported **as text
with provenance**: `tlapm` is neither in the dev shell nor in nixpkgs, is **not** invoked anywhere in
this repository, and no test or scenario parses these files with SANY. The corresponding record in
`results/human.jsonl` therefore carries `machine_checked: false` and the note that it is imported text
with provenance only. The published effort figures (proof lines, and the Paxos second refinement being
incomplete) are recorded there as citations, never as this repository's measurements.

## License notice

### tlaplus/tlapm — `LICENSE` @ `7824dab5…` (BSD-2-Clause)

> Copyright (c) 2008 INRIA and Microsoft Corporation
> Copyright (c) 2023 Linux Foundation
>
> Redistribution and use in source and binary forms, with or without
> modification, are permitted provided that the following conditions are
> met:
>
>   * Redistributions of source code must retain the above copyright
>     notice, this list of conditions and the following disclaimer.
>
>   * Redistributions in binary form must reproduce the above copyright
>     notice, this list of conditions and the following disclaimer in
>     the documentation and/or other materials provided with the
>     distribution.
>
> THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
> "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
> LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
> A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
> OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
> SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
> LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
> DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
> THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
> (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
> OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

No per-file license headers exist upstream; this file is the attribution.
