<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Reproduce the Erdős 257 computations

The truncated half-value problem HalfRung(J) holds for every truncation
order 3 ≤ J ≤ 22, and the greedy orbit for 1/2 with weights 1/(2^n − 1)
survives every rank through 200,000, so that
0 ≤ 1/2 − Σ_(d∈G, d≤200000) 1/(2^d − 1) < 2^(−199999). The programs here
reproduce these finite computations and the others cited in the
[Mersenne reasoning paper](../../../paper/257/erdos257-mersenne-reasoning-surface.tex):
the integer quotient rows, the sharp tail margins and the forced prefix to
depth 13,548,057. The two working notes behind those statements are in
[notes/](notes/). Every take, skip, witness and crossing decision is made
with exact integers. Each run covers a finite range, and none decides
Erdős #257. The programs do not run Lean.

Use Python 3.10 or newer. From the repository root, this command reruns
three short cases and compares each with its saved result, using only the
standard library:

```sh
python3 research/experiments/erdos257/replay.py
```

Expect `matched_recorded_result: true` for `truncation-ladder`,
`quotient-identity` and `tail-margins-3000`, in about half a minute. `--case NAME` runs one case and
`--case all` runs all nine in sequence. `--check` confirms that every saved
receipt still matches the program bytes without rerunning anything.
`--timeout` sets one time limit for every case; without it each case uses five minutes, or longer for the four large cases.

## The recorded runs

| Case | Paper statement | Program | Range | Needs | Observed time |
| --- | --- | --- | --- | --- | --- |
| [truncation-ladder](receipts/truncation-ladder-3-16.json) | HalfRung(J) proved for each J | [check_truncation_rung_ladder.py](check_truncation_rung_ladder.py) | J = 3 to 16 | standard library | under 1 second |
| [truncation-ladder-numpy](receipts/truncation-ladder-17-22.json) | B(19) = 1008, B(20) = B(21) = B(22) = 1530 | same program | J = 17 to 22 | NumPy | 2 minutes |
| [quotient-identity](receipts/quotient-identity-200.json) | identity (I), rows 6 to 200 | [check_master_identity.py](check_master_identity.py) | rows 6 to 200 | standard library | under 1 second |
| [seam-2500](receipts/seam-reset-crossing-2500.json) | 1209 resets, margins from +1.1119 bits | [check_seam_reset_crossing.py](check_seam_reset_crossing.py) | rows 6 to 2500 | standard library | 34 seconds |
| [tail-margins-3000](receipts/tail-margins-3000.json) | 1497 takes, 1502 skips, no fatal skip | [check_half_greedy_margins.py](check_half_greedy_margins.py) | ranks 2 to 3000 | standard library | 20 seconds |
| [seam-200000](receipts/seam-orbit-200000.json) | R:M:U = 100197:49899:49898, one target failure at r = 7 | [seam_orbit_replay.py](seam_orbit_replay.py) | rows 5 to 200,000 | standard library | 11 minutes |
| [greedy-prefix-200000](receipts/greedy-prefix-200000.json) | 0 ≤ 1/2 − (greedy prefix sum) < 2^−199999 | [certify_greedy_interval.py](certify_greedy_interval.py) | ranks 1 to 200,000 | standard library | 104 seconds |
| [greedy-prefix-100000](receipts/greedy-prefix-100000.json) | cross-check with a separate stream receipt | same program | ranks 1 to 100,000 | standard library | 42 seconds |
| [coefficient-macro](receipts/coefficient-macro-13548057.json) | depth 13,548,057 | [half_prefix_coefficient_macro_verify.cpp](half_prefix_coefficient_macro_verify.cpp) | depth 13,548,057 | C++20 compiler and GMP | 7 seconds with compilation |

The times were measured on one Apple M4 machine while other jobs were
running. The NumPy case needs the pinned dependency in a virtual
environment:

```sh
python3 -m venv .venv-computations
.venv-computations/bin/python -m pip install -r research/experiments/erdos257/requirements.txt
.venv-computations/bin/python research/experiments/erdos257/replay.py --case truncation-ladder-numpy
```

Integer, string and boolean results must match exactly. Floating-point
summaries of exact quantities (bit margins and averages) use relative and
absolute tolerance `1e-12`. Timing fields and temporary output paths are
left out of the comparison. A mismatch exits with code 1 and names the
first differing fields.

## Truncation rungs

For a truncation order J the weights are the first J terms of the geometric
expansion of 1/(2^n − 1). The program lists every M with misalignment mass
at most 11/15 (for J ≥ 7 only multiples of 12, by the mod-12 filter),
derives the bad ranks in [4, L_J/2] and their maximum B(J), and runs the
J-truncated greedy for 1/2 through rank B(J) with exact integers. By the
finite decision procedure in the paper, survival through B(J) proves
HalfRung(J). Every J from 3 to 22 reports `fatal_at: null` and
`n_hard_skips: 0`. The values of B(J) and the counts of bad ranks equal the
table in the [truncation note](notes/truncation-rung-ladder-2026-07-24.md).

For J ≥ 17 a NumPy floating-point filter with slack 10^−9 proposes witness
candidates, and every accepted witness is then rechecked with integers. A
witness missed by the filter could only add a bad rank and so lengthen the
exact greedy check; the survival conclusion therefore rests on the integer
steps. This single program is the whole check: no separate certificate file
or second verifier exists. Two further checks from the note run in under a
second each:

```sh
python3 research/experiments/erdos257/check_truncation_rung_ladder.py exhaustive 3 4 5
python3 research/experiments/erdos257/check_truncation_rung_ladder.py xcheck3 3000
```

They report zero fatal prefixes among 131,071 prefixes per rung through
rank 18, and agreement of the J = 3 automaton with the exact greedy through
depth 3000. These two are not part of the saved receipts.

## Integer quotient rows 6 to 2500

`check_seam_reset_crossing.py` recomputes every quotient row from its
definition, with weights ⌊4^n/(2^d − 1)⌋ and target 2^(2n−1) − 2^n,
classifies each transition as an upper reset, a middle reset or a right
step, and compares each reset deviation Δ with 2^((r+5)/2). The margin is
log₂|Δ_(r+1)| − (r+5)/2. The run checks the anchors rem(14) = 392 and
rem(15) = 34333 and finds:

* 1209 resets in rows 6 to 2500 (604 upper, 605 middle) and zero
  classification anomalies;
* a positive deviation at every middle reset and a negative deviation at
  every upper reset;
* smallest margin +1.1119 bits at row 14 among resets at rows 14 and above,
  largest 1246.55 bits at row 2499, mean 627.36;
* a single reset with nonpositive margin, at r = 7 (middle reset,
  deviation +9);
* exactly two crossing cells, (s, d) = (7, 5) on a middle branch and
  (10, 7) on a right branch, both below row 14.

The program writes its full ledger to a temporary directory during replay.
It stops early if its own 240 second sweep budget runs out, which would
show as a mismatch in `max_row` on a very slow machine.

## Sharp tail margins, ranks 2 to 3000

`check_half_greedy_margins.py` runs the greedy rule for 1/2 with the full
weights 1/(2^n − 1), keeping the remainder as an exact fraction. At each
skip it certifies that the remainder is at most the tail
T_(k+1) = Σ_(j>k) 1/(2^j − 1), using scaled integer bounds for the tail.
It finds 1497 takes and 1502 skips (take fraction 0.4992), no fatal skip
and no unresolved skip. The smallest safe-skip margin is +2.9922 bits at
rank 5 and the next is +3.3572 bits at rank 4. The smallest take margin is
+0.0340 bits at rank 7, where the remainder 1/126 exceeds the weight 1/127
and 1/126 − 1/127 = 1/16002. The margins are log₂(4^k(r_(k−1) − x_k)) at a
take and log₂(4^k(T_(k+1) − r_(k−1))) at a skip; they are floating-point
summaries of exact integers.

## Quotient rows to 200,000

`seam_orbit_replay.py` follows the same quotient rows through the exact
successor recursion for the three branches, so it reaches row 200,000;
the recorded run used 337 seconds of processor time. It checks the recursion against the direct row-by-row greedy
through row 100 and against a literal set recurrence through row 2000.
It finds:

* transitions from rows 6 to 200,000: 100197 right, 49899 middle and 49898
  upper steps; counted from row 5 there are 49899 upper steps, since the
  row-5 transition is itself an upper reset;
* the square-root target Δ_(r+1)² > 2^(r+5) fails at exactly one reset row
  r ≥ 6, namely r = 7 (the row-5 reset also fails and lies below the first
  quotient row);
* a longest run of 19 consecutive right steps, following the reset at row
  158,096;
* for transitions from rows 6 to 2499, the same 605 middle and 604 upper
  resets as the row-by-row program.

The row-stream and producer-stream hashes it prints equal those of the
maintainer's earlier 200,000-row receipt; the branch recursion is copied
unchanged from that program and the reset tally was added for this release
(see [source provenance](source-provenance.json)).

## Greedy prefix to rank 200,000

`certify_greedy_interval.py` replays the greedy rule for 1/2 with weights
1/(2^n − 1) using integer lower and upper bounds at a fixed scale of
200,512 bits. It decides every take and skip and certifies the comparison
with the tail at every rank. Through rank 200,000 the orbit survives with
100,306 takes, and every decision is settled by the interval bounds.
Survival at rank m means the remainder is at most T_(m+1), and
T_(m+1) < Σ_(j>m) 2^(1−j) = 2^(1−m). With m = 200,000 this gives
0 ≤ 1/2 − Σ_(d∈G, d≤m) 1/(2^d − 1) < 2^(−199999), the finite statement in
the paper. The `greedy-prefix-100000` case also compares the first 100,000
ranks with the separate stream receipt
[greedy-half-stream-100000.json](receipts/greedy-half-stream-100000.json):
50,214 takes and the same selected-sequence hash.

## Forced prefix to depth 13,548,057

`half_prefix_coefficient_macro_verify.cpp` works with the proper-divisor
coefficients g(r) = #{d in the support : d | r, d < r} and exact reverse
base-two normalisation. From depth 1 it regenerates an 18-step seed to
depth 423,377 and then five doubling steps to depth 13,548,057. At each
step it checks that the regenerated prefix agrees with the previous one,
that the reverse carry vanishes, and that every floor it uses is isolated
by strict integer bounds. It ends at depth 13,548,057 with 6,782,259
selected ranks, and the hashes of its four output files equal the original
receipt. When this release was prepared, its selected ranks up to 200,000
were also compared with the interval certificate above (same set) and up to
3000 with the tail-margin run (same set). The paper does not rely on this
computation.

The replay compiles the program into a temporary directory and runs it. The
program itself writes four files named `/tmp/coefficient_*`. To compile it
by hand:

```sh
clang++ -O3 -std=c++20 research/experiments/erdos257/half_prefix_coefficient_macro_verify.cpp -lgmpxx -lgmp -o macro_verify
./macro_verify
```

On macOS with Homebrew, add `-I/opt/homebrew/include -L/opt/homebrew/lib`.

## Quotient identity

`check_master_identity.py` checks identity (I),
Δ_n = K(2n) + Σ_(d∈Skip_n) ⌊4^n/(2^d − 1)⌋, at rows 6 to 200, the
recurrence K(M+1) = 2K(M) − (τ(M+1) − 1) against the definition of K up to
index 400, and the sum Σ_(d=n)^(2n) ⌊4^n/(2^d − 1)⌋ = 2^(n+1) used in the
proof. It reports zero mismatches. The paper proves (I) for every n ≥ 6;
this program is a finite check written for this release. `--max-row`
extends the range.

## Working notes

* [Truncation-rung ladder](notes/truncation-rung-ladder-2026-07-24.md)
  gives the ordinary proofs of witness exclusion, the half-LCM horizon, the
  mod-12 filter, the finite decision procedure, compactness transfer and the
  ladder dichotomy (its Corollary 8), with the certificate table for
  J = 3 to 22.
* [Reset-crossing unification](notes/reset-crossing-unification-2026-07-24.md)
  gives the quotient-row model, the reset and crossing analysis, the
  decision structure of the greedy orbit, and in its section 8 the
  2500-row and 3000-rank runs reproduced above.

Both notes were written with AI assistance in the maintainer's research
sessions and are published unchanged apart from a licence header. Neither
has had independent review. Their reproduction commands name the
maintainer's working paths; the programs are the files of the same name in
this directory.

## Provenance and reporting

Will Cook directed the original programs, which were written with AI
assistance. [Source provenance](source-provenance.json) records the
original hashes and every change made for the public copies. Each saved
receipt binds the public program bytes and exact arguments. Changing an
argument computes a different finite experiment and does not update a
saved result. Report a discrepancy, with the command, output and Python
version, through the repository's [contribution route](../../../CONTRIBUTING.md).
Code, notes and computation data use Apache-2.0. A match with a saved run
shows that the computation reproduces; review of the notes and of the
arguments that use these computations is a separate matter.
