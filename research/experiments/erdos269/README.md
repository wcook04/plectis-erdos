<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Exact finite checks

For every one of the 2,496 first-escape windows with `B≤97`, `gcd(B,30)=1`,
and starts 1–96, a successful length at most 10 is recorded. These are finite
certificates, not a cofinal escape or irrationality theorem.

Python 3.10 or later and the standard library suffice. Run without `-O`: the two inherited checkers use assertions. No network or formal prover is invoked.

```sh
python3 check_structures.py --n 256 --output exact_checks.json
python3 check_new_lemmas.py --n 256 --output new_ordinary_checks.json
python3 check_pass2.py --output-dir .
python3 verify_certificates.py pass2_certificates.json
```

The first two scripts reconstruct the literal shell sequence and independently count 781,832 weighted triangle terms over 256 shells. Their remaining diagnostics include finite shift identities and exact carry ansatz failures, not an assertion about every eventual polynomial or every fixed operator.

`pass2_certificates.json` contains the no-crossing cubic row counts and all 2,496 first-escape window witnesses for `B≤97`, `gcd(B,30)=1`, starts 1–96, maximum allowed length 24. Observed first lengths are 1–10. `verify_certificates.py` does not import the producer: it checks the cubic row endpoints with integer powers, reconstructs shell data with a separate enumeration and verifies the declared grid is complete. It checks first-success claims, not only success at a chosen length.

`check_pass2.py` also checks 25 exact strip decompositions, 14,000 synthetic rational-denominator cases, 125 onset fixtures, 150 direct-recoding indices and 3,900 explicit defect bounds. Six altered certificates must be rejected. Synthetic rational tests are algebraic fixtures, not approximations asserting the target scalar is rational.

`execution_receipt.json` records the commands actually run, runtime/version information, source hashes and output hashes. Output regeneration changes no manuscript and publishes nothing. Those four commands do not rerun the larger scan or the two large exclusions; the programs in [large-computations/](#the-larger-scan-and-the-two-large-exclusions) do. No finite output proves the cofinal escape statement or irrationality.

## The larger scan and the two large exclusions

The directory [large-computations/](large-computations/) reruns the three
larger computations of the long paper: the scan over B ≤ 5000, the
continued-fraction exclusion of every denominator up to 2^22482, and the
window-128 lattice exclusion up to the 106-digit bound B_max. From the
repository root, this command runs the smaller scan, the certificate
verifier and the continued-fraction regeneration, about fifteen seconds in
all, with the standard library only:

```sh
python3 research/experiments/erdos269/large-computations/replay.py
```

Expect `matched_recorded_result: true` for each case. `--case NAME` runs one
case, `--case all` runs every case and `--check` confirms program and data
hashes without rerunning anything. `cf-statistics` and `lattice-search`
need NumPy from `large-computations/requirements.txt`. Without `--timeout`,
each case may use five minutes, the large scan fifteen and the lattice
search thirty.

| Case | What it reproduces | Program | Observed time |
| --- | --- | --- | --- |
| [scan-small](large-computations/receipts/scan-1000-100-500.json) | 106,666 pairs, B ≤ 1000, 100 ≤ ℓ ≤ 500; every pair escapes; longest first length 14, first at B = 359, ℓ = 291 | [check_erdos269_dyadic_windows.py](../../../scripts/check_erdos269_dyadic_windows.py) | 5 seconds |
| [scan-large](large-computations/receipts/scan-5000-100-3000.json) | 3,869,934 pairs, B ≤ 5000, 100 ≤ ℓ ≤ 3000, search depth 24; every pair escapes; the paper's histogram and its length-18 case at B = 917, ℓ = 2980 | same program | 3.5 minutes |
| [regenerate-tail](large-computations/receipts/regenerate-tail.json) | shell data for 1 ≤ a ≤ 15,500, the rational enclosure of X_1 and its 13,540-term common continued-fraction prefix, byte for byte | [regenerate_269.py](large-computations/regenerate_269.py) | 6 seconds |
| [verify-certificates](large-computations/receipts/verify-certificates.json) | 37,462 integer checks of the stored shell data, enclosure, cylinder and lattice certificate | [verify_recovered.py](large-computations/verify_recovered.py) | 5 seconds |
| [cf-statistics](large-computations/receipts/cf-statistics.json) | the paper's recorded continued-fraction statistics | [erdos269_continued_fraction.py](large-computations/erdos269_continued_fraction.py) | 5 seconds |
| [lattice-search](large-computations/receipts/lattice-search.json) | the published lattice basis, budgets and B_max, from the shell data | [regenerate_block_certificate.py](large-computations/regenerate_block_certificate.py) | 7 minutes |

Times are from one Apple M4 machine while other jobs were running.

**The scan.** Every one of the 3,869,934 pairs with B ≤ 5000 coprime to 30
and 100 ≤ ℓ ≤ 3000 escapes within length 18. The first-success histogram
is 4: 1, 5: 104, 6: 812, 7: 5437, 8: 51409, 9: 237423, 10: 735450,
11: 1431226, 12: 1132756, 13: 236752, 14: 34910, 15: 3076, 16: 521, 17: 49,
18: 8, and the first length-18 case, B = 917 and ℓ = 2980, has endpoint jump
index 6179, window base 18139852800000000, accumulated numerator
13196471407660025821045, least positive residue 76322101735 and bound
3896420420. These are the figures printed in the paper.

**The continued-fraction exclusion.** Write X_1 = S − 1. With W and F the
window base and accumulated numerator of shells 1 to 15,500, the tail bound
that gives the paper's twelve-shell certificate gives
F/W < X_1 ≤ (F + Q)/W with Q = (n² + 8n + 18)/9 at n = 31,956, that is
Q = 340480534/3. Run with 11 shells, the same construction returns exactly
the twelve-shell enclosure printed in the paper. Every shell is built with
integers: each logarithm floor is decided by rational bounds, and shells 1
to 30 are also checked against a direct enumeration of the smooth numbers.
The two endpoints share their first 13,540 partial quotients. The first
13,109 digits (a_0 = 0 included) define a cylinder with endpoints p/q and
(p + p′)/(q + q′), which have cross-determinant 1 and strictly contain the
enclosure. Every fraction strictly between two such endpoints has
denominator at least q + (q + q′), here a 22,483-bit integer, so neither
X_1 nor S equals a fraction with denominator at most 2^22482. The endpoints
are in `regenerated/tail_certificate.json` and the digits in
`regenerated/cf_common_prefix.json`. The original probe counts 13,109
partial quotients after a_0 and reproduces the statistics the paper
records: largest convergent denominator 22,483 bits, largest partial
quotient 129,114, mean 23.4133, frequencies 0.4208, 0.1665, 0.0917, 0.0575,
0.0391 for the values 1 to 5, and Lévy value 1.18869.

**The window-128 lattice exclusion.** The certificate uses the first 64
starting indices a ≥ 10,005 whose length-128 windows have the same base as
the window at 10,005, namely P = 2^128 · 3^81 · 5^56. Put m_0 = P/2, let F_j be
the accumulated numerator of window j and w_j = (a_j + 128)² + 6(a_j + 128) + 11.
The certificate lists 64 integer vectors c_i with Σ_j c_ij F_j ≡ 0 (mod m_0),
their weighted sizes Σ_j |c_ij| w_j, the largest being 184,560,461,211, and
an integer matrix D with DC = CD = m_0 I. Suppose integers f_j satisfy
f_j = P s_j − 2B F_j and 0 < f_j ≤ B w_j for all j. Each Σ_j c_ij f_j is
then a multiple of P of absolute value at most 184,560,461,211 · B, hence
zero whenever B ≤ B_max = ⌊(P − 1)/184,560,461,211⌋, and invertibility of C
forces every f_j to vanish, a contradiction. This B_max is the 106-digit
number in the paper, and log₂ P = 386.40993. A rational value N/(MB) of
the series, with M dividing 2^10005 · 3^6312 · 5^4308 and gcd(B, 30) = 1,
yields such integers f_j through the window identity with the full height
at each start, the normalisation the paper notes for this family. This
replay checks the finite certificate in `regenerated/block_certificate.json`.
It does not check that reduction from a rational value to the 64
inequalities.

The certificate programs and data come from an AI-assisted research round
on 10 September 2026 and are published unchanged apart from licence
headers. The continued-fraction probe and its engine modules are the
maintainer's programs with local imports.
[Source provenance](large-computations/source-provenance.json) records the
original hashes. None of these runs proves escape for every denominator or
every start, and none proves irrationality.
