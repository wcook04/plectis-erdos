<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Exact computations and scope

For every rank `N≤8` and both shifts, the translated Hankel moment determinant
is monic with strictly positive coefficients in `t=p-1`; 76 cyclotomic residue
witnesses are nonzero, and a rational interval places the `31/4` exponent
strictly below 301. These are finite computer-algebra certificates, not Lean
theorems and not an all-rank sign result.

Tested with Python 3.13.5 and SymPy 1.14.0. `polynomials.py` has no run-on-import experiments. The package uses exact rational/polynomial arithmetic; floating-point values are timing data only. The interval program uses Python's `Fraction` without SymPy.

## Reproduce into a new directory

```sh
python -m pip install -r computations/requirements.txt
python computations/reproduce.py --output /path/to/new-certificates --max-rank 8 --residue-max-rank 8
python computations/intervals.py --output /path/to/new-intervals.json
python computations/check_independently.py \
  --output /path/to/new-independent-checks.json
```

Use the command-line `--help` of each script for the exact options. The reproduction driver refuses a nonempty output directory; interval and independent outputs must be new files. The rank guard is explicit. Run from the bundle root. Installation requires the user's own environment/network; no runtime package fetch is hidden inside the computations.

`certificates/` contains 16 translated moment-determinant coefficient lists through rank eight, both shifts; a summary; five full polynomial contents; 76 minimum-valuation residue witnesses; a run receipt; exact intervals; and independent checks. The old first-pass moment summary is intentionally not duplicated at this directory's root.

## What was recomputed

Two fresh complete runs agreed byte for byte on all **19 core mathematical JSON files**: the 16 coefficient lists plus the finite-moment summary, full contents and cyclotomic residue witnesses. `certificates/fresh_reproduction.json` records hashes and script versions. `reproduction.log` and `certificates/run.json` are run provenance, not mathematical certificates and not expected to have identical timing values across runs.

For each coefficient list, entries are decimal integer strings, ordered from constant coefficient to leading coefficient, in t=p−1. Every stored coefficient is strictly positive and the leading coefficient is 1. This proves the corresponding finite determinant inequality for all real p≥1 once the exact identity calculation is accepted. It does not prove positivity in all ranks. The degree table is checked against the independent all-rank degree argument in the paper.

Full contents are monic gcds over **Q[p]**, not integer contents over Z[p]. Values at Y=0,…,N suffice because the rational Vandermonde matrix is invertible. The −1 in β_m is part of the normalisation, including β_0=0. The 76 witnesses cover exactly 1≤N≤8 and 1≤d≤max(8,2N−2). All tested residues are nonzero: this certifies sharp entry-forced valuation at those pairs, not an unobserved surplus or all-index theorem.

## Independent checks

The separate checker uses Fraction Gaussian elimination at the integer bases named in the paper, together with the rational base 3/2. It checks positive Stieltjes coefficients and formal series through degree fifteen, and compares residue calculations with exhaustive permutations. It also checks invalid inputs and nonempty-output refusal under optimised Python. The selected bases and check counts are recorded in [the generated result](certificates/independent_checks.json). These are different implementation paths, but pointwise checks do not replace all-base polynomial identities.

The interval certificate bounds π with Machin's formula and alternating arctangent series, the positive trigamma tail with integral inequalities, and logarithms with rational atanh series. It encloses the inherited constants and the 31/4 exponent bound strictly below 301. It is an ordinary exact-arithmetic verification, not a fresh Lean theorem.

## Formal-status boundary

No Lean executable or lake build was run. The kernel-status discussion in the papers concerns the supplied indexed source and historical CI evidence, not these Python files. Historical rank-seven, reconstruction and direction checks from the earlier project are not presented as fresh reruns here.

## `finite_coefficients.json` — reconstructed 2026-09-20

The paper cites `computations/finite_coefficients.json` and
`computations/check_finite_coefficients.py`. Neither path existed in this
repository or anywhere in its git history; `git log --all` over those paths is
empty, and the only history hits for the string are the commits that introduced
the citing prose. The *data* was present all along, split across the sixteen
`certificates/s_hankel_rank<N>_shift<h>.json` files written by `reproduce.py`.
What was missing was the two cited filenames, not the computation.

The two files were therefore written fresh on 2026-09-20, from the definitions
in `paper/reasoning-parts/erdos1049/core.tex` (lines 1790–1896) and in
`lean/ErdosProblems/Erdos1049/PaperR20/CoefficientPencil.lean`. They are new
artefacts, not recovered originals. Both use the Python standard library only —
exact integers, no SymPy, no floating point — so they are an implementation path
independent of `polynomials.py` and `reproduce.py`.

```sh
python3 computations/finite_coefficients_generate.py   # writes finite_coefficients.json
python3 computations/check_finite_coefficients.py      # checks it, independently
```

`finite_coefficients_generate.py` builds `s_m` from the Gaussian-binomial
q-Pascal recursion and computes every `D_{N,h}` twice: once by a division-free
Laplace expansion over column subsets, once by the paper's Desnanot–Jacobi
condensation with all 56 divisions asserted to leave zero remainder. The two
routes are required to agree, and large products use Kronecker substitution,
which is exact. Runtime 71 s at rank eight.

`check_finite_coefficients.py` imports nothing from the generator. It rebuilds
`s_m` from the Gaussian-binomial *product* formula by exact division, cross-checks
`R_m` against Van Assche's positive expansion and `s_m(1)` against `(m!)^3`,
derives the degree bound by brute-force maximisation over all `N!` permutations
rather than from the paper's closed form, and then connects the stored list to
`D_{N,h}` by exact integer evaluation at more distinct bases than that degree
bound, against Bareiss fraction-free elimination of the integer Hankel matrix.
Agreement at `deg + 9` bases between two polynomials of degree at most `deg` is
an identity in `Z[p]`, not a sample. Runtime 16 s.

Both agree with the paper's degree table, with the count of 8824 strictly
positive coefficients, and with the sixteen existing per-rank files.
