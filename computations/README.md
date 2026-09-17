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

The separate checker uses Fraction Gaussian elimination at p=1,3/2,2 for 48 moment determinant comparisons; it checks 45 positive Stieltjes coefficients and three formal series through degree fifteen; and it compares 40 residue calculations with exhaustive permutations. It also checks six invalid-input cases and nonempty-output refusal under optimised Python. These are different implementation paths, but pointwise checks do not replace all-base polynomial identities.

The interval certificate bounds π with Machin's formula and alternating arctangent series, the positive trigamma tail with integral inequalities, and logarithms with rational atanh series. It encloses the inherited constants and the 31/4 exponent bound strictly below 301. It is an ordinary exact-arithmetic verification, not a fresh Lean theorem.

## Formal-status boundary

No Lean executable or lake build was run. The kernel-status discussion in the papers concerns the supplied indexed source and historical CI evidence, not these Python files. Historical rank-seven, reconstruction and direction checks from the earlier project are not presented as fresh reruns here.
