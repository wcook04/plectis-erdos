# Erdős 1049 finite computations

This directory holds the programs and recorded outputs for the finite
computations described in the long Erdős 1049 paper
(`paper/reasoning-parts/erdos1049/core.tex`). Each program states in its
docstring what it proves and what it leaves out. None of them runs Lean, and
none is used by the proof of the irrationality theorem.

| Computation | Program | Receipt | Replay time |
| --- | --- | --- | --- |
| Printed digits of the cutoff | [`threshold_digits.py`](threshold_digits.py) | [`threshold-digits.json`](receipts/threshold-digits.json) | under 1 second |
| Rational-base examples | [`rational_base_examples.py`](rational_base_examples.py) | [`rational-base-examples.json`](receipts/rational-base-examples.json) | under 1 second |
| Certified parameter box | [`parameter_box.py`](parameter_box.py) | [`parameter-box.json`](receipts/parameter-box.json) | 15 to 45 seconds |
| Source polynomials for n = 1, 2, 3, 4 | [`source_polynomials.py`](source_polynomials.py) | [`source-polynomials.json`](receipts/source-polynomials.json) | 10 to 25 seconds |
| Cyclotomic content of the coefficient pencil | [`cyclotomic_content.py`](cyclotomic_content.py) | [`cyclotomic-content.json`](receipts/cyclotomic-content.json) | 5 to 10 seconds |
| Sign of the main term at 31/4 for n <= 400 | [`main_term_31_4.py`](main_term_31_4.py) | [`main-term-31-4.json`](receipts/main-term-31-4.json) | 2 to 4 seconds |
| Hankel q-order and leading coefficient for N <= 7 | [`hankel_qorder.py`](hankel_qorder.py) | [`hankel-qorder.json`](receipts/hankel-qorder.json) | 2 to 4 seconds |
| Numerical direction search | [`direction_search.py`](direction_search.py) | [`direction-search-bound30.json`](receipts/direction-search-bound30.json) | see below |

The first seven programs use only the Python standard library (Python 3.11 or
newer) and exact integer or rational arithmetic. Times are wall-clock
replays on an Apple M4 laptop; the range reflects different machine load. A
full replay takes one to two minutes.

## Replay

From the repository root:

```sh
python3 research/experiments/erdos1049/replay.py
```

This reruns the seven exact computations and compares each output with its
receipt. Expect `matched_recorded_result: true` seven times. Every recorded
value is an integer, a string or a boolean, so the comparison is exact. Use
`--case NAME` to run one case (`threshold-digits`, `rational-base-examples`,
`parameter-box`, `source-polynomials`, `cyclotomic-content`,
`main-term-31-4`, `hankel-qorder`). With `--check`,
the script only confirms that each receipt records the SHA-256 of the current
program bytes and that the saved run verified every printed claim. A mismatch
exits with code 1 and names the first differing field.

Each program also runs on its own and prints its result as JSON, for example
`python3 research/experiments/erdos1049/threshold_digits.py`. The field
`all_printed_claims_verified` is `true` when every number the paper prints for
that computation is confirmed, and the exit code is then 0. The option
`--receipt PATH` writes a new receipt with the program digest.

## Printed digits of the cutoff

The paper prints

```
0.4056830213840605403 < theta* < 0.4056830213840605417,
2.4649786835749750334 < mu     < 2.4649786835749750415.
```

`threshold_digits.py` carries out the error bound printed after these
inequalities. For each of the thirteen intervals it rounds the first 65,536
summands of the trigamma difference down to multiples of 10^-50, adds the
integral bounds for the tail, encloses pi with Machin's formula and uses the
positivity of 225 - J to order the endpoints of C0. It also recovers the
thirteen intervals from the floor-function definition of the weight. The
recorded enclosure is

```
0.405683021384060540355787 <= theta* <= 0.405683021384060541675523,
2.464978683574975033445083 <= mu     <= 2.464978683574975041463955.
```

The printed bounds are the outward roundings of this enclosure to nineteen
decimal places. The options `--summands` and `--digits` run the same method
with other parameters; those runs do not reproduce the printed digits.

The coarser certificate with 256 summands, which gives the fourteen-place
values of J, C0 and theta* in Section 2 and the exponent bound between
300.4269130 and 300.4269164 for 31/4, is
[`computations/intervals.py`](../../../computations/intervals.py) with its
output in `computations/certificates/intervals.json`.

## Rational-base examples

`rational_base_examples.py` encloses logarithms by artanh series, pi by
Machin's formula and theta* by the method above with 4,096 summands, and
decides every comparison by disjoint rational intervals. It confirms:

- there are 1,101 reduced fractions a/b with 1 <= b < a <= 60; 137 lie in the
  region log b / log a < theta*, and 78 of those are non-integral;
- the two largest admitted ratios belong to 53/5 and 31/4, with margins that
  round to 0.000313 and 0.001985;
- the smallest excluded ratio belongs to 52/5, equals 0.4073243836..., and
  exceeds theta* by an amount that rounds to 0.001641;
- the strip s^mu < r <= s^mu_BV contains no coprime numerator for s = 2 and
  s = 3, only 31 for s = 4, and 53, 54, 56 for s = 5; and 5^mu > 52, so 31/4
  has the least numerator in the strip;
- the decimal values printed with the theorem on 31/4: log 4/log 31,
  4^mu, 4^mu_BV, mu_BV, 1/2 - 1/pi^2, log 2/log 3 and its excess over theta*,
  and the chain 1/2 - 1/pi^2 < 2/5 < log 4/log 31 < 81/200 < theta*.

## Certified parameter box

The box consists of the 37,533 integer tuples (alpha0, alpha1, alpha2; beta)
with entries at most 30, gcd 1, alpha1 <= alpha2 and
alpha1 + alpha2 < beta <= alpha0 + alpha2. `parameter_box.py` computes C0/C1
for every tuple with rational intervals, in two independent implementations.
Implementation A sums 256 terms per cell exactly and enumerates in increasing
order; implementation B uses 512 terms per cell, rounded summands, midpoint
weights and a decreasing enumeration. Both use the 278 cells cut out of [0, 1)
by the fractions j/c with c <= 30, and both check that every weight is 0 or 1.

Both implementations find exactly two maximisers, (14,12,14;27) and
(15,12,13;26). With 256 terms their enclosures lie inside
(0.40568302137302, 0.40568302139506), and the largest upper endpoint over all
other tuples is 0.40563943278332137, attained at (16,13,14;28), which is below
the printed 0.40563943278333. The 512-term run gives tighter enclosures and
the same conclusion. The exact equality of the two maximal values is the
analytic argument in the paper; the program checks its finite inputs (the floor
identity on every cell, m = 15, C1 = 1091/2 and the quadratic parts 266 and
265). The result concerns this finite box only.

## Source polynomials for n = 1, 2, 3, 4

`source_polynomials.py` builds A_n and D_N B_n in Z[X] from the displayed
formulas, divides by Omega_n and by X^(M_n) with zero remainder, and obtains
all coefficients of U_n and V_n. It confirms the printed degree table

| n | 1 | 2 | 3 | 4 |
| --- | --- | --- | --- | --- |
| K_n | 587 | 2264 | 5032 | 8891 |
| W_n | 333 | 1315 | 2944 | 5220 |
| deg D_N | 72 | 278 | 628 | 1102 |
| deg Omega_n | 25 | 94 | 219 | 380 |

together with deg V_n = W_n - 1 and leading coefficients (-1)^n. It expands
F(1/q) from the divisor function and checks that U_n(1/q) F(1/q) - V_n(1/q)
has no coefficient below q^(K_n - W_n) and that the next twelve coefficients
equal those of the positive source expression. At 31/4, 3 and 7/2 it evaluates
U_n and V_n exactly: U_n(a/b) has reduced denominator b^(W_n) and V_n(a/b) has
reduced denominator b^(W_n - 1). The receipt stores every coefficient of U_n
and V_n (decimal strings, lowest degree first; the largest has 151 bits) and a
SHA-256 digest of each list. The earlier high-precision real evaluations
mentioned in the paper are separate and are not rerun here.

## Cyclotomic content of the coefficient pencil

`cyclotomic_content.py` builds alpha_m and beta_m for m <= 14 and studies
H_N(Y; p) = det(alpha_(i+j) Y - beta_(i+j)). For each of the 76 pairs
1 <= N <= 8, 1 <= d <= max(8, 2N - 2) it records the assignment bound
e_(N,d), an optimal assignment, integer row and column potentials, the value
Y0 and the nonzero residue Gamma_(N,d)(Y0) modulo Phi_d. It computes that
residue three ways (the minimum-cost subset recurrence, the determinant of the
reduced matrix, and exact division of the full polynomial H_N(Y0; p) by
Phi_d^(e_(N,d))) and requires agreement. It confirms the example N = 2, d = 1
(entry valuations (0 2; 2 5), e = 4, Gamma(0) = -9). For N <= 5 it computes
H_N(Y0; p) for Y0 = 0, ..., N and their monic gcd in Q[p], and certifies by a
gcd computation modulo a prime that no further factor divides all of them. The
contents are the five printed factorisations. The receipt records the degree
and SHA-256 digest of every full determinant it computed and the digests of
alpha_m and beta_m. The 76 residues, assignment bounds and values Y0 agree
exactly with the earlier SymPy computation in
[`computations/certificates/cyclotomic_residue_witnesses.json`](../../../computations/certificates/cyclotomic_residue_witnesses.json).
The certificates at ranks six to eight cover only the stated window of
cyclotomic indices.

## Sign of the main term at 31/4

`main_term_31_4.py` computes W_n exactly from a totient sieve for
1 <= n <= 400, encloses log 4 and log 31 by artanh series, and checks that
K_n log 4 - (K_n - W_n) log 31 is negative for each of these n. It confirms the
printed values -58.478, -10.280, -4.297 and -3.863 of this main term divided by
n^2 at n = 1, 10, 100, 400, and the printed limit C1 log 4 - C0 log 31 =
-3.718... It makes no statement for n > 400.

## Hankel q-order and leading coefficient for N <= 7

`hankel_qorder.py` expands Zudilin's normalised moments v_m^* at x = z = 1
for 0 <= m <= 12 as exact integer power series in q through q^99, and forms
V_N^* = det(v_(i+j)^*) for 1 <= N <= 7. The moments are expanded twice, from
the hypergeometric sum and as alpha_m F(p) - beta_m in the coefficient
normalisation, and the determinant is computed twice, by expansion over column
subsets and by fraction-free elimination with every division checked exact;
both pairs must agree. The orders are 0, 1, 5, 14, 30, 55, 91 and the leading
coefficients 1, 6, 108, 4320, 324000, 40824000, 8001504000, equal to
N(N-1)(2N-1)/6 and (N!)^2 (N+1)!/2^N. The program also applies
D_j = prod_(r<j) (I - q^r S) to the moment sequence and confirms the row identity
D_j v_(j+l)^* = (-1)^j (j+1)^2 (j+2)/2 q^(j(j+1)/2 + jl) + ... for
0 <= j, l <= 6 (row 1 has order l + 1 and coefficient -6 in every column), the
contribution of each hypergeometric summand at that degree, and that the
reversal is the unique permutation of least total entry order at each rank.
The receipt records the first eight coefficients from the leading term at each
rank and a SHA-256 digest of each truncated determinant. The all-rank
statement is the paper's proof; this computation covers seven ranks.

## Numerical direction search

`direction_search.py` is the public adaptation of the research probe that
first ranked the directions. It evaluates the ratio theta_star = C0 / C1 from
equations (25) and (26) of Wadim Zudilin's 2004 paper for every primitive
integer direction in his cone whose four entries are at most 30. The formulas,
admissible cone, and permutation observation remain attributed to Zudilin.
For source custody, the pre-publication probe from which this copy was adapted
has SHA-256
`d0cd58b0a72dc5bcc98fb237b2033962fb66cf18157d281bb7758852f416fef2`.
It needs mpmath, pinned in `requirements.txt`:

```bash
python3 -m venv /tmp/erdos1049-direction-search
/tmp/erdos1049-direction-search/bin/python -m pip install \
  -r research/experiments/erdos1049/requirements.txt
/tmp/erdos1049-direction-search/bin/python \
  research/experiments/erdos1049/direction_search.py \
  --bound 30 \
  --output research/experiments/erdos1049/receipts/direction-search-bound30.json \
  --check
```

Without `--check` the command rewrites the receipt. The search visits 37,533
primitive directions. The cone inequalities, primitive normalization, rational
breakpoints, step-function weights, and `C1` are computed exactly. The
trigamma values and pi in `C0` are evaluated with mpmath 1.3.0 at 30 decimal
digits, so this receipt is numerical evidence for the ordering, including the
tied leading directions `(14,12,14;27)` and `(15,12,13;26)`. The interval
certificate for the same box is `parameter_box.py` above.

## Related computations elsewhere in the repository

The sixteen shifted and unshifted moment determinants, their coefficient
lists, and the 256-summand interval certificate live in the repository-root
[`computations/`](../../../computations/README.md) directory; see
[`HANKEL_SUITE.md`](HANKEL_SUITE.md).
