<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Transcendence along divisibility chains

For coprime integers `a > b >= 1` and every infinite chain
`n_1 | n_2 | n_3 | ...` of distinct positive integers, the number

```
X = sum_j 1/((a/b)^(n_j) - 1)
```

is transcendental. This is Theorem 6.5 of the synthesis paper
[Reading Eight Erdős Problems Together](../../../paper/synthesis/optimal-sparse-perturbations.pdf)
([source](../../../paper/synthesis/optimal-sparse-perturbations.tex)), Section 6.2.
It removes the hypothesis `a^2 > b^3` from Theorem 6.3(a) of that paper and
strengthens its conclusion from irrationality to transcendence, so every chain
at bases 4/3 and 5/4 is covered, including the chains at base 4/3 whose ratios
are 2 except for infinitely many 3s. At rational bases it also gives
Theorem 6.3(b) without Mahler's method.

**Status.** Ordinary proof. The p-adic Subspace Theorem (Schmidt's theorem in
Schlickewei's p-adic form, in the statement of Bilu's Bourbaki survey,
Theorem 2.3) is an external premise. Nothing here is checked in Lean, and no
Comparator or Palomar row states it. The script in this directory checks the
finite bookkeeping of the proof in exact rational arithmetic; those checks are
not the proof.

## Why the earlier argument stopped and what replaces it

Write `rho = b/a`, `D_j = a^(n_j) - b^(n_j)` and let `S_j` be the sum of the
first `j` terms. Because the chain is nested, `D_j S_j` is an integer. The proof
of Theorem 6.3(a) compares this one approximation with the whole tail
`X - S_j`, which is about `rho^(n_(j+1))`. At base 4/3 with ratio
`n_(j+1)/n_j = 2` the cleared tail `D_j (X - S_j)` grows like `(9/4)^(n_j)`,
so that comparison cannot succeed.

The new proof keeps the first `K - 1` terms of the tail as separate
coordinates. With `N = n_j` and `M = n_(j+1)`, the tail is
`sum_k c_j(k) rho^(kM)`, where `c_j(k)` counts the later chain terms dividing
`kM`, so `1 <= c_j(k) <= 1 + log2 k`. The integer vector

```
Y_j = (H, H rho^N, a^((K-1)M) D_j S_j, H rho^M, H rho^(N+M), ..., H rho^((K-1)M), H rho^(N+(K-1)M)),
H = a^(N+(K-1)M),
```

has every coordinate except the third composed of primes dividing `ab`. By the
product formula those coordinates contribute nothing to the product of
absolute values over the archimedean place and the primes dividing `ab`, and
the remaining product is at most `C_K a^N rho^(KM)`. When `K r log(a/b) > log a`
for a ratio `r` that occurs infinitely often (`K = 3` at base 4/3 with
`r = 2`), this is a negative power of the height of `Y_j`, and the Subspace
Theorem puts infinitely many `Y_j` in one proper rational subspace. A fixed
relation `lambda . Y_j = 0` is then impossible. With `z = rho^(n_j)`, dividing
by `H` turns it into `Q(z) = lambda_3 (1 - z) E_j`, where `Q` is a fixed
polynomial of degree less than `Kr` and `0 < E_j <= C_K z^(Kr)`. As `z -> 0`
this forces `Q = 0`, then `lambda_3 = 0` because `E_j > 0`, and then
`lambda = 0` because the exponents `0, 1, kr, 1 + kr` of `Q` are distinct when
`r >= 2`. If no ratio occurs infinitely often, the ratios tend to infinity
along a subsequence and `K = 1` suffices.

The identity `sum_j z^(2^j)/(1 - z^(2^(j+1))) = z/(1 - z)` shows why the
ratios must be at least 2. Its cleared partial sums are again integers; its
tail begins at the exponent of the cleared denominator itself, two coordinates
coincide, and the value is rational.

## Exact checks

From the repository root:

```sh
python3 research/experiments/chain_transcendence/chain_bookkeeping.py
python3 research/experiments/chain_transcendence/chain_bookkeeping.py --json /tmp/chain-bookkeeping.json
python3 research/experiments/chain_transcendence/test_chain_bookkeeping.py
```

[`chain_bookkeeping.py`](chain_bookkeeping.py) checks, at every listed index
`j` and with the least admissible `K`:

- `D_j S_j` is a positive integer and equals its divisor-count expansion
  `sum_(m <= N) #{i <= j : n_i | m} a^(N-m) b^m`;
- every coordinate of `Y_j` except the third is composed of primes dividing
  `ab`;
- with `X` replaced by a truncation whose omitted terms cannot divide
  `(K-1)M`, the identity `L(Y_j) = H (1 - rho^N) E_j` holds exactly, and
  `0 < E_j <= (K/(1-rho) + rho/(1-rho)^2) rho^(KM)`;
- the exponents `0, 1, kr, 1 + kr` (`1 <= k < K`) are distinct and below `Kr`,
  and `K r log(a/b) > log a` holds as an exact integer inequality;
- the logarithm of the product over places, divided by the logarithm of the
  largest coordinate, against the predicted limit
  `((1 - K r) + K r theta)/(1 + (K - 1) r)` with `theta = log b / log a`;
- the one-term quantity `log(D_j (X - S_j)) / n_j` used by the earlier
  argument, which is positive at base 4/3 with ratio 2.

The cases are bases 4/3, 5/4, 3/2, 9/7 and 2 with ratio words over `{2, 3}`
(ratio 3 at square indices, Fibonacci, Thue–Morse, constant 2) and one
factorial chain; [`results.json`](results.json) is the saved output. For
example, on the doubling chain at base 4/3 with `K = 3` the ratio is
`-0.04960` at `n_j = 256` against the predicted `-0.04902`, while the one-term
quantity is `+0.8109 = log(9/4)`. On the chain with ratio 3 at square indices
it is `-0.06160` at `n_j = 576` (`K = 2`, `r = 3`) against `-0.06128`.
The test file also checks that changing any one tail count makes `E_j` leave
its bound, that `K` below the threshold gives a positive exponent, and the
rational boundary identity.

These are finite checks of formulas that the proof uses. They verify neither
the Subspace Theorem nor any statement about infinitely many indices, and the
observed exponents at finite `n_j` only approach their limits.

## Literature consulted

The search ended on 26 September 2026. We did not find the theorem stated in
the literature. Novelty and significance are left to specialists.

- **The Subspace Theorem.** W. M. Schmidt, *Norm form equations*,
  Ann. of Math. 96 (1972), 526–551; H. P. Schlickewei, *Die p-adische
  Verallgemeinerung des Satzes von Thue–Siegel–Roth–Schmidt*, J. Reine Angew.
  Math. 288 (1976), 86–105. The statement used is Theorem 2.3 of Yu. F. Bilu,
  *The many faces of the subspace theorem*, Séminaire Bourbaki Exp. 967,
  Astérisque 317 (2008), 1–38 ([arXiv:0907.2098](https://arxiv.org/abs/0907.2098)):
  integer points, `||x|| = max |x_i|`, `|p|_p = 1/p`, linearly independent
  forms with algebraic coefficients at each place. J.-H. Evertse's Leiden
  lecture notes, Chapter 8, Theorem 8.7
  ([pdf](https://pub.math.leidenuniv.nl/~evertsejh/dio19-8.pdf)), state the
  same theorem with a constant factor. Schmidt's Lecture Notes in Mathematics
  1467 and Chapter 7 of Bombieri and Gubler were not consulted, so no theorem
  number from them is used.
- **P. Corvaja and U. Zannier**, *Some new applications of the subspace
  theorem*, Compositio Math. 131 (2002), 319–340. Theorem 4 shows that an
  S-integer has only finitely many sufficiently good approximations by a fixed
  linear combination of S-units, apart from vanishing subsums; the proof here
  is an instance of that method. Theorem 3 and Corollaries 3–5 treat lacunary
  series `sum a_i alpha^(m_i)` whose coefficient heights satisfy
  `sum_(i <= n) h(a_i) = o(m_n)`. As a power series in `rho` our sum has
  support all multiples of `n_1`, and as a sum over the chain its terms
  `rho^n/(1 - rho^n)` have height of order `n`, so those corollaries do not
  apply as stated.
- **J. H. Loxton and A. J. van der Poorten**, *Arithmetic properties of
  certain functions in several variables III*, Bull. Austral. Math. Soc. 16
  (1977), 15–47. Theorem 2 proves transcendence of lacunary power series along
  chains `u_h | u_(h+1)`. Theorem 4 (p. 38) treats sums of rational functions
  `phi(z^(n_h))` along a chain at algebraic points under a hypothesis of strong
  transcendence, uniform in the chain, on `f_k(z) = sum_(h >= k) phi(z^(n_h/n_k))`.
  With `phi(z) = z/(1 - z)` that hypothesis fails for unbounded ratios, since
  `(1 - z) f_k(z) - z` vanishes at 0 to order `n_(k+1)/n_k`. It was not checked
  for bounded ratios. A compactness argument over the bounded ratio words,
  combined with the natural boundary of each limiting function, appears to
  supply it; if it does, their theorem gives bounded-ratio chains at every
  algebraic base. This route was not written out. B. Adamczewski,
  *Mahler's method*, Documenta Math. Extra Volume Mahler Selecta (2019),
  95–122, Section 8.2, credits this paper with the extension of Mahler's method
  to infinite chains of functional equations.
- **K. F. Roth** (1955). For unbounded ratios the approximations `S_j` already
  contradict Roth's theorem along ratios with `r_j log(a/b) >= 3 log a`.
  At integer bases (`b = 1`) Roth's theorem covers every chain with ratio at
  least 3 infinitely often.
- **Mahler's method for constant ratios.** Ku. Nishioka, *Mahler Functions and
  Transcendence*, Lecture Notes in Math. 1631 (1996), used for
  Theorem 6.3(b); by the zbMATH review of Tanaka's paper, its Section 2.9
  presents the Loxton–van der Poorten chain reasoning (not consulted
  directly). T. Kanoko, T. Kurosawa and I. Shiokawa, Monatsh. Math. 157 (2009),
  323–334 (zbMATH 1194.11078), prove transcendence of
  `sum a_k/(R_(r^k) + b)` for integer binary recurrences and a fixed `r >= 2`,
  including a square discriminant, which contains the integer-base case
  `R_n = a^n - 1` with constant ratio. P.-G. Becker and T. Töpfer, Math. Nachr.
  168 (1994), 5–17; D. Duverney, T. Kanoko and T. Tanaka, Monatsh. Math. 137
  (2002), 115–128; T. Kurosawa, J. Number Theory 123 (2007), 35–58; and
  D. Duverney and Ku. Nishioka, Acta Arith. 110 (2003), 305–330, treat
  constant ratios (indices `c d^k + l` or `r^k`). T. Tanaka, Arch. Math. 78
  (2002), 202–209, proves transcendence of lacunary power series
  `sum alpha^(r_k)` when `r_(k+1)/r_k` tends to an integer `d >= 2` and
  `r_(k+1) >= d r_k - M`; their terms are single powers of `alpha`.
- **P. Bundschuh and A. Pethő**, *Zur Transzendenz gewisser Reihen*, Monatsh.
  Math. 104 (1987), 199–223 (zbMATH 0601.10025). By the review, Schmidt's
  simultaneous approximation theorem gives transcendence of series of
  rationals whose denominators come from recurrences whose characteristic
  polynomial is the minimal polynomial of a Pisot number, under divisibility
  and growth conditions. The denominators `a^n - b^n` with `b >= 2` have two
  roots greater than 1 and lie outside that setting. The paper itself was not
  consulted.
- **K. D. Nguyen**, *Transcendental series of reciprocals of Fibonacci and
  Lucas numbers*, [arXiv:2009.02446](https://arxiv.org/abs/2009.02446) (2020):
  a different application of the Subspace Theorem, for `sum 1/F_(n_k)` with
  `n_(k+1)/n_k >= c > 2` and no divisibility; ratio 2 is excluded there by
  Millin's identity. It does not treat rational bases.
- **Adamczewski and Bugeaud** (complexity of expansions, as surveyed in Bilu,
  Section 3): criteria for expansions in an integer, Pisot or Salem base with
  bounded digits. At an integer base our sum has coefficients `#{j : n_j | m}`, which
  are unbounded, so these criteria do not apply as stated.
- **P. Erdős**, *On the irrationality of certain series*, Math. Student 36
  (1968), 222–226: irrationality at integer bases for pairwise coprime `n_i`
  with `sum 1/n_i < infinity`. **V. Kovač and T. Tao**, arXiv:2406.17593v4:
  no treatment of divisibility chains. The Erdős problems page for #257,
  consulted on 26 September 2026, lists no result on chains.
- Not accessible and therefore not checked: Chapter 5 (pp. 172–187) of
  Corvaja and Zannier, *Applications of Diophantine Approximation to Integral
  Points and Transcendence* (Cambridge Tracts 212, 2018). Y. Bugeaud,
  *Linear Forms in Logarithms and Applications* (EMS, 2018): its table of
  contents has no chapter on the Subspace Theorem or on these series.

## Attribution and remaining questions

The argument was found on 26 September 2026 in AI-assisted readings of the
eight problem papers, independently in two sessions, and was re-derived and
checked step by step before it entered the paper. The Subspace Theorem is due
to Schmidt, with the p-adic extension due to Schlickewei; the method of
approximating an S-integer by S-units is due to Corvaja and Zannier.

The proof uses the rational base twice: the coordinates are rational integers
composed of primes dividing `ab`, and the height of an integer vector is its
largest coordinate. At an irrational algebraic base the partial sums lie in
`Q(t)` and their conjugates enter the height. That extension was sketched in
the originating session; it has not been checked and is not claimed. Chains
whose ratios are not eventually periodic therefore remain open at irrational
algebraic bases here, and supports that are not divisibility chains remain
open at rational bases. Neither #257 nor #1049 is settled.
