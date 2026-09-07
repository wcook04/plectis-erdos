# Erdős #1049: a positive discrete measure for Zudilin's 2016 normalized Hankel rows

Status: ordinary complete proof of a two-sided fixed-`q` size theorem for the
*2016* normalized Hankel family.  The algebraic core is in
`ZudilinHankelPositiveMeasure.lean`.  Focused `lean_fast_build --jobs 2
ErdosProblems.Erdos1049.ZudilinHankelPositiveMeasure` returned **75** this wave
(queued as `cf_2de33731e12b446c8c46`); not kernel evidence until that future
terminates.  This is not a 2004 construction, not a rational-base irrationality
theorem, and not a proof at `3/2`.

Collision.  The exact formal order `ord_q V_N^* = B_N` and leading coefficient
`C_N = (N!)²(N+1)!/2^N` are already registered
(`res:zudilin-sharp-qorder`, `ZudilinSharpHankelCoefficient.lean`).  The
argument below *recovers* those two formal facts as the `q→0` degeneration of
a positive-moment representation.  What is new is the representation itself,
strict positivity of every Hankel determinant at fixed `0<q<1`, and the
residual bound `log(V_N/(C_N q^{B_N})) = O_q(N)`.

## 1. Statement

Fix `0<q<1`.  Write `(z;q)_m = ∏_{r=0}^{m-1}(1-z q^r)` and `P = (q;q)_∞ > 0`.
Zudilin's normalized rows at `x=z=1` (2016, eq. (6) after Lemma 1) are

```
v_m = (q;q)_m³ ∑_{t≥0} q^{(m+1)t} (q^{t+1};q)_m / (q^{m+t+1};q)_{m+1},   m ≥ 0.
```

Let `V_N = det(v_{i+j})_{0≤i,j<N}`, `B_N = N(N-1)(2N-1)/6`, and
`C_N = (N!)²(N+1)!/2^N`.  Write `c_k = (k+1)²(k+2)/2`, so `∏_{i<N} c_i = C_N`.

**Theorem A.** There are weights `ω_k > 0` supported at every point `q^k` with
`v_m = ∑_{k≥0} ω_k (q^k)^m`.  In particular `V_N > 0` for every `N≥1`.  Moreover
there are constants `0 < c_q ≤ C_q < ∞`, independent of `N`, such that

```
c_q^N C_N q^{B_N} ≤ V_N ≤ C_q^N C_N q^{B_N},
```

hence `log(V_N / (C_N q^{B_N})) = O_q(N)`.

This is a size theorem for this determinant family.  It does not enlarge the
rational-base irrationality region and does not prove `F(3/2)` irrational.

## 2. Generating function

For `|w|<1` define

```
G_q(w) = 1/(w;q)_∞³  ∑_{t≥0}  w^t / (q;q)_t  · (q^t w²;q)_∞ / (q^t w;q)_∞².
```

The series converges normally on compact subdiscs of the unit disc: if `|w|≤r<1`
then each denominator product is bounded away from zero uniformly in `t`, the
numerators are bounded, `(q;q)_t ≥ P`, and the summands are `O(r^t)`.

Set `w = q^{m+1}`.  The three identities

```
(q;q)_m = P / (w;q)_∞,
(q^{t+1};q)_m = P / ((q;q)_t (q^t w;q)_∞),
1/(q^{m+t+1};q)_{m+1} = (q^t w²;q)_∞ / (q^t w;q)_∞
```

are the splitting `(q;q)_∞ = (q;q)_m (q^{m+1};q)_∞` and its translates.  They
give `v_m = P⁴ G_q(q^{m+1})`.  Write `G_q(w) = ∑_{k≥0} γ_k(q) w^k`.

## 3. Nonnegative coefficients

For each `t≥0` put `a = q^{t/2}` and `b = q^{(t+1)/2}`.  Splitting even and odd
factors yields the algebraic identity

```
(q^t w²;q)_∞ = (a w;q)_∞ (-a w;q)_∞ (b w;q)_∞ (-b w;q)_∞,
```

because `(z²;q)_∞ = (z;q²)_∞ (q z²;q²)_∞` rearranges into those four products.
Consequently the `t`-th summand of `G_q` is

```
(a w;q)_∞/(w;q)_∞ · (b w;q)_∞/(w;q)_∞ · (-a w;q)_∞ (-b w;q)_∞ / ((w;q)_∞ (q^t w;q)_∞²).
```

Every factor has nonnegative Taylor coefficients in `w`, for `0<q<1`:

* `(c w;q)_∞ / (w;q)_∞ = ∑_{k≥0} (c;q)_k/(q;q)_k w^k` for `0≤c≤1` (q-binomial
  series; equivalently the recurrence `(1-q^k) a_k = (1-c q^{k-1}) a_{k-1}` with
  `a_0=1`).  Lean: `qBinomialRatioCoeff_nonneg`.
* `(-c w;q)_∞ = ∏ (1+c w q^j)` and `1/(w;q)_∞` are visibly nonnegative.

Thus every `γ_k(q) ≥ 0`.  The `t=0` term is strictly positive in every degree
(next paragraph), so `γ_k(q) > 0` and `γ_0=1`.

The weights are `ω_k = P⁴ γ_k(q) q^k > 0`.  Their sum is `P⁴ G_q(q) = v_0 < ∞`.

## 4. Coefficient comparison

Write `Q = (√q;q)_∞ > 0`, `T = (-1;q)_∞² < ∞`.  The claim is
` (Q/3) c_k ≤ γ_k(q) ≤ T(P^{-4}+P^{-6}) c_k `.

Coefficients of `1/(w;q)_∞` lie between `1` and `P^{-1}`.  Coefficients of either
q-binomial ratio lie between `0` and `P^{-1}`.  The ratio with `c=√q` has
coefficients at least `Q`, because `(√q;q)_k / (q;q)_k ≥ (√q;q)_∞`.

At `t=0` the first ratio is `1`.  Convolution of a series with coefficients
`≥ Q` against `1/(w;q)_∞³ ≥ 1/(1-w)³` produces the lower bound
`Q \binom{k+3}{3}`, since `∑_{j=0}^k \binom{j+2}{2} = \binom{k+3}{3}`.  The two
negative-sign products contribute only extra nonnegative factors.

For the matching upper bound, bound four factors coefficientwise by `P^{-1}`
against `1/(1-w)` and the remaining product by the sum of its coefficients at
`w=1`, which is at most `T`.  This gives
`[w^k](t=0) ≤ T P^{-4} \binom{k+3}{3}`.

For `t≥1`, two ratios and one `1/(w;q)_∞` contribute at most
`P^{-3}\binom{k+2}{2}`; the remaining factors have coefficient-sum at most
`T P^{-2}` because `(q^t;q)_∞ ≥ P`; including `(q;q)_t^{-1} ≤ P^{-1}` and
summing the shifts `w^t` produces `T P^{-6} \binom{k+2}{3}`.

Finally `\binom{k+3}{3}/c_k = (k+3)/(3(k+1)) ∈ [1/3,1]`, so the comparison with
`c_k` follows.  Lean checks `coeff_G0_eq_zudilinMomentRowC` (the `q=0` case,
where equality holds) and `zudilinMomentRowC_shift_le`.

## 5. Gram expansion and size

Finite Cauchy–Binet, then entrywise convergence of truncated moment matrices,
gives

```
V_N = ∑_{0≤k₀<⋯<k_{N-1}} (∏_i ω_{k_i}) ∏_{i<j} (q^{k_i} - q^{k_j})².
```

All summands are nonnegative; the strictly increasing tuple is nonempty, so
`V_N > 0`.  Lean checks the finite `N`-atomic identity
`det(momentHankel ω v) = (∏ ω) det(vandermonde v)²` and the resulting positivity
on `ℝ` for positive weights and injective nodes.

The diagonal tuple `k_i = i` contributes exponent
`∑_i i + 2 ∑_i i(N-1-i) = B_N` (Lean: `sum_diag_zudilinHankelExponent`) and
row-coefficient product `C_N` (Lean: `prod_zudilinMomentRowC`).  The Vandermonde
correction is `∏_{d=1}^{N-1} (1-q^d)^{2(N-d)} ≥ P^{2N}`.  Together with the
lower bound on `γ_k` this yields `V_N ≥ (P^6 Q/3)^N C_N q^{B_N}`.

For the upper bound write `k_i = i+λ_i` and drop the ordering `λ_0 ≤ ⋯ ≤ λ_{N-1}`.
Then `∏_{i<j}(q^{k_i}-q^{k_j})² ≤ q^{2 ∑_i k_i (N-1-i)}` and
`c_{i+λ}/c_i ≤ (λ+1)³`.  Summing independently in the `λ_i` against the geometric
majorant `∑ (λ+1)³ q^λ = (1+4q+q²)/(1-q)⁴` produces a constant `C_q` with
`V_N ≤ C_q^N C_N q^{B_N}`.

## 6. Formal leading term (already registered)

Specialising the products in `G_q` at `q=0` gives
`G_0(w) = (1+2w)/(1-w)^4`, whose coefficients are `c_k`.  The Gram sum is
locally finite in `q`; the unique minimising tuple is `k_i=i`, with exponent
`B_N` and coefficient `C_N`.  This is an alternative proof of the already
registered formal theorem.  It does not replace
`ZudilinSharpHankelCoefficient.lean`, whose associated-graded route remains
the Lean authority for the formal coefficient, still conditional on row
`j≥3`.

A family with the same formal order and leading coefficient can still have
residual `log R_N = -Θ(N³)` (example: `C_N q^{B_N} (1-q)^{N³}`).  Formal
equality is therefore not a fixed-`q` lower bound.  Theorem A supplies the
missing analytic information for the *actual* family.

## 7. Boundary

This note uses only the 2016 normalized rows.  It does not consume Zudilin 2004
forms, does not claim a best-known status against Zudilin 2016 or Koizumi–Yokoi
August 2026, and does not prove irrationality at `3/2`.

## 8. R3 candidate (not a paper theorem)

Type B r3 returns a claimed sharper fixed-`q` asymptotic

```
V_N ~ K(q) C_N q^{B_N} (q;q)_∞^{2N} N^{-8 F(1/q)},
```

with `D(w) = P^4 (1-w)^4 G_q(w)`, `D(1)=3`, `D'(1)=2+8F(1/q)`, and a geometric-lattice Gram limit.  Collision with the landed formal core: `C_N`, `B_N`, and `G_0(w)=(1+2w)/(1-w)^4` are already registered; the new content is the power-law and Pochhammer factors, which would strengthen the `O_q(N)` remainder of Theorem A.  At `q=2/3` the exponent is `F(3/2)`, which is a relation, not an irrationality proof.

Numerical corroboration: `Erdos1049/scripts/check_r3_assimilation_probes.py --mode polar --quick` matches the sign and rough magnitude of `-8F(1/q)`.  Koizumi–Yokoi arXiv:2608.26918v1 (annex absent) constructs integer-base Apéry-type approximations to other `q`-series; its abstract does not state this Hankel asymptotic.  Novelty remains unconfirmed.  The claim is not inserted in the live short note.  This r3 wave did not re-run Lake; the combinatorial core already exited 0 in r2.
