# Erdős #1041 for collinear zeros

## Result

The natural theorem is quantitative, exact, and stronger than the Erdős
subcase.  Put

\[
  C_n=\frac{1}{2^{n-1}\cos^n(\pi/(2n))}.
\]

> **Sharp diameter theorem.** Let `f` be a monic polynomial of degree `n≥2` whose
> zeros are collinear, and let `D` be the diameter of the zero multiset.  Then
> two zeros can be joined by a straight segment of length at most `D` on which
> \[
>   |f|\le C_n(D/2)^n
>   =\frac{(D/2)^n}{2^{n-1}\cos^n(\pi/(2n))}.
> \]

Equivalently, this solves the associated critical-height extremal problem:
every monic real-rooted degree-`n` polynomial of root diameter `D` has a real
critical point `c` with

\[
 |f(c)|\le
 \frac{(D/2)^n}{2^{n-1}\cos^n(\pi/(2n))},
\]

and the constant is best possible.  For simple roots, take the maximum point
on the selected adjacent gap; Rolle interlacing makes it one of the `n-1`
real critical points.  A repeated root gives critical value zero immediately.

The constant is sharp in every degree.  Equality is attained by the affine
images of the roots of `T_n`, scaled so that their two extreme roots have
distance `D`.  If `D<2`, then the displayed bound is strictly below `1`, so the
segment has length below `2` and lies in the open lemniscate.  For `n≥3`, the
constant itself is already below one, so the lemniscate conclusion remains
strict even at `D=2`.  Indeed `r_n≥1/√2`, hence
`2^(n-1)r_n^n≥2^(n/2-1)`, with strict inequality above one for `n≥3`.

In fact the full path conclusion extends to the closed-disk boundary for
`n≥3`.  If a root is repeated, use the constant path between two copies.  If
all roots are distinct, three or more ordered collinear roots make every
adjacent gap strictly shorter than the total diameter `D≤2`; meanwhile the
sharp level is already strictly below one.  Degree two is the exact exception:
the roots `-1,1` give both length `2` and level `1`.

The formula recovers both previously visible sharp low-degree constants.  For
`n=2`, `C_2=1`, so the level is exactly `(D/2)^2`.  For `n=3`,
`r_3=√3/2` and

\[
 C_3(D/2)^3=\frac{D^3}{12\sqrt3},
\]

which is the independently derived exact cubic height.  Thus the alternation
theorem is not merely compatible with the quadratic and cubic computations;
it is their single all-degree continuation.

Relative to the clean resultant level `(D/2)^n/2^(n-2)`, the exact improvement
factor is

\[
 \frac{1}{2r_n^n}.
\]

It equals one at `n=2`, is strictly smaller thereafter, and tends to `1/2` as
`n→∞`.  The constrained comparison therefore recovers an asymptotic factor of
two over the clean Chebyshev--Hadamard/product route.

Translate the midpoint of the extreme zeros to the origin, rotate their line
to the real axis, and then scale by `R=D/2` for the determinant estimate.
Translation and rotation preserve the polynomial-value moduli and lengths;
the scale `R` is retained explicitly rather than normalised away.

The original Erdős hypothesis is an immediate corollary:

Let

\[
  f(z)=\prod_{j=1}^n(z-z_j)
\]

be monic, with every zero in the open unit disk.  If the zeros are collinear,
and `n≥2`, then two zeros can be joined by a straight segment of length strictly less
than `2` lying entirely in the open lemniscate `|f|<1`.

This is a complete unconditional subcase of Erdős #1041.  It is new to this
corpus; no claim of literature priority is made.

This does not contradict the corpus's exact cubic obstruction to universal
root chords.  The polynomial `z^3-(99/100)^3` has non-collinear roots and every
root-pair midpoint escapes the unit lemniscate.  The new proof spends exactly
the hypothesis absent there: a real ordering of all roots supplies `n-1`
adjacent gaps whose nonzero signs alternate, which is the input that forces
the comparison-polynomial root count.

## Exact sharp proof by constrained Chebyshev alternation

Repeated zeros are immediate: two copies of the repeated zero are joined by
the constant path.  We may therefore assume that the zeros are distinct.

Apply a rigid motion to the variable and multiply the polynomial by a
unimodular constant.  This preserves Euclidean lengths, critical-value
moduli, and lemniscate containment.  Send the midpoint of the two extreme
zeros to the origin.  The zeros may then be
written as real numbers

\[
  -D/2=x_1<x_2<\cdots <x_n=D/2,
\]

so every transformed zero has modulus at most `R=D/2`.  Scale once more and
write `y_i=x_i/R`.  The resulting monic polynomial `q` has roots

\[
 -1=y_1<y_2<\cdots<y_n=1,
\]

and `|f(x)|=R^n|q(x/R)|` on the root interval.

More explicitly, if the extreme zeros are `m±Re^{iθ}`, the normalized
polynomial is

\[
 q(w)=R^{-n}e^{-in\theta}f(m+Re^{i\theta}w).
\]

This formula makes both facts used below literal: `q` is monic, and
`|f(m+Re^{iθ}w)|=R^n|q(w)|`.  It also shows that no unrecorded real-coefficient
assumption is being made: after this normalization all roots of the monic
polynomial `q` are real, hence all of its coefficients are real.

Set `r_n=cos(π/(2n))` and consider the monic comparison polynomial

\[
 q_*(x)=\frac{T_n(r_nx)}{2^{n-1}r_n^n}.
\]

The leading coefficient of `T_n` is `2^{n-1}`, so `q_*` is monic.  Moreover,
`T_n(r_n)=cos(n·π/(2n))=0`, and parity gives `T_n(-r_n)=0`; hence
`q_*(-1)=q_*(1)=0`.  Since `|r_nx|≤1` on `[-1,1]`,

\[
 |q_*(x)|\le C_n=\frac1{2^{n-1}r_n^n}.
\]

For each adjacent-root interval `[y_i,y_{i+1}]`, choose a point `c_i` where
`|q|` is maximal.  The signs of `q(c_i)` alternate with `i`.  Suppose, for a
contradiction, that every one of these `n-1` gap maxima is strictly larger
than `C_n`.  At every `c_i`, the difference

\[
 h=q-q_*
\]

has the same sign as `q(c_i)`, because `|q_*(c_i)|≤C_n<|q(c_i)|`.  Thus `h`
has a zero strictly between every consecutive pair `c_i,c_{i+1}`.  It also
vanishes at `-1` and `1`, since both `q` and `q_*` do.  These are `n` distinct
real zeros.  But the leading terms of the two monic degree-`n` polynomials
cancel, so `deg h≤n-1`; and `h` is nonzero at each `c_i`.  This is impossible.

Therefore some adjacent gap satisfies `|q|≤C_n` throughout.  Scaling back
gives

\[
 |f|\le R^nC_n
 =\frac{(D/2)^n}{2^{n-1}\cos^n(\pi/(2n))}.
\]

The chord length is at most the diameter `D`.

For sharpness, take the roots

\[
 y_k=\frac{\cos((2k-1)\pi/(2n))}{r_n},\qquad 1\le k\le n.
\]

They are precisely the roots of `q_*`; their extremes are `±1`.  Between
successive roots, `q_*` reaches `±C_n` at the scaled Chebyshev extrema
`cos(kπ/n)/r_n`.  Hence every adjacent gap has height exactly `C_n`, proving
that no smaller universal constant is possible.

This completes the sharp diameter theorem and, for `D<2`, the collinear
Erdős conclusion.

## Independent resultant proof of a clean algebraic corollary

The following argument avoids trigonometric constants and gives the slightly
weaker but very clean level `(D/2)^n/2^(n-2)`.  It is useful as an independent
certificate and is the portion currently closest to kernel-complete Lean.
For comparison, `r_n^n≥1/2`: the function
`s ↦ s log(cos(π/(2s)))` is increasing for `s≥2`, since after putting
`x=π/(2s)` its derivative is `log(cos x)+x tan x>0`.  Thus the sharp constant
is always at most the clean one, with equality only at `n=2`.

The standard resultant identity gives, for the `n-1` critical points `c_k`,

\[
 \prod_{k=1}^{n-1}|f(c_k)|
   =\frac{\prod_{i<j}|x_i-x_j|^2}{n^n}.
\]

For completeness, the needed interval-Fekete estimate is Hadamard's
determinant inequality in a Chebyshev basis.  Put `y_i=x_i/R`, and let `T_j`
be the Chebyshev polynomial of degree `j`.  Form

\[
  B=(T_j(y_i))_{1\le i\le n,\ 0\le j<n}.
\]

Every entry of `B` has absolute value at most one, so every row has squared
Euclidean norm at most `n`.  The leading coefficient of `T_0` is one and that
of `T_j` for `j\ge1` is `2^{j-1}`.  Triangular column reduction from the
Chebyshev basis to the monomial basis therefore gives

\[
  |\det B|
   =2^{(n-1)(n-2)/2}|\det V|.
\]

Hadamard now yields the strengthened Vandermonde estimate

\[
  \prod_{i<j}|x_i-x_j|^2
  \le
  R^{n(n-1)}\frac{n^n}{2^{(n-1)(n-2)}}.
\]

Substitution in the resultant identity gives

\[
  \prod_{k=1}^{n-1}|f(c_k)|
  \le \frac{R^{n(n-1)}}{2^{(n-1)(n-2)}}
  =\left(\frac{R^n}{2^{n-2}}\right)^{n-1}.
\]

At least one critical point `c` therefore satisfies

\[
  |f(c)|\le \frac{R^n}{2^{n-2}}.
\]

Rolle interlacing for a real-rooted polynomial puts exactly one critical point
in every interval `(x_i,x_{i+1})`.  Choose the adjacent pair whose interval
contains `c`.  On this interval `f` is real up to one constant unimodular
factor.  Its derivative has no zero except `c`; consequently `|f|` rises from
zero to `|f(c)|` and then falls to zero.  Thus

\[
  |f(x)|\le |f(c)|\le
  \frac{R^n}{2^{n-2}}
  =\frac{(D/2)^n}{2^{n-2}}
  \qquad (x_i\le x\le x_{i+1}).
\]

Finally, its two endpoints belong to a set of diameter `D`, so

\[
  |x_{i+1}-x_i|\le D.
\]

This proves the claim.

## Exact all-degree interval-Fekete refinement

The clean power of two above is convenient for formalization, but the same
argument admits a strictly stronger explicit constant.  Let

\[
 \Lambda _2=4,
 \qquad
 \frac{\Lambda _{n+1}}{\Lambda _n}
 =\frac{(n+1)^{n+1}(n-1)^{n-1}}{(2n-1)^{2n-1}}
 \quad(n\ge2).
\]

Equivalently,

\[
 \Lambda_n
 =4\prod_{k=2}^{n-1}
   \frac{(k+1)^{k+1}(k-1)^{k-1}}{(2k-1)^{2k-1}}.
\]

Then `Λ_n` is the exact maximum of
`prod_{i<j}|y_i-y_j|^2` over `n` points of `[-1,1]`.  Consequently the selected
adjacent chord may be taken at the sharper level

\[
 |f|\le
 R^n\left(\frac{\Lambda_n}{n^n}\right)^{1/(n-1)}.
\]

Here is a self-contained derivation of the exact constant.  Maximize the
Vandermonde product on the compact ordered chamber
`-1≤y_1≤...≤y_n≤1`.  A positive competitor exists, so a maximizer has no
collision; pushing the two extreme points outward shows that its endpoints
are `-1` and `1`.  The logarithm of the product is strictly concave in the
remaining coordinates.  Its critical equations are

\[
 \sum_{j\ne i}\frac1{y_i-y_j}=0 \qquad (1<i<n).
\]

For the monic root polynomial `q(x)=prod_i(x-y_i)`, these equations say that
`q''` vanishes at every interior root.  Comparing degrees and leading
coefficients gives

\[
 (x^2-1)q''(x)=n(n-1)q(x).
\]

Thus the unique maximizer is the Legendre--Lobatto configuration: the roots
of `(x^2-1)P'_{n-1}(x)`.  If `a_m` is the leading coefficient of the Legendre
polynomial `P_m`, the Legendre equation gives

\[
 \left((x^2-1)P'_m(x)\right)'=m(m+1)P_m(x).
\]

Taking the product of these derivatives at all roots computes the
discriminant.  Using
`a_m/a_{m-1}=(2m-1)/m` and cancelling adjacent terms yields exactly

\[
 \frac{\Lambda_{n+1}}{\Lambda_n}
 =\frac{(n+1)^{n+1}(n-1)^{n-1}}{(2n-1)^{2n-1}},
\]

with `Λ_2=4`.  Substitution for the Chebyshev--Hadamard estimate in the
resultant proof gives the displayed refined chord level.  This is the exact
discriminant input; the final geometric-mean selection can still have slack,
so no all-degree optimality claim is made for the resulting chord height.

## Exact cubic refinement

For `n=3` the interval Fekete constant is elementary and improves the clean
Chebyshev bound.  The normalized roots are `-1,t,1`, with `|t|≤1`, so their
squared Vandermonde is

\[
  4(1-t^2)^2\le4.
\]

The two critical values therefore satisfy

\[
  |f(c_1)f(c_2)|\le \frac{4R^6}{27},
\]

and one adjacent root chord has height at most

\[
  \frac{2R^3}{3\sqrt3}
  =\frac{D^3}{12\sqrt3}.
\]

This cubic constant is sharp: for the equally spaced roots `-R,0,R`, the two
critical points are `±R/√3` and both critical-value moduli are exactly
`2R^3/(3√3)`.

For `n=2`, after the same rigid motion the polynomial is

\[
  f(x)=(x-R)(x+R)=x^2-R^2.
\]

Its modulus on the root chord is maximal at the midpoint and equals
`R^2=(D/2)^2`; the extra Chebyshev denominator is `2^0=1`.  Thus the theorem's
constant is exactly attained in degree two.

## Why the critical gap must be selected

The stronger statement “every adjacent-root segment is safe” is false already
for a rational cubic.  Take the three roots

\[
  -\frac{19}{20}<\frac9{10}<\frac{999}{1000}.
\]

On the segment joining the first two, the point `x=-1/3` gives

\[
 \left(x+\frac{19}{20}\right)
 \left(x-\frac9{10}\right)
 \left(x-\frac{999}{1000}\right)
 =\frac{5471893}{5400000}>1.
\]

Thus the discriminant product is doing real selection work: it chooses a
subunit critical gap, not an arbitrary adjacent pair.  The exact evaluation is
also stated in Lean as `unsafeAdjacentGapCubic_not_in_openLemniscate`.

## Formal boundary

`SharpCollinearAlternation.lean` isolates and kernel-checks the new proof's
load-bearing step: strict absolute-value domination preserves signs, opposite
polynomial values give an intervening real root, two shared endpoint zeros
plus all intervening sign changes exceed the degree of a nonzero difference
polynomial, and hence a same-degree monic comparison must dominate at some
alternating peak.  The exact target passed through `lean_fast_build.py
--jobs 2`; its public endpoint is
`SharpCollinearAlternation.exists_peak_le_of_monic_comparison`.

`SharpCollinearChebyshev.lean` kernel-checks the concrete comparison polynomial

```text
C ((2 : ℝ)^(n-1))⁻¹ * (Chebyshev.T ℝ n).scaleRoots
  (cos (π/(2*n)))⁻¹
```

whose evaluation is exactly `q_*`.  The same exact build checks its monicity,
the two endpoint zeros, the uniform interval bound, and the concrete theorem
`SharpCollinearChebyshev.exists_peak_le_comparisonBound`.  Thus the entire
contradiction-by-alternation mechanism and its scaled-Chebyshev instantiation
are Lean-verified.  The equality configuration itself is proved analytically
above from the standard Chebyshev extrema; formalising those node locations is
an optional sharpness cross-check, not a missing estimate or a premise of the
upper bound.

What is not yet packaged as one end-to-end Lean declaration is the routine
supplier that chooses a maximum in every adjacent root gap and the affine
normalisation from a complex polynomial with collinear roots to a monic real
polynomial with extreme roots `-1,1`.  Those steps are explicit in the proof
above; the hard alternation and comparator steps are the checked formal
boundary.

`CollinearRootCase.lean` formalizes the Chebyshev evaluation-matrix column
change, the refined interval Vandermonde/Hadamard estimate, the finite
geometric-mean selection, the peak-controlled segment consumer, and the two named conclusions
`CollinearScaleCriticalFamily.exists_diameter_chord` and
`CollinearScaleCriticalFamily.exists_erdos1041_chord`.  Thus the exact constant
`(D/2)^n / 2^(n-2)`, its strict conversion when `D<2`, and the final
straight-segment conclusion all occur inside Lean once the corresponding
critical-family product bound is supplied.

The remaining library-facing seam is to instantiate
`CollinearScaleCriticalFamily` from a monic polynomial whose roots are
collinear using the resultant identity and real-root interlacing.  It requires
no new mathematical estimate.

The intended supplier uses existing Mathlib entry points rather than a new
axiom: `Matrix.det_vandermonde` for the root-difference product,
`Polynomial.resultant_eq_prod_eval` together with `Polynomial.resultant_deriv`
for the critical-value product, and the polynomial Rolle/root-count lemmas in
`Mathlib.Analysis.Calculus.LocalExtr.Polynomial` for exactly one derivative root
per adjacent gap.  `CollinearCriticalFamily.exists_straightSegment_solution`
is the already-written fan-in theorem those ingredients must instantiate.

## Reproducible computation

The deterministic falsifier/exact-arithmetic companion is
`scripts/check_erdos1041_collinear_chebyshev.py`.  The checkpoint run was

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_collinear_chebyshev.py \
  --max-n 10 --samples 20000 --seed 1041
```

It checks the Chebyshev exponent exactly, stress-tests the determinant bound,
proves in rational arithmetic that the Legendre--Lobatto discriminants agree
with the displayed all-degree recurrence through the requested degree,
stress-tests both the Vandermonde inequality and the minimum adjacent-gap
height on 20,000 normalized random configurations in every degree
`2≤n≤10` (180,000 configurations total), checks equality for the scaled
Chebyshev roots in every one of those degrees, and verifies both the exact
cubic identity and the rational unsafe-gap scope guard.  It returned `PASS`.
These computations are falsification and discovery evidence; the constrained
alternation argument above is the proof of the sharp theorem.
