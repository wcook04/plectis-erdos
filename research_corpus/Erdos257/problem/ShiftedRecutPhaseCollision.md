# Shifted quotient recuts and the fractional phase

Status: exact deductions and an exact cross-target obstruction, 2026-08-20.
This note does not prove that the shifted remainder is subexponential.  It
combines the horizon monotonicity of `ShiftedQuotientComparatorProof.md` with
the phase coordinate of `FirstFailureGreedyBridge.md`.  The resulting
statement is quantitative: a genuine recut at rank (d) bounds the preceding
terminal remainder by the rank-(d) quotient coin.  Hence infinitely many
genuine recuts, at arbitrary ranks, already force the fatal mode to vanish.
The only remaining alternative is eventual pure extension.

## 1. The first-difference identity

Retain the notation

\[
 H_N=\left\lfloor\frac{2^N}{21}\right\rfloor,
 \qquad S_N=2\lfloor\sqrt N\rfloor+5,
 \qquad C_N=H_N-S_N,
\]

and let (x^{(N)}) be descending Boolean greedy for (C_N) with

\[
 q_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor.
\]

Write (r_N) for its terminal integer remainder.  Suppose that the first
difference between (x^{(N)}), padded by a final zero, and (x^{(N+1)})
occurs at rank (d\leq N).  By strict lexicographic increase,

\[
 x^{(N)}_d=0,
 \qquad x^{(N+1)}_d=1.                              \tag{1}
\]

The common prefix before (d) has old integer remainder

\[
 R_{N,d}=C_N-\sum_{e<d}x^{(N)}_e q_{N,e}.
\]

Let

\[
 F_{N,d}=\sum_{\substack{e<d\\e\mid N+1}}x^{(N)}_e,
 \qquad
 A_{N,d}=t_{N+1}+2S_N-S_{N+1}-F_{N,d},              \tag{2}
\]

where (H_{N+1}=2H_N+t_{N+1}).  The quotient pulse identity gives

\[
 R_{N+1,d}=2R_{N,d}+A_{N,d}                         \tag{3}
\]

as long as the two rows still have the same prefix.  Put

\[
 j_{N,d}=q_{N,d}-R_{N,d}.
\]

The old skip in (1) says (j_{N,d}\geq1).  The new take, together with

\[
 q_{N+1,d}=2q_{N,d}+\mathbf1_{d\mid N+1},
\]

then gives the exact collision inequality

\[
 \boxed{
  1\leq j_{N,d},\qquad
  2j_{N,d}+\mathbf1_{d\mid N+1}\leq A_{N,d}.}       \tag{4}
\]

Conversely, if the two greedy rows agree before (d), the old row skips at
(d), and (4) holds, then the new row takes at (d).  Thus (4) is an exact
criterion for the first horizon recut.  Its right side contains the source
digit, the square-root renormalisation, and the selected proper-divisor pulse;
its left side is the old binary-cell shortfall.

## 2. The same shortfall in the fractional seam coordinate

For the common prefix in Section 1 put

\[
 \Phi_{N,d}=\sum_{e<d}x^{(N)}_e
   \left\{\frac{2^N}{2^e-1}\right\},
 \qquad
 \phi_{N,d}=\left\{\frac{2^N}{2^d-1}\right\},
\]

and let \(\alpha_N=\{2^N/21\}\).  Splitting the real weights into quotient
and fractional parts gives

\[
 2^N\left(\frac1{21}-
     \sum_{e<d}\frac{x^{(N)}_e}{2^e-1}\right)
 =R_{N,d}+S_N+\alpha_N-\Phi_{N,d}.                  \tag{5}
\]

Consequently the rank-(d) atom is affordable after this prefix exactly when

\[
 \boxed{
 j_{N,d}\leq
 S_N+\alpha_N-\Phi_{N,d}-\phi_{N,d}.}               \tag{6}
\]

Equations (4) and (6) place the same integer (j_{N,d}) in the two clocks.
The horizon recut occurs when the next divisor pulse eats twice the integer
shortfall.  Real feasibility occurs when the denominator-(21) phase, after
subtracting the selected fractional divisor phases, eats the shortfall once.
This is the direct intersection of the quotient recut and moving-seam
descriptions; neither coordinate can be removed from the combined statement.

## 3. Recut ranks control the terminal remainder

At a recut rank (d), the old row skipped (q_{N,d}).  Every later greedy
operation only decreases its current remainder.  Therefore

\[
 0\leq r_N\leq R_{N,d}<q_{N,d}
 <\frac{2^N}{2^d-1}.                               \tag{7}
\]

In particular,

\[
 \boxed{\frac{r_N}{2^N}<\frac1{2^d-1}.}             \tag{8}
\]

This has an all-depth consequence.

**Recut theorem.**  If genuine horizon recuts occur infinitely often, then
(r_N=o(2^N)).

Indeed, lexicographic monotonicity implies that every fixed finite prefix of
(x^{(N)}) eventually stabilises.  Hence the first recut ranks along an
infinite sequence tend to infinity.  Equation (8) makes (r_N/2^N) tend to
zero along that sequence.  The limit law proved in
`ShiftedQuotientComparatorProof.md`,

\[
 \lim_N\frac{r_N}{2^N}
 =\frac1{21}-\sum_{d\in A}\frac1{2^d-1},            \tag{9}
\]

shows that the full sequence has a limit.  Its value is therefore zero.  The
limiting Boolean word (A) represents (1/21).

No bound on the lag (N-d) is required.  A bound such as (N-d=O(\log N)),
which is suggested by finite computation, would be much stronger than the
actual argument needs.

## 4. The exact alternative: eventual pure extension

The recut theorem leaves one alternative.  If there are only finitely many
genuine recuts, then from some horizon onward no old coordinate changes.  The
unused capacity of the padded old word at the next horizon is

\[
 2r_N+D_N,
 \qquad
 D_N=t_{N+1}+2S_N-S_{N+1}
       -\sum_{\substack{d\leq N\\d\mid N+1}}x^{(N)}_d.
\]

The proper-divisor estimate in `ShiftedQuotientComparatorProof.md` gives
(D_N\geq3).  Thus the new unit coin is taken, and the transition is exactly

\[
 x^{(N+1)}=x^{(N)}1,
 \qquad
 r_{N+1}=2r_N+D_N-1.                               \tag{10}
\]

The limiting word is then a fixed prefix followed by an all-one tail.  The
positive homogeneous mode in (10) is precisely the positive limit in (9).
Thus the positive fatal gap is confined to one rigid dynamical behaviour,
eventual pure extension, while every genuine recut supplies the quantitative
estimate (8).

To finish the (1/21) argument by this route it is enough to exclude a last
recut.  By (4), this means proving that the special denominator-(21) orbit
produces infinitely many prefix ranks for which the divisor allowance reaches
the integer shortfall.  Equation (6) records the additional fractional phase
condition needed to relate such a collision to the real Mersenne order.

## 5. Why the exclusion must be source-specific

The same monotonicity and pulse identities permit eventual pure extension at
other rational endpoints.  For (1/7),

\[
 \left\lfloor\frac{2^N}{7}\right\rfloor=q_{N,3}.
\]

The shifted target (q_{N,3}-S_N) skips ranks (1,2,3).  Moreover

\[
 q_{N,3}-S_N-\sum_{d=4}^Nq_{N,d}
 \geq \frac{2^N}{105}-S_N-1.                       \tag{11}
\]

The right side is positive for (N=11), and remains positive thereafter.
It follows by descending induction through the coins that every rank
(4,\ldots,N) is taken.  Hence for all (N\geq11)

\[
 x^{(N)}=0001^{N-3},
\]

all transitions are pure extensions, and (11) gives an exponentially large
terminal remainder.  This is an exact counterexample to any argument which
tries to deduce recurring recuts from lexicographic monotonicity, the divisor
pulse recurrence, and the square-root shift without using the special
(1/21) endpoint.

The exact audit script
`scripts/shifted_recut_phase_collision_audit.py` checks (4), (7), and (10).
Through horizon (2000), the (1/21) rows have a genuine recut at every
transition and terminal remainder zero; the largest first-recut lag in that
range is (18), at the transition to horizon (756).  For (1/7), the last
recut is at horizon (10), and every checked transition from horizon (11)
onward is the pure extension proved above.  These finite values select the
remaining theorem but do not prove it for (1/21).

## 6. Remaining phase-exclusion statement

The combined results isolate a single nonlocal assertion:

\[
 \text{the collision (4) occurs at arbitrarily large horizons.} \tag{12}
\]

A proof of (12) may be quantitative—for example, by bounding the first recut
lag—or qualitative.  Equation (6) locates a proposed recut on the real side,
but it does not imply the divisor collision (4).  A period-only or
denominator-free proof is impossible by Section 5.  The required input must
couple the exact phase

\[
 \alpha_N-\Phi_{N,d}-\phi_{N,d}
\]

to the selected-divisor allowance in (4).  This is the precise point at which
the moving binary hole and the divisor/LCM pulse are the same event rather
than parallel descriptions.
