# The paired fourth mode removes the sextic double contact

Status: ordinary analytic actual-polynomial theorem with exact symbolic and
rational checks, 2026-09-05. The result covers the natural second-mode plane
with zero first Fourier mode, including its zero-cubic degeneration, and a
specified neighborhood of that plane. It is not Lean checked and does not
settle every near-regular sextic or unrestricted Erdős #1041.

## The actual-polynomial statement

Let \(\omega=e^{\pi i/3}\),
\[
 a_j=\omega^j(1+e_j),\quad |a_j|\le1,\quad
 f(z)=\prod_{j=0}^5(z-a_j),\quad E_m=\sum_{j=0}^5e_j\omega^{-jm}.
\]
Choose the common rotational gauge \(E_0=-\Delta\), with \(\Delta\ge0\).
Assume \(E_2\ne0\), and put
\[
 \rho=|E_2|^{1/4},\quad A=E_1/\rho^5,\quad B=E_2/\rho^4,
 \quad C=\operatorname{Im}E_3/\rho^3,\quad
 M=\rho^2+\min\{|C|,1\}.
\]
**Theorem.** If
\[
 0<\rho\le10^{-18},\qquad \Delta\le20000\rho^6,
 \qquad |A|\le M/10000,                                  \tag{1}
\]
then two adjacent actual roots are connected inside \(\{|f|<1\}\) by two
radial tails and their joining chord, with total length at most
\[
                              2-\rho/2<2.                 \tag{2}
\]
Their common truncation radius is \(r_0\rho\), where
\[
 q_0=(7+4\sqrt3)/27,\qquad r_0=q_0^{1/4}.
\]
In particular the conclusion holds for **every actual configuration with
\(E_1=0\)** satisfying the first two conditions, with no extra condition on
the cubic coefficient. Root geometry automatically bounds \(|C|<500\).
At \(C=0\), the allowed first-mode thickness is
\(|E_1|\le\rho^7/10000\); away from zero cubic it is wider.

The new mechanism is a term lost in the leading homogeneous limit. The disc
constraint pairs \(E_4\) with \(-\overline{E_2}\). After spatial scaling this
produces \(-\rho^2\operatorname{Re}(\overline B w^4)\), whose value at the
canonical double contact is exactly \(-\rho^2/3\). This supplies a strict
margin even when the tangent cubic vanishes. Keeping the dependence on
\(|C|\) in the nonlinear remainder makes that margin survive for actual
polynomials.

## 1. A strict paired phase-circle lemma

For \(|B|=1\) and \(0<d\le10^{-12}\), define the even polynomial
\[
 V_{B,d}(z)=\operatorname{Re}(Bz^2-d\overline Bz^4-z^6).
\]
There is an adjacent sixth-root chord at radius \(r_0\) such that
\[
                         V_{B,d}\le-d/4.                  \tag{3}
\]
The pair can be chosen with its rotated coefficient phase in
\([\pi/3,\pi]\), exactly as in `SexticSecondModePhaseCircle.md`.

Here is why adding the fourth mode preserves that phase reduction. On the
base chord write \(z=R e^{i\alpha}\), \(0\le\alpha\le\pi/3\). The
coefficient-dependent part is
\[
 \operatorname{Re}\{B W\},\qquad
 W=z^2-d\overline z^4.
\]
On the first half, \(0\le\alpha\le\pi/6\), we have
\(\operatorname{Im}W\ge0\). With \(h=\pi/3-2\alpha\),
\[
 \operatorname{Im}(e^{-i\pi/3}W)
 =-R^2\sin h\,[1-2dR^2\cos h]\le0.
\]
Thus \(0\le\arg W\le\pi/3\). Reflection about the midpoint gives
\(\pi/3\le\arg W\le2\pi/3\) on the second half. For
\(\theta\in[\pi/3,\pi]\), the largest possible
\(\cos(\theta+\arg W)\) is consequently at \(\theta=\pi/3\) on the
first half and at \(\theta=\pi\) on the second. Rotation and reversal
identify the two boundary cases with the same canonical polynomial.

For that canonical case put
\(w(t)=1-t/2+i\sqrt3t/2\), \(t_*=\sqrt3-1\), \(x=t-t_*\).
The square-times-Bernstein factorization in
`SexticCanonicalMixedSlice.md`, strengthened by the exact square floor from
`SexticNullBranchFiniteTransfer.md`, gives
\[
 -r_0^2\operatorname{Re}(w^2+q_0w^6)
                  \le-\frac{r_0^2}{5}x^2\le-\frac7{50}x^2. \tag{4}
\]
The checker independently verifies the square division and all positive
Bernstein coefficients after subtracting \(1/5\).
At the contact,
\[
 q_0\operatorname{Re}w(t_*)^4=-1/3.                       \tag{5}
\]
The derivative of \(q_0\operatorname{Re}w^4\) has modulus at most four.
Therefore the canonical corrected value is at most
\[
 -\frac7{50}x^2-\frac d3+4d|x|
 \le-\frac d3+\frac{200}{7}d^2\le-d/4.                  \tag{6}
\]
This proves (3) on the entire phase circle, not only at the two boundary
phases.

## 2. An adaptive cubic margin and a small first mode

Keep the chosen chord or replace it by its antipode so that the tangent
cubic is favorable. The even polynomial is unchanged, and
\[
 \operatorname{Re}(iCz^3)
 =-|C|\frac{3\sqrt3}{2}r_0^3t(1-t).                      \tag{7}
\]
On \(1/8\le t\le7/8\), the coefficient multiplying \(-|C|\) is
larger than \(1/8\). On the two end intervals, the appropriate boundary
contact parameter is either \(2-\sqrt3\) or \(\sqrt3-1\), at distance
at least \(1/8\). Thus (4), together with the fourth term bounded by
\(d\), gives the stronger end-interval estimate
\[
                         V_{B,d}<-1/500.                  \tag{8}
\]
Combining (3), (7), (8) proves the uniform adaptive bound
\[
 V_{B,d}(z)+\operatorname{Re}(iCz^3)
                  \le-d/8-\min\{|C|,1\}/2000.           \tag{9}
\]
Now take \(d=\rho^2\), and add \(\operatorname{Re}(Az)\). Since
\(|z|<1\) and \(|A|\le M/10000\), the resulting normalized model
\[
 W_{A,B,C,\rho}(z)
 =\operatorname{Re}(Az+Bz^2+iCz^3-\rho^2\overline Bz^4-z^6)
\]
satisfies, on the complete chosen chord,
\[
                             W_{A,B,C,\rho}\le-M/2500.    \tag{10}
\]
This bound is uniform across \(C=0\); it does not divide by the cubic
coefficient.

The selected model ray directions have second-mode projections at most
\(1/2\), and the tangent cubic vanishes there. Since
\(q_0-1/2>1/64\) and \(r_0^2>7/10\), the even leading ray value for
\(r_0\le t\le32\) is at most \(-7/640\). The first and fourth terms
cost at most \(64/10000+32^4\rho^2\). Consequently both truncated rays
have value below \(-1/250<-M/2500\). The model margin (10) thus holds
on the chord and on both rays up to normalized radius 32.

## 3. The nonlinear remainder must retain its cubic dependence

The disc estimates and Fourier inversion from
`SexticNaturalScaleFiniteTransfer.md`, §2, remain valid because
\(|A|<1\), \(|B|=1\), and \(\Delta\le20000\rho^6\). In particular
\[
 |E_3|^2\le12\Delta,\quad |\operatorname{Re}E_3|\le\Delta,
 \quad |E_4+\overline E_2|\le2\Delta,
 \quad |E_5+\overline E_1|\le2\Delta.                     \tag{11}
\]
Write \(c=|C|\), \(\eta=\max_j|e_j|\). In addition to the coarse bound
\(\eta<100\rho^3\), there is the sharper estimate
\[
 \eta\le\frac{2\rho^4+2\rho^5+c\rho^3+5\Delta}{6}
                         \le\rho^3(c+\rho),              \tag{12}
\]
valid already for \(\rho\le10^{-6}\). This is the needed change from a
fixed cubic bound. When \(c=0\), the displacement is of order
\(\rho^4\), so the origin-anchored nonlinear error is smaller than the
quartic contact margin.

Use the exact anchored identity of
`FormACutQuantitativeExpansion.md`, §3:
\[
 \log|f(z)|=\log|f(0)|+\log|1-z^6|
       +\operatorname{Re}\frac{\sum_{m=1}^5 E_mz^m-\Delta z^6}{1-z^6}
       +R_a(z),
\]
\[
 |R_a(z)|\le\frac{6\eta^2r}{(1-r)^2(1-\eta/(1-r))}
 \quad (|z|\le r<1).
\]
Retain \(\log|f(0)|\le0\) exactly as a favorable term. With
\(R=32\), the positive normalized errors on \(z=\rho w\),
\(|w|\le R\), are bounded as follows; each row is divided by \(\rho^6\).

| source | bound |
|---|---|
| anchored nonlinear remainder | \(48R\rho(c+\rho)^2\) |
| defect in fourth-mode pairing | \(40000R^4\rho^4\) |
| real cubic coefficient | \(20000R^3\rho^3\) |
| fifth Fourier coefficient | \(R^5(|A|\rho^4+40000\rho^5)\) |
| zeroth Fourier term | \(20000R^6\rho^6\) |
| baseline logarithm correction | \(R^{12}\rho^6\) |
| denominator correction | \(40000000R^6\rho^6\) |
| replacement by actual root directions | \(3R(3\cdot10^8)\rho^3(c+\rho)\) |

For the denominator row, \(|N(\rho w)|/\rho^6<20000000\) follows from
the common coefficient bounds. For the angle row, actual unit root
directions differ from their sixth roots by at most \(3\eta\), and the
complex derivative of the normalized model on \(|w|\le32\) is below
\(3\cdot10^8\). The straight-line interpolation of actual directions
has the same displacement bound as the rays.

Here are elementary inequalities that make every row uniform at zero cubic:
\[
 M\ge\rho^2,\quad
 \frac{(c+\rho)^2}{M}\le500002,\quad
 \frac{c+\rho}{M}\le\frac{501}{\rho},\quad
 \frac{|A|}{M}\le1/10000.                                \tag{13}
\]
The first cubic ratio uses \(c^2/M\le250000\) and
\(\rho^2/M\le1\). The second uses \(c/M\le500\) and
\(\rho/M\le1/\rho\). Dividing the table by \(M\rho\), then using
\(\rho\le10^{-6}\), gives the rational estimate
\[
 \rho^{-6}\log|f(z_{\rm actual})|
 \le W_{A,B,C,\rho}(w_{\rm model})+10^{10}\rho M.          \tag{14}
\]
At the theorem cap \(\rho\le10^{-18}\), the last error is smaller
than \(M/5000\). Equations (10) and (14) prove strict actual containment
of the chord and the two arms through radius \(32\rho\).

## 4. Actual root endpoints and length

The outer-arm estimates in `SexticNaturalScaleFiniteTransfer.md`, §6, use
only \(|E_1|\le\rho^5\), \(|E_2|\le\rho^4\),
\(|E_3|\le500\rho^3\), \(\Delta\le20000\rho^6\), and
\(\eta<100\rho^3\). They require no positive lower bound on \(|A|\).
All these hypotheses hold here. They give \(\log|f|<-24t^6/25\) on
the actual rays for \(32\rho\le t\le1/2\), and
\(|f(tv_j)|\le1-t^6+210\eta<1\) from \(1/2\) to the actual root.
The checker replays those common rational absorptions.

The chosen directions are adjacent, so their actual unit directions satisfy
\(|v_i-v_j|\le1+6\eta<5/4\). Since \(r_0>4/5\), the full length is
\[
 |a_i|+|a_j|-2r_0\rho+r_0\rho|v_i-v_j|
 \le2-\tfrac34r_0\rho<2-\rho/2.
\]
This proves (2), including actual root endpoints and strict containment.

## Verification, contribution, and remaining boundary

Run

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_paired_quartic_finite_lift.py --actual-probe 21
```

The checker verifies the exact contact value, square-factor floor, cubic
identity, phase-wedge identity, and rational error absorptions. Its optional
300-digit actual-root experiment includes canonical boundary phases, zero
cubic, cubic of size \(\rho^2\), nonzero cubics of both signs, and small
nonzero first modes. It checks the theorem hypotheses and samples the actual
paths, including the algebraic contact parameters. The finite experiment is
regression evidence; the continuous theorem is proved above.

Candidate selection: a numerical parity-threshold survey of the residual
small-first-mode region pointed back to the known canonical double contact.
That survey is not a global certificate. The exact probe chosen instead was
the sign of the paired fourth mode at that contact and whether its margin
survives the actual-root remainder. The coefficient gives \(-1/3\), and
keeping \(c\) in (12) resolves the otherwise incorrect fixed-error
comparison at \(c=0\).

This complements the actual first-mode cone
\(|A|\ge13/25\) of `SexticNaturalScaleFiniteTransfer.md`. It closes the
finite transfer of the pure second-mode/cubic plane and the neighborhood
(1). The intermediate mixed region, the other radial/cubic branches, and
configurations outside the stated near-regular range remain open. Neither
an exhaustive near-regular sextic theorem nor an unrestricted #1041 solution
is asserted. No external novelty, independent review, or Lean check is
claimed.

`tao_pipeline_receipt`: input: a non-strict homogeneous phase-circle theorem;
output: an actual-polynomial theorem with explicit strict margin and path;
artifact: this note and checker; understanding delta: a paired fourth mode
removes the zero-cubic double contact, while a cubic-dependent displacement
bound permits one proof through that degeneration; verification: ordinary
analysis, exact symbolic identities and rational inequalities, plus an
explicitly finite high-precision falsifier; publication/review: internal and
not independently reviewed; canonicalization: the phase-circle finite lift
is one theorem with its zero-cubic limit included; unresolved bottleneck:
the intermediate mixed first/second-mode region; next owner: #1041 proof lane.

`tao_writing_review`: the statement distinguishes actual roots, normalized
coefficients, and model coordinates. The hard step is (12)–(14), because a
coarse error independent of the cubic would swamp the quartic margin.
The phase argument, canonical factorization, and shared outer-arm proof have
explicit source roles. Every endpoint, strictness assertion, scaling factor,
and numerical evidence boundary is displayed for ordinary proof review.
