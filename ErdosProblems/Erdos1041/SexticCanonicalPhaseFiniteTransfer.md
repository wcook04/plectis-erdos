# Actual sextics on the complete canonical second-mode phase

Status: ordinary analytic actual-polynomial theorem, with exact compact-cell
certificates and rational error bounds, 2026-09-05. The canonical-phase
transverse regime is closed under the explicit size and deficit hypotheses
below. Continuous second-mode phases and other near-regular branches remain
open. This is not a solution of unrestricted Erdős #1041, and is not Lean
checked or independently reviewed.

## The statement

Let \(\omega=e^{\pi i/3}\), and write
\[
 a_j=\omega^j(1+e_j),\quad |a_j|\le1,\quad
 f(z)=\prod_{j=0}^5(z-a_j),\quad E_m=\sum_{j=0}^5e_j\omega^{-jm}.
\]
Use the common rotational gauge \(E_0=-\Delta\), \(\Delta\ge0\), and put
\[
                 \rho=\max\{|E_1|^{1/5},|E_2|^{1/4}\}.
\]
**Theorem.** Suppose
\[
 0<\rho\le10^{-20},\qquad \Delta\le20000\rho^6,\qquad
 E_2\in\{-b,-b\omega^2,-b\omega^4:b\ge0\}.               \tag{1}
\]
Then two actual roots are joined inside the strict unit lemniscate
\(\{|f|<1\}\) by two actual radial tails and a straight chord, with
length at most
\[
                              2-\rho/800<2.               \tag{2}
\]
There is no restriction on the relative first-mode amplitude or on the
admissible tangent cubic beyond (1).

The new part is the branch
\(|E_1|<(13/25)|E_2|^{5/4}\). Here the roots can be chosen adjacent and
the stronger length bound \(2-\rho/4\) holds. The complementary branch
is the already proved actual first-mode cone in
`SexticNaturalScaleFiniteTransfer.md`; it supplies (2). Thus the conclusion
covers the whole canonical second-mode phase in the stated transverse
regime, rather than only the zero-first-mode plane or a small coefficient
neighborhood around it.

## 1. Normalize the remaining branch

On the new branch, \(E_2\ne0\) and \(\rho=|E_2|^{1/4}\). Sixth-root
rotation puts \(E_2/\rho^4=-1\). Set
\[
 A=E_1/\rho^5,\quad C=\operatorname{Im}E_3/\rho^3.
\]
Then \(|A|<13/25\), \(|C|<500\). Conjugation, when needed, allows us
to write \(A=a-iu\), with \(a\in\mathbb R\), \(u\ge0\). The
corresponding cubic changes sign under that conjugation.

We construct a connector for the pure-imaginary first coefficient. Reflect
it across the imaginary axis, if necessary, so that
\(a\operatorname{Re}z\le0\) on the whole connector. This only improves
the model inequality. The actual roots need not have these symmetries:
we use the symmetries to choose their indices, then explicitly account for
their actual angular displacements.

There are two ranges: \(0\le u\le1/16\), where strictness needs the
critical-threshold geometry, and \(1/16\le u<13/25\), where an exact
compact certificate suffices.

## 2. Uniform geometry near the vanishing first mode

Use the critical family \(\gamma(v),r(v),h(v)\) from
`SexticCanonicalCriticalThreshold.md`. Its parameters are
\[
 k=h^2/3,\quad D=5+25k-13k^2-k^3,\quad
 Y=(3k+1)/(3D),\quad y=Y^{1/4},\quad r=y(h+1)/\sqrt3.
\]
The family covers \(-1/16\le v\le1/16\) with
\(3/2\le h\le19/10\). Exact fourth-power comparisons at the two
endpoints prove this using its strict parameter monotonicity.

On this interval the exact critical-family identities give
\[
 10\le D\le20,\quad 1/20\le Y\le1,\quad R(k)\le3000,
 \quad -15k^3+51k^2+23k+5\ge40,                           \tag{3}
\]
where \(R\) is the positive degree-six derivative polynomial of that
source. Its curvature formula consequently yields
\[
 \gamma''(v)=
 \frac{4(15k^3-51k^2-23k-5)D}{y^3(3k-1)^3R(k)}
                         \le-1/100.                      \tag{4}
\]
Every inequality in (3) has an exact rational Bernstein check. Since
\(\gamma(0)=0\) and \(\gamma'(0)=\sqrt3\), Taylor's theorem implies
\[
                       \gamma(v)\le\sqrt3v-v^2/200.       \tag{5}
\]
Choose the upper chord with parameter \(v=u\) when \(C\ge\sqrt3u\),
and the antipodal chord with parameter \(v=-u\) when
\(C\le\sqrt3u\). Let
\[
 d_C=|C-\sqrt3u|,\qquad S\ge u^2/200+d_C
\]
be the favorable cubic surplus over that chosen family's critical value.
This surplus decreases the chord value by
\(S(3\sqrt3/2)r^3t(1-t)\), and vanishes on its root rays.

The exact positive square factor of the critical family supplies, with
\(t_*=2/(h+1)\) and \(x=t-t_*\), the global floor
\[
                     H_{-iv,\gamma(v)}\le-x^2/200.        \tag{6}
\]
Indeed its coefficient is
\(y^2(h+1)^3Q/(162D)\), where \(Q\ge16\), \(y^2\ge1/5\), and
(3) applies. Its radius satisfies \(1/2<r<1\).

## 3. The fourth mode supplies strictness at the critical contacts

The disc constraint gives
\(E_4=-\overline E_2+O(\Delta)\). Since the normalized second
coefficient is \(-1\), its retained fourth-mode contribution is
\(\rho^2\operatorname{Re}z^4\). Write \(d=\rho^2\).
At the critical point \(z_*=y(\sqrt k+i)\),
\[
 \operatorname{Re}z_*^4=Y(k^2-6k+1)\le-1/36.             \tag{7}
\]
For example \(k^2-6k+1\le-5/9\) for \(1/3\le k\le4/3\), and
(3) bounds \(Y\) below. Along the chord the derivative of
\(\operatorname{Re}z^4\) has modulus below eight. Thus (6) gives
\[
 H_{-iv,\gamma(v)}+d\operatorname{Re}z^4
 \le-\frac{x^2}{200}-\frac d{36}+8d|x|
 \le-\frac d{36}+3200d^2\le-d/72,                        \tag{8}
\]
valid already for \(\rho\le10^{-6}\).

On \(1/8\le t\le7/8\), the cubic shape is at least \(1/32\), using
\(r>1/2\). On the two end intervals, the critical parameter
\(t_*\in[20/29,4/5]\) is at distance at least \(3/40\). Equations
(6)–(8) then give an end-interval floor below \(-1/40000\), even after
the fourth-mode correction. The two estimates combine into
\[
 H_{-iu,C}+d\operatorname{Re}z^4
                    \le-d/144-\min\{S,1\}/100000.       \tag{9}
\]
On the chosen or reflected chord the real first term contributes at most
\(-|a|/4\). Define
\[
                       M=\rho^2+u^2+\min\{d_C,1\}+|a|.
\]
Since
\(\min\{S,1\}\ge\tfrac12(u^2/200+\min\{d_C,1\})\), (9) proves
\[
 \operatorname{Re}(Az-z^2+iCz^3+\rho^2z^4-z^6)
                             \le-M/40000000.              \tag{10}
\]
Here \(0<M<2\). This single bound covers zero cubic, the null relation
\(C=\sqrt3u\), and zero first mode without dividing by any vanishing
coefficient.

The two model rays also have sufficient margin. The nonreal chord endpoint
in the critical family has value at most \(-1/2000\), by the same exact
factorization with \((h+1)(h-1)^2\) in place of
\((h+1)^3x^2\). Its radial factor is nonincreasing beyond the truncation
radius, as proved in the critical-family source. The real ray is stronger.
The cubic surplus vanishes on the rays, and the real first term is favorable.
The fourth term costs at most \(32^4\rho^2\) through radius 32, leaving
\(-1/2500\). Thus (10) holds on the chord and both outward rays up to
normalized radius 32.

## 4. Eleven exact cells cover the remaining imaginary first mode

For \(1/16\le u\le13/25\), use the cutoff cubic \(C=\sqrt3u\).
On the upper radius-\(r\) chord, and on its antipodal copy with sign
\(s=1\) or \(s=-1\), respectively, the polynomial is
\[
 P_{s,u,r}(t)=
 su\left(\frac{\sqrt3r}{2}t-\frac92r^3t(1-t)\right)
          -r^2\operatorname{Re}w(t)^2-r^6\operatorname{Re}w(t)^6,
 \quad w(t)=1-t+t\omega.                                  \tag{11}
\]
Choose the upper family for \(C\ge\sqrt3u\), the lower for
\(C\le\sqrt3u\). The cubic difference is favorable on the entire
chosen chord, and zero on the two rays. Reflection handles the real first
coefficient as before.

The fixed rational radii are:

| sign | interval for \(u\) | radius |
|---|---|---|
| + | \([1/16,383/3200]\) | \(887/1000\) |
| + | \([383/3200,283/1600]\) | \(909/1000\) |
| + | \([283/1600,233/800]\) | \(471/500\) |
| + | \([233/800,13/25]\) | \(1003/1000\) |
| − | \([1/16,583/6400]\) | \(203/250\) |
| − | \([583/6400,383/3200]\) | \(399/500\) |
| − | \([383/3200,949/6400]\) | \(783/1000\) |
| − | \([949/6400,283/1600]\) | \(96/125\) |
| − | \([283/1600,749/3200]\) | \(93/125\) |
| − | \([749/3200,233/800]\) | \(177/250\) |
| − | \([233/800,13/25]\) | \(3/5\) |

For each row, exact rational Bernstein subdivision proves
\[
                 P_{s,u,r}(t)\le-10^{-6}
 \quad\text{throughout the full }(u,t)\text{ cell}.        \tag{12}
\]
The verifier encloses \(\sqrt3\) between
\(1732050807568/10^{12}\) and \(1732050807569/10^{12}\), using the
appropriate endpoint for the sign of its coefficient. Since (11) is affine
in \(u\), only the two interval endpoints require chord checks. They
produce 57 accepted Bernstein leaves in total. Coverage of both coefficient
intervals is checked exactly, with no gaps.

The nonreal ray endpoint satisfies the same \(-10^{-6}\) bound. Every
chosen \(r\ge3/5\) has \(r^4>1/10\); hence its radial factor
\(su\sqrt3/2+t/2-t^5\) is decreasing for \(t\ge r\), proving the
whole tail. The real ray is strictly negative independently. The radius
\(1003/1000\) is legitimate here: these are normalized coordinates, and
the physical chord radius is \(\rho r\), far below the actual root
radii. We extend model rays to normalized radius 32, not merely to one.

## 5. Exact actual-polynomial error control

Use the origin-anchored expansion and actual-direction comparison from
`SexticPairedQuarticFiniteLift.md`, §3. Root geometry gives both
\[
 \eta=\max|e_j|<100\rho^3,\qquad
 \eta\le\rho^3(|C|+\rho),\qquad |C|<500.                 \tag{13}
\]
The exact constant \(\log|f(0)|\le0\) is retained as a favorable term.
The remainder is estimated after subtracting that constant, not by a
possibly positive unanchored quadratic bound.

For the small-\(u\) branch, set \(c=|C|\). The new adaptive denominator
satisfies
\[
 \frac{(c+\rho)^2}{M}\le1100000,\qquad
 \frac{c+\rho}{M}\le503/\rho,\qquad
 \frac{|A|}{M}\le2/\rho.                                 \tag{14}
\]
For the first inequality, use \(c\le\sqrt3u+d_C\),
\(d_C<501\), \(u^2/M\le1\),
\(d_C^2/M\le251001\), and \(\rho^2/M\le1\).
For the others, use
\(u/(\rho^2+u^2)\le1/(2\rho)\),
\(d_C/M\le501\), and \(|a|/M\le1\).

The same error table as the paired-quartic lift, divided now by \(M\rho\)
and using (14), gives
\[
 \rho^{-6}\log|f(z_{\rm actual})|
 \le \operatorname{Re}(Az-z^2+iCz^3+\rho^2z^4-z^6)
                                      +10^{10}\rho M.     \tag{15}
\]
This holds on the actual chord and arms through \(32\rho\). The verifier
checks the explicit sum of every table row: anchored nonlinear remainder,
fourth-pairing defect, real cubic coefficient, fifth and zeroth Fourier
terms, logarithm and denominator corrections, and actual root-angle
substitution. The new fifth-mode ratio is the last inequality of (14).
At \(\rho\le10^{-20}\), the error is less than \(M/80000000\), so
(10) gives strict containment of every point.

On the compact branch, retaining a fourth-mode correction is unnecessary.
The coarser actual-polynomial estimate in
`SexticNaturalScaleFiniteTransfer.md`, §5, applies directly:
\[
 \rho^{-6}\log|f(z_{\rm actual})|
                \le\operatorname{Re}(Az-z^2+iCz^3-z^6)+10^9\rho.
\]
Its hypotheses are only the common coefficient and deficit bounds, not the
large-first-mode hypothesis used elsewhere in that source. Since
\(10^9\rho<10^{-6}/2\), (12) proves strict actual containment here too.

## 6. Extend to the roots and check length

The source-independent outer-arm estimates in
`SexticNaturalScaleFiniteTransfer.md`, §6, use only (13),
\(|E_1|\le\rho^5\), \(|E_2|\le\rho^4\), and the deficit bound.
They extend both actual tails from \(32\rho\) to their roots, with
strict \(|f|<1\) throughout. Their rational absorptions are replayed by
the verifier.

Every new-branch normalized radius exceeds \(1/2\). Actual adjacent root
directions satisfy \(|v_i-v_j|\le1+6\eta<5/4\). The path length is
therefore
\[
 |a_i|+|a_j|-2\rho r+\rho r|v_i-v_j|
                  \le2-\tfrac34\rho r<2-\rho/4.
\]
Combining this with the existing large-first-mode branch proves (1)–(2).

## Verification and remaining problem

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_canonical_phase_finite_transfer.py --actual-probe 24
```

Normal verification reads the fixed rational table
`scripts/sextic_canonical_compact_cells.json`; it performs no radius search.
The optional `--discover` command regenerates that table from numerical
proposals, accepting a proposal only after exact certification. The table's
SHA-256 is
`849987fdefbdaeee7a7e16fdc47b113914956e85a7f7502fde07bc5569a7658d`.

The optional 300-digit actual-root experiment adjusts the actual second
Fourier phase numerically, verifies the hypotheses to its stated tolerance,
and tests both assembled branches on actual polynomial paths. It is finite
regression evidence, not authority for continuous containment or an exact
phase claim. Equations (3)–(15), the exact cell coverage, and the imported
outer-arm inequalities are the ordinary proof.

The remaining transverse mixed problem has a continuous, noncanonical
second-mode phase. The deficit-dominated/cubic branches and configurations
outside (1) also retain their own obligations. The theorem does not turn a
sufficient transverse hypothesis into an equivalent formulation of #1041.

`tao_pipeline_receipt`: input: canonical critical-threshold model theorem;
output: actual-polynomial canonical-phase transverse theorem; artifact: this
note, checker and compact-cell table; understanding delta: the critical
quadratic gap and paired fourth mode handle vanishing margins, while eleven
fixed radii cover the regular compact interval; verification: ordinary
analytic continuous-containment proof with exact symbolic/rational checks;
publication/review: internal, not independently reviewed or Lean checked;
canonicalization: all canonical-phase relative first/cubic coefficients are
covered by one actual-polynomial theorem under (1); unresolved bottleneck:
continuous second-mode phases and other branches; next owner: #1041 proof lane.

`tao_writing_review`: the main statement uses actual roots, exact Fourier
phase, explicit size/deficit bounds and the weaker universal length bound.
The stronger adjacent-root bound is restricted to the new branch. Model
radii exceeding one are explained in physical coordinates. The proof treats
the zero-margin limit analytically and the compact interval by exact
certificates, with numerical discovery and regression clearly separated.
