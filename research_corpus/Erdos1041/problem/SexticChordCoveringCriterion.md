# The chord-covering criterion decouples, and the residual band closes at |A| = |B|

Status: complete homogeneous tangent-model theorems with exact replay
(`scripts/check_erdos1041_sextic_chord_covering_criterion.py`, 16/16 arms) and a
Lean scalar landing, 2026-08-25. The nonlinear actual-polynomial transfer and
the away-from-Fekete regimes remain open, so Erdős #1041 remains open.

Write the paired homogeneous sextic tangent model as

\[
\mathcal H_{A,B,C}(z)
 =\operatorname{Re}\!\left(Az+Bz^2+iCz^3-\overline Bz^4-\overline Az^5-z^6\right),
\qquad A,B\in\mathbb C,\ C\in\mathbb R,
\]

and let \(\omega=e^{\pi i/3}\).  For \(j\in\{0,\dots,5\}\) put

\[
\theta_j=\frac{(2j+1)\pi}{6},\qquad
 y(x)=\frac{\sqrt3+ix}{2},\qquad
 z_j(x)=e^{i\theta_j}y(x),\qquad -1\le x\le1,
\]

so that \(z_j\) traverses the adjacent unit chord \([\omega^j,\omega^{j+1}]\) and
\(z_{j+3}=-z_j\).  Write the rotated coefficients

\[
\alpha_j=Ae^{i\theta_j}=u_j+iv_j,\qquad
 \beta_j=Be^{2i\theta_j}=p_j+ir_j,\qquad
 c_j=(-1)^jC .
\]

## 1. The chord normal form

**Theorem 1.**  For every \(j\) and every \(x\in[-1,1]\),

\[
64\,\mathcal H_{A,B,C}(z_j(x))=-64+(1-x^2)\,N_j(x),
\tag{1}
\]

\[
N_j(x)=x^4-44x^2+91
 +4p_j(21-x^2)+16\sqrt3\,r_jx
 +10\sqrt3\,u_j(5-x^2)+2v_jx(29-x^2)
 -24\sqrt3\,c_j .
\tag{2}
\]

Every ingredient of the model collapses into one quartic damped by the endpoint
factor \(1-x^2\).  Two things follow immediately.

**Corollary 1.1 (uniform root depth).**  \(\mathcal H_{A,B,C}(\omega^j)=-1\) for
every \(j\) and every \((A,B,C)\).  In the paired model all six root directions
sit at exactly the same depth; no normalisation can move them.  Chord safety is
therefore a statement about the interior only, and \(x=\pm1\) never binds.

**Corollary 1.2.**  Chord \(j\) lies in \(\{\mathcal H\le0\}\) if and only if

\[
24\sqrt3\,c_j\ \ge\ S_j:=\sup_{|x|<1}W_j(x),
\qquad
W_j(x):=N_j(x)+24\sqrt3\,c_j-\frac{64}{1-x^2}.
\tag{3}
\]

\(W_j\) is free of \(C\); the cubic enters only through the scalar threshold.

## 2. The covering criterion decouples

**Theorem 2.**  Some adjacent unit chord lies in \(\{\mathcal H\le0\}\) *for every*
\(C\in\mathbb R\) **if and only if**

\[
\boxed{\ \min_{j\ \mathrm{even}}S_j\ +\ \min_{j\ \mathrm{odd}}S_j\ \le\ 0.\ }
\tag{4}
\]

*Proof.*  By (3), chord \(j\) is safe exactly when \(24\sqrt3\,(-1)^jC\ge S_j\).
For even \(j\) this is the upper half-line \(24\sqrt3\,C\ge S_j\); for odd \(j\)
the lower half-line \(24\sqrt3\,C\le-S_j\).  Six half-lines cover \(\mathbb R\)
iff the best upper one starts no later than the best lower one ends, which is
\(\min_{\mathrm{even}}S_j\le-\min_{\mathrm{odd}}S_j\).  \(\square\)

This is the exact criterion, and it **decouples**: the two-sided cubic question
becomes two independent one-dimensional suprema.  The pivot mechanism of the
supplied result is the special case \(j'=j+3\), which is only *sufficient*,
because \(\beta_{j+3}=\beta_j\) and \(\alpha_{j+3}=-\alpha_j\) force the pair to
share one second-mode phase.  Mixed pairs \(j'\neq j+3\) are strictly stronger
and are what the model actually uses once the first mode grows; see §6.

## 3. The residual band closes at |A| = |B|, not at 3|B|/4

Select \(j\) with \(\arg\beta_j\) in the closed left arc \([2\pi/3,4\pi/3]\);
one of the three admissible \(j\) always qualifies.  At the pivot
\(24\sqrt3\,c=50\sqrt3\,u\) the two antipodal profiles are \(M_j\pm\Omega_j\) with

\[
M_j(x)=x^4-44x^2+91+4p_j(21-x^2)+16\sqrt3\,r_jx,
\qquad
\Omega_j(x)=-10\sqrt3\,u_jx^2+2v_jx(29-x^2).
\]

On the arc the extremal phase is \(p_j=-1/2,\ |r_j|=\sqrt3/2\), giving
\(-64+(1-x^2)M_j(x)\le-P(t)\), \(t=|x|\), with

\[
P(t)=t^6-43t^4+24t^3+91t^2-24t+15 .
\tag{5}
\]

Cauchy--Schwarz on \(\Omega_j\) uses the exact kernel identity
\(300x^4+4x^2(29-x^2)^2=4x^2(x^4+17x^2+841)\), and the square root is removed by
the rational majorant

\[
\Bigl(29+\tfrac{5}{16}t^2\Bigr)^2-(t^4+17t^2+841)
 =\frac{3t^2\,(96-77t^2)}{256}\ \ge 0
\qquad(0\le t\le1).
\tag{6}
\]

Hence \(64\bigl(M\text{-part}+|\Omega|\text{-part}\bigr)\le-G_{|A|}(t)\) with
\(G_\lambda(t)=P(t)-2\lambda t(1-t^2)\bigl(29+\tfrac5{16}t^2\bigr)\).  At
\(\lambda=1\),

\[
G_1(t)=t^6+\tfrac58t^5-43t^4+\tfrac{651}8t^3+91t^2-82t+15 .
\tag{7}
\]

**Theorem 3.**  \(G_1(t)\ge\tfrac14\) on \([0,1]\).  Consequently, if
\(|B|=1\) and \(|A|\le1\), then for **every** \(C\in\mathbb R\) one of the two
antipodal adjacent unit chords at the selected \(j\) satisfies

\[
\mathcal H_{A,B,C}\le-\frac{1}{256}
\quad\text{on the whole chord, of Euclidean length exactly }1.
\tag{8}
\]

*Certificate.*  Six dyadic pieces, degree-six Bernstein controls, all strictly
positive:

| piece | least control |
|---|---|
| \([0,\tfrac14]\) | \(8535/8192\) |
| \([\tfrac14,\tfrac5{16}]\) | \(1473051/16777216\) |
| \([\tfrac5{16},\tfrac{11}{32}]\) | \(11388051/1342177280\) |
| \([\tfrac{11}{32},\tfrac38]\) | \(26890821/1073741824\) |
| \([\tfrac38,\tfrac12]\) | \(8035/32768\) |
| \([\tfrac12,1]\) | \(1029/256\) |

The dyadic halves \([0,\tfrac12],[\tfrac12,1]\) do **not** suffice at this
shift, at any Bernstein degree from 6 to 20 (the left control stays negative
throughout, only creeping from \(-1.628\) to \(-0.403\)).  The true minimum is
\(G_1\approx0.264286\) at \(t\approx0.335121\), so the subdivision has to
resolve that trough.  Lean carries all six identities and the case split.

**What this changes.**  The supplied result proves the band \(|A|\le\tfrac34|B|\)
with margin \(127/3072\); the desk residual is \(|E_1|/|E_2|<3/4\).  Theorem 3
proves the strictly larger band \(|A|\le|B|\).  The residual is therefore closed
**with a quarter-width overlap into the first-mode chart**, not met at a point.
Trading \(3/4\to1\) costs margin \(127/3072\to1/256\), a factor \(10.6\); both
branches are recorded, and the transfer may use whichever it needs.

## 4. The mechanism is sharp at 1.0153, and the pivot is not optimal

**Theorem 4.**  For the pivot \(T=25u/12\) at the extremal second-mode phase,
the exact threshold is

\[
\lambda^\ast=\min_{0<t<1}\frac{P(t)}{2t(1-t^2)\sqrt{t^4+17t^2+841}}
 =1.0153340671\ldots,
\tag{9}
\]

attained at the unique interior critical point \(t^\ast=0.3371285327\ldots\)
(the critical numerator has degree 18 and exactly one root in \((0,1)\)).
Moreover:

1. **Cauchy--Schwarz is lossless.**  The minimum over the direction of
   \(\alpha\) and the minimum over \(x\) commute, and for fixed \(x\) the inner
   maximum over unit directions *is* the Cauchy--Schwarz value.
2. **The symmetrisation is lossless.**  \(P(-t)-P(t)=48t(1-t^2)\ge0\), so the
   chord genuinely has more room on one half — but \(\arg A\) is adversarial and
   can always place the worst of \(|\Omega|\) on the tighter half.  Replacing
   \(P(x)\) by \(P(|x|)\) costs exactly nothing.
3. **The pivot itself is lossy.**  Allowing any real \(c\), not only \(c=T\),
   raises the antipodal-pair threshold from \(1.01533\) to \(1.38804\ldots\).

So \(3/4\) was never the boundary of the supplied mechanism.  Its own ceiling is
\(\lambda^\ast>1\), a factor \(1.3538\) beyond the stated band, and the freed
pivot reaches \(1.85\) times the stated band.

## 5. Where the antipodal pair genuinely dies

**Theorem 5.**  At \(x=0\) the two antipodal chords satisfy

\[
\bigl(N_j+24\sqrt3c_j\bigr)(0)+\bigl(N_{j+3}+24\sqrt3c_{j+3}\bigr)(0)=2(91+84p_j),
\]

so \(S_j+S_{j+3}\ge54+168p_j\), and any antipodal pair requires

\[
\operatorname{Re}\beta_j\le-\frac9{28}.
\tag{10}
\]

This is independent of \(A\), of \(C\), and of the pivot.  Since the best of the
three admissible \(j\) only guarantees \(\operatorname{Re}\beta_j\le-|B|/2\), the
antipodal mechanism cannot reach \(|B|<9/14\) at the extremal second-mode phase.
Below that ratio mixed pairs are mathematically necessary — which is exactly
what Theorem 2 supplies, and what a single-\(j\) pivot argument cannot.

## 6. Large first mode

Let \(\psi(\chi)=\max_{|x|\le1}\bigl[10\sqrt3\cos\chi\,(5-x^2)+2\sin\chi\,x(29-x^2)\bigr]\),
so that \(S_j=|A|\,\psi(\chi_j)+O(1)\) with \(\chi_j=\arg A+\theta_j\).  The six
\(\chi_j\) are equally spaced by \(\pi/3\) and alternate parity with \(j\).

**Theorem 6.**  For every \(\chi\) there are an even \(j\) and an odd \(j'\) with
\(|\chi_j-\pi|\le\pi/6\) and \(|\chi_{j'}-\pi|\le\pi/3\), and then

\[
\psi(\chi_j)\le-32,\qquad \psi(\chi_{j'})\le8\sqrt3,
\qquad\text{so}\qquad
\min_{\mathrm{even}}\psi+\min_{\mathrm{odd}}\psi\le8\sqrt3-32<0 .
\tag{11}
\]

*Proof.*  Inside \(\pi/6\): \(\cos\chi\le-\sqrt3/2\) and \(|\sin\chi|\le1/2\)
give \(f_\chi\le-75+15t^2+29t-t^3\), and
\(-32-(-75+15t^2+29t-t^3)=(t-1)(t^2-14t-43)\ge0\) on \([0,1]\).
Inside \(\pi/3\): \(\cos\chi\le-1/2\) and \(|\sin\chi|\le\sqrt3/2\) give
\(f_\chi\le\sqrt3(-25+5t^2+29t-t^3)\), and
\(8-(-25+5t^2+29t-t^3)=(t-1)(t^2-4t-33)\ge0\).  \(\square\)

With \(\sup_x\bigl[\Phi_\beta(x)-64/(1-x^2)\bigr]\le113\) for \(|\beta|\le1\),
criterion (4) therefore holds whenever

\[
|A|\ \ge\ \frac{226}{32-8\sqrt3}=12.46\ldots
\tag{12}
\]

The true extremal value of (11) is \(-32\sqrt3\), attained when the six
\(\chi_j\) land on the multiples of \(\pi/3\); (11) is the provable form, not the
sharp one.

## 7. What is now open in this lane

The desk residual is closed.  The exact remaining gap of the *chord* programme
is the band \(1<|A|<12.46\) at \(|B|=1\), where neither Theorem 3 nor Theorem 6
applies.  That band is already covered by the landed first-mode ray chart
(\(|A|\ge\tfrac34|B|\)), so nothing is uncovered — but the chord connector there
is only supported by a labelled numerical diagnostic, never by proof:

| \(\|A\|\) | \(\sup_{\text{phases}}\bigl(\min_{\mathrm{even}}S+\min_{\mathrm{odd}}S\bigr)\) | winning pair |
|---|---|---|
| \(0\) | \(-28.59\) | antipodal |
| \(0.5\) | \(-25.95\) | antipodal |
| \(1.0\) | \(-32.14\) | mixed |
| \(1.5\) | \(-84.85\) | mixed |
| \(3.0\) | \(-256.73\) | mixed |
| \(5.0\) | \(-454.39\) | mixed |

Mixed pairs take over at \(|A|\approx1\), and the criterion is monotonically
more negative afterwards.  This is *evidence for a producer, not a theorem*: no
uniform claim is made from it.  The producer is stated in
`research_packet.json` as `sextic_unrestricted_chord_covering_band`.

## 8. The transfer constant

The supplied result offers \(127/3072\) as the landing point for the nonlinear
actual-polynomial remainder.  That constant is correct **on its own band**
\(|A|\le\tfrac34\), but it was never the binding global constant: outside that
band the only available chart was the first-mode ray chart, whose margin is
\(|A|u/48\) at chord scale \(u\le1/16\), hence \(\ge1/1024\) at the chart floor
\(|A|=3/4\) — a factor \(42\) smaller, on a connector of length \(31/16\) with
length slack only \(1/16\).

After Theorem 3 the picture is:

| region | connector | length | slack | margin |
|---|---|---|---|---|
| \(\|A\|\le\|B\|=1\) | adjacent unit chord | \(1\) | \(1\) | \(1/256\) |
| \(\|A\|>\|B\|=1\) | truncated spokes | \(31/16\) | \(1/16\) | \(\ge1/768\) |

So the honest global constant is \(1/768\), set by the ray chart just above
\(|A|=1\), and the chord chart now owns the whole band where the first mode does
not dominate.  The ray-chart row restates
`SexticFirstModeThreeQuarterOverlap.md` as written; its proof was not
re-derived here.

## 9. Falsification, and one trap the checker had to be rebuilt around

Theorem 5 is not decorative: the chord chart really does die below
\(|B|=9/14\).  The checker exhibits it.  At \(|A|=0.2\), \(|B|=0.4\) there is a
choice of phases for which **no** adjacent chord is safe on an open window of
cubic coefficients of width \(3.2\times10^{-3}\); a second witness has width
\(2.4\times10^{-2}\).  Both sit inside the predicted dead zone
\(9/28<|B|<9/14\), and both are why the first-mode ray chart is not optional.

The first version of the criterion cross-check swept \(C\) on a uniform grid of
step \(0.05\) and declared those two instances *covered*.  They are not: the
grid stepped straight over an uncovered window narrower than one step.  A
uniform sweep is structurally the wrong instrument here, because the uncovered
set is the open interval \((U,L)\) and nothing bounds its width from below.  The
arm now places probes **relative to the two thresholds** — at \(L\pm\), \(U\pm\),
and strictly inside \((U,L)\) whenever \(U<L\) — and evaluates the original
complex chord formula there rather than the derived quantity.  It agrees on
every probe.  The mismatch was the sampler; the criterion was right.

## 10. Scope

Theorems 1–6 are statements about the homogeneous paired sextic tangent model.
They do not perform the source-specific nonlinear reconstruction from tangent
coefficients to an actual polynomial, do not touch the all-degree tied-face
regimes, and do not settle unrestricted Erdős #1041.  The pure-cubic face is
untouched and remains the separate radius-zero stratum of
`SexticCubicFaceConnectorNoGo.md`.
