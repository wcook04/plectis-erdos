# Fixed-source terminal windows cannot produce dyadic slivers

## Result

The sparse counterexample in
`UnitFractionDyadicSliverCounterexample.md` moves its target denominator
with the skipped rank and places every selected rank within $16$ places of
that rank. This mechanism cannot be translated to the fixed target
$1/465$, or to any fixed positive residual after a finite prefix.

Put

\[
w_d=\frac1{2^d-1}.
\]

Let $E$ be a fixed finite set and suppose

\[
\rho=x-\sum_{d\in E}w_d>0.
\]

For integers $m,L$ with $m-L>\max E$, let

\[
G\subseteq\{m-L,\ldots,m-1\},
\qquad
r=\rho-\sum_{d\in G}w_d.
\]

If rank $m$ is skipped, so that $0<r<w_m$, then necessarily

\[
\boxed{\rho<2^{L+2-m}.}                              \tag{1}
\]

Indeed,

\[
\rho=\sum_{d\in G}w_d+r
<\sum_{d=m-L}^{m}w_d
<\sum_{d=m-L}^{m}2^{1-d}
<2^{L+2-m}.
\]

This proves more than exclusion of the dangerous interval
$2^{-m}\le r<w_m$: under the opposite inequality

\[
\rho\ge 2^{L+2-m},                                   \tag{2}
\]

the proposed terminal support cannot even make rank $m$ a greedy skip.

For fixed $E$ and $\rho$, (1) implies

\[
L>m-2+\log_2\rho.                                   \tag{3}
\]

Thus a terminal-window construction valid at unbounded ranks must have
width $m-O_\rho(1)$. In particular, no fixed-width, logarithmic-width,
or $o(m)$-width terminal window can reproduce the sparse unit-fraction
counterexample for a fixed source residual.

## The first forced anchor for \(1/465\)

For $x=1/465$, ranks $1,\ldots,8$ are too large and rank $9$ is
taken. The residual after this first take is

\[
\rho_9=\frac1{465}-\frac1{511}
=\frac{46}{237615}>\frac1{8192}=2^{-13}.
\]

Apply the theorem with $E=\{9\}$. If every further selected rank before
a skipped rank $m$ belonged to a terminal window beginning at rank $15$
or later, then

\[
\sum_{d\ge15}w_d
<\sum_{d\ge15}2^{1-d}
=2^{-13}<\rho_9,
\]

so even the complete infinite continuation could not spend the residual.
Consequently the translated eight-rank pattern, whose first selected rank
is $m-16$, is impossible for $1/465$ once $m-16\ge15$. More
generally, after any fixed actual prefix with positive residual \(\rho_N\),
a dangerous skipped rank cannot be supplied only by a terminal window whose
left endpoint tends to infinity.

The conclusion is structural rather than a proof of dyadic undershoot. Any
counterexample on the $1/465$ orbit must use selected ranks across an
unbounded succession of intermediate scales. It cannot be a bounded
translate of a finite offset pattern.

## Exact fixed-\(465\) resonance

There is also a convenient integer form once the selected support $F$
contains denominators whose product is divisible by $465$. Write

\[
P=\prod_{d\in F}(2^d-1),
\qquad
S=\sum_{d\in F}\frac{P}{2^d-1},
\qquad
H=\frac P{465}-S.
\]

Then the residual is $r=H/P$. Since $P$ is odd, equality
$r=2^{-m}$ is impossible. Therefore the dyadic sliver condition is
equivalent to

\[
\boxed{1\le u_m:=2^mH-P\le H-1.}                    \tag{4}
\]

Equivalently, the positive residue of $2^mH$ modulo $P$ is smaller than
$H$. Formula (4) is the fixed-source analogue of the moment resonance
used by the sparse counterexample. It does not by itself exclude that
resonance for the actual orbit.

Before cancelling the factor $465$, write

\[
2^m=465K_m+a_m,
\qquad 1\le a_m<465,
\]

and put

\[
A_m=\sum_{d\in F}\left\lfloor\frac{2^m}{2^d-1}\right\rfloor,
\qquad Q_m=K_m-A_m.
\]

Since

\[
\frac{2^m}{2^d-1}
=\left\lfloor\frac{2^m}{2^d-1}\right\rfloor
+\frac{2^{m\bmod d}}{2^d-1},
\]

the uncleared error numerator is exactly

\[
\boxed{
465P\,(2^mr-1)
=P\bigl(465(Q_m-1)+a_m\bigr)
-465\sum_{d\in F}2^{m\bmod d}\frac{P}{2^d-1}.}     \tag{5}
\]

Thus an all-depth proof for $1/465$ must rule out a small positive value
of (5) using the complete multiscale greedy support. The terminal-window
theorem shows why the sparse offset resonance cannot supply such a value,
but it leaves the full-history case open.

## Relation to the finite-history counterfamily

`AnchorFourFiveFinitePhaseSynchronizationNoGo.md` freezes an arbitrary
actual prefix, then assigns zero coefficients over a long interval before
an eventual cofinite tail. At the synchronized rank $B$, its residual is
still the fixed positive number $\rho_N$, so $2^B\rho_N>1$.

There is no contradiction with (1). The assigned zero at rank $B$ is not
a real-greedy decision: for sufficiently large $B$, one has
$w_B<\rho_N$, and real greedy complementarity would force a take. In fact
(1), with an empty terminal window, gives a quantitative statement of the
missing condition. Quotient admissibility alone permits the frozen
continuation, whereas the real-greedy rule does not.
