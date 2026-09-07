# The first nonlocal recut for (M(4,5))

Put

\[
 w_r=\frac1{2^r-1},\qquad M(x,y)=w_xw_y,
 \qquad P_{r,c}=2^{-c}w_{r-c}.
\]

The target is

\[
 M(4,5)=\frac1{465}.                               \tag{1}
\]

Its first ordinary cylinder collision occurs at

\[
 n=4\cdot5+4+5=29.                                \tag{2}
\]

The optimal first-collision recut has coefficient

\[
 C=\frac{2^{28}-1}{2^4-1}-1
  =2^4+2^8+2^{12}+2^{16}+2^{20}+2^{24}.           \tag{3}
\]

This note follows the complete labelled first frontier through its first
moving hole.  The hole at rank (29) is not fatal.  It is repaired by an
ownership-closed pool containing two provisional packets and the residuals
attached to the two earlier retired heads.

## 1. Exact first frontier

Expanding the two outer paths to their first collision, and applying the
positive recut at rank (29), gives the stable atoms

\[
 9,13,14,17,19,21,24,25,28                       \tag{4}
\]

and the following cylinder blocks:

\[
\begin{array}{c|c}
\text{block}&(\text{front rank},\text{capacity})\\ \hline
M(9,13)&(22,13)\\
M(9,14)&(23,14)\\
M(13,17)&(30,17)\\
M(14,19)&(33,19)\\
M(5,29)&(34,29)\\
M(17,21)&(38,21)\\
M(19,24)&(43,24)\\
M(21,25)&(46,25)\\
M(25,29)&(54,29)
\end{array}                                       \tag{5}
\]

together with the children (M(24,29)) and the six binary blocks of
(C M(28,29)).  Their packet data are

\[
\begin{array}{c|c}
\text{block}&(\text{front rank},\text{capacity})\\ \hline
2^{24}M(28,29)&(33,5)\\
2^{20}M(28,29)&(37,9)\\
2^{16}M(28,29)&(41,13)\\
2^{12}M(28,29)&(45,17)\\
2^8M(28,29)&(49,21)\\
2^4M(28,29)&(53,25)\\
M(24,29)&(53,29).
\end{array}                                       \tag{6}
\]

The two forced collisions are

\[
 (33,5)+(33,19)\longrightarrow(32,4),
 \qquad
 (53,25)+(53,29)\longrightarrow(52,24).           \tag{7}
\]

No capacity-zero carry occurs.  The heads (22) and (23) agree with the
greedy support and may be retired, leaving their exact packet reserves in
the live residual.

## 2. The rank-(29) hole

Let

\[
 \mathcal P={9,13,14,17,19,21,22,23,24,25,28\}
\]

and define

\[
 R=M(4,5)-\sum_{r\in\mathcal P}w_r.               \tag{8}
\]

Exact comparison gives

\[
 w_{29}<R<2w_{29},                                 \tag{9}
\]

and

\[
 w_{34}<R-w_{29}<w_{33}.                          \tag{10}
\]

Thus the unique Boolean expansion, if it exists, must next contain ranks
(29) and (34).

At the packet-accounting level, after (7) and retirement of the heads
(22,23), write (E) for the pooled positive excess not attached to a
provisional head.  The residual has an exact decomposition

\[
\begin{aligned}
 R={}&E+P_{30,17}+P_{32,4}+P_{34,29}+P_{37,9}
       +P_{38,21}+P_{41,13}\\
    &+P_{43,24}+P_{45,17}+P_{46,25}+P_{49,21}
       +P_{52,24}+P_{54,29}.                       \tag{11}
\end{aligned}
\]

In particular, the provisional heads contain no rank (29).  The pooled
quantity (E) is useful for locating the hole, but it is not an ownership
unit: it contains fractional packet reserves from several physical cylinder
sources.  A valid recut must close under those sources.

The residuals behind the retired heads (22,23) are

\[
\begin{aligned}
 R_{22}&=M(9,13)-w_{22}=M(9,22)+M(13,22),\\
 R_{23}&=M(9,14)-w_{23}=M(9,23)+M(14,23).
\end{aligned}                                      \tag{12}
\]

The rank-(30) packet belongs to (M(13,17)).  The rank-(32) packet in
(7) belongs jointly to (M(14,19)) and (2^{24}M(28,29)).  Define the
ownership-closed pool

\[
 X=R_{22}+R_{23}+M(13,17)+M(14,19)
      +2^{24}M(28,29).                              \tag{13}
\]

Neither retired-head residual can be omitted:

\[
\begin{aligned}
 M(13,17)+M(14,19)+2^{24}M(28,29)+R_{22}&<w_{29},\\
 M(13,17)+M(14,19)+2^{24}M(28,29)+R_{23}&<w_{29},
\end{aligned}                                      \tag{14}
\]

but the complete pool satisfies

\[
 w_{29}<X<2w_{29}.                                 \tag{15}
\]

Put (Y=X-w_{29}).  Exact comparison gives

\[
 0<Y<w_{34},\qquad w_{35}<Y.                       \tag{16}
\]

This is a positive cylinder-cone recut, rather than only a packet
inequality.  Every term in (X) is a physical nonnegative cylinder cohort.
After writing (w_{29}=(2^e-1)M(e,29)) for any chosen (e), the aggregate
common-refinement identity recodes the positive difference (Y) as a
positive integer cylinder cohort.  Thus one may roll back the two
provisional packets together with the residuals of their two earlier sibling
heads, emit (w_{29}), and retain (Y) without fractional ownership.

The untouched cylinder (M(5,29)) supplies the next forced head (w_{34}),
consistently with (10).

This operation crosses two cylinder lineages.  No rule that preserves every
unique provisional head can perform it.  It is the first point at which the
unbounded schedule for (M(4,5)) genuinely differs from a static packet
normalization.

## 3. What the computation decides

The first static hole for (M(4,5)) is repairable with a positive exact
cylinder residual and without a deadline crossing.  The anchor therefore
survives the first global recut.  The calculation does not prove that the
same bounded pooling rule works at every later hole.  Proving that successive
ownership-closed recodings have uniformly bounded rollback width is the
unresolved scheduling theorem.

The relevant candidate invariant is now explicit: order the provisional
packets by front rank, close each candidate pool under the physical residuals
of previously retired sibling heads, and take the shortest ownership-closed
pool that crosses the next missing greedy weight.  At the first hole the pool
uses two provisional packets and two retired-head residuals, and its
post-recut residual begins six ranks later.  A proof for (M(4,5)) would have
to show that this ownership closure remains bounded, never reaches a
zero-capacity packet, and has recoded residual fronts tending to infinity.

## 4. Exact audit

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_first_nonlocal_recut.py
```

The script verifies the frontier identity, every packet in (5)--(7), the
residual decomposition (11), and the ownership-closed inequalities
(9)--(16) using exact rational arithmetic.
