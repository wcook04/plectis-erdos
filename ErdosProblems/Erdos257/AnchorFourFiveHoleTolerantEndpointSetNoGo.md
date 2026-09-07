# A common one-third prefix does not protect the source corridor

Status: exact finite countermodel to a compressed endpoint-set induction,
2026-08-21.  The countermodel uses the actual binary digits of (1/465),
the actual corridor ceilings, and genuine divisor loads from the certified
common prefix.  It is not a counterexample to the full-prefix dynamic
program: it deliberately assigns half-rank bits which the real rank-(111)
states do not have.

Put

\[
 K_n=\left\lfloor\frac n{20}\right\rfloor,
 \qquad
 q'=2q+t_n-h_n-e_n-b_n.                         \tag{1}
\]

Here (q) is the old endpoint, (b_n\in\{0,1\}) is the new bit,
(h_n) counts selected proper divisors at most (n/3), and
(e_n=b_{n/2}) when (n) is even and is zero when (n) is odd.  If all
states agree through (n/3), these are the only state-dependent terms in
the proper-divisor count.

## 1. The fixed source data

The common (1/465) prefix through rank (38) has support

\[
 \{9,13,14,17,19,21,22,23,24,25,28,29,34,35,36,37\}.
                                                               \tag{2}
\]

At ranks (112,ldots,116), its relevant divisor rows are

\[
\begin{array}{c|c|c|c}
n&t_n&\{d\le n/3:d\mid n,\ b_d=1\}&h_n\\ \hline
112&0&\{14,28\}&2\\
113&1&\varnothing&0\\
114&1&\{19\}&1\\
115&0&\{23\}&1\\
116&0&\{29\}&1.
\end{array}                                                   \tag{3}
\]

Also (K_n=5) throughout this range.  Thus every number in the
construction below is fixed by the real source and a genuine Boolean
divisor word; the free data are only the half-rank labels allowed by the
proposed compression.

## 2. Exact extinction

Start at rank (111) with the full endpoint set

\[
 S_{111}=\{0,1,2,3,4,5\}.
\]

Assign the rank-(56) labels, in endpoint order, by

\[
 (e_{112}(0),\ldots,e_{112}(5))=(0,1,0,1,0,0),                \tag{4}
\]

and put every surviving rank-(57) and rank-(58) label equal to zero.
Applying (1), taking both choices of (b_n), and intersecting with
([0,5]) gives

\[
\begin{aligned}
 S_{112}&=\{1,2,3,5\},\\
 S_{113}&=\{2,3,4,5\},\\
 S_{114}&=\{3,4,5\},\\
 S_{115}&=\{4,5\},\\
 S_{116}&=\varnothing.                              \tag{5}
\end{aligned}
\]

For example, at rank (112), equation (1) is
(q'=2q-2-e-b_{112}); the assignments in (4) give exactly the first
line of (5).  At ranks (113,ldots,116), the constants
(t_n-h_n) are (1,0,-1,-1), which give the remaining lines.

Thus even a full endpoint interval, the actual period-(20) source word,
the actual corridor width, a common prefix substantially longer than
(n/3), and genuine common divisor loads do not imply survival when the
half-rank bits are treated as arbitrary state labels.  Cardinality and a
central-band condition cannot repair this loss: the construction starts
with every endpoint and ends with none in five transitions.

## 3. Exact boundary

The full-prefix corridor is not refuted.  Its six exact states at rank
(111) all have

\[
 b_{56}=b_{57}=b_{58}=0,                            \tag{6}
\]

whereas (4) assigns (b_{56}=1) to two endpoints.  Consequently a valid
hole-tolerant theorem must retain more than a one-third common prefix and
the current endpoint set.  It must retain the inverse-cylinder relation
between endpoints and the half-rank bits, or prove a quantitative suffix
bound which makes those bits common before they enter a divisor row.

The companion script checks (2)--(6) in exact integer arithmetic, including
the real full-prefix states at rank (111).
