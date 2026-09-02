# Banked split packets: pooled closure and the exact boundary

Write
\[
 w_k=\frac1{2^k-1},\qquad M(a,b)=w_aw_b.
\]
This note audits the banked-packet proposal independently of the grouped
self-copy rule.  The verdict is positive locally: a whole power block has an
exact protected-bank rewrite, including every LCM-generated cohort.  The
one-bank-per-tax interpretation is false, but pooling repairs it without any
signed terms.

The result does not prove a global Boolean normal form.  It supplies the
local closure theorem that such a proof would have to schedule.

## 1. Numerical domination is exact cone domination

For four positive indices put
\[
 L=\operatorname{lcm}(a,c),\qquad
 K=\operatorname{lcm}(b,d).
\]
Then
\[
 M(a,b)-M(c,d)=A M(L,K),                            \tag{1}
\]
where
\[
 A=
 \frac{2^L-1}{2^a-1}\frac{2^K-1}{2^b-1}
 -\frac{2^L-1}{2^c-1}\frac{2^K-1}{2^d-1}.          \tag{2}
\]
Both products in (2) are integers.  Since (M(L,K)>0),
\[
 A>0\quad\Longleftrightarrow\quad M(a,b)>M(c,d).
\]
Thus the proposed generalized cylinder-domination lemma is correct.

There is a finite aggregate version.  Orient every cylinder in a finite
integer combination, choose a common multiple of all first coordinates and
a common multiple of all second coordinates, and rewrite every term on that
one common cylinder.  A numerically positive integer combination is then a
positive integer multiple of the common cylinder.  Hence aggregate numerical
domination is sufficient for an exact positive cone residual.

This common refinement does not preserve a useful small endpoint: its two
coordinates can be enormous.  It proves exact positivity, not hereditary
deadline control.  The protected identity below preserves the anchor and is
therefore stronger for the normalization problem.

## 2. Exact pooled-bank identity

Assume (2\leq a\leq b), put (n=a+b), and let (0\leq j\leq b).  The
cylinder split is
\[
 M(a,b)=w_n+M(a,n)+M(n,b).                          \tag{3}
\]
The raw tax for carrying (2^j) copies of (w_n) to rank (r=n-j) is
\[
 \mathcal T_{n,j}
 =w_{n-j}-2^jw_n
 =\sum_{q=1}^j2^{j-q}M(n-q,n-q+1).                 \tag{4}
\]

Take the (2^j) copies of (M(a,n)) as the pooled bank.  Since
(1+w_a=2^aw_a),
\[
\begin{aligned}
 2^jM(a,n)-\mathcal T_{n,j}
 &=2^{a+j}M(a,n)-w_{n-j}\\
 &=D_{a,n,a+j}>0,                                  \tag{5}
\end{aligned}
\]
where (D_{u,v,k}=2^kM(u,v)-w_{u+v-k}) is the exact
anchored power-packet residual.  Positivity follows from (a+j\leq n).

Substitution into (3) gives the protected rewrite
\[
 \boxed{
 2^jM(a,b)
 =w_{n-j}+D_{a,n,a+j}+2^jM(n,b).
 }                                                   \tag{6}
\]
Every term on the right is positive.  More importantly,
\[
 w_{n-j}+D_{a,n,a+j}=2^{a+j}M(a,n)                 \tag{7}
\]
is itself a power packet.  Its leading rank is (r=n-j), its capacity is
\[
 n-(a+j)=b-j,                                       \tag{8}
\]
and its hard deadline is (a).  Thus the leftover bank is not merely some
positive scalar.  It carries the exact hereditary deadline certificate of
the original block.  The other child (2^jM(n,b)) remains separately
owned.

Equation (6) is also the exact aggregate majorization criterion in this
homogeneous setting.  For arbitrary bank cylinders (B_i), pooled payment
of a prescribed integer tax cohort (T) is possible in the nonnegative
cylinder cone exactly when
\[
 \sum_i B_i\geq T.                                 \tag{9}
\]
Strict inequality leaves a positive cone residual by the common-refinement
lemma.  If the emitted rank is (r), that residual has raw individual depth
at least (h) precisely when it dominates the largest requested adjacent
tax,
\[
 \sum_iB_i-T\geq M(r-h,r-h+1).                    \tag{10}
\]
Packet depth is less restrictive and is the invariant preserved by (6): a
reserve (sigma) is certified for (h) binary carries exactly when
\[
 \sigma\geq
 \Theta_{r,h}:=\sum_{q=1}^h2^{-q}M(r-q,r-q+1).     \tag{11}
\]
For several packets arriving at the same rank, their deadlines must in
addition satisfy the fixed-rank interval Hall inequalities.  Local value
domination does not remove that scheduling condition.

## 3. The (256M(10,11)) stop-21 block

For the leading binary block in
\[
 340M(10,11)=(256+64+16+4)M(10,11),
\]
take (a=10), (b=11), (n=21), and (j=8).  Its tax is
\[
 \mathcal T_{21,8}
 =128M(20,21)+64M(19,20)+\cdots+M(13,14).          \tag{12}
\]

The proposed one-bank-per-tax matching fails.  With
(B=M(10,21)), the minimum numbers of whole banks needed for the eight tax
levels are
\[
 128,64,32,16,8,4,8,16,
\]
whose sum is (276>256).  At the last three levels the exact relevant
ratios are
\[
 \frac B{M(15,16)}=\frac{3298595}{3295523}>1,
\quad
 \frac B{M(14,15)}=\frac{6493}{25949},
\quad
 \frac B{M(13,14)}=\frac{352213}{5630933}.
\]
So the failure is real, not a rounding artefact.

Pooling all 256 banks gives instead
\[
\begin{aligned}
 256M(10,21)-\mathcal T_{21,8}
 &=D_{10,21,18}\\
 &=\frac{1836031}{17572852409343}>0.                \tag{13}
\end{aligned}
\]
The protected rewrite is
\[
 256M(10,11)
 =w_{13}+D_{10,21,18}+256M(21,11).                 \tag{14}
\]
The banked atom (w_{13}+D_{10,21,18}) has capacity three and deadline
10:
\[
 D_{10,21,18}\geq\Theta_{13,3},qquad
 D_{10,21,18}<\Theta_{13,4}.                        \tag{15}
\]
Thus it is hereditary in the exact packet sense.

The attachment's stronger raw-depth convention gives a different number.
The bank residual alone dominates (M(12,13)) but not (M(11,12)), so it
has raw individual depth one.  If the other child is pooled into the reserve,
the full residual
\[
 256M(10,11)-w_{13}
 =\frac{2815}{17152617471}                          \tag{16}
\]
has raw individual depth two.  This distinction matters: binary packet
closure spends the combined reserves of colliding packets; it does not need
one labelled bank to pay every raw tax by itself.

## 4. Recursive closure for generated LCM cohorts

The heuristic claim that multiplicity height is only logarithmic in the new
stop is not valid for generated LCM cohorts.  Their coefficient can be
exponential in the new LCM endpoint, so its top binary exponent can be linear
in that endpoint.  Fortunately, no such asymptotic separation is needed.

An LCM lift produces (A M(s,L)), with
\[
 0<A<\frac{2^L-1}{3}<2^{L-1}.                      \tag{17}
\]
Every occupied binary exponent therefore satisfies (j\leq L-2).  Apply
(6) with (a=s), (b=L).  Every binary block becomes a protected banked
packet whose capacity is
\[
 c=L-j\geq2,                                       \tag{18}
\]
plus a separately owned positive child cohort.  Hence fresh generated LCM
cohorts are closed under the banked split and start with at least two packet
capacity levels.

There is also a uniform load contraction.  Encode
(D_{a,n,a+j}) as an anchored cylinder cohort.  The anchored-residual theorem
gives it load less than (8/15) of the parent block's load.  The other child
(2^jM(n,b)=2^jM(b,n)) has relative load (2^{-a}).  Therefore the total
protected-child load is less than
\[
 \left(\frac8{15}+2^{-a}\right)
 \text{(parent load)}
 \leq\frac{47}{60}\text{(parent load)},            \tag{19}
\]
because (a\geq2).  This bound survives arbitrary generated coordinates; it
is not a finite-front observation.

For the stop-21 block the second-child ratio is only (2^{-10}), so its
actual contraction bound is (8/15+1/1024).

## 5. What is proved, and what is not

The banked split closes exactly for every power block and every fresh
LCM-generated binary cohort.  It defeats the apparent stop-21 obstruction:
the 256 banks pay the full tax in aggregate and leave a capacity-three
protected atom, even though every disjoint whole-bank matching fails.

What remains global is the interval Hall problem for packets arriving from
different stops.  Capacity decreases when banked atoms collide.  Neither
(6) nor the contraction (19) proves that later arrivals cannot overload a
common hard deadline, or that each fixed rank eventually stabilizes.  The
rank-20 moving hole is therefore not solved by this local theorem.

The correct local primitive is not “one atom carrying one bank that pays one
future tax.”  It is a leading atom together with a positive reserve certified
by (11), a hard deadline, and a separately owned child cohort.  This object is
closed under both the pooled split (6) and the existing binary packet carry.

## 6. Exact receipt

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/banked_split_packet_closure_audit.py
```

The script verifies the generalized domination identity, the pooled rewrite,
the failed (276>256) whole-bank matching, the exact stop-21 capacity, and
the protected-child load bounds with rational arithmetic.  The general
proofs are the identities above; the parameter sweep is only a regression
receipt.
