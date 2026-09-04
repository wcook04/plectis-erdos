# Grouped packet batches: exact algebra, failed ownership

Put
\[
 w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b,
\]
and assume (2\leq a\leq b), (0\leq j\leq b).  Set
\[
 c=b-j,\qquad r=a+c,
\]
and
\[
 P_{r,c}=\frac{w_a}{2^c}
 =w_r+\Theta_{r,c},\qquad
 \Theta_{r,c}=\sum_{s=1}^c2^{-s}M(r-s,r-s+1).
\]
The single-block identity is
\[
 2^jM(a,b)=P_{r,c}+2^{-c}M(a,b).                 \tag{1}
\]
This note audits the proposal to take (2^c) identical copies of (1),
recombine their fractional self-copies, and use the resulting expression as a
closed positive rewrite.

## 1. The batch identity is exact

Multiplying (1) by (2^c) gives
\[
 \boxed{2^bM(a,b)=w_a+M(a,b).}                   \tag{2}
\]
Thus the tax pieces do exactly what was hoped:
\[
 2^c\bigl(w_r+\Theta_{r,c}\bigr)=w_a,
\]
while the (2^c) fractional self-copies recombine to one integral copy of
(M(a,b)).  Both parts are positive, and their algebraic ownership is
disjoint.  There is no hidden signed cancellation in (2).

The problem is not the identity.  It is that (2) is not a closed
load-preserving packet rewrite.

## 2. One batch already exhausts its Hall budget

The deadline-packet load is (2^{-c}).  Hence the (2^c) input packets in one
batch have total load
\[
 2^c2^{-c}=1.                                     \tag{3}
\]
Their emitted atom (w_a=P_{a,0}) is at its endpoint and itself has load
(1).  The regenerated cylinder is still live.  Re-encoding
(M(a,b)) as its unit power packet gives capacity (b), deadline (a), and
strictly positive load (2^{-b}).  Therefore disjoint active ownership on the
output side has load
\[
 1+2^{-b}>1.                                      \tag{4}
\]

Consequently, the following three requirements cannot hold simultaneously:

1. the endpoint atom and regenerated cylinder are disjoint live resources;
2. the regenerated cylinder remains eligible for later packet expansion;
3. the rewrite preserves the input Hall/Kraft budget.

Assigning zero load to the residual avoids (4) only by making it unavailable
to subsequent packet reasoning.  Reactivating it later spends ancestry a
second time.  Deferring it until the endpoint atom is retired is a possible
two-level ledger convention, but it is not the proposed closed batch rewrite
and needs an additional global ownership theorem.

This is the exact form of the tax/residual double-use obstruction.  The tax
escrow can be disjoint algebraically while failing to be disjoint as a future
collision budget.

## 3. Two batches give the sharp endpoint overload

The obstruction is not merely an artefact of the load notation.  Two batches
give
\[
 2^{b+1}M(a,b)=2w_a+2M(a,b).                      \tag{5}
\]
The residual cannot pay the adjacent carry tax, because
\[
 2M(a,b)<M(a-1,a).                                \tag{6}
\]
Indeed, after cancelling (w_a>0), (6) is
(2w_b<w_{a-1}), which follows from (b\geq a) and
(w_{a-1}=2w_a+M(a-1,a)>2w_a\).

Thus
\[
 2w_a<2^{b+1}M(a,b)<w_{a-1}.                      \tag{7}
\]
This interval contains no Boolean Mersenne subsum.  No rank below (a) can
occur, because each such atom is at least (w_{a-1}).  On the other hand, at
most one (w_a) can occur and
\[
 \sum_{n>a}w_n<w_a.                               \tag{8}
\]
For completeness, expand geometrically:
\[
 \sum_{n>a}w_n
 =\sum_{k\geq1}\frac{2^{-ka}}{2^k-1}
 <\sum_{k\geq1}2^{-ka}=w_a.
\]
So every Boolean sum supported on ranks at least (a) is below (2w_a),
contradicting (7).

Two is the first number of complete batches that forces two atoms at the hard
deadline.  For the root-shaped example,
\[
 16M(2,3)=\frac{16}{21}
\]
lies strictly between (2w_2=2/3) and (w_1=1), and therefore has no Boolean
representation.  This is a minimal exact counterexample in batch count to a
universal positive Boolean batch normalizer.

## 4. The rule cannot fire on the first LCM lift

The exceptional first-lift cohort is
\[
 340M(10,11),\qquad 340=2^8+2^6+2^4+2^2.
\]
Grouping unit cylinders would require (2^{11}=2048) identical copies, but
(340<2048).  Grouping the four binary blocks separately does not help:
their capacities are respectively (3,5,7,9), so a batch would require
(8,32,128,512) identical copies of the corresponding block, while there is
only one of each.  Nor can a different power-block partition help: a batch of
(2^{11-j}) copies of (2^jM(10,11)) always consumes exactly (2^{11})
raw cylinder copies.

The six ordinary first-front cylinders are also singleton sources.  Sources
that happen to collide at the same rank are not interchangeable for this
batch rule: their fractional residuals have different cylinder labels.  For
example, the decisive rank-13 carry uses
\[
 2^8M(10,11)\quad\hbox{and}\quad M(5,8),
\]
whose residuals are (2^{-3}M(10,11)) and
(2^{-8}M(5,8)).  They cannot recombine into an integral self-copy.

Hence the number of legal grouped-self-copy rewrites on the entire first
front is exactly zero.  In particular, the grouped rule neither repairs nor
even reaches the known rank-20 moving hole.  The earlier packet carries that
recover ranks 11 and 13 necessarily combine nonidentical labelled sources;
their success does not provide the identical residual multiplicities demanded
by (2).

There is also a general local reason for this failure.  A single LCM lift with
new right endpoint (L) produces a cohort coefficient (A<2^{L-1}).  A unit
batch for a cylinder (M(n,L)) needs (2^L) copies.  Thus no isolated
newly-lifted cohort can close its fractional residuals by the grouped rule.
The coefficient bound is immediate from the exact LCM formula and (e\geq2):
\[
 A<\frac{2^L-1}{2^e-1}\leq\frac{2^L-1}{3}<2^{L-1}.
\]
Any eventual batch must pool ownership across distinct waves.  Such pooling is
precisely where a global ancestry ledger, rather than the local identity (2),
is required.

## 5. Verdict

The proposed algebra yields a useful exact renewal identity, but not a
deadline-safe Booleanisation mechanism:

\[
 \boxed{2^bM(a,b)\longmapsto w_a+M(a,b)}.
\]

It reaches the endpoint while regenerating the same cylinder.  The atom uses
the full unit Hall budget and the regenerated cylinder asks for additional
positive budget.  Two renewals create a genuine, unrepairable endpoint
overload.  On the actual first lift there is not even one complete identical
batch, so the rank-20 moving hole survives unchanged.

The only remaining viable version would need a nonlocal rule saying when a
residual is dormant, which discharged atom releases its ancestry, and how
residuals from different waves may be activated without double spending.  That
is additional mathematics; it is not contained in the grouped-packet
identity.

## 6. Exact receipt

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/grouped_packet_batch_ownership_obstruction.py
```

The script checks (1)--(7) over a finite parameter grid using exact rational
arithmetic, verifies the symbolic load mismatch, and reports that no grouped
self-copy rewrite is available on the ten labelled sources of the first
front.  The argument above, not the grid size, proves the result for all
parameters.
