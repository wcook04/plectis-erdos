# Cut-level reserve, the height-30 insolvency, and the global-lex veto

Write
\[
 w_n=\frac1{2^n-1},\qquad M_n=2^n-1.
\]
This note tests whether persistent ownership can strengthen the moving-corridor
exclusion for the fixed anchor-two root.  At the scalar cut level the answer is
negative.  Once the complete unresolved root tail is in the fatal corridor,
no repartition into a protected component and an external bank can pay the
predecessor deficit.  The exact shortfall is the upper cyclotomic gap already
present in the corridor coordinate.

This does not exclude an isolated first hit.  It shows that an independent
``unspent external bank'' invariant cannot exclude one: such an invariant is
equivalent to proving that the complete root tail never enters the corridor.

## 1. Common-denominator coordinate

Let \(r\ge16\), let \(H\) be divisible by \(15,r,r-1\), and let \(D\)
be any positive common Mersenne denominator divisible by
\(M_{15},M_r,M_{r-1}\) and by every selected denominator.  Starting from
the unresolved root cohort
\[
 X=1510M(2,15)=\frac{1510}{3M_{15}},
\]
remove a finite Boolean family \(F\), and put
\[
 T=X-\sum_{n\in F}w_n,\qquad K=3DT.
\]
Thus
\[
 K=1510\frac D{M_{15}}-3\sum_{n\in F}\frac D{M_n}.
\]
The predecessor endpoint is
\[
 U=3\frac D{M_{r-1}},\qquad \frac U{3D}=w_{r-1}.
\]

Suppose the physical unresolved state is partitioned as
\[
 T=V+R,
\]
where \(V\) is the protected component and \(R\ge0\) is every other
unspent root-owned summand.  The bank required to promote \(V\) to the
predecessor is
\[
 B=w_{r-1}-V.
\]
No ancestry or cylinder assumption is needed for the following identity:
\[
\boxed{
 R-B=T-w_{r-1}=\frac{K-U}{3D}.
}                                                     \tag{1}
\]
It is simply conservation of the complete physical state, but it is
lossless in the same integer coordinate as the primitive charge.

## 2. The ownership obstruction

If the complete state is in the moving fatal corridor
\[
 6\frac D{M_r}\le K<3\frac D{M_{r-1}}=U,
\]
then \(T<w_{r-1}\).  Since \(0\le V\le T\), the required bank \(B\) is
positive, and (1) gives
\[
 \boxed{B-R=\frac{U-K}{3D}>0.}                    \tag{2}
\]
Therefore every physical ownership partition is insolvent.  Moving value
between the protected component and the external bank changes \(B\) and
\(R\) by the same amount and cannot change their difference.

For a protected divisor-prefix genealogy, the adjacent cyclotomic theorem
gives
\[
 G:=U-K=b\Phi_r(2),\qquad b\in\mathbb N_{>0}.
\]
Consequently the exact ownership shortfall is
\[
 \boxed{B-R=\frac{b\Phi_r(2)}{3D}.}                \tag{3}
\]
The primitive rank-\(r\) charge is thus not a hidden reserve.  It is the
quantized amount by which the complete cut fails to own enough value for
the predecessor recut.

Conversely, \(K\ge U\) is exactly the whole-cohort solvency condition
\(R\ge B\).  Hence a positive cut-level reserve theorem for every first-hit
cut is logically identical to a non-entry theorem for the fixed root charge.
Persistent labels can still restrict which cuts are reachable, but after a
cut is reached they cannot repair (2).  Section 4 gives an exact insolvent cut
reachable under unrestricted positive common-height recuts.  Section 5 shows
the first precise restriction which excludes it from the complete-root greedy
row.

## 3. The first-wave boundary cases

The literal low first-wave packets have
\[
 V=P(15,2)+P(15,1)=2w_{15}.
\]
If they are isolated, \(R=0\), and
\[
 B-R=w_{14}-2w_{15}=M(14,15).                     \tag{4}
\]
This is the zero-buffer obstruction.

For the complete first wave, the external value is initially
\[
 R_0=1504M(2,15).
\]
More strongly, `FirstWaveZeroBufferSolvency.md` proves that after every
Boolean extraction from \(R_0\) avoiding ranks \(15,16\), the remaining
external bank is still greater than \(M(14,15)\).  Equation (1) identifies
that theorem exactly as exclusion of the complete root tail from the
rank-\(15\) corridor; it does not arise from a different ownership balance.

## 4. A complete-root height-30 insolvency

The schedule-independent extension of first-wave solvency is false even for
the fixed root.  Lift the complete unresolved root cohort from height 15 to
height 30.  Its coefficient is
\[
 C=\frac{1510M(2,15)}{M(2,30)}
  =1510(2^{15}+1)=49\,481\,190\equiv6\pmod8.       \tag{5}
\]
Thus its literal binary cohort contains the protected pair
\[
 P(30,2)+P(30,1)=6M(2,30)=2w_{30}.                 \tag{6}
\]

Put \(Y=1510M(2,15)-2w_{30}\).  Constrained greedy extraction from
\(Y\), with ranks 30 and 31 forbidden, reaches at rank 57 the finite set
\[
\begin{split}
F=\{&7,8,9,10,11,13,16,18,20,22,24,29,32,34,37,39,\
    &42,45,46,47,49,50,51,53,54,56,57\}.
\end{split}                                        \tag{7}
\]
Its exact remainder
\[
 R=Y-\sum_{n\in F}w_n
\]
satisfies
\[
 \boxed{0<R<M(29,30).}                             \tag{8}
\]
Because rank 29 is already selected, the complete local run obeys
\[
 2w_{30}+R<w_{29},\qquad
 w_{29}+2w_{30}+R<w_{28}.                          \tag{9}
\]
The first inequality is the zero-buffer failure; the second says that adding
the occupied predecessor still does not fund the next carry.

This is reachable under unrestricted positive common-height recuts.  Every
prefix of (7) leaves a positive external remainder.  If \(H\) is a common
multiple of 15, 30, and the finitely many extracted ranks, every denominator
divides \(M_H\), so each remainder is a positive integer multiple of
\(M(2,H)\).  Hence no signed identity or numerical approximation is used.
This reachability statement concerns the permissive global cone-recut grammar;
it does not assert that the cut occurs under complete-root greedy scheduling.

## 5. The first source-sensitive restriction

The witness (7) is itself the constrained greedy row of the *external*
value.  Its first disagreement with the complete-root greedy row occurs at
rank 28.  Let
\[
 F_0=\{5,7,8,9,10,11,13,16,18,20,22,24\},
 \qquad
 T_0=\frac1{21}-\sum_{n\in F_0}w_n,
\]
and freeze the protected pair by putting \(E_0=T_0-2w_{30}\).  Exact
comparison gives
\[
 \boxed{w_{29}\le E_0<w_{28}\le T_0<2w_{28}.}     \tag{10}
\]
Therefore the external row skips 28 and takes 29, exactly as in (7), while
the complete root row must take 28.  Moreover
\[
 T_0-w_{28}<w_{29},                                \tag{11}
\]
so after the global take there is no rank-29 occupation to form (9).

This is the first genuine ancestry restriction beyond an arbitrary finalized
Boolean family: a protected bank may not be frozen across an earlier global
lexicographic decision which its value changes.  The height-30 counterexample
therefore kills schedule-independent bank solvency, but it does not kill a
construction whose ownership law forces every provisional component to
participate in the complete-root lex comparison.  The remaining hereditary
theorem is to prove that all legal packet cuts obey this pooling rule, rather
than merely impose it at (10).

There is a universal form of this veto.  Let \((a_n)\) be any positive coin
sequence and compare greedy rows for \(X=Y+V\), with \(V>0\).  If the two
rows first differ at rank \(j\), their remainders immediately before \(j\)
satisfy
\[
 R_X(j)=R_Y(j)+V.
\]
Hence the first difference has only one possible orientation:
\[
 \boxed{b_j(X)=1,\qquad b_j(Y)=0.}                 \tag{12}
\]
The larger target cannot skip a coin which the smaller target takes.  Thus a
globally lex-consistent ownership schedule has a canonical action at the
first rank affected by frozen value: undo the external-only row and take the
complete-root coin.

For a protected coefficient-six pair \(V=2w_r\), (12) gives an exact
dichotomy.  If the first flip occurs at some \(j<r\), the pair is preempted by
an earlier global recut.  If no such flip occurs, ownership supplies no
additional obstruction before rank \(r\); any fatal state which remains is a
genuine complete-root corridor event.  This is why the pooled-lex law is not
another proof of solvency: it removes external-only counterexamples such as
(7), but deliberately leaves the source-specific isolated-hit problem.

An exact scout over all coefficient-six heights \(15,30,\ldots,300\) found
external constrained insolvency at heights
\[
 30,75,120,135,255,300.
\]
In every case the complete-root row had an earlier flip with the orientation
(12), at ranks
\[
 28,73,119,134,249,299
\]
respectively.  No complete-root fatal corridor occurred in this range.  This
finite audit is evidence for the relevance of the veto, not evidence for the
remaining non-entry theorem.

## 6. Consequence for the live route

The useful ownership question is therefore upstream of (1): does the packet
genealogy restrict the finalized Boolean family strongly enough that its
fixed root charge cannot enter the corridor?  Primitive charges,
reverse-superincreasing separation, the adjacent-gap semigroup, and the
global-lex veto (10) are valid tools for that reachability question.  A
monotone scalar reserve attached after the cut is not an additional tool,
because its margin is already \((K-U)/(3D)\).

The companion exact-arithmetic receipt checks (1)--(11), including arbitrary
rational partitions, the finite height-30 witness, and the first global-lex
divergence:

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/cut_level_reserve_charge_identity.py
```
