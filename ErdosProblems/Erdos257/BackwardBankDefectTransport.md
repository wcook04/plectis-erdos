# Backward-bank defect transport

The forward anti-compression theorem in
`NegacyclicSaturationModulus.md` leaves one precise escape: deficit mass
selected at a rank below a forbidden source may already be present in the
bank.  That escape is real.  There is an infinite family in which one safe
earlier rank starts a Boolean carry chain, later safe pure-bit deficits carry
the discrepancy through a linear interval of valuations, and the first
unavailable correction is exactly a new endpoint divisor.

This is not a rational Boolean subsum.  It is an exact counterexample to a
backward-rank descent argument: a forbidden pivot need not force an earlier
forbidden pivot.  An earlier provider can be endpoint-safe, and the subsequent
carry transports rather than dissipates endpoint debt.

## 1. Parameters

Let

\[
 T\equiv 8\pmod {42},\qquad T\geq 50,
 \qquad R=7T-12,
\]

and define

\[
\begin{aligned}
 d_0&=2T-3,&
 d_1&=\frac{13T-20}{7},&
 d_2&=\frac{13T-20}{3},\\
 A&=\frac{10T-24}{7},&
 C&=2T-6,&
 V&=\frac{R-2}{3},&
 W&=\frac{8T-16}{3}.
\end{aligned}                                                    \tag{1}
\]

All displayed quantities are integers.  They satisfy

\[
 T-2<A<C<V<W.                                      \tag{2}
\]

For a visible rank \(d\), write

\[
 D_{R,d}=2^{R-(d-(R\bmod d))}-\delta_R(d)           \tag{3}
\]

for the exact deficit from the common dyadic capacity.  Let

\[
 E=\{T-2\}\mathbin\cup
   \bigl(\{A,A+1,\ldots,V-1\}\setminus\{C\}\bigr), \tag{4}
\]

and, for \(v\in E\), put \(e_v=R-v\).

## 2. The safe correction bank

The source \(d_0\) is forbidden because

\[
 2R+3=7d_0.                                         \tag{5}
\]

In contrast, \(d_1<d_0<d_2\), and both \(d_1,d_2\) are endpoint-safe.
Indeed, for \(q\in\{1,2,3,4\}\),

\[
 2R+q-7d_1=T-4+q,
 \qquad
 2R+q-3d_2=T-4+q,                                  \tag{6}
\]

and these positive remainders are smaller than the corresponding ranks.
Thus \(d_1\) is a genuine earlier safe bank atom.

Every correction rank \(e_v\) is also endpoint-safe and has the pure deficit

\[
 D_{R,e_v}=2^v.                                     \tag{7}
\]

To see this, \(R=e_v+v\), while

\[
 3v\leq 3(V-1)=R-5.
\]

Hence the height-one block is short and its deficit is exactly \(2^v\).
Moreover, modulo \(e_v=R-v\), the four endpoint integers have remainders
\(2v+q\).  The inequality \(3v+q<R\) for \(1\leq q\leq4\) makes each
remainder strictly between zero and \(e_v\).

## 3. Exact transport theorem

The safe ranks in (6)--(7) reproduce the forbidden source and then expose a
new forbidden pivot at a higher valuation.  Precisely,

\[
 \boxed{
 v_2\!\left(
 D_{R,d_1}+D_{R,d_2}
 +\sum_{v\in E}D_{R,e_v}
 -D_{R,d_0}
 \right)=V.}                                      \tag{8}
\]

The rank

\[
 d_F=R-V=\frac{2R+2}{3}                             \tag{9}
\]

has

\[
 D_{R,d_F}=2^V,
 \qquad 3d_F=2R+2,                                 \tag{10}
\]

so it is exactly the forbidden label-two pivot exposed by (8).  After that
pivot is charged, the remaining discrepancy begins at the still higher
valuation \(W\):

\[
 \boxed{
 v_2\!\left(
 D_{R,d_1}+D_{R,d_2}
 +\sum_{v\in E}D_{R,e_v}
 -D_{R,d_0}-D_{R,d_F}
 \right)=W.}                                      \tag{11}
\]

Thus a forbidden label-three source is not killed by safe carry propagation.
One earlier safe bank atom and later safe atoms transport its local endpoint
defect to a forbidden label-two pivot, with exact agreement through all bits
below \(V\).  Since \(V=(7T-14)/3\) and \(W=(8T-16)/3\), both the safe carry
chain and the post-transport agreement depth are unbounded.

## 4. Proof of the carry identity

The Boolean block formula gives

\[
\begin{aligned}
D_{R,d_0}
 &=2^{T-3}+(2^T-1)
   \left(2^{2T-6}+2^{4T-9}\right),\\
D_{R,d_1}
 &=(2^{(3T+4)/7}-1)
   \left(2^{T-4}+2^{T-4+d_1}+2^{T-4+2d_1}\right),\\
D_{R,d_2}
 &=2^W-2^{T-4}.                                    \tag{12}
\end{aligned}
\]

The first block of \(D_{R,d_1}\) is \(2^A-2^{T-4}\), and its second
block begins at \(2A>W\).  The first long block of \(D_{R,d_0}\) begins
at \(C\) and extends past \(W\), while its second begins above \(W\).
Consequently, with

\[
 M=D_{R,d_1}+D_{R,d_2}-D_{R,d_0},
\]

one has the exact low-bit identity

\[
 M\equiv -2^{T-2}+2^A+2^C\pmod {2^W}.             \tag{13}
\]

On the other hand, (4) and (7) give

\[
 \sum_{v\in E}D_{R,e_v}
 =2^{T-2}+2^V-2^A-2^C.                            \tag{14}
\]

Adding (13) and (14) proves (8).  Modulo \(2^{W+1}\), the only remaining
term at exponent \(W\) is the leading endpoint \(2^W\) of
\(D_{R,d_2}\).  This proves the strict valuation in (11), not merely a
congruence lower bound.

There is also a literal carry-by-carry reading.  Before each pure correction
\(2^v\), in increasing order over \(E\), the current discrepancy has exact
valuation \(v\).  The first correction moves valuation from \(T-2\) to
\(A\); the corrections from \(A\) upward carry successively, except that the
existing bit at \(C\) supplies that step without a correction.  The chain
ends at \(V\), precisely where endpoint safety fails because the next label
is two.

## 5. Consequence for the propagation programme

The strict mod-six capacity contraction remains valid for a nonduplicating
safe migration forest.  The theorem above shows why the missing global
assignment cannot be obtained from backward rank descent, endpoint safety of
the first bank atom, or any fixed low-bit state.  Safe lower-carry atoms can
move a forbidden endpoint charge to a different endpoint phase over an
unbounded valuation distance.

What remains possible is an ownership theorem on disjoint binary blocks (or
an equivalent cocycle tied to the target equation).  Such a theorem must
charge the earlier atom \(d_1\) when its blocks enter the carry chain and must
also retain the transported label-two debt at \(d_F\).  Treating a whole
earlier deficit as either wholly unused or wholly consumed is too coarse:
the block formula permits different disjoint blocks of one deficit to enter
different carries.

The result does not assert that (11) can be closed modulo \(2^R+1\), and it
does not construct a rational infinite Boolean subsum.  Its unconditional
content is the exact infinite defect-transport family and the resulting
failure of backward-rank descent as the missing propagation law.

## 6. Reproduction

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/backward_bank_defect_transport.py
```

The script checks the parameter identities, endpoint classes, Boolean block
formula, every individual carry step, and the two strict terminal valuations
for a finite regression range.  Equations (1)--(14), not the size of that
range, prove the family.
