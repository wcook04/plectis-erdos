# Static Anchor-Coefficient Order No-Go

## Status

This note gives an exact infinite counterfamily to any proposed argument that
tries to exclude the 25-leading-one fatal state using only:

- odd-denominator rationality;
- a common Mersenne height \(L\);
- divisibility by the anchor factor \(2^{25}-1\);
- periodic binary expansion; or
- the one-rank anchor/scalar frontier law.

The counterfamily is not asserted to be reachable from the \(1/465\) greedy
orbit.  Its point is precisely that orbit history is indispensable.

## The counterfamily

For every \(L>26\), put
\[
  X_L=\frac{2}{2^L-1}=2w_L.
\]
If desired, restrict to \(L\equiv0\pmod{100}\), so the common height is
simultaneously compatible with the period-20 source and the anchor 25.

The scalar front of \(X_L\) is exactly \(L\).  Indeed,
\[
  X_L=2w_L\ge w_L
\]
and
\[
  \frac{2}{2^L-1}<\frac1{2^{L-1}-1}=w_{L-1},
\]
because \(2^L-2<2^L-1\).  Thus this state is fatal at equality:
\[
  f(X_L)=L,
  \qquad
  X_L=2w_{f(X_L)}.
\]

Now use the anchor-25 coefficient notation
\[
  R_L=(2^L-1)X_L,
  \qquad
  B_L=(2^{25}-1)R_L,
  \qquad
  c_L=(2^{25}-1)X_L.
\]
Then
\[
  R_L=2,
  \qquad
  B_L=2(2^{25}-1),
  \qquad
  c_L=\frac{B_L}{2^L-1}.
\]
The integer \(B_L\) has binary ones in precisely the exponent positions
\(1,2,\ldots,25\).  Consequently its left-padded \(L\)-bit periodic word
begins at digit
\[
  k=L-25
\]
with exactly 25 consecutive ones, followed by a zero.  Since
\(k+25=L=f(X_L)\), this is exactly the leading-one configuration forced by a
fatal gap in `AnchorFourFiveDynamicOwnershipFlow.md`.

## Consequence

There are infinitely many states satisfying every static coefficient/order
condition above while also exhibiting fatal escape.  In particular, no
argument based only on the denominator of \(B/(2^L-1)\), its binary order, the
factor \(2^{25}-1\), or its periodic-word shape can exclude a 25-run.

The remaining \(1/465\) theorem must use a reachability invariant of the
affine mask recurrence
\[
  R' = UR-e_nT_n,
  \qquad e_n\in\{0,1\},
\]
together with the actual period-20 source or the selected-divisor history.
Static common-height state membership is too coarse.
