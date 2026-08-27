# An all-degree even-symmetric diameter cone

## Theorem

Let `m>=1`, let `S` be any finite set of nonnegative integers, and consider
the real even polynomial

~~~text
P(z)=-z^(2m)+sum_{k in S} a_k z^(2k)+b,                   (1)
~~~

where every `a_k<=0` and `b<0`.  Then the entire real axis is strictly
contained in `{Re P<0}`.  Consequently, for every `R>0`, the segment
`[-R,R]` joins the two opposite asymptotic ends inside one negative component
and has length exactly `2R`; the two outward real tails are contained as well.

This is an all-degree finite-connector theorem on a full coefficient cone.  It
allows vanishing intermediate coefficients and critical-point degeneracies;
neither a critical hub nor a component passport is needed because the real
axis itself supplies the connected carrier.

## Proof

For real `x`, every even power is nonnegative.  Thus

~~~text
-x^(2m) <= 0,
a_k x^(2k) <= 0  for every k,
b < 0.
~~~

Adding gives `P(x)<0`.  This proves strict containment on the complete real
axis, hence on the diameter and both tails.  The Euclidean length from `-R`
to `R` is `2R`.

## The block-L1 family

Taking `m=3`, `S={1}`, and

~~~text
P_{a,b}(z)=-z^6+a z^2+b,
~~~

shows that every `a<=0,b<0` has a contained opposite-end diameter.  In
particular the exact block-L1 counterexample and its complete polyhedral
strict-slack cell lie in a much larger globally covered cone.

The two certificates have different downstream value:

- the diameter covers the whole cone but uses the exact metric budget `2R`;
- the rational adjacent-end connector has length about `1.27764<2` and hence
  carries strict metric slack on its polyhedral cell.

Thus the new theorem does not make the strict cell redundant.  It converts
the complement into an equality-contact transfer problem: on the full cone,
the model selector is solved and only preservation/resolution of the zero
metric defect remains.

## Consequence for the parent programme

Any all-degree tied-face proof may now close the even-symmetric
nonpositive-coefficient cone by the fixed opposite-end template.  Universal
angular adjacency and complete-spoke selection remain false outside this
cone, exactly as the existing no-go theorems state.  The unrestricted Erdős
#1041 theorem remains open because arbitrary tied Newton faces need not be
even or have coefficientwise nonpositive real restriction, and equality
contacts still need a valid finite transfer.

## Formal boundary

Lean proves the all-degree real-axis negativity theorem for an arbitrary
finite coefficient set and checks the diameter algebra.  The exact checker
replays representative rational specializations and the block-L1 inclusion.
The interpretation as two asymptotic ends and its use by stratified transfer
remain ordinary complex-analytic proof.
