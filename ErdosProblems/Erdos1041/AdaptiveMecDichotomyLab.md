# Erdős #1041: the adaptive minimum-enclosing-disk dichotomy is false

## Why this was the strongest direct extension of the quartic theorem

Let the roots lie in their minimum enclosing disk `D(q,R)`.  Because the
original roots lie in the open unit disk, `R<1`.  After writing

\[
  z_k=q+R w_k,
\]

all normalized roots lie in the closed unit disk.  Two elementary normalized
certificates would each solve Erdős #1041 immediately:

1. a root chord on which `product_k |w-w_k| <= 1`; or
2. two radial arms from `0` to distinct normalized roots on which the same
   product is at most one.

Indeed, rescaling multiplies the product by `R^n<1`.  A chord has length at
most `2R<2`, while two radial arms have combined length at most `2R<2`.
Pendyala's degree-four proof uses exactly this scheme: a sufficiently close
pair supplies the chord, and otherwise the four-point radial lemma supplies
two arms.

The literal radial lemma is false for five points, but its first falsifier has
a safe chord.  The correct next question was therefore the adaptive
dichotomy, not another radial-only search:

> For every normalized root set, is there either one safe root chord or two
> safe radial arms through the minimum-enclosing-disk center?

The answer is no already in degree five.

## Exact rational witness

Use the rational parametrization of the unit circle

\[
  u(s)=\left(\frac{1-s^2}{1+s^2},\frac{2s}{1+s^2}\right)
\]

with

\[
  s=0,\quad \frac{48031}{76394},\quad \frac{347397}{99299},
  \quad-\frac{203651}{55446},\quad-\frac{67203}{94835}.
\]

Put `r=9999/10000` and take the five roots `z_k=r u(s_k)`.  They are distinct
Gaussian rationals and all have norm exactly `r<1`.

The exact checker evaluates the factored polynomial at fourteen rational
waypoints:

- one waypoint on each of the radial arms with indices `1,2,3,4`; and
- one waypoint on every one of the ten root chords.

At every waypoint the squared modulus is strictly greater than one.  Thus at
most one radial arm is safe, and no root chord is safe.  The smallest squared
escape margin remains positive after the strict scale `r<1`; the receipt
stores its exact numerator and denominator rather than a floating-point
approximation.

## The center really is the minimum-enclosing-disk center

The directions with indices `0,2,4` have the positive rational barycentric
weights

\[
 \frac{6964549963}{23346120591},\qquad
 \frac{6190115973196675}{13763377639945224},\qquad
 \frac{670760794587883}{2662487780657976},
\]

which sum to one and whose weighted vector sum is zero.  For any disk center
`c`, the weighted mean of the squared distances from these three unit points
to `c` is therefore

\[
  \sum_i \lambda_i |u_i-c|^2=1+|c|^2\ge 1.
\]

Every disk containing them has radius at least one.  Since the unit disk
contains all five directions, it is their minimum enclosing disk.  After
scaling, `D(0,r)` is the minimum enclosing disk of the five roots.  The
counterexample therefore targets the adaptive MEC mechanism itself, not a
bad choice of center.

## Corpus-wide selection receipt

This probe was selected only after comparing three structurally distinct
full-problem fronts.

| Problem/front | Central representation | Strongest landed asset | Contrary evidence | Cheapest discriminating probe | Stop condition |
|---|---|---|---|---|---|
| #269 integral-tail escape | bounded-radix cocycle over a two-torus rotation | exact infinite tail recurrence and integral-or-cofinal-far dichotomy | eliminating integral states alone does not handle rational denominators coprime to `30`; finite observers and degree-two source coboundaries are already eliminated | test the cofinal zero-gap divisor condition and identify its parity cocycle | stop if the condition only eliminates the denominator-one branch or requires a new parity-equidistribution theorem |
| #1049 at `3/2` | q-Apéry/Padé integral forms with moving source primes | exact one-coordinate divisor consumer and analytic-aware unimodular recombination | the determinant inequality forces very large coefficient height, and fixed-prime persistence is false | compare the exact moving-prime window law with the required all-start height/decay inequality | stop if the source gives no uniform height gain beyond the determinant obstruction |
| #1041 adaptive MEC geometry | minimum-enclosing disk, root chords, and radial arms | the complete quartic theorem and the immediate all-degree metric/containment consumer above | radial-only degree-five witnesses exist, but none had tested the adaptive chord fallback | maximize the minimum of the best chord cost and second-best radial-arm cost | exactify the first score above one, then abandon the entire MEC dichotomy |

The #1041 probe crossed its falsifier at normalized score about `1.001845` and
has now been exactified.  That closes the direct all-degree extension of the
quartic proof.  The surviving constructive front is no longer MEC geometry:
it is a polynomial-adapted critical or curved hub, especially a theorem using
minimal critical value without requiring straight spokes.

## Claim boundary

This is an exact counterexample to a proof mechanism, not to Erdős #1041.
The polynomial still has short curves in its unit lemniscate; the checker does
not claim otherwise.  What is eliminated is the disjunction consisting of all
root chords and all two-arm broken lines through the minimum-enclosing-disk
center.

Replay:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_pendyala_radial_extension.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_pendyala_radial_extension.py --check
```

Canonical receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1041_adaptive_mec_dichotomy_receipt.json`.
