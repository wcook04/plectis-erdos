# Exact no-go for pointwise full-fibre `L1` contraction

## Result

The pointwise full-fibre inequality suggested by the fibre-product packet is
false, even with every critical value **strictly** in the open left
half-plane.  Put

```text
x = 1001/1000,
epsilon = x^3+3x-4 = 6003001/10^9,
P(z)=z^6+3z^2-epsilon,
s=2^(1/3).
```

On the simple fibre `P(z_j(s))=s^6=4`, analytically continue the six local
inverse branches with respect to `s`.  Then

```text
sum_(j=1)^6 |z_j'(s)| > 6.                                (1)
```

Thus neither the half-plane critical-value hypothesis, the exact all-sheet
speed-product contraction, nor the complete signed barycentric moment system
implies pointwise full-fibre `L1` contraction.  A successful fibre/monodromy
argument must use a component block, weights, weak majorization, or integrated
loop action.  This theorem does not refute any of those weaker producers.

## Strict critical-value condition

Differentiation gives

```text
P'(z)=6z(z^4+1).
```

The critical points are `0` and the four roots of `z^4=-1`.  At zero the
critical value is `-epsilon`.  At a nonzero critical point, `z^2=+i` or `-i`,
and hence

```text
P(z)=2z^2-epsilon=+2i-epsilon or -2i-epsilon.
```

Every critical value therefore has real part exactly `-epsilon<0`.  In
particular this is not a boundary-only failure caused by a critical value on
the imaginary axis.  The positive real fibre at value `4` contains no
critical point.

## Exact fibre and speed sum

Write `y=z^2`.  The choice of `epsilon` gives

```text
P(z)-4
 = y^3+3y-(x^3+3x)
 = (y-x)(y^2+xy+x^2+3).                                  (2)
```

Let `u,conj(u)` be the roots of the quadratic factor.  They satisfy

```text
u+conj(u)=-x,                 |u|^2=x^2+3.                 (3)
```

Moreover

```text
|u^2+1|^2
 = |u|^4+(u^2+conj(u)^2)+1
 = (x^2+3)^2-x^2-6+1
 = (x^2+1)(x^2+4).                                       (4)
```

Differentiating `P(z_j(s))=s^6` and using
`P'(z)=6z(z^4+1)` gives

```text
|z_j'(s)| = s^5/(|z_j| |z_j^4+1|).
```

There are two roots with `z^2=x` and four roots over `u,conj(u)`.  Equations
(3)--(4) therefore give the exact total

```text
L = 2s^5/(sqrt(x)(x^2+1))
    +4s^5/((x^2+3)^(1/4) sqrt((x^2+1)(x^2+4))).            (5)
```

## Rational strict certificate

Set

```text
A0 = 31748/10000,
D1 = 20031/10000,
D2 = 44759/10000.
```

All quantities are positive.  Exact integer arithmetic gives

```text
A0^3 < 32 = (s^5)^3,
D1^2 - x(x^2+1)^2
  = 393597994999/10^15 > 0,
D2^4 - (x^2+3)((x^2+1)(x^2+4))^2
  = 26040130756897462775941989999/10^30 > 0.
```

Taking the positive cube, square, and fourth roots yields

```text
s^5>A0,
sqrt(x)(x^2+1)<D1,
(x^2+3)^(1/4)sqrt((x^2+1)(x^2+4))<D2.
```

Substitution in (5) gives the fully rational lower bound

```text
L > 2A0/D1+4A0/D2
  = 44510696/7409649
  = 6+52802/7409649
  > 6.                                                       (6)
```

This proves (1).

## Consequence for the packet frontier

`TiedNewtonFaceFibreProduct.md` remains exact: the speed product contracts and
the full signed moment hierarchy holds.  `TiedNewtonFaceFibreL1Duality.md`
also remains exact: on this fibre its Chebyshev interpolation extremum is
strictly larger than the regular-fibre baseline.  What fails is precisely the
new comparison inequality, not either identity feeding it.

The next live desk-3 producer is therefore **not** another proof attempt for
pointwise full-sheet `L1`.  It is the weakest invariant statement that the
counterexample does not address: a monodromy-component block inequality, a
weighted comparison retaining the external factor, or an integrated loop
action with a two-end consumer.  Any such proposal must be tested on this
fibre and on the horizontal-fibre no-go/rescue quintics before it enters a
packet as a plausible universal bridge.

## Verification boundary

The factorization, critical-value computation, speed formula, radical
reduction, and root-counting argument above are an ordinary exact proof.  The
deterministic checker replays every algebraic identity and rational bound.
`TiedNewtonFacePointwiseL1NoGo.lean` checks the rational radical bounds and the
monotone rational lower-sum consumer.  Lean does not formalize the polynomial
root factorization or analytic inverse-branch differentiation in this module.

This is an exact no-go for one stronger selector, not a refutation of Erdős
#1041 and not a proof of the remaining block/integrated selector.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_tied_newton_face_pointwise_l1_no_go.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --jobs 2 ErdosProblems.Erdos1041.TiedNewtonFacePointwiseL1NoGo
```
