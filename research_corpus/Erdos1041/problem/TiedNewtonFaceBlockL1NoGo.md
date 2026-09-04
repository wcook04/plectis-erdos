# Exact no-go for pointwise component-block `L1` contraction

## Result

The pointwise block inequality suggested by the fibre-interpolation route is
false even when the relevant negative half-plane preimage consists of one
connected component carrying every sheet.

Put

```text
x = 999/1000,
epsilon = x^3+3x-4 = -5997001/10^9,
Q(z) = -z^6-3z^2+epsilon,
s = 2^(1/3).
```

Then every critical value of `Q` lies strictly in the open left half-plane,
`Omega_-={Re Q<0}` is connected, and

```text
Q|Omega_- : Omega_- -> {Re w<0}
```

has degree six.  Hence the six points on the fibre `Q(z)=-s^6=-4` form one
nontrivial monodromy end block.  For analytic inverse branches
`Q(z_j(s))=-s^6`,

```text
sum_(j=1)^6 |z_j'(s)| > 6.                                  (1)
```

Thus the regular-fibre pointwise bound

```text
sum_(j in E(U)) |z_j'(s)| <= |E(U)|
```

is false for an actual component block, not only for a union of unrelated
one-ended components.  A successful fibre route must now use external
weights, weak majorization of selected sheets, or integrated loop action.

## Critical values and the single component

Differentiation gives

```text
Q'(z)=-6z(z^4+1).
```

The five critical points are simple.  At `z=0` the critical value is
`epsilon`.  At `z^4=-1`, one has `z^6=-z^2` and therefore

```text
Q(z)=epsilon-2z^2 in {epsilon+2i, epsilon-2i}.
```

All five critical values have real part `epsilon<0`.

For each component `U_alpha` of `Omega_-`, the component-passport theorem
gives

```text
degree(Q|U_alpha)=1+ram(U_alpha),
```

where `ram(U_alpha)` is total critical ramification in that component.
Summing the component degrees gives six.  Every critical point belongs to
`Omega_-`, and their total ramification is five, so

```text
6 = sum_alpha degree(Q|U_alpha)
  = number_of_components + 5.
```

Consequently `Omega_-` has exactly one component and its end block has all
six labels.

## Exact fibre and speed sum

The equation `Q(z)=-4` is

```text
z^6+3z^2-epsilon=4.
```

Writing `y=z^2` gives the exact factorization

```text
y^3+3y-(4+epsilon)
  = (y-x)(y^2+xy+x^2+3).                                   (2)
```

The quadratic discriminant is `-3x^2-12<0`, so the fibre is simple.
Differentiating `Q(z_j(s))=-s^6` gives

```text
|z_j'(s)| = 6s^5/|Q'(z_j(s))|.
```

Summing the two square roots above each of the three roots of (2) yields

```text
L =
  2s^5/(sqrt(x)(x^2+1))
  + 4s^5/((x^2+3)^(1/4) sqrt((x^2+1)(x^2+4))).              (3)
```

The nonreal-root norm identities used in (3) follow from
`y^2+xy+x^2+3=0):

```text
|y|^2=x^2+3,
|y^2+1|^2=(x^2+1)(x^2+4).
```

Use the rational bounds

```text
A0=31748/10000 < s^5,
D1=20031/10000 > sqrt(x)(x^2+1),
D2=44759/10000
   > (x^2+3)^(1/4) sqrt((x^2+1)(x^2+4)).
```

They are certified by

```text
A0^3 < 32=(s^5)^3,
D1^2-x(x^2+1)^2
  =24393621995001/10^15 > 0,
D2^4-(x^2+3)((x^2+1)(x^2+4))^2
  =2666045458759613463223942009999/10^30 > 0.
```

Therefore

```text
L > 2A0/D1+4A0/D2
  = 44510696/7409649
  = 6+52802/7409649 > 6,
```

which proves (1).

## Consequence for the live producer

The stronger pointwise component-block Chebyshev conjecture is retired.  The
exact block duality remains valid, but its extremal constant can exceed the
regular baseline on the very component selected by the half-plane topology.
The next discriminating order is:

1. externally weighted block inequalities retaining the complementary factor;
2. weak majorization sufficient only for two sheets;
3. integrated excess along a monodromy loop, with equality rigidity.

This result does not refute any of those statements, the weighted
monodromy-loop representation, or unrestricted Erdős #1041.

## Formal boundary

The companion Lean module checks the strict sign of `epsilon`, the rational
radical bounds, and the monotonicity step producing `L>6`.  The proper-cover
component passport, the fibre factorization, and analytic inverse-branch
calculus are ordinary exact mathematics here.  The symbolic checker replays
those algebraic identities and the total-ramification count.
