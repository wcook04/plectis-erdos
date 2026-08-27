# Connected-cluster Bergman certificate

## Status

This note proves an independently meaningful sufficient theorem for Erdős
#1041.  It handles an entire multi-critical lemniscate component at once and so
does not choose a preferred critical hub across a tie.  It does **not** prove
the unrestricted problem; the remaining cluster-defect forcing statement is
recorded precisely below.

It also corrects a tempting but invalid compactness argument: although each
labelled marked-hub length can be plurisubharmonic, the minimum of those
functions need not be.  For example, the minimum of the harmonic functions
`Re z + Re z^2` and `-Re z + Re z^2` has a strict local maximum at zero.

## The theorem

Let `C` be a connected component of `{z : |f(z)| < t}`, where `f` is monic and
`t > 0` is a regular level.  Let `k >= 2` be the number of zeros in `C`, counted
with multiplicity, and suppose that at least two of those zeros have distinct
locations.  Put

```
A_C = Area(C),
q_C = max {|f(c)|/t : c in C and f'(c)=0}.
```

Then two distinct zero locations in `C` can be joined by a curve `Gamma` in
`C` satisfying

```
length(Gamma)^2
  <= (2 A_C/pi) log((1 + q_C^(2/k))/(1 - q_C^(2/k))).          (1)
```

Consequently, with `alpha_C = A_C/(pi t^(2/n))`,

```
alpha_C log((1 + q_C^(2/k))/(1 - q_C^(2/k))) <= 2             (2)
```

implies `length(Gamma) <= 2 t^(1/n)`.

## Proof

A polynomial lemniscate component is simply connected.  Choose a Riemann map
`phi : D -> C`.  Up to a unimodular constant,

```
B = f(phi(z))/t
```

is a finite Blaschke product of degree `k`, with zeros
`a_1,...,a_k` counted with multiplicity.  Let

```
U_epsilon = {|B| < q_C + epsilon},
r_epsilon = (q_C + epsilon)^(1/k),
```

where `0 < epsilon < 1-q_C`.

Every critical point of `B` lies in `U_epsilon`.  Every component of
`U_epsilon` is simply connected: a hole contains no zero, so `log |B|` is
harmonic there with constant boundary value, which is impossible unless it is
constant.  If `U_epsilon` had `s` components and the restrictions of `B` had
degrees `d_1,...,d_s`, Riemann--Hurwitz would count

```
sum (d_nu - 1) = k-s
```

critical points in it.  But all `k-1` critical points of `B`, counted with
multiplicity, lie there.  Hence `s=1`.

Since `|B(z)|` is the product of the pseudohyperbolic distances
`rho(z,a_j)`,

```
U_epsilon subset union_j D_rho(a_j,r_epsilon).
```

The left side is connected and contains every `a_j`; hence the disc
intersection graph is connected.  Because at least two zero locations are
distinct, some graph edge joins unequal centers.  For this pair,

```
rho(a_i,a_j) <= 2 r_epsilon/(1+r_epsilon^2).
```

Letting `epsilon` decrease to zero and writing `r=q_C^(1/k)` gives

```
1 - rho(a_i,a_j)^2
  >= ((1-r^2)/(1+r^2))^2.
```

The sharp Bergman estimate for the image under `phi` of the hyperbolic
geodesic from `a_i` to `a_j` is

```
length(Gamma)^2 <= (A_C/pi) log(1/(1-rho(a_i,a_j)^2)).
```

Substitution proves (1), and (2) proves the length conclusion.  The two scalar
steps are formalized in `ConnectedClusterBergman.lean`.

## Capacity form and the remaining implication

Let `kappa_C = cap(cl C)/t^(1/n)`.  Polya's area--capacity inequality gives
`alpha_C <= kappa_C^2`, so it is sufficient that

```
kappa_C^2 log((1 + q_C^(2/k))/(1 - q_C^(2/k))) <= 2,
```

equivalently

```
q_C <= tanh(1/kappa_C^2)^(k/2).                              (3)
```

At the Fekete scale `t=R^n`, this yields a path of length at most `2R < 2`.
Thus it closes every Fekete-scale component satisfying (2) or (3), including
components formed by simultaneous critical-value ties.

The exact residual is the following **cluster-defect forcing problem**:

> Show that some node `C` of the critical merge tree satisfies (2).

Using the existing exact component-capacity formula
`kappa_C = exp(-Sigma_C/n)`, failure at every node would force

```
q_C > tanh(exp(2 Sigma_C/n))^(k_C/2)
```

at every node.  This is a much narrower target than a generic tie
classification, but it is not proved here.  In particular, neither taking a
minimum of marked-hub functions nor a naive edge-area average establishes it.

