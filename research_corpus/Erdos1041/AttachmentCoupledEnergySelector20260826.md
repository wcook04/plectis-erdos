# Erdős 1041: the attachment-coupled selector, exact quartic no-go, and transport ceiling

Status, 2026-08-26: one exact actual-polynomial no-go, one sharp abstract
weighted-tree selector, and one exact transport identity showing why that
selector does not by itself close the polynomial metric consumer. Unrestricted
Erdős 1041 remains open.

This note assimilates Type-B returns 007 and 008 of
`erdos1041_20260826_return_stream_02`. Return 007's homothetic product
inequality is correct but already occupied by
`arbitrary_modulus_root_ray_product_contraction`; it does not fix the moving
root-index obstruction. Return 008 contains the genuinely new mathematics
below.

## 1. An actual quartic kills the terminal weighted-young lift

Let

```text
F(z)=(z^2-1/100)(z^2-1/4),  a=1/10,  b=1/2.
```

The inner and terminal merge moduli are respectively

```text
alpha=1/400,  beta=9/625,  beta/alpha=144/25>4.
```

Moreover

```text
|F'(+-a)|=6/125,    |F'(+-b)|=6/25,
Y_(+-a)^2=625/576,  Y_(+-b)^2=1/4.
```

Thus the two terminal-young outer roots carry only `144/769<1/2` of the
entrance energy, with exact deficit `481/1538`. This promotes the earlier
four-leaf invariant-ledger countermodel to an actual polynomial witness.
Symmetry leaves two terminal critical values tied; the displayed inequalities
are strict, so the failure persists under sufficiently small generic
perturbations. This refutes only the terminal-node weighted-young lift, not
Erdős 1041.

## 2. Sharp attachment-coupled selector

Let a rooted tree have `k>=2` leaves with weights `w_i>0`. A proper descendant
edge `u` has length `x_u>=0`, descendant set `S_u`, and energy
`E_u=sum_(i in S_u) w_i`. Put

```text
W=sum_i w_i,
G=(product_i w_i)^(1/k),
C=sum_u x_u E_u(W-E_u),
d(i,j)=sum_u x_u 1_{exactly one of i,j lies in S_u},
D=1-sum_i(w_i/W)^2.
```

For every `lambda>0`, some distinct ordered pair satisfies

```text
w_i w_j exp(-lambda d(i,j))
 >= [D W^2/(k(k-1))]
    exp(-2 lambda C/(D W^2))                         (AC1)
 >= G^2 exp(-2 lambda C/(k(k-1)G^2)).               (AC2)
```

Proof: with `p_i=w_i/W`, an edge separates two independent `p`-leaves with
probability `2(E_u/W)(1-E_u/W)`. Hence

```text
sum_(i!=j) p_i p_j d(i,j)=2C/W^2.
```

Condition on distinct leaves and apply Jensen to `exp(-lambda x)`. The largest
of the `k(k-1)` ordered summands is at least their arithmetic average, proving
`(AC1)`. AM-GM over all unordered products gives

```text
D >= k(k-1)G^2/W^2.
```

Since `z exp(-a/z)` is increasing for `z>0`, `(AC2)` follows. Equal weights on
an equal-edge star give equality throughout.

If `a=i meet j` is the selected pair's lowest common merge, then
`d(i,j)=A_i(a)+A_j(a)`. At `lambda=2`, AM-GM gives

```text
w_i exp(-2A_i(a))+w_j exp(-2A_j(a))
 >= 2W sqrt(D/(k(k-1))) exp(-2C/(D W^2))              (AC3)
 >= 2G exp(-2C/(k(k-1)G^2)).                         (AC4)
```

The returned hard trade-off is also valid. For `0<delta<1`, Markov under the
conditional distinct-pair distribution leaves mass at least `1-delta` on
pairs with

```text
d(i,j)<=2C/(delta D W^2)<=2C/(delta k(k-1)G^2).
```

Averaging on that good set yields one such pair with
`w_iw_j>=(1-delta)G^2`.

## 3. Stronger source-current conclusion: common ancestry returns exactly

The return proposes that moving from the terminal node `v` to the pair's
lowest common merge `a` cancels old common ancestry. It cancels it from the
tree distance, but not from the actual singleton entrance charge consumed by
the polynomial identities.

Write

```text
Y_(i,v)=T_(a,v) Y_(i,a),
B_a(v)=the common attachment age from a to v.
```

The propagation ledger and `EntranceEnergyRatioBridge` give the exact common
factor identity

```text
beta_a^(1/k_a)/T_(a,v)
 = beta_v^(1/k_v) exp(-B_a(v)).                        (TR1)
```

Consequently, for every leaf below `a`,

```text
q_i^2
 = beta_a^(2/k_a) Y_(i,a)^2 exp(-2A_i(a))
 = beta_v^(2/k_v) exp(-2B_a(v))
   Y_(i,v)^2 exp(-2A_i(a)).                            (TR2)
```

Thus `(AC3)` transports to a local charge pair only after multiplication by
the node-wide factor `beta_v^(2/k_v)exp(-2B_a(v))`. That factor can be
arbitrarily small from the abstract ledgers currently available. The proposed
"one compatibility theorem" is therefore not a formal rewrite waiting to be
done: it is exactly the missing polynomial-specific control of common ancestry.

This is the useful strengthened verdict. The attachment selector is correct
and should be retained, but it does **not** close the abstract Type-B allocation
problem in the currency consumed by the existing metric theorem. A completion
still needs either:

1. a consumer invariant under the factor in `(TR2)`; or
2. a polynomial-specific bound making the common-age factor pay through
   lifetime, charge, capacity, or another target-deciding global budget.

## 4. Validation

`scripts/check_erdos1041_attachment_coupled_energy_selector.py` replays the
quartic in exact rational arithmetic, checks the edge-separation identity on
deterministic rational trees, and tests `(AC1)--(AC4)` in high-precision
logarithmic arithmetic. The returned float stress script is not authority: its
fixed absolute tolerance fails on sufficiently imbalanced weights even though
the theorem is true. `AttachmentCoupledEnergySelector20260826.lean` checks the
exact quartic inequalities and the scalar common-ancestry factorisation in
`(TR2)`.

