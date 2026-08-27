# Erdős 1041: positivity of the charged lifetime terms does not force allocation

## Status

This note executes successor packet desk 2 against the source-current
full-energy-charged lifetime inequality. It proves an exact abstraction no-go:
the strict positivity of the node charges `J_v` and singleton charges is not,
by itself, a quantitative obstruction to a rapid labelled comb. A proof of the
target must couple those charges to attachment ancestry, root separation, or a
complete metric consumer.

This does not refute `(LC3)`, any polynomial theorem, or Erdős 1041. It removes
one tempting but insufficient composition of the new result.

## 1. The node charge has no uniform positive floor

For an internal merge node of size `k`, birth level `beta`, death level
`delta`, and positive leaf energy `E`, the joint assimilation defines

```text
J_k(E; beta,delta)
  = integral_beta^delta
      [max{t^(2/k) E, B_k(t)} - B_k(t)] dt/t,

B_k(t)=2/lambda_k(beta/t).
```

The elementary inequality

```text
0 <= max{x,y}-y <= x                     (x>=0, y>=0)
```

gives

```text
0 <= J_k(E;beta,delta)
   <= E integral_beta^delta t^(2/k) dt/t
   = (kE/2)(delta^(2/k)-beta^(2/k))
   <= kE/2,                               (1)
```

whenever `0<=beta<delta<=1`. The final bound is independent of the Bergman
barrier. Therefore

```text
J_k(E;beta,delta) -> 0 as E -> 0+.
```

For every fixed `E>0`, the charge is strictly positive at a genuine node,
as proved in `SixReturnJointAssimilation20260826.md`; equation (1) shows that
this strict positivity is not uniform over the scalar parameter space.

## 2. Exact finite-tree compatibility theorem

Let `V` be any finite collection of internal nodes with prescribed sizes
`k_v>=2`, birth/death intervals, and uncharged lifetime cost

```text
L = sum_(v in V) I_(k_v)(r_v).
```

Suppose only that `L<n/4`, and put `s=n/4-L>0`. For any positive weights
`e_v` with

```text
sum_v k_v e_v < s,
```

choose node energies `E_v=e_v`. By (1),

```text
(1/2) sum_v J_v < s/4.                    (2)
```

Now choose arbitrary positive singleton charges `q_i` with

```text
sum_i q_i < 2s.
```

Then

```text
L + (1/2)sum_v J_v + (1/4)sum_i q_i
  < L + s/4 + s/2
  < n/4.                                  (3)
```

Such positive finite families always exist: distribute any sufficiently small
rational fraction of `s` over the finitely many nodes and leaves. Hence every
strictly feasible uncharged scalar lifetime model admits strictly positive
charged decorations which remain feasible. The same conclusion holds with any
prescribed positive upper ceilings on the charges after shrinking the chosen
weights further.

### Theorem (charged-lifetime scalar allocation no-go)

The uncharged lifetime inequality plus the assertions `J_v>0` and
`q_i>0` cannot, without an additional quantitative relation tying these terms
to the labelled merge geometry, force a target-deciding node, rule out an
abstract rapid comb, or imply an attachment-compatible root pair.

The proof is (1)--(3). It is an abstraction theorem: actual polynomial
energies are not free parameters. Precisely that non-freedom is now the only
possible source of additional forcing.

## 3. Consequence for the live proof frontier

The first unjustified arrow in the tempting composition was

```text
strictly positive LC3 charges
  -> uniform loss on a long comb
  -> one target-deciding component.
```

The first arrow is false at the scalar level. The next admissible producer must
prove one of the following genuinely polynomial statements:

1. an attachment-weighted lower bound on a sum of `J_v` or singleton charges;
2. a tradeoff saying small charges force Gram/near-Fekete structure already
   covered by a connector consumer;
3. a root-labelled antichain inequality preventing every charge from being
   spent outside one selected component;
4. a direct pair/block selection theorem using the charges as weights.

This makes the best next experiment a coupled lower-bound or dichotomy, not a
larger scalar tree optimization with positivity as its only new input.

## 4. Evidence and claim boundary

Ordinary exact mathematics proves the pointwise maximum inequality, the
integral bound (1), and the finite-tree construction (2)--(3).
`ChargedLifetimeAllocationNoGo.lean` checks the aggregate slack construction
and its consumer-facing form. The deterministic checker replays rational
instances and the exact pointwise domination.

No unrestricted path theorem is claimed. The result does not show that actual
polynomial energies can be prescribed independently; instead it proves that a
future successful argument must use the constraints preventing such
independent prescription.
