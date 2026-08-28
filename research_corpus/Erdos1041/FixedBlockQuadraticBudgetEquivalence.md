# Erdős 1041: fixed-block quadratic budget equivalence

Status, 2026-08-27: exact conditional consumer and proof-boundary repair.  The
quadratic budget used by return stream 08 is sufficient, but it is not a
consequence of the source-current lifetime and full-fibre theorems.  It is a
variational rewriting of the still-missing average-length bound on one fixed
nontrivial monodromy block.  Unrestricted Erdős 1041 remains open.

## 1. The exact variational identity

Let `B` be a finite set of size `k`, and let `v_nu:[0,1]->[0,infinity)` be
measurable and integrable.  Give `B x [0,1]` the probability measure obtained
from normalized counting measure on `B` and Lebesgue measure.  Put

```text
Lbar = (1/k) sum_(nu in B) integral v_nu,
A(lambda) = (1/k) sum_(nu in B) integral lambda_nu,
E(lambda) = (1/k) sum_(nu in B) integral v_nu^2/lambda_nu,
```

where every `lambda_nu` is positive and measurable.  Then

```text
Lbar^2 <= A(lambda) E(lambda),                            (QB1)
inf_(lambda>0) A(lambda) E(lambda) = Lbar^2.              (QB2)
```

Indeed, `(QB1)` is Cauchy--Schwarz on the whole product space, applied to
`sqrt(lambda)` and `v/sqrt(lambda)`.  Conversely take
`lambda_epsilon=v+epsilon`.  Since the product measure has mass one,

```text
A(lambda_epsilon)=Lbar+epsilon,
E(lambda_epsilon)<=Lbar,
```

so the products have limsup at most `Lbar^2`; `(QB1)` gives the reverse
inequality.  If `v` is positive almost everywhere, equality is attained by
every `lambda=c v`, `c>0`.

Thus the proposed estimate `limsup A_m E_m<=4` is neither a new energy gain nor
a consequence of choosing clever lifetime weights.  After optimizing those
weights it says exactly

```text
limsup_m ( (1/k) sum_(nu in B) L_(nu,m) ) <= 2,           (QB3)
```

where `L_(nu,m)=integral |z'_(nu,m)|` is the length of one entire lift.

## 2. The valid fixed-block consumer

Suppose now that, for every `m`, the curves `z_(nu,m)` are the complete lifts
of one based value-plane loop, all lie in `{|Q|<=1}`, and continuation induces
the same nontrivial cycle `sigma` on the fixed block `B`.  If the quadratic
budget has limsup at most four, `(QB1)` gives

```text
min_(nu in B) L_(nu,m) <= 2+o(1).
```

Selection occurs after integration, so it chooses an entire lift, not a sheet
that changes with time.  Finiteness of `B` fixes a selected `nu` on a
subsequence.  That lift joins the distinct roots `a_nu` and `a_(sigma nu)`.

For normalized roots in the closed unit disc, nearest-point projection `pi`
to the disc fixes the endpoints and decreases every root distance:

```text
|pi(z)-a_j| <= |z-a_j|.
```

It therefore does not increase length or `|Q|`.  Constant-speed
parametrization, Arzelà--Ascoli, and lower semicontinuity of length give a
limiting root-to-root path of length at most two in `{|Q|<=1}`.  This part of
the stream-08 return is correct.

### 2.1 Fixed-point compensation: the exact allocation criterion

The single-cycle hypothesis can be weakened, and doing so exposes exactly
where a whole-fibre estimate loses the endpoint information.  Let `sigma` be
the continuation permutation of a finite sheet set `B`, and write

```text
M={nu:sigma(nu) != nu},       F={nu:sigma(nu)=nu}.
```

Let `L_nu` be the complete-lift lengths and let `C>=0`.  If `M` is nonempty,

```text
sum_(nu in B) L_nu <= C |B|,
sum_(nu in F) L_nu >= C |F|,                         (FC1)
```

then

```text
sum_(nu in M) L_nu <= C |M|,
```

so some moved sheet has `L_nu<=C`.  Its lift joins two distinct roots.  This
is just subtraction in `(FC1)`, but it is the exact allocation statement the
global average needs.  In particular:

* if `sigma` is a derangement on `B`, the fixed-sheet condition is empty;
* for the quadratic budget, `(QB1)` and `A(lambda)E(lambda)<=4` give the first
  inequality with `C=2`, so it is enough that the fixed lifts have average
  length at least two;
* one may instead restrict the variational identity to `M`, recovering the
  original safe-block formulation without paying for fixed sheets at all.

The compensation condition cannot simply be deleted.  For
`B={1,2,3}`, let `sigma` exchange `1,2` and fix `3`.  For `0<delta<=C/2`, take

```text
L_1=L_2=C+delta,       L_3=C-2 delta.
```

The whole-block average is exactly `C`, while every moved lift is longer than
`C`.  Thus a global full-fibre budget can be spent on a short fixed sheet even
when the monodromy is nontrivial.  A successful integrated-loop proof has two
precise options: construct fixed-point-free monodromy on the budgeted block,
or prove the fixed sheets pay their baseline cost.

### 2.2 Quantitative compensation: only unpaid fixed slack is lost

The binary condition in `(FC1)` has an exact quantitative refinement.  Let
`m=|M|>0`, `f=|F|`, and suppose only that

```text
sum_(nu in B) L_nu <= C(m+f).
```

Put

```text
S_F = C f - sum_(nu in F) L_nu.
```

Subtracting the fixed contribution gives

```text
sum_(nu in M) L_nu <= C m + S_F,                       (FC2)
min_(nu in M) L_nu <= C + S_F/m.                       (FC3)
```

More generally, if the whole-fibre estimate itself has strict margin
`Delta`,

```text
sum_(nu in B) L_nu <= C(m+f) - Delta,
```

then the exact net-margin form is

```text
sum_(nu in M) L_nu <= C m + S_F - Delta,                (FC3a)
min_(nu in M) L_nu <= C + (S_F-Delta)/m.                (FC3b)
```

Consequently `Delta>S_F` is precisely sufficient for a moved lift of length
strictly below `C`.  This separates the two missing analytic quantities: the
geometric construction must produce a strict whole-fibre margin `Delta` and
control the cheap fixed-sheet loss `S_F`, but it need not force `S_F<=0`.

Thus the fixed-sheet average need not be at least `C`.  A cheap fixed block is
permitted, and its total unpaid slack is exactly the additive penalty paid by
the selected moved lift.  The three-sheet model above has `S_F=2 delta`, so
`(FC3)` gives `C+delta` and is attained by both moved sheets; the coefficient
and denominator are sharp.

For the Erdős consumer, take `C=2`.  A whole-fibre loop budget now reduces to
the weaker geometric interface

```text
some moved lift has length <= 2 +
  (2|F| - total fixed-lift length)/|M|.                 (FC4)
```

To recover the sharp target directly one still needs nonpositive fixed slack,
but `(FC4)` exposes how a second source of strict metric margin can pay for a
cheap fixed block.  A grouped-cluster, Bergman, circumradius, or Fekete deficit
only has to dominate the displayed normalized slack; it need not prove a
separate fixed-sheet average lower bound of two.  This compensated margin
comparison is the first unsupported downstream implication for the
whole-fibre route.

`FixedBlockCompensation.lean` formalizes the finite sum-selection kernel,
`(FC2)`, the net-margin form `(FC3a)`, the zero-slack consumer, and the sharp
three-sheet equality model.
Focused Lean validation is currently deferred by the repository's low-disk
single-flight guard; the ordinary derivation above and the exact rational
checker remain the present authority.

## 3. Why this does not prove the parent theorem

The source-current full-fibre angular theorem bounds integrated lengths only
after summing over the whole inverse fibre.  It explicitly leaves open whether
two short branches belong to one safe monodromy block.  The tied-face metric
consumer likewise records the integrated two-sheet/block inequality as open.
Neither theorem constructs a fixed nontrivial block, loops on that block, and
weights satisfying `(QB3)`.

Consequently the return's “fixed-block quadratic-budget alternative” is not a
combined corollary of the charged-lifetime, moment, and monodromy results.  It
is the missing target-deciding producer, expressed through the Hilbert-space
factorization `(QB1)--(QB2)`.  Once assumed, the rest of its generic closure
and strictification argument is valid; the assumption itself is unsupported.

This diagnosis also explains why the return evades the known pointwise block
`L1` no-gos: it assumes the stronger integrated safe-block allocation that
those no-gos deliberately leave open.

## 4. Claim boundary

Proved by ordinary exact mathematics: `(QB1)--(QB2)`, the conditional
fixed-block monodromy consumer, and the fixed-point compensation criterion
with its sharp three-sheet countermodel.  Replayed in exact rational finite models by
`scripts/check_erdos1041_fixed_block_quadratic_budget.py`.

Not proved: existence of the fixed block and quadratic budget for every hard
polynomial, the integrated monodromy-loop inequality, componentwise combined
charge, COVER, FP--GM, or unrestricted Erdős 1041.
