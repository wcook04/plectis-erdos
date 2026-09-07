# Erdős 68 private-projection computational lab

## Claim boundary

The target is the irrationality of

\[
S=\sum_{n\ge 2}\frac1{n!-1}.
\]

This lab supplies exact finite integer evidence for one producer already
consumed by `EndpointWeightedPrivateSupport.lean`.  It does not turn a finite
prime range into a cofinal theorem.

## Analytic mechanism being tested

For a prime block `2 <= n <= 2p-1`, let

- `L_p` be the endpoint LCM;
- `C_p` be the pairwise-collision core;
- `r_n=(n!-1)/gcd(n!-1,C_p)` be the private quotient;
- `R_p=prod_n r_n` be the private modulus;
- `T_p=sum_n L_p/(n!-1)` be the endpoint numerator;
- `Q_n=R_p/r_n` be the leave-one-out modulus.

The Lean consumer proves that a pair of private owners whose complementary
projections disagree and whose collision cap closes yields an exact failure of
the unit-carry endpoint window.  Cofinal such failures imply irrationality.

The computational hypothesis is deliberately narrower:

> Cofinal prime blocks admit a moving pair selected from the largest
> leave-one-out moduli whose complementary projections disagree and whose
> collision cap closes.

The pair is allowed to move.  Fixed low-index owners cannot be cofinal because
their factorial-gap denominators are eventually absorbed into `(p-1)!`; the
owner-transition pattern, not persistence of one pair, is the possible source
of a theorem.

## Discriminating probe

The generator reconstructs every displayed quantity with Python integers.  At
each prime it orders the nontrivial private quotients by decreasing `Q_n`, takes
the first owner, and takes the first later owner with a different complementary
projection.  It then checks

\[
(2p+1)C_p\max(r_i,r_j)<2p^2(2p-1)!
\]

and the stronger global complementary-residue inequality.

The falsifier is the first prime block with fewer than two nontrivial owners,
no projection disagreement, a failed collision cap, or a failed global-residue
inequality.  Such a block kills this deterministic selection mechanism; it is
not to be hidden by extending a different horizon.

Finite survival has only one analytic use: inspect the transition points of the
selected owners and formulate an arithmetic supply lemma that forces new
private quotients before old ones are absorbed.  A longer run with the same
transition data is not itself progress.

## Reproducible receipt

Canonical generation:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos68_private_projections.py \
  --max-prime 607
```

Exact replay:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos68_private_projections.py \
  --max-prime 607 --check
```

The durable receipt is
`state/formal_math/erdos257_period_noncollapse/erdos68_private_projection_receipt.json`.
Its `experiment_contract` links this note, the generator, the Lean consumer,
the hypothesis, the falsifier, both analytic consequences, and the finite
result polarity.  Its `source` row binds the exact generator bytes.

## Exact-performance substrate

The generator now preserves two exact prefix recurrences instead of rebuilding
large rational data at every prime checkpoint.  If `L'=lcm(L,d)` and
`T=sum L/d_i`, then adding `d` gives

`T' = T (L'/L) + L'/d`.

Likewise the pairwise collision increment uses

`lcm_i gcd(d,d_i) = gcd(d,lcm_i d_i)`.

Finally, ordering leave-one-out moduli `R/r_n` is done by the inverse ordering
of the much smaller private quotients `r_n`; enormous divisions and modular
reductions are delayed until a candidate is actually inspected.  A complete
local p≤503 replay after these changes reproduced all rows, owner runs, and the
canonical exact-payload digest
`39dca640197e0b5281a663262db6d470eec288225be999d1e078bb832f57ccbf`
bit-for-bit in 67.86 seconds.  The computation is therefore both faster and
source-bound without changing its mathematical payload.

## Current exact finite frontier

Through prime `p=607`, all 107 displayed prime blocks pass.  The deterministic
owner pair changes in four runs:

| Prime range | Selected owners | Selected private quotients |
|---|---|---|
| `11..109` | `(6,8)` | `(719,1753)` |
| `113..179` | `(6,9)` | `(719,2999)` |
| `181..463` | `(9,7)` | `(2999,5039)` |
| `467..607` | `(7,11)` | `(5039,7853)` |

The transitions already rule out the naive fixed-pair version.  What remains
open is whether the staircase is forced by a renewable arithmetic source of
small nontrivial private quotients and whether that source closes the collision
cap cofinally.  The extension from 503 to 607 introduced no new transition and
is therefore recorded as validation coverage, not as a new mathematical
advance.  Its exact-payload digest is
`40e07ad98e336d349dfe2b2b74fa8fc5d5e42f51276ed21c98cd471d73fc8af8`.

## Exact transition mechanism

The run boundaries have a cheaper explanation than another giant-LCM scan.
Every selected private quotient in the four displayed runs is prime. For an
owner prime `q` first appearing at index `n`, compute the indices `m<q` with
`m!≡1 (mod q)`. The first hit after `n` is exactly the first point at which a
second displayed denominator can put `q` into the collision core.

The three observed exits agree exactly with that prediction:

| Exited prime | First later hit | First prime block containing it | Observed transition |
|---:|---:|---:|---:|
| `1753` | `221` | `113` | `113` |
| `719` | `359` | `181` | `181` |
| `2999` | `932` | `467` | `467` |

For the current owners, the same recurrence predicts first possible expiry
checkpoints `1277` for `5039` (repeat index `2519`) and `3923` for `7853`
(repeat index `7841`). This does not assert that the pair is otherwise
unchanged up to those checkpoints: a new smaller owner or a changed projection
may intervene. It does prove that the three historical staircase steps are
collision-renewal events rather than unexplained finite noise.

The analytic target is now sharper: produce cofinally two private owner primes
whose first later factorial-one hits lie beyond the active block, and then
establish the checked collision-cap and projection inequalities for those live
owners. This is a renewal theorem coupling unique support to first-repeat
time; fixed-owner persistence is no longer the model.

Exact generation and replay:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos68_private_owner_recurrences.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos68_private_owner_recurrences.py --check
```

The source-bound receipt is
`state/formal_math/erdos257_period_noncollapse/erdos68_private_owner_recurrence_receipt.json`.
Its experiment contract classifies the outcome as `mechanism_opened`, names the
cofinal renewal consumer, and explicitly refuses to promote these finite exact
transition identities to an irrationality proof.

## Terminal Wilson owners bypass renewal entirely

The recurrence picture has a structurally different boundary case.  Wilson's
theorem forces every prime `q>=5` to divide `(q-2)!-1`.  If `q-2` is the
*first* factorial-one hit for `q`, it is automatically the only hit globally:
`PrimeZeroBranch.lean::prime_terminal_factorialGap_hit_iff` kernel-checks that
Wilson excludes `q-1`, while every factorial from `q` onward is zero modulo
`q`.  Such a prime is therefore a terminal owner; it can never be absorbed by
a later factorial-gap collision.

The existing exact `q^2` recurrence engine exposes this family without any
giant LCM reconstruction.  Through `q<=50000`, 1,801 of the 5,133 primes have
first support exactly at `q-2`.  The full ordered list is source-bound by a
digest rather than copied into this note.  Among consecutive terminal primes,
1,799 pairs have owner indices that fit together in some block `[2,2p-1]`.
The first nontrivial canonical witness is `(q_1,q_2)=(37,41)`: their globally
unique owner indices are `35` and `39`, both in the block with `p=20`.  The
same exact reconstruction verifies more than support: `37` and `41` divide
the private modulus, their complementary factor projections disagree, and the
full factor-pair scale inequality closes.  Thus the existing endpoint-window
consumer fires for this natural block.

This is a one-way mechanism opening, not evidence for an infinite or positive-
density terminal family.  It bypasses the first-repeat renewal obligation and
closes every finite consumer condition for one exact pair, but it does not
supply those certificates cofinally.  The analytic producer is now precise:
prove cofinally many comparable terminal-first-hit pairs for which the same
factor-pair inequality closes, or extract a weaker cofinal supply from this
globally unique family.

Exact generation and replay:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos68_terminal_private_owners.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos68_terminal_private_owners.py --check
```

The durable receipt is
`state/formal_math/erdos257_period_noncollapse/erdos68_terminal_private_owner_receipt.json`.
