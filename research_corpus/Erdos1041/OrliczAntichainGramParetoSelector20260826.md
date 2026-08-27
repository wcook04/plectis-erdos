# Erdős 1041: overlap-sensitive Orlicz–Gram Pareto selector

## Status and source boundary

This note assimilates return 003 of
`state/formal_math/type_b_return_batches/erdos1041_20260826_return_stream_02`.
The return is mathematical evidence, including its proposed Lean sketches; it
is not an instruction to modify the corpus in the form requested by the
document.

The return's unconditional three-young/two-heavy theorem, optimal heavy
threshold, Orlicz antichain count, conditional Gram-compatible selector, and
root-centred Green-product polarity are valid as ordinary mathematics.  Its
four-leaf comb is an exact abstract invariant-ledger countermodel, not an
actual-polynomial counterexample.  It therefore refutes the deduction from the
listed uncoupled identities, but not a stronger polynomial-geometric theorem.

The return says that the weighted-selector mathematics is closed.  That is too
broad: it closes one abstract finite selection problem, while the Gram-good
version is conditional and return 002 proves that a Gram-bad root may be the
essential connector hub.  Section 3 gives a stronger and more precise result:
an overlap-sensitive two-tier Pareto selector that retains the sharp younger
pair with a product guarantee and separately supplies two individually heavy
roots.  Unrestricted Erdős 1041 is not proved here.

## 1. Retained exact inputs

Fix an actual `k`-root component `v`.  Write

```text
A_i >= 0,                  S = sum_i A_i,
q_i > 0,                   B = sum_i q_i^2,
P = product_i q_i,
F_i = q_i^2 exp(2A_i).
```

For an edge threshold `alpha` and Gram threshold `eta`, let

```text
E = roots whose path contains an increment x_u >= alpha,
G = roots whose Gram row defect is >= eta,
U = E union G,             b = |U|.
```

The returned Orlicz and Gram estimates imply

```text
|E| Phi(alpha) <= L,
|G| eta <= G_delta,
b <= |E|+|G|
  <= floor(L/Phi(alpha))+floor(G_delta/eta).           (OG1)
```

The last upper bound forgets overlap.  The exact number `b=|E union G|` is the
right selector parameter whenever the two bad sets are available.

For `k>=3`, define the closed heavy threshold

```text
h_cl = sqrt(P) ((k-2)/B)^((k-2)/4).                    (OG2)
```

At most one charge is strictly below `h_cl`.  More sharply, let

```text
p = P/(B/k)^(k/2)
```

and let `u in (0,1]` be the unique solution of

```text
u ((k-2u)/(k-2))^((k-2)/2) = p.
```

Then

```text
h_opt = sqrt(Bu/k)                                      (OG3)
```

is the largest threshold determined by `(B,P,k)` for which at most one charge
is strictly smaller.  In particular `h_opt>=h_cl`.

## 2. The returned selector and its exact boundary

If the coarse count

```text
floor(L/Phi(alpha))+floor(G_delta/eta) <= k-3           (OG4)
```

holds, the return selects two roots outside `E union G`, each with

```text
A_i <= S/(k-a-g-2),     q_i >= h_opt,     F_i >= h_opt^2.
```

This is correct, but (OG4) may be vacuous and its denominator pays separately
for edge-bad and Gram-bad roots even when they coincide.  It also discards the
sharper two-young pair merely because one of its charges may be light.

The four-leaf comb in the return shows the last loss is real for the abstract
ledger.  Its top ages are `(2s,2s,s,0)`, so the two-young set is exactly roots
3 and 4; the assigned charges make root 4 light and the other three heavy.
The model satisfies the stated merge-product, bridge, lifetime, and abstract
`H=I` Gram identities.  Because no root positions realise all of these data,
the result does not justify deleting a polynomial-geometric route.

## 3. Stronger overlap-sensitive Pareto selector

### Theorem A (sharp-age structural-good pair)

Assume `b<=k-2`.  There exist distinct `i,j` outside the exact bad union `U`
such that

```text
A_i,A_j <= S/(k-b-1),                                  (PA1)
P^2 (k-2)^(k-2)
  <= (q_i q_j)^2 Q_comp(i,j)^(k-2),                    (PA2)
```

where

```text
Q_comp(i,j) = sum_(ell notin {i,j}) q_ell^2.
```

Consequently

```text
q_i q_j >= P ((k-2)/Q_comp(i,j))^((k-2)/2)
          >= h_cl^2.                                   (PA3)
```

Both roots have every ancestral increment below `alpha` and Gram defect below
`eta`.  The guarantee uses the same selected pair and deletes no charge.

#### Proof

The young-quantile lemma with `m=b+2` supplies at least `b+2` roots of age at
most `S/(k-b-1)`.  Removing the exact union `U`, of cardinality `b`, leaves two
distinct roots.  Apply the survivor-local complement-energy AM--GM theorem of
`SparseDefectSurvivorSelector20260826` to this pair, taking the survivor set to
be the full component.  This proves (PA2), and positivity gives (PA3).  ∎

### Theorem B (individually heavy structural-good pair)

Assume `b<=k-3`.  There exist distinct `i,j` outside `U` such that

```text
A_i,A_j <= S/(k-b-2),                                  (PA4)
q_i,q_j >= h_opt,
F_i,F_j >= h_opt^2.                                    (PA5)
```

#### Proof

The young-quantile lemma with `m=b+3` gives at least `b+3` roots satisfying
(PA4).  Remove the `b` roots of `U` and the at most one root below `h_opt`.
At least two remain.  Since `F_r=q_r^2 exp(2A_r)` and `A_r>=0`, (PA5) follows.
∎

### Strict improvement over return 003

Theorem A has the better age denominator `k-b-1`, retains the original
two-young threshold when `b=0`, and guarantees the pair product needed by
`RIA3`/`ER4`.  Theorem B retains the return's individual-heavy conclusion but
uses the exact union count `b`, so any overlap between edge and Gram defects
strictly improves its age threshold.  Replacing `b` by the right side of
(OG1) recovers the returned theorem as a coarse corollary.

The two tiers are a genuine Pareto frontier.  The four-leaf abstract model
prevents promotion of Theorem A to two individually `h_cl`-heavy roots using
only `(S,B,P)` and the listed ledger identities.

## 4. Green-product polarity and the exceptional branch

The return's root-centred conformal-radius calculation is correct.  If
`Omega_t` is the component containing root `a_i`, then domain monotonicity from
the pre-merge singleton gives

```text
r_Omega_t(a_i) >= q_i,
P_i(t) = r_Omega_t(a_i)|f'(a_i)|/t >= sigma_i/t.        (GP1)
```

Thus youth near component birth supplies a lower bound near one, while the
root-centred Bergman consumer needs an upper bound away from one.  Charge
heaviness cancels out of (GP1); strengthening `h_opt` cannot fix this polarity.

Return 002 adds a second boundary.  A Gram-bad root can carry nearly all ER4
mass and be the simplest short connector hub.  Therefore Theorem B is a
conditional regular branch, never permission to delete `U`.  The source-current
architecture remains

```text
exceptional-root complete connector
or
regular structural-good pair feeding a complete metric consumer.           (D)
```

Theorem A strengthens the second branch when individual charge balance is not
needed; Theorem B strengthens it when it is.

## 5. Attempt at unrestricted Erdős 1041

The three arrived returns now give exact allocation information, but none of
the source-current complete consumers accepts only

```text
(young age, pair-product or individual charge, edge increments, Gram row).
```

In particular:

1. root-centred Bergman has the opposite polarity (GP1);
2. connected-cluster Bergman uses its internal critical ratio and an upper-area
   hypothesis, not entrance charge;
3. combined charge still lacks a proved component trace inequality, and return
   001 supplied no admissible countercertificate;
4. COVER still lacks a universal intrinsic one-root cover.

So the target-level residual is unchanged in kind but smaller in form:

> Prove one branch of (D), with the regular branch allowed to consume either
> the sharper pair-product tier (PA1)--(PA3) or the individual-heavy tier
> (PA4)--(PA5).

No such universal metric coupling is source-current.  Unrestricted Erdős 1041
remains open.

## Verification boundary

`OrliczAntichainGramParetoSelector20260826.lean` checks the finite-count fan-in,
the strict age-denominator separation, reuse of the survivor-product kernel,
and the final heavy-to-energy implication.
`scripts/check_erdos1041_orlicz_antichain_gram_pareto_selector.py` exhaustively
checks bounded rational age/charge/bad-set grids, solves the optimal threshold
by high-precision bisection, and replays the four-leaf calibration.  The
Orlicz convexity, antichain incidence proof, conformal-radius monotonicity, and
general finite AM--GM argument are ordinary exact mathematics.  The checker is
falsifier and replay evidence, not a proof of the endpoint.
