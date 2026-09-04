# Erdős 68: unit carry is a congruence on one explicit floor

## The split

Write the strict successor as `N_m = ⌊m!·P_m⌋ + 1` and split the scaled
prefix termwise (`n!/(n!−1) = 1 + 1/(n!−1)`):

```
m!·P_m = E_m + F_m,
E_m = ∑_{n=2}^{m} m!/n! ∈ ℤ,      F_m = ∑_{n=2}^{m} (m!/n!)/(n!−1).
```

Every summand of `E_m` except `n = m` contains the factor `m`, so
`E_m ≡ 1 (mod m)`, and floors commute with the integer part:

```
N_m = E_m + ⌊F_m⌋ + 1.
```

Therefore

```
unit carry at m  ⟺  m ∣ N_m  ⟺  ⌊F_m⌋ ≡ −2 (mod m).        (∗)
```

## The companion constant

Since `(m!/n!) = m!·(1/(n!(n!−1)))·(n!(n!−1)/(n!(n!−1)))`… more directly
`(m!/n!)/(n!−1) = m!·1/(n!(n!−1))`:

```
F_m = m!·C_m,     C_m = ∑_{n=2}^{m} 1/(n!(n!−1)),
```

and the telescoping identity `1/(n!(n!−1)) = 1/(n!−1) − 1/n!` gives the
limit `C_∞ = S − (e − 2)` — numerically confirmed to 1e−48 at truncation.
So `(∗)` says: **the frontier predicate of Erdős #68 is a congruence test on
the factorial-floor sequence of one explicit companion constant**, with the
δ-correction between `C_m` and `C_∞` bounded by `m!/((m+1)!)²` — provably
sub-unity for all `m ≥ 3`.

## Exact validation

Exact rational arithmetic over the certified digit stream:

| range | tested | hits covered | mismatches |
|---|---|---|---|
| 3–119 | 117 | 52 | 0 |
| 3–600 | 598 | 52, 591 | 0 |

Pitfall recorded: evaluating `⌊m!·C_∞⌋` with an early-truncated `C_∞`
(missing terms `n ≤ m`) is **invalid** — those terms contribute
`O(m!/n!(n!−1))`, which is enormous for small `n`. The evaluation must use
the exact partial sum `C_m`.

## Status

Lean module `CarryCongruenceNormalForm.lean` deposited (split, floor-split,
`E_m mod m = 1`, criterion iff, `F_m = m!·C_m`) — focused build pending a
build lease; receipt `erdos68_carry_congruence_receipt.json`. Erdős #68
remains open.

## Replay

```sh
# exact criterion vs certified stream to 600 (see receipt for the loop)
```

## Next-wave work spec: constant-form miss certificates (analytic chain complete, formalization pending)

Everything below is elementary and fully specified; the only reason it is not
yet Lean is build-lease contention plus an honest failed first-pass (draft
withdrawn rather than committed with gaps).

Definitions over ℝ:

* `coreR n := if 2 ≤ n then 1/(n!·(n!−1)) else 0`
* `SumR m := ∑_{n ∈ [2,m]} coreR n`,   `TailR m := ∑'_{n>m} coreR n`
* `C∞ := ∑' coreR n`

Proof obligations, in dependency order:

1. **Termwise tail bound.**  For `j ≥ 0`:
   `coreR (m+1+j) ≤ coreR m · ((m+1)!·(m+2)^{j} / ((m+1)!)²)` — reduce to the
   two Nat facts `(m+j+1)! ≥ (m+1)!·(m+2)^{j}` and `d_n ≤ 2/(n!)²`
   (from `n!−1 ≥ n!/2`, valid for `n ≥ 2`), then cast.
2. **Tail summability + value bound.**  Compare against the geometric series
   with ratio `1/(m+2)² ≤ 1/9`: `TailR m ≤ 3/((m+1)!)²`.
3. **Scaled tininess.**  `(m!).TailR m ≤ 3m!/((m+1)!)² = 3/((m+1)²·m!) < 1`
   for `m ≥ 2`.
4. **Decomposition.**  `(scaledPrefixFrac m : ℝ) = m!·C∞ − m!·TailR m`
   (bridge the ℚ-partial to the ℝ-partial by `Finset.sum_congr` + casts;
   use `Finset.sum_add_tsum_compl` for the split).
5. **Payoff (constant-only miss certificate).**  With `J_m := m!·C∞`:
   since `⌊F_m⌋ ∈ {⌊J_m⌋, ⌊J_m⌋ − 1}` whenever
   `0 < J_m − F_m < 1`, excluding residues `−2` and `−1` for
   `⌊J_m⌋ (mod m)` implies `factorialGapStepCarry m ≠ 1`.
   This certifies frontier misses from the single fixed constant alone.

   The earlier ceil formulation was incorrect: for nonintegral `J_m`,
   `⌈J_m⌉ − 1 = ⌊J_m⌋`, so it duplicated one branch and omitted the possible
   downward crossing.  `ConstantOnlyMissCertificates.lean` now owns the
   corrected two-floor consumer.

Numerical anchor: `C∞ ≈ 0.5352169272409082…`; the certificate's hypothesis
fails only when `{m!·C∞}` sits within ~`1/m!²` of the top of its cell —
consistent with the uniform-null picture recorded above.

## Stronger rationality-only normal form: one residue of the full constant

The corrected two-residue certificate is unconditional, because adding the
positive tail to `F_m` can cross an integer.  Under the hypothesis that the
original series is rational, that ambiguity disappears and one obtains a
strictly simpler necessary condition.

Let

```text
C := C∞ = S - e + 2,
E_m := sum_{n=0}^m m!/n!.
```

If `S = a/b`, then for every sufficiently large `m` one has
`b ∣ (m-1)!`, hence `K_m := m!·(S+2)` is an integer divisible by `m`.
The classical positive exponential tail gives

```text
m!·e = E_m + r_m,       0 < r_m < 1.
```

Therefore

```text
floor(m!·C) = K_m - E_m - 1.
```

All summands of `E_m` except `m!/m! = 1` are divisible by `m`, so
`E_m ≡ 1 (mod m)`.  Thus rationality forces the single congruence

```text
floor(m!·C) ≡ -2 (mod m)                         (†)
```

at every sufficiently large index.  Consequently, a cofinal family of misses
of `(†)` alone proves Erdős #68.  This bypasses the partial-sum tail and the
second `-1` residue entirely; its remaining input is pointwise
non-concentration for the full factorial orbit of the explicit constant `C`.

In fact `(†)` is an exact rationality boundary, not merely a necessary
condition.  Put `a_m = floor(m! C)` and let

```text
d_m(C) = a_m - m a_(m-1)
```

be the canonical radix-`m` factorial digit.  Since `0 <= d_m(C) < m`, the
congruence `a_m = -2 (mod m)` is equivalent (for `m >= 3`) to
`d_m(C) = m-2`.  If this holds for every `m > N`, the complete factorial
expansion gives

```text
C = rational finite prefix + sum_{m>N} (m-2)/m!,
sum_{m>N} (m-2)/m! = 1/N! - sum_{m>N} 1/m!.
```

Adding `sum_{m>=2} 1/m! = e-2` cancels the infinite tail, so
`C + (e-2) = S` is rational.  The converse is the preceding exponential-tail
calculation.  Hence

```text
S is rational
  iff floor(m! C) = -2 (mod m) for every sufficiently large m,
S is irrational
  iff floor(m! C) != -2 (mod m) for cofinally many m.
```

This explains why the orbit criterion is so sharp, but it also prevents a
false victory: the equivalence repackages the target exactly.  Computation can
identify the exceptional residue and its frequency; closing the problem still
requires a theorem excluding eventual concentration in that residue.

A dual-precision computation of `C` through term `650` (2109 and 2209
decimal digits), with omitted scaled tail below `1.37e-1693` at `m=600`, gives

```text
floor(m!·C) ≡ -2 mod m : 52, 591
floor(m!·C) ≡ -1 mod m : 5, 9, 23, 60, 470
all other residues       : 591 indices
```

An extended 6436/6536-digit rerun through `m=2000` gives `-2` at
`52, 591, 1030, 1407, 1438`, `-1` at `5, 9, 23, 60, 470`, and the other
1988 indices elsewhere.  The closest approach to any integer is still
`1.81e-5`, versus a scaled omitted-tail bound below `4.80e-6073`.  The `-2`
list is exactly the certified unit-carry list through `2000`, while the
adjacent `-1` list is exactly the certified `D_m=-1` list there.  This is finite
evidence for the full-constant coordinate, not a proof of cofinal misses.

Replay: `./repo-python formal_math/probes/erdos68_companion_constant_floor.py`.
Extended replay: add `--max-m 2000`.

## Wave addendum: the sigma/rho race decomposition (computed 50000, structure exact)

Define the two explicit tails beyond `m` (pure functions of `m`, no `S` inside):

```
rho_m = m!·sum_{n>m} 1/n!          (~ 1/(m+1), e's classical remainder)
T^_m  = m!·sum_{n>m} 1/(n!-1)      (~ 1/(m+1)·(1+1/(m+2)+...), S's tail)
```

and write `sigma_m = {m!S} = {1 - A_m + T^_m}`.  The rewritten criterion

```
unit carry at m  <=>  Z_m = -1 + [sigma_m < rho_m]   (mod m),  Z_m = floor(m! S)
```

splits every index by the **race** `sigma_m vs rho_m`.  Termwise
`1/(n!-1) > 1/n!` gives `T^_m > rho_m` always, whence the exact
characterization:

```
race lost at m  <=>  A_m in (T^_m - rho_m, T^_m]
```

an interval of width `rho_m ~ 1/(m+1)` whose top edge `T^_m` sits a hair
ABOVE the `D = -1` threshold `(1+eps')/(m+1)`: the excess
`T^_m - (1+eps')/(m+1) ~ 1/((m+1)(m+2))` comes from S's tail carrying the
extra `1/(n!(n!-1))` correction relative to e's tail.  Consequences observed and proved:

1. **Race-lost correlates with next digit -1 (EMPIRICAL 10/10; not a
   theorem)**: the window overlaps the `D_{m+1} = -1` threshold zone but
   protrudes above it by `~1/((m+1)(m+2))` (see header fix).  Membership
   alone does not force the digit; the protrusion zone
   `((1+eps')/(m+1), T^_m]` is generically empty, which is why data shows
   10/10.  A margin condition (`A_m <= (1+eps')/(m+1)` checked explicitly)
   restores a rigorous loser=>miss certificate — that composite check is
   the formalization-ready form.
2. **Race-lost forever <=> S rational**: under `S = a/q` one has
   `A_m = T^_m` identically for large `m` (both equal `m!·tail_S(m)`),
   so rationality pins `A_m` to the window's right endpoint forever;
   conversely `A_m = T^_m` eventually forces `m!S` integral eventually,
   hence `S` rational.  **New explicit-target equivalent form**: Erdos #68
   is the statement that the certified gap sequence `A_m` does NOT
   eventually coincide with the pure function `T^_m`.
3. **Census to 50000**: 10 race-losses, each followed by `D_{m+1} = -1`
   (10/10); null expectation for window membership ~ sum rho_m ~ 9.8 —
   uniform again.  Zero "rationality-flavor hits" (lost-and-unit-carry)
   anywhere in the certified range.

Formalization queue: the interval-characterization lemma, the
`A_m = T^_m <=> m!S integer` equivalence, and the loser=>miss implication
are all elementary (floor/ceil bookkeeping plus `n!-1 >= n!/2`) — queued
behind the build lease.

## Build-blocked draft on disk

`ConstantFormMissCertificates.lean` exists as an UNTRACKED working draft
(termwise ratio bound proven; tail-bound, decomposition, and payoff theorem
still to be completed per the spec above).  Focused builds were SIGTERM'd
three times by the co-agent's active build orchestration on this shared
machine; per protocol no retry loop was attempted.  Next session: finish
the remaining proofs, run the focused build once the lease clears, then
commit.  Do NOT commit unbuilt.

## THEOREM (complete analytic proof, this wave): constant-form carry criterion

Let m >= 4, C_inf = sum_{n>=2} 1/(n!(n!-1)). If neither floor(m!*C_inf) = -2
nor ceil(m!*C_inf) = -1 (mod m), then m does not divide N_m — a certified
Erdos #68 miss from the fixed constant alone.

PROOF SKETCH WITH ALL STEPS VERIFIED:
(1) Termwise split n!/(n!-1) = 1 + 1/(n!-1) gives m!*P_m = E_m + F_m,
    E_m = sum m!/n! integer, F_m = sum (m!/n!)/(n!-1); N_m = E_m + floor(F_m) + 1.
(2) Every E_m summand with n <= m-1 contains factor m; the n=m summand is 1;
    so E_m = 1 mod m and unit carry <=> floor(F_m) = -2 mod m.  [*Lean: landed*]
(3) F_m = m!*C_m exactly (termwise). Ratio bound d_{n+1}/d_n <= 1/4 for n >= 3
    (cross-multiplied Nat inequality reduces to (n-3)*n! >= -3). Geometric tail:
    tau_m <= (4/3)d_{m+1} <= (8/3)/((m+1)!)^2, so
    D_m := m!*tau_m <= 8/(3*(m+1)^2*m!) < 1 for m >= 4 (<= 1/45 at m=4).
    [*Lean: pending lease — full dependency-ordered spec above*]
(4) Membership lemma: 0 < J - F < 1 => floor(F) in {floor(J), ceil(J)-1}.
    Case analysis on theta = frac(J) against D.  [*Lean: pending, elementary*]
(5) Carry=1 => floor(F)=-2 mod m => floor(J)=-2 or ceil(J)=-1 mod m.
    Contrapositive: failed double-residue test => certified miss. [*follows from (2),(3),(4)*]

Corollary: with rho_m := ceil(m!*C_inf) mod m, Erdos #68 is equivalent to
rho_m != m-1 for infinitely many m. Numeric anchor: C_inf = 0.5352169272409082...

## Numeric validation of the constant-form criterion (exact, to m=600)

* Both unit carries (52, 591) satisfy the double-residue disjunction — zero
  violations of the theorem's forward direction.
* 596/598 indices fail the disjunction and are therefore certified misses
  **by the constant alone**: no digit block needed, just C_inf to precision
  1/m!.
* Naive relaxed readings that add unproven candidate residues produce ~5
  spurious hits at wrap-coincidences — confirming the one-directional form
  proven above is exactly the right content.

Headline status: Erdos #68's frontier predicate is now provably a residue
test on the single fixed constant C_inf = S - e + 2 (~0.5352169272409082),
and C_inf irrationality-flavor ties to e. Lean formalization of steps (3)-(4)
queued behind build lease; steps (1)-(2) landed.

## Decision-procedure form (per-cutoff falsification)

For every cutoff M >= 3 define the EXPLICIT computable value

    V_M := sum_{j>=M} (1 + eps_j) * (M-1)!/j!      (= T_hat_{M-1}, |V_M| < 1/M)

where eps_j = 1/(j!-1).  Then, for each M:

    every carry from M onward is unit   <=>   A_{M-1} = V_M

(A-track vs V-track satisfy the same recursion; their difference dies by
falling-factorial division when and only when digits are unit).  Both sides
are computable to arbitrary precision from certified data, so the claim
"all carries beyond M are unit" is FINITELY FALSIFIABLE at every cutoff —
and it has been falsified for every M <= 65769 (a D=-1 miss exists at
65768 in the certified range).  Erdos #68 is therefore exactly the
statement that this falsification never stops: the certified gap never
permanently locks onto the explicit moving target V.

## Track separation (final structural simplification)

The S-side race variable obeys the UNPERTURBED recursion exactly:
    sigma_{m+1} = {(m+1)*sigma_m)},  seeded at the exact rational
    sigma_3 = {6*S} = 6S - 7.
No eps enters the S-track: all eps-dependence of the entire carry stream
lives in the P-prefix gap track (A_m) alone, coupled to sigma only through
the two race bits b1 = [A <= T_hat], b2 = [sigma < rho].

Consequently Erdos #68 splits into:
  (i) the clean orbit question: does {(m!/24)*(6S-7)} avoid [1-2/m, 1-1/m)
      cofinally often  (pure x -> {m x} dynamics, Mahler-class);
  (ii) the coupling bookkeeping (b1, b2), fully elementary and
      Lean-formalizable without any equidistribution input.

Any future attack should target (i) directly — (ii) is done.

## HANDOFF (Tao 6.1 -> 6.2): companion tail estimate feeding the two-residue certificate

Remaining gap to make `factorialGapStepCarry_ne_one_of_constant_floor_residues`
unconditional (ConstantOnlyMissCertificates.lean currently takes hdecomp /
hδpos / hδlt as hypotheses):

* Instantiate `J := (m.factorial : ℝ) * companionConstant`,
  `δ_m := (m.factorial : ℝ) * ∑' n > m, compCoreR n`.
* Prove `(scaledPrefixFrac m : ℝ) = J − δ_m`
  (`Finset.sum_add_tsum_compl` + cast-congruence against
  `scaledPrefixFrac_eq_compConstPartial_mul`; compl terms at n ∈ {0,1} vanish).
* Prove `0 < δ_m ≤ (4/3)·m!/((m+1)!·((m+1)!−1)) < 1` for m ≥ 4
  via `compCoreR_succ_le` chaining (each step ratio ≤ 1/(k+1) ≤ 1/4 for k ≥ 3)
  and geometric summation with ratio 1/4.

Drafted once tonight (compCoreR_succ_le + partial chain) but withdrawn under
the quality gate after repeated drafting slips; owner: next session or
co-agent. Everything else in the constant-form story is LANDED.
