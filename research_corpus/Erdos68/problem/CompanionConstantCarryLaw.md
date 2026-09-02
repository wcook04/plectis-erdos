# Erdős 68: the carry sequence is the complement digit sequence of one fixed constant

Two Lean modules land here, both sorry-free on `{propext, Classical.choice,
Quot.sound}`:

* `CompanionConstantCarryLaw.lean` (kernel-checked 2026-09-02, `lean_fast_build.py` exit 0);
* `FactorialShiftFamilyOrbit.lean` (same build, exit 0).

Neither proves Erdős 68. The claim boundary is stated at the end.

## 1. Setting

`S = sum_(n>=2) 1/(n!-1)`, `H_m` its prefix, `Z_m = floor(m! H_m) + 1`, and
`b_m` the carry in `Z_m = m Z_(m-1) + 1 - b_m`. Lean already proves
`S rational <=> b_m = 1 eventually` and `b_m = 1 <=> floor(F_m) == -2 (mod m)`
for the finite carrier `F_m = m! C_m`, `C_m = sum_(n<=m) 1/(n!(n!-1))`.
The fixed companion constant is `C = lim C_m = S - (e - 2)`, and
`CompanionOrbitRationality.lean` proves `S rational <=> floor(m! C) == -2 (mod m)
eventually`.

What was missing was the pointwise bridge between `F_m` (finite, rational) and
`m! C` (one real constant). `SecondLayerDigit.lean` carried it under an explicit
floor-stability hypothesis; `ConstantOnlyMissCertificates.lean` carried the
miss certificate under an abstract `F_m = J - delta`, `0 < delta < 1`
hypothesis. Both hypotheses are now discharged.

## 2. Theorems (CompanionConstantCarryLaw.lean)

Let `delta_m = m! sum_(n>m) 1/(n!(n!-1))` (`companionScaledTail`).

**Tail identity.** `F_m = m! C - delta_m` and `0 < delta_m < 1/((m+1)!-1)` for
`m >= 2` (`scaledPrefixFrac_cast_eq_companion_sub_tail`, `companionScaledTail_pos`,
`companionScaledTail_lt`). Proof: the omitted tail is dominated termwise by
`1/((m+1)!-1)` times the exponential tail `sum_(n>m) 1/n!`, and
`m! sum_(n>m) 1/n! < 1` is already in the corpus.

**Wrap identity.** With `sigma_m = [fract(m! C) < delta_m]` (`companionWrap`),
`floor(F_m) = floor(m! C) - sigma_m` (`floor_scaledPrefixFrac_eq_facFloor_sub_wrap`).
This is the elementary fact that subtracting `0 < delta < 1` lowers a floor
exactly when the fractional part is below `delta`.

**Carry law.** For every `m >= 3`, with `d_m(C)` the canonical factorial digit
of `C`,

```text
b_m = (m - 1 - d_m(C)) + sigma_m - m sigma_(m-1).
```

(`factorialGapStepCarry_eq_companion_digit_law`). The proof composes the finite
second-layer digit law `floor(F_m) - m floor(F_(m-1)) = m - 1 - b_m` with the
wrap identity at `m` and `m - 1`.

**Consequences.**

* `b_m = 1  =>  d_m(C) in {m-2, m-1}` (`canonicalDigit_companion_of_unit_carry`);
* `b_m = 0  =>  d_m(C) in {m-1, 0}` (`canonicalDigit_companion_of_zero_carry`);
* if `floor(m! C)` avoids both residues `-2` and `-1` modulo `m`, then `b_m != 1`
  (`factorialGapStepCarry_ne_one_of_companion_floor_residues`). This is the
  packet's named "unconditional constant-only miss certificate"; no tail
  hypothesis remains;
* `SecondLayerFloorStableAt C m <=> delta_m <= fract(m! C)`
  (`secondLayerFloorStableAt_companion_iff`), so the conditional theorem of
  `SecondLayerDigit` is exactly the no-wrap case, and away from wraps
  `b_m = m - 1 - d_m(C)` (`factorialGapStepCarry_eq_complement_companion_digit_of_no_wrap`).

The wrap event `sigma_m = 1` means `F_m` lies within `delta_m < 1/((m+1)!-1)`
below an integer. `F_2 = 1` is an integer and `fract(2C) = delta_2` exactly, so
`sigma_2 = 0` under the strict inequality; the exact probe
`formal_math/probes/erdos68_companion_carry_law.py` finds no wrap through
`m = 160` and the smallest ratio `fract(m! C)/delta_m` there is `18.7`. A wrap
would force `den(F_m) > (m+1)! - 1`, which typical carriers satisfy by an
enormous margin, so wraps are not excluded by size; they are simply very rare
near-integer events. This is stated, not proved, and is not needed for any
theorem above.

## 3. Erdős's family under one boundary (FactorialShiftFamilyOrbit.lean)

Erdős (1988, p. 102) conjectures that `S_t = sum_(n>=2) 1/(n!+t)` is irrational
for every integer `t`. The termwise identity `1/(n!+t) = 1/n! - t/(n!(n!+t))`
gives `S_t = (e - 2) - t C_t` with `C_t = sum_(n>=2) 1/(n!(n!+t))`, and the
generic fixed-orbit theorem of `CompanionOrbitRationality.lean` applied to
`x = -t C_t` yields, for every integer `t >= -1`,

```text
S_t rational  <=>  ceil(t m! C_t) == 2 (mod m) for all sufficiently large m,
S_t irrational <=> the ceiling escapes the residue 2 cofinally
```

(`not_irrational_shiftGapSeries_iff_eventually_ceil_residue_two`,
`irrational_shiftGapSeries_iff_cofinal_ceil_residue_misses`). The restriction
`t >= -1` keeps every denominator `n! + t >= 1`; members with `t <= -2` differ
by a finite rational correction and are not formalised here.

Two sanity members are kernel-checked: `t = -1` is the Erdős 68 series
(`shiftGapSeries_neg_one_eq_factorialGapSeries`; the ceiling condition is then
`floor(m! C) == -2`, the existing boundary), and `t = 0` is `e - 2`
(`shiftGapSeries_zero_eq_exp_one_sub_two`) whose orbit `ceil(0) = 0` never lies
in the residue class `2` for `m >= 3`, so the boundary reproves the
irrationality of `e` (`irrational_exp_one_of_family_boundary`). The probe records,
as finite evidence only, the residue-`2` hits for `t = 1, 2, 3, 5` through
`m = 400`: `[3, 30, 110]`, `[3, 13, 61, 227, 377]`, `[6, 31, 45, 56]`,
`[11, 14, 20, 28, 29, 309]`, each consistent with a `1/m` hit rate.

This is an exact family boundary in the sense of Cantor's factorial-base
criterion (Cantor 1869; Galambos 1976, Ch. 1). It decides no member with
`t != 0`.

## 4. The parent, and the two producers examined

**Genuine attempt.** Under `S = a/q`, `Z_m = m! S` for every `m >= q`, so the
strict-successor criterion is Cantor's criterion in a rational coordinate: a
unit carry at `m` is exactly `fract((m-1)! H_(m-1)) in (1 - (2+eps_m)/m, 1 - (1+eps_m)/m]`,
a window of length `1/m`, and rationality is eventual residence in that window.
The fractional part is `frac(sum_(n<m) ((m-1)!/n! mod (n!-1))/(n!-1))`, a sum of
about `m/2` reduced residues of descending-factorial products modulo the
pairwise almost-coprime moduli `n! - 1`. No congruence, valuation, or
continued-fraction coordinate examined here controls that sum at scale `1/m`;
every representation returns the same residual, one non-concentration statement
for a sum of modular residues. No proof of the parent is offered.

**Odd-index parity cutoff.** The eleven `D_m = -1` events through `300000` are
`5, 9, 23, 60, 470, 3026, 19222, 27472, 30324, 35366, 65768`; the eight after
`23` are all even. Under the uniform-digit null (which the corpus already
verified at every tested stratum, parity included) the chance that eight
independent events are all even is `1/256`, and the pattern was noticed after
the fact among several tested arithmetic properties, so its pre-registered
significance is weaker still. The companion carry law shows `D_m = -1` is the
event `d_m(C) = m - 1` (or the near-integer wrap branch `d_m(C) = 0`), and the
digit `d_m(C) = floor(m fract((m-1)! C))` has no parity-sensitive mechanism:
`(m-1)! C mod 1` is again a sum of about `m/2` reduced residues. The
computational extension is not cheap: the certificate costs
`O(M^2 log M)` bit operations (the interval carries `bits(M!)` precision at
every step), so doubling the horizon to `600000` costs about four times the
landed run and is expected to add only `ln 2 ~ 0.7` new events. The honest
classification is a finite pattern consistent with chance, with no known
arithmetic mechanism; it is not escalated to a producer.

**Repeated prime-power record route.** The producer asks for infinitely many
`(q, n)` with `q^2 | n! - 1` after an earlier `q`-hit. The heuristic count of
`q^2 | n! - 1` events is `sum_n sum_(q>n) q^(-2) ~ sum_n 1/(n log n)`, which
diverges like `log log N`; the exact scan through `q <= 10^6` found six square
hits and three strict records. This is the density profile of Wilson and
Wieferich primes, whose infinitude is open, and no theorem in the sieve or
character-sum literature assimilated in the packet supplies even one `q^2`-hit
infinitely often. The route is therefore a Wieferich-type infinitude statement,
strictly harder than the corpus's incidence inputs can reach. This is a
classification with a heuristic, not a proof-backed no-go.

## 5. Claim boundary

Erdős 68 remains open. The carry law is an exact identity between the carry
sequence and the factorial digits of one fixed constant plus an explicit
exceptional indicator; the family theorem is an exact boundary for every
`t >= -1`; the `t = 0` member reproves a classical fact. No cofinal miss, no
non-concentration theorem, and no irrationality result for any `t != 0` is
claimed.

## 6. Replay

```sh
cd formal_math/erdos257_period_noncollapse
public-source-redacted://repo-python scripts/lean_fast_build.py \
  ErdosProblems.Erdos68.CompanionConstantCarryLaw \
  ErdosProblems.Erdos68.FactorialShiftFamilyOrbit
cd public-source-redacted://ai_workflow
./repo-python formal_math/probes/erdos68_companion_carry_law.py --max-m 160 --family-max-m 400
```

The probe exits 0 only if every predeclared falsifier passes (exact carry
identity at every `3 <= m <= 160`, the two digit-window consequences, the
`delta_m` bounds, the `t = 0` never-hit check, and agreement of the `t = -1`
residue hits with the certified unit-carry list).
