/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Rem.C1
import ErdosProblems.Rem.C3
import ErdosProblems.Rem.C6

/-!
# T3 — the 2-adic layer: what it removes from the hovering band, and what it does not

Write `ρ s = seamIntegerGreedyRemainder s` and `a s = ρ s - 2 ^ s`.  `Rem/C6`
leaves the `1/2` question of Erdős `#257` needing `ρ s ≤ 2 ^ s` cofinally, with
the surviving configuration being `a s` **hovering** in `[2, O(s)]` forever:
`Rem/C6` gives `a s < 2 * 2 ^ s` at a late row, `Bit/R1`'s descent
`a (s+1) ≤ 4 * a s - 4` has fixed point `4/3`, and `Rem/C1`'s `band_invariant`
shows the row law alone cannot expel a trajectory from `[2 ^ s + 2, 2 ^ s + 4]`.
This file attacks the hovering band, and it says at the outset what it achieves:

**The hovering band is NOT excluded here.**  `RemainderReachesHalfPointCofinally`
is not proved.  What is proved is an unconditional invariant of `ρ`, from
outside the row layer, which removes exactly the *even half* of the band at
cofinally many rows — together with a sharp negative showing that mod-`2`
information cannot remove the rest.

## The outside input, named

The row layer (`Bit/R1`–`R4`, `Rem/C1`) sees only *sizes*: the row-to-row lift,
its carry budget, and ceilings.  The input used here is the exact **2-adic
valuation of the seam weights**.  From `truncatedMersenneWeight_eq_geometricCore`,

    truncatedMersenneWeight s d = 2 ^ (2*s % d) * (odd number)      (d ≥ 2),

so `v₂(truncatedMersenneWeight s d) = 2*s % d` exactly, and the rank-`d` weight
is **odd iff `d ∣ 2*s`** (`truncatedMersenneWeight_odd_of_dvd`,
`truncatedMersenneWeight_even_of_not_dvd`).  No size argument can see this.

## What is PROVED

* `integerGreedyRemainder_mod_two_of_forall_even` — a descending greedy run
  against all-even weights preserves the parity of the capacity.  Taking *or*
  declining an even weight is invisible mod `2`.
* `seamIntegerGreedyRemainder_odd_of_isolated` — **the parity law.**  If no rank
  in `[3, s)` divides `2*s`, then `ρ s` is **odd**.  (Rank `2` carries the only
  odd weight of the row, the target `2 ^ (2*s-1) - 2 ^ s` is even, and rank `2`
  is always taken: `truncatedMersenneWeight_two_le_target`.)
* `seamIntegerGreedyRemainder_odd_of_prime`, `odd_remainder_cofinally` — the
  hypothesis holds at every prime row (`isolated_of_prime`), so **`ρ s` is odd at
  cofinally many rows**, unconditionally.
* `remainder_ne_two_pow_add_even` — at a prime row `ρ s ≠ 2 ^ s + c` for every
  even `c`.  Consequences:
  - `remainder_ne_two_pow`, `hitAt_iff_lt_of_prime`: the half point is never
    *attained* at a prime row, so `Rem/C3`'s `HitAt` is strict there.
  - `ne_surplusModel_of_even`, `surplusModel_two_fails_cofinally`: **`Rem/C1`'s
    persistent-surplus model `2 ^ s + 2` — the sequence `Rem/C1` exhibits as
    satisfying every row-level constraint the corpus owns — is not the true
    remainder at any prime row.**  The 2-adic layer refutes it where the row
    layer provably cannot.
  - `c1_band_collapses_at_prime`: at a prime row, `Rem/C1`'s forward-invariant
    band `[2 ^ s + 2, 2 ^ s + 4]` retains only its middle point `2 ^ s + 3`.
  - `remainder_ge_three_of_forcedRun`: `Bit/R1`'s unconditional forced-run pin
    `2 ^ s + 2 ≤ ρ s` improves to `2 ^ s + 3` at every prime row.
* `descent_gap_ge_five_before_prime` — **`Bit/R1`'s descent window `[4, 2*s]`
  narrows to `[5, 2*s]` at every row whose successor is prime.**  The one-step
  correction `4 * ρ s - ρ (s+1) - 2 ^ (s+1)` has the parity of `ρ (s+1)`.  This
  is sharp: `descent_gap_twelve` certifies the correction at `s = 12` is exactly
  `5`, and `descent_gap_ten` gives `7` at `s = 10`, while the composite contrast
  row `descent_gap_eleven` gives the even value `8`.
* `hovering_low_bits` — **the rigidity, made explicit.**  Hovering at row `s`
  says precisely that for every `k` with `2*s ≤ 2 ^ k ≤ 2 ^ s` the residue
  `ρ s % 2 ^ k` *is* the surplus: the binary expansion of `ρ s` carries a run of
  zeros from bit `⌈log₂ (2*s)⌉` up to bit `s - 1`, a run of length `s - O(log s)`.
  The hovering band is a statement about the low bits of `ρ s`, not about its size.
* `pinEscape_of_dvd_two_pow`, `pinEscapesCofinally_of_dyadicDepth`,
  `half_mem_of_ceilingCofinally_of_dyadicDepth` — a **sufficient condition**
  for `#257`'s `1/2` question, of a kind no size argument can state: if `2 ^ k`
  divides `ρ s` for some `2 * s ≤ 2 ^ k ≤ 2 ^ s` at cofinally many rows, then
  `Rem/C3`'s `PinEscapesCofinally` holds, and with `Rem/C3`'s `CeilingCofinally`
  the `1/2` question resolves positively.
* `pinned_odd_of_ceilingCofinally_of_not_half_mem` — `Rem/C3`'s pin sharpened:
  under a cofinal ceiling, failure of `1/2 ∈ mersenneAchievementSet` forces
  `2 ^ s + 3 ≤ ρ s < 2 ^ s + 2*s` at every large **prime** row.

## The sharp negative

`exists_persistent_odd_surplus_model`: `RemC1.surplusModel 3`, i.e. `2 ^ s + 3`,
is **odd at every row `s ≥ 1`**, obeys `Bit/R1.StepLaw` from row `5`, obeys every
row-level constraint listed in `Rem/C1` (good-row ceiling, pin window,
right-branch window, growth bound, trivial ceiling), lies inside `Rem/C1`'s
forward-invariant band at every row (`odd_surplus_model_in_c1_band`), and never
returns to the half point.  So **no consequence of the row law together with the
mod-`2` information proved here can imply
`RemainderReachesHalfPointCofinally`.**  The 2-adic layer at level `2` removes
exactly the even half of the hovering band; the odd half survives intact.

Removing the odd half needs `ρ s mod 4`, and the proof above does not extend:
mod `4` the contributing ranks are those with `2*s % d = 1`, i.e. the divisors of
`2*s - 1` in `[2, s)`, and their contribution depends on **which of them the
greedy selects** — information the corpus does not have at an arbitrary row.
I could not discharge that, and say so plainly.

## Distinguishing PROVED from MEASURED

Everything in the numbered sections is proved and kernel-checked.  The following
are MEASURED only, by an arbitrary-precision replication of `seamWeights`,
`seamSubsetTarget` and the descending greedy, agreeing with the kernel at every
row certified here:

* The parity law has an exact general form: over every row `s ∈ [5, 400]`,
  `ρ s ≡ #{d ∈ S s : d ∣ 2*s} (mod 2)`, where `S s` is the greedy-selected rank
  set.  Only the special case where that count is forced to `1` — no rank in
  `[3, s)` divides `2*s` — is proved here, because the general case needs the
  selected set.
* `ρ s` is odd at `223` of the `396` rows of `[5, 400]` and even at `173`; the
  parity is genuinely non-constant.  Evenness at cofinally many rows is **not**
  proved: it would need control of which divisors of `2*s` the greedy selects.
  Consequently "`a s` is not eventually constant" is **not** proved either.
* `v₂(ρ s)` over `[5, 1200]` has the histogram
  `0:677, 1:273, 2:131, 3:56, 4:28, 5:21, 6:4, 7:3, 8:1, 9:1, 15:1` — geometric
  in appearance, with ratios near `1/2`; no distribution law is proved.  The
  maximum is `v₂(ρ 575) = 15`.
* Consequently `DyadicDepthCofinally` is realised at exactly **one** row of
  `[5, 1200]`, namely `s = 575` (`dyadicDepth_575`, kernel-certified), and at
  that row `ρ 575 ≤ 2 ^ 575` already holds, so `Bit/R2`'s own criterion fires
  there too.  The dyadic criterion is therefore **not yet known to do independent
  work**; the heuristic `P(v₂ > log₂ 2s) ≈ 1/(2s)` predicts about `log s` such
  rows below `s`, which is consistent with cofinality but far from a proof.

## Non-vacuity audit (mandatory)

Hypotheses realised by a concrete, kernel-checked instance:

* `truncatedMersenneWeight_odd_of_dvd` / `_even_of_not_dvd`: `weight_five_two_odd`,
  `weight_five_three_even`.
* `integerGreedyRemainder_mod_two_of_forall_even`: `greedy_parity_witness`.
* `seamIntegerGreedyRemainder_odd_of_isolated`: every prime row; and
  `remainder_odd_101` cross-checks the conclusion in the kernel at `s = 101`.
  The hypothesis is **necessary**: `not_isolated_30` and `remainder_even_30` show
  the conclusion genuinely fails at the composite row `30`.
* `descent_gap_ge_five_before_prime`: `descent_gap_ge_five_twelve` and
  `descent_gap_ge_five_ten` (rows `11` and `13` are prime and bad).
* `hovering_low_bits`: `hovering_low_bits_eight` — row `8` is the one row of
  `[5, 1300]` (and, per `Rem/C3`'s wider run, of `[5, 3000]`) that actually sits
  in the pin window.
* `pinEscape_of_dvd_two_pow`: `dyadicDepth_witness` at `s = 575`, `k = 15`.

Hypotheses I could **not** discharge, stated plainly:

* `DyadicDepthCofinally` — open (see the measurement above).
* `RemC3.CeilingCofinally` — open, as `Rem/C3` already records.
* `BitR1.ForcedRun N` in `remainder_ge_three_of_forcedRun`, and
  `1/2 ∉ mersenneAchievementSet` in `pinned_odd_of_ceilingCofinally_of_not_half_mem`
  — these are the negation of the goal; the theorems are conditional structure
  results, exactly as in `Rem/C1` and `Rem/C3`.
* `c1_band_collapses_at_prime` — I could not exhibit any row satisfying its
  hypothesis `2 ^ s + 2 ≤ ρ s ≤ 2 ^ s + 4`.  The replication run for this file
  finds **no** such row in `[5, 1300]`.  The theorem is a conditional narrowing
  of `Rem/C1`'s band, not a statement about an occupied configuration.

Every theorem below checks with `lake env lean ErdosProblems/Three/T3.lean`
(exit `0`, empty output) and with axioms `[propext, Classical.choice, Quot.sound]`
only.  No `sorry`, no `native_decide`, no new axiom; `decide +kernel` only.
-/

namespace ErdosProblems.ThreeT3

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. The exact 2-adic valuation of a truncated Mersenne weight -/

/-- The geometric core of a truncated Mersenne weight is odd. -/
theorem geometricCore_odd {d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) :
    (∑ i ∈ Finset.range q, ((2 : ℕ) ^ d) ^ i) % 2 = 1 := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ q hq ih =>
      rw [Finset.sum_range_succ]
      have heven : ((2 : ℕ) ^ d) ^ q % 2 = 0 := by
        have hdvd : (2 : ℕ) ∣ (2 ^ d) ^ q := by
          rw [← pow_mul]
          exact dvd_pow_self 2 (by positivity)
        omega
      omega

/-- **Odd exactly on the ranks dividing `2 * s`.**  If `d ∣ 2 * s` then the
truncated Mersenne weight of rank `d` is odd. -/
theorem truncatedMersenneWeight_odd_of_dvd {s d : ℕ} (hd : 2 ≤ d) (hs : 1 ≤ s)
    (h : d ∣ 2 * s) : truncatedMersenneWeight s d % 2 = 1 := by
  obtain ⟨c, hc⟩ := h
  have hr : 2 * s % d = 0 := by rw [hc]; exact Nat.mul_mod_right d c
  have hq : 1 ≤ 2 * s / d := by
    refine (Nat.one_le_div_iff (by omega)).mpr ?_
    exact Nat.le_of_dvd (by omega) ⟨c, hc⟩
  rw [truncatedMersenneWeight_eq_geometricCore hd, hr, pow_zero, one_mul]
  exact geometricCore_odd (by omega) hq

/-- …and even off them: if `d` does not divide `2 * s` then the rank-`d` weight
is even. -/
theorem truncatedMersenneWeight_even_of_not_dvd {s d : ℕ} (hd : 2 ≤ d)
    (h : ¬ d ∣ 2 * s) : 2 ∣ truncatedMersenneWeight s d := by
  have hr : 1 ≤ 2 * s % d := by
    rcases Nat.eq_zero_or_pos (2 * s % d) with h0 | h1
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) h
    · exact h1
  rw [truncatedMersenneWeight_eq_geometricCore hd]
  exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

/-! ## 2. The descending greedy transports parity -/

/-- **Parity transport.**  A greedy run against weights that are all even
returns a remainder of the same parity as the capacity: taking or declining an
even weight cannot change the parity of the residual. -/
theorem integerGreedyRemainder_mod_two_of_forall_even :
    ∀ (ws : List ℕ), (∀ w ∈ ws, 2 ∣ w) → ∀ C : ℕ,
      integerGreedyRemainder ws C % 2 = C % 2 := by
  intro ws
  induction ws with
  | nil => intro _ C; rw [RemC6.integerGreedyRemainder_nil]
  | cons w ws ih =>
      intro heven C
      obtain ⟨k, hk⟩ := heven w (by simp)
      have htail : ∀ v ∈ ws, 2 ∣ v := fun v hv => heven v (by simp [hv])
      rw [RemC6.integerGreedyRemainder_cons]
      by_cases hle : w ≤ C
      · rw [if_pos hle, ih htail (C - w)]; omega
      · rw [if_neg hle, ih htail C]

/-- Both directions of §1 realised at a concrete row: `2 ∣ 2 * 5` and
`¬ 3 ∣ 2 * 5`. -/
theorem weight_five_two_odd : truncatedMersenneWeight 5 2 % 2 = 1 :=
  truncatedMersenneWeight_odd_of_dvd (by norm_num) (by norm_num) (by norm_num)

theorem weight_five_three_even : 2 ∣ truncatedMersenneWeight 5 3 :=
  truncatedMersenneWeight_even_of_not_dvd (by norm_num) (by decide)

/-- The hypothesis of §2 realised: a genuinely non-trivial all-even weight word,
where the greedy takes `8` and `4` and declines `2`. -/
theorem greedy_parity_witness :
    integerGreedyRemainder [8, 4, 2] 13 % 2 = 13 % 2 :=
  integerGreedyRemainder_mod_two_of_forall_even [8, 4, 2] (by decide) 13

/-! ## 3. The parity of the seam greedy remainder -/

/-- Every weight of the seam word from rank `a` on is even, provided no rank in
`[a, s)` divides `2 * s`. -/
theorem seamWeightsFrom_forall_even (s : ℕ) :
    ∀ (n a : ℕ), s ≤ a + n → 2 ≤ a →
      (∀ d : ℕ, a ≤ d → d < s → ¬ d ∣ 2 * s) →
      ∀ w ∈ seamWeightsFrom s a, 2 ∣ w := by
  intro n
  induction n with
  | zero =>
      intro a hle _ _ w hw
      rw [seamWeightsFrom_eq_nil (by omega)] at hw
      simp at hw
  | succ n ih =>
      intro a hle ha h w hw
      by_cases hlt : a < s
      · rw [seamWeightsFrom_eq_cons hlt] at hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact truncatedMersenneWeight_even_of_not_dvd ha (h a le_rfl hlt)
        · exact ih (a + 1) (by omega) (by omega)
            (fun d hd hds => h d (by omega) hds) w hw'
      · rw [seamWeightsFrom_eq_nil (by omega)] at hw
        simp at hw

/-- Rank `2` is always taken by the seam greedy: its weight `4 ^ s / 3` fits
inside the target `2 ^ (2*s-1) - 2 ^ s` for every `s ≥ 3`. -/
theorem truncatedMersenneWeight_two_le_target {s : ℕ} (hs : 3 ≤ s) :
    truncatedMersenneWeight s 2 ≤ seamSubsetTarget s := by
  have hAB : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hB8 : (8 : ℕ) ≤ 2 ^ s := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hAge : 8 * 2 ^ s ≤ 4 ^ s := by
    rw [hAB]; exact Nat.mul_le_mul_right _ hB8
  have hpow : (2 : ℕ) ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdouble : (2 : ℕ) ^ (2 * s - 1) * 2 = 4 ^ s := by
    rw [← pow_succ, show 2 * s - 1 + 1 = 2 * s by omega, pow_mul]
    norm_num
  have hw : truncatedMersenneWeight s 2 = 4 ^ s / 3 := by
    norm_num [truncatedMersenneWeight]
  have htar : seamSubsetTarget s = 2 ^ (2 * s - 1) - 2 ^ s := rfl
  have hd3 := Nat.div_add_mod (4 ^ s) 3
  have hd3' : 4 ^ s % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [hw, htar]
  omega

/-- **The parity law.**  If no rank strictly between `2` and `s` divides
`2 * s`, then the seam integer-greedy remainder of row `s` is **odd**.

The mechanism is entirely 2-adic and invisible to the row recurrence: the
`2`-adic valuation of `truncatedMersenneWeight s d` is exactly `2 * s % d`, so
rank `2` carries the only odd weight of the row, and rank `2` is always taken;
the target `2 ^ (2*s-1) - 2 ^ s` is even, and every later step of the greedy
adds or declines an even weight. -/
theorem seamIntegerGreedyRemainder_odd_of_isolated {s : ℕ} (hs : 3 ≤ s)
    (h : ∀ d : ℕ, 3 ≤ d → d < s → ¬ d ∣ 2 * s) :
    seamIntegerGreedyRemainder s % 2 = 1 := by
  have hsplit : seamWeights s = truncatedMersenneWeight s 2 :: seamWeightsFrom s 3 := by
    show seamWeightsFrom s 2 = _
    rw [seamWeightsFrom_eq_cons (show 2 < s by omega)]
  have htake : truncatedMersenneWeight s 2 ≤ seamSubsetTarget s :=
    truncatedMersenneWeight_two_le_target hs
  have hw2 : truncatedMersenneWeight s 2 % 2 = 1 :=
    truncatedMersenneWeight_odd_of_dvd (by norm_num) (by omega) ⟨s, rfl⟩
  have hC : seamSubsetTarget s % 2 = 0 := by
    have h1 : (2 : ℕ) ∣ 2 ^ (2 * s - 1) := dvd_pow_self 2 (by omega)
    have h2 : (2 : ℕ) ∣ 2 ^ s := dvd_pow_self 2 (by omega)
    have h3 : (2 : ℕ) ^ s ≤ 2 ^ (2 * s - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have htar : seamSubsetTarget s = 2 ^ (2 * s - 1) - 2 ^ s := rfl
    omega
  have heven : ∀ w ∈ seamWeightsFrom s 3, 2 ∣ w :=
    seamWeightsFrom_forall_even s s 3 (by omega) (by norm_num) h
  show integerGreedyRemainder (seamWeights s) (seamSubsetTarget s) % 2 = 1
  rw [hsplit, RemC6.integerGreedyRemainder_cons, if_pos htake,
    integerGreedyRemainder_mod_two_of_forall_even _ heven]
  omega

/-- A prime row has no rank strictly between `2` and `s` dividing `2 * s`. -/
theorem isolated_of_prime {s : ℕ} (hp : Nat.Prime s) :
    ∀ d : ℕ, 3 ≤ d → d < s → ¬ d ∣ 2 * s := by
  intro d hd hds hdvd
  have hnd : ¬ s ∣ d := fun hsd => by
    have := Nat.le_of_dvd (by omega) hsd
    omega
  have hcop : Nat.Coprime d s :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd |>.symm
  have : d ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- **The seam greedy remainder is odd at every prime row.** -/
theorem seamIntegerGreedyRemainder_odd_of_prime {s : ℕ} (hs : 3 ≤ s)
    (hp : Nat.Prime s) : seamIntegerGreedyRemainder s % 2 = 1 :=
  seamIntegerGreedyRemainder_odd_of_isolated hs (isolated_of_prime hp)

/-- **Cofinally many odd rows.**  Since the primes are unbounded, the remainder
is odd at arbitrarily large rows. -/
theorem odd_remainder_cofinally (N : ℕ) :
    ∃ s : ℕ, N ≤ s ∧ 5 ≤ s ∧ seamIntegerGreedyRemainder s % 2 = 1 := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max N 5)
  exact ⟨p, by omega, by omega, seamIntegerGreedyRemainder_odd_of_prime (by omega) hprime⟩

/-! ## 4. What the parity law removes from the hovering band -/

private theorem two_pow_mod_two {n : ℕ} (hn : 1 ≤ n) : (2 : ℕ) ^ n % 2 = 0 := by
  have : (2 : ℕ) ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  omega

/-- **No even offset at a prime row.**  The remainder of a prime row is never
`2 ^ s + c` for an even `c`; in particular it is never the half point itself. -/
theorem remainder_ne_two_pow_add_even {s c : ℕ} (hs : 3 ≤ s) (hp : Nat.Prime s)
    (hc : c % 2 = 0) : seamIntegerGreedyRemainder s ≠ 2 ^ s + c := by
  have hodd := seamIntegerGreedyRemainder_odd_of_prime hs hp
  have h2 := two_pow_mod_two (n := s) (by omega)
  omega

/-- The half point is never *attained* at a prime row. -/
theorem remainder_ne_two_pow {s : ℕ} (hs : 3 ≤ s) (hp : Nat.Prime s) :
    seamIntegerGreedyRemainder s ≠ 2 ^ s :=
  fun h => remainder_ne_two_pow_add_even hs hp (c := 0) rfl (by omega)

/-- At a prime row `Rem/C3`'s hit predicate is a *strict* inequality: the half
point itself is unreachable there. -/
theorem hitAt_iff_lt_of_prime {s : ℕ} (hs : 3 ≤ s) (hp : Nat.Prime s) :
    RemC3.HitAt s ↔ seamIntegerGreedyRemainder s < 2 ^ s := by
  have hne := remainder_ne_two_pow hs hp
  constructor
  · intro h; exact lt_of_le_of_ne h hne
  · intro h; exact le_of_lt h

/-- **`Rem/C1`'s persistent-surplus model is refuted at every prime row.**
`RemC1.surplusModel c` with `c` even — in particular `surplusModel 2`, the
sequence `Rem/C1` exhibits as satisfying every row-level constraint the corpus
owns — is *not* the true remainder at any prime row. -/
theorem ne_surplusModel_of_even {c : ℕ} (hc : c % 2 = 0) {s : ℕ} (hs : 3 ≤ s)
    (hp : Nat.Prime s) :
    seamIntegerGreedyRemainder s ≠ RemC1.surplusModel c s :=
  remainder_ne_two_pow_add_even hs hp hc

/-- The same, at cofinally many rows, for `Rem/C1`'s own model `2 ^ s + 2`. -/
theorem surplusModel_two_fails_cofinally (N : ℕ) :
    ∃ s : ℕ, N ≤ s ∧ 5 ≤ s ∧
      seamIntegerGreedyRemainder s ≠ RemC1.surplusModel 2 s := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max N 5)
  exact ⟨p, by omega, by omega, ne_surplusModel_of_even rfl (by omega) hprime⟩

/-- **`Rem/C1`'s forward-invariant band collapses to one point at prime rows.**
`RemC1.band_invariant` shows the row law cannot expel a trajectory from
`[2 ^ s + 2, 2 ^ s + 4]`.  At a prime row the true remainder can only occupy the
middle point of that band. -/
theorem c1_band_collapses_at_prime {s : ℕ} (hs : 3 ≤ s) (hp : Nat.Prime s)
    (hlo : 2 ^ s + 2 ≤ seamIntegerGreedyRemainder s)
    (hhi : seamIntegerGreedyRemainder s ≤ 2 ^ s + 4) :
    seamIntegerGreedyRemainder s = 2 ^ s + 3 := by
  have hodd := seamIntegerGreedyRemainder_odd_of_prime hs hp
  have h2 := two_pow_mod_two (n := s) (by omega)
  omega

/-- **The forced run's lower pin improves at prime rows.**  `Bit/R1` gives
`2 ^ s + 2 ≤ ρ s` under the forced run; parity removes the endpoint. -/
theorem remainder_ge_three_of_forcedRun {N s : ℕ} (h : BitR1.ForcedRun N)
    (hs : max N 3 ≤ s) (hp : Nat.Prime s) :
    2 ^ s + 3 ≤ seamIntegerGreedyRemainder s := by
  have hge := BitR1.remainder_ge_of_forcedRun h hs
  have hodd := seamIntegerGreedyRemainder_odd_of_prime (by omega) hp
  have h2 := two_pow_mod_two (n := s) (by omega)
  omega

/-! ## 5. The descent window narrows immediately below a prime row -/

/-- **`Bit/R1`'s descent window `[4, 2*s]` improves to `[5, 2*s]` at every row
whose successor is prime.**  The one-step correction
`4 * ρ s - ρ (s+1) - 2 ^ (s+1)` has the parity of `ρ (s+1)`, so it is odd — and
hence at least `5` — whenever row `s+1` is prime. -/
theorem descent_gap_ge_five_before_prime {s : ℕ} (hs : 3 ≤ s)
    (hp : Nat.Prime (s + 1)) (hbad : ¬ LargestSkipLateAt (s + 1)) :
    seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 5 ≤
      4 * seamIntegerGreedyRemainder s := by
  have hlaw := (BitR1.remainder_step_of_not_largestSkipLateAt hs hbad).1
  have hodd := seamIntegerGreedyRemainder_odd_of_prime (s := s + 1) (by omega) hp
  have h2 := two_pow_mod_two (n := s + 1) (by omega)
  omega

/-! ## 6. The hovering band is a statement about the low bits of `ρ s` -/

private theorem two_mul_lt_two_pow {s : ℕ} (hs : 5 ≤ s) : 2 * s < 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      have hp : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
      omega

/-- **The rigidity, made explicit.**  If row `s` sits in the hovering band
`2 ^ s < ρ s < 2 ^ s + 2 * s`, then for *every* `k` with `2 * s ≤ 2 ^ k ≤ 2 ^ s`
the residue `ρ s % 2 ^ k` is the surplus itself.  Equivalently: the binary
expansion of `ρ s` carries a run of zeros from bit `⌈log₂ (2*s)⌉` all the way up
to bit `s - 1`, a run of length `s - O(log s)`. -/
theorem hovering_low_bits {s k : ℕ} (_hs : 5 ≤ s) (hk : k ≤ s) (hbig : 2 * s ≤ 2 ^ k)
    (hlo : 2 ^ s < seamIntegerGreedyRemainder s)
    (hhi : seamIntegerGreedyRemainder s < 2 ^ s + 2 * s) :
    seamIntegerGreedyRemainder s % 2 ^ k = seamIntegerGreedyRemainder s - 2 ^ s := by
  obtain ⟨m, hm⟩ : (2 : ℕ) ^ k ∣ 2 ^ s := pow_dvd_pow 2 hk
  have hrho : seamIntegerGreedyRemainder s
      = (seamIntegerGreedyRemainder s - 2 ^ s) + 2 ^ k * m := by omega
  conv_lhs => rw [hrho]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **A dyadic pin-escape.**  One row at which `ρ s` is divisible by a power of
two exceeding `2 * s` escapes the hovering band outright: the surplus would be a
positive multiple of that power, hence at least `2 ^ k ≥ 2 * s`. -/
theorem pinEscape_of_dvd_two_pow {s k : ℕ} (hs : 5 ≤ s) (hk : k ≤ s)
    (hbig : 2 * s ≤ 2 ^ k) (hdvd : 2 ^ k ∣ seamIntegerGreedyRemainder s) :
    ¬ (2 ^ s < seamIntegerGreedyRemainder s ∧
        seamIntegerGreedyRemainder s < 2 ^ s + 2 * s) := by
  rintro ⟨hlo, hhi⟩
  have hmod := hovering_low_bits hs hk hbig hlo hhi
  have hz : seamIntegerGreedyRemainder s % 2 ^ k = 0 := by
    obtain ⟨t, ht⟩ := hdvd
    rw [ht]
    exact Nat.mul_mod_right _ _
  omega

/-- The parameter range of `pinEscape_of_dvd_two_pow` is never empty: `k = s`
always qualifies, since `2 * s < 2 ^ s` for `s ≥ 5`.  So the strongest instance
of the criterion is `2 ^ s ∣ ρ s`. -/
theorem pinEscape_of_dvd_two_pow_self {s : ℕ} (hs : 5 ≤ s)
    (hdvd : 2 ^ s ∣ seamIntegerGreedyRemainder s) :
    ¬ (2 ^ s < seamIntegerGreedyRemainder s ∧
        seamIntegerGreedyRemainder s < 2 ^ s + 2 * s) :=
  pinEscape_of_dvd_two_pow hs le_rfl (le_of_lt (two_mul_lt_two_pow hs)) hdvd

/-- The remainder is divisible by a power of two exceeding `2 * s` at
arbitrarily large rows. -/
def DyadicDepthCofinally : Prop :=
  ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ 5 ≤ s ∧
    ∃ k : ℕ, k ≤ s ∧ 2 * s ≤ 2 ^ k ∧ 2 ^ k ∣ seamIntegerGreedyRemainder s

theorem pinEscapesCofinally_of_dyadicDepth (h : DyadicDepthCofinally) :
    RemC3.PinEscapesCofinally := by
  intro N
  obtain ⟨s, hNs, hs5, k, hk, hbig, hdvd⟩ := h N
  exact ⟨s, hNs, hs5, pinEscape_of_dvd_two_pow hs5 hk hbig hdvd⟩

/-- **A sufficient condition for `#257`'s `1/2` question**, of a kind the
size layer cannot express: dyadic depth cofinally, together with `Rem/C3`'s
cofinal ceiling. -/
theorem half_mem_of_ceilingCofinally_of_dyadicDepth
    (h1 : RemC3.CeilingCofinally) (h2 : DyadicDepthCofinally) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  RemC3.half_mem_of_ceilingCofinally_of_pinEscapes h1
    (pinEscapesCofinally_of_dyadicDepth h2)

/-- **The hovering band, sharpened at prime rows.**  `Rem/C3` shows that a
cofinal ceiling plus failure of `1/2 ∈ mersenneAchievementSet` pins the
remainder into `(2 ^ s, 2 ^ s + 2 * s)` at every large row.  Parity removes the
lower endpoint at every prime row. -/
theorem pinned_odd_of_ceilingCofinally_of_not_half_mem
    (hceil : RemC3.CeilingCofinally) (hnot : (1 / 2 : ℝ) ∉ mersenneAchievementSet) :
    ∃ M : ℕ, ∀ s : ℕ, M ≤ s → Nat.Prime s →
      2 ^ s + 3 ≤ seamIntegerGreedyRemainder s ∧
        seamIntegerGreedyRemainder s < 2 ^ s + 2 * s := by
  obtain ⟨M, hpin⟩ := RemC3.pinned_of_ceilingCofinally_of_not_half_mem hceil hnot
  obtain ⟨N₀, hforced⟩ := BitR1.not_half_mem_iff_exists_forcedRun.mp hnot
  refine ⟨max (max M N₀) 3, fun s hs hp => ?_⟩
  have hMs : M ≤ s :=
    le_trans (le_trans (le_max_left M N₀) (le_max_left _ 3)) hs
  have hN₀s : max N₀ 3 ≤ s :=
    max_le (le_trans (le_trans (le_max_right M N₀) (le_max_left _ 3)) hs)
      (le_trans (le_max_right _ 3) hs)
  exact ⟨remainder_ge_three_of_forcedRun hforced hN₀s hp, (hpin s hMs).2⟩

/-! ## 7. Non-vacuity, in the kernel -/

section Certificates

set_option maxRecDepth 8000000

/-- Row `101` is prime, and the kernel agrees with the parity law there. -/
theorem remainder_odd_101 : seamIntegerGreedyRemainder 101 % 2 = 1 := by
  rw [← BitR3.rem_eq]
  decide +kernel

theorem remainder_odd_101' : seamIntegerGreedyRemainder 101 % 2 = 1 :=
  seamIntegerGreedyRemainder_odd_of_prime (by norm_num) (by norm_num)

/-- **The hypothesis of the parity law is doing work.**  Row `30` is composite —
`3, 5, 6, 10, 12, 15, 20` all divide `60` — and the remainder there is *even*.
So `seamIntegerGreedyRemainder_odd_of_isolated` is not a theorem about all rows,
and the isolation hypothesis cannot be dropped. -/
theorem remainder_even_30 : seamIntegerGreedyRemainder 30 % 2 = 0 := by
  rw [← BitR3.rem_eq]
  decide +kernel

/-- The isolation hypothesis genuinely fails at row `30`. -/
theorem not_isolated_30 : ¬ (∀ d : ℕ, 3 ≤ d → d < 30 → ¬ d ∣ 2 * 30) := by
  intro h
  exact h 3 (by norm_num) (by norm_num) (by norm_num)

/-- **The improved descent window is attained.**  Row `13` is prime and bad, so
`descent_gap_ge_five_before_prime` applies at `s = 12`; the kernel says the
correction there is exactly `5`.  `Bit/R1`'s window began at `4`. -/
theorem descent_gap_twelve :
    seamIntegerGreedyRemainder 13 + 2 ^ 13 + 5 = 4 * seamIntegerGreedyRemainder 12 := by
  simp only [BitR1.remOf_eq]
  decide +kernel

theorem descent_gap_ge_five_twelve :
    seamIntegerGreedyRemainder 13 + 2 ^ 13 + 5 ≤ 4 * seamIntegerGreedyRemainder 12 :=
  descent_gap_ge_five_before_prime (s := 12) (by norm_num) (by norm_num)
    BitR2.not_largestSkipLateAt_thirteen

/-- A second instance, at `s = 10`: row `11` is prime and bad, and the
correction is `7` — odd, as the parity law forces. -/
theorem descent_gap_ten :
    seamIntegerGreedyRemainder 11 + 2 ^ 11 + 7 = 4 * seamIntegerGreedyRemainder 10 := by
  simp only [BitR1.remOf_eq]
  decide +kernel

theorem descent_gap_ge_five_ten :
    seamIntegerGreedyRemainder 11 + 2 ^ 11 + 5 ≤ 4 * seamIntegerGreedyRemainder 10 :=
  descent_gap_ge_five_before_prime (s := 10) (by norm_num) (by norm_num)
    BitR2.not_largestSkipLateAt_eleven

/-- The contrast row.  Row `12` is composite, `descent_gap_ge_five_before_prime`
does not apply at `s = 11`, and the correction there is the *even* number `8`.
So the parity constraint is not a decoration: it is exactly what distinguishes
`s = 10, 12` from `s = 11`. -/
theorem descent_gap_eleven :
    seamIntegerGreedyRemainder 12 + 2 ^ 12 + 8 = 4 * seamIntegerGreedyRemainder 11 := by
  simp only [BitR1.remOf_eq]
  decide +kernel

/-- **The dyadic pin-escape hypothesis is realised.**  At row `575` the
remainder is divisible by `2 ^ 15 = 32768 ≥ 2 * 575`. -/
theorem rem_575_dyadic : BitR3.rem 575 % 2 ^ 15 = 0 := by decide +kernel

end Certificates

theorem dyadicDepth_575 : 2 ^ 15 ∣ seamIntegerGreedyRemainder 575 := by
  rw [← BitR3.rem_eq]
  exact Nat.dvd_of_mod_eq_zero rem_575_dyadic

/-- The inner predicate of `DyadicDepthCofinally` holds at `s = 575`, so the
criterion is not empty at the near end.  (Cofinality itself is **not** proved.
See the measurement note: over `[5, 1200]` row `575` is the *only* row realising
it, and at that row `ρ 575 ≤ 2 ^ 575` already, so `Bit/R2`'s own criterion fires
there too.  The dyadic criterion is not yet known to do independent work.) -/
theorem dyadicDepth_witness :
    ∃ k : ℕ, k ≤ 575 ∧ 2 * 575 ≤ 2 ^ k ∧ 2 ^ k ∣ seamIntegerGreedyRemainder 575 :=
  ⟨15, by norm_num, by norm_num, dyadicDepth_575⟩

/-- **The hypothesis of `hovering_low_bits` is realised.**  Row `8` is the one
row of `[5, 1300]` at which the remainder genuinely sits in the pin window
(`Rem/C3.Witness.pin_occupied_eight`: `ρ 8 = 265`, window `(256, 272)`).  There
`k = 4` qualifies (`2 * 8 = 16 = 2 ^ 4`), and the low four bits of `ρ 8` are
exactly the surplus `9`. -/
theorem hovering_low_bits_eight :
    seamIntegerGreedyRemainder 8 % 2 ^ 4 = seamIntegerGreedyRemainder 8 - 2 ^ 8 :=
  hovering_low_bits (s := 8) (k := 4) (by norm_num) (by norm_num) (by norm_num)
    RemC3.Witness.pin_occupied_eight.1 RemC3.Witness.pin_occupied_eight.2

/-! ## 8. The sharp negative: parity alone cannot close the band -/

/-- **The 2-adic layer removes exactly the even half of the hovering band.**
There is an explicit sequence that is odd at every row `s ≥ 1` — so it is
consistent with the parity law at every prime row — satisfies `Bit/R1`'s
two-sided row law, every row-level constraint listed in `Rem/C1`, and never
returns to the half point.  So no consequence of the row law *together with*
the mod-`2` information proved here can imply
`RemainderReachesHalfPointCofinally`. -/
theorem exists_persistent_odd_surplus_model :
    ∃ f : ℕ → ℕ, BitR1.StepLaw f 5 ∧ (∀ s : ℕ, 1 ≤ s → f s % 2 = 1) ∧
      ∀ s : ℕ, 5 ≤ s →
        2 ^ s < f s ∧
          3 * f s < 7 * 2 ^ s + 4 ∧
          f s < 2 ^ s + 2 * s ∧
          2 ^ (s + 1) + 4 ≤ 4 * f s ∧
          f s ≤ 2 ^ (s + 1) ∧
          f s ≤ seamSubsetTarget s := by
  refine ⟨RemC1.surplusModel 3,
    RemC1.surplusModel_stepLaw (by norm_num) (by norm_num), ?_,
    fun s hs => RemC1.surplusModel_constraints (by norm_num) hs (by omega)⟩
  intro s hs
  have h2 := two_pow_mod_two (n := s) hs
  simp only [RemC1.surplusModel]
  omega

/-- The model of `exists_persistent_odd_surplus_model` sits *inside* `Rem/C1`'s
forward-invariant band at every row, at the one point `c1_band_collapses_at_prime`
leaves open. -/
theorem odd_surplus_model_in_c1_band (s : ℕ) :
    2 ^ s + 2 ≤ RemC1.surplusModel 3 s ∧ RemC1.surplusModel 3 s ≤ 2 ^ s + 4 := by
  simp only [RemC1.surplusModel]
  omega

end ErdosProblems.ThreeT3
