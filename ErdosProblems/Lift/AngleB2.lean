/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.Recon257

/-!
# Angle B2: a conditional cofactor-budget calculation

`ErdosProblems/Lift/Recon257.lean` builds the local exclusion ratchet for the
hypothetical final middle cell of charge `-2` and shows that, with the forced
support `{2, 3, 6, 7, 14, 20, 21, 26}`, its non-dying set is exactly the `412`
rank-`26` survivor phases.  The present file studies an auxiliary budget obtained
by adding three row-dependent candidate ranks.  It does **not** prove that those
ranks occur in the concrete greedy support, and it does not empty the concrete
survivor set.

The pulse `rowPulse s d = [d ∣ 2s+2] + 2 * [d ∣ 2s+1]` is fired by every divisor
of `2s+1` or `2s+2`.  The following three row-dependent ranks are used:

* `(2s+1)/3`  (when `3 ∣ 2s+1`) — divides `2s+1`, pulse `2`;
* `2(s+1)/3`  (when `3 ∣ s+1`)  — divides `2s+2`, pulse `1`;
* `(s+1)/2`   (when `2 ∣ s+1`)  — divides `2s+2`, pulse `1`.

For the rows used below (`s ≥ 61`), each candidate rank that occurs lies in
`(s/2, s)`.  If these ranks are treated as certified support, they add the
floor `![0,3,1,1,2,2]`, indexed by `s % 6`.

**PROVED:** `cofRatchet_finite_core` checks that the resulting auxiliary budget
`cofRun D 3` is zero for each of the `2730` phases, and
`cofRatchet_run_eq_zero` extends this periodic calculation to every `D`.  These
theorems concern `cofRun`; they do not by themselves say that a concrete greedy
class dies.

**PROVED, CONDITIONAL:** `allRight_landingExcess_two_impossible` derives a
contradiction only after assuming an all-right tail, the exact landing equation
`Recon257.seamExcess (D+1) = 2`, and selection of the cofactor ranks at the first
three rows.  The last assumption is `hcof`.

**MEASURED / REFUTED ON THE CHECKED RANGE:** the landing equation has no
instance for `s ∈ [5,102]`, including the checked part of the theorem's
consumed range `s = D+1 ≥ 61`.  At `s = 58,...,65`, the measured magnitudes
are on the `2^s` scale.  Also, `hcof` fails at
`D = 101, 122, 164, 314, 545, 629, 1112`.  In the audited range
`D ∈ [60,700)`, every class satisfying `hcof` already dies by depth `3` under
the concrete `belowPulse`.

**RETRACTED:** earlier prose in this file described these results as emptying
the survivor set and leaving no residue classes.  Neither conclusion follows.
**MEASURED:** the auxiliary calculation closes no additional class in the
audited range.  The half-value membership question remains open.
-/

namespace Erdos249257

namespace AngleB2

open HalfCylinderIntegerGreedy
open scoped BigOperators

/-! ## The candidate cofactor ranks -/

/-- The candidate **cofactor ranks** at row `s`: divisors of `2s+1` and `2s+2`
obtained from the cofactors `3` and `4`.  Which ones occur in this candidate
set is decided by `s % 6`; membership in the concrete greedy support is a
separate assumption. -/
def cofRanks (s : ℕ) : Finset ℕ :=
  if s % 6 = 1 then {(2 * s + 1) / 3, (s + 1) / 2}
  else if s % 6 = 2 then {2 * (s + 1) / 3}
  else if s % 6 = 3 then {(s + 1) / 2}
  else if s % 6 = 4 then {(2 * s + 1) / 3}
  else if s % 6 = 5 then {2 * (s + 1) / 3, (s + 1) / 2}
  else ∅

/-- The lower bound on the sum of `rowPulse` over the candidate cofactor ranks.
This definition alone makes no claim that the ranks lie in the greedy support. -/
def cofFloor (s : ℕ) : ℕ :=
  if s % 6 = 1 then 3
  else if s % 6 = 2 then 1
  else if s % 6 = 3 then 1
  else if s % 6 = 4 then 2
  else if s % 6 = 5 then 2
  else 0

theorem cofRanks_cases {s d : ℕ} (hd : d ∈ cofRanks s) :
    d = (2 * s + 1) / 3 ∨ d = 2 * (s + 1) / 3 ∨ d = (s + 1) / 2 := by
  unfold cofRanks at hd
  split_ifs at hd <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] at hd <;> tauto

theorem cofRanks_ge (s : ℕ) (hs : 61 ≤ s) {d : ℕ} (hd : d ∈ cofRanks s) : 27 ≤ d := by
  rcases cofRanks_cases hd with rfl | rfl | rfl <;> omega

theorem cofRanks_lt (s : ℕ) (hs : 61 ≤ s) {d : ℕ} (hd : d ∈ cofRanks s) : d < s := by
  rcases cofRanks_cases hd with rfl | rfl | rfl <;> omega

/-- The cofactor ranks are disjoint from the eight forced ranks. -/
theorem cofRanks_disjoint (s : ℕ) (hs : 61 ≤ s) :
    Disjoint ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) (cofRanks s) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h27 := cofRanks_ge s hs hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-! ## The arithmetic pulse of the candidate ranks -/

theorem cofFloor_le_cofPulse (s : ℕ) (hs : 61 ≤ s) :
    cofFloor s ≤ ∑ d ∈ cofRanks s, rowPulse s d := by
  have h6 : s % 6 = 0 ∨ s % 6 = 1 ∨ s % 6 = 2 ∨ s % 6 = 3 ∨ s % 6 = 4 ∨ s % 6 = 5 := by
    omega
  rcases h6 with h | h | h | h | h | h
  · simp only [cofFloor, cofRanks, h]
    norm_num
  · -- `s ≡ 1 (mod 6)` : ranks `(2s+1)/3` and `(s+1)/2`, pulses `2` and `1`.
    obtain ⟨q, rfl⟩ : ∃ q, s = 6 * q + 1 := ⟨s / 6, by omega⟩
    have e1 : (2 * (6 * q + 1) + 1) / 3 = 4 * q + 1 := by omega
    have e2 : (6 * q + 1 + 1) / 2 = 3 * q + 1 := by omega
    have hset : cofRanks (6 * q + 1) = {4 * q + 1, 3 * q + 1} := by
      unfold cofRanks; rw [if_pos h, e1, e2]
    have hne : (4 * q + 1) ∉ ({3 * q + 1} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    have r1 : 2 ≤ rowPulse (6 * q + 1) (4 * q + 1) := by
      have hdv : (4 * q + 1) ∣ 2 * (6 * q + 1) + 1 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    have r2 : 1 ≤ rowPulse (6 * q + 1) (3 * q + 1) := by
      have hdv : (3 * q + 1) ∣ 2 * (6 * q + 1) + 2 := ⟨4, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_insert hne, Finset.sum_singleton]
    unfold cofFloor
    rw [if_pos h]
    omega
  · -- `s ≡ 2 (mod 6)` : rank `2(s+1)/3`, pulse `1`.
    obtain ⟨q, rfl⟩ : ∃ q, s = 6 * q + 2 := ⟨s / 6, by omega⟩
    have e1 : 2 * (6 * q + 2 + 1) / 3 = 4 * q + 2 := by omega
    have hset : cofRanks (6 * q + 2) = {4 * q + 2} := by
      unfold cofRanks; rw [if_neg (by omega), if_pos h, e1]
    have r1 : 1 ≤ rowPulse (6 * q + 2) (4 * q + 2) := by
      have hdv : (4 * q + 2) ∣ 2 * (6 * q + 2) + 2 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cofFloor
    rw [if_neg (by omega), if_pos h]
    omega
  · -- `s ≡ 3 (mod 6)` : rank `(s+1)/2`, pulse `1`.
    obtain ⟨q, rfl⟩ : ∃ q, s = 6 * q + 3 := ⟨s / 6, by omega⟩
    have e1 : (6 * q + 3 + 1) / 2 = 3 * q + 2 := by omega
    have hset : cofRanks (6 * q + 3) = {3 * q + 2} := by
      unfold cofRanks; rw [if_neg (by omega), if_neg (by omega), if_pos h, e1]
    have r1 : 1 ≤ rowPulse (6 * q + 3) (3 * q + 2) := by
      have hdv : (3 * q + 2) ∣ 2 * (6 * q + 3) + 2 := ⟨4, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cofFloor
    rw [if_neg (by omega), if_neg (by omega), if_pos h]
    omega
  · -- `s ≡ 4 (mod 6)` : rank `(2s+1)/3`, pulse `2`.
    obtain ⟨q, rfl⟩ : ∃ q, s = 6 * q + 4 := ⟨s / 6, by omega⟩
    have e1 : (2 * (6 * q + 4) + 1) / 3 = 4 * q + 3 := by omega
    have hset : cofRanks (6 * q + 4) = {4 * q + 3} := by
      unfold cofRanks
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h, e1]
    have r1 : 2 ≤ rowPulse (6 * q + 4) (4 * q + 3) := by
      have hdv : (4 * q + 3) ∣ 2 * (6 * q + 4) + 1 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cofFloor
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]
    omega
  · -- `s ≡ 5 (mod 6)` : ranks `2(s+1)/3` and `(s+1)/2`, pulses `1` and `1`.
    obtain ⟨q, rfl⟩ : ∃ q, s = 6 * q + 5 := ⟨s / 6, by omega⟩
    have e1 : 2 * (6 * q + 5 + 1) / 3 = 4 * q + 4 := by omega
    have e2 : (6 * q + 5 + 1) / 2 = 3 * q + 3 := by omega
    have hset : cofRanks (6 * q + 5) = {4 * q + 4, 3 * q + 3} := by
      unfold cofRanks
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos h, e1, e2]
    have hne : (4 * q + 4) ∉ ({3 * q + 3} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    have r1 : 1 ≤ rowPulse (6 * q + 5) (4 * q + 4) := by
      have hdv : (4 * q + 4) ∣ 2 * (6 * q + 5) + 2 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    have r2 : 1 ≤ rowPulse (6 * q + 5) (3 * q + 3) := by
      have hdv : (3 * q + 3) ∣ 2 * (6 * q + 5) + 2 := ⟨4, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_insert hne, Finset.sum_singleton]
    unfold cofFloor
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]
    omega

/-! ## The conditional total floor -/

/-- The auxiliary floor: eight forced ranks plus the candidate cofactor ranks. -/
def totalFloor (s : ℕ) : ℕ := Recon257.pulseFloor s + cofFloor s

theorem one_le_totalFloor (s : ℕ) : 1 ≤ totalFloor s := by
  have := Recon257.one_le_pulseFloor s
  unfold totalFloor
  omega

theorem totalFloor_add_period (s : ℕ) : totalFloor (s + 2730) = totalFloor s := by
  unfold totalFloor cofFloor
  rw [Recon257.pulseFloor_add_period, show (s + 2730) % 6 = s % 6 by omega]

/-- **PROVED, CONDITIONAL.**  The auxiliary floor is a lower bound for the
below-pulse of the concrete greedy seam cut once the candidate cofactor ranks
are assumed to be selected. -/
theorem totalFloor_le_belowPulse (s : ℕ) (hs : 61 ≤ s)
    (hcof : cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    totalFloor s ≤ (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega)
  have h7 := seven_mem_seamGreedySupport s (by omega)
  have h14 := fourteen_mem_seamGreedySupport s (by omega)
  have h20 := twenty_mem_seamGreedySupport s (by omega)
  have h21 := twentyOne_mem_seamGreedySupport s (by omega)
  have h26 := twentySix_mem_seamGreedySupport s (by omega)
  have hsmall : ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ⊆
      seamWordSupport (seamGreedyWord s) := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h236.1
    · exact h236.2.1
    · exact h236.2.2
    · exact h7
    · exact h14
    · exact h20
    · exact h21
    · exact h26
  have hsub : (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cofRanks s) ⊆
      seamWordSupport (seamGreedyWord s) := Finset.union_subset hsmall hcof
  have hsum :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cofRanks s), rowPulse s d ≤
        ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hsplit :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cofRanks s), rowPulse s d =
        (∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d) +
          ∑ d ∈ cofRanks s, rowPulse s d :=
    Finset.sum_union (cofRanks_disjoint s hs)
  have hexp : ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d =
      Recon257.pulseFloor s := by
    rw [Recon257.pulseFloor_eq_rowPulseSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hcofp := cofFloor_le_cofPulse s hs
  change totalFloor s ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  unfold totalFloor
  rw [hsplit, hexp] at hsum
  omega

/-! ## The cofactor ratchet -/

/-- One step of the auxiliary cofactor budget.  `0` is absorbing. -/
def cofStep (s b : ℕ) : ℕ :=
  if 3 * totalFloor s + 4 ≤ 4 * b then 4 * b - (3 * totalFloor s + 3) else 0

/-- The auxiliary orbit of the integer budget `3 * E - 3`, initialized to the
value corresponding to the hypothetical landing equation `E = 2` at `D+1`.
The definition does not assert that such a landing occurs. -/
def cofRun (D : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => cofStep (D + 1 + k) (cofRun D k)

@[simp] theorem cofRun_zero (D : ℕ) : cofRun D 0 = 3 := rfl

theorem cofRun_succ (D k : ℕ) :
    cofRun D (k + 1) = cofStep (D + 1 + k) (cofRun D k) := rfl

theorem cofRun_add_period (D k : ℕ) : cofRun (D + 2730) k = cofRun D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [cofRun_succ, cofRun_succ, ih]
      unfold cofStep
      rw [show D + 2730 + 1 + k = (D + 1 + k) + 2730 by ring, totalFloor_add_period]

theorem cofRun_add_mul_period (D k n : ℕ) :
    cofRun (D + 2730 * n) k = cofRun D k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show D + 2730 * (n + 1) = (D + 2730 * n) + 2730 by ring, cofRun_add_period, ih]

theorem cofRun_mod (D k : ℕ) : cofRun D k = cofRun (D % 2730) k := by
  conv_lhs => rw [show D = D % 2730 + 2730 * (D / 2730) by
    rw [Nat.add_comm]; exact (Nat.div_add_mod D 2730).symm]
  exact cofRun_add_mul_period _ _ _

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- **PROVED (finite auxiliary calculation).**  Each of the `2730` joint phases
has `cofRun D 3 = 0`.  This is a statement about the budget formed by treating
`cofRanks` as certified support.  It does not prove that the concrete greedy
support contains those ranks or that the concrete survivor set is empty. -/
theorem cofRatchet_finite_core : ∀ D < 2730, cofRun D 3 = 0 := by
  decide +kernel

/-- **PROVED.**  Periodicity extends the finite calculation to
`cofRun D 3 = 0` for every `D`; the conclusion still concerns only `cofRun`. -/
theorem cofRatchet_run_eq_zero (D : ℕ) : cofRun D 3 = 0 := by
  rw [cofRun_mod]
  exact cofRatchet_finite_core _ (Nat.mod_lt _ (by norm_num))

/-- **PROVED.**  A `Recon257.SurvivorPhase` also has zero auxiliary cofactor
budget at depth `3`.  The survivor hypothesis is not used, so this theorem does
not transfer auxiliary budget death to the concrete greedy orbit. -/
theorem survivorPhase_dies (D : ℕ) (_h : Recon257.SurvivorPhase D) : cofRun D 3 = 0 :=
  cofRatchet_run_eq_zero D

/-! ### Absorption and comparison laws for the auxiliary budget -/

/-- **PROVED.**  `0` is absorbing. -/
theorem cofStep_zero (s : ℕ) : cofStep s 0 = 0 := by
  unfold cofStep
  rw [if_neg (by have := one_le_totalFloor s; omega)]

theorem cofRun_eq_zero_of_le {D j k : ℕ} (hjk : j ≤ k) (hj : cofRun D j = 0) :
    cofRun D k = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction i with
  | zero => simpa using hj
  | succ i ih => rw [show j + (i + 1) = (j + i) + 1 by ring, cofRun_succ, ih, cofStep_zero]

/-- **PROVED.**  Once the auxiliary budget reaches zero it remains zero; by
`cofRatchet_run_eq_zero` this holds from depth `3` onward for every `D`. -/
theorem cofRun_eq_zero_of_three_le (D k : ℕ) (hk : 3 ≤ k) : cofRun D k = 0 :=
  cofRun_eq_zero_of_le hk (cofRatchet_run_eq_zero D)

/-- **PROVED.**  One-step comparison for the auxiliary budget.  On the live
branch there is equality after subtracting `3 * totalFloor + 3` from four times
the preceding budget; on the zero branch the displayed inequality remains
valid.  The undiscounted values `cofRun D k` need not decrease before reaching
zero. -/
theorem cofRun_potential_step (D k : ℕ) :
    4 * cofRun D k ≤ cofRun D (k + 1) + 3 * totalFloor (D + 1 + k) + 3 := by
  rw [cofRun_succ]
  unfold cofStep
  split_ifs with h <;> omega

/-- **PROVED.**  Enlarging the pulse floor from `Recon257.pulseFloor` to
`totalFloor` can only shrink the corresponding auxiliary budget.  Thus
`cofRun D k ≤ Recon257.ratchetRun D k`.  This comparison does not certify that
the added cofactor ranks belong to the concrete greedy support. -/
theorem cofRun_le_ratchetRun (D k : ℕ) : cofRun D k ≤ Recon257.ratchetRun D k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [cofRun_succ, Recon257.ratchetRun_succ]
      have hfl : Recon257.pulseFloor (D + 1 + k) ≤ totalFloor (D + 1 + k) := by
        unfold totalFloor; omega
      unfold cofStep Recon257.ratchetStep
      split_ifs with h1 h2 h2 <;> omega

/-! ## Soundness -/

/-- **PROVED, CONDITIONAL.**  Under `hright`, `hlanding`, and `hcof`, the
auxiliary budget dominates `3 * seamExcess - 3` for the first three steps.
Only the rows `D+1`, `D+2`, and `D+3` are used. -/
theorem cofRun_bound
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hcof : ∀ s : ℕ, D + 1 ≤ s → s < D + 4 →
      cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    ∀ k, k ≤ 3 → 3 * Recon257.seamExcess (D + 1 + k) - 3 ≤ (cofRun D k : ℤ) := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  intro k
  induction k with
  | zero =>
      intro _
      simp only [Nat.add_zero, cofRun_zero, hlanding]
      norm_num
  | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      have hs : D + 1 ≤ D + 1 + k := by omega
      have hstep := (horbit (D + 1 + k) hs).2
      have hrec : Recon257.seamExcess (D + 1 + (k + 1)) =
          4 * Recon257.seamExcess (D + 1 + k) -
            ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) - 4 := by
        simpa [Recon257.seamExcess, show D + 1 + (k + 1) = (D + 1 + k) + 1 by ring] using hstep
      have hfloor : (totalFloor (D + 1 + k) : ℤ) ≤
          ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
        exact_mod_cast totalFloor_le_belowPulse (D + 1 + k) (by omega)
          (hcof (D + 1 + k) (by omega) (by omega))
      have hmain : 3 * Recon257.seamExcess (D + 1 + (k + 1)) - 3 ≤
          4 * (cofRun D k : ℤ) - (3 * (totalFloor (D + 1 + k) : ℤ) + 3) := by
        rw [hrec]; omega
      rw [cofRun_succ]
      unfold cofStep
      split_ifs with hcond
      · have hle : 3 * totalFloor (D + 1 + k) + 3 ≤ 4 * cofRun D k := by omega
        have hcast :
            ((4 * cofRun D k - (3 * totalFloor (D + 1 + k) + 3) : ℕ) : ℤ) =
              4 * (cofRun D k : ℤ) - (3 * (totalFloor (D + 1 + k) : ℤ) + 3) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [hcast]
        exact hmain
      · have hcondZ : 4 * (cofRun D k : ℤ) ≤ 3 * (totalFloor (D + 1 + k) : ℤ) + 3 := by
          have hnat : 4 * cofRun D k ≤ 3 * totalFloor (D + 1 + k) + 3 := by omega
          exact_mod_cast hnat
        simp only [Nat.cast_zero]
        omega

/-- **PROVED, CONDITIONAL.**  The four hypotheses are inconsistent: an
all-right tail, the landing equation `seamExcess (D+1) = 2`, and cofactor-rank
selection at the first three rows cannot all hold for `D ≥ 60`.

This theorem does not empty the concrete survivor set.  **MEASURED:** the
landing equation has no instance for `s ∈ [5,102]`; `hcof` fails on the known
surviving classes `D = 101, 122, 164, 314, 545, 629, 1112`; and every class
satisfying `hcof` in `D ∈ [60,700)` already dies by depth `3` under the
concrete `belowPulse`. -/
theorem allRight_landingExcess_two_impossible
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hcof : ∀ s : ℕ, D + 1 ≤ s → s < D + 4 →
      cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    False := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  have hbound := cofRun_bound D hD hright hlanding hcof 3 le_rfl
  rw [cofRatchet_run_eq_zero D] at hbound
  have hpos : 0 < Recon257.seamExcess (D + 1 + 3) := by
    have := (horbit (D + 1 + 3) (by omega)).1
    simpa [Recon257.seamExcess] using this
  have hone : Recon257.seamExcess (D + 1 + 3) = 1 := by
    simp only [Nat.cast_zero] at hbound
    omega
  have hstep := (horbit (D + 1 + 3) (by omega)).2
  have hrec : Recon257.seamExcess (D + 1 + 3 + 1) =
      4 * Recon257.seamExcess (D + 1 + 3) -
        ((seamAdjacentCut (D + 1 + 3) (by omega : 5 ≤ D + 1 + 3)).belowPulse : ℤ) - 4 := by
    simpa [Recon257.seamExcess] using hstep
  have hnext : 0 < Recon257.seamExcess (D + 1 + 3 + 1) := by
    have := (horbit (D + 1 + 3 + 1) (by omega)).1
    simpa [Recon257.seamExcess] using this
  have hfloor : (Recon257.pulseFloor (D + 1 + 3) : ℤ) ≤
      ((seamAdjacentCut (D + 1 + 3) (by omega : 5 ≤ D + 1 + 3)).belowPulse : ℤ) := by
    exact_mod_cast Recon257.pulseFloor_le_belowPulse (D + 1 + 3) (by omega)
  have hone' : (1 : ℤ) ≤ (Recon257.pulseFloor (D + 1 + 3) : ℤ) := by
    exact_mod_cast Recon257.one_le_pulseFloor (D + 1 + 3)
  rw [hone] at hrec
  omega

/-- **PROVED, CONDITIONAL.**  This packages
`allRight_landingExcess_two_impossible` using middle-cell hypotheses that imply
the landing equation.  It still assumes the all-right tail and `hcof`; it is
not an unconditional exclusion of any residue class. -/
theorem finalMiddleCell_neg_two_impossible
    (D : ℕ) (hD : 60 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega : 5 ≤ D)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega : 5 ≤ D)).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse <
          (seamAdjacentCut D (by omega : 5 ≤ D)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega : 5 ≤ D)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse : ℤ) - 4 = -2)
    (hcof : ∀ s : ℕ, D + 1 ≤ s → s < D + 4 →
      cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    False :=
  allRight_landingExcess_two_impossible D hD hright
    (Recon257.seamExcess_landing_eq_two D (by omega) hncarry hmiddle hcell) hcof

/-!
## Status of the calculation

**PROVED:** `cofRatchet_finite_core` checks `cofRun D 3 = 0` for every phase
`D < 2730`; periodicity gives the same auxiliary-budget equation for every
`D`.  The undiscounted budget is not a monotone decreasing quantity before it
reaches zero.  What is proved is the finite depth-`3` calculation, the absorbing
zero law, and the comparison with `Recon257.ratchetRun`.

To compare this auxiliary budget with the concrete `belowPulse`, the proof
requires `hcof`.  For the three rows `s ∈ {D+1, D+2, D+3}`, this assumption says

* `(2s+1)/3 ∈ seamWordSupport (seamGreedyWord s)`  when `s ≡ 1, 4 (mod 6)`;
* `2(s+1)/3 ∈ seamWordSupport (seamGreedyWord s)`  when `s ≡ 2, 5 (mod 6)`;
* `(s+1)/2 ∈ seamWordSupport (seamGreedyWord s)`   when `s ≡ 1, 3, 5 (mod 6)`.

There are at most four rank-membership assertions over the three consecutive
rows.  The all-right equations add only the new top rank; they do not themselves
assert any of these memberships in the pre-existing part of the support.

**MEASURED:** individual cofactor-rank selections occur about half the time, but
the three-row conjunction `hcof` holds for only `61/640` values of
`D ∈ [60,700)`.  Every one of those `61` values already dies by depth `3` when
the concrete `belowPulse` is used.  Direct computation also gives
`¬ hcof` at `D = 101, 122, 164, 314, 545, 629, 1112`, the classes that survive
the concrete affine orbit to depth `25` in the audited range below `1370`.

The landing hypothesis is a separate antecedent.  **MEASURED / REFUTED ON THE
CHECKED RANGE:** `Recon257.seamExcess s = 2` has no solution for
`s ∈ [5,102]`; for example its values at `s = 58,...,65` are
`-59595710280535285`, `-238382841122141149`,
`-953531364488564606`, `797560560473129479`,
`3190242241892517909`, `-5685775106139480035`,
`14150387722861183090`, and `-17185425403393474124`.
Thus the landing antecedent of `allRight_landingExcess_two_impossible` is false
throughout that checked range.

**RETRACTED:** `hcof` is not the remaining #257 problem, the auxiliary budget
does not certify an empty survivor set, and this file does not close the
all-right-tail branch.  It proves a conditional finite budget calculation and
records the assumptions required to connect that calculation to the concrete
greedy orbit.
-/

end AngleB2

end Erdos249257
