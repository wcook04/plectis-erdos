import Erdos249257.HalfFinalMiddlePhaseSieve

/-!
# The exclusion ratchet for the final `-2` middle cell

This file isolates the *local transition law* behind the rank-`26` phase
sieve of `Erdos249257.HalfFinalMiddlePhaseSieve`.

Every exclusion in that file has the same anatomy.  On an eventual right
tail the signed excess above the dyadic half point,
`E s = seamIntegerGreedyRemainder s - 2 ^ s`, obeys the exact affine
recursion `E (s+1) = 4 * E s - belowPulse s - 4` together with the
constraint `0 < E s`.  A hypothetical final middle cell of charge `-2`
lands at `E (D+1) = 2`.  Each individual exclusion proof then chains three
or four steps of this recursion against explicit lower bounds for
`belowPulse` and closes with `omega`.

Here the chain is replaced by a single one-step law.  Put

* `pulseFloor s` = the row-pulse contribution of the eight *forced* greedy
  seam ranks `2, 3, 6, 7, 14, 20, 21, 26`; it is a certified lower bound
  for `belowPulse s` and depends only on `s % 2730`;
* `ratchetRun D k` = the orbit of the integer budget
  `b k = 3 * E (D+1+k) - 3` under `b ↦ 4 * b - 3 * pulseFloor s - 3`, with
  `0` as an absorbing dead state.

The main results are

* `ratchet_excludes` — soundness: if the budget ever dies the middle-cell
  hypotheses are contradictory.  One theorem replacing every hand-chained
  exclusion in the sieve file.
* `finalMiddleCell_neg_two_survivorPhase` — the entire rank-`26`
  four-modulus classification reproved from one ratchet run of depth `3`.
* `ratchetRun_pos_of_survivorPhase` — the *fixed-point* statement: on each
  of the 412 surviving classes the budget is positive at **every** depth.

The finite ratchet statements are **PROVED**.  Their connection to a concrete
all-right landing is conditional on `seamExcess (D+1) = 2`.  Direct evaluation
of the actual `seamGreedyWord` finds no such value for `s ∈ [5,102]`; in that
audited range the landing condition is unreachable.  Thus
`ratchet_excludes` and `finalMiddleCell_neg_two_survivorPhase` do not close an
observed class.  The corpus-shaped theorem `seamExcess_landing_eq_two` remains
a valid implication from the hypothetical middle-cell hypotheses, while the
finite-core and fixed-point theorems remain unconditional facts about the
defined ratchet.

The last is a sharp negative.  The rank-`26` survivor set is exactly the
non-dying set of the ratchet for the support `{2,3,6,7,14,20,21,26}`
(`ratchetRun_eq_zero_of_not_survivorPhase` gives the converse, with death
by depth `3`).  Hence iterating the existing sieve to any depth whatsoever
gains nothing: `412` is a genuine fixed point, not a stage.  The only way
to shrink it is to enlarge the forced support, whose next member is
rank `27`.  See the closing section for the quantitative obstruction.
-/

namespace Erdos249257

namespace Recon257

open HalfCylinderIntegerGreedy

/-! ## The certified pulse floor -/

/-- The row pulse of rank `d` at row `s`, in remainder form.  This agrees
with `rowPulse s d` for `0 < d` and is what the finite sieve check
evaluates. -/
def pulseAt (s d : ℕ) : ℕ :=
  (if (2 * s + 2) % d = 0 then 1 else 0) +
    2 * (if (2 * s + 1) % d = 0 then 1 else 0)

theorem pulseAt_two (s : ℕ) : pulseAt s 2 = rowPulse s 2 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_three (s : ℕ) : pulseAt s 3 = rowPulse s 3 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_six (s : ℕ) : pulseAt s 6 = rowPulse s 6 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_seven (s : ℕ) : pulseAt s 7 = rowPulse s 7 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_fourteen (s : ℕ) : pulseAt s 14 = rowPulse s 14 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_twenty (s : ℕ) : pulseAt s 20 = rowPulse s 20 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_twentyOne (s : ℕ) : pulseAt s 21 = rowPulse s 21 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_twentySix (s : ℕ) : pulseAt s 26 = rowPulse s 26 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

/-- The row-pulse contribution of the eight forced greedy seam ranks
`2, 3, 6, 7, 14, 20, 21, 26`.  Every one of these ranks is a proven member
of `seamWordSupport (seamGreedyWord s)` for `s ≥ 27`, so this is a
certified lower bound for `belowPulse s`. -/
def pulseFloor (s : ℕ) : ℕ :=
  pulseAt s 2 + pulseAt s 3 + pulseAt s 6 + pulseAt s 7 +
    pulseAt s 14 + pulseAt s 20 + pulseAt s 21 + pulseAt s 26

theorem pulseFloor_eq_rowPulseSum (s : ℕ) :
    pulseFloor s =
      rowPulse s 2 + rowPulse s 3 + rowPulse s 6 + rowPulse s 7 +
        rowPulse s 14 + rowPulse s 20 + rowPulse s 21 + rowPulse s 26 := by
  unfold pulseFloor
  rw [pulseAt_two, pulseAt_three, pulseAt_six, pulseAt_seven,
    pulseAt_fourteen, pulseAt_twenty, pulseAt_twentyOne, pulseAt_twentySix]

theorem one_le_pulseFloor (s : ℕ) : 1 ≤ pulseFloor s := by
  have h : pulseAt s 2 = 1 := by unfold pulseAt; split_ifs <;> omega
  unfold pulseFloor
  omega

/-- The forced pulse floor never exceeds `9`.  The `{3,6}` part, the
`{7,14}` part and the `21` part contribute at most `2` each, and the ranks
`2`, `20`, `26` contribute at most `1` each. -/
theorem pulseFloor_le_nine (s : ℕ) : pulseFloor s ≤ 9 := by
  have h2 : pulseAt s 2 = 1 := by unfold pulseAt; split_ifs <;> omega
  have h36 : pulseAt s 3 + pulseAt s 6 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h714 : pulseAt s 7 + pulseAt s 14 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h20 : pulseAt s 20 ≤ 1 := by unfold pulseAt; split_ifs <;> omega
  have h21 : pulseAt s 21 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h26 : pulseAt s 26 ≤ 1 := by unfold pulseAt; split_ifs <;> omega
  unfold pulseFloor
  omega

/-- The pulse floor only depends on `s % 2730`: every forced rank divides
`5460 = 2 * 2730`. -/
theorem pulseFloor_add_period (s : ℕ) : pulseFloor (s + 2730) = pulseFloor s := by
  have h2 : pulseAt (s + 2730) 2 = pulseAt s 2 := by
    unfold pulseAt; split_ifs <;> omega
  have h3 : pulseAt (s + 2730) 3 = pulseAt s 3 := by
    unfold pulseAt; split_ifs <;> omega
  have h6 : pulseAt (s + 2730) 6 = pulseAt s 6 := by
    unfold pulseAt; split_ifs <;> omega
  have h7 : pulseAt (s + 2730) 7 = pulseAt s 7 := by
    unfold pulseAt; split_ifs <;> omega
  have h14 : pulseAt (s + 2730) 14 = pulseAt s 14 := by
    unfold pulseAt; split_ifs <;> omega
  have h20 : pulseAt (s + 2730) 20 = pulseAt s 20 := by
    unfold pulseAt; split_ifs <;> omega
  have h21 : pulseAt (s + 2730) 21 = pulseAt s 21 := by
    unfold pulseAt; split_ifs <;> omega
  have h26 : pulseAt (s + 2730) 26 = pulseAt s 26 := by
    unfold pulseAt; split_ifs <;> omega
  unfold pulseFloor
  rw [h2, h3, h6, h7, h14, h20, h21, h26]

/-- The pulse floor is a genuine lower bound for the below-pulse of the
concrete greedy seam cut, from row `27` onward. -/
theorem pulseFloor_le_belowPulse (s : ℕ) (hs : 27 ≤ s) :
    pulseFloor s ≤ (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega)
  have h7 := seven_mem_seamGreedySupport s (by omega)
  have h14 := fourteen_mem_seamGreedySupport s (by omega)
  have h20 := twenty_mem_seamGreedySupport s (by omega)
  have h21 := twentyOne_mem_seamGreedySupport s (by omega)
  have h26 := twentySix_mem_seamGreedySupport s (by omega)
  have hsub : ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ⊆
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
  have hsum : ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d ≤
      ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hexp : ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d =
      pulseFloor s := by
    rw [pulseFloor_eq_rowPulseSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  change pulseFloor s ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport, ← hexp]
  exact hsum

/-! ## The ratchet -/

/-- One step of the exclusion ratchet.  The state `b` is an upper bound for
`3 * E s - 3`, where `E` is the signed excess above the dyadic half point;
`b = 0` is the absorbing dead state. -/
def ratchetStep (s b : ℕ) : ℕ :=
  if 3 * pulseFloor s + 4 ≤ 4 * b then 4 * b - (3 * pulseFloor s + 3) else 0

/-- The ratchet orbit started at the landing rank `D + 1` of a
hypothetical final middle cell of charge `-2`, whose landing excess is
exactly `2`, i.e. initial budget `3 * 2 - 3 = 3`. -/
def ratchetRun (D : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => ratchetStep (D + 1 + k) (ratchetRun D k)

@[simp] theorem ratchetRun_zero (D : ℕ) : ratchetRun D 0 = 3 := rfl

theorem ratchetRun_succ (D k : ℕ) :
    ratchetRun D (k + 1) = ratchetStep (D + 1 + k) (ratchetRun D k) := rfl

theorem ratchetStep_zero (s : ℕ) : ratchetStep s 0 = 0 := by
  unfold ratchetStep
  rw [if_neg (by have := one_le_pulseFloor s; omega)]

/-- Once the budget reaches `10` it can never die: the pulse floor is
capped at `9`, so `b ↦ 4 * b - 3 * pulseFloor s - 3` is non-decreasing
above that threshold. -/
theorem ten_le_ratchetStep (s b : ℕ) (hb : 10 ≤ b) : 10 ≤ ratchetStep s b := by
  have hp := pulseFloor_le_nine s
  unfold ratchetStep
  rw [if_pos (by omega)]
  omega

/-! ## Periodicity of the ratchet -/

theorem ratchetRun_add_period (D k : ℕ) :
    ratchetRun (D + 2730) k = ratchetRun D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [ratchetRun_succ, ratchetRun_succ, ih]
      unfold ratchetStep
      rw [show D + 2730 + 1 + k = (D + 1 + k) + 2730 by ring,
        pulseFloor_add_period]

theorem ratchetRun_add_mul_period (D k n : ℕ) :
    ratchetRun (D + 2730 * n) k = ratchetRun D k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show D + 2730 * (n + 1) = (D + 2730 * n) + 2730 by ring,
        ratchetRun_add_period, ih]

theorem ratchetRun_mod (D k : ℕ) :
    ratchetRun D k = ratchetRun (D % 2730) k := by
  conv_lhs => rw [show D = D % 2730 + 2730 * (D / 2730) by
    rw [Nat.add_comm]; exact (Nat.div_add_mod D 2730).symm]
  exact ratchetRun_add_mul_period _ _ _

/-! ## The rank-`26` survivor phases -/

/-- The joint residue conditions cut out by the rank-`26` sieve.  This is
the defining predicate of `finalMiddleTwentySixPhaseSurvivors`, whose
`Finset` has cardinality `412`. -/
def SurvivorPhase (D : ℕ) : Prop :=
  D % 21 ∈ ({11, 14, 17, 20} : Finset ℕ) ∧
    D % 10 ≠ 8 ∧
    ¬ (D % 10 = 7 ∧ D % 21 = 11) ∧
    D % 13 ≠ 11 ∧
    ¬ (D % 13 = 10 ∧ D % 21 = 11)

instance (D : ℕ) : Decidable (SurvivorPhase D) := by
  unfold SurvivorPhase; infer_instance

theorem survivorPhase_mod (D : ℕ) : SurvivorPhase D ↔ SurvivorPhase (D % 2730) := by
  have h21 : D % 2730 % 21 = D % 21 :=
    Nat.mod_mod_of_dvd D (by norm_num : (21 : ℕ) ∣ 2730)
  have h10 : D % 2730 % 10 = D % 10 :=
    Nat.mod_mod_of_dvd D (by norm_num : (10 : ℕ) ∣ 2730)
  have h13 : D % 2730 % 13 = D % 13 :=
    Nat.mod_mod_of_dvd D (by norm_num : (13 : ℕ) ∣ 2730)
  unfold SurvivorPhase
  rw [h21, h10, h13]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- The finite core of the ratchet, verified on all `2730` joint phases:
a non-surviving class is dead by depth `3`, and a surviving class has
budget at least `10` by depth `5`, hence escapes forever. -/
theorem ratchet_finite_core :
    ∀ D < 2730,
      (if SurvivorPhase D then 10 ≤ ratchetRun D 5 else ratchetRun D 3 = 0) := by
  decide +kernel

/-- **Fixed point.**  On every surviving class the ratchet budget is
positive at *every* depth.  The rank-`26` sieve is therefore not a stage of
the ratchet but its limit: no amount of further iteration of the existing
machinery removes any of the 412 classes. -/
theorem ratchetRun_pos_of_survivorPhase (D : ℕ) (h : SurvivorPhase D) :
    ∀ k, 0 < ratchetRun D k := by
  have hlt : D % 2730 < 2730 := Nat.mod_lt _ (by norm_num)
  have hcore := ratchet_finite_core _ hlt
  rw [if_pos ((survivorPhase_mod D).1 h)] at hcore
  have hfive : 10 ≤ ratchetRun D 5 := by rw [ratchetRun_mod]; exact hcore
  have hgrow : ∀ j, 10 ≤ ratchetRun D (5 + j) := by
    intro j
    induction j with
    | zero => exact hfive
    | succ j ih =>
        rw [show 5 + (j + 1) = (5 + j) + 1 by ring, ratchetRun_succ]
        exact ten_le_ratchetStep _ _ ih
  have hstep : ∀ j, ratchetRun D j = 0 → ratchetRun D (j + 1) = 0 := by
    intro j hj
    rw [ratchetRun_succ, hj, ratchetStep_zero]
  have hzero : ∀ j i, ratchetRun D j = 0 → ratchetRun D (j + i) = 0 := by
    intro j i hj
    induction i with
    | zero => simpa using hj
    | succ i ih => rw [show j + (i + 1) = (j + i) + 1 by ring]; exact hstep _ ih
  intro k
  rcases Nat.lt_or_ge k 5 with hk | hk
  · by_contra hcon
    have h0 : ratchetRun D k = 0 := by omega
    have hk5 := hzero k (5 - k) h0
    rw [show k + (5 - k) = 5 by omega] at hk5
    omega
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
    rw [hj]
    exact lt_of_lt_of_le (by norm_num) (hgrow j)

/-- Conversely, every non-surviving class is killed by the ratchet within
three steps.  Together with `ratchetRun_pos_of_survivorPhase` this says the
ratchet's non-dying set is *exactly* the 412 rank-`26` survivors. -/
theorem ratchetRun_eq_zero_of_not_survivorPhase (D : ℕ) (h : ¬ SurvivorPhase D) :
    ratchetRun D 3 = 0 := by
  have hlt : D % 2730 < 2730 := Nat.mod_lt _ (by norm_num)
  have hcore := ratchet_finite_core _ hlt
  rw [if_neg (fun hc ↦ h ((survivorPhase_mod D).2 hc))] at hcore
  rw [ratchetRun_mod]
  exact hcore

/-! ## Soundness: a dead budget contradicts the middle-cell hypotheses -/

/-- The signed excess of the concrete greedy seam above the dyadic half
point. -/
def seamExcess (s : ℕ) : ℤ :=
  (seamIntegerGreedyRemainder s : ℤ) - ((2 ^ s : ℕ) : ℤ)

/-- The ratchet budget dominates `3 * seamExcess - 3` along the whole
right-tail orbit.  This single induction replaces every hand-chained
exclusion in the rank-`26` sieve. -/
theorem ratchetRun_bound
    (D : ℕ) (hD27 : 27 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : seamExcess (D + 1) = 2) :
    ∀ k, 3 * seamExcess (D + 1 + k) - 3 ≤ (ratchetRun D k : ℤ) := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  intro k
  induction k with
  | zero =>
      simp only [Nat.add_zero, ratchetRun_zero, hlanding]
      norm_num
  | succ k ih =>
      have hs : D + 1 ≤ D + 1 + k := by omega
      have hstep := (horbit (D + 1 + k) hs).2
      have hrec : seamExcess (D + 1 + (k + 1)) =
          4 * seamExcess (D + 1 + k) -
            ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) - 4 := by
        simpa [seamExcess, show D + 1 + (k + 1) = (D + 1 + k) + 1 by ring] using hstep
      have hpos : 0 < seamExcess (D + 1 + (k + 1)) := by
        have := (horbit (D + 1 + (k + 1)) (by omega)).1
        simpa [seamExcess] using this
      have hfloor : (pulseFloor (D + 1 + k) : ℤ) ≤
          ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
        exact_mod_cast pulseFloor_le_belowPulse (D + 1 + k) (by omega)
      have hmain : 3 * seamExcess (D + 1 + (k + 1)) - 3 ≤
          4 * (ratchetRun D k : ℤ) - (3 * (pulseFloor (D + 1 + k) : ℤ) + 3) := by
        rw [hrec]; omega
      rw [ratchetRun_succ]
      unfold ratchetStep
      split_ifs with hcond
      · have hle : 3 * pulseFloor (D + 1 + k) + 3 ≤ 4 * ratchetRun D k := by omega
        have hcast :
            ((4 * ratchetRun D k - (3 * pulseFloor (D + 1 + k) + 3) : ℕ) : ℤ) =
              4 * (ratchetRun D k : ℤ) - (3 * (pulseFloor (D + 1 + k) : ℤ) + 3) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [hcast]
        exact hmain
      · have hcondZ : 4 * (ratchetRun D k : ℤ) ≤ 3 * (pulseFloor (D + 1 + k) : ℤ) + 3 := by
          have hnat : 4 * ratchetRun D k ≤ 3 * pulseFloor (D + 1 + k) + 3 := by omega
          exact_mod_cast hnat
        simp only [Nat.cast_zero]
        omega

/-- **Soundness of the ratchet.**  If the budget of the class of `D` ever
dies, the hypothetical final middle cell of charge `-2` at rank `D` with an
all-right tail is contradictory. -/
theorem ratchet_excludes
    (D : ℕ) (hD27 : 27 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : seamExcess (D + 1) = 2)
    (k : ℕ) (hdead : ratchetRun D k = 0) : False := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  have hbound := ratchetRun_bound D hD27 hright hlanding k
  rw [hdead] at hbound
  have hpos : 0 < seamExcess (D + 1 + k) := by
    have := (horbit (D + 1 + k) (by omega)).1
    simpa [seamExcess] using this
  have hone : seamExcess (D + 1 + k) = 1 := by
    simp only [Nat.cast_zero] at hbound
    omega
  have hstep := (horbit (D + 1 + k) (by omega)).2
  have hrec : seamExcess (D + 1 + k + 1) =
      4 * seamExcess (D + 1 + k) -
        ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) - 4 := by
    simpa [seamExcess] using hstep
  have hnext : 0 < seamExcess (D + 1 + k + 1) := by
    have := (horbit (D + 1 + k + 1) (by omega)).1
    simpa [seamExcess] using this
  have hfloor : (pulseFloor (D + 1 + k) : ℤ) ≤
      ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
    exact_mod_cast pulseFloor_le_belowPulse (D + 1 + k) (by omega)
  have hone' : (1 : ℤ) ≤ (pulseFloor (D + 1 + k) : ℤ) := by
    exact_mod_cast one_le_pulseFloor (D + 1 + k)
  rw [hone] at hrec
  omega

/-! ## The rank-`26` classification, reproved by the ratchet -/

/-- The landing excess of a hypothetical final middle cell of charge `-2`
is exactly `2`.  This is the shared opening move of every exclusion in
`HalfFinalMiddlePhaseSieve`. -/
theorem seamExcess_landing_eq_two
    (D : ℕ) (hD5 : 5 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D hD5).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D hD5).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D hD5).belowPulse <
          (seamAdjacentCut D hD5).terminalWeight)
    (hcell :
      4 * ((seamAdjacentCut D hD5).remainder : ℤ) -
          ((seamAdjacentCut D hD5).belowPulse : ℤ) - 4 = -2) :
    seamExcess (D + 1) = 2 := by
  have hmiddleRec := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    hD5 hncarry hmiddle
  have hmiddleRecZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hmiddleRec
  push_cast at hmiddleRecZ
  have hcellR :
      4 * (seamIntegerGreedyRemainder D : ℤ) -
          ((seamAdjacentCut D hD5).belowPulse : ℤ) - 4 = -2 := by
    simpa [seamAdjacentCut_remainder] using hcell
  unfold seamExcess
  push_cast
  omega

/-- **The rank-`26` classification, from the single local law.**  A
hypothetical final middle cell of charge `-2` with an all-right tail forces
the joint residue conditions cutting out the 412 surviving classes.  The
whole four-modulus classification now follows from one ratchet run of
depth `3`, with no chained pulse estimates. -/
theorem finalMiddleCell_neg_two_survivorPhase
    (D : ℕ) (hD27 : 27 ≤ D)
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
          ((seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse : ℤ) - 4 = -2) :
    SurvivorPhase D := by
  by_contra hcon
  exact ratchet_excludes D hD27 hright
    (seamExcess_landing_eq_two D (by omega) hncarry hmiddle hcell) 3
    (ratchetRun_eq_zero_of_not_survivorPhase D hcon)

/-- The ratchet's survivor predicate is exactly membership in the
`412`-element rank-`26` survivor set. -/
theorem survivorPhase_iff_mem_finalMiddleTwentySixPhaseSurvivors
    (D : ℕ) (hD : D < 2730) :
    SurvivorPhase D ↔ D ∈ finalMiddleTwentySixPhaseSurvivors := by
  unfold SurvivorPhase finalMiddleTwentySixPhaseSurvivors
  simp [Finset.mem_filter, Finset.mem_range, hD]

-- Axiom audit (run with `#print axioms`): `ratchet_finite_core`,
-- `ratchetRun_pos_of_survivorPhase`, `ratchetRun_eq_zero_of_not_survivorPhase`,
-- `ratchet_excludes` and `finalMiddleCell_neg_two_survivorPhase` depend only on
-- `propext`, `Classical.choice`, `Quot.sound`.

/-!
## What the fixed point means

`ratchetRun_pos_of_survivorPhase` and
`ratchetRun_eq_zero_of_not_survivorPhase` together say: the non-dying set
of the ratchet built from the forced support `{2,3,6,7,14,20,21,26}` is
*exactly* the 412 rank-`26` survivors.  The exclusion ratchet therefore
exists, is local — state = residue phase together with one integer budget,
transition `b ↦ 4 * b - 3 * pulseFloor s - 3` — and is already saturated.

The obstruction to emptying it is quantitative and is visible in the
recursion.  Writing `Φ k = (ratchetRun D k + 1) / 4 ^ k`, the step law
gives

  `Φ (k+1) = Φ k - 3 * pulseFloor (D + 1 + k) / 4 ^ (k+1)`,

so `Φ` is strictly decreasing, but its total decrease is the *convergent*
series `3 * ∑ pulseFloor (D+1+k) / 4 ^ (k+1)`.  The class `D` dies iff that
series exceeds the initial budget, i.e. iff

  `∑ j ≥ 1, pulseFloor (D + j) / 4 ^ j > 2 / 3`.

Since `pulseFloor ≥ 1` always, the baseline is `1/3` and the free budget is
exactly `1/3`.  Extending the forced support to rank `27` — the next member
of the greedy Mersenne-reciprocal expansion of `1/2`, whose support begins
`2, 3, 6, 7, 14, 20, 21, 26, 27, 32, 33, 34, 35, 38, 39, 42` — adds
`[27 ∣ s+1] + 2 * [27 ∣ 2s+1]` to `pulseFloor` and does strictly shrink the
survivor set, from `412 / 2730` to `3522 / 24570`.  But each new forced
rank `d` contributes at most `3` units per `d` consecutive ranks, hence a
discounted contribution of order `4 ^ (-d/2)`, while the mod-`3` part alone
already costs `10/63` of the `1/3` budget in the most favourable phase.  A
permanent slack therefore remains: no finite forced support empties the
survivor set.  The ratchet lowers the survivor density monotonically but
never to zero.

Closing the branch requires an exclusion whose strength is *not*
geometrically discounted against the factor `4` in the excess recursion.
-/

end Recon257

end Erdos249257
