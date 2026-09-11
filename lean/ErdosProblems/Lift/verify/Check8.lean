import ErdosProblems.Lift.AngleB3

open Erdos249257 AngleB3

#print axioms Erdos249257.AngleB3.seamExcess_pos
#print axioms Erdos249257.AngleB3.seamExcess_succ_eq
#print axioms Erdos249257.AngleB3.belowPulse_add_four_le
#print axioms Erdos249257.AngleB3.four_mul_escapePotential_le
#print axioms Erdos249257.AngleB3.escapePotential_geom
#print axioms Erdos249257.AngleB3.seamExcess_geom_lower
#print axioms Erdos249257.AngleB3.belowPulse_lt_of_escaped
#print axioms Erdos249257.AngleB3.band_of_never_escaping
#print axioms Erdos249257.AngleB3.escape_dichotomy
#print axioms Erdos249257.AngleB3.ratchetOrbit_no_recurrence
#print axioms Erdos249257.AngleB3.ratchetOrbit_injOn
#print axioms Erdos249257.AngleB3.ratchetOrbit_above_universal_barrier
#print axioms Erdos249257.AngleB3.pulseFloor_ratchet_escape_from_ten
#print axioms Erdos249257.AngleB3.pulseFloor_ratchetOrbit_unbounded

-- ADVERSARIAL CHECK 1.  The hypothesis of `ratchetOrbit_above_universal_barrier`
-- is `∀ s, P s + 4 ≤ 2 * s`.  At s = 0 this reads `P 0 + 4 ≤ 0`, which is false
-- for every `P : ℕ → ℕ`.  So NO pulse source satisfies it: the theorem is vacuous.
theorem universal_cap_is_unsatisfiable :
    ¬ ∃ P : ℕ → ℕ, ∀ s : ℕ, P s + 4 ≤ 2 * s := by
  rintro ⟨P, h⟩
  have := h 0
  omega

-- The vacuity is literally exploitable: from the hypothesis one derives False,
-- so the "forward invariance" conclusion carries no information.
theorem barrier_theorem_is_vacuous
    (P : ℕ → ℕ) (hcap : ∀ s, P s + 4 ≤ 2 * s) : False := by
  have := hcap 0
  omega

-- ADVERSARIAL CHECK 2.  The abstract bounded-pulse ratchet DOES have a periodic
-- orbit below the threshold, contradicting the file's prose claim that
-- `b = Q + 1` "is the only candidate cycle".  Take Q = 9, P ≡ 1, b = 2:
-- 4*2 - (3*1 + 3) = 2, a genuine fixed point with P ≤ Q everywhere.
theorem abstract_ratchet_has_a_low_cycle :
    (∀ s : ℕ, (fun _ : ℕ => (1 : ℕ)) s ≤ 9) ∧
      ∀ k : ℕ, ratchetOrbit (fun _ : ℕ => (1 : ℕ)) 0 2 k = 2 := by
  refine ⟨fun s => by norm_num, fun k => ?_⟩
  induction k with
  | zero => rfl
  | succ k ih => rw [ratchetOrbit_succ, ih]; unfold ratchetStep; norm_num

-- ADVERSARIAL CHECK 3.  How far does the escape hypothesis reach?  At the actual
-- landing configuration of the exclusion problem (`seamExcess (D+1) = 2`, the
-- `-2` middle cell), the escape potential is NEGATIVE for every D ≥ 2, so
-- Part 1's barrier does not apply at the landing rank.
theorem landing_is_not_escaped (D : ℕ) (hD : 2 ≤ D)
    (hland : seamExcess (D + 1) = 2) : escapePotential (D + 1) < 0 := by
  unfold escapePotential
  rw [hland]
  have : (2 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  push_cast
  omega
