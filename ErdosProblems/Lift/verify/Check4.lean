import ErdosProblems.Lift.AngleA4

/-!
Adversarial verification of `ErdosProblems/Lift/AngleA4.lean`.

Part 1: axiom footprint of every theorem in the file.
Part 2: a probe establishing that the hypothesis of `irrational_of_killsPeriod`
is *equivalent* to its conclusion, so the "faithful reduction" reduces nothing.
-/

open ErdosProblems.Lift.AngleA4

#print axioms ErdosProblems.Lift.AngleA4.totientTail_succ
#print axioms ErdosProblems.Lift.AngleA4.tailDiff_succ
#print axioms ErdosProblems.Lift.AngleA4.tailDiff_mem_int_succ
#print axioms ErdosProblems.Lift.AngleA4.tailDiff_mem_int_mono
#print axioms ErdosProblems.Lift.AngleA4.tailDiff_shift_mod_int
#print axioms ErdosProblems.Lift.AngleA4.tailDiff_eq
#print axioms ErdosProblems.Lift.AngleA4.tailDiff_mem_int_iff
#print axioms ErdosProblems.Lift.AngleA4.tailDiff_approx
#print axioms ErdosProblems.Lift.AngleA4.exists_certifiedKill_of_tailDiff_notMem_int
#print axioms ErdosProblems.Lift.AngleA4.exists_certifiedKill_iff
#print axioms ErdosProblems.Lift.AngleA4.exists_certifiedKill_antitone
#print axioms ErdosProblems.Lift.AngleA4.killsPeriod_iff
#print axioms ErdosProblems.Lift.AngleA4.irrational_of_killsPeriod
#print axioms ErdosProblems.Lift.AngleA4.mersenneRatio_mul
#print axioms ErdosProblems.Lift.AngleA4.killsPeriod_lift_iff
#print axioms ErdosProblems.Lift.AngleA4.tailDiff_lift_mod_int
#print axioms ErdosProblems.Lift.AngleA4.killsPeriod_one_div
#print axioms ErdosProblems.Lift.AngleA4.not_killsPeriod_one_div
#print axioms ErdosProblems.Lift.AngleA4.killsPeriod_lift_fails
#print axioms ErdosProblems.Lift.AngleA4.lift_fails_periodLcm_four_to_five
#print axioms ErdosProblems.Lift.AngleA4.periodLcm_dvd_of_le
#print axioms ErdosProblems.Lift.AngleA4.killsPeriod_of_dvd
#print axioms ErdosProblems.Lift.AngleA4.dvd_two_pow_sub_one_iff
#print axioms ErdosProblems.Lift.AngleA4.frontierWitness_dvd
#print axioms ErdosProblems.Lift.AngleA4.periodLcm_66_val
#print axioms ErdosProblems.Lift.AngleA4.not_dvd_67_periodLcm_66
#print axioms ErdosProblems.Lift.AngleA4.frontierWitness_kills_upto_66
#print axioms ErdosProblems.Lift.AngleA4.frontierWitness_fails_at_67
#print axioms ErdosProblems.Lift.AngleA4.exists_lattice_point
#print axioms ErdosProblems.Lift.AngleA4.frontier_multiplier_ge
#print axioms ErdosProblems.Lift.AngleA4.frontier_ball_meets_lattice

/-- PROBE (converse of `irrational_of_killsPeriod`).  Irrationality of `S`
implies the full period-kill supply. -/
theorem probe_killsPeriod_of_irrational (hirr : Irrational totientSeries)
    (h : ℕ) (hh : 0 < h) : killsPeriod totientSeries h := by
  intro N
  rintro ⟨k, hk⟩
  have hlt : (1 : ℤ) < 2 ^ h := by
    calc (1:ℤ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) hh
  have h1 : (0:ℤ) < 2 ^ N := by positivity
  have hcne : (2 ^ N * (2 ^ h - 1) : ℤ) ≠ 0 := by nlinarith
  have hcast : (((2 ^ N * (2 ^ h - 1) : ℤ) : ℝ)) * totientSeries
      = (2:ℝ) ^ N * ((2:ℝ) ^ h - 1) * totientSeries := by push_cast; ring
  exact (Irrational.intCast_mul hirr hcne).ne_int k (by rw [hcast]; exact hk.symm)

/-- PROBE.  Hence the hypothesis of the "faithful reduction" is *exactly* the
conclusion: `irrational_of_killsPeriod` is a change of notation, not a
weakening of the open problem. -/
theorem probe_reduction_is_an_iff :
    (∀ h : ℕ, 0 < h → killsPeriod totientSeries h) ↔ Irrational totientSeries :=
  ⟨irrational_of_killsPeriod, fun hirr h hh => probe_killsPeriod_of_irrational hirr h hh⟩
