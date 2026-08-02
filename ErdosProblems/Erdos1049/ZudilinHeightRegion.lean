import ErdosProblems.Erdos1049.RationalBaseLambert
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Erdős #1049: elementary height-region certificates

Define the height region by
`log b / log a < 81 / 200`.  Exact integer and logarithmic inequalities place
`31 / 4` and all its positive powers inside this region, place `31 / 4`
outside the Bundschuh--Väänänen region, and place `3 / 2` outside both.

These are elementary parameter inequalities.  No hypergeometric asymptotic or
irrationality theorem is imported as an axiom.  Membership becomes useful only
after a separate analytic theorem is applied, while failure of membership is
method inapplicability and proves neither rationality nor irrationality.
-/

namespace ErdosProblems.Erdos1049

/-- The parameter region cut out by the single inequality
`log b / log a < 81 / 200`; no analytic hypotheses are included. -/
def ZudilinHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < (81 : ℝ) / 200

/-- The exact integer comparison behind the `31 / 4` parameter certificate. -/
theorem thirtyoneFour_power_certificate : 4 ^ 200 < 31 ^ 81 := by
  norm_num

/-- The power certificate gives the required logarithmic height inequality. -/
theorem thirtyoneFour_log_ratio_lt_eightyOne_twoHundredths :
    Real.log 4 / Real.log 31 < (81 : ℝ) / 200 := by
  have hpows : (4 : ℝ) ^ 200 < (31 : ℝ) ^ 81 := by
    exact_mod_cast thirtyoneFour_power_certificate
  have hlogs :
      Real.log ((4 : ℝ) ^ 200) < Real.log ((31 : ℝ) ^ 81) :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hpows
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs
  have hlog31 : 0 < Real.log (31 : ℝ) := Real.log_pos (by norm_num)
  apply (div_lt_iff₀ hlog31).2
  nlinarith

/-- The base `31 / 4` lies in the height region. -/
theorem thirtyoneFour_mem_zudilinHeightRegion :
    ZudilinHeightRegion 31 4 :=
  thirtyoneFour_log_ratio_lt_eightyOne_twoHundredths

/-- The logarithmic height ratio is invariant under a common positive power. -/
theorem zudilinHeightRegion_pow (a b r : ℕ) (hr : 0 < r)
    (h : ZudilinHeightRegion a b) :
    ZudilinHeightRegion (a ^ r) (b ^ r) := by
  unfold ZudilinHeightRegion at h ⊢
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
  rw [mul_div_mul_left _ _ (by exact_mod_cast hr.ne')]
  exact h

/-- Every positive power of `31 / 4` satisfies the same height threshold. -/
theorem thirtyoneFour_power_mem_zudilinHeightRegion (r : ℕ) (hr : 0 < r) :
    ZudilinHeightRegion (31 ^ r) (4 ^ r) :=
  zudilinHeightRegion_pow 31 4 r hr thirtyoneFour_mem_zudilinHeightRegion

/-- The rational number `2 / 5` is a strict lower bound for
`log 4 / log 31`. -/
theorem twoFifths_lt_thirtyoneFour_log_ratio :
    (2 : ℝ) / 5 < Real.log 4 / Real.log 31 := by
  have hpows : (31 : ℝ) ^ 2 < (4 : ℝ) ^ 5 := by norm_num
  have hlogs :
      Real.log ((31 : ℝ) ^ 2) < Real.log ((4 : ℝ) ^ 5) :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hpows
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs
  have hlog31 : 0 < Real.log (31 : ℝ) := Real.log_pos (by norm_num)
  apply (lt_div_iff₀ hlog31).2
  nlinarith

/-- The old Bundschuh--Väänänen margin lies below `2 / 5`. -/
theorem bundschuhVaananenMargin_lt_twoFifths :
    1 / 2 - 1 / Real.pi ^ 2 < (2 : ℝ) / 5 := by
  have hpiPos : 0 < Real.pi := Real.pi_pos
  have hpiSqPos : 0 < Real.pi ^ 2 := sq_pos_of_pos hpiPos
  have hpiSq : Real.pi ^ 2 < (10 : ℝ) := by
    have hpi := Real.pi_lt_d2
    nlinarith
  have hinv : (1 : ℝ) / 10 < 1 / Real.pi ^ 2 :=
    one_div_lt_one_div_of_lt hpiSqPos hpiSq
  nlinarith

/-- The base `31 / 4` lies outside the Bundschuh--Väänänen height region. -/
theorem thirtyoneFour_outside_bundschuhVaananenHeightRegion :
    ¬ BundschuhVaananenHeightRegion 31 4 := by
  intro h
  exact (not_lt_of_ge
    (bundschuhVaananenMargin_lt_twoFifths.trans
      twoFifths_lt_thirtyoneFour_log_ratio).le) h

/-- The exact integer comparison placing `3 / 2` beyond the `81 / 200`
threshold defined above. -/
theorem threeHalves_zudilin_power_obstruction :
    3 ^ 81 < 2 ^ 200 := by
  norm_num

/-- The height ratio of `3 / 2` is strictly larger than `81 / 200`. -/
theorem eightyOneTwoHundredths_lt_threeHalves_log_ratio :
    (81 : ℝ) / 200 < Real.log 2 / Real.log 3 := by
  have hpows : (3 : ℝ) ^ 81 < (2 : ℝ) ^ 200 := by
    exact_mod_cast threeHalves_zudilin_power_obstruction
  have hlogs :
      Real.log ((3 : ℝ) ^ 81) < Real.log ((2 : ℝ) ^ 200) :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hpows
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  apply (lt_div_iff₀ hlog3).2
  nlinarith

/-- The height region defined above does not contain `3 / 2`.  This is a
method boundary, not a rationality or irrationality theorem for the
corresponding Lambert value. -/
theorem threeHalves_outside_zudilinHeightRegion :
    ¬ ZudilinHeightRegion 3 2 := by
  intro h
  exact (not_lt_of_ge
    eightyOneTwoHundredths_lt_threeHalves_log_ratio.le) h

/-- The Bundschuh--Väänänen height region also does not contain `3 / 2`; its
margin is smaller than the threshold already crossed above. -/
theorem threeHalves_outside_bundschuhVaananenHeightRegion :
    ¬ BundschuhVaananenHeightRegion 3 2 := by
  intro h
  have hmargin :
      1 / 2 - 1 / Real.pi ^ 2 < Real.log 2 / Real.log 3 := by
    calc
      1 / 2 - 1 / Real.pi ^ 2 < (2 : ℝ) / 5 :=
        bundschuhVaananenMargin_lt_twoFifths
      _ < (81 : ℝ) / 200 := by norm_num
      _ < Real.log 2 / Real.log 3 :=
        eightyOneTwoHundredths_lt_threeHalves_log_ratio
  exact (not_lt_of_ge hmargin.le) h

end ErdosProblems.Erdos1049
