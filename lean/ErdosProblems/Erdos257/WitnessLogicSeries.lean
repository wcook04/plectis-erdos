import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The analytic series for a witness clause

The scalar series arising in the ordinary block comparison converges exactly
when the intersection product is at least two. The comparison with the actual
prime-weighted arithmetic support is a separate obligation.
-/

noncomputable section
namespace ErdosProblems.Erdos257

/-- The Lambert coefficient series is bounded by a polynomial times a
geometric series. At `n = 0`, total division makes the term zero. -/
theorem summable_nat_div_pow_sub_one (b : ℕ) (hb : 2 ≤ b) :
    Summable (fun n : ℕ => (n : ℝ) / ((b : ℝ) ^ n - 1)) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by linarith
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * (1 / (b : ℝ)) ^ n) := by
    simpa only [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one 1
        (r := (1 / (b : ℝ))) (by
          rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hbpos)]
          exact (div_lt_one hbpos).mpr (by linarith))
  have hpow (n : ℕ) : (2 : ℝ) ≤ (b : ℝ) ^ (n + 1) := by
    calc
      (2 : ℝ) ≤ b := hbR
      _ ≤ (b : ℝ) * (b : ℝ) ^ n :=
        le_mul_of_one_le_right hbpos.le (one_le_pow₀ (by linarith))
      _ = (b : ℝ) ^ (n + 1) := (pow_succ' _ _).symm
  apply Summable.of_nonneg_of_le ?_ ?_ (hgeo.mul_left 2)
  · intro n
    rcases n with _ | n
    · simp
    · exact div_nonneg (Nat.cast_nonneg _) (by linarith [hpow n])
  · intro n
    rcases n with _ | n
    · simp
    · have hx := hpow n
      calc
        ((n + 1 : ℕ) : ℝ) / ((b : ℝ) ^ (n + 1) - 1) ≤
            ((n + 1 : ℕ) : ℝ) / ((b : ℝ) ^ (n + 1) / 2) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (by linarith)
        _ = 2 * (((n + 1 : ℕ) : ℝ) * (1 / (b : ℝ)) ^ (n + 1)) := by
          rw [one_div_pow]
          ring

/-- For a nonempty prime intersection, the clause comparison series is a
subseries of a summable Lambert coefficient series. -/
theorem summable_clause_series (b g : ℕ) (hb : 2 ≤ b) (hg : 2 ≤ g) :
    Summable (fun k : ℕ => ((g ^ k : ℕ) : ℝ) /
      ((b : ℝ) ^ (g ^ k) - 1)) := by
  exact (summable_nat_div_pow_sub_one b hb).comp_injective
    (Nat.pow_right_injective hg)

/-- A missing intersection (`g = 1`) yields a nonzero constant series;
every larger intersection product yields a summable series. -/
theorem summable_clause_series_iff (b g : ℕ) (hb : 2 ≤ b) (hg : 1 ≤ g) :
    Summable (fun k : ℕ => ((g ^ k : ℕ) : ℝ) /
      ((b : ℝ) ^ (g ^ k) - 1)) ↔ 2 ≤ g := by
  constructor
  · intro hs
    by_contra h
    have hg1 : g = 1 := by omega
    subst g
    have hn : (1 / ((b : ℝ) - 1)) ≠ 0 := by
      apply one_div_ne_zero
      have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    exact hn ((summable_const_iff (1 / ((b : ℝ) - 1))).mp (by simpa using hs))
  · exact summable_clause_series b g hb

#print axioms summable_nat_div_pow_sub_one
#print axioms summable_clause_series
#print axioms summable_clause_series_iff

end ErdosProblems.Erdos257
end
