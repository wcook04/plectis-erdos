import ErdosProblems.Erdos1049.BezoutPluckerJets
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Erdős #1049: two-selector analytic-nullspace escape

Two modular selector collisions can evade the same analytic remainder
nullspace only if their exact coefficient-pair sums are collinear.  The theorem
below is the source-independent algebraic consumer of the computational
rank-two certificate.
-/

namespace ErdosProblems.Erdos1049

open Filter

/-- Non-collinear coefficient pairs cannot both annihilate the same real
linear-form parameter. -/
theorem twoSelector_one_remainder_ne_zero
    (A₁ B₁ A₂ B₂ F : ℝ)
    (hdet : A₁ * B₂ - A₂ * B₁ ≠ 0) :
    B₁ * F - A₁ ≠ 0 ∨ B₂ * F - A₂ ≠ 0 := by
  by_cases h₁ : B₁ * F - A₁ = 0
  · right
    intro h₂
    have ha₁ : A₁ = B₁ * F := (sub_eq_zero.mp h₁).symm
    have ha₂ : A₂ = B₂ * F := (sub_eq_zero.mp h₂).symm
    apply hdet
    rw [ha₁, ha₂]
    ring
  · exact Or.inl h₁

/-! ## The rational gap behind the analytic-aware recombination

The continued-fraction recombination in `QAperyJointLocalRealLatticeLab.md`
acts by an integral unimodular matrix on two coefficient rows.  The following
lemmas isolate its exact logical reach.  Unimodularity preserves
non-collinearity, but at a rational target every nonzero integral linear form
has a fixed denominator gap.  Consequently, proving that both recombined
forms tend to zero already proves irrationality; coefficient-height control
alone cannot supply that decay.
-/

/-- Exact determinant scaling under an integral two-row recombination. -/
theorem twoSelector_recombined_det
    (A₁ B₁ A₂ B₂ u v w z : ℤ) :
    (u * A₁ + v * A₂) * (w * B₁ + z * B₂) -
        (w * A₁ + z * A₂) * (u * B₁ + v * B₂) =
      (u * z - v * w) * (A₁ * B₂ - A₂ * B₁) := by
  ring

/-- The exterior determinant forces a denominator-height versus remainder
tradeoff.  If both real forms are at most `ε`, their determinant is at most
`ε` times the sum of their denominator-coordinate heights. -/
theorem twoSelector_det_height_decay_tradeoff
    (A₁ B₁ A₂ B₂ F ε : ℝ)
    (h₁ : |B₁ * F - A₁| ≤ ε) (h₂ : |B₂ * F - A₂| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤ ε * (|B₁| + |B₂|) := by
  have hid :
      A₁ * B₂ - A₂ * B₁ =
        B₁ * (B₂ * F - A₂) - B₂ * (B₁ * F - A₁) := by
    ring
  rw [hid]
  calc
    |B₁ * (B₂ * F - A₂) - B₂ * (B₁ * F - A₁)| ≤
        |B₁ * (B₂ * F - A₂)| + |B₂ * (B₁ * F - A₁)| :=
      abs_sub _ _
    _ = |B₁| * |B₂ * F - A₂| + |B₂| * |B₁ * F - A₁| := by
      rw [abs_mul, abs_mul]
    _ ≤ |B₁| * ε + |B₂| * ε := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left h₂ (abs_nonneg B₁))
        (mul_le_mul_of_nonneg_left h₁ (abs_nonneg B₂))
    _ = ε * (|B₁| + |B₂|) := by ring

/-- For a unimodular recombination whose four coefficients have height at
most `H`, simultaneous decay to `ε` forces
`|det| ≤ 2 H ε (|B₁|+|B₂|)`.  Thus the enormous continued-fraction
coefficients in the finite #1049 certificate are constrained by the preserved
determinant, rather than being merely a weak search artefact. -/
theorem twoSelector_unimodular_height_decay_tradeoff
    (A₁ B₁ A₂ B₂ u v w z F H ε : ℝ)
    (hunimod : |u * z - v * w| = 1)
    (hε : 0 ≤ ε)
    (hu : |u| ≤ H) (hv : |v| ≤ H) (hw : |w| ≤ H) (hz : |z| ≤ H)
    (h₁ : |(u * B₁ + v * B₂) * F - (u * A₁ + v * A₂)| ≤ ε)
    (h₂ : |(w * B₁ + z * B₂) * F - (w * A₁ + z * A₂)| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤ 2 * H * ε * (|B₁| + |B₂|) := by
  have hB₁ : |u * B₁ + v * B₂| ≤ H * (|B₁| + |B₂|) := by
    calc
      |u * B₁ + v * B₂| ≤ |u * B₁| + |v * B₂| := abs_add_le _ _
      _ = |u| * |B₁| + |v| * |B₂| := by rw [abs_mul, abs_mul]
      _ ≤ H * |B₁| + H * |B₂| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hu (abs_nonneg B₁))
          (mul_le_mul_of_nonneg_right hv (abs_nonneg B₂))
      _ = H * (|B₁| + |B₂|) := by ring
  have hB₂ : |w * B₁ + z * B₂| ≤ H * (|B₁| + |B₂|) := by
    calc
      |w * B₁ + z * B₂| ≤ |w * B₁| + |z * B₂| := abs_add_le _ _
      _ = |w| * |B₁| + |z| * |B₂| := by rw [abs_mul, abs_mul]
      _ ≤ H * |B₁| + H * |B₂| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hw (abs_nonneg B₁))
          (mul_le_mul_of_nonneg_right hz (abs_nonneg B₂))
      _ = H * (|B₁| + |B₂|) := by ring
  have hdet := twoSelector_det_height_decay_tradeoff
    (u * A₁ + v * A₂) (u * B₁ + v * B₂)
    (w * A₁ + z * A₂) (w * B₁ + z * B₂) F ε h₁ h₂
  have hdetIdentity :
      (u * A₁ + v * A₂) * (w * B₁ + z * B₂) -
          (w * A₁ + z * A₂) * (u * B₁ + v * B₂) =
        (u * z - v * w) * (A₁ * B₂ - A₂ * B₁) := by
    ring
  rw [hdetIdentity, abs_mul, hunimod, one_mul] at hdet
  calc
    |A₁ * B₂ - A₂ * B₁| ≤
        ε * (|u * B₁ + v * B₂| + |w * B₁ + z * B₂|) := hdet
    _ ≤ ε * (H * (|B₁| + |B₂|) + H * (|B₁| + |B₂|)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hB₁ hB₂) hε
    _ = 2 * H * ε * (|B₁| + |B₂|) := by ring

/-- A nonzero integral linear form at the rational target `a / q` has
absolute value at least `1 / q`.  Coprimality is unnecessary for this lower
bound. -/
theorem rational_integerLinearForm_gap
    (a q A B : ℤ) (hq : 0 < q)
    (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hform :
      (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) =
        ((B * a - A * q : ℤ) : ℝ) / (q : ℝ) := by
    rw [show ((B * a - A * q : ℤ) : ℝ) =
      (B : ℝ) * (a : ℝ) - (A : ℝ) * (q : ℝ) by push_cast; ring]
    calc
      (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) =
          ((B : ℝ) * (a : ℝ)) / (q : ℝ) - (A : ℝ) := by ring
      _ = ((B : ℝ) * (a : ℝ)) / (q : ℝ) -
          ((A : ℝ) * (q : ℝ)) / (q : ℝ) := by
        rw [mul_div_cancel_right₀ _ hq0]
      _ = ((B : ℝ) * (a : ℝ) - (A : ℝ) * (q : ℝ)) / (q : ℝ) := by
        rw [sub_div]
  have hnum : B * a - A * q ≠ 0 := by
    intro hzero
    apply hne
    rw [hform, hzero]
    norm_num
  have honeZ : (1 : ℤ) ≤ |B * a - A * q| := Int.one_le_abs hnum
  have honeR : (1 : ℝ) ≤ |((B * a - A * q : ℤ) : ℝ)| := by
    exact_mod_cast honeZ
  rw [hform, abs_div, abs_of_pos hqR]
  exact (div_le_div_iff_of_pos_right hqR).2 honeR

/-- At a rational target, two non-collinear integral coefficient rows cannot
both have sub-`1/q` remainders. -/
theorem rational_twoSelector_remainder_gap
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hdet : A₁ * B₂ - A₂ * B₁ ≠ 0) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  have hdetR :
      (A₁ : ℝ) * (B₂ : ℝ) - (A₂ : ℝ) * (B₁ : ℝ) ≠ 0 := by
    exact_mod_cast hdet
  rcases twoSelector_one_remainder_ne_zero
      (A₁ : ℝ) (B₁ : ℝ) (A₂ : ℝ) (B₂ : ℝ)
      ((a : ℝ) / (q : ℝ)) hdetR with h₁ | h₂
  · exact Or.inl (rational_integerLinearForm_gap a q A₁ B₁ hq h₁)
  · exact Or.inr (rational_integerLinearForm_gap a q A₂ B₂ hq h₂)

/-- Cofinal two-form decay through non-collinear integral rows is impossible
at every rational target.  This is the exact obstruction to treating the
continued-fraction recombination as an independent irrationality engine. -/
theorem rational_twoSelector_not_both_tendsto_zero
    (a q : ℤ) (hq : 0 < q)
    (A₁ B₁ A₂ B₂ : ℕ → ℤ)
    (hdet : ∀ n, A₁ n * B₂ n - A₂ n * B₁ n ≠ 0) :
    ¬(Tendsto
        (fun n ↦ (B₁ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ n : ℝ))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ (B₂ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ n : ℝ))
        atTop (nhds 0)) := by
  rintro ⟨hlim₁, hlim₂⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have heps : (0 : ℝ) < 1 / q := one_div_pos.mpr hqR
  rcases Metric.tendsto_atTop.1 hlim₁ (1 / q) heps with ⟨N₁, hN₁⟩
  rcases Metric.tendsto_atTop.1 hlim₂ (1 / q) heps with ⟨N₂, hN₂⟩
  let N := max N₁ N₂
  have hsmall₁ :
      |(B₁ N : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ N : ℝ)| < 1 / q := by
    simpa [Real.dist_eq] using hN₁ N (le_max_left _ _)
  have hsmall₂ :
      |(B₂ N : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ N : ℝ)| < 1 / q := by
    simpa [Real.dist_eq] using hN₂ N (le_max_right _ _)
  rcases rational_twoSelector_remainder_gap
      a q (A₁ N) (B₁ N) (A₂ N) (B₂ N) hq (hdet N) with hgap | hgap
  · exact (not_lt_of_ge hgap) hsmall₁
  · exact (not_lt_of_ge hgap) hsmall₂

end ErdosProblems.Erdos1049
