import Mathlib.Tactic

/-!
# Erdős #1041: transverse selection at the sextic null branch

At the canonical sextic square contact, the four contact variations form a
regular tetrahedron.  This module formalizes the exact quantitative selector:
the least contact value is nonpositive and its square controls one third of
the complete transverse energy.  It also records the quadratic absorption
inequality used to pass from a negative contact to the whole local chord.
-/

namespace ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector

noncomputable section

def contactPP (p q r : ℝ) : ℝ := p + q + r
def contactPN (p q r : ℝ) : ℝ := p - q - r
def contactNP (p q r : ℝ) : ℝ := -p - q + r
def contactNN (p q r : ℝ) : ℝ := -p + q - r

def contactMin (p q r : ℝ) : ℝ :=
  min (min (contactPP p q r) (contactPN p q r))
    (min (contactNP p q r) (contactNN p q r))

def transverseEnergy (p q r : ℝ) : ℝ := p ^ 2 + q ^ 2 + r ^ 2

theorem contact_sum_zero (p q r : ℝ) :
    contactPP p q r + contactPN p q r +
      contactNP p q r + contactNN p q r = 0 := by
  unfold contactPP contactPN contactNP contactNN
  ring

theorem contact_square_sum (p q r : ℝ) :
    contactPP p q r ^ 2 + contactPN p q r ^ 2 +
        contactNP p q r ^ 2 + contactNN p q r ^ 2 =
      4 * transverseEnergy p q r := by
  unfold contactPP contactPN contactNP contactNN transverseEnergy
  ring

theorem contactMin_le_pp (p q r : ℝ) :
    contactMin p q r ≤ contactPP p q r := by
  unfold contactMin
  exact le_trans (min_le_left _ _) (min_le_left _ _)

theorem contactMin_le_pn (p q r : ℝ) :
    contactMin p q r ≤ contactPN p q r := by
  unfold contactMin
  exact le_trans (min_le_left _ _) (min_le_right _ _)

theorem contactMin_le_np (p q r : ℝ) :
    contactMin p q r ≤ contactNP p q r := by
  unfold contactMin
  exact le_trans (min_le_right _ _) (min_le_left _ _)

theorem contactMin_le_nn (p q r : ℝ) :
    contactMin p q r ≤ contactNN p q r := by
  unfold contactMin
  exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem contactMin_eq_one (p q r : ℝ) :
    contactMin p q r = contactPP p q r ∨
    contactMin p q r = contactPN p q r ∨
    contactMin p q r = contactNP p q r ∨
    contactMin p q r = contactNN p q r := by
  rcases min_choice (contactPP p q r) (contactPN p q r) with hLeft | hLeft <;>
    rcases min_choice (contactNP p q r) (contactNN p q r) with hRight | hRight <;>
    rcases min_choice
      (min (contactPP p q r) (contactPN p q r))
      (min (contactNP p q r) (contactNN p q r)) with hOuter | hOuter
  all_goals
    unfold contactMin
    simp only [hLeft, hRight]
    aesop

theorem contactMin_nonpos (p q r : ℝ) : contactMin p q r ≤ 0 := by
  have hpp := contactMin_le_pp p q r
  have hpn := contactMin_le_pn p q r
  have hnp := contactMin_le_np p q r
  have hnn := contactMin_le_nn p q r
  have hsum := contact_sum_zero p q r
  linarith

/-- The inradius estimate for the regular tetrahedron of contact gradients. -/
theorem transverseEnergy_le_three_contactMin_sq (p q r : ℝ) :
    transverseEnergy p q r ≤ 3 * contactMin p q r ^ 2 := by
  let m := contactMin p q r
  let v₁ := contactPP p q r
  let v₂ := contactPN p q r
  let v₃ := contactNP p q r
  let v₄ := contactNN p q r
  have hm1 : m ≤ v₁ := contactMin_le_pp p q r
  have hm2 : m ≤ v₂ := contactMin_le_pn p q r
  have hm3 : m ≤ v₃ := contactMin_le_np p q r
  have hm4 : m ≤ v₄ := contactMin_le_nn p q r
  have ha1 : 0 ≤ v₁ - m := sub_nonneg.mpr hm1
  have ha2 : 0 ≤ v₂ - m := sub_nonneg.mpr hm2
  have ha3 : 0 ≤ v₃ - m := sub_nonneg.mpr hm3
  have ha4 : 0 ≤ v₄ - m := sub_nonneg.mpr hm4
  have hp12 : 0 ≤ (v₁ - m) * (v₂ - m) := mul_nonneg ha1 ha2
  have hp13 : 0 ≤ (v₁ - m) * (v₃ - m) := mul_nonneg ha1 ha3
  have hp14 : 0 ≤ (v₁ - m) * (v₄ - m) := mul_nonneg ha1 ha4
  have hp23 : 0 ≤ (v₂ - m) * (v₃ - m) := mul_nonneg ha2 ha3
  have hp24 : 0 ≤ (v₂ - m) * (v₄ - m) := mul_nonneg ha2 ha4
  have hp34 : 0 ≤ (v₃ - m) * (v₄ - m) := mul_nonneg ha3 ha4
  have hsum : v₁ + v₂ + v₃ + v₄ = 0 := by
    simpa [v₁, v₂, v₃, v₄] using contact_sum_zero p q r
  have hsquares : v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 + v₄ ^ 2 =
      4 * transverseEnergy p q r := by
    simpa [v₁, v₂, v₃, v₄] using contact_square_sum p q r
  dsimp [m] at hm1 hm2 hm3 hm4 ⊢
  nlinarith

/-- A transverse perturbation cannot hide from all four square contacts. -/
theorem transverse_contact_selector (p q r : ℝ) :
    contactMin p q r ≤ 0 ∧
    transverseEnergy p q r ≤ 3 * contactMin p q r ^ 2 ∧
    (contactMin p q r = contactPP p q r ∨
     contactMin p q r = contactPN p q r ∨
     contactMin p q r = contactNP p q r ∨
     contactMin p q r = contactNN p q r) := by
  exact ⟨contactMin_nonpos p q r,
    transverseEnergy_le_three_contactMin_sq p q r,
    contactMin_eq_one p q r⟩

theorem contactMin_strict_of_transverseEnergy_pos {p q r : ℝ}
    (hE : 0 < transverseEnergy p q r) : contactMin p q r < 0 := by
  have hm := contactMin_nonpos p q r
  have hcontrol := transverseEnergy_le_three_contactMin_sq p q r
  by_contra h
  have hm0 : contactMin p q r = 0 := le_antisymm hm (le_of_not_gt h)
  rw [hm0] at hcontrol
  nlinarith

/-- The exact coordinates of the common first-order null line. -/
theorem transverse_coordinates_eq_zero_iff {a a₁ b₁ θ c : ℝ} (ha : 0 < a) :
    a * a₁ = 0 ∧
        2 * a ^ 2 * θ = 0 ∧
        -a * (b₁ + 2 * a ^ 2 * c) = 0 ↔
      a₁ = 0 ∧ θ = 0 ∧ b₁ = -2 * a ^ 2 * c := by
  constructor
  · rintro ⟨hp, hq, hr⟩
    have ha0 : a ≠ 0 := ne_of_gt ha
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    constructor
    · exact (mul_eq_zero.mp hp).resolve_left ha0
    constructor
    · nlinarith
    · have hsum : b₁ + 2 * a ^ 2 * c = 0 := by
        apply (mul_eq_zero.mp hr).resolve_left
        nlinarith
      linarith
  · rintro ⟨ha1, htheta, hb1⟩
    subst a₁
    subst θ
    constructor
    · ring
    constructor
    · ring
    · rw [hb1]
      ring

/-- Completing the square: a contact margin `45 δ²` absorbs a perturbation
whose variation away from contact is at most `3 δ |x|`, against canonical
quadratic curvature `x²/20`. -/
theorem quadratic_contact_absorption {x δ μ base perturb total : ℝ}
    (hbase : base ≤ -(x ^ 2) / 20)
    (hperturb : perturb ≤ -μ + 3 * δ * |x|)
    (hmargin : 45 * δ ^ 2 ≤ μ)
    (htotal : total = base + perturb) :
    total ≤ 0 := by
  have habs : |x| ^ 2 = x ^ 2 := sq_abs x
  have hsquare : 0 ≤ (|x| - 30 * δ) ^ 2 := sq_nonneg _
  rw [htotal]
  nlinarith

/-- Outside an explicit quadratic tube around the null line, the tetrahedral
selector supplies the `45 δ²` contact margin required by the local chord
absorption lemma. -/
theorem contactMin_le_neg_fortyFive_sq {p q r δ : ℝ}
    (houter : 6075 * δ ^ 4 ≤ transverseEnergy p q r) :
    contactMin p q r ≤ -45 * δ ^ 2 := by
  have hm := contactMin_nonpos p q r
  have hcontrol := transverseEnergy_le_three_contactMin_sq p q r
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  nlinarith [sq_nonneg (contactMin p q r + 45 * δ ^ 2)]

end

end ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector
