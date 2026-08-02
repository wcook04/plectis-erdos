import Erdos249257.BooleanMobiusGlobalRepair

/-!
# Quotient compactness at the prescribed point `1/21`

The denominator-`21` greedy orbit is one coherent way to attack the
prescribed rational point, but coherence is stronger than the closed-set
endpoint needs.  This file gives a softer finite-row route.

At binary depth `M`, split every scaled Mersenne weight into its integral
quotient and fractional part.  If a finite Boolean support has quotient
defect `E`, then its actual Mersenne value differs from `1/21` by at most

`(E + support.card + 1) / 2^M`.

Consequently, at the even depth `2R`, any support contained in `2,…,R`
whose quotient defect is below `2^R` already gives an approximation tending
to `1/21`.  The supports need not be nested and need not agree at any fixed
rank.  Closedness of the achievement set performs the compactness step.
-/

namespace Erdos249257

open Filter Set

/-- Integral target obtained by scaling `1/21` to binary depth `M`. -/
def twentyOneQuotientTarget (M : ℕ) : ℕ :=
  2 ^ M / 21

/-- Fractional part of the same scaled target. -/
def twentyOneTargetFraction (M : ℕ) : ℚ :=
  ((2 ^ M % 21 : ℕ) : ℚ) / 21

/-- Nonnegative quotient defect of an admissible finite row. -/
def twentyOneQuotientDefect (D : Finset ℕ) (M : ℕ) : ℕ :=
  twentyOneQuotientTarget M - localPrefixQuotient D M

/-- Exact quotient/fraction decomposition of the scaled target. -/
theorem scaled_one_div_twenty_one_eq_target_add_fraction (M : ℕ) :
    (2 : ℚ) ^ M * (1 / 21 : ℚ) =
      (twentyOneQuotientTarget M : ℚ) + twentyOneTargetFraction M := by
  have hdecomp := Nat.mod_add_div (2 ^ M) 21
  have hdecompQ :
      ((2 ^ M % 21 : ℕ) : ℚ) +
          21 * ((2 ^ M / 21 : ℕ) : ℚ) =
        (2 : ℚ) ^ M := by
    exact_mod_cast hdecomp
  unfold twentyOneQuotientTarget twentyOneTargetFraction
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  linarith

theorem twentyOneTargetFraction_nonneg (M : ℕ) :
    0 ≤ twentyOneTargetFraction M := by
  unfold twentyOneTargetFraction
  positivity

theorem twentyOneTargetFraction_lt_one (M : ℕ) :
    twentyOneTargetFraction M < 1 := by
  unfold twentyOneTargetFraction
  have hmod : 2 ^ M % 21 < 21 := Nat.mod_lt _ (by omega)
  exact (div_lt_one (by norm_num : (0 : ℚ) < 21)).2 (by exact_mod_cast hmod)

/-- Exact scaled error identity.  The quotient defect, source fractional
mass, and denominator-`21` target fraction are the only three terms. -/
theorem scaled_localMersennePrefixValue_sub_one_div_twenty_one
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hadm : localPrefixQuotient D M ≤ twentyOneQuotientTarget M) :
    (2 : ℚ) ^ M *
        (localMersennePrefixValue D - (1 / 21 : ℚ)) =
      localFractionMass D M -
        (twentyOneQuotientDefect D M : ℚ) -
          twentyOneTargetFraction M := by
  have hscale := scaled_localMersennePrefixValue
    (D := D) (M := M) hD
  have htarget := scaled_one_div_twenty_one_eq_target_add_fraction M
  have hdefect :
      (twentyOneQuotientDefect D M : ℚ) =
        (twentyOneQuotientTarget M : ℚ) -
          (localPrefixQuotient D M : ℚ) := by
    unfold twentyOneQuotientDefect
    rw [Nat.cast_sub hadm]
  rw [mul_sub, hscale, htarget, hdefect]
  ring

/-- A finite admissible quotient row gives an explicit real approximation
to `1/21`.  No coherence or greedy origin is assumed. -/
theorem abs_localMersennePrefixValue_sub_one_div_twenty_one_le
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hadm : localPrefixQuotient D M ≤ twentyOneQuotientTarget M) :
    |((localMersennePrefixValue D : ℚ) : ℝ) - (1 : ℝ) / 21| ≤
      ((twentyOneQuotientDefect D M + D.card + 1 : ℕ) : ℝ) /
        (2 : ℝ) ^ M := by
  have hid := scaled_localMersennePrefixValue_sub_one_div_twenty_one hD hadm
  have hF0 := localFractionMass_nonneg (D := D) (M := M) hD
  have hFcard := localFractionMass_le_card (D := D) (M := M) hD
  have hrho0 := twentyOneTargetFraction_nonneg M
  have hrho1 := twentyOneTargetFraction_lt_one M
  have hpowQ : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
  have herror :
      localMersennePrefixValue D - (1 / 21 : ℚ) =
        (localFractionMass D M -
            (twentyOneQuotientDefect D M : ℚ) -
              twentyOneTargetFraction M) / (2 : ℚ) ^ M := by
    rw [eq_div_iff hpowQ.ne']
    simpa [mul_comm] using hid
  have habsQ :
      |localMersennePrefixValue D - (1 / 21 : ℚ)| ≤
        ((twentyOneQuotientDefect D M + D.card + 1 : ℕ) : ℚ) /
          (2 : ℚ) ^ M := by
    rw [herror, abs_div, abs_of_pos hpowQ]
    apply div_le_div_of_nonneg_right _ hpowQ.le
    rw [abs_le]
    constructor
    · push_cast
      linarith
    · push_cast
      linarith
  have habsR :
      (((|localMersennePrefixValue D - (1 / 21 : ℚ)| : ℚ) : ℝ)) ≤
        ((((twentyOneQuotientDefect D M + D.card + 1 : ℕ) : ℚ) /
          (2 : ℚ) ^ M : ℚ) : ℝ) := by
    exact_mod_cast habsQ
  simpa using habsR

/-- The exact finite-row producer suggested by the quotient computation.
At each even depth `2R`, it asks only for one admissible lower support with
terminal defect inside the pure-binary upper window. -/
def TwentyOneEvenQuotientWindowSupply : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    ∃ D : Finset ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ R) ∧
      localPrefixQuotient D (2 * R) ≤
        twentyOneQuotientTarget (2 * R) ∧
      twentyOneQuotientDefect D (2 * R) < 2 ^ R

/-- The universal error envelope for an even quotient-window row tends to
zero. -/
theorem tendsto_twentyOne_evenQuotientWindow_error :
    Tendsto
      (fun R : ℕ =>
        (((2 ^ R + (2 * R + 1) : ℕ) : ℕ) : ℝ) /
          (2 : ℝ) ^ (2 * R))
      atTop (nhds 0) := by
  have hgeom :
      Tendsto (fun R : ℕ => (1 : ℝ) / (2 : ℝ) ^ R)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hlinear :
      Tendsto
        (fun R : ℕ => ((R : ℝ) / (4 : ℝ) ^ R))
        atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 4)
  have hone :
      Tendsto
        (fun R : ℕ => (1 : ℝ) / (4 : ℝ) ^ R)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4))
  have hsum :
      Tendsto
        (fun R : ℕ =>
          (1 : ℝ) / (2 : ℝ) ^ R +
            (2 * ((R : ℝ) / (4 : ℝ) ^ R) +
              1 / (4 : ℝ) ^ R))
        atTop (nhds 0) := by
    simpa using hgeom.add ((hlinear.const_mul 2).add hone)
  convert hsum using 1
  funext R
  push_cast
  have hfour : (2 : ℝ) ^ (2 * R) = (4 : ℝ) ^ R := by
    calc
      (2 : ℝ) ^ (2 * R) = ((2 : ℝ) ^ 2) ^ R := by rw [pow_mul]
      _ = (4 : ℝ) ^ R := by norm_num
  rw [hfour]
  have htwo : (4 : ℝ) ^ R = (2 : ℝ) ^ R * (2 : ℝ) ^ R := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  rw [htwo]
  field_simp

/-- **Cofinality without coherence.**  A square-root quotient window at
every even depth places `1/21` in the Mersenne achievement set. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_evenQuotientWindow
    (hsupply : TwentyOneEvenQuotientWindowSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  classical
  choose D hD hadm hwindow using fun R =>
    hsupply (R + 2) (by omega)
  let y : ℕ → ℝ := fun R =>
    ((localMersennePrefixValue (D R) : ℚ) : ℝ)
  have hshift : Tendsto (fun R : ℕ => R + 2) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat 2
  have hdist :
      Tendsto (fun R : ℕ => dist (y R) (1 / 21 : ℝ))
        atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => dist_nonneg)
      (Filter.Eventually.of_forall fun R => ?_)
      (tendsto_twentyOne_evenQuotientWindow_error.comp hshift)
    rw [Real.dist_eq]
    calc
      |y R - (1 / 21 : ℝ)| ≤
          ((twentyOneQuotientDefect (D R) (2 * (R + 2)) +
              (D R).card + 1 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * (R + 2)) := by
        exact abs_localMersennePrefixValue_sub_one_div_twenty_one_le
          (fun d hd => (hD R d hd).1) (hadm R)
      _ ≤
          (((2 ^ (R + 2) + (2 * (R + 2) + 1) : ℕ) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * (R + 2)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hcard : (D R).card ≤ R + 1 := by
          have hsubset : D R ⊆ Finset.Icc 2 (R + 2) := by
            intro d hd
            simp only [Finset.mem_Icc]
            exact hD R d hd
          calc
            (D R).card ≤ (Finset.Icc 2 (R + 2)).card :=
              Finset.card_le_card hsubset
            _ = R + 1 := by simp
        have hdefect :
            twentyOneQuotientDefect (D R) (2 * (R + 2)) ≤
              2 ^ (R + 2) := (hwindow R).le
        exact_mod_cast (by omega :
          twentyOneQuotientDefect (D R) (2 * (R + 2)) +
              (D R).card + 1 ≤
            2 ^ (R + 2) + (2 * (R + 2) + 1))
  have hy : Tendsto y atTop (nhds (1 / 21 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hyMem : ∀ R : ℕ, y R ∈ mersenneAchievementSet := by
    intro R
    let A : Set ℕ := ↑(D R)
    have hA0 : 0 ∉ A := by
      intro hzero
      have := (hD R 0 (by simpa [A] using hzero)).1
      omega
    refine ⟨A, hA0, ?_⟩
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [y, localMersennePrefixValue_eq_finiteErdosSum]
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

#print axioms abs_localMersennePrefixValue_sub_one_div_twenty_one_le
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_evenQuotientWindow

end Erdos249257
