import ErdosProblems.Erdos243.PaperCompleteR11.CubicQuarticWindows

/-!
# Explicit small-prime quartic certificates

Authored, UNRUN. Each certificate has an explicit root and a finite `decide`
proof body; no Python result is imported as a proof. The independent exact
arithmetic suite regenerates and exhaustively checks these data. The theorems
cover coefficient congruence classes, not all integer coefficient pairs.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

/-- All listed ratio classes have an explicit obstructed root modulo 5. -/
theorem mod_five_quartic_witness (ρ : ZMod 5)
    (hρ : ρ = 1 ∨ ρ = 4) : CubicQuarticWitness 5 ρ := by
  rcases hρ with rfl | rfl
  · exact ⟨3, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨2, by decide, by unfold CubicQuarticNonresidue; decide⟩

/-- The explicit modulo-5 coefficient classes give lower density 1/5. -/
theorem integral_cubic_mod_five_quartic_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 5) ≠ 0)
    (hρ : (c : ZMod 5) / (m : ZMod 5) = 1 ∨
      (c : ZMod 5) / (m : ZMod 5) = 4) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 5) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact integral_cubic_quartic_ratio_density a u v m c T 5 (by decide)
    hnum hden hm (mod_five_quartic_witness _ hρ)

/-- All listed ratio classes have an explicit obstructed root modulo 7. -/
theorem mod_seven_quartic_witness (ρ : ZMod 7)
    (hρ : ρ = 1 ∨ ρ = 3 ∨ ρ = 4 ∨ ρ = 6) : CubicQuarticWitness 7 ρ := by
  rcases hρ with rfl | rfl | rfl | rfl
  · exact ⟨5, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨3, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨4, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨2, by decide, by unfold CubicQuarticNonresidue; decide⟩

/-- The explicit modulo-7 coefficient classes give lower density 1/7. -/
theorem integral_cubic_mod_seven_quartic_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 7) ≠ 0)
    (hρ : (c : ZMod 7) / (m : ZMod 7) = 1 ∨
      (c : ZMod 7) / (m : ZMod 7) = 3 ∨
      (c : ZMod 7) / (m : ZMod 7) = 4 ∨
      (c : ZMod 7) / (m : ZMod 7) = 6) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 7) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact integral_cubic_quartic_ratio_density a u v m c T 7 (by decide)
    hnum hden hm (mod_seven_quartic_witness _ hρ)

/-- All listed ratio classes have an explicit obstructed root modulo 11. -/
theorem mod_eleven_quartic_witness (ρ : ZMod 11)
    (hρ : ρ = 2 ∨ ρ = 4 ∨ ρ = 7 ∨ ρ = 9) : CubicQuarticWitness 11 ρ := by
  rcases hρ with rfl | rfl | rfl | rfl
  · exact ⟨5, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨8, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨3, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨6, by decide, by unfold CubicQuarticNonresidue; decide⟩

/-- The explicit modulo-11 coefficient classes give lower density 1/11. -/
theorem integral_cubic_mod_eleven_quartic_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 11) ≠ 0)
    (hρ : (c : ZMod 11) / (m : ZMod 11) = 2 ∨
      (c : ZMod 11) / (m : ZMod 11) = 4 ∨
      (c : ZMod 11) / (m : ZMod 11) = 7 ∨
      (c : ZMod 11) / (m : ZMod 11) = 9) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 11) := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact integral_cubic_quartic_ratio_density a u v m c T 11 (by decide)
    hnum hden hm (mod_eleven_quartic_witness _ hρ)

/-- All listed ratio classes have an explicit obstructed root modulo 13. -/
theorem mod_thirteen_quartic_witness (ρ : ZMod 13)
    (hρ : ρ = 3 ∨ ρ = 4 ∨ ρ = 6 ∨ ρ = 7 ∨ ρ = 9 ∨ ρ = 10) : CubicQuarticWitness 13 ρ := by
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨4, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨10, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨5, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨8, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨3, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨9, by decide, by unfold CubicQuarticNonresidue; decide⟩

/-- The explicit modulo-13 coefficient classes give lower density 1/13. -/
theorem integral_cubic_mod_thirteen_quartic_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 13) ≠ 0)
    (hρ : (c : ZMod 13) / (m : ZMod 13) = 3 ∨
      (c : ZMod 13) / (m : ZMod 13) = 4 ∨
      (c : ZMod 13) / (m : ZMod 13) = 6 ∨
      (c : ZMod 13) / (m : ZMod 13) = 7 ∨
      (c : ZMod 13) / (m : ZMod 13) = 9 ∨
      (c : ZMod 13) / (m : ZMod 13) = 10) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 13) := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact integral_cubic_quartic_ratio_density a u v m c T 13 (by decide)
    hnum hden hm (mod_thirteen_quartic_witness _ hρ)

/-- All listed ratio classes have an explicit obstructed root modulo 17. -/
theorem mod_seventeen_quartic_witness (ρ : ZMod 17)
    (hρ : ρ = 1 ∨ ρ = 3 ∨ ρ = 5 ∨ ρ = 12 ∨ ρ = 14 ∨ ρ = 16) : CubicQuarticWitness 17 ρ := by
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨8, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨12, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨10, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨7, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨5, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨2, by decide, by unfold CubicQuarticNonresidue; decide⟩

/-- The explicit modulo-17 coefficient classes give lower density 1/17. -/
theorem integral_cubic_mod_seventeen_quartic_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 17) ≠ 0)
    (hρ : (c : ZMod 17) / (m : ZMod 17) = 1 ∨
      (c : ZMod 17) / (m : ZMod 17) = 3 ∨
      (c : ZMod 17) / (m : ZMod 17) = 5 ∨
      (c : ZMod 17) / (m : ZMod 17) = 12 ∨
      (c : ZMod 17) / (m : ZMod 17) = 14 ∨
      (c : ZMod 17) / (m : ZMod 17) = 16) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 17) := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  exact integral_cubic_quartic_ratio_density a u v m c T 17 (by decide)
    hnum hden hm (mod_seventeen_quartic_witness _ hρ)

/-- All listed ratio classes have an explicit obstructed root modulo 19. -/
theorem mod_nineteen_quartic_witness (ρ : ZMod 19)
    (hρ : ρ = 1 ∨ ρ = 4 ∨ ρ = 9 ∨ ρ = 10 ∨ ρ = 15 ∨ ρ = 18) : CubicQuarticWitness 19 ρ := by
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨7, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨16, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨4, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨15, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨3, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨2, by decide, by unfold CubicQuarticNonresidue; decide⟩

/-- The explicit modulo-19 coefficient classes give lower density 1/19. -/
theorem integral_cubic_mod_nineteen_quartic_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 19) ≠ 0)
    (hρ : (c : ZMod 19) / (m : ZMod 19) = 1 ∨
      (c : ZMod 19) / (m : ZMod 19) = 4 ∨
      (c : ZMod 19) / (m : ZMod 19) = 9 ∨
      (c : ZMod 19) / (m : ZMod 19) = 10 ∨
      (c : ZMod 19) / (m : ZMod 19) = 15 ∨
      (c : ZMod 19) / (m : ZMod 19) = 18) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 19) := by
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact integral_cubic_quartic_ratio_density a u v m c T 19 (by decide)
    hnum hden hm (mod_nineteen_quartic_witness _ hρ)

/-- All listed ratio classes have an explicit obstructed root modulo 23. -/
theorem mod_twenty_three_quartic_witness (ρ : ZMod 23)
    (hρ : ρ = 4 ∨ ρ = 5 ∨ ρ = 8 ∨ ρ = 10 ∨ ρ = 13 ∨ ρ = 15 ∨ ρ = 18 ∨ ρ = 19) : CubicQuarticWitness 23 ρ := by
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨13, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨14, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨8, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨11, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨4, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨15, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨9, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨3, by decide, by unfold CubicQuarticNonresidue; decide⟩

/-- The explicit modulo-23 coefficient classes give lower density 1/23. -/
theorem integral_cubic_mod_twenty_three_quartic_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 23) ≠ 0)
    (hρ : (c : ZMod 23) / (m : ZMod 23) = 4 ∨
      (c : ZMod 23) / (m : ZMod 23) = 5 ∨
      (c : ZMod 23) / (m : ZMod 23) = 8 ∨
      (c : ZMod 23) / (m : ZMod 23) = 10 ∨
      (c : ZMod 23) / (m : ZMod 23) = 13 ∨
      (c : ZMod 23) / (m : ZMod 23) = 15 ∨
      (c : ZMod 23) / (m : ZMod 23) = 18 ∨
      (c : ZMod 23) / (m : ZMod 23) = 19) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 23) := by
  letI : Fact (Nat.Prime 23) := ⟨by decide⟩
  exact integral_cubic_quartic_ratio_density a u v m c T 23 (by decide)
    hnum hden hm (mod_twenty_three_quartic_witness _ hρ)

/-- The nonunit square-field example previously outside the small-divisor
and modulo-five branches is covered by the four-term word modulo seven.
This is a theorem about every exact integer orbit with this profile, not a
finite simulation of one initial condition. -/
theorem integral_cubic_1920_841_density
    (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    LowerDensityAtLeast {n : ℕ | u n ≠ 1920 * risingBinomial n + 841} (1 / 7) := by
  apply integral_cubic_mod_seven_quartic_density a u v 1920 841 T hnum hden
  · decide
  · exact Or.inr (Or.inr (Or.inl (by decide)))

/-- The reflected constant is covered too; the two signs are not silently
identified by an order-reversing change of the natural index. -/
theorem integral_cubic_1920_neg841_density
    (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    LowerDensityAtLeast {n : ℕ | u n ≠ 1920 * risingBinomial n - 841} (1 / 7) := by
  have hh := integral_cubic_mod_seven_quartic_density a u v 1920 (-841) T hnum hden
    (by decide) (Or.inr (Or.inl (by decide)))
  simpa only [sub_eq_add_neg] using hh

/-- Positive-threshold exclusion for every certified coefficient class. -/
theorem quartic_witness_excluded_below_uniform
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime]
    (hp : 4 ≤ p) (hp28 : p ≤ 28)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 28))
    (hm : (m : ZMod p) ≠ 0) :
    ¬ CubicQuarticWitness p ((c : ZMod p) / (m : ZMod p)) := by
  intro hw
  exact hlow (integral_cubic_quartic_small_prime_uniform a u v m c T p hp hp28
    hnum hden hm hw)

end ErdosProblems.Erdos243.PaperCompleteR11
