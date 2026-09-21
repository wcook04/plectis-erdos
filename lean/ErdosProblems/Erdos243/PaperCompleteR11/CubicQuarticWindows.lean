import ErdosProblems.Erdos243.PaperCompleteR11.CubicModularDensity

/-!
# Four-term cubic words and a quartic obstruction

Authored proof candidates; Lean elaboration and actual axiom checks are UNRUN.
A word (x,y,0,t) in an exact reciprocal orbit forces
  (d*(d+y))^2 = -x^2*y*t.
This retains a compatibility equation lost by using only the three-term word
(y,0,t). No primitivity, unit constant, or infinite prime family is assumed.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- A four-term word in a reciprocal orbit satisfies this quartic equation. -/
theorem four_term_orbit_quartic {R : Type*} [CommRing R]
    (x y t d d₁ d₂ a b : R)
    (h₀ : y + d = a * x) (h₁ : d₁ = b * y) (h₂ : t + d₂ = 0)
    (hd₀ : d₁ = a * d) (hd₁ : d₂ = b * d₁) :
    (d * (d + y)) ^ 2 = -x ^ 2 * y * t := by
  have hxd : x * d₁ = d * (d + y) := by
    linear_combination x * hd₀ - d * h₀
  have hsq : d₁ ^ 2 = -y * t := by
    linear_combination d₁ * h₁ - y * hd₁ + y * h₂
  calc
    (d * (d + y)) ^ 2 = (x * d₁) ^ 2 := by rw [hxd]
    _ = x ^ 2 * d₁ ^ 2 := by ring
    _ = -x ^ 2 * y * t := by rw [hsq]; ring

/-- The compatibility equation is homogeneous of degree four. -/
theorem quartic_equation_remove_scale {F : Type*} [Field F]
    (s x y t d : F) (hs : s ≠ 0)
    (h : (d * (d + s * y)) ^ 2 = -(s * x) ^ 2 * (s * y) * (s * t)) :
    ((d / s) * (d / s + y)) ^ 2 = -x ^ 2 * y * t := by
  apply mul_left_cancel₀ (pow_ne_zero 4 hs)
  calc
    s ^ 4 * ((d / s) * (d / s + y)) ^ 2 = (d * (d + s * y)) ^ 2 := by
      field_simp [hs]
      <;> ring
    _ = -(s * x) ^ 2 * (s * y) * (s * t) := h
    _ = s ^ 4 * (-x ^ 2 * y * t) := by ring

/-- Values at distances two to the left, one to the left and one to the right
of a root of a depressed cubic, after subtracting its root equation. -/
def cubicLeftTwo {R : Type*} [CommRing R] (r : R) : R := -6 * (r - 1) ^ 2

def cubicLeftOne {R : Type*} [CommRing R] (r : R) : R := -3 * r * (r - 1)

def cubicRightOne {R : Type*} [CommRing R] (r : R) : R := 3 * r * (r + 1)

/-- A finite-field certificate that the four-term word cannot occur. -/
def CubicQuarticNonresidue {R : Type*} [CommRing R] (r : R) : Prop :=
  ∀ d : R, (d * (d + cubicLeftOne r)) ^ 2 ≠
    -(cubicLeftTwo r) ^ 2 * cubicLeftOne r * cubicRightOne r

/-- A concrete coefficient ratio is covered when it has an obstructed root. -/
def CubicQuarticWitness (p : ℕ) (ρ : ZMod p) : Prop :=
  ∃ r : ZMod p, r ^ 3 - r + 6 * ρ = 0 ∧ CubicQuarticNonresidue r

/-- Clearing the binomial profile directly into a residue ring. -/
theorem integral_cubic_scaled_mod_eval (p : ℕ) (m c : ℤ) (n : ℕ) :
    (6 : ZMod p) * ((m * risingBinomial n + c : ℤ) : ZMod p) =
      (m : ZMod p) * (((n : ZMod p) + 1) ^ 3 - ((n : ZMod p) + 1)) +
        6 * (c : ZMod p) := by
  have hB := congrArg (fun z : ℤ ↦ (z : ZMod p)) (six_mul_risingBinomial n)
  push_cast at hB ⊢
  linear_combination (m : ZMod p) * hB

/-- A supplied quartic certificate rules out four consecutive agreements.
The recurrence is the exact integer recurrence, not a separately postulated
modular orbit. All residue-ring equations are derived here. -/
theorem integral_cubic_quartic_window_hit
    (a u v : ℕ → ℤ) (m c : ℤ) (T n p : ℕ) [Fact p.Prime]
    (hn : T ≤ n)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ZMod p) (hm : (m : ZMod p) ≠ 0)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hcert : CubicQuarticNonresidue r) (hphase : (n : ZMod p) = r - 3) :
    ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ m * risingBinomial (n + j) + c := by
  classical
  by_contra h
  have hagree : ∀ j : ℕ, j < 4 → u (n + j) = m * risingBinomial (n + j) + c := by
    intro j hj
    by_contra hne
    exact h ⟨j, hj, hne⟩
  let U : ℕ → ZMod p := fun j ↦ 6 * (u j : ZMod p)
  let V : ℕ → ZMod p := fun j ↦ 6 * (v j : ZMod p)
  have hN : ∀ j, T ≤ j → U (j + 1) + V j = (a j : ZMod p) * U j := by
    intro j hj
    have hh := congrArg (fun z : ℤ ↦ (z : ZMod p)) (hnum j hj)
    push_cast at hh
    dsimp [U, V]
    linear_combination (6 : ZMod p) * hh
  have hD : ∀ j, T ≤ j → V (j + 1) = (a j : ZMod p) * V j := by
    intro j hj
    have hh := congrArg (fun z : ℤ ↦ (z : ZMod p)) (hden j hj)
    push_cast at hh
    dsimp [V]
    linear_combination (6 : ZMod p) * hh
  have hroot' : (m : ZMod p) * (r ^ 3 - r) + 6 * (c : ZMod p) = 0 := by
    simpa only [Int.cast_mul, Int.cast_ofNat] using hroot
  have heval (j : ℕ) (hj : j < 4) :
      U (n + j) = (m : ZMod p) *
        (((n : ZMod p) + (j : ZMod p) + 1) ^ 3 -
          ((n : ZMod p) + (j : ZMod p) + 1)) + 6 * (c : ZMod p) := by
    dsimp [U]
    rw [hagree j hj, integral_cubic_scaled_mod_eval]
    push_cast <;> rfl
  have hU₀ : U n = (m : ZMod p) * cubicLeftTwo r := by
    have hh := heval 0 (by decide)
    simp only [Nat.add_zero, Nat.cast_zero, add_zero] at hh
    rw [hphase] at hh
    dsimp [cubicLeftTwo]
    linear_combination hh + hroot'
  have hU₁ : U (n + 1) = (m : ZMod p) * cubicLeftOne r := by
    have hh := heval 1 (by decide)
    rw [hphase] at hh
    norm_num only [Nat.cast_one] at hh
    dsimp [cubicLeftOne]
    linear_combination hh + hroot'
  have hU₂ : U (n + 2) = 0 := by
    have hh := heval 2 (by decide)
    rw [hphase] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linear_combination hh + hroot'
  have hU₃ : U (n + 3) = (m : ZMod p) * cubicRightOne r := by
    have hh := heval 3 (by decide)
    rw [hphase] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp [cubicRightOne]
    linear_combination hh + hroot'
  have h₀ := hN n hn
  have h₁ : V (n + 1) = (a (n + 1) : ZMod p) * U (n + 1) := by
    have hh := hN (n + 1) (by omega)
    simpa only [show n + 1 + 1 = n + 2 by omega, hU₂, zero_add] using hh
  have h₂ : U (n + 3) + V (n + 2) = 0 := by
    have hh := hN (n + 2) (by omega)
    simpa only [show n + 2 + 1 = n + 3 by omega, hU₂, mul_zero] using hh
  have hd₀ := hD n hn
  have hd₁ : V (n + 2) = (a (n + 1) : ZMod p) * V (n + 1) := by
    simpa only [show n + 1 + 1 = n + 2 by omega] using hD (n + 1) (by omega)
  have hq := four_term_orbit_quartic (U n) (U (n + 1)) (U (n + 3))
    (V n) (V (n + 1)) (V (n + 2)) (a n : ZMod p) (a (n + 1) : ZMod p)
    h₀ h₁ h₂ hd₀ hd₁
  rw [hU₀, hU₁, hU₃] at hq
  exact hcert (V n / (m : ZMod p))
    (quartic_equation_remove_scale (m : ZMod p) (cubicLeftTwo r)
      (cubicLeftOne r) (cubicRightOne r) (V n) hm hq)

/-- One certified four-term word in each period gives density at least 1/p.
The four-windows are disjoint because p is at least four. -/
theorem integral_cubic_quartic_prime_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 4 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ZMod p) (hm : (m : ZMod p) ≠ 0)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hcert : CubicQuarticNonresidue r) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / (p : ℝ)) := by
  letI : NeZero p := ⟨by omega⟩
  let start := (r - 3).val + p * T
  apply disjoint_periodic_lowerDensity _ start p 4 (by omega) hp
  intro k
  have hT : T ≤ start + p * k := by
    have hmul := Nat.mul_le_mul_right T (show 1 ≤ p by omega)
    dsimp [start]
    omega
  have hphase : ((start + p * k : ℕ) : ZMod p) = r - 3 := by
    simp [start, ZMod.natCast_zmod_val]
  exact integral_cubic_quartic_window_hit a u v m c T (start + p * k) p
    hT hnum hden r hm hroot hcert hphase

/-- Ratio-form certificates are converted to the actual integer coefficients. -/
theorem integral_cubic_quartic_ratio_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 4 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod p) ≠ 0)
    (hw : CubicQuarticWitness p ((c : ZMod p) / (m : ZMod p))) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / (p : ℝ)) := by
  obtain ⟨r, hr, hc⟩ := hw
  apply integral_cubic_quartic_prime_density a u v m c T p hp hnum hden r hm _ hc
  push_cast
  field_simp [hm] at hr
  linear_combination hr

/-- A real small-prime witness, rather than an existential prime oracle,
settles the requested threshold on its coefficient class. -/
theorem integral_cubic_quartic_small_prime_uniform
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime]
    (hp : 4 ≤ p) (hp28 : p ≤ 28)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod p) ≠ 0)
    (hw : CubicQuarticWitness p ((c : ZMod p) / (m : ZMod p))) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 28) := by
  apply (integral_cubic_quartic_ratio_density a u v m c T p hp hnum hden hm hw).mono_bound
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hp28R : (p : ℝ) ≤ 28 := by exact_mod_cast hp28
  exact (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 28) hpR).mpr (by nlinarith)

end ErdosProblems.Erdos243.PaperCompleteR11
