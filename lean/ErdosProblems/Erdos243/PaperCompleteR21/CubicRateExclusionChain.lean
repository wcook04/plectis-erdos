import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR20.CubicSquareSpecializationAssembly
import ErdosProblems.Erdos243.PaperCompleteR20.CubicModularSquareSpecialisation
import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateCanonicalBridge
import ErdosProblems.Erdos243.PaperCompleteR11.DensityTransport

/-!
# Erdős 243: from the square specialisation to cubic-rate irrationality

Development file: the three paper environments downstream of
`long243:res:squarespec`, proved from that lemma taken as the hypothesis
`SquareSpecialisation`.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20

/-- The statement of `long243:res:squarespec`. -/
def SquareSpecialisation : Prop :=
  ∀ (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀) (f H : Polynomial ℚ),
    Irreducible f → Polynomial.aeval α f = 0 → Polynomial.aeval α H ≠ 0 →
    ∀ (d : ℕ), 0 < d → ∀ G J : Polynomial ℤ,
    G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f →
    J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H →
    (∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
        (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
        (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
          IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) →
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = Polynomial.aeval α H

/-- Evaluating the depressed cubic along any ring homomorphism out of `ℚ`. -/
theorem eval₂_cubicScalePolynomial {R : Type*} [CommRing R] (f : ℚ →+* R) (x : R) (η : ℚ) :
    Polynomial.eval₂ f x (cubicScalePolynomial η) = x ^ 3 - x + f η := by
  show Polynomial.eval₂ f x (Polynomial.X ^ 3 - Polynomial.X + Polynomial.C η) = _
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]

/-! ### `long243:res:transportsquare` -/

/-- The normalisation identity of `long243:res:transportsquare`: with `κ = m / 6`
and `η = 6 c / m`, `Q_{m,c} (n) = κ * f (n + 1)` for `f (T) = T ^ 3 - T + η`. -/
theorem cubic_normalisation_identity (m c : ℚ) (hm : m ≠ 0) (n : ℚ) :
    (m / 6) * ((n + 1) ^ 3 - (n + 1) + 6 * c / m)
      = (m / 6) * (n * (n + 1) * (n + 2)) + c := by
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- Paper statement of `long243:res:transportsquare`: under the standing
zero-lower-density assumption on a primitive positive orbit, `α ^ 2 - 1` is a
square in `ℚ(α) ^ ×` for a root `α` of `f (T) = T ^ 3 - T + 6 c / m`. -/
theorem transport_square (hss : SquareSpecialisation)
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀)
    (hroot : α ^ 3 = α - algebraMap ℚ L₀ (6 * (c : ℚ) / (m : ℚ))) :
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = α ^ 2 - 1 := by
  classical
  obtain ⟨hc, -, -, -, -, hirr⟩ :=
    primitive_zero_density_multiplier_irreducibility a u v m c T hm hv hnum hden hcop hzero
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hcQ : (c : ℚ) ≠ 0 := by
    rcases hc with rfl | rfl <;> norm_num
  set η : ℚ := 6 * (c : ℚ) / (m : ℚ) with hη
  have hη0 : η ≠ 0 := by
    rw [hη]
    exact div_ne_zero (by simpa using hcQ) hmQ
  set f : Polynomial ℚ := cubicScalePolynomial η with hf
  set H : Polynomial ℚ := Polynomial.X ^ 2 - 1 with hH
  have hfα : Polynomial.aeval α f = 0 := by
    rw [hf]
    simp only [cubicScalePolynomial, map_add, map_sub, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    rw [hroot]
    ring
  have hHα : Polynomial.aeval α H = α ^ 2 - 1 := by
    rw [hH]
    simp
  have hηL : algebraMap ℚ L₀ η ≠ 0 := by
    simpa using (map_ne_zero_iff _ (algebraMap ℚ L₀).injective).mpr hη0
  have hHα0 : Polynomial.aeval α H ≠ 0 := by
    rw [hHα]
    intro h
    apply hηL
    have key : α * (α ^ 2 - 1) = -algebraMap ℚ L₀ η := by linear_combination hroot
    rw [h, mul_zero] at key
    exact neg_eq_zero.mp key.symm
  -- integral models
  set G : Polynomial ℤ :=
    Polynomial.C (m : ℤ) * Polynomial.X ^ 3 - Polynomial.C (m : ℤ) * Polynomial.X
      + Polynomial.C (6 * c) with hG
  set J : Polynomial ℤ := Polynomial.C ((m : ℤ) ^ 2) * (Polynomial.X ^ 2 - 1) with hJ
  have hGmap : G.map (Int.castRingHom ℚ) = Polynomial.C (m : ℚ) * f := by
    have hmapG : G.map (Int.castRingHom ℚ)
        = Polynomial.C (m : ℚ) * Polynomial.X ^ 3 - Polynomial.C (m : ℚ) * Polynomial.X
          + Polynomial.C (6 * (c : ℚ)) := by
      have h1 : (Int.castRingHom ℚ) ((m : ℤ)) = (m : ℚ) := by simp
      have h2 : (Int.castRingHom ℚ) (6 * c) = 6 * (c : ℚ) := by simp
      rw [hG]
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
      rw [h1, h2]
    have hexp : Polynomial.C (m : ℚ) *
        (Polynomial.X ^ 3 - Polynomial.X + Polynomial.C η)
        = Polynomial.C (m : ℚ) * Polynomial.X ^ 3 - Polynomial.C (m : ℚ) * Polynomial.X
          + Polynomial.C ((m : ℚ) * η) := by
      rw [Polynomial.C_mul]
      ring
    have hcoef : (6 : ℚ) * (c : ℚ) = (m : ℚ) * η := by
      rw [hη]
      field_simp
    rw [hmapG, hf]
    simp only [cubicScalePolynomial]
    rw [hexp, hcoef]
  have hJmap : J.map (Int.castRingHom ℚ) = Polynomial.C ((m : ℚ) ^ 2) * H := by
    have h3 : (Int.castRingHom ℚ) ((m : ℤ) ^ 2) = (m : ℚ) ^ 2 := by simp
    rw [hJ, hH]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    rw [h3]
  -- the modular hypothesis
  have hmod : ∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
      (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
      (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
        IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r) := by
    refine ⟨max m 7, ?_⟩
    intro ℓ hℓ hℓN r hr
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓm : m < ℓ := lt_of_le_of_lt (le_max_left m 7) hℓN
    have hℓ7 : 7 < ℓ := lt_of_le_of_lt (le_max_right m 7) hℓN
    have hGval : (G.map (Int.castRingHom (ZMod ℓ))).eval r
        = (m : ZMod ℓ) * r ^ 3 - (m : ZMod ℓ) * r + ((6 * c : ℤ) : ZMod ℓ) := by
      rw [hG]
      simp
    have hJval : (J.map (Int.castRingHom (ZMod ℓ))).eval r
        = (m : ZMod ℓ) ^ 2 * (r ^ 2 - 1) := by
      rw [hJ]
      simp
    rw [hGval] at hr
    have hsix : ((6 : ℕ) : ZMod ℓ) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod ℓ) ℓ 6]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have h6c : ((6 * c : ℤ) : ZMod ℓ) ≠ 0 := by
      rcases hc with rfl | rfl
      · intro h
        apply hsix
        push_cast at h ⊢
        linear_combination h
      · intro h
        apply hsix
        push_cast at h ⊢
        linear_combination -h
    have hmz : (m : ZMod ℓ) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod ℓ) ℓ m]
      intro hdvd
      have := Nat.le_of_dvd hm hdvd
      omega
    have h3z : (3 : ZMod ℓ) ≠ 0 := by
      have h : ((3 : ℕ) : ZMod ℓ) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff (ZMod ℓ) ℓ 3]
        intro hdvd
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      simpa using h
    have hr0 : r ≠ 0 := by
      intro h
      apply h6c
      rw [h] at hr
      linear_combination hr
    have hrsq : r ^ 2 - 1 ≠ 0 := by
      intro h
      apply h6c
      have hcube : (m : ZMod ℓ) * r ^ 3 - (m : ZMod ℓ) * r = 0 := by
        linear_combination (m : ZMod ℓ) * r * h
      linear_combination hr - hcube
    have hfactor : 3 * (m : ZMod ℓ) * r ≠ 0 :=
      mul_ne_zero (mul_ne_zero h3z hmz) hr0
    have hroot' : (m : ZMod ℓ) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod ℓ) = 0 := by
      linear_combination hr
    have hsq := natural_zero_lower_density_forces_modular_root_square
      a u v m c T ℓ (by omega) hnum hden hzero r hroot' hfactor
    refine ⟨?_, ?_⟩
    · rw [hJval]
      exact mul_ne_zero (pow_ne_zero 2 hmz) hrsq
    · rw [hJval]
      obtain ⟨t, ht⟩ := hsq
      exact ⟨(m : ZMod ℓ) * t, by rw [ht]; ring⟩
  obtain ⟨β, hβmem, hβ0, hβsq⟩ :=
    hss L₀ α f H hirr hfα hHα0 m hm G J hGmap hJmap hmod
  exact ⟨β, hβmem, hβ0, by rw [hβsq, hHα]⟩

/-! ### `long243:res:cubicexclusion` -/

set_option maxHeartbeats 1000000 in
/-- Paper statement of `long243:res:cubicexclusion`.

The first clause is the paper's `liminf_{X → ∞} #{n ≤ X : C n ≠ P n} / X > 0`,
written without division: some `dens > 0` is an eventual lower bound for the
proportion, `exceptionCount E (X + 1)` being `#{n ≤ X : n ∈ E}`.  The second
clause is the paper's "in particular". -/
theorem cubic_exclusion (hss : SquareSpecialisation)
    (a C D : ℕ → ℤ) (ha : ∀ n, 0 < a n) (hC : ∀ n, 0 < C n) (hD : ∀ n, 0 < D n)
    (hCrec : ∀ n, C (n + 1) = a n * C n - D n)
    (hDrec : ∀ n, D (n + 1) = a n * D n)
    (A B : ℚ) (hA : 0 < A) :
    (∃ dens : ℝ, 0 < dens ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        dens * (X : ℝ) ≤ (exceptionCount
          {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
          (X + 1) : ℝ)) ∧
      ¬ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℚ) = A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B := by
  classical
  set E : Set ℕ :=
    {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B} with hE
  have hcore : ¬ ZeroLowerDensity E := by
    intro hzero
    set aN : ℕ → ℕ := fun n => (a n).toNat with haN
    set CN : ℕ → ℕ := fun n => (C n).toNat with hCN
    set DN : ℕ → ℕ := fun n => (D n).toNat with hDN
    have haNc : ∀ n, ((aN n : ℤ)) = a n := fun n => Int.toNat_of_nonneg (ha n).le
    have hCNc : ∀ n, ((CN n : ℤ)) = C n := fun n => Int.toNat_of_nonneg (hC n).le
    have hDNc : ∀ n, ((DN n : ℤ)) = D n := fun n => Int.toNat_of_nonneg (hD n).le
    have hCNpos : ∀ n, 0 < CN n := by
      intro n
      have h1 := hC n
      have h2 := hCNc n
      omega
    have hDNpos : ∀ n, 0 < DN n := by
      intro n
      have h1 := hD n
      have h2 := hDNc n
      omega
    have hCNrec : ∀ n, CN (n + 1) + DN n = aN n * CN n := by
      intro n
      have h : ((CN (n + 1) + DN n : ℕ) : ℤ) = ((aN n * CN n : ℕ) : ℤ) := by
        push_cast
        rw [hCNc, hDNc, haNc, hCNc]
        linarith [hCrec n]
      exact_mod_cast h
    have hDNrec : ∀ n, DN (n + 1) = aN n * DN n := by
      intro n
      have h : ((DN (n + 1) : ℕ) : ℤ) = ((aN n * DN n : ℕ) : ℤ) := by
        push_cast
        rw [hDNc, haNc, hDNc]
        linarith [hDrec n]
      exact_mod_cast h
    have hsets :
        {n : ℕ | (CN n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B} = E := by
      ext n
      simp only [hE, Set.mem_setOf_eq]
      have hcast : ((CN n : ℕ) : ℚ) = ((C n : ℤ) : ℚ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (hCNc n)
      rw [hcast]
    have hzero' : ZeroLowerDensity
        {n : ℕ | (CN n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B} := by
      rw [hsets]; exact hzero
    obtain ⟨N, g, m, c, hg, hm, hc, hmcoeff, hccoeff, hprofile, htail⟩ :=
      rational_cubic_zero_density_primitive_shape aN CN DN A B hA hCNpos hDNpos hCNrec hDNrec
        hzero'
    set u : ℕ → ℕ := fun n => CN n / g with hu
    set v : ℕ → ℕ := fun n => DN n / g with hv
    set mN : ℕ := m.toNat with hmN
    have hmNc : ((mN : ℤ)) = m := Int.toNat_of_nonneg hm.le
    have hmNpos : 0 < mN := by omega
    have hgQ : (g : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
    set F : Set ℕ := {n : ℕ | (u n : ℤ) ≠ (mN : ℤ) * risingBinomial n + c} with hF
    have heq : ∀ n, N ≤ n →
        (n ∈ {n : ℕ | (CN n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
          ↔ n ∈ F) := by
      intro n hn
      obtain ⟨hgcd, -, -, -, -, -, -⟩ := htail n hn
      have hdvd : g ∣ CN n := hgcd ▸ Nat.gcd_dvd_left (CN n) (DN n)
      have hCg : (CN n : ℚ) = (g : ℚ) * ((u n : ℕ) : ℚ) := by
        simp only [hu]
        have h : g * (CN n / g) = CN n := Nat.mul_div_cancel' hdvd
        have h2 : ((g * (CN n / g) : ℕ) : ℚ) = ((CN n : ℕ) : ℚ) := by exact_mod_cast h
        rw [Nat.cast_mul] at h2
        exact h2.symm
      have hprof : A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B
          = (g : ℚ) * (((m * risingBinomial n + c : ℤ)) : ℚ) := by
        rw [← hprofile n]
        field_simp
      simp only [hF, Set.mem_setOf_eq]
      refine not_congr ?_
      rw [hCg, hprof, hmNc]
      constructor
      · intro h
        exact_mod_cast mul_left_cancel₀ hgQ h
      · intro h
        congr 1
        exact_mod_cast h
    have hFzero : ZeroLowerDensity F := by
      apply (zeroLowerDensity_iff_no_positive_lower_bound F).mpr
      intro dd hdd hFd
      have hE' := (lowerDensityAtLeast_iff_of_eventual_iff _ F N dd heq).mpr hFd
      exact (hzero'.not_positive_lower_bound dd hdd) hE'
    have hvpos : ∀ n, N ≤ n → 0 < v n := by
      intro n hn
      obtain ⟨-, -, h, -, -, -, -⟩ := htail n hn
      exact h
    have hnum : ∀ n, N ≤ n → u (n + 1) + v n = aN n * u n := by
      intro n hn
      obtain ⟨-, -, -, -, -, h, -⟩ := htail n hn
      exact h
    have hden : ∀ n, N ≤ n → v (n + 1) = aN n * v n := by
      intro n hn
      obtain ⟨-, -, -, -, -, -, h⟩ := htail n hn
      exact h
    have hcop : ∀ n, N ≤ n → Nat.Coprime (u n) (v n) := by
      intro n hn
      obtain ⟨-, -, -, h, -, -, -⟩ := htail n hn
      exact h
    obtain ⟨-, -, -, -, -, hirr⟩ :=
      primitive_zero_density_multiplier_irreducibility aN u v mN c N hmNpos hvpos hnum hden hcop
        hFzero
    haveI : Fact (Irreducible (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))) := ⟨hirr⟩
    have hrootα :
        (AdjoinRoot.root (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))) ^ 3
          = (AdjoinRoot.root (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ))))
            - algebraMap ℚ (AdjoinRoot (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ))))
                (6 * (c : ℚ) / (mN : ℚ)) := by
      have hof : AdjoinRoot.of (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))
          = algebraMap ℚ (AdjoinRoot (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))) :=
        RingHom.ext_rat _ _
      have h := AdjoinRoot.eval₂_root (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))
      rw [hof, eval₂_cubicScalePolynomial] at h
      linear_combination h
    obtain ⟨β, hβmem, -, hβsq⟩ :=
      transport_square hss aN u v mN c N hmNpos hvpos hnum hden hcop hFzero
        (AdjoinRoot (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ))))
        (AdjoinRoot.root (cubicScalePolynomial (6 * (c : ℚ) / (mN : ℚ)))) hrootα
    exact primitive_cubic_zero_density_impossible_of_square_specialisation
      aN u v mN c N hmNpos hvpos hnum hden hcop hFzero _ β hrootα hβmem hβsq
  constructor
  · have hcore' : ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        ε * (X : ℝ) ≤ (exceptionCount E X : ℝ) := by
      by_contra h
      push_neg at h
      apply hcore
      intro ε hε N
      obtain ⟨X, hX1, hX2⟩ := h ε hε N
      exact ⟨X, hX1, hX2⟩
    obtain ⟨ε, hε, N, hN⟩ := hcore'
    refine ⟨ε, hε, N, ?_⟩
    intro X hX
    have h1 : ε * (((X + 1 : ℕ)) : ℝ) ≤ (exceptionCount E (X + 1) : ℝ) :=
      hN (X + 1) (by omega)
    have h2 : ε * (X : ℝ) ≤ ε * (((X + 1 : ℕ)) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      push_cast
      linarith
    linarith
  · rintro ⟨N, hN⟩
    apply hcore
    intro ε hε M
    have hbound : ∀ X : ℕ, exceptionCount E X ≤ N := by
      intro X
      have hsub : exceptionFinset E X ⊆ Finset.range N := by
        intro n hn
        simp only [exceptionFinset, Finset.mem_filter, Finset.mem_range] at hn ⊢
        by_contra hnN
        exact hn.2 (hN n (Nat.le_of_not_lt hnN))
      have h := Finset.card_le_card hsub
      simpa [exceptionCount] using h
    obtain ⟨X0, hX0⟩ := exists_nat_gt ((N : ℝ) / ε)
    refine ⟨max M X0, le_max_left _ _, ?_⟩
    have hle : (X0 : ℝ) ≤ ((max M X0 : ℕ) : ℝ) := by exact_mod_cast le_max_right M X0
    have hlt : (N : ℝ) / ε < ((max M X0 : ℕ) : ℝ) := lt_of_lt_of_le hX0 hle
    have hNlt : (N : ℝ) < ε * ((max M X0 : ℕ) : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hlt hε
      rw [div_mul_cancel₀ _ hε.ne'] at hmul
      linarith
    have hb : (exceptionCount E (max M X0) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hbound (max M X0)
    linarith

/-! ### `res:cubicrate` and `long243:res:cubicrate` -/

set_option maxHeartbeats 1000000 in
/-- Paper statement of the cubic-rate irrationality theorem (short paper
`res:cubicrate`, long paper `long243:res:cubicrate`): a strictly increasing
sequence of positive integers with `a n ^ 2 / a (n+1) = 1 + 3 / n + o (n ^ (-3))`
has irrational reciprocal sum. -/
theorem cubic_rate_irrationality (hss : SquareSpecialisation)
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv := by
  rintro ⟨q, hq⟩
  have hS' : HasSum (fun n : ℕ => 1 / (a n : ℝ)) ((q.num : ℝ) / (q.den : ℝ)) := by
    rw [show ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) from (Rat.cast_def q).symm, hq]
    exact hS
  obtain ⟨Ac, Dc, hAc, N, hN⟩ :=
    rational_reciprocal_sum_cubic_rate_gives_positive_eventual_cubic a ha hpos
      q.num q.den q.pos hS' hrate
  obtain ⟨hCpos, hDpos, hCrec, hDrec, -⟩ :=
    canonical_integer_tail a hpos q.num q.den q.pos hS'
  have hapos : ∀ n : ℕ, 0 < ((a n : ℤ)) := by
    intro n
    exact_mod_cast hpos n
  have hCpos' : ∀ n : ℕ, 0 < ((canonicalNaturalNumerator a q.num q.den n : ℤ)) := by
    intro n
    exact_mod_cast hCpos n
  have hDpos' : ∀ n : ℕ, 0 < ((canonicalDenominator a q.den n : ℤ)) := by
    intro n
    exact_mod_cast hDpos n
  have hCrec' : ∀ n : ℕ,
      ((canonicalNaturalNumerator a q.num q.den (n + 1) : ℤ))
        = ((a n : ℤ)) * ((canonicalNaturalNumerator a q.num q.den n : ℤ))
          - ((canonicalDenominator a q.den n : ℤ)) := by
    intro n
    have h : ((canonicalNaturalNumerator a q.num q.den (n + 1)
        + canonicalDenominator a q.den n : ℕ) : ℤ)
        = ((a n * canonicalNaturalNumerator a q.num q.den n : ℕ) : ℤ) := by
      exact_mod_cast hCrec n
    push_cast at h
    linarith
  have hDrec' : ∀ n : ℕ,
      ((canonicalDenominator a q.den (n + 1) : ℤ))
        = ((a n : ℤ)) * ((canonicalDenominator a q.den n : ℤ)) := by
    intro n
    have h : ((canonicalDenominator a q.den (n + 1) : ℕ) : ℤ)
        = ((a n * canonicalDenominator a q.den n : ℕ) : ℤ) := by
      exact_mod_cast hDrec n
    push_cast at h
    linarith
  refine (cubic_exclusion hss (fun n => (a n : ℤ))
      (fun n => (canonicalNaturalNumerator a q.num q.den n : ℤ))
      (fun n => (canonicalDenominator a q.den n : ℤ))
      hapos hCpos' hDpos' hCrec' hDrec' Ac Dc hAc).2 ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  simp only [risingCubic] at h
  have hQ : (((canonicalNaturalNumerator a q.num q.den n : ℕ) : ℚ) : ℝ)
      = ((Ac * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + Dc : ℚ) : ℝ) := by
    push_cast
    push_cast at h
    linarith
  have hq2 : ((canonicalNaturalNumerator a q.num q.den n : ℕ) : ℚ)
      = Ac * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + Dc := by
    exact_mod_cast hQ
  exact_mod_cast hq2

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.cubic_normalisation_identity
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.transport_square
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.cubic_exclusion
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality

end ErdosProblems.Erdos243.PaperCompleteR21
