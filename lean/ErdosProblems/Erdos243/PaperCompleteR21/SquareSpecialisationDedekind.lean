import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import ErdosProblems.Shared.NonsquareModuloPrimes

/-!
# Erdős 243: the square-specialisation lemma without the Chebotarev density theorem

Paper form of `long243:res:squarespec` of `paper/reasoning-parts/erdos243/core.tex`
(lemma at line 303): `f ∈ ℚ[T]` irreducible with root `α`, `H (α) ≠ 0`, and for all but finitely
many primes `ℓ` every root `r` of `f` modulo `ℓ` has `H (r)` a nonzero square modulo `ℓ`
(stated through integral models `G = d f`, `J = d ^ 2 H`); then `H (α)` is a square in `ℚ(α)`.

The paper derives this from the Chebotarev density theorem.  Here it follows from
`ErdosProblems.Shared.NonsquareModuloPrimes.exists_prime_hom_nonsquare_of_not_isSquare`, whose only analytic
input is the simple pole of the Dedekind zeta function at `s = 1`, already in Mathlib.

The reduction.  Put `K = ℚ[T] / (f)` with `α` the class of `T`, and `c` the leading coefficient
of `G`.  Then `a = c α` is integral, and for a polynomial `P ∈ ℤ[T]` and `e ≥ deg P` the element
`∑_{j ≤ e} P_j c ^ (e - j) a ^ j` of `𝓞 K` equals `c ^ e P (α)`; under any ring homomorphism
`φ : 𝓞 K → ZMod ℓ` it becomes `c ^ e P (r)` with `r = φ (a) / c`.  Taking `P = G` shows that
`r` is a root of `G` modulo `ℓ`, and taking `P = J`, `e = 2 deg J`, gives an element
`b = (c ^ (deg J) d) ^ 2 H (α)` of `𝓞 K` with `φ (b) = (c ^ (deg J)) ^ 2 J (r)`.  If `H (α)` were
not a square in `K`, neither would `b` be, and some prime `ℓ` beyond every bound would make
`φ (b)` a non-square, contradicting the hypothesis at the root `r`.

`squareSpecialisation_holds` is the statement of
`ErdosProblems.Erdos243.PaperCompleteR21.SquareSpecialisation` written out in full, so this file
depends on Mathlib and the `Shared` number-field files only.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open NumberField Polynomial

/-- `∑_{j ≤ e} P_j c ^ (e - j) a ^ j`: the value at `a` of `c ^ e P (T / c)`. -/
def scaledEval {R : Type*} [CommRing R] (P : Polynomial ℤ) (c : ℤ) (e : ℕ) (a : R) : R :=
  ∑ j ∈ Finset.range (e + 1), ((P.coeff j * c ^ (e - j) : ℤ) : R) * a ^ j

theorem map_scaledEval {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (P : Polynomial ℤ) (c : ℤ) (e : ℕ) (a : R) :
    φ (scaledEval P c e a) = scaledEval P c e (φ a) := by
  simp only [scaledEval, map_sum, map_mul, map_pow, map_intCast]

theorem scaledEval_mul {R : Type*} [CommRing R] (P : Polynomial ℤ) (c : ℤ) (e : ℕ)
    (hP : P.natDegree ≤ e) (r : R) :
    scaledEval P c e ((c : R) * r) = (c : R) ^ e * (P.map (Int.castRingHom R)).eval r := by
  rw [scaledEval, Polynomial.eval_eq_sum_range' (n := e + 1)
    (lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_of_le hP)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hje : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpow : (c : R) ^ e = (c : R) ^ (e - j) * (c : R) ^ j := (pow_sub_mul_pow _ hje).symm
  rw [coeff_map, eq_intCast, hpow]
  push_cast
  ring

theorem eval_map_int_eq_eval₂ {K : Type*} [Field K] [CharZero K] (α : K) (P : Polynomial ℤ) :
    (P.map (Int.castRingHom K)).eval α =
      (P.map (Int.castRingHom ℚ)).eval₂ (Rat.castHom K) α := by
  rw [eval_map, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

/-- The reduction of the square-specialisation lemma to
`NonsquareModuloPrimes.exists_prime_hom_nonsquare_of_not_isSquare`, over an arbitrary number field containing
a root `α` of `f` in which `H (α)` is not a square. -/
theorem false_of_modular_squares_allow_zero {K : Type*} [Field K] [NumberField K] (α : K)
    (f H : Polynomial ℚ) (hf0 : f ≠ 0) (hfα : f.eval₂ (Rat.castHom K) α = 0)
    (hnsq : ¬ IsSquare (H.eval₂ (Rat.castHom K) α))
    (d : ℕ) (hd : 0 < d) (G J : Polynomial ℤ)
    (hG : G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f)
    (hJ : J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H)
    (hmod : ∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
        (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
        IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) :
    False := by
  classical
  obtain ⟨Nmod, hNmod⟩ := hmod
  -- the leading coefficient of `G` and the integral element `a = c α`
  have hG0 : G ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hG
    have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    exact hf0 ((mul_eq_zero.mp hG.symm).resolve_left (by simpa using hd0))
  set c : ℤ := G.leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hG0
  have hGeval : (G.map (Int.castRingHom K)).eval α = 0 := by
    rw [eval_map_int_eq_eval₂, hG, eval₂_mul, eval₂_C, hfα, mul_zero]
  have hGα : Polynomial.aeval α G = 0 := by
    rw [aeval_def, algebraMap_int_eq, ← eval_map]
    exact hGeval
  have ha : IsIntegral ℤ (c • α) := isIntegral_leadingCoeff_smul G α hGα
  let a : 𝓞 K := ⟨c • α, ha⟩
  have hacoe : algebraMap (𝓞 K) K a = (c : K) * α := by
    show c • α = (c : K) * α
    rw [zsmul_eq_mul]
  -- the element `b` of `𝓞 K`
  set k := J.natDegree with hk
  obtain ⟨b, hbdef⟩ : ∃ b : 𝓞 K, b = scaledEval J c (2 * k) a := ⟨_, rfl⟩
  have hJeval : (J.map (Int.castRingHom K)).eval α =
      ((d : K) ^ 2) * H.eval₂ (Rat.castHom K) α := by
    rw [eval_map_int_eq_eval₂, hJ, eval₂_mul, eval₂_C]
    simp
  have hbcoe : algebraMap (𝓞 K) K b = ((c : K) ^ k * d) ^ 2 * H.eval₂ (Rat.castHom K) α := by
    rw [hbdef, map_scaledEval, hacoe, scaledEval_mul J c (2 * k) (by omega), hJeval]
    ring
  -- `b` is not a square in `K`
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc0
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hbnsq : ¬ IsSquare (algebraMap (𝓞 K) K b) := by
    rintro ⟨y, hy⟩
    apply hnsq
    refine ⟨y / ((c : K) ^ k * d), ?_⟩
    have hne : (c : K) ^ k * d ≠ 0 := mul_ne_zero (pow_ne_zero _ hcK) hdK
    rw [hbcoe] at hy
    field_simp
    linear_combination hy
  -- a prime `ℓ` beyond every bound at which `b` is not a square
  obtain ⟨ℓ, hℓ, hℓN, φ, hφ⟩ :=
    ErdosProblems.Shared.NonsquareModuloPrimes.exists_prime_hom_nonsquare_of_not_isSquare b
      hbnsq (max Nmod c.natAbs)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- `c` is a unit modulo `ℓ`
  have hcℓ : (c : ZMod ℓ) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have hle : ℓ ≤ c.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hc0) (Int.natCast_dvd.mp h)
    exact absurd (lt_of_le_of_lt (le_max_right _ _) hℓN) (not_lt.mpr hle)
  -- the root `r` of `G` modulo `ℓ`
  set r : ZMod ℓ := φ a * (c : ZMod ℓ)⁻¹ with hr
  have hφa : φ a = (c : ZMod ℓ) * r := by
    rw [hr, mul_left_comm, mul_inv_cancel₀ hcℓ, mul_one]
  have hGr : (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 := by
    have hzero : scaledEval G c G.natDegree a = 0 := by
      apply RingOfIntegers.coe_injective
      rw [map_scaledEval, hacoe, scaledEval_mul G c G.natDegree le_rfl, hGeval, mul_zero,
        map_zero]
    have h := congrArg φ hzero
    rw [map_scaledEval, hφa, scaledEval_mul G c G.natDegree le_rfl, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hcℓ)
  obtain ⟨s, hs⟩ := hNmod ℓ hℓ (lt_of_le_of_lt (le_max_left _ _) hℓN) r hGr
  have hφb : φ b = (c : ZMod ℓ) ^ (2 * k) * (J.map (Int.castRingHom (ZMod ℓ))).eval r := by
    rw [hbdef, map_scaledEval, hφa, scaledEval_mul J c (2 * k) (by omega)]
  apply hφ
  refine ⟨(c : ZMod ℓ) ^ k * s, ?_⟩
  rw [hφb, hs]
  ring

/-- Compatibility form of the square-specialisation contradiction, retaining the older
nonzero-square modular hypothesis. -/
theorem false_of_modular_squares {K : Type*} [Field K] [NumberField K] (α : K)
    (f H : Polynomial ℚ) (hf0 : f ≠ 0) (hfα : f.eval₂ (Rat.castHom K) α = 0)
    (hnsq : ¬ IsSquare (H.eval₂ (Rat.castHom K) α))
    (d : ℕ) (hd : 0 < d) (G J : Polynomial ℤ)
    (hG : G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f)
    (hJ : J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H)
    (hmod : ∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
        (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
        (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
          IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) :
    False := by
  apply false_of_modular_squares_allow_zero α f H hf0 hfα hnsq d hd G J hG hJ
  obtain ⟨N, hN⟩ := hmod
  refine ⟨N, ?_⟩
  intro ℓ hℓ hlt r hGr
  exact (hN ℓ hℓ hlt r hGr).2

/-- **Polynomial form of `long243:res:squarespec`**: under the paper's modular hypothesis, `H`
is a square modulo the irreducible `f`. -/
theorem sq_sub_dvd_of_modular_squares (f H : Polynomial ℚ) (hf : Irreducible f)
    (d : ℕ) (hd : 0 < d) (G J : Polynomial ℤ)
    (hG : G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f)
    (hJ : J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H)
    (hmod : ∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
        (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
        (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
          IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) :
    ∃ B : Polynomial ℚ, f ∣ B ^ 2 - H := by
  classical
  by_contra hno'
  have hno : ∀ B : Polynomial ℚ, ¬ f ∣ B ^ 2 - H := fun B hB => hno' ⟨B, hB⟩
  haveI : Fact (Irreducible f) := ⟨hf⟩
  have hof : AdjoinRoot.of f = Rat.castHom (AdjoinRoot f) := RingHom.ext_rat _ _
  have heval : ∀ P : Polynomial ℚ,
      P.eval₂ (Rat.castHom (AdjoinRoot f)) (AdjoinRoot.root f) = AdjoinRoot.mk f P := by
    intro P
    rw [← hof, ← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
  refine false_of_modular_squares (K := AdjoinRoot f) (AdjoinRoot.root f) f H hf.ne_zero
    ?_ ?_ d hd G J hG hJ hmod
  · rw [heval, AdjoinRoot.mk_self]
  · rintro ⟨y, hy⟩
    obtain ⟨B, rfl⟩ := AdjoinRoot.mk_surjective y
    apply hno B
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, sq, ← hy, heval, sub_self]

/-- **`long243:res:squarespec`, unconditionally.**  The statement of
`ErdosProblems.Erdos243.PaperCompleteR21.SquareSpecialisation`, written out in full. -/
theorem squareSpecialisation_holds :
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
        β ≠ 0 ∧ β ^ 2 = Polynomial.aeval α H := by
  intro L₀ _ _ α f H hf hfα hHα d hd G J hG hJ hmod
  obtain ⟨B, hB⟩ := sq_sub_dvd_of_modular_squares f H hf d hd G J hG hJ hmod
  have hsq : Polynomial.aeval α B ^ 2 = Polynomial.aeval α H := by
    obtain ⟨q, hq⟩ := hB
    have h1 : Polynomial.aeval α (B ^ 2 - H) = Polynomial.aeval α (f * q) := by rw [hq]
    rw [map_sub, map_pow, map_mul, hfα, zero_mul, sub_eq_zero] at h1
    exact h1
  refine ⟨Polynomial.aeval α B, ?_, ?_, hsq⟩
  · have hmem : Polynomial.aeval α B ∈ Algebra.adjoin ℚ ({α} : Set L₀) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
      exact ⟨B, rfl⟩
    have hle : Algebra.adjoin ℚ ({α} : Set L₀)
        ≤ (IntermediateField.adjoin ℚ ({α} : Set L₀)).toSubalgebra :=
      Algebra.adjoin_le fun x hx => IntermediateField.subset_adjoin ℚ _ hx
    exact hle hmem
  · intro h
    apply hHα
    rw [← hsq, h]
    ring

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.false_of_modular_squares_allow_zero
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.false_of_modular_squares
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.sq_sub_dvd_of_modular_squares
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds

end ErdosProblems.Erdos243.PaperCompleteR21
