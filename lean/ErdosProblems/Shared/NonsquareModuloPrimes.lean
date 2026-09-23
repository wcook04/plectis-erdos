import ErdosProblems.Shared.DirichletPoleComparison
import ErdosProblems.Shared.IdealCountingEuler
import ErdosProblems.Shared.QuadraticSplitPrimes
import Mathlib.RingTheory.AdjoinRoot

/-!
# A non-square of a number field stays a non-square modulo infinitely many primes

**Theorem** (`exists_prime_hom_not_isSquare`).  Let `K ⊆ M` be number fields with
`[M : K] = 2`, `M = K(γ)` and `γ ^ 2 = b ∈ 𝓞 K`.  Then for every `N` there are a prime `ℓ > N`
and a ring homomorphism `φ : 𝓞 K → ZMod ℓ` such that `φ b` is zero or a non-square.

This is the qualitative instance of the Chebotarev density theorem needed for the
square-specialisation lemma of Erdős #243, proved here from the simple pole of the Dedekind
zeta function (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) alone, by the classical
comparison of Dirichlet series at `s = 1`.  Suppose instead that `φ b` is a nonzero square for every
`φ` into every `ZMod ℓ` with `ℓ > N`.  Call a prime `𝔭` of `𝓞 K` good if its norm is a prime
`ℓ > max N 2`.  Then

* every good `𝔭` is the kernel of some `φ : 𝓞 K → ZMod ℓ`, `φ b = t ^ 2` with `t ≠ 0`, and the
  two extensions of `φ` to `𝓞 M` (`γ ↦ ± t`) have distinct kernels of norm `ℓ` above `𝔭`
  (`QuadraticSplit.exists_split_primes_of_forall_isSquare`);
* so the ideals of `𝓞 K` supported on good primes, counted in pairs, inject into the ideals
  of `𝓞 M` with the same norm (`IdealCounting.sum_countSupp_mul_le`), while every ideal of
  `𝓞 K` factors into a good and a bad part (`IdealCounting.card_le_sum_countSupp`), and the
  bad part has a convergent Dirichlet series at `s = 1` (`IdealCounting.sum_countSupp_div_le`);
* hence `ζ_K(s) ^ 2 ≤ B ^ 2 ζ_M(s)` for real `s > 1` near `1`, which is incompatible with both
  zeta functions having a simple pole at `s = 1` (`DirichletPole.false_of_pole_comparison`).
-/

noncomputable section

namespace ErdosProblems.Shared.NonsquareModuloPrimes

open NumberField Ideal Filter Topology

/-- **A non-square is a non-square modulo infinitely many primes.**  If `M = K(γ)` is a
quadratic extension of number fields with `γ ^ 2 = b ∈ 𝓞 K`, then for every `N` some prime
`ℓ > N` carries a ring homomorphism `φ : 𝓞 K → ZMod ℓ` with `φ b` zero or a non-square. -/
theorem exists_prime_hom_not_isSquare {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (hfin : Module.finrank K M = 2) (b : 𝓞 K) (γ : M)
    (hγ : γ ^ 2 = algebraMap K M (b : K)) (hγK : γ ∉ Set.range (algebraMap K M)) (N : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ N < ℓ ∧ ∃ φ : 𝓞 K →+* ZMod ℓ, ¬ (φ b ≠ 0 ∧ IsSquare (φ b)) := by
  classical
  by_contra hcon'
  have hcon : ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ φ : 𝓞 K →+* ZMod ℓ, φ b ≠ 0 ∧ IsSquare (φ b) := by
    intro ℓ hℓ hlt φ
    by_contra h
    exact hcon' ⟨ℓ, hℓ, hlt, φ, h⟩
  have hγint : IsIntegral ℤ γ := by
    have hb : IsIntegral ℤ (algebraMap K M (b : K)) :=
      (RingOfIntegers.isIntegral_coe b).map (algebraMap K M).toIntAlgHom
    have h2 : IsIntegral ℤ (γ ^ 2) := by rw [hγ]; exact hb
    exact IsIntegral.of_pow two_pos h2
  let γ' : 𝓞 M := ⟨γ, hγint⟩
  set N₀ := max N 2 with hN₀
  have H : ∀ ℓ : ℕ, ℓ.Prime → N₀ < ℓ → ∀ φ : 𝓞 K →+* ZMod ℓ, φ b ≠ 0 ∧ IsSquare (φ b) :=
    fun ℓ hℓ hlt φ => hcon ℓ hℓ (lt_of_le_of_lt (le_max_left _ _) hlt) φ
  have hsplit := QuadraticSplit.exists_split_primes_of_forall_isSquare hfin b γ' hγ hγK N₀
    (le_max_right _ _) H
  obtain ⟨B, hB⟩ := IdealCounting.sum_countSupp_div_le (K := K) N₀
  have hga : ∀ n, (IdealCounting.countSupp K
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ) ≤
        (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) := fun n => by
    exact_mod_cast IdealCounting.countSupp_le (K := K)
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n
  have h1 : ∀ n, n ≠ 0 → (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) ≤
      DirichletPole.dconv
        (fun n => (IdealCounting.countSupp K
          (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ))
        (fun n => (IdealCounting.countSupp K
          (fun 𝔭 => ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) n : ℝ)) n := by
    intro n hn
    simp only [DirichletPole.dconv]
    exact_mod_cast IdealCounting.card_le_sum_countSupp (K := K)
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) hn
  have h2 : ∀ n, n ≠ 0 →
      DirichletPole.dconv
        (fun n => (IdealCounting.countSupp K
          (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ))
        (fun n => (IdealCounting.countSupp K
          (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ)) n ≤
        (Nat.card {Q : Ideal (𝓞 M) // absNorm Q = n} : ℝ) := by
    intro n hn
    simp only [DirichletPole.dconv]
    exact_mod_cast IdealCounting.sum_countSupp_mul_le (K := K) M
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) hsplit hn
  have hA : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (fun n => ((Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) : ℂ)) s)
      (𝓝[>] 1) (𝓝 ((dedekindZeta_residue K : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_natCast]
    exact tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hM : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (fun n => ((Nat.card {Q : Ideal (𝓞 M) // absNorm Q = n} : ℝ) : ℂ)) s)
      (𝓝[>] 1) (𝓝 ((dedekindZeta_residue M : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_natCast]
    exact tendsto_sub_one_mul_dedekindZeta_nhdsGT M
  exact DirichletPole.false_of_pole_comparison
    (a := fun n => (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ))
    (g := fun n => (IdealCounting.countSupp K
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ))
    (b := fun n => (IdealCounting.countSupp K
      (fun 𝔭 => ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) n : ℝ))
    (m := fun n => (Nat.card {Q : Ideal (𝓞 M) // absNorm Q = n} : ℝ))
    (fun n => Nat.cast_nonneg _) (fun n => Nat.cast_nonneg _) (fun n => Nat.cast_nonneg _)
    hga h1 h2 B hB (dedekindZeta_residue_pos K) (dedekindZeta_residue_ne_zero M) hA hM

open Polynomial in
/-- The same statement with `M = K(√b)` realised as `AdjoinRoot (X ^ 2 - b)`, once that
polynomial is known to be irreducible. -/
theorem exists_prime_hom_not_isSquare_of_irreducible {K : Type*} [Field K] [NumberField K]
    (b : 𝓞 K) (hb : ¬ IsSquare (algebraMap (𝓞 K) K b))
    [hirr : Fact (Irreducible (X ^ 2 - C (algebraMap (𝓞 K) K b) : K[X]))] (N : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ N < ℓ ∧ ∃ φ : 𝓞 K →+* ZMod ℓ, ¬ (φ b ≠ 0 ∧ IsSquare (φ b)) := by
  have hne : (X ^ 2 - C (algebraMap (𝓞 K) K b) : K[X]) ≠ 0 := hirr.out.ne_zero
  haveI hfinite := (AdjoinRoot.powerBasis hne).finite
  haveI : NumberField (AdjoinRoot (X ^ 2 - C (algebraMap (𝓞 K) K b))) :=
    NumberField.of_module_finite K _
  have hfin := (AdjoinRoot.powerBasis hne).finrank.trans
    ((AdjoinRoot.powerBasis_dim hne).trans (natDegree_X_pow_sub_C (n := 2)))
  have hγ : AdjoinRoot.root (X ^ 2 - C (algebraMap (𝓞 K) K b)) ^ 2 =
      algebraMap K (AdjoinRoot (X ^ 2 - C (algebraMap (𝓞 K) K b))) (algebraMap (𝓞 K) K b) := by
    have h := AdjoinRoot.eval₂_root (X ^ 2 - C (algebraMap (𝓞 K) K b))
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
    rw [AdjoinRoot.algebraMap_eq]
    exact h
  have hγK : AdjoinRoot.root (X ^ 2 - C (algebraMap (𝓞 K) K b)) ∉
      Set.range (algebraMap K (AdjoinRoot (X ^ 2 - C (algebraMap (𝓞 K) K b)))) := by
    rintro ⟨y, hy⟩
    apply hb
    refine ⟨y, ?_⟩
    apply (algebraMap K (AdjoinRoot (X ^ 2 - C (algebraMap (𝓞 K) K b)))).injective
    rw [map_mul, hy, ← sq, hγ]
  exact exists_prime_hom_not_isSquare hfin b _ hγ hγK N

open Polynomial in
/-- **A non-square of `𝓞 K` is a non-square modulo infinitely many primes.**  If
`b ∈ 𝓞 K` is not a square in `K`, then for every `N` some prime `ℓ > N` carries a ring
homomorphism `φ : 𝓞 K → ZMod ℓ` with `φ b` zero or a non-square. -/
theorem exists_prime_hom_not_isSquare_of_not_isSquare {K : Type*} [Field K] [NumberField K]
    (b : 𝓞 K) (hb : ¬ IsSquare (algebraMap (𝓞 K) K b)) (N : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ N < ℓ ∧ ∃ φ : 𝓞 K →+* ZMod ℓ, ¬ (φ b ≠ 0 ∧ IsSquare (φ b)) := by
  haveI : Fact (Irreducible (X ^ 2 - C (algebraMap (𝓞 K) K b) : K[X])) := ⟨by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_X_pow_sub_C]
      simp
    · intro y hy
      apply hb
      refine ⟨y, ?_⟩
      rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy
      rw [← hy, sq]⟩
  exact exists_prime_hom_not_isSquare_of_irreducible b hb N

end ErdosProblems.Shared.NonsquareModuloPrimes
