import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Field.ZMod

/-!
# Degree-one primes that split in a quadratic extension

Let `K ⊆ M` be number fields with `[M : K] = 2` and `M = K(γ)`, `γ ^ 2 = b ∈ 𝓞 K`.  A ring
homomorphism `φ : 𝓞 K → ZMod ℓ` (`ℓ` an odd prime) with `φ b = t ^ 2`, `t ≠ 0`, extends to two
distinct ring homomorphisms `𝓞 M → ZMod ℓ`, sending `γ` to `t` and to `-t`.

The ring of integers of `M` is not described explicitly.  Instead every `x ∈ M` satisfies

`2 b x = b · Tr(x) + Tr(γ x) · γ`        (`Tr = Tr_{M/K}`),

because `x = u + v γ` with `Tr x = 2 u` and `Tr (γ x) = 2 b v`.  For `x ∈ 𝓞 M` both traces lie in
`𝓞 K`, so `x ↦ (φ b · φ (Tr x) + φ (Tr (γ x)) · t) / (2 φ b)` is defined on `𝓞 M`; it is
multiplicative because of the two trace identities `trace_identity_one` and
`trace_identity_two`, which follow from the displayed formula.

The kernels of the two extensions are two distinct primes of `𝓞 M` of norm `ℓ`, both lying over
the kernel of `φ`.  `exists_split_primes_of_forall_isSquare` packages this in the form consumed by
`ErdosProblems.Shared.IdealCounting.sum_countSupp_mul_le`.
-/

noncomputable section

namespace ErdosProblems.Shared.QuadraticSplit

open NumberField Polynomial

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

/-! ### The quadratic extension `M = K(γ)` -/

omit [NumberField K] [NumberField M] in
theorem trace_algebraMap_mul (c : K) (y : M) :
    Algebra.trace K M (algebraMap K M c * y) = c * Algebra.trace K M y := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem exists_eq_add_mul (hfin : Module.finrank K M = 2) (γ : M)
    (hγK : γ ∉ Set.range (algebraMap K M)) (x : M) :
    ∃ u v : K, x = algebraMap K M u + algebraMap K M v * γ := by
  have hli : LinearIndependent K ![(1 : M), γ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      refine ⟨?_, rfl⟩
      rwa [Algebra.smul_def, mul_one, map_eq_zero_iff _ (algebraMap K M).injective] at hst
    · exfalso
      apply hγK
      refine ⟨-(s / t), ?_⟩
      have htM : algebraMap K M t ≠ 0 := (map_ne_zero_iff _ (algebraMap K M).injective).mpr ht
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      apply mul_left_cancel₀ htM
      rw [← map_mul, show t * -(s / t) = -s by field_simp, map_neg]
      linear_combination -hst
  set bs := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hfin]) with hbs
  have h := bs.sum_repr x
  have h0 : bs 0 = 1 := by rw [hbs, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have h1 : bs 1 = γ := by rw [hbs, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  rw [Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
  exact ⟨_, _, h.symm⟩

theorem trace_algebraMap_eq (hfin : Module.finrank K M = 2) (c : K) :
    Algebra.trace K M (algebraMap K M c) = 2 * c := by
  rw [Algebra.trace_algebraMap, hfin, nsmul_eq_mul, Nat.cast_ofNat]

theorem trace_gen_eq_zero (b : K) (γ : M) (hγ : γ ^ 2 = algebraMap K M b)
    (hγK : γ ∉ Set.range (algebraMap K M)) : Algebra.trace K M γ = 0 := by
  have hirr : Irreducible (X ^ 2 - C b : K[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_X_pow_sub_C]
      simp
    · intro c hc
      apply hγK
      rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hc
      have hc' : algebraMap K M c ^ 2 = algebraMap K M b := by rw [← map_pow, hc]
      have h2 : (γ - algebraMap K M c) * (γ + algebraMap K M c) = 0 := by
        linear_combination hγ - hc'
      rcases mul_eq_zero.mp h2 with h | h
      · exact ⟨c, (sub_eq_zero.mp h).symm⟩
      · exact ⟨-c, by rw [map_neg]; linear_combination -h⟩
  have hmin : minpoly K γ = X ^ 2 - C b :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hγ])
      (monic_X_pow_sub_C b two_ne_zero)).symm
  have hnext : (X ^ 2 - C b : K[X]).nextCoeff = 0 := by
    rw [nextCoeff, natDegree_X_pow_sub_C]
    simp
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, hnext, neg_zero, mul_zero]

/-- The basic identity `2 b x = b Tr (x) + Tr (γ x) γ`. -/
theorem key_identity (hfin : Module.finrank K M = 2) (b : K) (γ : M)
    (hγ : γ ^ 2 = algebraMap K M b) (hγK : γ ∉ Set.range (algebraMap K M)) (x : M) :
    algebraMap K M (2 * b) * x =
      algebraMap K M (b * Algebra.trace K M x) +
        algebraMap K M (Algebra.trace K M (γ * x)) * γ := by
  obtain ⟨u, v, rfl⟩ := exists_eq_add_mul hfin γ hγK x
  have hT0 := trace_gen_eq_zero b γ hγ hγK
  have e1 : Algebra.trace K M (algebraMap K M u + algebraMap K M v * γ) = 2 * u := by
    rw [map_add, trace_algebraMap_mul, trace_algebraMap_eq hfin, hT0, mul_zero, add_zero]
  have e2 : Algebra.trace K M (γ * (algebraMap K M u + algebraMap K M v * γ)) = 2 * (v * b) := by
    have hsplit : γ * (algebraMap K M u + algebraMap K M v * γ) =
        algebraMap K M u * γ + algebraMap K M (v * b) := by
      rw [map_mul, ← hγ]
      ring
    rw [hsplit, map_add, trace_algebraMap_mul, hT0, mul_zero, zero_add,
      trace_algebraMap_eq hfin]
  rw [e1, e2]
  simp only [map_mul, map_ofNat]
  ring

theorem trace_identity_one (hfin : Module.finrank K M = 2) (b : K) (γ : M)
    (hγ : γ ^ 2 = algebraMap K M b) (hγK : γ ∉ Set.range (algebraMap K M)) (x y : M) :
    2 * b * Algebra.trace K M (x * y) =
      b * Algebra.trace K M x * Algebra.trace K M y +
        Algebra.trace K M (γ * x) * Algebra.trace K M (γ * y) := by
  have h := key_identity hfin b γ hγ hγK x
  have h' : algebraMap K M (2 * b) * (x * y) =
      algebraMap K M (b * Algebra.trace K M x) * y +
        algebraMap K M (Algebra.trace K M (γ * x)) * (γ * y) := by
    rw [← mul_assoc, h]
    ring
  have h'' := congrArg (Algebra.trace K M) h'
  rw [trace_algebraMap_mul, map_add, trace_algebraMap_mul, trace_algebraMap_mul] at h''
  linear_combination h''

theorem trace_identity_two (hfin : Module.finrank K M = 2) (b : K) (γ : M)
    (hγ : γ ^ 2 = algebraMap K M b) (hγK : γ ∉ Set.range (algebraMap K M)) (hb : b ≠ 0)
    (x y : M) :
    2 * Algebra.trace K M (γ * (x * y)) =
      Algebra.trace K M x * Algebra.trace K M (γ * y) +
        Algebra.trace K M (γ * x) * Algebra.trace K M y := by
  have h := key_identity hfin b γ hγ hγK x
  have h' : algebraMap K M (2 * b) * (γ * (x * y)) =
      algebraMap K M (b * Algebra.trace K M x) * (γ * y) +
        algebraMap K M (Algebra.trace K M (γ * x) * b) * y := by
    rw [map_mul (algebraMap K M) (Algebra.trace K M (γ * x)) b, ← hγ]
    calc algebraMap K M (2 * b) * (γ * (x * y)) = γ * (algebraMap K M (2 * b) * x) * y := by
          ring
      _ = γ * (algebraMap K M (b * Algebra.trace K M x) +
            algebraMap K M (Algebra.trace K M (γ * x)) * γ) * y := by rw [h]
      _ = _ := by ring
  have h'' := congrArg (Algebra.trace K M) h'
  rw [trace_algebraMap_mul, map_add, trace_algebraMap_mul, trace_algebraMap_mul] at h''
  have hmul : b * (2 * Algebra.trace K M (γ * (x * y)) -
      (Algebra.trace K M x * Algebra.trace K M (γ * y) +
        Algebra.trace K M (γ * x) * Algebra.trace K M y)) = 0 := by
    linear_combination h''
  rcases mul_eq_zero.mp hmul with h0 | h0
  · exact absurd h0 hb
  · linear_combination h0

/-! ### The two extensions of `φ` to `𝓞 M` -/

/-- The trace `𝓞 M → 𝓞 K`. -/
def trO (x : 𝓞 M) : 𝓞 K :=
  ⟨Algebra.trace K M (x : M), Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe x)⟩

theorem coe_trO (x : 𝓞 M) :
    algebraMap (𝓞 K) K (trO (K := K) x) = Algebra.trace K M (algebraMap (𝓞 M) M x) := rfl

omit [NumberField K] [NumberField M] in
theorem coe_algebraMap_ringOfIntegers (c : 𝓞 K) :
    algebraMap (𝓞 M) M (algebraMap (𝓞 K) (𝓞 M) c) = algebraMap K M (algebraMap (𝓞 K) K c) :=
  rfl

theorem exists_extension (hfin : Module.finrank K M = 2) (b : 𝓞 K) (γ : 𝓞 M)
    (hγ : (γ : M) ^ 2 = algebraMap K M (b : K)) (hγK : (γ : M) ∉ Set.range (algebraMap K M))
    {ℓ : ℕ} (φ : 𝓞 K →+* ZMod ℓ) (t : ZMod ℓ) (ht : t ^ 2 = φ b)
    (w : ZMod ℓ) (hw1 : 2 * φ b * w = 1) :
    ∃ ψ : 𝓞 M →+* ZMod ℓ, (∀ c : 𝓞 K, ψ (algebraMap (𝓞 K) (𝓞 M) c) = φ c) ∧ ψ γ = t := by
  have hγ' : algebraMap (𝓞 M) M γ ^ 2 = algebraMap K M (algebraMap (𝓞 K) K b) := hγ
  have hγK' : algebraMap (𝓞 M) M γ ∉ Set.range (algebraMap K M) := hγK
  have hb : algebraMap (𝓞 K) K b ≠ 0 := by
    intro h
    apply hγK'
    refine ⟨0, ?_⟩
    rw [map_zero, eq_comm, ← pow_eq_zero_iff two_ne_zero, hγ', h, map_zero]
  have hT0 : Algebra.trace K M (algebraMap (𝓞 M) M γ) = 0 := trace_gen_eq_zero _ _ hγ' hγK'
  -- identities in `𝓞 K`
  have hU1 : trO (K := K) (1 : 𝓞 M) = 2 := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_one, map_ofNat, ← map_one (algebraMap K M), trace_algebraMap_eq hfin,
      mul_one]
  have hV1 : trO (K := K) (γ * 1) = 0 := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, mul_one, hT0, map_zero]
  have hUalg : ∀ c : 𝓞 K, trO (K := K) (algebraMap (𝓞 K) (𝓞 M) c) = 2 * c := by
    intro c
    apply RingOfIntegers.coe_injective
    rw [coe_trO, coe_algebraMap_ringOfIntegers, trace_algebraMap_eq hfin, map_mul, map_ofNat]
  have hValg : ∀ c : 𝓞 K, trO (K := K) (γ * algebraMap (𝓞 K) (𝓞 M) c) = 0 := by
    intro c
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_mul, coe_algebraMap_ringOfIntegers, mul_comm, trace_algebraMap_mul, hT0,
      mul_zero, map_zero]
  have hUγ : trO (K := K) γ = 0 := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, hT0, map_zero]
  have hVγ : trO (K := K) (γ * γ) = 2 * b := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_mul, ← sq, hγ', trace_algebraMap_eq hfin, map_mul, map_ofNat]
  have hUadd : ∀ x y : 𝓞 M, trO (K := K) (x + y) = trO x + trO y := by
    intro x y
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_add, map_add, map_add, coe_trO, coe_trO]
  have hU0 : trO (K := K) (0 : 𝓞 M) = 0 := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_zero, map_zero, map_zero]
  have hI1 : ∀ x y : 𝓞 M, 2 * b * trO (K := K) (x * y) =
      b * trO x * trO y + trO (γ * x) * trO (γ * y) := by
    intro x y
    apply RingOfIntegers.coe_injective
    simp only [map_add, map_mul, map_ofNat, coe_trO]
    exact trace_identity_one hfin _ _ hγ' hγK' _ _
  have hI2 : ∀ x y : 𝓞 M, 2 * trO (K := K) (γ * (x * y)) =
      trO x * trO (γ * y) + trO (γ * x) * trO y := by
    intro x y
    apply RingOfIntegers.coe_injective
    simp only [map_add, map_mul, map_ofNat, coe_trO]
    exact trace_identity_two hfin _ _ hγ' hγK' hb _ _
  -- the extension
  let ψ : 𝓞 M →+* ZMod ℓ :=
    { toFun := fun x => (φ b * φ (trO x) + φ (trO (γ * x)) * t) * w
      map_one' := by
        show (φ b * φ (trO (1 : 𝓞 M)) + φ (trO (γ * 1)) * t) * w = 1
        rw [hU1, hV1, map_ofNat, map_zero]
        linear_combination hw1
      map_mul' := by
        intro x y
        show (φ b * φ (trO (x * y)) + φ (trO (γ * (x * y))) * t) * w =
          (φ b * φ (trO x) + φ (trO (γ * x)) * t) * w *
            ((φ b * φ (trO y) + φ (trO (γ * y)) * t) * w)
        have e1 := congrArg φ (hI1 x y)
        have e2 := congrArg φ (hI2 x y)
        simp only [map_add, map_mul, map_ofNat] at e1 e2
        linear_combination (-(φ b * φ (trO (x * y)) + φ (trO (γ * (x * y))) * t) * w) * hw1 +
          (w ^ 2 * φ b) * e1 + (w ^ 2 * φ b * t) * e2 -
          (w ^ 2 * φ (trO (γ * x)) * φ (trO (γ * y))) * ht
      map_zero' := by
        show (φ b * φ (trO (0 : 𝓞 M)) + φ (trO (γ * 0)) * t) * w = 0
        rw [mul_zero, hU0, map_zero]
        ring
      map_add' := by
        intro x y
        show (φ b * φ (trO (x + y)) + φ (trO (γ * (x + y))) * t) * w =
          (φ b * φ (trO x) + φ (trO (γ * x)) * t) * w +
            (φ b * φ (trO y) + φ (trO (γ * y)) * t) * w
        rw [mul_add, hUadd, hUadd, map_add, map_add]
        ring }
  refine ⟨ψ, fun c => ?_, ?_⟩
  · show (φ b * φ (trO (algebraMap (𝓞 K) (𝓞 M) c)) +
        φ (trO (γ * algebraMap (𝓞 K) (𝓞 M) c)) * t) * w = φ c
    rw [hUalg, hValg, map_mul, map_ofNat, map_zero]
    linear_combination φ c * hw1
  · show (φ b * φ (trO γ) + φ (trO (γ * γ)) * t) * w = t
    rw [hUγ, hVγ, map_mul, map_ofNat, map_zero]
    linear_combination t * hw1

/-! ### Kernels -/

theorem absNorm_ker {L : Type*} [Field L] [NumberField L] {ℓ : ℕ}
    (ψ : 𝓞 L →+* ZMod ℓ) : Ideal.absNorm (RingHom.ker ψ) = ℓ := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective ψ)).toEquiv,
    Nat.card_zmod]

theorem exists_hom_ker_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (𝔭 : Ideal (𝓞 K))
    (h : Ideal.absNorm 𝔭 = ℓ) : ∃ φ : 𝓞 K →+* ZMod ℓ, RingHom.ker φ = 𝔭 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hfin : Finite (𝓞 K ⧸ 𝔭) :=
    (Ideal.absNorm_ne_zero_iff 𝔭).mp (by rw [h]; exact hℓ.ne_zero)
  letI : Fintype (𝓞 K ⧸ 𝔭) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ 𝔭) = ℓ := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, h]
  haveI : CharP (𝓞 K ⧸ 𝔭) ℓ := charP_of_card_eq_prime hcard
  let e := ZMod.ringEquiv (𝓞 K ⧸ 𝔭) hcard
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔭), ?_⟩
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

theorem two_ne_zero_zmod {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : (2 : ZMod ℓ) ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  intro h
  have h' : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h')

/-- **Split primes.**  If `φ : 𝓞 K → ZMod ℓ` has kernel `𝔭` and `φ b` is a nonzero square, then
`𝔭` has two distinct primes of `𝓞 M` of norm `ℓ` above it. -/
theorem exists_split_primes (hfin : Module.finrank K M = 2) (b : 𝓞 K) (γ : 𝓞 M)
    (hγ : (γ : M) ^ 2 = algebraMap K M (b : K)) (hγK : (γ : M) ∉ Set.range (algebraMap K M))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (𝔭 : Ideal (𝓞 K)) (φ : 𝓞 K →+* ZMod ℓ)
    (hker : RingHom.ker φ = 𝔭) (hnorm : Ideal.absNorm 𝔭 = ℓ)
    (t : ZMod ℓ) (ht : t ^ 2 = φ b) (ht0 : t ≠ 0) :
    ∃ Q₁ Q₂ : Ideal (𝓞 M), Q₁.IsPrime ∧ Q₁ ≠ ⊥ ∧ Q₂.IsPrime ∧ Q₂ ≠ ⊥ ∧
      Ideal.absNorm Q₁ = Ideal.absNorm 𝔭 ∧ Ideal.absNorm Q₂ = Ideal.absNorm 𝔭 ∧
      Q₁.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧ Q₂.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧
      Q₁ ≠ Q₂ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have h2 := two_ne_zero_zmod hℓ hℓ2
  have hb0 : φ b ≠ 0 := by
    rw [← ht]
    exact pow_ne_zero 2 ht0
  have h2b : (2 : ZMod ℓ) * φ b ≠ 0 := mul_ne_zero h2 hb0
  obtain ⟨w, hw1⟩ : ∃ w : ZMod ℓ, 2 * φ b * w = 1 := ⟨(2 * φ b)⁻¹, mul_inv_cancel₀ h2b⟩
  obtain ⟨ψ₁, hψ₁, hψ₁γ⟩ := exists_extension hfin b γ hγ hγK φ t ht w hw1
  obtain ⟨ψ₂, hψ₂, hψ₂γ⟩ :=
    exists_extension hfin b γ hγ hγK φ (-t) (by rw [neg_sq, ht]) w hw1
  have hnormQ : ∀ ψ : 𝓞 M →+* ZMod ℓ, Ideal.absNorm (RingHom.ker ψ) = Ideal.absNorm 𝔭 :=
    fun ψ => by rw [absNorm_ker, hnorm]
  have hbot : ∀ ψ : 𝓞 M →+* ZMod ℓ, RingHom.ker ψ ≠ ⊥ := by
    intro ψ h
    have := absNorm_ker ψ
    rw [h, Ideal.absNorm_bot] at this
    exact hℓ.ne_zero this.symm
  have hcomap : ∀ ψ : 𝓞 M →+* ZMod ℓ, (∀ c : 𝓞 K, ψ (algebraMap (𝓞 K) (𝓞 M) c) = φ c) →
      (RingHom.ker ψ).comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 := by
    intro ψ hψ
    rw [RingHom.comap_ker, ← hker]
    congr 1
    exact RingHom.ext hψ
  refine ⟨RingHom.ker ψ₁, RingHom.ker ψ₂, RingHom.ker_isPrime ψ₁, hbot ψ₁,
    RingHom.ker_isPrime ψ₂, hbot ψ₂, hnormQ ψ₁, hnormQ ψ₂, hcomap ψ₁ hψ₁, hcomap ψ₂ hψ₂, ?_⟩
  obtain ⟨c, hc⟩ := ZMod.ringHom_surjective φ t
  intro heq
  have hz : γ - algebraMap (𝓞 K) (𝓞 M) c ∈ RingHom.ker ψ₁ := by
    rw [RingHom.mem_ker, map_sub, hψ₁γ, hψ₁, hc, sub_self]
  rw [heq, RingHom.mem_ker, map_sub, hψ₂γ, hψ₂, hc] at hz
  apply ht0
  have h2t : (2 : ZMod ℓ) * t = 0 := by linear_combination -hz
  rcases mul_eq_zero.mp h2t with h | h
  · exact absurd h h2
  · exact h

/-- The hypothesis of `ErdosProblems.Shared.IdealCounting.sum_countSupp_mul_le`, for primes of
prime norm larger than `N₀ ≥ 2`, when `b` is a nonzero square modulo every prime `ℓ > N₀`. -/
theorem exists_split_primes_of_forall_isSquare (hfin : Module.finrank K M = 2) (b : 𝓞 K)
    (γ : 𝓞 M) (hγ : (γ : M) ^ 2 = algebraMap K M (b : K))
    (hγK : (γ : M) ∉ Set.range (algebraMap K M)) (N₀ : ℕ) (hN₀ : 2 ≤ N₀)
    (H : ∀ ℓ : ℕ, ℓ.Prime → N₀ < ℓ → ∀ φ : 𝓞 K →+* ZMod ℓ, φ b ≠ 0 ∧ IsSquare (φ b)) :
    ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (Nat.Prime (Ideal.absNorm 𝔭) ∧ N₀ < Ideal.absNorm 𝔭) →
      ∃ Q₁ Q₂ : Ideal (𝓞 M), Q₁.IsPrime ∧ Q₁ ≠ ⊥ ∧ Q₂.IsPrime ∧ Q₂ ≠ ⊥ ∧
        Ideal.absNorm Q₁ = Ideal.absNorm 𝔭 ∧ Ideal.absNorm Q₂ = Ideal.absNorm 𝔭 ∧
        Q₁.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧ Q₂.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧
        Q₁ ≠ Q₂ := by
  intro 𝔭 _ _ hP
  obtain ⟨hpr, hbig⟩ := hP
  obtain ⟨φ, hker⟩ := exists_hom_ker_eq hpr 𝔭 rfl
  obtain ⟨hne, r, hr⟩ := H _ hpr hbig φ
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hne (by rw [hr, mul_zero])
  exact exists_split_primes hfin b γ hγ hγK hpr (by omega) 𝔭 φ hker rfl r
    (by rw [hr, sq]) hr0

end ErdosProblems.Shared.QuadraticSplit
