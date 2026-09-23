import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Analysis.PSeries
import Mathlib.FieldTheory.Finite.Basic

/-!
# Counting ideals by their prime factors in a number field

For a number field `K` and a predicate `P` on ideals of `𝓞 K`, `countSupp K P n` is the
number of ideals of absolute norm `n` all of whose prime factors satisfy `P`.  This file
proves the three coefficientwise facts that feed the pole comparison of
`ErdosProblems.Shared.DirichletPole`:

* `card_le_sum_countSupp` (**factorisation into two parts**): every ideal of norm `n` is the
  product of its `P`-part and its `¬P`-part, so the number of ideals of norm `n` is at most the
  Dirichlet convolution of the two restricted counts;
* `sum_countSupp_div_le` (**the bad part converges at `s = 1`**): when `P 𝔭` says that the
  norm of `𝔭` is a prime larger than `N₀`, the series `∑ countSupp K (¬P) n / n` has bounded
  partial sums.  The primes excluded are finitely many primes of small norm and primes of
  norm `p ^ f` with `f ≥ 2`; at most `[K : ℚ]` primes lie over each `p`, so their
  reciprocal norms are dominated by `[K : ℚ] ∑ 1 / p²`, and a finite Euler product over the
  primes involved bounds the whole series;
* `sum_countSupp_mul_le` (**split primes double the count**): if every prime `𝔭` with `P 𝔭`
  has two distinct primes of an extension `M` above it, each of the same norm as `𝔭`, then
  the Dirichlet convolution of the `P`-count with itself is at most the number of ideals of
  `𝓞 M` of norm `n`.  The injection sends a pair of ideals `(I, J)` to the product of the
  first lifts of the prime factors of `I` and the second lifts of those of `J`.
-/

noncomputable section

namespace ErdosProblems.Shared.IdealCounting

open NumberField UniqueFactorizationMonoid Ideal

variable (K : Type*) [Field K] [NumberField K]

/-- The number of ideals of `𝓞 K` of absolute norm `n` all of whose prime factors
satisfy `P`. -/
def countSupp (P : Ideal (𝓞 K) → Prop) (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // absNorm I = n ∧ ∀ 𝔭 ∈ normalizedFactors I, P 𝔭}

theorem natCard_eq_card_filter {α : Type*} (S : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ x, p x → x ∈ S) : Nat.card {x // p x} = (S.filter p).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [Finset.mem_filter]
    exact ⟨fun hx => ⟨h x hx, hx⟩, fun hx => hx.2⟩)

variable {K}

/-- The finite set of ideals of norm `n`. -/
abbrev normSet (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset

theorem mem_normSet {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ normSet n ↔ absNorm I = n := by
  simp [normSet]

theorem card_normSet (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = n} = (normSet (K := K) n).card := by
  classical
  rw [natCard_eq_card_filter (normSet n) (fun I : Ideal (𝓞 K) => absNorm I = n)
    (fun I h => mem_normSet.mpr h)]
  congr 1
  exact Finset.filter_true_of_mem fun I hI => mem_normSet.mp hI

theorem countSupp_eq (P : Ideal (𝓞 K) → Prop) (n : ℕ)
    [DecidablePred (fun I : Ideal (𝓞 K) => ∀ 𝔭 ∈ normalizedFactors I, P 𝔭)] :
    countSupp K P n = ((normSet (K := K) n).filter
      (fun I => ∀ 𝔭 ∈ normalizedFactors I, P 𝔭)).card := by
  classical
  rw [countSupp, natCard_eq_card_filter (normSet n)
    (fun I : Ideal (𝓞 K) => absNorm I = n ∧ ∀ 𝔭 ∈ normalizedFactors I, P 𝔭)
    (fun I h => mem_normSet.mpr h.1)]
  congr 1
  ext I
  simp only [Finset.mem_filter, mem_normSet]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1, h2⟩

theorem countSupp_le (P : Ideal (𝓞 K) → Prop) (n : ℕ) :
    countSupp K P n ≤ Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
  classical
  rw [countSupp_eq, card_normSet]
  exact Finset.card_filter_le _ _

/-! ### Factorisation into a `P`-part and a `¬P`-part -/

theorem prime_of_mem_normalizedFactors {I 𝔭 : Ideal (𝓞 K)} (h : 𝔭 ∈ normalizedFactors I) :
    𝔭.IsPrime ∧ 𝔭 ≠ ⊥ :=
  ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor 𝔭 h),
    (prime_of_normalized_factor 𝔭 h).ne_zero⟩

theorem normalizedFactors_prod_filter (Q : Ideal (𝓞 K) → Prop) [DecidablePred Q]
    (I : Ideal (𝓞 K)) :
    normalizedFactors ((normalizedFactors I).filter Q).prod = (normalizedFactors I).filter Q :=
  normalizedFactors_prod_of_prime fun 𝔭 h𝔭 =>
    prime_of_normalized_factor 𝔭 (Multiset.mem_of_mem_filter h𝔭)

theorem card_le_sum_countSupp (P : Ideal (𝓞 K) → Prop) {n : ℕ} (hn : n ≠ 0) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = n} ≤
      ∑ x ∈ n.divisorsAntidiagonal, countSupp K P x.1 * countSupp K (fun 𝔭 => ¬ P 𝔭) x.2 := by
  classical
  let gp : Ideal (𝓞 K) → Ideal (𝓞 K) := fun I => ((normalizedFactors I).filter P).prod
  let bp : Ideal (𝓞 K) → Ideal (𝓞 K) := fun I =>
    ((normalizedFactors I).filter (fun 𝔭 => ¬ P 𝔭)).prod
  have hgb : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → gp I * bp I = I := fun I hI => by
    simp only [gp, bp]
    rw [Multiset.prod_filter_mul_prod_filter_not, prod_normalizedFactors_eq_self hI]
  have hS0 : ∀ I ∈ normSet (K := K) n, I ≠ ⊥ := fun I hI h => by
    apply hn
    rw [← mem_normSet.mp hI, h, absNorm_bot]
  let f : Ideal (𝓞 K) → ℕ × ℕ := fun I => (absNorm (gp I), absNorm (bp I))
  have hmaps : ((normSet (K := K) n : Finset (Ideal (𝓞 K))) : Set (Ideal (𝓞 K))).MapsTo f
      (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    intro I hI
    simp only [Finset.mem_coe, Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, hn⟩
    show absNorm (gp I) * absNorm (bp I) = n
    rw [← map_mul, hgb I (hS0 I hI)]
    exact mem_normSet.mp hI
  rw [card_normSet, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [countSupp_eq, countSupp_eq, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun I => (gp I, bp I)) ?_ ?_
  · intro I hI
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hI
    obtain ⟨-, hfx⟩ := hI
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Set.mem_setOf_eq,
      mem_normSet]
    refine ⟨⟨congrArg Prod.fst hfx, ?_⟩, ⟨congrArg Prod.snd hfx, ?_⟩⟩
    · intro 𝔭 h𝔭
      simp only [gp] at h𝔭
      rw [normalizedFactors_prod_filter] at h𝔭
      exact Multiset.of_mem_filter h𝔭
    · intro 𝔭 h𝔭
      simp only [bp] at h𝔭
      rw [normalizedFactors_prod_filter] at h𝔭
      exact (Multiset.mem_filter.mp h𝔭).2
  · intro I hI J hJ hIJ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hI hJ
    have h1 : gp I = gp J := congrArg Prod.fst hIJ
    have h2 : bp I = bp J := congrArg Prod.snd hIJ
    rw [← hgb I (hS0 I hI.1), ← hgb J (hS0 J hJ.1), h1, h2]

/-! ### Split primes: the convolution of the `P`-count with itself -/

theorem sum_countSupp_mul_le (M : Type*) [Field M] [NumberField M] [Algebra K M]
    (P : Ideal (𝓞 K) → Prop)
    (hsplit : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → P 𝔭 →
      ∃ Q₁ Q₂ : Ideal (𝓞 M), Q₁.IsPrime ∧ Q₁ ≠ ⊥ ∧ Q₂.IsPrime ∧ Q₂ ≠ ⊥ ∧
        absNorm Q₁ = absNorm 𝔭 ∧ absNorm Q₂ = absNorm 𝔭 ∧
        Q₁.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧ Q₂.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧
        Q₁ ≠ Q₂)
    {n : ℕ} (hn : n ≠ 0) :
    ∑ x ∈ n.divisorsAntidiagonal, countSupp K P x.1 * countSupp K P x.2 ≤
      Nat.card {Q : Ideal (𝓞 M) // absNorm Q = n} := by
  classical
  choose! L₁ L₂ hL using hsplit
  set ι := algebraMap (𝓞 K) (𝓞 M) with hι
  -- goodness of an ideal
  let good : Ideal (𝓞 K) → Prop := fun I => ∀ 𝔭 ∈ normalizedFactors I, P 𝔭
  have hgoodL : ∀ I : Ideal (𝓞 K), good I → ∀ 𝔭 ∈ normalizedFactors I,
      (L₁ 𝔭).IsPrime ∧ L₁ 𝔭 ≠ ⊥ ∧ (L₂ 𝔭).IsPrime ∧ L₂ 𝔭 ≠ ⊥ ∧
        absNorm (L₁ 𝔭) = absNorm 𝔭 ∧ absNorm (L₂ 𝔭) = absNorm 𝔭 ∧
        (L₁ 𝔭).comap ι = 𝔭 ∧ (L₂ 𝔭).comap ι = 𝔭 ∧ L₁ 𝔭 ≠ L₂ 𝔭 := fun I hI 𝔭 h𝔭 =>
    hL 𝔭 (prime_of_mem_normalizedFactors h𝔭).1 (prime_of_mem_normalizedFactors h𝔭).2 (hI 𝔭 h𝔭)
  let X : Ideal (𝓞 K) × Ideal (𝓞 K) → Multiset (Ideal (𝓞 M)) := fun p =>
    (normalizedFactors p.1).map L₁ + (normalizedFactors p.2).map L₂
  let Φ : Ideal (𝓞 K) × Ideal (𝓞 K) → Ideal (𝓞 M) := fun p => (X p).prod
  have hXprime : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 →
      ∀ Q ∈ X p, Prime Q := by
    intro p h1 h2 Q hQ
    simp only [X, Multiset.mem_add, Multiset.mem_map] at hQ
    rcases hQ with ⟨𝔭, h𝔭, rfl⟩ | ⟨𝔭, h𝔭, rfl⟩
    · obtain ⟨hp, hb, -⟩ := hgoodL _ h1 𝔭 h𝔭
      exact Ideal.prime_of_isPrime hb hp
    · obtain ⟨-, -, hp, hb, -⟩ := hgoodL _ h2 𝔭 h𝔭
      exact Ideal.prime_of_isPrime hb hp
  have hnfΦ : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 →
      normalizedFactors (Φ p) = X p := fun p h1 h2 =>
    normalizedFactors_prod_of_prime (hXprime p h1 h2)
  -- recovering the two factorisations from `X p`
  have hrec₁ : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 →
      ((X p).filter (fun Q => L₁ (Q.comap ι) = Q)).map (fun Q => Q.comap ι) =
        normalizedFactors p.1 := by
    intro p h1 h2
    have e1 : ((normalizedFactors p.1).map L₁).filter (fun Q => L₁ (Q.comap ι) = Q) =
        (normalizedFactors p.1).map L₁ := by
      rw [Multiset.filter_eq_self]
      intro Q hQ
      obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hQ
      rw [(hgoodL _ h1 𝔭 h𝔭).2.2.2.2.2.2.1]
    have e2 : ((normalizedFactors p.2).map L₂).filter (fun Q => L₁ (Q.comap ι) = Q) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro Q hQ
      obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hQ
      rw [(hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.2.2.1]
      exact (hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.2.2.2
    show (((normalizedFactors p.1).map L₁ + (normalizedFactors p.2).map L₂).filter
      (fun Q => L₁ (Q.comap ι) = Q)).map (fun Q => Q.comap ι) = normalizedFactors p.1
    rw [Multiset.filter_add, e1, e2, add_zero, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (normalizedFactors p.1)]
    exact Multiset.map_congr rfl fun 𝔭 h𝔭 => (hgoodL _ h1 𝔭 h𝔭).2.2.2.2.2.2.1
  have hrec₂ : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 →
      ((X p).filter (fun Q => L₂ (Q.comap ι) = Q)).map (fun Q => Q.comap ι) =
        normalizedFactors p.2 := by
    intro p h1 h2
    have e1 : ((normalizedFactors p.1).map L₁).filter (fun Q => L₂ (Q.comap ι) = Q) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro Q hQ
      obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hQ
      rw [(hgoodL _ h1 𝔭 h𝔭).2.2.2.2.2.2.1]
      exact fun h => (hgoodL _ h1 𝔭 h𝔭).2.2.2.2.2.2.2.2 h.symm
    have e2 : ((normalizedFactors p.2).map L₂).filter (fun Q => L₂ (Q.comap ι) = Q) =
        (normalizedFactors p.2).map L₂ := by
      rw [Multiset.filter_eq_self]
      intro Q hQ
      obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hQ
      rw [(hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.2.2.1]
    show (((normalizedFactors p.1).map L₁ + (normalizedFactors p.2).map L₂).filter
      (fun Q => L₂ (Q.comap ι) = Q)).map (fun Q => Q.comap ι) = normalizedFactors p.2
    rw [Multiset.filter_add, e1, e2, zero_add, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (normalizedFactors p.2)]
    exact Multiset.map_congr rfl fun 𝔭 h𝔭 => (hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.2.2.1
  -- the norm of `Φ p`
  have hnormΦ : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 → p.1 ≠ ⊥ → p.2 ≠ ⊥ →
      absNorm (Φ p) = absNorm p.1 * absNorm p.2 := by
    intro p h1 h2 hp1 hp2
    simp only [Φ, X]
    rw [Multiset.prod_add, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map,
      Multiset.map_map]
    conv_rhs => rw [← prod_normalizedFactors_eq_self hp1, ← prod_normalizedFactors_eq_self hp2,
      map_multiset_prod, map_multiset_prod]
    congr 1
    · congr 1
      refine Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_
      exact (hgoodL _ h1 𝔭 h𝔭).2.2.2.2.1
    · congr 1
      refine Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_
      exact (hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.1
  -- the finite set of good pairs
  let G : ℕ → Finset (Ideal (𝓞 K)) := fun m =>
    (normSet (K := K) m).filter (fun I => ∀ 𝔭 ∈ normalizedFactors I, P 𝔭)
  let U : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
    n.divisorsAntidiagonal.biUnion fun x => G x.1 ×ˢ G x.2
  have hU : ∀ p ∈ U, good p.1 ∧ good p.2 ∧ absNorm p.1 * absNorm p.2 = n := by
    intro p hp
    simp only [U, Finset.mem_biUnion, Finset.mem_product, G, Finset.mem_filter,
      mem_normSet] at hp
    obtain ⟨x, hx, ⟨h1, g1⟩, ⟨h2, g2⟩⟩ := hp
    refine ⟨g1, g2, ?_⟩
    rw [h1, h2]
    exact (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hU0 : ∀ p ∈ U, p.1 ≠ ⊥ ∧ p.2 ≠ ⊥ := by
    intro p hp
    obtain ⟨-, -, hnorm⟩ := hU p hp
    constructor
    · intro h
      apply hn
      rw [← hnorm, h, absNorm_bot, zero_mul]
    · intro h
      apply hn
      rw [← hnorm, h, absNorm_bot, mul_zero]
  have hcardU : U.card = ∑ x ∈ n.divisorsAntidiagonal, countSupp K P x.1 * countSupp K P x.2 := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.card_product, countSupp_eq, countSupp_eq]
    · intro x _ y _ hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hpx hpy
      simp only [Finset.mem_product, G, Finset.mem_filter, mem_normSet] at hpx hpy
      apply hxy
      exact Prod.ext (hpx.1.1.symm.trans hpy.1.1) (hpx.2.1.symm.trans hpy.2.1)
  rw [← hcardU, card_normSet]
  refine Finset.card_le_card_of_injOn Φ ?_ ?_
  · intro p hp
    have hp' : p ∈ U := hp
    obtain ⟨g1, g2, hnorm⟩ := hU p hp'
    obtain ⟨hb1, hb2⟩ := hU0 p hp'
    simp only [Finset.mem_coe, mem_normSet]
    rw [hnormΦ p g1 g2 hb1 hb2, hnorm]
  · intro p hp q hq hpq
    have hp' : p ∈ U := hp
    have hq' : q ∈ U := hq
    obtain ⟨gp1, gp2, -⟩ := hU p hp'
    obtain ⟨gq1, gq2, -⟩ := hU q hq'
    obtain ⟨hp1, hp2⟩ := hU0 p hp'
    obtain ⟨hq1, hq2⟩ := hU0 q hq'
    have hX : X p = X q := by
      rw [← hnfΦ p gp1 gp2, ← hnfΦ q gq1 gq2]
      exact congrArg normalizedFactors hpq
    have e1 : normalizedFactors p.1 = normalizedFactors q.1 := by
      rw [← hrec₁ p gp1 gp2, ← hrec₁ q gq1 gq2, hX]
    have e2 : normalizedFactors p.2 = normalizedFactors q.2 := by
      rw [← hrec₂ p gp1 gp2, ← hrec₂ q gq1 gq2, hX]
    refine Prod.ext ?_ ?_
    · rw [← prod_normalizedFactors_eq_self hp1, ← prod_normalizedFactors_eq_self hq1, e1]
    · rw [← prod_normalizedFactors_eq_self hp2, ← prod_normalizedFactors_eq_self hq2, e2]

/-! ### A finite Euler product bound -/

theorem sum_inv_absNorm_le_prod (F : Finset (Ideal (𝓞 K))) (hF : ∀ 𝔭 ∈ F, 2 ≤ absNorm 𝔭)
    (T : Finset (Ideal (𝓞 K)))
    (hT : ∀ I ∈ T, I ≠ ⊥ ∧ ∀ 𝔭 ∈ normalizedFactors I, 𝔭 ∈ F) :
    ∑ I ∈ T, ((absNorm I : ℝ))⁻¹ ≤ ∏ 𝔭 ∈ F, (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹ := by
  classical
  set E : ℕ := T.sup (fun I => Multiset.card (normalizedFactors I)) with hE
  let Φ : (F → ℕ) → Ideal (𝓞 K) := fun e => ∏ i : F, (i : Ideal (𝓞 K)) ^ (e i)
  have hsub : T ⊆ (Fintype.piFinset (fun _ : F => Finset.range (E + 1))).image Φ := by
    intro I hI
    obtain ⟨hI0, hIF⟩ := hT I hI
    rw [Finset.mem_image]
    refine ⟨fun i => Multiset.count (i : Ideal (𝓞 K)) (normalizedFactors I), ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (Multiset.count_le_card _ _).trans
        (Finset.le_sup (f := fun I => Multiset.card (normalizedFactors I)) hI)
    · simp only [Φ]
      rw [Finset.prod_coe_sort F (fun i => i ^ Multiset.count i (normalizedFactors I)),
        ← Finset.prod_multiset_count_of_subset (normalizedFactors I) F]
      · exact prod_normalizedFactors_eq_self hI0
      · intro 𝔭 h𝔭
        exact hIF 𝔭 (Multiset.mem_toFinset.mp h𝔭)
  have hw : ∀ e : F → ℕ, ((absNorm (Φ e) : ℝ))⁻¹ =
      ∏ i : F, (((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹) ^ (e i) := by
    intro e
    simp only [Φ, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow, Finset.prod_inv_distrib,
      inv_pow]
  have hnn : ∀ I : Ideal (𝓞 K), 0 ≤ ((absNorm I : ℝ))⁻¹ := fun I =>
    inv_nonneg.mpr (Nat.cast_nonneg _)
  calc ∑ I ∈ T, ((absNorm I : ℝ))⁻¹
      ≤ ∑ I ∈ (Fintype.piFinset (fun _ : F => Finset.range (E + 1))).image Φ,
          ((absNorm I : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ => hnn I)
    _ ≤ ∑ e ∈ Fintype.piFinset (fun _ : F => Finset.range (E + 1)),
          ((absNorm (Φ e) : ℝ))⁻¹ :=
        Finset.sum_image_le_of_nonneg (fun I _ => hnn I)
    _ = ∑ e ∈ Fintype.piFinset (fun _ : F => Finset.range (E + 1)),
          ∏ i : F, (((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹) ^ (e i) :=
        Finset.sum_congr rfl fun e _ => hw e
    _ = ∏ i : F, ∑ k ∈ Finset.range (E + 1), (((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹) ^ k :=
        (Finset.prod_univ_sum (ι := F) (fun _ => Finset.range (E + 1))
          (fun (i : F) (k : ℕ) => (((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹) ^ k)).symm
    _ ≤ ∏ i : F, (1 - ((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹)⁻¹ := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg fun k _ => pow_nonneg (hnn _) k
        · intro i _
          have h2 : (2 : ℝ) ≤ absNorm (i : Ideal (𝓞 K)) := by exact_mod_cast hF i i.2
          have hx0 : 0 ≤ ((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹ := hnn _
          have hx1 : ((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹ < 1 :=
            inv_lt_one_of_one_lt₀ (by linarith)
          rw [← tsum_geometric_of_lt_one hx0 hx1]
          exact Summable.sum_le_tsum _ (fun k _ => pow_nonneg hx0 k)
            (summable_geometric_of_lt_one hx0 hx1)
    _ = ∏ 𝔭 ∈ F, (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹ :=
        Finset.prod_coe_sort F (fun 𝔭 => (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹)

theorem inv_one_sub_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have h1x : 0 < 1 - x := by linarith
  calc (1 - x)⁻¹ ≤ 2 * x + 1 := by
        rw [← one_div, div_le_iff₀ h1x]
        nlinarith
    _ ≤ Real.exp (2 * x) := Real.add_one_le_exp _

theorem prod_inv_one_sub_le_exp (F : Finset (Ideal (𝓞 K))) (hF : ∀ 𝔭 ∈ F, 2 ≤ absNorm 𝔭) :
    ∏ 𝔭 ∈ F, (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹ ≤
      Real.exp (2 * ∑ 𝔭 ∈ F, ((absNorm 𝔭 : ℝ))⁻¹) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro 𝔭 h𝔭
    have h2 : (2 : ℝ) ≤ absNorm 𝔭 := by exact_mod_cast hF 𝔭 h𝔭
    have hx1 : ((absNorm 𝔭 : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    exact inv_nonneg.mpr (by linarith)
  · intro 𝔭 h𝔭
    have h2 : (2 : ℝ) ≤ absNorm 𝔭 := by exact_mod_cast hF 𝔭 h𝔭
    apply inv_one_sub_le_exp (inv_nonneg.mpr (Nat.cast_nonneg _))
    rw [one_div]
    exact inv_anti₀ (by norm_num) h2

/-! ### Primes of non-prime norm -/

theorem exists_prime_pow_absNorm {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥) :
    ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ absNorm 𝔭 = p ^ k ∧ (p : 𝓞 K) ∈ 𝔭 := by
  haveI : 𝔭.IsMaximal := hp.isMaximal h0
  letI : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have hne : absNorm 𝔭 ≠ 0 := by rwa [Ne, absNorm_eq_zero_iff]
  haveI hfin : Finite (𝓞 K ⧸ 𝔭) := (absNorm_ne_zero_iff 𝔭).mp hne
  letI : Fintype (𝓞 K ⧸ 𝔭) := Fintype.ofFinite _
  obtain ⟨k, hpr, hcard⟩ := FiniteField.card (𝓞 K ⧸ 𝔭) (ringChar (𝓞 K ⧸ 𝔭))
  refine ⟨ringChar (𝓞 K ⧸ 𝔭), k, hpr, k.pos, ?_, ?_⟩
  · rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar

theorem card_le_finrank_of_forall_mem {p : ℕ} (hp : p.Prime) (F : Finset (Ideal (𝓞 K)))
    (hF : ∀ 𝔭 ∈ F, 𝔭.IsPrime ∧ (p : 𝓞 K) ∈ 𝔭) : F.card ≤ Module.finrank ℚ K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  calc F.card ≤ (primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card := by
        apply Finset.card_le_card
        intro 𝔭 h𝔭
        obtain ⟨hprime, hmem⟩ := hF 𝔭 h𝔭
        rw [mem_primesOverFinset_iff hp0]
        refine ⟨hprime, ⟨?_⟩⟩
        refine (Int.ideal_span_isMaximal_of_prime p).eq_of_le ?_ ?_
        · haveI := hprime
          exact Ideal.IsPrime.ne_top (Ideal.IsPrime.comap (algebraMap ℤ (𝓞 K)))
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          simpa using hmem
    _ ≤ Module.finrank ℚ K := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hp0

/-- The primes excluded by `P 𝔭 := (absNorm 𝔭 prime ∧ N₀ < absNorm 𝔭)` have uniformly
bounded sums of reciprocal norms. -/
theorem exists_bound_sum_inv_absNorm (N₀ : ℕ) :
    ∃ C : ℝ, ∀ F : Finset (Ideal (𝓞 K)),
      (∀ 𝔭 ∈ F, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) →
        ∑ 𝔭 ∈ F, ((absNorm 𝔭 : ℝ))⁻¹ ≤ C := by
  classical
  set F₀ := (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N₀).toFinset with hF₀
  have hsumm : Summable (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr one_lt_two
  refine ⟨F₀.card + Module.finrank ℚ K * ∑' m : ℕ, ((m : ℝ) ^ 2)⁻¹, ?_⟩
  intro F hF
  rw [← Finset.sum_filter_add_sum_filter_not F (fun 𝔭 => absNorm 𝔭 ≤ N₀)]
  have hone : ∀ 𝔭 ∈ F, (1 : ℝ) ≤ absNorm 𝔭 := by
    intro 𝔭 h𝔭
    have h0 : absNorm 𝔭 ≠ 0 := by rw [Ne, absNorm_eq_zero_iff]; exact (hF 𝔭 h𝔭).2.1
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  refine add_le_add ?_ ?_
  · calc ∑ 𝔭 ∈ F.filter (fun 𝔭 => absNorm 𝔭 ≤ N₀), ((absNorm 𝔭 : ℝ))⁻¹
        ≤ ∑ 𝔭 ∈ F.filter (fun 𝔭 => absNorm 𝔭 ≤ N₀), (1 : ℝ) := by
          refine Finset.sum_le_sum fun 𝔭 h𝔭 => ?_
          exact inv_le_one_of_one_le₀ (hone 𝔭 (Finset.mem_of_mem_filter 𝔭 h𝔭))
      _ = ((F.filter (fun 𝔭 => absNorm 𝔭 ≤ N₀)).card : ℝ) := by simp
      _ ≤ F₀.card := by
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          intro 𝔭 h𝔭
          rw [hF₀, Set.Finite.mem_toFinset]
          exact (Finset.mem_filter.mp h𝔭).2
  · set F₂ := F.filter (fun 𝔭 => ¬ absNorm 𝔭 ≤ N₀) with hF₂
    let q : Ideal (𝓞 K) → ℕ := fun 𝔭 => (absNorm 𝔭).minFac
    have hq : ∀ 𝔭 ∈ F₂, (q 𝔭).Prime ∧ ((q 𝔭 : ℕ) : 𝓞 K) ∈ 𝔭 ∧ (q 𝔭) ^ 2 ≤ absNorm 𝔭 := by
      intro 𝔭 h𝔭
      obtain ⟨h𝔭F, hbig⟩ := Finset.mem_filter.mp h𝔭
      obtain ⟨hprime, hbot, hbad⟩ := hF 𝔭 h𝔭F
      have hnotprime : ¬ Nat.Prime (absNorm 𝔭) := fun h => hbad ⟨h, not_le.mp hbig⟩
      obtain ⟨p, k, hp, hk, hnorm, hmem⟩ := exists_prime_pow_absNorm hprime hbot
      have hqp : q 𝔭 = p := by
        simp only [q]
        rw [hnorm]
        exact Nat.Prime.pow_minFac hp hk.ne'
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk1 : k = 1 := by omega
        rw [hnorm, hk1, pow_one] at hnotprime
        exact hnotprime hp
      refine ⟨hqp ▸ hp, hqp ▸ hmem, ?_⟩
      rw [hqp, hnorm]
      exact Nat.pow_le_pow_right hp.pos hk2
    have hfib : ∀ r ∈ F₂.image q, (F₂.filter (fun 𝔭 => q 𝔭 = r)).card ≤ Module.finrank ℚ K := by
      intro r hr
      obtain ⟨𝔭₀, h𝔭₀, rfl⟩ := Finset.mem_image.mp hr
      apply card_le_finrank_of_forall_mem (hq 𝔭₀ h𝔭₀).1
      intro 𝔭 h𝔭
      obtain ⟨h𝔭F₂, hqe⟩ := Finset.mem_filter.mp h𝔭
      refine ⟨(hF 𝔭 (Finset.mem_of_mem_filter 𝔭 h𝔭F₂)).1, ?_⟩
      rw [← hqe]
      exact (hq 𝔭 h𝔭F₂).2.1
    calc ∑ 𝔭 ∈ F₂, ((absNorm 𝔭 : ℝ))⁻¹
        ≤ ∑ 𝔭 ∈ F₂, (((q 𝔭 : ℕ) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun 𝔭 h𝔭 => ?_
          have hq2 := (hq 𝔭 h𝔭).2.2
          have hqpos : (0 : ℝ) < ((q 𝔭 : ℕ) : ℝ) ^ 2 := by
            have := (hq 𝔭 h𝔭).1.pos
            positivity
          exact inv_anti₀ hqpos (by exact_mod_cast hq2)
      _ = ∑ r ∈ F₂.image q, ∑ 𝔭 ∈ F₂.filter (fun 𝔭 => q 𝔭 = r), (((q 𝔭 : ℕ) : ℝ) ^ 2)⁻¹ :=
          (Finset.sum_fiberwise_of_maps_to (fun 𝔭 h𝔭 => Finset.mem_image_of_mem q h𝔭) _).symm
      _ = ∑ r ∈ F₂.image q, ((F₂.filter (fun 𝔭 => q 𝔭 = r)).card : ℝ) * (((r : ℕ) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_congr rfl (g := fun _ => (((r : ℕ) : ℝ) ^ 2)⁻¹)]
          · rw [Finset.sum_const, nsmul_eq_mul]
          · intro 𝔭 h𝔭
            rw [(Finset.mem_filter.mp h𝔭).2]
      _ ≤ ∑ r ∈ F₂.image q, (Module.finrank ℚ K : ℝ) * (((r : ℕ) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun r hr => ?_
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (by positivity))
          exact_mod_cast hfib r hr
      _ = (Module.finrank ℚ K : ℝ) * ∑ r ∈ F₂.image q, (((r : ℕ) : ℝ) ^ 2)⁻¹ :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, ((m : ℝ) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact Summable.sum_le_tsum _ (fun m _ => inv_nonneg.mpr (by positivity)) hsumm

/-- **The `¬P`-part converges at `s = 1`** for `P 𝔭 := (absNorm 𝔭 prime ∧ N₀ < absNorm 𝔭)`. -/
theorem sum_countSupp_div_le (N₀ : ℕ) :
    ∃ B : ℝ, ∀ X : ℕ, ∑ n ∈ Finset.range X,
      (countSupp K (fun 𝔭 => ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) n : ℝ) / n ≤ B := by
  classical
  obtain ⟨C, hC⟩ := exists_bound_sum_inv_absNorm (K := K) N₀
  refine ⟨Real.exp (2 * C), fun X => ?_⟩
  have hfinT : {I : Ideal (𝓞 K) | absNorm I < X ∧ I ≠ ⊥ ∧
      ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)}.Finite :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) X).subset fun I hI => le_of_lt hI.1
  set T := hfinT.toFinset with hT
  have hmemT : ∀ I, I ∈ T ↔ absNorm I < X ∧ I ≠ ⊥ ∧
      ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) := fun I => by
    rw [hT, Set.Finite.mem_toFinset]
    rfl
  have hsumT : ∑ n ∈ Finset.range X,
      (countSupp K (fun 𝔭 => ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) n : ℝ) / n =
        ∑ I ∈ T, ((absNorm I : ℝ))⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := Finset.range X)
      (g := fun I => absNorm I) (fun I hI => Finset.mem_range.mpr ((hmemT I).mp hI).1)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => ((n : ℝ))⁻¹)
      (fun I hI => by rw [(Finset.mem_filter.mp hI).2]), Finset.sum_const, nsmul_eq_mul,
      div_eq_mul_inv]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    congr 1
    have hcard := natCard_eq_card_filter T
      (fun I : Ideal (𝓞 K) => absNorm I = n ∧
        ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭))
      (fun I hI => by
        refine (hmemT I).mpr ⟨?_, ?_, hI.2⟩
        · rw [hI.1]
          exact Finset.mem_range.mp ‹n ∈ Finset.range X›
        · intro h
          apply hn
          rw [← hI.1, h, absNorm_bot])
    have hfilt : T.filter (fun I : Ideal (𝓞 K) => absNorm I = n ∧
        ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) =
        T.filter (fun I => absNorm I = n) := by
      ext I
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2, ((hmemT I).mp h1).2.2⟩
    rw [hfilt] at hcard
    unfold countSupp
    exact_mod_cast hcard
  rw [hsumT]
  have hTprop : ∀ I ∈ T, I ≠ ⊥ ∧
      ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) :=
    fun I hI => ((hmemT I).mp hI).2
  let F : Finset (Ideal (𝓞 K)) := T.biUnion fun I => (normalizedFactors I).toFinset
  have hF : ∀ 𝔭 ∈ F, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) := by
    intro 𝔭 h𝔭
    obtain ⟨I, hI, h𝔭I⟩ := Finset.mem_biUnion.mp h𝔭
    rw [Multiset.mem_toFinset] at h𝔭I
    exact ⟨(prime_of_mem_normalizedFactors h𝔭I).1, (prime_of_mem_normalizedFactors h𝔭I).2,
      (hTprop I hI).2 𝔭 h𝔭I⟩
  have hF2 : ∀ 𝔭 ∈ F, 2 ≤ absNorm 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨hprime, hbot, -⟩ := hF 𝔭 h𝔭
    have h0 : absNorm 𝔭 ≠ 0 := by rw [Ne, absNorm_eq_zero_iff]; exact hbot
    have h1 : absNorm 𝔭 ≠ 1 := by rw [Ne, absNorm_eq_one_iff]; exact hprime.ne_top
    omega
  calc ∑ I ∈ T, ((absNorm I : ℝ))⁻¹
      ≤ ∏ 𝔭 ∈ F, (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹ := by
        refine sum_inv_absNorm_le_prod F hF2 T fun I hI => ⟨(hTprop I hI).1, fun 𝔭 h𝔭 => ?_⟩
        exact Finset.mem_biUnion.mpr ⟨I, hI, Multiset.mem_toFinset.mpr h𝔭⟩
    _ ≤ Real.exp (2 * ∑ 𝔭 ∈ F, ((absNorm 𝔭 : ℝ))⁻¹) := prod_inv_one_sub_le_exp F hF2
    _ ≤ Real.exp (2 * C) := by
        apply Real.exp_le_exp.mpr
        have := hC F hF
        linarith

end ErdosProblems.Shared.IdealCounting
