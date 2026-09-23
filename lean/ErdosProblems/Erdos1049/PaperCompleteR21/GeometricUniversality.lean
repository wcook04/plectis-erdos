import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import ErdosProblems.Erdos1049.QProductBoundsR10

/-!
# Erdős #1049: determinants of geometric moments

`long1049:thm:geometric-universality` (core.tex, subsection "The size of `V_N^*` at a fixed
base"). Fix `0 < q < 1`, `P = (q;q)_∞` (the tree's `qPochhammerInfinity q q`),
`𝓜(q) = ∏_{d ≥ 1} (1 - q^d)^{-d}` (`gramM`) and `B_N = ∑_{j<N} j^2`. For weights `a_k > 0` with
`a_{k+h}/a_k → 1` for each fixed `h` and `a_{k+h}/a_k ≤ C (1+h)^κ`, the moments
`M_m = ∑_k a_k q^{(m+1)k}` converge and `D_N = det (M_{i+j})_{i,j<N}` satisfies
`D_N ∼ 𝓜(q)^3 q^{B_N} P^{2N} ∏_{k<N} a_k`. The main theorem is `geometric_universality`.

## Route

* `hasSum_heine`: Heine's expansion
  `D_N = ∑_{k_0<⋯<k_{N-1}} ∏_i a_{k_i} q^{k_i} ∏_{i<j} (q^{k_i} - q^{k_j})^2`, from the finite
  Andreief identity (`card_mul_det_truncHankel`, `sum_box_heineTerm`) and monotone passage from
  the first `K` atoms to the whole measure.
* `cauchy_det`: Cauchy's determinant, specialised in `cauchy_unit` to the unit weights, whose
  moments are `(1 - q^{m+1})^{-1}`.
* `tendsto_eProd`: `E_N = ∏_{j<N} (q;q)_j/P → 𝓜(q)`; `heineTerm_base`: the summand of the tuple
  `(0,…,N-1)` with unit weights is `q^{B_N} P^{2N} E_N^2`; `prod_unit_mul_eProd_sq`:
  `∏_{i,j<N} (1 - q^{i+j+1}) · E_N^2 = E_{2N}`.
* `partEquiv`, `hasSum_part`: strictly increasing `N`-tuples are indexed by partitions `μ` with
  at most `N` parts (`k_i = i + μ_{N-1-i}`), one index set for every `N`.
* `phi1_kappa_le`, `pi_kappa_le`, `summable_majorant`: the bound
  `∏_{j<ℓ(μ)} P^{-2} C (1+μ_j)^κ q^{(2j+1)μ_j}`, uniform in `N` and summable over partitions.
* Tannery's theorem compares the weights `a` with the unit weights partition by partition. The
  paper identifies the common pointwise limit of the two families of terms; here dominated
  convergence is applied to their difference, so that limit is never computed, and the unit
  weights are evaluated in closed form through Cauchy's determinant.
-/

noncomputable section

namespace ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality

open Filter Finset Matrix
open scoped Topology BigOperators Classical
open ErdosProblems.Erdos1049.PaperR10 (qPochhammerFinite qPochhammerInfinity)

/-! ### Heine's expansion -/

section Heine

variable {N : ℕ}

/-- The Vandermonde determinant `det (x_{f i}^j)`. -/
def vdet (x : ℕ → ℝ) (f : Fin N → ℕ) : ℝ := (vandermonde fun i => x (f i)).det

/-- The summand `∏_i w_{f i} · V(f)^2` of Heine's expansion. -/
def heineTerm (w x : ℕ → ℝ) (f : Fin N → ℕ) : ℝ := (∏ i, w (f i)) * vdet x f ^ 2

/-- The Hankel matrix of the moments truncated to the first `K` atoms. -/
def truncHankel (w x : ℕ → ℝ) (N K : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ∑ k ∈ range K, w k * x k ^ (i.val + j.val)

/-- The box of tuples with entries below `K`. -/
def box (N K : ℕ) : Finset (Fin N → ℕ) := Fintype.piFinset fun _ => range K

lemma mem_box {K : ℕ} {f : Fin N → ℕ} : f ∈ box N K ↔ ∀ i, f i < K := by
  simp [box]

lemma det_truncHankel_expand (w x : ℕ → ℝ) (N K : ℕ) :
    (truncHankel w x N K).det =
      ∑ f ∈ box N K, (∏ i, w (f i) * x (f i) ^ (i : ℕ)) * vdet x f := by
  rw [det_apply']
  simp only [truncHankel, of_apply]
  simp_rw [prod_univ_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun f _ => ?_
  rw [vdet, ← det_transpose, det_apply', mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  simp only [transpose_apply, vandermonde_apply, pow_add, prod_mul_distrib]
  ring

lemma sum_box_comp_perm {β : Type*} [AddCommMonoid β] (K : ℕ) (τ : Equiv.Perm (Fin N))
    (F : (Fin N → ℕ) → β) :
    ∑ f ∈ box N K, F (f ∘ τ) = ∑ f ∈ box N K, F f := by
  refine sum_nbij' (fun f => f ∘ τ) (fun f => f ∘ τ.symm) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_box] at hf ⊢
    intro i
    exact hf (τ i)
  · intro f hf
    simp only [mem_box] at hf ⊢
    intro i
    exact hf (τ.symm i)
  · intro f _
    funext i
    simp
  · intro f _
    funext i
    simp
  · intro f _
    rfl

lemma vdet_comp_perm (x : ℕ → ℝ) (f : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    vdet x (f ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℝ) * vdet x f := by
  unfold vdet
  have h : (vandermonde fun i => x ((f ∘ τ) i)) =
      (vandermonde fun i => x (f i)).submatrix τ id := by
    ext i j
    simp [vandermonde_apply]
  rw [h, det_permute]

lemma card_mul_det_truncHankel (w x : ℕ → ℝ) (N K : ℕ) :
    (N.factorial : ℝ) * (truncHankel w x N K).det = ∑ f ∈ box N K, heineTerm w x f := by
  have hperm : ∀ τ : Equiv.Perm (Fin N), (truncHankel w x N K).det =
      ∑ f ∈ box N K, ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        ((∏ i, w (f i)) * vdet x f * ∏ i, x (f (τ i)) ^ (i : ℕ)) := by
    intro τ
    rw [det_truncHankel_expand, ← sum_box_comp_perm K τ
      (fun f => (∏ i, w (f i) * x (f i) ^ (i : ℕ)) * vdet x f)]
    refine sum_congr rfl fun f _ => ?_
    rw [vdet_comp_perm]
    simp only [Function.comp_apply, prod_mul_distrib]
    have hw : ∏ i, w (f (τ i)) = ∏ i, w (f i) := Equiv.prod_comp τ (fun i => w (f i))
    rw [hw]
    ring
  have hV : ∀ f : Fin N → ℕ, ∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign τ : ℤ) : ℝ) *
      ∏ i, x (f (τ i)) ^ (i : ℕ) = vdet x f := by
    intro f
    rw [vdet, det_apply']
    simp only [vandermonde_apply]
  calc (N.factorial : ℝ) * (truncHankel w x N K).det
      = ∑ τ : Equiv.Perm (Fin N), (truncHankel w x N K).det := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ τ : Equiv.Perm (Fin N), ∑ f ∈ box N K, ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        ((∏ i, w (f i)) * vdet x f * ∏ i, x (f (τ i)) ^ (i : ℕ)) :=
        sum_congr rfl fun τ _ => hperm τ
    _ = ∑ f ∈ box N K, ∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        ((∏ i, w (f i)) * vdet x f * ∏ i, x (f (τ i)) ^ (i : ℕ)) := sum_comm
    _ = ∑ f ∈ box N K, heineTerm w x f := by
        refine sum_congr rfl fun f _ => ?_
        have h1 : ∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign τ : ℤ) : ℝ) *
            ((∏ i, w (f i)) * vdet x f * ∏ i, x (f (τ i)) ^ (i : ℕ)) =
            ((∏ i, w (f i)) * vdet x f) * ∑ τ : Equiv.Perm (Fin N),
              ((Equiv.Perm.sign τ : ℤ) : ℝ) * ∏ i, x (f (τ i)) ^ (i : ℕ) := by
          rw [mul_sum]
          exact sum_congr rfl fun τ _ => by ring
        rw [h1, hV f, heineTerm]
        ring

lemma heineTerm_comp_perm (w x : ℕ → ℝ) (f : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    heineTerm w x (f ∘ τ) = heineTerm w x f := by
  unfold heineTerm
  rw [vdet_comp_perm]
  have hw : ∏ i, w ((f ∘ τ) i) = ∏ i, w (f i) := Equiv.prod_comp τ (fun i => w (f i))
  rw [hw, mul_pow]
  have hs : ((Equiv.Perm.sign τ : ℤ) : ℝ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> norm_num
  rw [hs, one_mul]

lemma heineTerm_eq_zero_of_not_injective (w x : ℕ → ℝ) {f : Fin N → ℕ}
    (hf : ¬ Function.Injective f) : heineTerm w x f = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  unfold heineTerm vdet
  rw [det_zero_of_row_eq hne]
  · simp
  · funext k
    simp [vandermonde_apply, hij]

lemma sum_box_heineTerm (w x : ℕ → ℝ) (N K : ℕ) :
    ∑ f ∈ box N K, heineTerm w x f =
      (N.factorial : ℝ) * ∑ f ∈ (box N K).filter StrictMono, heineTerm w x f := by
  set S := (box N K).filter StrictMono with hS
  set Ψ : (Fin N → ℕ) × Equiv.Perm (Fin N) → (Fin N → ℕ) := fun p => p.1 ∘ p.2 with hΨ
  have hinj : Set.InjOn Ψ ↑(S ×ˢ (univ : Finset (Equiv.Perm (Fin N)))) := by
    rintro ⟨g, τ⟩ hg ⟨g', τ'⟩ hg' heq
    simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, hS, coe_univ, Set.mem_univ,
      and_true] at hg hg'
    simp only [hΨ] at heq
    set π : Equiv.Perm (Fin N) := τ' * τ⁻¹ with hπ
    have hgπ : ∀ i, g i = g' (π i) := by
      intro i
      have := congrFun heq (τ⁻¹ i)
      simpa [hπ, Equiv.Perm.mul_apply] using this
    have hπmono : Monotone π := by
      intro i j hij
      have h1 : g i ≤ g j := hg.2.monotone hij
      rw [hgπ i, hgπ j] at h1
      exact hg'.2.le_iff_le.mp h1
    have hπ1 : π = 1 := (Equiv.Perm.monotone_iff π).mp hπmono
    have hττ : τ' = τ := by
      rw [hπ, mul_inv_eq_one] at hπ1
      exact hπ1
    subst hττ
    have hgg : g = g' := by
      funext i
      have := congrFun heq (τ'⁻¹ i)
      simpa using this
    rw [hgg]
  have himage_sub : (S ×ˢ univ).image Ψ ⊆ box N K := by
    intro f hf
    simp only [mem_image, mem_product, mem_filter, hS, mem_univ, and_true] at hf
    obtain ⟨⟨g, τ⟩, ⟨hg, _⟩, rfl⟩ := hf
    rw [mem_box] at hg ⊢
    intro i
    exact hg (τ i)
  have hzero : ∀ f ∈ box N K, f ∉ (S ×ˢ univ).image Ψ → heineTerm w x f = 0 := by
    intro f hf hfn
    by_contra hne
    have hfinj : Function.Injective f := by
      by_contra hni
      exact hne (heineTerm_eq_zero_of_not_injective w x hni)
    apply hfn
    rw [mem_image]
    refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
    · simp only [mem_product, mem_filter, hS, mem_univ, and_true]
      refine ⟨?_, ?_⟩
      · rw [mem_box] at hf ⊢
        intro i
        exact hf _
      · exact (Tuple.monotone_sort f).strictMono_of_injective
          (hfinj.comp (Tuple.sort f).injective)
    · funext i
      simp [hΨ]
  rw [← sum_subset himage_sub hzero, sum_image hinj, sum_product, mul_sum]
  refine sum_congr rfl fun g _ => ?_
  simp only [hΨ, heineTerm_comp_perm, sum_const, card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

theorem det_truncHankel_eq (w x : ℕ → ℝ) (N K : ℕ) :
    (truncHankel w x N K).det =
      ∑ f ∈ box N K, if StrictMono f then heineTerm w x f else 0 := by
  rw [← sum_filter]
  have h := card_mul_det_truncHankel w x N K
  rw [sum_box_heineTerm] at h
  have hN : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  exact mul_left_cancel₀ hN h

/-- **Heine's expansion** for a positive discrete measure. -/
theorem hasSum_heine (w x : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (N : ℕ) (Mo : ℕ → ℝ)
    (hMo : ∀ m : ℕ, HasSum (fun k => w k * x k ^ m) (Mo m)) :
    HasSum (fun f : Fin N → ℕ => if StrictMono f then heineTerm w x f else 0)
      (Matrix.of fun i j : Fin N => Mo (i.val + j.val)).det := by
  set g : (Fin N → ℕ) → ℝ := fun f => if StrictMono f then heineTerm w x f else 0 with hg
  have hg0 : ∀ f, 0 ≤ g f := by
    intro f
    simp only [hg]
    split_ifs
    · exact mul_nonneg (prod_nonneg fun i _ => hw _) (sq_nonneg _)
    · exact le_rfl
  have hTmono : Monotone (box N) := by
    intro K K' hKK' f hf
    rw [mem_box] at hf ⊢
    exact fun i => lt_of_lt_of_le (hf i) hKK'
  have hTcover : ∀ f : Fin N → ℕ, ∃ K, f ∈ box N K := by
    intro f
    refine ⟨univ.sup f + 1, ?_⟩
    rw [mem_box]
    intro i
    exact Nat.lt_succ_of_le (le_sup (mem_univ i))
  have hTtend : Tendsto (box N) atTop atTop := tendsto_atTop_finset_of_monotone hTmono hTcover
  have hpartial : ∀ K, ∑ f ∈ box N K, g f = (truncHankel w x N K).det := fun K =>
    (det_truncHankel_eq w x N K).symm
  have hdet : Tendsto (fun K => (truncHankel w x N K).det) atTop
      (𝓝 (Matrix.of fun i j : Fin N => Mo (i.val + j.val)).det) := by
    simp only [det_apply']
    refine tendsto_finset_sum _ fun σ _ => ?_
    refine Tendsto.const_mul _ (tendsto_finset_prod _ fun i _ => ?_)
    simp only [truncHankel, of_apply]
    exact (hMo _).tendsto_sum_nat
  have hdet' : Tendsto (fun K => ∑ f ∈ box N K, g f) atTop
      (𝓝 (Matrix.of fun i j : Fin N => Mo (i.val + j.val)).det) := by
    simpa only [hpartial] using hdet
  have hmonoK : Monotone (fun K => ∑ f ∈ box N K, g f) := fun K K' h =>
    sum_le_sum_of_subset_of_nonneg (hTmono h) (fun f _ _ => hg0 f)
  have hsum : Summable g := by
    refine summable_of_sum_le (c := (Matrix.of fun i j : Fin N => Mo (i.val + j.val)).det)
      (fun f => hg0 f) fun t => ?_
    obtain ⟨K, hK⟩ := (hTtend.eventually (eventually_ge_atTop t)).exists
    exact (sum_le_sum_of_subset_of_nonneg hK fun f _ _ => hg0 f).trans
      (hmonoK.ge_of_tendsto hdet' K)
  have hlim : Tendsto (fun K => ∑ f ∈ box N K, g f) atTop (𝓝 (∑' f, g f)) :=
    hsum.hasSum.comp hTtend
  have heq : ∑' f, g f = (Matrix.of fun i j : Fin N => Mo (i.val + j.val)).det :=
    tendsto_nhds_unique hlim hdet'
  rw [← heq]
  exact hsum.hasSum

end Heine

/-! ### Cauchy's determinant -/

section Cauchy

/-- **Cauchy's determinant**:
`det (1/(1 - x_i y_j)) · ∏_{i,j} (1 - x_i y_j) = ∏_{i<j} (x_j - x_i) · ∏_{i<j} (y_j - y_i)`. -/
theorem cauchy_det : ∀ (n : ℕ) (x y : Fin n → ℝ), (∀ i j, 1 - x i * y j ≠ 0) →
    (Matrix.of fun i j => (1 - x i * y j)⁻¹).det * ∏ i, ∏ j, (1 - x i * y j) =
      (∏ i, ∏ j ∈ Ioi i, (x j - x i)) * ∏ i, ∏ j ∈ Ioi i, (y j - y i)
  | 0, x, y, _ => by simp
  | n + 1, x, y, h => by
    set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j => (1 - x i * y j)⁻¹
      with hA
    set c : Fin (n + 1) → ℝ := fun i => if i = 0 then 0 else (1 - x 0 * y 0) / (1 - x i * y 0)
      with hc
    have hc0 : c 0 = 0 := by simp [hc]
    set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j => A i j - c i * A 0 j
      with hB
    have hAB : A.det = B.det := by
      refine det_eq_of_forall_row_eq_smul_add_const c 0 hc0 fun i j => ?_
      simp only [hB, of_apply, hc0, zero_mul, sub_zero]
      ring
    have hB0 : ∀ i : Fin n, B i.succ 0 = 0 := by
      intro i
      have h1 := h i.succ 0
      have h2 := h 0 0
      have h1' : 1 - y 0 * x i.succ ≠ 0 := by rw [mul_comm]; exact h1
      have h2' : 1 - y 0 * x 0 ≠ 0 := by rw [mul_comm]; exact h2
      simp only [hB, hA, of_apply, hc, Fin.succ_ne_zero, if_false]
      field_simp
      ring
    have hdetB : B.det = B 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [det_succ_column_zero, Fin.sum_univ_succ]
      simp only [hB0, mul_zero, zero_mul, sum_const_zero, add_zero, Fin.val_zero, pow_zero,
        one_mul, Fin.succAbove_zero]
    set r : Fin n → ℝ := fun i => (x i.succ - x 0) / (1 - x i.succ * y 0) with hr
    set s : Fin n → ℝ := fun j => (y j.succ - y 0) / (1 - x 0 * y j.succ) with hs
    set A' : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (1 - x i.succ * y j.succ)⁻¹
      with hA'
    have hsub : B.submatrix Fin.succ Fin.succ = diagonal r * A' * diagonal s := by
      ext i j
      have h1 := h i.succ j.succ
      have h2 := h i.succ 0
      have h3 := h 0 j.succ
      have h4 := h 0 0
      have h1' : 1 - y j.succ * x i.succ ≠ 0 := by rw [mul_comm]; exact h1
      have h2' : 1 - y 0 * x i.succ ≠ 0 := by rw [mul_comm]; exact h2
      have h3' : 1 - y j.succ * x 0 ≠ 0 := by rw [mul_comm]; exact h3
      have h4' : 1 - y 0 * x 0 ≠ 0 := by rw [mul_comm]; exact h4
      simp only [submatrix_apply, hB, hA, of_apply, hc, Fin.succ_ne_zero, if_false,
        mul_diagonal, diagonal_mul, hA', hr, hs]
      field_simp
      ring
    have hB00 : B 0 0 = (1 - x 0 * y 0)⁻¹ := by simp [hB, hA, hc0]
    have ih := cauchy_det n (fun i => x i.succ) (fun j => y j.succ) (fun i j => h i.succ j.succ)
    have hdet : A.det = (1 - x 0 * y 0)⁻¹ * ((∏ i, r i) * A'.det * ∏ j, s j) := by
      rw [hAB, hdetB, hsub, det_mul, det_mul, det_diagonal, det_diagonal, hB00]
    have hPi : ∏ i : Fin (n + 1), ∏ j : Fin (n + 1), (1 - x i * y j) =
        (1 - x 0 * y 0) * (∏ j : Fin n, (1 - x 0 * y j.succ)) *
          ((∏ i : Fin n, (1 - x i.succ * y 0)) *
            ∏ i : Fin n, ∏ j : Fin n, (1 - x i.succ * y j.succ)) := by
      simp only [Fin.prod_univ_succ, prod_mul_distrib]
      ring
    have hVx : ∏ i : Fin (n + 1), ∏ j ∈ Ioi i, (x j - x i) =
        (∏ j : Fin n, (x j.succ - x 0)) * ∏ i : Fin n, ∏ j ∈ Ioi i, (x j.succ - x i.succ) := by
      rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
      simp only [Fin.prod_Ioi_succ]
    have hVy : ∏ i : Fin (n + 1), ∏ j ∈ Ioi i, (y j - y i) =
        (∏ j : Fin n, (y j.succ - y 0)) * ∏ i : Fin n, ∏ j ∈ Ioi i, (y j.succ - y i.succ) := by
      rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
      simp only [Fin.prod_Ioi_succ]
    have ha : 1 - x 0 * y 0 ≠ 0 := h 0 0
    have hPr : ∏ i : Fin n, (1 - x i.succ * y 0) ≠ 0 :=
      prod_ne_zero_iff.mpr fun i _ => h i.succ 0
    have hPs : ∏ j : Fin n, (1 - x 0 * y j.succ) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => h 0 j.succ
    have hrprod : ∏ i, r i = (∏ i : Fin n, (x i.succ - x 0)) / ∏ i : Fin n, (1 - x i.succ * y 0) := by
      rw [hr, prod_div_distrib]
    have hsprod : ∏ j, s j = (∏ j : Fin n, (y j.succ - y 0)) / ∏ j : Fin n, (1 - x 0 * y j.succ) := by
      rw [hs, prod_div_distrib]
    have ih' : A'.det * ∏ i : Fin n, ∏ j : Fin n, (1 - x i.succ * y j.succ) =
        (∏ i : Fin n, ∏ j ∈ Ioi i, (x j.succ - x i.succ)) *
          ∏ i : Fin n, ∏ j ∈ Ioi i, (y j.succ - y i.succ) := ih
    change A.det * _ = _
    rw [hdet, hPi, hVx, hVy, hrprod, hsprod]
    set a := 1 - x 0 * y 0 with ha_def
    set Nr := ∏ i : Fin n, (x i.succ - x 0) with hNr
    set Ns := ∏ j : Fin n, (y j.succ - y 0) with hNs
    set Pr := ∏ i : Fin n, (1 - x i.succ * y 0) with hPr_def
    set Ps := ∏ j : Fin n, (1 - x 0 * y j.succ) with hPs_def
    set Pij := ∏ i : Fin n, ∏ j : Fin n, (1 - x i.succ * y j.succ) with hPij
    set Vx := ∏ i : Fin n, ∏ j ∈ Ioi i, (x j.succ - x i.succ) with hVx_def
    set Vy := ∏ i : Fin n, ∏ j ∈ Ioi i, (y j.succ - y i.succ) with hVy_def
    calc a⁻¹ * (Nr / Pr * A'.det * (Ns / Ps)) * (a * Ps * (Pr * Pij))
        = Nr * Ns * (A'.det * Pij) * (a⁻¹ * a) * (Pr⁻¹ * Pr) * (Ps⁻¹ * Ps) := by ring
      _ = Nr * Vx * (Ns * Vy) := by
        rw [ih', inv_mul_cancel₀ ha, inv_mul_cancel₀ hPr, inv_mul_cancel₀ hPs]
        ring

end Cauchy

/-! ### The products `E_N` and `𝓜(q)` -/

section Products

open ErdosProblems.Erdos1049.PaperR10 (qPochhammerFinite qPochhammerInfinity)

variable {q : ℝ}

/-- `E_N = ∏_{j<N} (q;q)_j / (q;q)_∞`. -/
def eProd (q : ℝ) (N : ℕ) : ℝ :=
  ∏ j ∈ range N, qPochhammerFinite q q j / qPochhammerInfinity q q

/-- `𝓜(q) = ∏_{d ≥ 1} (1 - q^d)^{-d}`. -/
def gramM (q : ℝ) : ℝ := ∏' d : ℕ, ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹

/-- `u_d = -log (1 - q^{d+1})`. -/
def uLog (q : ℝ) (d : ℕ) : ℝ := -Real.log (1 - q ^ (d + 1))

lemma one_sub_pow_succ_pos (hq0 : 0 ≤ q) (hq1 : q < 1) (d : ℕ) : 0 < 1 - q ^ (d + 1) := by
  have : q ^ (d + 1) < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  linarith

lemma uLog_nonneg (hq0 : 0 ≤ q) (hq1 : q < 1) (d : ℕ) : 0 ≤ uLog q d := by
  unfold uLog
  have h1 := one_sub_pow_succ_pos hq0 hq1 d
  have h2 : 1 - q ^ (d + 1) ≤ 1 := by
    have := pow_nonneg hq0 (d + 1)
    linarith
  have := Real.log_nonpos h1.le h2
  linarith

lemma uLog_le (hq0 : 0 ≤ q) (hq1 : q < 1) (d : ℕ) : uLog q d ≤ q ^ (d + 1) / (1 - q) := by
  unfold uLog
  have hle : q ^ (d + 1) ≤ q := pow_le_of_le_one hq0 hq1.le (Nat.succ_ne_zero d)
  have h := PaperR10.abs_log_one_sub_le (pow_nonneg hq0 (d + 1)) hle hq1
  have := neg_le_abs (Real.log (1 - q ^ (d + 1)))
  linarith

lemma uLog_eq (q : ℝ) (k : ℕ) : uLog q k = -Real.log (1 - q * q ^ k) := by
  unfold uLog
  rw [pow_succ']

lemma summable_uLog (hq0 : 0 ≤ q) (hq1 : q < 1) : Summable (uLog q) :=
  (PaperR10.summable_log_qPochhammer hq0 hq1 hq0 hq1).neg.congr fun k => (uLog_eq q k).symm

lemma summable_weighted_uLog (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun d : ℕ => ((d : ℝ) + 1) * uLog q d) := by
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ 1 * q ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  have hg' : Summable (fun d : ℕ => ((d : ℝ) + 1) * q ^ (d + 1) / (1 - q)) := by
    have := ((summable_nat_add_iff 1).mpr hg).div_const (1 - q)
    refine this.congr fun d => ?_
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun d => mul_nonneg (by positivity) (uLog_nonneg hq0 hq1 d))
    (fun d => ?_) hg'
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (uLog_le hq0 hq1 d) (by positivity)

lemma log_P (q : ℝ) : Real.log (qPochhammerInfinity q q) = -∑' k, uLog q k := by
  unfold qPochhammerInfinity
  rw [Real.log_exp, ← tsum_neg]
  exact tsum_congr fun k => by rw [uLog_eq, neg_neg]

lemma log_qPochhammerFinite (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    Real.log (qPochhammerFinite q q j) = -∑ k ∈ range j, uLog q k := by
  rw [← PaperR10.exp_sum_log_qPochhammer hq0 hq1 hq0 hq1.le j, Real.log_exp, ← sum_neg_distrib]
  exact sum_congr rfl fun k _ => by rw [uLog_eq, neg_neg]

lemma qPochhammerFinite_q_pos (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    0 < qPochhammerFinite q q j :=
  PaperR10.qPochhammerFinite_pos hq0 hq1 hq0 hq1.le j

lemma log_eps (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    Real.log (qPochhammerFinite q q j / qPochhammerInfinity q q) = ∑' k, uLog q (k + j) := by
  rw [Real.log_div (qPochhammerFinite_q_pos hq0 hq1 j).ne'
      (PaperR10.qPochhammerInfinity_pos q q).ne', log_qPochhammerFinite hq0 hq1,
    log_P, ← (summable_uLog hq0 hq1).sum_add_tsum_nat_add j]
  ring

lemma eProd_eq_exp (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    eProd q N = Real.exp (∑ j ∈ range N, ∑' k, uLog q (k + j)) := by
  rw [Real.exp_sum]
  unfold eProd
  refine prod_congr rfl fun j _ => ?_
  rw [← log_eps hq0 hq1 j, Real.exp_log]
  exact div_pos (qPochhammerFinite_q_pos hq0 hq1 j) (PaperR10.qPochhammerInfinity_pos q q)

lemma eProd_pos (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) : 0 < eProd q N := by
  rw [eProd_eq_exp hq0 hq1]
  exact Real.exp_pos _

lemma hasProd_gramM (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasProd (fun d : ℕ => ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹)
      (Real.exp (∑' d : ℕ, ((d : ℝ) + 1) * uLog q d)) := by
  refine Real.hasProd_of_hasSum_log (fun d => ?_) ?_
  · have h1 := one_sub_pow_succ_pos hq0 hq1 d
    positivity
  · convert (summable_weighted_uLog hq0 hq1).hasSum using 1
    funext d
    rw [Real.log_inv, Real.log_pow, uLog]
    push_cast
    ring

lemma gramM_eq (hq0 : 0 ≤ q) (hq1 : q < 1) :
    gramM q = Real.exp (∑' d : ℕ, ((d : ℝ) + 1) * uLog q d) :=
  (hasProd_gramM hq0 hq1).tprod_eq

lemma gramM_pos (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < gramM q := by
  rw [gramM_eq hq0 hq1]
  exact Real.exp_pos _

lemma tsum_shift_eq_ite {u : ℕ → ℝ} (hu0 : ∀ d, 0 ≤ u d) (hu : Summable u) (j : ℕ) :
    ∑' k, u (k + j) = ∑' d, if j ≤ d then u d else 0 := by
  have hs : Summable (fun d => if j ≤ d then u d else 0) := by
    refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hu
    · split_ifs
      · exact hu0 d
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hu0 d
  rw [← hs.sum_add_tsum_nat_add j]
  have h1 : ∑ i ∈ range j, (if j ≤ i then u i else 0) = 0 :=
    sum_eq_zero fun i hi => by
      rw [mem_range] at hi
      rw [if_neg (by omega)]
  rw [h1, zero_add]
  exact tsum_congr fun k => by rw [if_pos (Nat.le_add_left j k)]

lemma card_filter_le_range (N d : ℕ) :
    ((range N).filter (fun j => j ≤ d)).card ≤ d + 1 := by
  calc ((range N).filter (fun j => j ≤ d)).card ≤ (range (d + 1)).card := by
        refine card_le_card fun j hj => ?_
        simp only [mem_filter, mem_range] at hj ⊢
        omega
    _ = d + 1 := card_range _

lemma card_filter_range_of_le {N d : ℕ} (h : d + 1 ≤ N) :
    ((range N).filter (fun j => j ≤ d)).card = d + 1 := by
  have : (range N).filter (fun j => j ≤ d) = range (d + 1) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [this, card_range]

theorem tendsto_eProd (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (eProd q) atTop (𝓝 (gramM q)) := by
  have hu0 := uLog_nonneg hq0 hq1
  have hu := summable_uLog hq0 hq1
  have hrw : ∀ N, ∑ j ∈ range N, ∑' k, uLog q (k + j) =
      ∑' d, (((range N).filter (fun j => j ≤ d)).card : ℝ) * uLog q d := by
    intro N
    have hsum : ∀ j ∈ range N, Summable (fun d => if j ≤ d then uLog q d else 0) := by
      intro j _
      refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hu
      · split_ifs
        · exact hu0 d
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · exact hu0 d
    simp_rw [tsum_shift_eq_ite hu0 hu]
    rw [← Summable.tsum_finsetSum hsum]
    refine tsum_congr fun d => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hfun : eProd q = fun N => Real.exp
      (∑' d, (((range N).filter (fun j => j ≤ d)).card : ℝ) * uLog q d) := by
    funext N
    rw [eProd_eq_exp hq0 hq1, hrw]
  rw [hfun, gramM_eq hq0 hq1]
  refine (Real.continuous_exp.tendsto _).comp ?_
  refine tendsto_tsum_of_dominated_convergence (bound := fun d => ((d : ℝ) + 1) * uLog q d)
    (summable_weighted_uLog hq0 hq1) (fun d => ?_) ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (d + 1)] with N hN
    rw [card_filter_range_of_le hN]
    push_cast
    ring
  · refine Eventually.of_forall fun N d => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (hu0 d))]
    refine mul_le_mul_of_nonneg_right ?_ (hu0 d)
    have := card_filter_le_range N d
    exact_mod_cast this

end Products

/-! ### Partitions as the index of Heine's expansion -/

section Partitions

variable {N : ℕ}

/-- `κ_N μ : i ↦ i + μ_{N-1-i}`: the strictly increasing tuple of the partition `μ`. -/
def kappa (N : ℕ) (μ : ℕ → ℕ) : Fin N → ℕ := fun i => (i : ℕ) + μ (N - 1 - (i : ℕ))

/-- The inverse of `kappa`: `j ↦ f_{N-1-j} - (N-1-j)` for `j < N`, and `0` beyond. -/
def iota (N : ℕ) (f : Fin N → ℕ) : ℕ → ℕ := fun j =>
  if h : j < N then f ⟨N - 1 - j, by omega⟩ - (N - 1 - j) else 0

lemma kappa_strictMono {μ : ℕ → ℕ} (hμ : Antitone μ) : StrictMono (kappa N μ) := by
  intro i i' hii'
  have h1 : (i : ℕ) < i' := hii'
  have h2 : μ (N - 1 - (i : ℕ)) ≤ μ (N - 1 - (i' : ℕ)) := hμ (by omega)
  simp only [kappa]
  omega

lemma strictMono_add_le {f : Fin N → ℕ} (hf : StrictMono f) :
    ∀ (d : ℕ) (i i' : Fin N), (i' : ℕ) = i + d → f i + d ≤ f i' := by
  intro d
  induction d with
  | zero =>
    intro i i' h
    have : i' = i := Fin.ext (by omega)
    subst this
    simp
  | succ d ih =>
    intro i i' h
    have hlt : (i : ℕ) + d < N := by
      have := i'.isLt
      omega
    have h1 := ih i ⟨(i : ℕ) + d, hlt⟩ rfl
    have h2 : f ⟨(i : ℕ) + d, hlt⟩ < f i' := hf (by rw [Fin.lt_def]; simp only; omega)
    omega

lemma val_le_apply {f : Fin N → ℕ} (hf : StrictMono f) (i : Fin N) : (i : ℕ) ≤ f i := by
  have h := strictMono_add_le hf i ⟨0, by have := i.isLt; omega⟩ i (by simp)
  omega

lemma apply_sub_mono {f : Fin N → ℕ} (hf : StrictMono f) {i i' : Fin N} (h : i ≤ i') :
    f i - i ≤ f i' - i' := by
  have hle : (i : ℕ) ≤ i' := h
  have h1 := strictMono_add_le hf ((i' : ℕ) - i) i i' (by omega)
  have h2 := val_le_apply hf i
  omega

lemma iota_antitone {f : Fin N → ℕ} (hf : StrictMono f) : Antitone (iota N f) := by
  intro j j' hjj'
  simp only [iota]
  by_cases hj' : j' < N
  · have hj : j < N := lt_of_le_of_lt hjj' hj'
    rw [dif_pos hj', dif_pos hj]
    exact apply_sub_mono hf (by rw [Fin.le_def]; simp only; omega)
  · rw [dif_neg hj']
    exact Nat.zero_le _

lemma iota_self (f : Fin N → ℕ) : iota N f N = 0 := by
  simp [iota]

lemma iota_kappa {μ : ℕ → ℕ} (hμ : Antitone μ) (h0 : μ N = 0) : iota N (kappa N μ) = μ := by
  funext j
  simp only [iota, kappa]
  split_ifs with hj
  · have e : N - 1 - (N - 1 - j) = j := by omega
    simp only [e]
    omega
  · have : μ j ≤ μ N := hμ (by omega)
    omega

lemma kappa_iota {f : Fin N → ℕ} (hf : StrictMono f) : kappa N (iota N f) = f := by
  funext i
  have hi := i.isLt
  simp only [kappa, iota]
  rw [dif_pos (by omega : N - 1 - (i : ℕ) < N)]
  have e : (⟨N - 1 - (N - 1 - (i : ℕ)), by omega⟩ : Fin N) = i := Fin.ext (by simp only; omega)
  rw [e]
  have := val_le_apply hf i
  omega

/-- Partitions with at most `N` parts correspond to strictly increasing `N`-tuples. -/
def partEquiv (N : ℕ) :
    {μ : ℕ → ℕ | Antitone μ ∧ μ N = 0} ≃ {f : Fin N → ℕ | StrictMono f} where
  toFun μ := ⟨kappa N μ.1, kappa_strictMono μ.2.1⟩
  invFun f := ⟨iota N f.1, iota_antitone f.2, iota_self f.1⟩
  left_inv μ := Subtype.ext (iota_kappa μ.2.1 μ.2.2)
  right_inv f := Subtype.ext (kappa_iota f.2)

lemma hasSum_part (N : ℕ) (Φ : (Fin N → ℕ) → ℝ) {D : ℝ}
    (h : HasSum (fun f : Fin N → ℕ => if StrictMono f then Φ f else 0) D) :
    HasSum (fun μ : ℕ → ℕ => if Antitone μ ∧ μ N = 0 then Φ (kappa N μ) else 0) D := by
  have h1 : HasSum (Set.indicator {f : Fin N → ℕ | StrictMono f} Φ) D := by
    convert h using 1
    funext f
    simp [Set.indicator_apply]
  rw [← hasSum_subtype_iff_indicator] at h1
  have h2 := (partEquiv N).hasSum_iff.mpr h1
  have h3 : HasSum (Set.indicator {μ : ℕ → ℕ | Antitone μ ∧ μ N = 0}
      (fun μ => Φ (kappa N μ))) D := by
    rw [← hasSum_subtype_iff_indicator]
    exact h2
  convert h3 using 1
  funext μ
  simp [Set.indicator_apply]

end Partitions

/-! ### Elementary product identities -/

section ProdIdentities

variable {q : ℝ}

lemma prod_fin_reflect (N : ℕ) (G : ℕ → ℝ) :
    ∏ i : Fin N, G (N - 1 - (i : ℕ)) = ∏ j ∈ range N, G j := by
  rw [Fin.prod_univ_eq_prod_range (fun i => G (N - 1 - i)) N, prod_range_reflect]

lemma prod_range_trunc {G : ℕ → ℝ} {L M : ℕ} (hLM : L ≤ M) (h1 : ∀ j, L ≤ j → G j = 1) :
    ∏ j ∈ range M, G j = ∏ j ∈ range L, G j := by
  rw [← prod_range_mul_prod_Ico _ hLM, prod_eq_one (fun j hj => h1 j (mem_Ico.mp hj).1), mul_one]

lemma prod_Iio_fin {N : ℕ} (j : Fin N) (g : ℕ → ℝ) :
    ∏ i ∈ Iio j, g i = ∏ m ∈ range j, g m := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, prod_map]
  rfl

lemma prod_range_one_sub_pow_sub (q : ℝ) (n : ℕ) :
    ∏ m ∈ range n, (1 - q ^ (n - m)) = qPochhammerFinite q q n := by
  unfold PaperR10.qPochhammerFinite
  rw [← prod_range_reflect (fun m => 1 - q * q ^ m) n]
  refine prod_congr rfl fun m hm => ?_
  rw [mem_range] at hm
  show 1 - q ^ (n - m) = 1 - q * q ^ (n - 1 - m)
  rw [← pow_succ']
  congr 2
  omega

lemma prod_range_pow_sub_sq (q : ℝ) (n : ℕ) :
    ∏ m ∈ range n, (q ^ n - q ^ m) ^ 2 = q ^ (n * (n - 1)) * qPochhammerFinite q q n ^ 2 := by
  have h1 : ∀ m ∈ range n, (q ^ n - q ^ m) ^ 2 = (q ^ m) ^ 2 * (1 - q ^ (n - m)) ^ 2 := by
    intro m hm
    rw [mem_range] at hm
    have : q ^ n = q ^ m * q ^ (n - m) := by
      rw [← pow_add]
      congr 1
      omega
    rw [this]
    ring
  rw [prod_congr rfl h1, prod_mul_distrib, prod_pow (range n) 2 (fun m => q ^ m),
    prod_pow_eq_pow_sum, ← pow_mul, sum_range_id_mul_two, prod_pow, prod_range_one_sub_pow_sub]

lemma add_mul_sub_one (n : ℕ) : n + n * (n - 1) = n ^ 2 := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [Nat.add_sub_cancel]
    ring

lemma vdet_pow_sq (q : ℝ) {N : ℕ} (f : Fin N → ℕ) :
    vdet (fun k => q ^ k) f ^ 2 = ∏ i, ∏ j ∈ Ioi i, (q ^ f j - q ^ f i) ^ 2 := by
  rw [vdet, det_vandermonde, ← prod_pow]
  exact prod_congr rfl fun i _ => by rw [← prod_pow]

lemma prod_Ioi_eq_prod_Iio {N : ℕ} (g : Fin N → Fin N → ℝ) :
    ∏ i, ∏ j ∈ Ioi i, g i j = ∏ j, ∏ i ∈ Iio j, g i j :=
  prod_comm' (by intro i j; simp [mem_Ioi, mem_Iio])

/-- The base value `Φ(0) = q^{B_N} P^{2N} E_N^2`. -/
lemma heineTerm_base (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    heineTerm (fun k => q ^ k) (fun k => q ^ k) (fun i : Fin N => (i : ℕ)) =
      q ^ (∑ j ∈ range N, j ^ 2) * qPochhammerInfinity q q ^ (2 * N) * eProd q N ^ 2 := by
  unfold heineTerm
  rw [vdet_pow_sq, prod_Ioi_eq_prod_Iio, ← prod_mul_distrib]
  have hj : ∀ j : Fin N, q ^ (j : ℕ) * ∏ i ∈ Iio j, (q ^ (j : ℕ) - q ^ (i : ℕ)) ^ 2 =
      q ^ ((j : ℕ) ^ 2) * qPochhammerFinite q q j ^ 2 := by
    intro j
    have e := prod_Iio_fin j (fun m => (q ^ (j : ℕ) - q ^ m) ^ 2)
    simp only at e
    rw [e, prod_range_pow_sub_sq, ← mul_assoc, ← pow_add, add_mul_sub_one]
  rw [prod_congr rfl fun j _ => hj j,
    Fin.prod_univ_eq_prod_range (fun j => q ^ (j ^ 2) * qPochhammerFinite q q j ^ 2) N,
    prod_mul_distrib, prod_pow_eq_pow_sum, mul_assoc]
  congr 1
  have hP := PaperR10.qPochhammerInfinity_pos q q
  unfold eProd
  rw [← prod_pow, pow_mul, ← card_range N, ← prod_const, card_range, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  field_simp

/-- Cauchy's determinant at `x_i = q^i`, `y_j = q^{j+1}`. -/
lemma cauchy_unit (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    (Matrix.of fun i j : Fin N => (1 - q ^ ((i : ℕ) + (j : ℕ) + 1))⁻¹).det *
      ∏ i : Fin N, ∏ j : Fin N, (1 - q ^ ((i : ℕ) + (j : ℕ) + 1)) =
    heineTerm (fun k => q ^ k) (fun k => q ^ k) (fun i : Fin N => (i : ℕ)) := by
  have hne : ∀ i j : Fin N, 1 - q ^ (i : ℕ) * q ^ ((j : ℕ) + 1) ≠ 0 := by
    intro i j
    rw [← pow_add, ← add_assoc]
    exact (one_sub_pow_succ_pos hq0.le hq1 _).ne'
  have h := cauchy_det N (fun i => q ^ (i : ℕ)) (fun j => q ^ ((j : ℕ) + 1)) hne
  have e1 : ∀ i j : Fin N, q ^ (i : ℕ) * q ^ ((j : ℕ) + 1) = q ^ ((i : ℕ) + (j : ℕ) + 1) := by
    intro i j
    rw [← pow_add, add_assoc]
  simp only [e1] at h
  rw [h]
  unfold heineTerm vdet
  rw [det_vandermonde]
  have hVy : ∏ i : Fin N, ∏ j ∈ Ioi i, (q ^ ((j : ℕ) + 1) - q ^ ((i : ℕ) + 1)) =
      (∏ i : Fin N, q ^ (i : ℕ)) * ∏ i : Fin N, ∏ j ∈ Ioi i, (q ^ (j : ℕ) - q ^ (i : ℕ)) := by
    have : ∀ i : Fin N, ∏ j ∈ Ioi i, (q ^ ((j : ℕ) + 1) - q ^ ((i : ℕ) + 1)) =
        q ^ (N - 1 - (i : ℕ)) * ∏ j ∈ Ioi i, (q ^ (j : ℕ) - q ^ (i : ℕ)) := by
      intro i
      rw [← Fin.card_Ioi, ← prod_const, ← prod_mul_distrib]
      exact prod_congr rfl fun j _ => by ring
    rw [prod_congr rfl fun i _ => this i, prod_mul_distrib]
    congr 1
    rw [prod_fin_reflect N (fun m => q ^ m), Fin.prod_univ_eq_prod_range (fun m => q ^ m) N]
  rw [hVy]
  ring

lemma prod_unit_mul_eProd_sq (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    (∏ i : Fin N, ∏ j : Fin N, (1 - q ^ ((i : ℕ) + (j : ℕ) + 1))) * eProd q N ^ 2 =
      eProd q (2 * N) := by
  have hinner : ∀ i : ℕ, qPochhammerFinite q q i * ∏ j : Fin N, (1 - q ^ (i + (j : ℕ) + 1)) =
      qPochhammerFinite q q (N + i) := by
    intro i
    rw [Fin.prod_univ_eq_prod_range (fun j => 1 - q ^ (i + j + 1)) N]
    unfold PaperR10.qPochhammerFinite
    rw [add_comm N i, prod_range_add]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    rw [← pow_succ']
  have houter : (∏ i ∈ range N, qPochhammerFinite q q i) *
      ∏ i : Fin N, ∏ j : Fin N, (1 - q ^ ((i : ℕ) + (j : ℕ) + 1)) =
        ∏ i ∈ range N, qPochhammerFinite q q (N + i) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ∏ j : Fin N, (1 - q ^ (i + (j : ℕ) + 1))) N,
      ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => hinner i
  have h2N : ∏ i ∈ range (2 * N), qPochhammerFinite q q i =
      (∏ i ∈ range N, qPochhammerFinite q q i) * ∏ i ∈ range N, qPochhammerFinite q q (N + i) := by
    rw [two_mul, prod_range_add]
  have hE : ∀ M, eProd q M =
      (∏ i ∈ range M, qPochhammerFinite q q i) / qPochhammerInfinity q q ^ M := by
    intro M
    unfold eProd
    rw [prod_div_distrib, prod_const, card_range]
  rw [hE, hE, h2N, ← houter]
  have hP := PaperR10.qPochhammerInfinity_pos q q
  have hQpos : 0 < ∏ i ∈ range N, qPochhammerFinite q q i :=
    prod_pos fun i _ => qPochhammerFinite_q_pos hq0.le hq1 i
  field_simp
  ring

end ProdIdentities

/-! ### The two bounds on a normalised Heine summand -/

section Bounds

variable {q : ℝ} {N : ℕ}

/-- `β_j(u) = q^{(2j+1)u}`, multiplied by `P^{-2}` when `u ≠ 0`. -/
def betaB (q : ℝ) (j u : ℕ) : ℝ :=
  q ^ ((2 * j + 1) * u) * (if u = 0 then 1 else ((qPochhammerInfinity q q) ^ 2)⁻¹)

/-- `α(u) = C (1+u)^n`, and `α(0) = 1`. -/
def alphaB (C : ℝ) (n u : ℕ) : ℝ := if u = 0 then 1 else C * (1 + (u : ℝ)) ^ n

/-- `θ_j(u) = β_j(u) α(u)`. -/
def thetaB (q C : ℝ) (n j u : ℕ) : ℝ := betaB q j u * alphaB C n u

lemma betaB_zero (q : ℝ) (j : ℕ) : betaB q j 0 = 1 := by simp [betaB]

lemma alphaB_zero (C : ℝ) (n : ℕ) : alphaB C n 0 = 1 := by simp [alphaB]

lemma thetaB_zero (q C : ℝ) (n j : ℕ) : thetaB q C n j 0 = 1 := by
  simp [thetaB, betaB_zero, alphaB_zero]

lemma betaB_nonneg (hq0 : 0 ≤ q) (j u : ℕ) : 0 ≤ betaB q j u := by
  unfold betaB
  have := PaperR10.qPochhammerInfinity_pos q q
  split_ifs <;> positivity

lemma one_le_alphaB {C : ℝ} (hC : 1 ≤ C) (n u : ℕ) : 1 ≤ alphaB C n u := by
  unfold alphaB
  split_ifs
  · exact le_rfl
  · have h1 : (1 : ℝ) ≤ (1 + (u : ℝ)) ^ n := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) u; linarith)
    nlinarith

lemma thetaB_nonneg (hq0 : 0 ≤ q) {C : ℝ} (hC : 1 ≤ C) (n j u : ℕ) : 0 ≤ thetaB q C n j u :=
  mul_nonneg (betaB_nonneg hq0 j u) (by linarith [one_le_alphaB hC n u])

lemma pair_bound (hq0 : 0 < q) (hq1 : q < 1) {i j a b : ℕ} (hij : i < j) (hab : a ≤ b) :
    (q ^ (j + b) - q ^ (i + a)) ^ 2 ≤
      (q ^ j - q ^ i) ^ 2 * q ^ (2 * a) *
        (if b = 0 then 1 else ((1 - q ^ (j - i)) ^ 2)⁻¹) := by
  split_ifs with hb
  · have ha : a = 0 := by omega
    subst ha
    subst hb
    simp
  · have h1 : q ^ (j + b) ≤ q ^ (i + a) := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    have h2 : 0 ≤ q ^ (j + b) := pow_nonneg hq0.le _
    have hsq : (q ^ (j + b) - q ^ (i + a)) ^ 2 ≤ (q ^ (i + a)) ^ 2 := by nlinarith
    have hji : q ^ j = q ^ i * q ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    have hd : 0 < 1 - q ^ (j - i) := by
      have : q ^ (j - i) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
      linarith
    have heq : (q ^ j - q ^ i) ^ 2 * q ^ (2 * a) * ((1 - q ^ (j - i)) ^ 2)⁻¹ =
        (q ^ (i + a)) ^ 2 := by
      rw [hji]
      field_simp
      ring
    linarith

/-- **First bound**: the unit-weight Heine summand at `κ_N μ`, relative to the base tuple. -/
lemma phi1_kappa_le (hq0 : 0 < q) (hq1 : q < 1) {μ : ℕ → ℕ} (hμ : Antitone μ) :
    heineTerm (fun k => q ^ k) (fun k => q ^ k) (kappa N μ) ≤
      heineTerm (fun k => q ^ k) (fun k => q ^ k) (fun i : Fin N => (i : ℕ)) *
        ∏ j ∈ range N, betaB q j (μ j) := by
  have hPpos : 0 < qPochhammerInfinity q q := PaperR10.qPochhammerInfinity_pos q q
  set lam : Fin N → ℕ := fun i => μ (N - 1 - (i : ℕ)) with hlam
  have hlam_mono : ∀ i j : Fin N, i ≤ j → lam i ≤ lam j := fun i j h => by
    have h' : (i : ℕ) ≤ j := h
    exact hμ (by omega)
  set vbf : Fin N → Fin N → ℝ := fun i j =>
    if lam j = 0 then 1 else ((1 - q ^ ((j : ℕ) - (i : ℕ))) ^ 2)⁻¹ with hvbf
  unfold heineTerm
  rw [vdet_pow_sq, vdet_pow_sq]
  have hpair : ∏ i, ∏ j ∈ Ioi i, (q ^ kappa N μ j - q ^ kappa N μ i) ^ 2 ≤
      ∏ i : Fin N, ∏ j ∈ Ioi i, ((q ^ (j : ℕ) - q ^ (i : ℕ)) ^ 2 * q ^ (2 * lam i) * vbf i j) := by
    refine prod_le_prod (fun i _ => prod_nonneg fun j _ => sq_nonneg _) fun i _ => ?_
    refine prod_le_prod (fun j _ => sq_nonneg _) fun j hj => ?_
    have hij' : i < j := mem_Ioi.mp hj
    have hij : (i : ℕ) < j := Fin.lt_def.mp hij'
    exact pair_bound hq0 hq1 hij (hlam_mono i j (le_of_lt hij'))
  have hsplit : ∏ i : Fin N, ∏ j ∈ Ioi i, ((q ^ (j : ℕ) - q ^ (i : ℕ)) ^ 2 * q ^ (2 * lam i) * vbf i j) =
      (∏ i : Fin N, ∏ j ∈ Ioi i, (q ^ (j : ℕ) - q ^ (i : ℕ)) ^ 2) *
        (∏ i : Fin N, q ^ (2 * lam i * (N - 1 - (i : ℕ)))) * ∏ i : Fin N, ∏ j ∈ Ioi i, vbf i j := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, Fin.card_Ioi, ← pow_mul]
  have hV : ∏ i : Fin N, ∏ j ∈ Ioi i, vbf i j ≤
      ∏ j : Fin N, (if lam j = 0 then 1 else ((qPochhammerInfinity q q) ^ 2)⁻¹) := by
    rw [prod_Ioi_eq_prod_Iio]
    refine prod_le_prod (fun j _ => prod_nonneg fun i _ => ?_) fun j _ => ?_
    · simp only [hvbf]
      split_ifs <;> positivity
    · simp only [hvbf]
      split_ifs with h0
      · simp
      · rw [prod_inv_distrib, prod_pow]
        have hprod : ∏ i ∈ Iio j, (1 - q ^ ((j : ℕ) - (i : ℕ))) = qPochhammerFinite q q j := by
          have e := prod_Iio_fin j (fun m => 1 - q ^ ((j : ℕ) - m))
          simp only at e
          rw [e, prod_range_one_sub_pow_sub]
        rw [hprod]
        have h1 := PaperR10.qPochhammerInfinity_le_finite hq0.le hq1 hq0.le hq1 j
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hPpos.le h1 2)
  have hQ : (∏ i : Fin N, q ^ lam i) * (∏ i : Fin N, q ^ (2 * lam i * (N - 1 - (i : ℕ)))) *
      ∏ j : Fin N, (if lam j = 0 then 1 else ((qPochhammerInfinity q q) ^ 2)⁻¹) =
        ∏ j ∈ range N, betaB q j (μ j) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib,
      ← prod_fin_reflect N (fun j => betaB q j (μ j))]
    refine prod_congr rfl fun i _ => ?_
    simp only [betaB, hlam]
    rw [← pow_add]
    have e : μ (N - 1 - (i : ℕ)) + 2 * μ (N - 1 - (i : ℕ)) * (N - 1 - (i : ℕ)) =
        (2 * (N - 1 - (i : ℕ)) + 1) * μ (N - 1 - (i : ℕ)) := by ring
    rw [e]
  have hkap : ∏ i : Fin N, q ^ kappa N μ i =
      (∏ i : Fin N, q ^ (i : ℕ)) * ∏ i : Fin N, q ^ lam i := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by rw [← pow_add]; rfl
  have hA0 : 0 ≤ ∏ i : Fin N, q ^ (i : ℕ) := prod_nonneg fun i _ => pow_nonneg hq0.le _
  have hB0 : 0 ≤ ∏ i : Fin N, ∏ j ∈ Ioi i, (q ^ (j : ℕ) - q ^ (i : ℕ)) ^ 2 :=
    prod_nonneg fun i _ => prod_nonneg fun j _ => sq_nonneg _
  have hX0 : 0 ≤ (∏ i : Fin N, q ^ lam i) * ∏ i : Fin N, q ^ (2 * lam i * (N - 1 - (i : ℕ))) :=
    mul_nonneg (prod_nonneg fun i _ => pow_nonneg hq0.le _)
      (prod_nonneg fun i _ => pow_nonneg hq0.le _)
  calc (∏ i, q ^ kappa N μ i) * ∏ i, ∏ j ∈ Ioi i, (q ^ kappa N μ j - q ^ kappa N μ i) ^ 2
      ≤ (∏ i, q ^ kappa N μ i) *
          ∏ i : Fin N, ∏ j ∈ Ioi i, ((q ^ (j : ℕ) - q ^ (i : ℕ)) ^ 2 * q ^ (2 * lam i) * vbf i j) :=
        mul_le_mul_of_nonneg_left hpair (prod_nonneg fun i _ => pow_nonneg hq0.le _)
    _ = ((∏ i : Fin N, q ^ (i : ℕ)) * ∏ i : Fin N, ∏ j ∈ Ioi i, (q ^ (j : ℕ) - q ^ (i : ℕ)) ^ 2) *
          (((∏ i : Fin N, q ^ lam i) * ∏ i : Fin N, q ^ (2 * lam i * (N - 1 - (i : ℕ)))) *
            ∏ i : Fin N, ∏ j ∈ Ioi i, vbf i j) := by
        rw [hsplit, hkap]
        ring
    _ ≤ ((∏ i : Fin N, q ^ (i : ℕ)) * ∏ i : Fin N, ∏ j ∈ Ioi i, (q ^ (j : ℕ) - q ^ (i : ℕ)) ^ 2) *
          (((∏ i : Fin N, q ^ lam i) * ∏ i : Fin N, q ^ (2 * lam i * (N - 1 - (i : ℕ)))) *
            ∏ j : Fin N, (if lam j = 0 then 1 else ((qPochhammerInfinity q q) ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hV hX0) (mul_nonneg hA0 hB0)
    _ = ((∏ i : Fin N, q ^ (i : ℕ)) * ∏ i : Fin N, ∏ j ∈ Ioi i, (q ^ (j : ℕ) - q ^ (i : ℕ)) ^ 2) *
          ∏ j ∈ range N, betaB q j (μ j) := by rw [hQ]

/-- The weight ratio `∏ a_{κ(i)} / ∏ a_i`, reindexed by the parts of `μ`. -/
lemma pi_kappa_eq (a : ℕ → ℝ) (μ : ℕ → ℕ) :
    (∏ i : Fin N, a (kappa N μ i)) / (∏ i : Fin N, a i) =
      ∏ j ∈ range N, a (N - 1 - j + μ j) / a (N - 1 - j) := by
  rw [← prod_div_distrib, ← prod_fin_reflect N (fun j => a (N - 1 - j + μ j) / a (N - 1 - j))]
  refine prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  have e : N - 1 - (N - 1 - (i : ℕ)) = i := by omega
  simp only [kappa, e]

/-- **Second bound**: the weight ratio. -/
lemma pi_kappa_le {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) {C : ℝ} {n : ℕ}
    (hbd : ∀ k h : ℕ, a (k + h) / a k ≤ C * (1 + (h : ℝ)) ^ n) (μ : ℕ → ℕ) :
    (∏ i : Fin N, a (kappa N μ i)) / (∏ i : Fin N, a i) ≤ ∏ j ∈ range N, alphaB C n (μ j) := by
  rw [← prod_div_distrib, ← prod_fin_reflect N (fun j => alphaB C n (μ j))]
  refine prod_le_prod (fun i _ => (div_pos (ha _) (ha _)).le) fun i _ => ?_
  simp only [kappa, alphaB]
  split_ifs with h
  · rw [h, add_zero, div_self (ha _).ne']
  · exact hbd i (μ (N - 1 - i))

lemma heineTerm_weight (a : ℕ → ℝ) (q : ℝ) (f : Fin N → ℕ) :
    heineTerm (fun k => a k * q ^ k) (fun k => q ^ k) f =
      (∏ i, a (f i)) * heineTerm (fun k => q ^ k) (fun k => q ^ k) f := by
  unfold heineTerm
  rw [prod_mul_distrib]
  ring

end Bounds

/-! ### The summable majorant over partitions -/

section Majorant

variable {q : ℝ}

/-- The majorant `∏_{j < ℓ(μ)} θ_j(μ_j)` on finitely supported antitone `μ`, zero elsewhere. -/
def majorant (q C : ℝ) (n : ℕ) (μ : ℕ → ℕ) : ℝ :=
  if h : Antitone μ ∧ ∃ L, μ L = 0 then ∏ j ∈ range (Nat.find h.2), thetaB q C n j (μ j) else 0

lemma majorant_nonneg (hq0 : 0 ≤ q) {C : ℝ} (hC : 1 ≤ C) (n : ℕ) (μ : ℕ → ℕ) :
    0 ≤ majorant q C n μ := by
  unfold majorant
  split_ifs
  · exact prod_nonneg fun j _ => thetaB_nonneg hq0 hC n j _
  · exact le_rfl

lemma zero_of_antitone {μ : ℕ → ℕ} (hμ : Antitone μ) {L : ℕ} (hL : μ L = 0) :
    ∀ j, L ≤ j → μ j = 0 := fun j hj => Nat.le_zero.mp (hL ▸ hμ hj)

lemma majorant_eq {C : ℝ} (n : ℕ) {μ : ℕ → ℕ} (hμ : Antitone μ) {M : ℕ} (hM : μ M = 0) :
    majorant q C n μ = ∏ j ∈ range M, thetaB q C n j (μ j) := by
  have hex : ∃ L, μ L = 0 := ⟨M, hM⟩
  unfold majorant
  rw [dif_pos ⟨hμ, hex⟩]
  have hle : Nat.find hex ≤ M := Nat.find_min' hex hM
  symm
  exact prod_range_trunc hle fun j hj => by
    rw [zero_of_antitone hμ (Nat.find_spec hex) j hj, thetaB_zero]

lemma summable_one_add_pow_mul_geometric (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    Summable (fun k : ℕ => (1 + (k : ℝ)) ^ n * q ^ k) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one n
    (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1 : ‖q‖ < 1)
  have h1 := ((summable_nat_add_iff 1).mpr h).mul_left q⁻¹
  refine h1.congr fun k => ?_
  push_cast
  field_simp
  ring

lemma summable_majorant (hq0 : 0 < q) (hq1 : q < 1) {C : ℝ} (hC : 1 ≤ C) (n : ℕ) :
    Summable (majorant q C n) := by
  have hPpos : 0 < qPochhammerInfinity q q := PaperR10.qPochhammerInfinity_pos q q
  have hg := summable_one_add_pow_mul_geometric hq0 hq1 n
  set Θ := ((qPochhammerInfinity q q) ^ 2)⁻¹ * C * ∑' u : ℕ, (1 + (u : ℝ)) ^ n * q ^ u with hΘ
  have hΘ0 : 0 ≤ Θ := by
    have : 0 ≤ ∑' u : ℕ, (1 + (u : ℝ)) ^ n * q ^ u := tsum_nonneg fun u => by positivity
    have hC0 : 0 ≤ C := by linarith
    positivity
  have hq2 : q ^ 2 < 1 := pow_lt_one₀ hq0.le hq1 two_ne_zero
  have hθterm : ∀ j u : ℕ, thetaB q C n j (u + 1) ≤
      ((qPochhammerInfinity q q) ^ 2)⁻¹ * C * ((1 + ((u + 1 : ℕ) : ℝ)) ^ n * q ^ (u + 1)) *
        (q ^ 2) ^ j := by
    intro j u
    simp only [thetaB, betaB, alphaB, Nat.succ_ne_zero, if_false]
    have hexp : q ^ ((2 * j + 1) * (u + 1)) ≤ q ^ (u + 1) * (q ^ 2) ^ j := by
      rw [← pow_mul, ← pow_add]
      exact pow_le_pow_of_le_one hq0.le hq1.le (by nlinarith)
    have hPi : 0 ≤ ((qPochhammerInfinity q q) ^ 2)⁻¹ := by positivity
    have hC0 : 0 ≤ C := by linarith
    have hpow : 0 ≤ (1 + ((u + 1 : ℕ) : ℝ)) ^ n := by positivity
    calc q ^ ((2 * j + 1) * (u + 1)) * ((qPochhammerInfinity q q) ^ 2)⁻¹ *
          (C * (1 + ((u + 1 : ℕ) : ℝ)) ^ n)
        ≤ (q ^ (u + 1) * (q ^ 2) ^ j) * ((qPochhammerInfinity q q) ^ 2)⁻¹ *
          (C * (1 + ((u + 1 : ℕ) : ℝ)) ^ n) := by gcongr
      _ = _ := by ring
  have hθsum : ∀ j U : ℕ, ∑ u ∈ range (U + 1), thetaB q C n j u ≤ 1 + Θ * (q ^ 2) ^ j := by
    intro j U
    rw [sum_range_succ', thetaB_zero]
    suffices hsuff : ∑ u ∈ range U, thetaB q C n j (u + 1) ≤ Θ * (q ^ 2) ^ j by linarith
    calc ∑ u ∈ range U, thetaB q C n j (u + 1)
        ≤ ∑ u ∈ range U, ((qPochhammerInfinity q q) ^ 2)⁻¹ * C *
            ((1 + ((u + 1 : ℕ) : ℝ)) ^ n * q ^ (u + 1)) * (q ^ 2) ^ j :=
          sum_le_sum fun u _ => hθterm j u
      _ = ((qPochhammerInfinity q q) ^ 2)⁻¹ * C *
            (∑ u ∈ range U, (1 + ((u + 1 : ℕ) : ℝ)) ^ n * q ^ (u + 1)) * (q ^ 2) ^ j := by
          rw [mul_sum, sum_mul]
      _ ≤ Θ * (q ^ 2) ^ j := by
          have hpart : ∑ u ∈ range U, (1 + ((u + 1 : ℕ) : ℝ)) ^ n * q ^ (u + 1) ≤
              ∑' u : ℕ, (1 + (u : ℝ)) ^ n * q ^ u := by
            have := (summable_nat_add_iff 1).mpr hg
            calc ∑ u ∈ range U, (1 + ((u + 1 : ℕ) : ℝ)) ^ n * q ^ (u + 1)
                ≤ ∑' u : ℕ, (1 + ((u + 1 : ℕ) : ℝ)) ^ n * q ^ (u + 1) :=
                  this.sum_le_tsum _ fun u _ => by positivity
              _ ≤ ∑' u : ℕ, (1 + (u : ℝ)) ^ n * q ^ u := by
                  rw [hg.tsum_eq_zero_add]
                  have : 0 ≤ (1 + ((0 : ℕ) : ℝ)) ^ n * q ^ 0 := by positivity
                  linarith
          have hC0 : 0 ≤ C := by linarith
          have hq2j : 0 ≤ (q ^ 2) ^ j := by positivity
          rw [hΘ]
          gcongr
  refine summable_of_sum_le (c := Real.exp (Θ / (1 - q ^ 2)))
    (fun μ => majorant_nonneg hq0.le hC n μ) fun F => ?_
  set good : (ℕ → ℕ) → Prop := fun μ => Antitone μ ∧ ∃ L, μ L = 0 with hgood
  set len : (ℕ → ℕ) → ℕ := fun μ => if h : ∃ L, μ L = 0 then Nat.find h else 0 with hlen
  set L0 := F.sup len with hL0
  set U := F.sup (fun μ => μ 0) with hU
  set F' := F.filter good with hF'
  have hF : ∑ μ ∈ F, majorant q C n μ = ∑ μ ∈ F', majorant q C n μ := by
    rw [hF', sum_filter]
    refine sum_congr rfl fun μ _ => ?_
    by_cases h : good μ
    · rw [if_pos h]
    · rw [if_neg h]
      unfold majorant
      rw [dif_neg h]
  have hzero : ∀ μ ∈ F', ∀ j, L0 ≤ j → μ j = 0 := by
    intro μ hμ j hj
    rw [hF', mem_filter] at hμ
    obtain ⟨hμF, hanti, hex⟩ := hμ
    have hlenμ : len μ = Nat.find hex := by simp only [hlen, dif_pos hex]
    have hle : len μ ≤ L0 := le_sup hμF
    exact zero_of_antitone hanti (Nat.find_spec hex) j (by rw [← hlenμ]; omega)
  have hbound : ∀ μ ∈ F', ∀ j, μ j ≤ U := by
    intro μ hμ j
    rw [hF', mem_filter] at hμ
    exact (hμ.2.1 (Nat.zero_le j)).trans (le_sup (f := fun μ => μ 0) hμ.1)
  have hmaj : ∀ μ ∈ F', majorant q C n μ = ∏ j : Fin L0, thetaB q C n j (μ j) := by
    intro μ hμ
    have hanti : Antitone μ := (mem_filter.mp hμ).2.1
    rw [majorant_eq n hanti (hzero μ hμ L0 le_rfl),
      Fin.prod_univ_eq_prod_range (fun j => thetaB q C n j (μ j)) L0]
  set ρ : (ℕ → ℕ) → (Fin L0 → ℕ) := fun μ j => μ j with hρ
  have hinj : Set.InjOn ρ F' := by
    intro μ hμ μ' hμ' h
    funext j
    by_cases hj : j < L0
    · have := congrFun h ⟨j, hj⟩
      simpa [hρ] using this
    · rw [hzero μ hμ j (by omega), hzero μ' hμ' j (by omega)]
  have hsub : F'.image ρ ⊆ box L0 (U + 1) := by
    intro v hv
    rw [mem_image] at hv
    obtain ⟨μ, hμ, rfl⟩ := hv
    rw [mem_box]
    intro j
    exact Nat.lt_succ_of_le (hbound μ hμ j)
  have hθ0 : ∀ j u, 0 ≤ thetaB q C n j u := fun j u => thetaB_nonneg hq0.le hC n j u
  calc ∑ μ ∈ F, majorant q C n μ
      = ∑ μ ∈ F', ∏ j : Fin L0, thetaB q C n j (ρ μ j) := by
        rw [hF]
        exact sum_congr rfl fun μ hμ => hmaj μ hμ
    _ = ∑ v ∈ F'.image ρ, ∏ j : Fin L0, thetaB q C n j (v j) :=
        (sum_image (f := fun v : Fin L0 → ℕ => ∏ j : Fin L0, thetaB q C n j (v j)) hinj).symm
    _ ≤ ∑ v ∈ box L0 (U + 1), ∏ j : Fin L0, thetaB q C n j (v j) :=
        sum_le_sum_of_subset_of_nonneg hsub fun v _ _ => prod_nonneg fun j _ => hθ0 _ _
    _ = ∏ j : Fin L0, ∑ u ∈ range (U + 1), thetaB q C n j u := by
        rw [box, prod_univ_sum]
    _ ≤ ∏ j : Fin L0, Real.exp (Θ * (q ^ 2) ^ (j : ℕ)) := by
        refine prod_le_prod (fun j _ => sum_nonneg fun u _ => hθ0 _ _) fun j _ => ?_
        refine (hθsum j U).trans ?_
        have := Real.add_one_le_exp (Θ * (q ^ 2) ^ (j : ℕ))
        linarith
    _ = Real.exp (∑ j : Fin L0, Θ * (q ^ 2) ^ (j : ℕ)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (Θ / (1 - q ^ 2)) := by
        rw [Real.exp_le_exp, Fin.sum_univ_eq_sum_range (fun j => Θ * (q ^ 2) ^ j) L0,
          ← mul_sum, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ hΘ0
        rw [← tsum_geometric_of_lt_one (by positivity) hq2]
        exact (summable_geometric_of_lt_one (by positivity) hq2).sum_le_tsum _
          fun j _ => by positivity

end Majorant

/-- The moment `M_m = ∑_{k ≥ 0} a_k q^{(m+1)k}`. -/
def geomMoment (q : ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ := ∑' k : ℕ, a k * q ^ ((m + 1) * k)

/-- The Hankel determinant `D_N = det (M_{i+j})_{0 ≤ i,j < N}`. -/
def geomHankelDet (q : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin N => geomMoment q a (i.val + j.val)).det

section Main

variable {q : ℝ}

/-- The Heine summand at the base tuple `(0, 1, …, N-1)` with unit weights. -/
def baseZ (q : ℝ) (N : ℕ) : ℝ :=
  heineTerm (fun k => q ^ k) (fun k => q ^ k) (fun i : Fin N => (i : ℕ))

lemma baseZ_pos (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) : 0 < baseZ q N := by
  rw [baseZ, heineTerm_base hq0 hq1]
  have := eProd_pos hq0.le hq1 N
  have := PaperR10.qPochhammerInfinity_pos q q
  positivity

lemma heineTerm_unit_nonneg (hq0 : 0 < q) {N : ℕ} (f : Fin N → ℕ) :
    0 ≤ heineTerm (fun k => q ^ k) (fun k => q ^ k) f :=
  mul_nonneg (prod_nonneg fun i _ => pow_nonneg hq0.le _) (sq_nonneg _)

/-- The unit-weight Hankel determinant, normalised by `baseZ`, tends to `𝓜(q)`. -/
lemma tendsto_unit_ratio (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun N : ℕ =>
      (Matrix.of fun i j : Fin N => (1 - q ^ ((i : ℕ) + (j : ℕ) + 1))⁻¹).det / baseZ q N)
      atTop (𝓝 (gramM q)) := by
  have hE := tendsto_eProd hq0.le hq1
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
  have h2 : Tendsto (fun N : ℕ => eProd q (2 * N)) atTop (𝓝 (gramM q)) := hE.comp h2N
  have hM := gramM_pos hq0.le hq1
  have hlim : Tendsto (fun N : ℕ => eProd q N ^ 2 / eProd q (2 * N)) atTop
      (𝓝 (gramM q ^ 2 / gramM q)) := (hE.pow 2).div h2 hM.ne'
  rw [show gramM q ^ 2 / gramM q = gramM q by field_simp] at hlim
  refine hlim.congr fun N => ?_
  have hc := cauchy_unit hq0 hq1 N
  have hp := prod_unit_mul_eProd_sq hq0 hq1 N
  have hZ := baseZ_pos hq0 hq1 N
  have hEN := eProd_pos hq0.le hq1 N
  have hE2N := eProd_pos hq0.le hq1 (2 * N)
  set Pi := ∏ i : Fin N, ∏ j : Fin N, (1 - q ^ ((i : ℕ) + (j : ℕ) + 1)) with hPi_def
  set D := (Matrix.of fun i j : Fin N => (1 - q ^ ((i : ℕ) + (j : ℕ) + 1))⁻¹).det with hD_def
  have hD : D ≠ 0 := by
    intro h
    rw [h, zero_mul] at hc
    rw [baseZ] at hZ
    linarith
  rw [baseZ, ← hc, ← hp, mul_comm Pi, div_mul_cancel_left₀ (pow_ne_zero 2 hEN.ne'),
    div_mul_cancel_left₀ hD]

/-- The normalised difference between the Heine summands of the weights `a` and of the unit
weights, indexed by partitions `μ`. -/
def Fterm (q : ℝ) (a : ℕ → ℝ) (N : ℕ) (μ : ℕ → ℕ) : ℝ :=
  if Antitone μ ∧ μ N = 0 then
    heineTerm (fun k => q ^ k) (fun k => q ^ k) (kappa N μ) / baseZ q N *
      ((∏ i : Fin N, a (kappa N μ i)) / (∏ i : Fin N, a i) - 1)
  else 0

lemma tendsto_Fterm (hq0 : 0 < q) (hq1 : q < 1) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (hlim : ∀ h : ℕ, Tendsto (fun k => a (k + h) / a k) atTop (𝓝 1)) (μ : ℕ → ℕ) :
    Tendsto (fun N => Fterm q a N μ) atTop (𝓝 0) := by
  by_cases hgood : Antitone μ ∧ ∃ L, μ L = 0
  · obtain ⟨hμ, L, hL⟩ := hgood
    have hz := zero_of_antitone hμ hL
    set c := ∏ j ∈ range L, betaB q j (μ j) with hc
    have hπ : Tendsto (fun N : ℕ => ∏ j ∈ range L, a (N - 1 - j + μ j) / a (N - 1 - j)) atTop
        (𝓝 1) := by
      rw [show (1 : ℝ) = ∏ j ∈ range L, (1 : ℝ) by simp]
      refine tendsto_finset_prod _ fun j _ => ?_
      refine ((hlim (μ j)).comp (tendsto_sub_atTop_nat (1 + j))).congr fun N => ?_
      simp only [Function.comp_apply, Nat.sub_sub]
    have hbnd : ∀ᶠ N in atTop, ‖Fterm q a N μ‖ ≤
        c * |∏ j ∈ range L, a (N - 1 - j + μ j) / a (N - 1 - j) - 1| := by
      filter_upwards [eventually_ge_atTop L] with N hN
      have hN0 : μ N = 0 := hz N hN
      have htr : ∏ j ∈ range N, a (N - 1 - j + μ j) / a (N - 1 - j) =
          ∏ j ∈ range L, a (N - 1 - j + μ j) / a (N - 1 - j) :=
        prod_range_trunc hN fun j hj => by rw [hz j hj, add_zero, div_self (ha _).ne']
      have htrb : ∏ j ∈ range N, betaB q j (μ j) = c :=
        prod_range_trunc hN fun j hj => by rw [hz j hj, betaB_zero]
      rw [Fterm, if_pos ⟨hμ, hN0⟩, pi_kappa_eq, htr, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have hZ := baseZ_pos hq0 hq1 N
      have hrho0 : 0 ≤ heineTerm (fun k => q ^ k) (fun k => q ^ k) (kappa N μ) / baseZ q N :=
        div_nonneg (heineTerm_unit_nonneg hq0 _) hZ.le
      rw [abs_of_nonneg hrho0, div_le_iff₀ hZ]
      calc heineTerm (fun k => q ^ k) (fun k => q ^ k) (kappa N μ)
          ≤ baseZ q N * ∏ j ∈ range N, betaB q j (μ j) := phi1_kappa_le hq0 hq1 hμ
        _ = c * baseZ q N := by rw [htrb]; ring
    refine squeeze_zero_norm' hbnd ?_
    have h0 : Tendsto (fun N : ℕ => c * |∏ j ∈ range L, a (N - 1 - j + μ j) / a (N - 1 - j) - 1|)
        atTop (𝓝 (c * |1 - 1|)) := ((hπ.sub_const 1).abs).const_mul c
    simpa using h0
  · refine tendsto_const_nhds.congr fun N => ?_
    rw [Fterm, if_neg]
    rintro ⟨hμ, hN⟩
    exact hgood ⟨hμ, N, hN⟩

lemma norm_Fterm_le (hq0 : 0 < q) (hq1 : q < 1) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) {C : ℝ}
    (hC : 1 ≤ C) {n : ℕ} (hbd : ∀ k h : ℕ, a (k + h) / a k ≤ C * (1 + (h : ℝ)) ^ n)
    (N : ℕ) (μ : ℕ → ℕ) :
    ‖Fterm q a N μ‖ ≤ majorant q C n μ := by
  by_cases hcond : Antitone μ ∧ μ N = 0
  · obtain ⟨hμ, hN0⟩ := hcond
    rw [Fterm, if_pos ⟨hμ, hN0⟩, majorant_eq n hμ hN0, Real.norm_eq_abs, abs_mul]
    have hZ := baseZ_pos hq0 hq1 N
    have hrho0 : 0 ≤ heineTerm (fun k => q ^ k) (fun k => q ^ k) (kappa N μ) / baseZ q N :=
      div_nonneg (heineTerm_unit_nonneg hq0 _) hZ.le
    have hrho : heineTerm (fun k => q ^ k) (fun k => q ^ k) (kappa N μ) / baseZ q N ≤
        ∏ j ∈ range N, betaB q j (μ j) := by
      rw [div_le_iff₀ hZ, mul_comm]
      exact phi1_kappa_le hq0 hq1 hμ
    have hpi0 : 0 ≤ (∏ i : Fin N, a (kappa N μ i)) / ∏ i : Fin N, a i :=
      div_nonneg (prod_nonneg fun i _ => (ha _).le) (prod_nonneg fun i _ => (ha _).le)
    have hpi := pi_kappa_le (N := N) ha hbd μ
    have hA1 : 1 ≤ ∏ j ∈ range N, alphaB C n (μ j) := by
      calc (1 : ℝ) = ∏ j ∈ range N, (1 : ℝ) := by simp
        _ ≤ ∏ j ∈ range N, alphaB C n (μ j) :=
          prod_le_prod (fun _ _ => zero_le_one) fun j _ => one_le_alphaB hC n _
    have habs : |(∏ i : Fin N, a (kappa N μ i)) / ∏ i : Fin N, a i - 1| ≤
        ∏ j ∈ range N, alphaB C n (μ j) := by
      rw [abs_le]
      constructor <;> linarith
    rw [abs_of_nonneg hrho0]
    calc heineTerm (fun k => q ^ k) (fun k => q ^ k) (kappa N μ) / baseZ q N *
          |(∏ i : Fin N, a (kappa N μ i)) / ∏ i : Fin N, a i - 1|
        ≤ (∏ j ∈ range N, betaB q j (μ j)) * ∏ j ∈ range N, alphaB C n (μ j) :=
          mul_le_mul hrho habs (abs_nonneg _) (prod_nonneg fun j _ => betaB_nonneg hq0.le j _)
      _ = ∏ j ∈ range N, thetaB q C n j (μ j) := by
          rw [← prod_mul_distrib]
          rfl
  · rw [Fterm, if_neg hcond, norm_zero]
    exact majorant_nonneg hq0.le hC n μ

/-- `long1049:thm:geometric-universality` (determinants of geometric moments).

Let `0 < q < 1` and let `a_k > 0` satisfy, for fixed constants `C` and `κ`,
`a_{k+h}/a_k → 1` (`k → ∞`) for each fixed `h ≥ 0`, and `a_{k+h}/a_k ≤ C (1+h)^κ` for all
`k, h ≥ 0`. Then
* `𝓜(q) = ∏_{d ≥ 1} (1 - q^d)^{-d}` converges (`HasProd`) to `gramM q`, which is positive;
* every moment `M_m = ∑_{k ≥ 0} a_k q^{(m+1)k}` converges;
* `D_N = det (M_{i+j})_{0 ≤ i,j < N}` (`geomHankelDet`) satisfies
  `D_N ∼ 𝓜(q)^3 q^{B_N} P^{2N} ∏_{k=0}^{N-1} a_k` as `N → ∞`: the ratio tends to `1`,
  with `B_N = ∑_{j<N} j^2` and `P = (q;q)_∞`. -/
theorem geometric_universality (hq0 : 0 < q) (hq1 : q < 1)
    {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) {C κ : ℝ}
    (hlim : ∀ h : ℕ, Tendsto (fun k => a (k + h) / a k) atTop (𝓝 1))
    (hbd : ∀ k h : ℕ, a (k + h) / a k ≤ C * (1 + (h : ℝ)) ^ κ) :
    HasProd (fun d : ℕ => ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹) (gramM q) ∧ 0 < gramM q ∧
    (∀ m : ℕ, Summable fun k => a k * q ^ ((m + 1) * k)) ∧
    Tendsto (fun N : ℕ => geomHankelDet q a N /
        (gramM q ^ 3 * q ^ (∑ j ∈ range N, j ^ 2) * qPochhammerInfinity q q ^ (2 * N) *
          ∏ k ∈ range N, a k))
      atTop (𝓝 1) := by
  have hMpos := gramM_pos hq0.le hq1
  have hMprod : HasProd (fun d : ℕ => ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹) (gramM q) := by
    rw [gramM_eq hq0.le hq1]
    exact hasProd_gramM hq0.le hq1
  have hC1 : 1 ≤ C := by
    have h := hbd 0 0
    rw [add_zero, div_self (ha 0).ne', Nat.cast_zero, add_zero, Real.one_rpow, mul_one] at h
    exact h
  set n : ℕ := ⌈max κ 0⌉₊ with hn
  have hbdn : ∀ k h : ℕ, a (k + h) / a k ≤ C * (1 + (h : ℝ)) ^ n := by
    intro k h
    refine (hbd k h).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    have h1 : (1 : ℝ) ≤ 1 + (h : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) h
      linarith
    calc (1 + (h : ℝ)) ^ κ ≤ (1 + (h : ℝ)) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 ((le_max_left κ 0).trans (Nat.le_ceil _))
      _ = (1 + (h : ℝ)) ^ n := Real.rpow_natCast _ _
  have hak : ∀ k, a k ≤ a 0 * C * (1 + (k : ℝ)) ^ n := by
    intro k
    have h := hbdn 0 k
    rw [zero_add, div_le_iff₀ (ha 0)] at h
    linarith
  have hpg := summable_one_add_pow_mul_geometric hq0 hq1 n
  have hmom : ∀ m : ℕ, Summable (fun k => a k * q ^ ((m + 1) * k)) := by
    intro m
    refine Summable.of_nonneg_of_le (fun k => (mul_pos (ha k) (pow_pos hq0 _)).le)
      (fun k => ?_) (hpg.mul_left (a 0 * C))
    have hqk : q ^ ((m + 1) * k) ≤ q ^ k :=
      pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_mul_of_pos_left k (Nat.succ_pos m))
    have ha0 := ha 0
    calc a k * q ^ ((m + 1) * k) ≤ (a 0 * C * (1 + (k : ℝ)) ^ n) * q ^ k :=
          mul_le_mul (hak k) hqk (pow_nonneg hq0.le _) (by positivity)
      _ = a 0 * C * ((1 + (k : ℝ)) ^ n * q ^ k) := by ring
  refine ⟨hMprod, hMpos, hmom, ?_⟩
  have hMo : ∀ m : ℕ, HasSum (fun k => (a k * q ^ k) * (q ^ k) ^ m) (geomMoment q a m) := by
    intro m
    have h := (hmom m).hasSum
    convert h using 1
    funext k
    rw [← pow_mul, mul_assoc, ← pow_add]
    congr 2
    ring
  have hM1 : ∀ m : ℕ, HasSum (fun k => q ^ k * (q ^ k) ^ m) (1 - q ^ (m + 1))⁻¹ := by
    intro m
    have h := hasSum_geometric_of_lt_one (pow_nonneg hq0.le (m + 1))
      (pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero m))
    convert h using 1
    funext k
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    ring
  have hDa : ∀ N, HasSum (fun μ : ℕ → ℕ => if Antitone μ ∧ μ N = 0 then
      heineTerm (fun k => a k * q ^ k) (fun k => q ^ k) (kappa N μ) else 0)
        (geomHankelDet q a N) := fun N =>
    hasSum_part N _ (hasSum_heine _ _ (fun k => (mul_pos (ha k) (pow_pos hq0 k)).le) N _ hMo)
  have hD1 : ∀ N, HasSum (fun μ : ℕ → ℕ => if Antitone μ ∧ μ N = 0 then
      heineTerm (fun k => q ^ k) (fun k => q ^ k) (kappa N μ) else 0)
        (Matrix.of fun i j : Fin N => (1 - q ^ ((i : ℕ) + (j : ℕ) + 1))⁻¹).det := fun N =>
    hasSum_part N _ (hasSum_heine _ _ (fun k => (pow_pos hq0 k).le) N _ hM1)
  have hFsum : ∀ N, HasSum (Fterm q a N)
      (geomHankelDet q a N / ((∏ i : Fin N, a i) * baseZ q N) -
        (Matrix.of fun i j : Fin N => (1 - q ^ ((i : ℕ) + (j : ℕ) + 1))⁻¹).det / baseZ q N) := by
    intro N
    have h := ((hDa N).div_const ((∏ i : Fin N, a i) * baseZ q N)).sub
      ((hD1 N).div_const (baseZ q N))
    convert h using 1
    funext μ
    simp only [Fterm]
    split_ifs
    · rw [heineTerm_weight]
      have hZ := baseZ_pos hq0 hq1 N
      have hPA : 0 < ∏ i : Fin N, a i := prod_pos fun i _ => ha i
      field_simp
    · simp
  have hT : Tendsto (fun N => ∑' μ, Fterm q a N μ) atTop (𝓝 (∑' μ : ℕ → ℕ, (0 : ℝ))) :=
    tendsto_tsum_of_dominated_convergence (bound := majorant q C n)
      (summable_majorant hq0 hq1 hC1 n) (fun μ => tendsto_Fterm hq0 hq1 ha hlim μ)
      (Eventually.of_forall fun N μ => norm_Fterm_le hq0 hq1 ha hC1 hbdn N μ)
  rw [tsum_zero] at hT
  have hRa : Tendsto (fun N => geomHankelDet q a N / ((∏ i : Fin N, a i) * baseZ q N)) atTop
      (𝓝 (gramM q)) := by
    have h := (tendsto_unit_ratio hq0 hq1).add hT
    rw [add_zero] at h
    refine h.congr fun N => ?_
    rw [(hFsum N).tsum_eq]
    ring
  have hfinal : ∀ N : ℕ, geomHankelDet q a N /
      (gramM q ^ 3 * q ^ (∑ j ∈ range N, j ^ 2) * qPochhammerInfinity q q ^ (2 * N) *
        ∏ k ∈ range N, a k) =
      geomHankelDet q a N / ((∏ i : Fin N, a i) * baseZ q N) * eProd q N ^ 2 / gramM q ^ 3 := by
    intro N
    rw [baseZ, heineTerm_base hq0 hq1, ← Fin.prod_univ_eq_prod_range a N]
    have hEN := eProd_pos hq0.le hq1 N
    have hP := PaperR10.qPochhammerInfinity_pos q q
    have hPA : 0 < ∏ i : Fin N, a i := prod_pos fun i _ => ha i
    have hqB : 0 < q ^ (∑ j ∈ range N, j ^ 2) := pow_pos hq0 _
    field_simp
  have hlimit := (hRa.mul ((tendsto_eProd hq0.le hq1).pow 2)).div_const (gramM q ^ 3)
  rw [show gramM q * gramM q ^ 2 / gramM q ^ 3 = 1 by field_simp] at hlimit
  exact hlimit.congr fun N => (hfinal N).symm

end Main

end ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality.geometric_universality
