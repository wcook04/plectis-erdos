import ErdosProblems.Erdos269.PaperR7AnalyticInterfaces
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Data.ENNReal.Real

/-!
# The infinite uniform finite-rank obstruction

The finite staircase minors alone do not prove a uniform lower bound. This
file uses their column separation inside a finite-dimensional bounded column
space, and a finite covering of a compact ball. Row factors in an arbitrary
separated representation need not be bounded; the subspace is formed by
intersecting their algebraic span with the space of bounded functions.

The final infimum ranges over ALL finite-separated-rank matrices. It uses an
extended nonnegative supremum so that unbounded approximants have infinite
uniform error, never the spurious zero returned by an unbounded real iSup.
The resulting finite value is also identified after conversion to the reals.
-/

namespace ErdosProblems.Erdos269.PaperR8

open PaperR7 ErdosProblems.Shared Set Metric
open scoped BigOperators Topology BoundedContinuousFunction ENNReal

abbrev BoundedColumn := ℕ →ᵇ ℝ
abbrev BoundedMatrix := (ℕ × ℕ) →ᵇ ℝ

def FiniteSeparatedRank (A : ℕ → ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ f g : Fin d → ℕ → ℝ,
    ∀ i j, A i j = ∑ k : Fin d, f k i * g k j

/-- Compact finite-dimensional balls have a finite packing bound. -/
theorem finite_packing_bound
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (M δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, ∀ v : Fin n → V, (∀ i, ‖v i‖ ≤ M) →
      ∃ i j, i ≠ j ∧ dist (v i) (v j) < δ := by
  classical
  -- Mathlib/Analysis/Normed/Module/FiniteDimension.lean: real proper-space instance.
  -- Mathlib/Topology/MetricSpace/Pseudo/Basic.lean: Metric.totallyBounded_iff.
  have hcompact : IsCompact (closedBall (0 : V) M) := isCompact_closedBall _ _
  obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp hcompact.totallyBounded
    (δ / 3) (by linarith)
  letI : Fintype s := hs.fintype
  refine ⟨Fintype.card s + 1, ?_⟩
  intro v hv
  have hc : ∀ i : Fin (Fintype.card s + 1),
      ∃ x : s, dist (v i) (x : V) < δ / 3 := by
    intro i
    have hi : v i ∈ closedBall (0 : V) M := by
      simpa only [mem_closedBall, dist_zero_right] using hv i
    have h := hcover hi
    rcases Set.mem_iUnion.mp h with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hxs, hball⟩
    exact ⟨⟨x, hxs⟩, hball⟩
  choose centre hcentre using hc
  by_contra hno
  have hinj : Function.Injective centre := by
    intro i j hij
    by_contra hne
    have hge : δ ≤ dist (v i) (v j) := by
      by_contra hlt
      exact hno ⟨i, j, hne, lt_of_not_ge hlt⟩
    have hi := hcentre i
    have hj : dist (centre i : V) (v j) < δ / 3 := by
      rw [hij, dist_comm]
      exact hcentre j
    have htriangle := dist_triangle (v i) (centre i : V) (v j)
    linarith
  -- Mathlib/Data/Fintype/Card.lean: Fintype.card_le_of_injective.
  have hcard := Fintype.card_le_of_injective centre hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Bounded columns of a finite-separated-rank matrix lie in a finite-dimensional
normed space, without a boundedness assumption on the chosen row factors. -/
theorem bounded_column_space (A : ℕ → ℕ → ℝ) (hA : FiniteSeparatedRank A)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i j, |A i j| ≤ M) :
    ∃ V : Submodule ℝ BoundedColumn, FiniteDimensional ℝ V ∧
      ∃ v : ℕ → V, (∀ i j, ((v j : BoundedColumn) i) = A i j) ∧
        ∀ j, ‖v j‖ ≤ M := by
  classical
  obtain ⟨d, f, g, hrep⟩ := hA
  let W : Submodule ℝ (ℕ → ℝ) := Submodule.span ℝ (Set.range f)
  -- Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean: span_of_finite, of_injective.
  letI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  let V : Submodule ℝ BoundedColumn :=
    { carrier := {u | (u : ℕ → ℝ) ∈ W}
      zero_mem' := W.zero_mem
      add_mem' := fun hu hv => W.add_mem hu hv
      smul_mem' := fun c u hu => W.smul_mem c hu }
  let F : V →ₗ[ℝ] W :=
    { toFun := fun u => ⟨(u.val : ℕ → ℝ), u.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hF : Function.Injective F := by
    intro u v huv
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro i
    exact congrFun (congrArg Subtype.val huv) i
  letI : FiniteDimensional ℝ V := FiniteDimensional.of_injective F hF
  -- Mathlib/Topology/ContinuousMap/Bounded/Normed.lean: ofNormedAddCommGroupDiscrete.
  let col : ℕ → BoundedColumn := fun j =>
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i => A i j) M
      (fun i => by simpa only [Real.norm_eq_abs] using hbound i j)
  have hcol : ∀ j, col j ∈ V := by
    intro j
    change (fun i => A i j) ∈ W
    have heq : (fun i => A i j) = ∑ k : Fin d, (g k j) • f k := by
      funext i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hrep i j
    rw [heq]
    exact W.sum_mem (fun k _ => W.smul_mem (g k j) (Submodule.subset_span ⟨k, rfl⟩))
  refine ⟨V, inferInstance, fun j => ⟨col j, hcol j⟩, ?_, ?_⟩
  · intro i j
    rfl
  · intro j
    change ‖col j‖ ≤ M
    -- Mathlib/Topology/ContinuousMap/Bounded/Normed.lean: norm_le.
    exact (BoundedContinuousFunction.norm_le hM).mpr
      (fun i => by simpa only [Real.norm_eq_abs] using hbound i j)

/-- The actual carry is bounded by one. -/
theorem realCarryMatrix_abs_le_one {p q r : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 1 < r) (i j : ℕ) :
    |realCarryMatrix p q r i j| ≤ 1 := by
  have hbit := logCarry_le_one hr (pow_ne_zero i hp.ne') (pow_ne_zero j hq.ne')
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_trans (by decide : 0 < 1) hr)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.le
  have hc : (r : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hr0).mpr hr1
  have hc0 : (0 : ℝ) ≤ (r : ℝ)⁻¹ := inv_nonneg.mpr hr0.le
  have hh : logCarry r (p ^ i) (q ^ j) = 0 ∨ logCarry r (p ^ i) (q ^ j) = 1 := by omega
  rcases hh with hh | hh
  · simp only [realCarryMatrix, hh, pow_zero, abs_one, le_refl]
  · simpa only [realCarryMatrix, hh, pow_one, abs_of_nonneg hc0] using hc

/-- All finite staircase patterns for the actual real carry. The phase selection
is reused from the compiled shared irrational-rotation module. -/
theorem realCarry_staircases {p q r : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 1 < r)
    (hα : NoIntegerOrbit (Real.logb r p)) (hβ : NoIntegerOrbit (Real.logb r q))
    (n : ℕ) :
    ∃ I J : Fin n → ℕ, ∀ a b,
      realCarryMatrix p q r (I a) (J b) =
        if b ≤ a then (r : ℝ)⁻¹ else 1 := by
  obtain ⟨I, J, _hIpos, _hJpos, _hIinj, _hJinj, hstair⟩ :=
    exists_staircase_indices hα hβ n
  refine ⟨I, J, ?_⟩
  intro a b
  have hc := logCarry_pow_eq_floor_fract (b := r) hr hp hq (I a) (J b)
  rw [hstair a b] at hc
  by_cases hba : b ≤ a
  · have hn : (b : ℕ) ≤ (a : ℕ) := hba
    rw [if_pos hn] at hc
    have hcarry : logCarry r (p ^ I a) (q ^ J b) = 1 := by omega
    simp only [realCarryMatrix, hcarry, pow_one, if_pos hba]
  · have hn : ¬(b : ℕ) ≤ (a : ℕ) := hba
    rw [if_neg hn] at hc
    have hcarry : logCarry r (p ^ I a) (q ^ J b) = 0 := by omega
    simp only [realCarryMatrix, hcarry, pow_zero, if_neg hba]

/-- The missing unrestricted lower bound: every finite-error finite-separated-rank
approximation has error at least half the carry jump. -/
theorem finite_rank_uniform_error_lower {p q r : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 1 < r)
    (hα : NoIntegerOrbit (Real.logb r p)) (hβ : NoIntegerOrbit (Real.logb r q))
    (A : ℕ → ℕ → ℝ) (hA : FiniteSeparatedRank A)
    (E : ℝ) (hE : 0 ≤ E)
    (herr : ∀ i j, |realCarryMatrix p q r i j - A i j| ≤ E) :
    (1 - (r : ℝ)⁻¹) / 2 ≤ E := by
  classical
  by_contra hnot
  have hsmall : E < (1 - (r : ℝ)⁻¹) / 2 := lt_of_not_ge hnot
  let δ : ℝ := 1 - (r : ℝ)⁻¹ - 2 * E
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hAbound : ∀ i j, |A i j| ≤ 1 + E := by
    intro i j
    calc
      |A i j| = |realCarryMatrix p q r i j -
          (realCarryMatrix p q r i j - A i j)| := by congr 1; ring
      _ ≤ |realCarryMatrix p q r i j| + |realCarryMatrix p q r i j - A i j| :=
        abs_sub _ _
      _ ≤ 1 + E := add_le_add (realCarryMatrix_abs_le_one hp hq hr i j) (herr i j)
  obtain ⟨V, hV, v, hv, hvbound⟩ := bounded_column_space A hA (1 + E) (by linarith) hAbound
  letI : FiniteDimensional ℝ V := hV
  obtain ⟨n, hn⟩ := finite_packing_bound V (1 + E) δ hδ
  obtain ⟨I, J, hIJ⟩ := realCarry_staircases hp hq hr hα hβ n
  obtain ⟨j, k, hjk, hclose⟩ := hn (fun j => v (J j)) (fun j => hvbound (J j))
  have hc1 : (r : ℝ)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by exact_mod_cast (lt_trans (by decide : 0 < 1) hr))).mpr
    exact_mod_cast hr.le
  have hsep : ∃ i : ℕ,
      |realCarryMatrix p q r i (J j) - realCarryMatrix p q r i (J k)| =
        1 - (r : ℝ)⁻¹ := by
    rcases lt_or_gt_of_ne hjk with hjk' | hkj'
    · refine ⟨I j, ?_⟩
      rw [hIJ, hIJ, if_pos (le_refl j), if_neg (not_le.mpr hjk')]
      rw [abs_of_nonpos (by linarith)]
      ring
    · refine ⟨I k, ?_⟩
      rw [hIJ, hIJ, if_neg (not_le.mpr hkj'), if_pos (le_refl k)]
      rw [abs_of_nonneg (by linarith)]
  obtain ⟨i, hi⟩ := hsep
  have hpoint : |A i (J j) - A i (J k)| ≤ dist (v (J j)) (v (J k)) := by
    -- Mathlib/Topology/ContinuousMap/Bounded/Basic.lean: dist_coe_le_dist.
    have h := BoundedContinuousFunction.dist_coe_le_dist
      (f := (v (J j) : BoundedColumn)) (g := (v (J k) : BoundedColumn)) i
    simpa only [hv, Real.dist_eq] using h
  have htriangle :
      |realCarryMatrix p q r i (J j) - realCarryMatrix p q r i (J k)| ≤
        |realCarryMatrix p q r i (J j) - A i (J j)| +
        |A i (J j) - A i (J k)| +
        |A i (J k) - realCarryMatrix p q r i (J k)| := by
    calc
      _ = |(realCarryMatrix p q r i (J j) - A i (J j)) +
          (A i (J j) - A i (J k)) +
          (A i (J k) - realCarryMatrix p q r i (J k))| := by congr 1; ring
      _ ≤ |realCarryMatrix p q r i (J j) - A i (J j) +
          (A i (J j) - A i (J k))| +
          |A i (J k) - realCarryMatrix p q r i (J k)| := abs_add_le
          ((realCarryMatrix p q r i (J j) - A i (J j)) + (A i (J j) - A i (J k)))
          (A i (J k) - realCarryMatrix p q r i (J k))
      _ ≤ _ := add_le_add
        (abs_add_le (realCarryMatrix p q r i (J j) - A i (J j))
          (A i (J j) - A i (J k)))
        (le_refl |A i (J k) - realCarryMatrix p q r i (J k)|)
  have he1 := herr i (J j)
  have he2 : |A i (J k) - realCarryMatrix p q r i (J k)| ≤ E := by
    rw [abs_sub_comm]
    exact herr i (J k)
  rw [hi] at htriangle
  dsimp [δ] at hclose
  have hupper := add_le_add (add_le_add he1 hpoint) he2
  have hsep := htriangle.trans hupper
  have impossible (x d e : ℝ) (h₁ : x ≤ e + d + e)
      (h₂ : d < x - 2 * e) : False := by linarith
  exact impossible (1 - (r : ℝ)⁻¹) (dist (v (J j)) (v (J k))) E hsep hclose


/-- All finite-separated-rank matrices, with no bounded-factor restriction. -/
abbrev FiniteRankMatrix := {A : ℕ → ℕ → ℝ // FiniteSeparatedRank A}

/-- An extended supremum is essential: the real supremum convention at an
unbounded set must not turn infinite error into zero. -/
noncomputable def uniformError (C A : ℕ → ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ i : ℕ, ⨆ j : ℕ, ENNReal.ofReal |C i j - A i j|

/-- The requested iInf equality over every finite separated rank. -/
theorem iInf_uniform_finite_rank_distance {p q r : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 1 < r)
    (hα : NoIntegerOrbit (Real.logb r p)) (hβ : NoIntegerOrbit (Real.logb r q)) :
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
      ENNReal.ofReal (((r : ℝ) - 1) / (2 * (r : ℝ))) := by
  classical
  let gap : ℝ := ((r : ℝ) - 1) / (2 * (r : ℝ))
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := lt_trans (by norm_num) hrR
  have hgap_eq : gap = (1 - (r : ℝ)⁻¹) / 2 := by
    dsimp [gap]
    field_simp [hr0.ne']
    <;> ring
  let mid : FiniteRankMatrix :=
    ⟨(fun _ _ => (1 + (r : ℝ)⁻¹) / 2),
      ⟨1, (fun _ _ => (1 + (r : ℝ)⁻¹) / 2), (fun _ _ => 1),
        by intro i j; simp⟩⟩
  change (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
    ENNReal.ofReal gap
  apply le_antisymm
  · refine (iInf_le _ mid).trans ?_
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    have h := (uniform_carry_midpoint_witness hp hq hr).2 i j
    change ENNReal.ofReal |realCarryMatrix p q r i j - (1 + (r : ℝ)⁻¹) / 2| ≤ _
    rw [h]
  · apply le_iInf
    intro A
    let E := uniformError (realCarryMatrix p q r) A.val
    change ENNReal.ofReal gap ≤ E
    by_cases htop : E = ⊤
    · rw [htop]
      exact le_top
    have herr : ∀ i j, |realCarryMatrix p q r i j - A.val i j| ≤ E.toReal := by
      intro i j
      have he : ENNReal.ofReal |realCarryMatrix p q r i j - A.val i j| ≤ E :=
        (le_iSup_of_le i (le_iSup_of_le j le_rfl))
      -- Mathlib/Data/ENNReal/Real.lean: toReal_mono.
      -- Mathlib/Data/ENNReal/Basic.lean: toReal_ofReal.
      have h := ENNReal.toReal_mono htop he
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h
    have hlow := finite_rank_uniform_error_lower hp hq hr hα hβ A.val A.property
      E.toReal ENNReal.toReal_nonneg herr
    rw [← hgap_eq] at hlow
    -- Mathlib/Data/ENNReal/Real.lean: ofReal_le_of_le_toReal.
    exact ENNReal.ofReal_le_of_le_toReal hlow

/-- The displayed prime-specialised equality, including the real-valued form. -/
theorem uniform_rank_prime_equality {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal (((r : ℝ) - 1) / (2 * (r : ℝ))) ∧
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val).toReal =
        ((r : ℝ) - 1) / (2 * (r : ℝ)) := by
  have h := iInf_uniform_finite_rank_distance hp.pos hq.pos hr.one_lt
    (noIntegerOrbit_logb_of_prime hp hr hpr)
    (noIntegerOrbit_logb_of_prime hq hr hqr)
  refine ⟨h, ?_⟩
  rw [h]
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr.one_lt
  exact ENNReal.toReal_ofReal
    (div_nonneg (sub_nonneg.mpr hrR.le) (mul_nonneg (by norm_num) (by positivity)))

/-- The entire displayed environment: both equal expressions for the infimum,
plus an explicit constant rank-one minimiser. No bounded-factor restriction. -/
theorem uniform_rank_complete {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal ((1 - (r : ℝ)⁻¹) / 2) ∧
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal (((r : ℝ) - 1) / (2 * (r : ℝ))) ∧
    ∃ A : FiniteRankMatrix,
      (∀ i j, A.val i j = (1 + (r : ℝ)⁻¹) / 2) ∧
      uniformError (realCarryMatrix p q r) A.val =
        (⨅ F : FiniteRankMatrix, uniformError (realCarryMatrix p q r) F.val) := by
  classical
  have heq := (uniform_rank_prime_equality hp hq hr hpr hqr).1
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hgap : ((r : ℝ) - 1) / (2 * (r : ℝ)) = (1 - (r : ℝ)⁻¹) / 2 := by
    field_simp [hr0]
    <;> ring
  refine ⟨heq.trans (congrArg ENNReal.ofReal hgap), heq, ?_⟩
  let A : FiniteRankMatrix :=
    ⟨(fun _ _ => (1 + (r : ℝ)⁻¹) / 2),
      ⟨1, (fun _ _ => (1 + (r : ℝ)⁻¹) / 2), (fun _ _ => 1),
        by intro i j; simp⟩⟩
  refine ⟨A, fun _ _ => rfl, ?_⟩
  apply le_antisymm
  · rw [heq]
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    change ENNReal.ofReal
      |realCarryMatrix p q r i j - (1 + (r : ℝ)⁻¹) / 2| ≤ _
    rw [(uniform_carry_midpoint_witness hp.pos hq.pos hr.one_lt).2 i j]
  · exact iInf_le _ A

end ErdosProblems.Erdos269.PaperR8
