import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget
import ErdosProblems.Erdos257.PaperCompleteR8.CoverPotentialBounds

/-!
# The arithmetic lower bound for every fractional cover (long #257, line 9369)

Display `eq:257-arithmetic-cover-lower` of the long Erdős #257 `cor`
"finite-functional separation" at
`paper/reasoning-parts/erdos257/a257_front.tex:9371`:

  `K_*(F) ≥ max_{ℓ ∣ Q} ℙ(U_F(N) > 1 | ℓ ∣ N)`,  `N` uniform modulo `Q = lcm F`.

`K_*(F)` is the tree's `optimizedLogCoverCost (F : Set ℕ)`, the infimum over the
paper's admissible countable fractional covers (frames `F_j`, exponents
`0 < α_j ≤ 1`, weights `η_j > 0` with `∑ η_j = 1`, coefficients `c_{j,d} ≥ 0`
majorising `f_{F_j}^{α_j}`) of the cost `∑_j C_j η_j^{-α_j}/(2^{α_j} - 1)`;
`U_F` is `framePotential`.  `ℙ_ℓ` is uniform sampling of `N = ℓ m` over one
period `Q/ℓ`, which for `ℓ ∣ Q` is `N` uniform modulo `Q` conditioned on
`ℓ ∣ N`.

The proof is the paper's: the pointwise estimate
`1_{U_F > 1} ≤ ∑_j η_j^{-α_j} U_j^{α_j} ≤ ∑_{j,d} η_j^{-α_j} c_{j,d} w_{B_j,d}`,
then the finite dyadic estimate `eq:257-mixed-finite-kernel` with its factor
`1 + 4L/M` (the tree's `dyadicMean_kernelWeight_le`), and then `R → ∞` and
`M → ∞`, the first limit being controlled by the periodic-average error bound
`periodicMean_sub_le` below.

This module covers only the displayed inequality of that corollary.  Its two
remaining clauses (`K_*(F) ≥ 1 - e^{-1}` and `κ₁(F;1) ≤ 30 log 2 / H` for the
supports of `thm:257-logarithmic-counterexample`, and the non-existence of an
absolute `C` with `K_* ≤ C κ₁`) depend on that theorem's construction, which is
not formalised.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems.Erdos257.PaperCompleteR8

/-! ### Periodic sampling means -/

/-- A bounded `P`-periodic sequence: its mean over `range T` is below its mean
over one period by at most `P/T`.  This is the paper's
`|T⁻¹ ∑_{m ≤ T} 1_{U_F(Lm) > 1} - p| ≤ P₀/T`, in the one-sided form used. -/
theorem periodicMean_sub_le (v : ℕ → ℝ) (P : ℕ) (hP : 0 < P)
    (hper : ∀ m, v (m + P) = v m) (hv0 : ∀ m, 0 ≤ v m) (hv1 : ∀ m, v m ≤ 1)
    (T : ℕ) (hT : 0 < T) :
    (∑ m ∈ Finset.range P, v m) / (P : ℝ) - (P : ℝ) / (T : ℝ)
      ≤ (∑ m ∈ Finset.range T, v m) / (T : ℝ) := by
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hshift : ∀ k m : ℕ, v (m + k * P) = v m := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
        intro m
        have hidx : m + (k + 1) * P = m + k * P + P := by ring
        rw [hidx, hper, ih]
  have hblock : ∀ k : ℕ, (∑ m ∈ Finset.range (k * P), v m)
      = (k : ℝ) * ∑ m ∈ Finset.range P, v m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hidx : (k + 1) * P = k * P + P := by ring
        rw [hidx, Finset.sum_range_add, ih]
        have hsh : (∑ i ∈ Finset.range P, v (k * P + i)) = ∑ i ∈ Finset.range P, v i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hcomm : k * P + i = i + k * P := by ring
          rw [hcomm, hshift]
        rw [hsh]
        push_cast
        ring
  obtain ⟨q, s, hslt, hTq⟩ : ∃ q s : ℕ, s < P ∧ T = q * P + s :=
    ⟨T / P, T % P, Nat.mod_lt T hP, by
      rw [Nat.mul_comm (T / P) P]
      exact (Nat.div_add_mod T P).symm⟩
  have hsplit : (∑ m ∈ Finset.range T, v m)
      = (q : ℝ) * (∑ m ∈ Finset.range P, v m) + ∑ i ∈ Finset.range s, v i := by
    rw [hTq, Finset.sum_range_add, hblock]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcomm : q * P + i = i + q * P := by ring
    rw [hcomm, hshift]
  have hSle : (∑ m ∈ Finset.range P, v m) ≤ (P : ℝ) := by
    calc (∑ m ∈ Finset.range P, v m) ≤ ∑ _m ∈ Finset.range P, (1 : ℝ) :=
          Finset.sum_le_sum fun m _ => hv1 m
      _ = (P : ℝ) := by simp
  have hS0 : (0 : ℝ) ≤ (∑ m ∈ Finset.range P, v m) := Finset.sum_nonneg fun m _ => hv0 m
  have hSs0 : (0 : ℝ) ≤ (∑ i ∈ Finset.range s, v i) := Finset.sum_nonneg fun m _ => hv0 m
  have hsR : (s : ℝ) ≤ (P : ℝ) := by exact_mod_cast hslt.le
  have hTcast : (T : ℝ) = (q : ℝ) * (P : ℝ) + (s : ℝ) := by rw [hTq]; push_cast; ring
  rw [sub_le_iff_le_add, ← add_div, div_le_div_iff₀ hPR hTR, hsplit, hTcast]
  nlinarith [mul_nonneg (sub_nonneg.mpr hsR) hS0,
    mul_nonneg (sub_nonneg.mpr hSle) hPR.le, mul_nonneg hSs0 hPR.le]

/-! ### The conditional arithmetic sampling measure -/

/-- The indicator of the paper's event `{U_F > 1}`. -/
def exceedInd (F : Finset ℕ) (N : ℕ) : ℝ := if 1 < framePotential F N then 1 else 0

theorem exceedInd_nonneg (F : Finset ℕ) (N : ℕ) : 0 ≤ exceedInd F N := by
  unfold exceedInd; split_ifs <;> norm_num

theorem exceedInd_le_one (F : Finset ℕ) (N : ℕ) : exceedInd F N ≤ 1 := by
  unfold exceedInd; split_ifs <;> norm_num

/-- `U_F` has period `Q = lcm F`. -/
theorem framePotential_add_lcm (F : Finset ℕ) (N : ℕ) :
    framePotential F (N + F.lcm id) = framePotential F N := by
  unfold framePotential
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨k, hk⟩ : a ∣ F.lcm id := Finset.dvd_lcm ha
  unfold kernelWeight
  rw [hk, Nat.add_mul_mod_self_left]

/-- The paper's `ℙ_ℓ(U_F > 1)`: uniform sampling of `N = ℓ m` over one period
`Q/ℓ` of `m ↦ U_F(ℓ m)`.  For `ℓ ∣ Q` the sampled points `ℓ, 2ℓ, …, Q` are a
complete set of representatives of the multiples of `ℓ` modulo `Q`, so this is
`ℙ(U_F(N) > 1 | ℓ ∣ N)` for `N` uniform modulo `Q`. -/
def condExceedProb (F : Finset ℕ) (ℓ : ℕ) : ℝ :=
  progressionMean ℓ (F.lcm id / ℓ) (exceedInd F)

/-- The dyadic observation mean of the indicator is at most `P/2^R` below
`ℙ_ℓ(U_F > 1)`. -/
theorem condExceedProb_sub_le_dyadicMean (F : Finset ℕ) (hF : 0 ∉ F)
    (ℓ : ℕ) (hℓ0 : 0 < ℓ) (hℓ : ℓ ∣ F.lcm id) (R M : ℕ) (hM : 0 < M) :
    condExceedProb F ℓ - ((F.lcm id / ℓ : ℕ) : ℝ) / (2 : ℝ) ^ R
      ≤ dyadicMean ℓ R M (exceedInd F) := by
  have hQ0 : F.lcm id ≠ 0 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h
    have hx0' : x = 0 := hx0
    exact hF (hx0' ▸ hx)
  have hQpos : 0 < F.lcm id := Nat.pos_of_ne_zero hQ0
  have hPpos : 0 < F.lcm id / ℓ := Nat.div_pos (Nat.le_of_dvd hQpos hℓ) hℓ0
  have hmul : ℓ * (F.lcm id / ℓ) = F.lcm id := Nat.mul_div_cancel' hℓ
  set P : ℕ := F.lcm id / ℓ with hPdef
  set v : ℕ → ℝ := fun m => exceedInd F ((m + 1) * ℓ) with hvdef
  have hper : ∀ m, v (m + P) = v m := by
    intro m
    have hidx : (m + P + 1) * ℓ = (m + 1) * ℓ + F.lcm id := by
      have : (m + P + 1) * ℓ = (m + 1) * ℓ + ℓ * P := by ring
      rw [this, hmul]
    simp only [hvdef]
    rw [hidx]
    unfold exceedInd
    rw [framePotential_add_lcm]
  have hmean : ∀ T : ℕ, 0 < T →
      condExceedProb F ℓ - (P : ℝ) / (T : ℝ)
        ≤ progressionMean ℓ T (exceedInd F) := by
    intro T hT
    have h := periodicMean_sub_le v P hPpos hper
      (fun m => exceedInd_nonneg F _) (fun m => exceedInd_le_one F _) T hT
    have hleft : (∑ m ∈ Finset.range P, v m) / (P : ℝ) = condExceedProb F ℓ := rfl
    have hright : (∑ m ∈ Finset.range T, v m) / (T : ℝ)
        = progressionMean ℓ T (exceedInd F) := rfl
    rw [hleft, hright] at h
    exact h
  have hstep : ∀ j ∈ Finset.Ico R (R + M),
      condExceedProb F ℓ - (P : ℝ) / (2 : ℝ) ^ R
        ≤ progressionMean ℓ (2 ^ j) (exceedInd F) := by
    intro j hj
    have hjR : R ≤ j := (Finset.mem_Ico.mp hj).1
    have hTpos : 0 < (2 : ℕ) ^ j := by positivity
    have h := hmean (2 ^ j) hTpos
    have hcast : (((2 : ℕ) ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
    rw [hcast] at h
    have h2j : (2 : ℝ) ^ R ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hjR
    have hPnn : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
    have hdiv : (P : ℝ) / (2 : ℝ) ^ j ≤ (P : ℝ) / (2 : ℝ) ^ R := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_left h2j hPnn
    linarith
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcard : (Finset.Ico R (R + M)).card = M := by rw [Nat.card_Ico]; omega
  have hsum : (condExceedProb F ℓ - (P : ℝ) / (2 : ℝ) ^ R) * (M : ℝ)
      ≤ ∑ j ∈ Finset.Ico R (R + M), progressionMean ℓ (2 ^ j) (exceedInd F) := by
    calc (condExceedProb F ℓ - (P : ℝ) / (2 : ℝ) ^ R) * (M : ℝ)
        = ∑ _j ∈ Finset.Ico R (R + M), (condExceedProb F ℓ - (P : ℝ) / (2 : ℝ) ^ R) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum hstep
  unfold dyadicMean
  rw [le_div_iff₀ hMR]
  exact hsum

/-! ### The cover majorant -/

/-- The fractional-cover data underlying a `LogBudgetCover`. -/
def coverData {A : Set ℕ} (C : LogBudgetCover A) : PositiveCoverData where
  frame := C.frame
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  majorises := C.majorises

/-- The paper's `j`-th cost term `C_j η_j^{-α_j}/(2^{α_j} - 1)`. -/
def coverBudget {A : Set ℕ} (C : LogBudgetCover A) (j : ℕ) : ℝ :=
  (∑' d : ℕ, C.coefficient j d / (d : ℝ)) / (C.weight j ^ C.exponent j) /
    ((2 : ℝ) ^ C.exponent j - 1)

/-- The paper's `j`-th pointwise majorant `η_j^{-α_j} V_j(N)`. -/
def scaledCoverPotential {A : Set ℕ} (C : LogBudgetCover A) (j N : ℕ) : ℝ :=
  C.weight j ^ (-C.exponent j) * coverPotential (coverData C) j N

theorem coverBudget_summable {A : Set ℕ} (C : LogBudgetCover A) :
    Summable (coverBudget C) := C.budget_summable

theorem cost_eq_tsum_coverBudget {A : Set ℕ} (C : LogBudgetCover A) :
    C.cost = ∑' j, coverBudget C j := rfl

theorem scaledCoverPotential_eq {A : Set ℕ} (C : LogBudgetCover A) (j N : ℕ) :
    scaledCoverPotential C j N
      = (C.weight j ^ C.exponent j)⁻¹ * coverPotential (coverData C) j N := by
  unfold scaledCoverPotential
  rw [Real.rpow_neg (C.weight_positive j).le]

theorem scaledCoverPotential_nonneg {A : Set ℕ} (C : LogBudgetCover A) (j N : ℕ) :
    0 ≤ scaledCoverPotential C j N :=
  mul_nonneg (Real.rpow_nonneg (C.weight_positive j).le _)
    (coverPotential_nonneg (coverData C) j N)

theorem coverBudget_nonneg {A : Set ℕ} (C : LogBudgetCover A) (j : ℕ) :
    0 ≤ coverBudget C j := by
  unfold coverBudget
  apply div_nonneg _ (sub_pos.mpr (coverBase_gt_one (coverData C) j)).le
  apply div_nonneg _ (Real.rpow_nonneg (C.weight_positive j).le _)
  exact positiveCover_cost_nonneg (coverData C) j

/-- Rewriting the scaled column cost as the paper's budget term. -/
theorem scaled_cost_eq {A : Set ℕ} (C : LogBudgetCover A) (j : ℕ) (x : ℝ) :
    (C.weight j ^ C.exponent j)⁻¹ *
        (x * ((coverData C).cost j /
          (coverBase (coverData C) j - 1)))
      = x * coverBudget C j := by
  unfold coverBudget
  have hb : coverBase (coverData C) j = (2 : ℝ) ^ C.exponent j := rfl
  have hc : (coverData C).cost j = ∑' d : ℕ, C.coefficient j d / (d : ℝ) := rfl
  rw [hb, hc]
  ring

theorem scaledCoverPotential_le {A : Set ℕ} (C : LogBudgetCover A) (j N : ℕ) :
    scaledCoverPotential C j N ≤ (2 * (N : ℝ) + 1) * coverBudget C j := by
  rw [scaledCoverPotential_eq]
  have hinv : (0 : ℝ) ≤ (C.weight j ^ C.exponent j)⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg (C.weight_positive j).le _)
  have h := mul_le_mul_of_nonneg_left
    (coverPotential_le_cost (coverData C) j N) hinv
  rw [scaled_cost_eq C j (2 * (N : ℝ) + 1)] at h
  exact h

theorem summable_scaledCoverPotential {A : Set ℕ} (C : LogBudgetCover A) (N : ℕ) :
    Summable (fun j => scaledCoverPotential C j N) := by
  refine Summable.of_nonneg_of_le (fun j => scaledCoverPotential_nonneg C j N)
    (fun j => scaledCoverPotential_le C j N) ?_
  exact (coverBudget_summable C).mul_left (2 * (N : ℝ) + 1)

/-! ### The pointwise cover estimate -/

/-- `U_F ≤ ∑_{j ∈ J} U_{F_j}` for a finite subcover. -/
theorem framePotential_le_sum_frames (F J : Finset ℕ) (G : ℕ → Finset ℕ)
    (hcover : F ⊆ J.biUnion G) (N : ℕ) :
    framePotential F N ≤ ∑ j ∈ J, framePotential (G j) N := by
  classical
  have hex : ∀ a ∈ F, ∃ j, j ∈ J ∧ a ∈ G j := fun a ha =>
    Finset.mem_biUnion.mp (hcover ha)
  choose! φ hφJ hφG using hex
  have hkey := Finset.sum_fiberwise_of_maps_to (g := φ) (t := J) hφJ
    (fun a => kernelWeight 2 a N)
  have hfp : framePotential F N = ∑ a ∈ F, kernelWeight 2 a N := rfl
  rw [hfp, ← hkey]
  refine Finset.sum_le_sum fun j _ => ?_
  have hsub : F.filter (fun a => φ a = j) ⊆ G j := by
    intro a ha
    obtain ⟨haF, haj⟩ := Finset.mem_filter.mp ha
    exact haj ▸ hφG a haF
  have hfpj : framePotential (G j) N = ∑ a ∈ G j, kernelWeight 2 a N := rfl
  rw [hfpj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun a _ _ => kernelWeight_nonneg (by norm_num) a N)

/-- The paper's "if `U_F > 1` then `U_j > η_j` for at least one index". -/
theorem exists_frame_gt_weight (F : Finset ℕ) (C : LogBudgetCover (F : Set ℕ))
    (N : ℕ) (hgt : 1 < framePotential F N) :
    ∃ j, C.weight j < framePotential (C.frame j) N := by
  classical
  obtain ⟨J, hJ⟩ := exists_finite_frame_subcover F C.frame
    (fun a ha => C.covers a (Finset.mem_coe.mpr ha))
  by_contra hcon
  push_neg at hcon
  have h1 : framePotential F N ≤ ∑ j ∈ J, framePotential (C.frame j) N :=
    framePotential_le_sum_frames F J C.frame hJ N
  have h2 : (∑ j ∈ J, framePotential (C.frame j) N) ≤ ∑ j ∈ J, C.weight j :=
    Finset.sum_le_sum fun j _ => hcon j
  have h3 : (∑ j ∈ J, C.weight j) ≤ 1 := by
    have h := C.weight_sum.summable.sum_le_tsum J (fun j _ => (C.weight_positive j).le)
    simpa only [C.weight_sum.tsum_eq] using h
  linarith

/-- The paper's pointwise estimate
`1_{U_F > 1} ≤ ∑_j η_j^{-α_j} U_j^{α_j} ≤ ∑_j η_j^{-α_j} V_j`. -/
theorem exceedInd_le_tsum_scaledCoverPotential (F : Finset ℕ) (hF : 0 ∉ F)
    (C : LogBudgetCover (F : Set ℕ)) (N : ℕ) :
    exceedInd F N ≤ ∑' j, scaledCoverPotential C j N := by
  classical
  have hsummable := summable_scaledCoverPotential C N
  unfold exceedInd
  split_ifs with hgt
  · obtain ⟨j, hj⟩ := exists_frame_gt_weight F C N hgt
    have hηpos : 0 < C.weight j := C.weight_positive j
    have hUpos : 0 < framePotential (C.frame j) N := lt_trans hηpos hj
    have hratio : (1 : ℝ) ≤ framePotential (C.frame j) N / C.weight j := by
      rw [le_div_iff₀ hηpos, one_mul]
      exact hj.le
    have hαpos : 0 < C.exponent j := (C.exponent_bounds j).1
    have hone : (1 : ℝ) ≤ (framePotential (C.frame j) N / C.weight j) ^ C.exponent j :=
      Real.one_le_rpow hratio hαpos.le
    have hdivrpow : (framePotential (C.frame j) N / C.weight j) ^ C.exponent j
        = framePotential (C.frame j) N ^ C.exponent j / C.weight j ^ C.exponent j :=
      Real.div_rpow (framePotential_nonneg (C.frame j) N) hηpos.le _
    have hbridge : framePotential (C.frame j) N ^ C.exponent j
        ≤ coverPotential (coverData C) j N :=
      positiveCover_frame_bridge (coverData C) j N
    have hwpos : (0 : ℝ) < C.weight j ^ C.exponent j := Real.rpow_pos_of_pos hηpos _
    have hwle : C.weight j ^ C.exponent j ≤ coverPotential (coverData C) j N := by
      rw [hdivrpow, le_div_iff₀ hwpos, one_mul] at hone
      exact le_trans hone hbridge
    have hterm : (1 : ℝ) ≤ scaledCoverPotential C j N := by
      rw [scaledCoverPotential_eq]
      have hmul := mul_le_mul_of_nonneg_left hwle (inv_nonneg.mpr hwpos.le)
      rw [inv_mul_cancel₀ hwpos.ne'] at hmul
      exact hmul
    have hsingle : scaledCoverPotential C j N ≤ ∑' i, scaledCoverPotential C i N := by
      have h := hsummable.sum_le_tsum {j}
        (fun i _ => scaledCoverPotential_nonneg C i N)
      simpa using h
    linarith
  · exact tsum_nonneg (fun j => scaledCoverPotential_nonneg C j N)

/-! ### The dyadic observation estimate -/

theorem dyadicMean_scaledCoverPotential_le {A : Set ℕ} (C : LogBudgetCover A)
    (j L R M : ℕ) (hL : 0 < L) (hM : 0 < M) :
    dyadicMean L R M (scaledCoverPotential C j)
      ≤ (1 + 4 * (L : ℝ) / M) * coverBudget C j := by
  have hinv : (0 : ℝ) ≤ (C.weight j ^ C.exponent j)⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg (C.weight_positive j).le _)
  have hrw : dyadicMean L R M (scaledCoverPotential C j)
      = (C.weight j ^ C.exponent j)⁻¹ *
        dyadicMean L R M (coverPotential (coverData C) j) := by
    have hfun : scaledCoverPotential C j
        = fun N => (C.weight j ^ C.exponent j)⁻¹ *
            coverPotential (coverData C) j N := by
      funext N
      exact scaledCoverPotential_eq C j N
    rw [hfun, dyadicMean_const_mul]
  rw [hrw]
  have h := mul_le_mul_of_nonneg_left
    (dyadicMean_coverPotential_le (coverData C) j L R M hL hM) hinv
  rw [scaled_cost_eq C j (1 + 4 * (L : ℝ) / M)] at h
  exact h

theorem dyadicMean_tsum_scaledCoverPotential_le {A : Set ℕ} (C : LogBudgetCover A)
    (L R M : ℕ) (hL : 0 < L) (hM : 0 < M) :
    dyadicMean L R M (fun N => ∑' j, scaledCoverPotential C j N)
      ≤ (1 + 4 * (L : ℝ) / M) * C.cost := by
  have hu : ∀ N : ℕ, Summable (fun j => scaledCoverPotential C j N) :=
    summable_scaledCoverPotential C
  have hdom : Summable (fun j => (1 + 4 * (L : ℝ) / M) * coverBudget C j) :=
    (coverBudget_summable C).mul_left _
  have hpoint : ∀ j, dyadicMean L R M (scaledCoverPotential C j)
      ≤ (1 + 4 * (L : ℝ) / M) * coverBudget C j :=
    fun j => dyadicMean_scaledCoverPotential_le C j L R M hL hM
  have hleft : Summable (fun j => dyadicMean L R M (scaledCoverPotential C j)) := by
    refine Summable.of_nonneg_of_le ?_ hpoint hdom
    intro j
    exact dyadicMean_nonneg L R M _ (fun N => scaledCoverPotential_nonneg C j N)
  have hh := Summable.tsum_le_tsum hpoint hleft hdom
  rw [tsum_dyadicMean (fun j N => scaledCoverPotential C j N) hu L R M,
    tsum_mul_left] at hh
  rw [cost_eq_tsum_coverBudget]
  exact hh

/-! ### The arithmetic lower bound -/

/-- Every admissible fractional cover costs at least `ℙ_ℓ(U_F > 1)`. -/
theorem condExceedProb_le_cost (F : Finset ℕ) (hF : 0 ∉ F)
    (ℓ : ℕ) (hℓ0 : 0 < ℓ) (hℓ : ℓ ∣ F.lcm id) (C : LogBudgetCover (F : Set ℕ)) :
    condExceedProb F ℓ ≤ C.cost := by
  have hcost0 : 0 ≤ C.cost := by
    rw [cost_eq_tsum_coverBudget]
    exact tsum_nonneg (fun j => coverBudget_nonneg C j)
  by_contra hcon
  push_neg at hcon
  have hε : 0 < condExceedProb F ℓ - C.cost := by linarith
  set P : ℕ := F.lcm id / ℓ with hPdef
  set ε : ℝ := condExceedProb F ℓ - C.cost with hεdef
  -- choose the observation width M
  obtain ⟨M0, hM0⟩ := exists_nat_gt (8 * (ℓ : ℝ) * C.cost / ε)
  have hMpos : 0 < M0 + 1 := Nat.succ_pos M0
  have hMR : (0 : ℝ) < ((M0 + 1 : ℕ) : ℝ) := by exact_mod_cast hMpos
  have hM0R : (M0 : ℝ) < ((M0 + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hwidth : 4 * (ℓ : ℝ) / ((M0 + 1 : ℕ) : ℝ) * C.cost < ε / 2 := by
    have hlt : 8 * (ℓ : ℝ) * C.cost / ε < ((M0 + 1 : ℕ) : ℝ) := lt_trans hM0 hM0R
    have h1 : 8 * (ℓ : ℝ) * C.cost < ((M0 + 1 : ℕ) : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hlt
    have h2 : 4 * (ℓ : ℝ) / ((M0 + 1 : ℕ) : ℝ) * C.cost
        = (4 * (ℓ : ℝ) * C.cost) / ((M0 + 1 : ℕ) : ℝ) := by
      field_simp
    rw [h2, div_lt_iff₀ hMR]
    linarith
  -- choose the observation depth R
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ε / (2 * ((P : ℝ) + 1)) by
      apply div_pos hε
      have : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
      linarith)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hdepth : (P : ℝ) / (2 : ℝ) ^ R < ε / 2 := by
    have hP1 : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
    have hpow : (0 : ℝ) < (2 : ℝ) ^ R := by positivity
    have hid : (1 / 2 : ℝ) ^ R = 1 / (2 : ℝ) ^ R := by
      rw [div_pow, one_pow]
    rw [hid] at hR
    have h1 : (P : ℝ) / (2 : ℝ) ^ R ≤ ((P : ℝ) + 1) * (1 / (2 : ℝ) ^ R) := by
      rw [mul_one_div, div_le_div_iff₀ hpow hpow]
      nlinarith [hpow]
    have h2 : ((P : ℝ) + 1) * (1 / (2 : ℝ) ^ R)
        < ((P : ℝ) + 1) * (ε / (2 * ((P : ℝ) + 1))) := by
      apply mul_lt_mul_of_pos_left hR
      linarith
    have h3 : ((P : ℝ) + 1) * (ε / (2 * ((P : ℝ) + 1))) = ε / 2 := by
      field_simp
    linarith
  -- the two estimates
  have hlow := condExceedProb_sub_le_dyadicMean F hF ℓ hℓ0 hℓ R (M0 + 1) hMpos
  have hmono : dyadicMean ℓ R (M0 + 1) (exceedInd F)
      ≤ dyadicMean ℓ R (M0 + 1) (fun N => ∑' j, scaledCoverPotential C j N) :=
    dyadicMean_mono ℓ R (M0 + 1) _ _
      (fun N => exceedInd_le_tsum_scaledCoverPotential F hF C N)
  have hhigh := dyadicMean_tsum_scaledCoverPotential_le C ℓ R (M0 + 1) hℓ0 hMpos
  have hexpand : (1 + 4 * (ℓ : ℝ) / ((M0 + 1 : ℕ) : ℝ)) * C.cost
      = C.cost + 4 * (ℓ : ℝ) / ((M0 + 1 : ℕ) : ℝ) * C.cost := by ring
  rw [hexpand] at hhigh
  linarith

/-! ### A finite support always admits a finite-cost cover -/

/-- The paper's "a finite-cost cover exists, for example the single set `F` with
exponent one". -/
def singleFrameCover (F : Finset ℕ) (hF : 0 ∉ F) : LogBudgetCover (F : Set ℕ) where
  frame := fun j => if j = 0 then F else ∅
  weight := fun j => (1 / 2 : ℝ) ^ (j + 1)
  exponent := fun _ => 1
  coefficient := fun j d => if j = 0 then (if d ∈ F then (1 : ℝ) else 0) else 0
  frame_positive := by
    intro j
    by_cases h : j = 0
    · simpa [h] using hF
    · simp [h]
  weight_positive := by intro j; positivity
  weight_sum := by
    have h := hasSum_geometric_two.mul_left (1 / 2 : ℝ)
    have hfun : (fun n : ℕ => (1 / 2 : ℝ) * ((1 / 2 : ℝ)) ^ n)
        = fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) := by
      funext n
      rw [pow_succ]
      ring
    have hone : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    rw [hfun, hone] at h
    exact h
  exponent_bounds := by intro j; norm_num
  coefficient_nonneg := by
    intro j d _
    split_ifs <;> norm_num
  column_summable := by
    intro j
    refine summable_of_ne_finset_zero (s := F) ?_
    intro d hd
    simp [if_neg hd]
  covers := by
    intro a ha
    exact ⟨0, by simpa using (Finset.mem_coe.mp ha)⟩
  majorises := by
    intro j n hn
    by_cases h : j = 0
    · subst h
      have hfil : F.filter (fun a => a ∣ n) = n.divisors.filter (fun d => d ∈ F) := by
        ext a
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨haF, han⟩
          exact ⟨⟨han, hn.ne'⟩, haF⟩
        · rintro ⟨⟨han, -⟩, haF⟩
          exact ⟨haF, han⟩
      simp only [eq_self_iff_true, if_true, Real.rpow_one]
      refine le_of_eq ?_
      rw [Finset.sum_boole, hfil]
    · simp only [if_neg h, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
        Real.rpow_one, Finset.sum_const_zero, le_refl]
  budget_summable := by
    refine summable_of_ne_finset_zero (s := {0}) ?_
    intro j hj
    have hj0 : j ≠ 0 := by simpa using hj
    have hzero : (∑' d : ℕ,
        (if j = 0 then (if d ∈ F then (1 : ℝ) else 0) else 0) / (d : ℝ)) = 0 := by
      have hall : ∀ d : ℕ,
          (if j = 0 then (if d ∈ F then (1 : ℝ) else 0) else 0) / (d : ℝ) = 0 := by
        intro d
        rw [if_neg hj0, zero_div]
      simp only [hall, tsum_zero]
    simp [hzero]

/-- Display `eq:257-arithmetic-cover-lower` (line 9371): `K_*(F)` is at least the
conditional arithmetic sampling probability at every divisor `ℓ` of `Q`. -/
theorem condExceedProb_le_optimizedLogCoverCost (F : Finset ℕ) (hF : 0 ∉ F)
    (ℓ : ℕ) (hℓ0 : 0 < ℓ) (hℓ : ℓ ∣ F.lcm id) :
    condExceedProb F ℓ ≤ optimizedLogCoverCost (F : Set ℕ) := by
  refine le_csInf ⟨(singleFrameCover F hF).cost, ⟨singleFrameCover F hF, rfl⟩⟩ ?_
  rintro x ⟨C, rfl⟩
  exact condExceedProb_le_cost F hF ℓ hℓ0 hℓ C

/-- The displayed maximum form of `eq:257-arithmetic-cover-lower`. -/
theorem sup_condExceedProb_le_optimizedLogCoverCost (F : Finset ℕ) (hF : 0 ∉ F)
    (hne : (F.lcm id).divisors.Nonempty) :
    (F.lcm id).divisors.sup' hne (fun ℓ => condExceedProb F ℓ)
      ≤ optimizedLogCoverCost (F : Set ℕ) := by
  refine Finset.sup'_le hne _ fun ℓ hℓ => ?_
  exact condExceedProb_le_optimizedLogCoverCost F hF ℓ
    (Nat.pos_of_mem_divisors hℓ) (Nat.dvd_of_mem_divisors hℓ)

#print axioms periodicMean_sub_le
#print axioms condExceedProb_sub_le_dyadicMean
#print axioms exceedInd_le_tsum_scaledCoverPotential
#print axioms condExceedProb_le_cost
#print axioms condExceedProb_le_optimizedLogCoverCost
#print axioms sup_condExceedProb_le_optimizedLogCoverCost

end ErdosProblems.Erdos257.PaperCompleteR21

end
