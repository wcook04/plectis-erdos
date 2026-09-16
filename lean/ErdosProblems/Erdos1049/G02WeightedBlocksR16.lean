import ErdosProblems.Erdos1049.G02ArithmeticR16
import ErdosProblems.Erdos1049.WeightedFloorBlocksR12
import ErdosProblems.Erdos1049.SourceHeightRateR14
import Mathlib

/-! Literal thirteen-block supplier: the complement degree has quadratic rate. -/
namespace ErdosProblems.Erdos1049.PaperR16
open Finset Filter Asymptotics
open PaperR11 PaperR12
open scoped BigOperators Topology
set_option maxHeartbeats 4000000

/-- Additive quadratic rate. This is deliberately not a logarithmic rate. -/
def QuadRateR16 (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (fun n => f n - a * PaperR9.sqScale n) =o[atTop] PaperR9.sqScale

noncomputable def trigammaSeriesR16 (u : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + u)^2
noncomputable def blockKernelR16 (u v : ℝ) (k : ℕ) : ℝ :=
  1 / ((k : ℝ) + u)^2 - 1 / ((k : ℝ) + v)^2
noncomputable def sourceJR16 : ℝ :=
  ∑ uv ∈ sourceIntervals,
    (trigammaSeriesR16 (uv.1 : ℝ) - trigammaSeriesR16 (uv.2 : ℝ))
noncomputable def sourceJPrefixR16 (N : ℕ) : ℝ :=
  ∑ uv ∈ sourceIntervals, ∑ k ∈ range N,
    blockKernelR16 (uv.1 : ℝ) (uv.2 : ℝ) k
noncomputable def complementDegreeR16 (n : ℕ) : ℝ :=
  ((sourceComplement n).natDegree : ℝ)
noncomputable def sourceGammaR16 : ℝ := totientConstantR16 * (225 - sourceJR16)
noncomputable def sourceC0R16 : ℝ := 266 - sourceGammaR16
noncomputable def sourceC1R16 : ℝ := 1091 / 2
noncomputable def sourceDeltaR16 : ℝ := sourceC1R16 - sourceC0R16

lemma sourceIntervals_minR16 (uv : ℚ × ℚ) (huv : uv ∈ sourceIntervals) :
    (1/14 : ℝ) ≤ uv.1 := by
  norm_num [sourceIntervals] at huv
  rcases huv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma sourceIntervals_separatedR16 :
    ∀ uv ∈ sourceIntervals, ∀ wx ∈ sourceIntervals,
      uv = wx ∨ uv.2 ≤ wx.1 ∨ wx.2 ≤ uv.1 := by
  simp only [sourceIntervals, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq]
  norm_num

lemma sourceIntervals_uniqueR16 (uv wx : ℚ × ℚ)
    (huv : uv ∈ sourceIntervals) (hwx : wx ∈ sourceIntervals)
    (x : ℝ) (hx : (uv.1 : ℝ) ≤ x ∧ x < (uv.2 : ℝ))
    (hy : (wx.1 : ℝ) ≤ x ∧ x < (wx.2 : ℝ)) : uv = wx := by
  rcases sourceIntervals_separatedR16 uv huv wx hwx with h | h | h
  · exact h
  · have h' : (uv.2 : ℝ) ≤ wx.1 := by exact_mod_cast h
    exfalso; linarith [hx.1, hx.2, hy.1, hy.2]
  · have h' : (wx.2 : ℝ) ≤ uv.1 := by exact_mod_cast h
    exfalso; linarith [hx.1, hx.2, hy.1, hy.2]

lemma trigamma_summableR16 (u : ℝ) (hu : 0 < u) :
    Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + u)^2) := by
  have h := (Real.summable_one_div_nat_add_rpow u (2 : ℝ)).2 (by norm_num)
  simpa only [Real.rpow_two, sq_abs] using h

lemma blockKernel_summableR16 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    Summable (blockKernelR16 u v) :=
  (trigamma_summableR16 u hu).sub (trigamma_summableR16 v hv)

lemma blockKernel_nonnegR16 (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (k : ℕ) :
    0 ≤ blockKernelR16 u v k := by
  unfold blockKernelR16
  apply sub_nonneg.mpr
  have hku : 0 < (k : ℝ) + u := by positivity
  apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hku)
  nlinarith

lemma trigamma_differenceR16 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (∑' k, blockKernelR16 u v k) = trigammaSeriesR16 u - trigammaSeriesR16 v := by
  exact (trigamma_summableR16 u hu).tsum_sub (trigamma_summableR16 v hv)

lemma sourceJ_nonnegR16 : 0 ≤ sourceJR16 := by
  unfold sourceJR16
  apply sum_nonneg
  intro uv huv
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  rw [← trigamma_differenceR16 _ _ hu (hu.trans huv')]
  exact tsum_nonneg (blockKernel_nonnegR16 _ _ hu huv'.le)

lemma telescope_rangeR16 (f : ℕ → ℝ) (K N : ℕ) :
    (∑ k ∈ range N, (f (k+K) - f (k+K+1))) = f K - f (N+K) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      convert (show f K - f (N+K) + (f (N+K) - f (N+K+1)) =
        f K - f (N+K+1) by ring) using 1 <;> congr 2 <;> omega

lemma blockKernel_tailR16 (u v : ℝ) (hu : 0 < u) (huv : u < v)
    (hv : v ≤ 1) (K : ℕ) :
    0 ≤ (∑' k : ℕ, blockKernelR16 u v (k+K)) ∧
      (∑' k : ℕ, blockKernelR16 u v (k+K)) ≤ 1 / ((K : ℝ)+u)^2 := by
  have hs := (summable_nat_add_iff K).2
    (blockKernel_summableR16 u v hu (hu.trans huv))
  constructor
  · exact tsum_nonneg (fun k => blockKernel_nonnegR16 u v hu huv.le _)
  · apply le_of_tendsto' hs.hasSum.tendsto_sum_nat
    intro N
    calc
      _ ≤ ∑ k ∈ range N,
          (1 / (((k+K : ℕ) : ℝ)+u)^2 -
            1 / (((k+K+1 : ℕ) : ℝ)+u)^2) := by
        apply sum_le_sum
        intro k hk
        unfold blockKernelR16
        apply sub_le_sub_left
        have hx : (0 : ℝ) ≤ ((k+K : ℕ) : ℝ) := Nat.cast_nonneg _
        have ha : 0 < ((k+K : ℕ) : ℝ) + v := by linarith
        apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
        have hle : ((k+K : ℕ) : ℝ) + v ≤ ((k+K+1 : ℕ) : ℝ) + u := by
          push_cast
          linarith
        exact pow_le_pow_left₀ ha.le hle 2
      _ = 1 / ((K : ℝ)+u)^2 - 1 / (((N+K : ℕ) : ℝ)+u)^2 := by
        exact telescope_rangeR16 (fun j => 1 / ((j : ℝ)+u)^2) K N
      _ ≤ _ := sub_le_self _ (by positivity)

lemma sourceJ_tail_identityR16 (N : ℕ) :
    sourceJR16 - sourceJPrefixR16 N =
      ∑ uv ∈ sourceIntervals, ∑' k : ℕ,
        blockKernelR16 (uv.1 : ℝ) (uv.2 : ℝ) (k+N) := by
  unfold sourceJR16 sourceJPrefixR16
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro uv huv
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  have hs := blockKernel_summableR16 _ _ hu (hu.trans huv')
  have h := hs.sum_add_tsum_nat_add N
  rw [trigamma_differenceR16 _ _ hu (hu.trans huv')] at h
  linarith

/-- Quantified main-term tail; no unproved interchange of limits. -/
theorem sourceJ_tail_boundR16 (N : ℕ) :
    0 ≤ sourceJR16 - sourceJPrefixR16 N ∧
      sourceJR16 - sourceJPrefixR16 N ≤ 13 / ((N : ℝ)+1/14)^2 := by
  rw [sourceJ_tail_identityR16]
  constructor
  · apply sum_nonneg
    intro uv huv
    obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
    exact (blockKernel_tailR16 _ _ hu huv' hv N).1
  · calc
      _ ≤ ∑ uv ∈ sourceIntervals, (1 : ℝ)/((N : ℝ)+1/14)^2 := by
        apply sum_le_sum
        intro uv huv
        obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
        apply (blockKernel_tailR16 _ _ hu huv' hv N).2.trans
        have hmin := sourceIntervals_minR16 uv huv
        apply div_le_div_of_nonneg_left (by norm_num)
          (by positivity : (0 : ℝ) < ((N : ℝ)+1/14)^2)
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      _ = _ := by simp [sourceIntervals_card]; ring

/-- The only block index is the integer part; the natural cut-off is <n. -/
lemma fract_block_natR16 (n l : ℕ) (hl : 1 ≤ l) (u v : ℝ)
    (hu : 0 < u) (huv : u < v) (hv : v ≤ 1) :
    (u ≤ Int.fract ((n : ℝ)/l) ∧ Int.fract ((n : ℝ)/l) < v) ↔
      ∃ k ∈ range n, (n : ℝ)/((k : ℝ)+v) < l ∧
        (l : ℝ) ≤ (n : ℝ)/((k : ℝ)+u) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  constructor
  · intro hx
    have hf0 : 0 ≤ ⌊(n : ℝ)/l⌋ := Int.floor_nonneg.mpr (div_nonneg hn0 hl0.le)
    let k : ℕ := ⌊(n : ℝ)/l⌋.toNat
    have hkZ : (k : ℤ) = ⌊(n : ℝ)/l⌋ := Int.toNat_of_nonneg hf0
    have hkR : (k : ℝ) = (⌊(n : ℝ)/l⌋ : ℝ) := by exact_mod_cast hkZ
    have hb : (k : ℝ)+u ≤ (n : ℝ)/l ∧ (n : ℝ)/l < (k : ℝ)+v := by
      change u ≤ (n : ℝ)/l - (⌊(n : ℝ)/l⌋ : ℝ) ∧
        (n : ℝ)/l - (⌊(n : ℝ)/l⌋ : ℝ) < v at hx
      rw [hkR]
      constructor <;> linarith [hx.1, hx.2]
    have hdiv : (n : ℝ)/l ≤ n := by
      apply (div_le_iff₀ hl0).2
      nlinarith
    have hkn : k < n := by exact_mod_cast (show (k : ℝ) < n by linarith [hb.1])
    refine ⟨k, mem_range.mpr hkn, ?_⟩
    exact (reciprocal_block_iff n l k u v hl0 (Nat.cast_nonneg _) hu huv).1 hb
  · rintro ⟨k, hk, hb⟩
    have hh := (reciprocal_block_iff n l k u v hl0 (Nat.cast_nonneg _) hu huv).2 hb
    have hf : ⌊(n : ℝ)/l⌋ = (k : ℤ) := Int.floor_eq_iff.mpr
      ⟨by push_cast; linarith [hh.1], by push_cast; linarith [hh.2]⟩
    change u ≤ (n : ℝ)/l - (⌊(n : ℝ)/l⌋ : ℝ) ∧
      (n : ℝ)/l - (⌊(n : ℝ)/l⌋ : ℝ) < v
    rw [hf]
    push_cast
    constructor <;> linarith [hh.1, hh.2]

lemma block_index_uniqueR16 (n l k j : ℕ) (hl : 1 ≤ l)
    (u v a b : ℝ) (hu : 0 < u) (huv : u < v) (hv : v ≤ 1)
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hk : (n : ℝ)/((k : ℝ)+v) < l ∧ (l : ℝ) ≤ (n : ℝ)/((k : ℝ)+u))
    (hj : (n : ℝ)/((j : ℝ)+b) < l ∧ (l : ℝ) ≤ (n : ℝ)/((j : ℝ)+a)) : k = j := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have h1 := (reciprocal_block_iff n l k u v hl0 (Nat.cast_nonneg _) hu huv).2 hk
  have h2 := (reciprocal_block_iff n l j a b hl0 (Nat.cast_nonneg _) ha hab).2 hj
  have hf1 : ⌊(n : ℝ)/l⌋ = (k : ℤ) := Int.floor_eq_iff.mpr
    ⟨by push_cast; linarith [h1.1], by push_cast; linarith [h1.2]⟩
  have hf2 : ⌊(n : ℝ)/l⌋ = (j : ℤ) := Int.floor_eq_iff.mpr
    ⟨by push_cast; linarith [h2.1], by push_cast; linarith [h2.2]⟩
  omega

lemma finite_prefix_eq_totientR16 (N : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hxN : x ≤ N) : (finiteTotientPrefix N x : ℝ) = totientPrefixR16 x := by
  classical
  have hfloor : ⌊x⌋₊ ≤ N := by
    have h := Nat.floor_mono hxN
    simpa using h
  have hset : (Icc 1 N).filter (fun l : ℕ => (l : ℝ) ≤ x) = Icc 1 ⌊x⌋₊ := by
    ext l
    simp only [mem_filter, mem_Icc, ← Nat.le_floor_iff hx]
    omega
  unfold finiteTotientPrefix totientPrefixR16
  push_cast
  rw [← sum_filter, hset]

lemma reciprocal_endpoint_capR16 (n k : ℕ) (uv : ℚ × ℚ)
    (huv : uv ∈ sourceIntervals) :
    0 ≤ (n : ℝ)/((k : ℝ)+(uv.2 : ℝ)) ∧
    (n : ℝ)/((k : ℝ)+(uv.2 : ℝ)) ≤ (n : ℝ)/((k : ℝ)+(uv.1 : ℝ)) ∧
    (n : ℝ)/((k : ℝ)+(uv.1 : ℝ)) ≤ 14*(n : ℝ) := by
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  have hmin := sourceIntervals_minR16 uv huv
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  constructor
  · exact div_nonneg hn0 (by linarith)
  constructor
  · exact div_le_div_of_nonneg_left hn0 (by positivity) (by linarith)
  · apply (div_le_iff₀ (by positivity : 0 < (k : ℝ)+(uv.1 : ℝ))).2
    have hm := mul_le_mul_of_nonneg_left hmin hn0
    have hk := mul_nonneg hn0 hk0
    nlinarith

/-- For each l, exactly one source interval and one block can contribute. -/
lemma weighted_indicator_blocksR16 (n l : ℕ) (hl : 1 ≤ l) :
    (if ∃ uv ∈ sourceIntervals,
        (uv.1 : ℝ) ≤ Int.fract ((n : ℝ)/l) ∧
          Int.fract ((n : ℝ)/l) < (uv.2 : ℝ)
      then (l.totient : ℝ) else 0) =
    ∑ uv ∈ sourceIntervals, ∑ k ∈ range n,
      if (n : ℝ)/((k : ℝ)+(uv.2 : ℝ)) < l ∧
        (l : ℝ) ≤ (n : ℝ)/((k : ℝ)+(uv.1 : ℝ))
      then (l.totient : ℝ) else 0 := by
  classical
  by_cases hex : ∃ uv ∈ sourceIntervals,
      (uv.1 : ℝ) ≤ Int.fract ((n : ℝ)/l) ∧
        Int.fract ((n : ℝ)/l) < (uv.2 : ℝ)
  · rw [if_pos hex]
    obtain ⟨uv, huv, hx⟩ := hex
    obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
    obtain ⟨k, hk, hblock⟩ := (fract_block_natR16 n l hl _ _ hu huv' hv).1 hx
    symm
    calc
      _ = ∑ j ∈ range n,
          if (n : ℝ)/((j : ℝ)+(uv.2 : ℝ)) < l ∧
            (l : ℝ) ≤ (n : ℝ)/((j : ℝ)+(uv.1 : ℝ))
          then (l.totient : ℝ) else 0 := by
        apply sum_eq_single uv
        · intro wx hwx hne
          apply sum_eq_zero
          intro j hj
          apply if_neg
          intro hb
          obtain ⟨ha, hab, hb1⟩ := sourceIntervals_bounds wx hwx
          have hxx := (fract_block_natR16 n l hl _ _ ha hab hb1).2 ⟨j, hj, hb⟩
          exact hne (sourceIntervals_uniqueR16 wx uv hwx huv _ hxx hx)
        · intro hn; exact (hn huv).elim
      _ = l.totient := by
        rw [sum_eq_single k]
        · simp [hblock]
        · intro j hj hjk
          apply if_neg
          intro hb
          exact hjk (block_index_uniqueR16 n l j k hl _ _ _ _ hu huv' hv hu huv' hv hb hblock)
        · intro hn; exact (hn hk).elim
  · rw [if_neg hex]
    symm
    apply sum_eq_zero
    intro uv huv
    apply sum_eq_zero
    intro k hk
    apply if_neg
    intro hb
    obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
    exact hex ⟨uv, huv, (fract_block_natR16 n l hl _ _ hu huv' hv).2 ⟨k, hk, hb⟩⟩

/-- Exact finite decomposition of the literal R12 weighted sum. -/
theorem actual_weighted_blocksR16 (n : ℕ) :
    (actualWeightedTotientSum n : ℝ) =
      ∑ uv ∈ sourceIntervals, ∑ k ∈ range n,
        (totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.1 : ℝ))) -
          totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.2 : ℝ)))) := by
  classical
  rw [actual_weighted_totient_indicator]
  push_cast
  have he : (∑ l ∈ Icc 1 (15*n),
      if ∃ uv ∈ sourceIntervals,
        (uv.1 : ℝ) ≤ Int.fract ((n : ℝ)/l) ∧
          Int.fract ((n : ℝ)/l) < (uv.2 : ℝ)
      then (l.totient : ℝ) else 0) =
      ∑ l ∈ Icc 1 (15*n), ∑ uv ∈ sourceIntervals, ∑ k ∈ range n,
        if (n : ℝ)/((k : ℝ)+(uv.2 : ℝ)) < l ∧
          (l : ℝ) ≤ (n : ℝ)/((k : ℝ)+(uv.1 : ℝ))
        then (l.totient : ℝ) else 0 := by
    apply sum_congr rfl
    intro l hl
    exact weighted_indicator_blocksR16 n l (mem_Icc.mp hl).1
  rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro uv huv
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  have hcap := reciprocal_endpoint_capR16 n k uv huv
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (actual_reciprocal_totient_block (15*n) n k uv.1 uv.2
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hu huv')
  push_cast at h
  rw [finite_prefix_eq_totientR16 _ _ (hcap.1.trans hcap.2.1)
      (by push_cast; nlinarith [hcap.2.2, Nat.cast_nonneg (α := ℝ) n]),
    finite_prefix_eq_totientR16 _ _ hcap.1
      (by push_cast; nlinarith [hcap.2.1, hcap.2.2, Nat.cast_nonneg (α := ℝ) n])] at h
  exact h

lemma block_prefix_errorR16 (n k : ℕ) (uv : ℚ × ℚ) (huv : uv ∈ sourceIntervals) :
    |(totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.1 : ℝ))) -
       totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.2 : ℝ)))) -
      totientConstantR16 * (n : ℝ)^2 * blockKernelR16 uv.1 uv.2 k| ≤
      4 * (n : ℝ) * (1+Real.log (1+14*(n : ℝ))) *
        (1/((k : ℝ)+(uv.1 : ℝ))) := by
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  have hcap := reciprocal_endpoint_capR16 n k uv huv
  let x : ℝ := (n : ℝ)/((k : ℝ)+(uv.1 : ℝ))
  let y : ℝ := (n : ℝ)/((k : ℝ)+(uv.2 : ℝ))
  have hx0 : 0 ≤ x := hcap.1.trans hcap.2.1
  have hy0 : 0 ≤ y := hcap.1
  have hyx : y ≤ x := hcap.2.1
  have hxm : x ≤ 14*(n : ℝ) := hcap.2.2
  have hx := summatory_totient_errorR16 x hx0
  have hy := summatory_totient_errorR16 y hy0
  have hxlog : Real.log (1+x) ≤ Real.log (1+14*(n : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hylog : Real.log (1+y) ≤ Real.log (1+14*(n : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hxE : totientErrorR16 x ≤ 2*x*(1+Real.log (1+14*(n : ℝ))) := by
    unfold totientErrorR16
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hyE : totientErrorR16 y ≤ 2*x*(1+Real.log (1+14*(n : ℝ))) := by
    unfold totientErrorR16
    apply mul_le_mul
    · linarith
    · linarith
    · exact add_nonneg zero_le_one (Real.log_nonneg (by linarith))
    · positivity
  have he : (totientPrefixR16 x - totientPrefixR16 y) -
      totientConstantR16*(n : ℝ)^2*blockKernelR16 uv.1 uv.2 k =
      (totientPrefixR16 x - totientConstantR16*x^2) -
        (totientPrefixR16 y - totientConstantR16*y^2) := by
    dsimp [x, y, blockKernelR16]
    have hku : (k : ℝ)+(uv.1 : ℝ) ≠ 0 := (by positivity : 0 < (k : ℝ)+(uv.1 : ℝ)).ne'
    have hkv : (k : ℝ)+(uv.2 : ℝ) ≠ 0 :=
      (by linarith [Nat.cast_nonneg (α := ℝ) k] : 0 < (k : ℝ)+(uv.2 : ℝ)).ne'
    field_simp [hku, hkv]
    <;> ring
  change |(totientPrefixR16 x-totientPrefixR16 y)-_| ≤ _
  rw [he]
  calc
    _ ≤ |totientPrefixR16 x-totientConstantR16*x^2| +
        |totientPrefixR16 y-totientConstantR16*y^2| := abs_sub _ _
    _ ≤ totientErrorR16 x + totientErrorR16 y := add_le_add hx hy
    _ ≤ 4*x*(1+Real.log (1+14*(n : ℝ))) := by linarith
    _ = _ := by dsimp [x]; ring

lemma reciprocal_range_boundR16 (n : ℕ) (hn : 1 ≤ n) (uv : ℚ × ℚ)
    (huv : uv ∈ sourceIntervals) :
    (∑ k ∈ range n, (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ))) ≤
      15 * PaperR14.sourceLogScale n := by
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  have hmin := sourceIntervals_minR16 uv huv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpad : (∑ k ∈ range n, (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ))) ≤
      ∑ k ∈ range (n+1), (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ)) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk; exact mem_range.mpr (by have := mem_range.mp hk; omega)
    · intro k hk hnot; positivity
  have hset : range (n+1) = insert 0 (Icc 1 n) := by
    ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
  have hzero : (1 : ℝ)/(uv.1 : ℝ) ≤ 14 := by
    apply (div_le_iff₀ hu).2
    nlinarith
  have hsum : (∑ k ∈ Icc 1 n, (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ))) ≤
      ∑ k ∈ Icc 1 n, (1 : ℝ)/(k : ℝ) := by
    apply sum_le_sum
    intro k hk
    have hk0 : (0 : ℝ) < k := by
      exact_mod_cast (show 0 < k by have := (mem_Icc.mp hk).1; omega)
    exact div_le_div_of_nonneg_left zero_le_one hk0 (by linarith)
  rw [hset, sum_insert (by simp)] at hpad
  simp only [Nat.cast_zero, zero_add] at hpad
  have hh := harmonic_Icc_boundR16 n
  have hl : Real.log n ≤ Real.log ((n : ℝ)+2) := Real.log_le_log hn0 (by linarith)
  have hl0 : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  unfold PaperR14.sourceLogScale
  nlinarith

lemma source_scaled_log_boundR16 (a n : ℕ) (ha : 1 ≤ a) :
    1 + Real.log (1+(a : ℝ)*(n : ℝ)) ≤ (a : ℝ) * PaperR14.sourceLogScale n := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hlog := Real.log_le_log (by positivity : 0 < 1+(a : ℝ)*(n : ℝ))
    (show 1+(a : ℝ)*(n : ℝ) ≤ (a : ℝ)*((n : ℝ)+2) by nlinarith)
  rw [Real.log_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (n : ℝ)+2 ≠ 0)] at hlog
  have haLog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < a by linarith)
  have hnLog : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by linarith)
  unfold PaperR14.sourceLogScale
  nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hnLog]

lemma actual_weighted_finite_errorR16 (n : ℕ) (hn : 1 ≤ n) :
    |(actualWeightedTotientSum n : ℝ) -
      totientConstantR16*(n : ℝ)^2*sourceJPrefixR16 n| ≤
      10920*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
  rw [actual_weighted_blocksR16]
  unfold sourceJPrefixR16
  rw [mul_sum, ← sum_sub_distrib]
  have hbound : ∀ uv ∈ sourceIntervals,
      |(∑ k ∈ range n,
        (totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.1 : ℝ))) -
          totientPrefixR16 ((n : ℝ)/((k : ℝ)+(uv.2 : ℝ))))) -
        totientConstantR16*(n : ℝ)^2*
          (∑ k ∈ range n, blockKernelR16 uv.1 uv.2 k)| ≤
      840*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
    intro uv huv
    rw [mul_sum, ← sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k ∈ range n,
          4*(n : ℝ)*(1+Real.log (1+14*(n : ℝ))) *
            (1/((k : ℝ)+(uv.1 : ℝ))) :=
        sum_le_sum (fun k hk => block_prefix_errorR16 n k uv huv)
      _ = 4*(n : ℝ)*(1+Real.log (1+14*(n : ℝ))) *
          (∑ k ∈ range n, (1 : ℝ)/((k : ℝ)+(uv.1 : ℝ))) := by rw [mul_sum]
      _ ≤ 4*(n : ℝ)*(1+Real.log (1+14*(n : ℝ))) *
          (15*PaperR14.sourceLogScale n) := by
        apply mul_le_mul_of_nonneg_left (reciprocal_range_boundR16 n hn uv huv)
        have hl := Real.log_nonneg
          (show (1 : ℝ) ≤ 1+14*(n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])
        exact mul_nonneg (by positivity) (by linarith)
      _ ≤ 840*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
        have hlog := source_scaled_log_boundR16 14 n (by norm_num)
        simp only [Nat.cast_ofNat] at hlog
        have hL := PaperR14.sourceLogScale_ge_one n
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        have h := mul_le_mul_of_nonneg_left hlog
          (show 0 ≤ 60*(n : ℝ)*PaperR14.sourceLogScale n by positivity)
        nlinarith
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ uv ∈ sourceIntervals, 840*(n : ℝ)*PaperR14.sourceLogScale n^2 :=
      sum_le_sum hbound
    _ = _ := by simp [sourceIntervals_card]; ring

/-- The n-dependent weighted sum has a genuine quantitative error. -/
theorem actual_weighted_totient_errorR16 (n : ℕ) (hn : 1 ≤ n) :
    |(actualWeightedTotientSum n : ℝ) -
      (totientConstantR16*sourceJR16)*(n : ℝ)^2| ≤
      10927*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
  have hfinite := actual_weighted_finite_errorR16 n hn
  obtain ⟨ht0, ht⟩ := sourceJ_tail_boundR16 n
  have hc0 := totient_constant_posR16.le
  have hc := totient_constant_le_halfR16
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := PaperR14.sourceLogScale_ge_one n
  have hLs : 1 ≤ PaperR14.sourceLogScale n^2 := one_le_pow₀ hL
  have hsmall : (n : ℝ)^2 * (13/((n : ℝ)+1/14)^2) ≤ 13 := by
    have hd : (0 : ℝ) < ((n : ℝ)+1/14)^2 := by positivity
    have h : (13*(n : ℝ)^2) / ((n : ℝ)+1/14)^2 ≤ 13 := by
      apply (div_le_iff₀ hd).2
      nlinarith
    convert h using 1 <;> ring
  have htail : |totientConstantR16*(n : ℝ)^2*(sourceJR16-sourceJPrefixR16 n)| ≤
      7*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
    rw [abs_of_nonneg (by positivity)]
    have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ (n : ℝ)^2 by positivity)
    have hc' := mul_le_mul_of_nonneg_left (ht'.trans hsmall) hc0
    have hnL := mul_le_mul_of_nonneg_left hLs (show (0 : ℝ) ≤ n by positivity)
    nlinarith
  have he : (actualWeightedTotientSum n : ℝ) -
      (totientConstantR16*sourceJR16)*(n : ℝ)^2 =
      ((actualWeightedTotientSum n : ℝ) - totientConstantR16*(n : ℝ)^2*sourceJPrefixR16 n) -
        totientConstantR16*(n : ℝ)^2*(sourceJR16-sourceJPrefixR16 n) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by nlinarith [hfinite, htail])

/-- Turns the already-proved R14 logarithmic envelope into little-o. -/
lemma littleO_of_logEnvelopeR16 (f : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ᶠ n : ℕ in atTop, |f n| ≤ C*(n : ℝ)*PaperR14.sourceLogScale n^2) :
    f =o[atTop] PaperR9.sqScale := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hf, PaperR14.source_n_log_squared_isLittleO.def (div_pos hε hC)] with n hn he
  have hL : 0 ≤ (n : ℝ)*PaperR14.sourceLogScale n^2 := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hL,
    abs_of_nonneg (PaperR9.sqScale_nonneg n)] at he ⊢
  calc
    |f n| ≤ C*((n : ℝ)*PaperR14.sourceLogScale n^2) := by nlinarith [hn]
    _ ≤ C*((ε/C)*PaperR9.sqScale n) := mul_le_mul_of_nonneg_left he hC.le
    _ = ε*PaperR9.sqScale n := by field_simp [hC.ne']

theorem actual_weighted_totient_rateR16 :
    QuadRateR16 (fun n => (actualWeightedTotientSum n : ℝ))
      (totientConstantR16*sourceJR16) := by
  apply littleO_of_logEnvelopeR16 _ 10927 (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa [PaperR9.sqScale] using actual_weighted_totient_errorR16 n hn

lemma total_totient_errorR16 (a n : ℕ) (ha : 1 ≤ a) :
    |totientPrefixR16 ((a : ℝ)*(n : ℝ)) -
      (totientConstantR16*(a : ℝ)^2)*(n : ℝ)^2| ≤
      (2*(a : ℝ)^2)*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
  have h := summatory_totient_errorR16 ((a : ℝ)*(n : ℝ)) (by positivity)
  have hl := source_scaled_log_boundR16 a n ha
  have hL := PaperR14.sourceLogScale_ge_one n
  have hLs : PaperR14.sourceLogScale n ≤ PaperR14.sourceLogScale n^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*(a : ℝ)*(n : ℝ) by positivity)
  have hb' := mul_le_mul_of_nonneg_left hLs (show 0 ≤ 2*(a : ℝ)^2*(n : ℝ) by positivity)
  unfold totientErrorR16 at h
  have he : totientConstantR16*((a : ℝ)*(n : ℝ))^2 =
      (totientConstantR16*(a : ℝ)^2)*(n : ℝ)^2 := by ring
  rw [he] at h
  exact h.trans (by nlinarith)

lemma actual_complement_degree_identityR16 (n : ℕ) :
    complementDegreeR16 n = totientPrefixR16 (15*(n : ℝ)) -
      (actualWeightedTotientSum n : ℝ) := by
  classical
  unfold complementDegreeR16
  rw [(sourceComplement_monic_degree n).2]
  have hf : ⌊15*(n : ℝ)⌋₊ = 15*n := by
    exact_mod_cast (Nat.floor_natCast (15 * n) : ⌊((15 * n : ℕ) : ℝ)⌋₊ = 15 * n)
  unfold totientPrefixR16 actualWeightedTotientSum
  rw [hf]
  push_cast
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro l hl
  rcases sourceWeight_zero_or_one n l with h | h <;> simp [h]

theorem actual_complement_degree_errorR16 (n : ℕ) (hn : 1 ≤ n) :
    |complementDegreeR16 n-sourceGammaR16*(n : ℝ)^2| ≤
      11377*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
  rw [actual_complement_degree_identityR16]
  have ht := total_totient_errorR16 15 n (by norm_num)
  have hw := actual_weighted_totient_errorR16 n hn
  norm_num at ht
  have he : (totientPrefixR16 (15*(n : ℝ))-(actualWeightedTotientSum n : ℝ)) -
      sourceGammaR16*(n : ℝ)^2 =
      (totientPrefixR16 (15*(n : ℝ))-(totientConstantR16*225)*(n : ℝ)^2) -
        ((actualWeightedTotientSum n : ℝ)-(totientConstantR16*sourceJR16)*(n : ℝ)^2) := by
    unfold sourceGammaR16
    ring
  rw [he]
  exact (abs_sub _ _).trans (by nlinarith [ht, hw])

theorem actual_complement_degree_rateR16 :
    QuadRateR16 complementDegreeR16 sourceGammaR16 := by
  apply littleO_of_logEnvelopeR16 _ 11377 (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa [PaperR9.sqScale] using actual_complement_degree_errorR16 n hn

lemma QuadRateR16.nonneg {f : ℕ → ℝ} {a : ℝ}
    (hf : QuadRateR16 f a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n) : 0 ≤ a := by
  by_contra h
  have ha : a < 0 := lt_of_not_ge h
  have he : 0 < -a/2 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hf.def he).and (h0.and (eventually_ge_atTop (1 : ℕ))))
  obtain ⟨hb, hnon, hn⟩ := hN N le_rfl
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (PaperR9.sqScale_nonneg N)] at hb
  have hs : 0 < PaperR9.sqScale N := by unfold PaperR9.sqScale; positivity
  have hx := (le_abs_self (f N-a*PaperR9.sqScale N)).trans hb
  nlinarith

lemma sourceGamma_nonnegR16 : 0 ≤ sourceGammaR16 :=
  actual_complement_degree_rateR16.nonneg
    (Filter.Eventually.of_forall (fun n => Nat.cast_nonneg _))

lemma sourceGamma_leR16 : sourceGammaR16 ≤ 225/2 := by
  have hc := totient_constant_le_halfR16
  have hc0 := totient_constant_posR16.le
  have hJ := sourceJ_nonnegR16
  unfold sourceGammaR16
  nlinarith [mul_nonneg hc0 hJ]

lemma sourceC0_posR16 : 0 < sourceC0R16 := by
  have h := sourceGamma_leR16
  unfold sourceC0R16
  linarith

lemma sourceDelta_posR16 : 0 < sourceDeltaR16 := by
  have h := sourceGamma_nonnegR16
  unfold sourceDeltaR16 sourceC1R16 sourceC0R16
  linarith

lemma source_rate_constantsR16 :
    sourceDeltaR16 + sourceC0R16 = sourceC1R16 ∧
      sourceGammaR16 - 266 = -sourceC0R16 := by
  unfold sourceDeltaR16 sourceC0R16
  constructor <;> ring

end ErdosProblems.Erdos1049.PaperR16
