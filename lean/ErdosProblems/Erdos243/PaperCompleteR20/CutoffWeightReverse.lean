import ErdosProblems.Erdos243.PaperCompleteR20.CutoffWeightCriterion

/-!
# Erdős 243: reverse weight criterion

The main technical point is to regroup an arbitrary enumeration of positive
integer locations, including repeated locations and infinite fibres, into its
exact-site masses.  The identities are proved in `ENNReal`, so they remain
valid before any finiteness has been established.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

/-- Total mass carried by the fibre whose location is exactly `n`. -/
def exactSiteMass (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑' j : u ⁻¹' {n}, w j.1

/-- Regrouping by exact integer location is valid even for infinite fibres. -/
theorem tsum_exactSiteMass (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) :
    (∑' n : ℕ, exactSiteMass u w n) = ∑' j : ℕ, w j := by
  exact ENNReal.tsum_fiberwise w u

/-- A prefix mass is the finite sum of its exact-site masses. -/
theorem cutoffPrefixMass_eq_sum_exactSiteMass
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (N : ℕ) :
    cutoffPrefixMass u w N =
      ∑ n ∈ Finset.range (N + 1), exactSiteMass u w n := by
  let v : ℕ → ℝ≥0∞ := fun j => if u j ≤ N then w j else 0
  calc
    cutoffPrefixMass u w N = ∑' j : ℕ, v j := by rfl
    _ = ∑' n : ℕ, ∑' j : u ⁻¹' {n}, v j.1 :=
      (ENNReal.tsum_fiberwise v u).symm
    _ = ∑' n : ℕ, if n ≤ N then exactSiteMass u w n else 0 := by
      apply tsum_congr
      intro n
      by_cases hn : n ≤ N
      · rw [if_pos hn]
        apply tsum_congr
        intro j
        simp only [v]
        have hj : u j.1 = n := j.2
        simp [hj, hn]
      · rw [if_neg hn]
        apply ENNReal.tsum_eq_zero.mpr
        intro j
        simp only [v]
        have hj : u j.1 = n := j.2
        simp [hj, hn]
    _ = ∑ n ∈ Finset.range (N + 1), exactSiteMass u w n := by
      rw [tsum_eq_sum]
      · apply Finset.sum_congr rfl
        intro n hn
        simp only [Finset.mem_range] at hn
        simp [Nat.le_of_lt_succ hn]
      · intro n hn
        simp only [Finset.mem_range, not_lt] at hn
        simp [show ¬ n ≤ N by omega]

/-- Fibrewise regrouping of weighted samples.  No injectivity of `u` and no
fibre-finiteness assumption is needed. -/
theorem weighted_tsum_eq_exactSiteMass
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (g : ℕ → ℝ≥0∞) :
    (∑' j : ℕ, w j * g (u j)) =
      ∑' n : ℕ, exactSiteMass u w n * g n := by
  calc
    (∑' j : ℕ, w j * g (u j)) =
        ∑' n : ℕ, ∑' j : u ⁻¹' {n}, w j.1 * g (u j.1) :=
      (ENNReal.tsum_fiberwise (fun j => w j * g (u j)) u).symm
    _ = ∑' n : ℕ, exactSiteMass u w n * g n := by
      apply tsum_congr
      intro n
      rw [exactSiteMass, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro j
      rw [j.2]

/-- If a nonnegative antitone weight has unbounded improper integral, every
integer sample on the paper domain is strictly positive. -/
theorem positive_nat_samples_of_integralUnbounded
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 1))
    (hfnn : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : PaperCompleteR11.IntegralUnbounded f) :
    ∀ n : ℕ, 0 < n → 0 < f n := by
  intro n hn
  have hnonneg : 0 ≤ f n := hfnn n (by exact_mod_cast hn)
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have htail : ∀ m : ℕ, n ≤ m → PaperCompleteR11.natWeight f m = 0 := by
    intro m hnm
    have hm1 : 1 ≤ m := hn.trans_le hnm
    have hle : f m ≤ f n := hf (by change 1 ≤ (n : ℝ); exact_mod_cast (show 1 ≤ n by omega))
      (by change 1 ≤ (m : ℝ); exact_mod_cast hm1)
      (by exact_mod_cast hnm)
    have hm0 : f m = 0 := le_antisymm (by simpa only [← hzero] using hle)
      (hfnn m (by exact_mod_cast hm1))
    simp [PaperCompleteR11.natWeight, max_eq_right hm1, hm0]
  have hfinite : (Function.support (PaperCompleteR11.natWeight f)).Finite := by
    apply (Set.finite_Iio n).subset
    intro m hm
    by_contra hmn
    exact hm (htail m (not_lt.mp hmn))
  exact (PaperCompleteR11.natWeight_not_summable_of_integral f hf hfnn hdiv)
    (summable_of_hasFiniteSupport hfinite)

/-- Summability of weighted samples forces every fixed prefix mass to be
finite.  This is the finiteness step required before real partial summation. -/
theorem cutoffPrefixMass_ne_top_of_weighted_summable
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j)
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 1))
    (hfnn : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : PaperCompleteR11.IntegralUnbounded f)
    (hs : Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ))) :
    ∀ N : ℕ, cutoffPrefixMass u (fun j => (w j : ℝ≥0∞)) N ≠ ∞ := by
  intro N
  by_cases hN : N = 0
  · subst N
    have hzero : cutoffPrefixMass u (fun j => (w j : ℝ≥0∞)) 0 = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro j
      simp [cutoffPrefixMass, (hu j).ne']
    simp [hzero]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hfN : 0 < f N := positive_nat_samples_of_integralUnbounded f hf hfnn hdiv N hNpos
    have hsabs : Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ)) := hs
    have hreal_nonneg : ∀ j, 0 ≤ (w j : ℝ) * f (u j : ℕ) := fun j =>
      mul_nonneg (w j).2 (hfnn _ (by exact_mod_cast hu j))
    let q : ℕ → ℝ≥0 := fun j => ⟨(w j : ℝ) * f (u j : ℕ), hreal_nonneg j⟩
    have hq : Summable q := (NNReal.summable_mk hreal_nonneg).mpr hsabs
    have hqtop : (∑' j : ℕ, (q j : ℝ≥0∞)) ≠ ∞ :=
      ENNReal.tsum_coe_ne_top_iff_summable.mpr hq
    have hENN : (∑' j : ℕ, ENNReal.ofReal ((w j : ℝ) * f (u j : ℕ))) ≠ ∞ := by
      convert hqtop using 1
      apply tsum_congr
      intro j
      exact ENNReal.ofReal_eq_coe_nnreal (hreal_nonneg j)
    have hbound : cutoffPrefixMass u (fun j => (w j : ℝ≥0∞)) N *
        ENNReal.ofReal (f N) ≤
        ∑' j : ℕ, ENNReal.ofReal ((w j : ℝ) * f (u j : ℕ)) := by
      rw [cutoffPrefixMass, ← ENNReal.tsum_mul_right]
      apply ENNReal.tsum_le_tsum
      intro j
      by_cases hj : u j ≤ N
      · simp only [if_pos hj]
        have hprod : ENNReal.ofReal ((w j : ℝ) * f (u j : ℕ)) =
            (w j : ℝ≥0∞) * ENNReal.ofReal (f (u j : ℕ)) := by
          calc
            _ = ENNReal.ofReal (w j : ℝ) * ENNReal.ofReal (f (u j : ℕ)) :=
              ENNReal.ofReal_mul (w j).2
            _ = _ := by rw [← ENNReal.coe_nnreal_eq (w j)]
        rw [hprod]
        have hmon : f (N : ℝ) ≤ f (u j : ℝ) := hf
          (by change 1 ≤ (u j : ℝ); exact_mod_cast (Nat.succ_le_of_lt (hu j)))
          (by change 1 ≤ (N : ℝ); exact_mod_cast (show 1 ≤ N by omega))
          (by exact_mod_cast hj)
        gcongr
      · simp [hj]
    intro htop
    rw [htop, ENNReal.top_mul (ENNReal.ofReal_ne_zero_iff.mpr hfN)] at hbound
    exact hENN (top_unique hbound)

/-- Tail telescoping in the indexing convention of the paper. -/
theorem weighted_difference_telescopes_from (f : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N) :
    (N : ℝ) * f N +
        ∑ n ∈ Finset.Ico M N, (n : ℝ) * (f n - f (n + 1)) =
      (M : ℝ) * f M + ∑ n ∈ Finset.Ico (M + 1) (N + 1), f n := by
  induction N with
  | zero =>
      have : M = 0 := by omega
      subst M
      simp
  | succ N ih =>
      by_cases hM : M ≤ N
      · rw [Finset.sum_Ico_succ_top hM, Finset.sum_Ico_succ_top (by omega)]
        have h := ih hM
        push_cast
        nlinarith
      · have : M = N + 1 := by omega
        subst M
        simp

/-- Eventual linear prefix mass forces weighted partial sums to dominate a
cofinal tail of the integer samples. -/
theorem eventual_linear_prefix_forces_tail_bound
    (a f : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ n, 0 ≤ a n) (hf : Antitone f) (hfnn : ∀ n, 0 ≤ f n)
    (M N : ℕ) (hMN : M ≤ N)
    (hprefix : ∀ n, M ≤ n → c * n ≤ finitePrefix a n) :
    c * ((M : ℝ) * f M + ∑ n ∈ Finset.Ico (M + 1) (N + 1), f n) ≤
      ∑ n ∈ Finset.range (N + 1), a n * f n := by
  rw [finite_partial_summation, ← weighted_difference_telescopes_from f M N hMN,
    mul_add, Finset.mul_sum]
  calc
    c * ((N : ℝ) * f N) +
        ∑ n ∈ Finset.Ico M N, c * ((n : ℝ) * (f n - f (n + 1))) ≤
      finitePrefix a N * f N +
        ∑ n ∈ Finset.Ico M N, finitePrefix a n * (f n - f (n + 1)) := by
      apply add_le_add
      · simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hprefix N hMN) (hfnn N)
      · apply Finset.sum_le_sum
        intro n hn
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hprefix n (Finset.mem_Ico.mp hn).1)
            (sub_nonneg.mpr (hf (Nat.le_succ n)))
    _ ≤ finitePrefix a N * f N +
        ∑ n ∈ Finset.range N, finitePrefix a n * (f n - f (n + 1)) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
      · intro n hnrange hnIco
        exact mul_nonneg (by
          unfold finitePrefix
          exact Finset.sum_nonneg (fun i _ => ha i)) (sub_nonneg.mpr (hf (Nat.le_succ n)))


/-- Failure of literal lower-density zero gives a positive finite eventual
linear lower bound. -/
theorem eventually_linear_prefix_of_liminf_ne_zero
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞)
    (hlim : ¬ PrefixLowerDensityZero u w) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ᶠ N : ℕ in atTop,
        c * (N : ℝ≥0∞) ≤ cutoffPrefixMass u w N := by
  let L := Filter.liminf
    (fun N : ℕ => cutoffPrefixMass u w N / (N : ℝ≥0∞)) atTop
  have hL : 0 < L := by
    apply bot_lt_iff_ne_bot.mpr
    simpa only [PrefixLowerDensityZero, L] using hlim
  obtain ⟨c, hc0, hcL⟩ : ∃ c : ℝ≥0∞, 0 < c ∧ c < L := exists_between hL
  have hcfin : c ≠ ∞ := ne_top_of_lt hcL
  have hevent : ∀ᶠ N : ℕ in atTop,
      c < cutoffPrefixMass u w N / (N : ℝ≥0∞) :=
    Filter.eventually_lt_of_lt_liminf hcL
  refine ⟨c, hc0, hcfin, ?_⟩
  filter_upwards [hevent, eventually_gt_atTop 0] with N hratio hN
  exact (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hN.ne'))
    (Or.inl (by simp))).mp hratio.le

/-- An eventual linear lower bound on real prefix sums is incompatible with a
summable weighted sample sequence when the nonnegative antitone samples are
not summable. -/
theorem not_summable_weighted_of_eventual_linear_prefix
    (a f : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hf : Antitone f)
    (hfnn : ∀ n, 0 ≤ f n) (hfdiv : ¬ Summable f)
    (c : ℝ) (hc : 0 < c)
    (hlinear : ∀ᶠ n : ℕ in atTop, c * n ≤ finitePrefix a n) :
    ¬ Summable (fun n => a n * f n) := by
  intro hs
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp hlinear
  let M := max M0 1
  have hMpos : 1 ≤ M := le_max_right _ _
  have hMp : ∀ n, M ≤ n → c * n ≤ finitePrefix a n := fun n hn =>
    hM0 n ((le_max_left M0 1).trans hn)
  let S := ∑' n : ℕ, a n * f n
  have hSnn : 0 ≤ S := tsum_nonneg (fun n => mul_nonneg (ha n) (hfnn n))
  have hpartial : ∀ N, (∑ n ∈ Finset.range (N + 1), a n * f n) ≤ S := by
    intro N
    exact hs.sum_le_tsum (Finset.range (N + 1)) (fun n _ => mul_nonneg (ha n) (hfnn n))
  have hbound : ∀ N, ∑ n ∈ Finset.range N, f n ≤
      (∑ n ∈ Finset.range M, f n) + S / c := by
    intro N
    by_cases hNM : N ≤ M
    · exact (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hNM) (fun n _ _ => hfnn n)).trans
          (le_add_of_nonneg_right (div_nonneg hSnn hc.le))
    · have hMN : M ≤ N - 1 := by omega
      have htail := eventual_linear_prefix_forces_tail_bound a f c hc.le ha hf hfnn
        M (N - 1) hMN hMp
      have htailS : c * ((M : ℝ) * f M +
          ∑ n ∈ Finset.Ico (M + 1) N, f n) ≤ S := by
        simpa only [Nat.sub_add_cancel (show 1 ≤ N by omega)] using
          htail.trans (hpartial (N - 1))
      have hdivle : (M : ℝ) * f M +
          ∑ n ∈ Finset.Ico (M + 1) N, f n ≤ S / c :=
        (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using htailS)
      rw [← Finset.sum_range_add_sum_Ico f (show M + 1 ≤ N by omega),
        Finset.sum_range_succ]
      have hfM : f M ≤ (M : ℝ) * f M := by
        nlinarith [hfnn M, show (1 : ℝ) ≤ M by exact_mod_cast hMpos]
      linarith
  exact hfdiv (summable_of_sum_range_le hfnn hbound)


/-- The exact reverse implication of `res:weights` for arbitrary enumerated
positive integer locations. -/
theorem liminf_eq_zero_of_admissible_real_weight
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j)
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 1))
    (hfnn : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : PaperCompleteR11.IntegralUnbounded f)
    (hs : Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ))) :
    PrefixLowerDensityZero u (fun j => (w j : ℝ≥0∞)) := by
  by_contra hlim
  obtain ⟨cE, hcE0, hcEtop, hcE⟩ := eventually_linear_prefix_of_liminf_ne_zero
    u (fun j => (w j : ℝ≥0∞)) hlim
  let fn : ℕ → ℝ := PaperCompleteR11.natWeight f
  have hfnnN : ∀ n, 0 ≤ fn n := PaperCompleteR11.natWeight_nonneg f hfnn
  have hfanti : Antitone fn := PaperCompleteR11.natWeight_antitone f hf
  have hfnot : ¬ Summable fn :=
    PaperCompleteR11.natWeight_not_summable_of_integral f hf hfnn hdiv
  have hprefixfinite := cutoffPrefixMass_ne_top_of_weighted_summable
    u w hu f hf hfnn hdiv hs
  let a : ℕ → ℝ := fun n => (exactSiteMass u (fun j => (w j : ℝ≥0∞)) n).toReal
  have hasite : ∀ n, exactSiteMass u (fun j => (w j : ℝ≥0∞)) n ≠ ∞ := by
    intro n
    apply ne_top_of_le_ne_top (hprefixfinite n)
    rw [cutoffPrefixMass_eq_sum_exactSiteMass]
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have ha : ∀ n, 0 ≤ a n := fun n => ENNReal.toReal_nonneg
  have hprefReal : ∀ n, finitePrefix a n =
      (cutoffPrefixMass u (fun j => (w j : ℝ≥0∞)) n).toReal := by
    intro n
    rw [cutoffPrefixMass_eq_sum_exactSiteMass, ENNReal.toReal_sum]
    · rfl
    · intro m hm
      exact hasite m
  let c : ℝ := cE.toReal
  have hc : 0 < c := ENNReal.toReal_pos hcE0.ne' hcEtop
  have hlinear : ∀ᶠ n : ℕ in atTop, c * n ≤ finitePrefix a n := by
    filter_upwards [hcE] with n hn
    rw [hprefReal]
    have hcast := ENNReal.toReal_mono (hprefixfinite n) hn
    simpa [c, ENNReal.toReal_mul, hcEtop] using hcast
  have hsnonneg : ∀ j, 0 ≤ (w j : ℝ) * f (u j : ℕ) := fun j =>
    mul_nonneg (w j).2 (hfnn _ (by exact_mod_cast hu j))
  let q : ℕ → ℝ≥0 := fun j => ⟨(w j : ℝ) * f (u j : ℕ), hsnonneg j⟩
  have hq : Summable q := (NNReal.summable_mk hsnonneg).mpr hs
  have hqtop : (∑' j : ℕ, (q j : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hq
  have hregroup : (∑' n : ℕ,
      exactSiteMass u (fun j => (w j : ℝ≥0∞)) n * ENNReal.ofReal (fn n)) ≠ ∞ := by
    rw [← weighted_tsum_eq_exactSiteMass]
    convert hqtop using 1
    apply tsum_congr
    intro j
    have hnat : fn (u j) = f (u j : ℕ) := by
      simp [fn, PaperCompleteR11.natWeight, max_eq_right (Nat.one_le_iff_ne_zero.mpr (hu j).ne')]
    rw [hnat]
    calc
      (w j : ℝ≥0∞) * ENNReal.ofReal (f (u j : ℕ)) =
          ENNReal.ofReal ((w j : ℝ) * f (u j : ℕ)) := by
        rw [ENNReal.coe_nnreal_eq (w j)]
        exact (ENNReal.ofReal_mul (q := f (u j : ℕ)) (w j).2).symm
      _ = (q j : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal (hsnonneg j)
  let b : ℕ → ℝ≥0 := fun n =>
    (exactSiteMass u (fun j => (w j : ℝ≥0∞)) n * ENNReal.ofReal (fn n)).toNNReal
  have hb : Summable b := ENNReal.tsum_coe_ne_top_iff_summable.mp (by
    simpa only [b, ENNReal.coe_toNNReal
      (ENNReal.ne_top_of_tsum_ne_top hregroup _)] using hregroup)
  have hab : (fun n => (b n : ℝ)) = fun n => a n * fn n := by
    funext n
    simp [b, a, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_mul,
      hasite n, ENNReal.toReal_ofReal (hfnnN n)]
  have hsaf : Summable (fun n => a n * fn n) := by
    rw [← hab]
    exact NNReal.summable_coe.mpr hb
  exact (not_summable_weighted_of_eventual_linear_prefix a fn ha hfanti hfnnN hfnot
    c hc hlinear) hsaf

/-- Complete paper criterion, with every clause of `res:weights` represented
literally. -/
theorem lowerDensityZero_iff_exists_admissible_real_weight
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j) :
    PrefixLowerDensityZero u (fun j => (w j : ℝ≥0∞)) ↔
      ∃ f : ℝ → ℝ,
        AntitoneOn f (Ici 1) ∧
        (∀ t : ℝ, 1 ≤ t → 0 ≤ f t) ∧
        PaperCompleteR11.IntegralUnbounded f ∧
        Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ)) := by
  constructor
  · exact exists_admissible_real_weight_of_liminf_eq_zero u w hu
  · rintro ⟨f, hf, hfnn, hdiv, hs⟩
    exact liminf_eq_zero_of_admissible_real_weight u w hu f hf hfnn hdiv hs


#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cutoffPrefixMass_eq_sum_exactSiteMass
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.weighted_tsum_eq_exactSiteMass
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.positive_nat_samples_of_integralUnbounded
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cutoffPrefixMass_ne_top_of_weighted_summable
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.liminf_eq_zero_of_admissible_real_weight
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.lowerDensityZero_iff_exists_admissible_real_weight

end ErdosProblems.Erdos243.PaperCompleteR20
