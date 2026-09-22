import ErdosProblems.Erdos251.ActualPrimePaperR11
import ErdosProblems.Erdos251.PaperCompleteR20.SparseNonconcentration

/-!
# Erdős #251: the simultaneous prime-gap countermodel

Paper restatement of `res:jointcountermodel` (short paper, "a rational sum with
the stated prime-gap statistics") and of `long251:res:jointcountermodel` (long
paper, "simultaneous prime-gap countermodel").

The missing analytic ingredient of the first pass was the *cumulative* support
estimate `|S ∩ [0,n)| = O_ε(n / log log n)`, which the paper obtains by
splitting `[√n, n)` into dyadic intervals.  It is proved here directly, and it
needs no prime-distribution input at all: `S` is the range of the schedule's
strictly increasing `centre` function, whose consecutive spacings are
`gap (level …)`, and `iterlog_centre_bound` already says that this spacing is
at least a constant multiple of `log log` of the position.  Splitting at
`m = Nat.sqrt n` — where `log log (m+3) ≥ log log (n+3) − log 2` — therefore
gives the whole estimate from one application of the local spacing bound:

* `cut_step_bound`: separation `R` beyond `m` bounds `#{j : c j < n}` by
  `#{j : c j < m} + (n − m)/R + 1`;
* `cut_prefix_bound`: with `m = Nat.sqrt n` this is `O_ε(n / log log n)`.

Everything else is assembled from the existing tree.  Two inputs of the paper's
proof are cited literature rather than Mathlib, so they are carried as explicit
named hypotheses and never assumed silently: `SchlagePuchtaLemma4` (fixed-block
polynomial nonconcentration for the actual prime gaps, Schlage-Puchta's Lemma 4)
and `PrimeNumberTheorem` (`p_n ∼ n log n`).
-/

noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperCompleteR21

open ErdosProblems.Erdos251.PaperR8.SparseSchedule
open ErdosProblems.Erdos251.PaperR9.SparseAmbient
open ErdosProblems.Erdos251.PaperR11.SparsePolylog
open ErdosProblems.Erdos251.PaperR11.GrowingBlocks
open ErdosProblems.Erdos251.PaperR11.SparsePaper
open ErdosProblems.Erdos251.PaperR11.Nonconcentration
open ErdosProblems.Erdos251.PaperR11.PerturbationGrowth
open ErdosProblems.Erdos251.PaperR11.PrimeSource

/-! ## Elementary facts about the correction allowance -/

/-- `log (n+3) ≥ 1` for every natural `n`, since `e < 3`. -/
theorem one_le_log_shift (n : ℕ) : (1 : ℝ) ≤ Real.log ((n : ℝ) + 3) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp : Real.exp 1 ≤ (n : ℝ) + 3 := by
    have h9 := Real.exp_one_lt_d9
    linarith
  exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp

/-- The allowance `(log (n+3))^α` is never below one. -/
theorem one_le_polylog {α : ℝ} (hα : 0 ≤ α) (n : ℕ) : 1 ≤ polylog α n := by
  have h := Real.rpow_le_rpow_of_exponent_le (one_le_log_shift n) hα
  rwa [Real.rpow_zero] at h

/-- The allowance is monotone in its exponent. -/
theorem polylog_exponent_mono {α β : ℝ} (hαβ : α ≤ β) (n : ℕ) :
    polylog α n ≤ polylog β n :=
  Real.rpow_le_rpow_of_exponent_le (one_le_log_shift n) hαβ

/-! ## The cumulative support estimate -/

/-- `cut c hc N` is the number of support points below `N`; it never exceeds `N`. -/
theorem cut_le_self (c : ℕ → ℕ) (hc : StrictMono c) (N : ℕ) : cut c hc N ≤ N := by
  by_contra hnot
  have h := (before_cut_iff c hc N N).mp (Nat.lt_of_not_ge hnot)
  have h2 := index_le_of_strictMono c hc N
  omega

/-- Separation `R` from `m` onwards bounds the number of support points in
`[m, n)` by `(n − m)/R + 1`. -/
theorem cut_step_bound (c : ℕ → ℕ) (hc : StrictMono c) (m n R : ℕ) (hR : 0 < R)
    (hsep : ∀ j, m ≤ c j → R ≤ c (j + 1) - c j) :
    cut c hc n ≤ cut c hc m + (n - m) / R + 1 := by
  have hj₀m : m ≤ c (cut c hc m) := cut_spec c hc m
  have hgrow : ∀ k : ℕ, c (cut c hc m) + R * k ≤ c (cut c hc m + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hge : m ≤ c (cut c hc m + k) :=
        le_trans hj₀m (hc.monotone (Nat.le_add_right _ _))
      have hs := hsep (cut c hc m + k) hge
      have hmono : c (cut c hc m + k) ≤ c (cut c hc m + k + 1) :=
        hc.monotone (Nat.le_succ _)
      have hmul : R * (k + 1) = R * k + R := by ring
      have hstep : c (cut c hc m + (k + 1)) = c (cut c hc m + k + 1) := by
        rw [Nat.add_assoc]
      omega
  by_contra hnot
  push_neg at hnot
  set q := (n - m) / R with hq
  set s := (n - m) % R with hs
  have hdm : R * q + s = n - m := Nat.div_add_mod (n - m) R
  have hsR : s < R := Nat.mod_lt _ hR
  have hlt : cut c hc m + (q + 1) < cut c hc n := by omega
  have hck : c (cut c hc m + (q + 1)) < n :=
    (before_cut_iff c hc n (cut c hc m + (q + 1))).mp hlt
  have hg := hgrow (q + 1)
  have hmul : R * (q + 1) = R * q + R := by ring
  omega

/-- The paper's cumulative support estimate, with an explicit constant. -/
theorem cut_prefix_bound_withQ {α : ℝ} (hα : 0 < α) (Q : ℕ) (hQ : 4 ≤ Q)
    (hαQ : 8 ≤ α * Q) (start : ℕ) (hc : StrictMono (centre (polylog α) start)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ((cut (centre (polylog α) start) hc n : ℕ) : ℝ)
        ≤ (8 * Q + 3) * n / iterlog n := by
  obtain ⟨J, hJ⟩ := level_cofinal (polylog α) (polylog_tendsto_atTop hα) start (start + 3)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (iterlog_tendsto_atTop.eventually_ge_atTop (2 * Real.log 2))
  set X₀ : ℕ := max 1 (centre (polylog α) start J + 1) with hX₀
  refine ⟨max (max 1 N₁) (X₀ * X₀), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnX : X₀ * X₀ ≤ n := le_trans (le_max_right _ _) hn
  set m : ℕ := Nat.sqrt n with hm
  have hmX₀ : X₀ ≤ m := Nat.le_sqrt.mpr hnX
  have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hmX₀
  have hmm : m * m ≤ n := by
    have h := Nat.sqrt_le' n
    rwa [pow_two] at h
  have hmlt : n < (m + 1) * (m + 1) := by
    have h := Nat.lt_succ_sqrt' n
    rwa [pow_two] at h
  have hmn : m ≤ n := Nat.sqrt_le_self n
  -- the separation at `m`
  have hcut : m ≤ centre (polylog α) start (cut (centre (polylog α) start) hc m) :=
    cut_spec _ hc m
  have hJcut : J ≤ cut (centre (polylog α) start) hc m := by
    by_contra hnot
    have hmono := hc (Nat.lt_of_not_ge hnot)
    have hCX : centre (polylog α) start J + 1 ≤ m := le_trans (le_max_right _ _) hmX₀
    omega
  have hjlevel : start + 3 ≤
      level (polylog α) start (cut (centre (polylog α) start) hc m) :=
    hJ.trans (level_mono _ _ hJcut)
  set R : ℕ := gap (level (polylog α) start (cut (centre (polylog α) start) hc m)) with hRdef
  have hR : 0 < R := gap_pos _
  have hD : iterlog m ≤ 4 * Q * (R : ℝ) :=
    (iterlog_mono hcut).trans
      (iterlog_centre_bound hα Q hQ hαQ start _ hjlevel)
  have hsep : ∀ j, m ≤ centre (polylog α) start j →
      R ≤ centre (polylog α) start (j + 1) - centre (polylog α) start j := by
    intro j hj
    have hjcut : cut (centre (polylog α) start) hc m ≤ j := by
      by_contra hnot
      have h := (before_cut_iff _ hc m j).mp (Nat.lt_of_not_ge hnot)
      omega
    rw [centre_succ, Nat.add_sub_cancel_left]
    exact gap_mono (level_mono _ _ hjcut)
  have hcutbd := cut_step_bound (centre (polylog α) start) hc m n R hR hsep
  have hcutm := cut_le_self (centre (polylog α) start) hc m
  have hnat : cut (centre (polylog α) start) hc n ≤ m + (n - m) / R + 1 := by omega
  -- real-valued repackaging
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hIn : 0 < iterlog n := iterlog_pos hn1
  have hIm : 0 < iterlog m := iterlog_pos hm1
  have hcast : ((cut (centre (polylog α) start) hc n : ℕ) : ℝ)
      ≤ (m : ℝ) + (n : ℝ) / R + 1 := by
    have h1 : ((cut (centre (polylog α) start) hc n : ℕ) : ℝ)
        ≤ (m : ℝ) + (((n - m) / R : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
    have h2 : (((n - m) / R : ℕ) : ℝ) ≤ ((n - m : ℕ) : ℝ) / R := Nat.cast_div_le
    have h3 : ((n - m : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : (n - m : ℕ) ≤ n := Nat.sub_le _ _
      exact_mod_cast this
    have h4 : ((n - m : ℕ) : ℝ) / R ≤ (n : ℝ) / R :=
      div_le_div_of_nonneg_right h3 hRpos.le
    linarith
  -- log log at the square root
  have hnm3 : (n : ℝ) + 3 ≤ ((m : ℝ) + 3) ^ 2 := by
    have hnat3 : n + 3 ≤ (m + 3) * (m + 3) := by nlinarith
    have : ((n + 3 : ℕ) : ℝ) ≤ (((m + 3) * (m + 3) : ℕ) : ℝ) := by exact_mod_cast hnat3
    push_cast at this
    nlinarith [this]
  have hlogs : Real.log ((n : ℝ) + 3) ≤ 2 * Real.log ((m : ℝ) + 3) := by
    have h := Real.log_le_log (by positivity) hnm3
    rwa [Real.log_pow] at h
    -- `Real.log_pow` : log (x ^ k) = k * log x
  have hiter : iterlog n ≤ Real.log 2 + iterlog m := by
    have hp := log_argument_positive n
    have h3 := Real.log_le_log hp hlogs
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (log_argument_positive m))] at h3
    exact h3
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hhalf : iterlog n / 2 ≤ iterlog m := by
    have h := hN₁ n hnN₁
    linarith
  -- `m` is small compared with `n / log log n`
  have hitm : iterlog m ≤ (m : ℝ) := iterlog_le_nat hm1
  have hmbig : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmsq : (m : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmm
  have hmbound : (m : ℝ) ≤ 2 * n / iterlog n := by
    rw [le_div_iff₀ hIn]
    nlinarith
  -- the spacing term
  have hspace : (n : ℝ) / R ≤ 8 * Q * n / iterlog n := by
    have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hIR : iterlog n ≤ 8 * (Q : ℝ) * R := by linarith
    have hmulR := mul_le_mul_of_nonneg_left hIR hn0
    rw [div_le_iff₀ hRpos, div_mul_eq_mul_div, le_div_iff₀ hIn]
    nlinarith [hmulR]
  have hone : (1 : ℝ) ≤ (n : ℝ) / iterlog n := by
    rw [le_div_iff₀ hIn]
    have := iterlog_le_nat hn1
    linarith
  have hfinal : (m : ℝ) + (n : ℝ) / R + 1 ≤ (8 * Q + 3) * n / iterlog n := by
    have hexp : (8 * (Q : ℝ) + 3) * n / iterlog n
        = 2 * n / iterlog n + 8 * Q * n / iterlog n + (n : ℝ) / iterlog n := by
      field_simp
      ring
    rw [hexp]
    linarith
  calc ((cut (centre (polylog α) start) hc n : ℕ) : ℝ)
      ≤ (m : ℝ) + (n : ℝ) / R + 1 := hcast
    _ ≤ (8 * Q + 3) * n / iterlog n := hfinal

/-- `|S ∩ [0,n)| = O_α(n / log log n)` for the schedule support. -/
theorem cut_prefix_bound {α : ℝ} (hα : 0 < α) (start : ℕ)
    (hc : StrictMono (centre (polylog α) start)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ((cut (centre (polylog α) start) hc n : ℕ) : ℝ) ≤ C * n / iterlog n := by
  obtain ⟨Q, hQbig⟩ := exists_nat_gt (max (4 : ℝ) (8 / α))
  have hQ : 4 ≤ Q := by exact_mod_cast ((le_max_left _ _).trans hQbig.le)
  have hαQ : 8 ≤ α * Q := by
    have h := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hQbig.le)
    nlinarith
  obtain ⟨N₀, hN₀⟩ := cut_prefix_bound_withQ hα Q hQ hαQ start hc
  exact ⟨8 * Q + 3, by positivity, N₀, hN₀⟩

/-! ## The corollary -/

/-- **Long paper, `long251:res:jointcountermodel`.**  For every prescribed
finite prime-gap prefix `K` and every `0 < ε ≤ 1` there is a nonnegative
integer correction `e`, vanishing on the prefix and eventually at most
`(log (n+3))^ε`, for which the altered sequence `b = g + e` simultaneously has

* a rational dyadic value;
* every fixed eventual coefficient and cumulative congruence;
* fixed-block polynomial nonconcentration;
* vanishing total variation distance between the unnormalised block
  distributions for block lengths `o(log log X)`;
* cumulative positions `P n = 2 + ∑_{i<n} b i` with
  `0 ≤ P n − p n = O_ε(n (log (n+3))^ε / log log n)` and `P n ∼ n log n`.

The two literature inputs appear as the explicit hypotheses `hSP` and `hPNT`. -/
theorem long_joint_prime_gap_countermodel
    (hSP : SchlagePuchtaLemma4) (hPNT : PrimeNumberTheorem)
    (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ e : ℕ → ℕ, ∃ r : ℚ, ∃ C : ℝ, 0 < C ∧
      (∀ n, n < K → e n = 0) ∧
      HasSum (fun n => ((primeGap0 n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        primeGap0 n + e n ≡ primeGap0 n [MOD q] ∧
        cumulative (fun i => primeGap0 i + e i) n ≡ prime0 n [MOD q]) ∧
      FixedBlockNonconcentration (fun n => ((primeGap0 n + e n : ℕ) : ℤ)) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        Tendsto (fun X =>
          blockTV primeGap0 (fun n => primeGap0 n + e n) X (m X)) atTop (𝓝 0)) ∧
      (∀ n, prime0 n ≤ cumulative (fun i => primeGap0 i + e i) n) ∧
      (∀ᶠ n : ℕ in atTop,
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) - prime0 n
          ≤ C * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ)))) ∧
      Tendsto (fun n =>
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) / scale n) atTop (𝓝 1) := by
  classical
  -- run the construction at an exponent below one; the allowance only shrinks
  set δ : ℝ := min ε (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  obtain ⟨start, l, u, C₀, hSK, hSZ, hAl, hlu, hC₀, hrate, hfill⟩ :=
    prime_polylogarithmic_interval hδ0 hδ1 hPNT K
  obtain ⟨r, hlr, hru⟩ := exists_rat_btwn hlu
  obtain ⟨e, heS, heprefix, hef, hcong, hes, hpos, heven, hgrowth, heblocks⟩ :=
    hfill (r : ℝ) hlr.le hru.le
  set c : ℕ → ℕ := centre (polylog δ) start with hcdef
  have hc : StrictMono c := centre_strictMono _ _
  -- nonconcentration transfers along the density-zero support
  have hZD : ZeroDensity (Set.range c) :=
    upperBanachZero_implies_zeroDensity hSZ
  have hNC : FixedBlockNonconcentration (fun n => ((primeGap0 n + e n : ℕ) : ℤ)) := by
    refine ErdosProblems.Erdos251.PaperCompleteR20.sparse_nonconcentration
      (fun n => (primeGap0 n : ℤ)) (fun n => ((primeGap0 n + e n : ℕ) : ℤ))
      (Set.range c) hZD ?_ (fixedBlock_of_SchlagePuchta hSP)
    intro n hn
    have hz : e n = 0 := by
      by_contra h
      exact hn (heS n h)
    simp [hz]
  -- the cumulative correction bound
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hef
  set B : ℝ := ∑ i ∈ range N₁, (e i : ℝ) with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hsumbound : ∀ n : ℕ, (∑ i ∈ range n, (e i : ℝ))
      ≤ ((cut c hc n : ℕ) : ℝ) * (B + polylog δ n) := by
    intro n
    have hsub : (range n).filter (fun i => e i ≠ 0) ⊆ (range (cut c hc n)).image c := by
      intro i hi
      obtain ⟨hin, hine⟩ := Finset.mem_filter.mp hi
      obtain ⟨j, hj⟩ := heS i hine
      refine Finset.mem_image.mpr ⟨j, ?_, hj⟩
      refine Finset.mem_range.mpr ((before_cut_iff c hc n j).mpr ?_)
      rw [hj]
      exact Finset.mem_range.mp hin
    have hEq : (∑ i ∈ (range n).filter (fun i => e i ≠ 0), (e i : ℝ))
        = ∑ i ∈ range n, (e i : ℝ) := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro x hx hxn
      have hz : e x = 0 := by
        by_contra h
        exact hxn (Finset.mem_filter.mpr ⟨hx, h⟩)
      simp [hz]
    have hLe : (∑ i ∈ (range n).filter (fun i => e i ≠ 0), (e i : ℝ))
        ≤ ∑ i ∈ (range (cut c hc n)).image c, (e i : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.cast_nonneg _)
    have hPt : ∀ i ∈ (range (cut c hc n)).image c, (e i : ℝ) ≤ B + polylog δ n := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hcjn : c j < n := (before_cut_iff c hc n j).mp (Finset.mem_range.mp hj)
      by_cases hlow : c j < N₁
      · have h1 : (e (c j) : ℝ) ≤ B :=
          Finset.single_le_sum (f := fun i => (e i : ℝ))
            (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.mpr hlow)
        have h2 := one_le_polylog hδ0.le n
        linarith
      · have h1 : (e (c j) : ℝ) ≤ polylog δ (c j) := hN₁ _ (Nat.le_of_not_lt hlow)
        have h2 : polylog δ (c j) ≤ polylog δ n :=
          polylog_mono hδ0.le (Nat.le_of_lt hcjn)
        linarith
    have hCard := Finset.sum_le_card_nsmul _ _ _ hPt
    rw [Finset.card_image_of_injective _ hc.injective, Finset.card_range,
      nsmul_eq_mul] at hCard
    calc (∑ i ∈ range n, (e i : ℝ))
        = ∑ i ∈ (range n).filter (fun i => e i ≠ 0), (e i : ℝ) := hEq.symm
      _ ≤ ∑ i ∈ (range (cut c hc n)).image c, (e i : ℝ) := hLe
      _ ≤ ((cut c hc n : ℕ) : ℝ) * (B + polylog δ n) := hCard
  obtain ⟨C₁, hC₁, N₂, hN₂⟩ := cut_prefix_bound hδ0 start hc
  refine ⟨e, r, C₁ * (B + 1), by positivity, ?_, hes, ?_, ?_, hNC, ?_, ?_, ?_, hgrowth⟩
  · intro n hn
    have h := heprefix n hn
    omega
  · filter_upwards [hef] with n hn
    exact hn.trans (polylog_exponent_mono hδε n)
  · intro q hq
    filter_upwards [hcong q hq] with n hn
    exact ⟨hn.2.2.1, hn.2.2.2⟩
  · intro m hm
    exact (heblocks m (small_blocks_shifted_iterlog m hm)).1
  · intro n
    rw [cumulative_correction_identity]
    omega
  · filter_upwards [eventually_ge_atTop (max N₂ 3)] with n hn
    have hnN₂ : N₂ ≤ n := le_trans (le_max_left _ _) hn
    have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
    have hn1 : 1 ≤ n := by omega
    -- the paper's `log log n` never exceeds the schedule's `log log (n+3)`
    have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hlog3 : (1 : ℝ) < Real.log (n : ℝ) := by
      have hexp : Real.exp 1 < (n : ℝ) := by
        have h9 := Real.exp_one_lt_d9
        linarith
      exact (Real.lt_log_iff_exp_lt (by linarith)).mpr hexp
    have hllpos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog3
    have hllle : Real.log (Real.log (n : ℝ)) ≤ iterlog n :=
      Real.log_le_log (by linarith) (Real.log_le_log (by linarith) (by linarith))
    have hIn : 0 < iterlog n := iterlog_pos hn1
    have hpolyδ : 1 ≤ polylog δ n := one_le_polylog hδ0.le n
    have hpolyε : polylog δ n ≤ polylog ε n := polylog_exponent_mono hδε n
    have hstep1 := hsumbound n
    have hstep2 := hN₂ n hnN₂
    have hcut0 : (0 : ℝ) ≤ ((cut c hc n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpack : (0 : ℝ) ≤ B + polylog δ n := by linarith
    have hstep3 : ((cut c hc n : ℕ) : ℝ) * (B + polylog δ n)
        ≤ (C₁ * n / iterlog n) * (B + polylog δ n) :=
      mul_le_mul_of_nonneg_right hstep2 hpack
    have hstep4 : B + polylog δ n ≤ (B + 1) * polylog δ n := by nlinarith
    have hCn : (0 : ℝ) ≤ C₁ * n / iterlog n := by positivity
    have hstep5 : (C₁ * n / iterlog n) * (B + polylog δ n)
        ≤ (C₁ * n / iterlog n) * ((B + 1) * polylog δ n) :=
      mul_le_mul_of_nonneg_left hstep4 hCn
    have hstep6 : (C₁ * n / iterlog n) * ((B + 1) * polylog δ n)
        ≤ (C₁ * n / iterlog n) * ((B + 1) * polylog ε n) := by
      have hB1 : (0 : ℝ) ≤ B + 1 := by linarith
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpolyε hB1) hCn
    have hrewrite : (C₁ * n / iterlog n) * ((B + 1) * polylog ε n)
        = C₁ * (B + 1) * ((n : ℝ) * polylog ε n / iterlog n) := by
      field_simp
      try ring
    have hid : (cumulative (fun i => primeGap0 i + e i) n : ℝ) - prime0 n
        = ∑ i ∈ range n, (e i : ℝ) := by
      rw [cumulative_correction_identity]
      push_cast
      ring
    rw [hid]
    calc (∑ i ∈ range n, (e i : ℝ))
        ≤ ((cut c hc n : ℕ) : ℝ) * (B + polylog δ n) := hstep1
      _ ≤ (C₁ * n / iterlog n) * (B + polylog δ n) := hstep3
      _ ≤ (C₁ * n / iterlog n) * ((B + 1) * polylog δ n) := hstep5
      _ ≤ (C₁ * n / iterlog n) * ((B + 1) * polylog ε n) := hstep6
      _ = C₁ * (B + 1) * ((n : ℝ) * polylog ε n / iterlog n) := hrewrite
      _ ≤ C₁ * (B + 1) * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ))) := by
            have hnum : (0 : ℝ) ≤ (n : ℝ) * polylog ε n :=
              mul_nonneg (Nat.cast_nonneg n)
                (le_trans zero_le_one (one_le_polylog hε.le n))
            have hCB : (0 : ℝ) ≤ C₁ * (B + 1) := mul_nonneg hC₁.le (by linarith)
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_left hnum hllpos hllle) hCB

/-- **Short paper, `res:jointcountermodel`.**  The same countermodel written
for the altered sequence `b` itself: `b` has a rational dyadic sum, agrees with
the prime gaps below `K`, dominates them, exceeds them by at most
`(log (n+3))^ε` eventually, keeps every fixed eventual residue of the
coefficients and of the cumulative positions, has vanishing block total
variation for lengths `o(log log X)`, has fixed-block polynomial
nonconcentration (`|{n < N : F(b n, …, b (n+k)) = 0}| = o(N)` for every fixed
nonzero `F`), and its cumulative positions satisfy
`0 ≤ P n − p n = O_ε(n (log (n+3))^ε / log log n)` and `P n ∼ n log n`.
The positions are not asserted to be prime. -/
theorem short_joint_prime_gap_countermodel
    (hSP : SchlagePuchtaLemma4) (hPNT : PrimeNumberTheorem)
    (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ b : ℕ → ℕ, ∃ r : ℚ, ∃ C : ℝ, 0 < C ∧
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ n, n < K → b n = primeGap0 n) ∧
      (∀ n, primeGap0 n ≤ b n) ∧
      (∀ᶠ n : ℕ in atTop, ((b n - primeGap0 n : ℕ) : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        b n ≡ primeGap0 n [MOD q] ∧ cumulative b n ≡ prime0 n [MOD q]) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        Tendsto (fun X => blockTV primeGap0 b X (m X)) atTop (𝓝 0)) ∧
      FixedBlockNonconcentration (fun n => (b n : ℤ)) ∧
      (∀ n, prime0 n ≤ cumulative b n) ∧
      (∀ᶠ n : ℕ in atTop, (cumulative b n : ℝ) - prime0 n
        ≤ C * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ)))) ∧
      Tendsto (fun n => (cumulative b n : ℝ) / scale n) atTop (𝓝 1) := by
  obtain ⟨e, r, C, hC, hprefix, hsum, hallow, hcong, hNC, hTV, hlo, hest, hgrow⟩ :=
    long_joint_prime_gap_countermodel hSP hPNT K hε hε1
  refine ⟨fun n => primeGap0 n + e n, r, C, hC, hsum, ?_, ?_, ?_, hcong, hTV, hNC,
    hlo, hest, hgrow⟩
  · intro n hn
    have h := hprefix n hn
    simp [h]
  · intro n
    exact Nat.le_add_right _ _
  · filter_upwards [hallow] with n hn
    simpa using hn

#print axioms cut_prefix_bound
#print axioms long_joint_prime_gap_countermodel
#print axioms short_joint_prime_gap_countermodel

end ErdosProblems.Erdos251.PaperCompleteR21
