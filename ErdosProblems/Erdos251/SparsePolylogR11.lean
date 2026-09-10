import ErdosProblems.Erdos251.SparseAmbientR9
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative counting for the actual envelope-driven sparse schedule

Candidate source, UNRUN. The rate is derived from explicit readiness
thresholds, not from upper Banach density zero. The extended-window theorem
covers [X,2X+m), including all right-edge coordinates of an m-block.
-/
noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR11.SparsePolylog
open PaperR8.SparseSchedule PaperR9.SparseAmbient

def polylog (α : ℝ) (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 3)) ^ α
def iterlog (n : ℕ) : ℝ := Real.log (Real.log ((n : ℝ) + 3))
def threshold (Q k : ℕ) : ℕ := 2 ^ (2 ^ (Q * gap k))

theorem log_argument_positive (n : ℕ) : 0 < Real.log ((n : ℝ) + 3) :=
  Real.log_pos (by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)

theorem polylog_mono {α : ℝ} (hα : 0 ≤ α) : Monotone (polylog α) := by
  intro n m hnm
  apply Real.rpow_le_rpow (log_argument_positive n).le
    (Real.log_le_log (by positivity)
      (show (n : ℝ) + 3 ≤ m + 3 by exact_mod_cast Nat.add_le_add_right hnm 3)) hα

theorem log_shift_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 3)) atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  apply Filter.tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ n + 3)
  exact tendsto_natCast_atTop_atTop

theorem polylog_tendsto_atTop {α : ℝ} (hα : 0 < α) :
    Tendsto (polylog α) atTop atTop :=
  (tendsto_rpow_atTop hα).comp log_shift_tendsto_atTop

theorem iterlog_tendsto_atTop : Tendsto iterlog atTop atTop :=
  Real.tendsto_log_atTop.comp log_shift_tendsto_atTop

theorem iterlog_mono : Monotone iterlog := by
  intro n m hnm
  apply Real.log_le_log (log_argument_positive n)
  exact Real.log_le_log (by positivity)
    (show (n : ℝ) + 3 ≤ m + 3 by exact_mod_cast Nat.add_le_add_right hnm 3)

theorem iterlog_pos {n : ℕ} (hn : 1 ≤ n) : 0 < iterlog n := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show (4 : ℝ) ≤ n + 3 by exact_mod_cast (show 4 ≤ n + 3 by omega))
  rw [h4] at hl
  exact Real.log_pos (by linarith [Real.log_two_gt_d9])

theorem iterlog_le_nat {n : ℕ} (hn : 1 ≤ n) : iterlog n ≤ n := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnr
  have harg : (n : ℝ) + 3 ≤ 4 * n := by linarith
  have hl := Real.log_le_log (by positivity : 0 < (n : ℝ) + 3) harg
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hnp.ne'] at hl
  have h4 : Real.log (4 : ℝ) ≤ 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    linarith [Real.log_two_lt_d9]
  have hnlog := Real.log_le_sub_one_of_pos hnp
  have hll := Real.log_le_sub_one_of_pos (log_argument_positive n)
  change Real.log (Real.log ((n : ℝ) + 3)) ≤ n
  linarith

theorem factorial_le_two_pow_square (n : ℕ) : n.factorial ≤ 2 ^ (n ^ 2) := by
  calc
    n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1 < 2)).le n
    _ = 2 ^ (n ^ 2) := by rw [← pow_mul, pow_two]

theorem amplitude_le_two_pow (k : ℕ) : amplitude k ≤ 2 ^ (3 * gap k) := by
  have hf := factorial_le_two_pow_square (k + 3)
  calc
    amplitude k ≤ 4 * 2 ^ ((k + 3) ^ 2) * 2 ^ gap k := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hf)
    _ = 2 ^ (2 + (k + 3) ^ 2 + gap k) := by
      rw [pow_add, pow_add]
      norm_num
    _ ≤ 2 ^ (3 * gap k) := by
      apply Nat.pow_le_pow_right (by decide)
      unfold gap
      simp only [pow_two]
      nlinarith

theorem gap_succ_le_twice (k : ℕ) : gap (k + 1) ≤ 2 * gap k := by
  unfold gap
  simp only [pow_two]
  nlinarith

theorem gap_succ_ge (k : ℕ) : gap k + 1 ≤ gap (k + 1) := by
  unfold gap
  simp only [pow_two]
  nlinarith

theorem threshold_mono (Q : ℕ) : Monotone (threshold Q) := by
  intro i j hij
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul_left Q (gap_mono hij)

theorem gap_le_threshold (Q k : ℕ) (hQ : 1 ≤ Q) : gap k ≤ threshold Q k := by
  have h0 : gap k ≤ Q * gap k := by nlinarith
  have h1 : Q * gap k ≤ 2 ^ (Q * gap k) := (Nat.lt_pow_self (by decide : 1 < 2)).le
  have h2 : 2 ^ (Q * gap k) ≤ 2 ^ (2 ^ (Q * gap k)) :=
    (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact h0.trans (h1.trans h2)

theorem threshold_double (Q k : ℕ) (hQ : 1 ≤ Q) :
    2 * threshold Q k ≤ threshold Q (k + 1) := by
  have hg := gap_succ_ge k
  have he : Q * gap k + 1 ≤ Q * gap (k + 1) := by nlinarith
  have hp : 2 ^ (Q * gap k + 1) ≤ 2 ^ (Q * gap (k + 1)) :=
    Nat.pow_le_pow_right (by decide) he
  rw [pow_succ] at hp
  have hpos : 1 ≤ 2 ^ (Q * gap k) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have hE : 2 ^ (Q * gap k) + 1 ≤ 2 ^ (Q * gap (k + 1)) := by omega
  have h : 2 ^ (2 ^ (Q * gap k) + 1) ≤ 2 ^ (2 ^ (Q * gap (k + 1))) :=
    Nat.pow_le_pow_right (by decide) hE
  simpa only [threshold, pow_succ, Nat.mul_comm] using h

theorem threshold_step (Q k : ℕ) (hQ : 1 ≤ Q) :
    threshold Q (k + 1) + gap k ≤ threshold Q (k + 2) := by
  have hg : gap k ≤ threshold Q (k + 1) :=
    (gap_mono (Nat.le_succ k)).trans (gap_le_threshold Q (k + 1) hQ)
  have ht := threshold_double Q (k + 1) hQ
  calc
    threshold Q (k + 1) + gap k ≤ 2 * threshold Q (k + 1) := by omega
    _ ≤ threshold Q (k + 2) := by simpa only [Nat.add_assoc] using ht

theorem log_threshold (Q k : ℕ) :
    Real.log (threshold Q k : ℝ) = (2 : ℝ) ^ (Q * gap k) * Real.log 2 := by
  simp only [threshold, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem log_log_threshold (Q k : ℕ) :
    Real.log (Real.log (threshold Q k : ℝ)) =
      (Q : ℝ) * (gap k : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
  rw [log_threshold, Real.log_mul (by positivity)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', Real.log_pow]
  push_cast
  ring

theorem log_log_two_lower : -Real.log 2 ≤ Real.log (Real.log 2) := by
  have h : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) h
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_one, zero_sub] at hl
  exact hl

/-- An explicit readiness supplier, including the independent linear cap. -/
theorem threshold_ready {α : ℝ} (hα : 0 < α) (Q : ℕ)
    (hQ : 4 ≤ Q) (hαQ : 8 ≤ α * Q) (k : ℕ) :
    Ready (polylog α) (threshold Q k) k := by
  have hg : (1 : ℝ) ≤ gap k := by exact_mod_cast (show 1 ≤ gap k by have := gap_pos k; omega)
  have hQr : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT : 0 < (threshold Q k : ℝ) := by
    have hTnat : 0 < threshold Q k := by simp only [threshold]; positivity
    exact_mod_cast hTnat
  have hTlog : 0 < Real.log (threshold Q k : ℝ) := by rw [log_threshold]; positivity
  have hpow : amplitude k ≤ threshold Q k := by
    apply (amplitude_le_two_pow k).trans
    apply Nat.pow_le_pow_right (by decide)
    have h1 : 3 * gap k ≤ Q * gap k := Nat.mul_le_mul_right _ (by omega)
    exact h1.trans (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hlogA : Real.log (amplitude k : ℝ) ≤ (3 * (gap k : ℝ)) * Real.log 2 := by
    have h := Real.log_le_log (by exact_mod_cast amplitude_pos k)
      (show (amplitude k : ℝ) ≤ (2 : ℝ) ^ (3 * gap k) by exact_mod_cast amplitude_le_two_pow k)
    simpa only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] using h
  have hexp : 3 * (gap k : ℝ) ≤ α * ((Q : ℝ) * gap k - 1) := by
    have h1 : 2 ≤ (Q : ℝ) * gap k := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left
      (show (Q : ℝ) * gap k / 2 ≤ (Q : ℝ) * gap k - 1 by linarith) hα.le
    have h3 := mul_le_mul_of_nonneg_right hαQ (show (0 : ℝ) ≤ gap k from Nat.cast_nonneg _)
    nlinarith
  have hlogpow : Real.log (amplitude k : ℝ) ≤
      Real.log ((Real.log (threshold Q k : ℝ)) ^ α) := by
    rw [Real.log_rpow hTlog α, log_log_threshold]
    have h1 := mul_le_mul_of_nonneg_left log_log_two_lower hα.le
    have h2 := mul_le_mul_of_nonneg_right hexp hln.le
    nlinarith
  have haT : (amplitude k : ℝ) ≤ (Real.log (threshold Q k : ℝ)) ^ α := by
    have h := Real.exp_le_exp.mpr hlogpow
    simpa only [Real.exp_log (by exact_mod_cast amplitude_pos k : (0 : ℝ) < amplitude k),
      Real.exp_log (Real.rpow_pos_of_pos hTlog α)] using h
  intro m hm
  have hTm : (threshold Q k : ℝ) ≤ (m : ℝ) + 3 := by exact_mod_cast (show threshold Q k ≤ m + 3 by omega)
  have hlogs := Real.log_le_log hT hTm
  refine ⟨haT.trans (Real.rpow_le_rpow hTlog.le hlogs hα.le), ?_⟩
  exact hpow.trans (hm.trans (Nat.le_succ m))

/-- A non-upgrading step cannot have crossed the next readiness threshold.
This is the quantitative lag invariant missing from the old candidates. -/
theorem centre_le_readiness_threshold (f : ℕ → ℝ) (T : ℕ → ℕ)
    (hT : ∀ k, Ready f (T k) k)
    (hstep : ∀ k, T (k + 1) + gap k ≤ T (k + 2)) (start : ℕ) :
    ∀ j, centre f start j ≤ start + T (level f start j + 1) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    classical
    by_cases hr : Ready f (centre f start (j + 1)) (level f start j + 1)
    · rw [level_succ, upgrade_of_ready hr, centre_succ]
      have h := hstep (level f start j)
      have hs := Nat.add_le_add_left h start
      calc
        centre f start j + gap (level f start j) ≤
            (start + T (level f start j + 1)) + gap (level f start j) :=
          Nat.add_le_add_right ih _
        _ = start + (T (level f start j + 1) + gap (level f start j)) := by omega
        _ ≤ start + T (level f start j + 2) := by simpa only [Nat.add_assoc] using hs
    · have hn : centre f start (j + 1) < T (level f start j + 1) := by
        by_contra hnot
        exact hr (ready_mono (hT (level f start j + 1)) (Nat.le_of_not_gt hnot))
      have hu : upgrade f (centre f start (j + 1)) (level f start j) = level f start j := by
        unfold upgrade
        exact if_neg hr
      rw [level_succ, hu]
      omega

theorem iterlog_centre_bound {α : ℝ} (hα : 0 < α) (Q : ℕ)
    (hQ : 4 ≤ Q) (hαQ : 8 ≤ α * Q) (start j : ℕ)
    (hj : start + 3 ≤ level (polylog α) start j) :
    iterlog (centre (polylog α) start j) ≤ 4 * Q * gap (level (polylog α) start j) := by
  let k := level (polylog α) start j
  let E := 2 ^ (Q * gap (k + 1))
  have hQ1 : 1 ≤ Q := by omega
  have hc := centre_le_readiness_threshold (polylog α) (threshold Q)
    (threshold_ready hα Q hQ hαQ) (fun k => threshold_step Q k hQ1) start j
  have ht : start + 3 ≤ threshold Q (k + 1) :=
    hj.trans ((level_le_gap k).trans
      ((gap_mono (Nat.le_succ k)).trans (gap_le_threshold Q (k + 1) hQ1)))
  have hc2 : centre (polylog α) start j + 3 ≤ 2 * threshold Q (k + 1) := by
    change centre (polylog α) start j ≤ start + threshold Q (k + 1) at hc
    omega
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : (1 : ℝ) ≤ E := by exact_mod_cast (show 1 ≤ E from Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hl := Real.log_le_log (by positivity : 0 < (centre (polylog α) start j : ℝ) + 3)
    (show (centre (polylog α) start j : ℝ) + 3 ≤ 2 * (threshold Q (k + 1) : ℝ) by exact_mod_cast hc2)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (show (threshold Q (k + 1) : ℝ) ≠ 0 by
      have ht : threshold Q (k + 1) ≠ 0 := by simp [threshold]
      exact_mod_cast ht), log_threshold] at hl
  have hEcast : (2 : ℝ) ^ (Q * gap (k + 1)) = (E : ℝ) := by simp [E]
  rw [hEcast] at hl
  have hlin : Real.log ((centre (polylog α) start j : ℝ) + 3) ≤ 2 * (E : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left (show Real.log 2 ≤ 1 by linarith [Real.log_two_lt_d9])
      (show 0 ≤ 1 + (E : ℝ) by positivity)
    nlinarith
  have hll := Real.log_le_log (log_argument_positive _) hlin
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hll
  have hlogE : Real.log (E : ℝ) = (Q : ℝ) * (gap (k + 1) : ℝ) * Real.log 2 := by
    simp [E, Real.log_pow]
  rw [hlogE] at hll
  have hgap : (gap (k + 1) : ℝ) ≤ 2 * (gap k : ℝ) := by exact_mod_cast gap_succ_le_twice k
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hg : (1 : ℝ) ≤ gap k := by exact_mod_cast (show 1 ≤ gap k by have := gap_pos k; omega)
  have hmul := mul_le_mul_of_nonneg_left (show Real.log 2 ≤ 1 by linarith [Real.log_two_lt_d9])
    (show 0 ≤ 1 + (Q : ℝ) * gap (k + 1) by positivity)
  have hscale := mul_le_mul_of_nonneg_left hgap (show (0 : ℝ) ≤ Q from Nat.cast_nonneg _)
  change Real.log (Real.log ((centre (polylog α) start j : ℝ) + 3)) ≤ 4 * Q * gap k
  nlinarith

/-- Local, rather than global-prefix, bin counting. -/
theorem supportSlice_card_le_local (c : ℕ → ℕ) (hc : StrictMono c)
    (a L R : ℕ) (hR : 0 < R)
    (hsep : ∀ j, a ≤ c j → R ≤ c (j + 1) - c j) :
    (supportSlice c a L).card ≤ L / R + 1 := by
  classical
  rw [supportSlice_card c hc a L]
  have hmap : Set.MapsTo (fun j => (c j - a) / R)
      (indexSlice c a L : Set ℕ) (range (L / R + 1) : Set ℕ) := by
    intro j hj
    have hb := (mem_filter.mp hj).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : c j - a ≤ L)))
  have hinj : Set.InjOn (fun j => (c j - a) / R) (indexSlice c a L : Set ℕ) := by
    intro i hi j hj heq
    have hib := (mem_filter.mp hi).2
    have hjb := (mem_filter.mp hj).2
    have hclose1 := equal_bin_close hR heq
    have hclose2 := equal_bin_close hR heq.symm
    obtain hij | hij | hij := lt_trichotomy i j
    · have hs := hsep i hib.1
      have hm := hc.monotone (Nat.succ_le_of_lt hij)
      change c (i + 1) ≤ c j at hm
      omega
    · exact hij
    · have hs := hsep j hjb.1
      have hm := hc.monotone (Nat.succ_le_of_lt hij)
      change c (j + 1) ≤ c i at hm
      omega
  simpa only [card_range] using card_le_card_of_injOn (fun j => (c j - a) / R) hmap hinj

/-- Quantitative support bound for every interval [X,X+L) of length at most 2X. -/
theorem polylog_extended_rate_withQ {α : ℝ} (hα : 0 < α)
    (Q : ℕ) (hQ : 4 ≤ Q) (hαQ : 8 ≤ α * Q) (start : ℕ) :
    ∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
      ((supportSlice (centre (polylog α) start) X L).card : ℝ) ≤
        (8 * Q + 1) * X / iterlog X := by
  let c := centre (polylog α) start
  have hc : StrictMono c := centre_strictMono _ _
  obtain ⟨J, hJ⟩ := level_cofinal (polylog α) (polylog_tendsto_atTop hα) start (start + 3)
  refine ⟨max 1 (c J + 1), ?_⟩
  intro X L hX hL
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  let j₀ := cut c hc X
  let R := gap (level (polylog α) start j₀)
  have hR : 0 < R := gap_pos _
  have hcut : X ≤ c j₀ := cut_spec c hc X
  have hJcut : J ≤ j₀ := by
    by_contra hnot
    have hmono := hc (Nat.lt_of_not_ge hnot)
    have hCX : c J + 1 ≤ X := (le_max_right _ _).trans hX
    omega
  have hjlevel : start + 3 ≤ level (polylog α) start j₀ := hJ.trans (level_mono _ _ hJcut)
  have hD : iterlog X ≤ 4 * Q * (R : ℝ) :=
    (iterlog_mono hcut).trans (iterlog_centre_bound hα Q hQ hαQ start j₀ hjlevel)
  have hsep : ∀ j, X ≤ c j → R ≤ c (j + 1) - c j := by
    intro j hj
    have hjcut : j₀ ≤ j := by
      by_contra hnot
      have h := (before_cut_iff c hc X j).mp (Nat.lt_of_not_ge hnot)
      omega
    change R ≤ centre (polylog α) start (j + 1) - centre (polylog α) start j
    rw [centre_succ, Nat.add_sub_cancel_left]
    exact gap_mono (level_mono _ _ hjcut)
  have hcount := supportSlice_card_le_local c hc X L R hR hsep
  have hprod : (supportSlice c X L).card * R ≤ L + R := by
    have h1 := Nat.mul_le_mul_right R hcount
    have h2 := Nat.div_mul_le_self L R
    nlinarith
  have hDp := iterlog_pos hX1
  change ((supportSlice c X L).card : ℝ) ≤ (8 * Q + 1) * X / iterlog X
  apply (le_div_iff₀ hDp).mpr
  by_cases hz : (supportSlice c X L).card = 0
  · simp only [hz, Nat.cast_zero, zero_mul]
    positivity
  · have hcard : (1 : ℝ) ≤ (supportSlice c X L).card := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
    have hp : (((supportSlice c X L).card : ℝ) - 1) * R ≤ L := by
      have h := (show ((supportSlice c X L).card : ℝ) * R ≤ (L : ℝ) + R by exact_mod_cast hprod)
      nlinarith
    have h1 := mul_le_mul_of_nonneg_left hD (sub_nonneg.mpr hcard)
    have h2 := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 4 * Q by positivity)
    have h3 : (L : ℝ) ≤ 2 * X := by exact_mod_cast hL
    have h4 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 4 * Q by positivity)
    have h5 := iterlog_le_nat hX1
    nlinarith

/-- The implied constant depends only on α, not on the initial prefix or seed. -/
theorem polylog_extended_rate_uniform {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ start : ℕ, ∃ X₀ : ℕ, ∀ X L : ℕ,
      X₀ ≤ X → L ≤ 2 * X →
      ((supportSlice (centre (polylog α) start) X L).card : ℝ) ≤ C * X / iterlog X := by
  obtain ⟨Q, hQbig⟩ := exists_nat_gt (max (4 : ℝ) (8 / α))
  have hQ : 4 ≤ Q := by exact_mod_cast ((le_max_left _ _).trans hQbig.le)
  have hαQ : 8 ≤ α * Q := by
    have h := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hQbig.le)
    nlinarith
  exact ⟨8 * Q + 1, by positivity,
    fun start => polylog_extended_rate_withQ hα Q hQ hαQ start⟩

theorem polylog_extended_rate {α : ℝ} (hα : 0 < α) (start : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
      ((supportSlice (centre (polylog α) start) X L).card : ℝ) ≤ C * X / iterlog X := by
  obtain ⟨C, hC, h⟩ := polylog_extended_rate_uniform hα
  exact ⟨C, hC, h start⟩

/-- Readiness supplies the other side of the asserted log-log spacing scale. -/
theorem gap_upper_of_ready {α : ℝ} (hα : 0 < α) (start : ℕ)
    (hready : Ready (polylog α) start 0) (j : ℕ) :
    (gap (level (polylog α) start j) : ℝ) ≤
      (α / Real.log 2) * iterlog (centre (polylog α) start j) := by
  let k := level (polylog α) start j
  have hpow : 2 ^ gap k ≤ amplitude k := by
    have hf := Nat.factorial_pos (k + 3)
    unfold amplitude
    nlinarith [Nat.one_le_pow (gap k) 2 (by decide)]
  have ha := (capacity_budget (polylog α) start hready j).1
  have hpowR : (2 : ℝ) ^ gap k ≤ (amplitude k : ℝ) := by exact_mod_cast hpow
  have hlower : (2 : ℝ) ^ gap k ≤ polylog α (centre (polylog α) start j) :=
    hpowR.trans ha
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ gap k) hlower
  rw [Real.log_pow, polylog, Real.log_rpow (log_argument_positive _) α] at hlog
  have hln : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  change (gap k : ℝ) ≤ (α / Real.log 2) * Real.log (Real.log ((centre (polylog α) start j : ℝ) + 3))
  calc
    (gap k : ℝ) ≤
        (α * Real.log (Real.log ((centre (polylog α) start j : ℝ) + 3))) / Real.log 2 :=
      (le_div_iff₀ hln).mpr hlog
    _ = _ := by ring

/-- The old target is now a proved declaration, not an assumed interface. -/
theorem polylogarithmic_rate : PolylogarithmicRate_target := by
  intro α hα start _hready
  obtain ⟨C, hC, X₀, hX₀⟩ := polylog_extended_rate hα start
  exact ⟨C, hC, X₀, fun X hX => hX₀ X X hX (by omega)⟩

#print axioms threshold_ready
#print axioms centre_le_readiness_threshold
#print axioms polylog_extended_rate
#print axioms polylogarithmic_rate
end ErdosProblems.Erdos251.PaperR11.SparsePolylog
