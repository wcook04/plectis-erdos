import ErdosProblems.Erdos251.SparseRationalisationCore

/-!
# Single-site residue feedback

This proof source reuses the supplied variableDigit_spec and gives
an explicit one-step selector and an abstract infinite-sum endpoint.

The logarithmic sparse schedule, its counting asymptotic, the Hausdorff
dimension argument and the application to prime gaps remain ordinary
proofs in proofs/SharpSparseFeedback.md. No registered declaration is changed.

The mathematical improvement is that the next residue may depend on the
accumulated sum. A common continuation interval replaces separate repair
sites and a digit-independent pair total.
-/

noncomputable section
open Filter Topology Finset

namespace ErdosProblems.Erdos251.ResidueFeedback

open SparseRationalisationDraft

/-- The last digit in one residue class loses fewer than M units of capacity. -/
theorem progressionCapacity {A M r : ℕ} (hM : 0 < M)
    (hr : r < M) (hA : 2 * M ≤ A) :
    r + M * ((A - r) / M) ≤ A ∧
      A ≤ r + M * ((A - r) / M) + M := by
  have har : r ≤ A := by omega
  have hd := Nat.mod_add_div (A - r) M
  have hm := Nat.mod_lt (A - r) hM
  have hs := Nat.sub_add_cancel har
  omega

/-- An explicit digit in the progression r + M * {0,...,D}. -/
def progressionDigit (r M D : ℕ) (w lo x : ℝ) : ℕ :=
  r + M * variableDigit D ((M : ℝ) * w) (x - (r : ℝ) * w - lo)

theorem progressionDigit_le (r M D : ℕ) (w lo x : ℝ) :
    progressionDigit r M D w lo x ≤ r + M * D := by
  unfold progressionDigit
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left M (variableDigit_le D _ _)) r

/-- Uniform interval selection for every residue r. The hypotheses are
stated with a general progression capacity D to separate floor arithmetic. -/
theorem progressionDigit_spec {A M r D : ℕ} {w lo hi x : ℝ}
    (hM : 0 < M) (hw : 0 < w) (hr : r ≤ M)
    (hcap : r + M * D ≤ A) (htop : A ≤ r + M * D + M)
    (hov : (M : ℝ) * w ≤ hi - lo)
    (hxl : (M : ℝ) * w + lo ≤ x)
    (hxu : x ≤ ((A : ℝ) - M) * w + hi) :
    progressionDigit r M D w lo x ≤ A ∧
      lo ≤ x - (progressionDigit r M D w lo x : ℝ) * w ∧
      x - (progressionDigit r M D w lo x : ℝ) * w ≤ hi := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hrr : (r : ℝ) ≤ M := by exact_mod_cast hr
  have htr : (A : ℝ) ≤ r + M * D + M := by exact_mod_cast htop
  have hz0 : 0 ≤ x - (r : ℝ) * w - lo := by nlinarith
  have hz1 : x - (r : ℝ) * w - lo ≤
      (D : ℝ) * ((M : ℝ) * w) + (hi - lo) := by nlinarith
  have hs := variableDigit_spec (mul_pos hMr hw) hz0 hz1 hov
  refine ⟨(progressionDigit_le r M D w lo x).trans hcap, ?_, ?_⟩
  · dsimp [progressionDigit]
    push_cast
    nlinarith [hs.1]
  · dsimp [progressionDigit]
    push_cast
    nlinarith [hs.2]

/-- The least nonnegative digit residue that repairs the cumulative sum. -/
def cumulativeResidue (C M : ℕ) : ℕ :=
  (repairBuffer (C : ℤ) (M : ℤ)).toNat

theorem cumulativeResidue_spec (C : ℕ) {M : ℕ} (hM : 0 < M) :
    cumulativeResidue C M < M ∧
      (M : ℤ) ∣ (C : ℤ) + (cumulativeResidue C M : ℤ) := by
  have hMi : (0 : ℤ) < M := by exact_mod_cast hM
  have hn := repairBuffer_nonneg (C : ℤ) hMi
  have he : (cumulativeResidue C M : ℤ) = repairBuffer (C : ℤ) (M : ℤ) := by
    exact Int.toNat_of_nonneg hn
  constructor
  · have hh := repairBuffer_lt (C : ℤ) hMi
    rw [← he] at hh
    exact_mod_cast hh
  · rw [he]
    exact repairBuffer_repairs (C : ℤ) (M : ℤ)

/-- One correction site simultaneously encodes a digit and repairs the sum. -/
def feedbackDigit (A M C : ℕ) (w lo x : ℝ) : ℕ :=
  let r := cumulativeResidue C M
  progressionDigit r M ((A - r) / M) w lo x

theorem feedbackDigit_spec {A M C : ℕ} {w lo hi x : ℝ}
    (hM : 0 < M) (hA : 2 * M ≤ A) (hw : 0 < w)
    (hov : (M : ℝ) * w ≤ hi - lo)
    (hxl : (M : ℝ) * w + lo ≤ x)
    (hxu : x ≤ ((A : ℝ) - M) * w + hi) :
    feedbackDigit A M C w lo x ≤ A ∧
      (M : ℤ) ∣ (C : ℤ) + (feedbackDigit A M C w lo x : ℤ) ∧
      lo ≤ x - (feedbackDigit A M C w lo x : ℝ) * w ∧
      x - (feedbackDigit A M C w lo x : ℝ) * w ≤ hi := by
  have hr := cumulativeResidue_spec C hM
  have hc := progressionCapacity hM hr.1 hA
  have hs := progressionDigit_spec hM hw hr.1.le hc.1 hc.2 hov hxl hxu
  refine ⟨hs.1, ?_, hs.2.1, hs.2.2⟩
  unfold feedbackDigit progressionDigit
  push_cast
  have hd : (M : ℤ) ∣ (M : ℤ) *
      (variableDigit ((A - cumulativeResidue C M) / M) ((M : ℝ) * w)
        (x - (cumulativeResidue C M : ℝ) * w - lo) : ℤ) := by
    exact ⟨_, rfl⟩
  simpa only [add_assoc] using dvd_add hr.2 hd

/-- Looking ahead to a multiple of the incoming modulus preserves the
coefficient congruence at the current site. -/
theorem previousModulus_dvd_digit {q C M d : ℤ}
    (hC : q ∣ C) (hM : q ∣ M) (hrepair : M ∣ C + d) : q ∣ d := by
  have h := dvd_sub (hM.trans hrepair) hC
  simpa using h

/-- State = (unweighted cumulative correction, weighted remainder). -/
def feedbackState (A M : ℕ → ℕ) (w lo : ℕ → ℝ) (y : ℝ) : ℕ → ℕ × ℝ
  | 0 => (0, y)
  | n + 1 =>
    let s := feedbackState A M w lo y n
    let d := feedbackDigit (A n) (M n) s.1 (w n) (lo (n + 1)) s.2
    (s.1 + d, s.2 - (d : ℝ) * w n)

def feedbackDigits (A M : ℕ → ℕ) (w lo : ℕ → ℝ) (y : ℝ) (n : ℕ) : ℕ :=
  feedbackDigit (A n) (M n) (feedbackState A M w lo y n).1
    (w n) (lo (n + 1)) (feedbackState A M w lo y n).2

theorem feedbackState_bounds {A M : ℕ → ℕ} {w lo hi : ℕ → ℝ} {y : ℝ}
    (hM : ∀ n, 0 < M n) (hA : ∀ n, 2 * M n ≤ A n)
    (hw : ∀ n, 0 < w n)
    (hl : ∀ n, lo n = (M n : ℝ) * w n + lo (n + 1))
    (hu : ∀ n, hi n = ((A n : ℝ) - M n) * w n + hi (n + 1))
    (hov : ∀ n, (M n : ℝ) * w n ≤ hi (n + 1) - lo (n + 1))
    (hyl : lo 0 ≤ y) (hyu : y ≤ hi 0) :
    ∀ n, lo n ≤ (feedbackState A M w lo y n).2 ∧
      (feedbackState A M w lo y n).2 ≤ hi n := by
  intro n
  induction n with
  | zero => exact ⟨hyl, hyu⟩
  | succ n ih =>
    have hxl : (M n : ℝ) * w n + lo (n + 1) ≤
        (feedbackState A M w lo y n).2 := by rw [← hl n]; exact ih.1
    have hxu : (feedbackState A M w lo y n).2 ≤
        ((A n : ℝ) - M n) * w n + hi (n + 1) := by rw [← hu n]; exact ih.2
    have hs := feedbackDigit_spec (C := (feedbackState A M w lo y n).1)
      (hM n) (hA n) (hw n) (hov n) hxl hxu
    exact ⟨hs.2.2.1, hs.2.2.2⟩

theorem feedback_prefix_sum (A M : ℕ → ℕ) (w lo : ℕ → ℝ) (y : ℝ) (N : ℕ) :
    ∑ n ∈ range N, feedbackDigits A M w lo y n =
      (feedbackState A M w lo y N).1 := by
  induction N with
  | zero => simp [feedbackState]
  | succ N ih =>
    rw [sum_range_succ, ih]
    rfl

theorem feedback_weighted_sum (A M : ℕ → ℕ) (w lo : ℕ → ℝ) (y : ℝ) (N : ℕ) :
    ∑ n ∈ range N, (feedbackDigits A M w lo y n : ℝ) * w n =
      y - (feedbackState A M w lo y N).2 := by
  induction N with
  | zero => simp [feedbackState]
  | succ N ih =>
    rw [sum_range_succ, ih]
    simp only [feedbackState, feedbackDigits]
    ring

/-- Infinite feedback filling under explicit interval and vanishing inputs.
M(n) is the modulus repaired AFTER digit n; the sparse embedding in the
ordinary proof takes M(n) to be the ambient modulus at the next support site. -/
theorem exists_feedback_digits_hasSum
    {A M : ℕ → ℕ} {w lo hi : ℕ → ℝ} {y : ℝ}
    (hM : ∀ n, 0 < M n) (hA : ∀ n, 2 * M n ≤ A n)
    (hw : ∀ n, 0 < w n) (hlo : ∀ n, 0 ≤ lo n)
    (hl : ∀ n, lo n = (M n : ℝ) * w n + lo (n + 1))
    (hu : ∀ n, hi n = ((A n : ℝ) - M n) * w n + hi (n + 1))
    (hov : ∀ n, (M n : ℝ) * w n ≤ hi (n + 1) - lo (n + 1))
    (hvanish : Tendsto hi atTop (𝓝 0))
    (hyl : lo 0 ≤ y) (hyu : y ≤ hi 0) :
    ∃ d : ℕ → ℕ,
      (∀ n, d n ≤ A n) ∧
      (∀ n, (M n : ℤ) ∣ ((∑ i ∈ range (n + 1), d i : ℕ) : ℤ)) ∧
      HasSum (fun n => (d n : ℝ) * w n) y := by
  have hb := feedbackState_bounds hM hA hw hl hu hov hyl hyu
  have hs : ∀ n,
      feedbackDigits A M w lo y n ≤ A n ∧
      (M n : ℤ) ∣ ((feedbackState A M w lo y (n + 1)).1 : ℤ) := by
    intro n
    have hxl : (M n : ℝ) * w n + lo (n + 1) ≤
        (feedbackState A M w lo y n).2 := by rw [← hl n]; exact (hb n).1
    have hxu : (feedbackState A M w lo y n).2 ≤
        ((A n : ℝ) - M n) * w n + hi (n + 1) := by rw [← hu n]; exact (hb n).2
    have h := feedbackDigit_spec (C := (feedbackState A M w lo y n).1)
      (hM n) (hA n) (hw n) (hov n) hxl hxu
    refine ⟨h.1, ?_⟩
    simpa only [feedbackState, Nat.cast_add] using h.2.1
  refine ⟨feedbackDigits A M w lo y, fun n => (hs n).1, ?_, ?_⟩
  · intro n
    rw [feedback_prefix_sum]
    exact (hs n).2
  · have hr : Tendsto (fun n => (feedbackState A M w lo y n).2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvanish
        (fun n => (hlo n).trans (hb n).1) (fun n => (hb n).2)
    have hn : ∀ n, 0 ≤ (feedbackDigits A M w lo y n : ℝ) * w n := by
      intro n
      exact mul_nonneg (Nat.cast_nonneg _) (hw n).le
    rw [hasSum_iff_tendsto_nat_of_nonneg hn]
    have ht : Tendsto (fun N => y - (feedbackState A M w lo y N).2)
        atTop (𝓝 (y - 0)) := tendsto_const_nhds.sub hr
    simpa only [feedback_weighted_sum, sub_zero] using ht

#print axioms progressionCapacity
#print axioms progressionDigit_spec
#print axioms feedbackDigit_spec
#print axioms exists_feedback_digits_hasSum

end ErdosProblems.Erdos251.ResidueFeedback
