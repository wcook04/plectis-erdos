import ErdosProblems.Erdos68.DivisorChannelBasis
import Mathlib.Tactic.IntervalCases

/-!
Finite-support companion to `DepthFourShortSupport.md`.
The coefficient domain is arbitrary signed integers. The short-support
identity gives the exact obstruction through index seven. The unrestricted
depth-four ideal then follows directly from the existing universal divisibility
by `12 * channelLCM 4` and the explicit index-eight vector; it does not need
the finite scalar table or the quadratic horizon theorem. No irrationality
claim is made.
-/

namespace ErdosProblems.Erdos68.ShortSupport

open Finsupp

/-- Increasing the permitted last index preserves a literal support bound. -/
lemma support_mono {a b : ℕ} (hab : a ≤ b) (f : ℕ →₀ ℤ)
    (hs : ∀ n, n ∉ Finset.Icc 2 a → f n = 0) :
    ∀ n, n ∉ Finset.Icc 2 b → f n = 0 := by
  intro n hn
  apply hs n
  intro ha
  exact hn (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
    le_trans (Finset.mem_Icc.mp ha).2 hab⟩)

/-- Expand the literal coefficient vector, rather than a bounded coefficient search. -/
lemma expand_seven (f : ℕ →₀ ℤ)
    (hs : ∀ n, n ∉ Finset.Icc 2 7 → f n = 0) :
    f = single 2 (f 2) + single 3 (f 3) + single 4 (f 4) +
      single 5 (f 5) + single 6 (f 6) + single 7 (f 7) := by
  ext n
  by_cases hn : n ∈ Finset.Icc 2 7
  · obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    interval_cases n <;> simp
  · have hz := hs n hn
    have h2 : 2 ≠ n := by intro h; subst n; norm_num at hn
    have h3 : 3 ≠ n := by intro h; subst n; norm_num at hn
    have h4 : 4 ≠ n := by intro h; subst n; norm_num at hn
    have h5 : 5 ≠ n := by intro h; subst n; norm_num at hn
    have h6 : 6 ≠ n := by intro h; subst n; norm_num at hn
    have h7 : 7 ≠ n := by intro h; subst n; norm_num at hn
    simp [hz, h2, h3, h4, h5, h6, h7]

/-- The paper's dual identity for every integer coefficient vector on 2,...,7. -/
theorem dual_identity_seven (f : ℕ →₀ ℤ)
    (hs : ∀ n, n ∉ Finset.Icc 2 7 → f n = 0) :
    11 * factorialMoment f - 46 * channelNumerator f 2 +
      12 * channelNumerator f 4 = 4140 * (f 6 + 7 * f 7) := by
  have he := expand_seven f hs
  conv_lhs => rw [he]
  norm_num [factorialMoment_add, factorialMoment_single,
    channelNumerator_add, channelNumerator_single, channelWeight]
  ring

/-- Only channels two and four are needed for the short-support obstruction. -/
theorem moment_dvd_seven (f : ℕ →₀ ℤ)
    (hs : ∀ n, n ∉ Finset.Icc 2 7 → f n = 0)
    (h2 : channelNumerator f 2 = 0) (h4 : channelNumerator f 4 = 0) :
    (4140 : ℤ) ∣ factorialMoment f := by
  have hd := dual_identity_seven f hs
  rw [h2, h4] at hd
  refine ⟨3011 * (f 6 + 7 * f 7) - 8 * factorialMoment f, ?_⟩
  nlinarith

theorem moment_ne_1380_seven (f : ℕ →₀ ℤ)
    (hs : ∀ n, n ∉ Finset.Icc 2 7 → f n = 0)
    (h2 : channelNumerator f 2 = 0) (h4 : channelNumerator f 4 = 0) :
    factorialMoment f ≠ 1380 := by
  intro hm
  have hd := moment_dvd_seven f hs h2 h4
  rw [hm] at hd
  norm_num at hd

/-- Through index five the same dual identity forces the moment to vanish. -/
theorem moment_zero_five (f : ℕ →₀ ℤ)
    (hs : ∀ n, n ∉ Finset.Icc 2 5 → f n = 0)
    (h2 : channelNumerator f 2 = 0) (h4 : channelNumerator f 4 = 0) :
    factorialMoment f = 0 := by
  have hd := dual_identity_seven f (support_mono (by omega) f hs)
  have h6 : f 6 = 0 := hs 6 (by norm_num)
  have h7 : f 7 = 0 := hs 7 (by norm_num)
  rw [h2, h4, h6, h7] at hd
  nlinarith

/-- An integral generator of the attainable moments through indices six and seven. -/
noncomputable def sixVector : ℕ →₀ ℤ :=
  single 2 246 + single 3 (-112) + single 4 180 + single 5 (-66) + single 6 11

theorem sixVector_observables :
    factorialMoment sixVector = 4140 ∧
    channelNumerator sixVector 2 = 0 ∧
    channelNumerator sixVector 3 = 0 ∧
    channelNumerator sixVector 4 = 0 := by
  norm_num [sixVector, factorialMoment_add, factorialMoment_neg, factorialMoment_single,
    channelNumerator_add, channelNumerator_neg, channelNumerator_single, channelWeight]

theorem sixVector_support (n : ℕ) (hn : n ∉ Finset.Icc 2 6) :
    sixVector n = 0 := by
  have h2 : 2 ≠ n := by intro h; subst n; norm_num at hn
  have h3 : 3 ≠ n := by intro h; subst n; norm_num at hn
  have h4 : 4 ≠ n := by intro h; subst n; norm_num at hn
  have h5 : 5 ≠ n := by intro h; subst n; norm_num at hn
  have h6 : 6 ≠ n := by intro h; subst n; norm_num at hn
  simp [sixVector, h2, h3, h4, h5, h6]

/-- Exact moment ideal on either short support, with all three channels zero. -/
theorem attainable_moment_iff {N : ℕ} (hNlo : 6 ≤ N) (hNhi : N ≤ 7) (m : ℤ) :
    (∃ f : ℕ →₀ ℤ, (∀ n, n ∉ Finset.Icc 2 N → f n = 0) ∧
      channelNumerator f 2 = 0 ∧ channelNumerator f 3 = 0 ∧
      channelNumerator f 4 = 0 ∧ factorialMoment f = m) ↔ (4140 : ℤ) ∣ m := by
  constructor
  · rintro ⟨f, hs, h2, _h3, h4, hm⟩
    rw [← hm]
    exact moment_dvd_seven f (support_mono hNhi f hs) h2 h4
  · rintro ⟨k, rfl⟩
    refine ⟨k • sixVector, ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn
      have hz := support_mono hNlo sixVector sixVector_support n hn
      simp [hz]
    · simp [channelNumerator_smul, sixVector_observables.2.1]
    · simp [channelNumerator_smul, sixVector_observables.2.2.1]
    · simp [channelNumerator_smul, sixVector_observables.2.2.2]
    · simp [factorialMoment_smul, sixVector_observables.1, mul_comm]

/-- The paper's explicit vector attaining 1380 at maximum index eight. -/
noncomputable def eightVector : ℕ →₀ ℤ :=
  single 2 1482 + single 3 (-784) + single 5 (-136) + single 6 83 + single 8 (-1)

theorem eightVector_observables :
    factorialMoment eightVector = 1380 ∧
    channelNumerator eightVector 2 = 0 ∧
    channelNumerator eightVector 3 = 0 ∧
    channelNumerator eightVector 4 = 0 := by
  norm_num [eightVector, factorialMoment_add, factorialMoment_neg, factorialMoment_single,
    channelNumerator_add, channelNumerator_neg, channelNumerator_single, channelWeight]

theorem eightVector_support (n : ℕ) (hn : n ∉ Finset.Icc 2 8) :
    eightVector n = 0 := by
  have h2 : 2 ≠ n := by intro h; subst n; norm_num at hn
  have h3 : 3 ≠ n := by intro h; subst n; norm_num at hn
  have h5 : 5 ≠ n := by intro h; subst n; norm_num at hn
  have h6 : 6 ≠ n := by intro h; subst n; norm_num at hn
  have h8 : 8 ≠ n := by intro h; subst n; norm_num at hn
  simp [eightVector, h2, h3, h5, h6, h8]

/-- Eight is the least permitted last index that attains moment 1380. -/
theorem attainable_1380_iff (N : ℕ) :
    (∃ f : ℕ →₀ ℤ, (∀ n, n ∉ Finset.Icc 2 N → f n = 0) ∧
      channelNumerator f 2 = 0 ∧ channelNumerator f 3 = 0 ∧
      channelNumerator f 4 = 0 ∧ factorialMoment f = 1380) ↔ 8 ≤ N := by
  constructor
  · rintro ⟨f, hs, h2, _h3, h4, hm⟩
    by_contra hN
    exact moment_ne_1380_seven f (support_mono (by omega) f hs) h2 h4 hm
  · intro hN
    exact ⟨eightVector, support_mono hN eightVector eightVector_support,
      eightVector_observables.2.1, eightVector_observables.2.2.1,
      eightVector_observables.2.2.2, eightVector_observables.1⟩

/-- The paper's exact minimum-index statement requires only channels two and four. -/
theorem attainable_1380_two_channels_iff (N : ℕ) :
    (∃ f : ℕ →₀ ℤ, (∀ n, n ∉ Finset.Icc 2 N → f n = 0) ∧
      channelNumerator f 2 = 0 ∧ channelNumerator f 4 = 0 ∧
      factorialMoment f = 1380) ↔ 8 ≤ N := by
  constructor
  · rintro ⟨f, hs, h2, h4, hm⟩
    by_contra hN
    exact moment_ne_1380_seven f (support_mono (by omega) f hs) h2 h4 hm
  · intro hN
    exact ⟨eightVector, support_mono hN eightVector eightVector_support,
      eightVector_observables.2.1, eightVector_observables.2.2.2,
      eightVector_observables.1⟩

/-- The general channel congruences already give the sharp depth-four divisor. -/
theorem all_support_moment_dvd (f : ℕ →₀ ℤ)
    (hs : ∀ n ∈ f.support, 2 ≤ n)
    (h2 : channelNumerator f 2 = 0) (h3 : channelNumerator f 3 = 0)
    (h4 : channelNumerator f 4 = 0) : (1380 : ℤ) ∣ factorialMoment f := by
  have hz : ∀ d ∈ Finset.Icc 2 4, channelNumerator f d = 0 := by
    intro d hd
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> assumption
  have hL : channelLCM 4 = 115 := by decide +kernel
  have hd := twelve_channelLCM_dvd_factorialMoment_of_channels_zero
    (D := 4) (by decide) f hs hz
  norm_num [hL] at hd
  exact hd

/-- Unrestricted depth-four moment ideal from one sharp divisor and one witness.
No upper bound on support, scalar recurrence table, or tail horizon is assumed. -/
theorem all_support_attainable_iff (m : ℤ) :
    (∃ f : ℕ →₀ ℤ, (∀ n ∈ f.support, 2 ≤ n) ∧
      channelNumerator f 2 = 0 ∧ channelNumerator f 3 = 0 ∧
      channelNumerator f 4 = 0 ∧ factorialMoment f = m) ↔ (1380 : ℤ) ∣ m := by
  constructor
  · rintro ⟨f, hs, h2, h3, h4, hm⟩
    rw [← hm]
    exact all_support_moment_dvd f hs h2 h3 h4
  · rintro ⟨k, rfl⟩
    refine ⟨k • eightVector, ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn
      by_contra hlo
      have hz := eightVector_support n (by simp only [Finset.mem_Icc]; omega)
      have hz' : (k • eightVector) n = 0 := by simp [hz]
      exact (Finsupp.mem_support_iff.mp hn) hz'
    · simp [channelNumerator_smul, eightVector_observables.2.1]
    · simp [channelNumerator_smul, eightVector_observables.2.2.1]
    · simp [channelNumerator_smul, eightVector_observables.2.2.2]
    · simp [factorialMoment_smul, eightVector_observables.1, mul_comm]

-- Keep the public proof boundary auditable at the same source revision.
#print axioms dual_identity_seven
#print axioms moment_zero_five
#print axioms attainable_moment_iff
#print axioms attainable_1380_iff
#print axioms attainable_1380_two_channels_iff
#print axioms all_support_attainable_iff

end ErdosProblems.Erdos68.ShortSupport
