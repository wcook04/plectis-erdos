import ErdosProblems.Erdos68.PaperCompleteDivisorCoordinates
import ErdosProblems.Erdos68.PaperCompleteIntegerSpan
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
The literal low-channel kernel and its unique integral classification.
Coordinate j>0 denotes U_(j+1); coordinate 0 denotes e_1.  Thus the tail
condition j>=D is precisely the paper's unit-index condition n>D.
New Lean checks: UNRUN.
-/
namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp

lemma channelSynthesis_smul (c : ℤ) (a : ℕ →₀ ℤ) :
    channelSynthesis (c • a) = c • channelSynthesis a := by
  classical
  unfold channelSynthesis
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [smul_eq_mul, mul_smul]
  unfold Finsupp.sum
  rw [Finset.smul_sum]

lemma channelSynthesis_sub (a b : ℕ →₀ ℤ) :
    channelSynthesis (a - b) = channelSynthesis a - channelSynthesis b := by
  have hn : channelSynthesis (-b) = -channelSynthesis b := by
    simpa using channelSynthesis_smul (-1) b
  rw [sub_eq_add_neg, channelSynthesis_add, hn, sub_eq_add_neg]

lemma channelSynthesis_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℤ) :
    channelSynthesis (∑ i ∈ s, a i) = ∑ i ∈ s, channelSynthesis (a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [channelSynthesis]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, channelSynthesis_add, ih]

lemma synthesis_at_zero (a : ℕ →₀ ℤ) : channelSynthesis a 0 = 0 := by
  classical
  unfold channelSynthesis Finsupp.sum
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases h : j = 0
  · simp [channelBasisColumn, h]
  · simp [channelBasisColumn, h, Finsupp.smul_apply,
      isolated_unit_outside (j + 1) 0 (Or.inl rfl)]

lemma local_channelLCM_pos (D : ℕ) : 0 < channelLCM D := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro d hd
  have hf : 1 < d.factorial := Nat.one_lt_factorial.mpr (Finset.mem_Icc.mp hd).1
  omega

lemma gap_dvd_channelLCM {D d : ℕ} (hd : 2 ≤ d) (hdD : d ≤ D) :
    ((d.factorial : ℤ) - 1) ∣ (channelLCM D : ℤ) := by
  have hn : d.factorial - 1 ∣ channelLCM D :=
    Finset.dvd_lcm (f := fun n => n.factorial - 1) (Finset.mem_Icc.mpr ⟨hd, hdD⟩)
  have hf : 1 ≤ d.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hz : ((d.factorial - 1 : ℕ) : ℤ) ∣ (channelLCM D : ℤ) := by
    exact_mod_cast hn
  simpa [Nat.cast_sub hf] using hz

noncomputable def kernelCoordinates (D : ℕ) : ℕ →₀ ℤ :=
  single 0 (channelLCM D : ℤ) -
    ∑ d ∈ Finset.Icc 2 D,
      single (d - 1) ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1))

lemma low_coordinate_sum_apply (D j : ℕ) :
    (∑ d ∈ Finset.Icc 2 D,
      single (d - 1) ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1))) j =
      if 1 ≤ j ∧ j + 1 ≤ D then
        (channelLCM D : ℤ) / (((j + 1).factorial : ℤ) - 1) else 0 := by
  classical
  rw [Finsupp.finset_sum_apply]
  by_cases h : 1 ≤ j ∧ j + 1 ≤ D
  · rw [if_pos h, Finset.sum_eq_single (j + 1)]
    · simp
    · intro d hd hne
      have hd2 := (Finset.mem_Icc.mp hd).1
      have hneq : d - 1 ≠ j := by omega
      simp [Finsupp.single_apply, hneq]
    · intro hn
      exact (hn (Finset.mem_Icc.mpr ⟨by omega, h.2⟩)).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro d hd
    have hd2 := (Finset.mem_Icc.mp hd).1
    have hdD := (Finset.mem_Icc.mp hd).2
    have hneq : d - 1 ≠ j := by omega
    simp [Finsupp.single_apply, hneq]

lemma kernelCoordinates_zero (D : ℕ) : kernelCoordinates D 0 = channelLCM D := by
  simp [kernelCoordinates, Finsupp.sub_apply, low_coordinate_sum_apply]

lemma kernelCoordinates_pos {j : ℕ} (hj : 0 < j) (D : ℕ) :
    kernelCoordinates D j =
      if j + 1 ≤ D then
        -((channelLCM D : ℤ) / (((j + 1).factorial : ℤ) - 1)) else 0 := by
  have hj0 : j ≠ 0 := by omega
  by_cases h : j + 1 ≤ D <;> simp [kernelCoordinates, Finsupp.sub_apply,
    low_coordinate_sum_apply, hj0, Ne.symm hj0, show 1 ≤ j by omega, h]

noncomputable def canonicalKernel (D : ℕ) : ℕ →₀ ℤ :=
  channelSynthesis (kernelCoordinates D)

noncomputable def kernelOne (D : ℕ) : ℤ := canonicalKernel D 1

/-- The definition agrees with the displayed K_D, including the auxiliary e_1. -/
theorem canonicalKernel_expansion (D : ℕ) :
    canonicalKernel D = (channelLCM D : ℤ) • single 1 1 -
      ∑ d ∈ Finset.Icc 2 D,
        ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1)) • isolatedChannelUnit d := by
  classical
  unfold canonicalKernel kernelCoordinates
  rw [channelSynthesis_sub, channelSynthesis_single, channelSynthesis_sum]
  simp only [channelBasisColumn, if_pos rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hn : d - 1 ≠ 0 := by omega
  have he : d - 1 + 1 = d := by omega
  rw [channelSynthesis_single]
  simp [channelBasisColumn, hn, he]

lemma canonicalKernel_moment (D : ℕ) :
    factorialMoment (canonicalKernel D) = (channelLCM D : ℤ) := by
  rw [canonicalKernel, synthesis_moment, kernelCoordinates_zero]

lemma canonicalKernel_channel {D d : ℕ} (hd : 2 ≤ d) :
    channelNumerator (canonicalKernel D) d =
      if d ≤ D then 0 else (channelLCM D : ℤ) := by
  have hj : 0 < d - 1 := by omega
  have he : d - 1 + 1 = d := by omega
  rw [canonicalKernel, synthesis_channel _ _ hd, kernelCoordinates_zero,
    kernelCoordinates_pos hj, he]
  by_cases h : d ≤ D
  · rw [if_pos h, if_pos h]
    have hq := Int.mul_ediv_cancel' (gap_dvd_channelLCM hd h)
    nlinarith [hq]
  · simp [h]

lemma canonicalKernel_at_zero (D : ℕ) : canonicalKernel D 0 = 0 :=
  synthesis_at_zero _

/-- Zero initial coordinates; the remaining finite coefficients index U_(j+1). -/
def TailCoordinates (D : ℕ) (z : ℕ →₀ ℤ) : Prop :=
  ∀ j, j < D → z j = 0

def LowChannels (D : ℕ) (f : ℕ →₀ ℤ) : Prop :=
  ∀ d ∈ Finset.Icc 2 D, channelNumerator f d = 0

def Admissible (f : ℕ →₀ ℤ) : Prop :=
  ∀ n ∈ f.support, 2 ≤ n

lemma admissible_iff (f : ℕ →₀ ℤ) :
    Admissible f ↔ f 0 = 0 ∧ f 1 = 0 := by
  classical
  constructor
  · intro h
    constructor
    · by_contra hn
      have := h 0 (Finsupp.mem_support_iff.mpr hn)
      omega
    · by_contra hn
      have := h 1 (Finsupp.mem_support_iff.mpr hn)
      omega
  · rintro ⟨h0, h1⟩ n hn
    have hne := Finsupp.mem_support_iff.mp hn
    by_contra h
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> contradiction

lemma tail_moment {D : ℕ} (hD : 1 ≤ D) {z : ℕ →₀ ℤ}
    (hz : TailCoordinates D z) : factorialMoment (channelSynthesis z) = 0 := by
  rw [synthesis_moment, hz 0 (by omega)]

lemma tail_channels {D : ℕ} (hD : 1 ≤ D) {z : ℕ →₀ ℤ}
    (hz : TailCoordinates D z) : LowChannels D (channelSynthesis z) := by
  intro d hd
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hdD := (Finset.mem_Icc.mp hd).2
  rw [synthesis_channel _ _ hd2, hz 0 (by omega), hz (d - 1) (by omega)]
  ring

/-- Full low-channel classification. No recurrence or spanning hypothesis is added. -/
theorem low_channel_classification {D : ℕ} (hD : 2 ≤ D)
    (f : ℕ →₀ ℤ) (h0 : f 0 = 0) :
    LowChannels D f ↔ ∃ t : ℤ, ∃ z : ℕ →₀ ℤ,
      TailCoordinates D z ∧ f = t • canonicalKernel D + channelSynthesis z := by
  classical
  constructor
  · intro hf
    obtain ⟨a, ha, _⟩ := existsUnique_channel_coordinates f h0
    obtain ⟨t, ht⟩ := channelLCM_dvd_factorialMoment_of_channels_zero D f hf
    let z := a - t • kernelCoordinates D
    have ha0 : a 0 = factorialMoment f := by rw [← ha, synthesis_moment]
    have hz : TailCoordinates D z := by
      intro j hj
      change a j - (t • kernelCoordinates D) j = 0
      rw [Finsupp.smul_apply, smul_eq_mul]
      by_cases hj0 : j = 0
      · subst j
        rw [kernelCoordinates_zero, ha0, ht]
        ring
      · have hjp : 0 < j := by omega
        have hd2 : 2 ≤ j + 1 := by omega
        have hdD : j + 1 ≤ D := by omega
        have hc := hf (j + 1) (Finset.mem_Icc.mpr ⟨hd2, hdD⟩)
        rw [← ha, synthesis_channel _ _ hd2] at hc
        simp only [Nat.add_sub_cancel] at hc
        have hq := Int.mul_ediv_cancel' (gap_dvd_channelLCM hd2 hdD)
        have hfac : (1 : ℤ) < (j + 1).factorial := by
          exact_mod_cast Nat.one_lt_factorial.mpr hd2
        have hne : ((j + 1).factorial : ℤ) - 1 ≠ 0 := by omega
        rw [kernelCoordinates_pos hjp D, if_pos hdD]
        apply mul_left_cancel₀ hne
        rw [mul_zero]
        rw [ha0, ht] at hc
        nlinarith [hc, congrArg (fun x : ℤ => t * x) hq]
    refine ⟨t, z, hz, ?_⟩
    dsimp [z]
    rw [channelSynthesis_sub, channelSynthesis_smul, ha]
    change f = t • canonicalKernel D + (f - t • canonicalKernel D)
    abel
  · rintro ⟨t, z, hz, rfl⟩ d hd
    rw [channelNumerator_add, channelNumerator_smul,
      canonicalKernel_channel (Finset.mem_Icc.mp hd).1,
      if_pos (Finset.mem_Icc.mp hd).2,
      tail_channels (by omega) hz d hd]
    ring

/-- Both the moment coefficient and finite tail coordinates are unique. -/
theorem low_channel_parameters_unique {D : ℕ} (hD : 2 ≤ D)
    {t s : ℤ} {z w : ℕ →₀ ℤ}
    (hz : TailCoordinates D z) (hw : TailCoordinates D w)
    (he : t • canonicalKernel D + channelSynthesis z =
      s • canonicalKernel D + channelSynthesis w) : t = s ∧ z = w := by
  have hm := congrArg factorialMoment he
  simp only [factorialMoment_add, factorialMoment_smul, canonicalKernel_moment,
    tail_moment (by omega) hz, tail_moment (by omega) hw, add_zero] at hm
  have hL : (channelLCM D : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (local_channelLCM_pos D))
  have hts : t = s := mul_right_cancel₀ hL hm
  refine ⟨hts, ?_⟩
  rw [hts] at he
  exact channelSynthesis_injective (add_left_cancel he)

/-- Actual support n>=2 imposes exactly one scalar equation. -/
theorem support_equation {D : ℕ} {t : ℤ} {z : ℕ →₀ ℤ} :
    Admissible (t • canonicalKernel D + channelSynthesis z) ↔
      t * kernelOne D + channelSynthesis z 1 = 0 := by
  rw [admissible_iff]
  simp [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    canonicalKernel_at_zero, synthesis_at_zero, kernelOne]

end ErdosProblems.Erdos68.PaperComplete
