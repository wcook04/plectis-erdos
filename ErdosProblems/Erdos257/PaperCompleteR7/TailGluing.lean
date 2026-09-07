import ErdosProblems.Erdos257.PaperCompleteR7.Displacement
import Erdos257PeriodNoncollapse.GreedyAchievementSet

/-!
# Infinite tail budget and the landed r6 delayed gluing theorem

Uncompiled proof candidates. This file goes beyond the finite algebra in
`DisplacementTailBudget.lean`: it proves the tail estimate for actual infinite
support sums and assembles the diagonal construction. Its hypothesis is the
r6 general version, namely return admissibility of *every finite union* of
the given hosts. It does not assume that separately admissible hosts can be
united, nor prove the missing weighted/positive-cover analytic producer.

The r6 construction is in the current short note's prose rather than a numbered
result environment. It is therefore recorded as supplementary coverage, not
used to inflate the 261-row theorem-environment census.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR7

open Erdos257PeriodNoncollapse Filter Set

/-- All selected exponents beyond R contribute at most the full tail. -/
theorem supportSeries_le_mersenneTail (A : Set ℕ) (R : ℕ)
    (hfuture : ∀ a ∈ A, R < a) :
    erdosSupportSeries 2 A ≤ mersenneTail R := by
  classical
  have hprefix : (∑ k ∈ Finset.range R,
      Set.indicator A mersenneWeight (k + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkR := Finset.mem_range.mp hk
    have hkA : k + 1 ∉ A := by
      intro hkA
      have := hfuture (k + 1) hkA
      omega
    simp [hkA]
  have heq := positiveMersenneSupportValue_eq_prefix_add_suffix A R
  rw [hprefix, zero_add, positiveMersenneSupportValue_eq_erdosSupportSeries] at heq
  rw [heq]
  exact positiveMersenneSupportSuffix_le_tail A R

/-- A coarse dyadic enclosure valid at R=0 as well as at positive indices. -/
theorem mersenneTail_le_dyadic_budget (R : ℕ) :
    mersenneTail R ≤ 2 / (2 : ℝ) ^ R := by
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ R := one_le_pow₀ (by norm_num)
  have hden : (2 : ℝ) ^ R ≤ (2 : ℝ) ^ (R + 1) - 1 := by
    rw [pow_succ]
    nlinarith
  calc
    mersenneTail R ≤ 2 * mersenneWeight (R + 1) := mersenneTail_le_two_mul_weight R
    _ ≤ 2 * (1 / (2 : ℝ) ^ R) := by
      unfold mersenneWeight
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (by positivity) hden) (by norm_num)
    _ = 2 / (2 : ℝ) ^ R := by ring

/-- The actual infinite future-support budget. No relation between N and R
is needed for this upper bound. -/
theorem displacement_future_budget (A : Set ℕ) (N R : ℕ)
    (hfuture : ∀ a ∈ A, R < a) :
    displacement 2 A N ≤ (2 : ℝ) ^ (N + 1) / (2 : ℝ) ^ R := by
  have hmass := (supportSeries_le_mersenneTail A R hfuture).trans
    (mersenneTail_le_dyadic_budget R)
  have hnonneg : 0 ≤ erdosSupportSeries 2 A := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact positiveMersenneSupportValue_nonneg A
  calc
    displacement 2 A N ≤ ((2 : ℝ) ^ N - 1) * erdosSupportSeries 2 A :=
      displacement_le_amplified_mass 2 A N (by norm_num)
    _ ≤ (2 : ℝ) ^ N * erdosSupportSeries 2 A :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ ≤ (2 : ℝ) ^ N * (2 / (2 : ℝ) ^ R) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (2 : ℝ) ^ (N + 1) / (2 : ℝ) ^ R := by rw [pow_succ]; ring

/-- Return admissibility with a prescribed divisor and arbitrarily late shifts. -/
def ReturnAdmissible (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ L : ℕ, 0 < L → ∀ N₀ : ℕ,
    ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧ L ∣ N ∧ displacement 2 A N < ε

theorem returnAdmissible_mono {A B : Set ℕ} (hBA : B ⊆ A)
    (hA : ReturnAdmissible A) : ReturnAdmissible B := by
  intro ε hε L hL N₀
  obtain ⟨N, hN₀, hN, hdiv, hsmall⟩ := hA ε hε L hL N₀
  exact ⟨N, hN₀, hN, hdiv,
    lt_of_le_of_lt (displacement_mono 2 B A N (by norm_num) hBA) hsmall⟩

/-- Return admissibility supplies hereditary irrationality, not conversely. -/
theorem returnAdmissible_hereditary_irrational {H : Set ℕ}
    (hH : ReturnAdmissible H) :
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A) := by
  apply all_base_hereditary_of_binary_returns H
  intro ε hε
  obtain ⟨N, _, hN, _, hsmall⟩ := hH ε hε 1 (by norm_num) 0
  exact ⟨N, hN, hsmall⟩

/-- A sequence of factorial-divisible samples with a geometric error envelope
contains a return for every prescribed divisor, tolerance, and lower index. -/
theorem returnAdmissible_of_samples (A : Set ℕ) (N : ℕ → ℕ)
    (hlarge : ∀ j, j + 1 ≤ N j)
    (hdiv : ∀ j, Nat.factorial (j + 1) ∣ N j)
    (hsmall : ∀ j, displacement 2 A (N j) ≤ 1 / (2 : ℝ) ^ j) :
    ReturnAdmissible A := by
  intro ε hε L hL N₀
  have hlim : Tendsto (fun j : ℕ => (1 : ℝ) / (2 : ℝ) ^ j)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hev : ∀ᶠ j : ℕ in atTop, (1 : ℝ) / (2 : ℝ) ^ j < ε :=
    hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hev
  let j := max J (max L N₀)
  have hjJ : J ≤ j := le_max_left _ _
  have hjL : L ≤ j := le_trans (le_max_left _ _) (le_max_right _ _)
  have hjN : N₀ ≤ j := le_trans (le_max_right _ _) (le_max_right _ _)
  have hfact : L ∣ Nat.factorial (j + 1) := Nat.dvd_factorial hL (by omega)
  refine ⟨N j, ?_, ?_, hfact.trans (hdiv j), ?_⟩
  · exact le_trans hjN (le_trans (Nat.le_succ _) (hlarge j))
  · have := hlarge j
    omega
  · exact lt_of_le_of_lt (hsmall j) (hJ j hjJ)

/-- Finite host union through index j, including both endpoints. -/
def hostPrefix (E : ℕ → Set ℕ) (j : ℕ) : Set ℕ :=
  {a | ∃ i, i ≤ j ∧ a ∈ E i}

/-- The landed r6 gluing theorem, in its general finite-union form.
The cutoffs are *chosen*; the untruncated countable union is not asserted to
be admissible. Every host is retained beyond its own finite cutoff. -/
theorem delayed_countable_gluing (E : ℕ → Set ℕ)
    (hfinite : ∀ j, ReturnAdmissible (hostPrefix E j)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ReturnAdmissible {a : ℕ | ∃ i, a ∈ E i ∧ s i < a} := by
  classical
  have hex : ∀ j : ℕ, ∃ N : ℕ,
      j + 1 ≤ N ∧ 0 < N ∧ Nat.factorial (j + 1) ∣ N ∧
        displacement 2 (hostPrefix E j) N < 1 / (2 : ℝ) ^ (j + 2) := by
    intro j
    exact hfinite j _ (by positivity) _ (Nat.factorial_pos _) (j + 1)
  choose N hN using hex
  let w : ℕ → ℕ := fun j => N j + j + 3
  let s : ℕ → ℕ := fun i => i + (Finset.range i).sup w
  let A : Set ℕ := {a | ∃ i, a ∈ E i ∧ s i < a}
  have hsup : Monotone (fun i : ℕ => (Finset.range i).sup w) := by
    intro i j hij
    apply Finset.sup_le
    intro k hk
    exact Finset.le_sup (Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hk) hij))
  have hs : StrictMono s := by
    intro i j hij
    dsimp [s]
    exact add_lt_add_of_lt_of_le hij (hsup hij.le)
  refine ⟨s, hs, ?_⟩
  change ReturnAdmissible A
  apply returnAdmissible_of_samples A N
    (fun j => (hN j).1) (fun j => (hN j).2.2.1)
  intro j
  let T : Set ℕ := A \ hostPrefix E j
  have hfuture : ∀ a ∈ T, N j + j + 3 < a := by
    intro a ha
    obtain ⟨i, hiE, hsa⟩ := ha.1
    have hji : j < i := by
      by_contra hnot
      apply ha.2
      exact ⟨i, by omega, hiE⟩
    have hw : w j ≤ (Finset.range i).sup w :=
      Finset.le_sup (Finset.mem_range.mpr hji)
    have hws : w j ≤ s i := by
      dsimp [s]
      omega
    exact lt_of_le_of_lt hws hsa
  have htail : displacement 2 T (N j) ≤ 1 / (2 : ℝ) ^ (j + 2) := by
    have h := displacement_future_budget T (N j) (N j + j + 3) hfuture
    have heq : (2 : ℝ) ^ (N j + 1) / (2 : ℝ) ^ (N j + j + 3) =
        1 / (2 : ℝ) ^ (j + 2) := by
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
      congr 1
      omega
    exact heq ▸ h
  have hsub : A ⊆ hostPrefix E j ∪ T := by
    intro a ha
    by_cases hB : a ∈ hostPrefix E j
    · exact Or.inl hB
    · exact Or.inr ⟨ha, hB⟩
  have hbound := (displacement_mono 2 A (hostPrefix E j ∪ T) (N j)
    (by norm_num) hsub).trans
      (displacement_union_le 2 (hostPrefix E j) T (N j) (by norm_num))
  have hquarter : (1 : ℝ) / (2 : ℝ) ^ (j + 2) =
      (1 / (2 : ℝ) ^ j) / 4 := by
    rw [pow_add]
    norm_num
    ring
  have hbase : 0 < (1 : ℝ) / (2 : ℝ) ^ j := by positivity
  have hprefix := (hN j).2.2.2
  rw [hquarter] at hprefix htail
  linarith

end ErdosProblems.Erdos257.PaperCompleteR7

end
