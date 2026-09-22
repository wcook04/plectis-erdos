import ErdosProblems.Erdos249.PeriodicTotientIndependence
import ErdosProblems.Erdos249.ResidueClassTotientSeries
import Mathlib

/-!
# Paper-complete interfaces: eventual periodic coefficients and cofinal pulses

Targets: short-note `cor:periodic-freezing` and `lem:bounded-pulse`.
This file extends the compiled r5 periodic theorem, not the uncompiled r6 helper.
Every theorem has a proof term and no extra mathematical assumption.
Build status for this return: source-reviewed, NOT RUN (no Lean executable).
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7

open scoped BigOperators

/-- The compiled common-period theorem also applies to eventual relations. -/
theorem periodic_coefficients_zero_eventually
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i)
    (w : ι → ℕ → ℚ) (Q : ℕ) (hQ : 0 < Q)
    (hw : ∀ i n, w i (n + Q) = w i n)
    (N₀ : ℕ)
    (hrel : ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (a i * n + b i) : ℚ) = 0) :
    ∀ i n, w i n = 0 := by
  classical
  let bb : ι → ℕ := fun i => a i * N₀ + b i
  let ww : ι → ℕ → ℚ := fun i n => w i (n + N₀)
  have hcross' : ∀ i j, i ≠ j → a i * bb j ≠ a j * bb i := by
    intro i j hij h
    apply hcross i j hij
    dsimp [bb] at h
    nlinarith [h]
  have hw' : ∀ i n, ww i (n + Q) = ww i n := by
    intro i n
    dsimp [ww]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      hw i (n + N₀)
  have hrel' : ∀ n,
      ∑ i, ww i n * (Nat.totient (a i * n + bb i) : ℚ) = 0 := by
    intro n
    have h := hrel (n + N₀) (by omega)
    have hind : ∀ i, a i * (n + N₀) + b i = a i * n + bb i := by
      intro i
      dsimp [bb]
      ring
    simpa only [hind, ww] using h
  have hz := PeriodicTotientIndependence.periodic_coefficients_zero
    a bb ha hcross' Q hQ ww hw' hrel'
  intro i n
  have hlarge : N₀ ≤ n + Q * N₀ := by nlinarith
  have hzero := hz i (n + Q * N₀ - N₀)
  have hind : n + Q * N₀ - N₀ + N₀ = n + Q * N₀ := Nat.sub_add_cancel hlarge
  change w i (n + Q * N₀ - N₀ + N₀) = 0 at hzero
  rw [hind] at hzero
  rw [PeriodicTotientIndependence.periodic_add_mul (w i) Q (hw i) n N₀] at hzero
  exact hzero

/-- Exact paper quantifiers: each coefficient may have its own positive period,
and the relation need hold only eventually. -/
theorem periodic_freezing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i)
    (w : ι → ℕ → ℚ)
    (hperiodic : ∀ i, ∃ q : ℕ, 0 < q ∧ ∀ n, w i (n + q) = w i n)
    (hrel : ∃ N₀, ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (a i * n + b i) : ℚ) = 0) :
    ∀ i n, w i n = 0 := by
  classical
  choose q hq hper using hperiodic
  let Q := ∏ i, q i
  have hQ : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos (fun i _ => hq i)
  have hdiv (i : ι) : q i ∣ Q := by
    exact Finset.dvd_prod_of_mem q (Finset.mem_univ i)
  have hperQ : ∀ i n, w i (n + Q) = w i n := by
    intro i n
    obtain ⟨t, ht⟩ := hdiv i
    rw [ht]
    exact PeriodicTotientIndependence.periodic_add_mul (w i) (q i) (hper i) n t
  obtain ⟨N₀, hN₀⟩ := hrel
  exact periodic_coefficients_zero_eventually a b ha hcross w Q hQ hperQ N₀ hN₀

/-- Cofinal lengths and the paper's weak `L < N` convention suffice for the
library pulse theorem, whose interface requests every length and `L+1 < N`.
The extra unit is obtained by selecting a strictly larger available length. -/
theorem irrational_dyadicValue_of_cofinal_pulses
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L₀ : ℕ, ∃ L N : ℕ, L₀ ≤ L ∧ L < N ∧ a N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (N - j) = 0 ∧ a (N + j) = 0) :
    Irrational (dyadicValue a) := by
  apply irrational_dyadicValue_of_pulses hC
  intro L
  obtain ⟨L', N, hL', hN, haN, hzero⟩ := hpulse (L + 1)
  refine ⟨N, by omega, haN, ?_⟩
  intro j hj hjL
  exact hzero j hj (by omega)

/-- Exact positive-index version of the paper's bounded isolated-pulse lemma.
The n=0 term in `dyadicValue` is an integer and is explicitly removed. -/
theorem bounded_isolated_pulse
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L₀ : ℕ, ∃ L N : ℕ, L₀ ≤ L ∧ L < N ∧ a N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (N - j) = 0 ∧ a (N + j) = 0) :
    Irrational (∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (n + 1)) := by
  have hirr := irrational_dyadicValue_of_cofinal_pulses a C hC hpulse
  have hs := summable_dyadicTerm hC
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (a n : ℝ) / 2 ^ n) 1 hs
  simp only [Finset.sum_range_one, pow_zero, div_one] at hsplit
  have heq : (∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (n + 1)) =
      dyadicValue a - (a 0 : ℝ) := by
    change (a 0 : ℝ) + (∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (n + 1)) =
      dyadicValue a at hsplit
    linarith
  rw [heq]
  exact hirr.sub_intCast (a 0)

end ErdosProblems.Erdos249.PaperCompleteR7
