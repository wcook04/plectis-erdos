import ErdosProblems.Erdos249.PeriodicTotientIndependence
import Mathlib

/-!
# Progression-local coefficients in affine totient relations

ROUND-SIX CANDIDATE: NOT COMPILED in this review environment.
Target: the supplied Lean 4.29.1 workspace. The imported r5 module was compiled
by the desk; this extension was not. No new arithmetic independence hypothesis
is introduced. This proves a transport interface, not signature completeness,
polynomial independence, or irrationality of the original totient series.

A coefficient need not be globally periodic. It suffices that, at each point,
all coefficients become constant on one progression through that point.
The relation itself is allowed to hold only beyond an explicit threshold.
-/

namespace ErdosProblems.Erdos249.ProgressionLocalTotientIndependence

open scoped BigOperators

/-- Locally frozen coefficients in an eventual affine-totient relation vanish. -/
theorem progression_local_coefficients_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i)
    (w : ι → ℕ → ℚ)
    (hfreeze : ∀ n, ∃ Q : ℕ, 0 < Q ∧ ∀ i t, w i (n + Q * t) = w i n)
    (N₀ : ℕ)
    (hrel : ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (a i * n + b i) : ℚ) = 0) :
    ∀ i n, w i n = 0 := by
  classical
  intro i n
  obtain ⟨Q, hQ, hconst⟩ := hfreeze n
  let aa : ι → ℕ := fun j => a j * Q
  let bb : ι → ℕ := fun j => a j * (n + Q * (N₀ + 1)) + b j
  have haa : ∀ j, 0 < aa j := fun j => Nat.mul_pos (ha j) hQ
  have hbb : ∀ j, 0 < bb j := by
    intro j
    dsimp [bb]
    have hx : 0 < n + Q * (N₀ + 1) := by positivity
    have hp := Nat.mul_pos (ha j) hx
    omega
  have hcc : ∀ j k, j ≠ k → aa j * bb k ≠ aa k * bb j := by
    intro j k hjk heq
    apply hcross j k hjk
    have hh : Q * (a j * b k) = Q * (a k * b j) := by
      dsimp [aa, bb] at heq
      nlinarith [heq]
    exact Nat.mul_left_cancel hQ hh
  have hli :=
    Erdos257PeriodNoncollapse.linearIndependent_totientAffineForms aa bb haa hbb hcc
  have hz : (∑ j, w j n •
      (fun t : ℕ => (Nat.totient (aa j * t + bb j) : ℚ))) = 0 := by
    funext t
    have hstart : N₀ ≤ n + Q * (t + N₀ + 1) := by
      have hQone : 1 ≤ Q := hQ
      have hmul : t + N₀ + 1 ≤ Q * (t + N₀ + 1) := by
        simpa only [one_mul] using
          (Nat.mul_le_mul_right (t + N₀ + 1) hQone)
      omega
    have hh := hrel (n + Q * (t + N₀ + 1)) hstart
    have hper : ∀ j, w j (n + Q * (t + N₀ + 1)) = w j n :=
      fun j => hconst j (t + N₀ + 1)
    have harg : ∀ j,
        a j * (n + Q * (t + N₀ + 1)) + b j = aa j * t + bb j := by
      intro j
      dsimp [aa, bb]
      ring
    simpa only [hper, harg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using hh
  exact (Fintype.linearIndependent_iff.mp hli) (fun j => w j n) hz i

/-- The eventual version of the compiled periodic helper. -/
theorem periodic_coefficients_zero_of_eventual
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i)
    (Q : ℕ) (hQ : 0 < Q) (w : ι → ℕ → ℚ)
    (hw : ∀ i n, w i (n + Q) = w i n)
    (N₀ : ℕ)
    (hrel : ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (a i * n + b i) : ℚ) = 0) :
    ∀ i n, w i n = 0 := by
  apply progression_local_coefficients_zero a b ha hcross w ?_ N₀ hrel
  intro n
  refine ⟨Q, hQ, ?_⟩
  intro i t
  exact ErdosProblems.Erdos249.PeriodicTotientIndependence.periodic_add_mul
    (w i) Q (hw i) n t

end ErdosProblems.Erdos249.ProgressionLocalTotientIndependence
