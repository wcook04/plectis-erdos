import ErdosProblems.Erdos249.PaperCompleteR7.PeriodicAndPulse
import Mathlib

/-!
# Periodic freezing for integer-intercept affine forms

The paper permits arbitrary integer intercepts.  The checked r7 theorem uses
natural intercepts; shifting far enough makes every intercept nonnegative,
without changing any cross determinant or the periodic coefficients.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR20

open scoped BigOperators

/-- The natural argument of an integer-intercept affine form.  Its values
before the form becomes nonnegative are irrelevant to an eventual relation. -/
def integerAffineValue {ι : Type*} (a : ι → ℕ) (b : ι → ℤ)
    (i : ι) (n : ℕ) : ℕ :=
  Int.toNat ((a i : ℤ) * (n : ℤ) + b i)

/-- Exact integer-intercept version of the paper's periodic-freezing
corollary. -/
theorem periodic_freezing_integer_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : ι → ℤ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → (a i : ℤ) * b j ≠ (a j : ℤ) * b i)
    (w : ι → ℕ → ℚ)
    (hperiodic : ∀ i, ∃ q : ℕ, 0 < q ∧ ∀ n, w i (n + q) = w i n)
    (hrel : ∃ N₀, ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (integerAffineValue a b i n) : ℚ) = 0) :
    ∀ i n, w i n = 0 := by
  classical
  obtain ⟨N₀, hN₀⟩ := hrel
  let B : ℕ := ∑ i, Int.natAbs (b i)
  let M : ℕ := N₀ + B + 1
  let bb : ι → ℕ := fun i => Int.toNat ((a i : ℤ) * (M : ℤ) + b i)
  let ww : ι → ℕ → ℚ := fun i n => w i (n + M)
  have hbB (i : ι) : Int.natAbs (b i) ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (f := fun j => Int.natAbs (b j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hb_lower (i : ι) : -(Int.natAbs (b i) : ℤ) ≤ b i := by
    simpa using neg_abs_le (b i)
  have hnonneg (i : ι) : 0 ≤ (a i : ℤ) * (M : ℤ) + b i := by
    have ha1 : 1 ≤ a i := ha i
    have hbi := hbB i
    have hBM : Int.natAbs (b i) < M := by
      dsimp [M]
      omega
    have hBMZ : (Int.natAbs (b i) : ℤ) < (M : ℤ) := by exact_mod_cast hBM
    have hM0 : (0 : ℤ) ≤ M := by positivity
    have hmul : (M : ℤ) ≤ (a i : ℤ) * M := by
      nlinarith
    linarith [hb_lower i]
  have hbb_cast (i : ι) : (bb i : ℤ) = (a i : ℤ) * (M : ℤ) + b i := by
    dsimp [bb]
    exact Int.toNat_of_nonneg (hnonneg i)
  have hcross' : ∀ i j, i ≠ j → a i * bb j ≠ a j * bb i := by
    intro i j hij heq
    apply hcross i j hij
    have heq' : (a i : ℤ) * (bb j : ℤ) = (a j : ℤ) * (bb i : ℤ) := by
      exact_mod_cast heq
    rw [hbb_cast i, hbb_cast j] at heq'
    nlinarith
  have hperiodic' : ∀ i, ∃ q : ℕ, 0 < q ∧ ∀ n, ww i (n + q) = ww i n := by
    intro i
    obtain ⟨q, hq, hqper⟩ := hperiodic i
    refine ⟨q, hq, ?_⟩
    intro n
    dsimp [ww]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hqper (n + M)
  have harg (i : ι) (n : ℕ) :
      integerAffineValue a b i (n + M) = a i * n + bb i := by
    apply Int.ofNat_inj.mp
    rw [Nat.cast_add, Nat.cast_mul, hbb_cast]
    rw [integerAffineValue, Int.toNat_of_nonneg]
    · push_cast
      ring
    · have ha0 : (0 : ℤ) ≤ a i := by positivity
      have hn0 : (0 : ℤ) ≤ n := by positivity
      push_cast
      nlinarith [hnonneg i]
  have hrel' : ∃ N₁, ∀ n, N₁ ≤ n →
      ∑ i, ww i n * (Nat.totient (a i * n + bb i) : ℚ) = 0 := by
    refine ⟨0, ?_⟩
    intro n _
    have hMge : N₀ ≤ n + M := by
      dsimp [M]
      omega
    have h := hN₀ (n + M) hMge
    simpa only [ww, harg] using h
  have hzero := ErdosProblems.Erdos249.PaperCompleteR7.periodic_freezing
    a bb ha hcross' ww hperiodic' hrel'
  intro i n
  obtain ⟨q, hq, hqper⟩ := hperiodic i
  have hMle : M ≤ n + q * M := by
    have hq1 : 1 ≤ q := hq
    nlinarith
  have hz := hzero i (n + q * M - M)
  change w i (n + q * M - M + M) = 0 at hz
  rw [Nat.sub_add_cancel hMle] at hz
  rw [ErdosProblems.Erdos249.PeriodicTotientIndependence.periodic_add_mul
    (w i) q hqper n M] at hz
  exact hz

#print axioms periodic_freezing_integer_affine

end ErdosProblems.Erdos249.PaperCompleteR20
