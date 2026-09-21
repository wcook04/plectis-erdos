import Erdos249257.HalfCylinderIntegerGreedy

namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

/-- The natural quotient is exactly the paper's real floor. -/
theorem row_weight_floor (n d : ℕ) (hd : 1 ≤ d) :
    ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋ = (truncatedMersenneWeight n d : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have hl := truncatedMersenneWeight_cast_le_scaled (s := n) hd
  have hu := scaled_lt_truncatedMersenneWeight_cast_add_one (s := n) hd
  push_cast
  simpa [mersenneWeight, div_eq_mul_inv] using And.intro hl hu

theorem row_weight_at_middle {n : ℕ} (hn : 2 ≤ n) :
    truncatedMersenneWeight n n = 2^n+1 := by
  rw [truncatedMersenneWeight_eq_geometricCore hn]
  simp [Nat.mul_div_right, Nat.mul_mod_right, Finset.sum_range_succ, add_comm, Nat.ne_of_gt (by omega : 0<n)]

theorem row_weight_above_middle {n d : ℕ} (hn : 2 ≤ n)
    (hnd : n < d) (hd : d ≤ 2*n) :
    truncatedMersenneWeight n d = 2^(2*n-d) := by
  have hq : (2*n)/d = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have hr : (2*n)%d = 2*n-d := by
    rw [Nat.mod_eq_sub_mod hd, Nat.mod_eq_of_lt (by omega)]
  rw [truncatedMersenneWeight_eq_geometricCore (by omega), hq, hr]
  simp

private theorem sum_two_pow_add_one (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 : ℕ)^i)+1 = 2^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- The full upper half of a quotient row has exact mass 2^(n+1). -/
theorem upper_row_sum {n : ℕ} (hn : 2 ≤ n) :
    ∑ d ∈ Finset.Ico n (2*n+1), truncatedMersenneWeight n d = 2^(n+1) := by
  have hsum : (∑ d ∈ Finset.Ico (n+1) (2*n+1), truncatedMersenneWeight n d) =
      ∑ i ∈ Finset.range n, (2 : ℕ)^i := by
    apply Finset.sum_bij (fun d _ ↦ 2*n-d)
    · intro d hd
      simp only [Finset.mem_Ico] at hd
      simp only [Finset.mem_range]
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Ico] at ha hb
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      refine ⟨2*n-i, ?_, ?_⟩
      · simp only [Finset.mem_Ico]; omega
      · omega
    · intro d hd
      simp only [Finset.mem_Ico] at hd
      exact row_weight_above_middle hn (by omega) (by omega)
  have hs := Finset.sum_Ico_consecutive (truncatedMersenneWeight n)
    (show n ≤ n+1 by omega) (show n+1 ≤ 2*n+1 by omega)
  simp only [Nat.Ico_succ_singleton, Finset.sum_singleton] at hs
  rw [row_weight_at_middle hn, hsum] at hs
  have hp := sum_two_pow_add_one n
  rw [pow_succ]
  omega

/-- Full-support carry K(2n), in the paper's integer coordinate. -/
def rowFullCarry (n : ℕ) : ℤ :=
  (2 : ℤ)^(2*n-1) - ∑ d ∈ Finset.Ico 2 (2*n+1), (truncatedMersenneWeight n d : ℤ)

/-- Delta for a selected prefix. This applies in particular to the integer
greedy take set; the identity itself needs no greediness hypothesis. -/
def rowDeviation (n : ℕ) (D : Finset ℕ) : ℤ :=
  (2 : ℤ)^(2*n-1) - (2 : ℤ)^(n+1) - ∑ d ∈ D, (truncatedMersenneWeight n d : ℤ)

/-- Exact whole master identity, stronger than the stated n>=6 greedy-row case. -/
theorem paper_master_identity {n : ℕ} (hn : 2 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    rowDeviation n D = rowFullCarry n +
      ∑ d ∈ (Finset.Ico 2 n) \ D, (truncatedMersenneWeight n d : ℤ) := by
  have hsplit := Finset.sum_Ico_consecutive
    (fun d ↦ (truncatedMersenneWeight n d : ℤ)) hn (show n ≤ 2*n+1 by omega)
  have hu : (∑ d ∈ Finset.Ico n (2*n+1), (truncatedMersenneWeight n d : ℤ)) =
      (2 : ℤ)^(n+1) := by exact_mod_cast upper_row_sum hn
  rw [hu] at hsplit
  have hd := Finset.sum_sdiff hD (f := fun d ↦ (truncatedMersenneWeight n d : ℤ))
  unfold rowDeviation rowFullCarry
  linarith

/-- Paper coordinates with literal real floors and both separate target offsets. -/
theorem paper_master_identity_floors {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ((2 : ℤ)^(2*n-1) - (2 : ℤ)^n -
      ∑ d ∈ D, ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋) - (2 : ℤ)^n =
    ((2 : ℤ)^(2*n-1) -
      ∑ d ∈ Finset.Ico 2 (2*n+1), ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋) +
      ∑ d ∈ (Finset.Ico 2 n) \ D, ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋ := by
  have hs (S : Finset ℕ) (hS : ∀ d ∈ S, 1 ≤ d) :
      (∑ d ∈ S, ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋) =
        ∑ d ∈ S, (truncatedMersenneWeight n d : ℤ) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact row_weight_floor n d (hS d hd)
  rw [hs D (by intro d hd; have := Finset.mem_Ico.mp (hD hd); omega),
    hs (Finset.Ico 2 (2*n+1)) (by intro d hd; have := Finset.mem_Ico.mp hd; omega),
    hs ((Finset.Ico 2 n) \ D) (by intro d hd; have := Finset.mem_Ico.mp (Finset.mem_sdiff.mp hd).1; omega)]
  have hi := paper_master_identity (show 2 ≤ n by omega) D hD
  unfold rowDeviation rowFullCarry at hi
  rw [pow_succ] at hi
  linarith

#print axioms paper_master_identity_floors
#print axioms row_weight_floor
#print axioms upper_row_sum
#print axioms paper_master_identity
end ErdosProblems.Erdos257.PaperCompleteR20
