import Erdos249257.HalfCarryReachability
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
Paper-form restatement of `record:257bm-i10` ("No finite support has value one
half") from the long Erdős #257 manuscript
`paper/reasoning-parts/erdos257/a257_front.tex:4611`.

The environment asserts three things, in this order:

1. a finite sum of reciprocals of odd integers has odd denominator in lowest
   terms — stated here for an arbitrary finite family of odd integers, not only
   for the Mersenne denominators;
2. hence such a sum cannot equal `1/2`;
3. applied to the denominators `2^a - 1`, a support representing `1/2` must be
   infinite.

Clause 1 is `paper_finite_sum_inv_odd_den_odd`, clause 2 is
`paper_finite_sum_inv_odd_ne_half`, and clause 3 is
`paper_half_representing_support_is_infinite`, routed through the specialisation
`paper_finiteErdosSum_den_odd` of clause 1 to `f a = 2 ^ a - 1`.
-/

open scoped BigOperators

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257

/-! ### The general premise: reciprocals of odd integers -/

/-- A divisor of an odd natural number is odd. -/
private theorem odd_of_dvd_odd {m n : ℕ} (hmn : m ∣ n) (hn : Odd n) : Odd m :=
  Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr hn).coprime_dvd_right hmn)

/-- Rationals with odd reduced denominator are closed under addition. -/
private theorem odd_den_add {a b : ℚ} (ha : Odd a.den) (hb : Odd b.den) :
    Odd (a + b).den :=
  odd_of_dvd_odd (Rat.add_den_dvd a b) (ha.mul hb)

/-- The reduced denominator of `1 / n` is odd when the integer `n` is odd. -/
private theorem odd_den_one_div_intCast {n : ℤ} (hn : Odd n) :
    Odd ((1 : ℚ) / (n : ℚ)).den := by
  have hdivInt : (1 : ℚ) / (n : ℚ) = Rat.divInt 1 n := (Rat.divInt_eq_div 1 n).symm
  have hdvdZ : (((Rat.divInt 1 n).den : ℕ) : ℤ) ∣ n := Rat.den_dvd 1 n
  have hdvd : ((1 : ℚ) / (n : ℚ)).den ∣ n.natAbs := by
    rw [hdivInt]
    simpa using Int.natAbs_dvd_natAbs.mpr hdvdZ
  exact odd_of_dvd_odd hdvd (Int.natAbs_odd.mpr hn)

/-- Paper display of the opening premise of `record:257bm-i10`: a finite sum of
reciprocals of odd integers has odd denominator in lowest terms. -/
theorem paper_finite_sum_inv_odd_den_odd {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    Odd (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)).den := by
  classical
  revert hodd
  induction s using Finset.induction_on with
  | empty =>
      intro _
      rw [Finset.sum_empty]
      exact ⟨0, by norm_num⟩
  | @insert a s ha ih =>
      intro hodd
      rw [Finset.sum_insert ha]
      exact odd_den_add
        (odd_den_one_div_intCast (hodd a (Finset.mem_insert_self a s)))
        (ih fun i hi => hodd i (Finset.mem_insert_of_mem hi))

/-- Paper display of the conclusion drawn from that premise: such a finite sum
cannot equal `1/2`, because `1/2` has even denominator. -/
theorem paper_finite_sum_inv_odd_ne_half {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)) ≠ (1 : ℚ) / 2 := by
  intro hhalf
  have hd := paper_finite_sum_inv_odd_den_odd s f hodd
  rw [hhalf] at hd
  obtain ⟨k, hk⟩ := hd
  norm_num at hk
  omega

/-! ### Applied to the Mersenne denominators `2 ^ a - 1` -/

/-- `2 ^ a - 1` is an odd integer for every positive exponent `a`. -/
private theorem odd_two_pow_sub_one {a : ℕ} (ha : a ≠ 0) :
    Odd ((2 : ℤ) ^ a - 1) :=
  (Int.even_pow.mpr ⟨even_two, ha⟩).sub_odd odd_one

/-- The specialisation the paper names: the finite base-two Erdős sum
`∑_{n ∈ F} 1 / (2 ^ n - 1)` over positive exponents has odd reduced
denominator.  This is the general premise above applied to `f a = 2 ^ a - 1`,
not a Mersenne-only argument. -/
theorem paper_finiteErdosSum_den_odd (F : Finset ℕ) (h0 : 0 ∉ F) :
    Odd (finiteErdosSum F 2).den := by
  have hodd : ∀ a ∈ F, Odd ((2 : ℤ) ^ a - 1) := by
    intro a ha
    refine odd_two_pow_sub_one ?_
    rintro rfl
    exact h0 ha
  have h := paper_finite_sum_inv_odd_den_odd F (fun a => (2 : ℤ) ^ a - 1) hodd
  have hsum :
      (∑ a ∈ F, (1 : ℚ) / ((((2 : ℤ) ^ a - 1 : ℤ)) : ℚ)) = finiteErdosSum F 2 := by
    unfold finiteErdosSum
    refine Finset.sum_congr rfl ?_
    intro a _
    push_cast
    ring
  rw [← hsum]
  exact h

/-- Paper display of `record:257bm-i10`: a finite positive-index support cannot
have support-series value `1/2`. -/
theorem paper_finite_support_series_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2 := by
  classical
  let F : Finset ℕ := hfinite.toFinset
  have hFA : (↑F : Set ℕ) = A := by
    dsimp [F]
    exact hfinite.coe_toFinset
  have hFzero : 0 ∉ F := by
    intro hmem
    apply hzero
    rw [← hFA]
    simpa using hmem
  intro hhalf
  have hcast : ((finiteErdosSum F 2 : ℚ) : ℝ) = (1 : ℝ) / 2 := by
    rw [← erdosSupportSeries_finset_eq_cast_finiteErdosSum F, hFA]
    exact hhalf
  have hrat : finiteErdosSum F 2 = (1 : ℚ) / 2 := by
    apply Rat.cast_injective (α := ℝ)
    simpa using hcast
  have hodd := paper_finiteErdosSum_den_odd F hFzero
  rw [hrat] at hodd
  obtain ⟨k, hk⟩ := hodd
  norm_num at hk
  omega

/-- The consequence the same environment draws: a support representing `1/2`
must be infinite. -/
theorem paper_half_representing_support_is_infinite
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2) :
    A.Infinite :=
  fun hfinite => paper_finite_support_series_ne_half A hfinite hzero hvalue

#print axioms paper_finite_sum_inv_odd_den_odd
#print axioms paper_finite_sum_inv_odd_ne_half
#print axioms paper_finiteErdosSum_den_odd
#print axioms paper_finite_support_series_ne_half
#print axioms paper_half_representing_support_is_infinite

end ErdosProblems.Erdos257.PaperCompleteR21
