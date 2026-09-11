import Mathlib

/-!
# Standalone actual-prime source slice

The elementary convergence proofs below are relocated from the pinned
PrimeGapDyadicTail.lean, commit d4fed71423840f70f10edf27b9ad27c22fc4f49a.
The original definitions are unchanged. A fresh namespace prevents duplicate
names when this packet is integrated into the full parent project. This is
source reuse, not a new convergence argument or a new verification receipt.
All declarations in this relocated module require fresh elaboration: UNRUN.
-/
noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR11.PrimeSource

/-- The actual zero-based prime enumeration, not an arbitrary model. -/
def prime0 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

def primeGap0 (n : ℕ) : ℕ := prime0 (n + 1) - prime0 n

def primeDyadicTerm (n : ℕ) : ℝ := (prime0 n : ℝ) / 2 ^ (n + 1)
def primeGapDyadicTerm (n : ℕ) : ℝ := (primeGap0 n : ℝ) / 2 ^ (n + 1)

@[simp] theorem prime0_zero : prime0 0 = 2 := by
  simp [prime0, Nat.nth_prime_zero_eq_two]

@[simp] theorem primeGap0_zero : primeGap0 0 = 1 := by
  simp [primeGap0, prime0, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

theorem prime0_strictMono : StrictMono prime0 :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

theorem prime0_mono_step (n : ℕ) : prime0 n ≤ prime0 (n + 1) :=
  prime0_strictMono.monotone (Nat.le_succ n)

theorem primeGap0_positive (n : ℕ) : 0 < primeGap0 n :=
  Nat.sub_pos_of_lt (prime0_strictMono (Nat.lt_succ_self n))

theorem primeGap0_even (n : ℕ) (hn : 1 ≤ n) : 2 ∣ primeGap0 n := by
  have hp (j : ℕ) : Nat.Prime (prime0 j) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j
  have hgt : 2 < prime0 n := by
    have h := prime0_strictMono (show 0 < n by omega)
    simpa using h
  have hgt' : 2 < prime0 (n + 1) := hgt.trans_le (prime0_mono_step n)
  have h0 := (hp n).mod_two_eq_one_iff_ne_two.mpr (by omega : prime0 n ≠ 2)
  have h1 := (hp (n + 1)).mod_two_eq_one_iff_ne_two.mpr (by omega : prime0 (n + 1) ≠ 2)
  apply Nat.dvd_of_mod_eq_zero
  unfold primeGap0
  have hm := prime0_mono_step n
  omega

theorem primeGapDyadicTerm_eq (n : ℕ) :
    primeGapDyadicTerm n = 2 * primeDyadicTerm (n + 1) - primeDyadicTerm n := by
  rw [primeGapDyadicTerm, primeDyadicTerm, primeDyadicTerm, primeGap0,
    Nat.cast_sub (prime0_mono_step n)]
  simp only [pow_succ]
  field_simp

-- The following convergence blocks retain the pinned source proofs.
theorem summable_primeDyadicTerm_of_polynomial_growth (C k : ℕ)
    (hgrowth : ∀ n, prime0 n ≤ C * (n + 1) ^ k) : Summable primeDyadicTerm := by
  have hpoly : Summable (fun n : ℕ => (n : ℝ) ^ k * ((1 / 2 : ℝ) ^ n)) := by
    exact summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
  have hshift : Summable (fun n : ℕ => (((1 + n : ℕ) : ℝ) ^ k) *
      ((1 / 2 : ℝ) ^ (1 + n))) := by
    simpa only [Function.comp_apply] using hpoly.comp_injective (add_right_injective 1)
  have hmajor : Summable (fun n : ℕ => (C : ℝ) *
      ((((1 + n : ℕ) : ℝ) ^ k) * ((1 / 2 : ℝ) ^ (1 + n)))) :=
    hshift.mul_left (C : ℝ)
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro n
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · intro n
    have hgrowthR : (prime0 n : ℝ) ≤ (C : ℝ) * (((1 + n : ℕ) : ℝ) ^ k) := by
      exact_mod_cast (by simpa [Nat.add_comm] using hgrowth n)
    rw [primeDyadicTerm]
    calc
      (prime0 n : ℝ) / 2 ^ (n + 1) ≤
          ((C : ℝ) * (((1 + n : ℕ) : ℝ) ^ k)) / 2 ^ (n + 1) :=
        div_le_div_of_nonneg_right hgrowthR (by positivity)
      _ = (C : ℝ) * ((((1 + n : ℕ) : ℝ) ^ k) * ((1 / 2 : ℝ) ^ (1 + n))) := by
        rw [Nat.add_comm n 1, one_div_pow]
        ring

theorem centralBinom_le_two_mul_pow_primeCounting (m : ℕ) (hm : 0 < m) :
    m.centralBinom ≤ (2 * m) ^ Nat.primeCounting (2 * m) := by
  have hfilter :
      (∏ p ∈ Finset.range (2 * m + 1) with p.Prime, p ^ m.centralBinom.factorization p) =
        ∏ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p := by
    refine Finset.prod_filter_of_ne fun p _hp hne => ?_
    contrapose! hne
    rw [Nat.factorization_eq_zero_of_not_prime m.centralBinom hne, pow_zero]
  rw [← Nat.prod_pow_factorization_centralBinom, ← hfilter]
  calc
    (∏ p ∈ Finset.range (2 * m + 1) with p.Prime, p ^ m.centralBinom.factorization p) ≤
        ∏ _p ∈ Finset.filter Nat.Prime (Finset.range (2 * m + 1)), 2 * m := by
      gcongr with p hp
      simpa [Nat.centralBinom] using
        (Nat.pow_factorization_choose_le (p := p) (k := m) (by omega : 0 < 2 * m))
    _ = (2 * m) ^ (Finset.filter Nat.Prime (Finset.range (2 * m + 1))).card := by simp
    _ = (2 * m) ^ Nat.primeCounting (2 * m) := by
      simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

theorem binomial_count_growth_bound (n : ℕ) :
    let m := (n + 5) ^ 4
    m * (2 * m) ^ n ≤ 4 ^ m := by
  let x := n + 5
  let m := x ^ 4
  have hxPow : x ≤ 2 ^ x := by
    induction x with
    | zero => simp
    | succ x ih =>
        rw [pow_succ]
        have hOne : 1 ≤ 2 ^ x := Nat.one_le_pow x 2 (by norm_num)
        omega
  have hExp : n + x * (4 * (n + 1)) ≤ 2 * m := by
    dsimp [x, m]
    nlinarith [sq_nonneg (n ^ 2 + 8 * n)]
  dsimp only
  change m * (2 * m) ^ n ≤ 4 ^ m
  calc
    m * (2 * m) ^ n = 2 ^ n * x ^ (4 * (n + 1)) := by
      simp only [m, mul_pow, pow_mul, pow_add]
      ring
    _ ≤ 2 ^ n * (2 ^ x) ^ (4 * (n + 1)) := by gcongr
    _ = 2 ^ (n + x * (4 * (n + 1))) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) hExp
    _ = 4 ^ m := by norm_num [pow_mul]

theorem lt_primeCounting_two_mul_fourth (n : ℕ) :
    n < Nat.primeCounting (2 * (n + 5) ^ 4) := by
  let m := (n + 5) ^ 4
  have hmFour : 4 ≤ m := by
    have hbase : 5 ≤ n + 5 := by omega
    have hpow := Nat.pow_le_pow_left hbase 4
    change 4 ≤ (n + 5) ^ 4
    calc
      4 ≤ 5 ^ 4 := by norm_num
      _ ≤ (n + 5) ^ 4 := hpow
  have hmPos : 0 < m := by omega
  have hcentral : 4 ^ m < m * m.centralBinom := Nat.four_pow_lt_mul_centralBinom m hmFour
  have hcentralBound : m.centralBinom ≤ (2 * m) ^ Nat.primeCounting (2 * m) :=
    centralBinom_le_two_mul_pow_primeCounting m hmPos
  have hgrowth : m * (2 * m) ^ n ≤ 4 ^ m := by
    simpa [m] using binomial_count_growth_bound n
  by_contra h
  have hcount : Nat.primeCounting (2 * m) ≤ n := Nat.le_of_not_gt (by simpa [m] using h)
  have hpow : (2 * m) ^ Nat.primeCounting (2 * m) ≤ (2 * m) ^ n :=
    Nat.pow_le_pow_right (by positivity) hcount
  have : m * m.centralBinom ≤ m * (2 * m) ^ n :=
    (Nat.mul_le_mul_left m hcentralBound).trans (Nat.mul_le_mul_left m hpow)
  omega

theorem prime0_le_polynomial (n : ℕ) : prime0 n ≤ 1250 * (n + 1) ^ 4 := by
  have hcount : n < Nat.count Nat.Prime (2 * (n + 5) ^ 4 + 1) := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using lt_primeCounting_two_mul_fourth n
  have hnth : prime0 n < 2 * (n + 5) ^ 4 + 1 := by
    rw [prime0]
    exact Nat.nth_lt_of_lt_count hcount
  have hbase : n + 5 ≤ 5 * (n + 1) := by omega
  have hpow := Nat.pow_le_pow_left hbase 4
  calc
    prime0 n ≤ 2 * (n + 5) ^ 4 := by omega
    _ ≤ 2 * (5 * (n + 1)) ^ 4 := Nat.mul_le_mul_left 2 hpow
    _ = 1250 * (n + 1) ^ 4 := by ring

theorem summable_primeDyadicTerm : Summable primeDyadicTerm :=
  summable_primeDyadicTerm_of_polynomial_growth 1250 4 prime0_le_polynomial

theorem summable_primeGapDyadicTerm : Summable primeGapDyadicTerm := by
  have hshift : Summable (fun n => primeDyadicTerm (n + 1)) := by
    simpa [Nat.add_comm] using summable_primeDyadicTerm.comp_injective (add_left_injective 1)
  exact ((hshift.mul_left 2).sub summable_primeDyadicTerm).congr fun n =>
    (primeGapDyadicTerm_eq n).symm

/-- Finite cumulative identity from the checked PaperCoreR7 proof. -/
theorem sum_prime_gaps (n : ℕ) : 2 + ∑ i ∈ range n, primeGap0 i = prime0 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← Nat.add_assoc, ih, primeGap0]
    have hm := prime0_mono_step n
    omega

/-- The actual scaled tail is defined using the convergent series. -/
def actualTail (N : ℕ) : ℝ := 2 ^ (N + 1) *
  ((∑' n, primeGapDyadicTerm n) - ∑ j ∈ range (N + 1), primeGapDyadicTerm j)

theorem actualTail_recurrence (N : ℕ) :
    actualTail (N + 1) = 2 * actualTail N - (primeGap0 (N + 1) : ℝ) := by
  unfold actualTail
  rw [show N + 1 + 1 = (N + 1) + 1 by omega, sum_range_succ]
  unfold primeGapDyadicTerm
  rw [pow_succ]
  have hp : (2 : ℝ) ^ (N + 1 + 1) ≠ 0 := by positivity
  have hp' : (2 : ℝ) ^ (N + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The series-tail formulation used in the paper, not just a recurrence model. -/
theorem actualTail_eq_shifted_sum (N : ℕ) :
    actualTail N = ∑' k : ℕ, (primeGap0 (N + k + 1) : ℝ) / 2 ^ (k + 1) := by
  have hshift : Summable (fun k => primeGapDyadicTerm (k + (N + 1))) := by
    simpa [Nat.add_comm] using
      summable_primeGapDyadicTerm.comp_injective (add_left_injective (N + 1))
  have hsplit := summable_primeGapDyadicTerm.sum_add_tsum_nat_add (N + 1)
  unfold actualTail
  rw [← hsplit]
  simp only [add_sub_cancel_left]
  rw [← (hshift.hasSum.mul_left (2 ^ (N + 1))).tsum_eq]
  apply tsum_congr
  intro k
  unfold primeGapDyadicTerm
  rw [show k + (N + 1) + 1 = (N + 1) + (k + 1) by omega, pow_add]
  rw [show k + (N + 1) = N + k + 1 by omega]
  field_simp
  rw [pow_add, pow_succ]
  ring

#print axioms summable_primeGapDyadicTerm
end ErdosProblems.Erdos251.PaperR11.PrimeSource
