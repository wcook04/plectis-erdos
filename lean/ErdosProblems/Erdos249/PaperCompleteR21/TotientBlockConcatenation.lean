import ErdosProblems.Erdos249.PeriodMultipleEscape

/-! Paper-form restatement of the long #249 paper's environment
"Concatenation and specified period multiples":

* the integer block sum `Q_{a,N} = ∑_{j=1}^{a} φ(N+j) 2^{a-j}` in the paper's
  index range, identified with the tree's `totientBlock`;
* the concatenation identity `Q_{a+b,N} = 2^b Q_{a,N} + Q_{b,N+a}` and its
  doubling instance `Q_{2h,N} = 2^h Q_{h,N} + Q_{h,N+h}`;
* the cyclotomic identity `Φ₄(2^h) = 2^{2h}+1 = Φ₂(2^{2h})`;
* the order-three factor `Φ₃(2^h) = 2^{2h}+2^h+1`;
* the worked instance `Φ₃(2) = 7`, which divides no `2^{2^j} - 1` because the
  order of `2` modulo `7` is `3` and `3 ∤ 2^j`. -/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open ErdosProblems.Erdos249.CyclotomicAnchoredKill
open ErdosProblems.Erdos249.PeriodMultipleEscape

/-! ### The block sum in the paper's index range -/

/-- **The integer block sum.**  `Q_{a,N} = ∑_{j=1}^{a} φ(N+j) 2^{a-j}`. -/
theorem totientBlock_eq_paper_indexed_sum (a N : ℕ) :
    totientBlock a N
      = ∑ j ∈ Finset.Icc 1 a, (Nat.totient (N + j) : ℤ) * 2 ^ (a - j) := by
  have hIccIco : Finset.Icc 1 a = Finset.Ico 1 (a + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIccIco, Finset.sum_Ico_eq_sum_range]
  have hn : a + 1 - 1 = a := by omega
  rw [hn]
  unfold totientBlock
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : N + 1 + j = N + (1 + j) := by omega
  have h2 : a - 1 - j = a - (1 + j) := by omega
  rw [h1, h2]

/-- **Block concatenation.**  Splitting a block after its first `a` terms
gives `Q_{a+b,N} = 2^b Q_{a,N} + Q_{b,N+a}`. -/
theorem totientBlock_concatenation (a b N : ℕ) :
    totientBlock (a + b) N = 2 ^ b * totientBlock a N + totientBlock b (N + a) :=
  totientBlock_add a b N

/-- **The doubling instance.**  `Q_{2h,N} = 2^h Q_{h,N} + Q_{h,N+h}`. -/
theorem totientBlock_doubling (h N : ℕ) :
    totientBlock (2 * h) N = 2 ^ h * totientBlock h N + totientBlock h (N + h) :=
  totientBlock_two_mul h N

/-! ### The cyclotomic identities -/

/-- `Φ₄(x) = x² + 1`. -/
theorem cyclotomic_four_eval (x : ℤ) :
    (Polynomial.cyclotomic 4 ℤ).eval x = x ^ 2 + 1 := by
  have h0 := Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1)
    Nat.prime_two
  rw [show (2 : ℕ) ^ (1 + 1) = 4 from by norm_num] at h0
  rw [h0]
  simp [Finset.sum_range_succ]
  try ring

/-- **The order-four factor at height `h` is the order-two factor at height
`2h`.**  `Φ₄(2^h) = 2^{2h} + 1 = Φ₂(2^{2h})`. -/
theorem cyclotomic_four_two_pow_eq_cyclotomic_two (h : ℕ) :
    (Polynomial.cyclotomic 4 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 1 ∧
      (Polynomial.cyclotomic 2 ℤ).eval ((2 : ℤ) ^ (2 * h)) = 2 ^ (2 * h) + 1 := by
  constructor
  · rw [cyclotomic_four_eval, ← pow_mul, mul_comm h 2]
  · rw [Polynomial.cyclotomic_two]
    simp

/-- **The order-three factor.**  `Φ₃(2^h) = 2^{2h} + 2^h + 1`. -/
theorem cyclotomic_three_two_pow (h : ℕ) :
    (Polynomial.cyclotomic 3 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 2 ^ h + 1 := by
  rw [Polynomial.cyclotomic_three]
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [← pow_mul, mul_comm h 2]

/-! ### The worked instance `Φ₃(2) = 7` -/

/-- The order of `2` modulo `7` is `3`. -/
theorem orderOf_two_mod_seven : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
  have h3 : ((2 : ℕ) : ZMod 7) ^ 3 = 1 := by decide
  have h1 : ((2 : ℕ) : ZMod 7) ≠ 1 := by decide
  have hdvd : orderOf ((2 : ℕ) : ZMod 7) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hdvd) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

/-- `3` never divides a power of `2`. -/
theorem three_not_dvd_two_pow (j : ℕ) : ¬ (3 ∣ 2 ^ j) := by
  intro hdvd
  have h := Nat.Prime.dvd_of_dvd_pow (p := 3) (by norm_num) hdvd
  omega

/-- **`Φ₃(2) = 7` divides none of the doubling-chain Mersenne numbers.**
`Φ₃(2) = 7`, the order of `2` modulo `7` is `3`, `3` divides no `2^j`, and
consequently `7 ∤ 2^{2^j} - 1` for every `j`. -/
theorem cyclotomic_three_eval_two_not_dvd_doubling_chain :
    (Polynomial.cyclotomic 3 ℤ).eval 2 = 7 ∧
      orderOf ((2 : ℕ) : ZMod 7) = 3 ∧
      (∀ j : ℕ, ¬ (3 ∣ 2 ^ j)) ∧
      (∀ j : ℕ, ¬ (7 ∣ 2 ^ 2 ^ j - 1)) := by
  refine ⟨?_, orderOf_two_mod_seven, three_not_dvd_two_pow, ?_⟩
  · rw [Polynomial.cyclotomic_three]
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X]
    norm_num
  · have key : ∀ j : ℕ, 2 ^ 2 ^ j % 7 = 2 ∨ 2 ^ 2 ^ j % 7 = 4 := by
      intro j
      induction j with
      | zero =>
        left
        norm_num
      | succ n ih =>
        have hstep : (2 : ℕ) ^ 2 ^ (n + 1) = (2 ^ 2 ^ n) ^ 2 := by
          rw [pow_succ, pow_mul]
        rw [hstep, Nat.pow_mod]
        rcases ih with h | h <;> rw [h] <;> norm_num
    intro j hdvd
    have hpos : 1 ≤ 2 ^ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨c, hc⟩ := hdvd
    have hdm := Nat.div_add_mod (2 ^ 2 ^ j) 7
    rcases key j with h | h <;> omega

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_eq_paper_indexed_sum
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_concatenation
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_doubling
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_eval
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_two_pow_eq_cyclotomic_two
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_two_pow
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.orderOf_two_mod_seven
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.three_not_dvd_two_pow
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_eval_two_not_dvd_doubling_chain
