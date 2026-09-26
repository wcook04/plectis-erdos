import ErdosProblems.Erdos269.DistinctHeightBlockRadix
import ErdosProblems.Erdos269.ThreePrimeRunningLcm

/-!
# Erdős #269: the distinct-height sum `𝒟_{2,3,5}` is irrational

Let `H(t) = 2^⌊log₂ t⌋ · 3^⌊log₃ t⌋ · 5^⌊log₅ t⌋` (`runningHeight235`).  For
`t ≥ 1` this is the running least common multiple of the `{2,3,5}`-smooth
integers not exceeding `t` (`smoothPrefixLcm_eq_runningHeight235`).  The #269
long record defines the distinct-height sum

    𝒟_{2,3,5} = 1 + ∑_{t ∈ {2^n, 3^n, 5^n : n ≥ 1}} 1 / H(t),

which counts every value of the running LCM once, at the jump where it first
appears.  This module proves

* `distinctHeightSum235_irrational : Irrational distinctHeightSum235`, the sum
  over the jump points exactly as displayed above, and
* `distinctHeightSum235_eq_tsum_range` together with
  `irrational_tsum_range_runningHeight235`: the same number is
  `∑' h : Set.range runningHeight235, 1 / h`, the sum of `1 / h` over the
  distinct values `h` of `H`, and it is irrational.

Erdős asserted the irrationality of distinct-height sums for finite sets of
primes in a letter of 1 January 1973 (Fibonacci Quarterly 12 (1974), p. 335)
and printed no argument.

## Route

Group the jump points into the dyadic blocks `(2^a, 2^(a+1)]`.  Each block
contains `2^(a+1)`, at most one power of `3` (`firstPow 3 a`, the first power of
`3` above `2^a`) and at most one power of `5` (`firstPow 5 a`), so its
contribution is `blockNum a / H(2^(a+1))` with `H(2^(a+1)) = blockBase a · H(2^a)`
and `(blockBase a, blockNum a)` one of the five block letters of
`ErdosProblems.Erdos269.DistinctHeightBlockRadix` (`sum_block_jumpTerm_eq`).
Every three consecutive blocks contain a power of `5`, because `4 < 5 < 8`
(`five_spacing`), and the blocks containing a power of `3` are not eventually
periodic, because `2^d = 3^c` is impossible for `d ≥ 1`
(`blockBase_not_eventually_periodic`).  The criterion
`irrational_tsum_blockTerm` then applies.
-/

namespace ErdosProblems.Erdos269

open Finset Filter Topology
open DistinctHeight235

/-- The running height `H(t) = 2^⌊log₂ t⌋ · 3^⌊log₃ t⌋ · 5^⌊log₅ t⌋`.  For `t ≥ 1`
it is the least common multiple of the `{2,3,5}`-smooth integers `≤ t`
(`smoothPrefixLcm_eq_runningHeight235`); it is `threePrimeHeight 2 3 5`. -/
def runningHeight235 (t : ℕ) : ℕ :=
  2 ^ Nat.log 2 t * 3 ^ Nat.log 3 t * 5 ^ Nat.log 5 t

theorem runningHeight235_eq_threePrimeHeight (t : ℕ) :
    runningHeight235 t = threePrimeHeight 2 3 5 t :=
  rfl

/-- `H(t)` is the literal running least common multiple of the `{2,3,5}`-smooth
integers not exceeding `t`. -/
theorem smoothPrefixLcm_eq_runningHeight235 {t : ℕ} (ht : t ≠ 0) :
    smoothPrefixLcm 2 3 5 t = runningHeight235 t :=
  smoothPrefixLcm_eq_threePrimeHeight Nat.prime_two Nat.prime_three Nat.prime_five
    (by norm_num) (by norm_num) (by norm_num) ht

/-- The jump points of the running height: the positive powers of `2`, `3`
and `5`. -/
def jumpPoints235 : Set ℕ :=
  {t | ∃ n, 1 ≤ n ∧ (t = 2 ^ n ∨ t = 3 ^ n ∨ t = 5 ^ n)}

/-- **The distinct-height sum**
`𝒟_{2,3,5} = 1 + ∑_{t ∈ {2^n, 3^n, 5^n : n ≥ 1}} 1 / H(t)` of the #269 long record,
with `H(t) = 2^⌊log₂ t⌋ 3^⌊log₃ t⌋ 5^⌊log₅ t⌋` the running LCM: the initial value
`1` plus one reciprocal `1 / H(t)` for every jump point `t`.  Every distinct value
of the running LCM is counted exactly once
(`distinctHeightSum235_eq_tsum_range`). -/
noncomputable def distinctHeightSum235 : ℝ :=
  1 + ∑' t : jumpPoints235, (1 : ℝ) / (runningHeight235 t : ℝ)

namespace DistinctHeight235

theorem mem_jumpPoints235 {t : ℕ} :
    t ∈ jumpPoints235 ↔ ∃ n, 1 ≤ n ∧ (t = 2 ^ n ∨ t = 3 ^ n ∨ t = 5 ^ n) :=
  Iff.rfl

theorem runningHeight235_pos (t : ℕ) : 0 < runningHeight235 t := by
  unfold runningHeight235
  positivity

theorem runningHeight235_zero : runningHeight235 0 = 1 := by
  simp [runningHeight235]

theorem runningHeight235_one : runningHeight235 1 = 1 := by
  simp [runningHeight235, Nat.log_one_right]

theorem runningHeight235_two_pow (a : ℕ) :
    runningHeight235 (2 ^ a) = 2 ^ a * 3 ^ Nat.log 3 (2 ^ a) * 5 ^ Nat.log 5 (2 ^ a) := by
  unfold runningHeight235
  rw [Nat.log_pow (by norm_num : 1 < 2)]

theorem zero_not_mem_jumpPoints235 : 0 ∉ jumpPoints235 := by
  intro h
  obtain ⟨n, -, h | h | h⟩ := mem_jumpPoints235.mp h <;>
    exact absurd h.symm (pow_ne_zero _ (by norm_num))

theorem one_not_mem_jumpPoints235 : 1 ∉ jumpPoints235 := by
  intro h
  obtain ⟨n, hn, h | h | h⟩ := mem_jumpPoints235.mp h
  · have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  · have : 3 ^ 1 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  · have : 5 ^ 1 ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega

/-! ## One dyadic block -/

/-- The first power of `p` above `2^a`. -/
def firstPow (p a : ℕ) : ℕ :=
  p ^ (Nat.log p (2 ^ a) + 1)

theorem two_pow_lt_firstPow {p : ℕ} (hp : 2 ≤ p) (a : ℕ) : 2 ^ a < firstPow p a :=
  Nat.lt_pow_succ_log_self (by omega) _

theorem pow_log_two_pow_le (p a : ℕ) : p ^ Nat.log p (2 ^ a) ≤ 2 ^ a :=
  Nat.pow_log_le_self p (by positivity)

theorem two_pow_succ_lt_mul_firstPow {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    2 ^ (a + 1) < p * firstPow p a := by
  have h := two_pow_lt_firstPow hp a
  calc 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    _ < 2 * firstPow p a := by omega
    _ ≤ p * firstPow p a := Nat.mul_le_mul_right _ hp

/-- Inside `[2^a, 2^(a+1)]` the base-`p` logarithm is `⌊log_p 2^a⌋` or one more,
and it is one more exactly from `firstPow p a` on. -/
theorem log_eq_of_mem_block {p a x : ℕ} (hp : 2 ≤ p) (hx₁ : 2 ^ a ≤ x)
    (hx₂ : x ≤ 2 ^ (a + 1)) :
    Nat.log p x =
      if firstPow p a ≤ x then Nat.log p (2 ^ a) + 1 else Nat.log p (2 ^ a) := by
  have hlow := pow_log_two_pow_le p a
  have hup := two_pow_succ_lt_mul_firstPow hp a
  split_ifs with h
  · refine Nat.log_eq_of_pow_le_of_lt_pow h ?_
    calc x ≤ 2 ^ (a + 1) := hx₂
      _ < p * firstPow p a := hup
      _ = p ^ (Nat.log p (2 ^ a) + 1 + 1) := by unfold firstPow; ring
  · exact Nat.log_eq_of_pow_le_of_lt_pow (hlow.trans hx₁) (not_le.mp h)

theorem firstPow_ne_two_pow {p : ℕ} (hp : Odd p) (a n : ℕ) : firstPow p a ≠ 2 ^ (n + 1) := by
  intro h
  have h1 : Odd (firstPow p a) := hp.pow
  rw [h] at h1
  exact (Nat.not_even_iff_odd.mpr h1) ((even_two).pow_of_ne_zero (by omega))

theorem firstPow_three_ne_firstPow_five (a : ℕ) : firstPow 3 a ≠ firstPow 5 a := by
  intro h
  have h3 : 3 ∣ firstPow 3 a := dvd_pow_self 3 (Nat.succ_ne_zero _)
  rw [h] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

/-- A power of `p` lying in the dyadic block `(2^a, 2^(a+1)]` is `firstPow p a`. -/
theorem pow_eq_firstPow_of_mem_block {p a n : ℕ} (hp : 2 ≤ p) (h₁ : 2 ^ a < p ^ n)
    (h₂ : p ^ n ≤ 2 ^ (a + 1)) : p ^ n = firstPow p a := by
  have hp1 : 1 < p := by omega
  have hlt : Nat.log p (2 ^ a) < n := (Nat.log_lt_iff_lt_pow hp1 (by positivity)).mpr h₁
  have hn : n < Nat.log p (2 ^ a) + 2 := by
    refine (Nat.pow_lt_pow_iff_right hp1).mp ?_
    calc p ^ n ≤ 2 ^ (a + 1) := h₂
      _ < p * firstPow p a := two_pow_succ_lt_mul_firstPow hp a
      _ = p ^ (Nat.log p (2 ^ a) + 2) := by unfold firstPow; ring
  unfold firstPow
  rw [show n = Nat.log p (2 ^ a) + 1 by omega]

/-- The jump points in the block `(2^a, 2^(a+1)]` are `2^(a+1)`, `firstPow 3 a` when
it is at most `2^(a+1)`, and `firstPow 5 a` when it is at most `2^(a+1)`. -/
theorem mem_jumpPoints235_iff_of_mem_block {a t : ℕ} (h₁ : 2 ^ a < t)
    (h₂ : t ≤ 2 ^ (a + 1)) :
    t ∈ jumpPoints235 ↔
      t = 2 ^ (a + 1) ∨ (firstPow 3 a ≤ 2 ^ (a + 1) ∧ t = firstPow 3 a) ∨
        (firstPow 5 a ≤ 2 ^ (a + 1) ∧ t = firstPow 5 a) := by
  constructor
  · intro ht
    obtain ⟨n, hn, h | h | h⟩ := mem_jumpPoints235.mp ht <;> subst h
    · left
      have e1 : a < n := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h₁
      have e2 : n ≤ a + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h₂
      rw [show n = a + 1 by omega]
    · have heq := pow_eq_firstPow_of_mem_block (by norm_num) h₁ h₂
      exact Or.inr (Or.inl ⟨by rw [← heq]; exact h₂, heq⟩)
    · have heq := pow_eq_firstPow_of_mem_block (by norm_num) h₁ h₂
      exact Or.inr (Or.inr ⟨by rw [← heq]; exact h₂, heq⟩)
  · rintro (h | ⟨-, h⟩ | ⟨-, h⟩) <;> subst h <;> refine mem_jumpPoints235.mpr ?_
    · exact ⟨a + 1, by omega, Or.inl rfl⟩
    · exact ⟨Nat.log 3 (2 ^ a) + 1, by omega, Or.inr (Or.inl rfl)⟩
    · exact ⟨Nat.log 5 (2 ^ a) + 1, by omega, Or.inr (Or.inr rfl)⟩

/-- `1 / H(t)`. -/
noncomputable def recipHeight (t : ℕ) : ℝ :=
  (1 : ℝ) / (runningHeight235 t : ℝ)

/-- The reciprocal running height at the jump points, and `0` elsewhere. -/
noncomputable def jumpTerm : ℕ → ℝ :=
  jumpPoints235.indicator recipHeight

theorem jumpTerm_nonneg (t : ℕ) : 0 ≤ jumpTerm t :=
  Set.indicator_nonneg (fun _ _ => by unfold recipHeight; positivity) t

theorem jumpTerm_zero : jumpTerm 0 = 0 :=
  Set.indicator_of_notMem zero_not_mem_jumpPoints235 _

theorem jumpTerm_one : jumpTerm 1 = 0 :=
  Set.indicator_of_notMem one_not_mem_jumpPoints235 _

theorem jumpTerm_eq_of_mem_block {a t : ℕ} (h₁ : 2 ^ a < t) (h₂ : t ≤ 2 ^ (a + 1)) :
    jumpTerm t =
      (if t = 2 ^ (a + 1) then recipHeight t else 0) +
      (if firstPow 3 a ≤ 2 ^ (a + 1) ∧ t = firstPow 3 a then recipHeight t else 0) +
      (if firstPow 5 a ≤ 2 ^ (a + 1) ∧ t = firstPow 5 a then recipHeight t else 0) := by
  have hmem := mem_jumpPoints235_iff_of_mem_block h₁ h₂
  have h23 : firstPow 3 a ≠ 2 ^ (a + 1) := firstPow_ne_two_pow ⟨1, by norm_num⟩ a a
  have h25 : firstPow 5 a ≠ 2 ^ (a + 1) := firstPow_ne_two_pow ⟨2, by norm_num⟩ a a
  have h35 : firstPow 3 a ≠ firstPow 5 a := firstPow_three_ne_firstPow_five a
  unfold jumpTerm
  by_cases hJ : t ∈ jumpPoints235
  · rw [Set.indicator_of_mem hJ]
    rcases hmem.mp hJ with hA | hB | hC
    · have n3 : ¬ (firstPow 3 a ≤ 2 ^ (a + 1) ∧ t = firstPow 3 a) :=
        fun h => h23 (h.2.symm.trans hA)
      have n5 : ¬ (firstPow 5 a ≤ 2 ^ (a + 1) ∧ t = firstPow 5 a) :=
        fun h => h25 (h.2.symm.trans hA)
      rw [if_pos hA, if_neg n3, if_neg n5]
      ring
    · have n2 : ¬ t = 2 ^ (a + 1) := fun h => h23 (hB.2.symm.trans h)
      have n5 : ¬ (firstPow 5 a ≤ 2 ^ (a + 1) ∧ t = firstPow 5 a) :=
        fun h => h35 (hB.2.symm.trans h.2)
      rw [if_neg n2, if_pos hB, if_neg n5]
      ring
    · have n2 : ¬ t = 2 ^ (a + 1) := fun h => h25 (hC.2.symm.trans h)
      have n3 : ¬ (firstPow 3 a ≤ 2 ^ (a + 1) ∧ t = firstPow 3 a) :=
        fun h => h35 (h.2.symm.trans hC.2)
      rw [if_neg n2, if_neg n3, if_pos hC]
      ring
  · have n2 : ¬ t = 2 ^ (a + 1) := fun h => hJ (hmem.mpr (Or.inl h))
    have n3 : ¬ (firstPow 3 a ≤ 2 ^ (a + 1) ∧ t = firstPow 3 a) :=
      fun h => hJ (hmem.mpr (Or.inr (Or.inl h)))
    have n5 : ¬ (firstPow 5 a ≤ 2 ^ (a + 1) ∧ t = firstPow 5 a) :=
      fun h => hJ (hmem.mpr (Or.inr (Or.inr h)))
    rw [Set.indicator_of_notMem hJ, if_neg n2, if_neg n3, if_neg n5]
    ring

/-- The jump terms of one dyadic block. -/
theorem sum_block_jumpTerm (a : ℕ) :
    ∑ t ∈ Ioc (2 ^ a) (2 ^ (a + 1)), jumpTerm t =
      recipHeight (2 ^ (a + 1)) +
      (if firstPow 3 a ≤ 2 ^ (a + 1) then recipHeight (firstPow 3 a) else 0) +
      (if firstPow 5 a ≤ 2 ^ (a + 1) then recipHeight (firstPow 5 a) else 0) := by
  rw [sum_congr rfl fun t ht => jumpTerm_eq_of_mem_block (a := a) (mem_Ioc.mp ht).1
      (mem_Ioc.mp ht).2, sum_add_distrib, sum_add_distrib]
  have hlt : 2 ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h3lo : 2 ^ a < firstPow 3 a := two_pow_lt_firstPow (by norm_num) a
  have h5lo : 2 ^ a < firstPow 5 a := two_pow_lt_firstPow (by norm_num) a
  congr 1
  congr 1
  · rw [sum_ite_eq', if_pos (mem_Ioc.mpr ⟨hlt, le_rfl⟩)]
  · by_cases c : firstPow 3 a ≤ 2 ^ (a + 1)
    · simp only [c, true_and, ↓reduceIte]
      rw [sum_ite_eq', if_pos (mem_Ioc.mpr ⟨h3lo, c⟩)]
    · simp only [c, false_and, ↓reduceIte, sum_const_zero]
  · by_cases c : firstPow 5 a ≤ 2 ^ (a + 1)
    · simp only [c, true_and, ↓reduceIte]
      rw [sum_ite_eq', if_pos (mem_Ioc.mpr ⟨h5lo, c⟩)]
    · simp only [c, false_and, ↓reduceIte, sum_const_zero]

/-- The radix `H(2^(a+1)) / H(2^a)` of the dyadic block `(2^a, 2^(a+1)]`. -/
def blockBase (a : ℕ) : ℕ :=
  if firstPow 3 a ≤ 2 ^ (a + 1) then
    (if firstPow 5 a ≤ 2 ^ (a + 1) then 30 else 6)
  else
    (if firstPow 5 a ≤ 2 ^ (a + 1) then 10 else 2)

/-- The numerator `H(2^(a+1)) · ∑_{t ∈ (2^a, 2^(a+1)]} 1 / H(t)` of the dyadic block,
the sum running over jump points. -/
def blockNum (a : ℕ) : ℕ :=
  if firstPow 3 a ≤ 2 ^ (a + 1) then
    (if firstPow 5 a ≤ 2 ^ (a + 1) then (if firstPow 3 a < firstPow 5 a then 13 else 9)
      else 3)
  else
    (if firstPow 5 a ≤ 2 ^ (a + 1) then 3 else 1)

theorem blockLetter_blockBase_blockNum (a : ℕ) : BlockLetter (blockBase a) (blockNum a) := by
  unfold blockBase blockNum BlockLetter
  split_ifs <;> simp

theorem runningHeight235_two_pow_succ (a : ℕ) :
    runningHeight235 (2 ^ (a + 1)) = blockBase a * runningHeight235 (2 ^ a) := by
  have hx : 2 ^ a ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have l3 := log_eq_of_mem_block (p := 3) (by norm_num) hx le_rfl
  have l5 := log_eq_of_mem_block (p := 5) (by norm_num) hx le_rfl
  rw [runningHeight235_two_pow a]
  unfold runningHeight235
  rw [Nat.log_pow (by norm_num : 1 < 2), l3, l5]
  unfold blockBase
  split_ifs <;> ring

theorem runningHeight235_firstPow_three {a : ℕ} (h3 : firstPow 3 a ≤ 2 ^ (a + 1)) :
    runningHeight235 (firstPow 3 a) =
      3 * (if firstPow 5 a ≤ firstPow 3 a then 5 else 1) * runningHeight235 (2 ^ a) := by
  have hlo : 2 ^ a < firstPow 3 a := two_pow_lt_firstPow (by norm_num) a
  have hhi : firstPow 3 a < 2 ^ (a + 1) :=
    lt_of_le_of_ne h3 (firstPow_ne_two_pow ⟨1, by norm_num⟩ a a)
  have l2 : Nat.log 2 (firstPow 3 a) = a := Nat.log_eq_of_pow_le_of_lt_pow hlo.le hhi
  have l3 : Nat.log 3 (firstPow 3 a) = Nat.log 3 (2 ^ a) + 1 :=
    Nat.log_pow (by norm_num) _
  have l5 := log_eq_of_mem_block (p := 5) (by norm_num) hlo.le h3
  rw [runningHeight235_two_pow a]
  unfold runningHeight235
  rw [l2, l3, l5]
  split_ifs <;> ring

theorem runningHeight235_firstPow_five {a : ℕ} (h5 : firstPow 5 a ≤ 2 ^ (a + 1)) :
    runningHeight235 (firstPow 5 a) =
      5 * (if firstPow 3 a ≤ firstPow 5 a then 3 else 1) * runningHeight235 (2 ^ a) := by
  have hlo : 2 ^ a < firstPow 5 a := two_pow_lt_firstPow (by norm_num) a
  have hhi : firstPow 5 a < 2 ^ (a + 1) :=
    lt_of_le_of_ne h5 (firstPow_ne_two_pow ⟨2, by norm_num⟩ a a)
  have l2 : Nat.log 2 (firstPow 5 a) = a := Nat.log_eq_of_pow_le_of_lt_pow hlo.le hhi
  have l3 := log_eq_of_mem_block (p := 3) (by norm_num) hlo.le h5
  have l5 : Nat.log 5 (firstPow 5 a) = Nat.log 5 (2 ^ a) + 1 :=
    Nat.log_pow (by norm_num) _
  rw [runningHeight235_two_pow a]
  unfold runningHeight235
  rw [l2, l3, l5]
  split_ifs <;> ring

/-- **One dyadic block.**  The jump points of `(2^a, 2^(a+1)]` contribute
`blockNum a / H(2^(a+1))`. -/
theorem sum_block_jumpTerm_eq (a : ℕ) :
    ∑ t ∈ Ioc (2 ^ a) (2 ^ (a + 1)), jumpTerm t =
      (blockNum a : ℝ) / (runningHeight235 (2 ^ (a + 1)) : ℝ) := by
  have h35 := firstPow_three_ne_firstPow_five a
  rw [sum_block_jumpTerm]
  unfold recipHeight
  rw [runningHeight235_two_pow_succ]
  by_cases c3 : firstPow 3 a ≤ 2 ^ (a + 1) <;> by_cases c5 : firstPow 5 a ≤ 2 ^ (a + 1)
  · rw [if_pos c3, if_pos c5, runningHeight235_firstPow_three c3,
      runningHeight235_firstPow_five c5]
    rcases lt_or_gt_of_ne h35 with o | o
    · simp only [blockNum, blockBase, c3, c5, o, not_le.mpr o, o.le, ↓reduceIte]
      push_cast
      ring
    · simp only [blockNum, blockBase, c3, c5, not_lt.mpr o.le, o.le, not_le.mpr o,
        ↓reduceIte]
      push_cast
      ring
  · have o : ¬ firstPow 5 a ≤ firstPow 3 a := fun h => c5 (h.trans c3)
    rw [if_pos c3, if_neg c5, runningHeight235_firstPow_three c3]
    simp only [blockNum, blockBase, c3, c5, o, ↓reduceIte]
    push_cast
    ring
  · have o : ¬ firstPow 3 a ≤ firstPow 5 a := fun h => c3 (h.trans c5)
    rw [if_neg c3, if_pos c5, runningHeight235_firstPow_five c5]
    simp only [blockNum, blockBase, c3, c5, o, ↓reduceIte]
    push_cast
    ring
  · rw [if_neg c3, if_neg c5]
    simp only [blockNum, blockBase, c3, c5, ↓reduceIte]
    push_cast
    ring

theorem radixProd_blockBase (a : ℕ) : radixProd blockBase a = runningHeight235 (2 ^ a) := by
  induction a with
  | zero => simp [runningHeight235, Nat.log_one_right]
  | succ a ih => rw [radixProd_succ, ih, runningHeight235_two_pow_succ, Nat.mul_comm]

/-! ## From the jump points to the block series -/

/-- The jump terms of the dyadic block `(2^a, 2^(a+1)]`. -/
noncomputable def blockSum (a : ℕ) : ℝ :=
  ∑ t ∈ Ioc (2 ^ a) (2 ^ (a + 1)), jumpTerm t

theorem blockSum_eq_blockTerm (a : ℕ) : blockSum a = blockTerm blockBase blockNum a := by
  rw [blockSum, sum_block_jumpTerm_eq, blockTerm, radixProd_blockBase]

theorem sum_range_jumpTerm (A : ℕ) :
    ∑ t ∈ range (2 ^ A + 1), jumpTerm t = ∑ a ∈ range A, blockSum a := by
  induction A with
  | zero => simp [sum_range_succ, jumpTerm_zero, jumpTerm_one]
  | succ A ih =>
    rw [sum_range_succ blockSum A, ← ih, blockSum, ← Finset.Ico_add_one_add_one_eq_Ioc,
      sum_range_add_sum_Ico jumpTerm
        (Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1)]

/-- The jump terms sum to the block series. -/
theorem hasSum_jumpTerm : HasSum jumpTerm (∑' a, blockTerm blockBase blockNum a) := by
  have hsb := summable_blockTerm blockLetter_blockBase_blockNum
  have hpart : ∀ A, ∑ t ∈ range (2 ^ A + 1), jumpTerm t =
      ∑ a ∈ range A, blockTerm blockBase blockNum a := fun A => by
    rw [sum_range_jumpTerm]
    exact sum_congr rfl fun a _ => blockSum_eq_blockTerm a
  have hbound : ∀ n, ∑ t ∈ range n, jumpTerm t ≤ ∑' a, blockTerm blockBase blockNum a := by
    intro n
    calc ∑ t ∈ range n, jumpTerm t ≤ ∑ t ∈ range (2 ^ n + 1), jumpTerm t :=
          sum_le_sum_of_subset_of_nonneg
            (range_subset_range.mpr (by have := Nat.lt_two_pow_self (n := n); omega))
            (fun t _ _ => jumpTerm_nonneg t)
      _ = ∑ a ∈ range n, blockTerm blockBase blockNum a := hpart n
      _ ≤ ∑' a, blockTerm blockBase blockNum a :=
          hsb.sum_le_tsum _ (fun a _ => blockTerm_nonneg _ _ a)
  have hsF : Summable jumpTerm := summable_of_sum_range_le jumpTerm_nonneg hbound
  have hmono : Tendsto (fun A : ℕ => 2 ^ A + 1) atTop atTop :=
    tendsto_atTop_mono (fun A => (Nat.lt_two_pow_self (n := A)).le.trans (Nat.le_succ _))
      tendsto_id
  have h1 : Tendsto (fun A => ∑ t ∈ range (2 ^ A + 1), jumpTerm t) atTop
      (𝓝 (∑' t, jumpTerm t)) :=
    hsF.hasSum.tendsto_sum_nat.comp hmono
  have h2 : Tendsto (fun A => ∑ t ∈ range (2 ^ A + 1), jumpTerm t) atTop
      (𝓝 (∑' a, blockTerm blockBase blockNum a)) :=
    hsb.hasSum.tendsto_sum_nat.congr fun A => (hpart A).symm
  rw [← tendsto_nhds_unique h1 h2]
  exact hsF.hasSum

/-! ## The powers of `5` and the powers of `3` -/

theorem five_dvd_blockBase_iff (a : ℕ) : 5 ∣ blockBase a ↔ firstPow 5 a ≤ 2 ^ (a + 1) := by
  unfold blockBase
  by_cases c3 : firstPow 3 a ≤ 2 ^ (a + 1) <;> by_cases c5 : firstPow 5 a ≤ 2 ^ (a + 1) <;>
    simp only [c3, c5, ↓reduceIte, iff_true, iff_false] <;> omega

theorem three_dvd_blockBase_iff (a : ℕ) : 3 ∣ blockBase a ↔ firstPow 3 a ≤ 2 ^ (a + 1) := by
  unfold blockBase
  by_cases c3 : firstPow 3 a ≤ 2 ^ (a + 1) <;> by_cases c5 : firstPow 5 a ≤ 2 ^ (a + 1) <;>
    simp only [c3, c5, ↓reduceIte, iff_true, iff_false] <;> omega

/-- **Every three consecutive blocks contain a power of `5`**, since consecutive
powers of `5` differ by the factor `5 < 8`. -/
theorem five_spacing (a : ℕ) :
    5 ∣ blockBase a ∨ 5 ∣ blockBase (a + 1) ∨ 5 ∣ blockBase (a + 2) := by
  rw [five_dvd_blockBase_iff, five_dvd_blockBase_iff, five_dvd_blockBase_iff]
  have hhi : firstPow 5 a < 2 ^ (a + 3) := by
    have h := pow_log_two_pow_le 5 a
    have e : firstPow 5 a = 5 * 5 ^ Nat.log 5 (2 ^ a) := by unfold firstPow; ring
    have e8 : 2 ^ (a + 3) = 8 * 2 ^ a := by ring
    have hpos : 0 < 2 ^ a := by positivity
    rw [e, e8]
    omega
  by_cases h1 : firstPow 5 a ≤ 2 ^ (a + 1)
  · exact Or.inl h1
  · right
    by_cases h2 : firstPow 5 a ≤ 2 ^ (a + 2)
    · left
      have heq := pow_eq_firstPow_of_mem_block (p := 5) (a := a + 1) (by norm_num)
        (show 2 ^ (a + 1) < 5 ^ (Nat.log 5 (2 ^ a) + 1) from not_le.mp h1) h2
      rw [← heq]
      exact h2
    · right
      have heq := pow_eq_firstPow_of_mem_block (p := 5) (a := a + 2) (by norm_num)
        (show 2 ^ (a + 2) < 5 ^ (Nat.log 5 (2 ^ a) + 1) from not_le.mp h2) hhi.le
      rw [← heq]
      exact hhi.le

/-- `⌊log₃ 2^n⌋`, the number of positive powers of `3` below `2^n`. -/
def log3TwoPow (n : ℕ) : ℕ :=
  Nat.log 3 (2 ^ n)

theorem log3TwoPow_succ (n : ℕ) :
    log3TwoPow (n + 1) = log3TwoPow n + (if 3 ∣ blockBase n then 1 else 0) := by
  have h := log_eq_of_mem_block (p := 3) (a := n) (x := 2 ^ (n + 1)) (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (by omega)) le_rfl
  unfold log3TwoPow
  rw [h]
  by_cases c : firstPow 3 n ≤ 2 ^ (n + 1)
  · rw [if_pos c, if_pos ((three_dvd_blockBase_iff n).mpr c)]
  · rw [if_neg c, if_neg (fun h' => c ((three_dvd_blockBase_iff n).mp h')), add_zero]

theorem log3TwoPow_bounds (n : ℕ) :
    3 ^ log3TwoPow n ≤ 2 ^ n ∧ 2 ^ n < 3 ^ (log3TwoPow n + 1) :=
  ⟨Nat.pow_log_le_self 3 (by positivity), Nat.lt_pow_succ_log_self (by norm_num) _⟩

/-- A geometric ratio above one is unbounded. -/
theorem pow_unbounded {x y A B : ℝ} (hy : 0 < y) (hxy : y < x) (hA : 0 < A)
    (h : ∀ k : ℕ, A * x ^ k ≤ B * y ^ k) : False := by
  have hr : 1 < x / y := (one_lt_div hy).mpr hxy
  obtain ⟨k, hk⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop (B / A)).exists
  have hyk : 0 < y ^ k := pow_pos hy k
  have h1 := h k
  rw [div_pow, div_lt_div_iff₀ hA hyk] at hk
  linarith

/-- **The blocks containing a power of `3` are not eventually periodic**: a period
`d` would give `⌊log₃ 2^(a + k d)⌋ = ⌊log₃ 2^a⌋ + k c` for all `k`, forcing
`2^d = 3^c`. -/
theorem blockBase_not_eventually_periodic :
    ∀ a d, 0 < d → ∃ j, blockBase (a + d + j) ≠ blockBase (a + j) := by
  intro a d hd
  by_contra hcon
  push Not at hcon
  have hinv : ∀ j, log3TwoPow (a + d + j) + log3TwoPow a =
      log3TwoPow (a + j) + log3TwoPow (a + d) := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.add_zero]
      omega
    | succ j ih =>
      have e1 := log3TwoPow_succ (a + d + j)
      have e2 := log3TwoPow_succ (a + j)
      rw [hcon j] at e1
      rw [show a + d + (j + 1) = a + d + j + 1 by omega,
        show a + (j + 1) = a + j + 1 by omega, e1, e2]
      linarith
  obtain ⟨C, hC⟩ : ∃ C, log3TwoPow (a + d) = log3TwoPow a + C := by
    have : log3TwoPow a ≤ log3TwoPow (a + d) :=
      Nat.log_mono_right (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact ⟨log3TwoPow (a + d) - log3TwoPow a, by omega⟩
  have hlin : ∀ k, log3TwoPow (a + k * d) = log3TwoPow a + k * C := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hinv (k * d)
      rw [ih, hC] at h
      rw [show a + (k + 1) * d = a + d + k * d by ring, add_mul, one_mul]
      linarith
  have hbound : ∀ k, 3 ^ (log3TwoPow a + k * C) ≤ 2 ^ (a + k * d) ∧
      2 ^ (a + k * d) < 3 ^ (log3TwoPow a + k * C + 1) := by
    intro k
    rw [← hlin k]
    exact log3TwoPow_bounds (a + k * d)
  have hpar : 2 ^ d ≠ 3 ^ C := by
    intro h
    have h2 : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
    rw [h] at h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega
  rcases lt_or_gt_of_ne hpar with hlt | hgt
  · refine pow_unbounded (x := (3 : ℝ) ^ C) (y := (2 : ℝ) ^ d)
      (A := (3 : ℝ) ^ log3TwoPow a) (B := (2 : ℝ) ^ a) (by positivity)
      (by exact_mod_cast hlt) (by positivity) (fun k => ?_)
    have h := (hbound k).1
    have e1 : (3 : ℕ) ^ (log3TwoPow a + k * C) = 3 ^ log3TwoPow a * (3 ^ C) ^ k := by ring
    have e2 : (2 : ℕ) ^ (a + k * d) = 2 ^ a * (2 ^ d) ^ k := by ring
    rw [e1, e2] at h
    exact_mod_cast h
  · refine pow_unbounded (x := (2 : ℝ) ^ d) (y := (3 : ℝ) ^ C) (A := (2 : ℝ) ^ a)
      (B := 3 * (3 : ℝ) ^ log3TwoPow a) (by positivity) (by exact_mod_cast hgt)
      (by positivity) (fun k => ?_)
    have h := (hbound k).2
    have e1 : (3 : ℕ) ^ (log3TwoPow a + k * C + 1) = 3 * 3 ^ log3TwoPow a * (3 ^ C) ^ k := by
      ring
    have e2 : (2 : ℕ) ^ (a + k * d) = 2 ^ a * (2 ^ d) ^ k := by ring
    rw [e1, e2] at h
    exact_mod_cast h.le

/-! ## Distinct values of the running height -/

theorem runningHeight235_lt_of_logs {s t : ℕ} (h2 : Nat.log 2 s ≤ Nat.log 2 t)
    (h3 : Nat.log 3 s ≤ Nat.log 3 t) (h5 : Nat.log 5 s ≤ Nat.log 5 t)
    (hne : Nat.log 2 s < Nat.log 2 t ∨ Nat.log 3 s < Nat.log 3 t ∨
      Nat.log 5 s < Nat.log 5 t) :
    runningHeight235 s < runningHeight235 t := by
  unfold runningHeight235
  have a2 : 2 ^ Nat.log 2 s ≤ 2 ^ Nat.log 2 t := Nat.pow_le_pow_right (by norm_num) h2
  have a3 : 3 ^ Nat.log 3 s ≤ 3 ^ Nat.log 3 t := Nat.pow_le_pow_right (by norm_num) h3
  have a5 : 5 ^ Nat.log 5 s ≤ 5 ^ Nat.log 5 t := Nat.pow_le_pow_right (by norm_num) h5
  have q2 : 0 < 2 ^ Nat.log 2 t := by positivity
  have q3 : 0 < 3 ^ Nat.log 3 t := by positivity
  have q5 : 0 < 5 ^ Nat.log 5 t := by positivity
  rcases hne with h | h | h
  · exact Nat.mul_lt_mul_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) h) a3 q3) a5 q5
  · exact Nat.mul_lt_mul_of_lt_of_le
      (Nat.mul_lt_mul_of_le_of_lt a2 (Nat.pow_lt_pow_right (by norm_num) h) q2) a5 q5
  · exact Nat.mul_lt_mul_of_le_of_lt (Nat.mul_le_mul a2 a3)
      (Nat.pow_lt_pow_right (by norm_num) h) (Nat.mul_pos q2 q3)

/-- The running height strictly increases at every jump point. -/
theorem runningHeight235_lt_of_lt_of_mem {s t : ℕ} (hs : s ≠ 0) (hst : s < t)
    (ht : t ∈ jumpPoints235) : runningHeight235 s < runningHeight235 t := by
  refine runningHeight235_lt_of_logs (Nat.log_mono_right hst.le) (Nat.log_mono_right hst.le)
    (Nat.log_mono_right hst.le) ?_
  obtain ⟨n, -, h | h | h⟩ := mem_jumpPoints235.mp ht <;> subst h
  · left
    rw [Nat.log_pow (by norm_num : 1 < 2)]
    exact Nat.log_lt_of_lt_pow hs hst
  · right; left
    rw [Nat.log_pow (by norm_num : 1 < 3)]
    exact Nat.log_lt_of_lt_pow hs hst
  · right; right
    rw [Nat.log_pow (by norm_num : 1 < 5)]
    exact Nat.log_lt_of_lt_pow hs hst

theorem runningHeight235_injOn : Set.InjOn runningHeight235 jumpPoints235 := by
  intro s hs t ht hst
  by_contra hne
  have hs0 : s ≠ 0 := fun h => zero_not_mem_jumpPoints235 (by subst h; exact hs)
  have ht0 : t ≠ 0 := fun h => zero_not_mem_jumpPoints235 (by subst h; exact ht)
  rcases lt_or_gt_of_ne hne with h | h
  · exact (runningHeight235_lt_of_lt_of_mem hs0 h ht).ne hst
  · exact (runningHeight235_lt_of_lt_of_mem ht0 h hs).ne hst.symm

theorem one_not_mem_image_jumpPoints235 : (1 : ℕ) ∉ runningHeight235 '' jumpPoints235 := by
  rintro ⟨t, ht, h1⟩
  have ht0 : t ≠ 0 := fun h => zero_not_mem_jumpPoints235 (by subst h; exact ht)
  have ht1 : t ≠ 1 := fun h => one_not_mem_jumpPoints235 (by subst h; exact ht)
  have := runningHeight235_lt_of_lt_of_mem one_ne_zero (by omega : 1 < t) ht
  rw [runningHeight235_one, h1] at this
  exact lt_irrefl 1 this

/-- Every value of the running height is `1` or a value at a jump point. -/
theorem runningHeight235_eq_one_or_jump (t : ℕ) :
    runningHeight235 t = 1 ∨ ∃ s ∈ jumpPoints235, runningHeight235 s = runningHeight235 t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact Or.inl runningHeight235_zero
  have ht0 : t ≠ 0 := ht.ne'
  obtain ⟨m, hm⟩ : ∃ m, m = max (max (2 ^ Nat.log 2 t) (3 ^ Nat.log 3 t)) (5 ^ Nat.log 5 t) :=
    ⟨_, rfl⟩
  have h2 : 2 ^ Nat.log 2 t ≤ m := by
    rw [hm]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have h3 : 3 ^ Nat.log 3 t ≤ m := by
    rw [hm]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h5 : 5 ^ Nat.log 5 t ≤ m := by
    rw [hm]; exact le_max_right _ _
  have hmt : m ≤ t := by
    rw [hm]
    exact max_le (max_le (Nat.pow_log_le_self 2 ht0) (Nat.pow_log_le_self 3 ht0))
      (Nat.pow_log_le_self 5 ht0)
  have hlog : ∀ p, 1 < p → p ^ Nat.log p t ≤ m → Nat.log p m = Nat.log p t :=
    fun p hp hpm => le_antisymm (Nat.log_mono_right hmt) (Nat.le_log_of_pow_le hp hpm)
  have hH : runningHeight235 m = runningHeight235 t := by
    unfold runningHeight235
    rw [hlog 2 (by norm_num) h2, hlog 3 (by norm_num) h3, hlog 5 (by norm_num) h5]
  have hjump : ∀ p e, m = p ^ e → (p = 2 ∨ p = 3 ∨ p = 5) →
      runningHeight235 t = 1 ∨ ∃ s ∈ jumpPoints235, runningHeight235 s = runningHeight235 t := by
    intro p e hme hp
    rcases Nat.eq_zero_or_pos e with he | he
    · left
      rw [← hH, hme, he, pow_zero, runningHeight235_one]
    · right
      refine ⟨m, mem_jumpPoints235.mpr ⟨e, by omega, ?_⟩, hH⟩
      rcases hp with rfl | rfl | rfl
      · exact Or.inl hme
      · exact Or.inr (Or.inl hme)
      · exact Or.inr (Or.inr hme)
  rcases max_choice (max (2 ^ Nat.log 2 t) (3 ^ Nat.log 3 t)) (5 ^ Nat.log 5 t) with h | h
  · rcases max_choice (2 ^ Nat.log 2 t) (3 ^ Nat.log 3 t) with h' | h'
    · exact hjump 2 (Nat.log 2 t) (by rw [hm, h, h']) (Or.inl rfl)
    · exact hjump 3 (Nat.log 3 t) (by rw [hm, h, h']) (Or.inr (Or.inl rfl))
  · exact hjump 5 (Nat.log 5 t) (by rw [hm, h]) (Or.inr (Or.inr rfl))

/-- The distinct values of the running height are `1` and its values at the jump
points. -/
theorem range_runningHeight235 :
    Set.range runningHeight235 = insert 1 (runningHeight235 '' jumpPoints235) := by
  ext h
  constructor
  · rintro ⟨t, rfl⟩
    rcases runningHeight235_eq_one_or_jump t with h1 | ⟨s, hs, hst⟩
    · exact Set.mem_insert_iff.mpr (Or.inl h1)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨s, hs, hst⟩)
  · intro hh
    rcases Set.mem_insert_iff.mp hh with rfl | ⟨s, -, rfl⟩
    · exact Set.mem_range.mpr ⟨1, runningHeight235_one⟩
    · exact Set.mem_range_self s

end DistinctHeight235

/-- The series over the jump points converges, so `distinctHeightSum235` is the value
of a convergent series. -/
theorem summable_distinctHeight235 :
    Summable (fun t : jumpPoints235 => (1 : ℝ) / (runningHeight235 t : ℝ)) :=
  ((hasSum_subtype_iff_indicator (s := jumpPoints235) (f := recipHeight)).mpr
    hasSum_jumpTerm).summable

/-- The distinct-height sum as the block series of
`ErdosProblems.Erdos269.DistinctHeightBlockRadix`. -/
theorem distinctHeightSum235_eq_one_add_tsum_blockTerm :
    distinctHeightSum235 = 1 + ∑' a, blockTerm blockBase blockNum a := by
  rw [distinctHeightSum235]
  congr 1
  exact ((hasSum_subtype_iff_indicator (s := jumpPoints235) (f := recipHeight)).mpr
    hasSum_jumpTerm).tsum_eq

/-- **Erdős #269, distinct-height sum for `{2,3,5}`.**  The number
`𝒟_{2,3,5} = 1 + ∑_{t ∈ {2^n, 3^n, 5^n : n ≥ 1}} 1 / H(t)`, with
`H(t) = 2^⌊log₂ t⌋ 3^⌊log₃ t⌋ 5^⌊log₅ t⌋` the running least common multiple of the
`{2,3,5}`-smooth integers up to `t`, is irrational. -/
theorem distinctHeightSum235_irrational : Irrational distinctHeightSum235 := by
  rw [distinctHeightSum235_eq_one_add_tsum_blockTerm]
  have h := (irrational_tsum_blockTerm blockLetter_blockBase_blockNum five_spacing
    blockBase_not_eventually_periodic).natCast_add 1
  rwa [Nat.cast_one] at h

/-- The distinct-height sum is the sum of `1 / h` over the distinct values `h` of the
running height `H`.  The range is taken over all `t : ℕ`; since `H 0 = H 1 = 1`, it is
the set of values of the running LCM at the positive integers. -/
theorem distinctHeightSum235_eq_tsum_range :
    distinctHeightSum235 = ∑' h : Set.range runningHeight235, (1 : ℝ) / ((h : ℕ) : ℝ) := by
  have hJ : HasSum (recipHeight ∘ ((↑) : jumpPoints235 → ℕ))
      (∑' a, blockTerm blockBase blockNum a) :=
    (hasSum_subtype_iff_indicator (s := jumpPoints235) (f := recipHeight)).mpr hasSum_jumpTerm
  have hImg : HasSum (fun h : ↥(runningHeight235 '' jumpPoints235) => (1 : ℝ) / ((h : ℕ) : ℝ))
      (∑' a, blockTerm blockBase blockNum a) :=
    (Equiv.Set.imageOfInjOn runningHeight235 jumpPoints235 runningHeight235_injOn).hasSum_iff.mp
      hJ
  have hOne : HasSum ((fun n : ℕ => (1 : ℝ) / (n : ℝ)) ∘ ((↑) : ({1} : Set ℕ) → ℕ)) 1 := by
    have h := hasSum_singleton (1 : ℕ) (fun n : ℕ => (1 : ℝ) / (n : ℝ))
    simp only [Nat.cast_one, div_one] at h
    exact h
  have hU := hOne.add_disjoint
    (Set.disjoint_singleton_left.mpr one_not_mem_image_jumpPoints235) hImg
  rw [← Set.insert_eq, ← range_runningHeight235] at hU
  rw [distinctHeightSum235_eq_one_add_tsum_blockTerm]
  exact hU.tsum_eq.symm

/-- **The distinct-height sum over the distinct values.**  The sum of `1 / h` over
the distinct values `h` of `H(t) = 2^⌊log₂ t⌋ 3^⌊log₃ t⌋ 5^⌊log₅ t⌋` is irrational. -/
theorem irrational_tsum_range_runningHeight235 :
    Irrational (∑' h : Set.range runningHeight235, (1 : ℝ) / ((h : ℕ) : ℝ)) := by
  rw [← distinctHeightSum235_eq_tsum_range]
  exact distinctHeightSum235_irrational

end ErdosProblems.Erdos269
