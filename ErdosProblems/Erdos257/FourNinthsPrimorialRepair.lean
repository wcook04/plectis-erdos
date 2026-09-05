import ErdosProblems.Erdos257.FourNinthsCofinalRepairConsumer
import Erdos249257.SupportDilationDifferences
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Bitwise

/-!
# Erdős #257: the causal seven-column producer for `4/9`

This module turns the surviving modulus-`120` computation into an exact Lean
interface.  The causal load is the union of selected divisors visible at the
three earlier ranks `n/2`, `n/3`, and `n/5`.  Inclusion-exclusion gives the
seven-column formula without natural-number subtraction, and the union embeds
in the full divisor load at `n`.

The all-depth seven-column inequality is deliberately retained as a named
hypothesis.  Proving it would give actual repairs at every positive multiple
of `120`, hence the infinite rational `4/9` counterexample packaged by
`FourNinthsCofinalRepairConsumer`.
-/

namespace ErdosProblems.Erdos257

open Set
open Erdos249257
open Erdos249257.SupportDilationDifferences

set_option maxRecDepth 10000

/-- Selected divisors of a rank, as a finite set. -/
private noncomputable def fourNinthsSelectedDivisors
    (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  letI := Classical.decPred fun d : ℕ ↦ d ∈ A
  n.divisors.filter fun d ↦ d ∈ A

private theorem fourNinthsSelectedDivisors_card (A : Set ℕ) (n : ℕ) :
    (fourNinthsSelectedDivisors A n).card = supportCoeff A n := by
  classical
  unfold fourNinthsSelectedDivisors
  exact (supportCoeff_eq_card_filter A n).symm

private theorem mem_fourNinthsPrefixRat_iff_real_support
    {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) n ↔
      d ∈ greedyMersenneSupport (4 / 9 : ℝ) := by
  classical
  unfold greedyMersennePrefixRat
  constructor
  · intro hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨-, htake⟩ := Finset.mem_filter.mp hj
    have htakeR := (rational_greedy_take_iff_real (4 / 9 : ℚ) j).1 htake
    norm_num at htakeR
    exact (succ_mem_greedyMersenneSupport_iff (4 / 9 : ℝ) j).2 htakeR
  · intro hd
    refine Finset.mem_image.mpr ⟨d - 1, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    apply (rational_greedy_take_iff_real (4 / 9 : ℚ) (d - 1)).2
    have htakeR :=
      (succ_mem_greedyMersenneSupport_iff (4 / 9 : ℝ) (d - 1)).1
        (by simpa only [Nat.sub_add_cancel hd1] using hd)
    norm_num at htakeR ⊢
    exact htakeR

/-- Linear evaluator used by the large exact finite certificates below. -/
private def fourNinthsGreedyStateRat (x : ℚ) : ℕ → ℚ × Finset ℕ
  | 0 => (x, ∅)
  | n + 1 =>
      let previous := fourNinthsGreedyStateRat x n
      if mersenneWeightRat (n + 1) ≤ previous.1 then
        (previous.1 - mersenneWeightRat (n + 1), insert (n + 1) previous.2)
      else
        previous

/-- Tail-recursive evaluator for large finite certificates. -/
private def fourNinthsGreedyStateRatFrom :
    ℕ → (ℚ × Finset ℕ) → ℕ → ℚ × Finset ℕ
  | _, state, 0 => state
  | n, state, k + 1 =>
      let rank := n + 1
      let next :=
        if mersenneWeightRat rank ≤ state.1 then
          (state.1 - mersenneWeightRat rank, insert rank state.2)
        else
          state
      fourNinthsGreedyStateRatFrom rank next k

private theorem fourNinthsGreedyStateRatFrom_eq
    (x : ℚ) (n k : ℕ) :
    fourNinthsGreedyStateRatFrom n (fourNinthsGreedyStateRat x n) k =
      fourNinthsGreedyStateRat x (n + k) := by
  induction k generalizing n with
  | zero => simp [fourNinthsGreedyStateRatFrom]
  | succ k ih =>
      rw [fourNinthsGreedyStateRatFrom]
      change
        fourNinthsGreedyStateRatFrom (n + 1)
            (fourNinthsGreedyStateRat x (n + 1)) k =
          fourNinthsGreedyStateRat x (n + (k + 1))
      rw [ih]
      congr 1
      omega

/-- Sixty-four-rank blocks keep kernel reduction shallow while preserving the
same greedy state. -/
private def fourNinthsGreedyStateRatChunks (x : ℚ) :
    ℕ → ℚ × Finset ℕ
  | 0 => (x, ∅)
  | k + 1 =>
      fourNinthsGreedyStateRatFrom (64 * k)
        (fourNinthsGreedyStateRatChunks x k) 64

private theorem fourNinthsGreedyStateRatChunks_eq (x : ℚ) (k : ℕ) :
    fourNinthsGreedyStateRatChunks x k =
      fourNinthsGreedyStateRat x (64 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [fourNinthsGreedyStateRatChunks, ih,
        fourNinthsGreedyStateRatFrom_eq]
      congr 1

/-- Array-backed greedy state used by large finite kernel certificates.  The
Boolean at index `d - 1` records whether rank `d` was selected. -/
private def fourNinthsGreedyArrayStateRat (x : ℚ) :
    ℕ → ℚ × Array Bool
  | 0 => (x, #[])
  | n + 1 =>
      let previous := fourNinthsGreedyArrayStateRat x n
      if mersenneWeightRat (n + 1) ≤ previous.1 then
        (previous.1 - mersenneWeightRat (n + 1), previous.2.push true)
      else
        (previous.1, previous.2.push false)

private theorem fourNinthsGreedyArrayStateRat_spec (x : ℚ) (n : ℕ) :
    (fourNinthsGreedyArrayStateRat x n).1 =
        (fourNinthsGreedyStateRat x n).1 ∧
      (fourNinthsGreedyArrayStateRat x n).2.size = n ∧
      ∀ d, 1 ≤ d →
        (d ∈ (fourNinthsGreedyStateRat x n).2 ↔
          (fourNinthsGreedyArrayStateRat x n).2[d - 1]? = some true) := by
  induction n with
  | zero =>
      simp [fourNinthsGreedyArrayStateRat, fourNinthsGreedyStateRat]
  | succ n ih =>
      rw [fourNinthsGreedyArrayStateRat, fourNinthsGreedyStateRat, ih.1]
      split_ifs with h
      · refine ⟨rfl, ?_, ?_⟩
        · simp [ih.2.1]
        · intro d hd
          rw [Finset.mem_insert, Array.getElem?_push, ih.2.1]
          by_cases hdnew : d = n + 1
          · subst d
            simp
          · have hindex : d - 1 ≠ n := by omega
            simp [hindex, hdnew, (ih.2.2 d hd)]
      · refine ⟨rfl, ?_, ?_⟩
        · simp [ih.2.1]
        · intro d hd
          rw [Array.getElem?_push, ih.2.1]
          by_cases hdnew : d = n + 1
          · subst d
            rw [ih.2.2 (n + 1) (by omega)]
            simp [ih.2.1]
          · have hindex : d - 1 ≠ n := by omega
            simp [hindex, (ih.2.2 d hd)]

private def fourNinthsGreedyArrayStateRatFrom :
    ℕ → (ℚ × Array Bool) → ℕ → ℚ × Array Bool
  | _, state, 0 => state
  | n, state, k + 1 =>
      let rank := n + 1
      let next :=
        if mersenneWeightRat rank ≤ state.1 then
          (state.1 - mersenneWeightRat rank, state.2.push true)
        else
          (state.1, state.2.push false)
      fourNinthsGreedyArrayStateRatFrom rank next k

private theorem fourNinthsGreedyArrayStateRatFrom_eq
    (x : ℚ) (n k : ℕ) :
    fourNinthsGreedyArrayStateRatFrom n
        (fourNinthsGreedyArrayStateRat x n) k =
      fourNinthsGreedyArrayStateRat x (n + k) := by
  induction k generalizing n with
  | zero => simp [fourNinthsGreedyArrayStateRatFrom]
  | succ k ih =>
      rw [fourNinthsGreedyArrayStateRatFrom]
      change
        fourNinthsGreedyArrayStateRatFrom (n + 1)
            (fourNinthsGreedyArrayStateRat x (n + 1)) k =
          fourNinthsGreedyArrayStateRat x (n + (k + 1))
      rw [ih]
      congr 1
      omega

private def fourNinthsGreedyArrayStateRatChunks (x : ℚ) :
    ℕ → ℚ × Array Bool
  | 0 => (x, #[])
  | k + 1 =>
      fourNinthsGreedyArrayStateRatFrom (64 * k)
        (fourNinthsGreedyArrayStateRatChunks x k) 64

private theorem fourNinthsGreedyArrayStateRatChunks_eq
    (x : ℚ) (k : ℕ) :
    fourNinthsGreedyArrayStateRatChunks x k =
      fourNinthsGreedyArrayStateRat x (64 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [fourNinthsGreedyArrayStateRatChunks, ih,
        fourNinthsGreedyArrayStateRatFrom_eq]
      congr 1

/-- Tail-recursive numerator continuation from a checked prefix. -/
private def binaryCoeffPrefixNumeratorFrom (c : ℕ → ℕ) :
    ℕ → ℕ → ℕ → ℕ
  | _, value, 0 => value
  | n, value, k + 1 =>
      binaryCoeffPrefixNumeratorFrom c (n + 1)
        (2 * value + c (n + 1)) k

private theorem binaryCoeffPrefixNumeratorFrom_eq
    (c : ℕ → ℕ) (n k : ℕ) :
    binaryCoeffPrefixNumeratorFrom c n
        (binaryCoeffPrefixNumerator c n) k =
      binaryCoeffPrefixNumerator c (n + k) := by
  induction k generalizing n with
  | zero => simp [binaryCoeffPrefixNumeratorFrom]
  | succ k ih =>
      rw [binaryCoeffPrefixNumeratorFrom]
      change
        binaryCoeffPrefixNumeratorFrom c (n + 1)
            (binaryCoeffPrefixNumerator c (n + 1)) k =
          binaryCoeffPrefixNumerator c (n + (k + 1))
      rw [ih]
      congr 1
      omega

/-- Sixty-four-rank blocks for the dyadic numerator computation. -/
private def binaryCoeffPrefixNumeratorChunks (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      binaryCoeffPrefixNumeratorFrom c (64 * k)
        (binaryCoeffPrefixNumeratorChunks c k) 64

private theorem binaryCoeffPrefixNumeratorChunks_eq
    (c : ℕ → ℕ) (k : ℕ) :
    binaryCoeffPrefixNumeratorChunks c k =
      binaryCoeffPrefixNumerator c (64 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [binaryCoeffPrefixNumeratorChunks, ih,
        binaryCoeffPrefixNumeratorFrom_eq]
      congr 1

private def binaryCoeffPrefixNumeratorChunked
    (c : ℕ → ℕ) (N : ℕ) : ℕ :=
  binaryCoeffPrefixNumeratorFrom c (64 * (N / 64))
    (binaryCoeffPrefixNumeratorChunks c (N / 64)) (N % 64)

private theorem binaryCoeffPrefixNumeratorChunked_eq
    (c : ℕ → ℕ) (N : ℕ) :
    binaryCoeffPrefixNumeratorChunked c N =
      binaryCoeffPrefixNumerator c N := by
  rw [binaryCoeffPrefixNumeratorChunked,
    binaryCoeffPrefixNumeratorChunks_eq,
    binaryCoeffPrefixNumeratorFrom_eq]
  congr 1
  omega

/-- Six-periodic kernel evaluator for the binary floor digit of `4/9`. -/
private def fourNinthsFloorBitFast (n : ℕ) : ℤ :=
  if n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 then 1 else 0

private theorem fourNinthsFloorBit_eq_fast (n : ℕ) :
    fourNinthsFloorBit n = fourNinthsFloorBitFast n := by
  let q := n / 6
  let r := n % 6
  have hr : r < 6 := by
    dsimp [r]
    exact Nat.mod_lt _ (by norm_num)
  have hn : n = 6 * q + r := by
    dsimp [q, r]
    omega
  have hbase : 2 ^ 6 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
  have hpow : (2 ^ 6) ^ q ≡ 1 ^ q [MOD 9] := hbase.pow q
  have hprod : (2 ^ 6) ^ q * 2 ^ r ≡ 1 ^ q * 2 ^ r [MOD 9] :=
    hpow.mul (Nat.ModEq.refl (2 ^ r))
  have hmodPow : 2 ^ n % 9 = 2 ^ r % 9 := by
    change 2 ^ n ≡ 2 ^ r [MOD 9]
    rw [hn, pow_add, pow_mul]
    simpa using hprod
  have hmod : (4 * 2 ^ n) % 9 = (4 * 2 ^ r) % 9 := by
    exact Nat.ModEq.mul_left 4 (by simpa [Nat.ModEq] using hmodPow)
  rw [fourNinthsFloorBit_eq_two_mul_mod_div, hmod]
  change
    (((2 * ((4 * 2 ^ r) % 9) / 9 : ℕ) : ℤ)) =
      (if r = 1 ∨ r = 2 ∨ r = 3 then 1 else 0)
  interval_cases r <;> norm_num

private def fourNinthsDefectRecFast (c : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      2 * fourNinthsDefectRecFast c n + fourNinthsFloorBitFast n -
        (c (n + 1) : ℤ)

private def fourNinthsDefectRecFrom (c : ℕ → ℕ) :
    ℕ → ℤ → ℕ → ℤ
  | _, value, 0 => value
  | n, value, k + 1 =>
      fourNinthsDefectRecFrom c (n + 1)
        (2 * value + fourNinthsFloorBitFast n - (c (n + 1) : ℤ)) k

private theorem fourNinthsDefectRecFrom_eq
    (c : ℕ → ℕ) (n k : ℕ) :
    fourNinthsDefectRecFrom c n (fourNinthsDefectRecFast c n) k =
      fourNinthsDefectRecFast c (n + k) := by
  induction k generalizing n with
  | zero => simp [fourNinthsDefectRecFrom]
  | succ k ih =>
      rw [fourNinthsDefectRecFrom]
      change
        fourNinthsDefectRecFrom c (n + 1)
            (fourNinthsDefectRecFast c (n + 1)) k =
          fourNinthsDefectRecFast c (n + (k + 1))
      rw [ih]
      congr 1
      omega

private def fourNinthsDefectRecChunks (c : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 =>
      fourNinthsDefectRecFrom c (64 * k)
        (fourNinthsDefectRecChunks c k) 64

private theorem fourNinthsDefectRecChunks_eq
    (c : ℕ → ℕ) (k : ℕ) :
    fourNinthsDefectRecChunks c k =
      fourNinthsDefectRecFast c (64 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [fourNinthsDefectRecChunks, ih, fourNinthsDefectRecFrom_eq]
      congr 1

private def fourNinthsDefectRecChunked (c : ℕ → ℕ) (N : ℕ) : ℤ :=
  fourNinthsDefectRecFrom c (64 * (N / 64))
    (fourNinthsDefectRecChunks c (N / 64)) (N % 64)

private theorem fourNinthsDefectRecChunked_eq
    (c : ℕ → ℕ) (N : ℕ) :
    fourNinthsDefectRecChunked c N = fourNinthsDefectRecFast c N := by
  rw [fourNinthsDefectRecChunked, fourNinthsDefectRecChunks_eq,
    fourNinthsDefectRecFrom_eq]
  congr 1
  omega

private theorem nat_le_of_int_cast_le {a b : ℕ}
    (h : (a : ℤ) ≤ (b : ℤ)) : a ≤ b := by
  exact_mod_cast h

@[simp] private theorem fourNinthsGreedyStateRat_fst (x : ℚ) (n : ℕ) :
    (fourNinthsGreedyStateRat x n).1 = greedyMersenneRemainderRat x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [fourNinthsGreedyStateRat, greedyMersenneRemainderRat]
      rw [ih]
      split <;> simp_all

private theorem fourNinthsGreedyPrefixRat_succ (x : ℚ) (n : ℕ) :
    greedyMersennePrefixRat x (n + 1) =
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        insert (n + 1) (greedyMersennePrefixRat x n)
      else
        greedyMersennePrefixRat x n := by
  classical
  unfold greedyMersennePrefixRat
  rw [Finset.range_add_one, Finset.filter_insert]
  split <;> simp_all

@[simp] private theorem fourNinthsGreedyStateRat_snd (x : ℚ) (n : ℕ) :
    (fourNinthsGreedyStateRat x n).2 = greedyMersennePrefixRat x n := by
  classical
  induction n with
  | zero => simp [fourNinthsGreedyStateRat, greedyMersennePrefixRat]
  | succ n ih =>
      rw [fourNinthsGreedyPrefixRat_succ]
      simp only [fourNinthsGreedyStateRat, fourNinthsGreedyStateRat_fst]
      split <;> simp_all

private theorem fourNinthsSupportCoeff_eq_prefix
    (F : Finset ℕ) (limit n : ℕ)
    (hF : F = greedyMersennePrefixRat (4 / 9 : ℚ) limit)
    (hn : 0 < n) (hnLimit : n ≤ limit) :
    supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n =
      (n.divisors.filter fun d => d ∈ F).card := by
  unfold supportCoeff
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hddiv, hdA⟩
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    have hdLimit : d ≤ limit := (Nat.le_of_dvd hn hdvd).trans hnLimit
    exact ⟨hddiv, by
      simpa only [hF] using
        (mem_fourNinthsPrefixRat_iff_real_support hdpos hdLimit).2 hdA⟩
  · rintro ⟨hddiv, hdF⟩
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    have hdLimit : d ≤ limit := (Nat.le_of_dvd hn hdvd).trans hnLimit
    have hdPrefix : d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) limit := by
      simpa only [hF] using hdF
    exact ⟨hddiv,
      (mem_fourNinthsPrefixRat_iff_real_support hdpos hdLimit).1 hdPrefix⟩

private theorem fourNinthsSelectedDivisors_eq_prefix
    (F : Finset ℕ) (limit n : ℕ)
    (hF : F = greedyMersennePrefixRat (4 / 9 : ℚ) limit)
    (hn : 0 < n) (hnLimit : n ≤ limit) :
    fourNinthsSelectedDivisors (greedyMersenneSupport (4 / 9 : ℝ)) n =
      fourNinthsSelectedDivisors (↑F : Set ℕ) n := by
  ext d
  unfold fourNinthsSelectedDivisors
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hddiv, hdA⟩
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    have hdLimit : d ≤ limit := (Nat.le_of_dvd hn hdvd).trans hnLimit
    exact ⟨hddiv, by
      simpa only [Finset.mem_coe, hF] using
        (mem_fourNinthsPrefixRat_iff_real_support hdpos hdLimit).2 hdA⟩
  · rintro ⟨hddiv, hdF⟩
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    have hdLimit : d ≤ limit := (Nat.le_of_dvd hn hdvd).trans hnLimit
    have hdPrefix : d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) limit := by
      simpa only [Finset.mem_coe, hF] using hdF
    exact ⟨hddiv,
      (mem_fourNinthsPrefixRat_iff_real_support hdpos hdLimit).1 hdPrefix⟩

private structure FourNinthsCertificateState where
  remainder : ℚ
  bits : Array Bool
  defect : ℤ

/-- A single forward pass computes the rational greedy support and the defect.
This avoids rebuilding a large finite support inside every coefficient query. -/
private def fourNinthsCertificateStateRat (x : ℚ) :
    ℕ → FourNinthsCertificateState
  | 0 => ⟨x, #[], 0⟩
  | n + 1 =>
      let previous := fourNinthsCertificateStateRat x n
      let take := mersenneWeightRat (n + 1) ≤ previous.remainder
      let remainder :=
        if take then previous.remainder - mersenneWeightRat (n + 1)
        else previous.remainder
      let bits := previous.bits.push (decide take)
      let coeff :=
        ((n + 1).divisors.filter fun d => bits[d - 1]? = some true).card
      ⟨remainder, bits,
        2 * previous.defect + fourNinthsFloorBitFast n - (coeff : ℤ)⟩

private theorem fourNinthsCertificateStateRat_agrees_array
    (x : ℚ) (n : ℕ) :
    (fourNinthsCertificateStateRat x n).remainder =
        (fourNinthsGreedyArrayStateRat x n).1 ∧
      (fourNinthsCertificateStateRat x n).bits =
        (fourNinthsGreedyArrayStateRat x n).2 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      simp only [fourNinthsCertificateStateRat,
        fourNinthsGreedyArrayStateRat]
      rw [ih.1, ih.2]
      by_cases h : mersenneWeightRat (n + 1) ≤
          (fourNinthsGreedyArrayStateRat x n).1
      · simp [h]
      · simp [h]

private theorem fourNinthsSupportCoeff_eq_arrayState (n : ℕ)
    (hn : 0 < n) :
    supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n =
      (n.divisors.filter fun d =>
        (fourNinthsGreedyArrayStateRat (4 / 9 : ℚ) n).2[d - 1]? =
          some true).card := by
  rw [show supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n =
      (n.divisors.filter fun d =>
        d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) n).card by
    exact fourNinthsSupportCoeff_eq_prefix
      (greedyMersennePrefixRat (4 / 9 : ℚ) n) n n rfl hn le_rfl]
  apply congrArg Finset.card
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hddiv, hdPrefix⟩
    have hdpos : 1 ≤ d :=
      Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hddiv) hn
    exact ⟨hddiv, (by
      rw [← fourNinthsGreedyStateRat_snd] at hdPrefix
      exact (fourNinthsGreedyArrayStateRat_spec
        (4 / 9 : ℚ) n).2.2 d hdpos |>.1 hdPrefix)⟩
  · rintro ⟨hddiv, hdBit⟩
    have hdpos : 1 ≤ d :=
      Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hddiv) hn
    exact ⟨hddiv, by
      rw [← fourNinthsGreedyStateRat_snd]
      exact (fourNinthsGreedyArrayStateRat_spec
        (4 / 9 : ℚ) n).2.2 d hdpos |>.2 hdBit⟩

private theorem fourNinthsCertificateStateRat_defect (n : ℕ) :
    (fourNinthsCertificateStateRat (4 / 9 : ℚ) n).defect =
      (fourNinthsGreedyDefect n : ℤ) := by
  induction n with
  | zero =>
      simp [fourNinthsCertificateStateRat, fourNinthsGreedyDefect,
        fourNinthsBinaryFloor, binaryCoeffPrefixNumerator]
  | succ n ih =>
      have hcoeff := fourNinthsSupportCoeff_eq_arrayState (n + 1) (by omega)
      rw [← (fourNinthsCertificateStateRat_agrees_array
        (4 / 9 : ℚ) (n + 1)).2] at hcoeff
      rw [fourNinthsGreedyDefect_succ, ← ih,
        fourNinthsFloorBit_eq_fast, hcoeff]
      rfl

private def fourNinthsCertificateStateRatFrom :
    ℕ → FourNinthsCertificateState → ℕ → FourNinthsCertificateState
  | _, state, 0 => state
  | n, state, k + 1 =>
      let rank := n + 1
      let take := mersenneWeightRat rank ≤ state.remainder
      let remainder :=
        if take then state.remainder - mersenneWeightRat rank
        else state.remainder
      let bits := state.bits.push (decide take)
      let coeff :=
        (rank.divisors.filter fun d => bits[d - 1]? = some true).card
      let next := ⟨remainder, bits,
        2 * state.defect + fourNinthsFloorBitFast n - (coeff : ℤ)⟩
      fourNinthsCertificateStateRatFrom rank next k

private theorem fourNinthsCertificateStateRatFrom_eq
    (x : ℚ) (n k : ℕ) :
    fourNinthsCertificateStateRatFrom n
        (fourNinthsCertificateStateRat x n) k =
      fourNinthsCertificateStateRat x (n + k) := by
  induction k generalizing n with
  | zero => simp [fourNinthsCertificateStateRatFrom]
  | succ k ih =>
      rw [fourNinthsCertificateStateRatFrom]
      change
        fourNinthsCertificateStateRatFrom (n + 1)
            (fourNinthsCertificateStateRat x (n + 1)) k =
          fourNinthsCertificateStateRat x (n + (k + 1))
      rw [ih]
      congr 1
      omega

private def fourNinthsCertificateStateRatChunks (x : ℚ) :
    ℕ → FourNinthsCertificateState
  | 0 => ⟨x, #[], 0⟩
  | k + 1 =>
      fourNinthsCertificateStateRatFrom (64 * k)
        (fourNinthsCertificateStateRatChunks x k) 64

private theorem fourNinthsCertificateStateRatChunks_eq
    (x : ℚ) (k : ℕ) :
    fourNinthsCertificateStateRatChunks x k =
      fourNinthsCertificateStateRat x (64 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [fourNinthsCertificateStateRatChunks, ih,
        fourNinthsCertificateStateRatFrom_eq]
      congr 1

private def fourNinthsCertificateStateRatChunked
    (x : ℚ) (N : ℕ) : FourNinthsCertificateState :=
  fourNinthsCertificateStateRatFrom (64 * (N / 64))
    (fourNinthsCertificateStateRatChunks x (N / 64)) (N % 64)

private theorem fourNinthsCertificateStateRatChunked_eq
    (x : ℚ) (N : ℕ) :
    fourNinthsCertificateStateRatChunked x N =
      fourNinthsCertificateStateRat x N := by
  rw [fourNinthsCertificateStateRatChunked,
    fourNinthsCertificateStateRatChunks_eq,
    fourNinthsCertificateStateRatFrom_eq]
  congr 1
  omega

private def fourNinthsFixedScale : ℕ := 2 ^ 3000

private def fourNinthsFixedDen (n : ℕ) : ℕ := 2 ^ n - 1

private def fourNinthsFixedWeightLo (n : ℕ) : ℕ :=
  fourNinthsFixedScale / fourNinthsFixedDen n

private def fourNinthsFixedWeightHi (n : ℕ) : ℕ :=
  fourNinthsFixedScale ⌈/⌉ fourNinthsFixedDen n

private theorem scaledFloor_div_le (a s d : ℕ) (hs : 0 < s) (hd : 0 < d) :
    (((a * s / d : ℕ) : ℚ) / s) ≤ a / d := by
  have hm : a * s / d * d ≤ a * s := Nat.div_mul_le_self _ _
  rw [div_le_div_iff₀ (by exact_mod_cast hs) (by exact_mod_cast hd)]
  exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using hm)

private theorem le_scaledCeil_div (a s d : ℕ) (hs : 0 < s) (hd : 0 < d) :
    (a : ℚ) / d ≤ (((a * s ⌈/⌉ d : ℕ) : ℚ) / s) := by
  have hm : a * s ≤ d * (a * s ⌈/⌉ d) :=
    (ceilDiv_le_iff_le_mul hd).1 le_rfl
  rw [div_le_div_iff₀ (by exact_mod_cast hd) (by exact_mod_cast hs)]
  exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using hm)

private theorem fourNinthsFixedWeight_enclosure (n : ℕ) (hn : 0 < n) :
    ((fourNinthsFixedWeightLo n : ℕ) : ℚ) / fourNinthsFixedScale ≤
        mersenneWeightRat n ∧
      mersenneWeightRat n ≤
        ((fourNinthsFixedWeightHi n : ℕ) : ℚ) / fourNinthsFixedScale := by
  have hscale : 0 < fourNinthsFixedScale := by
    unfold fourNinthsFixedScale
    exact pow_pos (by norm_num) _
  have hden : 0 < fourNinthsFixedDen n := by
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn.ne')
  have hcastDen : ((fourNinthsFixedDen n : ℕ) : ℚ) = 2 ^ n - 1 := by
    simp [fourNinthsFixedDen]
  constructor
  · rw [mersenneWeightRat, ← hcastDen]
    exact scaledFloor_div_le 1 fourNinthsFixedScale
      (fourNinthsFixedDen n) hscale hden
  · rw [mersenneWeightRat, ← hcastDen]
    exact le_scaledCeil_div 1 fourNinthsFixedScale
      (fourNinthsFixedDen n) hscale hden

private structure FourNinthsFixedState where
  lo : ℕ
  hi : ℕ
  bits : ℕ
  defect : ℤ
deriving DecidableEq
private def fourNinthsFixedInitial : FourNinthsFixedState :=
  ⟨4 * fourNinthsFixedScale / 9,
    4 * fourNinthsFixedScale ⌈/⌉ 9, 0, 0⟩

private def fourNinthsFixedStep
    (n : ℕ) (previous : FourNinthsFixedState) : Option FourNinthsFixedState :=
  let rank := n + 1
  let wLo := fourNinthsFixedWeightLo rank
  let wHi := fourNinthsFixedWeightHi rank
  if wHi ≤ previous.lo then
    let bits := previous.bits ||| 2 ^ n
    let coeff :=
      (rank.divisors.filter fun d => bits.testBit (d - 1)).card
    some ⟨previous.lo - wHi, previous.hi - wLo, bits,
      2 * previous.defect + fourNinthsFloorBitFast n - (coeff : ℤ)⟩
  else if previous.hi < wLo then
    let coeff :=
      (rank.divisors.filter fun d => previous.bits.testBit (d - 1)).card
    some ⟨previous.lo, previous.hi, previous.bits,
      2 * previous.defect + fourNinthsFloorBitFast n - (coeff : ℤ)⟩
  else none

private def fourNinthsFixedAdvance :
    ℕ → FourNinthsFixedState → ℕ → Option FourNinthsFixedState
  | _, state, 0 => some state
  | n, state, k + 1 =>
      (fourNinthsFixedStep n state).bind fun next =>
        fourNinthsFixedAdvance (n + 1) next k

private def FourNinthsFixedState.Sound
    (n : ℕ) (state : FourNinthsFixedState) : Prop :=
  state.lo ≤ state.hi ∧
    (((state.lo : ℕ) : ℚ) / fourNinthsFixedScale ≤
      (fourNinthsCertificateStateRat (4 / 9 : ℚ) n).remainder) ∧
    ((fourNinthsCertificateStateRat (4 / 9 : ℚ) n).remainder ≤
      ((state.hi : ℕ) : ℚ) / fourNinthsFixedScale) ∧
    state.bits < 2 ^ n ∧
    (∀ d, 1 ≤ d → d ≤ n →
      (fourNinthsCertificateStateRat (4 / 9 : ℚ) n).bits[d - 1]? =
        some (state.bits.testBit (d - 1))) ∧
    state.defect =
      (fourNinthsCertificateStateRat (4 / 9 : ℚ) n).defect

private theorem fourNinthsFixedInitial_sound :
    fourNinthsFixedInitial.Sound 0 := by
  have hscale : 0 < fourNinthsFixedScale := by
    unfold fourNinthsFixedScale
    exact pow_pos (by norm_num) _
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
  · dsimp [fourNinthsFixedInitial]
    rw [← Nat.floorDiv_eq_div]
    exact floorDiv_le_ceilDiv
  · simpa [fourNinthsFixedInitial, fourNinthsCertificateStateRat] using
      (scaledFloor_div_le 4 fourNinthsFixedScale 9 hscale (by norm_num))
  · simpa [fourNinthsFixedInitial, fourNinthsCertificateStateRat] using
      (le_scaledCeil_div 4 fourNinthsFixedScale 9 hscale (by norm_num))
  · simp [fourNinthsFixedInitial]
  · intro d hd hd0
    omega

private theorem fourNinthsFixedStep_sound
    {n : ℕ} {state next : FourNinthsFixedState}
    (hsound : state.Sound n)
    (hstep : fourNinthsFixedStep n state = some next) :
    next.Sound (n + 1) := by
  obtain ⟨hlohi, hlo, hhi, hbound, hbits, hdefect⟩ := hsound
  have hscale : 0 < fourNinthsFixedScale := by
    unfold fourNinthsFixedScale
    exact pow_pos (by norm_num) _
  have hw := fourNinthsFixedWeight_enclosure (n + 1) (by omega)
  have hsize :
      (fourNinthsCertificateStateRat (4 / 9 : ℚ) n).bits.size = n := by
    rw [(fourNinthsCertificateStateRat_agrees_array
      (4 / 9 : ℚ) n).2]
    exact (fourNinthsGreedyArrayStateRat_spec (4 / 9 : ℚ) n).2.1
  by_cases htake : fourNinthsFixedWeightHi (n + 1) ≤ state.lo
  · simp only [fourNinthsFixedStep, htake, if_true] at hstep
    injection hstep with hnext
    subst next
    let newBits := state.bits ||| 2 ^ n
    have hexactTake : mersenneWeightRat (n + 1) ≤
        (fourNinthsCertificateStateRat (4 / 9 : ℚ) n).remainder := by
      have hcast :
          ((fourNinthsFixedWeightHi (n + 1) : ℕ) : ℚ) /
              fourNinthsFixedScale ≤
            ((state.lo : ℕ) : ℚ) / fourNinthsFixedScale := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast htake) (by positivity)
      exact hw.2.trans (hcast.trans hlo)
    have hdecideTake : decide (mersenneWeightRat (n + 1) ≤
        (fourNinthsCertificateStateRat (4 / 9 : ℚ) n).remainder) = true := by
      simp [hexactTake]
    have hwlohi : fourNinthsFixedWeightLo (n + 1) ≤
        fourNinthsFixedWeightHi (n + 1) := by
      unfold fourNinthsFixedWeightLo fourNinthsFixedWeightHi
      rw [← Nat.floorDiv_eq_div]
      exact floorDiv_le_ceilDiv
    have hwlole : fourNinthsFixedWeightLo (n + 1) ≤ state.hi :=
      hwlohi.trans (htake.trans hlohi)
    have hloCast :
        (((state.lo - fourNinthsFixedWeightHi (n + 1) : ℕ) : ℚ)) =
          (state.lo : ℚ) - (fourNinthsFixedWeightHi (n + 1) : ℚ) := by
      rw [Nat.cast_sub htake]
    have hhiCast :
        (((state.hi - fourNinthsFixedWeightLo (n + 1) : ℕ) : ℚ)) =
          (state.hi : ℚ) - (fourNinthsFixedWeightLo (n + 1) : ℚ) := by
      rw [Nat.cast_sub hwlole]
    have hnewBound : newBits < 2 ^ (n + 1) := by
      apply Nat.bitwise_lt_two_pow
      · exact hbound.trans (Nat.pow_lt_pow_right (a := 2) (m := n)
          (n := n + 1) (by decide) (by omega))
      · exact Nat.pow_lt_pow_right (a := 2) (m := n)
          (n := n + 1) (by decide) (by omega)
    have hnewBits (d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n + 1) :
        (fourNinthsCertificateStateRat (4 / 9 : ℚ) (n + 1)).bits[d - 1]? =
          some (newBits.testBit (d - 1)) := by
      by_cases hdnew : d = n + 1
      · subst d
        rw [fourNinthsCertificateStateRat, if_pos hexactTake, hdecideTake,
          Array.getElem?_push, hsize]
        simp [newBits, Nat.testBit_two_pow]
      · have hdold : d ≤ n := by omega
        have hnidx : n ≠ d - 1 := by omega
        rw [fourNinthsCertificateStateRat, if_pos hexactTake, hdecideTake,
          Array.getElem?_push, hsize, if_neg (by omega)]
        simpa [newBits, Nat.testBit_two_pow, hnidx] using hbits d hd hdold
    have hcoeff :
        ((n + 1).divisors.filter fun d =>
          (fourNinthsCertificateStateRat
            (4 / 9 : ℚ) (n + 1)).bits[d - 1]? = some true).card =
        ((n + 1).divisors.filter fun d => newBits.testBit (d - 1)).card := by
      apply congrArg Finset.card
      ext d
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hddiv, hdtrue⟩
        have hdpos : 1 ≤ d :=
          Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hddiv) (by omega)
        have hdle : d ≤ n + 1 := Nat.le_of_dvd (by omega)
          (Nat.dvd_of_mem_divisors hddiv)
        exact ⟨hddiv, by
          have := hnewBits d hdpos hdle
          simpa [hdtrue] using this.symm⟩
      · rintro ⟨hddiv, hdtrue⟩
        have hdpos : 1 ≤ d :=
          Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hddiv) (by omega)
        have hdle : d ≤ n + 1 := Nat.le_of_dvd (by omega)
          (Nat.dvd_of_mem_divisors hddiv)
        exact ⟨hddiv, by
          have := hnewBits d hdpos hdle
          simpa [hdtrue] using this⟩
    refine ⟨(show state.lo - fourNinthsFixedWeightHi (n + 1) ≤
        state.hi - fourNinthsFixedWeightLo (n + 1) by omega),
      (show (((state.lo - fourNinthsFixedWeightHi (n + 1) : ℕ) : ℚ) /
          fourNinthsFixedScale) ≤
        (fourNinthsCertificateStateRat (4 / 9 : ℚ) (n + 1)).remainder from ?_),
      (show (fourNinthsCertificateStateRat
          (4 / 9 : ℚ) (n + 1)).remainder ≤
        (((state.hi - fourNinthsFixedWeightLo (n + 1) : ℕ) : ℚ) /
          fourNinthsFixedScale) from ?_), hnewBound, hnewBits, ?_⟩
    · rw [fourNinthsCertificateStateRat, if_pos hexactTake, hloCast]
      rw [sub_div]
      nlinarith
    · rw [fourNinthsCertificateStateRat, if_pos hexactTake, hhiCast]
      rw [sub_div]
      nlinarith
    · change 2 * state.defect + fourNinthsFloorBitFast n -
          (((n + 1).divisors.filter fun d => newBits.testBit (d - 1)).card : ℤ) = _
      rw [hdefect, ← hcoeff, fourNinthsCertificateStateRat,
        if_pos hexactTake, hdecideTake]
  · simp only [fourNinthsFixedStep, htake, if_false] at hstep
    by_cases hskip : state.hi < fourNinthsFixedWeightLo (n + 1)
    · simp only [hskip, if_true] at hstep
      injection hstep with hnext
      subst next
      have hexactSkip : ¬mersenneWeightRat (n + 1) ≤
          (fourNinthsCertificateStateRat (4 / 9 : ℚ) n).remainder := by
        have hcast :
            ((state.hi : ℕ) : ℚ) / fourNinthsFixedScale <
              ((fourNinthsFixedWeightLo (n + 1) : ℕ) : ℚ) /
                fourNinthsFixedScale := by
          exact div_lt_div_of_pos_right (by exact_mod_cast hskip) (by positivity)
        exact not_le_of_gt (hhi.trans_lt (hcast.trans_le hw.1))
      have hdecideSkip : decide (mersenneWeightRat (n + 1) ≤
          (fourNinthsCertificateStateRat (4 / 9 : ℚ) n).remainder) = false := by
        simp [hexactSkip]
      have hnewBound : state.bits < 2 ^ (n + 1) :=
        hbound.trans (Nat.pow_lt_pow_right (a := 2) (m := n)
          (n := n + 1) (by decide) (by omega))
      have hnewBits (d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n + 1) :
          (fourNinthsCertificateStateRat (4 / 9 : ℚ) (n + 1)).bits[d - 1]? =
            some (state.bits.testBit (d - 1)) := by
        by_cases hdnew : d = n + 1
        · subst d
          have hzero := Nat.testBit_eq_false_of_lt hbound
          rw [fourNinthsCertificateStateRat, if_neg hexactSkip, hdecideSkip,
            Array.getElem?_push, hsize]
          simp [hzero]
        · have hdold : d ≤ n := by omega
          rw [fourNinthsCertificateStateRat, if_neg hexactSkip, hdecideSkip,
            Array.getElem?_push, hsize, if_neg (by omega)]
          exact hbits d hd hdold
      have hcoeff :
          ((n + 1).divisors.filter fun d =>
            (fourNinthsCertificateStateRat
              (4 / 9 : ℚ) (n + 1)).bits[d - 1]? = some true).card =
          ((n + 1).divisors.filter fun d => state.bits.testBit (d - 1)).card := by
        apply congrArg Finset.card
        ext d
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hddiv, hdtrue⟩
          have hdpos : 1 ≤ d :=
            Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hddiv) (by omega)
          have hdle : d ≤ n + 1 := Nat.le_of_dvd (by omega)
            (Nat.dvd_of_mem_divisors hddiv)
          exact ⟨hddiv, by
            have := hnewBits d hdpos hdle
            simpa [hdtrue] using this.symm⟩
        · rintro ⟨hddiv, hdtrue⟩
          have hdpos : 1 ≤ d :=
            Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hddiv) (by omega)
          have hdle : d ≤ n + 1 := Nat.le_of_dvd (by omega)
            (Nat.dvd_of_mem_divisors hddiv)
          exact ⟨hddiv, by
            have := hnewBits d hdpos hdle
            simpa [hdtrue] using this⟩
      refine ⟨hlohi, ?_, ?_, hnewBound, hnewBits, ?_⟩
      · simpa [fourNinthsCertificateStateRat, hexactSkip] using hlo
      · simpa [fourNinthsCertificateStateRat, hexactSkip] using hhi
      · change 2 * state.defect + fourNinthsFloorBitFast n -
            (((n + 1).divisors.filter fun d => state.bits.testBit (d - 1)).card : ℤ) = _
        rw [hdefect, ← hcoeff, fourNinthsCertificateStateRat,
          if_neg hexactSkip, hdecideSkip]
    · simp only [hskip, if_false] at hstep
      cases hstep

set_option maxHeartbeats 1000000 in
private theorem fourNinthsFixedAdvance_sound
    {n k : ℕ} {state next : FourNinthsFixedState}
    (hsound : state.Sound n)
    (hadvance : fourNinthsFixedAdvance n state k = some next) :
    next.Sound (n + k) := by
  induction k generalizing n state next with
  | zero =>
      simp only [fourNinthsFixedAdvance, Option.some.injEq] at hadvance
      subst next
      simpa using hsound
  | succ k ih =>
      simp only [fourNinthsFixedAdvance] at hadvance
      cases hstep : fourNinthsFixedStep n state with
      | none => simp [hstep] at hadvance
      | some middle =>
          rw [hstep] at hadvance
          convert ih (fourNinthsFixedStep_sound hsound hstep) hadvance using 1 <;>
            omega

private theorem fourNinthsFixedSound_cast
    {m n : ℕ} {state : FourNinthsFixedState}
    (hmn : m = n) (hsound : state.Sound m) : state.Sound n := by
  subst n
  exact hsound

/-- Kernel-checked fixed-point checkpoints through the largest small-prime boundary.
Each closed reduction spans at most 32 ranks, bounding elaborator memory. -/
private def fourNinthsFixedCheckpoint0000 : FourNinthsFixedState :=
  fourNinthsFixedInitial

private theorem fourNinthsFixedCheckpoint0000_sound :
    fourNinthsFixedCheckpoint0000.Sound 0 :=
  fourNinthsFixedInitial_sound

private def fourNinthsFixedCheckpoint0032 : FourNinthsFixedState :=
  ⟨0xcb25121992da8edfa3b863f8c22f415b670515f5a812af56c346d7d2623a9ba33f55cda68eac974277cfe850f8287db9ee849ec42c90b35e1dc00f1aa8971fec6d62c119a11a07bfdb7e721c7546da8ab5416040aa2e7e678668ab7f87022c5d32ce897884f6a9403fcc0a241325d6f60da5408cb57271e8ea86b209be9e269b27848877cd6f2126669af6098f855de4b35edf69ecff08a4bfa58646421cd1b7ef98c8ec7b1f92a5aeab26020c60456e98894c70234182dd9a60c2dba16a0e5b018519768a340caa5c3b6fa74ac1dfc86460f51fc216189f14ef9c480db684c1414b23bcf718c8177025bd8269cbb13beb878ed5fea242aae4367e5ed890dbe5a68eee7d953c16bc436781ab0ddea19823fb8c54b2a7d58a43bf077778e42806ce22661d9f98a90658024e70f9788613a8debf0e895ffcbebf414d8ba0401a08dc960843896aede471a8692286071e7e246e65c5faf83d63310a9abf0b0546039cd2c65edd2bb1de190dbfa30ca232eb61b958, 0xcb25121992da8edfa3b863f8c22f415b670515f5a812af56c346d7d2623a9ba33f55cda68eac974277cfe850f8287db9ee849ec42c90b35e1dc00f1aa8971fec6d62c119a11a07bfdb7e721c7546da8ab5416040aa2e7e678668ab7f87022c5d32ce897884f6a9403fcc0a241325d6f60da5408cb57271e8ea86b209be9e269b27848877cd6f2126669af6098f855de4b35edf69ecff08a4bfa58646421cd1b7ef98c8ec7b1f92a5aeab26020c60456e98894c70234182dd9a60c2dba16a0e5b018519768a340caa5c3b6fa74ac1dfc86460f51fc216189f14ef9c480db684c1414b23bcf718c8177025bd8269cbb13beb878ed5fea242aae4367e5ed890dbe5a68eee7d953c16bc436781ab0ddea19823fb8c54b2a7d58a43bf077778e42806ce22661d9f98a90658024e70f9788613a8debf0e895ffcbebf414d8ba0401a08dc960843896aede471a8692286071e7e246e65c5faf83d63310a9abf0b0546039cd2c65edd2bb1de190dbfa30ca232eb61b969, 0x2cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0032_transition :
    fourNinthsFixedAdvance 0 fourNinthsFixedCheckpoint0000 32 =
      some fourNinthsFixedCheckpoint0032 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0032_sound :
    fourNinthsFixedCheckpoint0032.Sound 32 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0000_sound
      fourNinthsFixedCheckpoint0032_transition)

private def fourNinthsFixedCheckpoint0064 : FourNinthsFixedState :=
  ⟨0x42958ace7eb259b730ee313a56b502738301ad42bcffc7d0f138eaa23dbd0ba44e238640759aa44e54177ab4de4f9c732c7c92ca9cbc0eb592951fdb203f41076098c1778b7b4a1a5946a847a3401839a9cb79366e58a87d424a2adc32c7e86682f644af3f89e9028124b0de09a4ff80716f7188e7859de6bd841e8ce783e6752d1d1d20e67ae4e33c051de39f3bcea8cbff075fbb150643bcc9c1b7eb90ace6799d8a228e69e4bd0c1ff16b5878436e20f081cd0a4f3a999157ca3b0182d54e89e37c981738eea48aaebfc84bd0c31dbde6007cf26d98468b7278b03cb921fbe70dc6914024bb3e41b97116ea067d24f69d3e99db163b59d88eb661a64ede02843c04b67f6441a8c9de0f95c3d98c32929fd18a33be035d6fdee7e69ba1650b9e48a7034e7dfe6ff2e66583a89b6f06814fdabe3cb839096036f883da93fffa6965edb47057e80c63edd63c242d053fa7f7ab6220e980adf7043d010bb2a45a54eb70dcf7c3bf110c9c106a61ac41, 0x42958ace7eb259b730ee313a56b502738301ad42bcffc7d0f138eaa23dbd0ba44e238640759aa44e54177ab4de4f9c732c7c92ca9cbc0eb592951fdb203f41076098c1778b7b4a1a5946a847a3401839a9cb79366e58a87d424a2adc32c7e86682f644af3f89e9028124b0de09a4ff80716f7188e7859de6bd841e8ce783e6752d1d1d20e67ae4e33c051de39f3bcea8cbff075fbb150643bcc9c1b7eb90ace6799d8a228e69e4bd0c1ff16b5878436e20f081cd0a4f3a999157ca3b0182d54e89e37c981738eea48aaebfc84bd0c31dbde6007cf26d98468b7278b03cb921fbe70dc6914024bb3e41b97116ea067d24f69d3e99db163b59d88eb661a64ede02843c04b67f6441a8c9de0f95c3d98c32929fd18a33be035d6fdee7e69ba1650b9e48a7034e7dfe6ff2e66583a89b6f06814fdabe3cb839096036f883da93fffa6965edb47057e80c63edd63c242d053fa7f7ab6220e980adf7043d010bb2a45a54eb70dcf7c3bf110c9c106a61ac5f, 0x9848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0064_transition :
    fourNinthsFixedAdvance 32 fourNinthsFixedCheckpoint0032 32 =
      some fourNinthsFixedCheckpoint0064 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0064_sound :
    fourNinthsFixedCheckpoint0064.Sound 64 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0032_sound
      fourNinthsFixedCheckpoint0064_transition)

private def fourNinthsFixedCheckpoint0096 : FourNinthsFixedState :=
  ⟨0x7eb259b720e9f0291670b21f7f01a522acbea7cee814e84a2dbc0aa33de376304492932e500672b4dd8f786aeb77fea998bb8eaf92540bcae03a2dc75f9861760b7846175825d7c7a2301735a4c974766d57a675423029da9247e8666af1f22f3b78e8a27123b0adc694f377715f5170a78599d0bd430683e5f3e5751b1c9d0fa555c4e334039de38b3acc2587fee6dab705061ebcb8bd379a8c6ae66d9b89220e08c4accc0e71694067f36e1eaf61cc09c83a117157c8f70179d53945df5c979338a6a4896bbf9832c8a31dbdd5ef7bf06b7f864a6a78ae9cb81cfbd500c590ffc4bab541b9701246065804e67bbe99da863a3fc86ea260a50edd817c32c3967f6201a6883a0f0583d90b31825ec77931be015d6b9ddfe5798d550b9b38a7022df97e66e2966583249a26f5812bd99e3c7834d8582eef82da837ffa3843eda45053680c6295963a1fec053f45f7176118e8779de70417fdcbb2a2582fab6fdaa6c3be908c96efe75dabab, 0x7eb259b720e9f0291670b21f7f01a522acbea7cee814e84a2dbc0aa33de376304492932e500672b4dd8f786aeb77fea998bb8eaf92540bcae03a2dc75f9861760b7846175825d7c7a2301735a4c974766d57a675423029da9247e8666af1f22f3b78e8a27123b0adc694f377715f5170a78599d0bd430683e5f3e5751b1c9d0fa555c4e334039de38b3acc2587fee6dab705061ebcb8bd379a8c6ae66d9b89220e08c4accc0e71694067f36e1eaf61cc09c83a117157c8f70179d53945df5c979338a6a4896bbf9832c8a31dbdd5ef7bf06b7f864a6a78ae9cb81cfbd500c590ffc4bab541b9701246065804e67bbe99da863a3fc86ea260a50edd817c32c3967f6201a6883a0f0583d90b31825ec77931be015d6b9ddfe5798d550b9b38a7022df97e66e2966583249a26f5812bd99e3c7834d8582eef82da837ffa3843eda45053680c6295963a1fec053f45f7176118e8779de70417fdcbb2a2582fab6fdaa6c3be908c96efe75dabd7, 0x7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0096_transition :
    fourNinthsFixedAdvance 64 fourNinthsFixedCheckpoint0064 32 =
      some fourNinthsFixedCheckpoint0096 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0096_sound :
    fourNinthsFixedCheckpoint0096.Sound 96 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0064_sound
      fourNinthsFixedCheckpoint0096_transition)

private def fourNinthsFixedCheckpoint0128 : FourNinthsFixedState :=
  ⟨0x20e9f0291670b21f69ad601e9b7d62b9e814e84a2929c282addb721e437202e54ef561a4cd7e785aea76eea888687d1a724c09bae01a2d874f081f69f9283df61725d787a21c0e218487f0742c4f863441af28d59136c76668eff1262b786701611aacaac5947376504f406ba48458bf7942f63be5efdf741b0c76ff6549b2e213035c636b38cbd57efad5dab2e501cda8b7ad3719883ac66d1b70120d85bb8bc80e6167e057f3660e66617bf7a7a9d070d787f5f778d5263dce4b968b3786a2c9699f9422c39adcb8c5ed5bd06a3b05486a764d9c9814f6c0ffc50e7fb43ab13db7ef123d0547f3de56be98ca84b83ea79ea25ea3eebd297bb2c37e7f4ddda5083a0ded7fc30a31705ac71927ba012c679cbfc4e94c050b1938a6802def6d65d25524eb237916f5711bd6963c601f575724ed81d9737ff57842e5944b22c40b4275563a1cab043f04f6f55218a7759ce6ebf7bd7ab2a0571b2b0eda963b3e6f8b92dfa65d8b7d, 0x20e9f0291670b21f69ad601e9b7d62b9e814e84a2929c282addb721e437202e54ef561a4cd7e785aea76eea888687d1a724c09bae01a2d874f081f69f9283df61725d787a21c0e218487f0742c4f863441af28d59136c76668eff1262b786701611aacaac5947376504f406ba48458bf7942f63be5efdf741b0c76ff6549b2e213035c636b38cbd57efad5dab2e501cda8b7ad3719883ac66d1b70120d85bb8bc80e6167e057f3660e66617bf7a7a9d070d787f5f778d5263dce4b968b3786a2c9699f9422c39adcb8c5ed5bd06a3b05486a764d9c9814f6c0ffc50e7fb43ab13db7ef123d0547f3de56be98ca84b83ea79ea25ea3eebd297bb2c37e7f4ddda5083a0ded7fc30a31705ac71927ba012c679cbfc4e94c050b1938a6802def6d65d25524eb237916f5711bd6963c601f575724ed81d9737ff57842e5944b22c40b4275563a1cab043f04f6f55218a7759ce6ebf7bd7ab2a0571b2b0eda963b3e6f8b92dfa65d8bbd, 0xed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0128_transition :
    fourNinthsFixedAdvance 96 fourNinthsFixedCheckpoint0096 32 =
      some fourNinthsFixedCheckpoint0128 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0128_sound :
    fourNinthsFixedCheckpoint0128.Sound 128 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0096_sound
      fourNinthsFixedCheckpoint0128_transition)

private def fourNinthsFixedCheckpoint0160 : FourNinthsFixedState :=
  ⟨0x1670b21f69ad601e9b7d62b9e4149408d429be41addb721e437202e54e7561804b7d53caea766ca788687d1a723c09bacf0a1d863df71f69f9182df51723d787a213cc210486e8321c4f86343fae68d49136c35628ebf12527682601611aa4aa859073734c47404ba48356bb7132f53be5efdf6c19eb75fe6449b2e112025b426b38cbd57efa549a91e4f9cca8b6acb2d9682ac66d1b6fd1fd819b8b800e61656017e3620d66617bd7a3a95070d187f5a777d50539cdcb868b2785a2b9699f8420439ad9b8b5ec5ac06933050868764d9bd814f6b0fec4f67f7438ac2da7eed23cfd43f3de56be95ca80b7aea55e9d5d9bedbd295bb2c37e7f4cdd63083509e47fb1ea307059c71927ba012b679bb743e90ae0ea1938a6772def6d65d25424ea6377c6754d1ac6963c201f565724ed80d9533fe1682261944a1ac20b427556391ca9f43ce3f6f1421427758cd6abf7bd7ab2a04cdb2abeda933b3e5f0b915fa65b8b70, 0x1670b21f69ad601e9b7d62b9e4149408d429be41addb721e437202e54e7561804b7d53caea766ca788687d1a723c09bacf0a1d863df71f69f9182df51723d787a213cc210486e8321c4f86343fae68d49136c35628ebf12527682601611aa4aa859073734c47404ba48356bb7132f53be5efdf6c19eb75fe6449b2e112025b426b38cbd57efa549a91e4f9cca8b6acb2d9682ac66d1b6fd1fd819b8b800e61656017e3620d66617bd7a3a95070d187f5a777d50539cdcb868b2785a2b9699f8420439ad9b8b5ec5ac06933050868764d9bd814f6b0fec4f67f7438ac2da7eed23cfd43f3de56be95ca80b7aea55e9d5d9bedbd295bb2c37e7f4cdd63083509e47fb1ea307059c71927ba012b679bb743e90ae0ea1938a6772def6d65d25424ea6377c6754d1ac6963c201f565724ed80d9533fe1682261944a1ac20b427556391ca9f43ce3f6f1421427758cd6abf7bd7ab2a04cdb2abeda933b3e5f0b915fa65b8bbd, 0x940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0160_transition :
    fourNinthsFixedAdvance 128 fourNinthsFixedCheckpoint0128 32 =
      some fourNinthsFixedCheckpoint0160 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0160_sound :
    fourNinthsFixedCheckpoint0160.Sound 160 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0128_sound
      fourNinthsFixedCheckpoint0160_transition)

private def fourNinthsFixedCheckpoint0192 : FourNinthsFixedState :=
  ⟨0x69ad601e9b7d62b9e4149408d429be41acc75d1dfe6e01904e7561804b7d53caea766ca788583515e23be92ac70a0b3d3df71f69f9182df51722d677a102cc20f475e8221c4e75233fae68d49136b35208ebaf1527681dff511a84aa857fef524c473f4b944356ab3032f53be1ef9e6c19ab75fe6345a29011c1db426730bbd57efa529a89d4f9cc28b6acb1c946e9456d1a6ed0fd819b8b7f0e60646017e261fd665d78d6a2a80f50c187f5a777d48539adbb868a258592b5699f74083b97d8b8b5ec5ac02933010758764d57d014f6b0fac3762f6434ab2da7eeb23cfbc3e3dd56ae8dca80b6ae955d8d5b9badb5285ba2b37e6f47dd430834f9e43fafea207058c70926b9f022679ba543990ae0ea1908a6372cef6d65d244245a5f73a6344c5ac5963c201b560f24dd80d9533fe067225d913a198202426556381ca8f3bbe3f6f1420427758cc2aad5bd3ab1204adaeabeba932a3e5f0a915fa65b7b61, 0x69ad601e9b7d62b9e4149408d429be41acc75d1dfe6e01904e7561804b7d53caea766ca788583515e23be92ac70a0b3d3df71f69f9182df51722d677a102cc20f475e8221c4e75233fae68d49136b35208ebaf1527681dff511a84aa857fef524c473f4b944356ab3032f53be1ef9e6c19ab75fe6345a29011c1db426730bbd57efa529a89d4f9cc28b6acb1c946e9456d1a6ed0fd819b8b7f0e60646017e261fd665d78d6a2a80f50c187f5a777d48539adbb868a258592b5699f74083b97d8b8b5ec5ac02933010758764d57d014f6b0fac3762f6434ab2da7eeb23cfbc3e3dd56ae8dca80b6ae955d8d5b9badb5285ba2b37e6f47dd430834f9e43fafea207058c70926b9f022679ba543990ae0ea1908a6372cef6d65d244245a5f73a6344c5ac5963c201b560f24dd80d9533fe067225d913a198202426556381ca8f3bbe3f6f1420427758cc2aad5bd3ab1204adaeabeba932a3e5f0a915fa65b7bbd, 0xf84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0192_transition :
    fourNinthsFixedAdvance 160 fourNinthsFixedCheckpoint0160 32 =
      some fourNinthsFixedCheckpoint0192 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0192_sound :
    fourNinthsFixedCheckpoint0192.Sound 192 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0160_sound
      fourNinthsFixedCheckpoint0192_transition)

private def fourNinthsFixedCheckpoint0224 : FourNinthsFixedState :=
  ⟨0x9b7d62b9e4149408d429be41acc75d1dfe6e01903a341d2f377d5276ea766ca788583515e23be92ac70a0b3d39751e4976d729751722c42fa102cc20f475e8221c4e75233e9e58d38126a25107dbaf1527670cef511a84aa857fef524c053ecb933b54aaac31f4f9e1ef9e6c199af1de6345a29011b19b3e672fb7d53ef6429989c4b9cc28b6acb1c842d9056d1666d0dd819a897f0660442016e25df5665d78d6a2a80f40a04675a677d48438adba8689248591b5689e74083b97d8b8b5ac39bf2032010657f64d37d00cf2b0f9c375ef4434ab2da7deae3cfb83d3d551ac4dca7cb6ae554d8d5a9bada5245ba2af7def47db430834f7e3df9fe5a07056c6c926b8f022639b2443890ae0da1908a6362cdf5d63c2041c4a5e73a6334c5ac4562a201b558f24dd80d85337e0671f5d8138996e02426456281c28f1bbdff6f14204267588c2aad57d3aa11bcac6ea9eb593223e4f0a315fa65b7b51, 0x9b7d62b9e4149408d429be41acc75d1dfe6e01903a341d2f377d5276ea766ca788583515e23be92ac70a0b3d39751e4976d729751722c42fa102cc20f475e8221c4e75233e9e58d38126a25107dbaf1527670cef511a84aa857fef524c053ecb933b54aaac31f4f9e1ef9e6c199af1de6345a29011b19b3e672fb7d53ef6429989c4b9cc28b6acb1c842d9056d1666d0dd819a897f0660442016e25df5665d78d6a2a80f40a04675a677d48438adba8689248591b5689e74083b97d8b8b5ac39bf2032010657f64d37d00cf2b0f9c375ef4434ab2da7deae3cfb83d3d551ac4dca7cb6ae554d8d5a9bada5245ba2af7def47db430834f7e3df9fe5a07056c6c926b8f022639b2443890ae0da1908a6362cdf5d63c2041c4a5e73a6334c5ac4562a201b558f24dd80d85337e0671f5d8138996e02426456281c28f1bbdff6f14204267588c2aad57d3aa11bcac6ea9eb593223e4f0a315fa65b7bbc, 0x7806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0224_transition :
    fourNinthsFixedAdvance 192 fourNinthsFixedCheckpoint0192 32 =
      some fourNinthsFixedCheckpoint0224 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0224_sound :
    fourNinthsFixedCheckpoint0224.Sound 224 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0192_sound
      fourNinthsFixedCheckpoint0224_transition)

private def fourNinthsFixedCheckpoint0256 : FourNinthsFixedState :=
  ⟨0xe4149408d429be41acc75d1dfe6e01903a341d2f377d5276a93157567453efd4e23be92ac70a0b3d39751e4976d729751722c42f80f0c31c6234e3a2142de3223e9e58d38126a25107dbaf1527670cef41197499846ede514af53ebb832a44a9ac31f4f9e1ef9e6c199af1de5b45920ff0b1592de32eb7933ef6229187b439cb28b6acb1c842d905691665ccdd409a793e0250432006a25df5265978959ea80e40a04675a477d47418ad3986851c757175679e70003b97d838b3ac31af0032000557f64c36d00bf1b0f8c274ee4334aa2da6ddae3cfb82d3d451ab4cc8fcb6ad45458d589aada4e43b92a779ef46db42c814f7e3df9de59ff016a6b91db8b0215f9a24437906dfd9d8f8a6352cdf4d5fc2041c4a5a53a5f34c46c155ea181a548f20dd00c85137a0671e5d813498ee02425456201c27d1abdf76d13f04267487b2a9d56d39a11bc9c6ea9db5831a3e4f0a313fa5db6b3e, 0xe4149408d429be41acc75d1dfe6e01903a341d2f377d5276a93157567453efd4e23be92ac70a0b3d39751e4976d729751722c42f80f0c31c6234e3a2142de3223e9e58d38126a25107dbaf1527670cef41197499846ede514af53ebb832a44a9ac31f4f9e1ef9e6c199af1de5b45920ff0b1592de32eb7933ef6229187b439cb28b6acb1c842d905691665ccdd409a793e0250432006a25df5265978959ea80e40a04675a477d47418ad3986851c757175679e70003b97d838b3ac31af0032000557f64c36d00bf1b0f8c274ee4334aa2da6ddae3cfb82d3d451ab4cc8fcb6ad45458d589aada4e43b92a779ef46db42c814f7e3df9de59ff016a6b91db8b0215f9a24437906dfd9d8f8a6352cdf4d5fc2041c4a5a53a5f34c46c155ea181a548f20dd00c85137a0671e5d813498ee02425456201c27d1abdf76d13f04267487b2a9d56d39a11bc9c6ea9db5831a3e4f0a313fa5db6bbc, 0x9d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0256_transition :
    fourNinthsFixedAdvance 224 fourNinthsFixedCheckpoint0224 32 =
      some fourNinthsFixedCheckpoint0256 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0256_sound :
    fourNinthsFixedCheckpoint0256.Sound 256 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0224_sound
      fourNinthsFixedCheckpoint0256_transition)

private def fourNinthsFixedCheckpoint0288 : FourNinthsFixedState :=
  ⟨0xd429be41acc75d1dfe6e01903a341d2f377d5276a93157567453efd48e2be81a85fa0afd39751e4976d729751722c42f80f0c31c6234e3a2142de3221a1e18d370e68240c7dbad1527670cef41197499846ede514af53ebb832a44a99b21f3f9e1ee9d6c0999f0de5b45820ff0b1592de32eb7933ef6229187b439cb2074acadc842d8f565165dcccd3c9a793e01d0432006a25df5265978959ea80e3c9006759477d47417ad2986811c747165679e70003797d838b3ac31af0032000353ee4c36900bf1b0f8b274ae4332aa2d96dd6e3cfb82d3d431ab4cc8fcb6ad44448c589aaca4e43b92a778ef45db42c714f7e2df9ce59ff016a6b91cb8b0215f19e4237906dbd9d8f8a6352ccf4d5bc2041bca5a5395f34846c155ea181a5486e0ccfcc8513790671e5d813498ed02424456201be7d1abde76d12f04267487b289d16c79a11bc986ea9db5831a3e4efa313f65db6b34, 0xd429be41acc75d1dfe6e01903a341d2f377d5276a93157567453efd48e2be81a85fa0afd39751e4976d729751722c42f80f0c31c6234e3a2142de3221a1e18d370e68240c7dbad1527670cef41197499846ede514af53ebb832a44a99b21f3f9e1ee9d6c0999f0de5b45820ff0b1592de32eb7933ef6229187b439cb2074acadc842d8f565165dcccd3c9a793e01d0432006a25df5265978959ea80e3c9006759477d47417ad2986811c747165679e70003797d838b3ac31af0032000353ee4c36900bf1b0f8b274ae4332aa2d96dd6e3cfb82d3d431ab4cc8fcb6ad44448c589aaca4e43b92a778ef45db42c714f7e2df9ce59ff016a6b91cb8b0215f19e4237906dbd9d8f8a6352ccf4d5bc2041bca5a5395f34846c155ea181a5486e0ccfcc8513790671e5d813498ed02424456201be7d1abde76d12f04267487b289d16c79a11bc986ea9db5831a3e4efa313f65db6bbc, 0x102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0288_transition :
    fourNinthsFixedAdvance 256 fourNinthsFixedCheckpoint0256 32 =
      some fourNinthsFixedCheckpoint0288 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0288_sound :
    fourNinthsFixedCheckpoint0288.Sound 288 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0256_sound
      fourNinthsFixedCheckpoint0288_transition)

private def fourNinthsFixedCheckpoint0320 : FourNinthsFixedState :=
  ⟨0xacc75d1dfe6e01903a341d2f377d5276a93157567453efd48e2be81a85fa0afce8651a08318319741722c42f80f0c31c6234e3a2142de3221a1e18d370e68240c7dbad150356cceebf1854073c6ade504af53ebb832a44a99b21f3f9e1ee9d6c0999f0de5b45820fdfb0582de31ea7922ee5118186b439ca2074acadc842d8f565165dcccd3c9a793e01d04317c69259f5265778159da00c2c0be6755477d47317ad2986811c747165679e70003797d834a3ab319f0031ffc34fee4b328fcaeda0b8b264ae4332a92d96dd6e3cfb82d3d431ab4cc6f8b69d44048c589aa4a4c43b91a578e735bb024714f3e2df9ce59ef016a6b91cb8b0215e18e4227905dbd9d8f8a5352bcf4d5ac1041ac9595294f34845c155ea181a5386e0ccfcc7d0f790571e59813498ed0222444e201be6d12bde56c12700247487b249d16c79a11bc886aa8db5821a3e3efa313f65db6725, 0xacc75d1dfe6e01903a341d2f377d5276a93157567453efd48e2be81a85fa0afce8651a08318319741722c42f80f0c31c6234e3a2142de3221a1e18d370e68240c7dbad150356cceebf1854073c6ade504af53ebb832a44a99b21f3f9e1ee9d6c0999f0de5b45820fdfb0582de31ea7922ee5118186b439ca2074acadc842d8f565165dcccd3c9a793e01d04317c69259f5265778159da00c2c0be6755477d47317ad2986811c747165679e70003797d834a3ab319f0031ffc34fee4b328fcaeda0b8b264ae4332a92d96dd6e3cfb82d3d431ab4cc6f8b69d44048c589aa4a4c43b91a578e735bb024714f3e2df9ce59ef016a6b91cb8b0215e18e4227905dbd9d8f8a5352bcf4d5ac1041ac9595294f34845c155ea181a5386e0ccfcc7d0f790571e59813498ed0222444e201be6d12bde56c12700247487b249d16c79a11bc886aa8db5821a3e3efa313f65db67bc, 0x827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0320_transition :
    fourNinthsFixedAdvance 288 fourNinthsFixedCheckpoint0288 32 =
      some fourNinthsFixedCheckpoint0320 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0320_sound :
    fourNinthsFixedCheckpoint0320.Sound 320 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0288_sound
      fourNinthsFixedCheckpoint0320_transition)

private def fourNinthsFixedCheckpoint0352 : FourNinthsFixedState :=
  ⟨0xfe6e01903a341d2f377d5276a93157567453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb6234e3a2142de3221a1e18d370e68240c7dbad150356cceebf1854073c6ade502a72fe9782e140975a21e1b8e1ee9d6c0999f0de5b45820fdfb0582de31ea7922ee5118186b439ca10649badb742d7e464154ccbcd3b89783e01d04317c69259f5265778159da00c2c0be6755477d4730fab29028114347161469e2fefb396d8349327309f0031ffc34fee4b328fcaeda0b8b264ae4332a929969d6a2cfb7ec3d4319b0bc6e8b59934038c5899a094c33b91a578e735bb024714f3e2df9ce59eee169eb8fc78b01f5a18e4223884dbd5d8e884f52acf4d5ab0e3dac8595294f34845c155ea181a5385e0cbfcc6cff790561d59813497ec0122434e1f1ae5d12ade56c125ff237486b249d16c79a11bc8862a8d9582123a3efa30bf25db6713, 0xfe6e01903a341d2f377d5276a93157567453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb6234e3a2142de3221a1e18d370e68240c7dbad150356cceebf1854073c6ade502a72fe9782e140975a21e1b8e1ee9d6c0999f0de5b45820fdfb0582de31ea7922ee5118186b439ca10649badb742d7e464154ccbcd3b89783e01d04317c69259f5265778159da00c2c0be6755477d4730fab29028114347161469e2fefb396d8349327309f0031ffc34fee4b328fcaeda0b8b264ae4332a929969d6a2cfb7ec3d4319b0bc6e8b59934038c5899a094c33b91a578e735bb024714f3e2df9ce59eee169eb8fc78b01f5a18e4223884dbd5d8e884f52acf4d5ab0e3dac8595294f34845c155ea181a5385e0cbfcc6cff790561d59813497ec0122434e1f1ae5d12ade56c125ff237486b249d16c79a11bc8862a8d9582123a3efa30bf25db67bc, 0xb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0352_transition :
    fourNinthsFixedAdvance 320 fourNinthsFixedCheckpoint0320 32 =
      some fourNinthsFixedCheckpoint0352 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0352_sound :
    fourNinthsFixedCheckpoint0352.Sound 352 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0320_sound
      fourNinthsFixedCheckpoint0352_transition)

private def fourNinthsFixedCheckpoint0384 : FourNinthsFixedState :=
  ⟨0x3a341d2f377d5276a93157567453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca2221a1e18d370e68240c7dbad150356cceebf1854073c6ade502a72fe9782e140975a21e1b8bd5c55678751f0de5a25720fdfb0582de31ea7922ee5118186b439ca10649badb742d7e464154ccbcd3b89782cf0bf3316b68149f5265777059ca00c2c0be6755477d4730fab29028114347161469e2fefb396d83493273096be217ba34fac4aae6fcaeda0b8b15cae3332a929969d6a2cfb7ec3d4319b0bc6e8b59934038c5899a094c337816474d6f5baf20710e3a2df9ce59eee159ab8fb78b01f5a18e4223884dbd5d8e884f52acf4d5ab0e3dac8574e8ce328054155e6101a334560cbfcc6cff790551b59812497ec0122434e1f1ae5d12ade56c125ff237486b148d06b78a01ac886298c958111393efa30bf25db6704, 0x3a341d2f377d5276a93157567453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca2221a1e18d370e68240c7dbad150356cceebf1854073c6ade502a72fe9782e140975a21e1b8bd5c55678751f0de5a25720fdfb0582de31ea7922ee5118186b439ca10649badb742d7e464154ccbcd3b89782cf0bf3316b68149f5265777059ca00c2c0be6755477d4730fab29028114347161469e2fefb396d83493273096be217ba34fac4aae6fcaeda0b8b15cae3332a929969d6a2cfb7ec3d4319b0bc6e8b59934038c5899a094c337816474d6f5baf20710e3a2df9ce59eee159ab8fb78b01f5a18e4223884dbd5d8e884f52acf4d5ab0e3dac8574e8ce328054155e6101a334560cbfcc6cff790551b59812497ec0122434e1f1ae5d12ade56c125ff237486b148d06b78a01ac886298c958111393efa30bf25db67bc, 0x980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0384_transition :
    fourNinthsFixedAdvance 352 fourNinthsFixedCheckpoint0352 32 =
      some fourNinthsFixedCheckpoint0384 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0384_sound :
    fourNinthsFixedCheckpoint0384.Sound 384 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0352_sound
      fourNinthsFixedCheckpoint0384_transition)

private def fourNinthsFixedCheckpoint0416 : FourNinthsFixedState :=
  ⟨0x377d5276a93157567453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc7dbad150356cceebf1854073c6ade502a72fe9782e140975a21e1b8bd5c55678751f0de5a25720fdf1e502d52dea77fede48f3886b439ca10649badb742d7e464154ccbcd3b89782cf0bf3316b68149f5265777059ca00c2bfad6655466d3730faa18018104236061469e2fefb396d83493273096be217ba34fac4aae6fcaeda0b8b15cae3332a929948cea0cfb7cb3d0319b0bb664b4993203083799a094c337816474d6f5baf20710e3a2df9ce59eee159ab8fb78b01f5a18a31e3844dbd597e874f52acf4c56a0e2dac8174a7ca228054155e6101a334560cbfcc6cff790551b59812497ec012243460efae5512ade4eb125bf237486b138b02b77a01ac086094c148111393efa30bf25db66f4, 0x377d5276a93157567453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc7dbad150356cceebf1854073c6ade502a72fe9782e140975a21e1b8bd5c55678751f0de5a25720fdf1e502d52dea77fede48f3886b439ca10649badb742d7e464154ccbcd3b89782cf0bf3316b68149f5265777059ca00c2bfad6655466d3730faa18018104236061469e2fefb396d83493273096be217ba34fac4aae6fcaeda0b8b15cae3332a929948cea0cfb7cb3d0319b0bb664b4993203083799a094c337816474d6f5baf20710e3a2df9ce59eee159ab8fb78b01f5a18a31e3844dbd597e874f52acf4c56a0e2dac8174a7ca228054155e6101a334560cbfcc6cff790551b59812497ec012243460efae5512ade4eb125bf237486b138b02b77a01ac086094c148111393efa30bf25db67bc, 0xf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0416_transition :
    fourNinthsFixedAdvance 384 fourNinthsFixedCheckpoint0384 32 =
      some fourNinthsFixedCheckpoint0416 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0416_sound :
    fourNinthsFixedCheckpoint0416.Sound 416 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0384_sound
      fourNinthsFixedCheckpoint0416_transition)

private def fourNinthsFixedCheckpoint0448 : FourNinthsFixedState :=
  ⟨0xa93157567453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7dabf1854073c6ade502a72fe9782e140975a21e1b8bd5c55678751f0de5a25720fdf1e502d52dea77fede48f388623f0c57e23979daf3e479c64154ccbcd3b89782cf0bf3316b68149f5265777059ca00c2bfad6655466d3730faa18018104236061359d1eeea285d73392272095ad206ba34fac4aae6fcaeda0b8b15cae3332a929948cea0cfb7cb3d0319b0bb664b49932030837999e84bf1681226452f4bab1f710c3a29d8ce17eee159ab8fb78b01f5a18a31e3844dbd597e874f52acf4c56a0e2dac8174a7ca228050055d5cf1a23045cbbfbc6bff69054db5970e397dbc12243460efae5512ade4eb125bf237486b138b02b77a01ac086094c148111312ef9f03e25d75ed1, 0xa93157567453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7dabf1854073c6ade502a72fe9782e140975a21e1b8bd5c55678751f0de5a25720fdf1e502d52dea77fede48f388623f0c57e23979daf3e479c64154ccbcd3b89782cf0bf3316b68149f5265777059ca00c2bfad6655466d3730faa18018104236061359d1eeea285d73392272095ad206ba34fac4aae6fcaeda0b8b15cae3332a929948cea0cfb7cb3d0319b0bb664b49932030837999e84bf1681226452f4bab1f710c3a29d8ce17eee159ab8fb78b01f5a18a31e3844dbd597e874f52acf4c56a0e2dac8174a7ca228050055d5cf1a23045cbbfbc6bff69054db5970e397dbc12243460efae5512ade4eb125bf237486b138b02b77a01ac086094c148111312ef9f03e25d75fac, 0x6e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0448_transition :
    fourNinthsFixedAdvance 416 fourNinthsFixedCheckpoint0416 32 =
      some fourNinthsFixedCheckpoint0448 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0448_sound :
    fourNinthsFixedCheckpoint0448.Sound 448 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0416_sound
      fourNinthsFixedCheckpoint0448_transition)

private def fourNinthsFixedCheckpoint0480 : FourNinthsFixedState :=
  ⟨0x7453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c2a72fe9782e140975a21e1b8bd5c55678751f0de5a25720fdf1e502d52dea77fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb16b68149f5265777059ca00c2bfad6655466d3730faa18018104236061359d1eeea285d73392272095ad206b933f9c49ae5ecaec9fb7b04bad32319929948cea0cfb7cb3d0319b0bb664b49932030837999e84bf1681226452f4bab1f710c3a29d8ce17ee6139a38fa78ae0f5a17a2de2840bad557d870d52acf4c56a0e2dac8174a7ca228050055d5cf1a23045cbbfbc6bff69054db5970e397dbc11e43060afae4512a9d4eb124bf137386a0f7b01b76a00a8086094c148111312ef9f03e25d75ec1, 0x7453efd48e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c2a72fe9782e140975a21e1b8bd5c55678751f0de5a25720fdf1e502d52dea77fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb16b68149f5265777059ca00c2bfad6655466d3730faa18018104236061359d1eeea285d73392272095ad206b933f9c49ae5ecaec9fb7b04bad32319929948cea0cfb7cb3d0319b0bb664b49932030837999e84bf1681226452f4bab1f710c3a29d8ce17ee6139a38fa78ae0f5a17a2de2840bad557d870d52acf4c56a0e2dac8174a7ca228050055d5cf1a23045cbbfbc6bff69054db5970e397dbc11e43060afae4512a9d4eb124bf137386a0f7b01b76a00a8086094c148111312ef9f03e25d75fac, 0x6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0480_transition :
    fourNinthsFixedAdvance 448 fourNinthsFixedCheckpoint0448 32 =
      some fourNinthsFixedCheckpoint0480 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0480_sound :
    fourNinthsFixedCheckpoint0480.Sound 480 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0448_sound
      fourNinthsFixedCheckpoint0480_transition)

private def fourNinthsFixedCheckpoint0512 : FourNinthsFixedState :=
  ⟨0x8e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef875a21e1b8bd5c55678751f0de5a25720fdf1e502d52dea77fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc2bfad6655466d3730faa18018104236061359d1eeea285d73392272095ad206b933f9c49ae5ecaec9fb7b04bad32319928838bea0bfa7ca2bf2189faa563b39932030837999e84bf1681226452f4bab1f710c3a29d8ce17ee6139a38fa78ae0f5a17a2de2840bad557d870d52a8d3c52a0e29ab8172974602780df4d95bf1623045cbbfbc6bff69054db5970e397dbc11e43060afae4512a9d4eb124bf137386a0f7b01b76a00a8085f90b147111311ef8f03de4d34e6e, 0x8e2be81a85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef875a21e1b8bd5c55678751f0de5a25720fdf1e502d52dea77fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc2bfad6655466d3730faa18018104236061359d1eeea285d73392272095ad206b933f9c49ae5ecaec9fb7b04bad32319928838bea0bfa7ca2bf2189faa563b39932030837999e84bf1681226452f4bab1f710c3a29d8ce17ee6139a38fa78ae0f5a17a2de2840bad557d870d52a8d3c52a0e29ab8172974602780df4d95bf1623045cbbfbc6bff69054db5970e397dbc11e43060afae4512a9d4eb124bf137386a0f7b01b76a00a8085f90b147111311ef8f03de4d34f6c, 0x2bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0512_transition :
    fourNinthsFixedAdvance 480 fourNinthsFixedCheckpoint0480 32 =
      some fourNinthsFixedCheckpoint0512 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0512_sound :
    fourNinthsFixedCheckpoint0512.Sound 512 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0480_sound
      fourNinthsFixedCheckpoint0512_transition)

private def fourNinthsFixedCheckpoint0544 : FourNinthsFixedState :=
  ⟨0x85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c54238751f0de5a25720fdf1e502d52dea77fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f98104236061359d1eeea285d73392272095ad206b933f9c49ae5ecaec9fb7b04bad32319928838bea0bfa7ca2bf2189faa563b3992202f727998e74ae0571126452f3aaa1f710c3a29d8ce17ee6139a38fa78ae0f5a17a2de2840bad557d870d52a8d3c52a0e29ab8172974602780df4d95bf1622fc5cbb77a6bff48fd4ba512ee317dbc11e3285eafae4512a9d4eb124bf137386a0f7b01b76a00a8085f90b147111311ef8f03de4d34e5f, 0x85fa0afce8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c54238751f0de5a25720fdf1e502d52dea77fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f98104236061359d1eeea285d73392272095ad206b933f9c49ae5ecaec9fb7b04bad32319928838bea0bfa7ca2bf2189faa563b3992202f727998e74ae0571126452f3aaa1f710c3a29d8ce17ee6139a38fa78ae0f5a17a2de2840bad557d870d52a8d3c52a0e29ab8172974602780df4d95bf1622fc5cbb77a6bff48fd4ba512ee317dbc11e3285eafae4512a9d4eb124bf137386a0f7b01b76a00a8085f90b147111311ef8f03de4d34f6c, 0x5817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint0544_transition :
    fourNinthsFixedAdvance 512 fourNinthsFixedCheckpoint0512 32 =
      some fourNinthsFixedCheckpoint0544 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0544_sound :
    fourNinthsFixedCheckpoint0544.Sound 544 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0512_sound
      fourNinthsFixedCheckpoint0544_transition)

private def fourNinthsFixedCheckpoint0576 : FourNinthsFixedState :=
  ⟨0xe8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbfdf1e502d52dea77fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3973392272095ad206b933f9c49ae5ecaec9fb7b04bad32319928838bea0bfa7ca2bf2189faa563b3992202f727998e74ae0571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f5a17a2de2840bad557d870d52a8d3c52a0e29ab8172974602780df4d95bf1622fc5cbb77a6bff48fd4ba512ee317dbc11e3285eaf2e451269c466f143ef37386a0779013348f868085f90b147111311ef8f03de4d34e4e, 0xe8651a0831831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbfdf1e502d52dea77fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3973392272095ad206b933f9c49ae5ecaec9fb7b04bad32319928838bea0bfa7ca2bf2189faa563b3992202f727998e74ae0571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f5a17a2de2840bad557d870d52a8d3c52a0e29ab8172974602780df4d95bf1622fc5cbb77a6bff48fd4ba512ee317dbc11e3285eaf2e451269c466f143ef37386a0779013348f868085f90b147111311ef8f03de4d34f6c, 0x3f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0576_transition :
    fourNinthsFixedAdvance 544 fourNinthsFixedCheckpoint0544 32 =
      some fourNinthsFixedCheckpoint0576 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0576_sound :
    fourNinthsFixedCheckpoint0576.Sound 576 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0544_sound
      fourNinthsFixedCheckpoint0576_transition)

private def fourNinthsFixedCheckpoint0608 : FourNinthsFixedState :=
  ⟨0x31831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49ae5ecaec9fb7b04bad32319928838bea0bfa7ca2bf2189faa563b3992202f727998e74ae0571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0e29ab8172974602780df4d95bf1622fc5cbb77a6bff48fd4ba512ee317dbc11e3285eaf2e451269c466f143ef37386a0779013348f86807db70a947110ef1ef4ef3de4c2ce22, 0x31831973d2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fede48f388623f0c57e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49ae5ecaec9fb7b04bad32319928838bea0bfa7ca2bf2189faa563b3992202f727998e74ae0571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0e29ab8172974602780df4d95bf1622fc5cbb77a6bff48fd4ba512ee317dbc11e3285eaf2e451269c466f143ef37386a0779013348f86807db70a947110ef1ef4ef3de4c2cf4c, 0x1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint0608_transition :
    fourNinthsFixedAdvance 576 fourNinthsFixedCheckpoint0576 32 =
      some fourNinthsFixedCheckpoint0608 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0608_sound :
    fourNinthsFixedCheckpoint0608.Sound 608 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0576_sound
      fourNinthsFixedCheckpoint0608_transition)

private def fourNinthsFixedCheckpoint0640 : FourNinthsFixedState :=
  ⟨0xd2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc07e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da19028838bea0bfa7ca2bf2189faa563b3992202f727998e74ae0571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611fc5cbb77a6bff48fd4ba512ee317dbc11e3285eaf2e451269c466f143ef37386a0779013348f86807db70a947110ef1ef4ef3de4c2ce14, 0xd2d2741a6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc07e23979daf3e479c43934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da19028838bea0bfa7ca2bf2189faa563b3992202f727998e74ae0571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611fc5cbb77a6bff48fd4ba512ee317dbc11e3285eaf2e451269c466f143ef37386a0779013348f86807db70a947110ef1ef4ef3de4c2cf4c, 0xce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0640_transition :
    fourNinthsFixedAdvance 608 fourNinthsFixedCheckpoint0608 32 =
      some fourNinthsFixedCheckpoint0640 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0640_sound :
    fourNinthsFixedCheckpoint0640.Sound 640 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0608_sound
      fourNinthsFixedCheckpoint0640_transition)

private def fourNinthsFixedCheckpoint0672 : FourNinthsFixedState :=
  ⟨0x6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e465843934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a563b3992202f727998e74ae0571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11e3285eaf2e451269c466f143ef37386a0779013348f86807db70a947110ef1ef4ef3de4c2ce05, 0x6f9fc1cb0ce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e465843934bcb3d3a8567e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a563b3992202f727998e74ae0571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11e3285eaf2e451269c466f143ef37386a0779013348f86807db70a947110ef1ef4ef3de4c2cf4c, 0x582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0672_transition :
    fourNinthsFixedAdvance 640 fourNinthsFixedCheckpoint0640 32 =
      some fourNinthsFixedCheckpoint0672 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0672_sound :
    fourNinthsFixedCheckpoint0672.Sound 672 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0640_sound
      fourNinthsFixedCheckpoint0672_transition)

private def fourNinthsFixedCheckpoint0704 : FourNinthsFixedState :=
  ⟨0xce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a50571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0779013348f86807db70a947110ef1ef4ef3de4c2cdf1, 0xce0cf4e142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e3ecaeeb12264145e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a50571126452f3aaa1e710c2a18c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0779013348f86807db70a947110ef1ef4ef3de4c2cf4c, 0xd383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0704_transition :
    fourNinthsFixedAdvance 672 fourNinthsFixedCheckpoint0672 32 =
      some fourNinthsFixedCheckpoint0704 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0704_sound :
    fourNinthsFixedCheckpoint0704.Sound 704 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0672_sound
      fourNinthsFixedCheckpoint0704_transition)

private def fourNinthsFixedCheckpoint0736 : FourNinthsFixedState :=
  ⟨0x142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ef3de4c2cde2, 0x142ca22214da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e51d32f4bc788fcc0bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c7bd16ee6138a28e9679d0f490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ef3de4c2cf4c, 0x72f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0736_transition :
    fourNinthsFixedAdvance 704 fourNinthsFixedCheckpoint0704 32 =
      some fourNinthsFixedCheckpoint0736 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0736_sound :
    fourNinthsFixedCheckpoint0736.Sound 736 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0704_sound
      fourNinthsFixedCheckpoint0736_transition)

private def fourNinthsFixedCheckpoint0768 : FourNinthsFixedState :=
  ⟨0x14da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d07490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bdc7, 0x14da13c36f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80bf88e64d25daef10faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d07490792de2730b9d457d760c52a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bf3b, 0x4445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0768_transition :
    fourNinthsFixedAdvance 736 fourNinthsFixedCheckpoint0736 32 =
      some fourNinthsFixedCheckpoint0768 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0768_sound :
    fourNinthsFixedCheckpoint0768.Sound 768 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0736_sound
      fourNinthsFixedCheckpoint0768_transition)

private def fourNinthsFixedCheckpoint0800 : FourNinthsFixedState :=
  ⟨0x6f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eec0faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc2a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bdb9, 0x6f957debc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eec0faa05f96103e23bcf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc2a8d2c52a0d19ab70729744f277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bf3b, 0xc3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0800_transition :
    fourNinthsFixedAdvance 768 fourNinthsFixedCheckpoint0768 32 =
      some fourNinthsFixedCheckpoint0800 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0800_sound :
    fourNinthsFixedCheckpoint0800.Sound 800 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0768_sound
      fourNinthsFixedCheckpoint0800_transition)

private def fourNinthsFixedCheckpoint0832 : FourNinthsFixedState :=
  ⟨0xc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df6cf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bda3, 0xc2c697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df6cf2d9d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246277fcf4c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bf3b, 0xd7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint0832_transition :
    fourNinthsFixedAdvance 800 fourNinthsFixedCheckpoint0800 32 =
      some fourNinthsFixedCheckpoint0832 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0832_sound :
    fourNinthsFixedCheckpoint0832.Sound 832 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0800_sound
      fourNinthsFixedCheckpoint0832_transition)

private def fourNinthsFixedCheckpoint0864 : FourNinthsFixedState :=
  ⟨0xf252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a3920f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e95bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bd93, 0xf252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a3920f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e95bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bf3b, 0xc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0864_transition :
    fourNinthsFixedAdvance 832 fourNinthsFixedCheckpoint0832 32 =
      some fourNinthsFixedCheckpoint0864 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0864_sound :
    fourNinthsFixedCheckpoint0864.Sound 864 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0832_sound
      fourNinthsFixedCheckpoint0864_transition)

private def fourNinthsFixedCheckpoint0896 : FourNinthsFixedState :=
  ⟨0x7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf158b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a91d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bd80, 0x7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf158b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a91d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bf3b, 0x5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint0896_transition :
    fourNinthsFixedAdvance 864 fourNinthsFixedCheckpoint0864 32 =
      some fourNinthsFixedCheckpoint0896 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0896_sound :
    fourNinthsFixedCheckpoint0896.Sound 896 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0864_sound
      fourNinthsFixedCheckpoint0896_transition)

private def fourNinthsFixedCheckpoint0928 : FourNinthsFixedState :=
  ⟨0x2b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bd6e, 0x2b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bf3b, 0x60f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint0928_transition :
    fourNinthsFixedAdvance 896 fourNinthsFixedCheckpoint0896 32 =
      some fourNinthsFixedCheckpoint0928 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0928_sound :
    fourNinthsFixedCheckpoint0928.Sound 928 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0896_sound
      fourNinthsFixedCheckpoint0928_transition)

private def fourNinthsFixedCheckpoint0960 : FourNinthsFixedState :=
  ⟨0x1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c40047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406cb6f9837010de0ef4ee3ce4c2bd5d, 0x1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c40047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406cb6f9837010de0ef4ee3ce4c2bf3b, 0x3cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0960_transition :
    fourNinthsFixedAdvance 928 fourNinthsFixedCheckpoint0928 32 =
      some fourNinthsFixedCheckpoint0960 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0960_sound :
    fourNinthsFixedCheckpoint0960.Sound 960 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0928_sound
      fourNinthsFixedCheckpoint0960_transition)

private def fourNinthsFixedCheckpoint0992 : FourNinthsFixedState :=
  ⟨0x2e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc2bd4e, 0x2e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc2bf3b, 0x49b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint0992_transition :
    fourNinthsFixedAdvance 960 fourNinthsFixedCheckpoint0960 32 =
      some fourNinthsFixedCheckpoint0992 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint0992_sound :
    fourNinthsFixedCheckpoint0992.Sound 992 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0960_sound
      fourNinthsFixedCheckpoint0992_transition)

private def fourNinthsFixedCheckpoint1024 : FourNinthsFixedState :=
  ⟨0x19cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23af3, 0x19cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0xe1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1024_transition :
    fourNinthsFixedAdvance 992 fourNinthsFixedCheckpoint0992 32 =
      some fourNinthsFixedCheckpoint1024 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1024_sound :
    fourNinthsFixedCheckpoint1024.Sound 1024 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0992_sound
      fourNinthsFixedCheckpoint1024_transition)

private def fourNinthsFixedCheckpoint1056 : FourNinthsFixedState :=
  ⟨0x691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195da0056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23ae0, 0x691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195da0056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0xcebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1056_transition :
    fourNinthsFixedAdvance 1024 fourNinthsFixedCheckpoint1024 32 =
      some fourNinthsFixedCheckpoint1056 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1056_sound :
    fourNinthsFixedCheckpoint1056.Sound 1056 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1024_sound
      fourNinthsFixedCheckpoint1056_transition)

private def fourNinthsFixedCheckpoint1088 : FourNinthsFixedState :=
  ⟨0x47409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23ad3, 0x47409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0xc42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1088_transition :
    fourNinthsFixedAdvance 1056 fourNinthsFixedCheckpoint1056 32 =
      some fourNinthsFixedCheckpoint1088 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1088_sound :
    fourNinthsFixedCheckpoint1088.Sound 1088 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1056_sound
      fourNinthsFixedCheckpoint1088_transition)

private def fourNinthsFixedCheckpoint1120 : FourNinthsFixedState :=
  ⟨0x59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23ac5, 0x59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0x59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1120_transition :
    fourNinthsFixedAdvance 1088 fourNinthsFixedCheckpoint1088 32 =
      some fourNinthsFixedCheckpoint1120 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1120_sound :
    fourNinthsFixedCheckpoint1120.Sound 1120 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1088_sound
      fourNinthsFixedCheckpoint1120_transition)

private def fourNinthsFixedCheckpoint1152 : FourNinthsFixedState :=
  ⟨0x8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b248f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23ab3, 0x8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b248f752ba1528b9c44eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0xfd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1152_transition :
    fourNinthsFixedAdvance 1120 fourNinthsFixedCheckpoint1120 32 =
      some fourNinthsFixedCheckpoint1152 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1152_sound :
    fourNinthsFixedCheckpoint1152.Sound 1152 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1120_sound
      fourNinthsFixedCheckpoint1152_transition)

private def fourNinthsFixedCheckpoint1184 : FourNinthsFixedState :=
  ⟨0x519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8744eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23aa3, 0x519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8744eb360bc260ae33290909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0x383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1184_transition :
    fourNinthsFixedAdvance 1152 fourNinthsFixedCheckpoint1152 32 =
      some fourNinthsFixedCheckpoint1184 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1184_sound :
    fourNinthsFixedCheckpoint1184.Sound 1184 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1152_sound
      fourNinthsFixedCheckpoint1184_transition)

private def fourNinthsFixedCheckpoint1216 : FourNinthsFixedState :=
  ⟨0xe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd90909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23a91, 0xe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd90909624c604f246037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0xfce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1216_transition :
    fourNinthsFixedAdvance 1184 fourNinthsFixedCheckpoint1184 32 =
      some fourNinthsFixedCheckpoint1216 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1216_sound :
    fourNinthsFixedCheckpoint1216.Sound 1216 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1184_sound
      fourNinthsFixedCheckpoint1216_transition)

private def fourNinthsFixedCheckpoint1248 : FourNinthsFixedState :=
  ⟨0x84e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed41037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23a7f, 0x84e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed41037fc7289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0xccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint1248_transition :
    fourNinthsFixedAdvance 1216 fourNinthsFixedCheckpoint1216 32 =
      some fourNinthsFixedCheckpoint1248 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1248_sound :
    fourNinthsFixedCheckpoint1248.Sound 1248 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1216_sound
      fourNinthsFixedCheckpoint1248_transition)

private def fourNinthsFixedCheckpoint1280 : FourNinthsFixedState :=
  ⟨0x2d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23a71, 0x2d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0x3db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1280_transition :
    fourNinthsFixedAdvance 1248 fourNinthsFixedCheckpoint1248 32 =
      some fourNinthsFixedCheckpoint1280 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1280_sound :
    fourNinthsFixedCheckpoint1280.Sound 1280 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1248_sound
      fourNinthsFixedCheckpoint1280_transition)

private def fourNinthsFixedCheckpoint1312 : FourNinthsFixedState :=
  ⟨0x9a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3ac3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23a61, 0x9a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3ac3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0x9962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1312_transition :
    fourNinthsFixedAdvance 1280 fourNinthsFixedCheckpoint1280 32 =
      some fourNinthsFixedCheckpoint1312 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1312_sound :
    fourNinthsFixedCheckpoint1312.Sound 1312 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1280_sound
      fourNinthsFixedCheckpoint1312_transition)

private def fourNinthsFixedCheckpoint1344 : FourNinthsFixedState :=
  ⟨0x2f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea86918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23a53, 0x2f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea86918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0x1a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint1344_transition :
    fourNinthsFixedAdvance 1312 fourNinthsFixedCheckpoint1312 32 =
      some fourNinthsFixedCheckpoint1344 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1344_sound :
    fourNinthsFixedCheckpoint1344.Sound 1344 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1312_sound
      fourNinthsFixedCheckpoint1344_transition)

private def fourNinthsFixedCheckpoint1376 : FourNinthsFixedState :=
  ⟨0xed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d256270242466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23a42, 0xed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d256270242466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0xae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 4⟩

private theorem fourNinthsFixedCheckpoint1376_transition :
    fourNinthsFixedAdvance 1344 fourNinthsFixedCheckpoint1344 32 =
      some fourNinthsFixedCheckpoint1376 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1376_sound :
    fourNinthsFixedCheckpoint1376.Sound 1376 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1344_sound
      fourNinthsFixedCheckpoint1376_transition)

private def fourNinthsFixedCheckpoint1408 : FourNinthsFixedState :=
  ⟨0xe39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d90365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23a32, 0xe39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d90365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0x44ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1408_transition :
    fourNinthsFixedAdvance 1376 fourNinthsFixedCheckpoint1376 32 =
      some fourNinthsFixedCheckpoint1408 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1408_sound :
    fourNinthsFixedCheckpoint1408.Sound 1408 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1376_sound
      fourNinthsFixedCheckpoint1408_transition)

private def fourNinthsFixedCheckpoint1440 : FourNinthsFixedState :=
  ⟨0xc1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc6ca6b87ef008b98cb3ce2cdcc23a20, 0xc1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc6ca6b87ef008b98cb3ce2cdcc23cf3, 0x575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1440_transition :
    fourNinthsFixedAdvance 1408 fourNinthsFixedCheckpoint1408 32 =
      some fourNinthsFixedCheckpoint1440 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1440_sound :
    fourNinthsFixedCheckpoint1440.Sound 1440 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1408_sound
      fourNinthsFixedCheckpoint1440_transition)

private def fourNinthsFixedCheckpoint1472 : FourNinthsFixedState :=
  ⟨0xe40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648bb3ce2cdcc23a12, 0xe40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648bb3ce2cdcc23cf3, 0x8f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint1472_transition :
    fourNinthsFixedAdvance 1440 fourNinthsFixedCheckpoint1440 32 =
      some fourNinthsFixedCheckpoint1472 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1472_sound :
    fourNinthsFixedCheckpoint1472.Sound 1472 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1440_sound
      fourNinthsFixedCheckpoint1472_transition)

private def fourNinthsFixedCheckpoint1504 : FourNinthsFixedState :=
  ⟨0x78748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde5c0, 0x78748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 4⟩

private theorem fourNinthsFixedCheckpoint1504_transition :
    fourNinthsFixedAdvance 1472 fourNinthsFixedCheckpoint1472 32 =
      some fourNinthsFixedCheckpoint1504 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1504_sound :
    fourNinthsFixedCheckpoint1504.Sound 1504 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1472_sound
      fourNinthsFixedCheckpoint1504_transition)

private def fourNinthsFixedCheckpoint1536 : FourNinthsFixedState :=
  ⟨0xae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde5b1, 0xae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x13d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint1536_transition :
    fourNinthsFixedAdvance 1504 fourNinthsFixedCheckpoint1504 32 =
      some fourNinthsFixedCheckpoint1536 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1536_sound :
    fourNinthsFixedCheckpoint1536.Sound 1536 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1504_sound
      fourNinthsFixedCheckpoint1536_transition)

private def fourNinthsFixedCheckpoint1568 : FourNinthsFixedState :=
  ⟨0xd1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde5a5, 0xd1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x4bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1568_transition :
    fourNinthsFixedAdvance 1536 fourNinthsFixedCheckpoint1536 32 =
      some fourNinthsFixedCheckpoint1568 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1568_sound :
    fourNinthsFixedCheckpoint1568.Sound 1568 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1536_sound
      fourNinthsFixedCheckpoint1568_transition)

private def fourNinthsFixedCheckpoint1600 : FourNinthsFixedState :=
  ⟨0xfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde593, 0xfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1600_transition :
    fourNinthsFixedAdvance 1568 fourNinthsFixedCheckpoint1568 32 =
      some fourNinthsFixedCheckpoint1600 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1600_sound :
    fourNinthsFixedCheckpoint1600.Sound 1600 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1568_sound
      fourNinthsFixedCheckpoint1600_transition)

private def fourNinthsFixedCheckpoint1632 : FourNinthsFixedState :=
  ⟨0x4bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde582, 0x4bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x17232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1632_transition :
    fourNinthsFixedAdvance 1600 fourNinthsFixedCheckpoint1600 32 =
      some fourNinthsFixedCheckpoint1632 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1632_sound :
    fourNinthsFixedCheckpoint1632.Sound 1632 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1600_sound
      fourNinthsFixedCheckpoint1632_transition)

private def fourNinthsFixedCheckpoint1664 : FourNinthsFixedState :=
  ⟨0x7f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde570, 0x7f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 4⟩

private theorem fourNinthsFixedCheckpoint1664_transition :
    fourNinthsFixedAdvance 1632 fourNinthsFixedCheckpoint1632 32 =
      some fourNinthsFixedCheckpoint1664 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1664_sound :
    fourNinthsFixedCheckpoint1664.Sound 1664 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1632_sound
      fourNinthsFixedCheckpoint1664_transition)

private def fourNinthsFixedCheckpoint1696 : FourNinthsFixedState :=
  ⟨0xa568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde561, 0xa568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x10b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1696_transition :
    fourNinthsFixedAdvance 1664 fourNinthsFixedCheckpoint1664 32 =
      some fourNinthsFixedCheckpoint1696 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1696_sound :
    fourNinthsFixedCheckpoint1696.Sound 1696 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1664_sound
      fourNinthsFixedCheckpoint1696_transition)

private def fourNinthsFixedCheckpoint1728 : FourNinthsFixedState :=
  ⟨0xba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde553, 0xba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1728_transition :
    fourNinthsFixedAdvance 1696 fourNinthsFixedCheckpoint1696 32 =
      some fourNinthsFixedCheckpoint1728 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1728_sound :
    fourNinthsFixedCheckpoint1728.Sound 1728 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1696_sound
      fourNinthsFixedCheckpoint1728_transition)

private def fourNinthsFixedCheckpoint1760 : FourNinthsFixedState :=
  ⟨0xd056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde545, 0xd056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xe868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1760_transition :
    fourNinthsFixedAdvance 1728 fourNinthsFixedCheckpoint1728 32 =
      some fourNinthsFixedCheckpoint1760 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1760_sound :
    fourNinthsFixedCheckpoint1760.Sound 1760 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1728_sound
      fourNinthsFixedCheckpoint1760_transition)

private def fourNinthsFixedCheckpoint1792 : FourNinthsFixedState :=
  ⟨0x75fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde535, 0x75fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xa8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1792_transition :
    fourNinthsFixedAdvance 1760 fourNinthsFixedCheckpoint1760 32 =
      some fourNinthsFixedCheckpoint1792 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1792_sound :
    fourNinthsFixedCheckpoint1792.Sound 1792 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1760_sound
      fourNinthsFixedCheckpoint1792_transition)

private def fourNinthsFixedCheckpoint1824 : FourNinthsFixedState :=
  ⟨0x9d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde523, 0x9d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x2c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1824_transition :
    fourNinthsFixedAdvance 1792 fourNinthsFixedCheckpoint1792 32 =
      some fourNinthsFixedCheckpoint1824 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1824_sound :
    fourNinthsFixedCheckpoint1824.Sound 1824 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1792_sound
      fourNinthsFixedCheckpoint1824_transition)

private def fourNinthsFixedCheckpoint1856 : FourNinthsFixedState :=
  ⟨0x9b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde511, 0x9b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x1d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint1856_transition :
    fourNinthsFixedAdvance 1824 fourNinthsFixedCheckpoint1824 32 =
      some fourNinthsFixedCheckpoint1856 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1856_sound :
    fourNinthsFixedCheckpoint1856.Sound 1856 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1824_sound
      fourNinthsFixedCheckpoint1856_transition)

private def fourNinthsFixedCheckpoint1888 : FourNinthsFixedState :=
  ⟨0x5bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde500, 0x5bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 4⟩

private theorem fourNinthsFixedCheckpoint1888_transition :
    fourNinthsFixedAdvance 1856 fourNinthsFixedCheckpoint1856 32 =
      some fourNinthsFixedCheckpoint1888 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1888_sound :
    fourNinthsFixedCheckpoint1888.Sound 1888 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1856_sound
      fourNinthsFixedCheckpoint1888_transition)

private def fourNinthsFixedCheckpoint1920 : FourNinthsFixedState :=
  ⟨0x3626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde4f1, 0x3626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x2393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint1920_transition :
    fourNinthsFixedAdvance 1888 fourNinthsFixedCheckpoint1888 32 =
      some fourNinthsFixedCheckpoint1920 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1920_sound :
    fourNinthsFixedCheckpoint1920.Sound 1920 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1888_sound
      fourNinthsFixedCheckpoint1920_transition)

private def fourNinthsFixedCheckpoint1952 : FourNinthsFixedState :=
  ⟨0xa7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde4e3, 0xa7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x83f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint1952_transition :
    fourNinthsFixedAdvance 1920 fourNinthsFixedCheckpoint1920 32 =
      some fourNinthsFixedCheckpoint1952 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1952_sound :
    fourNinthsFixedCheckpoint1952.Sound 1952 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1920_sound
      fourNinthsFixedCheckpoint1952_transition)

private def fourNinthsFixedCheckpoint1984 : FourNinthsFixedState :=
  ⟨0x7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde4d3, 0x7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint1984_transition :
    fourNinthsFixedAdvance 1952 fourNinthsFixedCheckpoint1952 32 =
      some fourNinthsFixedCheckpoint1984 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint1984_sound :
    fourNinthsFixedCheckpoint1984.Sound 1984 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1952_sound
      fourNinthsFixedCheckpoint1984_transition)

private def fourNinthsFixedCheckpoint2016 : FourNinthsFixedState :=
  ⟨0x4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde4bf, 0x4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xb5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint2016_transition :
    fourNinthsFixedAdvance 1984 fourNinthsFixedCheckpoint1984 32 =
      some fourNinthsFixedCheckpoint2016 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2016_sound :
    fourNinthsFixedCheckpoint2016.Sound 2016 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1984_sound
      fourNinthsFixedCheckpoint2016_transition)

private def fourNinthsFixedCheckpoint2048 : FourNinthsFixedState :=
  ⟨0xe7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde4b3, 0xe7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x26543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint2048_transition :
    fourNinthsFixedAdvance 2016 fourNinthsFixedCheckpoint2016 32 =
      some fourNinthsFixedCheckpoint2048 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2048_sound :
    fourNinthsFixedCheckpoint2048.Sound 2048 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2016_sound
      fourNinthsFixedCheckpoint2048_transition)

private def fourNinthsFixedCheckpoint2080 : FourNinthsFixedState :=
  ⟨0x47195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde4a5, 0x47195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x6b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint2080_transition :
    fourNinthsFixedAdvance 2048 fourNinthsFixedCheckpoint2048 32 =
      some fourNinthsFixedCheckpoint2080 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2080_sound :
    fourNinthsFixedCheckpoint2080.Sound 2080 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2048_sound
      fourNinthsFixedCheckpoint2080_transition)

private def fourNinthsFixedCheckpoint2112 : FourNinthsFixedState :=
  ⟨0xf12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde493, 0xf12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xf9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2112_transition :
    fourNinthsFixedAdvance 2080 fourNinthsFixedCheckpoint2080 32 =
      some fourNinthsFixedCheckpoint2112 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2112_sound :
    fourNinthsFixedCheckpoint2112.Sound 2112 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2080_sound
      fourNinthsFixedCheckpoint2112_transition)

private def fourNinthsFixedCheckpoint2144 : FourNinthsFixedState :=
  ⟨0xc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde480, 0xc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xf70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 5⟩

private theorem fourNinthsFixedCheckpoint2144_transition :
    fourNinthsFixedAdvance 2112 fourNinthsFixedCheckpoint2112 32 =
      some fourNinthsFixedCheckpoint2144 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2144_sound :
    fourNinthsFixedCheckpoint2144.Sound 2144 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2112_sound
      fourNinthsFixedCheckpoint2144_transition)

private def fourNinthsFixedCheckpoint2176 : FourNinthsFixedState :=
  ⟨0x8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde472, 0x8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x5941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 4⟩

private theorem fourNinthsFixedCheckpoint2176_transition :
    fourNinthsFixedAdvance 2144 fourNinthsFixedCheckpoint2144 32 =
      some fourNinthsFixedCheckpoint2176 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2176_sound :
    fourNinthsFixedCheckpoint2176.Sound 2176 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2144_sound
      fourNinthsFixedCheckpoint2176_transition)

private def fourNinthsFixedCheckpoint2208 : FourNinthsFixedState :=
  ⟨0x4b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde460, 0x4b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x9a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint2208_transition :
    fourNinthsFixedAdvance 2176 fourNinthsFixedCheckpoint2176 32 =
      some fourNinthsFixedCheckpoint2208 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2208_sound :
    fourNinthsFixedCheckpoint2208.Sound 2208 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2176_sound
      fourNinthsFixedCheckpoint2208_transition)

private def fourNinthsFixedCheckpoint2240 : FourNinthsFixedState :=
  ⟨0x529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde454, 0x529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2240_transition :
    fourNinthsFixedAdvance 2208 fourNinthsFixedCheckpoint2208 32 =
      some fourNinthsFixedCheckpoint2240 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2240_sound :
    fourNinthsFixedCheckpoint2240.Sound 2240 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2208_sound
      fourNinthsFixedCheckpoint2240_transition)

private def fourNinthsFixedCheckpoint2272 : FourNinthsFixedState :=
  ⟨0xe016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde446, 0xe016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xe5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2272_transition :
    fourNinthsFixedAdvance 2240 fourNinthsFixedCheckpoint2240 32 =
      some fourNinthsFixedCheckpoint2272 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2272_sound :
    fourNinthsFixedCheckpoint2272.Sound 2272 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2240_sound
      fourNinthsFixedCheckpoint2272_transition)

private def fourNinthsFixedCheckpoint2304 : FourNinthsFixedState :=
  ⟨0x8b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde436, 0x8b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x4deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint2304_transition :
    fourNinthsFixedAdvance 2272 fourNinthsFixedCheckpoint2272 32 =
      some fourNinthsFixedCheckpoint2304 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2304_sound :
    fourNinthsFixedCheckpoint2304.Sound 2304 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2272_sound
      fourNinthsFixedCheckpoint2304_transition)

private def fourNinthsFixedCheckpoint2336 : FourNinthsFixedState :=
  ⟨0xfd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde42b, 0xfd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x6680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2336_transition :
    fourNinthsFixedAdvance 2304 fourNinthsFixedCheckpoint2304 32 =
      some fourNinthsFixedCheckpoint2336 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2336_sound :
    fourNinthsFixedCheckpoint2336.Sound 2336 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2304_sound
      fourNinthsFixedCheckpoint2336_transition)

private def fourNinthsFixedCheckpoint2368 : FourNinthsFixedState :=
  ⟨0x3db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde41b, 0x3db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 3⟩

private theorem fourNinthsFixedCheckpoint2368_transition :
    fourNinthsFixedAdvance 2336 fourNinthsFixedCheckpoint2336 32 =
      some fourNinthsFixedCheckpoint2368 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2368_sound :
    fourNinthsFixedCheckpoint2368.Sound 2368 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2336_sound
      fourNinthsFixedCheckpoint2368_transition)

private def fourNinthsFixedCheckpoint2400 : FourNinthsFixedState :=
  ⟨0xe1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde407, 0xe1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xeef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2400_transition :
    fourNinthsFixedAdvance 2368 fourNinthsFixedCheckpoint2368 32 =
      some fourNinthsFixedCheckpoint2400 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2400_sound :
    fourNinthsFixedCheckpoint2400.Sound 2400 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2368_sound
      fourNinthsFixedCheckpoint2400_transition)

private def fourNinthsFixedCheckpoint2432 : FourNinthsFixedState :=
  ⟨0x3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde3f1, 0x3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint2432_transition :
    fourNinthsFixedAdvance 2400 fourNinthsFixedCheckpoint2400 32 =
      some fourNinthsFixedCheckpoint2432 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2432_sound :
    fourNinthsFixedCheckpoint2432.Sound 2432 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2400_sound
      fourNinthsFixedCheckpoint2432_transition)

private def fourNinthsFixedCheckpoint2464 : FourNinthsFixedState :=
  ⟨0xb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde3e4, 0xb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 4⟩

private theorem fourNinthsFixedCheckpoint2464_transition :
    fourNinthsFixedAdvance 2432 fourNinthsFixedCheckpoint2432 32 =
      some fourNinthsFixedCheckpoint2464 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2464_sound :
    fourNinthsFixedCheckpoint2464.Sound 2464 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2432_sound
      fourNinthsFixedCheckpoint2464_transition)

private def fourNinthsFixedCheckpoint2496 : FourNinthsFixedState :=
  ⟨0xc36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde3d2, 0xc36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x2b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2496_transition :
    fourNinthsFixedAdvance 2464 fourNinthsFixedCheckpoint2464 32 =
      some fourNinthsFixedCheckpoint2496 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2496_sound :
    fourNinthsFixedCheckpoint2496.Sound 2496 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2464_sound
      fourNinthsFixedCheckpoint2496_transition)

private def fourNinthsFixedCheckpoint2528 : FourNinthsFixedState :=
  ⟨0x4320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde3c1, 0x4320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x24cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2528_transition :
    fourNinthsFixedAdvance 2496 fourNinthsFixedCheckpoint2496 32 =
      some fourNinthsFixedCheckpoint2528 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2528_sound :
    fourNinthsFixedCheckpoint2528.Sound 2528 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2496_sound
      fourNinthsFixedCheckpoint2528_transition)

private def fourNinthsFixedCheckpoint2560 : FourNinthsFixedState :=
  ⟨0x9de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde3b8, 0x9de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 4⟩

private theorem fourNinthsFixedCheckpoint2560_transition :
    fourNinthsFixedAdvance 2528 fourNinthsFixedCheckpoint2528 32 =
      some fourNinthsFixedCheckpoint2560 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2560_sound :
    fourNinthsFixedCheckpoint2560.Sound 2560 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2528_sound
      fourNinthsFixedCheckpoint2560_transition)

private def fourNinthsFixedCheckpoint2592 : FourNinthsFixedState :=
  ⟨0x611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde3a7, 0x611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint2592_transition :
    fourNinthsFixedAdvance 2560 fourNinthsFixedCheckpoint2560 32 =
      some fourNinthsFixedCheckpoint2592 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2592_sound :
    fourNinthsFixedCheckpoint2592.Sound 2592 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2560_sound
      fourNinthsFixedCheckpoint2592_transition)

private def fourNinthsFixedCheckpoint2624 : FourNinthsFixedState :=
  ⟨0x825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde398, 0x825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x5cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 4⟩

private theorem fourNinthsFixedCheckpoint2624_transition :
    fourNinthsFixedAdvance 2592 fourNinthsFixedCheckpoint2592 32 =
      some fourNinthsFixedCheckpoint2624 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2624_sound :
    fourNinthsFixedCheckpoint2624.Sound 2624 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2592_sound
      fourNinthsFixedCheckpoint2624_transition)

private def fourNinthsFixedCheckpoint2656 : FourNinthsFixedState :=
  ⟨0x89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde38a, 0x89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x52d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2656_transition :
    fourNinthsFixedAdvance 2624 fourNinthsFixedCheckpoint2624 32 =
      some fourNinthsFixedCheckpoint2656 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2656_sound :
    fourNinthsFixedCheckpoint2656.Sound 2656 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2624_sound
      fourNinthsFixedCheckpoint2656_transition)

private def fourNinthsFixedCheckpoint2688 : FourNinthsFixedState :=
  ⟨0x143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde37a, 0x143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x96157b9152d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint2688_transition :
    fourNinthsFixedAdvance 2656 fourNinthsFixedCheckpoint2656 32 =
      some fourNinthsFixedCheckpoint2688 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2688_sound :
    fourNinthsFixedCheckpoint2688.Sound 2688 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2656_sound
      fourNinthsFixedCheckpoint2688_transition)

private def fourNinthsFixedCheckpoint2720 : FourNinthsFixedState :=
  ⟨0xd2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde36b, 0xd2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x86e6dc2896157b9152d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint2720_transition :
    fourNinthsFixedAdvance 2688 fourNinthsFixedCheckpoint2688 32 =
      some fourNinthsFixedCheckpoint2720 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2720_sound :
    fourNinthsFixedCheckpoint2720.Sound 2720 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2688_sound
      fourNinthsFixedCheckpoint2720_transition)

private def fourNinthsFixedCheckpoint2752 : FourNinthsFixedState :=
  ⟨0xedf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde35e, 0xedf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x80e46a4b86e6dc2896157b9152d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 4⟩

private theorem fourNinthsFixedCheckpoint2752_transition :
    fourNinthsFixedAdvance 2720 fourNinthsFixedCheckpoint2720 32 =
      some fourNinthsFixedCheckpoint2752 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2752_sound :
    fourNinthsFixedCheckpoint2752.Sound 2752 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2720_sound
      fourNinthsFixedCheckpoint2752_transition)

private def fourNinthsFixedCheckpoint2784 : FourNinthsFixedState :=
  ⟨0x2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde34b, 0x2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x5196afb780e46a4b86e6dc2896157b9152d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2784_transition :
    fourNinthsFixedAdvance 2752 fourNinthsFixedCheckpoint2752 32 =
      some fourNinthsFixedCheckpoint2784 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2784_sound :
    fourNinthsFixedCheckpoint2784.Sound 2784 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2752_sound
      fourNinthsFixedCheckpoint2784_transition)

private def fourNinthsFixedCheckpoint2816 : FourNinthsFixedState :=
  ⟨0x3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde33e, 0x3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0xb66a06145196afb780e46a4b86e6dc2896157b9152d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 1⟩

private theorem fourNinthsFixedCheckpoint2816_transition :
    fourNinthsFixedAdvance 2784 fourNinthsFixedCheckpoint2784 32 =
      some fourNinthsFixedCheckpoint2816 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2816_sound :
    fourNinthsFixedCheckpoint2816.Sound 2816 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2784_sound
      fourNinthsFixedCheckpoint2816_transition)

private def fourNinthsFixedCheckpoint2848 : FourNinthsFixedState :=
  ⟨0xd13a9ffc1ca5677deb08648b5fbe2c8bbde332, 0xd13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x3988c3cb66a06145196afb780e46a4b86e6dc2896157b9152d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 5⟩

private theorem fourNinthsFixedCheckpoint2848_transition :
    fourNinthsFixedAdvance 2816 fourNinthsFixedCheckpoint2816 32 =
      some fourNinthsFixedCheckpoint2848 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2848_sound :
    fourNinthsFixedCheckpoint2848.Sound 2848 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2816_sound
      fourNinthsFixedCheckpoint2848_transition)

private def fourNinthsFixedCheckpoint2880 : FourNinthsFixedState :=
  ⟨0x1ca5677deb08648b5fbe2c8bbde31e, 0x1ca5677deb08648b5fbe2c8bbde8af, 0x3ff95c8b03988c3cb66a06145196afb780e46a4b86e6dc2896157b9152d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2880_transition :
    fourNinthsFixedAdvance 2848 fourNinthsFixedCheckpoint2848 32 =
      some fourNinthsFixedCheckpoint2880 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2880_sound :
    fourNinthsFixedCheckpoint2880.Sound 2880 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2848_sound
      fourNinthsFixedCheckpoint2880_transition)

private def fourNinthsFixedCheckpoint2912 : FourNinthsFixedState :=
  ⟨0xeb08648b5fbe2c8bbde30c, 0xeb08648b5fbe2c8bbde8af, 0xbee6a5383ff95c8b03988c3cb66a06145196afb780e46a4b86e6dc2896157b9152d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 2⟩

private theorem fourNinthsFixedCheckpoint2912_transition :
    fourNinthsFixedAdvance 2880 fourNinthsFixedCheckpoint2880 32 =
      some fourNinthsFixedCheckpoint2912 := by
  decide +kernel

private theorem fourNinthsFixedCheckpoint2912_sound :
    fourNinthsFixedCheckpoint2912.Sound 2912 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2880_sound
      fourNinthsFixedCheckpoint2912_transition)

private def fourNinthsFixedTarget0839 : FourNinthsFixedState :=
  ⟨0xc697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f299d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc74c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bda0, 0xc697c3f252b7da7ad74f062b55cd3c1562ed922e8bef8719cddd73691c542347409b9a59e11cbf8ade3c1c519aa73fe8e34f3384e2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f299d1ce67df3970f10271c156c20598b3f9a49adcec9cc9faeb039ac2da190047383c5fbf278127f2177f2a0e16a790fb9d327986a72a5056ed23fd2f3869f9e0cc0598c6b916e63d369a8e1671d0748f752ba1528b9c44eb360bc260ae33290909624c604f246037fc74c94ae1611eb5bbb6795bef47fd3a9502ee316cbb11d2274d9e2e340158b466f132df36375a0777f13237f86806cb6f9837010de0ef4ee3ce4c2bf3b, 0x43d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 9⟩

private theorem fourNinthsFixedTarget0839_transition :
    fourNinthsFixedAdvance 832 fourNinthsFixedCheckpoint0832 7 =
      some fourNinthsFixedTarget0839 := by
  decide +kernel

private theorem fourNinthsFixedTarget0839_sound :
    fourNinthsFixedTarget0839.Sound 839 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint0832_sound
      fourNinthsFixedTarget0839_transition)

private def fourNinthsFixedTarget1259 : FourNinthsFixedState :=
  ⟨0x2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23a7a, 0x2dbc02d1f46999a2e46582f3e0a75ed393522e39c5aeac1d130f1e40d2ea478748bc80ae83d20d1585eebfb54c4e84bb28df67f294d08a568a391ba0c1617d056cf1575fb49349d79c9b89b699f285bdc9c4003626fc1a7a1370e7acd37ad4c8c2a640e7882d647195d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73289465f601a237bb5e712eec7bc3a12f9e99f2b9a918906cb5d29a3c1342466ecb2d715a7190365b10e27ef4406ca6b87ef008b98cb3ce2cdcc23cf3, 0x721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 9⟩

private theorem fourNinthsFixedTarget1259_transition :
    fourNinthsFixedAdvance 1248 fourNinthsFixedCheckpoint1248 11 =
      some fourNinthsFixedTarget1259 := by
  decide +kernel

private theorem fourNinthsFixedTarget1259_sound :
    fourNinthsFixedTarget1259.Sound 1259 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint1248_sound
      fourNinthsFixedTarget1259_transition)

private def fourNinthsFixedTarget2099 : FourNinthsFixedState :=
  ⟨0x1d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde49d, 0x1d9ff12dd0efc1e3829a8df7b0594b26502a529215a7e016d7b208b301660fd8b8743db21f77e1f5dddd3c50421fb5afed40c36f73244320a6019de6ba09611aab3a825d2b4a89dea869143b6761d2562701edf5698a2860566d3c3119c0d13a9ffc1ca5677deb08648b5fbe2c8bbde8af, 0x298e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 10⟩

private theorem fourNinthsFixedTarget2099_transition :
    fourNinthsFixedAdvance 2080 fourNinthsFixedCheckpoint2080 19 =
      some fourNinthsFixedTarget2099 := by
  decide +kernel

private theorem fourNinthsFixedTarget2099_sound :
    fourNinthsFixedTarget2099.Sound 2099 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2080_sound
      fourNinthsFixedTarget2099_transition)

private def fourNinthsFixedTarget2939 : FourNinthsFixedState :=
  ⟨0xb5fbe2c8bbde301, 0xb5fbe2c8bbde8af, 0x12610d7bee6a5383ff95c8b03988c3cb66a06145196afb780e46a4b86e6dc2896157b9152d4ba415cd55886905d67b9806504c224cef6c302b7f5adf8420a3cbbbbaf87eef84dbc2e1d1bf06680cd104deb6807e5a8494a540a64d29a0defb15941c783f70bb48ff9ba98e26b411e7026543132b5ecb35e70ec85e583f646c002393bda14f996d91d939eb92c92dfaea8f36a0be868305d89c516a510b294fe6fb14dd217232adfd77a1a8b04bc175013d12e1e2574b0278f0c8b83575a39c744ac9cb7ae507cf41a6274599962f8b403db4721ccf2c717fce5598a383c7b51fd38879a59d902e2c42a3896cebbb398e1f7d17449b746a83cb3aad460f2eb5e5bed4a4fc3e96343d7bea9f6c3c85b284445342872f30730d383f9f6582e4b4bce98c18c1058a6173f505fa15817d4712bf7ca2e6aea8c956e4abeecf4b82c5c0980767fb8bae335827d942b102928279d46bed97806b596f84d0e68940f9704ed9a4d7e7351a9429848a4d32cd998da, 10⟩

private theorem fourNinthsFixedTarget2939_transition :
    fourNinthsFixedAdvance 2912 fourNinthsFixedCheckpoint2912 27 =
      some fourNinthsFixedTarget2939 := by
  decide +kernel

private theorem fourNinthsFixedTarget2939_sound :
    fourNinthsFixedTarget2939.Sound 2939 :=
  fourNinthsFixedSound_cast (by norm_num)
    (fourNinthsFixedAdvance_sound fourNinthsFixedCheckpoint2912_sound
      fourNinthsFixedTarget2939_transition)


private theorem binaryCoeffPrefixNumerator_eq_of_bounded_coeff
    (a b : ℕ → ℕ) (limit N : ℕ)
    (hcoeff : ∀ n, 0 < n → n ≤ limit → a n = b n)
    (hN : N ≤ limit) :
    binaryCoeffPrefixNumerator a N = binaryCoeffPrefixNumerator b N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [binaryCoeffPrefixNumerator, binaryCoeffPrefixNumerator,
        ih (by omega), hcoeff (N + 1) (by omega) hN]

private theorem fourNinthsSelectedDivisors_mono_of_dvd
    (A : Set ℕ) {a n : ℕ} (han : a ∣ n) (hn : 0 < n) :
    fourNinthsSelectedDivisors A a ⊆ fourNinthsSelectedDivisors A n := by
  classical
  intro d hd
  unfold fourNinthsSelectedDivisors at hd ⊢
  rcases Finset.mem_filter.mp hd with ⟨hda, hdA⟩
  rcases Nat.mem_divisors.mp hda with ⟨hda, -⟩
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hda.trans han, hn.ne'⟩, hdA⟩

private theorem fourNinthsSelectedDivisors_inter
    (A : Set ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    fourNinthsSelectedDivisors A a ∩ fourNinthsSelectedDivisors A b =
      fourNinthsSelectedDivisors A (Nat.gcd a b) := by
  classical
  ext d
  unfold fourNinthsSelectedDivisors
  simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨hda, -⟩, hdA⟩, ⟨⟨hdb, -⟩, -⟩⟩
    exact ⟨⟨Nat.dvd_gcd hda hdb, (Nat.gcd_pos_of_pos_left b ha).ne'⟩, hdA⟩
  · rintro ⟨⟨hdg, -⟩, hdA⟩
    exact
      ⟨⟨⟨hdg.trans (Nat.gcd_dvd_left a b), ha.ne'⟩, hdA⟩,
        ⟨⟨hdg.trans (Nat.gcd_dvd_right a b), hb.ne'⟩, hdA⟩⟩

private theorem finset_union_four_card_identity {α : Type*} [DecidableEq α]
    (X Y Z W : Finset α) :
    (((X ∪ Y) ∪ Z) ∪ W).card +
          (X ∩ Y).card + (X ∩ Z).card + (X ∩ W).card +
          (Y ∩ Z).card + (Y ∩ W).card + (Z ∩ W).card +
          (X ∩ Y ∩ Z ∩ W).card =
      X.card + Y.card + Z.card + W.card +
          (X ∩ Y ∩ Z).card + (X ∩ Y ∩ W).card +
          (X ∩ Z ∩ W).card + (Y ∩ Z ∩ W).card := by
  have hthree (A B C : Finset α) :
      ((A ∪ B) ∪ C).card + (A ∩ B).card + (A ∩ C).card +
          (B ∩ C).card =
        A.card + B.card + C.card + (A ∩ B ∩ C).card := by
    have hAB := Finset.card_union_add_card_inter A B
    have hABC := Finset.card_union_add_card_inter (A ∪ B) C
    have hdistrib : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
      ext d
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    have hinter : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
      ext d
      simp only [Finset.mem_inter]
      tauto
    have hpair := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
    rw [hdistrib] at hABC
    rw [hinter] at hpair
    omega
  have hXYZ := hthree X Y Z
  have hXYZW := Finset.card_union_add_card_inter ((X ∪ Y) ∪ Z) W
  have hdistribW : ((X ∪ Y) ∪ Z) ∩ W =
      ((X ∩ W) ∪ (Y ∩ W)) ∪ (Z ∩ W) := by
    ext d
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [hdistribW] at hXYZW
  have hW := hthree (X ∩ W) (Y ∩ W) (Z ∩ W)
  have hXYW : (X ∩ W) ∩ (Y ∩ W) = X ∩ Y ∩ W := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  have hXZW : (X ∩ W) ∩ (Z ∩ W) = X ∩ Z ∩ W := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  have hYZW : (Y ∩ W) ∩ (Z ∩ W) = Y ∩ Z ∩ W := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  have hXYZWInter : (X ∩ Y ∩ W) ∩ (Z ∩ W) =
      X ∩ Y ∩ Z ∩ W := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  rw [hXYW, hXZW, hYZW, hXYZWInter] at hW
  omega

private theorem fourNinthsSelectedDivisors_union_three_card_identity
    (A : Set ℕ) {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (((fourNinthsSelectedDivisors A a ∪ fourNinthsSelectedDivisors A b) ∪
          fourNinthsSelectedDivisors A c).card +
        supportCoeff A (Nat.gcd a b) +
        supportCoeff A (Nat.gcd a c) +
        supportCoeff A (Nat.gcd b c) =
      supportCoeff A a + supportCoeff A b + supportCoeff A c +
        supportCoeff A (Nat.gcd (Nat.gcd a b) c)) := by
  classical
  let X := fourNinthsSelectedDivisors A a
  let Y := fourNinthsSelectedDivisors A b
  let Z := fourNinthsSelectedDivisors A c
  have hXY : X ∩ Y = fourNinthsSelectedDivisors A (Nat.gcd a b) :=
    fourNinthsSelectedDivisors_inter A ha hb
  have hXZ : X ∩ Z = fourNinthsSelectedDivisors A (Nat.gcd a c) :=
    fourNinthsSelectedDivisors_inter A ha hc
  have hYZ : Y ∩ Z = fourNinthsSelectedDivisors A (Nat.gcd b c) :=
    fourNinthsSelectedDivisors_inter A hb hc
  have hgcd : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hXYZ : X ∩ Y ∩ Z =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd a b) c) := by
    rw [hXY]
    exact fourNinthsSelectedDivisors_inter A hgcd hc
  have hdistrib : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z) := by
    ext d
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hinter : (X ∩ Z) ∩ (Y ∩ Z) = X ∩ Y ∩ Z := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  have hXYcard := Finset.card_union_add_card_inter X Y
  have hXYZcard := Finset.card_union_add_card_inter (X ∪ Y) Z
  have hpairCard := Finset.card_union_add_card_inter (X ∩ Z) (Y ∩ Z)
  rw [hdistrib] at hXYZcard
  rw [hinter] at hpairCard
  have hcount :
      ((X ∪ Y) ∪ Z).card + (X ∩ Y).card + (X ∩ Z).card +
          (Y ∩ Z).card =
        X.card + Y.card + Z.card + (X ∩ Y ∩ Z).card := by
    omega
  rw [hXYZ, hXY, hXZ, hYZ] at hcount
  simpa only [X, Y, Z, fourNinthsSelectedDivisors_card] using hcount

private theorem fourNinthsSelectedDivisors_union_four_card_identity
    (A : Set ℕ) {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ((((fourNinthsSelectedDivisors A a ∪ fourNinthsSelectedDivisors A b) ∪
          fourNinthsSelectedDivisors A c) ∪
          fourNinthsSelectedDivisors A d).card +
        supportCoeff A (Nat.gcd a b) + supportCoeff A (Nat.gcd a c) +
        supportCoeff A (Nat.gcd a d) + supportCoeff A (Nat.gcd b c) +
        supportCoeff A (Nat.gcd b d) + supportCoeff A (Nat.gcd c d) +
        supportCoeff A (Nat.gcd (Nat.gcd (Nat.gcd a b) c) d) =
      supportCoeff A a + supportCoeff A b + supportCoeff A c +
        supportCoeff A d + supportCoeff A (Nat.gcd (Nat.gcd a b) c) +
        supportCoeff A (Nat.gcd (Nat.gcd a b) d) +
        supportCoeff A (Nat.gcd (Nat.gcd a c) d) +
        supportCoeff A (Nat.gcd (Nat.gcd b c) d)) := by
  classical
  let X := fourNinthsSelectedDivisors A a
  let Y := fourNinthsSelectedDivisors A b
  let Z := fourNinthsSelectedDivisors A c
  let W := fourNinthsSelectedDivisors A d
  have hXY : X ∩ Y = fourNinthsSelectedDivisors A (Nat.gcd a b) :=
    fourNinthsSelectedDivisors_inter A ha hb
  have hXZ : X ∩ Z = fourNinthsSelectedDivisors A (Nat.gcd a c) :=
    fourNinthsSelectedDivisors_inter A ha hc
  have hXW : X ∩ W = fourNinthsSelectedDivisors A (Nat.gcd a d) :=
    fourNinthsSelectedDivisors_inter A ha hd
  have hYZ : Y ∩ Z = fourNinthsSelectedDivisors A (Nat.gcd b c) :=
    fourNinthsSelectedDivisors_inter A hb hc
  have hYW : Y ∩ W = fourNinthsSelectedDivisors A (Nat.gcd b d) :=
    fourNinthsSelectedDivisors_inter A hb hd
  have hZW : Z ∩ W = fourNinthsSelectedDivisors A (Nat.gcd c d) :=
    fourNinthsSelectedDivisors_inter A hc hd
  have hgab : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hgac : 0 < Nat.gcd a c := Nat.gcd_pos_of_pos_left c ha
  have hgbc : 0 < Nat.gcd b c := Nat.gcd_pos_of_pos_left c hb
  have hXYZ : X ∩ Y ∩ Z =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd a b) c) := by
    rw [hXY]
    exact fourNinthsSelectedDivisors_inter A hgab hc
  have hXYW : X ∩ Y ∩ W =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd a b) d) := by
    rw [hXY]
    exact fourNinthsSelectedDivisors_inter A hgab hd
  have hXZW : X ∩ Z ∩ W =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd a c) d) := by
    rw [hXZ]
    exact fourNinthsSelectedDivisors_inter A hgac hd
  have hYZW : Y ∩ Z ∩ W =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd b c) d) := by
    rw [hYZ]
    exact fourNinthsSelectedDivisors_inter A hgbc hd
  have hgabc : 0 < Nat.gcd (Nat.gcd a b) c :=
    Nat.gcd_pos_of_pos_left c hgab
  have hXYZW : X ∩ Y ∩ Z ∩ W =
      fourNinthsSelectedDivisors A
        (Nat.gcd (Nat.gcd (Nat.gcd a b) c) d) := by
    rw [hXYZ]
    exact fourNinthsSelectedDivisors_inter A hgabc hd
  have hcount := finset_union_four_card_identity X Y Z W
  rw [hXYZW, hXYZ, hXYW, hXZW, hYZW, hXY, hXZ, hXW, hYZ, hYW,
    hZW] at hcount
  simpa only [X, Y, Z, W, fourNinthsSelectedDivisors_card] using hcount

/-- Selected divisors already visible in at least one of the `2`, `3`, or `5`
parent columns. -/
noncomputable def fourNinthsPrimorialUnionLoad (n : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  ((fourNinthsSelectedDivisors A (n / 2) ∪
      fourNinthsSelectedDivisors A (n / 3)) ∪
        fourNinthsSelectedDivisors A (n / 5)).card

/-- Exact kernel-certified base value for the prime-column normal form. -/
theorem fourNinthsPrimorialUnionLoad_120 :
    fourNinthsPrimorialUnionLoad 120 = 10 := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let P : Set ℕ := ↑(greedyMersennePrefixRat (4 / 9 : ℚ) 120)
  have hselected (n : ℕ) (hn : 0 < n) (hn120 : n ≤ 120) :
      fourNinthsSelectedDivisors A n = fourNinthsSelectedDivisors P n := by
    ext d
    unfold fourNinthsSelectedDivisors
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd120 : d ≤ 120 := (Nat.le_of_dvd hn hdvd).trans hn120
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 120
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd120).2 hdA⟩
    · rintro ⟨hddiv, hdP⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd120 : d ≤ 120 := (Nat.le_of_dvd hn hdvd).trans hn120
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 120 at hdP
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd120).1 hdP⟩
  change ((fourNinthsSelectedDivisors A 60 ∪
      fourNinthsSelectedDivisors A 40) ∪
        fourNinthsSelectedDivisors A 24).card = 10
  rw [hselected 60 (by norm_num) (by norm_num),
    hselected 40 (by norm_num) (by norm_num),
    hselected 24 (by norm_num) (by norm_num)]
  simp only [fourNinthsSelectedDivisors, P, Finset.mem_coe]
  decide +kernel

/-- Exact subtraction-free seven-column identity at positive multiples of
`120`. -/
theorem fourNinthsPrimorialUnionLoad_sevenColumn (k : ℕ) :
    let n := 120 * (k + 1)
    let A := greedyMersenneSupport (4 / 9 : ℝ)
    fourNinthsPrimorialUnionLoad n + supportCoeff A (n / 6) +
          supportCoeff A (n / 10) + supportCoeff A (n / 15) =
      supportCoeff A (n / 2) + supportCoeff A (n / 3) +
          supportCoeff A (n / 5) + supportCoeff A (n / 30) := by
  dsimp only
  let m := k + 1
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h := fourNinthsSelectedDivisors_union_three_card_identity A
    (a := 60 * m) (b := 40 * m) (c := 24 * m)
    (by positivity) (by positivity) (by positivity)
  have h2 : 120 * (k + 1) / 2 = 60 * m := by dsimp [m]; omega
  have h3 : 120 * (k + 1) / 3 = 40 * m := by dsimp [m]; omega
  have h5 : 120 * (k + 1) / 5 = 24 * m := by dsimp [m]; omega
  have h6 : 120 * (k + 1) / 6 = 20 * m := by dsimp [m]; omega
  have h10 : 120 * (k + 1) / 10 = 12 * m := by dsimp [m]; omega
  have h15 : 120 * (k + 1) / 15 = 8 * m := by dsimp [m]; omega
  have h30 : 120 * (k + 1) / 30 = 4 * m := by dsimp [m]; omega
  dsimp [fourNinthsPrimorialUnionLoad]
  rw [h2, h3, h5, h6, h10, h15, h30]
  norm_num [Nat.gcd_mul_right] at h
  simpa only [A, Finset.union_assoc] using h

/-- The causal union is a subset of the full selected-divisor load. -/
theorem fourNinthsPrimorialUnionLoad_le_supportCoeff
    {n : ℕ} (hn : 0 < n) (h30 : 30 ∣ n) :
    fourNinthsPrimorialUnionLoad n ≤
      supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h2 : 2 ∣ n := (show 2 ∣ 30 by norm_num).trans h30
  have h3 : 3 ∣ n := (show 3 ∣ 30 by norm_num).trans h30
  have h5 : 5 ∣ n := (show 5 ∣ 30 by norm_num).trans h30
  have hs2 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h2) hn
  have hs3 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h3) hn
  have hs5 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h5) hn
  rw [← fourNinthsSelectedDivisors_card A n]
  apply Finset.card_le_card
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · rcases Finset.mem_union.mp hd with hd | hd
    · exact hs2 hd
    · exact hs3 hd
  · exact hs5 hd

/-! ## The `2·3·7` causal producer -/

/-- Selected divisors already visible in at least one of the `2`, `3`, or `7`
parent columns. -/
noncomputable def fourNinthsHeptadicUnionLoad (n : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  ((fourNinthsSelectedDivisors A (n / 2) ∪
      fourNinthsSelectedDivisors A (n / 3)) ∪
        fourNinthsSelectedDivisors A (n / 7)).card

/-- Exact kernel-certified base value for the modulus-`84` normal form. -/
theorem fourNinthsHeptadicUnionLoad_84 :
    fourNinthsHeptadicUnionLoad 84 = 6 := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let P : Set ℕ := ↑(greedyMersennePrefixRat (4 / 9 : ℚ) 84)
  have hselected (n : ℕ) (hn : 0 < n) (hn84 : n ≤ 84) :
      fourNinthsSelectedDivisors A n = fourNinthsSelectedDivisors P n := by
    ext d
    unfold fourNinthsSelectedDivisors
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd84 : d ≤ 84 := (Nat.le_of_dvd hn hdvd).trans hn84
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 84
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd84).2 hdA⟩
    · rintro ⟨hddiv, hdP⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd84 : d ≤ 84 := (Nat.le_of_dvd hn hdvd).trans hn84
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 84 at hdP
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd84).1 hdP⟩
  change ((fourNinthsSelectedDivisors A 42 ∪
      fourNinthsSelectedDivisors A 28) ∪
        fourNinthsSelectedDivisors A 12).card = 6
  rw [hselected 42 (by norm_num) (by norm_num),
    hselected 28 (by norm_num) (by norm_num),
    hselected 12 (by norm_num) (by norm_num)]
  simp only [fourNinthsSelectedDivisors, P, Finset.mem_coe]
  decide +kernel

/-- Exact subtraction-free seven-column identity at positive multiples of
`84`. -/
theorem fourNinthsHeptadicUnionLoad_sevenColumn (k : ℕ) :
    let n := 84 * (k + 1)
    let A := greedyMersenneSupport (4 / 9 : ℝ)
    fourNinthsHeptadicUnionLoad n + supportCoeff A (n / 6) +
          supportCoeff A (n / 14) + supportCoeff A (n / 21) =
      supportCoeff A (n / 2) + supportCoeff A (n / 3) +
          supportCoeff A (n / 7) + supportCoeff A (n / 42) := by
  dsimp only
  let m := k + 1
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h := fourNinthsSelectedDivisors_union_three_card_identity A
    (a := 42 * m) (b := 28 * m) (c := 12 * m)
    (by positivity) (by positivity) (by positivity)
  have h2 : 84 * (k + 1) / 2 = 42 * m := by dsimp [m]; omega
  have h3 : 84 * (k + 1) / 3 = 28 * m := by dsimp [m]; omega
  have h7 : 84 * (k + 1) / 7 = 12 * m := by dsimp [m]; omega
  have h6 : 84 * (k + 1) / 6 = 14 * m := by dsimp [m]; omega
  have h14 : 84 * (k + 1) / 14 = 6 * m := by dsimp [m]; omega
  have h21 : 84 * (k + 1) / 21 = 4 * m := by dsimp [m]; omega
  have h42 : 84 * (k + 1) / 42 = 2 * m := by dsimp [m]; omega
  dsimp [fourNinthsHeptadicUnionLoad]
  rw [h2, h3, h7, h6, h14, h21, h42]
  norm_num [Nat.gcd_mul_right] at h
  simpa only [A, Finset.union_assoc] using h

/-- The `2·3·7` causal union is a subset of the full selected-divisor load. -/
theorem fourNinthsHeptadicUnionLoad_le_supportCoeff
    {n : ℕ} (hn : 0 < n) (h42 : 42 ∣ n) :
    fourNinthsHeptadicUnionLoad n ≤
      supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h2 : 2 ∣ n := (show 2 ∣ 42 by norm_num).trans h42
  have h3 : 3 ∣ n := (show 3 ∣ 42 by norm_num).trans h42
  have h7 : 7 ∣ n := (show 7 ∣ 42 by norm_num).trans h42
  have hs2 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h2) hn
  have hs3 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h3) hn
  have hs7 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h7) hn
  rw [← fourNinthsSelectedDivisors_card A n]
  apply Finset.card_le_card
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · rcases Finset.mem_union.mp hd with hd | hd
    · exact hs2 hd
    · exact hs3 hd
  · exact hs7 hd

/-! ## The `2·3·5·7` causal producer -/

/-- Selected divisors already visible in at least one of the `2`, `3`, `5`,
or `7` parent columns. -/
noncomputable def fourNinthsTetraprimeUnionLoad (n : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  (((fourNinthsSelectedDivisors A (n / 2) ∪
      fourNinthsSelectedDivisors A (n / 3)) ∪
        fourNinthsSelectedDivisors A (n / 5)) ∪
          fourNinthsSelectedDivisors A (n / 7)).card

/-- Exact subtraction-free fifteen-column identity at positive multiples of
`420`. -/
theorem fourNinthsTetraprimeUnionLoad_fifteenColumn (k : ℕ) :
    let n := 420 * (k + 1)
    let A := greedyMersenneSupport (4 / 9 : ℝ)
    fourNinthsTetraprimeUnionLoad n +
          supportCoeff A (n / 6) + supportCoeff A (n / 10) +
          supportCoeff A (n / 14) + supportCoeff A (n / 15) +
          supportCoeff A (n / 21) + supportCoeff A (n / 35) +
          supportCoeff A (n / 210) =
      supportCoeff A (n / 2) + supportCoeff A (n / 3) +
          supportCoeff A (n / 5) + supportCoeff A (n / 7) +
          supportCoeff A (n / 30) + supportCoeff A (n / 42) +
          supportCoeff A (n / 70) + supportCoeff A (n / 105) := by
  dsimp only
  let m := k + 1
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h := fourNinthsSelectedDivisors_union_four_card_identity A
    (a := 210 * m) (b := 140 * m) (c := 84 * m) (d := 60 * m)
    (by positivity) (by positivity) (by positivity) (by positivity)
  have h2 : 420 * (k + 1) / 2 = 210 * m := by dsimp [m]; omega
  have h3 : 420 * (k + 1) / 3 = 140 * m := by dsimp [m]; omega
  have h5 : 420 * (k + 1) / 5 = 84 * m := by dsimp [m]; omega
  have h7 : 420 * (k + 1) / 7 = 60 * m := by dsimp [m]; omega
  have h6 : 420 * (k + 1) / 6 = 70 * m := by dsimp [m]; omega
  have h10 : 420 * (k + 1) / 10 = 42 * m := by dsimp [m]; omega
  have h14 : 420 * (k + 1) / 14 = 30 * m := by dsimp [m]; omega
  have h15 : 420 * (k + 1) / 15 = 28 * m := by dsimp [m]; omega
  have h21 : 420 * (k + 1) / 21 = 20 * m := by dsimp [m]; omega
  have h35 : 420 * (k + 1) / 35 = 12 * m := by dsimp [m]; omega
  have h30 : 420 * (k + 1) / 30 = 14 * m := by dsimp [m]; omega
  have h42 : 420 * (k + 1) / 42 = 10 * m := by dsimp [m]; omega
  have h70 : 420 * (k + 1) / 70 = 6 * m := by dsimp [m]; omega
  have h105 : 420 * (k + 1) / 105 = 4 * m := by dsimp [m]; omega
  have h210 : 420 * (k + 1) / 210 = 2 * m := by dsimp [m]; omega
  dsimp [fourNinthsTetraprimeUnionLoad]
  rw [h2, h3, h5, h7, h6, h10, h14, h15, h21, h35, h30, h42,
    h70, h105, h210]
  norm_num [Nat.gcd_mul_right] at h
  simpa only [A, Finset.union_assoc] using h

/-- Exact kernel-certified base value for the modulus-`420` normal form. -/
theorem fourNinthsTetraprimeUnionLoad_420 :
    fourNinthsTetraprimeUnionLoad 420 = 12 := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let P : Set ℕ := ↑(greedyMersennePrefixRat (4 / 9 : ℚ) 420)
  have hselected (n : ℕ) (hn : 0 < n) (hn420 : n ≤ 420) :
      fourNinthsSelectedDivisors A n = fourNinthsSelectedDivisors P n := by
    ext d
    unfold fourNinthsSelectedDivisors
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd420 : d ≤ 420 := (Nat.le_of_dvd hn hdvd).trans hn420
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 420
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd420).2 hdA⟩
    · rintro ⟨hddiv, hdP⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd420 : d ≤ 420 := (Nat.le_of_dvd hn hdvd).trans hn420
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 420 at hdP
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd420).1 hdP⟩
  change (((fourNinthsSelectedDivisors A 210 ∪
      fourNinthsSelectedDivisors A 140) ∪
        fourNinthsSelectedDivisors A 84) ∪
          fourNinthsSelectedDivisors A 60).card = 12
  rw [hselected 210 (by norm_num) (by norm_num),
    hselected 140 (by norm_num) (by norm_num),
    hselected 84 (by norm_num) (by norm_num),
    hselected 60 (by norm_num) (by norm_num)]
  simp only [fourNinthsSelectedDivisors, P, Finset.mem_coe]
  decide +kernel

/-- Exact predecessor defect for the unit cofactor in the modulus-`420`
induction boundary. -/
theorem fourNinthsGreedyDefect_419 :
    fourNinthsGreedyDefect 419 = 7 := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let F := (fourNinthsGreedyStateRat (4 / 9 : ℚ) 419).2
  have hF : F = greedyMersennePrefixRat (4 / 9 : ℚ) 419 := by
    simp [F]
  let c : ℕ → ℕ := fun n =>
    (n.divisors.filter fun d => d ∈ F).card
  have hcoeff (n : ℕ) (hn : 0 < n) (hn419 : n ≤ 419) :
      supportCoeff A n = c n := by
    dsimp only [A, c]
    exact fourNinthsSupportCoeff_eq_prefix F 419 n hF hn hn419
  let defectRec : ℕ → ℤ := fun N =>
    Nat.rec 0 (fun n defect =>
      2 * defect + fourNinthsFloorBit n - (c (n + 1) : ℤ)) N
  have hdefect (N : ℕ) (hN : N ≤ 419) :
      (fourNinthsGreedyDefect N : ℤ) = defectRec N := by
    induction N with
    | zero =>
        simp [defectRec, fourNinthsGreedyDefect, fourNinthsBinaryFloor,
          binaryCoeffPrefixNumerator]
    | succ N ih =>
        rw [fourNinthsGreedyDefect_succ, ih (by omega),
          hcoeff (N + 1) (by omega) hN]
  have hcalc : defectRec 419 = 7 := by
    simp only [defectRec, c]
    decide +kernel
  have hcast : (fourNinthsGreedyDefect 419 : ℤ) = 7 :=
    (hdefect 419 (by norm_num)).trans hcalc
  exact_mod_cast hcast

theorem fourNinthsTetraprimeRepair_unit :
    fourNinthsGreedyDefect (420 - 1) ≤
      fourNinthsTetraprimeUnionLoad 420 := by
  rw [show 420 - 1 = 419 by norm_num, fourNinthsGreedyDefect_419,
    fourNinthsTetraprimeUnionLoad_420]
  norm_num

private def fourNinthsTetraprimeBitsetUnionLoad
    (bits n : ℕ) : ℕ :=
  let selected := fun m =>
    m.divisors.filter fun d => bits.testBit (d - 1)
  (((selected (n / 2) ∪ selected (n / 3)) ∪ selected (n / 5)) ∪
    selected (n / 7)).card

private theorem fourNinthsTetraprimeRepair_of_fixedCertificate
    {p : ℕ} (hp2 : 2 ≤ p) {C : FourNinthsFixedState}
    (hsound : C.Sound (420 * p - 1))
    (hcalc : C.defect ≤
      (fourNinthsTetraprimeBitsetUnionLoad C.bits (420 * p) : ℤ)) :
    fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p) := by
  classical
  let N := 420 * p - 1
  obtain ⟨-, -, -, -, hbits, hdefect⟩ := hsound
  have hdefect' : (fourNinthsGreedyDefect N : ℤ) = C.defect :=
    (fourNinthsCertificateStateRat_defect N).symm.trans hdefect.symm
  have hmem (d : ℕ) (hd : 1 ≤ d) (hdN : d ≤ N) :
      d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) N ↔
        C.bits.testBit (d - 1) := by
    have hcert :
        d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) N ↔
          (fourNinthsCertificateStateRat
            (4 / 9 : ℚ) N).bits[d - 1]? = some true := by
      rw [← fourNinthsGreedyStateRat_snd,
        (fourNinthsCertificateStateRat_agrees_array (4 / 9 : ℚ) N).2]
      exact (fourNinthsGreedyArrayStateRat_spec
        (4 / 9 : ℚ) N).2.2 d hd
    rw [hcert, hbits d hd hdN]
    simp
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let P : Set ℕ := {d | C.bits.testBit (d - 1)}
  have hselected (m : ℕ) (hm : 0 < m) (hmN : m ≤ N) :
      fourNinthsSelectedDivisors A m = fourNinthsSelectedDivisors P m := by
    rw [show fourNinthsSelectedDivisors A m =
        fourNinthsSelectedDivisors
          (↑(greedyMersennePrefixRat (4 / 9 : ℚ) N) : Set ℕ) m by
      dsimp only [A]
      exact fourNinthsSelectedDivisors_eq_prefix
        (greedyMersennePrefixRat (4 / 9 : ℚ) N) N m rfl hm hmN]
    ext d
    unfold fourNinthsSelectedDivisors
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdPrefix⟩
      have hdpos : 1 ≤ d :=
        Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hddiv) hm
      have hdN : d ≤ N :=
        (Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hddiv)).trans hmN
      exact ⟨hddiv, by
        change C.bits.testBit (d - 1)
        exact (hmem d hdpos hdN).1 hdPrefix⟩
    · rintro ⟨hddiv, hdBit⟩
      have hdpos : 1 ≤ d :=
        Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hddiv) hm
      have hdN : d ≤ N :=
        (Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hddiv)).trans hmN
      exact ⟨hddiv, by
        change C.bits.testBit (d - 1) at hdBit
        exact (hmem d hdpos hdN).2 hdBit⟩
  have hload :
      fourNinthsTetraprimeUnionLoad (420 * p) =
        fourNinthsTetraprimeBitsetUnionLoad C.bits (420 * p) := by
    unfold fourNinthsTetraprimeUnionLoad
      fourNinthsTetraprimeBitsetUnionLoad
    dsimp only
    rw [hselected _ (by omega) (by dsimp [N]; omega),
      hselected _ (by omega) (by dsimp [N]; omega),
      hselected _ (by omega) (by dsimp [N]; omega),
      hselected _ (by omega) (by dsimp [N]; omega)]
    simp only [fourNinthsSelectedDivisors, P, Set.mem_setOf_eq]
    apply congrArg Finset.card
    ext d
    simp
  apply nat_le_of_int_cast_le
  rw [show 420 * p - 1 = N by rfl, hdefect', hload]
  exact hcalc

set_option maxHeartbeats 10000000 in
/-- The only prime cofactors not covered by the prime-column normal form are
`2`, `3`, `5`, and `7`; all four repair exactly. -/
theorem fourNinthsTetraprimeRepair_smallPrime
    {p : ℕ} (hp : p.Prime) (hp7 : p ≤ 7) :
    fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p) := by
  interval_cases p <;> norm_num at hp
  · exact fourNinthsTetraprimeRepair_of_fixedCertificate (p := 2)
      (C := fourNinthsFixedTarget0839) (by norm_num)
      fourNinthsFixedTarget0839_sound (by decide +kernel)
  · exact fourNinthsTetraprimeRepair_of_fixedCertificate (p := 3)
      (C := fourNinthsFixedTarget1259) (by norm_num)
      fourNinthsFixedTarget1259_sound (by decide +kernel)
  · exact fourNinthsTetraprimeRepair_of_fixedCertificate (p := 5)
      (C := fourNinthsFixedTarget2099) (by norm_num)
      fourNinthsFixedTarget2099_sound (by decide +kernel)
  · exact fourNinthsTetraprimeRepair_of_fixedCertificate (p := 7)
      (C := fourNinthsFixedTarget2939) (by norm_num)
      fourNinthsFixedTarget2939_sound (by decide +kernel)

/-- The four-prime causal union is a subset of the full selected-divisor
load. -/
theorem fourNinthsTetraprimeUnionLoad_le_supportCoeff
    {n : ℕ} (hn : 0 < n) (h210 : 210 ∣ n) :
    fourNinthsTetraprimeUnionLoad n ≤
      supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h2 : 2 ∣ n := (show 2 ∣ 210 by norm_num).trans h210
  have h3 : 3 ∣ n := (show 3 ∣ 210 by norm_num).trans h210
  have h5 : 5 ∣ n := (show 5 ∣ 210 by norm_num).trans h210
  have h7 : 7 ∣ n := (show 7 ∣ 210 by norm_num).trans h210
  have hs2 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h2) hn
  have hs3 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h3) hn
  have hs5 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h5) hn
  have hs7 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h7) hn
  rw [← fourNinthsSelectedDivisors_card A n]
  apply Finset.card_le_card
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · rcases Finset.mem_union.mp hd with hd | hd
    · rcases Finset.mem_union.mp hd with hd | hd
      · exact hs2 hd
      · exact hs3 hd
    · exact hs5 hd
  · exact hs7 hd

/-! ## Prime-cofactor normal form -/

/-- The moving `420p` support column obtained by pulling the actual support
back through multiplication by a prime cofactor. -/
noncomputable def fourNinthsTetraprimePrimePullbackColumnLoad (p : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  (((fourNinthsSelectedDivisors B 210 ∪
      fourNinthsSelectedDivisors B 140) ∪
        fourNinthsSelectedDivisors B 84) ∪
          fourNinthsSelectedDivisors B 60).card

/-- The literal twenty-three-position support column on the proper divisors
of `420`, pulled forward by a cofactor. -/
noncomputable def fourNinthsTetraprimePrimeProperDivisorColumnLoad
    (p : ℕ) : ℕ := by
  classical
  exact (((420 : ℕ).divisors.erase 420).filter fun d =>
    p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card

theorem fourNinths_properDivisors_420_card :
    ((420 : ℕ).divisors.erase 420).card = 23 := by
  decide +kernel

theorem fourNinthsTetraprimePrimeProperDivisorColumnLoad_le_twenty_three
    (p : ℕ) :
    fourNinthsTetraprimePrimeProperDivisorColumnLoad p ≤ 23 := by
  classical
  unfold fourNinthsTetraprimePrimeProperDivisorColumnLoad
  calc
    (((420 : ℕ).divisors.erase 420).filter fun d =>
      p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card ≤
        ((420 : ℕ).divisors.erase 420).card := Finset.card_filter_le _ _
    _ = 23 := fourNinths_properDivisors_420_card

/-- The four-parent pullback union is exactly the literal proper-divisor
column of `420`. -/
theorem fourNinthsTetraprimePrimePullbackColumnLoad_eq_properDivisors
    (p : ℕ) :
    fourNinthsTetraprimePrimePullbackColumnLoad p =
      fourNinthsTetraprimePrimeProperDivisorColumnLoad p := by
  classical
  have hdivisors :
      (((210 : ℕ).divisors ∪ (140 : ℕ).divisors) ∪
          (84 : ℕ).divisors) ∪ (60 : ℕ).divisors =
        (420 : ℕ).divisors.erase 420 := by
    decide +kernel
  simp only [fourNinthsTetraprimePrimePullbackColumnLoad,
    fourNinthsTetraprimePrimeProperDivisorColumnLoad,
    fourNinthsSelectedDivisors, mem_supportPullback]
  rw [← Finset.filter_union, ← Finset.filter_union,
    ← Finset.filter_union, hdivisors]

private theorem fourNinths_tetraprimeFixedColumn_coprime_of_prime_gt_seven
    {p c : ℕ} (hp : p.Prime) (hp7 : 7 < p) (hc : c ∣ 420) :
    c.Coprime p := by
  have hp2 : p.Coprime 2 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp3 : p.Coprime 3 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp5 : p.Coprime 5 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp7' : p.Coprime 7 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp420' : p.Coprime ((2 ^ 2) * 3 * 5 * 7) :=
    (((Nat.Coprime.pow_right 2 hp2).mul_right hp3).mul_right hp5).mul_right hp7'
  have h420p : (420 : ℕ).Coprime p := by
    have := hp420'.symm
    norm_num at this ⊢
    exact this
  exact Nat.Coprime.of_dvd_left hc h420p

/-- At a prime cofactor above seven, the modulus-`420` causal union splits
exactly into its fixed base column and a twenty-three-position pullback
column. -/
theorem fourNinthsTetraprimeUnionLoad_primeColumn
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    fourNinthsTetraprimeUnionLoad (420 * p) =
      fourNinthsTetraprimeUnionLoad 420 +
        fourNinthsTetraprimePrimePullbackColumnLoad p := by
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  have hcop (c : ℕ) (hc : c ∣ 420) : c.Coprime p :=
    fourNinths_tetraprimeFixedColumn_coprime_of_prime_gt_seven hp hp7 hc
  have hsplit (c : ℕ) (hc : c ∣ 420) :
      supportCoeff A (c * p) = supportCoeff A c + supportCoeff B c := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop c hc)
  have h210 := hsplit 210 (by norm_num)
  have h140 := hsplit 140 (by norm_num)
  have h84 := hsplit 84 (by norm_num)
  have h60 := hsplit 60 (by norm_num)
  have h70 := hsplit 70 (by norm_num)
  have h42 := hsplit 42 (by norm_num)
  have h30 := hsplit 30 (by norm_num)
  have h28 := hsplit 28 (by norm_num)
  have h20 := hsplit 20 (by norm_num)
  have h12 := hsplit 12 (by norm_num)
  have h14 := hsplit 14 (by norm_num)
  have h10 := hsplit 10 (by norm_num)
  have h6 := hsplit 6 (by norm_num)
  have h4 := hsplit 4 (by norm_num)
  have h2 := hsplit 2 (by norm_num)
  have hpPred : p - 1 + 1 = p := by omega
  have hfifteenp := fourNinthsTetraprimeUnionLoad_fifteenColumn (p - 1)
  dsimp only at hfifteenp
  rw [hpPred] at hfifteenp
  have hp2 : 420 * p / 2 = 210 * p := by omega
  have hp3 : 420 * p / 3 = 140 * p := by omega
  have hp5div : 420 * p / 5 = 84 * p := by omega
  have hp7div : 420 * p / 7 = 60 * p := by omega
  have hp6 : 420 * p / 6 = 70 * p := by omega
  have hp10 : 420 * p / 10 = 42 * p := by omega
  have hp14 : 420 * p / 14 = 30 * p := by omega
  have hp15 : 420 * p / 15 = 28 * p := by omega
  have hp21 : 420 * p / 21 = 20 * p := by omega
  have hp35 : 420 * p / 35 = 12 * p := by omega
  have hp30 : 420 * p / 30 = 14 * p := by omega
  have hp42 : 420 * p / 42 = 10 * p := by omega
  have hp70 : 420 * p / 70 = 6 * p := by omega
  have hp105 : 420 * p / 105 = 4 * p := by omega
  have hp210 : 420 * p / 210 = 2 * p := by omega
  rw [hp2, hp3, hp5div, hp7div, hp6, hp10, hp14, hp15, hp21, hp35,
    hp30, hp42, hp70, hp105, hp210] at hfifteenp
  have hfifteen1 := fourNinthsTetraprimeUnionLoad_fifteenColumn 0
  norm_num at hfifteen1
  have hcolumnRaw := fourNinthsSelectedDivisors_union_four_card_identity B
    (a := 210) (b := 140) (c := 84) (d := 60)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcolumn :
      fourNinthsTetraprimePrimePullbackColumnLoad p +
          supportCoeff B 70 + supportCoeff B 42 + supportCoeff B 30 +
          supportCoeff B 28 + supportCoeff B 20 + supportCoeff B 12 +
          supportCoeff B 2 =
        supportCoeff B 210 + supportCoeff B 140 + supportCoeff B 84 +
          supportCoeff B 60 + supportCoeff B 14 + supportCoeff B 10 +
          supportCoeff B 6 + supportCoeff B 4 := by
    norm_num at hcolumnRaw
    simpa only [fourNinthsTetraprimePrimePullbackColumnLoad, A, B,
      Finset.union_assoc] using hcolumnRaw
  dsimp only [A, B] at h210 h140 h84 h60 h70 h42 h30 h28 h20 h12
  dsimp only [A, B] at h14 h10 h6 h4 h2 hcolumn hfifteenp hfifteen1 ⊢
  omega

/-- Numerical modulus-`420` prime-column boundary: all dependence on the
prime is carried by one twenty-three-position pullback column. -/
theorem fourNinthsTetraprimePrimeRepair_iff_defect_le_column_add_twelve
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    fourNinthsGreedyDefect (420 * p - 1) ≤
        fourNinthsTetraprimeUnionLoad (420 * p) ↔
      fourNinthsGreedyDefect (420 * p - 1) ≤
        fourNinthsTetraprimePrimePullbackColumnLoad p + 12 := by
  rw [fourNinthsTetraprimeUnionLoad_primeColumn hp hp7,
    fourNinthsTetraprimeUnionLoad_420]
  omega

/-- Any modulus-`420` prime-row causal repair has defect at most `35`. -/
theorem fourNinthsTetraprimePrimeRepair_defect_le_thirty_five
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hrepair : fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p)) :
    fourNinthsGreedyDefect (420 * p - 1) ≤ 35 := by
  have hcolumn :=
    (fourNinthsTetraprimePrimeRepair_iff_defect_le_column_add_twelve hp hp7).1
      hrepair
  have hle :=
    fourNinthsTetraprimePrimeProperDivisorColumnLoad_le_twenty_three p
  rw [fourNinthsTetraprimePrimePullbackColumnLoad_eq_properDivisors] at hcolumn
  omega

/-- The moving `84p` support column obtained by pulling the actual support
back through multiplication by a prime cofactor. -/
noncomputable def fourNinthsHeptadicPrimePullbackColumnLoad (p : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  ((fourNinthsSelectedDivisors B 42 ∪
      fourNinthsSelectedDivisors B 28) ∪
        fourNinthsSelectedDivisors B 12).card

/-- The literal eleven-position support column on the proper divisors of
`84`, pulled forward by a cofactor. -/
noncomputable def fourNinthsHeptadicPrimeProperDivisorColumnLoad
    (p : ℕ) : ℕ := by
  classical
  exact (((84 : ℕ).divisors.erase 84).filter fun d =>
    p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card

theorem fourNinths_properDivisors_84_card :
    ((84 : ℕ).divisors.erase 84).card = 11 := by
  decide +kernel

theorem fourNinthsHeptadicPrimeProperDivisorColumnLoad_le_eleven (p : ℕ) :
    fourNinthsHeptadicPrimeProperDivisorColumnLoad p ≤ 11 := by
  classical
  unfold fourNinthsHeptadicPrimeProperDivisorColumnLoad
  calc
    (((84 : ℕ).divisors.erase 84).filter fun d =>
      p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card ≤
        ((84 : ℕ).divisors.erase 84).card := Finset.card_filter_le _ _
    _ = 11 := fourNinths_properDivisors_84_card

/-- The moving heptadic pullback column is exactly the literal proper-divisor
column of width eleven. -/
theorem fourNinthsHeptadicPrimePullbackColumnLoad_eq_properDivisors (p : ℕ) :
    fourNinthsHeptadicPrimePullbackColumnLoad p =
      fourNinthsHeptadicPrimeProperDivisorColumnLoad p := by
  classical
  have hdivisors :
      ((42 : ℕ).divisors ∪ (28 : ℕ).divisors) ∪ (12 : ℕ).divisors =
        (84 : ℕ).divisors.erase 84 := by
    decide +kernel
  simp only [fourNinthsHeptadicPrimePullbackColumnLoad,
    fourNinthsHeptadicPrimeProperDivisorColumnLoad,
    fourNinthsSelectedDivisors, mem_supportPullback]
  rw [← Finset.filter_union, ← Finset.filter_union, hdivisors]

/-- The moving selected-divisor column obtained by pulling the actual support
back through multiplication by a prime cofactor. -/
noncomputable def fourNinthsPrimePullbackColumnLoad (p : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  ((fourNinthsSelectedDivisors B 60 ∪
      fourNinthsSelectedDivisors B 40) ∪
        fourNinthsSelectedDivisors B 24).card

/-- The literal fifteen-position support column on the proper divisors of
`120`, pulled forward by a cofactor. -/
noncomputable def fourNinthsPrimeProperDivisorColumnLoad (p : ℕ) : ℕ := by
  classical
  exact (((120 : ℕ).divisors.erase 120).filter fun d =>
    p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card

theorem fourNinths_properDivisors_120_card :
    ((120 : ℕ).divisors.erase 120).card = 15 := by
  decide +kernel

theorem fourNinthsPrimeProperDivisorColumnLoad_le_fifteen (p : ℕ) :
    fourNinthsPrimeProperDivisorColumnLoad p ≤ 15 := by
  classical
  unfold fourNinthsPrimeProperDivisorColumnLoad
  calc
    (((120 : ℕ).divisors.erase 120).filter fun d =>
      p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card ≤
        ((120 : ℕ).divisors.erase 120).card := Finset.card_filter_le _ _
    _ = 15 := fourNinths_properDivisors_120_card

/-- The moving prime pullback column is exactly the preceding literal
fifteen-position column. -/
theorem fourNinthsPrimePullbackColumnLoad_eq_properDivisors (p : ℕ) :
    fourNinthsPrimePullbackColumnLoad p =
      fourNinthsPrimeProperDivisorColumnLoad p := by
  classical
  have hdivisors :
      ((60 : ℕ).divisors ∪ (40 : ℕ).divisors) ∪ (24 : ℕ).divisors =
        (120 : ℕ).divisors.erase 120 := by
    decide +kernel
  simp only [fourNinthsPrimePullbackColumnLoad,
    fourNinthsPrimeProperDivisorColumnLoad, fourNinthsSelectedDivisors,
    mem_supportPullback]
  rw [← Finset.filter_union, ← Finset.filter_union, hdivisors]

private theorem fourNinths_heptadicFixedColumn_coprime_of_prime_gt_seven
    {p c : ℕ} (hp : p.Prime) (hp7 : 7 < p) (hc : c ∣ 84) :
    c.Coprime p := by
  have hp2 : p.Coprime 2 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp3 : p.Coprime 3 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp7' : p.Coprime 7 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp84' : p.Coprime ((2 ^ 2) * 3 * 7) :=
    ((Nat.Coprime.pow_right 2 hp2).mul_right hp3).mul_right hp7'
  have h84p : (84 : ℕ).Coprime p := by
    have := hp84'.symm
    norm_num at this ⊢
    exact this
  exact Nat.Coprime.of_dvd_left hc h84p

/-- At a prime cofactor above seven, the modulus-`84` causal union splits
exactly into its fixed base column and an eleven-position pullback column. -/
theorem fourNinthsHeptadicUnionLoad_primeColumn
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    fourNinthsHeptadicUnionLoad (84 * p) =
      fourNinthsHeptadicUnionLoad 84 +
        fourNinthsHeptadicPrimePullbackColumnLoad p := by
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  have hcop (c : ℕ) (hc : c ∣ 84) : c.Coprime p :=
    fourNinths_heptadicFixedColumn_coprime_of_prime_gt_seven hp hp7 hc
  have hsplit (c : ℕ) (hc : c ∣ 84) :
      supportCoeff A (c * p) = supportCoeff A c + supportCoeff B c := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop c hc)
  have h42 := hsplit 42 (by norm_num)
  have h28 := hsplit 28 (by norm_num)
  have h12 := hsplit 12 (by norm_num)
  have h14 := hsplit 14 (by norm_num)
  have h6 := hsplit 6 (by norm_num)
  have h4 := hsplit 4 (by norm_num)
  have h2 := hsplit 2 (by norm_num)
  have hpPred : p - 1 + 1 = p := by omega
  have hsevenp := fourNinthsHeptadicUnionLoad_sevenColumn (p - 1)
  dsimp only at hsevenp
  rw [hpPred] at hsevenp
  have hp2 : 84 * p / 2 = 42 * p := by omega
  have hp3 : 84 * p / 3 = 28 * p := by omega
  have hp7div : 84 * p / 7 = 12 * p := by omega
  have hp6 : 84 * p / 6 = 14 * p := by omega
  have hp14 : 84 * p / 14 = 6 * p := by omega
  have hp21 : 84 * p / 21 = 4 * p := by omega
  have hp42 : 84 * p / 42 = 2 * p := by omega
  rw [hp2, hp3, hp7div, hp6, hp14, hp21, hp42] at hsevenp
  have hseven1 := fourNinthsHeptadicUnionLoad_sevenColumn 0
  norm_num at hseven1
  have hcolumnRaw := fourNinthsSelectedDivisors_union_three_card_identity B
    (a := 42) (b := 28) (c := 12) (by norm_num) (by norm_num) (by norm_num)
  have hcolumn :
      fourNinthsHeptadicPrimePullbackColumnLoad p + supportCoeff B 14 +
          supportCoeff B 6 + supportCoeff B 4 =
        supportCoeff B 42 + supportCoeff B 28 + supportCoeff B 12 +
          supportCoeff B 2 := by
    norm_num at hcolumnRaw
    simpa only [fourNinthsHeptadicPrimePullbackColumnLoad, A, B,
      Finset.union_assoc] using hcolumnRaw
  dsimp only [A, B] at h42 h28 h12 h14 h6 h4 h2 hcolumn hsevenp hseven1 ⊢
  omega

/-- Numerical modulus-`84` prime-column boundary: all dependence on the prime
is carried by one eleven-position pullback column. -/
theorem fourNinthsHeptadicPrimeRepair_iff_defect_le_column_add_six
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    fourNinthsGreedyDefect (84 * p - 1) ≤
        fourNinthsHeptadicUnionLoad (84 * p) ↔
      fourNinthsGreedyDefect (84 * p - 1) ≤
        fourNinthsHeptadicPrimePullbackColumnLoad p + 6 := by
  rw [fourNinthsHeptadicUnionLoad_primeColumn hp hp7,
    fourNinthsHeptadicUnionLoad_84]
  omega

/-- Any modulus-`84` prime-row causal repair has defect at most `17`. -/
theorem fourNinthsHeptadicPrimeRepair_defect_le_seventeen
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hrepair : fourNinthsGreedyDefect (84 * p - 1) ≤
      fourNinthsHeptadicUnionLoad (84 * p)) :
    fourNinthsGreedyDefect (84 * p - 1) ≤ 17 := by
  have hcolumn :=
    (fourNinthsHeptadicPrimeRepair_iff_defect_le_column_add_six hp hp7).1
      hrepair
  have hle := fourNinthsHeptadicPrimeProperDivisorColumnLoad_le_eleven p
  rw [fourNinthsHeptadicPrimePullbackColumnLoad_eq_properDivisors] at hcolumn
  omega

private theorem fourNinths_fixedColumn_coprime_of_prime_gt_five
    {p c : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hc : c ∣ 120) :
    c.Coprime p := by
  have hp2 : p.Coprime 2 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp3 : p.Coprime 3 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp5' : p.Coprime 5 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp120' : p.Coprime ((2 ^ 3) * 3 * 5) :=
    ((Nat.Coprime.pow_right 3 hp2).mul_right hp3).mul_right hp5'
  have h120p : (120 : ℕ).Coprime p := by
    have := hp120'.symm
    norm_num at this ⊢
    exact this
  exact Nat.Coprime.of_dvd_left hc h120p

/-- At a prime cofactor above five, the causal union splits exactly into its
fixed base column and a finite pulled-back column. -/
theorem fourNinthsPrimorialUnionLoad_primeColumn
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    fourNinthsPrimorialUnionLoad (120 * p) =
      fourNinthsPrimorialUnionLoad 120 +
        fourNinthsPrimePullbackColumnLoad p := by
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  have hcop (c : ℕ) (hc : c ∣ 120) : c.Coprime p :=
    fourNinths_fixedColumn_coprime_of_prime_gt_five hp hp5 hc
  have hsplit (c : ℕ) (hc : c ∣ 120) :
      supportCoeff A (c * p) = supportCoeff A c + supportCoeff B c := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop c hc)
  have h60 := hsplit 60 (by norm_num)
  have h40 := hsplit 40 (by norm_num)
  have h24 := hsplit 24 (by norm_num)
  have h20 := hsplit 20 (by norm_num)
  have h12 := hsplit 12 (by norm_num)
  have h8 := hsplit 8 (by norm_num)
  have h4 := hsplit 4 (by norm_num)
  have hpPred : p - 1 + 1 = p := by omega
  have hsevenp := fourNinthsPrimorialUnionLoad_sevenColumn (p - 1)
  dsimp only at hsevenp
  rw [hpPred] at hsevenp
  have hp2 : 120 * p / 2 = 60 * p := by omega
  have hp3 : 120 * p / 3 = 40 * p := by omega
  have hp5div : 120 * p / 5 = 24 * p := by omega
  have hp6 : 120 * p / 6 = 20 * p := by omega
  have hp10 : 120 * p / 10 = 12 * p := by omega
  have hp15 : 120 * p / 15 = 8 * p := by omega
  have hp30 : 120 * p / 30 = 4 * p := by omega
  rw [hp2, hp3, hp5div, hp6, hp10, hp15, hp30] at hsevenp
  have hseven1 := fourNinthsPrimorialUnionLoad_sevenColumn 0
  norm_num at hseven1
  have hcolumnRaw := fourNinthsSelectedDivisors_union_three_card_identity B
    (a := 60) (b := 40) (c := 24) (by norm_num) (by norm_num) (by norm_num)
  have hcolumn :
      fourNinthsPrimePullbackColumnLoad p + supportCoeff B 20 +
          supportCoeff B 12 + supportCoeff B 8 =
        supportCoeff B 60 + supportCoeff B 40 + supportCoeff B 24 +
          supportCoeff B 4 := by
    norm_num at hcolumnRaw
    simpa only [fourNinthsPrimePullbackColumnLoad, A, B,
      Finset.union_assoc] using hcolumnRaw
  dsimp only [A, B] at h60 h40 h24 h20 h12 h8 h4 hcolumn hsevenp hseven1 ⊢
  omega

theorem fourNinthsPrimePrimorialRepair_iff_column
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    fourNinthsGreedyDefect (120 * p - 1) ≤
        fourNinthsPrimorialUnionLoad (120 * p) ↔
      fourNinthsGreedyDefect (120 * p - 1) ≤
        fourNinthsPrimorialUnionLoad 120 +
          fourNinthsPrimePullbackColumnLoad p := by
  rw [fourNinthsPrimorialUnionLoad_primeColumn hp hp5]

/-- Numerical prime-column boundary: all dependence on the prime is carried
by one finite pullback column. -/
theorem fourNinthsPrimePrimorialRepair_iff_defect_le_column_add_ten
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    fourNinthsGreedyDefect (120 * p - 1) ≤
        fourNinthsPrimorialUnionLoad (120 * p) ↔
      fourNinthsGreedyDefect (120 * p - 1) ≤
        fourNinthsPrimePullbackColumnLoad p + 10 := by
  rw [fourNinthsPrimorialUnionLoad_primeColumn hp hp5,
    fourNinthsPrimorialUnionLoad_120]
  omega

/-- Any prime-row repair has defect at most `25`; a larger prime-row defect
would be an immediate finite-column falsifier. -/
theorem fourNinthsPrimePrimorialRepair_defect_le_twenty_five
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hrepair : fourNinthsGreedyDefect (120 * p - 1) ≤
      fourNinthsPrimorialUnionLoad (120 * p)) :
    fourNinthsGreedyDefect (120 * p - 1) ≤ 25 := by
  have hcolumn :=
    (fourNinthsPrimePrimorialRepair_iff_defect_le_column_add_ten hp hp5).1
      hrepair
  have hle := fourNinthsPrimeProperDivisorColumnLoad_le_fifteen p
  rw [fourNinthsPrimePullbackColumnLoad_eq_properDivisors] at hcolumn
  omega

/-- The `4/9` floor bit immediately before every positive multiple of `120`
is zero. -/
theorem fourNinthsFloorBit_pred_multiple120 (k : ℕ) :
    fourNinthsFloorBit (120 * (k + 1) - 1) = 0 := by
  let t := 20 * (k + 1) - 1
  have hexp : 120 * (k + 1) - 1 = 6 * t + 5 := by
    dsimp [t]
    omega
  have hbase : 2 ^ 6 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
  have hfive : 2 ^ 5 ≡ 5 [MOD 9] := by norm_num [Nat.ModEq]
  have hpow : (2 ^ 6) ^ t ≡ 1 ^ t [MOD 9] := hbase.pow t
  have hprod : (2 ^ 6) ^ t * 2 ^ 5 ≡ 1 ^ t * 5 [MOD 9] :=
    hpow.mul hfive
  have hmodPow : 2 ^ (120 * (k + 1) - 1) % 9 = 5 := by
    change 2 ^ (120 * (k + 1) - 1) ≡ 5 [MOD 9]
    rw [hexp, pow_add, pow_mul]
    simpa using hprod
  have hmod : (4 * 2 ^ (120 * (k + 1) - 1)) % 9 = 2 := by
    have hfour : 4 ≡ 4 [MOD 9] := Nat.ModEq.refl 4
    have := hfour.mul (show 2 ^ (120 * (k + 1) - 1) ≡ 5 [MOD 9] by
      simpa [Nat.ModEq] using hmodPow)
    norm_num [Nat.ModEq] at this ⊢
    exact this
  rw [fourNinthsFloorBit_eq_two_mul_mod_div, hmod]
  norm_num

/-- The `4/9` floor bit immediately before every positive multiple of `84`
is zero. -/
theorem fourNinthsFloorBit_pred_multiple84 (k : ℕ) :
    fourNinthsFloorBit (84 * (k + 1) - 1) = 0 := by
  let t := 14 * (k + 1) - 1
  have hexp : 84 * (k + 1) - 1 = 6 * t + 5 := by
    dsimp [t]
    omega
  have hbase : 2 ^ 6 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
  have hfive : 2 ^ 5 ≡ 5 [MOD 9] := by norm_num [Nat.ModEq]
  have hpow : (2 ^ 6) ^ t ≡ 1 ^ t [MOD 9] := hbase.pow t
  have hprod : (2 ^ 6) ^ t * 2 ^ 5 ≡ 1 ^ t * 5 [MOD 9] :=
    hpow.mul hfive
  have hmodPow : 2 ^ (84 * (k + 1) - 1) % 9 = 5 := by
    change 2 ^ (84 * (k + 1) - 1) ≡ 5 [MOD 9]
    rw [hexp, pow_add, pow_mul]
    simpa using hprod
  have hmod : (4 * 2 ^ (84 * (k + 1) - 1)) % 9 = 2 := by
    have hfour : 4 ≡ 4 [MOD 9] := Nat.ModEq.refl 4
    have := hfour.mul (show 2 ^ (84 * (k + 1) - 1) ≡ 5 [MOD 9] by
      simpa [Nat.ModEq] using hmodPow)
    norm_num [Nat.ModEq] at this ⊢
    exact this
  rw [fourNinthsFloorBit_eq_two_mul_mod_div, hmod]
  norm_num

/-- The `4/9` floor bit immediately before every positive multiple of `420`
is zero. -/
theorem fourNinthsFloorBit_pred_multiple420 (k : ℕ) :
    fourNinthsFloorBit (420 * (k + 1) - 1) = 0 := by
  let t := 70 * (k + 1) - 1
  have hexp : 420 * (k + 1) - 1 = 6 * t + 5 := by
    dsimp [t]
    omega
  have hbase : 2 ^ 6 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
  have hfive : 2 ^ 5 ≡ 5 [MOD 9] := by norm_num [Nat.ModEq]
  have hpow : (2 ^ 6) ^ t ≡ 1 ^ t [MOD 9] := hbase.pow t
  have hprod : (2 ^ 6) ^ t * 2 ^ 5 ≡ 1 ^ t * 5 [MOD 9] :=
    hpow.mul hfive
  have hmodPow : 2 ^ (420 * (k + 1) - 1) % 9 = 5 := by
    change 2 ^ (420 * (k + 1) - 1) ≡ 5 [MOD 9]
    rw [hexp, pow_add, pow_mul]
    simpa using hprod
  have hmod : (4 * 2 ^ (420 * (k + 1) - 1)) % 9 = 2 := by
    have hfour : 4 ≡ 4 [MOD 9] := Nat.ModEq.refl 4
    have := hfour.mul (show 2 ^ (420 * (k + 1) - 1) ≡ 5 [MOD 9] by
      simpa [Nat.ModEq] using hmodPow)
    norm_num [Nat.ModEq] at this ⊢
    exact this
  rw [fourNinthsFloorBit_eq_two_mul_mod_div, hmod]
  norm_num

/-- Open producer corresponding exactly to the audited seven-column law. -/
def FourNinthsMultiple120PrimorialRepair : Prop :=
  ∀ k : ℕ,
    fourNinthsGreedyDefect (120 * (k + 1) - 1) ≤
      fourNinthsPrimorialUnionLoad (120 * (k + 1))

/-- The causal seven-column producer supplies an actual repair at every
positive multiple of `120`. -/
theorem fourNinths_multiple120RepairSupply_of_primorialRepair
    (hrepair : FourNinthsMultiple120PrimorialRepair) :
    FourNinthsMultiple120RepairSupply := by
  intro k
  let n := 120 * (k + 1)
  have hn : 0 < n := by simp [n]
  have h30 : 30 ∣ n := by dsimp [n]; omega
  have hload :
      fourNinthsGreedyDefect (n - 1) ≤
        supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n :=
    (hrepair k).trans (fourNinthsPrimorialUnionLoad_le_supportCoeff hn h30)
  have hpred : n - 1 + 1 = n := by omega
  have hrec := fourNinthsGreedyDefect_succ (n - 1)
  rw [hpred] at hrec
  have hbit : fourNinthsFloorBit (n - 1) = 0 := by
    simpa only [n] using fourNinthsFloorBit_pred_multiple120 k
  have hloadZ :
      (fourNinthsGreedyDefect (n - 1) : ℤ) ≤
        (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n : ℤ) := by
    exact_mod_cast hload
  unfold FourNinthsOneStepRepairSucc
  rw [hbit] at hrec
  rw [show 120 * (k + 1) - 1 + 1 = n by omega]
  exact_mod_cast (show
    (fourNinthsGreedyDefect n : ℤ) ≤
      (fourNinthsGreedyDefect (n - 1) : ℤ) by omega)

theorem four_ninths_mem_of_primorialRepair
    (hrepair : FourNinthsMultiple120PrimorialRepair) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet :=
  four_ninths_mem_of_multiple120RepairSupply
    (fourNinths_multiple120RepairSupply_of_primorialRepair hrepair)

/-- **Exact seven-column endpoint.**  The audited all-depth causal inequality
would refute the universal irrationality statement. -/
theorem not_universal_of_fourNinths_primorialRepair
    (hrepair : FourNinthsMultiple120PrimorialRepair) :
    ¬ UniversalMersenneSubseriesIrrationality :=
  not_universal_of_fourNinths_multiple120RepairSupply
    (fourNinths_multiple120RepairSupply_of_primorialRepair hrepair)

/-- Open producer corresponding exactly to the audited `2·3·7`
seven-column law. -/
def FourNinthsMultiple84HeptadicRepair : Prop :=
  ∀ k : ℕ,
    fourNinthsGreedyDefect (84 * (k + 1) - 1) ≤
      fourNinthsHeptadicUnionLoad (84 * (k + 1))

/-- The `2·3·7` causal producer supplies an actual repair at every positive
multiple of `84`. -/
theorem fourNinths_multiple84RepairSupply_of_heptadicRepair
    (hrepair : FourNinthsMultiple84HeptadicRepair) (k : ℕ) :
    FourNinthsOneStepRepairSucc (84 * (k + 1) - 1) := by
  let n := 84 * (k + 1)
  have hn : 0 < n := by simp [n]
  have h42 : 42 ∣ n := by dsimp [n]; omega
  have hload :
      fourNinthsGreedyDefect (n - 1) ≤
        supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n :=
    (hrepair k).trans (fourNinthsHeptadicUnionLoad_le_supportCoeff hn h42)
  have hpred : n - 1 + 1 = n := by omega
  have hrec := fourNinthsGreedyDefect_succ (n - 1)
  rw [hpred] at hrec
  have hbit : fourNinthsFloorBit (n - 1) = 0 := by
    simpa only [n] using fourNinthsFloorBit_pred_multiple84 k
  have hloadZ :
      (fourNinthsGreedyDefect (n - 1) : ℤ) ≤
        (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n : ℤ) := by
    exact_mod_cast hload
  unfold FourNinthsOneStepRepairSucc
  rw [hbit] at hrec
  rw [show 84 * (k + 1) - 1 + 1 = n by omega]
  exact_mod_cast (show
    (fourNinthsGreedyDefect n : ℤ) ≤
      (fourNinthsGreedyDefect (n - 1) : ℤ) by omega)

/-- The modulus-`84` producer is cofinal and therefore puts `4/9` in the
Mersenne achievement set. -/
theorem four_ninths_mem_of_heptadicRepair
    (hrepair : FourNinthsMultiple84HeptadicRepair) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet := by
  apply four_ninths_mem_mersenneAchievementSet_of_repairCofinal
  intro K
  refine ⟨84 * (K + 1) - 1, ?_,
    fourNinths_multiple84RepairSupply_of_heptadicRepair hrepair K⟩
  omega

/-- **Exact modulus-`84` endpoint.** The all-depth `2·3·7` causal inequality
would refute the universal irrationality statement. -/
theorem not_universal_of_fourNinths_heptadicRepair
    (hrepair : FourNinthsMultiple84HeptadicRepair) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  apply not_universal_of_fourNinths_repairCofinal
  intro K
  refine ⟨84 * (K + 1) - 1, ?_,
    fourNinths_multiple84RepairSupply_of_heptadicRepair hrepair K⟩
  omega

/-- Open four-prime producer corresponding to the audited modulus-`420`
fifteen-column law. -/
def FourNinthsMultiple420TetraprimeRepair : Prop :=
  ∀ k : ℕ,
    fourNinthsGreedyDefect (420 * (k + 1) - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * (k + 1))

/-- Prime-cofactor half of the modulus-`420` induction boundary. -/
def FourNinthsMultiple420PrimeBoundary : Prop :=
  ∀ p : ℕ, p.Prime →
    fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p)

/-- The genuinely moving part of the prime boundary.  The four smaller primes
are a finite kernel-checkable base and should not obscure the all-depth
arithmetic obligation. -/
def FourNinthsMultiple420LargePrimeBoundary : Prop :=
  ∀ p : ℕ, p.Prime → 7 < p →
    fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p)

/-- A phase-free composite boundary suggested by the exact unit margin.  It
asks for five units of causal slack on every composite cofactor. -/
def FourNinthsMultiple420CompositeMarginFive : Prop :=
  ∀ k : ℕ, 1 < k → ¬ k.Prime →
    fourNinthsGreedyDefect (420 * k - 1) + 5 ≤
      fourNinthsTetraprimeUnionLoad (420 * k)

/-- The checked small-prime rows upgrade the genuinely moving large-prime
boundary to the full prime boundary. -/
theorem fourNinths_primeBoundary_of_largePrimeBoundary
    (hlarge : FourNinthsMultiple420LargePrimeBoundary) :
    FourNinthsMultiple420PrimeBoundary := by
  intro p hp
  by_cases hp7 : p ≤ 7
  · exact fourNinthsTetraprimeRepair_smallPrime hp hp7
  · exact hlarge p hp (by omega)

/-- A factor-lattice descent step says the causal margin at a composite
cofactor is no smaller than the margin at one proper divisor.  It is written
without natural-number subtraction so it can be consumed directly by
induction. -/
def FourNinthsMultiple420ProperDivisorDescent : Prop :=
  ∀ k : ℕ, 1 < k → ¬ k.Prime →
    ∃ a : ℕ, 0 < a ∧ a < k ∧ a ∣ k ∧
      fourNinthsGreedyDefect (420 * k - 1) +
          fourNinthsTetraprimeUnionLoad (420 * a) ≤
        fourNinthsGreedyDefect (420 * a - 1) +
          fourNinthsTetraprimeUnionLoad (420 * k)

/-- Five units of composite margin imply the factor-lattice descent, with the
unit cofactor as the canonical parent.  This removes the existential divisor
choice from the live composite obligation. -/
theorem fourNinths_properDivisorDescent_of_compositeMarginFive
    (hmargin : FourNinthsMultiple420CompositeMarginFive) :
    FourNinthsMultiple420ProperDivisorDescent := by
  intro k hk hnotprime
  refine ⟨1, by norm_num, hk, one_dvd k, ?_⟩
  have hkMargin := hmargin k hk hnotprime
  rw [Nat.mul_one, fourNinthsGreedyDefect_419,
    fourNinthsTetraprimeUnionLoad_420]
  omega

/-- Exact induction consumer for the live computational geometry: unit and
prime repair rows plus one nondecreasing proper-divisor margin step for every
composite cofactor imply the full modulus-`420` producer. -/
theorem fourNinths_tetraprimeRepair_of_primeBoundary_of_descent
    (hprime : FourNinthsMultiple420PrimeBoundary)
    (hdescent : FourNinthsMultiple420ProperDivisorDescent) :
    FourNinthsMultiple420TetraprimeRepair := by
  have hall : ∀ k : ℕ, 0 < k →
      fourNinthsGreedyDefect (420 * k - 1) ≤
        fourNinthsTetraprimeUnionLoad (420 * k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hkp : k.Prime
      · exact hprime k hkp
      by_cases hk1 : k = 1
      · simpa only [hk1, Nat.mul_one] using fourNinthsTetraprimeRepair_unit
      have hkgt : 1 < k := by omega
      obtain ⟨a, ha0, hak, -, hmargin⟩ := hdescent k hkgt hkp
      have haRepair := ih a hak ha0
      omega
  intro k
  exact hall (k + 1) (by omega)

/-- Cleaner exact consumer: prime repair plus the uniform five-unit composite
margin imply the full modulus-`420` producer. -/
theorem fourNinths_tetraprimeRepair_of_primeBoundary_of_compositeMarginFive
    (hprime : FourNinthsMultiple420PrimeBoundary)
    (hmargin : FourNinthsMultiple420CompositeMarginFive) :
    FourNinthsMultiple420TetraprimeRepair :=
  fourNinths_tetraprimeRepair_of_primeBoundary_of_descent hprime
    (fourNinths_properDivisorDescent_of_compositeMarginFive hmargin)

/-- Final sharpened interface for the live computation: only primes above
seven and the five-unit composite margin remain open. -/
theorem fourNinths_tetraprimeRepair_of_largePrimeBoundary_of_compositeMarginFive
    (hprime : FourNinthsMultiple420LargePrimeBoundary)
    (hmargin : FourNinthsMultiple420CompositeMarginFive) :
    FourNinthsMultiple420TetraprimeRepair :=
  fourNinths_tetraprimeRepair_of_primeBoundary_of_compositeMarginFive
    (fourNinths_primeBoundary_of_largePrimeBoundary hprime) hmargin

theorem fourNinths_multiple420RepairSupply_of_tetraprimeRepair
    (hrepair : FourNinthsMultiple420TetraprimeRepair) (k : ℕ) :
    FourNinthsOneStepRepairSucc (420 * (k + 1) - 1) := by
  let n := 420 * (k + 1)
  have hn : 0 < n := by simp [n]
  have h210 : 210 ∣ n := by dsimp [n]; omega
  have hload :
      fourNinthsGreedyDefect (n - 1) ≤
        supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n :=
    (hrepair k).trans (fourNinthsTetraprimeUnionLoad_le_supportCoeff hn h210)
  have hpred : n - 1 + 1 = n := by omega
  have hrec := fourNinthsGreedyDefect_succ (n - 1)
  rw [hpred] at hrec
  have hbit : fourNinthsFloorBit (n - 1) = 0 := by
    simpa only [n] using fourNinthsFloorBit_pred_multiple420 k
  have hloadZ :
      (fourNinthsGreedyDefect (n - 1) : ℤ) ≤
        (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n : ℤ) := by
    exact_mod_cast hload
  unfold FourNinthsOneStepRepairSucc
  rw [hbit] at hrec
  rw [show 420 * (k + 1) - 1 + 1 = n by omega]
  exact_mod_cast (show
    (fourNinthsGreedyDefect n : ℤ) ≤
      (fourNinthsGreedyDefect (n - 1) : ℤ) by omega)

theorem not_universal_of_fourNinths_tetraprimeRepair
    (hrepair : FourNinthsMultiple420TetraprimeRepair) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  apply not_universal_of_fourNinths_repairCofinal
  intro K
  refine ⟨420 * (K + 1) - 1, ?_,
    fourNinths_multiple420RepairSupply_of_tetraprimeRepair hrepair K⟩
  omega

#print axioms fourNinthsPrimorialUnionLoad_sevenColumn
#print axioms fourNinthsPrimorialUnionLoad_120
#print axioms fourNinthsPrimorialUnionLoad_primeColumn
#print axioms fourNinthsPrimePullbackColumnLoad_eq_properDivisors
#print axioms fourNinthsPrimePrimorialRepair_defect_le_twenty_five
#print axioms fourNinths_multiple120RepairSupply_of_primorialRepair
#print axioms not_universal_of_fourNinths_primorialRepair
#print axioms fourNinthsHeptadicUnionLoad_sevenColumn
#print axioms fourNinthsHeptadicUnionLoad_84
#print axioms fourNinthsHeptadicUnionLoad_primeColumn
#print axioms fourNinthsHeptadicPrimePullbackColumnLoad_eq_properDivisors
#print axioms fourNinthsHeptadicPrimeRepair_defect_le_seventeen
#print axioms fourNinths_multiple84RepairSupply_of_heptadicRepair
#print axioms not_universal_of_fourNinths_heptadicRepair
#print axioms fourNinthsTetraprimeUnionLoad_420
#print axioms fourNinthsGreedyDefect_419
#print axioms fourNinthsTetraprimeRepair_unit
#print axioms fourNinthsTetraprimeRepair_smallPrime
#print axioms fourNinthsTetraprimeUnionLoad_fifteenColumn
#print axioms fourNinthsTetraprimeUnionLoad_primeColumn
#print axioms fourNinthsTetraprimePrimePullbackColumnLoad_eq_properDivisors
#print axioms fourNinthsTetraprimePrimeRepair_defect_le_thirty_five
#print axioms fourNinths_tetraprimeRepair_of_primeBoundary_of_descent
#print axioms fourNinths_properDivisorDescent_of_compositeMarginFive
#print axioms fourNinths_tetraprimeRepair_of_primeBoundary_of_compositeMarginFive
#print axioms fourNinths_tetraprimeRepair_of_largePrimeBoundary_of_compositeMarginFive
#print axioms fourNinths_multiple420RepairSupply_of_tetraprimeRepair
#print axioms not_universal_of_fourNinths_tetraprimeRepair

end ErdosProblems.Erdos257
