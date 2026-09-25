import ErdosProblems.Erdos249.PaperCompleteR7.RationalObservableClassification
import ErdosProblems.Erdos249.PaperCompleteR7.ArbitraryBaseIsolatedPulse

/-!
# Integer-radix totient observables

This module generalizes the analytic part of the bounded-residue theorem from
binary denominators to any integer radix at least two. The original binary
declarations remain the public compatibility interface.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

open scoped BigOperators
open ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables
open ErdosProblems.Erdos249.PaperCompleteR7.ArbitraryBasePulse

/-- The positive-index totient observable in an integer radix. -/
noncomputable def positiveRadixValue (B : ℕ) (f : ℕ → ℚ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, (f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1)

/-- The bounded integer word's value in radix `B`. -/
noncomputable def radixValue (B : ℕ) (a : ℕ → ℤ) : ℝ :=
  ∑' n : ℕ, (a n : ℝ) / (B : ℝ) ^ n

/-- The digits strictly after `N`, rescaled to start at the first radix place. -/
noncomputable def radixTail (B : ℕ) (a : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (a (N + 1 + j) : ℝ) / (B : ℝ) ^ (j + 1)

/-- The geometric series controlling every bounded radix observable. -/
theorem summable_radix_geometric (B : ℕ) (hB : 2 ≤ B) :
    Summable (fun n : ℕ => (1 / (B : ℝ)) ^ n) := by
  have hBreal : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  exact summable_geometric_of_lt_one (by positivity)
    (by rw [div_lt_one (by linarith : (0 : ℝ) < B)]; linarith)

/-- The same geometric series has its usual closed value. -/
theorem tsum_radix_geometric (B : ℕ) (hB : 2 ≤ B) :
    (∑' n : ℕ, (1 / (B : ℝ)) ^ n) = (B : ℝ) / ((B : ℝ) - 1) := by
  have hBreal : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hpos : (0 : ℝ) < (B : ℝ) := by linarith
  rw [tsum_geometric_of_lt_one (by positivity)
    (by rw [div_lt_one hpos]; linarith)]
  field_simp

/-- Closed value of a constant word after the radix point. -/
theorem tsum_const_div_radix_pow_succ (B : ℕ) (hB : 2 ≤ B) (C : ℝ) :
    (∑' j : ℕ, C / (B : ℝ) ^ (j + 1)) = C / ((B : ℝ) - 1) := by
  have hBreal : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  calc
    (∑' j : ℕ, C / (B : ℝ) ^ (j + 1))
        = ∑' j : ℕ, (C / (B : ℝ)) * (1 / (B : ℝ)) ^ j := by
            apply tsum_congr
            intro j
            rw [pow_succ, div_pow]
            field_simp
            simp
    _ = (C / (B : ℝ)) * ((B : ℝ) / ((B : ℝ) - 1)) := by
          rw [tsum_mul_left, tsum_radix_geometric B hB]
    _ = C / ((B : ℝ) - 1) := by
          field_simp

/-- The constant majorant used for bounded radix tails is summable. -/
theorem summable_const_div_radix_pow_succ (B : ℕ) (hB : 2 ≤ B) (C : ℝ) :
    Summable (fun j : ℕ => C / (B : ℝ) ^ (j + 1)) := by
  have hgeo : Summable (fun j : ℕ =>
      (C / (B : ℝ)) * (1 / (B : ℝ)) ^ j) :=
    (summable_radix_geometric B hB).mul_left _
  refine hgeo.congr ?_
  intro j
  rw [pow_succ, div_pow]
  field_simp
  simp

/-- A uniformly bounded integer word has a convergent radix value. -/
theorem summable_radix_terms (B : ℕ) (hB : 2 ≤ B)
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C) :
    Summable (fun n : ℕ => (a n : ℝ) / (B : ℝ) ^ n) := by
  have hgeo : Summable (fun n : ℕ => C * (1 / (B : ℝ)) ^ n) :=
    (summable_radix_geometric B hB).mul_left C
  apply Summable.of_norm_bounded (g := fun n : ℕ => C * (1 / (B : ℝ)) ^ n)
    hgeo
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (B : ℝ) ^ n)]
  rw [div_pow]
  simp only [one_pow, mul_one_div]
  exact div_le_div_of_nonneg_right (hC n) (by positivity)

/-- Every rescaled tail of a bounded word is summable. -/
theorem summable_radix_tail_terms (B : ℕ) (hB : 2 ≤ B)
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C) (N : ℕ) :
    Summable (fun j : ℕ => (a (N + 1 + j) : ℝ) / (B : ℝ) ^ (j + 1)) := by
  have hs := summable_radix_terms B hB (fun j => a (N + 1 + j)) C (fun j => hC _)
  have hs' : Summable (fun j : ℕ =>
      (1 / (B : ℝ)) * ((a (N + 1 + j) : ℝ) / (B : ℝ) ^ j)) :=
    hs.mul_left _
  refine hs'.congr ?_
  intro j
  rw [pow_succ]
  field_simp

/-- Every bounded integer word has a uniformly bounded rescaled tail. -/
theorem abs_radixTail_le (B : ℕ) (hB : 2 ≤ B)
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C) (N : ℕ) :
    |radixTail B a N| ≤ C / ((B : ℝ) - 1) := by
  have hs := summable_radix_tail_terms B hB a C hC N
  have hmajor := summable_const_div_radix_pow_succ B hB C
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  unfold radixTail
  rw [← Real.norm_eq_abs]
  calc
    ‖∑' j : ℕ, (a (N + 1 + j) : ℝ) / (B : ℝ) ^ (j + 1)‖
        ≤ ∑' j : ℕ, ‖(a (N + 1 + j) : ℝ) / (B : ℝ) ^ (j + 1)‖ :=
          norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' j : ℕ, C / (B : ℝ) ^ (j + 1) := by
      apply hs.norm.tsum_le_tsum _ hmajor
      intro j
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hBpos (j + 1))]
      exact div_le_div_of_nonneg_right (hC _) (by positivity)
    _ = C / ((B : ℝ) - 1) := tsum_const_div_radix_pow_succ B hB C

/-- The rescaled tails obey the integer-radix shift recurrence. -/
theorem radixTail_recurrence (B : ℕ) (hB : 2 ≤ B)
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C) (N : ℕ) :
    (B : ℝ) * radixTail B a N = (a (N + 1) : ℝ) + radixTail B a (N + 1) := by
  have hs := summable_radix_tail_terms B hB a C hC N
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun j : ℕ => (a (N + 1 + j) : ℝ) / (B : ℝ) ^ (j + 1)) 1 hs
  simp only [Finset.sum_range_one] at hsplit
  simp only [Nat.add_zero, zero_add, pow_one] at hsplit
  have htail :
      (∑' j : ℕ, (a (N + 1 + (j + 1)) : ℝ) / (B : ℝ) ^ (j + 1 + 1)) =
        (1 / (B : ℝ)) * radixTail B a (N + 1) := by
    unfold radixTail
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    have hidx : N + 1 + (j + 1) = N + 1 + 1 + j := by omega
    rw [hidx, show j + 1 + 1 = (j + 1) + 1 by omega, pow_succ]
    field_simp
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  change (a (N + 1) : ℝ) / (B : ℝ) +
      (∑' j : ℕ, (a (N + 1 + (j + 1)) : ℝ) / (B : ℝ) ^ (j + 1 + 1)) =
        radixTail B a N at hsplit
  rw [htail] at hsplit
  rw [← hsplit]
  field_simp

/-- Multiplying a bounded radix series by a radix power leaves an integer
prefix and exactly the rescaled tail. -/
theorem exists_int_add_radixTail (B : ℕ) (hB : 2 ≤ B)
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C) (N : ℕ) :
    ∃ P : ℤ, (B : ℝ) ^ N * radixValue B a = (P : ℝ) + radixTail B a N := by
  refine ⟨∑ i ∈ Finset.range (N + 1), a i * (B : ℤ) ^ (N - i), ?_⟩
  have hs := summable_radix_terms B hB a C hC
  have h := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (a n : ℝ) / (B : ℝ) ^ n) (N + 1) hs
  have hpre : (B : ℝ) ^ N *
      (∑ i ∈ Finset.range (N + 1), (a i : ℝ) / (B : ℝ) ^ i) =
      ((∑ i ∈ Finset.range (N + 1), a i * (B : ℤ) ^ (N - i) : ℤ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N + 1 := Finset.mem_range.mp hi
    have hsp : (B : ℝ) ^ N = (B : ℝ) ^ i * (B : ℝ) ^ (N - i) := by
      rw [← pow_add]; congr 1; omega
    have hB0 : (B : ℝ) ^ i ≠ 0 := by positivity
    rw [hsp]
    field_simp
  have htail : (B : ℝ) ^ N *
      (∑' s : ℕ, (a (s + (N + 1)) : ℝ) / (B : ℝ) ^ (s + (N + 1))) =
      radixTail B a N := by
    rw [← tsum_mul_left]
    refine tsum_congr fun s => ?_
    have hidx : s + (N + 1) = N + 1 + s := by omega
    rw [hidx]
    have hpow : (B : ℝ) ^ (N + 1 + s) =
        (B : ℝ) ^ N * (B : ℝ) ^ (s + 1) := by
      rw [← pow_add]; congr 1; omega
    have hB0 : (B : ℝ) ^ N ≠ 0 := by positivity
    rw [hpow]
    field_simp
  calc
    (B : ℝ) ^ N * radixValue B a =
        (B : ℝ) ^ N * (∑' n : ℕ, (a n : ℝ) / (B : ℝ) ^ n) := rfl
    _ = (B : ℝ) ^ N *
        ((∑ i ∈ Finset.range (N + 1), (a i : ℝ) / (B : ℝ) ^ i) +
          ∑' s : ℕ, (a (s + (N + 1)) : ℝ) / (B : ℝ) ^ (s + (N + 1))) := by
            rw [← h]
    _ = (B : ℝ) ^ N *
          (∑ i ∈ Finset.range (N + 1), (a i : ℝ) / (B : ℝ) ^ i) +
        (B : ℝ) ^ N *
          (∑' s : ℕ, (a (s + (N + 1)) : ℝ) / (B : ℝ) ^ (s + (N + 1))) := by ring
    _ = _ := by rw [hpre, htail]

/-- The integer-radix series of a bounded integer word is irrational whenever
it has arbitrarily long two-sided isolated nonzero coefficients. -/
theorem irrational_radixValue_of_pulses (B : ℕ) (hB : 2 ≤ B)
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0) :
    Irrational (radixValue B a) := by
  rintro ⟨x, hx⟩
  have hq : 0 < x.den := x.pos
  have hqR : (x.den : ℝ) ≠ 0 := by positivity
  have hvalue : (x.den : ℝ) * radixValue B a = (x.num : ℝ) := by
    rw [← hx, Rat.cast_def]
    field_simp
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hBreal : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ (B : ℝ) - 1 := by linarith
  have hBpos : (0 : ℝ) < (B : ℝ) - 1 := by linarith
  have hCT : ∀ n, |radixTail B a n| ≤ C := by
    intro n
    have htail := abs_radixTail_le B hB a C hC n
    have hdiv : C / ((B : ℝ) - 1) ≤ C :=
      (div_le_iff₀ hBpos).2 (by nlinarith)
    exact htail.trans hdiv
  have hlattice : ∀ n, ∃ z : ℤ,
      (x.den : ℝ) * radixTail B a n = (z : ℝ) := by
    intro n
    obtain ⟨P, hP⟩ := exists_int_add_radixTail B hB a C hC n
    refine ⟨x.num * (B : ℤ) ^ n - (x.den : ℤ) * P, ?_⟩
    push_cast
    have hstep := congrArg (fun y : ℝ => (x.den : ℝ) * y) hP
    calc
      (x.den : ℝ) * radixTail B a n =
          (x.den : ℝ) * ((B : ℝ) ^ n * radixValue B a) -
            (x.den : ℝ) * (P : ℝ) := by linarith
      _ = (x.num : ℝ) * (B : ℝ) ^ n - (x.den : ℝ) * (P : ℝ) := by
        rw [← hvalue]
        ring
  exact no_bounded_lattice_tail_of_pulses B x.den hB hq a
    (radixTail B a) C hC hCT
    (radixTail_recurrence B hB a C hC) hlattice hpulse

/-- The arithmetic prime-isolation theorem supplies the pulse hypothesis for
integer-valued totient observables in every integer radix at least two. -/
theorem irrational_radix_totientObservable
    (B : ℕ) (hB : 2 ≤ B) {m : ℕ} (hm : 2 ≤ m)
    (f : ℕ → ℤ) (hf0 : f 0 = 0)
    {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m) (hfr : f r ≠ 0) :
    Irrational (radixValue B (ErdosProblems.Erdos249.totientObservableCoeff f m)) := by
  let a := ErdosProblems.Erdos249.totientObservableCoeff f m
  let C : ℝ := ((∑ i ∈ Finset.range m, |f i| : ℤ) : ℝ)
  have hC : ∀ n : ℕ, |(a n : ℝ)| ≤ C := by
    intro n
    have hmem : Nat.totient n % m ∈ Finset.range m :=
      Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
    have hz : |f (Nat.totient n % m)| ≤ ∑ i ∈ Finset.range m, |f i| :=
      Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _) hmem
    calc
      |(a n : ℝ)| = ((|f (Nat.totient n % m)| : ℤ) : ℝ) := by
        simp only [a, ErdosProblems.Erdos249.totientObservableCoeff, Int.cast_abs]
      _ ≤ C := by dsimp [C]; exact_mod_cast hz
  have hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0 := by
    intro L
    obtain ⟨p, -, hpL, -, hres, hnb⟩ :=
      ErdosProblems.Erdos249.two_sided_prime_isolation hm L 0 r hcop
    refine ⟨p, hpL, ?_, ?_⟩
    · have hmod : Nat.totient p % m = r % m := hres
      simp only [a, ErdosProblems.Erdos249.totientObservableCoeff,
        hmod, Nat.mod_eq_of_lt hr]
      exact hfr
    · intro j hj hjL
      obtain ⟨hd1, hd2⟩ := hnb j hj hjL
      obtain ⟨c1, hc1⟩ := hd1
      obtain ⟨c2, hc2⟩ := hd2
      simp only [a, ErdosProblems.Erdos249.totientObservableCoeff]
      exact ⟨by rw [hc1, Nat.mul_mod_right, hf0],
        by rw [hc2, Nat.mul_mod_right, hf0]⟩
  exact irrational_radixValue_of_pulses B hB a C hC hpulse

/-- A finite-residue observable has a convergent positive-index radix value. -/
theorem summable_positive_terms (B : ℕ) (hB : 2 ≤ B)
    (m : ℕ) (hm : 0 < m) (f : ℕ → ℚ) :
    Summable (fun n : ℕ =>
      (f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1)) := by
  let C : ℝ := ∑ i ∈ Finset.range m, |(f i : ℝ)|
  have hbound (n : ℕ) : |(f (Nat.totient (n + 1) % m) : ℝ)| ≤ C :=
    Finset.single_le_sum (fun i _ => abs_nonneg (f i : ℝ))
      (Finset.mem_range.mpr (Nat.mod_lt _ hm))
  have hgeo : Summable (fun n : ℕ => (C / (B : ℝ)) * (1 / (B : ℝ)) ^ n) :=
    (summable_radix_geometric B hB).mul_left _
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (C / (B : ℝ)) * (1 / (B : ℝ)) ^ n) hgeo ?_
  intro n
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  calc
    ‖(f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1)‖
        = |(f (Nat.totient (n + 1) % m) : ℝ)| / (B : ℝ) ^ (n + 1) := by
          simp only [Real.norm_eq_abs, abs_div,
            abs_of_pos (pow_pos hBpos (n + 1))]
    _ ≤ C / (B : ℝ) ^ (n + 1) :=
      div_le_div_of_nonneg_right (hbound n) (by positivity)
    _ = (C / (B : ℝ)) * (1 / (B : ℝ)) ^ n := by
      rw [pow_succ, div_pow]
      field_simp
      simp

/-- Exact rational case of the all-integer-base observable classification. -/
theorem positiveRadixValue_eq_of_even_constant
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ℕ → ℚ) (c : ℚ)
    (hc : ∀ r, r < 2 ^ k → r % 2 = 0 → f r = c) :
    positiveRadixValue B f (2 ^ k) =
      ((B : ℝ) + 1) / (B : ℝ) ^ 2 * (f 1 : ℝ) +
        (c : ℝ) / ((B : ℝ) ^ 2 * ((B : ℝ) - 1)) := by
  have hBreal : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hB0 : (B : ℝ) ≠ 0 := by linarith
  have hB1 : (B : ℝ) - 1 ≠ 0 := by linarith
  have hm : 0 < 2 ^ k := by positivity
  have hm2 : 1 < 2 ^ k := by
    have h := two_le_two_pow hk
    omega
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ =>
      (f (Nat.totient (n + 1) % 2 ^ k) : ℝ) / (B : ℝ) ^ (n + 1)) 2
    (summable_positive_terms B hB (2 ^ k) hm f)
  have htail :
      (∑' n : ℕ,
        (f (Nat.totient (n + 2 + 1) % 2 ^ k) : ℝ) /
          (B : ℝ) ^ (n + 2 + 1)) =
        (c : ℝ) / ((B : ℝ) ^ 2 * ((B : ℝ) - 1)) := by
    calc
      (∑' n : ℕ,
          (f (Nat.totient (n + 2 + 1) % 2 ^ k) : ℝ) /
            (B : ℝ) ^ (n + 2 + 1))
          = ∑' n : ℕ, ((c : ℝ) / (B : ℝ) ^ 3) *
              (1 / (B : ℝ)) ^ n := by
                apply tsum_congr
                intro n
                rw [hc _ (Nat.mod_lt _ hm)
                  (totient_mod_two_pow_even hk (by omega))]
                rw [show n + 2 + 1 = 3 + n by omega, pow_add, div_pow]
                field_simp
                ring
      _ = ((c : ℝ) / (B : ℝ) ^ 3) *
          ((B : ℝ) / ((B : ℝ) - 1)) := by
            rw [tsum_mul_left, tsum_radix_geometric B hB]
      _ = (c : ℝ) / ((B : ℝ) ^ 2 * ((B : ℝ) - 1)) := by
            field_simp
  have hprefix :
      (∑ n ∈ Finset.range 2,
        (f (Nat.totient (n + 1) % 2 ^ k) : ℝ) / (B : ℝ) ^ (n + 1)) =
      (f 1 : ℝ) / (B : ℝ) + (f 1 : ℝ) / (B : ℝ) ^ 2 := by
    norm_num [Finset.sum_range_succ, Nat.mod_eq_of_lt hm2,
      show Nat.totient 2 = 1 by decide]
  rw [htail, hprefix] at hsplit
  unfold positiveRadixValue
  rw [← hsplit]
  field_simp

#print axioms tsum_radix_geometric
#print axioms tsum_const_div_radix_pow_succ
#print axioms summable_radix_terms
#print axioms summable_radix_tail_terms
#print axioms abs_radixTail_le
#print axioms radixTail_recurrence
#print axioms exists_int_add_radixTail
#print axioms irrational_radixValue_of_pulses
#print axioms irrational_radix_totientObservable
#print axioms summable_positive_terms
#print axioms positiveRadixValue_eq_of_even_constant

end ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables
