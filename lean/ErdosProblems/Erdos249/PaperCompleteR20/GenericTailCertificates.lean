import Erdos249257.GenericTailOrbitRigidity

/-! Generic coefficient certificates for the long paper's two tail lemmas.
The growth estimate and true-tail recurrence are recovered from
GenericTailOrbitRigidity; the finite discrepancy retains all coefficients. -/
namespace ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates
open Erdos249257
open scoped BigOperators

def windowPrefix (c : ℕ → ℕ) (N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (c (N + j + 1) : ℤ) * 2 ^ (L - 1 - j)

def discrepancy (c : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((c (N + h + j + 1) : ℤ) - c (N + j + 1)) * 2 ^ (L - 1 - j)

def certificate (c : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < discrepancy c h N L % 2 ^ L ∧
  discrepancy c h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

theorem prefix_succ (c : ℕ → ℕ) (N L : ℕ) :
    windowPrefix c N (L + 1) = 2 * windowPrefix c N L + c (N + L + 1) := by
  unfold windowPrefix
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [show L - j = (L - 1 - j) + 1 by omega, pow_succ]
  ring

theorem scaled_tail_split (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (N L : ℕ) :
    (2 : ℝ) ^ L * binaryCoeffTail c N =
      (windowPrefix c N L : ℝ) + binaryCoeffTail c (N + L) := by
  induction L with
  | zero => simp [windowPrefix]
  | succ L ih =>
    rw [prefix_succ, show N + (L + 1) = (N + L) + 1 by omega,
      binaryCoeffTail_succ c hc, pow_succ]
    push_cast
    nlinarith

theorem discrepancy_eq (c : ℕ → ℕ) (h N L : ℕ) :
    discrepancy c h N L = windowPrefix c (N + h) L - windowPrefix c N L := by
  simp only [discrepancy, windowPrefix, sub_mul, Finset.sum_sub_distrib]

theorem scaled_difference (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    (2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ) =
      binaryCoeffTail c (N + h + L) - binaryCoeffTail c (N + L) := by
  rw [discrepancy_eq, Int.cast_sub]
  linarith [scaled_tail_split c hc (N + h) L, scaled_tail_split c hc N L]

theorem truncation_error_bound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    |(2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ)| ≤ (N : ℝ) + h + L + 2 := by
  rw [scaled_difference c hc, abs_sub_le_iff]
  have h1 := binaryCoeffTail_le c hc (N + h + L)
  have h2 := binaryCoeffTail_le c hc (N + L)
  have h3 := binaryCoeffTail_nonneg c (N + h + L)
  have h4 := binaryCoeffTail_nonneg c (N + L)
  push_cast at h1 h2
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) h]

theorem certificate_sound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (h N L : ℕ) (hcert : certificate c h N L) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨k, hk⟩
  obtain ⟨hlow, hhigh⟩ := hcert
  have hb := truncation_error_bound c hc h N L
  rw [← hk] at hb
  have hint : |discrepancy c h N L - k * 2 ^ L| ≤ (N : ℤ) + h + L + 2 := by
    have hb' : |(discrepancy c h N L : ℝ) - (k : ℝ) * 2 ^ L| ≤
        (N : ℝ) + h + L + 2 := by
      simpa [abs_sub_comm, mul_comm] using hb
    exact_mod_cast hb'
  set A := discrepancy c h N L
  set P : ℤ := 2 ^ L
  have hPpos : (0 : ℤ) < P := by dsimp [P]; positivity
  set x : ℤ := A - k * P
  have hxmod : x % P = A % P := by
    have hrw : x = A + P * (-k) := by dsimp [x]; ring
    rw [hrw, Int.add_mul_emod_self_left]
  have hdm : P * (x / P) + A % P = x := by
    rw [← hxmod]
    exact Int.mul_ediv_add_emod x P
  have habs := abs_le.mp hint
  by_cases ht : 0 ≤ x / P
  · have hge : 0 ≤ P * (x / P) := mul_nonneg hPpos.le ht
    linarith [habs.2]
  · have ht1 : x / P ≤ -1 := by omega
    have hle : P * (x / P) ≤ P * (-1) := mul_le_mul_of_nonneg_left ht1 hPpos.le
    linarith [habs.1]

/-- The stated generic tail-period law; oddness of m is unnecessary once
its divisibility into the Mersenne factor is supplied. -/
theorem generic_tail_period (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (p : ℤ) (e m h N : ℕ) (hm : 0 < m) (hN : e ≤ N)
    (hdvd : m ∣ 2 ^ h - 1)
    (hS : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * m)) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨q, hq⟩ := hdvd
  have hpow : 1 ≤ (2 : ℕ) ^ h := Nat.one_le_pow _ _ (by norm_num)
  have hqR : (2 : ℝ) ^ h - 1 = (m : ℝ) * q := by
    have hh := congrArg (fun x : ℕ => (x : ℝ)) hq
    push_cast [Nat.cast_sub hpow] at hh
    exact hh
  have he : (2 : ℝ) ^ N = 2 ^ (N - e) * 2 ^ e := by
    rw [← pow_add, Nat.sub_add_cancel hN]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hf : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
      ((p : ℝ) / ((2 : ℝ) ^ e * m)) = 2 ^ (N - e) * q * p := by
    rw [he, hqR]
    field_simp
  have h1 := scaled_tail_split c hc 0 (N + h)
  have h2 := scaled_tail_split c hc 0 N
  simp only [binaryCoeffTail_zero, zero_add, hS, pow_add] at h1 h2
  refine ⟨(2 : ℤ) ^ (N - e) * q * p + windowPrefix c 0 N - windowPrefix c 0 (N + h), ?_⟩
  push_cast
  nlinarith

end ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_tail_split
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_difference
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.truncation_error_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.certificate_sound
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.generic_tail_period
