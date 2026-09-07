import Erdos257PeriodNoncollapse.GenericTailOrbitRigidity
import Mathlib

/-!
# Generic certificate soundness and the exact tail-period law

Targets: long-record lem:gsound and lem:gperiod. The ambient coefficient
class is the one explicitly fixed immediately before those lemmas: c : N -> N,
c(n) <= n. Neither theorem assumes a certificate producer.

All declarations contain proof bodies. Build status: NOT RUN.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates

open scoped BigOperators
open Erdos257PeriodNoncollapse

/-- The length-L integer block following the basepoint N. -/
def block (c : ℕ → ℕ) (N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (c (N + 1 + j) : ℤ) * 2 ^ (L - 1 - j)

/-- The paper's generic window discrepancy, with integer subtraction. -/
def window (c : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((c (N + h + 1 + j) : ℤ) - (c (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

def Kill (c : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N : ℤ) + h + L + 2 < window c h N L % 2 ^ L ∧
    window c h N L % 2 ^ L < 2 ^ L - ((N : ℤ) + h + L + 2)

@[simp] theorem block_zero (c : ℕ → ℕ) (N : ℕ) : block c N 0 = 0 := by
  simp [block]

theorem block_succ (c : ℕ → ℕ) (N L : ℕ) :
    block c N (L + 1) = 2 * block c N L + (c (N + L + 1) : ℤ) := by
  unfold block
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hexp (j : ℕ) (hj : j ∈ Finset.range L) :
      L + 1 - 1 - j = (L - 1 - j) + 1 := by
    have := Finset.mem_range.mp hj
    omega
  have hsum : (∑ j ∈ Finset.range L,
      (c (N + 1 + j) : ℤ) * 2 ^ (L + 1 - 1 - j)) =
      ∑ j ∈ Finset.range L, 2 * ((c (N + 1 + j) : ℤ) * 2 ^ (L - 1 - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hexp j hj, pow_succ]
    ring
  rw [hsum]
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem window_eq_sub_blocks (c : ℕ → ℕ) (h N L : ℕ) :
    window c h N L = block c (N + h) L - block c N L := by
  simp only [window, block, sub_mul, Finset.sum_sub_distrib]

/-- Exact finite-block recurrence, obtained from the existing convergent tail
recurrence rather than from a merely formal infinite-series manipulation. -/
theorem tail_block (c : ℕ → ℕ) (hg : ∀ n, c n ≤ n) (N L : ℕ) :
    binaryCoeffTail c (N + L) =
      (2 : ℝ) ^ L * binaryCoeffTail c N - (block c N L : ℝ) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [show N + (L + 1) = (N + L) + 1 by omega,
        binaryCoeffTail_succ c hg, ih, block_succ, pow_succ]
      push_cast
      ring

/-- The exact discrepancy leaves only two bounded nonnegative tails. -/
theorem window_metric_bound (c : ℕ → ℕ) (hg : ∀ n, c n ≤ n) (h N L : ℕ) :
    |(2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
        (window c h N L : ℝ)| ≤ (N : ℝ) + h + L + 2 := by
  have ht1 := tail_block c hg (N + h) L
  have ht2 := tail_block c hg N L
  have hlo1 := binaryCoeffTail_nonneg c (N + h + L)
  have hlo2 := binaryCoeffTail_nonneg c (N + L)
  have hhi1 := binaryCoeffTail_le c hg (N + h + L)
  have hhi2 := binaryCoeffTail_le c hg (N + L)
  have hid : (2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (window c h N L : ℝ) =
        binaryCoeffTail c (N + h + L) - binaryCoeffTail c (N + L) := by
    rw [window_eq_sub_blocks]
    push_cast
    linarith
  rw [hid, abs_le]
  push_cast at hhi1 hhi2
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  constructor <;> linarith

/-- Pure integer central-arc separation. This is independent of totients and
independent of the analytic proof of the bound. -/
theorem abs_sub_multiple_gt_of_central {A M B : ℤ} (hM : 0 < M)
    (hlow : B < A % M) (hhigh : A % M < M - B) (z : ℤ) :
    B < |A - z * M| := by
  by_contra hnot
  have habs := abs_le.mp (le_of_not_gt hnot)
  set x := A - z * M with hx
  have hxmod : x % M = A % M := by
    have hrw : x = A + M * (-z) := by rw [hx]; ring
    rw [hrw, Int.add_mul_emod_self_left]
  have hdm : M * (x / M) + A % M = x := by
    rw [← hxmod]
    exact Int.mul_ediv_add_emod x M
  by_cases ht : 0 ≤ x / M
  · have hge : 0 ≤ M * (x / M) := mul_nonneg hM.le ht
    change -B ≤ x ∧ x ≤ B at habs
    linarith
  · have ht1 : x / M ≤ -1 := by omega
    have hle : M * (x / M) ≤ M * (-1) := mul_le_mul_of_nonneg_left ht1 hM.le
    change -B ≤ x ∧ x ≤ B at habs
    linarith

/-- COMPLETE long-record lem:gsound, with the ambient growth hypothesis
explicit and with no change to the certificate radius. -/
theorem generic_soundness (c : ℕ → ℕ) (hg : ∀ n, c n ≤ n)
    {h N L : ℕ} (hkill : Kill c h N L) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  have hbound := window_metric_bound c hg h N L
  rw [← hz, abs_sub_comm] at hbound
  have hboundZ : |window c h N L - z * 2 ^ L| ≤ (N : ℤ) + h + L + 2 := by
    have hreal : |(window c h N L : ℝ) - (z : ℝ) * 2 ^ L| ≤
        (N : ℝ) + h + L + 2 := by simpa only [mul_comm] using hbound
    exact_mod_cast hreal
  exact (not_lt_of_ge hboundZ)
    (abs_sub_multiple_gt_of_central (by positivity) hkill.1 hkill.2 z)

/-- Generic digit-shift identity, also used by the rational period law. -/
theorem tail_eq_scaled_series_sub_block (c : ℕ → ℕ) (hg : ∀ n, c n ≤ n) (N : ℕ) :
    binaryCoeffTail c N = (2 : ℝ) ^ N * binaryCoeffSeries c - (block c 0 N : ℝ) := by
  simpa using tail_block c hg 0 N

/-- COMPLETE long-record lem:gperiod. Positivity of m and its Mersenne
divisibility are sufficient; oddness follows from that divisibility when
h>0 and does not need to be assumed again. The preperiod is exactly N>=e. -/
theorem generic_tail_period (c : ℕ → ℕ) (hg : ∀ n, c n ≤ n)
    (p : ℤ) (e m h N : ℕ) (hm : 0 < m) (heN : e ≤ N)
    (hdiv : m ∣ 2 ^ h - 1)
    (hseries : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * (m : ℝ))) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨a, ha⟩ := hdiv
  have hpow1 : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by norm_num)
  have haR : (2 : ℝ) ^ h - 1 = (m : ℝ) * (a : ℝ) := by
    have haCast : ((2 ^ h - 1 : ℕ) : ℝ) = ((m * a : ℕ) : ℝ) := by rw [ha]
    rw [Nat.cast_sub hpow1] at haCast
    push_cast at haCast
    exact haCast
  have hNp : (2 : ℝ) ^ N = (2 : ℝ) ^ e * 2 ^ (N - e) := by
    rw [← pow_add, Nat.add_sub_of_le heN]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hscale : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * binaryCoeffSeries c =
      ((2 ^ (N - e) : ℤ) * a * p : ℤ) := by
    rw [hseries, hNp, haR]
    push_cast
    field_simp [hmR] <;> ring
  refine ⟨(2 ^ (N - e) : ℤ) * a * p + block c 0 N - block c 0 (N + h), ?_⟩
  rw [tail_eq_scaled_series_sub_block c hg (N + h),
    tail_eq_scaled_series_sub_block c hg N, pow_add]
  push_cast at hscale ⊢
  nlinarith [hscale]

end ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates
