import ErdosProblems.Erdos68.ChannelIntegralCongruence
import ErdosProblems.Erdos68.PolynomialPerturbationLcm

/-!
# Exact quotient-gcd and logarithmic segment statements

Long-record labels res:gap-gcd and res:segment. The supplied library has the
integer product inequality, not the displayed sum of logarithms. Both the
quotient/descending-factorial bridge and the log-sum bridge are explicit here.
STATUS: uncompiled proof candidates. No placeholders or new assumptions.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators

lemma factorial_div_eq_descFactorial {i j : ℕ} (hij : i ≤ j) :
    j.factorial / i.factorial = j.descFactorial (j - i) := by
  have hprod : i.factorial * j.descFactorial (j - i) = j.factorial := by
    simpa only [Nat.sub_sub_self hij] using
      Nat.factorial_mul_descFactorial (Nat.sub_le j i)
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos i)
  calc
    i.factorial * (j.factorial / i.factorial) = j.factorial :=
      Nat.mul_div_cancel' (Nat.factorial_dvd_factorial hij)
    _ = i.factorial * j.descFactorial (j - i) := hprod.symm

/-- All three conclusions of res:gap-gcd, including the STRICT final bound. -/
theorem factorial_gap_gcd {i j : ℕ} (hi : 2 ≤ i) (hij : i < j) :
    Nat.gcd (i.factorial - 1) (j.factorial - 1) ∣
        j.factorial / i.factorial - 1 ∧
    Nat.gcd (i.factorial - 1) (j.factorial - 1) ≤
        j.factorial / i.factorial - 1 ∧
    j.factorial / i.factorial - 1 < j ^ (j - i) := by
  rw [factorial_div_eq_descFactorial hij.le]
  have hpos : 0 < j.descFactorial (j - i) :=
    Nat.descFactorial_pos.mpr (Nat.sub_le j i)
  have hge : j ≤ j.descFactorial (j - i) :=
    Nat.le_of_dvd hpos (_root_.Erdos68.dvd_descFactorial_of_pos
      (Nat.sub_pos_of_lt hij) (Nat.sub_le j i))
  have hsubpos : 0 < j.descFactorial (j - i) - 1 := by omega
  have hdiv := _root_.Erdos68.gcd_factorial_sub_one_dvd_descFactorial_sub_one hij
  refine ⟨hdiv, Nat.le_of_dvd hsubpos hdiv, ?_⟩
  exact (Nat.sub_lt hpos (by decide : 0 < (1 : ℕ))).trans_le
    (Nat.descFactorial_le_pow j (j - i))

/-- Exact log-product expansion, using a proved interval identity rather than
assuming that the recursive list has already been identified with a finset. -/
lemma log_factorialGapFrom_prod (k m : ℕ) (hm : 2 ≤ m) :
    Real.log ((_root_.Erdos68.factorialGapFrom m k).prod : ℝ) =
      ∑ n ∈ Finset.Ico m (m + k), Real.log ((n.factorial - 1 : ℕ) : ℝ) := by
  classical
  induction k generalizing m with
  | zero => simp [_root_.Erdos68.factorialGapFrom]
  | succ k ih =>
    have hgap : ((m.factorial - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hm)).ne'
    have htail : ((_root_.Erdos68.factorialGapFrom (m + 1) k).prod : ℝ) ≠ 0 := by
      exact_mod_cast (_root_.Erdos68.factorialGapFrom_prod_pos
        (m := m + 1) (k := k) (by omega)).ne'
    have hset : Finset.Ico m (m + (k + 1)) =
        insert m (Finset.Ico (m + 1) ((m + 1) + k)) := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnot : m ∉ Finset.Ico (m + 1) ((m + 1) + k) := by
      simp only [Finset.mem_Ico]
      omega
    rw [_root_.Erdos68.factorialGapFrom, List.prod_cons, Nat.cast_mul,
      Real.log_mul hgap htail, ih (m + 1) (by omega),
      hset, Finset.sum_insert hnot]

/-- Whole long-record res:segment with its printed finite interval and constant. -/
theorem segment_inequality {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N - 1) :
    (∑ n ∈ Finset.Icc (N - k + 1) N,
        Real.log ((n.factorial - 1 : ℕ) : ℝ)) ≤
      Real.log (_root_.Erdos68.channelLCM N : ℝ) +
        ((k + 1).choose 3 : ℝ) * Real.log (N : ℝ) := by
  classical
  have hklt : k < N := by omega
  have hm : 2 ≤ N + 1 - k := by omega
  have hprodpos : (0 : ℝ) < (_root_.Erdos68.factorialGapSegment N k).prod := by
    exact_mod_cast (_root_.Erdos68.factorialGapFrom_prod_pos
      (m := N + 1 - k) (k := k) hm)
  have hbound : ((_root_.Erdos68.factorialGapSegment N k).prod : ℝ) ≤
      (_root_.Erdos68.channelLCM N : ℝ) * (N : ℝ) ^ ((k + 1).choose 3) := by
    exact_mod_cast _root_.Erdos68.factorialGapSegment_prod_le_channelLCM_mul_pow_choose hklt
  have hL : (_root_.Erdos68.channelLCM N : ℝ) ≠ 0 := by
    exact_mod_cast (_root_.Erdos68.channelLCM_pos N).ne'
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlog := Real.log_le_log hprodpos hbound
  rw [Real.log_mul hL (pow_ne_zero _ hN), Real.log_pow] at hlog
  have hset : Finset.Ico (N + 1 - k) (N + 1 - k + k) =
      Finset.Icc (N - k + 1) N := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hleft := log_factorialGapFrom_prod k (N + 1 - k) hm
  rw [hset] at hleft
  change Real.log ((_root_.Erdos68.factorialGapFrom (N + 1 - k) k).prod : ℝ) ≤ _ at hlog
  rwa [hleft] at hlog

end ErdosProblems.Erdos68.PaperComplete
