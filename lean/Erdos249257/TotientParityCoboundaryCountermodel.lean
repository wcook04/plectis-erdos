import Erdos249257.TotientTailPeriodKiller

/-!
# A parity-and-nonperiodicity countermodel for Erdős #249

Parity of Euler's totient is eventually trivial: `phi(n)` is even for every
`n >= 3`.  That fact, even together with nonnegativity, the linear bound, and
non-eventual-periodicity of the coefficient word, cannot force irrationality
at `1/2`.

This file constructs a bounded natural sequence `c` with

* `0 <= c(n) <= n`;
* `c(n) = phi(n) (mod 2)` for every `n`;
* `c` not eventually periodic;
* `sum c(n)/2^n = 3/2`.

Start with coefficients `0,1,1,2,4,4,...`.  At each lacunary rank
`m = 2^(k+3)`, replace the pair `(4,4)` at `(m,m+1)` by `(6,0)`.  Each change
is the exact binary coboundary

`2/2^m - 4/2^(m+1) = 0`,

so the value stays rational while the coefficient word becomes aperiodic.
This refutes route sufficiency only; it says nothing about the actual totient
value beyond identifying the extra arithmetic information a proof must use.
-/

namespace Erdos249257
namespace TotientParityCoboundaryCountermodel

open Filter

noncomputable section

/-- Lacunary spike ranks `2^(k+3)`, beginning at `8`. -/
def IsLargePowerTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 ^ (k + 3)

/-- The zero-one indicator of the lacunary spike ranks. -/
noncomputable def largePowerTwoBit (n : ℕ) : ℕ := by
  classical
  exact if IsLargePowerTwo n then 1 else 0

/-- Rational base coefficients before adding zero-valued sparse carries. -/
def parityBaseWeight : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 4

private theorem parityBaseWeight_eq_four_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    parityBaseWeight n = 4 := by
  rcases n with _ | _ | _ | _ | n <;> simp [parityBaseWeight] at hn ⊢

/-- The parity countermodel.  Natural subtraction is exact because every
negative spike lands on a base coefficient `4`. -/
noncomputable def parityCoboundaryWeight (n : ℕ) : ℕ :=
  parityBaseWeight n + 2 * largePowerTwoBit n -
    4 * largePowerTwoBit (n - 1)

@[simp] theorem largePowerTwoBit_pow (k : ℕ) :
    largePowerTwoBit (2 ^ (k + 3)) = 1 := by
  classical
  rw [largePowerTwoBit, if_pos]
  exact ⟨k, rfl⟩

theorem largePowerTwoBit_eq_zero_of_lt_eight {n : ℕ} (hn : n < 8) :
    largePowerTwoBit n = 0 := by
  classical
  rw [largePowerTwoBit, if_neg]
  rintro ⟨k, rfl⟩
  have h8 : 8 ≤ 2 ^ (k + 3) := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  omega

theorem not_isLargePowerTwo_of_between {k n : ℕ}
    (hlow : 2 ^ (k + 3) < n) (hhigh : n < 2 ^ (k + 4)) :
    ¬ IsLargePowerTwo n := by
  rintro ⟨j, rfl⟩
  by_cases hj : j ≤ k
  · have hp : 2 ^ (j + 3) ≤ 2 ^ (k + 3) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (Nat.add_le_add_right hj 3)
    exact (not_lt_of_ge hp) hlow
  · have hkj : k + 1 ≤ j := by omega
    have hp : 2 ^ (k + 4) ≤ 2 ^ (j + 3) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    exact (not_lt_of_ge hp) hhigh

theorem largePowerTwoBit_eq_zero_of_between {k n : ℕ}
    (hlow : 2 ^ (k + 3) < n) (hhigh : n < 2 ^ (k + 4)) :
    largePowerTwoBit n = 0 := by
  classical
  simp [largePowerTwoBit, not_isLargePowerTwo_of_between hlow hhigh]

theorem largePowerTwoBit_le_one (n : ℕ) : largePowerTwoBit n ≤ 1 := by
  classical
  unfold largePowerTwoBit
  split <;> omega

private theorem largePowerTwoBit_pred_forces_base_four {n : ℕ}
    (hpred : largePowerTwoBit (n - 1) = 1) :
    parityBaseWeight n = 4 ∧ largePowerTwoBit n = 0 := by
  have hlarge : IsLargePowerTwo (n - 1) := by
    classical
    by_contra h
    simp [largePowerTwoBit, h] at hpred
  obtain ⟨k, hk⟩ := hlarge
  have hpow : n - 1 = 2 ^ (k + 3) := hk
  have hpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hpowPos : 0 < 2 ^ (k + 3) := pow_pos (by norm_num) _
    omega
  have hn : n = 2 ^ (k + 3) + 1 := by omega
  have h8 : 8 ≤ 2 ^ (k + 3) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbetweenLow : 2 ^ (k + 3) < n := by omega
  have hbetweenHigh : n < 2 ^ (k + 4) := by
    rw [show k + 4 = (k + 3) + 1 by omega, pow_succ]
    omega
  constructor
  · exact parityBaseWeight_eq_four_of_four_le (by omega)
  · exact largePowerTwoBit_eq_zero_of_between hbetweenLow hbetweenHigh

/-- The natural subtraction in the definition is genuine integer
subtraction; this is the algebraic coboundary normal form. -/
theorem parityCoboundaryWeight_cast (n : ℕ) :
    (parityCoboundaryWeight n : ℤ) =
      (parityBaseWeight n : ℤ) + 2 * largePowerTwoBit n -
        4 * largePowerTwoBit (n - 1) := by
  unfold parityCoboundaryWeight
  rw [Nat.cast_sub]
  · push_cast
    rfl
  · by_cases hpred : largePowerTwoBit (n - 1) = 1
    · obtain ⟨hbase, hcur⟩ := largePowerTwoBit_pred_forces_base_four hpred
      rw [hpred, hbase, hcur]
    · have hpred0 : largePowerTwoBit (n - 1) = 0 := by
        have hle := largePowerTwoBit_le_one (n - 1)
        omega
      rw [hpred0]
      simp

theorem parityCoboundaryWeight_nonneg (n : ℕ) :
    0 ≤ parityCoboundaryWeight n := Nat.zero_le _

theorem parityCoboundaryWeight_le_self (n : ℕ) :
    parityCoboundaryWeight n ≤ n := by
  by_cases hsmall : n < 4
  · interval_cases n <;>
      norm_num [parityCoboundaryWeight, parityBaseWeight,
        largePowerTwoBit_eq_zero_of_lt_eight]
  · have hn4 : 4 ≤ n := by omega
    by_cases hpred : largePowerTwoBit (n - 1) = 1
    · obtain ⟨hbase, hcur⟩ := largePowerTwoBit_pred_forces_base_four hpred
      simp [parityCoboundaryWeight, hpred, hbase, hcur]
    · have hpred0 : largePowerTwoBit (n - 1) = 0 := by
        have hle := largePowerTwoBit_le_one (n - 1)
        omega
      by_cases hcur : largePowerTwoBit n = 1
      · have hlarge : IsLargePowerTwo n := by
          classical
          by_contra h
          simp [largePowerTwoBit, h] at hcur
        obtain ⟨k, rfl⟩ := hlarge
        have h8 : 8 ≤ 2 ^ (k + 3) := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [parityCoboundaryWeight, parityBaseWeight_eq_four_of_four_le (by omega),
          hpred0, hcur]
        norm_num
        omega
      · have hcur0 : largePowerTwoBit n = 0 := by
          have hle := largePowerTwoBit_le_one n
          omega
        rw [parityCoboundaryWeight, parityBaseWeight_eq_four_of_four_le hn4,
          hpred0, hcur0]
        norm_num
        omega

private theorem totient_even_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    Even (Nat.totient n) := by
  exact Nat.totient_even (by omega)

/-- Exact parity agreement with Euler's totient. -/
theorem parityCoboundaryWeight_mod_two_eq_totient (n : ℕ) :
    parityCoboundaryWeight n % 2 = Nat.totient n % 2 := by
  by_cases hsmall : n < 3
  · interval_cases n <;>
      norm_num [parityCoboundaryWeight, parityBaseWeight,
        largePowerTwoBit_eq_zero_of_lt_eight]
  · have hn : 3 ≤ n := by omega
    have hphi := totient_even_of_three_le hn
    have hbit1 : Even (2 * largePowerTwoBit n) := even_two_mul _
    have hbase : Even (parityBaseWeight n) := by
      by_cases hn3 : n = 3
      · subst n
        norm_num [parityBaseWeight]
      · have hn4 : 4 ≤ n := by omega
        rw [parityBaseWeight_eq_four_of_four_le hn4]
        exact ⟨2, by norm_num⟩
    have hweight : Even (parityCoboundaryWeight n) := by
      by_cases hpred : largePowerTwoBit (n - 1) = 1
      · obtain ⟨hbase4, hcur⟩ := largePowerTwoBit_pred_forces_base_four hpred
        simp [parityCoboundaryWeight, hpred, hbase4, hcur]
      · have hpred0 : largePowerTwoBit (n - 1) = 0 := by
          have hle := largePowerTwoBit_le_one (n - 1)
          omega
        simp only [parityCoboundaryWeight, hpred0, mul_zero, Nat.sub_zero]
        exact hbase.add hbit1
    rw [Nat.even_iff.mp hweight, Nat.even_iff.mp hphi]

private theorem parityBaseWeight_le_four (n : ℕ) : parityBaseWeight n ≤ 4 := by
  rcases n with _ | _ | _ | _ | n <;> simp [parityBaseWeight]

/-- The countermodel uses only the six coefficient values below `7`.  Thus
finite-valuedness alone does not repair the parity-and-aperiodicity route;
one needs a digit/no-carry constraint or genuinely arithmetic information. -/
theorem parityCoboundaryWeight_le_six (n : ℕ) :
    parityCoboundaryWeight n ≤ 6 := by
  unfold parityCoboundaryWeight
  have hbase := parityBaseWeight_le_four n
  have hbit := largePowerTwoBit_le_one n
  omega

/-- Every lacunary spike really attains the upper value six.  Together with
`parityCoboundaryWeight_pow_succ`, this exposes the nonperiodic `6,0` carry
markers directly, rather than hiding them behind the uniform bound. -/
theorem parityCoboundaryWeight_pow (k : ℕ) :
    parityCoboundaryWeight (2 ^ (k + 3)) = 6 := by
  have hcur : largePowerTwoBit (2 ^ (k + 3)) = 1 :=
    largePowerTwoBit_pow k
  have hpred : largePowerTwoBit (2 ^ (k + 3) - 1) = 0 := by
    by_cases h : largePowerTwoBit (2 ^ (k + 3) - 1) = 1
    · have hnext :=
        (largePowerTwoBit_pred_forces_base_four (n := 2 ^ (k + 3)) h).2
      omega
    · have hle := largePowerTwoBit_le_one (2 ^ (k + 3) - 1)
      omega
  have hbase : parityBaseWeight (2 ^ (k + 3)) = 4 := by
    apply parityBaseWeight_eq_four_of_four_le
    calc
      4 ≤ 8 := by norm_num
      _ = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  simp [parityCoboundaryWeight, hbase, hcur, hpred]

private theorem summable_parityBaseWeight :
    Summable (fun n : ℕ => (parityBaseWeight n : ℝ) / 2 ^ n) := by
  have hgeo : Summable (fun n : ℕ => 4 * ((1 : ℝ) / 2) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  have hweight : (parityBaseWeight n : ℝ) ≤ 4 := by
    exact_mod_cast parityBaseWeight_le_four n
  calc
    (parityBaseWeight n : ℝ) / 2 ^ n ≤ 4 / 2 ^ n :=
      div_le_div_of_nonneg_right hweight (by positivity)
    _ = 4 * ((1 : ℝ) / 2) ^ n := by
      rw [div_pow, one_pow]
      ring

private theorem tsum_parityBaseWeight :
    (∑' n : ℕ, (parityBaseWeight n : ℝ) / 2 ^ n) = 3 / 2 := by
  have hsplit := summable_parityBaseWeight.sum_add_tsum_nat_add 4
  rw [← hsplit]
  have htail :
      (∑' n : ℕ, (parityBaseWeight (n + 4) : ℝ) / 2 ^ (n + 4)) = 1 / 2 := by
    calc
      (∑' n : ℕ, (parityBaseWeight (n + 4) : ℝ) / 2 ^ (n + 4)) =
          ∑' n : ℕ, (1 / 4 : ℝ) * ((1 : ℝ) / 2) ^ n := by
            apply tsum_congr
            intro n
            rw [parityBaseWeight_eq_four_of_four_le (by omega), pow_add, div_pow, one_pow]
            norm_num
            ring
      _ = (1 / 4 : ℝ) * ∑' n : ℕ, ((1 : ℝ) / 2) ^ n := tsum_mul_left
      _ = 1 / 2 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
  rw [htail]
  norm_num [Finset.sum_range_succ, parityBaseWeight]

private theorem summable_largePowerTwoBit :
    Summable (fun n : ℕ => (largePowerTwoBit n : ℝ) / 2 ^ n) := by
  have hgeo : Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  rw [div_pow, one_pow]
  gcongr
  exact_mod_cast largePowerTwoBit_le_one n

private theorem summable_shiftedLargePowerTwoBit :
    Summable (fun n : ℕ => (largePowerTwoBit (n - 1) : ℝ) / 2 ^ n) := by
  rw [← summable_nat_add_iff 1]
  refine (summable_largePowerTwoBit.mul_left (1 / 2 : ℝ)).congr (fun n => ?_)
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

private theorem tsum_sparse_coboundary_zero :
    (∑' n : ℕ,
      (2 * (largePowerTwoBit n : ℝ) -
        4 * largePowerTwoBit (n - 1)) / 2 ^ n) = 0 := by
  have hpos := summable_largePowerTwoBit.mul_left (2 : ℝ)
  have hneg := summable_shiftedLargePowerTwoBit.mul_left (4 : ℝ)
  have hpos' : Summable (fun n : ℕ => 2 * (largePowerTwoBit n : ℝ) / 2 ^ n) :=
    hpos.congr (fun n => by ring)
  have hneg' : Summable (fun n : ℕ => 4 * (largePowerTwoBit (n - 1) : ℝ) / 2 ^ n) :=
    hneg.congr (fun n => by ring)
  have hshift :
      (∑' n : ℕ, 4 * (largePowerTwoBit (n - 1) : ℝ) / 2 ^ n) =
        ∑' n : ℕ, 2 * (largePowerTwoBit n : ℝ) / 2 ^ n := by
    rw [hneg'.tsum_eq_zero_add]
    simp only [Nat.zero_sub, pow_zero, div_one]
    have hbit0 : largePowerTwoBit 0 = 0 :=
      largePowerTwoBit_eq_zero_of_lt_eight (by norm_num)
    rw [hbit0]
    simp only [Nat.cast_zero, mul_zero, zero_add, Nat.add_sub_cancel, pow_succ]
    apply tsum_congr
    intro n
    ring
  calc
    (∑' n : ℕ,
        (2 * (largePowerTwoBit n : ℝ) -
          4 * largePowerTwoBit (n - 1)) / 2 ^ n) =
        (∑' n : ℕ, 2 * (largePowerTwoBit n : ℝ) / 2 ^ n) -
          ∑' n : ℕ, 4 * (largePowerTwoBit (n - 1) : ℝ) / 2 ^ n := by
            rw [← hpos'.tsum_sub hneg']
            apply tsum_congr
            intro n
            ring
    _ = 0 := by rw [hshift]; ring

private theorem summable_parityCoboundaryWeight :
    Summable (fun n : ℕ => (parityCoboundaryWeight n : ℝ) / 2 ^ n) := by
  have hsparse : Summable (fun n : ℕ =>
      (2 * (largePowerTwoBit n : ℝ) -
        4 * largePowerTwoBit (n - 1)) / 2 ^ n) := by
    refine ((summable_largePowerTwoBit.mul_left (2 : ℝ)).sub
      (summable_shiftedLargePowerTwoBit.mul_left (4 : ℝ))).congr ?_
    intro n
    ring
  refine (summable_parityBaseWeight.add hsparse).congr (fun n => ?_)
  symm
  rw [← Int.cast_natCast, parityCoboundaryWeight_cast]
  push_cast
  ring

/-- Despite parity agreement, linear bounds, and sparse aperiodicity, the
countermodel has the rational dyadic value `3/2`. -/
theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2 := by
  have hsparse : Summable (fun n : ℕ =>
      (2 * (largePowerTwoBit n : ℝ) -
        4 * largePowerTwoBit (n - 1)) / 2 ^ n) := by
    refine ((summable_largePowerTwoBit.mul_left (2 : ℝ)).sub
      (summable_shiftedLargePowerTwoBit.mul_left (4 : ℝ))).congr ?_
    intro n
    ring
  calc
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) =
        (∑' n : ℕ, (parityBaseWeight n : ℝ) / 2 ^ n) +
          ∑' n : ℕ,
            (2 * (largePowerTwoBit n : ℝ) -
              4 * largePowerTwoBit (n - 1)) / 2 ^ n := by
          rw [← summable_parityBaseWeight.tsum_add hsparse]
          apply tsum_congr
          intro n
          rw [← Int.cast_natCast, parityCoboundaryWeight_cast]
          push_cast
          ring
    _ = 3 / 2 := by rw [tsum_parityBaseWeight, tsum_sparse_coboundary_zero, add_zero]

theorem parityCoboundaryWeight_pow_succ (k : ℕ) :
    parityCoboundaryWeight (2 ^ (k + 3) + 1) = 0 := by
  have hlow : 2 ^ (k + 3) < 2 ^ (k + 3) + 1 := by omega
  have hhigh : 2 ^ (k + 3) + 1 < 2 ^ (k + 4) := by
    have hp : 1 < 2 ^ (k + 3) := by
      exact one_lt_pow₀ (by norm_num) (by omega)
    calc
      2 ^ (k + 3) + 1 < 2 ^ (k + 3) + 2 ^ (k + 3) :=
        Nat.add_lt_add_left hp _
      _ = 2 ^ (k + 4) := by
        rw [show k + 4 = (k + 3) + 1 by omega, pow_succ]
        ring
  have hcur := largePowerTwoBit_eq_zero_of_between hlow hhigh
  have hbase : parityBaseWeight (2 ^ (k + 3) + 1) = 4 := by
    exact parityBaseWeight_eq_four_of_four_le (by
      have h8 : 8 ≤ 2 ^ (k + 3) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
  simp [parityCoboundaryWeight, hcur, hbase]

/-- The explicit `6,0` carry markers occur cofinally, not just at a named
lacunary sequence.  This is the cutoff-shaped interface used by arguments
that would otherwise have to unpack the powers-of-two witness themselves. -/
theorem exists_later_parityCoboundaryWeight_carry_pair (N : ℕ) :
    ∃ n : ℕ,
      N < n ∧
      parityCoboundaryWeight n = 6 ∧
      parityCoboundaryWeight (n + 1) = 0 := by
  refine ⟨2 ^ (N + 3), ?_, parityCoboundaryWeight_pow N,
    parityCoboundaryWeight_pow_succ N⟩
  have hpow : N < 2 ^ N := Nat.lt_two_pow_self
  exact hpow.trans_le
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))

/-- Two visible carry pairs can be found beyond any cutoff with any prescribed
gap between them.  Thus the rational countermodel retains arbitrarily sparse,
cofinally recurring carry markers. -/
theorem exists_later_separated_parityCoboundaryWeight_carry_pairs
    (N G : ℕ) :
    ∃ n m : ℕ,
      N < n ∧ n + G < m ∧
      parityCoboundaryWeight n = 6 ∧
      parityCoboundaryWeight (n + 1) = 0 ∧
      parityCoboundaryWeight m = 6 ∧
      parityCoboundaryWeight (m + 1) = 0 := by
  let k := N + G
  let n := 2 ^ (k + 3)
  let m := 2 ^ (k + 4)
  have hkpow : k < 2 ^ k := Nat.lt_two_pow_self
  have hpown : 2 ^ k ≤ n := by
    dsimp [n]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hNn : N < n := by
    exact (show N ≤ k by dsimp [k]; omega).trans_lt (hkpow.trans_le hpown)
  have hGn : G < n := by
    exact (show G ≤ k by dsimp [k]; omega).trans_lt (hkpow.trans_le hpown)
  have hm : m = n + n := by
    dsimp [m, n]
    rw [show k + 4 = (k + 3) + 1 by omega, pow_succ]
    ring
  have hnm : n + G < m := by
    rw [hm]
    exact Nat.add_lt_add_left hGn n
  have hkSuccExp : k + 1 + 3 = k + 4 := by omega
  refine ⟨n, m, hNn, hnm, ?_, ?_, ?_, ?_⟩
  · simpa [n] using parityCoboundaryWeight_pow k
  · simpa [n] using parityCoboundaryWeight_pow_succ k
  · simpa [m, hkSuccExp] using parityCoboundaryWeight_pow (k + 1)
  · simpa [m, hkSuccExp] using parityCoboundaryWeight_pow_succ (k + 1)

/-- Beyond every cutoff, the rational witness contains arbitrarily long
blocks of visible carry pairs with a prescribed gap between consecutive
markers.  The block uses consecutive powers of two; the base exponent is
chosen far enough out that every doubling clears the requested gap. -/
theorem exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs
    (N G K : ℕ) :
    ∃ k : ℕ,
      N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        parityCoboundaryWeight (2 ^ (k + i + 3)) = 6 ∧
        parityCoboundaryWeight (2 ^ (k + i + 3) + 1) = 0 := by
  let k := N + G
  have hkpow : k < 2 ^ k := Nat.lt_two_pow_self
  have hbase : 2 ^ k ≤ 2 ^ (k + 3) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  refine ⟨k, (show N ≤ k by dsimp [k]; omega).trans_lt
      (hkpow.trans_le hbase), ?_⟩
  intro i _hi
  have hscale : 2 ^ k ≤ 2 ^ (k + i + 3) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hgap : G < 2 ^ (k + i + 3) := by
    exact (show G ≤ k by dsimp [k]; omega).trans_lt
      (hkpow.trans_le hscale)
  have hdouble :
      2 ^ (k + i + 4) = 2 ^ (k + i + 3) + 2 ^ (k + i + 3) := by
    rw [show k + i + 4 = (k + i + 3) + 1 by omega, pow_succ]
    ring
  refine ⟨?_, parityCoboundaryWeight_pow (k + i),
    parityCoboundaryWeight_pow_succ (k + i)⟩
  rw [hdouble]
  exact Nat.add_lt_add_left hgap _

/-- The coefficient word is not eventually periodic. -/
theorem parityCoboundaryWeight_not_eventually_periodic :
    ¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n →
      parityCoboundaryWeight (n + p) = parityCoboundaryWeight n := by
  rintro ⟨p, N, hp, hperiod⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max N (p + 2))
    (by norm_num : (1 : ℕ) < 2)
  let M := 2 ^ (k + 3)
  have hNM : N ≤ M + 1 := by
    dsimp [M]
    have hpow : 2 ^ k ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpM : p + 1 < M := by
    dsimp [M]
    have hpow : 2 ^ k ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hzero : parityCoboundaryWeight (M + 1) = 0 := by
    simpa [M] using parityCoboundaryWeight_pow_succ k
  have hxlow : M < M + 1 + p := by omega
  have hxhigh : M + 1 + p < 2 * M := by omega
  have hpredlow : M < (M + 1 + p) - 1 := by omega
  have hpredhigh : (M + 1 + p) - 1 < 2 * M := by omega
  have htwoM : 2 * M = 2 ^ (k + 4) := by
    dsimp [M]
    rw [show k + 4 = (k + 3) + 1 by omega, pow_succ]
    ring
  have hcurBit : largePowerTwoBit (M + 1 + p) = 0 := by
    apply largePowerTwoBit_eq_zero_of_between (k := k)
    · simpa [M] using hxlow
    · rw [← htwoM]
      exact hxhigh
  have hpredBit : largePowerTwoBit ((M + 1 + p) - 1) = 0 := by
    apply largePowerTwoBit_eq_zero_of_between (k := k)
    · simpa [M] using hpredlow
    · rw [← htwoM]
      exact hpredhigh
  have hbase : parityBaseWeight (M + 1 + p) = 4 := by
    have hM8 : 8 ≤ M := by
      dsimp [M]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact parityBaseWeight_eq_four_of_four_le (by omega)
  have hfour : parityCoboundaryWeight (M + 1 + p) = 4 := by
    have hpredBit' : largePowerTwoBit (M + p) = 0 := by
      apply largePowerTwoBit_eq_zero_of_between (k := k)
      · dsimp [M]
        omega
      · rw [← htwoM]
        omega
    simp [parityCoboundaryWeight, hcurBit, hpredBit', hbase]
  have hper := hperiod (M + 1) hNM
  rw [hzero, hfour] at hper
  norm_num at hper

/-- The countermodel's dyadic value is rational. -/
theorem parityCoboundaryWeight_not_irrational :
    ¬ Irrational
      (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) := by
  intro hirr
  apply hirr.ne_rational 3 2
  rw [tsum_parityCoboundaryWeight_eq_three_halves]
  norm_num

/-- **Route-pruning theorem for Erdős #249.**  Uniform finite-valuedness,
natural-valued linear growth, exact agreement with the totient coefficients
modulo two, and failure of eventual periodicity do not by themselves force
irrationality of a binary coefficient series.  The witness is explicit,
bounded by six, and has value `3/2`.

This theorem rules out only that proof interface; it makes no claim about the
actual totient series. -/
theorem exists_totientParity_linear_aperiodic_rational_countermodel :
    ∃ c : ℕ → ℕ,
      (∀ n, c n ≤ 6) ∧
      (∀ n, c n ≤ n) ∧
      (∀ n, c n % 2 = Nat.totient n % 2) ∧
      (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n) ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  exact ⟨parityCoboundaryWeight,
    parityCoboundaryWeight_le_six,
    parityCoboundaryWeight_le_self,
    parityCoboundaryWeight_mod_two_eq_totient,
    parityCoboundaryWeight_not_eventually_periodic,
    parityCoboundaryWeight_not_irrational⟩

/-- The route-pruning witness can be chosen with explicit lacunary binary
carry pairs: every spike coefficient is six and its successor is zero.  Thus
the rationality mechanism survives even after the nonperiodicity witness is
made completely visible in the theorem statement. -/
theorem exists_totientParity_explicitCarry_rational_countermodel :
    ∃ c : ℕ → ℕ,
      (∀ k, c (2 ^ (k + 3)) = 6 ∧ c (2 ^ (k + 3) + 1) = 0) ∧
      (∀ n, c n ≤ 6) ∧
      (∀ n, c n ≤ n) ∧
      (∀ n, c n % 2 = Nat.totient n % 2) ∧
      (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n) ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  exact ⟨parityCoboundaryWeight,
    fun k ↦ ⟨parityCoboundaryWeight_pow k,
      parityCoboundaryWeight_pow_succ k⟩,
    parityCoboundaryWeight_le_six,
    parityCoboundaryWeight_le_self,
    parityCoboundaryWeight_mod_two_eq_totient,
    parityCoboundaryWeight_not_eventually_periodic,
    parityCoboundaryWeight_not_irrational⟩

/-- The same rational countermodel has a visible `6,0` carry pair beyond
every cutoff.  Hence even cofinally recurring, unboundedly located carry
markers do not rescue the parity-plus-aperiodicity irrationality route. -/
theorem exists_totientParity_cofinalCarry_rational_countermodel :
    ∃ c : ℕ → ℕ,
      (∀ N, ∃ n, N < n ∧ c n = 6 ∧ c (n + 1) = 0) ∧
      (∀ n, c n ≤ 6) ∧
      (∀ n, c n ≤ n) ∧
      (∀ n, c n % 2 = Nat.totient n % 2) ∧
      (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n) ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  exact ⟨parityCoboundaryWeight,
    exists_later_parityCoboundaryWeight_carry_pair,
    parityCoboundaryWeight_le_six,
    parityCoboundaryWeight_le_self,
    parityCoboundaryWeight_mod_two_eq_totient,
    parityCoboundaryWeight_not_eventually_periodic,
    parityCoboundaryWeight_not_irrational⟩

/-- Even cofinal carry pairs with arbitrarily large prescribed separation do
not rescue the parity-and-aperiodicity route: the witness remains bounded,
linearly dominated, nonperiodic, and rational-valued. -/
theorem exists_totientParity_separatedCarry_rational_countermodel :
    ∃ c : ℕ → ℕ,
      (∀ N G, ∃ n m,
        N < n ∧ n + G < m ∧
        c n = 6 ∧ c (n + 1) = 0 ∧
        c m = 6 ∧ c (m + 1) = 0) ∧
      (∀ n, c n ≤ 6) ∧
      (∀ n, c n ≤ n) ∧
      (∀ n, c n % 2 = Nat.totient n % 2) ∧
      (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n) ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  exact ⟨parityCoboundaryWeight,
    exists_later_separated_parityCoboundaryWeight_carry_pairs,
    parityCoboundaryWeight_le_six,
    parityCoboundaryWeight_le_self,
    parityCoboundaryWeight_mod_two_eq_totient,
    parityCoboundaryWeight_not_eventually_periodic,
    parityCoboundaryWeight_not_irrational⟩

/-- Arbitrarily many cofinally located and uniformly separated carry markers
still do not rescue the parity-and-aperiodicity route.  For every requested
block length, the same bounded natural-valued witness supplies that entire
block while its binary series remains the rational number `3/2`. -/
theorem exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel :
    ∃ c : ℕ → ℕ,
      (∀ N G K, ∃ k,
        N < 2 ^ (k + 3) ∧
        ∀ i : ℕ, i < K →
          2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
          c (2 ^ (k + i + 3)) = 6 ∧
          c (2 ^ (k + i + 3) + 1) = 0) ∧
      (∀ n, c n ≤ 6) ∧
      (∀ n, c n ≤ n) ∧
      (∀ n, c n % 2 = Nat.totient n % 2) ∧
      (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n) ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  exact ⟨parityCoboundaryWeight,
    exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs,
    parityCoboundaryWeight_le_six,
    parityCoboundaryWeight_le_self,
    parityCoboundaryWeight_mod_two_eq_totient,
    parityCoboundaryWeight_not_eventually_periodic,
    parityCoboundaryWeight_not_irrational⟩

#print axioms parityCoboundaryWeight_mod_two_eq_totient
#print axioms parityCoboundaryWeight_le_self
#print axioms parityCoboundaryWeight_le_six
#print axioms parityCoboundaryWeight_pow
#print axioms parityCoboundaryWeight_pow_succ
#print axioms exists_later_parityCoboundaryWeight_carry_pair
#print axioms exists_later_separated_parityCoboundaryWeight_carry_pairs
#print axioms exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs
#print axioms tsum_parityCoboundaryWeight_eq_three_halves
#print axioms parityCoboundaryWeight_not_eventually_periodic
#print axioms parityCoboundaryWeight_not_irrational
#print axioms exists_totientParity_linear_aperiodic_rational_countermodel
#print axioms exists_totientParity_explicitCarry_rational_countermodel
#print axioms exists_totientParity_cofinalCarry_rational_countermodel
#print axioms exists_totientParity_separatedCarry_rational_countermodel
#print axioms exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel

end
end TotientParityCoboundaryCountermodel
end Erdos249257
