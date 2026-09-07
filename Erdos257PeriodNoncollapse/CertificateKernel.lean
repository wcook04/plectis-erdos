import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Erdos257PeriodNoncollapse.GapFareyBound
import Erdos257PeriodNoncollapse.MersenneLambertLadder
import Erdos257PeriodNoncollapse.GeometricCoprimality
import Erdos257PeriodNoncollapse.GcdMomentCalculus
import Erdos257PeriodNoncollapse.SternBrocotRunGeometry
import Erdos257PeriodNoncollapse.TotientTailPeriodKiller
import Erdos257PeriodNoncollapse.CarrySurvivorExtinction
import Erdos257PeriodNoncollapse.LcmDiagonalReduction
import Erdos257PeriodNoncollapse.LcmConeFlatness
import Erdos257PeriodNoncollapse.LcmConeNonflat

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos257PeriodNoncollapse

theorem no_prime_drop_implies_eq
    (d L : Nat)
    (hLpos : 0 < L)
    (h_dvd : d ∣ L)
    (h_no_drop : ∀ p, Nat.Prime p → p ∣ L → ¬ d ∣ L / p) :
    d = L := by
  rcases h_dvd with ⟨k, rfl⟩
  by_cases hk : k = 1
  · simp [hk]
  have hk_pos : 0 < k := by
    by_contra hk_nonpos
    have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk_nonpos
    simp [hk_zero] at hLpos
  obtain ⟨p, hp_prime, hp_dvd_k⟩ := Nat.exists_prime_and_dvd hk
  have hp_dvd_L : p ∣ d * k := dvd_mul_of_dvd_right hp_dvd_k d
  have hdvd_drop : d ∣ d * k / p := by
    rcases hp_dvd_k with ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    rw [mul_comm p m, ← mul_assoc]
    exact Nat.mul_div_left _ hp_prime.pos
  exfalso
  exact (h_no_drop p hp_prime hp_dvd_L) hdvd_drop

theorem valuation_deficit_blocks_dvd
    {q M A : Nat}
    (_hq : Nat.Prime q)
    (hM : M ≠ 0)
    (hA : A ≠ 0)
    (hdef : M.factorization q > A.factorization q) :
    ¬ M ∣ A := by
  intro hdiv
  have hle : M.factorization q ≤ A.factorization q :=
    (Nat.factorization_le_iff_dvd hM hA).2 hdiv q
  exact Nat.not_lt_of_ge hle hdef

theorem factorization_le_of_dvd_ne_zero
    {q a b : Nat}
    (hb : b ≠ 0)
    (hab : a ∣ b) :
    a.factorization q ≤ b.factorization q := by
  have ha : a ≠ 0 := by
    intro ha
    rcases hab with ⟨c, hc⟩
    apply hb
    rw [hc, ha, zero_mul]
  exact (Nat.factorization_le_iff_dvd ha hb).2 hab q

theorem valuation_witnesses_imply_no_prime_drop
    (d L A : Nat)
    (M q : Nat → Nat)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_dvd : d ∣ L)
    (h_collapse_if_drop :
      ∀ p, Nat.Prime p → p ∣ L → d ∣ L / p → M p ∣ A)
    (h_q_prime :
      ∀ p, Nat.Prime p → p ∣ L → Nat.Prime (q p))
    (h_M_ne_zero :
      ∀ p, Nat.Prime p → p ∣ L → M p ≠ 0)
    (h_deficit :
      ∀ p, Nat.Prime p → p ∣ L →
        (M p).factorization (q p) > A.factorization (q p)) :
    d = L := by
  apply no_prime_drop_implies_eq d L hLpos h_dvd
  intro p hp hpL hdrop
  have hblock : ¬ M p ∣ A :=
    valuation_deficit_blocks_dvd
      (h_q_prime p hp hpL)
      (h_M_ne_zero p hp hpL)
      hA
      (h_deficit p hp hpL)
  exact hblock (h_collapse_if_drop p hp hpL hdrop)

theorem collapse_divisor_core
    {A B C M Q g : Nat}
    (hQpos : 0 < Q)
    (hB_MC : B = M * C)
    (hB_gQ : B = g * Q)
    (hQ_dvd_C : Q ∣ C)
    (hg_dvd_A : g ∣ A) :
    M ∣ A := by
  rcases hQ_dvd_C with ⟨t, ht⟩
  have hMg : M * t = g := by
    have hB_MtQ : B = (M * t) * Q := by
      rw [hB_MC, ht]
      ac_rfl
    have hmul : (M * t) * Q = g * Q := by
      rw [← hB_MtQ, hB_gQ]
    exact Nat.eq_of_mul_eq_mul_right hQpos hmul
  rcases hg_dvd_A with ⟨u, hu⟩
  refine ⟨t * u, ?_⟩
  rw [hu, ← hMg]
  ac_rfl

theorem gcd_denominator_factor
    (A B : Nat) :
    B = Nat.gcd A B * (B / Nat.gcd A B) := by
  have hdiv : Nat.gcd A B ∣ B := Nat.gcd_dvd_right A B
  rw [mul_comm]
  exact (Nat.div_mul_cancel hdiv).symm

theorem collapse_divisor_from_gcd_denominator
    {A B C M Q : Nat}
    (hQ : Q = B / Nat.gcd A B)
    (hB_MC : B = M * C)
    (hQ_dvd_C : Q ∣ C)
    (hQpos : 0 < Q) :
    M ∣ A := by
  exact collapse_divisor_core
    (A := A)
    (B := B)
    (C := C)
    (M := M)
    (Q := Q)
    (g := Nat.gcd A B)
    hQpos
    hB_MC
    (by
      rw [hQ]
      exact gcd_denominator_factor A B)
    hQ_dvd_C
    (Nat.gcd_dvd_left A B)

theorem period_witness_dvd_component
    {b Q d e : Nat}
    (hQ_period : Q ∣ b ^ d - 1)
    (hd_e : d ∣ e) :
    Q ∣ b ^ e - 1 := by
  exact dvd_trans hQ_period (Nat.pow_sub_one_dvd_pow_sub_one b hd_e)

theorem collapse_divisor_from_period_witness
    {A B C M Q b d e : Nat}
    (hQ : Q = B / Nat.gcd A B)
    (hB_MC : B = M * C)
    (hC_eq : C = b ^ e - 1)
    (hQ_period : Q ∣ b ^ d - 1)
    (hd_e : d ∣ e)
    (hQpos : 0 < Q) :
    M ∣ A := by
  exact collapse_divisor_from_gcd_denominator
    (A := A)
    (B := B)
    (C := C)
    (M := M)
    (Q := Q)
    hQ
    hB_MC
    (by
      rw [hC_eq]
      exact period_witness_dvd_component hQ_period hd_e)
    hQpos

theorem period_witness_certificate_implies_no_prime_drop
    (d L A B Q b : Nat)
    (M C q : Nat → Nat)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_dvd : d ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hQ_period : Q ∣ b ^ d - 1)
    (h_component_factor :
      ∀ p, Nat.Prime p → p ∣ L → B = M p * C p)
    (h_component_eq :
      ∀ p, Nat.Prime p → p ∣ L → C p = b ^ (L / p) - 1)
    (h_q_prime :
      ∀ p, Nat.Prime p → p ∣ L → Nat.Prime (q p))
    (h_M_ne_zero :
      ∀ p, Nat.Prime p → p ∣ L → M p ≠ 0)
    (h_deficit :
      ∀ p, Nat.Prime p → p ∣ L →
        (M p).factorization (q p) > A.factorization (q p)) :
    d = L := by
  apply valuation_witnesses_imply_no_prime_drop d L A M q hLpos hA h_dvd
  · intro p hp hpL hdrop
    exact collapse_divisor_from_period_witness
      (A := A)
      (B := B)
      (C := C p)
      (M := M p)
      (Q := Q)
      (b := b)
      (d := d)
      (e := L / p)
      hQ
      (h_component_factor p hp hpL)
      (h_component_eq p hp hpL)
      hQ_period
      hdrop
      hQpos
  · exact h_q_prime
  · exact h_M_ne_zero
  · exact h_deficit

theorem modEq_one_supplies_period_witness
    {b Q d : Nat}
    (hpow : 1 ≤ b ^ d)
    (hmod : b ^ d ≡ 1 [MOD Q]) :
    Q ∣ b ^ d - 1 := by
  exact (Nat.modEq_iff_dvd' hpow).1 hmod.symm

theorem collapse_divisor_from_modEq_period
    {A B C M Q b d e : Nat}
    (hQ : Q = B / Nat.gcd A B)
    (hB_MC : B = M * C)
    (hC_eq : C = b ^ e - 1)
    (hpow : 1 ≤ b ^ d)
    (hmod : b ^ d ≡ 1 [MOD Q])
    (hd_e : d ∣ e)
    (hQpos : 0 < Q) :
    M ∣ A := by
  exact collapse_divisor_from_period_witness
    (A := A)
    (B := B)
    (C := C)
    (M := M)
    (Q := Q)
    (b := b)
    (d := d)
    (e := e)
    hQ
    hB_MC
    hC_eq
    (modEq_one_supplies_period_witness hpow hmod)
    hd_e
    hQpos

theorem modEq_certificate_implies_no_prime_drop
    (d L A B Q b : Nat)
    (M C q : Nat → Nat)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_dvd : d ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hpow : 1 ≤ b ^ d)
    (hmod : b ^ d ≡ 1 [MOD Q])
    (h_component_factor :
      ∀ p, Nat.Prime p → p ∣ L → B = M p * C p)
    (h_component_eq :
      ∀ p, Nat.Prime p → p ∣ L → C p = b ^ (L / p) - 1)
    (h_q_prime :
      ∀ p, Nat.Prime p → p ∣ L → Nat.Prime (q p))
    (h_M_ne_zero :
      ∀ p, Nat.Prime p → p ∣ L → M p ≠ 0)
    (h_deficit :
      ∀ p, Nat.Prime p → p ∣ L →
        (M p).factorization (q p) > A.factorization (q p)) :
    d = L := by
  exact period_witness_certificate_implies_no_prime_drop
    d L A B Q b M C q
    hLpos
    hA
    h_dvd
    hQpos
    hQ
    (modEq_one_supplies_period_witness hpow hmod)
    h_component_factor
    h_component_eq
    h_q_prime
    h_M_ne_zero
    h_deficit

theorem orderOf_dvd_supplies_modEq
    {b Q d : Nat}
    (hcop : Nat.Coprime b Q)
    (hord_dvd : orderOf (ZMod.unitOfCoprime b hcop) ∣ d) :
    b ^ d ≡ 1 [MOD Q] := by
  have hunit_pow :
      (ZMod.unitOfCoprime b hcop) ^ d = 1 := by
    exact (orderOf_dvd_iff_pow_eq_one).1 hord_dvd
  have hzmod : ((b ^ d : Nat) : ZMod Q) = ((1 : Nat) : ZMod Q) := by
    have hcoerced :=
      congrArg (fun u : (ZMod Q)ˣ => (u : ZMod Q)) hunit_pow
    simpa [ZMod.coe_unitOfCoprime] using hcoerced
  exact (ZMod.natCast_eq_natCast_iff (b ^ d) 1 Q).1 hzmod

theorem orderOf_dvd_iff_modEq_one
    {b q n : Nat}
    (hcop : Nat.Coprime b q) :
    orderOf (ZMod.unitOfCoprime b hcop) ∣ n ↔ b ^ n ≡ 1 [MOD q] := by
  constructor
  · exact orderOf_dvd_supplies_modEq hcop
  · intro hmod
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply Units.ext
    have hzmod : ((b ^ n : Nat) : ZMod q) = ((1 : Nat) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff (b ^ n) 1 q).2 hmod
    simpa [ZMod.coe_unitOfCoprime] using hzmod

theorem orderOf_dvd_iff_q_dvd_pow_sub_one
    {b q n : Nat}
    (hcop : Nat.Coprime b q)
    (hpow : 1 ≤ b ^ n) :
    orderOf (ZMod.unitOfCoprime b hcop) ∣ n ↔ q ∣ b ^ n - 1 := by
  constructor
  · intro hord
    exact modEq_one_supplies_period_witness hpow
      ((orderOf_dvd_iff_modEq_one hcop).1 hord)
  · intro hdiv
    apply (orderOf_dvd_iff_modEq_one hcop).2
    exact ((Nat.modEq_iff_dvd' hpow).2 hdiv).symm

theorem odd_prime_order_padicVal_pow_sub_one
    {b q d k : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k ≠ 0) :
    padicValNat q (b ^ (d * k) - 1) =
      padicValNat q (b ^ d - 1) + padicValNat q k := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hbase_dvd : q ∣ b ^ d - 1 := by
    have hord : orderOf (ZMod.unitOfCoprime b hcop) ∣ d := by
      rw [hd_order]
    exact (orderOf_dvd_iff_q_dvd_pow_sub_one hcop (le_of_lt hbase_gt_one)).1 hord
  have hnot_dvd_base : ¬ q ∣ b ^ d := by
    have hcop_pow : Nat.Coprime (b ^ d) q := hcop.pow_left d
    exact (hq.coprime_iff_not_dvd).1 hcop_pow.symm
  simpa [pow_mul] using
    (padicValNat.pow_sub_pow
      (p := q)
      (x := b ^ d)
      (y := 1)
      hq_odd
      hbase_gt_one
      hbase_dvd
      hnot_dvd_base
      hk_ne_zero)

theorem factorization_left_factor_of_mul_eq
    {N Q D q : Nat}
    (hQ_ne_zero : Q ≠ 0)
    (hD_ne_zero : D ≠ 0)
    (hN : N = Q * D) :
    Q.factorization q = N.factorization q - D.factorization q := by
  rw [hN, Nat.factorization_mul hQ_ne_zero hD_ne_zero]
  simp

theorem odd_prime_order_factorization_pow_sub_one
    {b q d k : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k ≠ 0) :
    (b ^ (d * k) - 1).factorization q =
      (b ^ d - 1).factorization q + k.factorization q := by
  rw [Nat.factorization_def (b ^ (d * k) - 1) hq]
  rw [Nat.factorization_def (b ^ d - 1) hq]
  rw [Nat.factorization_def k hq]
  exact odd_prime_order_padicVal_pow_sub_one
    hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero

theorem collapse_divisor_from_orderOf_drop
    {A B C M Q b d e : Nat}
    (hcop : Nat.Coprime b Q)
    (hord_dvd : orderOf (ZMod.unitOfCoprime b hcop) ∣ d)
    (hQ : Q = B / Nat.gcd A B)
    (hB_MC : B = M * C)
    (hC_eq : C = b ^ e - 1)
    (hd_e : d ∣ e)
    (hQpos : 0 < Q)
    (hpow : 1 ≤ b ^ d) :
    M ∣ A := by
  exact collapse_divisor_from_modEq_period
    hQ
    hB_MC
    hC_eq
    hpow
    (orderOf_dvd_supplies_modEq hcop hord_dvd)
    hd_e
    hQpos

theorem pow_sub_one_component_factor
    (b L e : Nat)
    (heL : e ∣ L) :
    b ^ L - 1 = ((b ^ L - 1) / (b ^ e - 1)) * (b ^ e - 1) := by
  have hdiv : b ^ e - 1 ∣ b ^ L - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one b heL
  exact (Nat.div_mul_cancel hdiv).symm

theorem pow_sub_one_component_factorization
    {b L e q : Nat}
    (heL : e ∣ L)
    (hquot_ne_zero : ((b ^ L - 1) / (b ^ e - 1)) ≠ 0)
    (hden_ne_zero : b ^ e - 1 ≠ 0) :
    (((b ^ L - 1) / (b ^ e - 1)).factorization q)
      =
    (b ^ L - 1).factorization q - (b ^ e - 1).factorization q := by
  exact factorization_left_factor_of_mul_eq
    (N := b ^ L - 1)
    (Q := (b ^ L - 1) / (b ^ e - 1))
    (D := b ^ e - 1)
    hquot_ne_zero
    hden_ne_zero
    (pow_sub_one_component_factor b L e heL)

theorem odd_prime_order_component_term_valuation
    {b q d K k : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k ≠ 0)
    (hK_ne_zero : K ≠ 0)
    (hkK : k ∣ K)
    (hquot_ne_zero :
      ((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) ≠ 0)
    (hden_ne_zero : b ^ (d * k) - 1 ≠ 0) :
    (((b ^ (d * K) - 1) / (b ^ (d * k) - 1)).factorization q)
      =
    K.factorization q - k.factorization q := by
  have heL : d * k ∣ d * K := mul_dvd_mul_left d hkK
  have hquot :
      (((b ^ (d * K) - 1) / (b ^ (d * k) - 1)).factorization q)
        =
      (b ^ (d * K) - 1).factorization q -
        (b ^ (d * k) - 1).factorization q :=
    pow_sub_one_component_factorization
      (b := b)
      (L := d * K)
      (e := d * k)
      (q := q)
      heL
      hquot_ne_zero
      hden_ne_zero
  have hnum :
      (b ^ (d * K) - 1).factorization q =
        (b ^ d - 1).factorization q + K.factorization q :=
    odd_prime_order_factorization_pow_sub_one
      hq hq_odd hcop hd_order hbase_gt_one hK_ne_zero
  have hden :
      (b ^ (d * k) - 1).factorization q =
        (b ^ d - 1).factorization q + k.factorization q :=
    odd_prime_order_factorization_pow_sub_one
      hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero
  rw [hquot, hnum, hden]
  exact Nat.add_sub_add_left
    ((b ^ d - 1).factorization q)
    (K.factorization q)
    (k.factorization q)

theorem normalized_factorization_unit_not_dvd
    {q N : Nat}
    (hq : Nat.Prime q)
    (hN_ne_zero : N ≠ 0) :
    ¬ q ∣ N / q ^ (N.factorization q) := by
  have hpow_dvd_N : q ^ (N.factorization q) ∣ N := by
    exact (hq.pow_dvd_iff_le_factorization hN_ne_zero).2 le_rfl
  have hpow_pos : 0 < q ^ (N.factorization q) := pow_pos hq.pos _
  have hquot_pos : 0 < N / q ^ (N.factorization q) := by
    exact Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hN_ne_zero) hpow_dvd_N)
      hpow_pos
  have hquot_ne_zero :
      N / q ^ (N.factorization q) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hquot_pos
  intro hdiv
  have hpos : 0 < (N / q ^ (N.factorization q)).factorization q :=
    hq.factorization_pos_of_dvd hquot_ne_zero hdiv
  have hzero :
      (N / q ^ (N.factorization q)).factorization q = 0 := by
    have hf :=
      congrArg (fun f : Nat →₀ Nat => f q)
        (Nat.factorization_div hpow_dvd_N)
    simpa [Nat.factorization_pow, Nat.Prime.factorization_self hq] using hf
  exact (Nat.not_lt_zero _) (hzero ▸ hpos)

theorem odd_prime_order_normalized_pow_sub_one_not_dvd
    {b q d k : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k ≠ 0) :
    ¬ q ∣
      (b ^ (d * k) - 1) /
        q ^ ((b ^ d - 1).factorization q + k.factorization q) := by
  have hpow_gt_one : 1 < b ^ (d * k) := by
    rw [pow_mul]
    exact Nat.one_lt_pow hk_ne_zero hbase_gt_one
  have hN_ne_zero : b ^ (d * k) - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt hpow_gt_one
  have hunit := normalized_factorization_unit_not_dvd
    (q := q)
    (N := b ^ (d * k) - 1)
    hq
    hN_ne_zero
  have hval := odd_prime_order_factorization_pow_sub_one
    (b := b)
    (q := q)
    (d := d)
    (k := k)
    hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero
  rwa [hval] at hunit

theorem odd_prime_order_component_term_normalized_not_dvd
    {b q d K k : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k ≠ 0)
    (hK_ne_zero : K ≠ 0)
    (hkK : k ∣ K)
    (hquot_ne_zero :
      ((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) ≠ 0)
    (hden_ne_zero : b ^ (d * k) - 1 ≠ 0) :
    ¬ q ∣
      ((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) /
        q ^ (K.factorization q - k.factorization q) := by
  have hunit := normalized_factorization_unit_not_dvd
    (q := q)
    (N := (b ^ (d * K) - 1) / (b ^ (d * k) - 1))
    hq
    hquot_ne_zero
  have hval := odd_prime_order_component_term_valuation
    (b := b)
    (q := q)
    (d := d)
    (K := K)
    (k := k)
    hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero hK_ne_zero
    hkK hquot_ne_zero hden_ne_zero
  rwa [hval] at hunit

theorem exact_pow_div_eq_add_mul_of_eq_mul_add_pow_succ
    {q m N R C : Nat}
    (hqpos : 0 < q)
    (h :
      N = q ^ m * R + q ^ (m + 1) * C) :
    N / q ^ m = R + q * C := by
  rw [h]
  have hqm_pos : 0 < q ^ m := pow_pos hqpos _
  rw [pow_succ]
  rw [Nat.mul_assoc]
  rw [← Nat.mul_add]
  exact Nat.mul_div_cancel_left (R + q * C) hqm_pos

theorem exact_pow_div_modEq_of_eq_mul_add_pow_succ
    {q m N R C : Nat}
    (hqpos : 0 < q)
    (h :
      N = q ^ m * R + q ^ (m + 1) * C) :
    N / q ^ m ≡ R [MOD q] := by
  rw [exact_pow_div_eq_add_mul_of_eq_mul_add_pow_succ hqpos h]
  have hzero : q * C ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).2 ⟨C, rfl⟩
  exact Nat.ModEq.add_left R hzero

theorem exists_pow_first_order_any_exponent
    {q r u v : Nat}
    (_hqpos : 0 < q)
    (hr_pos : 0 < r) :
    ∃ C,
      (1 + q ^ r * u) ^ v =
        1 + q ^ r * (u * v) + q ^ (r + 1) * C := by
  cases r with
  | zero =>
      cases hr_pos
  | succ s =>
      induction v with
      | zero =>
          refine ⟨0, ?_⟩
          simp
      | succ v ih =>
          rcases ih with ⟨C, hC⟩
          refine ⟨C * (1 + q ^ (s + 1) * u) + q ^ s * ((u * v) * u), ?_⟩
          rw [pow_succ]
          rw [hC]
          ring_nf

theorem exists_pow_prime_step_first_order
    {q r u : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hr_pos : 0 < r) :
    ∃ C,
      (1 + q ^ r * u) ^ q =
        1 + q ^ (r + 1) * u + q ^ (r + 2) * C := by
  let f : Nat → Nat := fun m => (1 : Nat) ^ m * (q ^ r * u) ^ (q - m) * (q.choose m)
  have hq_ge3 : 3 ≤ q := by
    have hq_ne_two : q ≠ 2 := by
      intro h
      subst q
      rcases hq_odd with ⟨k, hk⟩
      omega
    have htwo : 2 ≤ q := hq.two_le
    omega
  have hq_two : 2 ≤ q := hq.two_le
  have hsplit : (∑ m ∈ Finset.range (q + 1), f m) =
      (∑ m ∈ Finset.range (q - 1), f m) + f (q - 1) + f q := by
    have hq_eq : q = (q - 1) + 1 := by omega
    calc
      (∑ m ∈ Finset.range (q + 1), f m)
          = (∑ m ∈ Finset.range q, f m) + f q := by
              simpa [Nat.add_comm] using (Finset.sum_range_succ f q)
      _ = ((∑ m ∈ Finset.range (q - 1), f m) + f (q - 1)) + f q := by
              conv_lhs => rw [hq_eq]
              rw [Finset.sum_range_succ]
              rw [← hq_eq]
      _ = (∑ m ∈ Finset.range (q - 1), f m) + f (q - 1) + f q := by
              ac_rfl
  have hhigh : q ^ (r + 2) ∣ (∑ m ∈ Finset.range (q - 1), f m) := by
    apply Finset.dvd_sum
    intro m hm
    have hm_lt_q_sub : m < q - 1 := Finset.mem_range.mp hm
    by_cases hm0 : m = 0
    · subst m
      have hle_exp : r + 2 ≤ r * q := by nlinarith
      have hpowdvd : q ^ (r + 2) ∣ q ^ (r * q) := Nat.pow_dvd_pow q hle_exp
      dsimp [f]
      simp [Nat.choose_zero_right]
      rw [mul_pow, ← pow_mul]
      exact dvd_mul_of_dvd_left hpowdvd (u ^ q)
    · have hm_lt_q : m < q := by omega
      have hq_choose : q ∣ q.choose m := hq.dvd_choose_self hm0 hm_lt_q
      have hqm_ge_two : 2 ≤ q - m := by omega
      have hle_exp : r + 1 ≤ r * (q - m) := by nlinarith
      have hpowdvd : q ^ (r + 1) ∣ (q ^ r * u) ^ (q - m) := by
        rw [mul_pow, ← pow_mul]
        exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow q hle_exp) (u ^ (q - m))
      rcases hpowdvd with ⟨A, hA⟩
      rcases hq_choose with ⟨B, hB⟩
      refine ⟨A * B, ?_⟩
      dsimp [f]
      rw [hA, hB]
      rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
      ring_nf
  rcases hhigh with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rw [add_pow]
  change (∑ m ∈ Finset.range (q + 1), f m) = 1 + q ^ (r + 1) * u + q ^ (r + 2) * C
  rw [hsplit, hC]
  have hfq : f q = 1 := by
    dsimp [f]
    simp [Nat.choose_self]
  have hfqm1 : f (q - 1) = q ^ (r + 1) * u := by
    dsimp [f]
    have hsub : q - (q - 1) = 1 := by omega
    have hchoose : q.choose (q - 1) = q := by
      rw [Nat.choose_symm (show 1 ≤ q by omega)]
      simp [Nat.choose_one_right]
    rw [hsub, hchoose]
    ring_nf
  rw [hfq, hfqm1]
  ring

theorem exists_pow_q_iter_first_order
    {q a s u : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (ha_pos : 0 < a) :
    ∃ C,
      (1 + q ^ a * u) ^ (q ^ s) =
        1 + q ^ (a + s) * u + q ^ (a + s + 1) * C := by
  induction s with
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | succ s ih =>
      rcases ih with ⟨C, hC⟩
      have has_pos : 0 < a + s := by omega
      obtain ⟨D, hD⟩ := exists_pow_prime_step_first_order
        (q := q) (r := a + s) (u := u + q * C) hq hq_odd has_pos
      refine ⟨C + D, ?_⟩
      rw [pow_succ]
      rw [pow_mul]
      rw [hC]
      have hbase :
          1 + q ^ (a + s) * u + q ^ (a + s + 1) * C =
            1 + q ^ (a + s) * (u + q * C) := by
        rw [show a + s + 1 = (a + s) + 1 by omega, pow_succ]
        ring
      rw [hbase]
      rw [hD]
      rw [show a + (s + 1) = a + s + 1 by omega]
      rw [show a + s + 1 + 1 = a + s + 2 by omega]
      rw [show a + s + 2 = (a + s + 1) + 1 by omega, pow_succ]
      ring

theorem factorization_pow_unit_mul_self
    {q k : Nat}
    (hq : Nat.Prime q)
    (hk_ne_zero : k ≠ 0) :
    q ^ (k.factorization q) * (k / q ^ (k.factorization q)) = k := by
  have hpow_dvd : q ^ (k.factorization q) ∣ k := by
    exact (hq.pow_dvd_iff_le_factorization hk_ne_zero).2 le_rfl
  exact Nat.mul_div_cancel' hpow_dvd

theorem odd_prime_order_base_eq_one_add_exact_unit
    {b q d : Nat}
    (hq : Nat.Prime q)
    (hbase_gt_one : 1 < b ^ d) :
    b ^ d =
      1 + q ^ ((b ^ d - 1).factorization q) *
        ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) := by
  have hN_ne_zero : b ^ d - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt hbase_gt_one
  have hpow_dvd :
      q ^ ((b ^ d - 1).factorization q) ∣ b ^ d - 1 := by
    exact (hq.pow_dvd_iff_le_factorization hN_ne_zero).2 le_rfl
  have hdecomp :
      q ^ ((b ^ d - 1).factorization q) *
          ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) =
        b ^ d - 1 :=
    Nat.mul_div_cancel' hpow_dvd
  rw [hdecomp]
  omega

theorem odd_prime_order_pow_sub_one_eq_mul_add_pow_succ
    {b q d k : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k ≠ 0) :
    ∃ C,
      b ^ (d * k) - 1 =
        q ^ ((b ^ d - 1).factorization q + k.factorization q) *
          (((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
            (k / q ^ (k.factorization q))) +
        q ^ (((b ^ d - 1).factorization q + k.factorization q) + 1) * C := by
  let m := (b ^ d - 1).factorization q
  let s := k.factorization q
  let U := (b ^ d - 1) / q ^ m
  let V := k / q ^ s
  have hbase_dvd : q ∣ b ^ d - 1 := by
    have hord : orderOf (ZMod.unitOfCoprime b hcop) ∣ d := by
      rw [hd_order]
    exact (orderOf_dvd_iff_q_dvd_pow_sub_one hcop (le_of_lt hbase_gt_one)).1 hord
  have hN_ne_zero : b ^ d - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt hbase_gt_one
  have hm_pos : 0 < m := by
    dsimp [m]
    exact hq.factorization_pos_of_dvd hN_ne_zero hbase_dvd
  have hk_decomp : q ^ s * V = k := by
    dsimp [s, V]
    exact factorization_pow_unit_mul_self hq hk_ne_zero
  have hbase_eq : b ^ d = 1 + q ^ m * U := by
    dsimp [m, U]
    exact odd_prime_order_base_eq_one_add_exact_unit hq hbase_gt_one
  obtain ⟨C, hC⟩ := exists_pow_q_iter_first_order
    (q := q) (a := m) (s := s) (u := U) hq hq_odd hm_pos
  have hms_pos : 0 < m + s := by omega
  obtain ⟨D, hD⟩ := exists_pow_first_order_any_exponent
    (q := q) (r := m + s) (u := U + q * C) (v := V) hq.pos hms_pos
  refine ⟨C * V + D, ?_⟩
  have hpow_eq :
      b ^ (d * k) =
        1 + q ^ (m + s) * (U * V) +
          q ^ ((m + s) + 1) * (C * V + D) := by
    rw [pow_mul]
    rw [← hk_decomp]
    rw [pow_mul]
    rw [hbase_eq]
    rw [hC]
    have hbase2 :
        1 + q ^ (m + s) * U + q ^ (m + s + 1) * C =
          1 + q ^ (m + s) * (U + q * C) := by
      rw [show m + s + 1 = (m + s) + 1 by omega, pow_succ]
      ring
    rw [hbase2]
    rw [hD]
    rw [show m + s + 1 = (m + s) + 1 by omega, pow_succ]
    ring
  dsimp [m, s, U, V] at hpow_eq ⊢
  rw [hpow_eq]
  omega

theorem odd_prime_order_normalized_pow_sub_one_modEq
    {b q d k : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k ≠ 0) :
    (b ^ (d * k) - 1) /
        q ^ ((b ^ d - 1).factorization q + k.factorization q)
      ≡
    ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
      (k / q ^ (k.factorization q))
      [MOD q] := by
  obtain ⟨C, hC⟩ := odd_prime_order_pow_sub_one_eq_mul_add_pow_succ
    hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero
  exact exact_pow_div_modEq_of_eq_mul_add_pow_succ hq.pos hC

theorem normalized_factorization_mul_eq
    {q N M D : Nat}
    (hq : Nat.Prime q)
    (hM_ne_zero : M ≠ 0)
    (hD_ne_zero : D ≠ 0)
    (hN_eq : N = M * D) :
    N / q ^ (N.factorization q) =
      (M / q ^ (M.factorization q)) *
        (D / q ^ (D.factorization q)) := by
  have hN_ne_zero : N ≠ 0 := by
    rw [hN_eq]
    exact mul_ne_zero hM_ne_zero hD_ne_zero
  have hv : N.factorization q = M.factorization q + D.factorization q := by
    rw [hN_eq, Nat.factorization_mul hM_ne_zero hD_ne_zero]
    rfl
  have hN_unit := factorization_pow_unit_mul_self hq hN_ne_zero
  have hM_unit := factorization_pow_unit_mul_self hq hM_ne_zero
  have hD_unit := factorization_pow_unit_mul_self hq hD_ne_zero
  have hprod :
      q ^ (N.factorization q) *
          ((M / q ^ (M.factorization q)) *
            (D / q ^ (D.factorization q))) = N := by
    calc
      q ^ (N.factorization q) *
          ((M / q ^ (M.factorization q)) *
            (D / q ^ (D.factorization q)))
          = (q ^ (M.factorization q) * q ^ (D.factorization q)) *
              ((M / q ^ (M.factorization q)) *
                (D / q ^ (D.factorization q))) := by
              rw [hv, pow_add]
      _ = (q ^ (M.factorization q) * (M / q ^ (M.factorization q))) *
              (q ^ (D.factorization q) * (D / q ^ (D.factorization q))) := by
              ring
      _ = M * D := by rw [hM_unit, hD_unit]
      _ = N := by rw [← hN_eq]
  exact Nat.mul_left_cancel (pow_pos hq.pos _) (by rw [hN_unit, hprod])

theorem odd_prime_order_component_term_normalized_crossmul_eq
    {b q d K k : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k ≠ 0)
    (hK_ne_zero : K ≠ 0)
    (hkK : k ∣ K)
    (hquot_ne_zero :
      ((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) ≠ 0)
    (hden_ne_zero : b ^ (d * k) - 1 ≠ 0) :
    (b ^ (d * K) - 1) /
        q ^ ((b ^ d - 1).factorization q + K.factorization q)
      =
    (((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) /
        q ^ (K.factorization q - k.factorization q)) *
      ((b ^ (d * k) - 1) /
        q ^ ((b ^ d - 1).factorization q + k.factorization q)) := by
  have hdk_dK : d * k ∣ d * K := by
    rcases hkK with ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    ring
  have hN_eq :
      b ^ (d * K) - 1 =
        ((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) *
          (b ^ (d * k) - 1) :=
    pow_sub_one_component_factor b (d * K) (d * k) hdk_dK
  have hNnorm := normalized_factorization_mul_eq
    (q := q)
    (N := b ^ (d * K) - 1)
    (M := (b ^ (d * K) - 1) / (b ^ (d * k) - 1))
    (D := b ^ (d * k) - 1)
    hq hquot_ne_zero hden_ne_zero hN_eq
  have hNval :
      (b ^ (d * K) - 1).factorization q =
        (b ^ d - 1).factorization q + K.factorization q :=
    odd_prime_order_factorization_pow_sub_one
      hq hq_odd hcop hd_order hbase_gt_one hK_ne_zero
  have hDval :
      (b ^ (d * k) - 1).factorization q =
        (b ^ d - 1).factorization q + k.factorization q :=
    odd_prime_order_factorization_pow_sub_one
      hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero
  have hMval :
      ((b ^ (d * K) - 1) / (b ^ (d * k) - 1)).factorization q =
        K.factorization q - k.factorization q :=
    odd_prime_order_component_term_valuation
      hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero hK_ne_zero
      hkK hquot_ne_zero hden_ne_zero
  simpa [hNval, hDval, hMval] using hNnorm

theorem odd_prime_order_component_term_residue_crossmul
    {b q d K k : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k ≠ 0)
    (hK_ne_zero : K ≠ 0)
    (hkK : k ∣ K)
    (hquot_ne_zero :
      ((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) ≠ 0)
    (hden_ne_zero : b ^ (d * k) - 1 ≠ 0) :
    (((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) /
        q ^ (K.factorization q - k.factorization q)) *
      (((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
        (k / q ^ (k.factorization q)))
      ≡
    ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
      (K / q ^ (K.factorization q))
      [MOD q] := by
  have hKmod := odd_prime_order_normalized_pow_sub_one_modEq
    (b := b) (q := q) (d := d) (k := K)
    hq hq_odd hcop hd_order hbase_gt_one hK_ne_zero
  have hkmod := odd_prime_order_normalized_pow_sub_one_modEq
    (b := b) (q := q) (d := d) (k := k)
    hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero
  have heq := odd_prime_order_component_term_normalized_crossmul_eq
    (b := b) (q := q) (d := d) (K := K) (k := k)
    hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero hK_ne_zero
    hkK hquot_ne_zero hden_ne_zero
  have hright :
      (((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) /
          q ^ (K.factorization q - k.factorization q)) *
        ((b ^ (d * k) - 1) /
          q ^ ((b ^ d - 1).factorization q + k.factorization q))
        ≡
      ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
        (K / q ^ (K.factorization q))
        [MOD q] := by
    rw [← heq]
    exact hKmod
  have hleft :
      (((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) /
          q ^ (K.factorization q - k.factorization q)) *
        ((b ^ (d * k) - 1) /
          q ^ ((b ^ d - 1).factorization q + k.factorization q))
        ≡
      (((b ^ (d * K) - 1) / (b ^ (d * k) - 1)) /
          q ^ (K.factorization q - k.factorization q)) *
        (((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
          (k / q ^ (k.factorization q)))
        [MOD q] := by
    exact Nat.ModEq.mul_left _ hkmod
  exact hleft.symm.trans hright

theorem finset_sum_modEq_of_forall
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {q : Nat}
    {f g : ι → Nat}
    (h : ∀ i, i ∈ s → f i ≡ g i [MOD q]) :
    (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [MOD q] := by
  induction s using Finset.induction_on with
  | empty =>
      exact Nat.ModEq.refl 0
  | insert a s ha ih =>
      simp [ha]
      exact Nat.ModEq.add
        (h a (by simp [ha]))
        (ih (by
          intro i hi
          exact h i (by simp [hi])))

theorem finset_sum_mul_prod_erase_modEq
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {q N : Nat}
    {T D : ι → Nat}
    (h : ∀ i, i ∈ s → T i * D i ≡ N [MOD q]) :
    (∑ i ∈ s, T i) * (∏ i ∈ s, D i)
      ≡
    ∑ i ∈ s, N * (∏ j ∈ s.erase i, D j)
      [MOD q] := by
  have hsum_eq :
      (∑ i ∈ s, T i) * (∏ i ∈ s, D i)
        =
      ∑ i ∈ s, T i * D i * (∏ j ∈ s.erase i, D j) := by
    calc
      (∑ i ∈ s, T i) * (∏ i ∈ s, D i)
          = ∑ i ∈ s, T i * (∏ i ∈ s, D i) := by
              rw [Finset.sum_mul]
      _ = ∑ i ∈ s, T i * (D i * (∏ j ∈ s.erase i, D j)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [← Finset.mul_prod_erase s D hi]
      _ = ∑ i ∈ s, T i * D i * (∏ j ∈ s.erase i, D j) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              ring
  rw [hsum_eq]
  exact finset_sum_modEq_of_forall (s := s)
    (f := fun i => T i * D i * (∏ j ∈ s.erase i, D j))
    (g := fun i => N * (∏ j ∈ s.erase i, D j))
    (by
      intro i hi
      exact Nat.ModEq.mul_right (∏ j ∈ s.erase i, D j) (h i hi))

theorem odd_prime_order_residue_formula
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {b q d K : Nat}
    {k : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : ∀ i, i ∈ s → k i ≠ 0)
    (hK_ne_zero : K ≠ 0)
    (hkK : ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero :
      ∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0)
    (hden_ne_zero :
      ∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0) :
    (∑ i ∈ s,
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) /
          q ^ (K.factorization q - (k i).factorization q)) *
      (∏ i ∈ s,
        ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
          (k i / q ^ ((k i).factorization q)))
      ≡
    ∑ i ∈ s,
      (((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
        (K / q ^ (K.factorization q))) *
        (∏ j ∈ s.erase i,
          ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
            (k j / q ^ ((k j).factorization q)))
      [MOD q] := by
  exact finset_sum_mul_prod_erase_modEq (s := s) (q := q)
    (T := fun i =>
      ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) /
        q ^ (K.factorization q - (k i).factorization q))
    (D := fun i =>
      ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
        (k i / q ^ ((k i).factorization q)))
    (N :=
      ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
        (K / q ^ (K.factorization q)))
    (by
      intro i hi
      exact odd_prime_order_component_term_residue_crossmul
        (b := b) (q := q) (d := d) (K := K) (k := k i)
        hq hq_odd hcop hd_order hbase_gt_one
        (hk_ne_zero i hi) hK_ne_zero (hkK i hi)
        (hquot_ne_zero i hi) (hden_ne_zero i hi))

theorem not_dvd_of_modEq_not_dvd
    {q a b : Nat}
    (hab : a ≡ b [MOD q])
    (hb : ¬ q ∣ b) :
    ¬ q ∣ a := by
  intro ha
  apply hb
  exact (Nat.modEq_zero_iff_dvd).1
    (hab.symm.trans ((Nat.modEq_zero_iff_dvd).2 ha))

theorem not_dvd_sum_of_common_denominator_residue
    {q S P R : Nat}
    (hresidue : S * P ≡ R [MOD q])
    (hR : ¬ q ∣ R) :
    ¬ q ∣ S := by
  intro hS
  exact (not_dvd_of_modEq_not_dvd hresidue hR)
    (dvd_mul_of_dvd_left hS P)

theorem odd_prime_order_residue_formula_not_dvd_sum
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {b q d K : Nat}
    {k : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : ∀ i, i ∈ s → k i ≠ 0)
    (hK_ne_zero : K ≠ 0)
    (hkK : ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero :
      ∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0)
    (hden_ne_zero :
      ∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0)
    (hR_not_dvd :
      ¬ q ∣
        ∑ i ∈ s,
          (((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
            (K / q ^ (K.factorization q))) *
            (∏ j ∈ s.erase i,
              ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
                (k j / q ^ ((k j).factorization q)))) :
    ¬ q ∣
      ∑ i ∈ s,
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) /
          q ^ (K.factorization q - (k i).factorization q) := by
  exact not_dvd_sum_of_common_denominator_residue
    (P := ∏ i ∈ s,
      ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
        (k i / q ^ ((k i).factorization q)))
    (R := ∑ i ∈ s,
      (((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
        (K / q ^ (K.factorization q))) *
        (∏ j ∈ s.erase i,
          ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
            (k j / q ^ ((k j).factorization q))))
    (odd_prime_order_residue_formula
      (b := b) (q := q) (d := d) (K := K) (k := k)
      hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero hK_ne_zero
      hkK hquot_ne_zero hden_ne_zero)
    hR_not_dvd

theorem collapse_divisor_from_orderOf_component
    {A B Q b d L e : Nat}
    (hcop : Nat.Coprime b Q)
    (hord_dvd : orderOf (ZMod.unitOfCoprime b hcop) ∣ d)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (heL : e ∣ L)
    (hd_e : d ∣ e)
    (hQpos : 0 < Q)
    (hpow : 1 ≤ b ^ d) :
    (b ^ L - 1) / (b ^ e - 1) ∣ A := by
  exact collapse_divisor_from_orderOf_drop
    (A := A)
    (B := B)
    (C := b ^ e - 1)
    (M := (b ^ L - 1) / (b ^ e - 1))
    (Q := Q)
    (b := b)
    (d := d)
    (e := e)
    hcop
    hord_dvd
    hQ
    (by
      rw [hB_eq]
      exact pow_sub_one_component_factor b L e heL)
    rfl
    hd_e
    hQpos
    hpow

theorem quotient_by_pos_divisor_dvd_self
    {L p : Nat}
    (hp_pos : 0 < p)
    (hpL : p ∣ L) :
    L / p ∣ L := by
  rcases hpL with ⟨k, rfl⟩
  rw [mul_comm p k, Nat.mul_div_left _ hp_pos]
  exact dvd_mul_right k p

theorem collapse_divisor_equivalence_one_direction
    {A B Q b d L p : Nat}
    (hp : Nat.Prime p)
    (hpL : p ∣ L)
    (hcop : Nat.Coprime b Q)
    (hord_dvd : orderOf (ZMod.unitOfCoprime b hcop) ∣ d)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hd_drop : d ∣ L / p)
    (hQpos : 0 < Q)
    (hpow : 1 ≤ b ^ d) :
    (b ^ L - 1) / (b ^ (L / p) - 1) ∣ A := by
  exact collapse_divisor_from_orderOf_component
    (A := A)
    (B := B)
    (Q := Q)
    (b := b)
    (d := d)
    (L := L)
    (e := L / p)
    hcop
    hord_dvd
    hQ
    hB_eq
    (quotient_by_pos_divisor_dvd_self hp.pos hpL)
    hd_drop
    hQpos
    hpow

theorem collapse_one_direction_certificate_implies_no_prime_drop
    (d L A B Q b : Nat)
    (q : Nat → Nat)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_dvd : d ∣ L)
    (hQpos : 0 < Q)
    (hcop : Nat.Coprime b Q)
    (hord_dvd : orderOf (ZMod.unitOfCoprime b hcop) ∣ d)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ d)
    (h_q_prime :
      ∀ p, Nat.Prime p → p ∣ L → Nat.Prime (q p))
    (h_M_ne_zero :
      ∀ p, Nat.Prime p → p ∣ L →
        ((b ^ L - 1) / (b ^ (L / p) - 1)) ≠ 0)
    (h_deficit :
      ∀ p, Nat.Prime p → p ∣ L →
        (((b ^ L - 1) / (b ^ (L / p) - 1)).factorization (q p)
          > A.factorization (q p))) :
    d = L := by
  apply valuation_witnesses_imply_no_prime_drop
    d
    L
    A
    (fun p => (b ^ L - 1) / (b ^ (L / p) - 1))
    q
    hLpos
    hA
    h_dvd
  · intro p hp hpL hdrop
    exact collapse_divisor_equivalence_one_direction
      (A := A)
      (B := B)
      (Q := Q)
      (b := b)
      (d := d)
      (L := L)
      (p := p)
      hp
      hpL
      hcop
      hord_dvd
      hQ
      hB_eq
      hdrop
      hQpos
      hpow
  · exact h_q_prime
  · exact h_M_ne_zero
  · exact h_deficit

theorem witness_certificate_implies_period_noncollapse
    (L A B Q b : Nat)
    (q : Nat → Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    (h_q_prime :
      ∀ p, Nat.Prime p → p ∣ L → Nat.Prime (q p))
    (h_M_ne_zero :
      ∀ p, Nat.Prime p → p ∣ L →
        ((b ^ L - 1) / (b ^ (L / p) - 1)) ≠ 0)
    (h_deficit :
      ∀ p, Nat.Prime p → p ∣ L →
        (((b ^ L - 1) / (b ^ (L / p) - 1)).factorization (q p)
          > A.factorization (q p))) :
    orderOf (ZMod.unitOfCoprime b hcop) = L := by
  exact collapse_one_direction_certificate_implies_no_prime_drop
    (d := orderOf (ZMod.unitOfCoprime b hcop))
    (L := L)
    (A := A)
    (B := B)
    (Q := Q)
    (b := b)
    (q := q)
    hLpos
    hA
    h_ord_dvd_L
    hQpos
    hcop
    dvd_rfl
    hQ
    hB_eq
    hpow
    h_q_prime
    h_M_ne_zero
    h_deficit

def primeComponentQuotient (b L p : Nat) : Nat :=
  (b ^ L - 1) / (b ^ (L / p) - 1)

def PrimeComponentWitness
    (L A b p q : Nat) : Prop :=
  Nat.Prime q ∧
    primeComponentQuotient b L p ≠ 0 ∧
    (primeComponentQuotient b L p).factorization q > A.factorization q

theorem primeComponentWitness_of_prime_power_cofactor
    (L A b p q quotient exponent reducedCofactor AExponent : Nat)
    (hq : Nat.Prime q)
    (hquot : primeComponentQuotient b L p = quotient)
    (hfactor : quotient = q ^ exponent * reducedCofactor)
    (hquot_ne_zero : quotient ≠ 0)
    (hA_factor : A.factorization q = AExponent)
    (hsurplus : AExponent < exponent) :
    PrimeComponentWitness L A b p q := by
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    exact hquot_ne_zero
  · rw [hquot, hA_factor]
    have hpow_dvd : q ^ exponent ∣ quotient := by
      rw [hfactor]
      exact dvd_mul_right _ _
    have hle : exponent ≤ quotient.factorization q := by
      simpa using (hq.pow_dvd_iff_le_factorization hquot_ne_zero).mp hpow_dvd
    exact lt_of_lt_of_le hsurplus hle

theorem PrimeComponentWitness.mul_right_of_factorization_eq_zero
    {L A b p q k : Nat}
    (hwit : PrimeComponentWitness L A b p q)
    (hA : A ≠ 0)
    (hk : k ≠ 0)
    (hkq : k.factorization q = 0) :
    PrimeComponentWitness L (A * k) b p q := by
  rcases hwit with ⟨hq, hquot_ne_zero, hdeficit⟩
  refine ⟨hq, hquot_ne_zero, ?_⟩
  rw [Nat.factorization_mul hA hk]
  simpa [hkq] using hdeficit

theorem PrimeComponentWitness.of_factorization_le
    {L A A' b p q : Nat}
    (hwit : PrimeComponentWitness L A b p q)
    (hle : A'.factorization q ≤ A.factorization q) :
    PrimeComponentWitness L A' b p q := by
  rcases hwit with ⟨hq, hquot_ne_zero, hdeficit⟩
  refine ⟨hq, hquot_ne_zero, ?_⟩
  exact lt_of_le_of_lt hle hdeficit

noncomputable def canonicalPrimeComponentWitness
    (L A b p : Nat)
    (hex : ∃ q, PrimeComponentWitness L A b p q) : Nat := by
  classical
  exact Nat.find hex

theorem canonicalPrimeComponentWitness_spec
    (L A b p : Nat)
    (hex : ∃ q, PrimeComponentWitness L A b p q) :
    PrimeComponentWitness L A b p
      (canonicalPrimeComponentWitness L A b p hex) := by
  classical
  simpa [canonicalPrimeComponentWitness] using (Nat.find_spec hex)

theorem canonicalPrimeComponentWitness_minimal
    (L A b p q : Nat)
    (hex : ∃ q, PrimeComponentWitness L A b p q)
    (hq : PrimeComponentWitness L A b p q) :
    canonicalPrimeComponentWitness L A b p hex ≤ q := by
  classical
  simpa [canonicalPrimeComponentWitness] using (Nat.find_min' hex hq)

theorem witness_existence_implies_period_noncollapse
    (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    (h_exists :
      ∀ p, Nat.Prime p → p ∣ L →
        ∃ q, PrimeComponentWitness L A b p q) :
    orderOf (ZMod.unitOfCoprime b hcop) = L := by
  classical
  let q : Nat → Nat := fun p =>
    if h : Nat.Prime p ∧ p ∣ L then
      canonicalPrimeComponentWitness L A b p (h_exists p h.1 h.2)
    else
      0
  apply witness_certificate_implies_period_noncollapse
    (L := L)
    (A := A)
    (B := B)
    (Q := Q)
    (b := b)
    (q := q)
    hcop
    hLpos
    hA
    h_ord_dvd_L
    hQpos
    hQ
    hB_eq
    hpow
  · intro p hp hpL
    have hs :
        PrimeComponentWitness L A b p (q p) := by
      dsimp [q]
      rw [dif_pos ⟨hp, hpL⟩]
      exact canonicalPrimeComponentWitness_spec
        L A b p (h_exists p hp hpL)
    exact hs.1
  · intro p hp hpL
    have hs :
        PrimeComponentWitness L A b p (q p) := by
      dsimp [q]
      rw [dif_pos ⟨hp, hpL⟩]
      exact canonicalPrimeComponentWitness_spec
        L A b p (h_exists p hp hpL)
    simpa [primeComponentQuotient] using hs.2.1
  · intro p hp hpL
    have hs :
        PrimeComponentWitness L A b p (q p) := by
      dsimp [q]
      rw [dif_pos ⟨hp, hpL⟩]
      exact canonicalPrimeComponentWitness_spec
        L A b p (h_exists p hp hpL)
    simpa [primeComponentQuotient] using hs.2.2

def LocalLayerCertificate
    {ι : Type*}
    (s : Finset ι)
    (q m : Nat)
    (T : ι → Nat) : Prop :=
  Nat.Prime q ∧
    (∀ i, i ∈ s → q ^ m ∣ T i) ∧
    ¬ q ∣ ∑ i ∈ s, T i / q ^ m

theorem local_layer_residue_nonzero_implies_sum_valuation
    {ι : Type*}
    (s : Finset ι)
    (q m : Nat)
    (T : ι → Nat)
    (hq : Nat.Prime q)
    (hdvd : ∀ i, i ∈ s → q ^ m ∣ T i)
    (hres : ¬ q ∣ ∑ i ∈ s, T i / q ^ m) :
    (∑ i ∈ s, T i).factorization q = m := by
  have hq_pos : 0 < q := hq.pos
  have hq_pow_pos : 0 < q ^ m := pow_pos hq_pos m
  have hq_pow_ne_zero : q ^ m ≠ 0 := Nat.pos_iff_ne_zero.mp hq_pow_pos
  have hsum_eq :
      ∑ i ∈ s, T i = q ^ m * (∑ i ∈ s, T i / q ^ m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact (Nat.mul_div_cancel' (hdvd i hi)).symm
  have hR_ne_zero : (∑ i ∈ s, T i / q ^ m) ≠ 0 := by
    intro hR_zero
    exact hres (hR_zero ▸ dvd_zero q)
  rw [hsum_eq, Nat.factorization_mul hq_pow_ne_zero hR_ne_zero]
  simp [Nat.factorization_eq_zero_of_not_dvd hres,
        Nat.Prime.factorization_pow hq]

theorem LocalLayerCertificate.sum_factorization
    {ι : Type*}
    {s : Finset ι}
    {q m : Nat}
    {T : ι → Nat}
    (cert : LocalLayerCertificate s q m T) :
    (∑ i ∈ s, T i).factorization q = m :=
  local_layer_residue_nonzero_implies_sum_valuation
    s q m T cert.1 cert.2.1 cert.2.2

theorem LocalLayerCertificate.of_q_pow_decomposition
    {ι : Type*}
    {s : Finset ι}
    {q m : Nat}
    {T R : ι → Nat}
    (hq : Nat.Prime q)
    (hT :
      ∀ i, i ∈ s → T i = q ^ m * R i)
    (hres :
      ¬ q ∣ ∑ i ∈ s, R i) :
    LocalLayerCertificate s q m T := by
  refine ⟨hq, ?_, ?_⟩
  · intro i hi
    refine ⟨R i, ?_⟩
    exact hT i hi
  · have hsum :
        (∑ i ∈ s, T i / q ^ m) = ∑ i ∈ s, R i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hT i hi]
      exact Nat.mul_div_cancel_left (R i) (pow_pos hq.pos m)
    rwa [hsum]

theorem not_dvd_sum_of_subset_complement_dvd
    {ι : Type*}
    [DecidableEq ι]
    {s t : Finset ι}
    {q : Nat}
    {R : ι → Nat}
    (hts : t ⊆ s)
    (hhigh :
      ∀ i, i ∈ s → i ∉ t → q ∣ R i)
    (hres_min :
      ¬ q ∣ ∑ i ∈ t, R i) :
    ¬ q ∣ ∑ i ∈ s, R i := by
  have hfilter_eq : s.filter (fun i => i ∈ t) = t := by
    ext i
    by_cases hit : i ∈ t
    · simp [hit, hts hit]
    · simp [hit]
  have hsplit :
      (∑ i ∈ t, R i) +
          (∑ i ∈ s.filter (fun i => i ∉ t), R i) =
        ∑ i ∈ s, R i := by
    simpa [hfilter_eq] using
      (Finset.sum_filter_add_sum_filter_not s (fun i => i ∈ t) R)
  have hhigh_sum :
      q ∣ ∑ i ∈ s.filter (fun i => i ∉ t), R i := by
    refine Finset.dvd_sum ?_
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨his, hit⟩
    exact hhigh i his hit
  intro hfull
  exact hres_min <| by
    apply (Nat.dvd_add_iff_left hhigh_sum).2
    rwa [hsplit]

theorem not_dvd_sum_of_singleton_unit_and_complement_dvd
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {q : Nat}
    {R : ι → Nat}
    (hi0 : i0 ∈ s)
    (hunit : ¬ q ∣ R i0)
    (hrest :
      ∀ i, i ∈ s → i ≠ i0 → q ∣ R i) :
    ¬ q ∣ ∑ i ∈ s, R i := by
  refine not_dvd_sum_of_subset_complement_dvd
    (s := s) (t := ({i0} : Finset ι)) (q := q) (R := R)
    ?hts ?hhigh ?hres_min
  · intro i hi
    rw [Finset.mem_singleton] at hi
    simpa [hi] using hi0
  · intro i hi hit
    exact hrest i hi (by
      intro h_eq
      apply hit
      simp [h_eq])
  · simpa using hunit

theorem residue_formula_singleton_nonzero_certificate
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {q commonResidue : Nat}
    {D : ι → Nat}
    (hi0 : i0 ∈ s)
    (hunit :
      ¬ q ∣ commonResidue * (∏ j ∈ s.erase i0, D j))
    (hrest :
      ∀ i, i ∈ s → i ≠ i0 →
        q ∣ commonResidue * (∏ j ∈ s.erase i, D j)) :
    ¬ q ∣ ∑ i ∈ s, commonResidue * (∏ j ∈ s.erase i, D j) := by
  exact not_dvd_sum_of_singleton_unit_and_complement_dvd
    (s := s)
    (i0 := i0)
    (q := q)
    (R := fun i => commonResidue * (∏ j ∈ s.erase i, D j))
    hi0 hunit hrest

theorem LocalLayerCertificate.of_minimal_layer_decomposition
    {ι : Type*}
    [DecidableEq ι]
    {s t : Finset ι}
    {q m : Nat}
    {T R : ι → Nat}
    (hq : Nat.Prime q)
    (hts : t ⊆ s)
    (hT :
      ∀ i, i ∈ s → T i = q ^ m * R i)
    (hhigh :
      ∀ i, i ∈ s → i ∉ t → q ∣ R i)
    (hres_min :
      ¬ q ∣ ∑ i ∈ t, R i) :
    LocalLayerCertificate s q m T := by
  refine LocalLayerCertificate.of_q_pow_decomposition hq hT ?_
  exact not_dvd_sum_of_subset_complement_dvd hts hhigh hres_min

theorem local_layer_certificate_supplies_PrimeComponentWitness
    {L A b p q : Nat}
    (hprime : Nat.Prime q)
    (hquot_ne_zero : primeComponentQuotient b L p ≠ 0)
    (hdef : A.factorization q < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q :=
  ⟨hprime, hquot_ne_zero, hdef⟩

theorem local_layer_sum_certificate_supplies_PrimeComponentWitness
    {ι : Type*}
    {s : Finset ι}
    {q m L A b p : Nat}
    {T : ι → Nat}
    (cert : LocalLayerCertificate s q m T)
    (hA_eq : A = ∑ i ∈ s, T i)
    (hquot_ne_zero : primeComponentQuotient b L p ≠ 0)
    (hMval : m < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q := by
  have hAval : A.factorization q = m := by
    rw [hA_eq]
    exact LocalLayerCertificate.sum_factorization cert
  refine local_layer_certificate_supplies_PrimeComponentWitness
    cert.1 hquot_ne_zero ?_
  rw [hAval]
  exact hMval

theorem local_layer_decomposition_supplies_PrimeComponentWitness
    {ι : Type*}
    {s : Finset ι}
    {q m L A b p : Nat}
    {T R : ι → Nat}
    (hq : Nat.Prime q)
    (hT :
      ∀ i, i ∈ s → T i = q ^ m * R i)
    (hres :
      ¬ q ∣ ∑ i ∈ s, R i)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hquot_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q :=
  local_layer_sum_certificate_supplies_PrimeComponentWitness
    (LocalLayerCertificate.of_q_pow_decomposition hq hT hres)
    hA_eq
    hquot_ne_zero
    hMval

theorem minimal_layer_decomposition_supplies_PrimeComponentWitness
    {ι : Type*}
    [DecidableEq ι]
    {s t : Finset ι}
    {q m L A b p : Nat}
    {T R : ι → Nat}
    (hq : Nat.Prime q)
    (hts : t ⊆ s)
    (hT :
      ∀ i, i ∈ s → T i = q ^ m * R i)
    (hhigh :
      ∀ i, i ∈ s → i ∉ t → q ∣ R i)
    (hres_min :
      ¬ q ∣ ∑ i ∈ t, R i)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hquot_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q :=
  local_layer_sum_certificate_supplies_PrimeComponentWitness
    (LocalLayerCertificate.of_minimal_layer_decomposition
      hq hts hT hhigh hres_min)
    hA_eq
    hquot_ne_zero
    hMval

theorem singleton_minimal_layer_row_supplies_PrimeComponentWitness
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {q m L A b p : Nat}
    {T R : ι → Nat}
    (hq : Nat.Prime q)
    (hi0 : i0 ∈ s)
    (hT :
      ∀ i, i ∈ s → T i = q ^ m * R i)
    (hhigh :
      ∀ i, i ∈ s → i ≠ i0 → q ∣ R i)
    (hres :
      ¬ q ∣ R i0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hquot_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q := by
  refine minimal_layer_decomposition_supplies_PrimeComponentWitness
    (s := s)
    (t := ({i0} : Finset ι))
    (q := q)
    (m := m)
    (L := L)
    (A := A)
    (b := b)
    (p := p)
    (T := T)
    (R := R)
    hq ?hts hT ?hhigh_min ?hres_min hA_eq hquot_ne_zero hMval
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    exact hi0
  · intro i hi hit
    exact hhigh i hi (by
      intro h_eq
      apply hit
      simp [h_eq])
  · simpa using hres

theorem singleton_minimal_layer_row_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {q m L A b p : Nat}
    {T R : ι → Nat}
    (hq : Nat.Prime q)
    (hi0 : i0 ∈ s)
    (hT :
      ∀ i, i ∈ s → T i = q ^ m * R i)
    (hhigh :
      ∀ i, i ∈ s → i ≠ i0 → q ∣ R i)
    (hres :
      ¬ q ∣ R i0)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hquot_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hW : PrimeComponentWitness L A b p q :=
    singleton_minimal_layer_row_supplies_PrimeComponentWitness
      (s := s)
      (i0 := i0)
      (q := q)
      (m := m)
      (L := L)
      (A := A)
      (b := b)
      (p := p)
      (T := T)
      (R := R)
      hq hi0 hT hhigh hres hA_eq hquot_ne_zero hMval
  exact valuation_deficit_blocks_dvd hW.1 hW.2.1 hA hW.2.2

theorem dvd_div_pow_of_lt_factorization
    {q N m : Nat}
    (hq : Nat.Prime q)
    (hN_ne_zero : N ≠ 0)
    (hm : m < N.factorization q) :
    q ∣ N / q ^ m := by
  have hsucc_le : m + 1 ≤ N.factorization q := by omega
  have hpow_succ_dvd : q ^ (m + 1) ∣ N :=
    (hq.pow_dvd_iff_le_factorization hN_ne_zero).2 hsucc_le
  rcases hpow_succ_dvd with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [ht]
  rw [show q ^ (m + 1) = q ^ m * q by rw [pow_succ]]
  rw [Nat.mul_assoc]
  exact Nat.mul_div_cancel_left (q * t) (pow_pos hq.pos m)

theorem not_dvd_div_pow_of_factorization_eq
    {q N m : Nat}
    (hq : Nat.Prime q)
    (hN_ne_zero : N ≠ 0)
    (hm : N.factorization q = m) :
    ¬ q ∣ N / q ^ m := by
  simpa [hm] using
    (normalized_factorization_unit_not_dvd
      (q := q)
      (N := N)
      hq
      hN_ne_zero)

theorem singleton_minimal_factorization_row_supplies_PrimeComponentWitness
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {q m L A b p : Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hi0 : i0 ∈ s)
    (hT_ne_zero :
      ∀ i, i ∈ s → T i ≠ 0)
    (hi0_val :
      (T i0).factorization q = m)
    (hhigh_val :
      ∀ i, i ∈ s → i ≠ i0 → m < (T i).factorization q)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hquot_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q := by
  refine singleton_minimal_layer_row_supplies_PrimeComponentWitness
    (s := s)
    (i0 := i0)
    (q := q)
    (m := m)
    (L := L)
    (A := A)
    (b := b)
    (p := p)
    (T := T)
    (R := fun i => T i / q ^ m)
    hq hi0 ?hT ?hhigh ?hres hA_eq hquot_ne_zero hMval
  · intro i hi
    have hdiv : q ^ m ∣ T i := by
      by_cases h_eq : i = i0
      · subst i
        exact (hq.pow_dvd_iff_le_factorization (hT_ne_zero i0 hi0)).2
          (by rw [hi0_val])
      · exact (hq.pow_dvd_iff_le_factorization (hT_ne_zero i hi)).2
          (le_of_lt (hhigh_val i hi h_eq))
    exact (Nat.mul_div_cancel' hdiv).symm
  · intro i hi hne
    exact dvd_div_pow_of_lt_factorization
      hq
      (hT_ne_zero i hi)
      (hhigh_val i hi hne)
  · exact not_dvd_div_pow_of_factorization_eq
      hq
      (hT_ne_zero i0 hi0)
      hi0_val

theorem singleton_minimal_factorization_row_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {q m L A b p : Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hi0 : i0 ∈ s)
    (hT_ne_zero :
      ∀ i, i ∈ s → T i ≠ 0)
    (hi0_val :
      (T i0).factorization q = m)
    (hhigh_val :
      ∀ i, i ∈ s → i ≠ i0 → m < (T i).factorization q)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hquot_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hW : PrimeComponentWitness L A b p q :=
    singleton_minimal_factorization_row_supplies_PrimeComponentWitness
      (s := s)
      (i0 := i0)
      (q := q)
      (m := m)
      (L := L)
      (A := A)
      (b := b)
      (p := p)
      (T := T)
      hq hi0 hT_ne_zero hi0_val hhigh_val hA_eq hquot_ne_zero hMval
  exact valuation_deficit_blocks_dvd hW.1 hW.2.1 hA hW.2.2

theorem primitive_witness_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {q m L A b p : Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hi0 : i0 ∈ s)
    (hT_ne_zero :
      ∀ i, i ∈ s → T i ≠ 0)
    (hi0_val :
      (T i0).factorization q = m)
    (hhigh_val :
      ∀ i, i ∈ s → i ≠ i0 → m < (T i).factorization q)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hquot_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A :=
  singleton_minimal_factorization_row_blocks_collapse
    (s := s)
    (i0 := i0)
    (q := q)
    (m := m)
    (L := L)
    (A := A)
    (b := b)
    (p := p)
    (T := T)
    hq hi0 hT_ne_zero hi0_val hhigh_val hA hA_eq hquot_ne_zero hMval

theorem sub_lt_sub_of_lt_right_with_le
    {A x y : Nat}
    (hyx : y < x)
    (hxA : x ≤ A) :
    A - x < A - y := by
  omega

theorem maximal_weight_factorization_row_supplies_PrimeComponentWitness
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {q M m L A b p : Nat}
    {T : ι → Nat}
    {w : ι → Nat}
    (hq : Nat.Prime q)
    (hi0 : i0 ∈ s)
    (hT_ne_zero :
      ∀ i, i ∈ s → T i ≠ 0)
    (hrow_val :
      ∀ i, i ∈ s → (T i).factorization q = M - w i)
    (hi0_le :
      w i0 ≤ M)
    (hm :
      m = M - w i0)
    (hstrict_max :
      ∀ i, i ∈ s → i ≠ i0 → w i < w i0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hquot_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q := by
  refine singleton_minimal_factorization_row_supplies_PrimeComponentWitness
    (s := s)
    (i0 := i0)
    (q := q)
    (m := m)
    (L := L)
    (A := A)
    (b := b)
    (p := p)
    (T := T)
    hq hi0 hT_ne_zero ?hi0_val ?hhigh_val hA_eq hquot_ne_zero hMval
  · rw [hrow_val i0 hi0, hm]
  · intro i hi hne
    rw [hrow_val i hi, hm]
    exact sub_lt_sub_of_lt_right_with_le (hstrict_max i hi hne) hi0_le

theorem maximal_weight_factorization_row_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {q M m L A b p : Nat}
    {T : ι → Nat}
    {w : ι → Nat}
    (hq : Nat.Prime q)
    (hi0 : i0 ∈ s)
    (hT_ne_zero :
      ∀ i, i ∈ s → T i ≠ 0)
    (hrow_val :
      ∀ i, i ∈ s → (T i).factorization q = M - w i)
    (hi0_le :
      w i0 ≤ M)
    (hm :
      m = M - w i0)
    (hstrict_max :
      ∀ i, i ∈ s → i ≠ i0 → w i < w i0)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hquot_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hW : PrimeComponentWitness L A b p q :=
    maximal_weight_factorization_row_supplies_PrimeComponentWitness
      (s := s)
      (i0 := i0)
      (q := q)
      (M := M)
      (m := m)
      (L := L)
      (A := A)
      (b := b)
      (p := p)
      (T := T)
      (w := w)
      hq hi0 hT_ne_zero hrow_val hi0_le hm hstrict_max hA_eq
      hquot_ne_zero hMval
  exact valuation_deficit_blocks_dvd hW.1 hW.2.1 hA hW.2.2

theorem component_term_maximal_row_supplies_PrimeComponentWitness
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b q d K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hi0 : i0 ∈ s)
    (hK_ne_zero : K ≠ 0)
    (hk_ne_zero :
      ∀ i, i ∈ s → k i ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0)
    (hden_ne_zero :
      ∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ (d * K) - 1) / (b ^ (d * k i) - 1))
    (hweight_le :
      ∀ i, i ∈ s → (k i).factorization q ≤ K.factorization q)
    (hm :
      m = K.factorization q - (k i0).factorization q)
    (hstrict_max :
      ∀ i, i ∈ s → i ≠ i0 →
        (k i).factorization q < (k i0).factorization q)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q := by
  refine maximal_weight_factorization_row_supplies_PrimeComponentWitness
    (s := s)
    (i0 := i0)
    (q := q)
    (M := K.factorization q)
    (m := m)
    (L := L)
    (A := A)
    (b := b)
    (p := p)
    (T := T)
    (w := fun i => (k i).factorization q)
    hq hi0 ?hT_ne_zero ?hrow_val (hweight_le i0 hi0) hm hstrict_max
    hA_eq hpcq_ne_zero hMval
  · intro i hi
    rw [hT i hi]
    exact hquot_ne_zero_rows i hi
  · intro i hi
    rw [hT i hi]
    exact odd_prime_order_component_term_valuation
      (b := b)
      (q := q)
      (d := d)
      (K := K)
      (k := k i)
      hq
      hq_odd
      hcop
      hd_order
      hbase_gt_one
      (hk_ne_zero i hi)
      hK_ne_zero
      (hkK i hi)
      (hquot_ne_zero_rows i hi)
      (hden_ne_zero i hi)

theorem component_term_maximal_row_supplies_PrimeComponentWitness_of_dvd
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b q d K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hi0 : i0 ∈ s)
    (hK_ne_zero : K ≠ 0)
    (hk_ne_zero :
      ∀ i, i ∈ s → k i ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0)
    (hden_ne_zero :
      ∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ (d * K) - 1) / (b ^ (d * k i) - 1))
    (hm :
      m = K.factorization q - (k i0).factorization q)
    (hstrict_max :
      ∀ i, i ∈ s → i ≠ i0 →
        (k i).factorization q < (k i0).factorization q)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q := by
  exact component_term_maximal_row_supplies_PrimeComponentWitness
    (s := s)
    (i0 := i0)
    (b := b)
    (q := q)
    (d := d)
    (K := K)
    (m := m)
    (L := L)
    (A := A)
    (p := p)
    (k := k)
    (T := T)
    hq hq_odd hcop hd_order hbase_gt_one hi0 hK_ne_zero hk_ne_zero
    hkK hquot_ne_zero_rows hden_ne_zero hT
    (fun i hi => factorization_le_of_dvd_ne_zero hK_ne_zero (hkK i hi))
    hm hstrict_max hA_eq hpcq_ne_zero hMval

theorem component_term_maximal_row_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b q d K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hi0 : i0 ∈ s)
    (hK_ne_zero : K ≠ 0)
    (hk_ne_zero :
      ∀ i, i ∈ s → k i ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0)
    (hden_ne_zero :
      ∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ (d * K) - 1) / (b ^ (d * k i) - 1))
    (hweight_le :
      ∀ i, i ∈ s → (k i).factorization q ≤ K.factorization q)
    (hm :
      m = K.factorization q - (k i0).factorization q)
    (hstrict_max :
      ∀ i, i ∈ s → i ≠ i0 →
        (k i).factorization q < (k i0).factorization q)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hW : PrimeComponentWitness L A b p q :=
    component_term_maximal_row_supplies_PrimeComponentWitness
      (s := s)
      (i0 := i0)
      (b := b)
      (q := q)
      (d := d)
      (K := K)
      (m := m)
      (L := L)
      (A := A)
      (p := p)
      (k := k)
      (T := T)
      hq hq_odd hcop hd_order hbase_gt_one hi0 hK_ne_zero hk_ne_zero
      hkK hquot_ne_zero_rows hden_ne_zero hT hweight_le hm hstrict_max
      hA_eq hpcq_ne_zero hMval
  exact valuation_deficit_blocks_dvd hW.1 hW.2.1 hA hW.2.2

theorem odd_component_canonical_row_supplies_PrimeComponentWitness
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b q d K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hi0 : i0 ∈ s)
    (hK_ne_zero : K ≠ 0)
    (hk_ne_zero :
      ∀ i, i ∈ s → k i ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0)
    (hden_ne_zero :
      ∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ (d * K) - 1) / (b ^ (d * k i) - 1))
    (hm :
      m = K.factorization q - (k i0).factorization q)
    (hstrict_max :
      ∀ i, i ∈ s → i ≠ i0 →
        (k i).factorization q < (k i0).factorization q)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    PrimeComponentWitness L A b p q := by
  exact component_term_maximal_row_supplies_PrimeComponentWitness_of_dvd
    (s := s)
    (i0 := i0)
    (b := b)
    (q := q)
    (d := d)
    (K := K)
    (m := m)
    (L := L)
    (A := A)
    (p := p)
    (k := k)
    (T := T)
    hq hq_odd hcop hd_order hbase_gt_one hi0 hK_ne_zero hk_ne_zero
    hkK hquot_ne_zero_rows hden_ne_zero hT hm hstrict_max hA_eq
    hpcq_ne_zero hMval

theorem odd_component_canonical_row_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b q d K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hi0 : i0 ∈ s)
    (hK_ne_zero : K ≠ 0)
    (hk_ne_zero :
      ∀ i, i ∈ s → k i ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0)
    (hden_ne_zero :
      ∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ (d * K) - 1) / (b ^ (d * k i) - 1))
    (hm :
      m = K.factorization q - (k i0).factorization q)
    (hstrict_max :
      ∀ i, i ∈ s → i ≠ i0 →
        (k i).factorization q < (k i0).factorization q)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hW : PrimeComponentWitness L A b p q :=
    odd_component_canonical_row_supplies_PrimeComponentWitness
      (s := s)
      (i0 := i0)
      (b := b)
      (q := q)
      (d := d)
      (K := K)
      (m := m)
      (L := L)
      (A := A)
      (p := p)
      (k := k)
      (T := T)
      hq hq_odd hcop hd_order hbase_gt_one hi0 hK_ne_zero hk_ne_zero
      hkK hquot_ne_zero_rows hden_ne_zero hT hm hstrict_max hA_eq
      hpcq_ne_zero hMval
  exact valuation_deficit_blocks_dvd hW.1 hW.2.1 hA hW.2.2

theorem two_adic_pow_sub_one_factorization_even
    {b n : Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hn_ne_zero : n ≠ 0)
    (hn_even : Even n) :
    (b ^ n - 1).factorization 2 + 1 =
      (b + 1).factorization 2 +
      (b - 1).factorization 2 +
      n.factorization 2 := by
  rw [Nat.factorization_def (b ^ n - 1) Nat.prime_two]
  rw [Nat.factorization_def (b + 1) Nat.prime_two]
  rw [Nat.factorization_def (b - 1) Nat.prime_two]
  rw [Nat.factorization_def n Nat.prime_two]
  exact padicValNat.pow_two_sub_one
    hb_gt_one
    (by
      intro h
      exact (Nat.not_even_iff_odd.mpr hb_odd) ((even_iff_two_dvd).2 h))
    hn_ne_zero
    hn_even

theorem two_adic_pow_sub_one_factorization_odd
    {b k : Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hk_ne_zero : k ≠ 0)
    (hk_odd : Odd k) :
    (b ^ k - 1).factorization 2 =
      (b - 1).factorization 2 := by
  rw [Nat.factorization_def (b ^ k - 1) Nat.prime_two]
  rw [Nat.factorization_def (b - 1) Nat.prime_two]
  apply ENat.coe_inj.mp
  have hpow_gt_one : 1 < b ^ k := Nat.one_lt_pow hk_ne_zero hb_gt_one
  have hpow_ne_zero : b ^ k - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hpow_gt_one
  have hbase_ne_zero : b - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hb_gt_one
  rw [padicValNat_eq_emultiplicity (p := 2) hpow_ne_zero]
  rw [padicValNat_eq_emultiplicity (p := 2) hbase_ne_zero]
  rw [← Int.natCast_emultiplicity 2 (b ^ k - 1)]
  rw [← Int.natCast_emultiplicity 2 (b - 1)]
  have hxy_nat : 2 ∣ b - 1 :=
    even_iff_two_dvd.mp (Nat.Odd.sub_odd hb_odd odd_one)
  have hxy_int : (2 : Int) ∣ (b : Int) - 1 := by
    have hcast : (2 : Int) ∣ ((b - 1 : Nat) : Int) :=
      (Int.natCast_dvd_natCast).2 hxy_nat
    simpa [Int.ofNat_sub (Nat.le_of_lt hb_gt_one)] using hcast
  have hx_int : ¬ (2 : Int) ∣ (b : Int) := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hb_odd)
      ((even_iff_two_dvd).2 ((Int.natCast_dvd_natCast).1 h))
  have hk_int : ¬ (2 : Int) ∣ (k : Int) := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hk_odd)
      ((even_iff_two_dvd).2 ((Int.natCast_dvd_natCast).1 h))
  have hpow_le : 1 ≤ b ^ k := Nat.le_of_lt hpow_gt_one
  have hbase_le : 1 ≤ b := Nat.le_of_lt hb_gt_one
  have hval :
      emultiplicity (2 : Int) ((b : Int) ^ k - (1 : Int) ^ k) =
        emultiplicity (2 : Int) ((b : Int) - (1 : Int)) := by
    exact emultiplicity_pow_sub_pow_of_prime
      (R := Int)
      (p := (2 : Int))
      ((Nat.prime_iff_prime_int).1 Nat.prime_two)
      (x := (b : Int))
      (y := (1 : Int))
      hxy_int
      hx_int
      (n := k)
      hk_int
  simpa [Int.ofNat_sub hpow_le, Int.ofNat_sub hbase_le, Int.natCast_pow] using hval

theorem two_adic_n0_2_selected_component_valuation
    {b K : Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hK_ne_zero : K ≠ 0)
    (hK_even : Even K)
    (h2K : 2 ∣ K)
    (hquot_ne_zero : ((b ^ K - 1) / (b ^ 2 - 1)) ≠ 0)
    (hden_ne_zero : b ^ 2 - 1 ≠ 0) :
    (((b ^ K - 1) / (b ^ 2 - 1)).factorization 2)
      = K.factorization 2 - 1 := by
  have hquot :
      (((b ^ K - 1) / (b ^ 2 - 1)).factorization 2)
        = (b ^ K - 1).factorization 2 - (b ^ 2 - 1).factorization 2 :=
    pow_sub_one_component_factorization
      (b := b)
      (L := K)
      (e := 2)
      (q := 2)
      h2K
      hquot_ne_zero
      hden_ne_zero
  have hnum := two_adic_pow_sub_one_factorization_even
    (b := b) (n := K) hb_gt_one hb_odd hK_ne_zero hK_even
  have hden := two_adic_pow_sub_one_factorization_even
    (b := b) (n := 2) hb_gt_one hb_odd (by decide) (by decide)
  have htwo : (2 : Nat).factorization 2 = 1 := by
    exact Nat.Prime.factorization_self Nat.prime_two
  rw [hquot]
  rw [htwo] at hden
  omega

theorem two_adic_n0_2_exception_supplies_PrimeComponentWitness
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hi0 : i0 ∈ s)
    (hi0_k : k i0 = 2)
    (hK_ne_zero : K ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ K - 1) / (b ^ k i - 1)) ≠ 0)
    (hden_ne_zero : b ^ 2 - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ K - 1) / (b ^ k i - 1))
    (hm :
      m = K.factorization 2 - 1)
    (hhigh_val :
      ∀ i, i ∈ s → i ≠ i0 → m < (T i).factorization 2)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization 2) :
    PrimeComponentWitness L A b p 2 := by
  refine singleton_minimal_factorization_row_supplies_PrimeComponentWitness
    (s := s)
    (i0 := i0)
    (q := 2)
    (m := m)
    (L := L)
    (A := A)
    (b := b)
    (p := p)
    (T := T)
    Nat.prime_two hi0 ?hT_ne_zero ?hi0_val hhigh_val hA_eq hpcq_ne_zero hMval
  · intro i hi
    rw [hT i hi]
    exact hquot_ne_zero_rows i hi
  · rw [hT i0 hi0, hi0_k]
    have h2K : 2 ∣ K := by
      simpa [hi0_k] using hkK i0 hi0
    have hK_even : Even K := (even_iff_two_dvd).2 h2K
    rw [hm]
    exact two_adic_n0_2_selected_component_valuation
      hb_gt_one hb_odd hK_ne_zero hK_even h2K
      (by simpa [hi0_k] using hquot_ne_zero_rows i0 hi0)
      hden_ne_zero

theorem two_adic_n0_2_odd_row_component_valuation_plus_one
    {b K k : Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hK_ne_zero : K ≠ 0)
    (h2K : 2 ∣ K)
    (hk_ne_zero : k ≠ 0)
    (hk_odd : Odd k)
    (hkK : k ∣ K)
    (hquot_ne_zero : ((b ^ K - 1) / (b ^ k - 1)) ≠ 0) :
    (((b ^ K - 1) / (b ^ k - 1)).factorization 2) + 1 =
      (b + 1).factorization 2 + K.factorization 2 := by
  have hK_even : Even K := (even_iff_two_dvd).2 h2K
  have hden_ne_zero : b ^ k - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hk_ne_zero hb_gt_one)
  have hquot :
      (((b ^ K - 1) / (b ^ k - 1)).factorization 2)
        = (b ^ K - 1).factorization 2 - (b ^ k - 1).factorization 2 :=
    pow_sub_one_component_factorization
      (b := b)
      (L := K)
      (e := k)
      (q := 2)
      hkK
      hquot_ne_zero
      hden_ne_zero
  have hnum := two_adic_pow_sub_one_factorization_even
    (b := b) (n := K) hb_gt_one hb_odd hK_ne_zero hK_even
  have hden := two_adic_pow_sub_one_factorization_odd
    (b := b) (k := k) hb_gt_one hb_odd hk_ne_zero hk_odd
  have hplus_pos : 0 < (b + 1).factorization 2 := by
    have htwo_dvd : 2 ∣ b + 1 :=
      even_iff_two_dvd.mp (Odd.add_odd hb_odd odd_one)
    have hb1_ne_zero : b + 1 ≠ 0 := by omega
    exact Nat.prime_two.factorization_pos_of_dvd hb1_ne_zero htwo_dvd
  have hbase_le_num : (b - 1).factorization 2 ≤ (b ^ K - 1).factorization 2 := by
    omega
  rw [hquot, hden]
  omega

theorem two_adic_n0_2_odd_row_component_high_valuation
    {b K k m : Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hK_ne_zero : K ≠ 0)
    (h2K : 2 ∣ K)
    (hk_ne_zero : k ≠ 0)
    (hk_odd : Odd k)
    (hkK : k ∣ K)
    (hquot_ne_zero : ((b ^ K - 1) / (b ^ k - 1)) ≠ 0)
    (hm : m = K.factorization 2 - 1) :
    m < (((b ^ K - 1) / (b ^ k - 1)).factorization 2) := by
  have hplus := two_adic_n0_2_odd_row_component_valuation_plus_one
    (b := b) (K := K) (k := k)
    hb_gt_one hb_odd hK_ne_zero h2K hk_ne_zero hk_odd hkK hquot_ne_zero
  have hplus_pos : 0 < (b + 1).factorization 2 := by
    have htwo_dvd : 2 ∣ b + 1 :=
      even_iff_two_dvd.mp (Odd.add_odd hb_odd odd_one)
    have hb1_ne_zero : b + 1 ≠ 0 := by omega
    exact Nat.prime_two.factorization_pos_of_dvd hb1_ne_zero htwo_dvd
  have hKf_pos : 0 < K.factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd hK_ne_zero h2K
  rw [hm]
  omega

theorem two_adic_n0_2_exception_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hi0 : i0 ∈ s)
    (hi0_k : k i0 = 2)
    (hK_ne_zero : K ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ K - 1) / (b ^ k i - 1)) ≠ 0)
    (hden_ne_zero : b ^ 2 - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ K - 1) / (b ^ k i - 1))
    (hm :
      m = K.factorization 2 - 1)
    (hhigh_val :
      ∀ i, i ∈ s → i ≠ i0 → m < (T i).factorization 2)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization 2) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hW : PrimeComponentWitness L A b p 2 :=
    two_adic_n0_2_exception_supplies_PrimeComponentWitness
      (s := s)
      (i0 := i0)
      (b := b)
      (K := K)
      (m := m)
      (L := L)
      (A := A)
      (p := p)
      (k := k)
      (T := T)
      hb_gt_one hb_odd hi0 hi0_k hK_ne_zero hkK hquot_ne_zero_rows
      hden_ne_zero hT hm hhigh_val hA_eq hpcq_ne_zero hMval
  exact valuation_deficit_blocks_dvd hW.1 hW.2.1 hA hW.2.2

theorem two_adic_n0_2_exception_supplies_PrimeComponentWitness_of_odd_rows
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hi0 : i0 ∈ s)
    (hi0_k : k i0 = 2)
    (hK_ne_zero : K ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hother_odd :
      ∀ i, i ∈ s → i ≠ i0 → Odd (k i))
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ K - 1) / (b ^ k i - 1)) ≠ 0)
    (hden_ne_zero : b ^ 2 - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ K - 1) / (b ^ k i - 1))
    (hm :
      m = K.factorization 2 - 1)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization 2) :
    PrimeComponentWitness L A b p 2 := by
  refine two_adic_n0_2_exception_supplies_PrimeComponentWitness
    (s := s)
    (i0 := i0)
    (b := b)
    (K := K)
    (m := m)
    (L := L)
    (A := A)
    (p := p)
    (k := k)
    (T := T)
    hb_gt_one hb_odd hi0 hi0_k hK_ne_zero hkK hquot_ne_zero_rows
    hden_ne_zero hT hm ?hhigh_val hA_eq hpcq_ne_zero hMval
  intro i hi hne
  rw [hT i hi]
  have h2K : 2 ∣ K := by
    simpa [hi0_k] using hkK i0 hi0
  have hki_ne_zero : k i ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Odd.pos (hother_odd i hi hne))
  exact two_adic_n0_2_odd_row_component_high_valuation
    (b := b)
    (K := K)
    (k := k i)
    (m := m)
    hb_gt_one
    hb_odd
    hK_ne_zero
    h2K
    hki_ne_zero
    (hother_odd i hi hne)
    (hkK i hi)
    (hquot_ne_zero_rows i hi)
    hm

theorem two_adic_n0_2_exception_blocks_collapse_of_odd_rows
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hi0 : i0 ∈ s)
    (hi0_k : k i0 = 2)
    (hK_ne_zero : K ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hother_odd :
      ∀ i, i ∈ s → i ≠ i0 → Odd (k i))
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ K - 1) / (b ^ k i - 1)) ≠ 0)
    (hden_ne_zero : b ^ 2 - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ K - 1) / (b ^ k i - 1))
    (hm :
      m = K.factorization 2 - 1)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization 2) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hW : PrimeComponentWitness L A b p 2 :=
    two_adic_n0_2_exception_supplies_PrimeComponentWitness_of_odd_rows
      (s := s)
      (i0 := i0)
      (b := b)
      (K := K)
      (m := m)
      (L := L)
      (A := A)
      (p := p)
      (k := k)
      (T := T)
      hb_gt_one hb_odd hi0 hi0_k hK_ne_zero hkK hother_odd
      hquot_ne_zero_rows hden_ne_zero hT hm hA_eq hpcq_ne_zero hMval
  exact valuation_deficit_blocks_dvd hW.1 hW.2.1 hA hW.2.2

theorem zsigmondy_exception_blocks_collapse_of_odd_rows
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hi0 : i0 ∈ s)
    (hi0_k : k i0 = 2)
    (hK_ne_zero : K ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hother_odd :
      ∀ i, i ∈ s → i ≠ i0 → Odd (k i))
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ K - 1) / (b ^ k i - 1)) ≠ 0)
    (hden_ne_zero : b ^ 2 - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ K - 1) / (b ^ k i - 1))
    (hm :
      m = K.factorization 2 - 1)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization 2) :
    ¬ primeComponentQuotient b L p ∣ A :=
  two_adic_n0_2_exception_blocks_collapse_of_odd_rows
    (s := s)
    (i0 := i0)
    (b := b)
    (K := K)
    (m := m)
    (L := L)
    (A := A)
    (p := p)
    (k := k)
    (T := T)
    hb_gt_one hb_odd hi0 hi0_k hK_ne_zero hkK hother_odd
    hquot_ne_zero_rows hden_ne_zero hT hm hA hA_eq hpcq_ne_zero hMval

theorem zsigmondy_exception_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hb_gt_one : 1 < b)
    (hb_odd : Odd b)
    (hi0 : i0 ∈ s)
    (hi0_k : k i0 = 2)
    (hK_ne_zero : K ≠ 0)
    (hkK :
      ∀ i, i ∈ s → k i ∣ K)
    (hquot_ne_zero_rows :
      ∀ i, i ∈ s →
        ((b ^ K - 1) / (b ^ k i - 1)) ≠ 0)
    (hden_ne_zero : b ^ 2 - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ s →
        T i = (b ^ K - 1) / (b ^ k i - 1))
    (hm :
      m = K.factorization 2 - 1)
    (hhigh_val :
      ∀ i, i ∈ s → i ≠ i0 → m < (T i).factorization 2)
    (hA : A ≠ 0)
    (hA_eq :
      A = ∑ i ∈ s, T i)
    (hpcq_ne_zero :
      primeComponentQuotient b L p ≠ 0)
    (hMval :
      m < (primeComponentQuotient b L p).factorization 2) :
    ¬ primeComponentQuotient b L p ∣ A :=
  two_adic_n0_2_exception_blocks_collapse
    (s := s)
    (i0 := i0)
    (b := b)
    (K := K)
    (m := m)
    (L := L)
    (A := A)
    (p := p)
    (k := k)
    (T := T)
    hb_gt_one hb_odd hi0 hi0_k hK_ne_zero hkK hquot_ne_zero_rows
    hden_ne_zero hT hm hhigh_val hA hA_eq hpcq_ne_zero hMval

def OddComponentCanonicalCase
    (L A b p q : Nat) : Prop :=
  ∃ (ι : Type) (_ : DecidableEq ι)
      (s : Finset ι) (i0 : ι)
      (d K m : Nat)
      (k : ι → Nat) (T : ι → Nat),
    Nat.Prime q ∧
      Odd q ∧
      ∃ hcop : Nat.Coprime b q,
      d = orderOf (ZMod.unitOfCoprime b hcop) ∧
      1 < b ^ d ∧
      i0 ∈ s ∧
      K ≠ 0 ∧
      (∀ i, i ∈ s → k i ≠ 0) ∧
      (∀ i, i ∈ s → k i ∣ K) ∧
      (∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0) ∧
      (∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0) ∧
      (∀ i, i ∈ s →
        T i = (b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ∧
      m = K.factorization q - (k i0).factorization q ∧
      (∀ i, i ∈ s → i ≠ i0 →
        (k i).factorization q < (k i0).factorization q) ∧
      A = ∑ i ∈ s, T i ∧
      primeComponentQuotient b L p ≠ 0 ∧
      m < (primeComponentQuotient b L p).factorization q

def Q2ExceptionCanonicalCase
    (L A b p : Nat) : Prop :=
  ∃ (ι : Type) (_ : DecidableEq ι)
      (s : Finset ι) (i0 : ι)
      (K m : Nat)
      (k : ι → Nat) (T : ι → Nat),
    1 < b ∧
      Odd b ∧
      i0 ∈ s ∧
      k i0 = 2 ∧
      K ≠ 0 ∧
      (∀ i, i ∈ s → k i ∣ K) ∧
      (∀ i, i ∈ s → i ≠ i0 → Odd (k i)) ∧
      (∀ i, i ∈ s →
        ((b ^ K - 1) / (b ^ k i - 1)) ≠ 0) ∧
      b ^ 2 - 1 ≠ 0 ∧
      (∀ i, i ∈ s →
        T i = (b ^ K - 1) / (b ^ k i - 1)) ∧
      m = K.factorization 2 - 1 ∧
      A = ∑ i ∈ s, T i ∧
      primeComponentQuotient b L p ≠ 0 ∧
      m < (primeComponentQuotient b L p).factorization 2

def CanonicalWitnessRowCase
    (L A b p : Nat) : Prop :=
  (∃ q, OddComponentCanonicalCase L A b p q) ∨
    Q2ExceptionCanonicalCase L A b p ∨
      ∃ q, PrimeComponentWitness L A b p q

theorem odd_component_canonical_case_supplies_PrimeComponentWitness
    {L A b p q : Nat}
    (hcase : OddComponentCanonicalCase L A b p q) :
    PrimeComponentWitness L A b p q := by
  rcases hcase with
    ⟨ι, hdec, s, i0, d, K, m, k, T, hq, hq_odd, hcop,
      hd_order, hbase_gt_one, hi0, hK_ne_zero, hk_ne_zero, hkK,
      hquot_ne_zero_rows, hden_ne_zero, hT, hm, hstrict_max,
      hA_eq, hpcq_ne_zero, hMval⟩
  letI := hdec
  exact odd_component_canonical_row_supplies_PrimeComponentWitness
    (s := s)
    (i0 := i0)
    (b := b)
    (q := q)
    (d := d)
    (K := K)
    (m := m)
    (L := L)
    (A := A)
    (p := p)
    (k := k)
    (T := T)
    hq hq_odd hcop hd_order hbase_gt_one hi0 hK_ne_zero hk_ne_zero
    hkK hquot_ne_zero_rows hden_ne_zero hT hm hstrict_max hA_eq
    hpcq_ne_zero hMval

theorem q2_exception_canonical_case_supplies_PrimeComponentWitness
    {L A b p : Nat}
    (hcase : Q2ExceptionCanonicalCase L A b p) :
    PrimeComponentWitness L A b p 2 := by
  rcases hcase with
    ⟨ι, hdec, s, i0, K, m, k, T, hb_gt_one, hb_odd, hi0,
      hi0_k, hK_ne_zero, hkK, hother_odd, hquot_ne_zero_rows,
      hden_ne_zero, hT, hm, hA_eq, hpcq_ne_zero, hMval⟩
  letI := hdec
  exact two_adic_n0_2_exception_supplies_PrimeComponentWitness_of_odd_rows
    (s := s)
    (i0 := i0)
    (b := b)
    (K := K)
    (m := m)
    (L := L)
    (A := A)
    (p := p)
    (k := k)
    (T := T)
    hb_gt_one hb_odd hi0 hi0_k hK_ne_zero hkK hother_odd
    hquot_ne_zero_rows hden_ne_zero hT hm hA_eq hpcq_ne_zero hMval

theorem CanonicalWitnessRowCase.supplies_PrimeComponentWitness
    {L A b p : Nat}
    (hcase : CanonicalWitnessRowCase L A b p) :
    ∃ q, PrimeComponentWitness L A b p q := by
  rcases hcase with hodd | hq2_or_direct
  · rcases hodd with ⟨q, hcase⟩
    exact ⟨q, odd_component_canonical_case_supplies_PrimeComponentWitness hcase⟩
  · rcases hq2_or_direct with hq2 | hdirect
    · exact ⟨2, q2_exception_canonical_case_supplies_PrimeComponentWitness hq2⟩
    · exact hdirect

theorem canonical_witness_singleton_minimality_supplies_witness_existence
    {L A b : Nat}
    (hcase :
      ∀ p, Nat.Prime p → p ∣ L →
        CanonicalWitnessRowCase L A b p) :
    ∀ p, Nat.Prime p → p ∣ L →
      ∃ q, PrimeComponentWitness L A b p q := by
  intro p hp hpL
  exact CanonicalWitnessRowCase.supplies_PrimeComponentWitness
    (hcase p hp hpL)

theorem finite_period_noncollapse_from_witness_route
    (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    (hcase :
      ∀ p, Nat.Prime p → p ∣ L →
        CanonicalWitnessRowCase L A b p) :
    orderOf (ZMod.unitOfCoprime b hcop) = L :=
  witness_existence_implies_period_noncollapse
    L A B Q b hcop hLpos hA h_ord_dvd_L hQpos hQ hB_eq hpow
    (canonical_witness_singleton_minimality_supplies_witness_existence hcase)

def FiniteCanonicalWitnessRows
    (L A b : Nat) : Prop :=
  ∃ rows : Finset Nat,
    (∀ p, Nat.Prime p → p ∣ L → p ∈ rows) ∧
      (∀ p, p ∈ rows → CanonicalWitnessRowCase L A b p)

theorem finite_certificate_rows_supply_CanonicalWitnessRowCase
    {L A b : Nat}
    (hrows : FiniteCanonicalWitnessRows L A b) :
    ∀ p, Nat.Prime p → p ∣ L →
      CanonicalWitnessRowCase L A b p := by
  intro p hp hpL
  rcases hrows with ⟨rows, hcover, hcase⟩
  exact hcase p (hcover p hp hpL)

theorem finite_period_noncollapse_from_residue_shapes
    (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    (hrows : FiniteCanonicalWitnessRows L A b) :
    orderOf (ZMod.unitOfCoprime b hcop) = L :=
  finite_period_noncollapse_from_witness_route
    L A B Q b hcop hLpos hA h_ord_dvd_L hQpos hQ hB_eq hpow
    (finite_certificate_rows_supply_CanonicalWitnessRowCase hrows)

def GeneratedFiniteCanonicalWitnessRows
    (L A b : Nat) : Prop :=
  L ≠ 0 ∧
    ∀ p, p ∈ L.factorization.support →
      CanonicalWitnessRowCase L A b p

theorem generated_finite_certificate_rows_supply_FiniteCanonicalWitnessRows
    {L A b : Nat}
    (hrows : GeneratedFiniteCanonicalWitnessRows L A b) :
    FiniteCanonicalWitnessRows L A b := by
  rcases hrows with ⟨hL_ne_zero, hcase⟩
  refine ⟨L.factorization.support, ?cover, hcase⟩
  intro p hp hpL
  have hpos : 0 < L.factorization p :=
    hp.factorization_pos_of_dvd hL_ne_zero hpL
  exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hpos)

theorem finite_period_noncollapse_from_generated_finite_rows
    (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    (hrows : GeneratedFiniteCanonicalWitnessRows L A b) :
    orderOf (ZMod.unitOfCoprime b hcop) = L :=
  finite_period_noncollapse_from_residue_shapes
    L A B Q b hcop hLpos hA h_ord_dvd_L hQpos hQ hB_eq hpow
    (generated_finite_certificate_rows_supply_FiniteCanonicalWitnessRows hrows)

theorem generated_support_table_supplies_GeneratedFiniteCanonicalWitnessRows
    {L A b : Nat}
    {rows : Finset Nat}
    (hL_ne_zero : L ≠ 0)
    (hcover : ∀ p, p ∈ L.factorization.support → p ∈ rows)
    (hcase : ∀ p, p ∈ rows → CanonicalWitnessRowCase L A b p) :
    GeneratedFiniteCanonicalWitnessRows L A b := by
  refine ⟨hL_ne_zero, ?_⟩
  intro p hp
  exact hcase p (hcover p hp)

inductive EmittedGeneratedRowCase
    (L A b p : Nat) : Prop
| odd_component
    {q : Nat}
    (hodd : OddComponentCanonicalCase L A b p q) :
    EmittedGeneratedRowCase L A b p
| q2_exception
    (hq2 : Q2ExceptionCanonicalCase L A b p) :
    EmittedGeneratedRowCase L A b p
| prime_witness
    {q : Nat}
    (hwit : PrimeComponentWitness L A b p q) :
    EmittedGeneratedRowCase L A b p

theorem EmittedGeneratedRowCase.supplies_CanonicalWitnessRowCase
    {L A b p : Nat}
    (hrow : EmittedGeneratedRowCase L A b p) :
    CanonicalWitnessRowCase L A b p := by
  cases hrow with
  | odd_component hodd =>
      exact Or.inl ⟨_, hodd⟩
  | q2_exception hq2 =>
      exact Or.inr (Or.inl hq2)
  | prime_witness hwit =>
      exact Or.inr (Or.inr ⟨_, hwit⟩)

theorem emitted_generated_row_table_supplies_GeneratedFiniteCanonicalWitnessRows
    {L A b : Nat}
    {rows : Finset Nat}
    (hL_ne_zero : L ≠ 0)
    (hcover : ∀ p, p ∈ L.factorization.support → p ∈ rows)
    (hrow : ∀ p, p ∈ rows → EmittedGeneratedRowCase L A b p) :
    GeneratedFiniteCanonicalWitnessRows L A b := by
  exact generated_support_table_supplies_GeneratedFiniteCanonicalWitnessRows
    hL_ne_zero hcover
    (fun p hp =>
      EmittedGeneratedRowCase.supplies_CanonicalWitnessRowCase (hrow p hp))

structure EmittedCertificateTable
    (L A b : Nat) where
  rows : Finset Nat
  L_ne_zero : L ≠ 0
  covers_factor_support :
    ∀ p, p ∈ L.factorization.support → p ∈ rows
  row_sound :
    ∀ p, p ∈ rows → EmittedGeneratedRowCase L A b p

theorem emitted_certificate_table_supplies_generated_finite_rows
    {L A b : Nat}
    (cert : EmittedCertificateTable L A b) :
    GeneratedFiniteCanonicalWitnessRows L A b :=
  emitted_generated_row_table_supplies_GeneratedFiniteCanonicalWitnessRows
    cert.L_ne_zero cert.covers_factor_support cert.row_sound

theorem emitted_row_object_projection_or_broader_generated_table_route
    {L A b : Nat}
    {rows : Finset Nat}
    (hL_ne_zero : L ≠ 0)
    (hcover : ∀ p, p ∈ L.factorization.support → p ∈ rows)
    (hrow : ∀ p, p ∈ rows → EmittedGeneratedRowCase L A b p) :
    GeneratedFiniteCanonicalWitnessRows L A b :=
  emitted_generated_row_table_supplies_GeneratedFiniteCanonicalWitnessRows
    hL_ne_zero hcover hrow

theorem finite_period_noncollapse_from_emitted_certificate_table
    (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    (cert : EmittedCertificateTable L A b) :
    orderOf (ZMod.unitOfCoprime b hcop) = L :=
  finite_period_noncollapse_from_generated_finite_rows
    L A B Q b hcop hLpos hA h_ord_dvd_L hQpos hQ hB_eq hpow
    (emitted_certificate_table_supplies_generated_finite_rows cert)

theorem finite_period_noncollapse_from_emitted_generated_row_table
    (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    {rows : Finset Nat}
    (hL_ne_zero : L ≠ 0)
    (hcover : ∀ p, p ∈ L.factorization.support → p ∈ rows)
    (hrow : ∀ p, p ∈ rows → EmittedGeneratedRowCase L A b p) :
    orderOf (ZMod.unitOfCoprime b hcop) = L :=
  finite_period_noncollapse_from_emitted_certificate_table
    L A B Q b hcop hLpos hA h_ord_dvd_L hQpos hQ hB_eq hpow
    { rows := rows
      L_ne_zero := hL_ne_zero
      covers_factor_support := hcover
      row_sound := hrow }

theorem concrete_generated_b2_F2_orderOf
    (hcop : Nat.Coprime 2 3) :
    orderOf (ZMod.unitOfCoprime 2 hcop) = 2 := by
  rw [orderOf_eq_prime_iff]
  constructor
  · apply Units.ext
    change (((ZMod.unitOfCoprime 2 hcop : (ZMod 3)ˣ) : ZMod 3) ^ 2) =
      (1 : ZMod 3)
    rw [ZMod.coe_unitOfCoprime]
    decide
  · intro h
    have hv := congrArg Units.val h
    change ((ZMod.unitOfCoprime 2 hcop : (ZMod 3)ˣ).val) =
      (1 : (ZMod 3)ˣ).val at hv
    rw [ZMod.coe_unitOfCoprime] at hv
    revert hv
    decide

theorem concrete_generated_b2_F2_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (2 : Nat).factorization.support) :
    p = 2 := by
  rw [Nat.support_factorization] at hp
  exact (Nat.prime_dvd_prime_iff_eq
    (Nat.prime_of_mem_primeFactors hp)
    (by decide : Nat.Prime 2)).mp
    ((Nat.mem_primeFactors.mp hp).2.1)

theorem concrete_generated_b2_F2_odd_component_case :
    OddComponentCanonicalCase 2 1 2 2 3 := by
  refine ⟨Unit, inferInstance, ({() } : Finset Unit), (), 2, 1, 0,
    (fun _ : Unit => 1), (fun _ : Unit => 1), ?_⟩
  refine ⟨(by decide : Nat.Prime 3), (by decide : Odd 3), ?_⟩
  refine ⟨(by decide : Nat.Coprime 2 3), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (concrete_generated_b2_F2_orderOf (by decide : Nat.Coprime 2 3)).symm
  · decide
  · simp
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · simp [Nat.factorization_one]
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 2 2 = 3 := by decide
    rw [hquot]
    rw [Nat.Prime.factorization_self (by decide : Nat.Prime 3)]
    decide

theorem concrete_generated_b2_F2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 2 1 2 2 := by
  exact Or.inl ⟨3, concrete_generated_b2_F2_odd_component_case⟩

theorem concrete_generated_finite_certificate_rows_supply_GeneratedFiniteCanonicalWitnessRows :
    GeneratedFiniteCanonicalWitnessRows 2 1 2 := by
  refine ⟨by decide, ?_⟩
  intro p hp
  have hp_eq : p = 2 := concrete_generated_b2_F2_factorization_support_cases hp
  subst p
  exact concrete_generated_b2_F2_CanonicalWitnessRowCase

theorem finite_period_noncollapse_from_concrete_generated_rows :
    orderOf (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 3)) = 2 := by
  let hcop : Nat.Coprime 2 3 := by decide
  exact finite_period_noncollapse_from_generated_finite_rows
    2 1 3 3 2 hcop
    (by decide)
    (by decide)
    (by rw [concrete_generated_b2_F2_orderOf hcop])
    (by decide)
    (by decide)
    (by decide)
    (by rw [concrete_generated_b2_F2_orderOf hcop]; decide)
    concrete_generated_finite_certificate_rows_supply_GeneratedFiniteCanonicalWitnessRows

theorem concrete_generated_b3_F2_q2_exception_case :
    Q2ExceptionCanonicalCase 2 1 3 2 := by
  refine ⟨Unit, inferInstance, ({() } : Finset Unit), (), 2, 0,
    (fun _ : Unit => 2), (fun _ : Unit => 1), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · simp
  · decide
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · have hfactorK : (2 : Nat).factorization 2 = 1 := by
      rw [show (2 : Nat) = 2 ^ 1 by decide]
      exact Nat.factorization_pow_self (by decide : Nat.Prime 2)
    rw [hfactorK]
  · decide
  · decide
  · have hquot : primeComponentQuotient 3 2 2 = 4 := by decide
    rw [hquot]
    have hfactor : (4 : Nat).factorization 2 = 2 := by
      rw [show (4 : Nat) = 2 ^ 2 by decide]
      exact Nat.factorization_pow_self (by decide : Nat.Prime 2)
    rw [hfactor]
    decide

theorem concrete_generated_b3_F2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 2 1 3 2 := by
  exact Or.inr (Or.inl concrete_generated_b3_F2_q2_exception_case)

theorem additional_generated_finite_certificate_rows_supply_GeneratedFiniteCanonicalWitnessRows :
    GeneratedFiniteCanonicalWitnessRows 2 1 3 := by
  refine generated_support_table_supplies_GeneratedFiniteCanonicalWitnessRows
    (L := 2)
    (A := 1)
    (b := 3)
    (rows := ({2} : Finset Nat))
    ?_ ?_ ?_
  · decide
  · intro p hp
    have hp_eq : p = 2 := concrete_generated_b2_F2_factorization_support_cases hp
    subst p
    simp
  · intro p hp
    have hp_eq : p = 2 := Finset.mem_singleton.mp hp
    subst p
    exact concrete_generated_b3_F2_CanonicalWitnessRowCase

theorem concrete_generated_b2_F6_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (6 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 6 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 6 := Nat.le_of_dvd (by decide : 0 < 6) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 6) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)

theorem concrete_generated_b2_F6_p2_odd_component_case :
    OddComponentCanonicalCase 6 1 2 2 3 := by
  refine ⟨Unit, inferInstance, ({() } : Finset Unit), (), 2, 1, 0,
    (fun _ : Unit => 1), (fun _ : Unit => 1), ?_⟩
  refine ⟨(by decide : Nat.Prime 3), (by decide : Odd 3), ?_⟩
  refine ⟨(by decide : Nat.Coprime 2 3), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (concrete_generated_b2_F2_orderOf (by decide : Nat.Coprime 2 3)).symm
  · decide
  · simp
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · simp [Nat.factorization_one]
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 6 2 = 9 := by decide
    rw [hquot]
    have hfactor : (9 : Nat).factorization 3 = 2 := by
      rw [show (9 : Nat) = 3 ^ 2 by decide]
      exact Nat.factorization_pow_self (by decide : Nat.Prime 3)
    rw [hfactor]
    decide

theorem concrete_generated_b2_F6_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 1 2 2 := by
  exact Or.inl ⟨3, concrete_generated_b2_F6_p2_odd_component_case⟩

theorem concrete_generated_b2_F6_p3_orderOf
    (hcop : Nat.Coprime 2 7) :
    orderOf (ZMod.unitOfCoprime 2 hcop) = 3 := by
  rw [orderOf_eq_prime_iff]
  constructor
  · apply Units.ext
    change (((ZMod.unitOfCoprime 2 hcop : (ZMod 7)ˣ) : ZMod 7) ^ 3) =
      (1 : ZMod 7)
    rw [ZMod.coe_unitOfCoprime]
    decide
  · intro h
    have hv := congrArg Units.val h
    change ((ZMod.unitOfCoprime 2 hcop : (ZMod 7)ˣ).val) =
      (1 : (ZMod 7)ˣ).val at hv
    rw [ZMod.coe_unitOfCoprime] at hv
    revert hv
    decide

theorem concrete_generated_b2_F6_p3_odd_component_case :
    OddComponentCanonicalCase 6 1 2 3 7 := by
  refine ⟨Unit, inferInstance, ({() } : Finset Unit), (), 3, 1, 0,
    (fun _ : Unit => 1), (fun _ : Unit => 1), ?_⟩
  refine ⟨(by decide : Nat.Prime 7), (by decide : Odd 7), ?_⟩
  refine ⟨(by decide : Nat.Coprime 2 7), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (concrete_generated_b2_F6_p3_orderOf (by decide : Nat.Coprime 2 7)).symm
  · decide
  · simp
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · simp [Nat.factorization_one]
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 6 3 = 21 := by decide
    rw [hquot]
    have hfactor : (21 : Nat).factorization 7 = 1 := by
      rw [show (21 : Nat) = 7 * 3 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 7),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 3),
      ]
    rw [hfactor]
    decide

theorem concrete_generated_b2_F6_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 1 2 3 := by
  exact Or.inl ⟨7, concrete_generated_b2_F6_p3_odd_component_case⟩

theorem multi_support_generated_fixture_or_emitter_row_projection :
    GeneratedFiniteCanonicalWitnessRows 6 1 2 := by
  refine generated_support_table_supplies_GeneratedFiniteCanonicalWitnessRows
    (L := 6)
    (A := 1)
    (b := 2)
    (rows := ({2, 3} : Finset Nat))
    ?_ ?_ ?_
  · decide
  · intro p hp
    rcases concrete_generated_b2_F6_factorization_support_cases hp with rfl | rfl <;>
      simp
  · intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact concrete_generated_b2_F6_p2_CanonicalWitnessRowCase
    · subst p
      exact concrete_generated_b2_F6_p3_CanonicalWitnessRowCase

def emittedCertificate_b2_L6_A1 :
    EmittedCertificateTable 6 1 2 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F6_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.odd_component
        concrete_generated_b2_F6_p2_odd_component_case
    · subst p
      exact EmittedGeneratedRowCase.odd_component
        concrete_generated_b2_F6_p3_odd_component_case

theorem orderOf_b2_mod63_eq_6_from_emittedCertificate :
    orderOf (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 63)) = 6 := by
  let hcop : Nat.Coprime 2 63 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 6 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 6 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 63)ˣ) : ZMod 63) ^ 6) =
        (1 : ZMod 63)
      rw [ZMod.coe_unitOfCoprime]
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    6 1 63 63 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L6_A1

theorem finite_period_noncollapse_from_multi_support_generated_rows :
    orderOf (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 63)) = 6 :=
  orderOf_b2_mod63_eq_6_from_emittedCertificate

theorem concrete_generated_b2_F10_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (10 : Nat).factorization.support) :
    p = 2 ∨ p = 5 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 10 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 10 := Nat.le_of_dvd (by decide : 0 < 10) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact False.elim ((by decide : ¬ 3 ∣ 10) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 10) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)

theorem concrete_generated_b2_F10_p2_odd_component_case :
    OddComponentCanonicalCase 10 1 2 2 3 := by
  refine ⟨Unit, inferInstance, ({() } : Finset Unit), (), 2, 1, 0,
    (fun _ : Unit => 1), (fun _ : Unit => 1), ?_⟩
  refine ⟨(by decide : Nat.Prime 3), (by decide : Odd 3), ?_⟩
  refine ⟨(by decide : Nat.Coprime 2 3), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (concrete_generated_b2_F2_orderOf (by decide : Nat.Coprime 2 3)).symm
  · decide
  · simp
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · simp [Nat.factorization_one]
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 10 2 = 33 := by decide
    rw [hquot]
    have hfactor : (33 : Nat).factorization 3 = 1 := by
      rw [show (33 : Nat) = 3 * 11 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 3),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 11),
      ]
    rw [hfactor]
    decide

theorem concrete_generated_b2_F10_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 10 1 2 2 := by
  exact Or.inl ⟨3, concrete_generated_b2_F10_p2_odd_component_case⟩

theorem concrete_generated_b2_F10_p5_orderOf
    (hcop : Nat.Coprime 2 11) :
    orderOf (ZMod.unitOfCoprime 2 hcop) = 10 := by
  rw [orderOf_eq_iff (by decide : 0 < 10)]
  constructor
  · apply Units.ext
    change (((ZMod.unitOfCoprime 2 hcop : (ZMod 11)ˣ) : ZMod 11) ^ 10) =
      (1 : ZMod 11)
    rw [ZMod.coe_unitOfCoprime]
    decide
  · intro m hm hpos
    interval_cases m <;> intro h
    all_goals
      have hv := congrArg Units.val h
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 11)ˣ) : ZMod 11) ^ _) =
        (1 : ZMod 11) at hv
      rw [ZMod.coe_unitOfCoprime] at hv
      revert hv
      decide

theorem concrete_generated_b2_F10_p5_odd_component_case :
    OddComponentCanonicalCase 10 1 2 5 11 := by
  refine ⟨Unit, inferInstance, ({() } : Finset Unit), (), 10, 1, 0,
    (fun _ : Unit => 1), (fun _ : Unit => 1), ?_⟩
  refine ⟨(by decide : Nat.Prime 11), (by decide : Odd 11), ?_⟩
  refine ⟨(by decide : Nat.Coprime 2 11), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (concrete_generated_b2_F10_p5_orderOf
      (by decide : Nat.Coprime 2 11)).symm
  · decide
  · simp
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · simp [Nat.factorization_one]
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 10 5 = 341 := by decide
    rw [hquot]
    have hfactor : (341 : Nat).factorization 11 = 1 := by
      rw [show (341 : Nat) = 11 * 31 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 11),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 31),
      ]
    rw [hfactor]
    decide

theorem concrete_generated_b2_F10_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 10 1 2 5 := by
  exact Or.inl ⟨11, concrete_generated_b2_F10_p5_odd_component_case⟩

def emittedCertificate_b2_L10_A1 :
    EmittedCertificateTable 10 1 2 where
  rows := ({2, 5} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F10_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.odd_component
        concrete_generated_b2_F10_p2_odd_component_case
    · subst p
      exact EmittedGeneratedRowCase.odd_component
        concrete_generated_b2_F10_p5_odd_component_case

theorem orderOf_b2_mod1023_eq_10_from_emittedCertificate :
    orderOf (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 1023)) = 10 := by
  let hcop : Nat.Coprime 2 1023 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 10 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 10 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 1023)ˣ) : ZMod 1023) ^ 10) =
        (1 : ZMod 1023)
      rw [ZMod.coe_unitOfCoprime]
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    10 1 1023 1023 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L10_A1

theorem concrete_generated_b2_F30_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (30 : Nat).factorization.support) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 30 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 30 := Nat.le_of_dvd (by decide : 0 < 30) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact Or.inr (Or.inr rfl)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 30) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 30) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)
  · exact False.elim ((by decide : ¬ 13 ∣ 30) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 14) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 15) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 16) hp_prime)
  · exact False.elim ((by decide : ¬ 17 ∣ 30) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 18) hp_prime)
  · exact False.elim ((by decide : ¬ 19 ∣ 30) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 20) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 21) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 22) hp_prime)
  · exact False.elim ((by decide : ¬ 23 ∣ 30) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 24) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 25) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 26) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 27) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 28) hp_prime)
  · exact False.elim ((by decide : ¬ 29 ∣ 30) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 30) hp_prime)

theorem concrete_generated_b2_F30_p2_odd_component_case :
    OddComponentCanonicalCase 30 1 2 2 3 := by
  refine ⟨Unit, inferInstance, ({() } : Finset Unit), (), 2, 1, 0,
    (fun _ : Unit => 1), (fun _ : Unit => 1), ?_⟩
  refine ⟨(by decide : Nat.Prime 3), (by decide : Odd 3), ?_⟩
  refine ⟨(by decide : Nat.Coprime 2 3), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (concrete_generated_b2_F2_orderOf (by decide : Nat.Coprime 2 3)).symm
  · decide
  · simp
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · simp [Nat.factorization_one]
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 30 2 = 32769 := by decide
    rw [hquot]
    have hfactor : (32769 : Nat).factorization 3 = 2 := by
      rw [show (32769 : Nat) = 3 ^ 2 * 3641 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      change (3 ^ 2 : Nat).factorization 3 + (3641 : Nat).factorization 3 = 2
      have hfactor_left : (3 ^ 2 : Nat).factorization 3 = 2 :=
        Nat.factorization_pow_self (by decide : Nat.Prime 3)
      have hfactor_right : (3641 : Nat).factorization 3 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 3641)
      rw [hfactor_left, hfactor_right]
    rw [hfactor]
    decide

theorem concrete_generated_b2_F30_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 30 1 2 2 := by
  exact Or.inl ⟨3, concrete_generated_b2_F30_p2_odd_component_case⟩

theorem concrete_generated_b2_F30_p3_odd_component_case :
    OddComponentCanonicalCase 30 1 2 3 7 := by
  refine ⟨Unit, inferInstance, ({() } : Finset Unit), (), 3, 1, 0,
    (fun _ : Unit => 1), (fun _ : Unit => 1), ?_⟩
  refine ⟨(by decide : Nat.Prime 7), (by decide : Odd 7), ?_⟩
  refine ⟨(by decide : Nat.Coprime 2 7), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (concrete_generated_b2_F6_p3_orderOf (by decide : Nat.Coprime 2 7)).symm
  · decide
  · simp
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · simp [Nat.factorization_one]
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 30 3 = 1049601 := by decide
    rw [hquot]
    have hfactor : (1049601 : Nat).factorization 7 = 1 := by
      rw [show (1049601 : Nat) = 7 * 149943 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 7),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 149943),
      ]
    rw [hfactor]
    decide

theorem concrete_generated_b2_F30_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 30 1 2 3 := by
  exact Or.inl ⟨7, concrete_generated_b2_F30_p3_odd_component_case⟩

theorem concrete_generated_b2_F30_p5_odd_component_case :
    OddComponentCanonicalCase 30 1 2 5 11 := by
  refine ⟨Unit, inferInstance, ({() } : Finset Unit), (), 10, 1, 0,
    (fun _ : Unit => 1), (fun _ : Unit => 1), ?_⟩
  refine ⟨(by decide : Nat.Prime 11), (by decide : Odd 11), ?_⟩
  refine ⟨(by decide : Nat.Coprime 2 11), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (concrete_generated_b2_F10_p5_orderOf
      (by decide : Nat.Coprime 2 11)).symm
  · decide
  · simp
  · decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    decide
  · simp [Nat.factorization_one]
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 30 5 = 17043521 := by decide
    rw [hquot]
    have hfactor : (17043521 : Nat).factorization 11 = 1 := by
      rw [show (17043521 : Nat) = 11 * 1549411 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 11),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 1549411),
      ]
    rw [hfactor]
    decide

theorem concrete_generated_b2_F30_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 30 1 2 5 := by
  exact Or.inl ⟨11, concrete_generated_b2_F30_p5_odd_component_case⟩

def emittedCertificate_b2_L30_A1 :
    EmittedCertificateTable 30 1 2 where
  rows := ({2, 3, 5} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F30_factorization_support_cases hp with rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.odd_component
        concrete_generated_b2_F30_p2_odd_component_case
    · subst p
      exact EmittedGeneratedRowCase.odd_component
        concrete_generated_b2_F30_p3_odd_component_case
    · subst p
      exact EmittedGeneratedRowCase.odd_component
        concrete_generated_b2_F30_p5_odd_component_case

theorem orderOf_b2_mod1073741823_eq_30_from_emittedCertificate :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 1073741823)) = 30 := by
  let hcop : Nat.Coprime 2 1073741823 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 30 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 30 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 1073741823)ˣ) : ZMod 1073741823) ^ 30) =
        (1 : ZMod 1073741823)
      rw [ZMod.coe_unitOfCoprime]
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    30 1 1073741823 1073741823 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L30_A1

theorem local_layer_certificate_blocks_collapse
    {ι : Type*}
    {s : Finset ι}
    {q m L A b p : Nat}
    {T : ι → Nat}
    (hA : A ≠ 0)
    (cert : LocalLayerCertificate s q m T)
    (hA_eq : A = ∑ i ∈ s, T i)
    (hquot_ne_zero : primeComponentQuotient b L p ≠ 0)
    (hMval : m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hW : PrimeComponentWitness L A b p q :=
    local_layer_sum_certificate_supplies_PrimeComponentWitness
      cert hA_eq hquot_ne_zero hMval
  exact valuation_deficit_blocks_dvd hW.1 hW.2.1 hA hW.2.2

theorem residue_formula_certificate_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {b q d K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : ∀ i, i ∈ s → k i ≠ 0)
    (hK_ne_zero : K ≠ 0)
    (hkK : ∀ i, i ∈ s → k i ∣ K)
    (hcomponent_quot_ne_zero :
      ∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0)
    (hden_ne_zero :
      ∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0)
    (hresidue_not_dvd :
      ¬ q ∣
        ∑ i ∈ s,
          (((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
            (K / q ^ (K.factorization q))) *
            (∏ j ∈ s.erase i,
              ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
                (k j / q ^ ((k j).factorization q))))
    (hT :
      ∀ i, i ∈ s →
        T i =
          q ^ m *
            (((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) /
              q ^ (K.factorization q - (k i).factorization q)))
    (hA : A ≠ 0)
    (hA_eq : A = ∑ i ∈ s, T i)
    (hquot_ne_zero : primeComponentQuotient b L p ≠ 0)
    (hMval : m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hsum_not_dvd :
      ¬ q ∣
        ∑ i ∈ s,
          ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) /
            q ^ (K.factorization q - (k i).factorization q) :=
    odd_prime_order_residue_formula_not_dvd_sum
      (b := b) (q := q) (d := d) (K := K) (k := k)
      hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero hK_ne_zero
      hkK hcomponent_quot_ne_zero hden_ne_zero hresidue_not_dvd
  have cert :
      LocalLayerCertificate s q m T :=
    LocalLayerCertificate.of_q_pow_decomposition
      (R := fun i =>
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) /
          q ^ (K.factorization q - (k i).factorization q))
      hq hT hsum_not_dvd
  exact local_layer_certificate_blocks_collapse
    (s := s) (q := q) (m := m) (L := L) (A := A) (b := b) (p := p)
    (T := T) hA cert hA_eq hquot_ne_zero hMval

theorem residue_formula_singleton_certificate_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {s : Finset ι}
    {i0 : ι}
    {b q d K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : ∀ i, i ∈ s → k i ≠ 0)
    (hK_ne_zero : K ≠ 0)
    (hkK : ∀ i, i ∈ s → k i ∣ K)
    (hcomponent_quot_ne_zero :
      ∀ i, i ∈ s →
        ((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) ≠ 0)
    (hden_ne_zero :
      ∀ i, i ∈ s → b ^ (d * k i) - 1 ≠ 0)
    (hi0 : i0 ∈ s)
    (hresidue_unit :
      ¬ q ∣
        (((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
          (K / q ^ (K.factorization q))) *
          (∏ j ∈ s.erase i0,
            ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
              (k j / q ^ ((k j).factorization q))))
    (hresidue_rest :
      ∀ i, i ∈ s → i ≠ i0 →
        q ∣
          (((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
            (K / q ^ (K.factorization q))) *
            (∏ j ∈ s.erase i,
              ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
                (k j / q ^ ((k j).factorization q))))
    (hT :
      ∀ i, i ∈ s →
        T i =
          q ^ m *
            (((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) /
              q ^ (K.factorization q - (k i).factorization q)))
    (hA : A ≠ 0)
    (hA_eq : A = ∑ i ∈ s, T i)
    (hquot_ne_zero : primeComponentQuotient b L p ≠ 0)
    (hMval : m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A := by
  exact residue_formula_certificate_blocks_collapse
    (s := s) (b := b) (q := q) (d := d) (K := K) (m := m)
    (L := L) (A := A) (p := p) (k := k) (T := T)
    hq hq_odd hcop hd_order hbase_gt_one hk_ne_zero hK_ne_zero
    hkK hcomponent_quot_ne_zero hden_ne_zero
    (residue_formula_singleton_nonzero_certificate
      (s := s)
      (i0 := i0)
      (q := q)
      (commonResidue :=
        ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
          (K / q ^ (K.factorization q)))
      (D := fun j =>
        ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
          (k j / q ^ ((k j).factorization q)))
      hi0 hresidue_unit hresidue_rest)
    hT hA hA_eq hquot_ne_zero hMval

theorem not_dvd_mul_of_prime_not_dvd
    {q a b : Nat}
    (hq : Nat.Prime q)
    (ha : ¬ q ∣ a)
    (hb : ¬ q ∣ b) :
    ¬ q ∣ a * b := by
  intro hmul
  rcases hq.dvd_mul.mp hmul with hdiv | hdiv
  · exact ha hdiv
  · exact hb hdiv

theorem residue_formula_singleton_residue_unit_not_dvd
    {b q d K : Nat}
    (hq : Nat.Prime q)
    (hbase_ne_zero : b ^ d - 1 ≠ 0)
    (hK_ne_zero : K ≠ 0) :
    ¬ q ∣
      ((b ^ d - 1) / q ^ ((b ^ d - 1).factorization q)) *
        (K / q ^ (K.factorization q)) := by
  exact not_dvd_mul_of_prime_not_dvd hq
    (normalized_factorization_unit_not_dvd
      (q := q)
      (N := b ^ d - 1)
      hq
      hbase_ne_zero)
    (normalized_factorization_unit_not_dvd
      (q := q)
      (N := K)
      hq
      hK_ne_zero)

theorem residue_formula_singleton_finset_certificate_blocks_collapse
    {ι : Type*}
    [DecidableEq ι]
    {i0 : ι}
    {b q d K m L A p : Nat}
    {k : ι → Nat}
    {T : ι → Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hcop : Nat.Coprime b q)
    (hd_order : d = orderOf (ZMod.unitOfCoprime b hcop))
    (hbase_gt_one : 1 < b ^ d)
    (hk_ne_zero : k i0 ≠ 0)
    (hK_ne_zero : K ≠ 0)
    (hkK : k i0 ∣ K)
    (hcomponent_quot_ne_zero :
      ((b ^ (d * K) - 1) / (b ^ (d * k i0) - 1)) ≠ 0)
    (hden_ne_zero :
      b ^ (d * k i0) - 1 ≠ 0)
    (hT :
      ∀ i, i ∈ ({i0} : Finset ι) →
        T i =
          q ^ m *
            (((b ^ (d * K) - 1) / (b ^ (d * k i) - 1)) /
              q ^ (K.factorization q - (k i).factorization q)))
    (hA : A ≠ 0)
    (hA_eq : A = ∑ i ∈ ({i0} : Finset ι), T i)
    (hquot_ne_zero : primeComponentQuotient b L p ≠ 0)
    (hMval : m < (primeComponentQuotient b L p).factorization q) :
    ¬ primeComponentQuotient b L p ∣ A := by
  have hbase_ne_zero : b ^ d - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt hbase_gt_one
  refine residue_formula_singleton_certificate_blocks_collapse
    (s := ({i0} : Finset ι))
    (i0 := i0)
    (b := b)
    (q := q)
    (d := d)
    (K := K)
    (m := m)
    (L := L)
    (A := A)
    (p := p)
    (k := k)
    (T := T)
    hq hq_odd hcop hd_order hbase_gt_one ?hk_ne_zero_all hK_ne_zero
    ?hkK_all ?hcomponent_all ?hden_all ?hi0 ?hresidue_unit ?hresidue_rest
    hT hA hA_eq hquot_ne_zero hMval
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    exact hk_ne_zero
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    exact hkK
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    exact hcomponent_quot_ne_zero
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    exact hden_ne_zero
  · simp
  · simpa using
      residue_formula_singleton_residue_unit_not_dvd
        (b := b) (q := q) (d := d) (K := K)
        hq hbase_ne_zero hK_ne_zero
  · intro i hi hne
    rcases Finset.mem_singleton.mp hi with rfl
    exact (hne rfl).elim

theorem LocalLayerCertificate.singleton
    {α : Type*} [DecidableEq α]
    (x : α)
    (T : α → Nat)
    (q m : Nat)
    (hq : Nat.Prime q)
    (hdvd : q ^ m ∣ T x)
    (hres : ¬ q ∣ (T x / q ^ m)) :
    LocalLayerCertificate ({x} : Finset α) q m T := by
  refine ⟨hq, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_singleton.mp hi with rfl
    exact hdvd
  · simpa using hres

theorem LocalLayerCertificate.singleton_q_pow_exact
    {α : Type*} [DecidableEq α]
    (x : α)
    (T : α → Nat)
    (q m : Nat)
    (hq : Nat.Prime q)
    (hT_eq : ∃ r, T x = q ^ m * r ∧ ¬ q ∣ r) :
    LocalLayerCertificate ({x} : Finset α) q m T := by
  obtain ⟨r, hTx, hres⟩ := hT_eq
  have hq_pos : 0 < q := hq.pos
  have hq_pow_pos : 0 < q ^ m := pow_pos hq_pos m
  have hdvd : q ^ m ∣ T x := ⟨r, hTx⟩
  refine LocalLayerCertificate.singleton x T q m hq hdvd ?_
  rw [hTx, Nat.mul_div_cancel_left _ hq_pow_pos]
  exact hres

theorem b2_F2_localLayerCertificate_fixture :
    LocalLayerCertificate ({() } : Finset Unit) 3 0 (fun _ : Unit => 1) := by
  refine LocalLayerCertificate.singleton_q_pow_exact
    ()
    (fun _ : Unit => 1)
    3
    0
    (by decide)
    ?_
  exact ⟨1, by decide, by decide⟩

theorem b2_F2_PrimeComponentWitness_fixture :
    PrimeComponentWitness 2 1 2 2 3 := by
  refine local_layer_sum_certificate_supplies_PrimeComponentWitness
    b2_F2_localLayerCertificate_fixture
    ?_
    ?_
    ?_
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 2 2 = 3 := by decide
    rw [hquot]
    rw [Nat.Prime.factorization_self (by decide : Nat.Prime 3)]
    decide

theorem b2_F2_local_layer_blocks_collapse_fixture :
    ¬ primeComponentQuotient 2 2 2 ∣ 1 := by
  refine local_layer_certificate_blocks_collapse
    (A := 1)
    (L := 2)
    (b := 2)
    (p := 2)
    (q := 3)
    (m := 0)
    (s := ({() } : Finset Unit))
    (T := fun _ : Unit => 1)
    (by decide)
    b2_F2_localLayerCertificate_fixture
    ?_
    ?_
    ?_
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 2 2 = 3 := by decide
    rw [hquot]
    rw [Nat.Prime.factorization_self (by decide : Nat.Prime 3)]
    decide

theorem b2_F6_p2_localLayerCertificate_fixture :
    LocalLayerCertificate ({() } : Finset Unit) 3 0 (fun _ : Unit => 1) := by
  exact b2_F2_localLayerCertificate_fixture

theorem b2_F6_p2_PrimeComponentWitness_fixture :
    PrimeComponentWitness 6 1 2 2 3 := by
  refine local_layer_sum_certificate_supplies_PrimeComponentWitness
    b2_F6_p2_localLayerCertificate_fixture
    ?_
    ?_
    ?_
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 6 2 = 9 := by decide
    rw [hquot]
    have hfactor : (9 : Nat).factorization 3 = 2 := by
      rw [show (9 : Nat) = 3 ^ 2 by decide]
      exact Nat.factorization_pow_self (by decide : Nat.Prime 3)
    rw [hfactor]
    decide

theorem b2_F6_p2_local_layer_blocks_collapse_fixture :
    ¬ primeComponentQuotient 2 6 2 ∣ 1 := by
  refine local_layer_certificate_blocks_collapse
    (A := 1)
    (L := 6)
    (b := 2)
    (p := 2)
    (q := 3)
    (m := 0)
    (s := ({() } : Finset Unit))
    (T := fun _ : Unit => 1)
    (by decide)
    b2_F6_p2_localLayerCertificate_fixture
    ?_
    ?_
    ?_
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 6 2 = 9 := by decide
    rw [hquot]
    have hfactor : (9 : Nat).factorization 3 = 2 := by
      rw [show (9 : Nat) = 3 ^ 2 by decide]
      exact Nat.factorization_pow_self (by decide : Nat.Prime 3)
    rw [hfactor]
    decide

def b2_F3_6_p3_terms (i : Bool) : Nat :=
  if i then 1 else 9

theorem b2_F3_6_p3_multiLocalLayerCertificate_fixture :
    LocalLayerCertificate
      (Finset.univ : Finset Bool)
      7
      0
      b2_F3_6_p3_terms := by
  refine ⟨(by decide : Nat.Prime 7), ?_, ?_⟩
  · intro i _hi
    exact one_dvd (b2_F3_6_p3_terms i)
  · decide

theorem b2_F3_6_p3_PrimeComponentWitness_fixture :
    PrimeComponentWitness 6 10 2 3 7 := by
  refine local_layer_sum_certificate_supplies_PrimeComponentWitness
    b2_F3_6_p3_multiLocalLayerCertificate_fixture
    ?_
    ?_
    ?_
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 6 3 = 21 := by decide
    rw [hquot]
    have hfactor : (21 : Nat).factorization 7 = 1 := by
      rw [show (21 : Nat) = 7 * 3 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 7),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 3),
      ]
    rw [hfactor]
    decide

theorem b2_F3_6_p3_local_layer_blocks_collapse_fixture :
    ¬ primeComponentQuotient 2 6 3 ∣ 10 := by
  refine local_layer_certificate_blocks_collapse
    (A := 10)
    (L := 6)
    (b := 2)
    (p := 3)
    (q := 7)
    (m := 0)
    (s := (Finset.univ : Finset Bool))
    (T := b2_F3_6_p3_terms)
    (by decide)
    b2_F3_6_p3_multiLocalLayerCertificate_fixture
    ?_
    ?_
    ?_
  · decide
  · decide
  · have hquot : primeComponentQuotient 2 6 3 = 21 := by decide
    rw [hquot]
    have hfactor : (21 : Nat).factorization 7 = 1 := by
      rw [show (21 : Nat) = 7 * 3 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 7),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 3),
      ]
    rw [hfactor]
    decide

theorem local_layer_witness_family_implies_period_noncollapse
    {ι : Type*}
    (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    (S : Nat → Finset ι)
    (T : Nat → ι → Nat)
    (m q : Nat → Nat)
    (h_local :
      ∀ p, Nat.Prime p → p ∣ L →
        LocalLayerCertificate (S p) (q p) (m p) (T p))
    (hA_eq :
      ∀ p, Nat.Prime p → p ∣ L →
        A = ∑ i ∈ S p, T p i)
    (hquot_ne_zero :
      ∀ p, Nat.Prime p → p ∣ L →
        primeComponentQuotient b L p ≠ 0)
    (hMval :
      ∀ p, Nat.Prime p → p ∣ L →
        m p < (primeComponentQuotient b L p).factorization (q p)) :
    orderOf (ZMod.unitOfCoprime b hcop) = L := by
  apply witness_existence_implies_period_noncollapse
    (L := L) (A := A) (B := B) (Q := Q) (b := b)
    hcop hLpos hA h_ord_dvd_L hQpos hQ hB_eq hpow
  intro p hp hpL
  exact ⟨q p,
    local_layer_sum_certificate_supplies_PrimeComponentWitness
      (h_local p hp hpL)
      (hA_eq p hp hpL)
      (hquot_ne_zero p hp hpL)
      (hMval p hp hpL)⟩

theorem local_layer_decomposition_family_implies_period_noncollapse
    {ι : Type*}
    (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    (S : Nat → Finset ι)
    (T R : Nat → ι → Nat)
    (m q : Nat → Nat)
    (hq :
      ∀ p, Nat.Prime p → p ∣ L → Nat.Prime (q p))
    (hT :
      ∀ p, Nat.Prime p → p ∣ L →
        ∀ i, i ∈ S p → T p i = (q p) ^ (m p) * R p i)
    (hres :
      ∀ p, Nat.Prime p → p ∣ L →
        ¬ q p ∣ ∑ i ∈ S p, R p i)
    (hA_eq :
      ∀ p, Nat.Prime p → p ∣ L →
        A = ∑ i ∈ S p, T p i)
    (hquot_ne_zero :
      ∀ p, Nat.Prime p → p ∣ L →
        primeComponentQuotient b L p ≠ 0)
    (hMval :
      ∀ p, Nat.Prime p → p ∣ L →
        m p < (primeComponentQuotient b L p).factorization (q p)) :
    orderOf (ZMod.unitOfCoprime b hcop) = L := by
  apply witness_existence_implies_period_noncollapse
    (L := L) (A := A) (B := B) (Q := Q) (b := b)
    hcop hLpos hA h_ord_dvd_L hQpos hQ hB_eq hpow
  intro p hp hpL
  exact ⟨q p,
    local_layer_decomposition_supplies_PrimeComponentWitness
      (hq p hp hpL)
      (hT p hp hpL)
      (hres p hp hpL)
      (hA_eq p hp hpL)
      (hquot_ne_zero p hp hpL)
      (hMval p hp hpL)⟩

theorem minimal_layer_decomposition_family_implies_period_noncollapse
    {ι : Type*}
    [DecidableEq ι]
    (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hLpos : 0 < L)
    (hA : A ≠ 0)
    (h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L)
    (hQpos : 0 < Q)
    (hQ : Q = B / Nat.gcd A B)
    (hB_eq : B = b ^ L - 1)
    (hpow : 1 ≤ b ^ orderOf (ZMod.unitOfCoprime b hcop))
    (S M : Nat → Finset ι)
    (T R : Nat → ι → Nat)
    (m q : Nat → Nat)
    (hq :
      ∀ p, Nat.Prime p → p ∣ L → Nat.Prime (q p))
    (hsub :
      ∀ p, Nat.Prime p → p ∣ L → M p ⊆ S p)
    (hT :
      ∀ p, Nat.Prime p → p ∣ L →
        ∀ i, i ∈ S p → T p i = (q p) ^ (m p) * R p i)
    (hhigh :
      ∀ p, Nat.Prime p → p ∣ L →
        ∀ i, i ∈ S p → i ∉ M p → q p ∣ R p i)
    (hres_min :
      ∀ p, Nat.Prime p → p ∣ L →
        ¬ q p ∣ ∑ i ∈ M p, R p i)
    (hA_eq :
      ∀ p, Nat.Prime p → p ∣ L →
        A = ∑ i ∈ S p, T p i)
    (hquot_ne_zero :
      ∀ p, Nat.Prime p → p ∣ L →
        primeComponentQuotient b L p ≠ 0)
    (hMval :
      ∀ p, Nat.Prime p → p ∣ L →
        m p < (primeComponentQuotient b L p).factorization (q p)) :
    orderOf (ZMod.unitOfCoprime b hcop) = L := by
  apply witness_existence_implies_period_noncollapse
    (L := L) (A := A) (B := B) (Q := Q) (b := b)
    hcop hLpos hA h_ord_dvd_L hQpos hQ hB_eq hpow
  intro p hp hpL
  exact ⟨q p,
    minimal_layer_decomposition_supplies_PrimeComponentWitness
      (hq p hp hpL)
      (hsub p hp hpL)
      (hT p hp hpL)
      (hhigh p hp hpL)
      (hres_min p hp hpL)
      (hA_eq p hp hpL)
      (hquot_ne_zero p hp hpL)
      (hMval p hp hpL)⟩

/-! ## Canonical witness selector: universal exact-order witness route

The canonical witness selector reduction, Lean-checked: for every finite
nonempty support `F` of positive exponents, every prime `p` dividing
`L = lcm F` admits a *selector row* — an element of `F` attaining the full
`p`-adic valuation of `L` while being multiple-free inside `F`.  Feeding each
selector row an exact-order prime-power witness (`q ^ s` divides `b ^ m - 1`
exactly when the selected exponent divides `m`) supplies the
`PrimeComponentWitness` valuation deficit, so the finite period-noncollapse
statement follows for the *actual* numerator `A = ∑ (b ^ L - 1) / (b ^ n - 1)`
conditional only on witness supply for the multiple-free rows. -/

theorem exists_lcm_factorization_le_row
    (F : Finset Nat) (hF : F.Nonempty) (h0 : 0 ∉ F) (p : Nat) :
    ∃ n ∈ F, (F.lcm id).factorization p ≤ n.factorization p := by
  classical
  induction hF using Finset.Nonempty.cons_induction with
  | singleton a =>
      refine ⟨a, Finset.mem_singleton_self a, ?_⟩
      simp [Finset.lcm_singleton]
  | cons a s ha hs ih =>
      have h0s : 0 ∉ s := fun h => h0 (Finset.mem_cons_of_mem h)
      have ha0 : a ≠ 0 := by
        intro h
        apply h0
        rw [← h]
        exact Finset.mem_cons_self a s
      have hs0 : s.lcm id ≠ 0 := by
        rw [Ne, Finset.lcm_eq_zero_iff]
        rintro ⟨x, hxs, hx0⟩
        rw [id_eq] at hx0
        exact h0s (hx0 ▸ hxs)
      obtain ⟨n, hn, hle⟩ := ih h0s
      have hlcm_cons :
          ((Finset.cons a s ha).lcm id).factorization p
            = (a.factorization ⊔ (s.lcm id).factorization) p := by
        rw [Finset.cons_eq_insert, Finset.lcm_insert]
        rw [show lcm (id a) (s.lcm id) = Nat.lcm a (s.lcm id) from rfl]
        rw [Nat.factorization_lcm ha0 hs0]
      rcases le_total ((s.lcm id).factorization p) (a.factorization p) with hcase | hcase
      · refine ⟨a, Finset.mem_cons_self a s, ?_⟩
        rw [hlcm_cons, Finsupp.sup_apply]
        exact sup_le le_rfl hcase
      · refine ⟨n, Finset.mem_cons_of_mem hn, ?_⟩
        rw [hlcm_cons, Finsupp.sup_apply]
        exact sup_le (hcase.trans hle) hle

theorem exists_canonical_witness_selector_row
    (F : Finset Nat) (hF : F.Nonempty) (h0 : 0 ∉ F) (p : Nat) :
    ∃ n ∈ F, n.factorization p = (F.lcm id).factorization p ∧
      ∀ m ∈ F, n ∣ m → m = n := by
  classical
  have hL0 : F.lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hxF, hx0⟩
    rw [id_eq] at hx0
    exact h0 (hx0 ▸ hxF)
  obtain ⟨w, hwF, hw⟩ := exists_lcm_factorization_le_row F hF h0 p
  set S : Finset Nat :=
    F.filter (fun n => (F.lcm id).factorization p ≤ n.factorization p) with hS_def
  have hS_ne : S.Nonempty := ⟨w, Finset.mem_filter.mpr ⟨hwF, hw⟩⟩
  have hn0S : S.max' hS_ne ∈ S := S.max'_mem hS_ne
  have hn0F : S.max' hS_ne ∈ F := (Finset.mem_filter.mp hn0S).1
  have hn0a : (F.lcm id).factorization p ≤ (S.max' hS_ne).factorization p :=
    (Finset.mem_filter.mp hn0S).2
  have hn0a' : (S.max' hS_ne).factorization p ≤ (F.lcm id).factorization p :=
    factorization_le_of_dvd_ne_zero hL0 (by simpa using Finset.dvd_lcm hn0F)
  refine ⟨S.max' hS_ne, hn0F, le_antisymm hn0a' hn0a, ?_⟩
  intro m hmF hdvd
  have hm0 : m ≠ 0 := fun h => h0 (h ▸ hmF)
  have hmS : m ∈ S := by
    refine Finset.mem_filter.mpr ⟨hmF, ?_⟩
    exact hn0a.trans (factorization_le_of_dvd_ne_zero hm0 hdvd)
  exact le_antisymm (S.le_max' m hmS) (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd)

/-- Exact-order prime-power witness for exponent `n` over base `b`:
the prime power `q ^ s` divides `b ^ m - 1` exactly when `n ∣ m`.
Prime powers (rather than bare primes) keep the Zsigmondy exception pairs
such as `(b, n) = (2, 6)` coverable via `3 ^ 2`. -/
def ExactOrderPrimePowerWitness (b n q s : Nat) : Prop :=
  Nat.Prime q ∧ 0 < s ∧ ∀ m : Nat, q ^ s ∣ b ^ m - 1 ↔ n ∣ m

theorem exactOrderPrimePowerWitness_of_orderOf
    {b n q s : Nat}
    (hq : Nat.Prime q)
    (hs : 0 < s)
    (hb : 0 < b)
    (hcop : Nat.Coprime b (q ^ s))
    (hord : orderOf (ZMod.unitOfCoprime b hcop) = n) :
    ExactOrderPrimePowerWitness b n q s := by
  refine ⟨hq, hs, fun m => ?_⟩
  rw [← hord]
  exact (orderOf_dvd_iff_q_dvd_pow_sub_one hcop (Nat.one_le_pow m b hb)).symm

theorem exactOrderPrimePowerWitness_of_orderOf_prime
    {b n q : Nat}
    (hq : Nat.Prime q)
    (hb : 0 < b)
    (hcop : Nat.Coprime b q)
    (hord : orderOf (ZMod.unitOfCoprime b hcop) = n) :
    ExactOrderPrimePowerWitness b n q 1 := by
  refine ⟨hq, Nat.one_pos, fun m => ?_⟩
  rw [pow_one, ← hord]
  exact (orderOf_dvd_iff_q_dvd_pow_sub_one hcop (Nat.one_le_pow m b hb)).symm

theorem exact_order_witness_supplies_PrimeComponentWitness
    {F : Finset Nat} {L A b p n q s : Nat}
    (hb : 2 ≤ b)
    (h0 : 0 ∉ F)
    (hL_eq : L = F.lcm id)
    (hp : Nat.Prime p)
    (hpL : p ∣ L)
    (hnF : n ∈ F)
    (hn_val : n.factorization p = L.factorization p)
    (hn_iso : ∀ m ∈ F, n ∣ m → m = n)
    (hwit : ExactOrderPrimePowerWitness b n q s)
    (hA_eq : A = ∑ m ∈ F, (b ^ L - 1) / (b ^ m - 1)) :
    PrimeComponentWitness L A b p q := by
  classical
  obtain ⟨hq, hs, hprofile⟩ := hwit
  have hL0 : L ≠ 0 := by
    rw [hL_eq, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hxF, hx0⟩
    rw [id_eq] at hx0
    exact h0 (hx0 ▸ hxF)
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  have hB_pos : 0 < b ^ L - 1 := by
    have := Nat.le_self_pow hL0 b
    omega
  have hden_pos : ∀ m ∈ F, 0 < b ^ m - 1 := by
    intro m hmF
    have hm0 : m ≠ 0 := fun h => h0 (h ▸ hmF)
    have := Nat.le_self_pow hm0 b
    omega
  have hden_dvd : ∀ m ∈ F, b ^ m - 1 ∣ b ^ L - 1 := by
    intro m hmF
    exact Nat.pow_sub_one_dvd_pow_sub_one b
      (by simpa [hL_eq] using Finset.dvd_lcm hmF)
  have hT_pos : ∀ m ∈ F, 0 < (b ^ L - 1) / (b ^ m - 1) := fun m hmF =>
    Nat.div_pos (Nat.le_of_dvd hB_pos (hden_dvd m hmF)) (hden_pos m hmF)
  have hT_val : ∀ m ∈ F, ((b ^ L - 1) / (b ^ m - 1)).factorization q
      = (b ^ L - 1).factorization q - (b ^ m - 1).factorization q := by
    intro m hmF
    exact pow_sub_one_component_factorization
      (by simpa [hL_eq] using Finset.dvd_lcm hmF)
      (hT_pos m hmF).ne'
      (hden_pos m hmF).ne'
  have hbn0 : b ^ n - 1 ≠ 0 := (hden_pos n hnF).ne'
  have hs_le : s ≤ (b ^ n - 1).factorization q :=
    (hq.pow_dvd_iff_le_factorization hbn0).mp ((hprofile n).mpr dvd_rfl)
  have hn_row_le : (b ^ n - 1).factorization q ≤ (b ^ L - 1).factorization q :=
    factorization_le_of_dvd_ne_zero hB_pos.ne' (hden_dvd n hnF)
  have hother : ∀ m ∈ F, m ≠ n → (b ^ m - 1).factorization q < s := by
    intro m hmF hne
    by_contra hge
    have hge := Nat.le_of_not_lt hge
    have hdvd : q ^ s ∣ b ^ m - 1 :=
      (hq.pow_dvd_iff_le_factorization (hden_pos m hmF).ne').mpr hge
    exact hne (hn_iso m hmF ((hprofile m).mp hdvd))
  -- the selected row blocks the drop to `L / p`
  have hLp_pos : 0 < L / p := Nat.div_pos (Nat.le_of_dvd hLpos hpL) hp.pos
  have hLp_dvd_L : L / p ∣ L := ⟨p, (Nat.div_mul_cancel hpL).symm⟩
  have hLp_val : (L / p).factorization p = L.factorization p - 1 := by
    have hmul : L = (L / p) * p := (Nat.div_mul_cancel hpL).symm
    rw [factorization_left_factor_of_mul_eq hLp_pos.ne' hp.pos.ne' hmul,
      hp.factorization_self]
  have ha_pos : 0 < L.factorization p := hp.factorization_pos_of_dvd hL0 hpL
  have hn_not_dvd_Lp : ¬ n ∣ L / p := by
    intro hdvd
    have hle : n.factorization p ≤ (L / p).factorization p :=
      factorization_le_of_dvd_ne_zero hLp_pos.ne' hdvd
    rw [hLp_val, hn_val] at hle
    omega
  have hLp_den_pos : 0 < b ^ (L / p) - 1 := by
    have := Nat.le_self_pow hLp_pos.ne' b
    omega
  have hquot_pos : 0 < primeComponentQuotient b L p := by
    show 0 < (b ^ L - 1) / (b ^ (L / p) - 1)
    exact Nat.div_pos
      (Nat.le_of_dvd hB_pos (Nat.pow_sub_one_dvd_pow_sub_one b hLp_dvd_L))
      hLp_den_pos
  have hLp_row_lt : (b ^ (L / p) - 1).factorization q < s := by
    by_contra hge
    have hge := Nat.le_of_not_lt hge
    have hdvd : q ^ s ∣ b ^ (L / p) - 1 :=
      (hq.pow_dvd_iff_le_factorization hLp_den_pos.ne').mpr hge
    exact hn_not_dvd_Lp ((hprofile (L / p)).mp hdvd)
  have hquot_val : (primeComponentQuotient b L p).factorization q
      = (b ^ L - 1).factorization q - (b ^ (L / p) - 1).factorization q := by
    show ((b ^ L - 1) / (b ^ (L / p) - 1)).factorization q = _
    exact pow_sub_one_component_factorization hLp_dvd_L
      hquot_pos.ne' hLp_den_pos.ne'
  refine singleton_minimal_factorization_row_supplies_PrimeComponentWitness
    (s := F) (i0 := n) (q := q)
    (m := ((b ^ L - 1) / (b ^ n - 1)).factorization q)
    (L := L) (A := A) (b := b) (p := p)
    (T := fun m => (b ^ L - 1) / (b ^ m - 1))
    hq hnF (fun m hm => (hT_pos m hm).ne') rfl ?hhigh hA_eq hquot_pos.ne' ?hM
  case hhigh =>
    intro m hmF hne
    rw [hT_val m hmF, hT_val n hnF]
    exact sub_lt_sub_of_lt_right_with_le
      (lt_of_lt_of_le (hother m hmF hne) hs_le) hn_row_le
  case hM =>
    rw [hT_val n hnF, hquot_val]
    exact sub_lt_sub_of_lt_right_with_le
      (lt_of_lt_of_le hLp_row_lt hs_le) hn_row_le

theorem finite_period_noncollapse_from_exact_order_witness_supply
    (F : Finset Nat) (L A B Q b : Nat)
    (hcop : Nat.Coprime b Q)
    (hF : F.Nonempty)
    (h0 : 0 ∉ F)
    (hb : 2 ≤ b)
    (hL_eq : L = F.lcm id)
    (hA_eq : A = ∑ n ∈ F, (b ^ L - 1) / (b ^ n - 1))
    (hB_eq : B = b ^ L - 1)
    (hQ : Q = B / Nat.gcd A B)
    (hsupply :
      ∀ n ∈ F, 2 ≤ n → (∀ m ∈ F, n ∣ m → m = n) →
        ∃ q s, ExactOrderPrimePowerWitness b n q s) :
    orderOf (ZMod.unitOfCoprime b hcop) = L := by
  classical
  have hL0 : L ≠ 0 := by
    rw [hL_eq, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hxF, hx0⟩
    rw [id_eq] at hx0
    exact h0 (hx0 ▸ hxF)
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  have hB_pos : 0 < B := by
    rw [hB_eq]
    have := Nat.le_self_pow hL0 b
    omega
  have hA_pos : 0 < A := by
    rw [hA_eq]
    refine Finset.sum_pos ?_ hF
    intro m hmF
    have hm0 : m ≠ 0 := fun h => h0 (h ▸ hmF)
    have hden_pos : 0 < b ^ m - 1 := by
      have := Nat.le_self_pow hm0 b
      omega
    have hBL_pos : 0 < b ^ L - 1 := by
      have := Nat.le_self_pow hL0 b
      omega
    exact Nat.div_pos
      (Nat.le_of_dvd hBL_pos
        (Nat.pow_sub_one_dvd_pow_sub_one b
          (by simpa [hL_eq] using Finset.dvd_lcm hmF)))
      hden_pos
  have hQpos : 0 < Q := by
    rw [hQ]
    exact Nat.div_pos (Nat.le_of_dvd hB_pos (Nat.gcd_dvd_right A B))
      (Nat.gcd_pos_of_pos_right A hB_pos)
  have hQ_dvd_B : Q ∣ B :=
    ⟨Nat.gcd A B, by rw [hQ, mul_comm]; exact gcd_denominator_factor A B⟩
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime b hcop) ∣ L := by
    refine (orderOf_dvd_iff_q_dvd_pow_sub_one hcop
      (Nat.one_le_pow L b (by omega))).mpr ?_
    rw [← hB_eq]
    exact hQ_dvd_B
  refine witness_existence_implies_period_noncollapse
    L A B Q b hcop hLpos hA_pos.ne' h_ord_dvd_L hQpos hQ hB_eq
    (Nat.one_le_pow _ b (by omega)) ?_
  intro p hp hpL
  obtain ⟨n, hnF, hval, hiso⟩ :=
    exists_canonical_witness_selector_row F hF h0 p
  have hn0 : n ≠ 0 := fun h => h0 (h ▸ hnF)
  have hn_val : n.factorization p = L.factorization p := by
    rw [hval, hL_eq]
  have hn2 : 2 ≤ n := by
    have hvp : 0 < n.factorization p := by
      rw [hn_val]
      exact hp.factorization_pos_of_dvd hL0 hpL
    have hpn : p ∣ n := Nat.dvd_of_factorization_pos hvp.ne'
    have hp2 := hp.two_le
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
    omega
  obtain ⟨q, s, hwit⟩ := hsupply n hnF hn2 hiso
  exact ⟨q, exact_order_witness_supplies_PrimeComponentWitness
    hb h0 hL_eq hp hpL hnF hn_val hiso hwit hA_eq⟩

/-! ### Concrete route demonstration, including a Zsigmondy exception pair

`F = {1, 2, 3, 6}` over `b = 2` forces the prime-power witness lane: no prime
has multiplicative order `6` for base `2` (the classical Zsigmondy exception
`2 ^ 6 - 1 = 63 = 3 ^ 2 * 7`), while `q ^ s = 3 ^ 2` works. -/

theorem orderOf_two_unit_mod_nine_eq_six
    (h9 : Nat.Coprime 2 (3 ^ 2)) :
    orderOf (ZMod.unitOfCoprime 2 h9) = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : (0 : Nat) < 6)
  · apply Units.ext
    change (((ZMod.unitOfCoprime 2 h9 : (ZMod (3 ^ 2))ˣ) : ZMod (3 ^ 2)) ^ 6) = 1
    rw [ZMod.coe_unitOfCoprime]
    decide
  · intro pr hpr hprd
    have hpr_le : pr ≤ 6 := Nat.le_of_dvd (by decide) hprd
    have hpr2 := hpr.two_le
    interval_cases pr
    · intro h
      have hv := congrArg Units.val h
      change ((ZMod.unitOfCoprime 2 h9 : (ZMod (3 ^ 2))ˣ).val ^ 3) =
        (1 : (ZMod (3 ^ 2))ˣ).val at hv
      rw [ZMod.coe_unitOfCoprime] at hv
      revert hv
      decide
    · intro h
      have hv := congrArg Units.val h
      change ((ZMod.unitOfCoprime 2 h9 : (ZMod (3 ^ 2))ˣ).val ^ 2) =
        (1 : (ZMod (3 ^ 2))ˣ).val at hv
      rw [ZMod.coe_unitOfCoprime] at hv
      revert hv
      decide
    · exact False.elim ((by decide : ¬ Nat.Prime 4) hpr)
    · exact False.elim ((by decide : ¬ (5 ∣ 6)) hprd)
    · exact False.elim ((by decide : ¬ Nat.Prime 6) hpr)

theorem orderOf_b2_mod63_eq_6_from_exact_order_witness_route
    (hcop : Nat.Coprime 2 63) :
    orderOf (ZMod.unitOfCoprime 2 hcop) = 6 := by
  refine finite_period_noncollapse_from_exact_order_witness_supply
    ({1, 2, 3, 6} : Finset Nat) 6 94 63 63 2 hcop
    ⟨1, by decide⟩ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  intro n hn hn2 hiso
  have hn_cases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
    simpa using hn
  rcases hn_cases with rfl | rfl | rfl | rfl
  · omega
  · exact absurd (hiso 6 (by decide) (by decide)) (by decide)
  · exact absurd (hiso 6 (by decide) (by decide)) (by decide)
  · exact ⟨3, 2, exactOrderPrimePowerWitness_of_orderOf
      (by decide) (by decide) (by decide) (by decide)
      (orderOf_two_unit_mod_nine_eq_six (by decide))⟩

/-! ## Unconditional exact-order witness supply: the cyclotomic route

Zsigmondy's theorem is not needed.  Because the witness interface asks for a
prime *power* `q ^ s` rather than a bare prime, the classical exception pairs
dissolve into a generic construction: any prime divisor `q` of the cyclotomic
value `Φ_n(b)` has `ord_q(b)` equal to the `q`-free part of `n`, and
lifting-the-exponent then chooses `s` so that `q ^ s` sees order exactly `n`.
The Zsigmondy exception families are recovered as instances of the same lift:
`(b, n) = (2, 6)` yields `q ^ s = 3 ^ 2`, and `n = 2` with `b + 1` a power of
two yields `q = 2` with the appropriate `s`. -/

theorem exists_prime_dvd_cyclotomic_eval
    {b n : Nat} (hb : 2 ≤ b) (hn : 2 ≤ n) :
    ∃ q : Nat, Nat.Prime q ∧
      (q : Int) ∣ (Polynomial.cyclotomic n Int).eval ((b : Nat) : Int) := by
  have hlt : b - 1 < ((Polynomial.cyclotomic n Int).eval ((b : Nat) : Int)).natAbs :=
    Polynomial.sub_one_lt_natAbs_cyclotomic_eval (by omega) (by omega)
  have h2 : ((Polynomial.cyclotomic n Int).eval ((b : Nat) : Int)).natAbs ≠ 1 := by
    omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd h2
  refine ⟨q, hq, ?_⟩
  exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hqdvd)

theorem orderOf_isRoot_cyclotomic_zmod_pow_mul
    {q : Nat} (hq : Nat.Prime q) :
    ∀ n : Nat, 0 < n → ∀ x : ZMod q,
      (Polynomial.cyclotomic n (ZMod q)).IsRoot x →
      ∃ a : Nat, n = q ^ a * orderOf x := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hroot
    by_cases hqn : q ∣ n
    · have hq1 : 1 < q := hq.one_lt
      have hnq_pos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqn) hq.pos
      have hnq_lt : n / q < n := Nat.div_lt_self hn hq1
      have hmul : n / q * q = n := Nat.div_mul_cancel hqn
      have hroot' : (Polynomial.cyclotomic (n / q) (ZMod q)).IsRoot x := by
        by_cases hqn' : q ∣ n / q
        · have hpow := Polynomial.cyclotomic_mul_prime_dvd_eq_pow (ZMod q) hqn'
          have hroot_pow : (Polynomial.cyclotomic (n / q) (ZMod q) ^ q).IsRoot x := by
            rw [← hpow, hmul]
            exact hroot
          have hev : (Polynomial.cyclotomic (n / q) (ZMod q)).eval x ^ q = 0 := by
            simpa [Polynomial.IsRoot, Polynomial.eval_pow] using hroot_pow
          simpa [Polynomial.IsRoot] using (pow_eq_zero_iff hq.pos.ne').mp hev
        · have hpow := Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod q) hqn'
          have hroot_pow :
              (Polynomial.cyclotomic (n / q) (ZMod q) ^ (q - 1)).IsRoot x := by
            rw [← hpow, hmul]
            exact hroot
          have hev : (Polynomial.cyclotomic (n / q) (ZMod q)).eval x ^ (q - 1) = 0 := by
            simpa [Polynomial.IsRoot, Polynomial.eval_pow] using hroot_pow
          simpa [Polynomial.IsRoot] using
            (pow_eq_zero_iff (by omega : q - 1 ≠ 0)).mp hev
      obtain ⟨a, ha⟩ := ih (n / q) hnq_lt hnq_pos x hroot'
      refine ⟨a + 1, ?_⟩
      calc n = n / q * q := hmul.symm
        _ = q ^ a * orderOf x * q := by rw [ha]
        _ = q ^ (a + 1) * orderOf x := by ring
    · haveI : NeZero ((n : ZMod q)) :=
        ⟨fun h => hqn ((ZMod.natCast_eq_zero_iff n q).mp h)⟩
      have hprim : IsPrimitiveRoot x n :=
        Polynomial.isRoot_cyclotomic_iff.mp hroot
      exact ⟨0, by simpa using hprim.eq_orderOf⟩

theorem exactOrderPrimePowerWitness_lift_odd
    {b q m a : Nat}
    (hq : Nat.Prime q)
    (hq_odd : Odd q)
    (hb : 2 ≤ b)
    (hcop : Nat.Coprime b q)
    (hm_ord : m = orderOf (ZMod.unitOfCoprime b hcop))
    (ha : 0 < a) :
    ExactOrderPrimePowerWitness b (q ^ a * m) q
      ((b ^ m - 1).factorization q + a) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hm_pos : 0 < m := by
    rw [hm_ord]
    exact orderOf_pos _
  have hchar : ∀ k : Nat, q ∣ b ^ k - 1 ↔ m ∣ k := by
    intro k
    rw [hm_ord]
    exact (orderOf_dvd_iff_q_dvd_pow_sub_one hcop
      (Nat.one_le_pow k b (by omega))).symm
  have hLTE : ∀ t : Nat, t ≠ 0 →
      (b ^ (m * t) - 1).factorization q
        = (b ^ m - 1).factorization q + t.factorization q := by
    intro t ht
    exact odd_prime_order_factorization_pow_sub_one hq hq_odd hcop hm_ord
      (Nat.one_lt_pow hm_pos.ne' (by omega)) ht
  refine ⟨hq, by omega, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp
  · have hbk_pos : 0 < b ^ k - 1 := by
      have := Nat.one_lt_pow hk_pos.ne' (show 1 < b by omega)
      omega
    constructor
    · intro hdvd
      have hq_dvd : q ∣ b ^ k - 1 :=
        dvd_trans (dvd_pow_self q (by omega)) hdvd
      obtain ⟨t, rfl⟩ := (hchar k).mp hq_dvd
      have ht : t ≠ 0 := by
        rintro rfl
        simp at hk_pos
      have hle : (b ^ m - 1).factorization q + a
          ≤ (b ^ (m * t) - 1).factorization q :=
        (hq.pow_dvd_iff_le_factorization hbk_pos.ne').mp hdvd
      rw [hLTE t ht] at hle
      have hqa_dvd : q ^ a ∣ t :=
        (hq.pow_dvd_iff_le_factorization ht).mpr (by omega)
      obtain ⟨t', rfl⟩ := hqa_dvd
      exact ⟨t', by ring⟩
    · intro hdvd
      obtain ⟨u, rfl⟩ := hdvd
      have hu : u ≠ 0 := by
        rintro rfl
        simp at hk_pos
      have hval : (b ^ (q ^ a * m * u) - 1).factorization q
          = (b ^ m - 1).factorization q + (q ^ a * u).factorization q := by
        rw [show q ^ a * m * u = m * (q ^ a * u) from by ring]
        exact hLTE _ (mul_ne_zero (pow_ne_zero a hq.pos.ne') hu)
      have hpowfac : (q ^ a).factorization q = a := by
        rw [hq.factorization_pow]
        simp
      have hsplit : (q ^ a * u).factorization q
          = (q ^ a).factorization q + u.factorization q := by
        rw [Nat.factorization_mul (pow_ne_zero a hq.pos.ne') hu]
        simp
      refine (hq.pow_dvd_iff_le_factorization hbk_pos.ne').mpr ?_
      rw [hval]
      omega

theorem exactOrderPrimePowerWitness_lift_two
    {b a : Nat}
    (hb : 2 ≤ b)
    (hb_odd : Odd b)
    (ha : 0 < a) :
    ExactOrderPrimePowerWitness b (2 ^ a) 2
      ((b - 1).factorization 2 + (b + 1).factorization 2 + (a - 1)) := by
  have hb1 : 1 < b := by omega
  have hc2_pos : 0 < (b + 1).factorization 2 := by
    have h2dvd : (2 : Nat) ∣ b + 1 := by
      rcases hb_odd with ⟨j, hj⟩
      exact ⟨j + 1, by omega⟩
    exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) h2dvd
  refine ⟨Nat.prime_two, by omega, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp
  · have hbk_pos : 0 < b ^ k - 1 := by
      have := Nat.one_lt_pow hk_pos.ne' hb1
      omega
    rcases Nat.even_or_odd k with hk_even | hk_odd
    · have hval := two_adic_pow_sub_one_factorization_even hb1 hb_odd hk_pos.ne' hk_even
      have hk2 : 0 < k.factorization 2 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two hk_pos.ne' hk_even.two_dvd
      constructor
      · intro hdvd
        have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hbk_pos.ne').mp hdvd
        refine (Nat.prime_two.pow_dvd_iff_le_factorization hk_pos.ne').mpr ?_
        omega
      · intro hdvd
        have hka := (Nat.prime_two.pow_dvd_iff_le_factorization hk_pos.ne').mp hdvd
        refine (Nat.prime_two.pow_dvd_iff_le_factorization hbk_pos.ne').mpr ?_
        omega
    · have hval := two_adic_pow_sub_one_factorization_odd hb1 hb_odd hk_pos.ne' hk_odd
      constructor
      · intro hdvd
        exfalso
        have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hbk_pos.ne').mp hdvd
        omega
      · intro hdvd
        exfalso
        have h2k : (2 : Nat) ∣ k := dvd_trans (dvd_pow_self 2 ha.ne') hdvd
        rcases hk_odd with ⟨j, hj⟩
        rcases h2k with ⟨i, hi⟩
        omega

theorem exists_exactOrderPrimePowerWitness
    {b n : Nat} (hb : 2 ≤ b) (hn : 2 ≤ n) :
    ∃ q s : Nat, ExactOrderPrimePowerWitness b n q s := by
  obtain ⟨q, hq, hdvd⟩ := exists_prime_dvd_cyclotomic_eval hb hn
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hroot : (Polynomial.cyclotomic n (ZMod q)).IsRoot ((b : Nat) : ZMod q) := by
    have hcast :
        (((Polynomial.cyclotomic n Int).eval ((b : Nat) : Int) : Int) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
    have hcomm : (Polynomial.cyclotomic n (ZMod q)).eval (((b : Nat) : Int) : ZMod q)
        = (((Polynomial.cyclotomic n Int).eval ((b : Nat) : Int) : Int) : ZMod q) := by
      rw [← Polynomial.map_cyclotomic_int n (ZMod q), Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply (Int.castRingHom (ZMod q)) _
    have hbcast : (((b : Nat) : Int) : ZMod q) = ((b : Nat) : ZMod q) := by
      push_cast
      rfl
    show (Polynomial.cyclotomic n (ZMod q)).eval ((b : Nat) : ZMod q) = 0
    rw [← hbcast, hcomm, hcast]
  obtain ⟨a, ha_eq⟩ :=
    orderOf_isRoot_cyclotomic_zmod_pow_mul hq n (by omega) _ hroot
  have hqb : ¬ q ∣ b := by
    intro hqb
    have hx0 : ((b : Nat) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff b q).mpr hqb
    have h1 : (Polynomial.cyclotomic n (ZMod q)).coeff 0 = 1 :=
      Polynomial.cyclotomic_coeff_zero (ZMod q) (by omega)
    have h0 : (Polynomial.cyclotomic n (ZMod q)).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      have hroot0 := hroot
      rw [Polynomial.IsRoot, hx0] at hroot0
      exact hroot0
    rw [h1] at h0
    exact one_ne_zero h0
  have hcop : Nat.Coprime b q := (hq.coprime_iff_not_dvd.mpr hqb).symm
  have hord_eq : orderOf (ZMod.unitOfCoprime b hcop)
      = orderOf ((b : Nat) : ZMod q) := by
    conv_rhs => rw [← ZMod.coe_unitOfCoprime b hcop]
    exact orderOf_units.symm
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · have hn_eq : n = orderOf ((b : Nat) : ZMod q) := by simpa using ha_eq
    refine ⟨q, 1, exactOrderPrimePowerWitness_of_orderOf_prime hq (by omega) hcop ?_⟩
    rw [hord_eq, ← hn_eq]
  · by_cases hq2 : q = 2
    · subst hq2
      have hb_odd : Odd b := by
        rcases Nat.even_or_odd b with he | ho
        · exact absurd he.two_dvd hqb
        · exact ho
      have hm1 : orderOf ((b : Nat) : ZMod 2) = 1 := by
        have h2b1 : (2 : Nat) ∣ b ^ 1 - 1 := by
          rcases hb_odd with ⟨j, hj⟩
          simp only [pow_one]
          exact ⟨j, by omega⟩
        have hdvd1 : orderOf (ZMod.unitOfCoprime b hcop) ∣ 1 :=
          (orderOf_dvd_iff_q_dvd_pow_sub_one hcop
            (Nat.one_le_pow 1 b (by omega))).mpr h2b1
        have h1 := Nat.dvd_one.mp hdvd1
        rw [hord_eq] at h1
        exact h1
      have hn_eq : n = 2 ^ a := by
        rw [ha_eq, hm1, mul_one]
      rw [hn_eq]
      exact ⟨2, _, exactOrderPrimePowerWitness_lift_two hb hb_odd ha_pos⟩
    · have hq_odd : Odd q := hq.odd_of_ne_two hq2
      rw [ha_eq]
      exact ⟨q, _, exactOrderPrimePowerWitness_lift_odd hq hq_odd hb hcop
        hord_eq.symm ha_pos⟩

/-! ## The unconditional finite period non-collapse theorem -/

/-- Common numerator `A = ∑_{n ∈ F} (b ^ lcm F - 1) / (b ^ n - 1)` of the sum
`∑_{n ∈ F} 1 / (b ^ n - 1)` over the common denominator `b ^ lcm F - 1`. -/
def commonNumerator (F : Finset Nat) (b : Nat) : Nat :=
  ∑ n ∈ F, (b ^ F.lcm id - 1) / (b ^ n - 1)

/-- Common denominator `B = b ^ lcm F - 1` of `∑_{n ∈ F} 1 / (b ^ n - 1)`. -/
def commonDenominator (F : Finset Nat) (b : Nat) : Nat :=
  b ^ F.lcm id - 1

/-- Reduced denominator `Q` of `∑_{n ∈ F} 1 / (b ^ n - 1)` in lowest terms. -/
def reducedDenominator (F : Finset Nat) (b : Nat) : Nat :=
  commonDenominator F b / Nat.gcd (commonNumerator F b) (commonDenominator F b)

theorem coprime_base_reducedDenominator
    (F : Finset Nat) (b : Nat) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    Nat.Coprime b (reducedDenominator F b) := by
  have hL0 : F.lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hxF, hx0⟩
    rw [id_eq] at hx0
    exact h0 (hx0 ▸ hxF)
  have h1 : 1 ≤ b ^ F.lcm id := Nat.one_le_pow _ _ (by omega)
  have hcopB : Nat.Coprime b (commonDenominator F b) := by
    have hsub : b ^ F.lcm id - commonDenominator F b = 1 := by
      simp only [commonDenominator]
      omega
    have hgcd_dvd_pow : Nat.gcd b (commonDenominator F b) ∣ b ^ F.lcm id :=
      (Nat.gcd_dvd_left _ _).trans (dvd_pow_self b hL0)
    have hgcd_dvd_one : Nat.gcd b (commonDenominator F b) ∣ 1 := by
      rw [← hsub]
      exact Nat.dvd_sub hgcd_dvd_pow (Nat.gcd_dvd_right _ _)
    exact Nat.dvd_one.mp hgcd_dvd_one
  have hQ_dvd : reducedDenominator F b ∣ commonDenominator F b :=
    ⟨Nat.gcd (commonNumerator F b) (commonDenominator F b), by
      rw [reducedDenominator, mul_comm]
      exact gcd_denominator_factor _ _⟩
  exact hcopB.coprime_dvd_right hQ_dvd

/-- **Unconditional finite period non-collapse.**  For every finite nonempty
set `F` of positive exponents and every base `b ≥ 2`, the reduced denominator
`Q` of `∑_{n ∈ F} 1 / (b ^ n - 1)` satisfies `ord_Q(b) = lcm F`.  No
witness-supply hypothesis remains: exact-order prime-power witnesses are
constructed for every selector row via the cyclotomic route. -/
theorem finite_period_noncollapse
    (F : Finset Nat) (b : Nat)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    orderOf (ZMod.unitOfCoprime b (coprime_base_reducedDenominator F b h0 hb))
      = F.lcm id := by
  refine finite_period_noncollapse_from_exact_order_witness_supply
    F (F.lcm id) (commonNumerator F b) (commonDenominator F b)
    (reducedDenominator F b) b
    (coprime_base_reducedDenominator F b h0 hb)
    hF h0 hb rfl rfl rfl rfl ?_
  intro n _ hn2 _
  exact exists_exactOrderPrimePowerWitness hb hn2

/-! ## Rational-denominator bridge and denominator growth

The unconditional theorem above speaks about `reducedDenominator F b`, a
`Nat`-valued construction.  This section identifies that construction with
`Rat.den` of the literal rational partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)`,
restates the theorem over that denominator, and derives the strict
denominator growth bound `lcm F < den`.  The capstone
`lcm_Icc_lt_den_erdosPartialSum` states the growth bound for the classical
partial sums `∑_{n=1}^{N} 1 / (b ^ n - 1)` in pure Mathlib vocabulary. -/

theorem pow_sub_one_pos_of_ne_zero
    (b n : Nat) (hb : 2 ≤ b) (hn : n ≠ 0) :
    0 < b ^ n - 1 := by
  have hbn : b ≤ b ^ n := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ b) (by omega : 1 ≤ n)
  omega

theorem natCast_pow_sub_one (b n : Nat) (hb : 2 ≤ b) :
    ((b ^ n - 1 : Nat) : Rat) = (b : Rat) ^ n - 1 := by
  have h1 : 1 ≤ b ^ n := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]

/-- The finite Erdős partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)` as a rational
number, stated with subtraction in `ℚ` so the statement reads exactly like
the mathematical series. -/
def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)

theorem lcm_ne_zero_of_zero_not_mem
    (F : Finset Nat) (h0 : 0 ∉ F) :
    F.lcm id ≠ 0 := by
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨x, hxF, hx0⟩
  rw [id_eq] at hx0
  exact h0 (hx0 ▸ hxF)

/-- The rational partial sum equals the audited common fraction
`commonNumerator / commonDenominator`. -/
theorem finiteErdosSum_eq_commonNumerator_div_commonDenominator
    (F : Finset Nat) (b : Nat) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    finiteErdosSum F b
      = (commonNumerator F b : Rat) / (commonDenominator F b : Rat) := by
  have hL0 : F.lcm id ≠ 0 := lcm_ne_zero_of_zero_not_mem F h0
  have hD_pos : 0 < commonDenominator F b := by
    simpa [commonDenominator] using pow_sub_one_pos_of_ne_zero b (F.lcm id) hb hL0
  have hD_ne : ((commonDenominator F b : Nat) : Rat) ≠ 0 := by
    exact_mod_cast hD_pos.ne'
  rw [eq_div_iff hD_ne]
  simp only [finiteErdosSum, commonNumerator]
  rw [Finset.sum_mul, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := fun h => h0 (h ▸ hn)
  have hn_dvd : n ∣ F.lcm id := by simpa using Finset.dvd_lcm hn
  have hdvd : b ^ n - 1 ∣ b ^ F.lcm id - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one b hn_dvd
  have hterm_pos : 0 < b ^ n - 1 := pow_sub_one_pos_of_ne_zero b n hb hn0
  have hterm_ne : ((b ^ n - 1 : Nat) : Rat) ≠ 0 := by
    exact_mod_cast hterm_pos.ne'
  simp only [commonDenominator]
  rw [Nat.cast_div hdvd hterm_ne, natCast_pow_sub_one b n hb]
  exact one_div_mul_eq_div _ _

/-- Denominator of a quotient of coprime naturals. -/
theorem den_natCast_div_natCast_of_coprime
    (x y : Nat) (hy : y ≠ 0) (hcop : Nat.Coprime x y) :
    ((x : Rat) / (y : Rat)).den = y := by
  have hb0 : (0 : Int) < (y : Int) := by
    exact_mod_cast Nat.pos_of_ne_zero hy
  have hnat : Nat.Coprime ((x : Int)).natAbs ((y : Int)).natAbs := by
    simpa using hcop
  have h := Rat.den_div_eq_of_coprime hb0 hnat
  have hx : (((x : Int) : Rat)) = (x : Rat) := Int.cast_natCast x
  have hyq : (((y : Int) : Rat)) = (y : Rat) := Int.cast_natCast y
  rw [hx, hyq] at h
  exact_mod_cast h

theorem mul_div_cross_of_dvd
    (g a d : Nat) (hg : 0 < g) (ha : g ∣ a) (hd : g ∣ d) :
    a * (d / g) = a / g * d := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨d', rfl⟩ := hd
  rw [Nat.mul_div_cancel_left a' hg, Nat.mul_div_cancel_left d' hg]
  ring

/-- Denominator of a quotient of naturals, via the gcd. -/
theorem den_natCast_div_natCast (a d : Nat) (hd : d ≠ 0) :
    ((a : Rat) / (d : Rat)).den = d / Nat.gcd a d := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  have hg_pos : 0 < Nat.gcd a d := Nat.gcd_pos_of_pos_right a hd_pos
  have hga : Nat.gcd a d ∣ a := Nat.gcd_dvd_left a d
  have hgd : Nat.gcd a d ∣ d := Nat.gcd_dvd_right a d
  have hd'_pos : 0 < d / Nat.gcd a d :=
    Nat.div_pos (Nat.le_of_dvd hd_pos hgd) hg_pos
  have hcop : Nat.Coprime (a / Nat.gcd a d) (d / Nat.gcd a d) :=
    Nat.coprime_div_gcd_div_gcd hg_pos
  have hval : (a : Rat) / (d : Rat)
      = ((a / Nat.gcd a d : Nat) : Rat) / ((d / Nat.gcd a d : Nat) : Rat) := by
    have hd_ne : ((d : Nat) : Rat) ≠ 0 := by exact_mod_cast hd_pos.ne'
    have hdg_ne : ((d / Nat.gcd a d : Nat) : Rat) ≠ 0 := by
      exact_mod_cast hd'_pos.ne'
    rw [div_eq_div_iff hd_ne hdg_ne]
    exact_mod_cast mul_div_cross_of_dvd (Nat.gcd a d) a d hg_pos hga hgd
  rw [hval, den_natCast_div_natCast_of_coprime _ _ hd'_pos.ne' hcop]

/-- **Statement-faithfulness bridge.**  The audited `reducedDenominator F b`
is literally `Rat.den` of the rational partial sum `∑_{n ∈ F} 1 / (b^n - 1)`:
the theorem about the constructed denominator is a theorem about the actual
reduced denominator of the actual rational number. -/
theorem finiteErdosSum_den_eq_reducedDenominator
    (F : Finset Nat) (b : Nat) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    (finiteErdosSum F b).den = reducedDenominator F b := by
  have hL0 : F.lcm id ≠ 0 := lcm_ne_zero_of_zero_not_mem F h0
  have hD_pos : 0 < commonDenominator F b := by
    simpa [commonDenominator] using pow_sub_one_pos_of_ne_zero b (F.lcm id) hb hL0
  rw [finiteErdosSum_eq_commonNumerator_div_commonDenominator F b h0 hb,
    den_natCast_div_natCast _ _ hD_pos.ne', reducedDenominator]

theorem coprime_base_den_finiteErdosSum
    (F : Finset Nat) (b : Nat) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    Nat.Coprime b (finiteErdosSum F b).den := by
  rw [finiteErdosSum_den_eq_reducedDenominator F b h0 hb]
  exact coprime_base_reducedDenominator F b h0 hb

/-- Concrete-transport wrapper: the unconditional theorem restated over any
naturals `L`, `Q` proven equal to `lcm F` and the reduced denominator.  This
is the thin interface a theorem-route certificate emitter instantiates: a
generated target supplies `F`, `b`, the two normalisation equalities, and a
coprimality witness, and receives the exact-order conclusion with no
per-prime witness rows. -/
theorem finite_period_noncollapse_concrete
    (F : Finset Nat) (b L Q : Nat)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hL : L = F.lcm id) (hQ : Q = reducedDenominator F b)
    (hcop : Nat.Coprime b Q) :
    orderOf (ZMod.unitOfCoprime b hcop) = L := by
  subst hL
  subst hQ
  exact finite_period_noncollapse F b hF h0 hb

/-- The unconditional finite theorem stated over `Rat.den` of the literal
rational partial sum: `ord_Q(b) = lcm F` where `Q` is the denominator in
lowest terms of `∑_{n ∈ F} 1 / (b ^ n - 1)` as a rational number. -/
theorem finite_period_noncollapse_rat_den
    (F : Finset Nat) (b : Nat)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    orderOf (ZMod.unitOfCoprime b (coprime_base_den_finiteErdosSum F b h0 hb))
      = F.lcm id :=
  finite_period_noncollapse_concrete F b (F.lcm id) (finiteErdosSum F b).den
    hF h0 hb rfl (finiteErdosSum_den_eq_reducedDenominator F b h0 hb)
    (coprime_base_den_finiteErdosSum F b h0 hb)

/-- **Denominator growth.**  The reduced denominator of the finite Erdős
partial sum strictly dominates `lcm F`: since `ord_Q(b) = lcm F` and the
order divides `φ(Q) < Q`, the denominator can never collapse below the lcm.
This is the quantitative engine an irrationality attack on the infinite
series needs from the finite layer. -/
theorem lcm_lt_den_finiteErdosSum
    (F : Finset Nat) (b : Nat)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den := by
  have hord :
      orderOf (ZMod.unitOfCoprime b (coprime_base_den_finiteErdosSum F b h0 hb))
        = F.lcm id :=
    finite_period_noncollapse_rat_den F b hF h0 hb
  have hQ_pos : 0 < (finiteErdosSum F b).den := Rat.den_pos _
  haveI : NeZero (finiteErdosSum F b).den := ⟨hQ_pos.ne'⟩
  have hdvd :
      orderOf (ZMod.unitOfCoprime b (coprime_base_den_finiteErdosSum F b h0 hb))
        ∣ Fintype.card (ZMod (finiteErdosSum F b).den)ˣ :=
    orderOf_dvd_card
  rw [ZMod.card_units_eq_totient, hord] at hdvd
  have hle : F.lcm id ≤ ((finiteErdosSum F b).den).totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr hQ_pos) hdvd
  have hQ1 : 1 < (finiteErdosSum F b).den := by
    rcases Nat.lt_or_ge 1 (finiteErdosSum F b).den with h | h
    · exact h
    · have hQ_eq : (finiteErdosSum F b).den = 1 := by omega
      rw [hQ_eq, Nat.totient_one] at hle
      omega
  exact lt_of_le_of_lt hle (Nat.totient_lt _ hQ1)

/-- **Denominator growth for the classical partial sums.**  For every base
`b ≥ 2` and every `N ≥ 2`, the reduced denominator of
`∑_{n=1}^{N} 1 / (b ^ n - 1)` strictly exceeds `lcm(1, …, N)`.  Stated in
pure Mathlib vocabulary: no project-local definition appears in the
statement. -/
theorem lcm_Icc_lt_den_erdosPartialSum
    (b N : Nat) (hb : 2 ≤ b) (hN : 2 ≤ N) :
    (Finset.Icc 1 N).lcm id
      < (∑ n ∈ Finset.Icc 1 N, 1 / ((b : Rat) ^ n - 1)).den := by
  have h0 : (0 : Nat) ∉ Finset.Icc 1 N := by
    simp [Finset.mem_Icc]
  have hF : (Finset.Icc 1 N).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩⟩
  have h2mem : (2 : Nat) ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨by omega, hN⟩
  have h2dvd : (2 : Nat) ∣ (Finset.Icc 1 N).lcm id := by
    simpa using Finset.dvd_lcm h2mem
  have hlcm_ne : (Finset.Icc 1 N).lcm id ≠ 0 :=
    lcm_ne_zero_of_zero_not_mem _ h0
  have h2 : 2 ≤ (Finset.Icc 1 N).lcm id :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hlcm_ne) h2dvd
  have hmain := lcm_lt_den_finiteErdosSum (Finset.Icc 1 N) b hF h0 hb h2
  simpa [finiteErdosSum] using hmain

/-! ## Infinite bridge: irrationality criterion and first infinite-support instances

The finite theorems above are exact statements about the reduced denominators
of the partial sums.  This section turns that denominator authority into an
irrationality engine for the *infinite* series: the Dirichlet-gap criterion
`irrational_of_den_mul_abs_sub_tendsto_zero` needs exactly an upper bound on
`Rat.den` of the partial sums times the tail, and `den_finiteErdosSum_dvd`
supplies it from the kernel's own common-denominator lattice.  The class
theorem `irrational_erdosSum_of_lcm_gap` proves irrationality of
`∑ 1 / (b ^ (a k) - 1)` for every base `b ≥ 2` whenever the support outruns
the lcm of its own prefix; factorial and geometric supports instantiate it,
giving the first infinite-series irrationality theorems in this development —
including the literal base-2 members of the Erdős #257 statement family.
The universal problem (every infinite support) remains open and is not
claimed. -/

open Filter Topology

/-- A strictly monotone `ℕ`-sequence gains at least one per step:
`a k + i ≤ a (k + i)`. -/
theorem strictMono_add_le_apply {a : ℕ → ℕ} (ha : StrictMono a) (k i : ℕ) :
    a k + i ≤ a (k + i) := by
  induction i with
  | zero => simp
  | succ n ih =>
      have h1 : a (k + n) < a (k + n + 1) := ha (Nat.lt_succ_self _)
      have h2 : k + (n + 1) = k + n + 1 := by omega
      rw [h2]
      omega

/-- **Rational gap.**  Two distinct rationals are at least
`1 / (den · den)` apart as real numbers. -/
theorem one_div_den_mul_den_le_abs_sub {q r : ℚ} (h : q ≠ r) :
    (1 : ℝ) / ((q.den : ℝ) * (r.den : ℝ)) ≤ |(q : ℝ) - (r : ℝ)| := by
  have hne : q - r ≠ 0 := sub_ne_zero.mpr h
  have hdvd : (q - r).den ∣ q.den * r.den := Rat.sub_den_dvd q r
  have hden_pos : (0 : ℝ) < ((q - r).den : ℝ) := by
    exact_mod_cast (q - r).den_pos
  have hnum : (1 : ℤ) ≤ |(q - r).num| := Int.one_le_abs (Rat.num_ne_zero.mpr hne)
  have h1d : (0 : ℝ) < 1 / ((q - r).den : ℝ) := by positivity
  have habs : (1 : ℝ) / (((q - r).den : ℝ)) ≤ |((q - r : ℚ) : ℝ)| := by
    calc (1 : ℝ) / (((q - r).den : ℝ))
        = 1 * (1 / (((q - r).den : ℝ))) := (one_mul _).symm
      _ ≤ |((q - r).num : ℝ)| * (1 / (((q - r).den : ℝ))) := by
          apply mul_le_mul_of_nonneg_right ?_ h1d.le
          exact_mod_cast hnum
      _ = |((q - r).num : ℝ)| / (((q - r).den : ℝ)) := mul_one_div _ _
      _ = |((q - r).num : ℝ) / (((q - r).den : ℝ))| := by
          rw [abs_div, abs_of_pos hden_pos]
      _ = |((q - r : ℚ) : ℝ)| := by rw [Rat.cast_def]
  calc (1 : ℝ) / ((q.den : ℝ) * (r.den : ℝ))
      ≤ 1 / (((q - r).den : ℝ)) := by
        apply one_div_le_one_div_of_le hden_pos
        exact_mod_cast Nat.le_of_dvd (Nat.mul_pos q.den_pos r.den_pos) hdvd
    _ ≤ |((q - r : ℚ) : ℝ)| := habs
    _ = |(q : ℝ) - (r : ℝ)| := by push_cast; ring_nf

/-- **Irrationality criterion.**  If a sequence of rationals is eventually
never equal to `x` and `den(u k) * |x - u k| → 0`, then `x` is irrational.
This is the Dirichlet-gap argument stated over `Rat.den` — the same
denominator object the finite kernel theorems audit. -/
theorem irrational_of_den_mul_abs_sub_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in atTop, ((u k : ℝ)) ≠ x)
    (h0 : Tendsto (fun k => ((u k).den : ℝ) * |x - (u k : ℝ)|) atTop (nhds 0)) :
    Irrational x := by
  rintro ⟨q, rfl⟩
  have hq_pos : (0 : ℝ) < 1 / (q.den : ℝ) := by positivity
  have hev : ∀ᶠ k in atTop,
      ((u k).den : ℝ) * |(q : ℝ) - (u k : ℝ)| < 1 / (q.den : ℝ) :=
    h0.eventually (gt_mem_nhds hq_pos)
  obtain ⟨k, hk_ne, hk_lt⟩ := (hne.and hev).exists
  have hqu : q ≠ u k := fun hEq => hk_ne (by rw [hEq])
  have hd_pos : (0 : ℝ) < ((u k).den : ℝ) := by exact_mod_cast (u k).den_pos
  have hgap := one_div_den_mul_den_le_abs_sub hqu
  have hmul : (1 : ℝ) / (q.den : ℝ)
      ≤ ((u k).den : ℝ) * |(q : ℝ) - ((u k : ℚ) : ℝ)| := by
    have h1 : ((u k).den : ℝ)
        * ((1 : ℝ) / ((q.den : ℝ) * ((u k).den : ℝ))) = 1 / (q.den : ℝ) := by
      field_simp
    calc (1 : ℝ) / (q.den : ℝ)
        = ((u k).den : ℝ) * (1 / ((q.den : ℝ) * ((u k).den : ℝ))) := h1.symm
      _ ≤ ((u k).den : ℝ) * |(q : ℝ) - ((u k : ℚ) : ℝ)| :=
          mul_le_mul_of_nonneg_left hgap hd_pos.le
  exact absurd (lt_of_le_of_lt hmul hk_lt) (lt_irrefl _)

/-- The reduced denominator of the finite Erdős partial sum divides the
common denominator `b ^ lcm F - 1`. -/
theorem den_finiteErdosSum_dvd
    (F : Finset Nat) (b : Nat) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    (finiteErdosSum F b).den ∣ b ^ (F.lcm id) - 1 := by
  rw [finiteErdosSum_den_eq_reducedDenominator F b h0 hb]
  show commonDenominator F b / Nat.gcd (commonNumerator F b) (commonDenominator F b)
      ∣ b ^ (F.lcm id) - 1
  have hg : Nat.gcd (commonNumerator F b) (commonDenominator F b)
      ∣ commonDenominator F b := Nat.gcd_dvd_right _ _
  have hself : commonDenominator F b
      / Nat.gcd (commonNumerator F b) (commonDenominator F b)
      ∣ commonDenominator F b :=
    ⟨Nat.gcd (commonNumerator F b) (commonDenominator F b),
      (Nat.div_mul_cancel hg).symm⟩
  simpa [commonDenominator] using hself

/-- A single Erdős summand has exactly its displayed Mersenne denominator. -/
theorem erdosTerm_den_eq (b n : Nat) (hb : 2 ≤ b) (hn : n ≠ 0) :
    (1 / ((b : Rat) ^ n - 1)).den = b ^ n - 1 := by
  rw [← natCast_pow_sub_one b n hb]
  exact den_natCast_div_natCast_of_coprime
    1 (b ^ n - 1) (pow_sub_one_pos_of_ne_zero b n hb hn).ne'
    (Nat.coprime_one_left _)

/-- The actual reduced denominator of a finite Erdős sum divides the lcm of
the displayed term denominators.  This can be much sharper than the generic
common denominator `b ^ lcm(F) - 1`. -/
theorem den_finiteErdosSum_dvd_termDenominatorLcm
    (F : Finset Nat) (b : Nat) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    (finiteErdosSum F b).den ∣ F.lcm (fun n => b ^ n - 1) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp [finiteErdosSum]
  | @insert n F hnF ih =>
      have hn0 : n ≠ 0 := fun hnEq => h0 (by simpa [hnEq])
      have h0F : 0 ∉ F := fun hmem => h0 (Finset.mem_insert_of_mem hmem)
      have ih' := ih h0F
      have hadd :
          (finiteErdosSum (insert n F) b).den ∣
            Nat.lcm (1 / ((b : Rat) ^ n - 1)).den
              (finiteErdosSum F b).den := by
        simpa [finiteErdosSum, Finset.sum_insert hnF] using
          Rat.add_den_dvd_lcm
            (1 / ((b : Rat) ^ n - 1)) (finiteErdosSum F b)
      rw [erdosTerm_den_eq b n hb hn0] at hadd
      rw [Finset.lcm_insert]
      exact hadd.trans (Nat.lcm_dvd
        (Nat.dvd_lcm_left _ _)
        (ih'.trans (Nat.dvd_lcm_right _ _)))

/-- Summability of the Erdős terms along any strictly monotone support with
positive first element. -/
theorem summable_erdos_term (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ)
    (ha : StrictMono a) (ha0 : 1 ≤ a 0) :
    Summable (fun k => (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hak : ∀ k, k + 1 ≤ a k := by
    intro k
    have h := strictMono_add_le_apply ha 0 k
    rw [Nat.zero_add] at h
    omega
  have hpow : ∀ k, (2 : ℝ) ^ (k + 1) ≤ (b : ℝ) ^ (a k) := by
    intro k
    calc (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (a k) := by
          apply pow_le_pow_right₀ (by norm_num) (hak k)
      _ ≤ (b : ℝ) ^ (a k) := by
          apply pow_le_pow_left₀ (by norm_num) hb2
  have hone : ∀ k : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ k := fun k => one_le_pow₀ (by norm_num)
  have hterm_pos : ∀ k, (0 : ℝ) < (b : ℝ) ^ (a k) - 1 := by
    intro k
    have h1 := hpow k
    have h2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have h3 := hone k
    nlinarith
  refine Summable.of_nonneg_of_le
    (fun k => (div_pos one_pos (hterm_pos k)).le) (fun k => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1))
  have h1 : (2 : ℝ) ^ k ≤ (b : ℝ) ^ (a k) - 1 := by
    have h2 := hpow k
    have h3 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have h4 := hone k
    nlinarith
  calc (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)
      ≤ 1 / (2 : ℝ) ^ k := by
        apply one_div_le_one_div_of_le (by positivity) h1
    _ = ((1 : ℝ) / 2) ^ k := by rw [div_pow, one_pow]

/-- The shifted-tail terms are summable. -/
theorem summable_erdos_term_shift (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ)
    (ha : StrictMono a) (ha0 : 1 ≤ a 0) (k : ℕ) :
    Summable (fun i => (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)) :=
  ((summable_nat_add_iff k).mpr (summable_erdos_term b hb a ha ha0))

/-- Positivity of every Erdős term. -/
theorem erdos_term_pos (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ)
    (ha : StrictMono a) (ha0 : 1 ≤ a 0) (j : ℕ) :
    (0 : ℝ) < 1 / ((b : ℝ) ^ (a j) - 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have haj : 1 ≤ a j := le_trans ha0 (ha.monotone (Nat.zero_le j))
  have h1 : (2 : ℝ) ≤ (b : ℝ) ^ (a j) := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ (a j) := by apply pow_le_pow_right₀ (by norm_num) haj
      _ ≤ (b : ℝ) ^ (a j) := by apply pow_le_pow_left₀ (by norm_num) hb2
  have hpos : (0 : ℝ) < (b : ℝ) ^ (a j) - 1 := by linarith
  positivity

/-- The tail after `k` terms is strictly positive. -/
theorem erdos_tail_pos (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ)
    (ha : StrictMono a) (ha0 : 1 ≤ a 0) (k : ℕ) :
    (0 : ℝ) < ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := by
  have hsum := summable_erdos_term_shift b hb a ha ha0 k
  have hpos : ∀ i, (0 : ℝ) ≤ 1 / ((b : ℝ) ^ (a (i + k)) - 1) :=
    fun i => (erdos_term_pos b hb a ha ha0 (i + k)).le
  exact hsum.tsum_pos hpos 0 (erdos_term_pos b hb a ha ha0 (0 + k))

/-- Geometric tail estimate: the tail after `k` terms is at most
`4 * (1/b) ^ (a k)`. -/
theorem erdos_tail_le (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ)
    (ha : StrictMono a) (ha0 : 1 ≤ a 0) (k : ℕ) :
    ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)
      ≤ 4 * ((1 : ℝ) / b) ^ (a k) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hrb0 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hrb1 : (1 : ℝ) / (b : ℝ) < 1 := by
    rw [div_lt_one hb_pos]; linarith
  have hterm : ∀ i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)
      ≤ (2 * ((1 : ℝ) / b) ^ (a k)) * ((1 : ℝ) / b) ^ i := by
    intro i
    have hshift : a k + i ≤ a (i + k) := by
      have h := strictMono_add_le_apply ha k i
      have hcomm : a (k + i) = a (i + k) := by rw [Nat.add_comm]
      omega
    have h1 : 1 ≤ a (i + k) := le_trans ha0 (ha.monotone (Nat.zero_le _))
    have hX2 : (2 : ℝ) ≤ (b : ℝ) ^ (a (i + k)) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ (a (i + k)) := by
            apply pow_le_pow_right₀ (by norm_num) h1
        _ ≤ (b : ℝ) ^ (a (i + k)) := by
            apply pow_le_pow_left₀ (by norm_num) hb2
    have hXpos : (0 : ℝ) < (b : ℝ) ^ (a (i + k)) - 1 := by linarith
    have h2X : (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)
        ≤ 2 / (b : ℝ) ^ (a (i + k)) := by
      rw [div_le_div_iff₀ hXpos (by positivity)]
      nlinarith
    have hmono : ((1 : ℝ) / b) ^ (a (i + k)) ≤ ((1 : ℝ) / b) ^ (a k + i) :=
      pow_le_pow_of_le_one hrb0 hrb1.le hshift
    calc (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)
        ≤ 2 / (b : ℝ) ^ (a (i + k)) := h2X
      _ = 2 * ((1 : ℝ) / b) ^ (a (i + k)) := by
          rw [div_pow, one_pow]; ring
      _ ≤ 2 * ((1 : ℝ) / b) ^ (a k + i) := by
          apply mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ = (2 * ((1 : ℝ) / b) ^ (a k)) * ((1 : ℝ) / b) ^ i := by
          rw [pow_add]; ring
  have hgeom : Summable (fun i => ((1 : ℝ) / b) ^ i) :=
    summable_geometric_of_lt_one hrb0 hrb1
  have hg_sum : Summable (fun i => (2 * ((1 : ℝ) / b) ^ (a k)) * ((1 : ℝ) / b) ^ i) :=
    hgeom.mul_left _
  have hf_sum := summable_erdos_term_shift b hb a ha ha0 k
  have hb_inv : (1 : ℝ) / (b : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hb_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hpos1 : (0 : ℝ) < 1 - 1 / (b : ℝ) := by linarith
  calc ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)
      ≤ ∑' i, (2 * ((1 : ℝ) / b) ^ (a k)) * ((1 : ℝ) / b) ^ i :=
        hf_sum.tsum_le_tsum hterm hg_sum
    _ = (2 * ((1 : ℝ) / b) ^ (a k)) * ∑' i, ((1 : ℝ) / b) ^ i := tsum_mul_left
    _ = (2 * ((1 : ℝ) / b) ^ (a k)) * (1 - 1 / (b : ℝ))⁻¹ := by
        rw [tsum_geometric_of_lt_one hrb0 hrb1]
    _ ≤ (2 * ((1 : ℝ) / b) ^ (a k)) * 2 := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [inv_eq_one_div, div_le_iff₀ hpos1]
        linarith
    _ = 4 * ((1 : ℝ) / b) ^ (a k) := by ring

/-- Casting the finite Erdős sum over the image support to the reals gives
the real partial sum. -/
theorem finiteErdosSum_image_range_cast (b : ℕ) (a : ℕ → ℕ)
    (ha : StrictMono a) (k : ℕ) :
    ((finiteErdosSum ((Finset.range k).image a) b : ℚ) : ℝ)
      = ∑ i ∈ Finset.range k, (1 : ℝ) / ((b : ℝ) ^ (a i) - 1) := by
  show (((∑ n ∈ (Finset.range k).image a, 1 / ((b : ℚ) ^ n - 1)) : ℚ) : ℝ) = _
  rw [Finset.sum_image (fun x _ y _ h => ha.injective h)]
  push_cast
  rfl

/-- A positive strictly monotone support never places exponent zero in any
finite prefix. -/
theorem zero_not_mem_image_range_of_strictMono_pos
    (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0) (k : ℕ) :
    0 ∉ (Finset.range k).image a := by
  intro hmem
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  have hai : 1 ≤ a i := le_trans ha0 (ha.monotone (Nat.zero_le i))
  omega

/-- **Pointwise rational-tail obstruction.**  If the infinite Erdős support
sum equals a rational `q`, then every nonzero tail is at least the Farey
spacing `1 / (den(q) * Qₖ)`, where `Qₖ` is the actual reduced denominator of
the corresponding prefix.  Unlike the asymptotic irrationality criterion,
this is a quantitative inequality at every prefix. -/
theorem rational_erdosSum_prefix_tail_lower
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (q : ℚ)
    (hq : (∑' j, (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) = (q : ℝ))
    (k : ℕ) :
    (1 : ℝ) /
        ((q.den : ℝ) *
          ((finiteErdosSum ((Finset.range k).image a) b).den : ℝ))
      ≤ ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := by
  have hsum : Summable (fun j => (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) :=
    summable_erdos_term b hb a ha ha0
  set x : ℝ := ∑' j, (1 : ℝ) / ((b : ℝ) ^ (a j) - 1) with hx
  set u : ℚ := finiteErdosSum ((Finset.range k).image a) b with hu
  have hxq : x = (q : ℝ) := by
    simpa [x] using hq
  have hval : (q : ℝ) - (u : ℝ)
      = ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := by
    have hsplit := hsum.sum_add_tsum_nat_add k
    have hcast := finiteErdosSum_image_range_cast b a ha k
    have huk : ((u : ℚ) : ℝ)
        = ∑ i ∈ Finset.range k, (1 : ℝ) / ((b : ℝ) ^ (a i) - 1) := by
      rw [hu]
      exact hcast
    rw [← hxq, huk]
    linarith
  have htail_pos := erdos_tail_pos b hb a ha ha0 k
  have hqu : q ≠ u := by
    intro hEq
    have h := hval
    rw [hEq] at h
    simp only [sub_self] at h
    linarith
  have habs : |(q : ℝ) - (u : ℝ)|
      = ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := by
    rw [hval]
    exact abs_of_pos htail_pos
  calc
    (1 : ℝ) / ((q.den : ℝ) * ((finiteErdosSum
        ((Finset.range k).image a) b).den : ℝ))
        ≤ |(q : ℝ) - (u : ℝ)| := by
          simpa [hu] using one_div_den_mul_den_le_abs_sub hqu
    _ = ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := habs

/-- **Pointwise reduced-denominator saturation.**  A rational value forces
the actual reduced denominator `Qₖ` of every prefix to satisfy
`b ^ a(k) ≤ 4 * den(q) * Qₖ`.  This is the quantitative lower bound hidden
behind the subsequence irrationality criterion, not merely its asymptotic
contrapositive. -/
theorem rational_erdosSum_prefix_denominator_saturation
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (q : ℚ)
    (hq : (∑' j, (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) = (q : ℝ))
    (k : ℕ) :
    (b : ℝ) ^ (a k) ≤
      4 * (q.den : ℝ) *
        ((finiteErdosSum ((Finset.range k).image a) b).den : ℝ) := by
  set u : ℚ := finiteErdosSum ((Finset.range k).image a) b with hu
  have hfrac :
      (1 : ℝ) / ((q.den : ℝ) * (u.den : ℝ))
        ≤ 4 / ((b : ℝ) ^ (a k)) := by
    calc
      (1 : ℝ) / ((q.den : ℝ) * (u.den : ℝ))
          ≤ ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := by
            simpa [hu] using
              rational_erdosSum_prefix_tail_lower b hb a ha ha0 q hq k
      _ ≤ 4 * ((1 : ℝ) / b) ^ (a k) :=
            erdos_tail_le b hb a ha ha0 k
      _ = 4 / ((b : ℝ) ^ (a k)) := by
            rw [div_pow, one_pow]
            ring
  have hden_pos : (0 : ℝ) < (q.den : ℝ) * (u.den : ℝ) := by positivity
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hb)
  have hpow_pos : (0 : ℝ) < (b : ℝ) ^ (a k) := pow_pos hb_pos _
  rw [div_le_div_iff₀ hden_pos hpow_pos] at hfrac
  simpa [hu, mul_assoc] using hfrac

/-- **Rational-support saturation package.**  At every nonempty prefix, a
hypothetical rational Erdős sum forces one and the same reduced denominator
to be exponentially large at the next support scale, to have exact
multiplicative order equal to the exponent lcm, and to divide the lcm of the
displayed Mersenne term denominators. -/
theorem rational_erdosSum_prefix_saturation_order_lcm
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (q : ℚ)
    (hq : (∑' j, (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) = (q : ℝ))
    (k : ℕ) (hk : 0 < k) :
    (b : ℝ) ^ (a k) ≤
        4 * (q.den : ℝ) *
          ((finiteErdosSum ((Finset.range k).image a) b).den : ℝ) ∧
      orderOf
          (ZMod.unitOfCoprime b
            (coprime_base_den_finiteErdosSum ((Finset.range k).image a) b
              (zero_not_mem_image_range_of_strictMono_pos a ha ha0 k) hb))
        = ((Finset.range k).image a).lcm id ∧
      (finiteErdosSum ((Finset.range k).image a) b).den ∣
        ((Finset.range k).image a).lcm (fun n => b ^ n - 1) := by
  have hF : ((Finset.range k).image a).Nonempty :=
    ⟨a 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, rfl⟩⟩
  have h0 := zero_not_mem_image_range_of_strictMono_pos a ha ha0 k
  exact ⟨
    rational_erdosSum_prefix_denominator_saturation b hb a ha ha0 q hq k,
    finite_period_noncollapse_rat_den ((Finset.range k).image a) b hF h0 hb,
    den_finiteErdosSum_dvd_termDenominatorLcm
      ((Finset.range k).image a) b h0 hb⟩

/-- **Sharp geometric tail envelope.**  A strictly increasing exponent tail
is strictly smaller than the geometric series whose first term is the actual
first Mersenne denominator.  This replaces the coarse factor-four bound by
an asymptotically optimal factor `b / (b - 1)`. -/
theorem erdos_tail_lt_first_term_geometric
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ)
    (ha : StrictMono a) (ha0 : 1 ≤ a 0) (k : ℕ) :
    ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)
      < (b : ℝ) /
          (((b : ℝ) - 1) * ((b : ℝ) ^ (a k) - 1)) := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hb)
  have hb_one : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hb)
  have hr0 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hr1 : (1 : ℝ) / (b : ℝ) < 1 := by
    rw [div_lt_one hb_pos]
    exact hb_one
  have hak : 1 ≤ a k := le_trans ha0 (ha.monotone (Nat.zero_le k))
  have hfirst_pos : (0 : ℝ) < (b : ℝ) ^ (a k) - 1 := by
    have : (1 : ℝ) < (b : ℝ) ^ (a k) := by
      calc
        (1 : ℝ) = (b : ℝ) ^ 0 := by simp
        _ < (b : ℝ) ^ (a k) :=
          pow_lt_pow_right₀ hb_one (by omega)
    linarith
  have hterm :
      ∀ i,
        (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)
          ≤ (1 / ((b : ℝ) ^ (a k) - 1)) *
              ((1 : ℝ) / b) ^ i := by
    intro i
    have hshift : a k + i ≤ a (i + k) := by
      have h := strictMono_add_le_apply ha k i
      have hcomm : a (k + i) = a (i + k) := by rw [Nat.add_comm]
      omega
    have hpow :
        (b : ℝ) ^ (a k + i) ≤ (b : ℝ) ^ (a (i + k)) := by
      exact pow_le_pow_right₀ hb_one.le hshift
    have hbi_one : (1 : ℝ) ≤ (b : ℝ) ^ i :=
      one_le_pow₀ hb_one.le
    have hden :
        (b : ℝ) ^ i * ((b : ℝ) ^ (a k) - 1)
          ≤ (b : ℝ) ^ (a (i + k)) - 1 := by
      rw [mul_sub, ← pow_add]
      rw [Nat.add_comm i (a k)]
      nlinarith
    have hprod_pos :
        (0 : ℝ) <
          (b : ℝ) ^ i * ((b : ℝ) ^ (a k) - 1) :=
      mul_pos (pow_pos hb_pos _) hfirst_pos
    calc
      (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)
          ≤ 1 /
              ((b : ℝ) ^ i * ((b : ℝ) ^ (a k) - 1)) := by
            exact one_div_le_one_div_of_le hprod_pos hden
      _ = (1 / ((b : ℝ) ^ (a k) - 1)) *
              ((1 : ℝ) / b) ^ i := by
            rw [div_pow, one_pow]
            field_simp [ne_of_gt hb_pos, ne_of_gt hfirst_pos]
  have hg :
      Summable
        (fun i =>
          (1 / ((b : ℝ) ^ (a k) - 1)) *
            ((1 : ℝ) / b) ^ i) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hnonneg :
      ∀ i, (0 : ℝ) ≤
        (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) :=
    fun i => (erdos_term_pos b hb a ha ha0 (i + k)).le
  have hstrict :
      (1 : ℝ) / ((b : ℝ) ^ (a (1 + k)) - 1)
        < (1 / ((b : ℝ) ^ (a k) - 1)) *
            ((1 : ℝ) / b) ^ 1 := by
    have hshift : a k + 1 ≤ a (1 + k) := by
      have h := strictMono_add_le_apply ha k 1
      have hcomm : a (k + 1) = a (1 + k) := by rw [Nat.add_comm]
      omega
    have hpow :
        (b : ℝ) ^ (a k + 1) ≤ (b : ℝ) ^ (a (1 + k)) :=
      pow_le_pow_right₀ hb_one.le hshift
    have hden :
        (b : ℝ) ^ 1 * ((b : ℝ) ^ (a k) - 1)
          < (b : ℝ) ^ (a (1 + k)) - 1 := by
      rw [pow_one, mul_sub, ← pow_succ']
      nlinarith
    have hprod_pos :
        (0 : ℝ) <
          (b : ℝ) ^ 1 * ((b : ℝ) ^ (a k) - 1) :=
      mul_pos (pow_pos hb_pos _) hfirst_pos
    calc
      (1 : ℝ) / ((b : ℝ) ^ (a (1 + k)) - 1)
          < 1 /
              ((b : ℝ) ^ 1 * ((b : ℝ) ^ (a k) - 1)) :=
            one_div_lt_one_div_of_lt hprod_pos hden
      _ = (1 / ((b : ℝ) ^ (a k) - 1)) *
              ((1 : ℝ) / b) ^ 1 := by
            rw [div_pow, one_pow]
            field_simp [ne_of_gt hb_pos, ne_of_gt hfirst_pos]
  have hsum :
      (∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1))
        < ∑' i,
            (1 / ((b : ℝ) ^ (a k) - 1)) *
              ((1 : ℝ) / b) ^ i :=
    Summable.tsum_lt_tsum_of_nonneg (i := 1)
      hnonneg hterm hstrict hg
  calc
    ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1)
        < ∑' i,
            (1 / ((b : ℝ) ^ (a k) - 1)) *
              ((1 : ℝ) / b) ^ i := hsum
    _ = (1 / ((b : ℝ) ^ (a k) - 1)) *
          ∑' i, ((1 : ℝ) / b) ^ i := tsum_mul_left
    _ = (1 / ((b : ℝ) ^ (a k) - 1)) *
          (1 - 1 / (b : ℝ))⁻¹ := by
            rw [tsum_geometric_of_lt_one hr0 hr1]
    _ = (b : ℝ) /
          (((b : ℝ) - 1) * ((b : ℝ) ^ (a k) - 1)) := by
            field_simp [ne_of_gt hb_pos, ne_of_gt hfirst_pos,
              ne_of_gt (sub_pos.mpr hb_one)]

/-- **Sharp rational-support saturation.**  Rationality forces
`(b - 1) * (b ^ a(k) - 1) < b * den(q) * Qₖ` at every prefix. -/
theorem rational_erdosSum_prefix_denominator_saturation_sharp
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ)
    (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (q : ℚ)
    (hq : (∑' j, (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) = (q : ℝ))
    (k : ℕ) :
    ((b : ℝ) - 1) * ((b : ℝ) ^ (a k) - 1)
      < (b : ℝ) * (q.den : ℝ) *
          ((finiteErdosSum ((Finset.range k).image a) b).den : ℝ) := by
  set u : ℚ := finiteErdosSum ((Finset.range k).image a) b with hu
  have hfrac :
      (1 : ℝ) / ((q.den : ℝ) * (u.den : ℝ))
        < (b : ℝ) /
            (((b : ℝ) - 1) * ((b : ℝ) ^ (a k) - 1)) := by
    exact lt_of_le_of_lt
      (by
        simpa [hu] using
          rational_erdosSum_prefix_tail_lower b hb a ha ha0 q hq k)
      (erdos_tail_lt_first_term_geometric b hb a ha ha0 k)
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hb)
  have hb_one : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hb)
  have hak : 1 ≤ a k := le_trans ha0 (ha.monotone (Nat.zero_le k))
  have hpow_pos : (0 : ℝ) < (b : ℝ) ^ (a k) - 1 := by
    have : (1 : ℝ) < (b : ℝ) ^ (a k) := by
      calc
        (1 : ℝ) = (b : ℝ) ^ 0 := by simp
        _ < (b : ℝ) ^ (a k) :=
          pow_lt_pow_right₀ hb_one (by omega)
    linarith
  have hleft_pos :
      (0 : ℝ) < (q.den : ℝ) * (u.den : ℝ) := by positivity
  have hright_pos :
      (0 : ℝ) <
        ((b : ℝ) - 1) * ((b : ℝ) ^ (a k) - 1) :=
    mul_pos (sub_pos.mpr hb_one) hpow_pos
  rw [div_lt_div_iff₀ hleft_pos hright_pos] at hfrac
  simpa [hu, mul_assoc] using hfrac

/-- At base two, rationality forces the strict inequality
`2 ^ a(k) - 1 < 2 * den(q) * Qₖ`. -/
theorem rational_erdosSum_prefix_denominator_saturation_sharp_two
    (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (q : ℚ)
    (hq : (∑' j, (1 : ℝ) / ((2 : ℝ) ^ (a j) - 1)) = (q : ℝ))
    (k : ℕ) :
    (2 : ℝ) ^ (a k) - 1
      < 2 * (q.den : ℝ) *
          ((finiteErdosSum ((Finset.range k).image a) 2).den : ℝ) := by
  have h :=
    rational_erdosSum_prefix_denominator_saturation_sharp
      2 (by omega) a ha ha0 q hq k
  norm_num at h ⊢
  exact h

/-- Integrality removes the residual `-1`: the clean base-two saturation law
is `2 ^ a(k) ≤ 2 * den(q) * Qₖ`, exactly halving the coarse coefficient. -/
theorem rational_erdosSum_prefix_denominator_saturation_sharp_two_nat
    (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (q : ℚ)
    (hq : (∑' j, (1 : ℝ) / ((2 : ℝ) ^ (a j) - 1)) = (q : ℝ))
    (k : ℕ) :
    2 ^ (a k)
      ≤ 2 * q.den *
          (finiteErdosSum ((Finset.range k).image a) 2).den := by
  have hreal :=
    rational_erdosSum_prefix_denominator_saturation_sharp_two
      a ha ha0 q hq k
  have hpow_one : 1 ≤ 2 ^ (a k) := Nat.one_le_pow _ _ (by omega)
  have hreal' :
      (((2 ^ (a k) - 1 : ℕ) : ℝ))
        < (((2 * q.den *
            (finiteErdosSum ((Finset.range k).image a) 2).den : ℕ) : ℝ)) := by
    simpa [Nat.cast_sub hpow_one] using hreal
  have hnat :
      2 ^ (a k) - 1
        < 2 * q.den *
            (finiteErdosSum ((Finset.range k).image a) 2).den := by
    exact_mod_cast hreal'
  omega

/-- The sharp saturation inequality, exact multiplicative order, and
term-denominator LCM divisibility hold simultaneously at every nonempty
prefix. -/
theorem rational_erdosSum_prefix_saturation_sharp_order_lcm
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ)
    (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (q : ℚ)
    (hq : (∑' j, (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) = (q : ℝ))
    (k : ℕ) (hk : 0 < k) :
    ((b : ℝ) - 1) * ((b : ℝ) ^ (a k) - 1)
        < (b : ℝ) * (q.den : ℝ) *
          ((finiteErdosSum ((Finset.range k).image a) b).den : ℝ) ∧
      orderOf
          (ZMod.unitOfCoprime b
            (coprime_base_den_finiteErdosSum ((Finset.range k).image a) b
              (zero_not_mem_image_range_of_strictMono_pos a ha ha0 k) hb))
        = ((Finset.range k).image a).lcm id ∧
      (finiteErdosSum ((Finset.range k).image a) b).den ∣
        ((Finset.range k).image a).lcm (fun n => b ^ n - 1) := by
  have hF : ((Finset.range k).image a).Nonempty :=
    ⟨a 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, rfl⟩⟩
  have h0 := zero_not_mem_image_range_of_strictMono_pos a ha ha0 k
  exact ⟨
    rational_erdosSum_prefix_denominator_saturation_sharp
      b hb a ha ha0 q hq k,
    finite_period_noncollapse_rat_den
      ((Finset.range k).image a) b hF h0 hb,
    den_finiteErdosSum_dvd_termDenominatorLcm
      ((Finset.range k).image a) b h0 hb⟩

/-- **Exact reduced-denominator subsequence criterion.**  Let `Qₖ` be the
actual reduced denominator of the finite support sum through any selected
prefix `κ k`.  If `Qₖ · b ^ (-a (κ k))` tends to zero, then the infinite
Erdős support sum is irrational.

This is strictly more flexible than the exponent-lcm criterion below: it uses
`Rat.den` itself rather than an upper common denominator, and it only needs a
successful subsequence of prefixes rather than a full-sequence gap law. -/
theorem irrational_erdosSum_of_reducedDenominator_subsequence_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (κ : ℕ → ℕ)
    (hgap : Tendsto
      (fun k =>
        ((finiteErdosSum ((Finset.range (κ k)).image a) b).den : ℝ) *
          ((1 : ℝ) / b) ^ (a (κ k)))
      atTop (nhds 0)) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := by
  have hsum : Summable (fun j => (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) :=
    summable_erdos_term b hb a ha ha0
  set x : ℝ := ∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1) with hx
  set u : ℕ → ℚ :=
    fun k => finiteErdosSum ((Finset.range (κ k)).image a) b with hu
  have hval : ∀ k, x - ((u k : ℚ) : ℝ)
      = ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + κ k)) - 1) := by
    intro k
    have hsplit := hsum.sum_add_tsum_nat_add (κ k)
    have hcast := finiteErdosSum_image_range_cast b a ha (κ k)
    have huk : ((u k : ℚ) : ℝ)
        = ∑ i ∈ Finset.range (κ k), (1 : ℝ) / ((b : ℝ) ^ (a i) - 1) := by
      rw [hu]
      exact hcast
    rw [huk]
    linarith
  have hne : ∀ k, ((u k : ℚ) : ℝ) ≠ x := by
    intro k hEq
    have h1 := hval k
    rw [hEq] at h1
    have h2 := erdos_tail_pos b hb a ha ha0 (κ k)
    simp only [sub_self] at h1
    linarith
  apply irrational_of_den_mul_abs_sub_tendsto_zero
    (Filter.Eventually.of_forall hne)
  have hlim : Tendsto
      (fun k =>
        4 * (((u k).den : ℝ) * ((1 : ℝ) / b) ^ (a (κ k))))
      atTop (nhds 0) := by
    have hgap' : Tendsto
        (fun k => ((u k).den : ℝ) * ((1 : ℝ) / b) ^ (a (κ k)))
        atTop (nhds 0) := by
      simpa [hu] using hgap
    simpa using hgap'.const_mul (4 : ℝ)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun k =>
      mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    (Filter.Eventually.of_forall fun k => ?_) hlim
  have htail_pos := erdos_tail_pos b hb a ha ha0 (κ k)
  have htail_le := erdos_tail_le b hb a ha ha0 (κ k)
  have habs : |x - ((u k : ℚ) : ℝ)|
      = ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + κ k)) - 1) := by
    rw [hval k]
    exact abs_of_pos htail_pos
  calc
    ((u k).den : ℝ) * |x - ((u k : ℚ) : ℝ)|
        = ((u k).den : ℝ) *
            ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + κ k)) - 1) := by
              rw [habs]
    _ ≤ ((u k).den : ℝ) * (4 * ((1 : ℝ) / b) ^ (a (κ k))) := by
          exact mul_le_mul_of_nonneg_left htail_le (Nat.cast_nonneg _)
    _ = 4 * (((u k).den : ℝ) * ((1 : ℝ) / b) ^ (a (κ k))) := by ring

/-- **Mersenne-term-lcm subsequence criterion.**  The reduced denominator
criterion follows already when the lcm of the *displayed term denominators*
`b ^ a(i) - 1` has sufficiently small product with the next geometric scale
along any sequence of prefixes.  This is sharper than replacing that lcm by
the larger common denominator `b ^ lcm(a(i)) - 1`. -/
theorem irrational_erdosSum_of_termDenominatorLcm_subsequence_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (κ : ℕ → ℕ)
    (hgap : Tendsto
      (fun k =>
        ((((Finset.range (κ k)).image a).lcm (fun n => b ^ n - 1) : Nat) : ℝ) *
          ((1 : ℝ) / b) ^ (a (κ k)))
      atTop (nhds 0)) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := by
  apply irrational_erdosSum_of_reducedDenominator_subsequence_gap
    b hb a ha ha0 κ
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun k =>
      mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (Filter.Eventually.of_forall fun k => ?_) hgap
  have h0F : 0 ∉ (Finset.range (κ k)).image a := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    have hai : 1 ≤ a i := le_trans ha0 (ha.monotone (Nat.zero_le i))
    omega
  have hL_ne :
      ((Finset.range (κ k)).image a).lcm (fun n => b ^ n - 1) ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨n, hn, hzero⟩
    have hn0 : n ≠ 0 := fun hnEq => h0F (hnEq ▸ hn)
    have hpos := pow_sub_one_pos_of_ne_zero b n hb hn0
    omega
  have hdvd := den_finiteErdosSum_dvd_termDenominatorLcm
    ((Finset.range (κ k)).image a) b h0F hb
  have hden_le :
      ((finiteErdosSum ((Finset.range (κ k)).image a) b).den : ℝ) ≤
        ((((Finset.range (κ k)).image a).lcm
          (fun n => b ^ n - 1) : Nat) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hL_ne) hdvd
  exact mul_le_mul_of_nonneg_right hden_le (by positivity)

/-- Full-sequence wrapper for
`irrational_erdosSum_of_reducedDenominator_subsequence_gap`. -/
theorem irrational_erdosSum_of_reducedDenominator_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (hgap : Tendsto
      (fun k =>
        ((finiteErdosSum ((Finset.range k).image a) b).den : ℝ) *
          ((1 : ℝ) / b) ^ (a k))
      atTop (nhds 0)) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := by
  simpa using
    irrational_erdosSum_of_reducedDenominator_subsequence_gap
      b hb a ha ha0 id hgap

/-- **Infinite bridge, class form.**  For every base `b ≥ 2` and every
strictly monotone support `a` with `a 0 ≥ 1`, if the gap between `a k` and
`lcm {a 0, …, a (k-1)}` tends to infinity, then the infinite series
`∑ 1 / (b ^ (a k) - 1)` is irrational.  The reduced denominators of the
partial sums — the objects the finite kernel theorems audit — are the `q`
of the Dirichlet gap argument. -/
theorem irrational_erdosSum_of_lcm_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (hgap : Tendsto (fun k => a k - ((Finset.range k).image a).lcm id)
      atTop atTop) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hsum : Summable (fun j => (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) :=
    summable_erdos_term b hb a ha ha0
  set x : ℝ := ∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1) with hx
  set u : ℕ → ℚ := fun k => finiteErdosSum ((Finset.range k).image a) b with hu
  have hval : ∀ k, x - ((u k : ℚ) : ℝ)
      = ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := by
    intro k
    have hsplit := hsum.sum_add_tsum_nat_add k
    have hcast := finiteErdosSum_image_range_cast b a ha k
    have huk : ((u k : ℚ) : ℝ)
        = ∑ i ∈ Finset.range k, (1 : ℝ) / ((b : ℝ) ^ (a i) - 1) := by
      rw [hu]; exact hcast
    rw [huk]
    linarith
  have hne : ∀ k, ((u k : ℚ) : ℝ) ≠ x := by
    intro k hEq
    have h1 := hval k
    rw [hEq] at h1
    have h2 := erdos_tail_pos b hb a ha ha0 k
    simp only [sub_self] at h1
    linarith
  apply irrational_of_den_mul_abs_sub_tendsto_zero
    (Filter.Eventually.of_forall hne)
  have hrb0 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hrb1 : (1 : ℝ) / (b : ℝ) < 1 := by
    rw [div_lt_one hb_pos]; linarith
  have hlim : Tendsto
      (fun k => 4 * ((1 : ℝ) / b) ^ (a k - ((Finset.range k).image a).lcm id))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ((1 : ℝ) / b) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hrb0 hrb1
    have h2 : Tendsto
        (fun k => ((1 : ℝ) / b) ^ (a k - ((Finset.range k).image a).lcm id))
        atTop (nhds 0) := h1.comp hgap
    simpa using h2.const_mul (4 : ℝ)
  apply squeeze_zero' (Filter.Eventually.of_forall fun k =>
    mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) ?_ hlim
  filter_upwards [hgap.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with k hgap1 hk1
  have h0F : 0 ∉ (Finset.range k).image a := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    have : 1 ≤ a i := le_trans ha0 (ha.monotone (Nat.zero_le i))
    omega
  have hL_ne : ((Finset.range k).image a).lcm id ≠ 0 :=
    lcm_ne_zero_of_zero_not_mem _ h0F
  have hLa : ((Finset.range k).image a).lcm id ≤ a k := by omega
  have hD_pos : 0 < b ^ (((Finset.range k).image a).lcm id) - 1 :=
    pow_sub_one_pos_of_ne_zero b _ hb hL_ne
  have hden_le : ((u k).den : ℝ)
      ≤ ((b ^ (((Finset.range k).image a).lcm id) - 1 : ℕ) : ℝ) := by
    have hdvd := den_finiteErdosSum_dvd ((Finset.range k).image a) b h0F hb
    exact_mod_cast Nat.le_of_dvd hD_pos hdvd
  have htail_pos := erdos_tail_pos b hb a ha ha0 k
  have htail_le := erdos_tail_le b hb a ha ha0 k
  have habs : |x - ((u k : ℚ) : ℝ)|
      = ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := by
    rw [hval k]
    exact abs_of_pos htail_pos
  have hcastD : ((b ^ (((Finset.range k).image a).lcm id) - 1 : ℕ) : ℝ)
      ≤ (b : ℝ) ^ (((Finset.range k).image a).lcm id) := by
    have h1 : (b ^ (((Finset.range k).image a).lcm id) - 1 : ℕ)
        ≤ b ^ (((Finset.range k).image a).lcm id) := Nat.sub_le _ _
    calc ((b ^ (((Finset.range k).image a).lcm id) - 1 : ℕ) : ℝ)
        ≤ ((b ^ (((Finset.range k).image a).lcm id) : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = (b : ℝ) ^ (((Finset.range k).image a).lcm id) := by push_cast; rfl
  have hpow_split : (b : ℝ) ^ (((Finset.range k).image a).lcm id)
      * ((1 : ℝ) / b) ^ (a k)
      = ((1 : ℝ) / b) ^ (a k - ((Finset.range k).image a).lcm id) := by
    have h1 : ((1 : ℝ) / b) ^ (a k)
        = ((1 : ℝ) / b) ^ (a k - ((Finset.range k).image a).lcm id)
          * ((1 : ℝ) / b) ^ (((Finset.range k).image a).lcm id) := by
      rw [← pow_add, Nat.sub_add_cancel hLa]
    rw [h1]
    have h2 : (b : ℝ) ^ (((Finset.range k).image a).lcm id)
        * (((1 : ℝ) / b) ^ (a k - ((Finset.range k).image a).lcm id)
          * ((1 : ℝ) / b) ^ (((Finset.range k).image a).lcm id))
        = ((1 : ℝ) / b) ^ (a k - ((Finset.range k).image a).lcm id)
          * ((b : ℝ) ^ (((Finset.range k).image a).lcm id)
            * ((1 : ℝ) / b) ^ (((Finset.range k).image a).lcm id)) := by ring
    rw [h2]
    have h3 : (b : ℝ) ^ (((Finset.range k).image a).lcm id)
        * ((1 : ℝ) / b) ^ (((Finset.range k).image a).lcm id)
        = ((b : ℝ) * (1 / b)) ^ (((Finset.range k).image a).lcm id) :=
      (mul_pow _ _ _).symm
    rw [h3, mul_one_div, div_self hb_pos.ne', one_pow, mul_one]
  have htail_nonneg : (0 : ℝ)
      ≤ ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := htail_pos.le
  calc ((u k).den : ℝ) * |x - ((u k : ℚ) : ℝ)|
      = ((u k).den : ℝ) * ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := by
        rw [habs]
    _ ≤ ((b ^ (((Finset.range k).image a).lcm id) - 1 : ℕ) : ℝ)
          * ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) :=
        mul_le_mul_of_nonneg_right hden_le htail_nonneg
    _ ≤ ((b ^ (((Finset.range k).image a).lcm id) - 1 : ℕ) : ℝ)
          * (4 * ((1 : ℝ) / b) ^ (a k)) := by
        apply mul_le_mul_of_nonneg_left htail_le
        positivity
    _ ≤ (b : ℝ) ^ (((Finset.range k).image a).lcm id)
          * (4 * ((1 : ℝ) / b) ^ (a k)) := by
        apply mul_le_mul_of_nonneg_right hcastD
        positivity
    _ = 4 * ((b : ℝ) ^ (((Finset.range k).image a).lcm id)
          * ((1 : ℝ) / b) ^ (a k)) := by ring
    _ = 4 * ((1 : ℝ) / b) ^ (a k - ((Finset.range k).image a).lcm id) := by
        rw [hpow_split]

/-- lcm of the factorial support prefix `{1!, …, k!}` is `k!`. -/
theorem lcm_image_factorial_succ (k : ℕ) (hk : 1 ≤ k) :
    ((Finset.range k).image (fun i => Nat.factorial (i + 1))).lcm id
      = Nat.factorial k := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    have hik : i + 1 ≤ k := Finset.mem_range.mp hi
    simpa using Nat.factorial_dvd_factorial hik
  · have hmem : Nat.factorial k
        ∈ (Finset.range k).image (fun i => Nat.factorial (i + 1)) := by
      apply Finset.mem_image.mpr
      exact ⟨k - 1, Finset.mem_range.mpr (by omega), by
        rw [Nat.sub_add_cancel hk]⟩
    simpa using Finset.dvd_lcm hmem

/-- lcm of the two-power support prefix `{2^0, …, 2^(k-1)}` is `2^(k-1)`. -/
theorem lcm_image_two_pow (k : ℕ) (hk : 1 ≤ k) :
    ((Finset.range k).image (fun i => 2 ^ i)).lcm id = 2 ^ (k - 1) := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    have hik : i < k := Finset.mem_range.mp hi
    simpa using pow_dvd_pow 2 (by omega : i ≤ k - 1)
  · have hmem : (2 : ℕ) ^ (k - 1)
        ∈ (Finset.range k).image (fun i => 2 ^ i) := by
      apply Finset.mem_image.mpr
      exact ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩
    simpa using Finset.dvd_lcm hmem

/-- **First infinite-support instance: factorial support.**  For every base
`b ≥ 2`, the infinite series `∑_{k≥0} 1 / (b ^ (k+1)! - 1)` is irrational.
Stated in pure Mathlib vocabulary.  The support `{n! : n ≥ 1}` is not
pairwise coprime (each factorial divides the next), so this instance is
outside the classical coprime-support family. -/
theorem irrational_erdosSum_factorial_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (Nat.factorial (k + 1)) - 1)) := by
  apply irrational_erdosSum_of_lcm_gap b hb (fun k => Nat.factorial (k + 1))
  · intro m n hmn
    exact (Nat.factorial_lt (Nat.succ_pos m)).mpr (Nat.succ_lt_succ hmn)
  · simp [Nat.factorial]
  · apply tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [lcm_image_factorial_succ k hk]
    have h1 : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k :=
      Nat.factorial_succ k
    have h2 : 1 ≤ Nat.factorial k := Nat.one_le_iff_ne_zero.mpr
      (Nat.factorial_ne_zero k)
    have h3 : k * 1 ≤ k * Nat.factorial k := Nat.mul_le_mul_left k h2
    have h4 : (k + 1) * Nat.factorial k
        = k * Nat.factorial k + Nat.factorial k := by ring
    simp only [id_eq]
    omega

/-- **First infinite-support instance: geometric support.**  For every base
`b ≥ 2`, the infinite series `∑_{k≥0} 1 / (b ^ (2^k) - 1)` is irrational.
The gap `2^k - lcm = 2^(k-1)` has bounded ratio to the lcm, so this
instance is *not* reachable by a Liouville-number shortcut; the
denominator-gap criterion handles it uniformly. -/
theorem irrational_erdosSum_two_pow_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (2 ^ k) - 1)) := by
  apply irrational_erdosSum_of_lcm_gap b hb (fun k => 2 ^ k)
  · intro m n hmn
    exact Nat.pow_lt_pow_right (by norm_num) hmn
  · simp
  · apply tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [lcm_image_two_pow k hk]
    have h1 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
      have hk1 : k - 1 + 1 = k := by omega
      calc (2 : ℕ) ^ k = 2 ^ (k - 1 + 1) := by rw [hk1]
        _ = 2 ^ (k - 1) * 2 := pow_succ 2 (k - 1)
        _ = 2 * 2 ^ (k - 1) := by ring
    have h2 : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
    simp only [id_eq]
    omega

/-- **Erdős #257 family, factorial instance at base 2.**  The literal series
`∑ 1 / (2^(n!) - 1)` over the infinite support `A = {n! : n ≥ 1}` is
irrational.  This is an instance of the statement family of Erdős
problem #257 (which asks the same for *every* infinite support); the
universal problem remains open and is not claimed. -/
theorem erdos257_family_factorial_instance :
    Irrational (∑' k, (1 : ℝ) / ((2 : ℝ) ^ (Nat.factorial (k + 1)) - 1)) :=
  irrational_erdosSum_factorial_support 2 le_rfl

/-- **Erdős #257 family, geometric instance at base 2.**  The literal series
`∑ 1 / (2^(2^n) - 1)` over the infinite support `A = {2^n : n ≥ 0}` is
irrational.  An instance of the #257 statement family; the universal
problem remains open and is not claimed. -/
theorem erdos257_family_two_pow_instance :
    Irrational (∑' k, (1 : ℝ) / ((2 : ℝ) ^ (2 ^ k) - 1)) :=
  irrational_erdosSum_two_pow_support 2 le_rfl

/-! ## Full-support lane: near-integer criterion and Lambert bridge

The lcm-gap criterion above provably cannot reach the full support
`a k = k + 1`: the closing theorem of this section,
`lcm_gap_hypothesis_fails_full_support`, machine-checks that the prefix lcm
of `{1, …, k}` outruns the next exponent `k + 1`, so the gap hypothesis
fails.  This section therefore opens the second route.
`irrational_of_int_mul_near_int` is the classical integer-dilation
near-integer irrationality criterion — the engine shape behind Erdős's 1948
digit/carry arguments.  `erdosSum_full_support_eq_tsum_divisor_count` is
the Lambert bridge identifying the full-support series `∑ 1 / (b^n - 1)`
with the divisor-count series `∑ τ(m) / b^m` (Mathlib's
`tsum_pow_div_one_sub_eq_tsum_sigma` at `k = 0`, `r = 1/b`), and
`irrational_erdosSum_full_support_of_near_int` reduces full-support
(Erdős–Borwein) irrationality to producing near-integer witnesses for the
divisor-count series — the exact obligation Erdős's 1948 congruence
construction discharges.  Those witnesses are not constructed here:
full-support irrationality is *not* claimed. -/

/-- **Second irrationality engine: integer-dilation near-integer criterion.**
If for every positive `q` some integer dilation `m * ξ` lies within `1 / q`
of an integer without being one, then `ξ` is irrational.  For rational
`ξ` with reduced denominator `d`, any `m * ξ` that is not an integer sits
at distance at least `1 / d` from every integer, so the witnesses force the
reduced denominator past every bound.  This is the classical criterion
shape behind digit/carry irrationality proofs (Erdős 1948). -/
theorem irrational_of_int_mul_near_int {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  rintro ⟨r, rfl⟩
  obtain ⟨m, z, hpos, hlt⟩ := h r.den r.den_pos
  have hden_pos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  set N : ℤ := m * r.num - z * (r.den : ℤ) with hN
  have hval : (m : ℝ) * (r : ℝ) - (z : ℝ) = (N : ℝ) / (r.den : ℝ) := by
    rw [hN, Rat.cast_def]
    push_cast
    field_simp
  have hN0 : N ≠ 0 := by
    intro h0
    rw [hval, h0] at hpos
    simp at hpos
  have h1 : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN0
  have hge : (1 : ℝ) / (r.den : ℝ) ≤ |(m : ℝ) * (r : ℝ) - (z : ℝ)| := by
    rw [hval, abs_div, abs_of_pos hden_pos]
    have h2 : (0 : ℝ) ≤ 1 / (r.den : ℝ) := by positivity
    calc (1 : ℝ) / (r.den : ℝ)
        = 1 * (1 / (r.den : ℝ)) := (one_mul _).symm
      _ ≤ |(N : ℝ)| * (1 / (r.den : ℝ)) := mul_le_mul_of_nonneg_right h1 h2
      _ = |(N : ℝ)| / (r.den : ℝ) := mul_one_div _ _
  exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)

/-- Base-power specialisation of the near-integer criterion: witnesses of
the form `b ^ n * ξ` suffice.  This is the interface a digit/carry
construction in base `b` feeds. -/
theorem irrational_of_pow_mul_near_int (b : ℕ) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  apply irrational_of_int_mul_near_int
  intro q hq
  obtain ⟨n, z, h1, h2⟩ := h q hq
  have hcast : (((b : ℤ) ^ n : ℤ) : ℝ) = (b : ℝ) ^ n := by push_cast; rfl
  exact ⟨(b : ℤ) ^ n, z, by rw [hcast]; exact h1, by rw [hcast]; exact h2⟩

/-- Summability of the divisor-count series `∑ τ(m+1) / b^(m+1)`:
`τ(n) ≤ n` and `∑ n · r^n` converges geometrically. -/
theorem summable_divisor_count_term (b : ℕ) (hb : 2 ≤ b) :
    Summable (fun m : ℕ => (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hr : ‖(1 : ℝ) / (b : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one hb_pos]
    linarith
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ 1 * ((1 : ℝ) / b) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hshift : Summable
      (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 1 * ((1 : ℝ) / b) ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr hgeo
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hshift
  have hτ : ((m + 1).divisors.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self (m + 1)
  have hpow : ((1 : ℝ) / b) ^ (m + 1) = 1 / (b : ℝ) ^ (m + 1) := by
    rw [div_pow, one_pow]
  calc (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1)
      = ((m + 1).divisors.card : ℝ) * (1 / (b : ℝ) ^ (m + 1)) :=
        (mul_one_div _ _).symm
    _ ≤ ((m + 1 : ℕ) : ℝ) * (1 / (b : ℝ) ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hτ (by positivity)
    _ = ((m + 1 : ℕ) : ℝ) ^ 1 * ((1 : ℝ) / b) ^ (m + 1) := by
        rw [pow_one, hpow]

/-- **Full-support Lambert bridge.**  For every base `b ≥ 2`, the
full-support series `∑_{n≥1} 1 / (b^n - 1)` equals the divisor-count
series `∑_{m≥1} τ(m) / b^m`.  This is the classical Lambert-series
identity (Mathlib's `tsum_pow_div_one_sub_eq_tsum_sigma` at `k = 0`,
`r = 1/b`), restated in the kernel's own series vocabulary: the left side
is the `a k = k + 1` (full-support) member of the Erdős #257 statement
family — the Erdős–Borwein shape. -/
theorem erdosSum_full_support_eq_tsum_divisor_count (b : ℕ) (hb : 2 ≤ b) :
    ∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)
      = ∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  have hr : ‖(1 : ℝ) / (b : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one hb_pos]
    linarith
  have hterm : ∀ n : ℕ, 0 < n →
      ((1 : ℝ) / b) ^ n / (1 - ((1 : ℝ) / b) ^ n) = 1 / ((b : ℝ) ^ n - 1) := by
    intro n hn
    have hbn : (1 : ℝ) < (b : ℝ) ^ n := one_lt_pow₀ hb1 (by omega)
    have hbn0 : (b : ℝ) ^ n ≠ 0 := by positivity
    have hbn1 : (b : ℝ) ^ n - 1 ≠ 0 := ne_of_gt (by linarith)
    have h1X : (1 : ℝ) - 1 / (b : ℝ) ^ n ≠ 0 := by
      have hEq : (1 : ℝ) - 1 / (b : ℝ) ^ n = ((b : ℝ) ^ n - 1) / (b : ℝ) ^ n := by
        field_simp
      rw [hEq]
      exact div_ne_zero hbn1 hbn0
    rw [div_pow, one_pow]
    field_simp
  have hlam := tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℝ) hr 0
  calc ∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)
      = ∑' n : ℕ+, (1 : ℝ) / ((b : ℝ) ^ (n : ℕ) - 1) :=
        (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (1 : ℝ) / ((b : ℝ) ^ n - 1))).symm
    _ = ∑' n : ℕ+, ((n : ℝ)) ^ 0 * ((1 : ℝ) / b) ^ (n : ℕ)
          / (1 - ((1 : ℝ) / b) ^ (n : ℕ)) := by
        refine tsum_congr fun n => ?_
        rw [pow_zero, one_mul, hterm (n : ℕ) n.pos]
    _ = ∑' n : ℕ+, ((ArithmeticFunction.sigma 0 (n : ℕ) : ℝ))
          * ((1 : ℝ) / b) ^ (n : ℕ) := hlam
    _ = ∑' m : ℕ, ((ArithmeticFunction.sigma 0 (m + 1) : ℝ))
          * ((1 : ℝ) / b) ^ (m + 1) :=
        tsum_pnat_eq_tsum_succ
          (f := fun n : ℕ => ((ArithmeticFunction.sigma 0 n : ℝ)) * ((1 : ℝ) / b) ^ n)
    _ = ∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1) := by
        refine tsum_congr fun m => ?_
        rw [ArithmeticFunction.sigma_zero_apply, div_pow, one_pow, mul_one_div]

/-- **Erdős–Borwein constant, Lambert form.**  The literal base-2
full-support series `∑_{n≥1} 1 / (2^n - 1)` — the Erdős–Borwein constant,
the `A = ℕ` member of the Erdős #257 statement family — equals the
divisor-count series `∑_{m≥1} τ(m) / 2^m`. -/
theorem erdosBorwein_constant_lambert_identity :
    ∑' k : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) - 1)
      = ∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (2 : ℝ) ^ (m + 1) := by
  have h := erdosSum_full_support_eq_tsum_divisor_count 2 le_rfl
  push_cast at h
  exact h

/-- **Reduction of full-support (Erdős–Borwein) irrationality to
near-integer witnesses.**  For every base `b ≥ 2`: if the divisor-count
series `∑ τ(m) / b^m` admits, for every `q`, a base-power dilation lying
within `1/q` of an integer without being one, then the full-support series
`∑_{n≥1} 1 / (b^n - 1)` is irrational.  The hypothesis is exactly the
obligation Erdős's 1948 congruence construction discharges; producing
those witnesses in Lean is the named remaining step of the full-support
lane, and is *not* claimed here. -/
theorem irrational_erdosSum_full_support_of_near_int (b : ℕ) (hb : 2 ≤ b)
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b : ℝ) ^ n
            * (∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)| ∧
        |(b : ℝ) ^ n
            * (∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := by
  rw [erdosSum_full_support_eq_tsum_divisor_count b hb]
  exact irrational_of_pow_mul_near_int b h

/-- **Machine-checked boundary: the lcm-gap criterion cannot fire on full
support.**  For the full support `a k = k + 1`, the prefix lcm
`lcm {1, …, k}` contains the coprime pair `k - 1, k`, hence is at least
`(k - 1) * k ≥ k + 2` for `k ≥ 3` — so the (truncated) gap
`(k + 1) - lcm {1, …, k}` is eventually `0` and does not tend to infinity.
The hypothesis of `irrational_erdosSum_of_lcm_gap` therefore fails at full
support: reaching the Erdős–Borwein case needs a different engine, which is
what the near-integer criterion above provides the interface for. -/
theorem lcm_gap_hypothesis_fails_full_support :
    ¬ Tendsto (fun k => (k + 1) - ((Finset.range k).image (fun i => i + 1)).lcm id)
        atTop atTop := by
  intro hT
  have h1 := hT.eventually_ge_atTop 1
  have h0 : ∀ᶠ k in atTop,
      (k + 1) - ((Finset.range k).image (fun i => i + 1)).lcm id = 0 := by
    filter_upwards [eventually_ge_atTop 3] with k hk
    have hmem1 : k - 1 ∈ (Finset.range k).image (fun i => i + 1) :=
      Finset.mem_image.mpr ⟨k - 2, Finset.mem_range.mpr (by omega), by omega⟩
    have hmem2 : k ∈ (Finset.range k).image (fun i => i + 1) :=
      Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
    have hd1 : (k - 1) ∣ ((Finset.range k).image (fun i => i + 1)).lcm id := by
      simpa using Finset.dvd_lcm hmem1
    have hd2 : k ∣ ((Finset.range k).image (fun i => i + 1)).lcm id := by
      simpa using Finset.dvd_lcm hmem2
    have hco : Nat.Coprime (k - 1) k := by
      have hk1 : k - 1 + 1 = k := by omega
      have hmod : k % (k - 1) = 1 := by
        calc k % (k - 1)
            = ((k - 1) + 1) % (k - 1) := by rw [hk1]
          _ = 1 % (k - 1) := Nat.add_mod_left _ _
          _ = 1 := Nat.mod_eq_of_lt (by omega)
      have hgcd : Nat.gcd (k - 1) k = 1 := by
        rw [Nat.gcd_rec, hmod]
        exact Nat.gcd_one_left _
      exact hgcd
    have hmul : (k - 1) * k ∣ ((Finset.range k).image (fun i => i + 1)).lcm id :=
      hco.mul_dvd_of_dvd_of_dvd hd1 hd2
    have h0F : 0 ∉ (Finset.range k).image (fun i => i + 1) := by
      intro hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      omega
    have hlcm_pos : 0 < ((Finset.range k).image (fun i => i + 1)).lcm id :=
      Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem _ h0F)
    have hle : (k - 1) * k ≤ ((Finset.range k).image (fun i => i + 1)).lcm id :=
      Nat.le_of_dvd hlcm_pos hmul
    have h2k : 2 * k ≤ (k - 1) * k :=
      Nat.mul_le_mul_right k (by omega : 2 ≤ k - 1)
    omega
  obtain ⟨k, hk1, hk0⟩ := (h1.and h0).exists
  omega

/-! ## Full-support lane: divisor block certificates

The reduction `irrational_erdosSum_full_support_of_near_int` (above) leaves a
single named obligation: near-integer witnesses for the divisor-count series.
This section factors that obligation into *finite block certificates*.  A
certificate for precision `q` is a tuple `(N, K, L, B)` of naturals with three
finite conditions: a first block `b ^ r ∣ τ (N + r)` for `1 ≤ r ≤ K` (which
makes the leading shifted-tail terms integral), a middle window
`τ (N + r) ≤ B` for `K < r ≤ L`, and one ℕ-arithmetic inequality
`q * (B * b ^ (L - K) + (N + L + 2)) < b ^ L` absorbing the geometric middle
bound and the crude `τ(n) ≤ n` far tail.
`near_int_witness_of_divisor_block_certificate` consumes a certificate and
produces the near-integer witness; `irrational_erdosSum_full_support_of_block_certificates`
closes the loop: certificates for every `q` give full-support irrationality.
`bpow_dvd_card_divisors_of_exact_prime_block` is the multiplicativity hinge
showing the first-block condition is reachable by prescribing exact prime
valuations (Erdős's 1948 congruence construction).  Producing certificates for
every `q` — Erdős's construction itself — is NOT claimed here. -/

/-- Summability of the shifted divisor-count tail
`∑_r τ(N+r+1) / b^(r+1)`: the `b^N`-dilated remainder series of the
divisor-count series past index `N`. -/
theorem summable_divisor_count_shift_tail (b N : ℕ) (hb : 2 ≤ b) :
    Summable (fun r : ℕ => (((N + r + 1).divisors.card : ℝ)) / (b : ℝ) ^ (r + 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hbase := summable_divisor_count_term b hb
  have hshift : Summable
      (fun r : ℕ => (((r + N + 1).divisors.card : ℝ)) / (b : ℝ) ^ (r + N + 1)) :=
    (summable_nat_add_iff N).mpr hbase
  have hmul := hshift.mul_left ((b : ℝ) ^ N)
  refine hmul.congr fun r => ?_
  rw [show r + N + 1 = N + r + 1 from by omega]
  have hsplit : (b : ℝ) ^ (N + r + 1) = (b : ℝ) ^ N * (b : ℝ) ^ (r + 1) := by ring
  rw [hsplit]
  field_simp

/-- **Shifted-tail decomposition.**  Dilating the divisor-count series by
`b^N` splits it into an integer (the first `N` terms clear their
denominators) plus the shifted tail `∑_r τ(N+r+1) / b^(r+1)`.  This is the
base-`b` carry skeleton behind Erdős's 1948 argument. -/
theorem bpow_mul_divisor_count_series_eq_int_add_tail (b N : ℕ) (hb : 2 ≤ b) :
    ∃ z : ℤ,
      (b : ℝ) ^ N * (∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1)) =
        (z : ℝ) + ∑' r : ℕ, (((N + r + 1).divisors.card : ℝ)) / (b : ℝ) ^ (r + 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hsum := summable_divisor_count_term b hb
  refine ⟨((∑ i ∈ Finset.range N, (i + 1).divisors.card * b ^ (N - (i + 1)) : ℕ) : ℤ), ?_⟩
  rw [← Summable.sum_add_tsum_nat_add N hsum, mul_add]
  congr 1
  · push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiN : i < N := Finset.mem_range.mp hi
    have hsplit : (b : ℝ) ^ N = (b : ℝ) ^ (N - (i + 1)) * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    field_simp
  · rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [show r + N + 1 = N + r + 1 from by omega]
    have hsplit : (b : ℝ) ^ (N + r + 1) = (b : ℝ) ^ N * (b : ℝ) ^ (r + 1) := by ring
    rw [hsplit]
    field_simp

/-- Summability of `(C + t) · x^t` for `0 ≤ x < 1`: a constant plus linear
coefficient against a geometric envelope. -/
theorem summable_const_add_mul_geometric (C : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun t : ℕ => ((C : ℝ) + (t : ℝ)) * x ^ t) := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  have h1 : Summable (fun t : ℕ => (C : ℝ) * x ^ t) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left _
  have h2 : Summable (fun t : ℕ => (t : ℝ) * x ^ t) := by
    refine (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).congr fun t => ?_
    rw [pow_one]
  refine (h1.add h2).congr fun t => ?_
  ring

/-- Geometric envelope bound: for `0 ≤ x ≤ 1/2`,
`∑_t (C + t) · x^t ≤ 2C + 2` (equality at `x = 1/2`).  The closed forms are
`C/(1-x)` and `x/(1-x)^2`, each at most `2C` and `2` on this range. -/
theorem tsum_const_add_mul_geometric_le (C : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 1 / 2) :
    ∑' t : ℕ, ((C : ℝ) + (t : ℝ)) * x ^ t ≤ 2 * (C : ℝ) + 2 := by
  have hx1 : x < 1 := by linarith
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  have hx1' : (0 : ℝ) < 1 - x := by linarith
  have h1 : Summable (fun t : ℕ => (C : ℝ) * x ^ t) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left _
  have h2 : Summable (fun t : ℕ => (t : ℝ) * x ^ t) := by
    refine (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).congr fun t => ?_
    rw [pow_one]
  have hsplit : (∑' t : ℕ, ((C : ℝ) + (t : ℝ)) * x ^ t)
      = (∑' t : ℕ, (C : ℝ) * x ^ t) + ∑' t : ℕ, (t : ℝ) * x ^ t := by
    rw [← h1.tsum_add h2]
    exact tsum_congr fun t => by ring
  rw [hsplit, tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1,
    tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  have hinv : (1 - x)⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hx1']
    linarith
  have hfrac : x / (1 - x) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * x) (by linarith : (0 : ℝ) ≤ 2 - x)]
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  nlinarith [mul_le_mul_of_nonneg_left hinv hC0]

/-- **Crude far-tail bound.**  Past index `L`, bounding `τ(n) ≤ n` and
summing the linear-times-geometric envelope gives
`∑_t τ(N+L+1+t) / b^(L+1+t) ≤ (N+L+2) / b^L` for every base `b ≥ 2`.  This
is the certificate's third window: it needs no divisor information at all. -/
theorem divisor_count_far_tail_le (b N L : ℕ) (hb : 2 ≤ b) :
    ∑' t : ℕ, (((N + L + 1 + t).divisors.card : ℝ)) / (b : ℝ) ^ (L + 1 + t)
      ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hx0 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hx1 : 1 / (b : ℝ) < 1 := by
    rw [div_lt_one hb_pos]
    linarith
  have hx2 : 1 / (b : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · exact hb2
  -- summability of the far series, from the shift-tail lemma at `N + L`
  have hshift := summable_divisor_count_shift_tail b (N + L) hb
  have hLHS_sum : Summable
      (fun t : ℕ => (((N + L + 1 + t).divisors.card : ℝ)) / (b : ℝ) ^ (L + 1 + t)) := by
    have hmul := hshift.mul_left ((1 : ℝ) / (b : ℝ) ^ L)
    refine hmul.congr fun t => ?_
    rw [show N + L + t + 1 = N + L + 1 + t from by omega]
    have hsplit : (b : ℝ) ^ (L + 1 + t) = (b : ℝ) ^ L * (b : ℝ) ^ (t + 1) := by ring
    rw [hsplit]
    field_simp
  -- comparison series
  have hcmp_sum : Summable
      (fun t : ℕ => ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
        (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t) := by
    have := (summable_const_add_mul_geometric (N + L + 1) hx0 hx1).mul_left
      ((1 : ℝ) / (b : ℝ) ^ (L + 1))
    refine this.congr fun t => ?_
    ring
  have hle : ∀ t : ℕ, (((N + L + 1 + t).divisors.card : ℝ)) / (b : ℝ) ^ (L + 1 + t)
      ≤ ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
        (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t := by
    intro t
    have hτ : (((N + L + 1 + t).divisors.card : ℝ)) ≤ ((N + L + 1 + t : ℕ) : ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self (N + L + 1 + t)
    have hpow : (b : ℝ) ^ (L + 1 + t) = (b : ℝ) ^ (L + 1) * (b : ℝ) ^ t := by ring
    calc (((N + L + 1 + t).divisors.card : ℝ)) / (b : ℝ) ^ (L + 1 + t)
        ≤ ((N + L + 1 + t : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + t) := by gcongr
      _ = ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
            (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t := by
          rw [hpow]
          push_cast
          rw [div_pow, one_pow]
          field_simp
  calc (∑' t : ℕ, (((N + L + 1 + t).divisors.card : ℝ)) / (b : ℝ) ^ (L + 1 + t))
      ≤ ∑' t : ℕ, ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
          (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t :=
        Summable.tsum_le_tsum hle hLHS_sum hcmp_sum
    _ = ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
          ∑' t : ℕ, (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t := by
        rw [← tsum_mul_left]
        exact tsum_congr fun t => by ring
    _ ≤ ((1 : ℝ) / (b : ℝ) ^ (L + 1)) * (2 * ((N + L + 1 : ℕ) : ℝ) + 2) := by
        apply mul_le_mul_of_nonneg_left
          (tsum_const_add_mul_geometric_le (N + L + 1) hx0 hx2) (by positivity)
    _ ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
        have hP : (0 : ℝ) < (b : ℝ) ^ L := by positivity
        have hS : (0 : ℝ) ≤ (N : ℝ) + (L : ℝ) + 2 := by positivity
        push_cast
        rw [pow_succ, one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) hP]
        nlinarith [mul_nonneg (mul_nonneg hS hP.le) (by linarith : (0 : ℝ) ≤ (b : ℝ) - 2)]

/-- **Multiplicativity hinge for the first block.**  If `P` is a set of
primes at which `n` has exact valuation `b - 1`, then `b ^ |P|` divides
`τ(n)`: each such prime contributes a factor `b` to
`τ(n) = ∏_p (v_p(n) + 1)`.  This is how Erdős's 1948 congruence construction
forces the first-block divisibility — many small exact valuations, never one
huge one. -/
theorem bpow_dvd_card_divisors_of_exact_prime_block (b n : ℕ) (hb : 2 ≤ b) (hn : n ≠ 0)
    (P : Finset ℕ) (hexact : ∀ p ∈ P, n.factorization p = b - 1) :
    b ^ P.card ∣ n.divisors.card := by
  have hsub : P ⊆ n.primeFactors := by
    intro p hp
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, hexact p hp]
    omega
  have h1 : ∀ p ∈ P, n.factorization p + 1 = b := by
    intro p hp
    rw [hexact p hp]
    omega
  have hval : ∏ p ∈ P, (n.factorization p + 1) = b ^ P.card := by
    rw [Finset.prod_congr rfl h1, Finset.prod_const]
  rw [Nat.card_divisors hn, ← hval]
  exact Finset.prod_dvd_prod_of_subset P n.primeFactors _ hsub

/-- **Certificate consumer.**  A divisor block certificate `(N, K, L, B)` for
precision `q` — first-block divisibility, middle window bounded by `B`, and
the ℕ-arithmetic inequality — yields a near-integer witness for the
`b^N`-dilated divisor-count series: the first block lands in ℤ, the middle
window contributes at most `B / b^K`, the far tail at most `(N+L+2) / b^L`,
and the remainder is strictly positive because every divisor count is. -/
theorem near_int_witness_of_divisor_block_certificate
    (b q N K L B : ℕ) (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (hblock : ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ (N + r).divisors.card)
    (hmiddle : ∀ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card ≤ B)
    (harith : q * (B * b ^ (L - K) + (N + L + 2)) < b ^ L) :
    ∃ z : ℤ,
      0 < |(b : ℝ) ^ N * (∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)| ∧
        |(b : ℝ) ^ N * (∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)| < 1 / (q : ℝ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨z₀, hz₀⟩ := bpow_mul_divisor_count_series_eq_int_add_tail b N hb
  have hfsum : Summable
      (fun r : ℕ => (((N + r + 1).divisors.card : ℝ)) / (b : ℝ) ^ (r + 1)) :=
    summable_divisor_count_shift_tail b N hb
  have hfarsum : Summable
      (fun t : ℕ => (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) :=
    (summable_nat_add_iff L).mpr hfsum
  -- split the tail at L
  have hsplitL : (∑' r : ℕ, (((N + r + 1).divisors.card : ℝ)) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  -- split the finite part at K
  have hsplitK : (∑ i ∈ Finset.range L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  -- the first block is an integer
  set z₁ : ℕ := ∑ i ∈ Finset.range K, (N + i + 1).divisors.card / b ^ (i + 1) with hz₁def
  have hz₁ : ((z₁ : ℕ) : ℝ)
      = ∑ i ∈ Finset.range K, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [hz₁def]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp hi
    have hdvd : b ^ (i + 1) ∣ (N + i + 1).divisors.card :=
      hblock (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hbpow0 : ((b ^ (i + 1) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_div hdvd hbpow0]
    push_cast
    ring
  -- the remainder and its bounds
  have hmid_nonneg : (0 : ℝ)
      ≤ ∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hfar_pos : (0 : ℝ)
      < ∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    have hne : N + (0 + L) + 1 ≠ 0 := by omega
    have hτpos : 0 < (N + (0 + L) + 1).divisors.card :=
      Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hne)
    have hterm0 : (0 : ℝ)
        < (((N + (0 + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((0 + L) + 1) := by
      have hc : (0 : ℝ) < (((N + (0 + L) + 1).divisors.card : ℝ)) := by exact_mod_cast hτpos
      positivity
    calc (0 : ℝ) < (((N + (0 + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((0 + L) + 1) := hterm0
      _ ≤ _ := hfarsum.le_tsum 0 fun j _ => by positivity
  -- middle window bound
  have hgeo_sum : Summable (fun j : ℕ => ((1 : ℝ) / (b : ℝ)) ^ j) :=
    summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one hb_pos]; linarith)
  have hmid : (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
      ≤ (B : ℝ) / (b : ℝ) ^ K := by
    have h1 : ∀ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1)
        ≤ (B : ℝ) * ((1 : ℝ) / (b : ℝ)) ^ (i + 1) := by
      intro i hi
      obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
      have hτB : (((N + i + 1).divisors.card : ℝ)) ≤ (B : ℝ) := by
        exact_mod_cast hmiddle (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [div_pow, one_pow, mul_one_div]
      gcongr
    have h3 : (∑ i ∈ Finset.Ico K L, ((1 : ℝ) / (b : ℝ)) ^ (i + 1))
        = ∑ j ∈ Finset.range (L - K), ((1 : ℝ) / (b : ℝ)) ^ (K + j + 1) :=
      Finset.sum_Ico_eq_sum_range (fun i => ((1 : ℝ) / (b : ℝ)) ^ (i + 1)) K L
    have h4 : (∑ j ∈ Finset.range (L - K), ((1 : ℝ) / (b : ℝ)) ^ (K + j + 1))
        = ((1 : ℝ) / (b : ℝ)) ^ (K + 1) * ∑ j ∈ Finset.range (L - K), ((1 : ℝ) / (b : ℝ)) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_add]
      congr 1
      omega
    have h5 : (∑ j ∈ Finset.range (L - K), ((1 : ℝ) / (b : ℝ)) ^ j)
        ≤ ∑' j : ℕ, ((1 : ℝ) / (b : ℝ)) ^ j :=
      Summable.sum_le_tsum _ (fun j _ => by positivity) hgeo_sum
    have h6 : (∑' j : ℕ, ((1 : ℝ) / (b : ℝ)) ^ j) ≤ 2 := by
      rw [tsum_geometric_of_lt_one (by positivity) (by rw [div_lt_one hb_pos]; linarith)]
      have hhalf : (0 : ℝ) < 1 - 1 / (b : ℝ) := by
        rw [sub_pos, div_lt_one hb_pos]
        linarith
      rw [← one_div, div_le_iff₀ hhalf]
      have : 1 / (b : ℝ) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le
        · norm_num
        · exact hb2
      linarith
    have h7 : (2 : ℝ) * ((1 : ℝ) / (b : ℝ)) ^ (K + 1) ≤ ((1 : ℝ) / (b : ℝ)) ^ K := by
      rw [pow_succ]
      have hxK : (0 : ℝ) ≤ ((1 : ℝ) / (b : ℝ)) ^ K := by positivity
      have h2x : (2 : ℝ) * ((1 : ℝ) / (b : ℝ)) ≤ 1 := by
        rw [mul_one_div, div_le_one hb_pos]
        linarith
      calc (2 : ℝ) * (((1 : ℝ) / (b : ℝ)) ^ K * ((1 : ℝ) / (b : ℝ)))
          = ((1 : ℝ) / (b : ℝ)) ^ K * (2 * ((1 : ℝ) / (b : ℝ))) := by ring
        _ ≤ ((1 : ℝ) / (b : ℝ)) ^ K * 1 := mul_le_mul_of_nonneg_left h2x hxK
        _ = ((1 : ℝ) / (b : ℝ)) ^ K := mul_one _
    have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
    calc (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        ≤ ∑ i ∈ Finset.Ico K L, (B : ℝ) * ((1 : ℝ) / (b : ℝ)) ^ (i + 1) :=
          Finset.sum_le_sum h1
      _ = (B : ℝ) * ∑ i ∈ Finset.Ico K L, ((1 : ℝ) / (b : ℝ)) ^ (i + 1) := by
          rw [Finset.mul_sum]
      _ = (B : ℝ) * (((1 : ℝ) / (b : ℝ)) ^ (K + 1)
            * ∑ j ∈ Finset.range (L - K), ((1 : ℝ) / (b : ℝ)) ^ j) := by rw [h3, h4]
      _ ≤ (B : ℝ) * (((1 : ℝ) / (b : ℝ)) ^ (K + 1) * 2) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          apply mul_le_mul_of_nonneg_left (le_trans h5 h6) (by positivity)
      _ = (B : ℝ) * (2 * ((1 : ℝ) / (b : ℝ)) ^ (K + 1)) := by ring
      _ ≤ (B : ℝ) * ((1 : ℝ) / (b : ℝ)) ^ K := mul_le_mul_of_nonneg_left h7 hB0
      _ = (B : ℝ) / (b : ℝ) ^ K := by
          rw [div_pow, one_pow, mul_one_div]
  -- far tail bound, reshaped from the far-tail lemma
  have hfar_eq : (∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, (((N + L + 1 + t).divisors.card : ℝ)) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar : (∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact divisor_count_far_tail_le b N L hb
  -- assemble the witness
  refine ⟨z₀ + (z₁ : ℤ), ?_⟩
  have habs : (b : ℝ) ^ N * (∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1))
      - ((z₀ + (z₁ : ℤ) : ℤ) : ℝ)
      = (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    rw [hz₀, hsplitL, hsplitK]
    push_cast
    rw [← hz₁]
    ring
  have hR_pos : (0 : ℝ)
      < (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    add_pos_of_nonneg_of_pos hmid_nonneg hfar_pos
  constructor
  · rw [habs]
    exact abs_pos.mpr (ne_of_gt hR_pos)
  · rw [habs, abs_of_pos hR_pos]
    have hsum_le : (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + (∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
        ≤ (B : ℝ) / (b : ℝ) ^ K + ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L :=
      add_le_add hmid hfar
    refine lt_of_le_of_lt hsum_le ?_
    have hbK : ((b : ℝ) ^ K) ≠ 0 := by positivity
    have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    have hpowsplit : (b : ℝ) ^ L = (b : ℝ) ^ K * (b : ℝ) ^ (L - K) := by
      rw [← pow_add]
      congr 1
      omega
    have h1 : (B : ℝ) / (b : ℝ) ^ K = (B : ℝ) * (b : ℝ) ^ (L - K) / (b : ℝ) ^ L := by
      rw [hpowsplit]
      field_simp
    have hc : (q : ℝ) * ((B : ℝ) * (b : ℝ) ^ (L - K) + ((N + L + 2 : ℕ) : ℝ)) < (b : ℝ) ^ L := by
      exact_mod_cast harith
    rw [h1, ← add_div, div_lt_div_iff₀ hbL hq', one_mul]
    calc ((B : ℝ) * (b : ℝ) ^ (L - K) + ((N + L + 2 : ℕ) : ℝ)) * (q : ℝ)
        = (q : ℝ) * ((B : ℝ) * (b : ℝ) ^ (L - K) + ((N + L + 2 : ℕ) : ℝ)) := mul_comm _ _
      _ < (b : ℝ) ^ L := hc

/-- **Full-support (Erdős–Borwein) irrationality from block certificates.**
If for every precision `q` some divisor block certificate `(N, K, L, B)`
exists, then the full-support series `∑_{n≥1} 1 / (b^n - 1)` is irrational.
This composes the certificate consumer with the landed near-integer
reduction: the remaining open obligation of the full-support lane is now the
purely finite arithmetic statement that certificates exist for every `q` —
which is what Erdős's 1948 congruence construction produces, and is NOT
claimed here. -/
theorem irrational_erdosSum_full_support_of_block_certificates
    (b : ℕ) (hb : 2 ≤ b)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L B : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ (N + r).divisors.card) ∧
        (∀ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card ≤ B) ∧
        q * (B * b ^ (L - K) + (N + L + 2)) < b ^ L) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := by
  refine irrational_erdosSum_full_support_of_near_int b hb fun q hq => ?_
  obtain ⟨N, K, L, B, hKL, hblock, hmiddle, harith⟩ := hcert q hq
  obtain ⟨z, hz⟩ :=
    near_int_witness_of_divisor_block_certificate b q N K L B hb hq hKL hblock hmiddle harith
  exact ⟨N, z, hz⟩

/-! ## Full-support lane: weighted divisor block certificates -/

theorem geom_sum_range_le_pow (b m : ℕ) (hb : 2 ≤ b) :
    ∑ j ∈ Finset.range m, b ^ j ≤ b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have h2 : b ^ m * 2 ≤ b ^ m * b := Nat.mul_le_mul (le_refl _) hb
      have hp : b ^ (m + 1) = b ^ m * b := pow_succ b m
      omega

/-- **Weighted middle bound from the pointwise one.**  A uniform bound `B`
on the middle window gives `∑ τ(N+r)·b^(L-r) ≤ B·b^(L-K)`: the weighted
interface is never worse than the pointwise interface. -/
theorem weighted_middle_bound_of_pointwise
    (b N K L B : ℕ) (hb : 2 ≤ b)
    (hmiddle : ∀ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card ≤ B) :
    ∑ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card * b ^ (L - r)
      ≤ B * b ^ (L - K) := by
  have h1 : ∑ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card * b ^ (L - r)
      ≤ ∑ r ∈ Finset.Icc (K + 1) L, B * b ^ (L - r) :=
    Finset.sum_le_sum fun r hr => Nat.mul_le_mul (hmiddle r hr) (le_refl _)
  have h3 : ∑ r ∈ Finset.Icc (K + 1) L, b ^ (L - r)
      = ∑ j ∈ Finset.range (L - K), b ^ (L - (K + 1 + j)) := by
    have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range]
    have hn : L + 1 - (K + 1) = L - K := by omega
    rw [hn]
  have h4 : ∑ j ∈ Finset.range (L - K), b ^ (L - (K + 1 + j))
      = ∑ j ∈ Finset.range (L - K), b ^ (L - K - 1 - j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    congr 1
    omega
  have h5 : ∑ j ∈ Finset.range (L - K), b ^ (L - K - 1 - j)
      = ∑ j ∈ Finset.range (L - K), b ^ j :=
    Finset.sum_range_reflect (fun j => b ^ j) (L - K)
  calc ∑ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card * b ^ (L - r)
      ≤ ∑ r ∈ Finset.Icc (K + 1) L, B * b ^ (L - r) := h1
    _ = B * ∑ r ∈ Finset.Icc (K + 1) L, b ^ (L - r) := by rw [Finset.mul_sum]
    _ = B * ∑ j ∈ Finset.range (L - K), b ^ j := by rw [h3, h4, h5]
    _ ≤ B * b ^ (L - K) :=
        Nat.mul_le_mul (le_refl _) (geom_sum_range_le_pow b (L - K) hb)

/-- **Weighted certificates subsume pointwise certificates.**  Classical
`(N, K, L, B)` divisor block certificate data yields weighted-middle
certificate data with `C = B·b^(L-K)` under the same arithmetic
inequality. -/
theorem weighted_block_certificate_of_pointwise
    (b q N K L B : ℕ) (hb : 2 ≤ b)
    (hmiddle : ∀ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card ≤ B)
    (harith : q * (B * b ^ (L - K) + (N + L + 2)) < b ^ L) :
    ∃ C : ℕ,
      (∑ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card * b ^ (L - r) ≤ C)
        ∧ q * (C + (N + L + 2)) < b ^ L :=
  ⟨B * b ^ (L - K), weighted_middle_bound_of_pointwise b N K L B hb hmiddle, harith⟩

/-- **Weighted certificate consumer.**  A weighted divisor block certificate
`(N, K, L, C)` for precision `q` — first-block divisibility, the exact
weighted middle sum `∑_{r=K+1}^{L} τ(N+r)·b^(L-r) ≤ C`, and the
ℕ-arithmetic inequality `q·(C + (N+L+2)) < b^L` — yields a near-integer
witness for the `b^N`-dilated divisor-count series.  The middle window is
paid at its exact weighted value rather than through a pointwise bound:
this is the certificate shape an averaging argument naturally produces,
and it subsumes the pointwise interface via
`weighted_block_certificate_of_pointwise`. -/
theorem near_int_witness_of_weighted_divisor_block_certificate
    (b q N K L C : ℕ) (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (hblock : ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ (N + r).divisors.card)
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card * b ^ (L - r) ≤ C)
    (harith : q * (C + (N + L + 2)) < b ^ L) :
    ∃ z : ℤ,
      0 < |(b : ℝ) ^ N * (∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)| ∧
        |(b : ℝ) ^ N * (∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)| < 1 / (q : ℝ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨z₀, hz₀⟩ := bpow_mul_divisor_count_series_eq_int_add_tail b N hb
  have hfsum : Summable
      (fun r : ℕ => (((N + r + 1).divisors.card : ℝ)) / (b : ℝ) ^ (r + 1)) :=
    summable_divisor_count_shift_tail b N hb
  have hfarsum : Summable
      (fun t : ℕ => (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) :=
    (summable_nat_add_iff L).mpr hfsum
  -- split the tail at L
  have hsplitL : (∑' r : ℕ, (((N + r + 1).divisors.card : ℝ)) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  -- split the finite part at K
  have hsplitK : (∑ i ∈ Finset.range L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  -- the first block is an integer
  set z₁ : ℕ := ∑ i ∈ Finset.range K, (N + i + 1).divisors.card / b ^ (i + 1) with hz₁def
  have hz₁ : ((z₁ : ℕ) : ℝ)
      = ∑ i ∈ Finset.range K, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [hz₁def]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp hi
    have hdvd : b ^ (i + 1) ∣ (N + i + 1).divisors.card :=
      hblock (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hbpow0 : ((b ^ (i + 1) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_div hdvd hbpow0]
    push_cast
    ring
  -- remainder positivity
  have hmid_nonneg : (0 : ℝ)
      ≤ ∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hfar_pos : (0 : ℝ)
      < ∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    have hne : N + (0 + L) + 1 ≠ 0 := by omega
    have hτpos : 0 < (N + (0 + L) + 1).divisors.card :=
      Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hne)
    have hterm0 : (0 : ℝ)
        < (((N + (0 + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((0 + L) + 1) := by
      have hc : (0 : ℝ) < (((N + (0 + L) + 1).divisors.card : ℝ)) := by exact_mod_cast hτpos
      positivity
    calc (0 : ℝ) < (((N + (0 + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((0 + L) + 1) := hterm0
      _ ≤ _ := hfarsum.le_tsum 0 fun j _ => by positivity
  -- middle window: exact weighted sum over the common denominator b^L
  have hterm : ∀ i ∈ Finset.Ico K L,
      (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1)
        = (((N + i + 1).divisors.card * b ^ (L - (i + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    intro i hi
    obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
    have hb1 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
    have hbL' : ((b : ℝ) ^ L) ≠ 0 := by positivity
    have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (L - (i + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_div_iff hb1 hbL']
    push_cast
    rw [hsplit]
    ring
  have hreindex : (∑ i ∈ Finset.Ico K L, (N + i + 1).divisors.card * b ^ (L - (i + 1)))
      = ∑ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card * b ^ (L - r) := by
    have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hn : L + 1 - (K + 1) = L - K := by omega
    rw [hn]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : N + (K + j) + 1 = N + (K + 1 + j) := by omega
    have h2 : L - (K + j + 1) = L - (K + 1 + j) := by omega
    rw [h1, h2]
  have hmid : (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
      ≤ (C : ℝ) / (b : ℝ) ^ L := by
    have hsum_eq : (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            (((N + i + 1).divisors.card * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    have hnum : (∑ i ∈ Finset.Ico K L,
        (((N + i + 1).divisors.card * b ^ (L - (i + 1)) : ℕ) : ℝ)) ≤ (C : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hreindex.trans_le hmiddle
    calc (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            (((N + i + 1).divisors.card * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := hsum_eq
      _ ≤ (C : ℝ) / (b : ℝ) ^ L := by gcongr
  -- far tail bound, reshaped from the far-tail lemma
  have hfar_eq : (∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, (((N + L + 1 + t).divisors.card : ℝ)) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar : (∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact divisor_count_far_tail_le b N L hb
  -- assemble the witness
  refine ⟨z₀ + (z₁ : ℤ), ?_⟩
  have habs : (b : ℝ) ^ N * (∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (b : ℝ) ^ (m + 1))
      - ((z₀ + (z₁ : ℤ) : ℤ) : ℝ)
      = (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    rw [hz₀, hsplitL, hsplitK]
    push_cast
    rw [← hz₁]
    ring
  have hR_pos : (0 : ℝ)
      < (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    add_pos_of_nonneg_of_pos hmid_nonneg hfar_pos
  constructor
  · rw [habs]
    exact abs_pos.mpr (ne_of_gt hR_pos)
  · rw [habs, abs_of_pos hR_pos]
    have hsum_le : (∑ i ∈ Finset.Ico K L, (((N + i + 1).divisors.card : ℝ)) / (b : ℝ) ^ (i + 1))
        + (∑' t : ℕ, (((N + (t + L) + 1).divisors.card : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
        ≤ (C : ℝ) / (b : ℝ) ^ L + ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L :=
      add_le_add hmid hfar
    refine lt_of_le_of_lt hsum_le ?_
    have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    have hc : (q : ℝ) * ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) < (b : ℝ) ^ L := by
      exact_mod_cast harith
    rw [← add_div, div_lt_div_iff₀ hbL hq', one_mul]
    calc ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) * (q : ℝ)
        = (q : ℝ) * ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) := mul_comm _ _
      _ < (b : ℝ) ^ L := hc

/-- **Full-support (Erdős–Borwein) irrationality from weighted block
certificates.**  If for every precision `q` some weighted divisor block
certificate `(N, K, L, C)` exists, the full-support series
`∑_{n≥1} 1 / (b^n - 1)` is irrational.  The weighted middle hypothesis is
implied by the pointwise one (`weighted_block_certificate_of_pointwise`),
so this closure is at least as strong as the landed pointwise closure;
certificate existence itself is NOT claimed. -/
theorem irrational_erdosSum_full_support_of_weighted_block_certificates
    (b : ℕ) (hb : 2 ≤ b)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ (N + r).divisors.card) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card * b ^ (L - r) ≤ C) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := by
  refine irrational_erdosSum_full_support_of_near_int b hb fun q hq => ?_
  obtain ⟨N, K, L, C, hKL, hblock, hmiddle, harith⟩ := hcert q hq
  obtain ⟨z, hz⟩ := near_int_witness_of_weighted_divisor_block_certificate
    b q N K L C hb hq hKL hblock hmiddle harith
  exact ⟨N, z, hz⟩

/-! ## Full-support lane: CRT first-block construction -/

/-- **Exact valuation from a product congruence.**  If
`n ≡ π^(b-1) [MOD π^b]` where `π = ∏ P` is a product of distinct primes,
then every `p ∈ P` has exact valuation `b - 1` in `n`: writing
`n = π^b·t + π^(b-1) = π^(b-1)·(π·t + 1)`, the cofactor is prime to `p`. -/
theorem factorization_eq_of_modEq_prod_pow
    (b : ℕ) (hb : 2 ≤ b) (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hπ : 2 ≤ ∏ p ∈ P, p) (n : ℕ)
    (hmod : n ≡ (∏ p ∈ P, p) ^ (b - 1) [MOD (∏ p ∈ P, p) ^ b]) :
    ∀ p ∈ P, n.factorization p = b - 1 := by
  intro p hpP
  set π : ℕ := ∏ p ∈ P, p with hπdef
  have hb1 : b - 1 + 1 = b := by omega
  have hπpos : 0 < π := by omega
  have hπpow : π ^ b = π ^ (b - 1) * π := by
    calc π ^ b = π ^ (b - 1 + 1) := by rw [hb1]
      _ = π ^ (b - 1) * π := pow_succ π (b - 1)
  have hpowpos : 0 < π ^ (b - 1) := pow_pos hπpos _
  have hlt : π ^ (b - 1) < π ^ b := by
    rw [hπpow]
    exact (Nat.lt_mul_iff_one_lt_right hpowpos).mpr (by omega)
  have hmodeq : n % π ^ b = π ^ (b - 1) := by
    have h : n % π ^ b = π ^ (b - 1) % π ^ b := hmod
    rw [h, Nat.mod_eq_of_lt hlt]
  have hn_eq : n = π ^ (b - 1) * (π * (n / π ^ b) + 1) := by
    have hdm := Nat.div_add_mod n (π ^ b)
    rw [hmodeq] at hdm
    calc n = π ^ b * (n / π ^ b) + π ^ (b - 1) := hdm.symm
      _ = π ^ (b - 1) * (π * (n / π ^ b) + 1) := by rw [hπpow]; ring
  have hp := hP p hpP
  have hp_dvd_π : p ∣ π := Finset.dvd_prod_of_mem _ hpP
  have hcof_ne : π * (n / π ^ b) + 1 ≠ 0 := by omega
  have hp_ndvd : ¬ p ∣ (π * (n / π ^ b) + 1) := by
    intro hdvd
    have h1 : p ∣ π * (n / π ^ b) := hp_dvd_π.mul_right _
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hdvd
    have h3 := Nat.le_of_dvd one_pos h2
    have h4 := hp.two_le
    omega
  have hvπ : π.factorization p = 1 := by
    rw [hπdef, Nat.factorization_prod (fun q hq => (hP q hq).pos.ne')]
    rw [Finset.sum_apply']
    rw [Finset.sum_eq_single p]
    · rw [(hP p hpP).factorization]
      simp
    · intro q hq hqp
      rw [(hP q hq).factorization]
      exact Finsupp.single_eq_of_ne (Ne.symm hqp)
    · intro hnot
      exact absurd hpP hnot
  have hv1 : (π * (n / π ^ b) + 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hp_ndvd
  rw [hn_eq, Nat.factorization_mul (pow_pos hπpos _).ne' hcof_ne, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hvπ, hv1, mul_one, add_zero]

theorem exists_prime_finset_card_gt (r M : ℕ) :
    ∃ P : Finset ℕ, P.card = r ∧ (∀ p ∈ P, Nat.Prime p) ∧ ∀ p ∈ P, M < p := by
  induction r with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ r ih =>
      obtain ⟨P, hcard, hprime, hgt⟩ := ih
      obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max M (P.sup id) + 1)
      have hpM : M < p := by
        have h1 := le_max_left M (P.sup id)
        omega
      have hpnotin : p ∉ P := by
        intro hmem
        have hle : p ≤ P.sup id := by simpa using Finset.le_sup (f := id) hmem
        have h2 := le_max_right M (P.sup id)
        omega
      refine ⟨insert p P, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hpnotin, hcard]
      · intro q hq
        rcases Finset.mem_insert.mp hq with h | h
        · exact h ▸ hp
        · exact hprime q h
      · intro q hq
        rcases Finset.mem_insert.mp hq with h | h
        · exact h ▸ hpM
        · exact hgt q h

/-- **CRT block construction (exact-valuation form).**  For every window
length `K` there are `x` and a positive modulus `A` such that along the
whole progression `x + y·A`, every slot `r ∈ [1, K]` carries a set of `r`
distinct primes, all above the prescribed bound `L`, at which
`x + y·A + r` has exact valuation `b - 1`.  Blocks are added one at a time:
each new slot imposes a single congruence
`x + r ≡ π^(b-1) [MOD π^b]` with `π` the product of a fresh prime block,
glued to the accumulated modulus by binary CRT. -/
theorem exists_exact_valuation_progression
    (b L : ℕ) (hb : 2 ≤ b) (K : ℕ) :
    ∃ x A : ℕ, 0 < A ∧
      ∀ r ∈ Finset.Icc 1 K, ∃ P : Finset ℕ,
        P.card = r ∧ (∀ p ∈ P, Nat.Prime p) ∧ (∀ p ∈ P, L < p) ∧
        ∀ y : ℕ, ∀ p ∈ P, (x + y * A + r).factorization p = b - 1 := by
  induction K with
  | zero =>
      refine ⟨0, 1, one_pos, fun r hr => ?_⟩
      have := Finset.mem_Icc.mp hr
      omega
  | succ K ih =>
      obtain ⟨x, A, hA, hblocks⟩ := ih
      obtain ⟨P, hcard, hprime, hgt⟩ :=
        exists_prime_finset_card_gt (K + 1) (max (max L A) (K + 1))
      have hgtL : ∀ p ∈ P, L < p := fun p hp =>
        lt_of_le_of_lt (le_trans (le_max_left L A) (le_max_left (max L A) (K + 1))) (hgt p hp)
      have hgtA : ∀ p ∈ P, A < p := fun p hp =>
        lt_of_le_of_lt (le_trans (le_max_right L A) (le_max_left (max L A) (K + 1))) (hgt p hp)
      have hgtK : ∀ p ∈ P, K + 1 < p := fun p hp =>
        lt_of_le_of_lt (le_max_right (max L A) (K + 1)) (hgt p hp)
      set π : ℕ := ∏ p ∈ P, p with hπdef
      have hπpos : 0 < π := Finset.prod_pos fun p hp => (hprime p hp).pos
      have hPne : P.Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨p₀, hp₀⟩ := hPne
      have hp₀_le : p₀ ≤ π := Nat.le_of_dvd hπpos (Finset.dvd_prod_of_mem _ hp₀)
      have hπgtK : K + 1 < π := lt_of_lt_of_le (hgtK p₀ hp₀) hp₀_le
      have hπ2 : 2 ≤ π := le_trans (hprime p₀ hp₀).two_le hp₀_le
      have hKle : K + 1 ≤ π ^ (b - 1) := by
        have hself : π ≤ π ^ (b - 1) := Nat.le_self_pow (by omega) π
        omega
      set c : ℕ := π ^ (b - 1) - (K + 1) with hcdef
      have hcop : Nat.Coprime A (π ^ b) := by
        have hπA : Nat.Coprime π A := Nat.Coprime.prod_left fun p hp =>
          ((hprime p hp).coprime_iff_not_dvd).mpr fun hdvd =>
            absurd (Nat.le_of_dvd hA hdvd) (not_le.mpr (hgtA p hp))
        exact (hπA.pow_left b).symm
      obtain ⟨x₁, hx₁A, hx₁M⟩ := Nat.chineseRemainder hcop x c
      set A' : ℕ := A * π ^ b with hA'def
      have hA'pos : 0 < A' := Nat.mul_pos hA (pow_pos hπpos b)
      set x' : ℕ := x₁ + A' * x with hx'def
      have hx'A : x' ≡ x [MOD A] := by
        have h1 : A ∣ A' * x := ⟨π ^ b * x, by rw [hA'def]; ring⟩
        have h2 : x₁ + A' * x ≡ x₁ + 0 [MOD A] :=
          (Nat.ModEq.refl x₁).add ((Nat.modEq_zero_iff_dvd).mpr h1)
        rw [hx'def]
        exact h2.trans (by simpa using hx₁A)
      have hx'M : x' ≡ c [MOD π ^ b] := by
        have h1 : π ^ b ∣ A' * x := ⟨A * x, by rw [hA'def]; ring⟩
        have h2 : x₁ + A' * x ≡ x₁ + 0 [MOD π ^ b] :=
          (Nat.ModEq.refl x₁).add ((Nat.modEq_zero_iff_dvd).mpr h1)
        rw [hx'def]
        exact h2.trans (by simpa using hx₁M)
      have hxle : x ≤ x' := by
        have hmul : x ≤ A' * x := Nat.le_mul_of_pos_left x hA'pos
        omega
      obtain ⟨t, ht⟩ : A ∣ x' - x := (Nat.modEq_iff_dvd' hxle).mp hx'A.symm
      have hx'eq : x' = x + A * t := by omega
      refine ⟨x', A', hA'pos, fun r hr => ?_⟩
      rcases Finset.mem_Icc.mp hr with ⟨hr1, hrK⟩
      by_cases hrle : r ≤ K
      · -- old block, transferred along the refined progression
        obtain ⟨Pr, hPrcard, hPrprime, hPrgt, hPrval⟩ :=
          hblocks r (Finset.mem_Icc.mpr ⟨hr1, hrle⟩)
        refine ⟨Pr, hPrcard, hPrprime, hPrgt, fun y p hp => ?_⟩
        have harg : x' + y * A' + r = x + (t + y * π ^ b) * A + r := by
          rw [hx'eq, hA'def]
          ring
        rw [harg]
        exact hPrval (t + y * π ^ b) p hp
      · -- new block r = K + 1
        have hreq : r = K + 1 := by omega
        subst hreq
        refine ⟨P, hcard, hprime, hgtL, fun y p hp => ?_⟩
        have h1 : π ^ b ∣ y * A' := ⟨y * A, by rw [hA'def]; ring⟩
        have hmodn : x' + y * A' + (K + 1) ≡ c + 0 + (K + 1) [MOD π ^ b] :=
          (hx'M.add ((Nat.modEq_zero_iff_dvd).mpr h1)).add (Nat.ModEq.refl (K + 1))
        have hc_eq : c + 0 + (K + 1) = π ^ (b - 1) := by
          rw [hcdef]
          omega
        rw [hc_eq] at hmodn
        exact factorization_eq_of_modEq_prod_pow b hb P hprime hπ2 _ hmodn p hp

/-- **First-block divisibility along a full arithmetic progression.**  For
every base `b ≥ 2`, window length `K`, and prime floor `L`, there are `x`
and a positive modulus `A` with `b^r ∣ τ(x + y·A + r)` for every `y` and
every `r ∈ [1, K]` — the first-block half of the divisor block certificate
obligation, produced by CRT from exact prime valuations via the
multiplicativity hinge, with every construction prime above `L`. -/
theorem exists_first_block_divisibility_progression
    (b K L : ℕ) (hb : 2 ≤ b) :
    ∃ x A : ℕ, 0 < A ∧
      ∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ (x + y * A + r).divisors.card := by
  obtain ⟨x, A, hA, hblocks⟩ := exists_exact_valuation_progression b L hb K
  refine ⟨x, A, hA, fun y r hr => ?_⟩
  obtain ⟨P, hcard, hprime, hgt, hval⟩ := hblocks r hr
  have hne : x + y * A + r ≠ 0 := by
    have := (Finset.mem_Icc.mp hr).1
    omega
  have hdvd := bpow_dvd_card_divisors_of_exact_prime_block b (x + y * A + r) hb hne P
    (fun p hp => hval y p hp)
  rwa [hcard] at hdvd

/-! ## Full-support lane: middle-window average and selection -/

/-- **CRT block construction with exposed modulus support.**  The same
construction as `exists_exact_valuation_progression`, additionally exposing
the arithmetic of the modulus: every prime divisor of `A` lies above `L`
and divides `x + r` for some first-block slot `r ∈ [1, K]`.  This is the
frame fact the middle-window analysis consumes — first-block primes cannot
touch the middle window. -/
theorem exists_exact_valuation_progression_with_support
    (b L : ℕ) (hb : 2 ≤ b) (K : ℕ) :
    ∃ x A : ℕ, 0 < A ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ A → L < p ∧ ∃ r ∈ Finset.Icc 1 K, p ∣ x + r) ∧
      ∀ r ∈ Finset.Icc 1 K, ∃ P : Finset ℕ,
        P.card = r ∧ (∀ p ∈ P, Nat.Prime p) ∧ (∀ p ∈ P, L < p) ∧
        ∀ y : ℕ, ∀ p ∈ P, (x + y * A + r).factorization p = b - 1 := by
  induction K with
  | zero =>
      refine ⟨0, 1, one_pos,
        fun p hp hdvd => absurd (Nat.dvd_one.mp hdvd) hp.ne_one, fun r hr => ?_⟩
      have := Finset.mem_Icc.mp hr
      omega
  | succ K ih =>
      obtain ⟨x, A, hA, hsupp, hblocks⟩ := ih
      obtain ⟨P, hcard, hprime, hgt⟩ :=
        exists_prime_finset_card_gt (K + 1) (max (max L A) (K + 1))
      have hgtL : ∀ p ∈ P, L < p := fun p hp =>
        lt_of_le_of_lt (le_trans (le_max_left L A) (le_max_left (max L A) (K + 1))) (hgt p hp)
      have hgtA : ∀ p ∈ P, A < p := fun p hp =>
        lt_of_le_of_lt (le_trans (le_max_right L A) (le_max_left (max L A) (K + 1))) (hgt p hp)
      have hgtK : ∀ p ∈ P, K + 1 < p := fun p hp =>
        lt_of_le_of_lt (le_max_right (max L A) (K + 1)) (hgt p hp)
      set π : ℕ := ∏ p ∈ P, p with hπdef
      have hπpos : 0 < π := Finset.prod_pos fun p hp => (hprime p hp).pos
      have hPne : P.Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨p₀, hp₀⟩ := hPne
      have hp₀_le : p₀ ≤ π := Nat.le_of_dvd hπpos (Finset.dvd_prod_of_mem _ hp₀)
      have hπgtK : K + 1 < π := lt_of_lt_of_le (hgtK p₀ hp₀) hp₀_le
      have hπ2 : 2 ≤ π := le_trans (hprime p₀ hp₀).two_le hp₀_le
      have hKle : K + 1 ≤ π ^ (b - 1) := by
        have hself : π ≤ π ^ (b - 1) := Nat.le_self_pow (by omega) π
        omega
      set c : ℕ := π ^ (b - 1) - (K + 1) with hcdef
      have hcop : Nat.Coprime A (π ^ b) := by
        have hπA : Nat.Coprime π A := Nat.Coprime.prod_left fun p hp =>
          ((hprime p hp).coprime_iff_not_dvd).mpr fun hdvd =>
            absurd (Nat.le_of_dvd hA hdvd) (not_le.mpr (hgtA p hp))
        exact (hπA.pow_left b).symm
      obtain ⟨x₁, hx₁A, hx₁M⟩ := Nat.chineseRemainder hcop x c
      set A' : ℕ := A * π ^ b with hA'def
      have hA'pos : 0 < A' := Nat.mul_pos hA (pow_pos hπpos b)
      set x' : ℕ := x₁ + A' * x with hx'def
      have hx'A : x' ≡ x [MOD A] := by
        have h1 : A ∣ A' * x := ⟨π ^ b * x, by rw [hA'def]; ring⟩
        have h2 : x₁ + A' * x ≡ x₁ + 0 [MOD A] :=
          (Nat.ModEq.refl x₁).add ((Nat.modEq_zero_iff_dvd).mpr h1)
        rw [hx'def]
        exact h2.trans (by simpa using hx₁A)
      have hx'M : x' ≡ c [MOD π ^ b] := by
        have h1 : π ^ b ∣ A' * x := ⟨A * x, by rw [hA'def]; ring⟩
        have h2 : x₁ + A' * x ≡ x₁ + 0 [MOD π ^ b] :=
          (Nat.ModEq.refl x₁).add ((Nat.modEq_zero_iff_dvd).mpr h1)
        rw [hx'def]
        exact h2.trans (by simpa using hx₁M)
      have hxle : x ≤ x' := by
        have hmul : x ≤ A' * x := Nat.le_mul_of_pos_left x hA'pos
        omega
      obtain ⟨t, ht⟩ : A ∣ x' - x := (Nat.modEq_iff_dvd' hxle).mp hx'A.symm
      have hx'eq : x' = x + A * t := by omega
      have hnewval : ∀ y : ℕ, ∀ p ∈ P,
          (x' + y * A' + (K + 1)).factorization p = b - 1 := by
        intro y p hp
        have h1 : π ^ b ∣ y * A' := ⟨y * A, by rw [hA'def]; ring⟩
        have hmodn : x' + y * A' + (K + 1) ≡ c + 0 + (K + 1) [MOD π ^ b] :=
          (hx'M.add ((Nat.modEq_zero_iff_dvd).mpr h1)).add (Nat.ModEq.refl (K + 1))
        have hc_eq : c + 0 + (K + 1) = π ^ (b - 1) := by
          rw [hcdef]
          omega
        rw [hc_eq] at hmodn
        exact factorization_eq_of_modEq_prod_pow b hb P hprime hπ2 _ hmodn p hp
      refine ⟨x', A', hA'pos, ?_, fun r hr => ?_⟩
      · -- modulus support: primes of `A' = A · π^b` are old frame primes or new ones
        intro p hp hpA'
        rw [hA'def] at hpA'
        rcases (Nat.Prime.dvd_mul hp).mp hpA' with hpA | hpπb
        · obtain ⟨hLp, r, hrmem, hpxr⟩ := hsupp p hp hpA
          rcases Finset.mem_Icc.mp hrmem with ⟨hr1, hr2⟩
          refine ⟨hLp, r, Finset.mem_Icc.mpr ⟨hr1, by omega⟩, ?_⟩
          have harg : x' + r = (x + r) + A * t := by
            rw [hx'eq]
            ring
          rw [harg]
          exact dvd_add hpxr (hpA.mul_right t)
        · have hpπ : p ∣ π := hp.dvd_of_dvd_pow hpπb
          have hpP : p ∈ P := by
            have hpπ' : p ∣ ∏ q ∈ P, q := by
              rw [← hπdef]
              exact hpπ
            obtain ⟨p', hp'P, hpp'⟩ := Prime.exists_mem_finset_dvd hp.prime hpπ'
            have heq : p = p' := (Nat.prime_dvd_prime_iff_eq hp (hprime p' hp'P)).mp hpp'
            rw [heq]
            exact hp'P
          refine ⟨hgtL p hpP, K + 1, Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩, ?_⟩
          have hval0 := hnewval 0 p hpP
          have hn0 : x' + 0 * A' + (K + 1) = x' + (K + 1) := by ring
          rw [hn0] at hval0
          have hne : x' + (K + 1) ≠ 0 := by omega
          refine (Nat.Prime.dvd_iff_one_le_factorization hp hne).mpr ?_
          rw [hval0]
          omega
      · rcases Finset.mem_Icc.mp hr with ⟨hr1, hrK⟩
        by_cases hrle : r ≤ K
        · obtain ⟨Pr, hPrcard, hPrprime, hPrgt, hPrval⟩ :=
            hblocks r (Finset.mem_Icc.mpr ⟨hr1, hrle⟩)
          refine ⟨Pr, hPrcard, hPrprime, hPrgt, fun y p hp => ?_⟩
          have harg : x' + y * A' + r = x + (t + y * π ^ b) * A + r := by
            rw [hx'eq, hA'def]
            ring
          rw [harg]
          exact hPrval (t + y * π ^ b) p hp
        · have hreq : r = K + 1 := by omega
          subst hreq
          exact ⟨P, hcard, hprime, hgtL, hnewval⟩

/-- **Middle-window coprimality from modulus support.**  If every prime of
`A` lies above `L` and divides `x + r` for some `r ∈ [1, K]`, then `A` is
coprime to every middle-window shift `x + s` with `K < s ≤ L`: a common
prime would divide `s - r`, which is positive and below `L < p`.  This is
the free lemma the CRT frame buys — the construction primes force the
first block and then vanish from the middle window. -/
theorem coprime_middle_of_first_block_support
    (x A K L s : ℕ)
    (hsupp : ∀ p : ℕ, Nat.Prime p → p ∣ A → L < p ∧ ∃ r ∈ Finset.Icc 1 K, p ∣ x + r)
    (hs1 : K < s) (hs2 : s ≤ L) :
    Nat.Coprime A (x + s) := by
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpA : p ∣ A := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpxs : p ∣ x + s := hpg.trans (Nat.gcd_dvd_right _ _)
  obtain ⟨hLp, r, hrmem, hpxr⟩ := hsupp p hp hpA
  rcases Finset.mem_Icc.mp hrmem with ⟨hr1, hrK⟩
  have hsub : p ∣ x + s - (x + r) := Nat.dvd_sub hpxs hpxr
  have heq : x + s - (x + r) = s - r := by omega
  rw [heq] at hsub
  have hple : p ≤ s - r := Nat.le_of_dvd (by omega) hsub
  omega

/-- **Single-residue-class divisor counting along a progression.**  A
modulus `d` coprime to the step `A` divides `A·y + c` for at most
`Y/d + 1` of the window values `y < Y`: any two solutions differ by a
multiple of `d`.  This is the exact-arithmetic engine behind the
divisor-sum average — no analytic number theory enters. -/
theorem card_filter_dvd_progression_le
    (A c d Y : ℕ) (hd : 0 < d) (hcop : Nat.Coprime d A) :
    ((Finset.range Y).filter (fun y => d ∣ A * y + c)).card ≤ Y / d + 1 := by
  classical
  have hmono : ∀ y₁ ∈ (Finset.range Y).filter (fun y => d ∣ A * y + c),
      ∀ y₂ ∈ (Finset.range Y).filter (fun y => d ∣ A * y + c),
      y₁ < y₂ → y₁ / d < y₂ / d := by
    intro y₁ h₁ y₂ h₂ hlt
    have hy₁d := (Finset.mem_filter.mp h₁).2
    have hy₂d := (Finset.mem_filter.mp h₂).2
    obtain ⟨k, rfl⟩ : ∃ k, y₂ = y₁ + k := ⟨y₂ - y₁, by omega⟩
    have hk : 0 < k := by omega
    have h3 : A * (y₁ + k) + c = (A * y₁ + c) + A * k := by ring
    rw [h3] at hy₂d
    have hAk : d ∣ A * k := (Nat.dvd_add_right hy₁d).mp hy₂d
    have hdk : d ∣ k := hcop.dvd_of_dvd_mul_left hAk
    have hdle : d ≤ k := Nat.le_of_dvd hk hdk
    have hstep : (y₁ + d) / d ≤ (y₁ + k) / d := Nat.div_le_div_right (by omega)
    have hsucc : (y₁ + d) / d = y₁ / d + 1 := Nat.add_div_right y₁ hd
    calc y₁ / d < y₁ / d + 1 := Nat.lt_succ_self _
      _ = (y₁ + d) / d := hsucc.symm
      _ ≤ (y₁ + k) / d := hstep
  have hmaps : ∀ y ∈ (Finset.range Y).filter (fun y => d ∣ A * y + c),
      y / d ∈ Finset.range (Y / d + 1) := by
    intro y hy
    have hyY : y < Y := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have hle : y / d ≤ Y / d := Nat.div_le_div_right (Nat.le_of_lt hyY)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hinj : Set.InjOn (fun y => y / d)
      ↑((Finset.range Y).filter (fun y => d ∣ A * y + c)) := by
    intro y₁ h₁ y₂ h₂ heq
    replace h₁ := Finset.mem_coe.mp h₁
    replace h₂ := Finset.mem_coe.mp h₂
    by_contra hne2
    rcases Nat.lt_or_ge y₁ y₂ with h | h
    · exact absurd heq (Nat.ne_of_lt (hmono y₁ h₁ y₂ h₂ h))
    · rcases Nat.lt_or_ge y₂ y₁ with h' | h'
      · exact absurd heq.symm (Nat.ne_of_lt (hmono y₂ h₂ y₁ h₁ h'))
      · exact hne2 (by omega)
  calc ((Finset.range Y).filter (fun y => d ∣ A * y + c)).card
      ≤ (Finset.range (Y / d + 1)).card :=
        Finset.card_le_card_of_injOn (fun y => y / d) hmaps hinj
    _ = Y / d + 1 := Finset.card_range _

/-- **Divisor pairing against a square bound.**  For `n ≤ X`, the divisor
count of `n` is at most twice the number of divisors of `n` up to `√X`:
divisors pair as `d·(n/d) = n`, and both partners cannot exceed `√X`. -/
theorem card_divisors_le_two_mul_card_small_divisors
    (n X : ℕ) (hnX : n ≤ X) :
    n.divisors.card
      ≤ 2 * ((Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ∣ n)).card := by
  classical
  have hsplit :
      (n.divisors.filter (fun d => d ≤ Nat.sqrt X)).card
        + (n.divisors.filter (fun d => ¬ d ≤ Nat.sqrt X)).card
      = n.divisors.card :=
    Finset.card_filter_add_card_filter_not _
  have hmaps : ∀ d ∈ n.divisors.filter (fun d => ¬ d ≤ Nat.sqrt X),
      n / d ∈ n.divisors.filter (fun d => d ≤ Nat.sqrt X) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hddvd, hdgt⟩
    rcases Nat.mem_divisors.mp hddvd with ⟨hdvd, hne⟩
    have hq_dvd : n / d ∣ n := ⟨d, (Nat.div_mul_cancel hdvd).symm⟩
    have hq_le : n / d ≤ Nat.sqrt X := by
      by_contra hq_gt
      have h3 : (Nat.sqrt X + 1) * (Nat.sqrt X + 1) ≤ d * (n / d) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h4 : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      have h5 : X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := Nat.lt_succ_sqrt X
      omega
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hq_dvd, hne⟩, hq_le⟩
  have hinj : Set.InjOn (fun d => n / d)
      ↑(n.divisors.filter (fun d => ¬ d ≤ Nat.sqrt X)) := by
    intro d₁ h₁ d₂ h₂ heq
    replace h₁ := Finset.mem_filter.mp (Finset.mem_coe.mp h₁)
    replace h₂ := Finset.mem_filter.mp (Finset.mem_coe.mp h₂)
    rcases Nat.mem_divisors.mp h₁.1 with ⟨hdvd₁, hne⟩
    rcases Nat.mem_divisors.mp h₂.1 with ⟨hdvd₂, _⟩
    have e₁ : n / (n / d₁) = d₁ := Nat.div_div_self hdvd₁ hne
    have e₂ : n / (n / d₂) = d₂ := Nat.div_div_self hdvd₂ hne
    calc d₁ = n / (n / d₁) := e₁.symm
      _ = n / (n / d₂) := by rw [show n / d₁ = n / d₂ from heq]
      _ = d₂ := e₂
  have hlarge_le :
      (n.divisors.filter (fun d => ¬ d ≤ Nat.sqrt X)).card
        ≤ (n.divisors.filter (fun d => d ≤ Nat.sqrt X)).card :=
    Finset.card_le_card_of_injOn (fun d => n / d) hmaps hinj
  have hsmall_le :
      (n.divisors.filter (fun d => d ≤ Nat.sqrt X)).card
        ≤ ((Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ∣ n)).card := by
    apply Finset.card_le_card
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hddvd, hdle⟩
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hddvd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hdpos, hdle⟩, (Nat.mem_divisors.mp hddvd).1⟩
  omega

/-- **Elementary divisor-sum average along a coprime progression.**  With
`gcd(A, c) = 1` and all window values bounded by `X`, the divisor counts
of `A·y + c` over `y < Y` sum to at most `2·∑_{d ≤ √X} (Y/d + 1)`:
divisor pairing plus single-residue-class counting.  PNT-free. -/
theorem sum_card_divisors_progression_le
    (A c Y X : ℕ) (hcop : Nat.Coprime A c)
    (hX : ∀ y ∈ Finset.range Y, A * y + c ≤ X) :
    ∑ y ∈ Finset.range Y, (A * y + c).divisors.card
      ≤ 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (Y / d + 1) := by
  classical
  have h1 : ∑ y ∈ Finset.range Y, (A * y + c).divisors.card
      ≤ ∑ y ∈ Finset.range Y,
          2 * ((Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ∣ A * y + c)).card :=
    Finset.sum_le_sum fun y hy =>
      card_divisors_le_two_mul_card_small_divisors (A * y + c) X (hX y hy)
  have h5 : ∀ d ∈ Finset.Icc 1 (Nat.sqrt X),
      ∑ y ∈ Finset.range Y, (if d ∣ A * y + c then 1 else 0) ≤ Y / d + 1 := by
    intro d hd
    have hd1 : 0 < d := by
      rcases Finset.mem_Icc.mp hd with ⟨h, _⟩
      omega
    have hcount : ∑ y ∈ Finset.range Y, (if d ∣ A * y + c then 1 else 0)
        = ((Finset.range Y).filter (fun y => d ∣ A * y + c)).card :=
      (Finset.card_filter _ _).symm
    rw [hcount]
    by_cases hdA : Nat.Coprime d A
    · exact card_filter_dvd_progression_le A c d Y hd1 hdA
    · have hempty : (Finset.range Y).filter (fun y => d ∣ A * y + c) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro y _ hdvd
        apply hdA
        have hg_A : Nat.gcd d A ∣ A := Nat.gcd_dvd_right _ _
        have hg_c : Nat.gcd d A ∣ c := by
          have hg_n : Nat.gcd d A ∣ A * y + c := (Nat.gcd_dvd_left d A).trans hdvd
          have hg_Ay : Nat.gcd d A ∣ A * y := hg_A.mul_right y
          have hsub := Nat.dvd_sub hg_n hg_Ay
          have heq : A * y + c - A * y = c := by omega
          rwa [heq] at hsub
        have hg1 : Nat.gcd d A ∣ Nat.gcd A c := Nat.dvd_gcd hg_A hg_c
        have hAc : Nat.gcd A c = 1 := hcop
        rw [hAc] at hg1
        exact Nat.dvd_one.mp hg1
      rw [hempty]
      simp
  calc ∑ y ∈ Finset.range Y, (A * y + c).divisors.card
      ≤ ∑ y ∈ Finset.range Y,
          2 * ((Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ∣ A * y + c)).card := h1
    _ = 2 * ∑ y ∈ Finset.range Y,
          ((Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ∣ A * y + c)).card := by
        rw [Finset.mul_sum]
    _ = 2 * ∑ y ∈ Finset.range Y,
          ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (if d ∣ A * y + c then 1 else 0) := by
        congr 1
        exact Finset.sum_congr rfl fun y _ => Finset.card_filter _ _
    _ = 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X),
          ∑ y ∈ Finset.range Y, (if d ∣ A * y + c then 1 else 0) := by
        rw [Finset.sum_comm]
    _ ≤ 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (Y / d + 1) :=
        Nat.mul_le_mul (le_refl 2) (Finset.sum_le_sum h5)

/-- Geometric weight of the middle window: `∑_{s=K+1}^{L} b^(L-s) ≤ b^(L-K)`. -/
theorem sum_pow_weight_middle_window_le (b K L : ℕ) (hb : 2 ≤ b) :
    ∑ s ∈ Finset.Icc (K + 1) L, b ^ (L - s) ≤ b ^ (L - K) := by
  have h3 : ∑ r ∈ Finset.Icc (K + 1) L, b ^ (L - r)
      = ∑ j ∈ Finset.range (L - K), b ^ (L - (K + 1 + j)) := by
    have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range]
    have hn : L + 1 - (K + 1) = L - K := by omega
    rw [hn]
  have h4 : ∑ j ∈ Finset.range (L - K), b ^ (L - (K + 1 + j))
      = ∑ j ∈ Finset.range (L - K), b ^ (L - K - 1 - j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    congr 1
    omega
  have h5 : ∑ j ∈ Finset.range (L - K), b ^ (L - K - 1 - j)
      = ∑ j ∈ Finset.range (L - K), b ^ j :=
    Finset.sum_range_reflect (fun j => b ^ j) (L - K)
  rw [h3, h4, h5]
  exact geom_sum_range_le_pow b (L - K) hb

/-- **Weighted middle-window total along the progression.**  Summing the
weighted middle sums over the window `y < Y` costs at most
`b^(L-K) · (2·∑_{d ≤ √X} (Y/d + 1))`: middle-window coprimality from the
modulus support, then the elementary progression average, then the
geometric weight. -/
theorem sum_weighted_middle_window_le
    (b x A K L Y X : ℕ) (hb : 2 ≤ b)
    (hsupp : ∀ p : ℕ, Nat.Prime p → p ∣ A → L < p ∧ ∃ r ∈ Finset.Icc 1 K, p ∣ x + r)
    (hX : ∀ y ∈ Finset.range Y, x + y * A + L ≤ X) :
    ∑ y ∈ Finset.range Y,
        ∑ s ∈ Finset.Icc (K + 1) L, (x + y * A + s).divisors.card * b ^ (L - s)
      ≤ b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (Y / d + 1)) := by
  classical
  have hinner : ∀ s ∈ Finset.Icc (K + 1) L,
      ∑ y ∈ Finset.range Y, (x + y * A + s).divisors.card
        ≤ 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (Y / d + 1) := by
    intro s hs
    rcases Finset.mem_Icc.mp hs with ⟨hs1, hs2⟩
    have hcop : Nat.Coprime A (x + s) :=
      coprime_middle_of_first_block_support x A K L s hsupp (by omega) hs2
    have hXs : ∀ y ∈ Finset.range Y, A * y + (x + s) ≤ X := by
      intro y hy
      have h := hX y hy
      have harr : A * y + (x + s) = x + y * A + s := by ring
      omega
    have hres := sum_card_divisors_progression_le A (x + s) Y X hcop hXs
    calc ∑ y ∈ Finset.range Y, (x + y * A + s).divisors.card
        = ∑ y ∈ Finset.range Y, (A * y + (x + s)).divisors.card := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have harr : x + y * A + s = A * y + (x + s) := by ring
          rw [harr]
      _ ≤ 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (Y / d + 1) := hres
  calc ∑ y ∈ Finset.range Y,
        ∑ s ∈ Finset.Icc (K + 1) L, (x + y * A + s).divisors.card * b ^ (L - s)
      = ∑ s ∈ Finset.Icc (K + 1) L,
          ∑ y ∈ Finset.range Y, (x + y * A + s).divisors.card * b ^ (L - s) :=
        Finset.sum_comm
    _ = ∑ s ∈ Finset.Icc (K + 1) L,
          (∑ y ∈ Finset.range Y, (x + y * A + s).divisors.card) * b ^ (L - s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
    _ ≤ ∑ s ∈ Finset.Icc (K + 1) L,
          b ^ (L - s) * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (Y / d + 1)) :=
        Finset.sum_le_sum fun s hs => by
          rw [Nat.mul_comm (b ^ (L - s)) (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (Y / d + 1))]
          exact Nat.mul_le_mul (hinner s hs) (le_refl _)
    _ = (∑ s ∈ Finset.Icc (K + 1) L, b ^ (L - s))
          * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (Y / d + 1)) := by
        rw [Finset.sum_mul]
    _ ≤ b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (Y / d + 1)) :=
        Nat.mul_le_mul (sum_pow_weight_middle_window_le b K L hb) (le_refl _)

/-- **Pigeonhole selection.**  If `Y` window values sum to at most `T`,
some value is at most `T / Y`. -/
theorem exists_le_div_of_sum_le (Y T : ℕ) (hY : 0 < Y) (W : ℕ → ℕ)
    (h : ∑ y ∈ Finset.range Y, W y ≤ T) :
    ∃ y : ℕ, y < Y ∧ W y ≤ T / Y := by
  by_contra hcon
  have hall : ∀ y ∈ Finset.range Y, T / Y + 1 ≤ W y := by
    intro y hy
    by_contra hle
    exact hcon ⟨y, Finset.mem_range.mp hy, Nat.lt_succ_iff.mp (Nat.not_le.mp hle)⟩
  have hsum : Y * (T / Y + 1) ≤ ∑ y ∈ Finset.range Y, W y := by
    calc Y * (T / Y + 1) = ∑ _y ∈ Finset.range Y, (T / Y + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ ∑ y ∈ Finset.range Y, W y := Finset.sum_le_sum hall
  have hTlt : T < Y * (T / Y) + Y := by
    have h1 : Y * (T / Y) + T % Y = T := Nat.div_add_mod T Y
    have h2 : T % Y < Y := Nat.mod_lt _ hY
    calc T = Y * (T / Y) + T % Y := h1.symm
      _ < Y * (T / Y) + Y := Nat.add_lt_add_left h2 _
  have hexp : Y * (T / Y + 1) = Y * (T / Y) + Y := by ring
  have hcontra : Y * (T / Y) + Y ≤ T := by
    rw [← hexp]
    exact le_trans hsum h
  exact absurd (lt_of_lt_of_le hTlt hcontra) (lt_irrefl T)

/-- **First-block progression with a selected small weighted middle.**
Unconditionally, for every base `b ≥ 2`, window shape `(K, L)`, and
averaging range `Y > 0`, the CRT construction yields `x` and `A > 0` with
first-block divisibility along the whole progression, together with some
`y < Y` whose weighted middle sum is bounded by the elementary
divisor-pair average `(b^(L-K) · 2·∑_{d ≤ √(x+Y·A+L)} (Y/d + 1)) / Y`.
This is the middle-window selection half of the Erdős 1948 route in
certificate shape; what remains for full certificate existence is
explicit size control of `x` and `A` (and hence parameter closure
in `q`). -/
theorem exists_first_block_progression_with_selected_weighted_middle
    (b K L Y : ℕ) (hb : 2 ≤ b) (hY : 0 < Y) :
    ∃ x A : ℕ, 0 < A ∧
      (∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ (x + y * A + r).divisors.card) ∧
      ∃ y : ℕ, y < Y ∧
        ∑ s ∈ Finset.Icc (K + 1) L, (x + y * A + s).divisors.card * b ^ (L - s)
          ≤ (b ^ (L - K)
              * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + Y * A + L)), (Y / d + 1))) / Y := by
  obtain ⟨x, A, hA, hsupp, hblocks⟩ :=
    exists_exact_valuation_progression_with_support b L hb K
  have hfirst : ∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K,
      b ^ r ∣ (x + y * A + r).divisors.card := by
    intro y r hr
    obtain ⟨P, hcard, hprime, hgt, hval⟩ := hblocks r hr
    have hne : x + y * A + r ≠ 0 := by
      have := (Finset.mem_Icc.mp hr).1
      omega
    have hdvd := bpow_dvd_card_divisors_of_exact_prime_block b (x + y * A + r) hb hne P
      (fun p hp => hval y p hp)
    rwa [hcard] at hdvd
  refine ⟨x, A, hA, hfirst, ?_⟩
  have hX : ∀ y ∈ Finset.range Y, x + y * A + L ≤ x + Y * A + L := by
    intro y hy
    have hyY : y ≤ Y := Nat.le_of_lt (Finset.mem_range.mp hy)
    have hmul : y * A ≤ Y * A := Nat.mul_le_mul_right A hyY
    omega
  have htotal := sum_weighted_middle_window_le b x A K L Y (x + Y * A + L) hb hsupp hX
  exact exists_le_div_of_sum_le Y
    (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + Y * A + L)), (Y / d + 1)))
    hY
    (fun y => ∑ s ∈ Finset.Icc (K + 1) L, (x + y * A + s).divisors.card * b ^ (L - s))
    htotal

/-! ## Full-support lane: bounded CRT frame and certificate existence -/

/-- **Parameter closure kernel.**  The linear function `c·κ + e` is dominated
by `2^κ` at `κ = 3c + e`: cube `c + 1 ≤ 2^c` and absorb the slack. -/
theorem param_linear_le_two_pow (c e : ℕ) :
    c * (3 * c + e) + e ≤ 2 ^ (3 * c + e) := by
  have hc : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  have he : e + 1 ≤ 2 ^ e := Nat.lt_two_pow_self
  have hcube : (c + 1) ^ 3 * (e + 1) ≤ 2 ^ (3 * c + e) := by
    calc (c + 1) ^ 3 * (e + 1) ≤ (2 ^ c) ^ 3 * 2 ^ e :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hc 3) he
      _ = 2 ^ (c * 3) * 2 ^ e := by rw [pow_mul]
      _ = 2 ^ (c * 3 + e) := (pow_add 2 (c * 3) e).symm
      _ = 2 ^ (3 * c + e) := by rw [Nat.mul_comm c 3]
  calc c * (3 * c + e) + e = 3 * c ^ 2 + c * e + e := by ring
    _ ≤ (c ^ 3 * e + 3 * c ^ 2 * e + 2 * c * e + c ^ 3 + 3 * c + 1)
          + (3 * c ^ 2 + c * e + e) := Nat.le_add_left _ _
    _ = (c + 1) ^ 3 * (e + 1) := by ring
    _ ≤ 2 ^ (3 * c + e) := hcube

/-- **Dyadic harmonic core.**  `∑_{d=1}^{S} ⌊Y/d⌋ ≤ Y·(J+1)` whenever
`S ≤ 2^J`: each dyadic bucket `(2^j, 2^{j+1}]` contributes at most `Y`. -/
theorem harmonic_div_sum_core (J : ℕ) :
    ∀ S Y : ℕ, S ≤ 2 ^ J → ∑ d ∈ Finset.Icc 1 S, Y / d ≤ Y * (J + 1) := by
  induction J with
  | zero =>
      intro S Y hS
      norm_num at hS
      interval_cases S
      · rw [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty]
        omega
      · rw [Finset.Icc_self, Finset.sum_singleton, Nat.div_one]
        omega
  | succ J ih =>
      intro S Y hS
      by_cases hS2 : S ≤ 2 ^ J
      · calc ∑ d ∈ Finset.Icc 1 S, Y / d ≤ Y * (J + 1) := ih S Y hS2
          _ ≤ Y * (J + 1 + 1) := Nat.mul_le_mul_left Y (by omega)
      · have hS2' : 2 ^ J < S := not_le.mp hS2
        have h2Jpos : 0 < 2 ^ J := pow_pos (by norm_num) J
        have hle : 2 ^ J ≤ S := Nat.le_of_lt hS2'
        have hsplit : Finset.Icc 1 S = Finset.Icc 1 (2 ^ J) ∪ Finset.Ioc (2 ^ J) S := by
          ext a
          simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
          omega
        have hdisj : Disjoint (Finset.Icc 1 (2 ^ J)) (Finset.Ioc (2 ^ J) S) := by
          rw [Finset.disjoint_left]
          intro a ha hb
          rw [Finset.mem_Icc] at ha
          rw [Finset.mem_Ioc] at hb
          omega
        rw [hsplit, Finset.sum_union hdisj]
        have h1 : ∑ d ∈ Finset.Icc 1 (2 ^ J), Y / d ≤ Y * (J + 1) :=
          ih (2 ^ J) Y (le_refl _)
        have h2 : ∑ d ∈ Finset.Ioc (2 ^ J) S, Y / d ≤ Y := by
          have hbound : ∀ d ∈ Finset.Ioc (2 ^ J) S, Y / d ≤ Y / 2 ^ J := by
            intro d hd
            rw [Finset.mem_Ioc] at hd
            exact Nat.div_le_div_left (Nat.le_of_lt hd.1) h2Jpos
          have hcardsum : ∑ d ∈ Finset.Ioc (2 ^ J) S, Y / d
              ≤ (Finset.Ioc (2 ^ J) S).card • (Y / 2 ^ J) :=
            Finset.sum_le_card_nsmul _ _ _ hbound
          have hcard : (Finset.Ioc (2 ^ J) S).card = S - 2 ^ J := Nat.card_Ioc _ _
          have hcard2 : S - 2 ^ J ≤ 2 ^ J := by
            have hpow : (2 : ℕ) ^ (J + 1) = 2 * 2 ^ J := by rw [pow_succ]; ring
            omega
          have hmul : (S - 2 ^ J) * (Y / 2 ^ J) ≤ 2 ^ J * (Y / 2 ^ J) :=
            Nat.mul_le_mul_right _ hcard2
          have hfold : 2 ^ J * (Y / 2 ^ J) ≤ Y := Nat.mul_div_le Y (2 ^ J)
          rw [hcard, smul_eq_mul] at hcardsum
          omega
        calc (∑ d ∈ Finset.Icc 1 (2 ^ J), Y / d) + ∑ d ∈ Finset.Ioc (2 ^ J) S, Y / d
            ≤ Y * (J + 1) + Y := Nat.add_le_add h1 h2
          _ = Y * (J + 1 + 1) := by ring

/-- **Dyadic harmonic compression.**  `∑_{d=1}^{S} (⌊Y/d⌋ + 1) ≤ Y·(J+1) + S`
for `S ≤ 2^J` — the closed form that turns the raw progression divisor
average into a parameter-usable middle bound. -/
theorem harmonic_div_sum_le (S Y J : ℕ) (hS : S ≤ 2 ^ J) :
    ∑ d ∈ Finset.Icc 1 S, (Y / d + 1) ≤ Y * (J + 1) + S := by
  have hsplit : ∑ d ∈ Finset.Icc 1 S, (Y / d + 1)
      = (∑ d ∈ Finset.Icc 1 S, Y / d) + (S + 1 - 1) * 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
  have hcore := harmonic_div_sum_core J S Y hS
  omega

/-- **Bertrand prime block.**  `r` distinct primes in `(m, 2^r·m]`, produced
by chaining Bertrand's postulate — bounded fresh prime supply with no
prime-counting input. -/
theorem exists_bertrand_prime_block (m r : ℕ) (hm : 1 ≤ m) :
    ∃ Q : Finset ℕ, Q.card = r ∧ (∀ p ∈ Q, Nat.Prime p) ∧
      (∀ p ∈ Q, m < p) ∧ (∀ p ∈ Q, p ≤ 2 ^ r * m) := by
  induction r with
  | zero => exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | succ r ih =>
      obtain ⟨Q, hcard, hprime, hgt, hle⟩ := ih
      have hn0 : 2 ^ r * m ≠ 0 := by positivity
      obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ r * m) hn0
      have hpnotin : p ∉ Q := fun hmem => absurd (hle p hmem) (not_le.mpr hpgt)
      refine ⟨insert p Q, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hpnotin, hcard]
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hp
        · exact hprime x h
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · have h1 : m ≤ 2 ^ r * m := Nat.le_mul_of_pos_left m (pow_pos (by norm_num) r)
          omega
        · exact hgt x h
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · have h2 : 2 * (2 ^ r * m) = 2 ^ (r + 1) * m := by rw [pow_succ]; ring
          omega
        · have h3 : 2 ^ r * m ≤ 2 ^ (r + 1) * m := by
            have h4 : (2 : ℕ) ^ r ≤ 2 ^ (r + 1) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
            exact Nat.mul_le_mul_right m h4
          have := hle x h
          omega

/-- **Bounded disjoint prime blocks.**  A triangular family of pairwise
disjoint prime blocks — block `r` has `r` primes — all in `(L, m]` with the
explicit global ceiling `m ≤ 2^(K(K+1))·(L+1)`.  Disjointness comes from
stacking Bertrand intervals, never from primes exceeding an accumulated
modulus. -/
theorem exists_bounded_disjoint_prime_blocks (L K : ℕ) :
    ∃ (P : ℕ → Finset ℕ) (m : ℕ),
      L + 1 ≤ m ∧ m ≤ 2 ^ (K * (K + 1)) * (L + 1) ∧
      (∀ r ∈ Finset.Icc 1 K, (P r).card = r) ∧
      (∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r, Nat.Prime p) ∧
      (∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r, L < p) ∧
      (∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r, p ≤ m) ∧
      (∀ r s, r ∈ Finset.Icc 1 K → s ∈ Finset.Icc 1 K → r ≠ s →
        Disjoint (P r) (P s)) := by
  induction K with
  | zero =>
      refine ⟨fun _ => ∅, L + 1, le_refl _, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr; exact absurd (Finset.mem_Icc.mp hr) (by omega)
      · intro r hr; exact absurd (Finset.mem_Icc.mp hr) (by omega)
      · intro r hr; exact absurd (Finset.mem_Icc.mp hr) (by omega)
      · intro r hr; exact absurd (Finset.mem_Icc.mp hr) (by omega)
      · intro r s hr hs hrs; exact absurd (Finset.mem_Icc.mp hr) (by omega)
  | succ K ih =>
      obtain ⟨P, m, hLm, hmB, hcards, hprimes, hgtL, hlem, hdisj⟩ := ih
      obtain ⟨Q, hQcard, hQprime, hQgt, hQle⟩ :=
        exists_bertrand_prime_block m (K + 1) (by omega)
      refine ⟨fun r => if r = K + 1 then Q else P r, 2 ^ (K + 1) * m,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h1 : m ≤ 2 ^ (K + 1) * m :=
          Nat.le_mul_of_pos_left m (pow_pos (by norm_num) _)
        omega
      · calc 2 ^ (K + 1) * m
            ≤ 2 ^ (K + 1) * (2 ^ (K * (K + 1)) * (L + 1)) :=
              Nat.mul_le_mul_left _ hmB
          _ = 2 ^ ((K + 1) + K * (K + 1)) * (L + 1) := by
              rw [← mul_assoc, ← pow_add]
          _ ≤ 2 ^ ((K + 1) * (K + 1 + 1)) * (L + 1) := by
              have h5 : (K + 1) * (K + 1 + 1)
                  = ((K + 1) + K * (K + 1)) + (K + 1) := by ring
              have h6 : (K + 1) + K * (K + 1) ≤ (K + 1) * (K + 1 + 1) := by omega
              exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h6)
      · intro r hr
        dsimp only
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases h : r = K + 1
        · rw [if_pos h, hQcard, h]
        · rw [if_neg h]
          exact hcards r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩)
      · intro r hr p hp
        dsimp only at hp
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases h : r = K + 1
        · rw [if_pos h] at hp
          exact hQprime p hp
        · rw [if_neg h] at hp
          exact hprimes r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩) p hp
      · intro r hr p hp
        dsimp only at hp
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases h : r = K + 1
        · rw [if_pos h] at hp
          have := hQgt p hp
          omega
        · rw [if_neg h] at hp
          exact hgtL r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩) p hp
      · intro r hr p hp
        dsimp only at hp
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases h : r = K + 1
        · rw [if_pos h] at hp
          have h1 : 2 ^ (K + 1) = 2 ^ (K + 1) := rfl
          exact hQle p hp
        · rw [if_neg h] at hp
          have h1 : p ≤ m := hlem r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩) p hp
          have h2 : m ≤ 2 ^ (K + 1) * m :=
            Nat.le_mul_of_pos_left m (pow_pos (by norm_num) _)
          omega
      · intro r s hr hs hrs
        dsimp only
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        rcases Finset.mem_Icc.mp hs with ⟨hs1, hs2⟩
        by_cases h1 : r = K + 1
        · have h2 : ¬ s = K + 1 := by omega
          rw [if_pos h1, if_neg h2, Finset.disjoint_left]
          intro p hpQ hpPs
          have hgt := hQgt p hpQ
          have hle := hlem s (Finset.mem_Icc.mpr ⟨hs1, by omega⟩) p hpPs
          omega
        · rw [if_neg h1]
          by_cases h2 : s = K + 1
          · rw [if_pos h2, Finset.disjoint_left]
            intro p hpPr hpQ
            have hgt := hQgt p hpQ
            have hle := hlem r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩) p hpPr
            omega
          · rw [if_neg h2]
            exact hdisj r s (Finset.mem_Icc.mpr ⟨hr1, by omega⟩)
              (Finset.mem_Icc.mpr ⟨hs1, by omega⟩) hrs

/-- **Normalised simultaneous CRT.**  Pairwise coprime moduli share a common
residue *below the product of the moduli* — the height-aware form: old
congruences transfer by divisibility, and the representative never leaves
`[0, ∏ m_r)`. -/
theorem exists_bounded_crt_residue (K : ℕ) (m c : ℕ → ℕ)
    (hpos : ∀ r ∈ Finset.Icc 1 K, 0 < m r)
    (hcop : ∀ r s, r ∈ Finset.Icc 1 K → s ∈ Finset.Icc 1 K → r ≠ s →
      Nat.Coprime (m r) (m s)) :
    ∃ x : ℕ, x < ∏ r ∈ Finset.Icc 1 K, m r ∧
      ∀ r ∈ Finset.Icc 1 K, x ≡ c r [MOD m r] := by
  induction K with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · rw [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.prod_empty]
        omega
      · intro r hr
        exact absurd (Finset.mem_Icc.mp hr) (by omega)
  | succ K ih =>
      have hsub : ∀ r, r ∈ Finset.Icc 1 K → r ∈ Finset.Icc 1 (K + 1) := by
        intro r hr
        rcases Finset.mem_Icc.mp hr with ⟨h1, h2⟩
        exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
      obtain ⟨x₀, hx₀lt, hx₀cong⟩ := ih (fun r hr => hpos r (hsub r hr))
        (fun r s hr hs hrs => hcop r s (hsub r hr) (hsub s hs) hrs)
      have hK1mem : K + 1 ∈ Finset.Icc 1 (K + 1) :=
        Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩
      have hcopA : Nat.Coprime (∏ r ∈ Finset.Icc 1 K, m r) (m (K + 1)) :=
        Nat.Coprime.prod_left fun r hr =>
          hcop r (K + 1) (hsub r hr) hK1mem
            (by rcases Finset.mem_Icc.mp hr with ⟨_, h2⟩; omega)
      have hA0 : (∏ r ∈ Finset.Icc 1 K, m r) ≠ 0 := by
        have h1 : 0 < ∏ r ∈ Finset.Icc 1 K, m r :=
          Finset.prod_pos fun r hr => hpos r (hsub r hr)
        omega
      have hm0 : m (K + 1) ≠ 0 := by
        have := hpos (K + 1) hK1mem
        omega
      have hlt := Nat.chineseRemainder_lt_mul hcopA x₀ (c (K + 1)) hA0 hm0
      obtain ⟨hcong1, hcong2⟩ := (Nat.chineseRemainder hcopA x₀ (c (K + 1))).2
      refine ⟨(Nat.chineseRemainder hcopA x₀ (c (K + 1)) : ℕ), ?_, ?_⟩
      · rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ K + 1)]
        exact hlt
      · intro r hr
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases hrK : r ≤ K
        · have hrmem : r ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hr1, hrK⟩
          have hdvd : m r ∣ ∏ j ∈ Finset.Icc 1 K, m j :=
            Finset.dvd_prod_of_mem m hrmem
          exact (Nat.ModEq.of_dvd hdvd hcong1).trans (hx₀cong r hrmem)
        · have hreq : r = K + 1 := by omega
          rw [hreq]
          exact hcong2

/-- **Bounded first-block frame.**  The height-aware replacement for the
qualitative CRT supply: `x < A`, the modulus support is exposed (every prime
of `A` is above `L` and meets the first block), first-block divisibility
holds along the whole progression, and — decisively — `A` carries the
explicit bound `(2^(K(K+1))·(L+1))^(b·K²)`.  Disjoint Bertrand blocks
replace "fresh prime above the accumulated modulus". -/
theorem exists_bounded_first_block_frame
    (b L K : ℕ) (hb : 2 ≤ b) (hK : 1 ≤ K) (hKL : K ≤ L) :
    ∃ x A : ℕ, 0 < A ∧ x < A ∧ L + 1 ≤ A ∧
      A ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (b * K ^ 2) ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ A → L < p ∧ ∃ r ∈ Finset.Icc 1 K, p ∣ x + r) ∧
      (∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ (x + y * A + r).divisors.card) := by
  classical
  obtain ⟨P, M, hLM, hMB, hcards, hprimes, hgtL, hleM, hdisj⟩ :=
    exists_bounded_disjoint_prime_blocks L K
  set π : ℕ → ℕ := fun r => ∏ p ∈ P r, p with hπdef
  set mm : ℕ → ℕ := fun r => (π r) ^ b with hmmdef
  have hπpos : ∀ r ∈ Finset.Icc 1 K, 0 < π r := fun r hr =>
    Finset.prod_pos fun p hp => (hprimes r hr p hp).pos
  have hπ2 : ∀ r ∈ Finset.Icc 1 K, 2 ≤ π r := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
    have hne : (P r).Nonempty := by
      rw [← Finset.card_pos, hcards r hr]
      omega
    obtain ⟨p₀, hp₀⟩ := hne
    have h1 : p₀ ≤ π r := Nat.le_of_dvd (hπpos r hr) (Finset.dvd_prod_of_mem _ hp₀)
    have h2 := (hprimes r hr p₀ hp₀).two_le
    omega
  have hπgtL : ∀ r ∈ Finset.Icc 1 K, L < π r := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
    have hne : (P r).Nonempty := by
      rw [← Finset.card_pos, hcards r hr]
      omega
    obtain ⟨p₀, hp₀⟩ := hne
    have h1 : p₀ ≤ π r := Nat.le_of_dvd (hπpos r hr) (Finset.dvd_prod_of_mem _ hp₀)
    have h2 := hgtL r hr p₀ hp₀
    omega
  have hmmpos : ∀ r ∈ Finset.Icc 1 K, 0 < mm r := fun r hr => pow_pos (hπpos r hr) b
  have hmmcop : ∀ r s, r ∈ Finset.Icc 1 K → s ∈ Finset.Icc 1 K → r ≠ s →
      Nat.Coprime (mm r) (mm s) := by
    intro r s hr hs hrs
    have hππ : Nat.Coprime (π r) (π s) := by
      apply Nat.Coprime.prod_left
      intro p hp
      have h1 : Nat.Coprime (π s) p := by
        apply Nat.Coprime.prod_left
        intro p' hp'
        have hne' : p' ≠ p := by
          intro heq
          have hp'' : p ∈ P s := heq ▸ hp'
          exact (Finset.disjoint_left.mp (hdisj r s hr hs hrs) hp) hp''
        exact (Nat.coprime_primes (hprimes s hs p' hp') (hprimes r hr p hp)).mpr hne'
      exact h1.symm
    exact Nat.Coprime.pow b b hππ
  have hrle : ∀ r ∈ Finset.Icc 1 K, r ≤ (π r) ^ (b - 1) := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
    have h1 : π r ≤ (π r) ^ (b - 1) := Nat.le_self_pow (by omega) _
    have h2 := hπgtL r hr
    omega
  obtain ⟨x, hxlt, hxcong⟩ := exists_bounded_crt_residue K mm
    (fun r => (π r) ^ (b - 1) - r) hmmpos hmmcop
  set A : ℕ := ∏ r ∈ Finset.Icc 1 K, mm r with hAdef
  have hApos : 0 < A := Finset.prod_pos hmmpos
  have hmmdvdA : ∀ r ∈ Finset.Icc 1 K, mm r ∣ A := fun r hr =>
    Finset.dvd_prod_of_mem mm hr
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_refl _, hK⟩
  have hLA : L + 1 ≤ A := by
    have h1 : mm 1 ≤ A := Nat.le_of_dvd hApos (hmmdvdA 1 h1mem)
    have h2 : π 1 ≤ mm 1 := Nat.le_self_pow (by omega) _
    have h3 := hπgtL 1 h1mem
    omega
  have hshift : ∀ r ∈ Finset.Icc 1 K, x + r ≡ (π r) ^ (b - 1) [MOD mm r] := by
    intro r hr
    have h1 := (hxcong r hr).add_right r
    have h2 : (π r) ^ (b - 1) - r + r = (π r) ^ (b - 1) :=
      Nat.sub_add_cancel (hrle r hr)
    rwa [h2] at h1
  have hprogcong : ∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K,
      x + y * A + r ≡ (π r) ^ (b - 1) [MOD mm r] := by
    intro y r hr
    have h1 : mm r ∣ y * A := Dvd.dvd.mul_left (hmmdvdA r hr) y
    have h2 : x + y * A + r ≡ x + 0 + r [MOD mm r] :=
      ((Nat.ModEq.refl x).add ((Nat.modEq_zero_iff_dvd).mpr h1)).add_right r
    have h3 : x + 0 + r = x + r := by ring
    rw [h3] at h2
    exact h2.trans (hshift r hr)
  have hval : ∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r,
      (x + y * A + r).factorization p = b - 1 := by
    intro y r hr p hp
    exact factorization_eq_of_modEq_prod_pow b hb (P r)
      (fun p' hp' => hprimes r hr p' hp') (hπ2 r hr) _ (hprogcong y r hr) p hp
  refine ⟨x, A, hApos, hxlt, hLA, ?_, ?_, ?_⟩
  · -- modulus bound
    have hMpos : 0 < M := by omega
    have hπleMK : ∀ r ∈ Finset.Icc 1 K, π r ≤ M ^ K := by
      intro r hr
      have h1 : π r ≤ M ^ (P r).card :=
        Finset.prod_le_pow_card (P r) _ M (fun p hp => hleM r hr p hp)
      have h2 : M ^ (P r).card = M ^ r := by rw [hcards r hr]
      have h3 : M ^ r ≤ M ^ K :=
        Nat.pow_le_pow_right hMpos (Finset.mem_Icc.mp hr).2
      omega
    have hmmle : ∀ r ∈ Finset.Icc 1 K, mm r ≤ (M ^ K) ^ b := fun r hr =>
      Nat.pow_le_pow_left (hπleMK r hr) b
    have hAle1 : A ≤ ((M ^ K) ^ b) ^ K := by
      have h1 : A ≤ ((M ^ K) ^ b) ^ (Finset.Icc 1 K).card :=
        Finset.prod_le_pow_card _ _ _ hmmle
      have h2 : (Finset.Icc 1 K).card = K := by rw [Nat.card_Icc]; omega
      rwa [h2] at h1
    have hAle2 : ((M ^ K) ^ b) ^ K = M ^ (b * K ^ 2) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    have hMle : M ^ (b * K ^ 2) ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (b * K ^ 2) :=
      Nat.pow_le_pow_left hMB _
    omega
  · -- modulus support
    intro p hp hpA
    rw [hAdef] at hpA
    obtain ⟨r, hrmem, hpmm⟩ := Prime.exists_mem_finset_dvd hp.prime hpA
    have hpπ : p ∣ π r := hp.dvd_of_dvd_pow hpmm
    obtain ⟨p', hp'mem, hpp'⟩ := Prime.exists_mem_finset_dvd hp.prime hpπ
    have heq : p = p' :=
      (Nat.prime_dvd_prime_iff_eq hp (hprimes r hrmem p' hp'mem)).mp hpp'
    have hpP : p ∈ P r := heq ▸ hp'mem
    refine ⟨hgtL r hrmem p hpP, r, hrmem, ?_⟩
    have h1 : p ∣ mm r := hpπ.trans (dvd_pow_self (π r) (by omega : b ≠ 0))
    have h2 : x + r ≡ (π r) ^ (b - 1) [MOD p] :=
      Nat.ModEq.of_dvd h1 (hshift r hrmem)
    have h3 : p ∣ (π r) ^ (b - 1) :=
      hpπ.trans (dvd_pow_self (π r) (by omega : b - 1 ≠ 0))
    have h4 : (π r) ^ (b - 1) ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr h3
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans h4)
  · -- first-block divisibility
    intro y r hr
    have hne : x + y * A + r ≠ 0 := by
      have := (Finset.mem_Icc.mp hr).1
      omega
    have hdvd := bpow_dvd_card_divisors_of_exact_prime_block b (x + y * A + r)
      hb hne (P r) (fun p hp => hval y r hr p hp)
    rwa [hcards r hr] at hdvd

/-- **Selected weighted middle for an external supported frame.**  The
middle-window selection argument, freed from the internal CRT supply: any
`x, A` with exposed support yield some `y < Y` whose weighted middle sum is
bounded by the elementary divisor-pair average.  This is the consumer the
bounded frame feeds. -/
theorem selected_weighted_middle_of_supported_frame
    (b x A K L Y : ℕ) (hb : 2 ≤ b) (hY : 0 < Y)
    (hsupp : ∀ p : ℕ, Nat.Prime p → p ∣ A → L < p ∧ ∃ r ∈ Finset.Icc 1 K, p ∣ x + r) :
    ∃ y : ℕ, y < Y ∧
      ∑ s ∈ Finset.Icc (K + 1) L, (x + y * A + s).divisors.card * b ^ (L - s)
        ≤ (b ^ (L - K)
            * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + Y * A + L)), (Y / d + 1))) / Y := by
  have hX : ∀ y ∈ Finset.range Y, x + y * A + L ≤ x + Y * A + L := by
    intro y hy
    have hyY : y ≤ Y := Nat.le_of_lt (Finset.mem_range.mp hy)
    have hmul : y * A ≤ Y * A := Nat.mul_le_mul_right A hyY
    omega
  have htotal := sum_weighted_middle_window_le b x A K L Y (x + Y * A + L) hb hsupp hX
  exact exists_le_div_of_sum_le Y
    (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + Y * A + L)), (Y / d + 1)))
    hY
    (fun y => ∑ s ∈ Finset.Icc (K + 1) L, (x + y * A + s).divisors.card * b ^ (L - s))
    htotal

/-- **Certificate parameter arithmetic.**  For `K = 9(q+b+100)` and the
explicit `κ`, `E` below: the middle cost `4q(E+κ+5)` fits under `b^K`, the
far-tail exponent budget `2E+κ+q+4` fits under `2^κ`, and `K ≤ 2^κ`.
Everything reduces to `n < 2^n` and exponent bookkeeping — no logarithms,
no analytic input. -/
theorem certificate_param_arithmetic
    (b q K κ E : ℕ) (hb : 2 ≤ b) (hq : 0 < q)
    (hK : K = 9 * (q + b + 100))
    (hκ : κ = 3 * (2 * b * K ^ 2 + 1) + (2 * b * K ^ 2 * (K * (K + 1) + 1) + q + 4))
    (hE : E = b * K ^ 2 * (K * (K + 1) + κ + 1)) :
    4 * q * (E + κ + 5) ≤ b ^ K ∧ 2 * E + κ + q + 4 ≤ 2 ^ κ ∧ 1 ≤ K ∧ K ≤ 2 ^ κ := by
  have hK1 : 1 ≤ K := by omega
  have hKκ : K ≤ κ := by
    have h1 : K ≤ K * K := Nat.le_mul_of_pos_left K (by omega)
    have h2 : K * K ≤ b * (K * K) := Nat.le_mul_of_pos_left (K * K) (by omega)
    have h3 : b * (K * K) = b * K ^ 2 := by ring
    have h4 : 2 * (b * K ^ 2) = 2 * b * K ^ 2 := by ring
    omega
  have hκpow : κ < 2 ^ κ := Nat.lt_two_pow_self
  have hKκpow : K ≤ 2 ^ κ := by omega
  have hclosure : 2 * E + κ + q + 4 ≤ 2 ^ κ := by
    have hkey := param_linear_le_two_pow (2 * b * K ^ 2 + 1)
      (2 * b * K ^ 2 * (K * (K + 1) + 1) + q + 4)
    rw [← hκ] at hkey
    have hle : 2 * E + κ + q + 4
        = (2 * b * K ^ 2 + 1) * κ + (2 * b * K ^ 2 * (K * (K + 1) + 1) + q + 4) := by
      rw [hE]; ring
    omega
  have hgrind : 4 * q * (E + κ + 5) ≤ b ^ K := by
    have hq2 : q < 2 ^ q := Nat.lt_two_pow_self
    have hb2 : b < 2 ^ b := Nat.lt_two_pow_self
    have hKle : K ≤ 2 ^ (q + b + 10) := by
      have h1 : q + b < 2 ^ (q + b) := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (q + b + 10) = 2 ^ (q + b) * 1024 := by
        rw [pow_add]; norm_num
      omega
    have hK1le : K + 1 ≤ 2 ^ (q + b + 11) := by
      have h2 : (2 : ℕ) ^ (q + b + 11) = 2 ^ (q + b + 10) * 2 := pow_succ 2 (q + b + 10)
      omega
    have hKsq : K ^ 2 ≤ 2 ^ (2 * q + 2 * b + 20) := by
      have h1 : K ^ 2 = K * K := by ring
      have h2 : K * K ≤ 2 ^ (q + b + 10) * 2 ^ (q + b + 10) := Nat.mul_le_mul hKle hKle
      have h3 : (2 : ℕ) ^ (q + b + 10) * 2 ^ (q + b + 10) = 2 ^ (2 * q + 2 * b + 20) := by
        rw [← pow_add]; congr 1; ring
      omega
    have hKK1 : K * (K + 1) ≤ 2 ^ (2 * q + 2 * b + 21) := by
      have h2 : K * (K + 1) ≤ 2 ^ (q + b + 10) * 2 ^ (q + b + 11) :=
        Nat.mul_le_mul hKle hK1le
      have h3 : (2 : ℕ) ^ (q + b + 10) * 2 ^ (q + b + 11) = 2 ^ (2 * q + 2 * b + 21) := by
        rw [← pow_add]; congr 1; ring
      omega
    have hbK2 : b * K ^ 2 ≤ 2 ^ (3 * q + 3 * b + 20) := by
      have h1 : b * K ^ 2 ≤ 2 ^ b * 2 ^ (2 * q + 2 * b + 20) :=
        Nat.mul_le_mul (Nat.le_of_lt hb2) hKsq
      have h2 : (2 : ℕ) ^ b * 2 ^ (2 * q + 2 * b + 20) = 2 ^ (2 * q + 3 * b + 20) := by
        rw [← pow_add]; congr 1; ring
      have h3 : (2 : ℕ) ^ (2 * q + 3 * b + 20) ≤ 2 ^ (3 * q + 3 * b + 20) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hKK1' : K * (K + 1) + 1 ≤ 2 ^ (2 * q + 2 * b + 22) := by
      have h1 : (1 : ℕ) ≤ 2 ^ (2 * q + 2 * b + 21) := Nat.one_le_two_pow
      have h2 : (2 : ℕ) ^ (2 * q + 2 * b + 22) = 2 ^ (2 * q + 2 * b + 21) * 2 :=
        pow_succ 2 _
      omega
    have hκle : κ ≤ 2 ^ (5 * q + 5 * b + 46) := by
      have hprod : b * K ^ 2 * (K * (K + 1) + 1) ≤ 2 ^ (5 * q + 5 * b + 42) := by
        have h1 : b * K ^ 2 * (K * (K + 1) + 1)
            ≤ 2 ^ (3 * q + 3 * b + 20) * 2 ^ (2 * q + 2 * b + 22) :=
          Nat.mul_le_mul hbK2 hKK1'
        have h2 : (2 : ℕ) ^ (3 * q + 3 * b + 20) * 2 ^ (2 * q + 2 * b + 22)
            = 2 ^ (5 * q + 5 * b + 42) := by
          rw [← pow_add]; congr 1; ring
        omega
      have hκ' : κ = 6 * (b * K ^ 2) + 2 * (b * K ^ 2 * (K * (K + 1) + 1)) + (q + 7) := by
        rw [hκ]; ring
      have hq7 : q + 7 ≤ 2 ^ (q + 3) := by
        have h1 : (2 : ℕ) ^ (q + 3) = 2 ^ q * 8 := by rw [pow_add]; norm_num
        omega
      have hup1 : (2 : ℕ) ^ (3 * q + 3 * b + 20) ≤ 2 ^ (5 * q + 5 * b + 42) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hup2 : (2 : ℕ) ^ (q + 3) ≤ 2 ^ (5 * q + 5 * b + 42) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hfin : (2 : ℕ) ^ (5 * q + 5 * b + 46) = 2 ^ (5 * q + 5 * b + 42) * 16 := by
        rw [show 5 * q + 5 * b + 46 = 5 * q + 5 * b + 42 + 4 by omega, pow_add]
        norm_num
      omega
    have hEle : E ≤ 2 ^ (8 * q + 8 * b + 70) := by
      have hin : K * (K + 1) + κ + 1 ≤ 2 ^ (5 * q + 5 * b + 48) := by
        have h1 : (2 : ℕ) ^ (2 * q + 2 * b + 21) ≤ 2 ^ (5 * q + 5 * b + 46) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : (1 : ℕ) ≤ 2 ^ (5 * q + 5 * b + 46) := Nat.one_le_two_pow
        have h3 : (2 : ℕ) ^ (5 * q + 5 * b + 48) = 2 ^ (5 * q + 5 * b + 46) * 4 := by
          rw [show 5 * q + 5 * b + 48 = 5 * q + 5 * b + 46 + 2 by omega, pow_add]
          norm_num
        omega
      have h4 : E ≤ 2 ^ (3 * q + 3 * b + 20) * 2 ^ (5 * q + 5 * b + 48) := by
        rw [hE]
        exact Nat.mul_le_mul hbK2 hin
      have h5 : (2 : ℕ) ^ (3 * q + 3 * b + 20) * 2 ^ (5 * q + 5 * b + 48)
          = 2 ^ (8 * q + 8 * b + 68) := by
        rw [← pow_add]; congr 1; ring
      have h6 : (2 : ℕ) ^ (8 * q + 8 * b + 68) ≤ 2 ^ (8 * q + 8 * b + 70) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hEκ5 : E + κ + 5 ≤ 2 ^ (8 * q + 8 * b + 72) := by
      have h1 : (2 : ℕ) ^ (5 * q + 5 * b + 46) ≤ 2 ^ (8 * q + 8 * b + 70) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2a : (2 : ℕ) ^ 3 ≤ 2 ^ (8 * q + 8 * b + 70) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (5 : ℕ) ≤ 2 ^ (8 * q + 8 * b + 70) := by
        norm_num at h2a
        omega
      have h3 : (2 : ℕ) ^ (8 * q + 8 * b + 72) = 2 ^ (8 * q + 8 * b + 70) * 4 := by
        rw [show 8 * q + 8 * b + 72 = 8 * q + 8 * b + 70 + 2 by omega, pow_add]
        norm_num
      omega
    have h4q : 4 * q ≤ 2 ^ (q + 2) := by
      have h1 : (2 : ℕ) ^ (q + 2) = 2 ^ q * 4 := by rw [pow_add]; norm_num
      omega
    have hprodf : 4 * q * (E + κ + 5) ≤ 2 ^ (q + 2) * 2 ^ (8 * q + 8 * b + 72) :=
      Nat.mul_le_mul h4q hEκ5
    have hexpf : (2 : ℕ) ^ (q + 2) * 2 ^ (8 * q + 8 * b + 72)
        = 2 ^ (9 * q + 8 * b + 74) := by
      rw [← pow_add]; congr 1; ring
    have hKexp : (2 : ℕ) ^ (9 * q + 8 * b + 74) ≤ 2 ^ K := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    have hbK : (2 : ℕ) ^ K ≤ b ^ K := Nat.pow_le_pow_left hb K
    omega
  exact ⟨hgrind, hclosure, hK1, hKκpow⟩

/-- **Weighted divisor block certificates exist for every precision.**  For
every base `b ≥ 2` and every `q > 0`, explicit parameters
`K = 9(q+b+100)`, `L = 2^κ` and the bounded Bertrand/CRT frame produce a
weighted certificate `(N, K, L, C)`: first-block divisibility, weighted
middle sum ≤ `C`, and `q·(C + N + L + 2) < b^L`.  This discharges the
certificate-existence hypothesis of the weighted closure — the
divisor-average half and the size-control half of Erdős 1948, composed. -/
theorem exists_weighted_block_certificates (b : ℕ) (hb : 2 ≤ b) :
    ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
      (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ (N + r).divisors.card) ∧
      (∑ r ∈ Finset.Icc (K + 1) L, (N + r).divisors.card * b ^ (L - r) ≤ C) ∧
      q * (C + (N + L + 2)) < b ^ L := by
  intro q hq
  set K : ℕ := 9 * (q + b + 100) with hKdef
  set κ : ℕ := 3 * (2 * b * K ^ 2 + 1) + (2 * b * K ^ 2 * (K * (K + 1) + 1) + q + 4)
    with hκdef
  set E : ℕ := b * K ^ 2 * (K * (K + 1) + κ + 1) with hEdef
  obtain ⟨hparamA, hparamB, hK1, hKκpow⟩ :=
    certificate_param_arithmetic b q K κ E hb hq hKdef hκdef hEdef
  set L : ℕ := 2 ^ κ with hLdef
  clear_value K κ E L
  have hKL : K ≤ L := hKκpow
  obtain ⟨x, A, hApos, hxA, hLA, hAle, hsupp, hfirst⟩ :=
    exists_bounded_first_block_frame b L K hb hK1 hKL
  have hA2E : A ≤ 2 ^ E := by
    have h1 : L + 1 ≤ 2 ^ (κ + 1) := by
      have h1a : (2 : ℕ) ^ (κ + 1) = 2 ^ κ * 2 := pow_succ 2 κ
      omega
    have h4 : A ≤ (2 ^ (K * (K + 1) + (κ + 1))) ^ (b * K ^ 2) := by
      calc A ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (b * K ^ 2) := hAle
        _ ≤ (2 ^ (K * (K + 1)) * 2 ^ (κ + 1)) ^ (b * K ^ 2) := by
            apply Nat.pow_le_pow_left
            exact Nat.mul_le_mul_left _ h1
        _ = (2 ^ (K * (K + 1) + (κ + 1))) ^ (b * K ^ 2) := by rw [← pow_add]
    have h5 : ((2 : ℕ) ^ (K * (K + 1) + (κ + 1))) ^ (b * K ^ 2)
        = 2 ^ ((K * (K + 1) + (κ + 1)) * (b * K ^ 2)) := (pow_mul 2 _ _).symm
    have h6 : (2 : ℕ) ^ ((K * (K + 1) + (κ + 1)) * (b * K ^ 2)) ≤ 2 ^ E := by
      apply Nat.pow_le_pow_right (by norm_num)
      have h7 : E = (K * (K + 1) + (κ + 1)) * (b * K ^ 2) := by rw [hEdef]; ring
      omega
    omega
  obtain ⟨y, hyA, hWy⟩ :=
    selected_weighted_middle_of_supported_frame b x A K L A hb hApos hsupp
  refine ⟨x + y * A, K, L,
    (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + A * A + L)), (A / d + 1))) / A,
    hKL, fun r hr => hfirst y r hr, hWy, ?_⟩
  set S : ℕ := Nat.sqrt (x + A * A + L) with hSdef
  have hSle : S ≤ A + L + 1 := by
    have h1 : x + A * A + L ≤ (A + L + 1) * (A + L + 1) := by
      have hexp : (A + L + 1) * (A + L + 1)
          = A * A + (2 * (A * (L + 1)) + (L + 1) * (L + 1)) := by ring
      have h2 : A ≤ A * (L + 1) := Nat.le_mul_of_pos_right A (by omega)
      have h3 : L + 1 ≤ (L + 1) * (L + 1) :=
        Nat.le_mul_of_pos_right (L + 1) (by omega)
      omega
    have h4 : Nat.sqrt (x + A * A + L) ≤ Nat.sqrt ((A + L + 1) * (A + L + 1)) :=
      Nat.sqrt_le_sqrt h1
    rw [Nat.sqrt_eq] at h4
    rw [hSdef]
    exact h4
  have hS2A : S ≤ 2 * A := by omega
  have hSpow : S ≤ 2 ^ (E + κ + 2) := by
    have h1 : (2 : ℕ) ^ (E + κ + 2) = 2 ^ E * 2 ^ (κ + 2) := pow_add 2 E (κ + 2)
    have h2 : (4 : ℕ) ≤ 2 ^ (κ + 2) := by
      have h2a : (2 : ℕ) ^ (κ + 2) = 2 ^ κ * 4 := by rw [pow_add]; norm_num
      have h2b : (1 : ℕ) ≤ 2 ^ κ := Nat.one_le_two_pow
      omega
    have h5 : 2 ^ E * 4 ≤ 2 ^ E * 2 ^ (κ + 2) := Nat.mul_le_mul_left _ h2
    omega
  have hHle : (∑ d ∈ Finset.Icc 1 S, (A / d + 1)) ≤ A * (E + κ + 5) := by
    have h1 := harmonic_div_sum_le S A (E + κ + 2) hSpow
    have h2 : A * (E + κ + 2 + 1) + 2 * A = A * (E + κ + 5) := by ring
    omega
  have hCle : (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A / d + 1))) / A
      ≤ 2 * b ^ (L - K) * (E + κ + 5) := by
    have h1 : b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A / d + 1))
        ≤ b ^ (L - K) * (2 * (A * (E + κ + 5))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hHle)
    have h2 : b ^ (L - K) * (2 * (A * (E + κ + 5)))
        = A * (2 * b ^ (L - K) * (E + κ + 5)) := by ring
    calc (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A / d + 1))) / A
        ≤ (A * (2 * b ^ (L - K) * (E + κ + 5))) / A := by
          apply Nat.div_le_div_right
          omega
      _ = 2 * b ^ (L - K) * (E + κ + 5) := Nat.mul_div_cancel_left _ hApos
  have hNle : x + y * A + L + 2 ≤ A * A + L + 2 := by
    have h1 : y * A ≤ (A - 1) * A := Nat.mul_le_mul_right A (by omega)
    have h3 : (A - 1) * A = A * A - A := Nat.sub_one_mul A A
    have h4 : A ≤ A * A := Nat.le_mul_of_pos_left A hApos
    omega
  have hhalf1 : 2 * (q * (2 * b ^ (L - K) * (E + κ + 5))) ≤ b ^ L := by
    have h1 : 2 * (q * (2 * b ^ (L - K) * (E + κ + 5)))
        = (4 * q * (E + κ + 5)) * b ^ (L - K) := by ring
    have h2 : (4 * q * (E + κ + 5)) * b ^ (L - K) ≤ b ^ K * b ^ (L - K) :=
      Nat.mul_le_mul_right _ hparamA
    have h3 : b ^ K * b ^ (L - K) = b ^ (K + (L - K)) := (pow_add b K (L - K)).symm
    have h4 : K + (L - K) = L := Nat.add_sub_cancel' hKL
    rw [h1]
    rw [h3, h4] at h2
    exact h2
  have hhalf2 : 2 * (q * (A * A + L + 2)) < b ^ L := by
    have hA2 : A * A ≤ 2 ^ (2 * E) := by
      have h1 : A * A ≤ 2 ^ E * 2 ^ E := Nat.mul_le_mul hA2E hA2E
      have h2 : (2 : ℕ) ^ E * 2 ^ E = 2 ^ (2 * E) := by
        rw [← pow_add]; congr 1; ring
      omega
    have hsum : A * A + L + 2 ≤ 2 ^ (2 * E + κ + 2) := by
      have hex : (2 : ℕ) ^ (2 * E + κ + 2) = 2 ^ (2 * E) * 2 ^ κ * 4 := by
        rw [pow_add, pow_add]; norm_num
      have hac1 : (2 : ℕ) ^ (2 * E) ≤ 2 ^ (2 * E) * 2 ^ κ :=
        Nat.le_mul_of_pos_right _ (by positivity)
      have hac2 : (2 : ℕ) ^ κ ≤ 2 ^ (2 * E) * 2 ^ κ :=
        Nat.le_mul_of_pos_left _ (by positivity)
      omega
    have h2q : 2 * q ≤ 2 ^ (q + 1) := by
      have h1 : q < 2 ^ q := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (q + 1) = 2 ^ q * 2 := pow_succ 2 q
      omega
    have hmul : 2 * (q * (A * A + L + 2)) ≤ 2 ^ (q + 1) * 2 ^ (2 * E + κ + 2) := by
      have h1 : 2 * (q * (A * A + L + 2)) = (2 * q) * (A * A + L + 2) := by ring
      rw [h1]
      exact Nat.mul_le_mul h2q hsum
    have hexp : (2 : ℕ) ^ (q + 1) * 2 ^ (2 * E + κ + 2) = 2 ^ (2 * E + κ + q + 3) := by
      rw [← pow_add]; congr 1; ring
    have hlt : (2 : ℕ) ^ (2 * E + κ + q + 3) * 2 ≤ 2 ^ L := by
      have h1 : (2 : ℕ) ^ (2 * E + κ + q + 3) * 2 = 2 ^ (2 * E + κ + q + 4) :=
        (pow_succ 2 _).symm
      rw [h1]
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    have ht1 : (1 : ℕ) ≤ 2 ^ (2 * E + κ + q + 3) := Nat.one_le_two_pow
    have h2L : (2 : ℕ) ^ L ≤ b ^ L := Nat.pow_le_pow_left hb L
    omega
  have hqC : q * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A / d + 1))) / A)
      ≤ q * (2 * b ^ (L - K) * (E + κ + 5)) := Nat.mul_le_mul_left q hCle
  have hqN : q * (x + y * A + L + 2) ≤ q * (A * A + L + 2) :=
    Nat.mul_le_mul_left q hNle
  have hdist : q * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A / d + 1))) / A
        + (x + y * A + L + 2))
      = q * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A / d + 1))) / A)
        + q * (x + y * A + L + 2) := by ring
  omega

/-- **Full-support (Erdős–Borwein) irrationality, unconditional.**  For every
base `b ≥ 2` the series `∑_{n≥1} 1/(b^n - 1)` is irrational — Erdős (1948),
through the certificate machine: bounded Bertrand/CRT first-block frame,
middle-window divisor-pair average with pigeonhole selection, and explicit
parameter closure. -/
theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) :=
  irrational_erdosSum_full_support_of_weighted_block_certificates b hb
    (exists_weighted_block_certificates b hb)

/-- **The Erdős–Borwein constant is irrational.**  Base-2 instance of the
full-support theorem: `∑_{n≥1} 1/(2^n - 1)` is irrational. -/
theorem irrational_erdosBorwein_series :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) - 1)) := by
  have h := irrational_erdosSum_full_support 2 (by norm_num)
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rwa [hcast] at h

/-! ## Support-coefficient calculus (wave 8)

The full-support theorem `irrational_erdosSum_full_support` is a statement
about the coefficient `τ(n) = n.divisors.card`.  Erdős #257 is a statement
about the coefficient `f_A(n) = #{d ∣ n : d ∈ A}` for an arbitrary support
`A ⊆ ℕ` — the Dirichlet incidence `1_A * 1`.  This section factors the
landed proof into that language: a *generic* weighted-coefficient
certificate engine (any `c : ℕ → ℕ` with `c m ≤ m`), a weighted Lambert
transform, the support coefficient `supportCoeff`, and the support series
`erdosSupportSeries`.  Full support is recovered as the `A = Set.univ`
instance; the multiples supports `A = dℕ` land as the first non-trivial
support classes.  Arbitrary-support Erdős #257 is NOT claimed: for a
general infinite `A`, certificate existence for `supportCoeff A` is an
open obligation, isolated here as an explicit hypothesis. -/

/-- Summability of a coefficient series `∑ c(m+1) / b^(m+1)` under the
linear growth envelope `c m ≤ m`: comparison against `∑ m · (1/b)^m`. -/
theorem summable_coeff_term (b : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b)
    (hgrowth : ∀ m : ℕ, c m ≤ m) :
    Summable (fun m : ℕ => ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hr : ‖(1 : ℝ) / (b : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one hb_pos]
    linarith
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ 1 * ((1 : ℝ) / b) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hshift : Summable
      (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 1 * ((1 : ℝ) / b) ^ (m + 1)) :=
    (summable_nat_add_iff 1).mpr hgeo
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hshift
  have hc : ((c (m + 1) : ℝ)) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hgrowth (m + 1)
  have hpow : ((1 : ℝ) / b) ^ (m + 1) = 1 / (b : ℝ) ^ (m + 1) := by
    rw [div_pow, one_pow]
  calc ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)
      = ((c (m + 1) : ℝ)) * (1 / (b : ℝ) ^ (m + 1)) := (mul_one_div _ _).symm
    _ ≤ ((m + 1 : ℕ) : ℝ) * (1 / (b : ℝ) ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = ((m + 1 : ℕ) : ℝ) ^ 1 * ((1 : ℝ) / b) ^ (m + 1) := by
        rw [pow_one, hpow]

/-- Summability of the shifted coefficient tail `∑_r c(N+r+1) / b^(r+1)`
under the growth envelope. -/
theorem summable_coeff_shift_tail (b N : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b)
    (hgrowth : ∀ m : ℕ, c m ≤ m) :
    Summable (fun r : ℕ => ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hbase := summable_coeff_term b c hb hgrowth
  have hshift : Summable
      (fun r : ℕ => ((c (r + N + 1) : ℝ)) / (b : ℝ) ^ (r + N + 1)) :=
    (summable_nat_add_iff N).mpr hbase
  have hmul := hshift.mul_left ((b : ℝ) ^ N)
  refine hmul.congr fun r => ?_
  rw [show r + N + 1 = N + r + 1 from by omega]
  have hsplit : (b : ℝ) ^ (N + r + 1) = (b : ℝ) ^ N * (b : ℝ) ^ (r + 1) := by ring
  rw [hsplit]
  field_simp

/-- **Generic shifted-tail decomposition.**  Dilating a coefficient series
by `b^N` splits it into an integer plus the shifted tail — the base-`b`
carry skeleton, for an arbitrary coefficient sequence. -/
theorem bpow_mul_coeff_series_eq_int_add_tail (b N : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b)
    (hgrowth : ∀ m : ℕ, c m ≤ m) :
    ∃ z : ℤ,
      (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) =
        (z : ℝ) + ∑' r : ℕ, ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hsum := summable_coeff_term b c hb hgrowth
  refine ⟨((∑ i ∈ Finset.range N, c (i + 1) * b ^ (N - (i + 1)) : ℕ) : ℤ), ?_⟩
  rw [← Summable.sum_add_tsum_nat_add N hsum, mul_add]
  congr 1
  · push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiN : i < N := Finset.mem_range.mp hi
    have hsplit : (b : ℝ) ^ N = (b : ℝ) ^ (N - (i + 1)) * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    field_simp
  · rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [show r + N + 1 = N + r + 1 from by omega]
    have hsplit : (b : ℝ) ^ (N + r + 1) = (b : ℝ) ^ N * (b : ℝ) ^ (r + 1) := by ring
    rw [hsplit]
    field_simp

/-- **Generic crude far-tail bound.**  Past index `L`, the growth envelope
`c m ≤ m` and the linear-times-geometric sum give
`∑_t c(N+L+1+t) / b^(L+1+t) ≤ (N+L+2) / b^L`. -/
theorem coeff_far_tail_le (b N L : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b)
    (hgrowth : ∀ m : ℕ, c m ≤ m) :
    ∑' t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t)
      ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hx0 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hx1 : 1 / (b : ℝ) < 1 := by
    rw [div_lt_one hb_pos]
    linarith
  have hx2 : 1 / (b : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · exact hb2
  have hshift := summable_coeff_shift_tail b (N + L) c hb hgrowth
  have hLHS_sum : Summable
      (fun t : ℕ => ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t)) := by
    have hmul := hshift.mul_left ((1 : ℝ) / (b : ℝ) ^ L)
    refine hmul.congr fun t => ?_
    rw [show N + L + t + 1 = N + L + 1 + t from by omega]
    have hsplit : (b : ℝ) ^ (L + 1 + t) = (b : ℝ) ^ L * (b : ℝ) ^ (t + 1) := by ring
    rw [hsplit]
    field_simp
  have hcmp_sum : Summable
      (fun t : ℕ => ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
        (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t) := by
    have := (summable_const_add_mul_geometric (N + L + 1) hx0 hx1).mul_left
      ((1 : ℝ) / (b : ℝ) ^ (L + 1))
    refine this.congr fun t => ?_
    ring
  have hle : ∀ t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t)
      ≤ ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
        (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t := by
    intro t
    have hc : ((c (N + L + 1 + t) : ℝ)) ≤ ((N + L + 1 + t : ℕ) : ℝ) := by
      exact_mod_cast hgrowth (N + L + 1 + t)
    have hpow : (b : ℝ) ^ (L + 1 + t) = (b : ℝ) ^ (L + 1) * (b : ℝ) ^ t := by ring
    calc ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t)
        ≤ ((N + L + 1 + t : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + t) := by gcongr
      _ = ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
            (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t := by
          rw [hpow]
          push_cast
          rw [div_pow, one_pow]
          field_simp
  calc (∑' t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t))
      ≤ ∑' t : ℕ, ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
          (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t :=
        Summable.tsum_le_tsum hle hLHS_sum hcmp_sum
    _ = ((1 : ℝ) / (b : ℝ) ^ (L + 1)) *
          ∑' t : ℕ, (((N + L + 1 : ℕ) : ℝ) + (t : ℝ)) * ((1 : ℝ) / (b : ℝ)) ^ t := by
        rw [← tsum_mul_left]
        exact tsum_congr fun t => by ring
    _ ≤ ((1 : ℝ) / (b : ℝ) ^ (L + 1)) * (2 * ((N + L + 1 : ℕ) : ℝ) + 2) := by
        apply mul_le_mul_of_nonneg_left
          (tsum_const_add_mul_geometric_le (N + L + 1) hx0 hx2) (by positivity)
    _ ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
        have hP : (0 : ℝ) < (b : ℝ) ^ L := by positivity
        have hS : (0 : ℝ) ≤ (N : ℝ) + (L : ℝ) + 2 := by positivity
        push_cast
        rw [pow_succ, one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) hP]
        nlinarith [mul_nonneg (mul_nonneg hS hP.le) (by linarith : (0 : ℝ) ≤ (b : ℝ) - 2)]

/-- **Generic weighted-coefficient certificate consumer, one-sided.**  A
weighted block certificate `(N, K, L, C)` for an arbitrary coefficient
sequence `c : ℕ → ℕ` with growth envelope `c m ≤ m` — first-block
divisibility `b^r ∣ c(N+r)`, weighted middle sum ≤ `C`, a nonzero
coefficient somewhere past the window, and the ℕ-arithmetic inequality —
yields a *one-sided* near-integer witness: the `b^N`-dilated coefficient
series exceeds an integer by strictly between `0` and `1/q`.  This is the
τ-free abstraction of `near_int_witness_of_weighted_divisor_block_certificate`;
the one-sided form exposes the digit/carry content (the dilated series has
a positive fractional part below `1/q`), which the absolute-value form
hides. -/
theorem near_int_witness_of_weighted_coeff_block_certificate
    (b q N K L C : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hblock : ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ c (N + r))
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C)
    (hpos : ∃ t : ℕ, 0 < c (N + L + 1 + t))
    (harith : q * (C + (N + L + 2)) < b ^ L) :
    ∃ z : ℤ,
      0 < (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ) ∧
        (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ) < 1 / (q : ℝ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨z₀, hz₀⟩ := bpow_mul_coeff_series_eq_int_add_tail b N c hb hgrowth
  have hfsum : Summable
      (fun r : ℕ => ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1)) :=
    summable_coeff_shift_tail b N c hb hgrowth
  have hfarsum : Summable
      (fun t : ℕ => ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) :=
    (summable_nat_add_iff L).mpr hfsum
  -- split the tail at L
  have hsplitL : (∑' r : ℕ, ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  -- split the finite part at K
  have hsplitK : (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  -- the first block is an integer
  set z₁ : ℕ := ∑ i ∈ Finset.range K, c (N + i + 1) / b ^ (i + 1) with hz₁def
  have hz₁ : ((z₁ : ℕ) : ℝ)
      = ∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [hz₁def]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp hi
    have hdvd : b ^ (i + 1) ∣ c (N + i + 1) :=
      hblock (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hbpow0 : ((b ^ (i + 1) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_div hdvd hbpow0]
    push_cast
    ring
  -- remainder positivity: some coefficient past the window is nonzero
  have hmid_nonneg : (0 : ℝ)
      ≤ ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨t₀, ht₀⟩ := hpos
  have hfar_pos : (0 : ℝ)
      < ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    have hcpos : (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) := by
      have hidx : N + (t₀ + L) + 1 = N + L + 1 + t₀ := by omega
      have h0 : 0 < c (N + (t₀ + L) + 1) := by rw [hidx]; exact ht₀
      exact_mod_cast h0
    have hterm0 : (0 : ℝ)
        < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := by positivity
    calc (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := hterm0
      _ ≤ _ := hfarsum.le_tsum t₀ fun j _ => by positivity
  -- middle window: exact weighted sum over the common denominator b^L
  have hterm : ∀ i ∈ Finset.Ico K L,
      ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1)
        = ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    intro i hi
    obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
    have hb1 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
    have hbL' : ((b : ℝ) ^ L) ≠ 0 := by positivity
    have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (L - (i + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_div_iff hb1 hbL']
    push_cast
    rw [hsplit]
    ring
  have hreindex : (∑ i ∈ Finset.Ico K L, c (N + i + 1) * b ^ (L - (i + 1)))
      = ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) := by
    have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hn : L + 1 - (K + 1) = L - K := by omega
    rw [hn]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : N + (K + j) + 1 = N + (K + 1 + j) := by omega
    have h2 : L - (K + j + 1) = L - (K + 1 + j) := by omega
    rw [h1, h2]
  have hmid : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      ≤ (C : ℝ) / (b : ℝ) ^ L := by
    have hsum_eq : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    have hnum : (∑ i ∈ Finset.Ico K L,
        ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) ≤ (C : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hreindex.trans_le hmiddle
    calc (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := hsum_eq
      _ ≤ (C : ℝ) / (b : ℝ) ^ L := by gcongr
  -- far tail bound, reshaped from the generic far-tail lemma
  have hfar_eq : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact coeff_far_tail_le b N L c hb hgrowth
  -- assemble the one-sided witness
  have hdiff : (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
      - ((z₀ + (z₁ : ℤ) : ℤ) : ℝ)
      = (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    rw [hz₀, hsplitL, hsplitK]
    push_cast
    rw [← hz₁]
    ring
  have hR_pos : (0 : ℝ)
      < (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    add_pos_of_nonneg_of_pos hmid_nonneg hfar_pos
  refine ⟨z₀ + (z₁ : ℤ), ?_, ?_⟩
  · rw [hdiff]
    exact hR_pos
  · rw [hdiff]
    have hsum_le : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
        ≤ (C : ℝ) / (b : ℝ) ^ L + ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L :=
      add_le_add hmid hfar
    refine lt_of_le_of_lt hsum_le ?_
    have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    have hc : (q : ℝ) * ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) < (b : ℝ) ^ L := by
      exact_mod_cast harith
    rw [← add_div, div_lt_div_iff₀ hbL hq', one_mul]
    calc ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) * (q : ℝ)
        = (q : ℝ) * ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) := mul_comm _ _
      _ < (b : ℝ) ^ L := hc

/-- **Generic coefficient-series irrationality from weighted certificates.**
If an arbitrary coefficient sequence `c : ℕ → ℕ` with growth envelope
`c m ≤ m` admits a weighted block certificate for every precision `q`,
then `∑ c(m) / b^m` is irrational.  The full-support theorem is the
instance `c = τ`; arbitrary-support Erdős #257 is the instance
`c = supportCoeff A`, whose certificate existence is NOT claimed here. -/
theorem irrational_coeff_series_of_weighted_coeff_block_certificates
    (b : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ c (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < c (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  apply irrational_of_pow_mul_near_int b
  intro q hq
  obtain ⟨N, K, L, C, hKL, hblock, hmiddle, hpos, harith⟩ := hcert q hq
  obtain ⟨z, hz_pos, hz_lt⟩ := near_int_witness_of_weighted_coeff_block_certificate
    b q N K L C c hb hq hKL hgrowth hblock hmiddle hpos harith
  refine ⟨N, z, ?_, ?_⟩
  · rw [abs_of_pos hz_pos]
    exact hz_pos
  · rw [abs_of_pos hz_pos]
    exact hz_lt

/-- **The coefficient engine subsumes the landed full-support theorem.**
Re-derivation of `irrational_erdosSum_full_support` through the generic
weighted-coefficient engine at `c = τ`: growth is `τ(m) ≤ m`, certificates
are the landed `exists_weighted_block_certificates`, and tail positivity
is `τ ≥ 1`.  This machine-checks that the abstraction loses nothing. -/
theorem irrational_erdosSum_full_support_via_coeff_engine (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := by
  rw [erdosSum_full_support_eq_tsum_divisor_count b hb]
  refine irrational_coeff_series_of_weighted_coeff_block_certificates b
    (fun m => m.divisors.card) hb (fun m => Nat.card_divisors_le_self m) ?_
  intro q hq
  obtain ⟨N, K, L, C, hKL, hblock, hmiddle, harith⟩ :=
    exists_weighted_block_certificates b hb q hq
  refine ⟨N, K, L, C, hKL, hblock, hmiddle, ⟨0, ?_⟩, harith⟩
  have hne : N + L + 1 + 0 ≠ 0 := by omega
  exact Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hne)

/-- **One-sided near-integer witnesses for the full-support series.**  For
every base `b ≥ 2` and every precision `q`, some `b^N`-dilation of
`∑_{n≥1} 1/(b^n - 1)` exceeds an integer by strictly between `0` and
`1/q`.  This is the digit/carry content of Erdős's 1948 construction made
explicit: the landed irrationality theorem is its corollary, but the
witnesses themselves say more — the dilated series has arbitrarily small
positive fractional part. -/
theorem near_int_witnesses_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    ∀ q : ℕ, 0 < q → ∃ (N : ℕ) (z : ℤ),
      0 < (b : ℝ) ^ N * (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) - (z : ℝ) ∧
        (b : ℝ) ^ N * (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) - (z : ℝ)
          < 1 / (q : ℝ) := by
  intro q hq
  rw [erdosSum_full_support_eq_tsum_divisor_count b hb]
  obtain ⟨N, K, L, C, hKL, hblock, hmiddle, harith⟩ :=
    exists_weighted_block_certificates b hb q hq
  have hpos : ∃ t : ℕ, 0 < (fun m => m.divisors.card) (N + L + 1 + t) := by
    refine ⟨0, ?_⟩
    have hne : N + L + 1 + 0 ≠ 0 := by omega
    exact Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hne)
  obtain ⟨z, hz_pos, hz_lt⟩ := near_int_witness_of_weighted_coeff_block_certificate
    b q N K L C (fun m => m.divisors.card) hb hq hKL
    (fun m => Nat.card_divisors_le_self m) hblock hmiddle hpos harith
  exact ⟨N, z, hz_pos, hz_lt⟩

/-- **Arbitrarily long zero blocks after the leading digit window.**  For
every base `b ≥ 2` and every window length `K`, some `b^N`-dilation of
`∑_{n≥1} 1/(b^n - 1)` exceeds an integer by strictly between `0` and
`b^(-K)` — so the base-`b` expansion of the full-support series contains
arbitrarily long blocks of zero digits.  Specialisation `q = b^K` of the
one-sided witness family. -/
theorem zero_block_witnesses_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    ∀ K : ℕ, ∃ (N : ℕ) (z : ℤ),
      0 < (b : ℝ) ^ N * (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) - (z : ℝ) ∧
        (b : ℝ) ^ N * (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) - (z : ℝ)
          < 1 / (b : ℝ) ^ K := by
  intro K
  have hbK : 0 < b ^ K := pow_pos (by omega : 0 < b) K
  obtain ⟨N, z, hz_pos, hz_lt⟩ :=
    near_int_witnesses_erdosSum_full_support b hb (b ^ K) hbK
  refine ⟨N, z, hz_pos, ?_⟩
  have hcast : ((b ^ K : ℕ) : ℝ) = (b : ℝ) ^ K := by push_cast; rfl
  rw [← hcast]
  exact hz_lt

/-! ## Support-coefficient calculus: the weighted Lambert transform -/

/-- **Weighted product-to-divisor-sum rearrangement.**  For a weight
`w : ℕ → ℝ` with `0 ≤ w ≤ 1` and `0 ≤ r < 1`, the double series
`∑_{d,m ≥ 1} w(d)·r^(dm)` regroups along divisor antidiagonals into
`∑_{n ≥ 1} (∑_{e ∣ n} w(e))·r^n`.  Weighted analogue of Mathlib's
`tsum_prod_pow_eq_tsum_sigma`, with the weight on the divisor factor. -/
theorem tsum_prod_weight_mul_pow_eq_tsum_divisor_weight_sum
    (w : ℕ → ℝ) (hw0 : ∀ e : ℕ, 0 ≤ w e) (hw1 : ∀ e : ℕ, w e ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e) * r ^ (n : ℕ) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hgeom : Summable (fun p : ℕ+ × ℕ+ => r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
    have hbase := summable_prod_mul_pow (𝕜 := ℝ) 0 hnorm
    refine hbase.congr fun p => ?_
    simp
  have hprod : Summable
      (fun p : ℕ+ × ℕ+ => w (p.1 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
    refine Summable.of_nonneg_of_le
      (fun p => mul_nonneg (hw0 _) (pow_nonneg hr0 _)) (fun p => ?_) hgeom
    calc w (p.1 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul_of_nonneg_right (hw1 _) (pow_nonneg hr0 _)
      _ = r ^ ((p.1 : ℕ) * (p.2 : ℕ)) := one_mul _
  have hsig : Summable
      (fun x : (Σ n : ℕ+, {y // y ∈ ((n : ℕ)).divisorsAntidiagonal}) =>
        w x.2.1.1 * r ^ (x.2.1.1 * x.2.1.2)) := by
    have h := (Equiv.summable_iff sigmaAntidiagonalEquivProd).mpr hprod
    refine h.congr fun x => ?_
    rcases x with ⟨n, ⟨⟨a, e⟩, hae⟩⟩
    simp [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]
  calc ∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))
      = ∑' x : (Σ n : ℕ+, {y // y ∈ ((n : ℕ)).divisorsAntidiagonal}),
          w x.2.1.1 * r ^ (x.2.1.1 * x.2.1.2) := by
        rw [← sigmaAntidiagonalEquivProd.tsum_eq
          (f := fun p : ℕ+ × ℕ+ => w (p.1 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ)))]
        refine tsum_congr fun x => ?_
        rcases x with ⟨n, ⟨⟨a, e⟩, hae⟩⟩
        simp [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]
    _ = ∑' n : ℕ+, ∑' y : {y // y ∈ ((n : ℕ)).divisorsAntidiagonal},
          w y.1.1 * r ^ (y.1.1 * y.1.2) := Summable.tsum_sigma hsig
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e) * r ^ (n : ℕ) := by
        refine tsum_congr fun n => ?_
        rw [tsum_fintype, Finset.univ_eq_attach,
          Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
            (fun y : ℕ × ℕ => w y.1 * r ^ (y.1 * y.2)),
          Nat.sum_divisorsAntidiagonal (fun d e => w d * r ^ (d * e))]
        have hstep : ∀ d ∈ (n : ℕ).divisors,
            w d * r ^ (d * ((n : ℕ) / d)) = w d * r ^ (n : ℕ) := by
          intro d hd
          rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
        rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]

/-- **Weighted Lambert series identity.**  For a weight `w : ℕ → ℝ` with
`0 ≤ w ≤ 1` and `0 ≤ r < 1`:
`∑_{d≥1} w(d)·r^d/(1-r^d) = ∑_{n≥1} (∑_{e ∣ n} w(e))·r^n`.
At `w ≡ 1` this is the classical `τ` Lambert identity; at
`w = 1_A` it is the arbitrary-support transform of Erdős #257. -/
theorem weighted_lambert_series_identity
    (w : ℕ → ℝ) (hw0 : ∀ e : ℕ, 0 ≤ w e) (hw1 : ∀ e : ℕ, w e ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)))
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e) * r ^ (n : ℕ) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hgeom : Summable (fun p : ℕ+ × ℕ+ => r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
    have hbase := summable_prod_mul_pow (𝕜 := ℝ) 0 hnorm
    refine hbase.congr fun p => ?_
    simp
  have hprod : Summable
      (fun p : ℕ+ × ℕ+ => w (p.1 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
    refine Summable.of_nonneg_of_le
      (fun p => mul_nonneg (hw0 _) (pow_nonneg hr0 _)) (fun p => ?_) hgeom
    calc w (p.1 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul_of_nonneg_right (hw1 _) (pow_nonneg hr0 _)
      _ = r ^ ((p.1 : ℕ) * (p.2 : ℕ)) := one_mul _
  have hterm : ∀ d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)))
      = ∑' m : ℕ+, w (d : ℕ) * r ^ ((d : ℕ) * (m : ℕ)) := by
    intro d
    have hd0 : (d : ℕ) ≠ 0 := d.pos.ne'
    have hrd : ‖r ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]) hnorm hd0
    have hgeo := tsum_geometric_of_norm_lt_one hrd
    have h1 : r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) = ∑' j : ℕ, (r ^ (d : ℕ)) ^ (j + 1) := by
      rw [div_eq_mul_inv, ← hgeo, ← tsum_mul_left]
      exact tsum_congr fun j => (pow_succ' _ _).symm
    rw [h1, ← tsum_mul_left,
      ← tsum_pnat_eq_tsum_succ (f := fun j : ℕ => w (d : ℕ) * (r ^ (d : ℕ)) ^ j)]
    exact tsum_congr fun m => by rw [← pow_mul]
  calc ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)))
      = ∑' d : ℕ+, ∑' m : ℕ+, w (d : ℕ) * r ^ ((d : ℕ) * (m : ℕ)) :=
        tsum_congr hterm
    _ = ∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
        (hprod.tsum_prod).symm
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e) * r ^ (n : ℕ) :=
        tsum_prod_weight_mul_pow_eq_tsum_divisor_weight_sum w hw0 hw1 hr0 hr1

/-! ## Support-coefficient calculus: supportCoeff and erdosSupportSeries -/

/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet
incidence `1_A * 1` of a support set `A ⊆ ℕ`.  This is the coefficient
in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1)
= ∑_n f_A(n)/b^n`.  Full support gives `f_ℕ = τ`; primes give `ω`;
prime powers give `Ω`. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

theorem supportCoeff_le_card_divisors (A : Set ℕ) (n : ℕ) :
    supportCoeff A n ≤ n.divisors.card := by
  classical
  unfold supportCoeff
  exact Finset.card_filter_le _ _

/-- Growth envelope for the support coefficient: `f_A(n) ≤ τ(n) ≤ n`.
This is exactly the hypothesis the generic coefficient engine needs. -/
theorem supportCoeff_le_self (A : Set ℕ) (n : ℕ) : supportCoeff A n ≤ n :=
  le_trans (supportCoeff_le_card_divisors A n) (Nat.card_divisors_le_self n)

/-- **Full support recovers the divisor count**: `f_ℕ = τ`.  The landed
full-support theorem is the `A = Set.univ` instance of the support
calculus. -/
theorem supportCoeff_univ_eq_card_divisors (n : ℕ) :
    supportCoeff Set.univ n = n.divisors.card := by
  unfold supportCoeff
  simp

/-- Cast bridge: the support coefficient is the divisor sum of the real
indicator weight `1_A`. -/
theorem supportCoeff_cast_eq_sum_indicator (A : Set ℕ) (n : ℕ) :
    ((supportCoeff A n : ℕ) : ℝ)
      = ∑ e ∈ n.divisors, Set.indicator A (fun _ => (1 : ℝ)) e := by
  classical
  unfold supportCoeff
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : e ∈ A
  · simp [h]
  · simp [h]

/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an
indicator series over ℕ.  The `a = 0` term is `1/(1-1) = 0` under real
division-by-zero conventions, so supports containing `0` contribute
nothing spurious. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

/-- Summability of the support-series terms, uniformly in `A`: dominated
by the geometric envelope `2·(1/b)^a`. -/
theorem summable_erdosSupport_indicator (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) :
    Summable (fun a : ℕ =>
      Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  have hgeo : Summable (fun a : ℕ => 2 * ((1 : ℝ) / b) ^ a) :=
    (summable_geometric_of_lt_one (by positivity)
      (by rw [div_lt_one hb_pos]; linarith)).mul_left 2
  refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) hgeo
  · refine Set.indicator_nonneg (fun a _ => ?_) a
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      simp
    · have h1 : (1 : ℝ) < (b : ℝ) ^ a := one_lt_pow₀ hb1 (by omega)
      exact (div_pos one_pos (by linarith)).le
  · by_cases hA : a ∈ A
    · rw [Set.indicator_of_mem hA]
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0
        simp
      · have hba : (2 : ℝ) ≤ (b : ℝ) ^ a := by
          calc (2 : ℝ) ≤ (b : ℝ) := hb2
            _ = (b : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (b : ℝ) ^ a := pow_le_pow_right₀ (by linarith) (by omega)
        have hpow : ((1 : ℝ) / b) ^ a = 1 / (b : ℝ) ^ a := by
          rw [div_pow, one_pow]
        rw [hpow, mul_one_div]
        rw [div_le_div_iff₀ (by linarith) (by positivity)]
        linarith
    · rw [Set.indicator_of_notMem hA]
      positivity

/-- **Full support instance of the support series**: at `A = Set.univ` the
support series is the full-support (Erdős–Borwein shape) series. -/
theorem erdosSupportSeries_univ_eq_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    erdosSupportSeries b Set.univ
      = ∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1) := by
  unfold erdosSupportSeries
  have hsum := summable_erdosSupport_indicator b Set.univ hb
  rw [hsum.tsum_eq_zero_add]
  simp

/-- **The arbitrary-support Lambert transform of Erdős #257.**  For every
base `b ≥ 2` and every support `A ⊆ ℕ`:
`∑_{a ∈ A} 1/(b^a - 1) = ∑_{n ≥ 1} f_A(n)/b^n`, where
`f_A = supportCoeff A` counts divisors lying in `A`.  This moves the
arbitrary-support problem into the coefficient language where the
weighted certificate engine operates.  Full support (`A = ℕ`, `f_A = τ`)
recovers `erdosSum_full_support_eq_tsum_divisor_count`. -/
theorem erdosSupportSeries_eq_tsum_supportCoeff (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) :
    erdosSupportSeries b A
      = ∑' m : ℕ, ((supportCoeff A (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hr1 : 1 / (b : ℝ) < 1 := by
    rw [div_lt_one hb_pos]
    linarith
  set w : ℕ → ℝ := Set.indicator A (fun _ => (1 : ℝ)) with hwdef
  have hw0 : ∀ e : ℕ, 0 ≤ w e := fun e =>
    Set.indicator_nonneg (fun _ _ => by norm_num) e
  have hw1 : ∀ e : ℕ, w e ≤ 1 := by
    intro e
    by_cases h : e ∈ A
    · rw [hwdef, Set.indicator_of_mem h]
    · rw [hwdef, Set.indicator_of_notMem h]
      norm_num
  -- the kernel's per-index Lambert term identity, junk-safe at 0
  have hterm_eq : ∀ a : ℕ, 0 < a →
      ((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a) = 1 / ((b : ℝ) ^ a - 1) := by
    intro a ha
    have hbn : (1 : ℝ) < (b : ℝ) ^ a := one_lt_pow₀ hb1 (by omega)
    have hbn0 : (b : ℝ) ^ a ≠ 0 := by positivity
    have hbn1 : (b : ℝ) ^ a - 1 ≠ 0 := ne_of_gt (by linarith)
    have h1X : (1 : ℝ) - 1 / (b : ℝ) ^ a ≠ 0 := by
      have hEq : (1 : ℝ) - 1 / (b : ℝ) ^ a = ((b : ℝ) ^ a - 1) / (b : ℝ) ^ a := by
        field_simp
      rw [hEq]
      exact div_ne_zero hbn1 hbn0
    rw [div_pow, one_pow]
    field_simp
  -- pointwise: the indicator series terms ARE the weighted Lambert terms
  have hpoint : ∀ a : ℕ,
      Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
        = w a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a)) := by
    intro a
    by_cases hA : a ∈ A
    · rw [Set.indicator_of_mem hA, hwdef, Set.indicator_of_mem hA, one_mul]
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0
        norm_num
      · rw [hterm_eq a hpos]
    · rw [Set.indicator_of_notMem hA, hwdef, Set.indicator_of_notMem hA, zero_mul]
  have hsum : Summable (fun a : ℕ =>
      w a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a))) :=
    (summable_erdosSupport_indicator b A hb).congr hpoint
  calc erdosSupportSeries b A
      = ∑' a : ℕ, w a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a)) := by
        unfold erdosSupportSeries
        exact tsum_congr hpoint
    _ = w 0 * (((1 : ℝ) / b) ^ 0 / (1 - ((1 : ℝ) / b) ^ 0))
          + ∑' m : ℕ, w (m + 1)
            * (((1 : ℝ) / b) ^ (m + 1) / (1 - ((1 : ℝ) / b) ^ (m + 1))) :=
        hsum.tsum_eq_zero_add
    _ = ∑' m : ℕ, w (m + 1)
          * (((1 : ℝ) / b) ^ (m + 1) / (1 - ((1 : ℝ) / b) ^ (m + 1))) := by
        simp
    _ = ∑' d : ℕ+, w (d : ℕ)
          * (((1 : ℝ) / b) ^ (d : ℕ) / (1 - ((1 : ℝ) / b) ^ (d : ℕ))) :=
        (tsum_pnat_eq_tsum_succ (f := fun a : ℕ =>
          w a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a)))).symm
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e) * ((1 : ℝ) / b) ^ (n : ℕ) :=
        weighted_lambert_series_identity w hw0 hw1 hr0 hr1
    _ = ∑' n : ℕ+, ((supportCoeff A (n : ℕ) : ℝ)) / (b : ℝ) ^ (n : ℕ) := by
        refine tsum_congr fun n => ?_
        rw [← supportCoeff_cast_eq_sum_indicator, div_pow, one_pow, mul_one_div]
    _ = ∑' m : ℕ, ((supportCoeff A (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1) :=
        tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
          ((supportCoeff A n : ℝ)) / (b : ℝ) ^ n)

/-- **Arbitrary-support irrationality from weighted coefficient
certificates.**  If the support coefficient `f_A` admits a weighted block
certificate for every precision, the support series
`∑_{a ∈ A} 1/(b^a - 1)` is irrational.  This is the engine Erdős #257
needs: the analytic content is reduced to certificate existence for
`f_A`, which for arbitrary infinite `A` remains an OPEN obligation —
this theorem does NOT resolve it. -/
theorem irrational_erdosSupportSeries_of_weighted_coeff_certificates
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ supportCoeff A (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, supportCoeff A (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < supportCoeff A (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (erdosSupportSeries b A) := by
  rw [erdosSupportSeries_eq_tsum_supportCoeff b A hb]
  exact irrational_coeff_series_of_weighted_coeff_block_certificates b
    (supportCoeff A) hb (supportCoeff_le_self A) hcert

/-- **Full support, in the support-series language**: the `A = Set.univ`
member of the Erdős #257 statement family is irrational. -/
theorem irrational_erdosSupportSeries_univ (b : ℕ) (hb : 2 ≤ b) :
    Irrational (erdosSupportSeries b Set.univ) := by
  rw [erdosSupportSeries_univ_eq_erdosSum_full_support b hb]
  exact irrational_erdosSum_full_support b hb

/-! ## Support-coefficient calculus: multiples supports `A = dℕ` -/

/-- **Dilation identity**: the support series over the multiples support
`A = dℕ` at base `b` is the full-support series at base `b^d`. -/
theorem erdosSupportSeries_multiples_eq_pow_base_full_support
    (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    erdosSupportSeries b {n : ℕ | d ∣ n}
      = ∑' k : ℕ, (1 : ℝ) / (((b : ℝ) ^ d) ^ (k + 1) - 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  have hbd1 : (1 : ℝ) < ((b : ℝ) ^ d) := one_lt_pow₀ hb1 (by omega)
  unfold erdosSupportSeries
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun k => d * ((k : ℕ) + 1)) ?_ ?_ ?_
  · -- injectivity on the support of the target series
    intro k₁ k₂ h
    have hd0 : d ≠ 0 := by omega
    have : (k₁ : ℕ) + 1 = (k₂ : ℕ) + 1 := Nat.eq_of_mul_eq_mul_left (by omega) h
    exact Subtype.ext (by omega)
  · -- the support of the indicator series is covered by the range
    intro a ha
    rw [Function.mem_support] at ha
    have hmem : a ∈ {n : ℕ | d ∣ n} := by
      by_contra hnot
      rw [Set.indicator_of_notMem hnot] at ha
      exact ha rfl
    obtain ⟨m, rfl⟩ := hmem
    have hm0 : m ≠ 0 := by
      intro h0
      subst h0
      apply ha
      have hmem0 : (d * 0) ∈ {n : ℕ | d ∣ n} := dvd_mul_right d 0
      rw [Set.indicator_of_mem hmem0]
      norm_num
    refine ⟨⟨m - 1, ?_⟩, ?_⟩
    · -- the target term at m - 1 is nonzero
      rw [Function.mem_support]
      have hpow : (1 : ℝ) < ((b : ℝ) ^ d) ^ (m - 1 + 1) := one_lt_pow₀ hbd1 (by omega)
      exact ne_of_gt (div_pos one_pos (by linarith))
    · show d * ((m - 1) + 1) = d * m
      congr 1
      omega
  · -- the terms agree along the bijection
    intro k
    have hmem : d * ((k : ℕ) + 1) ∈ {n : ℕ | d ∣ n} := ⟨(k : ℕ) + 1, rfl⟩
    rw [Set.indicator_of_mem hmem]
    rw [show (b : ℝ) ^ (d * ((k : ℕ) + 1)) = ((b : ℝ) ^ d) ^ ((k : ℕ) + 1) from
      pow_mul (b : ℝ) d ((k : ℕ) + 1)]

/-- **New support classes of Erdős #257: every multiples support.**  For
every base `b ≥ 2` and every `d ≥ 1`, the support series over `A = dℕ`
is irrational — at `b = 2` these are the `A = dℕ` members of Erdős #257
itself.  Proof: dilation to the full-support theorem at base `b^d`. -/
theorem irrational_erdosSupportSeries_multiples (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    Irrational (erdosSupportSeries b {n : ℕ | d ∣ n}) := by
  rw [erdosSupportSeries_multiples_eq_pow_base_full_support b d hb hd]
  have hbd : 2 ≤ b ^ d := le_trans hb (Nat.le_self_pow (by omega) b)
  have h := irrational_erdosSum_full_support (b ^ d) hbd
  have hcast : (((b ^ d : ℕ)) : ℝ) = ((b : ℝ) ^ d) := by push_cast; rfl
  rwa [hcast] at h

/-- **Raw-series form of the multiples support classes**: for every
`b ≥ 2` and `d ≥ 1`, `∑_{k≥1} 1/(b^(dk) - 1)` is irrational. -/
theorem irrational_erdosSum_multiples_support (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (d * (k + 1)) - 1)) := by
  have heq : (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (d * (k + 1)) - 1))
      = ∑' k : ℕ, (1 : ℝ) / (((b : ℝ) ^ d) ^ (k + 1) - 1) := by
    refine tsum_congr fun k => ?_
    rw [pow_mul]
  rw [heq]
  have hbd : 2 ≤ b ^ d := le_trans hb (Nat.le_self_pow (by omega) b)
  have h := irrational_erdosSum_full_support (b ^ d) hbd
  have hcast : (((b ^ d : ℕ)) : ℝ) = ((b : ℝ) ^ d) := by push_cast; rfl
  rwa [hcast] at h


/-! ## Support-coefficient calculus (wave 9): carry-aware certificates,
finite-prefix calculus, rational-prefix composition, stray-divisor
calculus, and the ω/Ω coefficient bridge

Wave 8 reduced arbitrary-support Erdős #257 to weighted-certificate
existence for `supportCoeff A`.  This wave repairs the certificate
interface for support families whose coefficients are not `τ`-shaped:

* the first block may be certified **in aggregate** (carry-aware) rather
  than digit-by-digit;
* a support may be **normalised by a finite prefix** per precision, with
  the rational prefix cleared by a `den · b^N` multiplier — necessarily
  so, since `b^a - 1` is coprime to `b` and no `b`-power multiplier can
  clear the prefix denominator;
* stray support divisors are counted by exact finite arithmetic
  (filter splits, reciprocal-tail budgets, and a two-line density bound),
  replacing the `τ`-specific valuation forcing that does NOT transfer;
* prime and prime-power supports are identified with `ω` and `Ω`,
  aligning the calculus with the Erdős #69 / Tao–Teräväinen frontier
  without claiming their analytic input.

None of this claims arbitrary-support certificate existence. -/

/-- **Digitwise first-block divisibility implies carry-block
divisibility**: each term `c(N+r)·b^(K-r)` is divisible by
`b^r · b^(K-r) = b^K`, so the wave-8 digitwise certificate is a special
case of the carry-aware certificate. -/
theorem carry_block_dvd_of_digitwise_blocks (b N K : ℕ) (c : ℕ → ℕ)
    (hblock : ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ c (N + r)) :
    b ^ K ∣ ∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r) := by
  refine Finset.dvd_sum fun r hr => ?_
  rcases Finset.mem_Icc.mp hr with ⟨hr1, hrK⟩
  obtain ⟨m, hm⟩ := hblock r hr
  refine ⟨m, ?_⟩
  rw [hm, show b ^ K = b ^ r * b ^ (K - r) from by rw [← pow_add]; congr 1; omega]
  ring

/-- **Carry-aware generic certificate consumer, one-sided.**  Like
`near_int_witness_of_weighted_coeff_block_certificate`, but the first
block is certified in aggregate: `b^K` divides the carry sum
`∑_{r≤K} c(N+r)·b^(K-r)`.  Individual digits need not vanish; only the
carried block total must be integral.  This is the certificate shape a
sieve construction with residual first-block digits feeds. -/
theorem near_int_witness_of_weighted_coeff_carry_block_certificate
    (b q N K L C : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hcarry : b ^ K ∣ ∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r))
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C)
    (hpos : ∃ t : ℕ, 0 < c (N + L + 1 + t))
    (harith : q * (C + (N + L + 2)) < b ^ L) :
    ∃ z : ℤ,
      0 < (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ) ∧
        (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ) < 1 / (q : ℝ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨z₀, hz₀⟩ := bpow_mul_coeff_series_eq_int_add_tail b N c hb hgrowth
  have hfsum : Summable
      (fun r : ℕ => ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1)) :=
    summable_coeff_shift_tail b N c hb hgrowth
  have hfarsum : Summable
      (fun t : ℕ => ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) :=
    (summable_nat_add_iff L).mpr hfsum
  -- split the tail at L
  have hsplitL : (∑' r : ℕ, ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  -- split the finite part at K
  have hsplitK : (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  -- the whole first block is one integer, by the carry certificate
  set S₁ : ℕ := ∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r) with hS₁def
  set z₁ : ℕ := S₁ / b ^ K with hz₁def
  have hz₁ : ((z₁ : ℕ) : ℝ)
      = ∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    have hreidx : S₁ = ∑ i ∈ Finset.range K, c (N + i + 1) * b ^ (K - (i + 1)) := by
      rw [hS₁def]
      have hIccIco : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIccIco, Finset.sum_Ico_eq_sum_range]
      have hn : K + 1 - 1 = K := by omega
      rw [hn]
      refine Finset.sum_congr rfl fun i hi => ?_
      have h1 : N + (1 + i) = N + i + 1 := by omega
      have h2 : K - (1 + i) = K - (i + 1) := by omega
      rw [h1, h2]
    have hbK0 : ((b ^ K : ℕ) : ℝ) ≠ 0 := by positivity
    have hcast : ((z₁ : ℕ) : ℝ) = ((S₁ : ℕ) : ℝ) / ((b ^ K : ℕ) : ℝ) := by
      rw [hz₁def, Nat.cast_div hcarry hbK0]
    rw [hcast, hreidx]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp hi
    have hsplit : (b : ℝ) ^ K = (b : ℝ) ^ (K - (i + 1)) * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    have hne1 : ((b : ℝ) ^ (K - (i + 1))) ≠ 0 := by positivity
    have hne2 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
    field_simp
  -- remainder positivity: some coefficient past the window is nonzero
  have hmid_nonneg : (0 : ℝ)
      ≤ ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨t₀, ht₀⟩ := hpos
  have hfar_pos : (0 : ℝ)
      < ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    have hcpos : (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) := by
      have hidx : N + (t₀ + L) + 1 = N + L + 1 + t₀ := by omega
      have h0 : 0 < c (N + (t₀ + L) + 1) := by rw [hidx]; exact ht₀
      exact_mod_cast h0
    have hterm0 : (0 : ℝ)
        < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := by positivity
    calc (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := hterm0
      _ ≤ _ := hfarsum.le_tsum t₀ fun j _ => by positivity
  -- middle window: exact weighted sum over the common denominator b^L
  have hterm : ∀ i ∈ Finset.Ico K L,
      ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1)
        = ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    intro i hi
    obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
    have hb1 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
    have hbL' : ((b : ℝ) ^ L) ≠ 0 := by positivity
    have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (L - (i + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_div_iff hb1 hbL']
    push_cast
    rw [hsplit]
    ring
  have hreindex : (∑ i ∈ Finset.Ico K L, c (N + i + 1) * b ^ (L - (i + 1)))
      = ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) := by
    have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hn : L + 1 - (K + 1) = L - K := by omega
    rw [hn]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : N + (K + j) + 1 = N + (K + 1 + j) := by omega
    have h2 : L - (K + j + 1) = L - (K + 1 + j) := by omega
    rw [h1, h2]
  have hmid : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      ≤ (C : ℝ) / (b : ℝ) ^ L := by
    have hsum_eq : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    have hnum : (∑ i ∈ Finset.Ico K L,
        ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) ≤ (C : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hreindex.trans_le hmiddle
    calc (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := hsum_eq
      _ ≤ (C : ℝ) / (b : ℝ) ^ L := by gcongr
  -- far tail bound, reshaped from the generic far-tail lemma
  have hfar_eq : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact coeff_far_tail_le b N L c hb hgrowth
  -- assemble the one-sided witness
  have hdiff : (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
      - ((z₀ + (z₁ : ℤ) : ℤ) : ℝ)
      = (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    rw [hz₀, hsplitL, hsplitK]
    push_cast
    rw [← hz₁]
    ring
  have hR_pos : (0 : ℝ)
      < (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    add_pos_of_nonneg_of_pos hmid_nonneg hfar_pos
  refine ⟨z₀ + (z₁ : ℤ), ?_, ?_⟩
  · rw [hdiff]
    exact hR_pos
  · rw [hdiff]
    have hsum_le : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
        ≤ (C : ℝ) / (b : ℝ) ^ L + ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L :=
      add_le_add hmid hfar
    refine lt_of_le_of_lt hsum_le ?_
    have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    have hc : (q : ℝ) * ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) < (b : ℝ) ^ L := by
      exact_mod_cast harith
    rw [← add_div, div_lt_div_iff₀ hbL hq', one_mul]
    calc ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) * (q : ℝ)
        = (q : ℝ) * ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) := mul_comm _ _
      _ < (b : ℝ) ^ L := hc

/-- **Carry-aware coefficient-series irrationality.**  If an arbitrary
coefficient sequence with growth envelope `c m ≤ m` admits a carry-aware
weighted certificate for every precision, `∑ c(m)/b^m` is irrational. -/
theorem irrational_coeff_series_of_weighted_coeff_carry_block_certificates
    (b : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < c (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  apply irrational_of_pow_mul_near_int b
  intro q hq
  obtain ⟨N, K, L, C, hKL, hcarry, hmiddle, hpos, harith⟩ := hcert q hq
  obtain ⟨z, hz_pos, hz_lt⟩ := near_int_witness_of_weighted_coeff_carry_block_certificate
    b q N K L C c hb hq hKL hgrowth hcarry hmiddle hpos harith
  refine ⟨N, z, ?_, ?_⟩
  · rw [abs_of_pos hz_pos]
    exact hz_pos
  · rw [abs_of_pos hz_pos]
    exact hz_lt

/-- **The carry interface subsumes the digitwise interface**: the wave-8
digitwise closure, re-derived through the carry-aware engine.  Machine
proof that loosening the first block to aggregate integrality loses
nothing. -/
theorem irrational_coeff_series_of_digitwise_via_carry
    (b : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ c (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < c (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  refine irrational_coeff_series_of_weighted_coeff_carry_block_certificates
    b c hb hgrowth fun q hq => ?_
  obtain ⟨N, K, L, C, hKL, hblock, hmiddle, hpos, harith⟩ := hcert q hq
  exact ⟨N, K, L, C, hKL, carry_block_dvd_of_digitwise_blocks b N K c hblock,
    hmiddle, hpos, harith⟩

/-- **Arbitrary-support irrationality from carry-aware certificates.**
The carry-aware analogue of
`irrational_erdosSupportSeries_of_weighted_coeff_certificates`:
certificate existence for `supportCoeff A` remains the OPEN obligation,
but the first block may now be supplied in carried aggregate. -/
theorem irrational_erdosSupportSeries_of_weighted_coeff_carry_certificates
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K, supportCoeff A (N + r) * b ^ (K - r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, supportCoeff A (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < supportCoeff A (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (erdosSupportSeries b A) := by
  rw [erdosSupportSeries_eq_tsum_supportCoeff b A hb]
  exact irrational_coeff_series_of_weighted_coeff_carry_block_certificates b
    (supportCoeff A) hb (supportCoeff_le_self A) hcert

/-! ## Finite-prefix calculus: height cuts of a support -/

/-- Pointwise indicator split of a support at a height cut `B`. -/
theorem indicator_support_split_at_cut (A : Set ℕ) (f : ℕ → ℝ) (B a : ℕ) :
    Set.indicator A f a
      = Set.indicator {n : ℕ | n ∈ A ∧ n ≤ B} f a
        + Set.indicator {n : ℕ | n ∈ A ∧ B < n} f a := by
  by_cases hA : a ∈ A
  · by_cases hB : a ≤ B
    · rw [Set.indicator_of_mem hA,
        Set.indicator_of_mem (show a ∈ {n : ℕ | n ∈ A ∧ n ≤ B} from ⟨hA, hB⟩),
        Set.indicator_of_notMem
          (show a ∉ {n : ℕ | n ∈ A ∧ B < n} by rintro ⟨-, h2⟩; omega)]
      ring
    · rw [Set.indicator_of_mem hA,
        Set.indicator_of_notMem
          (show a ∉ {n : ℕ | n ∈ A ∧ n ≤ B} by rintro ⟨-, h2⟩; omega),
        Set.indicator_of_mem
          (show a ∈ {n : ℕ | n ∈ A ∧ B < n} from ⟨hA, by omega⟩)]
      ring
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (show a ∉ {n : ℕ | n ∈ A ∧ n ≤ B} by
        rintro ⟨h1, -⟩; exact hA h1),
      Set.indicator_of_notMem (show a ∉ {n : ℕ | n ∈ A ∧ B < n} by
        rintro ⟨h1, -⟩; exact hA h1)]
    ring

/-- **The support series splits at any height cut** into a finite prefix
sum and the tail-support series. -/
theorem erdosSupportSeries_eq_prefix_add_tail (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b)
    (B : ℕ) :
    erdosSupportSeries b A
      = (∑ a ∈ Finset.range (B + 1),
          Set.indicator {n : ℕ | n ∈ A ∧ n ≤ B}
            (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a)
        + erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n} := by
  have h₁ := summable_erdosSupport_indicator b {n : ℕ | n ∈ A ∧ n ≤ B} hb
  have h₂ := summable_erdosSupport_indicator b {n : ℕ | n ∈ A ∧ B < n} hb
  have hsplit : erdosSupportSeries b A
      = (∑' a : ℕ, Set.indicator {n : ℕ | n ∈ A ∧ n ≤ B}
            (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a)
        + ∑' a : ℕ, Set.indicator {n : ℕ | n ∈ A ∧ B < n}
            (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a := by
    unfold erdosSupportSeries
    rw [← h₁.tsum_add h₂]
    exact tsum_congr fun a => indicator_support_split_at_cut A _ B a
  rw [hsplit]
  congr 1
  refine tsum_eq_sum fun a ha => ?_
  have haB : ¬ a ≤ B := fun h => ha (Finset.mem_range.mpr (by omega))
  exact Set.indicator_of_notMem (by rintro ⟨-, h2⟩; exact haB h2) _

/-- **The finite prefix is rational.** -/
theorem prefix_sum_eq_rat_cast (b : ℕ) (A : Set ℕ) (B : ℕ) :
    ∃ p : ℚ, ((p : ℚ) : ℝ)
      = ∑ a ∈ Finset.range (B + 1),
          Set.indicator {n : ℕ | n ∈ A ∧ n ≤ B}
            (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a := by
  classical
  refine ⟨∑ a ∈ Finset.range (B + 1),
    if a ∈ A ∧ a ≤ B then (1 : ℚ) / ((b : ℚ) ^ a - 1) else 0, ?_⟩
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a ∈ A ∧ a ≤ B
  · rw [if_pos h, Set.indicator_of_mem (show a ∈ {n : ℕ | n ∈ A ∧ n ≤ B} from h)]
    push_cast
    ring
  · rw [if_neg h, Set.indicator_of_notMem
      (show a ∉ {n : ℕ | n ∈ A ∧ n ≤ B} from h), Rat.cast_zero]

/-- **Finite-prefix invariance, downward**: irrationality of a
tail-support series transfers to the full support series — the prefix is
rational.  Removing finitely many bothersome small support elements is a
legitimate normalisation move. -/
theorem irrational_erdosSupportSeries_of_tail (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b)
    (B : ℕ) (h : Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n})) :
    Irrational (erdosSupportSeries b A) := by
  obtain ⟨p, hp⟩ := prefix_sum_eq_rat_cast b A B
  rw [erdosSupportSeries_eq_prefix_add_tail b A hb B, ← hp]
  exact h.ratCast_add p

/-- **Finite-prefix invariance, upward**: cutting a bounded prefix off a
support preserves irrationality of the support series. -/
theorem irrational_erdosSupportSeries_tail_of_irrational (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (B : ℕ) (h : Irrational (erdosSupportSeries b A)) :
    Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n}) := by
  obtain ⟨p, hp⟩ := prefix_sum_eq_rat_cast b A B
  have hsplit := erdosSupportSeries_eq_prefix_add_tail b A hb B
  have heq : erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n}
      = erdosSupportSeries b A + ((-p : ℚ) : ℝ) := by
    rw [hsplit, ← hp]
    push_cast
    ring
  rw [heq]
  exact h.add_ratCast (-p)

/-! ## Rational-prefix composition: near-integer witnesses with a
prefix-clearing multiplier -/

/-- **Rational-prefix near-integer composition.**  If for every precision
`q` some rational-plus-tail split of `x` admits a one-sided
`b^N`-dilated witness at the prefix-adjusted precision `q · p.den`, then
`x` is irrational.  The multiplier `p.den · b^N` clears the prefix
denominator.  This composition is forced: `b^a - 1` is coprime to `b`,
so no `b`-power multiplier can clear a support-prefix denominator, and
per-precision finite-prefix normalisation genuinely needs the
integer-multiplier criterion. -/
theorem irrational_of_rat_prefix_tail_near_int_witnesses
    (b : ℕ) (x : ℝ)
    (h : ∀ q : ℕ, 0 < q → ∃ (p : ℚ) (T : ℝ) (N : ℕ) (z : ℤ),
      x = (p : ℝ) + T ∧
      0 < (b : ℝ) ^ N * T - (z : ℝ) ∧
      (b : ℝ) ^ N * T - (z : ℝ) < 1 / ((q * p.den : ℕ) : ℝ)) :
    Irrational x := by
  apply irrational_of_int_mul_near_int
  intro q hq
  obtain ⟨p, T, N, z, hxsplit, hpos, hlt⟩ := h q hq
  have hden_pos : 0 < p.den := p.den_pos
  have hden' : (0 : ℝ) < (p.den : ℝ) := by exact_mod_cast hden_pos
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnum : (p.den : ℝ) * (p : ℝ) = (p.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  have hkey : (((p.den : ℤ) * (b : ℤ) ^ N : ℤ) : ℝ) * x
      - (((b : ℤ) ^ N * p.num + (p.den : ℤ) * z : ℤ) : ℝ)
      = (p.den : ℝ) * ((b : ℝ) ^ N * T - (z : ℝ)) := by
    push_cast
    rw [hxsplit]
    linear_combination ((b : ℝ) ^ N) * hnum
  refine ⟨(p.den : ℤ) * (b : ℤ) ^ N, (b : ℤ) ^ N * p.num + (p.den : ℤ) * z, ?_, ?_⟩
  · rw [hkey, abs_of_pos (mul_pos hden' hpos)]
    exact mul_pos hden' hpos
  · rw [hkey, abs_of_pos (mul_pos hden' hpos)]
    have h1 : (p.den : ℝ) * ((b : ℝ) ^ N * T - (z : ℝ))
        < (p.den : ℝ) * (1 / ((q * p.den : ℕ) : ℝ)) :=
      mul_lt_mul_of_pos_left hlt hden'
    have h2 : (p.den : ℝ) * (1 / ((q * p.den : ℕ) : ℝ)) = 1 / (q : ℝ) := by
      push_cast
      field_simp
    rw [h2] at h1
    exact h1

/-! ## Stray-divisor calculus: exact finite arithmetic for support
coefficients -/

/-- **Instance-agnostic filter form of the support coefficient**: under
any decidability instance for membership, `supportCoeff A n` is the
divisor-filter cardinality.  This is the bridge every stray-divisor
argument uses to leave the `Classical.decPred` packaging of the
definition. -/
theorem supportCoeff_eq_card_filter (A : Set ℕ) (n : ℕ)
    [DecidablePred (· ∈ A)] :
    supportCoeff A n = (n.divisors.filter fun d => d ∈ A).card := by
  unfold supportCoeff
  congr 1
  ext d
  simp only [Finset.mem_filter]

/-- **Support-coefficient split along a marked finite set**: divisors in
`A` split into those inside a marked finite set `F` and those outside —
the forced/stray decomposition, stated entirely in `supportCoeff`
language. -/
theorem supportCoeff_eq_inter_add_diff (A : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    supportCoeff A n
      = supportCoeff (A ∩ ↑F) n + supportCoeff (A \ ↑F) n := by
  classical
  have h1 : (n.divisors.filter fun d => d ∈ A ∩ ↑F)
      = (n.divisors.filter fun d => d ∈ A).filter fun d => d ∈ F := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    simp [Set.mem_inter_iff]
  have h2 : (n.divisors.filter fun d => d ∈ A \ ↑F)
      = (n.divisors.filter fun d => d ∈ A).filter fun d => ¬ d ∈ F := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    simp [Set.mem_diff]
  rw [supportCoeff_eq_card_filter A n, supportCoeff_eq_card_filter (A ∩ ↑F) n,
    supportCoeff_eq_card_filter (A \ ↑F) n, h1, h2]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-- **First-block exactness from forced divisors and no strays**: if the
divisors of `n` lying in `A` are exactly a designated finite set `P`,
then `supportCoeff A n = P.card`.  This is what replaces `τ`-valuation
forcing in support language: exactness is a counting statement, not a
valuation statement. -/
theorem supportCoeff_eq_card_of_forced_of_no_strays (A : Set ℕ) (P : Finset ℕ)
    (n : ℕ) (hn : n ≠ 0)
    (hPA : ∀ a ∈ P, a ∈ A) (hPdvd : ∀ a ∈ P, a ∣ n)
    (hno : ∀ d : ℕ, d ∣ n → d ∈ A → d ∈ P) :
    supportCoeff A n = P.card := by
  classical
  unfold supportCoeff
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, -⟩, hA⟩
    exact hno d hdvd hA
  · intro hdP
    exact ⟨⟨hPdvd d hdP, hn⟩, hPA d hdP⟩

/-- **Two-line density bound**: a finite set of positive integers bounded
by `X` has cardinality at most `X` times its reciprocal sum.  This is
the elementary replacement for analytic density arguments: summable
reciprocals force support sparsity. -/
theorem card_le_mul_sum_inv (X : ℕ) (T : Finset ℕ)
    (hT : ∀ a ∈ T, 0 < a ∧ a ≤ X) :
    (T.card : ℝ) ≤ (X : ℝ) * ∑ a ∈ T, (1 : ℝ) / a := by
  rw [Finset.mul_sum, Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_le_sum fun a ha => ?_
  obtain ⟨ha0, haX⟩ := hT a ha
  have ha0' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  rw [mul_one_div, le_div_iff₀ ha0', one_mul]
  exact_mod_cast haX

/-- **Progression-hit aggregation**: the residue-class hit counts
`Y/a + 1` aggregate against the reciprocal sum plus the cardinality —
the bridge from exact `ℕ` progression counting to real reciprocal
budgets. -/
theorem sum_div_add_one_cast_le (Y : ℕ) (T : Finset ℕ) :
    ((∑ a ∈ T, (Y / a + 1) : ℕ) : ℝ)
      ≤ (Y : ℝ) * (∑ a ∈ T, (1 : ℝ) / a) + (T.card : ℝ) := by
  push_cast
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.card_eq_sum_ones]
  push_cast
  refine add_le_add (Finset.sum_le_sum fun a _ => ?_) (le_refl _)
  rw [mul_one_div]
  exact Nat.cast_div_le

/-- **Reciprocal-tail extraction from summability**: past some height
`B`, every finite selection of indices beyond `B` has weight sum at most
`ε`.  This converts `Summable` into the finite tail budgets the sieve
constructions consume. -/
theorem exists_tail_bound_of_summable (g : ℕ → ℝ) (hg0 : ∀ n : ℕ, 0 ≤ g n)
    (hsum : Summable g) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ T : Finset ℕ, (∀ a ∈ T, B < a) → ∑ a ∈ T, g a ≤ ε := by
  have htendsto := hsum.hasSum.tendsto_sum_nat
  rw [Metric.tendsto_atTop] at htendsto
  obtain ⟨B, hB⟩ := htendsto ε hε
  refine ⟨B, fun T hT => ?_⟩
  have hBsum := hB B (le_refl B)
  rw [Real.dist_eq] at hBsum
  have habs := abs_lt.mp hBsum
  have hdisj : Disjoint (Finset.range B) T := by
    rw [Finset.disjoint_left]
    intro a ha haT
    have h1 := Finset.mem_range.mp ha
    have h2 := hT a haT
    omega
  have hunion : ∑ a ∈ Finset.range B, g a + ∑ a ∈ T, g a
      = ∑ a ∈ Finset.range B ∪ T, g a := (Finset.sum_union hdisj).symm
  have hle : ∑ a ∈ Finset.range B ∪ T, g a ≤ ∑' a : ℕ, g a :=
    hsum.sum_le_tsum _ (fun i _ => hg0 i)
  linarith [habs.1, habs.2]

/-! ## The ω / Ω coefficient bridge: prime and prime-power supports -/

/-- **Prime support gives ω**: the support coefficient of the prime
support counts distinct prime factors.  This aligns the support calculus
with Erdős #69: `∑_p 1/(b^p - 1) = ∑_m ω(m)/b^m`.  The analytic
irrationality input (Tao–Teräväinen) is NOT claimed — this identity
places it at the exact theorem boundary where it belongs. -/
theorem supportCoeff_primes_eq_card_primeFactors (n : ℕ) :
    supportCoeff {p : ℕ | p.Prime} n = n.primeFactors.card := by
  classical
  unfold supportCoeff
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors,
    Set.mem_setOf_eq]
  tauto

/-- **Prime-power support gives Ω**: the support coefficient of the
prime-power support is the number of prime factors counted with
multiplicity — prime-power divisors `p^k ∣ n` with `1 ≤ k` biject with
pairs `(p, k)`, `k ≤ v_p(n)`. -/
theorem supportCoeff_primePowers_eq_sum_factorization (n : ℕ) :
    supportCoeff {m : ℕ | ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ m = p ^ k} n
      = n.factorization.sum fun _ e => e := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · unfold supportCoeff
    simp
  have hΩ : (n.factorization.sum fun _ e => e)
      = ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [← Nat.support_factorization]
    rfl
  have hdisj : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ q →
      Disjoint ((Finset.Icc 1 (n.factorization p)).image (p ^ ·))
        ((Finset.Icc 1 (n.factorization q)).image (q ^ ·)) := by
    intro p hp q hq hpq
    rw [Finset.disjoint_left]
    rintro d hd hd'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hd'
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hqP : q.Prime := (Nat.mem_primeFactors.mp hq).1
    have hpd : p ∣ q ^ j := by
      rw [hEq]
      exact dvd_pow_self p (by omega)
    exact hpq ((Nat.prime_dvd_prime_iff_eq hpP hqP).mp (hpP.dvd_of_dvd_pow hpd))
  calc supportCoeff {m : ℕ | ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ m = p ^ k} n
      = (n.primeFactors.biUnion
          (fun p => (Finset.Icc 1 (n.factorization p)).image (p ^ ·))).card := by
        unfold supportCoeff
        congr 1
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Set.mem_setOf_eq,
          Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc,
          Nat.mem_primeFactors]
        constructor
        · rintro ⟨⟨hdvd, -⟩, p, k, hp, hk, rfl⟩
          exact ⟨p, ⟨hp, dvd_trans (dvd_pow_self p (by omega)) hdvd, hn⟩, k,
            ⟨hk, (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp hdvd⟩, rfl⟩
        · rintro ⟨p, ⟨hp, hpdvd, -⟩, k, ⟨hk1, hkle⟩, rfl⟩
          exact ⟨⟨(Nat.Prime.pow_dvd_iff_le_factorization hp hn).mpr hkle, hn⟩,
            p, k, hp, hk1, rfl⟩
    _ = ∑ p ∈ n.primeFactors,
          ((Finset.Icc 1 (n.factorization p)).image (p ^ ·)).card :=
        Finset.card_biUnion hdisj
    _ = ∑ p ∈ n.primeFactors, n.factorization p := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp2 : 2 ≤ p := (Nat.mem_primeFactors.mp hp).1.two_le
        rw [Finset.card_image_of_injective _ (Nat.pow_right_injective hp2),
          Nat.card_Icc]
        omega
    _ = n.factorization.sum fun _ e => e := hΩ.symm

/-- Series bridge at the prime support: `∑_{p prime} 1/(b^p - 1)
= ∑_m ω(m)/b^m` — the Erdős #69 identity, in support language. -/
theorem erdosSupportSeries_primes_eq_tsum_omega (b : ℕ) (hb : 2 ≤ b) :
    erdosSupportSeries b {p : ℕ | p.Prime}
      = ∑' m : ℕ, (((m + 1).primeFactors.card : ℕ) : ℝ) / (b : ℝ) ^ (m + 1) := by
  rw [erdosSupportSeries_eq_tsum_supportCoeff b _ hb]
  exact tsum_congr fun m => by rw [supportCoeff_primes_eq_card_primeFactors]

/-- Series bridge at the prime-power support:
`∑_{p^k} 1/(b^(p^k) - 1) = ∑_m Ω(m)/b^m`. -/
theorem erdosSupportSeries_primePowers_eq_tsum_bigOmega (b : ℕ) (hb : 2 ≤ b) :
    erdosSupportSeries b {m : ℕ | ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ m = p ^ k}
      = ∑' m : ℕ,
          (((m + 1).factorization.sum fun _ e => e : ℕ) : ℝ) / (b : ℝ) ^ (m + 1) := by
  rw [erdosSupportSeries_eq_tsum_supportCoeff b _ hb]
  exact tsum_congr fun m => by rw [supportCoeff_primePowers_eq_sum_factorization]

/-! ## Pairwise-coprime supports: Erdős's 1948 partial theorem -/

/-- Parameter-closure helper: every linear function of `L` is strictly
below `b^L` for some `L` past any threshold — the wave-9 form of the
wave-7 parameter kernel. -/
theorem exists_linear_lt_pow (b α β L₀ : ℕ) (hb : 2 ≤ b) :
    ∃ L : ℕ, L₀ ≤ L ∧ α + β * L < b ^ L := by
  set e : ℕ := α + β * (L₀ + 1) + L₀ with hedef
  set L : ℕ := 3 * β + e + 1 with hLdef
  refine ⟨L, by omega, ?_⟩
  have h1 : β * (3 * β + e) + e ≤ 2 ^ (3 * β + e) := param_linear_le_two_pow β e
  have h2 : α + β * L ≤ β * (3 * β + e) + e + β := by
    have hαe : α ≤ e := by omega
    calc α + β * L = α + β * (3 * β + e) + β := by rw [hLdef]; ring
      _ ≤ β * (3 * β + e) + e + β := by omega
  have hβpow : β < 2 ^ (3 * β + e) := by
    have hb1 : β < 2 ^ β := Nat.lt_two_pow_self
    have hmono : (2 : ℕ) ^ β ≤ 2 ^ (3 * β + e) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hstep : (2 : ℕ) ^ L = 2 ^ (3 * β + e) * 2 := by rw [hLdef, pow_succ]
  have h4 : (2 : ℕ) ^ L ≤ b ^ L := Nat.pow_le_pow_left hb L
  omega

/-- A support element dividing a nonzero integer makes the support
coefficient positive — the far-tail positivity every sieve certificate
needs, free from infinitude of the support. -/
theorem supportCoeff_pos_of_mem_dvd (A : Set ℕ) {a n : ℕ} (ha : a ∈ A)
    (hdvd : a ∣ n) (hn : n ≠ 0) : 0 < supportCoeff A n := by
  classical
  rw [supportCoeff_eq_card_filter]
  exact Finset.card_pos.mpr
    ⟨a, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hn⟩, ha⟩⟩

/-- **Weighted geometric window bound for one modulus**: a hit set inside
the window `(K, L]` whose members all sit at height `≥ m ≥ K + 1`
carries weight at most `b^(L + 1 - m)`. -/
theorem sum_pow_weight_window_hits_le (b K L m : ℕ) (hb : 2 ≤ b)
    (hm : K + 1 ≤ m) (H : Finset ℕ)
    (hH : ∀ s ∈ H, s ∈ Finset.Icc (K + 1) L ∧ m ≤ s) :
    ∑ s ∈ H, b ^ (L - s) ≤ b ^ (L + 1 - m) := by
  have hsub : H ⊆ Finset.Icc m L := by
    intro s hs
    obtain ⟨hwin, hms⟩ := hH s hs
    exact Finset.mem_Icc.mpr ⟨hms, (Finset.mem_Icc.mp hwin).2⟩
  calc ∑ s ∈ H, b ^ (L - s)
      ≤ ∑ s ∈ Finset.Icc m L, b ^ (L - s) :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ s ∈ Finset.Icc ((m - 1) + 1) L, b ^ (L - s) := by
        rw [show (m - 1) + 1 = m from by omega]
    _ ≤ b ^ (L - (m - 1)) := sum_pow_weight_middle_window_le b (m - 1) L hb
    _ = b ^ (L + 1 - m) := by
        congr 1
        omega

/-- Pairwise-coprime support elements have coprime disjoint-block
products. -/
theorem coprime_prod_prod_of_pairwise_disjoint (A : Set ℕ)
    (hpair : A.Pairwise Nat.Coprime) (P Q : Finset ℕ)
    (hP : ∀ a ∈ P, a ∈ A) (hQ : ∀ a ∈ Q, a ∈ A) (hdisj : Disjoint P Q) :
    Nat.Coprime (∏ a ∈ P, a) (∏ a ∈ Q, a) := by
  refine Nat.Coprime.prod_left fun a ha => ?_
  refine Nat.Coprime.prod_right fun c hc => ?_
  have hne : a ≠ c := by
    intro h
    subst h
    exact (Finset.disjoint_left.mp hdisj ha) hc
  exact hpair (hP a ha) (hQ c hc) hne

/-- A support element outside a marked finset of support elements is
coprime to the finset's product. -/
theorem coprime_prod_of_pairwise_notMem (A : Set ℕ)
    (hpair : A.Pairwise Nat.Coprime) (Q : Finset ℕ) (hQ : ∀ a ∈ Q, a ∈ A)
    {a : ℕ} (ha : a ∈ A) (hnot : a ∉ Q) :
    Nat.Coprime a (∏ c ∈ Q, c) := by
  refine Nat.Coprime.prod_right fun c hc => ?_
  have hne : a ≠ c := by
    intro h
    subst h
    exact hnot hc
  exact hpair ha (hQ c hc) hne

/-- **Disjoint block selection from an infinite support**: above any
buffer, an infinite support supplies pairwise-disjoint finite blocks of
any prescribed sizes. -/
theorem exists_disjoint_support_blocks (A : Set ℕ) (hA : A.Infinite)
    (Buf : ℕ) (sz : ℕ → ℕ) (K : ℕ) :
    ∃ P : ℕ → Finset ℕ,
      (∀ r : ℕ, ∀ a ∈ P r, a ∈ A ∧ Buf < a) ∧
      (∀ r ∈ Finset.Icc 1 K, (P r).card = sz r) ∧
      (∀ r : ℕ, r ∉ Finset.Icc 1 K → P r = ∅) ∧
      (∀ r s : ℕ, r ≠ s → Disjoint (P r) (P s)) := by
  classical
  induction K with
  | zero =>
      refine ⟨fun _ => ∅, by simp, ?_, fun r _ => rfl, by simp⟩
      intro r hr
      exact absurd (Finset.mem_Icc.mp hr) (by omega)
  | succ K ih =>
      obtain ⟨P, hPA, hPcard, hPempty, hPdisj⟩ := ih
      have hbig : (A \ ({a : ℕ | a ≤ Buf}
          ∪ ↑((Finset.Icc 1 K).biUnion P))).Infinite :=
        hA.diff ((Set.finite_le_nat Buf).union (Finset.finite_toSet _))
      obtain ⟨T, hTsub, hTcard⟩ := hbig.exists_subset_card_eq (sz (K + 1))
      refine ⟨fun r => if r = K + 1 then T else P r, ?_, ?_, ?_, ?_⟩
      · intro r a ha
        by_cases hr : r = K + 1
        · simp only [if_pos hr] at ha
          have hmem := hTsub (Finset.mem_coe.mpr ha)
          rw [Set.mem_diff, Set.mem_union] at hmem
          push Not at hmem
          exact ⟨hmem.1, by
            have := hmem.2.1
            simp only [Set.mem_setOf_eq] at this
            omega⟩
        · simp only [if_neg hr] at ha
          exact hPA r a ha
      · intro r hr
        rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
        by_cases hrK : r = K + 1
        · simp only [if_pos hrK]
          rw [hrK]
          exact hTcard
        · simp only [if_neg hrK]
          exact hPcard r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩)
      · intro r hr
        have hrK : r ≠ K + 1 := by
          intro h
          exact hr (by rw [h]; exact Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩)
        simp only [if_neg hrK]
        refine hPempty r fun hmem => hr ?_
        rcases Finset.mem_Icc.mp hmem with ⟨h1, h2⟩
        exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
      · intro r s hrs
        have hTP : ∀ u : ℕ, u ≠ K + 1 → Disjoint T (P u) := by
          intro u hu
          rw [Finset.disjoint_left]
          intro a haT haP
          have hmem := hTsub (Finset.mem_coe.mpr haT)
          rw [Set.mem_diff, Set.mem_union] at hmem
          push Not at hmem
          have hbi := hmem.2.2
          by_cases huI : u ∈ Finset.Icc 1 K
          · exact hbi (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨u, huI, haP⟩))
          · rw [hPempty u huI] at haP
            exact absurd haP (Finset.notMem_empty a)
        by_cases hr : r = K + 1
        · have hs : s ≠ K + 1 := by omega
          simp only [if_pos hr, if_neg hs]
          exact hTP s hs
        · by_cases hs : s = K + 1
          · simp only [if_neg hr, if_pos hs]
            exact (hTP r hr).symm
          · simp only [if_neg hr, if_neg hs]
            exact hPdisj r s hrs

/-- **Certificate supply for pairwise-coprime supports.**  Small support
elements join the CRT modulus with residue `0`; adaptive block sizes
`b^r - d_r mod b^r` absorb their deterministic first-block hits; pairwise
coprimality makes the moduli independent; summable reciprocals control
the strays through a single hit-count budget. -/
theorem exists_weighted_coeff_certificates_supportCoeff_pairwise_coprime
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a)) :
    ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
      (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ supportCoeff A (N + r)) ∧
      (∑ r ∈ Finset.Icc (K + 1) L, supportCoeff A (N + r) * b ^ (L - r) ≤ C) ∧
      (∃ t : ℕ, 0 < supportCoeff A (N + L + 1 + t)) ∧
      q * (C + (N + L + 2)) < b ^ L := by
  intro q hq
  classical
  -- reciprocal-tail budgets from summability
  have hg0 : ∀ n : ℕ, 0 ≤ Set.indicator A (fun a : ℕ => (1 : ℝ) / a) n :=
    fun n => Set.indicator_nonneg (fun a _ => by positivity) n
  have htail : ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∀ T : Finset ℕ,
      (∀ a ∈ T, a ∈ A ∧ B < a) → ∑ a ∈ T, (1 : ℝ) / a ≤ ε := by
    intro ε hε
    obtain ⟨B, hB⟩ := exists_tail_bound_of_summable _ hg0 hsum ε hε
    refine ⟨B, fun T hT => ?_⟩
    have heq : ∑ a ∈ T, (1 : ℝ) / a
        = ∑ a ∈ T, Set.indicator A (fun a : ℕ => (1 : ℝ) / a) a :=
      Finset.sum_congr rfl fun a ha =>
        (Set.indicator_of_mem (hT a ha).1 (fun a : ℕ => (1 : ℝ) / a)).symm
    rw [heq]
    exact hB T fun a ha => (hT a ha).2
  -- K: the base-power beats the linear certificate cost
  obtain ⟨K, hK1, hKarith⟩ := exists_linear_lt_pow b (2*q*(b+2)) (2*q) 1 hb
  -- B₀: reciprocal tail cut and forced-leak buffer
  have hε₀ : (0:ℝ) < 1 / (64 * ((K:ℝ) + 1)) := by positivity
  obtain ⟨B₁, hB₁⟩ := htail _ hε₀
  set B₀ : ℕ := max B₁ (3*K+1) with hB₀def
  have hB₀3K : 3*K+1 ≤ B₀ := le_max_right _ _
  have hB₀tail : ∀ T : Finset ℕ, (∀ a ∈ T, a ∈ A ∧ B₀ < a) →
      ∑ a ∈ T, (1:ℝ)/a ≤ 1 / (64 * ((K:ℝ) + 1)) := by
    intro T hT
    refine hB₁ T fun a ha => ⟨(hT a ha).1, ?_⟩
    have h1 := (hT a ha).2
    have h2 : B₁ ≤ B₀ := le_max_left _ _
    omega
  -- small support elements and their slot hit counts
  set smalls : Finset ℕ := (Finset.Icc 1 B₀).filter (· ∈ A) with hsmallsdef
  have hsmalls_mem : ∀ a ∈ smalls, a ∈ A ∧ 1 ≤ a ∧ a ≤ B₀ := by
    intro a ha
    obtain ⟨hI, hA'⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hI
    exact ⟨hA', h1, h2⟩
  set d : ℕ → ℕ := fun r => (smalls.filter (· ∣ r)).card with hddef
  set sz : ℕ → ℕ := fun r => b ^ r - d r % b ^ r with hszdef
  -- disjoint blocks above the buffer, of the adaptive sizes
  obtain ⟨P, hPA, hPcard, hPempty, hPdisj⟩ :=
    exists_disjoint_support_blocks A hA B₀ sz K
  set blocksU : Finset ℕ := (Finset.Icc 1 K).biUnion P with hblocksdef
  have hblocksU_mem : ∀ a ∈ blocksU, a ∈ A ∧ B₀ < a := by
    intro a ha
    obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp ha
    exact hPA r a har
  -- the modulus family: block products plus the small-element product
  set mset : ℕ → Finset ℕ := fun r => if r = K + 1 then smalls else P r
    with hmsetdef
  set m : ℕ → ℕ := fun r => ∏ a ∈ mset r, a with hmdef
  have hmset_mem : ∀ r : ℕ, ∀ a ∈ mset r, a ∈ A := by
    intro r a ha
    by_cases h : r = K + 1
    · rw [show mset r = smalls from by
        show (if r = K + 1 then smalls else P r) = smalls
        rw [if_pos h]] at ha
      exact (hsmalls_mem a ha).1
    · rw [show mset r = P r from by
        show (if r = K + 1 then smalls else P r) = P r
        rw [if_neg h]] at ha
      exact (hPA r a ha).1
  have hmset_pos : ∀ r : ℕ, ∀ a ∈ mset r, 0 < a := by
    intro r a ha
    by_cases h : r = K + 1
    · rw [show mset r = smalls from by
        show (if r = K + 1 then smalls else P r) = smalls
        rw [if_pos h]] at ha
      have := (hsmalls_mem a ha).2.1
      omega
    · rw [show mset r = P r from by
        show (if r = K + 1 then smalls else P r) = P r
        rw [if_neg h]] at ha
      have := (hPA r a ha).2
      omega
  have hmset_disj : ∀ r s : ℕ, r ≠ s → Disjoint (mset r) (mset s) := by
    intro r s hrs
    by_cases h1 : r = K + 1 <;> by_cases h2 : s = K + 1
    · exact absurd (h1.trans h2.symm) hrs
    · rw [show mset r = smalls from by
          show (if r = K + 1 then smalls else P r) = smalls
          rw [if_pos h1],
        show mset s = P s from by
          show (if s = K + 1 then smalls else P s) = P s
          rw [if_neg h2]]
      rw [Finset.disjoint_left]
      intro a haS haP
      have hle := (hsmalls_mem a haS).2.2
      have hgt := (hPA s a haP).2
      omega
    · rw [show mset r = P r from by
          show (if r = K + 1 then smalls else P r) = P r
          rw [if_neg h1],
        show mset s = smalls from by
          show (if s = K + 1 then smalls else P s) = smalls
          rw [if_pos h2]]
      rw [Finset.disjoint_left]
      intro a haP haS
      have hle := (hsmalls_mem a haS).2.2
      have hgt := (hPA r a haP).2
      omega
    · rw [show mset r = P r from by
          show (if r = K + 1 then smalls else P r) = P r
          rw [if_neg h1],
        show mset s = P s from by
          show (if s = K + 1 then smalls else P s) = P s
          rw [if_neg h2]]
      exact hPdisj r s hrs
  have hm_pos : ∀ r ∈ Finset.Icc 1 (K+1), 0 < m r := by
    intro r _
    exact Finset.prod_pos fun a ha => hmset_pos r a ha
  have hm_cop : ∀ r s, r ∈ Finset.Icc 1 (K+1) → s ∈ Finset.Icc 1 (K+1) →
      r ≠ s → Nat.Coprime (m r) (m s) := by
    intro r s _ _ hrs
    exact coprime_prod_prod_of_pairwise_disjoint A hpair (mset r) (mset s)
      (hmset_mem r) (hmset_mem s) (hmset_disj r s hrs)
  -- CRT: residue 0 on the small product, -r on each block product
  obtain ⟨x, hxlt, hxcong⟩ := exists_bounded_crt_residue (K+1) m
    (fun r => if r = K + 1 then 0 else (m r - r % m r) % m r) hm_pos hm_cop
  set M : ℕ := ∏ r ∈ Finset.Icc 1 (K+1), m r with hMdef
  have hMpos : 0 < M := Finset.prod_pos hm_pos
  have hmdvdM : ∀ r ∈ Finset.Icc 1 (K+1), m r ∣ M := fun r hr =>
    Finset.dvd_prod_of_mem m hr
  have hK1mem : K + 1 ∈ Finset.Icc 1 (K+1) :=
    Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩
  -- slot divisibility of the block moduli
  have hslot : ∀ r ∈ Finset.Icc 1 K, m r ∣ x + r := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrK⟩
    have hrmem : r ∈ Finset.Icc 1 (K+1) := Finset.mem_Icc.mpr ⟨hr1, by omega⟩
    have hrne : r ≠ K + 1 := by omega
    have hcong := hxcong r hrmem
    rw [if_neg hrne] at hcong
    have hpos := hm_pos r hrmem
    have hadd : x + r ≡ ((m r - r % m r) % m r) + r [MOD m r] :=
      Nat.ModEq.add_right r hcong
    have hdvd_rhs : m r ∣ ((m r - r % m r) % m r) + r := by
      have hdm := Nat.div_add_mod r (m r)
      have hmod_lt : r % m r < m r := Nat.mod_lt _ hpos
      by_cases hzero : r % m r = 0
      · have h1 : (m r - r % m r) % m r = 0 := by
          rw [hzero, Nat.sub_zero, Nat.mod_self]
        rw [h1, Nat.zero_add]
        exact Nat.dvd_of_mod_eq_zero hzero
      · have h1 : (m r - r % m r) % m r = m r - r % m r :=
          Nat.mod_eq_of_lt (by omega)
        rw [h1]
        refine ⟨1 + r / m r, ?_⟩
        have hexp : m r * (1 + r / m r) = m r + m r * (r / m r) := by ring
        omega
    exact (Nat.modEq_zero_iff_dvd).mp
      (hadd.trans ((Nat.modEq_zero_iff_dvd).mpr hdvd_rhs))
  -- small elements divide x, and divide M
  have hmK1smalls : mset (K+1) = smalls := by
    show (if K + 1 = K + 1 then smalls else P (K+1)) = smalls
    rw [if_pos rfl]
  have hsmalls_dvd_x : ∀ a ∈ smalls, a ∣ x := by
    intro a ha
    have hcong := hxcong (K+1) hK1mem
    rw [if_pos rfl] at hcong
    have hm0dvd : m (K+1) ∣ x := (Nat.modEq_zero_iff_dvd).mp hcong
    refine dvd_trans ?_ hm0dvd
    show a ∣ ∏ c ∈ mset (K+1), c
    rw [hmK1smalls]
    exact Finset.dvd_prod_of_mem _ ha
  have hsmalls_dvd_M : ∀ a ∈ smalls, a ∣ M := by
    intro a ha
    refine dvd_trans ?_ (hmdvdM (K+1) hK1mem)
    show a ∣ ∏ c ∈ mset (K+1), c
    rw [hmK1smalls]
    exact Finset.dvd_prod_of_mem _ ha
  -- block elements divide their slot and M
  have hmsetblock : ∀ r ∈ Finset.Icc 1 K, mset r = P r := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrK⟩
    show (if r = K + 1 then smalls else P r) = P r
    rw [if_neg (by omega : r ≠ K + 1)]
  have hblock_dvd_slot : ∀ r ∈ Finset.Icc 1 K, ∀ a ∈ P r, a ∣ x + r := by
    intro r hr a ha
    refine dvd_trans ?_ (hslot r hr)
    show a ∣ ∏ c ∈ mset r, c
    rw [hmsetblock r hr]
    exact Finset.dvd_prod_of_mem _ ha
  have hblocks_dvd_M : ∀ r ∈ Finset.Icc 1 K, ∀ a ∈ P r, a ∣ M := by
    intro r hr a ha
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrK⟩
    have hrmem : r ∈ Finset.Icc 1 (K+1) := Finset.mem_Icc.mpr ⟨hr1, by omega⟩
    refine dvd_trans ?_ (hmdvdM r hrmem)
    show a ∣ ∏ c ∈ mset r, c
    rw [hmsetblock r hr]
    exact Finset.dvd_prod_of_mem _ ha
  -- strays are coprime to the whole modulus
  have hstray_cop : ∀ a, a ∈ A → B₀ < a → a ∉ blocksU → Nat.Coprime a M := by
    intro a haA haB hanb
    refine Nat.Coprime.prod_right fun r hr => ?_
    show Nat.Coprime a (∏ c ∈ mset r, c)
    refine coprime_prod_of_pairwise_notMem A hpair (mset r) (hmset_mem r) haA ?_
    by_cases h : r = K + 1
    · subst h
      rw [hmK1smalls]
      intro hmem
      have := (hsmalls_mem a hmem).2.2
      omega
    · rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
      have hrK : r ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hr1, by omega⟩
      rw [hmsetblock r hrK]
      intro hmem
      exact hanb (Finset.mem_biUnion.mpr ⟨r, hrK, hmem⟩)
  -- the second tail cut, the window length, and the averaging range
  have hεY : (0:ℝ) < 1 / (64 * ((K:ℝ)+1) * ((M:ℝ)+1)) := by positivity
  obtain ⟨BY, hBY⟩ := htail _ hεY
  set Y₀ : ℕ := BY + x + K + 64 with hY₀def
  obtain ⟨L, hLge, hLarith⟩ := exists_linear_lt_pow b
    (2*q*(x + Y₀ * M + 2)) (2*q*(M+1)) (B₀ + K + 2) hb
  set Y : ℕ := Y₀ + L with hYdef
  have hKL : K ≤ L := by omega
  have hYpos : 0 < Y := by omega
  set X : ℕ := x + Y * M + L with hXdef
  -- the stray candidate set
  set SC : Finset ℕ := ((Finset.Ioc B₀ X).filter (· ∈ A)) \ blocksU with hSCdef
  have hSC_mem : ∀ a ∈ SC, a ∈ A ∧ B₀ < a ∧ a ≤ X ∧ a ∉ blocksU := by
    intro a ha
    obtain ⟨hf, hnb⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hIoc, hA'⟩ := Finset.mem_filter.mp hf
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hIoc
    exact ⟨hA', h1, h2, hnb⟩
  have hSC_pos : ∀ a ∈ SC, 0 < a := by
    intro a ha
    have := (hSC_mem a ha).2.1
    omega
  have hSC_cop : ∀ a ∈ SC, Nat.Coprime a M := fun a ha =>
    hstray_cop a (hSC_mem a ha).1 (hSC_mem a ha).2.1 (hSC_mem a ha).2.2.2
  -- the single hit-count budget
  set INNER : ℕ := ∑ a ∈ SC, (Y / a + 1) with hINNERdef
  have hINNER_bound : (INNER : ℝ) ≤ (Y : ℝ) / (16 * ((K:ℝ)+1)) := by
    have hsplit : INNER = (∑ a ∈ SC.filter (· ≤ Y), (Y / a + 1))
        + ∑ a ∈ SC.filter (fun a => ¬ a ≤ Y), (Y / a + 1) :=
      (Finset.sum_filter_add_sum_filter_not SC (· ≤ Y) _).symm
    have hsmall_nat : (∑ a ∈ SC.filter (· ≤ Y), (Y / a + 1))
        ≤ ∑ a ∈ SC.filter (· ≤ Y), 2 * (Y / a) := by
      refine Finset.sum_le_sum fun a ha => ?_
      have hmem := Finset.mem_filter.mp ha
      have hpos := hSC_pos a hmem.1
      have h1 : 1 ≤ Y / a := (Nat.one_le_div_iff hpos).mpr hmem.2
      omega
    have hsmall_cast : ((∑ a ∈ SC.filter (· ≤ Y), 2 * (Y / a) : ℕ) : ℝ)
        ≤ 2 * (Y : ℝ) * ∑ a ∈ SC.filter (· ≤ Y), (1:ℝ)/a := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a ha => ?_
      have hcast : ((Y / a : ℕ) : ℝ) ≤ (Y : ℝ) / (a : ℝ) := Nat.cast_div_le
      calc (2 : ℝ) * ((Y / a : ℕ) : ℝ) ≤ 2 * ((Y:ℝ) / (a:ℝ)) := by linarith
        _ = 2 * (Y:ℝ) * ((1:ℝ)/(a:ℝ)) := by ring
    have hsmall_tail : ∑ a ∈ SC.filter (· ≤ Y), (1:ℝ)/a
        ≤ 1 / (64 * ((K:ℝ) + 1)) := by
      refine hB₀tail _ fun a ha => ?_
      have hmem := Finset.mem_filter.mp ha
      exact ⟨(hSC_mem a hmem.1).1, (hSC_mem a hmem.1).2.1⟩
    have hbig_nat : (∑ a ∈ SC.filter (fun a => ¬ a ≤ Y), (Y / a + 1))
        = (SC.filter (fun a => ¬ a ≤ Y)).card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hmem := Finset.mem_filter.mp ha
      have hYa : Y < a := by omega
      rw [Nat.div_eq_of_lt hYa]
    have hbig_card : ((SC.filter (fun a => ¬ a ≤ Y)).card : ℝ)
        ≤ (X : ℝ) * ∑ a ∈ SC.filter (fun a => ¬ a ≤ Y), (1:ℝ)/a := by
      refine card_le_mul_sum_inv X _ fun a ha => ?_
      have hmem := Finset.mem_filter.mp ha
      exact ⟨hSC_pos a hmem.1, (hSC_mem a hmem.1).2.2.1⟩
    have hbig_tail : ∑ a ∈ SC.filter (fun a => ¬ a ≤ Y), (1:ℝ)/a
        ≤ 1 / (64 * ((K:ℝ)+1) * ((M:ℝ)+1)) := by
      refine hBY _ fun a ha => ?_
      have hmem := Finset.mem_filter.mp ha
      refine ⟨(hSC_mem a hmem.1).1, ?_⟩
      have h1 : ¬ a ≤ Y := hmem.2
      omega
    have hXle : (X : ℝ) ≤ (Y : ℝ) * ((M : ℝ) + 2) := by
      have hXnat : X ≤ Y * (M + 2) := by
        have hexp : Y * (M + 2) = Y * M + Y + Y := by ring
        omega
      calc (X : ℝ) ≤ ((Y * (M + 2) : ℕ) : ℝ) := by exact_mod_cast hXnat
        _ = (Y : ℝ) * ((M : ℝ) + 2) := by push_cast; ring
    have hKne : ((K:ℝ)+1) ≠ 0 := by positivity
    have hMne : ((M:ℝ)+1) ≠ 0 := by positivity
    have hYr : (0:ℝ) ≤ (Y:ℝ) := by positivity
    have c1 : ((∑ a ∈ SC.filter (· ≤ Y), (Y / a + 1) : ℕ) : ℝ)
        ≤ 2 * (Y:ℝ) * (1 / (64 * ((K:ℝ)+1))) := by
      calc ((∑ a ∈ SC.filter (· ≤ Y), (Y / a + 1) : ℕ) : ℝ)
          ≤ ((∑ a ∈ SC.filter (· ≤ Y), 2 * (Y / a) : ℕ) : ℝ) := by
            exact_mod_cast hsmall_nat
        _ ≤ 2 * (Y : ℝ) * ∑ a ∈ SC.filter (· ≤ Y), (1:ℝ)/a := hsmall_cast
        _ ≤ 2 * (Y:ℝ) * (1 / (64 * ((K:ℝ)+1))) :=
            mul_le_mul_of_nonneg_left hsmall_tail (by positivity)
    have c2 : ((∑ a ∈ SC.filter (fun a => ¬ a ≤ Y), (Y / a + 1) : ℕ) : ℝ)
        ≤ (Y:ℝ) * ((M:ℝ)+2) * (1 / (64 * ((K:ℝ)+1) * ((M:ℝ)+1))) := by
      calc ((∑ a ∈ SC.filter (fun a => ¬ a ≤ Y), (Y / a + 1) : ℕ) : ℝ)
          = ((SC.filter (fun a => ¬ a ≤ Y)).card : ℝ) := by rw [hbig_nat]
        _ ≤ (X : ℝ) * ∑ a ∈ SC.filter (fun a => ¬ a ≤ Y), (1:ℝ)/a := hbig_card
        _ ≤ (X : ℝ) * (1 / (64 * ((K:ℝ)+1) * ((M:ℝ)+1))) := by
            refine mul_le_mul_of_nonneg_left hbig_tail ?_
            positivity
        _ ≤ (Y:ℝ) * ((M:ℝ)+2) * (1 / (64 * ((K:ℝ)+1) * ((M:ℝ)+1))) :=
            mul_le_mul_of_nonneg_right hXle (by positivity)
    have hcast_split : (INNER : ℝ)
        = ((∑ a ∈ SC.filter (· ≤ Y), (Y / a + 1) : ℕ) : ℝ)
          + ((∑ a ∈ SC.filter (fun a => ¬ a ≤ Y), (Y / a + 1) : ℕ) : ℝ) := by
      exact_mod_cast hsplit
    have h1 : (M:ℝ) + 2 ≤ 2 * ((M:ℝ) + 1) := by linarith
    have h2 : (Y:ℝ) * ((M:ℝ)+2) * (1 / (64 * ((K:ℝ)+1) * ((M:ℝ)+1)))
        ≤ (Y:ℝ) * (2 * ((M:ℝ)+1)) * (1 / (64 * ((K:ℝ)+1) * ((M:ℝ)+1))) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left h1 hYr
    have h3 : (Y:ℝ) * (2 * ((M:ℝ)+1)) * (1 / (64 * ((K:ℝ)+1) * ((M:ℝ)+1)))
        = (Y:ℝ) / (32 * ((K:ℝ)+1)) := by
      field_simp
      all_goals ring
    have h4 : 2 * (Y:ℝ) * (1 / (64 * ((K:ℝ)+1))) = (Y:ℝ) / (32 * ((K:ℝ)+1)) := by
      field_simp
      all_goals ring
    have h5 : (Y:ℝ) / (32 * ((K:ℝ)+1)) + (Y:ℝ) / (32 * ((K:ℝ)+1))
        = (Y:ℝ) / (16 * ((K:ℝ)+1)) := by
      field_simp
      all_goals ring
    linarith
  -- exact per-residue progression counting
  have hAP : ∀ a ∈ SC, ∀ c : ℕ,
      ((Finset.range Y).filter (fun y => a ∣ x + y * M + c)).card ≤ Y / a + 1 := by
    intro a ha c
    have hcount := card_filter_dvd_progression_le M (x + c) a Y
      (hSC_pos a ha) (hSC_cop a ha)
    have heq : ((Finset.range Y).filter (fun y => a ∣ x + y * M + c))
        = ((Finset.range Y).filter (fun y => a ∣ M * y + (x + c))) := by
      refine Finset.filter_congr fun y _ => ?_
      rw [show M * y + (x + c) = x + y * M + c from by ring]
    rw [heq]
    exact hcount
  -- the two bad windows
  set bf : Finset ℕ := (Finset.range Y).filter
    (fun y => ∃ r ∈ Finset.Icc 1 K, ∃ a ∈ SC, a ∣ x + y * M + r) with hbfdef
  set strayN : ℕ → ℕ := fun y => ∑ s ∈ Finset.Icc (K+1) L,
    (SC.filter (· ∣ x + y * M + s)).card * b ^ (L - s) with hstrayNdef
  set bm : Finset ℕ := (Finset.range Y).filter
    (fun y => b ^ (L - K) < strayN y) with hbmdef
  have hbf_card : bf.card ≤ K * INNER := by
    have hsub : bf ⊆ (Finset.Icc 1 K).biUnion (fun r => SC.biUnion
        (fun a => (Finset.range Y).filter (fun y => a ∣ x + y * M + r))) := by
      intro y hy
      obtain ⟨hyY, r, hr, a, haSC, hdvd⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_biUnion.mpr ⟨a, haSC,
        Finset.mem_filter.mpr ⟨hyY, hdvd⟩⟩⟩
    calc bf.card ≤ ((Finset.Icc 1 K).biUnion (fun r => SC.biUnion
          (fun a => (Finset.range Y).filter (fun y => a ∣ x + y * M + r)))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ r ∈ Finset.Icc 1 K, (SC.biUnion
          (fun a => (Finset.range Y).filter (fun y => a ∣ x + y * M + r))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ r ∈ Finset.Icc 1 K, ∑ a ∈ SC,
          ((Finset.range Y).filter (fun y => a ∣ x + y * M + r)).card :=
          Finset.sum_le_sum fun r _ => Finset.card_biUnion_le
      _ ≤ ∑ r ∈ Finset.Icc 1 K, INNER := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [hINNERdef]
          exact Finset.sum_le_sum fun a ha => hAP a ha r
      _ = K * INNER := by
          rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
  have hstray_total : ∑ y ∈ Finset.range Y, strayN y ≤ b ^ (L - K) * INNER := by
    have hswap : ∀ s : ℕ, ∑ y ∈ Finset.range Y, (SC.filter (· ∣ x + y * M + s)).card
        = ∑ a ∈ SC, ((Finset.range Y).filter (fun y => a ∣ x + y * M + s)).card := by
      intro s
      calc ∑ y ∈ Finset.range Y, (SC.filter (· ∣ x + y * M + s)).card
          = ∑ y ∈ Finset.range Y, ∑ a ∈ SC,
              (if a ∣ x + y * M + s then 1 else 0) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.card_filter]
        _ = ∑ a ∈ SC, ∑ y ∈ Finset.range Y,
              (if a ∣ x + y * M + s then 1 else 0) := Finset.sum_comm
        _ = ∑ a ∈ SC, ((Finset.range Y).filter
              (fun y => a ∣ x + y * M + s)).card := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.card_filter]
    calc ∑ y ∈ Finset.range Y, strayN y
        = ∑ s ∈ Finset.Icc (K+1) L, ∑ y ∈ Finset.range Y,
            (SC.filter (· ∣ x + y * M + s)).card * b ^ (L - s) := Finset.sum_comm
      _ = ∑ s ∈ Finset.Icc (K+1) L, (∑ y ∈ Finset.range Y,
            (SC.filter (· ∣ x + y * M + s)).card) * b ^ (L - s) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_mul]
      _ ≤ ∑ s ∈ Finset.Icc (K+1) L, INNER * b ^ (L - s) := by
          refine Finset.sum_le_sum fun s _ => ?_
          refine Nat.mul_le_mul_right _ ?_
          rw [hswap s, hINNERdef]
          exact Finset.sum_le_sum fun a ha => hAP a ha s
      _ = INNER * ∑ s ∈ Finset.Icc (K+1) L, b ^ (L - s) := by
          rw [Finset.mul_sum]
      _ ≤ INNER * b ^ (L - K) :=
          Nat.mul_le_mul_left _ (sum_pow_weight_middle_window_le b K L hb)
      _ = b ^ (L - K) * INNER := Nat.mul_comm _ _
  have hbm_card : bm.card ≤ INNER := by
    have hw : 0 < b ^ (L-K) + 1 := by omega
    have hlow : (b ^ (L-K) + 1) * bm.card ≤ ∑ y ∈ Finset.range Y, strayN y := by
      rw [Nat.mul_comm]
      calc bm.card * (b ^ (L-K) + 1) = bm.card • (b ^ (L-K) + 1) :=
            (smul_eq_mul _ _).symm
        _ ≤ ∑ y ∈ bm, strayN y := by
            refine Finset.card_nsmul_le_sum bm strayN _ fun y hy => ?_
            have := (Finset.mem_filter.mp hy).2
            omega
        _ ≤ ∑ y ∈ Finset.range Y, strayN y :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hup : (b ^ (L-K) + 1) * bm.card ≤ (b ^ (L-K) + 1) * INNER := by
      refine le_trans (le_trans hlow hstray_total) ?_
      exact Nat.mul_le_mul_right INNER (by omega)
    exact Nat.le_of_mul_le_mul_left hup hw
  -- select a good averaging point
  have hgood : ∃ y, y ∈ Finset.range Y \ (bf ∪ bm) := by
    have h1 : (bf ∪ bm).card ≤ K * INNER + INNER :=
      le_trans (Finset.card_union_le _ _) (by omega)
    have h2 : ((bf ∪ bm).card : ℝ) ≤ ((K:ℝ) + 1) * (INNER:ℝ) := by
      calc ((bf ∪ bm).card : ℝ) ≤ ((K * INNER + INNER : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ = ((K:ℝ) + 1) * (INNER:ℝ) := by push_cast; ring
    have h3 : ((K:ℝ)+1) * (INNER:ℝ)
        ≤ ((K:ℝ)+1) * ((Y:ℝ) / (16 * ((K:ℝ)+1))) :=
      mul_le_mul_of_nonneg_left hINNER_bound (by positivity)
    have hKne : ((K:ℝ)+1) ≠ 0 := by positivity
    have h4 : ((K:ℝ)+1) * ((Y:ℝ) / (16 * ((K:ℝ)+1))) = (Y:ℝ) / 16 := by
      field_simp
      all_goals ring
    have hY1 : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hYpos
    have h5 : (Y:ℝ) / 16 < (Y:ℝ) := by linarith
    have hlt : (bf ∪ bm).card < Y := by
      have : ((bf ∪ bm).card : ℝ) < (Y : ℝ) := by linarith
      exact_mod_cast this
    have h6 := Finset.le_card_sdiff (bf ∪ bm) (Finset.range Y)
    rw [Finset.card_range] at h6
    have hpos : 0 < (Finset.range Y \ (bf ∪ bm)).card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    exact ⟨y, hy⟩
  obtain ⟨y, hy_mem⟩ := hgood
  obtain ⟨hyY, hy_notbad⟩ := Finset.mem_sdiff.mp hy_mem
  have hyY' : y < Y := Finset.mem_range.mp hyY
  have hy_nbf : y ∉ bf := fun h => hy_notbad (Finset.mem_union_left _ h)
  have hy_nbm : y ∉ bm := fun h => hy_notbad (Finset.mem_union_right _ h)
  have hno_stray_first : ∀ r ∈ Finset.Icc 1 K, ∀ a ∈ SC,
      ¬ a ∣ x + y * M + r := by
    intro r hr a ha hdvd
    exact hy_nbf (Finset.mem_filter.mpr ⟨hyY, ⟨r, hr, a, ha, hdvd⟩⟩)
  have hstrayN_le : strayN y ≤ b ^ (L - K) := by
    by_contra hcon
    push Not at hcon
    exact hy_nbm (Finset.mem_filter.mpr ⟨hyY, hcon⟩)
  set N : ℕ := x + y * M with hNdef
  -- first block: exact adaptive counts
  have hfirst : ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ supportCoeff A (N + r) := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrK⟩
    have hFdisj : Disjoint (smalls.filter (· ∣ r)) (P r) := by
      rw [Finset.disjoint_left]
      intro a ha haP
      have h1 := (hsmalls_mem a (Finset.mem_filter.mp ha).1).2.2
      have h2 := (hPA r a haP).2
      omega
    have hsupp_eq : supportCoeff A (N + r)
        = (smalls.filter (· ∣ r) ∪ P r).card := by
      refine supportCoeff_eq_card_of_forced_of_no_strays A _ (N + r)
        (by omega) ?_ ?_ ?_
      · intro a ha
        rcases Finset.mem_union.mp ha with h | h
        · exact (hsmalls_mem a (Finset.mem_filter.mp h).1).1
        · exact (hPA r a h).1
      · intro a ha
        rcases Finset.mem_union.mp ha with h | h
        · obtain ⟨hs, hdr⟩ := Finset.mem_filter.mp h
          have h1 : a ∣ x := hsmalls_dvd_x a hs
          have h2 : a ∣ y * M := (hsmalls_dvd_M a hs).mul_left y
          show a ∣ x + y * M + r
          exact dvd_add (dvd_add h1 h2) hdr
        · have h1 : a ∣ x + r := hblock_dvd_slot r hr a h
          have h2 : a ∣ M := hblocks_dvd_M r hr a h
          show a ∣ x + y * M + r
          rw [show x + y * M + r = (x + r) + y * M from by ring]
          exact dvd_add h1 (h2.mul_left y)
      · intro dd hdvd hddA
        by_cases hsmall : dd ≤ B₀
        · have hdd1 : 1 ≤ dd := by
            rcases Nat.eq_zero_or_pos dd with h0 | h
            · exfalso
              subst h0
              have h1 := Nat.eq_zero_of_zero_dvd hdvd
              omega
            · omega
          have hddS : dd ∈ smalls := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hdd1, hsmall⟩, hddA⟩
          have h1 : dd ∣ x := hsmalls_dvd_x dd hddS
          have h2 : dd ∣ y * M := (hsmalls_dvd_M dd hddS).mul_left y
          have h3 : dd ∣ x + y * M := dvd_add h1 h2
          have h4 : dd ∣ r := (Nat.dvd_add_right h3).mp hdvd
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hddS, h4⟩)
        · push Not at hsmall
          by_cases hblk : dd ∈ blocksU
          · obtain ⟨r', hr', hddP⟩ := Finset.mem_biUnion.mp hblk
            by_cases hrr : r' = r
            · subst hrr
              exact Finset.mem_union_right _ hddP
            · exfalso
              have h1 : dd ∣ x + r' := hblock_dvd_slot r' hr' dd hddP
              have h2 : dd ∣ M := hblocks_dvd_M r' hr' dd hddP
              have h3 : dd ∣ x + y * M + r' := by
                rw [show x + y * M + r' = (x + r') + y * M from by ring]
                exact dvd_add h1 (h2.mul_left y)
              rcases Finset.mem_Icc.mp hr' with ⟨hr'1, hr'K⟩
              have h4 := (hPA r' dd hddP).2
              rcases Nat.lt_or_ge r r' with hlt | hge
              · have h5 : dd ∣ (x + y * M + r') - (x + y * M + r) :=
                  Nat.dvd_sub h3 hdvd
                have heq : (x + y * M + r') - (x + y * M + r) = r' - r := by
                  omega
                rw [heq] at h5
                have h6 : dd ≤ r' - r := Nat.le_of_dvd (by omega) h5
                omega
              · have hgt : r' < r := by omega
                have h5 : dd ∣ (x + y * M + r) - (x + y * M + r') :=
                  Nat.dvd_sub hdvd h3
                have heq : (x + y * M + r) - (x + y * M + r') = r - r' := by
                  omega
                rw [heq] at h5
                have h6 : dd ≤ r - r' := Nat.le_of_dvd (by omega) h5
                omega
          · exfalso
            have hddX : dd ≤ X := by
              have h1 : dd ≤ N + r := Nat.le_of_dvd (by omega) hdvd
              have h2 : y * M ≤ Y * M := Nat.mul_le_mul_right M (by omega)
              omega
            have hddSC : dd ∈ SC := by
              rw [hSCdef]
              exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
                ⟨Finset.mem_Ioc.mpr ⟨hsmall, hddX⟩, hddA⟩, hblk⟩
            exact hno_stray_first r hr dd hddSC hdvd
    have hcard : (smalls.filter (· ∣ r) ∪ P r).card = d r + sz r := by
      rw [Finset.card_union_of_disjoint hFdisj]
      congr 1
      exact hPcard r hr
    have hdvd_sum : b ^ r ∣ d r + sz r := by
      have hbr_pos : 0 < b ^ r := pow_pos (by omega) r
      have hdm := Nat.div_add_mod (d r) (b ^ r)
      have hmod_lt : d r % b ^ r < b ^ r := Nat.mod_lt _ hbr_pos
      refine ⟨d r / b ^ r + 1, ?_⟩
      have hexp : b ^ r * (d r / b ^ r + 1) = b ^ r * (d r / b ^ r) + b ^ r := by
        ring
      show d r + (b ^ r - d r % b ^ r) = b ^ r * (d r / b ^ r + 1)
      omega
    rw [hsupp_eq, hcard]
    exact hdvd_sum
  -- far-tail positivity from infinitude
  have hfar : ∃ t : ℕ, 0 < supportCoeff A (N + L + 1 + t) := by
    have hinf2 : (A \ {a : ℕ | a ≤ N + L + 1}).Infinite :=
      hA.diff (Set.finite_le_nat _)
    obtain ⟨a₀, ha₀⟩ := hinf2.nonempty
    rw [Set.mem_diff, Set.mem_setOf_eq] at ha₀
    obtain ⟨ha₀A, ha₀gt⟩ := ha₀
    push Not at ha₀gt
    refine ⟨a₀ - (N + L + 1), ?_⟩
    have hidx : N + L + 1 + (a₀ - (N + L + 1)) = a₀ := by omega
    rw [hidx]
    exact supportCoeff_pos_of_mem_dvd A ha₀A dvd_rfl (by omega)
  -- the middle window
  set MF : Finset ℕ := smalls ∪ blocksU with hMFdef
  have hmid : ∀ s ∈ Finset.Icc (K+1) L,
      supportCoeff A (N + s) ≤ (smalls.filter (· ∣ s)).card
        + (blocksU.filter (· ∣ x + s)).card
        + (SC.filter (· ∣ x + y * M + s)).card := by
    intro s hs
    rcases Finset.mem_Icc.mp hs with ⟨hs1, hs2⟩
    have hpart1 : supportCoeff (A ∩ ↑MF) (N + s)
        ≤ (smalls.filter (· ∣ s)).card + (blocksU.filter (· ∣ x + s)).card := by
      rw [supportCoeff_eq_card_filter]
      have hsub : ((N + s).divisors.filter (· ∈ A ∩ ↑MF))
          ⊆ (smalls.filter (· ∣ s)) ∪ (blocksU.filter (· ∣ x + s)) := by
        intro dd hdd
        obtain ⟨hdiv, hmem⟩ := Finset.mem_filter.mp hdd
        obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hdiv
        obtain ⟨hddA, hddMF⟩ := hmem
        have hddMF' : dd ∈ MF := Finset.mem_coe.mp hddMF
        rcases Finset.mem_union.mp hddMF' with hS | hB
        · have h1 : dd ∣ x := hsmalls_dvd_x dd hS
          have h2 : dd ∣ y * M := (hsmalls_dvd_M dd hS).mul_left y
          have h3 : dd ∣ x + y * M := dvd_add h1 h2
          have h4 : dd ∣ s := (Nat.dvd_add_right h3).mp hdvd
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS, h4⟩)
        · obtain ⟨r', hr', hddP⟩ := Finset.mem_biUnion.mp hB
          have h2 : dd ∣ y * M := (hblocks_dvd_M r' hr' dd hddP).mul_left y
          have h7 : dd ∣ y * M + (x + s) := by
            rw [show y * M + (x + s) = x + y * M + s from by ring]
            exact hdvd
          have h4 : dd ∣ x + s := (Nat.dvd_add_right h2).mp h7
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hB, h4⟩)
      calc ((N + s).divisors.filter (· ∈ A ∩ ↑MF)).card
          ≤ ((smalls.filter (· ∣ s)) ∪ (blocksU.filter (· ∣ x + s))).card :=
            Finset.card_le_card hsub
        _ ≤ _ := Finset.card_union_le _ _
    have hpart2 : supportCoeff (A \ ↑MF) (N + s)
        ≤ (SC.filter (· ∣ x + y * M + s)).card := by
      rw [supportCoeff_eq_card_filter]
      refine Finset.card_le_card ?_
      intro dd hdd
      obtain ⟨hdiv, hmem⟩ := Finset.mem_filter.mp hdd
      obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hdiv
      obtain ⟨hddA, hddMF⟩ := hmem
      have hddnotMF : dd ∉ MF := fun h => hddMF (Finset.mem_coe.mpr h)
      have hdd_pos : 0 < dd := by
        rcases Nat.eq_zero_or_pos dd with h0 | h
        · exfalso
          subst h0
          have h1 := Nat.eq_zero_of_zero_dvd hdvd
          omega
        · exact h
      have hddB₀ : B₀ < dd := by
        by_contra hcon
        push Not at hcon
        refine hddnotMF (Finset.mem_union_left _ ?_)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨by omega, hcon⟩, hddA⟩
      have hddnb : dd ∉ blocksU := fun h =>
        hddnotMF (Finset.mem_union_right _ h)
      have hddX : dd ≤ X := by
        have h1 : dd ≤ N + s := Nat.le_of_dvd (by omega) hdvd
        have h2 : y * M ≤ Y * M := Nat.mul_le_mul_right M (by omega)
        omega
      refine Finset.mem_filter.mpr ⟨?_, hdvd⟩
      rw [hSCdef]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hddB₀, hddX⟩, hddA⟩, hddnb⟩
    have hsplit := supportCoeff_eq_inter_add_diff A MF (N + s)
    omega
  -- deterministic small-element leak
  have hswap_leak : ∀ (G : Finset ℕ) (g : ℕ → ℕ → Prop)
      [∀ a s, Decidable (g a s)],
      ∑ s ∈ Finset.Icc (K+1) L, (G.filter (fun a => g a s)).card * b ^ (L - s)
        = ∑ a ∈ G, ∑ s ∈ (Finset.Icc (K+1) L).filter (fun s => g a s),
            b ^ (L - s) := by
    intro G g _
    calc ∑ s ∈ Finset.Icc (K+1) L, (G.filter (fun a => g a s)).card * b ^ (L - s)
        = ∑ s ∈ Finset.Icc (K+1) L, ∑ a ∈ G,
            (if g a s then 1 else 0) * b ^ (L - s) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.card_filter, Finset.sum_mul]
      _ = ∑ a ∈ G, ∑ s ∈ Finset.Icc (K+1) L,
            (if g a s then 1 else 0) * b ^ (L - s) := Finset.sum_comm
      _ = ∑ a ∈ G, ∑ s ∈ Finset.Icc (K+1) L,
            (if g a s then b ^ (L - s) else 0) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
          by_cases h : g a s
          · rw [if_pos h, if_pos h, one_mul]
          · rw [if_neg h, if_neg h, zero_mul]
      _ = ∑ a ∈ G, ∑ s ∈ (Finset.Icc (K+1) L).filter (fun s => g a s),
            b ^ (L - s) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_filter]
  have hsmall_leak : ∑ s ∈ Finset.Icc (K+1) L,
      (smalls.filter (· ∣ s)).card * b ^ (L - s)
      ≤ K * b ^ (L - K) + b ^ (L - K + 1) := by
    rw [hswap_leak smalls (fun a s => a ∣ s)]
    have hper : ∀ a ∈ smalls,
        ∑ s ∈ (Finset.Icc (K+1) L).filter (fun s => a ∣ s), b ^ (L - s)
          ≤ b ^ (L + 1 - max (K + 1) a) := by
      intro a ha
      refine sum_pow_weight_window_hits_le b K L (max (K+1) a) hb
        (le_max_left _ _) _ ?_
      intro s hs
      obtain ⟨hwin, hdvd⟩ := Finset.mem_filter.mp hs
      refine ⟨hwin, ?_⟩
      have hs1 := (Finset.mem_Icc.mp hwin).1
      have haS : a ≤ s := Nat.le_of_dvd (by omega) hdvd
      exact max_le (by omega) haS
    calc ∑ a ∈ smalls, ∑ s ∈ (Finset.Icc (K+1) L).filter (fun s => a ∣ s),
          b ^ (L - s)
        ≤ ∑ a ∈ smalls, b ^ (L + 1 - max (K + 1) a) := Finset.sum_le_sum hper
      _ = (∑ a ∈ smalls.filter (· ≤ K), b ^ (L + 1 - max (K + 1) a))
          + ∑ a ∈ smalls.filter (fun a => ¬ a ≤ K), b ^ (L + 1 - max (K + 1) a) :=
          (Finset.sum_filter_add_sum_filter_not smalls (· ≤ K) _).symm
      _ ≤ K * b ^ (L - K) + b ^ (L - K + 1) := by
          have hle1 : ∑ a ∈ smalls.filter (· ≤ K), b ^ (L + 1 - max (K + 1) a)
              ≤ K * b ^ (L - K) := by
            have hcard : (smalls.filter (· ≤ K)).card ≤ K := by
              have hsub : smalls.filter (· ≤ K) ⊆ Finset.Icc 1 K := by
                intro a ha
                obtain ⟨haS, haK⟩ := Finset.mem_filter.mp ha
                exact Finset.mem_Icc.mpr ⟨(hsmalls_mem a haS).2.1, haK⟩
              calc (smalls.filter (· ≤ K)).card ≤ (Finset.Icc 1 K).card :=
                    Finset.card_le_card hsub
                _ = K := by rw [Nat.card_Icc]; omega
            calc ∑ a ∈ smalls.filter (· ≤ K), b ^ (L + 1 - max (K + 1) a)
                ≤ ∑ _a ∈ smalls.filter (· ≤ K), b ^ (L - K) := by
                  refine Finset.sum_le_sum fun a ha => ?_
                  have haK := (Finset.mem_filter.mp ha).2
                  have hmax : max (K+1) a = K + 1 := max_eq_left (by omega)
                  rw [hmax, show L + 1 - (K + 1) = L - K from by omega]
              _ = (smalls.filter (· ≤ K)).card * b ^ (L - K) := by
                  rw [Finset.sum_const, smul_eq_mul]
              _ ≤ K * b ^ (L - K) := Nat.mul_le_mul_right _ hcard
          have hle2 : ∑ a ∈ smalls.filter (fun a => ¬ a ≤ K),
              b ^ (L + 1 - max (K + 1) a) ≤ b ^ (L - K + 1) := by
            calc ∑ a ∈ smalls.filter (fun a => ¬ a ≤ K),
                  b ^ (L + 1 - max (K + 1) a)
                ≤ ∑ a ∈ Finset.Ioc K B₀, b ^ (L + 1 - max (K + 1) a) := by
                  refine Finset.sum_le_sum_of_subset ?_
                  intro a ha
                  obtain ⟨haS, haK⟩ := Finset.mem_filter.mp ha
                  refine Finset.mem_Ioc.mpr ⟨by omega, (hsmalls_mem a haS).2.2⟩
              _ = ∑ a ∈ Finset.Ioc K B₀, b ^ (L + 1 - a) := by
                  refine Finset.sum_congr rfl fun a ha => ?_
                  have h1 := (Finset.mem_Ioc.mp ha).1
                  rw [max_eq_right (by omega : K + 1 ≤ a)]
              _ ≤ b ^ (L - K + 1) := by
                  have hIocIco : Finset.Ioc K B₀ = Finset.Ico (K+1) (B₀+1) := by
                    ext a
                    simp only [Finset.mem_Ioc, Finset.mem_Ico]
                    omega
                  rw [hIocIco, Finset.sum_Ico_eq_sum_range,
                    show B₀ + 1 - (K + 1) = B₀ - K from by omega]
                  have hterm : ∀ i ∈ Finset.range (B₀ - K),
                      b ^ (L + 1 - (K + 1 + i)) = b ^ (L - K - i) := by
                    intro i _
                    congr 1
                    omega
                  rw [Finset.sum_congr rfl hterm]
                  have hBL : B₀ - K ≤ L - K + 1 := by omega
                  calc ∑ i ∈ Finset.range (B₀ - K), b ^ (L - K - i)
                      ≤ ∑ i ∈ Finset.range (L - K + 1), b ^ (L - K - i) := by
                        refine Finset.sum_le_sum_of_subset ?_
                        intro i hi
                        have := Finset.mem_range.mp hi
                        exact Finset.mem_range.mpr (by omega)
                    _ = ∑ i ∈ Finset.range (L - K + 1), b ^ i := by
                        calc ∑ i ∈ Finset.range (L - K + 1), b ^ (L - K - i)
                            = ∑ i ∈ Finset.range (L - K + 1),
                                b ^ (L - K + 1 - 1 - i) := by
                              refine Finset.sum_congr rfl fun i _ => ?_
                              congr 1 <;> omega
                          _ = ∑ i ∈ Finset.range (L - K + 1), b ^ i :=
                              Finset.sum_range_reflect (fun j => b ^ j) (L - K + 1)
                    _ ≤ b ^ (L - K + 1) := geom_sum_range_le_pow b (L - K + 1) hb
          omega
  -- deterministic block leak
  have hblock_leak : ∑ s ∈ Finset.Icc (K+1) L,
      (blocksU.filter (· ∣ x + s)).card * b ^ (L - s) ≤ b ^ (L - K) := by
    rw [hswap_leak blocksU (fun a s => a ∣ x + s)]
    have hper : ∀ a ∈ blocksU,
        ∑ s ∈ (Finset.Icc (K+1) L).filter (fun s => a ∣ x + s), b ^ (L - s)
          ≤ b ^ (L + 1 - (B₀ + 2)) := by
      intro a ha
      obtain ⟨r', hr', haP⟩ := Finset.mem_biUnion.mp ha
      refine sum_pow_weight_window_hits_le b K L (B₀ + 2) hb (by omega) _ ?_
      intro s hs
      obtain ⟨hwin, hdvd⟩ := Finset.mem_filter.mp hs
      refine ⟨hwin, ?_⟩
      have h1 : a ∣ x + r' := hblock_dvd_slot r' hr' a haP
      have hs1 := (Finset.mem_Icc.mp hwin).1
      rcases Finset.mem_Icc.mp hr' with ⟨hr'1, hr'K⟩
      have h2 : a ∣ (x + s) - (x + r') := Nat.dvd_sub hdvd h1
      have heq : (x + s) - (x + r') = s - r' := by omega
      rw [heq] at h2
      have h3 : a ≤ s - r' := Nat.le_of_dvd (by omega) h2
      have h4 := (hPA r' a haP).2
      omega
    have hcard_blocks : blocksU.card ≤ b ^ (K + 1) := by
      calc blocksU.card ≤ ∑ r ∈ Finset.Icc 1 K, (P r).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ r ∈ Finset.Icc 1 K, b ^ r := by
            refine Finset.sum_le_sum fun r hr => ?_
            rw [hPcard r hr]
            show b ^ r - d r % b ^ r ≤ b ^ r
            exact Nat.sub_le _ _
        _ ≤ ∑ r ∈ Finset.range (K + 1), b ^ r := by
            refine Finset.sum_le_sum_of_subset ?_
            intro r hr
            rcases Finset.mem_Icc.mp hr with ⟨h1, h2⟩
            exact Finset.mem_range.mpr (by omega)
        _ ≤ b ^ (K + 1) := geom_sum_range_le_pow b (K + 1) hb
    calc ∑ a ∈ blocksU, ∑ s ∈ (Finset.Icc (K+1) L).filter
          (fun s => a ∣ x + s), b ^ (L - s)
        ≤ ∑ _a ∈ blocksU, b ^ (L + 1 - (B₀ + 2)) := Finset.sum_le_sum hper
      _ = blocksU.card * b ^ (L + 1 - (B₀ + 2)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ b ^ (K + 1) * b ^ (L + 1 - (B₀ + 2)) :=
          Nat.mul_le_mul_right _ hcard_blocks
      _ = b ^ (K + 1 + (L + 1 - (B₀ + 2))) := (pow_add b _ _).symm
      _ ≤ b ^ (L - K) := by
          refine Nat.pow_le_pow_right (by omega) ?_
          omega
  -- assemble the middle certificate
  set C : ℕ := (K + b + 2) * b ^ (L - K) with hCdef
  have hmiddle : ∑ s ∈ Finset.Icc (K + 1) L,
      supportCoeff A (N + s) * b ^ (L - s) ≤ C := by
    have h1 : ∑ s ∈ Finset.Icc (K+1) L, supportCoeff A (N + s) * b ^ (L - s)
        ≤ ∑ s ∈ Finset.Icc (K+1) L,
            ((smalls.filter (· ∣ s)).card + (blocksU.filter (· ∣ x + s)).card
              + (SC.filter (· ∣ x + y * M + s)).card) * b ^ (L - s) :=
      Finset.sum_le_sum fun s hs => Nat.mul_le_mul_right _ (hmid s hs)
    have hdist : ∑ s ∈ Finset.Icc (K+1) L,
        ((smalls.filter (· ∣ s)).card + (blocksU.filter (· ∣ x + s)).card
          + (SC.filter (· ∣ x + y * M + s)).card) * b ^ (L - s)
        = (∑ s ∈ Finset.Icc (K+1) L, (smalls.filter (· ∣ s)).card * b ^ (L - s))
          + (∑ s ∈ Finset.Icc (K+1) L,
              (blocksU.filter (· ∣ x + s)).card * b ^ (L - s))
          + ∑ s ∈ Finset.Icc (K+1) L,
              (SC.filter (· ∣ x + y * M + s)).card * b ^ (L - s) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    have hstray_fold : ∑ s ∈ Finset.Icc (K+1) L,
        (SC.filter (· ∣ x + y * M + s)).card * b ^ (L - s) = strayN y := rfl
    have h2 : ∑ s ∈ Finset.Icc (K+1) L, supportCoeff A (N + s) * b ^ (L - s)
        ≤ (K * b ^ (L - K) + b ^ (L - K + 1)) + b ^ (L - K) + b ^ (L - K) := by
      rw [hdist, hstray_fold] at h1
      omega
    have hCexp : (K + b + 2) * b ^ (L - K)
        = K * b ^ (L - K) + b * b ^ (L - K) + 2 * b ^ (L - K) := by ring
    have hpow : b ^ (L - K + 1) = b * b ^ (L - K) := by
      rw [pow_succ]
      ring
    rw [hCdef]
    omega
  -- the certificate
  refine ⟨N, K, L, C, hKL, hfirst, hmiddle, hfar, ?_⟩
  have hpart1 : 2 * (q * C) < b ^ L := by
    have h1 : 2 * q * (K + b + 2) < b ^ K := by
      have hexp : 2*q*(K+b+2) = 2*q*(b+2) + 2*q*K := by ring
      omega
    have h2 : 2 * (q * C) = (2*q*(K+b+2)) * b ^ (L-K) := by
      rw [hCdef]
      ring
    have h3 : (2*q*(K+b+2)) * b ^ (L-K) < b ^ K * b ^ (L-K) :=
      mul_lt_mul_of_pos_right h1 (pow_pos (by omega) _)
    have h4 : b ^ K * b ^ (L-K) = b ^ L := by
      rw [← pow_add]
      congr 1
      omega
    omega
  have hpart2 : 2 * (q * (N + L + 2)) < b ^ L := by
    have hNle : N ≤ x + Y * M := by
      have h0 : y * M ≤ Y * M := Nat.mul_le_mul_right M (by omega)
      omega
    have hYM : Y * M = Y₀ * M + L * M := by
      rw [hYdef]
      ring
    have h1' : N + L + 2 ≤ x + Y₀ * M + (L * M + L) + 2 := by omega
    have h2 : 2*q*(N+L+2) ≤ 2*q*(x + Y₀ * M + (L * M + L) + 2) :=
      Nat.mul_le_mul_left (2*q) h1'
    have h3 : 2*q*(x + Y₀ * M + (L * M + L) + 2)
        = 2*q*(x + Y₀ * M + 2) + 2*q*(M+1)*L := by ring
    have h4 : 2*(q*(N+L+2)) = 2*q*(N+L+2) := by ring
    omega
  have hexpand : q * (C + (N + L + 2)) = q * C + q * (N + L + 2) := by ring
  omega

/-- **Erdős's pairwise-coprime support theorem (1948), machine-checked.**
For every base `b ≥ 2` and every infinite pairwise-coprime support
`A ⊆ ℕ` with summable reciprocals, `∑_{a ∈ A} 1/(b^a - 1)` is
irrational.  The first non-dilation support class of Erdős #257 to
submit to the support-coefficient calculus: this is NOT valuation
forcing — small support elements join the CRT modulus at residue zero,
adaptive block sizes absorb their deterministic first-block hits, and
summable reciprocals control the strays. -/
theorem irrational_erdosSupportSeries_pairwise_coprime (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (hA : A.Infinite) (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a)) :
    Irrational (erdosSupportSeries b A) :=
  irrational_erdosSupportSeries_of_weighted_coeff_certificates b A hb
    (exists_weighted_coeff_certificates_supportCoeff_pairwise_coprime
      b A hb hA hpair hsum)

/-! ## Support-coefficient calculus: eventually-periodic supports (wave 10)

Erdős #257 for supports whose indicator is eventually periodic.  The engine
is a **periodic divisor-orbit sieve**: if membership in `A` depends only on
the residue mod `m`, and `p` is a prime not dividing `m`, then Euler's
theorem makes the divisor ray `d, pd, p²d, …` sweep residues mod `m` with
period dividing `φ(m)`.  A prime with exact valuation `b·φ(m) - 1` therefore
splits every divisor ray into complete residue cycles repeated a multiple of
`b` times, contributing a clean factor `b` to `supportCoeff A n` — no primes
in arithmetic progressions, no Lambert `q`-series criterion.  The bounded
Bertrand/CRT frame of the full-support lane supplies such primes wholesale:
only the exact-valuation exponent changes, from `b - 1` to `b·φ(m) - 1`. -/

/-- **Iterated periodicity of a predicate**: an `m`-periodic predicate is
invariant under adding any multiple of `m`. -/
theorem periodic_pred_add_mul (χ : ℕ → Prop) (m : ℕ)
    (hper : ∀ x : ℕ, χ (x + m) ↔ χ x) :
    ∀ (k x : ℕ), χ (x + k * m) ↔ χ x := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ihk =>
      intro x
      have h1 : x + (k + 1) * m = (x + k * m) + m := by ring
      rw [h1]
      exact (hper (x + k * m)).trans (ihk x)

/-- **Periodic predicates respect congruence**: an `m`-periodic predicate
takes equal values on numbers congruent mod `m`. -/
theorem periodic_pred_iff_of_modEq (χ : ℕ → Prop) (m : ℕ)
    (hper : ∀ x : ℕ, χ (x + m) ↔ χ x) {a b : ℕ} (hab : a ≡ b [MOD m]) :
    χ a ↔ χ b := by
  have hmod : ∀ x : ℕ, χ x ↔ χ (x % m) := by
    intro x
    conv_lhs => rw [← Nat.mod_add_div x m]
    rw [show x % m + m * (x / m) = x % m + (x / m) * m from by ring]
    exact periodic_pred_add_mul χ m hper (x / m) (x % m)
  have hab' : a % m = b % m := hab
  rw [hmod a, hmod b, hab']

/-- **Complete-cycle count for a periodic predicate**: over a range of `s`
complete periods, a `t`-periodic predicate holds exactly `s` times its count
over one period.  This is the divisibility engine of the periodic orbit
lemma. -/
theorem card_filter_range_mul_of_periodic (Q : ℕ → Prop) [inst : DecidablePred Q]
    (t : ℕ) (hQ : ∀ j : ℕ, Q (j + t) ↔ Q j) :
    ∀ s : ℕ, ((Finset.range (s * t)).filter fun j => Q j).card
      = s * ((Finset.range t).filter fun j => Q j).card := by
  have hiter : ∀ (k j : ℕ), Q (j + k * t) ↔ Q j := periodic_pred_add_mul Q t hQ
  intro s
  induction s with
  | zero => simp
  | succ s ihs =>
      have hle1 : s * t ≤ (s + 1) * t := Nat.mul_le_mul_right t (by omega)
      have hdiff : (s + 1) * t - s * t = t := by
        have h1 : (s + 1) * t = s * t + t := by ring
        omega
      have hsplit : ∑ j ∈ Finset.range ((s + 1) * t), (if Q j then 1 else 0)
          = (∑ j ∈ Finset.range (s * t), (if Q j then 1 else 0))
            + ∑ i ∈ Finset.range t, (if Q (s * t + i) then 1 else 0) := by
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive (fun j => if Q j then 1 else 0)
            (Nat.zero_le (s * t)) hle1,
          ← Finset.range_eq_Ico]
        congr 1
        rw [Finset.sum_Ico_eq_sum_range, hdiff]
      have hshiftterm : ∑ i ∈ Finset.range t, (if Q (s * t + i) then 1 else 0)
          = ∑ i ∈ Finset.range t, (if Q i then 1 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show s * t + i = i + s * t from by ring]
        exact if_congr (hiter s i) rfl rfl
      rw [Finset.card_filter, hsplit, hshiftterm, ← Finset.card_filter,
        ← Finset.card_filter, ihs]
      ring

/-- **Divisor fiber decomposition at an exact prime power.**  Divisors of
`p^E · R` with `p ∤ R` factor uniquely as `p^j · d` with `j ≤ E`, `d ∣ R`:
any filtered divisor count decomposes as a sum over `d ∣ R` of counts along
the `p`-power ray through `d`.  This replaces `τ`-multiplicativity for
support coefficients, where the filter destroys the product structure. -/
theorem card_filter_divisors_prime_pow_mul_eq_sum
    (χ : ℕ → Prop) [inst : DecidablePred χ] (p E R : ℕ) (hp : Nat.Prime p)
    (hR : R ≠ 0) (hpR : ¬ p ∣ R) :
    (((p ^ E * R).divisors.filter fun D => χ D).card)
      = ∑ d ∈ R.divisors,
          ((Finset.range (E + 1)).filter fun j => χ (p ^ j * d)).card := by
  classical
  have hpE0 : p ^ E ≠ 0 := pow_ne_zero E hp.pos.ne'
  have hn0 : p ^ E * R ≠ 0 := mul_ne_zero hpE0 hR
  have hnfp : (p ^ E * R).factorization p = E := by
    rw [Nat.factorization_mul hpE0 hR, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hpR]
    omega
  -- every filtered divisor has a well-defined cofactor in `R.divisors`
  have hcofactor : ∀ D : ℕ, D ∣ p ^ E * R → D ≠ 0 →
      p ^ (D.factorization p) ∣ D ∧ ¬ p ∣ D / p ^ (D.factorization p) ∧
        D / p ^ (D.factorization p) ∣ R := by
    intro D hDdvd hD0
    have hproj : p ^ (D.factorization p) ∣ D :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hD0).mpr le_rfl
    set d : ℕ := D / p ^ (D.factorization p) with hddef
    have hDeq : D = p ^ (D.factorization p) * d := (Nat.mul_div_cancel' hproj).symm
    have hpd : ¬ p ∣ d := by
      intro hdvd
      have h1 : p ^ (D.factorization p + 1) ∣ D := by
        have h1a : p ^ (D.factorization p + 1) ∣ p ^ (D.factorization p) * d := by
          rw [pow_succ]
          exact mul_dvd_mul_left _ hdvd
        rwa [← hDeq] at h1a
      have h2 : D.factorization p + 1 ≤ D.factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hD0).mp h1
      omega
    have hddvd : d ∣ R := by
      have hdD : d ∣ D := ⟨p ^ (D.factorization p), by rw [mul_comm]; exact hDeq⟩
      have h1 : d ∣ p ^ E * R := hdD.trans hDdvd
      have hcop : Nat.Coprime d (p ^ E) :=
        Nat.Coprime.pow_right E (((hp.coprime_iff_not_dvd).mpr hpd).symm)
      exact hcop.dvd_of_dvd_mul_left h1
    exact ⟨hproj, hpd, hddvd⟩
  have hmapsto : ∀ D ∈ (p ^ E * R).divisors.filter fun D => χ D,
      D / p ^ (D.factorization p) ∈ R.divisors := by
    intro D hD
    rcases Finset.mem_filter.mp hD with ⟨hDdiv, _⟩
    rcases Nat.mem_divisors.mp hDdiv with ⟨hDdvd, _⟩
    have hD0 : D ≠ 0 := (Nat.pos_of_mem_divisors hDdiv).ne'
    obtain ⟨-, -, hddvd⟩ := hcofactor D hDdvd hD0
    exact Nat.mem_divisors.mpr ⟨hddvd, hR⟩
  rw [Finset.card_eq_sum_card_fiberwise hmapsto]
  refine Finset.sum_congr rfl fun d hd => ?_
  rcases Nat.mem_divisors.mp hd with ⟨hdR, -⟩
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hpd : ¬ p ∣ d := fun h => hpR (h.trans hdR)
  -- the fiber over `d` bijects with the `p`-power ray indices
  refine Finset.card_bij' (fun D _ => D.factorization p) (fun j _ => p ^ j * d)
    ?_ ?_ ?_ ?_
  · -- forward maps into the range filter
    intro D hD
    show D.factorization p ∈ (Finset.range (E + 1)).filter fun j => χ (p ^ j * d)
    rcases Finset.mem_filter.mp hD with ⟨hDfil, hfib⟩
    rcases Finset.mem_filter.mp hDfil with ⟨hDdiv, hχD⟩
    rcases Nat.mem_divisors.mp hDdiv with ⟨hDdvd, -⟩
    have hD0 : D ≠ 0 := (Nat.pos_of_mem_divisors hDdiv).ne'
    obtain ⟨hproj, -, -⟩ := hcofactor D hDdvd hD0
    have hvle : D.factorization p ≤ E := by
      have h1 : p ^ (D.factorization p) ∣ p ^ E * R := hproj.trans hDdvd
      have h2 := (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).mp h1
      omega
    have hDeq : D = p ^ (D.factorization p) * d :=
      Nat.eq_mul_of_div_eq_right hproj hfib
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [← hDeq]
    exact hχD
  · -- backward maps into the fiber
    intro j hj
    show p ^ j * d ∈ ((p ^ E * R).divisors.filter fun D => χ D).filter
      fun D => D / p ^ (D.factorization p) = d
    rcases Finset.mem_filter.mp hj with ⟨hjrange, hχj⟩
    have hjE : j ≤ E := by
      have := Finset.mem_range.mp hjrange
      omega
    have hdvd : p ^ j * d ∣ p ^ E * R :=
      mul_dvd_mul (pow_dvd_pow p hjE) hdR
    have hfp : (p ^ j * d).factorization p = j := by
      rw [Nat.factorization_mul (pow_ne_zero j hp.pos.ne') hd0, Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hpd]
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdvd, hn0⟩, hχj⟩, ?_⟩
    rw [hfp]
    exact Nat.mul_div_cancel_left d (pow_pos hp.pos j)
  · -- left inverse
    intro D hD
    show p ^ (D.factorization p) * d = D
    rcases Finset.mem_filter.mp hD with ⟨hDfil, hfib⟩
    rcases Finset.mem_filter.mp hDfil with ⟨hDdiv, -⟩
    rcases Nat.mem_divisors.mp hDdiv with ⟨hDdvd, -⟩
    have hD0 : D ≠ 0 := (Nat.pos_of_mem_divisors hDdiv).ne'
    obtain ⟨hproj, -, -⟩ := hcofactor D hDdvd hD0
    exact (Nat.eq_mul_of_div_eq_right hproj hfib).symm
  · -- right inverse
    intro j hj
    show (p ^ j * d).factorization p = j
    rcases Finset.mem_filter.mp hj with ⟨hjrange, -⟩
    rw [Nat.factorization_mul (pow_ne_zero j hp.pos.ne') hd0, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hpd]
    omega

set_option linter.unusedVariables false in
/-- **Periodic divisor-orbit block divisibility.**  If `χ` is `m`-periodic
and `P` is a set of primes not dividing `m`, at each of which `n` has exact
valuation `w·φ(m) - 1`, then `w^|P|` divides the `χ`-filtered divisor count
of `n`.  Each prime's ray decomposes the count into complete `φ(m)`-cycles
repeated `w · (…)` times (Euler), and the cycle sums recurse through the
remaining primes with the twisted predicates `x ↦ χ(p^j·x)`, which are again
`m`-periodic. -/
theorem bpow_dvd_card_filter_divisors_of_periodic_block
    (m w : ℕ) (hm : 0 < m) (hw : 0 < w) (P : Finset ℕ) :
    ∀ (χ : ℕ → Prop) [inst : DecidablePred χ] (n : ℕ),
      n ≠ 0 →
      (∀ x : ℕ, χ (x + m) ↔ χ x) →
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, ¬ p ∣ m) →
      (∀ p ∈ P, n.factorization p = w * m.totient - 1) →
      w ^ P.card ∣ (n.divisors.filter fun D => χ D).card := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      intro χ _ n _ _ _ _ _
      simp
  | insert p P' hpP' ih =>
      intro χ instχ n hn hχper hprime hndvd hval
      have hpprime : Nat.Prime p := hprime p (Finset.mem_insert_self p P')
      have hpm : ¬ p ∣ m := hndvd p (Finset.mem_insert_self p P')
      have htpos : 0 < m.totient := Nat.totient_pos.mpr hm
      have hwt1 : 1 ≤ w * m.totient := Nat.mul_pos hw htpos
      set E : ℕ := w * m.totient - 1 with hEdef
      have hE1 : E + 1 = w * m.totient := by omega
      have hvp : n.factorization p = E := by
        rw [hEdef]
        exact hval p (Finset.mem_insert_self p P')
      have hpEdvd : p ^ E ∣ n :=
        (Nat.Prime.pow_dvd_iff_le_factorization hpprime hn).mpr hvp.ge
      set R : ℕ := n / p ^ E with hRdef
      have hnR : n = p ^ E * R := (Nat.mul_div_cancel' hpEdvd).symm
      have hR0 : R ≠ 0 := by
        intro h
        rw [h, mul_zero] at hnR
        exact hn hnR
      have hpE0 : p ^ E ≠ 0 := pow_ne_zero E hpprime.pos.ne'
      have hpR : ¬ p ∣ R := by
        intro hdvd
        have h1 : p ^ (E + 1) ∣ n := by
          rw [hnR, pow_succ]
          exact mul_dvd_mul_left _ hdvd
        have h2 : E + 1 ≤ n.factorization p :=
          (Nat.Prime.pow_dvd_iff_le_factorization hpprime hn).mp h1
        omega
      -- valuations of the remaining primes carry over to `R`
      have hfacR : ∀ q ∈ P', R.factorization q = w * m.totient - 1 := by
        intro q hq
        have hqp : q ≠ p := by
          rintro rfl
          exact hpP' hq
        have h1 : n.factorization q = (p ^ E).factorization q + R.factorization q := by
          conv_lhs => rw [hnR]
          rw [Nat.factorization_mul hpE0 hR0, Finsupp.add_apply]
        have h2 : (p ^ E).factorization q = 0 := by
          rw [hpprime.factorization_pow, Finsupp.single_eq_of_ne hqp]
        have h3 := hval q (Finset.mem_insert_of_mem hq)
        omega
      -- fiber decomposition at `p`
      have hdecomp : ((n.divisors.filter fun D => χ D).card)
          = ∑ d ∈ R.divisors,
              ((Finset.range (E + 1)).filter fun j => χ (p ^ j * d)).card := by
        conv_lhs => rw [hnR]
        exact card_filter_divisors_prime_pow_mul_eq_sum χ p E R hpprime hR0 hpR
      -- each ray count is `w` complete `φ(m)`-cycles
      have hcount : ∀ d ∈ R.divisors,
          ((Finset.range (E + 1)).filter fun j => χ (p ^ j * d)).card
            = w * ((Finset.range m.totient).filter fun j => χ (p ^ j * d)).card := by
        intro d _
        have heuler : p ^ m.totient ≡ 1 [MOD m] :=
          Nat.ModEq.pow_totient ((hpprime.coprime_iff_not_dvd).mpr hpm)
        have hQper : ∀ j : ℕ, χ (p ^ (j + m.totient) * d) ↔ χ (p ^ j * d) := by
          intro j
          have h1 : p ^ (j + m.totient) * d = (p ^ j * d) * p ^ m.totient := by
            rw [pow_add]
            ring
          have h2 : (p ^ j * d) * p ^ m.totient ≡ (p ^ j * d) * 1 [MOD m] :=
            Nat.ModEq.mul_left _ heuler
          rw [h1]
          refine periodic_pred_iff_of_modEq χ m hχper ?_
          rw [mul_one] at h2
          exact h2
        rw [hE1]
        exact card_filter_range_mul_of_periodic (fun j => χ (p ^ j * d))
          m.totient hQper w
      -- swap the double count and recurse through the remaining primes
      have hswap : ∑ d ∈ R.divisors,
            ((Finset.range m.totient).filter fun j => χ (p ^ j * d)).card
          = ∑ j ∈ Finset.range m.totient,
              ((R.divisors.filter fun d => χ (p ^ j * d)).card) := by
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm
      have hinner : ∀ j ∈ Finset.range m.totient,
          w ^ P'.card ∣ ((R.divisors.filter fun d => χ (p ^ j * d)).card) := by
        intro j _
        have hχ' : ∀ x : ℕ, χ (p ^ j * (x + m)) ↔ χ (p ^ j * x) := by
          intro x
          rw [show p ^ j * (x + m) = p ^ j * x + p ^ j * m from by ring]
          exact periodic_pred_add_mul χ m hχper (p ^ j) (p ^ j * x)
        exact ih (fun x => χ (p ^ j * x)) (inst := fun x => instχ (p ^ j * x)) R hR0
          hχ' (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
          (fun q hq => hndvd q (Finset.mem_insert_of_mem hq)) hfacR
      have hdvd_inner : w ^ P'.card ∣ ∑ j ∈ Finset.range m.totient,
          ((R.divisors.filter fun d => χ (p ^ j * d)).card) :=
        Finset.dvd_sum hinner
      have htotal : ((n.divisors.filter fun D => χ D).card)
          = w * ∑ j ∈ Finset.range m.totient,
              ((R.divisors.filter fun d => χ (p ^ j * d)).card) := by
        rw [hdecomp, Finset.sum_congr rfl hcount, ← hswap, Finset.mul_sum]
      rw [htotal, Finset.card_insert_of_notMem hpP', pow_succ']
      exact mul_dvd_mul_left w hdvd_inner

/-- **Periodic orbit divisibility for the support coefficient.**  The
`Set`-level form the certificate assembly consumes: an `m`-periodic support
`A`, together with `|P|` primes above `m` at exact valuation `b·φ(m) - 1`,
forces `b^|P|` to divide `supportCoeff A n`. -/
theorem bpow_dvd_supportCoeff_of_periodic_exact_block
    (b m n : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m) (hn : n ≠ 0)
    (hper : ∀ x : ℕ, x + m ∈ A ↔ x ∈ A)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hgt : ∀ p ∈ P, m < p)
    (hexact : ∀ p ∈ P, n.factorization p = b * m.totient - 1) :
    b ^ P.card ∣ supportCoeff A n := by
  classical
  have hndvd : ∀ p ∈ P, ¬ p ∣ m := by
    intro p hp hdvd
    have h1 : p ≤ m := Nat.le_of_dvd hm hdvd
    have h2 := hgt p hp
    omega
  rw [supportCoeff_eq_card_filter]
  exact bpow_dvd_card_filter_divisors_of_periodic_block m b hm (by omega) P
    (fun d => d ∈ A) n hn hper hprime hndvd hexact

/-- **Bounded exact-valuation frame.**  The bounded Bertrand/CRT frame of
the full-support lane with its prime blocks exposed instead of consumed:
`x < A`, explicit modulus ceiling, exposed modulus support, and for every
slot `r ∈ [1, K]` a block of `r` primes above `L` at which the whole
progression has exact valuation `B - 1`.  Both the `τ` first-block
divisibility and the periodic-orbit first-block divisibility are corollaries
— they differ only in the multiplicity engine applied to the blocks. -/
theorem exists_bounded_exact_valuation_frame
    (B L K : ℕ) (hB : 2 ≤ B) (hK : 1 ≤ K) (hKL : K ≤ L) :
    ∃ x A : ℕ, ∃ P : ℕ → Finset ℕ, 0 < A ∧ x < A ∧ L + 1 ≤ A ∧
      A ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (B * K ^ 2) ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ A → L < p ∧ ∃ r ∈ Finset.Icc 1 K, p ∣ x + r) ∧
      (∀ r ∈ Finset.Icc 1 K, (P r).card = r) ∧
      (∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r, Nat.Prime p) ∧
      (∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r, L < p) ∧
      (∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r,
        (x + y * A + r).factorization p = B - 1) := by
  classical
  obtain ⟨P, M, hLM, hMB, hcards, hprimes, hgtL, hleM, hdisj⟩ :=
    exists_bounded_disjoint_prime_blocks L K
  set π : ℕ → ℕ := fun r => ∏ p ∈ P r, p with hπdef
  set mm : ℕ → ℕ := fun r => (π r) ^ B with hmmdef
  have hπpos : ∀ r ∈ Finset.Icc 1 K, 0 < π r := fun r hr =>
    Finset.prod_pos fun p hp => (hprimes r hr p hp).pos
  have hπ2 : ∀ r ∈ Finset.Icc 1 K, 2 ≤ π r := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
    have hne : (P r).Nonempty := by
      rw [← Finset.card_pos, hcards r hr]
      omega
    obtain ⟨p₀, hp₀⟩ := hne
    have h1 : p₀ ≤ π r := Nat.le_of_dvd (hπpos r hr) (Finset.dvd_prod_of_mem _ hp₀)
    have h2 := (hprimes r hr p₀ hp₀).two_le
    omega
  have hπgtL : ∀ r ∈ Finset.Icc 1 K, L < π r := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
    have hne : (P r).Nonempty := by
      rw [← Finset.card_pos, hcards r hr]
      omega
    obtain ⟨p₀, hp₀⟩ := hne
    have h1 : p₀ ≤ π r := Nat.le_of_dvd (hπpos r hr) (Finset.dvd_prod_of_mem _ hp₀)
    have h2 := hgtL r hr p₀ hp₀
    omega
  have hmmpos : ∀ r ∈ Finset.Icc 1 K, 0 < mm r := fun r hr => pow_pos (hπpos r hr) B
  have hmmcop : ∀ r s, r ∈ Finset.Icc 1 K → s ∈ Finset.Icc 1 K → r ≠ s →
      Nat.Coprime (mm r) (mm s) := by
    intro r s hr hs hrs
    have hππ : Nat.Coprime (π r) (π s) := by
      apply Nat.Coprime.prod_left
      intro p hp
      have h1 : Nat.Coprime (π s) p := by
        apply Nat.Coprime.prod_left
        intro p' hp'
        have hne' : p' ≠ p := by
          intro heq
          have hp'' : p ∈ P s := heq ▸ hp'
          exact (Finset.disjoint_left.mp (hdisj r s hr hs hrs) hp) hp''
        exact (Nat.coprime_primes (hprimes s hs p' hp') (hprimes r hr p hp)).mpr hne'
      exact h1.symm
    exact Nat.Coprime.pow B B hππ
  have hrle : ∀ r ∈ Finset.Icc 1 K, r ≤ (π r) ^ (B - 1) := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr2⟩
    have h1 : π r ≤ (π r) ^ (B - 1) := Nat.le_self_pow (by omega) _
    have h2 := hπgtL r hr
    omega
  obtain ⟨x, hxlt, hxcong⟩ := exists_bounded_crt_residue K mm
    (fun r => (π r) ^ (B - 1) - r) hmmpos hmmcop
  set A : ℕ := ∏ r ∈ Finset.Icc 1 K, mm r with hAdef
  have hApos : 0 < A := Finset.prod_pos hmmpos
  have hmmdvdA : ∀ r ∈ Finset.Icc 1 K, mm r ∣ A := fun r hr =>
    Finset.dvd_prod_of_mem mm hr
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_refl _, hK⟩
  have hLA : L + 1 ≤ A := by
    have h1 : mm 1 ≤ A := Nat.le_of_dvd hApos (hmmdvdA 1 h1mem)
    have h2 : π 1 ≤ mm 1 := Nat.le_self_pow (by omega) _
    have h3 := hπgtL 1 h1mem
    omega
  have hshift : ∀ r ∈ Finset.Icc 1 K, x + r ≡ (π r) ^ (B - 1) [MOD mm r] := by
    intro r hr
    have h1 := (hxcong r hr).add_right r
    have h2 : (π r) ^ (B - 1) - r + r = (π r) ^ (B - 1) :=
      Nat.sub_add_cancel (hrle r hr)
    rwa [h2] at h1
  have hprogcong : ∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K,
      x + y * A + r ≡ (π r) ^ (B - 1) [MOD mm r] := by
    intro y r hr
    have h1 : mm r ∣ y * A := Dvd.dvd.mul_left (hmmdvdA r hr) y
    have h2 : x + y * A + r ≡ x + 0 + r [MOD mm r] :=
      ((Nat.ModEq.refl x).add ((Nat.modEq_zero_iff_dvd).mpr h1)).add_right r
    have h3 : x + 0 + r = x + r := by ring
    rw [h3] at h2
    exact h2.trans (hshift r hr)
  have hval : ∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K, ∀ p ∈ P r,
      (x + y * A + r).factorization p = B - 1 := by
    intro y r hr p hp
    exact factorization_eq_of_modEq_prod_pow B hB (P r)
      (fun p' hp' => hprimes r hr p' hp') (hπ2 r hr) _ (hprogcong y r hr) p hp
  refine ⟨x, A, P, hApos, hxlt, hLA, ?_, ?_, hcards, hprimes, hgtL, hval⟩
  · -- modulus bound
    have hMpos : 0 < M := by omega
    have hπleMK : ∀ r ∈ Finset.Icc 1 K, π r ≤ M ^ K := by
      intro r hr
      have h1 : π r ≤ M ^ (P r).card :=
        Finset.prod_le_pow_card (P r) _ M (fun p hp => hleM r hr p hp)
      have h2 : M ^ (P r).card = M ^ r := by rw [hcards r hr]
      have h3 : M ^ r ≤ M ^ K :=
        Nat.pow_le_pow_right hMpos (Finset.mem_Icc.mp hr).2
      omega
    have hmmle : ∀ r ∈ Finset.Icc 1 K, mm r ≤ (M ^ K) ^ B := fun r hr =>
      Nat.pow_le_pow_left (hπleMK r hr) B
    have hAle1 : A ≤ ((M ^ K) ^ B) ^ K := by
      have h1 : A ≤ ((M ^ K) ^ B) ^ (Finset.Icc 1 K).card :=
        Finset.prod_le_pow_card _ _ _ hmmle
      have h2 : (Finset.Icc 1 K).card = K := by rw [Nat.card_Icc]; omega
      rwa [h2] at h1
    have hAle2 : ((M ^ K) ^ B) ^ K = M ^ (B * K ^ 2) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    have hMle : M ^ (B * K ^ 2) ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (B * K ^ 2) :=
      Nat.pow_le_pow_left hMB _
    omega
  · -- modulus support
    intro p hp hpA
    rw [hAdef] at hpA
    obtain ⟨r, hrmem, hpmm⟩ := Prime.exists_mem_finset_dvd hp.prime hpA
    have hpπ : p ∣ π r := hp.dvd_of_dvd_pow hpmm
    obtain ⟨p', hp'mem, hpp'⟩ := Prime.exists_mem_finset_dvd hp.prime hpπ
    have heq : p = p' :=
      (Nat.prime_dvd_prime_iff_eq hp (hprimes r hrmem p' hp'mem)).mp hpp'
    have hpP : p ∈ P r := heq ▸ hp'mem
    refine ⟨hgtL r hrmem p hpP, r, hrmem, ?_⟩
    have h1 : p ∣ mm r := hpπ.trans (dvd_pow_self (π r) (by omega : B ≠ 0))
    have h2 : x + r ≡ (π r) ^ (B - 1) [MOD p] :=
      Nat.ModEq.of_dvd h1 (hshift r hrmem)
    have h3 : p ∣ (π r) ^ (B - 1) :=
      hpπ.trans (dvd_pow_self (π r) (by omega : B - 1 ≠ 0))
    have h4 : (π r) ^ (B - 1) ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr h3
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans h4)

/-- **Mixed-base certificate parameter arithmetic.**  The scaled parameter
schedule for supports of period `m`: the frame runs at valuation base
`B = b·φ(m)` and the period joins the window schedule
`K = 9(q + B + m + 100)`, while the certificate budget stays at the series
base `b`.  All four closure facts survive, plus `m ≤ K`, which puts the
frame primes above the period. -/
theorem certificate_param_arithmetic_periodic
    (b B m q K κ E : ℕ) (hb : 2 ≤ b) (hB : 2 ≤ B) (hq : 0 < q)
    (hK : K = 9 * (q + B + m + 100))
    (hκ : κ = 3 * (2 * B * K ^ 2 + 1) + (2 * B * K ^ 2 * (K * (K + 1) + 1) + q + 4))
    (hE : E = B * K ^ 2 * (K * (K + 1) + κ + 1)) :
    4 * q * (E + κ + 5) ≤ b ^ K ∧ 2 * E + κ + q + 4 ≤ 2 ^ κ ∧ 1 ≤ K ∧
      K ≤ 2 ^ κ ∧ m ≤ K := by
  have hK1 : 1 ≤ K := by omega
  have hmK : m ≤ K := by omega
  have hKκ : K ≤ κ := by
    have h1 : K ≤ K * K := Nat.le_mul_of_pos_left K (by omega)
    have h2 : K * K ≤ B * (K * K) := Nat.le_mul_of_pos_left (K * K) (by omega)
    have h3 : B * (K * K) = B * K ^ 2 := by ring
    have h4 : 2 * (B * K ^ 2) = 2 * B * K ^ 2 := by ring
    omega
  have hκpow : κ < 2 ^ κ := Nat.lt_two_pow_self
  have hKκpow : K ≤ 2 ^ κ := by omega
  have hclosure : 2 * E + κ + q + 4 ≤ 2 ^ κ := by
    have hkey := param_linear_le_two_pow (2 * B * K ^ 2 + 1)
      (2 * B * K ^ 2 * (K * (K + 1) + 1) + q + 4)
    rw [← hκ] at hkey
    have hle : 2 * E + κ + q + 4
        = (2 * B * K ^ 2 + 1) * κ + (2 * B * K ^ 2 * (K * (K + 1) + 1) + q + 4) := by
      rw [hE]; ring
    omega
  have hgrind : 4 * q * (E + κ + 5) ≤ b ^ K := by
    set β : ℕ := B + m with hβdef
    have hKval : K = 9 * (q + β + 100) := by rw [hK, hβdef]; ring
    have hq2 : q < 2 ^ q := Nat.lt_two_pow_self
    have hβ2 : β < 2 ^ β := Nat.lt_two_pow_self
    have hBβ : B ≤ β := by omega
    have hKle : K ≤ 2 ^ (q + β + 10) := by
      have h1 : q + β < 2 ^ (q + β) := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (q + β + 10) = 2 ^ (q + β) * 1024 := by
        rw [pow_add]; norm_num
      omega
    have hK1le : K + 1 ≤ 2 ^ (q + β + 11) := by
      have h2 : (2 : ℕ) ^ (q + β + 11) = 2 ^ (q + β + 10) * 2 := pow_succ 2 (q + β + 10)
      omega
    have hKsq : K ^ 2 ≤ 2 ^ (2 * q + 2 * β + 20) := by
      have h1 : K ^ 2 = K * K := by ring
      have h2 : K * K ≤ 2 ^ (q + β + 10) * 2 ^ (q + β + 10) := Nat.mul_le_mul hKle hKle
      have h3 : (2 : ℕ) ^ (q + β + 10) * 2 ^ (q + β + 10) = 2 ^ (2 * q + 2 * β + 20) := by
        rw [← pow_add]; congr 1; ring
      omega
    have hKK1 : K * (K + 1) ≤ 2 ^ (2 * q + 2 * β + 21) := by
      have h2 : K * (K + 1) ≤ 2 ^ (q + β + 10) * 2 ^ (q + β + 11) :=
        Nat.mul_le_mul hKle hK1le
      have h3 : (2 : ℕ) ^ (q + β + 10) * 2 ^ (q + β + 11) = 2 ^ (2 * q + 2 * β + 21) := by
        rw [← pow_add]; congr 1; ring
      omega
    have hBK2 : B * K ^ 2 ≤ 2 ^ (3 * q + 3 * β + 20) := by
      have h0 : B < 2 ^ β := lt_of_le_of_lt hBβ hβ2
      have h1 : B * K ^ 2 ≤ 2 ^ β * 2 ^ (2 * q + 2 * β + 20) :=
        Nat.mul_le_mul (Nat.le_of_lt h0) hKsq
      have h2 : (2 : ℕ) ^ β * 2 ^ (2 * q + 2 * β + 20) = 2 ^ (2 * q + 3 * β + 20) := by
        rw [← pow_add]; congr 1; ring
      have h3 : (2 : ℕ) ^ (2 * q + 3 * β + 20) ≤ 2 ^ (3 * q + 3 * β + 20) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hKK1' : K * (K + 1) + 1 ≤ 2 ^ (2 * q + 2 * β + 22) := by
      have h1 : (1 : ℕ) ≤ 2 ^ (2 * q + 2 * β + 21) := Nat.one_le_two_pow
      have h2 : (2 : ℕ) ^ (2 * q + 2 * β + 22) = 2 ^ (2 * q + 2 * β + 21) * 2 :=
        pow_succ 2 _
      omega
    have hκle : κ ≤ 2 ^ (5 * q + 5 * β + 46) := by
      have hprod : B * K ^ 2 * (K * (K + 1) + 1) ≤ 2 ^ (5 * q + 5 * β + 42) := by
        have h1 : B * K ^ 2 * (K * (K + 1) + 1)
            ≤ 2 ^ (3 * q + 3 * β + 20) * 2 ^ (2 * q + 2 * β + 22) :=
          Nat.mul_le_mul hBK2 hKK1'
        have h2 : (2 : ℕ) ^ (3 * q + 3 * β + 20) * 2 ^ (2 * q + 2 * β + 22)
            = 2 ^ (5 * q + 5 * β + 42) := by
          rw [← pow_add]; congr 1; ring
        omega
      have hκ' : κ = 6 * (B * K ^ 2) + 2 * (B * K ^ 2 * (K * (K + 1) + 1)) + (q + 7) := by
        rw [hκ]; ring
      have hq7 : q + 7 ≤ 2 ^ (q + 3) := by
        have h1 : (2 : ℕ) ^ (q + 3) = 2 ^ q * 8 := by rw [pow_add]; norm_num
        omega
      have hup1 : (2 : ℕ) ^ (3 * q + 3 * β + 20) ≤ 2 ^ (5 * q + 5 * β + 42) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hup2 : (2 : ℕ) ^ (q + 3) ≤ 2 ^ (5 * q + 5 * β + 42) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hfin : (2 : ℕ) ^ (5 * q + 5 * β + 46) = 2 ^ (5 * q + 5 * β + 42) * 16 := by
        rw [show 5 * q + 5 * β + 46 = 5 * q + 5 * β + 42 + 4 by omega, pow_add]
        norm_num
      omega
    have hEle : E ≤ 2 ^ (8 * q + 8 * β + 70) := by
      have hin : K * (K + 1) + κ + 1 ≤ 2 ^ (5 * q + 5 * β + 48) := by
        have h1 : (2 : ℕ) ^ (2 * q + 2 * β + 21) ≤ 2 ^ (5 * q + 5 * β + 46) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : (1 : ℕ) ≤ 2 ^ (5 * q + 5 * β + 46) := Nat.one_le_two_pow
        have h3 : (2 : ℕ) ^ (5 * q + 5 * β + 48) = 2 ^ (5 * q + 5 * β + 46) * 4 := by
          rw [show 5 * q + 5 * β + 48 = 5 * q + 5 * β + 46 + 2 by omega, pow_add]
          norm_num
        omega
      have h4 : E ≤ 2 ^ (3 * q + 3 * β + 20) * 2 ^ (5 * q + 5 * β + 48) := by
        rw [hE]
        exact Nat.mul_le_mul hBK2 hin
      have h5 : (2 : ℕ) ^ (3 * q + 3 * β + 20) * 2 ^ (5 * q + 5 * β + 48)
          = 2 ^ (8 * q + 8 * β + 68) := by
        rw [← pow_add]; congr 1; ring
      have h6 : (2 : ℕ) ^ (8 * q + 8 * β + 68) ≤ 2 ^ (8 * q + 8 * β + 70) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hEκ5 : E + κ + 5 ≤ 2 ^ (8 * q + 8 * β + 72) := by
      have h1 : (2 : ℕ) ^ (5 * q + 5 * β + 46) ≤ 2 ^ (8 * q + 8 * β + 70) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2a : (2 : ℕ) ^ 3 ≤ 2 ^ (8 * q + 8 * β + 70) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (5 : ℕ) ≤ 2 ^ (8 * q + 8 * β + 70) := by
        norm_num at h2a
        omega
      have h3 : (2 : ℕ) ^ (8 * q + 8 * β + 72) = 2 ^ (8 * q + 8 * β + 70) * 4 := by
        rw [show 8 * q + 8 * β + 72 = 8 * q + 8 * β + 70 + 2 by omega, pow_add]
        norm_num
      omega
    have h4q : 4 * q ≤ 2 ^ (q + 2) := by
      have h1 : (2 : ℕ) ^ (q + 2) = 2 ^ q * 4 := by rw [pow_add]; norm_num
      omega
    have hprodf : 4 * q * (E + κ + 5) ≤ 2 ^ (q + 2) * 2 ^ (8 * q + 8 * β + 72) :=
      Nat.mul_le_mul h4q hEκ5
    have hexpf : (2 : ℕ) ^ (q + 2) * 2 ^ (8 * q + 8 * β + 72)
        = 2 ^ (9 * q + 8 * β + 74) := by
      rw [← pow_add]; congr 1; ring
    have hKexp : (2 : ℕ) ^ (9 * q + 8 * β + 74) ≤ 2 ^ K := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    have hbK : (2 : ℕ) ^ K ≤ b ^ K := Nat.pow_le_pow_left hb K
    omega
  exact ⟨hgrind, hclosure, hK1, hKκpow, hmK⟩

/-- **Weighted coefficient certificates for purely periodic supports.**
For every base `b ≥ 2` and every `m`-periodic support `A` with a positive
element, the periodic orbit sieve manufactures a weighted certificate at
every precision: the exact-valuation frame at base `B = b·φ(m)` feeds the
divisor-orbit divisibility for the first block, the full-support
divisor-pair average dominates the middle window through
`supportCoeff ≤ τ`, and the forward orbit of any positive support element
keeps the far tail alive. -/
theorem exists_weighted_coeff_certificates_supportCoeff_periodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, n + m ∈ A ↔ n ∈ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
      (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ supportCoeff A (N + r)) ∧
      (∑ r ∈ Finset.Icc (K + 1) L, supportCoeff A (N + r) * b ^ (L - r) ≤ C) ∧
      (∃ t : ℕ, 0 < supportCoeff A (N + L + 1 + t)) ∧
      q * (C + (N + L + 2)) < b ^ L := by
  intro q hq
  have htpos : 0 < m.totient := Nat.totient_pos.mpr hm
  set B : ℕ := b * m.totient with hBdef
  have hB : 2 ≤ B := by
    have h1 : b ≤ b * m.totient := Nat.le_mul_of_pos_right b htpos
    omega
  set K : ℕ := 9 * (q + B + m + 100) with hKdef
  set κ : ℕ := 3 * (2 * B * K ^ 2 + 1) + (2 * B * K ^ 2 * (K * (K + 1) + 1) + q + 4)
    with hκdef
  set E : ℕ := B * K ^ 2 * (K * (K + 1) + κ + 1) with hEdef
  obtain ⟨hparamA, hparamB, hK1, hKκpow, hmK⟩ :=
    certificate_param_arithmetic_periodic b B m q K κ E hb hB hq hKdef hκdef hEdef
  set L : ℕ := 2 ^ κ with hLdef
  clear_value K κ E L
  have hKL : K ≤ L := hKκpow
  have hmL : m ≤ L := le_trans hmK hKL
  obtain ⟨x, A', P, hApos, hxA, hLA, hAle, hsupp, hcards, hprimes, hgtL, hval⟩ :=
    exists_bounded_exact_valuation_frame B L K hB hK1 hKL
  have hA2E : A' ≤ 2 ^ E := by
    have h1 : L + 1 ≤ 2 ^ (κ + 1) := by
      have h1a : (2 : ℕ) ^ (κ + 1) = 2 ^ κ * 2 := pow_succ 2 κ
      omega
    have h4 : A' ≤ (2 ^ (K * (K + 1) + (κ + 1))) ^ (B * K ^ 2) := by
      calc A' ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (B * K ^ 2) := hAle
        _ ≤ (2 ^ (K * (K + 1)) * 2 ^ (κ + 1)) ^ (B * K ^ 2) := by
            apply Nat.pow_le_pow_left
            exact Nat.mul_le_mul_left _ h1
        _ = (2 ^ (K * (K + 1) + (κ + 1))) ^ (B * K ^ 2) := by rw [← pow_add]
    have h5 : ((2 : ℕ) ^ (K * (K + 1) + (κ + 1))) ^ (B * K ^ 2)
        = 2 ^ ((K * (K + 1) + (κ + 1)) * (B * K ^ 2)) := (pow_mul 2 _ _).symm
    have h6 : (2 : ℕ) ^ ((K * (K + 1) + (κ + 1)) * (B * K ^ 2)) ≤ 2 ^ E := by
      apply Nat.pow_le_pow_right (by norm_num)
      have h7 : E = (K * (K + 1) + (κ + 1)) * (B * K ^ 2) := by rw [hEdef]; ring
      omega
    omega
  obtain ⟨y, hyA, hWy⟩ :=
    selected_weighted_middle_of_supported_frame b x A' K L A' hb hApos hsupp
  -- first-block divisibility from the periodic orbit sieve
  have hfirst : ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ supportCoeff A (x + y * A' + r) := by
    intro r hr
    have hr1 := (Finset.mem_Icc.mp hr).1
    have hne : x + y * A' + r ≠ 0 := by omega
    have hgtm : ∀ p ∈ P r, m < p := by
      intro p hp
      have h1 := hgtL r hr p hp
      omega
    have hexact : ∀ p ∈ P r, (x + y * A' + r).factorization p = b * m.totient - 1 := by
      intro p hp
      have h1 := hval y r hr p hp
      rwa [hBdef] at h1
    have hdvd := bpow_dvd_supportCoeff_of_periodic_exact_block b m (x + y * A' + r) A
      hb hm hne hper (P r) (fun p hp => hprimes r hr p hp) hgtm hexact
    rwa [hcards r hr] at hdvd
  -- middle window: dominate the support coefficient by τ and reuse the
  -- selected divisor-pair average
  have hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, supportCoeff A (x + y * A' + r) * b ^ (L - r)
      ≤ (b ^ (L - K)
          * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + A' * A' + L)), (A' / d + 1))) / A' := by
    refine le_trans (Finset.sum_le_sum fun r _ => ?_) hWy
    exact Nat.mul_le_mul_right _ (supportCoeff_le_card_divisors A _)
  -- far-tail positivity from the forward orbit of a positive support element
  have htail : ∃ t : ℕ, 0 < supportCoeff A (x + y * A' + L + 1 + t) := by
    obtain ⟨a₀, ha₀pos, ha₀A⟩ := hpos
    set a : ℕ := a₀ + (x + y * A' + L + 2) * m with hadef
    have haA : a ∈ A := by
      rw [hadef]
      exact (periodic_pred_add_mul (fun x => x ∈ A) m hper (x + y * A' + L + 2) a₀).mpr ha₀A
    have hagt : x + y * A' + L + 1 < a := by
      have h1 : m ≥ 1 := hm
      have h2 : (x + y * A' + L + 2) * m ≥ (x + y * A' + L + 2) * 1 :=
        Nat.mul_le_mul_left _ h1
      omega
    refine ⟨a - (x + y * A' + L + 1), ?_⟩
    have heq : x + y * A' + L + 1 + (a - (x + y * A' + L + 1)) = a := by omega
    rw [heq]
    exact supportCoeff_pos_of_mem_dvd A haA (dvd_refl a) (by omega)
  refine ⟨x + y * A', K, L,
    (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + A' * A' + L)), (A' / d + 1))) / A',
    hKL, hfirst, hmiddle, htail, ?_⟩
  set S : ℕ := Nat.sqrt (x + A' * A' + L) with hSdef
  have hSle : S ≤ A' + L + 1 := by
    have h1 : x + A' * A' + L ≤ (A' + L + 1) * (A' + L + 1) := by
      have hexp : (A' + L + 1) * (A' + L + 1)
          = A' * A' + (2 * (A' * (L + 1)) + (L + 1) * (L + 1)) := by ring
      have h2 : A' ≤ A' * (L + 1) := Nat.le_mul_of_pos_right A' (by omega)
      have h3 : L + 1 ≤ (L + 1) * (L + 1) :=
        Nat.le_mul_of_pos_right (L + 1) (by omega)
      omega
    have h4 : Nat.sqrt (x + A' * A' + L) ≤ Nat.sqrt ((A' + L + 1) * (A' + L + 1)) :=
      Nat.sqrt_le_sqrt h1
    rw [Nat.sqrt_eq] at h4
    rw [hSdef]
    exact h4
  have hS2A : S ≤ 2 * A' := by omega
  have hSpow : S ≤ 2 ^ (E + κ + 2) := by
    have h1 : (2 : ℕ) ^ (E + κ + 2) = 2 ^ E * 2 ^ (κ + 2) := pow_add 2 E (κ + 2)
    have h2 : (4 : ℕ) ≤ 2 ^ (κ + 2) := by
      have h2a : (2 : ℕ) ^ (κ + 2) = 2 ^ κ * 4 := by rw [pow_add]; norm_num
      have h2b : (1 : ℕ) ≤ 2 ^ κ := Nat.one_le_two_pow
      omega
    have h5 : 2 ^ E * 4 ≤ 2 ^ E * 2 ^ (κ + 2) := Nat.mul_le_mul_left _ h2
    omega
  have hHle : (∑ d ∈ Finset.Icc 1 S, (A' / d + 1)) ≤ A' * (E + κ + 5) := by
    have h1 := harmonic_div_sum_le S A' (E + κ + 2) hSpow
    have h2 : A' * (E + κ + 2 + 1) + 2 * A' = A' * (E + κ + 5) := by ring
    omega
  have hCle : (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A'
      ≤ 2 * b ^ (L - K) * (E + κ + 5) := by
    have h1 : b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))
        ≤ b ^ (L - K) * (2 * (A' * (E + κ + 5))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hHle)
    have h2 : b ^ (L - K) * (2 * (A' * (E + κ + 5)))
        = A' * (2 * b ^ (L - K) * (E + κ + 5)) := by ring
    calc (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A'
        ≤ (A' * (2 * b ^ (L - K) * (E + κ + 5))) / A' := by
          apply Nat.div_le_div_right
          omega
      _ = 2 * b ^ (L - K) * (E + κ + 5) := Nat.mul_div_cancel_left _ hApos
  have hNle : x + y * A' + L + 2 ≤ A' * A' + L + 2 := by
    have h1 : y * A' ≤ (A' - 1) * A' := Nat.mul_le_mul_right A' (by omega)
    have h3 : (A' - 1) * A' = A' * A' - A' := Nat.sub_one_mul A' A'
    have h4 : A' ≤ A' * A' := Nat.le_mul_of_pos_left A' hApos
    omega
  have hhalf1 : 2 * (q * (2 * b ^ (L - K) * (E + κ + 5))) ≤ b ^ L := by
    have h1 : 2 * (q * (2 * b ^ (L - K) * (E + κ + 5)))
        = (4 * q * (E + κ + 5)) * b ^ (L - K) := by ring
    have h2 : (4 * q * (E + κ + 5)) * b ^ (L - K) ≤ b ^ K * b ^ (L - K) :=
      Nat.mul_le_mul_right _ hparamA
    have h3 : b ^ K * b ^ (L - K) = b ^ (K + (L - K)) := (pow_add b K (L - K)).symm
    have h4 : K + (L - K) = L := Nat.add_sub_cancel' hKL
    rw [h1]
    rw [h3, h4] at h2
    exact h2
  have hhalf2 : 2 * (q * (A' * A' + L + 2)) < b ^ L := by
    have hA2 : A' * A' ≤ 2 ^ (2 * E) := by
      have h1 : A' * A' ≤ 2 ^ E * 2 ^ E := Nat.mul_le_mul hA2E hA2E
      have h2 : (2 : ℕ) ^ E * 2 ^ E = 2 ^ (2 * E) := by
        rw [← pow_add]; congr 1; ring
      omega
    have hsum : A' * A' + L + 2 ≤ 2 ^ (2 * E + κ + 2) := by
      have hex : (2 : ℕ) ^ (2 * E + κ + 2) = 2 ^ (2 * E) * 2 ^ κ * 4 := by
        rw [pow_add, pow_add]; norm_num
      have hac1 : (2 : ℕ) ^ (2 * E) ≤ 2 ^ (2 * E) * 2 ^ κ :=
        Nat.le_mul_of_pos_right _ (by positivity)
      have hac2 : (2 : ℕ) ^ κ ≤ 2 ^ (2 * E) * 2 ^ κ :=
        Nat.le_mul_of_pos_left _ (by positivity)
      omega
    have h2q : 2 * q ≤ 2 ^ (q + 1) := by
      have h1 : q < 2 ^ q := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (q + 1) = 2 ^ q * 2 := pow_succ 2 q
      omega
    have hmul : 2 * (q * (A' * A' + L + 2)) ≤ 2 ^ (q + 1) * 2 ^ (2 * E + κ + 2) := by
      have h1 : 2 * (q * (A' * A' + L + 2)) = (2 * q) * (A' * A' + L + 2) := by ring
      rw [h1]
      exact Nat.mul_le_mul h2q hsum
    have hexp : (2 : ℕ) ^ (q + 1) * 2 ^ (2 * E + κ + 2) = 2 ^ (2 * E + κ + q + 3) := by
      rw [← pow_add]; congr 1; ring
    have hlt : (2 : ℕ) ^ (2 * E + κ + q + 3) * 2 ≤ 2 ^ L := by
      have h1 : (2 : ℕ) ^ (2 * E + κ + q + 3) * 2 = 2 ^ (2 * E + κ + q + 4) :=
        (pow_succ 2 _).symm
      rw [h1]
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    have ht1 : (1 : ℕ) ≤ 2 ^ (2 * E + κ + q + 3) := Nat.one_le_two_pow
    have h2L : (2 : ℕ) ^ L ≤ b ^ L := Nat.pow_le_pow_left hb L
    omega
  have hqC : q * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A')
      ≤ q * (2 * b ^ (L - K) * (E + κ + 5)) := Nat.mul_le_mul_left q hCle
  have hqN : q * (x + y * A' + L + 2) ≤ q * (A' * A' + L + 2) :=
    Nat.mul_le_mul_left q hNle
  have hdist : q * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A'
        + (x + y * A' + L + 2))
      = q * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A')
        + q * (x + y * A' + L + 2) := by ring
  omega

/-- **Purely periodic support irrationality.**  For every base `b ≥ 2` and
every `m`-periodic support `A` (`m ≥ 1`) containing a positive element,
`∑_{a ∈ A} 1/(b^a - 1)` is irrational.  At `m = 1` this recovers the full
support; residue classes, unions of residue classes, and gcd-pattern
supports are all instances. -/
theorem irrational_erdosSupportSeries_periodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, n + m ∈ A ↔ n ∈ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A) :=
  irrational_erdosSupportSeries_of_weighted_coeff_certificates b A hb
    (exists_weighted_coeff_certificates_supportCoeff_periodic b m A hb hm hper hpos)

/-- **Eventually periodic support irrationality (wave-10 frontier
theorem).**  For every base `b ≥ 2`: an infinite support whose membership is
`m`-periodic from some threshold `N₀` on has an irrational support series.
The purely periodic shift `A_pure = {n : n + m·N₀ ∈ A}` agrees with `A`
above the threshold, so the landed finite-prefix calculus transfers
irrationality across the finite symmetric difference. -/
theorem irrational_erdosSupportSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A))
    (hinf : A.Infinite) :
    Irrational (erdosSupportSeries b A) := by
  classical
  -- iterated step: adding `k·m` above the threshold preserves membership
  have hstep : ∀ (k n : ℕ), N₀ ≤ n → (n + k * m ∈ A ↔ n ∈ A) := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ihk =>
        intro n hn
        have h1 : n + (k + 1) * m = (n + k * m) + m := by ring
        have h2 : N₀ ≤ n + k * m := by omega
        rw [h1]
        exact (hper (n + k * m) h2).trans (ihk n hn)
  set Apure : Set ℕ := {n : ℕ | n + m * N₀ ∈ A} with hApuredef
  have hmN₀ : N₀ ≤ m * N₀ := Nat.le_mul_of_pos_left N₀ hm
  -- the shifted support is purely periodic
  have hpureper : ∀ n : ℕ, n + m ∈ Apure ↔ n ∈ Apure := by
    intro n
    have h1 : n + m + m * N₀ = (n + m * N₀) + m := by ring
    have h2 : N₀ ≤ n + m * N₀ := by omega
    constructor
    · intro hmem
      have h3 : (n + m * N₀) + m ∈ A := by
        rw [← h1]
        exact hmem
      exact (hper (n + m * N₀) h2).mp h3
    · intro hmem
      have h3 : (n + m * N₀) + m ∈ A := (hper (n + m * N₀) h2).mpr hmem
      rw [hApuredef]
      show n + m + m * N₀ ∈ A
      rw [h1]
      exact h3
  -- agreement above the threshold
  have hagree : ∀ n : ℕ, N₀ ≤ n → (n ∈ Apure ↔ n ∈ A) := by
    intro n hn
    have h1 : n + N₀ * m ∈ A ↔ n ∈ A := hstep N₀ n hn
    rw [hApuredef]
    show n + m * N₀ ∈ A ↔ n ∈ A
    rwa [Nat.mul_comm m N₀]
  -- a positive element of the pure support
  have hpurepos : ∃ a : ℕ, 0 < a ∧ a ∈ Apure := by
    obtain ⟨a, haA, hagt⟩ := hinf.exists_gt (max N₀ 1)
    have h1 : N₀ ≤ a := le_trans (le_max_left N₀ 1) (le_of_lt hagt)
    have h2 : 0 < a := lt_of_le_of_lt (Nat.zero_le _) hagt
    exact ⟨a, h2, (hagree a h1).mpr haA⟩
  have hpureirr : Irrational (erdosSupportSeries b Apure) :=
    irrational_erdosSupportSeries_periodic b m Apure hb hm hpureper hpurepos
  -- transfer through the common tail above the cut `N₀`
  have htailpure : Irrational (erdosSupportSeries b {n : ℕ | n ∈ Apure ∧ N₀ < n}) :=
    irrational_erdosSupportSeries_tail_of_irrational b Apure hb N₀ hpureirr
  have hseteq : {n : ℕ | n ∈ Apure ∧ N₀ < n} = {n : ℕ | n ∈ A ∧ N₀ < n} := by
    ext n
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hagree n (by omega)).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hagree n (by omega)).mpr h1, h2⟩
  rw [hseteq] at htailpure
  exact irrational_erdosSupportSeries_of_tail b A hb N₀ htailpure

/-- **Residue-class support irrationality**: for every base `b ≥ 2`, modulus
`m ≥ 1`, and residue `c`, the series `∑_{n ≡ c (m)} 1/(b^n - 1)` is
irrational. -/
theorem irrational_erdosSupportSeries_residueClass
    (b m c : ℕ) (hb : 2 ≤ b) (hm : 0 < m) :
    Irrational (erdosSupportSeries b {n : ℕ | n % m = c % m}) := by
  refine irrational_erdosSupportSeries_periodic b m _ hb hm ?_ ?_
  · intro n
    show (n + m) % m = c % m ↔ n % m = c % m
    rw [Nat.add_mod_right]
  · refine ⟨c % m + m, by omega, ?_⟩
    show (c % m + m) % m = c % m
    rw [Nat.add_mod_right, Nat.mod_mod_of_dvd c (dvd_refl m)]

/-- **Odd support irrationality**: `∑_{n odd} 1/(b^n - 1)` is irrational for
every base `b ≥ 2` — the first support class with density strictly between
`0` and `1` to land. -/
theorem irrational_erdosSupportSeries_odd (b : ℕ) (hb : 2 ≤ b) :
    Irrational (erdosSupportSeries b {n : ℕ | Odd n}) := by
  have hseteq : {n : ℕ | Odd n} = {n : ℕ | n % 2 = 1 % 2} := by
    ext n
    simp [Nat.odd_iff]
  rw [hseteq]
  exact irrational_erdosSupportSeries_residueClass b 2 1 hb (by norm_num)

/-- **Multiples support through the periodic engine**: the wave-8 dilation
theorem `A = dℕ` is also an instance of the periodic sieve — multiples of
`d` form a `d`-periodic support.  Sanity corollary demonstrating
subsumption; the dilation proof remains the canonical route. -/
theorem irrational_erdosSupportSeries_multiples_via_periodic
    (b d : ℕ) (hb : 2 ≤ b) (hd : 0 < d) :
    Irrational (erdosSupportSeries b {n : ℕ | d ∣ n}) := by
  refine irrational_erdosSupportSeries_periodic b d _ hb hd ?_ ?_
  · intro n
    show d ∣ n + d ↔ d ∣ n
    constructor
    · intro h
      have h2 : d ∣ (n + d) - d := Nat.dvd_sub h (dvd_refl d)
      simpa using h2
    · intro h
      exact Nat.dvd_add h (dvd_refl d)
  · exact ⟨d, hd, dvd_refl d⟩

/-! ## Weighted-coefficient calculus (wave 11): periodic Nat weights and
nonnegative rational periodic Lambert coefficients

Wave 10 proved Erdős #257 for eventually-periodic 0/1 supports through the
periodic divisor-orbit sieve.  This section lifts the sieve from indicator
supports to **multiplicity weights**: a bounded weight `w : ℕ → ℕ` is a
finite stack of indicator layers `χ_i(x) = (i < w x)`, each of which is
`m`-periodic whenever `w` is — so the landed predicate-level orbit theorem
applies layer by layer, and the weighted divisor coefficient
`weightedCoeff w n = ∑_{d ∣ n} w d` inherits the full `b^r` first-block
divisibility with NO new bijection arguments.  Combined with a
linear-growth generalisation of the generic coefficient engine
(`c n ≤ G·n` instead of `c n ≤ n`) and a `w ≤ W`-normalised weighted
Lambert bridge, this closes:

* `irrational_weightedErdosSeries_periodic` — every `m`-periodic Nat
  weight with a positive value has `∑_a w(a)/(b^a - 1)` irrational;
* `irrational_weightedErdosSeries_eventuallyPeriodic` — likewise for
  eventually periodic Nat weights with a positive value in the periodic
  tail;
* `irrational_ratWeightSeries_eventuallyPeriodic` — likewise for
  **nonnegative rational** eventually periodic coefficient sequences, by
  clearing one common denominator over the prefix-plus-period window.

The wave-10 support theorems are the `{0,1}`-valued instances
(`weightedCoeff_indicator_eq_supportCoeff`).  Mixed-sign rational periodic
coefficients (the full Luca–Tachiya statement) are NOT claimed: the
one-sided engine still needs tail positivity.  As the signed-lane socket,
the **one-extra-orbit defect** lemmas
(`weightedCoeff_modEq_of_periodic_extra_orbit`) show that exact valuation
`b·φ(m)` — one slot past the complete Euler cycles — pins the weighted
coefficient mod `b` to its cofactor value: complete cycles give
divisibility, one extra orbit gives a protected residue. -/

/-- **The weighted divisor coefficient** `∑_{d ∣ n} w d` — the Dirichlet
incidence `w * 1` of a multiplicity weight `w : ℕ → ℕ`.  At an indicator
weight this is `supportCoeff`; at `w ≡ 1` it is `τ`. -/
def weightedCoeff (w : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, w d

/-- Bounded weights give the `W·τ` growth envelope for the weighted
coefficient. -/
theorem weightedCoeff_le_mul_card_divisors (w : ℕ → ℕ) (W n : ℕ)
    (hW : ∀ d : ℕ, w d ≤ W) :
    weightedCoeff w n ≤ W * n.divisors.card := by
  unfold weightedCoeff
  calc ∑ d ∈ n.divisors, w d
      ≤ ∑ _d ∈ n.divisors, W := Finset.sum_le_sum fun d _ => hW d
    _ = n.divisors.card * W := by rw [Finset.sum_const, smul_eq_mul]
    _ = W * n.divisors.card := Nat.mul_comm _ _

/-- Linear growth envelope for the weighted coefficient:
`weightedCoeff w n ≤ W·n` — exactly the hypothesis shape of the
linear-growth coefficient engine. -/
theorem weightedCoeff_le_mul_self (w : ℕ → ℕ) (W n : ℕ)
    (hW : ∀ d : ℕ, w d ≤ W) :
    weightedCoeff w n ≤ W * n :=
  le_trans (weightedCoeff_le_mul_card_divisors w W n hW)
    (Nat.mul_le_mul_left W (Nat.card_divisors_le_self n))

/-- The self-divisor keeps the weighted coefficient above the weight:
`w n ≤ weightedCoeff w n` for `n ≠ 0`. -/
theorem weight_le_weightedCoeff (w : ℕ → ℕ) (n : ℕ) (hn : n ≠ 0) :
    w n ≤ weightedCoeff w n := by
  unfold weightedCoeff
  exact Finset.single_le_sum (fun d _ => Nat.zero_le (w d))
    (Nat.mem_divisors_self n hn)

/-- **Indicator weights recover the support coefficient**: the weighted
calculus strictly generalises the wave-8/9/10 support calculus. -/
theorem weightedCoeff_indicator_eq_supportCoeff (A : Set ℕ)
    [DecidablePred (· ∈ A)] (n : ℕ) :
    weightedCoeff (fun d => if d ∈ A then 1 else 0) n = supportCoeff A n := by
  rw [supportCoeff_eq_card_filter, Finset.card_filter]
  rfl

/-! ## Weighted-coefficient calculus: the periodic weight toolkit -/

/-- **Iterated eventual periodicity**: a function `m`-periodic from
threshold `N₀` on is invariant under adding any multiple of `m` above the
threshold.  Generic in the codomain — serves ℕ- and ℚ-valued weights. -/
theorem eventually_periodic_add_mul {α : Type*} (f : ℕ → α) (m N₀ : ℕ)
    (hper : ∀ n : ℕ, N₀ ≤ n → f (n + m) = f n) :
    ∀ (k n : ℕ), N₀ ≤ n → f (n + k * m) = f n := by
  intro k
  induction k with
  | zero => intro n _; simp
  | succ k ihk =>
      intro n hn
      have h1 : n + (k + 1) * m = (n + k * m) + m := by ring
      rw [h1, hper (n + k * m) (by omega), ihk n hn]

/-- **Fold-down for eventually periodic functions**: every value is
already taken on `[0, N₀ + m)` — prefix values verbatim, tail values by
reducing the offset mod `m`. -/
theorem eventually_periodic_fold {α : Type*} (f : ℕ → α) (m N₀ : ℕ)
    (hm : 0 < m) (hper : ∀ n : ℕ, N₀ ≤ n → f (n + m) = f n) :
    ∀ a : ℕ, ∃ r : ℕ, r < N₀ + m ∧ f a = f r := by
  intro a
  by_cases ha : a < N₀ + m
  · exact ⟨a, ha, rfl⟩
  · rw [not_lt] at ha
    set s : ℕ := (a - N₀) % m with hsdef
    set k : ℕ := (a - N₀) / m with hkdef
    have hs : s < m := by
      rw [hsdef]
      exact Nat.mod_lt _ hm
    have h1 : m * k + s = a - N₀ := by
      rw [hsdef, hkdef]
      exact Nat.div_add_mod (a - N₀) m
    have h2 : k * m = m * k := Nat.mul_comm k m
    have hsplit : a = (N₀ + s) + k * m := by omega
    refine ⟨N₀ + s, by omega, ?_⟩
    rw [hsplit]
    exact eventually_periodic_add_mul f m N₀ hper k (N₀ + s) (by omega)

/-- Eventually periodic Nat weights are globally bounded by their sup over
one prefix-plus-period window. -/
theorem eventually_periodic_weight_bound (w : ℕ → ℕ) (m N₀ : ℕ) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → w (n + m) = w n) :
    ∀ x : ℕ, w x ≤ (Finset.range (N₀ + m)).sup w := by
  intro x
  obtain ⟨r, hr, hxr⟩ := eventually_periodic_fold w m N₀ hm hper x
  rw [hxr]
  exact Finset.le_sup (Finset.mem_range.mpr hr)

/-! ## Weighted-coefficient calculus: the layer-cake decomposition -/

/-- **Layer-cake decomposition of the weighted coefficient.**  A weight
bounded by `W` is the stack of its indicator layers `χ_i(x) = (i < w x)`
for `i < W`, so the weighted divisor coefficient is the sum of the
`W` filtered divisor counts.  This is the bridge that lets every
predicate-level counting theorem act on multiplicity weights. -/
theorem weightedCoeff_eq_sum_card_filter (w : ℕ → ℕ) (W n : ℕ)
    (hW : ∀ d : ℕ, w d ≤ W) :
    weightedCoeff w n
      = ∑ i ∈ Finset.range W, ((n.divisors.filter fun D => i < w D).card) := by
  unfold weightedCoeff
  have hpoint : ∀ d : ℕ, w d = ((Finset.range W).filter fun i => i < w d).card := by
    intro d
    have hset : ((Finset.range W).filter fun i => i < w d) = Finset.range (w d) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have := hW d
      omega
    rw [hset, Finset.card_range]
  calc ∑ d ∈ n.divisors, w d
      = ∑ d ∈ n.divisors, ((Finset.range W).filter fun i => i < w d).card :=
        Finset.sum_congr rfl fun d _ => hpoint d
    _ = ∑ d ∈ n.divisors, ∑ i ∈ Finset.range W, (if i < w d then 1 else 0) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.card_filter]
    _ = ∑ i ∈ Finset.range W, ∑ d ∈ n.divisors, (if i < w d then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ i ∈ Finset.range W, ((n.divisors.filter fun D => i < w D).card) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.card_filter]

/-! ## Weighted-coefficient calculus: the layered periodic orbit sieve -/

/-- **Periodic orbit divisibility for weighted coefficients.**  An
`m`-periodic weight `w`, together with `|P|` primes above `m` at exact
valuation `b·φ(m) - 1`, forces `b^|P|` to divide `weightedCoeff w n`.
Each indicator layer `χ_i(x) = (i < w x)` is an `m`-periodic predicate, so
the landed predicate-level orbit theorem gives `b^|P|` on every layer of
the layer-cake decomposition — the weighted sieve costs no new counting
argument. -/
theorem bpow_dvd_weightedCoeff_of_periodic_exact_block
    (b m n : ℕ) (w : ℕ → ℕ) (hb : 2 ≤ b) (hm : 0 < m) (hn : n ≠ 0)
    (hper : ∀ x : ℕ, w (x + m) = w x)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hgt : ∀ p ∈ P, m < p)
    (hexact : ∀ p ∈ P, n.factorization p = b * m.totient - 1) :
    b ^ P.card ∣ weightedCoeff w n := by
  classical
  set W : ℕ := (Finset.range m).sup w with hWdef
  have hbound : ∀ x : ℕ, w x ≤ W := by
    intro x
    have h := eventually_periodic_weight_bound w m 0 hm (fun k _ => hper k) x
    simpa [hWdef] using h
  have hndvd : ∀ p ∈ P, ¬ p ∣ m := by
    intro p hp hdvd
    have h1 : p ≤ m := Nat.le_of_dvd hm hdvd
    have h2 := hgt p hp
    omega
  rw [weightedCoeff_eq_sum_card_filter w W n hbound]
  refine Finset.dvd_sum fun i _ => ?_
  exact bpow_dvd_card_filter_divisors_of_periodic_block m b hm (by omega) P
    (fun x => i < w x) n hn
    (fun x => by show i < w (x + m) ↔ i < w x; rw [hper x]) hprime hndvd hexact

/-! ## Weighted-coefficient calculus: the one-extra-orbit defect

Complete Euler cycles give divisibility; ONE extra orbit slot gives a
controlled residue.  At exact valuation `b·φ(m)` (instead of
`b·φ(m) - 1`), each divisor ray contributes `b` complete cycles plus a
single copy of its base value, so the whole coefficient is pinned mod `b`
to the coefficient of the cofactor.  This is the protected-residue
primitive the future signed-coefficient lane will consume: it converts
mixed-sign cancellation from an analytic positivity problem into a
finite modular problem.  No signed theorem is claimed here. -/

/-- **One-extra-slot cycle count**: over `s` complete periods plus one
extra slot, a `t`-periodic predicate holds `s` times its one-period count,
plus once more exactly when it holds at `0` — the extra slot `s·t` folds
back to the origin. -/
theorem card_filter_range_mul_succ_of_periodic (Q : ℕ → Prop)
    [inst : DecidablePred Q] (t : ℕ) (hQ : ∀ j : ℕ, Q (j + t) ↔ Q j) (s : ℕ) :
    ((Finset.range (s * t + 1)).filter fun j => Q j).card
      = s * ((Finset.range t).filter fun j => Q j).card
        + (if Q 0 then 1 else 0) := by
  have hQst : Q (s * t) ↔ Q 0 := by
    have h := periodic_pred_add_mul Q t hQ s 0
    simpa using h
  have hins : Finset.range (s * t + 1) = insert (s * t) (Finset.range (s * t)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  rw [hins, Finset.filter_insert]
  by_cases h : Q (s * t)
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp),
      card_filter_range_mul_of_periodic Q t hQ s, if_pos (hQst.mp h)]
  · rw [if_neg h, card_filter_range_mul_of_periodic Q t hQ s,
      if_neg (fun h0 => h (hQst.mpr h0))]
    omega

/-- **One-extra-orbit defect for filtered divisor counts.**  If `χ` is
`m`-periodic, `p ∤ m` is prime, and `p ∤ R`, then passing from `R` to
`p^(b·φ(m))·R` preserves the `χ`-filtered divisor count mod `b`: each
divisor ray through `d ∣ R` contributes `b` complete Euler cycles plus the
single extra slot `χ(p^(b·φ(m))·d) = χ(d)`. -/
theorem card_filter_divisors_modEq_of_periodic_extra_orbit
    (b m p R : ℕ) (χ : ℕ → Prop) [inst : DecidablePred χ]
    (hp : Nat.Prime p) (hR : R ≠ 0) (hpR : ¬ p ∣ R)
    (hpm : ¬ p ∣ m)
    (hper : ∀ x : ℕ, χ (x + m) ↔ χ x) :
    ((p ^ (b * m.totient) * R).divisors.filter fun D => χ D).card
      ≡ ((R.divisors.filter fun D => χ D).card) [MOD b] := by
  classical
  have hdecomp :=
    card_filter_divisors_prime_pow_mul_eq_sum χ p (b * m.totient) R hp hR hpR
  have heuler : p ^ m.totient ≡ 1 [MOD m] :=
    Nat.ModEq.pow_totient ((hp.coprime_iff_not_dvd).mpr hpm)
  have hray : ∀ d ∈ R.divisors,
      ((Finset.range (b * m.totient + 1)).filter fun j => χ (p ^ j * d)).card
        = b * ((Finset.range m.totient).filter fun j => χ (p ^ j * d)).card
          + (if χ (p ^ 0 * d) then 1 else 0) := by
    intro d _
    have hQper : ∀ j : ℕ, χ (p ^ (j + m.totient) * d) ↔ χ (p ^ j * d) := by
      intro j
      have h1 : p ^ (j + m.totient) * d = (p ^ j * d) * p ^ m.totient := by
        rw [pow_add]
        ring
      have h2 : (p ^ j * d) * p ^ m.totient ≡ (p ^ j * d) * 1 [MOD m] :=
        Nat.ModEq.mul_left _ heuler
      rw [h1]
      refine periodic_pred_iff_of_modEq χ m hper ?_
      rw [mul_one] at h2
      exact h2
    exact card_filter_range_mul_succ_of_periodic (fun j => χ (p ^ j * d))
      m.totient hQper b
  have hsum : ((p ^ (b * m.totient) * R).divisors.filter fun D => χ D).card
      = b * (∑ d ∈ R.divisors,
            ((Finset.range m.totient).filter fun j => χ (p ^ j * d)).card)
        + ((R.divisors.filter fun D => χ D).card) := by
    calc ((p ^ (b * m.totient) * R).divisors.filter fun D => χ D).card
        = ∑ d ∈ R.divisors,
            ((Finset.range (b * m.totient + 1)).filter fun j => χ (p ^ j * d)).card :=
          hdecomp
      _ = ∑ d ∈ R.divisors,
            (b * ((Finset.range m.totient).filter fun j => χ (p ^ j * d)).card
              + (if χ (p ^ 0 * d) then 1 else 0)) :=
          Finset.sum_congr rfl hray
      _ = b * (∑ d ∈ R.divisors,
            ((Finset.range m.totient).filter fun j => χ (p ^ j * d)).card)
          + ∑ d ∈ R.divisors, (if χ (p ^ 0 * d) then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = b * (∑ d ∈ R.divisors,
            ((Finset.range m.totient).filter fun j => χ (p ^ j * d)).card)
          + ((R.divisors.filter fun D => χ D).card) := by
          congr 1
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [pow_zero, one_mul]
  rw [hsum]
  have hfin : ((R.divisors.filter fun D => χ D).card)
      ≡ b * (∑ d ∈ R.divisors,
          ((Finset.range m.totient).filter fun j => χ (p ^ j * d)).card)
        + ((R.divisors.filter fun D => χ D).card) [MOD b] := by
    refine (Nat.modEq_iff_dvd' (Nat.le_add_left _ _)).mpr ?_
    rw [Nat.add_sub_cancel]
    exact dvd_mul_right b _
  exact hfin.symm

/-- **One-extra-orbit defect for weighted coefficients (signed-lane
socket).**  For an `m`-periodic weight `w`, exact valuation `b·φ(m)` at a
prime `p ∤ m` pins the weighted coefficient mod `b` to the cofactor
coefficient: `weightedCoeff w (p^(b·φ(m))·R) ≡ weightedCoeff w R [MOD b]`.
Complete cycles give the divisibility engine of this wave; the single
extra orbit gives the protected residue a future mixed-sign certificate
needs.  Layer-cake over the predicate-level defect. -/
theorem weightedCoeff_modEq_of_periodic_extra_orbit
    (b m p R : ℕ) (w : ℕ → ℕ) (hm : 0 < m) (hp : Nat.Prime p) (hR : R ≠ 0)
    (hpR : ¬ p ∣ R) (hpm : ¬ p ∣ m)
    (hper : ∀ x : ℕ, w (x + m) = w x) :
    weightedCoeff w (p ^ (b * m.totient) * R) ≡ weightedCoeff w R [MOD b] := by
  classical
  set W : ℕ := (Finset.range m).sup w with hWdef
  have hbound : ∀ x : ℕ, w x ≤ W := by
    intro x
    have h := eventually_periodic_weight_bound w m 0 hm (fun k _ => hper k) x
    simpa [hWdef] using h
  have hterm : ∀ i : ℕ,
      (((p ^ (b * m.totient) * R).divisors.filter fun D => i < w D).card) % b
        = (((R.divisors.filter fun D => i < w D).card)) % b := fun i =>
    card_filter_divisors_modEq_of_periodic_extra_orbit b m p R
      (fun x => i < w x) hp hR hpR hpm
      (fun x => by show i < w (x + m) ↔ i < w x; rw [hper x])
  rw [weightedCoeff_eq_sum_card_filter w W (p ^ (b * m.totient) * R) hbound,
    weightedCoeff_eq_sum_card_filter w W R hbound]
  show (∑ i ∈ Finset.range W,
      ((p ^ (b * m.totient) * R).divisors.filter fun D => i < w D).card) % b
    = (∑ i ∈ Finset.range W,
      ((R.divisors.filter fun D => i < w D).card)) % b
  rw [Finset.sum_nat_mod, Finset.sum_nat_mod (Finset.range W) b
    (fun i => ((R.divisors.filter fun D => i < w D).card))]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hterm i

/-! ## Weighted-coefficient calculus: the linear-growth coefficient engine

The wave-8 generic engine assumed the growth envelope `c m ≤ m` — enough
for `τ` and for support coefficients, but not for weighted coefficients,
which only satisfy `weightedCoeff w n ≤ W·n`.  These are the `G`-linear
generalisations; each delegates its analytic content to the `c = id`
instance of the landed lemma and scales by `G`. -/

/-- Summability of a coefficient series under linear growth `c m ≤ G·m`. -/
theorem summable_coeff_term_linear (b G : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b)
    (hgrowth : ∀ m : ℕ, c m ≤ G * m) :
    Summable (fun m : ℕ => ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  have hid : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ)) / (b : ℝ) ^ (m + 1)) :=
    summable_coeff_term b (fun m => m) hb (fun m => le_rfl)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    (hid.mul_left (G : ℝ))
  have hc : ((c (m + 1) : ℝ)) ≤ (G : ℝ) * ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hgrowth (m + 1)
  calc ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)
      ≤ ((G : ℝ) * ((m + 1 : ℕ) : ℝ)) / (b : ℝ) ^ (m + 1) := by gcongr
    _ = (G : ℝ) * ((((m + 1 : ℕ) : ℝ)) / (b : ℝ) ^ (m + 1)) := mul_div_assoc _ _ _

/-- Shifted-tail summability under linear growth. -/
theorem summable_coeff_shift_tail_linear (b N G : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b)
    (hgrowth : ∀ m : ℕ, c m ≤ G * m) :
    Summable (fun r : ℕ => ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1)) := by
  have hid : Summable (fun r : ℕ => (((N + r + 1 : ℕ) : ℝ)) / (b : ℝ) ^ (r + 1)) :=
    summable_coeff_shift_tail b N (fun m => m) hb (fun m => le_rfl)
  refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
    (hid.mul_left (G : ℝ))
  have hc : ((c (N + r + 1) : ℝ)) ≤ (G : ℝ) * ((N + r + 1 : ℕ) : ℝ) := by
    exact_mod_cast hgrowth (N + r + 1)
  calc ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1)
      ≤ ((G : ℝ) * ((N + r + 1 : ℕ) : ℝ)) / (b : ℝ) ^ (r + 1) := by gcongr
    _ = (G : ℝ) * ((((N + r + 1 : ℕ) : ℝ)) / (b : ℝ) ^ (r + 1)) := mul_div_assoc _ _ _

/-- **Generic shifted-tail decomposition under linear growth**: `b^N`
times the coefficient series is an integer plus the shifted tail. -/
theorem bpow_mul_coeff_series_eq_int_add_tail_linear (b N G : ℕ) (c : ℕ → ℕ)
    (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ G * m) :
    ∃ z : ℤ,
      (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) =
        (z : ℝ) + ∑' r : ℕ, ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hsum := summable_coeff_term_linear b G c hb hgrowth
  refine ⟨((∑ i ∈ Finset.range N, c (i + 1) * b ^ (N - (i + 1)) : ℕ) : ℤ), ?_⟩
  rw [← Summable.sum_add_tsum_nat_add N hsum, mul_add]
  congr 1
  · push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiN : i < N := Finset.mem_range.mp hi
    have hsplit : (b : ℝ) ^ N = (b : ℝ) ^ (N - (i + 1)) * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    field_simp
  · rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [show r + N + 1 = N + r + 1 from by omega]
    have hsplit : (b : ℝ) ^ (N + r + 1) = (b : ℝ) ^ N * (b : ℝ) ^ (r + 1) := by ring
    rw [hsplit]
    field_simp

/-- **Crude far-tail bound under linear growth**: past index `L`,
`∑_t c(N+L+1+t)/b^(L+1+t) ≤ G·(N+L+2)/b^L`.  The analytic content is the
`c = id` instance of the landed far-tail lemma, scaled by `G`. -/
theorem coeff_far_tail_le_linear (b N L G : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b)
    (hgrowth : ∀ m : ℕ, c m ≤ G * m) :
    ∑' t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t)
      ≤ ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hid : ∑' t : ℕ, (((N + L + 1 + t : ℕ) : ℝ)) / (b : ℝ) ^ (L + 1 + t)
      ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L :=
    coeff_far_tail_le b N L (fun m => m) hb (fun m => le_rfl)
  have hshift_id :=
    summable_coeff_shift_tail b (N + L) (fun m => m) hb (fun m => le_rfl)
  have hid_sum : Summable
      (fun t : ℕ => (((N + L + 1 + t : ℕ) : ℝ)) / (b : ℝ) ^ (L + 1 + t)) := by
    have hmul := hshift_id.mul_left ((1 : ℝ) / (b : ℝ) ^ L)
    refine hmul.congr fun t => ?_
    rw [show N + L + t + 1 = N + L + 1 + t from by omega]
    have hsplit : (b : ℝ) ^ (L + 1 + t) = (b : ℝ) ^ L * (b : ℝ) ^ (t + 1) := by ring
    rw [hsplit]
    field_simp
  have hle : ∀ t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t)
      ≤ (G : ℝ) * ((((N + L + 1 + t : ℕ) : ℝ)) / (b : ℝ) ^ (L + 1 + t)) := by
    intro t
    have hc : ((c (N + L + 1 + t) : ℝ)) ≤ (G : ℝ) * ((N + L + 1 + t : ℕ) : ℝ) := by
      exact_mod_cast hgrowth (N + L + 1 + t)
    calc ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t)
        ≤ ((G : ℝ) * ((N + L + 1 + t : ℕ) : ℝ)) / (b : ℝ) ^ (L + 1 + t) := by gcongr
      _ = (G : ℝ) * ((((N + L + 1 + t : ℕ) : ℝ)) / (b : ℝ) ^ (L + 1 + t)) :=
          mul_div_assoc _ _ _
  have hLHS_sum : Summable
      (fun t : ℕ => ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t)) :=
    Summable.of_nonneg_of_le (fun t => by positivity) hle (hid_sum.mul_left (G : ℝ))
  calc (∑' t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t))
      ≤ ∑' t : ℕ, (G : ℝ) * ((((N + L + 1 + t : ℕ) : ℝ)) / (b : ℝ) ^ (L + 1 + t)) :=
        Summable.tsum_le_tsum hle hLHS_sum (hid_sum.mul_left (G : ℝ))
    _ = (G : ℝ) * ∑' t : ℕ, (((N + L + 1 + t : ℕ) : ℝ)) / (b : ℝ) ^ (L + 1 + t) :=
        tsum_mul_left
    _ ≤ (G : ℝ) * (((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L) :=
        mul_le_mul_of_nonneg_left hid (Nat.cast_nonneg G)
    _ = ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
        push_cast
        ring

/-- **Linear-growth weighted-coefficient certificate consumer,
one-sided.**  The wave-8 near-integer witness with the growth envelope
relaxed to `c m ≤ G·m` and the arithmetic condition rescaled to
`q·(C + G·(N+L+2)) < b^L`.  At `G = 1` this is the landed consumer. -/
theorem near_int_witness_of_weighted_coeff_block_certificate_linear
    (b q N K L C G : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (hgrowth : ∀ m : ℕ, c m ≤ G * m)
    (hblock : ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ c (N + r))
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C)
    (hpos : ∃ t : ℕ, 0 < c (N + L + 1 + t))
    (harith : q * (C + G * (N + L + 2)) < b ^ L) :
    ∃ z : ℤ,
      0 < (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ) ∧
        (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ) < 1 / (q : ℝ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨z₀, hz₀⟩ := bpow_mul_coeff_series_eq_int_add_tail_linear b N G c hb hgrowth
  have hfsum : Summable
      (fun r : ℕ => ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1)) :=
    summable_coeff_shift_tail_linear b N G c hb hgrowth
  have hfarsum : Summable
      (fun t : ℕ => ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) :=
    (summable_nat_add_iff L).mpr hfsum
  -- split the tail at L
  have hsplitL : (∑' r : ℕ, ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  -- split the finite part at K
  have hsplitK : (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  -- the first block is an integer
  set z₁ : ℕ := ∑ i ∈ Finset.range K, c (N + i + 1) / b ^ (i + 1) with hz₁def
  have hz₁ : ((z₁ : ℕ) : ℝ)
      = ∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [hz₁def]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp hi
    have hdvd : b ^ (i + 1) ∣ c (N + i + 1) :=
      hblock (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hbpow0 : ((b ^ (i + 1) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_div hdvd hbpow0]
    push_cast
    ring
  -- remainder positivity: some coefficient past the window is nonzero
  have hmid_nonneg : (0 : ℝ)
      ≤ ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨t₀, ht₀⟩ := hpos
  have hfar_pos : (0 : ℝ)
      < ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    have hcpos : (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) := by
      have hidx : N + (t₀ + L) + 1 = N + L + 1 + t₀ := by omega
      have h0 : 0 < c (N + (t₀ + L) + 1) := by rw [hidx]; exact ht₀
      exact_mod_cast h0
    have hterm0 : (0 : ℝ)
        < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := by positivity
    calc (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := hterm0
      _ ≤ _ := hfarsum.le_tsum t₀ fun j _ => by positivity
  -- middle window: exact weighted sum over the common denominator b^L
  have hterm : ∀ i ∈ Finset.Ico K L,
      ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1)
        = ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    intro i hi
    obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
    have hb1 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
    have hbL' : ((b : ℝ) ^ L) ≠ 0 := by positivity
    have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (L - (i + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_div_iff hb1 hbL']
    push_cast
    rw [hsplit]
    ring
  have hreindex : (∑ i ∈ Finset.Ico K L, c (N + i + 1) * b ^ (L - (i + 1)))
      = ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) := by
    have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hn : L + 1 - (K + 1) = L - K := by omega
    rw [hn]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : N + (K + j) + 1 = N + (K + 1 + j) := by omega
    have h2 : L - (K + j + 1) = L - (K + 1 + j) := by omega
    rw [h1, h2]
  have hmid : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      ≤ (C : ℝ) / (b : ℝ) ^ L := by
    have hsum_eq : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    have hnum : (∑ i ∈ Finset.Ico K L,
        ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) ≤ (C : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hreindex.trans_le hmiddle
    calc (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := hsum_eq
      _ ≤ (C : ℝ) / (b : ℝ) ^ L := by gcongr
  -- far tail bound, reshaped from the linear far-tail lemma
  have hfar_eq : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      ≤ ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact coeff_far_tail_le_linear b N L G c hb hgrowth
  -- assemble the one-sided witness
  have hdiff : (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
      - ((z₀ + (z₁ : ℤ) : ℤ) : ℝ)
      = (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    rw [hz₀, hsplitL, hsplitK]
    push_cast
    rw [← hz₁]
    ring
  have hR_pos : (0 : ℝ)
      < (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    add_pos_of_nonneg_of_pos hmid_nonneg hfar_pos
  refine ⟨z₀ + (z₁ : ℤ), ?_, ?_⟩
  · rw [hdiff]
    exact hR_pos
  · rw [hdiff]
    have hsum_le : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
        ≤ (C : ℝ) / (b : ℝ) ^ L + ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L :=
      add_le_add hmid hfar
    refine lt_of_le_of_lt hsum_le ?_
    have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    have hc : (q : ℝ) * ((C : ℝ) + ((G * (N + L + 2) : ℕ) : ℝ)) < (b : ℝ) ^ L := by
      exact_mod_cast harith
    rw [← add_div, div_lt_div_iff₀ hbL hq', one_mul]
    calc ((C : ℝ) + ((G * (N + L + 2) : ℕ) : ℝ)) * (q : ℝ)
        = (q : ℝ) * ((C : ℝ) + ((G * (N + L + 2) : ℕ) : ℝ)) := mul_comm _ _
      _ < (b : ℝ) ^ L := hc

/-- **Linear-growth coefficient-series irrationality from weighted
certificates.**  If a coefficient sequence with growth envelope
`c m ≤ G·m` admits a `G`-rescaled weighted block certificate for every
precision, then `∑ c(m)/b^m` is irrational.  Weighted periodic Lambert
series are the instance `c = weightedCoeff w`, `G = W`. -/
theorem irrational_coeff_series_of_weighted_coeff_block_certificates_linear
    (b G : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ G * m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ c (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < c (N + L + 1 + t)) ∧
        q * (C + G * (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  apply irrational_of_pow_mul_near_int b
  intro q hq
  obtain ⟨N, K, L, C, hKL, hblock, hmiddle, hpos, harith⟩ := hcert q hq
  obtain ⟨z, hz_pos, hz_lt⟩ :=
    near_int_witness_of_weighted_coeff_block_certificate_linear
      b q N K L C G c hb hq hKL hgrowth hblock hmiddle hpos harith
  refine ⟨N, z, ?_, ?_⟩
  · rw [abs_of_pos hz_pos]
    exact hz_pos
  · rw [abs_of_pos hz_pos]
    exact hz_lt

/-! ## Weighted-coefficient calculus: the Nat-weight Lambert bridge -/

/-- **The weighted Erdős series** `∑_a w(a)/(b^a - 1)` for a Nat weight.
The `a = 0` term is `w(0)/0 = 0` under real division conventions.  At an
indicator weight this is `erdosSupportSeries`; nonnegative rational
coefficient series reduce to it by clearing denominators. -/
noncomputable def weightedErdosSeries (b : ℕ) (w : ℕ → ℕ) : ℝ :=
  ∑' a : ℕ, ((w a : ℝ)) / ((b : ℝ) ^ a - 1)

/-- Summability of the weighted series terms for a bounded weight,
dominated by the geometric envelope `W·(2·(1/b)^a)`. -/
theorem summable_weightedErdos_term (b W : ℕ) (w : ℕ → ℕ) (hb : 2 ≤ b)
    (hW : ∀ n : ℕ, w n ≤ W) :
    Summable (fun a : ℕ => ((w a : ℝ)) / ((b : ℝ) ^ a - 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  have hgeo : Summable (fun a : ℕ => (W : ℝ) * (2 * ((1 : ℝ) / b) ^ a)) :=
    ((summable_geometric_of_lt_one (by positivity)
      (by rw [div_lt_one hb_pos]; linarith)).mul_left 2).mul_left (W : ℝ)
  refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) hgeo
  · rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      simp
    · have h1 : (1 : ℝ) < (b : ℝ) ^ a := one_lt_pow₀ hb1 (by omega)
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      have h00 : ((w 0 : ℝ)) / ((b : ℝ) ^ 0 - 1) = 0 := by simp
      rw [h00]
      positivity
    · have hba : (2 : ℝ) ≤ (b : ℝ) ^ a := by
        calc (2 : ℝ) ≤ (b : ℝ) := hb2
          _ = (b : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (b : ℝ) ^ a := pow_le_pow_right₀ (by linarith) (by omega)
      have hkey : ((b : ℝ) ^ a) ≤ 2 * ((b : ℝ) ^ a - 1) := by linarith
      have hwa : ((w a : ℝ)) ≤ (W : ℝ) := by exact_mod_cast hW a
      have hpow : ((1 : ℝ) / b) ^ a = 1 / (b : ℝ) ^ a := by
        rw [div_pow, one_pow]
      rw [hpow, mul_one_div,
        show (W : ℝ) * (2 / (b : ℝ) ^ a) = ((W : ℝ) * 2) / (b : ℝ) ^ a from by ring,
        div_le_div_iff₀ (by linarith) (by positivity)]
      have hprod : ((w a : ℝ)) * ((b : ℝ) ^ a) ≤ (W : ℝ) * (2 * ((b : ℝ) ^ a - 1)) :=
        mul_le_mul hwa hkey (by positivity) (Nat.cast_nonneg W)
      linarith
/-- **The Nat-weight Lambert bridge**: for a weight `w ≤ W` (`W > 0`),
`∑_a w(a)/(b^a - 1) = ∑_n weightedCoeff w (n)/b^n`.  Normalising by `W`
feeds the landed real-weight Lambert identity; multiplying back exposes
the weighted divisor coefficient. -/
theorem weightedErdosSeries_eq_tsum_weightedCoeff (b W : ℕ) (w : ℕ → ℕ)
    (hb : 2 ≤ b) (hWpos : 0 < W) (hW : ∀ n : ℕ, w n ≤ W) :
    weightedErdosSeries b w
      = ∑' m : ℕ, ((weightedCoeff w (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hr1 : 1 / (b : ℝ) < 1 := by
    rw [div_lt_one hb_pos]
    linarith
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
  have hW0 : ((W : ℝ)) ≠ 0 := ne_of_gt hWR
  set wR : ℕ → ℝ := fun e => ((w e : ℝ)) / (W : ℝ) with hwRdef
  have hw0 : ∀ e : ℕ, 0 ≤ wR e := by
    intro e
    rw [hwRdef]
    positivity
  have hw1 : ∀ e : ℕ, wR e ≤ 1 := by
    intro e
    rw [hwRdef, div_le_one hWR]
    exact_mod_cast hW e
  -- the per-index Lambert term identity, junk-safe at 0
  have hterm_eq : ∀ a : ℕ, 0 < a →
      ((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a) = 1 / ((b : ℝ) ^ a - 1) := by
    intro a ha
    have hbn : (1 : ℝ) < (b : ℝ) ^ a := one_lt_pow₀ hb1 (by omega)
    have hbn0 : (b : ℝ) ^ a ≠ 0 := by positivity
    have hbn1 : (b : ℝ) ^ a - 1 ≠ 0 := ne_of_gt (by linarith)
    have h1X : (1 : ℝ) - 1 / (b : ℝ) ^ a ≠ 0 := by
      have hEq : (1 : ℝ) - 1 / (b : ℝ) ^ a = ((b : ℝ) ^ a - 1) / (b : ℝ) ^ a := by
        field_simp
      rw [hEq]
      exact div_ne_zero hbn1 hbn0
    rw [div_pow, one_pow]
    field_simp
  have hpoint : ∀ a : ℕ,
      ((w a : ℝ)) / ((b : ℝ) ^ a - 1)
        = (W : ℝ) * (wR a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a))) := by
    intro a
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      simp
    · have hbn : (1 : ℝ) < (b : ℝ) ^ a := one_lt_pow₀ hb1 (by omega)
      have hbn1 : (b : ℝ) ^ a - 1 ≠ 0 := ne_of_gt (by linarith)
      rw [hterm_eq a hpos, hwRdef]
      field_simp
  have hsumR : Summable
      (fun a : ℕ => wR a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a))) := by
    have hsum0 : Summable (fun a : ℕ => ((w a : ℝ)) / ((b : ℝ) ^ a - 1)) :=
      summable_weightedErdos_term b W w hb hW
    have hsum1 : Summable
        (fun a : ℕ =>
          (W : ℝ) * (wR a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a)))) :=
      hsum0.congr hpoint
    have hsum2 := hsum1.mul_left ((W : ℝ))⁻¹
    refine hsum2.congr fun a => ?_
    rw [← mul_assoc, inv_mul_cancel₀ hW0, one_mul]
  calc weightedErdosSeries b w
      = ∑' a : ℕ, (W : ℝ) * (wR a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a))) := by
        unfold weightedErdosSeries
        exact tsum_congr hpoint
    _ = (W : ℝ) * ∑' a : ℕ, wR a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a)) :=
        tsum_mul_left
    _ = (W : ℝ) * (wR 0 * (((1 : ℝ) / b) ^ 0 / (1 - ((1 : ℝ) / b) ^ 0))
          + ∑' m : ℕ, wR (m + 1)
              * (((1 : ℝ) / b) ^ (m + 1) / (1 - ((1 : ℝ) / b) ^ (m + 1)))) := by
        rw [hsumR.tsum_eq_zero_add]
    _ = (W : ℝ) * ∑' m : ℕ, wR (m + 1)
          * (((1 : ℝ) / b) ^ (m + 1) / (1 - ((1 : ℝ) / b) ^ (m + 1))) := by
        simp
    _ = (W : ℝ) * ∑' d : ℕ+, wR (d : ℕ)
          * (((1 : ℝ) / b) ^ (d : ℕ) / (1 - ((1 : ℝ) / b) ^ (d : ℕ))) := by
        rw [tsum_pnat_eq_tsum_succ (f := fun a : ℕ =>
          wR a * (((1 : ℝ) / b) ^ a / (1 - ((1 : ℝ) / b) ^ a)))]
    _ = (W : ℝ) * ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, wR e) * ((1 : ℝ) / b) ^ (n : ℕ) := by
        rw [weighted_lambert_series_identity wR hw0 hw1 hr0 hr1]
    _ = ∑' n : ℕ+, (W : ℝ) * ((∑ e ∈ (n : ℕ).divisors, wR e) * ((1 : ℝ) / b) ^ (n : ℕ)) :=
        (tsum_mul_left).symm
    _ = ∑' n : ℕ+, ((weightedCoeff w (n : ℕ) : ℝ)) / (b : ℝ) ^ (n : ℕ) := by
        refine tsum_congr fun n => ?_
        have hcast : ((weightedCoeff w (n : ℕ) : ℕ) : ℝ)
            = ∑ e ∈ (n : ℕ).divisors, ((w e : ℝ)) := by
          unfold weightedCoeff
          push_cast
          rfl
        have hWsum : (W : ℝ) * (∑ e ∈ (n : ℕ).divisors, wR e)
            = ∑ e ∈ (n : ℕ).divisors, ((w e : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hwRdef]
          field_simp
        calc (W : ℝ) * ((∑ e ∈ (n : ℕ).divisors, wR e) * ((1 : ℝ) / b) ^ (n : ℕ))
            = ((W : ℝ) * (∑ e ∈ (n : ℕ).divisors, wR e)) * ((1 : ℝ) / b) ^ (n : ℕ) :=
              (mul_assoc _ _ _).symm
          _ = (∑ e ∈ (n : ℕ).divisors, ((w e : ℝ))) * ((1 : ℝ) / b) ^ (n : ℕ) := by
              rw [hWsum]
          _ = ((weightedCoeff w (n : ℕ) : ℝ)) / (b : ℝ) ^ (n : ℕ) := by
              rw [← hcast, div_pow, one_pow, mul_one_div]
    _ = ∑' m : ℕ, ((weightedCoeff w (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1) :=
        tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
          ((weightedCoeff w n : ℝ)) / (b : ℝ) ^ n)

/-! ## Weighted-coefficient calculus: periodic weight certificate supply -/

/-- **Weighted coefficient certificates for periodic Nat weights.**  For
every base `b ≥ 2` and every `m`-periodic weight `w ≤ W` with a positive
value at a positive index, the layered periodic orbit sieve manufactures a
linear-growth certificate at every precision: the exact-valuation frame at
`B = b·φ(m)` feeds the layer-cake orbit divisibility for the first block,
`weightedCoeff ≤ W·τ` scales the selected divisor-pair average through the
middle window, the forward orbit of a positive weight value keeps the far
tail alive, and the frame precision is amplified to `q·W` so the final
inequality closes against the `W`-scaled middle and tail. -/
theorem exists_weighted_coeff_certificates_weightedCoeff_periodic
    (b m W : ℕ) (w : ℕ → ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hW : ∀ n : ℕ, w n ≤ W) (hWpos : 0 < W)
    (hpos : ∃ a : ℕ, 0 < a ∧ 0 < w a) :
    ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
      (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ weightedCoeff w (N + r)) ∧
      (∑ r ∈ Finset.Icc (K + 1) L, weightedCoeff w (N + r) * b ^ (L - r) ≤ C) ∧
      (∃ t : ℕ, 0 < weightedCoeff w (N + L + 1 + t)) ∧
      q * (C + W * (N + L + 2)) < b ^ L := by
  intro q hq
  have htpos : 0 < m.totient := Nat.totient_pos.mpr hm
  set q' : ℕ := q * W with hq'def
  have hq' : 0 < q' := Nat.mul_pos hq hWpos
  set B : ℕ := b * m.totient with hBdef
  have hB : 2 ≤ B := by
    have h1 : b ≤ b * m.totient := Nat.le_mul_of_pos_right b htpos
    omega
  set K : ℕ := 9 * (q' + B + m + 100) with hKdef
  set κ : ℕ := 3 * (2 * B * K ^ 2 + 1) + (2 * B * K ^ 2 * (K * (K + 1) + 1) + q' + 4)
    with hκdef
  set E : ℕ := B * K ^ 2 * (K * (K + 1) + κ + 1) with hEdef
  obtain ⟨hparamA, hparamB, hK1, hKκpow, hmK⟩ :=
    certificate_param_arithmetic_periodic b B m q' K κ E hb hB hq' hKdef hκdef hEdef
  set L : ℕ := 2 ^ κ with hLdef
  clear_value K κ E L
  have hKL : K ≤ L := hKκpow
  obtain ⟨x, A', P, hApos, hxA, hLA, hAle, hsupp, hcards, hprimes, hgtL, hval⟩ :=
    exists_bounded_exact_valuation_frame B L K hB hK1 hKL
  have hA2E : A' ≤ 2 ^ E := by
    have h1 : L + 1 ≤ 2 ^ (κ + 1) := by
      have h1a : (2 : ℕ) ^ (κ + 1) = 2 ^ κ * 2 := pow_succ 2 κ
      omega
    have h4 : A' ≤ (2 ^ (K * (K + 1) + (κ + 1))) ^ (B * K ^ 2) := by
      calc A' ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (B * K ^ 2) := hAle
        _ ≤ (2 ^ (K * (K + 1)) * 2 ^ (κ + 1)) ^ (B * K ^ 2) := by
            apply Nat.pow_le_pow_left
            exact Nat.mul_le_mul_left _ h1
        _ = (2 ^ (K * (K + 1) + (κ + 1))) ^ (B * K ^ 2) := by rw [← pow_add]
    have h5 : ((2 : ℕ) ^ (K * (K + 1) + (κ + 1))) ^ (B * K ^ 2)
        = 2 ^ ((K * (K + 1) + (κ + 1)) * (B * K ^ 2)) := (pow_mul 2 _ _).symm
    have h6 : (2 : ℕ) ^ ((K * (K + 1) + (κ + 1)) * (B * K ^ 2)) ≤ 2 ^ E := by
      apply Nat.pow_le_pow_right (by norm_num)
      have h7 : E = (K * (K + 1) + (κ + 1)) * (B * K ^ 2) := by rw [hEdef]; ring
      omega
    omega
  obtain ⟨y, hyA, hWy⟩ :=
    selected_weighted_middle_of_supported_frame b x A' K L A' hb hApos hsupp
  -- first block: layered periodic orbit sieve on the exposed prime blocks
  have hfirst : ∀ r ∈ Finset.Icc 1 K, b ^ r ∣ weightedCoeff w (x + y * A' + r) := by
    intro r hr
    have hr1 := (Finset.mem_Icc.mp hr).1
    have hne : x + y * A' + r ≠ 0 := by omega
    have hgtm : ∀ p ∈ P r, m < p := by
      intro p hp
      have h1 := hgtL r hr p hp
      have h2 : m ≤ K := hmK
      have h3 : K ≤ L := hKL
      omega
    have hexact : ∀ p ∈ P r, (x + y * A' + r).factorization p = b * m.totient - 1 := by
      intro p hp
      have h1 := hval y r hr p hp
      rwa [hBdef] at h1
    have hdvd := bpow_dvd_weightedCoeff_of_periodic_exact_block b m (x + y * A' + r) w
      hb hm hne hper (P r) (fun p hp => hprimes r hr p hp) hgtm hexact
    rwa [hcards r hr] at hdvd
  -- middle window: dominate by W·τ and reuse the selected divisor-pair average
  have hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, weightedCoeff w (x + y * A' + r) * b ^ (L - r)
      ≤ W * ((b ^ (L - K)
          * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + A' * A' + L)), (A' / d + 1))) / A') := by
    calc ∑ r ∈ Finset.Icc (K + 1) L, weightedCoeff w (x + y * A' + r) * b ^ (L - r)
        ≤ ∑ r ∈ Finset.Icc (K + 1) L,
            W * ((x + y * A' + r).divisors.card * b ^ (L - r)) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (weightedCoeff_le_mul_card_divisors w W _ hW)
      _ = W * ∑ r ∈ Finset.Icc (K + 1) L, (x + y * A' + r).divisors.card * b ^ (L - r) := by
          rw [Finset.mul_sum]
      _ ≤ W * ((b ^ (L - K)
            * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + A' * A' + L)), (A' / d + 1))) / A') :=
          Nat.mul_le_mul_left W hWy
  -- far-tail positivity from the forward orbit of a positive weight value
  have htail : ∃ t : ℕ, 0 < weightedCoeff w (x + y * A' + L + 1 + t) := by
    obtain ⟨a₀, ha₀pos, ha₀w⟩ := hpos
    refine ⟨a₀ + (x + y * A' + L + 2) * m - (x + y * A' + L + 1), ?_⟩
    have hstep : (x + y * A' + L + 2) * 1 ≤ (x + y * A' + L + 2) * m :=
      Nat.mul_le_mul_left _ hm
    have heq : x + y * A' + L + 1
        + (a₀ + (x + y * A' + L + 2) * m - (x + y * A' + L + 1))
        = a₀ + (x + y * A' + L + 2) * m := by omega
    rw [heq]
    have haw : w (a₀ + (x + y * A' + L + 2) * m) = w a₀ :=
      eventually_periodic_add_mul w m 0 (fun k _ => hper k) (x + y * A' + L + 2) a₀
        (Nat.zero_le a₀)
    have hne : a₀ + (x + y * A' + L + 2) * m ≠ 0 := by omega
    have h1 := weight_le_weightedCoeff w (a₀ + (x + y * A' + L + 2) * m) hne
    omega
  refine ⟨x + y * A', K, L,
    W * ((b ^ (L - K)
      * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + A' * A' + L)), (A' / d + 1))) / A'),
    hKL, hfirst, hmiddle, htail, ?_⟩
  set S : ℕ := Nat.sqrt (x + A' * A' + L) with hSdef
  have hSle : S ≤ A' + L + 1 := by
    have h1 : x + A' * A' + L ≤ (A' + L + 1) * (A' + L + 1) := by
      have hexp : (A' + L + 1) * (A' + L + 1)
          = A' * A' + (2 * (A' * (L + 1)) + (L + 1) * (L + 1)) := by ring
      have h2 : A' ≤ A' * (L + 1) := Nat.le_mul_of_pos_right A' (by omega)
      have h3 : L + 1 ≤ (L + 1) * (L + 1) :=
        Nat.le_mul_of_pos_right (L + 1) (by omega)
      omega
    have h4 : Nat.sqrt (x + A' * A' + L) ≤ Nat.sqrt ((A' + L + 1) * (A' + L + 1)) :=
      Nat.sqrt_le_sqrt h1
    rw [Nat.sqrt_eq] at h4
    rw [hSdef]
    exact h4
  have hSpow : S ≤ 2 ^ (E + κ + 2) := by
    have h1 : (2 : ℕ) ^ (E + κ + 2) = 2 ^ E * 2 ^ (κ + 2) := pow_add 2 E (κ + 2)
    have h2 : (4 : ℕ) ≤ 2 ^ (κ + 2) := by
      have h2a : (2 : ℕ) ^ (κ + 2) = 2 ^ κ * 4 := by rw [pow_add]; norm_num
      have h2b : (1 : ℕ) ≤ 2 ^ κ := Nat.one_le_two_pow
      omega
    have h5 : 2 ^ E * 4 ≤ 2 ^ E * 2 ^ (κ + 2) := Nat.mul_le_mul_left _ h2
    omega
  have hHle : (∑ d ∈ Finset.Icc 1 S, (A' / d + 1)) ≤ A' * (E + κ + 5) := by
    have h1 := harmonic_div_sum_le S A' (E + κ + 2) hSpow
    have h2 : A' * (E + κ + 2 + 1) + 2 * A' = A' * (E + κ + 5) := by ring
    omega
  have hCle : (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A'
      ≤ 2 * b ^ (L - K) * (E + κ + 5) := by
    have h1 : b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))
        ≤ b ^ (L - K) * (2 * (A' * (E + κ + 5))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hHle)
    have h2 : b ^ (L - K) * (2 * (A' * (E + κ + 5)))
        = A' * (2 * b ^ (L - K) * (E + κ + 5)) := by ring
    calc (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A'
        ≤ (A' * (2 * b ^ (L - K) * (E + κ + 5))) / A' := by
          apply Nat.div_le_div_right
          omega
      _ = 2 * b ^ (L - K) * (E + κ + 5) := Nat.mul_div_cancel_left _ hApos
  have hNle : x + y * A' + L + 2 ≤ A' * A' + L + 2 := by
    have h1 : y * A' ≤ (A' - 1) * A' := Nat.mul_le_mul_right A' (by omega)
    have h3 : (A' - 1) * A' = A' * A' - A' := Nat.sub_one_mul A' A'
    have h4 : A' ≤ A' * A' := Nat.le_mul_of_pos_left A' hApos
    omega
  have hhalf1 : 2 * (q' * (2 * b ^ (L - K) * (E + κ + 5))) ≤ b ^ L := by
    have h1 : 2 * (q' * (2 * b ^ (L - K) * (E + κ + 5)))
        = (4 * q' * (E + κ + 5)) * b ^ (L - K) := by ring
    have h2 : (4 * q' * (E + κ + 5)) * b ^ (L - K) ≤ b ^ K * b ^ (L - K) :=
      Nat.mul_le_mul_right _ hparamA
    have h3 : b ^ K * b ^ (L - K) = b ^ (K + (L - K)) := (pow_add b K (L - K)).symm
    have h4 : K + (L - K) = L := Nat.add_sub_cancel' hKL
    rw [h1]
    rw [h3, h4] at h2
    exact h2
  have hhalf2 : 2 * (q' * (A' * A' + L + 2)) < b ^ L := by
    have hA2 : A' * A' ≤ 2 ^ (2 * E) := by
      have h1 : A' * A' ≤ 2 ^ E * 2 ^ E := Nat.mul_le_mul hA2E hA2E
      have h2 : (2 : ℕ) ^ E * 2 ^ E = 2 ^ (2 * E) := by
        rw [← pow_add]; congr 1; ring
      omega
    have hsum : A' * A' + L + 2 ≤ 2 ^ (2 * E + κ + 2) := by
      have hex : (2 : ℕ) ^ (2 * E + κ + 2) = 2 ^ (2 * E) * 2 ^ κ * 4 := by
        rw [pow_add, pow_add]; norm_num
      have hac1 : (2 : ℕ) ^ (2 * E) ≤ 2 ^ (2 * E) * 2 ^ κ :=
        Nat.le_mul_of_pos_right _ (by positivity)
      have hac2 : (2 : ℕ) ^ κ ≤ 2 ^ (2 * E) * 2 ^ κ :=
        Nat.le_mul_of_pos_left _ (by positivity)
      omega
    have h2q : 2 * q' ≤ 2 ^ (q' + 1) := by
      have h1 : q' < 2 ^ q' := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (q' + 1) = 2 ^ q' * 2 := pow_succ 2 q'
      omega
    have hmul : 2 * (q' * (A' * A' + L + 2)) ≤ 2 ^ (q' + 1) * 2 ^ (2 * E + κ + 2) := by
      have h1 : 2 * (q' * (A' * A' + L + 2)) = (2 * q') * (A' * A' + L + 2) := by ring
      rw [h1]
      exact Nat.mul_le_mul h2q hsum
    have hexp : (2 : ℕ) ^ (q' + 1) * 2 ^ (2 * E + κ + 2) = 2 ^ (2 * E + κ + q' + 3) := by
      rw [← pow_add]; congr 1; ring
    have hlt : (2 : ℕ) ^ (2 * E + κ + q' + 3) * 2 ≤ 2 ^ L := by
      have h1 : (2 : ℕ) ^ (2 * E + κ + q' + 3) * 2 = 2 ^ (2 * E + κ + q' + 4) :=
        (pow_succ 2 _).symm
      rw [h1]
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    have ht1 : (1 : ℕ) ≤ 2 ^ (2 * E + κ + q' + 3) := Nat.one_le_two_pow
    have h2L : (2 : ℕ) ^ L ≤ b ^ L := Nat.pow_le_pow_left hb L
    omega
  have hqC : q' * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A')
      ≤ q' * (2 * b ^ (L - K) * (E + κ + 5)) := Nat.mul_le_mul_left q' hCle
  have hqN : q' * (x + y * A' + L + 2) ≤ q' * (A' * A' + L + 2) :=
    Nat.mul_le_mul_left q' hNle
  have hfin : q * (W * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A')
        + W * (x + y * A' + L + 2))
      = q' * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A')
        + q' * (x + y * A' + L + 2) := by
    rw [hq'def]
    ring
  omega

/-! ## Weighted-coefficient calculus: the wave-11 theorems -/

/-- **Periodic Nat-weight irrationality (wave-11 core).**  For every base
`b ≥ 2` and every `m`-periodic weight `w : ℕ → ℕ` (`m ≥ 1`) with a
positive value at a positive index, `∑_a w(a)/(b^a - 1)` is irrational.
At indicator weights this recovers the wave-10 periodic support theorem;
at `w ≡ 1` the full-support theorem. -/
theorem irrational_weightedErdosSeries_periodic
    (b m : ℕ) (w : ℕ → ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hpos : ∃ a : ℕ, 0 < a ∧ 0 < w a) :
    Irrational (weightedErdosSeries b w) := by
  set W : ℕ := (Finset.range m).sup w with hWdef
  have hbound : ∀ x : ℕ, w x ≤ W := by
    intro x
    have h := eventually_periodic_weight_bound w m 0 hm (fun k _ => hper k) x
    simpa [hWdef] using h
  have hWpos : 0 < W := by
    obtain ⟨a, ha0, haw⟩ := hpos
    have h1 := hbound a
    omega
  rw [weightedErdosSeries_eq_tsum_weightedCoeff b W w hb hWpos hbound]
  exact irrational_coeff_series_of_weighted_coeff_block_certificates_linear b W
    (weightedCoeff w) hb (fun n => weightedCoeff_le_mul_self w W n hbound)
    (exists_weighted_coeff_certificates_weightedCoeff_periodic b m W w hb hm hper
      hbound hWpos hpos)

/-- **Eventually periodic Nat-weight irrationality (wave-11 frontier
theorem, Nat form).**  For every base `b ≥ 2`: a weight that is
`m`-periodic from some threshold `N₀` on, with a positive value at a
positive index inside the periodic region, has an irrational weighted
series.  The purely periodic shift `w_pure(n) = w(n + m·N₀)` agrees with
`w` above the threshold, so the two series differ by the rational finite
prefix difference. -/
theorem irrational_weightedErdosSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (w : ℕ → ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → w (n + m) = w n)
    (hpos : ∃ a : ℕ, N₀ ≤ a ∧ 0 < a ∧ 0 < w a) :
    Irrational (weightedErdosSeries b w) := by
  classical
  have hstep : ∀ (k n : ℕ), N₀ ≤ n → w (n + k * m) = w n :=
    eventually_periodic_add_mul w m N₀ hper
  set wpure : ℕ → ℕ := fun n => w (n + m * N₀) with hwpuredef
  have hmN₀ : N₀ ≤ m * N₀ := Nat.le_mul_of_pos_left N₀ hm
  have hpureper : ∀ n : ℕ, wpure (n + m) = wpure n := by
    intro n
    show w (n + m + m * N₀) = w (n + m * N₀)
    rw [show n + m + m * N₀ = (n + m * N₀) + m from by ring]
    exact hper (n + m * N₀) (by omega)
  have hagree : ∀ n : ℕ, N₀ ≤ n → wpure n = w n := by
    intro n hn
    show w (n + m * N₀) = w n
    rw [show n + m * N₀ = n + N₀ * m from by ring]
    exact hstep N₀ n hn
  have hpurepos : ∃ a : ℕ, 0 < a ∧ 0 < wpure a := by
    obtain ⟨a, haN, ha0, haw⟩ := hpos
    refine ⟨a, ha0, ?_⟩
    rw [hagree a haN]
    exact haw
  have hpureirr : Irrational (weightedErdosSeries b wpure) :=
    irrational_weightedErdosSeries_periodic b m wpure hb hm hpureper hpurepos
  -- both term families are summable
  set W : ℕ := (Finset.range (N₀ + m)).sup w with hWdef
  have hbound : ∀ x : ℕ, w x ≤ W := by
    intro x
    have h := eventually_periodic_weight_bound w m N₀ hm hper x
    simpa [hWdef] using h
  have hsum_w : Summable (fun a : ℕ => ((w a : ℝ)) / ((b : ℝ) ^ a - 1)) :=
    summable_weightedErdos_term b W w hb hbound
  have hboundp : ∀ x : ℕ, wpure x ≤ W := fun x => hbound (x + m * N₀)
  have hsum_p : Summable (fun a : ℕ => ((wpure a : ℝ)) / ((b : ℝ) ^ a - 1)) :=
    summable_weightedErdos_term b W wpure hb hboundp
  -- split both series at the threshold; the tails agree
  have hsplit_w := Summable.sum_add_tsum_nat_add N₀ hsum_w
  have hsplit_p := Summable.sum_add_tsum_nat_add N₀ hsum_p
  have htail_eq : (∑' t : ℕ, ((w (t + N₀) : ℝ)) / ((b : ℝ) ^ (t + N₀) - 1))
      = ∑' t : ℕ, ((wpure (t + N₀) : ℝ)) / ((b : ℝ) ^ (t + N₀) - 1) := by
    refine tsum_congr fun t => ?_
    rw [hagree (t + N₀) (by omega)]
  -- finite prefixes are rational
  have hprefix : ∀ v : ℕ → ℕ,
      (∑ a ∈ Finset.range N₀, ((v a : ℝ)) / ((b : ℝ) ^ a - 1))
        = (((∑ a ∈ Finset.range N₀, ((v a : ℚ)) / ((b : ℚ) ^ a - 1)) : ℚ) : ℝ) := by
    intro v
    rw [Rat.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    norm_cast
  set qd : ℚ := (∑ a ∈ Finset.range N₀, ((w a : ℚ)) / ((b : ℚ) ^ a - 1))
      - (∑ a ∈ Finset.range N₀, ((wpure a : ℚ)) / ((b : ℚ) ^ a - 1)) with hqddef
  have hrel : weightedErdosSeries b w = weightedErdosSeries b wpure + (qd : ℝ) := by
    have h1 : (∑ a ∈ Finset.range N₀, ((w a : ℝ)) / ((b : ℝ) ^ a - 1))
        + (∑' t : ℕ, ((w (t + N₀) : ℝ)) / ((b : ℝ) ^ (t + N₀) - 1))
        = weightedErdosSeries b w := hsplit_w
    have h2 : (∑ a ∈ Finset.range N₀, ((wpure a : ℝ)) / ((b : ℝ) ^ a - 1))
        + (∑' t : ℕ, ((wpure (t + N₀) : ℝ)) / ((b : ℝ) ^ (t + N₀) - 1))
        = weightedErdosSeries b wpure := hsplit_p
    have h3 := hprefix w
    have h4 := hprefix wpure
    have h5 : (qd : ℝ)
        = (((∑ a ∈ Finset.range N₀, ((w a : ℚ)) / ((b : ℚ) ^ a - 1)) : ℚ) : ℝ)
          - (((∑ a ∈ Finset.range N₀, ((wpure a : ℚ)) / ((b : ℚ) ^ a - 1)) : ℚ) : ℝ) := by
      rw [hqddef]
      exact Rat.cast_sub _ _
    linarith [h1, h2, h3, h4, h5, htail_eq]
  rw [hrel]
  rintro ⟨r, hr⟩
  refine hpureirr ⟨r - qd, ?_⟩
  have hcast : ((r - qd : ℚ) : ℝ) = (r : ℝ) - (qd : ℝ) := Rat.cast_sub _ _
  rw [hcast]
  linarith [hr]

/-- **Nonnegative rational periodic Lambert coefficients (wave-11 frontier
theorem, ℚ form).**  For every base `b ≥ 2`: an eventually periodic
NONNEGATIVE rational coefficient sequence `γ` with a positive value at a
positive index inside its periodic region has
`∑_a γ(a)/(b^a - 1)` irrational.  One common denominator `D` over the
prefix-plus-period window clears `γ` to an eventually periodic Nat weight;
the series scales by `1/D`, and irrationality survives nonzero rational
scaling.  Mixed-sign rational periodic coefficients (the full Luca–Tachiya
statement) are NOT claimed. -/
theorem irrational_ratWeightSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (γ : ℕ → ℚ) (hb : 2 ≤ b) (hm : 0 < m)
    (hγ0 : ∀ n : ℕ, 0 ≤ γ n)
    (hper : ∀ n : ℕ, N₀ ≤ n → γ (n + m) = γ n)
    (hpos : ∃ a : ℕ, N₀ ≤ a ∧ 0 < a ∧ 0 < γ a) :
    Irrational (∑' a : ℕ, ((γ a : ℝ)) / ((b : ℝ) ^ a - 1)) := by
  classical
  set D : ℕ := ∏ r ∈ Finset.range (N₀ + m), (γ r).den with hDdef
  have hD0 : 0 < D := by
    rw [hDdef]
    exact Finset.prod_pos fun r _ => Nat.pos_of_ne_zero (γ r).den_nz
  have hdvdD : ∀ a : ℕ, (γ a).den ∣ D := by
    intro a
    obtain ⟨r, hr, har⟩ := eventually_periodic_fold γ m N₀ hm hper a
    rw [har, hDdef]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hr)
  set w : ℕ → ℕ := fun a => (D / (γ a).den) * (γ a).num.toNat with hwdef
  -- the cleared weight represents D·γ exactly
  have hwq : ∀ a : ℕ, ((w a : ℕ) : ℚ) = (D : ℚ) * γ a := by
    intro a
    obtain ⟨k, hk⟩ := hdvdD a
    have hnum0 : 0 ≤ (γ a).num := Rat.num_nonneg.mpr (hγ0 a)
    have hdiv : D / (γ a).den = k := by
      rw [hk]
      exact Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero (γ a).den_nz)
    have hden0 : ((γ a).den : ℚ) ≠ 0 := by
      exact_mod_cast (γ a).den_nz
    have hkey : ((γ a).den : ℚ) * γ a = ((γ a).num : ℚ) := by
      have h := Rat.num_div_den (γ a)
      rw [div_eq_iff hden0] at h
      rw [mul_comm] at h
      exact h.symm
    have hnumcast : (((γ a).num.toNat : ℕ) : ℚ) = ((γ a).num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum0
    calc ((w a : ℕ) : ℚ)
        = ((D / (γ a).den : ℕ) : ℚ) * (((γ a).num.toNat : ℕ) : ℚ) := by
          show (((D / (γ a).den) * (γ a).num.toNat : ℕ) : ℚ) = _
          push_cast
          ring
      _ = (k : ℚ) * ((γ a).num : ℚ) := by rw [hdiv, hnumcast]
      _ = (k : ℚ) * (((γ a).den : ℚ) * γ a) := by rw [hkey]
      _ = (D : ℚ) * γ a := by
          rw [hk]
          push_cast
          ring
  -- the cleared weight is eventually periodic with a positive tail value
  have hwper : ∀ n : ℕ, N₀ ≤ n → w (n + m) = w n := by
    intro n hn
    show (D / (γ (n + m)).den) * (γ (n + m)).num.toNat
      = (D / (γ n).den) * (γ n).num.toNat
    rw [hper n hn]
  have hwpos : ∃ a : ℕ, N₀ ≤ a ∧ 0 < a ∧ 0 < w a := by
    obtain ⟨a, haN, ha0, haγ⟩ := hpos
    refine ⟨a, haN, ha0, ?_⟩
    show 0 < (D / (γ a).den) * (γ a).num.toNat
    have h1 : 0 < (γ a).num := Rat.num_pos.mpr haγ
    have h2 : 0 < (γ a).num.toNat := by omega
    have h3 : 0 < D / (γ a).den :=
      Nat.div_pos (Nat.le_of_dvd hD0 (hdvdD a)) (Nat.pos_of_ne_zero (γ a).den_nz)
    exact Nat.mul_pos h3 h2
  have hwirr : Irrational (weightedErdosSeries b w) :=
    irrational_weightedErdosSeries_eventuallyPeriodic b m N₀ w hb hm hwper hwpos
  -- the rational series is the weighted series scaled by 1/D
  have hD0' : ((D : ℝ)) ≠ 0 := by
    have h : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD0
    linarith
  have hterm : ∀ a : ℕ, ((γ a : ℝ)) / ((b : ℝ) ^ a - 1)
      = ((1 : ℝ) / (D : ℝ)) * (((w a : ℝ)) / ((b : ℝ) ^ a - 1)) := by
    intro a
    have hcast : ((w a : ℝ)) = (D : ℝ) * ((γ a : ℝ)) := by
      have h2 : (((w a : ℕ) : ℚ) : ℝ) = (((D : ℚ) * γ a : ℚ) : ℝ) := by
        rw [hwq a]
      push_cast at h2
      exact h2
    rw [hcast, ← mul_div_assoc]
    congr 1
    rw [← mul_assoc, one_div_mul_cancel hD0', one_mul]
  have hrel : (∑' a : ℕ, ((γ a : ℝ)) / ((b : ℝ) ^ a - 1))
      = ((1 : ℝ) / (D : ℝ)) * weightedErdosSeries b w := by
    unfold weightedErdosSeries
    rw [← tsum_mul_left]
    exact tsum_congr hterm
  rw [hrel]
  rintro ⟨r, hr⟩
  refine hwirr ⟨(D : ℚ) * r, ?_⟩
  have hval : (((D : ℚ) * r : ℚ) : ℝ) = (D : ℝ) * (r : ℝ) := by norm_cast
  rw [hval, hr, ← mul_assoc, mul_one_div_cancel hD0', one_mul]

/-- **Showcase instance**: for every base `b ≥ 2` and every modulus
`m ≥ 2`, the series `∑_a (a mod m)/(b^a - 1)` is irrational — a
multiplicity-weighted periodic Lambert series no 0/1 support theorem can
express. -/
theorem irrational_weightedErdosSeries_mod (b m : ℕ) (hb : 2 ≤ b) (hm : 2 ≤ m) :
    Irrational (∑' a : ℕ, ((a % m : ℕ) : ℝ) / ((b : ℝ) ^ a - 1)) := by
  have h := irrational_weightedErdosSeries_periodic b m (fun a => a % m) hb
    (by omega) (fun n => Nat.add_mod_right n m)
    ⟨1, by omega, by
      show 0 < 1 % m
      rw [Nat.mod_eq_of_lt (by omega : 1 < m)]
      exact Nat.one_pos⟩
  simpa [weightedErdosSeries] using h

/-! ## Signed-coefficient calculus (wave 12): the ℤ-weight engine and the
protected-residue socket

Wave 11 closed nonnegative rational eventually-periodic Lambert
coefficients through the layer-cake orbit sieve and the one-sided
near-integer engine.  Mixed signs destroy exactly one ingredient: the
positive far tail that makes the fractional remainder nonzero.  This
section builds the signed replacement in four unconditional layers and
one explicitly conditional layer.

1. **Signed coefficient algebra.**  `intWeightedCoeff w n = ∑_{d∣n} w d`
   for `w : ℕ → ℤ`, with the `toNat`-part decomposition
   `intWeightedCoeff w = weightedCoeff w⁺ - weightedCoeff w⁻` and the
   `natAbs` growth envelopes.  The decomposition is ALGEBRA ONLY: no
   irrationality statement is ever inferred from the two nonnegative
   parts separately — differences of irrationals can be rational.

2. **Signed orbit layer.**  Complete Euler cycles never needed
   positivity: `b^|P| ∣ intWeightedCoeff w n` at exact valuations
   `b·φ(m) - 1` follows from the Nat theorem on both parts.  The landed
   one-extra-orbit defect is already an ARBITRARY-MODULUS statement (its
   `b` is a bare multiplier), so exact valuation `M·φ(m)` pins
   `intWeightedCoeff w (p^(M·φ(m))·R) ≡ intWeightedCoeff w R [ZMOD M]`
   for every modulus `M` — at `M = b^s` this is an arbitrary-precision
   protected residue, the bridge from "some digit is nonzero" to "a small
   nonzero fractional residue survives".

3. **Seed calculus.**  A minimal-index argument shows base-primitive
   signed weights have divisor coefficients that are nonzero (indeed
   non-divisible by any target modulus) at some positive index, and the
   extra-orbit transport carries that seed residue to infinitely many
   exact-valuation witnesses `p^(M·φ(m))·R`.  Non-cancellation is
   therefore ACHIEVABLE in isolation at every modulus.

4. **Signed certificate consumer.**  A protected-block certificate —
   first-block divisibility except at one protected slot `s`, a known
   nonzero residue `V` mod `b^s` at the protected slot, an absolute
   middle bound, and two inequalities (the protected term dominates the
   noise; everything is below `1/q`) — yields a two-sided near-integer
   witness.  Certificates for every precision give irrationality of the
   signed coefficient series and of the signed weighted Lambert series
   `intWeightedErdosSeries`.

5. **The conditional boundary.**  What is NOT claimed: that periodic
   signed weights possess protected-block certificates.  The frame
   machinery supplies the divisible slots and the middle average exactly
   as in waves 10–11, and the extra-orbit socket pins the protected slot
   to its cofactor coefficient mod `b^s` — but the cofactor `R` of a CRT
   progression slot is arithmetically uncontrolled, so `V ≠ 0` is an open
   supply obligation ("cofactor non-cancellation").  The two live
   branches are (a) a selection argument over the frame progression with
   arbitrary primes, or (b) a bounded prime-in-arithmetic-progression
   supply in the style of Luca–Tachiya's proof; qualitative Dirichlet is
   NOT enough, because the certificate arithmetic needs the selected slot
   inside a bounded window.  The unconditional mixed-sign rational
   periodic coefficient theorem (full Luca–Tachiya) remains a
   NON-CLAIM. -/

/-- **The signed weighted divisor coefficient** `∑_{d ∣ n} w d` for an
integer weight `w : ℕ → ℤ` — the Dirichlet incidence `w * 1` with signs.
At a Nat weight (cast) this is `weightedCoeff`. -/
def intWeightedCoeff (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, w d

/-- Cast compatibility: the signed coefficient of a cast Nat weight is
the cast Nat coefficient. -/
theorem intWeightedCoeff_natCast (w : ℕ → ℕ) (n : ℕ) :
    intWeightedCoeff (fun d => ((w d : ℤ))) n = ((weightedCoeff w n : ℕ) : ℤ) := by
  unfold intWeightedCoeff weightedCoeff
  push_cast
  rfl

/-- **`toNat`-part decomposition**: every signed coefficient is the
difference of the two Nat coefficients of the positive and negative
parts.  This is pure algebra — the signed irrationality engine never
subtracts two IRRATIONALITY statements, only two SUMS. -/
theorem intWeightedCoeff_eq_weightedCoeff_sub (w : ℕ → ℤ) (n : ℕ) :
    intWeightedCoeff w n
      = ((weightedCoeff (fun d => (w d).toNat) n : ℕ) : ℤ)
        - ((weightedCoeff (fun d => (-(w d)).toNat) n : ℕ) : ℤ) := by
  unfold intWeightedCoeff weightedCoeff
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  omega

/-- Triangle inequality for `natAbs` over a finite sum. -/
theorem natAbs_sum_le_sum_natAbs {ι : Type*} (t : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ t, f i).natAbs ≤ ∑ i ∈ t, (f i).natAbs := by
  have h : ((∑ i ∈ t, f i).natAbs : ℤ) ≤ ((∑ i ∈ t, (f i).natAbs : ℕ) : ℤ) := by
    rw [← Int.abs_eq_natAbs]
    calc |∑ i ∈ t, f i|
        ≤ ∑ i ∈ t, |f i| := Finset.abs_sum_le_sum_abs _ _
      _ = ((∑ i ∈ t, (f i).natAbs : ℕ) : ℤ) := by
          push_cast
          exact Finset.sum_congr rfl fun i _ => rfl
  exact_mod_cast h

/-- Bounded signed weights give the `W·τ` absolute growth envelope. -/
theorem natAbs_intWeightedCoeff_le_mul_card_divisors (w : ℕ → ℤ) (W n : ℕ)
    (hW : ∀ d : ℕ, (w d).natAbs ≤ W) :
    (intWeightedCoeff w n).natAbs ≤ W * n.divisors.card := by
  unfold intWeightedCoeff
  calc (∑ d ∈ n.divisors, w d).natAbs
      ≤ ∑ d ∈ n.divisors, (w d).natAbs := natAbs_sum_le_sum_natAbs _ _
    _ ≤ ∑ _d ∈ n.divisors, W := Finset.sum_le_sum fun d _ => hW d
    _ = n.divisors.card * W := by rw [Finset.sum_const, smul_eq_mul]
    _ = W * n.divisors.card := Nat.mul_comm _ _

/-- Linear absolute growth envelope for the signed coefficient:
`|intWeightedCoeff w n| ≤ W·n` — the hypothesis shape of the signed
certificate engine. -/
theorem natAbs_intWeightedCoeff_le_mul_self (w : ℕ → ℤ) (W n : ℕ)
    (hW : ∀ d : ℕ, (w d).natAbs ≤ W) :
    (intWeightedCoeff w n).natAbs ≤ W * n :=
  le_trans (natAbs_intWeightedCoeff_le_mul_card_divisors w W n hW)
    (Nat.mul_le_mul_left W (Nat.card_divisors_le_self n))

/-! ## Signed-coefficient calculus: the signed periodic orbit layer -/

/-- **Signed periodic orbit divisibility.**  Complete Euler cycles never
used positivity: an `m`-periodic SIGNED weight, together with `|P|`
primes above `m` at exact valuation `b·φ(m) - 1`, still forces
`b^|P| ∣ intWeightedCoeff w n` — apply the layered Nat orbit theorem to
both `toNat` parts and subtract. -/
theorem bpow_dvd_intWeightedCoeff_of_periodic_exact_block
    (b m n : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m) (hn : n ≠ 0)
    (hper : ∀ x : ℕ, w (x + m) = w x)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hgt : ∀ p ∈ P, m < p)
    (hexact : ∀ p ∈ P, n.factorization p = b * m.totient - 1) :
    ((b : ℤ)) ^ P.card ∣ intWeightedCoeff w n := by
  have hpos : b ^ P.card ∣ weightedCoeff (fun d => (w d).toNat) n :=
    bpow_dvd_weightedCoeff_of_periodic_exact_block b m n _ hb hm hn
      (fun x => by show (w (x + m)).toNat = (w x).toNat; rw [hper x])
      P hprime hgt hexact
  have hneg : b ^ P.card ∣ weightedCoeff (fun d => (-(w d)).toNat) n :=
    bpow_dvd_weightedCoeff_of_periodic_exact_block b m n _ hb hm hn
      (fun x => by show (-(w (x + m))).toNat = (-(w x)).toNat; rw [hper x])
      P hprime hgt hexact
  rw [intWeightedCoeff_eq_weightedCoeff_sub]
  have hcast : ((b : ℤ)) ^ P.card = (((b ^ P.card : ℕ)) : ℤ) := by push_cast; rfl
  rw [hcast]
  exact dvd_sub (Int.natCast_dvd_natCast.mpr hpos) (Int.natCast_dvd_natCast.mpr hneg)

/-- Nat congruences cast to integer congruences. -/
theorem int_modEq_of_nat_modEq {n a b : ℕ} (h : a ≡ b [MOD n]) :
    (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)] := by
  show (a : ℤ) % (n : ℤ) = (b : ℤ) % (n : ℤ)
  rw [← Int.natCast_mod, ← Int.natCast_mod]
  exact_mod_cast h

/-- **Arbitrary-modulus one-extra-orbit defect for signed weights.**  The
landed predicate-level defect is already modulus-generic (its `b` is a
bare cycle multiplier), so for every modulus `M`, an `m`-periodic signed
weight, and exact valuation `M·φ(m)` at a prime `p ∤ m`, the signed
coefficient is pinned mod `M` to its cofactor value:
`intWeightedCoeff w (p^(M·φ(m))·R) ≡ intWeightedCoeff w R [ZMOD M]`.
Complete cycles vanish mod `M`; the single extra slot survives.  This is
the protected-residue transport of the signed lane. -/
theorem intWeightedCoeff_modEq_of_periodic_extra_orbit
    (M m p R : ℕ) (w : ℕ → ℤ) (hm : 0 < m) (hp : Nat.Prime p) (hR : R ≠ 0)
    (hpR : ¬ p ∣ R) (hpm : ¬ p ∣ m)
    (hper : ∀ x : ℕ, w (x + m) = w x) :
    intWeightedCoeff w (p ^ (M * m.totient) * R)
      ≡ intWeightedCoeff w R [ZMOD (M : ℤ)] := by
  have hpos := weightedCoeff_modEq_of_periodic_extra_orbit M m p R
    (fun d => (w d).toNat) hm hp hR hpR hpm
    (fun x => by show (w (x + m)).toNat = (w x).toNat; rw [hper x])
  have hneg := weightedCoeff_modEq_of_periodic_extra_orbit M m p R
    (fun d => (-(w d)).toNat) hm hp hR hpR hpm
    (fun x => by show (-(w (x + m))).toNat = (-(w x)).toNat; rw [hper x])
  rw [intWeightedCoeff_eq_weightedCoeff_sub, intWeightedCoeff_eq_weightedCoeff_sub]
  exact (int_modEq_of_nat_modEq hpos).sub (int_modEq_of_nat_modEq hneg)

/-- **Arbitrary-precision protected residue** — the `M = b^s` instance:
exact valuation `b^s·φ(m)` pins the signed coefficient mod `b^s` to its
cofactor value.  A mod-`b` residue proves one nonzero digit; a mod-`b^s`
residue is a small nonzero fractional part after division by `b^s` — the
quantity a signed near-integer certificate protects. -/
theorem intWeightedCoeff_modEq_of_periodic_extra_orbit_bpow
    (b s m p R : ℕ) (w : ℕ → ℤ) (hm : 0 < m) (hp : Nat.Prime p) (hR : R ≠ 0)
    (hpR : ¬ p ∣ R) (hpm : ¬ p ∣ m)
    (hper : ∀ x : ℕ, w (x + m) = w x) :
    intWeightedCoeff w (p ^ (b ^ s * m.totient) * R)
      ≡ intWeightedCoeff w R [ZMOD ((b : ℤ) ^ s)] := by
  have h := intWeightedCoeff_modEq_of_periodic_extra_orbit (b ^ s) m p R w
    hm hp hR hpR hpm hper
  have hcast : (((b ^ s : ℕ)) : ℤ) = (b : ℤ) ^ s := by push_cast; rfl
  rwa [hcast] at h

/-! ## Signed-coefficient calculus: the seed calculus

Non-cancellation seeds: a signed weight that is not everywhere divisible
by the target modulus has a divisor coefficient that is not divisible by
it either — at the MINIMAL such index, because all proper divisors sit
below the minimum.  The extra-orbit transport then carries the seed
residue to exact-valuation witnesses at every modulus.  These lemmas show
the protected residue exists in isolation; steering the CERTIFICATE FRAME
onto such a witness is exactly the open supply obligation. -/

/-- At an index all of whose smaller positive indices carry zero weight,
the signed coefficient collapses to the weight itself. -/
theorem intWeightedCoeff_eq_weight_of_zero_below (w : ℕ → ℤ) (a : ℕ) (ha : 0 < a)
    (hzero : ∀ d : ℕ, 0 < d → d < a → w d = 0) :
    intWeightedCoeff w a = w a := by
  unfold intWeightedCoeff
  rw [← Nat.insert_self_properDivisors (show a ≠ 0 by omega),
    Finset.sum_insert Nat.self_notMem_properDivisors]
  have hzero' : ∑ d ∈ a.properDivisors, w d = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    rcases Nat.mem_properDivisors.mp hd with ⟨hdvd, hlt⟩
    exact hzero d (Nat.pos_of_dvd_of_pos hdvd ha) hlt
  rw [hzero', add_zero]

/-- **Base-primitive non-cancellation seed.**  If some positive index has
weight not divisible by `M`, then some positive index has signed divisor
COEFFICIENT not divisible by `M`: at the minimal such index, all proper
divisors contribute multiples of `M`.  Möbius-free. -/
theorem exists_pos_intWeightedCoeff_not_dvd (M : ℕ) (w : ℕ → ℤ)
    (hex : ∃ a : ℕ, 0 < a ∧ ¬ ((M : ℤ)) ∣ w a) :
    ∃ R : ℕ, 0 < R ∧ ¬ ((M : ℤ)) ∣ intWeightedCoeff w R := by
  classical
  have hexP : ∃ a : ℕ, 0 < a ∧ ¬ ((M : ℤ)) ∣ w a := hex
  obtain ⟨hapos, hand⟩ := Nat.find_spec hexP
  refine ⟨Nat.find hexP, hapos, ?_⟩
  intro hdvd
  have hbelow : ∀ d ∈ (Nat.find hexP).properDivisors, ((M : ℤ)) ∣ w d := by
    intro d hd
    rcases Nat.mem_properDivisors.mp hd with ⟨hdvd', hlt⟩
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd' hapos
    by_contra hnd
    exact Nat.find_min hexP hlt ⟨hd0, hnd⟩
  have hsum : ((M : ℤ)) ∣ ∑ d ∈ (Nat.find hexP).properDivisors, w d :=
    Finset.dvd_sum hbelow
  have hcoeff : intWeightedCoeff w (Nat.find hexP)
      = w (Nat.find hexP) + ∑ d ∈ (Nat.find hexP).properDivisors, w d := by
    unfold intWeightedCoeff
    rw [← Nat.insert_self_properDivisors (show Nat.find hexP ≠ 0 by omega),
      Finset.sum_insert Nat.self_notMem_properDivisors]
  have hw : ((M : ℤ)) ∣ w (Nat.find hexP) := by
    have h1 : w (Nat.find hexP)
        = intWeightedCoeff w (Nat.find hexP)
          - ∑ d ∈ (Nat.find hexP).properDivisors, w d := by
      rw [hcoeff]; ring
    rw [h1]
    exact dvd_sub hdvd hsum
  exact hand hw

/-- **Nonzero seed** — the `M = 0` instance: a not-identically-zero
signed weight (at positive indices) has a nonzero signed coefficient at
some positive index. -/
theorem exists_pos_intWeightedCoeff_ne_zero (w : ℕ → ℤ)
    (hex : ∃ a : ℕ, 0 < a ∧ w a ≠ 0) :
    ∃ R : ℕ, 0 < R ∧ intWeightedCoeff w R ≠ 0 := by
  obtain ⟨a, ha, hwa⟩ := hex
  obtain ⟨R, hR, hnd⟩ := exists_pos_intWeightedCoeff_not_dvd 0 w
    ⟨a, ha, by simpa using hwa⟩
  exact ⟨R, hR, by simpa using hnd⟩

/-- **Protected-residue witnesses exist at every modulus.**  For every
modulus `M` and `m`-periodic signed weight with some weight value not
divisible by `M`, there are a prime `p` and a cofactor `R` with
`intWeightedCoeff w (p^(M·φ(m))·R) ≢ 0 [ZMOD M]`: transport the seed
residue through one extra orbit.  Non-cancellation is achievable in
isolation; the open problem is achieving it INSIDE a certificate frame
progression, where the cofactor is CRT-uncontrolled. -/
theorem exists_intWeightedCoeff_extra_orbit_witness_not_dvd
    (M m : ℕ) (w : ℕ → ℤ) (hm : 0 < m)
    (hper : ∀ x : ℕ, w (x + m) = w x)
    (hex : ∃ a : ℕ, 0 < a ∧ ¬ ((M : ℤ)) ∣ w a) :
    ∃ p R : ℕ, Nat.Prime p ∧ 0 < R ∧ ¬ p ∣ R ∧ ¬ p ∣ m ∧
      ¬ ((M : ℤ)) ∣ intWeightedCoeff w (p ^ (M * m.totient) * R) := by
  obtain ⟨R, hRpos, hRnd⟩ := exists_pos_intWeightedCoeff_not_dvd M w hex
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max R m + 1)
  have hRle : R ≤ max R m := le_max_left R m
  have hmle : m ≤ max R m := le_max_right R m
  have hpR : ¬ p ∣ R := by
    intro hdvd
    have h1 : p ≤ R := Nat.le_of_dvd hRpos hdvd
    omega
  have hpm : ¬ p ∣ m := by
    intro hdvd
    have h1 : p ≤ m := Nat.le_of_dvd hm hdvd
    omega
  refine ⟨p, R, hp, hRpos, hpR, hpm, ?_⟩
  intro hdvd
  have hcong := intWeightedCoeff_modEq_of_periodic_extra_orbit M m p R w hm hp
    (by omega : R ≠ 0) hpR hpm hper
  have h0 : intWeightedCoeff w (p ^ (M * m.totient) * R) ≡ 0 [ZMOD (M : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr hdvd
  exact hRnd (Int.modEq_zero_iff_dvd.mp (hcong.symm.trans h0))

/-! ## Signed-coefficient calculus: the signed analysis layer

The analytic lemmas of the linear-growth engine, lifted to `ℤ`-valued
coefficients under the ABSOLUTE growth envelope `|c n| ≤ G·n`.  Each
delegates its content to the `natAbs` instance of the landed Nat lemma;
signs only pass through `summable_abs_iff` and triangle inequalities. -/

/-- Absolute value of an integer cast to ℝ is the cast of `natAbs` —
the cast normal form every signed/absolute comparison below routes
through. -/
theorem abs_intCast_eq_natAbs_cast (a : ℤ) :
    |((a : ℤ) : ℝ)| = ((a.natAbs : ℕ) : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- Summability of a signed coefficient series under absolute linear
growth. -/
theorem summable_int_coeff_term (b G : ℕ) (c : ℕ → ℤ) (hb : 2 ≤ b)
    (habs : ∀ m : ℕ, (c m).natAbs ≤ G * m) :
    Summable (fun m : ℕ => ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1)) := by
  rw [← summable_abs_iff]
  have hnat : Summable
      (fun m : ℕ => (((c (m + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (m + 1)) :=
    summable_coeff_term_linear b G (fun k => (c k).natAbs) hb habs
  refine hnat.congr fun m => ?_
  rw [abs_div, abs_of_pos (show (0 : ℝ) < (b : ℝ) ^ (m + 1) by positivity),
    abs_intCast_eq_natAbs_cast]

/-- Shifted-tail summability for signed coefficients. -/
theorem summable_int_coeff_shift_tail (b N G : ℕ) (c : ℕ → ℤ) (hb : 2 ≤ b)
    (habs : ∀ m : ℕ, (c m).natAbs ≤ G * m) :
    Summable (fun r : ℕ => ((c (N + r + 1) : ℤ) : ℝ) / (b : ℝ) ^ (r + 1)) := by
  rw [← summable_abs_iff]
  have hnat : Summable
      (fun r : ℕ => (((c (N + r + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (r + 1)) :=
    summable_coeff_shift_tail_linear b N G (fun k => (c k).natAbs) hb habs
  refine hnat.congr fun r => ?_
  rw [abs_div, abs_of_pos (show (0 : ℝ) < (b : ℝ) ^ (r + 1) by positivity),
    abs_intCast_eq_natAbs_cast]

/-- **Signed shifted-tail decomposition**: `b^N` times a signed
coefficient series is an integer plus the shifted signed tail. -/
theorem bpow_mul_int_coeff_series_eq_int_add_tail (b N G : ℕ) (c : ℕ → ℤ)
    (hb : 2 ≤ b) (habs : ∀ m : ℕ, (c m).natAbs ≤ G * m) :
    ∃ z : ℤ,
      (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1)) =
        (z : ℝ) + ∑' r : ℕ, ((c (N + r + 1) : ℤ) : ℝ) / (b : ℝ) ^ (r + 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hsum := summable_int_coeff_term b G c hb habs
  refine ⟨∑ i ∈ Finset.range N, c (i + 1) * (b : ℤ) ^ (N - (i + 1)), ?_⟩
  rw [← Summable.sum_add_tsum_nat_add N hsum, mul_add]
  congr 1
  · push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiN : i < N := Finset.mem_range.mp hi
    have hsplit : (b : ℝ) ^ N = (b : ℝ) ^ (N - (i + 1)) * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    field_simp
  · rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [show r + N + 1 = N + r + 1 from by omega]
    have hsplit : (b : ℝ) ^ (N + r + 1) = (b : ℝ) ^ N * (b : ℝ) ^ (r + 1) := by ring
    rw [hsplit]
    field_simp

/-- **Absolute far-tail bound for signed coefficients**: past index `L`,
the signed far tail is absolutely at most `G·(N+L+2)/b^L`. -/
theorem int_coeff_far_tail_abs_le (b N L G : ℕ) (c : ℕ → ℤ) (hb : 2 ≤ b)
    (habs : ∀ m : ℕ, (c m).natAbs ≤ G * m) :
    |∑' t : ℕ, ((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t)|
      ≤ ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  -- the natAbs comparison series, reshaped to the far-tail index pattern
  have hshift := summable_coeff_shift_tail_linear b (N + L) G
    (fun k => (c k).natAbs) hb habs
  have hnat_sum : Summable
      (fun t : ℕ => (((c (N + L + 1 + t)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + t)) := by
    have hmul := hshift.mul_left ((1 : ℝ) / (b : ℝ) ^ L)
    refine hmul.congr fun t => ?_
    rw [show N + L + t + 1 = N + L + 1 + t from by omega]
    have hsplit : (b : ℝ) ^ (L + 1 + t) = (b : ℝ) ^ L * (b : ℝ) ^ (t + 1) := by ring
    rw [hsplit]
    field_simp
  have habs_eq : ∀ t : ℕ,
      |((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t)|
        = (((c (N + L + 1 + t)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + t) := by
    intro t
    rw [abs_div, abs_of_pos (show (0 : ℝ) < (b : ℝ) ^ (L + 1 + t) by positivity),
      abs_intCast_eq_natAbs_cast]
  have habs_sum : Summable
      (fun t : ℕ => |((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t)|) :=
    hnat_sum.congr fun t => (habs_eq t).symm
  have hsigned_sum : Summable
      (fun t : ℕ => ((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t)) :=
    summable_abs_iff.mp habs_sum
  -- |tsum| ≤ tsum of absolute values
  have hle1 : (∑' t : ℕ, ((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t))
      ≤ ∑' t : ℕ, |((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t)| :=
    Summable.tsum_le_tsum (fun t => le_abs_self _) hsigned_sum habs_sum
  have hle2 : -(∑' t : ℕ, ((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t))
      ≤ ∑' t : ℕ, |((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t)| := by
    rw [← tsum_neg]
    exact Summable.tsum_le_tsum (fun t => neg_le_abs _) hsigned_sum.neg habs_sum
  have htri : |∑' t : ℕ, ((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t)|
      ≤ ∑' t : ℕ, |((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t)| :=
    abs_le.mpr ⟨by linarith, hle1⟩
  refine le_trans htri ?_
  have heq : (∑' t : ℕ, |((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t)|)
      = ∑' t : ℕ, (((c (N + L + 1 + t)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (L + 1 + t) :=
    tsum_congr habs_eq
  rw [heq]
  exact coeff_far_tail_le_linear b N L G (fun k => (c k).natAbs) hb habs

/-! ## Signed-coefficient calculus: the protected-block certificate
consumer -/

/-- Exact integer division casts to real division. -/
theorem int_cast_div_real (a d : ℤ) (hdvd : d ∣ a) (h0 : d ≠ 0) :
    (((a / d : ℤ)) : ℝ) = (a : ℝ) / (d : ℝ) := by
  rcases hdvd with ⟨e, rfl⟩
  have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast h0
  rw [Int.mul_ediv_cancel_left e h0]
  push_cast
  rw [mul_div_cancel_left₀ _ hd0]

set_option linter.unusedVariables false in
/-- **Signed protected-block near-integer witness.**  A protected-block
certificate for a signed coefficient sequence `c` with absolute growth
`|c| ≤ G·id`: every first-block slot `r ∈ [1, K]` except the protected
slot `s` is divisible by `b^r`; the protected slot carries a KNOWN
residue `V ≠ 0` mod `b^s`; the middle window `[K+1, L]` has absolute
mass at most `C` over the common denominator `b^L`; and two ℕ-arithmetic
inequalities hold — non-cancellation
`C + G·(N+L+2) < |V|·b^(L-s)` (the protected term dominates all noise)
and smallness `q·(|V|·b^(L-s) + C + G·(N+L+2)) < b^L`.  Then the
`b^N`-dilated signed series is within `(0, 1/q)` of an integer in
ABSOLUTE value — positivity of the tail is replaced by the protected
residue.  (`hV` is implied by `hlow` — it stays in the signature because
a protected-block certificate is DEFINED by its nonzero residue.) -/
theorem near_int_witness_of_int_coeff_protected_block_certificate
    (b q N K L s C G : ℕ) (c : ℕ → ℤ) (V : ℤ)
    (hb : 2 ≤ b) (hq : 0 < q) (hs1 : 1 ≤ s) (hsK : s ≤ K) (hKL : K ≤ L)
    (habs : ∀ m : ℕ, (c m).natAbs ≤ G * m)
    (hblock : ∀ r ∈ Finset.Icc 1 K, r ≠ s → ((b : ℤ)) ^ r ∣ c (N + r))
    (hprot : ((b : ℤ)) ^ s ∣ (c (N + s) - V))
    (hV : V ≠ 0)
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, (c (N + r)).natAbs * b ^ (L - r) ≤ C)
    (hlow : C + G * (N + L + 2) < V.natAbs * b ^ (L - s))
    (hhigh : q * (V.natAbs * b ^ (L - s) + (C + G * (N + L + 2))) < b ^ L) :
    ∃ z : ℤ,
      0 < |(b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)| ∧
        |(b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)| < 1 / (q : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = j + 1 := ⟨s - 1, by omega⟩
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hbZ : (b : ℤ) ≠ 0 := by
    have : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
    omega
  obtain ⟨z₀, hz₀⟩ := bpow_mul_int_coeff_series_eq_int_add_tail b N G c hb habs
  have hfsum : Summable
      (fun r : ℕ => ((c (N + r + 1) : ℤ) : ℝ) / (b : ℝ) ^ (r + 1)) :=
    summable_int_coeff_shift_tail b N G c hb habs
  have hfarsum : Summable
      (fun t : ℕ => ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)) :=
    (summable_nat_add_iff L).mpr hfsum
  -- split the tail at L, then the finite part at K
  have hsplitL : (∑' r : ℕ, ((c (N + r + 1) : ℤ) : ℝ) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  have hsplitK : (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  -- peel the protected slot off the first block
  have hjK : j ∈ Finset.range K := Finset.mem_range.mpr (by omega)
  have hsplitS : (∑ i ∈ Finset.range K, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
      = ((c (N + j + 1) : ℤ) : ℝ) / (b : ℝ) ^ (j + 1)
        + ∑ i ∈ (Finset.range K).erase j,
            ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1) :=
    (Finset.add_sum_erase _ _ hjK).symm
  -- the unprotected block slots form an integer
  have hz₁ : ((∑ i ∈ (Finset.range K).erase j,
        c (N + i + 1) / (b : ℤ) ^ (i + 1) : ℤ) : ℝ)
      = ∑ i ∈ (Finset.range K).erase j,
          ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1) := by
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hdvd : ((b : ℤ)) ^ (i + 1) ∣ c (N + i + 1) :=
      hblock (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)
    rw [int_cast_div_real (c (N + i + 1)) ((b : ℤ) ^ (i + 1)) hdvd
      (pow_ne_zero (i + 1) hbZ)]
    push_cast
    rfl
  -- the protected slot splits into an integer plus the residue term
  obtain ⟨a, ha⟩ := hprot
  have ha' : c (N + j + 1) - V = (b : ℤ) ^ (j + 1) * a := ha
  have hprot_eq : ((c (N + j + 1) : ℤ) : ℝ) / (b : ℝ) ^ (j + 1)
      = (a : ℝ) + ((V : ℤ) : ℝ) / (b : ℝ) ^ (j + 1) := by
    have hc : c (N + j + 1) = (b : ℤ) ^ (j + 1) * a + V := by omega
    rw [hc]
    have hbp : ((b : ℝ)) ^ (j + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  -- absolute middle bound over the common denominator b^L
  have hmid_abs : |∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1)|
      ≤ (C : ℝ) / (b : ℝ) ^ L := by
    have htri : |∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1)|
        ≤ ∑ i ∈ Finset.Ico K L,
            (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _)
        (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [abs_div, abs_of_pos (show (0 : ℝ) < (b : ℝ) ^ (i + 1) by positivity),
        abs_intCast_eq_natAbs_cast]
    refine le_trans htri ?_
    have hterm : ∀ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1)
          = (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
      intro i hi
      obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
      have hb1 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
      have hbL' : ((b : ℝ) ^ L) ≠ 0 := by positivity
      have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (L - (i + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [div_eq_div_iff hb1 hbL']
      push_cast
      rw [hsplit]
      ring
    have hreindex : (∑ i ∈ Finset.Ico K L, (c (N + i + 1)).natAbs * b ^ (L - (i + 1)))
        = ∑ r ∈ Finset.Icc (K + 1) L, (c (N + r)).natAbs * b ^ (L - r) := by
      have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
        ext a'
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      have hn : L + 1 - (K + 1) = L - K := by omega
      rw [hn]
      refine Finset.sum_congr rfl fun j' hj' => ?_
      have h1 : N + (K + j') + 1 = N + (K + 1 + j') := by omega
      have h2 : L - (K + j' + 1) = L - (K + 1 + j') := by omega
      rw [h1, h2]
    have hsum_eq : (∑ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    have hnum : (∑ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ)) ≤ (C : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hreindex.trans_le hmiddle
    calc (∑ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L :=
          hsum_eq
      _ ≤ (C : ℝ) / (b : ℝ) ^ L := by gcongr
  -- absolute far-tail bound
  have hfar_eq : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, ((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar_abs : |∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)|
      ≤ ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact int_coeff_far_tail_abs_le b N L G c hb habs
  -- assemble: deviation = protected residue + (middle + far)
  have hdiff : (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
      - ((z₀ + (∑ i ∈ (Finset.range K).erase j, c (N + i + 1) / (b : ℤ) ^ (i + 1))
          + a : ℤ) : ℝ)
      = ((V : ℤ) : ℝ) / (b : ℝ) ^ (j + 1)
        + ((∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
          + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)) := by
    rw [hz₀, hsplitL, hsplitK, hsplitS, hprot_eq]
    push_cast
    rw [← hz₁]
    push_cast
    ring
  set P : ℝ := ((V : ℤ) : ℝ) / (b : ℝ) ^ (j + 1) with hPdef
  set MF : ℝ := (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
      + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) with hMFdef
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  -- numeric bounds over the common denominator b^L
  have hMF_le : |MF| ≤ ((C + G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hMFdef]
    calc |(∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)|
        ≤ |∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1)|
          + |∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)| :=
          abs_add_le _ _
      _ ≤ (C : ℝ) / (b : ℝ) ^ L + ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L :=
          add_le_add hmid_abs hfar_abs
      _ = ((C + G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
          rw [← add_div]
          push_cast
          ring
  have hP_abs : |P| = ((V.natAbs * b ^ (L - (j + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    have h1 : |P| = ((V.natAbs : ℕ) : ℝ) / (b : ℝ) ^ (j + 1) := by
      rw [hPdef, abs_div,
        abs_of_pos (show (0 : ℝ) < (b : ℝ) ^ (j + 1) by positivity),
        abs_intCast_eq_natAbs_cast]
    have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (j + 1) * (b : ℝ) ^ (L - (j + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    have hb1 : ((b : ℝ) ^ (j + 1)) ≠ 0 := by positivity
    have hbL' : ((b : ℝ) ^ L) ≠ 0 := ne_of_gt hbL
    rw [h1, div_eq_div_iff hb1 hbL']
    push_cast
    rw [hsplit]
    ring
  -- lower bound: the protected residue survives the noise
  have hlow' : ((C + G * (N + L + 2) : ℕ) : ℝ)
      < ((V.natAbs * b ^ (L - (j + 1)) : ℕ) : ℝ) := by exact_mod_cast hlow
  have hP_gt : ((C + G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L < |P| := by
    rw [hP_abs]
    gcongr
  refine ⟨z₀ + (∑ i ∈ (Finset.range K).erase j, c (N + i + 1) / (b : ℤ) ^ (i + 1)) + a,
    ?_, ?_⟩
  · -- lower: the protected residue survives the noise
    rw [hdiff]
    have h7 : |P| ≤ |P + MF| + |MF| := by
      have h8 : P = P + MF + -MF := by ring
      calc |P| = |P + MF + -MF| := by rw [← h8]
        _ ≤ |P + MF| + |-MF| := abs_add_le _ _
        _ = |P + MF| + |MF| := by rw [abs_neg]
    have h9 : (0 : ℝ) < |P + MF| := by linarith
    exact h9
  · -- upper: everything is below 1/q
    rw [hdiff]
    have h10 : |P + MF| ≤ |P| + |MF| := abs_add_le _ _
    have h11 : |P| + |MF|
        ≤ ((V.natAbs * b ^ (L - (j + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L
          + ((C + G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
      rw [hP_abs]
      linarith
    have h12 : ((V.natAbs * b ^ (L - (j + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L
        + ((C + G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L < 1 / (q : ℝ) := by
      rw [← add_div, div_lt_div_iff₀ hbL hq', one_mul]
      have hc : (q : ℝ) * (((V.natAbs * b ^ (L - (j + 1)) : ℕ) : ℝ)
          + ((C + G * (N + L + 2) : ℕ) : ℝ)) < (b : ℝ) ^ L := by
        exact_mod_cast hhigh
      calc (((V.natAbs * b ^ (L - (j + 1)) : ℕ) : ℝ)
            + ((C + G * (N + L + 2) : ℕ) : ℝ)) * (q : ℝ)
          = (q : ℝ) * (((V.natAbs * b ^ (L - (j + 1)) : ℕ) : ℝ)
            + ((C + G * (N + L + 2) : ℕ) : ℝ)) := mul_comm _ _
        _ < (b : ℝ) ^ L := hc
    linarith

/-- **Signed coefficient-series irrationality from protected-block
certificates.**  If a signed coefficient sequence with absolute growth
`|c| ≤ G·id` has a protected-block certificate at every precision,
then `∑ c(m)/b^m` is irrational.  This is the signed analogue of the
one-sided engine: tail positivity is replaced by a certified protected
residue.  Whether `c = intWeightedCoeff w` for periodic signed `w`
has such certificates is the OPEN supply obligation — not claimed. -/
theorem irrational_int_coeff_series_of_protected_block_certificates
    (b G : ℕ) (c : ℕ → ℤ) (hb : 2 ≤ b)
    (habs : ∀ m : ℕ, (c m).natAbs ≤ G * m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ (N K L s C : ℕ) (V : ℤ), 1 ≤ s ∧ s ≤ K ∧ K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, r ≠ s → ((b : ℤ)) ^ r ∣ c (N + r)) ∧
        ((b : ℤ)) ^ s ∣ (c (N + s) - V) ∧ V ≠ 0 ∧
        (∑ r ∈ Finset.Icc (K + 1) L, (c (N + r)).natAbs * b ^ (L - r) ≤ C) ∧
        (C + G * (N + L + 2) < V.natAbs * b ^ (L - s)) ∧
        q * (V.natAbs * b ^ (L - s) + (C + G * (N + L + 2))) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1)) := by
  apply irrational_of_pow_mul_near_int b
  intro q hq
  obtain ⟨N, K, L, s, C, V, hs1, hsK, hKL, hblock, hprot, hV, hmiddle, hlow, hhigh⟩ :=
    hcert q hq
  obtain ⟨z, hz_pos, hz_lt⟩ :=
    near_int_witness_of_int_coeff_protected_block_certificate
      b q N K L s C G c V hb hq hs1 hsK hKL habs hblock hprot hV hmiddle hlow hhigh
  exact ⟨N, z, hz_pos, hz_lt⟩

/-! ## Signed-coefficient calculus: the signed weighted Lambert bridge -/

/-- **The signed weighted Erdős series** `∑_a w(a)/(b^a - 1)` for an
integer weight.  The `a = 0` term is junk-safe (`w(0)/0 = 0`).  At a cast
Nat weight this is `weightedErdosSeries`; mixed-sign rational coefficient
series reduce to it by clearing denominators. -/
noncomputable def intWeightedErdosSeries (b : ℕ) (w : ℕ → ℤ) : ℝ :=
  ∑' a : ℕ, ((w a : ℤ) : ℝ) / ((b : ℝ) ^ a - 1)

/-- Summability of the signed weighted series for a bounded weight. -/
theorem summable_intWeightedErdos_term (b W : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b)
    (hW : ∀ n : ℕ, (w n).natAbs ≤ W) :
    Summable (fun a : ℕ => ((w a : ℤ) : ℝ) / ((b : ℝ) ^ a - 1)) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have h : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  rw [← summable_abs_iff]
  have hnat := summable_weightedErdos_term b W (fun a => (w a).natAbs) hb hW
  refine hnat.congr fun a => ?_
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · simp
  · have hden : (0 : ℝ) < (b : ℝ) ^ a - 1 := by
      have h1 : (1 : ℝ) < (b : ℝ) ^ a := one_lt_pow₀ hb1 (by omega)
      linarith
    rw [abs_div, abs_of_pos hden, abs_intCast_eq_natAbs_cast]

/-- **Signed weighted Lambert bridge**: the signed weighted Erdős series
equals the signed coefficient series `∑ intWeightedCoeff w (n)/b^n`.
Both `toNat` parts ride the landed `W`-normalised Nat bridge; the
subtraction is an identity of SUMS, never of irrationality statements. -/
theorem intWeightedErdosSeries_eq_tsum_intWeightedCoeff (b W : ℕ) (w : ℕ → ℤ)
    (hb : 2 ≤ b) (hWpos : 0 < W) (hW : ∀ n : ℕ, (w n).natAbs ≤ W) :
    intWeightedErdosSeries b w
      = ∑' m : ℕ, ((intWeightedCoeff w (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1) := by
  have hwpW : ∀ n : ℕ, (w n).toNat ≤ W := by
    intro n
    have := hW n
    omega
  have hwnW : ∀ n : ℕ, (-(w n)).toNat ≤ W := by
    intro n
    have := hW n
    omega
  have hsp := summable_weightedErdos_term b W (fun a => (w a).toNat) hb hwpW
  have hsn := summable_weightedErdos_term b W (fun a => (-(w a)).toNat) hb hwnW
  have hpoint : ∀ a : ℕ, ((w a : ℤ) : ℝ) / ((b : ℝ) ^ a - 1)
      = (((w a).toNat : ℕ) : ℝ) / ((b : ℝ) ^ a - 1)
        - (((-(w a)).toNat : ℕ) : ℝ) / ((b : ℝ) ^ a - 1) := by
    intro a
    have hcast : ((w a : ℤ) : ℝ)
        = (((w a).toNat : ℕ) : ℝ) - (((-(w a)).toNat : ℕ) : ℝ) := by
      have h : (((w a).toNat : ℕ) : ℤ) - (((-(w a)).toNat : ℕ) : ℤ) = w a := by omega
      have h2 := congrArg (fun z : ℤ => ((z : ℤ) : ℝ)) h
      push_cast at h2
      linarith [h2]
    rw [hcast, sub_div]
  have hsplit : intWeightedErdosSeries b w
      = weightedErdosSeries b (fun a => (w a).toNat)
        - weightedErdosSeries b (fun a => (-(w a)).toNat) := by
    unfold intWeightedErdosSeries weightedErdosSeries
    rw [← Summable.tsum_sub hsp hsn]
    exact tsum_congr hpoint
  rw [hsplit,
    weightedErdosSeries_eq_tsum_weightedCoeff b W (fun a => (w a).toNat) hb hWpos hwpW,
    weightedErdosSeries_eq_tsum_weightedCoeff b W (fun a => (-(w a)).toNat) hb hWpos hwnW]
  have hcp : Summable (fun m : ℕ =>
      ((weightedCoeff (fun a => (w a).toNat) (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ (m + 1)) :=
    summable_coeff_term_linear b W _ hb
      (fun k => weightedCoeff_le_mul_self _ W k hwpW)
  have hcn : Summable (fun m : ℕ =>
      ((weightedCoeff (fun a => (-(w a)).toNat) (m + 1) : ℕ) : ℝ) / (b : ℝ) ^ (m + 1)) :=
    summable_coeff_term_linear b W _ hb
      (fun k => weightedCoeff_le_mul_self _ W k hwnW)
  rw [← Summable.tsum_sub hcp hcn]
  refine tsum_congr fun m => ?_
  rw [← sub_div]
  congr 1
  have h := intWeightedCoeff_eq_weightedCoeff_sub w (m + 1)
  have h2 := congrArg (fun z : ℤ => ((z : ℤ) : ℝ)) h
  push_cast at h2
  linarith [h2]

/-- **Conditional signed weighted Lambert irrationality.**  A bounded
signed weight whose coefficient sequence `intWeightedCoeff w` has
protected-block certificates at every precision has an irrational signed
weighted Erdős series `∑_a w(a)/(b^a - 1)`.  This is the signed
Luca–Tachiya SOCKET: everything is reduced to the certificate supply.
The supply for periodic signed weights — cofactor non-cancellation
inside the frame progression — is the open wave-13 obligation and is NOT
claimed here. -/
theorem irrational_intWeightedErdosSeries_of_protected_block_certificates
    (b W : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hWpos : 0 < W)
    (hW : ∀ n : ℕ, (w n).natAbs ≤ W)
    (hcert : ∀ q : ℕ, 0 < q → ∃ (N K L s C : ℕ) (V : ℤ), 1 ≤ s ∧ s ≤ K ∧ K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, r ≠ s →
          ((b : ℤ)) ^ r ∣ intWeightedCoeff w (N + r)) ∧
        ((b : ℤ)) ^ s ∣ (intWeightedCoeff w (N + s) - V) ∧ V ≠ 0 ∧
        (∑ r ∈ Finset.Icc (K + 1) L,
          (intWeightedCoeff w (N + r)).natAbs * b ^ (L - r) ≤ C) ∧
        (C + W * (N + L + 2) < V.natAbs * b ^ (L - s)) ∧
        q * (V.natAbs * b ^ (L - s) + (C + W * (N + L + 2))) < b ^ L) :
    Irrational (intWeightedErdosSeries b w) := by
  rw [intWeightedErdosSeries_eq_tsum_intWeightedCoeff b W w hb hWpos hW]
  exact irrational_int_coeff_series_of_protected_block_certificates b W
    (intWeightedCoeff w) hb
    (fun n => natAbs_intWeightedCoeff_le_mul_self w W n hW) hcert

/-! ## Signed-coefficient calculus: the wave-13 dichotomy engine

The wave-12 protected slot exists to certify a NONZERO fractional
residue.  Wave 13 records the reduction that makes most of that
machinery unnecessary: a rational number `x` whose base-`b` dilations
`b^N·x` are never integers keeps every `b^N·x` at distance `≥ 1/den(x)`
from `ℤ`, so a FULL-divisibility certificate (every first-block slot
divisible, no protected slot, no positivity, no nonzero residue) at
precision `q = den(x)` already contradicts rationality.  The
full-block certificate supply is the landed periodic frame machinery
verbatim — positivity was only ever consumed by the far-tail witness,
and the protected slot only ever excluded the single remaining escape:
`x` a base-`b` TERMINATING rational `z/b^k`.

Consequence, unconditional for EVERY `m`-periodic signed integer
weight: `∑ w(a)/(b^a−1)` is irrational OR equals `z/b^k` for some
`z, k`.  The mixed-sign obligation shrinks from protected-certificate
supply at every precision to the single non-termination question.

The companion lemma
`intWeightedCoeff_periodFourSignWeight_eq_zero_of_mod_four_eq_three`
records why the certificate frame CANNOT be steered onto nonzero
cofactor residues by residue selection alone: for the period-4 sign
weight `1, 0, −1, 0` the divisor involution `d ↦ n/d` pairs opposite
signs on every `n ≡ 3 mod 4`, so the signed coefficient vanishes
IDENTICALLY on that residue class — zero sets of periodic signed
coefficients can contain full arithmetic progressions.  Non-termination
for general periodic signed weights therefore remains the honest open
frontier; it is NOT claimed here. -/

/-- **Rational non-termination self-defence.**  If `b^N·x` is not the
integer `z` (as a rational number), then the real distance from
`b^N·x` to `z` is at least `1/den(x)`: the difference is a fraction
with nonzero integer numerator over the denominator of `x`.  This is
the entire reason full-divisibility certificates suffice against
non-terminating rationals. -/
theorem inv_den_le_abs_bpow_mul_sub_intCast (b N : ℕ) (x : ℚ) (z : ℤ)
    (hne : ((b : ℚ)) ^ N * x ≠ ((z : ℤ) : ℚ)) :
    1 / (x.den : ℝ) ≤ |(b : ℝ) ^ N * ((x : ℚ) : ℝ) - ((z : ℤ) : ℝ)| := by
  have hden0 : x.den ≠ 0 := x.den_nz
  have hdenQ : ((x.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hden0
  have hden_pos : (0 : ℝ) < (x.den : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hden0
  have hxq : x * ((x.den : ℕ) : ℚ) = ((x.num : ℤ) : ℚ) := by
    nth_rewrite 1 [← Rat.num_div_den x]
    exact div_mul_cancel₀ _ hdenQ
  have hD0 : (b : ℤ) ^ N * x.num - z * (x.den : ℤ) ≠ 0 := by
    intro h0
    apply hne
    have hnum : (b : ℤ) ^ N * x.num = z * (x.den : ℤ) := by omega
    have hcast := congrArg (fun t : ℤ => ((t : ℤ) : ℚ)) hnum
    push_cast at hcast
    have hmulden : ((b : ℚ)) ^ N * x * ((x.den : ℕ) : ℚ)
        = ((z : ℤ) : ℚ) * ((x.den : ℕ) : ℚ) := by
      have h1 : ((b : ℚ)) ^ N * x * ((x.den : ℕ) : ℚ)
          = ((b : ℚ)) ^ N * (x * ((x.den : ℕ) : ℚ)) := by ring
      rw [h1, hxq]
      exact_mod_cast hcast
    exact mul_right_cancel₀ hdenQ hmulden
  have honeZ : (1 : ℤ) ≤ |(b : ℤ) ^ N * x.num - z * (x.den : ℤ)| := Int.one_le_abs hD0
  have hkey : (b : ℝ) ^ N * ((x : ℚ) : ℝ) - ((z : ℤ) : ℝ)
      = (((b : ℤ) ^ N * x.num - z * (x.den : ℤ) : ℤ) : ℝ) / (x.den : ℝ) := by
    have hxR : ((x : ℚ) : ℝ) = ((x.num : ℤ) : ℝ) / ((x.den : ℕ) : ℝ) := by
      conv_lhs => rw [← Rat.num_div_den x]
      push_cast
      ring
    have hdR : ((x.den : ℕ) : ℝ) ≠ 0 := ne_of_gt hden_pos
    rw [hxR]
    field_simp
    push_cast
    ring
  rw [hkey, abs_div, abs_of_pos hden_pos]
  have honeR : (1 : ℝ) ≤ |(((b : ℤ) ^ N * x.num - z * (x.den : ℤ) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast honeZ
  gcongr

/-- **Full-block near-integer witness.**  A full-divisibility
certificate for a signed coefficient sequence `c` with absolute growth
`|c| ≤ G·id`: EVERY first-block slot `r ∈ [1, K]` is divisible by
`b^r` (no protected slot), the middle window `[K+1, L]` has absolute
mass at most `C` over the common denominator `b^L`, and the single
smallness inequality `q·(C + G·(N+L+2)) < b^L` holds.  Then the
`b^N`-dilated signed series is within `1/q` of an integer — with NO
claim that the distance is nonzero.  Nonzeroness is exactly what the
protected slot buys; against a non-terminating rational it is not
needed. -/
theorem near_int_of_int_coeff_full_block_certificate
    (b q N K L C G : ℕ) (c : ℕ → ℤ)
    (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (habs : ∀ m : ℕ, (c m).natAbs ≤ G * m)
    (hblock : ∀ r ∈ Finset.Icc 1 K, ((b : ℤ)) ^ r ∣ c (N + r))
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, (c (N + r)).natAbs * b ^ (L - r) ≤ C)
    (hhigh : q * (C + G * (N + L + 2)) < b ^ L) :
    ∃ z : ℤ,
      |(b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
          - (z : ℝ)| < 1 / (q : ℝ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hbZ : (b : ℤ) ≠ 0 := by
    have : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
    omega
  obtain ⟨z₀, hz₀⟩ := bpow_mul_int_coeff_series_eq_int_add_tail b N G c hb habs
  have hfsum : Summable
      (fun r : ℕ => ((c (N + r + 1) : ℤ) : ℝ) / (b : ℝ) ^ (r + 1)) :=
    summable_int_coeff_shift_tail b N G c hb habs
  have hsplitL : (∑' r : ℕ, ((c (N + r + 1) : ℤ) : ℝ) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  have hsplitK : (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  -- the ENTIRE first block is an integer: every slot is divisible
  have hz₁ : ((∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1) : ℤ) : ℝ)
      = ∑ i ∈ Finset.range K, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1) := by
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp hi
    have hdvd : ((b : ℤ)) ^ (i + 1) ∣ c (N + i + 1) :=
      hblock (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [int_cast_div_real (c (N + i + 1)) ((b : ℤ) ^ (i + 1)) hdvd
      (pow_ne_zero (i + 1) hbZ)]
    push_cast
    rfl
  -- absolute middle bound over the common denominator b^L
  have hmid_abs : |∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1)|
      ≤ (C : ℝ) / (b : ℝ) ^ L := by
    have htri : |∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1)|
        ≤ ∑ i ∈ Finset.Ico K L,
            (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _)
        (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [abs_div, abs_of_pos (show (0 : ℝ) < (b : ℝ) ^ (i + 1) by positivity),
        abs_intCast_eq_natAbs_cast]
    refine le_trans htri ?_
    have hterm : ∀ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1)
          = (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
      intro i hi
      obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
      have hb1 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
      have hbL' : ((b : ℝ) ^ L) ≠ 0 := by positivity
      have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (L - (i + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [div_eq_div_iff hb1 hbL']
      push_cast
      rw [hsplit]
      ring
    have hreindex : (∑ i ∈ Finset.Ico K L, (c (N + i + 1)).natAbs * b ^ (L - (i + 1)))
        = ∑ r ∈ Finset.Icc (K + 1) L, (c (N + r)).natAbs * b ^ (L - r) := by
      have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
        ext a'
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      have hn : L + 1 - (K + 1) = L - K := by omega
      rw [hn]
      refine Finset.sum_congr rfl fun j' hj' => ?_
      have h1 : N + (K + j') + 1 = N + (K + 1 + j') := by omega
      have h2 : L - (K + j' + 1) = L - (K + 1 + j') := by omega
      rw [h1, h2]
    have hsum_eq : (∑ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    have hnum : (∑ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ)) ≤ (C : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hreindex.trans_le hmiddle
    calc (∑ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L :=
          hsum_eq
      _ ≤ (C : ℝ) / (b : ℝ) ^ L := by gcongr
  -- absolute far-tail bound
  have hfar_eq : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, ((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar_abs : |∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)|
      ≤ ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact int_coeff_far_tail_abs_le b N L G c hb habs
  -- assemble: the deviation is exactly middle + far
  have hdiff : (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
      - ((z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1) : ℤ) : ℝ)
      = (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) := by
    rw [hz₀, hsplitL, hsplitK]
    push_cast
    rw [← hz₁]
    push_cast
    ring
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  refine ⟨z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1), ?_⟩
  rw [hdiff]
  calc |(∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
      + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)|
      ≤ (C : ℝ) / (b : ℝ) ^ L + ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L :=
        le_trans (abs_add_le _ _) (add_le_add hmid_abs hfar_abs)
    _ = ((C + G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
        rw [← add_div]
        push_cast
        ring
    _ < 1 / (q : ℝ) := by
        rw [div_lt_div_iff₀ hbL hq', one_mul]
        have hc : (q : ℝ) * ((C + G * (N + L + 2) : ℕ) : ℝ) < (b : ℝ) ^ L := by
          exact_mod_cast hhigh
        calc ((C + G * (N + L + 2) : ℕ) : ℝ) * (q : ℝ)
            = (q : ℝ) * ((C + G * (N + L + 2) : ℕ) : ℝ) := mul_comm _ _
          _ < (b : ℝ) ^ L := hc

/-- **The dichotomy engine.**  A signed coefficient sequence with
absolute linear growth and a full-divisibility certificate at every
precision has a series that is irrational OR base-`b` terminating
(`b^k`-dilate an integer for some `k`).  Proof shape: a rational value
whose dilations never hit `ℤ` defends itself at distance `1/den`
(`inv_den_le_abs_bpow_mul_sub_intCast`), while the certificate at
precision `den` pushes some dilation strictly closer than `1/den`. -/
theorem int_coeff_series_irrational_or_bpow_mul_eq_intCast_of_full_block_certificates
    (b G : ℕ) (c : ℕ → ℤ) (hb : 2 ≤ b)
    (habs : ∀ m : ℕ, (c m).natAbs ≤ G * m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, ((b : ℤ)) ^ r ∣ c (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, (c (N + r)).natAbs * b ^ (L - r) ≤ C) ∧
        q * (C + G * (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
      ∨ ∃ (k : ℕ) (z : ℤ),
          (b : ℝ) ^ k * (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
            = (z : ℝ) := by
  by_cases hirr : Irrational (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
  · exact Or.inl hirr
  · right
    by_contra hterm
    push Not at hterm
    have hmem : ¬¬((∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
        ∈ Set.range ((↑) : ℚ → ℝ)) := hirr
    obtain ⟨x, hx⟩ := not_not.mp hmem
    have hden0 : x.den ≠ 0 := x.den_nz
    have hdpos : 0 < x.den := Nat.pos_of_ne_zero hden0
    obtain ⟨N, K, L, C, hKL, hblock, hmiddle, hhigh⟩ := hcert x.den hdpos
    obtain ⟨z, hz⟩ := near_int_of_int_coeff_full_block_certificate
      b x.den N K L C G c hb hdpos hKL habs hblock hmiddle hhigh
    have hneQ : ((b : ℚ)) ^ N * x ≠ ((z : ℤ) : ℚ) := by
      intro heq
      refine hterm N z ?_
      rw [← hx]
      have hcast := congrArg (fun t : ℚ => ((t : ℚ) : ℝ)) heq
      push_cast at hcast
      exact_mod_cast hcast
    have hlow := inv_den_le_abs_bpow_mul_sub_intCast b N x z hneQ
    rw [hx] at hlow
    linarith [hz, hlow]

/-- **Full-block certificate supply for periodic signed weights** —
UNCONDITIONAL.  The layered periodic orbit sieve manufactures a
full-divisibility certificate at every precision for EVERY `m`-periodic
signed integer weight with `|w| ≤ W`: the exact-valuation frame at
`B = b·φ(m)` feeds the signed complete-cycle divisibility for the first
block (complete Euler cycles never used positivity), the absolute
envelope `|intWeightedCoeff| ≤ W·τ` scales the selected divisor-pair
average through the middle window, and the frame precision is amplified
to `q·W` so the smallness inequality closes.  This is the landed Nat
supply with the far-tail positivity witness DELETED — nothing else
changes. -/
theorem exists_full_block_certificates_intWeightedCoeff_periodic
    (b m W : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hW : ∀ n : ℕ, (w n).natAbs ≤ W) (hWpos : 0 < W) :
    ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
      (∀ r ∈ Finset.Icc 1 K, ((b : ℤ)) ^ r ∣ intWeightedCoeff w (N + r)) ∧
      (∑ r ∈ Finset.Icc (K + 1) L,
        (intWeightedCoeff w (N + r)).natAbs * b ^ (L - r) ≤ C) ∧
      q * (C + W * (N + L + 2)) < b ^ L := by
  intro q hq
  have htpos : 0 < m.totient := Nat.totient_pos.mpr hm
  set q' : ℕ := q * W with hq'def
  have hq' : 0 < q' := Nat.mul_pos hq hWpos
  set B : ℕ := b * m.totient with hBdef
  have hB : 2 ≤ B := by
    have h1 : b ≤ b * m.totient := Nat.le_mul_of_pos_right b htpos
    omega
  set K : ℕ := 9 * (q' + B + m + 100) with hKdef
  set κ : ℕ := 3 * (2 * B * K ^ 2 + 1) + (2 * B * K ^ 2 * (K * (K + 1) + 1) + q' + 4)
    with hκdef
  set E : ℕ := B * K ^ 2 * (K * (K + 1) + κ + 1) with hEdef
  obtain ⟨hparamA, hparamB, hK1, hKκpow, hmK⟩ :=
    certificate_param_arithmetic_periodic b B m q' K κ E hb hB hq' hKdef hκdef hEdef
  set L : ℕ := 2 ^ κ with hLdef
  clear_value K κ E L
  have hKL : K ≤ L := hKκpow
  obtain ⟨x, A', P, hApos, hxA, hLA, hAle, hsupp, hcards, hprimes, hgtL, hval⟩ :=
    exists_bounded_exact_valuation_frame B L K hB hK1 hKL
  have hA2E : A' ≤ 2 ^ E := by
    have h1 : L + 1 ≤ 2 ^ (κ + 1) := by
      have h1a : (2 : ℕ) ^ (κ + 1) = 2 ^ κ * 2 := pow_succ 2 κ
      omega
    have h4 : A' ≤ (2 ^ (K * (K + 1) + (κ + 1))) ^ (B * K ^ 2) := by
      calc A' ≤ (2 ^ (K * (K + 1)) * (L + 1)) ^ (B * K ^ 2) := hAle
        _ ≤ (2 ^ (K * (K + 1)) * 2 ^ (κ + 1)) ^ (B * K ^ 2) := by
            apply Nat.pow_le_pow_left
            exact Nat.mul_le_mul_left _ h1
        _ = (2 ^ (K * (K + 1) + (κ + 1))) ^ (B * K ^ 2) := by rw [← pow_add]
    have h5 : ((2 : ℕ) ^ (K * (K + 1) + (κ + 1))) ^ (B * K ^ 2)
        = 2 ^ ((K * (K + 1) + (κ + 1)) * (B * K ^ 2)) := (pow_mul 2 _ _).symm
    have h6 : (2 : ℕ) ^ ((K * (K + 1) + (κ + 1)) * (B * K ^ 2)) ≤ 2 ^ E := by
      apply Nat.pow_le_pow_right (by norm_num)
      have h7 : E = (K * (K + 1) + (κ + 1)) * (B * K ^ 2) := by rw [hEdef]; ring
      omega
    omega
  obtain ⟨y, hyA, hWy⟩ :=
    selected_weighted_middle_of_supported_frame b x A' K L A' hb hApos hsupp
  -- first block: signed complete-cycle divisibility on the exposed prime blocks
  have hfirst : ∀ r ∈ Finset.Icc 1 K,
      ((b : ℤ)) ^ r ∣ intWeightedCoeff w (x + y * A' + r) := by
    intro r hr
    have hr1 := (Finset.mem_Icc.mp hr).1
    have hne : x + y * A' + r ≠ 0 := by omega
    have hgtm : ∀ p ∈ P r, m < p := by
      intro p hp
      have h1 := hgtL r hr p hp
      have h2 : m ≤ K := hmK
      have h3 : K ≤ L := hKL
      omega
    have hexact : ∀ p ∈ P r, (x + y * A' + r).factorization p = b * m.totient - 1 := by
      intro p hp
      have h1 := hval y r hr p hp
      rwa [hBdef] at h1
    have hdvd := bpow_dvd_intWeightedCoeff_of_periodic_exact_block b m
      (x + y * A' + r) w hb hm hne hper (P r) (fun p hp => hprimes r hr p hp)
      hgtm hexact
    rwa [hcards r hr] at hdvd
  -- middle window: dominate by W·τ and reuse the selected divisor-pair average
  have hmiddle : ∑ r ∈ Finset.Icc (K + 1) L,
      (intWeightedCoeff w (x + y * A' + r)).natAbs * b ^ (L - r)
      ≤ W * ((b ^ (L - K)
          * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + A' * A' + L)), (A' / d + 1))) / A') := by
    calc ∑ r ∈ Finset.Icc (K + 1) L,
        (intWeightedCoeff w (x + y * A' + r)).natAbs * b ^ (L - r)
        ≤ ∑ r ∈ Finset.Icc (K + 1) L,
            W * ((x + y * A' + r).divisors.card * b ^ (L - r)) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _
            (natAbs_intWeightedCoeff_le_mul_card_divisors w W _ hW)
      _ = W * ∑ r ∈ Finset.Icc (K + 1) L,
            (x + y * A' + r).divisors.card * b ^ (L - r) := by
          rw [Finset.mul_sum]
      _ ≤ W * ((b ^ (L - K)
            * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + A' * A' + L)), (A' / d + 1))) / A') :=
          Nat.mul_le_mul_left W hWy
  refine ⟨x + y * A', K, L,
    W * ((b ^ (L - K)
      * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (x + A' * A' + L)), (A' / d + 1))) / A'),
    hKL, hfirst, hmiddle, ?_⟩
  set S : ℕ := Nat.sqrt (x + A' * A' + L) with hSdef
  have hSle : S ≤ A' + L + 1 := by
    have h1 : x + A' * A' + L ≤ (A' + L + 1) * (A' + L + 1) := by
      have hexp : (A' + L + 1) * (A' + L + 1)
          = A' * A' + (2 * (A' * (L + 1)) + (L + 1) * (L + 1)) := by ring
      have h2 : A' ≤ A' * (L + 1) := Nat.le_mul_of_pos_right A' (by omega)
      have h3 : L + 1 ≤ (L + 1) * (L + 1) :=
        Nat.le_mul_of_pos_right (L + 1) (by omega)
      omega
    have h4 : Nat.sqrt (x + A' * A' + L) ≤ Nat.sqrt ((A' + L + 1) * (A' + L + 1)) :=
      Nat.sqrt_le_sqrt h1
    rw [Nat.sqrt_eq] at h4
    rw [hSdef]
    exact h4
  have hSpow : S ≤ 2 ^ (E + κ + 2) := by
    have h1 : (2 : ℕ) ^ (E + κ + 2) = 2 ^ E * 2 ^ (κ + 2) := pow_add 2 E (κ + 2)
    have h2 : (4 : ℕ) ≤ 2 ^ (κ + 2) := by
      have h2a : (2 : ℕ) ^ (κ + 2) = 2 ^ κ * 4 := by rw [pow_add]; norm_num
      have h2b : (1 : ℕ) ≤ 2 ^ κ := Nat.one_le_two_pow
      omega
    have h5 : 2 ^ E * 4 ≤ 2 ^ E * 2 ^ (κ + 2) := Nat.mul_le_mul_left _ h2
    omega
  have hHle : (∑ d ∈ Finset.Icc 1 S, (A' / d + 1)) ≤ A' * (E + κ + 5) := by
    have h1 := harmonic_div_sum_le S A' (E + κ + 2) hSpow
    have h2 : A' * (E + κ + 2 + 1) + 2 * A' = A' * (E + κ + 5) := by ring
    omega
  have hCle : (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A'
      ≤ 2 * b ^ (L - K) * (E + κ + 5) := by
    have h1 : b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))
        ≤ b ^ (L - K) * (2 * (A' * (E + κ + 5))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hHle)
    have h2 : b ^ (L - K) * (2 * (A' * (E + κ + 5)))
        = A' * (2 * b ^ (L - K) * (E + κ + 5)) := by ring
    calc (b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A'
        ≤ (A' * (2 * b ^ (L - K) * (E + κ + 5))) / A' := by
          apply Nat.div_le_div_right
          omega
      _ = 2 * b ^ (L - K) * (E + κ + 5) := Nat.mul_div_cancel_left _ hApos
  have hNle : x + y * A' + L + 2 ≤ A' * A' + L + 2 := by
    have h1 : y * A' ≤ (A' - 1) * A' := Nat.mul_le_mul_right A' (by omega)
    have h3 : (A' - 1) * A' = A' * A' - A' := Nat.sub_one_mul A' A'
    have h4 : A' ≤ A' * A' := Nat.le_mul_of_pos_left A' hApos
    omega
  have hhalf1 : 2 * (q' * (2 * b ^ (L - K) * (E + κ + 5))) ≤ b ^ L := by
    have h1 : 2 * (q' * (2 * b ^ (L - K) * (E + κ + 5)))
        = (4 * q' * (E + κ + 5)) * b ^ (L - K) := by ring
    have h2 : (4 * q' * (E + κ + 5)) * b ^ (L - K) ≤ b ^ K * b ^ (L - K) :=
      Nat.mul_le_mul_right _ hparamA
    have h3 : b ^ K * b ^ (L - K) = b ^ (K + (L - K)) := (pow_add b K (L - K)).symm
    have h4 : K + (L - K) = L := Nat.add_sub_cancel' hKL
    rw [h1]
    rw [h3, h4] at h2
    exact h2
  have hhalf2 : 2 * (q' * (A' * A' + L + 2)) < b ^ L := by
    have hA2 : A' * A' ≤ 2 ^ (2 * E) := by
      have h1 : A' * A' ≤ 2 ^ E * 2 ^ E := Nat.mul_le_mul hA2E hA2E
      have h2 : (2 : ℕ) ^ E * 2 ^ E = 2 ^ (2 * E) := by
        rw [← pow_add]; congr 1; ring
      omega
    have hsum : A' * A' + L + 2 ≤ 2 ^ (2 * E + κ + 2) := by
      have hex : (2 : ℕ) ^ (2 * E + κ + 2) = 2 ^ (2 * E) * 2 ^ κ * 4 := by
        rw [pow_add, pow_add]; norm_num
      have hac1 : (2 : ℕ) ^ (2 * E) ≤ 2 ^ (2 * E) * 2 ^ κ :=
        Nat.le_mul_of_pos_right _ (by positivity)
      have hac2 : (2 : ℕ) ^ κ ≤ 2 ^ (2 * E) * 2 ^ κ :=
        Nat.le_mul_of_pos_left _ (by positivity)
      omega
    have h2q : 2 * q' ≤ 2 ^ (q' + 1) := by
      have h1 : q' < 2 ^ q' := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (q' + 1) = 2 ^ q' * 2 := pow_succ 2 q'
      omega
    have hmul : 2 * (q' * (A' * A' + L + 2)) ≤ 2 ^ (q' + 1) * 2 ^ (2 * E + κ + 2) := by
      have h1 : 2 * (q' * (A' * A' + L + 2)) = (2 * q') * (A' * A' + L + 2) := by ring
      rw [h1]
      exact Nat.mul_le_mul h2q hsum
    have hexp : (2 : ℕ) ^ (q' + 1) * 2 ^ (2 * E + κ + 2) = 2 ^ (2 * E + κ + q' + 3) := by
      rw [← pow_add]; congr 1; ring
    have hlt : (2 : ℕ) ^ (2 * E + κ + q' + 3) * 2 ≤ 2 ^ L := by
      have h1 : (2 : ℕ) ^ (2 * E + κ + q' + 3) * 2 = 2 ^ (2 * E + κ + q' + 4) :=
        (pow_succ 2 _).symm
      rw [h1]
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    have ht1 : (1 : ℕ) ≤ 2 ^ (2 * E + κ + q' + 3) := Nat.one_le_two_pow
    have h2L : (2 : ℕ) ^ L ≤ b ^ L := Nat.pow_le_pow_left hb L
    omega
  have hqC : q' * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A')
      ≤ q' * (2 * b ^ (L - K) * (E + κ + 5)) := Nat.mul_le_mul_left q' hCle
  have hqN : q' * (x + y * A' + L + 2) ≤ q' * (A' * A' + L + 2) :=
    Nat.mul_le_mul_left q' hNle
  have hfin : q * (W * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A')
        + W * (x + y * A' + L + 2))
      = q' * ((b ^ (L - K) * (2 * ∑ d ∈ Finset.Icc 1 S, (A' / d + 1))) / A')
        + q' * (x + y * A' + L + 2) := by
    rw [hq'def]
    ring
  omega

/-- **The wave-13 dichotomy, Lambert form** — UNCONDITIONAL, mixed signs
allowed: for every base `b ≥ 2` and EVERY `m`-periodic signed integer
weight `w`, the signed weighted Erdős series `∑_a w(a)/(b^a − 1)` is
irrational OR base-`b` terminating (`b^k·x ∈ ℤ` for some `k`).  This
discharges the entire protected-certificate-supply obligation except on
the terminating escape set; excluding that escape for general periodic
signed weights is the remaining open frontier and is NOT claimed. -/
theorem irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n) :
    Irrational (intWeightedErdosSeries b w)
      ∨ ∃ (k : ℕ) (z : ℤ), (b : ℝ) ^ k * intWeightedErdosSeries b w = (z : ℝ) := by
  set W : ℕ := (Finset.range (0 + m)).sup (fun a => (w a).natAbs) + 1 with hWdef
  have hbound : ∀ x : ℕ, (w x).natAbs ≤ W := by
    intro x
    have h := eventually_periodic_weight_bound (fun a => (w a).natAbs) m 0 hm
      (fun k _ => by show (w (k + m)).natAbs = (w k).natAbs; rw [hper k]) x
    omega
  have hWpos : 0 < W := by omega
  rw [intWeightedErdosSeries_eq_tsum_intWeightedCoeff b W w hb hWpos hbound]
  exact int_coeff_series_irrational_or_bpow_mul_eq_intCast_of_full_block_certificates
    b W (intWeightedCoeff w) hb
    (fun n => natAbs_intWeightedCoeff_le_mul_self w W n hbound)
    (exists_full_block_certificates_intWeightedCoeff_periodic b m W w hb hm hper
      hbound hWpos)

/-- **Non-termination socket.**  A periodic signed weight whose series
never terminates in base `b` has an irrational series.  Compared with
the wave-12 protected-block socket this hypothesis is a single
condition on the VALUE rather than a certificate family at every
precision — the residual analytic content of the mixed-sign
Luca–Tachiya statement lives entirely inside it. -/
theorem irrational_intWeightedErdosSeries_periodic_of_bpow_mul_ne_intCast
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hnt : ∀ (k : ℕ) (z : ℤ), (b : ℝ) ^ k * intWeightedErdosSeries b w ≠ (z : ℝ)) :
    Irrational (intWeightedErdosSeries b w) := by
  rcases irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic
    b m w hb hm hper with h | h
  · exact h
  · obtain ⟨k, z, hz⟩ := h
    exact absurd hz (hnt k z)

/-- The period-4 sign weight `1, 0, −1, 0` — the nontrivial sign
pattern mod 4 as an integer weight. -/
def periodFourSignWeight : ℕ → ℤ := fun a =>
  if a % 4 = 1 then 1 else if a % 4 = 3 then -1 else 0

/-- **The residue-selection obstruction, machine-checked.**  For the
period-4 sign weight the divisor involution `d ↦ n/d` pairs opposite
weights on every `n ≡ 3 mod 4` (the product of the two residues is
`3 mod 4`, so exactly one factor is `1` and the other `3`), hence the
signed coefficient vanishes IDENTICALLY on that residue class.  Zero
sets of periodic signed coefficients can therefore contain full
arithmetic progressions: no residue-blind selection over a cofactor
progression can force a nonzero protected residue for every periodic
signed weight, which is why wave 13 lands a dichotomy rather than a
protected-certificate supply. -/
theorem intWeightedCoeff_periodFourSignWeight_eq_zero_of_mod_four_eq_three
    (n : ℕ) (hn : n % 4 = 3) :
    intWeightedCoeff periodFourSignWeight n = 0 := by
  have hneg : ∀ d ∈ n.divisors, periodFourSignWeight (n / d)
      = - periodFourSignWeight d := by
    intro d hd
    obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd
    obtain ⟨e, rfl⟩ := hdvd
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at hn
    have hdiv : d * e / d = e := Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hd0)
    rw [hdiv]
    have hmod : d % 4 * (e % 4) % 4 = 3 := by
      rw [← Nat.mul_mod]
      exact hn
    have hDd : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
    have hEe : e % 4 = 0 ∨ e % 4 = 1 ∨ e % 4 = 2 ∨ e % 4 = 3 := by omega
    simp only [periodFourSignWeight]
    rcases hDd with h1 | h1 | h1 | h1 <;> rcases hEe with h2 | h2 | h2 | h2 <;>
      rw [h1, h2] at hmod <;> simp only [h1, h2] <;> revert hmod <;> decide
  have h2 : ∑ d ∈ n.divisors, periodFourSignWeight (n / d)
      = - intWeightedCoeff periodFourSignWeight n := by
    calc ∑ d ∈ n.divisors, periodFourSignWeight (n / d)
        = ∑ d ∈ n.divisors, - periodFourSignWeight d := Finset.sum_congr rfl hneg
      _ = - ∑ d ∈ n.divisors, periodFourSignWeight d := by
          rw [← Finset.sum_neg_distrib]
      _ = - intWeightedCoeff periodFourSignWeight n := rfl
  have h4 : intWeightedCoeff periodFourSignWeight n
      = ∑ d ∈ n.divisors, periodFourSignWeight (n / d) := by
    unfold intWeightedCoeff
    exact (Nat.sum_div_divisors n periodFourSignWeight).symm
  have h5 := h4.trans h2
  omega

/-! ## Signed-coefficient calculus: closing the terminating escape for
coefficient-nonnegative weights (wave 13b)

The wave-13 dichotomy leaves exactly one escape: the series could be a
base-`b` terminating rational `z₀/b^k`.  For weights whose divisor
COEFFICIENTS are nonnegative (the weights themselves may be mixed-sign
— the period-4 character-type weights are the motivating class), that
escape closes unconditionally:

* a terminating value keeps every dilation `b^N·x` either exactly an
  integer or at distance `≥ 1/b^k` from `ℤ`, so a full-block
  certificate at precision `q = b^k + 1` forces `b^N·x` to BE the
  integer it approximates;
* an exact integer value makes the post-block tail an integer in
  `[0, 1)`, hence ZERO — and a vanishing sum of nonnegative terms
  vanishes term by term, so EVERY coefficient beyond the first block
  is zero;
* that contradicts "infinitely many nonzero coefficients".

Result: `∑ w(a)/(b^a − 1)` is irrational for every `m`-periodic signed
weight with nonnegative (or nonpositive) divisor coefficients that do
not eventually vanish.  This strictly extends the wave-11 nonnegative
WEIGHT theorem: coefficient-nonnegativity tolerates sign-mixed weights.
The fully mixed-sign case (coefficients of both signs) remains open and
is NOT claimed. -/

/-- **Terminating values snap to integers.**  If `b^k·X` is the integer
`z₀`, then any dilation `b^N·X` that lies within `1/b^k` of an integer
`z` EQUALS `z`: the difference is an integer over `b^k` of absolute
value below one. -/
theorem bpow_mul_eq_intCast_of_abs_sub_lt_inv_bpow
    (b k N : ℕ) (X : ℝ) (z₀ z : ℤ) (hb : 2 ≤ b)
    (hterm : (b : ℝ) ^ k * X = (z₀ : ℝ))
    (hlt : |(b : ℝ) ^ N * X - (z : ℝ)| < 1 / (b : ℝ) ^ k) :
    (b : ℝ) ^ N * X = (z : ℝ) := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    have h2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hbk_pos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  have hX : X = (z₀ : ℝ) / (b : ℝ) ^ k := by
    rw [eq_div_iff (ne_of_gt hbk_pos), mul_comm]
    exact hterm
  have hkey : (b : ℝ) ^ N * X - (z : ℝ)
      = ((z₀ * (b : ℤ) ^ N - z * (b : ℤ) ^ k : ℤ) : ℝ) / (b : ℝ) ^ k := by
    rw [hX]
    field_simp
    push_cast
    ring
  have habs : |((z₀ * (b : ℤ) ^ N - z * (b : ℤ) ^ k : ℤ) : ℝ)| < 1 := by
    have h2 := hlt
    rw [hkey, abs_div, abs_of_pos hbk_pos,
      div_lt_div_iff₀ hbk_pos hbk_pos] at h2
    exact lt_of_mul_lt_mul_right h2 hbk_pos.le
  have hD : z₀ * (b : ℤ) ^ N - z * (b : ℤ) ^ k = 0 := by
    have h3 : |z₀ * (b : ℤ) ^ N - z * (b : ℤ) ^ k| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp h3
  have hfin : (b : ℝ) ^ N * X - (z : ℝ) = 0 := by
    rw [hkey, hD, Int.cast_zero, zero_div]
  exact sub_eq_zero.mp hfin

set_option maxHeartbeats 800000 in
/-- **Exact integer values force the post-block tail to vanish term by
term.**  Under a full-block certificate, if additionally every positive
index carries a NONNEGATIVE coefficient and the `b^N`-dilated series is
exactly the integer `z`, then every coefficient beyond the first block
is zero: the post-block tail is an integer in `[0, 1)`, hence zero, and
a zero sum of nonnegative terms vanishes pointwise. -/
theorem coeff_eq_zero_of_full_block_certificate_of_bpow_mul_eq_intCast
    (b q N K L C G : ℕ) (c : ℕ → ℤ) (z : ℤ)
    (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (habs : ∀ m : ℕ, (c m).natAbs ≤ G * m)
    (hc0 : ∀ m : ℕ, 0 < m → 0 ≤ c m)
    (hblock : ∀ r ∈ Finset.Icc 1 K, ((b : ℤ)) ^ r ∣ c (N + r))
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, (c (N + r)).natAbs * b ^ (L - r) ≤ C)
    (hhigh : q * (C + G * (N + L + 2)) < b ^ L)
    (hint : (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
      = (z : ℝ)) :
    ∀ n : ℕ, N + K < n → c n = 0 := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hbZ : (b : ℤ) ≠ 0 := by
    have h0b : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
    omega
  obtain ⟨z₀, hz₀⟩ := bpow_mul_int_coeff_series_eq_int_add_tail b N G c hb habs
  have hfsum : Summable
      (fun r : ℕ => ((c (N + r + 1) : ℤ) : ℝ) / (b : ℝ) ^ (r + 1)) :=
    summable_int_coeff_shift_tail b N G c hb habs
  have hfarsum : Summable
      (fun t : ℕ => ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)) :=
    (summable_nat_add_iff L).mpr hfsum
  have hsplitL : (∑' r : ℕ, ((c (N + r + 1) : ℤ) : ℝ) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  have hsplitK : (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  have hz₁ : ((∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1) : ℤ) : ℝ)
      = ∑ i ∈ Finset.range K, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1) := by
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp hi
    have hdvd : ((b : ℤ)) ^ (i + 1) ∣ c (N + i + 1) :=
      hblock (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [int_cast_div_real (c (N + i + 1)) ((b : ℤ) ^ (i + 1)) hdvd
      (pow_ne_zero (i + 1) hbZ)]
    push_cast
    rfl
  have hdiff : (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m + 1))
      - ((z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1) : ℤ) : ℝ)
      = (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) := by
    rw [hz₀, hsplitL, hsplitK]
    push_cast
    rw [← hz₁]
    push_cast
    ring
  -- nonnegativity of both tail pieces
  have hmid_nonneg : (0 : ℝ)
      ≤ ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1) := by
    refine Finset.sum_nonneg fun i _ => ?_
    have hc := hc0 (N + i + 1) (by omega)
    have hcR : (0 : ℝ) ≤ ((c (N + i + 1) : ℤ) : ℝ) := by exact_mod_cast hc
    positivity
  have hfar_term_nonneg : ∀ t : ℕ,
      (0 : ℝ) ≤ ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) := by
    intro t
    have hc := hc0 (N + (t + L) + 1) (by omega)
    have hcR : (0 : ℝ) ≤ ((c (N + (t + L) + 1) : ℤ) : ℝ) := by exact_mod_cast hc
    positivity
  have hfar_nonneg : (0 : ℝ)
      ≤ ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) :=
    tsum_nonneg hfar_term_nonneg
  -- the deviation is an integer in [0, 1), hence zero
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  have hmid_abs : |∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1)|
      ≤ (C : ℝ) / (b : ℝ) ^ L := by
    have htri : |∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1)|
        ≤ ∑ i ∈ Finset.Ico K L,
            (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _)
        (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [abs_div, abs_of_pos (show (0 : ℝ) < (b : ℝ) ^ (i + 1) by positivity),
        abs_intCast_eq_natAbs_cast]
    refine le_trans htri ?_
    have hterm : ∀ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1)
          = (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
      intro i hi
      obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
      have hb1 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
      have hbL' : ((b : ℝ) ^ L) ≠ 0 := by positivity
      have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (L - (i + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [div_eq_div_iff hb1 hbL']
      push_cast
      rw [hsplit]
      ring
    have hreindex : (∑ i ∈ Finset.Ico K L, (c (N + i + 1)).natAbs * b ^ (L - (i + 1)))
        = ∑ r ∈ Finset.Icc (K + 1) L, (c (N + r)).natAbs * b ^ (L - r) := by
      have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
        ext a'
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      have hn : L + 1 - (K + 1) = L - K := by omega
      rw [hn]
      refine Finset.sum_congr rfl fun j' hj' => ?_
      have h1 : N + (K + j') + 1 = N + (K + 1 + j') := by omega
      have h2 : L - (K + j' + 1) = L - (K + 1 + j') := by omega
      rw [h1, h2]
    have hsum_eq : (∑ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    have hnum : (∑ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ)) ≤ (C : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hreindex.trans_le hmiddle
    calc (∑ i ∈ Finset.Ico K L,
        (((c (N + i + 1)).natAbs : ℕ) : ℝ) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            (((c (N + i + 1)).natAbs * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L :=
          hsum_eq
      _ ≤ (C : ℝ) / (b : ℝ) ^ L := by gcongr
  have hfar_eq : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, ((c (N + L + 1 + t) : ℤ) : ℝ) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar_abs : |∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)|
      ≤ ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact int_coeff_far_tail_abs_le b N L G c hb habs
  have hsum_lt : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
      + (∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)) < 1 := by
    have h1 : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + (∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1))
        ≤ (C : ℝ) / (b : ℝ) ^ L + ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
      have h1a := le_abs_self (∑ i ∈ Finset.Ico K L,
        ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
      have h1b := le_abs_self (∑' t : ℕ,
        ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1))
      have h1c := le_trans h1a hmid_abs
      have h1d := le_trans h1b hfar_abs
      linarith
    have h2 : (C : ℝ) / (b : ℝ) ^ L + ((G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L
        = ((C + G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L := by
      rw [← add_div]
      push_cast
      ring
    have h3 : ((C + G * (N + L + 2) : ℕ) : ℝ) / (b : ℝ) ^ L < 1 / (q : ℝ) := by
      rw [div_lt_div_iff₀ hbL hq', one_mul]
      have hc : (q : ℝ) * ((C + G * (N + L + 2) : ℕ) : ℝ) < (b : ℝ) ^ L := by
        exact_mod_cast hhigh
      calc ((C + G * (N + L + 2) : ℕ) : ℝ) * (q : ℝ)
          = (q : ℝ) * ((C + G * (N + L + 2) : ℕ) : ℝ) := mul_comm _ _
        _ < (b : ℝ) ^ L := hc
    have h4 : (1 : ℝ) / (q : ℝ) ≤ 1 := by
      rw [div_le_one hq']
      exact_mod_cast hq
    linarith
  -- the deviation equals the integer z - (z₀ + block sum)
  have hDeq : ((z - (z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1)) : ℤ) : ℝ)
      = (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) := by
    rw [← hdiff, hint]
    push_cast
    ring
  have hD0 : z - (z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1)) = 0 := by
    have hge : (0 : ℝ)
        ≤ ((z - (z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1)) : ℤ) : ℝ) := by
      rw [hDeq]
      linarith
    have hlt1 : ((z - (z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1)) : ℤ) : ℝ)
        < 1 := by
      rw [hDeq]
      exact hsum_lt
    have hgeZ : (0 : ℤ) ≤ z - (z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1)) := by
      exact_mod_cast hge
    have hltZ : z - (z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1)) < 1 := by
      exact_mod_cast hlt1
    have habsD : |z - (z₀ + ∑ i ∈ Finset.range K, c (N + i + 1) / (b : ℤ) ^ (i + 1))| < 1 := by
      rw [abs_of_nonneg hgeZ]
      exact hltZ
    exact Int.abs_lt_one_iff.mp habsD
  -- so the nonnegative tail pieces sum to zero, hence vanish separately
  have hzero : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1))
      + (∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)) = 0 := by
    have h := hDeq
    rw [hD0, Int.cast_zero] at h
    exact h.symm
  have hmid0 : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1)) = 0 := by
    linarith
  have hfar0 : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1)) = 0 := by
    linarith
  have hmid_terms : ∀ i ∈ Finset.Ico K L,
      ((c (N + i + 1) : ℤ) : ℝ) / (b : ℝ) ^ (i + 1) = 0 := by
    intro i hi
    refine (Finset.sum_eq_zero_iff_of_nonneg fun j _ => ?_).mp hmid0 i hi
    have hc := hc0 (N + j + 1) (by omega)
    have hcR : (0 : ℝ) ≤ ((c (N + j + 1) : ℤ) : ℝ) := by exact_mod_cast hc
    positivity
  have hfar_terms : ∀ t : ℕ,
      ((c (N + (t + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t + L) + 1) = 0 := by
    intro t
    have hsplit2 : (∑' t' : ℕ, ((c (N + (t' + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((t' + L) + 1))
        = (∑ i ∈ Finset.range (t + 1),
            ((c (N + (i + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((i + L) + 1))
          + ∑' j : ℕ, ((c (N + (j + (t + 1) + L) + 1) : ℤ) : ℝ)
              / (b : ℝ) ^ ((j + (t + 1) + L) + 1) :=
      (Summable.sum_add_tsum_nat_add (t + 1) hfarsum).symm
    have htail0 : (0 : ℝ) ≤ ∑' j : ℕ, ((c (N + (j + (t + 1) + L) + 1) : ℤ) : ℝ)
        / (b : ℝ) ^ ((j + (t + 1) + L) + 1) :=
      tsum_nonneg fun j => hfar_term_nonneg (j + (t + 1))
    have hhead0 : (∑ i ∈ Finset.range (t + 1),
        ((c (N + (i + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((i + L) + 1)) = 0 := by
      have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (t + 1),
          ((c (N + (i + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((i + L) + 1) :=
        Finset.sum_nonneg fun i _ => hfar_term_nonneg i
      have h3 := hfar0
      rw [hsplit2] at h3
      have hAeq : (∑ i ∈ Finset.range (t + 1),
          ((c (N + (i + L) + 1) : ℤ) : ℝ) / (b : ℝ) ^ ((i + L) + 1))
          = -(∑' j : ℕ, ((c (N + (j + (t + 1) + L) + 1) : ℤ) : ℝ)
              / (b : ℝ) ^ ((j + (t + 1) + L) + 1)) :=
        eq_neg_of_add_eq_zero_left h3
      exact le_antisymm (hAeq.trans_le (neg_nonpos.mpr htail0)) hnn
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hfar_term_nonneg i).mp hhead0
      t (Finset.mem_range.mpr (by omega))
  -- extract pointwise vanishing of the coefficients
  intro n hn
  rcases le_or_gt n (N + L) with hcase | hcase
  · have hi : n - N - 1 ∈ Finset.Ico K L := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have h := hmid_terms _ hi
    rw [show N + (n - N - 1) + 1 = n from by omega] at h
    have hbp : ((b : ℝ) ^ (n - N - 1 + 1)) ≠ 0 := by positivity
    have hnum := (div_eq_zero_iff.mp h).resolve_right hbp
    exact_mod_cast hnum
  · have h := hfar_terms (n - N - L - 1)
    rw [show N + (n - N - L - 1 + L) + 1 = n from by omega] at h
    have hbp : ((b : ℝ) ^ (n - N - L - 1 + L + 1)) ≠ 0 := by positivity
    have hnum := (div_eq_zero_iff.mp h).resolve_right hbp
    exact_mod_cast hnum

/-- **Coefficient-nonnegative periodic irrationality — the terminating
escape closes.**  For every base `b ≥ 2` and every `m`-periodic signed
weight `w` whose divisor coefficients are all nonnegative and do not
eventually vanish, `∑ w(a)/(b^a − 1)` is IRRATIONAL — unconditionally.
The weight itself may be mixed-sign; only the coefficients are
one-sided.  Proof: the wave-13 dichotomy leaves only the terminating
branch `b^k·x = z₀`; a full-block certificate at precision `b^k + 1`
snaps some dilation onto an exact integer, which forces every
coefficient beyond the first block to vanish — contradiction. -/
theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → 0 ≤ intWeightedCoeff w n)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w) := by
  rcases irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic b m w hb hm hper
    with h | ⟨k, z₀, hk⟩
  · exact h
  · exfalso
    set W : ℕ := (Finset.range (0 + m)).sup (fun a => (w a).natAbs) + 1 with hWdef
    have hbound : ∀ x : ℕ, (w x).natAbs ≤ W := by
      intro x
      have h := eventually_periodic_weight_bound (fun a => (w a).natAbs) m 0 hm
        (fun j _ => by show (w (j + m)).natAbs = (w j).natAbs; rw [hper j]) x
      omega
    have hWpos : 0 < W := by omega
    rw [intWeightedErdosSeries_eq_tsum_intWeightedCoeff b W w hb hWpos hbound] at hk
    set q : ℕ := b ^ k + 1 with hqdef
    have hq : 0 < q := by rw [hqdef]; positivity
    obtain ⟨N, K, L, C, hKL, hblock, hmiddle, hhigh⟩ :=
      exists_full_block_certificates_intWeightedCoeff_periodic b m W w hb hm hper
        hbound hWpos q hq
    obtain ⟨z, hz⟩ := near_int_of_int_coeff_full_block_certificate
      b q N K L C W (intWeightedCoeff w) hb hq hKL
      (fun n => natAbs_intWeightedCoeff_le_mul_self w W n hbound) hblock hmiddle hhigh
    have hqR : (1 : ℝ) / (q : ℝ) < 1 / (b : ℝ) ^ k := by
      have hbk_pos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      have hq_gt : ((b : ℝ)) ^ k < (q : ℝ) := by
        rw [hqdef]
        push_cast
        linarith
      exact one_div_lt_one_div_of_lt hbk_pos hq_gt
    have heq := bpow_mul_eq_intCast_of_abs_sub_lt_inv_bpow b k N
      (∑' m' : ℕ, ((intWeightedCoeff w (m' + 1) : ℤ) : ℝ) / (b : ℝ) ^ (m' + 1))
      z₀ z hb hk (lt_trans hz hqR)
    have hvanish := coeff_eq_zero_of_full_block_certificate_of_bpow_mul_eq_intCast
      b q N K L C W (intWeightedCoeff w) z hb hq hKL
      (fun n => natAbs_intWeightedCoeff_le_mul_self w W n hbound) hc0
      hblock hmiddle hhigh heq
    obtain ⟨n, hn, hne'⟩ := hne (N + K)
    exact hne' (hvanish n hn)

/-- Negating the weight negates the signed coefficient. -/
theorem intWeightedCoeff_neg (w : ℕ → ℤ) (n : ℕ) :
    intWeightedCoeff (fun a => -(w a)) n = - intWeightedCoeff w n := by
  unfold intWeightedCoeff
  rw [← Finset.sum_neg_distrib]

/-- Negating the weight negates the signed weighted Erdős series. -/
theorem intWeightedErdosSeries_neg (b : ℕ) (w : ℕ → ℤ) :
    intWeightedErdosSeries b (fun a => -(w a)) = - intWeightedErdosSeries b w := by
  unfold intWeightedErdosSeries
  rw [← tsum_neg]
  refine tsum_congr fun a => ?_
  push_cast
  ring

/-- **Coefficient-nonpositive periodic irrationality** — the mirror of
the nonnegative theorem, by negating the weight. -/
theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → intWeightedCoeff w n ≤ 0)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w) := by
  have hneg := irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero
    b m (fun a => -(w a)) hb hm
    (fun n => by show -(w (n + m)) = -(w n); rw [hper n])
    (fun n hn => by
      rw [intWeightedCoeff_neg]
      have := hc0 n hn
      omega)
    (fun N => by
      obtain ⟨n, hn, hne'⟩ := hne N
      exact ⟨n, hn, by rw [intWeightedCoeff_neg]; exact neg_ne_zero.mpr hne'⟩)
  rw [intWeightedErdosSeries_neg] at hneg
  have h2 := hneg.neg
  rwa [neg_neg] at h2

/-! ## Erdős #249 lane: totient coefficient sockets and first-block supply (wave 14)

Erdős #249 asks whether `∑_{n≥1} φ(n)/2^n` is irrational.  It is the
coefficient-series instance `b = 2`, `c = Nat.totient` of the wave-8
engine: growth `φ(m) ≤ m` is `Nat.totient_le`, tail positivity is
`Nat.totient_pos`, and both the digitwise and the carry-aware consumers
apply verbatim.  This lane lands the two unconditional halves that exist
today and names the missing third:

* **Hinge (landed):** every odd prime divisor `p` of `n` contributes the
  even factor `p - 1` to Euler's product, so a block of `r` distinct odd
  prime divisors forces `2^r ∣ φ(n)`.  No exact valuation is needed.
* **First-block supply (landed):** the exact-valuation CRT progression at
  base `2`, prime floor `2` gives `2^r ∣ φ(x + y·A + r)` along a full
  arithmetic progression.
* **Certificate supply (MISSING — the open content of #249):** the `τ`
  middle window closed because divisor counts average polylogarithmically
  along the frame, so the pigeonhole selector
  (`selected_weighted_middle_of_supported_frame`) crushes the middle mass
  far below `N`.  `φ` has linear average: any middle window after a
  depth-`K` first block carries mass on the order of `N·2^(L-K)`, so the
  height inequality `q·(C + N + L + 2) < 2^L` forces roughly `q·N < 2^K`.
  But every window-local route to `2^r ∣ φ(N+r)` for all `r ≤ K` costs a
  CRT modulus of size `2^Ω(K²)` — `r` odd primes per slot here, or one
  prime `≡ 1 (mod 2^r)` per slot on Linnik-type input — hence
  `N ≥ 2^Ω(K²) ≫ 2^K` and the height inequality cannot close; emptying
  the middle (`K = L`) meets the same wall.  Producing certificates
  therefore needs input beyond window-local divisibility forcing (for
  example counting or equidistribution of the carry sum
  `∑_{r≤K} φ(N+r)·2^(K-r) mod 2^K` at height `N ≈ 2^K/q`), which is not
  claimed here.  Runner non-claims: `not_erdos_249_solution`,
  `not_totient_block_certificate_supply`,
  `not_totient_carry_certificate_supply`. -/

/-- **Totient hinge for the first block.**  A block of distinct odd prime
divisors of `n` forces `2`-adic depth in `φ(n)`: each odd prime divisor
`p` contributes the even factor `p - 1` to Euler's product
`φ(n) = ∏_p p^(v_p(n)-1)·(p-1)`, so `2^|P| ∣ φ(n)`.  Unlike the `τ`
hinge (`bpow_dvd_card_divisors_of_exact_prime_block`), no exact valuation
is needed — divisibility alone suffices, because `p - 1` enters the
product at every positive valuation. -/
theorem two_pow_card_dvd_totient_of_odd_prime_block
    (n : ℕ) (hn : n ≠ 0) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, p ≠ 2)
    (hdvd : ∀ p ∈ P, p ∣ n) :
    2 ^ P.card ∣ Nat.totient n := by
  have hsub : P ⊆ n.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨hprime p hp, hdvd p hp, hn⟩
  have heven : ∀ p ∈ P, 2 ∣ p ^ (n.factorization p - 1) * (p - 1) := fun p hp =>
    Dvd.dvd.mul_left (((hprime p hp).even_sub_one (hodd p hp)).two_dvd) _
  have hchain : 2 ^ P.card
      ∣ ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) := by
    calc (2 : ℕ) ^ P.card = ∏ _p ∈ P, 2 := by rw [Finset.prod_const]
      _ ∣ ∏ p ∈ P, p ^ (n.factorization p - 1) * (p - 1) :=
          Finset.prod_dvd_prod_of_dvd _ _ heven
      _ ∣ ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) :=
          Finset.prod_dvd_prod_of_subset P n.primeFactors _ hsub
  rw [Nat.totient_eq_prod_factorization hn]
  exact hchain

/-- **Totient first-block divisibility along a full arithmetic
progression.**  For every window length `K` there are `x` and a positive
modulus `A` with `2^r ∣ φ(x + y·A + r)` for every `y` and every
`r ∈ [1, K]` — the first-block half of an Erdős #249 certificate,
produced by specialising the exact-valuation CRT progression to base `2`
with prime floor `2`: every construction prime is odd, and slot `r`
carries `r` of them. -/
theorem exists_totient_first_block_divisibility_progression (K : ℕ) :
    ∃ x A : ℕ, 0 < A ∧
      ∀ y : ℕ, ∀ r ∈ Finset.Icc 1 K, 2 ^ r ∣ Nat.totient (x + y * A + r) := by
  obtain ⟨x, A, hA, hblocks⟩ := exists_exact_valuation_progression 2 2 (le_refl 2) K
  refine ⟨x, A, hA, fun y r hr => ?_⟩
  obtain ⟨P, hcard, hprime, hgt, hval⟩ := hblocks r hr
  have hne : x + y * A + r ≠ 0 := by
    have := (Finset.mem_Icc.mp hr).1
    omega
  have hdvd := two_pow_card_dvd_totient_of_odd_prime_block (x + y * A + r) hne P
    hprime
    (fun p hp => by have := hgt p hp; omega)
    (fun p hp => Nat.dvd_of_factorization_pos (by rw [hval y p hp]; omega))
  rwa [hcard] at hdvd

/-- **Index alignment for the totient series.**  The `n`-indexed series
`∑_{n≥0} φ(n)/b^n` (the Erdős #249 statement shape, with vanishing
`n = 0` term) equals the kernel-convention shifted series
`∑_m φ(m+1)/b^(m+1)`. -/
theorem tsum_totient_div_pow_eq_shifted (b : ℕ) (hb : 2 ≤ b) :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (b : ℝ) ^ n)
      = ∑' m : ℕ, ((Nat.totient (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1) := by
  have hshift : Summable
      (fun m : ℕ => ((Nat.totient (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) :=
    summable_coeff_term b Nat.totient hb Nat.totient_le
  have hsum : Summable (fun n : ℕ => ((Nat.totient n : ℝ)) / (b : ℝ) ^ n) :=
    (summable_nat_add_iff 1).mp hshift
  rw [← Summable.sum_add_tsum_nat_add 1 hsum]
  simp

/-- **Erdős #249 digitwise socket.**  If totient block certificates exist
at every precision — first-block divisibility `2^r ∣ φ(N+r)`, weighted
middle window `≤ C`, and the height inequality `q·(C+N+L+2) < 2^L` —
then `∑_{n≥1} φ(n)/2^n` is irrational.  Growth is `Nat.totient_le`, tail
positivity is `Nat.totient_pos`; certificate SUPPLY is the open content
of #249 and is NOT claimed. -/
theorem irrational_tsum_totient_div_pow_two_of_totient_block_certificates
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, 2 ^ r ∣ Nat.totient (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, Nat.totient (N + r) * 2 ^ (L - r) ≤ C) ∧
        q * (C + (N + L + 2)) < 2 ^ L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) := by
  have h := irrational_coeff_series_of_weighted_coeff_block_certificates 2 Nat.totient
    (by norm_num) Nat.totient_le ?_
  · have hbridge := tsum_totient_div_pow_eq_shifted 2 (by norm_num)
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hcast] at h hbridge
    rwa [hbridge]
  · intro q hq
    obtain ⟨N, K, L, C, hKL, hblock, hmiddle, harith⟩ := hcert q hq
    exact ⟨N, K, L, C, hKL, hblock, hmiddle,
      ⟨0, Nat.totient_pos.mpr (by omega)⟩, harith⟩

/-- **Erdős #249 carry-aware socket.**  Like the digitwise socket, but the
first block is certified in aggregate: `2^K` divides the carry sum
`∑_{r≤K} φ(N+r)·2^(K-r)`.  This is the certificate shape a counting or
equidistribution supply would feed — one congruence condition mod `2^K`
instead of `K` slotwise divisibilities.  Certificate SUPPLY is NOT
claimed. -/
theorem irrational_tsum_totient_div_pow_two_of_totient_carry_certificates
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (2 ^ K ∣ ∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, Nat.totient (N + r) * 2 ^ (L - r) ≤ C) ∧
        q * (C + (N + L + 2)) < 2 ^ L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) := by
  have h := irrational_coeff_series_of_weighted_coeff_carry_block_certificates 2
    Nat.totient (by norm_num) Nat.totient_le ?_
  · have hbridge := tsum_totient_div_pow_eq_shifted 2 (by norm_num)
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hcast] at h hbridge
    rwa [hbridge]
  · intro q hq
    obtain ⟨N, K, L, C, hKL, hcarry, hmiddle, harith⟩ := hcert q hq
    exact ⟨N, K, L, C, hKL, hcarry, hmiddle,
      ⟨0, Nat.totient_pos.mpr (by omega)⟩, harith⟩

/-! ## Erdős #249 lane, wave 15: low-carry residue-band certificates

Wave 14 shaped the carry-aware socket around **exact** first-block
integrality: `2^K ∣ ∑_{r≤K} φ(N+r)·2^(K-r)`.  That demand is an
artefact of the digitwise ancestry, not of the near-integer criterion:
irrationality needs a positive fractional part **below `1/q`**, not a
zero one.  This wave weakens the certificate interface so the first
block may leave the residue `V = carrySum % b^K`, absorbed by the
height inequality `q·(V·b^(L-K) + C + (N+L+2)) < b^L`.  Exact carry is
the `V = 0` special case (machine-checked below via
`irrational_coeff_series_of_carry_via_low_carry`), so the supply target
widens from ONE congruence class mod `2^K` to a band of ≈ `2^K/q`
residues — exponentially wider once `K` exceeds `2·log₂ q`.
Certificate SUPPLY remains the open content of #249 and is NOT claimed:
runner non-claims `not_erdos_249_solution`,
`not_totient_low_carry_certificate_supply`. -/

/-- **Low-carry (residue-band) generic certificate consumer, one-sided.**
Like `near_int_witness_of_weighted_coeff_carry_block_certificate`, but
the first block need not be integral: it may leave the residue
`V = (∑_{r≤K} c(N+r)·b^(K-r)) % b^K`, and the near-integer witness
survives whenever the height inequality absorbs it:
`q·(V·b^(L-K) + C + (N+L+2)) < b^L`.  The integer part of the packed
block is `⌊S₁/b^K⌋`; positivity still comes from the far tail, so a
zero residue loses nothing and a small residue costs only its own
size.  This is the certificate shape the irrationality criterion
actually needs — a band of acceptable residues, not one exact
congruence class. -/
theorem near_int_witness_of_weighted_coeff_low_carry_block_certificate
    (b q N K L C : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C)
    (hpos : ∃ t : ℕ, 0 < c (N + L + 1 + t))
    (harith : q * ((∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r)) % b ^ K
        * b ^ (L - K) + C + (N + L + 2)) < b ^ L) :
    ∃ z : ℤ,
      0 < (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ) ∧
        (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ) < 1 / (q : ℝ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨z₀, hz₀⟩ := bpow_mul_coeff_series_eq_int_add_tail b N c hb hgrowth
  have hfsum : Summable
      (fun r : ℕ => ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1)) :=
    summable_coeff_shift_tail b N c hb hgrowth
  have hfarsum : Summable
      (fun t : ℕ => ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) :=
    (summable_nat_add_iff L).mpr hfsum
  -- split the tail at L
  have hsplitL : (∑' r : ℕ, ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  -- split the finite part at K
  have hsplitK : (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  -- the first block splits as integer part + residue over `b^K`
  set S₁ : ℕ := ∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r) with hS₁def
  set z₁ : ℕ := S₁ / b ^ K with hz₁def
  set V : ℕ := S₁ % b ^ K with hVdef
  have hreidx : S₁ = ∑ i ∈ Finset.range K, c (N + i + 1) * b ^ (K - (i + 1)) := by
    rw [hS₁def]
    have hIccIco : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range]
    have hn : K + 1 - 1 = K := by omega
    rw [hn]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 : N + (1 + i) = N + i + 1 := by omega
    have h2 : K - (1 + i) = K - (i + 1) := by omega
    rw [h1, h2]
  have hblock_eq : ((S₁ : ℕ) : ℝ) / (b : ℝ) ^ K
      = ∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [hreidx]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp hi
    have hsplit : (b : ℝ) ^ K = (b : ℝ) ^ (K - (i + 1)) * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    have hne1 : ((b : ℝ) ^ (K - (i + 1))) ≠ 0 := by positivity
    have hne2 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
    field_simp
  have hdm : b ^ K * z₁ + V = S₁ := by
    rw [hz₁def, hVdef]
    exact Nat.div_add_mod S₁ (b ^ K)
  have hdmR : (b : ℝ) ^ K * ((z₁ : ℕ) : ℝ) + ((V : ℕ) : ℝ) = ((S₁ : ℕ) : ℝ) := by
    exact_mod_cast hdm
  have hblock_split : ((z₁ : ℕ) : ℝ) + ((V : ℕ) : ℝ) / (b : ℝ) ^ K
      = ∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [← hblock_eq, ← hdmR]
    have hbKne : ((b : ℝ) ^ K) ≠ 0 := by positivity
    field_simp
  -- remainder positivity: some coefficient past the window is nonzero
  have hmid_nonneg : (0 : ℝ)
      ≤ ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨t₀, ht₀⟩ := hpos
  have hfar_pos : (0 : ℝ)
      < ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    have hcpos : (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) := by
      have hidx : N + (t₀ + L) + 1 = N + L + 1 + t₀ := by omega
      have h0 : 0 < c (N + (t₀ + L) + 1) := by rw [hidx]; exact ht₀
      exact_mod_cast h0
    have hterm0 : (0 : ℝ)
        < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := by positivity
    calc (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := hterm0
      _ ≤ _ := hfarsum.le_tsum t₀ fun j _ => by positivity
  -- middle window: exact weighted sum over the common denominator b^L
  have hterm : ∀ i ∈ Finset.Ico K L,
      ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1)
        = ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    intro i hi
    obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
    have hb1 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
    have hbL' : ((b : ℝ) ^ L) ≠ 0 := by positivity
    have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (L - (i + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_div_iff hb1 hbL']
    push_cast
    rw [hsplit]
    ring
  have hreindex : (∑ i ∈ Finset.Ico K L, c (N + i + 1) * b ^ (L - (i + 1)))
      = ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) := by
    have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hn : L + 1 - (K + 1) = L - K := by omega
    rw [hn]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : N + (K + j) + 1 = N + (K + 1 + j) := by omega
    have h2 : L - (K + j + 1) = L - (K + 1 + j) := by omega
    rw [h1, h2]
  have hmid : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      ≤ (C : ℝ) / (b : ℝ) ^ L := by
    have hsum_eq : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    have hnum : (∑ i ∈ Finset.Ico K L,
        ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) ≤ (C : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hreindex.trans_le hmiddle
    calc (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := hsum_eq
      _ ≤ (C : ℝ) / (b : ℝ) ^ L := by gcongr
  -- far tail bound, reshaped from the generic far-tail lemma
  have hfar_eq : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact coeff_far_tail_le b N L c hb hgrowth
  -- assemble: the near-integer is z₀ + ⌊S₁/b^K⌋; the residue stays in the remainder
  have hdiff : (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
      - ((z₀ + (z₁ : ℤ) : ℤ) : ℝ)
      = ((V : ℕ) : ℝ) / (b : ℝ) ^ K
        + ((∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
          + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) := by
    rw [hz₀, hsplitL, hsplitK]
    push_cast
    rw [← hblock_split]
    ring
  have hV_nonneg : (0 : ℝ) ≤ ((V : ℕ) : ℝ) / (b : ℝ) ^ K := by positivity
  have hR_pos : (0 : ℝ)
      < ((V : ℕ) : ℝ) / (b : ℝ) ^ K
        + ((∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
          + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) :=
    add_pos_of_nonneg_of_pos hV_nonneg
      (add_pos_of_nonneg_of_pos hmid_nonneg hfar_pos)
  -- the residue over b^K, re-expressed over the common denominator b^L
  have hVK : ((V : ℕ) : ℝ) / (b : ℝ) ^ K
      = ((V * b ^ (L - K) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    have hbKne : ((b : ℝ) ^ K) ≠ 0 := by positivity
    have hbLne : ((b : ℝ) ^ L) ≠ 0 := by positivity
    rw [div_eq_div_iff hbKne hbLne]
    push_cast
    rw [show (b : ℝ) ^ L = (b : ℝ) ^ K * (b : ℝ) ^ (L - K) from by
      rw [← pow_add]; congr 1; omega]
    ring
  refine ⟨z₀ + (z₁ : ℤ), ?_, ?_⟩
  · rw [hdiff]
    exact hR_pos
  · rw [hdiff]
    have hsum_le : ((V : ℕ) : ℝ) / (b : ℝ) ^ K
        + ((∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
          + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
        ≤ ((V * b ^ (L - K) : ℕ) : ℝ) / (b : ℝ) ^ L
          + ((C : ℝ) / (b : ℝ) ^ L + ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L) :=
      add_le_add (le_of_eq hVK) (add_le_add hmid hfar)
    refine lt_of_le_of_lt hsum_le ?_
    have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
    have hc : (q : ℝ) * (((V * b ^ (L - K) : ℕ) : ℝ) + (C : ℝ)
        + ((N + L + 2 : ℕ) : ℝ)) < (b : ℝ) ^ L := by
      exact_mod_cast harith
    rw [← add_div, ← add_div, div_lt_div_iff₀ hbL hq', one_mul]
    calc (((V * b ^ (L - K) : ℕ) : ℝ) + ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ))) * (q : ℝ)
        = (q : ℝ) * (((V * b ^ (L - K) : ℕ) : ℝ) + (C : ℝ)
            + ((N + L + 2 : ℕ) : ℝ)) := by ring
      _ < (b : ℝ) ^ L := hc

/-- **Low-carry coefficient-series irrationality.**  If an arbitrary
coefficient sequence with growth envelope `c m ≤ m` admits a low-carry
residue-band certificate for every precision — residue
`V = carrySum % b^K` absorbed by `q·(V·b^(L-K) + C + (N+L+2)) < b^L` —
then `∑ c(m)/b^m` is irrational.  Strictly weaker demand than
`irrational_coeff_series_of_weighted_coeff_carry_block_certificates`:
the supply problem shrinks from hitting one residue class mod `b^K` to
hitting a low band of ≈ `b^L/q` residues. -/
theorem irrational_coeff_series_of_weighted_coeff_low_carry_block_certificates
    (b : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < c (N + L + 1 + t)) ∧
        q * ((∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r)) % b ^ K
          * b ^ (L - K) + C + (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  apply irrational_of_pow_mul_near_int b
  intro q hq
  obtain ⟨N, K, L, C, hKL, hmiddle, hpos, harith⟩ := hcert q hq
  obtain ⟨z, hz_pos, hz_lt⟩ :=
    near_int_witness_of_weighted_coeff_low_carry_block_certificate
      b q N K L C c hb hq hKL hgrowth hmiddle hpos harith
  refine ⟨N, z, ?_, ?_⟩
  · rw [abs_of_pos hz_pos]
    exact hz_pos
  · rw [abs_of_pos hz_pos]
    exact hz_lt

/-- **The low-carry interface subsumes the exact-carry interface**: the
wave-14 carry-aware closure, re-derived through the residue-band engine.
Machine proof that demanding exact first-block integrality
(`b^K ∣ carrySum`) was overconstraint — a zero residue satisfies the
residue-band height inequality verbatim. -/
theorem irrational_coeff_series_of_carry_via_low_carry
    (b : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < c (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) := by
  refine irrational_coeff_series_of_weighted_coeff_low_carry_block_certificates
    b c hb hgrowth fun q hq => ?_
  obtain ⟨N, K, L, C, hKL, hcarry, hmiddle, hpos, harith⟩ := hcert q hq
  obtain ⟨m, hm⟩ := hcarry
  have hV0 : (∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r)) % b ^ K = 0 := by
    rw [hm]
    exact Nat.mul_mod_right (b ^ K) m
  exact ⟨N, K, L, C, hKL, hmiddle, hpos, by simpa [hV0] using harith⟩

/-- **Erdős #249 low-carry socket.**  Like the wave-14 carry-aware
socket, but the first totient block may leave a residue: with
`V = (∑_{r≤K} φ(N+r)·2^(K-r)) % 2^K`, certificates need only
`q·(V·2^(L-K) + C + (N+L+2)) < 2^L`.  This is the sharpened live route
for #249 — the supply question becomes an interval-hit / low-band
statement for the carry residue rather than an exact congruence.
Certificate SUPPLY is NOT claimed. -/
theorem irrational_tsum_totient_div_pow_two_of_totient_low_carry_certificates
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∑ r ∈ Finset.Icc (K + 1) L, Nat.totient (N + r) * 2 ^ (L - r) ≤ C) ∧
        q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K
          * 2 ^ (L - K) + C + (N + L + 2)) < 2 ^ L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) := by
  have h := irrational_coeff_series_of_weighted_coeff_low_carry_block_certificates 2
    Nat.totient (by norm_num) Nat.totient_le ?_
  · have hbridge := tsum_totient_div_pow_eq_shifted 2 (by norm_num)
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hcast] at h hbridge
    rwa [hbridge]
  · intro q hq
    obtain ⟨N, K, L, C, hKL, hmiddle, harith⟩ := hcert q hq
    exact ⟨N, K, L, C, hKL, hmiddle,
      ⟨0, Nat.totient_pos.mpr (by omega)⟩, harith⟩

/-- **Erdős #249 low-carry supply target, full-block form.**  The
`L = K, C = 0` specialisation: `∑_{n≥1} φ(n)/2^n` is irrational provided
that for every `q` some window `(N, K)` has small carry residue,
`q·((∑_{r≤K} φ(N+r)·2^(K-r)) % 2^K + (N+K+2)) < 2^K`.  This is the
exact on-disk form of the OPEN interval-hit obligation: a band of
≈ `2^K/q` acceptable residues at height `N ≲ 2^K/q`, against wave-14's
single exact residue `0`.  SUPPLY is NOT claimed. -/
theorem irrational_tsum_totient_div_pow_two_of_totient_low_carry_full_block_certificates
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K : ℕ,
        q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K
          + (N + K + 2)) < 2 ^ K) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) := by
  apply irrational_tsum_totient_div_pow_two_of_totient_low_carry_certificates
  intro q hq
  obtain ⟨N, K, hlt⟩ := hcert q hq
  refine ⟨N, K, K, 0, le_refl K, ?_, ?_⟩
  · rw [Finset.Icc_eq_empty (by omega)]
    simp
  · simpa [Nat.sub_self] using hlt


/-! ## Erdős #249 lane, wave 16: carry-field recurrences, top-band transfer,
and machine-checked denominator exclusion

The residue field `V_K(N) = (∑_{r≤K} φ(N+r)·2^(K-r)) % 2^K` advances by the
same affine doubling map in both lattice directions: `V_K(N+1) =
(2·V_K(N) + φ(N+K+1)) % 2^K` (shift) and `V_{K+1}(N) = (2·V_K(N) +
φ(N+K+1)) % 2^(K+1)` (window).  Consequently the open low-band supply
obligation is exactly a carry-out event of the K-climb: whenever the
residue enters the top band — `2^(K+1) ≤ 2·V_K + φ(N+K+1)` — the next
window's residue drops below `φ(N+K+1)`
(`totient_carry_residue_top_band_step`), and that event yields a full
low-carry certificate whenever `q·(φ(N+K+1) + N+(K+1)+2) ≤ 2^(K+1)`
(`totient_low_carry_full_block_certificate_of_top_band`).

The per-`q` slice of the open supply is machine-checkable: one concrete
certificate at `q` denies every rational representation `a/q`
(`coeff_series_shifted_ne_int_div_of_low_carry_certificate`) and
transports down the whole denominator ladder
(`totient_low_carry_full_block_certificate_mono`).  This wave lands a
concrete certificate at `q = 4838` (window `N = 763`, `K = 34`, every
window totient certified by its prime factorization), so it is kernel
truth that `∑_{n≥0} φ(n)/2^n` has no rational representation with
denominator ≤ 4838 — the first unconditional statement about the #249
constant itself.  The ∀q supply — full #249 — remains OPEN and is NOT
claimed: runner non-claims `not_erdos_249_solution`,
`not_totient_low_carry_certificate_supply`,
`not_denominator_exclusion_beyond_verified_instance_ladder`. -/

/-- **Icc→range normal form for the totient carry sum.**  The first-block
weighted sum re-indexed to `Finset.range`, the shape shared by the carry
recurrences and by concrete certificate evaluation. -/
theorem totient_carry_sum_eq_range (M K : ℕ) :
    (∑ r ∈ Finset.Icc 1 K, Nat.totient (M + r) * 2 ^ (K - r))
      = ∑ i ∈ Finset.range K, Nat.totient (M + 1 + i) * 2 ^ (K - 1 - i) := by
  have hIccIco : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIccIco, Finset.sum_Ico_eq_sum_range]
  have hn : K + 1 - 1 = K := by omega
  rw [hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : M + (1 + i) = M + 1 + i := by omega
  have h2 : K - (1 + i) = K - 1 - i := by omega
  rw [h1, h2]

/-- **Carry-field K-step (window growth), exact form.**  Extending the
window by one slot doubles the carry sum and feeds in the next totient:
`T_{K+1}(N) = 2·T_K(N) + φ(N+K+1)`. -/
theorem totient_carry_sum_succ_window (N K : ℕ) :
    (∑ r ∈ Finset.Icc 1 (K + 1), Nat.totient (N + r) * 2 ^ (K + 1 - r))
      = 2 * (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r))
        + Nat.totient (N + (K + 1)) := by
  rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ K + 1)]
  have htop : Nat.totient (N + (K + 1)) * 2 ^ (K + 1 - (K + 1))
      = Nat.totient (N + (K + 1)) := by
    rw [Nat.sub_self, pow_zero, mul_one]
  rw [htop]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hr
  have h3 : K + 1 - r = (K - r) + 1 := by omega
  rw [h3, pow_succ]
  ring

/-- **Carry-field bottom split, exact form.**  The `(K+1)`-window splits at
its first slot: `T_{K+1}(N) = 2^K·φ(N+1) + T_K(N+1)`.  Together with the
K-step this yields the N-step recurrence. -/
theorem totient_carry_sum_bottom_split (N K : ℕ) :
    (∑ r ∈ Finset.Icc 1 (K + 1), Nat.totient (N + r) * 2 ^ (K + 1 - r))
      = 2 ^ K * Nat.totient (N + 1)
        + ∑ r ∈ Finset.Icc 1 K, Nat.totient (N + 1 + r) * 2 ^ (K - r) := by
  rw [totient_carry_sum_eq_range N (K + 1), totient_carry_sum_eq_range (N + 1) K]
  rw [Finset.sum_range_succ']
  have hzero : Nat.totient (N + 1 + 0) * 2 ^ (K + 1 - 1 - 0)
      = 2 ^ K * Nat.totient (N + 1) := by
    have h1 : N + 1 + 0 = N + 1 := by omega
    have h2 : K + 1 - 1 - 0 = K := by omega
    rw [h1, h2]
    ring
  rw [hzero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : N + 1 + (i + 1) = N + 1 + 1 + i := by omega
  have h2 : K + 1 - 1 - (i + 1) = K - 1 - i := by omega
  rw [h1, h2]

/-- **Carry-field N-step (shift), exact form.**  Shifting the window start
by one obeys `T_K(N+1) + 2^K·φ(N+1) = 2·T_K(N) + φ(N+K+1)` — the exact
integer form of the scout recurrence `V(N+1) = (2V(N) + φ(N+K+1)) mod 2^K`. -/
theorem totient_carry_sum_succ_shift (N K : ℕ) :
    (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + 1 + r) * 2 ^ (K - r))
        + 2 ^ K * Nat.totient (N + 1)
      = 2 * (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r))
        + Nat.totient (N + (K + 1)) := by
  have h1 := totient_carry_sum_bottom_split N K
  have h2 := totient_carry_sum_succ_window N K
  omega

/-- **Carry-residue N-step recurrence.**  The residue field advances by an
affine doubling map with totient input:
`V_K(N+1) = (2·V_K(N) + φ(N+K+1)) mod 2^K`. -/
theorem totient_carry_residue_succ_shift (N K : ℕ) :
    (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + 1 + r) * 2 ^ (K - r)) % 2 ^ K
      = (2 * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
          + Nat.totient (N + (K + 1))) % 2 ^ K := by
  have h := totient_carry_sum_succ_shift N K
  have hmod1 : (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + 1 + r) * 2 ^ (K - r)) % 2 ^ K
      = (2 * (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r))
          + Nat.totient (N + (K + 1))) % 2 ^ K := by
    conv_lhs => rw [← Nat.add_mul_mod_self_left
      (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + 1 + r) * 2 ^ (K - r))
      (2 ^ K) (Nat.totient (N + 1))]
    rw [h]
  have hmod2 : (2 * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
      + Nat.totient (N + (K + 1))) % 2 ^ K
      = (2 * (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r))
          + Nat.totient (N + (K + 1))) % 2 ^ K :=
    ((Nat.mod_modEq _ (2 ^ K)).mul_left 2).add_right _
  rw [hmod1, ← hmod2]

/-- **Carry-residue K-step recurrence.**  The same affine doubling map also
advances precision: `V_{K+1}(N) = (2·V_K(N) + φ(N+K+1)) mod 2^{K+1}`.
The K-climb `W_K = V_K/2^K` increases by `φ(N+K+1)/2^{K+1}` mod 1, so a
supply hit is exactly a carry-out event of this climb. -/
theorem totient_carry_residue_succ_window (N K : ℕ) :
    (∑ r ∈ Finset.Icc 1 (K + 1), Nat.totient (N + r) * 2 ^ (K + 1 - r)) % 2 ^ (K + 1)
      = (2 * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
          + Nat.totient (N + (K + 1))) % 2 ^ (K + 1) := by
  rw [totient_carry_sum_succ_window N K]
  have hsplit : 2 * (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r))
      = 2 * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
        + 2 ^ (K + 1) * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) / 2 ^ K) := by
    have hdm := Nat.div_add_mod
      (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) (2 ^ K)
    have hpow : (2 : ℕ) ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
    calc 2 * (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r))
        = 2 * (2 ^ K * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) / 2 ^ K)
            + (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K) := by
          rw [hdm]
      _ = 2 * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
            + 2 ^ (K + 1) * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) / 2 ^ K) := by
          rw [hpow]; ring
  rw [hsplit, add_right_comm, Nat.add_mul_mod_self_left]

/-- **Top-band transfer (carry-out event).**  If the residue sits within
`φ(N+K+1)` of the top of its scale — `2^{K+1} ≤ 2·V_K(N) + φ(N+K+1)` —
then one K-step wraps and the next residue is tiny:
`V_{K+1}(N) < φ(N+K+1)`.  Supply hits are exactly these carry-out events,
so the open low-band obligation may equivalently be hunted at the top of
the band, where the target width is `φ/2 ≈ N` instead of `2^K/q`. -/
theorem totient_carry_residue_top_band_step (N K : ℕ)
    (hf : Nat.totient (N + (K + 1)) < 2 ^ (K + 1))
    (htop : 2 ^ (K + 1)
      ≤ 2 * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
        + Nat.totient (N + (K + 1))) :
    (∑ r ∈ Finset.Icc 1 (K + 1), Nat.totient (N + r) * 2 ^ (K + 1 - r)) % 2 ^ (K + 1)
      < Nat.totient (N + (K + 1)) := by
  rw [totient_carry_residue_succ_window N K]
  have hvlt : (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K
      < 2 ^ K := Nat.mod_lt _ (Nat.two_pow_pos K)
  have h2v : 2 * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
      < 2 ^ (K + 1) := by
    have hpow : (2 : ℕ) ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
    omega
  rw [Nat.mod_eq_sub_mod htop, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Carry-out events supply certificates.**  A top-band hit at scale `K`
plus the height room `q·(φ(N+K+1) + N+(K+1)+2) ≤ 2^{K+1}` yields the full
low-carry certificate at scale `K+1`.  This is the machine-checked change
of coordinates on the open supply problem: find one carry-out event with
height room, and #249's certificate at that `q` exists. -/
theorem totient_low_carry_full_block_certificate_of_top_band (q N K : ℕ)
    (hf : Nat.totient (N + (K + 1)) < 2 ^ (K + 1))
    (htop : 2 ^ (K + 1)
      ≤ 2 * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
        + Nat.totient (N + (K + 1)))
    (hheight : q * (Nat.totient (N + (K + 1)) + (N + (K + 1) + 2)) ≤ 2 ^ (K + 1)) :
    q * ((∑ r ∈ Finset.Icc 1 (K + 1), Nat.totient (N + r) * 2 ^ (K + 1 - r)) % 2 ^ (K + 1)
        + (N + (K + 1) + 2)) < 2 ^ (K + 1) := by
  have hstep := totient_carry_residue_top_band_step N K hf htop
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    simp only [Nat.zero_mul]
    exact Nat.two_pow_pos (K + 1)
  · calc q * ((∑ r ∈ Finset.Icc 1 (K + 1), Nat.totient (N + r) * 2 ^ (K + 1 - r)) % 2 ^ (K + 1)
          + (N + (K + 1) + 2))
        < q * (Nat.totient (N + (K + 1)) + (N + (K + 1) + 2)) :=
          mul_lt_mul_of_pos_left (by omega) hq0
      _ ≤ 2 ^ (K + 1) := hheight

/-- **Certificate transport down the denominator ladder.**  A low-carry
full-block certificate at `q` is one at every `d ≤ q` with the same
witness `(N, K)`. -/
theorem totient_low_carry_full_block_certificate_mono (q d N K : ℕ) (hle : d ≤ q)
    (hcert : q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K
        + (N + K + 2)) < 2 ^ K) :
    d * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K
        + (N + K + 2)) < 2 ^ K :=
  lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) hcert

/-- **Per-`q` denominator exclusion, generic engine.**  One low-carry
certificate at a single `q` already denies every rational representation
with denominator exactly `q`: the near-integer witness puts
`q·(b^N·Σ − z)` strictly between consecutive integers, while `Σ = a/q`
would make it an integer. -/
theorem coeff_series_shifted_ne_int_div_of_low_carry_certificate
    (b q N K L C : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C)
    (hpos : ∃ t : ℕ, 0 < c (N + L + 1 + t))
    (harith : q * ((∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r)) % b ^ K
        * b ^ (L - K) + C + (N + L + 2)) < b ^ L) :
    ∀ a : ℤ, (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) ≠ (a : ℝ) / (q : ℝ) := by
  intro a heq
  obtain ⟨z, hz_pos, hz_lt⟩ :=
    near_int_witness_of_weighted_coeff_low_carry_block_certificate
      b q N K L C c hb hq hKL hgrowth hmiddle hpos harith
  rw [heq] at hz_pos hz_lt
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq'
  have hkey : ((((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z : ℤ) : ℝ)
      = (q : ℝ) * ((b : ℝ) ^ N * ((a : ℝ) / (q : ℝ)) - (z : ℝ)) := by
    push_cast
    field_simp
  have h0 : (0 : ℝ) < ((((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z : ℤ) : ℝ) := by
    rw [hkey]
    exact mul_pos hq' hz_pos
  have h1 : ((((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z : ℤ) : ℝ) < 1 := by
    rw [hkey]
    have := mul_lt_mul_of_pos_left hz_lt hq'
    rwa [mul_one_div, div_self hqne] at this
  have h0' : (0 : ℤ) < ((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z := by exact_mod_cast h0
  have h1' : ((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z < 1 := by exact_mod_cast h1
  omega

/-- **Erdős #249 per-`q` denominator exclusion.**  A single low-carry
full-block certificate at `q` denies every representation
`∑_{n≥0} φ(n)/2^n = a/q`.  This is the per-precision slice of the open
irrationality: instances are machine-checkable, the ∀q supply is not
claimed. -/
theorem tsum_totient_div_pow_two_ne_int_div_of_totient_low_carry_full_block_certificate
    (q N K : ℕ) (hq : 0 < q)
    (hcert : q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K
        + (N + K + 2)) < 2 ^ K) :
    ∀ a : ℤ, (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (q : ℝ) := by
  intro a
  have h := coeff_series_shifted_ne_int_div_of_low_carry_certificate
    2 q N K K 0 Nat.totient (by norm_num) hq (le_refl K) Nat.totient_le
    (by rw [Finset.Icc_eq_empty (by omega)]; simp)
    ⟨0, Nat.totient_pos.mpr (by omega)⟩
    (by simpa [Nat.sub_self] using hcert) a
  have hbridge := tsum_totient_div_pow_eq_shifted 2 (by norm_num)
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast] at h hbridge
  rw [hbridge]
  exact h

private lemma phi_4838_0 : Nat.totient (763 + 1 + 0) = 380 := by
  have e : (763 + 1 + 0 : ℕ) = 764 := by norm_num
  rw [e]
  rw [show (764 : ℕ) = 2 ^ 2 * 191 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (191)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 191)]
  norm_num
private lemma phi_4838_1 : Nat.totient (763 + 1 + 1) = 384 := by
  have e : (763 + 1 + 1 : ℕ) = 765 := by norm_num
  rw [e]
  rw [show (765 : ℕ) = 3 ^ 2 * (5 * 17) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (5 * 17)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (17)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]
  norm_num
private lemma phi_4838_2 : Nat.totient (763 + 1 + 2) = 382 := by
  have e : (763 + 1 + 2 : ℕ) = 766 := by norm_num
  rw [e]
  rw [show (766 : ℕ) = 2 * 383 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (383)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 383)]
private lemma phi_4838_3 : Nat.totient (763 + 1 + 3) = 696 := by
  have e : (763 + 1 + 3 : ℕ) = 767 := by norm_num
  rw [e]
  rw [show (767 : ℕ) = 13 * 59 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (13) (59)),
    Nat.totient_prime (by norm_num : Nat.Prime 13),
    Nat.totient_prime (by norm_num : Nat.Prime 59)]
private lemma phi_4838_4 : Nat.totient (763 + 1 + 4) = 256 := by
  have e : (763 + 1 + 4 : ℕ) = 768 := by norm_num
  rw [e]
  rw [show (768 : ℕ) = 2 ^ 8 * 3 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 8) (3)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 8),
    Nat.totient_prime (by norm_num : Nat.Prime 3)]
  norm_num
private lemma phi_4838_5 : Nat.totient (763 + 1 + 5) = 768 := by
  have e : (763 + 1 + 5 : ℕ) = 769 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 769)]
private lemma phi_4838_6 : Nat.totient (763 + 1 + 6) = 240 := by
  have e : (763 + 1 + 6 : ℕ) = 770 := by norm_num
  rw [e]
  rw [show (770 : ℕ) = 2 * (5 * (7 * 11)) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5 * (7 * 11))),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (7 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]
private lemma phi_4838_7 : Nat.totient (763 + 1 + 7) = 512 := by
  have e : (763 + 1 + 7 : ℕ) = 771 := by norm_num
  rw [e]
  rw [show (771 : ℕ) = 3 * 257 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (257)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 257)]
private lemma phi_4838_8 : Nat.totient (763 + 1 + 8) = 384 := by
  have e : (763 + 1 + 8 : ℕ) = 772 := by norm_num
  rw [e]
  rw [show (772 : ℕ) = 2 ^ 2 * 193 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (193)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 193)]
  norm_num
private lemma phi_4838_9 : Nat.totient (763 + 1 + 9) = 772 := by
  have e : (763 + 1 + 9 : ℕ) = 773 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 773)]
private lemma phi_4838_10 : Nat.totient (763 + 1 + 10) = 252 := by
  have e : (763 + 1 + 10 : ℕ) = 774 := by norm_num
  rw [e]
  rw [show (774 : ℕ) = 2 * (3 ^ 2 * 43) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 ^ 2 * 43)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (43)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 43)]
  norm_num
private lemma phi_4838_11 : Nat.totient (763 + 1 + 11) = 600 := by
  have e : (763 + 1 + 11 : ℕ) = 775 := by norm_num
  rw [e]
  rw [show (775 : ℕ) = 5 ^ 2 * 31 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5 ^ 2) (31)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 31)]
  norm_num
private lemma phi_4838_12 : Nat.totient (763 + 1 + 12) = 384 := by
  have e : (763 + 1 + 12 : ℕ) = 776 := by norm_num
  rw [e]
  rw [show (776 : ℕ) = 2 ^ 3 * 97 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (97)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 97)]
  norm_num
private lemma phi_4838_13 : Nat.totient (763 + 1 + 13) = 432 := by
  have e : (763 + 1 + 13 : ℕ) = 777 := by norm_num
  rw [e]
  rw [show (777 : ℕ) = 3 * (7 * 37) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (7 * 37)),
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (37)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 37)]
private lemma phi_4838_14 : Nat.totient (763 + 1 + 14) = 388 := by
  have e : (763 + 1 + 14 : ℕ) = 778 := by norm_num
  rw [e]
  rw [show (778 : ℕ) = 2 * 389 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (389)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 389)]
private lemma phi_4838_15 : Nat.totient (763 + 1 + 15) = 720 := by
  have e : (763 + 1 + 15 : ℕ) = 779 := by norm_num
  rw [e]
  rw [show (779 : ℕ) = 19 * 41 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (19) (41)),
    Nat.totient_prime (by norm_num : Nat.Prime 19),
    Nat.totient_prime (by norm_num : Nat.Prime 41)]
private lemma phi_4838_16 : Nat.totient (763 + 1 + 16) = 192 := by
  have e : (763 + 1 + 16 : ℕ) = 780 := by norm_num
  rw [e]
  rw [show (780 : ℕ) = 2 ^ 2 * (3 * (5 * 13)) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 * (5 * 13))),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5 * 13)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (13)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]
  norm_num
private lemma phi_4838_17 : Nat.totient (763 + 1 + 17) = 700 := by
  have e : (763 + 1 + 17 : ℕ) = 781 := by norm_num
  rw [e]
  rw [show (781 : ℕ) = 11 * 71 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (11) (71)),
    Nat.totient_prime (by norm_num : Nat.Prime 11),
    Nat.totient_prime (by norm_num : Nat.Prime 71)]
private lemma phi_4838_18 : Nat.totient (763 + 1 + 18) = 352 := by
  have e : (763 + 1 + 18 : ℕ) = 782 := by norm_num
  rw [e]
  rw [show (782 : ℕ) = 2 * (17 * 23) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (17 * 23)),
    Nat.totient_mul (by norm_num : Nat.Coprime (17) (23)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 17),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]
private lemma phi_4838_19 : Nat.totient (763 + 1 + 19) = 504 := by
  have e : (763 + 1 + 19 : ℕ) = 783 := by norm_num
  rw [e]
  rw [show (783 : ℕ) = 3 ^ 3 * 29 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 3) (29)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 29)]
  norm_num
private lemma phi_4838_20 : Nat.totient (763 + 1 + 20) = 336 := by
  have e : (763 + 1 + 20 : ℕ) = 784 := by norm_num
  rw [e]
  rw [show (784 : ℕ) = 2 ^ 4 * 7 ^ 2 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 4) (7 ^ 2)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 7) (by norm_num : 0 < 2)]
  norm_num
private lemma phi_4838_21 : Nat.totient (763 + 1 + 21) = 624 := by
  have e : (763 + 1 + 21 : ℕ) = 785 := by norm_num
  rw [e]
  rw [show (785 : ℕ) = 5 * 157 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (157)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 157)]
private lemma phi_4838_22 : Nat.totient (763 + 1 + 22) = 260 := by
  have e : (763 + 1 + 22 : ℕ) = 786 := by norm_num
  rw [e]
  rw [show (786 : ℕ) = 2 * (3 * 131) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 131)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (131)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 131)]
private lemma phi_4838_23 : Nat.totient (763 + 1 + 23) = 786 := by
  have e : (763 + 1 + 23 : ℕ) = 787 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 787)]
private lemma phi_4838_24 : Nat.totient (763 + 1 + 24) = 392 := by
  have e : (763 + 1 + 24 : ℕ) = 788 := by norm_num
  rw [e]
  rw [show (788 : ℕ) = 2 ^ 2 * 197 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (197)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 197)]
  norm_num
private lemma phi_4838_25 : Nat.totient (763 + 1 + 25) = 524 := by
  have e : (763 + 1 + 25 : ℕ) = 789 := by norm_num
  rw [e]
  rw [show (789 : ℕ) = 3 * 263 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (263)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 263)]
private lemma phi_4838_26 : Nat.totient (763 + 1 + 26) = 312 := by
  have e : (763 + 1 + 26 : ℕ) = 790 := by norm_num
  rw [e]
  rw [show (790 : ℕ) = 2 * (5 * 79) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5 * 79)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (79)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 79)]
private lemma phi_4838_27 : Nat.totient (763 + 1 + 27) = 672 := by
  have e : (763 + 1 + 27 : ℕ) = 791 := by norm_num
  rw [e]
  rw [show (791 : ℕ) = 7 * 113 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (113)),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 113)]
private lemma phi_4838_28 : Nat.totient (763 + 1 + 28) = 240 := by
  have e : (763 + 1 + 28 : ℕ) = 792 := by norm_num
  rw [e]
  rw [show (792 : ℕ) = 2 ^ 3 * (3 ^ 2 * 11) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (3 ^ 2 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (11)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]
  norm_num
private lemma phi_4838_29 : Nat.totient (763 + 1 + 29) = 720 := by
  have e : (763 + 1 + 29 : ℕ) = 793 := by norm_num
  rw [e]
  rw [show (793 : ℕ) = 13 * 61 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (13) (61)),
    Nat.totient_prime (by norm_num : Nat.Prime 13),
    Nat.totient_prime (by norm_num : Nat.Prime 61)]
private lemma phi_4838_30 : Nat.totient (763 + 1 + 30) = 396 := by
  have e : (763 + 1 + 30 : ℕ) = 794 := by norm_num
  rw [e]
  rw [show (794 : ℕ) = 2 * 397 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (397)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 397)]
private lemma phi_4838_31 : Nat.totient (763 + 1 + 31) = 416 := by
  have e : (763 + 1 + 31 : ℕ) = 795 := by norm_num
  rw [e]
  rw [show (795 : ℕ) = 3 * (5 * 53) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5 * 53)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (53)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 53)]
private lemma phi_4838_32 : Nat.totient (763 + 1 + 32) = 396 := by
  have e : (763 + 1 + 32 : ℕ) = 796 := by norm_num
  rw [e]
  rw [show (796 : ℕ) = 2 ^ 2 * 199 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (199)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 199)]
  norm_num
private lemma phi_4838_33 : Nat.totient (763 + 1 + 33) = 796 := by
  have e : (763 + 1 + 33 : ℕ) = 797 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 797)]
/-- **Concrete machine-checked low-carry certificate at `q = 4838`**
(witness `N = 763`, `K = 34`, residue `V = 3550228`):
`4838·(3550228 + 763 + 34 + 2) = 17179868626 < 2^34`.  Each window totient is
certified by its prime factorization and rewritten to a literal before any
arithmetic runs, so the proof is kernel-shallow and uses no compiler-trusted
reflection. -/
theorem totient_low_carry_full_block_certificate_4838 :
    4838 * ((∑ r ∈ Finset.Icc 1 34, Nat.totient (763 + r) * 2 ^ (34 - r)) % 2 ^ 34
      + (763 + 34 + 2)) < 2 ^ 34 := by
  rw [totient_carry_sum_eq_range 763 34]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, phi_4838_0, phi_4838_1, phi_4838_2, phi_4838_3, phi_4838_4, phi_4838_5, phi_4838_6, phi_4838_7, phi_4838_8, phi_4838_9, phi_4838_10, phi_4838_11, phi_4838_12, phi_4838_13, phi_4838_14, phi_4838_15, phi_4838_16, phi_4838_17, phi_4838_18, phi_4838_19, phi_4838_20, phi_4838_21, phi_4838_22, phi_4838_23, phi_4838_24, phi_4838_25, phi_4838_26, phi_4838_27, phi_4838_28, phi_4838_29, phi_4838_30, phi_4838_31, phi_4838_32, phi_4838_33]
  norm_num

/-- **Erdős #249 denominator exclusion to `4838`.**  Machine-checked:
`∑_{n≥0} φ(n)/2^n` is not `a/d` for any integer `a` and any denominator
`1 ≤ d ≤ 4838`; one certificate transports down the ladder via
`totient_low_carry_full_block_certificate_mono`.  Unconditional instance
slice of #249; the ∀q supply (full irrationality) is NOT claimed. -/
theorem tsum_totient_div_pow_two_ne_int_div_of_den_le_4838 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 4838 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) :=
  fun a d hd hdle =>
    tsum_totient_div_pow_two_ne_int_div_of_totient_low_carry_full_block_certificate
      d 763 34 hd
      (totient_low_carry_full_block_certificate_mono 4838 d 763 34 hdle
        totient_low_carry_full_block_certificate_4838) a

/-- **Erdős #249 denominator exclusion, `ℚ` form.**  If `∑_{n≥0} φ(n)/2^n`
is rational, its reduced denominator exceeds `4838`. -/
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_4838 :
    ∀ p : ℚ, p.den ≤ 4838 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  intro p hden heq
  exact tsum_totient_div_pow_two_ne_int_div_of_den_le_4838 p.num p.den p.pos hden
    (heq.trans (Rat.cast_def p))


/-! ### Wave 17 — gap-certificate engine and bulk denominator exclusion

**The gap reframe.**  Rationality `Σ = a/q` forces `q·F_N ∈ ℤ` at every
shift `N`, pinning the scaled tail to the integer lattice.  The wave-16
engine refuted a denominator only from the bottom band — residue
`V_K(N)` inside `(0, 2^K/q)`, a `1/q`-rare event that drove the witness
scout to `N ≈ 3×10^8` and into the large-totient kernel-recursion trap.
But landing strictly inside ANY consecutive-integer gap `(j, j+1)` after
scaling by `q` is an equal refutation: with `W = (q·V_K(N)) mod 2^K`, the
single inequality `W + q·(N+K+2) < 2^K` — avoid one thin TOP band — is a
full certificate (`strict_between_int_witness_of_weighted_coeff_gap_certificate`;
the landed low-carry certificate is exactly the `j = 0` case,
`totient_gap_certificate_of_low_carry_certificate`).  For
`2^K ≳ q²·(N+K)` essentially every window certifies every `q`, so `N = 1`
suffices and every window totient stays tiny (≤ 112 here): the
kernel-recursion ceiling that capped wave 16 at denominator 4838 is
gone, not merely raised.

**Bulk verification.**  One kernel-computed run of an unrolled
binary-splitting checker (`totient_gap_row_window_1_120` /
`totient_gap_check_window_1_120_pow_*`, recursion depth 22, ordinary
`Decidable` kernel evaluation via `decide +kernel` — no compiler-trusted
reflection, no new axioms) certifies the gap inequality for every
`q ≤ 2^22 = 4194304` at the single window `(N, K) = (1, 120)`;
per-level soundness lemmas convert the run into per-`q` theorems.
Headline: `∑_{n≥0} φ(n)/2^n` has no rational representation with
denominator ≤ 4194304 — wave 16's 4838, and the previously unreachable
empirical champion target 50357951, both fall out of one tiny window.

**What remains open (NOT claimed).**  The `∀q` gap supply — for every `q`
one window avoiding its thin top band — would close Erdős #249
(`irrational_tsum_totient_div_pow_two_of_gap_certificate_supply`).  Under
the rationality hypothesis the top-band deficit obeys the same expanding
shadow dynamics `s ↦ 2s − q·φ` as the residue field, so no unconditional
contradiction is available without new analytic input on totient carry
sums; the supply, and #249 itself, remain open.  Runner non-claims:
`not_erdos_249_solution`, `not_totient_gap_certificate_supply`,
`not_denominator_exclusion_beyond_verified_instance_ladder`. -/

/-- **Real sandwich for the gap band.**  Abstract core of the gap witness:
with `bL·j + W = q·U` (Euclidean split of `q·U`), positive remainder `s`
bounded by `(C + D)/bL`, and the band inequality `W + q·(C+D) < bL`, the
scaled value `q·(U/bL + s)` lies strictly between `j` and `j + 1`. -/
private lemma gap_band_sandwich (bL qR UR WR jR s CR DR : ℝ)
    (hbL : 0 < bL) (hq : 0 < qR) (hdm : bL * jR + WR = qR * UR)
    (hW : 0 ≤ WR) (hs : 0 < s) (hsle : s ≤ CR / bL + DR / bL)
    (hband : WR + qR * (CR + DR) < bL) :
    jR < qR * (UR / bL + s) ∧ qR * (UR / bL + s) < jR + 1 := by
  have hbLne : bL ≠ 0 := ne_of_gt hbL
  have hqU : qR * (UR / bL + s) = jR + WR / bL + qR * s := by
    field_simp
    linear_combination -hdm
  constructor
  · have h1 : 0 ≤ WR / bL := div_nonneg hW (le_of_lt hbL)
    have h2 : 0 < qR * s := mul_pos hq hs
    rw [hqU]
    linarith
  · rw [hqU]
    have h3 : qR * s ≤ qR * (CR / bL + DR / bL) :=
      mul_le_mul_of_nonneg_left hsle (le_of_lt hq)
    have h4 : WR / bL + qR * (CR / bL + DR / bL) < 1 := by
      have e : WR / bL + qR * (CR / bL + DR / bL) = (WR + qR * (CR + DR)) / bL := by
        ring
      rw [e, div_lt_one hbL]
      exact hband
    linarith

/-- **Gap witness.** Under the gap certificate
`(q·(V·b^(L−K))) % b^L + q·(C + (N+L+2)) < b^L` (with `V` the K-window
residue), the shifted series lands strictly inside a consecutive-integer
gap after scaling by `q`: `j < q·(b^N·Σ − z) < j + 1` for the explicit
`j = (q·V·b^(L−K)) / b^L`. -/
theorem strict_between_int_witness_of_weighted_coeff_gap_certificate
    (b q N K L C : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C)
    (hpos : ∃ t : ℕ, 0 < c (N + L + 1 + t))
    (harith : (q * ((∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r)) % b ^ K
        * b ^ (L - K))) % b ^ L + q * (C + (N + L + 2)) < b ^ L) :
    ∃ z : ℤ, ∃ j : ℕ,
      (j : ℝ) < (q : ℝ) * ((b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)) ∧
        (q : ℝ) * ((b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
            - (z : ℝ)) < (j : ℝ) + 1 := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb_pos : (0 : ℝ) < (b : ℝ) := by linarith
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨z₀, hz₀⟩ := bpow_mul_coeff_series_eq_int_add_tail b N c hb hgrowth
  have hfsum : Summable
      (fun r : ℕ => ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1)) :=
    summable_coeff_shift_tail b N c hb hgrowth
  have hfarsum : Summable
      (fun t : ℕ => ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) :=
    (summable_nat_add_iff L).mpr hfsum
  -- split the tail at L
  have hsplitL : (∑' r : ℕ, ((c (N + r + 1) : ℝ)) / (b : ℝ) ^ (r + 1))
      = (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    (Summable.sum_add_tsum_nat_add L hfsum).symm
  -- split the finite part at K
  have hsplitK : (∑ i ∈ Finset.range L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      = (∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKL,
      ← Finset.range_eq_Ico]
  -- the first block splits as integer part + residue over `b^K`
  set S₁ : ℕ := ∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r) with hS₁def
  set z₁ : ℕ := S₁ / b ^ K with hz₁def
  set V : ℕ := S₁ % b ^ K with hVdef
  have hreidx : S₁ = ∑ i ∈ Finset.range K, c (N + i + 1) * b ^ (K - (i + 1)) := by
    rw [hS₁def]
    have hIccIco : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range]
    have hn : K + 1 - 1 = K := by omega
    rw [hn]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 : N + (1 + i) = N + i + 1 := by omega
    have h2 : K - (1 + i) = K - (i + 1) := by omega
    rw [h1, h2]
  have hblock_eq : ((S₁ : ℕ) : ℝ) / (b : ℝ) ^ K
      = ∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [hreidx]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i < K := Finset.mem_range.mp hi
    have hsplit : (b : ℝ) ^ K = (b : ℝ) ^ (K - (i + 1)) * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    have hne1 : ((b : ℝ) ^ (K - (i + 1))) ≠ 0 := by positivity
    have hne2 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
    field_simp
  have hdm : b ^ K * z₁ + V = S₁ := by
    rw [hz₁def, hVdef]
    exact Nat.div_add_mod S₁ (b ^ K)
  have hdmR : (b : ℝ) ^ K * ((z₁ : ℕ) : ℝ) + ((V : ℕ) : ℝ) = ((S₁ : ℕ) : ℝ) := by
    exact_mod_cast hdm
  have hblock_split : ((z₁ : ℕ) : ℝ) + ((V : ℕ) : ℝ) / (b : ℝ) ^ K
      = ∑ i ∈ Finset.range K, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [← hblock_eq, ← hdmR]
    have hbKne : ((b : ℝ) ^ K) ≠ 0 := by positivity
    field_simp
  -- remainder positivity: some coefficient past the window is nonzero
  have hmid_nonneg : (0 : ℝ)
      ≤ ∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨t₀, ht₀⟩ := hpos
  have hfar_pos : (0 : ℝ)
      < ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) := by
    have hcpos : (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) := by
      have hidx : N + (t₀ + L) + 1 = N + L + 1 + t₀ := by omega
      have h0 : 0 < c (N + (t₀ + L) + 1) := by rw [hidx]; exact ht₀
      exact_mod_cast h0
    have hterm0 : (0 : ℝ)
        < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := by positivity
    calc (0 : ℝ) < ((c (N + (t₀ + L) + 1) : ℝ)) / (b : ℝ) ^ ((t₀ + L) + 1) := hterm0
      _ ≤ _ := hfarsum.le_tsum t₀ fun j _ => by positivity
  -- middle window: exact weighted sum over the common denominator b^L
  have hterm : ∀ i ∈ Finset.Ico K L,
      ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1)
        = ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    intro i hi
    obtain ⟨hKi, hiL⟩ := Finset.mem_Ico.mp hi
    have hb1 : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
    have hbL' : ((b : ℝ) ^ L) ≠ 0 := by positivity
    have hsplit : (b : ℝ) ^ L = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (L - (i + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_div_iff hb1 hbL']
    push_cast
    rw [hsplit]
    ring
  have hreindex : (∑ i ∈ Finset.Ico K L, c (N + i + 1) * b ^ (L - (i + 1)))
      = ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) := by
    have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hn : L + 1 - (K + 1) = L - K := by omega
    rw [hn]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : N + (K + j) + 1 = N + (K + 1 + j) := by omega
    have h2 : L - (K + j + 1) = L - (K + 1 + j) := by omega
    rw [h1, h2]
  have hmid : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      ≤ (C : ℝ) / (b : ℝ) ^ L := by
    have hsum_eq : (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    have hnum : (∑ i ∈ Finset.Ico K L,
        ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) ≤ (C : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hreindex.trans_le hmiddle
    calc (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        = (∑ i ∈ Finset.Ico K L,
            ((c (N + i + 1) * b ^ (L - (i + 1)) : ℕ) : ℝ)) / (b : ℝ) ^ L := hsum_eq
      _ ≤ (C : ℝ) / (b : ℝ) ^ L := by gcongr
  -- far tail bound, reshaped from the generic far-tail lemma
  have hfar_eq : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      = ∑' t : ℕ, ((c (N + L + 1 + t) : ℝ)) / (b : ℝ) ^ (L + 1 + t) := by
    refine tsum_congr fun t => ?_
    rw [show N + (t + L) + 1 = N + L + 1 + t from by omega,
      show t + L + 1 = L + 1 + t from by omega]
  have hfar : (∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
      ≤ ((N + L + 2 : ℕ) : ℝ) / (b : ℝ) ^ L := by
    rw [hfar_eq]
    exact coeff_far_tail_le b N L c hb hgrowth
  -- assemble the exact difference decomposition
  have hdiff : (b : ℝ) ^ N * (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
      - ((z₀ + (z₁ : ℤ) : ℤ) : ℝ)
      = ((V : ℕ) : ℝ) / (b : ℝ) ^ K
        + ((∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
          + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1)) := by
    rw [hz₀, hsplitL, hsplitK]
    push_cast
    rw [← hblock_split]
    ring
  -- the residue over b^K, re-expressed over the common denominator b^L
  have hVK : ((V : ℕ) : ℝ) / (b : ℝ) ^ K
      = ((V * b ^ (L - K) : ℕ) : ℝ) / (b : ℝ) ^ L := by
    have hbKne : ((b : ℝ) ^ K) ≠ 0 := by positivity
    have hbLne : ((b : ℝ) ^ L) ≠ 0 := by positivity
    rw [div_eq_div_iff hbKne hbLne]
    push_cast
    rw [show (b : ℝ) ^ L = (b : ℝ) ^ K * (b : ℝ) ^ (L - K) from by
      rw [← pow_add]; congr 1; omega]
    ring
  -- ============ gap-specific ending ============
  have hbLpos : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  have hmf_pos : (0 : ℝ)
      < (∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
        + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1) :=
    add_pos_of_nonneg_of_pos hmid_nonneg hfar_pos
  have hdmR : (b : ℝ) ^ L * (((q * (V * b ^ (L - K))) / b ^ L : ℕ) : ℝ)
        + (((q * (V * b ^ (L - K))) % b ^ L : ℕ) : ℝ)
      = (q : ℝ) * ((V * b ^ (L - K) : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_add_mod (q * (V * b ^ (L - K))) (b ^ L)
  have hWnn : (0 : ℝ) ≤ (((q * (V * b ^ (L - K))) % b ^ L : ℕ) : ℝ) := by positivity
  have hband : (((q * (V * b ^ (L - K))) % b ^ L : ℕ) : ℝ)
        + (q : ℝ) * ((C : ℝ) + ((N + L + 2 : ℕ) : ℝ)) < (b : ℝ) ^ L := by
    exact_mod_cast harith
  have hsw := gap_band_sandwich ((b : ℝ) ^ L) (q : ℝ) ((V * b ^ (L - K) : ℕ) : ℝ)
    (((q * (V * b ^ (L - K))) % b ^ L : ℕ) : ℝ)
    (((q * (V * b ^ (L - K))) / b ^ L : ℕ) : ℝ)
    ((∑ i ∈ Finset.Ico K L, ((c (N + i + 1) : ℝ)) / (b : ℝ) ^ (i + 1))
      + ∑' t : ℕ, ((c (N + (t + L) + 1) : ℝ)) / (b : ℝ) ^ ((t + L) + 1))
    (C : ℝ) ((N + L + 2 : ℕ) : ℝ)
    hbLpos hq' hdmR hWnn hmf_pos (add_le_add hmid hfar) hband
  refine ⟨z₀ + (z₁ : ℤ), (q * (V * b ^ (L - K))) / b ^ L, ?_, ?_⟩
  · rw [hdiff, hVK]
    exact hsw.1
  · rw [hdiff, hVK]
    exact hsw.2

/-- **Per-`q` denominator exclusion from a gap certificate, generic engine.**
A gap certificate at `q` denies every rational representation with
denominator exactly `q`: the witness puts `q·(b^N·Σ − z)` strictly between
the consecutive integers `j` and `j+1`, while `Σ = a/q` would make it an
integer.  The landed low-carry (bottom-band) certificate is the `j = 0`
special case. -/
theorem coeff_series_shifted_ne_int_div_of_gap_certificate
    (b q N K L C : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hq : 0 < q) (hKL : K ≤ L)
    (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C)
    (hpos : ∃ t : ℕ, 0 < c (N + L + 1 + t))
    (harith : (q * ((∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r)) % b ^ K
        * b ^ (L - K))) % b ^ L + q * (C + (N + L + 2)) < b ^ L) :
    ∀ a : ℤ, (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1)) ≠ (a : ℝ) / (q : ℝ) := by
  intro a heq
  obtain ⟨z, j, hlo, hhi⟩ :=
    strict_between_int_witness_of_weighted_coeff_gap_certificate
      b q N K L C c hb hq hKL hgrowth hmiddle hpos harith
  rw [heq] at hlo hhi
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq'
  have hkey : ((((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z : ℤ) : ℝ)
      = (q : ℝ) * ((b : ℝ) ^ N * ((a : ℝ) / (q : ℝ)) - (z : ℝ)) := by
    push_cast
    field_simp
  have h0 : ((j : ℤ) : ℝ) < ((((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z : ℤ) : ℝ) := by
    rw [hkey]
    exact_mod_cast hlo
  have h1 : ((((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z : ℤ) : ℝ) < ((j : ℤ) : ℝ) + 1 := by
    rw [hkey]
    exact_mod_cast hhi
  have h0' : (j : ℤ) < ((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z := by exact_mod_cast h0
  have h1' : ((b ^ N : ℕ) : ℤ) * a - (q : ℤ) * z < (j : ℤ) + 1 := by exact_mod_cast h1
  omega

/-- **Erdős #249 per-`q` denominator exclusion from a gap certificate.**
The gap certificate `(q·V_K(N)) mod 2^K + q·(N+K+2) < 2^K` — satisfiable by
a `1 − O(q·N/2^K)` fraction of residues instead of the bottom band's
`O(1/q)` fraction — denies every representation `∑_{n≥0} φ(n)/2^n = a/q`. -/
theorem tsum_totient_div_pow_two_ne_int_div_of_totient_gap_certificate
    (q N K : ℕ) (hq : 0 < q)
    (hcert : (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)) % 2 ^ K
        + q * (N + K + 2) < 2 ^ K) :
    ∀ a : ℤ, (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (q : ℝ) := by
  intro a
  have h := coeff_series_shifted_ne_int_div_of_gap_certificate
    2 q N K K 0 Nat.totient (by norm_num) hq (le_refl K) Nat.totient_le
    (by rw [Finset.Icc_eq_empty (by omega)]; simp)
    ⟨0, Nat.totient_pos.mpr (by omega)⟩
    (by simpa [Nat.sub_self] using hcert) a
  have hbridge := tsum_totient_div_pow_eq_shifted 2 (by norm_num)
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast] at h hbridge
  rw [hbridge]
  exact h

/-- **Bottom-band certificates transport into the gap engine.**  Every
landed low-carry certificate is a gap certificate (the `j = 0` band), so
the gap engine strictly supersedes the wave-16 engine. -/
theorem totient_gap_certificate_of_low_carry_certificate (q N K : ℕ)
    (hcert : q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K
        + (N + K + 2)) < 2 ^ K) :
    (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)) % 2 ^ K
        + q * (N + K + 2) < 2 ^ K := by
  have hmul : q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K
        + (N + K + 2))
      = q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
        + q * (N + K + 2) := Nat.mul_add q _ _
  have hlt : q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
      < 2 ^ K := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- **Gap-certificate supply closes Erdős #249.**  If every denominator `q`
admits one window `(N, K)` whose residue avoids the thin top band — width
`q·(N+K+2)` out of `2^K`, versus the bottom band's required width — then
`∑_{n≥0} φ(n)/2^n` is irrational.  This is the (strictly weaker) remaining
open obligation in gap coordinates; it is NOT claimed. -/
theorem irrational_tsum_totient_div_pow_two_of_gap_certificate_supply
    (hsupply : ∀ q : ℕ, 0 < q → ∃ N K : ℕ,
      (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)) % 2 ^ K
        + q * (N + K + 2) < 2 ^ K) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) := by
  rintro ⟨p, hp⟩
  obtain ⟨N, K, hcert⟩ := hsupply p.den p.pos
  exact tsum_totient_div_pow_two_ne_int_div_of_totient_gap_certificate
    p.den N K p.pos hcert p.num (hp.symm.trans (Rat.cast_def p))

/-- Single gap-certificate row at the wave-17 window `(N,K) = (1,120)`:
`(lo·V) mod 2^120 + lo·123 < 2^120` as a kernel-computable boolean. -/
def totient_gap_row_window_1_120 (lo : Nat) : Bool :=
  Nat.ble (lo * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + lo * 123 + 1) 1329227995784915872903807060280344576

private theorem totient_gap_row_window_1_120_sound (lo : Nat) (h : totient_gap_row_window_1_120 lo = true) :
    lo * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + lo * 123 < 1329227995784915872903807060280344576 := by
  have hle := Nat.le_of_ble_eq_true h
  omega

def totient_gap_check_window_1_120_pow_0 (lo : Nat) : Bool := totient_gap_row_window_1_120 lo

private theorem totient_gap_check_window_1_120_pow_0_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_0 lo = true) :
    ∀ i : Nat, i < 1 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  have hrow : totient_gap_row_window_1_120 lo = true := h
  have := totient_gap_row_window_1_120_sound lo hrow
  rw [Nat.add_zero]
  exact this

def totient_gap_check_window_1_120_pow_1 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_0 lo && totient_gap_check_window_1_120_pow_0 (lo + 1)

private theorem totient_gap_check_window_1_120_pow_1_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_1 lo = true) :
    ∀ i : Nat, i < 2 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_0 lo && totient_gap_check_window_1_120_pow_0 (lo + 1)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 1
  · exact totient_gap_check_window_1_120_pow_0_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_0_sound (lo + 1) hr (i - 1) (by omega)
    have hidx : lo + 1 + (i - 1) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_2 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_1 lo && totient_gap_check_window_1_120_pow_1 (lo + 2)

private theorem totient_gap_check_window_1_120_pow_2_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_2 lo = true) :
    ∀ i : Nat, i < 4 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_1 lo && totient_gap_check_window_1_120_pow_1 (lo + 2)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 2
  · exact totient_gap_check_window_1_120_pow_1_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_1_sound (lo + 2) hr (i - 2) (by omega)
    have hidx : lo + 2 + (i - 2) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_3 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_2 lo && totient_gap_check_window_1_120_pow_2 (lo + 4)

private theorem totient_gap_check_window_1_120_pow_3_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_3 lo = true) :
    ∀ i : Nat, i < 8 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_2 lo && totient_gap_check_window_1_120_pow_2 (lo + 4)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 4
  · exact totient_gap_check_window_1_120_pow_2_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_2_sound (lo + 4) hr (i - 4) (by omega)
    have hidx : lo + 4 + (i - 4) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_4 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_3 lo && totient_gap_check_window_1_120_pow_3 (lo + 8)

private theorem totient_gap_check_window_1_120_pow_4_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_4 lo = true) :
    ∀ i : Nat, i < 16 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_3 lo && totient_gap_check_window_1_120_pow_3 (lo + 8)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 8
  · exact totient_gap_check_window_1_120_pow_3_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_3_sound (lo + 8) hr (i - 8) (by omega)
    have hidx : lo + 8 + (i - 8) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_5 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_4 lo && totient_gap_check_window_1_120_pow_4 (lo + 16)

private theorem totient_gap_check_window_1_120_pow_5_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_5 lo = true) :
    ∀ i : Nat, i < 32 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_4 lo && totient_gap_check_window_1_120_pow_4 (lo + 16)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 16
  · exact totient_gap_check_window_1_120_pow_4_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_4_sound (lo + 16) hr (i - 16) (by omega)
    have hidx : lo + 16 + (i - 16) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_6 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_5 lo && totient_gap_check_window_1_120_pow_5 (lo + 32)

private theorem totient_gap_check_window_1_120_pow_6_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_6 lo = true) :
    ∀ i : Nat, i < 64 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_5 lo && totient_gap_check_window_1_120_pow_5 (lo + 32)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 32
  · exact totient_gap_check_window_1_120_pow_5_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_5_sound (lo + 32) hr (i - 32) (by omega)
    have hidx : lo + 32 + (i - 32) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_7 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_6 lo && totient_gap_check_window_1_120_pow_6 (lo + 64)

private theorem totient_gap_check_window_1_120_pow_7_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_7 lo = true) :
    ∀ i : Nat, i < 128 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_6 lo && totient_gap_check_window_1_120_pow_6 (lo + 64)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 64
  · exact totient_gap_check_window_1_120_pow_6_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_6_sound (lo + 64) hr (i - 64) (by omega)
    have hidx : lo + 64 + (i - 64) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_8 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_7 lo && totient_gap_check_window_1_120_pow_7 (lo + 128)

private theorem totient_gap_check_window_1_120_pow_8_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_8 lo = true) :
    ∀ i : Nat, i < 256 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_7 lo && totient_gap_check_window_1_120_pow_7 (lo + 128)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 128
  · exact totient_gap_check_window_1_120_pow_7_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_7_sound (lo + 128) hr (i - 128) (by omega)
    have hidx : lo + 128 + (i - 128) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_9 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_8 lo && totient_gap_check_window_1_120_pow_8 (lo + 256)

private theorem totient_gap_check_window_1_120_pow_9_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_9 lo = true) :
    ∀ i : Nat, i < 512 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_8 lo && totient_gap_check_window_1_120_pow_8 (lo + 256)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 256
  · exact totient_gap_check_window_1_120_pow_8_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_8_sound (lo + 256) hr (i - 256) (by omega)
    have hidx : lo + 256 + (i - 256) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_10 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_9 lo && totient_gap_check_window_1_120_pow_9 (lo + 512)

private theorem totient_gap_check_window_1_120_pow_10_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_10 lo = true) :
    ∀ i : Nat, i < 1024 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_9 lo && totient_gap_check_window_1_120_pow_9 (lo + 512)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 512
  · exact totient_gap_check_window_1_120_pow_9_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_9_sound (lo + 512) hr (i - 512) (by omega)
    have hidx : lo + 512 + (i - 512) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_11 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_10 lo && totient_gap_check_window_1_120_pow_10 (lo + 1024)

private theorem totient_gap_check_window_1_120_pow_11_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_11 lo = true) :
    ∀ i : Nat, i < 2048 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_10 lo && totient_gap_check_window_1_120_pow_10 (lo + 1024)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 1024
  · exact totient_gap_check_window_1_120_pow_10_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_10_sound (lo + 1024) hr (i - 1024) (by omega)
    have hidx : lo + 1024 + (i - 1024) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_12 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_11 lo && totient_gap_check_window_1_120_pow_11 (lo + 2048)

private theorem totient_gap_check_window_1_120_pow_12_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_12 lo = true) :
    ∀ i : Nat, i < 4096 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_11 lo && totient_gap_check_window_1_120_pow_11 (lo + 2048)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 2048
  · exact totient_gap_check_window_1_120_pow_11_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_11_sound (lo + 2048) hr (i - 2048) (by omega)
    have hidx : lo + 2048 + (i - 2048) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_13 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_12 lo && totient_gap_check_window_1_120_pow_12 (lo + 4096)

private theorem totient_gap_check_window_1_120_pow_13_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_13 lo = true) :
    ∀ i : Nat, i < 8192 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_12 lo && totient_gap_check_window_1_120_pow_12 (lo + 4096)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 4096
  · exact totient_gap_check_window_1_120_pow_12_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_12_sound (lo + 4096) hr (i - 4096) (by omega)
    have hidx : lo + 4096 + (i - 4096) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_14 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_13 lo && totient_gap_check_window_1_120_pow_13 (lo + 8192)

private theorem totient_gap_check_window_1_120_pow_14_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_14 lo = true) :
    ∀ i : Nat, i < 16384 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_13 lo && totient_gap_check_window_1_120_pow_13 (lo + 8192)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 8192
  · exact totient_gap_check_window_1_120_pow_13_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_13_sound (lo + 8192) hr (i - 8192) (by omega)
    have hidx : lo + 8192 + (i - 8192) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_15 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_14 lo && totient_gap_check_window_1_120_pow_14 (lo + 16384)

private theorem totient_gap_check_window_1_120_pow_15_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_15 lo = true) :
    ∀ i : Nat, i < 32768 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_14 lo && totient_gap_check_window_1_120_pow_14 (lo + 16384)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 16384
  · exact totient_gap_check_window_1_120_pow_14_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_14_sound (lo + 16384) hr (i - 16384) (by omega)
    have hidx : lo + 16384 + (i - 16384) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_16 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_15 lo && totient_gap_check_window_1_120_pow_15 (lo + 32768)

private theorem totient_gap_check_window_1_120_pow_16_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_16 lo = true) :
    ∀ i : Nat, i < 65536 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_15 lo && totient_gap_check_window_1_120_pow_15 (lo + 32768)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 32768
  · exact totient_gap_check_window_1_120_pow_15_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_15_sound (lo + 32768) hr (i - 32768) (by omega)
    have hidx : lo + 32768 + (i - 32768) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_17 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_16 lo && totient_gap_check_window_1_120_pow_16 (lo + 65536)

private theorem totient_gap_check_window_1_120_pow_17_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_17 lo = true) :
    ∀ i : Nat, i < 131072 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_16 lo && totient_gap_check_window_1_120_pow_16 (lo + 65536)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 65536
  · exact totient_gap_check_window_1_120_pow_16_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_16_sound (lo + 65536) hr (i - 65536) (by omega)
    have hidx : lo + 65536 + (i - 65536) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_18 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_17 lo && totient_gap_check_window_1_120_pow_17 (lo + 131072)

private theorem totient_gap_check_window_1_120_pow_18_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_18 lo = true) :
    ∀ i : Nat, i < 262144 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_17 lo && totient_gap_check_window_1_120_pow_17 (lo + 131072)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 131072
  · exact totient_gap_check_window_1_120_pow_17_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_17_sound (lo + 131072) hr (i - 131072) (by omega)
    have hidx : lo + 131072 + (i - 131072) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_19 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_18 lo && totient_gap_check_window_1_120_pow_18 (lo + 262144)

private theorem totient_gap_check_window_1_120_pow_19_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_19 lo = true) :
    ∀ i : Nat, i < 524288 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_18 lo && totient_gap_check_window_1_120_pow_18 (lo + 262144)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 262144
  · exact totient_gap_check_window_1_120_pow_18_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_18_sound (lo + 262144) hr (i - 262144) (by omega)
    have hidx : lo + 262144 + (i - 262144) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_20 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_19 lo && totient_gap_check_window_1_120_pow_19 (lo + 524288)

private theorem totient_gap_check_window_1_120_pow_20_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_20 lo = true) :
    ∀ i : Nat, i < 1048576 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_19 lo && totient_gap_check_window_1_120_pow_19 (lo + 524288)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 524288
  · exact totient_gap_check_window_1_120_pow_19_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_19_sound (lo + 524288) hr (i - 524288) (by omega)
    have hidx : lo + 524288 + (i - 524288) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_21 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_20 lo && totient_gap_check_window_1_120_pow_20 (lo + 1048576)

private theorem totient_gap_check_window_1_120_pow_21_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_21 lo = true) :
    ∀ i : Nat, i < 2097152 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_20 lo && totient_gap_check_window_1_120_pow_20 (lo + 1048576)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 1048576
  · exact totient_gap_check_window_1_120_pow_20_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_20_sound (lo + 1048576) hr (i - 1048576) (by omega)
    have hidx : lo + 1048576 + (i - 1048576) = lo + i := by omega
    rwa [hidx] at hres

def totient_gap_check_window_1_120_pow_22 (lo : Nat) : Bool :=
  totient_gap_check_window_1_120_pow_21 lo && totient_gap_check_window_1_120_pow_21 (lo + 2097152)

private theorem totient_gap_check_window_1_120_pow_22_sound (lo : Nat) (h : totient_gap_check_window_1_120_pow_22 lo = true) :
    ∀ i : Nat, i < 4194304 → (lo + i) * 977330308222705062435708544085600126 % 1329227995784915872903807060280344576 + (lo + i) * 123 < 1329227995784915872903807060280344576 := by
  have hsplit : (totient_gap_check_window_1_120_pow_21 lo && totient_gap_check_window_1_120_pow_21 (lo + 2097152)) = true := h
  rw [Bool.and_eq_true] at hsplit
  obtain ⟨hl, hr⟩ := hsplit
  intro i hi
  by_cases hcase : i < 2097152
  · exact totient_gap_check_window_1_120_pow_21_sound lo hl i hcase
  · have hres := totient_gap_check_window_1_120_pow_21_sound (lo + 2097152) hr (i - 2097152) (by omega)
    have hidx : lo + 2097152 + (i - 2097152) = lo + i := by omega
    rwa [hidx] at hres

private lemma phi_w17_0 : Nat.totient (1 + 1 + 0) = 1 := by
  have e : (1 + 1 + 0 : ℕ) = 2 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 2)]

private lemma phi_w17_1 : Nat.totient (1 + 1 + 1) = 2 := by
  have e : (1 + 1 + 1 : ℕ) = 3 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 3)]

private lemma phi_w17_2 : Nat.totient (1 + 1 + 2) = 2 := by
  have e : (1 + 1 + 2 : ℕ) = 4 := by norm_num
  rw [e]
  rw [show (4 : ℕ) = 2 ^ 2 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_3 : Nat.totient (1 + 1 + 3) = 4 := by
  have e : (1 + 1 + 3 : ℕ) = 5 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 5)]

private lemma phi_w17_4 : Nat.totient (1 + 1 + 4) = 2 := by
  have e : (1 + 1 + 4 : ℕ) = 6 := by norm_num
  rw [e]
  rw [show (6 : ℕ) = 2 * 3 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3)]

private lemma phi_w17_5 : Nat.totient (1 + 1 + 5) = 6 := by
  have e : (1 + 1 + 5 : ℕ) = 7 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 7)]

private lemma phi_w17_6 : Nat.totient (1 + 1 + 6) = 4 := by
  have e : (1 + 1 + 6 : ℕ) = 8 := by norm_num
  rw [e]
  rw [show (8 : ℕ) = 2 ^ 3 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3)]
  norm_num

private lemma phi_w17_7 : Nat.totient (1 + 1 + 7) = 6 := by
  have e : (1 + 1 + 7 : ℕ) = 9 := by norm_num
  rw [e]
  rw [show (9 : ℕ) = 3 ^ 2 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_8 : Nat.totient (1 + 1 + 8) = 4 := by
  have e : (1 + 1 + 8 : ℕ) = 10 := by norm_num
  rw [e]
  rw [show (10 : ℕ) = 2 * 5 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]

private lemma phi_w17_9 : Nat.totient (1 + 1 + 9) = 10 := by
  have e : (1 + 1 + 9 : ℕ) = 11 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w17_10 : Nat.totient (1 + 1 + 10) = 4 := by
  have e : (1 + 1 + 10 : ℕ) = 12 := by norm_num
  rw [e]
  rw [show (12 : ℕ) = 2 ^ 2 * 3 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3)]
  norm_num

private lemma phi_w17_11 : Nat.totient (1 + 1 + 11) = 12 := by
  have e : (1 + 1 + 11 : ℕ) = 13 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w17_12 : Nat.totient (1 + 1 + 12) = 6 := by
  have e : (1 + 1 + 12 : ℕ) = 14 := by norm_num
  rw [e]
  rw [show (14 : ℕ) = 2 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (7)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]

private lemma phi_w17_13 : Nat.totient (1 + 1 + 13) = 8 := by
  have e : (1 + 1 + 13 : ℕ) = 15 := by norm_num
  rw [e]
  rw [show (15 : ℕ) = 3 * 5 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]

private lemma phi_w17_14 : Nat.totient (1 + 1 + 14) = 8 := by
  have e : (1 + 1 + 14 : ℕ) = 16 := by norm_num
  rw [e]
  rw [show (16 : ℕ) = 2 ^ 4 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4)]
  norm_num

private lemma phi_w17_15 : Nat.totient (1 + 1 + 15) = 16 := by
  have e : (1 + 1 + 15 : ℕ) = 17 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w17_16 : Nat.totient (1 + 1 + 16) = 6 := by
  have e : (1 + 1 + 16 : ℕ) = 18 := by norm_num
  rw [e]
  rw [show (18 : ℕ) = 2 * (3 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 ^ 2)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_17 : Nat.totient (1 + 1 + 17) = 18 := by
  have e : (1 + 1 + 17 : ℕ) = 19 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 19)]

private lemma phi_w17_18 : Nat.totient (1 + 1 + 18) = 8 := by
  have e : (1 + 1 + 18 : ℕ) = 20 := by norm_num
  rw [e]
  rw [show (20 : ℕ) = 2 ^ 2 * 5 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w17_19 : Nat.totient (1 + 1 + 19) = 12 := by
  have e : (1 + 1 + 19 : ℕ) = 21 := by norm_num
  rw [e]
  rw [show (21 : ℕ) = 3 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (7)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]

private lemma phi_w17_20 : Nat.totient (1 + 1 + 20) = 10 := by
  have e : (1 + 1 + 20 : ℕ) = 22 := by norm_num
  rw [e]
  rw [show (22 : ℕ) = 2 * 11 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w17_21 : Nat.totient (1 + 1 + 21) = 22 := by
  have e : (1 + 1 + 21 : ℕ) = 23 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 23)]

private lemma phi_w17_22 : Nat.totient (1 + 1 + 22) = 8 := by
  have e : (1 + 1 + 22 : ℕ) = 24 := by norm_num
  rw [e]
  rw [show (24 : ℕ) = 2 ^ 3 * 3 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (3)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 3)]
  norm_num

private lemma phi_w17_23 : Nat.totient (1 + 1 + 23) = 20 := by
  have e : (1 + 1 + 23 : ℕ) = 25 := by norm_num
  rw [e]
  rw [show (25 : ℕ) = 5 ^ 2 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_24 : Nat.totient (1 + 1 + 24) = 12 := by
  have e : (1 + 1 + 24 : ℕ) = 26 := by norm_num
  rw [e]
  rw [show (26 : ℕ) = 2 * 13 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w17_25 : Nat.totient (1 + 1 + 25) = 18 := by
  have e : (1 + 1 + 25 : ℕ) = 27 := by norm_num
  rw [e]
  rw [show (27 : ℕ) = 3 ^ 3 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 3)]
  norm_num

private lemma phi_w17_26 : Nat.totient (1 + 1 + 26) = 12 := by
  have e : (1 + 1 + 26 : ℕ) = 28 := by norm_num
  rw [e]
  rw [show (28 : ℕ) = 2 ^ 2 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w17_27 : Nat.totient (1 + 1 + 27) = 28 := by
  have e : (1 + 1 + 27 : ℕ) = 29 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 29)]

private lemma phi_w17_28 : Nat.totient (1 + 1 + 28) = 8 := by
  have e : (1 + 1 + 28 : ℕ) = 30 := by norm_num
  rw [e]
  rw [show (30 : ℕ) = 2 * (3 * 5) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 5)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]

private lemma phi_w17_29 : Nat.totient (1 + 1 + 29) = 30 := by
  have e : (1 + 1 + 29 : ℕ) = 31 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 31)]

private lemma phi_w17_30 : Nat.totient (1 + 1 + 30) = 16 := by
  have e : (1 + 1 + 30 : ℕ) = 32 := by norm_num
  rw [e]
  rw [show (32 : ℕ) = 2 ^ 5 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 5)]
  norm_num

private lemma phi_w17_31 : Nat.totient (1 + 1 + 31) = 20 := by
  have e : (1 + 1 + 31 : ℕ) = 33 := by norm_num
  rw [e]
  rw [show (33 : ℕ) = 3 * 11 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w17_32 : Nat.totient (1 + 1 + 32) = 16 := by
  have e : (1 + 1 + 32 : ℕ) = 34 := by norm_num
  rw [e]
  rw [show (34 : ℕ) = 2 * 17 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (17)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w17_33 : Nat.totient (1 + 1 + 33) = 24 := by
  have e : (1 + 1 + 33 : ℕ) = 35 := by norm_num
  rw [e]
  rw [show (35 : ℕ) = 5 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (7)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]

private lemma phi_w17_34 : Nat.totient (1 + 1 + 34) = 12 := by
  have e : (1 + 1 + 34 : ℕ) = 36 := by norm_num
  rw [e]
  rw [show (36 : ℕ) = 2 ^ 2 * (3 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 ^ 2)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_35 : Nat.totient (1 + 1 + 35) = 36 := by
  have e : (1 + 1 + 35 : ℕ) = 37 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 37)]

private lemma phi_w17_36 : Nat.totient (1 + 1 + 36) = 18 := by
  have e : (1 + 1 + 36 : ℕ) = 38 := by norm_num
  rw [e]
  rw [show (38 : ℕ) = 2 * 19 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (19)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]

private lemma phi_w17_37 : Nat.totient (1 + 1 + 37) = 24 := by
  have e : (1 + 1 + 37 : ℕ) = 39 := by norm_num
  rw [e]
  rw [show (39 : ℕ) = 3 * 13 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w17_38 : Nat.totient (1 + 1 + 38) = 16 := by
  have e : (1 + 1 + 38 : ℕ) = 40 := by norm_num
  rw [e]
  rw [show (40 : ℕ) = 2 ^ 3 * 5 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w17_39 : Nat.totient (1 + 1 + 39) = 40 := by
  have e : (1 + 1 + 39 : ℕ) = 41 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 41)]

private lemma phi_w17_40 : Nat.totient (1 + 1 + 40) = 12 := by
  have e : (1 + 1 + 40 : ℕ) = 42 := by norm_num
  rw [e]
  rw [show (42 : ℕ) = 2 * (3 * 7) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 7)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (7)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]

private lemma phi_w17_41 : Nat.totient (1 + 1 + 41) = 42 := by
  have e : (1 + 1 + 41 : ℕ) = 43 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 43)]

private lemma phi_w17_42 : Nat.totient (1 + 1 + 42) = 20 := by
  have e : (1 + 1 + 42 : ℕ) = 44 := by norm_num
  rw [e]
  rw [show (44 : ℕ) = 2 ^ 2 * 11 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (11)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]
  norm_num

private lemma phi_w17_43 : Nat.totient (1 + 1 + 43) = 24 := by
  have e : (1 + 1 + 43 : ℕ) = 45 := by norm_num
  rw [e]
  rw [show (45 : ℕ) = 3 ^ 2 * 5 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w17_44 : Nat.totient (1 + 1 + 44) = 22 := by
  have e : (1 + 1 + 44 : ℕ) = 46 := by norm_num
  rw [e]
  rw [show (46 : ℕ) = 2 * 23 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (23)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]

private lemma phi_w17_45 : Nat.totient (1 + 1 + 45) = 46 := by
  have e : (1 + 1 + 45 : ℕ) = 47 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 47)]

private lemma phi_w17_46 : Nat.totient (1 + 1 + 46) = 16 := by
  have e : (1 + 1 + 46 : ℕ) = 48 := by norm_num
  rw [e]
  rw [show (48 : ℕ) = 2 ^ 4 * 3 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 4) (3)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4),
    Nat.totient_prime (by norm_num : Nat.Prime 3)]
  norm_num

private lemma phi_w17_47 : Nat.totient (1 + 1 + 47) = 42 := by
  have e : (1 + 1 + 47 : ℕ) = 49 := by norm_num
  rw [e]
  rw [show (49 : ℕ) = 7 ^ 2 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 7) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_48 : Nat.totient (1 + 1 + 48) = 20 := by
  have e : (1 + 1 + 48 : ℕ) = 50 := by norm_num
  rw [e]
  rw [show (50 : ℕ) = 2 * (5 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5 ^ 2)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_49 : Nat.totient (1 + 1 + 49) = 32 := by
  have e : (1 + 1 + 49 : ℕ) = 51 := by norm_num
  rw [e]
  rw [show (51 : ℕ) = 3 * 17 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (17)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w17_50 : Nat.totient (1 + 1 + 50) = 24 := by
  have e : (1 + 1 + 50 : ℕ) = 52 := by norm_num
  rw [e]
  rw [show (52 : ℕ) = 2 ^ 2 * 13 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (13)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]
  norm_num

private lemma phi_w17_51 : Nat.totient (1 + 1 + 51) = 52 := by
  have e : (1 + 1 + 51 : ℕ) = 53 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 53)]

private lemma phi_w17_52 : Nat.totient (1 + 1 + 52) = 18 := by
  have e : (1 + 1 + 52 : ℕ) = 54 := by norm_num
  rw [e]
  rw [show (54 : ℕ) = 2 * (3 ^ 3) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 ^ 3)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 3)]
  norm_num

private lemma phi_w17_53 : Nat.totient (1 + 1 + 53) = 40 := by
  have e : (1 + 1 + 53 : ℕ) = 55 := by norm_num
  rw [e]
  rw [show (55 : ℕ) = 5 * 11 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w17_54 : Nat.totient (1 + 1 + 54) = 24 := by
  have e : (1 + 1 + 54 : ℕ) = 56 := by norm_num
  rw [e]
  rw [show (56 : ℕ) = 2 ^ 3 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w17_55 : Nat.totient (1 + 1 + 55) = 36 := by
  have e : (1 + 1 + 55 : ℕ) = 57 := by norm_num
  rw [e]
  rw [show (57 : ℕ) = 3 * 19 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (19)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]

private lemma phi_w17_56 : Nat.totient (1 + 1 + 56) = 28 := by
  have e : (1 + 1 + 56 : ℕ) = 58 := by norm_num
  rw [e]
  rw [show (58 : ℕ) = 2 * 29 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (29)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 29)]

private lemma phi_w17_57 : Nat.totient (1 + 1 + 57) = 58 := by
  have e : (1 + 1 + 57 : ℕ) = 59 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 59)]

private lemma phi_w17_58 : Nat.totient (1 + 1 + 58) = 16 := by
  have e : (1 + 1 + 58 : ℕ) = 60 := by norm_num
  rw [e]
  rw [show (60 : ℕ) = 2 ^ 2 * (3 * 5) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 * 5)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w17_59 : Nat.totient (1 + 1 + 59) = 60 := by
  have e : (1 + 1 + 59 : ℕ) = 61 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 61)]

private lemma phi_w17_60 : Nat.totient (1 + 1 + 60) = 30 := by
  have e : (1 + 1 + 60 : ℕ) = 62 := by norm_num
  rw [e]
  rw [show (62 : ℕ) = 2 * 31 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (31)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 31)]

private lemma phi_w17_61 : Nat.totient (1 + 1 + 61) = 36 := by
  have e : (1 + 1 + 61 : ℕ) = 63 := by norm_num
  rw [e]
  rw [show (63 : ℕ) = 3 ^ 2 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w17_62 : Nat.totient (1 + 1 + 62) = 32 := by
  have e : (1 + 1 + 62 : ℕ) = 64 := by norm_num
  rw [e]
  rw [show (64 : ℕ) = 2 ^ 6 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 6)]
  norm_num

private lemma phi_w17_63 : Nat.totient (1 + 1 + 63) = 48 := by
  have e : (1 + 1 + 63 : ℕ) = 65 := by norm_num
  rw [e]
  rw [show (65 : ℕ) = 5 * 13 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w17_64 : Nat.totient (1 + 1 + 64) = 20 := by
  have e : (1 + 1 + 64 : ℕ) = 66 := by norm_num
  rw [e]
  rw [show (66 : ℕ) = 2 * (3 * 11) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w17_65 : Nat.totient (1 + 1 + 65) = 66 := by
  have e : (1 + 1 + 65 : ℕ) = 67 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 67)]

private lemma phi_w17_66 : Nat.totient (1 + 1 + 66) = 32 := by
  have e : (1 + 1 + 66 : ℕ) = 68 := by norm_num
  rw [e]
  rw [show (68 : ℕ) = 2 ^ 2 * 17 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (17)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]
  norm_num

private lemma phi_w17_67 : Nat.totient (1 + 1 + 67) = 44 := by
  have e : (1 + 1 + 67 : ℕ) = 69 := by norm_num
  rw [e]
  rw [show (69 : ℕ) = 3 * 23 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (23)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]

private lemma phi_w17_68 : Nat.totient (1 + 1 + 68) = 24 := by
  have e : (1 + 1 + 68 : ℕ) = 70 := by norm_num
  rw [e]
  rw [show (70 : ℕ) = 2 * (5 * 7) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5 * 7)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (7)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]

private lemma phi_w17_69 : Nat.totient (1 + 1 + 69) = 70 := by
  have e : (1 + 1 + 69 : ℕ) = 71 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 71)]

private lemma phi_w17_70 : Nat.totient (1 + 1 + 70) = 24 := by
  have e : (1 + 1 + 70 : ℕ) = 72 := by norm_num
  rw [e]
  rw [show (72 : ℕ) = 2 ^ 3 * (3 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (3 ^ 2)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_71 : Nat.totient (1 + 1 + 71) = 72 := by
  have e : (1 + 1 + 71 : ℕ) = 73 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 73)]

private lemma phi_w17_72 : Nat.totient (1 + 1 + 72) = 36 := by
  have e : (1 + 1 + 72 : ℕ) = 74 := by norm_num
  rw [e]
  rw [show (74 : ℕ) = 2 * 37 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (37)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 37)]

private lemma phi_w17_73 : Nat.totient (1 + 1 + 73) = 40 := by
  have e : (1 + 1 + 73 : ℕ) = 75 := by norm_num
  rw [e]
  rw [show (75 : ℕ) = 3 * (5 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5 ^ 2)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_74 : Nat.totient (1 + 1 + 74) = 36 := by
  have e : (1 + 1 + 74 : ℕ) = 76 := by norm_num
  rw [e]
  rw [show (76 : ℕ) = 2 ^ 2 * 19 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (19)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]
  norm_num

private lemma phi_w17_75 : Nat.totient (1 + 1 + 75) = 60 := by
  have e : (1 + 1 + 75 : ℕ) = 77 := by norm_num
  rw [e]
  rw [show (77 : ℕ) = 7 * 11 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w17_76 : Nat.totient (1 + 1 + 76) = 24 := by
  have e : (1 + 1 + 76 : ℕ) = 78 := by norm_num
  rw [e]
  rw [show (78 : ℕ) = 2 * (3 * 13) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 13)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w17_77 : Nat.totient (1 + 1 + 77) = 78 := by
  have e : (1 + 1 + 77 : ℕ) = 79 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 79)]

private lemma phi_w17_78 : Nat.totient (1 + 1 + 78) = 32 := by
  have e : (1 + 1 + 78 : ℕ) = 80 := by norm_num
  rw [e]
  rw [show (80 : ℕ) = 2 ^ 4 * 5 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 4) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w17_79 : Nat.totient (1 + 1 + 79) = 54 := by
  have e : (1 + 1 + 79 : ℕ) = 81 := by norm_num
  rw [e]
  rw [show (81 : ℕ) = 3 ^ 4 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 4)]
  norm_num

private lemma phi_w17_80 : Nat.totient (1 + 1 + 80) = 40 := by
  have e : (1 + 1 + 80 : ℕ) = 82 := by norm_num
  rw [e]
  rw [show (82 : ℕ) = 2 * 41 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (41)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 41)]

private lemma phi_w17_81 : Nat.totient (1 + 1 + 81) = 82 := by
  have e : (1 + 1 + 81 : ℕ) = 83 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 83)]

private lemma phi_w17_82 : Nat.totient (1 + 1 + 82) = 24 := by
  have e : (1 + 1 + 82 : ℕ) = 84 := by norm_num
  rw [e]
  rw [show (84 : ℕ) = 2 ^ 2 * (3 * 7) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 * 7)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w17_83 : Nat.totient (1 + 1 + 83) = 64 := by
  have e : (1 + 1 + 83 : ℕ) = 85 := by norm_num
  rw [e]
  rw [show (85 : ℕ) = 5 * 17 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (17)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w17_84 : Nat.totient (1 + 1 + 84) = 42 := by
  have e : (1 + 1 + 84 : ℕ) = 86 := by norm_num
  rw [e]
  rw [show (86 : ℕ) = 2 * 43 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (43)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 43)]

private lemma phi_w17_85 : Nat.totient (1 + 1 + 85) = 56 := by
  have e : (1 + 1 + 85 : ℕ) = 87 := by norm_num
  rw [e]
  rw [show (87 : ℕ) = 3 * 29 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (29)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 29)]

private lemma phi_w17_86 : Nat.totient (1 + 1 + 86) = 40 := by
  have e : (1 + 1 + 86 : ℕ) = 88 := by norm_num
  rw [e]
  rw [show (88 : ℕ) = 2 ^ 3 * 11 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (11)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]
  norm_num

private lemma phi_w17_87 : Nat.totient (1 + 1 + 87) = 88 := by
  have e : (1 + 1 + 87 : ℕ) = 89 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 89)]

private lemma phi_w17_88 : Nat.totient (1 + 1 + 88) = 24 := by
  have e : (1 + 1 + 88 : ℕ) = 90 := by norm_num
  rw [e]
  rw [show (90 : ℕ) = 2 * (3 ^ 2 * 5) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 ^ 2 * 5)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (5)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w17_89 : Nat.totient (1 + 1 + 89) = 72 := by
  have e : (1 + 1 + 89 : ℕ) = 91 := by norm_num
  rw [e]
  rw [show (91 : ℕ) = 7 * 13 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w17_90 : Nat.totient (1 + 1 + 90) = 44 := by
  have e : (1 + 1 + 90 : ℕ) = 92 := by norm_num
  rw [e]
  rw [show (92 : ℕ) = 2 ^ 2 * 23 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (23)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]
  norm_num

private lemma phi_w17_91 : Nat.totient (1 + 1 + 91) = 60 := by
  have e : (1 + 1 + 91 : ℕ) = 93 := by norm_num
  rw [e]
  rw [show (93 : ℕ) = 3 * 31 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (31)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 31)]

private lemma phi_w17_92 : Nat.totient (1 + 1 + 92) = 46 := by
  have e : (1 + 1 + 92 : ℕ) = 94 := by norm_num
  rw [e]
  rw [show (94 : ℕ) = 2 * 47 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (47)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 47)]

private lemma phi_w17_93 : Nat.totient (1 + 1 + 93) = 72 := by
  have e : (1 + 1 + 93 : ℕ) = 95 := by norm_num
  rw [e]
  rw [show (95 : ℕ) = 5 * 19 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (19)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]

private lemma phi_w17_94 : Nat.totient (1 + 1 + 94) = 32 := by
  have e : (1 + 1 + 94 : ℕ) = 96 := by norm_num
  rw [e]
  rw [show (96 : ℕ) = 2 ^ 5 * 3 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 5) (3)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 5),
    Nat.totient_prime (by norm_num : Nat.Prime 3)]
  norm_num

private lemma phi_w17_95 : Nat.totient (1 + 1 + 95) = 96 := by
  have e : (1 + 1 + 95 : ℕ) = 97 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 97)]

private lemma phi_w17_96 : Nat.totient (1 + 1 + 96) = 42 := by
  have e : (1 + 1 + 96 : ℕ) = 98 := by norm_num
  rw [e]
  rw [show (98 : ℕ) = 2 * (7 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (7 ^ 2)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 7) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_97 : Nat.totient (1 + 1 + 97) = 60 := by
  have e : (1 + 1 + 97 : ℕ) = 99 := by norm_num
  rw [e]
  rw [show (99 : ℕ) = 3 ^ 2 * 11 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (11)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]
  norm_num

private lemma phi_w17_98 : Nat.totient (1 + 1 + 98) = 40 := by
  have e : (1 + 1 + 98 : ℕ) = 100 := by norm_num
  rw [e]
  rw [show (100 : ℕ) = 2 ^ 2 * (5 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (5 ^ 2)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w17_99 : Nat.totient (1 + 1 + 99) = 100 := by
  have e : (1 + 1 + 99 : ℕ) = 101 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 101)]

private lemma phi_w17_100 : Nat.totient (1 + 1 + 100) = 32 := by
  have e : (1 + 1 + 100 : ℕ) = 102 := by norm_num
  rw [e]
  rw [show (102 : ℕ) = 2 * (3 * 17) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 17)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (17)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w17_101 : Nat.totient (1 + 1 + 101) = 102 := by
  have e : (1 + 1 + 101 : ℕ) = 103 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 103)]

private lemma phi_w17_102 : Nat.totient (1 + 1 + 102) = 48 := by
  have e : (1 + 1 + 102 : ℕ) = 104 := by norm_num
  rw [e]
  rw [show (104 : ℕ) = 2 ^ 3 * 13 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (13)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]
  norm_num

private lemma phi_w17_103 : Nat.totient (1 + 1 + 103) = 48 := by
  have e : (1 + 1 + 103 : ℕ) = 105 := by norm_num
  rw [e]
  rw [show (105 : ℕ) = 3 * (5 * 7) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5 * 7)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (7)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]

private lemma phi_w17_104 : Nat.totient (1 + 1 + 104) = 52 := by
  have e : (1 + 1 + 104 : ℕ) = 106 := by norm_num
  rw [e]
  rw [show (106 : ℕ) = 2 * 53 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (53)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 53)]

private lemma phi_w17_105 : Nat.totient (1 + 1 + 105) = 106 := by
  have e : (1 + 1 + 105 : ℕ) = 107 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 107)]

private lemma phi_w17_106 : Nat.totient (1 + 1 + 106) = 36 := by
  have e : (1 + 1 + 106 : ℕ) = 108 := by norm_num
  rw [e]
  rw [show (108 : ℕ) = 2 ^ 2 * (3 ^ 3) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 ^ 3)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 3)]
  norm_num

private lemma phi_w17_107 : Nat.totient (1 + 1 + 107) = 108 := by
  have e : (1 + 1 + 107 : ℕ) = 109 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 109)]

private lemma phi_w17_108 : Nat.totient (1 + 1 + 108) = 40 := by
  have e : (1 + 1 + 108 : ℕ) = 110 := by norm_num
  rw [e]
  rw [show (110 : ℕ) = 2 * (5 * 11) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w17_109 : Nat.totient (1 + 1 + 109) = 72 := by
  have e : (1 + 1 + 109 : ℕ) = 111 := by norm_num
  rw [e]
  rw [show (111 : ℕ) = 3 * 37 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (37)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 37)]

private lemma phi_w17_110 : Nat.totient (1 + 1 + 110) = 48 := by
  have e : (1 + 1 + 110 : ℕ) = 112 := by norm_num
  rw [e]
  rw [show (112 : ℕ) = 2 ^ 4 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 4) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w17_111 : Nat.totient (1 + 1 + 111) = 112 := by
  have e : (1 + 1 + 111 : ℕ) = 113 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 113)]

private lemma phi_w17_112 : Nat.totient (1 + 1 + 112) = 36 := by
  have e : (1 + 1 + 112 : ℕ) = 114 := by norm_num
  rw [e]
  rw [show (114 : ℕ) = 2 * (3 * 19) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 19)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (19)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]

private lemma phi_w17_113 : Nat.totient (1 + 1 + 113) = 88 := by
  have e : (1 + 1 + 113 : ℕ) = 115 := by norm_num
  rw [e]
  rw [show (115 : ℕ) = 5 * 23 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (23)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]

private lemma phi_w17_114 : Nat.totient (1 + 1 + 114) = 56 := by
  have e : (1 + 1 + 114 : ℕ) = 116 := by norm_num
  rw [e]
  rw [show (116 : ℕ) = 2 ^ 2 * 29 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (29)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 29)]
  norm_num

private lemma phi_w17_115 : Nat.totient (1 + 1 + 115) = 72 := by
  have e : (1 + 1 + 115 : ℕ) = 117 := by norm_num
  rw [e]
  rw [show (117 : ℕ) = 3 ^ 2 * 13 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (13)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]
  norm_num

private lemma phi_w17_116 : Nat.totient (1 + 1 + 116) = 58 := by
  have e : (1 + 1 + 116 : ℕ) = 118 := by norm_num
  rw [e]
  rw [show (118 : ℕ) = 2 * 59 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (59)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 59)]

private lemma phi_w17_117 : Nat.totient (1 + 1 + 117) = 96 := by
  have e : (1 + 1 + 117 : ℕ) = 119 := by norm_num
  rw [e]
  rw [show (119 : ℕ) = 7 * 17 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (17)),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w17_118 : Nat.totient (1 + 1 + 118) = 32 := by
  have e : (1 + 1 + 118 : ℕ) = 120 := by norm_num
  rw [e]
  rw [show (120 : ℕ) = 2 ^ 3 * (3 * 5) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (3 * 5)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w17_119 : Nat.totient (1 + 1 + 119) = 110 := by
  have e : (1 + 1 + 119 : ℕ) = 121 := by norm_num
  rw [e]
  rw [show (121 : ℕ) = 11 ^ 2 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 11) (by norm_num : 0 < 2)]
  norm_num

/-- **Wave-17 window residue, kernel-evaluated.**  The `K = 120` carry
residue at shift `N = 1`: every window totient (all ≤ 112) is certified by
its prime factorization and rewritten to a literal before arithmetic. -/
theorem totient_carry_residue_window_1_120_eq :
    (∑ r ∈ Finset.Icc 1 120, Nat.totient (1 + r) * 2 ^ (120 - r)) % 2 ^ 120
      = 977330308222705062435708544085600126 := by
  rw [totient_carry_sum_eq_range 1 120]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, phi_w17_0, phi_w17_1, phi_w17_2, phi_w17_3, phi_w17_4, phi_w17_5, phi_w17_6, phi_w17_7, phi_w17_8, phi_w17_9, phi_w17_10, phi_w17_11, phi_w17_12, phi_w17_13, phi_w17_14, phi_w17_15, phi_w17_16, phi_w17_17, phi_w17_18, phi_w17_19, phi_w17_20, phi_w17_21, phi_w17_22, phi_w17_23, phi_w17_24, phi_w17_25, phi_w17_26, phi_w17_27, phi_w17_28, phi_w17_29, phi_w17_30, phi_w17_31, phi_w17_32, phi_w17_33, phi_w17_34, phi_w17_35, phi_w17_36, phi_w17_37, phi_w17_38, phi_w17_39, phi_w17_40, phi_w17_41, phi_w17_42, phi_w17_43, phi_w17_44, phi_w17_45, phi_w17_46, phi_w17_47, phi_w17_48, phi_w17_49, phi_w17_50, phi_w17_51, phi_w17_52, phi_w17_53, phi_w17_54, phi_w17_55, phi_w17_56, phi_w17_57, phi_w17_58, phi_w17_59, phi_w17_60, phi_w17_61, phi_w17_62, phi_w17_63, phi_w17_64, phi_w17_65, phi_w17_66, phi_w17_67, phi_w17_68, phi_w17_69, phi_w17_70, phi_w17_71, phi_w17_72, phi_w17_73, phi_w17_74, phi_w17_75, phi_w17_76, phi_w17_77, phi_w17_78, phi_w17_79, phi_w17_80, phi_w17_81, phi_w17_82, phi_w17_83, phi_w17_84, phi_w17_85, phi_w17_86, phi_w17_87, phi_w17_88, phi_w17_89, phi_w17_90, phi_w17_91, phi_w17_92, phi_w17_93, phi_w17_94, phi_w17_95, phi_w17_96, phi_w17_97, phi_w17_98, phi_w17_99, phi_w17_100, phi_w17_101, phi_w17_102, phi_w17_103, phi_w17_104, phi_w17_105, phi_w17_106, phi_w17_107, phi_w17_108, phi_w17_109, phi_w17_110, phi_w17_111, phi_w17_112, phi_w17_113, phi_w17_114, phi_w17_115, phi_w17_116, phi_w17_117, phi_w17_118, phi_w17_119]
  norm_num


private lemma phi_w240_120 : Nat.totient (1 + 1 + 120) = 60 := by
  have e : (1 + 1 + 120 : ℕ) = 122 := by norm_num
  rw [e]
  rw [show (122 : ℕ) = 2 * 61 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (61)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 61)]

private lemma phi_w240_121 : Nat.totient (1 + 1 + 121) = 80 := by
  have e : (1 + 1 + 121 : ℕ) = 123 := by norm_num
  rw [e]
  rw [show (123 : ℕ) = 3 * 41 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (41)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 41)]

private lemma phi_w240_122 : Nat.totient (1 + 1 + 122) = 60 := by
  have e : (1 + 1 + 122 : ℕ) = 124 := by norm_num
  rw [e]
  rw [show (124 : ℕ) = 2 ^ 2 * 31 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (31)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 31)]
  norm_num

private lemma phi_w240_123 : Nat.totient (1 + 1 + 123) = 100 := by
  have e : (1 + 1 + 123 : ℕ) = 125 := by norm_num
  rw [e]
  rw [show (125 : ℕ) = 5 ^ 3 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 3)]
  norm_num

private lemma phi_w240_124 : Nat.totient (1 + 1 + 124) = 36 := by
  have e : (1 + 1 + 124 : ℕ) = 126 := by norm_num
  rw [e]
  rw [show (126 : ℕ) = 2 * (3 ^ 2 * 7) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 ^ 2 * 7)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (7)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w240_125 : Nat.totient (1 + 1 + 125) = 126 := by
  have e : (1 + 1 + 125 : ℕ) = 127 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 127)]

private lemma phi_w240_126 : Nat.totient (1 + 1 + 126) = 64 := by
  have e : (1 + 1 + 126 : ℕ) = 128 := by norm_num
  rw [e]
  rw [show (128 : ℕ) = 2 ^ 7 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 7)]
  norm_num

private lemma phi_w240_127 : Nat.totient (1 + 1 + 127) = 84 := by
  have e : (1 + 1 + 127 : ℕ) = 129 := by norm_num
  rw [e]
  rw [show (129 : ℕ) = 3 * 43 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (43)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 43)]

private lemma phi_w240_128 : Nat.totient (1 + 1 + 128) = 48 := by
  have e : (1 + 1 + 128 : ℕ) = 130 := by norm_num
  rw [e]
  rw [show (130 : ℕ) = 2 * (5 * 13) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5 * 13)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w240_129 : Nat.totient (1 + 1 + 129) = 130 := by
  have e : (1 + 1 + 129 : ℕ) = 131 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 131)]

private lemma phi_w240_130 : Nat.totient (1 + 1 + 130) = 40 := by
  have e : (1 + 1 + 130 : ℕ) = 132 := by norm_num
  rw [e]
  rw [show (132 : ℕ) = 2 ^ 2 * (3 * 11) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (11)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]
  norm_num

private lemma phi_w240_131 : Nat.totient (1 + 1 + 131) = 108 := by
  have e : (1 + 1 + 131 : ℕ) = 133 := by norm_num
  rw [e]
  rw [show (133 : ℕ) = 7 * 19 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (19)),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]

private lemma phi_w240_132 : Nat.totient (1 + 1 + 132) = 66 := by
  have e : (1 + 1 + 132 : ℕ) = 134 := by norm_num
  rw [e]
  rw [show (134 : ℕ) = 2 * 67 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (67)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 67)]

private lemma phi_w240_133 : Nat.totient (1 + 1 + 133) = 72 := by
  have e : (1 + 1 + 133 : ℕ) = 135 := by norm_num
  rw [e]
  rw [show (135 : ℕ) = 3 ^ 3 * 5 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 3) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w240_134 : Nat.totient (1 + 1 + 134) = 64 := by
  have e : (1 + 1 + 134 : ℕ) = 136 := by norm_num
  rw [e]
  rw [show (136 : ℕ) = 2 ^ 3 * 17 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (17)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]
  norm_num

private lemma phi_w240_135 : Nat.totient (1 + 1 + 135) = 136 := by
  have e : (1 + 1 + 135 : ℕ) = 137 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 137)]

private lemma phi_w240_136 : Nat.totient (1 + 1 + 136) = 44 := by
  have e : (1 + 1 + 136 : ℕ) = 138 := by norm_num
  rw [e]
  rw [show (138 : ℕ) = 2 * (3 * 23) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 23)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (23)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]

private lemma phi_w240_137 : Nat.totient (1 + 1 + 137) = 138 := by
  have e : (1 + 1 + 137 : ℕ) = 139 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 139)]

private lemma phi_w240_138 : Nat.totient (1 + 1 + 138) = 48 := by
  have e : (1 + 1 + 138 : ℕ) = 140 := by norm_num
  rw [e]
  rw [show (140 : ℕ) = 2 ^ 2 * (5 * 7) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (5 * 7)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w240_139 : Nat.totient (1 + 1 + 139) = 92 := by
  have e : (1 + 1 + 139 : ℕ) = 141 := by norm_num
  rw [e]
  rw [show (141 : ℕ) = 3 * 47 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (47)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 47)]

private lemma phi_w240_140 : Nat.totient (1 + 1 + 140) = 70 := by
  have e : (1 + 1 + 140 : ℕ) = 142 := by norm_num
  rw [e]
  rw [show (142 : ℕ) = 2 * 71 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (71)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 71)]

private lemma phi_w240_141 : Nat.totient (1 + 1 + 141) = 120 := by
  have e : (1 + 1 + 141 : ℕ) = 143 := by norm_num
  rw [e]
  rw [show (143 : ℕ) = 11 * 13 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (11) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 11),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w240_142 : Nat.totient (1 + 1 + 142) = 48 := by
  have e : (1 + 1 + 142 : ℕ) = 144 := by norm_num
  rw [e]
  rw [show (144 : ℕ) = 2 ^ 4 * (3 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 4) (3 ^ 2)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w240_143 : Nat.totient (1 + 1 + 143) = 112 := by
  have e : (1 + 1 + 143 : ℕ) = 145 := by norm_num
  rw [e]
  rw [show (145 : ℕ) = 5 * 29 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (29)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 29)]

private lemma phi_w240_144 : Nat.totient (1 + 1 + 144) = 72 := by
  have e : (1 + 1 + 144 : ℕ) = 146 := by norm_num
  rw [e]
  rw [show (146 : ℕ) = 2 * 73 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (73)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 73)]

private lemma phi_w240_145 : Nat.totient (1 + 1 + 145) = 84 := by
  have e : (1 + 1 + 145 : ℕ) = 147 := by norm_num
  rw [e]
  rw [show (147 : ℕ) = 3 * (7 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (7 ^ 2)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 7) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w240_146 : Nat.totient (1 + 1 + 146) = 72 := by
  have e : (1 + 1 + 146 : ℕ) = 148 := by norm_num
  rw [e]
  rw [show (148 : ℕ) = 2 ^ 2 * 37 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (37)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 37)]
  norm_num

private lemma phi_w240_147 : Nat.totient (1 + 1 + 147) = 148 := by
  have e : (1 + 1 + 147 : ℕ) = 149 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 149)]

private lemma phi_w240_148 : Nat.totient (1 + 1 + 148) = 40 := by
  have e : (1 + 1 + 148 : ℕ) = 150 := by norm_num
  rw [e]
  rw [show (150 : ℕ) = 2 * (3 * (5 ^ 2)) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * (5 ^ 2))),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5 ^ 2)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w240_149 : Nat.totient (1 + 1 + 149) = 150 := by
  have e : (1 + 1 + 149 : ℕ) = 151 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 151)]

private lemma phi_w240_150 : Nat.totient (1 + 1 + 150) = 72 := by
  have e : (1 + 1 + 150 : ℕ) = 152 := by norm_num
  rw [e]
  rw [show (152 : ℕ) = 2 ^ 3 * 19 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (19)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]
  norm_num

private lemma phi_w240_151 : Nat.totient (1 + 1 + 151) = 96 := by
  have e : (1 + 1 + 151 : ℕ) = 153 := by norm_num
  rw [e]
  rw [show (153 : ℕ) = 3 ^ 2 * 17 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (17)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]
  norm_num

private lemma phi_w240_152 : Nat.totient (1 + 1 + 152) = 60 := by
  have e : (1 + 1 + 152 : ℕ) = 154 := by norm_num
  rw [e]
  rw [show (154 : ℕ) = 2 * (7 * 11) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (7 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w240_153 : Nat.totient (1 + 1 + 153) = 120 := by
  have e : (1 + 1 + 153 : ℕ) = 155 := by norm_num
  rw [e]
  rw [show (155 : ℕ) = 5 * 31 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (31)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 31)]

private lemma phi_w240_154 : Nat.totient (1 + 1 + 154) = 48 := by
  have e : (1 + 1 + 154 : ℕ) = 156 := by norm_num
  rw [e]
  rw [show (156 : ℕ) = 2 ^ 2 * (3 * 13) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 * 13)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (13)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]
  norm_num

private lemma phi_w240_155 : Nat.totient (1 + 1 + 155) = 156 := by
  have e : (1 + 1 + 155 : ℕ) = 157 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 157)]

private lemma phi_w240_156 : Nat.totient (1 + 1 + 156) = 78 := by
  have e : (1 + 1 + 156 : ℕ) = 158 := by norm_num
  rw [e]
  rw [show (158 : ℕ) = 2 * 79 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (79)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 79)]

private lemma phi_w240_157 : Nat.totient (1 + 1 + 157) = 104 := by
  have e : (1 + 1 + 157 : ℕ) = 159 := by norm_num
  rw [e]
  rw [show (159 : ℕ) = 3 * 53 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (53)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 53)]

private lemma phi_w240_158 : Nat.totient (1 + 1 + 158) = 64 := by
  have e : (1 + 1 + 158 : ℕ) = 160 := by norm_num
  rw [e]
  rw [show (160 : ℕ) = 2 ^ 5 * 5 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 5) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 5),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w240_159 : Nat.totient (1 + 1 + 159) = 132 := by
  have e : (1 + 1 + 159 : ℕ) = 161 := by norm_num
  rw [e]
  rw [show (161 : ℕ) = 7 * 23 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (23)),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]

private lemma phi_w240_160 : Nat.totient (1 + 1 + 160) = 54 := by
  have e : (1 + 1 + 160 : ℕ) = 162 := by norm_num
  rw [e]
  rw [show (162 : ℕ) = 2 * (3 ^ 4) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 ^ 4)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 4)]
  norm_num

private lemma phi_w240_161 : Nat.totient (1 + 1 + 161) = 162 := by
  have e : (1 + 1 + 161 : ℕ) = 163 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 163)]

private lemma phi_w240_162 : Nat.totient (1 + 1 + 162) = 80 := by
  have e : (1 + 1 + 162 : ℕ) = 164 := by norm_num
  rw [e]
  rw [show (164 : ℕ) = 2 ^ 2 * 41 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (41)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 41)]
  norm_num

private lemma phi_w240_163 : Nat.totient (1 + 1 + 163) = 80 := by
  have e : (1 + 1 + 163 : ℕ) = 165 := by norm_num
  rw [e]
  rw [show (165 : ℕ) = 3 * (5 * 11) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w240_164 : Nat.totient (1 + 1 + 164) = 82 := by
  have e : (1 + 1 + 164 : ℕ) = 166 := by norm_num
  rw [e]
  rw [show (166 : ℕ) = 2 * 83 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (83)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 83)]

private lemma phi_w240_165 : Nat.totient (1 + 1 + 165) = 166 := by
  have e : (1 + 1 + 165 : ℕ) = 167 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 167)]

private lemma phi_w240_166 : Nat.totient (1 + 1 + 166) = 48 := by
  have e : (1 + 1 + 166 : ℕ) = 168 := by norm_num
  rw [e]
  rw [show (168 : ℕ) = 2 ^ 3 * (3 * 7) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (3 * 7)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w240_167 : Nat.totient (1 + 1 + 167) = 156 := by
  have e : (1 + 1 + 167 : ℕ) = 169 := by norm_num
  rw [e]
  rw [show (169 : ℕ) = 13 ^ 2 from by norm_num,
    Nat.totient_prime_pow (by norm_num : Nat.Prime 13) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w240_168 : Nat.totient (1 + 1 + 168) = 64 := by
  have e : (1 + 1 + 168 : ℕ) = 170 := by norm_num
  rw [e]
  rw [show (170 : ℕ) = 2 * (5 * 17) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5 * 17)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (17)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w240_169 : Nat.totient (1 + 1 + 169) = 108 := by
  have e : (1 + 1 + 169 : ℕ) = 171 := by norm_num
  rw [e]
  rw [show (171 : ℕ) = 3 ^ 2 * 19 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (19)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]
  norm_num

private lemma phi_w240_170 : Nat.totient (1 + 1 + 170) = 84 := by
  have e : (1 + 1 + 170 : ℕ) = 172 := by norm_num
  rw [e]
  rw [show (172 : ℕ) = 2 ^ 2 * 43 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (43)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 43)]
  norm_num

private lemma phi_w240_171 : Nat.totient (1 + 1 + 171) = 172 := by
  have e : (1 + 1 + 171 : ℕ) = 173 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 173)]

private lemma phi_w240_172 : Nat.totient (1 + 1 + 172) = 56 := by
  have e : (1 + 1 + 172 : ℕ) = 174 := by norm_num
  rw [e]
  rw [show (174 : ℕ) = 2 * (3 * 29) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 29)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (29)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 29)]

private lemma phi_w240_173 : Nat.totient (1 + 1 + 173) = 120 := by
  have e : (1 + 1 + 173 : ℕ) = 175 := by norm_num
  rw [e]
  rw [show (175 : ℕ) = 5 ^ 2 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5 ^ 2) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w240_174 : Nat.totient (1 + 1 + 174) = 80 := by
  have e : (1 + 1 + 174 : ℕ) = 176 := by norm_num
  rw [e]
  rw [show (176 : ℕ) = 2 ^ 4 * 11 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 4) (11)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]
  norm_num

private lemma phi_w240_175 : Nat.totient (1 + 1 + 175) = 116 := by
  have e : (1 + 1 + 175 : ℕ) = 177 := by norm_num
  rw [e]
  rw [show (177 : ℕ) = 3 * 59 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (59)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 59)]

private lemma phi_w240_176 : Nat.totient (1 + 1 + 176) = 88 := by
  have e : (1 + 1 + 176 : ℕ) = 178 := by norm_num
  rw [e]
  rw [show (178 : ℕ) = 2 * 89 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (89)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 89)]

private lemma phi_w240_177 : Nat.totient (1 + 1 + 177) = 178 := by
  have e : (1 + 1 + 177 : ℕ) = 179 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 179)]

private lemma phi_w240_178 : Nat.totient (1 + 1 + 178) = 48 := by
  have e : (1 + 1 + 178 : ℕ) = 180 := by norm_num
  rw [e]
  rw [show (180 : ℕ) = 2 ^ 2 * (3 ^ 2 * 5) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 ^ 2 * 5)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w240_179 : Nat.totient (1 + 1 + 179) = 180 := by
  have e : (1 + 1 + 179 : ℕ) = 181 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 181)]

private lemma phi_w240_180 : Nat.totient (1 + 1 + 180) = 72 := by
  have e : (1 + 1 + 180 : ℕ) = 182 := by norm_num
  rw [e]
  rw [show (182 : ℕ) = 2 * (7 * 13) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (7 * 13)),
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w240_181 : Nat.totient (1 + 1 + 181) = 120 := by
  have e : (1 + 1 + 181 : ℕ) = 183 := by norm_num
  rw [e]
  rw [show (183 : ℕ) = 3 * 61 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (61)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 61)]

private lemma phi_w240_182 : Nat.totient (1 + 1 + 182) = 88 := by
  have e : (1 + 1 + 182 : ℕ) = 184 := by norm_num
  rw [e]
  rw [show (184 : ℕ) = 2 ^ 3 * 23 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (23)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]
  norm_num

private lemma phi_w240_183 : Nat.totient (1 + 1 + 183) = 144 := by
  have e : (1 + 1 + 183 : ℕ) = 185 := by norm_num
  rw [e]
  rw [show (185 : ℕ) = 5 * 37 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (37)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 37)]

private lemma phi_w240_184 : Nat.totient (1 + 1 + 184) = 60 := by
  have e : (1 + 1 + 184 : ℕ) = 186 := by norm_num
  rw [e]
  rw [show (186 : ℕ) = 2 * (3 * 31) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 31)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (31)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 31)]

private lemma phi_w240_185 : Nat.totient (1 + 1 + 185) = 160 := by
  have e : (1 + 1 + 185 : ℕ) = 187 := by norm_num
  rw [e]
  rw [show (187 : ℕ) = 11 * 17 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (11) (17)),
    Nat.totient_prime (by norm_num : Nat.Prime 11),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w240_186 : Nat.totient (1 + 1 + 186) = 92 := by
  have e : (1 + 1 + 186 : ℕ) = 188 := by norm_num
  rw [e]
  rw [show (188 : ℕ) = 2 ^ 2 * 47 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (47)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 47)]
  norm_num

private lemma phi_w240_187 : Nat.totient (1 + 1 + 187) = 108 := by
  have e : (1 + 1 + 187 : ℕ) = 189 := by norm_num
  rw [e]
  rw [show (189 : ℕ) = 3 ^ 3 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 3) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w240_188 : Nat.totient (1 + 1 + 188) = 72 := by
  have e : (1 + 1 + 188 : ℕ) = 190 := by norm_num
  rw [e]
  rw [show (190 : ℕ) = 2 * (5 * 19) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5 * 19)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (19)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]

private lemma phi_w240_189 : Nat.totient (1 + 1 + 189) = 190 := by
  have e : (1 + 1 + 189 : ℕ) = 191 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 191)]

private lemma phi_w240_190 : Nat.totient (1 + 1 + 190) = 64 := by
  have e : (1 + 1 + 190 : ℕ) = 192 := by norm_num
  rw [e]
  rw [show (192 : ℕ) = 2 ^ 6 * 3 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 6) (3)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 6),
    Nat.totient_prime (by norm_num : Nat.Prime 3)]
  norm_num

private lemma phi_w240_191 : Nat.totient (1 + 1 + 191) = 192 := by
  have e : (1 + 1 + 191 : ℕ) = 193 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 193)]

private lemma phi_w240_192 : Nat.totient (1 + 1 + 192) = 96 := by
  have e : (1 + 1 + 192 : ℕ) = 194 := by norm_num
  rw [e]
  rw [show (194 : ℕ) = 2 * 97 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (97)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 97)]

private lemma phi_w240_193 : Nat.totient (1 + 1 + 193) = 96 := by
  have e : (1 + 1 + 193 : ℕ) = 195 := by norm_num
  rw [e]
  rw [show (195 : ℕ) = 3 * (5 * 13) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5 * 13)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]

private lemma phi_w240_194 : Nat.totient (1 + 1 + 194) = 84 := by
  have e : (1 + 1 + 194 : ℕ) = 196 := by norm_num
  rw [e]
  rw [show (196 : ℕ) = 2 ^ 2 * (7 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (7 ^ 2)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 7) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w240_195 : Nat.totient (1 + 1 + 195) = 196 := by
  have e : (1 + 1 + 195 : ℕ) = 197 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 197)]

private lemma phi_w240_196 : Nat.totient (1 + 1 + 196) = 60 := by
  have e : (1 + 1 + 196 : ℕ) = 198 := by norm_num
  rw [e]
  rw [show (198 : ℕ) = 2 * (3 ^ 2 * 11) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 ^ 2 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]
  norm_num

private lemma phi_w240_197 : Nat.totient (1 + 1 + 197) = 198 := by
  have e : (1 + 1 + 197 : ℕ) = 199 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 199)]

private lemma phi_w240_198 : Nat.totient (1 + 1 + 198) = 80 := by
  have e : (1 + 1 + 198 : ℕ) = 200 := by norm_num
  rw [e]
  rw [show (200 : ℕ) = 2 ^ 3 * (5 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (5 ^ 2)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w240_199 : Nat.totient (1 + 1 + 199) = 132 := by
  have e : (1 + 1 + 199 : ℕ) = 201 := by norm_num
  rw [e]
  rw [show (201 : ℕ) = 3 * 67 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (67)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 67)]

private lemma phi_w240_200 : Nat.totient (1 + 1 + 200) = 100 := by
  have e : (1 + 1 + 200 : ℕ) = 202 := by norm_num
  rw [e]
  rw [show (202 : ℕ) = 2 * 101 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (101)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 101)]

private lemma phi_w240_201 : Nat.totient (1 + 1 + 201) = 168 := by
  have e : (1 + 1 + 201 : ℕ) = 203 := by norm_num
  rw [e]
  rw [show (203 : ℕ) = 7 * 29 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (29)),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 29)]

private lemma phi_w240_202 : Nat.totient (1 + 1 + 202) = 64 := by
  have e : (1 + 1 + 202 : ℕ) = 204 := by norm_num
  rw [e]
  rw [show (204 : ℕ) = 2 ^ 2 * (3 * 17) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 * 17)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (17)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]
  norm_num

private lemma phi_w240_203 : Nat.totient (1 + 1 + 203) = 160 := by
  have e : (1 + 1 + 203 : ℕ) = 205 := by norm_num
  rw [e]
  rw [show (205 : ℕ) = 5 * 41 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (41)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 41)]

private lemma phi_w240_204 : Nat.totient (1 + 1 + 204) = 102 := by
  have e : (1 + 1 + 204 : ℕ) = 206 := by norm_num
  rw [e]
  rw [show (206 : ℕ) = 2 * 103 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (103)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 103)]

private lemma phi_w240_205 : Nat.totient (1 + 1 + 205) = 132 := by
  have e : (1 + 1 + 205 : ℕ) = 207 := by norm_num
  rw [e]
  rw [show (207 : ℕ) = 3 ^ 2 * 23 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (23)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]
  norm_num

private lemma phi_w240_206 : Nat.totient (1 + 1 + 206) = 96 := by
  have e : (1 + 1 + 206 : ℕ) = 208 := by norm_num
  rw [e]
  rw [show (208 : ℕ) = 2 ^ 4 * 13 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 4) (13)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]
  norm_num

private lemma phi_w240_207 : Nat.totient (1 + 1 + 207) = 180 := by
  have e : (1 + 1 + 207 : ℕ) = 209 := by norm_num
  rw [e]
  rw [show (209 : ℕ) = 11 * 19 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (11) (19)),
    Nat.totient_prime (by norm_num : Nat.Prime 11),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]

private lemma phi_w240_208 : Nat.totient (1 + 1 + 208) = 48 := by
  have e : (1 + 1 + 208 : ℕ) = 210 := by norm_num
  rw [e]
  rw [show (210 : ℕ) = 2 * (3 * (5 * 7)) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * (5 * 7))),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5 * 7)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (7)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]

private lemma phi_w240_209 : Nat.totient (1 + 1 + 209) = 210 := by
  have e : (1 + 1 + 209 : ℕ) = 211 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 211)]

private lemma phi_w240_210 : Nat.totient (1 + 1 + 210) = 104 := by
  have e : (1 + 1 + 210 : ℕ) = 212 := by norm_num
  rw [e]
  rw [show (212 : ℕ) = 2 ^ 2 * 53 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (53)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 53)]
  norm_num

private lemma phi_w240_211 : Nat.totient (1 + 1 + 211) = 140 := by
  have e : (1 + 1 + 211 : ℕ) = 213 := by norm_num
  rw [e]
  rw [show (213 : ℕ) = 3 * 71 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (71)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 71)]

private lemma phi_w240_212 : Nat.totient (1 + 1 + 212) = 106 := by
  have e : (1 + 1 + 212 : ℕ) = 214 := by norm_num
  rw [e]
  rw [show (214 : ℕ) = 2 * 107 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (107)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 107)]

private lemma phi_w240_213 : Nat.totient (1 + 1 + 213) = 168 := by
  have e : (1 + 1 + 213 : ℕ) = 215 := by norm_num
  rw [e]
  rw [show (215 : ℕ) = 5 * 43 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (43)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 43)]

private lemma phi_w240_214 : Nat.totient (1 + 1 + 214) = 72 := by
  have e : (1 + 1 + 214 : ℕ) = 216 := by norm_num
  rw [e]
  rw [show (216 : ℕ) = 2 ^ 3 * (3 ^ 3) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (3 ^ 3)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 3)]
  norm_num

private lemma phi_w240_215 : Nat.totient (1 + 1 + 215) = 180 := by
  have e : (1 + 1 + 215 : ℕ) = 217 := by norm_num
  rw [e]
  rw [show (217 : ℕ) = 7 * 31 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (31)),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 31)]

private lemma phi_w240_216 : Nat.totient (1 + 1 + 216) = 108 := by
  have e : (1 + 1 + 216 : ℕ) = 218 := by norm_num
  rw [e]
  rw [show (218 : ℕ) = 2 * 109 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (109)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 109)]

private lemma phi_w240_217 : Nat.totient (1 + 1 + 217) = 144 := by
  have e : (1 + 1 + 217 : ℕ) = 219 := by norm_num
  rw [e]
  rw [show (219 : ℕ) = 3 * 73 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (73)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 73)]

private lemma phi_w240_218 : Nat.totient (1 + 1 + 218) = 80 := by
  have e : (1 + 1 + 218 : ℕ) = 220 := by norm_num
  rw [e]
  rw [show (220 : ℕ) = 2 ^ 2 * (5 * 11) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (5 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (11)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]
  norm_num

private lemma phi_w240_219 : Nat.totient (1 + 1 + 219) = 192 := by
  have e : (1 + 1 + 219 : ℕ) = 221 := by norm_num
  rw [e]
  rw [show (221 : ℕ) = 13 * 17 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (13) (17)),
    Nat.totient_prime (by norm_num : Nat.Prime 13),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w240_220 : Nat.totient (1 + 1 + 220) = 72 := by
  have e : (1 + 1 + 220 : ℕ) = 222 := by norm_num
  rw [e]
  rw [show (222 : ℕ) = 2 * (3 * 37) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 * 37)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (37)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 37)]

private lemma phi_w240_221 : Nat.totient (1 + 1 + 221) = 222 := by
  have e : (1 + 1 + 221 : ℕ) = 223 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 223)]

private lemma phi_w240_222 : Nat.totient (1 + 1 + 222) = 96 := by
  have e : (1 + 1 + 222 : ℕ) = 224 := by norm_num
  rw [e]
  rw [show (224 : ℕ) = 2 ^ 5 * 7 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 5) (7)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 5),
    Nat.totient_prime (by norm_num : Nat.Prime 7)]
  norm_num

private lemma phi_w240_223 : Nat.totient (1 + 1 + 223) = 120 := by
  have e : (1 + 1 + 223 : ℕ) = 225 := by norm_num
  rw [e]
  rw [show (225 : ℕ) = 3 ^ 2 * (5 ^ 2) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (5 ^ 2)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2)]
  norm_num

private lemma phi_w240_224 : Nat.totient (1 + 1 + 224) = 112 := by
  have e : (1 + 1 + 224 : ℕ) = 226 := by norm_num
  rw [e]
  rw [show (226 : ℕ) = 2 * 113 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (113)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 113)]

private lemma phi_w240_225 : Nat.totient (1 + 1 + 225) = 226 := by
  have e : (1 + 1 + 225 : ℕ) = 227 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 227)]

private lemma phi_w240_226 : Nat.totient (1 + 1 + 226) = 72 := by
  have e : (1 + 1 + 226 : ℕ) = 228 := by norm_num
  rw [e]
  rw [show (228 : ℕ) = 2 ^ 2 * (3 * 19) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 * 19)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (19)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 19)]
  norm_num

private lemma phi_w240_227 : Nat.totient (1 + 1 + 227) = 228 := by
  have e : (1 + 1 + 227 : ℕ) = 229 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 229)]

private lemma phi_w240_228 : Nat.totient (1 + 1 + 228) = 88 := by
  have e : (1 + 1 + 228 : ℕ) = 230 := by norm_num
  rw [e]
  rw [show (230 : ℕ) = 2 * (5 * 23) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (5 * 23)),
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (23)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 23)]

private lemma phi_w240_229 : Nat.totient (1 + 1 + 229) = 120 := by
  have e : (1 + 1 + 229 : ℕ) = 231 := by norm_num
  rw [e]
  rw [show (231 : ℕ) = 3 * (7 * 11) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (7 * 11)),
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (11)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

private lemma phi_w240_230 : Nat.totient (1 + 1 + 230) = 112 := by
  have e : (1 + 1 + 230 : ℕ) = 232 := by norm_num
  rw [e]
  rw [show (232 : ℕ) = 2 ^ 3 * 29 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 3) (29)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3),
    Nat.totient_prime (by norm_num : Nat.Prime 29)]
  norm_num

private lemma phi_w240_231 : Nat.totient (1 + 1 + 231) = 232 := by
  have e : (1 + 1 + 231 : ℕ) = 233 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 233)]

private lemma phi_w240_232 : Nat.totient (1 + 1 + 232) = 72 := by
  have e : (1 + 1 + 232 : ℕ) = 234 := by norm_num
  rw [e]
  rw [show (234 : ℕ) = 2 * (3 ^ 2 * 13) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (3 ^ 2 * 13)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3 ^ 2) (13)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 13)]
  norm_num

private lemma phi_w240_233 : Nat.totient (1 + 1 + 233) = 184 := by
  have e : (1 + 1 + 233 : ℕ) = 235 := by norm_num
  rw [e]
  rw [show (235 : ℕ) = 5 * 47 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (5) (47)),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 47)]

private lemma phi_w240_234 : Nat.totient (1 + 1 + 234) = 116 := by
  have e : (1 + 1 + 234 : ℕ) = 236 := by norm_num
  rw [e]
  rw [show (236 : ℕ) = 2 ^ 2 * 59 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (59)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2),
    Nat.totient_prime (by norm_num : Nat.Prime 59)]
  norm_num

private lemma phi_w240_235 : Nat.totient (1 + 1 + 235) = 156 := by
  have e : (1 + 1 + 235 : ℕ) = 237 := by norm_num
  rw [e]
  rw [show (237 : ℕ) = 3 * 79 from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (79)),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 79)]

private lemma phi_w240_236 : Nat.totient (1 + 1 + 236) = 96 := by
  have e : (1 + 1 + 236 : ℕ) = 238 := by norm_num
  rw [e]
  rw [show (238 : ℕ) = 2 * (7 * 17) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2) (7 * 17)),
    Nat.totient_mul (by norm_num : Nat.Coprime (7) (17)),
    Nat.totient_prime (by norm_num : Nat.Prime 2),
    Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 17)]

private lemma phi_w240_237 : Nat.totient (1 + 1 + 237) = 238 := by
  have e : (1 + 1 + 237 : ℕ) = 239 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 239)]

private lemma phi_w240_238 : Nat.totient (1 + 1 + 238) = 64 := by
  have e : (1 + 1 + 238 : ℕ) = 240 := by norm_num
  rw [e]
  rw [show (240 : ℕ) = 2 ^ 4 * (3 * 5) from by norm_num,
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 4) (3 * 5)),
    Nat.totient_mul (by norm_num : Nat.Coprime (3) (5)),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4),
    Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5)]
  norm_num

private lemma phi_w240_239 : Nat.totient (1 + 1 + 239) = 240 := by
  have e : (1 + 1 + 239 : ℕ) = 241 := by norm_num
  rw [e]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 241)]

set_option maxRecDepth 8000 in
/-- **Window residue `(N,K) = (1,240)`, kernel-evaluated.**  Every window
totient is certified by its prime factorization and rewritten to a literal
before arithmetic — no `Nat.totient` kernel unfolding at any point. -/
theorem totient_carry_residue_window_1_240_eq :
    (∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r)) % 2 ^ 240
      = 1299094806818720335611738031537456208600423915562142231419225521361164904 := by
  rw [totient_carry_sum_eq_range 1 240]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, phi_w17_0, phi_w17_1, phi_w17_2, phi_w17_3, phi_w17_4, phi_w17_5, phi_w17_6, phi_w17_7, phi_w17_8, phi_w17_9, phi_w17_10, phi_w17_11, phi_w17_12, phi_w17_13, phi_w17_14, phi_w17_15, phi_w17_16, phi_w17_17, phi_w17_18, phi_w17_19, phi_w17_20, phi_w17_21, phi_w17_22, phi_w17_23, phi_w17_24, phi_w17_25, phi_w17_26, phi_w17_27, phi_w17_28, phi_w17_29, phi_w17_30, phi_w17_31, phi_w17_32, phi_w17_33, phi_w17_34, phi_w17_35, phi_w17_36, phi_w17_37, phi_w17_38, phi_w17_39, phi_w17_40, phi_w17_41, phi_w17_42, phi_w17_43, phi_w17_44, phi_w17_45, phi_w17_46, phi_w17_47, phi_w17_48, phi_w17_49, phi_w17_50, phi_w17_51, phi_w17_52, phi_w17_53, phi_w17_54, phi_w17_55, phi_w17_56, phi_w17_57, phi_w17_58, phi_w17_59, phi_w17_60, phi_w17_61, phi_w17_62, phi_w17_63, phi_w17_64, phi_w17_65, phi_w17_66, phi_w17_67, phi_w17_68, phi_w17_69, phi_w17_70, phi_w17_71, phi_w17_72, phi_w17_73, phi_w17_74, phi_w17_75, phi_w17_76, phi_w17_77, phi_w17_78, phi_w17_79, phi_w17_80, phi_w17_81, phi_w17_82, phi_w17_83, phi_w17_84, phi_w17_85, phi_w17_86, phi_w17_87, phi_w17_88, phi_w17_89, phi_w17_90, phi_w17_91, phi_w17_92, phi_w17_93, phi_w17_94, phi_w17_95, phi_w17_96, phi_w17_97, phi_w17_98, phi_w17_99, phi_w17_100, phi_w17_101, phi_w17_102, phi_w17_103, phi_w17_104, phi_w17_105, phi_w17_106, phi_w17_107, phi_w17_108, phi_w17_109, phi_w17_110, phi_w17_111, phi_w17_112, phi_w17_113, phi_w17_114, phi_w17_115, phi_w17_116, phi_w17_117, phi_w17_118, phi_w17_119, phi_w240_120, phi_w240_121, phi_w240_122, phi_w240_123, phi_w240_124, phi_w240_125, phi_w240_126, phi_w240_127, phi_w240_128, phi_w240_129, phi_w240_130, phi_w240_131, phi_w240_132, phi_w240_133, phi_w240_134, phi_w240_135, phi_w240_136, phi_w240_137, phi_w240_138, phi_w240_139, phi_w240_140, phi_w240_141, phi_w240_142, phi_w240_143, phi_w240_144, phi_w240_145, phi_w240_146, phi_w240_147, phi_w240_148, phi_w240_149, phi_w240_150, phi_w240_151, phi_w240_152, phi_w240_153, phi_w240_154, phi_w240_155, phi_w240_156, phi_w240_157, phi_w240_158, phi_w240_159, phi_w240_160, phi_w240_161, phi_w240_162, phi_w240_163, phi_w240_164, phi_w240_165, phi_w240_166, phi_w240_167, phi_w240_168, phi_w240_169, phi_w240_170, phi_w240_171, phi_w240_172, phi_w240_173, phi_w240_174, phi_w240_175, phi_w240_176, phi_w240_177, phi_w240_178, phi_w240_179, phi_w240_180, phi_w240_181, phi_w240_182, phi_w240_183, phi_w240_184, phi_w240_185, phi_w240_186, phi_w240_187, phi_w240_188, phi_w240_189, phi_w240_190, phi_w240_191, phi_w240_192, phi_w240_193, phi_w240_194, phi_w240_195, phi_w240_196, phi_w240_197, phi_w240_198, phi_w240_199, phi_w240_200, phi_w240_201, phi_w240_202, phi_w240_203, phi_w240_204, phi_w240_205, phi_w240_206, phi_w240_207, phi_w240_208, phi_w240_209, phi_w240_210, phi_w240_211, phi_w240_212, phi_w240_213, phi_w240_214, phi_w240_215, phi_w240_216, phi_w240_217, phi_w240_218, phi_w240_219, phi_w240_220, phi_w240_221, phi_w240_222, phi_w240_223, phi_w240_224, phi_w240_225, phi_w240_226, phi_w240_227, phi_w240_228, phi_w240_229, phi_w240_230, phi_w240_231, phi_w240_232, phi_w240_233, phi_w240_234, phi_w240_235, phi_w240_236, phi_w240_237, phi_w240_238, phi_w240_239]
  norm_num

/-- **Erdős #249 denominator exclusion to `248672326362367909`.**
Machine-checked: `∑_{n≥0} φ(n)/2^n` is not `a/d` for any integer `a` and any
denominator `1 ≤ d ≤ 248672326362367909`.  The Farey-gap feed
(`GapFareyBound.gap_check_window_1_120_le_248672326362367909`) replaces bulk
kernel enumeration; every denominator receives its certificate from the single
window `(N, K) = (1, 120)`.  Unconditional instance slice of #249; the ∀q
supply is NOT claimed. -/
theorem tsum_totient_div_pow_two_ne_int_div_of_den_le_248672326362367909 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 248672326362367909 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) := by
  intro a d hd hdle
  refine tsum_totient_div_pow_two_ne_int_div_of_totient_gap_certificate d 1 120 hd ?_ a
  rw [totient_carry_residue_window_1_120_eq]
  have hH : (1 + 120 + 2 : ℕ) = 123 := by norm_num
  rw [hH]
  exact GapFareyBound.gap_check_window_1_120_le_248672326362367909 d hd hdle

/-- **Erdős #249 denominator exclusion to `248672326362367909`, `ℚ` form.**
If `∑_{n≥0} φ(n)/2^n` is rational, its reduced denominator exceeds
`248672326362367909`. -/
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_248672326362367909 :
    ∀ p : ℚ, p.den ≤ 248672326362367909 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  intro p hden heq
  exact tsum_totient_div_pow_two_ne_int_div_of_den_le_248672326362367909 p.num p.den p.pos hden
    (heq.trans (Rat.cast_def p))

/-- **Erdős #249 denominator exclusion to `4194304` — retained name.**  Now a
one-line corollary of the Farey-gap bound; the depth-22 bulk `decide +kernel`
enumeration this name used to carry is superseded (same statement, strictly
cheaper proof, identical trusted base). -/
theorem tsum_totient_div_pow_two_ne_int_div_of_den_le_4194304 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 4194304 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) := by
  intro a d hd hdle
  exact tsum_totient_div_pow_two_ne_int_div_of_den_le_248672326362367909 a d hd (by omega)

/-- **Erdős #249 denominator exclusion to `4194304`, `ℚ` form.**  If
`∑_{n≥0} φ(n)/2^n` is rational, its reduced denominator exceeds
`4194304`. -/
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_4194304 :
    ∀ p : ℚ, p.den ≤ 4194304 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  intro p hden heq
  exact tsum_totient_div_pow_two_ne_int_div_of_den_le_4194304 p.num p.den p.pos hden
    (heq.trans (Rat.cast_def p))

/-- **Erdős #249 denominator exclusion to `79639646646701375323355774875831053`.**
Machine-checked: `∑_{n≥0} φ(n)/2^n` is not `a/d` for any integer `a` and any
denominator `1 ≤ d ≤ 79639646646701375323355774875831053`.  The Farey-gap feed
(`GapFareyBound.gap_check_window_1_240_le_79639646646701375323355774875831053`) replaces bulk
kernel enumeration; every denominator receives its certificate from the single
window `(N, K) = (1, 240)`.  Unconditional instance slice of #249; the ∀q
supply is NOT claimed. -/
theorem tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) := by
  intro a d hd hdle
  refine tsum_totient_div_pow_two_ne_int_div_of_totient_gap_certificate d 1 240 hd ?_ a
  rw [totient_carry_residue_window_1_240_eq]
  have hH : (1 + 240 + 2 : ℕ) = 243 := by norm_num
  rw [hH]
  exact GapFareyBound.gap_check_window_1_240_le_79639646646701375323355774875831053 d hd hdle

/-- **Erdős #249 denominator exclusion to `79639646646701375323355774875831053`, `ℚ` form.**
If `∑_{n≥0} φ(n)/2^n` is rational, its reduced denominator exceeds
`79639646646701375323355774875831053`. -/
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  intro p hden heq
  exact tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053 p.num p.den p.pos hden
    (heq.trans (Rat.cast_def p))

/-! ## Wave 18: the Mersenne–Lambert ladder — where the #249 constant lives

`L(f) = ∑_{n≥1} f(n)/(2ⁿ-1)` places `S = ∑ φ(n)/2ⁿ` in a one-parameter
family of Lambert values indexed by Dirichlet convolution:

* `L(μ) = 1/2` and `L(φ) = 2` — EXACTLY rational (machine-checked below);
* `L(1) = E`, the Erdős–Borwein constant — IRRATIONAL
  (`irrational_erdosBorwein_series`, machine-checked in this kernel);
* `L(A) = S` for the nonnegative primitive-conductor weight `A = φ * μ`
  (`A(n)` counts primitive Dirichlet characters of conductor `n`) — OPEN;
  this IS Erdős #249, now in positive Erdős–Borwein form, and it inherits
  the wave-17.5 record: no denominator `≤ 7.96×10³⁴`;
* `L(Id) = ∑ σ(m)/2^m` — transcendental by Nesterenko 1996 via `E₂(1/2)`
  (cited, not formalised).

One convolution by `ζ` (`A * ζ = φ`) separates the open constant from a
rational; one more (`φ * ζ = Id`) separates rational from transcendental.
The bodies live in `MersenneLambertLadder`; these kernel restatements bind
them to the literal #249 series shape and to the Farey-gap record bound.
No irrationality of `S` is claimed; the ladder relocates the problem, it
does not solve it. -/

/-- **Index bridge**: the #249 statement-shape series over `ℕ` equals the
ladder-convention `ℕ+` series with explicit `(1/2)ⁿ` terms. -/
theorem tsum_totient_div_pow_two_eq_pnat_half_pow :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  have hshift := tsum_totient_div_pow_eq_shifted 2 (by norm_num)
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast] at hshift
  rw [hshift,
    ← tsum_pnat_eq_tsum_succ (f := fun m : ℕ => ((Nat.totient m : ℝ)) / (2 : ℝ) ^ m)]
  refine tsum_congr fun n => ?_
  rw [div_pow, one_pow, mul_one_div]

/-- **Rational rung `L(φ) = 2`**: `∑_{d≥1} φ(d)/(2^d-1) = 2`, exactly.  The
Lambert transform of the #249 coefficients at the #249 point is rational —
the difficulty of #249 lives entirely on the power-series side. -/
theorem tsum_totient_div_two_pow_sub_one_eq_two :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 2 :=
  MersenneLambertLadder.tsum_totient_div_two_pow_sub_one_eq_two

/-- **Rational rung `L(μ) = 1/2`**: `∑_{d≥1} μ(d)/(2^d-1) = 1/2`, exactly. -/
theorem tsum_moebius_div_two_pow_sub_one_eq_half :
    ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
      / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2 :=
  MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half

/-- **The positive lift `L(A) = S`**: the #249 series IS the Mersenne–Lambert
transform of the nonnegative primitive-conductor weight `A = φ * μ`
(`A(p) = p - 2`, `A(p^e) = (p-1)²·p^(e-2)`, `A ≥ 0`,
`MersenneLambertLadder.primWeight`).  Same shape as the Erdős–Borwein
constant `∑ 1/(2^d-1)` — whose irrationality IS machine-checked in this
kernel — with weight `1` replaced by `A`. -/
theorem tsum_primWeight_div_two_pow_sub_one_eq_totient_series :
    ∑' d : ℕ+, ((MersenneLambertLadder.primWeight (d : ℕ) : ℤ) : ℝ)
        / ((2 : ℝ) ^ (d : ℕ) - 1)
      = ∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n := by
  rw [tsum_totient_div_pow_two_eq_pnat_half_pow]
  exact MersenneLambertLadder.tsum_primWeight_div_two_pow_sub_one

/-- **Möbius-square lens**: `∑ φ(n)/2ⁿ = 1/2 + ∑_{d≥1} μ(d)/(2^d-1)²`.
The #249 constant as a signed squared-Mersenne Lambert series. -/
theorem totient_series_eq_half_add_moebius_mersenne_square :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  rw [tsum_totient_div_pow_two_eq_pnat_half_pow]
  exact MersenneLambertLadder.tsum_totient_half_pow_eq_half_add_moebius_sq

/-- Alias under the `mobius` spelling, for callers that use it in place of `moebius`.
Definitionally the theorem above; it states nothing further. -/
theorem totient_series_eq_half_add_mobius_mersenne_square :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 :=
  totient_series_eq_half_add_moebius_mersenne_square

/-- **Record-bound transfer to the positive lift.**  The primitive-conductor
Erdős–Borwein series `∑ A(d)/(2^d-1)` has no rational representation with
denominator `≤ 79639646646701375323355774875831053` — the wave-17.5 Farey
record, restated on the ladder's positive representation of `S`. -/
theorem tsum_primWeight_div_two_pow_sub_one_ne_int_div_of_den_le_79639646646701375323355774875831053 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 79639646646701375323355774875831053 →
      (∑' k : ℕ+, ((MersenneLambertLadder.primWeight (k : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (k : ℕ) - 1))
        ≠ (a : ℝ) / (d : ℝ) := by
  intro a d hd hdle
  rw [tsum_primWeight_div_two_pow_sub_one_eq_totient_series]
  exact tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053
    a d hd hdle

/-- **Record-bound transfer to the Möbius-square lens.**  The signed series
`T = ∑ μ(d)/(2^d-1)²` has no rational representation with denominator
`≤ 39819823323350687661677887437915526` (half the wave-17.5 record):
`T = a/d` would force `S = (d+2a)/(2d)` with `2d` under the record bound. -/
theorem tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 39819823323350687661677887437915526 →
      (∑' k : ℕ+, ((ArithmeticFunction.moebius (k : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (k : ℕ) - 1) ^ 2)
        ≠ (a : ℝ) / (d : ℝ) := by
  intro a d hd hdle heq
  have hS := totient_series_eq_half_add_moebius_mersenne_square
  rw [heq] at hS
  have hd0 : ((d : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hd.ne'
  have hcalc : (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = (((d : ℤ) + 2 * a : ℤ) : ℝ) / ((2 * d : ℕ) : ℝ) := by
    rw [hS]
    push_cast
    field_simp
  exact tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053
    ((d : ℤ) + 2 * a) (2 * d) (by omega) (by omega) hcalc

/-! ## Wave 19: geometric coprimality — the #249 constant as visible-lattice mass

Let `X` be the fair-coin waiting time (`P(X = n) = 2⁻ⁿ`, `n ≥ 1`).  Then
`P(d ∣ X) = 1/(2ᵈ-1)`, so the wave-18 Mersenne–Lambert ladder is the divisor
calculus of `X`: `L(f) = ∑ f(d)/(2ᵈ-1) = E[(f * ζ)(X)]`, and the rungs read

* `L(μ) = 1/2 = P(X = 1)`,
* `L(φ) = 2   = E[X]`,
* `L(1) = E   = E[τ(X)]`  (Erdős–Borwein; irrational, this kernel),
* `L(A) = S   = E[φ(X)]`  — OPEN; this IS #249.

This wave adds the two-variable coordinate (bodies in `GeometricCoprimality`):
`φ(n)` counts the visible lattice points `(a, b)`, `a + b = n`, `0 < a`,
`gcd(a,b) = 1` — uniformly in `n`, no case split — so the #249 constant is
itself a coprime-pair mass, and

  `S - 1/2 = ∑_{(a,b) coprime, a,b ≥ 1} 2^{-(a+b)} = P(gcd(X,Y) = 1)`

for independent fair-coin waiting times `X, Y` (base 2 is the unique point
where `P(X = a)·P(Y = b) = 2^{-(a+b)}` with no normalizing constant).  Erdős
#249 asks whether this coprimality probability is irrational.  The gcd-layer
theorem closes the picture: `∑_{g≥1} P(gcd(X,Y) = g) = 1` exactly — the
probabilistic content of the rational rung `L(φ) = 2` — and the wave-17.5
Farey record transfers: `P(gcd(X,Y) = 1)` has no rational representation with
denominator `≤ 3.98×10³⁴`.  No irrationality of `S` is claimed; the coordinate
change relocates #249 onto the visible lattice, it does not solve it. -/

/-- **Index bridge, `ℕ`-power form**: the #249 statement-shape series with
explicit `(1/2)ⁿ` terms, still over `ℕ`. -/
theorem tsum_totient_div_pow_two_eq_nat_half_pow :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = ∑' n : ℕ, (Nat.totient n : ℝ) * ((1 : ℝ) / 2) ^ n := by
  refine tsum_congr fun n => ?_
  rw [div_pow, one_pow, mul_one_div]

/-- **The #249 constant IS a visible-lattice mass**: summing `2^{-(a+b)}` over
the half-open coprime pairs (`a ≥ 1`, `b ≥ 0`, `gcd(a,b) = 1`) gives exactly
`∑ φ(n)/2ⁿ` — no boundary correction, because the visible-point count on the
half-open antidiagonal equals `φ(n)` for every `n` including `0` and `1`. -/
theorem tsum_visible_coprime_pairs_eq_totient_series :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n := by
  rw [tsum_totient_div_pow_two_eq_nat_half_pow]
  exact GeometricCoprimality.tsum_coprime_pair_pow_eq_tsum_totient_mul_pow
    (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)

/-- **Fair-coin geometric coprimality**: `∑ φ(n)/2ⁿ = 1/2 + P(gcd(X,Y) = 1)`,
where the probability is spelled as its defining series
`∑_{(a,b) coprime, a,b ≥ 1} 2^{-(a+b)}`.  The boundary term `1/2` is
`P(X = 1) = L(μ)` — the ladder's Möbius rung.  Erdős #249 is equivalent to
irrationality of this coprimality probability. -/
theorem totient_series_eq_half_add_visible_coprime_pairs :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' p : ℕ × ℕ, (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0) := by
  rw [tsum_totient_div_pow_two_eq_nat_half_pow,
    GeometricCoprimality.tsum_pos_coprime_pair_pow
      (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)]
  ring

/-- **Record-bound transfer to the coprimality probability.**  The probability
that two independent fair-coin waiting times are coprime,
`P(gcd(X,Y) = 1) = ∑_{(a,b)=1} 2^{-(a+b)}`, has no rational representation
with denominator `≤ 39819823323350687661677887437915526` (half the wave-17.5
Farey record): `P = a/d` would force `S = (d+2a)/(2d)` with `2d` under the
record bound. -/
theorem tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 39819823323350687661677887437915526 →
      (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
        ≠ (a : ℝ) / (d : ℝ) := by
  intro a d hd hdle heq
  have hS := totient_series_eq_half_add_visible_coprime_pairs
  rw [heq] at hS
  have hd0 : ((d : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hd.ne'
  have hcalc : (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = (((d : ℤ) + 2 * a : ℤ) : ℝ) / ((2 * d : ℕ) : ℝ) := by
    rw [hS]
    push_cast
    field_simp
  exact tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053
    ((d : ℤ) + 2 * a) (2 * d) (by omega) (by omega) hcalc

/-- **The fair-coin gcd law is exactly normalized**: layer `g` of the sum is
`P(gcd(X,Y) = g+1)` — the coprime-pair mass at scale `(1/2)^(g+1)`, by the
unique factorization `(a,b) = g·(a',b')` — and the layers sum to `1`: the gcd
of two independent fair-coin waiting times is finite almost surely.  Through
the visible-coprime bridge this is the probabilistic content of the wave-18
rational rung `L(φ) = 2`.  The open #249 value `S - 1/2` is the `g = 1` atom
of this exactly-normalized distribution. -/
theorem tsum_visible_coprime_gcd_layers_eq_one :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0) = 1 :=
  GeometricCoprimality.tsum_gcd_layer_pos_coprime_half_eq_one

/-! ## Wave 20: the squared Lambert transform — gcd moments and Stern–Brocot cylinders

Wave 19 made `S - 1/2 = P(gcd(X,Y) = 1)` the open atom of an exactly-normalized
distribution.  This wave lands the calculus that distribution carries.  The
foundation stone is the divisibility factorization

  `P(d ∣ gcd(X,Y)) = P(d ∣ X)·P(d ∣ Y) = 1/(2ᵈ-1)²`,

so the SQUARED Lambert transform `L₂(f) = ∑ f(d)/(2ᵈ-1)² = E[(f * ζ)(gcd)]`
is the two-variable ladder (bodies in `GcdMomentCalculus`):

* `L₂(μ) = S - 1/2 = P(gcd = 1)`          — the OPEN #249 atom (wave 18's
  Möbius-square lens `tsum_totient_half_pow_eq_half_add_moebius_sq`),
* `L₂(1) = ∑ (σ(n)-τ(n))/2ⁿ = E[τ(gcd)]`  — the q-zeta anchor
  `ζ_q(2) - ζ_q(1)` at `q = 1/2`; irrational by Postelmans–Van Assche q-Padé
  (cited, NOT formalised — the identity is machine-checked here),
* `L₂(φ) = ∑ (P(n)-n)/2ⁿ = E[gcd(X,Y)]`   — `P = φ * Id` is Pillai's gcd-sum.

The MIRROR: at level 1, `L(μ) = 1/2` is trivial and `L(1) = E` is the hard
irrational (Erdős 1948); at level 2, `L₂(1)` is the known irrational (q-Padé)
and `L₂(μ)` IS #249.  Möbius projection is the single remaining wall, at both
levels.  The reduced-direction law `∑_{(a,b)=1} 1/(2^{a+b}-1) = 1` and the
Stern–Brocot cylinder closed form `M(a,b) = 1/((2ᵃ-1)(2ᵇ-1)) = P(a∣X)·P(b∣Y)`
(exact mediant telescoping + `(2/3)ᵈ`-rate limit) give the cylinder topology a
cusp-isolation attack would consume: all-left cusps `(N,1)` have mass
`1/(2ᴺ-1)` — near-Mersenne reciprocals, one exponential order closer to the
Erdős–Borwein engine than the raw totient coefficients.  No irrationality of
`S` is claimed; #249 remains open. -/

/-- **E[τ(gcd)] — the q-zeta anchor of the level-2 ladder**:
`∑_{d≥1} 1/(2ᵈ-1)² = ∑_{n≥1} (σ(n) - τ(n))·(1/2)ⁿ`, exactly, with the
coefficient spelled as its divisor sums.  This is `ζ_q(2) - ζ_q(1)` at
`q = 1/2`; its irrationality (q-Padé) is cited, not formalised. -/
theorem tsum_inv_mersenne_sq_eq_sigma_sub_tau_series :
    ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (((n : ℕ) / e : ℕ) : ℝ)) - ((n : ℕ).divisors.card : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ) :=
  GcdMomentCalculus.tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series

/-- **E[gcd(X,Y)] — the first moment of the fair-coin gcd law**:
`∑_{d≥1} φ(d)/(2ᵈ-1)² = ∑_{n≥1} (P(n) - n)·(1/2)ⁿ`, where
`P(n) = ∑_{e∣n} φ(e)·(n/e)` is Pillai's gcd-sum function. -/
theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) :=
  GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series

/-- **The divisibility factorization** — foundation stone of the squared
kernel: the fair-coin mass of `{(a,b) : a,b ≥ 1, d ∣ a, d ∣ b}` is exactly
`1/(2ᵈ-1)²`, i.e. `P(d ∣ gcd(X,Y)) = P(d ∣ X)·P(d ∣ Y)`. -/
theorem tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2 :=
  GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq d hd

/-- **The reduced-direction law**: the Mersenne masses of the reduced slopes
sum to one — `∑_{(a,b) coprime, a,b ≥ 1} 1/(2^{a+b}-1) = 1`.  This is the root
cylinder of the Stern–Brocot law, proved through the wave-19 gcd-layer
normalization. -/
theorem tsum_visible_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1 :=
  GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one

/-- **Stern–Brocot cylinder approximation with explicit rate**: the depth-`d`
unfolding of the mediant recursion at `(a,b)` under-approximates the closed
form `1/((2ᵃ-1)(2ᵇ-1))` with error at most `(2/3)ᵈ` of it. -/
theorem stern_brocot_cylinder_mass_error_le (dp : ℕ) (a b : ℕ+) :
    GcdMomentCalculus.sternBrocotDepthMass dp a b
        ≤ 1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))
      ∧ 1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))
          - GcdMomentCalculus.sternBrocotDepthMass dp a b
        ≤ (2 / 3 : ℝ) ^ dp * (1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))) := by
  obtain ⟨h0, hle⟩ := GcdMomentCalculus.sternBrocotDepthMass_error dp a b
  exact ⟨sub_nonneg.mp h0, hle⟩

/-- **The Stern–Brocot cylinder law, limit form**: the mediant recursion's
depth-`d` masses converge to `M(a,b) = 1/((2ᵃ-1)(2ᵇ-1)) = P(a∣X)·P(b∣Y)`.
At the root, `M(1,1) = 1` — the reduced-direction law. -/
theorem tendsto_stern_brocot_cylinder_mass (a b : ℕ+) :
    Filter.Tendsto (fun dp : ℕ => GcdMomentCalculus.sternBrocotDepthMass dp a b)
      Filter.atTop (nhds (1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)))) :=
  GcdMomentCalculus.tendsto_sternBrocotDepthMass a b

/-! ## Induced Stern–Brocot runs: Fibonacci pressure and the denominator knife-edge

Raw tree depth has parabolic cusp branches of only linear height.  Grouping
maximal same-direction runs exposes the correct unconditional scale: an
alternating word with `r` nonempty runs has height at least `F_{r+3}`, with
equality on the all-unit spine.  The run continuant below is tied back to the
literal mediant word, not asserted as an independent coordinate.

The natural invariant-coordinate exponents along that spine sum to
`F_{r+3}-2`.  Thus run induction creates Fibonacci analytic pressure but the
naive Mersenne clearing cost lies on the same exponential scale.  These facts
do not supply a denominator surplus and do not prove #249; they isolate the
arithmetic obligation any external cocycle or period identity must beat.
-/

/-- Exact transport from alternating run lengths to the literal
Stern–Brocot pair. -/
theorem stern_brocot_pair_of_run_lengths
    (newest : SternBrocotRunGeometry.LR) (ns : List ℕ) :
    SternBrocotRunGeometry.sbPair (SternBrocotRunGeometry.runWord newest ns) =
      match newest with
      | .left => SternBrocotRunGeometry.runBoundaryPair ns
      | .right =>
          ((SternBrocotRunGeometry.runBoundaryPair ns).2,
            (SternBrocotRunGeometry.runBoundaryPair ns).1) :=
  SternBrocotRunGeometry.sbPair_runWord newest ns

/-- Fibonacci minimum height for positive alternating run lengths. -/
theorem stern_brocot_run_height_fib_lower
    (newest : SternBrocotRunGeometry.LR) (ns : List ℕ)
    (hpos : ∀ n ∈ ns, 0 < n) :
    Nat.fib (ns.length + 3) ≤
      SternBrocotRunGeometry.sbHeight (SternBrocotRunGeometry.runWord newest ns) :=
  SternBrocotRunGeometry.sbHeight_runWord_fib_lower newest ns hpos

/-- The all-unit alternating spine attains the Fibonacci floor exactly. -/
theorem stern_brocot_unit_run_height_eq_fib (r : ℕ) :
    SternBrocotRunGeometry.runHeight (List.replicate r 1) = Nat.fib (r + 3) :=
  SternBrocotRunGeometry.runHeight_replicate_one r

/-- Exact two-run height, the finite identity behind the second induced
Lambert layer. -/
theorem stern_brocot_two_run_height (m n : ℕ) :
    SternBrocotRunGeometry.runHeight [m, n] = (m + 1) * (n + 1) + 1 :=
  SternBrocotRunGeometry.runHeight_pair m n

/-- Exact first two induced contributions: the root has mass `1/4`, and the
two one-run cusps together have mass `1/2`. -/
theorem stern_brocot_zero_run_mass_eq_quarter :
    SternBrocotRunGeometry.zeroRunMass = 1 / 4 :=
  SternBrocotRunGeometry.zeroRunMass_eq_quarter

theorem stern_brocot_one_run_mass_eq_half :
    SternBrocotRunGeometry.oneRunMass = 1 / 2 :=
  SternBrocotRunGeometry.oneRunMass_eq_half

/-- Natural run-resolvent exponent clearing is exactly two below the
Fibonacci height scale. -/
theorem stern_brocot_natural_run_denominator_exponent_add_two (r : ℕ) :
    SternBrocotRunGeometry.naturalRunDenominatorExponent r + 2 = Nat.fib (r + 3) :=
  SternBrocotRunGeometry.naturalRunDenominatorExponent_add_two r

/-! ## Wave 21: the totient-tail period killer — rationality itself is the enemy

Every earlier wave attacked digits (force a zero corridor); wave 20 measured why
that fails (`√log` affordance vs `log` need).  Wave 21 attacks the PERIOD:
rationality of `S` forces the local totient tail `R_N = ∑_{j≥1} φ(N+j)/2ʲ` to
obey `R_{N+h} - R_N ∈ ℤ` eventually (tail-period law), and killing one `(h, N)`
is a finite decidable residue certificate with forbidden zone `O(N)` inside
modulus `2^L ≈ N³` — the proof no longer has to HIT a measure-zero target, only
MISS a vanishing one.  The reduction is complete: a certified kill supply at
every scale proves #249.  Proof bodies: `TotientTailPeriodKiller.lean`. -/

/-- **Shift identity**: `2^N·S = Φ_N + R_N` — the local totient tail is the
fractional layer of `2^N·S`. -/
theorem two_pow_mul_totient_series_eq_prefix_add_tail (N : ℕ) :
    (2 : ℝ) ^ N * (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = (TotientTailPeriodKiller.totientPrefix N : ℝ)
        + TotientTailPeriodKiller.totientTail N :=
  TotientTailPeriodKiller.two_pow_mul_totient_series_eq N

/-- **Certificate soundness**: a residue of the window discrepancy `A_{h,N,L}`
modulo `2^L` outside the radius-`(N+h+L+2)` neighbourhood of `0` kills period `h`
at position `N` — the tail difference is provably not an integer. -/
theorem totient_tail_diff_not_int_of_certified_kill {h N L : ℕ}
    (hcert : TotientTailPeriodKiller.certifiedKill h N L) :
    TotientTailPeriodKiller.totientTail (N + h) - TotientTailPeriodKiller.totientTail N
      ∉ Set.range ((↑) : ℤ → ℝ) :=
  TotientTailPeriodKiller.tail_diff_notMem_int_of_certifiedKill hcert

/-- **Tail-period law**: if `S` is rational then some period `h ≥ 1` makes every
shifted tail difference an integer from the pre-period `v₂(den)` on. -/
theorem rational_totient_series_forces_eventual_tail_period
    (hrat : ¬ Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      TotientTailPeriodKiller.totientTail (N + h) - TotientTailPeriodKiller.totientTail N
        ∈ Set.range ((↑) : ℤ → ℝ) :=
  TotientTailPeriodKiller.eventual_period_of_not_irrational hrat

/-- **The wave-21 reduction (the throat of #249)**: a certified period-kill supply
— every period `h ≥ 1` killed beyond every threshold — proves `S` irrational. -/
theorem irrational_totient_series_of_period_kill_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L,
      TotientTailPeriodKiller.certifiedKill h N L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_certificate_supply hsupply

/-- **Concrete deposit**: every period `h ≤ 8` is certified dead at
`(N, L) = (12, 16)` — machine-checked residue certificates. -/
theorem totient_tail_period_killed_upto_eight :
    ∀ h ∈ Finset.Icc 1 8, TotientTailPeriodKiller.certifiedKill h 12 16 :=
  TotientTailPeriodKiller.certifiedKill_all_small

/-- **Concrete denominator exclusion**: `S` is not a rational whose denominator
divides `2¹²·(2ʰ-1)` for any `1 ≤ h ≤ 8` — no dyadic rational up to `2¹²`, and
no odd part whose multiplicative order of `2` is at most `8`. -/
theorem totient_series_ne_rat_of_den_dvd_pow_two_mul_mersenne (r : ℚ) (h : ℕ)
    (h1 : 1 ≤ h) (h8 : h ≤ 8) (hdvd : (r.den : ℕ) ∣ 2 ^ 12 * (2 ^ h - 1)) :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (r : ℝ) :=
  TotientTailPeriodKiller.totient_series_ne_rat_of_den_dvd r h h1 h8 hdvd

/-! ## Wave 22: carry-survivor extinction and the multiple-period collapse

Rationality gives more than the wave-21 socket spent: if `h₀` is an eventual
binary period, every multiple `m·h₀` is one too (pure telescoping), so the
supply obligation collapses from ∀h to one kill per divisibility ray — and
further onto the single ℕ-indexed family `lcm(1..t)`.  And the bounded-orbit
reformulation is now kernel-checked: an integer tail difference launches an
exact integer carry orbit trapped in a linear strip; the decidable survivor
certificate verifies every candidate escapes.  Proof bodies:
`CarrySurvivorExtinction.lean`. -/

/-- **Carry recurrence**: `R_{M+1} = 2·R_M - φ(M+1)` — doubling the tail shifts
the window by one and expels the head totient. -/
theorem totient_tail_carry_recurrence (M : ℕ) :
    TotientTailPeriodKiller.totientTail (M + 1)
      = 2 * TotientTailPeriodKiller.totientTail M - (Nat.totient (M + 1) : ℝ) :=
  TotientTailPeriodKiller.totientTail_succ M

/-- **Survivor soundness**: the decidable carry-survivor certificate — every
integer candidate in the initial box escapes the strip `|·| < N+i+h+2` within
`K` steps — kills period `h` at position `N`. -/
theorem totient_tail_diff_not_int_of_survivor_kill {h N K : ℕ}
    (hkill : TotientTailPeriodKiller.survivorKill h N K) :
    TotientTailPeriodKiller.totientTail (N + h) - TotientTailPeriodKiller.totientTail N
      ∉ Set.range ((↑) : ℤ → ℝ) :=
  TotientTailPeriodKiller.tail_diff_notMem_int_of_survivorKill hkill

/-- **Period-ray telescoping**: the `m·h` tail difference is the sum of `m`
translated `h` tail differences — integrality flows down every multiple. -/
theorem totient_tail_diff_multiple_telescope (h N m : ℕ) :
    TotientTailPeriodKiller.totientTail (N + m * h) - TotientTailPeriodKiller.totientTail N
      = ∑ i ∈ Finset.range m,
          (TotientTailPeriodKiller.totientTail (N + i * h + h)
            - TotientTailPeriodKiller.totientTail (N + i * h)) :=
  TotientTailPeriodKiller.tail_diff_mul h N m

/-- **The wave-22 reduction**: a survivor kill along ANY multiple of each
primitive period, at arbitrarily large `N`, proves `S` irrational — the weakest
supply hypothesis in the ladder. -/
theorem irrational_totient_series_of_multiple_period_kill_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ K, TotientTailPeriodKiller.survivorKill (m * h₀) N K) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_multiple_survivor_supply hsupply

/-- The endpoint-window variant of the multiple-period reduction. -/
theorem irrational_totient_series_of_multiple_window_kill_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, TotientTailPeriodKiller.certifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_multiple_certificate_supply hsupply

/-- **One-parameter collapse**: survivor kills along the single family
`lcm(1..t)` at arbitrarily large `t` and `N` prove #249. -/
theorem irrational_totient_series_of_lcm_period_kill_supply
    (hsupply : ∀ t₀ N₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ K,
      TotientTailPeriodKiller.survivorKill (TotientTailPeriodKiller.periodLcm t) N K) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_survivor_supply hsupply

/-- **Strictness witness**: at `(h, N) = (1, 57)` the survivor certificate kills
at depth `8` while every endpoint window `L ≤ 8` fails — the survivor predicate
is strictly stronger at equal budget (and measured near-equivalent in minimal
depth by the wave-22 probe). -/
theorem totient_tail_survivor_strict_at_equal_budget :
    TotientTailPeriodKiller.survivorKill 1 57 8
      ∧ ∀ L ∈ Finset.Icc 1 8, ¬ TotientTailPeriodKiller.certifiedKill 1 57 L :=
  TotientTailPeriodKiller.survivor_strict_at_equal_budget

/-- **Concrete deposit**: every period `h ≤ 16` is certified dead at
`(N, L) = (14, 9)` — twice the wave-21 period range in a smaller window. -/
theorem totient_tail_period_killed_upto_sixteen :
    ∀ h ∈ Finset.Icc 1 16, TotientTailPeriodKiller.certifiedKill h 14 9 :=
  TotientTailPeriodKiller.certifiedKill_all_upto_sixteen

/-- **Extended denominator exclusion**: `S` is not a rational whose denominator
divides `2¹⁴·(2ʰ-1)` for any `1 ≤ h ≤ 16` — subsumes the wave-21 lattice on
both axes. -/
theorem totient_series_ne_rat_of_den_dvd_pow_two_mul_mersenne_upto_sixteen
    (r : ℚ) (h : ℕ) (h1 : 1 ≤ h) (h16 : h ≤ 16)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1)) :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (r : ℝ) :=
  TotientTailPeriodKiller.totient_series_ne_rat_of_den_dvd_upto_sixteen r h h1 h16 hdvd

/-! ## Wave 23: the diagonal lcm collapse and the lcm-ray window structure

Wave 22 collapsed the supply throat onto the one-parameter period family
`lcm(1..t)` but left the position `N` free.  Wave 23 removes the second
parameter: standing AT the ray point `N = lcm(1..t)` still beats every
hypothetical rational — any `t ≥ max(h₀, N₀)` satisfies `h₀ ∣ lcm(1..t)` and
`lcm(1..t) ≥ t ≥ N₀` simultaneously — so #249 follows from a SINGLE ℕ-indexed
sequence of decidable statements `P t := ∃ L, certifiedKill(lcm(1..t),
lcm(1..t), L)` holding for infinitely many `t`.  Below `2t` every window
index divides the period except bare prime powers in `(t, 2t)`, and clean
divisors split the window totient exactly — the first coordinates in which
the open supply is structured arithmetic rather than totient noise.  Proof
bodies: `LcmDiagonalReduction.lean`. -/

/-- **Endpoint lcm collapse (general position)**: certified window kills along
`lcm(1..t)` at arbitrarily large `t` and `N` prove #249 — fills the endpoint
gap of the wave-22 survivor-only lcm reduction. -/
theorem irrational_totient_series_of_lcm_window_kill_supply
    (hsupply : ∀ t₀ N₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ L,
      TotientTailPeriodKiller.certifiedKill (TotientTailPeriodKiller.periodLcm t) N L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_certificate_supply hsupply

/-- **The wave-23 diagonal collapse**: #249 follows from ONE ℕ-indexed sequence
of decidable statements — the endpoint certificate firing on the diagonal
`(h, N) = (lcm(1..t), lcm(1..t))` for infinitely many `t`.  No second
parameter remains. -/
theorem irrational_totient_series_of_lcm_diagonal_window_kill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
      TotientTailPeriodKiller.certifiedKill (TotientTailPeriodKiller.periodLcm t)
        (TotientTailPeriodKiller.periodLcm t) L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_certificate_supply hsupply

/-- Survivor variant of the diagonal collapse. -/
theorem irrational_totient_series_of_lcm_diagonal_period_kill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ K,
      TotientTailPeriodKiller.survivorKill (TotientTailPeriodKiller.periodLcm t)
        (TotientTailPeriodKiller.periodLcm t) K) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_survivor_supply hsupply

/-- **Window structure of the lcm ray**: below `2t` every non-divisor of
`lcm(1..t)` is a bare prime power exceeding `t` — all other window indices
divide the period. -/
theorem period_lcm_window_index_prime_pow_of_not_dvd {t j : ℕ} (hj : 0 < j)
    (hlt : j < 2 * t) (hnd : ¬ j ∣ TotientTailPeriodKiller.periodLcm t) :
    ∃ p k : ℕ, Nat.Prime p ∧ j = p ^ k ∧ t < j :=
  TotientTailPeriodKiller.eq_prime_pow_of_not_dvd_periodLcm hj hlt hnd

/-- **Lcm-ray window factorisation**: on a clean divisor `j` of `lcm(1..t)`
the window totient splits exactly into the known local part `φ(j)` and a
cofactor totient whose argument is forced `≡ 1` mod every non-exhausted
prime of `j`. -/
theorem totient_period_lcm_ray_factorisation {t j : ℕ} (q : ℕ)
    (hdvd : j ∣ TotientTailPeriodKiller.periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j →
      p ∣ (TotientTailPeriodKiller.periodLcm t / j)) :
    Nat.totient (q * TotientTailPeriodKiller.periodLcm t + j)
      = Nat.totient j
        * Nat.totient (q * (TotientTailPeriodKiller.periodLcm t / j) + 1) :=
  TotientTailPeriodKiller.totient_periodLcm_ray_split q hdvd hclean

/-- **Diagonal deposits**: the wave-23 predicate `P t` is kernel-checked for
every `t ≤ 6` at the probe-tabulated depths. -/
theorem totient_tail_period_lcm_diagonal_killed_upto_six :
    ∀ t ∈ Finset.Icc 1 6,
      TotientTailPeriodKiller.certifiedKill (TotientTailPeriodKiller.periodLcm t)
        (TotientTailPeriodKiller.periodLcm t)
        (TotientTailPeriodKiller.diagonalKillDepth t) :=
  TotientTailPeriodKiller.certifiedKill_periodLcm_diagonal_upto_six

/-- `P 7` and `P 8`: diagonal kills at `lcm(1..7) = 420` (depth `14`) and
`lcm(1..8) = 840` (depth `15`). -/
theorem totient_tail_period_lcm_diagonal_killed_at_seven_and_eight :
    TotientTailPeriodKiller.certifiedKill (TotientTailPeriodKiller.periodLcm 7)
        (TotientTailPeriodKiller.periodLcm 7) 14
      ∧ TotientTailPeriodKiller.certifiedKill (TotientTailPeriodKiller.periodLcm 8)
        (TotientTailPeriodKiller.periodLcm 8) 15 :=
  ⟨TotientTailPeriodKiller.certifiedKill_periodLcm_diagonal_at_seven,
    TotientTailPeriodKiller.certifiedKill_periodLcm_diagonal_at_eight⟩

/-! ## Wave 24: the lcm-cone flatness law and the annihilator calculus

Wave 23 stood at one diagonal cell of the lcm lattice.  Wave 24 spends the
rationality hypothesis all the way: rationality forces ONE fractional
constant on the entire lcm cone `{k·lcm(1..t) : k ≥ 1}`, so every cone
difference is forced integral — and one certified annihilator anywhere on
the cone at arbitrarily large scale proves #249.  The diagonal, all q-ray
steps, q-gaps, and the prime-jump pairs `lcm(1..t+1) - lcm(1..t)` are cells
of ONE supply theorem.  The endpoint certificate is also proved COMPLETE
(kills exist exactly at non-integers), so the frontier now reads in pure
non-integrality form.  Rank-2 second-difference certificates land sound,
with the measured verdict (probe v2: shadow cancelled, kills NOT shallower)
kernel-checked at a fixture cell.  Proof bodies: `LcmConeFlatness.lean`. -/

/-- **Scale-ladder divisibility**: `lcm(1..t) ∣ lcm(1..u)` for `t ≤ u` — the
cones at all scales form one directed system, so cross-scale cone pairs are
same-scale pairs on the finer ray. -/
theorem period_lcm_dvd_period_lcm_of_le {t u : ℕ} (htu : t ≤ u) :
    TotientTailPeriodKiller.periodLcm t ∣ TotientTailPeriodKiller.periodLcm u :=
  TotientTailPeriodKiller.periodLcm_dvd_periodLcm htu

/-- **The lcm-cone flatness law**: if the totient series is rational, then
from some scale on the whole lcm cone is fractionally flat — every difference
`R_{q·H_t + m·H_t} - R_{q·H_t}` is an integer. -/
theorem rational_totient_series_forces_lcm_cone_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      TotientTailPeriodKiller.totientTail
          (q * TotientTailPeriodKiller.periodLcm t + m * TotientTailPeriodKiller.periodLcm t)
        - TotientTailPeriodKiller.totientTail (q * TotientTailPeriodKiller.periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ) :=
  TotientTailPeriodKiller.rational_totient_series_forces_lcm_cone_flatness hrat

/-- **The wave-24 cone collapse**: certified window kills anywhere on the
two-multiplier lcm cone — `(h, N) = (m·H_t, q·H_t)` at arbitrarily large
`t` — prove #249.  The wave-23 diagonal is the cell `q = m = 1`. -/
theorem irrational_totient_series_of_lcm_cone_window_kill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
      TotientTailPeriodKiller.certifiedKill
        (m * TotientTailPeriodKiller.periodLcm t)
        (q * TotientTailPeriodKiller.periodLcm t) L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_certificate_supply hsupply

/-- **Certificate completeness**: some depth certifies `(h, N)` iff the tail
difference `R_{N+h} - R_N` is a non-integer.  Certificates are receipts;
non-integrality is the object. -/
theorem totient_tail_window_kill_exists_iff_tail_diff_not_int (h N : ℕ) :
    (∃ L, TotientTailPeriodKiller.certifiedKill h N L) ↔
      TotientTailPeriodKiller.totientTail (N + h)
          - TotientTailPeriodKiller.totientTail N ∉ Set.range ((↑) : ℤ → ℝ) :=
  TotientTailPeriodKiller.exists_certifiedKill_iff_tail_diff_notMem_int h N

/-- **The diagonal frontier in pure form**: non-integral diagonal tail
differences at arbitrarily large `t` prove #249 — no certificate vocabulary
in the hypothesis. -/
theorem irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧
      TotientTailPeriodKiller.totientTail
          (TotientTailPeriodKiller.periodLcm t + TotientTailPeriodKiller.periodLcm t)
        - TotientTailPeriodKiller.totientTail (TotientTailPeriodKiller.periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
    hsupply

/-- **The cone frontier in pure form**: one non-integral cone difference at
arbitrarily large scale proves #249. -/
theorem irrational_totient_series_of_lcm_cone_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m : ℕ, 0 < q ∧
      TotientTailPeriodKiller.totientTail
          (q * TotientTailPeriodKiller.periodLcm t + m * TotientTailPeriodKiller.periodLcm t)
        - TotientTailPeriodKiller.totientTail (q * TotientTailPeriodKiller.periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonintegrality_supply hsupply

/-- **Rank-2 soundness**: a certified second-difference residue proves
`(R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N)` is not an integer. -/
theorem totient_tail_second_diff_not_int_of_rank_two_kill {h N L : ℕ}
    (hcert : TotientTailPeriodKiller.certifiedRank2Kill h N L) :
    (TotientTailPeriodKiller.totientTail (N + 2 * h)
          - TotientTailPeriodKiller.totientTail (N + h))
        - (TotientTailPeriodKiller.totientTail (N + h)
          - TotientTailPeriodKiller.totientTail N) ∉ Set.range ((↑) : ℤ → ℝ) :=
  TotientTailPeriodKiller.second_diff_notMem_int_of_certifiedRank2Kill hcert

/-- **Rank-2 cone supply**: certified second-difference kills along the
q-rays of the lcm cone at arbitrarily large `t` prove #249. -/
theorem irrational_totient_series_of_lcm_qray_rank_two_kill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q L : ℕ, 0 < q ∧
      TotientTailPeriodKiller.certifiedRank2Kill (TotientTailPeriodKiller.periodLcm t)
        (q * TotientTailPeriodKiller.periodLcm t) L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_qray_rank2_supply hsupply

/-- **Cone-lattice deposits off the diagonal**: certified kills at
`(t, q, m) = (2, 3, 1)`, `(3, 2, 2)`, `(3, 1, 3)` at the probe-tabulated
depths. -/
theorem totient_tail_lcm_cone_cells_killed :
    TotientTailPeriodKiller.certifiedKill (1 * TotientTailPeriodKiller.periodLcm 2)
        (3 * TotientTailPeriodKiller.periodLcm 2) 6
      ∧ TotientTailPeriodKiller.certifiedKill (2 * TotientTailPeriodKiller.periodLcm 3)
        (2 * TotientTailPeriodKiller.periodLcm 3) 7
      ∧ TotientTailPeriodKiller.certifiedKill (3 * TotientTailPeriodKiller.periodLcm 3)
        (1 * TotientTailPeriodKiller.periodLcm 3) 8 :=
  TotientTailPeriodKiller.certifiedKill_lcm_cone_cells

/-- **The measured rank-2 verdict, kernel-checked**: at `(h, N) = (1, 8)` the
rank-1 certificate fires at depth `8`, no rank-2 certificate exists at any
depth `≤ 8`, and rank-2 first fires at depth `9` — sound but not shallower
(probe v2, `t ≤ 20`: rank-1 at least as shallow in 30 of 40 cells). -/
theorem totient_tail_rank_two_kill_sound_but_not_shallower_cell :
    TotientTailPeriodKiller.certifiedKill 1 8 8
      ∧ (∀ L ∈ Finset.Icc 1 8, ¬ TotientTailPeriodKiller.certifiedRank2Kill 1 8 L)
      ∧ TotientTailPeriodKiller.certifiedRank2Kill 1 8 9 :=
  TotientTailPeriodKiller.rank2_kill_sound_but_not_shallower_at_cell

/-- The diagonal tail differences at `t = 7` and `t = 8` are non-integers —
the wave-23 corollary extended past its decide ceiling. -/
theorem totient_tail_period_lcm_diagonal_not_int_at_seven_and_eight :
    (TotientTailPeriodKiller.totientTail
          (TotientTailPeriodKiller.periodLcm 7 + TotientTailPeriodKiller.periodLcm 7)
        - TotientTailPeriodKiller.totientTail (TotientTailPeriodKiller.periodLcm 7)
        ∉ Set.range ((↑) : ℤ → ℝ))
      ∧ (TotientTailPeriodKiller.totientTail
          (TotientTailPeriodKiller.periodLcm 8 + TotientTailPeriodKiller.periodLcm 8)
        - TotientTailPeriodKiller.totientTail (TotientTailPeriodKiller.periodLcm 8)
        ∉ Set.range ((↑) : ℤ → ℝ)) :=
  TotientTailPeriodKiller.tail_diff_not_int_periodLcm_diagonal_seven_eight

/-! ## Wave 25: the cone non-flatness refuter — killing the menu, not the pair

Wave 24 flattened the whole lcm cone under rationality; every certificate
still interrogated flatness through one PAIR of cone points.  Wave 25
interrogates a finite MENU of cone vertices at once: each vertex pins
`2^L·R_{q·H}` inside a one-sided arc of radius `q·H+L+2`, joint flatness
forces a common point of all the arcs, and `coneNonflatCert` refutes every
candidate common point with `|Q|²` one-sided endpoint checks (argmin lemma:
the vertex of minimal deep tail would be a common left endpoint).  Each arc
charges only its OWN one-sided radius — `certifiedKill` charges the top
vertex's radius on both sides — so the menu floor is HALF the pairwise
floor: strict depth wins are kernel-checked below, including a genuinely
JOINT cell (`t = 8`, menu `[1,2,3,4]`, depth `12` — at floor, slack zero)
where the menu is inconsistent while every pair alone stays consistent.
The lcm-jump lane is named as a supply theorem with no side conditions.
Proof bodies: `LcmConeNonflat.lean`. -/

/-- **Menu refutation soundness**: a firing non-flatness certificate (with
one-sided floors) forces some pair of menu vertices to have a non-integral
tail difference. -/
theorem totient_tail_nonintegral_pair_of_cone_nonflat_cert {H L : ℕ}
    {Q : List ℕ} (hQ : Q ≠ [])
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : TotientTailPeriodKiller.coneNonflatCert H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      TotientTailPeriodKiller.totientTail (qj * H)
        - TotientTailPeriodKiller.totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ) :=
  TotientTailPeriodKiller.exists_nonintegral_pair_of_coneNonflatCert hQ hfloor hcert

/-- **The cone non-flatness supply theorem**: one firing vertex menu at
arbitrarily large scale proves #249. -/
theorem irrational_totient_series_of_lcm_cone_nonflat_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : List ℕ, Q ≠ [] ∧
      (∀ q ∈ Q, 0 < q) ∧
      (∀ q ∈ Q, (q * TotientTailPeriodKiller.periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      TotientTailPeriodKiller.coneNonflatCert
        (TotientTailPeriodKiller.periodLcm t) L Q) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonflat_supply hsupply

/-- **The lcm-jump supply theorem**: certified kills at the jumps
`(h, N) = (H_{t+1} - H_t, H_t)` at arbitrarily large `t` prove #249 — the
cone cells `(q, m) = (1, p-1)`, with no side conditions at all. -/
theorem irrational_totient_series_of_lcm_jump_window_kill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      TotientTailPeriodKiller.certifiedKill
        (TotientTailPeriodKiller.periodLcm (t + 1) - TotientTailPeriodKiller.periodLcm t)
        (TotientTailPeriodKiller.periodLcm t) L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) :=
  TotientTailPeriodKiller.irrational_totient_series_of_lcm_jump_kill_supply hsupply

/-- First firing menus at the probe-tabulated smallest cells. -/
theorem totient_tail_cone_nonflat_cells_certified :
    TotientTailPeriodKiller.coneNonflatCert
        (TotientTailPeriodKiller.periodLcm 1) 5 [1, 2, 3]
      ∧ TotientTailPeriodKiller.coneNonflatCert
        (TotientTailPeriodKiller.periodLcm 2) 5 [1, 2, 3, 4]
      ∧ TotientTailPeriodKiller.coneNonflatCert
        (TotientTailPeriodKiller.periodLcm 3) 6 [1, 2, 3] :=
  TotientTailPeriodKiller.coneNonflatCert_cells

/-- **The measured strict win, kernel-checked**: at `t = 2` the menu
`[1, 3]` refutes joint flatness at depth `8` while no pairwise certificate
exists at any depth `≤ 8` (the pair first kills at depth `9`). -/
theorem totient_tail_cone_nonflat_strict_win_at_cell :
    TotientTailPeriodKiller.coneNonflatCert
        (TotientTailPeriodKiller.periodLcm 2) 8 [1, 3]
      ∧ (∀ L ∈ Finset.Icc 1 8,
        ¬ TotientTailPeriodKiller.certifiedKill
          (2 * TotientTailPeriodKiller.periodLcm 2)
          (1 * TotientTailPeriodKiller.periodLcm 2) L)
      ∧ TotientTailPeriodKiller.certifiedKill
        (2 * TotientTailPeriodKiller.periodLcm 2)
        (1 * TotientTailPeriodKiller.periodLcm 2) 9 :=
  TotientTailPeriodKiller.cone_nonflat_strict_win_at_cell

/-- **The measured joint win, kernel-checked**: at `t = 2` the menu
`[2, 3, 4]` refutes joint flatness at depth `5` while every 2-vertex
submenu refuter and every pairwise certificate is silent at depth `5` —
the menu is inconsistent at a depth where every pair alone stays
consistent. -/
theorem totient_tail_cone_nonflat_joint_win_at_cell :
    TotientTailPeriodKiller.coneNonflatCert
        (TotientTailPeriodKiller.periodLcm 2) 5 [2, 3, 4]
      ∧ (¬ TotientTailPeriodKiller.coneNonflatCert
        (TotientTailPeriodKiller.periodLcm 2) 5 [2, 3])
      ∧ (¬ TotientTailPeriodKiller.coneNonflatCert
        (TotientTailPeriodKiller.periodLcm 2) 5 [2, 4])
      ∧ (¬ TotientTailPeriodKiller.coneNonflatCert
        (TotientTailPeriodKiller.periodLcm 2) 5 [3, 4])
      ∧ (¬ TotientTailPeriodKiller.certifiedKill
        (1 * TotientTailPeriodKiller.periodLcm 2)
        (2 * TotientTailPeriodKiller.periodLcm 2) 5)
      ∧ (¬ TotientTailPeriodKiller.certifiedKill
        (2 * TotientTailPeriodKiller.periodLcm 2)
        (2 * TotientTailPeriodKiller.periodLcm 2) 5)
      ∧ (¬ TotientTailPeriodKiller.certifiedKill
        (1 * TotientTailPeriodKiller.periodLcm 2)
        (3 * TotientTailPeriodKiller.periodLcm 2) 5) :=
  TotientTailPeriodKiller.cone_nonflat_joint_win_at_cell

/-! ## Wave 27: exactness and depth-monotonicity of the menu refuter

Wave 26 measured the fixed-menu advisory mechanism dead (limit-shape
endpoint model refuted at every tested scale) while the firing
observations survived; what earns kernel status this wave is the exact
calculus those measurements ran on.  The probe gate "certificate fires iff
no common point exists" and the depth law behind `nonflat_L_min` are now
theorems: a purely combinatorial argmin (no analytic tails), the window
recursion `P_{L+1} = 2·P_L + φ(M+L+1)`, and a halving descent for common
points.  Consequence: a firing certificate fires at EVERY deeper depth
(floors held), so `∃L` in any supply statement collapses onto canonical
large-enough depths and `nonflat_L_min` is THE firing threshold.
Proof bodies: `LcmConeNonflat.lean`. -/

/-- **Exactness of the menu refuter**: the certificate fires iff the menu
arcs share NO common point — the probe's brute-force gate
(`nonflat_matches_common_point_bruteforce`), now a theorem at every
cell. -/
theorem totient_tail_cone_nonflat_cert_iff_no_common_point {H L : ℕ}
    {Q : List ℕ} (hQ : Q ≠ []) :
    TotientTailPeriodKiller.coneNonflatCert H L Q
      ↔ ¬ TotientTailPeriodKiller.coneCommonPoint H L Q :=
  TotientTailPeriodKiller.coneNonflatCert_iff_no_common_point hQ

/-- **Halving descent**: a common point of the depth-`L+1` menu arcs
yields one at depth `L` (floors held at `L`). -/
theorem totient_tail_cone_common_point_halving_descent {H L : ℕ}
    {Q : List ℕ}
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (h : TotientTailPeriodKiller.coneCommonPoint H (L + 1) Q) :
    TotientTailPeriodKiller.coneCommonPoint H L Q :=
  TotientTailPeriodKiller.coneCommonPoint_of_succ hfloor h

/-- **Depth monotonicity of the menu refuter**: a firing certificate keeps
firing at every deeper depth (floors held at the base), so
`nonflat_L_min` is THE firing threshold. -/
theorem totient_tail_cone_nonflat_cert_depth_monotone {H L L' : ℕ}
    {Q : List ℕ} (hQ : Q ≠ [])
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : TotientTailPeriodKiller.coneNonflatCert H L Q)
    (hle : L ≤ L') :
    TotientTailPeriodKiller.coneNonflatCert H L' Q :=
  TotientTailPeriodKiller.coneNonflatCert_mono_of_le hQ hfloor hcert hle

/-- **Menu monotonicity**: a firing certificate keeps firing for every
supermenu at the SAME depth — adding cone vertices cannot refill an empty
arc intersection.  This is why the wave-25 joint wins exist (firing runs
upward in the menu) and why a small seed suffices. -/
theorem totient_tail_cone_nonflat_cert_supermenu {H L : ℕ}
    {Q Q' : List ℕ} (hQ : Q ≠ [])
    (hsub : ∀ q ∈ Q, q ∈ Q')
    (hcert : TotientTailPeriodKiller.coneNonflatCert H L Q) :
    TotientTailPeriodKiller.coneNonflatCert H L Q' :=
  TotientTailPeriodKiller.coneNonflatCert_supermenu hQ hsub hcert

/-- **Seed-lift**: a small seed menu firing at its own floor inflates to
every supermenu at every deeper depth (depth monotonicity up, menu
monotonicity out).  For supply it suffices that some prefix seed fires at
its floor for arbitrarily large `t`. -/
theorem totient_tail_cone_nonflat_cert_seed_lift {H L L' : ℕ}
    {Q Q' : List ℕ} (hQ : Q ≠ [])
    (hsub : ∀ q ∈ Q, q ∈ Q')
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : TotientTailPeriodKiller.coneNonflatCert H L Q)
    (hle : L ≤ L') :
    TotientTailPeriodKiller.coneNonflatCert H L' Q' :=
  TotientTailPeriodKiller.coneNonflatCert_seed_lift hQ hsub hfloor hcert hle

end Erdos257PeriodNoncollapse
