import ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature
import Erdos257PeriodNoncollapse.CertificateKernel
import Erdos257PeriodNoncollapse.TotientActualLcmTopEdgeStaircase
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Erdős #249: the exact `X - 2` cyclotomic layer and anchored period kills

For the polynomial `X - 2`, the cyclic resultant at index `n` is `2^n - 1`.
This file discharges the previously abstract prime-ray producer completely:
every prime divisor of `2^q - 1`, for prime `q`, is `1 mod q`; consequently
the prime divisors appearing in these layers are unbounded.

That arithmetic support theorem does not itself prove irrationality of the
binary totient series.  The second half records the exact missing bridge:
cofinally remote certified tail discrepancies, with the period allowed to be
a multiple of the cyclotomic anchor.  Two substantial finite certificates are
also checked by the Lean kernel.
-/

namespace ErdosProblems.Erdos249.CyclotomicAnchoredKill

open ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.TotientTailPeriodKiller

/-- The cyclotomic layer for the exact polynomial `X - 2`. -/
def mersenneLayer (n : ℕ) : ℕ := 2 ^ n - 1

/-- A prime divisor of the prime-index Mersenne layer has exact order `q`
for the residue of `2`, and hence is congruent to `1` modulo `q`. -/
theorem prime_index_dvd_pred
    {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hdiv : p ∣ mersenneLayer q) :
    q ∣ p - 1 := by
  have hpTwo : p ≠ 2 := by
    intro hp2
    subst p
    have hqZero : q = 0 := by
      simpa [mersenneLayer, Nat.dvd_iff_mod_eq_zero] using hdiv
    exact hq.ne_zero hqZero
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvdTwo : p ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    rcases (Nat.dvd_prime Nat.prime_two).mp hpDvdTwo with hpOne | hpEqTwo
    · exact hp.ne_one hpOne
    · exact hpTwo hpEqTwo
  have hpow : (2 : ZMod p) ^ q = 1 := by
    have hmod : 2 ^ q ≡ 1 [MOD p] :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow q 2 (by norm_num))).2 hdiv |>.symm
    have hcast :=
      (ZMod.natCast_eq_natCast_iff (2 ^ q) 1 p).2 hmod
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  have horderDvdQ : orderOf (2 : ZMod p) ∣ q :=
    orderOf_dvd_of_pow_eq_one hpow
  have horderNeOne : orderOf (2 : ZMod p) ≠ 1 := by
    intro horder
    have hcast : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp horder
    have hcast' : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hcast
    have hmod : 2 ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff 2 1 p).mp hcast'
    have hpDvdOne : p ∣ 1 :=
      (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp hmod.symm
    exact hp.not_dvd_one hpDvdOne
  have horderEqQ : orderOf (2 : ZMod p) = q := by
    rcases (Nat.dvd_prime hq).mp horderDvdQ with horder | horder
    · exact (horderNeOne horder).elim
    · exact horder
  simpa [horderEqQ] using ZMod.orderOf_dvd_card_sub_one htwo

/-- Exact degree-one order consumer for the polynomial `X - 2`. -/
theorem mersenneLayer_orderConsumer :
    BoundedDegreeOrderConsumer mersenneLayer 1 1 := by
  intro q p hq hp hdiv
  refine ⟨1, by omega, by omega, ?_⟩
  have hdiv' : p ∣ mersenneLayer q := by simpa using hdiv
  simpa using prime_index_dvd_pred hq hp hdiv'

/-- Prime-index Mersenne layers are nontrivial and coprime to their index. -/
theorem mersenneLayer_layerSupply :
    PrimeRayLayerSupply mersenneLayer 1 := by
  refine ⟨3, ?_⟩
  intro q hq hq3
  have hqPos : 0 < q := hq.pos
  have hlarge : 1 < mersenneLayer (1 * q) := by
    simp only [one_mul, mersenneLayer]
    have : 2 ^ 3 ≤ 2 ^ q :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hq3
    norm_num at this ⊢
    omega
  refine ⟨hlarge, ?_⟩
  have hnot : ¬ q ∣ mersenneLayer (1 * q) := by
    intro hdiv
    have hpred := prime_index_dvd_pred hq hq (by simpa using hdiv)
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < q - 1) (by omega : q - 1 < q)) hpred
  simpa using (hq.coprime_iff_not_dvd.mpr (by simpa using hnot)).symm

/-- **Unconditional unbounded prime support for the exact `X - 2` layers.**
For every size bound and every lower bound on the prime index, a remote
prime-index Mersenne layer has a prime divisor exceeding the size bound. -/
theorem mersenneLayer_unboundedPrimeDivisorSupply :
    UnboundedPrimeDivisorSupply mersenneLayer 1 :=
  unboundedPrimeDivisorSupply_of_orderConsumer
    (by omega) mersenneLayer_layerSupply mersenneLayer_orderConsumer

/-! ## Prime-filtered carry candidates -/

/-- The first `H` totient-tail letters at `N`, cleared by `2^H`. -/
def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)

/-- Exact finite-block identity:
`(2^H-1) R_N = Q_(H,N) + (R_(N+H)-R_N)`. -/
theorem mersenne_mul_tail_eq_block_add_diff (H N : ℕ) :
    ((2 : ℝ) ^ H - 1) * totientTail N =
      (totientBlock H N : ℝ) +
        (totientTail (N + H) - totientTail N) := by
  have hblock :
      ((totientBlock H N : ℤ) : ℝ) / 2 ^ H =
        ∑ j ∈ Finset.range H,
          (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1) := by
    unfold totientBlock
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjH : j < H := Finset.mem_range.mp hj
    have hsplit :
        (2 : ℝ) ^ H = 2 ^ (H - 1 - j) * 2 ^ (j + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hleft : (2 : ℝ) ^ (H - 1 - j) ≠ 0 := by positivity
    have hright : (2 : ℝ) ^ (j + 1) ≠ 0 := by positivity
    rw [hsplit]
    field_simp
  have htail := totientTail_eq_partial_add_shifted N H
  rw [← hblock] at htail
  have hpow : (2 : ℝ) ^ H ≠ 0 := by positivity
  rw [htail]
  field_simp [hpow]
  ring

/-- Sliding the finite Mersenne block by one obeys the same affine
recurrence as the carry, up to the exact multiple
`(2^H-1) * φ(N+1)`. -/
theorem totientBlock_succ (H N : ℕ) :
    totientBlock H (N + 1) =
      2 * totientBlock H N -
        ((2 : ℤ) ^ H - 1) * (Nat.totient (N + 1) : ℤ) +
        deltaTotient H (N + 1) := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  have hblock := mersenne_mul_tail_eq_block_add_diff H N
  have hblockSucc := mersenne_mul_tail_eq_block_add_diff H (N + 1)
  have htail := totientTail_succ N
  have hdiff := tail_diff_succ H N
  rw [hdiff] at hblockSucc
  rw [htail] at hblockSucc
  linarith

/-- The prime-filtered residue propagates at every carry depth.  Thus the
endpoint is simultaneously constrained modulo the Mersenne prime and,
through the ordinary carry reset, modulo the relevant power of two. -/
theorem carryOrbit_modEq_neg_totientBlock_shift
    {H N p : ℕ} {d : ℤ} (hpM : p ∣ 2 ^ H - 1)
    (hmod : Int.ModEq (p : ℤ) d (-totientBlock H N)) :
    ∀ i : ℕ,
      Int.ModEq (p : ℤ) (carryOrbit H N d i)
        (-totientBlock H (N + i)) := by
  intro i
  induction i with
  | zero => simpa [carryOrbit] using hmod
  | succ i ih =>
      rw [Int.modEq_iff_dvd] at ih ⊢
      have hpMZ : (p : ℤ) ∣ (2 : ℤ) ^ H - 1 := by
        have hpow : 1 ≤ 2 ^ H := Nat.one_le_pow _ _ (by norm_num)
        have hcast :
            (((2 ^ H - 1 : ℕ) : ℤ)) = (2 : ℤ) ^ H - 1 := by
          rw [Nat.cast_sub hpow]
          norm_num
        rw [← hcast]
        exact Int.natCast_dvd_natCast.mpr hpM
      have hdouble :
          (p : ℤ) ∣
            2 * ((-totientBlock H (N + i)) -
              carryOrbit H N d i) :=
        dvd_mul_of_dvd_right ih 2
      have hmultiple :
          (p : ℤ) ∣
            ((2 : ℤ) ^ H - 1) *
              (Nat.totient (N + i + 1) : ℤ) :=
        dvd_mul_of_dvd_left hpMZ _
      have hcombined := dvd_add hdouble hmultiple
      convert hcombined using 1
      · rw [show N + (i + 1) = (N + i) + 1 by omega,
          totientBlock_succ, carryOrbit]
        ring

/-- **Product-modulus four-to-one collapse at a free basepoint.**  Under the
large-prime geometry `N < p` and `H ≤ p-1`, two states in the same
prime-filtered class cannot both remain in the sharp strip through depth
three.  Their initial spacing is a nonzero multiple of `p`; the dyadic carry
multiplies it by `8`, beyond the combined width of the two endpoint strips. -/
theorem primeBasepointFiltered_survivor_at_three_unique
    {H N p : ℕ} (hp : p.Prime) (hNp : N < p) (hH : H ≤ p - 1)
    {z w : ℤ}
    (hzMod : Int.ModEq (p : ℤ) z (-totientBlock H N))
    (hwMod : Int.ModEq (p : ℤ) w (-totientBlock H N))
    (hzSurv : |carryOrbit H N z 3| ≤ (N + H + 4 : ℤ))
    (hwSurv : |carryOrbit H N w 3| ≤ (N + H + 4 : ℤ)) :
    z = w := by
  by_contra hne
  have hzwMod : Int.ModEq (p : ℤ) z w :=
    hzMod.trans hwMod.symm
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hzwMod)
  have hkEq : w - z = (p : ℤ) * k := by
    simpa [mul_comm] using hk
  have hkNe : k ≠ 0 := by
    intro hkZero
    rw [hkZero, mul_zero] at hkEq
    exact hne (sub_eq_zero.mp hkEq).symm
  have horbit := carryOrbit_sub H N z w 3
  norm_num at horbit
  have hzBounds := abs_le.mp hzSurv
  have hwBounds := abs_le.mp hwSurv
  have hpTwoZ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hNZ : (N : ℤ) ≤ (p : ℤ) - 1 := by
    have hNpZ : (N : ℤ) < (p : ℤ) := by exact_mod_cast hNp
    omega
  have hHZ : (H : ℤ) ≤ (p : ℤ) - 1 := by
    have hHLt : H < p := by omega
    have hHLtZ : (H : ℤ) < (p : ℤ) := by exact_mod_cast hHLt
    omega
  rcases lt_or_gt_of_ne hkNe with hkNeg | hkPos
  · have hkLe : k ≤ -1 := by omega
    nlinarith
  · have hkGe : 1 ≤ k := by omega
    nlinarith

/-- **General product-modulus spacing.**  At depth `K`, two launches in one
class modulo `M` are separated by a multiple of `2^K M`.  Hence a strip of
radius strictly below `2^(K-1) M` contains at most one surviving state.
This isolates the quantitative fact behind both the clean-prime collapse
and any later full-Mersenne-quotient filter. -/
theorem modulusFiltered_survivor_unique
    {H N M K : ℕ} (hK : 1 ≤ K) (hM : 0 < M)
    {z w : ℤ}
    (hzMod : Int.ModEq (M : ℤ) z w)
    (hzSurv : |carryOrbit H N z K| ≤ (N + H + K + 1 : ℤ))
    (hwSurv : |carryOrbit H N w K| ≤ (N + H + K + 1 : ℤ))
    (hwidth :
      (N + H + K + 1 : ℤ) <
        (2 : ℤ) ^ (K - 1) * (M : ℤ)) :
    z = w := by
  by_contra hne
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hzMod)
  have hkEq : w - z = (M : ℤ) * k := by
    simpa [mul_comm] using hk
  have hkNe : k ≠ 0 := by
    intro hkZero
    rw [hkZero, mul_zero] at hkEq
    exact hne (sub_eq_zero.mp hkEq).symm
  have horbit := carryOrbit_sub H N z w K
  have hzBounds := abs_le.mp hzSurv
  have hwBounds := abs_le.mp hwSurv
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  have hpowPos : (0 : ℤ) < (2 : ℤ) ^ (K - 1) := by positivity
  have hpow :
      (2 : ℤ) ^ K = 2 * (2 : ℤ) ^ (K - 1) := by
    calc
      (2 : ℤ) ^ K = (2 : ℤ) ^ ((K - 1) + 1) :=
        congrArg (fun e : ℕ => (2 : ℤ) ^ e)
          (Nat.sub_add_cancel hK).symm
      _ = 2 * (2 : ℤ) ^ (K - 1) := by rw [pow_succ]; ring
  have hbaseNonneg :
      0 ≤ (2 : ℤ) ^ (K - 1) * (M : ℤ) :=
    mul_nonneg hpowPos.le hMZ.le
  rcases lt_or_gt_of_ne hkNe with hkNeg | hkPos
  · have hkNegGe : 1 ≤ -k := by omega
    have hscale :
        (2 : ℤ) ^ (K - 1) * (M : ℤ) ≤
          ((2 : ℤ) ^ (K - 1) * (M : ℤ)) * (-k) := by
      simpa using mul_le_mul_of_nonneg_left hkNegGe hbaseNonneg
    have horbitEq :
        carryOrbit H N z K - carryOrbit H N w K =
          2 * (((2 : ℤ) ^ (K - 1) * (M : ℤ)) * (-k)) := by
      rw [horbit, hpow]
      have hzw : z - w = -((M : ℤ) * k) := by
        nlinarith [hkEq]
      rw [hzw]
      ring
    nlinarith [hscale]
  · have hkGe : 1 ≤ k := by omega
    have hscale :
        (2 : ℤ) ^ (K - 1) * (M : ℤ) ≤
          ((2 : ℤ) ^ (K - 1) * (M : ℤ)) * k := by
      simpa using mul_le_mul_of_nonneg_left hkGe hbaseNonneg
    have horbitEq :
        carryOrbit H N z K - carryOrbit H N w K =
          -2 * (((2 : ℤ) ^ (K - 1) * (M : ℤ)) * k) := by
      rw [horbit, hpow]
      have hzw : z - w = -((M : ℤ) * k) := by
        nlinarith [hkEq]
      rw [hzw]
      ring
    nlinarith [hscale]

/-- Every denominator-compatible integer carry at a clean prime anchor must
leave the exact tail strip within `K` steps.  The congruence reduces the
unfiltered interval of `O(p)` candidates to at most four states. -/
def PrimeFilteredCarryKill (H p K : ℕ) : Prop :=
  ∀ j ∈ Finset.range (2 * (p + H) + 1),
    Int.ModEq (p : ℤ) ((j : ℤ) - (p + H : ℤ))
      (-totientBlock H (p - 1)) →
    ∃ i ∈ Finset.range (K + 1),
      carryOrbit H (p - 1) ((j : ℤ) - (p + H : ℤ)) i ≤
          -(p + H + i + 1 : ℤ) ∨
        (p + H + i + 1 : ℤ) ≤
          carryOrbit H (p - 1) ((j : ℤ) - (p + H : ℤ)) i

instance (H p K : ℕ) : Decidable (PrimeFilteredCarryKill H p K) := by
  unfold PrimeFilteredCarryKill
  infer_instance

/-- Least nonnegative representative of the denominator-forced carry
class. -/
def primeFilteredResidue (H p : ℕ) : ℤ :=
  (-totientBlock H (p - 1)) % (p : ℤ)

/-- Exact four-state normal form.  If `H ≤ p-1`, every filtered candidate
in the analytic initial box is one of
`r-2p, r-p, r, r+p`, where `r` is the least nonnegative filtered residue. -/
theorem primeFiltered_candidate_eq_one_of_four
    {H p : ℕ} (hp : p.Prime) (hH : H ≤ p - 1)
    {z : ℤ} (hbox : |z| ≤ (p + H : ℤ))
    (hmod : Int.ModEq (p : ℤ) z (-totientBlock H (p - 1))) :
    z = primeFilteredResidue H p - 2 * p ∨
      z = primeFilteredResidue H p - p ∨
      z = primeFilteredResidue H p ∨
      z = primeFilteredResidue H p + p := by
  let r : ℤ := primeFilteredResidue H p
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hrNonneg : 0 ≤ r := by
    dsimp [r, primeFilteredResidue]
    exact Int.emod_nonneg _ hpZ.ne'
  have hrLt : r < (p : ℤ) := by
    dsimp [r, primeFilteredResidue]
    exact Int.emod_lt_of_pos _ hpZ
  have hzmod : Int.ModEq (p : ℤ) z r := by
    exact hmod.trans (Int.mod_modEq (-totientBlock H (p - 1)) p).symm
  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.mp hzmod)
  have htEq : r - z = (p : ℤ) * t := by simpa [mul_comm] using ht
  have hzBounds := abs_le.mp hbox
  have hHZ : (H : ℤ) ≤ (p : ℤ) - 1 := by
    have hHLt : H < p := by omega
    have hHLtZ : (H : ℤ) < (p : ℤ) := by exact_mod_cast hHLt
    omega
  have htLower : (-1 : ℤ) ≤ t := by
    by_contra htBad
    have htLe : t ≤ -2 := by omega
    nlinarith
  have htUpper : t ≤ 2 := by
    by_contra htBad
    have htGe : 3 ≤ t := by omega
    nlinarith
  have htCases : t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases htCases with rfl | rfl | rfl | rfl
  · right
    right
    right
    dsimp [r] at htEq ⊢
    nlinarith
  · right
    right
    left
    dsimp [r] at htEq ⊢
    linarith
  · right
    left
    dsimp [r] at htEq ⊢
    linarith
  · left
    dsimp [r] at htEq ⊢
    linarith

/-- The four explicit representatives which can meet the analytic candidate
box at a clean anchor. -/
def primeFourCarryCandidates (H p : ℕ) : Finset ℤ :=
  {primeFilteredResidue H p - 2 * p,
    primeFilteredResidue H p - p,
    primeFilteredResidue H p,
    primeFilteredResidue H p + p}

/-- Every one of the four explicit states has the filtered residue. -/
theorem primeFourCarryCandidate_modEq_residue
    {H p : ℕ} {z : ℤ} (hz : z ∈ primeFourCarryCandidates H p) :
    Int.ModEq (p : ℤ) z (primeFilteredResidue H p) := by
  rw [Int.modEq_iff_dvd]
  simp only [primeFourCarryCandidates, Finset.mem_insert,
    Finset.mem_singleton] at hz
  rcases hz with hcase | hcase | hcase | hcase
  · rw [hcase]
    exact ⟨2, by ring⟩
  · rw [hcase]
    exact ⟨1, by ring⟩
  · rw [hcase]
    exact ⟨0, by ring⟩
  · rw [hcase]
    exact ⟨-1, by ring⟩

/-- **Four-to-one collapse in three steps.**  Two distinct filtered states
cannot both survive through carry depth three.  Their difference is a
nonzero multiple of `p`, hence grows by a factor `8`, while both sharp
analytic strips together have width less than `8p`. -/
theorem primeFourCarry_survivor_at_three_unique
    {H p : ℕ} (hp : p.Prime) (hH : H ≤ p - 1)
    {z w : ℤ}
    (hz : z ∈ primeFourCarryCandidates H p)
    (hw : w ∈ primeFourCarryCandidates H p)
    (hzSurv :
      |carryOrbit H (p - 1) z 3| ≤ (p + H + 3 : ℤ))
    (hwSurv :
      |carryOrbit H (p - 1) w 3| ≤ (p + H + 3 : ℤ)) :
    z = w := by
  by_contra hne
  have hzwMod : Int.ModEq (p : ℤ) z w :=
    (primeFourCarryCandidate_modEq_residue hz).trans
      (primeFourCarryCandidate_modEq_residue hw).symm
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hzwMod)
  have hkEq : w - z = (p : ℤ) * k := by simpa [mul_comm] using hk
  have hkNe : k ≠ 0 := by
    intro hkZero
    rw [hkZero, mul_zero] at hkEq
    exact hne (sub_eq_zero.mp hkEq).symm
  have horbit := carryOrbit_sub H (p - 1) z w 3
  norm_num at horbit
  have hzBounds := abs_le.mp hzSurv
  have hwBounds := abs_le.mp hwSurv
  have hpTwoZ : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hHZ : (H : ℤ) ≤ (p : ℤ) - 1 := by
    have hHLt : H < p := by omega
    have hHLtZ : (H : ℤ) < (p : ℤ) := by exact_mod_cast hHLt
    omega
  rcases lt_or_gt_of_ne hkNe with hkNeg | hkPos
  · have hkLe : k ≤ -1 := by omega
    nlinarith
  · have hkGe : 1 ≤ k := by omega
    nlinarith

/-- Literal four-state version of the denominator-filtered carry search. -/
def PrimeFourCarryKill (H p K : ℕ) : Prop :=
  ∀ z ∈ primeFourCarryCandidates H p,
    |z| ≤ (p + H : ℤ) →
    ∃ i ∈ Finset.range (K + 1),
      carryOrbit H (p - 1) z i ≤ -(p + H + i + 1 : ℤ) ∨
        (p + H + i + 1 : ℤ) ≤ carryOrbit H (p - 1) z i

instance (H p K : ℕ) : Decidable (PrimeFourCarryKill H p K) := by
  unfold PrimeFourCarryKill
  exact Finset.decidableDforallFinset

/-- Four-state launches which stay in every sharp integer strip through
depth `K`. -/
def primeFourCarryLockedThrough (H p K : ℕ) : Finset ℤ :=
  letI : DecidablePred (fun z : ℤ =>
      ∀ i ∈ Finset.range (K + 1),
        |carryOrbit H (p - 1) z i| ≤ (p + H + i : ℤ)) :=
    fun _ => Finset.decidableDforallFinset
  (primeFourCarryCandidates H p).filter fun z =>
    |z| ≤ (p + H : ℤ) ∧
      ∀ i ∈ Finset.range (K + 1),
        |carryOrbit H (p - 1) z i| ≤ (p + H + i : ℤ)

@[simp]
theorem mem_primeFourCarryLockedThrough_iff
    {H p K : ℕ} {z : ℤ} :
    z ∈ primeFourCarryLockedThrough H p K ↔
      z ∈ primeFourCarryCandidates H p ∧
        |z| ≤ (p + H : ℤ) ∧
          ∀ i ∈ Finset.range (K + 1),
            |carryOrbit H (p - 1) z i| ≤ (p + H + i : ℤ) := by
  unfold primeFourCarryLockedThrough
  simp only [Finset.mem_filter]

/-- A four-state kill says exactly that no four-state launch remains locked
through the checked depth. -/
theorem primeFourCarryKill_iff_lockedThrough_eq_empty
    {H p K : ℕ} :
    PrimeFourCarryKill H p K ↔
      primeFourCarryLockedThrough H p K = ∅ := by
  constructor
  · intro hkill
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨z, hzlocked⟩ := hnonempty
    rw [mem_primeFourCarryLockedThrough_iff] at hzlocked
    obtain ⟨hzmem, hbox, hlocked⟩ := hzlocked
    obtain ⟨i, hi, hescape⟩ := hkill z hzmem hbox
    have hbound := hlocked i hi
    rw [abs_le] at hbound
    rcases hescape with hlo | hhi <;> omega
  · intro hempty z hzmem hbox
    by_contra hnoEscape
    push Not at hnoEscape
    have hlocked : ∀ i ∈ Finset.range (K + 1),
        |carryOrbit H (p - 1) z i| ≤ (p + H + i : ℤ) := by
      intro i hi
      have hno := hnoEscape i hi
      rw [abs_le]
      constructor <;> omega
    have hzlocked : z ∈ primeFourCarryLockedThrough H p K := by
      rw [mem_primeFourCarryLockedThrough_iff]
      exact ⟨hzmem, hbox, hlocked⟩
    rw [hempty] at hzlocked
    simp at hzlocked

/-- After three steps the locked-state set has cardinality at most one. -/
theorem primeFourCarryLockedThrough_three_card_le_one
    {H p : ℕ} (hp : p.Prime) (hH : H ≤ p - 1) :
    (primeFourCarryLockedThrough H p 3).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro z w hz hw
  rw [mem_primeFourCarryLockedThrough_iff] at hz hw
  obtain ⟨hzmem, hboxz, hzlocked⟩ := hz
  obtain ⟨hwmem, hboxw, hwlocked⟩ := hw
  apply primeFourCarry_survivor_at_three_unique hp hH hzmem hwmem
  · exact hzlocked 3 (by simp)
  · exact hwlocked 3 (by simp)

/-- Once the first three carry steps have collapsed the four possible
launches to at most one, it suffices to test only that locked state.  The
depth lower bound makes the reduction back to the four-state predicate
lossless. -/
def PrimeSingleLockedCarryKill (H p K : ℕ) : Prop :=
  3 ≤ K ∧
    ∀ z ∈ primeFourCarryLockedThrough H p 3,
      ∃ i ∈ Finset.range (K + 1),
        carryOrbit H (p - 1) z i ≤ -(p + H + i + 1 : ℤ) ∨
          (p + H + i + 1 : ℤ) ≤ carryOrbit H (p - 1) z i

instance (H p K : ℕ) : Decidable (PrimeSingleLockedCarryKill H p K) := by
  unfold PrimeSingleLockedCarryKill
  exact instDecidableAnd

/-- Carry-kill certificates are monotone in the checked depth. -/
theorem primeFourCarryKill_mono
    {H p K K' : ℕ} (hKK' : K ≤ K')
    (hkill : PrimeFourCarryKill H p K) :
    PrimeFourCarryKill H p K' := by
  intro z hz hbox
  obtain ⟨i, hi, hescape⟩ := hkill z hz hbox
  refine ⟨i, ?_, hescape⟩
  rw [Finset.mem_range] at hi ⊢
  omega

/-- A four-state certificate of depth at least three kills the sole
three-step locked state, if that state exists. -/
theorem primeSingleLockedCarryKill_of_primeFourCarryKill
    {H p K : ℕ} (hK : 3 ≤ K)
    (hkill : PrimeFourCarryKill H p K) :
    PrimeSingleLockedCarryKill H p K := by
  refine ⟨hK, ?_⟩
  intro z hz
  rw [mem_primeFourCarryLockedThrough_iff] at hz
  exact hkill z hz.1 hz.2.1

/-- Testing the state locked through depth three recovers the full
four-state kill: every state omitted from the locked set already escaped in
one of those first three steps. -/
theorem primeFourCarryKill_of_primeSingleLockedCarryKill
    {H p K : ℕ}
    (hkill : PrimeSingleLockedCarryKill H p K) :
    PrimeFourCarryKill H p K := by
  obtain ⟨hK, hsingle⟩ := hkill
  intro z hzmem hbox
  by_cases hzlocked : z ∈ primeFourCarryLockedThrough H p 3
  · exact hsingle z hzlocked
  · have hnotAll :
        ¬ ∀ i ∈ Finset.range (3 + 1),
            |carryOrbit H (p - 1) z i| ≤ (p + H + i : ℤ) := by
      intro hall
      apply hzlocked
      rw [mem_primeFourCarryLockedThrough_iff]
      exact ⟨hzmem, hbox, hall⟩
    push Not at hnotAll
    obtain ⟨i, hi, hbad⟩ := hnotAll
    have hiK : i ∈ Finset.range (K + 1) := by
      rw [Finset.mem_range] at hi ⊢
      omega
    have hlarge :
        (p + H + i : ℤ) < |carryOrbit H (p - 1) z i| := by
      omega
    rcases (lt_abs.mp hlarge) with hhigh | hlow
    · exact ⟨i, hiK, Or.inr (by omega)⟩
    · exact ⟨i, hiK, Or.inl (by omega)⟩

/-- At every checked depth at least three, the four-state predicate is
equivalent to testing only the state which survived those first steps. -/
theorem primeSingleLockedCarryKill_iff_primeFourCarryKill
    {H p K : ℕ} (hK : 3 ≤ K) :
    PrimeSingleLockedCarryKill H p K ↔ PrimeFourCarryKill H p K := by
  constructor
  · exact primeFourCarryKill_of_primeSingleLockedCarryKill
  · exact primeSingleLockedCarryKill_of_primeFourCarryKill hK

/-- Four-state and residue-filtered certificates are equivalent at a clean
size-compatible anchor. -/
theorem primeFourCarryKill_iff_primeFilteredCarryKill
    {H p K : ℕ} (hp : p.Prime) (hH : H ≤ p - 1) :
    PrimeFourCarryKill H p K ↔ PrimeFilteredCarryKill H p K := by
  constructor
  · intro hfour j hj hmod
    let z : ℤ := (j : ℤ) - (p + H : ℤ)
    have hjlt : j < 2 * (p + H) + 1 := Finset.mem_range.mp hj
    have hbox : |z| ≤ (p + H : ℤ) := by
      rw [abs_le]
      dsimp [z]
      omega
    have hcases :=
      primeFiltered_candidate_eq_one_of_four hp hH hbox hmod
    have hzmem : z ∈ primeFourCarryCandidates H p := by
      rcases hcases with hcase | hcase | hcase | hcase <;>
        simp [primeFourCarryCandidates, hcase]
    exact hfour z hzmem hbox
  · intro hfiltered z hzmem hbox
    have hzBounds := abs_le.mp hbox
    have hjmem :
        (z + (p + H : ℤ)).toNat ∈
          Finset.range (2 * (p + H) + 1) := by
      rw [Finset.mem_range]
      omega
    have hcand :
        (((z + (p + H : ℤ)).toNat : ℕ) : ℤ) -
            (p + H : ℤ) = z := by
      omega
    have hzmodr :
        Int.ModEq (p : ℤ) z (primeFilteredResidue H p) := by
      exact primeFourCarryCandidate_modEq_residue hzmem
    have hrmod :
        Int.ModEq (p : ℤ) (primeFilteredResidue H p)
          (-totientBlock H (p - 1)) := by
      exact Int.mod_modEq (-totientBlock H (p - 1)) p
    have hmod :
        Int.ModEq (p : ℤ)
          ((((z + (p + H : ℤ)).toNat : ℕ) : ℤ) - (p + H : ℤ))
          (-totientBlock H (p - 1)) := by
      rw [hcand]
      exact hzmodr.trans hrmod
    obtain ⟨i, hi, hescape⟩ :=
      hfiltered (z + (p + H : ℤ)).toNat hjmem hmod
    rw [hcand] at hescape
    exact ⟨i, hi, hescape⟩

/-- Soundness of the filtered finite search, separated from the
rational-denominator argument which supplies its initial congruence. -/
theorem tail_diff_notMem_int_of_primeFilteredCarryKill
    {H p K : ℕ} (hp : p.Prime) (hkill : PrimeFilteredCarryKill H p K)
    (hfilter : ∀ z : ℤ,
      (z : ℝ) = totientTail (p - 1 + H) - totientTail (p - 1) →
      Int.ModEq (p : ℤ) z (-totientBlock H (p - 1))) :
    totientTail (p - 1 + H) - totientTail (p - 1) ∉
      Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  have hboxR : |(z : ℝ)| < (p : ℝ) + H + 1 := by
    rw [hz]
    have htail := abs_tail_diff_lt H (p - 1)
    rw [Nat.cast_sub hp.one_le] at htail
    push_cast at htail
    linarith
  have hbox : |z| ≤ (p + H : ℤ) := by
    have hboxZ : |z| < (p + H + 1 : ℤ) := by
      exact_mod_cast hboxR
    omega
  have hlohi := abs_le.mp hbox
  have hjmem :
      (z + (p + H : ℤ)).toNat ∈ Finset.range (2 * (p + H) + 1) := by
    rw [Finset.mem_range]
    omega
  have hcand :
      (((z + (p + H : ℤ)).toNat : ℕ) : ℤ) - (p + H : ℤ) = z := by
    omega
  have hfilteredCandidate :
      Int.ModEq (p : ℤ)
        ((((z + (p + H : ℤ)).toNat : ℕ) : ℤ) - (p + H : ℤ))
        (-totientBlock H (p - 1)) := by
    rw [hcand]
    exact hfilter z hz
  obtain ⟨i, hi, hescape⟩ :=
    hkill (z + (p + H : ℤ)).toNat hjmem hfilteredCandidate
  rw [hcand] at hescape
  have htrack := carryOrbit_eq_tail_diff hz i
  have hstrip := abs_tail_diff_lt H (p - 1 + i)
  rw [Nat.cast_add, Nat.cast_sub hp.one_le] at hstrip
  push_cast at hstrip
  rw [abs_lt] at hstrip
  rcases hescape with hlo | hhi
  · have hloR :
        (carryOrbit H (p - 1) z i : ℝ) ≤
          -((p : ℝ) + H + i + 1) := by
      exact_mod_cast hlo
    rw [htrack] at hloR
    linarith [hstrip.1]
  · have hhiR :
        (p : ℝ) + H + i + 1 ≤
          (carryOrbit H (p - 1) z i : ℝ) := by
      exact_mod_cast hhi
    rw [htrack] at hhiR
    linarith [hstrip.2]

/-- Pointwise completeness of the finite carry search.  If the true tail
difference is not integral, no integer launch can stay forever in the sharp
linear strip; finiteness of the initial candidate interval then supplies one
uniform escape depth.  The residue filter may only discard candidates. -/
theorem exists_primeFilteredCarryKill_of_tail_diff_notMem_int
    {H p : ℕ} (hp : p.Prime)
    (hnon :
      totientTail (p - 1 + H) - totientTail (p - 1) ∉
        Set.range ((↑) : ℤ → ℝ)) :
    ∃ K : ℕ, PrimeFilteredCarryKill H p K := by
  classical
  have hescape : ∀ j : ℕ, ∃ i : ℕ,
      carryOrbit H (p - 1) ((j : ℤ) - (p + H : ℤ)) i ≤
          -(p + H + i + 1 : ℤ) ∨
        (p + H + i + 1 : ℤ) ≤
          carryOrbit H (p - 1) ((j : ℤ) - (p + H : ℤ)) i := by
    intro j
    let d : ℤ := (j : ℤ) - (p + H : ℤ)
    have hnotBounded : ¬BoundedTailCarry H (p - 1) d := by
      intro hbounded
      exact hnon (tail_diff_mem_int_of_boundedTailCarry hbounded)
    unfold BoundedTailCarry at hnotBounded
    push Not at hnotBounded
    obtain ⟨i, hi⟩ := hnotBounded
    refine ⟨i, ?_⟩
    have hi' :
        (p + H + i : ℤ) <
          |carryOrbit H (p - 1) d i| := by
      rw [Nat.cast_sub hp.one_le] at hi
      push_cast at hi ⊢
      linarith
    rcases (lt_abs.mp hi') with hhigh | hlow
    · right
      dsimp [d] at hhigh ⊢
      omega
    · left
      dsimp [d] at hlow ⊢
      omega
  let escapeDepth (j : ℕ) : ℕ := Classical.choose (hescape j)
  let K : ℕ :=
    ∑ j ∈ Finset.range (2 * (p + H) + 1), escapeDepth j
  refine ⟨K, ?_⟩
  intro j hj _hfiltered
  have hle : escapeDepth j ≤ K := by
    exact Finset.single_le_sum
      (fun i hi => Nat.zero_le (escapeDepth i)) hj
  refine ⟨escapeDepth j, ?_, Classical.choose_spec (hescape j)⟩
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact hle

/-- Basepoint-decoupled denominator-filtered carry search.  The modulus
prime need not also determine the left endpoint: this is the form needed to
combine a large divisor of `2^H - 1` with an independently engineered short
totient window. -/
def PrimeBasepointFilteredCarryKill (H N p K : ℕ) : Prop :=
  ∀ j ∈ Finset.range (2 * (N + H + 1) + 1),
    Int.ModEq (p : ℤ) ((j : ℤ) - (N + H + 1 : ℤ))
      (-totientBlock H N) →
    ∃ i ∈ Finset.range (K + 1),
      carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i ≤
          -(N + H + i + 2 : ℤ) ∨
        (N + H + i + 2 : ℤ) ≤
          carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i

instance (H N p K : ℕ) :
    Decidable (PrimeBasepointFilteredCarryKill H N p K) := by
  unfold PrimeBasepointFilteredCarryKill
  infer_instance

/-- Prime-filtered launch indices which remain in every sharp integer strip
through depth `K` at an arbitrary basepoint.  Storing the indices rather
than the translated integer states makes membership in the finite analytic
launch interval structural. -/
def primeBasepointFilteredLockedThrough
    (H N p K : ℕ) : Finset ℕ :=
  letI : DecidablePred (fun j : ℕ =>
      ∀ i ∈ Finset.range (K + 1),
        |carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i| ≤
          (N + H + i + 1 : ℤ)) :=
    fun _ => Finset.decidableDforallFinset
  letI : DecidablePred (fun j : ℕ =>
      Int.ModEq (p : ℤ) ((j : ℤ) - (N + H + 1 : ℤ))
          (-totientBlock H N) ∧
        ∀ i ∈ Finset.range (K + 1),
          |carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i| ≤
            (N + H + i + 1 : ℤ)) :=
    fun _ => instDecidableAnd
  (Finset.range (2 * (N + H + 1) + 1)).filter fun j =>
    Int.ModEq (p : ℤ) ((j : ℤ) - (N + H + 1 : ℤ))
        (-totientBlock H N) ∧
      ∀ i ∈ Finset.range (K + 1),
        |carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i| ≤
          (N + H + i + 1 : ℤ)

@[simp]
theorem mem_primeBasepointFilteredLockedThrough_iff
    {H N p K j : ℕ} :
    j ∈ primeBasepointFilteredLockedThrough H N p K ↔
      j ∈ Finset.range (2 * (N + H + 1) + 1) ∧
        Int.ModEq (p : ℤ) ((j : ℤ) - (N + H + 1 : ℤ))
          (-totientBlock H N) ∧
        ∀ i ∈ Finset.range (K + 1),
          |carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i| ≤
            (N + H + i + 1 : ℤ) := by
  unfold primeBasepointFilteredLockedThrough
  simp only [Finset.mem_filter]

/-- The entire free-basepoint filtered launch interval has at most one
state which survives through depth three. -/
theorem primeBasepointFilteredLockedThrough_three_card_le_one
    {H N p : ℕ} (hp : p.Prime) (hNp : N < p) (hH : H ≤ p - 1) :
    (primeBasepointFilteredLockedThrough H N p 3).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro j k hj hk
  rw [mem_primeBasepointFilteredLockedThrough_iff] at hj hk
  obtain ⟨_hjRange, hjMod, hjLocked⟩ := hj
  obtain ⟨_hkRange, hkMod, hkLocked⟩ := hk
  have hstate :
      ((j : ℤ) - (N + H + 1 : ℤ)) =
        ((k : ℤ) - (N + H + 1 : ℤ)) :=
    primeBasepointFiltered_survivor_at_three_unique hp hNp hH
      hjMod hkMod
      (hjLocked 3 (by simp))
      (hkLocked 3 (by simp))
  have hcast : (j : ℤ) = (k : ℤ) := by omega
  exact_mod_cast hcast

/-- If a composite modulus already exceeds the initial analytic radius,
the filtered launch set locked through depth three has cardinality at most
one.  This is the form used by the full Mersenne quotient after the odd
denominator has been divided out. -/
theorem modulusFilteredLockedThrough_three_card_le_one
    {H N M : ℕ} (hM : 0 < M) (hwidth : N + H + 2 < M) :
    (primeBasepointFilteredLockedThrough H N M 3).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro j k hj hk
  rw [mem_primeBasepointFilteredLockedThrough_iff] at hj hk
  obtain ⟨_hjRange, hjMod, hjLocked⟩ := hj
  obtain ⟨_hkRange, hkMod, hkLocked⟩ := hk
  have hwidthZ :
      (N + H + 3 + 1 : ℤ) <
        (2 : ℤ) ^ (3 - 1) * (M : ℤ) := by
    have hwidth' : N + H + 4 < 4 * M := by omega
    exact_mod_cast hwidth'
  have hstate :
      ((j : ℤ) - (N + H + 1 : ℤ)) =
        ((k : ℤ) - (N + H + 1 : ℤ)) :=
    modulusFiltered_survivor_unique (by omega) hM
      (hjMod.trans hkMod.symm)
      (hjLocked 3 (by simp))
      (hkLocked 3 (by simp))
      hwidthZ
  have hcast : (j : ℤ) = (k : ℤ) := by omega
  exact_mod_cast hcast

/-- Once the full filtered interval has collapsed through depth three, the
basepoint certificate needs to test only its at-most-one locked index. -/
def PrimeBasepointSingleLockedCarryKill (H N p K : ℕ) : Prop :=
  3 ≤ K ∧
    ∀ j ∈ primeBasepointFilteredLockedThrough H N p 3,
      ∃ i ∈ Finset.range (K + 1),
        carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i ≤
            -(N + H + i + 2 : ℤ) ∨
          (N + H + i + 2 : ℤ) ≤
            carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i

instance (H N p K : ℕ) :
    Decidable (PrimeBasepointSingleLockedCarryKill H N p K) := by
  unfold PrimeBasepointSingleLockedCarryKill
  infer_instance

/-- Free-basepoint filtered certificates are monotone in the checked
depth. -/
theorem primeBasepointFilteredCarryKill_mono
    {H N p K K' : ℕ} (hKK' : K ≤ K')
    (hkill : PrimeBasepointFilteredCarryKill H N p K) :
    PrimeBasepointFilteredCarryKill H N p K' := by
  intro j hj hmod
  obtain ⟨i, hi, hescape⟩ := hkill j hj hmod
  refine ⟨i, ?_, hescape⟩
  rw [Finset.mem_range] at hi ⊢
  omega

/-- A full free-basepoint certificate of depth at least three kills the
sole three-step locked state, if it exists. -/
theorem primeBasepointSingleLockedCarryKill_of_filtered
    {H N p K : ℕ} (hK : 3 ≤ K)
    (hkill : PrimeBasepointFilteredCarryKill H N p K) :
    PrimeBasepointSingleLockedCarryKill H N p K := by
  refine ⟨hK, ?_⟩
  intro j hj
  rw [mem_primeBasepointFilteredLockedThrough_iff] at hj
  exact hkill j hj.1 hj.2.1

/-- Testing only the free-basepoint state locked through depth three
recovers the full filtered kill: every omitted index already escaped
during those first three steps. -/
theorem primeBasepointFilteredCarryKill_of_singleLocked
    {H N p K : ℕ}
    (hkill : PrimeBasepointSingleLockedCarryKill H N p K) :
    PrimeBasepointFilteredCarryKill H N p K := by
  obtain ⟨hK, hsingle⟩ := hkill
  intro j hjRange hjMod
  by_cases hjLocked :
      j ∈ primeBasepointFilteredLockedThrough H N p 3
  · exact hsingle j hjLocked
  · have hnotAll :
        ¬ ∀ i ∈ Finset.range (3 + 1),
            |carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i| ≤
              (N + H + i + 1 : ℤ) := by
      intro hall
      apply hjLocked
      rw [mem_primeBasepointFilteredLockedThrough_iff]
      exact ⟨hjRange, hjMod, hall⟩
    push Not at hnotAll
    obtain ⟨i, hi, hbad⟩ := hnotAll
    have hiK : i ∈ Finset.range (K + 1) := by
      rw [Finset.mem_range] at hi ⊢
      omega
    have hlarge :
        (N + H + i + 1 : ℤ) <
          |carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i| := by
      omega
    rcases (lt_abs.mp hlarge) with hhigh | hlow
    · exact ⟨i, hiK, Or.inr (by omega)⟩
    · exact ⟨i, hiK, Or.inl (by omega)⟩

/-- At every checked depth at least three, the full free-basepoint
predicate is equivalent to testing its at-most-one locked state. -/
theorem primeBasepointSingleLockedCarryKill_iff_filtered
    {H N p K : ℕ} (hK : 3 ≤ K) :
    PrimeBasepointSingleLockedCarryKill H N p K ↔
      PrimeBasepointFilteredCarryKill H N p K := by
  constructor
  · exact primeBasepointFilteredCarryKill_of_singleLocked
  · exact primeBasepointSingleLockedCarryKill_of_filtered hK

/-- The original prime-predecessor predicate is exactly the general
basepoint predicate at `N = p-1`. -/
theorem primeBasepointFilteredCarryKill_pred_iff
    {H p K : ℕ} (hp : p.Prime) :
    PrimeBasepointFilteredCarryKill H (p - 1) p K ↔
      PrimeFilteredCarryKill H p K := by
  have hp1 : 1 ≤ p := hp.one_le
  have hbase : p - 1 + H + 1 = p + H := by omega
  have hbaseZ :
      ((p - 1 : ℕ) : ℤ) + (H : ℤ) + 1 = (p : ℤ) + (H : ℤ) := by
    omega
  have hboundZ (i : ℕ) :
      ((p - 1 : ℕ) : ℤ) + (H : ℤ) + (i : ℤ) + 2 =
        (p : ℤ) + (H : ℤ) + (i : ℤ) + 1 := by
    omega
  unfold PrimeBasepointFilteredCarryKill PrimeFilteredCarryKill
  simp only [hbase, hbaseZ, hboundZ]

/-- Soundness at an arbitrary basepoint.  A filtered candidate which
escaped the sharp integer strip cannot represent the true tail difference. -/
theorem tail_diff_notMem_int_of_primeBasepointFilteredCarryKill
    {H N p K : ℕ}
    (hkill : PrimeBasepointFilteredCarryKill H N p K)
    (hfilter : ∀ z : ℤ,
      (z : ℝ) = totientTail (N + H) - totientTail N →
      Int.ModEq (p : ℤ) z (-totientBlock H N)) :
    totientTail (N + H) - totientTail N ∉
      Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  have hboxR : |(z : ℝ)| < (N + H + 2 : ℝ) := by
    rw [hz]
    exact abs_tail_diff_lt H N
  have hbox : |z| ≤ (N + H + 1 : ℤ) := by
    have hboxZ : |z| < (N + H + 2 : ℤ) := by
      exact_mod_cast hboxR
    omega
  have hlohi := abs_le.mp hbox
  have hjmem :
      (z + (N + H + 1 : ℤ)).toNat ∈
        Finset.range (2 * (N + H + 1) + 1) := by
    rw [Finset.mem_range]
    omega
  have hcand :
      (((z + (N + H + 1 : ℤ)).toNat : ℕ) : ℤ) -
          (N + H + 1 : ℤ) = z := by
    omega
  have hfilteredCandidate :
      Int.ModEq (p : ℤ)
        ((((z + (N + H + 1 : ℤ)).toNat : ℕ) : ℤ) -
          (N + H + 1 : ℤ))
        (-totientBlock H N) := by
    rw [hcand]
    exact hfilter z hz
  obtain ⟨i, hi, hescape⟩ :=
    hkill (z + (N + H + 1 : ℤ)).toNat hjmem hfilteredCandidate
  rw [hcand] at hescape
  have htrack := carryOrbit_eq_tail_diff hz i
  have hstrip := abs_tail_diff_lt H (N + i)
  push_cast at hstrip
  rw [abs_lt] at hstrip
  rcases hescape with hlo | hhi
  · have hloR :
        (carryOrbit H N z i : ℝ) ≤
          -(N + H + i + 2 : ℝ) := by
      exact_mod_cast hlo
    rw [htrack] at hloR
    linarith [hstrip.1]
  · have hhiR :
        (N + H + i + 2 : ℝ) ≤
          (carryOrbit H N z i : ℝ) := by
      exact_mod_cast hhi
    rw [htrack] at hhiR
    linarith [hstrip.2]

/-- Pointwise completeness also survives basepoint decoupling: a
nonintegral tail difference supplies a uniform finite escape depth for the
finite filtered launch interval. -/
theorem exists_primeBasepointFilteredCarryKill_of_tail_diff_notMem_int
    {H N p : ℕ}
    (hnon :
      totientTail (N + H) - totientTail N ∉
        Set.range ((↑) : ℤ → ℝ)) :
    ∃ K : ℕ, PrimeBasepointFilteredCarryKill H N p K := by
  classical
  have hescape : ∀ j : ℕ, ∃ i : ℕ,
      carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i ≤
          -(N + H + i + 2 : ℤ) ∨
        (N + H + i + 2 : ℤ) ≤
          carryOrbit H N ((j : ℤ) - (N + H + 1 : ℤ)) i := by
    intro j
    let d : ℤ := (j : ℤ) - (N + H + 1 : ℤ)
    have hnotBounded : ¬BoundedTailCarry H N d := by
      intro hbounded
      exact hnon (tail_diff_mem_int_of_boundedTailCarry hbounded)
    unfold BoundedTailCarry at hnotBounded
    push Not at hnotBounded
    obtain ⟨i, hi⟩ := hnotBounded
    refine ⟨i, ?_⟩
    have hi' :
        (N + H + i + 1 : ℤ) < |carryOrbit H N d i| := by
      linarith
    rcases (lt_abs.mp hi') with hhigh | hlow
    · right
      dsimp [d] at hhigh ⊢
      omega
    · left
      dsimp [d] at hlow ⊢
      omega
  let escapeDepth (j : ℕ) : ℕ := Classical.choose (hescape j)
  let K : ℕ :=
    ∑ j ∈ Finset.range (2 * (N + H + 1) + 1), escapeDepth j
  refine ⟨K, ?_⟩
  intro j hj _hfiltered
  have hle : escapeDepth j ≤ K := by
    exact Finset.single_le_sum
      (fun i hi => Nat.zero_le (escapeDepth i)) hj
  refine ⟨escapeDepth j, ?_, Classical.choose_spec (hescape j)⟩
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact hle

/-- The denominator filter in its algebraic core.  If `v R_N` is an integer
and a prime `p ∤ v` divides `2^H-1`, then every integral `H`-step tail
difference is congruent to the negative cleared finite block modulo `p`. -/
theorem tail_diff_modEq_neg_totientBlock_of_scaled_tail
    {H N p v : ℕ} {d u : ℤ}
    (hp : p.Prime) (hpM : p ∣ 2 ^ H - 1) (hcop : Nat.Coprime p v)
    (hd : (d : ℝ) = totientTail (N + H) - totientTail N)
    (hu : (u : ℝ) = (v : ℝ) * totientTail N) :
    Int.ModEq (p : ℤ) d (-totientBlock H N) := by
  have hpowone : 1 ≤ 2 ^ H := Nat.one_le_pow _ _ (by norm_num)
  have heq :
      ((((2 ^ H - 1 : ℕ) : ℤ) * u : ℤ)) =
        (v : ℤ) * (totientBlock H N + d) := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [Nat.cast_sub hpowone]
    push_cast
    rw [hu]
    calc
      ((2 : ℝ) ^ H - 1) * ((v : ℝ) * totientTail N) =
          (v : ℝ) * (((2 : ℝ) ^ H - 1) * totientTail N) := by ring
      _ = (v : ℝ) * ((totientBlock H N : ℝ) +
          (totientTail (N + H) - totientTail N)) := by
        rw [mersenne_mul_tail_eq_block_add_diff]
      _ = (v : ℝ) * ((totientBlock H N : ℝ) + (d : ℝ)) := by
        rw [← hd]
  have hpMZ : (p : ℤ) ∣ ((2 ^ H - 1 : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpM
  have hpProduct :
      (p : ℤ) ∣ (v : ℤ) * (totientBlock H N + d) := by
    rw [← heq]
    exact dvd_mul_of_dvd_left hpMZ u
  have hpSum : (p : ℤ) ∣ totientBlock H N + d := by
    rcases Int.Prime.dvd_mul' hp hpProduct with hpv | hsum
    · have hpvNat : p ∣ v := Int.natCast_dvd_natCast.mp hpv
      have hpgcd : p ∣ Nat.gcd p v := Nat.dvd_gcd (dvd_refl p) hpvNat
      rw [hcop.gcd_eq_one] at hpgcd
      exact (hp.not_dvd_one hpgcd).elim
    · exact hsum
  rw [Int.modEq_iff_dvd]
  have hneg :
      -totientBlock H N - d = -(totientBlock H N + d) := by ring
  rw [hneg]
  exact dvd_neg.mpr hpSum

/-- **Full Mersenne-factor filter.**  Primality is not needed when the odd
denominator factor itself has been divided from `2^H-1`.  If
`v * M = 2^H-1` and `v R_N` is integral, then every integral tail
difference lies in the single class `-Q_(H,N) mod M`.  Unlike a lone
cyclotomic prime, this modulus can retain essentially the entire
exponential Mersenne size. -/
theorem tail_diff_modEq_neg_totientBlock_of_scaled_tail_factor
    {H N v M : ℕ} {d u : ℤ}
    (hv : 0 < v) (hfactor : v * M = 2 ^ H - 1)
    (hd : (d : ℝ) = totientTail (N + H) - totientTail N)
    (hu : (u : ℝ) = (v : ℝ) * totientTail N) :
    Int.ModEq (M : ℤ) d (-totientBlock H N) := by
  have hpowone : 1 ≤ 2 ^ H := Nat.one_le_pow _ _ (by norm_num)
  have heq :
      ((((2 ^ H - 1 : ℕ) : ℤ) * u : ℤ)) =
        (v : ℤ) * (totientBlock H N + d) := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [Nat.cast_sub hpowone]
    push_cast
    rw [hu]
    calc
      ((2 : ℝ) ^ H - 1) * ((v : ℝ) * totientTail N) =
          (v : ℝ) * (((2 : ℝ) ^ H - 1) * totientTail N) := by ring
      _ = (v : ℝ) * ((totientBlock H N : ℝ) +
          (totientTail (N + H) - totientTail N)) := by
        rw [mersenne_mul_tail_eq_block_add_diff]
      _ = (v : ℝ) * ((totientBlock H N : ℝ) + (d : ℝ)) := by
        rw [← hd]
  have hfactorZ :
      (v : ℤ) * (M : ℤ) = ((2 ^ H - 1 : ℕ) : ℤ) := by
    exact_mod_cast hfactor
  have hvZ : (v : ℤ) ≠ 0 := by exact_mod_cast hv.ne'
  have hcancel :
      (M : ℤ) * u = totientBlock H N + d := by
    apply mul_left_cancel₀ hvZ
    calc
      (v : ℤ) * ((M : ℤ) * u) =
          (((2 ^ H - 1 : ℕ) : ℤ) * u) := by rw [← hfactorZ]; ring
      _ = (v : ℤ) * (totientBlock H N + d) := heq
  have hmSum : (M : ℤ) ∣ totientBlock H N + d :=
    ⟨u, hcancel.symm⟩
  rw [Int.modEq_iff_dvd]
  have hneg :
      -totientBlock H N - d = -(totientBlock H N + d) := by ring
  rw [hneg]
  exact dvd_neg.mpr hmSum

/-- **Initial candidate as a near-integer witness.**  Retaining the full
Mersenne quotient changes the geometry qualitatively.  Any filtered
integer in the initial analytic box forces the fixed scaled tail
`v R_N` to lie within `2(N+H+2)/M` of an integer.  For denominator-compatible
shifts this error tends to zero exponentially, while `v R_N` is fixed. -/
theorem scaled_tail_near_int_of_mersenne_factor_candidate
    {H N v M : ℕ} (hM : 0 < M)
    (hfactor : v * M = 2 ^ H - 1)
    {z : ℤ} (hbox : |z| ≤ (N + H + 1 : ℤ))
    (hmod : Int.ModEq (M : ℤ) z (-totientBlock H N)) :
    ∃ k : ℤ,
      |(v : ℝ) * totientTail N - (k : ℝ)| <
        (2 * (N + H + 2 : ℝ)) / (M : ℝ) := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hmod
  let k : ℤ := -t
  have hk :
      totientBlock H N + z = (M : ℤ) * k := by
    dsimp [k]
    nlinarith
  have hpowone : 1 ≤ 2 ^ H := Nat.one_le_pow _ _ (by norm_num)
  have hfactorR :
      (v : ℝ) * (M : ℝ) = (2 : ℝ) ^ H - 1 := by
    calc
      (v : ℝ) * (M : ℝ) = ((v * M : ℕ) : ℝ) := by push_cast; ring
      _ = ((2 ^ H - 1 : ℕ) : ℝ) := by rw [hfactor]
      _ = (2 : ℝ) ^ H - 1 := by
        rw [Nat.cast_sub hpowone]
        norm_num
  have hx :
      (M : ℝ) * ((v : ℝ) * totientTail N) =
        (totientBlock H N : ℝ) +
          (totientTail (N + H) - totientTail N) := by
    calc
      (M : ℝ) * ((v : ℝ) * totientTail N) =
          ((v : ℝ) * (M : ℝ)) * totientTail N := by ring
      _ = ((2 : ℝ) ^ H - 1) * totientTail N := by rw [hfactorR]
      _ = (totientBlock H N : ℝ) +
          (totientTail (N + H) - totientTail N) :=
        mersenne_mul_tail_eq_block_add_diff H N
  have hkR :
      (totientBlock H N : ℝ) + (z : ℝ) =
        (M : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  have heq :
      (M : ℝ) *
          ((v : ℝ) * totientTail N - (k : ℝ)) =
        (totientTail (N + H) - totientTail N) - (z : ℝ) := by
    rw [mul_sub, hx]
    linarith
  have htail :=
    abs_tail_diff_lt H N
  have hboxR : |(z : ℝ)| ≤ (N + H + 1 : ℝ) := by
    exact_mod_cast hbox
  have hdiffBound :
      |(totientTail (N + H) - totientTail N) - (z : ℝ)| <
        2 * (N + H + 2 : ℝ) := by
    calc
      |(totientTail (N + H) - totientTail N) - (z : ℝ)| ≤
          |totientTail (N + H) - totientTail N| + |(z : ℝ)| :=
        abs_sub _ _
      _ < (N + H + 2 : ℝ) + (N + H + 2 : ℝ) := by
        gcongr
        linarith
      _ = 2 * (N + H + 2 : ℝ) := by ring
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have heq' :
      ((v : ℝ) * totientTail N - (k : ℝ)) * (M : ℝ) =
        (totientTail (N + H) - totientTail N) - (z : ℝ) := by
    rw [mul_comm]
    exact heq
  have habsEq :
      |(v : ℝ) * totientTail N - (k : ℝ)| =
        |(totientTail (N + H) - totientTail N) - (z : ℝ)| /
          (M : ℝ) := by
    apply (eq_div_iff hMR.ne').mpr
    rw [← abs_of_pos hMR, ← abs_mul, heq']
  refine ⟨k, ?_⟩
  rw [habsEq]
  exact div_lt_div_of_pos_right hdiffBound hMR

/-- Every noninteger real has a positive uniform distance from the integer
lattice.  This reusable floor-gap form is the topological half of the
full-Mersenne initial-residue argument. -/
theorem exists_uniform_int_gap_of_notMem_int
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℤ, δ ≤ |x - (z : ℝ)| := by
  obtain ⟨g, hg⟩ := exists_floor x
  have hgle : (g : ℝ) ≤ x := (hg g).mp le_rfl
  have hglt : x < (g : ℝ) + 1 := by
    by_contra hle
    have hle' : (g : ℝ) + 1 ≤ x := not_lt.mp hle
    have h1 : ((g + 1 : ℤ) : ℝ) ≤ x := by push_cast; linarith
    have h2 : g + 1 ≤ g := (hg (g + 1)).mpr h1
    omega
  have hf0 : 0 < x - (g : ℝ) := by
    rcases eq_or_lt_of_le
        (show 0 ≤ x - (g : ℝ) by linarith) with heq | hlt
    · exfalso
      exact hx ⟨g, by linarith⟩
    · exact hlt
  have hf1 : x - (g : ℝ) < 1 := by linarith
  let δ : ℝ := min (x - (g : ℝ)) (1 - (x - (g : ℝ)))
  have hδ0 : 0 < δ := lt_min hf0 (by linarith)
  have hδlo : δ ≤ x - (g : ℝ) := min_le_left _ _
  have hδhi : δ ≤ 1 - (x - (g : ℝ)) := min_le_right _ _
  refine ⟨δ, hδ0, ?_⟩
  intro z
  by_cases hz : z ≤ g
  · have hz' : (z : ℝ) ≤ (g : ℝ) := by exact_mod_cast hz
    have hlow : δ ≤ x - (z : ℝ) := by linarith
    exact hlow.trans (le_abs_self _)
  · have hz1 : g + 1 ≤ z := Int.lt_iff_add_one_le.mp (not_le.mp hz)
    have hz' : (g : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz1
    have hup : δ ≤ (z : ℝ) - x := by linarith
    calc
      δ ≤ (z : ℝ) - x := hup
      _ ≤ |(z : ℝ) - x| := le_abs_self _
      _ = |x - (z : ℝ)| := abs_sub_comm _ _

/-- Once the full-Mersenne approximation error is below the lattice gap
of `v R_N`, the initial analytic interval contains no filtered launch at
all. -/
theorem no_mersenne_factor_candidate_of_scaled_tail_gap
    {H N v M : ℕ} (hM : 0 < M)
    (hfactor : v * M = 2 ^ H - 1)
    {δ : ℝ} (hgap : ∀ k : ℤ,
      δ ≤ |(v : ℝ) * totientTail N - (k : ℝ)|)
    (hratio :
      (2 * (N + H + 2 : ℝ)) / (M : ℝ) < δ) :
    ∀ j ∈ Finset.range (2 * (N + H + 1) + 1),
      ¬Int.ModEq (M : ℤ) ((j : ℤ) - (N + H + 1 : ℤ))
        (-totientBlock H N) := by
  intro j hj hmod
  have hjlt : j < 2 * (N + H + 1) + 1 :=
    Finset.mem_range.mp hj
  have hbox :
      |(j : ℤ) - (N + H + 1 : ℤ)| ≤ (N + H + 1 : ℤ) := by
    rw [abs_le]
    omega
  obtain ⟨k, hk⟩ :=
    scaled_tail_near_int_of_mersenne_factor_candidate
      hM hfactor hbox hmod
  exact (not_lt_of_ge (hgap k)) (hk.trans hratio)

/-- Irrationality of the full series makes every positive integral scaling
of every shifted tail nonintegral.  Otherwise the shift identity would
write the original series as an explicit rational number. -/
theorem scaled_totientTail_notMem_int_of_irrational
    (hirr : Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    {N v : ℕ} (hv : 0 < v) :
    (v : ℝ) * totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  apply hirr
  let q : ℚ :=
    ((((v * totientPrefix N : ℕ) : ℤ) + z : ℤ) : ℚ) /
      ((v * 2 ^ N : ℕ) : ℚ)
  refine ⟨q, ?_⟩
  have hshift := two_pow_mul_totient_series_eq N
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hpowR : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hdenR : (0 : ℝ) < (v : ℝ) * 2 ^ N :=
    mul_pos hvR hpowR
  dsimp [q]
  push_cast
  apply (div_eq_iff hdenR.ne').mpr
  nlinarith

/-- Clearing the dyadic part of a rational denominator leaves an integral
multiple of every sufficiently shifted tail. -/
theorem exists_int_scaled_tail_of_rat_den_eq
    (r : ℚ)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (r : ℝ))
    {c v N : ℕ} (hden : 2 ^ c * v = r.den) (hN : c ≤ N) :
    ∃ u : ℤ, (u : ℝ) = (v : ℝ) * totientTail N := by
  have hv : 0 < v := by
    by_contra hv0
    have : v = 0 := by omega
    subst v
    simp at hden
    exact r.den_pos.ne' hden.symm
  have hpowNat : 2 ^ N = 2 ^ c * 2 ^ (N - c) := by
    rw [← pow_add]
    congr 1
    omega
  have hscaled :
      (v : ℝ) * ((2 : ℝ) ^ N * (r : ℝ)) =
        ((((2 ^ (N - c) : ℕ) : ℤ) * r.num : ℤ) : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    rw [show (r.den : ℝ) = (2 : ℝ) ^ c * (v : ℝ) by
      exact_mod_cast hden.symm]
    rw [show (2 : ℝ) ^ N = (2 : ℝ) ^ c * 2 ^ (N - c) by
      exact_mod_cast hpowNat]
    field_simp
  have hshift := two_pow_mul_totient_series_eq N
  rw [hS] at hshift
  refine ⟨(2 ^ (N - c) : ℤ) * r.num -
    (v : ℤ) * (totientPrefix N : ℤ), ?_⟩
  push_cast at hscaled ⊢
  linarith [hscaled, congrArg (fun x : ℝ => (v : ℝ) * x) hshift]

/-- A multiplier whose dyadic scaling is merely divisible by the reduced
denominator already clears every sufficiently shifted rational tail.  This
is the divisor-strengthening of `exists_int_scaled_tail_of_rat_den_eq`. -/
theorem exists_int_scaled_tail_of_rat_den_dvd
    (r : ℚ)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (r : ℝ))
    {c v N : ℕ} (hden : r.den ∣ 2 ^ c * v) (hN : c ≤ N) :
    ∃ u : ℤ, (u : ℝ) = (v : ℝ) * totientTail N := by
  obtain ⟨k, hk⟩ := hden
  have hpowNat : 2 ^ N = 2 ^ c * 2 ^ (N - c) := by
    rw [← pow_add]
    congr 1
    omega
  have hscaled :
      (v : ℝ) * ((2 : ℝ) ^ N * (r : ℝ)) =
        ((((2 ^ (N - c) * k : ℕ) : ℤ) * r.num : ℤ) : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    rw [show (2 : ℝ) ^ N = (2 : ℝ) ^ c * 2 ^ (N - c) by
      exact_mod_cast hpowNat]
    have hkR : (2 : ℝ) ^ c * (v : ℝ) = (r.den : ℝ) * (k : ℝ) := by
      exact_mod_cast hk
    calc
      (v : ℝ) *
          ((2 : ℝ) ^ c * 2 ^ (N - c) *
            ((r.num : ℝ) / (r.den : ℝ))) =
          (2 : ℝ) ^ (N - c) *
            (((2 : ℝ) ^ c * (v : ℝ)) *
              ((r.num : ℝ) / (r.den : ℝ))) := by ring
      _ = (2 : ℝ) ^ (N - c) *
            (((r.den : ℝ) * (k : ℝ)) *
              ((r.num : ℝ) / (r.den : ℝ))) := by rw [hkR]
      _ = (2 : ℝ) ^ (N - c) * (k : ℝ) * (r.num : ℝ) := by
        field_simp
  have hshift := two_pow_mul_totient_series_eq N
  rw [hS] at hshift
  refine ⟨((2 ^ (N - c) * k : ℕ) : ℤ) * r.num -
    (v : ℤ) * (totientPrefix N : ℤ), ?_⟩
  push_cast at hscaled ⊢
  linarith [hscaled, congrArg (fun x : ℝ => (v : ℝ) * x) hshift]

/-! ## Cofinal clean composite-index cyclotomic anchors -/

/-- The unsigned binary cyclotomic layer `|Φ_n(2)|`. -/
noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs

/-- Every binary cyclotomic layer divides the corresponding Mersenne
number. -/
theorem binaryCyclotomicLayer_dvd_mersenneLayer (n : ℕ) :
    binaryCyclotomicLayer n ∣ mersenneLayer n := by
  have hpoly := Polynomial.cyclotomic.dvd_X_pow_sub_one n ℤ
  have heval := map_dvd (Polynomial.evalRingHom (R := ℤ) 2) hpoly
  have hpow : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hint :
      (Polynomial.cyclotomic n ℤ).eval (2 : ℤ) ∣
        (mersenneLayer n : ℤ) := by
    simpa [mersenneLayer, Nat.cast_sub hpow] using heval
  simpa [binaryCyclotomicLayer] using Int.natAbs_dvd_natAbs.mpr hint

/-- A prime divisor of `Φ_n(2)` supplies the characteristic-free order
decomposition `n = p^a * ord_p(2)`.  The decomposition remains valid in the
exceptional characteristic case; cleanliness below is exactly what forces
`a = 0`. -/
theorem binaryCyclotomicLayer_prime_order_decomposition
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpdvd : p ∣ binaryCyclotomicLayer n) :
    ∃ a : ℕ, n = p ^ a * orderOf ((2 : ℕ) : ZMod p) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hpdvdInt :
      (p : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval (2 : ℤ) := by
    exact Int.dvd_natAbs.mp
      (Int.natCast_dvd_natCast.mpr (by
        simpa [binaryCyclotomicLayer] using hpdvd))
  have hroot :
      (Polynomial.cyclotomic n (ZMod p)).IsRoot ((2 : ℕ) : ZMod p) := by
    have hcast :
        (((Polynomial.cyclotomic n ℤ).eval (2 : ℤ) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpdvdInt
    have hcomm :
        (Polynomial.cyclotomic n (ZMod p)).eval (((2 : ℤ) : ZMod p))
          =
        (((Polynomial.cyclotomic n ℤ).eval (2 : ℤ) : ℤ) : ZMod p) := by
      rw [← Polynomial.map_cyclotomic_int n (ZMod p), Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply (Int.castRingHom (ZMod p)) _
    show (Polynomial.cyclotomic n (ZMod p)).eval ((2 : ℕ) : ZMod p) = 0
    norm_num at hcomm ⊢
    rw [hcomm, hcast]
  exact orderOf_isRoot_cyclotomic_zmod_pow_mul hp n hn _ hroot

/-- The residue of `2` is nonzero at every prime divisor of a positive
binary cyclotomic layer. -/
theorem two_ne_zero_of_prime_dvd_binaryCyclotomicLayer
    {n p : ℕ} (hn : 1 < n) (hp : p.Prime)
    (hpdvd : p ∣ binaryCyclotomicLayer n) :
    ((2 : ℕ) : ZMod p) ≠ 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hpdvdInt :
      (p : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval (2 : ℤ) := by
    exact Int.dvd_natAbs.mp
      (Int.natCast_dvd_natCast.mpr (by
        simpa [binaryCyclotomicLayer] using hpdvd))
  have hroot :
      (Polynomial.cyclotomic n (ZMod p)).IsRoot ((2 : ℕ) : ZMod p) := by
    have hcast :
        (((Polynomial.cyclotomic n ℤ).eval (2 : ℤ) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpdvdInt
    have hcomm :
        (Polynomial.cyclotomic n (ZMod p)).eval (((2 : ℤ) : ZMod p))
          =
        (((Polynomial.cyclotomic n ℤ).eval (2 : ℤ) : ℤ) : ZMod p) := by
      rw [← Polynomial.map_cyclotomic_int n (ZMod p), Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply (Int.castRingHom (ZMod p)) _
    show (Polynomial.cyclotomic n (ZMod p)).eval ((2 : ℕ) : ZMod p) = 0
    norm_num at hcomm ⊢
    rw [hcomm, hcast]
  intro hzero
  have hcoeff : (Polynomial.cyclotomic n (ZMod p)).coeff 0 = 1 :=
    Polynomial.cyclotomic_coeff_zero (ZMod p) hn
  have hcoeffZero :
      (Polynomial.cyclotomic n (ZMod p)).coeff 0 = 0 := by
    have hrootZero := hroot
    rw [hzero] at hrootZero
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa [Polynomial.IsRoot] using hrootZero
  rw [hcoeff] at hcoeffZero
  exact one_ne_zero hcoeffZero

/-- **Unconditional clean composite-ray producer.**  For every positive
period `h` and every threshold, a prime-index multiplier `q` and a prime
factor `p` of `Φ_(h*q)(2)` can be chosen so that the factor is clean,
`ord_p(2) = h*q`, and hence `h*q ∣ p-1`.

The characteristic-prime case is eliminated directly from the exact
cyclotomic order decomposition.  Choosing `q > 2^h` rules out `p = q`;
choosing `q > h` rules out every `p ∣ h`. -/
theorem exists_clean_binaryCyclotomicAnchor
    (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ binaryCyclotomicLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 := by
  let B : ℕ := max (max h N₀) (2 ^ h)
  obtain ⟨q, hqB, hq⟩ := Nat.exists_infinite_primes (B + 1)
  have hqh : h < q := by
    dsimp [B] at hqB
    omega
  have hqN : N₀ < q := by
    dsimp [B] at hqB
    omega
  have hqpow : 2 ^ h < q := by
    dsimp [B] at hqB
    omega
  have hHtwo : 2 ≤ h * q := by
    have hqTwo : 2 ≤ q := hq.two_le
    nlinarith
  obtain ⟨p, hp, hpEval⟩ :=
    exists_prime_dvd_cyclotomic_eval
      (b := 2) (n := h * q) (by norm_num) hHtwo
  have hpLayer : p ∣ binaryCyclotomicLayer (h * q) := by
    unfold binaryCyclotomicLayer
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hpEval)
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨a, hdecomp⟩ :=
    binaryCyclotomicLayer_prime_order_decomposition
      (n := h * q) (p := p) (by positivity) hp hpLayer
  let m : ℕ := orderOf ((2 : ℕ) : ZMod p)
  have hdecomp' : h * q = p ^ a * m := by
    simpa [m] using hdecomp
  have htwoNonzero :
      ((2 : ℕ) : ZMod p) ≠ 0 :=
    two_ne_zero_of_prime_dvd_binaryCyclotomicLayer
      (n := h * q) (p := p) hHtwo hp hpLayer
  have hmDvd : m ∣ p - 1 := by
    simpa [m] using ZMod.orderOf_dvd_card_sub_one htwoNonzero
  have hpNotH : ¬p ∣ h * q := by
    intro hpH
    rcases hp.dvd_mul.mp hpH with hph | hpq
    · have hpLeH : p ≤ h := Nat.le_of_dvd hh hph
      have hpNeQ : p ≠ q := by omega
      have hqProd : q ∣ p ^ a * m := by
        rw [← hdecomp']
        exact ⟨h, by ring⟩
      have hqM : q ∣ m := by
        rcases hq.dvd_mul.mp hqProd with hqPow | hqm
        · have hqp : q = p :=
            Nat.prime_eq_prime_of_dvd_pow hq hp hqPow
          exact (hpNeQ hqp.symm).elim
        · exact hqm
      have hqPred : q ∣ p - 1 := hqM.trans hmDvd
      have hpTwo : 2 ≤ p := hp.two_le
      have hpredPos : 0 < p - 1 := by omega
      have hqLe : q ≤ p - 1 := Nat.le_of_dvd hpredPos hqPred
      omega
    · have hpEqQ : p = q := by
        rcases (Nat.dvd_prime hq).mp hpq with hpOne | hpq'
        · exact (hp.ne_one hpOne).elim
        · exact hpq'
      subst p
      rcases Nat.eq_zero_or_pos a with haZero | haPos
      · subst a
        simp only [pow_zero, one_mul] at hdecomp'
        have hmLe : m ≤ q - 1 := Nat.le_of_dvd (by omega) hmDvd
        have hqLeH : q ≤ h * q := by
          simpa using Nat.mul_le_mul_right q (show 1 ≤ h by omega)
        omega
      · by_cases haOne : a = 1
        · subst a
          simp only [pow_one] at hdecomp'
          have hmEq : m = h := by
            have hEq : q * h = q * m := by
              simpa [Nat.mul_comm] using hdecomp'
            exact (Nat.mul_left_cancel hq.pos hEq).symm
          have hpowZ : (((2 : ℕ) : ZMod q) ^ h) = 1 := by
            rw [← hmEq]
            exact pow_orderOf_eq_one _
          have hpowOne : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by norm_num)
          have hcastPow : ((2 ^ h : ℕ) : ZMod q) = 1 := by
            simpa using hpowZ
          have hcast :
              ((2 ^ h - 1 : ℕ) : ZMod q) = 0 := by
            rw [Nat.cast_sub hpowOne, hcastPow, Nat.cast_one, sub_self]
          have hqDvd : q ∣ 2 ^ h - 1 :=
            (ZMod.natCast_eq_zero_iff (2 ^ h - 1) q).mp hcast
          have hsubPos : 0 < 2 ^ h - 1 := by
            have : 1 < 2 ^ h := Nat.one_lt_pow hh.ne' (by norm_num)
            omega
          have hsubLt : 2 ^ h - 1 < q := by omega
          exact (Nat.not_dvd_of_pos_of_lt hsubPos hsubLt) hqDvd
        · have haTwo : 2 ≤ a := by omega
          have hqSqPow : q ^ 2 ∣ q ^ a := pow_dvd_pow q haTwo
          have hqSqH : q ^ 2 ∣ h * q := by
            rw [hdecomp']
            exact dvd_mul_of_dvd_left hqSqPow m
          obtain ⟨k, hk⟩ := hqSqH
          have hhFactor : h = q * k := by
            have hEq : h * q = (q * k) * q := by
              simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hk
            exact Nat.mul_right_cancel hq.pos hEq
          have hqDvdH : q ∣ h := ⟨k, hhFactor⟩
          have hqLeH : q ≤ h := Nat.le_of_dvd hh hqDvdH
          omega
  have hcop : Nat.Coprime p (h * q) :=
    hp.coprime_iff_not_dvd.mpr hpNotH
  have haZero : a = 0 := by
    by_contra ha
    have haPos : 0 < a := Nat.pos_of_ne_zero ha
    apply hpNotH
    rw [hdecomp']
    exact dvd_mul_of_dvd_left (dvd_pow_self p haPos.ne') m
  have hHord : h * q = m := by
    simpa [haZero] using hdecomp'
  have hperiodDvd : h * q ∣ p - 1 := by
    rw [hHord]
    exact hmDvd
  have hpTwo : 2 ≤ p := hp.two_le
  have hHle : h * q ≤ p - 1 :=
    Nat.le_of_dvd (by omega) hperiodDvd
  have hN : N₀ ≤ p - 1 := by
    have hqLeH : q ≤ h * q := by
      nlinarith
    omega
  exact ⟨q, p, hq, hp, hcop, hpLayer, hperiodDvd, hN⟩

/-- Past the explicit exceptional range, every prime divisor of the binary
cyclotomic layer is clean and supplies exact order `h*q`.  The two bounds have
different roles: `q > h` excludes characteristics dividing the fixed ray
multiplier, while `q > 2^h` excludes the moving characteristic `p = q`. -/
theorem prime_dvd_binaryCyclotomicLayer_clean_order
    {h q p : ℕ} (hh : 0 < h) (hq : q.Prime)
    (hqh : h < q) (hqpow : 2 ^ h < q)
    (hp : p.Prime) (hpLayer : p ∣ binaryCyclotomicLayer (h * q)) :
    Nat.Coprime p (h * q) ∧ h * q ∣ p - 1 := by
  have hHtwo : 2 ≤ h * q := by
    have hqTwo : 2 ≤ q := hq.two_le
    nlinarith
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨a, hdecomp⟩ :=
    binaryCyclotomicLayer_prime_order_decomposition
      (n := h * q) (p := p) (by positivity) hp hpLayer
  let o : ℕ := orderOf ((2 : ℕ) : ZMod p)
  have hdecomp' : h * q = p ^ a * o := by
    simpa [o] using hdecomp
  have htwoNonzero : ((2 : ℕ) : ZMod p) ≠ 0 :=
    two_ne_zero_of_prime_dvd_binaryCyclotomicLayer
      (n := h * q) (p := p) hHtwo hp hpLayer
  have hoDvd : o ∣ p - 1 := by
    simpa [o] using ZMod.orderOf_dvd_card_sub_one htwoNonzero
  have hpNotIndex : ¬p ∣ h * q := by
    intro hpIndex
    rcases hp.dvd_mul.mp hpIndex with hph | hpq
    · have hpLeH : p ≤ h := Nat.le_of_dvd hh hph
      have hpNeQ : p ≠ q := by omega
      have hqProd : q ∣ p ^ a * o := by
        rw [← hdecomp']
        exact ⟨h, by ring⟩
      have hqO : q ∣ o := by
        rcases hq.dvd_mul.mp hqProd with hqPow | hqo
        · have hqp : q = p := Nat.prime_eq_prime_of_dvd_pow hq hp hqPow
          exact (hpNeQ hqp.symm).elim
        · exact hqo
      have hqPred : q ∣ p - 1 := hqO.trans hoDvd
      have hpTwo : 2 ≤ p := hp.two_le
      have hpredPos : 0 < p - 1 := by omega
      have hqLe : q ≤ p - 1 := Nat.le_of_dvd hpredPos hqPred
      omega
    · have hpEqQ : p = q := by
        rcases (Nat.dvd_prime hq).mp hpq with hpOne | hpq'
        · exact (hp.ne_one hpOne).elim
        · exact hpq'
      subst p
      rcases Nat.eq_zero_or_pos a with haZero | haPos
      · subst a
        simp only [pow_zero, one_mul] at hdecomp'
        have hoLe : o ≤ q - 1 := Nat.le_of_dvd (by omega) hoDvd
        have hqLeH : q ≤ h * q := by
          simpa using Nat.mul_le_mul_right q (show 1 ≤ h by omega)
        omega
      · by_cases haOne : a = 1
        · subst a
          simp only [pow_one] at hdecomp'
          have hoEq : o = h := by
            have hEq : q * h = q * o := by
              simpa [Nat.mul_comm] using hdecomp'
            exact (Nat.mul_left_cancel hq.pos hEq).symm
          have hpowZ : (((2 : ℕ) : ZMod q) ^ h) = 1 := by
            rw [← hoEq]
            exact pow_orderOf_eq_one _
          have hpowOne : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by norm_num)
          have hcastPow : ((2 ^ h : ℕ) : ZMod q) = 1 := by
            simpa using hpowZ
          have hcast : ((2 ^ h - 1 : ℕ) : ZMod q) = 0 := by
            rw [Nat.cast_sub hpowOne, hcastPow, Nat.cast_one, sub_self]
          have hqDvd : q ∣ 2 ^ h - 1 :=
            (ZMod.natCast_eq_zero_iff (2 ^ h - 1) q).mp hcast
          have hsubPos : 0 < 2 ^ h - 1 := by
            have : 1 < 2 ^ h := Nat.one_lt_pow hh.ne' (by norm_num)
            omega
          have hsubLt : 2 ^ h - 1 < q := by omega
          exact (Nat.not_dvd_of_pos_of_lt hsubPos hsubLt) hqDvd
        · have haTwo : 2 ≤ a := by omega
          have hqSqPow : q ^ 2 ∣ q ^ a := pow_dvd_pow q haTwo
          have hqSqH : q ^ 2 ∣ h * q := by
            rw [hdecomp']
            exact dvd_mul_of_dvd_left hqSqPow o
          obtain ⟨k, hk⟩ := hqSqH
          have hhFactor : h = q * k := by
            have hEq : h * q = (q * k) * q := by
              simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hk
            exact Nat.mul_right_cancel hq.pos hEq
          have hqDvdH : q ∣ h := ⟨k, hhFactor⟩
          have hqLeH : q ≤ h := Nat.le_of_dvd hh hqDvdH
          omega
  have hcop : Nat.Coprime p (h * q) := hp.coprime_iff_not_dvd.mpr hpNotIndex
  have haZero : a = 0 := by
    by_contra ha
    have haPos : 0 < a := Nat.pos_of_ne_zero ha
    apply hpNotIndex
    rw [hdecomp']
    exact dvd_mul_of_dvd_left (dvd_pow_self p haPos.ne') o
  have hHord : h * q = o := by simpa [haZero] using hdecomp'
  refine ⟨hcop, ?_⟩
  rw [hHord]
  exact hoDvd

/-- The actual binary cyclotomic layers are eventually nontrivial and clean
on every positive prime ray. -/
theorem binaryCyclotomicLayer_layerSupply (h : ℕ) (hh : 0 < h) :
    PrimeRayLayerSupply binaryCyclotomicLayer h := by
  refine ⟨max (h + 1) (2 ^ h + 1), ?_⟩
  intro q hq hqLower
  have hqh : h < q := by
    have : h + 1 ≤ q := le_trans (le_max_left _ _) hqLower
    omega
  have hqpow : 2 ^ h < q := by
    have : 2 ^ h + 1 ≤ q := le_trans (le_max_right _ _) hqLower
    omega
  have hHtwo : 2 ≤ h * q := by
    have hqTwo : 2 ≤ q := hq.two_le
    nlinarith
  have hlarge : 1 < binaryCyclotomicLayer (h * q) := by
    simpa [binaryCyclotomicLayer] using
      (Polynomial.sub_one_lt_natAbs_cyclotomic_eval
        (n := h * q) (q := 2) hHtwo (by norm_num))
  refine ⟨hlarge, ?_⟩
  by_contra hcop
  obtain ⟨p, hp, hpLayer, hpIndex⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  exact (hp.coprime_iff_not_dvd.mp
    (prime_dvd_binaryCyclotomicLayer_clean_order
      hh hq hqh hqpow hp hpLayer).1) hpIndex

/-- The actual binary cyclotomic layer has degree-one order witnesses beyond
the same explicit exceptional range. -/
theorem binaryCyclotomicLayer_eventualOrderConsumer (h : ℕ) (hh : 0 < h) :
    EventualBoundedDegreeOrderConsumer binaryCyclotomicLayer h 1 := by
  refine ⟨max (h + 1) (2 ^ h + 1), ?_⟩
  intro q p hq hqLower hp hpLayer
  have hqh : h < q := by
    have : h + 1 ≤ q := le_trans (le_max_left _ _) hqLower
    omega
  have hqpow : 2 ^ h < q := by
    have : 2 ^ h + 1 ≤ q := le_trans (le_max_right _ _) hqLower
    omega
  refine ⟨1, by omega, by omega, ?_⟩
  simpa using (prime_dvd_binaryCyclotomicLayer_clean_order
    hh hq hqh hqpow hp hpLayer).2

/-- Unbounded prime support is unconditional for every positive binary
cyclotomic prime ray.  This remains an arithmetic support statement, not a
carry/phase escape theorem and not an irrationality theorem for Erdős #249. -/
theorem binaryCyclotomicLayer_unboundedPrimeDivisorSupply
    (h : ℕ) (hh : 0 < h) :
    UnboundedPrimeDivisorSupply binaryCyclotomicLayer h :=
  unboundedPrimeDivisorSupply_of_eventualOrderConsumer hh
    (binaryCyclotomicLayer_layerSupply h hh)
    (binaryCyclotomicLayer_eventualOrderConsumer h hh)

/-- The original global order-consumer predicate is genuinely too strong for
composite cyclotomic rays: at `h = 2`, `q = 3`, the layer is
`Φ₆(2) = 3`, whose characteristic prime cannot realise order six. -/
theorem binaryCyclotomicLayer_not_globalOrderConsumer :
    ¬ BoundedDegreeOrderConsumer binaryCyclotomicLayer 2 1 := by
  intro horder
  have hthree : 3 ∣ binaryCyclotomicLayer (2 * 3) := by
    norm_num [binaryCyclotomicLayer, Polynomial.cyclotomic_six]
  obtain ⟨k, hk1, hkUpper, hkdiv⟩ :=
    horder 3 3 (by norm_num) (by norm_num) hthree
  have hk : k = 1 := by omega
  subst k
  norm_num at hkdiv

/-- **Exact obstruction to a support-only proof of Erdős #249.**  If the
totient series were rational, its eventual integral tail-period law would
hold on some positive period ray.  The actual binary cyclotomic layers still
have unbounded prime divisors on that same ray.  Thus unbounded prime support
is compatible with the precise period lock supplied by hypothetical
rationality; an additional carry or phase-escape bridge is indispensable. -/
theorem
    exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
    (hrat : ¬ Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧
      UnboundedPrimeDivisorSupply binaryCyclotomicLayer h ∧
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        totientTail (N + h) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨h, hh, hperiod⟩ := eventual_period_of_not_irrational hrat
  exact ⟨h, hh,
    binaryCyclotomicLayer_unboundedPrimeDivisorSupply h hh, hperiod⟩

/-- An eventual `h`-period tail-integrality law also holds for every
positive or zero multiple `h * k`, by telescoping `k` adjacent differences. -/
lemma tail_diff_int_of_period_mul
    {h N₀ : ℕ}
    (hint :
      ∀ N, N₀ ≤ N →
        totientTail (N + h) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ)) :
    ∀ k N, N₀ ≤ N →
      totientTail (N + h * k) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := by
  intro k
  induction k with
  | zero =>
      intro N hN
      exact ⟨0, by simp⟩
  | succ k ih =>
      intro N hN
      obtain ⟨a, ha⟩ := ih N hN
      obtain ⟨b, hb⟩ := hint (N + h * k) (by omega)
      refine ⟨a + b, ?_⟩
      push_cast
      rw [show N + h * Nat.succ k = (N + h * k) + h by
        rw [Nat.mul_succ]
        omega]
      linarith

/-- Cofinal clean cyclotomic provenance, without any certificate field. -/
def CleanCyclotomicAnchorSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1

/-- The actual binary cyclotomic layers have unconditional cofinal clean
anchors. -/
theorem cleanCyclotomicAnchorSupply_binaryCyclotomicLayer :
    CleanCyclotomicAnchorSupply binaryCyclotomicLayer :=
  fun h hh N₀ => exists_clean_binaryCyclotomicAnchor h N₀ hh

/-- The exact denominator-filtered residual.  At a cofinal clean cyclotomic
anchor, only the carry candidates in one forced residue class modulo `p`
must be expelled.  Since `H ∣ p-1`, the initial interval contains at most
four such candidates. -/
def CyclotomicPrimeFilteredCarryKillSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p K : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      p ∣ mersenneLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 ∧
      PrimeFilteredCarryKill (h * q) p K

/-- The same cofinal residual with the carry search literally restricted to
the four possible representatives. -/
def CyclotomicPrimeFourCarryKillSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p K : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      p ∣ mersenneLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 ∧
      PrimeFourCarryKill (h * q) p K

/-- The exact cofinal residual after the four-to-one collapse: each clean
anchor asks only whether its at-most-one state locked through depth three
eventually leaves the sharp strip. -/
def CyclotomicPrimeSingleLockedCarryKillSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p K : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      p ∣ mersenneLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 ∧
      PrimeSingleLockedCarryKill (h * q) p K

/-- Basepoint-decoupled prime-filter supply.  A multiple `H` of the
denominator period supplies the Mersenne divisor, while the left endpoint
`N` is free to carry an independently constructed short arithmetic window.
The size condition `H ≤ p-1` retains the large-modulus geometry of clean
cyclotomic anchors. -/
def PrimeBasepointFilteredCarryKillSupply : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ H N p K : ℕ,
      0 < H ∧
      h ∣ H ∧
      N₀ ≤ N ∧
      N < p ∧
      p.Prime ∧
      p ∣ mersenneLayer H ∧
      H ≤ p - 1 ∧
      PrimeBasepointFilteredCarryKill H N p K

/-- Exact one-locked-state version of the basepoint-decoupled supply. -/
def PrimeBasepointSingleLockedCarryKillSupply : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ H N p K : ℕ,
      0 < H ∧
      h ∣ H ∧
      N₀ ≤ N ∧
      N < p ∧
      p.Prime ∧
      p ∣ mersenneLayer H ∧
      H ≤ p - 1 ∧
      PrimeBasepointSingleLockedCarryKill H N p K

/-- The free-basepoint one-state supply and full filtered supply are
exactly equivalent. -/
theorem primeBasepointSingleLockedCarryKillSupply_iff_filtered :
    PrimeBasepointSingleLockedCarryKillSupply ↔
      PrimeBasepointFilteredCarryKillSupply := by
  constructor
  · intro hsupply h hh N₀
    obtain ⟨H, N, p, K, hHpos, hhH, hNremote, hNp, hp, hpM, hHle,
        hsingle⟩ :=
      hsupply h hh N₀
    exact ⟨H, N, p, K, hHpos, hhH, hNremote, hNp, hp, hpM, hHle,
      primeBasepointFilteredCarryKill_of_singleLocked hsingle⟩
  · intro hsupply h hh N₀
    obtain ⟨H, N, p, K, hHpos, hhH, hNremote, hNp, hp, hpM, hHle,
        hfiltered⟩ :=
      hsupply h hh N₀
    let K' := max 3 K
    have hK' : 3 ≤ K' := le_max_left 3 K
    have hmono : PrimeBasepointFilteredCarryKill H N p K' :=
      primeBasepointFilteredCarryKill_mono (le_max_right 3 K) hfiltered
    have hsingle : PrimeBasepointSingleLockedCarryKill H N p K' :=
      primeBasepointSingleLockedCarryKill_of_filtered hK' hmono
    exact ⟨H, N, p, K', hHpos, hhH, hNremote, hNp, hp, hpM, hHle,
      hsingle⟩

/-- Cofinal four-state and residue-filtered supplies are exactly equivalent;
the order divisibility field supplies the required bound `H ≤ p-1`. -/
theorem cyclotomicPrimeFourCarryKillSupply_iff_filtered
    {C : ℕ → ℕ} :
    CyclotomicPrimeFourCarryKillSupply C ↔
      CyclotomicPrimeFilteredCarryKillSupply C := by
  constructor
  · intro hsupply h hh N₀
    obtain ⟨q, p, K, hq, hp, hcop, hpC, hpM, hord, hN, hfour⟩ :=
      hsupply h hh N₀
    have hHle : h * q ≤ p - 1 :=
      Nat.le_of_dvd (by have := hp.two_le; omega) hord
    have hfiltered : PrimeFilteredCarryKill (h * q) p K :=
      (primeFourCarryKill_iff_primeFilteredCarryKill hp hHle).mp hfour
    exact ⟨q, p, K, hq, hp, hcop, hpC, hpM, hord, hN, hfiltered⟩
  · intro hsupply h hh N₀
    obtain ⟨q, p, K, hq, hp, hcop, hpC, hpM, hord, hN, hfiltered⟩ :=
      hsupply h hh N₀
    have hHle : h * q ≤ p - 1 :=
      Nat.le_of_dvd (by have := hp.two_le; omega) hord
    have hfour : PrimeFourCarryKill (h * q) p K :=
      (primeFourCarryKill_iff_primeFilteredCarryKill hp hHle).mpr hfiltered
    exact ⟨q, p, K, hq, hp, hcop, hpC, hpM, hord, hN, hfour⟩

/-- Cofinal one-state and four-state supplies are exactly equivalent.  In
the reverse direction a certificate is harmlessly extended to depth three
before restricting it to the locked state. -/
theorem cyclotomicPrimeSingleLockedCarryKillSupply_iff_four
    {C : ℕ → ℕ} :
    CyclotomicPrimeSingleLockedCarryKillSupply C ↔
      CyclotomicPrimeFourCarryKillSupply C := by
  constructor
  · intro hsupply h hh N₀
    obtain ⟨q, p, K, hq, hp, hcop, hpC, hpM, hord, hN, hsingle⟩ :=
      hsupply h hh N₀
    exact ⟨q, p, K, hq, hp, hcop, hpC, hpM, hord, hN,
      primeFourCarryKill_of_primeSingleLockedCarryKill hsingle⟩
  · intro hsupply h hh N₀
    obtain ⟨q, p, K, hq, hp, hcop, hpC, hpM, hord, hN, hfour⟩ :=
      hsupply h hh N₀
    let K' := max 3 K
    have hK' : 3 ≤ K' := le_max_left 3 K
    have hmono : PrimeFourCarryKill (h * q) p K' :=
      primeFourCarryKill_mono (le_max_right 3 K) hfour
    have hsingle : PrimeSingleLockedCarryKill (h * q) p K' :=
      primeSingleLockedCarryKill_of_primeFourCarryKill hK' hmono
    exact ⟨q, p, K', hq, hp, hcop, hpC, hpM, hord, hN, hsingle⟩

/-- Every cyclotomic filtered supply furnishes the more flexible
basepoint-decoupled supply by taking its original endpoint `N = p-1`. -/
theorem primeBasepointFilteredCarryKillSupply_of_cyclotomicFiltered
    {C : ℕ → ℕ}
    (hsupply : CyclotomicPrimeFilteredCarryKillSupply C) :
    PrimeBasepointFilteredCarryKillSupply := by
  intro h hh N₀
  obtain ⟨q, p, K, hq, hp, hcop, hpC, hpM, hord, hN, hkill⟩ :=
    hsupply h hh N₀
  have hHpos : 0 < h * q := Nat.mul_pos hh hq.pos
  have hbaseKill :
      PrimeBasepointFilteredCarryKill (h * q) (p - 1) p K :=
    (primeBasepointFilteredCarryKill_pred_iff hp).mpr hkill
  exact ⟨h * q, p - 1, p, K, hHpos, dvd_mul_right h q, hN,
    Nat.sub_lt hp.pos (by norm_num), hp, hpM,
    Nat.le_of_dvd (by have := hp.two_le; omega) hord, hbaseKill⟩

/-- **Basepoint-decoupled conditional closure of Erdős #249.**  Rationality
clears the dyadic denominator at the independently supplied endpoint `N`;
the odd denominator is absorbed because its Euler period divides `H`, and
the fresh prime divisor of `2^H-1` forces the filtered block congruence. -/
theorem irrational_totient_series_of_primeBasepointFilteredCarryKillSupply
    (hsupply : PrimeBasepointFilteredCarryKillSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  have hmem :
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ∈
        Set.range ((↑) : ℚ → ℝ) := by
    by_contra hnot
    exact hrat hnot
  obtain ⟨r, hr⟩ := hmem
  let v : ℕ := ordCompl[2] r.den
  let c : ℕ := r.den.factorization 2
  let h : ℕ := Nat.totient v
  have hv : 0 < v := by
    dsimp [v]
    exact Nat.ordCompl_pos 2 r.den_pos.ne'
  have hcopTwo : Nat.Coprime 2 v := by
    dsimp [v]
    exact Nat.coprime_ordCompl Nat.prime_two r.den_pos.ne'
  have hh : 0 < h := by
    dsimp [h]
    exact Nat.totient_pos.mpr hv
  obtain ⟨H, N, p, K, hHpos, hhH, hNremote, hNp, hp, hpM,
      hHle, hkill⟩ :=
    hsupply h hh (max c v)
  have hcN : c ≤ N := (le_max_left c v).trans hNremote
  have hvN : v ≤ N := (le_max_right c v).trans hNremote
  have hpNotDvdV : ¬p ∣ v := by
    intro hpdvd
    have hpLeV : p ≤ v := Nat.le_of_dvd hv hpdvd
    omega
  have hcopPV : Nat.Coprime p v :=
    hp.coprime_iff_not_dvd.mpr hpNotDvdV
  have hden : 2 ^ c * v = r.den := by
    simpa [c, v] using Nat.ordProj_mul_ordCompl_eq_self r.den 2
  have heuler : (2 : ℕ) ^ h ≡ 1 [MOD v] := by
    dsimp [h]
    exact Nat.ModEq.pow_totient hcopTwo
  have hvMbase : v ∣ 2 ^ h - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp heuler.symm
  have hbaseDvd : 2 ^ h - 1 ∣ 2 ^ H - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one 2 hhH
  have hvM : v ∣ 2 ^ H - 1 := hvMbase.trans hbaseDvd
  have h2c : (2 : ℕ) ^ c ∣ 2 ^ N := pow_dvd_pow 2 hcN
  have hcopPow : Nat.Coprime (2 ^ c) v :=
    Nat.Coprime.pow_left _ hcopTwo
  have hdenDvd :
      2 ^ c * v ∣ 2 ^ N * (2 ^ H - 1) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopPow
      (dvd_mul_of_dvd_left h2c _)
      (dvd_mul_of_dvd_right hvM _)
  have hrdenDvd :
      r.den ∣ 2 ^ N * (2 ^ H - 1) := by
    rwa [hden] at hdenDvd
  obtain ⟨d, hd⟩ :=
    tail_diff_int_of_den_dvd r hr.symm H N hrdenDvd
  obtain ⟨u, hu⟩ :=
    exists_int_scaled_tail_of_rat_den_eq r hr.symm hden hcN
  have hfilter : ∀ z : ℤ,
      (z : ℝ) = totientTail (N + H) - totientTail N →
      Int.ModEq (p : ℤ) z (-totientBlock H N) := by
    intro z hz
    exact tail_diff_modEq_neg_totientBlock_of_scaled_tail
      hp hpM hcopPV hz hu
  exact
    (tail_diff_notMem_int_of_primeBasepointFilteredCarryKill hkill hfilter)
      ⟨d, hd⟩

/-- **Prime-filtered conditional closure of Erdős #249.**  Rationality splits
its denominator as `2^c v`; Euler supplies a base period `φ(v)`, and every
clean cyclotomic multiple forces an integral tail carry into the single
residue class checked by `PrimeFilteredCarryKill`. -/
theorem irrational_totient_series_of_cyclotomicPrimeFilteredCarryKillSupply
    {C : ℕ → ℕ}
    (hsupply : CyclotomicPrimeFilteredCarryKillSupply C) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  have hmem :
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ∈
        Set.range ((↑) : ℚ → ℝ) := by
    by_contra hnot
    exact hrat hnot
  obtain ⟨r, hr⟩ := hmem
  let v : ℕ := ordCompl[2] r.den
  let c : ℕ := r.den.factorization 2
  let h : ℕ := Nat.totient v
  have hv : 0 < v := by
    dsimp [v]
    exact Nat.ordCompl_pos 2 r.den_pos.ne'
  have hcopTwo : Nat.Coprime 2 v := by
    dsimp [v]
    exact Nat.coprime_ordCompl Nat.prime_two r.den_pos.ne'
  have hh : 0 < h := by
    dsimp [h]
    exact Nat.totient_pos.mpr hv
  obtain ⟨q, p, K, hq, hp, hcopAnchor, hpC, hpM, hord, hremote, hkill⟩ :=
    hsupply h hh (max c v)
  have hcN : c ≤ p - 1 := (le_max_left c v).trans hremote
  have hvN : v ≤ p - 1 := (le_max_right c v).trans hremote
  have hpNotDvdV : ¬p ∣ v := by
    intro hpdvd
    have hpLeV : p ≤ v := Nat.le_of_dvd hv hpdvd
    omega
  have hcopPV : Nat.Coprime p v :=
    hp.coprime_iff_not_dvd.mpr hpNotDvdV
  have hden : 2 ^ c * v = r.den := by
    simpa [c, v] using Nat.ordProj_mul_ordCompl_eq_self r.den 2
  have heuler : (2 : ℕ) ^ h ≡ 1 [MOD v] := by
    dsimp [h]
    exact Nat.ModEq.pow_totient hcopTwo
  have hvMbase : v ∣ 2 ^ h - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp heuler.symm
  have hbaseDvd : 2 ^ h - 1 ∣ 2 ^ (h * q) - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_right h q)
  have hvM : v ∣ 2 ^ (h * q) - 1 := hvMbase.trans hbaseDvd
  have h2c : (2 : ℕ) ^ c ∣ 2 ^ (p - 1) := pow_dvd_pow 2 hcN
  have hcopPow : Nat.Coprime (2 ^ c) v :=
    Nat.Coprime.pow_left _ hcopTwo
  have hdenDvd :
      2 ^ c * v ∣ 2 ^ (p - 1) * (2 ^ (h * q) - 1) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopPow
      (dvd_mul_of_dvd_left h2c _)
      (dvd_mul_of_dvd_right hvM _)
  have hrdenDvd :
      r.den ∣ 2 ^ (p - 1) * (2 ^ (h * q) - 1) := by
    rwa [hden] at hdenDvd
  obtain ⟨d, hd⟩ :=
    tail_diff_int_of_den_dvd r hr.symm (h * q) (p - 1) hrdenDvd
  obtain ⟨u, hu⟩ :=
    exists_int_scaled_tail_of_rat_den_eq r hr.symm hden hcN
  have hfilter : ∀ z : ℤ,
      (z : ℝ) =
        totientTail (p - 1 + h * q) - totientTail (p - 1) →
      Int.ModEq (p : ℤ) z (-totientBlock (h * q) (p - 1)) := by
    intro z hz
    exact tail_diff_modEq_neg_totientBlock_of_scaled_tail
      hp hpM hcopPV hz hu
  exact
    (tail_diff_notMem_int_of_primeFilteredCarryKill hp hkill hfilter)
      ⟨d, hd⟩

/-- Irrationality repopulates the filtered finite certificates at any clean
anchor family whose layers divide the corresponding Mersenne values. -/
theorem cyclotomicPrimeFilteredCarryKillSupply_of_irrational_of_cleanAnchorSupply
    {C : ℕ → ℕ}
    (hclean : CleanCyclotomicAnchorSupply C)
    (hMersenne : ∀ n : ℕ, C n ∣ mersenneLayer n)
    (hirr : Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    CyclotomicPrimeFilteredCarryKillSupply C := by
  intro h hh N₀
  obtain ⟨q, p, hq, hp, hcop, hpC, hord, hN⟩ :=
    hclean h hh N₀
  have hpM : p ∣ mersenneLayer (h * q) :=
    hpC.trans (hMersenne (h * q))
  have hHpos : 0 < h * q := Nat.mul_pos hh hq.pos
  have hnon :
      totientTail (p - 1 + h * q) - totientTail (p - 1) ∉
        Set.range ((↑) : ℤ → ℝ) :=
    irrational_totient_series_iff_all_tail_diffs_nonintegral.mp
      hirr (h * q) hHpos (p - 1)
  obtain ⟨K, hkill⟩ :=
    exists_primeFilteredCarryKill_of_tail_diff_notMem_int hp hnon
  exact ⟨q, p, K, hq, hp, hcop, hpC, hpM, hord, hN, hkill⟩

/-- With clean Mersenne-dividing layers, the denominator-filtered four-state
certificate supply is exactly Erdős #249, not a stronger surrogate. -/
theorem cyclotomicPrimeFilteredCarryKillSupply_iff_irrational_of_cleanAnchorSupply
    {C : ℕ → ℕ}
    (hclean : CleanCyclotomicAnchorSupply C)
    (hMersenne : ∀ n : ℕ, C n ∣ mersenneLayer n) :
    CyclotomicPrimeFilteredCarryKillSupply C ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  constructor
  · exact irrational_totient_series_of_cyclotomicPrimeFilteredCarryKillSupply
  · exact cyclotomicPrimeFilteredCarryKillSupply_of_irrational_of_cleanAnchorSupply
      hclean hMersenne

/-- Exact prime-filtered claim ceiling for the concrete binary cyclotomic
layers. -/
theorem binaryCyclotomicPrimeFilteredCarryKillSupply_iff_irrational :
    CyclotomicPrimeFilteredCarryKillSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  cyclotomicPrimeFilteredCarryKillSupply_iff_irrational_of_cleanAnchorSupply
    cleanCyclotomicAnchorSupply_binaryCyclotomicLayer
    binaryCyclotomicLayer_dvd_mersenneLayer

/-- The basepoint-decoupled supply is itself exactly Erdős #249.  The
forward implication uses its direct consumer; the reverse implication is
already furnished by clean binary cyclotomic anchors. -/
theorem primeBasepointFilteredCarryKillSupply_iff_irrational :
    PrimeBasepointFilteredCarryKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  constructor
  · exact irrational_totient_series_of_primeBasepointFilteredCarryKillSupply
  · intro hirr
    exact primeBasepointFilteredCarryKillSupply_of_cyclotomicFiltered
      (binaryCyclotomicPrimeFilteredCarryKillSupply_iff_irrational.mpr hirr)

/-- **Full-Mersenne one-state claim ceiling.**  For every possible dyadic
preperiod `c` and positive odd denominator factor `v`, a remote multiple
`H` of `φ(v)` retains the whole quotient

`M = (2^H - 1) / v`.

The quotient is required to exceed the complete initial carry radius, so
its launches locked through depth three form an at-most-one set.  The only
remaining demand is that this single state eventually escape. -/
def FullMersenneSingleLockedCarryKillSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∀ N₀ : ℕ, ∃ H N M K : ℕ,
      0 < H ∧
      Nat.totient v ∣ H ∧
      max c N₀ ≤ N ∧
      v * M = 2 ^ H - 1 ∧
      N + H + 2 < M ∧
      PrimeBasepointSingleLockedCarryKill H N M K

/-- Irrationality supplies the full-Mersenne one-state certificates.  The
exponential quotient is made larger than the chosen linear carry radius by
the repository's general linear-versus-power lemma; Euler supplies the
exact denominator factor. -/
theorem fullMersenneSingleLockedCarryKillSupply_of_irrational
    (hirr : Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    FullMersenneSingleLockedCarryKillSupply := by
  intro c v hv hcop N₀
  let N : ℕ := max c N₀
  let h : ℕ := Nat.totient v
  have hh : 0 < h := by
    dsimp [h]
    exact Nat.totient_pos.mpr hv
  obtain ⟨t, ht, htPow⟩ :=
    exists_linear_lt_pow 2 (v * (N + 2) + 1) (v * h) 1 (by omega)
  let H : ℕ := h * t
  have hHpos : 0 < H := Nat.mul_pos hh (by omega)
  have hhH : h ∣ H := dvd_mul_right h t
  have htH : t ≤ H := by
    dsimp [H]
    have hhOne : 1 ≤ h := hh
    nlinarith
  have htwoPow : 2 ^ t ≤ 2 ^ H :=
    Nat.pow_le_pow_right (by omega) htH
  have hlinear :
      v * (N + H + 2) + 1 < 2 ^ t := by
    dsimp [H] at htPow ⊢
    nlinarith
  have hscaledWidth : v * (N + H + 2) < 2 ^ H - 1 := by
    have hpowPos : 0 < 2 ^ H := pow_pos (by omega) H
    omega
  have heuler : (2 : ℕ) ^ h ≡ 1 [MOD v] := by
    dsimp [h]
    exact Nat.ModEq.pow_totient hcop
  have hvBase : v ∣ 2 ^ h - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp
      heuler.symm
  have hvMersenne : v ∣ 2 ^ H - 1 := by
    exact hvBase.trans
      (Nat.pow_sub_one_dvd_pow_sub_one 2 hhH)
  let M : ℕ := (2 ^ H - 1) / v
  have hfactor : v * M = 2 ^ H - 1 := by
    dsimp [M]
    exact Nat.mul_div_cancel' hvMersenne
  have hwidth : N + H + 2 < M := by
    have hmul :
        v * (N + H + 2) < v * M := by
      rwa [hfactor]
    exact (Nat.mul_lt_mul_left hv).mp hmul
  have hnon :
      totientTail (N + H) - totientTail N ∉
        Set.range ((↑) : ℤ → ℝ) :=
    irrational_totient_series_iff_all_tail_diffs_nonintegral.mp
      hirr H hHpos N
  obtain ⟨K, hfiltered⟩ :=
    exists_primeBasepointFilteredCarryKill_of_tail_diff_notMem_int
      (p := M) hnon
  let K' : ℕ := max 3 K
  have hK' : 3 ≤ K' := le_max_left 3 K
  have hmono : PrimeBasepointFilteredCarryKill H N M K' :=
    primeBasepointFilteredCarryKill_mono (le_max_right 3 K) hfiltered
  have hsingle : PrimeBasepointSingleLockedCarryKill H N M K' :=
    primeBasepointSingleLockedCarryKill_of_filtered hK' hmono
  exact ⟨H, N, M, K', hHpos, hhH, le_rfl, hfactor, hwidth, hsingle⟩

/-- The full Mersenne quotient directly excludes rationality.  For the
actual odd denominator factor `v`, the supplied factorization makes every
integral tail difference land in the retained composite residue class;
the one-state certificate is losslessly converted back to the full
filtered kill. -/
theorem irrational_totient_series_of_fullMersenneSingleLockedCarryKillSupply
    (hsupply : FullMersenneSingleLockedCarryKillSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  have hmem :
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ∈
        Set.range ((↑) : ℚ → ℝ) := by
    by_contra hnot
    exact hrat hnot
  obtain ⟨r, hr⟩ := hmem
  let v : ℕ := ordCompl[2] r.den
  let c : ℕ := r.den.factorization 2
  have hv : 0 < v := by
    dsimp [v]
    exact Nat.ordCompl_pos 2 r.den_pos.ne'
  have hcopTwo : Nat.Coprime 2 v := by
    dsimp [v]
    exact Nat.coprime_ordCompl Nat.prime_two r.den_pos.ne'
  obtain ⟨H, N, M, K, hHpos, _hperiod, hNremote, hfactor, _hwidth,
      hsingle⟩ :=
    hsupply c v hv hcopTwo 0
  have hcN : c ≤ N := by
    exact (le_max_left c 0).trans hNremote
  have hden : 2 ^ c * v = r.den := by
    simpa [c, v] using Nat.ordProj_mul_ordCompl_eq_self r.den 2
  have h2c : (2 : ℕ) ^ c ∣ 2 ^ N := pow_dvd_pow 2 hcN
  have hvM : v ∣ 2 ^ H - 1 := ⟨M, hfactor.symm⟩
  have hcopPow : Nat.Coprime (2 ^ c) v :=
    Nat.Coprime.pow_left _ hcopTwo
  have hdenDvd :
      2 ^ c * v ∣ 2 ^ N * (2 ^ H - 1) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopPow
      (dvd_mul_of_dvd_left h2c _)
      (dvd_mul_of_dvd_right hvM _)
  have hrdenDvd :
      r.den ∣ 2 ^ N * (2 ^ H - 1) := by
    rwa [hden] at hdenDvd
  obtain ⟨d, hd⟩ :=
    tail_diff_int_of_den_dvd r hr.symm H N hrdenDvd
  obtain ⟨u, hu⟩ :=
    exists_int_scaled_tail_of_rat_den_eq r hr.symm hden hcN
  have hfilter : ∀ z : ℤ,
      (z : ℝ) = totientTail (N + H) - totientTail N →
      Int.ModEq (M : ℤ) z (-totientBlock H N) := by
    intro z hz
    exact tail_diff_modEq_neg_totientBlock_of_scaled_tail_factor
      hv hfactor hz hu
  have hfiltered : PrimeBasepointFilteredCarryKill H N M K :=
    primeBasepointFilteredCarryKill_of_singleLocked hsingle
  exact
    (tail_diff_notMem_int_of_primeBasepointFilteredCarryKill
      hfiltered hfilter) ⟨d, hd⟩

/-- The full-Mersenne one-state residual is exactly Erdős #249.  It loses
neither direction while replacing the prime factor by an exponentially
large denominator quotient and certifying that only one launch survives
the initial collapse. -/
theorem fullMersenneSingleLockedCarryKillSupply_iff_irrational :
    FullMersenneSingleLockedCarryKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  constructor
  · exact irrational_totient_series_of_fullMersenneSingleLockedCarryKillSupply
  · exact fullMersenneSingleLockedCarryKillSupply_of_irrational

/-- The least nonnegative representative of the forced full-Mersenne block
class. -/
def fullMersenneBlockResidue (H N M : ℕ) : ℤ :=
  (-totientBlock H N) % (M : ℤ)

/-- The forced block residue lies in the central open arc left after
removing the complete initial analytic interval from both ends of a
modulus. -/
def FullMersenneCenteredResidueGap (H N M : ℕ) : Prop :=
  let B : ℤ := N + H + 1
  B < fullMersenneBlockResidue H N M ∧
    fullMersenneBlockResidue H N M < (M : ℤ) - B

instance (H N M : ℕ) :
    Decidable (FullMersenneCenteredResidueGap H N M) := by
  unfold FullMersenneCenteredResidueGap
  infer_instance

/-- **Exact centered-residue dynamics.**  Once `M` divides the height-`H`
Mersenne number, sliding the basepoint doubles the current residue and
subtracts the new totient-difference letter.  The large endpoint term in
`totientBlock_succ` disappears modulo `M`; no analytic tail or carry lift
remains in this recurrence. -/
theorem fullMersenneBlockResidue_succ
    {H N M : ℕ} (hM : M ∣ 2 ^ H - 1) :
    fullMersenneBlockResidue H (N + 1) M =
      (2 * fullMersenneBlockResidue H N M -
        deltaTotient H (N + 1)) % (M : ℤ) := by
  have hMZ : (M : ℤ) ∣ (2 : ℤ) ^ H - 1 := by
    have hpow : 1 ≤ 2 ^ H := one_le_pow₀ (by omega : 1 ≤ 2)
    have hcast :
        (((2 ^ H - 1 : ℕ) : ℤ)) = (2 : ℤ) ^ H - 1 := by
      rw [Nat.cast_sub hpow, Nat.cast_pow]
      norm_num
    rw [← hcast]
    exact Int.natCast_dvd_natCast.mpr hM
  have hstep :
      Int.ModEq (M : ℤ) (-totientBlock H (N + 1))
        (2 * (-totientBlock H N) - deltaTotient H (N + 1)) := by
    rw [totientBlock_succ]
    rw [Int.modEq_iff_dvd]
    have hmultiple :
        (M : ℤ) ∣ ((2 : ℤ) ^ H - 1) *
          (Nat.totient (N + 1) : ℤ) :=
      dvd_mul_of_dvd_left hMZ _
    convert dvd_neg.mpr hmultiple using 1
    ring
  have hreduce :
      Int.ModEq (M : ℤ)
        (2 * (-totientBlock H N) - deltaTotient H (N + 1))
        (2 * fullMersenneBlockResidue H N M -
          deltaTotient H (N + 1)) := by
    exact
      ((Int.mod_modEq (-totientBlock H N) (M : ℤ)).symm.mul_left 2).sub
        (Int.ModEq.refl (deltaTotient H (N + 1)))
  simpa only [fullMersenneBlockResidue, Int.ModEq] using
    hstep.trans hreduce

/-- The canonical signed representative of the forced full-Mersenne block
class.  Unlike the least nonnegative residue, this lives in the closed
signed half-cell around zero. -/
def fullMersenneBlockCenteredLift (H N M : ℕ) : ℤ :=
  Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.actualCenteredLift
    (-totientBlock H N) (M : ℤ)

/-- Centering preserves exactly the least nonnegative full-Mersenne block
residue. -/
theorem fullMersenneBlockCenteredLift_emod
    (H N M : ℕ) :
    fullMersenneBlockCenteredLift H N M % (M : ℤ) =
      fullMersenneBlockResidue H N M := by
  simpa only [fullMersenneBlockCenteredLift, fullMersenneBlockResidue,
    Int.ModEq] using
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.actualCenteredLift_modEq
      (-totientBlock H N) (M : ℤ)

/-- Signed centered lifts obey the same affine recurrence modulo every
divisor of `2^H-1`.  This is the signed version of
`fullMersenneBlockResidue_succ`, suitable for a later no-wrap argument. -/
theorem fullMersenneBlockCenteredLift_succ_modEq
    {H N M : ℕ} (hM : M ∣ 2 ^ H - 1) :
    Int.ModEq (M : ℤ)
      (fullMersenneBlockCenteredLift H (N + 1) M)
      (2 * fullMersenneBlockCenteredLift H N M -
        deltaTotient H (N + 1)) := by
  have hleft :
      Int.ModEq (M : ℤ)
        (fullMersenneBlockCenteredLift H (N + 1) M)
        (-totientBlock H (N + 1)) := by
    exact
      Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.actualCenteredLift_modEq
        (-totientBlock H (N + 1)) (M : ℤ)
  have hMZ : (M : ℤ) ∣ (2 : ℤ) ^ H - 1 := by
    have hpow : 1 ≤ 2 ^ H := one_le_pow₀ (by omega : 1 ≤ 2)
    have hcast :
        (((2 ^ H - 1 : ℕ) : ℤ)) = (2 : ℤ) ^ H - 1 := by
      rw [Nat.cast_sub hpow, Nat.cast_pow]
      norm_num
    rw [← hcast]
    exact Int.natCast_dvd_natCast.mpr hM
  have hstep :
      Int.ModEq (M : ℤ) (-totientBlock H (N + 1))
        (2 * (-totientBlock H N) - deltaTotient H (N + 1)) := by
    rw [totientBlock_succ, Int.modEq_iff_dvd]
    have hmultiple :
        (M : ℤ) ∣ ((2 : ℤ) ^ H - 1) *
          (Nat.totient (N + 1) : ℤ) :=
      dvd_mul_of_dvd_left hMZ _
    convert dvd_neg.mpr hmultiple using 1
    ring
  have hright :
      Int.ModEq (M : ℤ)
        (2 * (-totientBlock H N) - deltaTotient H (N + 1))
        (2 * fullMersenneBlockCenteredLift H N M -
          deltaTotient H (N + 1)) := by
    exact
      ((Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.actualCenteredLift_modEq
          (-totientBlock H N) (M : ℤ)).symm.mul_left 2).sub
          (Int.ModEq.refl (deltaTotient H (N + 1)))
  exact hleft.trans (hstep.trans hright)

/-- Quantitative no-wrap principle for the centered residue dynamics.  If
the two signed sides together fit strictly inside one modulus, their modular
affine recurrence is an actual equality in `ℤ`. -/
theorem fullMersenneBlockCenteredLift_succ_eq_of_abs_add_abs_lt
    {H N M : ℕ} (hM : M ∣ 2 ^ H - 1)
    (hsmall :
      |fullMersenneBlockCenteredLift H (N + 1) M| +
          |2 * fullMersenneBlockCenteredLift H N M -
            deltaTotient H (N + 1)| < (M : ℤ)) :
    fullMersenneBlockCenteredLift H (N + 1) M =
      2 * fullMersenneBlockCenteredLift H N M -
        deltaTotient H (N + 1) := by
  have hmod :=
    fullMersenneBlockCenteredLift_succ_modEq
      (H := H) (N := N) (M := M) hM
  rw [Int.modEq_iff_dvd] at hmod
  have htriangle :
      |(2 * fullMersenneBlockCenteredLift H N M -
          deltaTotient H (N + 1)) -
        fullMersenneBlockCenteredLift H (N + 1) M| ≤
          |2 * fullMersenneBlockCenteredLift H N M -
            deltaTotient H (N + 1)| +
          |fullMersenneBlockCenteredLift H (N + 1) M| := by
    exact abs_sub _ _
  have habs :
      |(2 * fullMersenneBlockCenteredLift H N M -
          deltaTotient H (N + 1)) -
        fullMersenneBlockCenteredLift H (N + 1) M| < (M : ℤ) := by
    linarith
  have hzero := Int.eq_zero_of_abs_lt_dvd hmod habs
  linarith

/-- With one unit of room for strict integer inequalities, the open central
residue arc is exactly escape of the signed centered lift from the analytic
radius `N+H+1`.  This turns the remaining Euclidean two-sided band into one
absolute-value inequality. -/
theorem fullMersenneCenteredResidueGap_iff_abs_centeredLift
    {H N M : ℕ} (hM : 0 < M)
    (hroom : 2 * (N + H + 2) ≤ M) :
    FullMersenneCenteredResidueGap H N M ↔
      ((N + H + 1 : ℕ) : ℤ) <
        |fullMersenneBlockCenteredLift H N M| := by
  let B : ℤ := ((N + H + 1 : ℕ) : ℤ)
  let T : ℤ := B + 1
  let z : ℤ := fullMersenneBlockCenteredLift H N M
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  have hroomZ : 2 * T ≤ (M : ℤ) := by
    dsimp [T, B]
    exact_mod_cast hroom
  have hz : |z| ≤ (M : ℤ) / 2 := by
    dsimp [z, fullMersenneBlockCenteredLift]
    exact
      Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.abs_actualCenteredLift_le_half
        hMZ
  have hzmod :
      z % (M : ℤ) = fullMersenneBlockResidue H N M := by
    dsimp [z]
    exact fullMersenneBlockCenteredLift_emod H N M
  have hband :
      (T ≤ z % (M : ℤ) ∧ z % (M : ℤ) ≤ (M : ℤ) - T) ↔
        T ≤ |z| :=
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.centeredTopEdgeBand_iff_abs
      hMZ hroomZ hz
  rw [hzmod] at hband
  change
    (B < fullMersenneBlockResidue H N M ∧
      fullMersenneBlockResidue H N M < (M : ℤ) - B) ↔
      B < |z|
  omega

/-- **Two-edge-lock rigidity.**  When the modulus is wider than four
successive analytic radii, failure of the central gap at two adjacent
basepoints removes every possible modular wrap.  The signed representatives
must then follow the literal affine totient-difference recurrence in `ℤ`.
Thus a long edge-locked residue orbit is not merely congruent to a carry
orbit: in the large-modulus regime it *is* that orbit. -/
theorem fullMersenneBlockCenteredLift_succ_eq_of_two_edge_locks
    {H N M : ℕ} (hM : 0 < M) (hMersenne : M ∣ 2 ^ H - 1)
    (hlarge : 4 * (N + H + 3) < M)
    (hlock : ¬FullMersenneCenteredResidueGap H N M)
    (hlockSucc : ¬FullMersenneCenteredResidueGap H (N + 1) M) :
    fullMersenneBlockCenteredLift H (N + 1) M =
      2 * fullMersenneBlockCenteredLift H N M -
        deltaTotient H (N + 1) := by
  have hroom : 2 * (N + H + 2) ≤ M := by omega
  have hroomSucc : 2 * ((N + 1) + H + 2) ≤ M := by omega
  have hNiff :=
    fullMersenneCenteredResidueGap_iff_abs_centeredLift
      (H := H) (N := N) (M := M) hM hroom
  have hSuccIff :=
    fullMersenneCenteredResidueGap_iff_abs_centeredLift
      (H := H) (N := N + 1) (M := M) hM hroomSucc
  have hx :
      |fullMersenneBlockCenteredLift H N M| ≤
        ((N + H + 1 : ℕ) : ℤ) := by
    by_contra hnot
    exact hlock (hNiff.mpr (lt_of_not_ge hnot))
  have hy :
      |fullMersenneBlockCenteredLift H (N + 1) M| ≤
        (((N + 1) + H + 1 : ℕ) : ℤ) := by
    by_contra hnot
    exact hlockSucc (hSuccIff.mpr (lt_of_not_ge hnot))
  have hd := abs_deltaTotient_le H (N + 1)
  have hraw :
      |2 * fullMersenneBlockCenteredLift H N M -
          deltaTotient H (N + 1)| ≤
        2 * |fullMersenneBlockCenteredLift H N M| +
          |deltaTotient H (N + 1)| := by
    calc
      |2 * fullMersenneBlockCenteredLift H N M -
          deltaTotient H (N + 1)| ≤
          |2 * fullMersenneBlockCenteredLift H N M| +
            |deltaTotient H (N + 1)| := abs_sub _ _
      _ = 2 * |fullMersenneBlockCenteredLift H N M| +
            |deltaTotient H (N + 1)| := by
          rw [abs_mul]
          norm_num
  have hlargeZ :
      (4 : ℤ) * ((N + H + 3 : ℕ) : ℤ) < (M : ℤ) := by
    exact_mod_cast hlarge
  push_cast at hx hy hd hlargeZ
  have hsmall :
      |fullMersenneBlockCenteredLift H (N + 1) M| +
          |2 * fullMersenneBlockCenteredLift H N M -
            deltaTotient H (N + 1)| < (M : ℤ) := by
    nlinarith
  exact
    fullMersenneBlockCenteredLift_succ_eq_of_abs_add_abs_lt
      hMersenne hsmall

/-- **Interval edge-lock rigidity.**  If the central full-Mersenne gap fails
through a whole interval and the modulus has room for the final analytic
radius, then every centered block lift on that interval is literally the
ordinary integer carry orbit launched from the first lift.  This is the
iterated form of `fullMersenneBlockCenteredLift_succ_eq_of_two_edge_locks`;
there is no modular ambiguity left anywhere in the interval. -/
theorem fullMersenneBlockCenteredLift_add_eq_carryOrbit_of_edge_locks
    {H N M L : ℕ} (hM : 0 < M) (hMersenne : M ∣ 2 ^ H - 1)
    (hlarge : 4 * (N + L + H + 3) < M)
    (hlock :
      ∀ i : ℕ, i ≤ L →
        ¬FullMersenneCenteredResidueGap H (N + i) M) :
    ∀ i : ℕ, i ≤ L →
      fullMersenneBlockCenteredLift H (N + i) M =
        carryOrbit H N (fullMersenneBlockCenteredLift H N M) i := by
  intro i hi
  induction i with
  | zero =>
      simp [carryOrbit]
  | succ i ih =>
      have hiL : i ≤ L := by omega
      have hlocalLarge : 4 * ((N + i) + H + 3) < M := by
        nlinarith
      have hstep :=
        fullMersenneBlockCenteredLift_succ_eq_of_two_edge_locks
          (H := H) (N := N + i) (M := M) hM hMersenne hlocalLarge
          (hlock i hiL) (hlock (i + 1) hi)
      rw [show N + (i + 1) = (N + i) + 1 by omega, hstep, ih hiL]
      simp only [carryOrbit]

/-- **Finite full-Mersenne escape certificate.**  Under the same
large-modulus geometry, it is enough to find one depth at which the ordinary
carry orbit launched from the canonical signed block lift exceeds the local
analytic radius.  Some central full-Mersenne residue gap must then already
occur at or before that depth.  This is the exact contrapositive consumer of
interval edge-lock rigidity. -/
theorem exists_fullMersenneCenteredResidueGap_of_carryOrbit_escape
    {H N M L : ℕ} (hM : 0 < M) (hMersenne : M ∣ 2 ^ H - 1)
    (hlarge : 4 * (N + L + H + 3) < M)
    (hescape :
      ∃ i : ℕ, i ≤ L ∧
        (((N + i + H + 1 : ℕ) : ℤ) <
          |carryOrbit H N (fullMersenneBlockCenteredLift H N M) i|)) :
    ∃ i : ℕ, i ≤ L ∧
      FullMersenneCenteredResidueGap H (N + i) M := by
  by_contra hnone
  push Not at hnone
  obtain ⟨i, hi, hescapeAt⟩ := hescape
  have htrack :=
    fullMersenneBlockCenteredLift_add_eq_carryOrbit_of_edge_locks
      (H := H) (N := N) (M := M) (L := L) hM hMersenne hlarge
      hnone i hi
  have hroom : 2 * ((N + i) + H + 2) ≤ M := by
    nlinarith
  have hgap :=
    (fullMersenneCenteredResidueGap_iff_abs_centeredLift
      (H := H) (N := N + i) (M := M) hM hroom).mpr
      (by simpa [htrack] using hescapeAt)
  exact hnone i hi hgap

/-- The ordinary finite survivor certificate can now be consumed directly
against the canonical full-Mersenne residue.  If every integer launch in the
initial analytic box escapes by depth `L`, then a modulus large enough to
prevent wrapping cannot remain edge-locked throughout that interval. -/
theorem exists_fullMersenneCenteredResidueGap_of_survivorKill
    {H N M L : ℕ} (hM : 0 < M) (hMersenne : M ∣ 2 ^ H - 1)
    (hlarge : 4 * (N + L + H + 3) < M)
    (hkill : survivorKill H N L) :
    ∃ i : ℕ, i ≤ L ∧
      FullMersenneCenteredResidueGap H (N + i) M := by
  by_contra hnone
  push Not at hnone
  let c : ℤ := fullMersenneBlockCenteredLift H N M
  let R : ℤ := ((N + H + 1 : ℕ) : ℤ)
  have hroom : 2 * (N + H + 2) ≤ M := by
    nlinarith
  have hgapIff :=
    fullMersenneCenteredResidueGap_iff_abs_centeredLift
      (H := H) (N := N) (M := M) hM hroom
  have hcabs : |c| ≤ R := by
    by_contra hnot
    have hgap :
        FullMersenneCenteredResidueGap H N M :=
      hgapIff.mpr (by
        dsimp [c, R] at *
        omega)
    exact hnone 0 (by omega) (by simpa using hgap)
  have hcnonneg : 0 ≤ c + R := by
    have hclow : -R ≤ c := (abs_le.mp hcabs).1
    linarith
  have hcast : (((c + R).toNat : ℕ) : ℤ) = c + R :=
    Int.toNat_of_nonneg hcnonneg
  have hmem :
      (c + R).toNat ∈ Finset.range (2 * (N + H + 1) + 1) := by
    rw [Finset.mem_range]
    have hhigh : c ≤ R := (abs_le.mp hcabs).2
    dsimp [R] at *
    omega
  obtain ⟨i, hiRange, hescape⟩ :=
    hkill (c + R).toNat hmem
  have hi : i ≤ L := by
    rw [Finset.mem_range] at hiRange
    omega
  have hcand :
      (((c + R).toNat : ℤ)) - (N + H + 1 : ℤ) = c := by
    rw [hcast]
    dsimp [R]
    ring
  rw [hcand] at hescape
  have hescapeAt :
      (((N + i + H + 1 : ℕ) : ℤ) <
        |carryOrbit H N (fullMersenneBlockCenteredLift H N M) i|) := by
    dsimp [c] at hescape
    rcases hescape with hlow | hhigh
    · have hnonpos :
          carryOrbit H N (fullMersenneBlockCenteredLift H N M) i ≤ 0 := by
        omega
      rw [abs_of_nonpos hnonpos]
      push_cast
      omega
    · have hnonneg :
          0 ≤ carryOrbit H N (fullMersenneBlockCenteredLift H N M) i := by
        omega
      rw [abs_of_nonneg hnonneg]
      push_cast
      omega
  obtain ⟨j, hj, hgap⟩ :=
    exists_fullMersenneCenteredResidueGap_of_carryOrbit_escape
      hM hMersenne hlarge ⟨i, hi, hescapeAt⟩
  exact hnone j hj hgap

/-- A central dyadic endpoint certificate kills every launch in the initial
analytic box at its certified depth.  This packages the endpoint-fibre
interpretation of `certifiedKill` in the `survivorKill` interface used by the
full-Mersenne dynamics. -/
theorem survivorKill_of_certifiedKill
    {H N L : ℕ} (hcert : certifiedKill H N L) :
    survivorKill H N L := by
  intro j _hj
  let d : ℤ := (j : ℤ) - (N + H + 1 : ℤ)
  let z : ℤ := carryOrbit H N d L
  refine ⟨L, Finset.mem_range.mpr (by omega), ?_⟩
  change z ≤ -(N + L + H + 2 : ℤ) ∨
    (N + L + H + 2 : ℤ) ≤ z
  by_contra hinside
  push Not at hinside
  have hzabs :
      |-z| ≤ (N + H + L + 2 : ℤ) := by
    rw [abs_le]
    omega
  have hreset :=
    carryOrbit_modEq_neg_windowDiscrepancy H N d L
  have hneg := hreset.neg
  have hzmod :
      (-z) % (2 : ℤ) ^ L =
        windowDiscrepancy H N L % (2 : ℤ) ^ L := by
    simpa [z] using hneg
  exact
    no_endpointSurvivor_of_certifiedKill hcert (-z)
      ⟨by simpa [add_assoc, add_left_comm, add_comm] using hzabs, hzmod⟩

/-- Every ordinary dyadic central-arc certificate therefore forces a genuine
central gap for any sufficiently large divisor of the same Mersenne layer.
This lets the existing checked certificate bank feed the exact
full-Mersenne quotient geometry without another launch enumeration. -/
theorem exists_fullMersenneCenteredResidueGap_of_certifiedKill
    {H N M L : ℕ} (hM : 0 < M) (hMersenne : M ∣ 2 ^ H - 1)
    (hlarge : 4 * (N + L + H + 3) < M)
    (hcert : certifiedKill H N L) :
    ∃ i : ℕ, i ≤ L ∧
      FullMersenneCenteredResidueGap H (N + i) M :=
  exists_fullMersenneCenteredResidueGap_of_survivorKill
    hM hMersenne hlarge (survivorKill_of_certifiedKill hcert)

/-- The full Mersenne quotient residue misses the complete initial
analytic interval.  Equivalently, there is no denominator-compatible
launch even before the carry orbit is iterated. -/
def FullMersenneInitialResidueGap (H N M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (2 * (N + H + 1) + 1),
    ¬Int.ModEq (M : ℤ) ((j : ℤ) - (N + H + 1 : ℤ))
      (-totientBlock H N)

instance (H N M : ℕ) :
    Decidable (FullMersenneInitialResidueGap H N M) := by
  unfold FullMersenneInitialResidueGap
  infer_instance

/-- Exact Euclidean normal form of the zero-launch condition.  For a
positive modulus, absence of every representative in `[-B,B]` is
equivalent to the least nonnegative block residue lying strictly between
`B` and `M-B`. -/
theorem fullMersenneInitialResidueGap_iff_centered
    {H N M : ℕ} (hM : 0 < M) :
    FullMersenneInitialResidueGap H N M ↔
      FullMersenneCenteredResidueGap H N M := by
  let B : ℤ := N + H + 1
  let A : ℤ := -totientBlock H N
  let r : ℤ := A % (M : ℤ)
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg A hMZ.ne'
  have hrM : r < (M : ℤ) := by
    dsimp [r]
    exact Int.emod_lt_of_pos A hMZ
  change
    (∀ j ∈ Finset.range (2 * (N + H + 1) + 1),
      ¬Int.ModEq (M : ℤ) ((j : ℤ) - (N + H + 1 : ℤ)) A) ↔
      B < r ∧ r < (M : ℤ) - B
  constructor
  · intro hgap
    constructor
    · by_contra hnot
      have hrB : r ≤ B := le_of_not_gt hnot
      let j : ℕ := (r + B).toNat
      have hj :
          j ∈ Finset.range (2 * (N + H + 1) + 1) := by
        rw [Finset.mem_range]
        dsimp [j, B] at *
        omega
      have hcand :
          (j : ℤ) - (N + H + 1 : ℤ) = r := by
        dsimp [j, B] at *
        omega
      apply hgap j hj
      rw [hcand]
      dsimp [r, A]
      exact Int.mod_modEq _ _
    · by_contra hnot
      have hrEdge : (M : ℤ) - B ≤ r := le_of_not_gt hnot
      let j : ℕ := (r - (M : ℤ) + B).toNat
      have hj :
          j ∈ Finset.range (2 * (N + H + 1) + 1) := by
        rw [Finset.mem_range]
        dsimp [j, B] at *
        omega
      have hcand :
          (j : ℤ) - (N + H + 1 : ℤ) = r - (M : ℤ) := by
        dsimp [j, B] at *
        omega
      apply hgap j hj
      rw [hcand]
      dsimp [r, A]
      exact Int.sub_modulus_modEq_iff.mpr (Int.mod_modEq _ _)
  · rintro ⟨hlow, hhigh⟩ j hj hmod
    let z : ℤ := (j : ℤ) - (N + H + 1 : ℤ)
    have hjlt : j < 2 * (N + H + 1) + 1 :=
      Finset.mem_range.mp hj
    have hzbox : |z| ≤ B := by
      dsimp [z, B]
      rw [abs_le]
      omega
    have hzmod : z % (M : ℤ) = r := by
      have := hmod.eq
      simpa [z, r, A] using this
    have hzdecomp :
        (M : ℤ) * (z / (M : ℤ)) + r = z := by
      rw [← hzmod]
      exact Int.mul_ediv_add_emod z M
    have hzlohi := abs_le.mp hzbox
    by_cases hq : 0 ≤ z / (M : ℤ)
    · have hmultiple :
          0 ≤ (M : ℤ) * (z / (M : ℤ)) :=
        mul_nonneg hMZ.le hq
      linarith
    · have hqneg : z / (M : ℤ) ≤ -1 := by omega
      have hmultiple :
          (M : ℤ) * (z / (M : ℤ)) ≤ -(M : ℤ) := by
        nlinarith
      linarith

/-- Any positive-height exact factorization
`v M = 2^H - 1` has a positive quotient. -/
theorem mersenne_factor_modulus_pos
    {H v M : ℕ} (hH : 0 < H)
    (hfactor : v * M = 2 ^ H - 1) :
    0 < M := by
  have hprod : 0 < v * M := by
    rw [hfactor]
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hH.ne')
  by_contra hnot
  have hzero : M = 0 := Nat.eq_zero_of_not_pos hnot
  simp [hzero] at hprod

/-- **Full-Mersenne launch-gap claim ceiling.**  For every possible
rational denominator and every requested basepoint, a remote Euler
multiple has a full quotient whose forced block residue misses the entire
initial analytic interval. -/
def FullMersenneInitialResidueGapSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∀ N₀ : ℕ, ∃ H N M : ℕ,
      0 < H ∧
      Nat.totient v ∣ H ∧
      max c N₀ ≤ N ∧
      v * M = 2 ^ H - 1 ∧
      FullMersenneInitialResidueGap H N M

/-- Pure centered-residue form of the full-Mersenne residual.  This is an
explicit arithmetic statement about one finite block sum and one Euclidean
remainder; it contains no carry orbit and no quantified launch index. -/
def FullMersenneCenteredResidueGapSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∀ N₀ : ℕ, ∃ H N M : ℕ,
      0 < H ∧
      Nat.totient v ∣ H ∧
      max c N₀ ≤ N ∧
      v * M = 2 ^ H - 1 ∧
      FullMersenneCenteredResidueGap H N M

/-- **Canonical-denominator basepoint form.**  For a prospective rational
denominator `2^c v`, the finite block starts at the single forced basepoint
`N = c`.  There is no remote-basepoint quantifier and no basepoint witness;
only the Euler-multiple height and its exact Mersenne quotient remain. -/
def FullMersenneCanonicalBasepointResidueGapSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∃ H M : ℕ,
      0 < H ∧
      Nat.totient v ∣ H ∧
      v * M = 2 ^ H - 1 ∧
      FullMersenneCenteredResidueGap H c M

theorem fullMersenneInitialResidueGapSupply_iff_centered :
    FullMersenneInitialResidueGapSupply ↔
      FullMersenneCenteredResidueGapSupply := by
  constructor
  · intro hsupply c v hv hcop N₀
    obtain ⟨H, N, M, hH, hperiod, hN, hfactor, hgap⟩ :=
      hsupply c v hv hcop N₀
    have hM : 0 < M :=
      mersenne_factor_modulus_pos hH hfactor
    exact
      ⟨H, N, M, hH, hperiod, hN, hfactor,
        (fullMersenneInitialResidueGap_iff_centered hM).mp hgap⟩
  · intro hsupply c v hv hcop N₀
    obtain ⟨H, N, M, hH, hperiod, hN, hfactor, hgap⟩ :=
      hsupply c v hv hcop N₀
    have hM : 0 < M :=
      mersenne_factor_modulus_pos hH hfactor
    exact
      ⟨H, N, M, hH, hperiod, hN, hfactor,
        (fullMersenneInitialResidueGap_iff_centered hM).mpr hgap⟩

/-- **One canonical residue gap excludes a full divisor class.**  If the
reduced denominator of `r` divides `2^c * v` and one full-Mersenne
factorization at the canonical basepoint `c` has a centered residue gap, then
the totient series is not `r`.  This turns any certified pointwise gap into a
genuine finite denominator exclusion; it makes no cofinal or irrationality
claim. -/
theorem
    totient_series_ne_rat_of_fullMersenneCanonicalBasepointResidueGap_of_den_dvd
    {c v H M : ℕ} (hv : 0 < v) (hH : 0 < H)
    (hfactor : v * M = 2 ^ H - 1)
    (hgap : FullMersenneCenteredResidueGap H c M)
    (r : ℚ) (hden : r.den ∣ 2 ^ c * v) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := by
  intro hS
  have hM : 0 < M := mersenne_factor_modulus_pos hH hfactor
  have hinitial : FullMersenneInitialResidueGap H c M :=
    (fullMersenneInitialResidueGap_iff_centered hM).mpr hgap
  have hscaleDvd : 2 ^ c * v ∣ 2 ^ c * (2 ^ H - 1) := by
    refine ⟨M, ?_⟩
    rw [← hfactor]
    ring
  have hrdenDvd : r.den ∣ 2 ^ c * (2 ^ H - 1) := by
    exact hden.trans hscaleDvd
  obtain ⟨d, hd⟩ :=
    tail_diff_int_of_den_dvd r hS H c hrdenDvd
  obtain ⟨u, hu⟩ :=
    exists_int_scaled_tail_of_rat_den_dvd r hS hden (le_refl c)
  have hfilter : ∀ z : ℤ,
      (z : ℝ) = totientTail (c + H) - totientTail c →
      Int.ModEq (M : ℤ) z (-totientBlock H c) := by
    intro z hz
    exact tail_diff_modEq_neg_totientBlock_of_scaled_tail_factor
      hv hfactor hz hu
  have hkill : PrimeBasepointFilteredCarryKill H c M 0 := by
    intro j hj hmod
    exact (hinitial j hj hmod).elim
  exact
    (tail_diff_notMem_int_of_primeBasepointFilteredCarryKill
      hkill hfilter) ⟨d, hd⟩

/-- Equality-form specialization of the pointwise denominator-divisor
consumer. -/
theorem totient_series_ne_rat_of_fullMersenneCanonicalBasepointResidueGap
    {c v H M : ℕ} (hv : 0 < v) (hH : 0 < H)
    (hfactor : v * M = 2 ^ H - 1)
    (hgap : FullMersenneCenteredResidueGap H c M)
    (r : ℚ) (hden : 2 ^ c * v = r.den) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := by
  exact
    totient_series_ne_rat_of_fullMersenneCanonicalBasepointResidueGap_of_den_dvd
      hv hH hfactor hgap r (by simp [← hden])

/-- At every *prescribed* basepoint, irrationality supplies a sufficiently
large Euler-multiple height whose full Mersenne quotient misses the complete
analytic launch interval.  This is stronger than merely finding a remote
basepoint: `N` is fixed before `H` is chosen. -/
theorem exists_fullMersenneInitialResidueGap_at_of_irrational
    (hirr : Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    (v N : ℕ) (hv : 0 < v) (hcop : Nat.Coprime 2 v) :
    ∃ H M : ℕ,
      0 < H ∧
      Nat.totient v ∣ H ∧
      v * M = 2 ^ H - 1 ∧
      FullMersenneInitialResidueGap H N M := by
  have htailNon :
      (v : ℝ) * totientTail N ∉ Set.range ((↑) : ℤ → ℝ) :=
    scaled_totientTail_notMem_int_of_irrational hirr hv
  obtain ⟨δ, hδ, hgap⟩ :=
    exists_uniform_int_gap_of_notMem_int htailNon
  obtain ⟨a, ha⟩ := exists_nat_one_div_lt (K := ℝ) hδ
  let A : ℕ := a + 1
  have hA : 0 < A := by
    dsimp [A]
    omega
  let h : ℕ := Nat.totient v
  have hh : 0 < h := by
    dsimp [h]
    exact Nat.totient_pos.mpr hv
  obtain ⟨t, ht, htPow⟩ :=
    exists_linear_lt_pow 2
      (v * (A * (2 * (N + 2))) + 1)
      (v * (A * (2 * h))) 1 (by omega)
  let H : ℕ := h * t
  have hHpos : 0 < H := Nat.mul_pos hh (by omega)
  have hhH : h ∣ H := dvd_mul_right h t
  have htH : t ≤ H := by
    dsimp [H]
    nlinarith
  have htwoPow : 2 ^ t ≤ 2 ^ H :=
    Nat.pow_le_pow_right (by omega) htH
  have hlinear :
      v * (A * (2 * (N + H + 2))) + 1 < 2 ^ t := by
    dsimp [H] at htPow ⊢
    ring_nf at htPow ⊢
    exact htPow
  have hscaledWidth :
      v * (A * (2 * (N + H + 2))) < 2 ^ H - 1 := by
    have hpowPos : 0 < 2 ^ H := pow_pos (by omega) H
    omega
  have heuler : (2 : ℕ) ^ h ≡ 1 [MOD v] := by
    dsimp [h]
    exact Nat.ModEq.pow_totient hcop
  have hvBase : v ∣ 2 ^ h - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp
      heuler.symm
  have hvMersenne : v ∣ 2 ^ H - 1 := by
    exact hvBase.trans
      (Nat.pow_sub_one_dvd_pow_sub_one 2 hhH)
  let M : ℕ := (2 ^ H - 1) / v
  have hfactor : v * M = 2 ^ H - 1 := by
    dsimp [M]
    exact Nat.mul_div_cancel' hvMersenne
  have hwidth : A * (2 * (N + H + 2)) < M := by
    have hmul :
        v * (A * (2 * (N + H + 2))) < v * M := by
      rwa [hfactor]
    exact (Nat.mul_lt_mul_left hv).mp hmul
  have hM : 0 < M := by
    omega
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hratioA :
      (2 * (N + H + 2 : ℝ)) / (M : ℝ) < 1 / (A : ℝ) := by
    rw [div_lt_div_iff₀ hMR hAR]
    have hwidthR :
        (A : ℝ) * (2 * (N + H + 2 : ℝ)) < (M : ℝ) := by
      exact_mod_cast hwidth
    nlinarith
  have hratio :
      (2 * (N + H + 2 : ℝ)) / (M : ℝ) < δ := by
    exact hratioA.trans (by simpa [A] using ha)
  have hno : FullMersenneInitialResidueGap H N M :=
    no_mersenne_factor_candidate_of_scaled_tail_gap
      hM hfactor hgap hratio
  exact ⟨H, M, hHpos, by simpa [h] using hhH, hfactor, hno⟩

/-- Irrationality forces cofinally remote full-Mersenne launch gaps.  At
a fixed basepoint `N`, the scaled tail `v R_N` has a positive distance
from the integer lattice.  An Euler multiple `H` is then chosen so that
the exponentially large quotient `(2^H-1)/v` makes every hypothetical
launch contradict this fixed gap. -/
theorem fullMersenneInitialResidueGapSupply_of_irrational
    (hirr : Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    FullMersenneInitialResidueGapSupply := by
  intro c v hv hcop N₀
  let N : ℕ := max c N₀
  obtain ⟨H, M, hH, hperiod, hfactor, hgap⟩ :=
    exists_fullMersenneInitialResidueGap_at_of_irrational
      hirr v N hv hcop
  exact ⟨H, N, M, hH, hperiod, le_rfl, hfactor, hgap⟩

/-- A full-Mersenne launch-gap supply excludes every rational denominator.
The rational-denominator clearing argument forces the true integral tail
difference into precisely the residue class which the supplied gap says
does not meet its unavoidable analytic interval. -/
theorem irrational_totient_series_of_fullMersenneInitialResidueGapSupply
    (hsupply : FullMersenneInitialResidueGapSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  have hmem :
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ∈
        Set.range ((↑) : ℚ → ℝ) := by
    by_contra hnot
    exact hrat hnot
  obtain ⟨r, hr⟩ := hmem
  let v : ℕ := ordCompl[2] r.den
  let c : ℕ := r.den.factorization 2
  have hv : 0 < v := by
    dsimp [v]
    exact Nat.ordCompl_pos 2 r.den_pos.ne'
  have hcopTwo : Nat.Coprime 2 v := by
    dsimp [v]
    exact Nat.coprime_ordCompl Nat.prime_two r.den_pos.ne'
  obtain ⟨H, N, M, hHpos, _hperiod, hNremote, hfactor, hgap⟩ :=
    hsupply c v hv hcopTwo 0
  have hcN : c ≤ N :=
    (le_max_left c 0).trans hNremote
  have hden : 2 ^ c * v = r.den := by
    simpa [c, v] using Nat.ordProj_mul_ordCompl_eq_self r.den 2
  have h2c : (2 : ℕ) ^ c ∣ 2 ^ N :=
    pow_dvd_pow 2 hcN
  have hvM : v ∣ 2 ^ H - 1 :=
    ⟨M, hfactor.symm⟩
  have hcopPow : Nat.Coprime (2 ^ c) v :=
    Nat.Coprime.pow_left _ hcopTwo
  have hdenDvd :
      2 ^ c * v ∣ 2 ^ N * (2 ^ H - 1) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopPow
      (dvd_mul_of_dvd_left h2c _)
      (dvd_mul_of_dvd_right hvM _)
  have hrdenDvd :
      r.den ∣ 2 ^ N * (2 ^ H - 1) := by
    rwa [hden] at hdenDvd
  obtain ⟨d, hd⟩ :=
    tail_diff_int_of_den_dvd r hr.symm H N hrdenDvd
  obtain ⟨u, hu⟩ :=
    exists_int_scaled_tail_of_rat_den_eq r hr.symm hden hcN
  have hfilter : ∀ z : ℤ,
      (z : ℝ) = totientTail (N + H) - totientTail N →
      Int.ModEq (M : ℤ) z (-totientBlock H N) := by
    intro z hz
    exact tail_diff_modEq_neg_totientBlock_of_scaled_tail_factor
      hv hfactor hz hu
  have hkill : PrimeBasepointFilteredCarryKill H N M 0 := by
    intro j hj hmod
    exact (hgap j hj hmod).elim
  exact
    (tail_diff_notMem_int_of_primeBasepointFilteredCarryKill
      hkill hfilter) ⟨d, hd⟩

/-- **Exact zero-launch claim ceiling.**  Erdős #249 is equivalent to the
statement that, for every possible rational denominator, some remote full
Mersenne quotient has no compatible integer even in the initial analytic
box.  Thus no positive-depth carry search remains in the exact residual. -/
theorem fullMersenneInitialResidueGapSupply_iff_irrational :
    FullMersenneInitialResidueGapSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  constructor
  · exact irrational_totient_series_of_fullMersenneInitialResidueGapSupply
  · exact fullMersenneInitialResidueGapSupply_of_irrational

/-- **Arithmetic normal form of Erdős #249.**  The problem is exactly the
cofinal centrality of the explicit remainder

`(-totientBlock H N) % ((2^H-1)/v)`.

All analytic tails, carry trajectories, cyclotomic prime choices, and
finite launch searches have been eliminated from this equivalent claim. -/
theorem fullMersenneCenteredResidueGapSupply_iff_irrational :
    FullMersenneCenteredResidueGapSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  rw [← fullMersenneInitialResidueGapSupply_iff_centered,
    fullMersenneInitialResidueGapSupply_iff_irrational]

/-- A canonical-basepoint gap can be inflated to any requested remote
basepoint by feeding `max c N₀` into the dyadic-exponent slot.  The odd
denominator `v`, Euler height condition, and full Mersenne quotient are
unchanged. -/
theorem fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint
    (hsupply : FullMersenneCanonicalBasepointResidueGapSupply) :
    FullMersenneCenteredResidueGapSupply := by
  intro c v hv hcop N₀
  let N : ℕ := max c N₀
  obtain ⟨H, M, hH, hperiod, hfactor, hgap⟩ :=
    hsupply N v hv hcop
  exact ⟨H, N, M, hH, hperiod, le_rfl, hfactor, hgap⟩

/-- Irrationality supplies the centered gap at the exact denominator
basepoint `N = c`; no search in `N` is needed. -/
theorem fullMersenneCanonicalBasepointResidueGapSupply_of_irrational
    (hirr : Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    FullMersenneCanonicalBasepointResidueGapSupply := by
  intro c v hv hcop
  obtain ⟨H, M, hH, hperiod, hfactor, hgap⟩ :=
    exists_fullMersenneInitialResidueGap_at_of_irrational
      hirr v c hv hcop
  have hM : 0 < M :=
    mersenne_factor_modulus_pos hH hfactor
  exact
    ⟨H, M, hH, hperiod, hfactor,
      (fullMersenneInitialResidueGap_iff_centered hM).mp hgap⟩

/-- **Fixed-basepoint arithmetic normal form of Erdős #249.**  For every
candidate denominator `2^c v`, it is enough—and is exactly equivalent—to
find one Euler-multiple height `H` for which

`(-totientBlock H c) % ((2^H-1)/v)`

lies outside the two endpoint intervals of width `c+H+1`.  The arbitrary
remote basepoint and its witness have disappeared. -/
theorem fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational :
    FullMersenneCanonicalBasepointResidueGapSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  constructor
  · intro hsupply
    exact fullMersenneCenteredResidueGapSupply_iff_irrational.mp
      (fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint
        hsupply)
  · exact fullMersenneCanonicalBasepointResidueGapSupply_of_irrational

/-- The most compressed free-basepoint claim ceiling is exactly Erdős
#249: every remote clean anchor has at most one three-step survivor, and
that sole state eventually escapes. -/
theorem primeBasepointSingleLockedCarryKillSupply_iff_irrational :
    PrimeBasepointSingleLockedCarryKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  rw [primeBasepointSingleLockedCarryKillSupply_iff_filtered,
    primeBasepointFilteredCarryKillSupply_iff_irrational]

/-- Four-state conditional closure of Erdős #249. -/
theorem irrational_totient_series_of_cyclotomicPrimeFourCarryKillSupply
    {C : ℕ → ℕ}
    (hsupply : CyclotomicPrimeFourCarryKillSupply C) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_cyclotomicPrimeFilteredCarryKillSupply
    (cyclotomicPrimeFourCarryKillSupply_iff_filtered.mp hsupply)

/-- Under clean Mersenne-dividing layers, the literal four-state supply is
exactly Erdős #249. -/
theorem cyclotomicPrimeFourCarryKillSupply_iff_irrational_of_cleanAnchorSupply
    {C : ℕ → ℕ}
    (hclean : CleanCyclotomicAnchorSupply C)
    (hMersenne : ∀ n : ℕ, C n ∣ mersenneLayer n) :
    CyclotomicPrimeFourCarryKillSupply C ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  cyclotomicPrimeFourCarryKillSupply_iff_filtered.trans
    (cyclotomicPrimeFilteredCarryKillSupply_iff_irrational_of_cleanAnchorSupply
      hclean hMersenne)

/-- **Literal four-state claim ceiling for the concrete binary cyclotomic
layers.** -/
theorem binaryCyclotomicPrimeFourCarryKillSupply_iff_irrational :
    CyclotomicPrimeFourCarryKillSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  cyclotomicPrimeFourCarryKillSupply_iff_irrational_of_cleanAnchorSupply
    cleanCyclotomicAnchorSupply_binaryCyclotomicLayer
    binaryCyclotomicLayer_dvd_mersenneLayer

/-- **One-state claim ceiling for the concrete binary cyclotomic layers.**
At each clean anchor, the finite residual contains at most one launch, and
the cofinal assertion that this launch eventually escapes is exactly Erdős
#249. -/
theorem binaryCyclotomicPrimeSingleLockedCarryKillSupply_iff_irrational :
    CyclotomicPrimeSingleLockedCarryKillSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  cyclotomicPrimeSingleLockedCarryKillSupply_iff_four.trans
    binaryCyclotomicPrimeFourCarryKillSupply_iff_irrational

/-- The exact remaining producer after prime support is discharged.  Besides
the certified discrepancy itself, the fields retain the cyclotomic provenance:
`p` is a clean prime divisor of the `h*q` layer and `h*q ∣ p-1`.

The irrationality consumer below needs only the cofinal location and the
certificate.  The additional fields state the intended arithmetic route and
prevent the residual from silently weakening into an unrelated certificate
search. -/
def CyclotomicAnchoredKillSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p L : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 ∧
      certifiedKill (h * q) (p - 1) L

/-- The cyclotomic producer written in its exact finite normal form.  The
arbitrary certificate depth in `CyclotomicAnchoredKillSupply` is replaced by
one translated logarithmic socket or one translated mixed two-bit guard.
All prime-layer provenance is retained verbatim. -/
def CyclotomicGuardCylinderSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 ∧
      GuardCylinderWitness (h * q) (p - 1)

/-- The guard-cylinder formulation loses no arithmetic information: it is
exactly the existing cyclotomic anchored-kill supply. -/
theorem cyclotomicGuardCylinderSupply_iff_anchoredKillSupply
    {C : ℕ → ℕ} :
    CyclotomicGuardCylinderSupply C ↔
      CyclotomicAnchoredKillSupply C := by
  constructor
  · intro hsupply h hh N₀
    obtain ⟨q, p, hq, hp, hcop, hpC, hord, hN, hguard⟩ :=
      hsupply h hh N₀
    obtain ⟨L, hcert⟩ :=
      (exists_certifiedKill_iff_guardCylinderWitness
        (h * q) (p - 1)).mpr hguard
    exact ⟨q, p, L, hq, hp, hcop, hpC, hord, hN, hcert⟩
  · intro hsupply h hh N₀
    obtain ⟨q, p, L, hq, hp, hcop, hpC, hord, hN, hcert⟩ :=
      hsupply h hh N₀
    have hguard : GuardCylinderWitness (h * q) (p - 1) :=
      (exists_certifiedKill_iff_guardCylinderWitness
        (h * q) (p - 1)).mp ⟨L, hcert⟩
    exact ⟨q, p, hq, hp, hcop, hpC, hord, hN, hguard⟩

/-- **Complete conditional closure of Erdős #249.**  Cofinal
cyclotomic-anchored discrepancy kills contradict every eventual rational
period, because rational periods remain periods after multiplication. -/
theorem irrational_totient_series_of_cyclotomicAnchoredKillSupply
    {C : ℕ → ℕ}
    (hsupply : CyclotomicAnchoredKillSupply C) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨h, hh, N₀, hperiod⟩ :=
    eventual_period_of_not_irrational hrat
  obtain ⟨q, p, L, hq, hp, hcop, hpC, hord, hN, hcert⟩ :=
    hsupply h hh N₀
  have hint :
      totientTail ((p - 1) + h * q) - totientTail (p - 1) ∈
        Set.range ((↑) : ℤ → ℝ) :=
    tail_diff_int_of_period_mul hperiod q (p - 1) hN
  exact tail_diff_notMem_int_of_certifiedKill hcert hint

/-- Under clean anchor supply, irrationality itself repopulates the
cyclotomic anchored-kill fields by pointwise certificate completeness. -/
theorem cyclotomicAnchoredKillSupply_of_irrational_of_cleanAnchorSupply
    {C : ℕ → ℕ}
    (hclean : CleanCyclotomicAnchorSupply C)
    (hirr : Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    CyclotomicAnchoredKillSupply C := by
  intro h hh N₀
  obtain ⟨q, p, hq, hp, hcop, hpC, hord, hN⟩ :=
    hclean h hh N₀
  obtain ⟨L, hcert⟩ :=
    (irrational_totient_series_iff_pointwise_certificates.mp hirr)
      (h * q) (Nat.mul_pos hh hq.pos) (p - 1)
  exact ⟨q, p, L, hq, hp, hcop, hpC, hord, hN, hcert⟩

/-- Once clean anchors are present, the anchored-kill supply is equivalent
to Erdős #249 itself.  Thus prime production is completely discharged and
the remaining content is exactly terminal anti-locking of the totient word. -/
theorem cyclotomicAnchoredKillSupply_iff_irrational_of_cleanAnchorSupply
    {C : ℕ → ℕ}
    (hclean : CleanCyclotomicAnchorSupply C) :
    CyclotomicAnchoredKillSupply C ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  constructor
  · exact irrational_totient_series_of_cyclotomicAnchoredKillSupply
  · exact cyclotomicAnchoredKillSupply_of_irrational_of_cleanAnchorSupply
      hclean

/-- Exact claim ceiling for the concrete layers `|Φ_n(2)|`. -/
theorem binaryCyclotomicAnchoredKillSupply_iff_irrational :
    CyclotomicAnchoredKillSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  cyclotomicAnchoredKillSupply_iff_irrational_of_cleanAnchorSupply
    cleanCyclotomicAnchorSupply_binaryCyclotomicLayer

/-- **Guard-cylinder closure of Erdős #249.**  It suffices to force, at
cofinally remote clean cyclotomic anchors, either the terminal socket or the
mixed two-bit guard from the exact certificate normal form. -/
theorem irrational_totient_series_of_cyclotomicGuardCylinderSupply
    {C : ℕ → ℕ}
    (hsupply : CyclotomicGuardCylinderSupply C) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_cyclotomicAnchoredKillSupply
    (cyclotomicGuardCylinderSupply_iff_anchoredKillSupply.mp hsupply)

/-- Exact guard-cylinder claim ceiling for the concrete binary cyclotomic
layers. -/
theorem binaryCyclotomicGuardCylinderSupply_iff_irrational :
    CyclotomicGuardCylinderSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  rw [cyclotomicGuardCylinderSupply_iff_anchoredKillSupply]
  exact binaryCyclotomicAnchoredKillSupply_iff_irrational

set_option maxRecDepth 100000

/-- The natural `331`-layer certificate at period `30` and start `300`.
Its exact discrepancy is `385374`, with residue `350` modulo `8192` and
certificate radius `345`. -/
theorem certifiedKill_cyclotomic_30_331_natural :
    certifiedKill 30 (331 - 30 - 1) 13 := by
  decide

/-- The prime-anchored `331` certificate at period `30` and start `330`.
Its exact discrepancy is `10864`, with residue `624` modulo `1024` and
certificate radius `372`. -/
theorem certifiedKill_cyclotomic_30_331_anchor :
    certifiedKill 30 (331 - 1) 10 := by
  decide

/-- At the deeper phase-comparison depth `16`, the same natural anchor has
residue `2928` modulo `65536`.  This is the exact finite datum behind the
strict-`9/10` non-implication calculation in the packet. -/
theorem windowDiscrepancy_30_300_16_mod :
    windowDiscrepancy 30 300 16 % 2 ^ 16 = 2928 := by
  decide

/-- Exact denominator exclusion delivered by the natural `331` certificate:
the binary totient series equals no rational whose denominator divides
`2^300 * (2^30 - 1)`. -/
theorem totient_series_ne_rat_of_den_dvd_30_300
    (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 300 * (2 ^ 30 - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := by
  intro hS
  exact tail_diff_notMem_int_of_certifiedKill
    certifiedKill_cyclotomic_30_331_natural
    (tail_diff_int_of_den_dvd r hS 30 300 hdvd)

#print axioms prime_index_dvd_pred
#print axioms mersenneLayer_unboundedPrimeDivisorSupply
#print axioms exists_clean_binaryCyclotomicAnchor
#print axioms cleanCyclotomicAnchorSupply_binaryCyclotomicLayer
#print axioms exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
#print axioms tail_diff_int_of_period_mul
#print axioms exists_int_scaled_tail_of_rat_den_dvd
#print axioms fullMersenneBlockResidue_succ
#print axioms fullMersenneBlockCenteredLift_succ_modEq
#print axioms fullMersenneCenteredResidueGap_iff_abs_centeredLift
#print axioms fullMersenneBlockCenteredLift_succ_eq_of_two_edge_locks
#print axioms fullMersenneBlockCenteredLift_add_eq_carryOrbit_of_edge_locks
#print axioms exists_fullMersenneCenteredResidueGap_of_carryOrbit_escape
#print axioms exists_fullMersenneCenteredResidueGap_of_survivorKill
#print axioms survivorKill_of_certifiedKill
#print axioms exists_fullMersenneCenteredResidueGap_of_certifiedKill
#print axioms totient_series_ne_rat_of_fullMersenneCanonicalBasepointResidueGap_of_den_dvd
#print axioms totient_series_ne_rat_of_fullMersenneCanonicalBasepointResidueGap
#print axioms exists_fullMersenneInitialResidueGap_at_of_irrational
#print axioms fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational
#print axioms cyclotomicGuardCylinderSupply_iff_anchoredKillSupply
#print axioms irrational_totient_series_of_cyclotomicAnchoredKillSupply
#print axioms irrational_totient_series_of_cyclotomicGuardCylinderSupply
#print axioms binaryCyclotomicGuardCylinderSupply_iff_irrational
#print axioms certifiedKill_cyclotomic_30_331_natural
#print axioms certifiedKill_cyclotomic_30_331_anchor
#print axioms windowDiscrepancy_30_300_16_mod
#print axioms totient_series_ne_rat_of_den_dvd_30_300

end ErdosProblems.Erdos249.CyclotomicAnchoredKill
