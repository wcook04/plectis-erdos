import Erdos257PeriodNoncollapse.GreedyAchievementSet
import Erdos257PeriodNoncollapse.HalfCutLocator
import Erdos257PeriodNoncollapse.RationalSupportCarrySkeleton

/-!
# Dyadic prefix compression

This module owns the corrected transport from a reduced finite Mersenne prefix to the residual
support fraction and its wrap-ratio bound.
The reusable core is stated for an arbitrary finite positive fragment, not
only for an initial segment.

No novelty or priority claim is made for the statements in this file.  Nothing here proves or
refutes the universal Erdős #257 problem.
-/

namespace Erdos257PeriodNoncollapse

open Set

/-! ## Pure reduced-denominator transport -/

/-- Integer residual numerator.  This is the algebraically natural core:
unlike the interface natural specialization below, it needs no ordering
hypothesis on the subtraction. -/
def dyadicResidualIntNumerator (p r : ℤ) (c D : ℕ) : ℤ :=
  p * (D : ℤ) - ((2 ^ c : ℕ) : ℤ) * r

/-- Integer displayed residual normalized by `Rat.divInt`. -/
def dyadicResidualIntRat (p r : ℤ) (c D : ℕ) : ℚ :=
  Rat.divInt (dyadicResidualIntNumerator p r c D) (((2 ^ c * D : ℕ) : ℤ))

/-- The decisive congruence argument in `ℤ`: adding the multiple `pD` to
`-2^c r` preserves coprimality with the odd modulus `D`. -/
theorem dyadicResidualIntNumerator_coprime_oddDenominator
    (p r : ℤ) (c D : ℕ) (hDodd : Odd D)
    (hrD : r.natAbs.Coprime D) :
    (dyadicResidualIntNumerator p r c D).natAbs.Coprime D := by
  have hpowDnat : Nat.Coprime (2 ^ c) D :=
    (Nat.coprime_two_left.mpr hDodd).pow_left c
  have hpowDint : IsCoprime (((2 ^ c : ℕ) : ℤ)) (D : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hpowDnat
  have hrDint : IsCoprime r (D : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hrD
  have hprod : IsCoprime (((2 ^ c : ℕ) : ℤ) * r) (D : ℤ) :=
    hpowDint.mul_left hrDint
  have hadd := hprod.neg_left.add_mul_left_left p
  rw [Int.isCoprime_iff_nat_coprime] at hadd
  simpa only [dyadicResidualIntNumerator, sub_eq_add_neg, mul_comm, add_comm]
    using hadd

/-- Integer form of the exact denominator sandwich.  It works for positive,
zero, or negative displayed residual numerators once coprimality with `D` is
known. -/
theorem dyadicResidualInt_denominator_sandwich
    (p r : ℤ) (c D : ℕ) (hDpos : 0 < D)
    (hND : (dyadicResidualIntNumerator p r c D).natAbs.Coprime D) :
    D ∣ (dyadicResidualIntRat p r c D).den ∧
      (dyadicResidualIntRat p r c D).den ∣ 2 ^ c * D := by
  let N : ℤ := dyadicResidualIntNumerator p r c D
  let P : ℕ := 2 ^ c
  let B : ℕ := P * D
  let g : ℕ := ((B : ℤ)).gcd N
  have hPpos : 0 < P := by simp [P]
  have hBpos : 0 < B := Nat.mul_pos hPpos hDpos
  have hBne : (B : ℤ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hden : (dyadicResidualIntRat p r c D).den = B / g := by
    rw [dyadicResidualIntRat, Rat.den_divInt, if_neg hBne]
    simp only [Int.natAbs_natCast]
    rfl
  have hgB : g ∣ B := Int.gcd_dvd_natAbs_left (B : ℤ) N
  have hgN : g ∣ N.natAbs := Int.gcd_dvd_natAbs_right (B : ℤ) N
  have hgD : g.Coprime D := hND.coprime_dvd_left (by simpa [N] using hgN)
  have hgP : g ∣ P := (hgD.dvd_mul_right).mp (by simpa [B] using hgB)
  change D ∣ (dyadicResidualIntRat p r c D).den ∧
    (dyadicResidualIntRat p r c D).den ∣ B
  rw [hden]
  constructor
  · refine ⟨P / g, ?_⟩
    simpa [B, Nat.mul_comm] using (Nat.mul_div_assoc D hgP)
  · exact Nat.div_dvd_of_dvd hgB

/-- Numerator left after subtracting a reduced finite prefix `r / D` from a
dyadic rational `p / 2^c`.  The transport theorem below assumes the
subtraction is nonnegative, so natural subtraction is exact. -/
def dyadicResidualNumerator (p r c D : ℕ) : ℕ :=
  p * D - 2 ^ c * r

/-- The displayed residual rational before its remaining power-of-two
cancellation is normalized by `Rat`. -/
def dyadicResidualRat (p r c D : ℕ) : ℚ :=
  (dyadicResidualNumerator p r c D : ℚ) / (2 ^ c * D : ℕ)

/-- Subtracting a reduced odd-denominator fraction from a dyadic fraction
cannot cancel any factor of the odd denominator. -/
theorem dyadicResidualNumerator_coprime_oddDenominator
    (p r c D : ℕ) (hDodd : Odd D) (hrD : r.Coprime D)
    (hle : 2 ^ c * r ≤ p * D) :
    (dyadicResidualNumerator p r c D).Coprime D := by
  let N := dyadicResidualNumerator p r c D
  have hpow : (2 ^ c).Coprime D :=
    (Nat.coprime_two_left.mpr hDodd).pow_left c
  have hscaled : (2 ^ c * r).Coprime D := hpow.mul_left hrD
  show Nat.gcd N D = 1
  have hgN : Nat.gcd N D ∣ N := Nat.gcd_dvd_left N D
  have hgD : Nat.gcd N D ∣ D := Nat.gcd_dvd_right N D
  have hgPD : Nat.gcd N D ∣ p * D := dvd_mul_of_dvd_right hgD p
  have hgscaled : Nat.gcd N D ∣ 2 ^ c * r := by
    have hsub := Nat.dvd_sub hgPD hgN
    simpa [N, dyadicResidualNumerator, Nat.sub_sub_self hle] using hsub
  exact Nat.eq_one_of_dvd_coprimes hscaled hgscaled hgD

/-- Exact denominator sandwich.  If `Q` is the normalized denominator of the
residual, then `D ∣ Q ∣ 2^c D`.  This is the division-free statement that the
odd part inherited from the finite prefix is exactly `D`. -/
theorem dyadicResidual_denominator_sandwich
    (p r c D : ℕ) (hDpos : 0 < D) (hDodd : Odd D)
    (hrD : r.Coprime D) (hle : 2 ^ c * r ≤ p * D) :
    D ∣ (dyadicResidualRat p r c D).den ∧
      (dyadicResidualRat p r c D).den ∣ 2 ^ c * D := by
  let N := dyadicResidualNumerator p r c D
  let P := 2 ^ c
  let T := P * D
  let g := Nat.gcd N T
  have hTpos : 0 < T := mul_pos (pow_pos (by omega) c) hDpos
  have hden : (dyadicResidualRat p r c D).den = T / g := by
    simpa [dyadicResidualRat, N, P, T, g] using
      den_natCast_div_natCast N T hTpos.ne'
  have hND : N.Coprime D := by
    simpa [N] using
      dyadicResidualNumerator_coprime_oddDenominator p r c D hDodd hrD hle
  have hgN : g ∣ N := by
    exact Nat.gcd_dvd_left N T
  have hgT : g ∣ T := by
    exact Nat.gcd_dvd_right N T
  have hgD : g.Coprime D := Nat.Coprime.coprime_dvd_left hgN hND
  have hgP : g ∣ P := by
    exact (hgD.dvd_mul_right).mp (by simpa [T] using hgT)
  rw [hden]
  constructor
  · refine ⟨P / g, ?_⟩
    rw [show T = D * P by simp [T, mul_comm], Nat.mul_div_assoc D hgP]
  · exact ⟨g, by simpa [T] using (Nat.div_mul_cancel hgT).symm⟩

/-! ## Exact skipped-rank numerator for the greedy half orbit -/

/-- For a displayed residual `p / (2L)`, the integer numerator of its
excess above the next dyadic point `2^-(n+1)`.  Indeed,

`p/(2L) - 2^-(n+1) = E/(2^(n+1)L)`.

Keeping `E` integral makes the unresolved skipped-branch comparison an
exact Diophantine inequality rather than a real-valued phase estimate. -/
def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)

/-- With displayed numerator and denominator fixed across one skipped rank,
the next dyadic excess doubles and receives one denominator increment. -/
theorem nextDyadicExcessIntNumerator_succ (p : ℤ) (n L : ℕ) :
    nextDyadicExcessIntNumerator p (n + 1) L =
      2 * nextDyadicExcessIntNumerator p n L + (L : ℤ) := by
  simp only [nextDyadicExcessIntNumerator, pow_succ]
  push_cast
  ring

/-- Closed form of the unchanged-denominator skip-run recurrence. -/
theorem nextDyadicExcessIntNumerator_add (p : ℤ) (n k L : ℕ) :
    nextDyadicExcessIntNumerator p (n + k) L =
      (((2 ^ k : ℕ) : ℤ) * nextDyadicExcessIntNumerator p n L) +
        ((((2 ^ k : ℕ) : ℤ) - 1) * (L : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega,
        nextDyadicExcessIntNumerator_succ, ih]
      simp only [pow_succ]
      push_cast
      ring

/-- Exact rational identity represented by `nextDyadicExcessIntNumerator`. -/
theorem divInt_sub_nextDyadic_eq_excess_divInt
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    Rat.divInt p ((2 * L : ℕ) : ℤ) - (1 / (2 : ℚ) ^ (n + 1)) =
      Rat.divInt (nextDyadicExcessIntNumerator p n L)
        (((2 ^ (n + 1) * L : ℕ) : ℤ)) := by
  have htwoL : ((2 * L : ℕ) : ℤ) ≠ 0 := by positivity
  have hpowL : ((2 ^ (n + 1) * L : ℕ) : ℤ) ≠ 0 := by positivity
  rw [Rat.divInt_eq_div, Rat.divInt_eq_div]
  field_simp [htwoL, hpowL]
  simp only [nextDyadicExcessIntNumerator, pow_succ]
  push_cast
  ring

/-- The displayed residual is on the dyadic-safe side exactly when its
integer excess numerator is nonpositive. -/
theorem divInt_le_nextDyadic_iff_excess_nonpos
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    Rat.divInt p ((2 * L : ℕ) : ℤ) ≤ 1 / (2 : ℚ) ^ (n + 1) ↔
      nextDyadicExcessIntNumerator p n L ≤ 0 := by
  rw [← sub_nonpos, divInt_sub_nextDyadic_eq_excess_divInt p n L hL]
  rw [Rat.divInt_eq_div]
  have hden : (0 : ℚ) < (((2 ^ (n + 1) * L : ℕ) : ℤ) : ℚ) := by
    positivity
  rw [div_le_iff₀ hden, zero_mul]
  norm_cast

/-- At the prospective rank `n+1`, selection of the Mersenne weight is the
complementary exact inequality `p ≤ 2E`.  Together with the dyadic sign test,
this identifies the entire forbidden sliver using one integer numerator. -/
theorem mersenneWeightRat_succ_le_divInt_iff_excess
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    mersenneWeightRat (n + 1) ≤ Rat.divInt p ((2 * L : ℕ) : ℤ) ↔
      p ≤ 2 * nextDyadicExcessIntNumerator p n L := by
  have hq : (0 : ℚ) < (2 : ℚ) ^ (n + 1) - 1 := by
    have hone : (1 : ℚ) < 2 ^ (n + 1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hden : (0 : ℚ) < ((((2 * L : ℕ) : ℤ)) : ℚ) := by
    positivity
  unfold mersenneWeightRat
  rw [Rat.divInt_eq_div, div_le_div_iff₀ hq hden]
  simp only [one_mul]
  have hid :
      2 * nextDyadicExcessIntNumerator p n L - p =
        p * (((2 ^ (n + 1) : ℕ) : ℤ) - 1) - ((2 * L : ℕ) : ℤ) := by
    simp only [nextDyadicExcessIntNumerator]
    push_cast
    rw [pow_succ]
    ring
  constructor
  · intro h
    have hz : ((2 * L : ℕ) : ℤ) ≤
        p * (((2 ^ (n + 1) : ℕ) : ℤ) - 1) := by
      exact_mod_cast h
    have hz0 : 0 ≤
        p * (((2 ^ (n + 1) : ℕ) : ℤ) - 1) - ((2 * L : ℕ) : ℤ) :=
      sub_nonneg.mpr hz
    rw [← hid] at hz0
    omega
  · intro h
    have hz0 : 0 ≤ 2 * nextDyadicExcessIntNumerator p n L - p := by
      omega
    rw [hid] at hz0
    have hz : ((2 * L : ℕ) : ℤ) ≤
        p * (((2 ^ (n + 1) : ℕ) : ℤ) - 1) := sub_nonneg.mp hz0
    exact_mod_cast hz

/-- A skipped prospective rank is exactly the strict complementary excess
inequality `2E < p`. -/
theorem divInt_lt_mersenneWeightRat_succ_iff_excess
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    Rat.divInt p ((2 * L : ℕ) : ℤ) < mersenneWeightRat (n + 1) ↔
      2 * nextDyadicExcessIntNumerator p n L < p := by
  simpa only [not_le] using
    not_congr (mersenneWeightRat_succ_le_divInt_iff_excess p n L hL)

/-- Exact forbidden-sliver classifier for a displayed residual.  A skipped
rank is dyadically unsafe precisely in the finite integer window
`0 < E` and `2E < p`. -/
theorem divInt_mem_nextMersenneDyadicSliver_iff_excess
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    (1 / (2 : ℚ) ^ (n + 1) < Rat.divInt p ((2 * L : ℕ) : ℤ) ∧
        Rat.divInt p ((2 * L : ℕ) : ℤ) < mersenneWeightRat (n + 1)) ↔
      (0 < nextDyadicExcessIntNumerator p n L ∧
        2 * nextDyadicExcessIntNumerator p n L < p) := by
  have hdyadic :
      1 / (2 : ℚ) ^ (n + 1) < Rat.divInt p ((2 * L : ℕ) : ℤ) ↔
        0 < nextDyadicExcessIntNumerator p n L := by
    simpa only [not_le] using
      not_congr (divInt_le_nextDyadic_iff_excess_nonpos p n L hL)
  rw [hdyadic, divInt_lt_mersenneWeightRat_succ_iff_excess p n L hL]

/-! ## GCD-free compression between taken ranks -/

/-- The cross-multiplied defect at prospective rank `n+1`. -/
def nextMersenneDecisionDefect (p : ℤ) (n L : ℕ) : ℤ :=
  p * ((((2 ^ (n + 1) : ℕ) : ℤ)) - 1) - 2 * (L : ℤ)

/-- The decision defect is exactly `2E-p`. -/
theorem nextMersenneDecisionDefect_eq_two_excess_sub
    (p : ℤ) (n L : ℕ) :
    nextMersenneDecisionDefect p n L =
      2 * nextDyadicExcessIntNumerator p n L - p := by
  simp only [nextMersenneDecisionDefect,
    nextDyadicExcessIntNumerator, pow_succ]
  push_cast
  ring

/-- A skipped decision is dyadically safe exactly when its raw defect is at
least one full displayed numerator below zero. -/
theorem nextMersenneDecisionDefect_le_neg_iff_excess_nonpos
    (p : ℤ) (n L : ℕ) :
    nextMersenneDecisionDefect p n L ≤ -p ↔
      nextDyadicExcessIntNumerator p n L ≤ 0 := by
  rw [nextMersenneDecisionDefect_eq_two_excess_sub]
  omega

/-- The strengthened taken branch `E ≥ p` is the symmetric unit-margin
condition on the positive raw defect. -/
theorem le_nextMersenneDecisionDefect_iff_le_excess
    (p : ℤ) (n L : ℕ) :
    p ≤ nextMersenneDecisionDefect p n L ↔
      p ≤ nextDyadicExcessIntNumerator p n L := by
  rw [nextMersenneDecisionDefect_eq_two_excess_sub]
  omega

/-- The unresolved unsafe-skip window is the open unit neighbourhood below
the Mersenne threshold, expressed without division. -/
theorem nextMersenneDecisionDefect_mem_neg_unit_window_iff
    (p : ℤ) (n L : ℕ) :
    (-p < nextMersenneDecisionDefect p n L ∧
        nextMersenneDecisionDefect p n L < 0) ↔
      (0 < nextDyadicExcessIntNumerator p n L ∧
        2 * nextDyadicExcessIntNumerator p n L < p) := by
  rw [nextMersenneDecisionDefect_eq_two_excess_sub]
  omega

/-- The Mersenne term at rank `k` is taken by the displayed residual
`p/(2D)`, in cross-multiplied natural coordinates. -/
def BlockTakeAt (p D k : ℕ) : Prop :=
  2 * D ≤ p * (2 ^ k - 1)

/-- The displayed residual lies below the dyadic skeleton `2^-k`. -/
def BlockDyadicSafeAt (p D k : ℕ) : Prop :=
  p * 2 ^ k ≤ 2 * D

/-- `b` is the first taken rank strictly after `a`. -/
def IsFirstBlockTakeAfter (p D a b : ℕ) : Prop :=
  a < b ∧ BlockTakeAt p D b ∧
    ∀ k : ℕ, a < k → k < b → ¬ BlockTakeAt p D k

/-- Over a constant-residual skip block, dyadic safety is monotone in the
rank.  Hence every intermediate skip is safe iff either the block is empty
or its last rank is safe. -/
theorem all_intermediate_BlockDyadicSafeAt_iff_last
    (p D a b : ℕ) (hab : a < b) :
    (∀ k : ℕ, a < k → k < b → BlockDyadicSafeAt p D k) ↔
      b = a + 1 ∨ BlockDyadicSafeAt p D (b - 1) := by
  constructor
  · intro hall
    by_cases hadj : b = a + 1
    · exact Or.inl hadj
    · right
      apply hall (b - 1) <;> omega
  · rintro (hadj | hlast) k hak hkb
    · omega
    · unfold BlockDyadicSafeAt at hlast ⊢
      have hk : k ≤ b - 1 := by omega
      have hpow : 2 ^ k ≤ 2 ^ (b - 1) :=
        Nat.pow_le_pow_right (by omega) hk
      exact (Nat.mul_le_mul_left p hpow).trans hlast

/-- Minimality of a non-adjacent next take supplies only the open Mersenne
predecessor bound.  The missing skip-sign theorem must strengthen this by
exactly one unit, from `2^(b-1)-1` to `2^(b-1)`. -/
theorem firstBlockTake_predecessor_open_bound
    {p D a b : ℕ} (hfirst : IsFirstBlockTakeAfter p D a b)
    (hgap : a + 1 < b) :
    p * (2 ^ (b - 1) - 1) < 2 * D := by
  have hskip := hfirst.2.2 (b - 1) (by omega) (by omega)
  simpa only [BlockTakeAt, not_le] using hskip

/-- Exact block compression under the first-take hypothesis. -/
theorem firstBlockTake_all_skips_safe_iff_last_margin
    {p D a b : ℕ} (hfirst : IsFirstBlockTakeAfter p D a b) :
    (∀ k : ℕ, a < k → k < b → BlockDyadicSafeAt p D k) ↔
      b = a + 1 ∨ p * 2 ^ (b - 1) ≤ 2 * D := by
  rw [all_intermediate_BlockDyadicSafeAt_iff_last p D a b hfirst.1]
  rfl

/-! ### Cancellation-free transport to the next taken block -/

/-- Raw positive numerator produced by taking rank `b`. -/
def rawTakenResidualNumerator (p D b : ℕ) : ℕ :=
  p * (2 ^ b - 1) - 2 * D

/-- Raw odd-denominator coordinate produced by taking rank `b`. -/
def rawTakenResidualDenominator (D b : ℕ) : ℕ :=
  D * (2 ^ b - 1)

/-- A common positive reduction factor cancels out of the next take test. -/
theorem blockTakeAt_commonFactor_iff
    {H B g p D k : ℕ} (hg : 0 < g)
    (hH : H = g * p) (hB : B = g * D) :
    BlockTakeAt p D k ↔ BlockTakeAt H B k := by
  unfold BlockTakeAt
  constructor
  · intro h
    calc
      2 * B = g * (2 * D) := by rw [hB]; ring
      _ ≤ g * (p * (2 ^ k - 1)) := Nat.mul_le_mul_left g h
      _ = H * (2 ^ k - 1) := by rw [hH]; ring
  · intro h
    have hscaled : g * (2 * D) ≤ g * (p * (2 ^ k - 1)) := by
      calc
        g * (2 * D) = 2 * (g * D) := by ring
        _ ≤ (g * p) * (2 ^ k - 1) := by
          simpa only [hH, hB] using h
        _ = g * (p * (2 ^ k - 1)) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled hg

/-- The same common factor cancels out of the dyadic-safe margin. -/
theorem blockDyadicSafeAt_commonFactor_iff
    {H B g p D k : ℕ} (hg : 0 < g)
    (hH : H = g * p) (hB : B = g * D) :
    BlockDyadicSafeAt p D k ↔ BlockDyadicSafeAt H B k := by
  unfold BlockDyadicSafeAt
  constructor
  · intro h
    calc
      H * 2 ^ k = g * (p * 2 ^ k) := by rw [hH]; ring
      _ ≤ g * (2 * D) := Nat.mul_le_mul_left g h
      _ = 2 * B := by rw [hB]; ring
  · intro h
    have hscaled : g * (p * 2 ^ k) ≤ g * (2 * D) := by
      calc
        g * (p * 2 ^ k) = (g * p) * 2 ^ k := by ring
        _ ≤ 2 * (g * D) := by
          simpa only [hH, hB] using h
        _ = g * (2 * D) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled hg

/-- A common reduction factor therefore also cancels out of the identity of
the next taken rank. -/
theorem firstBlockTakeAfter_commonFactor_iff
    {H B g p D a b : ℕ} (hg : 0 < g)
    (hH : H = g * p) (hB : B = g * D) :
    IsFirstBlockTakeAfter p D a b ↔
      IsFirstBlockTakeAfter H B a b := by
  unfold IsFirstBlockTakeAfter
  constructor
  · rintro ⟨hab, htake, hskip⟩
    refine ⟨hab, (blockTakeAt_commonFactor_iff hg hH hB).1 htake, ?_⟩
    intro k hak hkb
    exact fun h ↦ hskip k hak hkb
      ((blockTakeAt_commonFactor_iff hg hH hB).2 h)
  · rintro ⟨hab, htake, hskip⟩
    refine ⟨hab, (blockTakeAt_commonFactor_iff hg hH hB).2 htake, ?_⟩
    intro k hak hkb
    exact fun h ↦ hskip k hak hkb
      ((blockTakeAt_commonFactor_iff hg hH hB).1 h)

/-- **GCD-free taken-block reduction.**  Suppose taking rank `b` creates raw
coordinates `(H,B)`, and reducing them by any positive common factor gives
the next displayed state `(p',D')`.  If `c` is its next taken rank, all
intervening skips are dyadically safe iff either there are no intervening
skips or the single raw inequality `H*2^(c-1) ≤ 2B` holds.  No gcd or
cancellation factor remains in the proof obligation. -/
theorem reduced_nextBlock_all_skips_safe_iff_gcdFree
    {b H B g p' D' c : ℕ}
    (hg : 0 < g) (hHred : H = g * p') (hBred : B = g * D')
    (hfirst : IsFirstBlockTakeAfter p' D' b c) :
    (∀ k : ℕ, b < k → k < c → BlockDyadicSafeAt p' D' k) ↔
      c = b + 1 ∨ H * 2 ^ (c - 1) ≤ 2 * B := by
  have hbase := firstBlockTake_all_skips_safe_iff_last_margin hfirst
  rw [hbase]
  apply or_congr Iff.rfl
  exact blockDyadicSafeAt_commonFactor_iff hg hHred hBred

/-- Expanded form of the raw gcd-free margin after taking rank `b`. -/
theorem reduced_nextBlock_gcdFree_margin_expanded
    {p D b H B c : ℕ}
    (hHraw : H = rawTakenResidualNumerator p D b)
    (hBraw : B = rawTakenResidualDenominator D b) :
    (H * 2 ^ (c - 1) ≤ 2 * B) ↔
      (p * (2 ^ b - 1) - 2 * D) * 2 ^ (c - 1) ≤
        2 * (D * (2 ^ b - 1)) := by
  simp only [hHraw, hBraw, rawTakenResidualNumerator,
    rawTakenResidualDenominator]

/-- Direct source-state form: the reduced next residual may have arbitrary
positive cancellation, but the complete intervening-skip obligation is the
single raw inequality displayed on the right. -/
theorem takenBlock_all_next_skips_safe_iff_raw_margin
    {p D b g p' D' c : ℕ} (hg : 0 < g)
    (hnum : rawTakenResidualNumerator p D b = g * p')
    (hden : rawTakenResidualDenominator D b = g * D')
    (hfirst : IsFirstBlockTakeAfter p' D' b c) :
    (∀ k : ℕ, b < k → k < c → BlockDyadicSafeAt p' D' k) ↔
      c = b + 1 ∨
        (p * (2 ^ b - 1) - 2 * D) * 2 ^ (c - 1) ≤
          2 * (D * (2 ^ b - 1)) := by
  have h := reduced_nextBlock_all_skips_safe_iff_gcdFree
    hg hnum hden hfirst
  simpa only [rawTakenResidualNumerator,
    rawTakenResidualDenominator] using h

/-! ### Exact reciprocal-floor obstruction -/

/-- The block margin is automatically inductive across an adjacent pair of
takes.  If the state before taking `b` was safe at its predecessor dyadic
scale, the raw state after the take is safe at scale `b`.  Thus only
nonadjacent successor blocks require new orbit arithmetic. -/
theorem rawTakenResidual_adjacent_margin_of_predecessor_safe
    {p D b : ℕ} (hb : 0 < b)
    (hsafe : BlockDyadicSafeAt p D (b - 1))
    (htake : BlockTakeAt p D b) :
    rawTakenResidualNumerator p D b * 2 ^ b ≤
      2 * rawTakenResidualDenominator D b := by
  let P := 2 ^ (b - 1)
  let q := 2 ^ b - 1
  let H := p * q - 2 * D
  have hpow : 2 ^ b = 2 * P := by
    rw [show b = (b - 1) + 1 by omega, pow_succ]
    simp only [P, Nat.mul_comm]
  have hq : q = 2 * P - 1 := by
    dsimp only [q]
    rw [hpow]
  have htake' : 2 * D ≤ p * q := by
    simpa only [BlockTakeAt, q] using htake
  have hHadd : H + 2 * D = p * q := Nat.sub_add_cancel htake'
  have hsafe' : p * P ≤ 2 * D := by
    simpa only [BlockDyadicSafeAt, P] using hsafe
  have hscaled := Nat.mul_le_mul_left (2 * q) hsafe'
  have hsum : H * (2 * P) + (2 * D) * (2 * P) ≤
      (2 * D * q) + (2 * D * q) := by
    calc
      H * (2 * P) + (2 * D) * (2 * P) =
          (H + 2 * D) * (2 * P) := by ring
      _ = (p * q) * (2 * P) := by rw [hHadd]
      _ = (2 * q) * (p * P) := by ring
      _ ≤ (2 * q) * (2 * D) := hscaled
      _ = (2 * D * q) + (2 * D * q) := by ring
  have hqle : q ≤ 2 * P := by rw [hq]; omega
  have hden : 2 * D * q ≤ (2 * D) * (2 * P) := by
    exact Nat.mul_le_mul_left (2 * D) hqle
  have hsum' : H * (2 * P) + (2 * D * q) ≤
      (2 * D * q) + (2 * D * q) :=
    (Nat.add_le_add_left hden (H * (2 * P))).trans hsum
  have hmargin : H * (2 * P) ≤ 2 * D * q := by
    apply Nat.le_of_add_le_add_right
    simpa only [Nat.add_comm] using hsum'
  change H * 2 ^ b ≤ 2 * (D * q)
  rw [hpow]
  calc
    H * (2 * P) ≤ 2 * D * q := hmargin
    _ = 2 * (D * q) := by ring

/-- At a nonadjacent first-take block, the missing dyadic margin is exactly
avoidance of the lower Mersenne value by the integer part of the reciprocal
residual. -/
theorem firstBlockTake_margin_iff_reciprocalFloor_ne_mersenne
    {p D a b : ℕ} (hp : 0 < p)
    (hfirst : IsFirstBlockTakeAfter p D a b)
    (hgap : a + 1 < b) :
    BlockDyadicSafeAt p D (b - 1) ↔
      (2 * D) / p ≠ 2 ^ (b - 1) - 1 := by
  have hskip : ¬ BlockTakeAt p D (b - 1) :=
    hfirst.2.2 (b - 1) (by omega) (by omega)
  have hlower : p * (2 ^ (b - 1) - 1) < 2 * D := by
    simpa only [BlockTakeAt, not_le] using hskip
  have hfloorLower : 2 ^ (b - 1) - 1 ≤ (2 * D) / p := by
    exact (Nat.le_div_iff_mul_le hp).2 (by
      simpa only [Nat.mul_comm] using hlower.le)
  have hpowpos : 0 < 2 ^ (b - 1) := pow_pos (by omega) _
  have hqsucc : 2 ^ (b - 1) - 1 + 1 = 2 ^ (b - 1) :=
    Nat.sub_add_cancel hpowpos
  constructor
  · intro hsafe heq
    have hupper : 2 * D < p * ((2 * D) / p + 1) :=
      Nat.lt_mul_div_succ (2 * D) hp
    unfold BlockDyadicSafeAt at hsafe
    rw [heq, hqsucc] at hupper
    exact (not_lt_of_ge hsafe) hupper
  · intro hne
    unfold BlockDyadicSafeAt
    by_contra hbad
    have hfloorUpper : (2 * D) / p < 2 ^ (b - 1) := by
      apply (Nat.div_lt_iff_lt_mul hp).2
      simpa only [Nat.mul_comm] using (Nat.lt_of_not_ge hbad)
    apply hne
    omega

/-- Source-coordinate specialization of the same exact quotient obstruction.
All cancellation is absent: only the raw post-take numerator and denominator
enter the quotient. -/
theorem takenBlock_rawMargin_iff_reciprocalFloor_ne_mersenne
    {p D b c : ℕ}
    (hpos : 0 < rawTakenResidualNumerator p D b)
    (hfirst : IsFirstBlockTakeAfter
      (rawTakenResidualNumerator p D b)
      (rawTakenResidualDenominator D b) b c)
    (hgap : b + 1 < c) :
    ((p * (2 ^ b - 1) - 2 * D) * 2 ^ (c - 1) ≤
        2 * (D * (2 ^ b - 1))) ↔
      (2 * rawTakenResidualDenominator D b) /
          rawTakenResidualNumerator p D b ≠
        2 ^ (c - 1) - 1 := by
  simpa only [BlockDyadicSafeAt, rawTakenResidualNumerator,
    rawTakenResidualDenominator] using
      firstBlockTake_margin_iff_reciprocalFloor_ne_mersenne
        hpos hfirst hgap

/-- Cancellation-aware form matching an actual taken block.  The raw source
margin is equivalent to Mersenne-floor avoidance in the reduced post-take
state; the common reduction factor disappears from both sides. -/
theorem takenBlock_rawMargin_iff_reducedReciprocalFloor_ne_mersenne
    {p D b g p' D' c : ℕ}
    (hg : 0 < g) (hp' : 0 < p')
    (hnum : rawTakenResidualNumerator p D b = g * p')
    (hden : rawTakenResidualDenominator D b = g * D')
    (hfirst : IsFirstBlockTakeAfter p' D' b c)
    (hgap : b + 1 < c) :
    ((p * (2 ^ b - 1) - 2 * D) * 2 ^ (c - 1) ≤
        2 * (D * (2 ^ b - 1))) ↔
      (2 * D') / p' ≠ 2 ^ (c - 1) - 1 := by
  change BlockDyadicSafeAt
      (rawTakenResidualNumerator p D b)
      (rawTakenResidualDenominator D b) (c - 1) ↔ _
  exact
    (blockDyadicSafeAt_commonFactor_iff hg hnum hden).symm.trans
      (firstBlockTake_margin_iff_reciprocalFloor_ne_mersenne
        hp' hfirst hgap)

/-! ### Exact falsifiers for weaker inductive states -/

/-- Safe bracketing plus nondecrease of the displayed numerator is not an
inductive invariant.  The state `7/(2*17)` takes rank `3`, producing
`15/(2*119)`, but rank `4` is an unsafe skip with exact excess `1`. -/
theorem safeBracket_and_numeratorMonotone_not_inductive_fixture :
    BlockDyadicSafeAt 7 17 2 ∧
      BlockTakeAt 7 17 3 ∧
      rawTakenResidualNumerator 7 17 3 = 15 ∧
      rawTakenResidualDenominator 17 3 = 119 ∧
      7 ≤ 15 ∧
      ¬ BlockTakeAt 15 119 4 ∧
      ¬ BlockDyadicSafeAt 15 119 4 ∧
      nextDyadicExcessIntNumerator 15 3 119 = 1 ∧
      BlockTakeAt 15 119 5 := by
  norm_num [BlockDyadicSafeAt, BlockTakeAt,
    rawTakenResidualNumerator, rawTakenResidualDenominator,
    nextDyadicExcessIntNumerator]

/-- The denominator in the second fixture is already saturated by every
Mersenne denominator through rank `7`. -/
theorem mersenneLcm_through_seven_eq :
    Nat.lcm 3 (Nat.lcm 7 (Nat.lcm 15 (Nat.lcm 31 (Nat.lcm 63 127)))) =
      1240155 := by
  norm_num [Nat.lcm]

/-- Even full initial-LCM denominator saturation, safe current bracketing,
positive cancellation, and numerator increase do not make the block margin
inductive.  After the rank-`8` take, rank `10` is skipped but has exact
positive excess `1013`. -/
theorem lcmSaturated_safeBracket_not_inductive_fixture :
    BlockDyadicSafeAt 12149 1240155 7 ∧
      BlockTakeAt 12149 1240155 8 ∧
      rawTakenResidualNumerator 12149 1240155 8 = 15 * 41179 ∧
      rawTakenResidualDenominator 1240155 8 = 15 * 21082635 ∧
      12149 ≤ 41179 ∧
      ¬ BlockTakeAt 41179 21082635 9 ∧
      ¬ BlockTakeAt 41179 21082635 10 ∧
      ¬ BlockDyadicSafeAt 41179 21082635 10 ∧
      nextDyadicExcessIntNumerator 41179 9 21082635 = 1013 ∧
      BlockTakeAt 41179 21082635 11 := by
  norm_num [BlockDyadicSafeAt, BlockTakeAt,
    rawTakenResidualNumerator, rawTakenResidualDenominator,
    nextDyadicExcessIntNumerator]

/-- The two-channel cap at the next exponent is exactly one integer
inequality.  This is the division-free form

`3 * 2^(n+1) * E ≤ L`

for the displayed residual `p/(2L)`. -/
theorem divInt_le_nextTwoChannelCap_iff_excess
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    Rat.divInt p ((2 * L : ℕ) : ℤ) ≤
        (1 / (2 : ℚ)) ^ (n + 1) +
          (1 / 3 : ℚ) * (1 / 4 : ℚ) ^ (n + 1) ↔
      3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
          nextDyadicExcessIntNumerator p n L) ≤ (L : ℤ) := by
  let E : ℤ := nextDyadicExcessIntNumerator p n L
  have hden : ((3 * 4 ^ (n + 1) * L : ℕ) : ℤ) ≠ 0 := by positivity
  have hscaled :
      Rat.divInt E (((2 ^ (n + 1) * L : ℕ) : ℤ)) -
          (1 / 3 : ℚ) * (1 / 4 : ℚ) ^ (n + 1) =
        Rat.divInt
          (3 * (((2 ^ (n + 1) : ℕ) : ℤ) * E) - (L : ℤ))
          ((3 * 4 ^ (n + 1) * L : ℕ) : ℤ) := by
    have hleft : ((2 ^ (n + 1) * L : ℕ) : ℤ) ≠ 0 := by positivity
    have hfourNat : 4 ^ (n + 1) = 2 ^ (n + 1) * 2 ^ (n + 1) := by
      rw [← mul_pow]
      norm_num
    have hfourRat : (4 : ℚ) ^ (n + 1) =
        (2 : ℚ) ^ (n + 1) * (2 : ℚ) ^ (n + 1) := by
      rw [← mul_pow]
      norm_num
    rw [Rat.divInt_eq_div, Rat.divInt_eq_div]
    rw [div_pow, one_pow, hfourRat, hfourNat]
    field_simp [hleft, hden]
    push_cast
    ring
  rw [← sub_nonpos]
  have hid := divInt_sub_nextDyadic_eq_excess_divInt p n L hL
  rw [sub_add_eq_sub_sub, one_div_pow (2 : ℚ), hid]
  change Rat.divInt E (((2 ^ (n + 1) * L : ℕ) : ℤ)) -
      (1 / 3 : ℚ) * (1 / 4 : ℚ) ^ (n + 1) ≤ 0 ↔ _
  rw [hscaled, Rat.divInt_eq_div]
  have hdenpos : (0 : ℚ) < (((3 * 4 ^ (n + 1) * L : ℕ) : ℤ) : ℚ) := by
    positivity
  rw [div_le_iff₀ hdenpos, zero_mul]
  norm_cast
  dsimp [E]
  simp only [sub_nonpos]

/-- The exact finite greedy prefix used to display the half residual. -/
def halfGreedyPrefixRat (n : ℕ) : ℚ :=
  finiteErdosSum (greedyMersennePrefixRat (1 / 2 : ℚ) n) 2

/-- The inherited odd denominator of the exact finite greedy prefix. -/
def halfGreedyPrefixDenominator (n : ℕ) : ℕ :=
  (halfGreedyPrefixRat n).den

/-- Displayed numerator `p_n` in
`r_n = p_n / (2 * halfGreedyPrefixDenominator n)`. -/
def halfGreedyResidualDisplayedNumerator (n : ℕ) : ℤ :=
  (halfGreedyPrefixDenominator n : ℤ) -
    2 * (halfGreedyPrefixRat n).num

/-- The actual greedy half-orbit specialization of the integral excess
numerator.  At level `n`, it measures excess above `2^-(n+1)`. -/
def halfGreedyNextDyadicExcessNumerator (n : ℕ) : ℤ :=
  nextDyadicExcessIntNumerator
    (halfGreedyResidualDisplayedNumerator n) n
    (halfGreedyPrefixDenominator n)

/-- The rational greedy half residual has the exact displayed numerator and
odd prefix denominator above. -/
theorem greedyHalfRemainderRat_eq_displayed_divInt (n : ℕ) :
    greedyMersenneRemainderRat (1 / 2 : ℚ) n =
      Rat.divInt (halfGreedyResidualDisplayedNumerator n)
        ((2 * halfGreedyPrefixDenominator n : ℕ) : ℤ) := by
  rw [greedyMersenneRemainderRat_eq_sub_finiteErdosSum]
  change (1 / 2 : ℚ) - halfGreedyPrefixRat n = _
  rw [← Rat.num_div_den (halfGreedyPrefixRat n)]
  rw [Rat.divInt_eq_div]
  have hDNat : halfGreedyPrefixDenominator n ≠ 0 := by
    exact Rat.den_nz (halfGreedyPrefixRat n)
  have hD : ((halfGreedyPrefixDenominator n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hDNat
  have h2DNat : 2 * halfGreedyPrefixDenominator n ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) hDNat
  have h2D : (((2 * halfGreedyPrefixDenominator n : ℕ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast h2DNat
  field_simp [hD, h2D]
  simp only [halfGreedyResidualDisplayedNumerator,
    halfGreedyPrefixDenominator]
  push_cast
  ring

/-- The rational second-channel phase is exactly the dyadically scaled
integral excess divided by the inherited odd prefix denominator:

`φ_n = 2^n E_n / D_n`.

This is the missing coordinate bridge between the one-dimensional phase
dynamics and the reduced prefix lattice. -/
theorem greedyMersenneSecondChannelPhaseRat_eq_scaled_excess (n : ℕ) :
    greedyMersenneSecondChannelPhaseRat n =
      Rat.divInt
        (((2 ^ n : ℕ) : ℤ) *
          halfGreedyNextDyadicExcessNumerator n)
        (halfGreedyPrefixDenominator n : ℤ) := by
  rw [greedyMersenneSecondChannelPhaseRat_eq_scaled_remainder]
  rw [greedyHalfRemainderRat_eq_displayed_divInt]
  rw [Rat.divInt_eq_div, Rat.divInt_eq_div]
  have hDnat : halfGreedyPrefixDenominator n ≠ 0 :=
    Rat.den_nz (halfGreedyPrefixRat n)
  have hD : ((halfGreedyPrefixDenominator n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hDnat
  have hfour :
      (4 : ℚ) ^ n = (2 : ℚ) ^ (n * 2) := by
    calc
      (4 : ℚ) ^ n = ((2 : ℚ) ^ 2) ^ n := by norm_num
      _ = (2 : ℚ) ^ (2 * n) := by rw [pow_mul]
      _ = (2 : ℚ) ^ (n * 2) := by congr 1 <;> omega
  simp only [halfGreedyNextDyadicExcessNumerator,
    nextDyadicExcessIntNumerator]
  field_simp [hD]
  push_cast
  rw [hfour]
  ring

/-- Consequently, avoiding the open unit interval is a division-free integer
dichotomy.  On the positive branch it asks exactly for
`D_n ≤ 2^n E_n`; the nonpositive branch is simply `E_n ≤ 0`. -/
theorem secondChannelPhaseRat_outside_unit_iff_scaled_excess (n : ℕ) :
    (greedyMersenneSecondChannelPhaseRat n ≤ 0 ∨
        1 ≤ greedyMersenneSecondChannelPhaseRat n) ↔
      (halfGreedyNextDyadicExcessNumerator n ≤ 0 ∨
        (halfGreedyPrefixDenominator n : ℤ) ≤
          ((2 ^ n : ℕ) : ℤ) *
            halfGreedyNextDyadicExcessNumerator n) := by
  have hDposNat : 0 < halfGreedyPrefixDenominator n :=
    Rat.den_pos (halfGreedyPrefixRat n)
  have hDpos :
      (0 : ℚ) < ((halfGreedyPrefixDenominator n : ℤ) : ℚ) := by
    exact_mod_cast hDposNat
  rw [greedyMersenneSecondChannelPhaseRat_eq_scaled_excess,
    Rat.divInt_eq_div]
  constructor
  · rintro (hneg | hpos)
    · left
      have hnum :
          ((((2 ^ n : ℕ) : ℤ) *
              halfGreedyNextDyadicExcessNumerator n : ℤ) : ℚ) ≤ 0 := by
        have hcross := (div_le_iff₀ hDpos).mp hneg
        simpa using hcross
      have hnumInt :
          ((2 ^ n : ℕ) : ℤ) *
              halfGreedyNextDyadicExcessNumerator n ≤ 0 := by
        exact_mod_cast hnum
      have hpow : (0 : ℤ) < ((2 ^ n : ℕ) : ℤ) := by positivity
      exact nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hnumInt) hpow
    · right
      have hscaled :
          (((halfGreedyPrefixDenominator n : ℤ) : ℚ) ≤
            ((((2 ^ n : ℕ) : ℤ) *
              halfGreedyNextDyadicExcessNumerator n : ℤ) : ℚ)) := by
        have := (le_div_iff₀ hDpos).mp hpos
        simpa using this
      exact_mod_cast hscaled
  · rintro (hneg | hscaled)
    · left
      have hpow : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := by positivity
      have hnumInt :
          ((2 ^ n : ℕ) : ℤ) *
              halfGreedyNextDyadicExcessNumerator n ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpow hneg
      have hnum :
          ((((2 ^ n : ℕ) : ℤ) *
              halfGreedyNextDyadicExcessNumerator n : ℤ) : ℚ) ≤ 0 := by
        exact_mod_cast hnumInt
      apply (div_le_iff₀ hDpos).2
      simpa using hnum
    · right
      have hscaledRat :
          (((halfGreedyPrefixDenominator n : ℤ) : ℚ) ≤
            ((((2 ^ n : ℕ) : ℤ) *
              halfGreedyNextDyadicExcessNumerator n : ℤ) : ℚ)) := by
        exact_mod_cast hscaled
      apply (le_div_iff₀ hDpos).2
      simpa using hscaledRat

/-- Division-free producer socket for the second-channel route.  It asks the
actual reduced half-greedy prefix to avoid the single integer window

`0 < 2^n E_n < D_n`

from rank seven onward. -/
def HalfGreedyScaledExcessOutsideUnit : Prop :=
  ∀ n : ℕ, 7 ≤ n →
    halfGreedyNextDyadicExcessNumerator n ≤ 0 ∨
      (halfGreedyPrefixDenominator n : ℤ) ≤
        ((2 ^ n : ℕ) : ℤ) *
          halfGreedyNextDyadicExcessNumerator n

/-- The outside-unit dichotomy is unconditional through rank twenty.  This
includes the first transition at which the displayed residual numerator is
not one, so the remaining producer is not concealing a unit-numerator base
case. -/
theorem halfGreedy_scaledExcessOutsideUnit_of_le_twenty
    (n : ℕ) (hn : n ≤ 20) :
    halfGreedyNextDyadicExcessNumerator n ≤ 0 ∨
      (halfGreedyPrefixDenominator n : ℤ) ≤
        ((2 ^ n : ℕ) : ℤ) *
          halfGreedyNextDyadicExcessNumerator n := by
  apply (secondChannelPhaseRat_outside_unit_iff_scaled_excess n).1
  interval_cases n <;>
    norm_num [greedyMersenneSecondChannelPhaseRat,
      greedyMersenneRemainderRat, mersenneWeightRat]

/-- The genuinely infinite arithmetic producer after discharging every rank
through the first non-unit transition. -/
def HalfGreedyScaledExcessOutsideUnitFromTwentyOne : Prop :=
  ∀ n : ℕ, 21 ≤ n →
    halfGreedyNextDyadicExcessNumerator n ≤ 0 ∨
      (halfGreedyPrefixDenominator n : ℤ) ≤
        ((2 ^ n : ℕ) : ℤ) *
          halfGreedyNextDyadicExcessNumerator n

/-- End-to-end integer consumer for the rational-half counterexample route.
The finite ranks are discharged by the existing exact certificate; a proof
that the actual reduced excess never enters `0 < 2^n E_n < D_n` would place
`1/2` in the Mersenne achievement set. -/
theorem half_mem_mersenneAchievementSet_of_scaledExcessOutsideUnit
    (hout : HalfGreedyScaledExcessOutsideUnit) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven
  intro n hn
  apply halfSecondChannelSeparatedRat_of_outside_unit (by omega)
  exact (secondChannelPhaseRat_outside_unit_iff_scaled_excess n).2
    (hout n hn)

/-- End-to-end form with the complete finite prefix removed from the
hypothesis.  Only ranks `n ≥ 21` remain. -/
theorem half_mem_mersenneAchievementSet_of_scaledExcessOutsideUnitFromTwentyOne
    (hout : HalfGreedyScaledExcessOutsideUnitFromTwentyOne) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_scaledExcessOutsideUnit
  intro n hn
  by_cases h20 : n ≤ 20
  · exact halfGreedy_scaledExcessOutsideUnit_of_le_twenty n h20
  · exact hout n (by omega)

/-- The exact actual-orbit cap socket: the real two-channel cap is equivalent
to a single integer inequality in the greedy prefix numerator and its odd
denominator. -/
theorem greedyHalfRemainder_le_twoChannelCap_iff_excess (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≤ halfTwoChannelCap (n + 1) ↔
      3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
          halfGreedyNextDyadicExcessNumerator n) ≤
        (halfGreedyPrefixDenominator n : ℤ) := by
  have hD : 0 < halfGreedyPrefixDenominator n :=
    Rat.den_pos (halfGreedyPrefixRat n)
  have hrat := divInt_le_nextTwoChannelCap_iff_excess
    (halfGreedyResidualDisplayedNumerator n) n
    (halfGreedyPrefixDenominator n) hD
  rw [← greedyHalfRemainderRat_eq_displayed_divInt] at hrat
  have hrat' :
      greedyMersenneRemainderRat (1 / 2 : ℚ) n ≤
          (1 / (2 : ℚ)) ^ (n + 1) +
            (1 / 3 : ℚ) * (1 / 4 : ℚ) ^ (n + 1) ↔
        3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
            halfGreedyNextDyadicExcessNumerator n) ≤
          (halfGreedyPrefixDenominator n : ℤ) := by
    simpa only [halfGreedyNextDyadicExcessNumerator] using hrat
  rw [← hrat']
  have hcap :
      ((((1 / (2 : ℚ)) ^ (n + 1) +
          (1 / 3 : ℚ) * (1 / 4 : ℚ) ^ (n + 1) : ℚ)) : ℝ) =
        halfTwoChannelCap (n + 1) := by
    unfold halfTwoChannelCap
    push_cast
    norm_num
  have hhalf : (((1 / 2 : ℚ) : ℚ) : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  constructor
  · intro h
    have hcast :
        ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) ≤
          ((((1 / (2 : ℚ)) ^ (n + 1) +
            (1 / 3 : ℚ) * (1 / 4 : ℚ) ^ (n + 1) : ℚ)) : ℝ) := by
      rw [cast_greedyMersenneRemainderRat, hcap]
      simpa only [hhalf] using h
    exact_mod_cast hcast
  · intro h
    have hcast :
        ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) ≤
          ((((1 / (2 : ℚ)) ^ (n + 1) +
            (1 / 3 : ℚ) * (1 / 4 : ℚ) ^ (n + 1) : ℚ)) : ℝ) := by
      exact_mod_cast h
    rw [cast_greedyMersenneRemainderRat, hcap] at hcast
    simpa only [hhalf] using hcast

/-- The stronger dyadic-safe predicate is simply the sign of the same exact
integer numerator. -/
theorem greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≤ halfDyadicCap (n + 1) ↔
      halfGreedyNextDyadicExcessNumerator n ≤ 0 := by
  have hD : 0 < halfGreedyPrefixDenominator n :=
    Rat.den_pos (halfGreedyPrefixRat n)
  have hrat := divInt_le_nextDyadic_iff_excess_nonpos
    (halfGreedyResidualDisplayedNumerator n) n
    (halfGreedyPrefixDenominator n) hD
  rw [← greedyHalfRemainderRat_eq_displayed_divInt] at hrat
  have hrat' :
      greedyMersenneRemainderRat (1 / 2 : ℚ) n ≤
          1 / (2 : ℚ) ^ (n + 1) ↔
        halfGreedyNextDyadicExcessNumerator n ≤ 0 := by
    simpa only [halfGreedyNextDyadicExcessNumerator] using hrat
  rw [← hrat']
  have hcap :
      (((1 / (2 : ℚ) ^ (n + 1) : ℚ)) : ℝ) =
        halfDyadicCap (n + 1) := by
    unfold halfDyadicCap
    push_cast
    rw [div_pow]
    norm_num
  have hhalf : (((1 / 2 : ℚ) : ℚ) : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  constructor
  · intro h
    have hcast :
        ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) ≤
          ((1 / (2 : ℚ) ^ (n + 1) : ℚ) : ℝ) := by
      rw [cast_greedyMersenneRemainderRat, hcap]
      simpa only [hhalf] using h
    exact_mod_cast hcast
  · intro h
    have hcast :
        ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) ≤
          ((1 / (2 : ℚ) ^ (n + 1) : ℚ) : ℝ) := by
      exact_mod_cast h
    rw [cast_greedyMersenneRemainderRat, hcap] at hcast
    simpa only [hhalf] using hcast

/-- A genuine landing in the next Mersenne--dyadic sliver is detected by a
positive integer numerator.  The skipped-branch hypothesis supplies the
independent strict upper bound by the next Mersenne weight. -/
theorem nextDyadic_lt_greedyHalfRemainder_iff_excess_pos (n : ℕ) :
    halfDyadicCap (n + 1) <
        greedyMersenneRemainder (1 / 2 : ℝ) n ↔
      0 < halfGreedyNextDyadicExcessNumerator n := by
  simpa only [not_le] using
    not_congr (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos n)

/-- The actual half orbit skips rank `n+1` exactly when its displayed excess
satisfies `2E_n < p_n`. -/
theorem greedyHalfRemainder_lt_mersenneWeight_iff_excess (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n < mersenneWeight (n + 1) ↔
      2 * halfGreedyNextDyadicExcessNumerator n <
        halfGreedyResidualDisplayedNumerator n := by
  have hD : 0 < halfGreedyPrefixDenominator n :=
    Rat.den_pos (halfGreedyPrefixRat n)
  have hgeneric := mersenneWeightRat_succ_le_divInt_iff_excess
    (halfGreedyResidualDisplayedNumerator n) n
    (halfGreedyPrefixDenominator n) hD
  rw [← greedyHalfRemainderRat_eq_displayed_divInt] at hgeneric
  have hhalf : (((1 / 2 : ℚ) : ℚ) : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  have htakeCast :
      mersenneWeightRat (n + 1) ≤
          greedyMersenneRemainderRat (1 / 2 : ℚ) n ↔
        mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) n := by
    simpa only [hhalf] using
      (rational_greedy_take_iff_real (1 / 2 : ℚ) n)
  have htake :
      mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) n ↔
        halfGreedyResidualDisplayedNumerator n ≤
          2 * halfGreedyNextDyadicExcessNumerator n :=
    htakeCast.symm.trans
      (by simpa only [halfGreedyNextDyadicExcessNumerator] using hgeneric)
  simpa only [not_le] using not_congr htake

/-- The actual forbidden Mersenne--dyadic sliver is the finite integer
window `0 < E_n` and `2E_n < p_n`.  This is the exact last-skip comparison
that any run-compressed producer must exclude. -/
theorem greedyHalf_mem_nextMersenneDyadicSliver_iff_excess (n : ℕ) :
    (halfDyadicCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n <
          mersenneWeight (n + 1)) ↔
      (0 < halfGreedyNextDyadicExcessNumerator n ∧
        2 * halfGreedyNextDyadicExcessNumerator n <
          halfGreedyResidualDisplayedNumerator n) := by
  rw [nextDyadic_lt_greedyHalfRemainder_iff_excess_pos,
    greedyHalfRemainder_lt_mersenneWeight_iff_excess]

/-- Exact hard falsifier for the two-channel producer: a cap violation is
the reverse strict integer inequality, with no numerical approximation. -/
theorem twoChannelCap_lt_greedyHalfRemainder_iff_excess (n : ℕ) :
    halfTwoChannelCap (n + 1) <
        greedyMersenneRemainder (1 / 2 : ℝ) n ↔
      (halfGreedyPrefixDenominator n : ℤ) <
        3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
          halfGreedyNextDyadicExcessNumerator n) := by
  simpa only [not_le] using
    not_congr (greedyHalfRemainder_le_twoChannelCap_iff_excess n)

/-- Division-free producer for the only branch on which the greedy
two-channel cap has arithmetic content. -/
def HalfGreedySkippedExcessBound : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
          halfGreedyNextDyadicExcessNumerator n) ≤
        (halfGreedyPrefixDenominator n : ℤ)

/-- The integer skipped-rank producer plugs directly into the landed greedy
membership consumer. -/
theorem half_mem_mersenneAchievementSet_of_skipped_excessBound
    (hbound : HalfGreedySkippedExcessBound) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
  intro n hskip
  exact (greedyHalfRemainder_le_twoChannelCap_iff_excess n).2
    (hbound n hskip)

/-! ## Unsafe-skip block forcing -/

/-- The Mersenne mass through twice the current depth is already smaller than
the current dyadic cap.  This converts a dyadically unsafe skipped remainder
into a long forced block of subsequent greedy selections. -/
theorem mersennePrefix_doubleDepth_lt_halfDyadicCap
    {m : ℕ} (hm : 0 < m) :
    (∑ k ∈ Finset.range (m + 1), mersenneWeight (m + k + 1)) <
      halfDyadicCap m := by
  have hsplit := mersenneTail_eq_prefix_add_tail m (m + 1)
  have hcorr := mersenneCorrectionTail_lt_doubleDepth hm
  have hpost := mersenneCorrectionTail_pos (m + (m + 1))
  unfold mersenneCorrectionTail at hcorr hpost
  unfold halfDyadicCap
  have hindex : 2 * m + 1 = m + (m + 1) := by omega
  rw [hindex] at hcorr
  linarith

/-- If a finite block weighs less than the current remainder, greedy must
select every term in that block. -/
theorem greedyMersenne_forcedBlock_selected
    {x : ℝ} {m J : ℕ}
    (hblock :
      (∑ k ∈ Finset.range J, mersenneWeight (m + k + 1)) <
        greedyMersenneRemainder x m) :
    ∀ j ∈ Finset.range J,
      mersenneWeight (m + j + 1) ≤
        greedyMersenneRemainder x (m + j) := by
  have hstate : ∀ j : ℕ, j ≤ J →
      greedyMersenneRemainder x (m + j) =
        greedyMersenneRemainder x m -
          ∑ k ∈ Finset.range j, mersenneWeight (m + k + 1) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have hjJ : j ≤ J := by omega
        have hprefix :
            (∑ k ∈ Finset.range (j + 1), mersenneWeight (m + k + 1)) ≤
              ∑ k ∈ Finset.range J, mersenneWeight (m + k + 1) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
          intro k _ _
          exact (mersenneWeight_pos (by omega)).le
        have htake : mersenneWeight (m + j + 1) ≤
            greedyMersenneRemainder x (m + j) := by
          rw [ih hjJ]
          rw [Finset.sum_range_succ] at hprefix
          linarith
        rw [show m + (j + 1) = (m + j) + 1 by omega,
          greedyMersenneRemainder_succ, if_pos htake, ih hjJ,
          Finset.sum_range_succ]
        ring
  intro j hj
  have hjlt : j < J := Finset.mem_range.mp hj
  have hprefix :
      (∑ k ∈ Finset.range (j + 1), mersenneWeight (m + k + 1)) ≤
        ∑ k ∈ Finset.range J, mersenneWeight (m + k + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro k _ _
    exact (mersenneWeight_pos (by omega)).le
  rw [hstate j (by omega)]
  rw [Finset.sum_range_succ] at hprefix
  linarith

/-- Consecutive selections preserve signed distance from the exact tail
separatrix.  This explains why a forced take block alone cannot produce a
contradiction: both the remainder and the true tail lose the same prefix. -/
theorem forcedBlock_tailExcess_eq (m J : ℕ) (r : ℝ) :
    (r - (∑ k ∈ Finset.range J, mersenneWeight (m + k + 1))) -
        mersenneTail (m + J) =
      r - mersenneTail m := by
  have htail := mersenneTail_eq_prefix_add_tail m J
  linarith

/-- Starting at exponent at least two improves the crude factor-two envelope
on each higher-channel term to `4/3`. -/
theorem mersenneWeightRemainder_le_four_thirds
    {n : ℕ} (hn : 2 ≤ n) :
    mersenneWeightRemainder n ≤
      (4 / 3 : ℝ) * ((1 : ℝ) / 8) ^ n := by
  have hxle : ((1 : ℝ) / 2) ^ n ≤ (1 : ℝ) / 4 := by
    calc
      ((1 : ℝ) / 2) ^ n ≤ ((1 : ℝ) / 2) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = (1 : ℝ) / 4 := by norm_num
  have hden : 0 < 1 - ((1 : ℝ) / 2) ^ n := by linarith
  unfold mersenneWeightRemainder
  rw [div_le_iff₀ hden]
  have hpow : 0 ≤ ((1 : ℝ) / 8) ^ n := by positivity
  nlinarith

/-- At positive starting depth, the accumulated channels of order at least
three are bounded by `(4/21)·8⁻ᵐ`. -/
theorem mersenneWeightRemainderTail_le_four_twentyone
    {m : ℕ} (hm : 0 < m) :
    mersenneWeightRemainderTail m ≤
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := by
  have henv : Summable (fun k : ℕ =>
      (4 / 3 : ℝ) * ((1 : ℝ) / 8) ^ (m + k + 1)) := by
    have hbase := summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
    have hshift := (summable_nat_add_iff (m + 1)).mpr hbase
    have hmul := hshift.mul_left (4 / 3 : ℝ)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul
  calc
    mersenneWeightRemainderTail m
        ≤ ∑' k : ℕ,
            (4 / 3 : ℝ) * ((1 : ℝ) / 8) ^ (m + k + 1) := by
          unfold mersenneWeightRemainderTail
          exact (summable_mersenneWeightRemainderTail m).tsum_le_tsum
            (fun k => mersenneWeightRemainder_le_four_thirds
              (by omega)) henv
    _ = (4 / 3 : ℝ) *
          ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) := tsum_mul_left
    _ = (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := by
      rw [tsum_eighth_nat_add_succ]
      ring

/-- The higher-channel tail at depth `m` is strictly smaller than the dyadic
tail at depth `3m+2`. -/
theorem remainderTail_lt_tripleDyadic
    {m : ℕ} (hm : 0 < m) :
    mersenneWeightRemainderTail m <
      ((1 : ℝ) / 2) ^ (3 * m + 2) := by
  have hrem := mersenneWeightRemainderTail_le_four_twentyone hm
  have hid : ((1 : ℝ) / 2) ^ (3 * m + 2) =
      (1 / 4 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    rw [pow_add, show ((1 : ℝ) / 2) ^ (3 * m) =
      ((1 : ℝ) / 8) ^ m by
        rw [show ((1 : ℝ) / 8) = ((1 : ℝ) / 2) ^ 3 by norm_num,
          pow_mul]]
    norm_num
    ring
  rw [hid]
  have hpow : 0 < ((1 : ℝ) / 8) ^ m := by positivity
  nlinarith

/-- The complete consecutive block through exponent `3m+2` is still
strictly lighter than the two-channel cap at depth `m`. -/
theorem mersennePrefix_threeDepth_add_two_lt_halfTwoChannelCap
    {m : ℕ} (hm : 0 < m) :
    (∑ k ∈ Finset.range (2 * m + 2), mersenneWeight (m + k + 1)) <
      halfTwoChannelCap m := by
  have hsplit := mersenneTail_eq_prefix_add_tail m (2 * m + 2)
  have hrem := remainderTail_lt_tripleDyadic hm
  have htailDecomp := mersenneTail_eq_two_channels_add_remainderTail m
  have hindex : m + (2 * m + 2) = 3 * m + 2 := by omega
  rw [hindex] at hsplit
  have hdyadicBelow : ((1 : ℝ) / 2) ^ (3 * m + 2) <
      mersenneTail (3 * m + 2) := by
    rw [mersenneTail_eq_two_channels_add_remainderTail]
    have hquarter : 0 < (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (3 * m + 2) := by
      positivity
    have hnonneg := mersenneWeightRemainderTail_nonneg (3 * m + 2)
    linarith
  unfold halfTwoChannelCap
  linarith

/-- A two-channel-cap violation forces the consecutive greedy take block
through exponent `3m+2`. -/
theorem capViolation_forces_threeDepthBlock
    {x : ℝ} {m : ℕ} (hm : 0 < m)
    (hcap : halfTwoChannelCap m < greedyMersenneRemainder x m) :
    ∀ j ∈ Finset.range (2 * m + 2),
      mersenneWeight (m + j + 1) ≤
        greedyMersenneRemainder x (m + j) := by
  have hblock :
      (∑ k ∈ Finset.range (2 * m + 2), mersenneWeight (m + k + 1)) <
        greedyMersenneRemainder x m :=
    (mersennePrefix_threeDepth_add_two_lt_halfTwoChannelCap hm).trans hcap
  exact greedyMersenne_forcedBlock_selected hblock

/-- At the first depth beyond the forced block, the full remaining tail is
already smaller than the third-channel contribution at the starting depth. -/
theorem tripleDepthTail_lt_thirdChannel
    {m : ℕ} (hm : 0 < m) :
    mersenneTail (3 * m + 3) <
      (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ m := by
  have hdecomp := mersenneTail_eq_two_channels_add_remainderTail (3 * m + 3)
  have hrem := mersenneWeightRemainderTail_le (3 * m + 3)
  have hhalf : ((1 : ℝ) / 2) ^ (3 * m + 3) =
      (1 / 8 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    rw [pow_add, show ((1 : ℝ) / 2) ^ (3 * m) =
      ((1 : ℝ) / 8) ^ m by
        rw [show ((1 : ℝ) / 8) = ((1 : ℝ) / 2) ^ 3 by norm_num,
          pow_mul]]
    norm_num
    ring
  have hquarterEq : ((1 : ℝ) / 4) ^ (3 * m + 3) =
      ((1 : ℝ) / 2) ^ (3 * m + 6) *
        ((1 : ℝ) / 8) ^ m := by
    rw [show ((1 : ℝ) / 4) ^ (3 * m + 3) =
      ((1 : ℝ) / 2) ^ (2 * (3 * m + 3)) by
        rw [show ((1 : ℝ) / 4) = ((1 : ℝ) / 2) ^ 2 by norm_num,
          ← pow_mul],
      show ((1 : ℝ) / 8) ^ m = ((1 : ℝ) / 2) ^ (3 * m) by
        rw [show ((1 : ℝ) / 8) = ((1 : ℝ) / 2) ^ 3 by norm_num,
          ← pow_mul],
      ← pow_add]
    congr 1
    omega
  have hquarterFactor : ((1 : ℝ) / 2) ^ (3 * m + 6) ≤
      (1 / 512 : ℝ) := by
    calc
      ((1 : ℝ) / 2) ^ (3 * m + 6) ≤
          ((1 : ℝ) / 2) ^ 9 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = (1 / 512 : ℝ) := by norm_num
  have hquarter : ((1 : ℝ) / 4) ^ (3 * m + 3) ≤
      (1 / 512 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    rw [hquarterEq]
    exact mul_le_mul_of_nonneg_right hquarterFactor (by positivity)
  have heightEq : ((1 : ℝ) / 8) ^ (3 * m + 3) =
      ((1 : ℝ) / 8) ^ (2 * m + 3) *
        ((1 : ℝ) / 8) ^ m := by
    rw [← pow_add]
    congr 1
    omega
  have heightFactor : ((1 : ℝ) / 8) ^ (2 * m + 3) ≤
      (1 / 32768 : ℝ) := by
    calc
      ((1 : ℝ) / 8) ^ (2 * m + 3) ≤
          ((1 : ℝ) / 8) ^ 5 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = (1 / 32768 : ℝ) := by norm_num
  have height : ((1 : ℝ) / 8) ^ (3 * m + 3) ≤
      (1 / 32768 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    rw [heightEq]
    exact mul_le_mul_of_nonneg_right heightFactor (by positivity)
  have hpow : 0 < ((1 : ℝ) / 8) ^ m := by positivity
  have hquarterScaled := mul_le_mul_of_nonneg_left hquarter
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have heightScaled := mul_le_mul_of_nonneg_left height
    (by norm_num : (0 : ℝ) ≤ 2 / 7)
  nlinarith

/-- The two-channel cap lies strictly before the next (`2m+3`)-term prefix.
Together with the preceding lower bracket, this pins its exact prefix cell. -/
theorem halfTwoChannelCap_lt_mersennePrefix_threeDepth_add_three
    {m : ℕ} (hm : 0 < m) :
    halfTwoChannelCap m <
      (∑ k ∈ Finset.range (2 * m + 3), mersenneWeight (m + k + 1)) := by
  have hsplit := mersenneTail_eq_prefix_add_tail m (2 * m + 3)
  have htail := tripleDepthTail_lt_thirdChannel hm
  have hthird := one_seventh_eighth_pow_lt_mersenneWeightRemainderTail m
  have hdecomp := mersenneTail_eq_two_channels_add_remainderTail m
  have hindex : m + (2 * m + 3) = 3 * m + 3 := by omega
  rw [hindex] at hsplit
  unfold halfTwoChannelCap
  linarith

/-- Hard local falsifier: there is an open relaxed-state cell above the
two-channel cap which takes every exponent through `3m+2` and then skips
`3m+3`.  Hence skip-plus-forced-run geometry alone cannot close the producer;
some arithmetic property of the actual greedy prefix is indispensable. -/
theorem exists_relaxed_capViolation_exact_block
    {m : ℕ} (hm : 0 < m) :
    ∃ r : ℝ,
      halfTwoChannelCap m < r ∧
      r < mersenneWeight m ∧
      (∑ k ∈ Finset.range (2 * m + 2),
          mersenneWeight (m + k + 1)) < r ∧
      r - (∑ k ∈ Finset.range (2 * m + 2),
          mersenneWeight (m + k + 1)) < mersenneWeight (3 * m + 3) := by
  let P : ℝ := ∑ k ∈ Finset.range (2 * m + 2),
    mersenneWeight (m + k + 1)
  let Q : ℝ := ∑ k ∈ Finset.range (2 * m + 3),
    mersenneWeight (m + k + 1)
  have hP : P < halfTwoChannelCap m := by
    simpa [P] using
      mersennePrefix_threeDepth_add_two_lt_halfTwoChannelCap hm
  have hQ : halfTwoChannelCap m < Q := by
    simpa [Q] using
      halfTwoChannelCap_lt_mersennePrefix_threeDepth_add_three hm
  have hQstep : Q = P + mersenneWeight (3 * m + 3) := by
    dsimp [P, Q]
    rw [Finset.sum_range_succ]
    congr 1
    ring
  have hQtail : Q < mersenneTail m := by
    have hsplit := mersenneTail_eq_prefix_add_tail m (2 * m + 3)
    have hpos := mersenneTail_pos (m + (2 * m + 3))
    change mersenneTail m = Q + mersenneTail (m + (2 * m + 3)) at hsplit
    linarith
  have hQweight : Q < mersenneWeight m :=
    hQtail.trans (mersenneTail_lt_weight hm)
  refine ⟨(halfTwoChannelCap m + Q) / 2, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · rw [hQstep] at hQ
    linarith

/-- A skipped half-orbit rank above its dyadic cap forces selection of every
one of the next `n + 2` exponents. -/
theorem greedyHalf_unsafeSkip_forces_doubleBlock
    (n : ℕ)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n)
    (hunsafe : halfDyadicCap (n + 1) <
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    ∀ j ∈ Finset.range (n + 2),
      mersenneWeight (n + j + 2) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (n + j + 1) := by
  have hrem : greedyMersenneRemainder (1 / 2 : ℝ) (n + 1) =
      greedyMersenneRemainder (1 / 2 : ℝ) n := by
    rw [greedyMersenneRemainder_succ, if_neg hskip]
  have hprefix :=
    mersennePrefix_doubleDepth_lt_halfDyadicCap (m := n + 1) (by omega)
  have hblock :
      (∑ k ∈ Finset.range (n + 2),
          mersenneWeight ((n + 1) + k + 1)) <
        greedyMersenneRemainder (1 / 2 : ℝ) (n + 1) := by
    rw [hrem]
    exact hprefix.trans hunsafe
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    greedyMersenne_forcedBlock_selected hblock

/-- On the actual half orbit, a skipped rank which violates the two-channel
cap forces the maximal uniform block supplied by tail geometry: all following
exponents through `3(n+1)+2`. -/
theorem greedyHalf_capViolationSkip_forces_threeDepthBlock
    (n : ℕ)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n)
    (hcap : halfTwoChannelCap (n + 1) <
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    ∀ j ∈ Finset.range (2 * n + 4),
      mersenneWeight (n + j + 2) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (n + j + 1) := by
  have hrem : greedyMersenneRemainder (1 / 2 : ℝ) (n + 1) =
      greedyMersenneRemainder (1 / 2 : ℝ) n := by
    rw [greedyMersenneRemainder_succ, if_neg hskip]
  have hforce := capViolation_forces_threeDepthBlock
    (x := (1 / 2 : ℝ)) (m := n + 1) (by omega) (by
      rw [hrem]
      exact hcap)
  simpa only [show 2 * (n + 1) + 2 = 2 * n + 4 by omega,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hforce

/-- Strongest run-compressed arithmetic producer supplied by the uniform
tail geometry.  The exact excess inequality is required only when a skipped
rank is followed by the entire forced take block through exponent `3n+5`. -/
def HalfGreedyThreeDepthTakeRunExcessBound : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      (∀ j ∈ Finset.range (2 * n + 4),
        mersenneWeight (n + j + 2) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) (n + j + 1)) →
        3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
            halfGreedyNextDyadicExcessNumerator n) ≤
          (halfGreedyPrefixDenominator n : ℤ)

/-- The triple-depth run producer is sufficient for the original skipped-rank
excess bound.  If the displayed run fails, the cap violation itself is
impossible by `greedyHalf_capViolationSkip_forces_threeDepthBlock`. -/
theorem halfGreedySkippedExcessBound_of_threeDepthTakeRun
    (hthree : HalfGreedyThreeDepthTakeRunExcessBound) :
    HalfGreedySkippedExcessBound := by
  intro n hskip
  by_cases hrun : ∀ j ∈ Finset.range (2 * n + 4),
      mersenneWeight (n + j + 2) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (n + j + 1)
  · exact hthree n hskip hrun
  · have hcap : greedyMersenneRemainder (1 / 2 : ℝ) n ≤
        halfTwoChannelCap (n + 1) := by
      apply not_lt.mp
      intro hbad
      exact hrun
        (greedyHalf_capViolationSkip_forces_threeDepthBlock n hskip hbad)
    exact (greedyHalfRemainder_le_twoChannelCap_iff_excess n).1 hcap

/-- The strongest run-compressed producer feeds the half-membership
consumer. -/
theorem half_mem_mersenneAchievementSet_of_threeDepthTakeRunExcessBound
    (hthree : HalfGreedyThreeDepthTakeRunExcessBound) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_skipped_excessBound
    (halfGreedySkippedExcessBound_of_threeDepthTakeRun hthree)

/-- Earlier, weaker run-compressed producer retained for compatibility.  It
uses only the dyadic unsafe-skip block through twice the current depth; the
triple-depth producer above has a strictly narrower exceptional branch. -/
def HalfGreedyLongTakeRunExcessBound : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      (∀ j ∈ Finset.range (n + 2),
        mersenneWeight (n + j + 2) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) (n + j + 1)) →
        3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
            halfGreedyNextDyadicExcessNumerator n) ≤
          (halfGreedyPrefixDenominator n : ℤ)

theorem halfGreedySkippedExcessBound_of_longTakeRun
    (hlong : HalfGreedyLongTakeRunExcessBound) :
    HalfGreedySkippedExcessBound := by
  intro n hskip
  by_cases hrun : ∀ j ∈ Finset.range (n + 2),
      mersenneWeight (n + j + 2) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (n + j + 1)
  · exact hlong n hskip hrun
  · have hsafeReal : greedyMersenneRemainder (1 / 2 : ℝ) n ≤
        halfDyadicCap (n + 1) := by
      apply not_lt.mp
      intro hunsafe
      exact hrun (greedyHalf_unsafeSkip_forces_doubleBlock n hskip hunsafe)
    have hE : halfGreedyNextDyadicExcessNumerator n ≤ 0 :=
      (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos n).1 hsafeReal
    have hD : 0 < (halfGreedyPrefixDenominator n : ℤ) := by
      exact_mod_cast Rat.den_pos (halfGreedyPrefixRat n)
    have hpow : 0 ≤ (((2 ^ (n + 1) : ℕ) : ℤ)) := by positivity
    nlinarith

/-- The long-take-run producer feeds the existing exact half-membership
consumer. -/
theorem half_mem_mersenneAchievementSet_of_longTakeRunExcessBound
    (hlong : HalfGreedyLongTakeRunExcessBound) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_skipped_excessBound
    (halfGreedySkippedExcessBound_of_longTakeRun hlong)

/-! ## Existing finite-denominator and support-series bridges -/

/-- At base two, the actual reduced denominator of every positive finite
Erdős fragment is odd. -/
theorem finiteErdosSum_den_odd
    (F : Finset ℕ) (h0 : 0 ∉ F) :
    Odd (finiteErdosSum F 2).den := by
  exact Nat.coprime_two_left.mp
    (coprime_base_den_finiteErdosSum F 2 h0 (by omega))

/-- The denominator used by the skipped-rank numerator is genuinely odd,
because the finite greedy prefix contains no exponent zero. -/
theorem halfGreedyPrefixDenominator_odd (n : ℕ) :
    Odd (halfGreedyPrefixDenominator n) := by
  unfold halfGreedyPrefixDenominator halfGreedyPrefixRat
  exact finiteErdosSum_den_odd
    (greedyMersennePrefixRat (1 / 2 : ℚ) n)
    (zero_not_mem_greedyMersennePrefixRat (1 / 2 : ℚ) n)

/-- The existing finite noncollapse theorem rewritten in the T9 order API:
the order of two modulo the actual reduced denominator is `lcm F`. -/
theorem oddDoublingOrder_finiteErdosSum_den_eq_lcm
    (F : Finset ℕ) (hF : F.Nonempty) (h0 : 0 ∉ F) :
    oddDoublingOrder (finiteErdosSum F 2).den
        (finiteErdosSum_den_odd F h0) = F.lcm id := by
  simpa [oddDoublingOrder] using
    finite_period_noncollapse_rat_den F 2 hF h0 (by omega)

/-- A finite support series is the real cast of the audited rational
`finiteErdosSum`. -/
theorem erdosSupportSeries_finset_eq_cast_finiteErdosSum (F : Finset ℕ) :
    erdosSupportSeries 2 (↑F : Set ℕ) = ((finiteErdosSum F 2 : ℚ) : ℝ) := by
  calc
    erdosSupportSeries 2 (↑F : Set ℕ)
        = ∑ a ∈ F, mersenneWeight a := by
            unfold erdosSupportSeries
            rw [tsum_eq_sum (s := F)]
            · exact Finset.sum_congr rfl fun a ha => by
                simp [mersenneWeight, ha]
            · intro a ha
              simp [ha]
    _ = ((∑ a ∈ F, mersenneWeightRat a : ℚ) : ℝ) := by
          push_cast
          simp only [cast_mersenneWeightRat]
    _ = ((finiteErdosSum F 2 : ℚ) : ℝ) := by
          congr 1

/-- Removing a finite fragment from a support subtracts exactly its audited
finite rational sum.  No ordering or prefix hypothesis is used. -/
theorem erdosSupportSeries_diff_finset
    (A : Set ℕ) (F : Finset ℕ) (hFA : (↑F : Set ℕ) ⊆ A) :
    erdosSupportSeries 2 (A \ (↑F : Set ℕ)) =
      erdosSupportSeries 2 A - ((finiteErdosSum F 2 : ℚ) : ℝ) := by
  let fA : ℕ → ℝ := fun a =>
    Set.indicator A (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a
  let fF : ℕ → ℝ := fun a =>
    Set.indicator (↑F : Set ℕ) (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a
  have hsA : Summable fA := by
    simpa [fA] using summable_erdosSupport_indicator 2 A (by omega)
  have hsF : Summable fF := by
    simpa [fF] using
      summable_erdosSupport_indicator 2 (↑F : Set ℕ) (by omega)
  calc
    erdosSupportSeries 2 (A \ (↑F : Set ℕ))
        = ∑' a : ℕ, (fA a - fF a) := by
            unfold erdosSupportSeries
            apply tsum_congr
            intro a
            by_cases haF : a ∈ F
            · have haA : a ∈ A := hFA (by simpa using haF)
              simp [fA, fF, haF, haA]
            · by_cases haA : a ∈ A
              · simp [fA, fF, haF, haA]
              · simp [fA, fF, haF, haA]
    _ = (∑' a : ℕ, fA a) - ∑' a : ℕ, fF a := hsA.tsum_sub hsF
    _ = erdosSupportSeries 2 A - erdosSupportSeries 2 (↑F : Set ℕ) := by
          rfl
    _ = erdosSupportSeries 2 A - ((finiteErdosSum F 2 : ℚ) : ℝ) := by
          rw [erdosSupportSeries_finset_eq_cast_finiteErdosSum]

/-- Algebraic composition of the support-difference bridge with displayed
dyadic and reduced-prefix fractions. -/
theorem finiteFragment_residual_value
    (A : Set ℕ) (F : Finset ℕ) (p r c D : ℕ)
    (hFA : (↑F : Set ℕ) ⊆ A)
    (hwhole : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ))
    (hprefix : finiteErdosSum F 2 = (r : ℚ) / (D : ℚ))
    (hDpos : 0 < D) (hle : 2 ^ c * r ≤ p * D) :
    erdosSupportSeries 2 (A \ (↑F : Set ℕ)) =
      (dyadicResidualNumerator p r c D : ℝ) /
        ((2 ^ c * D : ℕ) : ℝ) := by
  have hprefixR : ((finiteErdosSum F 2 : ℚ) : ℝ) =
      (r : ℝ) / (D : ℝ) := by
    simpa using congrArg (fun q : ℚ => (q : ℝ)) hprefix
  rw [erdosSupportSeries_diff_finset A F hFA, hwhole, hprefixR]
  unfold dyadicResidualNumerator
  rw [Nat.cast_sub hle]
  push_cast
  field_simp

/-! ## Certificate transport into the T9 wrap-ratio theorem -/

/-- The proof-bearing T12 product.  It records the no-odd-cancellation
transport, exact residual value, exact finite period, and the T9 analytic
conclusion in one reusable certificate. -/
structure DyadicPrefixCompressionCertificate
    (A : Set ℕ) (F : Finset ℕ) (p r c D : ℕ) : Prop where
  oddDenominator : Odd D
  numeratorPositive : 0 < dyadicResidualNumerator p r c D
  numeratorCoprime : (dyadicResidualNumerator p r c D).Coprime D
  denominatorSandwich :
    D ∣ (dyadicResidualRat p r c D).den ∧
      (dyadicResidualRat p r c D).den ∣ 2 ^ c * D
  residualValue :
    erdosSupportSeries 2 (A \ (↑F : Set ℕ)) =
      (dyadicResidualNumerator p r c D : ℝ) /
        ((2 ^ c * D : ℕ) : ℝ)
  orderEq : oddDoublingOrder D oddDenominator = F.lcm id
  wrapBound :
    ReciprocalMassDivergesOrAtLeast (A \ (↑F : Set ℕ))
      ((doublingWrapCount (dyadicResidualNumerator p r c D) D (F.lcm id) : ℝ) /
        ((F.lcm id : ℕ) : ℝ))

/-- Generic finite-fragment T12 transport.  The prefix certificate names the
actual reduced denominator and numerator; the existing noncollapse theorem
supplies the exact order, while T9 supplies the analytic disjunction. -/
theorem finiteFragment_dyadicPrefixCompression
    (A : Set ℕ) (F : Finset ℕ) (p r c D : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hFA : (↑F : Set ℕ) ⊆ A)
    (hwhole : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ))
    (hprefix : finiteErdosSum F 2 = (r : ℚ) / (D : ℚ))
    (hDactual : D = (finiteErdosSum F 2).den)
    (hrD : r.Coprime D) (hDgtOne : 1 < D)
    (hle : 2 ^ c * r ≤ p * D)
    (hNpos : 0 < dyadicResidualNumerator p r c D)
    (hResidual : ∃ a : ℕ, 0 < a ∧ a ∈ A \ (↑F : Set ℕ)) :
    DyadicPrefixCompressionCertificate A F p r c D := by
  have hDodd : Odd D := by
    rw [hDactual]
    exact finiteErdosSum_den_odd F h0
  have hNcop : (dyadicResidualNumerator p r c D).Coprime D :=
    dyadicResidualNumerator_coprime_oddDenominator p r c D hDodd hrD hle
  have hsandwich := dyadicResidual_denominator_sandwich
    p r c D (by omega) hDodd hrD hle
  have hresidualValue := finiteFragment_residual_value
    A F p r c D hFA hwhole hprefix (by omega) hle
  have horder : oddDoublingOrder D hDodd = F.lcm id := by
    subst D
    exact oddDoublingOrder_finiteErdosSum_den_eq_lcm F hF h0
  have hwrap :=
    support_fraction_oddOrder_wrapRatio_reciprocalMassDivergesOrAtLeast
      (A \ (↑F : Set ℕ)) hResidual
      ((dyadicResidualNumerator p r c D : ℕ) : ℤ) c hDgtOne hDodd
      (by simpa using hresidualValue)
  refine
    { oddDenominator := hDodd
      numeratorPositive := hNpos
      numeratorCoprime := hNcop
      denominatorSandwich := hsandwich
      residualValue := hresidualValue
      orderEq := horder
      wrapBound := ?_ }
  simpa [horder] using hwrap

/-! ## Finite fixtures -/

/-- Exact arithmetic, reduced odd denominator, order and wrap count for the
`{2,3}` finite fragment. -/
theorem two_three_dyadicPrefix_fixture :
    finiteErdosSum ({2, 3} : Finset ℕ) 2 = (10 : ℚ) / 21 ∧
      (finiteErdosSum ({2, 3} : Finset ℕ) 2).den = 21 ∧
      oddDoublingOrder 21 (by decide : Odd 21) = 6 ∧
      doublingWrapCount 1 21 6 = 2 ∧
      dyadicResidualRat 1 10 1 21 = (1 : ℚ) / 42 := by
  have horder := oddDoublingOrder_finiteErdosSum_den_eq_lcm
    ({2, 3} : Finset ℕ) (by simp) (by simp)
  norm_num [finiteErdosSum] at horder
  refine ⟨by norm_num [finiteErdosSum], by norm_num [finiteErdosSum], ?_, ?_, ?_⟩
  · simpa using horder
  · norm_num [doublingWrapCount, doublingWrapDigit, doublingResidue,
      Finset.sum_range_succ]
  · norm_num [dyadicResidualRat, dyadicResidualNumerator]

/-- Exact arithmetic, reduced odd denominator, order and wrap count for the
five-term finite fragment. -/
theorem five_term_dyadicPrefix_fixture :
    finiteErdosSum ({2, 3, 6, 7, 14} : Finset ℕ) 2 =
        (172021 : ℚ) / 344043 ∧
      (finiteErdosSum ({2, 3, 6, 7, 14} : Finset ℕ) 2).den = 344043 ∧
      oddDoublingOrder 344043 (by decide : Odd 344043) = 42 ∧
      doublingWrapCount 1 344043 42 = 13 ∧
      dyadicResidualRat 1 172021 1 344043 = (1 : ℚ) / 688086 := by
  have horder := oddDoublingOrder_finiteErdosSum_den_eq_lcm
    ({2, 3, 6, 7, 14} : Finset ℕ) (by simp) (by simp)
  norm_num [finiteErdosSum] at horder
  refine ⟨by norm_num [finiteErdosSum], by norm_num [finiteErdosSum], ?_, ?_, ?_⟩
  · simpa using horder
  · norm_num [doublingWrapCount, doublingWrapDigit, doublingResidue,
      Finset.sum_range_succ]
  · norm_num [dyadicResidualRat, dyadicResidualNumerator]

/-- Conditional wrapper for `F={2,3}`.  Any support of dyadic value
`1/2` containing this fragment and a positive residual witness inherits the
exact lower bound `1/3` (or divergent reciprocal mass). -/
theorem two_three_residual_reciprocalMassDivergesOrAtLeast
    (A : Set ℕ) (hFA : (↑({2, 3} : Finset ℕ) : Set ℕ) ⊆ A)
    (hwhole : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (hResidual : ∃ a : ℕ, 0 < a ∧ a ∈ A \ (↑({2, 3} : Finset ℕ) : Set ℕ)) :
    ReciprocalMassDivergesOrAtLeast
      (A \ (↑({2, 3} : Finset ℕ) : Set ℕ)) (1 / 3 : ℝ) := by
  have hcert := finiteFragment_dyadicPrefixCompression
    A ({2, 3} : Finset ℕ) 1 10 1 21
    (by simp) (by simp) hFA
    (by simpa using hwhole)
    (by norm_num [finiteErdosSum])
    (by norm_num [finiteErdosSum])
    (by decide) (by omega) (by norm_num) (by norm_num [dyadicResidualNumerator])
    hResidual
  have hbound := hcert.wrapBound
  have hwrap : doublingWrapCount 1 21 6 = 2 :=
    two_three_dyadicPrefix_fixture.2.2.2.1
  norm_num [dyadicResidualNumerator] at hbound
  rw [show GCDMonoid.lcm 2 3 = 6 by decide] at hbound
  rw [hwrap] at hbound
  norm_num at hbound
  simpa using hbound

/-- Conditional wrapper for `F={2,3,6,7,14}` with the exact
`13/42` residual wrap ratio. -/
theorem five_term_residual_reciprocalMassDivergesOrAtLeast
    (A : Set ℕ)
    (hFA : (↑({2, 3, 6, 7, 14} : Finset ℕ) : Set ℕ) ⊆ A)
    (hwhole : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (hResidual : ∃ a : ℕ, 0 < a ∧
      a ∈ A \ (↑({2, 3, 6, 7, 14} : Finset ℕ) : Set ℕ)) :
    ReciprocalMassDivergesOrAtLeast
      (A \ (↑({2, 3, 6, 7, 14} : Finset ℕ) : Set ℕ)) (13 / 42 : ℝ) := by
  have hcert := finiteFragment_dyadicPrefixCompression
    A ({2, 3, 6, 7, 14} : Finset ℕ) 1 172021 1 344043
    (by simp) (by simp) hFA
    (by simpa using hwhole)
    (by norm_num [finiteErdosSum])
    (by norm_num [finiteErdosSum])
    (by decide) (by omega) (by norm_num) (by norm_num [dyadicResidualNumerator])
    hResidual
  have hbound := hcert.wrapBound
  have hwrap : doublingWrapCount 1 344043 42 = 13 :=
    five_term_dyadicPrefix_fixture.2.2.2.1
  norm_num [dyadicResidualNumerator] at hbound
  rw [show GCDMonoid.lcm 2
      (GCDMonoid.lcm 3
        (GCDMonoid.lcm 6 (GCDMonoid.lcm 7 14))) = 42 by decide] at hbound
  rw [hwrap] at hbound
  norm_num at hbound
  simpa using hbound

/-! Reduced half-prefix lattice. -/

theorem halfGreedyExcess_add_denominator (n : ℕ) :
    (halfGreedyPrefixDenominator n : ℤ) +
        halfGreedyNextDyadicExcessNumerator n =
      ((2 ^ n : ℕ) : ℤ) * halfGreedyResidualDisplayedNumerator n := by
  simp only [halfGreedyNextDyadicExcessNumerator,
    nextDyadicExcessIntNumerator]
  ring

theorem halfGreedyResidualDisplayedNumerator_odd (n : ℕ) :
    Odd (halfGreedyResidualDisplayedNumerator n) := by
  have hD : Odd (halfGreedyPrefixDenominator n) :=
    halfGreedyPrefixDenominator_odd n
  have hDInt : Odd ((halfGreedyPrefixDenominator n : ℕ) : ℤ) :=
    hD.natCast
  have htwoNum : Even (2 * (halfGreedyPrefixRat n).num) := by
    exact ⟨(halfGreedyPrefixRat n).num, by ring⟩
  unfold halfGreedyResidualDisplayedNumerator
  exact hDInt.sub_even htwoNum

theorem halfGreedyResidualDisplayedNumerator_coprime_denominator
    (n : ℕ) :
    (halfGreedyResidualDisplayedNumerator n).natAbs.Coprime
      (halfGreedyPrefixDenominator n) := by
  let q : ℚ := halfGreedyPrefixRat n
  let D : ℕ := halfGreedyPrefixDenominator n
  have hDodd : Odd D := by
    simpa [D] using halfGreedyPrefixDenominator_odd n
  have htwoDnat : Nat.Coprime 2 D := Nat.coprime_two_left.mpr hDodd
  have htwoDint : IsCoprime (2 : ℤ) (D : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using htwoDnat
  have hnumDnat : q.num.natAbs.Coprime D := by
    simpa [q, D, halfGreedyPrefixDenominator] using q.reduced
  have hnumDint : IsCoprime q.num (D : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hnumDnat
  have hprod : IsCoprime ((2 : ℤ) * q.num) (D : ℤ) :=
    htwoDint.mul_left hnumDint
  have hadd := hprod.neg_left.add_mul_left_left (1 : ℤ)
  rw [Int.isCoprime_iff_nat_coprime] at hadd
  simpa [halfGreedyResidualDisplayedNumerator, q, D,
    halfGreedyPrefixDenominator, add_comm, mul_comm] using hadd

theorem halfGreedyNextDyadicExcessNumerator_coprime_denominator
    (n : ℕ) :
    (halfGreedyNextDyadicExcessNumerator n).natAbs.Coprime
      (halfGreedyPrefixDenominator n) := by
  let p : ℤ := halfGreedyResidualDisplayedNumerator n
  let D : ℕ := halfGreedyPrefixDenominator n
  have hDodd : Odd D := by
    simpa [D] using halfGreedyPrefixDenominator_odd n
  have hpowDnat : Nat.Coprime (2 ^ n) D :=
    (Nat.coprime_two_left.mpr hDodd).pow_left n
  have hpowDint : IsCoprime (((2 ^ n : ℕ) : ℤ)) (D : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hpowDnat
  have hpDnat : p.natAbs.Coprime D := by
    simpa [p, D] using
      halfGreedyResidualDisplayedNumerator_coprime_denominator n
  have hpDint : IsCoprime p (D : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hpDnat
  have hprod : IsCoprime (((2 ^ n : ℕ) : ℤ) * p) (D : ℤ) :=
    hpowDint.mul_left hpDint
  have hadd := hprod.add_mul_left_left (-1 : ℤ)
  have heq : (((2 ^ n : ℕ) : ℤ) * p) + (D : ℤ) * (-1) =
      ((2 ^ n : ℕ) : ℤ) * p - (D : ℤ) := by ring
  rw [heq] at hadd
  rw [Int.isCoprime_iff_nat_coprime] at hadd
  simpa [halfGreedyNextDyadicExcessNumerator,
    nextDyadicExcessIntNumerator, p, D, add_comm, mul_comm] using hadd

theorem halfGreedyNextDyadicExcessNumerator_odd
    {n : ℕ} (hn : 0 < n) :
    Odd (halfGreedyNextDyadicExcessNumerator n) := by
  have hpowNat : Even (2 ^ n) := by
    rw [even_iff_two_dvd]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  have hpowInt : Even (((2 ^ n : ℕ) : ℤ)) := hpowNat.natCast
  have hprod : Even (((2 ^ n : ℕ) : ℤ) *
      halfGreedyResidualDisplayedNumerator n) := by
    simpa [mul_comm] using
      hpowInt.mul_left (halfGreedyResidualDisplayedNumerator n)
  have hDInt : Odd ((halfGreedyPrefixDenominator n : ℕ) : ℤ) :=
    (halfGreedyPrefixDenominator_odd n).natCast
  simp only [halfGreedyNextDyadicExcessNumerator,
    nextDyadicExcessIntNumerator]
  exact hprod.sub_odd hDInt

/-! Full support-aware common-fraction lattice. -/

def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n

def halfGreedyPrefixCommonNumerator (n : ℕ) : ℕ :=
  commonNumerator (halfGreedyPrefixSupport n) 2

def halfGreedyPrefixCommonDenominator (n : ℕ) : ℕ :=
  commonDenominator (halfGreedyPrefixSupport n) 2

def halfGreedyRawResidualNumerator (n : ℕ) : ℤ :=
  (halfGreedyPrefixCommonDenominator n : ℤ) -
    2 * (halfGreedyPrefixCommonNumerator n : ℤ)

def halfGreedyRawNextDyadicExcessNumerator (n : ℕ) : ℤ :=
  nextDyadicExcessIntNumerator (halfGreedyRawResidualNumerator n) n
    (halfGreedyPrefixCommonDenominator n)

def halfGreedyPrefixReductionFactor (n : ℕ) : ℕ :=
  halfGreedyPrefixCommonDenominator n / halfGreedyPrefixDenominator n

theorem halfGreedyPrefixCommonDenominator_pos (n : ℕ) :
    0 < halfGreedyPrefixCommonDenominator n := by
  let F := halfGreedyPrefixSupport n
  have h0 : 0 ∉ F := by
    simpa [F, halfGreedyPrefixSupport] using
      zero_not_mem_greedyMersennePrefixRat (1 / 2 : ℚ) n
  have hL0 : F.lcm id ≠ 0 := lcm_ne_zero_of_zero_not_mem F h0
  simpa [halfGreedyPrefixCommonDenominator, F, commonDenominator] using
    pow_sub_one_pos_of_ne_zero 2 (F.lcm id) (by omega) hL0

theorem halfGreedyPrefixDenominator_eq_common_reduction (n : ℕ) :
    halfGreedyPrefixDenominator n =
      halfGreedyPrefixCommonDenominator n /
        Nat.gcd (halfGreedyPrefixCommonNumerator n)
          (halfGreedyPrefixCommonDenominator n) := by
  let F := halfGreedyPrefixSupport n
  have h0 : 0 ∉ F := by
    simpa [F, halfGreedyPrefixSupport] using
      zero_not_mem_greedyMersennePrefixRat (1 / 2 : ℚ) n
  have hden := finiteErdosSum_den_eq_reducedDenominator F 2 h0 (by omega)
  simpa [halfGreedyPrefixDenominator, halfGreedyPrefixRat,
    halfGreedyPrefixSupport, halfGreedyPrefixCommonNumerator,
    halfGreedyPrefixCommonDenominator, F, reducedDenominator] using hden

theorem halfGreedyPrefixDenominator_dvd_common (n : ℕ) :
    halfGreedyPrefixDenominator n ∣
      halfGreedyPrefixCommonDenominator n := by
  rw [halfGreedyPrefixDenominator_eq_common_reduction]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

theorem halfGreedyPrefixCommonDenominator_eq_reduced_mul_factor
    (n : ℕ) :
    halfGreedyPrefixCommonDenominator n =
      halfGreedyPrefixDenominator n * halfGreedyPrefixReductionFactor n := by
  rw [halfGreedyPrefixReductionFactor]
  exact (Nat.mul_div_cancel'
    (halfGreedyPrefixDenominator_dvd_common n)).symm

theorem halfGreedyPrefixReductionFactor_pos (n : ℕ) :
    0 < halfGreedyPrefixReductionFactor n := by
  rw [halfGreedyPrefixReductionFactor]
  apply Nat.div_pos
  · exact Nat.le_of_dvd (halfGreedyPrefixCommonDenominator_pos n)
      (halfGreedyPrefixDenominator_dvd_common n)
  · exact Rat.den_pos (halfGreedyPrefixRat n)

/-- The common-to-reduced scaling factor is exactly the cancellation gcd of
the actual greedy support's common numerator and denominator. -/
theorem halfGreedyPrefixReductionFactor_eq_gcd (n : ℕ) :
    halfGreedyPrefixReductionFactor n =
      Nat.gcd (halfGreedyPrefixCommonNumerator n)
        (halfGreedyPrefixCommonDenominator n) := by
  let A := halfGreedyPrefixCommonNumerator n
  let B := halfGreedyPrefixCommonDenominator n
  let g := Nat.gcd A B
  have hBpos : 0 < B := halfGreedyPrefixCommonDenominator_pos n
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right A hBpos
  have hgd : g ∣ B := Nat.gcd_dvd_right A B
  obtain ⟨k, hk⟩ := hgd
  have hkpos : 0 < k := by
    by_contra hknot
    have hkzero : k = 0 := by omega
    subst k
    simp at hk
    omega
  rw [halfGreedyPrefixReductionFactor,
    halfGreedyPrefixDenominator_eq_common_reduction]
  change B / (B / g) = g
  rw [hk]
  simp [hgpos, hkpos]

theorem greedyHalfRemainderRat_eq_rawCommon_divInt (n : ℕ) :
    greedyMersenneRemainderRat (1 / 2 : ℚ) n =
      Rat.divInt (halfGreedyRawResidualNumerator n)
        ((2 * halfGreedyPrefixCommonDenominator n : ℕ) : ℤ) := by
  let F := halfGreedyPrefixSupport n
  have h0 : 0 ∉ F := by
    simpa [F, halfGreedyPrefixSupport] using
      zero_not_mem_greedyMersennePrefixRat (1 / 2 : ℚ) n
  have hBpos : 0 < halfGreedyPrefixCommonDenominator n :=
    halfGreedyPrefixCommonDenominator_pos n
  have hB : ((halfGreedyPrefixCommonDenominator n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hBpos.ne'
  have h2B : (((2 * halfGreedyPrefixCommonDenominator n : ℕ) : ℤ) : ℚ) ≠ 0 := by
    positivity
  rw [greedyMersenneRemainderRat_eq_sub_finiteErdosSum]
  change (1 / 2 : ℚ) - finiteErdosSum F 2 = _
  rw [finiteErdosSum_eq_commonNumerator_div_commonDenominator F 2 h0 (by omega)]
  change (1 / 2 : ℚ) -
      (halfGreedyPrefixCommonNumerator n : ℚ) /
        (halfGreedyPrefixCommonDenominator n : ℚ) = _
  rw [Rat.divInt_eq_div]
  field_simp [hB, h2B]
  simp only [halfGreedyRawResidualNumerator]
  push_cast
  ring

theorem halfGreedyRawResidualNumerator_eq_reduced_mul_factor
    (n : ℕ) :
    halfGreedyRawResidualNumerator n =
      (halfGreedyPrefixReductionFactor n : ℤ) *
        halfGreedyResidualDisplayedNumerator n := by
  have heq :
      Rat.divInt (halfGreedyRawResidualNumerator n)
          ((2 * halfGreedyPrefixCommonDenominator n : ℕ) : ℤ) =
        Rat.divInt (halfGreedyResidualDisplayedNumerator n)
          ((2 * halfGreedyPrefixDenominator n : ℕ) : ℤ) := by
    rw [← greedyHalfRemainderRat_eq_rawCommon_divInt,
      ← greedyHalfRemainderRat_eq_displayed_divInt]
  have hB : (((2 * halfGreedyPrefixCommonDenominator n : ℕ) : ℤ) : ℚ) ≠ 0 := by
    have hBnat : 2 * halfGreedyPrefixCommonDenominator n ≠ 0 :=
      Nat.mul_ne_zero (by norm_num)
        (halfGreedyPrefixCommonDenominator_pos n).ne'
    exact_mod_cast hBnat
  have hD : (((2 * halfGreedyPrefixDenominator n : ℕ) : ℤ) : ℚ) ≠ 0 := by
    have hDnat : 2 * halfGreedyPrefixDenominator n ≠ 0 :=
      Nat.mul_ne_zero (by norm_num) (Rat.den_nz (halfGreedyPrefixRat n))
    exact_mod_cast hDnat
  rw [Rat.divInt_eq_div, Rat.divInt_eq_div] at heq
  have hcross := (div_eq_div_iff hB hD).mp heq
  have hcrossInt :
      halfGreedyRawResidualNumerator n *
          ((2 * halfGreedyPrefixDenominator n : ℕ) : ℤ) =
        halfGreedyResidualDisplayedNumerator n *
          ((2 * halfGreedyPrefixCommonDenominator n : ℕ) : ℤ) := by
    exact_mod_cast hcross
  have hBfactor :=
    halfGreedyPrefixCommonDenominator_eq_reduced_mul_factor n
  have hDpos : (0 : ℤ) < (halfGreedyPrefixDenominator n : ℤ) := by
    exact_mod_cast Rat.den_pos (halfGreedyPrefixRat n)
  have hmul :
      (2 * (halfGreedyPrefixDenominator n : ℤ)) *
          halfGreedyRawResidualNumerator n =
        (2 * (halfGreedyPrefixDenominator n : ℤ)) *
          ((halfGreedyPrefixReductionFactor n : ℤ) *
            halfGreedyResidualDisplayedNumerator n) := by
    rw [hBfactor] at hcrossInt
    calc
      (2 * (halfGreedyPrefixDenominator n : ℤ)) *
            halfGreedyRawResidualNumerator n =
          halfGreedyRawResidualNumerator n *
            (2 * (halfGreedyPrefixDenominator n : ℤ)) := by ring
      _ = halfGreedyResidualDisplayedNumerator n *
            (2 * ((halfGreedyPrefixDenominator n *
              halfGreedyPrefixReductionFactor n : ℕ) : ℤ)) := hcrossInt
      _ = (2 * (halfGreedyPrefixDenominator n : ℤ)) *
          ((halfGreedyPrefixReductionFactor n : ℤ) *
            halfGreedyResidualDisplayedNumerator n) := by push_cast; ring
  exact mul_left_cancel₀ (by positivity) hmul

theorem halfGreedyRawNextDyadicExcessNumerator_eq_reduced_mul_factor
    (n : ℕ) :
    halfGreedyRawNextDyadicExcessNumerator n =
      (halfGreedyPrefixReductionFactor n : ℤ) *
        halfGreedyNextDyadicExcessNumerator n := by
  rw [halfGreedyRawNextDyadicExcessNumerator,
    nextDyadicExcessIntNumerator,
    halfGreedyRawResidualNumerator_eq_reduced_mul_factor,
    halfGreedyPrefixCommonDenominator_eq_reduced_mul_factor]
  push_cast
  simp only [halfGreedyNextDyadicExcessNumerator,
    nextDyadicExcessIntNumerator, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- In common-support coordinates the raw residual numerator is the reduced
display numerator multiplied by the exact common-fraction cancellation gcd. -/
theorem halfGreedyRawResidualNumerator_eq_gcd_mul_displayed (n : ℕ) :
    halfGreedyRawResidualNumerator n =
      (Nat.gcd (halfGreedyPrefixCommonNumerator n)
          (halfGreedyPrefixCommonDenominator n) : ℤ) *
        halfGreedyResidualDisplayedNumerator n := by
  rw [halfGreedyRawResidualNumerator_eq_reduced_mul_factor,
    halfGreedyPrefixReductionFactor_eq_gcd]

/-- The same cancellation gcd scales the dyadic excess numerator, so the
raw support lattice and reduced primitive lattice carry identical signs and
strict cap/skip comparisons. -/
theorem halfGreedyRawNextDyadicExcessNumerator_eq_gcd_mul_reduced (n : ℕ) :
    halfGreedyRawNextDyadicExcessNumerator n =
      (Nat.gcd (halfGreedyPrefixCommonNumerator n)
          (halfGreedyPrefixCommonDenominator n) : ℤ) *
        halfGreedyNextDyadicExcessNumerator n := by
  rw [halfGreedyRawNextDyadicExcessNumerator_eq_reduced_mul_factor,
    halfGreedyPrefixReductionFactor_eq_gcd]

theorem halfGreedyRawExcessBound_iff_reduced (n : ℕ) :
    3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
        halfGreedyRawNextDyadicExcessNumerator n) ≤
          (halfGreedyPrefixCommonDenominator n : ℤ) ↔
      3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
        halfGreedyNextDyadicExcessNumerator n) ≤
          (halfGreedyPrefixDenominator n : ℤ) := by
  rw [halfGreedyRawNextDyadicExcessNumerator_eq_reduced_mul_factor,
    halfGreedyPrefixCommonDenominator_eq_reduced_mul_factor]
  push_cast
  have hg : (0 : ℤ) < (halfGreedyPrefixReductionFactor n : ℤ) := by
    exact_mod_cast halfGreedyPrefixReductionFactor_pos n
  have hleft :
      3 * ((2 : ℤ) ^ (n + 1) *
          ((halfGreedyPrefixReductionFactor n : ℤ) *
            halfGreedyNextDyadicExcessNumerator n)) =
        (halfGreedyPrefixReductionFactor n : ℤ) *
          (3 * ((2 : ℤ) ^ (n + 1) *
            halfGreedyNextDyadicExcessNumerator n)) := by ring
  have hright :
      (halfGreedyPrefixDenominator n : ℤ) *
          (halfGreedyPrefixReductionFactor n : ℤ) =
        (halfGreedyPrefixReductionFactor n : ℤ) *
          (halfGreedyPrefixDenominator n : ℤ) := by ring
  rw [hleft, hright]
  constructor
  · intro h
    by_contra hnot
    have hlt := lt_of_not_ge hnot
    have hcontra := mul_lt_mul_of_pos_left hlt hg
    exact (not_lt_of_ge h) hcontra
  · intro h
    exact mul_le_mul_of_nonneg_left h hg.le

def HalfGreedyRawSupportExcessBound : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
          halfGreedyRawNextDyadicExcessNumerator n) ≤
        (halfGreedyPrefixCommonDenominator n : ℤ)

theorem halfGreedyRawSupportExcessBound_iff :
    HalfGreedyRawSupportExcessBound ↔ HalfGreedySkippedExcessBound := by
  constructor
  · intro hraw n hskip
    exact (halfGreedyRawExcessBound_iff_reduced n).1
      (hraw n hskip)
  · intro hred n hskip
    exact (halfGreedyRawExcessBound_iff_reduced n).2
      (hred n hskip)

theorem greedyHalfRemainderRat_le_twoChannelCap_iff_rawExcess
    (n : ℕ) :
    greedyMersenneRemainderRat (1 / 2 : ℚ) n ≤
        (1 / (2 : ℚ)) ^ (n + 1) +
          (1 / 3 : ℚ) * (1 / 4 : ℚ) ^ (n + 1) ↔
      3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
          halfGreedyRawNextDyadicExcessNumerator n) ≤
        (halfGreedyPrefixCommonDenominator n : ℤ) := by
  have hB : 0 < halfGreedyPrefixCommonDenominator n :=
    halfGreedyPrefixCommonDenominator_pos n
  have hgeneric := divInt_le_nextTwoChannelCap_iff_excess
    (halfGreedyRawResidualNumerator n) n
    (halfGreedyPrefixCommonDenominator n) hB
  rw [← greedyHalfRemainderRat_eq_rawCommon_divInt] at hgeneric
  simpa only [halfGreedyRawNextDyadicExcessNumerator] using hgeneric

theorem greedyHalfRemainderRat_lt_mersenneWeight_iff_rawExcess
    (n : ℕ) :
    greedyMersenneRemainderRat (1 / 2 : ℚ) n <
        mersenneWeightRat (n + 1) ↔
      2 * halfGreedyRawNextDyadicExcessNumerator n <
        halfGreedyRawResidualNumerator n := by
  have hB : 0 < halfGreedyPrefixCommonDenominator n :=
    halfGreedyPrefixCommonDenominator_pos n
  have hgeneric := divInt_lt_mersenneWeightRat_succ_iff_excess
    (halfGreedyRawResidualNumerator n) n
    (halfGreedyPrefixCommonDenominator n) hB
  rw [← greedyHalfRemainderRat_eq_rawCommon_divInt] at hgeneric
  simpa only [halfGreedyRawNextDyadicExcessNumerator] using hgeneric

theorem mem_halfGreedyPrefixSupport_iff
    {n a : ℕ} (ha : 0 < a) (han : a ≤ n) :
    a ∈ halfGreedyPrefixSupport n ↔
      mersenneWeightRat a ≤
        (1 / 2 : ℚ) -
          finiteErdosSum (halfGreedyPrefixSupport (a - 1)) 2 := by
  classical
  have haeq : (a - 1) + 1 = a := by omega
  have hmem : a ∈ greedyMersennePrefixRat (1 / 2 : ℚ) n ↔
      mersenneWeightRat a ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) (a - 1) := by
    unfold greedyMersennePrefixRat
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨k, ⟨hklt, htake⟩, hka⟩
      have hk : k = a - 1 := by omega
      simpa [hk, haeq] using htake
    · intro htake
      refine ⟨a - 1, ⟨by omega, ?_⟩, haeq⟩
      simpa [haeq] using htake
  rw [halfGreedyPrefixSupport, hmem,
    greedyMersenneRemainderRat_eq_sub_finiteErdosSum]
  rfl


/-- The triple-depth take-run socket is not merely sufficient: after the
forced-block theorem, it is exactly equivalent to the original skipped-rank
excess producer.  This records the endpoint of what uniform run geometry can
remove from the arithmetic obligation. -/
theorem halfGreedyThreeDepthTakeRunExcessBound_iff_skippedExcessBound :
    HalfGreedyThreeDepthTakeRunExcessBound ↔
      HalfGreedySkippedExcessBound := by
  constructor
  · exact halfGreedySkippedExcessBound_of_threeDepthTakeRun
  · intro hskip n hn _hrun
    exact hskip n hn

/-- A skipped, dyadically unsafe, two-channel-cap-violating half-prefix is
exactly a point of the primitive integer lattice cut out by the three strict
inequalities below.  The raw support coordinates introduced above retain the
additional common-numerator information that reduction erases. -/
theorem greedyHalf_badSkipCapViolation_iff_primitiveLattice (n : ℕ) :
    (halfDyadicCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n <
          mersenneWeight (n + 1) ∧
        halfTwoChannelCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n) ↔
      (0 < halfGreedyNextDyadicExcessNumerator n ∧
        2 * halfGreedyNextDyadicExcessNumerator n <
          halfGreedyResidualDisplayedNumerator n ∧
        (halfGreedyPrefixDenominator n : ℤ) <
          3 * (((2 ^ (n + 1) : ℕ) : ℤ) *
            halfGreedyNextDyadicExcessNumerator n)) := by
  rw [nextDyadic_lt_greedyHalfRemainder_iff_excess_pos,
    greedyHalfRemainder_lt_mersenneWeight_iff_excess,
    twoChannelCap_lt_greedyHalfRemainder_iff_excess]

/-! ## Actual-prefix support-tail coordinate -/

noncomputable def halfGreedyPrefixCoeffTail (n : ℕ) : ℝ :=
  binaryCoeffTail
    (supportCoeff (↑(halfGreedyPrefixSupport n) : Set ℕ)) (n + 1)

noncomputable def halfGreedyPrefixIntegerCarry (n : ℕ) : ℤ :=
  affineBinaryOrbit
    (fun k : ℕ ↦
      (supportCoeff (↑(halfGreedyPrefixSupport n) : Set ℕ) (k + 1) : ℤ))
    1 n

/-- Signed distance by which the actual finite-prefix coefficient tail lies
below the preceding integer carry.  The `-1` exactly removes the first
dyadic channel at the next rank. -/
noncomputable def halfGreedyPrefixSupportTailGap (n : ℕ) : ℝ :=
  (halfGreedyPrefixIntegerCarry n : ℝ) - 1 -
    halfGreedyPrefixCoeffTail n

theorem halfGreedyPrefixSupport_subset_Iic_succ (n : ℕ) :
    (↑(halfGreedyPrefixSupport n) : Set ℕ) ⊆ Set.Iic (n + 1) := by
  intro a ha
  unfold halfGreedyPrefixSupport greedyMersennePrefixRat at ha
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
  have hklt : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  change k + 1 ≤ n + 1
  omega

theorem one_not_mem_halfGreedyPrefixSupport (n : ℕ) :
    1 ∉ halfGreedyPrefixSupport n := by
  classical
  intro h
  unfold halfGreedyPrefixSupport greedyMersennePrefixRat at h
  obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.mp h
  have htake := (Finset.mem_filter.mp hk).2
  have hk0 : k = 0 := by omega
  subst k
  norm_num [mersenneWeightRat, greedyMersenneRemainderRat] at htake

theorem greedyHalfRemainder_eq_integerCarry_sub_coeffTail_div_pow
    (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n =
      ((halfGreedyPrefixIntegerCarry n : ℝ) -
          halfGreedyPrefixCoeffTail n) / (2 : ℝ) ^ (n + 1) := by
  let F := halfGreedyPrefixSupport n
  let A : Set ℕ := ↑F
  have hone : 1 ∉ A := by
    simpa [A, F] using one_not_mem_halfGreedyPrefixSupport n
  have hsub : A ∩ Set.Iic (n + 1) = A := by
    apply Set.inter_eq_left.mpr
    simpa [A, F] using halfGreedyPrefixSupport_subset_Iic_succ n
  have hfinite := halfFinitePrefix_residual_eq_pow_mul_integerCarry_sub_finiteTail
    A hone n
  rw [hsub] at hfinite
  have hresRat := greedyMersenneRemainderRat_eq_sub_finiteErdosSum
    (1 / 2 : ℚ) n
  have hcast := congrArg (fun q : ℚ ↦ (q : ℝ)) hresRat
  change
    ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) =
      (((1 / 2 : ℚ) - finiteErdosSum
        (greedyMersennePrefixRat (1 / 2 : ℚ) n) 2 : ℚ) : ℝ) at hcast
  rw [cast_greedyMersenneRemainderRat] at hcast
  have hseries := erdosSupportSeries_finset_eq_cast_finiteErdosSum F
  have hres :
      greedyMersenneRemainder (1 / 2 : ℝ) n =
        (1 : ℝ) / 2 - erdosSupportSeries 2 A := by
    rw [hseries]
    simpa [A, F, halfGreedyPrefixSupport] using hcast
  rw [hres]
  simpa [halfGreedyPrefixIntegerCarry, halfGreedyPrefixCoeffTail, A, F]
    using hfinite

/-- The support-tail gap is not a new scalar relaxation: it is exactly the
primitive dyadic excess ratio `Eₙ / Dₙ`.  Its extra content is the
decomposition of that ratio as an integer carry minus the true finite-support
coefficient tail. -/
theorem halfGreedyPrefixSupportTailGap_eq_excess_div_denominator
    (n : ℕ) :
    halfGreedyPrefixSupportTailGap n =
      (halfGreedyNextDyadicExcessNumerator n : ℝ) /
        (halfGreedyPrefixDenominator n : ℝ) := by
  have hrem :=
    greedyHalfRemainder_eq_integerCarry_sub_coeffTail_div_pow n
  have hP : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  have hscaled :
      (halfGreedyPrefixIntegerCarry n : ℝ) -
          halfGreedyPrefixCoeffTail n =
        (2 : ℝ) ^ (n + 1) *
          greedyMersenneRemainder (1 / 2 : ℝ) n := by
    rw [hrem]
    field_simp
  have hrat := greedyHalfRemainderRat_eq_displayed_divInt n
  rw [Rat.divInt_eq_div] at hrat
  have hcast := congrArg (fun q : ℚ ↦ (q : ℝ)) hrat
  have hdisplay :
      greedyMersenneRemainder (1 / 2 : ℝ) n =
        (halfGreedyResidualDisplayedNumerator n : ℝ) /
          (2 * (halfGreedyPrefixDenominator n : ℝ)) := by
    simpa using hcast
  have hD : (halfGreedyPrefixDenominator n : ℝ) ≠ 0 := by
    exact_mod_cast Rat.den_nz (halfGreedyPrefixRat n)
  unfold halfGreedyPrefixSupportTailGap
  rw [show
    (halfGreedyPrefixIntegerCarry n : ℝ) - 1 -
        halfGreedyPrefixCoeffTail n =
      ((halfGreedyPrefixIntegerCarry n : ℝ) -
        halfGreedyPrefixCoeffTail n) - 1 by ring,
    hscaled, hdisplay]
  simp only [halfGreedyNextDyadicExcessNumerator,
    nextDyadicExcessIntNumerator]
  push_cast
  rw [pow_succ]
  field_simp

theorem greedyHalf_badSkipCapViolation_iff_supportCoeffTailGap
    (n : ℕ) :
    (halfDyadicCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n <
          mersenneWeight (n + 1) ∧
        halfTwoChannelCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n) ↔
      ((1 : ℝ) / (3 * (2 : ℝ) ^ (n + 1)) <
          halfGreedyPrefixSupportTailGap n ∧
        halfGreedyPrefixSupportTailGap n <
          (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) := by
  rw [greedyHalfRemainder_eq_integerCarry_sub_coeffTail_div_pow]
  unfold halfGreedyPrefixSupportTailGap
  unfold halfDyadicCap halfTwoChannelCap mersenneWeight
  have hfour : (4 : ℝ) ^ (n + 1) =
      (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (n + 1) := by
    rw [← mul_pow]
    norm_num
  rw [div_pow, div_pow, hfour]
  simp only [one_pow]
  have hp : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  have hm : (0 : ℝ) < (2 : ℝ) ^ (n + 1) - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ (n + 1) := by
      exact one_lt_pow₀ (by norm_num) (by omega)
    linarith
  constructor
  · rintro ⟨_, hskip, hcap⟩
    constructor
    · field_simp at hcap ⊢
      nlinarith
    · rw [div_lt_div_iff₀ hp hm] at hskip
      field_simp at hskip ⊢
      nlinarith
  · rintro ⟨hlow, hupp⟩
    constructor
    · field_simp at hlow ⊢
      nlinarith
    constructor
    · rw [div_lt_div_iff₀ hp hm]
      field_simp at hupp ⊢
      nlinarith
    · field_simp at hlow ⊢
      nlinarith


/-! ## Exact reduced take-step cancellation -/

def reducedTakeStepNumerator (N D₁ q₁ : ℕ) : ℕ :=
  N * q₁ + D₁

def reducedTakeStepCancellation (N d D₁ q₁ : ℕ) : ℕ :=
  Nat.gcd (reducedTakeStepNumerator N D₁ q₁) d

def reducedTakeStepDenominator (N d D₁ q₁ : ℕ) : ℕ :=
  (d / reducedTakeStepCancellation N d D₁ q₁) * D₁ * q₁

/-- The new prefix numerator is coprime to both quotient-denominator
channels.  Consequently `e = gcd(U,d)` is the complete cancellation, not
merely a divisor of it. -/
theorem reducedTakeStep_coprime
    (N d D₁ q₁ : ℕ)
    (hd : 0 < d)
    (hND : Nat.Coprime N (d * D₁))
    (hDq : Nat.Coprime D₁ q₁) :
    let U := reducedTakeStepNumerator N D₁ q₁
    let e := reducedTakeStepCancellation N d D₁ q₁
    Nat.Coprime (U / e) ((d / e) * D₁ * q₁) := by
  dsimp only
  let U := reducedTakeStepNumerator N D₁ q₁
  let e := Nat.gcd U d
  have hepos : 0 < e := Nat.gcd_pos_of_pos_right U hd
  have heU : e ∣ U := Nat.gcd_dvd_left U d
  have hed : e ∣ d := Nat.gcd_dvd_right U d
  have hN_D₁ : Nat.Coprime N D₁ :=
    hND.coprime_dvd_right (dvd_mul_left D₁ d)
  have hq_D₁ : Nat.Coprime q₁ D₁ := hDq.symm
  have hNq_D₁ : Nat.Coprime (N * q₁) D₁ :=
    hN_D₁.mul_left hq_D₁
  have hU_D₁ : Nat.Coprime U D₁ := by
    simpa [U, reducedTakeStepNumerator] using
      (Nat.coprime_add_self_left.mpr hNq_D₁)
  have hU_q₁ : Nat.Coprime U q₁ := by
    simpa [U, reducedTakeStepNumerator] using
      (Nat.coprime_mul_right_add_left D₁ q₁ N).mpr hDq
  have hU_tail : Nat.Coprime U (D₁ * q₁) :=
    hU_D₁.mul_right hU_q₁
  have hUred_tail : Nat.Coprime (U / e) (D₁ * q₁) :=
    hU_tail.coprime_dvd_left (Nat.div_dvd_of_dvd heU)
  have hUred_dred : Nat.Coprime (U / e) (d / e) :=
    Nat.coprime_div_gcd_div_gcd hepos
  simpa [Nat.mul_assoc] using hUred_dred.mul_right hUred_tail

/-- Exact rational take-step normal form. -/
theorem reducedTakeStep_eq
    (N d D₁ q₁ : ℕ)
    (hd : 0 < d) (hD₁ : 0 < D₁) (hq₁ : 0 < q₁) :
    let U := reducedTakeStepNumerator N D₁ q₁
    let e := reducedTakeStepCancellation N d D₁ q₁
    (N : ℚ) / (d * D₁ : ℕ) + 1 / (d * q₁ : ℕ) =
      ((U / e : ℕ) : ℚ) / (((d / e) * D₁ * q₁ : ℕ) : ℚ) := by
  dsimp only
  let U := reducedTakeStepNumerator N D₁ q₁
  let e := Nat.gcd U d
  have hepos : 0 < e := Nat.gcd_pos_of_pos_right U hd
  have heU : e ∣ U := Nat.gcd_dvd_left U d
  have hed : e ∣ d := Nat.gcd_dvd_right U d
  have hdred : 0 < d / e :=
    Nat.div_pos (Nat.le_of_dvd hd hed) hepos
  have hrawDen : ((d * D₁ * q₁ : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos hd hD₁) hq₁).ne'
  have hredDen : ((((d / e) * D₁ * q₁ : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos hdred hD₁) hq₁).ne'
  have hraw :
      (N : ℚ) / (d * D₁ : ℕ) + 1 / (d * q₁ : ℕ) =
        (U : ℚ) / (d * D₁ * q₁ : ℕ) := by
    have hdD₁ : (((d * D₁ : ℕ) : ℚ)) ≠ 0 := by positivity
    have hdq₁ : (((d * q₁ : ℕ) : ℚ)) ≠ 0 := by positivity
    field_simp [hdD₁, hdq₁, hrawDen]
    simp only [U, reducedTakeStepNumerator]
    push_cast
    ring
  have hcrossNat :
      U * ((d / e) * D₁ * q₁) =
        (U / e) * (d * D₁ * q₁) := by
    have hcross := mul_div_cross_of_dvd e U d hepos heU hed
    calc
      U * ((d / e) * D₁ * q₁) =
          (U * (d / e)) * D₁ * q₁ := by ring
      _ = ((U / e) * d) * D₁ * q₁ := by rw [hcross]
      _ = (U / e) * (d * D₁ * q₁) := by ring
  have hred :
      (U : ℚ) / (d * D₁ * q₁ : ℕ) =
        ((U / e : ℕ) : ℚ) / (((d / e) * D₁ * q₁ : ℕ) : ℚ) := by
    rw [div_eq_div_iff hrawDen hredDen]
    exact_mod_cast hcrossNat
  exact hraw.trans hred

/-- Division-free displayed-residual recurrence.  If
`p = d*D₁ - 2N`, then after taking `1/(d*q₁)` the displayed numerator
`p' = (d/e)D₁q₁ - 2(U/e)` obeys

  `e p' = p q₁ - 2D₁`.
-/
theorem reducedTakeStep_residualNumerator
    (N d D₁ q₁ : ℕ) (hd : 0 < d) :
    let U := reducedTakeStepNumerator N D₁ q₁
    let e := reducedTakeStepCancellation N d D₁ q₁
    (e : ℤ) *
        ((((d / e) * D₁ * q₁ : ℕ) : ℤ) -
          2 * ((U / e : ℕ) : ℤ)) =
      ((((d * D₁ : ℕ) : ℤ) - 2 * (N : ℤ)) * (q₁ : ℤ) -
        2 * (D₁ : ℤ)) := by
  dsimp only
  let U := reducedTakeStepNumerator N D₁ q₁
  let e := Nat.gcd U d
  have heU : e ∣ U := Nat.gcd_dvd_left U d
  have hed : e ∣ d := Nat.gcd_dvd_right U d
  have hUcancel : (e : ℤ) * ((U / e : ℕ) : ℤ) = (U : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' heU
  have hdcancel : (e : ℤ) * ((d / e : ℕ) : ℤ) = (d : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hed
  simp only [U, reducedTakeStepNumerator] at ⊢
  push_cast at ⊢
  calc
    (e : ℤ) *
        (((d / e : ℕ) : ℤ) * (D₁ : ℤ) * (q₁ : ℤ) -
          2 * ((U / e : ℕ) : ℤ)) =
      ((e : ℤ) * ((d / e : ℕ) : ℤ)) * (D₁ : ℤ) * (q₁ : ℤ) -
        2 * ((e : ℤ) * ((U / e : ℕ) : ℤ)) := by ring
    _ = (d : ℤ) * (D₁ : ℤ) * (q₁ : ℤ) - 2 * (U : ℤ) := by
      rw [hdcancel, hUcancel]
    _ = (((d : ℤ) * (D₁ : ℤ) - 2 * (N : ℤ)) * (q₁ : ℤ) -
        2 * (D₁ : ℤ)) := by
      simp only [U, reducedTakeStepNumerator]
      push_cast
      ring

/-- Exact cancellation-gcd theorem for a positive take.  The extra
cancellation in the residual numerator is exactly the same `e` as the new
prefix-numerator cancellation. -/
theorem reducedTakeStep_residual_gcd
    (N d D₁ q₁ : ℕ)
    (hd : 0 < d) (hdodd : Odd d)
    (hNle : 2 * N ≤ d * D₁)
    (htake : 2 * D₁ ≤ (d * D₁ - 2 * N) * q₁) :
    let U := reducedTakeStepNumerator N D₁ q₁
    let e := reducedTakeStepCancellation N d D₁ q₁
    let p := d * D₁ - 2 * N
    let R := p * q₁ - 2 * D₁
    Nat.gcd R d = e := by
  dsimp only
  let U := reducedTakeStepNumerator N D₁ q₁
  let e := Nat.gcd U d
  let p := d * D₁ - 2 * N
  let R := p * q₁ - 2 * D₁
  have hpadd : p + 2 * N = d * D₁ := by
    simpa [p] using Nat.sub_add_cancel hNle
  have hRadd : R + 2 * U = d * (D₁ * q₁) := by
    have hsub : (p * q₁ - 2 * D₁) + 2 * D₁ = p * q₁ :=
      Nat.sub_add_cancel htake
    have htwoNq : 2 * (N * q₁) = 2 * N * q₁ := by ring
    simp only [R, U, reducedTakeStepNumerator]
    calc
      (p * q₁ - 2 * D₁) + 2 * (N * q₁ + D₁) =
          ((p * q₁ - 2 * D₁) + 2 * D₁) + 2 * N * q₁ := by
            rw [mul_add, htwoNq]
            ac_rfl
      _ = p * q₁ + 2 * N * q₁ := by rw [hsub]
      _ = (p + 2 * N) * q₁ := by ring
      _ = d * (D₁ * q₁) := by rw [hpadd]; ring
  apply Nat.dvd_antisymm
  · let k := Nat.gcd R d
    have hkR : k ∣ R := Nat.gcd_dvd_left R d
    have hkd : k ∣ d := Nat.gcd_dvd_right R d
    have hkSum : k ∣ R + 2 * U := by
      rw [hRadd]
      exact dvd_mul_of_dvd_left hkd (D₁ * q₁)
    have hk2U : k ∣ 2 * U := (Nat.dvd_add_right hkR).mp hkSum
    have h2d : Nat.Coprime 2 d := Nat.coprime_two_left.mpr hdodd
    have hk2 : Nat.Coprime k 2 :=
      (h2d.coprime_dvd_right hkd).symm
    have hkU : k ∣ U := (hk2.dvd_mul_left).mp hk2U
    exact Nat.dvd_gcd hkU hkd
  · have heU : e ∣ U := Nat.gcd_dvd_left U d
    have hed : e ∣ d := Nat.gcd_dvd_right U d
    have heSum : e ∣ R + 2 * U := by
      rw [hRadd]
      exact dvd_mul_of_dvd_left hed (D₁ * q₁)
    have he2U : e ∣ 2 * U := dvd_mul_of_dvd_right heU 2
    have heR : e ∣ R := (Nat.dvd_add_right he2U).mp (by
      simpa [Nat.add_comm] using heSum)
    exact Nat.dvd_gcd heR hed

/-! ## Actual greedy take-step specialization -/

theorem greedyMersenneRemainderRat_nonneg_of_nonneg
    {x : ℚ} (hx : 0 ≤ x) :
    ∀ n : ℕ, 0 ≤ greedyMersenneRemainderRat x n := by
  intro n
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [greedyMersenneRemainderRat_succ]
      split
      · rename_i htake
        exact sub_nonneg.mpr htake
      · exact ih

theorem halfGreedyPrefixRat_nonneg (n : ℕ) :
    0 ≤ halfGreedyPrefixRat n := by
  rw [halfGreedyPrefixRat,
    finiteErdosSum_greedyMersennePrefixRat]
  exact Finset.sum_nonneg fun k hk => by
    split
    · exact (mersenneWeightRat_pos (n := k + 1) (by omega)).le
    · exact le_rfl

theorem halfGreedyPrefixRat_le_half (n : ℕ) :
    halfGreedyPrefixRat n ≤ (1 / 2 : ℚ) := by
  have hrem := greedyMersenneRemainderRat_eq_sub_finiteErdosSum
    (1 / 2 : ℚ) n
  have hrem0 := greedyMersenneRemainderRat_nonneg_of_nonneg
    (x := (1 / 2 : ℚ)) (by norm_num) n
  change greedyMersenneRemainderRat (1 / 2 : ℚ) n =
      (1 / 2 : ℚ) - halfGreedyPrefixRat n at hrem
  linarith

/-- Processing a taken rank adds exactly that Mersenne unit fraction to the
finite reduced prefix. -/
theorem halfGreedyPrefixRat_succ_of_take
    (n : ℕ)
    (htake : mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n) :
    halfGreedyPrefixRat (n + 1) =
      halfGreedyPrefixRat n + mersenneWeightRat (n + 1) := by
  unfold halfGreedyPrefixRat
  rw [finiteErdosSum_greedyMersennePrefixRat,
    finiteErdosSum_greedyMersennePrefixRat,
    Finset.sum_range_succ, if_pos htake]

/-- Processing a skipped rank leaves the exact reduced prefix unchanged. -/
theorem halfGreedyPrefixRat_succ_of_skip
    (n : ℕ)
    (hskip : ¬ mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n) :
    halfGreedyPrefixRat (n + 1) = halfGreedyPrefixRat n := by
  unfold halfGreedyPrefixRat
  rw [finiteErdosSum_greedyMersennePrefixRat,
    finiteErdosSum_greedyMersennePrefixRat,
    Finset.sum_range_succ, if_neg hskip, add_zero]

theorem halfGreedyPrefixDenominator_succ_of_skip
    (n : ℕ)
    (hskip : ¬ mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n) :
    halfGreedyPrefixDenominator (n + 1) =
      halfGreedyPrefixDenominator n := by
  simp only [halfGreedyPrefixDenominator,
    halfGreedyPrefixRat_succ_of_skip n hskip]

theorem halfGreedyResidualDisplayedNumerator_succ_of_skip
    (n : ℕ)
    (hskip : ¬ mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n) :
    halfGreedyResidualDisplayedNumerator (n + 1) =
      halfGreedyResidualDisplayedNumerator n := by
  simp only [halfGreedyResidualDisplayedNumerator,
    halfGreedyPrefixDenominator_succ_of_skip n hskip,
    halfGreedyPrefixRat_succ_of_skip n hskip]

/-- The actual skipped branch obeys the affine excess recurrence with no
hidden reduction factor, because the reduced prefix itself is unchanged. -/
theorem halfGreedyNextDyadicExcessNumerator_succ_of_skip
    (n : ℕ)
    (hskip : ¬ mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n) :
    halfGreedyNextDyadicExcessNumerator (n + 1) =
      2 * halfGreedyNextDyadicExcessNumerator n +
        (halfGreedyPrefixDenominator n : ℤ) := by
  simp only [halfGreedyNextDyadicExcessNumerator,
    halfGreedyResidualDisplayedNumerator_succ_of_skip n hskip,
    halfGreedyPrefixDenominator_succ_of_skip n hskip]
  exact nextDyadicExcessIntNumerator_succ
    (halfGreedyResidualDisplayedNumerator n) n
      (halfGreedyPrefixDenominator n)

/-!
At a taken rank `n+1`, map the actual prefix into the generic take-step
coordinates as follows:

* `x = halfGreedyPrefixRat n`, `N = |x.num|`, `D = x.den`;
* `q = 2^(n+1)-1`, `d = gcd D q`;
* `D₁ = D/d`, `q₁ = q/d`;
* `U = N*q₁ + D₁`, `e = gcd U d`;
* `D' = (d/e)*D₁*q₁`.

The theorem identifies the next actual prefix's reduced numerator and
denominator and then instantiates the displayed residual recurrence

  `e p_(n+1) = p_n q₁ - 2D₁`.
-/
theorem halfGreedy_takenRank_reducedTakeStep
    (n : ℕ)
    (htake : mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n) :
    let x := halfGreedyPrefixRat n
    let N := x.num.natAbs
    let D := x.den
    let q := 2 ^ (n + 1) - 1
    let d := Nat.gcd D q
    let D₁ := D / d
    let q₁ := q / d
    let U := reducedTakeStepNumerator N D₁ q₁
    let e := reducedTakeStepCancellation N d D₁ q₁
    let Dnext := reducedTakeStepDenominator N d D₁ q₁
    (halfGreedyPrefixRat (n + 1)).num = (U / e : ℕ) ∧
      (halfGreedyPrefixRat (n + 1)).den = Dnext ∧
      (e : ℤ) * halfGreedyResidualDisplayedNumerator (n + 1) =
        halfGreedyResidualDisplayedNumerator n * (q₁ : ℤ) -
          2 * (D₁ : ℤ) := by
  dsimp only
  let x := halfGreedyPrefixRat n
  let N := x.num.natAbs
  let D := x.den
  let q := 2 ^ (n + 1) - 1
  let d := Nat.gcd D q
  let D₁ := D / d
  let q₁ := q / d
  let U := reducedTakeStepNumerator N D₁ q₁
  let e := reducedTakeStepCancellation N d D₁ q₁
  let Dnext := reducedTakeStepDenominator N d D₁ q₁
  have hx0 : 0 ≤ x := by
    simpa [x] using halfGreedyPrefixRat_nonneg n
  have hxnum0 : 0 ≤ x.num := Rat.num_nonneg.mpr hx0
  have hNcast : (N : ℤ) = x.num := by
    simpa [N, Int.natAbs_of_nonneg hxnum0]
  have hDpos : 0 < D := by simpa [D] using Rat.den_pos x
  have hqpos : 0 < q := by
    dsimp [q]
    exact pow_sub_one_pos_of_ne_zero 2 (n + 1) (by omega) (by omega)
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left q hDpos
  have hdD : d ∣ D := Nat.gcd_dvd_left D q
  have hdq : d ∣ q := Nat.gcd_dvd_right D q
  have hDfac : d * D₁ = D := by
    simpa [D₁] using Nat.mul_div_cancel' hdD
  have hqfac : d * q₁ = q := by
    simpa [q₁] using Nat.mul_div_cancel' hdq
  have hD₁pos : 0 < D₁ := by
    exact Nat.div_pos (Nat.le_of_dvd hDpos hdD) hdpos
  have hq₁pos : 0 < q₁ := by
    exact Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos
  have hND : Nat.Coprime N (d * D₁) := by
    rw [hDfac]
    simpa [N, D] using x.reduced
  have hDq : Nat.Coprime D₁ q₁ := by
    simpa [D₁, q₁, d] using
      Nat.coprime_div_gcd_div_gcd hdpos
  have hcurrent : (N : ℚ) / (d * D₁ : ℕ) = x := by
    rw [hDfac]
    change (N : ℚ) / (D : ℕ) = x
    rw [show (N : ℚ) = (x.num : ℚ) by exact_mod_cast hNcast]
    exact Rat.num_div_den x
  have hweight :
      (1 : ℚ) / (d * q₁ : ℕ) = mersenneWeightRat (n + 1) := by
    rw [hqfac]
    simp [q, mersenneWeightRat, natCast_pow_sub_one]
  have hstep := reducedTakeStep_eq N d D₁ q₁
    hdpos hD₁pos hq₁pos
  have hnext :
      halfGreedyPrefixRat (n + 1) =
        ((U / e : ℕ) : ℚ) / (Dnext : ℚ) := by
    calc
      halfGreedyPrefixRat (n + 1) =
          halfGreedyPrefixRat n + mersenneWeightRat (n + 1) :=
        halfGreedyPrefixRat_succ_of_take n htake
      _ = (N : ℚ) / (d * D₁ : ℕ) + 1 / (d * q₁ : ℕ) := by
        rw [hcurrent, hweight]
      _ = ((U / e : ℕ) : ℚ) / (Dnext : ℚ) := by
        simpa [U, e, Dnext, reducedTakeStepDenominator] using hstep
  have hcopNext : Nat.Coprime (U / e) Dnext := by
    simpa [U, e, Dnext, reducedTakeStepDenominator] using
      reducedTakeStep_coprime N d D₁ q₁ hdpos hND hDq
  have hepos : 0 < e := by
    exact Nat.gcd_pos_of_pos_right U hdpos
  have hed : e ∣ d := Nat.gcd_dvd_right U d
  have hdredpos : 0 < d / e :=
    Nat.div_pos (Nat.le_of_dvd hdpos hed) hepos
  have hDnextpos : 0 < Dnext := by
    simpa [Dnext, reducedTakeStepDenominator, U, e] using
      Nat.mul_pos (Nat.mul_pos hdredpos hD₁pos) hq₁pos
  have hnumNext :
      (halfGreedyPrefixRat (n + 1)).num = (U / e : ℕ) := by
    rw [hnext]
    have hcopInt :
        Nat.Coprime (((U / e : ℕ) : ℤ).natAbs)
          ((Dnext : ℤ).natAbs) := by
      simpa using hcopNext
    simpa using Rat.num_div_eq_of_coprime
      (a := ((U / e : ℕ) : ℤ)) (b := (Dnext : ℤ))
      (by exact_mod_cast hDnextpos) hcopInt
  have hdenNext :
      (halfGreedyPrefixRat (n + 1)).den = Dnext := by
    rw [hnext]
    exact den_natCast_div_natCast_of_coprime
      (U / e) Dnext hDnextpos.ne' hcopNext
  have hpCurrent :
      halfGreedyResidualDisplayedNumerator n =
        (D : ℤ) - 2 * (N : ℤ) := by
    simp only [halfGreedyResidualDisplayedNumerator,
      halfGreedyPrefixDenominator]
    change (D : ℤ) - 2 * x.num = _
    rw [← hNcast]
  have hpNext :
      halfGreedyResidualDisplayedNumerator (n + 1) =
        (Dnext : ℤ) - 2 * ((U / e : ℕ) : ℤ) := by
    simp only [halfGreedyResidualDisplayedNumerator,
      halfGreedyPrefixDenominator]
    rw [hnumNext, hdenNext]
  refine ⟨hnumNext, hdenNext, ?_⟩
  rw [hpNext, hpCurrent]
  change (e : ℤ) *
      ((Dnext : ℤ) - 2 * ((U / e : ℕ) : ℤ)) =
    ((D : ℤ) - 2 * (N : ℤ)) * (q₁ : ℤ) - 2 * (D₁ : ℤ)
  simpa only [U, e, Dnext, reducedTakeStepDenominator, hDfac] using
    reducedTakeStep_residualNumerator N d D₁ q₁ hdpos

/-- At an actual taken rank, the residual-numerator cancellation is exactly
the prefix take-step cancellation `e = gcd (N*q₁ + D₁) d`. -/
theorem halfGreedy_takenRank_residualCancellation
    (n : ℕ)
    (htake : mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n) :
    let x := halfGreedyPrefixRat n
    let N := x.num.natAbs
    let D := x.den
    let q := 2 ^ (n + 1) - 1
    let d := Nat.gcd D q
    let D₁ := D / d
    let q₁ := q / d
    let e := reducedTakeStepCancellation N d D₁ q₁
    let pNat := D - 2 * N
    Nat.gcd (pNat * q₁ - 2 * D₁) d = e := by
  dsimp only
  let x := halfGreedyPrefixRat n
  let N := x.num.natAbs
  let D := x.den
  let q := 2 ^ (n + 1) - 1
  let d := Nat.gcd D q
  let D₁ := D / d
  let q₁ := q / d
  let e := reducedTakeStepCancellation N d D₁ q₁
  let pNat := D - 2 * N
  have hx0 : 0 ≤ x := by
    simpa [x] using halfGreedyPrefixRat_nonneg n
  have hxle : x ≤ (1 / 2 : ℚ) := by
    simpa [x] using halfGreedyPrefixRat_le_half n
  have hxnum0 : 0 ≤ x.num := Rat.num_nonneg.mpr hx0
  have hNcastInt : (N : ℤ) = x.num := by
    simpa [N, Int.natAbs_of_nonneg hxnum0]
  have hNcastRat : (N : ℚ) = (x.num : ℚ) := by
    exact_mod_cast hNcastInt
  have hDpos : 0 < D := by simpa [D] using Rat.den_pos x
  have hDposRat : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hDpos
  have hxform : (N : ℚ) / (D : ℚ) = x := by
    rw [hNcastRat]
    exact Rat.num_div_den x
  have hNleRat : (2 : ℚ) * (N : ℚ) ≤ (D : ℚ) := by
    rw [← hxform] at hxle
    rw [div_le_iff₀ hDposRat] at hxle
    nlinarith
  have hNle : 2 * N ≤ D := by
    exact_mod_cast hNleRat
  have hpcast : (pNat : ℤ) =
      halfGreedyResidualDisplayedNumerator n := by
    have hsubcast : ((D - 2 * N : ℕ) : ℤ) =
        (D : ℤ) - 2 * (N : ℤ) := by
      rw [Int.natCast_sub hNle]
      push_cast
      rfl
    change ((D - 2 * N : ℕ) : ℤ) =
      halfGreedyResidualDisplayedNumerator n
    rw [hsubcast]
    simp only [halfGreedyResidualDisplayedNumerator,
      halfGreedyPrefixDenominator]
    change (D : ℤ) - 2 * (N : ℤ) = (D : ℤ) - 2 * x.num
    rw [hNcastInt]
  have hqpos : 0 < q := by
    dsimp [q]
    exact pow_sub_one_pos_of_ne_zero 2 (n + 1) (by omega) (by omega)
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left q hDpos
  have hdD : d ∣ D := Nat.gcd_dvd_left D q
  have hdq : d ∣ q := Nat.gcd_dvd_right D q
  have hDfac : d * D₁ = D := by
    simpa [D₁] using Nat.mul_div_cancel' hdD
  have hqfac : d * q₁ = q := by
    simpa [q₁] using Nat.mul_div_cancel' hdq
  have hrem := greedyHalfRemainderRat_eq_displayed_divInt n
  rw [Rat.divInt_eq_div, ← hpcast] at hrem
  have hremform :
      greedyMersenneRemainderRat (1 / 2 : ℚ) n =
        (pNat : ℚ) / ((2 * D : ℕ) : ℚ) := by
    simpa [D, halfGreedyPrefixDenominator] using hrem
  have hweight :
      mersenneWeightRat (n + 1) = (1 : ℚ) / (q : ℚ) := by
    simp [q, mersenneWeightRat]
  have hqposRat : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hqpos
  have h2DposRat : (0 : ℚ) < ((2 * D : ℕ) : ℚ) := by positivity
  have htakeCrossRat :
      (((2 * D : ℕ) : ℚ)) ≤ ((pNat * q : ℕ) : ℚ) := by
    rw [hweight, hremform] at htake
    rw [div_le_div_iff₀ hqposRat h2DposRat] at htake
    simpa using htake
  have htakeCross : 2 * D ≤ pNat * q := by
    exact_mod_cast htakeCrossRat
  have htakeScaled : d * (2 * D₁) ≤ d * (pNat * q₁) := by
    calc
      d * (2 * D₁) = 2 * D := by rw [← hDfac]; ring
      _ ≤ pNat * q := htakeCross
      _ = d * (pNat * q₁) := by rw [← hqfac]; ring
  have htakeFactored : 2 * D₁ ≤ pNat * q₁ :=
    Nat.le_of_mul_le_mul_left htakeScaled hdpos
  have hNleFactored : 2 * N ≤ d * D₁ := by
    simpa only [hDfac] using hNle
  have htakeGeneric : 2 * D₁ ≤ (d * D₁ - 2 * N) * q₁ := by
    simpa only [pNat, hDfac] using htakeFactored
  have hDodd : Odd D := by
    simpa [D, x] using halfGreedyPrefixDenominator_odd n
  have h2Dcop : Nat.Coprime 2 D := Nat.coprime_two_left.mpr hDodd
  have hdodd : Odd d := Nat.coprime_two_left.mp
    (h2Dcop.coprime_dvd_right hdD)
  simpa only [e, pNat, hDfac] using
    reducedTakeStep_residual_gcd N d D₁ q₁
      hdpos hdodd hNleFactored htakeGeneric


/-- The displayed numerator of every actual half-greedy residual is nonnegative. -/
theorem halfGreedyResidualDisplayedNumerator_nonneg (n : ℕ) :
    0 ≤ halfGreedyResidualDisplayedNumerator n := by
  have hrem := greedyHalfRemainderRat_eq_displayed_divInt n
  have hrem0 := greedyMersenneRemainderRat_nonneg_of_nonneg
    (x := (1 / 2 : ℚ)) (by norm_num) n
  rw [hrem, Rat.divInt_eq_div] at hrem0
  have hden : (0 : ℚ) <
      (((2 * halfGreedyPrefixDenominator n : ℕ) : ℤ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (by norm_num)
      (Rat.den_pos (halfGreedyPrefixRat n))
  rw [div_nonneg_iff] at hrem0
  rcases hrem0 with h | h
  · exact_mod_cast h.1
  · exfalso
    exact (not_lt_of_ge h.2) hden

/-- The natural block-safe inequality at the actual displayed state is
exactly strong enough to make the next skipped state dyadically safe. -/
theorem greedyHalfRemainder_le_nextDyadic_of_BlockSafe
    (n : ℕ)
    (hsafe : BlockDyadicSafeAt
      (halfGreedyResidualDisplayedNumerator n).natAbs
      (halfGreedyPrefixDenominator n) (n + 1)) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≤ halfDyadicCap (n + 1) := by
  apply (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos n).2
  have hp0 := halfGreedyResidualDisplayedNumerator_nonneg n
  have hpcast :
      (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℤ) =
        halfGreedyResidualDisplayedNumerator n := by
    simp [Int.natAbs_of_nonneg hp0]
  unfold BlockDyadicSafeAt at hsafe
  have hsafeZ :
      (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℤ) *
          (((2 ^ (n + 1) : ℕ) : ℤ)) ≤
        2 * (halfGreedyPrefixDenominator n : ℤ) := by
    exact_mod_cast hsafe
  rw [hpcast] at hsafeZ
  unfold halfGreedyNextDyadicExcessNumerator
  unfold nextDyadicExcessIntNumerator
  rw [pow_succ] at hsafeZ
  push_cast at hsafeZ
  change ((2 : ℤ) ^ n) * halfGreedyResidualDisplayedNumerator n -
      (halfGreedyPrefixDenominator n : ℤ) ≤ 0
  ring_nf at hsafeZ ⊢
  linarith

/-- Actual-state block safety on every skipped rank composes all the way to
exact half-membership. -/
theorem half_mem_mersenneAchievementSet_of_actualBlockSafe
    (hsafe : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) n →
        BlockDyadicSafeAt
          (halfGreedyResidualDisplayedNumerator n).natAbs
          (halfGreedyPrefixDenominator n) (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_skipped_dyadicCap
  intro n hskip
  exact greedyHalfRemainder_le_nextDyadic_of_BlockSafe n
    (hsafe n hskip)

/-- The generic natural `BlockTakeAt` test is exactly the actual real greedy
decision in the current displayed half-orbit coordinates. -/
theorem greedyHalf_take_iff_BlockTakeAt (n : ℕ) :
    mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n ↔
      BlockTakeAt
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) := by
  have hp0 := halfGreedyResidualDisplayedNumerator_nonneg n
  have hpcast :
      (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℤ) =
        halfGreedyResidualDisplayedNumerator n := by
    simp [Int.natAbs_of_nonneg hp0]
  have hD : 0 < halfGreedyPrefixDenominator n :=
    Rat.den_pos (halfGreedyPrefixRat n)
  have hgeneric := mersenneWeightRat_succ_le_divInt_iff_excess
    (halfGreedyResidualDisplayedNumerator n) n
    (halfGreedyPrefixDenominator n) hD
  rw [← greedyHalfRemainderRat_eq_displayed_divInt] at hgeneric
  have hcast := rational_greedy_take_iff_real (1 / 2 : ℚ) n
  have hrealRat :
      mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) n ↔
        mersenneWeightRat (n + 1) ≤
          greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
    simpa using hcast.symm
  rw [hrealRat, hgeneric]
  unfold BlockTakeAt
  unfold nextDyadicExcessIntNumerator
  rw [pow_succ]
  have hpowpos : 0 < 2 ^ (n + 1) := by positivity
  have hsubcast :
      (((2 ^ (n + 1) - 1 : ℕ) : ℤ)) =
        (((2 ^ (n + 1) : ℕ) : ℤ)) - 1 := by
    exact_mod_cast Nat.cast_sub (by omega : 1 ≤ 2 ^ (n + 1))
  have hpowcastn : (((2 ^ n : ℕ) : ℤ)) = (2 : ℤ) ^ n := by
    norm_num
  have hpowcastsucc : (((2 ^ (n + 1) : ℕ) : ℤ)) =
      (2 : ℤ) ^ (n + 1) := by
    norm_num
  constructor
  · intro h
    have hZ :
        2 * (halfGreedyPrefixDenominator n : ℤ) ≤
          (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℤ) *
            (((2 ^ (n + 1) - 1 : ℕ) : ℤ)) := by
      rw [hpcast, hsubcast, hpowcastsucc]
      push_cast at h
      rw [pow_succ]
      ring_nf at h ⊢
      linarith
    exact_mod_cast hZ
  · intro h
    have hZ :
        2 * (halfGreedyPrefixDenominator n : ℤ) ≤
          (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℤ) *
            (((2 ^ (n + 1) - 1 : ℕ) : ℤ)) := by
      exact_mod_cast h
    rw [hpcast, hsubcast, hpowcastsucc] at hZ
    push_cast
    rw [pow_succ] at hZ
    ring_nf at hZ ⊢
    linarith

/-- An actual taken rank really produces the next displayed state by reducing
the generic raw `(H,B)` coordinates by one positive common factor. -/
theorem halfGreedy_take_raw_reduces_to_next
    (n : ℕ)
    (htake : mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    ∃ g : ℕ, 0 < g ∧
      rawTakenResidualNumerator
          (halfGreedyResidualDisplayedNumerator n).natAbs
          (halfGreedyPrefixDenominator n) (n + 1) =
        g * (halfGreedyResidualDisplayedNumerator (n + 1)).natAbs ∧
      rawTakenResidualDenominator
          (halfGreedyPrefixDenominator n) (n + 1) =
        g * halfGreedyPrefixDenominator (n + 1) := by
  let P := (halfGreedyResidualDisplayedNumerator n).natAbs
  let P' := (halfGreedyResidualDisplayedNumerator (n + 1)).natAbs
  let D := halfGreedyPrefixDenominator n
  let D' := halfGreedyPrefixDenominator (n + 1)
  let q := 2 ^ (n + 1) - 1
  let H := rawTakenResidualNumerator P D (n + 1)
  let B := rawTakenResidualDenominator D (n + 1)
  have hp0 := halfGreedyResidualDisplayedNumerator_nonneg n
  have hp0' := halfGreedyResidualDisplayedNumerator_nonneg (n + 1)
  have hPcast : (P : ℤ) = halfGreedyResidualDisplayedNumerator n := by
    simp [P, Int.natAbs_of_nonneg hp0]
  have hPcast' : (P' : ℤ) =
      halfGreedyResidualDisplayedNumerator (n + 1) := by
    simp [P', Int.natAbs_of_nonneg hp0']
  have hDpos : 0 < D := by
    simpa [D] using Rat.den_pos (halfGreedyPrefixRat n)
  have hDpos' : 0 < D' := by
    simpa [D'] using Rat.den_pos (halfGreedyPrefixRat (n + 1))
  have hqpos : 0 < q := by
    dsimp [q]
    exact pow_sub_one_pos_of_ne_zero 2 (n + 1) (by omega) (by omega)
  have hblock : BlockTakeAt P D (n + 1) := by
    simpa [P, D] using
      (greedyHalf_take_iff_BlockTakeAt n).1 htake
  have hrawle : 2 * D ≤ P * q := by
    simpa [BlockTakeAt, q] using hblock
  have hHform : H = P * q - 2 * D := by
    rfl
  have hBform : B = D * q := by
    rfl
  have hHcast : (H : ℤ) = (P : ℤ) * (q : ℤ) - 2 * (D : ℤ) := by
    rw [hHform, Int.natCast_sub hrawle]
    push_cast
    ring
  have hBcast : (B : ℤ) = (D : ℤ) * (q : ℤ) := by
    rw [hBform]
    push_cast
    rfl
  have htakeRat : mersenneWeightRat (n + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
    exact (rational_greedy_take_iff_real (1 / 2 : ℚ) n).2 (by
      simpa using htake)
  have hstepRat :
      Rat.divInt (P' : ℤ) ((2 * D' : ℕ) : ℤ) =
        Rat.divInt (P : ℤ) ((2 * D : ℕ) : ℤ) -
          1 / (q : ℚ) := by
    calc
      Rat.divInt (P' : ℤ) ((2 * D' : ℕ) : ℤ) =
          greedyMersenneRemainderRat (1 / 2 : ℚ) (n + 1) := by
        rw [greedyHalfRemainderRat_eq_displayed_divInt]
        rw [hPcast']
      _ = greedyMersenneRemainderRat (1 / 2 : ℚ) n -
          mersenneWeightRat (n + 1) := by
        rw [greedyMersenneRemainderRat_succ, if_pos htakeRat]
      _ = Rat.divInt (P : ℤ) ((2 * D : ℕ) : ℤ) -
          1 / (q : ℚ) := by
        rw [greedyHalfRemainderRat_eq_displayed_divInt]
        rw [hPcast]
        simp [D, mersenneWeightRat, q]
  have h2D : (((2 * D : ℕ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (by norm_num) hDpos).ne'
  have h2D' : (((2 * D' : ℕ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (by norm_num) hDpos').ne'
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
  rw [Rat.divInt_eq_div, Rat.divInt_eq_div] at hstepRat
  field_simp [h2D, h2D', hq] at hstepRat
  have hstepZ :
      (P' : ℤ) * (2 * (D : ℤ)) * (q : ℤ) =
        (2 * (D' : ℤ)) *
          ((P : ℤ) * (q : ℤ) - 2 * (D : ℤ)) := by
    exact_mod_cast hstepRat
  have hcrossZ :
      ((P : ℤ) * (q : ℤ) - 2 * (D : ℤ)) * (D' : ℤ) =
        (P' : ℤ) * ((D : ℤ) * (q : ℤ)) := by
    apply (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0))
    calc
      2 * (((P : ℤ) * (q : ℤ) - 2 * (D : ℤ)) * (D' : ℤ)) =
          (2 * (D' : ℤ)) *
            ((P : ℤ) * (q : ℤ) - 2 * (D : ℤ)) := by ring
      _ = (P' : ℤ) * (2 * (D : ℤ)) * (q : ℤ) := hstepZ.symm
      _ = 2 * ((P' : ℤ) * ((D : ℤ) * (q : ℤ))) := by ring
  have hcross : H * D' = P' * B := by
    have hcrossZ' : (H : ℤ) * (D' : ℤ) =
        (P' : ℤ) * (B : ℤ) := by
      rw [hHcast, hBcast]
      exact hcrossZ
    exact_mod_cast hcrossZ'
  have hcop : P'.Coprime D' := by
    simpa [P', D'] using
      halfGreedyResidualDisplayedNumerator_coprime_denominator (n + 1)
  have hBpos : 0 < B := by
    simpa [hBform] using Nat.mul_pos hDpos hqpos
  by_cases hP'z : P' = 0
  · have hD'one : D' = 1 := by
      simpa [hP'z] using hcop
    have hHz : H = 0 := by
      simpa [hP'z, hD'one] using hcross
    refine ⟨B, hBpos, ?_, ?_⟩
    · change H = B * P'
      rw [hHz, hP'z]
      simp
    · change B = B * D'
      rw [hD'one]
      simp
  · have hP'pos : 0 < P' := Nat.pos_of_ne_zero hP'z
    have hP'dvdHD : P' ∣ H * D' := by
      exact ⟨B, hcross⟩
    have hP'dvdH : P' ∣ H := (hcop.dvd_mul_right).mp hP'dvdHD
    obtain ⟨g, hHg⟩ := hP'dvdH
    have hB : B = g * D' := by
      have hscaled : P' * B = P' * (g * D') := by
        calc
          P' * B = H * D' := hcross.symm
          _ = (P' * g) * D' := by rw [hHg]
          _ = P' * (g * D') := by ring
      exact Nat.eq_of_mul_eq_mul_left hP'pos hscaled
    have hgpos : 0 < g := by
      by_contra hg
      have hg0 : g = 0 := by omega
      simp [hg0] at hB
      omega
    refine ⟨g, hgpos, ?_, ?_⟩
    · change H = g * P'
      simpa [mul_comm] using hHg
    · change B = g * D'
      exact hB

/-- A run of actual skipped decisions leaves both reduced displayed
coordinates unchanged. -/
theorem halfGreedy_coordinates_add_of_all_skips
    (b j : ℕ)
    (hskip : ∀ t : ℕ, t < j →
      ¬ mersenneWeight (b + t + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (b + t)) :
    halfGreedyResidualDisplayedNumerator (b + j) =
        halfGreedyResidualDisplayedNumerator b ∧
      halfGreedyPrefixDenominator (b + j) =
        halfGreedyPrefixDenominator b := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hprev := ih (fun t ht ↦ hskip t (by omega))
      have hskipReal := hskip j (by omega)
      have hskipRat :
          ¬ mersenneWeightRat (b + j + 1) ≤
            greedyMersenneRemainderRat (1 / 2 : ℚ) (b + j) := by
        intro htakeRat
        have htakeReal :=
          (rational_greedy_take_iff_real (1 / 2 : ℚ) (b + j)).1
            (by simpa [Nat.add_assoc] using htakeRat)
        exact hskipReal (by simpa using htakeReal)
      rw [show b + (j + 1) = (b + j) + 1 by omega]
      constructor
      · rw [halfGreedyResidualDisplayedNumerator_succ_of_skip
          (b + j) (by simpa [Nat.add_assoc] using hskipRat), hprev.1]
      · rw [halfGreedyPrefixDenominator_succ_of_skip
          (b + j) (by simpa [Nat.add_assoc] using hskipRat), hprev.2]

/-- The arithmetically meaningful remaining producer: every actual skipped
rank is bracketed by consecutive actual takes whose source-coordinate raw
margin holds. -/
structure HalfGreedySkippedActualRawMarginWitness (n : ℕ) where
  sourceRank : ℕ
  nextRank : ℕ
  hbpos : 0 < sourceRank
  hb : sourceRank < n + 1
  hc : n + 1 < nextRank
  htakeSource : mersenneWeight sourceRank ≤
    greedyMersenneRemainder (1 / 2 : ℝ) (sourceRank - 1)
  htakeNext : mersenneWeight nextRank ≤
    greedyMersenneRemainder (1 / 2 : ℝ) (nextRank - 1)
  hskipBetween : ∀ k : ℕ, sourceRank < k → k < nextRank →
    ¬ mersenneWeight k ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (k - 1)
  hmargin : nextRank = sourceRank + 1 ∨
    ((halfGreedyResidualDisplayedNumerator (sourceRank - 1)).natAbs *
          (2 ^ sourceRank - 1) -
        2 * halfGreedyPrefixDenominator (sourceRank - 1)) *
          2 ^ (nextRank - 1) ≤
      2 * (halfGreedyPrefixDenominator (sourceRank - 1) *
        (2 ^ sourceRank - 1))

/-- Exact actual-state witness needed to consume one raw taken-block margin
at a skipped rank.  The source coordinates are the state immediately before
the earlier take; the target coordinates are the live state at the skipped
rank. -/
structure HalfGreedySkippedRawBlockWitness (n : ℕ) where
  sourceRank : ℕ
  nextRank : ℕ
  factor : ℕ
  hbpos : 0 < sourceRank
  hb : sourceRank < n + 1
  hc : n + 1 < nextRank
  hg : 0 < factor
  hnum : rawTakenResidualNumerator
      (halfGreedyResidualDisplayedNumerator (sourceRank - 1)).natAbs
      (halfGreedyPrefixDenominator (sourceRank - 1)) sourceRank =
    factor * (halfGreedyResidualDisplayedNumerator n).natAbs
  hden : rawTakenResidualDenominator
      (halfGreedyPrefixDenominator (sourceRank - 1)) sourceRank =
    factor * halfGreedyPrefixDenominator n
  hfirst : IsFirstBlockTakeAfter
    (halfGreedyResidualDisplayedNumerator n).natAbs
    (halfGreedyPrefixDenominator n) sourceRank nextRank
  hmargin : nextRank = sourceRank + 1 ∨
    ((halfGreedyResidualDisplayedNumerator (sourceRank - 1)).natAbs *
          (2 ^ sourceRank - 1) -
        2 * halfGreedyPrefixDenominator (sourceRank - 1)) *
          2 ^ (nextRank - 1) ≤
      2 * (halfGreedyPrefixDenominator (sourceRank - 1) *
        (2 ^ sourceRank - 1))

/-- All state-identification and cancellation fields required by the generic
raw block theorem follow from an actual consecutive-take witness. -/
theorem halfGreedy_rawBlockWitness_of_actualRawMarginWitness
    {n : ℕ} (h : HalfGreedySkippedActualRawMarginWitness n) :
    Nonempty (HalfGreedySkippedRawBlockWitness n) := by
  have hbpos := h.hbpos
  have hb := h.hb
  have hc := h.hc
  have hcoord : ∀ m : ℕ, h.sourceRank ≤ m → m < h.nextRank →
      halfGreedyResidualDisplayedNumerator m =
          halfGreedyResidualDisplayedNumerator h.sourceRank ∧
        halfGreedyPrefixDenominator m =
          halfGreedyPrefixDenominator h.sourceRank := by
    intro m hsm hmnext
    have hrun := halfGreedy_coordinates_add_of_all_skips
      h.sourceRank (m - h.sourceRank) (fun t ht ↦ ?_)
    · simpa [Nat.add_sub_of_le hsm] using hrun
    · have hkSource : h.sourceRank < h.sourceRank + t + 1 := by omega
      have hkM : h.sourceRank + t + 1 ≤ m := by omega
      have hskip := h.hskipBetween (h.sourceRank + t + 1)
        hkSource (lt_of_le_of_lt hkM hmnext)
      simpa [show h.sourceRank + t + 1 - 1 = h.sourceRank + t by omega]
        using hskip
  have hsourceLeN : h.sourceRank ≤ n := by omega
  have hnlt : n < h.nextRank := by omega
  have hcoordN := hcoord n hsourceLeN hnlt
  have hsourceIndex : h.sourceRank - 1 + 1 = h.sourceRank := by omega
  have htakeSource' : mersenneWeight (h.sourceRank - 1 + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (h.sourceRank - 1) := by
    simpa [hsourceIndex] using h.htakeSource
  obtain ⟨g, hg, hnum0, hden0⟩ :=
    halfGreedy_take_raw_reduces_to_next
      (h.sourceRank - 1) htakeSource'
  have hnum : rawTakenResidualNumerator
      (halfGreedyResidualDisplayedNumerator (h.sourceRank - 1)).natAbs
      (halfGreedyPrefixDenominator (h.sourceRank - 1)) h.sourceRank =
        g * (halfGreedyResidualDisplayedNumerator n).natAbs := by
    rw [hcoordN.1]
    simpa [hsourceIndex] using hnum0
  have hden : rawTakenResidualDenominator
      (halfGreedyPrefixDenominator (h.sourceRank - 1)) h.sourceRank =
        g * halfGreedyPrefixDenominator n := by
    rw [hcoordN.2]
    simpa [hsourceIndex] using hden0
  have hfirst : IsFirstBlockTakeAfter
      (halfGreedyResidualDisplayedNumerator n).natAbs
      (halfGreedyPrefixDenominator n) h.sourceRank h.nextRank := by
    refine ⟨by omega, ?_, ?_⟩
    · have hnextpos : 0 < h.nextRank := by omega
      have hnextIndex : h.nextRank - 1 + 1 = h.nextRank := by omega
      have htakeNext' : mersenneWeight (h.nextRank - 1 + 1) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) (h.nextRank - 1) := by
        simpa [hnextIndex] using h.htakeNext
      have hblockNext :=
        (greedyHalf_take_iff_BlockTakeAt (h.nextRank - 1)).1
          htakeNext'
      have hcoordNext := hcoord (h.nextRank - 1) (by omega) (by omega)
      rw [hnextIndex] at hblockNext
      rw [hcoordNext.1, hcoordNext.2] at hblockNext
      rw [hcoordN.1, hcoordN.2]
      exact hblockNext
    · intro k hsk hkn hblockN
      have hkpos : 0 < k := by omega
      have hkIndex : k - 1 + 1 = k := by omega
      have hcoordK := hcoord (k - 1) (by omega) (by omega)
      have hblockK : BlockTakeAt
          (halfGreedyResidualDisplayedNumerator (k - 1)).natAbs
          (halfGreedyPrefixDenominator (k - 1)) (k - 1 + 1) := by
        rw [hkIndex]
        rw [hcoordK.1, hcoordK.2]
        rw [hcoordN.1, hcoordN.2] at hblockN
        exact hblockN
      have htakeK := (greedyHalf_take_iff_BlockTakeAt (k - 1)).2
        hblockK
      exact h.hskipBetween k hsk hkn (by simpa [hkIndex] using htakeK)
  exact ⟨{
    sourceRank := h.sourceRank
    nextRank := h.nextRank
    factor := g
    hbpos := h.hbpos
    hb := h.hb
    hc := h.hc
    hg := hg
    hnum := hnum
    hden := hden
    hfirst := hfirst
    hmargin := h.hmargin }⟩

def HalfGreedySkippedRawBlockMarginSupply : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      Nonempty (HalfGreedySkippedRawBlockWitness n)

def HalfGreedySkippedActualRawMarginSupply : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      Nonempty (HalfGreedySkippedActualRawMarginWitness n)

/-- Minimal producer form: a raw block witness is required only for a
putative skipped rank that is not already dyadically safe. -/
def HalfGreedyUnsafeSkipActualRawMarginSupply : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      ¬ BlockDyadicSafeAt
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) →
      Nonempty (HalfGreedySkippedActualRawMarginWitness n)

/-- The raw block theorem turns the actual-state witness into the precise
dyadic safety fact consumed by greedy membership. -/
theorem halfGreedy_BlockSafe_of_rawBlockWitness
    {n : ℕ} (h : HalfGreedySkippedRawBlockWitness n) :
    BlockDyadicSafeAt
      (halfGreedyResidualDisplayedNumerator n).natAbs
      (halfGreedyPrefixDenominator n) (n + 1) := by
  have hall := (takenBlock_all_next_skips_safe_iff_raw_margin
    h.hg h.hnum h.hden h.hfirst).2 h.hmargin
  exact hall (n + 1) h.hb h.hc

/-- A universal actual raw taken-block margin supply closes exact
half-membership. -/
theorem half_mem_mersenneAchievementSet_of_skippedRawBlockMarginSupply
    (hsupply : HalfGreedySkippedRawBlockMarginSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_actualBlockSafe
  intro n hskip
  rcases hsupply n hskip with ⟨h⟩
  exact halfGreedy_BlockSafe_of_rawBlockWitness h

/-- Actual consecutive takes plus the single raw gcd-free margin at every
skipped rank are sufficient for exact half-membership. -/
theorem half_mem_mersenneAchievementSet_of_skippedActualRawMarginSupply
    (hsupply : HalfGreedySkippedActualRawMarginSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_skippedRawBlockMarginSupply
  intro n hskip
  rcases hsupply n hskip with ⟨h⟩
  exact halfGreedy_rawBlockWitness_of_actualRawMarginWitness h

/-- The minimal unsafe-skip actual raw-margin producer closes exact
half-membership: a witness converts through actual state/cancellation into
the generic raw theorem and contradicts the alleged unsafe state. -/
theorem half_mem_mersenneAchievementSet_of_unsafeSkipActualRawMarginSupply
    (hsupply : HalfGreedyUnsafeSkipActualRawMarginSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_actualBlockSafe
  intro n hskip
  by_contra hunsafe
  rcases hsupply n hskip hunsafe with ⟨hactual⟩
  rcases halfGreedy_rawBlockWitness_of_actualRawMarginWitness hactual with ⟨hraw⟩
  exact hunsafe (halfGreedy_BlockSafe_of_rawBlockWitness hraw)

/-- Raw dyadic safety is exactly the unscaled predecessor-overshoot bound.
This is the condition measured by the rigorous interval receipt. -/
theorem blockDyadicSafeAt_iff_rawPredecessorOvershoot (p D k : ℕ) :
    BlockDyadicSafeAt p D k ↔
      p ≤ 2 * D - p * (2 ^ k - 1) := by
  unfold BlockDyadicSafeAt
  have hpow : 1 ≤ 2 ^ k := by
    have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
    omega
  have hsplit : p * 2 ^ k = p * (2 ^ k - 1) + p := by
    calc
      p * 2 ^ k = p * ((2 ^ k - 1) + 1) := by
        rw [Nat.sub_add_cancel hpow]
      _ = p * (2 ^ k - 1) + p := by
        simp only [Nat.mul_add, Nat.mul_one]
  rw [hsplit]
  constructor
  · intro h
    exact Nat.le_sub_of_add_le (by omega)
  · intro h
    by_cases hp : p = 0
    · simp [hp]
    have ha : p * (2 ^ k - 1) ≤ 2 * D := by
      by_contra hnot
      have hzero : 2 * D - p * (2 ^ k - 1) = 0 :=
        Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hnot)
      rw [hzero] at h
      omega
    omega

/-- A positive denominator makes the predecessor gcd at least one, so the
gcd-scaled overshoot bound implies the exact raw bound. -/
theorem rawPredecessorOvershoot_of_gcdScaled
    {p D k : ℕ} (hD : 0 < D)
    (hscaled :
      Nat.gcd D (2 ^ k - 1) * p ≤
        2 * D - p * (2 ^ k - 1)) :
    p ≤ 2 * D - p * (2 ^ k - 1) := by
  have hg : 1 ≤ Nat.gcd D (2 ^ k - 1) :=
    Nat.gcd_pos_of_pos_left (2 ^ k - 1) hD
  calc
    p = 1 * p := by simp
    _ ≤ Nat.gcd D (2 ^ k - 1) * p := Nat.mul_le_mul_right p hg
    _ ≤ 2 * D - p * (2 ^ k - 1) := hscaled

/-- The gcd-scaled producer is strictly stronger than raw dyadic safety,
even for coprime displayed coordinates. -/
theorem rawSafe_but_not_gcdScaled_fixture :
    Nat.gcd 7 15 = 1 ∧
      BlockDyadicSafeAt 7 15 2 ∧
      7 ≤ 2 * 15 - 7 * (2 ^ 2 - 1) ∧
      ¬ Nat.gcd 15 (2 ^ 2 - 1) * 7 ≤
          2 * 15 - 7 * (2 ^ 2 - 1) := by
  norm_num [BlockDyadicSafeAt]

/-- In the non-inductivity fixture, ranks `6,7,8` are skipped and rank `9`
is the first take after the rank-`5` update. -/
theorem firstTake_rank9_after_rank5_fixture :
    IsFirstBlockTakeAfter 131 16709 5 9 := by
  refine ⟨by norm_num, by norm_num [BlockTakeAt], ?_⟩
  intro k hk5 hk9
  interval_cases k <;> norm_num [BlockTakeAt]

/-- Exact one-step falsifier for generic propagation of the sharp empirical
factor `11`.  The source `(39,539)` is predecessor-safe and has overshoot
`493 ≥ 11*39`; taking rank `5` gives the reduced state `(131,16709)`, whose
first next take is rank `9`, but its predecessor overshoot is only `13`.
The target fresh quotient is already `255 ≥ 10*9`, so its size alone does
not repair the failed margin. -/
theorem factorEleven_predecessorOvershoot_not_inductive_fixture :
    BlockDyadicSafeAt 39 539 4 ∧
      11 * 39 ≤ 2 * 539 - 39 * (2 ^ 4 - 1) ∧
      BlockTakeAt 39 539 5 ∧
      rawTakenResidualNumerator 39 539 5 = 131 ∧
      rawTakenResidualDenominator 539 5 = 16709 ∧
      Nat.gcd 131 16709 = 1 ∧
      Nat.gcd 16709 (2 ^ (9 - 1) - 1) = 1 ∧
      10 * 9 ≤ (2 ^ (9 - 1) - 1) /
        Nat.gcd 16709 (2 ^ (9 - 1) - 1) ∧
      IsFirstBlockTakeAfter 131 16709 5 9 ∧
      2 * 16709 - 131 * (2 ^ (9 - 1) - 1) = 13 ∧
      ¬ BlockDyadicSafeAt 131 16709 (9 - 1) ∧
      ¬ Nat.gcd 16709 (2 ^ (9 - 1) - 1) * 131 ≤
          2 * 16709 - 131 * (2 ^ (9 - 1) - 1) := by
  refine ⟨by norm_num [BlockDyadicSafeAt], by norm_num,
    by norm_num [BlockTakeAt], by norm_num [rawTakenResidualNumerator],
    by norm_num [rawTakenResidualDenominator], by norm_num,
    by norm_num, by norm_num,
    firstTake_rank9_after_rank5_fixture, by norm_num,
    by norm_num [BlockDyadicSafeAt], by norm_num⟩

/-- The predecessor gcd divides the exact positive-side overshoot numerator;
there is no hidden floor in its primitive quotient. -/
theorem gcd_dvd_predecessorOvershoot (p D c : ℕ) :
    Nat.gcd D (2 ^ (c - 1) - 1) ∣
      2 * D - p * (2 ^ (c - 1) - 1) := by
  apply Nat.dvd_sub
  · exact dvd_mul_of_dvd_right
      (Nat.gcd_dvd_left D (2 ^ (c - 1) - 1)) 2
  · exact dvd_mul_of_dvd_right
      (Nat.gcd_dvd_right D (2 ^ (c - 1) - 1)) p

/-- A reduced rational strictly between the Mersenne reciprocal at rank
`c` and its dyadic cap has only one way for the next Mersenne gcd to fail
the strict numerator bound.  Writing
`delta = q - p(2^c - 1)`, the two adjacent gcds divide `delta` and
`|p - 2 delta|`.  The latter vanishes only when coprimality collapses the
state to the exact exceptional residual `2 / (2^(c+1) - 1)`. -/
theorem unsafeMersenneSandwich_consecutive_gcd_lt_or_exception
    {p q c : ℕ} (hcop : p.Coprime q)
    (hskip : p * (2 ^ c - 1) < q)
    (hunsafe : q < p * 2 ^ c) :
    (p = 2 ∧ q = 2 ^ (c + 1) - 1) ∨
      (Nat.gcd q (2 ^ c - 1) < p ∧
        Nat.gcd q (2 ^ (c + 1) - 1) < p) := by
  let M := 2 ^ c - 1
  let delta := q - p * M
  have hpowpos : 0 < 2 ^ c := pow_pos (by omega) c
  have hMsucc : M + 1 = 2 ^ c := by
    dsimp only [M]
    exact Nat.sub_add_cancel hpowpos
  have hskip' : p * M < q := by
    simpa only [M] using hskip
  have hbase : p * M ≤ q := hskip'.le
  have hdeltaPos : 0 < delta := by
    simpa only [delta] using Nat.sub_pos_of_lt hskip'
  have hdeltaAdd : delta + p * M = q := by
    simpa only [delta] using Nat.sub_add_cancel hbase
  have hunsafe' : q < p * M + p := by
    calc
      q < p * 2 ^ c := hunsafe
      _ = p * M + p := by rw [← hMsucc]; ring
  have hdeltaLt : delta < p := by omega
  have hfirstDvd : Nat.gcd q M ∣ delta := by
    apply Nat.dvd_sub
    · exact Nat.gcd_dvd_left q M
    · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right q M) p
  have hfirstLe : Nat.gcd q M ≤ delta :=
    Nat.le_of_dvd hdeltaPos hfirstDvd
  have hfirst : Nat.gcd q M < p := hfirstLe.trans_lt hdeltaLt

  let Q := 2 ^ (c + 1) - 1
  let g := Nat.gcd q Q
  have hQ : Q = 2 * M + 1 := by
    dsimp only [Q]
    rw [pow_succ, ← hMsucc]
    omega
  have hbalance : p * Q + 2 * delta = 2 * q + p := by
    rw [hQ]
    calc
      p * (2 * M + 1) + 2 * delta =
          2 * (delta + p * M) + p := by ring
      _ = 2 * q + p := by rw [hdeltaAdd]
  have hgq : g ∣ q := Nat.gcd_dvd_left q Q
  have hgQ : g ∣ Q := Nat.gcd_dvd_right q Q
  have hgtwoq : g ∣ 2 * q := dvd_mul_of_dvd_right hgq 2
  have hgpQ : g ∣ p * Q := dvd_mul_of_dvd_right hgQ p
  by_cases heq : 2 * delta = p
  · left
    have hpdelta : p = 2 * delta := heq.symm
    have hqeq : q = delta * Q := by
      calc
        q = delta + p * M := hdeltaAdd.symm
        _ = delta * Q := by rw [hpdelta, hQ]; ring
    have hdeltaDvdP : delta ∣ p := ⟨2, by omega⟩
    have hdeltaDvdQ : delta ∣ q := ⟨Q, hqeq⟩
    have hdeltaOne : delta = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hdeltaDvdP hdeltaDvdQ
    constructor
    · omega
    · simpa only [Q, hdeltaOne, one_mul] using hqeq
  · right
    refine ⟨hfirst, ?_⟩
    rcases lt_or_gt_of_ne heq with hbelow | habove
    · have hdvd : g ∣ p * Q - 2 * q := Nat.dvd_sub hgpQ hgtwoq
      have heqDiff : p * Q - 2 * q = p - 2 * delta := by omega
      have hpos : 0 < p * Q - 2 * q := by omega
      have hle : g ≤ p * Q - 2 * q := Nat.le_of_dvd hpos hdvd
      rw [heqDiff] at hle
      simpa only [g] using (show g < p by omega)
    · have hdvd : g ∣ 2 * q - p * Q := Nat.dvd_sub hgtwoq hgpQ
      have heqDiff : 2 * q - p * Q = 2 * delta - p := by omega
      have hpos : 0 < 2 * q - p * Q := by omega
      have hle : g ≤ 2 * q - p * Q := Nat.le_of_dvd hpos hdvd
      rw [heqDiff] at hle
      simpa only [g] using (show g < p by omega)

/-- Rational-coordinate form of
`unsafeMersenneSandwich_consecutive_gcd_lt_or_exception`.  Every reduced
rational in the open sliver between the dyadic cap `2^-c` and the
Mersenne weight at rank `c` has either the unique exceptional reduced
coordinates `(2, 2^(c+1)-1)`, or two consecutive Mersenne gcds strictly
below its numerator. -/
theorem rat_mem_mersenneDyadicSliver_consecutive_gcd_lt_or_exception
    (x : ℚ) {c : ℕ} (hc : 0 < c)
    (hdyadic : 1 / (2 : ℚ) ^ c < x)
    (hskip : x < mersenneWeightRat c) :
    (x.num.natAbs = 2 ∧ x.den = 2 ^ (c + 1) - 1) ∨
      (Nat.gcd x.den (2 ^ c - 1) < x.num.natAbs ∧
        Nat.gcd x.den (2 ^ (c + 1) - 1) < x.num.natAbs) := by
  let p := x.num.natAbs
  let q := x.den
  let M := 2 ^ c - 1
  have hxpos : 0 < x := by
    have hcapPos : (0 : ℚ) < 1 / (2 : ℚ) ^ c := by positivity
    exact hcapPos.trans hdyadic
  have hnumPos : 0 < x.num := Rat.num_pos.mpr hxpos
  have hpcastInt : (p : ℤ) = x.num := by
    simpa only [p, Int.natAbs_of_nonneg hnumPos.le]
  have hpcastRat : (p : ℚ) = (x.num : ℚ) := by
    exact_mod_cast hpcastInt
  have hqpos : 0 < q := by simpa only [q] using Rat.den_pos x
  have hqposRat : (0 : ℚ) < q := by exact_mod_cast hqpos
  have hMpos : 0 < M := by
    dsimp only [M]
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) hc.ne')
  have hMposRat : (0 : ℚ) < M := by exact_mod_cast hMpos
  have hxform : x = (p : ℚ) / (q : ℚ) := by
    rw [hpcastRat]
    simpa only [q] using (Rat.num_div_den x).symm
  have hMcast : (M : ℚ) = (2 : ℚ) ^ c - 1 := by
    simpa only [M] using natCast_pow_sub_one 2 c (by omega)
  have hskipForm : x < (1 : ℚ) / (M : ℚ) := by
    rw [hMcast]
    simpa only [mersenneWeightRat] using hskip
  have hskipCrossRat : (p : ℚ) * (M : ℚ) < q := by
    rw [hxform] at hskipForm
    have hcross :=
      (div_lt_div_iff₀ hqposRat hMposRat).mp hskipForm
    simpa only [one_mul] using hcross
  have hskipNat : p * M < q := by exact_mod_cast hskipCrossRat
  have hpowpos : 0 < 2 ^ c := pow_pos (by omega) c
  have hpowposRat : (0 : ℚ) < (2 ^ c : ℕ) := by
    exact_mod_cast hpowpos
  have hpowcast : (((2 ^ c : ℕ) : ℚ)) = (2 : ℚ) ^ c := by
    norm_cast
  have hdyadicForm :
      (1 : ℚ) / (2 ^ c : ℕ) < (p : ℚ) / (q : ℚ) := by
    rw [hpowcast, ← hxform]
    exact hdyadic
  have hunsafeCrossRat : (q : ℚ) < (p : ℚ) * (2 ^ c : ℕ) := by
    have hcross :=
      (div_lt_div_iff₀ hpowposRat hqposRat).mp hdyadicForm
    simpa only [one_mul] using hcross
  have hunsafeNat : q < p * 2 ^ c := by
    exact_mod_cast hunsafeCrossRat
  have hcop : p.Coprime q := by
    simpa only [p, q] using x.reduced
  simpa only [p, q, M] using
    unsafeMersenneSandwich_consecutive_gcd_lt_or_exception
      hcop hskipNat hunsafeNat

/-- Exact `1/21` greedy-orbit specialization.  Thus any skipped target
rank whose residual still exceeds the dyadic cap is forced into the
uniform two-gcd obstruction, except for one explicit Mersenne residual. -/
theorem greedyTwentyOne_unsafeSkip_consecutive_gcd_lt_or_exception
    (n : ℕ)
    (hdyadic :
      1 / (2 : ℚ) ^ (n + 1) <
        greedyMersenneRemainderRat (1 / 21 : ℚ) n)
    (hskip :
      greedyMersenneRemainderRat (1 / 21 : ℚ) n <
        mersenneWeightRat (n + 1)) :
    let x := greedyMersenneRemainderRat (1 / 21 : ℚ) n
    (x.num.natAbs = 2 ∧ x.den = 2 ^ (n + 2) - 1) ∨
      (Nat.gcd x.den (2 ^ (n + 1) - 1) < x.num.natAbs ∧
        Nat.gcd x.den (2 ^ (n + 2) - 1) < x.num.natAbs) := by
  dsimp only
  simpa only [Nat.add_assoc] using
    rat_mem_mersenneDyadicSliver_consecutive_gcd_lt_or_exception
      (greedyMersenneRemainderRat (1 / 21 : ℚ) n)
      (c := n + 1) (by omega) hdyadic hskip

/-- A prime power dividing a finite lcm already divides one of its nonzero
rows.  The factorization-max row is the exact form needed for an
`ExactOrderPrimePowerWitness`, including witnesses whose exponent is
larger than one. -/
theorem exists_primePow_dvd_of_primePow_dvd_finset_lcm
    (E : Finset ℕ) (hE : E.Nonempty) (h0 : 0 ∉ E)
    {q s : ℕ} (hq : Nat.Prime q)
    (hdvd : q ^ s ∣ E.lcm id) :
    ∃ d ∈ E, q ^ s ∣ d := by
  obtain ⟨d, hdE, hfactor, _⟩ :=
    exists_canonical_witness_selector_row E hE h0 q
  have hD0 : E.lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨a, haE, ha0⟩
    rw [id_eq] at ha0
    exact h0 (ha0 ▸ haE)
  have hd0 : d ≠ 0 := fun hd => h0 (hd ▸ hdE)
  have hsle : s ≤ (E.lcm id).factorization q :=
    (hq.pow_dvd_iff_le_factorization hD0).mp hdvd
  refine ⟨d, hdE, (hq.pow_dvd_iff_le_factorization hd0).mpr ?_⟩
  rwa [hfactor]

/-- The first five `1/21` greedy residuals still have reduced numerator
one.  Hence any putative exceptional numerator-two residual occurs only
after the exact-order argument has ranks `2` and `3` strictly behind it. -/
theorem greedyTwentyOneResidual_num_ne_two_of_lt_five
    (n : ℕ) (hn : n < 5) :
    (greedyMersenneRemainderRat (1 / 21 : ℚ) n).num.natAbs ≠ 2 := by
  interval_cases n <;>
    norm_num [greedyMersenneRemainderRat, mersenneWeightRat]

/-- The exceptional sliver coordinate can never occur on the `1/21`
greedy orbit.  If the residual denominator were `2^(n+2)-1`, an
exact-order prime power for exponent `n+2` would divide the lcm of
denominators coming only from ranks `2`, `3`, and the selected ranks at
most `n`.  A factorization-max row would then make `n+2` divide one of
those strictly smaller ranks, a contradiction. -/
theorem greedyTwentyOneResidual_not_mersenneException (n : ℕ) :
    let x := greedyMersenneRemainderRat (1 / 21 : ℚ) n
    ¬ (x.num.natAbs = 2 ∧ x.den = 2 ^ (n + 2) - 1) := by
  dsimp only
  rintro ⟨hnum, hden⟩
  have hn5 : 5 ≤ n := by
    by_contra hn
    exact greedyTwentyOneResidual_num_ne_two_of_lt_five n (by omega) hnum
  let P := greedyMersennePrefixRat (1 / 21 : ℚ) n
  let F := insert 2 (insert 3 P)
  let E := F.image (fun k => 2 ^ k - 1)
  let D := E.lcm id
  have hP0 : 0 ∉ P := by
    simpa only [P] using
      zero_not_mem_greedyMersennePrefixRat (1 / 21 : ℚ) n
  have hF0 : 0 ∉ F := by
    intro hzero
    rcases Finset.mem_insert.mp hzero with hzero | hzero
    · norm_num at hzero
    · rcases Finset.mem_insert.mp hzero with hzero | hzero
      · norm_num at hzero
      · exact hP0 hzero
  have hEne : E.Nonempty := by
    refine ⟨3, ?_⟩
    simp only [E, F, Finset.mem_image, Finset.mem_insert]
    exact ⟨2, Or.inl rfl, by norm_num⟩
  have hE0 : 0 ∉ E := by
    intro hzero
    obtain ⟨k, hkF, hkzero⟩ := Finset.mem_image.mp hzero
    have hk0 : k ≠ 0 := fun hk => hF0 (hk ▸ hkF)
    have hkpos : 0 < 2 ^ k - 1 :=
      pow_sub_one_pos_of_ne_zero 2 k (by omega) hk0
    omega
  have hthreeD : 3 ∣ D := by
    apply Finset.dvd_lcm
    show 3 ∈ E
    simp only [E, F, Finset.mem_image, Finset.mem_insert]
    exact ⟨2, Or.inl rfl, by norm_num⟩
  have hsevenD : 7 ∣ D := by
    apply Finset.dvd_lcm
    show 7 ∈ E
    simp only [E, F, Finset.mem_image, Finset.mem_insert]
    exact ⟨3, Or.inr (Or.inl rfl), by norm_num⟩
  have htwentyOneD : 21 ∣ D := by
    have hlcm : Nat.lcm 3 7 ∣ D := Nat.lcm_dvd hthreeD hsevenD
    norm_num at hlcm ⊢
    exact hlcm
  have hprefixTermLcmD :
      P.lcm (fun k => 2 ^ k - 1) ∣ D := by
    apply Finset.lcm_dvd
    intro k hkP
    apply Finset.dvd_lcm
    show 2 ^ k - 1 ∈ E
    exact Finset.mem_image.mpr
      ⟨k, by simp only [F, Finset.mem_insert]; exact Or.inr (Or.inr hkP), rfl⟩
  have hprefixDenD : (finiteErdosSum P 2).den ∣ D := by
    exact (den_finiteErdosSum_dvd_termDenominatorLcm P 2 hP0 (by omega)).trans
      hprefixTermLcmD
  have htargetDen : (1 / 21 : ℚ).den = 21 := by norm_num
  have hremEq :
      greedyMersenneRemainderRat (1 / 21 : ℚ) n =
        (1 / 21 : ℚ) - finiteErdosSum P 2 := by
    simpa only [P] using
      greedyMersenneRemainderRat_eq_sub_finiteErdosSum
        (1 / 21 : ℚ) n
  have hremDenD :
      (greedyMersenneRemainderRat (1 / 21 : ℚ) n).den ∣ D := by
    rw [hremEq]
    exact (Rat.sub_den_dvd_lcm
      (1 / 21 : ℚ) (finiteErdosSum P 2)).trans
        (Nat.lcm_dvd (by simpa only [htargetDen] using htwentyOneD) hprefixDenD)
  let m := n + 2
  obtain ⟨q, s, hwit⟩ :=
    exists_exactOrderPrimePowerWitness (b := 2) (n := m)
      (by omega) (by omega)
  have hqm : q ^ s ∣ 2 ^ m - 1 := (hwit.2.2 m).2 dvd_rfl
  have hqrem :
      q ^ s ∣ (greedyMersenneRemainderRat (1 / 21 : ℚ) n).den := by
    rw [hden]
    simpa only [m] using hqm
  have hqD : q ^ s ∣ D := hqrem.trans hremDenD
  obtain ⟨d, hdE, hqd⟩ :=
    exists_primePow_dvd_of_primePow_dvd_finset_lcm
      E hEne hE0 hwit.1 hqD
  obtain ⟨k, hkF, rfl⟩ := Finset.mem_image.mp hdE
  have hmk : m ∣ k := (hwit.2.2 k).1 hqd
  rcases Finset.mem_insert.mp hkF with rfl | hkF
  · have := Nat.le_of_dvd (by omega : 0 < 2) hmk
    omega
  · rcases Finset.mem_insert.mp hkF with rfl | hkP
    · have := Nat.le_of_dvd (by omega : 0 < 3) hmk
      omega
    · unfold P at hkP
      obtain ⟨j, hj, hkj⟩ := Finset.mem_image.mp hkP
      have hjlt : j < n := by
        exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hkpos : 0 < j + 1 := by omega
      have hle := Nat.le_of_dvd hkpos (by simpa only [hkj] using hmk)
      omega

/-- The `1/21` target orbit therefore has no exceptional branch: every
dyadically unsafe skipped rank forces both adjacent Mersenne gcds below
the current reduced numerator. -/
theorem greedyTwentyOne_unsafeSkip_consecutive_gcd_lt
    (n : ℕ)
    (hdyadic :
      1 / (2 : ℚ) ^ (n + 1) <
        greedyMersenneRemainderRat (1 / 21 : ℚ) n)
    (hskip :
      greedyMersenneRemainderRat (1 / 21 : ℚ) n <
        mersenneWeightRat (n + 1)) :
    let x := greedyMersenneRemainderRat (1 / 21 : ℚ) n
    Nat.gcd x.den (2 ^ (n + 1) - 1) < x.num.natAbs ∧
      Nat.gcd x.den (2 ^ (n + 2) - 1) < x.num.natAbs := by
  dsimp only
  rcases greedyTwentyOne_unsafeSkip_consecutive_gcd_lt_or_exception
      n hdyadic hskip with hexception | hgcd
  · exact absurd hexception (greedyTwentyOneResidual_not_mersenneException n)
  · exact hgcd

/-- The dyadic lower edge of a positive rational interval is exactly the
cross-multiplied upper bound on its reduced denominator. -/
theorem rat_den_lt_num_natAbs_mul_twoPow_of_inv_twoPow_lt
    (x : ℚ) {c : ℕ}
    (hdyadic : 1 / (2 : ℚ) ^ c < x) :
    x.den < x.num.natAbs * 2 ^ c := by
  let p := x.num.natAbs
  let q := x.den
  have hxpos : 0 < x := by
    have hcapPos : (0 : ℚ) < 1 / (2 : ℚ) ^ c := by positivity
    exact hcapPos.trans hdyadic
  have hnumPos : 0 < x.num := Rat.num_pos.mpr hxpos
  have hpcastInt : (p : ℤ) = x.num := by
    simpa only [p, Int.natAbs_of_nonneg hnumPos.le]
  have hpcastRat : (p : ℚ) = (x.num : ℚ) := by
    exact_mod_cast hpcastInt
  have hqpos : 0 < q := by simpa only [q] using Rat.den_pos x
  have hqposRat : (0 : ℚ) < q := by exact_mod_cast hqpos
  have hpowpos : 0 < 2 ^ c := pow_pos (by omega) c
  have hpowposRat : (0 : ℚ) < (2 ^ c : ℕ) := by
    exact_mod_cast hpowpos
  have hxform : x = (p : ℚ) / (q : ℚ) := by
    rw [hpcastRat]
    simpa only [q] using (Rat.num_div_den x).symm
  have hpowcast : (((2 ^ c : ℕ) : ℚ)) = (2 : ℚ) ^ c := by
    norm_cast
  have hdyadicForm :
      (1 : ℚ) / (2 ^ c : ℕ) < (p : ℚ) / (q : ℚ) := by
    rw [hpowcast, ← hxform]
    exact hdyadic
  have hcross : (q : ℚ) < (p : ℚ) * (2 ^ c : ℕ) := by
    have :=
      (div_lt_div_iff₀ hpowposRat hqposRat).mp hdyadicForm
    simpa only [one_mul] using this
  exact_mod_cast hcross

/-- After an unsafe skip, cancel from the next raw take the gcd already
visible in the old denominator and the next Mersenne denominator.  The
remaining primitive numerator is larger than the skipped Mersenne
denominator.  Any further reduction must therefore come from a second
gcd entirely inside that first cancellation factor. -/
theorem unsafeMersenneSandwich_nextPrimitiveNumerator_gt
    {p q c : ℕ} (hc : 0 < c)
    (hunsafe : q < p * 2 ^ c)
    (hglt : Nat.gcd q (2 ^ (c + 1) - 1) < p) :
    2 ^ c - 1 <
      (p * (2 ^ (c + 1) - 1) - q) /
        Nat.gcd q (2 ^ (c + 1) - 1) := by
  let T := 2 ^ c
  let M := T - 1
  let Q := 2 ^ (c + 1) - 1
  let g := Nat.gcd q Q
  let H := p * Q - q
  have hTpos : 0 < T := by
    simpa only [T] using pow_pos (by omega : 0 < 2) c
  have hMpos : 0 < M := by
    dsimp only [M, T]
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) hc.ne')
  have hQdecomp : Q = T + M := by
    dsimp only [Q, T, M]
    rw [pow_succ]
    omega
  have hp : 0 < p := by
    simpa only [g] using (lt_of_le_of_lt (Nat.zero_le g) hglt)
  have hTltQ : T < Q := by omega
  have hqRaw : q ≤ p * Q := by
    have hpTQ : p * T < p * Q :=
      Nat.mul_lt_mul_of_pos_left hTltQ hp
    exact (hunsafe.trans hpTQ).le
  have hHadd : H + q = p * Q := by
    simpa only [H] using Nat.sub_add_cancel hqRaw
  have hpQdecomp : p * Q = p * T + p * M := by
    rw [hQdecomp]
    ring
  have hunsafeT : q < p * T := by
    simpa only [T] using hunsafe
  have hrawGt : p * M < H := by omega
  have hgDvd : g ∣ H := by
    dsimp only [g, H]
    apply Nat.dvd_sub
    · exact dvd_mul_of_dvd_right
        (Nat.gcd_dvd_right q Q) p
    · exact Nat.gcd_dvd_left q Q
  have hfactor : g * (H / g) = H := Nat.mul_div_cancel' hgDvd
  by_contra hnot
  have hquotLe : H / g ≤ M := Nat.le_of_not_gt hnot
  have hmulLe : g * (H / g) ≤ g * M :=
    Nat.mul_le_mul_left g hquotLe
  rw [hfactor] at hmulLe
  have hgMlt : g * M < p * M :=
    Nat.mul_lt_mul_of_pos_right (by simpa only [g] using hglt) hMpos
  exact (not_lt_of_ge hmulLe) (hgMlt.trans hrawGt)

/-- Actual-orbit form of the forced numerator jump.  At every unsafe
skipped rank of the `1/21` greedy orbit, the next Mersenne take has
first-stage primitive numerator strictly above the skipped denominator. -/
theorem greedyTwentyOne_unsafeSkip_nextPrimitiveNumerator_gt
    (n : ℕ)
    (hdyadic :
      1 / (2 : ℚ) ^ (n + 1) <
        greedyMersenneRemainderRat (1 / 21 : ℚ) n)
    (hskip :
      greedyMersenneRemainderRat (1 / 21 : ℚ) n <
        mersenneWeightRat (n + 1)) :
    let x := greedyMersenneRemainderRat (1 / 21 : ℚ) n
    2 ^ (n + 1) - 1 <
      (x.num.natAbs * (2 ^ (n + 2) - 1) - x.den) /
        Nat.gcd x.den (2 ^ (n + 2) - 1) := by
  dsimp only
  let x := greedyMersenneRemainderRat (1 / 21 : ℚ) n
  have hunsafe :
      x.den < x.num.natAbs * 2 ^ (n + 1) := by
    exact rat_den_lt_num_natAbs_mul_twoPow_of_inv_twoPow_lt x hdyadic
  have hglt :
      Nat.gcd x.den (2 ^ (n + 2) - 1) < x.num.natAbs := by
    have hg :=
      greedyTwentyOne_unsafeSkip_consecutive_gcd_lt n hdyadic hskip
    simpa only [x] using hg.2
  simpa only [x, Nat.add_assoc] using
    unsafeMersenneSandwich_nextPrimitiveNumerator_gt
      (c := n + 1) (by omega) hunsafe hglt

/-- Exact two-stage normalization of a positive rational residual after
subtracting one reciprocal.  The first cancellation is
`d = gcd(x.den,Q)`; after dividing it out, coprimality shows that every
remaining cancellation is concentrated in the single factor
`e = gcd(p*(Q/d)-q/d,d)`. -/
theorem rat_sub_inv_nat_twoStage_normalForm
    (x : ℚ) {Q : ℕ} (hQ : 0 < Q)
    (htake : (1 : ℚ) / Q < x) :
    let p := x.num.natAbs
    let q := x.den
    let d := Nat.gcd q Q
    let q₁ := q / d
    let Q₁ := Q / d
    let A := p * Q₁ - q₁
    let e := Nat.gcd A d
    (x - (1 : ℚ) / Q).num.natAbs = A / e ∧
      (x - (1 : ℚ) / Q).den = (d / e) * q₁ * Q₁ := by
  dsimp only
  let p := x.num.natAbs
  let q := x.den
  let d := Nat.gcd q Q
  let q₁ := q / d
  let Q₁ := Q / d
  let A := p * Q₁ - q₁
  let e := Nat.gcd A d
  let B := (d / e) * q₁ * Q₁
  have hxpos : 0 < x := by
    exact (by positivity : (0 : ℚ) < (1 : ℚ) / Q).trans htake
  have hnumPos : 0 < x.num := Rat.num_pos.mpr hxpos
  have hpcastInt : (p : ℤ) = x.num := by
    simpa only [p, Int.natAbs_of_nonneg hnumPos.le]
  have hpcastRat : (p : ℚ) = (x.num : ℚ) := by
    exact_mod_cast hpcastInt
  have hqpos : 0 < q := by simpa only [q] using Rat.den_pos x
  have hqposRat : (0 : ℚ) < q := by exact_mod_cast hqpos
  have hQposRat : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hxform : x = (p : ℚ) / (q : ℚ) := by
    rw [hpcastRat]
    simpa only [q] using (Rat.num_div_den x).symm
  have hcrossRat : (q : ℚ) < (p : ℚ) * Q := by
    rw [hxform] at htake
    have hcross := (div_lt_div_iff₀ hQposRat hqposRat).mp htake
    simpa only [one_mul] using hcross
  have hcross : q < p * Q := by exact_mod_cast hcrossRat
  have hdpos : 0 < d := by
    simpa only [d] using Nat.gcd_pos_of_pos_left Q hqpos
  have hdq : d ∣ q := Nat.gcd_dvd_left q Q
  have hdQ : d ∣ Q := Nat.gcd_dvd_right q Q
  have hqfac : d * q₁ = q := by
    simpa only [q₁] using Nat.mul_div_cancel' hdq
  have hQfac : d * Q₁ = Q := by
    simpa only [Q₁] using Nat.mul_div_cancel' hdQ
  have hq₁pos : 0 < q₁ :=
    Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos
  have hQ₁pos : 0 < Q₁ :=
    Nat.div_pos (Nat.le_of_dvd hQ hdQ) hdpos
  have hcrossScaled : d * q₁ < d * (p * Q₁) := by
    calc
      d * q₁ = q := hqfac
      _ < p * Q := hcross
      _ = d * (p * Q₁) := by rw [← hQfac]; ring
  have hcross₁ : q₁ < p * Q₁ :=
    (Nat.mul_lt_mul_left hdpos).mp hcrossScaled
  have hApos : 0 < A := by
    simpa only [A] using Nat.sub_pos_of_lt hcross₁
  have hpq : p.Coprime (d * q₁) := by
    rw [hqfac]
    simpa only [p, q] using x.reduced
  have hpq₁ : p.Coprime q₁ :=
    hpq.coprime_dvd_right (dvd_mul_left q₁ d)
  have hq₁Q₁ : q₁.Coprime Q₁ := by
    simpa only [q₁, Q₁, d] using
      Nat.coprime_div_gcd_div_gcd hdpos
  have hpQ₁_q₁ : (p * Q₁).Coprime q₁ :=
    hpq₁.mul_left hq₁Q₁.symm
  have hAq₁ : A.Coprime q₁ := by
    simpa only [A] using
      (Nat.coprime_sub_self_left hcross₁.le).mpr hpQ₁_q₁
  have hA_pQ₁ : A.Coprime (p * Q₁) := by
    simpa only [A] using
      (Nat.coprime_self_sub_left hcross₁.le).mpr hpQ₁_q₁.symm
  have hAQ₁ : A.Coprime Q₁ :=
    hA_pQ₁.coprime_dvd_right (dvd_mul_left Q₁ p)
  have hepos : 0 < e := by
    exact Nat.gcd_pos_of_pos_right A hdpos
  have heA : e ∣ A := Nat.gcd_dvd_left A d
  have hed : e ∣ d := Nat.gcd_dvd_right A d
  have hdredpos : 0 < d / e :=
    Nat.div_pos (Nat.le_of_dvd hdpos hed) hepos
  have hAredTail : (A / e).Coprime (q₁ * Q₁) :=
    (hAq₁.mul_right hAQ₁).coprime_dvd_left
      (Nat.div_dvd_of_dvd heA)
  have hAredDred : (A / e).Coprime (d / e) :=
    Nat.coprime_div_gcd_div_gcd hepos
  have hcopB : (A / e).Coprime B := by
    simpa only [B, Nat.mul_assoc] using
      hAredDred.mul_right hAredTail
  have hBpos : 0 < B := by
    exact Nat.mul_pos (Nat.mul_pos hdredpos hq₁pos) hQ₁pos
  have hrawDen : ((d * q₁ * Q₁ : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos hdpos hq₁pos) hQ₁pos).ne'
  have hredDen : (B : ℚ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hraw :
      x - (1 : ℚ) / Q = (A : ℚ) / (d * q₁ * Q₁ : ℕ) := by
    rw [hxform, ← hqfac, ← hQfac]
    have hdq₁ : (((d * q₁ : ℕ) : ℚ)) ≠ 0 := by positivity
    have hdQ₁ : (((d * Q₁ : ℕ) : ℚ)) ≠ 0 := by positivity
    have hAcast : (A : ℚ) = (p : ℚ) * Q₁ - q₁ := by
      change (((p * Q₁ - q₁ : ℕ) : ℚ)) =
        (p : ℚ) * Q₁ - q₁
      rw [Nat.cast_sub hcross₁.le]
      push_cast
      rfl
    rw [hAcast]
    field_simp [hdq₁, hdQ₁, hrawDen]
    push_cast
    ring
  have hcrossReduced :
      A * B = (A / e) * (d * q₁ * Q₁) := by
    have hAe : e * (A / e) = A := Nat.mul_div_cancel' heA
    have hde : e * (d / e) = d := Nat.mul_div_cancel' hed
    calc
      A * B = (e * (A / e)) * ((d / e) * q₁ * Q₁) := by rw [hAe]
      _ = (A / e) * ((e * (d / e)) * q₁ * Q₁) := by ring
      _ = (A / e) * (d * q₁ * Q₁) := by rw [hde]
  have hred :
      (A : ℚ) / (d * q₁ * Q₁ : ℕ) =
        ((A / e : ℕ) : ℚ) / (B : ℚ) := by
    rw [div_eq_div_iff hrawDen hredDen]
    exact_mod_cast hcrossReduced
  have hnormal :
      x - (1 : ℚ) / Q =
        ((A / e : ℕ) : ℚ) / (B : ℚ) := hraw.trans hred
  have hnum :
      (x - (1 : ℚ) / Q).num = (A / e : ℕ) := by
    rw [hnormal]
    have hcopInt :
        Nat.Coprime (((A / e : ℕ) : ℤ).natAbs) ((B : ℤ).natAbs) := by
      simpa using hcopB
    simpa using Rat.num_div_eq_of_coprime
      (a := ((A / e : ℕ) : ℤ)) (b := (B : ℤ))
      (by exact_mod_cast hBpos) hcopInt
  have hden :
      (x - (1 : ℚ) / Q).den = B := by
    rw [hnormal]
    exact den_natCast_div_natCast_of_coprime
      (A / e) B hBpos.ne' hcopB
  refine ⟨?_, ?_⟩
  · change (x - (1 : ℚ) / Q).num.natAbs = A / e
    simpa using congrArg Int.natAbs hnum
  · simpa only [B] using hden

/-- The next Mersenne weight lies strictly below the current dyadic cap. -/
theorem mersenneWeightRat_succ_lt_inv_twoPow
    (c : ℕ) (hc : 0 < c) :
    mersenneWeightRat (c + 1) < 1 / (2 : ℚ) ^ c := by
  have hpowPos : (0 : ℚ) < (2 : ℚ) ^ c := by positivity
  have hpowOne : (1 : ℚ) < (2 : ℚ) ^ c :=
    one_lt_pow₀ (by norm_num) hc.ne'
  have hden :
      (2 : ℚ) ^ c < (2 : ℚ) ^ (c + 1) - 1 := by
    rw [pow_succ]
    nlinarith
  unfold mersenneWeightRat
  exact one_div_lt_one_div_of_lt hpowPos hden

/-- Full actual-orbit normalization after an unsafe `1/21` skip.  The
skipped rank leaves the residual unchanged; the dyadic lower edge forces
the next rank to be taken; and the resulting reduced numerator is the
first-stage primitive numerator divided by exactly one residual
cancellation `e`.  Moreover `e` times that actual numerator is larger than
the skipped Mersenne denominator. -/
theorem greedyTwentyOne_unsafeSkip_nextResidual_twoStage
    (n : ℕ)
    (hdyadic :
      1 / (2 : ℚ) ^ (n + 1) <
        greedyMersenneRemainderRat (1 / 21 : ℚ) n)
    (hskip :
      greedyMersenneRemainderRat (1 / 21 : ℚ) n <
        mersenneWeightRat (n + 1)) :
    let x := greedyMersenneRemainderRat (1 / 21 : ℚ) n
    let Q := 2 ^ (n + 2) - 1
    let d := Nat.gcd x.den Q
    let q₁ := x.den / d
    let Q₁ := Q / d
    let A := x.num.natAbs * Q₁ - q₁
    let e := Nat.gcd A d
    let y := greedyMersenneRemainderRat (1 / 21 : ℚ) (n + 2)
    y.num.natAbs = A / e ∧
      y.den = (d / e) * q₁ * Q₁ ∧
        2 ^ (n + 1) - 1 < e * y.num.natAbs := by
  dsimp only
  let x := greedyMersenneRemainderRat (1 / 21 : ℚ) n
  let Q := 2 ^ (n + 2) - 1
  let d := Nat.gcd x.den Q
  let q₁ := x.den / d
  let Q₁ := Q / d
  let A := x.num.natAbs * Q₁ - q₁
  let e := Nat.gcd A d
  let y := greedyMersenneRemainderRat (1 / 21 : ℚ) (n + 2)
  have hskipNot : ¬ mersenneWeightRat (n + 1) ≤ x :=
    not_le.mpr hskip
  have hremSkip :
      greedyMersenneRemainderRat (1 / 21 : ℚ) (n + 1) = x := by
    rw [greedyMersenneRemainderRat_succ]
    simp only [if_neg hskipNot, x]
  have hweightNext :
      mersenneWeightRat (n + 2) < x := by
    exact (mersenneWeightRat_succ_lt_inv_twoPow
      (n + 1) (by omega)).trans hdyadic
  have htakeNext : mersenneWeightRat (n + 2) ≤ x :=
    hweightNext.le
  have hweightQ :
      mersenneWeightRat (n + 2) = (1 : ℚ) / Q := by
    simp [Q, mersenneWeightRat, natCast_pow_sub_one]
  have hremTake : y = x - (1 : ℚ) / Q := by
    dsimp only [y]
    rw [show n + 2 = (n + 1) + 1 by omega,
      greedyMersenneRemainderRat_succ, hremSkip,
      if_pos htakeNext, hweightQ]
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact pow_sub_one_pos_of_ne_zero 2 (n + 2) (by omega) (by omega)
  have hnormal0 :=
    rat_sub_inv_nat_twoStage_normalForm x hQpos
      (by simpa only [hweightQ] using hweightNext)
  have hnormal :
      y.num.natAbs = A / e ∧
        y.den = (d / e) * q₁ * Q₁ := by
    rw [hremTake]
    simpa only [d, q₁, Q₁, A, e] using hnormal0
  have hfirst :
      2 ^ (n + 1) - 1 <
        (x.num.natAbs * Q - x.den) / d := by
    simpa only [x, Q, d] using
      greedyTwentyOne_unsafeSkip_nextPrimitiveNumerator_gt
        n hdyadic hskip
  have hdpos : 0 < d := by
    have hxden : 0 < x.den := Rat.den_pos x
    simpa only [d] using Nat.gcd_pos_of_pos_left Q hxden
  have hdq : d ∣ x.den := by
    exact Nat.gcd_dvd_left x.den Q
  have hdQ : d ∣ Q := by
    exact Nat.gcd_dvd_right x.den Q
  have hqfac : d * q₁ = x.den := by
    simpa only [q₁] using Nat.mul_div_cancel' hdq
  have hQfac : d * Q₁ = Q := by
    simpa only [Q₁] using Nat.mul_div_cancel' hdQ
  have hcross :
      x.den < x.num.natAbs * Q := by
    have hpowCross :=
      rat_den_lt_num_natAbs_mul_twoPow_of_inv_twoPow_lt x hdyadic
    have hpowQ : 2 ^ (n + 1) < Q := by
      have hpow : 1 < 2 ^ (n + 1) :=
        one_lt_pow₀ (by omega) (by omega)
      have hpowSucc :
          2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        ring
      dsimp only [Q]
      rw [hpowSucc]
      omega
    have hnumPos : 0 < x.num.natAbs := by
      have hxpos : 0 < x := (by positivity : (0 : ℚ) <
        1 / (2 : ℚ) ^ (n + 1)).trans hdyadic
      exact Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hxpos.ne')
    exact hpowCross.trans
      (Nat.mul_lt_mul_of_pos_left hpowQ hnumPos)
  have hrawFactor :
      x.num.natAbs * Q - x.den = d * A := by
    calc
      x.num.natAbs * Q - x.den =
          d * (x.num.natAbs * Q₁) - d * q₁ := by
            rw [← hQfac, ← hqfac]
            congr 1
            ring
      _ = d * (x.num.natAbs * Q₁ - q₁) := by
            exact (Nat.mul_sub_left_distrib d
              (x.num.natAbs * Q₁) q₁).symm
      _ = d * A := by rfl
  have hquotient :
      (x.num.natAbs * Q - x.den) / d = A := by
    rw [hrawFactor]
    simpa only [mul_comm] using Nat.mul_div_left A hdpos
  have hAgt : 2 ^ (n + 1) - 1 < A := by
    rwa [hquotient] at hfirst
  have heA : e ∣ A := Nat.gcd_dvd_left A d
  have hfactor : e * (A / e) = A := Nat.mul_div_cancel' heA
  refine ⟨hnormal.1, hnormal.2, ?_⟩
  rw [hnormal.1, hfactor]
  exact hAgt

/-- The residual cancellation can be removed from the statement entirely.
Since `e` divides the old/next denominator gcd and that gcd is strictly
below the current numerator, every unsafe skip forces an exponential
multiplicative jump across the forced next take. -/
theorem greedyTwentyOne_unsafeSkip_numeratorProduct_gt
    (n : ℕ)
    (hdyadic :
      1 / (2 : ℚ) ^ (n + 1) <
        greedyMersenneRemainderRat (1 / 21 : ℚ) n)
    (hskip :
      greedyMersenneRemainderRat (1 / 21 : ℚ) n <
        mersenneWeightRat (n + 1)) :
    2 ^ (n + 1) - 1 <
      (greedyMersenneRemainderRat (1 / 21 : ℚ) n).num.natAbs *
        (greedyMersenneRemainderRat
          (1 / 21 : ℚ) (n + 2)).num.natAbs := by
  let x := greedyMersenneRemainderRat (1 / 21 : ℚ) n
  let Q := 2 ^ (n + 2) - 1
  let d := Nat.gcd x.den Q
  let q₁ := x.den / d
  let Q₁ := Q / d
  let A := x.num.natAbs * Q₁ - q₁
  let e := Nat.gcd A d
  let y := greedyMersenneRemainderRat (1 / 21 : ℚ) (n + 2)
  have htwo :=
    greedyTwentyOne_unsafeSkip_nextResidual_twoStage n hdyadic hskip
  have hprod : 2 ^ (n + 1) - 1 < e * y.num.natAbs := by
    simpa only [x, Q, d, q₁, Q₁, A, e, y] using htwo.2.2
  have hdpos : 0 < d := by
    have hxden : 0 < x.den := Rat.den_pos x
    have hQpos : 0 < Q := by
      dsimp only [Q]
      exact pow_sub_one_pos_of_ne_zero 2 (n + 2) (by omega) (by omega)
    simpa only [d] using Nat.gcd_pos_of_pos_left Q hxden
  have hed : e ∣ d := Nat.gcd_dvd_right A d
  have heLeD : e ≤ d := Nat.le_of_dvd hdpos hed
  have hdLtP : d < x.num.natAbs := by
    have hg :=
      greedyTwentyOne_unsafeSkip_consecutive_gcd_lt n hdyadic hskip
    simpa only [x, Q, d] using hg.2
  have heLeP : e ≤ x.num.natAbs := heLeD.trans hdLtP.le
  have hmul :
      e * y.num.natAbs ≤ x.num.natAbs * y.num.natAbs :=
    Nat.mul_le_mul_right y.num.natAbs heLeP
  simpa only [x, y] using hprod.trans_le hmul

/-- An unsafe Mersenne sandwich forces both adjacent Mersenne gcds to be
strictly smaller than the displayed numerator.  For the lower gcd this is
the positive overshoot `delta = 2D - p(2^c - 1)`.  For the next gcd, the
same divisor divides `|2 delta - p|`; oddness of `p` makes this difference
nonzero, while `0 < delta < p` keeps it strictly below `p`. -/
theorem unsafeSandwich_consecutive_gcd_lt
    {p D c : ℕ} (hD : 0 < D) (hc : 0 < c) (hpodd : Odd p)
    (hskip : p * (2 ^ c - 1) < 2 * D)
    (hunsafe : 2 * D < p * 2 ^ c) :
    Nat.gcd D (2 ^ c - 1) < p ∧
      Nat.gcd D (2 ^ (c + 1) - 1) < p := by
  let q := 2 ^ c - 1
  let delta := 2 * D - p * q
  have hpowpos : 0 < 2 ^ c := pow_pos (by omega) c
  have hqsucc : q + 1 = 2 ^ c := by
    dsimp only [q]
    exact Nat.sub_add_cancel hpowpos
  have hskip' : p * q < 2 * D := by
    simpa only [q] using hskip
  have hbase : p * q ≤ 2 * D := hskip'.le
  have hdeltaPos : 0 < delta := by
    simpa only [delta] using Nat.sub_pos_of_lt hskip'
  have hdeltaAdd : delta + p * q = 2 * D := by
    simpa only [delta] using Nat.sub_add_cancel hbase
  have hunsafe' : 2 * D < p * q + p := by
    calc
      2 * D < p * 2 ^ c := hunsafe
      _ = p * q + p := by rw [← hqsucc]; ring
  have hdeltaLt : delta < p := by omega
  have hindex : c + 1 - 1 = c := by omega
  have hfirstDvd : Nat.gcd D q ∣ delta := by
    simpa only [hindex, q, delta] using
      gcd_dvd_predecessorOvershoot p D (c + 1)
  have hfirstLe : Nat.gcd D q ≤ delta :=
    Nat.le_of_dvd hdeltaPos hfirstDvd
  have hfirst : Nat.gcd D q < p := hfirstLe.trans_lt hdeltaLt

  let Q := 2 ^ (c + 1) - 1
  let g := Nat.gcd D Q
  have hQ : Q = 2 * q + 1 := by
    dsimp only [Q]
    rw [pow_succ, ← hqsucc]
    omega
  have hbalance : p * Q + 2 * delta = 4 * D + p := by
    rw [hQ]
    calc
      p * (2 * q + 1) + 2 * delta =
          2 * (delta + p * q) + p := by ring
      _ = 2 * (2 * D) + p := by rw [hdeltaAdd]
      _ = 4 * D + p := by ring
  have hgD : g ∣ D := by
    exact Nat.gcd_dvd_left D Q
  have hgQ : g ∣ Q := by
    exact Nat.gcd_dvd_right D Q
  have hgFourD : g ∣ 4 * D := dvd_mul_of_dvd_right hgD 4
  have hgpQ : g ∣ p * Q := dvd_mul_of_dvd_right hgQ p
  have htwodeltaNe : 2 * delta ≠ p := by
    intro heq
    apply (Nat.not_even_iff_odd.mpr hpodd)
    rw [← heq]
    exact ⟨delta, by ring⟩
  have hsecond : g < p := by
    rcases lt_or_gt_of_ne htwodeltaNe with hbelow | habove
    · have hdvd : g ∣ p * Q - 4 * D := Nat.dvd_sub hgpQ hgFourD
      have heq : p * Q - 4 * D = p - 2 * delta := by omega
      have hpos : 0 < p * Q - 4 * D := by omega
      have hle : g ≤ p * Q - 4 * D := Nat.le_of_dvd hpos hdvd
      rw [heq] at hle
      omega
    · have hdvd : g ∣ 4 * D - p * Q := Nat.dvd_sub hgFourD hgpQ
      have heq : 4 * D - p * Q = 2 * delta - p := by omega
      have hpos : 0 < 4 * D - p * Q := by omega
      have hle : g ≤ 4 * D - p * Q := Nat.le_of_dvd hpos hdvd
      rw [heq] at hle
      omega
  simpa only [q, Q, g] using And.intro hfirst hsecond

/-- Actual half-greedy specialization: every putative dyadically unsafe
skipped rank makes the two consecutive Mersenne gcds smaller than the
current displayed residual numerator. -/
theorem greedyHalf_unsafeSkip_consecutive_gcd_lt
    (n : ℕ)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n)
    (hunsafe : ¬ BlockDyadicSafeAt
      (halfGreedyResidualDisplayedNumerator n).natAbs
      (halfGreedyPrefixDenominator n) (n + 1)) :
    Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1) <
        (halfGreedyResidualDisplayedNumerator n).natAbs ∧
      Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 2) - 1) <
        (halfGreedyResidualDisplayedNumerator n).natAbs := by
  let p := (halfGreedyResidualDisplayedNumerator n).natAbs
  let D := halfGreedyPrefixDenominator n
  have hD : 0 < D := by
    simpa only [D] using Rat.den_pos (halfGreedyPrefixRat n)
  have hpodd : Odd p := by
    simpa only [p] using
      (halfGreedyResidualDisplayedNumerator_odd n).natAbs
  have hskipBlock : ¬ BlockTakeAt p D (n + 1) := by
    intro htake
    apply hskip
    apply (greedyHalf_take_iff_BlockTakeAt n).2
    simpa only [p, D] using htake
  have hskipNat : p * (2 ^ (n + 1) - 1) < 2 * D := by
    simpa only [BlockTakeAt, not_le] using hskipBlock
  have hunsafeBlock : ¬ BlockDyadicSafeAt p D (n + 1) := by
    simpa only [p, D] using hunsafe
  have hunsafeNat : 2 * D < p * 2 ^ (n + 1) := by
    simpa only [BlockDyadicSafeAt, not_le] using hunsafeBlock
  have hresult := unsafeSandwich_consecutive_gcd_lt
    (p := p) (D := D) (c := n + 1) hD (by omega) hpodd
      hskipNat hunsafeNat
  simpa only [p, D, show (n + 1) + 1 = n + 2 by omega] using hresult

/-- The gcd-scaled overshoot inequality is exactly the lower bound on the
primitive quotient used by the executable actual-orbit replay. -/
theorem gcdScaled_predecessorOvershoot_iff_primitiveQuotient
    {p D c : ℕ} (hD : 0 < D) :
    Nat.gcd D (2 ^ (c - 1) - 1) * p ≤
        2 * D - p * (2 ^ (c - 1) - 1) ↔
      p ≤ (2 * D - p * (2 ^ (c - 1) - 1)) /
        Nat.gcd D (2 ^ (c - 1) - 1) := by
  have hgpos : 0 < Nat.gcd D (2 ^ (c - 1) - 1) :=
    Nat.gcd_pos_of_pos_left _ hD
  rw [Nat.le_div_iff_mul_le hgpos]
  simp only [Nat.mul_comm]

/-- A gcd-scaled primitive overshoot at the predecessor Mersenne threshold
forces the missing dyadic margin. -/
theorem blockDyadicSafeAt_of_gcdScaled_predecessorOvershoot
    {p D c : ℕ} (hp : 0 < p) (hD : 0 < D) (hc : 1 < c)
    (hover :
      Nat.gcd D (2 ^ (c - 1) - 1) * p ≤
        2 * D - p * (2 ^ (c - 1) - 1)) :
    BlockDyadicSafeAt p D (c - 1) := by
  let q := 2 ^ (c - 1) - 1
  let g := Nat.gcd D q
  have hpowpos : 0 < 2 ^ (c - 1) := pow_pos (by omega) _
  have hqpos : 0 < q := by
    dsimp only [q]
    exact pow_sub_one_pos_of_ne_zero 2 (c - 1) (by omega) (by omega)
  have hgpos : 0 < g := by
    exact Nat.gcd_pos_of_pos_left q hD
  have hover' : g * p ≤ 2 * D - p * q := by
    simpa only [g, q] using hover
  have hbase : p * q ≤ 2 * D := by
    by_contra hnot
    have hreverse : 2 * D ≤ p * q := Nat.le_of_not_ge hnot
    have hzero : 2 * D - p * q = 0 := Nat.sub_eq_zero_of_le hreverse
    rw [hzero] at hover'
    have hpositive : 0 < g * p := Nat.mul_pos hgpos hp
    omega
  have hp_le_scaled : p ≤ g * p := by
    calc
      p = 1 * p := by simp
      _ ≤ g * p := Nat.mul_le_mul_right p hgpos
  have hp_le_overshoot : p ≤ 2 * D - p * q :=
    hp_le_scaled.trans hover'
  have hqsucc : q + 1 = 2 ^ (c - 1) := by
    simpa only [q] using Nat.sub_add_cancel hpowpos
  have hsubadd : (2 * D - p * q) + p * q = 2 * D :=
    Nat.sub_add_cancel hbase
  unfold BlockDyadicSafeAt
  calc
    p * 2 ^ (c - 1) = p * q + p := by rw [← hqsucc]; ring
    _ ≤ p * q + (2 * D - p * q) :=
      Nat.add_le_add_left hp_le_overshoot (p * q)
    _ = 2 * D := by omega

/-- Actual-orbit producer suggested by the primitive quotient replay.  It is
required only on a putative unsafe skipped rank. -/
def HalfGreedyUnsafeSkipGcdOvershootSupply : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      ¬ BlockDyadicSafeAt
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) →
      Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1) *
          (halfGreedyResidualDisplayedNumerator n).natAbs ≤
        2 * halfGreedyPrefixDenominator n -
          (halfGreedyResidualDisplayedNumerator n).natAbs *
            (2 ^ (n + 1) - 1)

/-- The primitive overshoot producer excludes every unsafe skip and hence
closes exact half-membership. -/
theorem half_mem_mersenneAchievementSet_of_unsafeSkipGcdOvershootSupply
    (hsupply : HalfGreedyUnsafeSkipGcdOvershootSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_actualBlockSafe
  intro n hskip
  by_contra hunsafe
  let p := (halfGreedyResidualDisplayedNumerator n).natAbs
  let D := halfGreedyPrefixDenominator n
  have hp : 0 < p := by
    by_contra hnot
    have hp0 : p = 0 := Nat.eq_zero_of_not_pos hnot
    apply hunsafe
    simp only [BlockDyadicSafeAt, p, hp0, zero_mul, zero_le]
  have hD : 0 < D := by
    simpa only [D] using Rat.den_pos (halfGreedyPrefixRat n)
  have hover : Nat.gcd D (2 ^ (n + 1) - 1) * p ≤
      2 * D - p * (2 ^ (n + 1) - 1) := by
    simpa only [p, D] using hsupply n hskip hunsafe
  have hsafe := blockDyadicSafeAt_of_gcdScaled_predecessorOvershoot
    (p := p) (D := D) (c := n + 2) hp hD (by omega) (by
      simpa only [show n + 2 - 1 = n + 1 by omega] using hover)
  exact hunsafe (by
    simpa only [p, D, show n + 2 - 1 = n + 1 by omega] using hsafe)

/-- Executable form of the actual-orbit producer: divide the predecessor
overshoot by its guaranteed gcd and compare the resulting primitive quotient
directly with the reduced residual numerator. -/
def HalfGreedyUnsafeSkipPrimitiveOvershootSupply : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      ¬ BlockDyadicSafeAt
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) →
      (halfGreedyResidualDisplayedNumerator n).natAbs ≤
        (2 * halfGreedyPrefixDenominator n -
            (halfGreedyResidualDisplayedNumerator n).natAbs *
              (2 ^ (n + 1) - 1)) /
          Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1)

/-- The gcd-scaled and primitive-quotient actual-orbit producers are exactly
equivalent, not merely one-way sufficient conditions. -/
theorem unsafeSkipGcdOvershootSupply_iff_primitive :
    HalfGreedyUnsafeSkipGcdOvershootSupply ↔
      HalfGreedyUnsafeSkipPrimitiveOvershootSupply := by
  constructor <;> intro h n hskip hunsafe
  · have hiff := gcdScaled_predecessorOvershoot_iff_primitiveQuotient
      (p := (halfGreedyResidualDisplayedNumerator n).natAbs)
      (D := halfGreedyPrefixDenominator n) (c := n + 2)
      (Rat.den_pos (halfGreedyPrefixRat n))
    have hiff' :
        Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1) *
              (halfGreedyResidualDisplayedNumerator n).natAbs ≤
            2 * halfGreedyPrefixDenominator n -
              (halfGreedyResidualDisplayedNumerator n).natAbs *
                (2 ^ (n + 1) - 1) ↔
          (halfGreedyResidualDisplayedNumerator n).natAbs ≤
            (2 * halfGreedyPrefixDenominator n -
                (halfGreedyResidualDisplayedNumerator n).natAbs *
                  (2 ^ (n + 1) - 1)) /
              Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1) := by
      simpa only [show n + 2 - 1 = n + 1 by omega] using hiff
    exact hiff'.1 (h n hskip hunsafe)
  · have hiff := gcdScaled_predecessorOvershoot_iff_primitiveQuotient
      (p := (halfGreedyResidualDisplayedNumerator n).natAbs)
      (D := halfGreedyPrefixDenominator n) (c := n + 2)
      (Rat.den_pos (halfGreedyPrefixRat n))
    have hiff' :
        Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1) *
              (halfGreedyResidualDisplayedNumerator n).natAbs ≤
            2 * halfGreedyPrefixDenominator n -
              (halfGreedyResidualDisplayedNumerator n).natAbs *
                (2 ^ (n + 1) - 1) ↔
          (halfGreedyResidualDisplayedNumerator n).natAbs ≤
            (2 * halfGreedyPrefixDenominator n -
                (halfGreedyResidualDisplayedNumerator n).natAbs *
                  (2 ^ (n + 1) - 1)) /
              Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1) := by
      simpa only [show n + 2 - 1 = n + 1 by omega] using hiff
    exact hiff'.2 (h n hskip hunsafe)

/-- The exact primitive quotient inequality on each putative unsafe skip is a
complete arithmetic endpoint for half-membership. -/
theorem half_mem_mersenneAchievementSet_of_unsafeSkipPrimitiveOvershootSupply
    (hsupply : HalfGreedyUnsafeSkipPrimitiveOvershootSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_unsafeSkipGcdOvershootSupply
  exact unsafeSkipGcdOvershootSupply_iff_primitive.mpr hsupply

/-- The factor `11` seen sharply in exact replay is a strict strengthening of
the primitive overshoot producer. -/
def HalfGreedyUnsafeSkipElevenGcdOvershootSupply : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      ¬ BlockDyadicSafeAt
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) →
      11 * (Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1) *
          (halfGreedyResidualDisplayedNumerator n).natAbs) ≤
        2 * halfGreedyPrefixDenominator n -
          (halfGreedyResidualDisplayedNumerator n).natAbs *
            (2 ^ (n + 1) - 1)

theorem unsafeSkipGcdOvershootSupply_of_eleven
    (hsupply : HalfGreedyUnsafeSkipElevenGcdOvershootSupply) :
    HalfGreedyUnsafeSkipGcdOvershootSupply := by
  intro n hskip hunsafe
  have h := hsupply n hskip hunsafe
  have hscale :
      Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1) *
          (halfGreedyResidualDisplayedNumerator n).natAbs ≤
        11 * (Nat.gcd (halfGreedyPrefixDenominator n) (2 ^ (n + 1) - 1) *
          (halfGreedyResidualDisplayedNumerator n).natAbs) := by omega
  exact hscale.trans h

theorem half_mem_mersenneAchievementSet_of_unsafeSkipElevenGcdOvershootSupply
    (hsupply : HalfGreedyUnsafeSkipElevenGcdOvershootSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_unsafeSkipGcdOvershootSupply
    (unsafeSkipGcdOvershootSupply_of_eleven hsupply)

/-! ## Cofinal selected ranks and canonical next-take blocks -/

/-- The rational and real half-greedy residuals are strictly positive at
every finite rank.  Nonnegativity is automatic from greedy subtraction, while
the displayed numerator is odd and therefore cannot vanish.  This is the
finite-prefix obstruction that prevents the half orbit from terminating. -/
theorem greedyHalfRemainder_pos (n : ℕ) :
    0 < greedyMersenneRemainder (1 / 2 : ℝ) n := by
  have hp0 : 0 ≤ halfGreedyResidualDisplayedNumerator n :=
    halfGreedyResidualDisplayedNumerator_nonneg n
  have hpne : halfGreedyResidualDisplayedNumerator n ≠ 0 := by
    intro hpzero
    rcases halfGreedyResidualDisplayedNumerator_odd n with ⟨k, hk⟩
    rw [hpzero] at hk
    omega
  have hp : 0 < halfGreedyResidualDisplayedNumerator n :=
    lt_of_le_of_ne hp0 (Ne.symm hpne)
  have hD : 0 < halfGreedyPrefixDenominator n :=
    Rat.den_pos (halfGreedyPrefixRat n)
  have hrat :
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
    rw [greedyHalfRemainderRat_eq_displayed_divInt, Rat.divInt_eq_div]
    positivity
  have hcast :
      (0 : ℝ) <
        ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) := by
    exact_mod_cast hrat
  simpa using hcast

/-- If the greedy support has no selected exponent in the next `L` ranks,
the real residual is unchanged across that block.  This local copy is kept
in the dyadic-prefix module so the block decomposition does not depend on
the later Boolean--Möbius layer. -/
theorem greedyMersenneRemainder_add_eq_of_local_support_gap
    (x : ℝ) (K : ℕ) :
    ∀ L : ℕ,
      (∀ n : ℕ, K < n → n ≤ K + L →
        n ∉ greedyMersenneSupport x) →
      greedyMersenneRemainder x (K + L) =
        greedyMersenneRemainder x K := by
  intro L
  induction L with
  | zero =>
      simp
  | succ L ih =>
      intro hgap
      have hprevGap :
          ∀ n : ℕ, K < n → n ≤ K + L →
            n ∉ greedyMersenneSupport x := by
        intro n hKn hnKL
        exact hgap n hKn (by omega)
      have hprev := ih hprevGap
      have hnot :
          K + L + 1 ∉ greedyMersenneSupport x :=
        hgap (K + L + 1) (by omega) (by omega)
      have hskip :
          ¬ mersenneWeight (K + L + 1) ≤
            greedyMersenneRemainder x (K + L) := by
        simpa only [succ_mem_greedyMersenneSupport_iff] using hnot
      rw [show K + (L + 1) = K + L + 1 by omega,
        greedyMersenneRemainder_succ, if_neg hskip, hprev]

/-- Selected ranks of the actual half-greedy orbit are cofinal.  Otherwise
the residual would freeze at a strictly positive value, while summability
forces a later Mersenne weight below that value and hence forces a take. -/
theorem greedyHalf_selectedRanks_cofinal (N : ℕ) :
    ∃ c : ℕ, N < c ∧
      c ∈ greedyMersenneSupport (1 / 2 : ℝ) := by
  by_contra hcofinal
  push_neg at hcofinal
  have hremPos : 0 < greedyMersenneRemainder (1 / 2 : ℝ) N :=
    greedyHalfRemainder_pos N
  have hlim :=
    summable_mersenneWeight.tendsto_atTop_zero
  have hevent :
      ∀ᶠ k : ℕ in Filter.atTop,
        mersenneWeight (k + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) N :=
    hlim.eventually_mem (Iio_mem_nhds hremPos)
  have hlarge : ∀ᶠ k : ℕ in Filter.atTop, N ≤ k :=
    Filter.eventually_ge_atTop N
  obtain ⟨k, hkWeight, hNk⟩ := (hevent.and hlarge).exists
  have hgap :
      ∀ m : ℕ, N < m → m ≤ k →
        m ∉ greedyMersenneSupport (1 / 2 : ℝ) := by
    intro m hNm _ hm
    exact (hcofinal m hNm) hm
  have hrem :
      greedyMersenneRemainder (1 / 2 : ℝ) k =
        greedyMersenneRemainder (1 / 2 : ℝ) N := by
    obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hNk
    exact greedyMersenneRemainder_add_eq_of_local_support_gap
      (1 / 2 : ℝ) N L hgap
  have htake :
      mersenneWeight (k + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) k := by
    rw [hrem]
    exact hkWeight.le
  have hmem :
      k + 1 ∈ greedyMersenneSupport (1 / 2 : ℝ) :=
    (succ_mem_greedyMersenneSupport_iff (1 / 2 : ℝ) k).2 htake
  exact (hcofinal (k + 1) (by omega)) hmem

/-- The first selected half-greedy rank strictly after `N`.  Cofinality makes
this a total canonical block endpoint rather than an advisory witness. -/
noncomputable def nextHalfGreedyTakenRank (N : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (greedyHalf_selectedRanks_cofinal N)

theorem nextHalfGreedyTakenRank_spec (N : ℕ) :
    N < nextHalfGreedyTakenRank N ∧
      nextHalfGreedyTakenRank N ∈
        greedyMersenneSupport (1 / 2 : ℝ) := by
  classical
  unfold nextHalfGreedyTakenRank
  exact Nat.find_spec (greedyHalf_selectedRanks_cofinal N)

/-- No actual take lies strictly between a rank and its canonical next
selected rank. -/
theorem not_mem_greedyHalf_between_nextTakenRank
    {N k : ℕ} (hNk : N < k)
    (hkNext : k < nextHalfGreedyTakenRank N) :
    k ∉ greedyMersenneSupport (1 / 2 : ℝ) := by
  classical
  unfold nextHalfGreedyTakenRank at hkNext
  intro hk
  exact (Nat.find_min (greedyHalf_selectedRanks_cofinal N) hkNext)
    ⟨hNk, hk⟩

/-- In the displayed state immediately after a selected rank `b`, the
canonical next selected rank is exactly the first `BlockTakeAt` after `b`.
All intervening actual skips keep the displayed numerator and denominator
fixed, so the abstract block predicate and the real greedy orbit coincide. -/
theorem nextHalfGreedyTakenRank_isFirstBlockTakeAfter
    (b : ℕ)
    (hbmem : b ∈ greedyMersenneSupport (1 / 2 : ℝ)) :
    IsFirstBlockTakeAfter
      (halfGreedyResidualDisplayedNumerator b).natAbs
      (halfGreedyPrefixDenominator b)
      b (nextHalfGreedyTakenRank b) := by
  let c := nextHalfGreedyTakenRank b
  have hcSpec :
      b < c ∧ c ∈ greedyMersenneSupport (1 / 2 : ℝ) := by
    simpa only [c] using nextHalfGreedyTakenRank_spec b
  have hcoord :
      ∀ m : ℕ, b ≤ m → m < c →
        halfGreedyResidualDisplayedNumerator m =
            halfGreedyResidualDisplayedNumerator b ∧
          halfGreedyPrefixDenominator m =
            halfGreedyPrefixDenominator b := by
    intro m hbm hmc
    have hrun := halfGreedy_coordinates_add_of_all_skips
      b (m - b) (fun t ht ↦ ?_)
    · simpa [Nat.add_sub_of_le hbm] using hrun
    · have hbt : b < b + t + 1 := by omega
      have htM : b + t + 1 ≤ m := by omega
      have htC : b + t + 1 < c := lt_of_le_of_lt htM hmc
      have hnot :=
        not_mem_greedyHalf_between_nextTakenRank hbt (by
          simpa only [c] using htC)
      simpa only [succ_mem_greedyMersenneSupport_iff] using hnot
  refine ⟨hcSpec.1, ?_, ?_⟩
  · have hcpos : 0 < c := by omega
    have hcIndex : c - 1 + 1 = c := by omega
    have htake :
        mersenneWeight c ≤
          greedyMersenneRemainder (1 / 2 : ℝ) (c - 1) := by
      have :=
        (succ_mem_greedyMersenneSupport_iff
          (1 / 2 : ℝ) (c - 1)).1 (by
            simpa only [hcIndex] using hcSpec.2)
      simpa only [hcIndex] using this
    have hblock :=
      (greedyHalf_take_iff_BlockTakeAt (c - 1)).1 (by
        simpa only [hcIndex] using htake)
    have hcoords := hcoord (c - 1) (by omega) (by omega)
    rw [hcIndex] at hblock
    simpa only [hcoords.1, hcoords.2] using hblock
  · intro k hbk hkc hblock
    have hkpos : 0 < k := by omega
    have hkIndex : k - 1 + 1 = k := by omega
    have hcoords := hcoord (k - 1) (by omega) (by omega)
    have hblockActual :
        BlockTakeAt
          (halfGreedyResidualDisplayedNumerator (k - 1)).natAbs
          (halfGreedyPrefixDenominator (k - 1)) k := by
      simpa only [hcoords.1, hcoords.2] using hblock
    have htake :=
      (greedyHalf_take_iff_BlockTakeAt (k - 1)).2 (by
        simpa only [hkIndex] using hblockActual)
    have hmem0 :=
      (succ_mem_greedyMersenneSupport_iff
        (1 / 2 : ℝ) (k - 1)).2 (by
          simpa only [hkIndex] using htake)
    have hmem :
        k ∈ greedyMersenneSupport (1 / 2 : ℝ) := by
      simpa only [hkIndex] using hmem0
    exact
      (not_mem_greedyHalf_between_nextTakenRank
        hbk (by simpa only [c] using hkc)) hmem

/-- The single arithmetic margin attached to the actual consecutive-take
block from selected rank `b` to the canonical next selected rank `c`.
Adjacent takes carry no skipped decisions and therefore need no inequality. -/
def HalfGreedyTakenBlockRawMargin (b c : ℕ) : Prop :=
  c = b + 1 ∨
    ((halfGreedyResidualDisplayedNumerator (b - 1)).natAbs *
          (2 ^ b - 1) -
        2 * halfGreedyPrefixDenominator (b - 1)) *
          2 ^ (c - 1) ≤
      2 * (halfGreedyPrefixDenominator (b - 1) *
        (2 ^ b - 1))

/-- One margin per selected rank, evaluated only at its actual next selected
rank.  Unlike `HalfGreedyUnsafeSkipActualRawMarginSupply`, this does not
repeat the same block witness once for every skipped decision in the block. -/
def HalfGreedyConsecutiveTakeRawMarginSupply : Prop :=
  ∀ b : ℕ,
    b ∈ greedyMersenneSupport (1 / 2 : ℝ) →
      HalfGreedyTakenBlockRawMargin b (nextHalfGreedyTakenRank b)

/-- Reciprocal-floor form of the one-per-block producer.  At a nonadjacent
consecutive selected pair `b<c`, the only forbidden value of the reciprocal
floor in the post-`b` displayed state is the lower Mersenne integer
`2^(c-1)-1`. -/
def HalfGreedyConsecutiveTakeReciprocalFloorSupply : Prop :=
  ∀ b : ℕ,
    b ∈ greedyMersenneSupport (1 / 2 : ℝ) →
      let c := nextHalfGreedyTakenRank b
      c = b + 1 ∨
        (2 * halfGreedyPrefixDenominator b) /
            (halfGreedyResidualDisplayedNumerator b).natAbs ≠
          2 ^ (c - 1) - 1

/-- Exact arithmetic identification of the new block producer: the raw
source margin and the post-take reciprocal-floor exclusion are equivalent
on every actual consecutive-take block. -/
theorem consecutiveTakeRawMarginSupply_iff_reciprocalFloor :
    HalfGreedyConsecutiveTakeRawMarginSupply ↔
      HalfGreedyConsecutiveTakeReciprocalFloorSupply := by
  constructor
  · intro hraw b hbmem
    let c := nextHalfGreedyTakenRank b
    by_cases hadj : c = b + 1
    · exact Or.inl hadj
    · right
      have hbc : b < c := by
        simpa only [c] using (nextHalfGreedyTakenRank_spec b).1
      have hgap : b + 1 < c := by omega
      have hbpos : 0 < b := by
        apply Nat.pos_of_ne_zero
        intro hbzero
        apply zero_not_mem_greedyMersenneSupport (1 / 2 : ℝ)
        simpa only [hbzero] using hbmem
      have hbIndex : b - 1 + 1 = b := by omega
      have htake :
          mersenneWeight (b - 1 + 1) ≤
            greedyMersenneRemainder (1 / 2 : ℝ) (b - 1) := by
        exact (succ_mem_greedyMersenneSupport_iff
          (1 / 2 : ℝ) (b - 1)).1 (by
            simpa only [hbIndex] using hbmem)
      obtain ⟨g, hg, hnum, hden⟩ :=
        halfGreedy_take_raw_reduces_to_next (b - 1) htake
      have hp :
          0 < (halfGreedyResidualDisplayedNumerator b).natAbs := by
        apply Int.natAbs_pos.mpr
        intro hpzero
        rcases halfGreedyResidualDisplayedNumerator_odd b with ⟨j, hj⟩
        rw [hpzero] at hj
        omega
      have hfirst :
          IsFirstBlockTakeAfter
            (halfGreedyResidualDisplayedNumerator b).natAbs
            (halfGreedyPrefixDenominator b) b c := by
        simpa only [c] using
          nextHalfGreedyTakenRank_isFirstBlockTakeAfter b hbmem
      have hiff :=
        takenBlock_rawMargin_iff_reducedReciprocalFloor_ne_mersenne
          (p :=
            (halfGreedyResidualDisplayedNumerator (b - 1)).natAbs)
          (D := halfGreedyPrefixDenominator (b - 1))
          (b := b) (g := g)
          (p' := (halfGreedyResidualDisplayedNumerator b).natAbs)
          (D' := halfGreedyPrefixDenominator b)
          (c := c) hg hp (by simpa only [hbIndex] using hnum)
            (by simpa only [hbIndex] using hden) hfirst hgap
      have hmargin :
          ((halfGreedyResidualDisplayedNumerator (b - 1)).natAbs *
                (2 ^ b - 1) -
              2 * halfGreedyPrefixDenominator (b - 1)) *
                2 ^ (c - 1) ≤
            2 * (halfGreedyPrefixDenominator (b - 1) *
              (2 ^ b - 1)) := by
        rcases hraw b hbmem with h | h
        · exact False.elim (hadj (by simpa only [c] using h))
        · simpa only [c] using h
      exact hiff.1 hmargin
  · intro hfloor b hbmem
    let c := nextHalfGreedyTakenRank b
    by_cases hadj : c = b + 1
    · exact Or.inl (by simpa only [c] using hadj)
    · right
      have hbc : b < c := by
        simpa only [c] using (nextHalfGreedyTakenRank_spec b).1
      have hgap : b + 1 < c := by omega
      have hbpos : 0 < b := by
        apply Nat.pos_of_ne_zero
        intro hbzero
        apply zero_not_mem_greedyMersenneSupport (1 / 2 : ℝ)
        simpa only [hbzero] using hbmem
      have hbIndex : b - 1 + 1 = b := by omega
      have htake :
          mersenneWeight (b - 1 + 1) ≤
            greedyMersenneRemainder (1 / 2 : ℝ) (b - 1) := by
        exact (succ_mem_greedyMersenneSupport_iff
          (1 / 2 : ℝ) (b - 1)).1 (by
            simpa only [hbIndex] using hbmem)
      obtain ⟨g, hg, hnum, hden⟩ :=
        halfGreedy_take_raw_reduces_to_next (b - 1) htake
      have hp :
          0 < (halfGreedyResidualDisplayedNumerator b).natAbs := by
        apply Int.natAbs_pos.mpr
        intro hpzero
        rcases halfGreedyResidualDisplayedNumerator_odd b with ⟨j, hj⟩
        rw [hpzero] at hj
        omega
      have hfirst :
          IsFirstBlockTakeAfter
            (halfGreedyResidualDisplayedNumerator b).natAbs
            (halfGreedyPrefixDenominator b) b c := by
        simpa only [c] using
          nextHalfGreedyTakenRank_isFirstBlockTakeAfter b hbmem
      have hiff :=
        takenBlock_rawMargin_iff_reducedReciprocalFloor_ne_mersenne
          (p :=
            (halfGreedyResidualDisplayedNumerator (b - 1)).natAbs)
          (D := halfGreedyPrefixDenominator (b - 1))
          (b := b) (g := g)
          (p' := (halfGreedyResidualDisplayedNumerator b).natAbs)
          (D' := halfGreedyPrefixDenominator b)
          (c := c) hg hp (by simpa only [hbIndex] using hnum)
            (by simpa only [hbIndex] using hden) hfirst hgap
      apply hiff.2
      rcases hfloor b hbmem with h | h
      · exact False.elim (hadj (by simpa only [c] using h))
      · simpa only [c] using h

/-- A selected source rank below a skipped decision, together with the fact
that no selection intervenes, determines the complete actual raw-margin
witness from the one-per-block supply. -/
theorem nonempty_actualRawMarginWitness_of_selected_source
    {n b : ℕ} (hbpos : 0 < b) (hb : b < n + 1)
    (htakeSource :
      b ∈ greedyMersenneSupport (1 / 2 : ℝ))
    (hgap : ∀ k : ℕ, b < k → k ≤ n + 1 →
      k ∉ greedyMersenneSupport (1 / 2 : ℝ))
    (hsupply : HalfGreedyConsecutiveTakeRawMarginSupply) :
    Nonempty (HalfGreedySkippedActualRawMarginWitness n) := by
  let c := nextHalfGreedyTakenRank b
  have hcSpec :
      b < c ∧ c ∈ greedyMersenneSupport (1 / 2 : ℝ) := by
    simpa only [c] using nextHalfGreedyTakenRank_spec b
  have hnc : n + 1 < c := by
    by_contra hnot
    exact hgap c hcSpec.1 (le_of_not_gt hnot) hcSpec.2
  have hbIndex : b - 1 + 1 = b := by omega
  have hcIndex : c - 1 + 1 = c := by omega
  have htakeSource' :
      mersenneWeight b ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (b - 1) := by
    have htake :=
      (succ_mem_greedyMersenneSupport_iff
        (1 / 2 : ℝ) (b - 1)).1 (by
          simpa only [hbIndex] using htakeSource)
    simpa only [hbIndex] using htake
  have htakeNext :
      mersenneWeight c ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (c - 1) := by
    have htake :=
      (succ_mem_greedyMersenneSupport_iff
        (1 / 2 : ℝ) (c - 1)).1 (by
          simpa only [hcIndex] using hcSpec.2)
    simpa only [hcIndex] using htake
  have hskipBetween :
      ∀ k : ℕ, b < k → k < c →
        ¬ mersenneWeight k ≤
          greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) := by
    intro k hbk hkc htake
    have hkpos : 0 < k := by omega
    have hkIndex : k - 1 + 1 = k := by omega
    have hmem :
        k ∈ greedyMersenneSupport (1 / 2 : ℝ) := by
      have :=
        (succ_mem_greedyMersenneSupport_iff
          (1 / 2 : ℝ) (k - 1)).2 (by
            simpa only [hkIndex] using htake)
      simpa only [hkIndex] using this
    exact
      (not_mem_greedyHalf_between_nextTakenRank
        hbk (by simpa only [c] using hkc)) hmem
  refine ⟨{
    sourceRank := b
    nextRank := c
    hbpos := hbpos
    hb := hb
    hc := hnc
    htakeSource := htakeSource'
    htakeNext := htakeNext
    hskipBetween := hskipBetween
    hmargin := ?_ }⟩
  simpa only [HalfGreedyTakenBlockRawMargin, c] using
    hsupply b htakeSource

/-- Rank two is the first selected exponent of the half-greedy orbit. -/
theorem two_mem_greedyHalfSupport :
    2 ∈ greedyMersenneSupport (1 / 2 : ℝ) := by
  have htake :
      mersenneWeight 2 ≤
        greedyMersenneRemainder (1 / 2 : ℝ) 1 := by
    norm_num [mersenneWeight, greedyMersenneRemainder]
  simpa using
    (succ_mem_greedyMersenneSupport_iff (1 / 2 : ℝ) 1).2 htake

/-- The one-per-consecutive-take-block raw margin is sufficient for exact
half-membership.  For a putative unsafe skip at rank `n+1`, take the maximum
selected exponent `b ≤ n`; cofinality supplies the canonical next selected
rank `c`, and maximality/minimality put the skip inside the unique block
`(b,c)`. -/
theorem half_mem_mersenneAchievementSet_of_consecutiveTakeRawMarginSupply
    (hsupply : HalfGreedyConsecutiveTakeRawMarginSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_unsafeSkipActualRawMarginSupply
  intro n hskip hunsafe
  by_cases hn : 2 ≤ n
  · classical
    let F : Finset ℕ :=
      (Finset.range (n + 1)).filter
        (fun k ↦ k ∈ greedyMersenneSupport (1 / 2 : ℝ))
    have hFne : F.Nonempty := by
      refine ⟨2, Finset.mem_filter.mpr ⟨?_, two_mem_greedyHalfSupport⟩⟩
      exact Finset.mem_range.mpr (by omega)
    let b : ℕ := F.max' hFne
    have hbF : b ∈ F := Finset.max'_mem F hFne
    have hbData := Finset.mem_filter.mp hbF
    have hbLe : b ≤ n := by
      have := Finset.mem_range.mp hbData.1
      omega
    have hbTake :
        b ∈ greedyMersenneSupport (1 / 2 : ℝ) := hbData.2
    have hbpos : 0 < b := by
      apply Nat.pos_of_ne_zero
      intro hbzero
      apply zero_not_mem_greedyMersenneSupport (1 / 2 : ℝ)
      simpa only [hbzero] using hbTake
    have hnNot :
        n + 1 ∉ greedyMersenneSupport (1 / 2 : ℝ) := by
      simpa only [succ_mem_greedyMersenneSupport_iff] using hskip
    have hgap :
        ∀ k : ℕ, b < k → k ≤ n + 1 →
          k ∉ greedyMersenneSupport (1 / 2 : ℝ) := by
      intro k hbk hkUpper hkTake
      by_cases hkend : k = n + 1
      · exact hnNot (by simpa only [hkend] using hkTake)
      · have hklt : k < n + 1 := lt_of_le_of_ne hkUpper hkend
        have hkF : k ∈ F := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hklt, hkTake⟩
        have hkle : k ≤ b := Finset.le_max' F k hkF
        omega
    exact nonempty_actualRawMarginWitness_of_selected_source
      hbpos (by omega) hbTake hgap hsupply
  · have hnlt : n < 2 := by omega
    interval_cases n
    · exfalso
      apply hunsafe
      norm_num [BlockDyadicSafeAt, halfGreedyResidualDisplayedNumerator,
        halfGreedyPrefixDenominator, halfGreedyPrefixRat,
        greedyMersennePrefixRat, finiteErdosSum]
    · exfalso
      apply hskip
      norm_num [mersenneWeight, greedyMersenneRemainder]

/-- Final reciprocal-floor endpoint: excluding one Mersenne integer at each
nonadjacent consecutive-take block proves that one half belongs to the
Mersenne achievement set. -/
theorem
    half_mem_mersenneAchievementSet_of_consecutiveTakeReciprocalFloorSupply
    (hsupply : HalfGreedyConsecutiveTakeReciprocalFloorSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_consecutiveTakeRawMarginSupply
  exact consecutiveTakeRawMarginSupply_iff_reciprocalFloor.mpr hsupply

/-! ### The consecutive-take reciprocal dynamical system -/

/-- Reciprocal of a displayed residual `p/(2D)`. -/
def blockReciprocalRat (p D : ℕ) : ℚ :=
  (2 * D : ℚ) / p

/-- Möbius update of the reciprocal residual after subtracting the
Mersenne weight at rank `b`. -/
def takenReciprocalMapRat (x : ℚ) (b : ℕ) : ℚ :=
  x * (2 ^ b - 1) / ((2 ^ b - 1) - x)

/-- Before fraction reduction, a positive taken residual evolves by the
one-dimensional Möbius map on reciprocal coordinates. -/
theorem rawTaken_blockReciprocalRat_eq_map
    {p D b : ℕ} (hp : 0 < p)
    (hraw : 0 < rawTakenResidualNumerator p D b) :
    blockReciprocalRat
        (rawTakenResidualNumerator p D b)
        (rawTakenResidualDenominator D b) =
      takenReciprocalMapRat (blockReciprocalRat p D) b := by
  let q := 2 ^ b - 1
  have hlt : 2 * D < p * q := by
    unfold rawTakenResidualNumerator at hraw
    simpa only [q, Nat.sub_pos_iff_lt] using hraw
  have hle : 2 * D ≤ p * q := hlt.le
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hrawQ :
      ((p * q - 2 * D : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_iff_lt.mpr hlt).ne'
  have hpQpos : (0 : ℚ) < p := by exact_mod_cast hp
  have hltQ : (2 * D : ℚ) < p * q := by exact_mod_cast hlt
  have hdenPos :
      0 < (q : ℚ) - (2 * D : ℚ) / p := by
    rw [sub_pos, div_lt_iff₀ hpQpos]
    simpa only [mul_comm] using hltQ
  have hdenQ : (q : ℚ) - (2 * D : ℚ) / p ≠ 0 :=
    hdenPos.ne'
  have hqQ : (q : ℚ) = (2 : ℚ) ^ b - 1 := by
    simp [q]
  unfold blockReciprocalRat takenReciprocalMapRat
  simp only [rawTakenResidualNumerator, rawTakenResidualDenominator]
  rw [show 2 ^ b - 1 = q by rfl]
  push_cast
  rw [Nat.cast_sub hle]
  rw [← hqQ]
  field_simp [hpQ, hrawQ, hdenQ]
  push_cast
  ring

/-- A positive common reduction factor does not change reciprocal
coordinates. -/
theorem blockReciprocalRat_commonFactor
    {g p D : ℕ} (hg : 0 < g) (hp : 0 < p) :
    blockReciprocalRat (g * p) (g * D) =
      blockReciprocalRat p D := by
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold blockReciprocalRat
  push_cast
  field_simp [hgQ, hpQ]

/-- The displayed numerator of every finite half-greedy residual is
strictly positive. -/
theorem halfGreedyResidualDisplayedNumerator_natAbs_pos (n : ℕ) :
    0 < (halfGreedyResidualDisplayedNumerator n).natAbs := by
  apply Int.natAbs_pos.mpr
  intro hz
  rcases halfGreedyResidualDisplayedNumerator_odd n with ⟨j, hj⟩
  rw [hz] at hj
  omega

/-- Reciprocal coordinate of the actual reduced half-greedy residual. -/
def halfGreedyReciprocalRat (n : ℕ) : ℚ :=
  blockReciprocalRat
    (halfGreedyResidualDisplayedNumerator n).natAbs
    (halfGreedyPrefixDenominator n)

/-- Exact one-step recurrence at every selected rank.  Arbitrary gcd
reduction in the displayed fraction cancels, leaving the same Möbius map
as in the unreduced coordinates. -/
theorem halfGreedyReciprocalRat_succ_of_take
    (n : ℕ)
    (htake : mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    halfGreedyReciprocalRat (n + 1) =
      takenReciprocalMapRat (halfGreedyReciprocalRat n) (n + 1) := by
  obtain ⟨g, hg, hnum, hden⟩ :=
    halfGreedy_take_raw_reduces_to_next n htake
  have hp := halfGreedyResidualDisplayedNumerator_natAbs_pos n
  have hp' := halfGreedyResidualDisplayedNumerator_natAbs_pos (n + 1)
  have hraw :
      0 < rawTakenResidualNumerator
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) := by
    rw [hnum]
    exact Nat.mul_pos hg hp'
  unfold halfGreedyReciprocalRat
  calc
    blockReciprocalRat
        (halfGreedyResidualDisplayedNumerator (n + 1)).natAbs
        (halfGreedyPrefixDenominator (n + 1)) =
      blockReciprocalRat
        (rawTakenResidualNumerator
          (halfGreedyResidualDisplayedNumerator n).natAbs
          (halfGreedyPrefixDenominator n) (n + 1))
        (rawTakenResidualDenominator
          (halfGreedyPrefixDenominator n) (n + 1)) := by
            rw [hnum, hden]
            exact (blockReciprocalRat_commonFactor hg hp').symm
    _ = takenReciprocalMapRat
        (blockReciprocalRat
          (halfGreedyResidualDisplayedNumerator n).natAbs
          (halfGreedyPrefixDenominator n)) (n + 1) :=
      rawTaken_blockReciprocalRat_eq_map hp hraw

#print axioms half_mem_mersenneAchievementSet_of_actualBlockSafe
#print axioms greedyHalf_take_iff_BlockTakeAt
#print axioms halfGreedy_take_raw_reduces_to_next
#print axioms half_mem_mersenneAchievementSet_of_skippedRawBlockMarginSupply
#print axioms half_mem_mersenneAchievementSet_of_skippedActualRawMarginSupply
#print axioms half_mem_mersenneAchievementSet_of_unsafeSkipActualRawMarginSupply
#print axioms blockDyadicSafeAt_iff_rawPredecessorOvershoot
#print axioms rawPredecessorOvershoot_of_gcdScaled
#print axioms rawSafe_but_not_gcdScaled_fixture
#print axioms firstTake_rank9_after_rank5_fixture
#print axioms factorEleven_predecessorOvershoot_not_inductive_fixture
#print axioms gcd_dvd_predecessorOvershoot
#print axioms unsafeSandwich_consecutive_gcd_lt
#print axioms greedyHalf_unsafeSkip_consecutive_gcd_lt
#print axioms gcdScaled_predecessorOvershoot_iff_primitiveQuotient
#print axioms blockDyadicSafeAt_of_gcdScaled_predecessorOvershoot
#print axioms half_mem_mersenneAchievementSet_of_unsafeSkipGcdOvershootSupply
#print axioms unsafeSkipGcdOvershootSupply_iff_primitive
#print axioms half_mem_mersenneAchievementSet_of_unsafeSkipPrimitiveOvershootSupply
#print axioms half_mem_mersenneAchievementSet_of_unsafeSkipElevenGcdOvershootSupply
#print axioms greedyHalfRemainder_pos
#print axioms greedyHalf_selectedRanks_cofinal
#print axioms nextHalfGreedyTakenRank_spec
#print axioms not_mem_greedyHalf_between_nextTakenRank
#print axioms nextHalfGreedyTakenRank_isFirstBlockTakeAfter
#print axioms consecutiveTakeRawMarginSupply_iff_reciprocalFloor
#print axioms nonempty_actualRawMarginWitness_of_selected_source
#print axioms half_mem_mersenneAchievementSet_of_consecutiveTakeRawMarginSupply
#print axioms half_mem_mersenneAchievementSet_of_consecutiveTakeReciprocalFloorSupply
#print axioms rawTaken_blockReciprocalRat_eq_map
#print axioms blockReciprocalRat_commonFactor
#print axioms halfGreedyResidualDisplayedNumerator_natAbs_pos
#print axioms halfGreedyReciprocalRat_succ_of_take
#print axioms greedyMersenneSecondChannelPhaseRat_eq_scaled_excess
#print axioms secondChannelPhaseRat_outside_unit_iff_scaled_excess
#print axioms halfGreedy_scaledExcessOutsideUnit_of_le_twenty
#print axioms half_mem_mersenneAchievementSet_of_scaledExcessOutsideUnit
#print axioms half_mem_mersenneAchievementSet_of_scaledExcessOutsideUnitFromTwentyOne
#print axioms nextDyadicExcessIntNumerator_succ
#print axioms nextDyadicExcessIntNumerator_add
#print axioms nextMersenneDecisionDefect_eq_two_excess_sub
#print axioms nextMersenneDecisionDefect_le_neg_iff_excess_nonpos
#print axioms nextMersenneDecisionDefect_mem_neg_unit_window_iff
#print axioms firstBlockTake_all_skips_safe_iff_last_margin
#print axioms reduced_nextBlock_all_skips_safe_iff_gcdFree
#print axioms takenBlock_all_next_skips_safe_iff_raw_margin
#print axioms rawTakenResidual_adjacent_margin_of_predecessor_safe
#print axioms firstBlockTake_margin_iff_reciprocalFloor_ne_mersenne
#print axioms takenBlock_rawMargin_iff_reciprocalFloor_ne_mersenne
#print axioms takenBlock_rawMargin_iff_reducedReciprocalFloor_ne_mersenne
#print axioms safeBracket_and_numeratorMonotone_not_inductive_fixture
#print axioms lcmSaturated_safeBracket_not_inductive_fixture
#print axioms mersennePrefix_doubleDepth_lt_halfDyadicCap
#print axioms greedyMersenne_forcedBlock_selected
#print axioms forcedBlock_tailExcess_eq
#print axioms mersenneWeightRemainderTail_le_four_twentyone
#print axioms mersennePrefix_threeDepth_add_two_lt_halfTwoChannelCap
#print axioms capViolation_forces_threeDepthBlock
#print axioms tripleDepthTail_lt_thirdChannel
#print axioms halfTwoChannelCap_lt_mersennePrefix_threeDepth_add_three
#print axioms exists_relaxed_capViolation_exact_block
#print axioms greedyHalf_unsafeSkip_forces_doubleBlock
#print axioms greedyHalf_capViolationSkip_forces_threeDepthBlock
#print axioms halfGreedySkippedExcessBound_of_threeDepthTakeRun
#print axioms half_mem_mersenneAchievementSet_of_threeDepthTakeRunExcessBound
#print axioms halfGreedySkippedExcessBound_of_longTakeRun
#print axioms half_mem_mersenneAchievementSet_of_longTakeRunExcessBound
#print axioms halfGreedyRawSupportExcessBound_iff
#print axioms halfGreedyPrefixReductionFactor_eq_gcd
#print axioms halfGreedyRawResidualNumerator_eq_gcd_mul_displayed
#print axioms halfGreedyRawNextDyadicExcessNumerator_eq_gcd_mul_reduced
#print axioms mem_halfGreedyPrefixSupport_iff
#print axioms halfGreedyThreeDepthTakeRunExcessBound_iff_skippedExcessBound
#print axioms greedyHalf_badSkipCapViolation_iff_primitiveLattice
#print axioms greedyHalfRemainder_eq_integerCarry_sub_coeffTail_div_pow
#print axioms halfGreedyPrefixSupportTailGap_eq_excess_div_denominator
#print axioms greedyHalf_badSkipCapViolation_iff_supportCoeffTailGap
#print axioms reducedTakeStep_coprime
#print axioms reducedTakeStep_eq
#print axioms reducedTakeStep_residualNumerator
#print axioms reducedTakeStep_residual_gcd
#print axioms halfGreedyNextDyadicExcessNumerator_succ_of_skip
#print axioms halfGreedy_takenRank_reducedTakeStep
#print axioms halfGreedy_takenRank_residualCancellation

end Erdos257PeriodNoncollapse
