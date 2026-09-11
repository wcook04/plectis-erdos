import Erdos249257.TotientActualLcmOrbitArithmetic

/-!
# Fixed-rank asymptotics on power-of-two LCM heights

This module sharpens the finite rough-Euler-product estimates used by the
actual-LCM orbit.  It records only unconditional finite inequalities; the
remaining Mersenne-residue anti-concentration needed for Erdős #249 is not
asserted here.
-/

namespace Erdos249257
namespace TotientFixedRankLcmAsymptotic

open DiagonalFreshLossBridge
open DiagonalFreshLossBridge.PowerTwoOddWindowAffine
open TotientTailPeriodKiller

/-- A `2^a`-rough integer below the actual-LCM height range has at most
`2/a` as many distinct prime factors as the roughness cutoff.  This is the
vanishing version of the fixed `1/4` estimate used by the sign corridor. -/
theorem exponent_mul_primeFactors_card_lt
    {a n : ℕ} (hn : 0 < n)
    (hrough : ∀ r : ℕ, Nat.Prime r → r ∣ n → 2 ^ a < r)
    (hnPow : n < 2 ^ (2 * 2 ^ a)) :
    a * n.primeFactors.card < 2 * 2 ^ a := by
  let t := 2 ^ a
  have hcardPower : (t + 1) ^ n.primeFactors.card ≤ n := by
    apply rough_primeFactors_card_power_le hn
    intro r hr hrdvd
    simpa [t] using hrough r hr hrdvd
  by_cases hcardZero : n.primeFactors.card = 0
  · simp [hcardZero]
  have hbase : t < t + 1 := Nat.lt_succ_self t
  have hbasePow : t ^ n.primeFactors.card <
      (t + 1) ^ n.primeFactors.card :=
    Nat.pow_lt_pow_left hbase hcardZero
  have hpow : 2 ^ (a * n.primeFactors.card) < 2 ^ (2 * t) := by
    calc
      2 ^ (a * n.primeFactors.card) = t ^ n.primeFactors.card := by
        simp [t, pow_mul]
      _ < (t + 1) ^ n.primeFactors.card := hbasePow
      _ ≤ n := hcardPower
      _ < 2 ^ (2 * t) := by simpa [t] using hnPow
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hpow

/-- Quantitative rough Euler-density estimate.  The defect is less than
`2/a`, so the density tends to one along the power-of-two LCM scale without
using the prime number theorem. -/
theorem one_sub_two_div_lt_totient_density_of_rough
    {a n : ℕ} (ha : 0 < a) (hn : 0 < n)
    (hrough : ∀ r : ℕ, Nat.Prime r → r ∣ n → 2 ^ a < r)
    (hnPow : n < 2 ^ (2 * 2 ^ a)) :
    (n : ℚ) * (1 - (2 : ℚ) / a) < Nat.totient n := by
  let t := 2 ^ a
  have hcard := exponent_mul_primeFactors_card_lt hn hrough hnPow
  have hfrac :
      (n.primeFactors.card : ℚ) / ((t + 1 : ℕ) : ℚ) < (2 : ℚ) / a := by
    have haQ : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
    have htQ : (0 : ℚ) < ((t + 1 : ℕ) : ℚ) := by positivity
    rw [div_lt_div_iff₀ htQ haQ]
    have hcardQ :
        (a : ℚ) * (n.primeFactors.card : ℚ) < 2 * (t : ℚ) := by
      exact_mod_cast (by simpa [t] using hcard)
    have htLt : (t : ℚ) < (t + 1 : ℕ) := by
      exact_mod_cast Nat.lt_succ_self t
    nlinarith only [hcardQ, htLt]
  have htotient :
      (n : ℚ) *
          (1 - (n.primeFactors.card : ℚ) / ((t + 1 : ℕ) : ℚ)) ≤
        Nat.totient n := by
    apply totient_rational_lower_bound_of_primeFactors_gt hn
    intro r hr hrdvd
    simpa [t] using hrough r hr hrdvd
  have hfactor :
      (1 : ℚ) - 2 / a <
        1 - (n.primeFactors.card : ℚ) / ((t + 1 : ℕ) : ℚ) := by
    linarith
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  exact (mul_lt_mul_of_pos_left hfactor hnQ).trans_le htotient

/-! ## Clean fixed offsets on the actual LCM ray -/

/-- If `j² ≤ t`, then `j` is not merely a divisor of `L(t)`: every prime
of `j` still occurs in the complementary cofactor `L(t) / j`.  The square
cutoff is the elementary uniform range in which the exact ray factorisation
can be used without inspecting the prime-power exponents of `j`. -/
theorem clean_periodLcm_divisor_of_sq_le
    {t j : ℕ} (hj : 0 < j) (hsq : j * j ≤ t) :
    j ∣ periodLcm t ∧
      ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm t / j := by
  have hjleSq : j ≤ j * j := by
    nlinarith
  have hjle : j ≤ t := hjleSq.trans hsq
  have hjdvd : j ∣ periodLcm t := dvd_periodLcm hj hjle
  refine ⟨hjdvd, ?_⟩
  intro p hp hpj
  have hple : p ≤ j := Nat.le_of_dvd hj hpj
  have hpjle : p * j ≤ t := by
    exact (Nat.mul_le_mul_right j hple).trans hsq
  have hpjdvd : p * j ∣ periodLcm t :=
    dvd_periodLcm (Nat.mul_pos hp.pos hj) hpjle
  exact (Nat.dvd_div_iff_mul_dvd hjdvd).2 (by
    simpa [Nat.mul_comm] using hpjdvd)

/-- The three fixed ray endpoints fit below the rough-density height range.
The twelve-bit saving for the actual LCM makes this a completely elementary
consequence, with ample room for the additive endpoint. -/
theorem three_mul_periodLcm_add_one_lt_two_pow
    {a : ℕ} (ha : 4 ≤ a) :
    3 * periodLcm (2 ^ a) + 1 < 2 ^ (2 * 2 ^ a) := by
  let t := 2 ^ a
  let H := periodLcm t
  have htSixteen : 16 ≤ t := by
    change 2 ^ 4 ≤ 2 ^ a
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) ha
  have hHpos : 0 < H := periodLcm_pos t
  have hH : H < 2 ^ (2 * t - 12) := by
    simpa [H, t] using periodLcm_pow_two_lt_two_pow_guardTwelve ha
  have hguardPos : 0 < 2 ^ (2 * t - 12) := pow_pos (by norm_num) _
  have hleft : 3 * H + 1 ≤ 4 * H := by omega
  have hscaled : 4 * H < 4 * 2 ^ (2 * t - 12) := by
    exact Nat.mul_lt_mul_of_pos_left hH (by norm_num)
  calc
    3 * periodLcm (2 ^ a) + 1 = 3 * H + 1 := by simp [H, t]
    _ ≤ 4 * H := hleft
    _ < 4 * 2 ^ (2 * t - 12) := hscaled
    _ = 2 ^ (2 * t - 10) := by
      rw [show 2 * t - 10 = (2 * t - 12) + 2 by omega, pow_add]
      norm_num
      ring
    _ ≤ 2 ^ (2 * t) := by
      exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    _ = 2 ^ (2 * 2 ^ a) := by simp [t]

/-- A clean LCM-ray cofactor has no prime at or below the LCM cutoff. -/
theorem clean_ray_cofactor_primeFactors_gt
    {t j q r : ℕ} (hj : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm t / j)
    (hr : Nat.Prime r) (hrdvd : r ∣ q * (periodLcm t / j) + 1) :
    t < r := by
  let H := periodLcm t
  let A := H / j
  have hH : j * A = H := by
    simpa [A, H] using Nat.mul_div_cancel' hj
  have hcop : Nat.Coprime j (q * A + 1) :=
    coprime_ray_cofactor (j := j) (a := A) q (by
      simpa [A, H] using hclean)
  by_contra hnot
  have hrt : r ≤ t := Nat.le_of_not_gt hnot
  have hrH : r ∣ H := by
    dsimp [H]
    exact dvd_periodLcm hr.pos hrt
  have hrJA : r ∣ j * A := by simpa [hH] using hrH
  rcases hr.dvd_mul.mp hrJA with hrj | hrA
  · have hrgcd : r ∣ Nat.gcd j (q * A + 1) :=
      Nat.dvd_gcd hrj (by simpa [A, H] using hrdvd)
    rw [hcop.gcd_eq_one] at hrgcd
    exact hr.not_dvd_one hrgcd
  · have hrqA : r ∣ q * A := dvd_mul_of_dvd_right hrA q
    have hrOne : r ∣ 1 := (Nat.dvd_add_right hrqA).mp (by
      simpa [A, H] using hrdvd)
    exact hr.not_dvd_one hrOne

/-- Uniform fixed-rank ray estimate.  On every clean offset `j² ≤ 2^a`
and every rank `q ≤ 3`, the exact endpoint totient differs from its affine
main term `φ(j)·(q·(H/j)+1)` by a relative amount below `2/a`.

This is the quantitative input needed to make every fixed-rank second
difference `o(H)`; unlike the earlier fixed `3/4` corridor, its error tends
to zero with the LCM scale. -/
theorem fixed_rank_clean_endpoint_totient_bounds
    {a j q : ℕ} (ha : 4 ≤ a) (hj : 0 < j)
    (hsq : j * j ≤ 2 ^ a) (hq : q ≤ 3) :
    let H := periodLcm (2 ^ a)
    let A := H / j
    (Nat.totient j : ℚ) * ((q * A + 1 : ℕ) : ℚ) *
        (1 - (2 : ℚ) / a) <
        Nat.totient (q * H + j) ∧
      (Nat.totient (q * H + j) : ℚ) ≤
        (Nat.totient j : ℚ) * ((q * A + 1 : ℕ) : ℚ) := by
  let t := 2 ^ a
  let H := periodLcm t
  let A := H / j
  let y := q * A + 1
  have hcleanPair := clean_periodLcm_divisor_of_sq_le hj (by
    simpa [t] using hsq)
  have hjdvd : j ∣ H := by simpa [H, t] using hcleanPair.1
  have hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ A := by
    simpa [A, H] using hcleanPair.2
  have hsplit : Nat.totient (q * H + j) =
      Nat.totient j * Nat.totient y := by
    simpa [H, t, A, y] using
      (totient_periodLcm_ray_split (t := t) (j := j) q
        (by simpa [H] using hjdvd) (by simpa [A, H] using hclean))
  have hyPos : 0 < y := by simp [y]
  have hrough : ∀ r : ℕ, Nat.Prime r → r ∣ y → t < r := by
    intro r hr hrdvd
    exact clean_ray_cofactor_primeFactors_gt
      (t := t) (j := j) (q := q) (r := r)
      (by simpa [H] using hjdvd) (by simpa [A, H] using hclean) hr
      (by simpa [y, A, H] using hrdvd)
  have hAle : A ≤ H := Nat.div_le_self H j
  have hqAle : q * A ≤ 3 * H := Nat.mul_le_mul hq hAle
  have hyHeight : y < 2 ^ (2 * t) := by
    calc
      y = q * A + 1 := rfl
      _ ≤ 3 * H + 1 := Nat.add_le_add_right hqAle 1
      _ < 2 ^ (2 * t) := by
        simpa [H, t] using three_mul_periodLcm_add_one_lt_two_pow ha
  have hdensity :
      (y : ℚ) * (1 - (2 : ℚ) / a) < Nat.totient y := by
    apply one_sub_two_div_lt_totient_density_of_rough (by omega) hyPos
    · simpa [t] using hrough
    · simpa [t] using hyHeight
  have hphiJ : (0 : ℚ) < (Nat.totient j : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr hj
  have hlower := mul_lt_mul_of_pos_left hdensity hphiJ
  have hupperNat : Nat.totient y ≤ y := Nat.totient_le y
  have hupperQ : (Nat.totient y : ℚ) ≤ y := by exact_mod_cast hupperNat
  dsimp only
  constructor
  · calc
      (Nat.totient j : ℚ) *
          ((q * (periodLcm (2 ^ a) / j) + 1 : ℕ) : ℚ) *
          (1 - (2 : ℚ) / a) =
          (Nat.totient j : ℚ) *
            ((y : ℚ) * (1 - (2 : ℚ) / a)) := by
              simp [y, A, H, t]
              ring
      _ < (Nat.totient j : ℚ) * Nat.totient y := hlower
      _ = Nat.totient (q * periodLcm (2 ^ a) + j) := by
        rw [hsplit]
        norm_num
  · calc
      (Nat.totient (q * periodLcm (2 ^ a) + j) : ℚ) =
          (Nat.totient j : ℚ) * Nat.totient y := by
            rw [hsplit]
            norm_num
      _ ≤ (Nat.totient j : ℚ) * (y : ℚ) :=
        mul_le_mul_of_nonneg_left hupperQ hphiJ.le
      _ = (Nat.totient j : ℚ) *
          ((q * (periodLcm (2 ^ a) / j) + 1 : ℕ) : ℚ) := by
            simp [y, A, H, t]

/-- The nonnegative loss from the affine fixed-rank main term. -/
def fixedRankEndpointDefect (a j q : ℕ) : ℚ :=
  let H := periodLcm (2 ^ a)
  (Nat.totient j : ℚ) * ((q * (H / j) + 1 : ℕ) : ℚ) -
    Nat.totient (q * H + j)

/-! ## The primitive three-rank kernel and its exact two-adic content -/

/-- The integral second difference across the first three positive LCM
ranks.  Its coefficient vector `(1,-2,1)` has `ℓ¹` height four. -/
def fixedRankSecondDifference (H j : ℕ) : ℤ :=
  (Nat.totient (3 * H + j) : ℤ) -
    2 * Nat.totient (2 * H + j) + Nat.totient (H + j)

/-- The exact ordering socket for the fixed-rank curvature: the rank-two
totient is strictly below both outer ranks or strictly above both of them.

This is the local conclusion supplied by any factor-separated ordering of
the three nonproportional linear forms.  The unresolved arithmetic step for
Erdős #249 is to force this socket on cofinally many prescribed LCM heights,
not merely on a positive-density set of unrestricted heights. -/
def MiddleRankTotientExtremal (H j : ℕ) : Prop :=
  (Nat.totient (2 * H + j) < Nat.totient (H + j) ∧
      Nat.totient (2 * H + j) < Nat.totient (3 * H + j)) ∨
    (Nat.totient (H + j) < Nat.totient (2 * H + j) ∧
      Nat.totient (3 * H + j) < Nat.totient (2 * H + j))

/-- If the middle-rank totient is the strict minimum, the primitive
three-rank curvature is positive. -/
theorem fixedRankSecondDifference_pos_of_middle_strict_min
    {H j : ℕ}
    (hleft : Nat.totient (2 * H + j) < Nat.totient (H + j))
    (hright : Nat.totient (2 * H + j) < Nat.totient (3 * H + j)) :
    0 < fixedRankSecondDifference H j := by
  have hleftZ :
      (Nat.totient (2 * H + j) : ℤ) < Nat.totient (H + j) := by
    exact_mod_cast hleft
  have hrightZ :
      (Nat.totient (2 * H + j) : ℤ) < Nat.totient (3 * H + j) := by
    exact_mod_cast hright
  unfold fixedRankSecondDifference
  omega

/-- If the middle-rank totient is the strict maximum, the primitive
three-rank curvature is negative. -/
theorem fixedRankSecondDifference_neg_of_middle_strict_max
    {H j : ℕ}
    (hleft : Nat.totient (H + j) < Nat.totient (2 * H + j))
    (hright : Nat.totient (3 * H + j) < Nat.totient (2 * H + j)) :
    fixedRankSecondDifference H j < 0 := by
  have hleftZ :
      (Nat.totient (H + j) : ℤ) < Nat.totient (2 * H + j) := by
    exact_mod_cast hleft
  have hrightZ :
      (Nat.totient (3 * H + j) : ℤ) < Nat.totient (2 * H + j) := by
    exact_mod_cast hright
  unfold fixedRankSecondDifference
  omega

/-- A middle-extremal ordering is already enough to separate the normalized
fixed-rank curvature from zero; no quantitative gap is required. -/
theorem fixedRankSecondDifference_ne_zero_of_middleRankTotientExtremal
    {H j : ℕ} (h : MiddleRankTotientExtremal H j) :
    fixedRankSecondDifference H j ≠ 0 := by
  rcases h with hmin | hmax
  · exact ne_of_gt
      (fixedRankSecondDifference_pos_of_middle_strict_min hmin.1 hmin.2)
  · exact ne_of_lt
      (fixedRankSecondDifference_neg_of_middle_strict_max hmax.1 hmax.2)

/-- The specified sparse-orbit input suggested by simultaneous totient
ordering results: a fixed offset whose rank-two value is extremal at
arbitrarily large power-of-two LCM heights. -/
def PowerTwoLcmMiddleRankExtremalSupply (j : ℕ) : Prop :=
  ∀ A : ℕ, ∃ a : ℕ, A ≤ a ∧
    MiddleRankTotientExtremal (periodLcm (2 ^ a)) j

/-- The exact Lean consumer of the sparse-orbit ordering wish.  Once the
middle-extremal ordering is transferred to cofinally many LCM heights, the
primitive fixed-rank curvature is nonzero at those same heights. -/
theorem cofinal_fixedRankSecondDifference_ne_zero_of_middleRankExtremalSupply
    {j : ℕ} (h : PowerTwoLcmMiddleRankExtremalSupply j) :
    ∀ A : ℕ, ∃ a : ℕ, A ≤ a ∧
      fixedRankSecondDifference (periodLcm (2 ^ a)) j ≠ 0 := by
  intro A
  obtain ⟨a, ha, hextremal⟩ := h A
  exact ⟨a, ha,
    fixedRankSecondDifference_ne_zero_of_middleRankTotientExtremal hextremal⟩

/-- The primitive three-coordinate kernel annihilating both the constant and
linear rank moments is unique.  The pivot minor on the first two columns is
`1`, hence odd; no hidden lattice index enlarges the primitive kernel. -/
theorem affine_rank_three_kernel_classification
    {c₁ c₂ c₃ : ℤ} (hzero : c₁ + c₂ + c₃ = 0)
    (hlinear : c₁ + 2 * c₂ + 3 * c₃ = 0) :
    c₁ = c₃ ∧ c₂ = -2 * c₃ ∧
      |c₁| + |c₂| + |c₃| = 4 * |c₃| := by
  have hc₁ : c₁ = c₃ := by linarith
  have hc₂ : c₂ = -2 * c₃ := by linarith
  refine ⟨hc₁, hc₂, ?_⟩
  rw [hc₁, hc₂, abs_mul]
  norm_num
  ring

/-- The chosen affine-moment pivot minor is an odd unit. -/
theorem affine_rank_three_pivotMinor_odd :
    Odd ((1 : ℤ) * 2 - 1 * 1) := by norm_num

/-- Exact dyadic scaling of the primitive rank curvature when the reduced
height and offset are even. -/
theorem fixedRankSecondDifference_two_mul_even
    {H j : ℕ} (hH : Even H) (hj : Even j) :
    fixedRankSecondDifference (2 * H) (2 * j) =
      2 * fixedRankSecondDifference H j := by
  have h₁ : Even (H + j) := hH.add hj
  have h₂ : Even (2 * H + j) := (even_two_mul H).add hj
  have h₃ : Even (3 * H + j) := (hH.mul_left 3).add hj
  unfold fixedRankSecondDifference
  rw [show 3 * (2 * H) + 2 * j = 2 * (3 * H + j) by ring,
    show 2 * (2 * H) + 2 * j = 2 * (2 * H + j) by ring,
    show 2 * H + 2 * j = 2 * (H + j) by ring,
    Nat.totient_two_mul_of_even h₃,
    Nat.totient_two_mul_of_even h₂,
    Nat.totient_two_mul_of_even h₁]
  push_cast
  ring

/-- Exact dyadic scaling of the primitive rank curvature at an odd reduced
offset: the final factor of two does not enlarge the curvature. -/
theorem fixedRankSecondDifference_two_mul_odd
    {H j : ℕ} (hH : Even H) (hj : Odd j) :
    fixedRankSecondDifference (2 * H) (2 * j) =
      fixedRankSecondDifference H j := by
  have h₁ : Odd (H + j) := hH.add_odd hj
  have h₂ : Odd (2 * H + j) := (even_two_mul H).add_odd hj
  have h₃ : Odd (3 * H + j) := (hH.mul_left 3).add_odd hj
  unfold fixedRankSecondDifference
  rw [show 3 * (2 * H) + 2 * j = 2 * (3 * H + j) by ring,
    show 2 * (2 * H) + 2 * j = 2 * (2 * H + j) by ring,
    show 2 * H + 2 * j = 2 * (H + j) by ring,
    Nat.totient_two_mul_of_odd h₃,
    Nat.totient_two_mul_of_odd h₂,
    Nat.totient_two_mul_of_odd h₁]

/-- Iterating the parity split gives the exact valuation contribution of a
dyadically scaled odd offset. -/
theorem fixedRankSecondDifference_two_pow_succ_mul
    (H j n : ℕ) (hH : Even H) (hj : Odd j) :
    fixedRankSecondDifference (2 ^ (n + 1) * H) (2 ^ (n + 1) * j) =
      (2 : ℤ) ^ n * fixedRankSecondDifference H j := by
  induction n with
  | zero =>
      simpa using fixedRankSecondDifference_two_mul_odd hH hj
  | succ n ih =>
      have hHn : Even (2 ^ (n + 1) * H) := by
        rw [show 2 ^ (n + 1) * H = 2 * (2 ^ n * H) by
          rw [pow_succ]
          ring]
        exact even_two_mul _
      have hjn : Even (2 ^ (n + 1) * j) := by
        rw [show 2 ^ (n + 1) * j = 2 * (2 ^ n * j) by
          rw [pow_succ]
          ring]
        exact even_two_mul _
      have hstep := fixedRankSecondDifference_two_mul_even hHn hjn
      have hpowH : 2 ^ (n + 2) * H = 2 * (2 ^ (n + 1) * H) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        ring
      have hpowJ : 2 ^ (n + 2) * j = 2 * (2 ^ (n + 1) * j) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        ring
      calc
        fixedRankSecondDifference (2 ^ (n + 2) * H) (2 ^ (n + 2) * j) =
            fixedRankSecondDifference
              (2 * (2 ^ (n + 1) * H)) (2 * (2 ^ (n + 1) * j)) := by
                rw [hpowH, hpowJ]
        _ = 2 * fixedRankSecondDifference
              (2 ^ (n + 1) * H) (2 ^ (n + 1) * j) := hstep
        _ = 2 * ((2 : ℤ) ^ n * fixedRankSecondDifference H j) := by rw [ih]
        _ = (2 : ℤ) ^ (n + 1) * fixedRankSecondDifference H j := by
          rw [pow_succ]
          ring

/-- Every positive-offset curvature above height two is even. -/
theorem fixedRankSecondDifference_even
    {H j : ℕ} (hH : 2 ≤ H) (hj : 1 ≤ j) :
    Even (fixedRankSecondDifference H j) := by
  have h₁ : 2 < H + j := by omega
  have h₂ : 2 < 2 * H + j := by omega
  have h₃ : 2 < 3 * H + j := by omega
  obtain ⟨u₁, hu₁⟩ := Nat.totient_even h₁
  obtain ⟨u₂, hu₂⟩ := Nat.totient_even h₂
  obtain ⟨u₃, hu₃⟩ := Nat.totient_even h₃
  refine ⟨(u₃ : ℤ) - 2 * (u₂ : ℤ) + (u₁ : ℤ), ?_⟩
  unfold fixedRankSecondDifference
  rw [hu₁, hu₂, hu₃]
  push_cast
  ring

/-- The primitive rank kernel acquires exactly the expected growing dyadic
divisor on scaled odd offsets. -/
theorem two_pow_succ_dvd_fixedRankSecondDifference
    (H j n : ℕ) (hH : Even H) (hHtwo : 2 ≤ H) (hj : Odd j) :
    (2 : ℤ) ^ (n + 1) ∣
      fixedRankSecondDifference (2 ^ (n + 1) * H) (2 ^ (n + 1) * j) := by
  have hjOne : 1 ≤ j := by
    have := Odd.pos hj
    omega
  obtain ⟨z, hz⟩ := fixedRankSecondDifference_even hHtwo hjOne
  refine ⟨z, ?_⟩
  rw [fixedRankSecondDifference_two_pow_succ_mul H j n hH hj, hz, pow_succ]
  ring

/-- Sharpness of the two-adic theorem: the normalized one-by-one minor is
odd at every depth.  Thus the bounded-height primitive kernel alone cannot
force even one additional factor of two. -/
theorem fixedRankSecondDifference_dyadic_fixture_exact (n : ℕ) :
    fixedRankSecondDifference (2 ^ (n + 1) * 2) (2 ^ (n + 1) * 3) =
      -(2 : ℤ) ^ (n + 1) := by
  rw [fixedRankSecondDifference_two_pow_succ_mul 2 3 n (by norm_num) (by norm_num)]
  have hbase : fixedRankSecondDifference 2 3 = -2 := by decide
  rw [hbase, pow_succ]
  ring

/-- The fixed-rank endpoint defect is nonnegative and has relative size
strictly below `2/a`. -/
theorem fixedRankEndpointDefect_nonneg_and_lt
    {a j q : ℕ} (ha : 4 ≤ a) (hj : 0 < j)
    (hsq : j * j ≤ 2 ^ a) (hq : q ≤ 3) :
    0 ≤ fixedRankEndpointDefect a j q ∧
      fixedRankEndpointDefect a j q <
        (Nat.totient j : ℚ) *
          ((q * (periodLcm (2 ^ a) / j) + 1 : ℕ) : ℚ) *
          (2 / (a : ℚ)) := by
  obtain ⟨hlower, hupper⟩ :=
    fixed_rank_clean_endpoint_totient_bounds ha hj hsq hq
  let M : ℚ :=
    (Nat.totient j : ℚ) *
      ((q * (periodLcm (2 ^ a) / j) + 1 : ℕ) : ℚ)
  have hdef : fixedRankEndpointDefect a j q =
      M - Nat.totient (q * periodLcm (2 ^ a) + j) := by
    rfl
  have hlower' : M * (1 - (2 : ℚ) / a) <
      Nat.totient (q * periodLcm (2 ^ a) + j) := by
    simpa [M] using hlower
  have hupper' : (Nat.totient (q * periodLcm (2 ^ a) + j) : ℚ) ≤ M := by
    simpa [M] using hupper
  rw [hdef]
  constructor
  · exact sub_nonneg.mpr hupper'
  · nlinarith only [hlower']

/-- Exact clean-ray factorisation of the primitive rank curvature. -/
theorem fixedRankSecondDifference_periodLcm_eq_mul
    {t j : ℕ} (hjdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm t / j) :
    fixedRankSecondDifference (periodLcm t) j =
      (Nat.totient j : ℤ) *
        ((Nat.totient (3 * (periodLcm t / j) + 1) : ℤ) -
          2 * Nat.totient (2 * (periodLcm t / j) + 1) +
          Nat.totient (periodLcm t / j + 1)) := by
  have h₁ := totient_periodLcm_ray_split (t := t) (j := j) 1 hjdvd hclean
  have h₂ := totient_periodLcm_ray_split (t := t) (j := j) 2 hjdvd hclean
  have h₃ := totient_periodLcm_ray_split (t := t) (j := j) 3 hjdvd hclean
  unfold fixedRankSecondDifference
  norm_num only [one_mul] at h₁
  rw [h₁, h₂, h₃]
  push_cast
  ring

/-- On the square-root clean window the primitive curvature is divisible by
`2·φ(j)`.  The factor `φ(j)` is the exact local ray factor; the extra `2`
comes from parity of the three odd rough cofactors. -/
theorem two_mul_totient_dvd_fixedRankSecondDifference
    {a j : ℕ} (ha : 4 ≤ a) (hj : 0 < j)
    (hsq : j * j ≤ 2 ^ a) :
    (2 * (Nat.totient j : ℤ)) ∣
      fixedRankSecondDifference (periodLcm (2 ^ a)) j := by
  let t := 2 ^ a
  let H := periodLcm t
  let A := H / j
  have hcleanPair := clean_periodLcm_divisor_of_sq_le hj (by
    simpa [t] using hsq)
  have hjdvd : j ∣ H := by simpa [H, t] using hcleanPair.1
  have hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ A := by
    simpa [A, H] using hcleanPair.2
  have htwoJLe : 2 * j ≤ t := by
    by_cases hjOne : j = 1
    · subst j
      have : 16 ≤ t := by
        change 2 ^ 4 ≤ 2 ^ a
        exact Nat.pow_le_pow_right (by norm_num : 0 < 2) ha
      omega
    · have hjTwo : 2 ≤ j := by omega
      exact (Nat.mul_le_mul_right j hjTwo).trans (by simpa [t] using hsq)
  have htwoJdvd : 2 * j ∣ H := by
    dsimp [H]
    exact dvd_periodLcm (Nat.mul_pos (by norm_num) hj) htwoJLe
  have hAle : 2 ≤ A := by
    apply (Nat.le_div_iff_mul_le hj).2
    exact Nat.le_of_dvd (periodLcm_pos t) (by simpa [H] using htwoJdvd)
  have h₁gt : 2 < A + 1 := by omega
  have h₂gt : 2 < 2 * A + 1 := by omega
  have h₃gt : 2 < 3 * A + 1 := by omega
  obtain ⟨u₁, hu₁⟩ := Nat.totient_even h₁gt
  obtain ⟨u₂, hu₂⟩ := Nat.totient_even h₂gt
  obtain ⟨u₃, hu₃⟩ := Nat.totient_even h₃gt
  refine ⟨(u₃ : ℤ) - 2 * (u₂ : ℤ) + (u₁ : ℤ), ?_⟩
  rw [fixedRankSecondDifference_periodLcm_eq_mul
    (t := t) (j := j) (by simpa [H] using hjdvd) (by simpa [A, H] using hclean)]
  rw [hu₁, hu₂, hu₃]
  push_cast
  ring

/-- **Fixed-offset second-rank cancellation.**  On every clean offset in the
square-root window, the three endpoint ranks have an affine main term, so its
second difference vanishes.  What remains is bounded by the sum of three
nonnegative rough-Euler defects, hence is `O(H/a)` with an explicit constant.

This is a rigorous nonlinear normalization unavailable to any fixed-density
estimate: the right-hand side is `o(H)` for every fixed offset `j`. -/
theorem fixed_rank_secondDifference_abs_lt
    {a j : ℕ} (ha : 4 ≤ a) (hj : 0 < j)
    (hsq : j * j ≤ 2 ^ a) :
    let H := periodLcm (2 ^ a)
    |(Nat.totient (3 * H + j) : ℚ) -
        2 * Nat.totient (2 * H + j) + Nat.totient (H + j)| <
      (Nat.totient j : ℚ) * (((8 * (H / j) + 4 : ℕ) : ℚ)) *
        (2 / (a : ℚ)) := by
  let H := periodLcm (2 ^ a)
  let A := H / j
  let d₁ := fixedRankEndpointDefect a j 1
  let d₂ := fixedRankEndpointDefect a j 2
  let d₃ := fixedRankEndpointDefect a j 3
  obtain ⟨hd₁Nonneg, hd₁Lt⟩ :=
    fixedRankEndpointDefect_nonneg_and_lt ha hj hsq (by omega : 1 ≤ 3)
  obtain ⟨hd₂Nonneg, hd₂Lt⟩ :=
    fixedRankEndpointDefect_nonneg_and_lt ha hj hsq (by omega : 2 ≤ 3)
  obtain ⟨hd₃Nonneg, hd₃Lt⟩ :=
    fixedRankEndpointDefect_nonneg_and_lt ha hj hsq (by omega : 3 ≤ 3)
  have hsecond :
      (Nat.totient (3 * H + j) : ℚ) -
          2 * Nat.totient (2 * H + j) + Nat.totient (H + j) =
        -d₃ + 2 * d₂ - d₁ := by
    dsimp [d₁, d₂, d₃, fixedRankEndpointDefect, H, A]
    push_cast
    ring
  have habs : |(-d₃ + 2 * d₂ - d₁)| ≤ d₃ + 2 * d₂ + d₁ := by
    rw [abs_le]
    constructor <;> nlinarith only [hd₁Nonneg, hd₂Nonneg, hd₃Nonneg]
  have hsum : d₃ + 2 * d₂ + d₁ <
      (Nat.totient j : ℚ) * (((8 * A + 4 : ℕ) : ℚ)) *
        (2 / (a : ℚ)) := by
    have hd₁Lt' : d₁ <
        (Nat.totient j : ℚ) * (((1 * A + 1 : ℕ) : ℚ)) *
          (2 / (a : ℚ)) := by
      simpa [d₁, A, H] using hd₁Lt
    have hd₂Lt' : d₂ <
        (Nat.totient j : ℚ) * (((2 * A + 1 : ℕ) : ℚ)) *
          (2 / (a : ℚ)) := by
      simpa [d₂, A, H] using hd₂Lt
    have hd₃Lt' : d₃ <
        (Nat.totient j : ℚ) * (((3 * A + 1 : ℕ) : ℚ)) *
          (2 / (a : ℚ)) := by
      simpa [d₃, A, H] using hd₃Lt
    calc
      d₃ + 2 * d₂ + d₁ <
          (Nat.totient j : ℚ) * (((3 * A + 1 : ℕ) : ℚ)) *
              (2 / (a : ℚ)) +
            2 * ((Nat.totient j : ℚ) * (((2 * A + 1 : ℕ) : ℚ)) *
              (2 / (a : ℚ))) +
            (Nat.totient j : ℚ) * (((1 * A + 1 : ℕ) : ℚ)) *
              (2 / (a : ℚ)) := by
              nlinarith only [hd₁Lt', hd₂Lt', hd₃Lt']
      _ = (Nat.totient j : ℚ) * (((8 * A + 4 : ℕ) : ℚ)) *
          (2 / (a : ℚ)) := by
        push_cast
        ring
  dsimp only
  rw [show periodLcm (2 ^ a) = H by rfl]
  rw [hsecond]
  exact habs.trans_lt (by simpa [A] using hsum)

/-- **Primitive localized curvature.**  After removing the exact local
factor `2·φ(j)`, the three-rank curvature is an integer whose Archimedean
height is strictly below `(8·H/j+4)/a`.

The final disjunction is the exact second-order anti-concentration boundary:
the normalized curvature either vanishes, or its absolute value is at least
one.  Thus any future argument only has to separate this primitive integer
from zero; no coefficient gcd or hidden lattice index remains. -/
theorem exists_primitive_fixedRankCurvature_with_bound
    {a j : ℕ} (ha : 4 ≤ a) (hj : 0 < j)
    (hsq : j * j ≤ 2 ^ a) :
    ∃ z : ℤ,
      fixedRankSecondDifference (periodLcm (2 ^ a)) j =
          (2 * (Nat.totient j : ℤ)) * z ∧
        |(z : ℚ)| <
          ((8 * (periodLcm (2 ^ a) / j) + 4 : ℕ) : ℚ) / a ∧
        (z = 0 ∨ 1 ≤ |z|) := by
  obtain ⟨z, hz⟩ :=
    two_mul_totient_dvd_fixedRankSecondDifference ha hj hsq
  have hbound := fixed_rank_secondDifference_abs_lt ha hj hsq
  have hphiPos : (0 : ℚ) < (Nat.totient j : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr hj
  have hzQ :
      (fixedRankSecondDifference (periodLcm (2 ^ a)) j : ℚ) =
        (2 * (Nat.totient j : ℚ)) * (z : ℚ) := by
    exact_mod_cast hz
  have hcurvQ :
      (fixedRankSecondDifference (periodLcm (2 ^ a)) j : ℚ) =
        (Nat.totient (3 * periodLcm (2 ^ a) + j) : ℚ) -
          2 * Nat.totient (2 * periodLcm (2 ^ a) + j) +
          Nat.totient (periodLcm (2 ^ a) + j) := by
    unfold fixedRankSecondDifference
    push_cast
    ring
  have hscaled :
      (2 * (Nat.totient j : ℚ)) * |(z : ℚ)| <
        (2 * (Nat.totient j : ℚ)) *
          (((8 * (periodLcm (2 ^ a) / j) + 4 : ℕ) : ℚ) / a) := by
    calc
      (2 * (Nat.totient j : ℚ)) * |(z : ℚ)| =
          |(2 * (Nat.totient j : ℚ)) * (z : ℚ)| := by
            rw [abs_mul, abs_of_pos (by positivity :
              (0 : ℚ) < 2 * (Nat.totient j : ℚ))]
      _ = |(fixedRankSecondDifference (periodLcm (2 ^ a)) j : ℚ)| := by
        rw [hzQ]
      _ = |(Nat.totient (3 * periodLcm (2 ^ a) + j) : ℚ) -
          2 * Nat.totient (2 * periodLcm (2 ^ a) + j) +
          Nat.totient (periodLcm (2 ^ a) + j)| := by rw [hcurvQ]
      _ < (Nat.totient j : ℚ) *
          (((8 * (periodLcm (2 ^ a) / j) + 4 : ℕ) : ℚ)) *
          (2 / (a : ℚ)) := by simpa using hbound
      _ = (2 * (Nat.totient j : ℚ)) *
          (((8 * (periodLcm (2 ^ a) / j) + 4 : ℕ) : ℚ) / a) := by ring
  refine ⟨z, hz, ?_, ?_⟩
  · nlinarith only [hscaled, hphiPos]
  · by_cases hzZero : z = 0
    · exact Or.inl hzZero
    · exact Or.inr (Int.one_le_abs hzZero)

#print axioms one_sub_two_div_lt_totient_density_of_rough
#print axioms affine_rank_three_kernel_classification
#print axioms fixedRankSecondDifference_dyadic_fixture_exact
#print axioms fixed_rank_secondDifference_abs_lt
#print axioms exists_primitive_fixedRankCurvature_with_bound

end TotientFixedRankLcmAsymptotic
end Erdos249257
