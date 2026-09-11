import Erdos249257.FullTargetPrimeAdjunctionNoGo
import Erdos249257.MersenneLambertLadder
import Mathlib.Tactic

/-!
# Squared-Mersenne enclosures for the actual #249 diagonal

This bridge spends the exactly summable first-order Lambert component before
estimating a complement. Its finite centre therefore has only the
squared-Mersenne tail left, works at every cutoff, and feeds the generic
full-target enclosure consumer directly.
-/

namespace Erdos249257.SquaredMersenneDiagonalEnclosure

open scoped ArithmeticFunction.Moebius BigOperators
open FullTargetPrimeAdjunctionNoGo
open TotientTailPeriodKiller

/-- Executable rational partial state
`1/2 + ∑_{1 ≤ d ≤ D} μ(d)/(2^d-1)^2`. -/
def mobiusSquarePartialRat (D : ℕ) : ℚ :=
  1 / 2 + ∑ k ∈ Finset.range D,
    (ArithmeticFunction.moebius (k + 1) : ℚ) /
      (((2 : ℚ) ^ (k + 1) - 1) ^ 2)

/-- Rational centre for the actual diagonal. -/
def lambertProjectedDiagonalRat (H D : ℕ) : ℚ :=
  (diagonalPrefixCorrection H : ℚ) +
    (diagonalCoefficient H : ℚ) * mobiusSquarePartialRat D

/-- Exact reduced-denominator formula for an integral affine image of a
rational.  Adding the integral offset does not change the denominator, while
multiplication cancels exactly the gcd with the scaling integer. -/
theorem rat_den_int_add_mul (z c : ℤ) (x : ℚ) :
    ((z : ℚ) + (c : ℚ) * x).den =
      x.den / Nat.gcd x.den c.natAbs := by
  rw [Rat.intCast_add_den, Rat.mul_den]
  simp only [Rat.den_intCast, one_mul, Rat.num_intCast, Int.natAbs_mul]
  rw [Nat.gcd_comm x.den c.natAbs]
  congr 1
  simpa [Nat.mul_comm] using
    (Nat.Coprime.gcd_mul_left_cancel c.natAbs x.reduced)

/-- Specialisation of `rat_den_int_add_mul` to the canonical direct centre. -/
theorem lambertProjectedDiagonalRat_den (H D : ℕ) :
    (lambertProjectedDiagonalRat H D).den =
      (mobiusSquarePartialRat D).den /
        Nat.gcd (mobiusSquarePartialRat D).den (diagonalCoefficient H) := by
  unfold lambertProjectedDiagonalRat
  simpa using rat_den_int_add_mul
    (diagonalPrefixCorrection H) (diagonalCoefficient H) (mobiusSquarePartialRat D)

/-- Real display of the exact rational centre. -/
noncomputable def lambertProjectedDiagonal (H D : ℕ) : ℝ :=
  (lambertProjectedDiagonalRat H D : ℝ)

/-- The omitted signed squared-Mersenne tail, indexed from `D+1`. -/
noncomputable def mobiusSquareTail (D : ℕ) : ℝ :=
  ∑' k : ℕ,
    ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
      (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)

/-- Sharp elementary radius obtained by comparing every later Mersenne
denominator with `2^k (2^(D+1)-1)`. -/
noncomputable def lambertSquareComplementBound (H D : ℕ) : ℝ :=
  4 * (diagonalCoefficient H : ℝ) /
    (3 * (((2 : ℝ) ^ (D + 1) - 1) ^ 2))

/-- The local `ℕ` series convention agrees with the ladder's positive-index
convention. -/
theorem totientSeries_eq_pnat_half_pow :
    totientSeries =
      ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) *
        ((1 : ℝ) / 2) ^ (n : ℕ) := by
  have hsum := summable_totient_div_two_pow
  unfold totientSeries
  calc
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
        ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) / 2 ^ (n + 1) := by
      rw [hsum.tsum_eq_zero_add]
      simp
    _ = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) / 2 ^ (n : ℕ) := by
      exact (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => (Nat.totient n : ℝ) / 2 ^ n)).symm
    _ = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) *
        ((1 : ℝ) / 2) ^ (n : ℕ) := by
      apply tsum_congr
      intro n
      rw [div_pow, one_pow, mul_one_div]

/-- The full Möbius-square series splits into the exact rational prefix and
the shifted tail. -/
theorem mobius_square_series_eq_partial_add_tail (D : ℕ) :
    1 / 2 + ∑' d : ℕ+,
        ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
          (((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) =
      (mobiusSquarePartialRat D : ℝ) + mobiusSquareTail D := by
  let f : ℕ → ℝ := fun n =>
    ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) /
      (((2 : ℝ) ^ (n + 1) - 1) ^ 2)
  have hsum : Summable f := by
    dsimp [f]
    rw [← summable_pnat_iff_summable_succ
      (f := fun n : ℕ =>
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) /
          (((2 : ℝ) ^ n - 1) ^ 2))]
    exact MersenneLambertLadder.summable_moebius_div_mersenne_sq
  have hsplit := hsum.sum_add_tsum_nat_add D
  have hpnat :
      (∑' d : ℕ+,
        ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
          (((2 : ℝ) ^ (d : ℕ) - 1) ^ 2)) = ∑' n : ℕ, f n := by
    simpa [f] using
      (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ =>
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) /
            (((2 : ℝ) ^ n - 1) ^ 2)))
  have hpartial : (mobiusSquarePartialRat D : ℝ) =
      1 / 2 + ∑ n ∈ Finset.range D, f n := by
    unfold mobiusSquarePartialRat
    push_cast
    congr 1
  have htail : mobiusSquareTail D = ∑' n : ℕ, f (n + D) := by
    unfold mobiusSquareTail
    apply tsum_congr
    intro k
    change
      ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
          (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2) =
        ((ArithmeticFunction.moebius ((k + D) + 1) : ℤ) : ℝ) /
          (((2 : ℝ) ^ ((k + D) + 1) - 1) ^ 2)
    rw [show D + 1 + k = (k + D) + 1 by omega]
  rw [hpnat, ← hsplit, hpartial, htail]
  ring

/-- Exact direct projection: no residue split and no `2H ≤ D` condition. -/
theorem scaleDiagonalTailDifference_sub_lambertProjectedDiagonal
    (H D : ℕ) :
    scaleDiagonalTailDifference H - lambertProjectedDiagonal H D =
      (diagonalCoefficient H : ℝ) * mobiusSquareTail D := by
  rw [scaleDiagonalTailDifference_eq, totientSeries_eq_pnat_half_pow,
    MersenneLambertLadder.tsum_totient_half_pow_eq_half_add_moebius_sq,
    mobius_square_series_eq_partial_add_tail]
  unfold lambertProjectedDiagonal lambertProjectedDiagonalRat
  push_cast
  ring

/-- Later Mersenne denominators grow at least geometrically from the first
omitted denominator. -/
theorem mersenne_shift_lower_bound (D k : ℕ) :
    (2 : ℝ) ^ k * ((2 : ℝ) ^ (D + 1) - 1) ≤
      (2 : ℝ) ^ (D + 1 + k) - 1 := by
  have hpow : (2 : ℝ) ^ (D + 1 + k) =
      (2 : ℝ) ^ (D + 1) * (2 : ℝ) ^ k := by
    rw [← pow_add]
  rw [hpow]
  have hk : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  calc
    (2 : ℝ) ^ k * ((2 : ℝ) ^ (D + 1) - 1) =
        (2 : ℝ) ^ (D + 1) * (2 : ℝ) ^ k - (2 : ℝ) ^ k := by ring
    _ ≤ (2 : ℝ) ^ (D + 1) * (2 : ℝ) ^ k - 1 :=
      sub_le_sub_left hk _

/-- The signed square tail is bounded by the exact first-denominator
geometric majorant. -/
theorem abs_mobiusSquareTail_le (D : ℕ) :
    |mobiusSquareTail D| ≤
      4 / (3 * (((2 : ℝ) ^ (D + 1) - 1) ^ 2)) := by
  let term : ℕ → ℝ := fun k =>
    ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
      (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)
  let majorant : ℕ → ℝ := fun k =>
    (1 / (((2 : ℝ) ^ (D + 1) - 1) ^ 2)) * (1 / 4 : ℝ) ^ k
  have hbase : (0 : ℝ) < (2 : ℝ) ^ (D + 1) - 1 := by
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
  have hterm : ∀ k : ℕ, |term k| ≤ majorant k := by
    intro k
    have hden : (0 : ℝ) < (2 : ℝ) ^ (D + 1 + k) - 1 := by
      exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
    have hkpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hprod : (0 : ℝ) <
        (2 : ℝ) ^ k * ((2 : ℝ) ^ (D + 1) - 1) :=
      mul_pos hkpow hbase
    have hsquare :
        ((2 : ℝ) ^ k * ((2 : ℝ) ^ (D + 1) - 1)) ^ 2 ≤
          ((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2 :=
      (sq_le_sq₀ hprod.le hden.le).2 (mersenne_shift_lower_bound D k)
    have hmu :
        |((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast MersenneLambertLadder.abs_moebius_le_one (D + 1 + k)
    calc
      |term k| =
          |((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ)| /
            (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2) := by
        change
          |((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
              (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)| = _
        rw [abs_div, abs_of_pos (sq_pos_of_pos hden)]
      _ ≤ 1 / (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2) := by
        gcongr
      _ ≤ 1 /
          (((2 : ℝ) ^ k * ((2 : ℝ) ^ (D + 1) - 1)) ^ 2) := by
        exact one_div_le_one_div_of_le (sq_pos_of_pos hprod) hsquare
      _ = majorant k := by
        unfold majorant
        rw [mul_pow, div_pow, one_pow]
        field_simp
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_two]
  have hmajorant : Summable majorant := by
    unfold majorant
    exact ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
      (1 / (((2 : ℝ) ^ (D + 1) - 1) ^ 2)))
  have habs : Summable (fun k => |term k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hterm hmajorant
  have hsigned : Summable term := summable_abs_iff.mp habs
  have htail : mobiusSquareTail D = ∑' k : ℕ, term k := by
    unfold mobiusSquareTail
    rfl
  rw [htail]
  have hle1 : (∑' k : ℕ, term k) ≤ ∑' k : ℕ, |term k| :=
    Summable.tsum_le_tsum (fun k => le_abs_self _) hsigned habs
  have hle2 : -(∑' k : ℕ, term k) ≤ ∑' k : ℕ, |term k| := by
    rw [← tsum_neg]
    exact Summable.tsum_le_tsum (fun k => neg_le_abs _) hsigned.neg habs
  have htri : |∑' k : ℕ, term k| ≤ ∑' k : ℕ, |term k| :=
    abs_le.mpr ⟨by linarith, hle1⟩
  calc
    |∑' k : ℕ, term k| ≤ ∑' k : ℕ, |term k| := htri
    _ ≤ ∑' k : ℕ, majorant k := habs.tsum_le_tsum hterm hmajorant
    _ = 4 / (3 * (((2 : ℝ) ^ (D + 1) - 1) ^ 2)) := by
      unfold majorant
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
      field_simp
      norm_num

/-! ## Directed first-support enclosure -/

/-- If `n` is the first nonzero Möbius channel after `D`, the tail splits into
that channel and the tail after `n`.  This is the exact algebraic input for a
one-sided enclosure; no minimisation operator is needed. -/
theorem mobiusSquareTail_eq_first_support_add_tail
    {D n : ℕ} (hDn : D < n)
    (hzero : ∀ d : ℕ, D < d → d < n → ArithmeticFunction.moebius d = 0) :
    mobiusSquareTail D =
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) /
          (((2 : ℝ) ^ n - 1) ^ 2) +
        mobiusSquareTail n := by
  have hdiff : 0 < n - D := Nat.sub_pos_iff_lt.mpr hDn
  have hsum : D + (n - D) = n := Nat.add_sub_of_le (Nat.le_of_lt hDn)
  have hone : 1 ≤ n - D := hdiff
  have hlast : D + 1 + (n - D - 1) = n := by
    calc
      D + 1 + (n - D - 1) = D + ((n - D - 1) + 1) := by ac_rfl
      _ = D + (n - D) := by rw [Nat.sub_add_cancel hone]
      _ = n := hsum
  let f : ℕ → ℝ := fun k =>
    ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
      (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)
  let base : ℕ → ℝ := fun k =>
    ((ArithmeticFunction.moebius (k + 1) : ℤ) : ℝ) /
      (((2 : ℝ) ^ (k + 1) - 1) ^ 2)
  have hbase : Summable base := by
    dsimp [base]
    rw [← summable_pnat_iff_summable_succ
      (f := fun d : ℕ =>
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
          (((2 : ℝ) ^ d - 1) ^ 2))]
    exact MersenneLambertLadder.summable_moebius_div_mersenne_sq
  have hf : Summable f := by
    have hshift := (summable_nat_add_iff D).mpr hbase
    simpa [f, base, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hsplit := hf.sum_add_tsum_nat_add (n - D)
  have hfinite : ∑ k ∈ Finset.range (n - D), f k =
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) /
        (((2 : ℝ) ^ n - 1) ^ 2) := by
    rw [show n - D = (n - D - 1) + 1 by omega, Finset.sum_range_succ]
    have hprefix : ∑ k ∈ Finset.range (n - D - 1), f k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hklt : k < n - D - 1 := Finset.mem_range.mp hk
      have hidx : D < D + 1 + k := by omega
      have hidxn : D + 1 + k < n := by omega
      simp [f, hzero (D + 1 + k) hidx hidxn]
    rw [hprefix, zero_add]
    simp only [f]
    rw [hlast]
  have htail : ∑' k : ℕ, f (k + (n - D)) = mobiusSquareTail n := by
    unfold mobiusSquareTail
    apply tsum_congr
    intro k
    change
      ((ArithmeticFunction.moebius (D + 1 + (k + (n - D))) : ℤ) : ℝ) /
          (((2 : ℝ) ^ (D + 1 + (k + (n - D))) - 1) ^ 2) =
        ((ArithmeticFunction.moebius (n + 1 + k) : ℤ) : ℝ) /
          (((2 : ℝ) ^ (n + 1 + k) - 1) ^ 2)
    have hshift : D + 1 + (k + (n - D)) = n + 1 + k := by
      calc
        D + 1 + (k + (n - D)) = (D + (n - D)) + 1 + k := by ac_rfl
        _ = n + 1 + k := by rw [hsum]
    rw [hshift]
  change (∑' k : ℕ, f k) =
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) /
        (((2 : ℝ) ^ n - 1) ^ 2) +
      mobiusSquareTail n
  rw [← hsplit, hfinite, htail]

/-- The sign of the first nonzero omitted Möbius channel directs the entire
tail.  The remaining uncertainty is the sharp square-tail radius after that
channel, so this interval can certify cases missed by the symmetric bound. -/
theorem mobiusSquareTail_directed_of_first_support
    {D n : ℕ} (hDn : D < n)
    (hzero : ∀ d : ℕ, D < d → d < n → ArithmeticFunction.moebius d = 0)
    (hunit : |ArithmeticFunction.moebius n| = 1) :
    1 / (((2 : ℝ) ^ n - 1) ^ 2) -
          4 / (3 * (((2 : ℝ) ^ (n + 1) - 1) ^ 2)) ≤
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * mobiusSquareTail D ∧
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) * mobiusSquareTail D ≤
        1 / (((2 : ℝ) ^ n - 1) ^ 2) +
          4 / (3 * (((2 : ℝ) ^ (n + 1) - 1) ^ 2)) := by
  let μn : ℝ := ((ArithmeticFunction.moebius n : ℤ) : ℝ)
  let R : ℝ := 4 / (3 * (((2 : ℝ) ^ (n + 1) - 1) ^ 2))
  have hμabs : |μn| = 1 := by
    dsimp [μn]
    rw [← Int.cast_abs]
    exact_mod_cast hunit
  have hμsq : μn ^ 2 = 1 := by
    rw [← sq_abs, hμabs]
    norm_num
  have hscaled : |μn * mobiusSquareTail n| ≤ R := by
    rw [abs_mul, hμabs, one_mul]
    exact abs_mobiusSquareTail_le n
  have hsides := abs_le.mp hscaled
  rw [mobiusSquareTail_eq_first_support_add_tail hDn hzero]
  change
    1 / (((2 : ℝ) ^ n - 1) ^ 2) - R ≤
        μn * (μn / (((2 : ℝ) ^ n - 1) ^ 2) + mobiusSquareTail n) ∧
      μn * (μn / (((2 : ℝ) ^ n - 1) ^ 2) + mobiusSquareTail n) ≤
        1 / (((2 : ℝ) ^ n - 1) ^ 2) + R
  have hmain :
      μn * (μn / (((2 : ℝ) ^ n - 1) ^ 2) + mobiusSquareTail n) =
        1 / (((2 : ℝ) ^ n - 1) ^ 2) + μn * mobiusSquareTail n := by
    calc
      _ = μn ^ 2 / (((2 : ℝ) ^ n - 1) ^ 2) +
          μn * mobiusSquareTail n := by ring
      _ = _ := by rw [hμsq]
  rw [hmain]
  constructor <;> linarith [hsides.1, hsides.2]

/-- Lower endpoint of the directed interval for the actual diagonal. -/
noncomputable def directedLambertLowerBound (H n : ℕ) : ℝ :=
  (diagonalCoefficient H : ℝ) *
    (1 / (((2 : ℝ) ^ n - 1) ^ 2) -
      4 / (3 * (((2 : ℝ) ^ (n + 1) - 1) ^ 2)))

/-- Upper endpoint of the directed interval for the actual diagonal. -/
noncomputable def directedLambertUpperBound (H n : ℕ) : ℝ :=
  (diagonalCoefficient H : ℝ) *
    (1 / (((2 : ℝ) ^ n - 1) ^ 2) +
      4 / (3 * (((2 : ℝ) ^ (n + 1) - 1) ^ 2)))

/-- The actual diagonal displacement from the rational centre lies in the
first-support-directed interval. -/
theorem scaleDiagonalTailDifference_directed_lambert_interval
    {H D n : ℕ} (hDn : D < n)
    (hzero : ∀ d : ℕ, D < d → d < n → ArithmeticFunction.moebius d = 0)
    (hunit : |ArithmeticFunction.moebius n| = 1) :
    directedLambertLowerBound H n ≤
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          (scaleDiagonalTailDifference H - lambertProjectedDiagonal H D) ∧
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          (scaleDiagonalTailDifference H - lambertProjectedDiagonal H D) ≤
        directedLambertUpperBound H n := by
  have hdir := mobiusSquareTail_directed_of_first_support hDn hzero hunit
  have hC : (0 : ℝ) ≤ diagonalCoefficient H := by positivity
  rw [scaleDiagonalTailDifference_sub_lambertProjectedDiagonal]
  unfold directedLambertLowerBound directedLambertUpperBound
  constructor
  · convert mul_le_mul_of_nonneg_left hdir.1 hC using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hdir.2 hC using 1 <;> ring

/-- Directed separation from the integer lattice rules out a full-target hit.
Unlike the symmetric consumer, the hypothesis only excludes the one interval
in which the first omitted Möbius channel can move the centre. -/
theorem scaleFullTarget_miss_of_directed_lambert_interval
    {H D n : ℕ} (hDn : D < n)
    (hzero : ∀ d : ℕ, D < d → d < n → ArithmeticFunction.moebius d = 0)
    (hunit : |ArithmeticFunction.moebius n| = 1)
    (hsep : ∀ z : ℤ, ¬(
      directedLambertLowerBound H n ≤
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            ((z : ℝ) - lambertProjectedDiagonal H D) ∧
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            ((z : ℝ) - lambertProjectedDiagonal H D) ≤
          directedLambertUpperBound H n)) :
    ¬ScaleFullTargetHit H := by
  rw [scaleFullTargetHit_iff_integral]
  rintro ⟨z, hz⟩
  have hbounds := scaleDiagonalTailDifference_directed_lambert_interval
    (H := H) hDn hzero hunit
  rw [← hz] at hbounds
  exact hsep z hbounds

/-- The actual diagonal lies in the sharp squared-Mersenne enclosure around
the exact rational centre. -/
theorem abs_scaleDiagonalTailDifference_sub_lambertProjectedDiagonal_le
    (H D : ℕ) :
    |scaleDiagonalTailDifference H - lambertProjectedDiagonal H D| ≤
      lambertSquareComplementBound H D := by
  rw [scaleDiagonalTailDifference_sub_lambertProjectedDiagonal, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ diagonalCoefficient H by positivity)]
  unfold lambertSquareComplementBound
  calc
    (diagonalCoefficient H : ℝ) * |mobiusSquareTail D| ≤
        (diagonalCoefficient H : ℝ) *
          (4 / (3 * (((2 : ℝ) ^ (D + 1) - 1) ^ 2))) := by
      gcongr
      exact abs_mobiusSquareTail_le D
    _ = 4 * (diagonalCoefficient H : ℝ) /
        (3 * (((2 : ℝ) ^ (D + 1) - 1) ^ 2)) := by ring

/-- Exact rational separation of the squared-Mersenne centre from the integer
lattice forces a genuine miss of the actual full target. -/
theorem scaleFullTarget_miss_of_lambert_projected_separation
    {H D : ℕ}
    (hsep : ∀ z : ℤ, lambertSquareComplementBound H D <
      |lambertProjectedDiagonal H D - (z : ℝ)|) :
    ¬ScaleFullTargetHit H :=
  scaleFullTarget_miss_of_enclosure
    (abs_scaleDiagonalTailDifference_sub_lambertProjectedDiagonal_le H D) hsep

#print axioms totientSeries_eq_pnat_half_pow
#print axioms rat_den_int_add_mul
#print axioms lambertProjectedDiagonalRat_den
#print axioms mobius_square_series_eq_partial_add_tail
#print axioms scaleDiagonalTailDifference_sub_lambertProjectedDiagonal
#print axioms abs_mobiusSquareTail_le
#print axioms mobiusSquareTail_eq_first_support_add_tail
#print axioms mobiusSquareTail_directed_of_first_support
#print axioms scaleDiagonalTailDifference_directed_lambert_interval
#print axioms scaleFullTarget_miss_of_directed_lambert_interval
#print axioms abs_scaleDiagonalTailDifference_sub_lambertProjectedDiagonal_le
#print axioms scaleFullTarget_miss_of_lambert_projected_separation

end Erdos249257.SquaredMersenneDiagonalEnclosure
