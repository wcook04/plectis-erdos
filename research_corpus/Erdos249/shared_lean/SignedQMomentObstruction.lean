import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Erdos257PeriodNoncollapse.MersenneLambertLadder

/-!
# Signed finite q-moment determinants

This file isolates two algebraic cores of the signed-Hankel route for Erdős
#249: a positivity-free rectangular determinant expansion derived from the
Leibniz formula, and the unique-largest-dyadic-exponent parity argument that
forces a cleared common numerator to be odd and hence non-zero.
-/

namespace Erdos257PeriodNoncollapse.SignedQMomentObstruction

open scoped BigOperators
open Matrix

/-! ## A rectangular Cauchy–Binet expansion

The pinned Mathlib determinant API does not currently expose rectangular
Cauchy–Binet directly.  The following compact expansion is derived from the
Leibniz formula.  Non-injective maps remain in the sum here; in Vandermonde
applications their determinant is zero.
-/

theorem det_mul_rectangular
    {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix ι κ R) (N : Matrix κ ι R) :
    Matrix.det (M * N) =
      ∑ p : ι → κ, Matrix.det (fun i j ↦ M i (p j)) * ∏ i, N (p i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  congr 1
  funext p
  rw [Finset.sum_mul]
  congr 1
  funext σ
  rw [Finset.prod_mul_distrib]
  ring

/-- A finite signed moment matrix on an arbitrary finite atom type.  Here `w`
is the full atom mass (for the target application, `w N = a N * x N`). -/
def finiteSignedMomentMatrix
    {R κ : Type*} [CommRing R] [Fintype κ]
    (n : ℕ) (w x : κ → R) : Matrix (Fin n) (Fin n) R :=
  fun i j ↦ ∑ a : κ, w a * x a ^ (i.1 + j.1)

/-! ## Unique-terminal dyadic parity -/

private theorem even_finset_sum {α : Type*} (s : Finset α) (f : α → ℤ)
    (h : ∀ i ∈ s, Even (f i)) : Even (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih (fun i hi ↦ h i (by simp [hi])))

private theorem not_even_finset_sum_of_unique_not_even
    {α : Type*} (s : Finset α) (f : α → ℤ) (m : α)
    (hm : m ∈ s) (hodd : ¬ Even (f m))
    (heven : ∀ i ∈ s, i ≠ m → Even (f i)) :
    ¬ Even (∑ i ∈ s, f i) := by
  classical
  rw [← Finset.sum_erase_add _ _ hm]
  intro htotal
  have hrest : Even (∑ i ∈ s.erase m, f i) :=
    even_finset_sum (s.erase m) f (fun i hi ↦
      heven i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  exact hodd ((Int.even_add.mp htotal).mp hrest)

/-- If one dyadic denominator exponent is uniquely largest and its numerator
is odd, the common numerator obtained by clearing that denominator is odd. -/
theorem scaled_dyadic_sum_odd {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) % 2 = 1 := by
  rw [← Int.not_even_iff]
  apply not_even_finset_sum_of_unique_not_even s
      (fun i ↦ u i * (2 : ℤ) ^ (e m - e i)) m hm
  · simpa using hu
  · intro i hi him
    have hne : e m - e i ≠ 0 :=
      Nat.ne_of_gt (Nat.sub_pos_of_lt (hmax i hi him))
    have hp : Even ((2 : ℤ) ^ (e m - e i)) :=
      Int.even_pow.mpr ⟨⟨1, rfl⟩, hne⟩
    exact hp.mul_left (u i)

/-- The same unique-terminal hypothesis gives non-vanishing after common
dyadic denominator clearing. -/
theorem scaled_dyadic_sum_ne_zero {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) ≠ 0 := by
  intro hzero
  have hodd := scaled_dyadic_sum_odd s u e m hm hu hmax
  simp [hzero] at hodd

/-! ## Concrete truncated moments -/

/-- The finite signed `q = 1/2` moment used by the Möbius Hankel lane. -/
def truncatedMoment (a : ℕ → ℤ) (Y k : ℕ) : ℚ :=
  ∑ N ∈ Finset.Icc 1 Y,
    (a N : ℚ) * ((1 / (2 : ℚ)) ^ N) ^ (k + 1)

/-- Hankel matrix associated to a moment sequence. -/
def hankelMatrix (m : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ m (i.1 + j.1)

/-- Order-`n` Hankel determinant associated to a moment sequence. -/
def hankelDet (m : ℕ → ℚ) (n : ℕ) : ℚ :=
  Matrix.det (hankelMatrix m n)

/-! ## The infinite Möbius--Mersenne ladder

The first two atoms are `1` and `-3⁻ʳ`.  The remaining atoms admit a
uniform geometric majorant, giving a kernel-checked analytic entrypoint for
the signed-Hankel packet rather than only its finite determinant algebra.
-/

open ArithmeticFunction

/-- The `n`th atom of the Möbius--Mersenne power ladder, with the positive
integer index shifted to `n + 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)

/-- The Möbius--Mersenne power ladder `Θᵣ`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

/-- The exact contribution of the first two atoms `d = 1, 2`. -/
noncomputable def mobiusMersenneTwoAtom (r : ℕ) : ℝ :=
  1 - 1 / (3 : ℝ) ^ r

/-- The ladder tail beginning at the third positive-integer atom. -/
noncomputable def mobiusMersenneTailAfterTwo (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r (n + 2)

private lemma mersenne_shift_lower (n : ℕ) :
    (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) - 1 := by
  rw [pow_succ]
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  nlinarith

/-- Every rung `r ≥ 1` is dominated termwise by the geometric series with
ratio `2⁻ʳ`. -/
theorem norm_mobiusMersenneTerm_le_geometric
    (r n : ℕ) :
    ‖mobiusMersenneTerm r n‖ ≤
      ((1 : ℝ) / (2 : ℝ) ^ r) ^ n := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ (n + 1) - 1 := by
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
  have hpow_lower :
      ((2 : ℝ) ^ n) ^ r ≤ ((2 : ℝ) ^ (n + 1) - 1) ^ r :=
    pow_le_pow_left₀ (by positivity) (mersenne_shift_lower n) r
  have hmu : |((moebius (n + 1) : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast MersenneLambertLadder.abs_moebius_le_one (n + 1)
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hden_pow_pos :
      (0 : ℝ) < ((2 : ℝ) ^ (n + 1) - 1) ^ r := by positivity
  have hpow_comm : ((2 : ℝ) ^ r) ^ n = ((2 : ℝ) ^ n) ^ r := by
    simp only [← pow_mul]
    rw [Nat.mul_comm]
  rw [mobiusMersenneTerm, Real.norm_eq_abs, abs_div,
    abs_of_pos hden_pow_pos, div_pow, one_pow, hpow_comm,
    div_le_div_iff₀ hden_pow_pos (pow_pos hpow_pos r)]
  calc
    |((moebius (n + 1) : ℤ) : ℝ)| * ((2 : ℝ) ^ n) ^ r
        ≤ 1 * ((2 : ℝ) ^ n) ^ r :=
      mul_le_mul_of_nonneg_right hmu (pow_nonneg hpow_pos.le r)
    _ = ((2 : ℝ) ^ n) ^ r := one_mul _
    _ ≤ ((2 : ℝ) ^ (n + 1) - 1) ^ r := hpow_lower
    _ = 1 * ((2 : ℝ) ^ (n + 1) - 1) ^ r := (one_mul _).symm

/-- Absolute convergence of every nontrivial rung of the ladder. -/
theorem summable_mobiusMersenneTerm (r : ℕ) (hr : 1 ≤ r) :
    Summable (mobiusMersenneTerm r) := by
  have hratio : ((1 : ℝ) / (2 : ℝ) ^ r) < 1 := by
    have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
      one_lt_pow₀ (by norm_num) (by omega)
    exact (div_lt_one (by positivity)).2 hp
  have hgeo : Summable (fun n : ℕ => ((1 : ℝ) / (2 : ℝ) ^ r) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hratio
  exact Summable.of_norm_bounded hgeo
    (norm_mobiusMersenneTerm_le_geometric r)

/-- The first rung is the exact rational value `1/2`. -/
theorem mobiusMersenneTheta_one :
    mobiusMersenneTheta 1 = 1 / 2 := by
  calc
    mobiusMersenneTheta 1 =
        ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) /
          ((2 : ℝ) ^ (d : ℕ) - 1) := by
            rw [mobiusMersenneTheta,
              tsum_pnat_eq_tsum_succ
                (f := fun d : ℕ => ((moebius d : ℤ) : ℝ) /
                  ((2 : ℝ) ^ d - 1))]
            apply tsum_congr
            intro n
            simp [mobiusMersenneTerm]
    _ = 1 / 2 :=
      MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half

/-- The second rung is exactly the #249 totient value minus `1/2`. -/
theorem mobiusMersenneTheta_two_eq_totient_offset :
    mobiusMersenneTheta 2 =
      (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) *
        ((1 : ℝ) / 2) ^ (n : ℕ)) - 1 / 2 := by
  have h := MersenneLambertLadder.tsum_totient_half_pow_eq_half_add_moebius_sq
  have htheta :
      mobiusMersenneTheta 2 =
        ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) /
          ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
    rw [mobiusMersenneTheta,
      tsum_pnat_eq_tsum_succ
        (f := fun d : ℕ => ((moebius d : ℤ) : ℝ) /
          ((2 : ℝ) ^ d - 1) ^ 2)]
    apply tsum_congr
    intro n
    simp [mobiusMersenneTerm]
  rw [htheta]
  linarith

/-- Exact decomposition into the two dominant atoms and the geometric tail. -/
theorem mobiusMersenneTheta_eq_twoAtom_add_tail
    (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r =
      mobiusMersenneTwoAtom r + mobiusMersenneTailAfterTwo r := by
  have hsplit := (summable_mobiusMersenneTerm r hr).sum_add_tsum_nat_add 2
  rw [mobiusMersenneTheta, ← hsplit]
  rw [mobiusMersenneTailAfterTwo]
  have hprefix :
      (∑ i ∈ Finset.range 2, mobiusMersenneTerm r i) =
        mobiusMersenneTwoAtom r := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    have hmu1 : moebius 1 = 1 := moebius_apply_one
    have hmu2 : moebius 2 = -1 :=
      moebius_apply_prime (by norm_num : Nat.Prime 2)
    rw [show mobiusMersenneTerm r 0 = 1 by
          rw [mobiusMersenneTerm, hmu1]
          norm_num [one_pow],
        show mobiusMersenneTerm r 1 = -(1 / (3 : ℝ) ^ r) by
          rw [mobiusMersenneTerm, hmu2]
          norm_num [div_eq_mul_inv]]
    unfold mobiusMersenneTwoAtom
    ring
  rw [hprefix]

/-- Sharp geometric enclosure for all atoms after `d = 2`. -/
theorem abs_mobiusMersenneTailAfterTwo_le
    (r : ℕ) (hr : 1 ≤ r) :
    |mobiusMersenneTailAfterTwo r| ≤
      (((1 : ℝ) / (2 : ℝ) ^ r) ^ 2) /
        (1 - (1 : ℝ) / (2 : ℝ) ^ r) := by
  let q : ℝ := (1 : ℝ) / (2 : ℝ) ^ r
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
      one_lt_pow₀ (by norm_num) (by omega)
    exact (div_lt_one (by positivity)).2 hp
  have hgeo : Summable (fun n : ℕ => q ^ (n + 2)) := by
    have h := summable_geometric_of_lt_one hq0 hq1
    exact (h.mul_left (q ^ 2)).congr (fun n => by rw [pow_add]; ring)
  have hterm : ∀ n : ℕ,
      |mobiusMersenneTerm r (n + 2)| ≤ q ^ (n + 2) := by
    intro n
    rw [← Real.norm_eq_abs]
    exact norm_mobiusMersenneTerm_le_geometric r (n + 2)
  have habs : Summable (fun n : ℕ => |mobiusMersenneTerm r (n + 2)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm hgeo
  have hsigned : Summable (fun n : ℕ => mobiusMersenneTerm r (n + 2)) :=
    summable_abs_iff.mp habs
  rw [mobiusMersenneTailAfterTwo]
  have hupper :
      (∑' n : ℕ, mobiusMersenneTerm r (n + 2)) ≤
        ∑' n : ℕ, |mobiusMersenneTerm r (n + 2)| :=
    hsigned.tsum_le_tsum (fun n => le_abs_self _) habs
  have hlower :
      -(∑' n : ℕ, mobiusMersenneTerm r (n + 2)) ≤
        ∑' n : ℕ, |mobiusMersenneTerm r (n + 2)| := by
    rw [← tsum_neg]
    exact hsigned.neg.tsum_le_tsum (fun n => neg_le_abs _) habs
  calc
    |∑' n : ℕ, mobiusMersenneTerm r (n + 2)|
        ≤ ∑' n : ℕ, |mobiusMersenneTerm r (n + 2)| :=
      abs_le.mpr ⟨by linarith, hupper⟩
    _ ≤ ∑' n : ℕ, q ^ (n + 2) := habs.tsum_le_tsum hterm hgeo
    _ = ∑' n : ℕ, q ^ 2 * q ^ n := by
      apply tsum_congr
      intro n
      rw [pow_add]
      ring
    _ = q ^ 2 * ∑' n : ℕ, q ^ n := tsum_mul_left
    _ = q ^ 2 / (1 - q) := by
      rw [tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]
    _ = (((1 : ℝ) / (2 : ℝ) ^ r) ^ 2) /
        (1 - (1 : ℝ) / (2 : ℝ) ^ r) := by rfl

/-- The dominant two-atom ladder has an exact strictly positive Hankel gap. -/
theorem mobiusMersenneTwoAtom_hankelGap (r : ℕ) :
    mobiusMersenneTwoAtom (r + 1) ^ 2 -
        mobiusMersenneTwoAtom r * mobiusMersenneTwoAtom (r + 2) =
      4 / (3 : ℝ) ^ (r + 2) := by
  unfold mobiusMersenneTwoAtom
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  field_simp [pow_add, h3]
  ring

theorem mobiusMersenneTwoAtom_strict_logConcave (r : ℕ) :
    mobiusMersenneTwoAtom r * mobiusMersenneTwoAtom (r + 2) <
      mobiusMersenneTwoAtom (r + 1) ^ 2 := by
  have hgap := mobiusMersenneTwoAtom_hankelGap r
  have hpos : (0 : ℝ) < 4 / (3 : ℝ) ^ (r + 2) := by positivity
  linarith

/-! ## Eventual strict log-concavity of the full ladder -/

/-- Closed form of the geometric tail bound. -/
noncomputable def mobiusMersenneTailBound (r : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1))

/-- The perturbation budget for the shifted `2 × 2` Hankel gap. -/
noncomputable def mobiusMersenneHankelError (r : ℕ) : ℝ :=
  mobiusMersenneTailBound r +
    2 * mobiusMersenneTailBound (r + 1) +
    mobiusMersenneTailBound (r + 2) +
    mobiusMersenneTailBound r * mobiusMersenneTailBound (r + 2)

/-- The exact dominant two-atom gap. -/
noncomputable def mobiusMersenneDominantGap (r : ℕ) : ℝ :=
  4 / (3 : ℝ) ^ (r + 2)

theorem mobiusMersenneTailBound_pos (r : ℕ) (hr : 1 ≤ r) :
    0 < mobiusMersenneTailBound r := by
  have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hsub : (0 : ℝ) < (2 : ℝ) ^ r - 1 := by linarith
  unfold mobiusMersenneTailBound
  exact one_div_pos.mpr (mul_pos hp0 hsub)

theorem mobiusMersenneTailBound_eq_geometric
    (r : ℕ) (hr : 1 ≤ r) :
    (((1 : ℝ) / (2 : ℝ) ^ r) ^ 2) /
        (1 - (1 : ℝ) / (2 : ℝ) ^ r) =
      mobiusMersenneTailBound r := by
  have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hsub : (0 : ℝ) < (2 : ℝ) ^ r - 1 := by linarith
  unfold mobiusMersenneTailBound
  field_simp [ne_of_gt hp0, ne_of_gt hsub]

theorem abs_mobiusMersenneTailAfterTwo_le_bound
    (r : ℕ) (hr : 1 ≤ r) :
    |mobiusMersenneTailAfterTwo r| ≤ mobiusMersenneTailBound r := by
  calc
    |mobiusMersenneTailAfterTwo r| ≤
        (((1 : ℝ) / (2 : ℝ) ^ r) ^ 2) /
          (1 - (1 : ℝ) / (2 : ℝ) ^ r) :=
      abs_mobiusMersenneTailAfterTwo_le r hr
    _ = mobiusMersenneTailBound r :=
      mobiusMersenneTailBound_eq_geometric r hr

/-- Exact positive difference behind the `1/4` tail contraction. -/
theorem mobiusMersenneTailBound_sub_four_succ
    (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTailBound r -
        4 * mobiusMersenneTailBound (r + 1) =
      1 / ((2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) *
        (2 * (2 : ℝ) ^ r - 1)) := by
  have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hsub : (0 : ℝ) < (2 : ℝ) ^ r - 1 := by linarith
  have htwosub : (0 : ℝ) < 2 * (2 : ℝ) ^ r - 1 := by linarith
  have htwosub' : (0 : ℝ) < (2 : ℝ) ^ r * 2 - 1 := by linarith
  unfold mobiusMersenneTailBound
  rw [pow_succ]
  field_simp [ne_of_gt hp0, ne_of_gt hsub, ne_of_gt htwosub,
    ne_of_gt htwosub']
  ring

theorem mobiusMersenneTailBound_succ_lt_quarter
    (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTailBound (r + 1) <
      mobiusMersenneTailBound r / 4 := by
  have hdiff := mobiusMersenneTailBound_sub_four_succ r hr
  have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hsub : (0 : ℝ) < (2 : ℝ) ^ r - 1 := by linarith
  have htwosub : (0 : ℝ) < 2 * (2 : ℝ) ^ r - 1 := by linarith
  have hrhs :
      0 < 1 / ((2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) *
        (2 * (2 : ℝ) ^ r - 1)) := by
    exact one_div_pos.mpr (mul_pos (mul_pos hp0 hsub) htwosub)
  nlinarith

theorem mobiusMersenneHankelError_succ_lt_quarter
    (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneHankelError (r + 1) <
      mobiusMersenneHankelError r / 4 := by
  have h0 := mobiusMersenneTailBound_succ_lt_quarter r hr
  have h1 := mobiusMersenneTailBound_succ_lt_quarter (r + 1) (by omega)
  have h2 := mobiusMersenneTailBound_succ_lt_quarter (r + 2) (by omega)
  have h1' :
      mobiusMersenneTailBound (r + 2) <
        mobiusMersenneTailBound (r + 1) / 4 := by
    simpa only [Nat.add_assoc] using h1
  have h2' :
      mobiusMersenneTailBound (r + 3) ≤
        mobiusMersenneTailBound (r + 2) / 4 := by
    simpa only [Nat.add_assoc] using h2.le
  have hb0 := (mobiusMersenneTailBound_pos r hr).le
  have hb1 := (mobiusMersenneTailBound_pos (r + 1) (by omega)).le
  have hb2 := (mobiusMersenneTailBound_pos (r + 2) (by omega)).le
  have hb3pos := mobiusMersenneTailBound_pos (r + 3) (by omega)
  have hb3 := hb3pos.le
  have hprod :
      mobiusMersenneTailBound (r + 1) *
          mobiusMersenneTailBound (r + 3) <
        (mobiusMersenneTailBound r / 4) *
          (mobiusMersenneTailBound (r + 2) / 4) :=
    mul_lt_mul h0 h2' hb3pos (by positivity)
  have hprod' :
      mobiusMersenneTailBound (r + 1) *
          mobiusMersenneTailBound (r + 3) <
        mobiusMersenneTailBound r *
          mobiusMersenneTailBound (r + 2) / 4 := by
    nlinarith [mul_nonneg hb0 hb2]
  unfold mobiusMersenneHankelError
  nlinarith

theorem mobiusMersenneDominantGap_succ (r : ℕ) :
    mobiusMersenneDominantGap (r + 1) =
      mobiusMersenneDominantGap r / 3 := by
  unfold mobiusMersenneDominantGap
  have hidx : r + 1 + 2 = (r + 2) + 1 := by omega
  rw [hidx, pow_succ]
  ring

theorem mobiusMersenneDominantGap_pos (r : ℕ) :
    0 < mobiusMersenneDominantGap r := by
  unfold mobiusMersenneDominantGap
  positivity

/-- The exact-rational base margin from the verifier, propagated by the
`1/4` tail contraction against the `1/3` dominant-gap contraction. -/
theorem mobiusMersenneHankelError_lt_dominantGap
    (r : ℕ) (hr : 5 ≤ r) :
    mobiusMersenneHankelError r < mobiusMersenneDominantGap r := by
  induction r, hr using Nat.le_induction with
  | base =>
      norm_num [mobiusMersenneHankelError, mobiusMersenneTailBound,
        mobiusMersenneDominantGap]
  | succ r hr ih =>
      have herror := mobiusMersenneHankelError_succ_lt_quarter r (by omega)
      have hgap := mobiusMersenneDominantGap_succ r
      have hgapPos := mobiusMersenneDominantGap_pos r
      rw [hgap]
      nlinarith

private theorem perturbed_hankel_gap_lower
    (T0 T1 T2 e0 e1 e2 B0 B1 B2 : ℝ)
    (hT0 : 0 ≤ T0 ∧ T0 ≤ 1)
    (hT1 : 0 ≤ T1 ∧ T1 ≤ 1)
    (hT2 : 0 ≤ T2 ∧ T2 ≤ 1)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (he0 : |e0| ≤ B0) (he1 : |e1| ≤ B1) (he2 : |e2| ≤ B2) :
    T1 ^ 2 - T0 * T2 - (B0 + 2 * B1 + B2 + B0 * B2) ≤
      (T1 + e1) ^ 2 - (T0 + e0) * (T2 + e2) := by
  have hc1 : |2 * T1 * e1| ≤ 2 * B1 := by
    have hmul : T1 * |e1| ≤ 1 * B1 :=
      mul_le_mul hT1.2 he1 (abs_nonneg _) (by norm_num)
    calc
      |2 * T1 * e1| = 2 * T1 * |e1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hT1.1]
      _ ≤ 2 * (1 * B1) :=
        by simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
      _ = 2 * B1 := by ring
  have hc0 : |T0 * e2| ≤ B2 := by
    have hmul : T0 * |e2| ≤ 1 * B2 :=
      mul_le_mul hT0.2 he2 (abs_nonneg _) (by norm_num)
    calc
      |T0 * e2| = T0 * |e2| := by rw [abs_mul, abs_of_nonneg hT0.1]
      _ ≤ 1 * B2 := hmul
      _ = B2 := one_mul _
  have hc2 : |T2 * e0| ≤ B0 := by
    have hmul : T2 * |e0| ≤ 1 * B0 :=
      mul_le_mul hT2.2 he0 (abs_nonneg _) (by norm_num)
    calc
      |T2 * e0| = T2 * |e0| := by rw [abs_mul, abs_of_nonneg hT2.1]
      _ ≤ 1 * B0 := hmul
      _ = B0 := one_mul _
  have hce : |e0 * e2| ≤ B0 * B2 := by
    rw [abs_mul]
    exact mul_le_mul he0 he2 (abs_nonneg _) hB0
  have hc1lo := (abs_le.mp hc1).1
  have hc0hi := (abs_le.mp hc0).2
  have hc2hi := (abs_le.mp hc2).2
  have hcehi := (abs_le.mp hce).2
  nlinarith [sq_nonneg e1]

theorem mobiusMersenneTwoAtom_mem_unitInterval
    (r : ℕ) (hr : 1 ≤ r) :
    0 ≤ mobiusMersenneTwoAtom r ∧ mobiusMersenneTwoAtom r ≤ 1 := by
  have hp : (1 : ℝ) < (3 : ℝ) ^ r :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hfracPos : (0 : ℝ) < 1 / (3 : ℝ) ^ r := by positivity
  have hfracLe : (1 : ℝ) / (3 : ℝ) ^ r ≤ 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp.le
    norm_num at h ⊢
    exact h
  unfold mobiusMersenneTwoAtom
  constructor <;> linarith

/-- Every shifted `2 × 2` Hankel determinant is already strictly negative
from rung `5` onward.  This is the first unconditional infinite nonvanishing
theorem for the full Möbius--Mersenne ladder in the packet. -/
theorem mobiusMersenneTheta_strict_logConcave_of_five_le
    (r : ℕ) (hr : 5 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) <
      mobiusMersenneTheta (r + 1) ^ 2 := by
  have hs0 := mobiusMersenneTheta_eq_twoAtom_add_tail r (by omega)
  have hs1 := mobiusMersenneTheta_eq_twoAtom_add_tail (r + 1) (by omega)
  have hs2 := mobiusMersenneTheta_eq_twoAtom_add_tail (r + 2) (by omega)
  rw [hs0, hs1, hs2]
  have hpert := perturbed_hankel_gap_lower
    (mobiusMersenneTwoAtom r)
    (mobiusMersenneTwoAtom (r + 1))
    (mobiusMersenneTwoAtom (r + 2))
    (mobiusMersenneTailAfterTwo r)
    (mobiusMersenneTailAfterTwo (r + 1))
    (mobiusMersenneTailAfterTwo (r + 2))
    (mobiusMersenneTailBound r)
    (mobiusMersenneTailBound (r + 1))
    (mobiusMersenneTailBound (r + 2))
    (mobiusMersenneTwoAtom_mem_unitInterval r (by omega))
    (mobiusMersenneTwoAtom_mem_unitInterval (r + 1) (by omega))
    (mobiusMersenneTwoAtom_mem_unitInterval (r + 2) (by omega))
    (mobiusMersenneTailBound_pos r (by omega)).le
    (mobiusMersenneTailBound_pos (r + 1) (by omega)).le
    (mobiusMersenneTailBound_pos (r + 2) (by omega)).le
    (abs_mobiusMersenneTailAfterTwo_le_bound r (by omega))
    (abs_mobiusMersenneTailAfterTwo_le_bound (r + 1) (by omega))
    (abs_mobiusMersenneTailAfterTwo_le_bound (r + 2) (by omega))
  have htwo := mobiusMersenneTwoAtom_hankelGap r
  have herr := mobiusMersenneHankelError_lt_dominantGap r hr
  unfold mobiusMersenneHankelError mobiusMersenneDominantGap at herr
  nlinarith

/-! ## The four finite rungs and the all-rung theorem -/

/-- Exact first-five-atom approximation (`d = 1,2,3,4,5`). -/
noncomputable def mobiusMersennePrefixFive (r : ℕ) : ℝ :=
  1 - 1 / (3 : ℝ) ^ r - 1 / (7 : ℝ) ^ r - 1 / (31 : ℝ) ^ r

/-- Remaining atoms after the first five positive indices. -/
noncomputable def mobiusMersenneTailAfterFive (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r (n + 5)

/-- Geometric majorant for the tail after `d = 5`. -/
noncomputable def mobiusMersenneTailBoundFive (r : ℕ) : ℝ :=
  (((1 : ℝ) / (2 : ℝ) ^ r) ^ 5) /
    (1 - (1 : ℝ) / (2 : ℝ) ^ r)

theorem mobiusMersenneTheta_eq_prefixFive_add_tail
    (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r =
      mobiusMersennePrefixFive r + mobiusMersenneTailAfterFive r := by
  have hsplit := (summable_mobiusMersenneTerm r hr).sum_add_tsum_nat_add 5
  rw [mobiusMersenneTheta, ← hsplit, mobiusMersenneTailAfterFive]
  have hmu1 : moebius 1 = 1 := moebius_apply_one
  have hmu2 : moebius 2 = -1 :=
    moebius_apply_prime (by norm_num : Nat.Prime 2)
  have hmu3 : moebius 3 = -1 :=
    moebius_apply_prime (by norm_num : Nat.Prime 3)
  have hmu4 : moebius 4 = 0 := by
    have h := moebius_apply_prime_pow (p := 2) (k := 2)
      (by norm_num : Nat.Prime 2) (by norm_num)
    norm_num at h
    simpa using h
  have hmu5 : moebius 5 = -1 :=
    moebius_apply_prime (by norm_num : Nat.Prime 5)
  have hprefix :
      (∑ i ∈ Finset.range 5, mobiusMersenneTerm r i) =
        mobiusMersennePrefixFive r := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    rw [show mobiusMersenneTerm r 0 = 1 by
          rw [mobiusMersenneTerm, hmu1]
          norm_num [one_pow],
        show mobiusMersenneTerm r 1 = -(1 / (3 : ℝ) ^ r) by
          rw [mobiusMersenneTerm, hmu2]
          norm_num [div_eq_mul_inv],
        show mobiusMersenneTerm r 2 = -(1 / (7 : ℝ) ^ r) by
          rw [mobiusMersenneTerm, hmu3]
          norm_num [div_eq_mul_inv],
        show mobiusMersenneTerm r 3 = 0 by
          simp [mobiusMersenneTerm, hmu4],
        show mobiusMersenneTerm r 4 = -(1 / (31 : ℝ) ^ r) by
          rw [mobiusMersenneTerm, hmu5]
          norm_num [div_eq_mul_inv]]
    unfold mobiusMersennePrefixFive
    ring
  rw [hprefix]

theorem mobiusMersenneTailBoundFive_pos (r : ℕ) (hr : 1 ≤ r) :
    0 < mobiusMersenneTailBoundFive r := by
  have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hden : (0 : ℝ) < 1 - (1 : ℝ) / (2 : ℝ) ^ r := by
    rw [sub_pos, div_lt_one (by positivity)]
    exact hp
  unfold mobiusMersenneTailBoundFive
  positivity

theorem abs_mobiusMersenneTailAfterFive_le
    (r : ℕ) (hr : 1 ≤ r) :
    |mobiusMersenneTailAfterFive r| ≤ mobiusMersenneTailBoundFive r := by
  let q : ℝ := (1 : ℝ) / (2 : ℝ) ^ r
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
      one_lt_pow₀ (by norm_num) (by omega)
    exact (div_lt_one (by positivity)).2 hp
  have hgeo : Summable (fun n : ℕ => q ^ (n + 5)) := by
    have h := summable_geometric_of_lt_one hq0 hq1
    exact (h.mul_left (q ^ 5)).congr (fun n => by rw [pow_add]; ring)
  have hterm : ∀ n : ℕ,
      |mobiusMersenneTerm r (n + 5)| ≤ q ^ (n + 5) := by
    intro n
    rw [← Real.norm_eq_abs]
    exact norm_mobiusMersenneTerm_le_geometric r (n + 5)
  have habs : Summable (fun n : ℕ => |mobiusMersenneTerm r (n + 5)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm hgeo
  have hsigned : Summable (fun n : ℕ => mobiusMersenneTerm r (n + 5)) :=
    summable_abs_iff.mp habs
  rw [mobiusMersenneTailAfterFive]
  have hupper :
      (∑' n : ℕ, mobiusMersenneTerm r (n + 5)) ≤
        ∑' n : ℕ, |mobiusMersenneTerm r (n + 5)| :=
    hsigned.tsum_le_tsum (fun n => le_abs_self _) habs
  have hlower :
      -(∑' n : ℕ, mobiusMersenneTerm r (n + 5)) ≤
        ∑' n : ℕ, |mobiusMersenneTerm r (n + 5)| := by
    rw [← tsum_neg]
    exact hsigned.neg.tsum_le_tsum (fun n => neg_le_abs _) habs
  calc
    |∑' n : ℕ, mobiusMersenneTerm r (n + 5)|
        ≤ ∑' n : ℕ, |mobiusMersenneTerm r (n + 5)| :=
      abs_le.mpr ⟨by linarith, hupper⟩
    _ ≤ ∑' n : ℕ, q ^ (n + 5) := habs.tsum_le_tsum hterm hgeo
    _ = ∑' n : ℕ, q ^ 5 * q ^ n := by
      apply tsum_congr
      intro n
      rw [pow_add]
      ring
    _ = q ^ 5 * ∑' n : ℕ, q ^ n := tsum_mul_left
    _ = q ^ 5 / (1 - q) := by
      rw [tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]
    _ = mobiusMersenneTailBoundFive r := by rfl

private theorem mobiusMersenneTheta_strict_of_prefixFive
    (r : ℕ) (hr : 1 ≤ r)
    (hT0 : 0 ≤ mobiusMersennePrefixFive r ∧
      mobiusMersennePrefixFive r ≤ 1)
    (hT1 : 0 ≤ mobiusMersennePrefixFive (r + 1) ∧
      mobiusMersennePrefixFive (r + 1) ≤ 1)
    (hT2 : 0 ≤ mobiusMersennePrefixFive (r + 2) ∧
      mobiusMersennePrefixFive (r + 2) ≤ 1)
    (hnumeric :
      0 < mobiusMersennePrefixFive (r + 1) ^ 2 -
        mobiusMersennePrefixFive r * mobiusMersennePrefixFive (r + 2) -
        (mobiusMersenneTailBoundFive r +
          2 * mobiusMersenneTailBoundFive (r + 1) +
          mobiusMersenneTailBoundFive (r + 2) +
          mobiusMersenneTailBoundFive r *
            mobiusMersenneTailBoundFive (r + 2))) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) <
      mobiusMersenneTheta (r + 1) ^ 2 := by
  have hs0 := mobiusMersenneTheta_eq_prefixFive_add_tail r hr
  have hs1 := mobiusMersenneTheta_eq_prefixFive_add_tail (r + 1) (by omega)
  have hs2 := mobiusMersenneTheta_eq_prefixFive_add_tail (r + 2) (by omega)
  rw [hs0, hs1, hs2]
  have hpert := perturbed_hankel_gap_lower
    (mobiusMersennePrefixFive r)
    (mobiusMersennePrefixFive (r + 1))
    (mobiusMersennePrefixFive (r + 2))
    (mobiusMersenneTailAfterFive r)
    (mobiusMersenneTailAfterFive (r + 1))
    (mobiusMersenneTailAfterFive (r + 2))
    (mobiusMersenneTailBoundFive r)
    (mobiusMersenneTailBoundFive (r + 1))
    (mobiusMersenneTailBoundFive (r + 2))
    hT0 hT1 hT2
    (mobiusMersenneTailBoundFive_pos r hr).le
    (mobiusMersenneTailBoundFive_pos (r + 1) (by omega)).le
    (mobiusMersenneTailBoundFive_pos (r + 2) (by omega)).le
    (abs_mobiusMersenneTailAfterFive_le r hr)
    (abs_mobiusMersenneTailAfterFive_le (r + 1) (by omega))
    (abs_mobiusMersenneTailAfterFive_le (r + 2) (by omega))
  nlinarith

theorem mobiusMersenneTheta_strict_logConcave_of_one_le_of_lt_five
    (r : ℕ) (hr1 : 1 ≤ r) (hr5 : r < 5) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) <
      mobiusMersenneTheta (r + 1) ^ 2 := by
  interval_cases r <;>
    apply mobiusMersenneTheta_strict_of_prefixFive <;>
    norm_num [mobiusMersennePrefixFive, mobiusMersenneTailBoundFive]

/-- Full order-two signed-Hankel theorem from the returned packet. -/
theorem mobiusMersenneTheta_strict_logConcave
    (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) <
      mobiusMersenneTheta (r + 1) ^ 2 := by
  by_cases h5 : 5 ≤ r
  · exact mobiusMersenneTheta_strict_logConcave_of_five_le r h5
  · exact mobiusMersenneTheta_strict_logConcave_of_one_le_of_lt_five
      r hr (by omega)

/-- The corresponding shifted `2 × 2` Hankel determinant is negative. -/
theorem mobiusMersenneTheta_hankel_two_neg
    (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) -
      mobiusMersenneTheta (r + 1) ^ 2 < 0 := by
  have h := mobiusMersenneTheta_strict_logConcave r hr
  linarith

#print axioms mobiusMersenneTheta_eq_twoAtom_add_tail
#print axioms abs_mobiusMersenneTailAfterTwo_le
#print axioms mobiusMersenneTwoAtom_strict_logConcave
#print axioms mobiusMersenneTheta_strict_logConcave_of_five_le
#print axioms mobiusMersenneTheta_strict_logConcave
#print axioms mobiusMersenneTheta_hankel_two_neg

end Erdos257PeriodNoncollapse.SignedQMomentObstruction
