import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős #1049: finite arithmetic for rational Padé homogenisation

This module isolates formal denominator-exponent calculations for rational-base
Padé homogenisation.  Every exponent is doubled, so the statements live over
`ℤ` and contain no floor or parity bookkeeping.  It also records elementary
content and sign identities for a `2 × 2` determinant of integer coefficient
pairs.  No concrete coefficient family, integrality theorem, remainder
estimate, or sign theorem is supplied here.
-/

namespace ErdosProblems.Erdos1049

/-- Twice a proposed common denominator exponent
`Eₙ = (3n² - n) / 2`. -/
def rationalPadeDenExpTwice (n : ℤ) : ℤ :=
  3 * n * n - n

/-- Twice the denominator exponent of the `k`-th summand in the homogenised
little-`q` Legendre `P` polynomial. -/
def rationalPadePSummandDenExpTwice (n k : ℤ) : ℤ :=
  2 * (k * (n - k) + n * k) + k * (k - 1)

/-- The doubled `P`-summand exponent never exceeds the proposed common
exponent when `0 ≤ k ≤ n`.  The gap factors as
`(n-k)(3n-k-1)`. -/
theorem rationalPadePSummandDenExpTwice_le
    {n k : ℤ} (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k ≤ n) :
    rationalPadePSummandDenExpTwice n k ≤ rationalPadeDenExpTwice n := by
  by_cases hn0 : n = 0
  · have hk0 : k = 0 := by omega
    simp [rationalPadePSummandDenExpTwice, rationalPadeDenExpTwice, hn0, hk0]
  · have hn1 : 1 ≤ n := by omega
    have hleft : 0 ≤ n - k := sub_nonneg.mpr hkn
    have hright : 0 ≤ 3 * n - k - 1 := by nlinarith
    have hprod : 0 ≤ (n - k) * (3 * n - k - 1) :=
      mul_nonneg hleft hright
    unfold rationalPadePSummandDenExpTwice rationalPadeDenExpTwice
    nlinarith

/-- Twice the maximal denominator exponent in the `Q`-summand calculation,
after the change of variables `j = n - m - 1`. -/
def rationalPadeQMaxDenExpTwice (n m : ℤ) : ℤ :=
  let j := n - m - 1
  2 * (n * n - n) + j * j + 2 * j * m + j - m * m + 3 * m

/-- Exact doubled gap identity for the rational `Q`-summand maximum:
`2(Eₙ-Fmax) = 2(n + m(m-1))`. -/
theorem rationalPadeQMaxDenExpTwice_gap (n m : ℤ) :
    rationalPadeDenExpTwice n - rationalPadeQMaxDenExpTwice n m =
      2 * (n + m * (m - 1)) := by
  simp [rationalPadeDenExpTwice, rationalPadeQMaxDenExpTwice]
  ring

/-- In the nonvanishing `m ≥ 1` range, the doubled `Q` exponent is bounded
by the same common exponent. -/
theorem rationalPadeQMaxDenExpTwice_le
    {n m : ℤ} (hn : 0 ≤ n) (hm : 1 ≤ m) :
    rationalPadeQMaxDenExpTwice n m ≤ rationalPadeDenExpTwice n := by
  have hm0 : 0 ≤ m := by omega
  have hmm1 : 0 ≤ m - 1 := by omega
  have hprod : 0 ≤ m * (m - 1) := mul_nonneg hm0 hmm1
  have hgap := rationalPadeQMaxDenExpTwice_gap n m
  nlinarith

/-- The real error of an integer Padé coefficient pair `(U,V)` at `S`. -/
noncomputable def rationalPadeError (S : ℝ) (U V : ℤ) : ℝ :=
  (U : ℝ) * S - (V : ℝ)

/-- The `2 × 2` determinant of two integer Padé coefficient pairs.

For coefficient pairs indexed by `n` and `m`, this is
`Uₙ Vₘ - Uₘ Vₙ`.  Unlike either individual coefficient pair, the determinant
can inherit every divisor common to the two `U` coefficients and every divisor
common to the two `V` coefficients. -/
def rationalPadeExteriorDet (Un Vn Um Vm : ℤ) : ℤ :=
  Un * Vm - Um * Vn

/-- Scaling both coefficients in one Padé row scales its error by exactly the
same factor.  Row content therefore carries no hidden analytic improvement. -/
theorem rationalPadeError_mul
    (S : ℝ) (c U V : ℤ) :
    rationalPadeError S (c * U) (c * V) =
      (c : ℝ) * rationalPadeError S U V := by
  simp [rationalPadeError]
  ring

/-- Rowwise contents factor from the exterior determinant exactly.  Thus any
local divisor coming only from independent contents of the two rows is paid
for by the same product in the Archimedean determinant height. -/
theorem rationalPadeExteriorDet_mul_contents
    (cn cm Un Vn Um Vm : ℤ) :
    rationalPadeExteriorDet
        (cn * Un) (cn * Vn) (cm * Um) (cm * Vm) =
      cn * cm * rationalPadeExteriorDet Un Vn Um Vm := by
  simp [rationalPadeExteriorDet]
  ring

/-- The Archimedean determinant height acquires exactly the absolute product
of the two row contents—no less and no more. -/
theorem natAbs_rationalPadeExteriorDet_mul_contents
    (cn cm Un Vn Um Vm : ℤ) :
    Int.natAbs (rationalPadeExteriorDet
        (cn * Un) (cn * Vn) (cm * Um) (cm * Vm)) =
      Int.natAbs cn * Int.natAbs cm *
        Int.natAbs (rationalPadeExteriorDet Un Vn Um Vm) := by
  rw [rationalPadeExteriorDet_mul_contents]
  simp only [Int.natAbs_mul]

/-- The product of the two row contents is therefore an explicit divisor of
the scaled exterior determinant.  The residual arithmetic object is precisely
the determinant of the primitive rows. -/
theorem contentProduct_dvd_rationalPadeExteriorDet
    (cn cm Un Vn Um Vm : ℤ) :
    cn * cm ∣ rationalPadeExteriorDet
      (cn * Un) (cn * Vn) (cm * Um) (cm * Vm) := by
  refine ⟨rationalPadeExteriorDet Un Vn Um Vm, ?_⟩
  exact rationalPadeExteriorDet_mul_contents cn cm Un Vn Um Vm

/-- Exact cancellation of the target value in the exterior determinant. -/
theorem rationalPadeExteriorDet_cast_eq
    (S : ℝ) (Un Vn Um Vm : ℤ) :
    (rationalPadeExteriorDet Un Vn Um Vm : ℝ) =
      (Um : ℝ) * rationalPadeError S Un Vn -
        (Un : ℝ) * rationalPadeError S Um Vm := by
  simp [rationalPadeExteriorDet, rationalPadeError]
  ring

/-- A divisor common to the two `U` coefficients divides their `2 × 2`
determinant. -/
theorem commonU_dvd_rationalPadeExteriorDet
    {d Un Vn Um Vm : ℤ} (hUn : d ∣ Un) (hUm : d ∣ Um) :
    d ∣ rationalPadeExteriorDet Un Vn Um Vm := by
  rcases hUn with ⟨un, rfl⟩
  rcases hUm with ⟨um, rfl⟩
  refine ⟨un * Vm - um * Vn, ?_⟩
  simp [rationalPadeExteriorDet]
  ring

/-- A divisor common to the two `V` coefficients also divides their `2 × 2`
determinant. -/
theorem commonV_dvd_rationalPadeExteriorDet
    {d Un Vn Um Vm : ℤ} (hVn : d ∣ Vn) (hVm : d ∣ Vm) :
    d ∣ rationalPadeExteriorDet Un Vn Um Vm := by
  rcases hVn with ⟨vn, rfl⟩
  rcases hVm with ⟨vm, rfl⟩
  refine ⟨Un * vm - Um * vn, ?_⟩
  simp [rationalPadeExteriorDet]
  ring

/-- If both Padé errors are positive while the first coefficients have signs
`Uₙ < 0 < Uₘ`, the exterior determinant is strictly positive. -/
theorem rationalPadeExteriorDet_pos_of_left_neg_right_pos
    {S : ℝ} {Un Vn Um Vm : ℤ}
    (hLn : 0 < rationalPadeError S Un Vn)
    (hLm : 0 < rationalPadeError S Um Vm)
    (hUn : Un < 0) (hUm : 0 < Um) :
    0 < rationalPadeExteriorDet Un Vn Um Vm := by
  have hUmR : (0 : ℝ) < Um := by exact_mod_cast hUm
  have hUnR : (Un : ℝ) < 0 := by exact_mod_cast hUn
  have hfirst :
      0 < (Um : ℝ) * rationalPadeError S Un Vn :=
    mul_pos hUmR hLn
  have hsecond :
      (Un : ℝ) * rationalPadeError S Um Vm < 0 :=
    mul_neg_of_neg_of_pos hUnR hLm
  have hdetR : (0 : ℝ) < rationalPadeExteriorDet Un Vn Um Vm := by
    rw [rationalPadeExteriorDet_cast_eq]
    linarith
  exact_mod_cast hdetR

/-- The reversed alternating-sign configuration makes the exterior determinant
strictly negative. -/
theorem rationalPadeExteriorDet_neg_of_left_pos_right_neg
    {S : ℝ} {Un Vn Um Vm : ℤ}
    (hLn : 0 < rationalPadeError S Un Vn)
    (hLm : 0 < rationalPadeError S Um Vm)
    (hUn : 0 < Un) (hUm : Um < 0) :
    rationalPadeExteriorDet Un Vn Um Vm < 0 := by
  have hUnR : (0 : ℝ) < Un := by exact_mod_cast hUn
  have hUmR : (Um : ℝ) < 0 := by exact_mod_cast hUm
  have hfirst :
      (Um : ℝ) * rationalPadeError S Un Vn < 0 :=
    mul_neg_of_neg_of_pos hUmR hLn
  have hsecond :
      0 < (Un : ℝ) * rationalPadeError S Um Vm :=
    mul_pos hUnR hLm
  have hdetR : (rationalPadeExteriorDet Un Vn Um Vm : ℝ) < 0 := by
    rw [rationalPadeExteriorDet_cast_eq]
    linarith
  exact_mod_cast hdetR

/-- Under the displayed positivity and alternating-sign hypotheses, the
adjacent determinant cannot vanish.  This theorem does not produce those
hypotheses for a concrete Padé sequence. -/
theorem rationalPadeExteriorDet_ne_zero_of_left_neg_right_pos
    {S : ℝ} {Un Vn Um Vm : ℤ}
    (hLn : 0 < rationalPadeError S Un Vn)
    (hLm : 0 < rationalPadeError S Um Vm)
    (hUn : Un < 0) (hUm : 0 < Um) :
    rationalPadeExteriorDet Un Vn Um Vm ≠ 0 :=
  ne_of_gt
    (rationalPadeExteriorDet_pos_of_left_neg_right_pos
      hLn hLm hUn hUm)

/-- The reversed alternating-sign configuration likewise prevents
cancellation, provided both errors are positive. -/
theorem rationalPadeExteriorDet_ne_zero_of_left_pos_right_neg
    {S : ℝ} {Un Vn Um Vm : ℤ}
    (hLn : 0 < rationalPadeError S Un Vn)
    (hLm : 0 < rationalPadeError S Um Vm)
    (hUn : 0 < Un) (hUm : Um < 0) :
    rationalPadeExteriorDet Un Vn Um Vm ≠ 0 :=
  ne_of_lt
    (rationalPadeExteriorDet_neg_of_left_pos_right_neg
      hLn hLm hUn hUm)

end ErdosProblems.Erdos1049
