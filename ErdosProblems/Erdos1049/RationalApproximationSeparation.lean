import ErdosProblems.Erdos1049.TwoSelectorRemainderEscape

/-!
R6 candidate. NOT compiled in the review environment.

Finite separation at a rational test point. The result uses the already
present rational_integerLinearForm_gap, handles the zero determinant case,
and avoids requiring two independent approximating rows. The asymptotic
source estimates needed for an irrationality measure are not proved here.
-/
namespace ErdosProblems.Erdos1049

/-- An integral form of size at most `1/(2*q)` controls separation from every
rational with denominator `q`, even when that rational equals the row ratio. -/
theorem rational_separation_of_small_integer_form
    (A B p q : ℤ) (ξ : ℝ) (hq : 0 < q)
    (hsmall : 2 * (q : ℝ) * |(A : ℝ) * ξ - B| ≤ 1) :
    |(A : ℝ) * ξ - B| ≤
      |(A : ℝ)| * |ξ - (p : ℝ) / (q : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hz : (A : ℝ) * ((p : ℝ) / (q : ℝ)) - B = 0
  · have hid : (A : ℝ) * ξ - B =
        (A : ℝ) * (ξ - (p : ℝ) / (q : ℝ)) := by
      calc
        (A : ℝ) * ξ - B =
            (A : ℝ) * (ξ - (p : ℝ) / (q : ℝ)) +
              ((A : ℝ) * ((p : ℝ) / (q : ℝ)) - B) := by ring
        _ = (A : ℝ) * (ξ - (p : ℝ) / (q : ℝ)) := by rw [hz]; ring
    exact le_of_eq (by rw [hid, abs_mul])
  · have hgap := rational_integerLinearForm_gap p q B A hq hz
    have hhalf : 2 * |(A : ℝ) * ξ - B| ≤ (1 : ℝ) / q := by
      apply (le_div_iff₀ hqR).2
      nlinarith [hsmall]
    have htriangle :
        |(A : ℝ) * ((p : ℝ) / (q : ℝ)) - B| ≤
          |(A : ℝ) * ξ - B| +
            |(A : ℝ)| * |ξ - (p : ℝ) / (q : ℝ)| := by
      calc
        |(A : ℝ) * ((p : ℝ) / (q : ℝ)) - B| =
            |((A : ℝ) * ξ - B) -
              (A : ℝ) * (ξ - (p : ℝ) / (q : ℝ))| := by
                congr 1
                ring
        _ ≤ |(A : ℝ) * ξ - B| +
              |(A : ℝ) * (ξ - (p : ℝ) / (q : ℝ))| := abs_sub _ _
        _ = |(A : ℝ) * ξ - B| +
              |(A : ℝ)| * |ξ - (p : ℝ) / (q : ℝ)| := by rw [abs_mul]
    linarith

end ErdosProblems.Erdos1049
