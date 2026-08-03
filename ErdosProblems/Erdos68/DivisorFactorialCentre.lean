import ErdosProblems.Erdos68.FiniteDefectAutomaton
<<<<<<< HEAD
=======
import ErdosProblems.Erdos68.FactorialCarry
>>>>>>> pr-30
import Mathlib.Tactic

/-!
# Erdős problem 68: divisor-factorial residual centre

For each `m`, this module defines the finite rational sum

`F_m = m! * sum_{2 <= n <= m} 1 / ((n!)^(floor(m/n)) (n!-1))`

and the divisor sum

`C_m = sum_{2 <= n <= m, n | m} m! / (n!)^(m/n)`.

Splitting the summands according to whether `n` divides `m` gives the exact
identity

`F_m = m F_(m-1) + 1 + 1/(m!-1) - C_m`

<<<<<<< HEAD
for `m >= 3`.  This is a rational finite-sum recurrence.  The file does not
prove that `C_m` is the cast of an integer sequence, so it does not by itself
instantiate the integer defect code from `FiniteDefectAutomaton`.  It also
does not identify `F_m` with a remainder of the infinite series or prove an
orbit, tail estimate, or irrationality statement.
=======
for `m >= 3`.  Multinomial divisibility shows that every summand of `C_m` is
an integer.  The recurrence therefore instantiates the integer defect code
from `FiniteDefectAutomaton`, giving an exact floor formula and fractional
recurrence for the concrete finite centres.  The file does not identify
`F_m` with a remainder of the infinite series or prove a finite-state orbit,
tail estimate, or irrationality statement.
>>>>>>> pr-30
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- One summand of the finite residual centre. -/
def residualCentreTerm (m n : ℕ) : ℚ :=
  (m.factorial : ℚ) /
    ((n.factorial : ℚ) ^ (m / n) * ((n.factorial : ℚ) - 1))

/-- One divisor-factorial coefficient summand. -/
def factorialCoeffTerm (m n : ℕ) : ℚ :=
  (m.factorial : ℚ) / (n.factorial : ℚ) ^ (m / n)

/-- The finite rational centre
`m! * sum_{2 <= n <= m} 1 / ((n!)^(floor(m/n)) (n!-1))`. -/
def residualCentre (m : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 2 m, residualCentreTerm m n

/-- Rational form of the divisor-factorial coefficient
`sum_{n | m, n >= 2} m! / (n!)^(m/n)`. -/
def factorialCoeffRat (m : ℕ) : ℚ :=
  ∑ n ∈ (Finset.Icc 2 m).filter (· ∣ m), factorialCoeffTerm m n

<<<<<<< HEAD
=======
/-- Integer form of the divisor-factorial coefficient. -/
def factorialCoeffNat (m : ℕ) : ℕ :=
  ∑ n ∈ (Finset.Icc 2 m).filter (· ∣ m),
    m.factorial / (n.factorial ^ (m / n))

/-- Each rational divisor-factorial summand is the cast of its exact natural
quotient. -/
theorem factorialCoeffTerm_eq_natCast_of_dvd (m n : ℕ) (hdvd : n ∣ m) :
    factorialCoeffTerm m n =
      (m.factorial / (n.factorial ^ (m / n)) : ℕ) := by
  have hdiv : n.factorial ^ (m / n) ∣ m.factorial :=
    factorial_pow_dvd_factorial_of_dvd hdvd
  have hne : ((n.factorial ^ (m / n) : ℕ) : ℚ) ≠ 0 := by
    positivity
  unfold factorialCoeffTerm
  rw [← Nat.cast_pow]
  exact (Nat.cast_div hdiv hne).symm

/-- The rational divisor-factorial coefficient is the cast of the integer
coefficient with the same support. -/
theorem factorialCoeffRat_eq_natCast (m : ℕ) :
    factorialCoeffRat m = (factorialCoeffNat m : ℚ) := by
  unfold factorialCoeffRat factorialCoeffNat
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact factorialCoeffTerm_eq_natCast_of_dvd m n (Finset.mem_filter.mp hn).2

>>>>>>> pr-30
private theorem factorial_eq_mul_pred_factorial (m : ℕ) (hm : 1 ≤ m) :
    m.factorial = m * (m - 1).factorial := by
  have hs : m - 1 + 1 = m := by omega
  calc
    m.factorial = (m - 1 + 1).factorial := by rw [hs]
    _ = (m - 1 + 1) * (m - 1).factorial := Nat.factorial_succ _
    _ = m * (m - 1).factorial := by rw [hs]

private theorem pred_div_eq_of_not_dvd {m n : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) (hndvd : ¬n ∣ m) :
    (m - 1) / n = m / n := by
  apply Nat.div_eq_of_lt_le
  · have hmod : m % n ≠ 0 := by
      simpa [Nat.dvd_iff_mod_eq_zero] using hndvd
    have hdecomp := Nat.div_add_mod m n
    have hmodPos : 1 ≤ m % n := Nat.one_le_iff_ne_zero.mpr hmod
    rw [mul_comm] at hdecomp
    omega
  · have hupper := Nat.lt_mul_div_succ m hn
    rw [mul_comm n] at hupper
    omega

private theorem pred_div_add_one_eq_of_dvd {m n : ℕ}
    (hn : 0 < n) (hnm : n ≤ m) (hdvd : n ∣ m) :
    (m - 1) / n + 1 = m / n := by
  have hmod : m % n = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hdecomp : n * (m / n) = m := by
    have h := Nat.div_add_mod m n
    rw [hmod, add_zero] at h
    exact h
  have hqPos : 0 < m / n := Nat.div_pos hnm hn
  have hqPred : m / n - 1 + 1 = m / n := Nat.sub_add_cancel hqPos
  have hlower : (m / n - 1) * n ≤ m - 1 := by
    have heq : (m / n - 1) * n + n = m := by
      calc
        (m / n - 1) * n + n =
            ((m / n - 1) + 1) * n := by rw [add_mul, one_mul]
        _ = (m / n) * n := by rw [hqPred]
        _ = m := by rw [mul_comm, hdecomp]
    omega
  have hupper : m - 1 < (m / n - 1 + 1) * n := by
    rw [hqPred, mul_comm, hdecomp]
    omega
  have hdiv :
      (m - 1) / n = m / n - 1 :=
    Nat.div_eq_of_lt_le hlower hupper
  omega

/-- Away from a divisor of `m`, the centre term merely scales by `m`. -/
theorem residualCentreTerm_of_not_dvd (m n : ℕ)
    (hm : 1 ≤ m) (hn : 2 ≤ n) (hndvd : ¬n ∣ m) :
    residualCentreTerm m n =
      (m : ℚ) * residualCentreTerm (m - 1) n := by
  have hfacNat := factorial_eq_mul_pred_factorial m hm
  have hfac :
      (m.factorial : ℚ) =
        (m : ℚ) * ((m - 1).factorial : ℚ) := by
    exact_mod_cast hfacNat
  have hdiv :=
    pred_div_eq_of_not_dvd (show 0 < n by omega) hm hndvd
  unfold residualCentreTerm
  rw [hfac, hdiv]
  ring

/-- At a divisor of `m`, increasing the exponent removes exactly the
corresponding divisor-factorial coefficient term. -/
theorem residualCentreTerm_of_dvd (m n : ℕ)
    (hn : 2 ≤ n) (hnm : n ≤ m) (hdvd : n ∣ m) :
    residualCentreTerm m n =
      (m : ℚ) * residualCentreTerm (m - 1) n -
        factorialCoeffTerm m n := by
  have hm : 1 ≤ m := by omega
  have hfacNat := factorial_eq_mul_pred_factorial m hm
  have hfac :
      (m.factorial : ℚ) =
        (m : ℚ) * ((m - 1).factorial : ℚ) := by
    exact_mod_cast hfacNat
  have hdiv :=
    pred_div_add_one_eq_of_dvd (show 0 < n by omega) hnm hdvd
  have hfactPos : 1 < n.factorial :=
    (Nat.one_lt_factorial).2 hn
  have hfact : (n.factorial : ℚ) ≠ 0 := by positivity
  have hfactSub : (n.factorial : ℚ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hfactPos.ne')
  unfold residualCentreTerm factorialCoeffTerm
  rw [hfac, ← hdiv, pow_succ]
  field_simp
  ring

/-- The diagonal centre term is the factorial error `1 / (m! - 1)`. -/
theorem residualCentreTerm_self (m : ℕ) (hm : 2 ≤ m) :
    residualCentreTerm m m = factorialEpsilon m := by
  have hmpos : 0 < m := by omega
  have hfac : (m.factorial : ℚ) ≠ 0 := by positivity
  unfold residualCentreTerm factorialEpsilon
  rw [Nat.div_self hmpos, pow_one]
  field_simp

/-- The diagonal divisor-factorial coefficient term is one. -/
theorem factorialCoeffTerm_self (m : ℕ) (hm : 1 ≤ m) :
    factorialCoeffTerm m m = 1 := by
  have hmpos : 0 < m := by omega
  have hfac : (m.factorial : ℚ) ≠ 0 := by positivity
  unfold factorialCoeffTerm
  rw [Nat.div_self hmpos, pow_one]
  exact div_self hfac

/-- Exact finite-sum recurrence for the residual centre. -/
theorem residualCentre_recurrence (m : ℕ) (hm : 3 ≤ m) :
    residualCentre m =
      (m : ℚ) * residualCentre (m - 1) + 1 +
        factorialEpsilon m - factorialCoeffRat m := by
  let s := Finset.Icc 2 (m - 1)
  have hm1 : 1 ≤ m := by omega
  have hIcc :
      Finset.Icc 2 m = insert m s := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    dsimp [s]
    simp only [Finset.mem_Icc]
    omega
  have hmNotMem : m ∉ s := by
    simp [s]
    omega
  have hFilter :
      (Finset.Icc 2 m).filter (· ∣ m) =
        insert m (s.filter (· ∣ m)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    dsimp [s]
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn2, hnm⟩, hdiv⟩
      by_cases hEq : n = m
      · exact Or.inl hEq
      · exact Or.inr ⟨⟨hn2, by omega⟩, hdiv⟩
    · rintro (hEq | ⟨⟨hn2, hpred⟩, hdiv⟩)
      · subst n
        exact ⟨⟨by omega, le_rfl⟩, dvd_rfl⟩
      · exact ⟨⟨hn2, by omega⟩, hdiv⟩
  have hmNotFilter : m ∉ s.filter (· ∣ m) := by
    simp [hmNotMem]
  have hpoint :
      ∀ n ∈ s,
        residualCentreTerm m n =
          (m : ℚ) * residualCentreTerm (m - 1) n -
            if n ∣ m then factorialCoeffTerm m n else 0 := by
    intro n hn
    have hnBounds : 2 ≤ n ∧ n ≤ m - 1 := by
      simpa [s] using hn
    by_cases hdiv : n ∣ m
    · rw [if_pos hdiv]
      exact residualCentreTerm_of_dvd m n hnBounds.1 (by omega) hdiv
    · rw [if_neg hdiv, sub_zero]
      exact residualCentreTerm_of_not_dvd m n hm1 hnBounds.1 hdiv
  have hsum :
      ∑ n ∈ s, residualCentreTerm m n =
        (m : ℚ) * ∑ n ∈ s, residualCentreTerm (m - 1) n -
          ∑ n ∈ s.filter (· ∣ m), factorialCoeffTerm m n := by
    calc
      ∑ n ∈ s, residualCentreTerm m n =
          ∑ n ∈ s,
            ((m : ℚ) * residualCentreTerm (m - 1) n -
              if n ∣ m then factorialCoeffTerm m n else 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hpoint n hn
      _ =
          (m : ℚ) * ∑ n ∈ s, residualCentreTerm (m - 1) n -
            ∑ n ∈ s.filter (· ∣ m), factorialCoeffTerm m n := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
            congr 1
            rw [Finset.sum_filter]
  have hCentre :
      residualCentre m =
        residualCentreTerm m m +
          ∑ n ∈ s, residualCentreTerm m n := by
    unfold residualCentre
    rw [hIcc, Finset.sum_insert hmNotMem]
  have hCentrePred :
      residualCentre (m - 1) =
        ∑ n ∈ s, residualCentreTerm (m - 1) n := by
    rfl
  have hCoeff :
      factorialCoeffRat m =
        factorialCoeffTerm m m +
          ∑ n ∈ s.filter (· ∣ m), factorialCoeffTerm m n := by
    unfold factorialCoeffRat
    rw [hFilter, Finset.sum_insert hmNotFilter]
  rw [hCentre, hCentrePred, hCoeff, hsum,
    residualCentreTerm_self m (by omega),
    factorialCoeffTerm_self m (by omega)]
  ring

<<<<<<< HEAD
=======
/-- Integer-coefficient form of the concrete finite-centre recurrence. -/
theorem residualCentre_recurrence_int (m : ℕ) (hm : 3 ≤ m) :
    residualCentre m =
      (m : ℚ) * residualCentre (m - 1) + 1 + factorialEpsilon m -
        ((factorialCoeffNat m : ℤ) : ℚ) := by
  simpa [factorialCoeffRat_eq_natCast] using residualCentre_recurrence m hm

/-- The concrete residual centre instantiates the integer factorial defect
code: its code is the floor of the preceding rescaled gap. -/
theorem residualCentre_defectCode_eq_factorial_floor
    (m : ℕ) (hm : 3 ≤ m) :
    centreDefectCode residualCentre (fun k => (factorialCoeffNat k : ℤ)) m =
      ⌊(m : ℚ) * centreGap residualCentre (m - 1) -
        1 / ((m.factorial : ℚ) - 1)⌋ := by
  apply centreDefectCode_eq_factorial_floor
  exact residualCentre_recurrence_int m hm

/-- Exact fractional recurrence for the gap of the concrete finite residual
centre. -/
theorem residualCentre_gap_factorial_recurrence
    (m : ℕ) (hm : 3 ≤ m) :
    centreGap residualCentre m =
      (m : ℚ) * centreGap residualCentre (m - 1) -
        1 / ((m.factorial : ℚ) - 1) -
          (centreDefectCode residualCentre
            (fun k => (factorialCoeffNat k : ℤ)) m : ℚ) := by
  apply centreGap_factorial_recurrence
  exact residualCentre_recurrence_int m hm

>>>>>>> pr-30
end ErdosProblems.Erdos68
