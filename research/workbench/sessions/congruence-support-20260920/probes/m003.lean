import ErdosProblems.Erdos251.ResidueFeedbackCore
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Congruence feedback and bounded-carry rigidity

The existing #251 `ResidueFeedback` module supplies the constructive side,
including the infinite-sum theorem. This module supplies its arithmetic
contrast: an unbounded common divisor of radix and correction excludes every
positive bounded rational carry orbit. The ordinary factorial support theorem
is in `paper/synthesis/optimal-sparse-perturbations.tex`.
-/

namespace ErdosProblems.Synthesis.CongruenceInterpolation

/-- The carry recurrence has no positive bounded solution at a modulus hit.
This is the arithmetic obstruction behind the factorial/Cantor-series theorem. -/
theorem no_bounded_carry_at_modulus_hit
    (q base prev carry a e : ℕ)
    (hbase : q ∣ base) (he : q ∣ e)
    (hrec : carry + a + e = base * prev)
    (hpos : 0 < carry + a) (hbound : carry + a < q) : False := by
  have hsum : q ∣ carry + a + e := by rw [hrec]; exact dvd_mul_of_dvd_left hbase _
  have hdiv : q ∣ carry + a := (Nat.dvd_add_iff_left he).mpr hsum
  exact (not_le_of_gt hbound) (Nat.le_of_dvd hpos hdiv)

/-- Cofinal multiplier divisibility defeats every eventually positive bounded
integral carry with eventually divisible corrections. Only one sufficiently
large modulus is needed. -/
theorem no_eventual_bounded_carry
    (base carry a e : ℕ → ℕ) (q N B : ℕ)
    (hB : B < q)
    (hhit : ∀ K, ∃ n, K ≤ n ∧ q ∣ base n)
    (he : ∀ n, N ≤ n → q ∣ e n)
    (hrec : ∀ n, N ≤ n → carry (n + 1) + a n + e n = base n * carry n)
    (hpos : ∀ n, N ≤ n → 0 < carry (n + 1) + a n)
    (hbound : ∀ n, N ≤ n → carry (n + 1) + a n ≤ B) : False := by
  obtain ⟨n, hn, hd⟩ := hhit N
  exact no_bounded_carry_at_modulus_hit q (base n) (carry n) (carry (n + 1))
    (a n) (e n) hd (he n hn) (hrec n hn) (hpos n hn)
    (lt_of_le_of_lt (hbound n hn) hB)

/-- Quantitative obstruction: an eventually bounded positive real carry orbit
with natural coefficients is irrational if the radix and correction have
arbitrarily large common divisors arbitrarily late. This theorem does not
assume that the mixed-radix denominators clear every rational denominator. -/
theorem irrational_of_unbounded_gcd
    (base a e : ℕ → ℕ) (tail : ℕ → ℝ) (N B : ℕ)
    (hrec : ∀ n, (base n : ℝ) * tail n = a n + e n + tail (n + 1))
    (hpos : ∀ n, N ≤ n → 0 < tail (n + 1) + a n)
    (hbound : ∀ n, N ≤ n → tail (n + 1) + a n ≤ B)
    (hgcd : ∀ K L, ∃ n, K ≤ n ∧ L < Nat.gcd (base n) (e n)) :
    Irrational (tail 0) := by
  by_contra hrat
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  let d : ℕ := r.den
  let C : ℕ → ℤ := fun n => Nat.rec r.num
    (fun i z => (base i : ℤ) * z - (d : ℤ) * ((a i : ℤ) + e i)) n
  have hd : (0 : ℝ) < d := by exact_mod_cast r.den_pos
  have hC : ∀ n, (Int.cast (R := ℝ) (C n)) = (d : ℝ) * tail n := by
    intro n
    induction n with
    | zero =>
      simp only [C, Nat.rec_zero]
      rw [hr, Rat.cast_def]
      dsimp [d]
      field_simp
    | succ n ih =>
      change (↑((base n : ℤ) * C n - (d : ℤ) * ((a n : ℤ) + e n)) : ℝ) = _
      push_cast
      rw [ih]
      calc
        (base n : ℝ) * ((d : ℝ) * tail n) - (d : ℝ) * (a n + e n) =
            (d : ℝ) * ((base n : ℝ) * tail n - (a n + e n)) := by ring
        _ = (d : ℝ) * tail (n + 1) := by rw [hrec n]; ring
  obtain ⟨n, hn, hg⟩ := hgcd N (d * B)
  let g := Nat.gcd (base n) (e n)
  have hdiv : (g : ℤ) ∣ C (n + 1) + (d : ℤ) * a n := by
    obtain ⟨u, hu⟩ := Nat.gcd_dvd_left (base n) (e n)
    obtain ⟨v, hv⟩ := Nat.gcd_dvd_right (base n) (e n)
    refine ⟨(u : ℤ) * C n - (d : ℤ) * v, ?_⟩
    change (base n : ℤ) * C n - (d : ℤ) * ((a n : ℤ) + e n) +
      (d : ℤ) * a n = _
    rw [hu, hv]
    push_cast
    dsimp [g]
    ring
  have hz : (↑(C (n + 1) + (d : ℤ) * a n) : ℝ) =
      (d : ℝ) * (tail (n + 1) + a n) := by
    push_cast
    rw [hC]
    ring
  have hpositive : 0 < C (n + 1) + (d : ℤ) * a n := by
    have := mul_pos hd (hpos n hn)
    rw [← hz] at this
    exact_mod_cast this
  have hsmall : C (n + 1) + (d : ℤ) * a n < (g : ℤ) := by
    have hle := mul_le_mul_of_nonneg_left (hbound n hn) hd.le
    have hgr : (d : ℝ) * B < g := by exact_mod_cast hg
    have := lt_of_le_of_lt hle hgr
    rw [← hz] at this
    exact_mod_cast this
  exact (not_le_of_gt hsmall) (Int.le_of_dvd hpositive hdiv)

#print axioms no_eventual_bounded_carry
#print axioms irrational_of_unbounded_gcd

end ErdosProblems.Synthesis.CongruenceInterpolation
