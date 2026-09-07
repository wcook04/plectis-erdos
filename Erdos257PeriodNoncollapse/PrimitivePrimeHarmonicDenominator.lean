import Mathlib

/-!
# A primitive-prime harmonic congruence for finite Mersenne subsums

Every finite-endpoint argument in the Erdős #257 programme ends by excluding a *finite*
Boolean Mersenne subsum equal to the rational target.  The standard tool for that is the
primitive-prime (Bang–Zsigmondy) obstruction applied to the **largest** element of the
support: a primitive prime of `2 ^ max A - 1` divides no lower Mersenne number, so it
survives into the reduced denominator.

That argument uses one element.  This module proves the statement for **every** element of
the support at once, and the price of a general element is exactly one congruence.

Fix `n ∈ A` and a prime `p` whose order of `2` is `n` (so `p ∣ 2 ^ n - 1` and `p ∣ 2 ^ m - 1`
only when `n ∣ m`).  Let `K` be the multiples of `n` inside `A`.  Then

`p` divides the denominator of `∑ m ∈ A, 1 / (2 ^ m - 1)`

**unless** the harmonic sum over `K` vanishes mod `p`:

`∑ m ∈ K, ∏ m' ∈ K.erase m, (m' / n) ≡ 0  [ZMOD p]`,

which is the numerator of `∑ m ∈ K, n / m` cleared by `∏ m ∈ K, (m / n)`.
Taking `n = max A` makes `K = {n}`, the sum is the empty product `1`, and the congruence
fails outright — recovering the terminal-spectrum statement as the degenerate case
(`terminal_case` below).

The proof is elementary: no `p`-adic valuation, no lifting-the-exponent, no multiplicity
API.  The whole content is a single explicit common denominator

`Δ = (2 ^ n - 1) * P * R`,  `P = ∏_{n ∤ m} (2 ^ m - 1)`,  `R = ∏_{n ∣ m} (2 ^ m - 1)/(2 ^ n - 1)`

for which `p ∣ Δ` while `p ∤ S * Δ`.

Quantitative corollaries (`max A ≥ (1 - o(1)) n log n` for all but `ω(v) + 1` elements of a
finite representation, and `max (A ∩ nℤ) ≥ n²` when `n` has a single proper multiple in `A`)
follow from `harmonic_numerator_lt_of_dvd` together with `p ≥ n + 1`; they are recorded in
the module docstring of the analytic companion rather than formalised here.
-/

namespace Erdos257PeriodNoncollapse
namespace PrimitivePrimeHarmonic

open Finset

/-! ## Mersenne numbers over `ℤ` -/

/-- `2 ^ m - 1`, taken in `ℤ` so that no truncated subtraction ever occurs. -/
def mersenneInt (m : ℕ) : ℤ := 2 ^ m - 1

lemma two_le_two_pow {m : ℕ} (hm : 1 ≤ m) : (2 : ℤ) ≤ 2 ^ m := by
  have h : (2 : ℕ) ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h' : ((2 ^ 1 : ℕ) : ℤ) ≤ ((2 ^ m : ℕ) : ℤ) := Int.ofNat_le.mpr h
  simpa using h'

lemma mersenneInt_pos {m : ℕ} (hm : 1 ≤ m) : 0 < mersenneInt m := by
  have := two_le_two_pow hm
  simp only [mersenneInt]
  linarith

lemma mersenneInt_ne_zero {m : ℕ} (hm : 1 ≤ m) : mersenneInt m ≠ 0 :=
  ne_of_gt (mersenneInt_pos hm)

/-- The cofactor `(2 ^ (n * k) - 1) / (2 ^ n - 1)`, defined directly as a geometric sum so
that the division is never performed. -/
def mersenneCofactor (n k : ℕ) : ℤ := ∑ i ∈ range k, ((2 : ℤ) ^ n) ^ i

lemma mersenneCofactor_mul (n k : ℕ) :
    mersenneCofactor n k * mersenneInt n = mersenneInt (n * k) := by
  simp only [mersenneCofactor, mersenneInt]
  rw [geom_sum_mul, ← pow_mul]

/-- Modulo a prime dividing `2 ^ n - 1`, the cofactor is just its index. -/
lemma mersenneCofactor_cast {n k p : ℕ} (hpn : (p : ℤ) ∣ mersenneInt n) :
    ((mersenneCofactor n k : ℤ) : ZMod p) = (k : ZMod p) := by
  have h0 : ((mersenneInt n : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hpn
  have h2 : ((2 : ZMod p)) ^ n = 1 := by
    simp only [mersenneInt] at h0
    push_cast at h0
    linear_combination h0
  simp only [mersenneCofactor]
  push_cast
  rw [Finset.sum_congr rfl (fun i _ => by rw [h2, one_pow])]
  simp

/-! ## The explicit common denominator -/

variable (A : Finset ℕ) (n : ℕ)

/-- The elements of `A` that are multiples of `n`. -/
def multiplesIn : Finset ℕ := A.filter (fun m => n ∣ m)

/-- The elements of `A` that are not multiples of `n`. -/
def nonMultiplesIn : Finset ℕ := A.filter (fun m => ¬ n ∣ m)

/-- `∏_{n ∤ m} (2 ^ m - 1)`: the part of the denominator `p` cannot see. -/
def bigP : ℤ := ∏ m ∈ nonMultiplesIn A n, mersenneInt m

/-- `∏_{n ∣ m} (2 ^ m - 1) / (2 ^ n - 1)`: the cofactor part, congruent to `∏ (m / n)`. -/
def bigR : ℤ := ∏ m ∈ multiplesIn A n, mersenneCofactor n (m / n)

/-- The explicit common denominator `Δ = (2 ^ n - 1) * P * R`.  It carries exactly one
factor of `2 ^ n - 1`, which is the whole point. -/
def commonDen : ℤ := mersenneInt n * bigP A n * bigR A n

/-- `Δ / (2 ^ m - 1)`, produced without ever dividing. -/
def quotientAt (m : ℕ) : ℤ :=
  if n ∣ m then bigP A n * ∏ m' ∈ (multiplesIn A n).erase m, mersenneCofactor n (m' / n)
  else mersenneInt n * bigR A n * ∏ m' ∈ (nonMultiplesIn A n).erase m, mersenneInt m'

/-- The numerator of `∑_{n ∣ m ∈ A} n / m`, cleared by `∏ (m / n)`.  For `n = max A` the
index set is `{n}` and this is the empty product `1`. -/
def harmonicNumerator : ℤ :=
  ∑ m ∈ multiplesIn A n, ∏ m' ∈ (multiplesIn A n).erase m, ((m' / n : ℕ) : ℤ)

variable {A n}

lemma commonDen_eq_quotientAt_mul {m : ℕ} (hm : m ∈ A) :
    commonDen A n = quotientAt A n m * mersenneInt m := by
  classical
  by_cases hdvd : n ∣ m
  · have hmem : m ∈ multiplesIn A n := by
      simp [multiplesIn, hm, hdvd]
    have hsplit : mersenneCofactor n (m / n) *
        ∏ m' ∈ (multiplesIn A n).erase m, mersenneCofactor n (m' / n) = bigR A n :=
      Finset.mul_prod_erase (multiplesIn A n) (fun m' => mersenneCofactor n (m' / n)) hmem
    have hm' : mersenneCofactor n (m / n) * mersenneInt n = mersenneInt m := by
      rw [mersenneCofactor_mul, Nat.mul_div_cancel' hdvd]
    simp only [quotientAt, commonDen, if_pos hdvd]
    calc mersenneInt n * bigP A n * bigR A n
        = mersenneInt n * bigP A n *
            (mersenneCofactor n (m / n) *
              ∏ m' ∈ (multiplesIn A n).erase m, mersenneCofactor n (m' / n)) := by
          rw [hsplit]
      _ = bigP A n * (∏ m' ∈ (multiplesIn A n).erase m, mersenneCofactor n (m' / n)) *
            (mersenneCofactor n (m / n) * mersenneInt n) := by ring
      _ = bigP A n * (∏ m' ∈ (multiplesIn A n).erase m, mersenneCofactor n (m' / n)) *
            mersenneInt m := by rw [hm']
  · have hmem : m ∈ nonMultiplesIn A n := by
      simp [nonMultiplesIn, hm, hdvd]
    have hsplit : mersenneInt m *
        ∏ m' ∈ (nonMultiplesIn A n).erase m, mersenneInt m' = bigP A n :=
      Finset.mul_prod_erase (nonMultiplesIn A n) (fun m' => mersenneInt m') hmem
    simp only [quotientAt, commonDen, if_neg hdvd]
    calc mersenneInt n * bigP A n * bigR A n
        = mersenneInt n * bigR A n *
            (mersenneInt m * ∏ m' ∈ (nonMultiplesIn A n).erase m, mersenneInt m') := by
          rw [hsplit]; ring
      _ = mersenneInt n * bigR A n *
            (∏ m' ∈ (nonMultiplesIn A n).erase m, mersenneInt m') * mersenneInt m := by ring

/-- The defining identity: the Mersenne subsum, cleared by `Δ`, is the explicit integer
`∑ Δ / (2 ^ m - 1)`. -/
lemma sum_mul_commonDen (hA1 : ∀ m ∈ A, 1 ≤ m) :
    (∑ m ∈ A, ((mersenneInt m : ℤ) : ℚ)⁻¹) * ((commonDen A n : ℤ) : ℚ)
      = ((∑ m ∈ A, quotientAt A n m : ℤ) : ℚ) := by
  classical
  rw [Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hne : ((mersenneInt m : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast mersenneInt_ne_zero (hA1 m hm)
  have h := congrArg (fun z : ℤ => (z : ℚ)) (commonDen_eq_quotientAt_mul (n := n) hm)
  push_cast at h
  field_simp
  linarith [h]

/-! ## Reduction mod `p` -/

lemma dvd_commonDen {p : ℕ} (hpn : (p : ℤ) ∣ mersenneInt n) :
    (p : ℤ) ∣ commonDen A n :=
  Dvd.dvd.mul_right (Dvd.dvd.mul_right hpn _) _

/-- Mod `p`, the cleared numerator collapses onto `P` times the harmonic numerator: every
non-multiple term carries the factor `2 ^ n - 1`, and every multiple term contributes its
cofactor product, which is congruent to `∏ (m' / n)`. -/
lemma sum_quotientAt_cast {p : ℕ} (hpn : (p : ℤ) ∣ mersenneInt n) :
    ((∑ m ∈ A, quotientAt A n m : ℤ) : ZMod p)
      = ((bigP A n : ℤ) : ZMod p) * ((harmonicNumerator A n : ℤ) : ZMod p) := by
  have hzero : ((mersenneInt n : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hpn
  have hsplit :
      ((∑ m ∈ A, quotientAt A n m : ℤ) : ZMod p)
        = (∑ m ∈ multiplesIn A n, ((quotientAt A n m : ℤ) : ZMod p))
          + ∑ m ∈ nonMultiplesIn A n, ((quotientAt A n m : ℤ) : ZMod p) := by
    simp only [multiplesIn, nonMultiplesIn]
    rw [← Finset.sum_filter_add_sum_filter_not A (fun m => n ∣ m) (quotientAt A n)]
    push_cast
    ring
  have hnon : (∑ m ∈ nonMultiplesIn A n, ((quotientAt A n m : ℤ) : ZMod p)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    have hdvd : ¬ n ∣ m := (Finset.mem_filter.1 hm).2
    simp only [quotientAt, if_neg hdvd]
    push_cast
    rw [hzero]
    ring
  have hmul : (∑ m ∈ multiplesIn A n, ((quotientAt A n m : ℤ) : ZMod p))
      = ((bigP A n : ℤ) : ZMod p) * ((harmonicNumerator A n : ℤ) : ZMod p) := by
    simp only [harmonicNumerator, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hdvd : n ∣ m := (Finset.mem_filter.1 hm).2
    simp only [quotientAt, if_pos hdvd, Int.cast_mul, Int.cast_prod, Int.cast_natCast]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro m' _
    exact mersenneCofactor_cast hpn
  rw [hsplit, hnon, hmul, add_zero]

/-- Primitivity keeps `p` out of the non-multiple part of the denominator. -/
lemma not_dvd_bigP {p : ℕ}
    (hprim : ∀ m : ℕ, (p : ℤ) ∣ mersenneInt m → n ∣ m) (hp : p.Prime) :
    ¬ (p : ℤ) ∣ bigP A n := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [bigP, Int.cast_prod]
  refine Finset.prod_ne_zero_iff.2 ?_
  intro i hi
  have hi' : i ∈ A ∧ ¬ n ∣ i := by simpa [nonMultiplesIn] using hi
  have hdvd : ¬ n ∣ i := hi'.2
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact fun h => hdvd (hprim i h)

/-! ## The theorem -/

/-- **Theorem A.**  Let `A` be a finite set of positive integers and let `p` be a prime whose
order of `2` is `n ∈ A` (`hpn` and `hprim`).  If the harmonic numerator over the multiples of
`n` inside `A` is not divisible by `p`, then `p` divides the denominator of **every**
representation of `∑ m ∈ A, 1 / (2 ^ m - 1)` as a fraction of integers. -/
theorem dvd_den_of_not_dvd_harmonicNumerator
    {A : Finset ℕ} {n p : ℕ} (hp : p.Prime)
    (hA1 : ∀ m ∈ A, 1 ≤ m)
    (hpn : (p : ℤ) ∣ mersenneInt n)
    (hprim : ∀ m : ℕ, (p : ℤ) ∣ mersenneInt m → n ∣ m)
    (hharm : ¬ (p : ℤ) ∣ harmonicNumerator A n)
    {a b : ℤ} (hb : b ≠ 0)
    (hab : (∑ m ∈ A, ((mersenneInt m : ℤ) : ℚ)⁻¹) = (a : ℚ) / (b : ℚ)) :
    (p : ℤ) ∣ b := by
  haveI : Fact p.Prime := ⟨hp⟩
  set T : ℤ := ∑ m ∈ A, quotientAt A n m with hT
  have hTnz : ((T : ℤ) : ZMod p) ≠ 0 := by
    rw [hT, sum_quotientAt_cast hpn]
    refine mul_ne_zero ?_ ?_
    · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact not_dvd_bigP hprim hp
    · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hharm
  have hTP : ¬ (p : ℤ) ∣ T := fun h =>
    hTnz ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h)
  have hkey := sum_mul_commonDen (A := A) (n := n) hA1
  rw [hab] at hkey
  have hbq : ((b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.2 hb
  have hQ : (a : ℚ) * ((commonDen A n : ℤ) : ℚ) = ((T : ℤ) : ℚ) * ((b : ℤ) : ℚ) := by
    field_simp at hkey
    linarith [hkey]
  have hZ : a * commonDen A n = T * b := by exact_mod_cast hQ
  have hdvd : (p : ℤ) ∣ T * b := by
    rw [← hZ]
    exact Dvd.dvd.mul_left (dvd_commonDen hpn) a
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.1 hdvd with h | h
  · exact absurd h hTP
  · exact h

/-- The same conclusion, read off the reduced denominator. -/
theorem dvd_rat_den_of_not_dvd_harmonicNumerator
    {A : Finset ℕ} {n p : ℕ} (hp : p.Prime)
    (hA1 : ∀ m ∈ A, 1 ≤ m)
    (hpn : (p : ℤ) ∣ mersenneInt n)
    (hprim : ∀ m : ℕ, (p : ℤ) ∣ mersenneInt m → n ∣ m)
    (hharm : ¬ (p : ℤ) ∣ harmonicNumerator A n) :
    p ∣ (∑ m ∈ A, ((mersenneInt m : ℤ) : ℚ)⁻¹).den := by
  set S : ℚ := ∑ m ∈ A, ((mersenneInt m : ℤ) : ℚ)⁻¹ with hS
  have hb : (S.den : ℤ) ≠ 0 := by exact_mod_cast S.den_nz
  have hab : S = ((S.num : ℤ) : ℚ) / (((S.den : ℤ)) : ℚ) := by
    push_cast
    exact (Rat.num_div_den S).symm
  have := dvd_den_of_not_dvd_harmonicNumerator (A := A) (n := n) hp hA1 hpn hprim hharm hb hab
  exact_mod_cast this

/-! ## The terminal case: the classical primitive-prime obstruction -/

/-- When `n` is the only multiple of itself inside `A`, the harmonic numerator is the empty
product `1`. -/
lemma harmonicNumerator_eq_one {A : Finset ℕ} {n : ℕ}
    (h : multiplesIn A n = {n}) : harmonicNumerator A n = 1 := by
  simp [harmonicNumerator, h]

/-- For the largest element of `A` the multiples set is a singleton. -/
lemma multiplesIn_max_eq_singleton {A : Finset ℕ} {n : ℕ}
    (hn : n ∈ A) (hA1 : ∀ m ∈ A, 1 ≤ m) (hmax : ∀ m ∈ A, m ≤ n) :
    multiplesIn A n = {n} := by
  ext m
  simp only [multiplesIn, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hmA, hdvd⟩
    have hpos : 0 < m := hA1 m hmA
    have hle : n ≤ m := Nat.le_of_dvd hpos hdvd
    exact le_antisymm (hmax m hmA) hle
  · rintro rfl
    exact ⟨hn, dvd_rfl⟩

/-- **Terminal-spectrum corollary.**  A primitive prime of `2 ^ (max A) - 1` divides the
reduced denominator of a finite Mersenne subsum.  This is the classical one-element
statement, recovered as the degenerate case `harmonicNumerator = 1`. -/
theorem dvd_rat_den_of_max
    {A : Finset ℕ} {n p : ℕ} (hp : p.Prime)
    (hn : n ∈ A) (hA1 : ∀ m ∈ A, 1 ≤ m) (hmax : ∀ m ∈ A, m ≤ n)
    (hpn : (p : ℤ) ∣ mersenneInt n)
    (hprim : ∀ m : ℕ, (p : ℤ) ∣ mersenneInt m → n ∣ m) :
    p ∣ (∑ m ∈ A, ((mersenneInt m : ℤ) : ℚ)⁻¹).den := by
  refine dvd_rat_den_of_not_dvd_harmonicNumerator hp hA1 hpn hprim ?_
  rw [harmonicNumerator_eq_one (multiplesIn_max_eq_singleton hn hA1 hmax)]
  intro h
  have h1 : p ∣ 1 := by exact_mod_cast h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-! ## Worked instances

Two concrete supports pin the two sides of the congruence.  Both are checked by evaluation,
so the module certifies its own sharpness.
-/

/-- `A = {2, 3}`, `n = 2`, `p = 3`: `2` has no proper multiple in `A`, the harmonic numerator
is the empty product `1`, the congruence fails, and indeed `3 ∣ 21 = den (10/21)`. -/
example : harmonicNumerator {2, 3} 2 = 1 := by decide

example : (∑ m ∈ ({2, 3} : Finset ℕ), ((mersenneInt m : ℤ) : ℚ)⁻¹) = 10 / 21 := by
  norm_num [mersenneInt, Finset.sum_pair]

/-- `A = {2, 4}`, `n = 2`, `p = 3`: now `4 = 2 * 2` is a proper multiple, the harmonic
numerator is `1 * 2 + 1 = 3 ≡ 0 (mod 3)`, the obstruction is switched off, and indeed the
value is `2/5` with `3 ∤ 5`.  This is the equality case of the quantitative corollary
`max (A ∩ nℤ) ≥ n²`, since `4 = 2²`. -/
example : harmonicNumerator {2, 4} 2 = 3 := by decide

example : (∑ m ∈ ({2, 4} : Finset ℕ), ((mersenneInt m : ℤ) : ℚ)⁻¹) = 2 / 5 := by
  norm_num [mersenneInt, Finset.sum_pair]

end PrimitivePrimeHarmonic
end Erdos257PeriodNoncollapse
