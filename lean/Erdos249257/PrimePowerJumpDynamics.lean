import Erdos249257.CyclotomicProjectionOfShadow
import Mathlib.Data.Finset.NatDivisors
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-!
# Prime-power jump dynamics for the repunit Möbius numerator

This file owns the algebraic T5 recurrence.  Adjoining a new prime `p` to an
exponent `r` splits the divisor sum into its old divisors and their `p`-multiples.
The resulting identity is stated canonically with `Polynomial.expand`, so its
substitution and evaluation interfaces are inherited directly from Mathlib.

This is finite algebraic infrastructure.  It supplies no infinite
channel-avoidance statement and makes no claim that Erdős #249 is resolved.
-/

open scoped ArithmeticFunction.Moebius BigOperators Pointwise Polynomial

namespace Erdos249257.PrimePowerJumpDynamics

open RepunitMobiusNumerator
open CyclotomicProjectionOfShadow

private theorem divisors_mul_prime_split {r p : ℕ}
    (hp : p.Prime) (_hpr : ¬ p ∣ r) :
    (r * p).divisors =
      r.divisors ∪ r.divisors.image (fun d => d * p) := by
  rw [Nat.divisors_mul, hp.divisors]
  ext d
  simp only [Finset.mem_mul, Finset.mem_union, Nat.mem_divisors,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor <;> aesop

private theorem divisors_disjoint_prime_multiples {r p : ℕ}
    (_hp : p.Prime) (hpr : ¬ p ∣ r) :
    Disjoint r.divisors (r.divisors.image fun d => d * p) := by
  rw [Finset.disjoint_left]
  intro d hdr hdp
  obtain ⟨e, her, rfl⟩ := Finset.mem_image.mp hdp
  have hep_dvd_r : e * p ∣ r := Nat.dvd_of_mem_divisors hdr
  exact hpr ((dvd_mul_left p e).trans hep_dvd_r)

@[simp]
theorem expand_spacedRepunit (d q p : ℕ) :
    Polynomial.expand ℤ p (spacedRepunit d q) =
      spacedRepunit (d * p) q := by
  classical
  rw [spacedRepunit, spacedRepunit, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.expand_monomial]
  congr 1
  ac_rfl

private theorem spacedRepunit_eq_sum_X_pow (d q : ℕ) :
    spacedRepunit d q =
      ∑ j ∈ Finset.range q, (Polynomial.X : ℤ[X]) ^ (d * j) := by
  simp [spacedRepunit, Polynomial.monomial_one_right_eq_X_pow]

private theorem spacedRepunit_mul_X_pow_sub_one (d q : ℕ) :
    spacedRepunit d q * ((Polynomial.X : ℤ[X]) ^ d - 1) =
      (Polynomial.X : ℤ[X]) ^ (d * q) - 1 := by
  rw [spacedRepunit_eq_sum_X_pow]
  simp_rw [pow_mul]
  exact geom_sum_mul ((Polynomial.X : ℤ[X]) ^ d) q

private theorem X_pow_sub_one_ne_zero {d : ℕ} (hd : 0 < d) :
    (Polynomial.X : ℤ[X]) ^ d - 1 ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun P : ℤ[X] => P.coeff 0) h
  have h0d : 0 ≠ d := Nat.ne_of_lt hd
  simp [Polynomial.coeff_X_pow, h0d] at hcoeff

private theorem spacedRepunit_blocks
    {d q p : ℕ} (hd : 0 < d) :
    spacedRepunit (d * q) p * spacedRepunit d q =
      spacedRepunit d (q * p) := by
  apply mul_right_cancel₀ (X_pow_sub_one_ne_zero hd)
  calc
    (spacedRepunit (d * q) p * spacedRepunit d q) *
        ((Polynomial.X : ℤ[X]) ^ d - 1) =
      spacedRepunit (d * q) p *
        ((Polynomial.X : ℤ[X]) ^ (d * q) - 1) := by
          rw [mul_assoc, spacedRepunit_mul_X_pow_sub_one]
    _ = (Polynomial.X : ℤ[X]) ^ ((d * q) * p) - 1 :=
      spacedRepunit_mul_X_pow_sub_one (d * q) p
    _ = (Polynomial.X : ℤ[X]) ^ (d * (q * p)) - 1 := by
      rw [mul_assoc]
    _ = spacedRepunit d (q * p) *
        ((Polynomial.X : ℤ[X]) ^ d - 1) := by
          rw [spacedRepunit_mul_X_pow_sub_one]

private theorem moebius_mul_prime {d p : ℕ}
    (hp : p.Prime) (hpd : ¬ p ∣ d) :
    ArithmeticFunction.moebius (d * p) =
      -ArithmeticFunction.moebius d := by
  have hcop : d.Coprime p := ((hp.coprime_iff_not_dvd).2 hpd).symm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  ring

private theorem old_divisor_summand {r p d : ℕ}
    (hr : 0 < r) (hd : d ∣ r) :
    Polynomial.C
          (ArithmeticFunction.moebius d * ((((r * p) / d : ℕ) : ℤ))) *
        spacedRepunit d ((r * p) / d) =
      Polynomial.C (p : ℤ) * spacedRepunit r p *
        (Polynomial.C
            (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
          spacedRepunit d (r / d)) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  have hquot : (r * p) / d = (r / d) * p := by
    rw [Nat.mul_comm r p, Nat.mul_div_assoc p hd, Nat.mul_comm]
  have hblocks :
      spacedRepunit r p * spacedRepunit d (r / d) =
        spacedRepunit d ((r / d) * p) := by
    simpa [Nat.mul_div_cancel' hd] using
      (spacedRepunit_blocks (d := d) (q := r / d) (p := p) hdpos)
  rw [hquot, Nat.cast_mul]
  calc
    Polynomial.C
          (ArithmeticFunction.moebius d *
            (((r / d : ℕ) : ℤ) * (p : ℤ))) *
        spacedRepunit d ((r / d) * p) =
      Polynomial.C
          (ArithmeticFunction.moebius d *
            (((r / d : ℕ) : ℤ) * (p : ℤ))) *
        (spacedRepunit r p * spacedRepunit d (r / d)) := by
          rw [hblocks]
    _ = Polynomial.C (p : ℤ) * spacedRepunit r p *
        (Polynomial.C
            (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
          spacedRepunit d (r / d)) := by
            simp only [map_mul]
            ring

private theorem new_divisor_summand {r p d : ℕ}
    (hp : p.Prime) (hd : d ∣ r)
    (hpr : ¬ p ∣ r) :
    Polynomial.C
          (ArithmeticFunction.moebius (d * p) *
            ((((r * p) / (d * p) : ℕ) : ℤ))) *
        spacedRepunit (d * p) ((r * p) / (d * p)) =
      -Polynomial.expand ℤ p
        (Polynomial.C
            (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
          spacedRepunit d (r / d)) := by
  have hpd : ¬ p ∣ d := fun h =>
    hpr (h.trans hd)
  have hquot : (r * p) / (d * p) = r / d := by
    exact Nat.mul_div_mul_right r d hp.pos
  rw [hquot, moebius_mul_prime hp hpd]
  simp only [map_mul, map_neg, Polynomial.expand_C, expand_spacedRepunit]
  ring

/-- T5 in its strongest natural algebraic form: adjoining a prime not already
dividing `r` produces an old-divisor block minus the `p`-fold expansion.  No
squarefree hypothesis is needed for this divisor-sum identity. -/
theorem mobiusNumeratorPolynomial_mul_prime
    {r p : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) :
    mobiusNumeratorPolynomial (r * p) =
      Polynomial.C (p : ℤ) * spacedRepunit r p *
          mobiusNumeratorPolynomial r -
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) := by
  classical
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    exact hpr (dvd_zero p)
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  let F : ℕ → ℕ → ℤ[X] := fun n d =>
    Polynomial.C
        (ArithmeticFunction.moebius d * (((n / d : ℕ) : ℤ))) *
      spacedRepunit d (n / d)
  unfold mobiusNumeratorPolynomial
  change (∑ d ∈ (r * p).divisors, F (r * p) d) =
    Polynomial.C (p : ℤ) * spacedRepunit r p *
        (∑ d ∈ r.divisors, F r d) -
      Polynomial.expand ℤ p (∑ d ∈ r.divisors, F r d)
  rw [divisors_mul_prime_split hp hpr,
    Finset.sum_union (divisors_disjoint_prime_multiples hp hpr)]
  rw [Finset.sum_image]
  · calc
      (∑ d ∈ r.divisors, F (r * p) d) +
          ∑ d ∈ r.divisors, F (r * p) (d * p) =
        (∑ d ∈ r.divisors,
            Polynomial.C (p : ℤ) * spacedRepunit r p * F r d) +
          ∑ d ∈ r.divisors,
            -Polynomial.expand ℤ p (F r d) := by
              congr 1
              · apply Finset.sum_congr rfl
                intro d hd
                exact old_divisor_summand hr
                  (Nat.dvd_of_mem_divisors hd)
              · apply Finset.sum_congr rfl
                intro d hd
                exact new_divisor_summand hp
                  (Nat.dvd_of_mem_divisors hd) hpr
      _ = Polynomial.C (p : ℤ) * spacedRepunit r p *
            (∑ d ∈ r.divisors, F r d) -
          Polynomial.expand ℤ p (∑ d ∈ r.divisors, F r d) := by
            rw [← Finset.mul_sum]
            simp only [map_sum, Finset.sum_neg_distrib]
            ring
  · intro d₁ hd₁ d₂ hd₂ heq
    exact Nat.eq_of_mul_eq_mul_right hp.pos heq

/-- Development-facing commuted orientation of the T5 recurrence. -/
theorem mobiusNumeratorPolynomial_prime_mul
    {p r : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) :
    mobiusNumeratorPolynomial (p * r) =
      Polynomial.C (p : ℤ) * spacedRepunit r p *
          mobiusNumeratorPolynomial r -
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) := by
  simpa [Nat.mul_comm] using
    mobiusNumeratorPolynomial_mul_prime hp hpr

/-- Compatibility wrapper exposing substitution as polynomial composition. -/
theorem mobiusNumeratorPolynomial_mul_prime_comp
    {r p : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) :
    mobiusNumeratorPolynomial (r * p) =
      Polynomial.C (p : ℤ) * spacedRepunit r p *
          mobiusNumeratorPolynomial r -
        (mobiusNumeratorPolynomial r).comp (Polynomial.X ^ p) := by
  simpa [Polynomial.expand_eq_comp_X_pow] using
    mobiusNumeratorPolynomial_mul_prime hp hpr

/-- Evaluation form of T5: expansion at `x` is evaluation at `x ^ p`. -/
theorem mobiusNumeratorPolynomial_mul_prime_eval
    {r p : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (x : ℤ) :
    (mobiusNumeratorPolynomial (r * p)).eval x =
      (p : ℤ) * (spacedRepunit r p).eval x *
          (mobiusNumeratorPolynomial r).eval x -
        (mobiusNumeratorPolynomial r).eval (x ^ p) := by
  rw [mobiusNumeratorPolynomial_mul_prime hp hpr]
  simp

/-! ## Old and new cyclotomic fibres

The recurrence preserves more than the ambient polynomial identity.  A new
`m * p` fibre kills the geometric old-divisor block, while an old `m` fibre
sees multiplication by `p ^ 2 - 1`.  These are finite congruence interfaces;
they do not assert that any foreign defect misses the displayed target. -/

private theorem prime_not_dvd_divisor
    {r p m : ℕ} (hpr : ¬ p ∣ r) (hm : m ∣ r) : ¬ p ∣ m := by
  exact fun hpm => hpr (hpm.trans hm)

private theorem polynomial_dvd_sub {a b c : ℤ[X]}
    (hb : a ∣ b) (hc : a ∣ c) : a ∣ b - c := by
  obtain ⟨u, rfl⟩ := hb
  obtain ⟨v, rfl⟩ := hc
  exact ⟨u - v, by ring⟩

private theorem cyclotomic_dvd_expand_sub_constant
    {r p m : ℕ} (hr : Squarefree r) (hp : p.Prime)
    (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) -
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m)) := by
  let a : ℤ := ArithmeticFunction.moebius m * jordanTotientTwo (r / m)
  have hbase : Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial r - Polynomial.C a :=
    cyclotomic_dvd_mobiusNumeratorPolynomial_sub hr hm
  have hexpand : Polynomial.expand ℤ p (Polynomial.cyclotomic m ℤ) ∣
      Polynomial.expand ℤ p
        (mobiusNumeratorPolynomial r - Polynomial.C a) :=
    (Polynomial.expand ℤ p).map_dvd hbase
  have hfactor : Polynomial.cyclotomic m ℤ ∣
      Polynomial.expand ℤ p (Polynomial.cyclotomic m ℤ) := by
    rw [Polynomial.cyclotomic_expand_eq_cyclotomic_mul hp
      (prime_not_dvd_divisor hpr hm) ℤ]
    exact dvd_mul_left _ _
  exact hfactor.trans <| by
    simpa [a] using hexpand

/-- In a genuinely new `m * p` fibre, the geometric old-divisor block
vanishes, so the jump numerator is the negative `p`-fold expansion. -/
theorem cyclotomic_dvd_primeJump_new_fibre
    {r p m : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic (m * p) ℤ ∣
      mobiusNumeratorPolynomial (r * p) +
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) := by
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    exact hpr (dvd_zero p)
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  have hnewNotOld : ¬ m * p ∣ r := by
    intro h
    exact hpr ((dvd_mul_left p m).trans h)
  have hgeom : Polynomial.cyclotomic (m * p) ℤ ∣ spacedRepunit r p := by
    simpa [Nat.mul_div_cancel_left p hr] using
      (cyclotomic_dvd_spacedRepunit_of_not_dvd
        (r := r * p) (d := r) (m := m * p)
        (Nat.mul_pos hr hp.pos) (dvd_mul_right r p)
        (Nat.mul_dvd_mul_right hm p) hnewNotOld)
  rw [mobiusNumeratorPolynomial_mul_prime hp hpr]
  ring_nf
  obtain ⟨q, hq⟩ := hgeom
  refine ⟨Polynomial.C (p : ℤ) * q * mobiusNumeratorPolynomial r, ?_⟩
  rw [hq]
  ring

/-- On an old `m` fibre, adjoining the new prime scales the old numerator by
`p ^ 2 - 1`.  Squarefreeness is needed only to invoke the T2 constant-fibre
theorem, not for the underlying T5 recurrence. -/
theorem cyclotomic_dvd_primeJump_old_fibre
    {r p m : ℕ} (hr : Squarefree r) (hp : p.Prime)
    (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial (r * p) -
        Polynomial.C ((p : ℤ) ^ 2 - 1) *
          mobiusNumeratorPolynomial r := by
  have hgeom : Polynomial.cyclotomic m ℤ ∣
      spacedRepunit r p - Polynomial.C (p : ℤ) := by
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
    simpa [Nat.mul_div_cancel_left p hrpos] using
      (cyclotomic_dvd_spacedRepunit_sub_C_of_dvd
        (r := r * p) (d := r) (m := m) hm)
  have hexpand : Polynomial.cyclotomic m ℤ ∣
      Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) -
        mobiusNumeratorPolynomial r := by
    let a : ℤ := ArithmeticFunction.moebius m * jordanTotientTwo (r / m)
    have hnew := cyclotomic_dvd_expand_sub_constant hr hp hpr hm
    have hold := cyclotomic_dvd_mobiusNumeratorPolynomial_sub hr hm
    have hsub := polynomial_dvd_sub hnew hold
    simpa [a] using hsub
  rw [mobiusNumeratorPolynomial_mul_prime hp hpr]
  have hfirst : Polynomial.cyclotomic m ℤ ∣
      Polynomial.C (p : ℤ) *
        (spacedRepunit r p - Polynomial.C (p : ℤ)) *
          mobiusNumeratorPolynomial r :=
    by
      obtain ⟨q, hq⟩ := hgeom
      refine ⟨Polynomial.C (p : ℤ) * q * mobiusNumeratorPolynomial r, ?_⟩
      rw [hq]
      ring
  have htotal := polynomial_dvd_sub hfirst hexpand
  convert htotal using 1
  simp only [map_sub, map_pow, map_one]
  ring

/-- The new fibre carries the negated old T2 constant explicitly. -/
theorem cyclotomic_dvd_primeJump_new_fibre_constant
    {r p m : ℕ} (hr : Squarefree r) (hp : p.Prime)
    (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic (m * p) ℤ ∣
      mobiusNumeratorPolynomial (r * p) +
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m)) := by
  let a : ℤ := ArithmeticFunction.moebius m * jordanTotientTwo (r / m)
  have hjump := cyclotomic_dvd_primeJump_new_fibre hp hpr hm
  have hbase : Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial r - Polynomial.C a :=
    cyclotomic_dvd_mobiusNumeratorPolynomial_sub hr hm
  have hexpand : Polynomial.expand ℤ p (Polynomial.cyclotomic m ℤ) ∣
      Polynomial.expand ℤ p
        (mobiusNumeratorPolynomial r - Polynomial.C a) :=
    (Polynomial.expand ℤ p).map_dvd hbase
  have hnew : Polynomial.cyclotomic (m * p) ℤ ∣
      Polynomial.expand ℤ p (mobiusNumeratorPolynomial r) -
        Polynomial.C a := by
    have hpnotm := prime_not_dvd_divisor hpr hm
    have hfactor : Polynomial.cyclotomic (m * p) ℤ ∣
        Polynomial.expand ℤ p (Polynomial.cyclotomic m ℤ) := by
      rw [Polynomial.cyclotomic_expand_eq_cyclotomic_mul hp hpnotm ℤ]
      exact dvd_mul_right _ _
    exact hfactor.trans <| by simpa [a] using hexpand
  have htotal := polynomial_dvd_sub hjump hnew
  convert htotal using 1
  ring

/-! Kernel-checked recurrence fixtures pin the corrected sign, multiplication
orientation, and the fact that the source exponent need not be squarefree. -/

/-- Smallest explicit sign fixture. -/
theorem mobiusNumeratorPolynomial_two_fixture :
    mobiusNumeratorPolynomial 2 =
      1 + 2 * (Polynomial.X : ℤ[X]) := by
  rw [show 2 = 1 * 2 by norm_num,
    mobiusNumeratorPolynomial_mul_prime (by norm_num) (by norm_num)]
  simp [mobiusNumeratorPolynomial, spacedRepunit,
    Finset.sum_range_succ, Polynomial.monomial_one_right_eq_X_pow]
  ring

/-- First nontrivial squarefree new-prime jump, expanded coefficientwise. -/
theorem mobiusNumeratorPolynomial_six_fixture :
    mobiusNumeratorPolynomial 6 =
      2 + 6 * Polynomial.X + 3 * Polynomial.X ^ 2 +
        4 * Polynomial.X ^ 3 + 3 * Polynomial.X ^ 4 +
        6 * Polynomial.X ^ 5 := by
  rw [show 6 = 2 * 3 by norm_num,
    mobiusNumeratorPolynomial_mul_prime (by norm_num) (by norm_num),
    mobiusNumeratorPolynomial_two_fixture]
  simp [spacedRepunit, Finset.sum_range_succ,
    Polynomial.monomial_one_right_eq_X_pow,
    Polynomial.expand_eq_comp_X_pow]
  ring

/-- Explicit `Φ₆` quotient for the first new fibre. -/
theorem primeJump_new_fibre_six_factorization :
    mobiusNumeratorPolynomial 6 +
        Polynomial.expand ℤ 3 (mobiusNumeratorPolynomial 2) =
      Polynomial.cyclotomic 6 ℤ *
        (6 * Polynomial.X ^ 3 + 9 * Polynomial.X ^ 2 +
          9 * Polynomial.X + 3) := by
  rw [mobiusNumeratorPolynomial_six_fixture,
    mobiusNumeratorPolynomial_two_fixture]
  simp [Polynomial.cyclotomic_six, Polynomial.expand_eq_comp_X_pow]
  ring

/-- Explicit `Φ₂` quotient for the corresponding old fibre. -/
theorem primeJump_old_fibre_two_factorization :
    mobiusNumeratorPolynomial 6 -
        Polynomial.C (((3 : ℤ) ^ 2) - 1) * mobiusNumeratorPolynomial 2 =
      Polynomial.cyclotomic 2 ℤ *
        (6 * Polynomial.X ^ 4 - 3 * Polynomial.X ^ 3 +
          7 * Polynomial.X ^ 2 - 4 * Polynomial.X - 6) := by
  rw [mobiusNumeratorPolynomial_six_fixture,
    mobiusNumeratorPolynomial_two_fixture]
  simp
  ring

/-- The `r = 4`, `p = 3` fixture prevents accidental regression to T1's
squarefree source boundary. -/
example : mobiusNumeratorPolynomial 12 =
    Polynomial.C (3 : ℤ) * spacedRepunit 4 3 *
        mobiusNumeratorPolynomial 4 -
      Polynomial.expand ℤ 3 (mobiusNumeratorPolynomial 4) := by
  simpa using mobiusNumeratorPolynomial_mul_prime
    (r := 4) (p := 3) (by norm_num) (by norm_num)

#print axioms mobiusNumeratorPolynomial_mul_prime
#print axioms mobiusNumeratorPolynomial_prime_mul
#print axioms mobiusNumeratorPolynomial_mul_prime_comp
#print axioms mobiusNumeratorPolynomial_mul_prime_eval
#print axioms cyclotomic_dvd_primeJump_new_fibre
#print axioms cyclotomic_dvd_primeJump_old_fibre
#print axioms cyclotomic_dvd_primeJump_new_fibre_constant
#print axioms mobiusNumeratorPolynomial_two_fixture
#print axioms mobiusNumeratorPolynomial_six_fixture
#print axioms primeJump_new_fibre_six_factorization
#print axioms primeJump_old_fibre_two_factorization

end Erdos249257.PrimePowerJumpDynamics
