import Erdos249257.MersenneLambertLadder
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

/-!
# Primitive determinant index obstruction for Erdős #249

Let `A = φ * μ` be `MersenneLambertLadder.primWeight`.  The normalized
Euler coordinate of the global primitive determinant is `A(n) / n`.  This
file records the finite arithmetic obstruction that is independent of any
analytic realization of the determinant.

If one positive integer `D` clears the normalized coordinates through order
`N`, then every odd prime `p ≤ N` divides `D`, every odd prime with
`p² ≤ N` contributes a second factor of `p`, and `4 ∣ D` once `N ≥ 4`.
The `twoTierPrimorial` theorem packages these local obligations into one
finite lcm.  Consequently no fixed positive index clears all coordinates.

This is a no-lift theorem for the integral Euler/Witt-coordinate category.
It is not the more general Dieudonné--Dwork theorem for arbitrary integral
power-series jets, and it does not prove the irrationality of the #249
constant.
-/

namespace PrimitiveDeterminantLift

open MersenneLambertLadder

/-- The rational primitive Euler/Witt coordinate `A(n) / n`. -/
def primEulerCoord (n : ℕ) : ℚ :=
  ((primWeight n : ℤ) : ℚ) / (n : ℚ)

/-- A common positive index `D` clears every primitive Euler coordinate up to
the jet horizon `N`. -/
def IntegralPrimitiveEulerJet (N D : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ N → ∃ z : ℤ, (D : ℚ) * primEulerCoord n = (z : ℚ)

/-- Clearing `A(n) / n` is equivalent to the elementary divisibility
condition `n ∣ D A(n)`. -/
theorem integral_primEulerCoord_iff_dvd {n D : ℕ} (hn : n ≠ 0) :
    (∃ z : ℤ, (D : ℚ) * primEulerCoord n = (z : ℚ)) ↔
      (n : ℤ) ∣ (D : ℤ) * primWeight n := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hz' : (D : ℚ) * (primWeight n : ℚ) = (n : ℚ) * (z : ℚ) := by
      rw [primEulerCoord, div_eq_mul_inv] at hz
      calc
        (D : ℚ) * (primWeight n : ℚ) =
            ((D : ℚ) * ((primWeight n : ℚ) * (n : ℚ)⁻¹)) * (n : ℚ) := by
              field_simp
        _ = (z : ℚ) * (n : ℚ) := by rw [hz]
        _ = (n : ℚ) * (z : ℚ) := mul_comm _ _
    exact_mod_cast hz'
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hz' : (D : ℚ) * (primWeight n : ℚ) = (n : ℚ) * (z : ℚ) := by
      exact_mod_cast hz
    rw [primEulerCoord, div_eq_mul_inv]
    calc
      (D : ℚ) * ((primWeight n : ℚ) * (n : ℚ)⁻¹) =
          ((D : ℚ) * (primWeight n : ℚ)) * (n : ℚ)⁻¹ := by ring
      _ = ((n : ℚ) * (z : ℚ)) * (n : ℚ)⁻¹ := by rw [hz']
      _ = (z : ℚ) := by field_simp

/-- Prime-square value `A(p²) = (p-1)²`. -/
theorem primWeight_apply_prime_sq {p : ℕ} (hp : p.Prime) :
    primWeight (p ^ 2) = ((p - 1 : ℕ) : ℤ) ^ 2 := by
  rw [primWeight_apply_prime_pow hp (by norm_num : (2 : ℕ) ≠ 0),
    Nat.totient_prime_pow hp (by norm_num : 0 < (2 : ℕ))]
  norm_num [Nat.totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_le
  push_cast [Nat.cast_sub hp1]
  ring

/-- The prime `p` does not divide its prime-square primitive numerator. -/
theorem prime_not_dvd_primWeight_prime_sq {p : ℕ} (hp : p.Prime) :
    ¬ (p : ℤ) ∣ primWeight (p ^ 2) := by
  rw [primWeight_apply_prime_sq hp, pow_two]
  intro h
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpInt.dvd_or_dvd h with h | h
  · have hcast : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by
      rw [Int.ofNat_sub hp.one_le]
      norm_num
    rw [← hcast] at h
    exact hpInt.not_dvd_one (by simpa using ((dvd_refl (p : ℤ)).sub h))
  · have hcast : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by
      rw [Int.ofNat_sub hp.one_le]
      norm_num
    rw [← hcast] at h
    exact hpInt.not_dvd_one (by simpa using ((dvd_refl (p : ℤ)).sub h))

/-- Every odd prime at or below the jet horizon divides the common index. -/
theorem oddPrime_dvd_index_of_integral_jet
    {N D p : ℕ} (hjet : IntegralPrimitiveEulerJet N D)
    (hp : p.Prime) (hpodd : p ≠ 2) (hpN : p ≤ N) :
    p ∣ D := by
  have hcoord := hjet p hp.pos hpN
  have hdiv : (p : ℤ) ∣ (D : ℤ) * primWeight p :=
    (integral_primEulerCoord_iff_dvd hp.ne_zero).mp hcoord
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hDInt : (p : ℤ) ∣ (D : ℤ) :=
    (hpInt.dvd_or_dvd hdiv).resolve_right (primWeight_prime_dold_defect hp hpodd)
  exact Int.natCast_dvd_natCast.mp hDInt

/-- A prime whose square lies below the jet horizon contributes two copies to
the common index. -/
theorem primeSq_dvd_index_of_integral_jet
    {N D p : ℕ} (hjet : IntegralPrimitiveEulerJet N D)
    (hp : p.Prime) (hpSqN : p ^ 2 ≤ N) :
    p ^ 2 ∣ D := by
  have hpSqPos : 0 < p ^ 2 := pow_pos hp.pos _
  have hcoord := hjet (p ^ 2) hpSqPos hpSqN
  have hdiv : ((p ^ 2 : ℕ) : ℤ) ∣ (D : ℤ) * primWeight (p ^ 2) :=
    (integral_primEulerCoord_iff_dvd hpSqPos.ne').mp hcoord
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdiv' : (p : ℤ) ^ 2 ∣ (D : ℤ) * primWeight (p ^ 2) := by
    exact_mod_cast hdiv
  have hDInt : (p : ℤ) ^ 2 ∣ (D : ℤ) :=
    hpInt.pow_dvd_of_dvd_mul_right 2 (prime_not_dvd_primWeight_prime_sq hp) hdiv'
  exact_mod_cast hDInt

/-- The exceptional prime `2` first contributes at the coordinate `n = 4`. -/
theorem four_dvd_index_of_integral_jet
    {N D : ℕ} (hjet : IntegralPrimitiveEulerJet N D) (hN : 4 ≤ N) :
    4 ∣ D := by
  simpa using primeSq_dvd_index_of_integral_jet hjet Nat.prime_two hN

/-- The local index required at one prime through horizon `N`.  The prime `2`
contributes only its square, while an odd prime contributes once at `p` and a
second time at `p²`. -/
def localPrimitiveIndex (N p : ℕ) : ℕ :=
  if hp : p.Prime then
    if p = 2 then
      if 4 ≤ N then 4 else 1
    else if p ^ 2 ≤ N then p ^ 2 else p
  else 1

/-- Lcm form of the two-tier primorial index through horizon `N`. -/
def twoTierPrimorial (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).lcm (localPrimitiveIndex N)

/-- The complete finite-jet obstruction: the two-tier primorial divides every
common index clearing all primitive Euler coordinates through `N`. -/
theorem twoTierPrimorial_dvd_of_integral_jet
    {N D : ℕ} (hN : 4 ≤ N) (hjet : IntegralPrimitiveEulerJet N D) :
    twoTierPrimorial N ∣ D := by
  rw [twoTierPrimorial, Finset.lcm_dvd_iff]
  intro p hpRange
  have hpN : p ≤ N := by
    have hpLt : p < N + 1 := Finset.mem_range.mp hpRange
    omega
  by_cases hp : p.Prime
  · by_cases hpTwo : p = 2
    · subst p
      simpa [localPrimitiveIndex, hN] using
        (four_dvd_index_of_integral_jet hjet hN)
    · by_cases hpSq : p ^ 2 ≤ N
      · simpa [localPrimitiveIndex, hp, hpTwo, hpSq] using
          (primeSq_dvd_index_of_integral_jet hjet hp hpSq)
      · simpa [localPrimitiveIndex, hp, hpTwo, hpSq] using
          (oddPrime_dvd_index_of_integral_jet hjet hp hpTwo hpN)
  · simp [localPrimitiveIndex, hp]

/-- No fixed positive integer clears all normalized primitive coordinates. -/
theorem no_fixed_integral_primitive_euler_index (D : ℕ) (hD : 0 < D) :
    ¬ ∀ n : ℕ, 0 < n → ∃ z : ℤ, (D : ℚ) * primEulerCoord n = (z : ℚ) := by
  intro hall
  obtain ⟨p, hpLower, hp⟩ := Nat.exists_infinite_primes (max (D + 1) 3)
  have hpD : D + 1 ≤ p := (le_max_left _ _).trans hpLower
  have hpThree : 3 ≤ p := (le_max_right _ _).trans hpLower
  have hpodd : p ≠ 2 := by omega
  have hjet : IntegralPrimitiveEulerJet p D := by
    intro n hn _
    exact hall n hn
  have hpdvd : p ∣ D := oddPrime_dvd_index_of_integral_jet hjet hp hpodd le_rfl
  have hpLeD : p ≤ D := Nat.le_of_dvd hD hpdvd
  omega

example : twoTierPrimorial 10 = 1260 := by decide

#print axioms integral_primEulerCoord_iff_dvd
#print axioms primWeight_apply_prime_sq
#print axioms oddPrime_dvd_index_of_integral_jet
#print axioms primeSq_dvd_index_of_integral_jet
#print axioms four_dvd_index_of_integral_jet
#print axioms twoTierPrimorial_dvd_of_integral_jet
#print axioms no_fixed_integral_primitive_euler_index

end PrimitiveDeterminantLift
