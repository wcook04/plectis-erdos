import Erdos249257.RationalDenominatorSurvival
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Adelic height obstruction for scalar localisation

This module records the exact arithmetic obstruction behind attempts to turn
2-adic depth of a rational tail into a small integer by retaining only one
odd denominator channel.  It deliberately makes no irrationality claim for
arbitrary support: its role is to prove that scalar denominator clearing
cannot discard the complementary reduced denominator.
-/

namespace Erdos249257.AdelicHeightObstruction

/-- If a scalar multiple of a reduced rational has denominator contained in
`H`, then the complementary denominator `x.den / H` divides the scalar.

This is the exact scalar-localisation tax: shrinking the displayed denominator
to a surviving channel does not discard the complement; it moves that
complement into the coefficient. -/
theorem scalarLocalization_complement_dvd
    (x : ℚ) (c : ℤ) {H : ℕ} (hH : H ∣ x.den)
    (hscaled : ((c : ℚ) * x).den ∣ H) :
    x.den / H ∣ c.natAbs := by
  have hHpos : 0 < H := Nat.pos_of_dvd_of_pos hH x.den_pos
  rw [Nat.div_dvd_iff_dvd_mul hH hHpos]
  let g := Nat.gcd (c * x.num).natAbs x.den
  have hden : x.den = ((c : ℚ) * x).den * g := by
    simpa [g] using Rat.den_mul_den_eq_den_mul_gcd (c : ℚ) x
  have hg_num : g ∣ c.natAbs * x.num.natAbs := by
    simpa [g, Int.natAbs_mul] using Nat.gcd_dvd_left (c * x.num).natAbs x.den
  have hg_den : g ∣ x.den := by
    exact Nat.gcd_dvd_right (c * x.num).natAbs x.den
  have hcop : Nat.Coprime g x.num.natAbs :=
    (x.reduced.of_dvd_right hg_den).symm
  have hg_c : g ∣ c.natAbs := (hcop.dvd_mul_right).mp hg_num
  rw [hden]
  simpa [Nat.mul_comm] using Nat.mul_dvd_mul hscaled hg_c

/-- Any prescribed divisor of the complementary denominator must already
divide the scalar coefficient.  This is the form used to compare a desired
2-adic gain with the Archimedean size paid by the localiser. -/
theorem scalarLocalization_divisor_dvd_coefficient
    (x : ℚ) (c : ℤ) {H R : ℕ} (hH : H ∣ x.den)
    (hscaled : ((c : ℚ) * x).den ∣ H)
    (hR : R ∣ x.den / H) :
    R ∣ c.natAbs :=
  hR.trans (scalarLocalization_complement_dvd x c hH hscaled)

/-- After scalar localisation, the resulting channel-cleared rational is an
integer multiple of the *original reduced numerator*.  This is the equality
form of height conservation: the omitted denominator has been transferred to
the coefficient exactly, not erased. -/
theorem scalarLocalization_integer_eq_mul_num
    (x : ℚ) (c : ℤ) {H : ℕ} (hH : H ∣ x.den)
    (hscaled : ((c : ℚ) * x).den ∣ H) :
    ∃ t : ℤ, (H : ℚ) * (c : ℚ) * x = (t : ℚ) * x.num := by
  have hKc : x.den / H ∣ c.natAbs :=
    scalarLocalization_complement_dvd x c hH hscaled
  have hKcZ : ((x.den / H : ℕ) : ℤ) ∣ c := Int.natCast_dvd.mpr hKc
  obtain ⟨t, ht⟩ := hKcZ
  refine ⟨t, ?_⟩
  have hden : H * (x.den / H) = x.den := Nat.mul_div_cancel' hH
  have hdenQ : (H : ℚ) * (x.den / H : ℕ) = x.den := by
    exact_mod_cast hden
  rw [ht, Int.cast_mul, Int.cast_natCast, ← Rat.den_mul_eq_num x, ← hdenQ]
  ring

/-- Elementary real/2-adic height conservation in an integral form.  If a
positive rational `x` is smaller than `2 / M` and `N` divides its reduced
numerator, then `N * M < 2 * x.den`.

Taking `N = 2^r` gives the denominator lower bound needed for synchronized
tails, without introducing a global prefix LCM. -/
theorem positiveRat_numDivisor_mul_lt_two_mul_den
    (x : ℚ) {N M : ℕ} (hx : 0 < x) (hM : 0 < M)
    (hNnum : N ∣ x.num.natAbs) (hlt : x < (2 : ℚ) / M) :
    N * M < 2 * x.den := by
  have hnum_pos : 0 < x.num := Rat.num_pos.mpr hx
  have hcross : (x.num : ℚ) * (M : ℚ) < 2 * (x.den : ℚ) := by
    apply (div_lt_div_iff₀ (show (0 : ℚ) < x.den by positivity)
      (show (0 : ℚ) < M by exact_mod_cast hM)).mp
    simpa [Rat.num_div_den] using hlt
  have hcrossInt : x.num * (M : ℤ) < 2 * (x.den : ℤ) := by
    exact_mod_cast hcross
  have hcrossNat : x.num.natAbs * M < 2 * x.den := by
    have hnumAbs : (x.num.natAbs : ℤ) = x.num :=
      Int.natAbs_of_nonneg hnum_pos.le
    exact_mod_cast (hnumAbs.symm ▸ hcrossInt)
  have hNle : N ≤ x.num.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hnum_pos.ne') hNnum
  exact (Nat.mul_le_mul_right M hNle).trans_lt hcrossNat

/-- The 2-power specialization used by a synchronized rational tail. -/
theorem positiveRat_twoPow_mul_lt_two_mul_den
    (x : ℚ) {r M : ℕ} (hx : 0 < x) (hM : 0 < M)
    (hpow : 2 ^ r ∣ x.num.natAbs) (hlt : x < (2 : ℚ) / M) :
    2 ^ r * M < 2 * x.den := by
  exact positiveRat_numDivisor_mul_lt_two_mul_den x hx hM hpow hlt

/-- Mersenne-denominator form of the elementary adelic height bound. -/
theorem positiveRat_mersenne_height
    (x : ℚ) {r n : ℕ} (hx : 0 < x) (hn : 0 < n)
    (hpow : 2 ^ r ∣ x.num.natAbs)
    (hlt : x < (2 : ℚ) / (2 ^ n - 1 : ℕ)) :
    2 ^ r * (2 ^ n - 1) < 2 * x.den := by
  apply positiveRat_twoPow_mul_lt_two_mul_den x hx
  · exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) hn.ne')
  · exact hpow
  · exact hlt

/-- A linear channel that kills every scalar relation is only the original
evaluation followed by multiplication by one fixed vector.  Thus a
rational-linear cyclotomic or residue channel cannot descend from equality of
scalar values while retaining independent denominator information.

The explicit preimage of `1` is the minimal surjectivity hypothesis needed
for the one-dimensional quotient argument. -/
theorem linearDescender_eq_smul_eval
    {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (ev : V →ₗ[ℚ] ℚ) (Λ : V →ₗ[ℚ] W)
    (hker : LinearMap.ker ev ≤ LinearMap.ker Λ)
    (he : ∃ e : V, ev e = 1) :
    ∃ w₀ : W, ∀ v : V, Λ v = ev v • w₀ := by
  obtain ⟨e, he⟩ := he
  refine ⟨Λ e, fun v => ?_⟩
  have hz : v - ev v • e ∈ LinearMap.ker ev := by
    rw [LinearMap.mem_ker, map_sub, map_smul, he, smul_eq_mul, mul_one, sub_self]
  have hΛz : Λ (v - ev v • e) = 0 := LinearMap.mem_ker.mp (hker hz)
  simpa [map_sub, map_smul, sub_eq_zero] using hΛz

example : (12 : ℕ) / 3 ∣ ((20 : ℤ).natAbs) := by
  exact scalarLocalization_complement_dvd (Rat.divInt 5 12) 20
    (by norm_num [Rat.divInt]) (by norm_num [Rat.divInt])

example : (8 : ℕ) * 7 < 2 * (Rat.divInt 8 63).den := by
  apply positiveRat_numDivisor_mul_lt_two_mul_den (Rat.divInt 8 63)
      (N := 8) (M := 7)
  · norm_num [Rat.divInt]
  · norm_num
  · norm_num [Rat.divInt]
  · norm_num [Rat.divInt]

#print axioms scalarLocalization_complement_dvd
#print axioms scalarLocalization_divisor_dvd_coefficient
#print axioms scalarLocalization_integer_eq_mul_num
#print axioms positiveRat_numDivisor_mul_lt_two_mul_den
#print axioms positiveRat_twoPow_mul_lt_two_mul_den
#print axioms positiveRat_mersenne_height
#print axioms linearDescender_eq_smul_eval

end Erdos249257.AdelicHeightObstruction
