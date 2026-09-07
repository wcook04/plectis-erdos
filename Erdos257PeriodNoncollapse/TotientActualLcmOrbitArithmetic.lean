import Erdos257PeriodNoncollapse.TotientActualLcmOrbitNonintegrality
import Erdos257PeriodNoncollapse.DiagonalFreshLossBridge

/-!
# Coefficient arithmetic for the actual LCM orbit

This module refines the finite-window side of the exact actual-LCM orbit
frontier.  The existing clean-divisor identity
`deltaTotient_periodLcm_ray_split` factors a ray letter only when every prime
of the offset remains in the quotient `H / j`.  Here the missing overlap is
kept exactly.

For `x > 0`, the standard identity

`phi(gcd(j,x)) * phi(j*x) = phi(j) * phi(x) * gcd(j,x)`

shows that `phi(j*x)` is `phi(x)` times an explicit integral overlap factor.
Consequently every divisor-offset letter on the actual diagonal is reduced
to totients at the smaller quotient scale `H / j`, with no cleanliness
hypothesis.  In a window shorter than `2*t`, every remaining nondivisor
offset is a bare prime power by `eq_prime_pow_of_not_dvd_periodLcm`.

The final supply is intentionally conditional.  It is a strictly stronger
short-window arithmetic producer for the landed actual-orbit endpoint, not a
claim that the cofinal residue band has been proved.
-/

namespace Erdos257PeriodNoncollapse
namespace DiagonalFreshLossBridge
namespace PowerTwoOddWindowAffine

open Finset
open TotientTailPeriodKiller

/-- The integral correction for the primes shared by `j` and `x` in the
totient of the product `j*x`. -/
def totientOverlapFactor (j x : ℕ) : ℕ :=
  (Nat.totient j / Nat.totient (Nat.gcd j x)) * Nat.gcd j x

/-- Exact product formula with all common-prime overlap retained in an
integral factor.  This is the non-coprime extension of `Nat.totient_mul`
needed by divisor offsets which exhaust a prime power of an LCM height. -/
theorem totient_mul_eq_overlapFactor_mul (j x : ℕ) (hx : 0 < x) :
    Nat.totient (j * x) =
      totientOverlapFactor j x * Nat.totient x := by
  let g := Nat.gcd j x
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right j hx
  have hphigpos : 0 < Nat.totient g := Nat.totient_pos.mpr hgpos
  have hdiv : Nat.totient g ∣ Nat.totient j :=
    Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left j x)
  have hbase := Nat.totient_gcd_mul_totient_mul j x
  have hfactor :
      Nat.totient g *
          (((Nat.totient j / Nat.totient g) * g) * Nat.totient x) =
        Nat.totient j * Nat.totient x * g := by
    calc
      Nat.totient g *
          (((Nat.totient j / Nat.totient g) * g) * Nat.totient x) =
          (Nat.totient g * (Nat.totient j / Nat.totient g)) *
            Nat.totient x * g := by ring
      _ = Nat.totient j * Nat.totient x * g := by
        rw [Nat.mul_div_cancel' hdiv]
  apply Nat.eq_of_mul_eq_mul_left hphigpos
  change Nat.totient g * Nat.totient (j * x) =
    Nat.totient g * (totientOverlapFactor j x * Nat.totient x)
  rw [hbase]
  simpa [totientOverlapFactor, g] using hfactor.symm

/-! ### The relative Euler product

The overlap factor is integral and convenient for exact descent, but its
Euler-product meaning is more transparent after dividing by `phi(j)`: the
only density losses which remain are primes of `x` which were not already
present in `j`.  This is the coordinate needed for the rough endpoint
estimates below.
-/

/-- Prime factors introduced by `x`, rather than already present in `j`. -/
def relativePrimeFactors (j x : ℕ) : Finset ℕ :=
  x.primeFactors \ j.primeFactors

/-- Prime factors of a product split into the old factors and the genuinely
new factors of the second input. -/
theorem primeFactors_mul_eq_union_relative
    {j x : ℕ} (hj : 0 < j) (hx : 0 < x) :
    (j * x).primeFactors =
      j.primeFactors ∪ relativePrimeFactors j x := by
  rw [Nat.primeFactors_mul hj.ne' hx.ne']
  unfold relativePrimeFactors
  ext p
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- Relative Euler product in multiplication form.  Equivalently,

`phi(j*x) / phi(j) = x * ∏_{p|x, p∤j} (1 - 1/p)`.

The multiplication form avoids a denominator in downstream ordered-field
arguments while retaining exactly the same information. -/
theorem totient_mul_eq_totient_mul_relativeEulerProduct
    (j x : ℕ) (hj : 0 < j) (hx : 0 < x) :
    (Nat.totient (j * x) : ℚ) =
      (Nat.totient j : ℚ) * (x : ℚ) *
        ∏ p ∈ relativePrimeFactors j x, (1 - (p : ℚ)⁻¹) := by
  rw [Nat.totient_eq_mul_prod_factors,
    Nat.totient_eq_mul_prod_factors,
    primeFactors_mul_eq_union_relative hj hx]
  unfold relativePrimeFactors
  rw [Finset.prod_union Finset.disjoint_sdiff]
  push_cast
  ring

/-- Quotient orientation of the relative Euler product. -/
theorem totient_mul_div_totient_eq_relativeEulerProduct
    (j x : ℕ) (hj : 0 < j) (hx : 0 < x) :
    (Nat.totient (j * x) : ℚ) / Nat.totient j =
      (x : ℚ) *
        ∏ p ∈ relativePrimeFactors j x, (1 - (p : ℚ)⁻¹) := by
  have hphi : (Nat.totient j : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hj))
  rw [totient_mul_eq_totient_mul_relativeEulerProduct j x hj hx]
  field_simp

/-- Every genuinely new prime in a divisor-ray endpoint lies above the LCM
cutoff.  Small primes may occur in the endpoint only when they were already
present in the outer divisor `j`, and the relative Euler product removes
exactly those factors. -/
theorem relativePrimeFactors_lcmDivisor_endpoint_gt
    {t j q r : ℕ} (hj : j ∣ periodLcm t)
    (hrmem : r ∈ relativePrimeFactors j (q * (periodLcm t / j) + 1)) :
    t < r := by
  let H := periodLcm t
  let A := H / j
  have hHPos : 0 < H := by
    dsimp [H]
    exact periodLcm_pos t
  have hjPos : 0 < j := Nat.pos_of_dvd_of_pos hj hHPos
  have hH : j * A = H := by
    simpa [A, H] using Nat.mul_div_cancel' hj
  change r ∈
    (q * (periodLcm t / j) + 1).primeFactors \ j.primeFactors at hrmem
  obtain ⟨hrxMem, hrjNotMem⟩ := Finset.mem_sdiff.mp hrmem
  have hrPrime : Nat.Prime r := Nat.prime_of_mem_primeFactors hrxMem
  have hrx : r ∣ q * A + 1 := by
    simpa [A, H] using Nat.dvd_of_mem_primeFactors hrxMem
  have hrNotJ : ¬r ∣ j := by
    intro hrj
    exact hrjNotMem (hrPrime.mem_primeFactors hrj hjPos.ne')
  by_contra hnot
  have hrt : r ≤ t := Nat.le_of_not_gt hnot
  have hrH : r ∣ H := by
    dsimp [H]
    exact dvd_periodLcm hrPrime.pos hrt
  have hrJA : r ∣ j * A := by simpa [hH] using hrH
  rcases hrPrime.dvd_mul.mp hrJA with hrj | hrA
  · exact hrNotJ hrj
  · have hrqA : r ∣ q * A := dvd_mul_of_dvd_right hrA q
    have hrOne : r ∣ 1 := (Nat.dvd_add_right hrqA).mp hrx
    exact absurd (Nat.dvd_one.mp hrOne) hrPrime.one_lt.ne'

/-- In the coprime case the overlap factor is the familiar outer factor
`phi(j)`. -/
theorem totientOverlapFactor_eq_totient_of_coprime
    {j x : ℕ} (hcop : Nat.Coprime j x) :
    totientOverlapFactor j x = Nat.totient j := by
  simp [totientOverlapFactor, hcop.gcd_eq_one]

/-- Common-prime overlap can only enlarge the outer totient factor. -/
theorem totient_le_totientOverlapFactor (j x : ℕ) (hx : 0 < x) :
    Nat.totient j ≤ totientOverlapFactor j x := by
  have hmul := Nat.totient_super_multiplicative j x
  rw [totient_mul_eq_overlapFactor_mul j x hx] at hmul
  exact Nat.le_of_mul_le_mul_right hmul (Nat.totient_pos.mpr hx)

/-- The nonnegative amount by which common-prime overlap enlarges the clean
outer factor. -/
def totientOverlapExcess (j x : ℕ) : ℕ :=
  totientOverlapFactor j x - Nat.totient j

theorem totientOverlapFactor_eq_totient_add_excess
    (j x : ℕ) (hx : 0 < x) :
    totientOverlapFactor j x =
      Nat.totient j + totientOverlapExcess j x := by
  exact (Nat.add_sub_of_le (totient_le_totientOverlapFactor j x hx)).symm

/-- A nonzero overlap excess on an LCM quotient ray is supported by a prime
which is present in the offset but exhausted from the quotient. -/
theorem exists_saturated_prime_of_overlapExcess_ne_zero
    {H j q : ℕ}
    (hne : totientOverlapExcess j (q * (H / j) + 1) ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ j ∧ ¬p ∣ H / j := by
  let x := q * (H / j) + 1
  have hnotcop : ¬Nat.Coprime j x := by
    intro hcop
    apply hne
    unfold totientOverlapExcess
    rw [totientOverlapFactor_eq_totient_of_coprime hcop]
    simp
  rw [Nat.coprime_iff_gcd_eq_one] at hnotcop
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hnotcop
  have hpj : p ∣ j := hpdvd.trans (Nat.gcd_dvd_left j x)
  have hpx : p ∣ x := hpdvd.trans (Nat.gcd_dvd_right j x)
  refine ⟨p, hp, hpj, ?_⟩
  intro hpa
  have hpqa : p ∣ q * (H / j) := hpa.mul_left q
  have hp1 : p ∣ 1 := by
    dsimp [x] at hpx
    exact (Nat.dvd_add_right hpqa).mp hpx
  exact absurd (Nat.dvd_one.mp hp1) hp.one_lt.ne'

/-- The quotient-scale letter attached to a divisor offset `j | H` on the
actual diagonal.  Its two overlap factors record exactly which saturated
prime powers of `j` reappear in `H/j + 1` and `2*(H/j) + 1`. -/
def lcmDivisorRayLetter (H j : ℕ) : ℤ :=
  let a := H / j
  ((totientOverlapFactor j (2 * a + 1) *
      Nat.totient (2 * a + 1) : ℕ) : ℤ) -
    ((totientOverlapFactor j (a + 1) *
      Nat.totient (a + 1) : ℕ) : ℤ)

/-- Exact signed loss decomposition of a divisor letter: the clean recursive
core plus a nonnegative top-overlap deposit minus a nonnegative lower-overlap
deposit.  This identifies precisely what is discarded by the clean-divisor
API. -/
theorem lcmDivisorRayLetter_eq_cleanCore_add_overlapExcess (H j : ℕ) :
    lcmDivisorRayLetter H j =
      (Nat.totient j : ℤ) *
          deltaTotient (H / j) (H / j + 1) +
        (totientOverlapExcess j (2 * (H / j) + 1) : ℤ) *
          Nat.totient (2 * (H / j) + 1) -
        (totientOverlapExcess j (H / j + 1) : ℤ) *
          Nat.totient (H / j + 1) := by
  have htop := totientOverlapFactor_eq_totient_add_excess
    j (2 * (H / j) + 1) (by omega)
  have hlow := totientOverlapFactor_eq_totient_add_excess
    j (H / j + 1) (Nat.zero_lt_succ (H / j))
  unfold lcmDivisorRayLetter deltaTotient
  dsimp only
  rw [htop, hlow]
  rw [show H / j + 1 + H / j = 2 * (H / j) + 1 by omega]
  push_cast
  ring

/-- Every divisor-offset forcing letter is an exact quotient-scale letter;
unlike `deltaTotient_periodLcm_ray_split`, no cleanliness hypothesis is
needed. -/
theorem deltaTotient_divisor_ray_eq_overlapLetter
    {H j : ℕ} (hdvd : j ∣ H) :
    deltaTotient H (H + j) = lcmDivisorRayLetter H j := by
  have hH : j * (H / j) = H := Nat.mul_div_cancel' hdvd
  have htop : H + j + H = j * (2 * (H / j) + 1) := by
    calc
      H + j + H = 2 * H + j := by omega
      _ = 2 * (j * (H / j)) + j := by rw [hH]
      _ = j * (2 * (H / j) + 1) := by ring
  have hlow : H + j = j * (H / j + 1) := by
    calc
      H + j = j * (H / j) + j := by rw [hH]
      _ = j * (H / j + 1) := by ring
  unfold deltaTotient lcmDivisorRayLetter
  dsimp only
  rw [htop, hlow,
    totient_mul_eq_overlapFactor_mul j (2 * (H / j) + 1) (by omega),
    totient_mul_eq_overlapFactor_mul j (H / j + 1)
      (Nat.zero_lt_succ (H / j))]

/-- On a clean divisor the overlap factors collapse, recovering the recursive
letter from `deltaTotient_periodLcm_ray_split`.  Thus the overlap letter is a
genuine extension of that API rather than a competing coordinate. -/
theorem lcmDivisorRayLetter_eq_clean_delta
    {H j : ℕ}
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (H / j)) :
    lcmDivisorRayLetter H j =
      (Nat.totient j : ℤ) *
        deltaTotient (H / j) (H / j + 1) := by
  have hcopTop : Nat.Coprime j (2 * (H / j) + 1) :=
    coprime_ray_cofactor (j := j) (a := H / j) 2 hclean
  have hcopLow : Nat.Coprime j (H / j + 1) := by
    simpa using
      (coprime_ray_cofactor (j := j) (a := H / j) 1 hclean)
  unfold lcmDivisorRayLetter deltaTotient
  dsimp only
  rw [totientOverlapFactor_eq_totient_of_coprime hcopTop,
    totientOverlapFactor_eq_totient_of_coprime hcopLow]
  rw [show H / j + 1 + H / j = 2 * (H / j) + 1 by omega]
  push_cast
  ring

/-- Actual LCM-ray letter: divisor offsets use the exact quotient-scale
formula, while nondivisor offsets retain the literal totient difference. -/
def lcmRayArithmeticLetter (t j : ℕ) : ℤ :=
  if j ∣ periodLcm t then
    lcmDivisorRayLetter (periodLcm t) j
  else
    deltaTotient (periodLcm t) (periodLcm t + j)

/-- The arithmetic letter is exactly the genuine totient forcing letter. -/
theorem lcmRayArithmeticLetter_eq_deltaTotient (t j : ℕ) :
    lcmRayArithmeticLetter t j =
      deltaTotient (periodLcm t) (periodLcm t + j) := by
  unfold lcmRayArithmeticLetter
  split_ifs with hdvd
  · exact (deltaTotient_divisor_ray_eq_overlapLetter hdvd).symm
  · rfl

/-- The literal diagonal increment and the arithmetic LCM-ray letter are the
same integer.  Keeping this bridge named avoids reopening the endpoint
addition normalization whenever a cocycle identity is combined with the
divisor/prime-power arithmetic of `lcmRayArithmeticLetter`. -/
theorem diagonalWindowIncrement_eq_lcmRayArithmeticLetter (t j : ℕ) :
    diagonalWindowIncrement t j = lcmRayArithmeticLetter t j := by
  rw [lcmRayArithmeticLetter_eq_deltaTotient]
  unfold diagonalWindowIncrement deltaTotient
  have htop :
      periodLcm t + j + periodLcm t = 2 * periodLcm t + j := by
    omega
  rw [htop]

/-- A divisor offset contributes a forcing letter divisible by its own
totient.  Both endpoints are multiples of the offset, so monotonicity of
Euler's totient under divisibility applies before taking their difference. -/
theorem totient_dvd_lcmRayArithmeticLetter_of_dvd
    {t j : ℕ} (hjdvd : j ∣ periodLcm t) :
    (Nat.totient j : ℤ) ∣ lcmRayArithmeticLetter t j := by
  rw [lcmRayArithmeticLetter_eq_deltaTotient]
  unfold deltaTotient
  have hlow : j ∣ periodLcm t + j := hjdvd.add (dvd_refl j)
  have htop : j ∣ periodLcm t + j + periodLcm t := hlow.add hjdvd
  exact dvd_sub
    (Int.natCast_dvd_natCast.mpr (Nat.totient_dvd_of_dvd htop))
    (Int.natCast_dvd_natCast.mpr (Nat.totient_dvd_of_dvd hlow))

/-- Every positive even offset in the dyadic short window already divides
the LCM height.  A missing short offset would be a prime power above `2^a`;
evenness forces its prime base to be two, contradicting the upper edge of
the same window. -/
theorem even_short_offset_dvd_periodLcm_pow_two
    {a j : ℕ} (hjpos : 0 < j) (hjeven : Even j)
    (hjlt : j < 2 * 2 ^ a) :
    j ∣ periodLcm (2 ^ a) := by
  by_contra hnd
  obtain ⟨p, k, hp, hj, htj⟩ :=
    eq_prime_pow_of_not_dvd_periodLcm hjpos hjlt hnd
  have hkpos : 0 < k := by
    by_contra hnot
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hkzero, pow_zero] at hj
    subst j
    exact (Nat.not_even_one hjeven)
  have hpEven : Even p := by
    apply (Nat.even_pow' hkpos.ne').mp
    simpa [hj] using hjeven
  have hpTwo : p = 2 := hp.even_iff.mp hpEven
  subst p
  have hak : a < k := by
    apply (Nat.pow_lt_pow_iff_right (by omega : 1 < (2 : ℕ))).mp
    simpa [hj] using htj
  have hka : k < a + 1 := by
    apply (Nat.pow_lt_pow_iff_right (by omega : 1 < (2 : ℕ))).mp
    simpa [hj, pow_succ, mul_comm] using hjlt
  omega

/-- Consequently every positive even short-window letter carries the exact
factor `φ(j)`.  In particular this applies to the even terminal offset
`j = 2*q+2` in the odd-rank carry corridor. -/
theorem totient_dvd_lcmRayArithmeticLetter_of_even_short_pow_two
    {a j : ℕ} (hjpos : 0 < j) (hjeven : Even j)
    (hjlt : j < 2 * 2 ^ a) :
    (Nat.totient j : ℤ) ∣ lcmRayArithmeticLetter (2 ^ a) j :=
  totient_dvd_lcmRayArithmeticLetter_of_dvd
    (even_short_offset_dvd_periodLcm_pow_two hjpos hjeven hjlt)

/-- Below `2*t`, each arithmetic letter is either a quotient-scale divisor
letter or a literal letter at a bare prime-power offset above `t`.  This is
the exact divisor/foreign dichotomy for the short actual-LCM window. -/
theorem lcmRayArithmeticLetter_divisor_or_primePower
    {t j : ℕ} (hjpos : 0 < j) (hjlt : j < 2 * t) :
    (j ∣ periodLcm t ∧
        lcmRayArithmeticLetter t j =
          lcmDivisorRayLetter (periodLcm t) j) ∨
      ∃ p k : ℕ, Nat.Prime p ∧ j = p ^ k ∧ t < j ∧
        lcmRayArithmeticLetter t j =
          deltaTotient (periodLcm t) (periodLcm t + j) := by
  by_cases hdvd : j ∣ periodLcm t
  · left
    exact ⟨hdvd, by simp [lcmRayArithmeticLetter, hdvd]⟩
  · right
    obtain ⟨p, k, hp, hj, htj⟩ :=
      eq_prime_pow_of_not_dvd_periodLcm hjpos hjlt hdvd
    exact ⟨p, k, hp, hj, htj, by simp [lcmRayArithmeticLetter, hdvd]⟩

/-! ## Descent of the foreign prime-power letters

The divisor/prime-power dichotomy still leaves the nondivisor letters in
literal form.  A higher prime power is not genuinely foreign at every level:
its immediate predecessor already divides the LCM height, and is saturated
there.  Factoring that predecessor gives another exact overlap letter.  Thus
only exponent-one primes in `(t,2*t)` resist quotient descent.
-/

/-- The immediate predecessor of a short foreign prime power divides the LCM
height, but the next copy of its prime does not survive in the quotient. -/
theorem foreignPrimePower_predecessor_dvd_periodLcm
    {t p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k)
    (hlt : p ^ k < 2 * t) (hnd : ¬p ^ k ∣ periodLcm t) :
    p ^ (k - 1) ∣ periodLcm t ∧
      ¬p ∣ periodLcm t / p ^ (k - 1) := by
  let d := p ^ (k - 1)
  have hpow : p ^ k = d * p := by
    dsimp [d]
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  have htwoD : 2 * d ≤ p ^ k := by
    rw [hpow]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left d hp.two_le
  have hdlt : d < t := by omega
  have hdvd : d ∣ periodLcm t :=
    dvd_periodLcm (pow_pos hp.pos _) hdlt.le
  refine ⟨hdvd, ?_⟩
  intro hpq
  obtain ⟨c, hc⟩ := hpq
  have hH : d * (periodLcm t / d) = periodLcm t :=
    Nat.mul_div_cancel' hdvd
  have hdp : d * p ∣ periodLcm t := by
    refine ⟨c, ?_⟩
    calc
      periodLcm t = d * (periodLcm t / d) := hH.symm
      _ = d * (p * c) := by rw [hc]
      _ = (d * p) * c := by ring
  apply hnd
  simpa only [hpow] using hdp

/-- After a foreign prime power is divided by its saturated predecessor, every
prime factor of either coprime ray endpoint lies above the original LCM
cutoff.  The multiplier `u` is later specialized to `1` and `2`. -/
theorem foreignPrimePower_predecessor_endpoint_primeFactors_gt
    {t p k u r : ℕ} (hp : Nat.Prime p) (hk : 0 < k)
    (hlt : p ^ k < 2 * t) (hnd : ¬p ^ k ∣ periodLcm t)
    (hup : Nat.Coprime u p) (hr : Nat.Prime r)
    (hrdvd : r ∣ u * (periodLcm t / p ^ (k - 1)) + p) :
    t < r := by
  let H := periodLcm t
  let d := p ^ (k - 1)
  let A := H / d
  have hpred := foreignPrimePower_predecessor_dvd_periodLcm hp hk hlt hnd
  have hdvd : d ∣ H := by simpa [d, H] using hpred.1
  have hpA : ¬p ∣ A := by simpa [A, d, H] using hpred.2
  have hH : d * A = H := by
    simpa [A] using Nat.mul_div_cancel' hdvd
  by_contra hnot
  have hrt : r ≤ t := not_lt.mp hnot
  have hrH : r ∣ H := by
    dsimp [H]
    exact dvd_periodLcm hr.pos hrt
  have hrDA : r ∣ d * A := by rwa [hH]
  rcases hr.dvd_mul.mp hrDA with hrD | hrA
  · have hrP : r ∣ p := hr.dvd_of_dvd_pow (by simpa [d] using hrD)
    have hrEq : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrP
    subst r
    have hpUA : p ∣ u * A := by
      apply (Nat.dvd_add_right (dvd_refl p)).mp
      simpa [Nat.add_comm, A, d, H] using hrdvd
    exact hpA (hup.symm.dvd_of_dvd_mul_left hpUA)
  · have hrUA : r ∣ u * A := dvd_mul_of_dvd_right hrA u
    have hrP : r ∣ p := by
      apply (Nat.dvd_add_right hrUA).mp
      simpa [A, d, H] using hrdvd
    have hrEq : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrP
    subst r
    exact hpA hrA

/-- Quotient-scale overlap letter for a foreign prime power after removing
the predecessor power already present in the LCM height. -/
def lcmPrimePowerPredecessorLetter (H p k : ℕ) : ℤ :=
  let d := p ^ (k - 1)
  let a := H / d
  ((totientOverlapFactor d (2 * a + p) *
      Nat.totient (2 * a + p) : ℕ) : ℤ) -
    ((totientOverlapFactor d (a + p) *
      Nat.totient (a + p) : ℕ) : ℤ)

/-- Every short foreign prime-power letter has an exact predecessor-scale
overlap formula.  For `k = 1` the predecessor is `1`, so this deliberately
degenerates to the literal new-prime letter; for `k ≥ 2` it is a genuine
strict descent. -/
theorem deltaTotient_foreignPrimePower_ray_eq_predecessorLetter
    {t p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k)
    (hlt : p ^ k < 2 * t) (hnd : ¬p ^ k ∣ periodLcm t) :
    deltaTotient (periodLcm t) (periodLcm t + p ^ k) =
      lcmPrimePowerPredecessorLetter (periodLcm t) p k := by
  let H := periodLcm t
  let d := p ^ (k - 1)
  have hdvd : d ∣ H :=
    (foreignPrimePower_predecessor_dvd_periodLcm hp hk hlt hnd).1
  have hH : d * (H / d) = H := Nat.mul_div_cancel' hdvd
  have hpow : p ^ k = d * p := by
    dsimp [d]
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  have htop : H + p ^ k + H = d * (2 * (H / d) + p) := by
    calc
      H + p ^ k + H = 2 * H + p ^ k := by omega
      _ = 2 * (d * (H / d)) + d * p := by rw [hH, hpow]
      _ = d * (2 * (H / d) + p) := by ring
  have hlow : H + p ^ k = d * (H / d + p) := by
    calc
      H + p ^ k = d * (H / d) + d * p := by rw [hH, hpow]
      _ = d * (H / d + p) := by ring
  unfold deltaTotient lcmPrimePowerPredecessorLetter
  dsimp only [H, d]
  rw [htop, hlow,
    totient_mul_eq_overlapFactor_mul _ _
      (hp.pos.trans_le (Nat.le_add_left p (2 * (H / d)))),
    totient_mul_eq_overlapFactor_mul _ _
      (hp.pos.trans_le (Nat.le_add_left p (H / d)))]

/-- A higher foreign prime power really descends to a smaller LCM quotient.
This leaves exponent-one primes as the only nondivisor letters with no
strict quotient reduction in the short window. -/
theorem foreignPrimePower_predecessor_quotient_lt
    {t p k : ℕ} (hp : Nat.Prime p) (hk : 2 ≤ k)
    (hlt : p ^ k < 2 * t) (hnd : ¬p ^ k ∣ periodLcm t) :
    periodLcm t / p ^ (k - 1) < periodLcm t := by
  let H := periodLcm t
  let d := p ^ (k - 1)
  have hkpos : 0 < k := by omega
  have hdvd : d ∣ H :=
    (foreignPrimePower_predecessor_dvd_periodLcm hp hkpos hlt hnd).1
  have hd2 : 2 ≤ d := by
    dsimp [d]
    exact hp.two_le.trans (by
      simpa using
        (Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ k - 1)))
  have hqpos : 0 < H / d :=
    Nat.div_pos (Nat.le_of_dvd (periodLcm_pos t) hdvd) (pow_pos hp.pos _)
  have hqTwo : H / d < 2 * (H / d) := by omega
  have htwoD : 2 * (H / d) ≤ d * (H / d) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (H / d) hd2
  calc
    H / d < d * (H / d) := hqTwo.trans_le htwoD
    _ = H := Nat.mul_div_cancel' hdvd

/-- Fully descended short-window classification.  Divisor offsets use their
quotient overlap letter; every nondivisor prime power uses its predecessor
overlap letter together with the exact saturation witness. -/
theorem lcmRayArithmeticLetter_divisor_or_predecessorPrimePower
    {t j : ℕ} (hjpos : 0 < j) (hjlt : j < 2 * t) :
    (j ∣ periodLcm t ∧
        lcmRayArithmeticLetter t j =
          lcmDivisorRayLetter (periodLcm t) j) ∨
      ∃ p k : ℕ, Nat.Prime p ∧ j = p ^ k ∧ t < j ∧
        p ^ (k - 1) ∣ periodLcm t ∧
        ¬p ∣ periodLcm t / p ^ (k - 1) ∧
        lcmRayArithmeticLetter t j =
          lcmPrimePowerPredecessorLetter (periodLcm t) p k := by
  by_cases hdvd : j ∣ periodLcm t
  · left
    exact ⟨hdvd, by simp [lcmRayArithmeticLetter, hdvd]⟩
  · right
    obtain ⟨p, k, hp, hj, htj⟩ :=
      eq_prime_pow_of_not_dvd_periodLcm hjpos hjlt hdvd
    have hk : 0 < k := by
      by_contra hnot
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hj
      omega
    have hndPow : ¬p ^ k ∣ periodLcm t := by simpa only [hj] using hdvd
    have hpred := foreignPrimePower_predecessor_dvd_periodLcm
      hp hk (by simpa only [← hj] using hjlt) hndPow
    refine ⟨p, k, hp, hj, htj, hpred.1, hpred.2, ?_⟩
    rw [lcmRayArithmeticLetter, if_neg hdvd,
      show j = p ^ k from hj,
      deltaTotient_foreignPrimePower_ray_eq_predecessorLetter hp hk
        (by simpa only [← hj] using hjlt) hndPow]

/-! ## The exponent-one frontier

The predecessor descent is strict unless `k = 1`.  In that remaining case
the offset itself is a new prime `p ∈ (t,2*t)`.  Its two ray endpoints have
two rigid properties: every prime factor is above `t`, and the endpoints are
coprime to one another.  Thus the genuinely new part of the actual-LCM word
is reduced to a pair of coprime `t`-rough integers; no higher prime power is
left in this frontier.
-/

/-- A prime strictly above the cutoff does not divide the LCM height. -/
theorem newPrime_not_dvd_periodLcm
    {t p : ℕ} (hp : Nat.Prime p) (htp : t < p) :
    ¬p ∣ periodLcm t := by
  rw [DiagonalPincerDecomposition.periodLcm_eq_lcmHeight]
  intro hpdvd
  have hpt : p ≤ t :=
    (MersenneShadowCyclotomicNoncollapse.prime_dvd_lcmHeight_iff hp).1 hpdvd
  omega

/-- Every prime factor of a new-prime ray endpoint `q*H_t+p` lies above the
LCM cutoff.  This holds for every ray multiplier `q`, not only the two
multipliers used by the diagonal letter. -/
theorem newPrime_lcmRay_endpoint_primeFactors_gt
    {t p q ℓ : ℕ} (hp : Nat.Prime p) (htp : t < p)
    (hℓ : Nat.Prime ℓ) (hℓdvd : ℓ ∣ q * periodLcm t + p) :
    t < ℓ := by
  by_contra hnot
  have hℓt : ℓ ≤ t := by omega
  have hℓp : ℓ ∣ p :=
    (small_prime_dvd_cone_window_iff_dvd_offset hℓ hℓt).1 hℓdvd
  have hℓeq : ℓ = p :=
    (Nat.prime_dvd_prime_iff_eq hℓ hp).1 hℓp
  omega

/-! ### A quantitative roughness bound

The exponent-one frontier admits more than a support classification.  The
Euler product and the elementary union bound

`prod (1 - x_i) ≥ 1 - sum x_i`

show that a `t`-rough integer with `w` distinct prime factors has totient
density at least `1 - w/(t+1)`.  The product of those distinct factors also
gives `(t+1)^w ≤ n`.  Combining these two estimates with the landed
`periodLcm (2^a) < 2^(2*2^a-12)` bound makes the actual `q=1` new-prime
letter strictly positive for every `a ≥ 8`.
-/

/-- Finite union bound in product form over the rationals. -/
theorem one_sub_sum_le_prod_one_sub_rational
    (s : Finset ℕ) (f : ℕ → ℚ)
    (hzero : ∀ i ∈ s, 0 ≤ f i)
    (hone : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  rw [Finset.prod_one_sub_ordered]
  have hsum :
      (∑ i ∈ s,
          f i * ∏ j ∈ s with j < i, (1 - f j)) ≤
        ∑ i ∈ s, f i := by
    apply Finset.sum_le_sum
    intro i hi
    have hprodOne :
        (∏ j ∈ s with j < i, (1 - f j)) ≤ 1 := by
      apply Finset.prod_le_one
      · intro j hj
        have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
        exact sub_nonneg.mpr (hone j hjs)
      · intro j hj
        have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
        linarith [hzero j hjs]
    simpa using mul_le_mul_of_nonneg_left hprodOne (hzero i hi)
  linarith

/-- If every prime factor of `n` is above `t`, then the product of the
distinct factors bounds `(t+1)^omega(n)` from below. -/
theorem rough_primeFactors_card_power_le
    {t n : ℕ} (hn : 0 < n)
    (hrough : ∀ r : ℕ, Nat.Prime r → r ∣ n → t < r) :
    (t + 1) ^ n.primeFactors.card ≤ n := by
  calc
    (t + 1) ^ n.primeFactors.card ≤
        ∏ r ∈ n.primeFactors, r := by
      apply Finset.pow_card_le_prod
      intro r hr
      exact Nat.succ_le_iff.mpr
        (hrough r (Nat.prime_of_mem_primeFactors hr)
          (Nat.dvd_of_mem_primeFactors hr))
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- Rational Euler-product lower bound for a `t`-rough integer. -/
theorem totient_rational_lower_bound_of_primeFactors_gt
    {t n : ℕ} (hn : 0 < n)
    (hrough : ∀ r : ℕ, Nat.Prime r → r ∣ n → t < r) :
    (n : ℚ) *
        (1 - (n.primeFactors.card : ℚ) / ((t + 1 : ℕ) : ℚ)) ≤
      (Nat.totient n : ℚ) := by
  let s := n.primeFactors
  let f : ℕ → ℚ := fun r => (r : ℚ)⁻¹
  have hzero : ∀ r ∈ s, 0 ≤ f r := by
    intro r _hr
    dsimp [f]
    positivity
  have hone : ∀ r ∈ s, f r ≤ 1 := by
    intro r hr
    have hrPrime : Nat.Prime r := by
      exact Nat.prime_of_mem_primeFactors (by simpa [s] using hr)
    dsimp [f]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hrPrime.one_le)
  have hsum :
      (∑ r ∈ s, f r) ≤
        (s.card : ℚ) / ((t + 1 : ℕ) : ℚ) := by
    calc
      (∑ r ∈ s, f r) ≤
          ∑ _r ∈ s, (((t + 1 : ℕ) : ℚ))⁻¹ := by
        apply Finset.sum_le_sum
        intro r hr
        have hrMem : r ∈ n.primeFactors := by simpa [s] using hr
        have hrPrime : Nat.Prime r :=
          Nat.prime_of_mem_primeFactors hrMem
        have htr : t + 1 ≤ r :=
          Nat.succ_le_iff.mpr
            (hrough r hrPrime
              (Nat.dvd_of_mem_primeFactors hrMem))
        have htrQ : (((t + 1 : ℕ) : ℚ)) ≤ (r : ℚ) := by
          exact_mod_cast htr
        dsimp [f]
        have htQ : (0 : ℚ) < ((t + 1 : ℕ) : ℚ) := by positivity
        have hrQ : (0 : ℚ) < (r : ℚ) := by
          exact_mod_cast Nat.Prime.pos hrPrime
        exact (inv_le_inv₀ hrQ htQ).2 htrQ
      _ = (s.card : ℚ) / ((t + 1 : ℕ) : ℚ) := by
        simp [div_eq_mul_inv]
  have hprodBase :=
    one_sub_sum_le_prod_one_sub_rational s f hzero hone
  have hprod :
      1 - (s.card : ℚ) / ((t + 1 : ℕ) : ℚ) ≤
        ∏ r ∈ s, (1 - f r) :=
    (sub_le_sub_left hsum 1).trans hprodBase
  rw [Nat.totient_eq_mul_prod_factors]
  exact mul_le_mul_of_nonneg_left
    (by simpa [s, f] using hprod) (by positivity)

/-- A positive `2^a`-rough integer below `2^(2*2^a)` has fewer than one
quarter as many distinct prime factors as the roughness cutoff.  This is the
generic counting core used by both exponent-one and predecessor letters. -/
theorem rough_primeFactors_card_lt_quarter_of_lt_two_pow
    {a n : ℕ} (ha : 8 ≤ a) (hnPos : 0 < n)
    (hrough : ∀ r : ℕ, Nat.Prime r → r ∣ n → 2 ^ a < r)
    (hnPow : n < 2 ^ (2 * 2 ^ a)) :
    n.primeFactors.card < 2 ^ a / 4 := by
  let t := 2 ^ a
  have ht256 : 256 ≤ t := by
    change 2 ^ 8 ≤ 2 ^ a
    exact Nat.pow_le_pow_right (by norm_num) ha
  have htEq : t = 4 * 2 ^ (a - 2) := by
    dsimp [t]
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have htDiv : t / 4 = 2 ^ (a - 2) := by
    rw [htEq]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have htQuarterPos : 0 < t / 4 := by
    rw [htDiv]
    exact pow_pos (by norm_num) _
  have hcardPower : (t + 1) ^ n.primeFactors.card ≤ n := by
    apply rough_primeFactors_card_power_le hnPos
    intro r hr hrdvd
    simpa [t] using hrough r hr hrdvd
  have hmulExp : 8 * (t / 4) = 2 * t := by
    rw [htDiv, htEq]
    ring
  have hbase : 2 ^ 8 < t + 1 := by omega
  have hbasePow : 2 ^ (2 * t) < (t + 1) ^ (t / 4) := by
    calc
      2 ^ (2 * t) = (2 ^ 8) ^ (t / 4) := by
        rw [← pow_mul, hmulExp]
      _ < (t + 1) ^ (t / 4) :=
        Nat.pow_lt_pow_left hbase (Nat.ne_of_gt htQuarterPos)
  by_contra hnot
  have hquarterLe : t / 4 ≤ n.primeFactors.card :=
    Nat.le_of_not_gt (by simpa [t] using hnot)
  have hmono :
      (t + 1) ^ (t / 4) ≤ (t + 1) ^ n.primeFactors.card :=
    Nat.pow_le_pow_right (by omega) hquarterLe
  have hnPowT : n < 2 ^ (2 * t) := by simpa [t] using hnPow
  omega

/-- The corresponding uniform density statement: a positive `2^a`-rough
integer in the same height range retains more than three quarters of its
mass under Euler's totient. -/
theorem three_quarters_mul_lt_totient_of_rough_lt_two_pow
    {a n : ℕ} (ha : 8 ≤ a) (hnPos : 0 < n)
    (hrough : ∀ r : ℕ, Nat.Prime r → r ∣ n → 2 ^ a < r)
    (hnPow : n < 2 ^ (2 * 2 ^ a)) :
    (3 / 4 : ℚ) * (n : ℚ) < (Nat.totient n : ℚ) := by
  let t := 2 ^ a
  have hcard : n.primeFactors.card < t / 4 := by
    simpa [t] using
      rough_primeFactors_card_lt_quarter_of_lt_two_pow ha hnPos hrough hnPow
  have hfourCard : 4 * n.primeFactors.card < t + 1 := by
    have htEq : t = 4 * 2 ^ (a - 2) := by
      dsimp [t]
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have htDiv : t / 4 = 2 ^ (a - 2) := by
      rw [htEq]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    omega
  have hfrac :
      (n.primeFactors.card : ℚ) / ((t + 1 : ℕ) : ℚ) < 1 / 4 := by
    have hden : (0 : ℚ) < ((t + 1 : ℕ) : ℚ) := by positivity
    apply (div_lt_iff₀ hden).2
    have hfourCardQ :
        (4 : ℚ) * (n.primeFactors.card : ℚ) <
          ((t + 1 : ℕ) : ℚ) := by
      exact_mod_cast hfourCard
    nlinarith only [hfourCardQ]
  have htotientLower :
      (n : ℚ) *
          (1 - (n.primeFactors.card : ℚ) / ((t + 1 : ℕ) : ℚ)) ≤
        (Nat.totient n : ℚ) := by
    apply totient_rational_lower_bound_of_primeFactors_gt hnPos
    intro r hr hrdvd
    simpa [t] using hrough r hr hrdvd
  have hdensity :
      (3 / 4 : ℚ) <
        1 - (n.primeFactors.card : ℚ) / ((t + 1 : ℕ) : ℚ) := by
    linarith only [hfrac]
  have hmul := mul_lt_mul_of_pos_left hdensity (by positivity : (0 : ℚ) < n)
  nlinarith only [hmul, htotientLower]

/-! ### Relative roughness

For divisor offsets the endpoint itself need not be `t`-rough: a small prime
may divide both the outer divisor and the endpoint quotient.  The relative
Euler product has already removed exactly those old primes.  The same
cardinality argument therefore applies to `relativePrimeFactors j x`, which
is all that is needed for a uniform lower bound on the relative density.
-/

/-- The product of the genuinely new prime factors of `x` is bounded by
`x`.  Consequently a uniform lower bound on those primes controls their
cardinality exactly as in the fully rough case. -/
theorem relativePrimeFactors_card_power_le
    {t j x : ℕ} (hx : 0 < x)
    (hrough : ∀ r ∈ relativePrimeFactors j x, t < r) :
    (t + 1) ^ (relativePrimeFactors j x).card ≤ x := by
  have hsub : relativePrimeFactors j x ⊆ x.primeFactors := by
    exact Finset.sdiff_subset
  calc
    (t + 1) ^ (relativePrimeFactors j x).card ≤
        ∏ r ∈ relativePrimeFactors j x, r := by
      apply Finset.pow_card_le_prod
      intro r hr
      exact Nat.succ_le_iff.mpr (hrough r hr)
    _ ≤ x := by
      apply Nat.le_of_dvd hx
      exact
        (Finset.prod_dvd_prod_of_subset
          (relativePrimeFactors j x) x.primeFactors (fun r => r) hsub).trans
          (Nat.prod_primeFactors_dvd x)

/-- A relative prime-factor set in the actual LCM height range has fewer
than one quarter as many elements as the power-of-two cutoff. -/
theorem relativePrimeFactors_card_lt_quarter_of_lt_two_pow
    {a j x : ℕ} (ha : 8 ≤ a) (hx : 0 < x)
    (hrough : ∀ r ∈ relativePrimeFactors j x, 2 ^ a < r)
    (hxPow : x < 2 ^ (2 * 2 ^ a)) :
    (relativePrimeFactors j x).card < 2 ^ a / 4 := by
  let t := 2 ^ a
  have htEq : t = 4 * 2 ^ (a - 2) := by
    dsimp [t]
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have htDiv : t / 4 = 2 ^ (a - 2) := by
    rw [htEq]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have htQuarterPos : 0 < t / 4 := by
    rw [htDiv]
    exact pow_pos (by norm_num) _
  have hcardPower :
      (t + 1) ^ (relativePrimeFactors j x).card ≤ x := by
    apply relativePrimeFactors_card_power_le hx
    intro r hr
    simpa [t] using hrough r hr
  have hmulExp : 8 * (t / 4) = 2 * t := by
    rw [htDiv, htEq]
    ring
  have hbase : 2 ^ 8 < t + 1 := by
    have ht256 : 256 ≤ t := by
      change 2 ^ 8 ≤ 2 ^ a
      exact Nat.pow_le_pow_right (by norm_num) ha
    omega
  have hbasePow : 2 ^ (2 * t) < (t + 1) ^ (t / 4) := by
    calc
      2 ^ (2 * t) = (2 ^ 8) ^ (t / 4) := by
        rw [← pow_mul, hmulExp]
      _ < (t + 1) ^ (t / 4) :=
        Nat.pow_lt_pow_left hbase (Nat.ne_of_gt htQuarterPos)
  by_contra hnot
  have hquarterLe :
      t / 4 ≤ (relativePrimeFactors j x).card :=
    Nat.le_of_not_gt (by simpa [t] using hnot)
  have hmono :
      (t + 1) ^ (t / 4) ≤
        (t + 1) ^ (relativePrimeFactors j x).card :=
    Nat.pow_le_pow_right (by omega) hquarterLe
  have hxPowT : x < 2 ^ (2 * t) := by simpa [t] using hxPow
  omega

/-- Uniform three-quarter lower bound for the relative Euler density.  Only
the genuinely new primes must lie above the cutoff; primes shared with the
outer factor `j` are harmless because they are absent from this product. -/
theorem three_quarters_lt_relativeEulerProduct_of_lt_two_pow
    {a j x : ℕ} (ha : 8 ≤ a) (hx : 0 < x)
    (hrough : ∀ r ∈ relativePrimeFactors j x, 2 ^ a < r)
    (hxPow : x < 2 ^ (2 * 2 ^ a)) :
    (3 / 4 : ℚ) <
      ∏ r ∈ relativePrimeFactors j x, (1 - (r : ℚ)⁻¹) := by
  let t := 2 ^ a
  let s := relativePrimeFactors j x
  let f : ℕ → ℚ := fun r => (r : ℚ)⁻¹
  have hcard : s.card < t / 4 := by
    simpa [s, t] using
      relativePrimeFactors_card_lt_quarter_of_lt_two_pow ha hx hrough hxPow
  have hfourCard : 4 * s.card < t + 1 := by
    have htEq : t = 4 * 2 ^ (a - 2) := by
      dsimp [t]
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have htDiv : t / 4 = 2 ^ (a - 2) := by
      rw [htEq]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    omega
  have hzero : ∀ r ∈ s, 0 ≤ f r := by
    intro r _hr
    dsimp [f]
    positivity
  have hone : ∀ r ∈ s, f r ≤ 1 := by
    intro r hr
    have hrMem : r ∈ x.primeFactors := by
      change r ∈ relativePrimeFactors j x at hr
      unfold relativePrimeFactors at hr
      exact (Finset.mem_sdiff.mp hr).1
    have hrPrime : Nat.Prime r := Nat.prime_of_mem_primeFactors hrMem
    dsimp [f]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hrPrime.one_le)
  have hsum :
      (∑ r ∈ s, f r) ≤ (s.card : ℚ) / ((t + 1 : ℕ) : ℚ) := by
    calc
      (∑ r ∈ s, f r) ≤
          ∑ _r ∈ s, (((t + 1 : ℕ) : ℚ))⁻¹ := by
        apply Finset.sum_le_sum
        intro r hr
        have htr : t + 1 ≤ r := by
          exact Nat.succ_le_iff.mpr (by
            simpa [s, t] using hrough r (by simpa [s] using hr))
        have htrQ : (((t + 1 : ℕ) : ℚ)) ≤ (r : ℚ) := by
          exact_mod_cast htr
        have htQ : (0 : ℚ) < ((t + 1 : ℕ) : ℚ) := by positivity
        have hrQ : (0 : ℚ) < (r : ℚ) := by
          have hrMem : r ∈ x.primeFactors := by
            change r ∈ relativePrimeFactors j x at hr
            unfold relativePrimeFactors at hr
            exact (Finset.mem_sdiff.mp hr).1
          exact_mod_cast (Nat.prime_of_mem_primeFactors hrMem).pos
        dsimp [f]
        exact (inv_le_inv₀ hrQ htQ).2 htrQ
      _ = (s.card : ℚ) / ((t + 1 : ℕ) : ℚ) := by
        simp [div_eq_mul_inv]
  have hfrac :
      (s.card : ℚ) / ((t + 1 : ℕ) : ℚ) < 1 / 4 := by
    have hden : (0 : ℚ) < ((t + 1 : ℕ) : ℚ) := by positivity
    apply (div_lt_iff₀ hden).2
    have hfourCardQ :
        (4 : ℚ) * (s.card : ℚ) < ((t + 1 : ℕ) : ℚ) := by
      exact_mod_cast hfourCard
    nlinarith only [hfourCardQ]
  have hprodBase :=
    one_sub_sum_le_prod_one_sub_rational s f hzero hone
  have hprod :
      1 - (s.card : ℚ) / ((t + 1 : ℕ) : ℚ) ≤
        ∏ r ∈ s, (1 - f r) :=
    (sub_le_sub_left hsum 1).trans hprodBase
  have hdensity :
      (3 / 4 : ℚ) <
        1 - (s.card : ℚ) / ((t + 1 : ℕ) : ℚ) := by
    linarith only [hfrac]
  exact hdensity.trans_le (by simpa [s, f] using hprod)

/-- Every endpoint `2*A+p` below an actual power-of-two LCM height lies in
the counting range used by the rough-density lemmas, provided `A ≤ H` and
`p < 2*t`. -/
theorem two_mul_le_periodLcm_add_lt_two_pow
    {a A p : ℕ} (ha : 8 ≤ a)
    (hA : A ≤ periodLcm (2 ^ a)) (hp : p < 2 * 2 ^ a) :
    2 * A + p < 2 ^ (2 * 2 ^ a) := by
  let t := 2 ^ a
  let H := periodLcm t
  have ht256 : 256 ≤ t := by
    change 2 ^ 8 ≤ 2 ^ a
    exact Nat.pow_le_pow_right (by norm_num) ha
  have hHeight : H < 2 ^ (2 * t - 12) := by
    simpa [H, t] using
      (periodLcm_pow_two_lt_two_pow_guardTwelve (by omega : 4 ≤ a))
  have hHeightCoarse : H < 2 ^ (2 * t - 2) := by
    exact hHeight.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hTwoHeight : 2 * H < 2 ^ (2 * t - 1) := by
    calc
      2 * H < 2 * 2 ^ (2 * t - 2) :=
        Nat.mul_lt_mul_of_pos_left hHeightCoarse (by omega)
      _ = 2 ^ (2 * t - 1) := by
        rw [show 2 * t - 1 = (2 * t - 2) + 1 by omega, pow_succ]
        ring
  have hTwoT : 2 * t ≤ 2 ^ (2 * t - 1) := by
    have hpowAux : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            n + 2 ≤ 2 * (n + 1) := by omega
            _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
            _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]
    have hpow := hpowAux (2 * t - 1)
    omega
  have hpT : p < 2 * t := by simpa [t] using hp
  have hpPow : p < 2 ^ (2 * t - 1) := hpT.trans_le hTwoT
  have hAT : A ≤ H := by simpa [H, t] using hA
  have hTwoA : 2 * A < 2 ^ (2 * t - 1) :=
    (Nat.mul_le_mul_left 2 hAT).trans_lt hTwoHeight
  have hsum : 2 * A + p < 2 ^ (2 * t) := by
    calc
      2 * A + p < 2 ^ (2 * t - 1) + 2 ^ (2 * t - 1) :=
        Nat.add_lt_add hTwoA hpPow
      _ = 2 ^ (2 * t) := by
        calc
          2 ^ (2 * t - 1) + 2 ^ (2 * t - 1) =
              2 * 2 ^ (2 * t - 1) := by ring
          _ = 2 ^ ((2 * t - 1) + 1) := by
            simp [pow_succ, Nat.mul_comm]
          _ = 2 ^ (2 * t) := by congr 1; omega
  simpa [t] using hsum

/-! ### Positivity of every divisor letter

Write `H = j*A`.  Relative Euler products give

`phi(j*(2*A+1))/phi(j) > (3/4)*(2*A+1)`

while the corresponding ratio at `A+1` is at most `A+1`.  Their difference
is greater than `A/2 - 1/4`, hence is positive even when the two endpoints
share saturated small primes with `j`.
-/

/-- Quantitative divisor-letter bound.  If `H = periodLcm (2^a)` and
`j ∣ H`, then `H < 4*j*c_j`.  This is uniform enough to make the complete
short word grow on a logarithmic-in-`t` scale. -/
theorem periodLcm_lt_four_mul_j_mul_lcmRayArithmeticLetter_divisor
    {a j : ℕ} (ha : 8 ≤ a) (hjpos : 0 < j)
    (hjdvd : j ∣ periodLcm (2 ^ a)) :
    (periodLcm (2 ^ a) : ℤ) <
      4 * (j : ℤ) * lcmRayArithmeticLetter (2 ^ a) j := by
  let t := 2 ^ a
  let H := periodLcm t
  let A := H / j
  let x := A + 1
  let y := 2 * A + 1
  have hHPos : 0 < H := by
    dsimp [H]
    exact periodLcm_pos t
  have hAPos : 0 < A := by
    exact Nat.div_pos (Nat.le_of_dvd hHPos (by simpa [H, t] using hjdvd)) hjpos
  have hH : j * A = H := by
    simpa [A, H, t] using Nat.mul_div_cancel' hjdvd
  have hxPos : 0 < x := by dsimp [x]; omega
  have hyPos : 0 < y := by dsimp [y]; omega
  have hroughY :
      ∀ r ∈ relativePrimeFactors j y, t < r := by
    intro r hr
    exact relativePrimeFactors_lcmDivisor_endpoint_gt
      (t := t) (j := j) (q := 2) (by simpa [H, t] using hjdvd)
      (by simpa [y, A, H] using hr)
  have hAleH : A ≤ H := by
    dsimp [A]
    exact Nat.div_le_self H j
  have hyPow : y < 2 ^ (2 * t) := by
    simpa [y, A, H, t] using
      (two_mul_le_periodLcm_add_lt_two_pow ha (A := H / j) (p := 1)
        (Nat.div_le_self _ _) (by
          have htPos : 0 < t := by dsimp [t]; positivity
          simpa [t] using (show 1 < 2 * t by omega)))
  have hprodY :
      (3 / 4 : ℚ) <
        ∏ r ∈ relativePrimeFactors j y, (1 - (r : ℚ)⁻¹) := by
    apply three_quarters_lt_relativeEulerProduct_of_lt_two_pow ha hyPos
    · intro r hr
      simpa [t] using hroughY r hr
    · simpa [t] using hyPow
  have hprodX :
      (∏ r ∈ relativePrimeFactors j x, (1 - (r : ℚ)⁻¹)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro r hr
      have hrMem : r ∈ x.primeFactors :=
        Finset.sdiff_subset hr
      have hrPrime : Nat.Prime r := Nat.prime_of_mem_primeFactors hrMem
      exact sub_nonneg.mpr
        (inv_le_one_of_one_le₀ (by exact_mod_cast hrPrime.one_le))
    · intro r _hr
      exact sub_le_self 1 (inv_nonneg.mpr (by positivity))
  have htopFormula :=
    totient_mul_eq_totient_mul_relativeEulerProduct j y hjpos hyPos
  have hlowFormula :=
    totient_mul_eq_totient_mul_relativeEulerProduct j x hjpos hxPos
  have hphiJPos : (0 : ℚ) < (Nat.totient j : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr hjpos
  have hxQPos : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hxPos
  have hyQPos : (0 : ℚ) < (y : ℚ) := by exact_mod_cast hyPos
  have htopLower :
      (Nat.totient j : ℚ) * (3 / 4 : ℚ) * (y : ℚ) <
        (Nat.totient (j * y) : ℚ) := by
    calc
      (Nat.totient j : ℚ) * (3 / 4 : ℚ) * (y : ℚ) =
          (Nat.totient j : ℚ) * (y : ℚ) * (3 / 4 : ℚ) := by ring
      _ < (Nat.totient j : ℚ) * (y : ℚ) *
          ∏ r ∈ relativePrimeFactors j y, (1 - (r : ℚ)⁻¹) :=
        mul_lt_mul_of_pos_left hprodY (mul_pos hphiJPos hyQPos)
      _ = (Nat.totient (j * y) : ℚ) := htopFormula.symm
  have hlowUpper :
      (Nat.totient (j * x) : ℚ) ≤
        (Nat.totient j : ℚ) * (x : ℚ) := by
    calc
      (Nat.totient (j * x) : ℚ) =
          (Nat.totient j : ℚ) * (x : ℚ) *
            ∏ r ∈ relativePrimeFactors j x, (1 - (r : ℚ)⁻¹) :=
        hlowFormula
      _ ≤ (Nat.totient j : ℚ) * (x : ℚ) * 1 :=
        mul_le_mul_of_nonneg_left hprodX (mul_pos hphiJPos hxQPos).le
      _ = (Nat.totient j : ℚ) * (x : ℚ) := by ring
  have hbase : (x : ℚ) < (3 / 4 : ℚ) * (y : ℚ) := by
    have hAOne : (1 : ℚ) ≤ (A : ℚ) := by exact_mod_cast hAPos
    dsimp [x, y]
    push_cast
    nlinarith only [hAOne]
  have hmargin :
      (A : ℚ) / 4 ≤ (3 / 4 : ℚ) * (y : ℚ) - (x : ℚ) := by
    have hAOne : (1 : ℚ) ≤ (A : ℚ) := by exact_mod_cast hAPos
    dsimp [x, y]
    push_cast
    nlinarith only [hAOne]
  have hphiJOne : (1 : ℚ) ≤ (Nat.totient j : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr hjpos
  have hmarginNonneg :
      (0 : ℚ) ≤ (3 / 4 : ℚ) * (y : ℚ) - (x : ℚ) := by
    exact sub_nonneg.mpr hbase.le
  have hmarginScale :
      (3 / 4 : ℚ) * (y : ℚ) - (x : ℚ) ≤
        (Nat.totient j : ℚ) *
          ((3 / 4 : ℚ) * (y : ℚ) - (x : ℚ)) := by
    simpa using mul_le_mul_of_nonneg_right hphiJOne hmarginNonneg
  have hscaledMargin :
      (Nat.totient j : ℚ) * (x : ℚ) + (A : ℚ) / 4 ≤
        (Nat.totient j : ℚ) * (3 / 4 : ℚ) * (y : ℚ) := by
    nlinarith only [hmargin, hmarginScale]
  have hgapLower :
      (A : ℚ) / 4 <
        (Nat.totient (j * y) : ℚ) - (Nat.totient (j * x) : ℚ) := by
    linarith only [hlowUpper, hscaledMargin, htopLower]
  have hletter :
      lcmRayArithmeticLetter t j =
        (Nat.totient (j * y) : ℤ) - (Nat.totient (j * x) : ℤ) := by
    rw [lcmRayArithmeticLetter_eq_deltaTotient]
    unfold deltaTotient
    rw [show periodLcm t + j + periodLcm t = j * y by
      dsimp only [y]
      change H + j + H = j * (2 * A + 1)
      rw [← hH]
      ring,
      show periodLcm t + j = j * x by
        dsimp only [x]
        change H + j = j * (A + 1)
        rw [← hH]
        ring]
  have hletterQ :
      (lcmRayArithmeticLetter t j : ℚ) =
        (Nat.totient (j * y) : ℚ) - (Nat.totient (j * x) : ℚ) := by
    exact_mod_cast hletter
  have hAQuarter :
      (A : ℚ) / 4 < (lcmRayArithmeticLetter t j : ℚ) := by
    rw [hletterQ]
    exact hgapLower
  have hA : (A : ℚ) < 4 * (lcmRayArithmeticLetter t j : ℚ) := by
    nlinarith only [hAQuarter]
  have hjQPos : (0 : ℚ) < (j : ℚ) := by exact_mod_cast hjpos
  have hmul := mul_lt_mul_of_pos_left hA hjQPos
  have hboundQ :
      (H : ℚ) < 4 * (j : ℚ) * (lcmRayArithmeticLetter t j : ℚ) := by
    calc
      (H : ℚ) = (j : ℚ) * (A : ℚ) := by exact_mod_cast hH.symm
      _ < (j : ℚ) * (4 * (lcmRayArithmeticLetter t j : ℚ)) := hmul
      _ = 4 * (j : ℚ) * (lcmRayArithmeticLetter t j : ℚ) := by ring
  have hboundZ :
      (H : ℤ) < 4 * (j : ℤ) * lcmRayArithmeticLetter t j := by
    exact_mod_cast hboundQ
  simpa [H, t] using hboundZ

/-- Every divisor-offset letter at a sufficiently large power-of-two LCM
height is strictly positive.  No cleanliness condition on the divisor is
required. -/
theorem lcmRayArithmeticLetter_divisor_pos
    {a j : ℕ} (ha : 8 ≤ a) (hjpos : 0 < j)
    (hjdvd : j ∣ periodLcm (2 ^ a)) :
    0 < lcmRayArithmeticLetter (2 ^ a) j := by
  have hbound :=
    periodLcm_lt_four_mul_j_mul_lcmRayArithmeticLetter_divisor
      ha hjpos hjdvd
  have hHPos : (0 : ℤ) < (periodLcm (2 ^ a) : ℤ) := by
    exact_mod_cast periodLcm_pos (2 ^ a)
  have hjZPos : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hjpos
  nlinarith only [hbound, hHPos, hjZPos]

/-- Higher foreign prime powers obey the same quarter-height lower bound as
the exponent-one frontier, and a uniform five-halves upper bound.  The
statement is integral: `H < 4*c` and `2*c < 5*H` are exactly
`H/4 < c < 5*H/2` after embedding in `ℚ`. -/
theorem lcmRayArithmeticLetter_foreignPrimePower_bracket
    {a p k : ℕ} (ha : 8 ≤ a) (hp : Nat.Prime p) (hk : 2 ≤ k)
    (htq : 2 ^ a < p ^ k) (hqt : p ^ k < 2 * 2 ^ a)
    (hnd : ¬p ^ k ∣ periodLcm (2 ^ a)) :
    (periodLcm (2 ^ a) : ℤ) <
        4 * lcmRayArithmeticLetter (2 ^ a) (p ^ k) ∧
      2 * lcmRayArithmeticLetter (2 ^ a) (p ^ k) <
        5 * (periodLcm (2 ^ a) : ℤ) := by
  let t := 2 ^ a
  let H := periodLcm t
  let q := p ^ k
  let d := p ^ (k - 1)
  let A := H / d
  let x := A + p
  let y := 2 * A + p
  have ht256 : 256 ≤ t := by
    change 2 ^ 8 ≤ 2 ^ a
    exact Nat.pow_le_pow_right (by norm_num) ha
  have hkPos : 0 < k := by omega
  have hqPos : 0 < q := by dsimp [q]; exact pow_pos hp.pos _
  have hqtT : q < 2 * t := by simpa [q, t] using hqt
  have hndT : ¬q ∣ H := by simpa [q, H, t] using hnd
  have hpred :=
    foreignPrimePower_predecessor_dvd_periodLcm hp hkPos hqtT hndT
  have hdvd : d ∣ H := by simpa [d] using hpred.1
  have hpA : ¬p ∣ A := by simpa [A, d] using hpred.2
  have hdPos : 0 < d := by dsimp [d]; exact pow_pos hp.pos _
  have hHPos : 0 < H := by dsimp [H]; exact periodLcm_pos t
  have hAPos : 0 < A :=
    Nat.div_pos (Nat.le_of_dvd hHPos hdvd) hdPos
  have hH : d * A = H := by
    simpa [A] using Nat.mul_div_cancel' hdvd
  have hq : d * p = q := by
    dsimp [d, q]
    conv_rhs => rw [← Nat.sub_add_cancel hkPos]
    rw [pow_succ]
  have hpNeTwo : p ≠ 2 := by
    intro hpTwo
    subst p
    have hak : a < k := by
      apply (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp
      simpa [t, q] using htq
    have hka : k < a + 1 := by
      apply (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp
      calc
        2 ^ k < 2 * 2 ^ a := by simpa [q, t] using hqt
        _ = 2 ^ (a + 1) := by rw [pow_succ]; ring
    omega
  have hpTwo : 2 ≤ p := hp.two_le
  have hpThree : 3 ≤ p := by omega
  have hpOdd : Odd p :=
    Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hpNeTwo)
  have hcopOne : Nat.Coprime 1 p := by simp
  have hcopTwo : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpOdd
  have hxPos : 0 < x := by dsimp [x]; omega
  have hyPos : 0 < y := by dsimp [y]; omega
  have hroughY :
      ∀ r : ℕ, Nat.Prime r → r ∣ y → t < r := by
    intro r hr hrdvd
    exact foreignPrimePower_predecessor_endpoint_primeFactors_gt
      hp hkPos hqtT hndT hcopTwo hr (by simpa [y, A, d, H] using hrdvd)
  have hAleH : A ≤ H := by dsimp [A]; exact Nat.div_le_self H d
  have hpLeQ : p ≤ q := by
    dsimp [q]
    simpa using Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ k)
  have hpLtTwoT : p < 2 * 2 ^ a := hpLeQ.trans_lt hqt
  have hyPow : y < 2 ^ (2 * t) := by
    simpa [y, A, H, d, t] using
      (two_mul_le_periodLcm_add_lt_two_pow ha
        (A := periodLcm (2 ^ a) / p ^ (k - 1))
        (Nat.div_le_self _ _) hpLtTwoT)
  have htopDensity :
      (3 / 4 : ℚ) * (y : ℚ) < (Nat.totient y : ℚ) := by
    apply three_quarters_mul_lt_totient_of_rough_lt_two_pow ha hyPos
    · intro r hr hrdvd
      simpa [t] using hroughY r hr hrdvd
    · simpa [t] using hyPow
  have hpX : ¬p ∣ x := by
    intro hpXdvd
    apply hpA
    apply (Nat.dvd_add_right (dvd_refl p)).mp
    simpa [Nat.add_comm, x] using hpXdvd
  have hpY : ¬p ∣ y := by
    intro hpYdvd
    have hpTwoA : p ∣ 2 * A := by
      apply (Nat.dvd_add_right (dvd_refl p)).mp
      simpa [Nat.add_comm, y] using hpYdvd
    exact hpA (hcopTwo.symm.dvd_of_dvd_mul_left hpTwoA)
  have hcopDX : Nat.Coprime d x := by
    dsimp [d]
    exact (hp.coprime_iff_not_dvd.mpr hpX).pow_left (k - 1)
  have hcopDY : Nat.Coprime d y := by
    dsimp [d]
    exact (hp.coprime_iff_not_dvd.mpr hpY).pow_left (k - 1)
  have hletter :
      lcmRayArithmeticLetter t q =
        (Nat.totient d : ℤ) *
          ((Nat.totient y : ℤ) - (Nat.totient x : ℤ)) := by
    rw [lcmRayArithmeticLetter, if_neg hndT,
      deltaTotient_foreignPrimePower_ray_eq_predecessorLetter hp hkPos hqtT hndT]
    unfold lcmPrimePowerPredecessorLetter
    dsimp only
    rw [totientOverlapFactor_eq_totient_of_coprime (by simpa [d, y, A, H] using hcopDY),
      totientOverlapFactor_eq_totient_of_coprime (by simpa [d, x, A, H] using hcopDX)]
    push_cast
    ring
  have hphiDFormula :
      Nat.totient d = p ^ (k - 2) * (p - 1) := by
    dsimp [d]
    simpa using Nat.totient_prime_pow hp (by omega : 0 < k - 1)
  have hdFormula : d = p ^ (k - 2) * p := by
    dsimp [d]
    rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  have htwoDLeThreePhi : 2 * d ≤ 3 * Nat.totient d := by
    have hbase : 2 * p ≤ 3 * (p - 1) := by omega
    calc
      2 * d = p ^ (k - 2) * (2 * p) := by rw [hdFormula]; ring
      _ ≤ p ^ (k - 2) * (3 * (p - 1)) :=
        Nat.mul_le_mul_left _ hbase
      _ = 3 * Nat.totient d := by rw [hphiDFormula]; ring
  have htDvd : t ∣ H := by
    dsimp [H]
    exact dvd_periodLcm (by omega) le_rfl
  have htPredDvd : t - 1 ∣ H := by
    dsimp [H]
    exact dvd_periodLcm (by omega) (by omega)
  have htCoprimePred : Nat.Coprime t (t - 1) := by
    rw [Nat.coprime_self_sub_right (by omega : 1 ≤ t)]
    simp
  have htProdLeH : t * (t - 1) ≤ H :=
    Nat.le_of_dvd hHPos
      (htCoprimePred.mul_dvd_of_dvd_of_dvd htDvd htPredDvd)
  have hfourTLeH : 4 * t ≤ H := by
    calc
      4 * t = t * 4 := by omega
      _ ≤ t * (t - 1) := Nat.mul_le_mul_left t (by omega)
      _ ≤ H := htProdLeH
  have htwoQltH : 2 * q < H := by
    calc
      2 * q < 2 * (2 * t) := Nat.mul_lt_mul_of_pos_left hqtT (by omega)
      _ = 4 * t := by ring
      _ ≤ H := hfourTLeH
  have htwoPltA : 2 * p < A := by
    apply Nat.lt_of_mul_lt_mul_left (a := d)
    calc
      d * (2 * p) = 2 * q := by rw [← hq]; ring
      _ < H := htwoQltH
      _ = d * A := hH.symm
  have hphiXLe : (Nat.totient x : ℚ) ≤ (x : ℚ) := by
    exact_mod_cast Nat.totient_le x
  have hgapBase :
      (A : ℚ) / 2 - (p : ℚ) / 4 <
        (Nat.totient y : ℚ) - (Nat.totient x : ℚ) := by
    dsimp [x, y] at hphiXLe htopDensity
    push_cast at hphiXLe htopDensity
    nlinarith only [hphiXLe, htopDensity]
  have hbasePos : (0 : ℚ) < (A : ℚ) / 2 - (p : ℚ) / 4 := by
    have htwoPltAQ : (2 : ℚ) * p < A := by exact_mod_cast htwoPltA
    nlinarith only [htwoPltAQ]
  have hphiDLower :
      (2 / 3 : ℚ) * (d : ℚ) ≤ (Nat.totient d : ℚ) := by
    have hcast : (2 : ℚ) * d ≤ 3 * Nat.totient d := by
      exact_mod_cast htwoDLeThreePhi
    nlinarith only [hcast]
  have hscalar :
      (A : ℚ) / 4 <
        (2 / 3 : ℚ) * ((A : ℚ) / 2 - (p : ℚ) / 4) := by
    have htwoPltAQ : (2 : ℚ) * p < A := by exact_mod_cast htwoPltA
    nlinarith only [htwoPltAQ]
  have hdQPos : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hdPos
  have hHQuarter :
      (H : ℚ) / 4 <
        (Nat.totient d : ℚ) *
          ((A : ℚ) / 2 - (p : ℚ) / 4) := by
    have hscale := mul_lt_mul_of_pos_left hscalar hdQPos
    have hdensityScale := mul_le_mul_of_nonneg_right hphiDLower hbasePos.le
    have hHQ : (d : ℚ) * A = H := by exact_mod_cast hH
    nlinarith only [hscale, hdensityScale, hHQ]
  have hphiDPos : (0 : ℚ) < (Nat.totient d : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr hdPos
  have hgapLower :
      (H : ℚ) / 4 <
        (Nat.totient d : ℚ) *
          ((Nat.totient y : ℚ) - (Nat.totient x : ℚ)) := by
    exact hHQuarter.trans
      (mul_lt_mul_of_pos_left hgapBase hphiDPos)
  have hgapPos :
      (0 : ℚ) < (Nat.totient y : ℚ) - (Nat.totient x : ℚ) :=
    hbasePos.trans hgapBase
  have hphiDLe : (Nat.totient d : ℚ) ≤ (d : ℚ) := by
    exact_mod_cast Nat.totient_le d
  have hphiXPos : (0 : ℚ) < (Nat.totient x : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr hxPos
  have hphiYLe : (Nat.totient y : ℚ) ≤ (y : ℚ) := by
    exact_mod_cast Nat.totient_le y
  have hgapLtY :
      (Nat.totient y : ℚ) - (Nat.totient x : ℚ) < (y : ℚ) := by
    nlinarith only [hphiXPos, hphiYLe]
  have hgapUpper :
      (Nat.totient d : ℚ) *
          ((Nat.totient y : ℚ) - (Nat.totient x : ℚ)) <
        (5 / 2 : ℚ) * (H : ℚ) := by
    have hfirst := mul_le_mul_of_nonneg_right hphiDLe hgapPos.le
    have hsecond := mul_lt_mul_of_pos_left hgapLtY hdQPos
    have hHQ : (d : ℚ) * A = H := by exact_mod_cast hH
    have hqQ : (d : ℚ) * p = q := by exact_mod_cast hq
    have htwoQQ : (2 : ℚ) * q < H := by exact_mod_cast htwoQltH
    dsimp [y] at hsecond
    push_cast at hsecond
    nlinarith only [hfirst, hsecond, hHQ, hqQ, htwoQQ]
  have hletterQ :
      (lcmRayArithmeticLetter t q : ℚ) =
        (Nat.totient d : ℚ) *
          ((Nat.totient y : ℚ) - (Nat.totient x : ℚ)) := by
    exact_mod_cast hletter
  constructor
  · have hQ :
        (H : ℚ) < 4 * (lcmRayArithmeticLetter t q : ℚ) := by
      rw [hletterQ]
      nlinarith only [hgapLower]
    have hZ :
        (H : ℤ) < 4 * lcmRayArithmeticLetter t q := by
      exact_mod_cast hQ
    simpa [H, t, q] using hZ
  · have hQ :
        2 * (lcmRayArithmeticLetter t q : ℚ) < 5 * (H : ℚ) := by
      rw [hletterQ]
      nlinarith only [hgapUpper]
    have hZ :
        2 * lcmRayArithmeticLetter t q < 5 * (H : ℤ) := by
      exact_mod_cast hQ
    simpa [H, t, q] using hZ

/-- At a sufficiently large power-of-two LCM height, the upper endpoint of
a new-prime letter has fewer than `t/4` distinct prime factors.  The explicit
threshold `a ≥ 8` is deliberately coarse but completely elementary. -/
theorem newPrime_upper_endpoint_primeFactors_card_lt_quarter
    {a p : ℕ} (ha : 8 ≤ a) (hp : Nat.Prime p)
    (htp : 2 ^ a < p) (hpt : p < 2 * 2 ^ a) :
    (2 * periodLcm (2 ^ a) + p).primeFactors.card < 2 ^ a / 4 := by
  let t := 2 ^ a
  let H := periodLcm t
  let y := 2 * H + p
  have htPos : 0 < t := by dsimp [t]; positivity
  have ht256 : 256 ≤ t := by
    change 2 ^ 8 ≤ 2 ^ a
    exact Nat.pow_le_pow_right (by norm_num) ha
  have htEq : t = 4 * 2 ^ (a - 2) := by
    dsimp [t]
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have htDiv : t / 4 = 2 ^ (a - 2) := by
    rw [htEq]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have htQuarterPos : 0 < t / 4 := by
    rw [htDiv]
    exact pow_pos (by norm_num) _
  have hyPos : 0 < y := by
    dsimp only [y]
    exact Nat.add_pos_right _ hp.pos
  have hrough :
      ∀ r : ℕ, Nat.Prime r → r ∣ y → t < r := by
    intro r hr hrdvd
    exact newPrime_lcmRay_endpoint_primeFactors_gt
      (q := 2) hp (by simpa [t] using htp) hr
        (by simpa [y, H] using hrdvd)
  have hcardPower : (t + 1) ^ y.primeFactors.card ≤ y :=
    rough_primeFactors_card_power_le hyPos hrough
  have hHeight : H < 2 ^ (2 * t - 12) := by
    simpa [H, t] using
      (periodLcm_pow_two_lt_two_pow_guardTwelve (by omega : 4 ≤ a))
  have hHeightCoarse : H < 2 ^ (2 * t - 2) := by
    exact hHeight.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hTwoHeight : 2 * H < 2 ^ (2 * t - 1) := by
    calc
      2 * H < 2 * 2 ^ (2 * t - 2) :=
        Nat.mul_lt_mul_of_pos_left hHeightCoarse (by omega)
      _ = 2 ^ (2 * t - 1) := by
        rw [show 2 * t - 1 = (2 * t - 2) + 1 by omega, pow_succ]
        ring
  have hTwoT : 2 * t ≤ 2 ^ (2 * t - 1) := by
    have hpowAux : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            n + 2 ≤ 2 * (n + 1) := by omega
            _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
            _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]
    have hpow := hpowAux (2 * t - 1)
    omega
  have hptT : p < 2 * t := by simpa [t] using hpt
  have hpPow : p < 2 ^ (2 * t - 1) := hptT.trans_le hTwoT
  have hyPow : y < 2 ^ (2 * t) := by
    calc
      y = 2 * H + p := rfl
      _ < 2 ^ (2 * t - 1) + 2 ^ (2 * t - 1) :=
        Nat.add_lt_add hTwoHeight hpPow
      _ = 2 ^ (2 * t) := by
        calc
          2 ^ (2 * t - 1) + 2 ^ (2 * t - 1) =
              2 * 2 ^ (2 * t - 1) := by ring
          _ = 2 ^ ((2 * t - 1) + 1) := by
            simp [pow_succ, Nat.mul_comm]
          _ = 2 ^ (2 * t) := by congr 1; omega
  have hmulExp : 8 * (t / 4) = 2 * t := by
    rw [htDiv, htEq]
    ring
  have hbase : 2 ^ 8 < t + 1 := by omega
  have hbasePow : 2 ^ (2 * t) < (t + 1) ^ (t / 4) := by
    calc
      2 ^ (2 * t) = (2 ^ 8) ^ (t / 4) := by
        rw [← pow_mul, hmulExp]
      _ < (t + 1) ^ (t / 4) :=
        Nat.pow_lt_pow_left hbase (Nat.ne_of_gt htQuarterPos)
  by_contra hnot
  have hquarterLe : t / 4 ≤ y.primeFactors.card :=
    Nat.le_of_not_gt hnot
  have hmono :
      (t + 1) ^ (t / 4) ≤ (t + 1) ^ y.primeFactors.card :=
    Nat.pow_le_pow_right (by omega) hquarterLe
  omega

/-- Quantitative resolution of the actual exponent-one frontier: for `a ≥ 8`,
every new-prime coefficient `c` in `(2^a,2^(a+1))` satisfies `H < 4*c`,
where `H = periodLcm (2^a)`.  Equivalently, `c > H/4`.

The extra quarter-height margin comes from the elementary fact that the
coprime divisors `t` and `t-1` have product dividing `H`.  Thus `p < 2*t ≤ H`,
and the rough-totient estimate
`c > (3/4)*(2*H+p) - (H+p) = H/2-p/4` is greater than `H/4`. -/
theorem periodLcm_lt_four_mul_lcmRayArithmeticLetter_newPrime
    {a p : ℕ} (ha : 8 ≤ a) (hp : Nat.Prime p)
    (htp : 2 ^ a < p) (hpt : p < 2 * 2 ^ a) :
    (periodLcm (2 ^ a) : ℤ) <
      4 * lcmRayArithmeticLetter (2 ^ a) p := by
  let t := 2 ^ a
  let H := periodLcm t
  let y := 2 * H + p
  have htPos : 0 < t := by dsimp [t]; positivity
  have ht256 : 256 ≤ t := by
    change 2 ^ 8 ≤ 2 ^ a
    exact Nat.pow_le_pow_right (by norm_num) ha
  have hptT : p < 2 * t := by simpa [t] using hpt
  have htDvd : t ∣ H := by
    dsimp [H]
    exact dvd_periodLcm (by omega) le_rfl
  have htPredDvd : t - 1 ∣ H := by
    dsimp [H]
    exact dvd_periodLcm (by omega) (by omega)
  have htCoprimePred : Nat.Coprime t (t - 1) := by
    rw [Nat.coprime_self_sub_right (by omega : 1 ≤ t)]
    simp
  have htProdDvd : t * (t - 1) ∣ H :=
    htCoprimePred.mul_dvd_of_dvd_of_dvd htDvd htPredDvd
  have htProdLeH : t * (t - 1) ≤ H :=
    Nat.le_of_dvd (by dsimp [H]; exact periodLcm_pos t) htProdDvd
  have htwoTLeH : 2 * t ≤ H := by
    calc
      2 * t = t * 2 := by omega
      _ ≤ t * (t - 1) := Nat.mul_le_mul_left t (by omega)
      _ ≤ H := htProdLeH
  have hpH : p < H := hptT.trans_le htwoTLeH
  have hyPos : 0 < y := by
    dsimp only [y]
    exact Nat.add_pos_right _ hp.pos
  have hrough :
      ∀ r : ℕ, Nat.Prime r → r ∣ y → t < r := by
    intro r hr hrdvd
    exact newPrime_lcmRay_endpoint_primeFactors_gt
      (q := 2) hp (by simpa [t] using htp) hr
        (by simpa [y, H] using hrdvd)
  have hcard : y.primeFactors.card < t / 4 := by
    simpa [y, H, t] using
      (newPrime_upper_endpoint_primeFactors_card_lt_quarter ha hp htp hpt)
  have hfourCard : 4 * y.primeFactors.card < t + 1 := by
    have htEq : t = 4 * 2 ^ (a - 2) := by
      dsimp [t]
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have htDiv : t / 4 = 2 ^ (a - 2) := by
      rw [htEq]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    omega
  have hfrac :
      (y.primeFactors.card : ℚ) / ((t + 1 : ℕ) : ℚ) < 1 / 4 := by
    have hden : (0 : ℚ) < ((t + 1 : ℕ) : ℚ) := by positivity
    apply (div_lt_iff₀ hden).2
    have hfourCardQ :
        (4 : ℚ) * (y.primeFactors.card : ℚ) <
          ((t + 1 : ℕ) : ℚ) := by
      exact_mod_cast hfourCard
    nlinarith
  have htotientLower :=
    totient_rational_lower_bound_of_primeFactors_gt hyPos hrough
  have hthreeQuarter :
      (3 / 4 : ℚ) * (y : ℚ) < (Nat.totient y : ℚ) := by
    have hdensity :
        (3 / 4 : ℚ) <
          1 - (y.primeFactors.card : ℚ) / ((t + 1 : ℕ) : ℚ) := by
      linarith
    have hmul := mul_lt_mul_of_pos_left hdensity (by positivity : (0 : ℚ) < y)
    nlinarith
  have hphiLowerEndpoint :
      (Nat.totient (H + p) : ℚ) ≤ ((H + p : ℕ) : ℚ) := by
    exact_mod_cast (Nat.totient_le (H + p))
  have hpHQ : (p : ℚ) < (H : ℚ) := by exact_mod_cast hpH
  have hquarterGapQ :
      (H : ℚ) <
        4 * ((Nat.totient y : ℚ) - (Nat.totient (H + p) : ℚ)) := by
    dsimp [y] at hthreeQuarter
    push_cast at hthreeQuarter hphiLowerEndpoint
    nlinarith
  have hquarterGapZ :
      (H : ℤ) <
        4 * ((Nat.totient y : ℤ) - (Nat.totient (H + p) : ℤ)) := by
    exact_mod_cast hquarterGapQ
  have hnd : ¬p ∣ periodLcm (2 ^ a) :=
    newPrime_not_dvd_periodLcm hp htp
  rw [lcmRayArithmeticLetter, if_neg hnd]
  unfold deltaTotient
  rw [show periodLcm (2 ^ a) + p + periodLcm (2 ^ a) = y by
    dsimp [y, H, t]; omega]
  simpa [H, t] using hquarterGapZ

/-- Rationally normalized form of the quarter-height frontier bound. -/
theorem quarter_periodLcm_lt_lcmRayArithmeticLetter_newPrime
    {a p : ℕ} (ha : 8 ≤ a) (hp : Nat.Prime p)
    (htp : 2 ^ a < p) (hpt : p < 2 * 2 ^ a) :
    ((periodLcm (2 ^ a) : ℚ) / 4) <
      (lcmRayArithmeticLetter (2 ^ a) p : ℚ) := by
  have hstrong :=
    periodLcm_lt_four_mul_lcmRayArithmeticLetter_newPrime ha hp htp hpt
  have hstrongQ :
      (periodLcm (2 ^ a) : ℚ) <
        4 * (lcmRayArithmeticLetter (2 ^ a) p : ℚ) := by
    exact_mod_cast hstrong
  nlinarith

/-- In particular, every actual exponent-one new-prime coefficient is
strictly positive once the power-of-two height reaches `2^8`. -/
theorem lcmRayArithmeticLetter_newPrime_pos
    {a p : ℕ} (ha : 8 ≤ a) (hp : Nat.Prime p)
    (htp : 2 ^ a < p) (hpt : p < 2 * 2 ^ a) :
    0 < lcmRayArithmeticLetter (2 ^ a) p := by
  have hquarter :=
    quarter_periodLcm_lt_lcmRayArithmeticLetter_newPrime ha hp htp hpt
  have hHpos : (0 : ℚ) < (periodLcm (2 ^ a) : ℚ) := by
    exact_mod_cast (periodLcm_pos (2 ^ a))
  have hletterQ :
      (0 : ℚ) < (lcmRayArithmeticLetter (2 ^ a) p : ℚ) := by
    nlinarith
  exact_mod_cast hletterQ

/-- Every nondivisor coefficient in the short window has the uniform
quarter-height lower bound.  The prime-power classification combines the
higher-power predecessor estimate with the exponent-one frontier. -/
theorem periodLcm_lt_four_mul_lcmRayArithmeticLetter_of_not_dvd
    {a j : ℕ} (ha : 8 ≤ a) (hjpos : 0 < j)
    (hjlt : j < 2 * 2 ^ a)
    (hnd : ¬j ∣ periodLcm (2 ^ a)) :
    (periodLcm (2 ^ a) : ℤ) <
      4 * lcmRayArithmeticLetter (2 ^ a) j := by
  let t := 2 ^ a
  obtain ⟨p, k, hp, hj, htj⟩ :=
    eq_prime_pow_of_not_dvd_periodLcm (t := t) hjpos
      (by simpa [t] using hjlt) (by simpa [t] using hnd)
  have hkPos : 0 < k := by
    by_contra hnot
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hnot
    have hjOne : j = 1 := by simpa [hkZero] using hj
    have htPos : 0 < t := by dsimp [t]; positivity
    omega
  by_cases hkOne : k = 1
  · have hjp : j = p := by simpa [hkOne] using hj
    have htp : 2 ^ a < p := by simpa [t, hjp] using htj
    have hpt : p < 2 * 2 ^ a := by simpa [hjp] using hjlt
    simpa [hjp] using
      (periodLcm_lt_four_mul_lcmRayArithmeticLetter_newPrime
        ha hp htp hpt)
  · have hkTwo : 2 ≤ k := by omega
    have htq : 2 ^ a < p ^ k := by simpa [t, hj] using htj
    have hqt : p ^ k < 2 * 2 ^ a := by simpa [hj] using hjlt
    have hndPow : ¬p ^ k ∣ periodLcm (2 ^ a) := by simpa [hj] using hnd
    simpa [hj] using
      (lcmRayArithmeticLetter_foreignPrimePower_bracket
        ha hp hkTwo htq hqt hndPow).1

/-- Every coefficient in the complete short window is positive.  Divisor
offsets use the relative Euler product, while the sparse nondivisor
complement is a prime power and is handled by the predecessor/new-prime
frontier. -/
theorem lcmRayArithmeticLetter_pos_of_lt_two_mul
    {a j : ℕ} (ha : 8 ≤ a) (hjpos : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    0 < lcmRayArithmeticLetter (2 ^ a) j := by
  let t := 2 ^ a
  change 0 < lcmRayArithmeticLetter t j
  by_cases hdvd : j ∣ periodLcm t
  · exact lcmRayArithmeticLetter_divisor_pos ha hjpos
      (by simpa [t] using hdvd)
  · obtain ⟨p, k, hp, hj, htj⟩ :=
      eq_prime_pow_of_not_dvd_periodLcm (t := t) hjpos
        (by simpa [t] using hjlt) hdvd
    have hkPos : 0 < k := by
      by_contra hnot
      have hkZero : k = 0 := Nat.eq_zero_of_not_pos hnot
      have hjOne : j = 1 := by simpa [hkZero] using hj
      have htPos : 0 < t := by dsimp [t]; positivity
      omega
    by_cases hkOne : k = 1
    · have hjp : j = p := by simpa [hkOne] using hj
      have htp : 2 ^ a < p := by simpa [t, hjp] using htj
      have hpt : p < 2 * 2 ^ a := by simpa [hjp] using hjlt
      simpa [t, hjp] using
        (lcmRayArithmeticLetter_newPrime_pos ha hp htp hpt)
    · have hkTwo : 2 ≤ k := by omega
      have htq : 2 ^ a < p ^ k := by simpa [t, hj] using htj
      have hqt : p ^ k < 2 * 2 ^ a := by simpa [hj] using hjlt
      have hnd : ¬p ^ k ∣ periodLcm (2 ^ a) := by
        simpa [t, hj] using hdvd
      have hlower :=
        (lcmRayArithmeticLetter_foreignPrimePower_bracket
          ha hp hkTwo htq hqt hnd).1
      have hHPos : (0 : ℤ) < (periodLcm (2 ^ a) : ℤ) := by
        exact_mod_cast periodLcm_pos (2 ^ a)
      have hposPow :
          (0 : ℤ) < lcmRayArithmeticLetter (2 ^ a) (p ^ k) := by
        omega
      simpa [t, hj] using hposPow

/-- In the short power-two window, the even initial letter in the exact
three-letter half-correction formula is a *positive* multiple of its own
Euler totient.  This is the strongest direct factorization supplied by the
new terminal divisor: it rewrites the half-correction using the two following
letters and a positive arithmetic quotient, without asserting the missing
state/carry anti-concentration. -/
theorem exists_pos_terminalTotient_factorization_of_actualOddHalfCorrection
    {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 < 2 * 2 ^ a) :
    ∃ k : ℤ, 0 < k ∧
      lcmRayArithmeticLetter (2 ^ a) (2 * q + 2) =
        (Nat.totient (2 * q + 2) : ℤ) * k ∧
      2 * actualOddHalfCorrection a q =
        diagonalWindowIncrement (2 ^ a) (2 * q + 3) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 4) -
            2 * (Nat.totient (2 * q + 2) : ℤ) * k := by
  have hjpos : 0 < 2 * q + 2 := by omega
  have hjeven : Even (2 * q + 2) := by
    exact ⟨q + 1, by omega⟩
  have hdvd :=
    totient_dvd_lcmRayArithmeticLetter_of_even_short_pow_two
      (a := a) hjpos hjeven hshort
  obtain ⟨k, hk⟩ := hdvd
  have hdpos :
      0 < lcmRayArithmeticLetter (2 ^ a) (2 * q + 2) :=
    lcmRayArithmeticLetter_pos_of_lt_two_mul ha hjpos hshort
  have hphipos : (0 : ℤ) < (Nat.totient (2 * q + 2) : ℤ) := by
    exact_mod_cast Nat.totient_pos.mpr hjpos
  have hprod :
      0 < (Nat.totient (2 * q + 2) : ℤ) * k := by
    rwa [← hk]
  have hkpos : 0 < k := by
    rcases (mul_pos_iff.mp hprod) with hboth | hboth
    · exact hboth.2
    · exact (not_lt_of_ge hphipos.le hboth.1).elim
  have hmiddle :
      diagonalWindowIncrement (2 ^ a) (2 * q + 2) =
        (Nat.totient (2 * q + 2) : ℤ) * k := by
    rw [diagonalWindowIncrement_eq_lcmRayArithmeticLetter]
    exact hk
  have hthree :=
    two_mul_actualOddHalfCorrection_eq_three_diagonalWindowIncrements
      (a := a) (q := q) (show 2 ≤ a by omega)
  rw [hmiddle] at hthree
  refine ⟨k, hkpos, hk, ?_⟩
  calc
    2 * actualOddHalfCorrection a q =
        diagonalWindowIncrement (2 ^ a) (2 * q + 3) -
          2 * ((Nat.totient (2 * q + 2) : ℤ) * k) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 4) := hthree
    _ = diagonalWindowIncrement (2 ^ a) (2 * q + 3) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 4) -
            2 * (Nat.totient (2 * q + 2) : ℤ) * k := by ring

/-- Divisibility-only projection of the positive terminal factorization.  It
constrains the actual correction relative to its two neighbouring literal
letters, but deliberately makes no endpoint claim: the same middle factor
cancels in the existing two-rank carry recurrence. -/
theorem two_mul_totient_dvd_actualOddHalfCorrection_sub_following_pair
    {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 < 2 * 2 ^ a) :
    2 * (Nat.totient (2 * q + 2) : ℤ) ∣
      2 * actualOddHalfCorrection a q -
        diagonalWindowIncrement (2 ^ a) (2 * q + 3) -
        diagonalWindowIncrement (2 ^ a) (2 * q + 4) := by
  obtain ⟨k, _hkpos, _hletter, hcorrection⟩ :=
    exists_pos_terminalTotient_factorization_of_actualOddHalfCorrection
      ha hshort
  refine ⟨-k, ?_⟩
  rw [hcorrection]
  ring

/-- The three-letter correction formula is exactly compatible with two
steps of the affine carry recurrence.  Thus a terminal identity at odd rank
`q` propagates to the next odd rank after the state update
`u ↦ 4 * u + actualOddHalfCorrection a q`.  In particular, the positive
totient quotient exposed above cancels from this propagation and supplies no
independent corridor-escape inequality. -/
theorem two_mul_affineStep_eq_terminal_sub_carry_add_two
    {a q : ℕ} (ha : 2 ≤ a) {u z : ℤ}
    (hterminal :
      2 * u =
        diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
          carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
            (2 * q + 1)) :
    2 * (4 * u + actualOddHalfCorrection a q) =
      diagonalWindowIncrement (2 ^ a) (2 * q + 4) -
        carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
          (2 * q + 3) := by
  have hstepOne :
      carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
          (2 * q + 2) =
        2 * carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
            (2 * q + 1) -
          diagonalWindowIncrement (2 ^ a) (2 * q + 2) := by
    conv_lhs =>
      rw [show 2 * q + 2 = (2 * q + 1) + 1 by omega]
    change
      2 * carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
            (2 * q + 1) -
          deltaTotient (periodLcm (2 ^ a))
            (periodLcm (2 ^ a) + (2 * q + 1) + 1) =
        2 * carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
            (2 * q + 1) -
          diagonalWindowIncrement (2 ^ a) (2 * q + 2)
    unfold diagonalWindowIncrement deltaTotient
    have htop :
        periodLcm (2 ^ a) + (2 * q + 1) + 1 + periodLcm (2 ^ a) =
          2 * periodLcm (2 ^ a) + (2 * q + 2) := by omega
    have hbot :
        periodLcm (2 ^ a) + (2 * q + 1) + 1 =
          periodLcm (2 ^ a) + (2 * q + 2) := by omega
    rw [htop, hbot]
  have hstepTwo :
      carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
          (2 * q + 3) =
        2 * carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
            (2 * q + 2) -
          diagonalWindowIncrement (2 ^ a) (2 * q + 3) := by
    conv_lhs =>
      rw [show 2 * q + 3 = (2 * q + 2) + 1 by omega]
    change
      2 * carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
            (2 * q + 2) -
          deltaTotient (periodLcm (2 ^ a))
            (periodLcm (2 ^ a) + (2 * q + 2) + 1) =
        2 * carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
            (2 * q + 2) -
          diagonalWindowIncrement (2 ^ a) (2 * q + 3)
    unfold diagonalWindowIncrement deltaTotient
    have htop :
        periodLcm (2 ^ a) + (2 * q + 2) + 1 + periodLcm (2 ^ a) =
          2 * periodLcm (2 ^ a) + (2 * q + 3) := by omega
    have hbot :
        periodLcm (2 ^ a) + (2 * q + 2) + 1 =
          periodLcm (2 ^ a) + (2 * q + 3) := by omega
    rw [htop, hbot]
  have hcorrection :=
    two_mul_actualOddHalfCorrection_eq_three_diagonalWindowIncrements
      (a := a) (q := q) ha
  calc
    2 * (4 * u + actualOddHalfCorrection a q) =
        4 * (2 * u) + 2 * actualOddHalfCorrection a q := by ring
    _ = 4 *
          (diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
            carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
              (2 * q + 1)) +
        (diagonalWindowIncrement (2 ^ a) (2 * q + 3) -
          2 * diagonalWindowIncrement (2 ^ a) (2 * q + 2) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 4)) := by
      rw [hterminal, hcorrection]
    _ = diagonalWindowIncrement (2 ^ a) (2 * q + 4) -
        (2 *
            (2 * carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
                (2 * q + 1) -
              diagonalWindowIncrement (2 ^ a) (2 * q + 2)) -
          diagonalWindowIncrement (2 ^ a) (2 * q + 3)) := by ring
    _ = diagonalWindowIncrement (2 ^ a) (2 * q + 4) -
        carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
          (2 * q + 3) := by rw [← hstepOne, ← hstepTwo]

/-- Uniform quantitative lower bound for every coefficient in the complete
short window.  Divisor letters lose a factor `j < 2*t`; foreign prime powers
retain the stronger quarter-height estimate. -/
theorem periodLcm_lt_eight_mul_t_mul_lcmRayArithmeticLetter
    {a j : ℕ} (ha : 8 ≤ a) (hjpos : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    (periodLcm (2 ^ a) : ℤ) <
      8 * (2 ^ a : ℤ) * lcmRayArithmeticLetter (2 ^ a) j := by
  let t := 2 ^ a
  have htPos : (0 : ℤ) < (t : ℤ) := by dsimp [t]; positivity
  have hcPos : (0 : ℤ) < lcmRayArithmeticLetter t j := by
    simpa [t] using lcmRayArithmeticLetter_pos_of_lt_two_mul ha hjpos hjlt
  by_cases hdvd : j ∣ periodLcm t
  · have hdiv :=
      periodLcm_lt_four_mul_j_mul_lcmRayArithmeticLetter_divisor
        ha hjpos (by simpa [t] using hdvd)
    have hjBound : (4 : ℤ) * j ≤ 8 * t := by
      have hjltZ : (j : ℤ) < 2 * (t : ℤ) := by
        exact_mod_cast (by simpa [t] using hjlt)
      omega
    have hscale := mul_le_mul_of_nonneg_right hjBound hcPos.le
    have hdivT :
        (periodLcm t : ℤ) <
          4 * (j : ℤ) * lcmRayArithmeticLetter t j := by
      simpa [t] using hdiv
    exact hdivT.trans_le (by simpa [mul_assoc] using hscale)
  · have hforeign :=
      periodLcm_lt_four_mul_lcmRayArithmeticLetter_of_not_dvd
        ha hjpos hjlt (by simpa [t] using hdvd)
    have hfactor : (4 : ℤ) ≤ 8 * t := by omega
    have hscale := mul_le_mul_of_nonneg_right hfactor hcPos.le
    have hforeignT :
        (periodLcm t : ℤ) < 4 * lcmRayArithmeticLetter t j := by
      simpa [t] using hforeign
    exact hforeignT.trans_le (by simpa [mul_assoc] using hscale)

/-- The lower and upper endpoints belonging to a new-prime offset are
coprime.  Indeed their difference is the LCM height, which is coprime to the
new prime. -/
theorem newPrime_lcmRay_endpoints_coprime
    {t p : ℕ} (hp : Nat.Prime p) (htp : t < p) :
    Nat.Coprime (periodLcm t + p) (2 * periodLcm t + p) := by
  have hpH : Nat.Coprime p (periodLcm t) :=
    hp.coprime_iff_not_dvd.mpr (newPrime_not_dvd_periodLcm hp htp)
  have hlowerH : Nat.Coprime (periodLcm t + p) (periodLcm t) :=
    Nat.coprime_self_add_left.mpr hpH
  have hray :
      Nat.Coprime (periodLcm t + p)
        ((periodLcm t + p) + periodLcm t) :=
    Nat.coprime_self_add_right.mpr hlowerH
  rw [show 2 * periodLcm t + p =
    (periodLcm t + p) + periodLcm t by omega]
  exact hray

/-- Complete structural package for an exponent-one foreign letter.  Its
literal coefficient is the totient difference of two coprime integers whose
prime factors all lie beyond the LCM cutoff. -/
theorem lcmRayArithmeticLetter_newPrime_frontier
    {t p : ℕ} (hp : Nat.Prime p) (htp : t < p) :
    lcmRayArithmeticLetter t p =
        deltaTotient (periodLcm t) (periodLcm t + p) ∧
      Nat.Coprime (periodLcm t + p) (2 * periodLcm t + p) ∧
      (∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ periodLcm t + p → t < ℓ) ∧
      (∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ 2 * periodLcm t + p → t < ℓ) := by
  have hnd : ¬p ∣ periodLcm t := newPrime_not_dvd_periodLcm hp htp
  refine ⟨by simp [lcmRayArithmeticLetter, hnd],
    newPrime_lcmRay_endpoints_coprime hp htp, ?_, ?_⟩
  · intro ℓ hℓ hℓdvd
    exact newPrime_lcmRay_endpoint_primeFactors_gt
      (q := 1) hp htp hℓ (by simpa using hℓdvd)
  · intro ℓ hℓ hℓdvd
    exact newPrime_lcmRay_endpoint_primeFactors_gt
      (q := 2) hp htp hℓ hℓdvd

/-- Every coefficient actually used by a short arithmetic word inherits the
divisor/prime-power dichotomy. -/
theorem lcmDiagonalArithmeticWord_term_divisor_or_primePower
    {t L r : ℕ} (hr : r < L) (hshort : L < 2 * t) :
    ((r + 1) ∣ periodLcm t ∧
        lcmRayArithmeticLetter t (r + 1) =
          lcmDivisorRayLetter (periodLcm t) (r + 1)) ∨
      ∃ p k : ℕ, Nat.Prime p ∧ r + 1 = p ^ k ∧ t < r + 1 ∧
        lcmRayArithmeticLetter t (r + 1) =
          deltaTotient (periodLcm t) (periodLcm t + (r + 1)) := by
  exact lcmRayArithmeticLetter_divisor_or_primePower
    (j := r + 1) (by omega) (by omega)

/-- Binary-reversed finite word built from the quotient-scale divisor letters
and the sparse prime-power complement. -/
def lcmDiagonalArithmeticWord (t L : ℕ) : ℤ :=
  ∑ r ∈ Finset.range L,
    lcmRayArithmeticLetter t (r + 1) * 2 ^ (L - 1 - r)

/-- Exact identification of the arithmetic word with the actual diagonal
window discrepancy. -/
theorem lcmDiagonalArithmeticWord_eq_windowDiscrepancy (t L : ℕ) :
    lcmDiagonalArithmeticWord t L =
      windowDiscrepancy (periodLcm t) (periodLcm t) L := by
  unfold lcmDiagonalArithmeticWord windowDiscrepancy
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun z : ℤ => z * 2 ^ (L - 1 - r))
  rw [lcmRayArithmeticLetter_eq_deltaTotient]
  unfold deltaTotient
  rw [show periodLcm t + periodLcm t + 1 + r =
      periodLcm t + (r + 1) + periodLcm t by omega,
    show periodLcm t + 1 + r = periodLcm t + (r + 1) by omega]

/-- Appending one arithmetic letter is the exact binary affine recurrence
for the unreduced word. -/
theorem lcmDiagonalArithmeticWord_succ (t L : ℕ) :
    lcmDiagonalArithmeticWord t (L + 1) =
      2 * lcmDiagonalArithmeticWord t L +
        lcmRayArithmeticLetter t (L + 1) := by
  rw [lcmDiagonalArithmeticWord_eq_windowDiscrepancy,
    windowDiscrepancy_succ,
    ← lcmDiagonalArithmeticWord_eq_windowDiscrepancy]
  congr 1
  simpa [Nat.add_assoc] using
    (lcmRayArithmeticLetter_eq_deltaTotient t (L + 1)).symm

/-- Throughout the short power-of-two window, the positive appended letter
makes the unreduced word grow by strictly more than doubling. -/
theorem two_mul_lcmDiagonalArithmeticWord_lt_succ
    {a L : ℕ} (ha : 8 ≤ a) (hshort : L + 1 < 2 * 2 ^ a) :
    2 * lcmDiagonalArithmeticWord (2 ^ a) L <
      lcmDiagonalArithmeticWord (2 ^ a) (L + 1) := by
  rw [lcmDiagonalArithmeticWord_succ]
  have hletter :
      0 < lcmRayArithmeticLetter (2 ^ a) (L + 1) :=
    lcmRayArithmeticLetter_pos_of_lt_two_mul ha (by omega) hshort
  omega

/-- A finite arithmetic residue band at one LCM height. -/
def LcmDiagonalArithmeticKill (t L : ℕ) : Prop :=
  let H := periodLcm t
  (2 * H + L + 2 : ℤ) < lcmDiagonalArithmeticWord t L % 2 ^ L ∧
    lcmDiagonalArithmeticWord t L % 2 ^ L <
      2 ^ L - (2 * H + L + 2)

/-- The quotient-scale arithmetic band is exactly a certified kill on the
actual LCM diagonal. -/
theorem lcmDiagonalArithmeticKill_iff_certifiedKill (t L : ℕ) :
    LcmDiagonalArithmeticKill t L ↔
      certifiedKill (periodLcm t) (periodLcm t) L := by
  unfold LcmDiagonalArithmeticKill certifiedKill
  rw [lcmDiagonalArithmeticWord_eq_windowDiscrepancy]
  omega

/-! ## Identification with the adjacent-suffix / fresh-loss surface -/

/-- The quotient-scale arithmetic word is the same signed binary window used
by `diagonalWindowResidue`.  This is the exact bridge from the short-word
producer to the older adjacent-suffix and fresh-loss machinery; the two
surfaces differ only in which safe interval they ask the common residue to
occupy. -/
theorem lcmDiagonalArithmeticWord_emod_eq_diagonalWindowResidue
    (t L : ℕ) :
    lcmDiagonalArithmeticWord t L % 2 ^ L =
      diagonalWindowResidue t L := by
  rw [lcmDiagonalArithmeticWord_eq_windowDiscrepancy]
  unfold windowDiscrepancy diagonalWindowResidue windowNumerator
  push_cast
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The symmetric residue surface is exactly the actual-LCM arithmetic kill;
the two modules expose different names for the same modular word. -/
theorem lcmDiagonalArithmeticKill_iff_diagonalSymmetricResidueCert
    (t L : ℕ) :
    LcmDiagonalArithmeticKill t L ↔ diagonalSymmetricResidueCert t L := by
  unfold LcmDiagonalArithmeticKill diagonalSymmetricResidueCert
  rw [lcmDiagonalArithmeticWord_emod_eq_diagonalWindowResidue]

/-- The symmetric short arithmetic band is stronger than the asymmetric
fresh-loss band at the same actual LCM height.  Thus every arithmetic kill
can be consumed directly by the adjacent-suffix/full-target proof cone. -/
theorem diagonalFreshLossResidueCert_of_lcmDiagonalArithmeticKill
    {t L : ℕ} (hkill : LcmDiagonalArithmeticKill t L) :
    diagonalFreshLossResidueCert t L := by
  unfold LcmDiagonalArithmeticKill at hkill
  rw [lcmDiagonalArithmeticWord_emod_eq_diagonalWindowResidue] at hkill
  unfold diagonalFreshLossResidueCert
  constructor
  · omega
  · exact hkill.2

/-- One coefficient-arithmetic band already rules out an integer hit by the
actual LCM tail orbit at that exponent. -/
theorem actualLcmTailOrbit_notMem_int_of_arithmeticKill
    {a L : ℕ} (hkill : LcmDiagonalArithmeticKill (2 ^ a) L) :
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ) := by
  have hcert :
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L :=
    (lcmDiagonalArithmeticKill_iff_certifiedKill (2 ^ a) L).mp hkill
  simpa only [actualLcmTailOrbit, actualLcmHeight, two_mul] using
    (tail_diff_notMem_int_of_certifiedKill hcert)

/-- Strictly stronger producer than unrestricted actual-orbit
nonintegrality: certificates must occur inside the short window where every
nondivisor coefficient is a prime power. -/
def PowerTwoActualLcmShortArithmeticKillSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
    LcmDiagonalArithmeticKill (2 ^ a) L

/-- The existing odd-guard half-word producer already pays the stronger
symmetric margin.  Projecting that receipt here closes the routing gap from
the adjacent-suffix cone to the short actual-LCM arithmetic endpoint. -/
theorem powerTwoActualLcmShortArithmeticKillSupply_of_oddGuardHalfWordBand
    (hsupply : PowerTwoOddGuardHalfWordBandSupply) :
    PowerTwoActualLcmShortArithmeticKillSupply := by
  intro a₀
  obtain ⟨a, q, ha, hdepth, hlo, hhi⟩ := hsupply (max 4 a₀)
  have ha4 : 4 ≤ a := (le_max_left 4 a₀).trans
    ((le_max_right 2 (max 4 a₀)).trans ha)
  have ha₀ : a₀ ≤ a := (le_max_right 4 a₀).trans
    ((le_max_right 2 (max 4 a₀)).trans ha)
  rcases diagonalSymmetricResidueCert_or_of_powerTwo_oddGuard_halfWordBand
      (show 2 ≤ a by omega) hdepth hlo hhi with hcert | hcert
  · refine ⟨a, 2 * q + 1, ha₀, ?_, ?_⟩
    · rw [← hdepth]
      exact oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_lt_two_mul ha4
    · exact (lcmDiagonalArithmeticKill_iff_diagonalSymmetricResidueCert
        (2 ^ a) (2 * q + 1)).2 hcert
  · refine ⟨a, 1 + (2 * q + 1), ha₀, ?_, ?_⟩
    · rw [← hdepth]
      simpa only [Nat.add_comm] using
        oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_succ_lt_two_mul ha4
    · exact (lcmDiagonalArithmeticKill_iff_diagonalSymmetricResidueCert
        (2 ^ a) (1 + (2 * q + 1))).2 hcert

/-- The cofinal short-word producer therefore also feeds the landed
fresh-loss projection supply.  This connects the actual-orbit route to the
adjacent-suffix, jump-cocycle, and signed-margin reductions without changing
the stronger short-window obligation. -/
theorem diagonalFreshLossProjectionSupply_of_shortArithmeticKill
    (hsupply : PowerTwoActualLcmShortArithmeticKillSupply) :
    DiagonalFreshLossProjectionSupply := by
  intro t₀
  obtain ⟨a, L, ha, _hshort, hkill⟩ := hsupply t₀
  have hat : a < 2 ^ a := Nat.lt_two_pow_self
  exact ⟨2 ^ a, by omega, L,
    diagonalFreshLossResidueCert_of_lcmDiagonalArithmeticKill hkill⟩

/-- The short coefficient-arithmetic producer feeds the landed exact
actual-LCM nonintegrality endpoint. -/
theorem actualLcmOrbitNonintegralitySupply_of_shortArithmeticKill
    (hsupply : PowerTwoActualLcmShortArithmeticKillSupply) :
    PowerTwoActualLcmOrbitNonintegralitySupply := by
  intro a₀
  obtain ⟨a, L, ha, _hshort, hkill⟩ := hsupply a₀
  exact ⟨a, ha, actualLcmTailOrbit_notMem_int_of_arithmeticKill hkill⟩

#print axioms totient_mul_eq_overlapFactor_mul
#print axioms lcmDiagonalArithmeticKill_iff_diagonalSymmetricResidueCert
#print axioms powerTwoActualLcmShortArithmeticKillSupply_of_oddGuardHalfWordBand
#print axioms totient_le_totientOverlapFactor
#print axioms exists_saturated_prime_of_overlapExcess_ne_zero
#print axioms lcmDivisorRayLetter_eq_cleanCore_add_overlapExcess
#print axioms deltaTotient_divisor_ray_eq_overlapLetter
#print axioms lcmDivisorRayLetter_eq_clean_delta
#print axioms diagonalWindowIncrement_eq_lcmRayArithmeticLetter
#print axioms totient_dvd_lcmRayArithmeticLetter_of_dvd
#print axioms even_short_offset_dvd_periodLcm_pow_two
#print axioms totient_dvd_lcmRayArithmeticLetter_of_even_short_pow_two
#print axioms lcmRayArithmeticLetter_divisor_or_primePower
#print axioms foreignPrimePower_predecessor_dvd_periodLcm
#print axioms deltaTotient_foreignPrimePower_ray_eq_predecessorLetter
#print axioms foreignPrimePower_predecessor_quotient_lt
#print axioms lcmRayArithmeticLetter_divisor_or_predecessorPrimePower
#print axioms newPrime_not_dvd_periodLcm
#print axioms newPrime_lcmRay_endpoint_primeFactors_gt
#print axioms rough_primeFactors_card_power_le
#print axioms totient_rational_lower_bound_of_primeFactors_gt
#print axioms three_quarters_lt_relativeEulerProduct_of_lt_two_pow
#print axioms periodLcm_lt_four_mul_j_mul_lcmRayArithmeticLetter_divisor
#print axioms lcmRayArithmeticLetter_divisor_pos
#print axioms newPrime_upper_endpoint_primeFactors_card_lt_quarter
#print axioms lcmRayArithmeticLetter_newPrime_pos
#print axioms periodLcm_lt_four_mul_lcmRayArithmeticLetter_of_not_dvd
#print axioms lcmRayArithmeticLetter_pos_of_lt_two_mul
#print axioms exists_pos_terminalTotient_factorization_of_actualOddHalfCorrection
#print axioms two_mul_totient_dvd_actualOddHalfCorrection_sub_following_pair
#print axioms two_mul_affineStep_eq_terminal_sub_carry_add_two
#print axioms periodLcm_lt_eight_mul_t_mul_lcmRayArithmeticLetter
#print axioms newPrime_lcmRay_endpoints_coprime
#print axioms lcmRayArithmeticLetter_newPrime_frontier
#print axioms lcmDiagonalArithmeticWord_eq_windowDiscrepancy
#print axioms lcmDiagonalArithmeticWord_succ
#print axioms two_mul_lcmDiagonalArithmeticWord_lt_succ
#print axioms lcmDiagonalArithmeticWord_emod_eq_diagonalWindowResidue
#print axioms diagonalFreshLossResidueCert_of_lcmDiagonalArithmeticKill
#print axioms diagonalFreshLossProjectionSupply_of_shortArithmeticKill
#print axioms actualLcmTailOrbit_notMem_int_of_arithmeticKill
#print axioms actualLcmOrbitNonintegralitySupply_of_shortArithmeticKill

end PowerTwoOddWindowAffine
end DiagonalFreshLossBridge
end Erdos257PeriodNoncollapse
