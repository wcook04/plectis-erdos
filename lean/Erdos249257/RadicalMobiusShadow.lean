import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.NatAbs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Radical Möbius shadows for Erdős #249

This file formalises the finite algebraic part of the corrected T6 development.  It
keeps three objects separate:

* `mobiusNumerator r` is the integral common-denominator numerator `M_r`;
* `baseMobiusShadow r = M_r / (2^r - 1)` is the unscaled radical shadow `B(r)`;
* `numericMobiusShadow H` divides `B(rad H)` by `rad H`, so multiplication by
  `H` introduces the additional scale `H / rad H`.

Accordingly, `baseMobiusShadow_den` computes the reduced denominator before
that extra scale is applied.  The file does not claim that the scaled shadow
has the same denominator, and it makes no infinite-series or channel-survival
claim.
-/

open scoped BigOperators

namespace Erdos249257.RadicalMobiusShadow

private theorem sum_powerset_singleton {α β : Type*} [DecidableEq α]
    [AddCommMonoid β] (a : α) (f : Finset α → β) :
    ∑ t ∈ ({a} : Finset α).powerset, f t = f ∅ + f {a} := by
  rw [show ({a} : Finset α) = insert a ∅ by rfl,
    Finset.sum_powerset_insert (by simp)]
  simp

/-- The Mersenne denominator at exponent `n`. -/
def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

/-- The squarefree kernel used by the numeric shadow: the product of the
distinct prime factors of `n`.  For `n = 0` this convention gives `1`; all
development-facing scaling theorems assume `0 < n`. -/
def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem squarefreeKernel_primeFactors (n : ℕ) :
    (squarefreeKernel n).primeFactors = n.primeFactors := by
  unfold squarefreeKernel
  exact Nat.primeFactors_prod fun p hp ↦ Nat.prime_of_mem_primeFactors hp

@[simp]
theorem squarefreeKernel_idem (n : ℕ) :
    squarefreeKernel (squarefreeKernel n) = squarefreeKernel n := by
  unfold squarefreeKernel
  rw [Nat.primeFactors_prod
    (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)]

theorem squarefreeKernel_pos (n : ℕ) : 0 < squarefreeKernel n := by
  unfold squarefreeKernel
  exact Finset.prod_pos fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos

theorem squarefreeKernel_dvd (n : ℕ) : squarefreeKernel n ∣ n := by
  exact Nat.prod_primeFactors_dvd n

/-- The canonical kernel is squarefree, including at the convention
`squarefreeKernel 0 = 1`. -/
theorem squarefreeKernel_squarefree (n : ℕ) :
    Squarefree (squarefreeKernel n) := by
  unfold squarefreeKernel
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

/-- Away from the exceptional zero convention, taking the squarefree kernel
preserves exactly the prime divisors. -/
theorem prime_dvd_squarefreeKernel_iff
    {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    p ∣ squarefreeKernel n ↔ p ∣ n := by
  constructor
  · intro hpk
    have hmem : p ∈ (squarefreeKernel n).primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero (squarefreeKernel_pos n).ne').2
        ⟨hp, hpk⟩
    rw [squarefreeKernel_primeFactors] at hmem
    exact ((Nat.mem_primeFactors_of_ne_zero hn).1 hmem).2
  · intro hpn
    have hmem : p ∈ n.primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero hn).2 ⟨hp, hpn⟩
    rw [← squarefreeKernel_primeFactors] at hmem
    exact ((Nat.mem_primeFactors_of_ne_zero
      (squarefreeKernel_pos n).ne').1 hmem).2

/-- The integral numerator, written as its squarefree-divisor expansion.

For `s ⊆ primeFactors(r)`, put `d = ∏ p ∈ s, p`.  Then the summand is
`(-1)^|s| (r/d) ((2^r-1)/(2^d-1))`.  This is exactly the nonzero part of
`Σ_{d ∣ r} μ(d) (r/d) ((2^r-1)/(2^d-1))`: nonsquarefree divisors have
Möbius coefficient zero.  The subset form makes that finite support explicit
and keeps the definition executable without factoring irrelevant divisors. -/
def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)

/-- The unscaled radical shadow `B(r) = M_r / (2^r - 1)`. -/
def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)

/-- The numeric shadow at an arbitrary scale.  By construction it only sees
the distinct prime factors of `H`. -/
def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)

/-- Exact radical reduction: repeated prime powers do not change the numeric
Möbius shadow. -/
theorem numericMobiusShadow_radical (H : ℕ) :
    numericMobiusShadow H = numericMobiusShadow (squarefreeKernel H) := by
  simp [numericMobiusShadow]

/-- Scaling by `H` is exactly scaling the unscaled radical shadow by
`H / rad(H)`.  This theorem deliberately leaves `B(r)` reduced separately;
the factor `H / r` may cause further cancellation. -/
theorem scaledMobiusShadow_eq_radicalBase (H : ℕ) (_hH : 0 < H) :
    (H : ℚ) * numericMobiusShadow H =
      ((H / squarefreeKernel H : ℕ) : ℚ) *
        baseMobiusShadow (squarefreeKernel H) := by
  have hr0 : (squarefreeKernel H : ℚ) ≠ 0 := by
    exact_mod_cast (squarefreeKernel_pos H).ne'
  have hmul : H / squarefreeKernel H * squarefreeKernel H = H :=
    Nat.div_mul_cancel (squarefreeKernel_dvd H)
  have hcast : (H : ℚ) =
      ((H / squarefreeKernel H : ℕ) : ℚ) * (squarefreeKernel H : ℚ) := by
    exact_mod_cast hmul.symm
  rw [numericMobiusShadow, hcast]
  field_simp

/-- The development's scaled formula with the numerator and Mersenne denominator
displayed explicitly. -/
theorem scaledMobiusShadow_eq_radicalNumerator (H : ℕ) (hH : 0 < H) :
    (H : ℚ) * numericMobiusShadow H =
      ((H / squarefreeKernel H : ℕ) : ℚ) *
        Rat.divInt (mobiusNumerator (squarefreeKernel H))
          (mersenne (squarefreeKernel H) : ℤ) := by
  simpa [baseMobiusShadow] using scaledMobiusShadow_eq_radicalBase H hH

/-- Exact reduced denominator of the unscaled shadow.  This is the generic
gcd formula in T6; no coprimality or channel-survival hypothesis is hidden. -/
theorem baseMobiusShadow_den (r : ℕ) (hr : 0 < r) :
    (baseMobiusShadow r).den =
      mersenne r / (mobiusNumerator r).natAbs.gcd (mersenne r) := by
  have hmersenne : mersenne r ≠ 0 := by
    simp only [mersenne, Nat.sub_ne_zero_iff_lt]
    exact Nat.one_lt_two_pow hr.ne'
  rw [baseMobiusShadow, Rat.den_divInt, if_neg]
  · simp only [Int.natAbs_natCast, Int.gcd_eq_natAbs]
    rw [Nat.gcd_comm]
  · exact Int.natCast_ne_zero.mpr hmersenne

/-- A reusable corollary: a kernel-checked gcd certificate immediately gives
the displayed reduced denominator. -/
theorem baseMobiusShadow_den_of_gcd_eq (r g : ℕ) (hr : 0 < r)
    (hgcd : (mobiusNumerator r).natAbs.gcd (mersenne r) = g) :
    (baseMobiusShadow r).den = mersenne r / g := by
  rw [baseMobiusShadow_den r hr, hgcd]

/-! ## Prime-shape algebra -/

/-- For a prime radical there are only the empty and singleton subsets, so
the Möbius numerator is `p(2^p-1)-1`. -/
theorem mobiusNumerator_prime {p : ℕ} (hp : p.Prime) :
    mobiusNumerator p = (p : ℤ) * (mersenne p : ℤ) - 1 := by
  rw [mobiusNumerator, hp.primeFactors, sum_powerset_singleton]
  simp [mersenne, hp.ne_zero]
  ring

/-- The prime numerator is coprime to its Mersenne denominator. -/
theorem mobiusNumerator_prime_gcd {p : ℕ} (hp : p.Prime) :
    (mobiusNumerator p).natAbs.gcd (mersenne p) = 1 := by
  rw [mobiusNumerator_prime hp]
  have hDpos : 0 < mersenne p := by
    simp only [mersenne, Nat.sub_pos_iff_lt]
    exact Nat.one_lt_two_pow hp.ne_zero
  have hone : 1 ≤ p * mersenne p :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hDpos.ne')
  have habs : ((p : ℤ) * (mersenne p : ℤ) - 1).natAbs =
      p * mersenne p - 1 := by
    rw [← Int.natCast_mul, ← Int.natCast_one,
      Int.natAbs_natCast_sub_natCast_of_ge hone]
  rw [habs]
  have hcopProd : (p * mersenne p - 1).Coprime (p * mersenne p) := by
    rw [Nat.coprime_self_sub_left hone]
    simp
  have hcopD : (p * mersenne p - 1).Coprime (mersenne p) :=
    hcopProd.of_dvd_right (dvd_mul_left (mersenne p) p)
  exact hcopD.gcd_eq_one

/-- Exact prime-radical denominator from the generic gcd formula. -/
theorem baseMobiusShadow_den_prime {p : ℕ} (hp : p.Prime) :
    (baseMobiusShadow p).den = mersenne p := by
  rw [baseMobiusShadow_den p hp.pos, mobiusNumerator_prime_gcd hp, Nat.div_one]

/-- The four-term numerator expansion for a twice-prime radical.  This is the
exact algebraic fixture used before proving the gcd is `3`; the natural
quotients are exact because `3 = 2^2-1` and `2^p-1` divide `2^(2p)-1`. -/
theorem mobiusNumerator_twicePrime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    mobiusNumerator (2 * p) =
      ((2 * p : ℕ) : ℤ) * (mersenne (2 * p) : ℤ) -
        (p : ℤ) * ((mersenne (2 * p) / 3 : ℕ) : ℤ) -
          2 * ((mersenne (2 * p) / mersenne p : ℕ) : ℤ) + 1 := by
  have hp2 : p ≠ 2 := by omega
  have h2p : 2 ≠ p := by omega
  have hpf : (2 * p).primeFactors = {2, p} := by
    rw [Nat.primeFactors_mul (by norm_num) hp.ne_zero,
      Nat.prime_two.primeFactors, hp.primeFactors]
    ext q
    simp
  rw [mobiusNumerator, hpf,
    Finset.sum_powerset_insert (by simpa using h2p : 2 ∉ ({p} : Finset ℕ)),
    sum_powerset_singleton, sum_powerset_singleton]
  simp [mersenne, hp.ne_zero, h2p, Finset.prod_insert]
  ring

private theorem prime_mod_six_eq_one_or_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hpne2 : p ≠ 2 := by omega
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hpne2
  have hpne3 : p ≠ 3 := by omega
  have hnot3dvd : ¬ 3 ∣ p := by
    intro h
    exact hpne3 ((hp.dvd_iff_eq (by norm_num : 3 ≠ 1)).mp h)
  have hpmod3ne : p % 3 ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hnot3dvd
  have hrlt : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hrmod2 : (p % 6) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 6), hpodd]
  have hrmod3ne : (p % 6) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 6)]
    exact hpmod3ne
  omega

private theorem prime_pow_two_mod_nine_cases {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p % 6 = 1 ∧ 2 ^ p % 9 = 2) ∨ (p % 6 = 5 ∧ 2 ^ p % 9 = 5) := by
  rcases prime_mod_six_eq_one_or_five hp hp5 with hpmod | hpmod
  · left
    refine ⟨hpmod, ?_⟩
    have hpdecomp : p = 6 * (p / 6) + 1 := by
      have h := Nat.div_add_mod p 6
      omega
    rw [hpdecomp, pow_add, pow_mul]
    have h64 : 64 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
    have h := (h64.pow (p / 6)).mul_right 2
    simpa [Nat.ModEq] using h
  · right
    refine ⟨hpmod, ?_⟩
    have hpdecomp : p = 6 * (p / 6) + 5 := by
      have h := Nat.div_add_mod p 6
      omega
    rw [hpdecomp, pow_add, pow_mul]
    have h64 : 64 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
    have h := (h64.pow (p / 6)).mul_right 32
    simpa [Nat.ModEq] using h

/-- For every prime `p ≥ 5`, the twice-prime numerator has exactly the
factor `3` in common with its Mersenne denominator. -/
theorem mobiusNumerator_twicePrime_gcd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (mobiusNumerator (2 * p)).natAbs.gcd (mersenne (2 * p)) = 3 := by
  have hp0 : 0 < p := hp.pos
  have hx1 : 1 < 2 ^ p := Nat.one_lt_two_pow hp0.ne'
  have hDfactor :
      mersenne (2 * p) = (2 ^ p - 1) * (2 ^ p + 1) := by
    simpa [mersenne, Nat.mul_comm 2 p, pow_mul, mul_comm] using
      (sq_tsub_sq (2 ^ p) 1)
  have hDrepr : mersenne (2 * p) = (2 ^ p) ^ 2 - 1 := by
    simp [mersenne, Nat.mul_comm 2 p, pow_mul]
  have hquot : mersenne (2 * p) / mersenne p = 2 ^ p + 1 := by
    rw [hDfactor, mersenne]
    simpa [mul_comm] using
      (Nat.mul_div_left (2 ^ p + 1) (Nat.sub_pos_of_lt hx1))
  rcases prime_pow_two_mod_nine_cases hp hp5 with hcase | hcase
  all_goals
    rcases hcase with ⟨hpmod6, hxmod9⟩
    have hxmod : 2 ^ p ≡ 2 ^ p % 9 [MOD 9] := (Nat.mod_modEq _ _).symm
    have hsqmod := hxmod.pow 2
    have hDmod9 : mersenne (2 * p) % 9 =
        if p % 6 = 1 then 3 else 6 := by
      simp [hpmod6]
      rw [hDrepr]
      by_cases h : 2 ^ p % 9 = 2
      · have hs : ((2 ^ p) ^ 2) % 9 = 4 := by
          simpa [Nat.ModEq, h] using hsqmod
        omega
      · have hs : ((2 ^ p) ^ 2) % 9 = 7 := by
          have hx : 2 ^ p % 9 = 5 := by omega
          simpa [Nat.ModEq, hx] using hsqmod
        omega
    have hDmod9' : mersenne (2 * p) % 9 =
        (if p % 6 = 1 then 3 else 6) := hDmod9
    have h3D : 3 ∣ mersenne (2 * p) := by
      rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_mod_of_dvd (mersenne (2 * p))
        (by norm_num : 3 ∣ 9), hDmod9']
      split_ifs <;> norm_num
    have hAmod : (mersenne (2 * p) / 3) % 3 =
        if p % 6 = 1 then 1 else 2 := by
      simp [hpmod6]
      have hdiv := Nat.div_add_mod (mersenne (2 * p)) 9
      simp [hpmod6] at hDmod9'
      omega
    have hpmod3 : p % 3 = if p % 6 = 1 then 1 else 2 := by
      simp [hpmod6]
      rw [← Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 6), hpmod6]
    have hpAmod : (p * (mersenne (2 * p) / 3)) % 3 = 1 := by
      rw [Nat.mul_mod, hpmod3, hAmod]
      simp [hpmod6]
    have hDpos : 0 < mersenne (2 * p) := by
      simp [hpmod6] at hDmod9'
      omega
    have hApos : 0 < mersenne (2 * p) / 3 := by
      apply Nat.div_pos (Nat.le_of_dvd hDpos h3D)
      norm_num
    have hOneLe : 1 ≤ p * (mersenne (2 * p) / 3) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hApos.ne')
    have h3pAsub : 3 ∣ p * (mersenne (2 * p) / 3) - 1 := by
      apply (Nat.modEq_iff_dvd' hOneLe).mp
      show 1 ≡ p * (mersenne (2 * p) / 3) [MOD 3]
      simpa [Nat.ModEq] using hpAmod.symm
    have hxmod3 : 2 ^ p % 3 = 2 := by
      rw [← Nat.mod_mod_of_dvd (2 ^ p) (by norm_num : 3 ∣ 9), hxmod9]
    have h3quot : 3 ∣ mersenne (2 * p) / mersenne p := by
      rw [hquot, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hxmod3]
    have h3M : (3 : ℤ) ∣ mobiusNumerator (2 * p) := by
      rw [mobiusNumerator_twicePrime hp hp5]
      have hfirst : (3 : ℤ) ∣
          ((2 * p : ℕ) : ℤ) * (mersenne (2 * p) : ℤ) := by
        exact dvd_mul_of_dvd_right (by exact_mod_cast h3D) _
      have hsecond : (3 : ℤ) ∣
          ((p * (mersenne (2 * p) / 3) - 1 : ℕ) : ℤ) := by
        exact_mod_cast h3pAsub
      have hthird : (3 : ℤ) ∣
          2 * ((mersenne (2 * p) / mersenne p : ℕ) : ℤ) := by
        exact dvd_mul_of_dvd_right (by exact_mod_cast h3quot) _
      convert hfirst.sub (hsecond.add hthird) using 1
      push_cast [Nat.cast_sub hOneLe]
      ring
    let g := (mobiusNumerator (2 * p)).natAbs.gcd (mersenne (2 * p))
    have hgM : (g : ℤ) ∣ mobiusNumerator (2 * p) := by
      apply Int.natCast_dvd.mpr
      exact Nat.gcd_dvd_left _ _
    have hgD : (g : ℤ) ∣ (mersenne (2 * p) : ℤ) := by
      exact_mod_cast (Nat.gcd_dvd_right (mobiusNumerator (2 * p)).natAbs
        (mersenne (2 * p)))
    have hthreeA : 3 * (mersenne (2 * p) / 3) = mersenne (2 * p) :=
      Nat.mul_div_cancel' h3D
    have hidentity :
        (3 : ℤ) * mobiusNumerator (2 * p) =
          5 * (p : ℤ) * (mersenne (2 * p) : ℤ) -
            3 * (2 * (2 ^ p : ℤ) + 1) := by
      rw [mobiusNumerator_twicePrime hp hp5, hquot]
      have hthreeA' : (3 : ℤ) * ((mersenne (2 * p) / 3 : ℕ) : ℤ) =
          (mersenne (2 * p) : ℤ) := by exact_mod_cast hthreeA
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
      linear_combination -(p : ℤ) * hthreeA'
    have hg3x : (g : ℤ) ∣ 3 * (2 * (2 ^ p : ℤ) + 1) := by
      have h := (hgD.mul_left (5 * (p : ℤ))).sub (hgM.mul_left 3)
      convert h using 1
      nlinarith [hidentity]
    have hDrepr' : (mersenne (2 * p) : ℤ) = (2 ^ p : ℤ) ^ 2 - 1 := by
      have hsquarepos : 0 < (2 ^ p) ^ 2 := pow_pos (by norm_num) _
      have hsquare : 1 ≤ (2 ^ p) ^ 2 := hsquarepos
      rw [hDrepr, Nat.cast_sub hsquare]
      norm_num
    have hg9int : (g : ℤ) ∣ (9 : ℤ) := by
      have h := (hg3x.mul_right (2 * (2 ^ p : ℤ) - 1)).sub (hgD.mul_left 12)
      convert h using 1
      rw [hDrepr']
      ring
    have hg9 : g ∣ 9 := by exact_mod_cast hg9int
    have h9D : Nat.gcd 9 (mersenne (2 * p)) = 3 := by
      rw [Nat.gcd_rec, hDmod9']
      split_ifs <;> norm_num
    apply Nat.dvd_antisymm
    · have : g ∣ Nat.gcd 9 (mersenne (2 * p)) := Nat.dvd_gcd hg9
          (Nat.gcd_dvd_right _ _)
      simpa [h9D] using this
    · apply Nat.dvd_gcd
      · exact Int.natCast_dvd.mp h3M
      · exact h3D

/-- Exact reduced denominator for a twice-prime radical. -/
theorem baseMobiusShadow_den_twicePrime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (baseMobiusShadow (2 * p)).den = mersenne (2 * p) / 3 := by
  exact baseMobiusShadow_den_of_gcd_eq (2 * p) 3 (by positivity)
    (mobiusNumerator_twicePrime_gcd hp hp5)

/-! ## Exact regression fixtures

The first two fixtures use the smallest development-relevant prime `p = 5` and its
double.  The `210` fixture checks the full denominator claimed in T6 without
materialising any later large-LCM object.
-/

theorem prime5_numerator_fixture : mobiusNumerator 5 = 154 := by
  have hpf : (5 : ℕ).primeFactors = {5} := by
    simpa using (Nat.primeFactors_prod (s := {5}) (by norm_num))
  norm_num [mobiusNumerator, hpf, mersenne, Finset.sum_powerset_insert,
    sum_powerset_singleton]

theorem prime5_den_fixture :
    (baseMobiusShadow 5).den = mersenne 5 := by
  rw [baseMobiusShadow_den 5 (by norm_num), prime5_numerator_fixture]
  norm_num [mersenne]

theorem twicePrime5_numerator_fixture : mobiusNumerator 10 = 8460 := by
  have hpf : (10 : ℕ).primeFactors = {2, 5} := by
    simpa using (Nat.primeFactors_prod (s := {2, 5}) (by norm_num))
  norm_num [mobiusNumerator, hpf, mersenne, Finset.sum_powerset_insert,
    sum_powerset_singleton]

theorem twicePrime5_gcd_fixture :
    (mobiusNumerator 10).natAbs.gcd (mersenne 10) = 3 := by
  rw [twicePrime5_numerator_fixture]
  norm_num [mersenne]

theorem twicePrime5_den_fixture :
    (baseMobiusShadow 10).den = mersenne 10 / 3 := by
  exact baseMobiusShadow_den_of_gcd_eq 10 3 (by norm_num) twicePrime5_gcd_fixture

theorem radical210_numerator_fixture :
    mobiusNumerator 210 =
      269840322196455381281607797238455068282170398510853406123556081640 := by
  have hpf : (210 : ℕ).primeFactors = {2, 3, 5, 7} := by
    simpa using (Nat.primeFactors_prod (s := {2, 3, 5, 7}) (by norm_num))
  norm_num [mobiusNumerator, hpf, mersenne, Finset.sum_powerset_insert,
    sum_powerset_singleton]

theorem radical210_gcd_fixture :
    (mobiusNumerator 210).natAbs.gcd (mersenne 210) = 9 := by
  rw [radical210_numerator_fixture]
  norm_num [mersenne]

theorem radical210_den_fixture :
    (baseMobiusShadow 210).den = mersenne 210 / 9 := by
  exact baseMobiusShadow_den_of_gcd_eq 210 9 (by norm_num) radical210_gcd_fixture

#print axioms numericMobiusShadow_radical
#print axioms scaledMobiusShadow_eq_radicalNumerator
#print axioms baseMobiusShadow_den
#print axioms squarefreeKernel_squarefree
#print axioms prime_dvd_squarefreeKernel_iff
#print axioms mobiusNumerator_twicePrime_gcd
#print axioms baseMobiusShadow_den_twicePrime
#print axioms radical210_den_fixture

end Erdos249257.RadicalMobiusShadow
