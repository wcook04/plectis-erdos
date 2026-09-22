import ErdosProblems.Erdos1049.SourceRootCarriesR13
import Mathlib

/-!
# Global residue-block cancellation at the literal source indices


A weight depending on floor((2*n+s)/ell) is constant on the nonzero
local residues. This gives cancellation for every such weight, including
the harmonic weight that occurs in the cleared B numerator.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators

lemma choose_two_add_r13 (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  have ha := twice_choose_two_int a
  have hb := twice_choose_two_int b
  have hab := twice_choose_two_int (a + b)
  have h : ((a + b).choose 2 : ℤ) =
      (a.choose 2 : ℤ) + (b.choose 2 : ℤ) + (a : ℤ) * b := by
    push_cast at hab
    nlinarith
  exact_mod_cast h

lemma root_block_digits_no_carry (a t h ell : ℕ) (hell : 0 < ell)
    (hh : a % ell + h < ell) :
    (a + t * ell + h) / ell = a / ell + t ∧
      (a + t * ell + h) % ell = a % ell + h := by
  have ha := Nat.mod_add_div a ell
  have hid : a + t * ell + h =
      (a / ell + t) * ell + (a % ell + h) := by
    nlinarith [ha]
  have hd : (a + t * ell + h) / ell = a / ell + t := by
    apply (Nat.div_eq_iff hell).mpr
    constructor <;> omega
  have hr := Nat.mod_add_div (a + t * ell + h) ell
  rw [hd] at hr
  exact ⟨hd, by nlinarith⟩

lemma root_block_digits_carry (a t h ell : ℕ) (hell : 0 < ell)
    (hlo : ell ≤ a % ell + h) (hhi : a % ell + h < 2 * ell) :
    (a + t * ell + h) / ell = a / ell + t + 1 ∧
      (a + t * ell + h) % ell = a % ell + h - ell := by
  have ha := Nat.mod_add_div a ell
  have hre : a % ell + h - ell + ell = a % ell + h := by omega
  have hid : a + t * ell + h =
      (a / ell + t + 1) * ell + (a % ell + h - ell) := by
    nlinarith [ha, hre]
  have hd : (a + t * ell + h) / ell = a / ell + t + 1 := by
    apply (Nat.div_eq_iff hell).mpr
    constructor <;> omega
  have hr := Nat.mod_add_div (a + t * ell + h) ell
  rw [hd] at hr
  have he : (a + t * ell + h) % ell + ell = a % ell + h := by nlinarith
  exact ⟨hd, by omega⟩

lemma finite_sum_rectangular_blocks {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (T ell : ℕ) :
    (∑ s ∈ range (T * ell), f s) =
      ∑ t ∈ range T, ∑ h ∈ range ell, f (t * ell + h) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

section Field
variable {K : Type*} [Field K]

def gaussianPhase (q : K) (k : ℕ) : K := (-1 : K) ^ k * q ^ k.choose 2

lemma gaussianPhase_add (q : K) (a b : ℕ) :
    gaussianPhase q (a + b) = gaussianPhase q a * gaussianPhase q b * q ^ (a * b) := by
  simp only [gaussianPhase, choose_two_add_r13, pow_add]
  ring

lemma gaussianPhase_at_root_order (q : K) {ell : ℕ} (hell : 0 < ell)
    (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1) :
    gaussianPhase q ell = -1 := by
  have hsum : (∑ j ∈ range ell, qBinomialTerm q (1 : K) ell j) = 1 := by
    rw [sum_eq_single 0]
    · exact qBinomialTerm_zero _ _ _
    · intro j hj hj0
      simp only [qBinomialTerm,
        gaussian_first_root_block_zero q hroot hprimitive (by omega) (mem_range.mp hj),
        zero_mul]
    · intro hnot
      exact (hnot (mem_range.mpr hell)).elim
  have hz := qPochhammer_one q hell
  rw [qPochhammer_eq_sum, sum_range_succ, hsum] at hz
  have he : 1 + gaussianPhase q ell = 0 := by
    simpa [qBinomialTerm, gaussianPhase, gaussBinom_self] using hz
  calc
    gaussianPhase q ell = (1 + gaussianPhase q ell) - 1 := by ring
    _ = -1 := by rw [he]; ring

lemma gaussianPhase_root_block (q : K) {ell : ℕ} (hell : 0 < ell)
    (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1) (t h : ℕ) :
    gaussianPhase q (t * ell + h) = (-1 : K) ^ t * gaussianPhase q h := by
  induction t with
  | zero => simp [gaussianPhase]
  | succ t ih =>
      have he : (t + 1) * ell + h = (t * ell + h) + ell := by ring
      have hp : q ^ ((t * ell + h) * ell) = 1 := by
        rw [Nat.mul_comm, pow_mul, hroot, one_pow]
      rw [he, gaussianPhase_add, gaussianPhase_at_root_order q hell hroot hprimitive,
        hp, mul_one, ih, pow_succ]
      ring

lemma root_linear_phase_block (q : K) {ell : ℕ} (hroot : q ^ ell = 1)
    (n t h : ℕ) :
    q ^ ((n + 1) * (t * ell + h)) = q ^ ((n % ell + 1) * h) := by
  have hblock : q ^ (t * ell + h) = q ^ h := by
    rw [pow_add, Nat.mul_comm t ell, pow_mul, hroot, one_pow, one_mul]
  have hn : q ^ (n + 1) = q ^ (n % ell + 1) := by
    rw [pow_succ, root_power_reduce q hroot n, ← pow_succ]
  calc
    _ = (q ^ (t * ell + h)) ^ (n + 1) := by rw [← pow_mul, Nat.mul_comm]
    _ = (q ^ h) ^ (n + 1) := by rw [hblock]
    _ = (q ^ (n + 1)) ^ h := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = _ := by rw [hn, ← pow_mul]

/-- The source residue with its common monomial removed, symmetrised only
inside the valid source range. Outside that range this auxiliary term is
zero, enabling a justified rectangular extension of the finite sum. -/
def sourceRootTerm (q : K) (n s : ℕ) : K :=
  gaussianPhase q s * q ^ ((n + 1) * s) *
    gaussBinom q (14 * n + s) (12 * n) * gaussBinom q (13 * n) s

def localGaussianTerm (q : K) (w a r v h : ℕ) : K :=
  (-1 : K) ^ h * q ^ (h.choose 2 + (r + 1) * h) *
    gaussBinom q v h * gaussBinom q (w + h) a

lemma sourceRootTerm_eq_actual (q : K) (n s : ℕ) (hs : s ≤ 13 * n) :
    (sourceASummand n s).eval₂ (Int.castRingHom K) q =
      q ^ (sourceM n + 2 * n ^ 2) * sourceRootTerm q n s := by
  simp only [sourceASummand, sourceGaussianProduct, sourceAExponent, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_X, Int.cast_pow, Int.cast_neg, Int.cast_one,
    eval₂_gaussBinom]
  rw [← gaussian_field_symmetry q (13 * n) s hs]
  have hsign : (Int.castRingHom K) ((-1 : ℤ) ^ s) = (-1 : K) ^ s := by simp
  rw [hsign]
  simp only [sourceRootTerm, gaussianPhase, pow_add]
  ring

lemma sourceRootTerm_zero_above (q : K) (n s : ℕ) (hs : 13 * n < s) :
    sourceRootTerm q n s = 0 := by
  unfold sourceRootTerm
  rw [gaussBinom_eq_zero_of_lt q hs, mul_zero]

/-- On every nonzero residue, both Gaussian quotients and the harmonic floor
have their exact constant block values. The zero cases are retained. -/
theorem sourceRootTerm_weighted_block (q : K) (hq : q ≠ 0)
    (n ell t h : ℕ) (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hfirst : sourceCarryOne n ell ≤ 0) (hsecond : sourceCarryTwo n ell = 1)
    (hh : h < ell) (f : ℕ → K) :
    sourceRootTerm q n (t * ell + h) * f ((2 * n + (t * ell + h)) / ell) =
      ((-1 : K) ^ t * ((13 * n / ell).choose t : K) *
        ((14 * n / ell + t).choose (12 * n / ell) : K) *
          f (t + (14 * n / ell - 12 * n / ell))) *
        localGaussianTerm q ((14 * n) % ell) ((12 * n) % ell) (n % ell) ((13 * n) % ell) h := by
  have ha_lt := Nat.mod_lt (12 * n) hell
  have hv_lt := Nat.mod_lt (13 * n) hell
  have hw_lt := Nat.mod_lt (14 * n) hell
  have hs : (t * ell + h) / ell = t ∧ (t * ell + h) % ell = h := by
    simpa using root_block_digits_no_carry 0 t h ell hell (by simpa using hh)
  have hG2 := gaussian_qLucas q hq hell hroot hprimitive (13 * n) (t * ell + h)
  rw [hs.1, hs.2] at hG2
  by_cases hv : h ≤ (13 * n) % ell
  · by_cases hwrap : ell ≤ (14 * n) % ell + h
    · have hd := root_block_digits_carry (14 * n) t h ell hell hwrap (by omega)
      have hz := source_second_carry_wrapped_zero_geometry n ell h hell hfirst hsecond hv hwrap
      have hbig : gaussBinom q (14 * n + (t * ell + h)) (12 * n) = 0 := by
        rw [gaussian_qLucas q hq hell hroot hprimitive]
        have hre : (14 * n + (t * ell + h)) % ell = (14 * n) % ell + h - ell := by
          simpa only [Nat.add_assoc] using hd.2
        rw [hre, gaussBinom_eq_zero_of_lt q hz, mul_zero]
      have hsmall : gaussBinom q ((14 * n) % ell + h) ((12 * n) % ell) = 0 := by
        rw [gaussian_qLucas q hq hell hroot hprimitive]
        have hmod : ((14 * n) % ell + h) % ell = (14 * n) % ell + h - ell := by
          have hx := root_block_digits_carry ((14 * n) % ell) 0 h ell hell
            (by simpa using hwrap) (by simpa using (show (14 * n) % ell + h < 2 * ell by omega))
          simpa using hx.2
        rw [hmod, Nat.mod_eq_of_lt ha_lt, gaussBinom_eq_zero_of_lt q hz, mul_zero]
      simp only [sourceRootTerm, localGaussianTerm, hbig, hsmall, mul_zero, zero_mul]
    · have hnowrap : (14 * n) % ell + h < ell := by omega
      have hd := root_block_digits_no_carry (14 * n) t h ell hell hnowrap
      have hG1 : gaussBinom q (14 * n + (t * ell + h)) (12 * n) =
          ((14 * n / ell + t).choose (12 * n / ell) : K) *
            gaussBinom q ((14 * n) % ell + h) ((12 * n) % ell) := by
        rw [gaussian_qLucas q hq hell hroot hprimitive]
        have hd' :
            (14 * n + (t * ell + h)) / ell = 14 * n / ell + t ∧
              (14 * n + (t * ell + h)) % ell = 14 * n % ell + h := by
          simpa only [Nat.add_assoc] using hd
        rw [hd'.1, hd'.2]
      by_cases hlo : (12 * n) % ell ≤ (14 * n) % ell + h
      · have hfloor := source_surviving_harmonic_floor n ell h hell hlo hnowrap
        have hfshift := (root_block_digits_no_carry (2 * n + h) t 0 ell hell
          (by simpa using Nat.mod_lt (2 * n + h) hell)).1
        have hf : (2 * n + (t * ell + h)) / ell = t + (14 * n / ell - 12 * n / ell) := by
          have hre : 2 * n + h + t * ell + 0 = 2 * n + (t * ell + h) := by ring
          rw [hre, hfloor] at hfshift
          omega
        simp only [sourceRootTerm, hG1, hG2, hf]
        rw [gaussianPhase_root_block q hell hroot hprimitive,
          root_linear_phase_block q hroot]
        simp only [localGaussianTerm, gaussianPhase, pow_add]
        ring
      · have hz : gaussBinom q ((14 * n) % ell + h) ((12 * n) % ell) = 0 :=
          gaussBinom_eq_zero_of_lt q (by omega)
        simp only [sourceRootTerm, hG1, localGaussianTerm, hz, mul_zero, zero_mul]
  · have hz : gaussBinom q ((13 * n) % ell) h = 0 := gaussBinom_eq_zero_of_lt q (by omega)
    simp only [sourceRootTerm, hG2, localGaussianTerm, hz, mul_zero, zero_mul]

lemma localGaussianTerm_sum_full_block_zero (q : K) (hq : q ≠ 0)
    (n ell : ℕ) (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hfirst : sourceCarryOne n ell ≤ 0) (hsecond : sourceCarryTwo n ell = 1) :
    (∑ h ∈ range ell,
      localGaussianTerm q ((14 * n) % ell) ((12 * n) % ell) (n % ell) ((13 * n) % ell) h) = 0 := by
  have hv := Nat.mod_lt (13 * n) hell
  have he : (∑ h ∈ range ((13 * n) % ell + 1),
      localGaussianTerm q ((14 * n) % ell) ((12 * n) % ell) (n % ell) ((13 * n) % ell) h) =
      ∑ h ∈ range ell,
        localGaussianTerm q ((14 * n) % ell) ((12 * n) % ell) (n % ell) ((13 * n) % ell) h := by
    apply sum_subset (range_mono (by omega))
    intro h hh hnot
    have hz : (13 * n) % ell < h := by
      have hnot' := mt mem_range.mpr hnot
      omega
    simp only [localGaussianTerm, gaussBinom_eq_zero_of_lt q hz, mul_zero, zero_mul]
  rw [← he]
  exact actual_source_second_carry_local_zero q hq n ell hell hroot hprimitive hfirst hsecond

/-- The complete finite block assembly for an arbitrary cutoff-dependent
weight. In particular, no harmonic cancellation is postulated as a premise. -/
theorem actual_source_second_carry_weighted_zero (q : K) (hq : q ≠ 0)
    (n ell : ℕ) (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hfirst : sourceCarryOne n ell ≤ 0) (hsecond : sourceCarryTwo n ell = 1)
    (f : ℕ → K) :
    (∑ s ∈ range (13 * n + 1),
      (sourceASummand n s).eval₂ (Int.castRingHom K) q * f ((2 * n + s) / ell)) = 0 := by
  have hbound : 13 * n + 1 ≤ (13 * n / ell + 1) * ell := by
    have he := Nat.mod_add_div (13 * n) ell
    have hr := Nat.mod_lt (13 * n) hell
    nlinarith
  have hsum : (∑ s ∈ range (13 * n + 1),
      sourceRootTerm q n s * f ((2 * n + s) / ell)) =
      ∑ s ∈ range ((13 * n / ell + 1) * ell),
        sourceRootTerm q n s * f ((2 * n + s) / ell) := by
    apply sum_subset (range_mono hbound)
    intro s hs hnot
    have hs' : 13 * n < s := by have h := mt mem_range.mpr hnot; omega
    rw [sourceRootTerm_zero_above q n s hs', zero_mul]
  have hzero : (∑ s ∈ range (13 * n + 1),
      sourceRootTerm q n s * f ((2 * n + s) / ell)) = 0 := by
    rw [hsum, finite_sum_rectangular_blocks]
    apply sum_eq_zero
    intro t ht
    have he : (∑ h ∈ range ell,
        sourceRootTerm q n (t * ell + h) * f ((2 * n + (t * ell + h)) / ell)) =
        ((-1 : K) ^ t * ((13 * n / ell).choose t : K) *
          ((14 * n / ell + t).choose (12 * n / ell) : K) *
            f (t + (14 * n / ell - 12 * n / ell))) *
        ∑ h ∈ range ell,
          localGaussianTerm q ((14 * n) % ell) ((12 * n) % ell) (n % ell) ((13 * n) % ell) h := by
      rw [mul_sum]
      apply sum_congr rfl
      intro h hh
      exact sourceRootTerm_weighted_block q hq n ell t h hell hroot hprimitive
        hfirst hsecond (mem_range.mp hh) f
    rw [he, localGaussianTerm_sum_full_block_zero q hq n ell hell hroot hprimitive hfirst hsecond,
      mul_zero]
  calc
    _ = q ^ (sourceM n + 2 * n ^ 2) *
        ∑ s ∈ range (13 * n + 1), sourceRootTerm q n s * f ((2 * n + s) / ell) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro s hs
      rw [sourceRootTerm_eq_actual q n s (by have h := mem_range.mp hs; omega)]
      ring
    _ = 0 := by rw [hzero, mul_zero]

end Field
end ErdosProblems.Erdos1049.PaperR13
