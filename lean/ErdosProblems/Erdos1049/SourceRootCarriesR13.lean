import ErdosProblems.Erdos1049.QLucasR13
import ErdosProblems.Erdos1049.SourceBTopDegreeR13
import Mathlib

/-!
# Exact source carry geometry and the first Omega channel


The carry expressions are linked to the literal sourceWeight. The first
carry case is carried through to the actual cleared B polynomial. The
second case supplies its exact local-window geometry and constant harmonic
floor; its global residue-block assembly is not asserted by this file.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators

def sourceCarryOne (n ell : ℕ) : ℤ :=
  ((14 * n / ell : ℕ) : ℤ) + (13 * n / ell : ℕ) - (12 * n / ell : ℕ) - (15 * n / ell : ℕ)

def sourceCarryTwo (n ell : ℕ) : ℤ :=
  2 * ((14 * n / ell : ℕ) : ℤ) - (13 * n / ell : ℕ) - (15 * n / ell : ℕ)

lemma floor_nat_ratio_int (a b : ℕ) :
    ⌊(a : ℝ) / (b : ℝ)⌋ = ((a / b : ℕ) : ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_natCast]
  norm_cast

/-- No numerical comparison of floors is substituted for the literal weight. -/
theorem sourceWeight_eq_carries (n ell : ℕ) :
    sourceWeight n ell = max 0 (max (sourceCarryOne n ell) (sourceCarryTwo n ell)) := by
  have hf (c : ℕ) : ⌊(c : ℝ) * ((n : ℝ) / (ell : ℝ))⌋ =
      ((c * n / ell : ℕ) : ℤ) := by
    rw [← mul_div_assoc, ← Nat.cast_mul]
    exact floor_nat_ratio_int _ _
  unfold sourceWeight PaperR7.omegaWeight sourceCarryOne sourceCarryTwo
  rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, hf 14,
    show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, hf 13,
    show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, hf 12,
    show (15 : ℝ) = ((15 : ℕ) : ℝ) by norm_num, hf 15]

/-- A complete and disjoint split of the source weight-one cases. -/
theorem sourceWeight_one_carry_cases (n ell : ℕ) (hw : sourceWeight n ell = 1) :
    sourceCarryOne n ell = 1 ∨
      (sourceCarryOne n ell ≤ 0 ∧ sourceCarryTwo n ell = 1) := by
  rw [sourceWeight_eq_carries] at hw
  simp only [max_def] at hw
  split_ifs at hw <;> omega

lemma source_add_div (a b n ell : ℕ) (hell : 0 < ell) :
    ((a + b) * n) / ell = a * n / ell + b * n / ell +
      if ell ≤ (a * n) % ell + (b * n) % ell then 1 else 0 := by
  rw [add_mul]
  exact Nat.add_div hell

lemma source_add_mod (a b n ell : ℕ) :
    ((a + b) * n) % ell =
      (a * n) % ell + (b * n) % ell -
        if (a * n) % ell + (b * n) % ell < ell then 0 else ell := by
  rw [add_mul]
  exact Nat.add_mod_eq_sub

/-- First carry: the surviving lower Gaussian digit always exceeds the upper. -/
theorem source_first_carry_geometry (n ell : ℕ) (hell : 0 < ell)
    (hcarry : sourceCarryOne n ell = 1) :
    ell ≤ (12 * n) % ell + (2 * n) % ell ∧
    (13 * n) % ell + (2 * n) % ell < ell ∧
    (14 * n) % ell + ell = (12 * n) % ell + (2 * n) % ell := by
  have h14 := source_add_div 12 2 n ell hell
  have h15 := source_add_div 13 2 n ell hell
  norm_num only at h14 h15
  unfold sourceCarryOne at hcarry
  have hfirst : ell ≤ (12 * n) % ell + (2 * n) % ell := by
    split_ifs at h14 h15 <;> omega
  have hsecond : (13 * n) % ell + (2 * n) % ell < ell := by
    split_ifs at h14 h15 <;> omega
  refine ⟨hfirst, hsecond, ?_⟩
  have hm := source_add_mod 12 2 n ell
  norm_num only at hm
  rw [if_neg (not_lt.mpr hfirst)] at hm
  omega

/-- Second carry after excluding the first: a+r=v and the local window
necessarily crosses ell. These are exactly the hypotheses used by the
finite local cancellation theorem. -/
theorem source_second_carry_geometry (n ell : ℕ) (hell : 0 < ell)
    (hfirst : sourceCarryOne n ell ≤ 0) (hsecond : sourceCarryTwo n ell = 1) :
    (12 * n) % ell + n % ell = (13 * n) % ell ∧
    ell ≤ (13 * n) % ell + n % ell ∧
    (14 * n) % ell + n % ell < ell ∧
    (14 * n) % ell + ell = (13 * n) % ell + n % ell := by
  have h13 := source_add_div 12 1 n ell hell
  have h14 := source_add_div 13 1 n ell hell
  have h15 := source_add_div 14 1 n ell hell
  norm_num only [one_mul] at h13 h14 h15
  unfold sourceCarryOne at hfirst
  unfold sourceCarryTwo at hsecond
  have hcarry : ell ≤ (13 * n) % ell + n % ell := by
    split_ifs at h14 h15 <;> omega
  have hncarry : (14 * n) % ell + n % ell < ell := by
    split_ifs at h14 h15 <;> omega
  have hlow : (12 * n) % ell + n % ell < ell := by
    split_ifs at h13 h14 h15 <;> omega
  have hm13 := source_add_mod 12 1 n ell
  have hm14 := source_add_mod 13 1 n ell
  norm_num only [one_mul] at hm13 hm14
  rw [if_pos hlow, Nat.sub_zero] at hm13
  rw [if_neg (not_lt.mpr hcarry)] at hm14
  exact ⟨hm13.symm, hcarry, hncarry, by omega⟩

/-- All wrapped residues in the second carry have a zero first Gaussian. -/
theorem source_second_carry_wrapped_zero_geometry (n ell h : ℕ) (hell : 0 < ell)
    (hfirst : sourceCarryOne n ell ≤ 0) (hsecond : sourceCarryTwo n ell = 1)
    (hh : h ≤ (13 * n) % ell) (hwrap : ell ≤ (14 * n) % ell + h) :
    (14 * n) % ell + h - ell < (12 * n) % ell := by
  obtain ⟨ha, hc, hw, he⟩ := source_second_carry_geometry n ell hell hfirst hsecond
  omega

/-- The harmonic cutoff is constant in every nonzero local block. -/
theorem source_surviving_harmonic_floor (n ell h : ℕ) (hell : 0 < ell)
    (hlo : (12 * n) % ell ≤ (14 * n) % ell + h)
    (hhi : (14 * n) % ell + h < ell) :
    (2 * n + h) / ell = (14 * n / ell) - (12 * n / ell) := by
  have h12 := Nat.mod_add_div (12 * n) ell
  have h14 := Nat.mod_add_div (14 * n) ell
  have hle : 12 * n / ell ≤ 14 * n / ell := Nat.div_le_div_right (by omega)
  have hmul := congrArg (fun k : ℕ => ell * k) (Nat.sub_add_cancel hle)
  change ell * (14 * n / ell - 12 * n / ell + 12 * n / ell) =
    ell * (14 * n / ell) at hmul
  rw [Nat.mul_add] at hmul
  have hid :
      (14 * n / ell - 12 * n / ell) * ell + (14 * n) % ell =
        2 * n + (12 * n) % ell := by
    nlinarith [h12, h14, hmul]
  apply (Nat.div_eq_iff hell).mpr
  constructor <;> omega

section Field
variable {K : Type*} [Field K]

lemma gaussian_field_symmetry (q : K) (n k : ℕ) (hk : k ≤ n) :
    gaussBinom q n k = gaussBinom q n (n - k) := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom K) q)
    (gaussian_polynomial_symmetry n k hk)
  simpa only [eval₂_gaussBinom] using h

/-- Actual source Gaussian product, not an abstract residue family. -/
theorem actual_source_gaussian_product_first_carry_zero (q : K) (hq : q ≠ 0)
    (n ell s : ℕ) (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hcarry : sourceCarryOne n ell = 1) (hs : s ≤ 13 * n) :
    (sourceGaussianProduct n s).eval₂ (Int.castRingHom K) q = 0 := by
  simp only [sourceGaussianProduct, eval₂_mul, eval₂_gaussBinom]
  rw [← gaussian_field_symmetry q (13 * n) s hs]
  by_cases hrem : s % ell ≤ (13 * n) % ell
  · obtain ⟨hfirst, hsecond, hlast⟩ := source_first_carry_geometry n ell hell hcarry
    have hsmall : (14 * n) % ell + s % ell < (12 * n) % ell := by omega
    have hm : (14 * n + s) % ell = (14 * n) % ell + s % ell := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (hsmall.trans (Nat.mod_lt _ hell))]
    rw [gaussian_qLucas q hq hell hroot hprimitive (14 * n + s) (12 * n), hm,
      gaussBinom_eq_zero_of_lt q hsmall]
    ring
  · rw [gaussian_qLucas q hq hell hroot hprimitive (13 * n) s,
      gaussBinom_eq_zero_of_lt q (by omega : (13 * n) % ell < s % ell)]
    ring

/-- Every actual A residue is zero in the first carry case. -/
theorem actual_ASummand_first_carry_zero (q : K) (hq : q ≠ 0)
    (n ell s : ℕ) (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hcarry : sourceCarryOne n ell = 1) (hs : s ≤ 13 * n) :
    (sourceASummand n s).eval₂ (Int.castRingHom K) q = 0 := by
  simp only [sourceASummand, eval₂_mul]
  rw [actual_source_gaussian_product_first_carry_zero q hq n ell s hell hroot hprimitive hcarry hs]
  ring

/-- This reaches the actual D-cleared B numerator for the entire first carry
case, including all shifted channels. No B-identity premise is used. -/
theorem actual_cleared_B_first_carry_zero (q : K) (hq : q ≠ 0)
    (n ell : ℕ) (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hcarry : sourceCarryOne n ell = 1) :
    (sourceClearedB n).eval₂ (Int.castRingHom K) q = 0 := by
  classical
  let f : ℤ[X] →+* K := Polynomial.eval₂RingHom (Int.castRingHom K) q
  change f (sourceClearedB n) = 0
  unfold sourceClearedB
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  have hs' : s ≤ 13 * n := by have := Finset.mem_range.mp hs; omega
  have hA : f (sourceASummand n s) = 0 :=
    actual_ASummand_first_carry_zero q hq n ell s hell hroot hprimitive hcarry hs'
  rw [map_add, map_sum, map_sum]
  have hleft : (∑ l ∈ Finset.Icc 1 (2 * n + s),
      f (sourceASummand n s * sourceDQuotient n l)) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [map_mul, hA, zero_mul]
  have hright : (∑ j ∈ Finset.Icc 1 (14 * n),
      f (sourceShiftedASummand n s j * sourceDQuotient n j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_mul, sourceShiftedASummand_map f n s j hs' (Finset.mem_Icc.mp hj).2
      (by simpa [f] using hq), hA, zero_mul, zero_mul]
  rw [hleft, hright, zero_add]

/-- Literal source digits supply the already-proved local cancellation in
the remaining carry case. The global harmonic block assembly is separate. -/
theorem actual_source_second_carry_local_zero (q : K) (hq : q ≠ 0)
    (n ell : ℕ) (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hfirst : sourceCarryOne n ell ≤ 0) (hsecond : sourceCarryTwo n ell = 1) :
    rootLocalGaussianSum q ((14 * n) % ell) ((12 * n) % ell) (n % ell) ((13 * n) % ell) = 0 := by
  obtain ⟨ha, hc, hw, he⟩ := source_second_carry_geometry n ell hell hfirst hsecond
  exact rootLocalGaussianSum_eq_zero_of_residues q hq hroot hprimitive
    (Nat.mod_lt _ hell) ha (by simpa [add_comm] using hc)

end Field
end ErdosProblems.Erdos1049.PaperR13
