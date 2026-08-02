import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the finite least-positive-residue obstruction

For a positive modulus `C`, the least positive representative of a congruence
class is `C` for the zero class and lies in `1, ..., C - 1` otherwise.  Hence a
positive integer state bounded by `K` cannot be congruent to an integer whose
least positive representative is larger than `K`.

This module proves only that final finite obstruction.  An application to the
series in Erdős problem #269 still needs two upstream inputs: rationality must
produce a positive bounded integral state with the required smooth-divisibility
congruence, and one must construct arbitrarily late finite windows whose least
positive residues escape the corresponding bound.  Neither input, and hence no
irrationality theorem for the series, is proved here.
-/

namespace ErdosProblems.Erdos269

/-- Canonical positive representative of an integer modulo `C`: a zero
residue is represented by `C`, and every nonzero residue by its nonnegative
Euclidean remainder.  The definition is total at `C = 0`, but all theorems
using its positive-representative meaning assume `0 < C`. -/
def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))

/-- The least positive representative really lies in the canonical interval
`1, ..., C` when the modulus is positive. -/
theorem leastPositiveResidue_pos_le
    {C : ℕ} (hC : 0 < C) (x : ℤ) :
    0 < leastPositiveResidue C x ∧ leastPositiveResidue C x ≤ C := by
  unfold leastPositiveResidue
  by_cases hx : x % (C : ℤ) = 0
  · simp [hx, hC]
  · simp only [hx, if_false]
    have hCInt : (0 : ℤ) < C := by exact_mod_cast hC
    have hnonneg : 0 ≤ x % (C : ℤ) :=
      Int.emod_nonneg x hCInt.ne'
    have hlt : x % (C : ℤ) < C :=
      Int.emod_lt_of_pos x hCInt
    constructor
    · exact Int.natAbs_pos.mpr hx
    · have habsLt : Int.natAbs (x % (C : ℤ)) < C := by
        exact_mod_cast (show (Int.natAbs (x % (C : ℤ)) : ℤ) < C by
          simpa [Int.natAbs_of_nonneg hnonneg] using hlt)
      omega

/-- The canonical positive representative is congruent to the source
integer. -/
theorem leastPositiveResidue_modEq
    {C : ℕ} (hC : 0 < C) (x : ℤ) :
    Int.ModEq C (leastPositiveResidue C x : ℤ) x := by
  unfold leastPositiveResidue Int.ModEq
  by_cases hx : x % (C : ℤ) = 0
  · simp [hx]
  · simp only [hx, if_false]
    have hCInt : (0 : ℤ) < C := by exact_mod_cast hC
    have hnonneg : 0 ≤ x % (C : ℤ) :=
      Int.emod_nonneg x hCInt.ne'
    have hlt : x % (C : ℤ) < C :=
      Int.emod_lt_of_pos x hCInt
    have hcast :
        ((Int.natAbs (x % (C : ℤ)) : ℕ) : ℤ) =
          x % (C : ℤ) := by
      simp [Int.natAbs_of_nonneg hnonneg]
    rw [hcast, Int.emod_eq_of_lt hnonneg hlt]

/-- The numerical predicate `bound < residue ≤ C`. -/
def ResidueEscapesWindow (C bound residue : ℕ) : Prop :=
  bound < residue ∧ residue ≤ C

/-- No positive state bounded by `bound` can represent, modulo `C`, a residue
in the canonical positive range that lies above `bound`. -/
theorem no_bounded_positive_state_of_residue_escape
    {C bound residue c : ℕ}
    (hcpos : 0 < c)
    (hcbound : c ≤ bound)
    (hescape : ResidueEscapesWindow C bound residue)
    (hmod : c % C = residue % C) :
    False := by
  rcases hescape with ⟨hboundResidue, hresidueC⟩
  have hcC : c < C :=
    lt_of_le_of_lt hcbound (hboundResidue.trans_le hresidueC)
  by_cases hresidueEq : residue = C
  · subst residue
    rw [Nat.mod_eq_of_lt hcC, Nat.mod_self] at hmod
    omega
  · have hresidueLt : residue < C := lt_of_le_of_ne hresidueC hresidueEq
    rw [Nat.mod_eq_of_lt hcC, Nat.mod_eq_of_lt hresidueLt] at hmod
    omega

/-- Contrapositive form: if a positive bounded state has the prescribed
congruence, then its canonical positive residue cannot exceed the bound. -/
theorem residue_le_bound_of_bounded_positive_state
    {C bound residue c : ℕ}
    (hcpos : 0 < c)
    (hcbound : c ≤ bound)
    (hresidueC : residue ≤ C)
    (hmod : c % C = residue % C) :
    residue ≤ bound := by
  by_contra hnot
  exact no_bounded_positive_state_of_residue_escape
    hcpos hcbound ⟨Nat.lt_of_not_ge hnot, hresidueC⟩ hmod

/-- Integer-valued form of the finite contradiction.  A positive integer
bounded by `bound` cannot be congruent to an integer whose least positive
residue lies above that bound. -/
theorem no_bounded_positive_int_state_of_leastPositiveResidue
    {C bound : ℕ} {x c : ℤ}
    (hC : 0 < C)
    (hcpos : 0 < c)
    (hcbound : Int.natAbs c ≤ bound)
    (hescape : bound < leastPositiveResidue C x)
    (hmod : Int.ModEq C c x) :
    False := by
  have hresidue :=
    leastPositiveResidue_pos_le hC x
  have hmodInt :
      ((Int.natAbs c : ℕ) : ℤ) % (C : ℤ) =
        ((leastPositiveResidue C x : ℕ) : ℤ) % (C : ℤ) := by
    have hcx :
        Int.ModEq C ((Int.natAbs c : ℕ) : ℤ) x := by
      simpa [Int.natAbs_of_nonneg hcpos.le] using hmod
    exact (hcx.trans (leastPositiveResidue_modEq hC x).symm).eq
  have hmodNat :
      Int.natAbs c % C = leastPositiveResidue C x % C := by
    exact_mod_cast hmodInt
  exact no_bounded_positive_state_of_residue_escape
    (Int.natAbs_pos.mpr hcpos.ne')
    hcbound
    ⟨hescape, hresidue.2⟩
    hmodNat

/-- A positive integer already lying in the canonical interval is exactly the
least positive representative of its congruence class. -/
theorem leastPositiveResidue_eq_natAbs_of_pos_le_modEq
    {C : ℕ} (hC : 0 < C) {x c : ℤ}
    (hcpos : 0 < c)
    (hcle : Int.natAbs c ≤ C)
    (hmod : Int.ModEq C c x) :
    leastPositiveResidue C x = Int.natAbs c := by
  have hresidue := leastPositiveResidue_pos_le hC x
  have hresidue_le : leastPositiveResidue C x ≤ Int.natAbs c := by
    by_contra hnot
    exact no_bounded_positive_int_state_of_leastPositiveResidue
      hC hcpos le_rfl (Nat.lt_of_not_ge hnot) hmod
  have hmodInt :
      ((leastPositiveResidue C x : ℕ) : ℤ) % (C : ℤ) =
        ((Int.natAbs c : ℕ) : ℤ) % (C : ℤ) := by
    have hcx :
        Int.ModEq C ((Int.natAbs c : ℕ) : ℤ) x := by
      simpa [Int.natAbs_of_nonneg hcpos.le] using hmod
    exact ((leastPositiveResidue_modEq hC x).trans hcx.symm).eq
  have hmodNat :
      leastPositiveResidue C x % C = Int.natAbs c % C := by
    exact_mod_cast hmodInt
  have hc_le : Int.natAbs c ≤ leastPositiveResidue C x :=
    residue_le_bound_of_bounded_positive_state
      hresidue.1 le_rfl hcle hmodNat
  omega

end ErdosProblems.Erdos269
