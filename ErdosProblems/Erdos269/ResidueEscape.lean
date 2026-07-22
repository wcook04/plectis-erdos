import Mathlib.Tactic.Ring

/-!
# Erdős #269: the finite residue-escape consumer

The three-prime research packet reduces irrationality to producing a block
whose least positive residue lies above a polynomial tail window.  This module
kernel-checks the final finite contradiction only.  It does not assert the
open uniform theorem that such an escaping block exists for every putative
rational denominator.
-/

namespace ErdosProblems.Erdos269

/-- A residue representative escapes a tail window when it is strictly above
the window but still lies in the canonical positive range `1, ..., C`. -/
def ResidueEscapesWindow (C bound residue : ℕ) : Prop :=
  bound < residue ∧ residue ≤ C

/-- No positive state bounded by `bound` can represent, modulo `C`, a least
positive residue which escapes that bound.  This is the finite contradiction
at the end of the prime-channel residue-escape strategy. -/
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

/-- Contrapositive form used by a rational-tail argument: if a positive state
in the short window has the prescribed congruence, then that residue cannot
escape the window. -/
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

end ErdosProblems.Erdos269
