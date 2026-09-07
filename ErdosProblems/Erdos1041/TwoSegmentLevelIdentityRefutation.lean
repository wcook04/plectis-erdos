import Mathlib.Data.Set.Basic

/-!
# The gate kernel behind the two-segment level-identity refutation

The analytic certificate supplies a unique first-merge point `c` and proves
that no root spoke from `c` is contained in the first critical sublevel set.
The only topological input needed after that is: any two-arm connection of two
roots at the first level must contain `c` on one of its arms, and a subsegment
of a safe arm is safe.  This file checks that finite implication abstractly.
-/

namespace ErdosProblems.Erdos1041

variable {α : Type*}

def segmentSafe (segment : α → α → Set α) (K : Set α) (a b : α) : Prop :=
  segment a b ⊆ K

theorem segmentSafe_of_subsegment
    (segment : α → α → Set α) (K : Set α) {h c a : α}
    (hsub : segment c a ⊆ segment h a)
    (hsafe : segmentSafe segment K h a) :
    segmentSafe segment K c a := by
  exact Set.Subset.trans hsub hsafe

theorem safe_spoke_of_safe_two_arm_at_gate
    (segment : α → α → Set α) (K : Set α) {h c a b : α}
    (leftSubsegment : c ∈ segment h a → segment c a ⊆ segment h a)
    (rightSubsegment : c ∈ segment h b → segment c b ⊆ segment h b)
    (hgate : c ∈ segment h a ∨ c ∈ segment h b)
    (ha : segmentSafe segment K h a)
    (hb : segmentSafe segment K h b) :
    segmentSafe segment K c a ∨ segmentSafe segment K c b := by
  rcases hgate with hca | hcb
  · exact Or.inl (segmentSafe_of_subsegment segment K (leftSubsegment hca) ha)
  · exact Or.inr (segmentSafe_of_subsegment segment K (rightSubsegment hcb) hb)

theorem no_safe_two_arm_at_gate_of_no_safe_spoke
    (segment : α → α → Set α) (K : Set α) {h c a b : α}
    (leftSubsegment : c ∈ segment h a → segment c a ⊆ segment h a)
    (rightSubsegment : c ∈ segment h b → segment c b ⊆ segment h b)
    (hgate : c ∈ segment h a ∨ c ∈ segment h b)
    (haUnsafe : ¬segmentSafe segment K c a)
    (hbUnsafe : ¬segmentSafe segment K c b) :
    ¬(segmentSafe segment K h a ∧ segmentSafe segment K h b) := by
  rintro ⟨ha, hb⟩
  rcases safe_spoke_of_safe_two_arm_at_gate
      segment K leftSubsegment rightSubsegment hgate ha hb with hsafe | hsafe
  · exact haUnsafe hsafe
  · exact hbUnsafe hsafe

end ErdosProblems.Erdos1041
