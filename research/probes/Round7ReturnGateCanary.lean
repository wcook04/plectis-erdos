/- P4 regression candidates; NOT compiled in the Type B environment.
   Proposed home: research/examples/ReturnGateCanary.lean, admitted through the
   repository's existing kernel-probe/coverage owners after review.
   These are elementary logical regression examples, not new research results. -/
import ErdosProblems.ArgumentGraph.Contracts
set_option autoImplicit false
open ErdosProblems.ArgumentGraph.Contracts
namespace Round7ReturnGateCanary

-- One residual equals the target; the extra residual may still be false.
theorem singleton_not_joint : ¬ (∀ (P Q : Prop), (P ↔ P) → (P ↔ (P ∧ Q))) := by
  intro h
  have hf : False := ((h True False Iff.rfl).mp True.intro).2
  exact hf

-- Failure of a universally quantified demand is not pointwise refutation.
theorem not_all_not_pointwise : (¬ (∀ b : Bool, b = true)) ∧ ¬ (∀ b : Bool, ¬ (b = true)) := by
  constructor
  · intro h
    have hf := h false
    cases hf
  · intro h
    exact h true rfl

-- A same-context weakening/strengthening requires the proper orientation.
theorem replacement_excludes_separation {α : Sort _} {Γ H R : α → Prop} (s : SlotReplacement Γ H R) :
    ¬ Separates Γ R H := by
  intro witness
  exact witness.not_entails s.reconstruct

-- Separately closing an inconsistent context can make arbitrary relations true.
theorem inconsistent_context_equivalence {α : Sort _} (Γ P Q : α → Prop) (empty : ∀ x, ¬ Γ x) : Equivalent Γ P Q := by
  constructor
  · intro x hx hp
    exact False.elim (empty x hx)
  · intro x hx hq
    exact False.elim (empty x hx)

#print axioms singleton_not_joint
#print axioms not_all_not_pointwise
#print axioms replacement_excludes_separation
#print axioms inconsistent_context_equivalence
end Round7ReturnGateCanary
