-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.ArgumentGraph.Contracts

/-! DRAFT Type-A kernel probe: the displayed False/True equivalence is impossible.
This adds no problem mathematics and does not accuse the original prime-gap
certificate of asserting this relation. It tests the metadata-binding boundary. -/
open ErdosProblems.ArgumentGraph.Contracts
namespace Round7RelationBindingCanary

theorem false_true_not_equivalent : ¬ Equivalent (fun _ : Unit => True)
    (fun _ => False) (fun _ => True) := by
  intro equivalence
  exact equivalence.backward () trivial trivial

-- Vacuous equivalence is possible and does NOT establish feasibility.
theorem empty_context_equivalence : Equivalent (fun _ : Empty => True)
    (fun _ => False) (fun _ => True) := by
  constructor <;> intro x <;> exact Empty.elim x

#print axioms false_true_not_equivalent
#print axioms empty_context_equivalence
end Round7RelationBindingCanary
