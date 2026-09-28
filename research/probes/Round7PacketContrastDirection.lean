-- Candidate owner: a temporary research/probes/PacketContrastDirection.lean.
-- Purpose: check correspondence of contrast wording with an EXISTING contract.
-- No Erdős result is claimed. This file has NOT been compiled in this response.
import ErdosProblems.ArgumentGraph.Contracts

set_option autoImplicit false
open ErdosProblems.ArgumentGraph.Contracts
universe u
namespace PacketContrastDirection

theorem forward_contract {α : Sort u} {Γ H R : α → Prop}
    (h : SlotReplacement Γ H R) : ¬ Separates Γ R H :=
  h.not_separates

-- Both H and R are feasible; this is not an empty-context trick.
theorem feasible_replacement :
    SlotReplacement (fun _ : Bool => True) (fun _ => True) (fun b => b = true) :=
  ⟨fun _ _ _ => trivial⟩

theorem replacement_feasible :
    Feasible (fun _ : Bool => True) (fun b => b = true) :=
  ⟨true, trivial, rfl⟩

theorem original_wording_has_counterexample :
    Separates (fun _ : Bool => True) (fun _ => True) (fun b => b = true) :=
  ⟨false, trivial, trivial, by decide⟩

#print axioms forward_contract
#print axioms feasible_replacement
#print axioms replacement_feasible
#print axioms original_wording_has_counterexample
end PacketContrastDirection
