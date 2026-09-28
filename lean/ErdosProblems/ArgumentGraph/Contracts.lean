-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

/-!
# Relation contracts between statements in a shared context

The research record compares statements: a returned hypothesis against the one it replaces,
a reformulation against its target, a proposed route against an endpoint. Every such
comparison happens inside a context: the parameters in scope and the hypotheses already
available. This module fixes the vocabulary once, over an arbitrary context type `α` and a
background predicate `Γ : α → Prop` that records the admissible context values.

* `Entails Γ P Q`: at every admissible context value, `P` gives `Q`.
* `Separates Γ P Q`: some admissible context value satisfies `P` and fails `Q`.
* `Feasible Γ P`, `Refuted Γ P`, `Supplied Γ P`: some, no, every admissible value satisfies `P`.
* `Equivalent Γ P Q`: entailment in both directions.
* `StrictlyStronger Γ new old`: `new` gives `old`, and a separator shows `old` does not give `new`.

Two certificate types keep apart comparisons that earlier exports conflated.

* `SlotReplacement Γ H R`: a replacement `R` for a hypothesis `H` that reconstructs `H`.
  A slot replacement is never strictly weaker than the hypothesis it replaces
  (`SlotReplacement.not_separates`); a proof of the converse makes the two equivalent
  (`SlotReplacement.equivalent_of_converse`).
* `EndpointRoute Γ R G`: a condition `R` that gives the endpoint `G` directly, without
  reconstructing any intermediate hypothesis. Only this kind can reach an endpoint from less
  than an earlier route demanded.

Transport is asymmetric: supply moves forward along an entailment
(`Entails.transport_supply`), refutation moves backward (`Entails.transport_refutation`), and a
failed attempt moves nowhere, since no theorem here mentions attempts.

The canaries at the end record, over `Nat`, `Int` and `Bool`, the shapes of comparisons the
corpus has actually produced: a hypothesis that is redundant only inside its telescope, a
replacement that strengthens a growth bound to vanishing, a separately closed pair whose
equivalence says nothing about the replacement, a rearranged inequality, a sign slice that is
strict yet feasible, independent against synchronised witnesses, clause vacuity against
statement vacuity, and a comparison over an empty context. The module imports nothing beyond
the Lean core.
-/

set_option autoImplicit false

namespace ErdosProblems.ArgumentGraph.Contracts

universe u

section Vocabulary

variable {α : Sort u}

/-- At every admissible context value, `P` gives `Q`. -/
def Entails (Γ P Q : α → Prop) : Prop :=
  ∀ x, Γ x → P x → Q x

/-- Some admissible context value satisfies `P` and fails `Q`. -/
def Separates (Γ P Q : α → Prop) : Prop :=
  ∃ x, Γ x ∧ P x ∧ ¬ Q x

/-- Some admissible context value satisfies `P`. -/
def Feasible (Γ P : α → Prop) : Prop :=
  ∃ x, Γ x ∧ P x

/-- No admissible context value satisfies `P`. -/
def Refuted (Γ P : α → Prop) : Prop :=
  ∀ x, Γ x → ¬ P x

/-- Every admissible context value satisfies `P`: the statement is supplied in this context. -/
def Supplied (Γ P : α → Prop) : Prop :=
  ∀ x, Γ x → P x

/-- Entailment in both directions, in one context. -/
structure Equivalent (Γ P Q : α → Prop) : Prop where
  forward : Entails Γ P Q
  backward : Entails Γ Q P

/-- `new` gives `old`, and some admissible value satisfies `old` while failing `new`. -/
structure StrictlyStronger (Γ new old : α → Prop) : Prop where
  sufficient : Entails Γ new old
  lost : Separates Γ old new

/-- A replacement `R` for the hypothesis `H` that reconstructs `H` in the same context. -/
structure SlotReplacement (Γ H R : α → Prop) : Prop where
  reconstruct : Entails Γ R H

/-- A condition `R` that gives the endpoint `G` directly in the same context. -/
structure EndpointRoute (Γ R G : α → Prop) : Prop where
  reconstruct : Entails Γ R G

end Vocabulary

section Laws

variable {α : Sort u} {Γ P Q S : α → Prop}

theorem Entails.refl : Entails Γ P P :=
  fun _ _ hP => hP

theorem Entails.trans (first : Entails Γ P Q) (second : Entails Γ Q S) : Entails Γ P S :=
  fun x hΓ hP => second x hΓ (first x hΓ hP)

/-- A separator excludes the entailment it separates. -/
theorem Separates.not_entails (h : Separates Γ P Q) : ¬ Entails Γ P Q := by
  intro implication
  obtain ⟨x, hΓ, hP, hnQ⟩ := h
  exact hnQ (implication x hΓ hP)

/-- A feasibility witness excludes a refutation in the same context. -/
theorem Feasible.not_refuted (h : Feasible Γ P) : ¬ Refuted Γ P := by
  intro refutation
  obtain ⟨x, hΓ, hP⟩ := h
  exact refutation x hΓ hP

/-- Supply moves forward along an entailment. -/
theorem Entails.transport_supply (h : Entails Γ P Q) (supply : Supplied Γ P) :
    Supplied Γ Q :=
  fun x hΓ => h x hΓ (supply x hΓ)

/-- Refutation moves backward along an entailment. -/
theorem Entails.transport_refutation (h : Entails Γ P Q) (refutation : Refuted Γ Q) :
    Refuted Γ P :=
  fun x hΓ hP => refutation x hΓ (h x hΓ hP)

/-- A joint obligation is met at one context value, never at two chosen separately. -/
theorem Entails.and_intro (left : Entails Γ P Q) (right : Entails Γ P S) :
    Entails Γ P (fun x => Q x ∧ S x) :=
  fun x hΓ hP => ⟨left x hΓ hP, right x hΓ hP⟩

/-- A separator transfers along entailments that point the right way. -/
theorem Separates.transport {P' Q' : α → Prop} (w : Separates Γ P Q)
    (positive : Entails Γ P P') (negative : Entails Γ Q' Q) : Separates Γ P' Q' := by
  obtain ⟨x, hΓ, hP, hnQ⟩ := w
  exact ⟨x, hΓ, positive x hΓ hP, fun hQ' => hnQ (negative x hΓ hQ')⟩

theorem Equivalent.symm (h : Equivalent Γ P Q) : Equivalent Γ Q P :=
  ⟨h.backward, h.forward⟩

theorem Equivalent.trans (first : Equivalent Γ P Q) (second : Equivalent Γ Q S) :
    Equivalent Γ P S :=
  ⟨first.forward.trans second.forward, second.backward.trans first.backward⟩

/-- Equivalent statements are supplied together. -/
theorem Equivalent.supplied_iff (h : Equivalent Γ P Q) : Supplied Γ P ↔ Supplied Γ Q :=
  ⟨h.forward.transport_supply, h.backward.transport_supply⟩

/-- A strictly stronger statement is never equivalent to the one it strengthens. -/
theorem StrictlyStronger.not_equivalent (h : StrictlyStronger Γ P Q) : ¬ Equivalent Γ P Q :=
  fun e => h.lost.not_entails e.backward

/-- A slot replacement is never strictly weaker than the hypothesis it replaces. -/
theorem SlotReplacement.not_separates (h : SlotReplacement Γ Q P) : ¬ Separates Γ P Q :=
  fun w => w.not_entails h.reconstruct

/-- A slot replacement together with the converse is an equivalence in the same context. -/
theorem SlotReplacement.equivalent_of_converse (h : SlotReplacement Γ Q P)
    (converse : Entails Γ Q P) : Equivalent Γ Q P :=
  ⟨converse, h.reconstruct⟩

/-- A slot replacement composes with a route through the hypothesis it replaces. -/
theorem SlotReplacement.route (h : SlotReplacement Γ Q P) (route : EndpointRoute Γ Q S) :
    EndpointRoute Γ P S :=
  ⟨h.reconstruct.trans route.reconstruct⟩

/-- Over a context that nothing satisfies, every pointwise comparison holds. -/
theorem Equivalent.of_refuted_context (h : Refuted (fun _ => True) Γ) : Equivalent Γ P Q :=
  ⟨fun x hΓ _ => absurd hΓ (h x trivial), fun x hΓ _ => absurd hΓ (h x trivial)⟩

end Laws

namespace Canary

/-! ## Canaries

Each canary records the shape of a comparison the corpus produced, over `Nat`, `Int` or `Bool`.
No canary concerns an Erdős problem. -/

/-- Inside the telescope `k < n`, positivity of `n` is redundant. -/
theorem positivity_redundant_in_telescope :
    Entails (fun p : Nat × Nat => p.1 < p.2) (fun _ => True) (fun p => 0 < p.2) :=
  fun p hk _ => Nat.lt_of_le_of_lt (Nat.zero_le p.1) hk

/-- The same replacement with the telescope dropped and the hypothesis closed on its own. -/
theorem positivity_closed_display_false : ¬ (True → ∀ n : Nat, 0 < n) :=
  fun h => Nat.lt_irrefl 0 (h trivial 0)

/-- A growth bound. -/
def Growth (c : Nat → Nat) : Prop := ∀ m, c m ≤ m

/-- The vanishing bound a search can offer as a replacement for `Growth`. -/
def Vanishing (c : Nat → Nat) : Prop := ∀ m, c m ≤ 0

/-- Replacing a growth bound by vanishing is a strict strengthening. -/
theorem vanishing_strictly_stronger :
    StrictlyStronger (fun _ : Nat → Nat => True) Vanishing Growth := by
  refine ⟨fun c _ hv m => Nat.le_trans (hv m) (Nat.zero_le m), ⟨fun m => m, trivial, ?_, ?_⟩⟩
  · intro m
    exact Nat.le_refl m
  · intro hv
    exact absurd (hv 1) (by decide)

/-- Closed separately, both statements are false, so the two closures are equivalent. -/
theorem separately_closed_equivalence :
    (∀ c : Nat → Nat, Growth c) ↔ (∀ c : Nat → Nat, Vanishing c) := by
  constructor
  · intro h
    exact absurd (h (fun _ => 1) 0) (by decide)
  · intro h
    exact absurd (h (fun _ => 1) 0) (by decide)

/-- A rearranged linear inequality is an equivalence, whatever a bounded search reports. -/
theorem rearranged_inequality_equivalent :
    Equivalent (fun _ : Int × Int => True)
      (fun v => 28 + 37 * v.1 ≤ 56 * v.2) (fun v => 37 * v.1 ≤ 56 * v.2 - 28) :=
  ⟨fun _ _ h => by omega, fun _ _ h => by omega⟩

/-- Under a positive bound `t`, replacing `r < t` by `r ≤ 0` is strict and still feasible. -/
theorem sign_slice_strict_and_feasible :
    StrictlyStronger (fun v : Int × Int => 0 < v.2) (fun v => v.1 ≤ 0) (fun v => v.1 < v.2) ∧
      Feasible (fun v : Int × Int => 0 < v.2) (fun v => v.1 ≤ 0) := by
  refine ⟨⟨fun v ht hr => by omega, ⟨(1, 2), by decide, by decide, by decide⟩⟩,
    ⟨(0, 1), by decide, by decide⟩⟩

/-- Every value has its own witness. -/
def IndependentWitnesses : Prop := ∀ a : Nat, ∃ x : Nat, x = a

/-- One witness serves every value below it. -/
def SynchronisedWitnesses : Prop := ∀ n : Nat, ∃ x : Nat, n ≤ x ∧ ∀ a : Nat, a ≤ x → x = a

theorem independent_not_synchronised : IndependentWitnesses ∧ ¬ SynchronisedWitnesses := by
  refine ⟨fun a => ⟨a, rfl⟩, ?_⟩
  intro h
  obtain ⟨x, hx, hall⟩ := h 1
  have h0 := hall 0 (Nat.zero_le x)
  omega

/-- Closed over the whole type, the implication holds; pointwise, it is refuted. -/
theorem bool_closed_implication : (∀ b : Bool, b = false) → ∀ _ : Bool, False := by
  intro h _
  exact Bool.noConfusion (h true)

theorem bool_pointwise_refuted : ¬ ∀ b : Bool, b = false → False :=
  fun h => h false rfl

/-- A clause that no context value off the switch can reach. -/
def ClauseOffSwitch (v : Nat × Nat) : Prop := v.2 < v.1 ∧ v.1 < v.2

/-- The whole statement: the switch or the clause. -/
def SwitchOrClause (v : Nat × Nat) : Prop := v.1 = 0 ∨ ClauseOffSwitch v

/-- The clause is refuted, while the statement it belongs to is feasible. -/
theorem clause_vacuous_statement_feasible :
    Refuted (fun _ : Nat × Nat => True) ClauseOffSwitch ∧
      Feasible (fun _ : Nat × Nat => True) SwitchOrClause :=
  ⟨fun _ _ h => by unfold ClauseOffSwitch at h; omega, ⟨(0, 0), trivial, Or.inl rfl⟩⟩

/-- Over an empty context every comparison holds, so feasibility of the context comes first. -/
theorem empty_context_equivalent (P Q : Empty → Prop) :
    Equivalent (fun _ : Empty => True) P Q :=
  ⟨fun x => x.elim, fun x => x.elim⟩

end Canary

end ErdosProblems.ArgumentGraph.Contracts
