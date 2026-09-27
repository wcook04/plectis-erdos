import Mathlib.Tactic.Linarith

-- CANDIDATE: elementary proof schemas; not compiled in this response.
-- Scalar source-binding remains separate from these general theorems.

namespace Plectis.ObservableContracts
universe u v

/-- A weakest condition in a CHOSEN observable language, relative to Gamma.
The hidden type may depend on the observable. -/
def Safe {α : Sort u} {β : α → Sort v}
    (Gamma E : (x : α) → β x → Prop) (x : α) : Prop :=
  ∀ y, Gamma x y → E x y

theorem safe_iff_no_countermodel {α : Sort u} {β : α → Sort v}
    (Gamma E : (x : α) → β x → Prop) (x : α) :
    Safe Gamma E x ↔ ¬ ∃ y, Gamma x y ∧ ¬ E x y := by
  classical
  constructor
  · intro hs hbad
    obtain ⟨y, hGamma, hnot⟩ := hbad
    exact hnot (hs y hGamma)
  · intro hn y hGamma
    by_contra hE
    exact hn ⟨y, hGamma, hE⟩

theorem safe_is_sufficient {α : Sort u} {β : α → Sort v}
    (Gamma E : (x : α) → β x → Prop) (x : α) (y : β x)
    (hGamma : Gamma x y) (hs : Safe Gamma E x) : E x y :=
  hs y hGamma

theorem safe_is_weakest {α : Sort u} {β : α → Sort v}
    (Gamma E : (x : α) → β x → Prop) (C : α → Prop)
    (hC : ∀ x, C x → ∀ y, Gamma x y → E x y) :
    ∀ x, C x → Safe Gamma E x := by
  intro x hx y hGamma
  exact hC x hx y hGamma

/-- Exact subset-budget transport. No independence or probabilistic premise. -/
theorem subset_budget (mass m b u B U g c : ℝ)
    (hpartition : m + b + u = mass)
    (hb : b ≤ B) (hu : u ≤ U) (hc : 0 ≤ c)
    (hgap : g ≤ c * (mass - B - U)) : g ≤ c * m := by
  have hremaining : mass - B - U ≤ m := by linarith
  exact le_trans hgap (mul_le_mul_of_nonneg_left hremaining hc)

/-- The full-block alternative pays for the complement instead. -/
theorem whole_block_budget (t g b u B U c : ℝ)
    (hpartition_bound : t ≤ g + b + u)
    (hb : b ≤ B) (hu : u ≤ U)
    (hgap : g ≤ c - B - U) : t ≤ c := by
  linarith

end Plectis.ObservableContracts

-- CANDIDATE: compile with the pinned Lean environment before admission.
-- The scalar-to-corpus binding is a separate required theorem.
namespace Plectis.AbductiveCandidate
theorem goal_0 (b : ℝ) (g : ℝ) (gamma : ℝ) (m : ℝ) (u : ℝ)
    (h0 : (((1 : ℝ) * b) + ((1 : ℝ) * m) + ((1 : ℝ) * u) ≤ (1 : ℝ)))
    (h1 : (((-1 : ℝ) * b) + ((-1 : ℝ) * m) + ((-1 : ℝ) * u) ≤ (-1 : ℝ)))
    (h2 : (((1 : ℝ) * b) < (1 / 100 : ℝ)))
    (h3 : (((1 : ℝ) * u) < (8 / 25 : ℝ)))
    (h4 : (((-1 : ℝ) * b) ≤ (0 : ℝ)))
    (h5 : (((-1 : ℝ) * u) ≤ (0 : ℝ)))
    (h6 : (((1 : ℝ) * g) + ((-1 : ℝ) * gamma) ≤ (0 : ℝ)))
    (h7 : (((-1 : ℝ) * g) + ((-1 : ℝ) * m) ≤ (0 : ℝ)))
    (h8 : (((1 : ℝ) * g) + ((-1 : ℝ) * m) ≤ (0 : ℝ)))
    (hsafe : (((0 : ℝ) < (0 : ℝ)) ∨ (((1 : ℝ) * gamma) ≤ (603 / 1000 : ℝ)))) : (((1 : ℝ) * g) + ((-9 / 10 : ℝ) * m) ≤ (0 : ℝ)) := by
  rcases hsafe with hs | hs
  · by_contra hbad
    have hneg : (((-1 : ℝ) * g) + ((9 / 10 : ℝ) * m) < (0 : ℝ)) := by linarith only [hbad]
    have hout : ((0 : ℝ) ≤ (0 : ℝ)) := by
      linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, hneg]
    linarith only [hout, hs]
  · by_contra hbad
    have hneg : (((-1 : ℝ) * g) + ((9 / 10 : ℝ) * m) < (0 : ℝ)) := by linarith only [hbad]
    have hout : (((-1 : ℝ) * gamma) < (-603 / 1000 : ℝ)) := by
      linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, hneg]
    linarith only [hout, hs]
end Plectis.AbductiveCandidate

-- CANDIDATE: compile with the pinned Lean environment before admission.
-- The scalar-to-corpus binding is a separate required theorem.
namespace Plectis.AbductiveCandidate
theorem goal_0 (b : ℝ) (g : ℝ) (gamma : ℝ) (m : ℝ) (t : ℝ) (u : ℝ)
    (h0 : (((1 : ℝ) * b) + ((1 : ℝ) * m) + ((1 : ℝ) * u) ≤ (1 : ℝ)))
    (h1 : (((-1 : ℝ) * b) + ((-1 : ℝ) * m) + ((-1 : ℝ) * u) ≤ (-1 : ℝ)))
    (h2 : (((1 : ℝ) * b) < (1 / 100 : ℝ)))
    (h3 : (((1 : ℝ) * u) < (8 / 25 : ℝ)))
    (h4 : (((-1 : ℝ) * b) ≤ (0 : ℝ)))
    (h5 : (((-1 : ℝ) * u) ≤ (0 : ℝ)))
    (h6 : (((1 : ℝ) * g) + ((-1 : ℝ) * gamma) ≤ (0 : ℝ)))
    (h7 : (((-1 : ℝ) * g) + ((-1 : ℝ) * m) ≤ (0 : ℝ)))
    (h8 : (((1 : ℝ) * g) + ((-1 : ℝ) * m) ≤ (0 : ℝ)))
    (h9 : (((-1 : ℝ) * b) + ((-1 : ℝ) * g) + ((1 : ℝ) * t) + ((-1 : ℝ) * u) ≤ (0 : ℝ)))
    (h10 : (((-1 : ℝ) * t) ≤ (1 : ℝ)))
    (hsafe : (((0 : ℝ) < (0 : ℝ)) ∨ (((1 : ℝ) * gamma) ≤ (57 / 100 : ℝ)))) : (((1 : ℝ) * t) ≤ (9 / 10 : ℝ)) := by
  rcases hsafe with hs | hs
  · by_contra hbad
    have hneg : (((-1 : ℝ) * t) < (-9 / 10 : ℝ)) := by linarith only [hbad]
    have hout : ((0 : ℝ) ≤ (0 : ℝ)) := by
      linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hneg]
    linarith only [hout, hs]
  · by_contra hbad
    have hneg : (((-1 : ℝ) * t) < (-9 / 10 : ℝ)) := by linarith only [hbad]
    have hout : (((-1 : ℝ) * gamma) < (-57 / 100 : ℝ)) := by
      linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hneg]
    linarith only [hout, hs]
end Plectis.AbductiveCandidate
