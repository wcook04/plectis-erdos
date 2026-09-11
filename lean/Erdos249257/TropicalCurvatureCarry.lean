import Erdos249257.CurvatureCarry

set_option maxRecDepth 10000

/-!
# Fixed-precision tropical curvature no-go

This module isolates the elementary obstruction behind a proposed
valuation--unit-word attack on the curvature carry.  A fixed number of odd
unit bits leaves an arbitrary integral high quotient at every offset.  Those
quotients can always be chosen so that the next carry state is centred in the
corresponding dyadic interval, and this construction iterates over every
finite word.

The result is a no-go theorem for the bounded local signature alone.  It does
not rule out arithmetic relations between the high quotients, growing unit
precision, or exact rough-prime labels, and it does not settle Erdős problem
#249.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

/-- A nonzero 2-adic valuation--unit symbol.  `valuation` records the power of
two and `unit` is an odd representative of the retained unit bits. -/
structure VUSymbol where
  valuation : ℕ
  unit : ℤ

/-- Integers carrying the fixed-precision symbol `σ` are obtained by varying
an unrestricted high quotient `z`. -/
def VUCompatible (u : ℕ) (σ : VUSymbol) (c : ℤ) : Prop :=
  Odd σ.unit ∧
    ∃ z : ℤ,
      c = (2 : ℤ) ^ σ.valuation * (σ.unit + (2 : ℤ) ^ u * z)

/-- The modulus left by retaining `u` unit bits at valuation `σ.valuation`. -/
def vuModulus (u : ℕ) (σ : VUSymbol) : ℤ :=
  (2 : ℤ) ^ (σ.valuation + u)

/-- Half of `vuModulus`, available when at least one unit bit is retained. -/
def vuRadius (u : ℕ) (σ : VUSymbol) : ℤ :=
  (2 : ℤ) ^ (σ.valuation + u - 1)

/-- The least representative of the valuation--unit cylinder. -/
def vuBaseDigit (σ : VUSymbol) : ℤ :=
  (2 : ℤ) ^ σ.valuation * σ.unit

/-- Recenter `2e + vuBaseDigit σ` in the symmetric interval of radius
`vuRadius u σ`. -/
def vuCentredStep (u : ℕ) (σ : VUSymbol) (e : ℤ) : ℤ :=
  let R := vuRadius u σ
  let M := vuModulus u σ
  (2 * e + vuBaseDigit σ + R) % M - R

lemma vuModulus_eq_two_mul_radius (u : ℕ) (σ : VUSymbol) (hu : 0 < u) :
    vuModulus u σ = 2 * vuRadius u σ := by
  unfold vuModulus vuRadius
  calc
    (2 : ℤ) ^ (σ.valuation + u) =
        2 ^ ((σ.valuation + u - 1) + 1) := by
          congr 1
          omega
    _ = 2 ^ (σ.valuation + u - 1) * 2 := by rw [pow_succ]
    _ = 2 * 2 ^ (σ.valuation + u - 1) := by ring

/-- Every one-step fixed-precision symbol has a compatible digit that
recentres an arbitrary incoming carry state. -/
theorem vu_step_has_centred_completion (u : ℕ) (σ : VUSymbol)
    (hu : 0 < u) (hodd : Odd σ.unit) (e : ℤ) :
    ∃ c e' : ℤ,
      VUCompatible u σ c ∧
      e' = 2 * e + c ∧
      |e'| ≤ vuRadius u σ := by
  let R := vuRadius u σ
  let M := vuModulus u σ
  let x := 2 * e + vuBaseDigit σ
  let y := x + R
  let e' := y % M - R
  let c := e' - 2 * e
  have hM : M = 2 * R := by
    simpa [M, R] using vuModulus_eq_two_mul_radius u σ hu
  have hRpos : 0 < R := by
    dsimp [R, vuRadius]
    positivity
  have hMpos : 0 < M := by omega
  have hrem_nonneg : 0 ≤ y % M := Int.emod_nonneg y (ne_of_gt hMpos)
  have hrem_lt : y % M < M := Int.emod_lt_of_pos y hMpos
  have hdiv := Int.mul_ediv_add_emod y M
  have hc : VUCompatible u σ c := by
    refine ⟨hodd, -(y / M), ?_⟩
    have hrem : y % M = y - M * (y / M) := by linarith [hdiv]
    dsimp [c, e']
    rw [hrem]
    dsimp [y, x, M, vuModulus, vuBaseDigit]
    rw [pow_add]
    ring
  have hbound : |e'| ≤ R := by
    rw [abs_le]
    dsimp [e']
    omega
  exact ⟨c, e', hc, by simp [c], by simpa [R] using hbound⟩

/-- An exact finite carry orbit whose successive input digits realise the
listed valuation--unit symbols. -/
inductive VUOrbit (u : ℕ) : ℤ → List VUSymbol → List ℤ → Prop
  | nil (e : ℤ) : VUOrbit u e [] []
  | cons (e c e' : ℤ) (σ : VUSymbol) (symbols : List VUSymbol)
      (states : List ℤ) (hcompat : VUCompatible u σ c)
      (hstep : e' = 2 * e + c) (htail : VUOrbit u e' symbols states) :
      VUOrbit u e (σ :: symbols) (e' :: states)

/-- Every finite word of odd valuation--unit symbols has a compatible carry
orbit centred at every prefix.  The initial state is arbitrary. -/
theorem vu_word_has_prefix_locked_completion (u : ℕ) (hu : 0 < u)
    (symbols : List VUSymbol) (hodd : ∀ σ ∈ symbols, Odd σ.unit) (e : ℤ) :
    ∃ states : List ℤ,
      VUOrbit u e symbols states ∧
      List.Forall₂ (fun σ e' => |e'| ≤ vuRadius u σ) symbols states := by
  induction symbols generalizing e with
  | nil =>
      exact ⟨[], VUOrbit.nil e, .nil⟩
  | cons σ symbols ih =>
      have hσ : Odd σ.unit := hodd σ (by simp)
      obtain ⟨c, e', hcompat, hstep, hbound⟩ :=
        vu_step_has_centred_completion u σ hu hσ e
      have htailOdd : ∀ τ ∈ symbols, Odd τ.unit := by
        intro τ hτ
        exact hodd τ (by simp [hτ])
      obtain ⟨states, horbit, hbounds⟩ := ih htailOdd e'
      exact ⟨e' :: states,
        VUOrbit.cons e c e' σ symbols states hcompat hstep horbit,
        .cons hbound hbounds⟩

/-- Formal fixed-precision tropical no-go: bounded local valuation--unit data
alone never excludes all finite centred carry completions. -/
theorem fixedPrecisionTropicalNoGo (u : ℕ) (hu : 0 < u)
    (symbols : List VUSymbol) (hodd : ∀ σ ∈ symbols, Odd σ.unit) (e : ℤ) :
    ∃ states : List ℤ,
      VUOrbit u e symbols states ∧
      List.Forall₂ (fun σ e' => |e'| ≤ vuRadius u σ) symbols states :=
  vu_word_has_prefix_locked_completion u hu symbols hodd e

#print axioms vu_step_has_centred_completion
#print axioms vu_word_has_prefix_locked_completion
#print axioms fixedPrecisionTropicalNoGo

end TotientTailPeriodKiller
end Erdos249257
