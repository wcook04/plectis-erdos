import Erdos249257.TropicalCurvatureCarry
import Mathlib.Tactic

/-!
# Erdős #249: prime-ray cyclotomic curvature interfaces

Problem-owned algebraic producer/consumer interfaces extracted from the
legacy curvature programme.  Polynomial resultant realisability and
Archimedean growth remain explicit upstream obligations.
-/

namespace ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature

/-- Mixed Boolean curvature on a two-anchor rectangle. -/
def checkerboard (F : Bool → Bool → ℤ) : ℤ :=
  F true true - F true false - F false true + F false false

/-- The checkerboard kills every sum of one-coordinate backgrounds. -/
theorem checkerboard_separable (u v : Bool → ℤ) :
    checkerboard (fun i j => u i + v j) = 0 := by
  simp [checkerboard]
  ring

/-- The checkerboard is the unique two-by-two joint annihilator up to scale. -/
theorem checkerboard_unique
    (c00 c10 c01 c11 : ℤ)
    (hrow0 : c00 + c01 = 0)
    (hrow1 : c10 + c11 = 0)
    (hcol0 : c00 + c10 = 0)
    (hcol1 : c01 + c11 = 0) :
    c10 = -c00 ∧ c01 = -c00 ∧ c11 = c00 := by
  constructor
  · omega
  · constructor <;> omega

/-- Abstract squarefree divisor-layer cancellation.  The hypotheses are the
four explicit divisor factorizations, so no resultant API is hidden here. -/
theorem fourPoint_layer_identity
    (A C : ℕ → ℕ) (r s q : ℕ)
    (hq : A q = C 1 * C q)
    (hrq : A (r * q) = C 1 * C r * C q * C (r * q))
    (hsq : A (s * q) = C 1 * C s * C q * C (s * q))
    (hrsq :
      A (r * s * q) =
        C 1 * C r * C s * C q *
          C (r * s) * C (r * q) * C (s * q) * C (r * s * q)) :
    A (r * s * q) * A q =
      A (r * q) * A (s * q) * C (r * s) * C (r * s * q) := by
  rw [hrsq, hq, hrq, hsq]
  ring

/-- Any prescribed residue class modulo an even modulus admits a digit which
recentres an affine carry step.  This generalises the legacy fixed-precision
valuation/unit completion no-go. -/
theorem residueClass_step_has_centred_completion
    (b a e M R : ℤ) (hR : 0 < R) (hM : M = 2 * R) :
    ∃ c e' : ℤ,
      (∃ z : ℤ, c = a + M * z) ∧
      e' = b * e + c ∧
      |e'| ≤ R := by
  let y := b * e + a + R
  let e' := y % M - R
  let c := e' - b * e
  have hMpos : 0 < M := by omega
  have hrem_nonneg : 0 ≤ y % M :=
    Int.emod_nonneg y (ne_of_gt hMpos)
  have hrem_lt : y % M < M :=
    Int.emod_lt_of_pos y hMpos
  have hdiv := Int.mul_ediv_add_emod y M
  have hclass : ∃ z : ℤ, c = a + M * z := by
    refine ⟨-(y / M), ?_⟩
    have hrem : y % M = y - M * (y / M) := by
      linarith [hdiv]
    dsimp [c, e']
    rw [hrem]
    dsimp [y]
    ring
  have hstep : e' = b * e + c := by
    dsimp [c]
    ring
  have hbound : |e'| ≤ R := by
    rw [abs_le]
    dsimp [e']
    omega
  exact ⟨c, e', hclass, hstep, hbound⟩

/-- Eventual nontrivial, clean cyclotomic layers on the prime ray `m*q`. -/
def PrimeRayLayerSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q)

/-- Every rational prime divisor of a layer supplies an exact-order witness
in extension degree at most `d`. -/
def BoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∀ q p : ℕ,
    q.Prime → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1

/-- Large prime-ray layers escape every prescribed finite prime support. -/
def FinitePrimeSupportEscape (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)

end ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature
