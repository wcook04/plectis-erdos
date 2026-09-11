import Erdos249257.HalfCylinderFiniteShadow

/-!
# Exact fixed-coefficient rewind and the residual seam pair

For a row with common proper-divisor coefficient `c`, the canonical inverse
parent selected for a positive target carry `k` is

`T_c(k) = (k + c + 1) / 2`.

Iterating these maps does not contract a short interval to one point without
a dyadic phase condition.  It contracts an interval of width at most `2^L`
to either one ancestor or two adjacent ancestors.  This file records the
exact closed form, the phase criterion, and a small downstream interface for
the adjacent (one-hole seam) case.
-/

namespace Erdos249257
namespace FixedCoeffRewind

/-- Canonical inverse parent for a target carry under common coefficient
`c`.  The extra `1` is the usual natural-number expression for the ceiling
of `(k + c) / 2`. -/
def parent (c k : ℕ) : ℕ := (k + c + 1) / 2

/-- Apply the coefficient rows in list order, earliest row first. -/
def rewind : List ℕ → ℕ → ℕ
  | [], k => k
  | c :: cs, k => rewind cs (parent c k)

/-- Numerator offset accumulated by a rewind.  A later parent map is one
binary place more significant than every earlier map. -/
def offset : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + 1 + 2 * offset cs

/-- Common denominator in the closed form. -/
def denom (cs : List ℕ) : ℕ := 2 ^ cs.length

/-- The dyadic phase of the left endpoint `1`. -/
def phase (cs : List ℕ) : ℕ := (1 + offset cs) % denom cs

@[simp] theorem denom_pos (cs : List ℕ) : 0 < denom cs := by
  simp [denom]

/-- Exact iterate formula.  Floor-of-floor composition is absorbed into a
single division because every later translation is scaled by the appropriate
power of two in `offset`. -/
theorem rewind_eq_closedForm (cs : List ℕ) (k : ℕ) :
    rewind cs k = (k + offset cs) / denom cs := by
  induction cs generalizing k with
  | nil => simp [rewind, offset, denom]
  | cons c cs ih =>
      rw [rewind, ih]
      simp only [parent, offset, denom, List.length_cons]
      calc
        ((k + c + 1) / 2 + offset cs) / 2 ^ cs.length =
            ((k + c + 1 + 2 * offset cs) / 2) / 2 ^ cs.length := by
          rw [Nat.add_mul_div_left (k + c + 1) (offset cs)
            (by omega : 0 < 2)]
        _ = (k + c + 1 + 2 * offset cs) / (2 * 2 ^ cs.length) :=
          Nat.div_div_eq_div_mul _ _ _
        _ = (k + (c + 1 + 2 * offset cs)) / 2 ^ (cs.length + 1) := by
          congr 1
          · omega
          · simp [pow_succ, Nat.mul_comm]

/-- Rewind is monotone in the terminal carry. -/
theorem rewind_mono (cs : List ℕ) : Monotone (rewind cs) := by
  intro a b hab
  rw [rewind_eq_closedForm, rewind_eq_closedForm]
  exact Nat.div_le_div_right (Nat.add_le_add_right hab (offset cs))

/-- Adding a numerator shorter than the denominator preserves the current
quotient exactly iff it does not overflow the current residue. -/
theorem add_div_eq_left_div_iff_phase_fit
    {x y D : ℕ} (hD : 0 < D) (hy : y < D) :
    (x + y) / D = x / D ↔ x % D + y < D := by
  rw [Nat.add_div hD, Nat.div_eq_of_lt hy, Nat.mod_eq_of_lt hy]
  simp only [Nat.add_zero]
  split_ifs <;> omega

/-- If the input interval `[1,B]` has width at most the rewind denominator,
its two endpoint ancestors differ by at most one.  This is the corrected
contraction statement: a singleton conclusion requires phase information. -/
theorem rewind_endpoint_le_succ
    (cs : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hwidth : B ≤ denom cs) :
    rewind cs B ≤ rewind cs 1 + 1 := by
  rw [rewind_eq_closedForm, rewind_eq_closedForm]
  have hy : B - 1 < denom cs := by
    have hD := denom_pos cs
    omega
  have hsum : B + offset cs = (1 + offset cs) + (B - 1) := by
    omega
  rw [hsum, Nat.add_div (denom_pos cs), Nat.div_eq_of_lt hy]
  split_ifs <;> omega

/-- Exact singleton criterion for the endpoints. -/
theorem rewind_endpoint_eq_iff_phase_fit
    (cs : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hwidth : B ≤ denom cs) :
    rewind cs B = rewind cs 1 ↔
      phase cs + (B - 1) < denom cs := by
  rw [rewind_eq_closedForm, rewind_eq_closedForm]
  have hy : B - 1 < denom cs := by
    have hD := denom_pos cs
    omega
  have hsum : B + offset cs = (1 + offset cs) + (B - 1) := by
    omega
  rw [hsum]
  simpa [phase] using
    (add_div_eq_left_div_iff_phase_fit
      (x := 1 + offset cs) (y := B - 1) (D := denom cs)
      (denom_pos cs) hy)

/-- The residual alternative after maximal fixed-coefficient contraction:
the right endpoint has landed at the successor of the left endpoint.  Every
interior target then lands on one of these same two ancestors (proved below),
so this is the exact scalar socket for a canonical one-hole seam argument. -/
def IsSeamPair (cs : List ℕ) (B : ℕ) : Prop :=
  rewind cs B = rewind cs 1 + 1

/-- The seam-pair alternative is exactly dyadic phase overflow. -/
theorem isSeamPair_iff_phase_overflow
    (cs : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hwidth : B ≤ denom cs) :
    IsSeamPair cs B ↔ denom cs ≤ phase cs + (B - 1) := by
  have heq := rewind_endpoint_eq_iff_phase_fit cs hB hwidth
  have hgap := rewind_endpoint_le_succ cs hB hwidth
  have hmono : rewind cs 1 ≤ rewind cs B := rewind_mono cs hB
  constructor
  · intro hseam
    change rewind cs B = rewind cs 1 + 1 at hseam
    have hne : rewind cs B ≠ rewind cs 1 := by omega
    have hnotfit : ¬ phase cs + (B - 1) < denom cs := by
      intro hfit
      exact hne (heq.mpr hfit)
    omega
  · intro hover
    change rewind cs B = rewind cs 1 + 1
    have hne : rewind cs B ≠ rewind cs 1 := by
      intro hend
      have hfit := heq.mp hend
      omega
    omega

/-- Under the seam-pair alternative, every rewound target lies on one of the
two adjacent ancestors. -/
theorem rewind_eq_left_or_right_of_isSeamPair
    (cs : List ℕ) {B k : ℕ}
    (hk : 1 ≤ k) (hkB : k ≤ B) (hseam : IsSeamPair cs B) :
    rewind cs k = rewind cs 1 ∨
      rewind cs k = rewind cs 1 + 1 := by
  have hlo : rewind cs 1 ≤ rewind cs k := rewind_mono cs hk
  have hhi : rewind cs k ≤ rewind cs B := rewind_mono cs hkB
  change rewind cs B = rewind cs 1 + 1 at hseam
  omega

/-- The entire interval is a singleton exactly when its endpoints agree. -/
theorem rewind_interval_singleton_iff_endpoint_eq
    (cs : List ℕ) {B : ℕ} (hB : 1 ≤ B) :
    (∀ k : ℕ, 1 ≤ k → k ≤ B → rewind cs k = rewind cs 1) ↔
      rewind cs B = rewind cs 1 := by
  constructor
  · intro hall
    exact hall B hB (le_refl B)
  · intro hend k hk hkB
    have hlo : rewind cs 1 ≤ rewind cs k := rewind_mono cs hk
    have hhi : rewind cs k ≤ rewind cs B := rewind_mono cs hkB
    omega

/-- Full interval phase criterion. -/
theorem rewind_interval_singleton_iff_phase_fit
    (cs : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hwidth : B ≤ denom cs) :
    (∀ k : ℕ, 1 ≤ k → k ≤ B → rewind cs k = rewind cs 1) ↔
      phase cs + (B - 1) < denom cs := by
  exact (rewind_interval_singleton_iff_endpoint_eq cs hB).trans
    (rewind_endpoint_eq_iff_phase_fit cs hB hwidth)

/-- Correct fixed-tail contraction dichotomy.  Width alone proves exactly a
singleton-or-seam-pair result, never an unconditional singleton. -/
theorem rewind_singleton_or_isSeamPair
    (cs : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hwidth : B ≤ denom cs) :
    (∀ k : ℕ, 1 ≤ k → k ≤ B → rewind cs k = rewind cs 1) ∨
      IsSeamPair cs B := by
  by_cases hend : rewind cs B = rewind cs 1
  · exact Or.inl ((rewind_interval_singleton_iff_endpoint_eq cs hB).mpr hend)
  · right
    change rewind cs B = rewind cs 1 + 1
    have hmono : rewind cs 1 ≤ rewind cs B := rewind_mono cs hB
    have hgap := rewind_endpoint_le_succ cs hB hwidth
    omega

#print axioms denom_pos
#print axioms rewind_eq_closedForm
#print axioms rewind_mono
#print axioms add_div_eq_left_div_iff_phase_fit
#print axioms rewind_endpoint_le_succ
#print axioms rewind_endpoint_eq_iff_phase_fit
#print axioms isSeamPair_iff_phase_overflow
#print axioms rewind_eq_left_or_right_of_isSeamPair
#print axioms rewind_interval_singleton_iff_endpoint_eq
#print axioms rewind_interval_singleton_iff_phase_fit
#print axioms rewind_singleton_or_isSeamPair

end FixedCoeffRewind
end Erdos249257
