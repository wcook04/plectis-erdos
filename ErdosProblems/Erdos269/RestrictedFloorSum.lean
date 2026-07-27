import ErdosProblems.Erdos269.ResidueEscape
import Mathlib.Tactic.Ring

/-!
# Erdős #269: local-window residue reduction

This public module isolates the exact algebraic bridge from a
denominator-dependent local-window escape theorem to extinction of a positive
reduced integral carry.  It does not assert that the actual ordered
`{2,3,5}` forcing word supplies the required escaping windows.
-/

namespace ErdosProblems.Erdos269

/-- Multiplicative base accumulated across a local window. -/
def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len

/-- Affine forcing accumulated across the same local window. -/
def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)

/-- Any first-order affine recurrence unrolls exactly into the local base and
local forcing. -/
theorem affineRecurrence_window
    (A b e : ℕ → ℤ) (lo len : ℕ)
    (hrec : ∀ n, A (n + 1) = b n * A n + e n) :
    A (lo + len) =
      windowBase b lo len * A lo + windowForcing b e lo len := by
  induction len with
  | zero => simp [windowBase, windowForcing]
  | succ len ih =>
      rw [Nat.add_succ, hrec, ih]
      simp only [windowBase, windowForcing]
      ring

/-- Scaling every forcing term scales the accumulated local numerator by the
same constant. -/
theorem windowForcing_const_mul
    (b e : ℕ → ℤ) (B : ℤ) (lo len : ℕ) :
    windowForcing b (fun n => B * e n) lo len =
      B * windowForcing b e lo len := by
  induction len with
  | zero => simp [windowForcing]
  | succ len ih =>
      simp only [windowForcing, ih]
      ring

/-- Integral-carry form of the local-window identity. -/
theorem integralCarry_window
    (c b m : ℕ → ℤ) (B : ℤ) (lo len : ℕ)
    (hrec : ∀ n, c (n + 1) = b n * c n - B * m n) :
    c (lo + len) =
      windowBase b lo len * c lo -
        B * windowForcing b m lo len := by
  have hrec' : ∀ n, c (n + 1) = b n * c n + (-B) * m n := by
    intro n
    rw [hrec]
    ring
  rw [affineRecurrence_window c b (fun n => (-B) * m n) lo len hrec']
  rw [windowForcing_const_mul b m (-B) lo len]
  ring

/-- The exact remaining producer after local-window compression.  The short
bound is denominator-dependent because a rational carry bound scales with
the reduced denominator `B`. -/
def CofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ) : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 →
    ∀ lo₀ : ℕ, ∃ lo len : ℕ,
      lo₀ ≤ lo ∧ 0 < len ∧
      0 < Int.natAbs (windowBase (fun n => b n) lo len) ∧
      shortBound B (lo + len) <
        leastPositiveResidue
          (Int.natAbs (windowBase (fun n => b n) lo len))
          (-((B : ℤ) *
            windowForcing (fun n => b n) (fun n => m n) lo len))

/-- A denominator-dependent cofinal local-window escape rules out every
positive reduced carry satisfying the matching bound. -/
theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (d : ℕ → ℤ)
    (hrec : ∀ n,
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) :
    False := by
  rcases hescape B hBpos hBcoprime 0 with
    ⟨lo, len, _hlo, _hlen, hbasePos, hresidueEscape⟩
  let W : ℤ := windowBase (fun n => (b n : ℤ)) lo len
  let F : ℤ := windowForcing
    (fun n => (b n : ℤ)) (fun n => (m n : ℤ)) lo len
  have hwindow :
      d (lo + len) = W * d lo - (B : ℤ) * F := by
    simpa [W, F] using
      integralCarry_window d
        (fun n => (b n : ℤ)) (fun n => (m n : ℤ))
        (B : ℤ) lo len hrec
  have hmodW :
      Int.ModEq W (d (lo + len)) (-((B : ℤ) * F)) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-d lo, ?_⟩
    rw [hwindow]
    ring
  have hmod :
      Int.ModEq (Int.natAbs W)
        (d (lo + len)) (-((B : ℤ) * F)) :=
    (Int.modEq_natAbs).2 hmodW
  exact no_bounded_positive_int_state_of_leastPositiveResidue
    (by simpa [W] using hbasePos)
    (hpos (lo + len))
    (hbound (lo + len))
    (by simpa [W, F] using hresidueEscape)
    hmod

end ErdosProblems.Erdos269
