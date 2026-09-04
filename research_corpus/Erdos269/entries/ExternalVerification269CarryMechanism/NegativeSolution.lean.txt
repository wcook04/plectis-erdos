/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Deliberately weakened #269 carry fixture

The local-window theorem assumes the strictly stronger bound `<` in place of
the checked `≤`.  Comparator must reject the watered-down statement.
-/

namespace Erdos249257.ExternalVerification269CarryMechanism

def carryResidue (B c : ℤ) : ℤ := c % B
def carryQuotient (B c : ℤ) : ℤ := c / B
def residueDigit (B base residue nextResidue : ℤ) : ℤ :=
  (base * residue - nextResidue) / B

theorem carry_eq_residueDigit_add_coboundary
    (B : ℤ) (hB : 0 < B)
    (base carry digit : ℕ → ℤ)
    (hrec : ∀ n,
      carry (n + 1) = base n * carry n - B * digit n) :
    let residue := fun n => carryResidue B (carry n)
    let quotient := fun n => carryQuotient B (carry n)
    ∀ n,
      digit n =
        residueDigit B (base n)
          (residue n) (residue (n + 1)) +
        base n * quotient n - quotient (n + 1) := by
  sorry

def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))

def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len

def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)

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

theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (d : ℕ → ℤ)
    (hrec : ∀ n,
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) < shortBound B n) :
    False := by
  sorry

end Erdos249257.ExternalVerification269CarryMechanism
