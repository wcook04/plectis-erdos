/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the two-modulus record cut in Erdős #243

Two source-independent propositions.

The finite cut fixes a height `H ≡ 5 (mod 6)` and two moduli greater than one,
one dividing `H` and one dividing `H + 2`, both dividing the next reduced
denominator.  Then no primitive step can cross `H` with a jump of at most four.
Two forbidden landings are killed by the moduli against coprimality of the next
pair; the remaining three landings are killed by the congruence on `H`, which
makes `H + 1` divisible by six and so collides with `H - 3`, `H - 2` and
`H - 1` in turn.

The orbit form assumes those two moduli persist in the reduced denominator from
an index onward, places `H` above the running maximum there, and bounds every
record-setting jump by four; the conclusion is that the orbit never reaches `H`.

Boundary.  Persistence is a hypothesis, not a conclusion, and the cut is sharp:
the source module records a genuine primitive step crossing both forbidden
landings in one jump of size five.  Erdős #243 remains open.
-/

namespace Erdos249257.ExternalVerification243TwoModulusRecordCut

/-- The running maximum of a natural-valued sequence. -/
def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

/-- **Two-modulus cut.**  No primitive step crosses a height congruent to five
modulo six with a jump of at most four, when two moduli greater than one divide
`H` and `H + 2` respectively and both divide the next reduced denominator. -/
theorem two_modulus_cut
    {H m l u u' v' : ℕ}
    (hH : H % 6 = 5)
    (hmH : m ∣ H) (hlH : l ∣ H + 2)
    (hm1 : 1 < m) (hl1 : 1 < l)
    (hmv' : m ∣ v') (hlv' : l ∣ v')
    (hcop' : Nat.Coprime u' v')
    (hadj : Nat.Coprime u u')
    (hlo : u < H) (hhi : H ≤ u') (hjump : u' ≤ u + 4) :
    False := by
  sorry

/-- **Two-modulus record cut.**  If two moduli persist in the reduced
denominator from an index onward, a height congruent to five modulo six sits
above the running maximum there and is divided as above, and every
record-setting step rises by at most four, then the orbit never reaches that
height. -/
theorem two_modulus_record_cut
    (a u v w hc : ℕ → ℕ) (m l s H : ℕ)
    (hm1 : 1 < m) (hl1 : 1 < l)
    (hH : H % 6 = 5)
    (hmH : m ∣ H) (hlH : l ∣ H + 2)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hmv : ∀ n, s ≤ n → m ∣ v n)
    (hlv : ∀ n, s ≤ n → l ∣ v n)
    (hRs : runningMax u s < H)
    (hrec : ∀ n, s ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 4) :
    ∀ n, s ≤ n → u n < H := by
  sorry

end Erdos249257.ExternalVerification243TwoModulusRecordCut
