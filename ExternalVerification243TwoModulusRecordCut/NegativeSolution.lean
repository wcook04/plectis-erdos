/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Deliberately incomplete results for the #243 two-modulus package

These same-named declarations retain the full hypothesis lists but replace
each conclusion with an unrelated, strictly weaker claim: an inequality on the
crossing pair in place of the contradiction, and a bound only at the starting
index in place of the whole orbit. Comparator must reject both as type
mismatches against `Challenge.lean`.
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
    u ≤ u' := by
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
    u s < H := by
  sorry

end Erdos249257.ExternalVerification243TwoModulusRecordCut
