/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.TwoModulusRecordCut

/-!
# Source transport for the two-modulus record cut in Erdős #243

The finite cut is already stated in Mathlib-only vocabulary and transports
directly. The orbit form needs only that the locally defined `runningMax`
agrees with the corpus `runningMax` (same primitive recursion).
-/
namespace Erdos249257.ExternalVerification243TwoModulusRecordCut

def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

/-- The local `runningMax` is the corpus `runningMax`. -/
theorem runningMax_eq (u : ℕ → ℕ) (n : ℕ) :
    runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
  induction n with
  | zero => simp [runningMax, ErdosProblems.Erdos243.runningMax]
  | succ k ih => simp [runningMax, ErdosProblems.Erdos243.runningMax, ih]

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
    False :=
  ErdosProblems.Erdos243.two_modulus_cut hH hmH hlH hm1 hl1 hmv' hlv' hcop'
    hadj hlo hhi hjump

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
  have hRs' : ErdosProblems.Erdos243.runningMax u s < H := by
    simpa [runningMax_eq] using hRs
  have hrec' : ∀ n, s ≤ n →
      ErdosProblems.Erdos243.runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 4 := by
    intro n hn hrn
    exact hrec n hn (by simpa [runningMax_eq] using hrn)
  exact ErdosProblems.Erdos243.two_modulus_record_cut a u v w hc m l s H hm1 hl1
    hH hmH hlH hred hw hnum hmv hlv hRs' hrec' 

end Erdos249257.ExternalVerification243TwoModulusRecordCut
