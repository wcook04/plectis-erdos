import ErdosProblems.Erdos243.PrimitiveRecordBarrier

/-!
# Erdős 243: exact prime-power persistence interval

This file assembles the literal interval conclusion of
`long243:res:powerpersistence` from the checked one-step valuation-loss
threshold `primitive_valuation_no_drop`.

The functions are the reduced reciprocal-tail data from the paper:
`w n + v n = a n * u n`, `w n = hc n * u (n + 1)`, and
`a n * v n = hc n * v (n + 1)`.  No bound on the cancellation factors is
assumed.  The only interval hypothesis is the displayed paper bound
`w n < p ^ (k + 1)` for `s ≤ n < t`.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR20

/-- **Persistence of a prime power (`long243:res:powerpersistence`).**
If `p ^ k` divides the reduced denominator at time `s`, and every raw next
numerator on `[s,t)` is below `p ^ (k+1)`, then `p ^ k` still divides the
reduced denominator at time `t`.

This is an interval induction using `primitive_valuation_no_drop`; its
hypotheses spell out exactly the standing primitive reduced-tail recurrence
used by the paper. -/
theorem primePower_persists
    (a u v w hc : ℕ → ℕ) {p k s t : ℕ}
    (hp : p.Prime)
    (hst : s ≤ t)
    (hcop : ∀ n, Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, 0 < v n)
    (hq : ∀ n, w n + v n = a n * u n)
    (hwpos : ∀ n, 0 < w n)
    (hnum : ∀ n, w n = hc n * u (n + 1))
    (hden : ∀ n, a n * v n = hc n * v (n + 1))
    (hstart : p ^ k ∣ v s)
    (hsmall : ∀ n, s ≤ n → n < t → w n < p ^ (k + 1)) :
    p ^ k ∣ v t := by
  induction t, hst using Nat.le_induction with
  | base => exact hstart
  | succ n hsn ih =>
      have ih' : p ^ k ∣ v n :=
        ih (fun m hsm hmn => hsmall m hsm (hmn.trans (Nat.lt_succ_self n)))
      exact primitive_valuation_no_drop hp (hcop n) (hvpos n) (hq n) (hwpos n)
        (hnum n) (hden n) ih' (hsmall n hsn (Nat.lt_succ_self n))

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.primePower_persists

end ErdosProblems.Erdos243.PaperCompleteR20
