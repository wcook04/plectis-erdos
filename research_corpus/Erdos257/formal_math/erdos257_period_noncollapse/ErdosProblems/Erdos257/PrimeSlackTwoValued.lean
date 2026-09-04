import Mathlib.Tactic

/-!
# The prime slack is two-valued, with a closed form

`CertificateSocketCollapse.md` section 84 derives the sharpest local constraint in the
carry system and confirms it on 20,358 primes, but section 87.1 records the Lean file as
written and **unproven**: the project build lease was held by a foreign owner and returned
`rc = 75` (`validation_capacity_deferred`, ticket `rct_51cbac976b5c5ef58f60`), so the file
was removed rather than left unbuilt. This module supplies the missing proof.

## The setting

Writing `τ_A(m) = ε_m + 2 C_{m-1} - C_m` for the carry identity of
`RunLengthMarginLawAndDivisorMultiplicity.md` sections 3 and 11, at a **prime** `p` the
only divisor of `p` that can lie in `A` is `p` itself, since `1` is never selected
(`w₁ = 1` exceeds every target below `1`). Hence `τ_A(p) = 1_A(p) ∈ {0,1}`, and the carry
identity rearranges into the natural-subtraction-free form

`t + cp = e + 2 * cm`,   `t = τ_A(p) ≤ 1`,  `e = ε_p ≤ 1`,  `cp = C_p`,  `cm = C_{p-1}`.

The prime slack is `s(p) = (C_p + 1) / 2 - C_{p-1}`. Everything below is a statement about
that hypothesis alone: pure linear arithmetic over `ℕ` with division by the literal `2`,
which is exactly the fragment `omega` decides. No divisor theory enters, which is why
section 84's result states abstractly.

## What is proved, and what it is not

The four theorems give the halving bound, two-valuedness, and a closed characterisation of
each value. Section 84's own claim boundary stands verbatim: `s(p)` is a function of
`1_A(p)` and `ε_p` alone, both already known at `p`, so it carries no information about
survival that the support word does not already carry. **This is a theorem about the carry
system, not progress on Erdős 257.**
-/

namespace ErdosProblems.Erdos257

namespace PrimeSlackTwoValued

/-- The halving bound at a prime: the carry is at most (half) its running bound
immediately before every prime. This is the inequality `2 C_{p-1} ≤ C_p + 1` of
`CertificateSocketCollapse.md` section 84 and of section 12 of
`RunLengthMarginLawAndDivisorMultiplicity.md`. -/
theorem primeSlack_halving {t e cp cm : ℕ} (ht : t ≤ 1) (he : e ≤ 1)
    (hcar : t + cp = e + 2 * cm) : 2 * cm ≤ cp + 1 := by
  omega

/-- The slack `s(p) = (C_p + 1) / 2 - C_{p-1}` takes only the values `0` and `1`. -/
theorem primeSlack_two_valued {t e cp cm : ℕ} (ht : t ≤ 1) (he : e ≤ 1)
    (hcar : t + cp = e + 2 * cm) :
    (cp + 1) / 2 = cm ∨ (cp + 1) / 2 = cm + 1 := by
  omega

/-- Closed form for the slack-one case: `s(p) = 1` exactly when `p` is **not** selected and
the digit `ε_p` is `1`. -/
theorem primeSlack_eq_one_iff {t e cp cm : ℕ} (ht : t ≤ 1) (he : e ≤ 1)
    (hcar : t + cp = e + 2 * cm) :
    (cp + 1) / 2 = cm + 1 ↔ (t = 0 ∧ e = 1) := by
  omega

/-- Closed form for the vanishing set: `s(p) = 0` exactly when `p` is selected or the digit
`ε_p` is `0`. Together with `primeSlack_eq_one_iff` this makes the vanishing set
`{p ∈ A} ∪ {p : ε_p = 0}`, explicit and structureless. -/
theorem primeSlack_eq_zero_iff {t e cp cm : ℕ} (ht : t ≤ 1) (he : e ≤ 1)
    (hcar : t + cp = e + 2 * cm) :
    (cp + 1) / 2 = cm ↔ (t = 1 ∨ e = 0) := by
  omega

/-- The parity corollary the closed form rests on: `C_p ≡ 1_A(p) + ε_p (mod 2)`.  This one
needs no bounds on `t` or `e` at all — it is forced by the carry identity alone, since the
`2 * cm` term is even. -/
theorem carry_parity_at_prime {t e cp cm : ℕ}
    (hcar : t + cp = e + 2 * cm) : cp % 2 = (t + e) % 2 := by
  omega

#print axioms primeSlack_halving
#print axioms primeSlack_two_valued
#print axioms primeSlack_eq_one_iff
#print axioms primeSlack_eq_zero_iff
#print axioms carry_parity_at_prime

end PrimeSlackTwoValued

end ErdosProblems.Erdos257
