import Erdos249257.CertificateKernel

/-!
# The complement identity for the support coefficient

`CertificateSocketCollapse.md` section 66 rests on one pointwise fact: a divisor of `n`
lies in `A` exactly when it does not lie in the complement, so the two support
coefficients partition the divisor count.

    supportCoeff A n + supportCoeff Aᶜ n = τ(n).

Everything section 66 builds on top of this -- `Odd_A = Sq XOR Odd_E`, and the socket
criterion "kills iff `Odd_E` is syndetic" -- is downstream of this identity plus the
`F₂`-linearity of reduction mod 2.

**Standing caveat, from cross-index T51.** This identity lives inside the DIVISOR LAYER,
which `SupportWordStructureLab.md` section 5d proves cannot obstruct Erdős 257 on its own.
This file is certified infrastructure, not progress toward the problem.
-/

namespace Erdos249257

open Finset

/-- **Complement identity.** The support coefficients of `A` and of its complement
partition the divisor count of `n`: every divisor of `n` is counted exactly once. -/
theorem supportCoeff_add_supportCoeff_compl (A : Set ℕ) (n : ℕ) :
    supportCoeff A n + supportCoeff Aᶜ n = n.divisors.card := by
  classical
  simp only [supportCoeff, Set.mem_compl_iff]
  exact Finset.card_filter_add_card_filter_not _

/-- **The socket XOR, pointwise.** `A` and its complement have opposite support-coefficient
parity at `n` exactly when `n` has an odd number of divisors.  This is the `F₂`-linearity
step of `CertificateSocketCollapse.md` section 66 -- the relation section 66 writes as
`Odd_A = Sq △ Odd_E` -- with `Odd (n.divisors.card)` standing in for `Sq`.

The identification `Odd (d n) ↔ IsSquare n` is a separate, purely classical fact which is
absent from Mathlib and from this corpus; it is NOT needed for the linearity itself, which
is what this lemma isolates. -/
theorem supportCoeff_odd_xor (A : Set ℕ) (n : ℕ) :
    ((Odd (supportCoeff A n) ↔ ¬ Odd (supportCoeff Aᶜ n)) ↔ Odd n.divisors.card) := by
  have h := supportCoeff_add_supportCoeff_compl A n
  simp only [Nat.odd_iff]
  omega

#print axioms Erdos249257.supportCoeff_add_supportCoeff_compl
#print axioms Erdos249257.supportCoeff_odd_xor

end Erdos249257
