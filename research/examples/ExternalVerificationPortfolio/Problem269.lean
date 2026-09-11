/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257
import ExternalVerification.Solution

/-!
# Erdős #269: two reusable Comparator routes

This small downstream module exposes the two distinct #269 mechanisms that
are currently strong enough to be useful outside their proof files.  The
first separates a finite residue digit from an integral quotient coboundary;
the second consumes a cofinal local-window escape hypothesis to rule out a
positive short-bounded carry.  Neither example supplies the missing bridge
from the actual running-LCM series, and neither is an endpoint or novelty
claim for Erdős #269.
-/

namespace ExternalVerificationPortfolio.Problem269

/-! ## Weighted phase: finite residue, uncontrolled transfer -/

/- The exact Comparator representative and its source-side finite-coordinate
   support are intentionally visible to a reader inspecting this module. -/
#check Erdos249257.ExternalVerification.carry_eq_residueDigit_add_coboundary
#check ErdosProblems.Erdos269.carryResidue_mem_interval
#check ErdosProblems.Erdos269.residueDigit_mem_interval
#check ErdosProblems.Erdos269.finite_realisedSpan_of_factorisation

/-
The recurrence is split into a canonical finite residue digit and an
integral quotient coboundary.  The finite residue and digit intervals are
source-level support, while finite realised span follows only when the
symbolic realisation factors through an explicitly finite-dimensional,
function-faithful observer.  A scalar evaluation does not establish that
factorisation; no finite-state quotient recurrence, actual three-prime
running-LCM bridge, or #269 rationality/irrationality conclusion follows.
-/
example
    (B : ℤ) (hB : 0 < B)
    (base carry digit : ℕ → ℤ)
    (hrec : ∀ n,
      carry (n + 1) = base n * carry n - B * digit n) :
    let residue := fun n =>
      Erdos249257.ExternalVerification.weightedCarryResidue B (carry n)
    let quotient := fun n =>
      Erdos249257.ExternalVerification.weightedCarryQuotient B (carry n)
    ∀ n,
      digit n =
        Erdos249257.ExternalVerification.weightedResidueDigit B (base n)
          (residue n) (residue (n + 1)) +
          base n * quotient n - quotient (n + 1) :=
  Erdos249257.ExternalVerification.carry_eq_residueDigit_add_coboundary
    B hB base carry digit hrec

/-! ## Conditional carry escape: the local-window consumer -/

#check Erdos249257.ExternalVerification.no_positive_reducedCarry_of_cofinalLocalWindowEscape
#check ErdosProblems.Erdos269.CofinalLocalWindowEscape

/-
The second representative consumes the exact cofinal local-window escape
predicate.  Given positivity, coprimality, the multiplier recurrence, and
the denominator-dependent short bound, it derives `False`.  The cofinal
escape producer itself is open, as is any actual-series/rationality bridge
that would instantiate this carry.  Thus the example records a reusable
conditional obstruction, not an unconditional #269 endpoint or novelty
claim.
-/
example
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape :
      Erdos249257.ExternalVerification.CofinalLocalWindowEscape
        b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (d : ℕ → ℤ)
    (hrec : ∀ n,
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) :
    False :=
  Erdos249257.ExternalVerification.no_positive_reducedCarry_of_cofinalLocalWindowEscape
    b m shortBound hescape B hBpos hBcoprime d hrec hpos hbound

end ExternalVerificationPortfolio.Problem269
