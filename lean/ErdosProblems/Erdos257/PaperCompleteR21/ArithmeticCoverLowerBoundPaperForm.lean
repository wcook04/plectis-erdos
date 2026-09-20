import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCoverLowerBound
import ErdosProblems.Erdos257.PaperCompleteR21.FiniteFamilyCoverCost

/-!
# Display `eq:257-arithmetic-cover-lower` for the paper's own `K_*(F)`

Clause 1 of the long Erdős #257 `cor` "finite-functional separation"
(`paper/reasoning-parts/erdos257/a257_front.tex:9369`), in the paper's exact
form:

  `K_*(F) ≥ max_{ℓ ∣ Q} ℙ(U_F(N) > 1 ∣ ℓ ∣ N)`,  `N` uniform modulo `Q = lcm F`.

`ArithmeticCoverLowerBound.lean` proves this with `K_*` read as the tree's
`optimizedLogCoverCost`, an infimum over `ℕ`-indexed `LogBudgetCover`s only.
The paper's `K_*(F)` is the infimum over finite **or** countable families, which
is a priori smaller, so that statement was weaker than the display.
`FiniteFamilyCoverCost.lean` shows the two infima are the same number
(`paperCoverCost_eq_optimizedLogCoverCost`).  This module is the one-line
composition, so that a single declaration now states the display with `K_*`
meaning what the paper says it means.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset
open ErdosProblems.Erdos257.PaperCompleteR8

/-- Every finite support admits an admissible countable cover, so the infimum
defining `K_*(F)` is over a nonempty set. -/
theorem admissibleLogCoverCosts_nonempty (F : Finset ℕ) (hF : 0 ∉ F) :
    (admissibleLogCoverCosts (F : Set ℕ)).Nonempty :=
  ⟨(singleFrameCover F hF).cost, ⟨singleFrameCover F hF, rfl⟩⟩

/-- Display `eq:257-arithmetic-cover-lower` (line 9371) with `K_*(F)` the
paper's infimum over finite or countable admissible fractional covers:

  `K_*(F) ≥ max_{ℓ ∣ Q} ℙ(U_F(N) > 1 ∣ ℓ ∣ N)`. -/
theorem sup_condExceedProb_le_paperCoverCost (F : Finset ℕ) (hF : 0 ∉ F)
    (hne : (F.lcm id).divisors.Nonempty) :
    (F.lcm id).divisors.sup' hne (fun ℓ => condExceedProb F ℓ)
      ≤ paperCoverCost (F : Set ℕ) := by
  rw [paperCoverCost_eq_optimizedLogCoverCost _ (admissibleLogCoverCosts_nonempty F hF)]
  exact sup_condExceedProb_le_optimizedLogCoverCost F hF hne

/-- The same, at a single divisor `ℓ ∣ Q`. -/
theorem condExceedProb_le_paperCoverCost (F : Finset ℕ) (hF : 0 ∉ F)
    (ℓ : ℕ) (hℓ0 : 0 < ℓ) (hℓ : ℓ ∣ F.lcm id) :
    condExceedProb F ℓ ≤ paperCoverCost (F : Set ℕ) := by
  rw [paperCoverCost_eq_optimizedLogCoverCost _ (admissibleLogCoverCosts_nonempty F hF)]
  exact condExceedProb_le_optimizedLogCoverCost F hF ℓ hℓ0 hℓ

#print axioms admissibleLogCoverCosts_nonempty
#print axioms sup_condExceedProb_le_paperCoverCost
#print axioms condExceedProb_le_paperCoverCost

end ErdosProblems.Erdos257.PaperCompleteR21

end
