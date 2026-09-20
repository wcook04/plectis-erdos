import ErdosProblems.Erdos243.ReciprocalTailRigidity

/-!
# Erdős 243: descent, and the constant and periodic negative magnitudes

Paper-form restatements of three environments of the long note
`paper/reasoning-parts/erdos243/core.tex`:

* `long243:res:descent` (descent), stated exactly by the existing
  `centeredState_eventually_zero`;
* `long243:res:constant` (no constant negative magnitude), both its clause
  at every index and its clause "the same holds if the shape equation only
  begins at some index";
* `long243:res:periodic` (no periodic negative magnitude).

The two exclusion theorems are phrased in the paper as the non-existence of a
pair (respectively a quadruple) of sequences.  The tree states them as the
falsity of the hypotheses.  The restatements below are the packaged
`¬ ∃` forms, so that the Lean statement is literally the paper's.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

/-! ## Descent (`long243:res:descent`)

"Let `C, E : ℕ → ℕ` satisfy `Cₙ₊₁ + Eₙ = Cₙ` for every `n`.  Then `Eₙ = 0`
for all sufficiently large `n`."  This is the existing tree declaration
verbatim; the axiom print below is its home in this release. -/

#print axioms ErdosProblems.Erdos243.centeredState_eventually_zero

/-! ## No constant negative magnitude (`long243:res:constant`) -/

/-- **No constant negative magnitude (`long243:res:constant`), first clause.**
For any `m, c : ℕ` with `m > 0`, there is no pair of sequences
`a, D : ℕ → ℕ` with `aₙ ≥ 2` for all `n` satisfying `Dₙ₊₁ = aₙ Dₙ` and the
shape equation `Dₙ + m = (aₙ - 1)(c + n m)` of `(5.1)`. -/
theorem no_constantNegative_shapeEquation
    (m c : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D n + m = (a n - 1) * (c + n * m)) := by
  rintro ⟨a, D, ha, hD, hshape⟩
  exact no_constantNegative_orbit a D m c hm ha hD hshape

/-- **No constant negative magnitude (`long243:res:constant`), second clause:
"the same holds if the shape equation only begins at some index".**
Here the shape equation is read from index `N` on, with the numerator
restarted at `c = C N`, so that at index `N + n` it reads
`D (N + n) + m = (a (N + n) - 1) (c + n m)`. -/
theorem no_eventuallyConstantNegative_shapeEquation
    (m c N : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D (N + n) + m = (a (N + n) - 1) * (c + n * m)) := by
  rintro ⟨a, D, ha, hD, hshape⟩
  exact no_eventuallyConstantNegative_orbit a D m c N hm ha hD hshape

/-! ## No periodic negative magnitude (`long243:res:periodic`) -/

/-- **No periodic negative magnitude (`long243:res:periodic`).**
There are no `a, D, C, e : ℕ → ℕ` with `aₙ ≥ 2`, `eₙ > 0` and `eₙ < aₙ` for
every `n`, satisfying `Dₙ₊₁ = aₙ Dₙ`, `Cₙ₊₁ = Cₙ + eₙ` and
`Dₙ + eₙ = (aₙ - 1) Cₙ`, with `eₙ₊ₕ = eₙ` and `Cₙ₊ₕ = Cₙ + M` for some
`h > 0` and `M > 0`. -/
theorem no_periodicNegative_shapeEquation
    (h M : ℕ) (hh : 0 < h) (hM : 0 < M) :
    ¬ ∃ a D C e : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, 0 < e n) ∧
      (∀ n, e n < a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, C (n + 1) = C n + e n) ∧
      (∀ n, D n + e n = (a n - 1) * C n) ∧
      (∀ n, e (n + h) = e n) ∧
      (∀ n, C (n + h) = C n + M) := by
  rintro ⟨a, D, C, e, ha, hepos, helt, hD, hC, hshape, hperiod, hphase⟩
  exact no_periodicNegative_orbit a D C e h M hh hM ha hepos helt hD hC
    hshape hperiod hphase

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.no_constantNegative_shapeEquation
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.no_eventuallyConstantNegative_shapeEquation
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.no_periodicNegative_shapeEquation

end ErdosProblems.Erdos243.PaperCompleteR21
