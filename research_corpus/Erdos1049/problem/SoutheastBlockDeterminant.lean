import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Erdős #1049: the border-rank engine behind a cyclotomic Hankel factor

`BezoutPluckerJets` removes charge from Zudilin's cubic Hankel determinant by
linear algebra on the endpoint jets.  A different and larger source of charge is
purely combinatorial: when a matrix becomes *low border rank* modulo a prime or
cyclotomic factor `π` — that is, when its southeast `(N-d)×(N-d)` block vanishes
mod `π` — every Leibniz term is forced to pick up many divisible entries.

This module isolates that mechanism as a source-independent Mathlib-level
lemma, together with the row-and-column content factorisation that always
precedes it.

## The two lemmas

* `det_southeastBlock_dvd` — if `π ∣ M i j` whenever `d ≤ i` and `d ≤ j`, then
  `π ^ (N - 2d) ∣ det M`.  Proof: in each Leibniz term, at most `d` of the
  `N - d` rows with `d ≤ i` can be sent into the `d` columns with `j < d`, so at
  least `N - 2d` selected entries lie in the divisible block.

* `det_diagonal_mul_mul_diagonal` — extracting a common row *and* column factor
  `c` multiplies the determinant by `(∏ c)²`.

Together these are the exact shape of a cyclotomic Hankel charge extraction:
first pull the common row/column content out of `M i j = c i · c j · B i j`,
then read off the residual border-rank divisibility of `B` modulo each
`Φ_d`.

## Scope

The repository carries the 2016 source, and `ZudilinScalarContentLab.md`
applies the row-and-column content layer to `V_N(μ; p, 1, 1)`.  The subsequent
source calculation in `ZudilinResidualBorderChargeLab.md` now identifies the
primitive residual blocks: their entry exponents are `1` or `4`, so this
module's generic lemma forces `Phi_d^(N-2d)`.  That application is authored
source algebra rather than a polynomial formalisation inside this file.

The resulting first-order border charge, even combined with scalar content,
has a Lean-checked insufficient ceiling.  Higher residual valuations,
determinant cancellation, and their effective charge at `p = 3/2` remain open.

## Claim ceiling

**Erdős #1049 remains open.**  The universally forced first-order border
charge is insufficient; nothing here bounds any deeper effective charge.
-/

namespace ErdosProblems.Erdos1049

open Finset Matrix

/-- **Border-rank determinant divisibility.**  If every entry of the southeast
block `{(i,j) : d ≤ i, d ≤ j}` is divisible by `π`, then `π ^ (N - 2d)` divides
the determinant.

Each permutation must select at least `N - 2d` entries from that block: of the
`N - d` rows with `d ≤ i`, at most `d` can be mapped into the `d` columns with
`j < d`. -/
theorem det_southeastBlock_dvd {R : Type*} [CommRing R] {N d : ℕ}
    (π : R) (M : Matrix (Fin N) (Fin N) R)
    (hblock : ∀ i j : Fin N, d ≤ (i : ℕ) → d ≤ (j : ℕ) → π ∣ M i j) :
    π ^ (N - 2 * d) ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  refine Finset.dvd_sum fun σ _ => Dvd.dvd.mul_left ?_ _
  set S : Finset (Fin N) := univ.filter (fun i : Fin N => d ≤ (i : ℕ)) with hSdef
  set A : Finset (Fin N) := S.filter (fun i => d ≤ ((σ i : Fin N) : ℕ)) with hAdef
  -- `|T| ≤ d` where `T` is the set of small indices.
  have hTcard : (univ.filter (fun i : Fin N => ¬ (d ≤ (i : ℕ)))).card ≤ d := by
    have hle : (univ.filter (fun i : Fin N => ¬ (d ≤ (i : ℕ)))).card
        ≤ (Finset.range d).card := by
      refine Finset.card_le_card_of_injOn (fun i => (i : ℕ)) ?_ ?_
      · intro i hi
        obtain ⟨-, hi2⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_range.mpr (not_le.mp hi2)
      · intro a _ b _ hab
        exact Fin.ext hab
    simpa using hle
  -- `|S| ≥ N - d`.
  have hScard : N - d ≤ S.card := by
    have hsum : S.card + (univ.filter (fun i : Fin N => ¬ (d ≤ (i : ℕ)))).card
        = N := by
      rw [hSdef, Finset.card_filter_add_card_filter_not, card_univ,
        Fintype.card_fin]
    omega
  -- The rows of `S` sent into small columns number at most `d`.
  have hbadcard : (S.filter (fun i => ¬ (d ≤ ((σ i : Fin N) : ℕ)))).card ≤ d := by
    have hle : (S.filter (fun i => ¬ (d ≤ ((σ i : Fin N) : ℕ)))).card
        ≤ (Finset.range d).card := by
      refine Finset.card_le_card_of_injOn (fun i => ((σ i : Fin N) : ℕ)) ?_ ?_
      · intro i hi
        obtain ⟨-, hi2⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_range.mpr (not_le.mp hi2)
      · intro a _ b _ hab
        exact σ.injective (Fin.ext hab)
    simpa using hle
  -- Hence `|A| ≥ N - 2d`.
  have hsplitA : A.card + (S.filter (fun i => ¬ (d ≤ ((σ i : Fin N) : ℕ)))).card
      = S.card := by
    rw [hAdef, Finset.card_filter_add_card_filter_not]
  have hAcard : N - 2 * d ≤ A.card := by omega
  -- Every selected entry over `A` is divisible.
  have hdvdA : π ^ A.card ∣ ∏ i ∈ A, M (σ i) i := by
    have : ∏ _i ∈ A, π ∣ ∏ i ∈ A, M (σ i) i := by
      refine Finset.prod_dvd_prod_of_dvd _ _ fun i hi => ?_
      obtain ⟨hiS, hi2⟩ := Finset.mem_filter.mp hi
      obtain ⟨-, hi1⟩ := Finset.mem_filter.mp hiS
      exact hblock _ _ hi2 hi1
    simpa [Finset.prod_const] using this
  have hsub : ∏ i ∈ A, M (σ i) i ∣ ∏ i, M (σ i) i :=
    Finset.prod_dvd_prod_of_subset A univ _ (subset_univ A)
  exact dvd_trans (dvd_trans (pow_dvd_pow π hAcard) hdvdA) hsub

/-! ## Row-and-column content -/

theorem diagonal_mul_mul_diagonal_apply {R : Type*} [CommRing R] {N : ℕ}
    (c : Fin N → R) (B : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    (Matrix.diagonal c * B * Matrix.diagonal c) i j = c i * B i j * c j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **Row-and-column content.**  Extracting a common factor from every row and
every column multiplies the determinant by the square of its product. -/
theorem det_diagonal_mul_mul_diagonal {R : Type*} [CommRing R] {N : ℕ}
    (c : Fin N → R) (B : Matrix (Fin N) (Fin N) R) :
    (Matrix.diagonal c * B * Matrix.diagonal c).det = (∏ i, c i) ^ 2 * B.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

end ErdosProblems.Erdos1049
