import ErdosProblems.Erdos1049.PaperR20.CoefficientPencilAssembly
import ErdosProblems.Erdos1049.PaperR20.SourcePadeAnalyticRemainder
import ErdosProblems.Erdos1049.PaperR20.HankelKroneckerCertificate

/-!
# The finite coefficient pencil at ranks up to eight

Paper statement (`long1049:res:finite-pencil`, `paper/reasoning-parts/erdos1049/core.tex`):

> For every real `p > 1` and `1 ≤ N ≤ 8`, `A_N` is positive definite and all roots
> of `det(Y A_N − B_N)` are real and strictly less than `F(p)`. The roots at
> consecutive ranks `N, N+1 ≤ 8` interlace non-strictly.

Here `A_N = (α_{i+j})` is `coefficientAlphaMatrix p N`, `B_N = (β_{i+j})` is
`coefficientBetaMatrix p N`, the determinant polynomial `det(Y A_N − B_N)` is
`coefficientPencilPoly p N`, and `F(p) = PaperR16.lambert (1 / p)`.

Three inputs are combined.

* Positivity of the leading Hankel determinants `D_{k,0}(p)` for `k ≤ 8` and
  `p ≥ 1`, from their positive coefficients in `t = p − 1`.
* The remainder identity `v*_m = α_m F(p) − β_m` at every moment index `m`.
  Together with positive definiteness of the remainder moment matrices at every
  rank, it gives `F(p) A_N − B_N > 0`.
* Sylvester's criterion, the square-root congruence for symmetric definite
  pencils, and inertia interlacing for leading principal pencils.

"All roots are real" is stated as `Splits`: the real polynomial factors into
linear factors over `ℝ`. Interlacing is stated for the ordered root lists,
with algebraic multiplicities recorded by the root multisets.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Matrix Polynomial

/-- The paper's proposition `long1049:res:finite-pencil`, for every real `p > 1`.

1. For every `N ≤ 8`: `A_N` is positive definite, `det(Y A_N − B_N)` splits
   over `ℝ`, and each of its roots is strictly less than `F(p)`.
2. For every `N` with `N + 1 ≤ 8`: the roots at ranks `N + 1` and `N`, listed in
   decreasing order with multiplicity, interlace non-strictly. -/
theorem coefficientPencil_finitePencil {p : ℝ} (hp : 1 < p) :
    (∀ N : ℕ, N ≤ 8 →
      (coefficientAlphaMatrix p N).PosDef ∧
        (coefficientPencilPoly p N).Splits ∧
        ∀ x : ℝ, (coefficientPencilPoly p N).IsRoot x → x < PaperR16.lambert (1 / p)) ∧
    (∀ N : ℕ, N + 1 ≤ 8 →
      ∃ (large : Fin (N + 1) → ℝ) (small : Fin N → ℝ),
        Antitone large ∧ Antitone small ∧
        (coefficientPencilPoly p (N + 1)).roots = Multiset.map large Finset.univ.val ∧
        (coefficientPencilPoly p N).roots = Multiset.map small Finset.univ.val ∧
        ∀ i : Fin N, small i ≤ large i.castSucc ∧ large i.succ ≤ small i) := by
  have hdet : ∀ k : ℕ, k ≤ 8 → 0 < k →
      0 < (coefficientHankelDetPoly k 0).eval₂ (Int.castRingHom ℝ) p :=
    fun k hk _ => coefficientHankelDetPoly_shift0_pos hp.le k hk
  refine ⟨fun N hN => ?_, fun N hN => ?_⟩
  · rw [one_div]
    exact coefficientPencil_splits_and_roots_lt_of_certificates hp N
      (fun k hk hk0 => hdet k (hk.trans hN) hk0)
      (fun i j => sourcePade_actualMoment_eq_coefficientLinearForm (i.val + j.val) p hp)
  · exact coefficientPencil_interlaces_of_certificates hp N
      (fun k hk hk0 => hdet k (hk.trans hN) hk0)

end ErdosProblems.Erdos1049.PaperR20
