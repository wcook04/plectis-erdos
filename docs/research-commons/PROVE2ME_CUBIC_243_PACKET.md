<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Cubic-rate Erdős #243 theorem on Prove2Me

The [zero-indexed cubic-rate theorem](https://prove2.me/theorems/51fbd303-588d-4586-9bbc-f5813513b52c)
is public and **Proved** on Prove2Me in Lean 4.30.0 with Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. It assumes a strictly
increasing sequence `a : ℕ → ℕ` of positive integers, the limit
`n³ (aₙ²/aₙ₊₁ − (1 + 3/n)) → 0`, and `HasSum (fun n => 1 / aₙ) S`.
It concludes `Irrational S`. The [public claim record](../claims.json)
identifies this as a theorem for the stated cubic-rate subclass. The
unrestricted Erdős #243 eventual-recurrence problem remains open.

**Reading the proof.** Prove2Me shows a challenge statement ending in
`by sorry` even though this theorem is Proved. The accepted Solution is a
separate object under **View graph → Solutions & Sketches**; the graph asks
signed-out readers to sign in. The exact accepted Solution is copied below
so that a signed-out reader can inspect it. Its final line applies
`cubic_rate_irrationality` to the proved `squareSpecialisation`; the
substantial cubic-rate and field arguments live in the imported public
theorems. This page copies the accepted native Lean 4.30 proof, while the
[original Lean source](https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L67-L77)
is pinned separately.

The [paper's cubic-rate theorem and index bridge](https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L734-L752)
state a one-based version. That bridge changes a finite prefix while
preserving the eventual indices; shifting the whole sequence by one would
change the displayed rate. The paper is by Will Cook and separately
[discloses AI-assisted research and drafting](https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188).
It distinguishes the [original problem and Koizumi's earlier work](https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110).

Here is the accepted Solution as stored by Prove2Me on 25 September 2026.
The Lean block has SHA-256
`9e6cd254f87a248db5a4d429f042d81b8a3672f9d8934c12f5256e6f72549030`.

```lean
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticCertificates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR21_CubicRateExclusionChain
import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR21_SquareSpecialisationDedekind
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_cubic_rate_irrationality
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_squareSpecialisation_holds
import Mathlib
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Erdős 243: the square-specialisation lemma and its consumers, unconditionally

`SquareSpecialisationDedekind.lean` proves the statement of `long243:res:squarespec`
(`paper/reasoning-parts/erdos243/core.tex`, lemma at line 303) from the simple pole of the
Dedekind zeta function, which is in Mathlib; the Chebotarev density theorem is not used.  This
file records it as `squareSpecialisation : SquareSpecialisation` and discharges the hypothesis
`hss : SquareSpecialisation` of the three downstream paper statements in
`CubicRateExclusionChain.lean`:

* `transport_square_unconditional` — `long243:res:transportsquare`;
* `cubic_exclusion_unconditional` — `long243:res:cubicexclusion`;
* `cubic_rate_irrationality_unconditional` — `res:cubicrate` and `long243:res:cubicrate`.

Each is the corresponding `CubicRateExclusionChain` theorem applied to `squareSpecialisation`,
with no hypothesis added.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21
open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20

/-- **`long243:res:squarespec`**, with no hypothesis: if `f ∈ ℚ[T]` is irreducible with root
`α`, `H (α) ≠ 0`, and for all but finitely many primes `ℓ` every root `r` of `f` modulo `ℓ` has
`H (r)` a nonzero square modulo `ℓ`, then `H (α)` is a square in `ℚ(α)`. -/
theorem squareSpecialisation : SquareSpecialisation :=
  squareSpecialisation_holds
end ErdosProblems.Erdos243.PaperCompleteR21

open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR21 in
theorem solution
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv :=
  cubic_rate_irrationality squareSpecialisation a ha hpos hrate Sv hS
```

A [public every-tail consequence](https://prove2.me/theorems/d45dcaf7-5de2-4435-b9ec-5315778b172c)
imports this proved theorem in the same environment and derives
irrationality after removing any finite rational prefix. Its proof idea
was prepared from the source before hosted submission, so it is
source-assisted native reuse rather than a blind outside first-use trial.

The Prove2Me Proved status and accepted proof are technical verification
of the displayed formal statement. This copy does not independently
replay the platform environment, establish mathematical peer review, or
settle the unrestricted Erdős #243 problem. A fresh reader can use the
[Prove2Me proof guide](https://prove2.me/references/prove.md) and the
public theorem page to test what the entry point actually lets them do.
