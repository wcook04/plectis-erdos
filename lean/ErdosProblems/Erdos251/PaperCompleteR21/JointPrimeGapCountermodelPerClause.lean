-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.ArgumentGraph.Derived.Erdos251

/-!
# Erdős #251: the simultaneous countermodel, each input at its clause

`short_joint_prime_gap_countermodel` (`res:jointcountermodel`) and
`long_joint_prime_gap_countermodel` (`long251:res:jointcountermodel`) assume
Schlage-Puchta's Lemma 4 and the prime number theorem and restrict the allowance
exponent to `0 < ε ≤ 1`. Their proofs use Schlage-Puchta's Lemma 4 only to prove
fixed-block nonconcentration, the prime number theorem only to prove `P n ∼ n log n`,
and never use `ε ≤ 1`: the construction runs at the exponent `min ε (1/2)`. So the
sequence exists unconditionally for every `ε > 0`, with all its other properties,
and each input is needed only for its own clause. The two theorems below state
this. Their proofs are `derive_factor`'s factorings of the two countermodels
(`ErdosProblems.ArgumentGraph.Derived.Erdos251`), which follow the construction
through `prime_polylogarithmic_interval` and derive its factoring on the way; the
kernel checks each of them.
-/

noncomputable section
open Filter Topology Finset

namespace ErdosProblems.Erdos251.PaperCompleteR21

open ErdosProblems.Erdos251.PaperR8.SparseSchedule
open ErdosProblems.Erdos251.PaperR11.SparsePolylog
open ErdosProblems.Erdos251.PaperR11.GrowingBlocks
open ErdosProblems.Erdos251.PaperR11.Nonconcentration
open ErdosProblems.Erdos251.PaperR11.PerturbationGrowth
open ErdosProblems.Erdos251.PaperR11.PrimeSource

/-- **Long paper, `long251:res:jointcountermodel`, each input at its clause.** For every
prefix length `K` and every `ε > 0` there is a correction `e` with every property of
`long_joint_prime_gap_countermodel`; Schlage-Puchta's Lemma 4 is assumed only by the
fixed-block nonconcentration clause and the prime number theorem only by the growth
clause `P n ∼ n log n`. -/
theorem long_joint_prime_gap_countermodel_per_clause (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ → ℕ, ∃ r : ℚ, ∃ C : ℝ, 0 < C ∧
      (∀ n, n < K → e n = 0) ∧
      HasSum (fun n => ((primeGap0 n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        primeGap0 n + e n ≡ primeGap0 n [MOD q] ∧
        cumulative (fun i => primeGap0 i + e i) n ≡ prime0 n [MOD q]) ∧
      (SchlagePuchtaLemma4 →
        FixedBlockNonconcentration (fun n => ((primeGap0 n + e n : ℕ) : ℤ))) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        Tendsto (fun X =>
          blockTV primeGap0 (fun n => primeGap0 n + e n) X (m X)) atTop (𝓝 0)) ∧
      (∀ n, prime0 n ≤ cumulative (fun i => primeGap0 i + e i) n) ∧
      (∀ᶠ n : ℕ in atTop,
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) - prime0 n
          ≤ C * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ)))) ∧
      (PrimeNumberTheorem → Tendsto (fun n =>
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) / scale n) atTop (𝓝 1)) :=
  long_joint_prime_gap_countermodel.factored K hε

/-- **Short paper, `res:jointcountermodel`, each input at its clause.** For every prefix
length `K` and every `ε > 0` there is `b` with a rational dyadic sum, `b n = g n` below
`K`, `g n ≤ b n ≤ g n + (log (n+3))^ε` eventually, every fixed eventual residue of the
coefficients and cumulative positions, vanishing block total variation for lengths
`o(log log X)`, and `0 ≤ P n - p n = O_ε(n (log (n+3))^ε / log log n)`; fixed-block
polynomial nonconcentration holds under Schlage-Puchta's Lemma 4, and `P n ∼ n log n`
under the prime number theorem. -/
theorem short_joint_prime_gap_countermodel_per_clause (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℕ → ℕ, ∃ r : ℚ, ∃ C : ℝ, 0 < C ∧
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ n, n < K → b n = primeGap0 n) ∧
      (∀ n, primeGap0 n ≤ b n) ∧
      (∀ᶠ n : ℕ in atTop, ((b n - primeGap0 n : ℕ) : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        b n ≡ primeGap0 n [MOD q] ∧ cumulative b n ≡ prime0 n [MOD q]) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        Tendsto (fun X => blockTV primeGap0 b X (m X)) atTop (𝓝 0)) ∧
      (SchlagePuchtaLemma4 → FixedBlockNonconcentration (fun n => (b n : ℤ))) ∧
      (∀ n, prime0 n ≤ cumulative b n) ∧
      (∀ᶠ n : ℕ in atTop, (cumulative b n : ℝ) - prime0 n
        ≤ C * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ)))) ∧
      (PrimeNumberTheorem → Tendsto (fun n => (cumulative b n : ℝ) / scale n) atTop (𝓝 1)) :=
  short_joint_prime_gap_countermodel.factored K hε

end ErdosProblems.Erdos251.PaperCompleteR21

#print axioms ErdosProblems.Erdos251.PaperCompleteR21.long_joint_prime_gap_countermodel_per_clause
#print axioms ErdosProblems.Erdos251.PaperCompleteR21.short_joint_prime_gap_countermodel_per_clause
