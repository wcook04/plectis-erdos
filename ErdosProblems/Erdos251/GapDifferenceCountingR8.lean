import ErdosProblems.Erdos251.PaperNonconcentrationR7
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Correct counting input for gap differences

UNCOMPILED R8 source. The analytic target is a count of THREE-prime
configurations, not the number of occurrences of one fixed prime gap.
No analytic target below is asserted as a theorem or introduced as an axiom.
The full polynomial nonconcentration conclusion requires more than the
adjacent-difference special case formalised here.

Pinned APIs: Mathlib/Data/Finset/Card.lean (card_le_card_of_injOn,
card_le_card, card_union_le); Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
(sum_le_sum, sum_filter); the prime enumeration facts are the same APIs
used by the live PrimeGapDyadicTail.lean. See evidence/checks/pinned_api_sources.json.
-/

open scoped BigOperators
open Finset
namespace ErdosProblems.Erdos251.PaperR8.GapCounting
noncomputable section

open PaperR7

/-- Integers d and prime starting points x for x,x+d,x+2d+r prime.
The explicit nonnegativity condition avoids changing signed shifts by toNat. -/
def tripleCandidates (N H : ℕ) (r : ℤ) : Finset (ℕ × ℕ) := by
  classical
  exact ((range (prime0 N)).product (range (H + 1))).filter fun z =>
    Nat.Prime z.1 ∧ Nat.Prime (z.1 + z.2) ∧
    0 ≤ (z.1 : ℤ) + 2 * z.2 + r ∧
    Nat.Prime (((z.1 : ℤ) + 2 * z.2 + r).toNat)

def adjacentMatches (N : ℕ) (r : ℤ) : Finset ℕ := by
  classical
  exact (range N).filter fun n =>
    (primeGap0 (n + 1) : ℤ) - primeGap0 n = r

def largeGaps (N H : ℕ) : Finset ℕ := by
  classical
  exact (range N).filter fun n => H < primeGap0 n

/-- Exact three-prime identity; no density or sieve hypothesis. -/
theorem adjacent_difference_iff (n : ℕ) (r : ℤ) :
    (primeGap0 (n + 1) : ℤ) - primeGap0 n = r ↔
      (prime0 (n + 2) : ℤ) + prime0 n = 2 * prime0 (n + 1) + r := by
  have h0 := prime0_mono_step n
  have h1 := prime0_mono_step (n + 1)
  have e0 : prime0 n + primeGap0 n = prime0 (n + 1) := by
    unfold primeGap0
    omega
  have e1 : prime0 (n + 1) + primeGap0 (n + 1) = prime0 (n + 2) := by
    unfold primeGap0
    simp only [Nat.add_assoc, Nat.reduceAdd] at h1 ⊢
    omega
  have z0 : (prime0 n : ℤ) + primeGap0 n = prime0 (n + 1) := by
    exact_mod_cast e0
  have z1 : (prime0 (n + 1) : ℤ) + primeGap0 (n + 1) = prime0 (n + 2) := by
    exact_mod_cast e1
  constructor <;> intro h <;> omega

/-- The first gap alone needs truncating. All other prime triples are allowed
in the upper bound, so no assumption of consecutive primes is hidden there. -/
theorem short_matches_le_triples (N H : ℕ) (r : ℤ) :
    ((adjacentMatches N r).filter fun n => primeGap0 n ≤ H).card ≤
      (tripleCandidates N H r).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun n => (prime0 n, primeGap0 n))
  · intro n hn
    obtain ⟨hnMatch, hgap⟩ := mem_filter.mp hn
    obtain ⟨hnN, hdelta⟩ := mem_filter.mp hnMatch
    have hnlt : n < N := mem_range.mp hnN
    have hp : Nat.Prime (prime0 n) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    have hp1 : Nat.Prime (prime0 (n + 1)) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + 1)
    have hp2 : Nat.Prime (prime0 (n + 2)) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + 2)
    have hless : prime0 n < prime0 N :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime) hnlt
    have hmono := prime0_mono_step n
    have ep : prime0 n + primeGap0 n = prime0 (n + 1) := by
      unfold primeGap0
      omega
    have ez : (prime0 n : ℤ) + primeGap0 n = prime0 (n + 1) := by
      exact_mod_cast ep
    have bal := (adjacent_difference_iff n r).mp hdelta
    have ethird : (prime0 n : ℤ) + 2 * primeGap0 n + r = prime0 (n + 2) := by
      omega
    change (prime0 n, primeGap0 n) ∈ tripleCandidates N H r
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_range.mpr hless, mem_range.mpr (by omega)⟩,
      hp, ?_, ?_, ?_⟩
    · rw [ep]
      exact hp1
    · rw [ethird]
      exact Int.ofNat_nonneg _
    · rw [ethird]
      simpa only [Int.toNat_natCast] using hp2
  · intro n _ m _ he
    have hp : prime0 n = prime0 m := congrArg Prod.fst he
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hp

/-- First-moment tail bound, with exact finite endpoints. -/
theorem large_gap_mass_bound (N H : ℕ) :
    (H + 1) * (largeGaps N H).card + 2 ≤ prime0 N := by
  classical
  have hsum : (H + 1) * (largeGaps N H).card ≤
      ∑ n ∈ range N, primeGap0 n := by
    calc
      (H + 1) * (largeGaps N H).card =
          ∑ n ∈ range N, if H < primeGap0 n then H + 1 else 0 := by
            rw [← Finset.sum_filter]
            simp [largeGaps, Nat.mul_comm]
      _ ≤ ∑ n ∈ range N, primeGap0 n := by
        apply Finset.sum_le_sum
        intro n _
        by_cases hn : H < primeGap0 n
        · rw [if_pos hn]
          omega
        · rw [if_neg hn]
          exact Nat.zero_le _
  have hp := PaperR7.sum_prime_gaps N
  omega

/-- A finite bound ready for a genuine three-prime sieve estimate. -/
theorem adjacent_count_bound (N H : ℕ) (r : ℤ) :
    (H + 1) * (adjacentMatches N r).card ≤
      prime0 N + (H + 1) * (tripleCandidates N H r).card := by
  classical
  let small := (adjacentMatches N r).filter fun n => primeGap0 n ≤ H
  have hsub : adjacentMatches N r ⊆ largeGaps N H ∪ small := by
    intro n hn
    have hnN := (mem_filter.mp hn).1
    by_cases hs : primeGap0 n ≤ H
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hn, hs⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hnN, by omega⟩))
  have hcard : (adjacentMatches N r).card ≤ (largeGaps N H).card + small.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsmall : small.card ≤ (tripleCandidates N H r).card :=
    short_matches_le_triples N H r
  have hmass := large_gap_mass_bound N H
  have hscaled := Nat.mul_le_mul_left (H + 1) hcard
  have hsmallscaled := Nat.mul_le_mul_left (H + 1) hsmall
  nlinarith only [hscaled, hsmallscaled, hmass]

/-- The outstanding analytic statement. For a suitable H(N), a sieve must
bound triples strongly enough that this quantity is o((H+1)N).
This is a definition, not a theorem, and not an assumption of the library. -/
def AdjacentTripleSieve_target (r : ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ H : ℕ,
    (prime0 N : ℝ) + (H + 1 : ℕ) * ((tripleCandidates N H r).card : ℝ) <
      ε * N * (H + 1 : ℕ)

/-- The correct analytic input implies the adjacent-difference density result.
It does not establish higher-shift differences or full polynomial nonconcentration. -/
theorem adjacent_zeroDensity_of_triple_sieve (r : ℤ)
    (hsieve : AdjacentTripleSieve_target r) :
    ZeroDensity {n | (primeGap0 (n + 1) : ℤ) - primeGap0 n = r} := by
  classical
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hsieve ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨H, hH⟩ := hN₀ N hN
  have hc : ((H + 1 : ℕ) : ℝ) * ((adjacentMatches N r).card : ℝ) ≤
      (prime0 N : ℝ) + (H + 1 : ℕ) * ((tripleCandidates N H r).card : ℝ) := by
    exact_mod_cast adjacent_count_bound N H r
  have hpos : (0 : ℝ) < (H + 1 : ℕ) := by positivity
  have hcount : ((adjacentMatches N r).card : ℝ) < ε * N := by
    nlinarith only [hc, hH, hpos]
  convert hcount using 1 <;> congr

/-- Named full obligations; neither is inferred from the adjacent special case. -/
def FullPrimeNonconcentration_target : Prop :=
  FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))

def NthPrimePNT_target : Prop :=
  Filter.Tendsto (fun n : ℕ => (prime0 n : ℝ) /
    ((n : ℝ) * Real.log n)) Filter.atTop (nhds 1)

/-- Every fixed shift is needed for the displayed density conclusion. The
adjacent (h=1) special case is not silently promoted to this target. -/
def PrimeDifferenceNonconcentration_target : Prop :=
  ∀ h : ℕ, 0 < h → ∀ r : ℤ,
    ZeroDensity {n | (primeGap0 (n + h) : ℤ) - primeGap0 n = r}

/-- Transfer the existing finite cumulative estimate through the PNT
normalisation. The actual prime asymptotic remains an explicit input.
APIs: Mathlib/Topology/Algebra/Order/Field.lean, Tendsto.div_atTop;
Order/Filter/AtTopBot/Archimedean.lean, tendsto_natCast_atTop_atTop. -/
theorem perturbed_positions_PNT_of_prime_PNT (hP : NthPrimePNT_target)
    (M : ℕ) (δ : ℕ → ℕ) (hδ : ∀ n, δ n ≤ 1) :
    Filter.Tendsto (fun n : ℕ =>
      ((2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) : ℕ) : ℝ) /
        ((n : ℝ) * Real.log n)) Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Filter.Tendsto (fun n : ℕ => (M : ℝ) / Real.log n)
      Filter.atTop (nhds 0) :=
    (tendsto_const_nhds (x := (M : ℝ))).div_atTop hlog
  have hu := hP.add herr
  have hu' : Filter.Tendsto (fun n : ℕ =>
      (prime0 n : ℝ) / ((n : ℝ) * Real.log n) + M / Real.log n)
      Filter.atTop (nhds 1) := by
    simpa only [add_zero] using hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hP hu'
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hden : 0 ≤ (n : ℝ) * Real.log n :=
      mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    have hlow : (prime0 n : ℝ) ≤
        ((2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) : ℕ) : ℝ) := by
      exact_mod_cast (PaperR7.perturbed_cumulative_bounds M δ hδ n).1
    exact div_le_div_of_nonneg_right hlow hden
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hl : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hhigh : ((2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) : ℕ) : ℝ) ≤
        (prime0 n : ℝ) + M * n := by
      exact_mod_cast (PaperR7.perturbed_cumulative_bounds M δ hδ n).2
    have hdiv := div_le_div_of_nonneg_right hhigh (mul_pos hnR hl).le
    have heq : ((prime0 n : ℝ) + M * n) / ((n : ℝ) * Real.log n) =
        (prime0 n : ℝ) / ((n : ℝ) * Real.log n) + M / Real.log n := by
      field_simp [hnR.ne', hl.ne']
    exact hdiv.trans_eq heq

/-- Quantitative no-go for the proposed one-gap shortcut.
Every fixed value has at most one occurrence; difference 2 holds everywhere.
The word is synthetic, positive and even, not a sequence of actual prime gaps. -/
def singleGapNoGoWord (n : ℕ) : ℕ := 2 * n + 2

theorem one_gap_counts_do_not_control_difference_counts (N v : ℕ) :
    ((range N).filter fun n => singleGapNoGoWord n = v).card ≤ 1 ∧
    ((range N).filter fun n =>
      (singleGapNoGoWord (n + 1) : ℤ) - singleGapNoGoWord n = 2).card = N := by
  classical
  constructor
  · have hsub : (range N).filter (fun n => singleGapNoGoWord n = v) ⊆
        ({(v - 2) / 2} : Finset ℕ) := by
      intro n hn
      have hv := (mem_filter.mp hn).2
      apply mem_singleton.mpr
      unfold singleGapNoGoWord at hv
      omega
    have hc := Finset.card_le_card hsub
    simpa only [card_singleton] using hc
  · have hall : (range N).filter (fun n =>
        (singleGapNoGoWord (n + 1) : ℤ) - singleGapNoGoWord n = 2) = range N := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun hn => hn.1
      · intro hn
        refine ⟨hn, ?_⟩
        simp only [singleGapNoGoWord, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        omega
    rw [hall, card_range]

#print axioms perturbed_positions_PNT_of_prime_PNT
#print axioms adjacent_count_bound
#print axioms adjacent_zeroDensity_of_triple_sieve
#print axioms one_gap_counts_do_not_control_difference_counts
end
end ErdosProblems.Erdos251.PaperR8.GapCounting
