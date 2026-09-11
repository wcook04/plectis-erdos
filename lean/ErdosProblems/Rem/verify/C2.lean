/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Rem.C2

/-!
# Adversarial verification of `ErdosProblems/Rem/C2.lean`

Three jobs:

1. `#print axioms` on every public theorem of `C2`.
2. Satisfiability: `#eval` every non-trivial hypothesis on real corpus data
   over a wide range of rows, using the corpus's own definitions
   (`seamIntegerGreedyRemainder`, `seamWeights`, `seamSubsetTarget`,
   `truncatedMersenneWeight`, `mersenneWeightRat`), never a proxy.
3. Independent re-derivation, plus a second, different certificate pushed
   through the general theorem to check it is not a one-instance shell.
-/

namespace ErdosProblems.RemC2.Verify

open ErdosProblems.RemC2 Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

/-! ## 0. The headline statements, fully qualified.

Confirms `C2` talks about the corpus's own `seamIntegerGreedyRemainder`,
`seamSubsetTarget`, `truncatedMersenneWeight` and `mersenneWeightRat`, and has
not silently introduced a proxy of its own. -/

set_option pp.fullNames true in
#check @sixteen_thousand_two_mul_seamIntegerGreedyRemainder_le

set_option pp.fullNames true in
#check @certificate_exceeds_half_point

set_option pp.fullNames true in
#check @seamIntegerGreedyRemainder_add_le_of_certificate

set_option pp.fullNames true in
#check @certificate_lt_half_iff

/-! ## 1. Axioms of every public theorem of `C2` -/

#print axioms integerGreedyRemainder_le
#print axioms integerGreedyRemainder_cons_take
#print axioms integerGreedyRemainder_cons_skip
#print axioms truncatedMersenneWeight_bracket
#print axioms seamWeights_eq_prefix
#print axioms seamIntegerGreedyRemainder_le_prefixCapacity
#print axioms sixteen_thousand_two_mul_seamIntegerGreedyRemainder_le
#print axioms two_mul_seamIntegerGreedyRemainder_le
#print axioms weightedBoolSum_replicate_false
#print axioms seamWeightsFrom_length
#print axioms seamIntegerGreedyRemainder_add_le_of_certificate
#print axioms prefixCertificate_length
#print axioms weightedBoolSum_prefixCertificate
#print axioms seamIntegerGreedyRemainder_add_prefix_le
#print axioms mul_certificate_sum_le
#print axioms certificate_exceeds_half_point
#print axioms prefixCertificate_value
#print axioms prefixCertificate_exceeds_half_point
#print axioms remainder_fourteen
#print axioms bound_fourteen_nonvacuous
#print axioms barrier_twenty_nonvacuous
#print axioms certificate_ratSum
#print axioms certificate_lt_half_iff
#print axioms prefixCertificate_lt_half

/-! ## 2. Satisfiability on real corpus data

Everything below runs the corpus definitions, not a re-implementation. -/

/-- Rows `14 … 120`. -/
def rowsHi : List ℕ := List.range' 14 107

/-- Rows `0 … 13`, below the stated threshold. -/
def rowsLo : List ℕ := List.range 14

/-- The first six bits the corpus greedy actually produces at row `s`. -/
def prefixDecisions (s : ℕ) : List Bool :=
  (integerGreedyBits (seamWeights s) (seamSubsetTarget s)).take 6

def cert4 : List (ℕ × ℕ) := [(2, 56007), (3, 24003), (6, 2667), (7, 1323)]

def cert5 : List (ℕ × ℕ) :=
  [(2, 229362), (3, 98298), (6, 10922), (7, 5418), (14, 42)]

/-! ### 2.0  The remainder sequence itself, and §9's `ρ_14 = 392` -/

#eval (List.range' 2 30).map fun s => (s, seamIntegerGreedyRemainder s)
#eval seamIntegerGreedyRemainder 14
#eval (decide (seamIntegerGreedyRemainder 14 = 392))

/-! ### 2a. The headline positive bound, on real data.

First: `16002 * ρ_s ≤ 4 ^ s` for every row in `[14, 121)` — expect `true`.
Second: the rows BELOW the threshold where the same inequality FAILS.  A
non-empty list there proves the hypothesis `14 ≤ s` is load-bearing, i.e. the
theorem is not a hypothesis-free statement in disguise.
Third: `⌊4 ^ s / ρ_s⌋` and its minimum, measuring how close `16002` is to the
truth. -/

#eval rowsHi.all fun s => 16002 * seamIntegerGreedyRemainder s ≤ 4 ^ s
#eval rowsLo.filter fun s => ¬ (16002 * seamIntegerGreedyRemainder s ≤ 4 ^ s)
#eval ((rowsHi.filter fun s => 0 < seamIntegerGreedyRemainder s).map fun s =>
  4 ^ s / seamIntegerGreedyRemainder s).foldl min (4 ^ 200)
#eval (List.range' 14 12).map fun s => (s, 4 ^ s / seamIntegerGreedyRemainder s)

/-! ### 2b. The six greedy decisions the proof asserts are uniform.

`C2` §5 claims: take `2,3`, skip `4,5`, take `6,7`, uniformly for `s ≥ 14`.
Then the same six decisions on rows `8 … 13`, where the pattern differs — so
`14 ≤ s` is sharp for the rank-`7` decision, not a proof artefact. -/

#eval rowsHi.all fun s => prefixDecisions s = [true, true, false, false, true, true]
#eval (List.range' 8 6).map fun s => (s, prefixDecisions s)

/-! ### 2c. Hypotheses of the general certificate transfer.

`hlen`, then `hadm`, then a check that `prefixCertificate` really selects
ranks `2,3,6,7` of the seam word, then the slack in the transferred
conclusion (`target - (ρ_s + certificate sum)`). -/

#eval (List.range' 8 113).all fun s =>
  (prefixCertificate s).length = (seamWeights s).length
#eval rowsHi.all fun s =>
  weightedBoolSum (seamWeights s) (prefixCertificate s) ≤ seamSubsetTarget s
#eval rowsHi.all fun s =>
  weightedBoolSum (seamWeights s) (prefixCertificate s) =
    truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
      truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7
#eval (List.range' 14 12).map fun s =>
  (s, seamSubsetTarget s -
    (seamIntegerGreedyRemainder s +
      weightedBoolSum (seamWeights s) (prefixCertificate s)))

/-! ### 2d. Hypotheses of the barrier.

`hcert` with `M = 168021`; `hlt : 2 * Σ m_d < M` and the slack `M - 2Σ`;
`hbig : 4 * M * 2 ^ s < 4 ^ s` and the rows where it holds; then the barrier's
CONCLUSION evaluated directly on corpus data — the rows where the capacity
left by the four-rank certificate already exceeds `2 ^ s`. -/

#eval cert4.all fun p => (2 ^ p.1 - 1) * p.2 = 168021
#eval (2 * (cert4.map Prod.snd).sum, 168021,
  decide (2 * (cert4.map Prod.snd).sum < 168021))
#eval (List.range 30).filter fun s => 4 * 168021 * 2 ^ s < 4 ^ s
#eval (List.range 40).filter fun s =>
  2 ^ s + (truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
      truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7) <
    seamSubsetTarget s
#eval (List.range' 20 380).all fun s =>
  2 ^ s + (truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
      truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7) <
    seamSubsetTarget s
#eval (List.range' 20 8).map fun s =>
  (s, (seamSubsetTarget s -
    (truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
      truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7)) - 2 ^ s)

/-! ### 2e. The rational reading of the barrier hypothesis.

`Σ_d 1 / (2 ^ d - 1)` for the four-rank certificate, as an exact rational via
the corpus's own `mersenneWeightRat`; the strict inequality; the exact deficit
`1/2 - Σ`; and a numeric cross-check of `certificate_ratSum`. -/

#eval (cert4.map fun p => mersenneWeightRat p.1).sum
#eval decide ((cert4.map fun p => mersenneWeightRat p.1).sum < 1 / 2)
#eval (1 / 2 - (cert4.map fun p => mersenneWeightRat p.1).sum)
#eval decide ((cert4.map fun p => mersenneWeightRat p.1).sum =
  ((cert4.map Prod.snd).sum : ℚ) / (168021 : ℚ))

/-! ### 2f. The "measured, not proved" claim of the header.

Rows where `ρ_s ≤ 2 ^ s`.  The header asserts these are exactly the ranks of
the greedy Mersenne expansion of `1/2`; that is not proved in `C2` and is not
proved here — recorded only to confirm the header reports its own data
honestly. -/

#eval (List.range' 2 60).filter fun s => seamIntegerGreedyRemainder s ≤ 2 ^ s

/-! ## 3. A second certificate through the general theorem

If `certificate_exceeds_half_point` were a one-instance shell it would not
carry a different certificate.  Here is the five-rank certificate the header
mentions in passing (`1/3 + 1/7 + 1/63 + 1/127 + 1/16383`, common denominator
`M = 688086`), pushed through the same general theorem.  Nothing from `C2`'s
§8 is reused. -/

#eval cert5.all fun p => (2 ^ p.1 - 1) * p.2 = 688086
#eval (2 * (cert5.map Prod.snd).sum, 688086)
#eval (cert5.map fun p => mersenneWeightRat p.1).sum
#eval (1 / 2 - (cert5.map fun p => mersenneWeightRat p.1).sum)

theorem cert5_lt_half :
    (cert5.map fun p => mersenneWeightRat p.1).sum < 1 / 2 :=
  (certificate_lt_half_iff (M := 688086) (by norm_num) cert5 (by decide)).mpr
    (by decide)

/-- The general barrier, carried by a *different* certificate: from row `22`
on, the five-rank certificate also leaves more capacity than the half point.
This is the general theorem doing work, not a restatement of §8. -/
theorem cert5_exceeds_half_point {s : ℕ} (hs : 22 ≤ s) :
    2 ^ s + (truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
        truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7 +
        truncatedMersenneWeight s 14) <
      seamSubsetTarget s := by
  have h1 : (2 : ℕ) ^ 22 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have h2 : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have h3 : (2752344 : ℕ) < 2 ^ s := by
    have h4 : (4194304 : ℕ) ≤ 2 ^ s := by norm_num at h1; exact h1
    omega
  have hbig : 4 * 688086 * 2 ^ s < 4 ^ s := by
    calc 4 * 688086 * 2 ^ s = 2752344 * 2 ^ s := by norm_num
      _ < 2 ^ s * 2 ^ s := Nat.mul_lt_mul_of_lt_of_le h3 (le_refl _) (by positivity)
      _ = 4 ^ s := h2.symm
  have h := certificate_exceeds_half_point (s := s) (cert := cert5)
    (M := 688086) (by norm_num) (by omega) (by decide) (by decide) hbig
  simp only [cert5, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at h
  omega

#print axioms cert5_lt_half
#print axioms cert5_exceeds_half_point

/-! Sanity: the five-rank conclusion holds on real data from `s = 22` on (and
in fact already from `s = 21`). -/

#eval (List.range 40).filter fun s =>
  2 ^ s + (truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
      truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7 +
      truncatedMersenneWeight s 14) < seamSubsetTarget s

/-! ## 4. Distance from `O(2 ^ s)`

`RemainderReachesHalfPointCofinally`-style claims need `ρ_s ≤ 2 ^ s`.  What
`C2` proves is `ρ_s ≤ 4 ^ s / 16002`.  The ratio between the two is the honest
measure of the gap: it grows like `2 ^ s / 16002`. -/

#eval (List.range' 20 10).map fun s => (s, 4 ^ s / 16002, 2 ^ s)
#eval (List.range' 20 10).map fun s => (s, (4 ^ s / 16002) / 2 ^ s)

end ErdosProblems.RemC2.Verify
