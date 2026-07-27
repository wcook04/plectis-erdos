/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.HalfCylinderIntegerGreedy

/-!
# Rem C2: an unconditional upper bound on the seam greedy remainder, and the
exact reason the method stops there

Write `ρ_s := seamIntegerGreedyRemainder s = integerGreedyRemainder
(seamWeights s) (seamSubsetTarget s)`, the one scalar per row on which the
`1/2` question of Erdős `#257` has been reduced to sit.  Before this file the
*only* unconditional bound on `ρ_s` at an arbitrary row was the trivial

  `ρ_s ≤ seamSubsetTarget s`, i.e. `2 * ρ_s ≤ 4 ^ s`,

recorded here as `two_mul_seamIntegerGreedyRemainder_le`.  That bound scales
by `4` from row to row exactly as the row map does, so it is inert.

## What is proved

**Positive.**  `sixteen_thousand_two_mul_seamIntegerGreedyRemainder_le`:

  `∀ s ≥ 14,  16002 * ρ_s ≤ 4 ^ s`.

An unconditional factor-`8001` improvement over the trivial bound, at every
row from `14` on.  The mechanism is not a recurrence: it is a *certificate*.
Ranks `2, 3, 6, 7` are shown to be taken by the row-`s` greedy and ranks
`4, 5` skipped, uniformly in `s`, by Euclidean bracketing of the four floors
`⌊4^s/3⌋, ⌊4^s/7⌋, ⌊4^s/63⌋, ⌊4^s/127⌋` (§2, §5).  Since
`1/2 - 1/3 - 1/7 - 1/63 - 1/127 = 1/16002`, the capacity the greedy still
carries after those decisions is at most `4 ^ s / 16002`, and the remainder
never exceeds the capacity.

**The general tool.**  `seamIntegerGreedyRemainder_add_le_of_certificate`:
*any* admissible Boolean selection of the seam weights bounds `ρ_s`,

  `ρ_s + weightedBoolSum (seamWeights s) bits ≤ seamSubsetTarget s`,

by maximality of descending greedy on the gap-dominating seam word.  This is
the correct general shape of an unconditional upper bound on `ρ`: exhibit a
subset of ranks, not a recurrence.  It is instantiated non-vacuously by
`prefixCertificate`, giving `seamIntegerGreedyRemainder_add_prefix_le`.

**Negative for fixed finite certificates.**  `certificate_exceeds_half_point`.
Encode a *fixed*
certificate as a finite list of pairs `(d, m_d)` with common denominator
`(2 ^ d - 1) * m_d = M`; by `certificate_ratSum` its exact rational value is
`(Σ m_d) / M`, and by `certificate_lt_half_iff` the condition
`2 * Σ m_d < M` says precisely that this value is `< 1/2`.  Under that
condition, as soon as `4 * M * 2 ^ s < 4 ^ s`,

  `2 ^ s + Σ_d ⌊4 ^ s / (2 ^ d - 1)⌋ < seamSubsetTarget s`,

i.e. the capacity the certificate leaves is *already larger than the half
point*.  Specialised to the four-rank certificate of §5
(`prefixCertificate_exceeds_half_point`): from row `20` on it can never
witness `ρ_s ≤ 2 ^ s`.

So this fixed-certificate form of the `C2` angle is capped.  The displayed
constant-depth explicit subsets buy larger constant factors over `4 ^ s / 2`
(adjoin
rank `14` and the rational identity `1/2 - 1/3 - 1/7 - 1/63 - 1/127 - 1/16383
= 1/688086` replaces `16002` by `688086`; the same §5 argument then runs from
row `20`), but the bound stays `Θ(4 ^ s)`, while
`RemainderReachesHalfPointCofinally` needs `O(2 ^ s)`.  The one escape route
the theorem leaves open is the boundary case `2 * Σ m_d = M`: a finite set of
ranks whose Mersenne reciprocals sum to exactly `1/2`.  That is Erdős `#257`
answered positively outright, so within this encoded fixed-certificate schema,
either the selected reciprocals sum exactly to `1/2` or the resulting capacity
eventually exceeds the half point.

Any unconditional bound of order `2 ^ s` obtained by this subset-certificate
method must therefore use certificates whose depth grows with `s`.

## Measured, not proved

Running the corpus definitions on the exact greedy Mersenne expansion of
`1/2` (ranks `2, 3, 6, 7, 14, 20, 21, 26, 27, 32, 33, 34, 35, 38, 39, 42,
44, …`) gives, for every `s` in `[6, 260)`,

  `ρ_s ≤ 2 ^ s`  ⟺  `s` is a rank of that expansion.

No proof of either direction is claimed here.  The forward direction reduces
to the residual bound `r < 2 ^ (1 - s)` where the greedy only supplies
`r < 1 / (2 ^ (s - 1) - 1)`; the two differ by a relative `2 ^ (1 - s)`, which
is the same hairline the whole problem turns on.
-/

namespace ErdosProblems.RemC2

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. Greedy-remainder API -/

theorem integerGreedyRemainder_le (weights : List ℕ) (C : ℕ) :
    integerGreedyRemainder weights C ≤ C :=
  Nat.sub_le _ _

theorem integerGreedyRemainder_cons_take {w C : ℕ} (ws : List ℕ) (h : w ≤ C) :
    integerGreedyRemainder (w :: ws) C = integerGreedyRemainder ws (C - w) := by
  unfold integerGreedyRemainder
  rw [integerGreedyBits, if_pos h]
  simp only [weightedBoolSum]
  omega

theorem integerGreedyRemainder_cons_skip {w C : ℕ} (ws : List ℕ) (h : ¬ w ≤ C) :
    integerGreedyRemainder (w :: ws) C = integerGreedyRemainder ws C := by
  unfold integerGreedyRemainder
  rw [integerGreedyBits, if_neg h]
  simp only [weightedBoolSum]

/-! ## 2. Euclidean bracket for the truncated Mersenne weights -/

theorem truncatedMersenneWeight_bracket (s d : ℕ) (hb0 : 0 < 2 ^ d - 1) :
    (2 ^ d - 1) * truncatedMersenneWeight s d ≤ 4 ^ s ∧
      4 ^ s < (2 ^ d - 1) * truncatedMersenneWeight s d + (2 ^ d - 1) := by
  constructor
  · simpa [truncatedMersenneWeight, Nat.mul_comm] using
      Nat.mul_div_le (4 ^ s) (2 ^ d - 1)
  · have h := (Nat.div_lt_iff_lt_mul hb0).1
      (Nat.lt_succ_self (4 ^ s / (2 ^ d - 1)))
    show 4 ^ s < (2 ^ d - 1) * (4 ^ s / (2 ^ d - 1)) + (2 ^ d - 1)
    calc 4 ^ s < (4 ^ s / (2 ^ d - 1) + 1) * (2 ^ d - 1) := h
      _ = (2 ^ d - 1) * (4 ^ s / (2 ^ d - 1)) + (2 ^ d - 1) := by ring

/-! ## 3. The pure arithmetic of the first four greedy decisions -/

private theorem arith_prefix
    (P Q A w2 w3 w4 w5 w6 w7 : ℕ)
    (hA : 2 * A = P) (hQA : Q ≤ A) (hQ : 16384 ≤ Q) (hbig : 16384 * Q ≤ P)
    (h2 : 3 * w2 ≤ P) (h2' : P < 3 * w2 + 3)
    (h3 : 7 * w3 ≤ P) (h3' : P < 7 * w3 + 7)
    (h4 : 15 * w4 ≤ P) (h4' : P < 15 * w4 + 15)
    (h5 : 31 * w5 ≤ P) (h5' : P < 31 * w5 + 31)
    (h6 : 63 * w6 ≤ P) (h6' : P < 63 * w6 + 63)
    (h7 : 127 * w7 ≤ P) (h7' : P < 127 * w7 + 127) :
    w2 ≤ A - Q ∧
      w3 ≤ A - Q - w2 ∧
      ¬ w4 ≤ A - Q - w2 - w3 ∧
      ¬ w5 ≤ A - Q - w2 - w3 ∧
      w6 ≤ A - Q - w2 - w3 ∧
      w7 ≤ A - Q - w2 - w3 - w6 ∧
      16002 * (A - Q - w2 - w3 - w6 - w7) + 16002 * Q ≤ P + 64007 ∧
      16002 * (A - Q - w2 - w3 - w6 - w7) ≤ P := by
  omega

/-! ## 4. Row shape -/

theorem seamWeights_eq_prefix {s : ℕ} (hs : 8 ≤ s) :
    seamWeights s =
      truncatedMersenneWeight s 2 :: truncatedMersenneWeight s 3 ::
        truncatedMersenneWeight s 4 :: truncatedMersenneWeight s 5 ::
          truncatedMersenneWeight s 6 :: truncatedMersenneWeight s 7 ::
            seamWeightsFrom s 8 := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by omega : 2 < s),
    seamWeightsFrom_eq_cons (by omega : 3 < s),
    seamWeightsFrom_eq_cons (by omega : 4 < s),
    seamWeightsFrom_eq_cons (by omega : 5 < s),
    seamWeightsFrom_eq_cons (by omega : 6 < s),
    seamWeightsFrom_eq_cons (by omega : 7 < s)]

private theorem pow_facts {s : ℕ} (hs : 14 ≤ s) :
    2 * 2 ^ (2 * s - 1) = 4 ^ s ∧ 2 ^ s ≤ 2 ^ (2 * s - 1) ∧
      16384 ≤ 2 ^ s ∧ 16384 * 2 ^ s ≤ 4 ^ s := by
  have hsplit : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hQ : (16384 : ℕ) ≤ 2 ^ s := by
    calc (16384 : ℕ) = 2 ^ 14 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  refine ⟨?_, ?_, hQ, ?_⟩
  · have h1 : (2 : ℕ) * 2 ^ (2 * s - 1) = 2 ^ (2 * s - 1 + 1) := by
      rw [pow_succ]; ring
    rw [h1, show 2 * s - 1 + 1 = 2 * s by omega, pow_mul]
    norm_num
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [hsplit]
    exact Nat.mul_le_mul_right _ hQ

/-! ## 5. The unconditional bound -/

/-- Everything the first six greedy decisions of a row `s ≥ 14` need, in one
place: ranks `2, 3` are taken, ranks `4, 5` are skipped, ranks `6, 7` are
taken, and the resulting capacity is at most `4 ^ s / 16002`. -/
private theorem row_facts {s : ℕ} (hs : 14 ≤ s) :
    truncatedMersenneWeight s 2 ≤ seamSubsetTarget s ∧
      truncatedMersenneWeight s 3 ≤
          seamSubsetTarget s - truncatedMersenneWeight s 2 ∧
      ¬ truncatedMersenneWeight s 4 ≤
          seamSubsetTarget s - truncatedMersenneWeight s 2 -
            truncatedMersenneWeight s 3 ∧
      ¬ truncatedMersenneWeight s 5 ≤
          seamSubsetTarget s - truncatedMersenneWeight s 2 -
            truncatedMersenneWeight s 3 ∧
      truncatedMersenneWeight s 6 ≤
          seamSubsetTarget s - truncatedMersenneWeight s 2 -
            truncatedMersenneWeight s 3 ∧
      truncatedMersenneWeight s 7 ≤
          seamSubsetTarget s - truncatedMersenneWeight s 2 -
            truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 ∧
      16002 * (seamSubsetTarget s - truncatedMersenneWeight s 2 -
          truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
          truncatedMersenneWeight s 7) ≤ 4 ^ s ∧
      truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
          truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7 ≤
        seamSubsetTarget s := by
  obtain ⟨hA, hQA, hQ, hbig⟩ := pow_facts hs
  have b2 := truncatedMersenneWeight_bracket s 2 (by norm_num)
  have b3 := truncatedMersenneWeight_bracket s 3 (by norm_num)
  have b4 := truncatedMersenneWeight_bracket s 4 (by norm_num)
  have b5 := truncatedMersenneWeight_bracket s 5 (by norm_num)
  have b6 := truncatedMersenneWeight_bracket s 6 (by norm_num)
  have b7 := truncatedMersenneWeight_bracket s 7 (by norm_num)
  norm_num at b2 b3 b4 b5 b6 b7
  have hT : seamSubsetTarget s = 2 ^ (2 * s - 1) - 2 ^ s := rfl
  rw [hT]
  omega

/-- **The four-rank prefix bound.**  Row `s ≥ 14` of the concrete seam greedy
takes ranks `2, 3, 6, 7`, skips ranks `4, 5`, and therefore never exceeds the
capacity left after those four subtractions. -/
theorem seamIntegerGreedyRemainder_le_prefixCapacity {s : ℕ} (hs : 14 ≤ s) :
    seamIntegerGreedyRemainder s ≤
      seamSubsetTarget s - truncatedMersenneWeight s 2 -
        truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
        truncatedMersenneWeight s 7 := by
  obtain ⟨c2, c3, c4, c5, c6, c7, -, -⟩ := row_facts hs
  unfold seamIntegerGreedyRemainder
  rw [seamWeights_eq_prefix (by omega),
    integerGreedyRemainder_cons_take _ c2,
    integerGreedyRemainder_cons_take _ c3,
    integerGreedyRemainder_cons_skip _ c4,
    integerGreedyRemainder_cons_skip _ c5,
    integerGreedyRemainder_cons_take _ c6,
    integerGreedyRemainder_cons_take _ c7]
  exact integerGreedyRemainder_le _ _

/-- **The unconditional row bound.**  For every row `s ≥ 14`,
`16002 * ρ_s ≤ 4 ^ s`.  The only unconditional bound available at an arbitrary
row before this was the trivial `2 * ρ_s ≤ 4 ^ s` coming from
`ρ_s ≤ seamSubsetTarget s`. -/
theorem sixteen_thousand_two_mul_seamIntegerGreedyRemainder_le
    {s : ℕ} (hs : 14 ≤ s) :
    16002 * seamIntegerGreedyRemainder s ≤ 4 ^ s := by
  obtain ⟨-, -, -, -, -, -, hfinal, -⟩ := row_facts hs
  have hle := seamIntegerGreedyRemainder_le_prefixCapacity hs
  omega

/-- The trivial bound the corpus already had, for comparison. -/
theorem two_mul_seamIntegerGreedyRemainder_le (s : ℕ) (hs : 1 ≤ s) :
    2 * seamIntegerGreedyRemainder s ≤ 4 ^ s := by
  have h1 : seamIntegerGreedyRemainder s ≤ seamSubsetTarget s :=
    integerGreedyRemainder_le _ _
  have h2 : 2 * 2 ^ (2 * s - 1) = 4 ^ s := by
    have h1' : (2 : ℕ) * 2 ^ (2 * s - 1) = 2 ^ (2 * s - 1 + 1) := by
      rw [pow_succ]; ring
    rw [h1', show 2 * s - 1 + 1 = 2 * s by omega, pow_mul]
    norm_num
  have h3 : seamSubsetTarget s ≤ 2 ^ (2 * s - 1) := Nat.sub_le _ _
  calc 2 * seamIntegerGreedyRemainder s ≤ 2 * 2 ^ (2 * s - 1) :=
        Nat.mul_le_mul_left 2 (h1.trans h3)
    _ = 4 ^ s := h2

/-! ## 6. The general certificate transfer -/

theorem weightedBoolSum_replicate_false (ws : List ℕ) (n : ℕ) :
    weightedBoolSum ws (List.replicate n false) = 0 := by
  induction ws generalizing n with
  | nil => cases n <;> simp [weightedBoolSum]
  | cons w ws ih =>
      cases n with
      | zero => simp [weightedBoolSum]
      | succ n => simpa [List.replicate, weightedBoolSum] using ih n

theorem seamWeightsFrom_length (s d : ℕ) :
    (seamWeightsFrom s d).length = s - d := by
  by_cases h : d < s
  · rw [seamWeightsFrom_eq_cons h, List.length_cons,
      seamWeightsFrom_length s (d + 1)]
    omega
  · rw [seamWeightsFrom_eq_nil (by omega : s ≤ d)]
    simp
    omega
termination_by s - d
decreasing_by omega

/-- **Certificate transfer.**  Any admissible Boolean selection of the seam
weights bounds the greedy remainder.  This is the general shape of an
unconditional upper bound on `ρ_s`: a certificate, not a recurrence. -/
theorem seamIntegerGreedyRemainder_add_le_of_certificate {s : ℕ} (hs : 2 ≤ s)
    {bits : List Bool} (hlen : bits.length = (seamWeights s).length)
    (hadm : weightedBoolSum (seamWeights s) bits ≤ seamSubsetTarget s) :
    seamIntegerGreedyRemainder s + weightedBoolSum (seamWeights s) bits ≤
      seamSubsetTarget s := by
  have hmax := integerGreedyBits_maximal (gap := 2 ^ (s + 1)) (by positivity)
    (seamWeights_gapDominates hs) hlen hadm
  have hadm2 := integerGreedyBits_admissible (seamWeights s) (seamSubsetTarget s)
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  omega

/-- The explicit rank-`{2,3,6,7}` Boolean certificate of row `s`. -/
def prefixCertificate (s : ℕ) : List Bool :=
  [true, true, false, false, true, true] ++ List.replicate (s - 8) false

theorem prefixCertificate_length {s : ℕ} (hs : 8 ≤ s) :
    (prefixCertificate s).length = (seamWeights s).length := by
  rw [prefixCertificate, seamWeights, List.length_append, List.length_replicate,
    seamWeightsFrom_length]
  simp
  omega

theorem weightedBoolSum_prefixCertificate {s : ℕ} (hs : 8 ≤ s) :
    weightedBoolSum (seamWeights s) (prefixCertificate s) =
      truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
        truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7 := by
  rw [seamWeights_eq_prefix hs, prefixCertificate]
  simp only [List.cons_append, List.nil_append, weightedBoolSum]
  rw [weightedBoolSum_replicate_false]
  omega

/-- The four-rank certificate really is admissible and really does bound the
remainder: the certificate transfer, instantiated. -/
theorem seamIntegerGreedyRemainder_add_prefix_le {s : ℕ} (hs : 14 ≤ s) :
    seamIntegerGreedyRemainder s +
        (truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
          truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7) ≤
      seamSubsetTarget s := by
  obtain ⟨-, -, -, -, -, -, -, hadm⟩ := row_facts hs
  have hsum := weightedBoolSum_prefixCertificate (s := s) (by omega)
  have hmain := seamIntegerGreedyRemainder_add_le_of_certificate (s := s)
    (by omega) (prefixCertificate_length (by omega)) (by rw [hsum]; exact hadm)
  rw [hsum] at hmain
  exact hmain

/-! ## 7. The barrier: no fixed certificate ever reaches the half point -/

private theorem barrier_arith {mp mq kp P : ℕ}
    (a1 : mp ≤ 4 * mq + 2 * kp) (a2 : 2 * kp + P ≤ mp) (a3 : 4 * mq < P) :
    False := by
  omega

/-- Clearing denominators: if every rank `d` of the certificate satisfies
`(2 ^ d - 1) * m_d = M`, then `M * Σ_d ⌊4 ^ s / (2 ^ d - 1)⌋ ≤ (Σ_d m_d) * 4 ^ s`. -/
theorem mul_certificate_sum_le {s M : ℕ} (hM : 0 < M) :
    ∀ cert : List (ℕ × ℕ), (∀ p ∈ cert, (2 ^ p.1 - 1) * p.2 = M) →
      M * (cert.map fun p => truncatedMersenneWeight s p.1).sum ≤
        (cert.map Prod.snd).sum * 4 ^ s := by
  intro cert
  induction cert with
  | nil => intro _; simp
  | cons p rest ih =>
      intro hcert
      have hp : (2 ^ p.1 - 1) * p.2 = M := hcert p (by simp)
      have hpos : 0 < 2 ^ p.1 - 1 := by
        rcases Nat.eq_zero_or_pos (2 ^ p.1 - 1) with h | h
        · rw [h, Nat.zero_mul] at hp; omega
        · exact h
      have hb := (truncatedMersenneWeight_bracket s p.1 hpos).1
      have hrest := ih fun q hq => hcert q (List.mem_cons_of_mem _ hq)
      have key : M * truncatedMersenneWeight s p.1 ≤ p.2 * 4 ^ s := by
        calc M * truncatedMersenneWeight s p.1
            = p.2 * ((2 ^ p.1 - 1) * truncatedMersenneWeight s p.1) := by
              rw [← hp]; ring
          _ ≤ p.2 * 4 ^ s := Nat.mul_le_mul_left _ hb
      simp only [List.map_cons, List.sum_cons]
      calc M * (truncatedMersenneWeight s p.1 +
            (rest.map fun p => truncatedMersenneWeight s p.1).sum)
          = M * truncatedMersenneWeight s p.1 +
              M * (rest.map fun p => truncatedMersenneWeight s p.1).sum := by ring
        _ ≤ p.2 * 4 ^ s + (rest.map Prod.snd).sum * 4 ^ s :=
            Nat.add_le_add key hrest
        _ = (p.2 + (rest.map Prod.snd).sum) * 4 ^ s := by ring

/-- **The barrier.**  Let a *fixed* certificate be a finite list of ranks `d`
with common-denominator data `(2 ^ d - 1) * m_d = M`.  If its exact rational
value `Σ_d 1 / (2 ^ d - 1) = (Σ_d m_d) / M` is *strictly* below `1 / 2` — that
is, `2 * Σ_d m_d < M` — then from `4 * M * 2 ^ s < 4 ^ s` on the capacity left
after the certificate is already larger than the half point `2 ^ s`.

So no constant-depth explicit subset of the seam weights can ever certify
`seamIntegerGreedyRemainder s ≤ 2 ^ s`, and the `C2` route caps out at
constant-factor improvements of the trivial `4 ^ s / 2`.  The single escape is
`2 * Σ_d m_d = M`, i.e. an exact finite Mersenne representation of `1 / 2`,
which is Erdős `#257` answered positively outright. -/
theorem certificate_exceeds_half_point {s : ℕ} {cert : List (ℕ × ℕ)} {M : ℕ}
    (hM : 0 < M) (hs1 : 1 ≤ s)
    (hcert : ∀ p ∈ cert, (2 ^ p.1 - 1) * p.2 = M)
    (hlt : 2 * (cert.map Prod.snd).sum < M)
    (hbig : 4 * M * 2 ^ s < 4 ^ s) :
    2 ^ s + (cert.map fun p => truncatedMersenneWeight s p.1).sum <
      seamSubsetTarget s := by
  have hMT := mul_certificate_sum_le (s := s) hM cert hcert
  have hC : 2 * seamSubsetTarget s + 2 * 2 ^ s = 4 ^ s := by
    have h1 : (2 : ℕ) * 2 ^ (2 * s - 1) = 4 ^ s := by
      have h1' : (2 : ℕ) * 2 ^ (2 * s - 1) = 2 ^ (2 * s - 1 + 1) := by
        rw [pow_succ]; ring
      rw [h1', show 2 * s - 1 + 1 = 2 * s by omega, pow_mul]
      norm_num
    have h2 : (2 : ℕ) ^ s ≤ 2 ^ (2 * s - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : seamSubsetTarget s = 2 ^ (2 * s - 1) - 2 ^ s := rfl
    omega
  by_contra hcon
  rw [Nat.not_lt] at hcon
  have hstep : M * (2 * seamSubsetTarget s) ≤
      M * (2 * 2 ^ s) +
        2 * (M * (cert.map fun p => truncatedMersenneWeight s p.1).sum) := by
    have hdouble : 2 * seamSubsetTarget s ≤
        2 * 2 ^ s + 2 * (cert.map fun p => truncatedMersenneWeight s p.1).sum := by
      omega
    calc M * (2 * seamSubsetTarget s)
        ≤ M * (2 * 2 ^ s +
            2 * (cert.map fun p => truncatedMersenneWeight s p.1).sum) :=
          Nat.mul_le_mul_left _ hdouble
      _ = M * (2 * 2 ^ s) +
            2 * (M * (cert.map fun p => truncatedMersenneWeight s p.1).sum) := by
          ring
  have hMC : M * (2 * seamSubsetTarget s) + M * (2 * 2 ^ s) = M * 4 ^ s := by
    rw [← Nat.mul_add, hC]
  have a1 : M * 4 ^ s ≤ 4 * (M * 2 ^ s) +
      2 * ((cert.map Prod.snd).sum * 4 ^ s) := by
    calc M * 4 ^ s = M * (2 * seamSubsetTarget s) + M * (2 * 2 ^ s) := hMC.symm
      _ ≤ (M * (2 * 2 ^ s) +
            2 * (M * (cert.map fun p => truncatedMersenneWeight s p.1).sum)) +
              M * (2 * 2 ^ s) := Nat.add_le_add_right hstep _
      _ = 4 * (M * 2 ^ s) +
            2 * (M * (cert.map fun p => truncatedMersenneWeight s p.1).sum) := by
          ring
      _ ≤ 4 * (M * 2 ^ s) + 2 * ((cert.map Prod.snd).sum * 4 ^ s) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 2 hMT) _
  have a2 : 2 * ((cert.map Prod.snd).sum * 4 ^ s) + 4 ^ s ≤ M * 4 ^ s := by
    calc 2 * ((cert.map Prod.snd).sum * 4 ^ s) + 4 ^ s
        = (2 * (cert.map Prod.snd).sum + 1) * 4 ^ s := by ring
      _ ≤ M * 4 ^ s := Nat.mul_le_mul_right _ (by omega)
  have a3 : 4 * (M * 2 ^ s) < 4 ^ s := by
    calc 4 * (M * 2 ^ s) = 4 * M * 2 ^ s := by ring
      _ < 4 ^ s := hbig
  exact barrier_arith a1 a2 a3

/-! ## 8. The four-rank certificate, both sides -/

/-- The positive side, restated: `1/3 + 1/7 + 1/63 + 1/127 = 84000 / 168021`
and `168021 - 2 * 84000 = 21`, so the certificate leaves `4 ^ s / 16002`. -/
theorem prefixCertificate_value :
    2 * ([(2, 56007), (3, 24003), (6, 2667), (7, 1323)].map Prod.snd).sum + 21 =
      168021 := by
  decide

/-- **The negative side, sharp.**  The rank-`{2,3,6,7}` certificate can never
witness `seamIntegerGreedyRemainder s ≤ 2 ^ s`: from row `20` on, the capacity
it leaves already exceeds the half point. -/
theorem prefixCertificate_exceeds_half_point {s : ℕ} (hs : 20 ≤ s) :
    2 ^ s + (truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
        truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7) <
      seamSubsetTarget s := by
  have h1 : (2 : ℕ) ^ 20 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have h2 : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have h3 : (672084 : ℕ) < 2 ^ s := by
    have : (1048576 : ℕ) ≤ 2 ^ s := by norm_num at h1; exact h1
    omega
  have hbig : 4 * 168021 * 2 ^ s < 4 ^ s := by
    calc 4 * 168021 * 2 ^ s = 672084 * 2 ^ s := by norm_num
      _ < 2 ^ s * 2 ^ s := by
          exact Nat.mul_lt_mul_of_lt_of_le h3 (le_refl _) (by positivity)
      _ = 4 ^ s := h2.symm
  have h := certificate_exceeds_half_point (s := s)
    (cert := [(2, 56007), (3, 24003), (6, 2667), (7, 1323)]) (M := 168021)
    (by norm_num) (by omega) (by decide) (by decide) hbig
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
  omega

/-! ## 9. Non-vacuity -/

private theorem seamWeights_fourteen' :
    seamWeights 14 =
      [89478485, 38347922, 17895697, 8659208, 4260880, 2113665,
        1052688, 525314, 262400, 131136, 65552, 32772] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 13 < 14),
    seamWeightsFrom_eq_nil (by norm_num : 14 ≤ 14)]
  norm_num [truncatedMersenneWeight]

/-- The row-`14` remainder, computed in the kernel. -/
theorem remainder_fourteen : seamIntegerGreedyRemainder 14 = 392 := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [seamWeights_fourteen',
    show seamSubsetTarget 14 = 134201344 by norm_num [seamSubsetTarget]]
  norm_num [integerGreedyBits, weightedBoolSum]

/-- The bound of §5 at `s = 14` is a statement about a real number, and it is
true there with room to spare: `16002 * 392 = 6272784 ≤ 4 ^ 14 = 268435456`. -/
theorem bound_fourteen_nonvacuous :
    16002 * seamIntegerGreedyRemainder 14 ≤ 4 ^ 14 ∧
      16002 * seamIntegerGreedyRemainder 14 = 6272784 := by
  refine ⟨sixteen_thousand_two_mul_seamIntegerGreedyRemainder_le (by norm_num), ?_⟩
  rw [remainder_fourteen]

/-- And the barrier is not vacuous either: at `s = 20` the certificate capacity
really does exceed `2 ^ 20`, while the true remainder there is far below it. -/
theorem barrier_twenty_nonvacuous :
    2 ^ 20 + (truncatedMersenneWeight 20 2 + truncatedMersenneWeight 20 3 +
        truncatedMersenneWeight 20 6 + truncatedMersenneWeight 20 7) <
      seamSubsetTarget 20 :=
  prefixCertificate_exceeds_half_point (by norm_num)

/-! ## 10. Reading the barrier hypothesis as an exact rational value -/

/-- The common-denominator data really does compute the certificate's exact
rational value `Σ_d 1 / (2 ^ d - 1)`. -/
theorem certificate_ratSum {M : ℕ} (hM : 0 < M) :
    ∀ cert : List (ℕ × ℕ), (∀ p ∈ cert, (2 ^ p.1 - 1) * p.2 = M) →
      (cert.map fun p => mersenneWeightRat p.1).sum =
        ((cert.map Prod.snd).sum : ℚ) / (M : ℚ) := by
  have hMne : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  intro cert
  induction cert with
  | nil => intro _; simp
  | cons p rest ih =>
      intro hcert
      have hp : (2 ^ p.1 - 1) * p.2 = M := hcert p (by simp)
      have hpos : 0 < 2 ^ p.1 - 1 := by
        rcases Nat.eq_zero_or_pos (2 ^ p.1 - 1) with h | h
        · rw [h, Nat.zero_mul] at hp; omega
        · exact h
      have hone : 1 ≤ (2 : ℕ) ^ p.1 := Nat.one_le_two_pow
      have hcast : ((2 ^ p.1 - 1 : ℕ) : ℚ) = (2 : ℚ) ^ p.1 - 1 := by
        rw [Nat.cast_sub hone]
        norm_num
      have hqne : ((2 : ℚ) ^ p.1 - 1) ≠ 0 := by
        rw [← hcast]
        exact Nat.cast_ne_zero.mpr (by omega)
      have hpQ : ((2 : ℚ) ^ p.1 - 1) * (p.2 : ℚ) = (M : ℚ) := by
        rw [← hcast, ← Nat.cast_mul, hp]
      have hhead : mersenneWeightRat p.1 = (p.2 : ℚ) / (M : ℚ) := by
        rw [mersenneWeightRat, div_eq_div_iff hqne hMne, one_mul, ← hpQ]
        ring
      rw [List.map_cons, List.sum_cons, hhead,
        ih fun q hq => hcert q (List.mem_cons_of_mem _ hq),
        List.map_cons, List.sum_cons]
      push_cast
      ring

/-- So the barrier hypothesis `2 * Σ_d m_d < M` is exactly "the certificate's
exact value is strictly below `1 / 2`". -/
theorem certificate_lt_half_iff {M : ℕ} (hM : 0 < M) (cert : List (ℕ × ℕ))
    (hcert : ∀ p ∈ cert, (2 ^ p.1 - 1) * p.2 = M) :
    (cert.map fun p => mersenneWeightRat p.1).sum < 1 / 2 ↔
      2 * (cert.map Prod.snd).sum < M := by
  have hMpos : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM
  rw [certificate_ratSum hM cert hcert, div_lt_div_iff₀ hMpos (by norm_num)]
  constructor
  · intro h
    have : (2 : ℚ) * ((cert.map Prod.snd).sum : ℚ) < (M : ℚ) := by linarith
    exact_mod_cast this
  · intro h
    have : (2 : ℚ) * ((cert.map Prod.snd).sum : ℚ) < (M : ℚ) := by
      exact_mod_cast h
    linarith

/-- The four-rank certificate, read as a rational: `1/3 + 1/7 + 1/63 + 1/127`
is strictly below `1/2`, which is precisely why §7 applies to it. -/
theorem prefixCertificate_lt_half :
    ([(2, 56007), (3, 24003), (6, 2667), (7, 1323)].map
        fun p => mersenneWeightRat p.1).sum < 1 / 2 :=
  (certificate_lt_half_iff (M := 168021) (by norm_num) _ (by decide)).mpr
    (by decide)

end ErdosProblems.RemC2
