import ErdosProblems.Erdos251.GapDifferenceCountingR8

/-!
# Four-prime finite reduction for EVERY separated gap shift

UNCOMPILED. This extends the R8 adjacent (three-prime) reduction to h >= 2.
The target configuration is x, x+d, x+s, x+s+d+r, with four DISTINCT
prime positions. The intervening h-1 primes need not be prescribed for
an upper bound. Large complete spans are removed by an exact first moment.
No sieve estimate, PNT, or density theorem is asserted without its premise.
The case h=1 remains the three-prime problem; it is not run through a
four-distinct-prime bound with repeated positions.
-/

noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR9.ShiftCounting
open PaperR7 PaperR8.GapCounting

/-- Total span of k successive gaps. -/
def gapWindow (n k : ℕ) : ℕ := ∑ i ∈ range k, primeGap0 (n + i)

theorem gapWindow_identity (n k : ℕ) :
    prime0 n + gapWindow n k = prime0 (n + k) := by
  induction k with
  | zero => simp only [gapWindow, sum_range_zero, Nat.add_zero]
  | succ k ih =>
    have hstep : prime0 (n + k) + primeGap0 (n + k) = prime0 (n + k + 1) := by
      have hm := prime0_mono_step (n + k)
      unfold primeGap0
      omega
    rw [gapWindow, sum_range_succ, ← Nat.add_assoc]
    change prime0 n + gapWindow n k + primeGap0 (n + k) = _
    rw [ih]
    simpa only [Nat.add_assoc] using hstep

/-- The total mass of all length-k windows is at most k times one prime
endpoint. This does not assume an asymptotic estimate for that endpoint. -/
theorem window_mass_bound (N k : ℕ) :
    (∑ n ∈ range N, gapWindow n k) ≤ k * prime0 (N + k) := by
  unfold gapWindow
  rw [Finset.sum_comm]
  calc
    (∑ i ∈ range k, ∑ n ∈ range N, primeGap0 (n + i)) ≤
        ∑ _i ∈ range k, prime0 (N + k) := by
      apply Finset.sum_le_sum
      intro i hi
      have hid := gapWindow_identity i N
      have hinner : (∑ n ∈ range N, primeGap0 (n + i)) = gapWindow i N := by
        simp only [gapWindow, Nat.add_comm]
      rw [hinner]
      have him : prime0 (i + N) ≤ prime0 (N + k) :=
        (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (by
          have hik := mem_range.mp hi
          omega)
      omega
    _ = k * prime0 (N + k) := by simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_id]

def shiftedMatches (h N : ℕ) (r : ℤ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => (primeGap0 (n + h) : ℤ) - primeGap0 n = r)

def largeSpans (h N H : ℕ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => H < gapWindow n (h + 1))

/-- Four distinct primes with two outer gaps differing by r. -/
def quadCandidates (N H : ℕ) (r : ℤ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (((range (prime0 N)).product (range (H + 1))).product (range (H + 1))).filter
    (fun z =>
      0 < z.1.2 ∧ z.1.2 < z.2 ∧ 0 < (z.1.2 : ℤ) + r ∧
      Nat.Prime z.1.1 ∧ Nat.Prime (z.1.1 + z.1.2) ∧ Nat.Prime (z.1.1 + z.2) ∧
      Nat.Prime (((z.1.1 : ℤ) + z.2 + z.1.2 + r).toNat))

/-- A genuine injection into the four-prime count for h >= 2. -/
theorem short_shifted_matches_le_quad (h N H : ℕ) (hh : 2 ≤ h) (r : ℤ) :
    ((shiftedMatches h N r).filter (fun n => gapWindow n (h + 1) ≤ H)).card ≤
      (quadCandidates N H r).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun n => ((prime0 n, primeGap0 n), prime0 (n + h) - prime0 n))
  · intro n hn
    obtain ⟨hm, hspan⟩ := mem_filter.mp hn
    obtain ⟨hnN, hdiff⟩ := mem_filter.mp hm
    have hnlt : n < N := mem_range.mp hnN
    have hmono := (Nat.nth_strictMono Nat.infinite_setOf_prime)
    have h01 : prime0 n < prime0 (n + 1) := hmono (by omega)
    have h0h : prime0 n ≤ prime0 (n + h) := hmono.monotone (by omega)
    have h1h : prime0 (n + 1) < prime0 (n + h) := hmono (by omega)
    have hh1 : prime0 (n + h) < prime0 (n + h + 1) := hmono (by omega)
    have ep : prime0 n + primeGap0 n = prime0 (n + 1) := by
      unfold primeGap0
      omega
    have es : prime0 n + (prime0 (n + h) - prime0 n) = prime0 (n + h) := by omega
    have el : prime0 (n + h) + primeGap0 (n + h) = prime0 (n + h + 1) := by
      unfold primeGap0
      omega
    have ewindow : prime0 n + gapWindow n (h + 1) = prime0 (n + h + 1) := by
      simpa only [Nat.add_assoc] using gapWindow_identity n (h + 1)
    have hdH : primeGap0 n ≤ H := by omega
    have hsH : prime0 (n + h) - prime0 n ≤ H := by omega
    have hp0 : Nat.Prime (prime0 n) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    have hp1 : Nat.Prime (prime0 (n + 1)) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + 1)
    have hph : Nat.Prime (prime0 (n + h)) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + h)
    have hplast : Nat.Prime (prime0 (n + h + 1)) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + h + 1)
    have zes : (prime0 n : ℤ) + (prime0 (n + h) - prime0 n : ℕ) = prime0 (n + h) := by
      exact_mod_cast es
    have zel : (prime0 (n + h) : ℤ) + primeGap0 (n + h) = prime0 (n + h + 1) := by
      exact_mod_cast el
    have ez : (prime0 n : ℤ) + (prime0 (n + h) - prime0 n : ℕ) + primeGap0 n + r =
        prime0 (n + h + 1) := by omega
    have hpositive : (0 : ℤ) < (primeGap0 n : ℤ) + r := by
      have hlast : (0 : ℤ) < (primeGap0 (n + h) : ℤ) := by
        exact_mod_cast (show 0 < primeGap0 (n + h) by omega)
      omega
    dsimp only
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_product.mpr
      ⟨mem_range.mpr (hmono hnlt), mem_range.mpr (by dsimp only; omega)⟩,
      mem_range.mpr (by dsimp only; omega)⟩, ?_, ?_, hpositive, hp0, ?_, ?_, ?_⟩
    · dsimp only
      omega
    · dsimp only
      omega
    · simpa only [ep] using hp1
    · simpa only [es] using hph
    · rw [ez]
      simpa only [Int.toNat_natCast] using hplast
  · intro n _ m _ hnm
    have he : prime0 n = prime0 m := congrArg (fun z : (ℕ × ℕ) × ℕ => z.1.1) hnm
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective he

/-- First-moment bound for exceptional complete spans. -/
theorem large_span_mass_bound (h N H : ℕ) :
    (H + 1) * (largeSpans h N H).card ≤ (h + 1) * prime0 (N + (h + 1)) := by
  classical
  have hmass : (H + 1) * (largeSpans h N H).card ≤ ∑ n ∈ range N, gapWindow n (h + 1) := by
    calc
      (H + 1) * (largeSpans h N H).card =
          ∑ n ∈ range N, if H < gapWindow n (h + 1) then H + 1 else 0 := by
        rw [← Finset.sum_filter]
        simp only [largeSpans, sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
      _ ≤ ∑ n ∈ range N, gapWindow n (h + 1) := by
        apply Finset.sum_le_sum
        intro n hn
        split_ifs with he
        · omega
        · exact Nat.zero_le _
  exact hmass.trans (window_mass_bound N (h + 1))

theorem shifted_count_bound (h N H : ℕ) (hh : 2 ≤ h) (r : ℤ) :
    (H + 1) * (shiftedMatches h N r).card ≤
      (h + 1) * prime0 (N + (h + 1)) + (H + 1) * (quadCandidates N H r).card := by
  classical
  let small := (shiftedMatches h N r).filter (fun n => gapWindow n (h + 1) ≤ H)
  have hsub : shiftedMatches h N r ⊆ largeSpans h N H ∪ small := by
    intro n hn
    by_cases hs : gapWindow n (h + 1) ≤ H
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hn, hs⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨(mem_filter.mp hn).1, by omega⟩))
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hsmall : small.card ≤ (quadCandidates N H r).card := short_shifted_matches_le_quad h N H hh r
  have hs := Nat.mul_le_mul_left (H + 1) hc
  have ht := Nat.mul_le_mul_left (H + 1) hsmall
  have hb := large_span_mass_bound h N H
  nlinarith only [hs, ht, hb]

/-- Unproved ANALYTIC target. This is defined for h >= 2 only at use sites.
It is not installed as an axiom and is not claimed from the generic sieve. -/
def SeparatedQuadSieve_target (h : ℕ) (r : ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ H : ℕ,
    ((h + 1 : ℕ) : ℝ) * prime0 (N + (h + 1)) +
      (H + 1 : ℕ) * ((quadCandidates N H r).card : ℝ) < ε * N * (H + 1 : ℕ)

theorem separated_zeroDensity_of_quad_sieve (h : ℕ) (hh : 2 ≤ h) (r : ℤ)
    (hsieve : SeparatedQuadSieve_target h r) :
    ZeroDensity {n | (primeGap0 (n + h) : ℤ) - primeGap0 n = r} := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hsieve ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨H, hH⟩ := hN₀ N hN
  have hc : ((H + 1 : ℕ) : ℝ) * ((shiftedMatches h N r).card : ℝ) ≤
      (h + 1 : ℕ) * (prime0 (N + (h + 1)) : ℝ) +
        (H + 1 : ℕ) * ((quadCandidates N H r).card : ℝ) := by
    exact_mod_cast shifted_count_bound h N H hh r
  have hp : (0 : ℝ) < (H + 1 : ℕ) := by positivity
  have hcount : ((shiftedMatches h N r).card : ℝ) < ε * N := by
    nlinarith only [hc, hH, hp]
  convert hcount using 1 <;> congr

/-- All positive shifts, explicitly separating the adjacent triple case
from the separated four-prime case. The analytic premises remain visible. -/
theorem every_shift_of_counting_estimates
    (hthree : ∀ r : ℤ, AdjacentTripleSieve_target r)
    (hfour : ∀ h : ℕ, 2 ≤ h → ∀ r : ℤ, SeparatedQuadSieve_target h r) :
    PrimeDifferenceNonconcentration_target := by
  intro h hh r
  by_cases h1 : h = 1
  · subst h
    exact adjacent_zeroDensity_of_triple_sieve r (hthree r)
  · exact separated_zeroDensity_of_quad_sieve h (by omega) r (hfour h (by omega) r)

#print axioms short_shifted_matches_le_quad
#print axioms shifted_count_bound
#print axioms every_shift_of_counting_estimates
end ErdosProblems.Erdos251.PaperR9.ShiftCounting
