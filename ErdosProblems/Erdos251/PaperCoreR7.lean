import ErdosProblems.Erdos251.RealPrimeGapTail
import ErdosProblems.Erdos251.PolynomialGapSeriesValue
import ErdosProblems.Erdos251.FreePairReduction
import ErdosProblems.Erdos251.AffineCylinderCollapse
import ErdosProblems.Erdos251.BoundedPerturbationCountermodel
import Mathlib

/-!
# Paper-complete assemblies for Erdős 251, round 7

New proof SOURCE; compilation has not been run in the return environment.
The imports are the supplied library. Existing single-statement theorems
are referenced in theorem_coverage.json, not re-proved here.

This file assembles conjunctions which the paper displays as one result,
resolves the two existing definitions of the actual real tail, and supplies
the generic real cofinal consumer and the general bounded-perturbation
rational target. It does not assume or prove a prime-specific supply.
-/

open scoped BigOperators

namespace ErdosProblems.Erdos251.PaperR7

/-- The complete statement of `res:polynomialcountermodel`, covering both
index conventions used by the short note and the long record. -/
theorem polynomial_countermodel :
    (∀ n, 0 < polynomialGapWord n) ∧
    (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
    StrictMono polynomialGapWord ∧
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
    (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = 4 * (n : ℤ) + 10) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧
      polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧
    HasSum (fun n : ℕ => (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)) 32 := by
  refine ⟨polynomialGapWord_pos, polynomialGapWord_even,
    polynomialGapWord_strictMono, polynomialTailOrbit_recurrence,
    polynomialTailOrbit_shift_integral, (fun n => by simpa using polynomialGapWord_succ_sub n), ?_,
    hasSum_polynomialGapDyadicTerm⟩
  intro n
  exact ⟨polynomialGapWord_adjacent_difference_ne_two n,
    polynomialGapWord_adjacent_difference_ne_neg_two n⟩

/-- `res:infinite`: summability is part of the conclusion, not an
unexpressed requirement for interpreting the `tsum`. -/
theorem infinite_prime_gap_identity :
    Summable primeDyadicTerm ∧ Summable primeGapDyadicTerm ∧
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n :=
  ⟨summable_primeDyadicTerm, summable_primeGapDyadicTerm,
    tsum_primeDyadicTerm_eq_two_add_primeGap_unconditional⟩

/-- `res:irr-equivalence`, including the extra denominator-`2^n`
normalisation displayed in both versions of the paper. -/
theorem irrationality_reformulation :
    (Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) ∧
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n ∧
    (Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) :=
  ⟨irrational_tsum_primeDyadicTerm_iff_primeGap summable_primeDyadicTerm,
    tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap summable_primeDyadicTerm,
    irrational_tsum_primeDisplayedDyadicTerm_iff_primeGap summable_primeDyadicTerm⟩

/-- `res:block`, both displayed equations in one declaration. -/
theorem block_identity {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h ∧
    tailShift T h N = ((2 ^ h : ℚ) - 1) * T N - dyadicTailBlock g N h :=
  ⟨tail_iterate_eq_pow_mul_sub_block hrec N h,
    tailShift_eq_scaled_sub_block hrec N h⟩

/-- The real version needed when the long record uses the actual tail. -/
theorem real_block_identity {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h ∧
    realTailShift T h N = ((2 ^ h : ℝ) - 1) * T N - dyadicTailBlock g N h :=
  ⟨real_tail_iterate_eq_pow_mul_sub_block hrec N h,
    realTailShift_eq_scaled_sub_block hrec N h⟩

/-- The indexed version of `res:collapse` exactly as printed. -/
theorem eventual_integral_positive_shift {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ h N₀ : ℕ, 0 < h ∧ ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N) := by
  obtain ⟨h, N₀, hh, htail⟩ := exists_eventually_integral_tailShift hrec
  refine ⟨h, N₀, hh, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact htail k

/-- `res:escape-irrational`: the three rationality conditions and both
irrationality conditions are packaged together. -/
theorem rationality_classification {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    (¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N)) ∧
    (¬ Irrational (T 0) ↔
      ∃ h N₀ : ℕ, 0 < h ∧
        ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔
      ∀ h : ℕ, 0 < h → ∀ N, ¬ RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔ CofinalNonintegralTailShifts T) := by
  refine ⟨not_irrational_initial_iff_exists_integral_positive_tailShift hrec,
    ?_, irrational_initial_iff_all_positive_tailShifts_nonintegral hrec,
    irrational_initial_iff_cofinalNonintegralTailShifts hrec⟩
  constructor
  · intro hrat
    obtain ⟨h, N₀, hh, htail⟩ :=
      (not_irrational_initial_iff_exists_eventually_integral_positive_tailShift hrec).mp hrat
    refine ⟨h, N₀, hh, fun N hN => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    exact htail k
  · rintro ⟨h, N₀, hh, htail⟩
    exact (not_irrational_initial_iff_exists_integral_positive_tailShift hrec).mpr
      ⟨h, N₀, hh, htail N₀ le_rfl⟩

/-- A missing generic assembly in the real form of `res:smallpair-real`.
There is no rationality or actual-prime assumption here. -/
theorem real_not_eventually_integral_of_small_mismatch
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h : ℕ)
    (hsupply : ∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
       (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N) := by
  rintro ⟨N₀, hInt⟩
  obtain ⟨N, hN, hsmall, hdigit⟩ := hsupply N₀
  exact realTailShift_not_both_integral_of_small_pair_of_digit_ne hrec h N
    hsmall hdigit ⟨hInt N hN, hInt (N + 1) (by omega)⟩

/-- The signed normal form also holds for real states. The existing
`adjacent_small_mismatch_iff_signed_two_window` has rational states. -/
theorem real_signed_two_window {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < realTailShift T h N ∧ realTailShift T h N < 1 ∧
      -1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1 ∧
      g (N + h + 1) ≠ g (N + 1)) ↔
    ((g (N + h + 1) - g (N + 1) = 2 ∧
       1 / 2 < realTailShift T h N ∧ realTailShift T h N < 1) ∨
     (g (N + h + 1) - g (N + 1) = -2 ∧
       -1 < realTailShift T h N ∧ realTailShift T h N < -(1 / 2))) := by
  have hstep := realTailShift_succ hrec h N
  constructor
  · rintro ⟨hlo, hhi, hslo, hshi, hne⟩
    obtain ⟨k, hk⟩ := heven
    have hkR : (g (N + h + 1) : ℝ) - g (N + 1) = 2 * (k : ℝ) := by
      exact_mod_cast hk
    have hklo : (-2 : ℤ) < k := by
      have : (-2 : ℝ) < (k : ℝ) := by linarith
      exact_mod_cast this
    have hkhi : k < (2 : ℤ) := by
      have : (k : ℝ) < 2 := by linarith
      exact_mod_cast this
    have hkne : k ≠ 0 := by intro hz; apply hne; omega
    have hkcases : k = 1 ∨ k = -1 := by omega
    rcases hkcases with hkone | hkneg
    · left
      have heq : g (N + h + 1) - g (N + 1) = 2 := by omega
      have heqR : (g (N + h + 1) : ℝ) - g (N + 1) = 2 := by exact_mod_cast heq
      exact ⟨heq, by linarith, hhi⟩
    · right
      have heq : g (N + h + 1) - g (N + 1) = -2 := by omega
      have heqR : (g (N + h + 1) : ℝ) - g (N + 1) = -2 := by exact_mod_cast heq
      exact ⟨heq, hlo, by linarith⟩
  · rintro (⟨hd, hlo, hhi⟩ | ⟨hd, hlo, hhi⟩)
    · have hdR : (g (N + h + 1) : ℝ) - g (N + 1) = 2 := by exact_mod_cast hd
      exact ⟨by linarith, hhi, by linarith, by linarith, by omega⟩
    · have hdR : (g (N + h + 1) : ℝ) - g (N + 1) = -2 := by exact_mod_cast hd
      exact ⟨hlo, by linarith, by linarith, by linarith, by omega⟩

/-- Removes the one-index offset in the existing nonperiodicity theorem. -/
theorem prime_gaps_not_eventually_periodic {h : ℕ} (hh : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → primeGap0 (N + h) = primeGap0 N := by
  rintro ⟨N₀, hp⟩
  apply primeGap0_not_eventually_periodic hh
  refine ⟨N₀, fun N hN => ?_⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    hp (N + 1) (by omega)

/-- The two real-tail definitions in the supplied corpus coincide. -/
theorem actual_tail_definitions_agree (N : ℕ) :
    realPrimeGapTail N = primeGapRealTail N :=
  realPrimeGapTail_eq_scaled_tsum N

/-- The long-record free-pair statement with the short-note tail definition. -/
theorem actual_free_pair_criterion :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral realPrimeGapTail := by
  have heq : realPrimeGapTail = primeGapRealTail :=
    funext actual_tail_definitions_agree
  rw [heq]
  exact irrational_primeGap_tsum_iff_cofinalFreePairNonintegral

/-- `res:boundedperturbation` for an arbitrary input sequence. The existing
library has the arbitrary real target theorem and the prime-specific
rational-target theorem; this completes the general rational-target assembly. -/
theorem rational_bounded_perturbation {a : ℕ → ℕ}
    (ha : Summable (fun n => (a n : ℝ) / 2 ^ (n + 1)))
    (M K : ℕ) (hM : 0 < M) :
    ∃ (δ : ℕ → ℕ) (r : ℚ),
      (∀ n, δ n = 0 ∨ δ n = 1) ∧
      (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((a n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) := by
  let A := ∑' n : ℕ, (a n : ℝ) / 2 ^ (n + 1)
  have hpos : (0 : ℝ) < (M : ℝ) / 2 ^ K := by positivity
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn (show A < A + M / 2 ^ K by linarith)
  obtain ⟨δ, hd, hprefix, hsum⟩ :=
    exists_bounded_perturbation ha.hasSum M hM (r : ℝ) hrlo K hrhi
  exact ⟨δ, r, fun n => by have := hd n; omega, hprefix, hsum⟩

/-- Raw summation-by-parts identity for the cumulative perturbation.
Used for the algebraic part of `res:nonconc-primes`; no PNT or
nonconcentration assertion is smuggled into this lemma. -/
theorem sum_prime_gaps (n : ℕ) :
    2 + ∑ i ∈ Finset.range n, primeGap0 i = prime0 n := by
  induction n with
  | zero => simp [prime0, Nat.nth_prime_zero_eq_two]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← Nat.add_assoc, ih, primeGap0]
    have hm := prime0_mono_step n
    omega

theorem perturbed_cumulative_bounds (M : ℕ) (δ : ℕ → ℕ)
    (hδ : ∀ n, δ n ≤ 1) (n : ℕ) :
    prime0 n ≤ 2 + ∑ i ∈ Finset.range n, (primeGap0 i + M * δ i) ∧
    2 + ∑ i ∈ Finset.range n, (primeGap0 i + M * δ i) ≤ prime0 n + M * n := by
  rw [Finset.sum_add_distrib, ← Nat.add_assoc, sum_prime_gaps]
  have hsum : ∑ i ∈ Finset.range n, M * δ i ≤ M * n := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, M :=
        Finset.sum_le_sum fun i _ => by have := hδ i; nlinarith
      _ = M * n := by simp [Nat.mul_comm]
  constructor <;> omega

/-- The whole affine/fixed-lattice theorem as one logical package; all
three mechanisms are reused from the supplied source, without treating one
of them as coverage of the other two. -/
theorem affine_circularity_bundle {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    (∀ h N r : ℕ,
      RatAffinePowTwo (tailShift T h (N + r))
        (dyadicTailBlock (shiftDigit g h) N r) r ↔
      RatEvenIntegral (tailShift T h N)) ∧
    (∀ h : ℕ,
      (∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) →
      ((∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
        ¬ RatAffinePowTwo (tailShift T h (N + r))
          (dyadicTailBlock (shiftDigit g h) N r) r) ↔
        ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))) ∧
    (∀ (h : ℕ) (bound : ℕ → ℚ),
      (∀ N, |tailShift T h N| ≤ bound N) → DyadicScaleDominates bound →
      ((∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧ ∀ z : ℤ,
        bound (N + r) <
          |(dyadicTailBlock (shiftDigit g h) N r : ℚ) - 2 ^ r * (z : ℚ)|) ↔
        ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))) := by
  refine ⟨ratAffinePowTwo_iff_evenIntegral hrec, ?_, ?_⟩
  · intro h heven
    exact cofinal_affinePowTwo_escape_iff_not_eventuallyIntegral hrec h heven
  · intro h bound hbound hscale
    exact cofinal_blockResidue_escape_iff_not_eventuallyIntegral hrec h bound hbound hscale

/-- Local rational obstruction and its cofinal consequence, exactly the two
clauses in `res:smallpair`. -/
theorem rational_small_pair_bundle {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ) :
    (∀ N, ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
      (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) →
      g (N + h + 1) ≠ g (N + 1) →
      ¬ (RatIntegral (tailShift T h N) ∧ RatIntegral (tailShift T h (N + 1)))) ∧
    ((∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
       (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N)) := by
  exact ⟨tailShift_not_both_integral_of_small_pair_of_digit_ne hrec h,
    not_eventuallyIntegralTailShift_of_cofinal_small_mismatch hrec h⟩

/-- The same complete bundle in real states. -/
theorem real_small_pair_bundle {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h : ℕ) :
    (∀ N, ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
      (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) →
      g (N + h + 1) ≠ g (N + 1) →
      ¬ (RealIntegral (realTailShift T h N) ∧ RealIntegral (realTailShift T h (N + 1)))) ∧
    ((∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
       (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) := by
  exact ⟨realTailShift_not_both_integral_of_small_pair_of_digit_ne hrec h,
    real_not_eventually_integral_of_small_mismatch hrec h⟩

/-- Long-record `res:smallpair-real`: both the generic real statement and
the explicitly conditional actual-prime conclusion are kept together. -/
theorem real_small_pair_prime_endpoint {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h : ℕ) :
    (∀ N, ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
      (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) →
      g (N + h + 1) ≠ g (N + 1) →
      ¬ (RealIntegral (realTailShift T h N) ∧ RealIntegral (realTailShift T h (N + 1)))) ∧
    ((∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
       (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) ∧
    ((∀ h' : ℕ, 0 < h' → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ((-1 < realTailShift realPrimeGapTail h' N ∧
        realTailShift realPrimeGapTail h' N < 1) ∧
       (-1 < realTailShift realPrimeGapTail h' (N + 1) ∧
        realTailShift realPrimeGapTail h' (N + 1) < 1)) ∧
      primeGap0 (N + h' + 1) ≠ primeGap0 (N + 1)) →
      Irrational (∑' n : ℕ, primeDyadicTerm n)) := by
  exact ⟨(real_small_pair_bundle hrec h).1,
    (real_small_pair_bundle hrec h).2,
    irrational_primeSeries_of_realPrimeGapTail_small_mismatch⟩

end ErdosProblems.Erdos251.PaperR7
