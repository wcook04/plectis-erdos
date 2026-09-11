import ErdosProblems.Erdos251.PrimeSourceR11
import ErdosProblems.Erdos251.BinarySourceR11
import ErdosProblems.Erdos251.NonconcentrationConsequencesR11
import ErdosProblems.Erdos251.PerturbationGrowthR11

/-!
# Actual-prime specialisations and explicit external-source boundaries

UNRUN. SchlagePuchtaLemma4 is the fixed-polynomial, fixed-block theorem
attributed to Schlage-Puchta, not a growing-block theorem. It is an explicit
argument, not an axiom. PrimeNumberTheorem concerns only Nat.nth Nat.Prime.
The perturbation, its nonconcentration, its cumulative growth and all sparse
support/statistics conclusions are proved, not postulated.
-/
noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR11.PrimeSource
open Nonconcentration SparsePolylog GrowingBlocks SparsePaper PerturbationGrowth
open PaperR8.SparseSchedule

/-- Schlage-Puchta, Lemma 4, in zero-based consecutive-prime-gap notation. -/
def SchlagePuchtaLemma4 : Prop :=
  ∀ k : ℕ, ∀ F : MvPolynomial (Fin (k + 1)) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval
      (fun i : Fin (k + 1) => (primeGap0 (n + i.val) : ℤ)) F = 0}

/-- Classical PNT input only for the ORIGINAL nth prime. -/
def PrimeNumberTheorem : Prop :=
  Tendsto (fun n => (prime0 n : ℝ) / scale n) atTop (𝓝 1)

theorem fixedBlock_of_SchlagePuchta (hSP : SchlagePuchtaLemma4) :
    FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ)) := by
  intro m hm
  cases m with
  | zero => omega
  | succ k => exact hSP k

def cumulative (b : ℕ → ℕ) (n : ℕ) : ℕ := 2 + ∑ i ∈ range n, b i

theorem cumulative_correction_identity (e : ℕ → ℕ) (n : ℕ) :
    cumulative (fun i => primeGap0 i + e i) n = prime0 n + ∑ i ∈ range n, e i := by
  unfold cumulative
  rw [sum_add_distrib, ← Nat.add_assoc, sum_prime_gaps]

theorem bounded_cumulative_sandwich (M : ℕ) (δ : ℕ → ℕ)
    (hδ : ∀ n, δ n ≤ 1) (n : ℕ) :
    prime0 n ≤ cumulative (fun i => primeGap0 i + M * δ i) n ∧
    cumulative (fun i => primeGap0 i + M * δ i) n ≤ prime0 n + M * n := by
  rw [cumulative_correction_identity]
  have hsum : ∑ i ∈ range n, M * δ i ≤ M * n := by
    calc
      _ ≤ ∑ _i ∈ range n, M := sum_le_sum (fun i _ => by have := hδ i; nlinarith)
      _ = _ := by simp [Nat.mul_comm]
  constructor <;> omega

/-- Complete bounded actual-prime corollary, including the cumulative limit.
The input is on the actual unperturbed primes; nothing about b is assumed. -/
theorem prime_bounded_nonconcentration (hSP : SchlagePuchtaLemma4)
    (hPNT : PrimeNumberTheorem) (M K : ℕ) (hM : 0 < M) :
    ∃ b : ℕ → ℕ, ∃ r : ℚ,
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ n < K, b n = primeGap0 n) ∧
      (∀ n, b n = primeGap0 n ∨ b n = primeGap0 n + M) ∧
      (∀ n, b n ≡ primeGap0 n [MOD M]) ∧
      FixedBlockNonconcentration (fun n => (b n : ℤ)) ∧
      (∀ n, prime0 n ≤ cumulative b n ∧ cumulative b n ≤ prime0 n + M * n) ∧
      Tendsto (fun n => (cumulative b n : ℝ) / scale n) atTop (𝓝 1) ∧
      (∀ n, 0 < b n) ∧
      (2 ∣ M → ∀ n, 1 ≤ n → 2 ∣ b n) := by
  classical
  let S : ℝ := ∑' n, primeGapDyadicTerm n
  have hS : HasSum (fun n => (primeGap0 n : ℝ) / 2 ^ (n + 1)) S :=
    summable_primeGapDyadicTerm.hasSum
  have hwidth : 0 < (M : ℝ) / 2 ^ K := by positivity
  obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (show S < S + M / 2 ^ K by linarith)
  obtain ⟨δ, hδ, hprefix, hsum⟩ :=
    BinarySource.exists_bounded_perturbation hS M hM r hr0 K hr1
  let b : ℕ → ℕ := fun n => primeGap0 n + M * δ n
  have hchoices : ∀ n, b n = primeGap0 n ∨ b n = primeGap0 n + M := by
    intro n
    have hd := hδ n
    have hd' : δ n = 0 ∨ δ n = 1 := by omega
    rcases hd' with hd' | hd' <;> simp [b, hd']
  have hNC : FixedBlockNonconcentration (fun n => (b n : ℤ)) := by
    apply finite_perturbation_stability (fun n => (primeGap0 n : ℤ))
      (fun n => (b n : ℤ)) ({0, (M : ℤ)} : Finset ℤ) (fixedBlock_of_SchlagePuchta hSP)
    intro n
    rcases hchoices n with hn | hn <;> simp [hn]
  have hsand := bounded_cumulative_sandwich M δ hδ
  have hlimit : Tendsto (fun n => (cumulative b n : ℝ) / scale n) atTop (𝓝 1) := by
    apply sandwich_preserves_growth (fun n => (prime0 n : ℝ))
      (fun n => (cumulative b n : ℝ)) (M : ℝ) (Nat.cast_nonneg _) hPNT
    · intro n
      exact_mod_cast (hsand n).1
    · intro n
      exact_mod_cast (hsand n).2
  refine ⟨b, r, hsum, ?_, hchoices, ?_, hNC, hsand, hlimit, ?_, ?_⟩
  · intro n hn
    simp [b, hprefix n hn]
  · intro n
    simp [b, Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  · intro n
    exact (primeGap0_positive n).trans_le (Nat.le_add_right _ _)
  · intro hMeven n hn
    exact dvd_add (primeGap0_even n hn) (dvd_mul_of_dvd_left hMeven (δ n))

/-- Exact two-window density-zero specialisation to the convergent actual tail. -/
theorem actual_prime_small_mismatch_zeroDensity (hSP : SchlagePuchtaLemma4)
    (h : ℕ) (hh : 0 < h) :
    ZeroDensity {N | 1 ≤ N ∧ (-1 < shift actualTail h N ∧ shift actualTail h N < 1) ∧
      (-1 < shift actualTail h (N + 1) ∧ shift actualTail h (N + 1) < 1) ∧
      primeGap0 (N + h + 1) ≠ primeGap0 (N + 1)} ∧
    ZeroDensity {N | primeGap0 (N + h + 1) = primeGap0 (N + 1)} := by
  have hrec : Recurrence (fun n => (primeGap0 n : ℤ)) actualTail := by
    intro N
    simpa only [Int.cast_natCast] using actualTail_recurrence N
  obtain ⟨hsmall, hequal⟩ :=
    small_mismatch_zeroDensity (fun n => (primeGap0 n : ℤ)) actualTail
      (fixedBlock_of_SchlagePuchta hSP) hrec h hh
  refine ⟨?_, ?_⟩
  · convert hsmall using 1
    ext N
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hN, hx, hy, hne⟩
      exact ⟨hN, hx, hy, fun heq => hne (by exact_mod_cast heq)⟩
    · rintro ⟨hN, hx, hy, hne⟩
      exact ⟨hN, hx, hy, fun heq => hne (by exact_mod_cast heq)⟩
  · convert hequal using 1
    ext N
    simp only [Set.mem_setOf_eq]
    exact_mod_cast Iff.rfl

/-- The printed ±2 restriction, including its parity premise proved for primes. -/
theorem actual_prime_small_mismatch_pm_two (h N : ℕ)
    (hx : -1 < shift actualTail h N ∧ shift actualTail h N < 1)
    (hy : -1 < shift actualTail h (N + 1) ∧ shift actualTail h (N + 1) < 1)
    (hne : primeGap0 (N + h + 1) ≠ primeGap0 (N + 1)) :
    (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) = 2 ∨
    (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) = -2 := by
  have hrec : Recurrence (fun n => (primeGap0 n : ℤ)) actualTail := by
    intro j
    simpa only [Int.cast_natCast] using actualTail_recurrence j
  have hd0 : (2 : ℤ) ∣ (primeGap0 (N + h + 1) : ℤ) := by
    exact_mod_cast primeGap0_even (N + h + 1) (by omega)
  have hd1 : (2 : ℤ) ∣ (primeGap0 (N + 1) : ℤ) := by
    exact_mod_cast primeGap0_even (N + 1) (by omega)
  have hs := shift_succ hrec h N
  refine small_even_mismatch (d := (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1))
    (x := shift actualTail h N) (y := shift actualTail h (N + 1))
    (dvd_sub hd0 hd1) ?_ hx hy ?_
  · linarith [hs]
  · intro hz
    have hz' := sub_eq_zero.mp hz
    exact hne (by exact_mod_cast hz')

/-- Sparse prime rationalisation: the same support/interval for every target,
with eventual congruences for both coefficients and reconstructed positions. -/
theorem prime_polylogarithmic_interval {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hPNT : PrimeNumberTheorem) (K : ℕ) :
    ∃ start : ℕ, ∃ l u C : ℝ,
      Set.range (centre (polylog ε) start) ⊆ Set.Ici K ∧
      UpperBanachZero (Set.range (centre (polylog ε) start)) ∧
      (∑' n, primeGapDyadicTerm n) < l ∧ l < u ∧ 0 < C ∧
      (∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
        ((supportSlice (centre (polylog ε) start) X L).card : ℝ) ≤ C * X / iterlog X) ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre (polylog ε) start)) ∧
        (∀ n < K, primeGap0 n + e n = primeGap0 n) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
        (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i ∧
          primeGap0 n + e n ≡ primeGap0 n [MOD q] ∧
          cumulative (fun i => primeGap0 i + e i) n ≡ prime0 n [MOD q]) ∧
        HasSum (fun n => ((primeGap0 n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r ∧
        (∀ n, 0 < primeGap0 n + e n) ∧
        (∀ᶠ n : ℕ in atTop, 2 ∣ primeGap0 n + e n) ∧
        Tendsto (fun n => (cumulative (fun i => primeGap0 i + e i) n : ℝ) / scale n) atTop (𝓝 1) ∧
        ∀ m : ℕ → ℕ, Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0) →
          Tendsto (fun X => blockTV primeGap0 (fun n => primeGap0 n + e n) X (m X)) atTop (𝓝 0) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop,
            ∀ Φ : ℕ → (Fin (m X) → ℕ) → ℝ,
              (∀ N ∈ Ico X (2 * X), |Φ N (fun i => primeGap0 (N + i.val))| ≤ 1) →
              (∀ N ∈ Ico X (2 * X), |Φ N (fun i => primeGap0 (N + i.val) + e (N + i.val))| ≤ 1) →
              |testMean primeGap0 X (m X) Φ -
                testMean (fun n => primeGap0 n + e n) X (m X) Φ| < η := by
  obtain ⟨start, l, u, C, hSK, hSZ, hAl, hlu, hC, hrate, hfill⟩ :=
    polylogarithmic_word_interval primeGap0 summable_primeGapDyadicTerm.hasSum hε K
  refine ⟨start, l, u, C, hSK, hSZ, hAl, hlu, hC, hrate, ?_⟩
  intro r hrl hru
  obtain ⟨e, heS, hef, heq, heprefix, hes, heblocks⟩ := hfill r hrl hru
  refine ⟨e, heS, heprefix, hef, ?_, hes, ?_, ?_, ?_, heblocks⟩
  · intro q hq
    filter_upwards [heq q hq] with n hn
    refine ⟨hn.1, hn.2, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hn.1
      simp [Nat.ModEq, hz, Nat.add_mod, Nat.mul_mod]
    · rw [cumulative_correction_identity]
      obtain ⟨z, hz⟩ := hn.2
      simp [Nat.ModEq, hz, Nat.add_mod, Nat.mul_mod]
  · intro n
    exact (primeGap0_positive n).trans_le (Nat.le_add_right _ _)
  · filter_upwards [heq 2 (by norm_num), eventually_ge_atTop (1 : ℕ)] with n hn hn1
    exact dvd_add (primeGap0_even n hn1) hn.1
  · simpa only [cumulative_correction_identity] using
      polylog_positions_preserve_growth prime0 e hPNT hε hε1 hef

/-- The common nondegenerate interval contains an actual rational number. -/
theorem prime_sparse_rational_value {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ S : Set ℕ, ∃ e : ℕ → ℕ, ∃ r : ℚ,
      S ⊆ Set.Ici K ∧ UpperBanachZero S ∧ (∑' n, primeGapDyadicTerm n) < (r : ℝ) ∧
      (∀ n, e n ≠ 0 → n ∈ S) ∧
      (∀ n < K, primeGap0 n + e n = primeGap0 n) ∧
      (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop, q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
      HasSum (fun n => ((primeGap0 n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) :=
  arbitrary_word_sparse_rational_target primeGap0 summable_primeGapDyadicTerm.hasSum
    (polylog ε) (polylog_tendsto_atTop hε) K

/-- Why the arbitrary-M parity remark needs an even-M qualification. -/
theorem odd_perturbation_does_not_preserve_parity :
    (2 : ℕ) ∣ 2 ∧ ¬ (2 : ℕ) ∣ 2 + 1 * 1 := by decide

#print axioms prime_bounded_nonconcentration
#print axioms actual_prime_small_mismatch_zeroDensity
#print axioms prime_polylogarithmic_interval
#print axioms prime_sparse_rational_value
end ErdosProblems.Erdos251.PaperR11.PrimeSource
