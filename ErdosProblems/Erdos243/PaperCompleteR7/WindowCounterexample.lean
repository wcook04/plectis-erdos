import ErdosProblems.Erdos243.PaperCompleteR7.RealTail
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Basic

/-!
# Full infinite-modulus no-go for real window endpoints

Uncompiled candidate for the literal first sentence of long-record
`res:coprimalitycap`.  Unlike the finite rounding fixture, this constructs
an infinite strictly increasing pairwise-coprime modulus family, proves
summability of its reciprocals and a bound below 2/5, and computes the
actual active-modulus set.  Thus all global premises are retained.
The later, asymptotic consequence in that environment is not refuted.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7.WindowCounterexample

open scoped BigOperators

private noncomputable def largePrime (N : ℕ) : ℕ :=
  Classical.choose (Nat.exists_infinite_primes N)

private theorem largePrime_spec (N : ℕ) : N ≤ largePrime N ∧ (largePrime N).Prime :=
  Classical.choose_spec (Nat.exists_infinite_primes N)

private noncomputable def tailPrime : ℕ → ℕ :=
  Nat.rec (largePrime 64) (fun n prev ↦ largePrime (max (prev + 1) (2 ^ (n + 7))))

private theorem tailPrime_lower (n : ℕ) : 2 ^ (n + 6) ≤ tailPrime n := by
  cases n with
  | zero => exact (largePrime_spec 64).1
  | succ n =>
      have hh := (largePrime_spec (max (tailPrime n + 1) (2 ^ (n + 7)))).1
      change 2 ^ (n + 1 + 6) ≤ largePrime (max (tailPrime n + 1) (2 ^ (n + 7)))
      have hidx : n + 1 + 6 = n + 7 := by omega
      rw [hidx]
      exact (Nat.le_max_right _ _).trans hh

private theorem tailPrime_prime (n : ℕ) : (tailPrime n).Prime := by
  cases n with
  | zero => exact (largePrime_spec 64).2
  | succ n => exact (largePrime_spec (max (tailPrime n + 1) (2 ^ (n + 7)))).2

private theorem tailPrime_strictMono : StrictMono tailPrime := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hh := (largePrime_spec (max (tailPrime n + 1) (2 ^ (n + 7)))).1
  change tailPrime n < largePrime (max (tailPrime n + 1) (2 ^ (n + 7)))
  have hm := Nat.le_max_left (tailPrime n + 1) (2 ^ (n + 7))
  omega

noncomputable def moduli : ℕ → ℕ
  | 0 => 3
  | n + 1 => tailPrime n

theorem moduli_strictMono : StrictMono moduli := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero =>
      have hh := tailPrime_lower 0
      change 3 < tailPrime 0
      norm_num at hh
      omega
  | succ n => exact tailPrime_strictMono (Nat.lt_succ_self n)

theorem moduli_prime (n : ℕ) : (moduli n).Prime := by
  cases n with
  | zero => norm_num [moduli]
  | succ n => exact tailPrime_prime n

theorem moduli_pairwise : ∀ i j, i ≠ j → Nat.Coprime (moduli i) (moduli j) := by
  intro i j hij
  apply (Nat.coprime_primes (moduli_prime i) (moduli_prime j)).mpr
  exact fun heq ↦ hij (moduli_strictMono.injective heq)

private theorem tail_reciprocal_bound (n : ℕ) :
    1 / (tailPrime n : ℝ) ≤ (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ n := by
  have hlo : (2 : ℝ) ^ (n + 6) ≤ (tailPrime n : ℝ) := by
    exact_mod_cast tailPrime_lower n
  have hp : (0 : ℝ) < (tailPrime n : ℝ) := by exact_mod_cast (tailPrime_prime n).pos
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ (n + 6) := by positivity
  calc
    1 / (tailPrime n : ℝ) ≤ 1 / (2 : ℝ) ^ (n + 6) := by
      apply (div_le_div_iff₀ hp hp2).mpr
      simpa only [one_mul] using hlo
    _ = (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ n := by
      rw [pow_add, one_div_pow]
      norm_num [one_div, mul_inv_rev] <;> ring

private theorem tail_reciprocals :
    Summable (fun n ↦ 1 / (tailPrime n : ℝ)) ∧
      (∑' n, 1 / (tailPrime n : ℝ)) ≤ 1 / 32 := by
  have hg : HasSum (fun n : ℕ ↦ (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ n) (1 / 32) := by
    have hh := (hasSum_geometric_of_abs_lt_one
      (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left (1 / 64 : ℝ)
    norm_num at hh
    exact hh
  have hnonneg : ∀ n, (0 : ℝ) ≤ 1 / (tailPrime n : ℝ) :=
    fun n ↦ div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hsum : Summable (fun n ↦ 1 / (tailPrime n : ℝ)) := by
    apply summable_of_sum_le hnonneg
    intro s
    calc
      ∑ n ∈ s, 1 / (tailPrime n : ℝ) ≤
          ∑ n ∈ s, (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ n :=
        Finset.sum_le_sum (fun n _ ↦ tail_reciprocal_bound n)
      _ ≤ ∑' n, (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ n :=
        hg.summable.sum_le_tsum s (fun n _ ↦ by positivity)
  refine ⟨hsum, ?_⟩
  calc
    (∑' n, 1 / (tailPrime n : ℝ)) ≤ ∑' n, (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ n :=
      hsum.tsum_le_tsum tail_reciprocal_bound hg.summable
    _ = 1 / 32 := hg.tsum_eq

theorem moduli_reciprocals :
    Summable (fun n ↦ 1 / (moduli n : ℝ)) ∧
      (∑' n, 1 / (moduli n : ℝ)) < 2 / 5 := by
  obtain ⟨htail, hbound⟩ := tail_reciprocals
  have hsum : Summable (fun n ↦ 1 / (moduli n : ℝ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [moduli] using htail
  refine ⟨hsum, ?_⟩
  have heq := hsum.tsum_eq_zero_add
  change (∑' n, 1 / (moduli n : ℝ)) =
    1 / (3 : ℝ) + ∑' n, 1 / (tailPrime n : ℝ) at heq
  linarith

/-- The active-index set is exactly {0}, not an assumed value of k. -/
theorem active_moduli_exact :
    {i : ℕ | (moduli i : ℝ) ≤ (21 / 10 : ℝ) + 9 / 5} = {0} := by
  ext i
  cases i with
  | zero => norm_num [moduli]
  | succ i =>
      have h0 := tailPrime_lower 0
      have hmono := tailPrime_strictMono.monotone (Nat.zero_le i)
      have hlarge : (64 : ℝ) ≤ (tailPrime i : ℝ) := by
        have hnat : 64 ≤ tailPrime i := by norm_num at h0; omega
        exact_mod_cast hnat
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, moduli]
      constructor
      · intro h; linarith
      · intro h; omega

/-- Literal real-endpoint first claim of `res:coprimalitycap`. -/
def RealWindowRule : Prop :=
  ∀ m : ℕ → ℕ, StrictMono m → (∀ n, 2 ≤ m n) →
    (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) →
    Summable (fun n ↦ 1 / (m n : ℝ)) →
    (∑' n, 1 / (m n : ℝ)) < 1 →
    ∀ x L : ℝ, 1 ≤ x →
      ({i : ℕ | (m i : ℝ) ≤ x + L}.ncard : ℝ) /
          (1 - ∑' n, 1 / (m n : ℝ)) < L →
      ∃ u : ℕ, x ≤ (u : ℝ) ∧ (u : ℝ) < x + L ∧ ∀ i, ¬ m i ∣ u

/-- Full infinite-family refutation, with every global premise retained. -/
theorem not_real_window_rule : ¬ RealWindowRule := by
  intro h
  obtain ⟨hs, htheta⟩ := moduli_reciprocals
  have ht1 : (∑' n, 1 / (moduli n : ℝ)) < 1 := by linarith
  have hlength :
      ({i : ℕ | (moduli i : ℝ) ≤ (21 / 10 : ℝ) + 9 / 5}.ncard : ℝ) /
        (1 - ∑' n, 1 / (moduli n : ℝ)) < (9 / 5 : ℝ) := by
    rw [active_moduli_exact]
    simp only [Set.ncard_singleton, Nat.cast_one]
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) <
      1 - ∑' n, 1 / (moduli n : ℝ))).mpr
    linarith
  obtain ⟨u, hu0, hu1, huavoid⟩ := h moduli moduli_strictMono
    (fun n ↦ (moduli_prime n).two_le) moduli_pairwise hs ht1
    (21 / 10) (9 / 5) (by norm_num) hlength
  have hu3 : u = 3 := by
    have hlo : (3 : ℝ) ≤ (u : ℝ) := by
      have hnot : ¬ u ≤ 2 := by
        intro hle
        have hr : (u : ℝ) ≤ 2 := by exact_mod_cast hle
        linarith
      exact_mod_cast (show 3 ≤ u by omega)
    have hhi : (u : ℝ) < 4 := by linarith
    have hnhi : u < 4 := by exact_mod_cast hhi
    have hnlo : 3 ≤ u := by exact_mod_cast hlo
    omega
  apply huavoid 0
  simpa only [moduli, hu3] using (dvd_rfl : 3 ∣ 3)

end ErdosProblems.Erdos243.PaperCompleteR7.WindowCounterexample
