import Erdos249257.CarrySurvivorExtinction

/-!
Paper-form restatement of `prop:carry-survivor-extinction` (line 7656) of the
long Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

The environment is about the Problem 249 totient series `∑ φ(n)/2^n`.  Its
mathematical clauses are: the finite survivor test excludes integrality of a
shifted tail difference; rationality would supply an eventual period `h₀`;
telescoping propagates integrality along the whole period ray `m·h₀`; the
resulting certificate-supply hypothesis proves irrationality; the single ray
`h = lcm(1,…,t)` suffices; and the supplied finite theorem kills every
`1 ≤ h ≤ 16` at `(N, L) = (14, 9)`, hence every rational whose reduced
denominator divides `2¹⁴·(2ʰ − 1)`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.TotientTailPeriodKiller

/-- `periodLcm t` is the paper's `lcm(1,…,t)`: positive, and divisible by every
`1 ≤ h ≤ t`. -/
theorem paper_periodLcm_is_prefix_lcm (t : ℕ) :
    0 < periodLcm t ∧ ∀ h : ℕ, 1 ≤ h → h ≤ t → h ∣ periodLcm t :=
  ⟨periodLcm_pos t, fun _ h1 ht => dvd_periodLcm h1 ht⟩

/-- Long `prop:carry-survivor-extinction`, every asserted mathematical clause.

1. A survivor kill excludes integrality of `totientTail(N+h) − totientTail(N)`.
2. If the series is not irrational, some positive period `h` makes every tail
   difference integral from some `N₀` on.
3. Telescoping then gives integrality along every positive multiple `m·h`.
4. Hence the stated certificate supply — for every `h₀ ≥ 1` and every `N₀`,
   some `m ≥ 1`, `N ≥ N₀` and finite test length `K` — proves irrationality.
5. It is sufficient to supply those certificates along the single ray
   `h = periodLcm t = lcm(1,…,t)`, with `t` and `N` both unbounded.
6. The supplied finite theorem kills every `1 ≤ h ≤ 16` at `(N, L) = (14, 9)`,
   excludes the corresponding tail differences, and hence excludes every
   rational whose reduced denominator divides `2¹⁴·(2ʰ − 1)` for such an `h`. -/
theorem paper_carry_survivor_extinction :
    (∀ h N K : ℕ, survivorKill h N K →
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) ∧
      (¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) →
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
          totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ h N₀ : ℕ,
        (∀ N, N₀ ≤ N →
            totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) →
          ∀ m N : ℕ, N₀ ≤ N →
            totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      ((∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
          ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (m * h₀) N K) →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      ((∀ t₀ N₀ : ℕ,
          ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (periodLcm t) N K) →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9) ∧
      (∀ h : ℕ, 1 ≤ h → h ≤ 16 →
        totientTail (14 + h) - totientTail 14 ∉ Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 16 →
        (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1) →
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)) := by
  refine ⟨fun _ _ _ hkill => tail_diff_notMem_int_of_survivorKill hkill,
    fun hrat => eventual_period_of_not_irrational hrat,
    fun _ _ hint m N hN => tail_diff_mul_mem_int hint m N hN,
    fun hsupply => irrational_totient_series_of_multiple_survivor_supply hsupply,
    fun hsupply => irrational_totient_series_of_lcm_survivor_supply hsupply,
    certifiedKill_all_upto_sixteen,
    fun h h1 h16 => tail_diff_not_int_upto_sixteen h h1 h16,
    fun r h h1 h16 hdvd =>
      totient_series_ne_rat_of_den_dvd_upto_sixteen r h h1 h16 hdvd⟩

#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_periodLcm_is_prefix_lcm
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_carry_survivor_extinction

end ErdosProblems.Erdos257.PaperCompleteR21
