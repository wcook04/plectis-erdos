import Erdos249257.TotientActualLcmOrbitNonintegrality
import Erdos249257.TotientActualLcmShortKill

/-! Paper-form restatements of the long paper's actual-LCM diagonal
consequences:

* `prop:NI-01` — irrationality is equivalent to cofinal non-integrality of the
  diagonal orbit `Ω_a = R_{2H(2^a)} - R_{H(2^a)}`;
* `prop:AR-07` — a cofinal supply of short-window diagonal certificates
  (`L < 2·2^a`) implies irrationality, with the certificate written out;
* `prop:SEP-03` — the fixed separation `|Ω_a - z| ≥ 1/32 + ε_{a,q_a}` at the
  prescribed odd depth `2q_a+1` implies irrationality;
* `prop:SK-02` — the supplied finite result through exponent six, with the
  witnesses at `(a,L) = (4,23)` and `(6,93)`.

Here `H(t) = periodLcm t`, `R_N = totientTail N`, `D(h,N,L) =
windowDiscrepancy h N L` and `C(h,N,L) = certifiedKill h N L`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine

/-! ### `prop:NI-01` — the equivalent diagonal nonintegrality condition -/

/-- **An equivalent diagonal nonintegrality condition.**
`S ∉ ℚ ↔ ∀ a₀, ∃ a ≥ a₀, Ω_a ∉ ℤ`. -/
theorem irrational_iff_diagonal_orbit_nonintegrality :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
        totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
          Set.range ((↑) : ℤ → ℝ) :=
  irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply

/-! ### `prop:AR-07` — a sufficient short-window condition -/

/-- The diagonal certificate written out: at `h = N = H(2^a)` the excluded
radius is `2H + L + 2`. -/
theorem diagonal_certificate_unfolded (a L : ℕ) :
    certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L ↔
      (((2 * periodLcm (2 ^ a) + L + 2 : ℕ) : ℤ) <
          windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L % 2 ^ L ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L % 2 ^ L <
          2 ^ L - ((2 * periodLcm (2 ^ a) + L + 2 : ℕ) : ℤ)) := by
  unfold certifiedKill
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **A sufficient short-window condition.**  If for every `a₀` there are
`a ≥ a₀` and `L < 2·2^a` with `C(H_{2^a}, H_{2^a}, L)`, then `S ∉ ℚ`. -/
theorem irrational_of_short_window_diagonal_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totientSeries_of_shortArithmeticKillSupply ?_
  intro a₀
  obtain ⟨a, L, ha, hL, hcert⟩ := hsupply a₀
  exact ⟨a, L, ha, hL, (lcmDiagonalArithmeticKill_iff_certifiedKill (2 ^ a) L).2 hcert⟩

/-! ### `prop:SEP-03` — a sufficient approximation condition -/

/-- The paper's prescribed index `q_a = ⌊(⌊log₂ H⌋ + 10)/2⌋`, so that
`2q_a + 1` is the least odd integer at least `⌊log₂ H⌋ + 10`. -/
def prescribedOddIndex (a : ℕ) : ℕ := (Nat.log2 (periodLcm (2 ^ a)) + 10) / 2

/-- The prescribed odd depth is the tree's odd-guarded canonical depth. -/
theorem oddGuarded_depth_eq_prescribed (a : ℕ) :
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * prescribedOddIndex a + 1 := by
  unfold prescribedOddIndex
  have hc : canonicalAdjacentSuffixDepth (2 ^ a) = Nat.log2 (periodLcm (2 ^ a)) + 10 := rfl
  by_cases h : Even (canonicalAdjacentSuffixDepth (2 ^ a))
  · rw [oddGuardedCanonicalAdjacentSuffixDepth_of_even h, hc]
    obtain ⟨k, hk⟩ := h
    rw [hc] at hk
    omega
  · rw [Nat.not_even_iff_odd] at h
    rw [oddGuardedCanonicalAdjacentSuffixDepth_of_odd h, hc]
    obtain ⟨k, hk⟩ := h
    rw [hc] at hk
    omega

/-- **A sufficient approximation condition.**  If for every `a₀` there is
`a ≥ max(2, a₀)` with `|Ω_a - z| ≥ 1/32 + ε_{a,q_a}` for every integer `z`,
then `S ∉ ℚ`.  Here `ε_{a,q} = (2H + 2q + 3)/2^{2q+1}`. -/
theorem irrational_of_diagonal_orbit_separation_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a : ℕ, max 2 a₀ ≤ a ∧ ∀ z : ℤ,
      (1 : ℝ) / 32 +
          ((2 * periodLcm (2 ^ a) + 2 * prescribedOddIndex a + 3 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * prescribedOddIndex a + 1) ≤
        |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) - (z : ℝ)|) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totientSeries_of_actualLcmOrbitSeparationSupply ?_
  intro a₀
  obtain ⟨a, ha, hsep⟩ := hsupply a₀
  exact ⟨a, prescribedOddIndex a, ha, oddGuarded_depth_eq_prescribed a, hsep⟩

/-! ### `prop:SK-02` — the supplied finite result through exponent six -/

/-- **A sufficient extension of the examples through exponent 6.**
`∀ a₀ ≤ 6, ∃ a, L, a ≥ a₀ ∧ L < 2·2^a ∧ C(H_{2^a}, H_{2^a}, L)`. -/
theorem short_window_diagonal_through_six (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L := by
  obtain ⟨a, L, ha, hL, hkill⟩ :=
    powerTwoActualLcmShortArithmeticKillSupply_through_six a₀ ha₀
  exact ⟨a, L, ha, hL, (lcmDiagonalArithmeticKill_iff_certifiedKill (2 ^ a) L).1 hkill⟩

/-- The two witnesses `(a,L) = (4,23)` and `(6,93)` giving the bounded family. -/
theorem short_window_diagonal_witnesses :
    certifiedKill (periodLcm (2 ^ 4)) (periodLcm (2 ^ 4)) 23 ∧ (23 : ℕ) < 2 * 2 ^ 4 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ∧ (93 : ℕ) < 2 * 2 ^ 6 :=
  ⟨(lcmDiagonalArithmeticKill_iff_certifiedKill (2 ^ 4) 23).1
      lcmDiagonalArithmeticKill_two_pow_four, by norm_num,
    (lcmDiagonalArithmeticKill_iff_certifiedKill (2 ^ 6) 93).1
      lcmDiagonalArithmeticKill_two_pow_six, by norm_num⟩

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_iff_diagonal_orbit_nonintegrality
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.diagonal_certificate_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_short_window_diagonal_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.oddGuarded_depth_eq_prescribed
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_diagonal_orbit_separation_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_through_six
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_witnesses
