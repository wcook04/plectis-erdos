import Erdos249257.FirstHarmonicGap

/-!
# Erdős #249: a kill at some multiple of each lag is enough

If `∑ φ(n)/2^n` were rational, `eventual_period_of_not_irrational` gives a period `h₀` from some
threshold `N₀` on, and then every multiple `k * h₀` is a period from the same threshold on, since
the tail differences telescope. So the certificate supply needs, for each `h₀ ≥ 1` and each
threshold, a certified kill at SOME multiple of `h₀`, and the multiple may depend on the
threshold. The corpus already proves this (`irrational_totient_series_of_multiple_certificate_supply`,
`CarrySurvivorExtinction.lean`); this file uses it.

The window discrepancy is a difference of one window weight at two bases
(`windowDiscrepancy_eq_windowWeight_sub`), so the first harmonic at lag `h` summed over bases is
the lag-`h` autocorrelation of `M ↦ e(windowWeight M L / 2^L)`. With the subset barrier this gives
the interface `irrational_totient_series_of_multiple_support_gap`: for each `h₀`, some multiple of
`h₀` with a support of average first cosine at most `9/10`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

/-- The window weight `W_L(M) = ∑_{j<L} φ(M+1+j) 2^{L-1-j}`. -/
def windowWeight (M L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (Nat.totient (M + 1 + j) : ℤ) * 2 ^ (L - 1 - j)

/-- The window discrepancy at lag `h` is the difference of the window weights at `N + h` and `N`. -/
theorem windowDiscrepancy_eq_windowWeight_sub (h N L : ℕ) :
    windowDiscrepancy h N L = windowWeight (N + h) L - windowWeight N L := by
  unfold windowDiscrepancy windowWeight
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The support gap along multiples.** For every `h₀ ≥ 1` and every threshold `A`, some multiple
`k * h₀`, some scale `X` and depth `L` with room, and some nonempty set of bases in `[A, 2X)` whose
average first cosine at lag `k * h₀` is at most `9/10`: this gives the irrationality. -/
theorem irrational_totient_series_of_multiple_support_gap
    (hgap : ∀ h₀ : ℕ, 0 < h₀ → ∀ A : ℕ, ∃ k X L : ℕ, ∃ T : Finset ℕ, 0 < k ∧
      16 * (2 * X + k * h₀ + L + 2) ≤ 2 ^ L ∧ T.Nonempty ∧ (∀ N ∈ T, A ≤ N ∧ N < 2 * X) ∧
      (∑ N ∈ T, windowFirstCos (k * h₀) N L) ≤ (9 / 10 : ℝ) * T.card) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_multiple_certificate_supply
  intro h₀ hh₀ A
  obtain ⟨k, X, L, T, hk, hroom, hne, hT, hcos⟩ := hgap h₀ hh₀ A
  obtain ⟨N, hN, hkill⟩ :=
    exists_certifiedKill_of_first_harmonic_gap_subset T (fun N hN => (hT N hN).2) hne hroom hcos
  exact ⟨k, hk, N, (hT N hN).1, L, hkill⟩

end TotientTailPeriodKiller
end Erdos249257

#print axioms Erdos249257.TotientTailPeriodKiller.windowDiscrepancy_eq_windowWeight_sub
#print axioms Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_multiple_support_gap
