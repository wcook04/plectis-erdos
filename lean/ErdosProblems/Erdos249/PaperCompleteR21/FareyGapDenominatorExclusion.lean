import Erdos249257.CertificateKernel
import Erdos249257.GapFareyBound

/-! Paper-form restatement of `prop:C2sup` of the long #249 manuscript:
unbounded Farey-gap denominator bounds imply irrationality.  The hypothesis
`sup_K (b+d)(K) = ∞` says exactly that the proved exclusion bounds on the
`N = 1` window family are arbitrarily large; nothing here proves or attempts
that unboundedness. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21

/-- The wave-17 gap certificate at window `(N, K)` for the denominator `q`:
the committed totient residue avoids the thin band of width `q(N+K+2)`. -/
def GapCertificate (N K q : ℕ) : Prop :=
  (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K))
      % 2 ^ K + q * (N + K + 2) < 2 ^ K

/-- `sup_K (b+d)(K) = ∞`: the proved Farey-gap denominator-exclusion bounds on
the `N = 1` window family are arbitrarily large, that is, every finite
denominator range `[1, Q]` is excluded by some single window `K`. -/
def FareyGapExclusionUnbounded : Prop :=
  ∀ Q : ℕ, ∃ K : ℕ, ∀ q : ℕ, 0 < q → q ≤ Q → GapCertificate 1 K q

/-- **Unbounded Farey bounds imply irrationality** (`prop:C2sup`).
If `sup_K (b+d)(K) = ∞`, then `S = ∑ φ(n)/2ⁿ` is irrational, via the
denominator-exclusion implication and without assuming the certificate supply
of `prop:A10`.  No unboundedness claim is proved here. -/
theorem irrational_totientSeries_of_fareyGapExclusionUnbounded
    (hsup : FareyGapExclusionUnbounded) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine Erdos249257.irrational_tsum_totient_div_pow_two_of_gap_certificate_supply ?_
  intro q hq
  obtain ⟨K, hK⟩ := hsup q
  exact ⟨1, K, hK q hq le_rfl⟩

/-- The currently proved rung of the `N = 1` family, in gap-checker
coordinates: at `K = 240` every denominator `q` with
`0 < q ≤ 79639646646701375323355774875831053 ≈ 7.96×10³⁴` satisfies the gap
certificate.  Each such rung is a finite exclusion. -/
theorem gapFareyBound_window_1_240 (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904)
        % 2 ^ 240 + q * 243 < 2 ^ 240 :=
  GapFareyBound.gap_check_window_1_240_le_79639646646701375323355774875831053
    q hq hqQ

#print axioms irrational_totientSeries_of_fareyGapExclusionUnbounded
#print axioms gapFareyBound_window_1_240
end ErdosProblems.Erdos249.PaperCompleteR21
