import ErdosProblems.Erdos68.DivisorChannelBasis
import ErdosProblems.Erdos68.ChannelBreakpointRigidity

/-!
# Literal support-sensitive normal-form and band statements

The assumptions below concern only nonzero coefficients in lambda.support.
They do not require an arbitrary list's zero-coefficient entries to satisfy
support restrictions. These are the Finsupp forms of long res:normalform and
res:bandbreakpoint. All pointwise arithmetic is reused from the supplied source.
STATUS: uncompiled proof candidates.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators

/-- Integral normal form on the literal finite coefficient support. -/
theorem supported_integral_normal_form (f : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℤ, channelNumerator f d = factorialMoment f + ((d.factorial : ℤ) - 1) * k := by
  obtain ⟨k, hk⟩ := channelModulus_dvd_moment_sub_channel f hd
  refine ⟨-k, ?_⟩
  linarith

/-- The whole band identity with no restrictions on zero coefficients. -/
theorem supported_quotient_band (f : ℕ →₀ ℤ) (d k : ℕ)
    (hlo : ∀ n ∈ f.support, k * d ≤ n)
    (hhi : ∀ n ∈ f.support, n < (k + 1) * d) :
    factorialMoment f = (d.factorial : ℤ) ^ k * channelNumerator f d := by
  classical
  unfold factorialMoment channelNumerator Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have h := _root_.Erdos68.channel_coefficient_band (hlo n hn) (hhi n hn)
  have hc : (n.factorial : ℤ) = (d.factorial : ℤ) ^ k * (channelWeight n d : ℤ) := by
    have hz := congrArg (fun a : ℕ => (a : ℤ)) h.symm
    simpa only [channelWeight, Nat.cast_mul, Nat.cast_pow] using hz
  show f n * (n.factorial : ℤ) =
      (d.factorial : ℤ) ^ k * (f n * (channelWeight n d : ℤ))
  rw [hc]
  ring

theorem supported_first_band_cancellation (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hhi : ∀ n ∈ f.support, n < 2 * d)
    (hz : channelNumerator f d = 0) : factorialMoment f = 0 := by
  have h := supported_quotient_band f d 1
    (by simpa using hlo) (by simpa using hhi)
  simpa [hz] using h

/-- The witness is an actually supported index, not an unused list entry. -/
theorem supported_breakpoint_escape (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hz : channelNumerator f d = 0) (hm : factorialMoment f ≠ 0) :
    ∃ n ∈ f.support, 2 * d ≤ n := by
  classical
  by_contra h
  have hhi : ∀ n ∈ f.support, n < 2 * d := by
    intro n hn
    exact lt_of_not_ge (fun hnd => h ⟨n, hn, hnd⟩)
  exact hm (supported_first_band_cancellation f d hlo hhi hz)

end ErdosProblems.Erdos68.PaperComplete
