import Erdos249257.CertificateKernel
import Erdos249257.GapFareyBound

/-! Paper-form restatements of two long-paper environments of Erdős #249:

* the fixed Farey bound: if `S` is rational, its reduced denominator exceeds
  `7.9639646646701375323355774875831053 × 10³⁴`, together with the classical
  mediant lemma and the `K = 240` window certificate and its exact first
  failure, which are the two components the bound is built from;
* the sufficient extension: unbounded exclusion bounds `g(K) → ∞` along the
  `(N = 1, K)` gap checks force `S ∉ ℚ`.

Here `S = ∑_{n≥0} φ(n)/2ⁿ`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open GapFareyBound

/-! ### The fixed Farey bound -/

/-- **The fixed Farey bound.**  If `S` is rational, its reduced denominator
exceeds `79639646646701375323355774875831053`. -/
theorem totientSeries_rational_den_gt_fareyBound (q : ℚ)
    (hq : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (q : ℝ)) :
    79639646646701375323355774875831053 < q.den := by
  by_contra hcon
  exact tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053
    q (not_lt.mp hcon) hq

/-- The classical mediant lemma the bound is built from. -/
theorem farey_gap_paper {a b c d r s : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1) (hleft : a * s < r * b) (hright : r * d < c * s) :
    b + d ≤ s :=
  farey_gap hb hd hdet hleft hright

/-- The `K = 240` window certificate: every denominator
`0 < q ≤ 79639646646701375323355774875831053` passes the `(N = 1, K = 240)`
gap inequality. -/
theorem gapCheck_window_1_240_paper (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904)
        % 2 ^ 240 + q * 243 < 2 ^ 240 :=
  gap_check_window_1_240_le_79639646646701375323355774875831053 q hq hqQ

/-- The bound is sharp at that window: the mediant denominator
`79639646646701375323355774875831054` is the exact first displayed denominator
at which the gap inequality fails. -/
theorem gapCheck_window_1_240_first_failure_paper :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054 :=
  gap_check_window_1_240_first_failure

/-! ### A sufficient extension -/

/-- The `(N = 1, K)` gap check at denominator `q` excludes every rational with
that denominator. -/
theorem gapCheck_window_one_excludes (K q : ℕ) (hq : 0 < q)
    (hcert : (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (1 + r) * 2 ^ (K - r)) % 2 ^ K))
        % 2 ^ K + q * (1 + K + 2) < 2 ^ K) :
    ∀ a : ℤ, (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ) :=
  tsum_totient_div_pow_two_ne_int_div_of_totient_gap_certificate q 1 K hq hcert

/-- **A sufficient extension.**  Suppose `g(K) → ∞` and, for every `K`, the
`(N = 1, K)` gap check excludes every rational of reduced denominator at most
`g(K)`.  Then `S` is irrational: any rational value of `S` would have a fixed
finite denominator, contradicted at a sufficiently large `K`. -/
theorem irrational_of_unbounded_window_one_gapCheck (g : ℕ → ℕ)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop)
    (hcheck : ∀ K q : ℕ, 0 < q → q ≤ g K →
      (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (1 + r) * 2 ^ (K - r)) % 2 ^ K))
        % 2 ^ K + q * (1 + K + 2) < 2 ^ K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  rintro ⟨p, hp⟩
  obtain ⟨K, hK⟩ := (hg.eventually_ge_atTop p.den).exists
  have hcast : (p : ℝ) = (p.num : ℝ) / (p.den : ℝ) := by
    rw [Rat.cast_def]
  exact gapCheck_window_one_excludes K p.den p.pos (hcheck K p.den p.pos hK) p.num
    (hp.symm.trans hcast)

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_rational_den_gt_fareyBound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.farey_gap_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_1_240_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_1_240_first_failure_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_one_excludes
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_unbounded_window_one_gapCheck
