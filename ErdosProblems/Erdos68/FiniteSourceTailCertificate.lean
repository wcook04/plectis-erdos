import Mathlib.Tactic

/-!
# Finite-source closure for integer triangular recurrences

STATUS: uncompiled draft, prepared against the supplied Lean 4.29.1 slice.
No kernel verification is claimed for this file. There are no new axioms or
proof placeholders. This module proves the *generic induction step only*.

For the factorial application, the desk must separately prove the scalar
recurrence for `isolatedChannelUnit n 1` and the unordered-block divisibility
`k! | (d*k)! / (d!)^k`, then supply the finite-source hypothesis below.
It would be inaccurate to call this a formalisation of the quadratic horizon.
-/

namespace ErdosProblems.Erdos68.FiniteSource

open scoped BigOperators

/-- The contribution of the fixed initial segment to one triangular row. -/
def initialSource (D : ℕ) (w : ℕ → ℕ → ℤ) (u : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ Finset.range n, if d ≤ D then w n d * u d else 0

/-- Once the computed tail and every later net initial source are divisible by
`g`, strong induction propagates divisibility through the entire tail.
The source condition concerns the sum, so cancellations are retained. -/
theorem tail_dvd_of_net_initialSource
    (D N : ℕ) (g : ℤ) (u : ℕ → ℤ) (w : ℕ → ℕ → ℤ)
    (hrec : ∀ n, D < n → u n = -(∑ d ∈ Finset.range n, w n d * u d))
    (hprefix : ∀ n, D < n → n ≤ N → g ∣ u n)
    (hsource : ∀ n, N < n → g ∣ initialSource D w u n) :
    ∀ n, D < n → g ∣ u n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsmall : n ≤ N
    · exact hprefix n hn hsmall
    · have hlarge : N < n := Nat.lt_of_not_ge hsmall
      have hterm : ∀ d ∈ Finset.range n,
          g ∣ (w n d * u d - (if d ≤ D then w n d * u d else 0)) := by
        intro d hd
        by_cases hlow : d ≤ D
        · simp [hlow]
        · have hdu : g ∣ u d :=
            ih d (Finset.mem_range.mp hd) (Nat.lt_of_not_ge hlow)
          rcases hdu with ⟨a, ha⟩
          refine ⟨w n d * a, ?_⟩
          simp only [if_neg hlow, sub_zero]
          rw [ha]
          ring
      have hrest : g ∣
          (∑ d ∈ Finset.range n, w n d * u d) - initialSource D w u n := by
        unfold initialSource
        rw [← Finset.sum_sub_distrib]
        exact Finset.dvd_sum hterm
      have htotal : g ∣ ∑ d ∈ Finset.range n, w n d * u d := by
        have hadd := dvd_add hrest (hsource n hlarge)
        simpa only [sub_add_cancel] using hadd
      rw [hrec n hn]
      exact dvd_neg.mpr htotal

/-- Termwise extinction is sufficient but stronger than net-source closure. -/
theorem tail_dvd_of_termwise_initialSource
    (D N : ℕ) (g : ℤ) (u : ℕ → ℤ) (w : ℕ → ℕ → ℤ)
    (hrec : ∀ n, D < n → u n = -(∑ d ∈ Finset.range n, w n d * u d))
    (hprefix : ∀ n, D < n → n ≤ N → g ∣ u n)
    (hsource : ∀ n, N < n → ∀ d, d < n → d ≤ D → g ∣ w n d * u d) :
    ∀ n, D < n → g ∣ u n := by
  apply tail_dvd_of_net_initialSource D N g u w hrec hprefix
  intro n hn
  unfold initialSource
  apply Finset.dvd_sum
  intro d hd
  by_cases hlow : d ≤ D
  · simpa only [if_pos hlow] using hsource n hn d (Finset.mem_range.mp hd) hlow
  · simp only [if_neg hlow, dvd_zero]

/-- The two nonzero residues in the depth-24 certificate sum to its modulus.
This arithmetic identity does not establish their factorial-source provenance. -/
theorem depth24_source_residues_cancel :
    (7228208988000 : ℤ) + 14456417976000 = 21684626964000 := by
  norm_num

/-- A sharp remote-support witness: channel 2 vanishes and the moment is 360.
The ordinary report proves the matching universal lower bound on support n≥4. -/
theorem remote_small_witness :
    (-15 : ℤ) * 6 + 90 = 0 ∧ (-15 : ℤ) * 24 + 720 = 360 := by
  norm_num

end ErdosProblems.Erdos68.FiniteSource
