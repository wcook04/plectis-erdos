import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState
import ErdosProblems.Erdos243.SparseResetRecovery

/-!
# State-level assembly behind the canonical frontier proposition

Uncompiled candidates.  The state theorem is first assembled separately.
The final theorem constructs the canonical state from the explicit rational
sum and quadratic growth, then concludes the paper's whole frontier,
including divergence of the nonnegative partial sums.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators

/-- Failure of the natural Sylvester conclusion forces all four state
properties in `res:frontier`.  The cofinal negative conclusion is expressed
with both the time threshold and magnitude bound quantified explicitly. -/
theorem state_frontier
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∃ N, ∀ n, N ≤ n → 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    (∃ N, ∀ n, N ≤ n → E n ≠ 0) ∧
    Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0) ∧
    (∀ N B : ℕ, ∃ n, N ≤ n ∧ E n < -(B : ℤ)) ∧
    ¬ Summable (negativeRelativeMass C E) := by
  have hnotzero : ¬ ∃ N, ∀ n, N ≤ n → E n = 0 := by
    intro hz
    exact hnot (natural_sylvester_of_eventual_zero a C D E hCpos hC hD hE hz)
  obtain ⟨Nc, hNc⟩ := hvanish 1
  have habsorb : ∀ n, Nc ≤ n → E n = 0 → E (n + 1) = 0 := by
    intro n hn hz
    apply zero_absorbing_at a C D E hC hD hE n hz
    simpa only [one_mul] using hNc (n + 1) (by omega)
  have hnonzero := eventually_nonzero_of_zero_absorbing E Nc habsorb hnotzero
  refine ⟨⟨Nc, hnonzero⟩, (normalized_vanishing_iff C E hCpos).mpr hvanish,
    ?_, ?_⟩
  · intro N B
    by_contra hnone
    have hbound : ∀ n, N ≤ n → -(B : ℤ) ≤ E n := by
      intro n hn
      by_contra he
      apply hnone
      exact ⟨n, hn, by omega⟩
    exact hnot (bounded_negative_endpoint_eventual_multiplier
      a C D E ha hCpos hC hD hE ⟨N, B, hbound⟩ hvanish)
  · intro hsum
    exact hnotzero (eventually_zero_of_summable_negativeRelativeMass_scalar
      C E hCpos (natTail_eq_sub_centeredState a C D E hC hE) hsum)

/-- The numerical negative part in the paper is exactly the corpus's
`negativeRelativeMass`, not a different signed sum. -/
theorem negativeRelativeMass_eq_positive_part
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) :
    negativeRelativeMass C E n = max (-(E n : ℝ)) 0 / (C n : ℝ) := by
  unfold negativeRelativeMass
  congr 1
  by_cases he : 0 ≤ E n
  · have her : (0 : ℝ) ≤ (E n : ℝ) := by exact_mod_cast he
    rw [min_eq_right he]
    simp [max_eq_right (by linarith : -(E n : ℝ) ≤ 0)]
  · have hei : E n ≤ 0 := by omega
    have her : (E n : ℝ) ≤ 0 := by exact_mod_cast hei
    rw [min_eq_left hei, natAbs_cast_real, abs_of_nonpos her,
      max_eq_left (by linarith : (0 : ℝ) ≤ -(E n : ℝ))]

/-- Function-level form of the pointwise identity, so that `Summable`
statements transport between the two spellings. -/
theorem negativeRelativeMass_eq_fun (C : ℕ → ℕ) (E : ℕ → ℤ) :
    negativeRelativeMass C E =
      fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ) :=
  funext (negativeRelativeMass_eq_positive_part C E)

/-- Long record `res:mass`: complete scalar and exact-orbit assertions
with the printed positive-part summand.  The redundant normalised limit
is deliberately not required. -/
theorem finite_negative_mass_paper :
    (∀ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) →
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) →
      Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) →
      ∃ N, ∀ n, N ≤ n → E n = 0) ∧
    (∀ (a C D : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) →
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) →
      Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) →
      ∃ N, ∀ n, N ≤ n →
        (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) := by
  have hscalar : ∀ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) →
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) →
      Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) →
      ∃ N, ∀ n, N ≤ n → E n = 0 := by
    intro C E hc hs hsum
    apply eventually_zero_of_summable_negativeRelativeMass_scalar C E hc hs
    simpa only [negativeRelativeMass_eq_fun] using hsum
  refine ⟨hscalar, ?_⟩
  intro a C D E hc hs hd he hsum
  exact natural_sylvester_of_eventual_zero a C D E hc hs hd he
    (hscalar C E hc (natTail_eq_sub_centeredState a C D E hs he) hsum)


/-- Nonnegative nonsummability is actual divergence of the initial partial
sums to positive infinity.  It is not interpreted via Lean's default value
of `tsum` on nonsummable functions. -/
theorem nonnegative_partial_sums_tendsto_atTop
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hnot : ¬ Summable f) :
    Tendsto (fun n ↦ ∑ j ∈ Finset.range n, f j) atTop atTop := by
  classical
  have hex : ∀ B : ℝ, ∃ N, B ≤ ∑ j ∈ Finset.range N, f j := by
    intro B
    by_contra hnone
    apply hnot
    apply summable_of_sum_le hf
    intro s
    let N := s.sup id + 1
    have hsub : s ⊆ Finset.range N := by
      intro j hj
      apply Finset.mem_range.mpr
      have hjle : j ≤ s.sup id := Finset.le_sup (f := id) hj
      dsimp [N]
      omega
    have hle : ∑ j ∈ s, f j ≤ ∑ j ∈ Finset.range N, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ ↦ hf j)
    have hlt : (∑ j ∈ Finset.range N, f j) < B := by
      by_contra hge
      exact hnone ⟨N, by linarith⟩
    exact hle.trans hlt.le
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨N, hN⟩ := hex B
  refine Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
  exact hN.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hn) (fun j _ _ ↦ hf j))

/-- Both `res:frontier` occurrences, from the actual hypotheses on the
rational reciprocal series.  The displayed infinite mass is represented
by divergence of partial sums, not by the default nonsummable `tsum`.
Indices are zero-based: a 0 represents the first positive denominator.
The hypothetical failure of eventual Sylvester behaviour remains an
explicit premise, so this declaration does not assert a parent solution. -/
theorem canonical_frontier
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (∃ N, ∀ n, N ≤ n → E n ≠ 0) ∧
    Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0) ∧
    (∀ N B : ℕ, ∃ n, N ≤ n ∧ E n < -(B : ℤ)) ∧
    Tendsto (fun N ↦ ∑ n ∈ Finset.range N,
      max (-(E n : ℝ)) 0 / (C n : ℝ)) atTop atTop := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  obtain ⟨hcpos, hdpos, hc, hd, hrep, hnorm, _⟩ :=
    canonical_integer_tail_normalized a ha hapos p q hq hs hgrowth
  have haevent : ∃ N, ∀ n, N ≤ n → 1 < a n := by
    refine ⟨1, fun n hn ↦ ?_⟩
    have h0 := hapos 0
    have hn0 := ha (show 0 < n by omega)
    omega
  obtain ⟨hnonzero, hlim, hnegative, hmass⟩ :=
    state_frontier a C D E haevent hcpos hc hd (fun _ ↦ rfl) hnorm hnot
  refine ⟨hnonzero, hlim, hnegative, ?_⟩
  have hsum : ¬ Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) := by
    simpa only [negativeRelativeMass_eq_fun] using hmass
  apply nonnegative_partial_sums_tendsto_atTop _ _ hsum
  intro n
  exact div_nonneg (le_max_right _ _) (Nat.cast_nonneg _)

end ErdosProblems.Erdos243.PaperCompleteR7
