import ErdosProblems.Erdos251.PaperCoreR7

/-!
# Explicit real-tail truncation for the two papers

New proof source, NOT compiled in the return environment.
Targets: long `res:explicit-remainder`, short `res:truncation`, long
`xr:truncation`. No analytic assumption is inserted into the explicit
quartic estimate. The general majorant theorem keeps the paper's
summability and cofinal certificate hypotheses explicit.
-/

open Filter Topology
open scoped BigOperators

namespace ErdosProblems.Erdos251.PaperR7

noncomputable def shiftedGapTerm (N j : ℕ) : ℝ :=
  (primeGap0 (N + j + 1) : ℝ) / 2 ^ (j + 1)

/-- Summability of the actual shifted gap series, not just of its `tsum`. -/
theorem summable_shiftedGapTerm (N : ℕ) : Summable (shiftedGapTerm N) := by
  have hs : Summable (fun j => primeGapDyadicTerm (j + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr summable_primeGapDyadicTerm
  refine (hs.mul_left ((2 : ℝ) ^ (N + 1))).congr fun j => ?_
  unfold shiftedGapTerm primeGapDyadicTerm
  rw [show j + (N + 1) = N + j + 1 by omega]
  rw [show N + j + 1 + 1 = (N + 1) + (j + 1) by omega, pow_add]
  field_simp
  ring

/-- HasSum version of the actual real-tail bridge. -/
theorem hasSum_shiftedGapTerm (N : ℕ) :
    HasSum (shiftedGapTerm N) (realPrimeGapTail N) := by
  rw [realPrimeGapTail_eq_tsum_shifted_gaps]
  exact (summable_shiftedGapTerm N).hasSum

theorem realPrimeGapTail_nonneg (N : ℕ) : 0 ≤ realPrimeGapTail N := by
  rw [realPrimeGapTail_eq_tsum_shifted_gaps]
  exact tsum_nonneg fun j => by positivity

/-- Real quartic from the displayed remainder, with all constants unchanged. -/
def quarticTailPolynomial (x : ℝ) : ℝ :=
  x ^ 4 + 8 * x ^ 3 + 36 * x ^ 2 + 104 * x + 150

theorem quarticTailPolynomial_step (x : ℝ) :
    quarticTailPolynomial (x + 1) =
      2 * quarticTailPolynomial x - (x + 1) ^ 4 := by
  unfold quarticTailPolynomial
  ring

/-- Exact finite fourth-moment telescope. -/
theorem quartic_weighted_partial_sum (x : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, (x + (j : ℝ) + 1) ^ 4 / 2 ^ (j + 1) =
      quarticTailPolynomial x - quarticTailPolynomial (x + m) / 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hstep : quarticTailPolynomial (x + (m + 1 : ℕ)) =
        2 * quarticTailPolynomial (x + m) - (x + m + 1) ^ 4 := by
      push_cast
      simpa [add_assoc] using quarticTailPolynomial_step (x + m)
    rw [hstep, pow_succ]
    field_simp
    ring

/-- Each polynomial term in the terminal remainder vanishes. -/
theorem tendsto_quarticTailPolynomial_div_two_pow (x : ℝ) :
    Tendsto (fun n : ℕ => quarticTailPolynomial (x + n) / 2 ^ n)
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ 0 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num)
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num)
  have h4 : Tendsto (fun n : ℕ => (n : ℝ) ^ 4 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num)
  have hlim := (((h4.add (h3.const_mul (4 * x + 8))).add
      (h2.const_mul (6 * x ^ 2 + 24 * x + 36))).add
      (h1.const_mul (4 * x ^ 3 + 24 * x ^ 2 + 72 * x + 104))).add
      (h0.const_mul (quarticTailPolynomial x))
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr fun n => ?_
  unfold quarticTailPolynomial
  ring

/-- The infinite polynomial sum is evaluated, not postulated. -/
theorem hasSum_quartic_weighted (x : ℝ) :
    HasSum (fun j : ℕ => (x + (j : ℝ) + 1) ^ 4 / 2 ^ (j + 1))
      (quarticTailPolynomial x) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity)]
  have hlim := (tendsto_const_nhds (x := quarticTailPolynomial x)).sub
    (tendsto_quarticTailPolynomial_div_two_pow x)
  simpa only [quartic_weighted_partial_sum, sub_zero] using hlim

/-- The source's bound on nth primes gives the needed bound on each gap. -/
theorem gap_le_quartic (n : ℕ) :
    (primeGap0 n : ℝ) ≤ 1250 * ((n : ℝ) + 2) ^ 4 := by
  have hg : primeGap0 n ≤ 1250 * (n + 2) ^ 4 :=
    (Nat.sub_le _ _).trans (by simpa [Nat.add_assoc] using prime0_le_polynomial (n + 1))
  exact_mod_cast hg

/-- An unconditional bound on each COMPLETE shifted tail. -/
theorem realPrimeGapTail_le_quartic (N : ℕ) :
    realPrimeGapTail N ≤ 1250 * quarticTailPolynomial ((N : ℝ) + 2) := by
  have hm := (hasSum_quartic_weighted ((N : ℝ) + 2)).mul_left 1250
  calc
    realPrimeGapTail N = ∑' j : ℕ, shiftedGapTerm N j :=
      (hasSum_shiftedGapTerm N).tsum_eq.symm
    _ ≤ ∑' j : ℕ, 1250 * (((N : ℝ) + 2 + j + 1) ^ 4 / 2 ^ (j + 1)) := by
      apply (summable_shiftedGapTerm N).tsum_le_tsum _ hm.summable
      intro j
      have hb := gap_le_quartic (N + j + 1)
      dsimp [shiftedGapTerm]
      have hb' : (primeGap0 (N + j + 1) : ℝ) ≤
          1250 * ((N : ℝ) + 2 + j + 1) ^ 4 := by
        convert hb using 1 <;> push_cast <;> ring
      calc
        _ ≤ (1250 * ((N : ℝ) + 2 + j + 1) ^ 4) / 2 ^ (j + 1) :=
          div_le_div_of_nonneg_right hb' (by positivity)
        _ = _ := by ring
    _ = _ := hm.tsum_eq

noncomputable def signedWindow (h N L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L,
    ((primeGap0 (N + h + j + 1) : ℝ) - primeGap0 (N + j + 1)) / 2 ^ (j + 1)

/-- Exact split of the complete tail after L terms. -/
theorem realPrimeGapTail_split (N L : ℕ) :
    realPrimeGapTail N =
      (∑ j ∈ Finset.range L, shiftedGapTerm N j) +
        realPrimeGapTail (N + L) / 2 ^ L := by
  have ht : HasSum (fun j => shiftedGapTerm N (j + L))
      (realPrimeGapTail (N + L) / 2 ^ L) := by
    convert (hasSum_shiftedGapTerm (N + L)).div_const ((2 : ℝ) ^ L) using 1
    funext j
    unfold shiftedGapTerm
    rw [show N + (j + L) + 1 = N + L + j + 1 by omega]
    rw [show j + L + 1 = (j + 1) + L by omega, pow_add]
    field_simp
  have hs := (summable_shiftedGapTerm N).sum_add_tsum_nat_add L
  rw [(hasSum_shiftedGapTerm N).tsum_eq, ht.tsum_eq] at hs
  exact hs.symm

/-- No unknown error is discarded: it is the scaled later complete shift. -/
theorem signedWindow_exact_remainder (h N L : ℕ) :
    realTailShift realPrimeGapTail h N - signedWindow h N L =
      realTailShift realPrimeGapTail h (N + L) / 2 ^ L := by
  have hA := realPrimeGapTail_split (N + h) L
  have hB := realPrimeGapTail_split N L
  have hW : signedWindow h N L =
      (∑ j ∈ Finset.range L, shiftedGapTerm (N + h) j) -
      (∑ j ∈ Finset.range L, shiftedGapTerm N j) := by
    simp only [signedWindow, shiftedGapTerm, sub_div, Finset.sum_sub_distrib]
  rw [hW, realTailShift, hA, hB, realTailShift]
  rw [show N + L + h = N + h + L by omega]
  ring

theorem abs_signedWindow_error_le_tail_mass (h N L : ℕ) :
    |realTailShift realPrimeGapTail h N - signedWindow h N L| ≤
      (realPrimeGapTail (N + h + L) + realPrimeGapTail (N + L)) / 2 ^ L := by
  rw [signedWindow_exact_remainder, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ L)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold realTailShift
  rw [show N + L + h = N + h + L by omega]
  calc
    _ ≤ |realPrimeGapTail (N + h + L)| + |realPrimeGapTail (N + L)| := by
      simpa using abs_sub_le (realPrimeGapTail (N + h + L)) 0 (realPrimeGapTail (N + L))
    _ = _ := by rw [abs_of_nonneg (realPrimeGapTail_nonneg _),
      abs_of_nonneg (realPrimeGapTail_nonneg _)]

noncomputable def explicitRemainder (h N L : ℕ) : ℝ :=
  1250 / 2 ^ L * (quarticTailPolynomial ((N : ℝ) + h + L + 2) +
    quarticTailPolynomial ((N : ℝ) + L + 2))

/-- The bound in long-record `res:explicit-remainder`, with EXACT P and 1250. -/
theorem explicit_remainder_bound (h N L : ℕ) :
    |realTailShift realPrimeGapTail h N - signedWindow h N L| ≤
      explicitRemainder h N L := by
  calc
    _ ≤ (realPrimeGapTail (N + h + L) + realPrimeGapTail (N + L)) / 2 ^ L :=
      abs_signedWindow_error_le_tail_mass h N L
    _ ≤ (1250 * quarticTailPolynomial ((N + h + L : ℕ) + (2 : ℝ)) +
      1250 * quarticTailPolynomial ((N + L : ℕ) + (2 : ℝ))) / 2 ^ L := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact add_le_add (realPrimeGapTail_le_quartic _) (realPrimeGapTail_le_quartic _)
    _ = _ := by unfold explicitRemainder; push_cast; ring

/-- Euclidean distance to the complete integer lattice. -/
noncomputable def integerDistance (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ)))

theorem integerDistance_le (x : ℝ) (z : ℤ) : integerDistance x ≤ |x - z| := by
  simpa only [integerDistance, Real.dist_eq] using
    (Metric.infDist_le_dist_of_mem (Set.mem_range_self z) :
      Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ))) ≤ dist x (z : ℝ))

theorem not_realIntegral_of_error_bound {x F E : ℝ}
    (herr : |x - F| ≤ E) (hsep : E < integerDistance F) : ¬ RealIntegral x := by
  rintro ⟨z, rfl⟩
  have hdist := integerDistance_le F z
  rw [abs_sub_comm (z : ℝ) F] at herr
  linarith

/-- Full `res:explicit-remainder`, including BOTH certificate implications. -/
theorem explicit_remainder_certificate (h N L : ℕ) :
    |realTailShift realPrimeGapTail h N - signedWindow h N L| ≤ explicitRemainder h N L ∧
    (|signedWindow h N L| + explicitRemainder h N L < 1 →
      |realTailShift realPrimeGapTail h N| < 1) ∧
    (explicitRemainder h N L < integerDistance (signedWindow h N L) →
      ¬ RealIntegral (realTailShift realPrimeGapTail h N)) := by
  refine ⟨explicit_remainder_bound h N L, ?_, ?_⟩
  · intro hsmall
    have htri : |realTailShift realPrimeGapTail h N| ≤
        |realTailShift realPrimeGapTail h N - signedWindow h N L| + |signedWindow h N L| := by
      simpa using abs_add_le
        (realTailShift realPrimeGapTail h N - signedWindow h N L) (signedWindow h N L)
    linarith [explicit_remainder_bound h N L]
  · exact not_realIntegral_of_error_bound (explicit_remainder_bound h N L)

noncomputable def majorantRemainderTerm (M : ℕ → ℝ) (h N L j : ℕ) : ℝ :=
  (M (N + h + L + j + 1) + M (N + L + j + 1)) / 2 ^ (L + j + 1)

noncomputable def majorantRemainder (M : ℕ → ℝ) (h N L : ℕ) : ℝ :=
  ∑' j : ℕ, majorantRemainderTerm M h N L j

/-- The actual infinite error is bounded by the paper's arbitrary majorant. -/
theorem signedWindow_error_le_majorant (M : ℕ → ℝ)
    (hM : ∀ n, (primeGap0 n : ℝ) ≤ M n) (h N L : ℕ)
    (hsum : Summable (majorantRemainderTerm M h N L)) :
    |realTailShift realPrimeGapTail h N - signedWindow h N L| ≤
      majorantRemainder M h N L := by
  have hmass : HasSum
      (fun j : ℕ => ((primeGap0 (N + h + L + j + 1) : ℝ) +
        primeGap0 (N + L + j + 1)) / 2 ^ (L + j + 1))
      ((realPrimeGapTail (N + h + L) + realPrimeGapTail (N + L)) / 2 ^ L) := by
    convert ((hasSum_shiftedGapTerm (N + h + L)).add
      (hasSum_shiftedGapTerm (N + L))).div_const ((2 : ℝ) ^ L) using 1
    funext j
    unfold shiftedGapTerm
    rw [show L + j + 1 = (j + 1) + L by omega, pow_add]
    field_simp
  calc
    _ ≤ (realPrimeGapTail (N + h + L) + realPrimeGapTail (N + L)) / 2 ^ L :=
      abs_signedWindow_error_le_tail_mass h N L
    _ = ∑' j : ℕ, ((primeGap0 (N + h + L + j + 1) : ℝ) +
        primeGap0 (N + L + j + 1)) / 2 ^ (L + j + 1) := hmass.tsum_eq.symm
    _ ≤ majorantRemainder M h N L := by
      apply hmass.summable.tsum_le_tsum _ hsum
      intro j
      exact div_le_div_of_nonneg_right (add_le_add (hM _) (hM _)) (by positivity)

/-- End-to-end short `res:truncation` and long `xr:truncation`.
The summability is required only at the configurations actually used.
This is weaker as an assumption than convergence at every configuration. -/
theorem cofinal_escape_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (primeGap0 n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (majorantRemainderTerm M h N L) ∧
      majorantRemainder M h N L < integerDistance (signedWindow h N L)) :
    CofinalNonintegralTailShifts realPrimeGapTail := by
  intro h hh N₀
  obtain ⟨N, L, hN, _hL, hsum, hsep⟩ := hsupply h hh N₀
  exact ⟨N, hN, not_realIntegral_of_error_bound
    (signedWindow_error_le_majorant M hM h N L hsum) hsep⟩

/-- The explicitly conditional actual-series endpoint, with no extra bridge. -/
theorem irrational_prime_series_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (primeGap0 n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (majorantRemainderTerm M h N L) ∧
      majorantRemainder M h N L < integerDistance (signedWindow h N L)) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) :=
  irrational_primeSeries_iff_realPrimeGapTail_escape.mpr
    (cofinal_escape_of_finite_truncation M hM hsupply)

end ErdosProblems.Erdos251.PaperR7
