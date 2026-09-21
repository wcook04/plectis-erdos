import Erdos249257.TotientTailCarryPeriod
import ErdosProblems.Erdos249.ParityPerturbedRationalControl

/-! Paper-form restatements of the long-paper block on dyadic totient sections
and the carry rank that rationality would force:

* the retained dyadic sections form a basis of all sections through level `e`,
  of dimension `2^e+1`, while the *complete* level-zero truncation consists
  only of `φ` and has dimension one;
* the canonical family `{φ(n), φ(2n)} ∪ {φ(2^j n + r) : 1 ≤ j ≤ e, 0 < r < 2^j,
  r odd}` is `ℚ`-linearly independent, has `2^e+1` members and spans the
  sections through level `e`;
* if `S ∈ ℚ`, choosing `v > 0` with `vS ∈ ℤ` and setting `u_N = v R_N` gives an
  integer sequence with `u_{N+1} = 2u_N - vφ(N+1)`, `0 ≤ u_N ≤ v(N+2)`, whose
  dyadic carry sections have rank at least `2^e-1` at every level;
* the generic proposal that a rational coefficient series has bounded
  tempered-carry rank is false: the `5/4` control has a tempered orbit whose
  carry sections are eventually periodic modulo the multiplier and still have
  rank at least `2^e-1` at every level.

Here `R_N = totientTail N` and `Φ_N = totientPrefix N`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.ParityPerturbedRationalControl

/-! ### The canonical family, its cardinality, and its span -/

/-- The canonical family is exactly the paper's list: `φ(n)`, `φ(2n)`, and the
odd-residue sections `n ↦ φ(2^{j+1} n + (2r+1))` with `1 ≤ j+1 ≤ e` and
`0 < 2r+1 < 2^{j+1}`. -/
theorem canonicalTotientKernelFamily_entries (e : ℕ) :
    canonicalTotientKernelFamily e (Sum.inl 0) = (fun n => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily e (Sum.inl 1)
        = (fun n => (Nat.totient (2 * n) : ℚ)) ∧
      ∀ (j : Fin e) (r : Fin (2 ^ j.val)),
        canonicalTotientKernelFamily e (Sum.inr ⟨j, r⟩)
          = fun n => (Nat.totient (2 ^ (j.val + 1) * n + (2 * r.val + 1)) : ℚ) := by
  refine ⟨?_, ?_, ?_⟩
  · funext n
    simp [canonicalTotientKernelFamily, totientKernelSeq]
  · funext n
    simp [canonicalTotientKernelFamily, totientKernelSeq]
  · intro j r
    funext n
    simp [canonicalTotientKernelFamily, totientKernelSeq]

/-- **Exact dyadic rank and infinite-dimensionality.**  For every `e ≥ 1` the
canonical family is `ℚ`-linearly independent, contains `2^e+1` sequences, and
spans the complete truncation through level `e`; consequently the span of all
dyadic sections is not finite-dimensional. -/
theorem canonicalTotientKernelFamily_independent_card_and_span (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Function.Injective (canonicalTotientKernelFamily e) ∧
      Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 ∧
      Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))
        = Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) ∧
      ¬ FiniteDimensional ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)) :=
  ⟨linearIndependent_canonicalTotientKernelFamily e,
    (linearIndependent_canonicalTotientKernelFamily e).injective,
    card_totientCanonicalIndex e,
    span_totientKernelThroughLevelFamily_eq_canonical e he,
    not_finiteDimensional_span_fullTotientKernel⟩

/-! ### The retained sections are a basis of the truncation -/

/-- The retained (canonical) sections, transported along the equality of spans,
as a basis of the complete truncation through level `e ≥ 1`. -/
noncomputable def retainedSectionBasis (e : ℕ) (he : 1 ≤ e) :
    Module.Basis (TotientCanonicalIndex e) ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) :=
  (Module.Basis.span (linearIndependent_canonicalTotientKernelFamily e)).map
    (LinearEquiv.ofEq _ _ (span_totientKernelThroughLevelFamily_eq_canonical e he).symm)

/-- **The retained dyadic totient sections form a basis for all sections
through level `e`, of dimension `2^e+1`.** -/
theorem retainedSections_basis_and_rank (e : ℕ) (he : 1 ≤ e) :
    (∃ b : Module.Basis (TotientCanonicalIndex e) ℚ
        (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))),
        ∀ i, (b i : ℕ → ℚ) = canonicalTotientKernelFamily e i) ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
        = 2 ^ e + 1 := by
  refine ⟨⟨retainedSectionBasis e he, ?_⟩, finrank_totientKernelThroughLevelFamily_eq e he⟩
  intro i
  simp only [retainedSectionBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply]

/-- **The complete level-zero truncation consists only of `φ` and has
dimension one.** -/
theorem completeLevelZeroTruncation_is_totient_and_rank_one :
    Set.range (totientKernelThroughLevelFamily 0) = {fun n => (Nat.totient n : ℚ)} ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1 := by
  have hrange :
      Set.range (totientKernelThroughLevelFamily 0) = {fun n => (Nat.totient n : ℚ)} := by
    ext f
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨⟨j, hj⟩, ⟨r, hr⟩⟩, rfl⟩
      have hj0 : j = 0 := by omega
      subst hj0
      have hr0 : r = 0 := by
        have hr' : r < 1 := by simpa using hr
        omega
      subst hr0
      funext n
      simp [totientKernelThroughLevelFamily, totientKernelSeq]
    · rintro rfl
      refine ⟨⟨⟨0, by omega⟩, ⟨0, by norm_num⟩⟩, ?_⟩
      funext n
      simp [totientKernelThroughLevelFamily, totientKernelSeq]
  refine ⟨hrange, ?_⟩
  rw [hrange]
  have hne : (fun n => (Nat.totient n : ℚ)) ≠ 0 := by
    intro hzero
    have h1 := congrFun hzero 1
    simp at h1
  exact finrank_span_singleton hne

/-! ### The integral carry supplied by rationality -/

/-- **The carry orbit of a rational value.**  If `v > 0` and `vS = p ∈ ℤ`, then
`u_N = v R_N` is an integer sequence, `u_{N+1} = 2u_N - vφ(N+1)`,
`0 ≤ u_N ≤ v(N+2)`, and for every `e` the retained carry sections through level
`e` span a `ℚ`-space of dimension at least `2^e - 1`. -/
theorem rationalValue_integral_carry_and_rank_floor
    {v : ℕ} (hv : 0 < v) {p : ℤ}
    (hvS : (v : ℝ) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (p : ℝ)) :
    ∃ u : ℕ → ℤ,
      (∀ N : ℕ, (u N : ℝ) = (v : ℝ) * totientTail N) ∧
      (∀ N : ℕ, u (N + 1) = 2 * u N - (v : ℤ) * (Nat.totient (N + 1) : ℤ)) ∧
      (∀ N : ℕ, 0 ≤ u N ∧ u N ≤ (v : ℤ) * ((N : ℤ) + 2)) ∧
      (∀ e : ℕ, 2 ^ e - 1 ≤
        Module.finrank ℚ
          (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) := by
  classical
  set u : ℕ → ℤ := fun N => 2 ^ N * p - (v : ℤ) * (totientPrefix N : ℤ) with hu
  have hval : ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * totientTail N := by
    intro N
    have hsplit := two_pow_mul_totient_series_eq N
    have h2 : (2 : ℝ) ^ N * (p : ℝ)
        = (v : ℝ) * ((totientPrefix N : ℝ) + totientTail N) := by
      rw [← hsplit, ← hvS]; ring
    have hcast : (u N : ℝ)
        = (2 : ℝ) ^ N * (p : ℝ) - (v : ℝ) * (totientPrefix N : ℝ) := by
      simp only [hu]; push_cast; ring
    rw [hcast, h2]; ring
  have hrec : ∀ N : ℕ, u (N + 1) = 2 * u N - (v : ℤ) * (Nat.totient (N + 1) : ℤ) := by
    intro N
    have h1 := hval (N + 1)
    have h2 := hval N
    have hsucc := totientTail_succ N
    have hR : ((u (N + 1) : ℤ) : ℝ)
        = ((2 * u N - (v : ℤ) * (Nat.totient (N + 1) : ℤ) : ℤ) : ℝ) := by
      push_cast
      rw [h1, h2, hsucc]
      ring
    exact_mod_cast hR
  have hbound : ∀ N : ℕ, 0 ≤ u N ∧ u N ≤ (v : ℤ) * ((N : ℤ) + 2) := by
    intro N
    have hpos := totientTail_pos N
    have hle := totientTail_le N
    have hvR : (0 : ℝ) ≤ (v : ℝ) := by positivity
    have h1 : (0 : ℝ) ≤ ((u N : ℤ) : ℝ) := by
      rw [hval N]; nlinarith
    have h2 : ((u N : ℤ) : ℝ) ≤ (((v : ℤ) * ((N : ℤ) + 2) : ℤ) : ℝ) := by
      rw [hval N]; push_cast; nlinarith
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have htemp :
      Filter.Tendsto (fun N : ℕ => (u N : ℝ) / (2 : ℝ) ^ N) Filter.atTop (nhds 0) := by
    have h0 := binaryCoeffTail_div_pow_tendsto_zero Nat.totient Nat.totient_le
    have h1 : Filter.Tendsto
        (fun N : ℕ => (v : ℝ) * (binaryCoeffTail Nat.totient N / (2 : ℝ) ^ N))
        Filter.atTop (nhds 0) := by
      simpa using h0.const_mul (v : ℝ)
    refine h1.congr ?_
    intro N
    rw [binaryCoeffTail_totient_eq, hval N]
    ring
  have horbit : IsTemperedBinaryOrbit Nat.totient v u := by
    refine ⟨?_, htemp⟩
    intro N
    rw [hrec N]
    push_cast
    ring
  exact ⟨u, hval, hrec, hbound, fun e => finrank_canonicalCarryKernel_ge hv horbit e⟩

/-! ### Rationality alone does not bound the carry rank -/

/-- An integral tail displacement is a carry displacement divisible by the
multiplier, for any tempered orbit. -/
theorem multiplier_dvd_carryShift_of_tailDiff_int
    {c : ℕ → ℕ} (hgrowth : ∀ n, c n ≤ n) {v : ℕ} {u : ℕ → ℤ}
    (horbit : IsTemperedBinaryOrbit c v u) {N k : ℕ} {z : ℤ}
    (hz : binaryCoeffTail c (N + k) - binaryCoeffTail c N = (z : ℝ)) :
    (v : ℤ) ∣ u (N + k) - u N := by
  have h1 := temperedBinaryOrbit_eq_scaledTail c hgrowth horbit (N + k)
  have h2 := temperedBinaryOrbit_eq_scaledTail c hgrowth horbit N
  refine ⟨z, ?_⟩
  have hR : ((u (N + k) - u N : ℤ) : ℝ) = (((v : ℤ) * z : ℤ) : ℝ) := by
    push_cast
    rw [h1, h2, ← hz]
    ring
  exact_mod_cast hR

/-- The explicit integer shift `2^N X_c = z + T_c(N)`. -/
theorem exists_int_prefix_shift (c : ℕ → ℕ) (hgrowth : ∀ n, c n ≤ n) (N : ℕ) :
    ∃ z : ℤ, (2 : ℝ) ^ N * binaryCoeffSeries c = (z : ℝ) + binaryCoeffTail c N := by
  obtain ⟨z, hz⟩ := bpow_mul_coeff_series_eq_int_add_tail 2 N c (by norm_num) hgrowth
  exact ⟨z, by simpa [binaryCoeffSeries, binaryCoeffTail] using hz⟩

/-- For the `5/4` control the two-step tail displacement is an integer from
`N = 2` on. -/
theorem control_tailDiff_int {N : ℕ} (hN : 2 ≤ N) :
    ∃ z : ℤ, binaryCoeffTail control (N + 2) - binaryCoeffTail control N = (z : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
  obtain ⟨z1, hz1⟩ := exists_int_prefix_shift control control_le (m + 2 + 2)
  obtain ⟨z2, hz2⟩ := exists_int_prefix_shift control control_le (m + 2)
  rw [control_series] at hz1 hz2
  refine ⟨15 * 2 ^ m - z1 + z2, ?_⟩
  have e1 : (2 : ℝ) ^ (m + 2 + 2) * (5 / 4) = 20 * 2 ^ m := by ring
  have e2 : (2 : ℝ) ^ (m + 2) * (5 / 4) = 5 * 2 ^ m := by ring
  rw [e1] at hz1
  rw [e2] at hz2
  push_cast
  linarith

/-- **A rational coefficient series can have unbounded tempered-carry rank.**
The `5/4` control has a tempered integral carry whose dyadic sections are
uniformly eventually periodic modulo the multiplier from index `2` on, with
period `2`, and whose canonical carry sections nevertheless have `ℚ`-rank at
least `2^e - 1` at every level.  So quotient periodicity does not bound the
rational span, and no general bounded-rank lemma for rational coefficient
series is available. -/
theorem rationalControl_periodic_with_unbounded_carry_rank :
    ∃ c : ℕ → ℕ, (∀ n, c n ≤ n) ∧ binaryCoeffSeries c = 5 / 4 ∧
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit c v u ∧
          CarrySectionsEventuallyPeriodicMod v 2 2 u ∧
          ∀ e : ℕ, 2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  obtain ⟨v, hv, u, hu, hrank⟩ := control_temperedOrbit_carryRank_unbounded
  refine ⟨control, control_le, control_series, v, hv, u, hu, ?_, hrank⟩
  apply carrySectionsEventuallyPeriodicMod_of_shift_dvd
  intro N hN
  obtain ⟨z, hz⟩ := control_tailDiff_int hN
  exact multiplier_dvd_carryShift_of_tailDiff_int control_le hu hz

/-- **The conditional theorem recorded in the totient tail carry period
source.**  Rationality of `S` supplies one carry that is uniformly eventually
periodic modulo `v` and has unbounded rational section rank. -/
theorem rationality_gives_mod_period_and_unbounded_rank
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ, 2 ^ e - 1 ≤
          Module.finrank ℚ
            (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := by
  refine not_irrational_totientSeries_implies_mod_period_and_unbounded_rank ?_
  rwa [binaryCoeffSeries_totient_eq]

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_entries
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_independent_card_and_span
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.retainedSections_basis_and_rank
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.completeLevelZeroTruncation_is_totient_and_rank_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.rationalValue_integral_carry_and_rank_floor
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.multiplier_dvd_carryShift_of_tailDiff_int
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_int_prefix_shift
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.control_tailDiff_int
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.rationalControl_periodic_with_unbounded_carry_rank
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.rationality_gives_mod_period_and_unbounded_rank
