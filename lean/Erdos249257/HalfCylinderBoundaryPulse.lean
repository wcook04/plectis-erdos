import Erdos249257.HalfCylinderLargestSkipGap

/-!
# Boundary pulse normalization for the largest-skip crossing

When a largest skipped rank `d` lies beyond two thirds of row `s`, every
strictly larger rank `e < s` is too large to divide either new incidence
index `2*s+1` or `2*s+2`.  Hence the completely filled suffix above `d`
contributes no row pulse.

At the first row where the strict inequality would fail, elementary integer
arithmetic leaves exactly two boundary cases: `3*d = 2*s+1` and
`3*d = 2*s+2`.  The pulse at `d` is respectively two or one.  These facts
are the incidence normalization needed by the remaining producer estimate.
-/

namespace Erdos249257

open HalfCylinderIntegerGreedy
open scoped BigOperators

/-- The Boolean-word pulse is exactly the row-pulse sum over its finite
support. -/
theorem wordPulse_eq_sum_seamWordSupport
    {s : ℕ} (b : SeamRowWord s) :
    wordPulse s b.toNatWord =
      ∑ d ∈ seamWordSupport b, rowPulse s d := by
  classical
  have hfin :
      wordPulse s b.toNatWord =
        ∑ i : Fin (s - 2),
          if b i then rowPulse s ((i : ℕ) + 2) else 0 := by
    unfold wordPulse
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have his : (i : ℕ) + 2 < s := by omega
    simp [SeamRowWord.toNatWord, his]
  rw [hfin]
  unfold seamWordSupport
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
  · intro i hi j hj hij
    apply Fin.ext
    exact Nat.add_right_cancel hij

/-- A strict suffix rank above a late largest skip cannot divide the first
new incidence index. -/
theorem not_dvd_two_mul_add_one_of_late_strictSuffix
    {s d e : ℕ} (hd2 : 2 ≤ d) (hde : d < e) (hes : e < s)
    (hlate : 2 * s < 3 * d) :
    ¬ e ∣ 2 * s + 1 := by
  intro hdiv
  have htwo : e ∣ 2 * e := ⟨2, by omega⟩
  have hrem : e ∣ (2 * s + 1) - 2 * e := Nat.dvd_sub hdiv htwo
  have hpos : 0 < (2 * s + 1) - 2 * e := by omega
  have hle : e ≤ (2 * s + 1) - 2 * e := Nat.le_of_dvd hpos hrem
  omega

/-- A strict suffix rank above a late largest skip cannot divide the second
new incidence index. -/
theorem not_dvd_two_mul_add_two_of_late_strictSuffix
    {s d e : ℕ} (hd2 : 2 ≤ d) (hde : d < e) (hes : e < s)
    (hlate : 2 * s < 3 * d) :
    ¬ e ∣ 2 * s + 2 := by
  intro hdiv
  have htwo : e ∣ 2 * e := ⟨2, by omega⟩
  have hrem : e ∣ (2 * s + 2) - 2 * e := Nat.dvd_sub hdiv htwo
  have hpos : 0 < (2 * s + 2) - 2 * e := by omega
  have hle : e ≤ (2 * s + 2) - 2 * e := Nat.le_of_dvd hpos hrem
  omega

/-- Every filled strict-suffix rank above a late largest skip has zero row
pulse. -/
theorem rowPulse_eq_zero_of_late_strictSuffix
    {s d e : ℕ} (hd2 : 2 ≤ d) (hde : d < e) (hes : e < s)
    (hlate : 2 * s < 3 * d) :
    rowPulse s e = 0 := by
  simp [rowPulse,
    not_dvd_two_mul_add_one_of_late_strictSuffix hd2 hde hes hlate,
    not_dvd_two_mul_add_two_of_late_strictSuffix hd2 hde hes hlate]

/-- For a late largest skipped rank, the filled suffix is pulse-invisible:
the whole word pulse is carried by the lower prefix below `d`. -/
theorem exists_lowerPrefix_wordPulse_eq_of_largestFalse_late
    {s d : ℕ} {b : SeamRowWord s}
    (hmax : IsLargestFalseRank b d) (hlate : 2 * s < 3 * d) :
    ∃ u : Finset ℕ,
      (∀ e ∈ u, 2 ≤ e ∧ e < d) ∧
        seamWordSupport b = u ∪ Finset.Ico (d + 1) s ∧
          wordPulse s b.toNatWord = ∑ e ∈ u, rowPulse s e := by
  classical
  rcases hmax with ⟨hd2, hds, hdnot, hfull⟩
  obtain ⟨u, hu, hsupport⟩ :=
    (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix b hd2 hds).mp
      ⟨hd2, hds, hdnot, hfull⟩
  refine ⟨u, hu, hsupport, ?_⟩
  have hdisjoint : Disjoint u (Finset.Ico (d + 1) s) := by
    apply Finset.disjoint_left.mpr
    intro e heu heinterval
    have heulow := (hu e heu).2
    have hehigh := (Finset.mem_Ico.mp heinterval).1
    omega
  have hsuffix : ∑ e ∈ Finset.Ico (d + 1) s, rowPulse s e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hebounds := Finset.mem_Ico.mp he
    exact rowPulse_eq_zero_of_late_strictSuffix
      hd2 (by omega) hebounds.2 hlate
  rw [wordPulse_eq_sum_seamWordSupport, hsupport,
    Finset.sum_union hdisjoint, hsuffix, add_zero]

/-- At the first crossing of the two-thirds boundary, the boundary incidence
is one of the two consecutive new indices. -/
theorem late_firstCrossing_boundary
    {s d : ℕ} (hlate : 2 * s < 3 * d)
    (hcross : ¬ 2 * (s + 1) < 3 * d) :
    3 * d = 2 * s + 1 ∨ 3 * d = 2 * s + 2 := by
  omega

/-- In the odd boundary case, only `2*s+1` is divisible by `d`, so the
boundary rank contributes pulse two. -/
theorem rowPulse_eq_two_of_boundary_one
    {s d : ℕ} (hd2 : 2 ≤ d) (hboundary : 3 * d = 2 * s + 1) :
    rowPulse s d = 2 := by
  have hone : d ∣ 2 * s + 1 := ⟨3, by omega⟩
  have htwo : ¬ d ∣ 2 * s + 2 := by
    intro hdiv
    have hsub : d ∣ (2 * s + 2) - (2 * s + 1) :=
      Nat.dvd_sub hdiv hone
    have hdle : d ≤ 1 := Nat.le_of_dvd (by omega) (by simpa using hsub)
    omega
  simp [rowPulse, hone, htwo]

/-- In the even boundary case, only `2*s+2` is divisible by `d`, so the
boundary rank contributes pulse one. -/
theorem rowPulse_eq_one_of_boundary_two
    {s d : ℕ} (hd2 : 2 ≤ d) (hboundary : 3 * d = 2 * s + 2) :
    rowPulse s d = 1 := by
  have htwo : d ∣ 2 * s + 2 := ⟨3, by omega⟩
  have hone : ¬ d ∣ 2 * s + 1 := by
    intro hdiv
    have hsub : d ∣ (2 * s + 2) - (2 * s + 1) :=
      Nat.dvd_sub htwo hdiv
    have hdle : d ≤ 1 := Nat.le_of_dvd (by omega) (by simpa using hsub)
    omega
  simp [rowPulse, hone, htwo]

/-- Combined first-crossing pulse dichotomy at the largest skipped rank. -/
theorem rowPulse_boundary_of_late_firstCrossing
    {s d : ℕ} (hd2 : 2 ≤ d) (hlate : 2 * s < 3 * d)
    (hcross : ¬ 2 * (s + 1) < 3 * d) :
    (3 * d = 2 * s + 1 ∧ rowPulse s d = 2) ∨
      (3 * d = 2 * s + 2 ∧ rowPulse s d = 1) := by
  rcases late_firstCrossing_boundary hlate hcross with hone | htwo
  · exact Or.inl ⟨hone, rowPulse_eq_two_of_boundary_one hd2 hone⟩
  · exact Or.inr ⟨htwo, rowPulse_eq_one_of_boundary_two hd2 htwo⟩

#print axioms rowPulse_eq_zero_of_late_strictSuffix
#print axioms exists_lowerPrefix_wordPulse_eq_of_largestFalse_late
#print axioms late_firstCrossing_boundary
#print axioms rowPulse_boundary_of_late_firstCrossing

end Erdos249257
