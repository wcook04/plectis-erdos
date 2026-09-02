import ErdosProblems.Erdos257.FourNinthsQuotientCompactness

/-!
# Exact two-step transport for the totient four-ninths cylinder

This module formalizes the algebraic transport used by the exact even-cylinder audit and
the divisor localization that leaves only one midpoint bit state-dependent.  It consumes
`FourNinthsQuotientCompactness.abs_localMersennePrefixValue_sub_four_ninths_le` as the
downstream finite-row approximation interface.  The remaining producer is still global:
exclude crossing of the one surviving midpoint seam along the reachable cylinder.
-/

namespace ErdosProblems.Erdos257

namespace TotientFourNinthsCylinderTransport

open Erdos257PeriodNoncollapse
open FourNinthsQuotientCompactness
open FourNinthsQuotientDefect
open Filter Set

/-- One binary corridor update with target digit `t`, proper-divisor load `g`, and
appended Boolean digit `b`. -/
def fourNinthsCylinderStep (q t g b : ℤ) : ℤ :=
  2 * q + t - g - b

/-- Two binary rows are one base-four affine update. -/
theorem fourNinthsCylinderStep_two
    (q t₁ g₁ b₁ t₂ g₂ b₂ : ℤ) :
    fourNinthsCylinderStep (fourNinthsCylinderStep q t₁ g₁ b₁)
        t₂ g₂ b₂ =
      4 * q + (2 * (t₁ - g₁) + (t₂ - g₂)) - (2 * b₁ + b₂) := by
  unfold fourNinthsCylinderStep
  ring

/-- **Cylinder transport identity.**  If the old endpoint `q` is encoded by suffix
integer `A-q`, and the appended base-four digit `v` sends it to `q'`, then the new suffix
integer is `(4A+C)-q'`.  Thus the new top is independent of the chosen parent. -/
theorem fourNinthsCylinderSuffix_transport
    {A q C v q' : ℤ} (hq' : q' = 4 * q + C - v) :
    4 * (A - q) + v = (4 * A + C) - q' := by
  rw [hq']
  ring

/-- Pointwise transport of a full endpoint family.  The existence of a parent and a
base-four digit is deliberately explicit: this theorem handles the exact affine geometry,
while the surviving midpoint-seam producer owns fullness of the next family. -/
theorem fourNinthsCylinderFamily_transport
    {A C : ℤ} {parent digit : ℤ → ℤ}
    (htransition : ∀ q' : ℤ,
      q' = 4 * parent q' + C - digit q') :
    ∀ q' : ℤ,
      4 * (A - parent q') + digit q' = (4 * A + C) - q' := by
  intro q'
  exact fourNinthsCylinderSuffix_transport (htransition q')

/-- A proper divisor of an odd integer has co-divisor at least three.  This is the exact
reason every proper divisor of the first row `2m+1` lies below its one-third line. -/
theorem three_mul_le_of_dvd_odd_of_lt
    {N d : ℕ} (hodd : Odd N) (hdpos : 0 < d)
    (hdvd : d ∣ N) (hdlt : d < N) :
    3 * d ≤ N := by
  have hNpos : 0 < N := by
    rcases hodd with ⟨r, hr⟩
    omega
  obtain ⟨q, hq⟩ := hdvd
  have hqpos : 0 < q := by
    by_contra hq0
    have : q = 0 := by omega
    subst q
    have hN0 : N = 0 := by simpa using hq
    omega
  have hqne1 : q ≠ 1 := by
    intro hq1
    subst q
    have hNd : N = d := by simpa using hq
    omega
  have hqodd : Odd q := by
    have hmulodd : Odd (d * q) := by simpa [hq] using hodd
    exact (Nat.odd_mul.mp hmulodd).2
  have hq3 : 3 ≤ q := by
    rcases hqodd with ⟨r, hr⟩
    omega
  calc
    3 * d ≤ q * d := Nat.mul_le_mul_right d hq3
    _ = N := by simpa [Nat.mul_comm] using hq.symm

/-- At the second row `2(m+1)`, every proper divisor above the one-third line is exactly
the midpoint `m+1`.  Hence after the earlier prefix is fixed, this is the sole possible
state-dependent divisor load. -/
theorem eq_midpoint_of_dvd_two_mul_of_above_third
    {m d : ℕ} (hdpos : 0 < d)
    (hdvd : d ∣ 2 * (m + 1)) (hdlt : d < 2 * (m + 1))
    (habove : 2 * (m + 1) < 3 * d) :
    d = m + 1 := by
  obtain ⟨q, hq⟩ := hdvd
  have hqpos : 0 < q := by
    by_contra hq0
    have : q = 0 := by omega
    subst q
    simp at hq
  have hqge2 : 2 ≤ q := by
    by_contra hq2
    have hq1 : q = 1 := by omega
    subst q
    have hNd : 2 * (m + 1) = d := by simpa using hq
    omega
  have hqlt3 : q < 3 := by
    apply (Nat.mul_lt_mul_left hdpos).mp
    calc
      d * q = 2 * (m + 1) := hq.symm
      _ < 3 * d := habove
      _ = d * 3 := by omega
  have hq2 : q = 2 := by omega
  subst q
  omega

/-- Every positive proper divisor needed by the odd row `2m+1` is already contained in
the prefix through rank `m`. -/
theorem properDivisor_two_mul_add_one_le_midpoint
    {m d : ℕ} (hdpos : 0 < d)
    (hdvd : d ∣ 2 * m + 1) (hdlt : d < 2 * m + 1) :
    d ≤ m := by
  have hodd : Odd (2 * m + 1) := ⟨m, by omega⟩
  have hthird := three_mul_le_of_dvd_odd_of_lt hodd hdpos hdvd hdlt
  omega

/-- **Midpoint-only divisor localization.**  For `m≥2`, a positive proper divisor of
the even row `2m+2` either belongs to the already fixed prefix through `m`, or is the
single midpoint rank `m+1`.  This deletes every other state-dependent load case in the
two-step cylinder transport. -/
theorem properDivisor_two_mul_add_two_le_midpoint_or_eq
    {m d : ℕ} (hm : 2 ≤ m) (hdpos : 0 < d)
    (hdvd : d ∣ 2 * m + 2) (hdlt : d < 2 * m + 2) :
    d ≤ m ∨ d = m + 1 := by
  have hrewrite : 2 * m + 2 = 2 * (m + 1) := by omega
  rw [hrewrite] at hdvd hdlt
  by_cases habove : 2 * (m + 1) < 3 * d
  · exact Or.inr
      (eq_midpoint_of_dvd_two_mul_of_above_third hdpos hdvd hdlt habove)
  · left
    have hthird : 3 * d ≤ 2 * (m + 1) := by omega
    omega

/-- Two endpoint words that agree through rank `m` necessarily give the same bit at
every proper divisor of `2m+2` except the midpoint.  This is the pointwise load statement
used by the compressed cylinder recurrence. -/
theorem endpointBits_eq_at_evenProperDivisor_ne_midpoint
    {m d : ℕ} (hm : 2 ≤ m) {b c : ℕ → ℕ}
    (hprefix : ∀ a : ℕ, a ≤ m → b a = c a)
    (hdpos : 0 < d) (hdvd : d ∣ 2 * m + 2) (hdlt : d < 2 * m + 2)
    (hne : d ≠ m + 1) :
    b d = c d := by
  rcases properDivisor_two_mul_add_two_le_midpoint_or_eq hm hdpos hdvd hdlt with
    hdle | hdeq
  · exact hprefix d hdle
  · exact (hne hdeq).elim

/-- On the odd row even the midpoint exception disappears. -/
theorem endpointBits_eq_at_oddProperDivisor
    {m d : ℕ} {b c : ℕ → ℕ}
    (hprefix : ∀ a : ℕ, a ≤ m → b a = c a)
    (hdpos : 0 < d) (hdvd : d ∣ 2 * m + 1) (hdlt : d < 2 * m + 1) :
    b d = c d := by
  exact hprefix d
    (properDivisor_two_mul_add_one_le_midpoint hdpos hdvd hdlt)

/-! ## The exact suffix-width seam consumer -/

/-- If an even-rank cylinder at rank `2m` has suffix width at most `m-1`, then its
common prefix reaches through the exceptional midpoint rank `m+1`.  This is the exact
arithmetic implication needed by the seam argument. -/
theorem midpoint_le_commonPrefix_of_suffixWidth_le
    {m L : ℕ} (hm : 1 ≤ m) (hL : L ≤ m - 1) :
    m + 1 ≤ 2 * m - L := by
  omega

/-- A suffix-width estimate `L≤m-1` removes the final midpoint exception: two endpoint
words with common prefix of length `2m-L` agree at every positive proper divisor of the
next even row `2m+2`. -/
theorem endpointBits_eq_at_evenProperDivisor_of_suffixWidth_le
    {m L d : ℕ} (hm : 2 ≤ m) (hL : L ≤ m - 1) {b c : ℕ → ℕ}
    (hprefix : ∀ a : ℕ, a ≤ 2 * m - L → b a = c a)
    (hdpos : 0 < d) (hdvd : d ∣ 2 * m + 2) (hdlt : d < 2 * m + 2) :
    b d = c d := by
  rcases properDivisor_two_mul_add_two_le_midpoint_or_eq hm hdpos hdvd hdlt with
    hdle | hdeq
  · apply hprefix d
    have hmid : m + 1 ≤ 2 * m - L :=
      midpoint_le_commonPrefix_of_suffixWidth_le (by omega) hL
    omega
  · subst d
    exact hprefix (m + 1)
      (midpoint_le_commonPrefix_of_suffixWidth_le (by omega) hL)

/-- The next odd row is automatically covered by the same common-prefix estimate. -/
theorem endpointBits_eq_at_oddProperDivisor_of_suffixWidth_le
    {m L d : ℕ} (hm : 2 ≤ m) (hL : L ≤ m - 1) {b c : ℕ → ℕ}
    (hprefix : ∀ a : ℕ, a ≤ 2 * m - L → b a = c a)
    (hdpos : 0 < d) (hdvd : d ∣ 2 * m + 1) (hdlt : d < 2 * m + 1) :
    b d = c d := by
  apply hprefix d
  have hdle : d ≤ m :=
    properDivisor_two_mul_add_one_le_midpoint hdpos hdvd hdlt
  have hmid : m + 1 ≤ 2 * m - L :=
    midpoint_le_commonPrefix_of_suffixWidth_le (by omega) hL
  omega

/-! ## Endpoint-zero compactness consumer -/

/-- The finite product expected from a full even cylinder: at every depth there is one
Boolean quotient row with exact endpoint defect zero.  No nesting assumption is needed. -/
def FourNinthsEvenZeroQuotientSupply : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∃ D : Finset ℕ,
      (∀ a ∈ D, 2 ≤ a ∧ a ≤ d) ∧
      localPrefixQuotient D (2 * d) = fourNinthsQuotientTarget d

/-- An endpoint-zero row has only its fractional mass and target fraction left in the
scaled error. -/
theorem abs_localMersennePrefixValue_sub_four_ninths_le_of_endpoint_zero
    {D : Finset ℕ} {d : ℕ}
    (hD : ∀ a ∈ D, 2 ≤ a)
    (hzero : localPrefixQuotient D (2 * d) = fourNinthsQuotientTarget d) :
    |((localMersennePrefixValue D : ℚ) : ℝ) - (4 : ℝ) / 9| ≤
      ((D.card + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * d) := by
  have h := abs_localMersennePrefixValue_sub_four_ninths_le hD hzero.le
  rw [hzero] at h
  simpa using h

/-- Exact endpoint zero at every even depth already constructs `4/9` by closedness of
the Mersenne achievement set.  The rows may vary arbitrarily with depth; the cylinder's
common-prefix coherence is stronger than this compactness consumer requires. -/
theorem four_ninths_mem_mersenneAchievementSet_of_evenZeroQuotientSupply
    (hsupply : FourNinthsEvenZeroQuotientSupply) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet := by
  classical
  let D : ℕ → Finset ℕ := fun n ↦ (hsupply (n + 2) (by omega)).choose
  have hD (n : ℕ) : ∀ a ∈ D n, 2 ≤ a ∧ a ≤ n + 2 :=
    (hsupply (n + 2) (by omega)).choose_spec.1
  have hzero (n : ℕ) :
      localPrefixQuotient (D n) (2 * (n + 2)) =
        fourNinthsQuotientTarget (n + 2) :=
    (hsupply (n + 2) (by omega)).choose_spec.2
  let y : ℕ → ℝ := fun n ↦ ((localMersennePrefixValue (D n) : ℚ) : ℝ)
  have hdist : Tendsto (fun n : ℕ ↦ dist (y n) (4 / 9 : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ ↦ dist_nonneg)
      (Filter.Eventually.of_forall fun n ↦ ?_)
      (tendsto_twentyOne_evenQuotientWindow_error.comp
        (by simpa [Nat.add_comm] using tendsto_add_atTop_nat 2))
    rw [Real.dist_eq]
    calc
      |y n - (4 / 9 : ℝ)| ≤
          (((D n).card + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * (n + 2)) := by
        exact abs_localMersennePrefixValue_sub_four_ninths_le_of_endpoint_zero
          (fun a ha ↦ (hD n a ha).1) (hzero n)
      _ ≤
          (((2 ^ (n + 2) + (2 * (n + 2) + 1) : ℕ) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * (n + 2)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hcard : (D n).card ≤ n + 3 := by
          have hsubset : D n ⊆ Finset.range (n + 3) := by
            intro a ha
            exact Finset.mem_range.mpr (by have := (hD n a ha).2; omega)
          simpa using Finset.card_le_card hsubset
        exact_mod_cast (calc
          (D n).card + 1 ≤ n + 4 := by omega
          _ ≤ 2 ^ (n + 2) + (2 * (n + 2) + 1) := by
            have hp : 0 ≤ 2 ^ (n + 2) := Nat.zero_le _
            omega)
  have hy : Tendsto y atTop (nhds (4 / 9 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hyMem : ∀ n : ℕ, y n ∈ mersenneAchievementSet := by
    intro n
    let A : Set ℕ := ↑(D n)
    have hA0 : 0 ∉ A := by
      intro hzeroA
      have hbounds := hD n 0 (by simpa [A] using hzeroA)
      omega
    refine ⟨A, hA0, ?_⟩
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [y, localMersennePrefixValue_eq_finiteErdosSum]
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

#print axioms fourNinthsCylinderStep_two
#print axioms fourNinthsCylinderSuffix_transport
#print axioms fourNinthsCylinderFamily_transport
#print axioms three_mul_le_of_dvd_odd_of_lt
#print axioms eq_midpoint_of_dvd_two_mul_of_above_third
#print axioms properDivisor_two_mul_add_one_le_midpoint
#print axioms properDivisor_two_mul_add_two_le_midpoint_or_eq
#print axioms endpointBits_eq_at_evenProperDivisor_ne_midpoint
#print axioms endpointBits_eq_at_oddProperDivisor
#print axioms midpoint_le_commonPrefix_of_suffixWidth_le
#print axioms endpointBits_eq_at_evenProperDivisor_of_suffixWidth_le
#print axioms endpointBits_eq_at_oddProperDivisor_of_suffixWidth_le
#print axioms abs_localMersennePrefixValue_sub_four_ninths_le_of_endpoint_zero
#print axioms four_ninths_mem_mersenneAchievementSet_of_evenZeroQuotientSupply

end TotientFourNinthsCylinderTransport

end ErdosProblems.Erdos257
