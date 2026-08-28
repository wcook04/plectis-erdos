import ErdosProblems.Erdos1041.ConnectedClusterBergman
import Mathlib.Tactic

/-!
# Erdős #1041: fixed-level area forcing across connected clusters

The analytic companion applies the connected-cluster Bergman certificate to
all multi-root components of one regular lemniscate level.  Their normalized
areas sum to at most one.  This module checks the finite pigeonhole kernel and
its exact composition with
`ConnectedClusterBergman.length_le_two_of_cluster_certificate`.

It does not prove that the reciprocal-barrier sum is always at least one, and
it does not assert unrestricted Erdős #1041.
-/

namespace ErdosProblems.Erdos1041.ConnectedClusterAreaForcing

/-- If nonnegative normalized component areas have total at most one, while
the reciprocal Bergman barriers have total at least one, some component meets
its area-times-barrier certificate. -/
theorem exists_cluster_certificate_of_area_sum
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (areaFactor logarithmicFactor : ι → ℝ)
    (hfactorPos : ∀ i, 0 < logarithmicFactor i)
    (hareaSum : ∑ i, areaFactor i ≤ 1)
    (hreciprocalSum : 1 ≤ ∑ i, 2 / logarithmicFactor i) :
    ∃ i, areaFactor i * logarithmicFactor i ≤ 2 := by
  by_contra hnone
  push Not at hnone
  have hterm : ∀ i, 2 / logarithmicFactor i < areaFactor i := fun i => by
    apply (div_lt_iff₀ (hfactorPos i)).2
    simpa [mul_comm] using hnone i
  have hsumlt :
      (∑ i, 2 / logarithmicFactor i) < ∑ i, areaFactor i := by
    apply Finset.sum_lt_sum (fun i _ => le_of_lt (hterm i))
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Finset.mem_univ i, hterm i⟩
  linarith

/-- Direct composition with the landed connected-cluster geodesic consumer:
the fixed-level reciprocal-barrier forcing condition produces one curve of
normalized length at most two. -/
theorem exists_length_le_two_of_area_forcing
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (length areaFactor logarithmicFactor : ι → ℝ)
    (hfactorPos : ∀ i, 0 < logarithmicFactor i)
    (hareaSum : ∑ i, areaFactor i ≤ 1)
    (hreciprocalSum : 1 ≤ ∑ i, 2 / logarithmicFactor i)
    (hgeodesic : ∀ i,
      (length i) ^ 2 ≤ 2 * areaFactor i * logarithmicFactor i) :
    ∃ i, length i ≤ 2 := by
  obtain ⟨i, hi⟩ := exists_cluster_certificate_of_area_sum
    areaFactor logarithmicFactor hfactorPos hareaSum hreciprocalSum
  exact ⟨i,
    ConnectedClusterBergman.length_le_two_of_cluster_certificate
      (hgeodesic i) hi⟩

/-- A strict area-times-barrier certificate gives strict normalized length. -/
theorem length_lt_two_of_strict_cluster_certificate
    {length areaFactor logarithmicFactor : ℝ}
    (hgeodesic : length ^ 2 ≤ 2 * areaFactor * logarithmicFactor)
    (hcertificate : areaFactor * logarithmicFactor < 2) :
    length < 2 := by
  have hsquare : length ^ 2 < 4 := by nlinarith
  by_contra hnot
  have hge : 2 ≤ length := le_of_not_gt hnot
  nlinarith [sq_nonneg (length - 2)]

end ErdosProblems.Erdos1041.ConnectedClusterAreaForcing
