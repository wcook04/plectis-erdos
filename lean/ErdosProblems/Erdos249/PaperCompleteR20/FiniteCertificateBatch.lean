import Erdos249257.CarrySurvivorExtinction
import Erdos249257.DiagonalPincerCertificatesT64
import ErdosProblems.Skip.LadderT67

/-! Whole finite certificate claims, retaining their bounded scope.
Existing residue computations and denominator exclusions are reused.
The index unions verify the manuscript's distinct-value counts. -/
namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257.TotientTailPeriodKiller

/-- The arguments of the totient evaluations in a family of two windows. -/
def certificateWindowIndices (H N L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).biUnion fun h =>
    (Finset.range L).image (fun j => N + 1 + j) ∪
      (Finset.range L).image (fun j => N + h + 1 + j)

theorem certificateWindowIndices_eq (H N L : ℕ) (hH : 0 < H) (hL : 0 < L) :
    certificateWindowIndices H N L = Finset.Icc (N + 1) (N + H + L) := by
  ext k
  simp only [certificateWindowIndices, Finset.mem_biUnion, Finset.mem_Icc,
    Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨h, ⟨hlo, hhi⟩, hx | hx⟩
    · obtain ⟨j, hj, rfl⟩ := hx
      omega
    · obtain ⟨j, hj, rfl⟩ := hx
      omega
  · rintro ⟨hklo, hkhi⟩
    by_cases hk : k ≤ N + L
    · refine ⟨1, by omega, Or.inl ⟨k - (N + 1), by omega, by omega⟩⟩
    · refine ⟨k - (N + L), by omega, Or.inr ⟨L - 1, by omega, by omega⟩⟩

theorem small_certificate_windows :
    certificateWindowIndices 8 12 16 = Finset.Icc 13 36 ∧
      (certificateWindowIndices 8 12 16).card = 24 := by
  rw [certificateWindowIndices_eq 8 12 16 (by decide) (by decide)]
  decide

theorem sixteen_certificate_windows :
    certificateWindowIndices 16 14 9 = Finset.Icc 15 39 ∧
      (certificateWindowIndices 16 14 9).card = 25 := by
  rw [certificateWindowIndices_eq 16 14 9 (by decide) (by decide)]
  decide

theorem small_certificates_and_exclusions :
    (∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16) ∧
    (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 8 → r.den ∣ 2 ^ 12 * (2 ^ h - 1) →
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)) :=
  ⟨certifiedKill_all_small, totient_series_ne_rat_of_den_dvd⟩

theorem sixteen_certificates_and_exclusions :
    (∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9) ∧
    (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 16 → r.den ∣ 2 ^ 14 * (2 ^ h - 1) →
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)) :=
  ⟨certifiedKill_all_upto_sixteen, totient_series_ne_rat_of_den_dvd_upto_sixteen⟩

theorem historical_table_size_and_initial_depths :
    diagonalPincerCertificateScalesThroughT64.length = 28 ∧
    diagonalPincerCertificateScalesThroughT64.Nodup ∧
    diagonalPincerCertificateScalesThroughT64.getLast? = some 64 ∧
    ([1,2,3,4,5,7,8,9,11,13,16,17].map diagonalPincerKillDepthThroughT64) =
      [6,5,7,7,9,14,15,14,21,22,23,26] := by decide

theorem historical_table_and_complete_band :
    (∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t)) ∧
    (∀ t : ℕ, t ≤ 82 → ∃ L, certifiedKill (periodLcm t) (periodLcm t) L) :=
  ⟨certifiedKill_diagonal_all_imported_through_t64,
    ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82⟩

end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.small_certificate_windows
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificate_windows
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.small_certificates_and_exclusions
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificates_and_exclusions
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.historical_table_size_and_initial_depths
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.historical_table_and_complete_band
