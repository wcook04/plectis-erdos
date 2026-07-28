import ErdosProblems.Lift.AngleA1
import Erdos249257.LcmConeFlatness

open Erdos249257 Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Lift.AngleA1

-- Axiom footprints of every public theorem in AngleA1.lean
#print axioms ErdosProblems.Lift.AngleA1.coeffDiscrepancy_congr
#print axioms ErdosProblems.Lift.AngleA1.coeffDiscrepancy_update
#print axioms ErdosProblems.Lift.AngleA1.coeffDiscrepancy_update_not_dvd
#print axioms ErdosProblems.Lift.AngleA1.totient_gcd_dvd_window
#print axioms ErdosProblems.Lift.AngleA1.totient_gcd_dvd_windowCoeff
#print axioms ErdosProblems.Lift.AngleA1.totient_gcd_dvd_diagCoeff
#print axioms ErdosProblems.Lift.AngleA1.sixteen_dvd_diagCoeff_offset_seventeen
#print axioms ErdosProblems.Lift.AngleA1.scaleFree_bit_ceiling
#print axioms ErdosProblems.Lift.AngleA1.two_pow_supplyBits_le
#print axioms ErdosProblems.Lift.AngleA1.supplyBits_le_six
#print axioms ErdosProblems.Lift.AngleA1.frontier_demand
#print axioms ErdosProblems.Lift.AngleA1.frontier_supply_ledger
#print axioms ErdosProblems.Lift.AngleA1.irrational_totient_series_of_lcm_base_supply
#print axioms ErdosProblems.Lift.AngleA1.base_depth_floor
#print axioms ErdosProblems.Lift.AngleA1.periodLcm_67_val
#print axioms ErdosProblems.Lift.AngleA1.base_depth_floor_at_67
#print axioms ErdosProblems.Lift.AngleA1.base_depth_97_is_admissible
#print axioms ErdosProblems.Lift.AngleA1.base_margin_98_beats_diagonal_98
#print axioms ErdosProblems.Lift.AngleA1.exists_baseKill_le_ten
#print axioms ErdosProblems.Lift.AngleA1.constant_model_never_kills
#print axioms ErdosProblems.Lift.AngleA1.identity_model_never_kills
#print axioms ErdosProblems.Lift.AngleA1.tail_diff_int_scale_up
#print axioms ErdosProblems.Lift.AngleA1.exists_certifiedKill_of_tail_diff_notMem_int
#print axioms ErdosProblems.Lift.AngleA1.exists_certifiedKill_diagonal_iff
#print axioms ErdosProblems.Lift.AngleA1.exists_certifiedKill_descends
#print axioms ErdosProblems.Lift.AngleA1.diagonal_certified_downward_closed
#print axioms ErdosProblems.Lift.AngleA1.frontier_certificate_implies_all_seed
#print axioms ErdosProblems.Lift.AngleA1.irrational_iff_all_diagonal_certified
#print axioms ErdosProblems.Lift.AngleA1.periodLcm_dvd_of_le

-- Exact statements, unfolded, for reading
#check @ErdosProblems.Lift.AngleA1.irrational_totient_series_of_lcm_base_supply
#check @ErdosProblems.Lift.AngleA1.exists_certifiedKill_descends
#check @ErdosProblems.Lift.AngleA1.irrational_iff_all_diagonal_certified
#check @ErdosProblems.Lift.AngleA1.frontier_supply_ledger
#check @ErdosProblems.Lift.AngleA1.constant_model_never_kills

-- Independent probe A: is there any theorem in this file whose hypothesis is a
-- certificate at a HIGHER scale being used to get one at a LOWER scale?  (yes:
-- that is the whole of Part 4).  Confirm the direction by instantiating.
example (L : ℕ) (h : certifiedKill (periodLcm 67) (periodLcm 67) L) :
    ∃ L', certifiedKill (periodLcm 66) (periodLcm 66) L' :=
  frontier_certificate_implies_all_seed h 66 (by norm_num)

-- Independent probe B: the RHS of irrational_iff_all_diagonal_certified is
-- literally the open supply hypothesis, i.e. the iff is a restatement of #249,
-- not a reduction of it.
example : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) →
    ∀ t : ℕ, ∃ L, certifiedKill (periodLcm t) (periodLcm t) L :=
  irrational_iff_all_diagonal_certified.mp

-- Independent probe C: the "demand" theorem is pure arithmetic on Icc 1 98 with
-- no reference to certifiedKill, the totient, periodLcm, or any window.
example : ∑ d ∈ Finset.Icc 1 98, d = 4851 := frontier_demand

-- Independent probe D: frontier_supply_ledger is 98 * 6 and holds for ANY h,
-- including h = 0, where supplyBits 0 m = (φ m).factorization 2 has nothing to
-- do with any certificate.
example : ∑ d ∈ Finset.Icc 1 98, supplyBits 0 d ≤ 588 := frontier_supply_ledger 0

-- Independent probe E: the "2433x margin" is an artefact of comparing at the
-- diagonal's own depth floor.  One extra bit of depth erases it entirely:
-- the diagonal arc at depth 99 is already more than half of 2^99.
example :
    (2 : ℤ) ^ 99 - 2 * ((periodLcm 67 : ℤ) + (periodLcm 67 : ℤ) + 99 + 2)
      > (2 : ℤ) ^ 98 := by
  rw [periodLcm_67_val]; norm_num

-- Independent probe F: a single-coefficient perturbation by 2^(j) destroys the
-- RESIDUE mod 2^L (coeffDiscrepancy_update_not_dvd) but need NOT destroy ARC
-- MEMBERSHIP, which is what certifiedKill actually asserts.  At the base cell
-- t = 67 and depth L = 110, both r = 2^108 and (r + 2^109) mod 2^110 lie in the
-- admissible arc, so the "no fewer than j+1 bits" necessity claim is a claim
-- about pinning the residue, not about certifying.
example :
    ((67 : ℤ) + (periodLcm 67 : ℤ) + 110 + 2) < 2 ^ 108 ∧
    (2 : ℤ) ^ 108 < 2 ^ 110 - ((67 : ℤ) + (periodLcm 67 : ℤ) + 110 + 2) ∧
    ((67 : ℤ) + (periodLcm 67 : ℤ) + 110 + 2) < ((2 ^ 108 + 2 ^ 109) % 2 ^ 110 : ℤ) ∧
    ((2 ^ 108 + 2 ^ 109) % 2 ^ 110 : ℤ)
      < 2 ^ 110 - ((67 : ℤ) + (periodLcm 67 : ℤ) + 110 + 2) := by
  rw [periodLcm_67_val]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

-- Independent probe G: the "demand" ledger grows like L^2 while the certificate
-- it is supposed to price gets EASIER with depth: at depth 110 the excluded arc
-- of the base cell at t = 67 is under 1/10000 of the circle, i.e. the certificate
-- is "the residue is not tiny" and needs essentially no coefficient information.
example : 10000 * (2 * ((67 : ℤ) + (periodLcm 67 : ℤ) + 112 + 2)) < 2 ^ 112 := by
  rw [periodLcm_67_val]; norm_num

-- Independent probe H: the base cell is a strictly WEAKER statement than the
-- diagonal cell at the same scale.  For t <= H, a diagonal certificate at H
-- implies a base certificate at (H, t), using only pre-existing corpus lemmas
-- (LcmConeFlatness, 2026-07-22).  Hence every baseKill_k deposit in AngleA1 is a
-- logical consequence of the corpus's already-recorded diagonal deposits, and
-- Part 2 adds no new mathematical content beyond a compute-cost observation.
-- NOTE: AngleA1 shadows the corpus name `exists_certifiedKill_of_tail_diff_notMem_int`
-- (Erdos249257.TotientTailPeriodKiller, general in (h, N)) with a strictly less
-- general diagonal-only copy.  Any file opening both namespaces gets an ambiguous
-- overload, so the corpus name must be written out in full below.
open Erdos249257.TotientTailPeriodKiller in
theorem base_cell_implied_by_diagonal_cell {t H L : ℕ} (htH : t ≤ H)
    (hc : certifiedKill H H L) : ∃ L', certifiedKill H t L' := by
  have hdiag : totientTail (H + H) - totientTail H ∉ Set.range ((↑) : ℤ → ℝ) :=
    tail_diff_notMem_int_of_certifiedKill hc
  refine Erdos249257.TotientTailPeriodKiller.exists_certifiedKill_of_tail_diff_notMem_int
    (fun hmem => hdiag ?_)
  obtain ⟨K, hK⟩ := (tail_diff_mem_int_iff_scaled_series_mem_int H t).mp hmem
  refine (tail_diff_mem_int_iff_scaled_series_mem_int H H).mpr ⟨2 ^ (H - t) * K, ?_⟩
  have hcast : (((2 ^ (H - t) * K : ℤ)) : ℝ) = (2 : ℝ) ^ (H - t) * ((K : ℤ) : ℝ) := by
    push_cast; ring
  have hsplit : (2 : ℝ) ^ (H - t) * (2 : ℝ) ^ t = (2 : ℝ) ^ H := by
    rw [← pow_add]; congr 1; omega
  calc (((2 ^ (H - t) * K : ℤ)) : ℝ)
      = (2 : ℝ) ^ (H - t) * ((K : ℤ) : ℝ) := hcast
    _ = (2 : ℝ) ^ (H - t)
          * ((2 : ℝ) ^ t * ((2 : ℝ) ^ H - 1)
              * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by rw [hK]
    _ = ((2 : ℝ) ^ (H - t) * (2 : ℝ) ^ t) * ((2 : ℝ) ^ H - 1)
          * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by ring
    _ = (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1)
          * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by rw [hsplit]

-- Concretely: baseKill_8 (AngleA1) is already implied by the corpus deposit
-- certifiedKill_periodLcm_diagonal_at_eight (LcmDiagonalReduction, 2026-07-22).
example : ∃ L', certifiedKill (periodLcm 8) 8 L' :=
  base_cell_implied_by_diagonal_cell (le_periodLcm 8)
    certifiedKill_periodLcm_diagonal_at_eight
