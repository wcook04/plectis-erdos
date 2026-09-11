/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.Recon257
import Erdos249257.HalfCylinderFatalGapRightTail

/-!
# Angle B4: cross-representation transport for the final `-2` middle cell

The `1/2`-membership programme uses four related objects at seam row `s`:

* **greedy** — the Boolean word `seamGreedyWord s : SeamRowWord s`;
* **carry** — the branch predicate `successorCarries` / `SeamGreedyUpperOrMiddleAt`;
* **seam** — the adjacent cut `seamAdjacentCut s`, i.e. `remainder`, `belowPulse`,
  `terminalWeight`;
* **residue** — the phase `D % 2730` used by the rank-`26` sieve and by the
  exclusion ratchet of `Lift/Recon257.lean`.

The first three objects are connected by the seam-word identities in the imported
development.  The residue phase is coarser: it sees only the *fixed* forced support
`{2,3,6,7,14,20,21,26}`, i.e. `pulseFloor`, while the greedy word sees the whole
of `seamWordSupport (seamGreedyWord s)`.

This file studies an auxiliary transport construction.  Conditional on a
hypothetical final middle cell of charge `-2` at rank `D` with an all-right tail,
the greedy representation certifies that every rank in
`[D+1, s-1]` lies in the support at row `s` (`seamWordSupport_add_eq_of_eventually_right`).
Transporting that conditional information defines the candidate floor

  `transportedFloor D s = pulseFloor s + tailPulse D s`,

and hence a ratchet that is at least as strong as `Recon257.ratchetRun`
when it is connected to such an orbit.  `transported_excludes` is the conditional
soundness statement: it assumes both the all-right tail and
`seamExcess (D+1) = 2`.

**MEASURED STATUS.**  The landing hypothesis `seamExcess s = 2` has no instance
for `5 ≤ s ≤ 102` in the audit computation.  Thus no audited concrete seam orbit
satisfies the hypotheses of `transported_excludes`; this file excludes no audited
class of the original problem.

## The result

The following results concern the auxiliary transported recurrence:

* **PROVED (auxiliary):** `tailPulse_eq_zero_of_two_mul_le` gives
  `tailPulse D s = 0` for every
  row with `2 * s ≤ 3 * D`.  A rank `d ≥ D+1` can divide `2s+1` or `2s+2` only via a
  cofactor `≥ 3`, so it must satisfy `3 * d ≤ 2 * s + 2`; the transported support is
  silent until row `(3D+1)/2`, i.e. for the first `⌊(D-2)/2⌋` steps of the ratchet.
* **PROVED (auxiliary):** `threshold_sharp` and
  `one_le_tailPulse_at_threshold` show that the arithmetic delay bound is sharp:
  at `2 * s = 3 * D + 1` (odd `D`) the rank `D+1` contributes to `tailPulse`.
  This does not assert that the corresponding `D` lies on a concrete all-right
  seam orbit.
* **PROVED (auxiliary):** `transportedRun_eq_ratchetRun` says that the
  transported ratchet is
  *literally the same function* as the residue ratchet up to depth `⌊D/2⌋`.
* **PROVED (auxiliary):** `transportedRun_immune` propagates the inequality
  `4 * s ≤ transportedRun D k` once it holds, using the proved bound
  `transportedFloor D s ≤ 2 * s + 9`.
* **PROVED (auxiliary):** `transported_nonDying_iff_survivorPhase` says that the
  transported recurrence is positive at every depth exactly on the same residue
  phases as `Recon257.SurvivorPhase`; outside those phases it is zero at depth `3`.

**Conclusion about the auxiliary construction.**  Its non-dying residue phases
are exactly `SurvivorPhase`, the same phases left by the imported residue ratchet.
Adding the formal tail contribution therefore removes no phase from that
auxiliary recurrence.  This is not a theorem that there are concrete #257
survivors in those phases: connection to a concrete orbit requires `hright` and
the unobserved landing hypothesis above.  The delay comes from the fact that the
extra support lives at ranks `≥ D+1`, and a rank of size `≥ D+1`
cannot divide `2s+1` or `2s+2` before row `3D/2`, by which time the geometric
factor `4` in the excess recursion has put the budget out of reach of any linear
pulse in the auxiliary bound.  The construction does not supply the *prefix*
part `seamWordSupport (seamGreedyWord s) ∩ [27, D]`.
-/

namespace Erdos249257

namespace AngleB4

open HalfCylinderIntegerGreedy
open Recon257
open scoped BigOperators

/-! ## 1.  The greedy-representation pulse of the all-right tail -/

/-- The row pulse at row `s` contributed by the ranks `D+1, …, s-1`.  On the
all-right tail of a hypothetical final middle cell at rank `D` every one of these
ranks is a certified member of the greedy support, so this is a certified addition
to the residue-representation floor `pulseFloor`. -/
def tailPulse (D s : ℕ) : ℕ := ∑ d ∈ Finset.Ico (D + 1) s, rowPulse s d

/-- Transport, greedy → seam: on an all-right tail every rank strictly between
`D` and `s` belongs to the row-`s` greedy support. -/
theorem Ico_subset_seamWordSupport
    {D : ℕ} (hD : 4 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hs : D + 1 ≤ s) :
    Finset.Ico (D + 1) s ⊆ seamWordSupport (seamGreedyWord s) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [seamWordSupport_add_eq_of_eventually_right (D + 1) (by omega) hright j]
  intro e he
  exact Finset.mem_union_right _ he

theorem sum_forced_eq_pulseFloor (s : ℕ) :
    ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d = pulseFloor s := by
  rw [pulseFloor_eq_rowPulseSum]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **PROVED, conditional.**  Under an all-right tail, the residue-representation
floor plus the tail contribution is a lower bound for the actual below-pulse of
the greedy seam cut.  The added term can be positive arithmetically, but this
theorem does not produce an all-right orbit on which that happens. -/
theorem pulseFloor_add_tailPulse_le_belowPulse
    (D : ℕ) (hD : 27 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (s : ℕ) (hs : D + 1 ≤ s) :
    pulseFloor s + tailPulse D s ≤
      (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega)
  have h7 := seven_mem_seamGreedySupport s (by omega)
  have h14 := fourteen_mem_seamGreedySupport s (by omega)
  have h20 := twenty_mem_seamGreedySupport s (by omega)
  have h21 := twentyOne_mem_seamGreedySupport s (by omega)
  have h26 := twentySix_mem_seamGreedySupport s (by omega)
  have hforced : ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ⊆
      seamWordSupport (seamGreedyWord s) := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h236.1
    · exact h236.2.1
    · exact h236.2.2
    · exact h7
    · exact h14
    · exact h20
    · exact h21
    · exact h26
  have htail := Ico_subset_seamWordSupport (D := D) (by omega) hright hs
  have hdisj : Disjoint ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ)
      (Finset.Ico (D + 1) s) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    have hab := (Finset.mem_Ico.mp hb).1
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hsub : ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ Finset.Ico (D + 1) s ⊆
      seamWordSupport (seamGreedyWord s) := Finset.union_subset hforced htail
  have hsum : ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪
        Finset.Ico (D + 1) s), rowPulse s d ≤
      ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  rw [Finset.sum_union hdisj, sum_forced_eq_pulseFloor] at hsum
  change pulseFloor s + tailPulse D s ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  exact hsum

/-! ## 2.  The delay: transported support cannot pulse before row `3D/2` -/

/-- **The representation-independent obstruction.**  A rank `d < s` is mute at row
`s` unless `3 * d ≤ 2 * s + 2`.  Indeed a divisor `d < s` of `2s+1` or of `2s+2` has
cofactor at least `3`, since cofactor `≤ 2` would force `2s + 1 ≤ 2d ≤ 2s - 2`.

Consequently: *certifying* that a rank `d` lies in the greedy support — in any of
the four representations, by any argument — can influence the exclusion ratchet
only from row `⌈(3d - 2)/2⌉ onwards`.  Support certification is useful only at
ranks `d ≤ (2s+2)/3`. -/
theorem rowPulse_eq_zero_of_large_rank
    {s d : ℕ} (hds : d < s) (h : 2 * s + 2 < 3 * d) :
    rowPulse s d = 0 := by
  have hnd2 : ¬ d ∣ 2 * s + 2 := by
    rintro ⟨m, hm⟩
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · have h2 : d * m ≤ d * 2 := Nat.mul_le_mul le_rfl (by omega)
      rw [← hm] at h2
      omega
    · have h3 : d * 3 ≤ d * m := Nat.mul_le_mul le_rfl hm3
      rw [← hm] at h3
      omega
  have hnd1 : ¬ d ∣ 2 * s + 1 := by
    rintro ⟨m, hm⟩
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · have h2 : d * m ≤ d * 2 := Nat.mul_le_mul le_rfl (by omega)
      rw [← hm] at h2
      omega
    · have h3 : d * 3 ≤ d * m := Nat.mul_le_mul le_rfl hm3
      rw [← hm] at h3
      omega
  simp [rowPulse, hnd1, hnd2]

/-- A rank above `D` cannot pulse at row `s` while `2 * s ≤ 3 * D`:
`2s + 2 ≤ 3D + 2 < 3D + 3 ≤ 3 * d`. -/
theorem rowPulse_eq_zero_of_tail_rank
    {D s d : ℕ} (hds : d < s) (hd : D + 1 ≤ d) (h : 2 * s ≤ 3 * D) :
    rowPulse s d = 0 :=
  rowPulse_eq_zero_of_large_rank hds (by omega)

/-- **The delay.**  The information transported from the greedy representation is
completely silent on every row `s` with `2 * s ≤ 3 * D`, i.e. for the first
`⌊(D-2)/2⌋` steps of the ratchet. -/
theorem tailPulse_eq_zero_of_two_mul_le
    (D s : ℕ) (h : 2 * s ≤ 3 * D) : tailPulse D s = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨hd1, hd2⟩ := Finset.mem_Ico.mp hd
  exact rowPulse_eq_zero_of_tail_rank hd2 hd1 h

/-- The delay bound is sharp: the witness row below sits at `2 * s = 3 * D + 1`. -/
theorem threshold_sharp (m : ℕ) : 2 * (3 * m + 2) = 3 * (2 * m + 1) + 1 := by ring

/-- **PROVED for the auxiliary tail sum.**  At the first row past the delay
threshold the rank `D + 1` itself divides `2s + 2`, so `tailPulse` is positive.
This arithmetic witness is not a witness to the all-right-tail hypotheses used
by `pulseFloor_add_tailPulse_le_belowPulse`. -/
theorem one_le_tailPulse_at_threshold (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ tailPulse (2 * m + 1) (3 * m + 2) := by
  have hdvd : (2 * m + 2) ∣ 2 * (3 * m + 2) + 2 := ⟨3, by ring⟩
  have hone : 1 ≤ rowPulse (3 * m + 2) (2 * m + 2) := by
    simp only [rowPulse, if_pos hdvd]
    omega
  have hmem : 2 * m + 2 ∈ Finset.Ico (2 * m + 1 + 1) (3 * m + 2) :=
    Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  refine le_trans hone ?_
  exact Finset.single_le_sum (f := fun d ↦ rowPulse (3 * m + 2) d)
    (fun i _ ↦ Nat.zero_le _) hmem

/-- The exact contrast.  Any rank `d ≥ 2` pulses at least once in every window of
`d + 1` consecutive rows (take the row with `d ∣ s + 1`).  So a certified *prefix*
rank `d ≤ D` fires at ratchet depth at most `d`, while by
`rowPulse_eq_zero_of_large_rank` every *tail* rank `d ≥ D + 1` is silent until
depth `≥ (D - 1)/2`.  Prefix certification is worth an undiscounted pulse; tail
certification is worth `4 ^ (-D/2)`. -/
theorem exists_rowPulse_pos (d : ℕ) (hd : 2 ≤ d) (S : ℕ) :
    ∃ s, S ≤ s ∧ s ≤ S + d ∧ 1 ≤ rowPulse s d := by
  have hdpos : 0 < d := by omega
  have hlt : (S + 1) % d < d := Nat.mod_lt _ hdpos
  have hle : (S + 1) % d ≤ S + 1 := Nat.mod_le _ _
  refine ⟨S + (d - (S + 1) % d), by omega, by omega, ?_⟩
  have hsucc : d ∣ (S + (d - (S + 1) % d)) + 1 := by
    have hrw : (S + (d - (S + 1) % d)) + 1 = (S + 1 - (S + 1) % d) + d := by omega
    rw [hrw]
    exact Nat.dvd_add (Nat.dvd_sub_mod (S + 1)) dvd_rfl
  have hdvd : d ∣ 2 * (S + (d - (S + 1) % d)) + 2 := by
    have hrw2 : 2 * (S + (d - (S + 1) % d)) + 2 =
        2 * ((S + (d - (S + 1) % d)) + 1) := by ring
    rw [hrw2]
    exact hsucc.mul_left 2
  simp only [rowPulse, if_pos hdvd]
  omega

/-- Depth form of the contrast: a rank `d` fires at some ratchet depth `≤ d`. -/
theorem exists_depth_rowPulse_pos (D d : ℕ) (hd : 2 ≤ d) :
    ∃ k, k ≤ d ∧ 1 ≤ rowPulse (D + 1 + k) d := by
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_rowPulse_pos d hd (D + 1)
  exact ⟨s - (D + 1), by omega, by rwa [show D + 1 + (s - (D + 1)) = s by omega]⟩

/-- Crude cap on the transported contribution: at most two per rank. -/
theorem tailPulse_le_two_mul (D s : ℕ) (hD : 1 ≤ D) : tailPulse D s ≤ 2 * s := by
  have hle : tailPulse D s ≤ ∑ _d ∈ Finset.Ico (D + 1) s, 2 := by
    apply Finset.sum_le_sum
    intro d hd
    exact rowPulse_le_two s d (by have := (Finset.mem_Ico.mp hd).1; omega)
  have hcard : ∑ _d ∈ Finset.Ico (D + 1) s, 2 = 2 * (s - (D + 1)) := by
    simp [Nat.mul_comm]
  omega

/-! ## 3.  The transported ratchet -/

/-- The certified pulse floor after cross-representation transport. -/
def transportedFloor (D s : ℕ) : ℕ := pulseFloor s + tailPulse D s

/-- One step of the transported ratchet. -/
def transportedStep (D s b : ℕ) : ℕ :=
  if 3 * transportedFloor D s + 4 ≤ 4 * b then
    4 * b - (3 * transportedFloor D s + 3)
  else 0

/-- The transported ratchet orbit from the landing budget `3 * 2 - 3 = 3`. -/
def transportedRun (D : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => transportedStep D (D + 1 + k) (transportedRun D k)

@[simp] theorem transportedRun_zero (D : ℕ) : transportedRun D 0 = 3 := rfl

theorem transportedRun_succ (D k : ℕ) :
    transportedRun D (k + 1) = transportedStep D (D + 1 + k) (transportedRun D k) := rfl

theorem transportedStep_zero (D s : ℕ) : transportedStep D s 0 = 0 := by
  unfold transportedStep
  rw [if_neg (by have := one_le_pulseFloor s; unfold transportedFloor; omega)]

/-! ### Conditional soundness of the transported ratchet -/

/-- The transported budget dominates `3 * seamExcess - 3` along the whole
right-tail orbit.  Same induction as `Recon257.ratchetRun_bound`, with the larger
certified floor. -/
theorem transportedRun_bound
    (D : ℕ) (hD27 : 27 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : seamExcess (D + 1) = 2) :
    ∀ k, 3 * seamExcess (D + 1 + k) - 3 ≤ (transportedRun D k : ℤ) := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  intro k
  induction k with
  | zero =>
      simp only [Nat.add_zero, transportedRun_zero, hlanding]
      norm_num
  | succ k ih =>
      have hs : D + 1 ≤ D + 1 + k := by omega
      have hstep := (horbit (D + 1 + k) hs).2
      have hrec : seamExcess (D + 1 + (k + 1)) =
          4 * seamExcess (D + 1 + k) -
            ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) - 4 := by
        simpa [seamExcess, show D + 1 + (k + 1) = (D + 1 + k) + 1 by ring] using hstep
      have hfloor : (transportedFloor D (D + 1 + k) : ℤ) ≤
          ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
        exact_mod_cast pulseFloor_add_tailPulse_le_belowPulse D hD27 hright (D + 1 + k) hs
      have hmain : 3 * seamExcess (D + 1 + (k + 1)) - 3 ≤
          4 * (transportedRun D k : ℤ) -
            (3 * (transportedFloor D (D + 1 + k) : ℤ) + 3) := by
        rw [hrec]; omega
      rw [transportedRun_succ]
      unfold transportedStep
      split_ifs with hcond
      · have hle : 3 * transportedFloor D (D + 1 + k) + 3 ≤ 4 * transportedRun D k := by
          omega
        have hcast :
            ((4 * transportedRun D k -
                (3 * transportedFloor D (D + 1 + k) + 3) : ℕ) : ℤ) =
              4 * (transportedRun D k : ℤ) -
                (3 * (transportedFloor D (D + 1 + k) : ℤ) + 3) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [hcast]
        exact hmain
      · have hcondZ : 4 * (transportedRun D k : ℤ) ≤
            3 * (transportedFloor D (D + 1 + k) : ℤ) + 3 := by
          have hnat : 4 * transportedRun D k ≤
              3 * transportedFloor D (D + 1 + k) + 3 := by omega
          exact_mod_cast hnat
        simp only [Nat.cast_zero]
        omega

/-- **PROVED, conditional soundness.**  If the transported budget dies, a final
middle cell of charge `-2` at rank `D` satisfying both the all-right-tail
hypothesis and `seamExcess (D+1) = 2` is contradictory.  The latter hypothesis
has no audited instance for seam rows `5 ≤ s ≤ 102`. -/
theorem transported_excludes
    (D : ℕ) (hD27 : 27 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : seamExcess (D + 1) = 2)
    (k : ℕ) (hdead : transportedRun D k = 0) : False := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  have hbound := transportedRun_bound D hD27 hright hlanding k
  rw [hdead] at hbound
  have hpos : 0 < seamExcess (D + 1 + k) := by
    have := (horbit (D + 1 + k) (by omega)).1
    simpa [seamExcess] using this
  have hone : seamExcess (D + 1 + k) = 1 := by
    simp only [Nat.cast_zero] at hbound
    omega
  have hstep := (horbit (D + 1 + k) (by omega)).2
  have hrec : seamExcess (D + 1 + k + 1) =
      4 * seamExcess (D + 1 + k) -
        ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) - 4 := by
    simpa [seamExcess] using hstep
  have hnext : 0 < seamExcess (D + 1 + k + 1) := by
    have := (horbit (D + 1 + k + 1) (by omega)).1
    simpa [seamExcess] using this
  have hfloor : (pulseFloor (D + 1 + k) : ℤ) ≤
      ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
    exact_mod_cast pulseFloor_le_belowPulse (D + 1 + k) (by omega)
  have hone' : (1 : ℤ) ≤ (pulseFloor (D + 1 + k) : ℤ) := by
    exact_mod_cast one_le_pulseFloor (D + 1 + k)
  rw [hone] at hrec
  omega

/-! ## 4.  The transported ratchet is the residue ratchet below the delay -/

theorem transportedFloor_eq_pulseFloor (D s : ℕ) (h : 2 * s ≤ 3 * D) :
    transportedFloor D s = pulseFloor s := by
  unfold transportedFloor
  rw [tailPulse_eq_zero_of_two_mul_le D s h]
  omega

/-- **No early gain.**  Through depth `⌊D/2⌋` the transported ratchet is literally
the same function as the residue ratchet of `Recon257`. -/
theorem transportedRun_eq_ratchetRun (D : ℕ) :
    ∀ k, 2 * k ≤ D → transportedRun D k = ratchetRun D k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      rw [transportedRun_succ, ratchetRun_succ, ih (by omega)]
      unfold transportedStep ratchetStep
      rw [transportedFloor_eq_pulseFloor D (D + 1 + k) (by omega)]

/-- Every class the residue ratchet kills is killed by the transported ratchet at
the same depth `3` (for `D ≥ 6`). -/
theorem transportedRun_eq_zero_of_not_survivorPhase
    (D : ℕ) (hD : 6 ≤ D) (h : ¬ SurvivorPhase D) : transportedRun D 3 = 0 := by
  rw [transportedRun_eq_ratchetRun D 3 (by omega)]
  exact ratchetRun_eq_zero_of_not_survivorPhase D h

/-! ## 5.  Immunity under the transported-floor bound -/

theorem transportedFloor_le (D s : ℕ) (hD : 1 ≤ D) :
    transportedFloor D s ≤ 2 * s + 9 := by
  have h1 := pulseFloor_le_nine s
  have h2 := tailPulse_le_two_mul D s hD
  unfold transportedFloor
  omega

/-- Once the budget exceeds `4 * s`, the auxiliary transported step increases it
past `4 * (s + 1)`, using `transportedFloor D s ≤ 2 * s + 9`.  This theorem is
about `transportedFloor`; it does not replace that floor by the concrete
below-pulse of an arbitrary seam word. -/
theorem transportedStep_ge
    (D s b : ℕ) (hD : 1 ≤ D) (hs : 6 ≤ s) (hb : 4 * s ≤ b) :
    4 * (s + 1) ≤ transportedStep D s b := by
  have hF := transportedFloor_le D s hD
  unfold transportedStep
  rw [if_pos (by omega)]
  omega

/-- Immunity is permanent. -/
theorem transportedRun_immune
    (D : ℕ) (hD : 5 ≤ D) (k : ℕ) (hk : 4 * (D + 1 + k) ≤ transportedRun D k) :
    ∀ i, 4 * (D + 1 + (k + i)) ≤ transportedRun D (k + i) := by
  intro i
  induction i with
  | zero => simpa using hk
  | succ i ih =>
      have hstep := transportedStep_ge D (D + 1 + (k + i)) (transportedRun D (k + i))
        (by omega) (by omega) ih
      rw [show k + (i + 1) = (k + i) + 1 by ring, transportedRun_succ]
      have hrw : D + 1 + (k + i) + 1 = D + 1 + (k + (i + 1)) := by ring
      rw [hrw] at hstep
      exact hstep

/-! ## 6.  Growth of the residue budget -/

theorem pulseFloor_add_mul_period (s n : ℕ) : pulseFloor (s + 2730 * n) = pulseFloor s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show s + 2730 * (n + 1) = (s + 2730 * n) + 2730 by ring,
        pulseFloor_add_period, ih]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- The weighted three-row pulse budget, checked on all `2730` phases.  The bound
`157` is attained. -/
theorem pulseFloorTriple_core :
    ∀ r < 2730,
      16 * pulseFloor r + 4 * pulseFloor (r + 1) + pulseFloor (r + 2) ≤ 157 := by
  decide +kernel

theorem pulseFloorTriple (s : ℕ) :
    16 * pulseFloor s + 4 * pulseFloor (s + 1) + pulseFloor (s + 2) ≤ 157 := by
  have hr : s % 2730 < 2730 := Nat.mod_lt _ (by norm_num)
  have e0 : pulseFloor s = pulseFloor (s % 2730) := by
    conv_lhs => rw [show s = s % 2730 + 2730 * (s / 2730) by omega]
    exact pulseFloor_add_mul_period _ _
  have e1 : pulseFloor (s + 1) = pulseFloor (s % 2730 + 1) := by
    conv_lhs => rw [show s + 1 = (s % 2730 + 1) + 2730 * (s / 2730) by omega]
    exact pulseFloor_add_mul_period _ _
  have e2 : pulseFloor (s + 2) = pulseFloor (s % 2730 + 2) := by
    conv_lhs => rw [show s + 2 = (s % 2730 + 2) + 2730 * (s / 2730) by omega]
    exact pulseFloor_add_mul_period _ _
  rw [e0, e1, e2]
  exact pulseFloorTriple_core _ hr

theorem ratchetStep_eq_of_eight_le (s b : ℕ) (hb : 8 ≤ b) :
    ratchetStep s b = 4 * b - (3 * pulseFloor s + 3) := by
  have h := pulseFloor_le_nine s
  unfold ratchetStep
  rw [if_pos (by omega)]

/-- Three residue-ratchet steps multiply the budget by at least `8`. -/
theorem ratchetRun_three_step (D k : ℕ) (hb : 10 ≤ ratchetRun D k) :
    8 * ratchetRun D k ≤ ratchetRun D (k + 3) := by
  have h0 := pulseFloor_le_nine (D + 1 + k)
  have h1 := pulseFloor_le_nine (D + 1 + k + 1)
  have h2 := pulseFloor_le_nine (D + 1 + k + 2)
  have htri := pulseFloorTriple (D + 1 + k)
  have hb1 : 10 ≤ ratchetRun D (k + 1) := ten_le_ratchetStep _ _ hb
  have hb2 : 10 ≤ ratchetRun D (k + 2) := ten_le_ratchetStep _ _ hb1
  have e1 : ratchetRun D (k + 1) = 4 * ratchetRun D k - (3 * pulseFloor (D + 1 + k) + 3) := by
    rw [ratchetRun_succ]
    exact ratchetStep_eq_of_eight_le _ _ (by omega)
  have e2 : ratchetRun D (k + 2) =
      4 * ratchetRun D (k + 1) - (3 * pulseFloor (D + 1 + k + 1) + 3) := by
    rw [ratchetRun_succ]
    rw [show D + 1 + (k + 1) = D + 1 + k + 1 by ring]
    exact ratchetStep_eq_of_eight_le _ _ (by omega)
  have e3 : ratchetRun D (k + 3) =
      4 * ratchetRun D (k + 2) - (3 * pulseFloor (D + 1 + k + 2) + 3) := by
    rw [ratchetRun_succ]
    rw [show D + 1 + (k + 2) = D + 1 + k + 2 by ring]
    exact ratchetStep_eq_of_eight_le _ _ (by omega)
  omega

theorem ratchetRun_geom (D : ℕ) (h5 : 10 ≤ ratchetRun D 5) :
    ∀ j, 10 * 8 ^ j ≤ ratchetRun D (5 + 3 * j) := by
  intro j
  induction j with
  | zero => simpa using h5
  | succ j ih =>
      have hpow : 1 ≤ 8 ^ j := Nat.one_le_pow _ _ (by norm_num)
      have hb : 10 ≤ ratchetRun D (5 + 3 * j) := by nlinarith
      have hstep := ratchetRun_three_step D (5 + 3 * j) hb
      have hidx : 5 + 3 * (j + 1) = (5 + 3 * j) + 3 := by ring
      rw [hidx]
      have : 10 * 8 ^ (j + 1) = 8 * (10 * 8 ^ j) := by ring
      omega

/-! ## 7.  Assembly: the auxiliary transport removes no survivor phase -/

theorem linear_le_geom : ∀ j, 2 ≤ j → 36 * j + 84 ≤ 10 * 8 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
      have hpow : 1 ≤ 8 ^ j := Nat.one_le_pow _ _ (by norm_num)
      have hgrow : 10 * 8 ^ (j + 1) = 8 * (10 * 8 ^ j) := by ring
      omega

/-- **PROVED, auxiliary negative result.**  On every `SurvivorPhase`, the
transported recurrence is positive at every depth.  This is a statement about
the defined recurrence, not the existence of a concrete all-right seam orbit in
that phase. -/
theorem transported_ratchet_never_dies
    (D : ℕ) (hD : 27 ≤ D) (h : SurvivorPhase D) :
    ∀ k, 0 < transportedRun D k := by
  classical
  have h5 : 10 ≤ ratchetRun D 5 := by
    have hlt : D % 2730 < 2730 := Nat.mod_lt _ (by norm_num)
    have hcore := ratchet_finite_core _ hlt
    rw [if_pos ((survivorPhase_mod D).1 h)] at hcore
    rw [ratchetRun_mod]
    exact hcore
  obtain ⟨j, hj2, hjlow, hjhigh⟩ :
      ∃ j : ℕ, 2 ≤ j ∧ 2 * (5 + 3 * j) ≤ D ∧ D ≤ 6 * j + 15 := by
    refine ⟨(D - 10) / 6, ?_, ?_, ?_⟩ <;> omega
  have hgeom := ratchetRun_geom D h5 j
  have hlin := linear_le_geom j hj2
  have hbig : 4 * (D + 1 + (5 + 3 * j)) ≤ ratchetRun D (5 + 3 * j) := by omega
  have heq0 : transportedRun D (5 + 3 * j) = ratchetRun D (5 + 3 * j) :=
    transportedRun_eq_ratchetRun D (5 + 3 * j) (by omega)
  have hbigT : 4 * (D + 1 + (5 + 3 * j)) ≤ transportedRun D (5 + 3 * j) := by
    rw [heq0]; exact hbig
  intro k
  rcases Nat.lt_or_ge k (5 + 3 * j) with hk | hk
  · rw [transportedRun_eq_ratchetRun D k (by omega)]
    exact ratchetRun_pos_of_survivorPhase D h k
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
    have := transportedRun_immune D (by omega) (5 + 3 * j) hbigT i
    omega

/-- **PROVED, auxiliary exact converse.**  The transported recurrence is
non-dying exactly on `SurvivorPhase`.  This equates the two devices' non-dying
phase sets; it does not say their values are extensionally equal at all depths,
nor does it produce concrete seam orbits. -/
theorem transported_nonDying_iff_survivorPhase
    (D : ℕ) (hD : 27 ≤ D) :
    (∀ k, 0 < transportedRun D k) ↔ SurvivorPhase D := by
  constructor
  · intro hpos
    by_contra hcon
    have := transportedRun_eq_zero_of_not_survivorPhase D (by omega) hcon
    have := hpos 3
    omega
  · exact transported_ratchet_never_dies D hD

/-!
## What this settles

`transported_nonDying_iff_survivorPhase` answers the auxiliary B4 recurrence
question: adding `tailPulse` does not change its non-dying phase set.

**PROVED, conditional:** `pulseFloor_add_tailPulse_le_belowPulse` turns the tail
sum into a certified lower bound when an all-right tail is supplied, and
`transported_excludes` is sound when the additional landing hypothesis
`seamExcess (D+1) = 2` is supplied.

**MEASURED:** the audit found no row `5 ≤ s ≤ 102` with `seamExcess s = 2`.
Consequently these conditional theorems exclude no audited concrete class.  The
unconditional theorem `one_le_tailPulse_at_threshold` only shows that the
auxiliary tail sum can be positive at arithmetic witness rows; it does not show
that those rows occur on an all-right seam orbit.

Within the auxiliary recurrence, the transported tail contribution is inert with
respect to the non-dying phase set.  The delay is proved by
`rowPulse_eq_zero_of_tail_rank`: a rank `d` can pulse at row `s` only if it divides
`2s+1` or `2s+2`, and a proper divisor `d < s` of either has cofactor `≥ 3`, hence
`3 * d ≤ 2s + 2`.  Ranks certified by the tail satisfy `d ≥ D+1`, so they are mute
until `s ≥ (3D+1)/2`, i.e. until ratchet depth `≈ D/2`.  By depth `5 + 3⌊(D-10)/6⌋`
the residue budget already exceeds `4 * s` (`ratchetRun_geom`), and from there
`transportedStep_ge` shows the budget grows under the defined transported floor,
which is bounded by `2s + 9`.

The calculation therefore identifies what this transport construction omits:
ranks in the *prefix* of the greedy support, including `[27, D]`.  It does not
prove that certifying that prefix would close the original branch, nor that the
remaining phases contain concrete survivor classes.

`rowPulse_eq_zero_of_large_rank` states this in representation-free form: a rank
`d` is invisible at every row `s < (3 * d - 2) / 2`.  Thus any support
certification that influences the first `k` steps of this ratchet at rank `D`
must involve ranks `d ≤ (2 * (D + 1 + k) + 2) / 3`.  For the depths used here,
those ranks lie below `D`, in the prefix about which the all-right tail says
nothing.

Axiom audit (checked with `#print axioms`):
`pulseFloor_add_tailPulse_le_belowPulse`, `tailPulse_eq_zero_of_two_mul_le`,
`one_le_tailPulse_at_threshold`, `transported_excludes`,
`transportedRun_eq_ratchetRun`, `pulseFloorTriple`,
`transported_ratchet_never_dies` and `transported_nonDying_iff_survivorPhase`
depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

end AngleB4

end Erdos249257
