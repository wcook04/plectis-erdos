/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.HalfFinalMiddlePhaseSieve

/-!
# Angle B1: an auxiliary exclusion ratchet at rank `27`

`Erdos249257.HalfFinalMiddlePhaseSieve` supplies residue conditions modulo `2730`
for a hypothetical final middle cell of charge `-2`.  This file studies a separate,
auxiliary recurrence built from the nine forced concrete-greedy ranks
`2, 3, 6, 7, 14, 20, 21, 26, 27`.

## Logical status

* **PROVED:** rank `27` belongs to the concrete greedy seam support for `s ≥ 32`;
  the resulting nine-rank pulse is a lower bound for the concrete below-pulse.
* **PROVED (auxiliary recurrence):** the finite residue computations, strict
  inclusion of phase sets, and permanent positive phase at residue `14`.
* **PROVED CONDITIONAL:** the auxiliary recurrence constrains a final-middle
  configuration only under an all-right concrete seam tail and the landing equality
  `seamExcess (D + 1) = 2` (or hypotheses that imply that equality).
* **MEASURED:** direct evaluation finds no `s ∈ [5, 102]` with
  `seamExcess s = 2`.  Thus the conditional bridge has no audited landing instance
  in that range.
* **RETRACTED:** the auxiliary phase sets are not certified sets of realizable
  #257 classes, and their shrinkage is not progress on the live #257 branch.

## What is new here

1.  **PROVED: rank `27` is a forced greedy seam rank**
    (`twentySeven_mem_seamGreedySupport`).
    This is the new mathematical input.  It is *not* available from row `28`: the
    exact integer comparison
    `truncatedMersenneWeight s 27 ≤ seamSubsetTarget s - (the eight earlier weights)`
    is **MEASURED false** for `s = 28, 29, 30, 31`; the `32 ≤ s` direction is
    **PROVED** in Lean.  Accordingly, the theorem carries `32 ≤ s` and the
    conditional bridge statements carry `31 ≤ D`.

2.  **PROVED (auxiliary recurrence): the nine-rank ratchet** `ratchetRun27`.
    Its state is a natural-number budget with transition
    `b ↦ 4 * b - 3 * pulseFloor27 s - 3` when the guarded subtraction remains
    positive, and with `0` absorbing.  It depends on `D` only through
    `D % 24570`.  Its domination of
    `3 * (seamIntegerGreedyRemainder s - 2 ^ s) - 3` is **PROVED CONDITIONAL**
    in `ratchetRun27_bound`, under the all-right-tail and landing hypotheses.

3.  **PROVED (auxiliary recurrence): strict shrinking**
    (`survivors27_ssubset_liftedSurvivors26`,
    `survivors27_card_lt`).  The auxiliary phase set at rank `27` is a *proper* subset of
    the lift to modulus `24570` of the `412` rank-`26` auxiliary phases: the
    nine-rank recurrence kills the phase `D ≡ 200 (mod 24570)`, which the eight-rank
    recurrence keeps.  On the base residue block `[0, 2730)`, Lean proves that the
    auxiliary count drops from `412` to `390`
    (`survivors27Base_card`, `survivors27Base_card_lt`).  The full-modulus counts
    `3708 = 9 * 412` and `3522` are **MEASURED**, not kernel-proved here.

4.  **PROVED (auxiliary recurrence): the fixed phase set**
    (`ratchetRun27_pos_of_alive`, `ratchet27_finite_core`).  By depth `6` every
    residue phase is either dead or already above the escape threshold `12`.
    Therefore every auxiliary phase surviving depth `6` survives every depth.
    `ratchetRun27_pos_fourteen` exhibits `D ≡ 14 (mod 24570)` as a phase the
    recurrence never excludes.  It does not exhibit a realizable final-middle
    configuration.

## What the auxiliary calculation shows

The auxiliary recurrence has a geometrically discounted pulse term.  The Lean
theorems below prove two finite statements about that recurrence; they do not prove
an infinite-series equivalence for realizable #257 configurations.

* `pulseAt_twentySeven_window` : rank `27` supplies **exactly `3`** units of pulse per
  `27` consecutive rows, wherever the window starts.  This exact finite-window
  identity is the proved content.

* `pulseFloor27_le_eleven` : the whole nine-rank floor is bounded by the *constant*
  `11`.  Together with `twelve_le_ratchetStep` and `ratchet27_finite_core`, this
  proves that an auxiliary phase alive at depth `6` stays alive at every later depth.

Together these show that adding rank `27` changes the auxiliary base-block count
from `412` to `390` but leaves a nonempty fixed phase set.  Because the bridge to the
concrete seam orbit also requires the unobserved landing equality, this calculation
does not close or reduce the live #257 branch.
-/

namespace Erdos249257

namespace AngleB1

open HalfCylinderIntegerGreedy

/-! ## PROVED: rank `27` is a forced greedy seam rank

The eight forced ranks `2, 3, 6, 7, 14, 20, 21, 26` are already recorded in
`HalfFinalMiddlePhaseSieve`.  The greedy Mersenne-reciprocal expansion of `1/2` has
`27` as its ninth term, and the deficit after nine terms is
`107644170831134536927 / 243343288463189657575723817850 ≈ 4.42 * 10 ^ (-10)`.  The
floor-truncated integer greedy only sees this once `2 ^ s` exceeds the reciprocal of
twice that deficit.  The direction from `s = 32` is proved below; sharpness in the
four preceding rows is measured outside Lean. -/

/-- **PROVED for `s ≥ 32`.**  The exact integer comparison that makes rank `27` a
selected greedy rank.  The
nine reciprocals `1/3 + 1/7 + 1/63 + 1/127 + 1/16383 + 1/1048575 + 1/2097151 +
1/67108863 + 1/134217727` fall short of `1/2` by exactly
`107644170831134536927 / 243343288463189657575723817850`.
Failure at `s = 28, 29, 30, 31` is **MEASURED** outside this theorem. -/
theorem seamGreedy_postTwentySix_decision_twentySeven (s : ℕ) (hs : 32 ≤ s) :
    truncatedMersenneWeight s 27 ≤
      seamSubsetTarget s - truncatedMersenneWeight s 2 -
        truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
        truncatedMersenneWeight s 7 - truncatedMersenneWeight s 14 -
        truncatedMersenneWeight s 20 - truncatedMersenneWeight s 21 -
        truncatedMersenneWeight s 26 := by
  let X := 4 ^ s
  let w2 := truncatedMersenneWeight s 2
  let w3 := truncatedMersenneWeight s 3
  let w6 := truncatedMersenneWeight s 6
  let w7 := truncatedMersenneWeight s 7
  let w14 := truncatedMersenneWeight s 14
  let w20 := truncatedMersenneWeight s 20
  let w21 := truncatedMersenneWeight s 21
  let w26 := truncatedMersenneWeight s 26
  let w27 := truncatedMersenneWeight s 27
  have hfour : X = 2 * 2 ^ (2 * s - 1) := by
    dsimp [X]
    calc
      4 ^ s = 2 ^ (2 * s) := by
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
      _ = 2 ^ ((2 * s - 1) + 1) := by
        congr 1
        omega
      _ = 2 * 2 ^ (2 * s - 1) := by
        rw [pow_succ]
        ring
  have hyA : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have htargetAdd : seamSubsetTarget s + 2 ^ s = 2 ^ (2 * s - 1) := by
    unfold seamSubsetTarget
    omega
  have hw2Upper : 3 * w2 ≤ X := by
    dsimp [X, w2, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 3
  have hw3Upper : 7 * w3 ≤ X := by
    dsimp [X, w3, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 7
  have hw6Upper : 63 * w6 ≤ X := by
    dsimp [X, w6, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 63
  have hw7Upper : 127 * w7 ≤ X := by
    dsimp [X, w7, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 127
  have hw14Upper : 16383 * w14 ≤ X := by
    dsimp [X, w14, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 16383
  have hw20Upper : 1048575 * w20 ≤ X := by
    dsimp [X, w20, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 1048575
  have hw21Upper : 2097151 * w21 ≤ X := by
    dsimp [X, w21, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 2097151
  have hw26Upper : 67108863 * w26 ≤ X := by
    dsimp [X, w26, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 67108863
  have hw27Upper : 134217727 * w27 ≤ X := by
    dsimp [X, w27, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 134217727
  have h2u := Nat.mul_le_mul_left 40557214743864942929287302975 hw2Upper
  have h3u := Nat.mul_le_mul_left 17381663461656404112551701275 hw3Upper
  have h6u := Nat.mul_le_mul_left 1931295940184044901394633475 hw6Upper
  have h7u := Nat.mul_le_mul_left 958044442768463218802062275 hw7Upper
  have h14u := Nat.mul_le_mul_left 7426701106732273013969475 hw14Upper
  have h20u := Nat.mul_le_mul_left 116035232798411967468099 hw20Upper
  have h21u := Nat.mul_le_mul_left 58017588734237462532675 hw21Upper
  have h26u := Nat.mul_le_mul_left 1813048810432011473475 hw26Upper
  have h27u := Nat.mul_le_mul_left 906524398461872542275 hw27Upper
  have hsumUpper :
      121671644231594828787861908925 *
          (w2 + w3 + w6 + w7 + w14 + w20 + w21 + w26 + w27) ≤
        60835822061975328978363685999 * X := by
    omega
  have hpow32 :
      243343288463189657575723817850 ≤ 107644170831134536927 * 2 ^ s := by
    have hmono : 2 ^ 32 ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbase :
        243343288463189657575723817850 ≤ 107644170831134536927 * 2 ^ 32 := by
      norm_num
    exact hbase.trans (Nat.mul_le_mul_left 107644170831134536927 hmono)
  have hside :
      243343288463189657575723817850 * 2 ^ s ≤ 107644170831134536927 * X := by
    have hmul := Nat.mul_le_mul_right (2 ^ s) hpow32
    calc
      243343288463189657575723817850 * 2 ^ s ≤
          (107644170831134536927 * 2 ^ s) * 2 ^ s := hmul
      _ = 107644170831134536927 * X := by
        have hpow : 4 ^ s = 2 ^ s * 2 ^ s := by
          calc
            4 ^ s = 2 ^ (2 * s) := by
              rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
            _ = 2 ^ (s + s) := by rw [two_mul]
            _ = 2 ^ s * 2 ^ s := by rw [pow_add]
        dsimp [X]
        rw [hpow]
        ring
  have htake : w2 + w3 + w6 + w7 + w14 + w20 + w21 + w26 + w27 ≤
      seamSubsetTarget s := by omega
  dsimp [w2, w3, w6, w7, w14, w20, w21, w26, w27] at htake
  omega

/-- List-level normal form of the forced seam decisions through rank `27`. -/
theorem seamGreedyBits_head2367_14_20_21_26_27
    (s : ℕ) (hs : 32 ≤ s) :
    integerGreedyBits (seamWeights s) (seamSubsetTarget s) =
      true :: true :: false :: false :: true :: true ::
        false :: false :: false :: false :: false :: false :: true ::
          false :: false :: false :: false :: false :: true :: true ::
            false :: false :: false :: false :: true :: true ::
              integerGreedyBits (seamWeightsFrom s 28)
                (seamSubsetTarget s - truncatedMersenneWeight s 2 -
                  truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
                  truncatedMersenneWeight s 7 - truncatedMersenneWeight s 14 -
                  truncatedMersenneWeight s 20 - truncatedMersenneWeight s 21 -
                  truncatedMersenneWeight s 26 -
                  truncatedMersenneWeight s 27) := by
  have h27 := seamGreedy_postTwentySix_decision_twentySeven s hs
  rw [seamGreedyBits_head2367_14_20_21_26 s (by omega),
    seamWeightsFrom_eq_cons (by omega : 27 < s)]
  simp only [integerGreedyBits]
  rw [if_pos h27]

/-- **PROVED:** rank `27` is the ninth mandatory selected concrete-seam rank from
row `32` on. -/
theorem twentySeven_mem_seamGreedySupport
    (s : ℕ) (hs : 32 ≤ s) :
    27 ∈ seamWordSupport (seamGreedyWord s) := by
  have hbits := seamGreedyBits_head2367_14_20_21_26_27 s hs
  apply mem_seamWordSupport_iff.mpr
  refine ⟨⟨25, by omega⟩, ?_, by norm_num⟩
  simp [seamGreedyWord, SeamRowWord.ofList, hbits]

/-! ## PROVED: the certified nine-rank pulse floor

The row pulse in remainder form, and the sum of the row pulses of the nine forced
greedy seam ranks `2, 3, 6, 7, 14, 20, 21, 26, 27`.  The eight-rank version and the
`pulseAt` interface are the ones introduced in `Lift/Recon257.lean`; everything below
is the nine-rank extension. -/

/-- The row pulse of rank `d` at row `s`, in remainder form. -/
def pulseAt (s d : ℕ) : ℕ :=
  (if (2 * s + 2) % d = 0 then 1 else 0) +
    2 * (if (2 * s + 1) % d = 0 then 1 else 0)

theorem pulseAt_two (s : ℕ) : pulseAt s 2 = rowPulse s 2 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_three (s : ℕ) : pulseAt s 3 = rowPulse s 3 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_six (s : ℕ) : pulseAt s 6 = rowPulse s 6 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_seven (s : ℕ) : pulseAt s 7 = rowPulse s 7 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_fourteen (s : ℕ) : pulseAt s 14 = rowPulse s 14 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_twenty (s : ℕ) : pulseAt s 20 = rowPulse s 20 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_twentyOne (s : ℕ) : pulseAt s 21 = rowPulse s 21 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_twentySix (s : ℕ) : pulseAt s 26 = rowPulse s 26 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

theorem pulseAt_twentySeven (s : ℕ) : pulseAt s 27 = rowPulse s 27 := by
  unfold pulseAt rowPulse; split_ifs <;> omega

/-- The eight-rank pulse floor of the existing sieve. -/
def pulseFloor26 (s : ℕ) : ℕ :=
  pulseAt s 2 + pulseAt s 3 + pulseAt s 6 + pulseAt s 7 +
    pulseAt s 14 + pulseAt s 20 + pulseAt s 21 + pulseAt s 26

/-- The nine-rank pulse floor: the eight-rank floor plus the rank-`27` row pulse. -/
def pulseFloor27 (s : ℕ) : ℕ := pulseFloor26 s + pulseAt s 27

theorem pulseFloor26_le_pulseFloor27 (s : ℕ) : pulseFloor26 s ≤ pulseFloor27 s := by
  unfold pulseFloor27; omega

theorem pulseFloor27_eq_rowPulseSum (s : ℕ) :
    pulseFloor27 s =
      rowPulse s 2 + rowPulse s 3 + rowPulse s 6 + rowPulse s 7 +
        rowPulse s 14 + rowPulse s 20 + rowPulse s 21 + rowPulse s 26 +
        rowPulse s 27 := by
  unfold pulseFloor27 pulseFloor26
  rw [pulseAt_two, pulseAt_three, pulseAt_six, pulseAt_seven,
    pulseAt_fourteen, pulseAt_twenty, pulseAt_twentyOne, pulseAt_twentySix,
    pulseAt_twentySeven]

theorem one_le_pulseFloor27 (s : ℕ) : 1 ≤ pulseFloor27 s := by
  have h : pulseAt s 2 = 1 := by unfold pulseAt; split_ifs <;> omega
  unfold pulseFloor27 pulseFloor26
  omega

/-- **PROVED:** the nine-rank pulse floor never exceeds `11`:
`{3,6}`, `{7,14}`, `21` and `27` contribute at most `2` each, and `2`, `20`, `26`
contribute at most `1` each.  Hence the ratchet has a *constant* escape threshold. -/
theorem pulseFloor27_le_eleven (s : ℕ) : pulseFloor27 s ≤ 11 := by
  have h2 : pulseAt s 2 = 1 := by unfold pulseAt; split_ifs <;> omega
  have h36 : pulseAt s 3 + pulseAt s 6 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h714 : pulseAt s 7 + pulseAt s 14 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h20 : pulseAt s 20 ≤ 1 := by unfold pulseAt; split_ifs <;> omega
  have h21 : pulseAt s 21 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h26 : pulseAt s 26 ≤ 1 := by unfold pulseAt; split_ifs <;> omega
  have h27 : pulseAt s 27 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  unfold pulseFloor27 pulseFloor26
  omega

/-- The nine-rank floor depends only on `s % 24570`: every forced rank divides
`49140 = 2 * 24570`. -/
theorem pulseFloor27_add_period (s : ℕ) :
    pulseFloor27 (s + 24570) = pulseFloor27 s := by
  have h2 : pulseAt (s + 24570) 2 = pulseAt s 2 := by
    unfold pulseAt; split_ifs <;> omega
  have h3 : pulseAt (s + 24570) 3 = pulseAt s 3 := by
    unfold pulseAt; split_ifs <;> omega
  have h6 : pulseAt (s + 24570) 6 = pulseAt s 6 := by
    unfold pulseAt; split_ifs <;> omega
  have h7 : pulseAt (s + 24570) 7 = pulseAt s 7 := by
    unfold pulseAt; split_ifs <;> omega
  have h14 : pulseAt (s + 24570) 14 = pulseAt s 14 := by
    unfold pulseAt; split_ifs <;> omega
  have h20 : pulseAt (s + 24570) 20 = pulseAt s 20 := by
    unfold pulseAt; split_ifs <;> omega
  have h21 : pulseAt (s + 24570) 21 = pulseAt s 21 := by
    unfold pulseAt; split_ifs <;> omega
  have h26 : pulseAt (s + 24570) 26 = pulseAt s 26 := by
    unfold pulseAt; split_ifs <;> omega
  have h27 : pulseAt (s + 24570) 27 = pulseAt s 27 := by
    unfold pulseAt; split_ifs <;> omega
  unfold pulseFloor27 pulseFloor26
  rw [h2, h3, h6, h7, h14, h20, h21, h26, h27]

/-- **PROVED:** all nine forced ranks lie in the concrete
greedy seam support from row `32` on, so their row pulses sum to a lower bound for the
below-pulse of the concrete adjacent cut. -/
theorem pulseFloor27_le_belowPulse (s : ℕ) (hs : 32 ≤ s) :
    pulseFloor27 s ≤ (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega)
  have h7 := seven_mem_seamGreedySupport s (by omega)
  have h14 := fourteen_mem_seamGreedySupport s (by omega)
  have h20 := twenty_mem_seamGreedySupport s (by omega)
  have h21 := twentyOne_mem_seamGreedySupport s (by omega)
  have h26 := twentySix_mem_seamGreedySupport s (by omega)
  have h27 := twentySeven_mem_seamGreedySupport s (by omega)
  have hsub : ({2, 3, 6, 7, 14, 20, 21, 26, 27} : Finset ℕ) ⊆
      seamWordSupport (seamGreedyWord s) := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h236.1
    · exact h236.2.1
    · exact h236.2.2
    · exact h7
    · exact h14
    · exact h20
    · exact h21
    · exact h26
    · exact h27
  have hsum :
      ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26, 27} : Finset ℕ), rowPulse s d ≤
        ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hexp :
      ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26, 27} : Finset ℕ), rowPulse s d =
        pulseFloor27 s := by
    rw [pulseFloor27_eq_rowPulseSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  change pulseFloor27 s ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport, ← hexp]
  exact hsum

/-! ## PROVED: the auxiliary ratchet -/

/-- One step of the exclusion ratchet, as a function of the pulse charge `P` alone.
The state `b` is an auxiliary budget, and `b = 0` is absorbing.  Its comparison with
`3 * E s - 3` for the concrete seam excess `E` is established only by the conditional
theorem `ratchetRun27_bound`. -/
def ratchetStep (P b : ℕ) : ℕ :=
  if 3 * P + 4 ≤ 4 * b then 4 * b - (3 * P + 3) else 0

theorem ratchetStep_zero (P : ℕ) : ratchetStep P 0 = 0 := by
  unfold ratchetStep; rw [if_neg (by omega)]

/-- **PROVED (auxiliary recurrence):** the step is antitone in the pulse charge and
monotone in the budget. -/
theorem ratchetStep_mono {P P' b b' : ℕ} (hP : P' ≤ P) (hb : b ≤ b') :
    ratchetStep P b ≤ ratchetStep P' b' := by
  unfold ratchetStep; split_ifs <;> omega

/-- Once the budget reaches `12` it can never die, because `pulseFloor27 ≤ 11`. -/
theorem twelve_le_ratchetStep (s b : ℕ) (hb : 12 ≤ b) :
    12 ≤ ratchetStep (pulseFloor27 s) b := by
  have hp := pulseFloor27_le_eleven s
  unfold ratchetStep
  rw [if_pos (by omega)]
  omega

/-- The nine-rank auxiliary orbit initialized with budget `3`.  Interpreting this as
the landing rank `D + 1` of a hypothetical final middle cell requires the separate
hypothesis `seamExcess (D + 1) = 2`; no such concrete landing is measured on
`s ∈ [5, 102]`. -/
def ratchetRun27 (D : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => ratchetStep (pulseFloor27 (D + 1 + k)) (ratchetRun27 D k)

/-- The eight-rank auxiliary orbit used by the rank-`26` phase sieve. -/
def ratchetRun26 (D : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => ratchetStep (pulseFloor26 (D + 1 + k)) (ratchetRun26 D k)

@[simp] theorem ratchetRun27_zero (D : ℕ) : ratchetRun27 D 0 = 3 := rfl

@[simp] theorem ratchetRun26_zero (D : ℕ) : ratchetRun26 D 0 = 3 := rfl

theorem ratchetRun27_succ (D k : ℕ) :
    ratchetRun27 D (k + 1) =
      ratchetStep (pulseFloor27 (D + 1 + k)) (ratchetRun27 D k) := rfl

theorem ratchetRun26_succ (D k : ℕ) :
    ratchetRun26 D (k + 1) =
      ratchetStep (pulseFloor26 (D + 1 + k)) (ratchetRun26 D k) := rfl

/-- **PROVED (auxiliary recurrence):** adjoining rank `27` to the forced support can
only lower the ratchet budget, at every depth and every residue phase. -/
theorem ratchetRun27_le_ratchetRun26 (D k : ℕ) :
    ratchetRun27 D k ≤ ratchetRun26 D k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [ratchetRun27_succ, ratchetRun26_succ]
      exact ratchetStep_mono (pulseFloor26_le_pulseFloor27 _) ih

theorem ratchetRun27_eq_zero_succ (D k : ℕ) (h : ratchetRun27 D k = 0) :
    ratchetRun27 D (k + 1) = 0 := by
  rw [ratchetRun27_succ, h, ratchetStep_zero]

theorem ratchetRun27_eq_zero_add (D k i : ℕ) (h : ratchetRun27 D k = 0) :
    ratchetRun27 D (k + i) = 0 := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      rw [show k + (i + 1) = (k + i) + 1 by ring]
      exact ratchetRun27_eq_zero_succ D _ ih

/-! ## Periodicity -/

theorem ratchetRun27_add_period (D k : ℕ) :
    ratchetRun27 (D + 24570) k = ratchetRun27 D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [ratchetRun27_succ, ratchetRun27_succ, ih,
        show D + 24570 + 1 + k = (D + 1 + k) + 24570 by ring,
        pulseFloor27_add_period]

theorem ratchetRun27_add_mul_period (D k n : ℕ) :
    ratchetRun27 (D + 24570 * n) k = ratchetRun27 D k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show D + 24570 * (n + 1) = (D + 24570 * n) + 24570 by ring,
        ratchetRun27_add_period, ih]

theorem ratchetRun27_mod (D k : ℕ) :
    ratchetRun27 D k = ratchetRun27 (D % 24570) k := by
  conv_lhs => rw [show D = D % 24570 + 24570 * (D / 24570) by
    rw [Nat.add_comm]; exact (Nat.div_add_mod D 24570).symm]
  exact ratchetRun27_add_mul_period _ _ _

/-! ## PROVED CONDITIONAL: bridge to the middle-cell hypotheses

The argument is the one isolated in `Lift/Recon257.lean` for the eight-rank floor,
run against the nine-rank floor and therefore requiring `31 ≤ D` rather than
`27 ≤ D`.  It also requires an all-right concrete seam tail and
`seamExcess (D + 1) = 2`.  Direct evaluation finds no such landing equality on
`s ∈ [5, 102]`, so this section supplies a conditional implication, not an exclusion
of an audited #257 class. -/

/-- The signed excess of the concrete greedy seam above the dyadic half point. -/
def seamExcess (s : ℕ) : ℤ :=
  (seamIntegerGreedyRemainder s : ℤ) - ((2 ^ s : ℕ) : ℤ)

/-- **PROVED CONDITIONAL:** the nine-rank ratchet budget dominates
`3 * seamExcess - 3` along an all-right-tail orbit with landing excess `2`. -/
theorem ratchetRun27_bound
    (D : ℕ) (hD31 : 31 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : seamExcess (D + 1) = 2) :
    ∀ k, 3 * seamExcess (D + 1 + k) - 3 ≤ (ratchetRun27 D k : ℤ) := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  intro k
  induction k with
  | zero =>
      simp only [Nat.add_zero, ratchetRun27_zero, hlanding]
      norm_num
  | succ k ih =>
      have hs : D + 1 ≤ D + 1 + k := by omega
      have hstep := (horbit (D + 1 + k) hs).2
      have hrec : seamExcess (D + 1 + (k + 1)) =
          4 * seamExcess (D + 1 + k) -
            ((seamAdjacentCut (D + 1 + k)
              (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) - 4 := by
        simpa [seamExcess, show D + 1 + (k + 1) = (D + 1 + k) + 1 by ring] using hstep
      have hfloor : (pulseFloor27 (D + 1 + k) : ℤ) ≤
          ((seamAdjacentCut (D + 1 + k)
            (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
        exact_mod_cast pulseFloor27_le_belowPulse (D + 1 + k) (by omega)
      have hmain : 3 * seamExcess (D + 1 + (k + 1)) - 3 ≤
          4 * (ratchetRun27 D k : ℤ) -
            (3 * (pulseFloor27 (D + 1 + k) : ℤ) + 3) := by
        rw [hrec]; omega
      rw [ratchetRun27_succ]
      unfold ratchetStep
      split_ifs with hcond
      · have hle : 3 * pulseFloor27 (D + 1 + k) + 3 ≤ 4 * ratchetRun27 D k := by omega
        have hcast :
            ((4 * ratchetRun27 D k - (3 * pulseFloor27 (D + 1 + k) + 3) : ℕ) : ℤ) =
              4 * (ratchetRun27 D k : ℤ) -
                (3 * (pulseFloor27 (D + 1 + k) : ℤ) + 3) := by
          push_cast [Nat.cast_sub hle]
          ring
        rw [hcast]
        exact hmain
      · have hcondZ : 4 * (ratchetRun27 D k : ℤ) ≤
            3 * (pulseFloor27 (D + 1 + k) : ℤ) + 3 := by
          have hnat : 4 * ratchetRun27 D k ≤ 3 * pulseFloor27 (D + 1 + k) + 3 := by omega
          exact_mod_cast hnat
        simp only [Nat.cast_zero]
        omega

/-- **PROVED CONDITIONAL:** if the auxiliary budget of `D` dies, then an all-right
concrete seam tail with landing excess `2` is contradictory.  The theorem does not
assert that any `D` realizes the landing hypothesis. -/
theorem ratchet27_excludes
    (D : ℕ) (hD31 : 31 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : seamExcess (D + 1) = 2)
    (k : ℕ) (hdead : ratchetRun27 D k = 0) : False := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  have hbound := ratchetRun27_bound D hD31 hright hlanding k
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
        ((seamAdjacentCut (D + 1 + k)
          (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) - 4 := by
    simpa [seamExcess] using hstep
  have hnext : 0 < seamExcess (D + 1 + k + 1) := by
    have := (horbit (D + 1 + k + 1) (by omega)).1
    simpa [seamExcess] using this
  have hfloor : (pulseFloor27 (D + 1 + k) : ℤ) ≤
      ((seamAdjacentCut (D + 1 + k)
        (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
    exact_mod_cast pulseFloor27_le_belowPulse (D + 1 + k) (by omega)
  have hone' : (1 : ℤ) ≤ (pulseFloor27 (D + 1 + k) : ℤ) := by
    exact_mod_cast one_le_pulseFloor27 (D + 1 + k)
  rw [hone] at hrec
  omega

/-- **PROVED CONDITIONAL:** the displayed no-carry, middle-branch, and charge
hypotheses imply landing excess `2`.  The theorem does not assert that those
hypotheses are jointly realized by the concrete seam. -/
theorem seamExcess_landing_eq_two
    (D : ℕ) (hD5 : 5 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D hD5).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D hD5).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D hD5).belowPulse <
          (seamAdjacentCut D hD5).terminalWeight)
    (hcell :
      4 * ((seamAdjacentCut D hD5).remainder : ℤ) -
          ((seamAdjacentCut D hD5).belowPulse : ℤ) - 4 = -2) :
    seamExcess (D + 1) = 2 := by
  have hmiddleRec := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    hD5 hncarry hmiddle
  have hmiddleRecZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hmiddleRec
  push_cast at hmiddleRecZ
  have hcellR :
      4 * (seamIntegerGreedyRemainder D : ℤ) -
          ((seamAdjacentCut D hD5).belowPulse : ℤ) - 4 = -2 := by
    simpa [seamAdjacentCut_remainder] using hcell
  unfold seamExcess
  push_cast
  omega

/-! ## PROVED: the auxiliary finite core at modulus `24570`

`Nat.decidableBallLT` recurses once per residue phase, and a single kernel evaluation
over all `24570` phases overflows the kernel stack.  The check is therefore split into nine
blocks of `2730`, each of the size the rank-`26` sieve already uses. -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
private theorem core_block0 :
    ∀ r < 2730, ratchetRun27 (2730 * 0 + r) 6 = 0 ∨
      12 ≤ ratchetRun27 (2730 * 0 + r) 6 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
private theorem core_block1 :
    ∀ r < 2730, ratchetRun27 (2730 * 1 + r) 6 = 0 ∨
      12 ≤ ratchetRun27 (2730 * 1 + r) 6 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
private theorem core_block2 :
    ∀ r < 2730, ratchetRun27 (2730 * 2 + r) 6 = 0 ∨
      12 ≤ ratchetRun27 (2730 * 2 + r) 6 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
private theorem core_block3 :
    ∀ r < 2730, ratchetRun27 (2730 * 3 + r) 6 = 0 ∨
      12 ≤ ratchetRun27 (2730 * 3 + r) 6 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
private theorem core_block4 :
    ∀ r < 2730, ratchetRun27 (2730 * 4 + r) 6 = 0 ∨
      12 ≤ ratchetRun27 (2730 * 4 + r) 6 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
private theorem core_block5 :
    ∀ r < 2730, ratchetRun27 (2730 * 5 + r) 6 = 0 ∨
      12 ≤ ratchetRun27 (2730 * 5 + r) 6 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
private theorem core_block6 :
    ∀ r < 2730, ratchetRun27 (2730 * 6 + r) 6 = 0 ∨
      12 ≤ ratchetRun27 (2730 * 6 + r) 6 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
private theorem core_block7 :
    ∀ r < 2730, ratchetRun27 (2730 * 7 + r) 6 = 0 ∨
      12 ≤ ratchetRun27 (2730 * 7 + r) 6 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
private theorem core_block8 :
    ∀ r < 2730, ratchetRun27 (2730 * 8 + r) 6 = 0 ∨
      12 ≤ ratchetRun27 (2730 * 8 + r) 6 := by
  decide +kernel

/-- **PROVED (auxiliary recurrence):** on all `24570` joint phases, by depth `6`
every phase is either dead or already past the escape threshold `12`.  There is no
intermediate regime, so the auxiliary phase set is settled at depth `6`. -/
theorem ratchet27_finite_core :
    ∀ D < 24570, ratchetRun27 D 6 = 0 ∨ 12 ≤ ratchetRun27 D 6 := by
  intro D hD
  have hr : D % 2730 < 2730 := Nat.mod_lt _ (by norm_num)
  have h9 : D = 2730 * 0 + D % 2730 ∨ D = 2730 * 1 + D % 2730 ∨
      D = 2730 * 2 + D % 2730 ∨ D = 2730 * 3 + D % 2730 ∨
      D = 2730 * 4 + D % 2730 ∨ D = 2730 * 5 + D % 2730 ∨
      D = 2730 * 6 + D % 2730 ∨ D = 2730 * 7 + D % 2730 ∨
      D = 2730 * 8 + D % 2730 := by omega
  rcases h9 with h | h | h | h | h | h | h | h | h
  · rw [h]; exact core_block0 _ hr
  · rw [h]; exact core_block1 _ hr
  · rw [h]; exact core_block2 _ hr
  · rw [h]; exact core_block3 _ hr
  · rw [h]; exact core_block4 _ hr
  · rw [h]; exact core_block5 _ hr
  · rw [h]; exact core_block6 _ hr
  · rw [h]; exact core_block7 _ hr
  · rw [h]; exact core_block8 _ hr

/-- **PROVED (auxiliary recurrence):** every residue phase alive at depth `6` is
alive at every depth.  Thus the phase set is a fixed point of this recurrence. -/
theorem ratchetRun27_pos_of_alive (D : ℕ) (h : ratchetRun27 D 6 ≠ 0) :
    ∀ k, 0 < ratchetRun27 D k := by
  have hlt : D % 24570 < 24570 := Nat.mod_lt _ (by norm_num)
  have hcore := ratchet27_finite_core _ hlt
  rw [← ratchetRun27_mod] at hcore
  have hsix : 12 ≤ ratchetRun27 D 6 := by
    rcases hcore with hc | hc
    · exact absurd hc h
    · exact hc
  have hgrow : ∀ j, 12 ≤ ratchetRun27 D (6 + j) := by
    intro j
    induction j with
    | zero => exact hsix
    | succ j ih =>
        rw [show 6 + (j + 1) = (6 + j) + 1 by ring, ratchetRun27_succ]
        exact twelve_le_ratchetStep _ _ ih
  intro k
  rcases Nat.lt_or_ge k 6 with hk | hk
  · by_contra hcon
    have h0 : ratchetRun27 D k = 0 := by omega
    have hk6 := ratchetRun27_eq_zero_add D k (6 - k) h0
    rw [show k + (6 - k) = 6 by omega] at hk6
    exact h hk6
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
    rw [hj]
    exact lt_of_lt_of_le (by norm_num) (hgrow j)

/-! ## PROVED: auxiliary rank-`26` phases and strict shrinking -/

/-- The joint residue conditions cut out by the auxiliary rank-`26` sieve: the defining
predicate of `finalMiddleTwentySixPhaseSurvivors`, whose `Finset` has cardinality
`412`. -/
def SurvivorPhase26 (D : ℕ) : Prop :=
  D % 21 ∈ ({11, 14, 17, 20} : Finset ℕ) ∧
    D % 10 ≠ 8 ∧
    ¬ (D % 10 = 7 ∧ D % 21 = 11) ∧
    D % 13 ≠ 11 ∧
    ¬ (D % 13 = 10 ∧ D % 21 = 11)

instance (D : ℕ) : Decidable (SurvivorPhase26 D) := by
  unfold SurvivorPhase26; infer_instance

theorem survivorPhase26_mod (D : ℕ) :
    SurvivorPhase26 D ↔ SurvivorPhase26 (D % 2730) := by
  have h21 : D % 2730 % 21 = D % 21 :=
    Nat.mod_mod_of_dvd D (by norm_num : (21 : ℕ) ∣ 2730)
  have h10 : D % 2730 % 10 = D % 10 :=
    Nat.mod_mod_of_dvd D (by norm_num : (10 : ℕ) ∣ 2730)
  have h13 : D % 2730 % 13 = D % 13 :=
    Nat.mod_mod_of_dvd D (by norm_num : (13 : ℕ) ∣ 2730)
  unfold SurvivorPhase26
  rw [h21, h10, h13]

theorem pulseFloor26_add_period (s : ℕ) :
    pulseFloor26 (s + 2730) = pulseFloor26 s := by
  have h2 : pulseAt (s + 2730) 2 = pulseAt s 2 := by
    unfold pulseAt; split_ifs <;> omega
  have h3 : pulseAt (s + 2730) 3 = pulseAt s 3 := by
    unfold pulseAt; split_ifs <;> omega
  have h6 : pulseAt (s + 2730) 6 = pulseAt s 6 := by
    unfold pulseAt; split_ifs <;> omega
  have h7 : pulseAt (s + 2730) 7 = pulseAt s 7 := by
    unfold pulseAt; split_ifs <;> omega
  have h14 : pulseAt (s + 2730) 14 = pulseAt s 14 := by
    unfold pulseAt; split_ifs <;> omega
  have h20 : pulseAt (s + 2730) 20 = pulseAt s 20 := by
    unfold pulseAt; split_ifs <;> omega
  have h21 : pulseAt (s + 2730) 21 = pulseAt s 21 := by
    unfold pulseAt; split_ifs <;> omega
  have h26 : pulseAt (s + 2730) 26 = pulseAt s 26 := by
    unfold pulseAt; split_ifs <;> omega
  unfold pulseFloor26
  rw [h2, h3, h6, h7, h14, h20, h21, h26]

theorem ratchetRun26_add_period (D k : ℕ) :
    ratchetRun26 (D + 2730) k = ratchetRun26 D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [ratchetRun26_succ, ratchetRun26_succ, ih,
        show D + 2730 + 1 + k = (D + 1 + k) + 2730 by ring,
        pulseFloor26_add_period]

theorem ratchetRun26_add_mul_period (D k n : ℕ) :
    ratchetRun26 (D + 2730 * n) k = ratchetRun26 D k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show D + 2730 * (n + 1) = (D + 2730 * n) + 2730 by ring,
        ratchetRun26_add_period, ih]

theorem ratchetRun26_mod (D k : ℕ) :
    ratchetRun26 D k = ratchetRun26 (D % 2730) k := by
  conv_lhs => rw [show D = D % 2730 + 2730 * (D / 2730) by
    rw [Nat.add_comm]; exact (Nat.div_add_mod D 2730).symm]
  exact ratchetRun26_add_mul_period _ _ _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **PROVED (auxiliary recurrence):** the eight-rank ratchet reproduces the
rank-`26` phase sieve: every non-surviving phase is dead by depth `3`. -/
theorem ratchet26_finite_core :
    ∀ D < 2730, SurvivorPhase26 D ∨ ratchetRun26 D 3 = 0 := by
  decide +kernel

theorem survivorPhase26_of_ratchetRun26_ne_zero
    (D : ℕ) (h : ratchetRun26 D 3 ≠ 0) : SurvivorPhase26 D := by
  have hlt : D % 2730 < 2730 := Nat.mod_lt _ (by norm_num)
  rcases ratchet26_finite_core _ hlt with hc | hc
  · exact (survivorPhase26_mod D).2 hc
  · exact absurd (by rw [ratchetRun26_mod]; exact hc) h

/-- **PROVED (auxiliary recurrence):** a phase alive at rank `27` is alive at
rank `26`, by monotone refinement and the eight-rank finite core. -/
theorem survivorPhase26_of_ratchetRun27_ne_zero
    (D : ℕ) (h : ratchetRun27 D 6 ≠ 0) : SurvivorPhase26 D := by
  apply survivorPhase26_of_ratchetRun26_ne_zero
  intro hzero
  apply h
  have h36 : ratchetRun26 D 6 = 0 := by
    have hstep : ∀ j, ratchetRun26 D j = 0 → ratchetRun26 D (j + 1) = 0 := by
      intro j hj
      rw [ratchetRun26_succ, hj, ratchetStep_zero]
    have h4 := hstep 3 hzero
    have h5 := hstep 4 h4
    exact hstep 5 h5
  have hle := ratchetRun27_le_ratchetRun26 D 6
  omega

/-! ## PROVED: two auxiliary phase sets at modulus `24570` -/

/-- The lift to modulus `24570` of the `412` surviving auxiliary rank-`26` phases. -/
def liftedSurvivors26 : Finset ℕ :=
  (Finset.range 24570).filter SurvivorPhase26

/-- The surviving phases of the nine-rank auxiliary recurrence at modulus `24570`.
Membership does not assert realizability by a concrete #257 configuration. -/
def survivors27 : Finset ℕ :=
  (Finset.range 24570).filter (fun D ↦ ratchetRun27 D 6 ≠ 0)

theorem mem_liftedSurvivors26_iff_mem_sieve (D : ℕ) (hD : D < 24570) :
    D ∈ liftedSurvivors26 ↔
      D % 2730 ∈ finalMiddleTwentySixPhaseSurvivors := by
  have hmod : D % 2730 < 2730 := Nat.mod_lt _ (by norm_num)
  unfold liftedSurvivors26 finalMiddleTwentySixPhaseSurvivors
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_range, hD, hmod, true_and]
  exact survivorPhase26_mod D

theorem survivors27_subset_liftedSurvivors26 :
    survivors27 ⊆ liftedSurvivors26 := by
  intro D hD
  unfold survivors27 at hD
  unfold liftedSurvivors26
  rw [Finset.mem_filter] at hD ⊢
  exact ⟨hD.1, survivorPhase26_of_ratchetRun27_ne_zero D hD.2⟩

/-- The explicit auxiliary phase killed by rank `27`: `D = 200`.  It satisfies every
rank-`26` residue condition (`200 % 21 = 11`, `200 % 10 = 0`, `200 % 13 = 5`) but its
nine-rank budget dies at depth `3`, because `200 + 2 = 202 ≡ 13 (mod 27)` puts the
double rank-`27` pulse at the second row of the orbit. -/
theorem twoHundred_mem_liftedSurvivors26 : 200 ∈ liftedSurvivors26 := by
  unfold liftedSurvivors26
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (by norm_num), by decide⟩

theorem twoHundred_not_mem_survivors27 : 200 ∉ survivors27 := by
  unfold survivors27
  rw [Finset.mem_filter]
  rintro ⟨-, hne⟩
  exact hne (by decide)

/-- **PROVED (auxiliary recurrence):** the nine-rank phase set is a proper subset
of the lift of the rank-`26` phase set. -/
theorem survivors27_ssubset_liftedSurvivors26 :
    survivors27 ⊂ liftedSurvivors26 :=
  (Finset.ssubset_iff_of_subset survivors27_subset_liftedSurvivors26).2
    ⟨200, twoHundred_mem_liftedSurvivors26, twoHundred_not_mem_survivors27⟩

/-- **PROVED (auxiliary recurrence):** the phase-set cardinality strictly shrinks.
The exact full-modulus counts `3522` and `3708 = 9 * 412` are **MEASURED** outside
Lean, not asserted by this theorem. -/
theorem survivors27_card_lt :
    survivors27.card < liftedSurvivors26.card :=
  Finset.card_lt_card survivors27_ssubset_liftedSurvivors26

/-! ### The count on the base residue block

The auxiliary set `survivors27` lives modulo `24570`, and a kernel evaluation of its cardinality
overflows the stack.  Its intersection with the base block `[0, 2730)` is the same
size of computation as the existing rank-`26` count, and is exhibited here: the
rank-`26` recurrence keeps `412` phases there and the rank-`27` recurrence keeps
`390`. -/

/-- The auxiliary rank-`27` phases inside the base residue block `[0, 2730)`. -/
def survivors27Base : Finset ℕ :=
  (Finset.range 2730).filter (fun r ↦ ratchetRun27 r 6 ≠ 0)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 40000 in
/-- **PROVED (auxiliary recurrence):** `412` becomes `390` on the base block. -/
theorem survivors27Base_card : survivors27Base.card = 390 := by
  decide +kernel

theorem survivors27Base_subset :
    survivors27Base ⊆ finalMiddleTwentySixPhaseSurvivors := by
  intro r hr
  unfold survivors27Base at hr
  rw [Finset.mem_filter] at hr
  have hphase := survivorPhase26_of_ratchetRun27_ne_zero r hr.2
  unfold SurvivorPhase26 at hphase
  unfold finalMiddleTwentySixPhaseSurvivors
  rw [Finset.mem_filter]
  exact ⟨hr.1, hphase⟩

theorem twoHundred_mem_finalMiddleTwentySixPhaseSurvivors :
    200 ∈ finalMiddleTwentySixPhaseSurvivors := by
  unfold finalMiddleTwentySixPhaseSurvivors
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (by norm_num), by decide⟩

theorem twoHundred_not_mem_survivors27Base : 200 ∉ survivors27Base := by
  unfold survivors27Base
  rw [Finset.mem_filter]
  rintro ⟨-, hne⟩
  exact hne (by decide)

theorem survivors27Base_ssubset :
    survivors27Base ⊂ finalMiddleTwentySixPhaseSurvivors :=
  (Finset.ssubset_iff_of_subset survivors27Base_subset).2
    ⟨200, twoHundred_mem_finalMiddleTwentySixPhaseSurvivors,
      twoHundred_not_mem_survivors27Base⟩

/-- The quantitative form: `390 < 412`, with both sides certified — the right-hand
count is `finalMiddleTwentySixPhaseSurvivors_card` from the sieve file. -/
theorem survivors27Base_card_lt :
    survivors27Base.card < finalMiddleTwentySixPhaseSurvivors.card :=
  Finset.card_lt_card survivors27Base_ssubset

/-! ## PROVED CONDITIONAL: the rank-`27` phase classification -/

/-- **PROVED CONDITIONAL:** the displayed no-carry, middle-branch, all-right-tail,
and charge hypotheses force `D % 24570` into the auxiliary set `survivors27`.
No audited concrete landing instance satisfies the implied equality
`seamExcess (D + 1) = 2` on `D + 1 ∈ [5, 102]`. -/
theorem finalMiddleCell_neg_two_mem_survivors27
    (D : ℕ) (hD31 : 31 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega : 5 ≤ D)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega : 5 ≤ D)).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse <
          (seamAdjacentCut D (by omega : 5 ≤ D)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega : 5 ≤ D)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse : ℤ) - 4 = -2) :
    D % 24570 ∈ survivors27 := by
  have hlanding := seamExcess_landing_eq_two D (by omega) hncarry hmiddle hcell
  have halive : ratchetRun27 D 6 ≠ 0 := by
    intro hzero
    exact ratchet27_excludes D hD31 hright hlanding 6 hzero
  unfold survivors27
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)), ?_⟩
  rw [← ratchetRun27_mod]
  exact halive

/-! ## PROVED limits of the auxiliary recurrence

Two statements.  First, the *budget* a new forced rank can ever supply: over any
window of `27` consecutive rows, rank `27` contributes exactly `3` units of pulse —
one from `27 ∣ 2s+2` and two from `27 ∣ 2s+1`.  This is the exact form of the
heuristic "a forced rank `d` is worth at most `3` units per `d` consecutive rows".
The exact window identity is proved below; the discounted asymptotic interpretation
is explanatory prose about the auxiliary recurrence.

Second, the consequence: an explicit auxiliary phase that the nine-rank recurrence
never kills. -/

theorem pulseAt_twentySeven_period (s : ℕ) :
    pulseAt (s + 27) 27 = pulseAt s 27 := by
  unfold pulseAt; split_ifs <;> omega

/-- **The exact budget of the new forced rank.**  Rank `27` supplies exactly three
units of pulse per `27` consecutive rows, wherever the window starts. -/
theorem pulseAt_twentySeven_window (s : ℕ) :
    ∑ j ∈ Finset.range 27, pulseAt (s + j) 27 = 3 := by
  induction s with
  | zero => decide +kernel
  | succ s ih =>
      have hA : ∑ j ∈ Finset.range 28, pulseAt (s + j) 27 =
          (∑ j ∈ Finset.range 27, pulseAt (s + (j + 1)) 27) + pulseAt (s + 0) 27 :=
        Finset.sum_range_succ' (fun j ↦ pulseAt (s + j) 27) 27
      have hB : ∑ j ∈ Finset.range 28, pulseAt (s + j) 27 =
          (∑ j ∈ Finset.range 27, pulseAt (s + j) 27) + pulseAt (s + 27) 27 :=
        Finset.sum_range_succ (fun j ↦ pulseAt (s + j) 27) 27
      have hC : ∑ j ∈ Finset.range 27, pulseAt (s + 1 + j) 27 =
          ∑ j ∈ Finset.range 27, pulseAt (s + (j + 1)) 27 :=
        Finset.sum_congr rfl (fun j _ ↦ by rw [show s + 1 + j = s + (j + 1) by omega])
      have hD : pulseAt (s + 27) 27 = pulseAt (s + 0) 27 := by
        rw [Nat.add_zero]
        exact pulseAt_twentySeven_period s
      rw [hC]
      omega

/-- **PROVED (auxiliary recurrence):** the phase `D ≡ 14 (mod 24570)` survives the
nine-rank ratchet.  This does not certify a concrete seam landing at that residue. -/
theorem fourteen_mem_survivors27 : 14 ∈ survivors27 := by
  unfold survivors27
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (by norm_num), by decide +kernel⟩

theorem survivors27_nonempty : survivors27.Nonempty :=
  ⟨14, fourteen_mem_survivors27⟩

/-- **PROVED (auxiliary recurrence):** the nine-rank ratchet has a permanently
positive budget on phase `14`; no depth of this recurrence excludes it.  Therefore
adding rank `27` removes some auxiliary phases and then stalls.  This is not a
statement that the `1/2`-membership branch contains or realizes phase `14`. -/
theorem ratchetRun27_pos_fourteen : ∀ k, 0 < ratchetRun27 14 k :=
  ratchetRun27_pos_of_alive 14 (by decide +kernel)

end AngleB1

end Erdos249257
