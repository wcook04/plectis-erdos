import Erdos249257.HalfCylinderMiddleCarryLowerBound
import Erdos249257.HalfCylinderFinalMiddleTailSocket
import Erdos249257.HalfCylinderFiniteShadow

/-!
# A finite phase sieve for the final `-2` middle cell

The existing lazy-tail argument forces a hypothetical final middle cell of
charge `-2` into the phase `D = 2 (mod 3)`.  The exact middle landing then
starts the all-right signed excess at `2`.  Forced ranks `2`, `3`, `6`, `7`,
and `14` leave only five joint `21`-phases.  The exact prefix through rank
`20` and `21` sharpen that sieve to thirty-five classes modulo `210`.  The
next forced rank is `26`; its pulse removes a full phase modulo `13` and one
additional joint phase, leaving 412 classes modulo `2730`.
-/

namespace Erdos249257

open Set
open HalfCylinderIntegerGreedy
open HalfCylinderFiniteShadow
open scoped BigOperators

noncomputable section

/-! ## Public prerequisites for the phase sieve -/

/-- A finite support contributes at most one divisor per support element. -/

private theorem pair_rowPulse_le_wordPulse
    {s a b : ℕ} (hab : a ≠ b)
    (ha : a ∈ seamWordSupport (seamGreedyWord s))
    (hb : b ∈ seamWordSupport (seamGreedyWord s)) :
    rowPulse s a + rowPulse s b ≤
      wordPulse s (seamGreedyWord s).toNatWord := by
  classical
  rw [wordPulse_eq_sum_seamWordSupport]
  calc
    rowPulse s a + rowPulse s b =
        ∑ d ∈ ({a, b} : Finset ℕ), rowPulse s d := by
          simp [hab]
    _ ≤ ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact ha
        · exact hb
      · intro d _ _
        omega

private theorem rowPulse_le_wordPulse
    {s d : ℕ} (hd : d ∈ seamWordSupport (seamGreedyWord s)) :
    rowPulse s d ≤ wordPulse s (seamGreedyWord s).toNatWord := by
  classical
  rw [wordPulse_eq_sum_seamWordSupport]
  exact Finset.single_le_sum (fun e _ ↦ Nat.zero_le (rowPulse s e)) hd

private theorem three_le_belowPulse_of_mod_three_one
    (s : ℕ) (hs13 : 13 ≤ s) (hmod : s % 3 = 1) :
    3 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  have hmem := two_three_six_mem_seamGreedySupport s hs13
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have h3odd : 3 ∣ 2 * s + 1 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h3even : ¬ 3 ∣ 2 * s + 2 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp3 : rowPulse s 3 = 2 := by
    simp [rowPulse, h3even, h3odd]
  have hp := pair_rowPulse_le_wordPulse
    (s := s) (a := 2) (b := 3) (by norm_num) hmem.1 hmem.2.1
  change 3 ≤ wordPulse s (seamGreedyWord s).toNatWord
  omega

private theorem three_le_belowPulse_of_mod_three_two
    (s : ℕ) (hs13 : 13 ≤ s) (hmod : s % 3 = 2) :
    3 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  classical
  have hmem := two_three_six_mem_seamGreedySupport s hs13
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have h3even : 3 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h3odd : ¬ 3 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have h6even : 6 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h6odd : ¬ 6 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp3 : rowPulse s 3 = 1 := by
    simp [rowPulse, h3even, h3odd]
  have hp6 : rowPulse s 6 = 1 := by
    simp [rowPulse, h6even, h6odd]
  change 3 ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  calc
    3 = ∑ d ∈ ({2, 3, 6} : Finset ℕ), rowPulse s d := by
      simp [hp2, hp3, hp6]
    _ ≤ ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact hmem.1
        · exact hmem.2.1
        · exact hmem.2.2
      · intro d _ _
        omega

private theorem three_le_belowPulse_of_mod_seven_three
    (s : ℕ) (hs14 : 14 ≤ s) (hmod : s % 7 = 3) :
    3 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  have h2mem :=
    (two_three_six_mem_seamGreedySupport s (by omega : 13 ≤ s)).1
  have h7mem := seven_mem_seamGreedySupport s hs14
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have h7odd : 7 ∣ 2 * s + 1 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h7even : ¬ 7 ∣ 2 * s + 2 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp7 : rowPulse s 7 = 2 := by
    simp [rowPulse, h7even, h7odd]
  have hp := pair_rowPulse_le_wordPulse
    (s := s) (a := 2) (b := 7) (by norm_num) h2mem h7mem
  change 3 ≤ wordPulse s (seamGreedyWord s).toNatWord
  omega

/-! ## A longer forced seam prefix -/

/-- From row twenty onward, the remainder after the forced ranks
`2,3,6,7` skips every rank from `8` through `13` and then takes rank `14`.
The two common-denominator estimates are exact: adding rank `13` pushes the
reciprocal sum above one half, whereas adding rank `14` leaves deficit
`1 / 688086`; the dyadic side term fits inside that deficit once `s ≥ 20`. -/
theorem seamGreedy_postSeven_decisions_through_fourteen
    (s : ℕ) (hs : 20 ≤ s) :
    let R := seamSubsetTarget s - truncatedMersenneWeight s 2 -
      truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
      truncatedMersenneWeight s 7
    R < truncatedMersenneWeight s 8 ∧
      R < truncatedMersenneWeight s 9 ∧
      R < truncatedMersenneWeight s 10 ∧
      R < truncatedMersenneWeight s 11 ∧
      R < truncatedMersenneWeight s 12 ∧
      R < truncatedMersenneWeight s 13 ∧
      truncatedMersenneWeight s 14 ≤ R := by
  dsimp only
  let X := 4 ^ s
  let w2 := truncatedMersenneWeight s 2
  let w3 := truncatedMersenneWeight s 3
  let w6 := truncatedMersenneWeight s 6
  let w7 := truncatedMersenneWeight s 7
  let w13 := truncatedMersenneWeight s 13
  let w14 := truncatedMersenneWeight s 14
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
  have hpow9 : 4 ^ 9 ≤ X := by
    dsimp [X]
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < (4 : ℕ)) (by omega : 9 ≤ s))
  have hw2Lower : X < 3 * (w2 + 1) := by
    dsimp [X, w2, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 3))
  have hw3Lower : X < 7 * (w3 + 1) := by
    dsimp [X, w3, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 7))
  have hw6Lower : X < 63 * (w6 + 1) := by
    dsimp [X, w6, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 63))
  have hw7Lower : X < 127 * (w7 + 1) := by
    dsimp [X, w7, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 127))
  have hw13Lower : X < 8191 * (w13 + 1) := by
    dsimp [X, w13, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 8191))
  have h2s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 21845397)).2 hw2Lower
  have h3s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 9362313)).2 hw3Lower
  have h6s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 1040257)).2 hw6Lower
  have h7s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 516033)).2 hw7Lower
  have h13s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 8001)).2 hw13Lower
  have hsumLower :
      32772001 * X < 65536191 * (w2 + w3 + w6 + w7 + w13 + 5) := by
    omega
  have hyA : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have htargetAdd : seamSubsetTarget s + 2 ^ s = 2 ^ (2 * s - 1) := by
    unfold seamSubsetTarget
    omega
  have hpowA : 131072 ≤ 2 ^ (2 * s - 1) := by
    omega
  have htwoy : 2 * 2 ^ s ≤ 2 ^ (2 * s - 1) := by
    calc
      2 * 2 ^ s = 2 ^ (s + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (2 * s - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have htargetBig : 65536 ≤ seamSubsetTarget s := by
    omega
  have htarget_lt_sum :
      seamSubsetTarget s < w2 + w3 + w6 + w7 + w13 := by
    by_contra hnot
    have hle : w2 + w3 + w6 + w7 + w13 ≤ seamSubsetTarget s :=
      Nat.le_of_not_gt hnot
    omega
  have hskip13 :
      seamSubsetTarget s - w2 - w3 - w6 - w7 < w13 := by
    omega
  have hmono8 : w13 ≤ truncatedMersenneWeight s 8 := by
    dsimp [w13, truncatedMersenneWeight]
    apply Nat.div_le_div_left
    · norm_num
    · norm_num
  have hmono9 : w13 ≤ truncatedMersenneWeight s 9 := by
    dsimp [w13, truncatedMersenneWeight]
    apply Nat.div_le_div_left
    · norm_num
    · norm_num
  have hmono10 : w13 ≤ truncatedMersenneWeight s 10 := by
    dsimp [w13, truncatedMersenneWeight]
    apply Nat.div_le_div_left
    · norm_num
    · norm_num
  have hmono11 : w13 ≤ truncatedMersenneWeight s 11 := by
    dsimp [w13, truncatedMersenneWeight]
    apply Nat.div_le_div_left
    · norm_num
    · norm_num
  have hmono12 : w13 ≤ truncatedMersenneWeight s 12 := by
    dsimp [w13, truncatedMersenneWeight]
    apply Nat.div_le_div_left
    · norm_num
    · norm_num

  have hpow20 : 688086 ≤ 2 ^ s := by
    have hmono : 2 ^ 20 ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hmono ⊢
    omega
  have hside : 688086 * 2 ^ s ≤ X := by
    have hmul := Nat.mul_le_mul_right (2 ^ s) hpow20
    calc
      688086 * 2 ^ s ≤ 2 ^ s * 2 ^ s := hmul
      _ = X := by
        dsimp [X]
        rw [← pow_add, show s + s = 2 * s by omega]
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
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
  have h2u := Nat.mul_le_mul_left 114681 hw2Upper
  have h3u := Nat.mul_le_mul_left 49149 hw3Upper
  have h6u := Nat.mul_le_mul_left 5461 hw6Upper
  have h7u := Nat.mul_le_mul_left 2709 hw7Upper
  have h14u := Nat.mul_le_mul_left 21 hw14Upper
  have hsumUpper :
      344043 * (w2 + w3 + w6 + w7 + w14) ≤ 172021 * X := by
    omega
  have htake14 : w14 ≤
      seamSubsetTarget s - w2 - w3 - w6 - w7 := by
    unfold seamSubsetTarget
    omega
  dsimp [w2, w3, w6, w7, w14] at htake14
  dsimp [w2, w3, w6, w7, w13] at hskip13
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  exact ⟨hskip13, htake14⟩

/-- List-level normal form of the forced seam decisions through rank `14`. -/
theorem seamGreedyBits_head2367_14
    (s : ℕ) (hs : 20 ≤ s) :
    integerGreedyBits (seamWeights s) (seamSubsetTarget s) =
      true :: true :: false :: false :: true :: true ::
        false :: false :: false :: false :: false :: false :: true ::
          integerGreedyBits (seamWeightsFrom s 15)
            (seamSubsetTarget s - truncatedMersenneWeight s 2 -
              truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
              truncatedMersenneWeight s 7 - truncatedMersenneWeight s 14) := by
  rcases seamGreedy_postSeven_decisions_through_fourteen s hs with
    ⟨h8, h9, h10, h11, h12, h13, h14⟩
  rw [seamGreedyBits_head2367 s (by omega : 14 ≤ s),
    seamWeightsFrom_eq_cons (by omega : 8 < s),
    seamWeightsFrom_eq_cons (by omega : 9 < s),
    seamWeightsFrom_eq_cons (by omega : 10 < s),
    seamWeightsFrom_eq_cons (by omega : 11 < s),
    seamWeightsFrom_eq_cons (by omega : 12 < s),
    seamWeightsFrom_eq_cons (by omega : 13 < s),
    seamWeightsFrom_eq_cons (by omega : 14 < s)]
  simp only [integerGreedyBits]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h14]

/-- Rank `14` is a fifth mandatory selected seam rank from row twenty onward. -/
theorem fourteen_mem_seamGreedySupport
    (s : ℕ) (hs : 20 ≤ s) :
    14 ∈ seamWordSupport (seamGreedyWord s) := by
  have hbits := seamGreedyBits_head2367_14 s hs
  apply mem_seamWordSupport_iff.mpr
  refine ⟨⟨12, by omega⟩, ?_, by norm_num⟩
  simp [seamGreedyWord, SeamRowWord.ofList, hbits]

/-- After the forced rank `14`, rows `s ≥ 21` skip ranks `15` through `19`
and take rank `20`.  The skip comparison uses the positive excess
`163799 / 360754544682` above one half after adjoining rank `19`; the take
comparison uses the deficit `120163 / 240503259150` below one half after
adjoining rank `20`. -/
theorem seamGreedy_postFourteen_decisions_through_twenty
    (s : ℕ) (hs : 21 ≤ s) :
    let R := seamSubsetTarget s - truncatedMersenneWeight s 2 -
      truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
      truncatedMersenneWeight s 7 - truncatedMersenneWeight s 14
    R < truncatedMersenneWeight s 15 ∧
      R < truncatedMersenneWeight s 16 ∧
      R < truncatedMersenneWeight s 17 ∧
      R < truncatedMersenneWeight s 18 ∧
      R < truncatedMersenneWeight s 19 ∧
      truncatedMersenneWeight s 20 ≤ R := by
  dsimp only
  let X := 4 ^ s
  let w2 := truncatedMersenneWeight s 2
  let w3 := truncatedMersenneWeight s 3
  let w6 := truncatedMersenneWeight s 6
  let w7 := truncatedMersenneWeight s 7
  let w14 := truncatedMersenneWeight s 14
  let w19 := truncatedMersenneWeight s 19
  let w20 := truncatedMersenneWeight s 20
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

  have hw2Lower : X < 3 * (w2 + 1) := by
    dsimp [X, w2, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 3))
  have hw3Lower : X < 7 * (w3 + 1) := by
    dsimp [X, w3, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 7))
  have hw6Lower : X < 63 * (w6 + 1) := by
    dsimp [X, w6, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 63))
  have hw7Lower : X < 127 * (w7 + 1) := by
    dsimp [X, w7, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 127))
  have hw14Lower : X < 16383 * (w14 + 1) := by
    dsimp [X, w14, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 16383))
  have hw19Lower : X < 524287 * (w19 + 1) := by
    dsimp [X, w19, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 524287))
  have h2s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 60125757447)).2 hw2Lower
  have h3s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 25768181763)).2 hw3Lower
  have h6s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 2863131307)).2 hw6Lower
  have h7s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 1420293483)).2 hw7Lower
  have h14s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 11010027)).2 hw14Lower
  have h19s :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 344043)).2 hw19Lower
  have hsumLower :
      90188718070 * X <
        180377272341 * (w2 + w3 + w6 + w7 + w14 + w19 + 6) := by
    omega
  have hy6 : 6 ≤ 2 ^ s := by
    have hmono : 2 ^ 3 ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hmono ⊢
    omega
  have htarget_lt_sum :
      seamSubsetTarget s < w2 + w3 + w6 + w7 + w14 + w19 := by
    by_contra hnot
    have hle : w2 + w3 + w6 + w7 + w14 + w19 ≤
        seamSubsetTarget s := Nat.le_of_not_gt hnot
    omega
  have hw19Pos : 0 < w19 := by
    dsimp [w19, truncatedMersenneWeight]
    apply Nat.div_pos
    · have hmono : 4 ^ 10 ≤ 4 ^ s :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hmono ⊢
      omega
    · norm_num
  have hskip19 :
      seamSubsetTarget s - w2 - w3 - w6 - w7 - w14 < w19 := by
    simp only [Nat.sub_sub]
    omega
  have hmono15 : w19 ≤ truncatedMersenneWeight s 15 := by
    dsimp [w19, truncatedMersenneWeight]
    apply Nat.div_le_div_left
    · norm_num
    · norm_num
  have hmono16 : w19 ≤ truncatedMersenneWeight s 16 := by
    dsimp [w19, truncatedMersenneWeight]
    apply Nat.div_le_div_left
    · norm_num
    · norm_num
  have hmono17 : w19 ≤ truncatedMersenneWeight s 17 := by
    dsimp [w19, truncatedMersenneWeight]
    apply Nat.div_le_div_left
    · norm_num
    · norm_num
  have hmono18 : w19 ≤ truncatedMersenneWeight s 18 := by
    dsimp [w19, truncatedMersenneWeight]
    apply Nat.div_le_div_left
    · norm_num
    · norm_num

  have hpow21 : 240503259150 ≤ 120163 * 2 ^ s := by
    have hmono : 2 ^ 21 ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbase : 240503259150 ≤ 120163 * 2 ^ 21 := by norm_num
    exact hbase.trans (Nat.mul_le_mul_left 120163 hmono)
  have hside : 240503259150 * 2 ^ s ≤ 120163 * X := by
    have hmul := Nat.mul_le_mul_right (2 ^ s) hpow21
    calc
      240503259150 * 2 ^ s ≤ (120163 * 2 ^ s) * 2 ^ s := hmul
      _ = 120163 * X := by
        have hpow : 4 ^ s = 2 ^ s * 2 ^ s := by
          calc
            4 ^ s = 2 ^ (2 * s) := by
              rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
            _ = 2 ^ (s + s) := by congr 1 <;> omega
            _ = 2 ^ s * 2 ^ s := by rw [pow_add]
        dsimp [X]
        rw [hpow]
        ring
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
  have h2u := Nat.mul_le_mul_left 40083876525 hw2Upper
  have h3u := Nat.mul_le_mul_left 17178804225 hw3Upper
  have h6u := Nat.mul_le_mul_left 1908756025 hw6Upper
  have h7u := Nat.mul_le_mul_left 946863225 hw7Upper
  have h14u := Nat.mul_le_mul_left 7340025 hw14Upper
  have h20u := Nat.mul_le_mul_left 114681 hw20Upper
  have hsumUpper :
      120251629575 * (w2 + w3 + w6 + w7 + w14 + w20) ≤
        60125754706 * X := by
    omega
  have htake20 : w20 ≤
      seamSubsetTarget s - w2 - w3 - w6 - w7 - w14 := by
    omega
  dsimp [w2, w3, w6, w7, w14, w20] at htake20
  dsimp [w2, w3, w6, w7, w14, w19] at hskip19
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  exact ⟨hskip19, htake20⟩

/-- List-level normal form of the forced seam decisions through rank `20`. -/
theorem seamGreedyBits_head2367_14_20
    (s : ℕ) (hs : 21 ≤ s) :
    integerGreedyBits (seamWeights s) (seamSubsetTarget s) =
      true :: true :: false :: false :: true :: true ::
        false :: false :: false :: false :: false :: false :: true ::
          false :: false :: false :: false :: false :: true ::
            integerGreedyBits (seamWeightsFrom s 21)
              (seamSubsetTarget s - truncatedMersenneWeight s 2 -
                truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
                truncatedMersenneWeight s 7 - truncatedMersenneWeight s 14 -
                truncatedMersenneWeight s 20) := by
  rcases seamGreedy_postFourteen_decisions_through_twenty s hs with
    ⟨h15, h16, h17, h18, h19, h20⟩
  rw [seamGreedyBits_head2367_14 s (by omega),
    seamWeightsFrom_eq_cons (by omega : 15 < s),
    seamWeightsFrom_eq_cons (by omega : 16 < s),
    seamWeightsFrom_eq_cons (by omega : 17 < s),
    seamWeightsFrom_eq_cons (by omega : 18 < s),
    seamWeightsFrom_eq_cons (by omega : 19 < s),
    seamWeightsFrom_eq_cons (by omega : 20 < s)]
  simp only [integerGreedyBits]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos h20]

/-- Rank `20` is a sixth mandatory selected seam rank from row twenty-one. -/
theorem twenty_mem_seamGreedySupport
    (s : ℕ) (hs : 21 ≤ s) :
    20 ∈ seamWordSupport (seamGreedyWord s) := by
  have hbits := seamGreedyBits_head2367_14_20 s hs
  apply mem_seamWordSupport_iff.mpr
  refine ⟨⟨18, by omega⟩, ?_, by norm_num⟩
  simp [seamGreedyWord, SeamRowWord.ofList, hbits]

/-- Once `s ≥ 26`, the positive reciprocal deficit left after rank `20`
also forces rank `21`.  The exact deficit is
`12932167 / 567347188334850`; the dyadic side term fits inside it from
row twenty-six onward. -/
theorem seamGreedy_postTwenty_decision_twentyOne
    (s : ℕ) (hs : 26 ≤ s) :
    truncatedMersenneWeight s 21 ≤
      seamSubsetTarget s - truncatedMersenneWeight s 2 -
        truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
        truncatedMersenneWeight s 7 - truncatedMersenneWeight s 14 -
        truncatedMersenneWeight s 20 := by
  let X := 4 ^ s
  let w2 := truncatedMersenneWeight s 2
  let w3 := truncatedMersenneWeight s 3
  let w6 := truncatedMersenneWeight s 6
  let w7 := truncatedMersenneWeight s 7
  let w14 := truncatedMersenneWeight s 14
  let w20 := truncatedMersenneWeight s 20
  let w21 := truncatedMersenneWeight s 21
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
  have hpow26 : 567347188334850 ≤ 12932167 * 2 ^ s := by
    have hmono : 2 ^ 26 ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbase : 567347188334850 ≤ 12932167 * 2 ^ 26 := by norm_num
    exact hbase.trans (Nat.mul_le_mul_left 12932167 hmono)
  have hside : 567347188334850 * 2 ^ s ≤ 12932167 * X := by
    have hmul := Nat.mul_le_mul_right (2 ^ s) hpow26
    calc
      567347188334850 * 2 ^ s ≤ (12932167 * 2 ^ s) * 2 ^ s := hmul
      _ = 12932167 * X := by
        have hpow : 4 ^ s = 2 ^ s * 2 ^ s := by
          calc
            4 ^ s = 2 ^ (2 * s) := by
              rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
            _ = 2 ^ (s + s) := by congr 1 <;> omega
            _ = 2 ^ s * 2 ^ s := by rw [pow_add]
        dsimp [X]
        rw [hpow]
        ring
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
  have h2u := Nat.mul_le_mul_left 94557864722475 hw2Upper
  have h3u := Nat.mul_le_mul_left 40524799166775 hw3Upper
  have h6u := Nat.mul_le_mul_left 4502755462975 hw6Upper
  have h7u := Nat.mul_le_mul_left 2233650347775 hw7Upper
  have h14u := Nat.mul_le_mul_left 17315118975 hw14Upper
  have h20u := Nat.mul_le_mul_left 270532479 hw20Upper
  have h21u := Nat.mul_le_mul_left 135266175 hw21Upper
  have hsumUpper :
      283673594167425 * (w2 + w3 + w6 + w7 + w14 + w20 + w21) ≤
        141836790617629 * X := by
    omega
  have htake21 : w21 ≤
      seamSubsetTarget s - w2 - w3 - w6 - w7 - w14 - w20 := by
    omega
  simpa [w2, w3, w6, w7, w14, w20, w21] using htake21

/-- List-level normal form of the forced seam decisions through rank `21`. -/
theorem seamGreedyBits_head2367_14_20_21
    (s : ℕ) (hs : 26 ≤ s) :
    integerGreedyBits (seamWeights s) (seamSubsetTarget s) =
      true :: true :: false :: false :: true :: true ::
        false :: false :: false :: false :: false :: false :: true ::
          false :: false :: false :: false :: false :: true :: true ::
            integerGreedyBits (seamWeightsFrom s 22)
              (seamSubsetTarget s - truncatedMersenneWeight s 2 -
                truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
                truncatedMersenneWeight s 7 - truncatedMersenneWeight s 14 -
                truncatedMersenneWeight s 20 - truncatedMersenneWeight s 21) := by
  have h21 := seamGreedy_postTwenty_decision_twentyOne s hs
  rw [seamGreedyBits_head2367_14_20 s (by omega),
    seamWeightsFrom_eq_cons (by omega : 21 < s)]
  simp only [integerGreedyBits]
  rw [if_pos h21]

/-- Rank `21` is a seventh mandatory selected seam rank from row twenty-six. -/
theorem twentyOne_mem_seamGreedySupport
    (s : ℕ) (hs : 26 ≤ s) :
    21 ∈ seamWordSupport (seamGreedyWord s) := by
  have hbits := seamGreedyBits_head2367_14_20_21 s hs
  apply mem_seamWordSupport_iff.mpr
  refine ⟨⟨19, by omega⟩, ?_, by norm_num⟩
  simp [seamGreedyWord, SeamRowWord.ofList, hbits]

/-- After rank `21`, rows `s ≥ 27` skip ranks `22` through `25` and take
rank `26`.  The exact reciprocal comparison at rank `25` has excess
`4303731711383 / 614097164000829974850`, while adjoining rank `26` leaves
deficit `100171945053757 / 12691341578466215591850`. -/
theorem seamGreedy_postTwentyOne_decisions_through_twentySix
    (s : ℕ) (hs : 27 ≤ s) :
    let R := seamSubsetTarget s - truncatedMersenneWeight s 2 -
      truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
      truncatedMersenneWeight s 7 - truncatedMersenneWeight s 14 -
      truncatedMersenneWeight s 20 - truncatedMersenneWeight s 21
    R < truncatedMersenneWeight s 22 ∧
      R < truncatedMersenneWeight s 23 ∧
      R < truncatedMersenneWeight s 24 ∧
      R < truncatedMersenneWeight s 25 ∧
      truncatedMersenneWeight s 26 ≤ R := by
  dsimp only
  let X := 4 ^ s
  let w2 := truncatedMersenneWeight s 2
  let w3 := truncatedMersenneWeight s 3
  let w6 := truncatedMersenneWeight s 6
  let w7 := truncatedMersenneWeight s 7
  let w14 := truncatedMersenneWeight s 14
  let w20 := truncatedMersenneWeight s 20
  let w21 := truncatedMersenneWeight s 21
  let w25 := truncatedMersenneWeight s 25
  let w26 := truncatedMersenneWeight s 26
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

  have hw2Lower : X < 3 * (w2 + 1) := by
    dsimp [X, w2, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 3))
  have hw3Lower : X < 7 * (w3 + 1) := by
    dsimp [X, w3, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 7))
  have hw6Lower : X < 63 * (w6 + 1) := by
    dsimp [X, w6, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 63))
  have hw7Lower : X < 127 * (w7 + 1) := by
    dsimp [X, w7, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 127))
  have hw14Lower : X < 16383 * (w14 + 1) := by
    dsimp [X, w14, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 16383))
  have hw20Lower : X < 1048575 * (w20 + 1) := by
    dsimp [X, w20, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 1048575))
  have hw21Lower : X < 2097151 * (w21 + 1) := by
    dsimp [X, w21, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 2097151))
  have hw25Lower : X < 33554431 * (w25 + 1) := by
    dsimp [X, w25, truncatedMersenneWeight]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 33554431))
  have h2s := (Nat.mul_lt_mul_left
    (by norm_num : 0 < 102349527333471662475)).2 hw2Lower
  have h3s := (Nat.mul_lt_mul_left
    (by norm_num : 0 < 43864083142916426775)).2 hw3Lower
  have h6s := (Nat.mul_lt_mul_left
    (by norm_num : 0 < 4873787015879602975)).2 hw6Lower
  have h7s := (Nat.mul_lt_mul_left
    (by norm_num : 0 < 2417705370082007775)).2 hw7Lower
  have h14s := (Nat.mul_lt_mul_left
    (by norm_num : 0 < 18741902093658975)).2 hw14Lower
  have h20s := (Nat.mul_lt_mul_left
    (by norm_num : 0 < 292824625802079)).2 hw20Lower
  have h21s := (Nat.mul_lt_mul_left
    (by norm_num : 0 < 146412243086175)).2 hw21Lower
  have h25s := (Nat.mul_lt_mul_left
    (by norm_num : 0 < 9150761102175)).2 hw25Lower
  have hsumLower :
      153524293152073349404 * X <
        307048582000414987425 *
          (w2 + w3 + w6 + w7 + w14 + w20 + w21 + w25 + 8) := by
    omega
  have hy8 : 8 ≤ 2 ^ s := by
    have hmono : 2 ^ 3 ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hmono ⊢
    omega
  have htarget_lt_sum : seamSubsetTarget s <
      w2 + w3 + w6 + w7 + w14 + w20 + w21 + w25 := by
    by_contra hnot
    have hle : w2 + w3 + w6 + w7 + w14 + w20 + w21 + w25 ≤
        seamSubsetTarget s := Nat.le_of_not_gt hnot
    omega
  have hw25Pos : 0 < w25 := by
    dsimp [w25, truncatedMersenneWeight]
    apply Nat.div_pos
    · have hmono : 4 ^ 13 ≤ 4 ^ s :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hmono ⊢
      omega
    · norm_num
  have hskip25 :
      seamSubsetTarget s - w2 - w3 - w6 - w7 - w14 - w20 - w21 < w25 := by
    simp only [Nat.sub_sub]
    omega
  have hmono22 : w25 ≤ truncatedMersenneWeight s 22 := by
    dsimp [w25, truncatedMersenneWeight]
    apply Nat.div_le_div_left <;> norm_num
  have hmono23 : w25 ≤ truncatedMersenneWeight s 23 := by
    dsimp [w25, truncatedMersenneWeight]
    apply Nat.div_le_div_left <;> norm_num
  have hmono24 : w25 ≤ truncatedMersenneWeight s 24 := by
    dsimp [w25, truncatedMersenneWeight]
    apply Nat.div_le_div_left <;> norm_num

  have hpow27 :
      12691341578466215591850 ≤ 100171945053757 * 2 ^ s := by
    have hmono : 2 ^ 27 ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbase :
        12691341578466215591850 ≤ 100171945053757 * 2 ^ 27 := by
      norm_num
    exact hbase.trans (Nat.mul_le_mul_left 100171945053757 hmono)
  have hside :
      12691341578466215591850 * 2 ^ s ≤ 100171945053757 * X := by
    have hmul := Nat.mul_le_mul_right (2 ^ s) hpow27
    calc
      12691341578466215591850 * 2 ^ s ≤
          (100171945053757 * 2 ^ s) * 2 ^ s := hmul
      _ = 100171945053757 * X := by
        have hpow : 4 ^ s = 2 ^ s * 2 ^ s := by
          calc
            4 ^ s = 2 ^ (2 * s) := by
              rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
            _ = 2 ^ (s + s) := by congr 1 <;> omega
            _ = 2 ^ s * 2 ^ s := by rw [pow_add]
        dsimp [X]
        rw [hpow]
        ring
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
  have h2u := Nat.mul_le_mul_left 2115223596411035931975 hw2Upper
  have h3u := Nat.mul_le_mul_left 906524398461872542275 hw3Upper
  have h6u := Nat.mul_le_mul_left 100724933162430282475 hw6Upper
  have h7u := Nat.mul_le_mul_left 49965911726244943275 hw7Upper
  have h14u := Nat.mul_le_mul_left 387332649040658475 hw14Upper
  have h20u := Nat.mul_le_mul_left 6051709023420459 hw20Upper
  have h21u := Nat.mul_le_mul_left 3025853068869675 hw21Upper
  have h26u := Nat.mul_le_mul_left 94557864722475 hw26Upper
  have hsumUpper :
      6345670789233107795925 *
          (w2 + w3 + w6 + w7 + w14 + w20 + w21 + w26) ≤
        3172835344530581371084 * X := by
    omega
  have htake26 : w26 ≤
      seamSubsetTarget s - w2 - w3 - w6 - w7 - w14 - w20 - w21 := by
    omega
  dsimp [w2, w3, w6, w7, w14, w20, w21, w26] at htake26
  dsimp [w2, w3, w6, w7, w14, w20, w21, w25] at hskip25
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  exact ⟨hskip25, htake26⟩

/-- List-level normal form of the forced seam decisions through rank `26`. -/
theorem seamGreedyBits_head2367_14_20_21_26
    (s : ℕ) (hs : 27 ≤ s) :
    integerGreedyBits (seamWeights s) (seamSubsetTarget s) =
      true :: true :: false :: false :: true :: true ::
        false :: false :: false :: false :: false :: false :: true ::
          false :: false :: false :: false :: false :: true :: true ::
            false :: false :: false :: false :: true ::
              integerGreedyBits (seamWeightsFrom s 27)
                (seamSubsetTarget s - truncatedMersenneWeight s 2 -
                  truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
                  truncatedMersenneWeight s 7 - truncatedMersenneWeight s 14 -
                  truncatedMersenneWeight s 20 - truncatedMersenneWeight s 21 -
                  truncatedMersenneWeight s 26) := by
  rcases seamGreedy_postTwentyOne_decisions_through_twentySix s hs with
    ⟨h22, h23, h24, h25, h26⟩
  rw [seamGreedyBits_head2367_14_20_21 s (by omega),
    seamWeightsFrom_eq_cons (by omega : 22 < s),
    seamWeightsFrom_eq_cons (by omega : 23 < s),
    seamWeightsFrom_eq_cons (by omega : 24 < s),
    seamWeightsFrom_eq_cons (by omega : 25 < s),
    seamWeightsFrom_eq_cons (by omega : 26 < s)]
  simp only [integerGreedyBits]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos h26]

/-- Rank `26` is the eighth mandatory selected seam rank from row 27. -/
theorem twentySix_mem_seamGreedySupport
    (s : ℕ) (hs : 27 ≤ s) :
    26 ∈ seamWordSupport (seamGreedyWord s) := by
  have hbits := seamGreedyBits_head2367_14_20_21_26 s hs
  apply mem_seamWordSupport_iff.mpr
  refine ⟨⟨24, by omega⟩, ?_, by norm_num⟩
  simp [seamGreedyWord, SeamRowWord.ofList, hbits]

/-- At phase `s = 12 (mod 13)`, ranks `2` and `26` each contribute one
unit of boundary pulse. -/
private theorem two_le_belowPulse_of_mod_thirteen_twelve
    (s : ℕ) (hs27 : 27 ≤ s) (hmod : s % 13 = 12) :
    2 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  have h2mem :=
    (two_three_six_mem_seamGreedySupport s (by omega : 13 ≤ s)).1
  have h26mem := twentySix_mem_seamGreedySupport s hs27
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have h26even : 26 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h26odd : ¬ 26 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp26 : rowPulse s 26 = 1 := by
    simp [rowPulse, h26even, h26odd]
  have hp := pair_rowPulse_le_wordPulse
    (s := s) (a := 2) (b := 26) (by norm_num) h2mem h26mem
  change 2 ≤ wordPulse s (seamGreedyWord s).toNatWord
  omega

/-- In the joint phase `s = 1 (mod 3)`, `s = 6 (mod 7)`, and
`s = 12 (mod 13)`, forced ranks `2`, `3`, `7`, `14`, and `26` supply six
units of boundary pulse. -/
private theorem six_le_belowPulse_of_joint_phase_thirteen
    (s : ℕ) (hs27 : 27 ≤ s)
    (hmod3 : s % 3 = 1) (hmod7 : s % 7 = 6)
    (hmod13 : s % 13 = 12) :
    6 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega : 13 ≤ s)
  have h7mem := seven_mem_seamGreedySupport s (by omega)
  have h14mem := fourteen_mem_seamGreedySupport s (by omega)
  have h26mem := twentySix_mem_seamGreedySupport s hs27
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have h3odd : 3 ∣ 2 * s + 1 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h3even : ¬ 3 ∣ 2 * s + 2 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have h7even : 7 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h7odd : ¬ 7 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have h14even : 14 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h14odd : ¬ 14 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have h26even : 26 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h26odd : ¬ 26 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp3 : rowPulse s 3 = 2 := by
    simp [rowPulse, h3even, h3odd]
  have hp7 : rowPulse s 7 = 1 := by
    simp [rowPulse, h7even, h7odd]
  have hp14 : rowPulse s 14 = 1 := by
    simp [rowPulse, h14even, h14odd]
  have hp26 : rowPulse s 26 = 1 := by
    simp [rowPulse, h26even, h26odd]
  change 6 ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  calc
    6 = ∑ d ∈ ({2, 3, 7, 14, 26} : Finset ℕ), rowPulse s d := by
      simp [hp2, hp3, hp7, hp14, hp26]
    _ ≤ ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · exact h236.1
        · exact h236.2.1
        · exact h7mem
        · exact h14mem
        · exact h26mem
      · intro d _ _
        omega
/-- When `s = 9 (mod 10)`, forced ranks `2` and `20` each contribute one
unit of boundary pulse. -/
private theorem two_le_belowPulse_of_mod_ten_nine
    (s : ℕ) (hs21 : 21 ≤ s) (hmod : s % 10 = 9) :
    2 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  have h2mem :=
    (two_three_six_mem_seamGreedySupport s (by omega : 13 ≤ s)).1
  have h20mem := twenty_mem_seamGreedySupport s hs21
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have h20even : 20 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h20odd : ¬ 20 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp20 : rowPulse s 20 = 1 := by
    simp [rowPulse, h20even, h20odd]
  have hp := pair_rowPulse_le_wordPulse
    (s := s) (a := 2) (b := 20) (by norm_num) h2mem h20mem
  change 2 ≤ wordPulse s (seamGreedyWord s).toNatWord
  omega

/-- The permanently selected rank `2` supplies a baseline unit pulse. -/
private theorem one_le_belowPulse
    (s : ℕ) (hs13 : 13 ≤ s) :
    1 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  have h2mem := (two_three_six_mem_seamGreedySupport s hs13).1
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp := rowPulse_le_wordPulse (s := s) h2mem
  change 1 ≤ wordPulse s (seamGreedyWord s).toNatWord
  omega

/-- At phase `s = 10 (mod 21)`, ranks `2`, `3`, `7`, and the newly forced
rank `21` contribute respectively `1`, `2`, `2`, and `2` pulse units. -/
private theorem seven_le_belowPulse_of_mod_twentyOne_ten
    (s : ℕ) (hs26 : 26 ≤ s) (hmod : s % 21 = 10) :
    7 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega : 13 ≤ s)
  have h7mem := seven_mem_seamGreedySupport s (by omega)
  have h21mem := twentyOne_mem_seamGreedySupport s hs26
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have h3odd : 3 ∣ 2 * s + 1 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h3even : ¬ 3 ∣ 2 * s + 2 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have h7odd : 7 ∣ 2 * s + 1 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h7even : ¬ 7 ∣ 2 * s + 2 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have h21odd : 21 ∣ 2 * s + 1 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h21even : ¬ 21 ∣ 2 * s + 2 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp3 : rowPulse s 3 = 2 := by
    simp [rowPulse, h3even, h3odd]
  have hp7 : rowPulse s 7 = 2 := by
    simp [rowPulse, h7even, h7odd]
  have hp21 : rowPulse s 21 = 2 := by
    simp [rowPulse, h21even, h21odd]
  change 7 ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  calc
    7 = ∑ d ∈ ({2, 3, 7, 21} : Finset ℕ), rowPulse s d := by
      simp [hp2, hp3, hp7, hp21]
    _ ≤ ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl
        · exact h236.1
        · exact h236.2.1
        · exact h7mem
        · exact h21mem
      · intro d _ _
        omega

/-- At the simultaneous phases `s = 1 (mod 3)`, `s = 9 (mod 10)`, and
`s = 3` or `6 (mod 7)`, the forced prefix supplies at least six units of
boundary pulse. -/
private theorem six_le_belowPulse_of_joint_phase
    (s : ℕ) (hs21 : 21 ≤ s)
    (hmod3 : s % 3 = 1) (hmod10 : s % 10 = 9)
    (hmod7 : s % 7 = 3 ∨ s % 7 = 6) :
    6 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega : 13 ≤ s)
  have h7mem := seven_mem_seamGreedySupport s (by omega)
  have h14mem := fourteen_mem_seamGreedySupport s (by omega)
  have h20mem := twenty_mem_seamGreedySupport s hs21
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have h3odd : 3 ∣ 2 * s + 1 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h3even : ¬ 3 ∣ 2 * s + 2 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have h20even : 20 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h20odd : ¬ 20 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp3 : rowPulse s 3 = 2 := by
    simp [rowPulse, h3even, h3odd]
  have hp20 : rowPulse s 20 = 1 := by
    simp [rowPulse, h20even, h20odd]
  change 6 ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  rcases hmod7 with hmod7 | hmod7
  · have h7odd : 7 ∣ 2 * s + 1 :=
      Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have h7even : ¬ 7 ∣ 2 * s + 2 := by
      intro hdiv
      have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
      omega
    have hp7 : rowPulse s 7 = 2 := by
      simp [rowPulse, h7even, h7odd]
    calc
      6 = ∑ d ∈ ({2, 3, 7, 20} : Finset ℕ), rowPulse s d := by
        simp [hp2, hp3, hp7, hp20]
      _ ≤ ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl | rfl
          · exact h236.1
          · exact h236.2.1
          · exact h7mem
          · exact h20mem
        · intro d _ _
          omega
  · have h7even : 7 ∣ 2 * s + 2 :=
      Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have h7odd : ¬ 7 ∣ 2 * s + 1 := by
      intro hdiv
      have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
      omega
    have h14even : 14 ∣ 2 * s + 2 :=
      Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have h14odd : ¬ 14 ∣ 2 * s + 1 := by
      intro hdiv
      have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
      omega
    have hp7 : rowPulse s 7 = 1 := by
      simp [rowPulse, h7even, h7odd]
    have hp14 : rowPulse s 14 = 1 := by
      simp [rowPulse, h14even, h14odd]
    calc
      6 = ∑ d ∈ ({2, 3, 7, 14, 20} : Finset ℕ), rowPulse s d := by
        simp [hp2, hp3, hp7, hp14, hp20]
      _ ≤ ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl
          · exact h236.1
          · exact h236.2.1
          · exact h7mem
          · exact h14mem
          · exact h20mem
        · intro d _ _
          omega

/-- In the `s = 6 (mod 7)` phase, selected ranks `2`, `7`, and `14` each
contribute one unit of boundary pulse. -/
private theorem three_le_belowPulse_of_mod_seven_six
    (s : ℕ) (hs20 : 20 ≤ s) (hmod : s % 7 = 6) :
    3 ≤ (seamAdjacentCut s (by omega)).belowPulse := by
  classical
  have h2mem :=
    (two_three_six_mem_seamGreedySupport s (by omega : 13 ≤ s)).1
  have h7mem := seven_mem_seamGreedySupport s (by omega)
  have h14mem := fourteen_mem_seamGreedySupport s hs20
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have h7even : 7 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h7odd : ¬ 7 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have h14even : 14 ∣ 2 * s + 2 :=
    Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h14odd : ¬ 14 ∣ 2 * s + 1 := by
    intro hdiv
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  have hp7 : rowPulse s 7 = 1 := by
    simp [rowPulse, h7even, h7odd]
  have hp14 : rowPulse s 14 = 1 := by
    simp [rowPulse, h14even, h14odd]
  change 3 ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  calc
    3 = ∑ d ∈ ({2, 7, 14} : Finset ℕ), rowPulse s d := by
      simp [hp2, hp7, hp14]
    _ ≤ ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact h2mem
        · exact h7mem
        · exact h14mem
      · intro d _ _
        omega

/-- A hypothetical last middle producer in cell `-2` can occupy only five
of the twenty-one joint `3`- and `7`-phases.  This is a concrete consequence
of its actual all-right suffix, not a conditional producer interface. -/
theorem finalMiddleCell_neg_two_forces_mod_twenty_one
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2) :
    D % 21 ∈ ({8, 11, 14, 17, 20} : Finset ℕ) := by
  classical
  let hs5 : 5 ≤ D := by omega
  let u : Finset ℕ := seamWordSupport (seamGreedyWord D)
  have hword :
      seamGreedyWord (D + 1) = (seamGreedyWord D).extend false := by
    simpa [seamAdjacentCut] using
      seamGreedyWord_succ_eq_middleBranch D hs5 hncarry hmiddle
  have hu : ∀ e ∈ u, 2 ≤ e ∧ e < D := by
    intro e he
    exact seamWordSupport_below he
  have hbase : seamWordSupport (seamGreedyWord (D + 1)) =
      u ∪ Finset.Ico (D + 1) (D + 1) := by
    rw [hword, seamWordSupport_extend_false (by omega)]
    simp [u]
  have hlazy : positiveMersenneSupportValue (↑u : Set ℕ) +
      mersenneTail D < (1 / 2 : ℝ) := by
    exact prefix_add_mersenneTail_lt_half_of_eventually_right
      (S := D + 1) (D := D) (u := u)
      (by omega) (by omega) hu hright hbase
  have hseries :
      erdosSupportSeries 2 ((↑u : Set ℕ) ∪ Set.Ioi D) <
        (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    rw [positiveMersenneSupportValue_union_Ioi_eq_add_tail]
    · simpa using hlazy
    · intro e he
      exact ⟨by have := (hu e he).1; omega, (hu e he).2⟩
  have hone : 1 ∉ (↑u : Set ℕ) ∪ Set.Ioi D := by
    intro hmem
    rcases hmem with huone | hDone
    · have := (hu 1 huone).1
      omega
    · change D < 1 at hDone
      omega
  have hproducer :
      producerCarry (insert D (↑u : Set ℕ)) D = -2 := by
    calc
      producerCarry (insert D (↑u : Set ℕ)) D =
          4 * ((seamAdjacentCut D hs5).remainder : ℤ) -
            ((seamAdjacentCut D hs5).belowPulse : ℤ) - 4 := by
              simpa [u, seamAdjacentCut] using
                producerCarry_insert_seamBelowSupport_eq_middleCoordinate
                  D hs5
      _ = -2 := by simpa using hcell
  have hmod3 : D % 3 = 2 := by
    apply finalMiddleCell_neg_two_forces_mod_three_two D hD13
    · simpa [u] using hone
    · simpa [u] using hseries
    · simpa [u] using hproducer
  have hD14 : 14 ≤ D := by omega

  have hmiddleRec := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    hs5 hncarry hmiddle
  have hmiddleRecZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hmiddleRec
  push_cast at hmiddleRecZ
  have hcellR :
      4 * (seamIntegerGreedyRemainder D : ℤ) -
          ((seamAdjacentCut D hs5).belowPulse : ℤ) - 4 = -2 := by
    simpa [seamAdjacentCut_remainder] using hcell
  have hlanding :
      (seamIntegerGreedyRemainder (D + 1) : ℤ) -
          ((2 ^ (D + 1) : ℕ) : ℤ) = 2 := by
    omega
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright

  have hnot7two : D % 7 ≠ 2 := by
    intro hmod7
    have hpulse1 := three_le_belowPulse_of_mod_seven_three
      (D + 1) (by omega) (by omega)
    have hpulse1Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 1) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse1
    have hstep1 := (horbit (D + 1) le_rfl).2
    norm_num only [show D + 1 + 1 = D + 2 by omega] at hstep1
    have hE2le :
        (seamIntegerGreedyRemainder (D + 2) : ℤ) -
            ((2 ^ (D + 2) : ℕ) : ℤ) ≤ 1 := by
      rw [hlanding] at hstep1
      omega
    have hpulse2 := three_le_belowPulse_of_mod_three_one
      (D + 2) (by omega) (by omega)
    have hpulse2Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 2) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse2
    have hstep2 := (horbit (D + 2) (by omega)).2
    norm_num only [show D + 2 + 1 = D + 3 by omega] at hstep2
    have hpos3 := (horbit (D + 3) (by omega)).1
    omega

  have hnot7five : D % 7 ≠ 5 := by
    intro hmod7
    have hpulse1 := three_le_belowPulse_of_mod_seven_six
      (D + 1) (by omega) (by omega)
    have hpulse1Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 1) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse1
    have hstep1 := (horbit (D + 1) le_rfl).2
    norm_num only [show D + 1 + 1 = D + 2 by omega] at hstep1
    have hE2le :
        (seamIntegerGreedyRemainder (D + 2) : ℤ) -
            ((2 ^ (D + 2) : ℕ) : ℤ) ≤ 1 := by
      rw [hlanding] at hstep1
      omega
    have hpulse2 := three_le_belowPulse_of_mod_three_one
      (D + 2) (by omega) (by omega)
    have hpulse2Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 2) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse2
    have hstep2 := (horbit (D + 2) (by omega)).2
    norm_num only [show D + 2 + 1 = D + 3 by omega] at hstep2
    have hpos3 := (horbit (D + 3) (by omega)).1
    omega

  have h21lt : D % 21 < 21 := Nat.mod_lt _ (by norm_num)
  have h21mod3 : (D % 21) % 3 = 2 := by
    rw [Nat.mod_mod_of_dvd D (by norm_num : 3 ∣ 21), hmod3]
  have h21mod7ne2 : (D % 21) % 7 ≠ 2 := by
    rw [Nat.mod_mod_of_dvd D (by norm_num : 7 ∣ 21)]
    exact hnot7two
  have h21mod7ne5 : (D % 21) % 7 ≠ 5 := by
    rw [Nat.mod_mod_of_dvd D (by norm_num : 7 ∣ 21)]
    exact hnot7five
  simp only [Finset.mem_insert, Finset.mem_singleton]
  interval_cases h : D % 21 <;> simp_all

/-- Rank `20` refines the final-middle phase sieve: once it is uniformly
present, none of the five surviving `21`-phases can occur together with
`D = 8 (mod 10)`, while phases `8` and `11 (mod 21)` also exclude
`D = 7 (mod 10)`.  These seven exclusions reduce the combined `210`-phase
survivor set from fifty classes to forty-three. -/
theorem finalMiddleCell_neg_two_forces_phase_refinement
    (D : ℕ) (hD20 : 20 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2) :
    D % 21 ∈ ({8, 11, 14, 17, 20} : Finset ℕ) ∧
      D % 10 ≠ 8 ∧
      ¬ (D % 10 = 7 ∧ D % 21 ∈ ({8, 11} : Finset ℕ)) := by
  have hphase := finalMiddleCell_neg_two_forces_mod_twenty_one
    D (by omega) hncarry hmiddle hright hcell
  have hphaseMod3 : (D % 21) % 3 = 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hphase
    rcases hphase with h | h | h | h | h <;> simp [h]
  have hmod3 : D % 3 = 2 := by
    rw [← Nat.mod_mod_of_dvd D (by norm_num : 3 ∣ 21)]
    exact hphaseMod3

  let hs5 : 5 ≤ D := by omega
  have hmiddleRec := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    hs5 hncarry hmiddle
  have hmiddleRecZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hmiddleRec
  push_cast at hmiddleRecZ
  have hcellR :
      4 * (seamIntegerGreedyRemainder D : ℤ) -
          ((seamAdjacentCut D hs5).belowPulse : ℤ) - 4 = -2 := by
    simpa [seamAdjacentCut_remainder] using hcell
  have hlanding :
      (seamIntegerGreedyRemainder (D + 1) : ℤ) -
          ((2 ^ (D + 1) : ℕ) : ℤ) = 2 := by
    omega
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright

  have hnot10eight : D % 10 ≠ 8 := by
    intro hmod10
    have hpulse1 := two_le_belowPulse_of_mod_ten_nine
      (D + 1) (by omega) (by omega)
    have hpulse1Z : (2 : ℤ) ≤
        ((seamAdjacentCut (D + 1) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse1
    have hstep1 := (horbit (D + 1) le_rfl).2
    norm_num only [show D + 1 + 1 = D + 2 by omega] at hstep1
    have hE2le :
        (seamIntegerGreedyRemainder (D + 2) : ℤ) -
            ((2 ^ (D + 2) : ℕ) : ℤ) ≤ 2 := by
      rw [hlanding] at hstep1
      omega
    have hpulse2 := three_le_belowPulse_of_mod_three_one
      (D + 2) (by omega) (by omega)
    have hpulse2Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 2) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse2
    have hstep2 := (horbit (D + 2) (by omega)).2
    norm_num only [show D + 2 + 1 = D + 3 by omega] at hstep2
    have hE3le :
        (seamIntegerGreedyRemainder (D + 3) : ℤ) -
            ((2 ^ (D + 3) : ℕ) : ℤ) ≤ 1 := by
      omega
    have hpulse3 := three_le_belowPulse_of_mod_three_two
      (D + 3) (by omega) (by omega)
    have hpulse3Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 3) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse3
    have hstep3 := (horbit (D + 3) (by omega)).2
    norm_num only [show D + 3 + 1 = D + 4 by omega] at hstep3
    have hpos4 := (horbit (D + 4) (by omega)).1
    omega

  have hnot10sevenPhases :
      ¬ (D % 10 = 7 ∧ D % 21 ∈ ({8, 11} : Finset ℕ)) := by
    rintro ⟨hmod10, hsmallPhase⟩
    have hphaseEq : D % 21 = 8 ∨ D % 21 = 11 := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hsmallPhase
    have hmod7 : D % 7 = 1 ∨ D % 7 = 4 := by
      rcases hphaseEq with h8 | h11
      · left
        rw [← Nat.mod_mod_of_dvd D (by norm_num : 7 ∣ 21), h8]
      · right
        rw [← Nat.mod_mod_of_dvd D (by norm_num : 7 ∣ 21), h11]
    have hpulse1 := one_le_belowPulse (D + 1) (by omega)
    have hpulse1Z : (1 : ℤ) ≤
        ((seamAdjacentCut (D + 1) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse1
    have hstep1 := (horbit (D + 1) le_rfl).2
    norm_num only [show D + 1 + 1 = D + 2 by omega] at hstep1
    have hE2le :
        (seamIntegerGreedyRemainder (D + 2) : ℤ) -
            ((2 ^ (D + 2) : ℕ) : ℤ) ≤ 3 := by
      rw [hlanding] at hstep1
      omega
    have hrow7 : (D + 2) % 7 = 3 ∨ (D + 2) % 7 = 6 := by
      rcases hmod7 with h7 | h7 <;> omega
    have hpulse2 := six_le_belowPulse_of_joint_phase
      (D + 2) (by omega) (by omega) (by omega) hrow7
    have hpulse2Z : (6 : ℤ) ≤
        ((seamAdjacentCut (D + 2) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse2
    have hstep2 := (horbit (D + 2) (by omega)).2
    norm_num only [show D + 2 + 1 = D + 3 by omega] at hstep2
    have hE3le :
        (seamIntegerGreedyRemainder (D + 3) : ℤ) -
            ((2 ^ (D + 3) : ℕ) : ℤ) ≤ 2 := by
      omega
    have hpulse3 := three_le_belowPulse_of_mod_three_two
      (D + 3) (by omega) (by omega)
    have hpulse3Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 3) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse3
    have hstep3 := (horbit (D + 3) (by omega)).2
    norm_num only [show D + 3 + 1 = D + 4 by omega] at hstep3
    have hE4le :
        (seamIntegerGreedyRemainder (D + 4) : ℤ) -
            ((2 ^ (D + 4) : ℕ) : ℤ) ≤ 1 := by
      omega
    have hpulse4 := one_le_belowPulse (D + 4) (by omega)
    have hpulse4Z : (1 : ℤ) ≤
        ((seamAdjacentCut (D + 4) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse4
    have hstep4 := (horbit (D + 4) (by omega)).2
    norm_num only [show D + 4 + 1 = D + 5 by omega] at hstep4
    have hpos5 := (horbit (D + 5) (by omega)).1
    omega
  exact ⟨finalMiddleCell_neg_two_forces_mod_twenty_one
    D (by omega) hncarry hmiddle hright hcell,
    hnot10eight, hnot10sevenPhases⟩

/-- The forced rank `21` removes the entire phase `D = 8 (mod 21)`.
Together with the rank-`20` sieve, this leaves thirty-five classes modulo
`210`: four surviving `21`-phases, none paired with `D = 8 (mod 10)`, and
the phase `11 (mod 21)` also not paired with `D = 7 (mod 10)`. -/
theorem finalMiddleCell_neg_two_forces_phase_refinement_through_twentyOne
    (D : ℕ) (hD26 : 26 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2) :
    D % 21 ∈ ({11, 14, 17, 20} : Finset ℕ) ∧
      D % 10 ≠ 8 ∧
      ¬ (D % 10 = 7 ∧ D % 21 = 11) := by
  have hold := finalMiddleCell_neg_two_forces_phase_refinement
    D (by omega) hncarry hmiddle hright hcell
  have hnotEight : D % 21 ≠ 8 := by
    intro hmod21
    let hs5 : 5 ≤ D := by omega
    have hmiddleRec := seamMiddleBranch_nextRemainder_add_belowPulse_eq
      hs5 hncarry hmiddle
    have hmiddleRecZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hmiddleRec
    push_cast at hmiddleRecZ
    have hcellR :
        4 * (seamIntegerGreedyRemainder D : ℤ) -
            ((seamAdjacentCut D hs5).belowPulse : ℤ) - 4 = -2 := by
      simpa [seamAdjacentCut_remainder] using hcell
    have hlanding :
        (seamIntegerGreedyRemainder (D + 1) : ℤ) -
            ((2 ^ (D + 1) : ℕ) : ℤ) = 2 := by
      omega
    have horbit := eventualRightTail_positive_affineExcess
      (S := D + 1) (by omega) hright
    have hpulse1 := one_le_belowPulse (D + 1) (by omega)
    have hpulse1Z : (1 : ℤ) ≤
        ((seamAdjacentCut (D + 1) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse1
    have hstep1 := (horbit (D + 1) le_rfl).2
    norm_num only [show D + 1 + 1 = D + 2 by omega] at hstep1
    have hE2le :
        (seamIntegerGreedyRemainder (D + 2) : ℤ) -
            ((2 ^ (D + 2) : ℕ) : ℤ) ≤ 3 := by
      rw [hlanding] at hstep1
      omega
    have hpulse2 := seven_le_belowPulse_of_mod_twentyOne_ten
      (D + 2) (by omega) (by omega)
    have hpulse2Z : (7 : ℤ) ≤
        ((seamAdjacentCut (D + 2) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse2
    have hstep2 := (horbit (D + 2) (by omega)).2
    norm_num only [show D + 2 + 1 = D + 3 by omega] at hstep2
    have hE3le :
        (seamIntegerGreedyRemainder (D + 3) : ℤ) -
            ((2 ^ (D + 3) : ℕ) : ℤ) ≤ 1 := by
      omega
    have hpulse3 := three_le_belowPulse_of_mod_three_two
      (D + 3) (by omega) (by omega)
    have hpulse3Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 3) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse3
    have hstep3 := (horbit (D + 3) (by omega)).2
    norm_num only [show D + 3 + 1 = D + 4 by omega] at hstep3
    have hpos4 := (horbit (D + 4) (by omega)).1
    omega
  have hphase : D % 21 ∈ ({11, 14, 17, 20} : Finset ℕ) := by
    have hphaseOld := hold.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hphaseOld ⊢
    rcases hphaseOld with h8 | h11 | h14 | h17 | h20
    · exact False.elim (hnotEight h8)
    · exact Or.inl h11
    · exact Or.inr (Or.inl h14)
    · exact Or.inr (Or.inr (Or.inl h17))
    · exact Or.inr (Or.inr (Or.inr h20))
  have hnotSevenEleven : ¬ (D % 10 = 7 ∧ D % 21 = 11) := by
    rintro ⟨h10, h21⟩
    exact hold.2.2 ⟨h10, by simp [h21]⟩
  exact ⟨hphase, hold.2.1, hnotSevenEleven⟩

/-- The next forced rank, `26`, removes every surviving class with
`D = 11 (mod 13)`.  In the adjacent `D = 10 (mod 13)` phase it also removes
the full `D = 11 (mod 21)` slice.  Thus the hypothetical final `-2` middle
cell is confined to 412 of the 2730 joint phases. -/
theorem finalMiddleCell_neg_two_forces_phase_refinement_through_twentySix
    (D : ℕ) (hD27 : 27 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2) :
    D % 21 ∈ ({11, 14, 17, 20} : Finset ℕ) ∧
      D % 10 ≠ 8 ∧
      ¬ (D % 10 = 7 ∧ D % 21 = 11) ∧
      D % 13 ≠ 11 ∧
      ¬ (D % 13 = 10 ∧ D % 21 = 11) := by
  have hold := finalMiddleCell_neg_two_forces_phase_refinement_through_twentyOne
    D (by omega) hncarry hmiddle hright hcell
  have hphase := hold.1
  have hphaseMod3 : (D % 21) % 3 = 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hphase
    rcases hphase with h | h | h | h <;> simp [h]
  have hmod3 : D % 3 = 2 := by
    rw [← Nat.mod_mod_of_dvd D (by norm_num : 3 ∣ 21)]
    exact hphaseMod3

  let hs5 : 5 ≤ D := by omega
  have hmiddleRec := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    hs5 hncarry hmiddle
  have hmiddleRecZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hmiddleRec
  push_cast at hmiddleRecZ
  have hcellR :
      4 * (seamIntegerGreedyRemainder D : ℤ) -
          ((seamAdjacentCut D hs5).belowPulse : ℤ) - 4 = -2 := by
    simpa [seamAdjacentCut_remainder] using hcell
  have hlanding :
      (seamIntegerGreedyRemainder (D + 1) : ℤ) -
          ((2 ^ (D + 1) : ℕ) : ℤ) = 2 := by
    omega
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright

  have hnot13eleven : D % 13 ≠ 11 := by
    intro hmod13
    have hpulse1 := two_le_belowPulse_of_mod_thirteen_twelve
      (D + 1) (by omega) (by omega)
    have hpulse1Z : (2 : ℤ) ≤
        ((seamAdjacentCut (D + 1) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse1
    have hstep1 := (horbit (D + 1) le_rfl).2
    norm_num only [show D + 1 + 1 = D + 2 by omega] at hstep1
    have hE2le :
        (seamIntegerGreedyRemainder (D + 2) : ℤ) -
            ((2 ^ (D + 2) : ℕ) : ℤ) ≤ 2 := by
      rw [hlanding] at hstep1
      omega
    have hpulse2 := three_le_belowPulse_of_mod_three_one
      (D + 2) (by omega) (by omega)
    have hpulse2Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 2) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse2
    have hstep2 := (horbit (D + 2) (by omega)).2
    norm_num only [show D + 2 + 1 = D + 3 by omega] at hstep2
    have hE3le :
        (seamIntegerGreedyRemainder (D + 3) : ℤ) -
            ((2 ^ (D + 3) : ℕ) : ℤ) ≤ 1 := by
      omega
    have hpulse3 := three_le_belowPulse_of_mod_three_two
      (D + 3) (by omega) (by omega)
    have hpulse3Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 3) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse3
    have hstep3 := (horbit (D + 3) (by omega)).2
    norm_num only [show D + 3 + 1 = D + 4 by omega] at hstep3
    have hpos4 := (horbit (D + 4) (by omega)).1
    omega

  have hnotJoint : ¬ (D % 13 = 10 ∧ D % 21 = 11) := by
    rintro ⟨hmod13, hmod21⟩
    have hDmod7 : D % 7 = 4 := by
      rw [← Nat.mod_mod_of_dvd D (by norm_num : 7 ∣ 21), hmod21]
    have hpulse1 := one_le_belowPulse (D + 1) (by omega)
    have hpulse1Z : (1 : ℤ) ≤
        ((seamAdjacentCut (D + 1) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse1
    have hstep1 := (horbit (D + 1) le_rfl).2
    norm_num only [show D + 1 + 1 = D + 2 by omega] at hstep1
    have hE2le :
        (seamIntegerGreedyRemainder (D + 2) : ℤ) -
            ((2 ^ (D + 2) : ℕ) : ℤ) ≤ 3 := by
      rw [hlanding] at hstep1
      omega
    have hpulse2 := six_le_belowPulse_of_joint_phase_thirteen
      (D + 2) (by omega) (by omega) (by omega) (by omega)
    have hpulse2Z : (6 : ℤ) ≤
        ((seamAdjacentCut (D + 2) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse2
    have hstep2 := (horbit (D + 2) (by omega)).2
    norm_num only [show D + 2 + 1 = D + 3 by omega] at hstep2
    have hE3le :
        (seamIntegerGreedyRemainder (D + 3) : ℤ) -
            ((2 ^ (D + 3) : ℕ) : ℤ) ≤ 2 := by
      omega
    have hpulse3 := three_le_belowPulse_of_mod_three_two
      (D + 3) (by omega) (by omega)
    have hpulse3Z : (3 : ℤ) ≤
        ((seamAdjacentCut (D + 3) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse3
    have hstep3 := (horbit (D + 3) (by omega)).2
    norm_num only [show D + 3 + 1 = D + 4 by omega] at hstep3
    have hE4le :
        (seamIntegerGreedyRemainder (D + 4) : ℤ) -
            ((2 ^ (D + 4) : ℕ) : ℤ) ≤ 1 := by
      omega
    have hpulse4 := one_le_belowPulse (D + 4) (by omega)
    have hpulse4Z : (1 : ℤ) ≤
        ((seamAdjacentCut (D + 4) (by omega)).belowPulse : ℤ) := by
      exact_mod_cast hpulse4
    have hstep4 := (horbit (D + 4) (by omega)).2
    norm_num only [show D + 4 + 1 = D + 5 by omega] at hstep4
    have hpos5 := (horbit (D + 5) (by omega)).1
    omega
  exact ⟨hold.1, hold.2.1, hold.2.2, hnot13eleven, hnotJoint⟩

/-- The joint residue classes left by the rank-`26` final-middle sieve. -/
def finalMiddleTwentySixPhaseSurvivors : Finset ℕ :=
  (Finset.range 2730).filter fun D ↦
    D % 21 ∈ ({11, 14, 17, 20} : Finset ℕ) ∧
      D % 10 ≠ 8 ∧
      ¬ (D % 10 = 7 ∧ D % 21 = 11) ∧
      D % 13 ≠ 11 ∧
      ¬ (D % 13 = 10 ∧ D % 21 = 11)

set_option maxRecDepth 100000 in
/-- The rank-`26` refinement leaves exactly 412 of the 2730 joint phases. -/
theorem finalMiddleTwentySixPhaseSurvivors_card :
    finalMiddleTwentySixPhaseSurvivors.card = 412 := by
  decide

#print axioms finalMiddleCell_neg_two_forces_mod_twenty_one
#print axioms seamGreedy_postSeven_decisions_through_fourteen
#print axioms seamGreedyBits_head2367_14
#print axioms fourteen_mem_seamGreedySupport
#print axioms seamGreedy_postFourteen_decisions_through_twenty
#print axioms seamGreedyBits_head2367_14_20
#print axioms twenty_mem_seamGreedySupport
#print axioms finalMiddleCell_neg_two_forces_phase_refinement
#print axioms seamGreedy_postTwenty_decision_twentyOne
#print axioms seamGreedyBits_head2367_14_20_21
#print axioms twentyOne_mem_seamGreedySupport
#print axioms finalMiddleCell_neg_two_forces_phase_refinement_through_twentyOne
#print axioms seamGreedy_postTwentyOne_decisions_through_twentySix
#print axioms seamGreedyBits_head2367_14_20_21_26
#print axioms twentySix_mem_seamGreedySupport
#print axioms finalMiddleCell_neg_two_forces_phase_refinement_through_twentySix
#print axioms finalMiddleTwentySixPhaseSurvivors_card

end

end Erdos249257
