import ErdosProblems.Erdos257.FourNinthsCofinalRepairConsumer
import Erdos257PeriodNoncollapse.SupportDilationDifferences

/-!
# Erdős #257: the causal seven-column producer for `4/9`

This module turns the surviving modulus-`120` computation into an exact Lean
interface.  The causal load is the union of selected divisors visible at the
three earlier ranks `n/2`, `n/3`, and `n/5`.  Inclusion-exclusion gives the
seven-column formula without natural-number subtraction, and the union embeds
in the full divisor load at `n`.

The all-depth seven-column inequality is deliberately retained as a named
hypothesis.  Proving it would give actual repairs at every positive multiple
of `120`, hence the infinite rational `4/9` counterexample packaged by
`FourNinthsCofinalRepairConsumer`.
-/

namespace ErdosProblems.Erdos257

open Set
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.SupportDilationDifferences

/-- Selected divisors of a rank, as a finite set. -/
private noncomputable def fourNinthsSelectedDivisors
    (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  letI := Classical.decPred fun d : ℕ ↦ d ∈ A
  n.divisors.filter fun d ↦ d ∈ A

private theorem fourNinthsSelectedDivisors_card (A : Set ℕ) (n : ℕ) :
    (fourNinthsSelectedDivisors A n).card = supportCoeff A n := by
  classical
  unfold fourNinthsSelectedDivisors
  exact (supportCoeff_eq_card_filter A n).symm

private theorem mem_fourNinthsPrefixRat_iff_real_support
    {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) n ↔
      d ∈ greedyMersenneSupport (4 / 9 : ℝ) := by
  classical
  unfold greedyMersennePrefixRat
  constructor
  · intro hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨-, htake⟩ := Finset.mem_filter.mp hj
    have htakeR := (rational_greedy_take_iff_real (4 / 9 : ℚ) j).1 htake
    norm_num at htakeR
    exact (succ_mem_greedyMersenneSupport_iff (4 / 9 : ℝ) j).2 htakeR
  · intro hd
    refine Finset.mem_image.mpr ⟨d - 1, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    apply (rational_greedy_take_iff_real (4 / 9 : ℚ) (d - 1)).2
    have htakeR :=
      (succ_mem_greedyMersenneSupport_iff (4 / 9 : ℝ) (d - 1)).1
        (by simpa only [Nat.sub_add_cancel hd1] using hd)
    norm_num at htakeR ⊢
    exact htakeR

private theorem fourNinthsSelectedDivisors_mono_of_dvd
    (A : Set ℕ) {a n : ℕ} (han : a ∣ n) (hn : 0 < n) :
    fourNinthsSelectedDivisors A a ⊆ fourNinthsSelectedDivisors A n := by
  classical
  intro d hd
  unfold fourNinthsSelectedDivisors at hd ⊢
  rcases Finset.mem_filter.mp hd with ⟨hda, hdA⟩
  rcases Nat.mem_divisors.mp hda with ⟨hda, -⟩
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hda.trans han, hn.ne'⟩, hdA⟩

private theorem fourNinthsSelectedDivisors_inter
    (A : Set ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    fourNinthsSelectedDivisors A a ∩ fourNinthsSelectedDivisors A b =
      fourNinthsSelectedDivisors A (Nat.gcd a b) := by
  classical
  ext d
  unfold fourNinthsSelectedDivisors
  simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨hda, -⟩, hdA⟩, ⟨⟨hdb, -⟩, -⟩⟩
    exact ⟨⟨Nat.dvd_gcd hda hdb, (Nat.gcd_pos_of_pos_left b ha).ne'⟩, hdA⟩
  · rintro ⟨⟨hdg, -⟩, hdA⟩
    exact
      ⟨⟨⟨hdg.trans (Nat.gcd_dvd_left a b), ha.ne'⟩, hdA⟩,
        ⟨⟨hdg.trans (Nat.gcd_dvd_right a b), hb.ne'⟩, hdA⟩⟩

private theorem finset_union_four_card_identity {α : Type*} [DecidableEq α]
    (X Y Z W : Finset α) :
    (((X ∪ Y) ∪ Z) ∪ W).card +
          (X ∩ Y).card + (X ∩ Z).card + (X ∩ W).card +
          (Y ∩ Z).card + (Y ∩ W).card + (Z ∩ W).card +
          (X ∩ Y ∩ Z ∩ W).card =
      X.card + Y.card + Z.card + W.card +
          (X ∩ Y ∩ Z).card + (X ∩ Y ∩ W).card +
          (X ∩ Z ∩ W).card + (Y ∩ Z ∩ W).card := by
  have hthree (A B C : Finset α) :
      ((A ∪ B) ∪ C).card + (A ∩ B).card + (A ∩ C).card +
          (B ∩ C).card =
        A.card + B.card + C.card + (A ∩ B ∩ C).card := by
    have hAB := Finset.card_union_add_card_inter A B
    have hABC := Finset.card_union_add_card_inter (A ∪ B) C
    have hdistrib : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
      ext d
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    have hinter : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
      ext d
      simp only [Finset.mem_inter]
      tauto
    have hpair := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
    rw [hdistrib] at hABC
    rw [hinter] at hpair
    omega
  have hXYZ := hthree X Y Z
  have hXYZW := Finset.card_union_add_card_inter ((X ∪ Y) ∪ Z) W
  have hdistribW : ((X ∪ Y) ∪ Z) ∩ W =
      ((X ∩ W) ∪ (Y ∩ W)) ∪ (Z ∩ W) := by
    ext d
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [hdistribW] at hXYZW
  have hW := hthree (X ∩ W) (Y ∩ W) (Z ∩ W)
  have hXYW : (X ∩ W) ∩ (Y ∩ W) = X ∩ Y ∩ W := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  have hXZW : (X ∩ W) ∩ (Z ∩ W) = X ∩ Z ∩ W := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  have hYZW : (Y ∩ W) ∩ (Z ∩ W) = Y ∩ Z ∩ W := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  have hXYZWInter : (X ∩ Y ∩ W) ∩ (Z ∩ W) =
      X ∩ Y ∩ Z ∩ W := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  rw [hXYW, hXZW, hYZW, hXYZWInter] at hW
  omega

private theorem fourNinthsSelectedDivisors_union_three_card_identity
    (A : Set ℕ) {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (((fourNinthsSelectedDivisors A a ∪ fourNinthsSelectedDivisors A b) ∪
          fourNinthsSelectedDivisors A c).card +
        supportCoeff A (Nat.gcd a b) +
        supportCoeff A (Nat.gcd a c) +
        supportCoeff A (Nat.gcd b c) =
      supportCoeff A a + supportCoeff A b + supportCoeff A c +
        supportCoeff A (Nat.gcd (Nat.gcd a b) c)) := by
  classical
  let X := fourNinthsSelectedDivisors A a
  let Y := fourNinthsSelectedDivisors A b
  let Z := fourNinthsSelectedDivisors A c
  have hXY : X ∩ Y = fourNinthsSelectedDivisors A (Nat.gcd a b) :=
    fourNinthsSelectedDivisors_inter A ha hb
  have hXZ : X ∩ Z = fourNinthsSelectedDivisors A (Nat.gcd a c) :=
    fourNinthsSelectedDivisors_inter A ha hc
  have hYZ : Y ∩ Z = fourNinthsSelectedDivisors A (Nat.gcd b c) :=
    fourNinthsSelectedDivisors_inter A hb hc
  have hgcd : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hXYZ : X ∩ Y ∩ Z =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd a b) c) := by
    rw [hXY]
    exact fourNinthsSelectedDivisors_inter A hgcd hc
  have hdistrib : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z) := by
    ext d
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hinter : (X ∩ Z) ∩ (Y ∩ Z) = X ∩ Y ∩ Z := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  have hXYcard := Finset.card_union_add_card_inter X Y
  have hXYZcard := Finset.card_union_add_card_inter (X ∪ Y) Z
  have hpairCard := Finset.card_union_add_card_inter (X ∩ Z) (Y ∩ Z)
  rw [hdistrib] at hXYZcard
  rw [hinter] at hpairCard
  have hcount :
      ((X ∪ Y) ∪ Z).card + (X ∩ Y).card + (X ∩ Z).card +
          (Y ∩ Z).card =
        X.card + Y.card + Z.card + (X ∩ Y ∩ Z).card := by
    omega
  rw [hXYZ, hXY, hXZ, hYZ] at hcount
  simpa only [X, Y, Z, fourNinthsSelectedDivisors_card] using hcount

private theorem fourNinthsSelectedDivisors_union_four_card_identity
    (A : Set ℕ) {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ((((fourNinthsSelectedDivisors A a ∪ fourNinthsSelectedDivisors A b) ∪
          fourNinthsSelectedDivisors A c) ∪
          fourNinthsSelectedDivisors A d).card +
        supportCoeff A (Nat.gcd a b) + supportCoeff A (Nat.gcd a c) +
        supportCoeff A (Nat.gcd a d) + supportCoeff A (Nat.gcd b c) +
        supportCoeff A (Nat.gcd b d) + supportCoeff A (Nat.gcd c d) +
        supportCoeff A (Nat.gcd (Nat.gcd (Nat.gcd a b) c) d) =
      supportCoeff A a + supportCoeff A b + supportCoeff A c +
        supportCoeff A d + supportCoeff A (Nat.gcd (Nat.gcd a b) c) +
        supportCoeff A (Nat.gcd (Nat.gcd a b) d) +
        supportCoeff A (Nat.gcd (Nat.gcd a c) d) +
        supportCoeff A (Nat.gcd (Nat.gcd b c) d)) := by
  classical
  let X := fourNinthsSelectedDivisors A a
  let Y := fourNinthsSelectedDivisors A b
  let Z := fourNinthsSelectedDivisors A c
  let W := fourNinthsSelectedDivisors A d
  have hXY : X ∩ Y = fourNinthsSelectedDivisors A (Nat.gcd a b) :=
    fourNinthsSelectedDivisors_inter A ha hb
  have hXZ : X ∩ Z = fourNinthsSelectedDivisors A (Nat.gcd a c) :=
    fourNinthsSelectedDivisors_inter A ha hc
  have hXW : X ∩ W = fourNinthsSelectedDivisors A (Nat.gcd a d) :=
    fourNinthsSelectedDivisors_inter A ha hd
  have hYZ : Y ∩ Z = fourNinthsSelectedDivisors A (Nat.gcd b c) :=
    fourNinthsSelectedDivisors_inter A hb hc
  have hYW : Y ∩ W = fourNinthsSelectedDivisors A (Nat.gcd b d) :=
    fourNinthsSelectedDivisors_inter A hb hd
  have hZW : Z ∩ W = fourNinthsSelectedDivisors A (Nat.gcd c d) :=
    fourNinthsSelectedDivisors_inter A hc hd
  have hgab : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hgac : 0 < Nat.gcd a c := Nat.gcd_pos_of_pos_left c ha
  have hgbc : 0 < Nat.gcd b c := Nat.gcd_pos_of_pos_left c hb
  have hXYZ : X ∩ Y ∩ Z =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd a b) c) := by
    rw [hXY]
    exact fourNinthsSelectedDivisors_inter A hgab hc
  have hXYW : X ∩ Y ∩ W =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd a b) d) := by
    rw [hXY]
    exact fourNinthsSelectedDivisors_inter A hgab hd
  have hXZW : X ∩ Z ∩ W =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd a c) d) := by
    rw [hXZ]
    exact fourNinthsSelectedDivisors_inter A hgac hd
  have hYZW : Y ∩ Z ∩ W =
      fourNinthsSelectedDivisors A (Nat.gcd (Nat.gcd b c) d) := by
    rw [hYZ]
    exact fourNinthsSelectedDivisors_inter A hgbc hd
  have hgabc : 0 < Nat.gcd (Nat.gcd a b) c :=
    Nat.gcd_pos_of_pos_left c hgab
  have hXYZW : X ∩ Y ∩ Z ∩ W =
      fourNinthsSelectedDivisors A
        (Nat.gcd (Nat.gcd (Nat.gcd a b) c) d) := by
    rw [hXYZ]
    exact fourNinthsSelectedDivisors_inter A hgabc hd
  have hcount := finset_union_four_card_identity X Y Z W
  rw [hXYZW, hXYZ, hXYW, hXZW, hYZW, hXY, hXZ, hXW, hYZ, hYW,
    hZW] at hcount
  simpa only [X, Y, Z, W, fourNinthsSelectedDivisors_card] using hcount

/-- Selected divisors already visible in at least one of the `2`, `3`, or `5`
parent columns. -/
noncomputable def fourNinthsPrimorialUnionLoad (n : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  ((fourNinthsSelectedDivisors A (n / 2) ∪
      fourNinthsSelectedDivisors A (n / 3)) ∪
        fourNinthsSelectedDivisors A (n / 5)).card

/-- Exact kernel-certified base value for the prime-column normal form. -/
theorem fourNinthsPrimorialUnionLoad_120 :
    fourNinthsPrimorialUnionLoad 120 = 10 := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let P : Set ℕ := ↑(greedyMersennePrefixRat (4 / 9 : ℚ) 120)
  have hselected (n : ℕ) (hn : 0 < n) (hn120 : n ≤ 120) :
      fourNinthsSelectedDivisors A n = fourNinthsSelectedDivisors P n := by
    ext d
    unfold fourNinthsSelectedDivisors
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd120 : d ≤ 120 := (Nat.le_of_dvd hn hdvd).trans hn120
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 120
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd120).2 hdA⟩
    · rintro ⟨hddiv, hdP⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd120 : d ≤ 120 := (Nat.le_of_dvd hn hdvd).trans hn120
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 120 at hdP
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd120).1 hdP⟩
  change ((fourNinthsSelectedDivisors A 60 ∪
      fourNinthsSelectedDivisors A 40) ∪
        fourNinthsSelectedDivisors A 24).card = 10
  rw [hselected 60 (by norm_num) (by norm_num),
    hselected 40 (by norm_num) (by norm_num),
    hselected 24 (by norm_num) (by norm_num)]
  simp only [fourNinthsSelectedDivisors, P, Finset.mem_coe]
  native_decide

/-- Exact subtraction-free seven-column identity at positive multiples of
`120`. -/
theorem fourNinthsPrimorialUnionLoad_sevenColumn (k : ℕ) :
    let n := 120 * (k + 1)
    let A := greedyMersenneSupport (4 / 9 : ℝ)
    fourNinthsPrimorialUnionLoad n + supportCoeff A (n / 6) +
          supportCoeff A (n / 10) + supportCoeff A (n / 15) =
      supportCoeff A (n / 2) + supportCoeff A (n / 3) +
          supportCoeff A (n / 5) + supportCoeff A (n / 30) := by
  dsimp only
  let m := k + 1
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h := fourNinthsSelectedDivisors_union_three_card_identity A
    (a := 60 * m) (b := 40 * m) (c := 24 * m)
    (by positivity) (by positivity) (by positivity)
  have h2 : 120 * (k + 1) / 2 = 60 * m := by dsimp [m]; omega
  have h3 : 120 * (k + 1) / 3 = 40 * m := by dsimp [m]; omega
  have h5 : 120 * (k + 1) / 5 = 24 * m := by dsimp [m]; omega
  have h6 : 120 * (k + 1) / 6 = 20 * m := by dsimp [m]; omega
  have h10 : 120 * (k + 1) / 10 = 12 * m := by dsimp [m]; omega
  have h15 : 120 * (k + 1) / 15 = 8 * m := by dsimp [m]; omega
  have h30 : 120 * (k + 1) / 30 = 4 * m := by dsimp [m]; omega
  dsimp [fourNinthsPrimorialUnionLoad]
  rw [h2, h3, h5, h6, h10, h15, h30]
  norm_num [Nat.gcd_mul_right] at h
  simpa only [A, Finset.union_assoc] using h

/-- The causal union is a subset of the full selected-divisor load. -/
theorem fourNinthsPrimorialUnionLoad_le_supportCoeff
    {n : ℕ} (hn : 0 < n) (h30 : 30 ∣ n) :
    fourNinthsPrimorialUnionLoad n ≤
      supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h2 : 2 ∣ n := (show 2 ∣ 30 by norm_num).trans h30
  have h3 : 3 ∣ n := (show 3 ∣ 30 by norm_num).trans h30
  have h5 : 5 ∣ n := (show 5 ∣ 30 by norm_num).trans h30
  have hs2 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h2) hn
  have hs3 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h3) hn
  have hs5 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h5) hn
  rw [← fourNinthsSelectedDivisors_card A n]
  apply Finset.card_le_card
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · rcases Finset.mem_union.mp hd with hd | hd
    · exact hs2 hd
    · exact hs3 hd
  · exact hs5 hd

/-! ## The `2·3·7` causal producer -/

/-- Selected divisors already visible in at least one of the `2`, `3`, or `7`
parent columns. -/
noncomputable def fourNinthsHeptadicUnionLoad (n : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  ((fourNinthsSelectedDivisors A (n / 2) ∪
      fourNinthsSelectedDivisors A (n / 3)) ∪
        fourNinthsSelectedDivisors A (n / 7)).card

/-- Exact kernel-certified base value for the modulus-`84` normal form. -/
theorem fourNinthsHeptadicUnionLoad_84 :
    fourNinthsHeptadicUnionLoad 84 = 6 := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let P : Set ℕ := ↑(greedyMersennePrefixRat (4 / 9 : ℚ) 84)
  have hselected (n : ℕ) (hn : 0 < n) (hn84 : n ≤ 84) :
      fourNinthsSelectedDivisors A n = fourNinthsSelectedDivisors P n := by
    ext d
    unfold fourNinthsSelectedDivisors
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd84 : d ≤ 84 := (Nat.le_of_dvd hn hdvd).trans hn84
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 84
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd84).2 hdA⟩
    · rintro ⟨hddiv, hdP⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd84 : d ≤ 84 := (Nat.le_of_dvd hn hdvd).trans hn84
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 84 at hdP
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd84).1 hdP⟩
  change ((fourNinthsSelectedDivisors A 42 ∪
      fourNinthsSelectedDivisors A 28) ∪
        fourNinthsSelectedDivisors A 12).card = 6
  rw [hselected 42 (by norm_num) (by norm_num),
    hselected 28 (by norm_num) (by norm_num),
    hselected 12 (by norm_num) (by norm_num)]
  simp only [fourNinthsSelectedDivisors, P, Finset.mem_coe]
  native_decide

/-- Exact subtraction-free seven-column identity at positive multiples of
`84`. -/
theorem fourNinthsHeptadicUnionLoad_sevenColumn (k : ℕ) :
    let n := 84 * (k + 1)
    let A := greedyMersenneSupport (4 / 9 : ℝ)
    fourNinthsHeptadicUnionLoad n + supportCoeff A (n / 6) +
          supportCoeff A (n / 14) + supportCoeff A (n / 21) =
      supportCoeff A (n / 2) + supportCoeff A (n / 3) +
          supportCoeff A (n / 7) + supportCoeff A (n / 42) := by
  dsimp only
  let m := k + 1
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h := fourNinthsSelectedDivisors_union_three_card_identity A
    (a := 42 * m) (b := 28 * m) (c := 12 * m)
    (by positivity) (by positivity) (by positivity)
  have h2 : 84 * (k + 1) / 2 = 42 * m := by dsimp [m]; omega
  have h3 : 84 * (k + 1) / 3 = 28 * m := by dsimp [m]; omega
  have h7 : 84 * (k + 1) / 7 = 12 * m := by dsimp [m]; omega
  have h6 : 84 * (k + 1) / 6 = 14 * m := by dsimp [m]; omega
  have h14 : 84 * (k + 1) / 14 = 6 * m := by dsimp [m]; omega
  have h21 : 84 * (k + 1) / 21 = 4 * m := by dsimp [m]; omega
  have h42 : 84 * (k + 1) / 42 = 2 * m := by dsimp [m]; omega
  dsimp [fourNinthsHeptadicUnionLoad]
  rw [h2, h3, h7, h6, h14, h21, h42]
  norm_num [Nat.gcd_mul_right] at h
  simpa only [A, Finset.union_assoc] using h

/-- The `2·3·7` causal union is a subset of the full selected-divisor load. -/
theorem fourNinthsHeptadicUnionLoad_le_supportCoeff
    {n : ℕ} (hn : 0 < n) (h42 : 42 ∣ n) :
    fourNinthsHeptadicUnionLoad n ≤
      supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h2 : 2 ∣ n := (show 2 ∣ 42 by norm_num).trans h42
  have h3 : 3 ∣ n := (show 3 ∣ 42 by norm_num).trans h42
  have h7 : 7 ∣ n := (show 7 ∣ 42 by norm_num).trans h42
  have hs2 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h2) hn
  have hs3 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h3) hn
  have hs7 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h7) hn
  rw [← fourNinthsSelectedDivisors_card A n]
  apply Finset.card_le_card
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · rcases Finset.mem_union.mp hd with hd | hd
    · exact hs2 hd
    · exact hs3 hd
  · exact hs7 hd

/-! ## The `2·3·5·7` causal producer -/

/-- Selected divisors already visible in at least one of the `2`, `3`, `5`,
or `7` parent columns. -/
noncomputable def fourNinthsTetraprimeUnionLoad (n : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  (((fourNinthsSelectedDivisors A (n / 2) ∪
      fourNinthsSelectedDivisors A (n / 3)) ∪
        fourNinthsSelectedDivisors A (n / 5)) ∪
          fourNinthsSelectedDivisors A (n / 7)).card

/-- Exact subtraction-free fifteen-column identity at positive multiples of
`420`. -/
theorem fourNinthsTetraprimeUnionLoad_fifteenColumn (k : ℕ) :
    let n := 420 * (k + 1)
    let A := greedyMersenneSupport (4 / 9 : ℝ)
    fourNinthsTetraprimeUnionLoad n +
          supportCoeff A (n / 6) + supportCoeff A (n / 10) +
          supportCoeff A (n / 14) + supportCoeff A (n / 15) +
          supportCoeff A (n / 21) + supportCoeff A (n / 35) +
          supportCoeff A (n / 210) =
      supportCoeff A (n / 2) + supportCoeff A (n / 3) +
          supportCoeff A (n / 5) + supportCoeff A (n / 7) +
          supportCoeff A (n / 30) + supportCoeff A (n / 42) +
          supportCoeff A (n / 70) + supportCoeff A (n / 105) := by
  dsimp only
  let m := k + 1
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h := fourNinthsSelectedDivisors_union_four_card_identity A
    (a := 210 * m) (b := 140 * m) (c := 84 * m) (d := 60 * m)
    (by positivity) (by positivity) (by positivity) (by positivity)
  have h2 : 420 * (k + 1) / 2 = 210 * m := by dsimp [m]; omega
  have h3 : 420 * (k + 1) / 3 = 140 * m := by dsimp [m]; omega
  have h5 : 420 * (k + 1) / 5 = 84 * m := by dsimp [m]; omega
  have h7 : 420 * (k + 1) / 7 = 60 * m := by dsimp [m]; omega
  have h6 : 420 * (k + 1) / 6 = 70 * m := by dsimp [m]; omega
  have h10 : 420 * (k + 1) / 10 = 42 * m := by dsimp [m]; omega
  have h14 : 420 * (k + 1) / 14 = 30 * m := by dsimp [m]; omega
  have h15 : 420 * (k + 1) / 15 = 28 * m := by dsimp [m]; omega
  have h21 : 420 * (k + 1) / 21 = 20 * m := by dsimp [m]; omega
  have h35 : 420 * (k + 1) / 35 = 12 * m := by dsimp [m]; omega
  have h30 : 420 * (k + 1) / 30 = 14 * m := by dsimp [m]; omega
  have h42 : 420 * (k + 1) / 42 = 10 * m := by dsimp [m]; omega
  have h70 : 420 * (k + 1) / 70 = 6 * m := by dsimp [m]; omega
  have h105 : 420 * (k + 1) / 105 = 4 * m := by dsimp [m]; omega
  have h210 : 420 * (k + 1) / 210 = 2 * m := by dsimp [m]; omega
  dsimp [fourNinthsTetraprimeUnionLoad]
  rw [h2, h3, h5, h7, h6, h10, h14, h15, h21, h35, h30, h42,
    h70, h105, h210]
  norm_num [Nat.gcd_mul_right] at h
  simpa only [A, Finset.union_assoc] using h

/-- Exact kernel-certified base value for the modulus-`420` normal form. -/
theorem fourNinthsTetraprimeUnionLoad_420 :
    fourNinthsTetraprimeUnionLoad 420 = 12 := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let P : Set ℕ := ↑(greedyMersennePrefixRat (4 / 9 : ℚ) 420)
  have hselected (n : ℕ) (hn : 0 < n) (hn420 : n ≤ 420) :
      fourNinthsSelectedDivisors A n = fourNinthsSelectedDivisors P n := by
    ext d
    unfold fourNinthsSelectedDivisors
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd420 : d ≤ 420 := (Nat.le_of_dvd hn hdvd).trans hn420
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 420
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd420).2 hdA⟩
    · rintro ⟨hddiv, hdP⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd420 : d ≤ 420 := (Nat.le_of_dvd hn hdvd).trans hn420
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (4 / 9 : ℚ) 420 at hdP
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd420).1 hdP⟩
  change (((fourNinthsSelectedDivisors A 210 ∪
      fourNinthsSelectedDivisors A 140) ∪
        fourNinthsSelectedDivisors A 84) ∪
          fourNinthsSelectedDivisors A 60).card = 12
  rw [hselected 210 (by norm_num) (by norm_num),
    hselected 140 (by norm_num) (by norm_num),
    hselected 84 (by norm_num) (by norm_num),
    hselected 60 (by norm_num) (by norm_num)]
  simp only [fourNinthsSelectedDivisors, P, Finset.mem_coe]
  native_decide

/-- Exact predecessor defect for the unit cofactor in the modulus-`420`
induction boundary. -/
theorem fourNinthsGreedyDefect_419 :
    fourNinthsGreedyDefect 419 = 7 := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let F := greedyMersennePrefixRat (4 / 9 : ℚ) 419
  let c : ℕ → ℕ := fun n =>
    (n.divisors.filter fun d => d ∈ F).card
  have hcoeff (n : ℕ) (hn : 0 < n) (hn419 : n ≤ 419) :
      supportCoeff A n = c n := by
    unfold supportCoeff c
    congr 1
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd419 : d ≤ 419 := (Nat.le_of_dvd hn hdvd).trans hn419
      exact ⟨hddiv,
        (mem_fourNinthsPrefixRat_iff_real_support hdpos hd419).2 hdA⟩
    · rintro ⟨hddiv, hdP⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd419 : d ≤ 419 := (Nat.le_of_dvd hn hdvd).trans hn419
      exact ⟨hddiv,
        (mem_fourNinthsPrefixRat_iff_real_support hdpos hd419).1 hdP⟩
  have hnum (N : ℕ) (hN : N ≤ 419) :
      binaryCoeffPrefixNumerator (supportCoeff A) N =
        binaryCoeffPrefixNumerator c N := by
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [binaryCoeffPrefixNumerator, binaryCoeffPrefixNumerator,
        ih (by omega), hcoeff (N + 1) (by omega) hN]
  unfold fourNinthsGreedyDefect
  rw [hnum 419 (by norm_num)]
  simp only [c, F]
  native_decide

theorem fourNinthsTetraprimeRepair_unit :
    fourNinthsGreedyDefect (420 - 1) ≤
      fourNinthsTetraprimeUnionLoad 420 := by
  rw [show 420 - 1 = 419 by norm_num, fourNinthsGreedyDefect_419,
    fourNinthsTetraprimeUnionLoad_420]
  norm_num

/-- The only prime cofactors not covered by the prime-column normal form are
`2`, `3`, `5`, and `7`; all four repair exactly. -/
theorem fourNinthsTetraprimeRepair_smallPrime
    {p : ℕ} (hp : p.Prime) (hp7 : p ≤ 7) :
    fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p) := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let F := greedyMersennePrefixRat (4 / 9 : ℚ) 2939
  let P : Set ℕ := ↑F
  let c : ℕ → ℕ := fun n =>
    (n.divisors.filter fun d => d ∈ F).card
  have hcoeff (n : ℕ) (hn : 0 < n) (hn2939 : n ≤ 2939) :
      supportCoeff A n = c n := by
    unfold supportCoeff c
    congr 1
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd2939 : d ≤ 2939 := (Nat.le_of_dvd hn hdvd).trans hn2939
      exact ⟨hddiv,
        (mem_fourNinthsPrefixRat_iff_real_support hdpos hd2939).2 hdA⟩
    · rintro ⟨hddiv, hdF⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd2939 : d ≤ 2939 := (Nat.le_of_dvd hn hdvd).trans hn2939
      exact ⟨hddiv,
        (mem_fourNinthsPrefixRat_iff_real_support hdpos hd2939).1 hdF⟩
  have hnum (N : ℕ) (hN : N ≤ 2939) :
      binaryCoeffPrefixNumerator (supportCoeff A) N =
        binaryCoeffPrefixNumerator c N := by
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [binaryCoeffPrefixNumerator, binaryCoeffPrefixNumerator,
        ih (by omega), hcoeff (N + 1) (by omega) hN]
  have hselected (n : ℕ) (hn : 0 < n) (hn2939 : n ≤ 2939) :
      fourNinthsSelectedDivisors A n = fourNinthsSelectedDivisors P n := by
    ext d
    unfold fourNinthsSelectedDivisors
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd2939 : d ≤ 2939 := (Nat.le_of_dvd hn hdvd).trans hn2939
      exact ⟨hddiv, by
        change d ∈ F
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd2939).2 hdA⟩
    · rintro ⟨hddiv, hdP⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd2939 : d ≤ 2939 := (Nat.le_of_dvd hn hdvd).trans hn2939
      exact ⟨hddiv, by
        change d ∈ F at hdP
        exact (mem_fourNinthsPrefixRat_iff_real_support hdpos hd2939).1 hdP⟩
  interval_cases p <;> norm_num at hp
  all_goals
    unfold fourNinthsGreedyDefect
    rw [hnum _ (by norm_num)]
    unfold fourNinthsTetraprimeUnionLoad
    dsimp only
    rw [hselected _ (by norm_num) (by norm_num),
      hselected _ (by norm_num) (by norm_num),
      hselected _ (by norm_num) (by norm_num),
      hselected _ (by norm_num) (by norm_num)]
    simp only [A, P, c, F, fourNinthsSelectedDivisors, Finset.mem_coe]
    native_decide

/-- The four-prime causal union is a subset of the full selected-divisor
load. -/
theorem fourNinthsTetraprimeUnionLoad_le_supportCoeff
    {n : ℕ} (hn : 0 < n) (h210 : 210 ∣ n) :
    fourNinthsTetraprimeUnionLoad n ≤
      supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n := by
  classical
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  have h2 : 2 ∣ n := (show 2 ∣ 210 by norm_num).trans h210
  have h3 : 3 ∣ n := (show 3 ∣ 210 by norm_num).trans h210
  have h5 : 5 ∣ n := (show 5 ∣ 210 by norm_num).trans h210
  have h7 : 7 ∣ n := (show 7 ∣ 210 by norm_num).trans h210
  have hs2 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h2) hn
  have hs3 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h3) hn
  have hs5 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h5) hn
  have hs7 := fourNinthsSelectedDivisors_mono_of_dvd A
    (Nat.div_dvd_of_dvd h7) hn
  rw [← fourNinthsSelectedDivisors_card A n]
  apply Finset.card_le_card
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · rcases Finset.mem_union.mp hd with hd | hd
    · rcases Finset.mem_union.mp hd with hd | hd
      · exact hs2 hd
      · exact hs3 hd
    · exact hs5 hd
  · exact hs7 hd

/-! ## Prime-cofactor normal form -/

/-- The moving `420p` support column obtained by pulling the actual support
back through multiplication by a prime cofactor. -/
noncomputable def fourNinthsTetraprimePrimePullbackColumnLoad (p : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  (((fourNinthsSelectedDivisors B 210 ∪
      fourNinthsSelectedDivisors B 140) ∪
        fourNinthsSelectedDivisors B 84) ∪
          fourNinthsSelectedDivisors B 60).card

/-- The literal twenty-three-position support column on the proper divisors
of `420`, pulled forward by a cofactor. -/
noncomputable def fourNinthsTetraprimePrimeProperDivisorColumnLoad
    (p : ℕ) : ℕ := by
  classical
  exact (((420 : ℕ).divisors.erase 420).filter fun d =>
    p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card

theorem fourNinths_properDivisors_420_card :
    ((420 : ℕ).divisors.erase 420).card = 23 := by
  native_decide

theorem fourNinthsTetraprimePrimeProperDivisorColumnLoad_le_twenty_three
    (p : ℕ) :
    fourNinthsTetraprimePrimeProperDivisorColumnLoad p ≤ 23 := by
  classical
  unfold fourNinthsTetraprimePrimeProperDivisorColumnLoad
  calc
    (((420 : ℕ).divisors.erase 420).filter fun d =>
      p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card ≤
        ((420 : ℕ).divisors.erase 420).card := Finset.card_filter_le _ _
    _ = 23 := fourNinths_properDivisors_420_card

/-- The four-parent pullback union is exactly the literal proper-divisor
column of `420`. -/
theorem fourNinthsTetraprimePrimePullbackColumnLoad_eq_properDivisors
    (p : ℕ) :
    fourNinthsTetraprimePrimePullbackColumnLoad p =
      fourNinthsTetraprimePrimeProperDivisorColumnLoad p := by
  classical
  have hdivisors :
      (((210 : ℕ).divisors ∪ (140 : ℕ).divisors) ∪
          (84 : ℕ).divisors) ∪ (60 : ℕ).divisors =
        (420 : ℕ).divisors.erase 420 := by
    native_decide
  simp only [fourNinthsTetraprimePrimePullbackColumnLoad,
    fourNinthsTetraprimePrimeProperDivisorColumnLoad,
    fourNinthsSelectedDivisors, mem_supportPullback]
  rw [← Finset.filter_union, ← Finset.filter_union,
    ← Finset.filter_union, hdivisors]

private theorem fourNinths_tetraprimeFixedColumn_coprime_of_prime_gt_seven
    {p c : ℕ} (hp : p.Prime) (hp7 : 7 < p) (hc : c ∣ 420) :
    c.Coprime p := by
  have hp2 : p.Coprime 2 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp3 : p.Coprime 3 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp5 : p.Coprime 5 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp7' : p.Coprime 7 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp420' : p.Coprime ((2 ^ 2) * 3 * 5 * 7) :=
    (((Nat.Coprime.pow_right 2 hp2).mul_right hp3).mul_right hp5).mul_right hp7'
  have h420p : (420 : ℕ).Coprime p := by
    have := hp420'.symm
    norm_num at this ⊢
    exact this
  exact Nat.Coprime.of_dvd_left hc h420p

/-- At a prime cofactor above seven, the modulus-`420` causal union splits
exactly into its fixed base column and a twenty-three-position pullback
column. -/
theorem fourNinthsTetraprimeUnionLoad_primeColumn
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    fourNinthsTetraprimeUnionLoad (420 * p) =
      fourNinthsTetraprimeUnionLoad 420 +
        fourNinthsTetraprimePrimePullbackColumnLoad p := by
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  have hcop (c : ℕ) (hc : c ∣ 420) : c.Coprime p :=
    fourNinths_tetraprimeFixedColumn_coprime_of_prime_gt_seven hp hp7 hc
  have hsplit (c : ℕ) (hc : c ∣ 420) :
      supportCoeff A (c * p) = supportCoeff A c + supportCoeff B c := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop c hc)
  have h210 := hsplit 210 (by norm_num)
  have h140 := hsplit 140 (by norm_num)
  have h84 := hsplit 84 (by norm_num)
  have h60 := hsplit 60 (by norm_num)
  have h70 := hsplit 70 (by norm_num)
  have h42 := hsplit 42 (by norm_num)
  have h30 := hsplit 30 (by norm_num)
  have h28 := hsplit 28 (by norm_num)
  have h20 := hsplit 20 (by norm_num)
  have h12 := hsplit 12 (by norm_num)
  have h14 := hsplit 14 (by norm_num)
  have h10 := hsplit 10 (by norm_num)
  have h6 := hsplit 6 (by norm_num)
  have h4 := hsplit 4 (by norm_num)
  have h2 := hsplit 2 (by norm_num)
  have hpPred : p - 1 + 1 = p := by omega
  have hfifteenp := fourNinthsTetraprimeUnionLoad_fifteenColumn (p - 1)
  dsimp only at hfifteenp
  rw [hpPred] at hfifteenp
  have hp2 : 420 * p / 2 = 210 * p := by omega
  have hp3 : 420 * p / 3 = 140 * p := by omega
  have hp5div : 420 * p / 5 = 84 * p := by omega
  have hp7div : 420 * p / 7 = 60 * p := by omega
  have hp6 : 420 * p / 6 = 70 * p := by omega
  have hp10 : 420 * p / 10 = 42 * p := by omega
  have hp14 : 420 * p / 14 = 30 * p := by omega
  have hp15 : 420 * p / 15 = 28 * p := by omega
  have hp21 : 420 * p / 21 = 20 * p := by omega
  have hp35 : 420 * p / 35 = 12 * p := by omega
  have hp30 : 420 * p / 30 = 14 * p := by omega
  have hp42 : 420 * p / 42 = 10 * p := by omega
  have hp70 : 420 * p / 70 = 6 * p := by omega
  have hp105 : 420 * p / 105 = 4 * p := by omega
  have hp210 : 420 * p / 210 = 2 * p := by omega
  rw [hp2, hp3, hp5div, hp7div, hp6, hp10, hp14, hp15, hp21, hp35,
    hp30, hp42, hp70, hp105, hp210] at hfifteenp
  have hfifteen1 := fourNinthsTetraprimeUnionLoad_fifteenColumn 0
  norm_num at hfifteen1
  have hcolumnRaw := fourNinthsSelectedDivisors_union_four_card_identity B
    (a := 210) (b := 140) (c := 84) (d := 60)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcolumn :
      fourNinthsTetraprimePrimePullbackColumnLoad p +
          supportCoeff B 70 + supportCoeff B 42 + supportCoeff B 30 +
          supportCoeff B 28 + supportCoeff B 20 + supportCoeff B 12 +
          supportCoeff B 2 =
        supportCoeff B 210 + supportCoeff B 140 + supportCoeff B 84 +
          supportCoeff B 60 + supportCoeff B 14 + supportCoeff B 10 +
          supportCoeff B 6 + supportCoeff B 4 := by
    norm_num at hcolumnRaw
    simpa only [fourNinthsTetraprimePrimePullbackColumnLoad, A, B,
      Finset.union_assoc] using hcolumnRaw
  dsimp only [A, B] at h210 h140 h84 h60 h70 h42 h30 h28 h20 h12
  dsimp only [A, B] at h14 h10 h6 h4 h2 hcolumn hfifteenp hfifteen1 ⊢
  omega

/-- Numerical modulus-`420` prime-column boundary: all dependence on the
prime is carried by one twenty-three-position pullback column. -/
theorem fourNinthsTetraprimePrimeRepair_iff_defect_le_column_add_twelve
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    fourNinthsGreedyDefect (420 * p - 1) ≤
        fourNinthsTetraprimeUnionLoad (420 * p) ↔
      fourNinthsGreedyDefect (420 * p - 1) ≤
        fourNinthsTetraprimePrimePullbackColumnLoad p + 12 := by
  rw [fourNinthsTetraprimeUnionLoad_primeColumn hp hp7,
    fourNinthsTetraprimeUnionLoad_420]
  omega

/-- Any modulus-`420` prime-row causal repair has defect at most `35`. -/
theorem fourNinthsTetraprimePrimeRepair_defect_le_thirty_five
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hrepair : fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p)) :
    fourNinthsGreedyDefect (420 * p - 1) ≤ 35 := by
  have hcolumn :=
    (fourNinthsTetraprimePrimeRepair_iff_defect_le_column_add_twelve hp hp7).1
      hrepair
  have hle :=
    fourNinthsTetraprimePrimeProperDivisorColumnLoad_le_twenty_three p
  rw [fourNinthsTetraprimePrimePullbackColumnLoad_eq_properDivisors] at hcolumn
  omega

/-- The moving `84p` support column obtained by pulling the actual support
back through multiplication by a prime cofactor. -/
noncomputable def fourNinthsHeptadicPrimePullbackColumnLoad (p : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  ((fourNinthsSelectedDivisors B 42 ∪
      fourNinthsSelectedDivisors B 28) ∪
        fourNinthsSelectedDivisors B 12).card

/-- The literal eleven-position support column on the proper divisors of
`84`, pulled forward by a cofactor. -/
noncomputable def fourNinthsHeptadicPrimeProperDivisorColumnLoad
    (p : ℕ) : ℕ := by
  classical
  exact (((84 : ℕ).divisors.erase 84).filter fun d =>
    p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card

theorem fourNinths_properDivisors_84_card :
    ((84 : ℕ).divisors.erase 84).card = 11 := by
  native_decide

theorem fourNinthsHeptadicPrimeProperDivisorColumnLoad_le_eleven (p : ℕ) :
    fourNinthsHeptadicPrimeProperDivisorColumnLoad p ≤ 11 := by
  classical
  unfold fourNinthsHeptadicPrimeProperDivisorColumnLoad
  calc
    (((84 : ℕ).divisors.erase 84).filter fun d =>
      p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card ≤
        ((84 : ℕ).divisors.erase 84).card := Finset.card_filter_le _ _
    _ = 11 := fourNinths_properDivisors_84_card

/-- The moving heptadic pullback column is exactly the literal proper-divisor
column of width eleven. -/
theorem fourNinthsHeptadicPrimePullbackColumnLoad_eq_properDivisors (p : ℕ) :
    fourNinthsHeptadicPrimePullbackColumnLoad p =
      fourNinthsHeptadicPrimeProperDivisorColumnLoad p := by
  classical
  have hdivisors :
      ((42 : ℕ).divisors ∪ (28 : ℕ).divisors) ∪ (12 : ℕ).divisors =
        (84 : ℕ).divisors.erase 84 := by
    native_decide
  simp only [fourNinthsHeptadicPrimePullbackColumnLoad,
    fourNinthsHeptadicPrimeProperDivisorColumnLoad,
    fourNinthsSelectedDivisors, mem_supportPullback]
  rw [← Finset.filter_union, ← Finset.filter_union, hdivisors]

/-- The moving selected-divisor column obtained by pulling the actual support
back through multiplication by a prime cofactor. -/
noncomputable def fourNinthsPrimePullbackColumnLoad (p : ℕ) : ℕ :=
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  ((fourNinthsSelectedDivisors B 60 ∪
      fourNinthsSelectedDivisors B 40) ∪
        fourNinthsSelectedDivisors B 24).card

/-- The literal fifteen-position support column on the proper divisors of
`120`, pulled forward by a cofactor. -/
noncomputable def fourNinthsPrimeProperDivisorColumnLoad (p : ℕ) : ℕ := by
  classical
  exact (((120 : ℕ).divisors.erase 120).filter fun d =>
    p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card

theorem fourNinths_properDivisors_120_card :
    ((120 : ℕ).divisors.erase 120).card = 15 := by
  native_decide

theorem fourNinthsPrimeProperDivisorColumnLoad_le_fifteen (p : ℕ) :
    fourNinthsPrimeProperDivisorColumnLoad p ≤ 15 := by
  classical
  unfold fourNinthsPrimeProperDivisorColumnLoad
  calc
    (((120 : ℕ).divisors.erase 120).filter fun d =>
      p * d ∈ greedyMersenneSupport (4 / 9 : ℝ)).card ≤
        ((120 : ℕ).divisors.erase 120).card := Finset.card_filter_le _ _
    _ = 15 := fourNinths_properDivisors_120_card

/-- The moving prime pullback column is exactly the preceding literal
fifteen-position column. -/
theorem fourNinthsPrimePullbackColumnLoad_eq_properDivisors (p : ℕ) :
    fourNinthsPrimePullbackColumnLoad p =
      fourNinthsPrimeProperDivisorColumnLoad p := by
  classical
  have hdivisors :
      ((60 : ℕ).divisors ∪ (40 : ℕ).divisors) ∪ (24 : ℕ).divisors =
        (120 : ℕ).divisors.erase 120 := by
    native_decide
  simp only [fourNinthsPrimePullbackColumnLoad,
    fourNinthsPrimeProperDivisorColumnLoad, fourNinthsSelectedDivisors,
    mem_supportPullback]
  rw [← Finset.filter_union, ← Finset.filter_union, hdivisors]

private theorem fourNinths_heptadicFixedColumn_coprime_of_prime_gt_seven
    {p c : ℕ} (hp : p.Prime) (hp7 : 7 < p) (hc : c ∣ 84) :
    c.Coprime p := by
  have hp2 : p.Coprime 2 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp3 : p.Coprime 3 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp7' : p.Coprime 7 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp84' : p.Coprime ((2 ^ 2) * 3 * 7) :=
    ((Nat.Coprime.pow_right 2 hp2).mul_right hp3).mul_right hp7'
  have h84p : (84 : ℕ).Coprime p := by
    have := hp84'.symm
    norm_num at this ⊢
    exact this
  exact Nat.Coprime.of_dvd_left hc h84p

/-- At a prime cofactor above seven, the modulus-`84` causal union splits
exactly into its fixed base column and an eleven-position pullback column. -/
theorem fourNinthsHeptadicUnionLoad_primeColumn
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    fourNinthsHeptadicUnionLoad (84 * p) =
      fourNinthsHeptadicUnionLoad 84 +
        fourNinthsHeptadicPrimePullbackColumnLoad p := by
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  have hcop (c : ℕ) (hc : c ∣ 84) : c.Coprime p :=
    fourNinths_heptadicFixedColumn_coprime_of_prime_gt_seven hp hp7 hc
  have hsplit (c : ℕ) (hc : c ∣ 84) :
      supportCoeff A (c * p) = supportCoeff A c + supportCoeff B c := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop c hc)
  have h42 := hsplit 42 (by norm_num)
  have h28 := hsplit 28 (by norm_num)
  have h12 := hsplit 12 (by norm_num)
  have h14 := hsplit 14 (by norm_num)
  have h6 := hsplit 6 (by norm_num)
  have h4 := hsplit 4 (by norm_num)
  have h2 := hsplit 2 (by norm_num)
  have hpPred : p - 1 + 1 = p := by omega
  have hsevenp := fourNinthsHeptadicUnionLoad_sevenColumn (p - 1)
  dsimp only at hsevenp
  rw [hpPred] at hsevenp
  have hp2 : 84 * p / 2 = 42 * p := by omega
  have hp3 : 84 * p / 3 = 28 * p := by omega
  have hp7div : 84 * p / 7 = 12 * p := by omega
  have hp6 : 84 * p / 6 = 14 * p := by omega
  have hp14 : 84 * p / 14 = 6 * p := by omega
  have hp21 : 84 * p / 21 = 4 * p := by omega
  have hp42 : 84 * p / 42 = 2 * p := by omega
  rw [hp2, hp3, hp7div, hp6, hp14, hp21, hp42] at hsevenp
  have hseven1 := fourNinthsHeptadicUnionLoad_sevenColumn 0
  norm_num at hseven1
  have hcolumnRaw := fourNinthsSelectedDivisors_union_three_card_identity B
    (a := 42) (b := 28) (c := 12) (by norm_num) (by norm_num) (by norm_num)
  have hcolumn :
      fourNinthsHeptadicPrimePullbackColumnLoad p + supportCoeff B 14 +
          supportCoeff B 6 + supportCoeff B 4 =
        supportCoeff B 42 + supportCoeff B 28 + supportCoeff B 12 +
          supportCoeff B 2 := by
    norm_num at hcolumnRaw
    simpa only [fourNinthsHeptadicPrimePullbackColumnLoad, A, B,
      Finset.union_assoc] using hcolumnRaw
  dsimp only [A, B] at h42 h28 h12 h14 h6 h4 h2 hcolumn hsevenp hseven1 ⊢
  omega

/-- Numerical modulus-`84` prime-column boundary: all dependence on the prime
is carried by one eleven-position pullback column. -/
theorem fourNinthsHeptadicPrimeRepair_iff_defect_le_column_add_six
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    fourNinthsGreedyDefect (84 * p - 1) ≤
        fourNinthsHeptadicUnionLoad (84 * p) ↔
      fourNinthsGreedyDefect (84 * p - 1) ≤
        fourNinthsHeptadicPrimePullbackColumnLoad p + 6 := by
  rw [fourNinthsHeptadicUnionLoad_primeColumn hp hp7,
    fourNinthsHeptadicUnionLoad_84]
  omega

/-- Any modulus-`84` prime-row causal repair has defect at most `17`. -/
theorem fourNinthsHeptadicPrimeRepair_defect_le_seventeen
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hrepair : fourNinthsGreedyDefect (84 * p - 1) ≤
      fourNinthsHeptadicUnionLoad (84 * p)) :
    fourNinthsGreedyDefect (84 * p - 1) ≤ 17 := by
  have hcolumn :=
    (fourNinthsHeptadicPrimeRepair_iff_defect_le_column_add_six hp hp7).1
      hrepair
  have hle := fourNinthsHeptadicPrimeProperDivisorColumnLoad_le_eleven p
  rw [fourNinthsHeptadicPrimePullbackColumnLoad_eq_properDivisors] at hcolumn
  omega

private theorem fourNinths_fixedColumn_coprime_of_prime_gt_five
    {p c : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hc : c ∣ 120) :
    c.Coprime p := by
  have hp2 : p.Coprime 2 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp3 : p.Coprime 3 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp5' : p.Coprime 5 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp120' : p.Coprime ((2 ^ 3) * 3 * 5) :=
    ((Nat.Coprime.pow_right 3 hp2).mul_right hp3).mul_right hp5'
  have h120p : (120 : ℕ).Coprime p := by
    have := hp120'.symm
    norm_num at this ⊢
    exact this
  exact Nat.Coprime.of_dvd_left hc h120p

/-- At a prime cofactor above five, the causal union splits exactly into its
fixed base column and a finite pulled-back column. -/
theorem fourNinthsPrimorialUnionLoad_primeColumn
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    fourNinthsPrimorialUnionLoad (120 * p) =
      fourNinthsPrimorialUnionLoad 120 +
        fourNinthsPrimePullbackColumnLoad p := by
  let A := greedyMersenneSupport (4 / 9 : ℝ)
  let B := supportPullback p A
  have hcop (c : ℕ) (hc : c ∣ 120) : c.Coprime p :=
    fourNinths_fixedColumn_coprime_of_prime_gt_five hp hp5 hc
  have hsplit (c : ℕ) (hc : c ∣ 120) :
      supportCoeff A (c * p) = supportCoeff A c + supportCoeff B c := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop c hc)
  have h60 := hsplit 60 (by norm_num)
  have h40 := hsplit 40 (by norm_num)
  have h24 := hsplit 24 (by norm_num)
  have h20 := hsplit 20 (by norm_num)
  have h12 := hsplit 12 (by norm_num)
  have h8 := hsplit 8 (by norm_num)
  have h4 := hsplit 4 (by norm_num)
  have hpPred : p - 1 + 1 = p := by omega
  have hsevenp := fourNinthsPrimorialUnionLoad_sevenColumn (p - 1)
  dsimp only at hsevenp
  rw [hpPred] at hsevenp
  have hp2 : 120 * p / 2 = 60 * p := by omega
  have hp3 : 120 * p / 3 = 40 * p := by omega
  have hp5div : 120 * p / 5 = 24 * p := by omega
  have hp6 : 120 * p / 6 = 20 * p := by omega
  have hp10 : 120 * p / 10 = 12 * p := by omega
  have hp15 : 120 * p / 15 = 8 * p := by omega
  have hp30 : 120 * p / 30 = 4 * p := by omega
  rw [hp2, hp3, hp5div, hp6, hp10, hp15, hp30] at hsevenp
  have hseven1 := fourNinthsPrimorialUnionLoad_sevenColumn 0
  norm_num at hseven1
  have hcolumnRaw := fourNinthsSelectedDivisors_union_three_card_identity B
    (a := 60) (b := 40) (c := 24) (by norm_num) (by norm_num) (by norm_num)
  have hcolumn :
      fourNinthsPrimePullbackColumnLoad p + supportCoeff B 20 +
          supportCoeff B 12 + supportCoeff B 8 =
        supportCoeff B 60 + supportCoeff B 40 + supportCoeff B 24 +
          supportCoeff B 4 := by
    norm_num at hcolumnRaw
    simpa only [fourNinthsPrimePullbackColumnLoad, A, B,
      Finset.union_assoc] using hcolumnRaw
  dsimp only [A, B] at h60 h40 h24 h20 h12 h8 h4 hcolumn hsevenp hseven1 ⊢
  omega

theorem fourNinthsPrimePrimorialRepair_iff_column
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    fourNinthsGreedyDefect (120 * p - 1) ≤
        fourNinthsPrimorialUnionLoad (120 * p) ↔
      fourNinthsGreedyDefect (120 * p - 1) ≤
        fourNinthsPrimorialUnionLoad 120 +
          fourNinthsPrimePullbackColumnLoad p := by
  rw [fourNinthsPrimorialUnionLoad_primeColumn hp hp5]

/-- Numerical prime-column boundary: all dependence on the prime is carried
by one finite pullback column. -/
theorem fourNinthsPrimePrimorialRepair_iff_defect_le_column_add_ten
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    fourNinthsGreedyDefect (120 * p - 1) ≤
        fourNinthsPrimorialUnionLoad (120 * p) ↔
      fourNinthsGreedyDefect (120 * p - 1) ≤
        fourNinthsPrimePullbackColumnLoad p + 10 := by
  rw [fourNinthsPrimorialUnionLoad_primeColumn hp hp5,
    fourNinthsPrimorialUnionLoad_120]
  omega

/-- Any prime-row repair has defect at most `25`; a larger prime-row defect
would be an immediate finite-column falsifier. -/
theorem fourNinthsPrimePrimorialRepair_defect_le_twenty_five
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hrepair : fourNinthsGreedyDefect (120 * p - 1) ≤
      fourNinthsPrimorialUnionLoad (120 * p)) :
    fourNinthsGreedyDefect (120 * p - 1) ≤ 25 := by
  have hcolumn :=
    (fourNinthsPrimePrimorialRepair_iff_defect_le_column_add_ten hp hp5).1
      hrepair
  have hle := fourNinthsPrimeProperDivisorColumnLoad_le_fifteen p
  rw [fourNinthsPrimePullbackColumnLoad_eq_properDivisors] at hcolumn
  omega

/-- The `4/9` floor bit immediately before every positive multiple of `120`
is zero. -/
theorem fourNinthsFloorBit_pred_multiple120 (k : ℕ) :
    fourNinthsFloorBit (120 * (k + 1) - 1) = 0 := by
  let t := 20 * (k + 1) - 1
  have hexp : 120 * (k + 1) - 1 = 6 * t + 5 := by
    dsimp [t]
    omega
  have hbase : 2 ^ 6 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
  have hfive : 2 ^ 5 ≡ 5 [MOD 9] := by norm_num [Nat.ModEq]
  have hpow : (2 ^ 6) ^ t ≡ 1 ^ t [MOD 9] := hbase.pow t
  have hprod : (2 ^ 6) ^ t * 2 ^ 5 ≡ 1 ^ t * 5 [MOD 9] :=
    hpow.mul hfive
  have hmodPow : 2 ^ (120 * (k + 1) - 1) % 9 = 5 := by
    change 2 ^ (120 * (k + 1) - 1) ≡ 5 [MOD 9]
    rw [hexp, pow_add, pow_mul]
    simpa using hprod
  have hmod : (4 * 2 ^ (120 * (k + 1) - 1)) % 9 = 2 := by
    have hfour : 4 ≡ 4 [MOD 9] := Nat.ModEq.refl 4
    have := hfour.mul (show 2 ^ (120 * (k + 1) - 1) ≡ 5 [MOD 9] by
      simpa [Nat.ModEq] using hmodPow)
    norm_num [Nat.ModEq] at this ⊢
    exact this
  rw [fourNinthsFloorBit_eq_two_mul_mod_div, hmod]
  norm_num

/-- The `4/9` floor bit immediately before every positive multiple of `84`
is zero. -/
theorem fourNinthsFloorBit_pred_multiple84 (k : ℕ) :
    fourNinthsFloorBit (84 * (k + 1) - 1) = 0 := by
  let t := 14 * (k + 1) - 1
  have hexp : 84 * (k + 1) - 1 = 6 * t + 5 := by
    dsimp [t]
    omega
  have hbase : 2 ^ 6 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
  have hfive : 2 ^ 5 ≡ 5 [MOD 9] := by norm_num [Nat.ModEq]
  have hpow : (2 ^ 6) ^ t ≡ 1 ^ t [MOD 9] := hbase.pow t
  have hprod : (2 ^ 6) ^ t * 2 ^ 5 ≡ 1 ^ t * 5 [MOD 9] :=
    hpow.mul hfive
  have hmodPow : 2 ^ (84 * (k + 1) - 1) % 9 = 5 := by
    change 2 ^ (84 * (k + 1) - 1) ≡ 5 [MOD 9]
    rw [hexp, pow_add, pow_mul]
    simpa using hprod
  have hmod : (4 * 2 ^ (84 * (k + 1) - 1)) % 9 = 2 := by
    have hfour : 4 ≡ 4 [MOD 9] := Nat.ModEq.refl 4
    have := hfour.mul (show 2 ^ (84 * (k + 1) - 1) ≡ 5 [MOD 9] by
      simpa [Nat.ModEq] using hmodPow)
    norm_num [Nat.ModEq] at this ⊢
    exact this
  rw [fourNinthsFloorBit_eq_two_mul_mod_div, hmod]
  norm_num

/-- The `4/9` floor bit immediately before every positive multiple of `420`
is zero. -/
theorem fourNinthsFloorBit_pred_multiple420 (k : ℕ) :
    fourNinthsFloorBit (420 * (k + 1) - 1) = 0 := by
  let t := 70 * (k + 1) - 1
  have hexp : 420 * (k + 1) - 1 = 6 * t + 5 := by
    dsimp [t]
    omega
  have hbase : 2 ^ 6 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
  have hfive : 2 ^ 5 ≡ 5 [MOD 9] := by norm_num [Nat.ModEq]
  have hpow : (2 ^ 6) ^ t ≡ 1 ^ t [MOD 9] := hbase.pow t
  have hprod : (2 ^ 6) ^ t * 2 ^ 5 ≡ 1 ^ t * 5 [MOD 9] :=
    hpow.mul hfive
  have hmodPow : 2 ^ (420 * (k + 1) - 1) % 9 = 5 := by
    change 2 ^ (420 * (k + 1) - 1) ≡ 5 [MOD 9]
    rw [hexp, pow_add, pow_mul]
    simpa using hprod
  have hmod : (4 * 2 ^ (420 * (k + 1) - 1)) % 9 = 2 := by
    have hfour : 4 ≡ 4 [MOD 9] := Nat.ModEq.refl 4
    have := hfour.mul (show 2 ^ (420 * (k + 1) - 1) ≡ 5 [MOD 9] by
      simpa [Nat.ModEq] using hmodPow)
    norm_num [Nat.ModEq] at this ⊢
    exact this
  rw [fourNinthsFloorBit_eq_two_mul_mod_div, hmod]
  norm_num

/-- Open producer corresponding exactly to the audited seven-column law. -/
def FourNinthsMultiple120PrimorialRepair : Prop :=
  ∀ k : ℕ,
    fourNinthsGreedyDefect (120 * (k + 1) - 1) ≤
      fourNinthsPrimorialUnionLoad (120 * (k + 1))

/-- The causal seven-column producer supplies an actual repair at every
positive multiple of `120`. -/
theorem fourNinths_multiple120RepairSupply_of_primorialRepair
    (hrepair : FourNinthsMultiple120PrimorialRepair) :
    FourNinthsMultiple120RepairSupply := by
  intro k
  let n := 120 * (k + 1)
  have hn : 0 < n := by simp [n]
  have h30 : 30 ∣ n := by dsimp [n]; omega
  have hload :
      fourNinthsGreedyDefect (n - 1) ≤
        supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n :=
    (hrepair k).trans (fourNinthsPrimorialUnionLoad_le_supportCoeff hn h30)
  have hpred : n - 1 + 1 = n := by omega
  have hrec := fourNinthsGreedyDefect_succ (n - 1)
  rw [hpred] at hrec
  have hbit : fourNinthsFloorBit (n - 1) = 0 := by
    simpa only [n] using fourNinthsFloorBit_pred_multiple120 k
  have hloadZ :
      (fourNinthsGreedyDefect (n - 1) : ℤ) ≤
        (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n : ℤ) := by
    exact_mod_cast hload
  unfold FourNinthsOneStepRepairSucc
  rw [hbit] at hrec
  rw [show 120 * (k + 1) - 1 + 1 = n by omega]
  exact_mod_cast (show
    (fourNinthsGreedyDefect n : ℤ) ≤
      (fourNinthsGreedyDefect (n - 1) : ℤ) by omega)

theorem four_ninths_mem_of_primorialRepair
    (hrepair : FourNinthsMultiple120PrimorialRepair) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet :=
  four_ninths_mem_of_multiple120RepairSupply
    (fourNinths_multiple120RepairSupply_of_primorialRepair hrepair)

/-- **Exact seven-column endpoint.**  The audited all-depth causal inequality
would refute the universal irrationality statement. -/
theorem not_universal_of_fourNinths_primorialRepair
    (hrepair : FourNinthsMultiple120PrimorialRepair) :
    ¬ UniversalMersenneSubseriesIrrationality :=
  not_universal_of_fourNinths_multiple120RepairSupply
    (fourNinths_multiple120RepairSupply_of_primorialRepair hrepair)

/-- Open producer corresponding exactly to the audited `2·3·7`
seven-column law. -/
def FourNinthsMultiple84HeptadicRepair : Prop :=
  ∀ k : ℕ,
    fourNinthsGreedyDefect (84 * (k + 1) - 1) ≤
      fourNinthsHeptadicUnionLoad (84 * (k + 1))

/-- The `2·3·7` causal producer supplies an actual repair at every positive
multiple of `84`. -/
theorem fourNinths_multiple84RepairSupply_of_heptadicRepair
    (hrepair : FourNinthsMultiple84HeptadicRepair) (k : ℕ) :
    FourNinthsOneStepRepairSucc (84 * (k + 1) - 1) := by
  let n := 84 * (k + 1)
  have hn : 0 < n := by simp [n]
  have h42 : 42 ∣ n := by dsimp [n]; omega
  have hload :
      fourNinthsGreedyDefect (n - 1) ≤
        supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n :=
    (hrepair k).trans (fourNinthsHeptadicUnionLoad_le_supportCoeff hn h42)
  have hpred : n - 1 + 1 = n := by omega
  have hrec := fourNinthsGreedyDefect_succ (n - 1)
  rw [hpred] at hrec
  have hbit : fourNinthsFloorBit (n - 1) = 0 := by
    simpa only [n] using fourNinthsFloorBit_pred_multiple84 k
  have hloadZ :
      (fourNinthsGreedyDefect (n - 1) : ℤ) ≤
        (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n : ℤ) := by
    exact_mod_cast hload
  unfold FourNinthsOneStepRepairSucc
  rw [hbit] at hrec
  rw [show 84 * (k + 1) - 1 + 1 = n by omega]
  exact_mod_cast (show
    (fourNinthsGreedyDefect n : ℤ) ≤
      (fourNinthsGreedyDefect (n - 1) : ℤ) by omega)

/-- The modulus-`84` producer is cofinal and therefore puts `4/9` in the
Mersenne achievement set. -/
theorem four_ninths_mem_of_heptadicRepair
    (hrepair : FourNinthsMultiple84HeptadicRepair) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet := by
  apply four_ninths_mem_mersenneAchievementSet_of_repairCofinal
  intro K
  refine ⟨84 * (K + 1) - 1, ?_,
    fourNinths_multiple84RepairSupply_of_heptadicRepair hrepair K⟩
  omega

/-- **Exact modulus-`84` endpoint.** The all-depth `2·3·7` causal inequality
would refute the universal irrationality statement. -/
theorem not_universal_of_fourNinths_heptadicRepair
    (hrepair : FourNinthsMultiple84HeptadicRepair) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  apply not_universal_of_fourNinths_repairCofinal
  intro K
  refine ⟨84 * (K + 1) - 1, ?_,
    fourNinths_multiple84RepairSupply_of_heptadicRepair hrepair K⟩
  omega

/-- Open four-prime producer corresponding to the audited modulus-`420`
fifteen-column law. -/
def FourNinthsMultiple420TetraprimeRepair : Prop :=
  ∀ k : ℕ,
    fourNinthsGreedyDefect (420 * (k + 1) - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * (k + 1))

/-- Prime-cofactor half of the modulus-`420` induction boundary. -/
def FourNinthsMultiple420PrimeBoundary : Prop :=
  ∀ p : ℕ, p.Prime →
    fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p)

/-- The genuinely moving part of the prime boundary.  The four smaller primes
are a finite kernel-checkable base and should not obscure the all-depth
arithmetic obligation. -/
def FourNinthsMultiple420LargePrimeBoundary : Prop :=
  ∀ p : ℕ, p.Prime → 7 < p →
    fourNinthsGreedyDefect (420 * p - 1) ≤
      fourNinthsTetraprimeUnionLoad (420 * p)

/-- A phase-free composite boundary suggested by the exact unit margin.  It
asks for five units of causal slack on every composite cofactor. -/
def FourNinthsMultiple420CompositeMarginFive : Prop :=
  ∀ k : ℕ, 1 < k → ¬ k.Prime →
    fourNinthsGreedyDefect (420 * k - 1) + 5 ≤
      fourNinthsTetraprimeUnionLoad (420 * k)

/-- The checked small-prime rows upgrade the genuinely moving large-prime
boundary to the full prime boundary. -/
theorem fourNinths_primeBoundary_of_largePrimeBoundary
    (hlarge : FourNinthsMultiple420LargePrimeBoundary) :
    FourNinthsMultiple420PrimeBoundary := by
  intro p hp
  by_cases hp7 : p ≤ 7
  · exact fourNinthsTetraprimeRepair_smallPrime hp hp7
  · exact hlarge p hp (by omega)

/-- A factor-lattice descent step says the causal margin at a composite
cofactor is no smaller than the margin at one proper divisor.  It is written
without natural-number subtraction so it can be consumed directly by
induction. -/
def FourNinthsMultiple420ProperDivisorDescent : Prop :=
  ∀ k : ℕ, 1 < k → ¬ k.Prime →
    ∃ a : ℕ, 0 < a ∧ a < k ∧ a ∣ k ∧
      fourNinthsGreedyDefect (420 * k - 1) +
          fourNinthsTetraprimeUnionLoad (420 * a) ≤
        fourNinthsGreedyDefect (420 * a - 1) +
          fourNinthsTetraprimeUnionLoad (420 * k)

/-- Five units of composite margin imply the factor-lattice descent, with the
unit cofactor as the canonical parent.  This removes the existential divisor
choice from the live composite obligation. -/
theorem fourNinths_properDivisorDescent_of_compositeMarginFive
    (hmargin : FourNinthsMultiple420CompositeMarginFive) :
    FourNinthsMultiple420ProperDivisorDescent := by
  intro k hk hnotprime
  refine ⟨1, by norm_num, hk, one_dvd k, ?_⟩
  have hkMargin := hmargin k hk hnotprime
  rw [Nat.mul_one, fourNinthsGreedyDefect_419,
    fourNinthsTetraprimeUnionLoad_420]
  omega

/-- Exact induction consumer for the live computational geometry: unit and
prime repair rows plus one nondecreasing proper-divisor margin step for every
composite cofactor imply the full modulus-`420` producer. -/
theorem fourNinths_tetraprimeRepair_of_primeBoundary_of_descent
    (hprime : FourNinthsMultiple420PrimeBoundary)
    (hdescent : FourNinthsMultiple420ProperDivisorDescent) :
    FourNinthsMultiple420TetraprimeRepair := by
  have hall : ∀ k : ℕ, 0 < k →
      fourNinthsGreedyDefect (420 * k - 1) ≤
        fourNinthsTetraprimeUnionLoad (420 * k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hkp : k.Prime
      · exact hprime k hkp
      by_cases hk1 : k = 1
      · simpa only [hk1, Nat.mul_one] using fourNinthsTetraprimeRepair_unit
      have hkgt : 1 < k := by omega
      obtain ⟨a, ha0, hak, -, hmargin⟩ := hdescent k hkgt hkp
      have haRepair := ih a hak ha0
      omega
  intro k
  exact hall (k + 1) (by omega)

/-- Cleaner exact consumer: prime repair plus the uniform five-unit composite
margin imply the full modulus-`420` producer. -/
theorem fourNinths_tetraprimeRepair_of_primeBoundary_of_compositeMarginFive
    (hprime : FourNinthsMultiple420PrimeBoundary)
    (hmargin : FourNinthsMultiple420CompositeMarginFive) :
    FourNinthsMultiple420TetraprimeRepair :=
  fourNinths_tetraprimeRepair_of_primeBoundary_of_descent hprime
    (fourNinths_properDivisorDescent_of_compositeMarginFive hmargin)

/-- Final sharpened interface for the live computation: only primes above
seven and the five-unit composite margin remain open. -/
theorem fourNinths_tetraprimeRepair_of_largePrimeBoundary_of_compositeMarginFive
    (hprime : FourNinthsMultiple420LargePrimeBoundary)
    (hmargin : FourNinthsMultiple420CompositeMarginFive) :
    FourNinthsMultiple420TetraprimeRepair :=
  fourNinths_tetraprimeRepair_of_primeBoundary_of_compositeMarginFive
    (fourNinths_primeBoundary_of_largePrimeBoundary hprime) hmargin

theorem fourNinths_multiple420RepairSupply_of_tetraprimeRepair
    (hrepair : FourNinthsMultiple420TetraprimeRepair) (k : ℕ) :
    FourNinthsOneStepRepairSucc (420 * (k + 1) - 1) := by
  let n := 420 * (k + 1)
  have hn : 0 < n := by simp [n]
  have h210 : 210 ∣ n := by dsimp [n]; omega
  have hload :
      fourNinthsGreedyDefect (n - 1) ≤
        supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n :=
    (hrepair k).trans (fourNinthsTetraprimeUnionLoad_le_supportCoeff hn h210)
  have hpred : n - 1 + 1 = n := by omega
  have hrec := fourNinthsGreedyDefect_succ (n - 1)
  rw [hpred] at hrec
  have hbit : fourNinthsFloorBit (n - 1) = 0 := by
    simpa only [n] using fourNinthsFloorBit_pred_multiple420 k
  have hloadZ :
      (fourNinthsGreedyDefect (n - 1) : ℤ) ≤
        (supportCoeff (greedyMersenneSupport (4 / 9 : ℝ)) n : ℤ) := by
    exact_mod_cast hload
  unfold FourNinthsOneStepRepairSucc
  rw [hbit] at hrec
  rw [show 420 * (k + 1) - 1 + 1 = n by omega]
  exact_mod_cast (show
    (fourNinthsGreedyDefect n : ℤ) ≤
      (fourNinthsGreedyDefect (n - 1) : ℤ) by omega)

theorem not_universal_of_fourNinths_tetraprimeRepair
    (hrepair : FourNinthsMultiple420TetraprimeRepair) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  apply not_universal_of_fourNinths_repairCofinal
  intro K
  refine ⟨420 * (K + 1) - 1, ?_,
    fourNinths_multiple420RepairSupply_of_tetraprimeRepair hrepair K⟩
  omega

#print axioms fourNinthsPrimorialUnionLoad_sevenColumn
#print axioms fourNinthsPrimorialUnionLoad_120
#print axioms fourNinthsPrimorialUnionLoad_primeColumn
#print axioms fourNinthsPrimePullbackColumnLoad_eq_properDivisors
#print axioms fourNinthsPrimePrimorialRepair_defect_le_twenty_five
#print axioms fourNinths_multiple120RepairSupply_of_primorialRepair
#print axioms not_universal_of_fourNinths_primorialRepair
#print axioms fourNinthsHeptadicUnionLoad_sevenColumn
#print axioms fourNinthsHeptadicUnionLoad_84
#print axioms fourNinthsHeptadicUnionLoad_primeColumn
#print axioms fourNinthsHeptadicPrimePullbackColumnLoad_eq_properDivisors
#print axioms fourNinthsHeptadicPrimeRepair_defect_le_seventeen
#print axioms fourNinths_multiple84RepairSupply_of_heptadicRepair
#print axioms not_universal_of_fourNinths_heptadicRepair
#print axioms fourNinthsTetraprimeUnionLoad_420
#print axioms fourNinthsGreedyDefect_419
#print axioms fourNinthsTetraprimeRepair_unit
#print axioms fourNinthsTetraprimeRepair_smallPrime
#print axioms fourNinthsTetraprimeUnionLoad_fifteenColumn
#print axioms fourNinthsTetraprimeUnionLoad_primeColumn
#print axioms fourNinthsTetraprimePrimePullbackColumnLoad_eq_properDivisors
#print axioms fourNinthsTetraprimePrimeRepair_defect_le_thirty_five
#print axioms fourNinths_tetraprimeRepair_of_primeBoundary_of_descent
#print axioms fourNinths_properDivisorDescent_of_compositeMarginFive
#print axioms fourNinths_tetraprimeRepair_of_primeBoundary_of_compositeMarginFive
#print axioms fourNinths_tetraprimeRepair_of_largePrimeBoundary_of_compositeMarginFive
#print axioms fourNinths_multiple420RepairSupply_of_tetraprimeRepair
#print axioms not_universal_of_fourNinths_tetraprimeRepair

end ErdosProblems.Erdos257
