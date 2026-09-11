import Erdos249257.HalfCylinderSkippedEndpointClassifier
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Exact floor-error and reset coordinates for the half-cylinder seam

This module records the rational floor error hidden by the integer seam
weights.  It proves the exact rational take comparison, derives the three
`U`/`M`/`R` updates of the corrected coordinate, and exposes the two reset
inequalities as named sockets.  The sockets are deliberately not asserted:
their universal validity is the remaining arithmetic problem.
-/

namespace Erdos249257

open Set
open HalfCarryReachability
open HalfCylinderFiniteShadow
open HalfCylinderIntegerGreedy
open scoped BigOperators

noncomputable section

/-! ## Finite rational support and floor error -/

/-- The natural exponent support encoded by a finite seam word. -/
def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)

theorem mem_seamWordSupport_iff
    {s d : ℕ} {b : SeamRowWord s} :
    d ∈ seamWordSupport b ↔
      ∃ i : Fin (s - 2), b i = true ∧ d = (i : ℕ) + 2 := by
  classical
  constructor
  · intro hd
    obtain ⟨i, hi, hdi⟩ := Finset.mem_image.mp hd
    exact ⟨i, (Finset.mem_filter.mp hi).2, hdi.symm⟩
  · rintro ⟨i, hi, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

theorem seamWordSupport_below
    {s d : ℕ} {b : SeamRowWord s} (hd : d ∈ seamWordSupport b) :
    2 ≤ d ∧ d < s := by
  obtain ⟨i, _hi, rfl⟩ := mem_seamWordSupport_iff.mp hd
  omega

theorem seamWordSupport_card_le_width
    {s : ℕ} (b : SeamRowWord s) :
    (seamWordSupport b).card ≤ s - 2 := by
  classical
  unfold seamWordSupport
  calc
    (((Finset.univ : Finset (Fin (s - 2))).filter
        (fun i => b i = true)).image
          (fun i : Fin (s - 2) => (i : ℕ) + 2)).card
        ≤ ((Finset.univ : Finset (Fin (s - 2))).filter
            (fun i => b i = true)).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin (s - 2))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = s - 2 := by simp

theorem seamWordSupport_extend_false
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordSupport (b.extend false) = seamWordSupport b := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨i, hi, hdi⟩ := mem_seamWordSupport_iff.mp hd
    by_cases hlt : (i : ℕ) < s - 2
    · refine mem_seamWordSupport_iff.mpr
        ⟨⟨i, hlt⟩, ?_, hdi⟩
      simpa [SeamRowWord.extend, hlt] using hi
    · simp [SeamRowWord.extend, hlt] at hi
  · intro hd
    obtain ⟨i, hi, hdi⟩ := mem_seamWordSupport_iff.mp hd
    let j : Fin (s + 1 - 2) := ⟨i, by omega⟩
    refine mem_seamWordSupport_iff.mpr ⟨j, ?_, ?_⟩
    · simpa [j, SeamRowWord.extend, i.isLt] using hi
    · simpa [j] using hdi

theorem seamWordSupport_extend_true
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordSupport (b.extend true) = insert s (seamWordSupport b) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨i, hi, hdi⟩ := mem_seamWordSupport_iff.mp hd
    by_cases hlt : (i : ℕ) < s - 2
    · apply Finset.mem_insert_of_mem
      refine mem_seamWordSupport_iff.mpr
        ⟨⟨i, hlt⟩, ?_, hdi⟩
      simpa [SeamRowWord.extend, hlt] using hi
    · have hilast : (i : ℕ) = s - 2 := by omega
      apply Finset.mem_insert.mpr
      left
      omega
  · intro hd
    rcases Finset.mem_insert.mp hd with hds | hd
    · subst d
      let i : Fin (s + 1 - 2) := ⟨s - 2, by omega⟩
      refine mem_seamWordSupport_iff.mpr ⟨i, ?_, ?_⟩
      · simp [i, SeamRowWord.extend]
      · simp [i, Nat.sub_add_cancel (by omega : 2 ≤ s)]
    · obtain ⟨i, hi, hdi⟩ := mem_seamWordSupport_iff.mp hd
      let j : Fin (s + 1 - 2) := ⟨i, by omega⟩
      refine mem_seamWordSupport_iff.mpr ⟨j, ?_, ?_⟩
      · simpa [j, SeamRowWord.extend, i.isLt] using hi
      · simpa [j] using hdi

theorem seamWordSupport_halfActualSeamWord
    (s : ℕ) (hs : 2 ≤ s) :
    seamWordSupport (halfActualSeamWord s) =
      halfGreedyPrefixSupport (s - 1) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨i, hi, hdi⟩ := mem_seamWordSupport_iff.mp hd
    rw [hdi]
    simpa [halfActualSeamWord] using hi
  · intro hd
    have hbelow := halfGreedyPrefixSupport_pred_below s hs d hd
    let i : Fin (s - 2) := ⟨d - 2, by omega⟩
    refine mem_seamWordSupport_iff.mpr ⟨i, ?_, ?_⟩
    · simp [i, halfActualSeamWord, Nat.sub_add_cancel hbelow.1, hd]
    · simp [i, Nat.sub_add_cancel hbelow.1]

/-- The exact rational sum selected by a seam word. -/
def seamWordRationalSum {s : ℕ} (b : SeamRowWord s) : ℚ :=
  finiteErdosSum (seamWordSupport b) 2

/-- The rational residual left by a seam word. -/
def seamWordRationalRemainder {s : ℕ} (b : SeamRowWord s) : ℚ :=
  1 / 2 - seamWordRationalSum b

theorem seamWordRationalRemainder_halfActualSeamWord
    (s : ℕ) (hs : 2 ≤ s) :
    seamWordRationalRemainder (halfActualSeamWord s) =
      greedyMersenneRemainderRat (1 / 2 : ℚ) (s - 1) := by
  rw [seamWordRationalRemainder, seamWordRationalSum,
    seamWordSupport_halfActualSeamWord s hs]
  simpa [halfGreedyPrefixSupport] using
    (greedyMersenneRemainderRat_eq_sub_finiteErdosSum
      (1 / 2 : ℚ) (s - 1)).symm

/-- Fractional error of one truncated Mersenne weight. -/
def seamRankFloorError (s d : ℕ) : ℚ :=
  (4 : ℚ) ^ s * mersenneWeightRat d -
    (truncatedMersenneWeight s d : ℚ)

/-- Total rational floor error of a finite seam word. -/
def seamWordFloorError {s : ℕ} (b : SeamRowWord s) : ℚ :=
  ∑ d ∈ seamWordSupport b, seamRankFloorError s d

theorem seamRankFloorError_nonneg
    {s d : ℕ} (hd : 1 ≤ d) :
    0 ≤ seamRankFloorError s d := by
  let N := 4 ^ s
  let q := 2 ^ d - 1
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hdiv : ((N / q : ℕ) : ℚ) ≤ (N : ℚ) / (q : ℚ) := by
    apply (le_div_iff₀ hqQ).2
    exact_mod_cast Nat.div_mul_le_self N q
  have hNcast : (N : ℚ) = (4 : ℚ) ^ s := by simp [N]
  have hqcast : (q : ℚ) = (2 : ℚ) ^ d - 1 := by
    simpa [q] using natCast_pow_sub_one 2 d (by norm_num)
  rw [seamRankFloorError, mersenneWeightRat, truncatedMersenneWeight,
    ← hNcast, ← hqcast, mul_one_div]
  exact sub_nonneg.mpr hdiv

theorem seamRankFloorError_lt_one
    {s d : ℕ} (hd : 1 ≤ d) :
    seamRankFloorError s d < 1 := by
  let N := 4 ^ s
  let q := 2 ^ d - 1
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hltNat : N < q * (N / q + 1) := Nat.lt_mul_div_succ N hq
  have hlt : (N : ℚ) / (q : ℚ) < ((N / q : ℕ) : ℚ) + 1 := by
    apply (div_lt_iff₀ hqQ).2
    exact_mod_cast (by simpa [Nat.mul_comm] using hltNat)
  have hNcast : (N : ℚ) = (4 : ℚ) ^ s := by simp [N]
  have hqcast : (q : ℚ) = (2 : ℚ) ^ d - 1 := by
    simpa [q] using natCast_pow_sub_one 2 d (by norm_num)
  rw [seamRankFloorError, mersenneWeightRat, truncatedMersenneWeight,
    ← hNcast, ← hqcast, mul_one_div]
  linarith

/-- Euclidean division makes the floor error literally the remainder divided
by the Mersenne denominator. -/
theorem seamRankFloorError_eq_mod_div
    {s d : ℕ} (hd : 1 ≤ d) :
    seamRankFloorError s d =
      (((4 ^ s) % (2 ^ d - 1) : ℕ) : ℚ) /
        ((2 ^ d - 1 : ℕ) : ℚ) := by
  let N := 4 ^ s
  let q := 2 ^ d - 1
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hNcast : (N : ℚ) = (4 : ℚ) ^ s := by simp [N]
  have hqcast : (q : ℚ) = (2 : ℚ) ^ d - 1 := by
    simpa [q] using natCast_pow_sub_one 2 d (by norm_num)
  have hdivmod : (N : ℚ) =
      ((N / q : ℕ) : ℚ) * (q : ℚ) + ((N % q : ℕ) : ℚ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_add_mod N q).symm)
  rw [seamRankFloorError, mersenneWeightRat, truncatedMersenneWeight,
    ← hNcast, ← hqcast, mul_one_div]
  change (N : ℚ) / (q : ℚ) - ((N / q : ℕ) : ℚ) =
    ((N % q : ℕ) : ℚ) / (q : ℚ)
  field_simp
  linarith

/-- The remainder of `4^s` modulo the Mersenne denominator is the power of
two selected by the exponent remainder. -/
theorem four_pow_mod_mersenne
    {s d : ℕ} (hd : 2 ≤ d) :
    4 ^ s % (2 ^ d - 1) = 2 ^ ((2 * s) % d) := by
  let q := (2 * s) / d
  let r := (2 * s) % d
  let G := 2 ^ r * ∑ i ∈ Finset.range q, (2 ^ d) ^ i
  have hdpos : 0 < d := by omega
  have hdivmod : 2 * s = d * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod (2 * s) d).symm
  have hpowOne : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have hgeom :
      (∑ i ∈ Finset.range q, (2 ^ d) ^ i) * (2 ^ d - 1) + 1 =
        (2 ^ d) ^ q := by
    simpa only [Nat.sub_add_cancel hpowOne] using
      (geom_sum_mul_add (R := ℕ) (2 ^ d - 1) q)
  have hdecomp : 4 ^ s = G * (2 ^ d - 1) + 2 ^ r := by
    calc
      4 ^ s = 2 ^ (2 * s) := by
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
      _ = 2 ^ (d * q + r) := by rw [hdivmod]
      _ = 2 ^ r * (2 ^ d) ^ q := by
        rw [pow_add, pow_mul]
        ring
      _ = 2 ^ r *
          ((∑ i ∈ Finset.range q, (2 ^ d) ^ i) * (2 ^ d - 1) + 1) := by
        rw [hgeom]
      _ = G * (2 ^ d - 1) + 2 ^ r := by
        dsimp [G]
        ring
  have hrlt : r < d := by
    dsimp [r]
    exact Nat.mod_lt _ hdpos
  have hrle : r ≤ d - 1 := by omega
  have hpowle : 2 ^ r ≤ 2 ^ (d - 1) :=
    Nat.pow_le_pow_right (by norm_num) hrle
  have hpowSplit : 2 ^ d = 2 ^ (d - 1) * 2 := by
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (d - 1) * 2 := by rw [pow_succ]
  have hrem : 2 ^ r < 2 ^ d - 1 := by
    have hhalfTwo : 2 ≤ 2 ^ (d - 1) := by
      simpa using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ d - 1))
    omega
  rw [hdecomp, Nat.add_mod, Nat.mul_mod, Nat.mod_self]
  simp [Nat.mod_eq_of_lt hrem, r]

/-- Closed form used by the quotient-cell decomposition. -/
theorem seamRankFloorError_eq_modPow
    {s d : ℕ} (hd : 2 ≤ d) :
    seamRankFloorError s d =
      (2 ^ ((2 * s) % d) : ℚ) / ((2 ^ d - 1 : ℕ) : ℚ) := by
  rw [seamRankFloorError_eq_mod_div (by omega), four_pow_mod_mersenne hd]
  norm_cast

/-- Uniform low-rank estimate.  Rank two is sharper because `2s` is even;
from rank three onward the worst possible exponent remainder is `d - 1`. -/
theorem seamRankFloorError_le_four_sevenths
    {s d : ℕ} (hd : 2 ≤ d) :
    seamRankFloorError s d ≤ 4 / 7 := by
  rw [seamRankFloorError_eq_modPow hd]
  by_cases hd2 : d = 2
  · subst d
    norm_num [Nat.mul_mod]
  · have hd3 : 3 ≤ d := by omega
    let r := (2 * s) % d
    have hrlt : r < d := by
      dsimp [r]
      exact Nat.mod_lt _ (by omega)
    have hrle : r ≤ d - 1 := by omega
    have hpowle : 2 ^ r ≤ 2 ^ (d - 1) :=
      Nat.pow_le_pow_right (by norm_num) hrle
    have hpow4 : 4 ≤ 2 ^ (d - 1) := by
      simpa using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 2 ≤ d - 1))
    have hsplit : 2 ^ d = 2 ^ (d - 1) * 2 := by
      calc
        2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (d - 1) * 2 := by rw [pow_succ]
    have hcrossNat : 7 * 2 ^ r ≤ 4 * (2 ^ d - 1) := by
      rw [hsplit]
      omega
    have hcross : (7 : ℚ) * (2 ^ r : ℕ) ≤
        4 * (2 ^ d - 1 : ℕ) := by exact_mod_cast hcrossNat
    have hdenNat : 0 < 2 ^ d - 1 := by
      exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
    have hden : (0 : ℚ) < ((2 ^ d - 1 : ℕ) : ℚ) := by
      exact_mod_cast hdenNat
    apply (div_le_iff₀ hden).2
    change (2 ^ r : ℚ) ≤ 4 / 7 * ((2 ^ d - 1 : ℕ) : ℚ)
    push_cast at hcross
    linarith

/-- The unweighted floor-error envelope at the even truncation `2h`. -/
def evenTruncationFloorErrorEnvelope (h : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 2 h, seamRankFloorError h d

theorem evenTruncationFloorErrorEnvelope_eq_modPowSum
    (h : ℕ) :
    evenTruncationFloorErrorEnvelope h =
      ∑ d ∈ Finset.Icc 2 h,
        (2 ^ ((2 * h) % d) : ℚ) / ((2 ^ d - 1 : ℕ) : ℚ) := by
  unfold evenTruncationFloorErrorEnvelope
  apply Finset.sum_congr rfl
  intro d hd
  rw [seamRankFloorError_eq_modPow (Finset.mem_Icc.mp hd).1]

/-- Pointwise geometric majorant inside a fixed Euclidean-quotient cell. -/
theorem seamRankFloorError_le_quotientGeometric
    {h d q : ℕ} (hd : 3 ≤ d) (hq : (2 * h) / d = q) :
    seamRankFloorError h d ≤
      8 / 7 * (1 / 2 : ℚ) ^ ((q + 1) * d - 2 * h) := by
  rw [seamRankFloorError_eq_modPow (by omega)]
  let r := (2 * h) % d
  let e := (q + 1) * d - 2 * h
  have hdpos : 0 < d := by omega
  have hdivmod : 2 * h = d * q + r := by
    dsimp [r]
    rw [← hq]
    simpa [Nat.mul_comm] using (Nat.div_add_mod (2 * h) d).symm
  have hrlt : r < d := by
    dsimp [r]
    exact Nat.mod_lt _ hdpos
  have he : e = d - r := by
    dsimp [e]
    rw [show (q + 1) * d = d * q + d by ring, hdivmod]
    omega
  have hre : r + e = d := by omega
  have hpowSplit : 2 ^ d = 2 ^ r * 2 ^ e := by
    rw [← pow_add, hre]
  have hpowEight : 8 ≤ 2 ^ d := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hd)
  have hcrossNat : 7 * 2 ^ r * 2 ^ e ≤ 8 * (2 ^ d - 1) := by
    calc
      7 * 2 ^ r * 2 ^ e = 7 * (2 ^ r * 2 ^ e) := by ring
      _ = 7 * 2 ^ d := by rw [hpowSplit]
      _ ≤ 8 * (2 ^ d - 1) := by omega
  have hcross : (7 : ℚ) * (2 ^ r : ℕ) * (2 ^ e : ℕ) ≤
      8 * (2 ^ d - 1 : ℕ) := by exact_mod_cast hcrossNat
  have hdenNat : 0 < 2 ^ d - 1 := by
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  have hden : (0 : ℚ) < ((2 ^ d - 1 : ℕ) : ℚ) := by
    exact_mod_cast hdenNat
  have hpowE : (0 : ℚ) < ((2 ^ e : ℕ) : ℚ) := by positivity
  apply (div_le_iff₀ hden).2
  change (2 ^ r : ℚ) ≤
    8 / 7 * (1 / 2 : ℚ) ^ e * ((2 ^ d - 1 : ℕ) : ℚ)
  rw [div_pow]
  simp only [one_pow]
  rw [show 8 / 7 * (1 / (2 : ℚ) ^ e) * ((2 ^ d - 1 : ℕ) : ℚ) =
      (8 * ((2 ^ d - 1 : ℕ) : ℚ)) / (7 * (2 ^ e : ℕ)) by
        push_cast
        field_simp
        <;> ring]
  apply (le_div_iff₀ (mul_pos (by norm_num) hpowE)).2
  push_cast
  push_cast at hcross
  nlinarith

/-- The quotient cell is parameterized from its first possible denominator,
so the summation index itself records the geometric decay. -/
def evenTruncationFloorErrorQuotientCell (h q : ℕ) : ℚ :=
  let a := (2 * h) / (q + 1) + 1
  ∑ j ∈ Finset.range (h + 1 - a),
    if (2 * h) / (a + j) = q then seamRankFloorError h (a + j) else 0

theorem evenTruncationFloorErrorQuotientCell_eq_filterSum
    (h q : ℕ) :
    evenTruncationFloorErrorQuotientCell h q =
      ∑ d ∈ (Finset.Icc ((2 * h) / (q + 1) + 1) h).filter
        (fun d => (2 * h) / d = q), seamRankFloorError h d := by
  classical
  let a := (2 * h) / (q + 1) + 1
  unfold evenTruncationFloorErrorQuotientCell
  dsimp only
  rw [← Finset.sum_filter]
  change
    (∑ j ∈ (Finset.range (h + 1 - a)).filter
        (fun j => (2 * h) / (a + j) = q), seamRankFloorError h (a + j)) =
      ∑ d ∈ (Finset.Icc a h).filter (fun d => (2 * h) / d = q),
        seamRankFloorError h d
  refine Finset.sum_bij (fun j _hj => a + j) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hjlt := Finset.mem_range.mp hj'.1
    have hale : a ≤ h := by omega
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.le_add_right a j
      · calc
          a + j ≤ a + (h - a) := Nat.add_le_add_left (by omega) a
          _ = h := Nat.add_sub_of_le hale
    · exact hj'.2
  · intro j₁ hj₁ j₂ hj₂ heq
    exact Nat.add_left_cancel heq
  · intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hdIcc := Finset.mem_Icc.mp hd'.1
    refine ⟨d - a, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · simpa [Nat.add_sub_of_le hdIcc.1] using hd'.2
    · exact Nat.add_sub_of_le hdIcc.1
  · intro j hj
    rfl

theorem evenTruncationFloorErrorQuotientCell_le
    {h q : ℕ} (hq : 2 ≤ q)
    (ha : 3 ≤ (2 * h) / (q + 1) + 1) :
    evenTruncationFloorErrorQuotientCell h q ≤ 32 / 49 := by
  let a := (2 * h) / (q + 1) + 1
  have ha' : 3 ≤ a := by simpa [a] using ha
  have hbase : 2 * h < (q + 1) * a := by
    dsimp [a]
    exact Nat.lt_mul_div_succ (2 * h) (by omega)
  calc
    evenTruncationFloorErrorQuotientCell h q ≤
        ∑ j ∈ Finset.range (h + 1 - a),
          4 / 7 * (1 / 8 : ℚ) ^ j := by
      unfold evenTruncationFloorErrorQuotientCell
      dsimp only
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with hjq
      · have hbig : 2 * h + (3 * j + 1) ≤ (q + 1) * (a + j) := by
          nlinarith
        have hexp : 3 * j + 1 ≤ (q + 1) * (a + j) - 2 * h :=
          Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hbig)
        have hterm := seamRankFloorError_le_quotientGeometric
          (h := h) (d := a + j) (q := q) (by omega) hjq
        have hpow :
            (1 / 2 : ℚ) ^ ((q + 1) * (a + j) - 2 * h) ≤
              (1 / 2 : ℚ) ^ (3 * j + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
        calc
          seamRankFloorError h (a + j) ≤
              8 / 7 * (1 / 2 : ℚ) ^ ((q + 1) * (a + j) - 2 * h) := hterm
          _ ≤ 8 / 7 * (1 / 2 : ℚ) ^ (3 * j + 1) := by
            gcongr
          _ = 4 / 7 * (1 / 8 : ℚ) ^ j := by
            rw [pow_add, pow_mul]
            norm_num
            ring
      · positivity
    _ = 4 / 7 * ∑ j ∈ Finset.range (h + 1 - a), (1 / 8 : ℚ) ^ j := by
      rw [Finset.mul_sum]
    _ ≤ 4 / 7 * (1 - (1 / 8 : ℚ))⁻¹ := by
      apply mul_le_mul_of_nonneg_left
      · have hgeom := geom_sum_Ico_le_of_lt_one
          (K := ℚ) (m := 0) (n := h + 1 - a)
          (by norm_num : (0 : ℚ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℚ) < 1)
        simpa using hgeom
      · norm_num
    _ = 32 / 49 := by norm_num

/-- The part of one quotient cell lying above an arbitrary cutoff. -/
def evenTruncationHighQuotientCell (h D q : ℕ) : ℚ :=
  ∑ d ∈ (Finset.Ioc D h).filter (fun d => (2 * h) / d = q),
    seamRankFloorError h d

theorem evenTruncationHighQuotientCell_le
    {h D q : ℕ} (hq : 2 ≤ q)
    (ha : 3 ≤ (2 * h) / (q + 1) + 1) :
    evenTruncationHighQuotientCell h D q ≤ 32 / 49 := by
  classical
  let a := (2 * h) / (q + 1) + 1
  have hsubset :
      (Finset.Ioc D h).filter (fun d => (2 * h) / d = q) ⊆
        (Finset.Icc a h).filter (fun d => (2 * h) / d = q) := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hdIoc := Finset.mem_Ioc.mp hd'.1
    have hdpos : 0 < d := by omega
    have hmul : 2 * h < (q + 1) * d := by
      have h := Nat.lt_mul_div_succ (2 * h) hdpos
      rw [hd'.2] at h
      simpa [Nat.mul_comm] using h
    have hdivlt : (2 * h) / (q + 1) < d :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by
        simpa [Nat.mul_comm] using hmul)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by dsimp [a]; omega, hdIoc.2⟩, hd'.2⟩
  calc
    evenTruncationHighQuotientCell h D q ≤
        ∑ d ∈ (Finset.Icc a h).filter (fun d => (2 * h) / d = q),
          seamRankFloorError h d := by
      unfold evenTruncationHighQuotientCell
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d hd hdnot
      exact seamRankFloorError_nonneg (by
        have hdIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
        have ha' : 3 ≤ a := by simpa [a] using ha
        omega)
    _ = evenTruncationFloorErrorQuotientCell h q := by
      simpa [a] using
        (evenTruncationFloorErrorQuotientCell_eq_filterSum h q).symm
    _ ≤ 32 / 49 := evenTruncationFloorErrorQuotientCell_le hq ha

theorem evenTruncationHighFloorError_eq_sum_cells
    (h D : ℕ)
    (hquot : ∀ d ∈ Finset.Ioc D h,
      2 ≤ (2 * h) / d ∧ (2 * h) / d ≤ D) :
    (∑ d ∈ Finset.Ioc D h, seamRankFloorError h d) =
      ∑ q ∈ Finset.Icc 2 D, evenTruncationHighQuotientCell h D q := by
  classical
  unfold evenTruncationHighQuotientCell
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hqmem : (2 * h) / d ∈ Finset.Icc 2 D :=
    Finset.mem_Icc.mpr (hquot d hd)
  symm
  rw [Finset.sum_eq_single ((2 * h) / d)]
  · simp
  · intro q hq hne
    simp [Ne.symm hne]
  · intro hnotmem
    exact (hnotmem hqmem).elim

theorem evenTruncation_highQuotient_range
    {h d : ℕ} (hd : d ∈ Finset.Ioc (Nat.sqrt (2 * h)) h) :
    2 ≤ (2 * h) / d ∧ (2 * h) / d ≤ Nat.sqrt (2 * h) := by
  let D := Nat.sqrt (2 * h)
  have hdIoc := Finset.mem_Ioc.mp hd
  have hdpos : 0 < d := by omega
  have hqLower : 2 ≤ (2 * h) / d := by
    apply (Nat.le_div_iff_mul_le hdpos).2
    omega
  have hsqrt : 2 * h < (D + 1) * (D + 1) := by
    simpa [D] using Nat.lt_succ_sqrt (2 * h)
  have hmul : 2 * h < (D + 1) * d := by
    exact lt_of_lt_of_le hsqrt (Nat.mul_le_mul_left (D + 1) (by omega))
  have hqUpper : (2 * h) / d < D + 1 := by
    apply (Nat.div_lt_iff_lt_mul hdpos).2
    simpa [Nat.mul_comm] using hmul
  exact ⟨hqLower, by simpa [D] using (show (2 * h) / d ≤ D by omega)⟩

theorem evenTruncation_lowFloorError_le
    {h D : ℕ} (hD : 2 ≤ D) :
    (∑ d ∈ Finset.Icc 2 D, seamRankFloorError h d) ≤
      4 / 7 * (D - 1 : ℕ) := by
  calc
    (∑ d ∈ Finset.Icc 2 D, seamRankFloorError h d) ≤
        ∑ _d ∈ Finset.Icc 2 D, (4 / 7 : ℚ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact seamRankFloorError_le_four_sevenths (Finset.mem_Icc.mp hd).1
    _ = 4 / 7 * (D - 1 : ℕ) := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp [nsmul_eq_mul, mul_comm]

theorem evenTruncation_highFloorError_le
    {h : ℕ} (hh : 5 ≤ h) :
    (∑ d ∈ Finset.Ioc (Nat.sqrt (2 * h)) h,
        seamRankFloorError h d) ≤
      32 / 49 * (Nat.sqrt (2 * h) - 1 : ℕ) := by
  let D := Nat.sqrt (2 * h)
  have hD : 3 ≤ D := by
    apply (Nat.le_sqrt).2
    dsimp [D]
    nlinarith
  have hpartition := evenTruncationHighFloorError_eq_sum_cells h D
    (fun d hd => by simpa [D] using evenTruncation_highQuotient_range hd)
  rw [hpartition]
  calc
    (∑ q ∈ Finset.Icc 2 D, evenTruncationHighQuotientCell h D q) ≤
        ∑ _q ∈ Finset.Icc 2 D, (32 / 49 : ℚ) := by
      apply Finset.sum_le_sum
      intro q hqmem
      have hqBounds := Finset.mem_Icc.mp hqmem
      have hqSucc : q + 1 ≤ D + 1 := by omega
      have hmul : (D - 1) * (q + 1) ≤ (D - 1) * (D + 1) :=
        Nat.mul_le_mul_left (D - 1) hqSucc
      have hsqrt : D * D ≤ 2 * h := by
        simpa [D] using Nat.sqrt_le (2 * h)
      have hDone : 1 ≤ D := by omega
      have hidentity : (D - 1) * (D + 1) + 1 = D * D := by
        calc
          (D - 1) * (D + 1) + 1 =
              (D - 1) * D + ((D - 1) + 1) := by
                rw [Nat.mul_add]
                ring
          _ = (D - 1) * D + D := by rw [Nat.sub_add_cancel hDone]
          _ = ((D - 1) + 1) * D := by ring
          _ = D * D := by rw [Nat.sub_add_cancel hDone]
      have hmiddle : (D - 1) * (D + 1) ≤ D * D := by
        omega
      have hprod : (D - 1) * (q + 1) ≤ 2 * h :=
        hmul.trans (hmiddle.trans hsqrt)
      have hdiv : D - 1 ≤ (2 * h) / (q + 1) :=
        (Nat.le_div_iff_mul_le (by omega)).2 hprod
      apply evenTruncationHighQuotientCell_le hqBounds.1
      omega
    _ = 32 / 49 * (D - 1 : ℕ) := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp [nsmul_eq_mul, mul_comm]

/-- The complete quotient-cell estimate from the continuation packet. -/
theorem evenTruncationFloorErrorEnvelope_le_sqrtCellBound
    {h : ℕ} (hh : 5 ≤ h) :
    evenTruncationFloorErrorEnvelope h ≤
      60 / 49 * (Nat.sqrt (2 * h) - 1 : ℕ) := by
  let D := Nat.sqrt (2 * h)
  have hD : 3 ≤ D := by
    apply (Nat.le_sqrt).2
    dsimp [D]
    nlinarith
  have hDle : D ≤ h := by
    have hlt : 2 * h < (h + 1) * (h + 1) := by nlinarith
    have : Nat.sqrt (2 * h) < h + 1 := (Nat.sqrt_lt).2 hlt
    simpa [D] using (show D ≤ h by omega)
  have hsets : Finset.Icc 2 h = Finset.Icc 2 D ∪ Finset.Ioc D h := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisjoint : Disjoint (Finset.Icc 2 D) (Finset.Ioc D h) := by
    apply Finset.disjoint_left.mpr
    intro d hdLow hdHigh
    have := Finset.mem_Icc.mp hdLow
    have := Finset.mem_Ioc.mp hdHigh
    omega
  have hlow := evenTruncation_lowFloorError_le (h := h) (D := D) (by omega)
  have hhigh := evenTruncation_highFloorError_le (h := h) hh
  rw [show Nat.sqrt (2 * h) = D by rfl] at hhigh
  unfold evenTruncationFloorErrorEnvelope
  rw [hsets, Finset.sum_union hdisjoint]
  nlinarith

theorem evenTruncationFloorErrorEnvelope_lt_two_sqrt_add_four
    {h : ℕ} (hh : 5 ≤ h) :
    evenTruncationFloorErrorEnvelope h <
      2 * (Nat.sqrt (2 * h) : ℚ) + 4 := by
  have hcell := evenTruncationFloorErrorEnvelope_le_sqrtCellBound hh
  have hD : 1 ≤ Nat.sqrt (2 * h) := by
    apply (Nat.le_sqrt).2
    nlinarith
  have hcast : ((Nat.sqrt (2 * h) - 1 : ℕ) : ℚ) =
      (Nat.sqrt (2 * h) : ℚ) - 1 := by
    rw [Nat.cast_sub hD]
    simp
  rw [hcast] at hcell
  norm_num at hcell ⊢
  nlinarith

theorem seamWordFloorError_le_evenTruncationEnvelope
    {s : ℕ} (b : SeamRowWord s) :
    seamWordFloorError b ≤ evenTruncationFloorErrorEnvelope s := by
  classical
  unfold seamWordFloorError evenTruncationFloorErrorEnvelope
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    have hbounds := seamWordSupport_below hd
    exact Finset.mem_Icc.mpr ⟨hbounds.1, hbounds.2.le⟩
  · intro d hd hdnot
    exact seamRankFloorError_nonneg (by
      have := (Finset.mem_Icc.mp hd).1
      omega)

theorem wordWeightSum_eq_sum_seamWordSupport
    {s : ℕ} (b : SeamRowWord s) :
    wordWeightSum s b.toNatWord =
      ∑ d ∈ seamWordSupport b, truncatedMersenneWeight s d := by
  classical
  have hfin :
      wordWeightSum s b.toNatWord =
        ∑ i : Fin (s - 2),
          if b i then truncatedMersenneWeight s ((i : ℕ) + 2) else 0 := by
    unfold wordWeightSum
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

theorem seamWordFloorError_eq_scaledSum_sub_weightSum
    {s : ℕ} (b : SeamRowWord s) :
    seamWordFloorError b =
      (4 : ℚ) ^ s * seamWordRationalSum b -
        (wordWeightSum s b.toNatWord : ℚ) := by
  classical
  unfold seamWordFloorError seamRankFloorError
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsum :
      (∑ d ∈ seamWordSupport b, mersenneWeightRat d) =
        seamWordRationalSum b := by
    simp [seamWordRationalSum, finiteErdosSum, mersenneWeightRat]
  have hweight :
      (∑ d ∈ seamWordSupport b,
          (truncatedMersenneWeight s d : ℚ)) =
        (wordWeightSum s b.toNatWord : ℚ) := by
    rw [wordWeightSum_eq_sum_seamWordSupport]
    push_cast
    rfl
  rw [hsum, hweight]

theorem seamWordFloorError_nonneg
    {s : ℕ} (b : SeamRowWord s) :
    0 ≤ seamWordFloorError b := by
  unfold seamWordFloorError
  apply Finset.sum_nonneg
  intro d hd
  exact seamRankFloorError_nonneg (by
    have := (seamWordSupport_below hd).1
    omega)

theorem seamWordFloorError_lt_card
    {s : ℕ} {b : SeamRowWord s}
    (hne : (seamWordSupport b).Nonempty) :
    seamWordFloorError b < ((seamWordSupport b).card : ℚ) := by
  calc
    seamWordFloorError b =
        ∑ d ∈ seamWordSupport b, seamRankFloorError s d := rfl
    _ < ∑ _d ∈ seamWordSupport b, (1 : ℚ) :=
      Finset.sum_lt_sum_of_nonempty hne fun d hd =>
        seamRankFloorError_lt_one (by
          have := (seamWordSupport_below hd).1
          omega)
    _ = ((seamWordSupport b).card : ℚ) := by simp

theorem seamWordFloorError_lt_width
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordFloorError b < (s - 2 : ℕ) := by
  by_cases hne : (seamWordSupport b).Nonempty
  · have hlt := seamWordFloorError_lt_card hne
    have hcard := seamWordSupport_card_le_width b
    exact hlt.trans_le (by exact_mod_cast hcard)
  · have hempty : seamWordSupport b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [seamWordFloorError, hempty]
    omega

/-! ## Exact corrected coordinate and take comparison -/

/-- Signed defect corrected by the rational floor error. -/
def seamWordFloorZ {s : ℕ} (b : SeamRowWord s) : ℚ :=
  ((wordDefect s b.toNatWord : ℤ) : ℚ) - seamWordFloorError b

def seamTakeThreshold (s : ℕ) : ℚ :=
  (2 : ℚ) ^ s / ((2 : ℚ) ^ s - 1)

theorem four_pow_eq_two_pow_sq (s : ℕ) :
    (4 : ℚ) ^ s = ((2 : ℚ) ^ s) ^ 2 := by
  rw [show (4 : ℚ) = 2 * 2 by norm_num, mul_pow]
  ring

theorem seamSubsetTarget_cast_rat
    (s : ℕ) (hs : 1 ≤ s) :
    (seamSubsetTarget s : ℚ) =
      (4 : ℚ) ^ s / 2 - (2 : ℚ) ^ s := by
  have hpow : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold seamSubsetTarget
  rw [Nat.cast_sub hpow]
  push_cast
  rw [four_pow_eq_two_pow_sq]
  have hsquare : ((2 : ℚ) ^ s) ^ 2 = (2 : ℚ) ^ (2 * s) := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  have hstep : (2 : ℚ) ^ (2 * s) =
      2 * (2 : ℚ) ^ (2 * s - 1) := by
    calc
      (2 : ℚ) ^ (2 * s) = (2 : ℚ) ^ ((2 * s - 1) + 1) := by
        congr 1
        omega
      _ = 2 * (2 : ℚ) ^ (2 * s - 1) := by
        rw [pow_succ]
        ring
  rw [hsquare, hstep]
  ring

theorem seamWordFloorZ_eq_target_sub_scaledSum
    {s : ℕ} (b : SeamRowWord s) :
    seamWordFloorZ b =
      (seamSubsetTarget s : ℚ) -
        (4 : ℚ) ^ s * seamWordRationalSum b := by
  rw [seamWordFloorZ,
    seamWordFloorError_eq_scaledSum_sub_weightSum]
  unfold wordDefect
  push_cast
  ring

theorem seamWordRationalRemainder_eq_pow_add_floorZ_div
    {s : ℕ} (hs : 1 ≤ s) (b : SeamRowWord s) :
    seamWordRationalRemainder b =
      ((2 : ℚ) ^ s + seamWordFloorZ b) / (4 : ℚ) ^ s := by
  rw [seamWordRationalRemainder,
    seamWordFloorZ_eq_target_sub_scaledSum,
    seamSubsetTarget_cast_rat s hs]
  have hpow : (4 : ℚ) ^ s ≠ 0 := by positivity
  field_simp
  ring

/-- Exact residual decomposition behind any terminal-only completion.  The
floor-error term is additive, but it does not replace the scaled rational
remainder. -/
theorem wordDefect_eq_scaledRemainder_sub_pow_add_floorError
    {s : ℕ} (hs : 1 ≤ s) (b : SeamRowWord s) :
    ((wordDefect s b.toNatWord : ℤ) : ℚ) =
      (4 : ℚ) ^ s * seamWordRationalRemainder b -
        (2 : ℚ) ^ s + seamWordFloorError b := by
  rw [seamWordRationalRemainder_eq_pow_add_floorZ_div hs]
  have hpow : (4 : ℚ) ^ s ≠ 0 := by positivity
  field_simp
  rw [seamWordFloorZ]
  ring

theorem halfActualWordDefect_eq_scaledGreedyRemainder_sub_pow_add_floorError
    (s : ℕ) (hs : 2 ≤ s) :
    ((wordDefect s (halfActualSeamWord s).toNatWord : ℤ) : ℚ) =
      (4 : ℚ) ^ s * greedyMersenneRemainderRat (1 / 2 : ℚ) (s - 1) -
        (2 : ℚ) ^ s + seamWordFloorError (halfActualSeamWord s) := by
  rw [wordDefect_eq_scaledRemainder_sub_pow_add_floorError (by omega),
    seamWordRationalRemainder_halfActualSeamWord s hs]

theorem seamWord_take_iff_floorZ
    {s : ℕ} (hs : 1 ≤ s) (b : SeamRowWord s) :
    mersenneWeightRat s ≤ seamWordRationalRemainder b ↔
      seamTakeThreshold s ≤ seamWordFloorZ b := by
  rw [seamWordRationalRemainder_eq_pow_add_floorZ_div hs]
  let a : ℚ := (2 : ℚ) ^ s
  have ha : 1 < a := by
    dsimp [a]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hden : 0 < a - 1 := sub_pos.mpr ha
  have hsquare : (4 : ℚ) ^ s = a ^ 2 := by
    simpa [a] using four_pow_eq_two_pow_sq s
  have hsquarePos : 0 < a ^ 2 := sq_pos_of_pos (by linarith)
  have hbridge : a ^ 2 / (a - 1) - a = a / (a - 1) := by
    field_simp
    ring
  rw [mersenneWeightRat, seamTakeThreshold, show (2 : ℚ) ^ s = a by rfl,
    hsquare]
  constructor
  · intro h
    have hscaled : a ^ 2 / (a - 1) ≤ a + seamWordFloorZ b := by
      have h' := (le_div_iff₀ hsquarePos).mp h
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
    linarith
  · intro h
    apply (le_div_iff₀ hsquarePos).mpr
    have hscaled : a ^ 2 / (a - 1) ≤ a + seamWordFloorZ b := by
      linarith
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

theorem seamTakeThreshold_lt_two
    (s : ℕ) (hs : 2 ≤ s) :
    seamTakeThreshold s < 2 := by
  let a : ℚ := (2 : ℚ) ^ s
  have hpow : 2 ^ 2 ≤ 2 ^ s :=
    Nat.pow_le_pow_right (by norm_num) hs
  have ha4 : (4 : ℚ) ≤ a := by
    dsimp [a]
    exact_mod_cast hpow
  have ha : 2 < a := by
    linarith
  have hden : 0 < a - 1 := by linarith
  unfold seamTakeThreshold
  change a / (a - 1) < 2
  exact (div_lt_iff₀ hden).2 (by linarith)

/-! ## Exact word updates -/

theorem seamWordRationalSum_extend_false
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordRationalSum (b.extend false) = seamWordRationalSum b := by
  simp [seamWordRationalSum, seamWordSupport_extend_false hs b]

theorem seamWordRationalSum_extend_true
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordRationalSum (b.extend true) =
      seamWordRationalSum b + mersenneWeightRat s := by
  have hnot : s ∉ seamWordSupport b := by
    intro h
    exact (Nat.lt_irrefl s) (seamWordSupport_below h).2
  rw [seamWordRationalSum, seamWordSupport_extend_true hs b]
  unfold seamWordRationalSum finiteErdosSum
  rw [Finset.sum_insert hnot]
  simp [mersenneWeightRat, add_comm]

theorem seamWordFloorError_extend_false
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordFloorError (b.extend false) =
      4 * seamWordFloorError b -
        (wordPulse s b.toNatWord : ℚ) := by
  rw [seamWordFloorError_eq_scaledSum_sub_weightSum,
    seamWordRationalSum_extend_false hs b,
    SeamRowWord.toNatWord_extend hs,
    wordWeightSum_succ hs b.toNatWord false,
    seamWordFloorError_eq_scaledSum_sub_weightSum]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  push_cast
  rw [pow_succ]
  ring

theorem seamRankFloorError_newRank
    {s : ℕ} (hs : 3 ≤ s) :
    seamRankFloorError (s + 1) s =
      4 / ((2 : ℚ) ^ s - 1) := by
  rw [seamRankFloorError, truncatedMersenneWeight_newRank hs]
  unfold mersenneWeightRat
  push_cast
  rw [pow_succ, four_pow_eq_two_pow_sq]
  have hden : (2 : ℚ) ^ s - 1 ≠ 0 := by
    have : (1 : ℚ) < (2 : ℚ) ^ s :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  field_simp
  ring

theorem seamWordFloorError_extend_true
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordFloorError (b.extend true) =
      4 * seamWordFloorError b -
        (wordPulse s b.toNatWord : ℚ) +
        4 / ((2 : ℚ) ^ s - 1) := by
  rw [seamWordFloorError_eq_scaledSum_sub_weightSum,
    seamWordRationalSum_extend_true hs b,
    SeamRowWord.toNatWord_extend hs,
    wordWeightSum_succ hs b.toNatWord true,
    seamWordFloorError_eq_scaledSum_sub_weightSum]
  simp only [if_true]
  push_cast
  rw [pow_succ, four_pow_eq_two_pow_sq]
  unfold mersenneWeightRat
  have hden : (2 : ℚ) ^ s - 1 ≠ 0 := by
    have : (1 : ℚ) < (2 : ℚ) ^ s :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  field_simp
  ring

theorem seamWordFloorZ_extend_false
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordFloorZ (b.extend false) =
      4 * seamWordFloorZ b + (2 : ℚ) ^ (s + 1) := by
  rw [seamWordFloorZ, SeamRowWord.toNatWord_extend hs,
    wordDefect_succ hs b.toNatWord false,
    seamWordFloorError_extend_false hs b, seamWordFloorZ]
  simp only [Bool.false_eq_true, ↓reduceIte]
  push_cast
  ring

theorem seamWordFloorZ_extend_true
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordFloorZ (b.extend true) =
      4 * seamWordFloorZ b - (2 : ℚ) ^ (s + 1) - 4 -
        4 / ((2 : ℚ) ^ s - 1) := by
  rw [seamWordFloorZ, SeamRowWord.toNatWord_extend hs,
    wordDefect_succ hs b.toNatWord true,
    seamWordFloorError_extend_true hs b, seamWordFloorZ]
  simp only [if_true]
  push_cast
  ring

/-! ## Concrete seam `U`/`M`/`R` updates -/

def seamGreedyFloorError (s : ℕ) : ℚ :=
  seamWordFloorError (seamGreedyWord s)

def seamAboveFloorError (s : ℕ) (hs : 5 ≤ s) : ℚ :=
  seamWordFloorError (seamAboveWord s hs)

def seamGreedyFloorZ (s : ℕ) : ℚ :=
  seamWordFloorZ (seamGreedyWord s)

theorem seamGreedyFloorZ_eq_remainder_sub_error
    (s : ℕ) (hs : 5 ≤ s) :
    seamGreedyFloorZ s =
      (seamIntegerGreedyRemainder s : ℚ) - seamGreedyFloorError s := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hsum := K.old_below_add_remainder
  have hdef :
      ((wordDefect s (seamGreedyWord s).toNatWord : ℤ) : ℚ) =
        (seamIntegerGreedyRemainder s : ℚ) := by
    change (((seamSubsetTarget s : ℤ) -
      (F.oldSum K.below : ℤ) : ℤ) : ℚ) = _
    push_cast
    have hsum' : F.oldSum K.below + seamIntegerGreedyRemainder s =
        seamSubsetTarget s := by
      simpa [K, seamAdjacentCut_remainder hs] using hsum
    have hsumQ : (F.oldSum K.below : ℚ) +
        (seamIntegerGreedyRemainder s : ℚ) =
          (seamSubsetTarget s : ℚ) := by
      exact_mod_cast hsum'
    linarith
  rw [seamGreedyFloorZ, seamWordFloorZ, hdef]
  rfl

/-- The elementary finite-probe lower bound: a seam remainder at least two
larger than the selected support cardinality already clears the exact
rational take threshold. -/
theorem seamTakeThreshold_le_greedyFloorZ_of_card_add_two_le
    (s : ℕ) (hs : 5 ≤ s)
    (hlarge :
      (seamWordSupport (seamGreedyWord s)).card + 2 ≤
        seamIntegerGreedyRemainder s) :
    seamTakeThreshold s ≤ seamGreedyFloorZ s := by
  rw [seamGreedyFloorZ_eq_remainder_sub_error s hs]
  have hthreshold := seamTakeThreshold_lt_two s (by omega)
  have hlargeQ :
      ((seamWordSupport (seamGreedyWord s)).card : ℚ) + 2 ≤
        (seamIntegerGreedyRemainder s : ℚ) := by
    exact_mod_cast hlarge
  have htwoNat : 2 ≤ seamIntegerGreedyRemainder s := by omega
  have htwoQ : (2 : ℚ) ≤ (seamIntegerGreedyRemainder s : ℚ) := by
    exact_mod_cast htwoNat
  by_cases hne :
      (seamWordSupport (seamGreedyWord s)).Nonempty
  · have hPhi := seamWordFloorError_lt_card hne
    change seamGreedyFloorError s <
      ((seamWordSupport (seamGreedyWord s)).card : ℚ) at hPhi
    linarith
  · have hempty : seamWordSupport (seamGreedyWord s) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty] at hlargeQ
    have hPhi : seamGreedyFloorError s = 0 := by
      simp [seamGreedyFloorError, seamWordFloorError, hempty]
    rw [hPhi]
    linarith

theorem mersenneWeightRat_le_seamGreedyRemainder_of_card_add_two_le
    (s : ℕ) (hs : 5 ≤ s)
    (hlarge :
      (seamWordSupport (seamGreedyWord s)).card + 2 ≤
        seamIntegerGreedyRemainder s) :
    mersenneWeightRat s ≤
      seamWordRationalRemainder (seamGreedyWord s) :=
  (seamWord_take_iff_floorZ (by omega : 1 ≤ s) (seamGreedyWord s)).2
    (seamTakeThreshold_le_greedyFloorZ_of_card_add_two_le s hs hlarge)

theorem seamAboveFloorZ_eq_neg_overshoot_sub_error
    (s : ℕ) (hs : 5 ≤ s) :
    seamWordFloorZ (seamAboveWord s hs) =
      -((seamAdjacentCut s hs).overshoot : ℚ) -
        seamAboveFloorError s hs := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hsum := K.capacity_add_overshoot
  have hdef :
      ((wordDefect s (seamAboveWord s hs).toNatWord : ℤ) : ℚ) =
        -((K.overshoot : ℕ) : ℚ) := by
    change (((seamSubsetTarget s : ℤ) -
      (F.oldSum K.above : ℤ) : ℤ) : ℚ) = _
    push_cast
    have hsum' : seamSubsetTarget s + K.overshoot = F.oldSum K.above := by
      simpa [K] using hsum
    have hsumQ : (seamSubsetTarget s : ℚ) + (K.overshoot : ℚ) =
        (F.oldSum K.above : ℚ) := by
      exact_mod_cast hsum'
    linarith
  rw [seamWordFloorZ, hdef]
  rfl

theorem seamGreedyFloorZ_succ_upper
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    seamGreedyFloorZ (s + 1) =
      (2 : ℚ) ^ (s + 1) -
        4 * ((seamAdjacentCut s hs).overshoot +
          seamAboveFloorError s hs) := by
  rw [seamGreedyFloorZ, seamGreedyWord_succ_eq_upperBranch s hs hcarry,
    seamWordFloorZ_extend_false (by omega)]
  have habove :
      seamWordFloorZ (seamAdjacentCut s hs).above =
        -((seamAdjacentCut s hs).overshoot : ℚ) -
          seamAboveFloorError s hs := by
    change seamWordFloorZ (seamAboveWord s hs) =
      -((seamAdjacentCut s hs).overshoot : ℚ) -
        seamAboveFloorError s hs
    exact seamAboveFloorZ_eq_neg_overshoot_sub_error s hs
  rw [habove]
  push_cast
  ring

theorem seamGreedyFloorZ_succ_middle
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
          (seamPerturbedFamily s (by omega)).gap -
          (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight) :
    seamGreedyFloorZ (s + 1) =
      4 * seamGreedyFloorZ s + (2 : ℚ) ^ (s + 1) := by
  rw [seamGreedyFloorZ, seamGreedyWord_succ_eq_middleBranch
      s hs hcarry hmiddle,
    seamWordFloorZ_extend_false (by omega)]
  rfl

theorem seamGreedyFloorZ_succ_right
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hright : (seamAdjacentCut s hs).terminalWeight ≤
      4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse) :
    seamGreedyFloorZ (s + 1) =
      4 * seamGreedyFloorZ s - (2 : ℚ) ^ (s + 1) - 4 -
        4 / ((2 : ℚ) ^ s - 1) := by
  rw [seamGreedyFloorZ, seamGreedyWord_succ_eq_rightBranch
      s hs hcarry hright,
    seamWordFloorZ_extend_true (by omega)]
  rfl

/-! ## Honest reset sockets -/

/-- The unresolved upper-reset inequality, stated in the exact output
coordinate supplied by `seamGreedyFloorZ_succ_upper`. -/
def SeamResetUAt (s : ℕ) (hs : 5 ≤ s) : Prop :=
  (seamAdjacentCut s hs).successorCarries →
    0 < seamIntegerGreedyRemainder (s + 1) →
      seamTakeThreshold (s + 1) ≤
        (2 : ℚ) ^ (s + 1) -
          4 * ((seamAdjacentCut s hs).overshoot +
            seamAboveFloorError s hs)

/-- The unresolved terminal/right-reset inequality, again stated in the
exact output coordinate. -/
def SeamResetRAt (s : ℕ) (hs : 5 ≤ s) : Prop :=
  ¬ (seamAdjacentCut s hs).successorCarries →
    (seamAdjacentCut s hs).terminalWeight ≤
      4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse →
    0 < seamIntegerGreedyRemainder (s + 1) →
      seamTakeThreshold (s + 1) ≤
        4 * seamGreedyFloorZ s - (2 : ℚ) ^ (s + 1) - 4 -
          4 / ((2 : ℚ) ^ s - 1)

theorem seamResetUAt_iff_output_floorZ
    (s : ℕ) (hs : 5 ≤ s) :
    SeamResetUAt s hs ↔
      (seamAdjacentCut s hs).successorCarries →
        0 < seamIntegerGreedyRemainder (s + 1) →
          seamTakeThreshold (s + 1) ≤ seamGreedyFloorZ (s + 1) := by
  constructor
  · intro h hcarry hpos
    rw [seamGreedyFloorZ_succ_upper s hs hcarry]
    exact h hcarry hpos
  · intro h hcarry hpos
    rw [← seamGreedyFloorZ_succ_upper s hs hcarry]
    exact h hcarry hpos

theorem seamResetRAt_iff_output_floorZ
    (s : ℕ) (hs : 5 ≤ s) :
    SeamResetRAt s hs ↔
      ¬ (seamAdjacentCut s hs).successorCarries →
        (seamAdjacentCut s hs).terminalWeight ≤
          4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse →
        0 < seamIntegerGreedyRemainder (s + 1) →
          seamTakeThreshold (s + 1) ≤ seamGreedyFloorZ (s + 1) := by
  constructor
  · intro h hcarry hright hpos
    rw [seamGreedyFloorZ_succ_right s hs hcarry hright]
    exact h hcarry hright hpos
  · intro h hcarry hright hpos
    rw [← seamGreedyFloorZ_succ_right s hs hcarry hright]
    exact h hcarry hright hpos

/-! ## First proved composition: a bad aligned skip cannot skip again -/

theorem four_mul_sub_three_add_two_lt_two_pow_succ
    (s : ℕ) (hs : 5 ≤ s) :
    4 * (s - 3) + 2 < 2 ^ (s + 1) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      rw [pow_succ]
      have hp : 4 ≤ 2 ^ (s + 1) := by
        simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2)
          (by omega : 2 ≤ s + 1))
      omega

/-- A hypothetical skipped, aligned, positive-remainder cell forces the
next actual rational/real greedy decision to be a take.  This uses only the
exact `Z` comparison and the proved `Phi < width` floor-error bound. -/
theorem alignedPositiveSkip_forces_next_take
    (s : ℕ) (hs : 5 ≤ s)
    (hskip : ¬ mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1))
    (halign : halfActualSeamWord s = seamGreedyWord s)
    (hpos : 1 ≤ seamIntegerGreedyRemainder s) :
    mersenneWeight (s + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) s := by
  have hdec : decide (mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1)) = false := by
    simp only [decide_eq_false_iff_not]
    exact hskip
  have hactual :
      halfActualSeamWord (s + 1) =
        (seamGreedyWord s).extend false := by
    rw [halfActualSeamWord_succ s (by omega), halign, hdec]
  have hPhi := seamWordFloorError_lt_width (by omega : 3 ≤ s)
    (seamGreedyWord s)
  have hZ := seamGreedyFloorZ_eq_remainder_sub_error s hs
  have hupdate := seamWordFloorZ_extend_false (by omega : 3 ≤ s)
    (seamGreedyWord s)
  have hpow := four_mul_sub_three_add_two_lt_two_pow_succ s hs
  have hpowQ :
      (4 * (s - 3) + 2 : ℕ) < ((2 : ℚ) ^ (s + 1)) := by
    exact_mod_cast hpow
  have hpowQ' :
      4 * ((s : ℚ) - 3) + 2 < ((2 : ℚ) ^ (s + 1)) := by
    calc
      4 * ((s : ℚ) - 3) + 2 =
          ((4 * (s - 3) + 2 : ℕ) : ℚ) := by
        rw [Nat.cast_add, Nat.cast_mul,
          Nat.cast_sub (by omega : 3 ≤ s)]
        norm_num
      _ < ((2 : ℚ) ^ (s + 1)) := hpowQ
  have hposQ : (1 : ℚ) ≤ (seamIntegerGreedyRemainder s : ℚ) := by
    exact_mod_cast hpos
  have hthreshold := seamTakeThreshold_lt_two (s + 1) (by omega)
  have hZnext :
      seamTakeThreshold (s + 1) <
        seamWordFloorZ ((seamGreedyWord s).extend false) := by
    rw [hupdate]
    change seamTakeThreshold (s + 1) <
      4 * seamGreedyFloorZ s + (2 : ℚ) ^ (s + 1)
    rw [hZ]
    change seamGreedyFloorError s < ((s - 2 : ℕ) : ℚ) at hPhi
    rw [Nat.cast_sub (by omega : 2 ≤ s)] at hPhi
    push_cast at hPhi
    nlinarith
  have htakeRat :
      mersenneWeightRat (s + 1) ≤
        seamWordRationalRemainder ((seamGreedyWord s).extend false) :=
    (seamWord_take_iff_floorZ (by omega : 1 ≤ s + 1)
      ((seamGreedyWord s).extend false)).2 hZnext.le
  have hrem :
      seamWordRationalRemainder ((seamGreedyWord s).extend false) =
        greedyMersenneRemainderRat (1 / 2 : ℚ) s := by
    rw [← hactual]
    exact seamWordRationalRemainder_halfActualSeamWord (s + 1) (by omega)
  rw [hrem] at htakeRat
  simpa using
    (rational_greedy_take_iff_real (1 / 2 : ℚ) s).1 htakeRat

#print axioms seamWord_take_iff_floorZ
#print axioms seamWordFloorZ_extend_false
#print axioms seamWordFloorZ_extend_true
#print axioms seamGreedyFloorZ_succ_upper
#print axioms seamGreedyFloorZ_succ_middle
#print axioms seamGreedyFloorZ_succ_right
#print axioms seamTakeThreshold_le_greedyFloorZ_of_card_add_two_le
#print axioms mersenneWeightRat_le_seamGreedyRemainder_of_card_add_two_le
#print axioms seamResetUAt_iff_output_floorZ
#print axioms seamResetRAt_iff_output_floorZ
#print axioms alignedPositiveSkip_forces_next_take

end

end Erdos249257
