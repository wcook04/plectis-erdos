/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2

/-!
# Angle D3: finite checks on seven measured survivor classes

`ErdosProblems/Lift/AngleB2.lean` does **not** close the all-right-tail branch
of Erdős #257.  Its theorem `allRight_landingExcess_two_impossible` is a
**PROVED, CONDITIONAL** implication requiring, among other hypotheses,

* `Recon257.seamExcess (D + 1) = 2`, and
* `hcof`: selection of `AngleB2.cofRanks s` at the three rows
  `s = D+1, D+2, D+3`.

**MEASURED, NOT PROVED HERE:** `seamExcess s = 2` has no instance on the
audited range `s ∈ [5,102]`, so the connection theorem is unreachable there.
In the separate scan `D ∈ [60,700)`, every `D` satisfying `hcof` already dies
by depth at most `3` under the concrete `belowPulse`; on that range `hcof`
therefore supplies no exclusion beyond the direct computation.  The same scan
identified seven classes

  `D = 101, 122, 164, 314, 545, 629, 1112`

whose concrete below-pulse orbit remains positive through depth `25`.

**PROVED IN THIS FILE:** `hcof` fails on those seven explicit classes; all
twenty-one rows `D+1, D+2, D+3` have `LargestSkipLateAt`; the stated
cofactor arithmetic, late-only ratchet computations, and cofinal endpoint
implications hold.  These facts do not make the conditional Angle B2 theorem
applicable and do not resolve Erdős #257.
-/

namespace Erdos249257

namespace SkipD3

open HalfCylinderIntegerGreedy

/-! ## 1. The late zone and the largest false rank -/

/-- **Any late false rank forces a late largest false rank.**  If some rank `m`
in the late zone `2 * s < 3 * m` is skipped by the greedy, the *largest* false
rank of the row is at least `m`, hence also late.  So `LargestSkipLateAt s`
follows from a single skipped late rank; the skipped rank itself need not be
the largest one. -/
theorem largestSkipLateAt_of_late_skip
    {s m : ℕ} (hm2 : 2 ≤ m) (hms : m < s) (hlate : 2 * s < 3 * m)
    (hnot : m ∉ seamWordSupport (seamGreedyWord s)) :
    LargestSkipLateAt s := by
  classical
  set F : Finset ℕ :=
    (Finset.Ico 2 s).filter (fun e => e ∉ seamWordSupport (seamGreedyWord s)) with hF
  have hmF : m ∈ F := by
    rw [hF]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hm2, hms⟩, hnot⟩
  have hne : F.Nonempty := ⟨m, hmF⟩
  set d := F.max' hne with hd
  have hdF : d ∈ F := F.max'_mem hne
  have hdmem := Finset.mem_filter.mp (hF ▸ hdF)
  have hdIco := Finset.mem_Ico.mp hdmem.1
  have hmd : m ≤ d := F.le_max' m hmF
  refine ⟨d, ⟨hdIco.1, hdIco.2, hdmem.2, ?_⟩, by omega⟩
  intro e hde hes
  by_contra hmem
  have heF : e ∈ F := by
    rw [hF]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hes⟩, hmem⟩
  have := F.le_max' e heF
  omega

/-- **The tautological late-zone dichotomy.**  Either every rank in the late
zone `(2s/3, s)` is selected, or the row has a late largest false rank. -/
theorem lateZone_dichotomy (s : ℕ) (hs : 4 ≤ s) :
    (∀ e : ℕ, 2 * s < 3 * e → e < s → e ∈ seamWordSupport (seamGreedyWord s))
      ∨ LargestSkipLateAt s := by
  classical
  by_cases h : ∀ e : ℕ, 2 * s < 3 * e → e < s → e ∈ seamWordSupport (seamGreedyWord s)
  · exact Or.inl h
  · right
    simp only [not_forall] at h
    obtain ⟨e, hlate, hes, hmem⟩ := h
    exact largestSkipLateAt_of_late_skip (by omega) hes hlate hmem

/-! ## 2. Which cofactor ranks are late

`AngleB2.cofRanks s` carries up to two ranks.  The two *three*-cofactors
`(2s+1)/3` and `2(s+1)/3` are late; the *two*-cofactor `(s+1)/2` is not, and no
additional divisor of `2s+1` or `2s+2` with cofactor `5, 7, …` can lie in the
late zone.  These are **PROVED** arithmetic facts below. -/

theorem threeCofOdd_late {s : ℕ} (_hs : 1 ≤ s) (hdvd : 3 ∣ 2 * s + 1) :
    2 * s < 3 * ((2 * s + 1) / 3) := by
  obtain ⟨c, hc⟩ := hdvd
  omega

theorem threeCofEven_late {s : ℕ} (_hs : 1 ≤ s) (hdvd : 3 ∣ s + 1) :
    2 * s < 3 * (2 * (s + 1) / 3) := by
  obtain ⟨c, hc⟩ := hdvd
  have : 2 * (s + 1) / 3 = 2 * c := by omega
  omega

/-- **The two-cofactor is never late.**  `(s+1)/2` sits at half the row, well
inside `2s/3`, so a skip of `(s+1)/2` supplies no information about the largest
false rank. -/
theorem halfCof_not_late {s : ℕ} (hs : 3 ≤ s) : ¬ (2 * s < 3 * ((s + 1) / 2)) := by
  omega

/-- Skipping the odd three-cofactor gives the late largest skip. -/
theorem largestSkipLateAt_of_threeCofOdd_skip
    {s : ℕ} (hs : 5 ≤ s) (hdvd : 3 ∣ 2 * s + 1)
    (hnot : (2 * s + 1) / 3 ∉ seamWordSupport (seamGreedyWord s)) :
    LargestSkipLateAt s := by
  obtain ⟨c, hc⟩ := hdvd
  refine largestSkipLateAt_of_late_skip (m := (2 * s + 1) / 3) (by omega) (by omega)
    (threeCofOdd_late (by omega) ⟨c, hc⟩) hnot

/-- Skipping the even three-cofactor gives the late largest skip. -/
theorem largestSkipLateAt_of_threeCofEven_skip
    {s : ℕ} (hs : 5 ≤ s) (hdvd : 3 ∣ s + 1)
    (hnot : 2 * (s + 1) / 3 ∉ seamWordSupport (seamGreedyWord s)) :
    LargestSkipLateAt s := by
  obtain ⟨c, hc⟩ := hdvd
  have hval : 2 * (s + 1) / 3 = 2 * c := by omega
  refine largestSkipLateAt_of_late_skip (m := 2 * (s + 1) / 3) (by omega) (by omega)
    (threeCofEven_late (by omega) ⟨c, hc⟩) hnot

/-- **Three is the only cofactor that reaches the late zone.**  A rank `m < s`
with `2 * s < 3 * m` that divides `2s+1` or `2s+2` must be `(2s+1)/3` or
`2(s+1)/3`.  So enlarging `AngleB2.cofRanks` with cofactors `5, 7, …` cannot
produce further late ranks from these two divisibility sources. -/
theorem late_divisor_cofactor_three
    {s m : ℕ} (hs : 4 ≤ s) (hms : m < s) (hlate : 2 * s < 3 * m)
    (hdvd : m ∣ 2 * s + 1 ∨ m ∣ 2 * s + 2) :
    3 * m = 2 * s + 1 ∨ 3 * m = 2 * s + 2 := by
  have hm3 : 3 ≤ m := by omega
  rcases hdvd with ⟨c, hc⟩ | ⟨c, hc⟩
  · left
    have hc3 : c = 3 := by nlinarith
    subst hc3
    omega
  · right
    have hc3 : c = 3 := by nlinarith
    subst hc3
    omega

/-! ## 3. Executable access to the concrete greedy row

`seamWeightsFrom` is defined by well-founded recursion, so it does not reduce
in the kernel.  `wgt` is the same list produced by structural recursion on a
fuel argument, and `wgt_eq` identifies the two.  Everything below is therefore
`decide +kernel`-computable. -/

/-- Fuel-driven structural recomputation of `seamWeightsFrom`. -/
def wgt (s : ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | d, (n + 1) => if d < s then truncatedMersenneWeight s d :: wgt s (d + 1) n else []

theorem wgt_eq (s : ℕ) : ∀ (n d : ℕ), s - d ≤ n → seamWeightsFrom s d = wgt s d n := by
  intro n
  induction n with
  | zero =>
      intro d hd
      rw [seamWeightsFrom_eq_nil (by omega), wgt]
  | succ n ih =>
      intro d hd
      by_cases h : d < s
      · rw [seamWeightsFrom_eq_cons h, wgt, if_pos h, ih (d + 1) (by omega)]
      · rw [seamWeightsFrom_eq_nil (by omega), wgt, if_neg h]

theorem seamWeights_eq_wgt (s : ℕ) : seamWeights s = wgt s 2 (s - 2) := by
  unfold seamWeights
  exact wgt_eq s (s - 2) 2 le_rfl

/-- The concrete greedy bit word of row `s`, kernel-computable. -/
def gb (s : ℕ) : List Bool := integerGreedyBits (wgt s 2 (s - 2)) (seamSubsetTarget s)

theorem gb_eq (s : ℕ) : gb s = integerGreedyBits (seamWeights s) (seamSubsetTarget s) := by
  rw [gb, seamWeights_eq_wgt]

theorem gb_length (s : ℕ) : (gb s).length = s - 2 := by
  rw [gb_eq, integerGreedyBits_length, seamWeights_length_eq]

theorem seamGreedyWord_apply {s : ℕ} (i : Fin (s - 2)) :
    seamGreedyWord s i = (gb s).getD (i : ℕ) false := by
  have hlt : (i : ℕ) < (gb s).length := by rw [gb_length]; exact i.isLt
  rw [← List.getElem_eq_getD (h := hlt) false]
  simp [seamGreedyWord, SeamRowWord.ofList, gb_eq]

/-- Membership in the seam support is exactly a bit lookup in `gb`. -/
theorem mem_support_iff {s d : ℕ} (h2 : 2 ≤ d) (hds : d < s) :
    d ∈ seamWordSupport (seamGreedyWord s) ↔ (gb s).getD (d - 2) false = true := by
  rw [mem_seamWordSupport_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [seamGreedyWord_apply] at hi
    simpa using hi
  · intro h
    refine ⟨⟨d - 2, by omega⟩, ?_, by show d = d - 2 + 2; omega⟩
    rw [seamGreedyWord_apply]
    simpa using h

theorem notMem_support_of_gb_false {s d : ℕ} (h2 : 2 ≤ d) (hds : d < s)
    (h : (gb s).getD (d - 2) false = false) :
    d ∉ seamWordSupport (seamGreedyWord s) := by
  intro hmem
  rw [mem_support_iff h2 hds, h] at hmem
  exact Bool.false_ne_true hmem

/-- Decidable certificate that rank `d` is the largest false rank of row `s`:
bit `d` is off and every bit above it, up to the terminal rank `s-1`, is on. -/
def rowChk (s d : ℕ) : Bool :=
  ((gb s).getD (d - 2) false == false) &&
    ((List.range (s - d - 1)).all (fun k => (gb s).getD (d - 1 + k) false))

theorem isLargestFalseRank_of_rowChk {s d : ℕ} (h2 : 2 ≤ d) (hds : d < s)
    (h : rowChk s d = true) :
    IsLargestFalseRank (seamGreedyWord s) d := by
  rw [rowChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hfalse, htail⟩ := h
  refine ⟨h2, hds, notMem_support_of_gb_false h2 hds hfalse, ?_⟩
  intro e hde hes
  rw [mem_support_iff (by omega) hes]
  have hk : (e - d - 1) ∈ List.range (s - d - 1) := List.mem_range.mpr (by omega)
  have hval := htail _ hk
  rwa [show d - 1 + (e - d - 1) = e - 2 by omega] at hval

theorem largestSkipLateAt_of_rowChk {s d : ℕ} (h2 : 2 ≤ d) (hds : d < s)
    (hlate : 2 * s < 3 * d) (h : rowChk s d = true) :
    LargestSkipLateAt s :=
  ⟨d, isLargestFalseRank_of_rowChk h2 hds h, hlate⟩

/-! ## 4. The twenty-one rows of the seven surviving classes

**MEASURED CONTEXT:** the seven values of `D` below were the depth-25
survivors in the scan described in the module header.

**PROVED HERE:** for each such explicit `D` and each of the three rows
`s = D+1, D+2, D+3` used by `AngleB2.hcof`, `rowChk` certifies the concrete
largest false rank and proves it is late.  Thus `LargestSkipLateAt s` holds at
all twenty-one listed rows. -/

section Rows

set_option maxRecDepth 8000000

/-! ### `D = 101` -/

/-- Row `102`: the largest false rank is `101`, and `3 * 101 = 303 > 204 = 2 * 102`. -/
theorem lateAt_102 : LargestSkipLateAt 102 :=
  largestSkipLateAt_of_rowChk (d := 101) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `103`: the largest false rank is `101`, and `3 * 101 = 303 > 206 = 2 * 103`. -/
theorem lateAt_103 : LargestSkipLateAt 103 :=
  largestSkipLateAt_of_rowChk (d := 101) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `104`: the largest false rank is `101`, and `3 * 101 = 303 > 208 = 2 * 104`. -/
theorem lateAt_104 : LargestSkipLateAt 104 :=
  largestSkipLateAt_of_rowChk (d := 101) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-! ### `D = 122` -/

/-- Row `123`: the largest false rank is `121`, and `3 * 121 = 363 > 246 = 2 * 123`. -/
theorem lateAt_123 : LargestSkipLateAt 123 :=
  largestSkipLateAt_of_rowChk (d := 121) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `124`: the largest false rank is `123`, and `3 * 123 = 369 > 248 = 2 * 124`. -/
theorem lateAt_124 : LargestSkipLateAt 124 :=
  largestSkipLateAt_of_rowChk (d := 123) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `125`: the largest false rank is `124`, and `3 * 124 = 372 > 250 = 2 * 125`. -/
theorem lateAt_125 : LargestSkipLateAt 125 :=
  largestSkipLateAt_of_rowChk (d := 124) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-! ### `D = 164` -/

/-- Row `165`: the largest false rank is `162`, and `3 * 162 = 486 > 330 = 2 * 165`. -/
theorem lateAt_165 : LargestSkipLateAt 165 :=
  largestSkipLateAt_of_rowChk (d := 162) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `166`: the largest false rank is `165`, and `3 * 165 = 495 > 332 = 2 * 166`. -/
theorem lateAt_166 : LargestSkipLateAt 166 :=
  largestSkipLateAt_of_rowChk (d := 165) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `167`: the largest false rank is `166`, and `3 * 166 = 498 > 334 = 2 * 167`. -/
theorem lateAt_167 : LargestSkipLateAt 167 :=
  largestSkipLateAt_of_rowChk (d := 166) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-! ### `D = 314` -/

/-- Row `315`: the largest false rank is `314`, and `3 * 314 = 942 > 630 = 2 * 315`. -/
theorem lateAt_315 : LargestSkipLateAt 315 :=
  largestSkipLateAt_of_rowChk (d := 314) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `316`: the largest false rank is `315`, and `3 * 315 = 945 > 632 = 2 * 316`. -/
theorem lateAt_316 : LargestSkipLateAt 316 :=
  largestSkipLateAt_of_rowChk (d := 315) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `317`: the largest false rank is `316`, and `3 * 316 = 948 > 634 = 2 * 317`. -/
theorem lateAt_317 : LargestSkipLateAt 317 :=
  largestSkipLateAt_of_rowChk (d := 316) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-! ### `D = 545` -/

/-- Row `546`: the largest false rank is `545`, and `3 * 545 = 1635 > 1092 = 2 * 546`. -/
theorem lateAt_546 : LargestSkipLateAt 546 :=
  largestSkipLateAt_of_rowChk (d := 545) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `547`: the largest false rank is `546`, and `3 * 546 = 1638 > 1094 = 2 * 547`. -/
theorem lateAt_547 : LargestSkipLateAt 547 :=
  largestSkipLateAt_of_rowChk (d := 546) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `548`: the largest false rank is `546`, and `3 * 546 = 1638 > 1096 = 2 * 548`. -/
theorem lateAt_548 : LargestSkipLateAt 548 :=
  largestSkipLateAt_of_rowChk (d := 546) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-! ### `D = 629` -/

/-- Row `630`: the largest false rank is `628`, and `3 * 628 = 1884 > 1260 = 2 * 630`. -/
theorem lateAt_630 : LargestSkipLateAt 630 :=
  largestSkipLateAt_of_rowChk (d := 628) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `631`: the largest false rank is `630`, and `3 * 630 = 1890 > 1262 = 2 * 631`. -/
theorem lateAt_631 : LargestSkipLateAt 631 :=
  largestSkipLateAt_of_rowChk (d := 630) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `632`: the largest false rank is `630`, and `3 * 630 = 1890 > 1264 = 2 * 632`. -/
theorem lateAt_632 : LargestSkipLateAt 632 :=
  largestSkipLateAt_of_rowChk (d := 630) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-! ### `D = 1112` -/

/-- Row `1113`: the largest false rank is `1111`, and `3 * 1111 = 3333 > 2226 = 2 * 1113`. -/
theorem lateAt_1113 : LargestSkipLateAt 1113 :=
  largestSkipLateAt_of_rowChk (d := 1111) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `1114`: the largest false rank is `1113`, and `3 * 1113 = 3339 > 2228 = 2 * 1114`. -/
theorem lateAt_1114 : LargestSkipLateAt 1114 :=
  largestSkipLateAt_of_rowChk (d := 1113) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- Row `1115`: the largest false rank is `1114`, and `3 * 1114 = 3342 > 2230 = 2 * 1115`. -/
theorem lateAt_1115 : LargestSkipLateAt 1115 :=
  largestSkipLateAt_of_rowChk (d := 1114) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

end Rows

/-! ## 5. The left disjunct fails, the right disjunct is structural

**PROVED:** at one row inside each window a cofactor rank is skipped, so
`AngleB2.hcof` is false for all seven explicit classes.  Consequently the
Angle B2 connection theorem cannot use its `hcof` hypothesis on any of them.
At one row inside each window the skipped rank is a *late* three-cofactor, so
`LargestSkipLateAt` there also follows from
`largestSkipLateAt_of_threeCofOdd_skip`, independently of the largest-rank
scan. -/

section Skips

set_option maxRecDepth 8000000

/-- At row `103` the three-cofactor `(2 * 103 + 1) / 3 = 69` is skipped. -/
theorem cofSkip_103_69 : (69 : ℕ) ∉ seamWordSupport (seamGreedyWord 103) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- Hence row `103` is late for a *structural* reason, independent of the
row scan: a late rank is skipped, so the largest false rank is late. -/
theorem lateAt_103_via_cofactor : LargestSkipLateAt 103 := by
  refine largestSkipLateAt_of_threeCofOdd_skip (s := 103) (by norm_num) (by decide) ?_
  rw [show ((2 * 103 + 1) / 3 : ℕ) = 69 from by norm_num]
  exact cofSkip_103_69

/-- At row `124` the three-cofactor `(2 * 124 + 1) / 3 = 83` is skipped. -/
theorem cofSkip_124_83 : (83 : ℕ) ∉ seamWordSupport (seamGreedyWord 124) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- Hence row `124` is late for a *structural* reason, independent of the
row scan: a late rank is skipped, so the largest false rank is late. -/
theorem lateAt_124_via_cofactor : LargestSkipLateAt 124 := by
  refine largestSkipLateAt_of_threeCofOdd_skip (s := 124) (by norm_num) (by decide) ?_
  rw [show ((2 * 124 + 1) / 3 : ℕ) = 83 from by norm_num]
  exact cofSkip_124_83

/-- At row `166` the three-cofactor `(2 * 166 + 1) / 3 = 111` is skipped. -/
theorem cofSkip_166_111 : (111 : ℕ) ∉ seamWordSupport (seamGreedyWord 166) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- Hence row `166` is late for a *structural* reason, independent of the
row scan: a late rank is skipped, so the largest false rank is late. -/
theorem lateAt_166_via_cofactor : LargestSkipLateAt 166 := by
  refine largestSkipLateAt_of_threeCofOdd_skip (s := 166) (by norm_num) (by decide) ?_
  rw [show ((2 * 166 + 1) / 3 : ℕ) = 111 from by norm_num]
  exact cofSkip_166_111

/-- At row `316` the three-cofactor `(2 * 316 + 1) / 3 = 211` is skipped. -/
theorem cofSkip_316_211 : (211 : ℕ) ∉ seamWordSupport (seamGreedyWord 316) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- Hence row `316` is late for a *structural* reason, independent of the
row scan: a late rank is skipped, so the largest false rank is late. -/
theorem lateAt_316_via_cofactor : LargestSkipLateAt 316 := by
  refine largestSkipLateAt_of_threeCofOdd_skip (s := 316) (by norm_num) (by decide) ?_
  rw [show ((2 * 316 + 1) / 3 : ℕ) = 211 from by norm_num]
  exact cofSkip_316_211

/-- At row `547` the three-cofactor `(2 * 547 + 1) / 3 = 365` is skipped. -/
theorem cofSkip_547_365 : (365 : ℕ) ∉ seamWordSupport (seamGreedyWord 547) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- Hence row `547` is late for a *structural* reason, independent of the
row scan: a late rank is skipped, so the largest false rank is late. -/
theorem lateAt_547_via_cofactor : LargestSkipLateAt 547 := by
  refine largestSkipLateAt_of_threeCofOdd_skip (s := 547) (by norm_num) (by decide) ?_
  rw [show ((2 * 547 + 1) / 3 : ℕ) = 365 from by norm_num]
  exact cofSkip_547_365

/-- At row `631` the three-cofactor `(2 * 631 + 1) / 3 = 421` is skipped. -/
theorem cofSkip_631_421 : (421 : ℕ) ∉ seamWordSupport (seamGreedyWord 631) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- Hence row `631` is late for a *structural* reason, independent of the
row scan: a late rank is skipped, so the largest false rank is late. -/
theorem lateAt_631_via_cofactor : LargestSkipLateAt 631 := by
  refine largestSkipLateAt_of_threeCofOdd_skip (s := 631) (by norm_num) (by decide) ?_
  rw [show ((2 * 631 + 1) / 3 : ℕ) = 421 from by norm_num]
  exact cofSkip_631_421

/-- At row `1114` the three-cofactor `(2 * 1114 + 1) / 3 = 743` is skipped. -/
theorem cofSkip_1114_743 : (743 : ℕ) ∉ seamWordSupport (seamGreedyWord 1114) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- Hence row `1114` is late for a *structural* reason, independent of the
row scan: a late rank is skipped, so the largest false rank is late. -/
theorem lateAt_1114_via_cofactor : LargestSkipLateAt 1114 := by
  refine largestSkipLateAt_of_threeCofOdd_skip (s := 1114) (by norm_num) (by decide) ?_
  rw [show ((2 * 1114 + 1) / 3 : ℕ) = 743 from by norm_num]
  exact cofSkip_1114_743


/-- `AngleB2.hcof` is **false** for `D = 101`: the cofactor rank `69` is
skipped at row `103`. -/
theorem hcof_fails_101 :
    ¬ (∀ s : ℕ, 101 + 1 ≤ s → s < 101 + 4 →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) := by
  intro h
  exact cofSkip_103_69 (h 103 (by norm_num) (by norm_num) (by decide))


theorem cofSkip_123_62 : (62 : ℕ) ∉ seamWordSupport (seamGreedyWord 123) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- `AngleB2.hcof` is **false** for `D = 122`: the cofactor rank `62` is
skipped at row `123`. -/
theorem hcof_fails_122 :
    ¬ (∀ s : ℕ, 122 + 1 ≤ s → s < 122 + 4 →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) := by
  intro h
  exact cofSkip_123_62 (h 123 (by norm_num) (by norm_num) (by decide))


theorem cofSkip_165_83 : (83 : ℕ) ∉ seamWordSupport (seamGreedyWord 165) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- `AngleB2.hcof` is **false** for `D = 164`: the cofactor rank `83` is
skipped at row `165`. -/
theorem hcof_fails_164 :
    ¬ (∀ s : ℕ, 164 + 1 ≤ s → s < 164 + 4 →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) := by
  intro h
  exact cofSkip_165_83 (h 165 (by norm_num) (by norm_num) (by decide))


theorem cofSkip_315_158 : (158 : ℕ) ∉ seamWordSupport (seamGreedyWord 315) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- `AngleB2.hcof` is **false** for `D = 314`: the cofactor rank `158` is
skipped at row `315`. -/
theorem hcof_fails_314 :
    ¬ (∀ s : ℕ, 314 + 1 ≤ s → s < 314 + 4 →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) := by
  intro h
  exact cofSkip_315_158 (h 315 (by norm_num) (by norm_num) (by decide))


/-- `AngleB2.hcof` is **false** for `D = 545`: the cofactor rank `365` is
skipped at row `547`. -/
theorem hcof_fails_545 :
    ¬ (∀ s : ℕ, 545 + 1 ≤ s → s < 545 + 4 →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) := by
  intro h
  exact cofSkip_547_365 (h 547 (by norm_num) (by norm_num) (by decide))


/-- `AngleB2.hcof` is **false** for `D = 629`: the cofactor rank `421` is
skipped at row `631`. -/
theorem hcof_fails_629 :
    ¬ (∀ s : ℕ, 629 + 1 ≤ s → s < 629 + 4 →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) := by
  intro h
  exact cofSkip_631_421 (h 631 (by norm_num) (by norm_num) (by decide))


theorem cofSkip_1113_557 : (557 : ℕ) ∉ seamWordSupport (seamGreedyWord 1113) :=
  notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel)

/-- `AngleB2.hcof` is **false** for `D = 1112`: the cofactor rank `557` is
skipped at row `1113`. -/
theorem hcof_fails_1112 :
    ¬ (∀ s : ℕ, 1112 + 1 ≤ s → s < 1112 + 4 →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) := by
  intro h
  exact cofSkip_1113_557 (h 1113 (by norm_num) (by norm_num) (by decide))

end Skips

/-! ## 6. Finite verdict for the seven measured survivor classes -/

/-- **PROVED, FINITE:** for each of the seven explicit values of `D` and each
of the three rows `D+1, D+2, D+3` consumed by `AngleB2.hcof`, the disjunction

  `cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s`

holds — and in all twenty-one cases through its **right** disjunct. -/
theorem skipDichotomy_survivors {D : ℕ}
    (hD : D = 101 ∨ D = 122 ∨ D = 164 ∨ D = 314 ∨ D = 545 ∨ D = 629 ∨ D = 1112)
    {s : ℕ} (hs1 : D + 1 ≤ s) (hs2 : s < D + 4) :
    AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s := by
  right
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases s <;>
    first
      | exact lateAt_102
      | exact lateAt_103
      | exact lateAt_104
      | exact lateAt_123
      | exact lateAt_124
      | exact lateAt_125
      | exact lateAt_165
      | exact lateAt_166
      | exact lateAt_167
      | exact lateAt_315
      | exact lateAt_316
      | exact lateAt_317
      | exact lateAt_546
      | exact lateAt_547
      | exact lateAt_548
      | exact lateAt_630
      | exact lateAt_631
      | exact lateAt_632
      | exact lateAt_1113
      | exact lateAt_1114
      | exact lateAt_1115

/-- **`AngleB2.hcof` is false on all seven explicit classes.**  At one row of
each window a cofactor rank is skipped by the concrete greedy, so the
conditional Angle B2 connection theorem is inapplicable there. -/
theorem hcof_fails_survivors {D : ℕ}
    (hD : D = 101 ∨ D = 122 ∨ D = 164 ∨ D = 314 ∨ D = 545 ∨ D = 629 ∨ D = 1112) :
    ¬ (∀ s : ℕ, D + 1 ≤ s → s < D + 4 →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) := by
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hcof_fails_101, hcof_fails_122, hcof_fails_164, hcof_fails_314, hcof_fails_545, hcof_fails_629, hcof_fails_1112]

/-- **PROVED, UNCONDITIONAL:** at every row `s ≥ 5`, either both ranks defined
by the two three-cofactor equations are selected, or `LargestSkipLateAt s`.
The implication from a skipped rank is `largestSkipLateAt_of_late_skip`; the
late-divisor restriction is `late_divisor_cofactor_three`. -/
theorem threeCof_skipDichotomy (s : ℕ) (hs : 5 ≤ s) :
    (∀ m : ℕ, 3 * m = 2 * s + 1 ∨ 3 * m = 2 * s + 2 →
        m ∈ seamWordSupport (seamGreedyWord s))
      ∨ LargestSkipLateAt s := by
  classical
  by_cases h : ∀ m : ℕ, 3 * m = 2 * s + 1 ∨ 3 * m = 2 * s + 2 →
      m ∈ seamWordSupport (seamGreedyWord s)
  · exact Or.inl h
  · right
    simp only [not_forall] at h
    obtain ⟨m, hm, hmem⟩ := h
    exact largestSkipLateAt_of_late_skip (by omega) (by omega) (by omega) hmem

/-! ## 7. Why the provable dichotomy still does not close the branch

`threeCof_skipDichotomy` is the form supported by the divisor/cofactor
argument in this file: the `(s+1)/2` cofactor cannot appear in the late zone
(`halfCof_not_late`), and `late_divisor_cofactor_three` excludes further
divisors of `2s+1` or `2s+2` from that zone.  Thus this argument certifies only
`lateCofRanks s ⊆ seamWordSupport …`, which supplies the smaller floor
`lateTotalFloor` rather than `AngleB2.totalFloor`.

**PROVED:** `AngleB2.cofRatchet_finite_core` computes zero for all `2730`
auxiliary full-floor phases at depth `3`.  For the different late-only
auxiliary ratchet, `lateRatchet_survivor_count` computes exactly `87` nonzero
phases at depth `12`, while the persistence theorems below certify named
nonterminating phases and an infinite arithmetic progression.  Neither
auxiliary computation makes the unreachable `seamExcess = 2` connection
theorem applicable. -/

section LateRatchet

/-- The cofactor ranks that actually lie in the late zone: the three-cofactors
only. -/
def lateCofRanks (s : ℕ) : Finset ℕ :=
  if s % 3 = 1 then {(2 * s + 1) / 3}
  else if s % 3 = 2 then {2 * (s + 1) / 3}
  else ∅

/-- The pulse those late ranks are guaranteed to contribute. -/
def lateCofFloor (s : ℕ) : ℕ :=
  if s % 3 = 1 then 2 else if s % 3 = 2 then 1 else 0

theorem lateCofRanks_subset_cofRanks (s : ℕ) : lateCofRanks s ⊆ AngleB2.cofRanks s := by
  have h6 : s % 6 = 0 ∨ s % 6 = 1 ∨ s % 6 = 2 ∨ s % 6 = 3 ∨ s % 6 = 4 ∨ s % 6 = 5 := by omega
  unfold lateCofRanks AngleB2.cofRanks
  rcases h6 with h | h | h | h | h | h
  · rw [if_neg (by omega : ¬ s % 3 = 1), if_neg (by omega : ¬ s % 3 = 2)]
    simp
  · rw [if_pos (by omega : s % 3 = 1), if_pos h]
    intro a ha
    simp only [Finset.mem_singleton] at ha
    simp [ha]
  · rw [if_neg (by omega : ¬ s % 3 = 1), if_pos (by omega : s % 3 = 2),
      if_neg (by omega : ¬ s % 6 = 1), if_pos h]
  · rw [if_neg (by omega : ¬ s % 3 = 1), if_neg (by omega : ¬ s % 3 = 2)]
    simp
  · rw [if_pos (by omega : s % 3 = 1), if_neg (by omega : ¬ s % 6 = 1),
      if_neg (by omega : ¬ s % 6 = 2), if_neg (by omega : ¬ s % 6 = 3), if_pos h]
  · rw [if_neg (by omega : ¬ s % 3 = 1), if_pos (by omega : s % 3 = 2),
      if_neg (by omega : ¬ s % 6 = 1), if_neg (by omega : ¬ s % 6 = 2),
      if_neg (by omega : ¬ s % 6 = 3), if_neg (by omega : ¬ s % 6 = 4), if_pos h]
    intro a ha
    simp only [Finset.mem_singleton] at ha
    simp [ha]

theorem lateCofRanks_cases {s d : ℕ} (hd : d ∈ lateCofRanks s) :
    d = (2 * s + 1) / 3 ∨ d = 2 * (s + 1) / 3 := by
  unfold lateCofRanks at hd
  split_ifs at hd <;>
    simp only [Finset.mem_singleton, Finset.notMem_empty] at hd <;> tauto

theorem lateCofRanks_ge (s : ℕ) (hs : 61 ≤ s) {d : ℕ} (hd : d ∈ lateCofRanks s) : 27 ≤ d := by
  rcases lateCofRanks_cases hd with rfl | rfl <;> omega

theorem lateCofRanks_disjoint (s : ℕ) (hs : 61 ≤ s) :
    Disjoint ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) (lateCofRanks s) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h27 := lateCofRanks_ge s hs hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem lateCofFloor_le_lateCofPulse (s : ℕ) (hs : 61 ≤ s) :
    lateCofFloor s ≤ ∑ d ∈ lateCofRanks s, rowPulse s d := by
  have h3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases h3 with h | h | h
  · simp only [lateCofFloor, lateCofRanks, if_neg (by omega : ¬ s % 3 = 1),
      if_neg (by omega : ¬ s % 3 = 2)]
    norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, s = 3 * q + 1 := ⟨s / 3, by omega⟩
    have e1 : (2 * (3 * q + 1) + 1) / 3 = 2 * q + 1 := by omega
    have hset : lateCofRanks (3 * q + 1) = {2 * q + 1} := by
      unfold lateCofRanks; rw [if_pos (by omega : (3 * q + 1) % 3 = 1), e1]
    have r1 : 2 ≤ rowPulse (3 * q + 1) (2 * q + 1) := by
      have hdv : (2 * q + 1) ∣ 2 * (3 * q + 1) + 1 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold lateCofFloor
    rw [if_pos (by omega : (3 * q + 1) % 3 = 1)]
    omega
  · obtain ⟨q, rfl⟩ : ∃ q, s = 3 * q + 2 := ⟨s / 3, by omega⟩
    have e1 : 2 * (3 * q + 2 + 1) / 3 = 2 * q + 2 := by omega
    have hset : lateCofRanks (3 * q + 2) = {2 * q + 2} := by
      unfold lateCofRanks
      rw [if_neg (by omega : ¬ (3 * q + 2) % 3 = 1), if_pos (by omega : (3 * q + 2) % 3 = 2), e1]
    have r1 : 1 ≤ rowPulse (3 * q + 2) (2 * q + 2) := by
      have hdv : (2 * q + 2) ∣ 2 * (3 * q + 2) + 2 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold lateCofFloor
    rw [if_neg (by omega : ¬ (3 * q + 2) % 3 = 1), if_pos (by omega : (3 * q + 2) % 3 = 2)]
    omega

/-- The late-only certified floor. -/
def lateTotalFloor (s : ℕ) : ℕ := Recon257.pulseFloor s + lateCofFloor s

/-- **Soundness of the late-only floor.**  Exactly `AngleB2.totalFloor_le_belowPulse`,
but assuming only that the *late* cofactor ranks are selected. -/
theorem lateTotalFloor_le_belowPulse (s : ℕ) (hs : 61 ≤ s)
    (hcof : lateCofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    lateTotalFloor s ≤ (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega)
  have h7 := seven_mem_seamGreedySupport s (by omega)
  have h14 := fourteen_mem_seamGreedySupport s (by omega)
  have h20 := twenty_mem_seamGreedySupport s (by omega)
  have h21 := twentyOne_mem_seamGreedySupport s (by omega)
  have h26 := twentySix_mem_seamGreedySupport s (by omega)
  have hsmall : ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ⊆
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
  have hsub : (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ lateCofRanks s) ⊆
      seamWordSupport (seamGreedyWord s) := Finset.union_subset hsmall hcof
  have hsum :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ lateCofRanks s), rowPulse s d ≤
        ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hsplit :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ lateCofRanks s), rowPulse s d =
        (∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d) +
          ∑ d ∈ lateCofRanks s, rowPulse s d :=
    Finset.sum_union (lateCofRanks_disjoint s hs)
  have hexp : ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d =
      Recon257.pulseFloor s := by
    rw [Recon257.pulseFloor_eq_rowPulseSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hcofp := lateCofFloor_le_lateCofPulse s hs
  change lateTotalFloor s ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  unfold lateTotalFloor
  rw [hsplit, hexp] at hsum
  omega

/-! ### The late-only ratchet -/

def lateStep (s b : ℕ) : ℕ :=
  if 3 * lateTotalFloor s + 4 ≤ 4 * b then 4 * b - (3 * lateTotalFloor s + 3) else 0

def lateRun (D : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => lateStep (D + 1 + k) (lateRun D k)

theorem lateRun_succ (D k : ℕ) : lateRun D (k + 1) = lateStep (D + 1 + k) (lateRun D k) := rfl

theorem lateCofFloor_le_two (s : ℕ) : lateCofFloor s ≤ 2 := by
  unfold lateCofFloor; split_ifs <;> omega

theorem lateTotalFloor_le_eleven (s : ℕ) : lateTotalFloor s ≤ 11 := by
  have h1 := Recon257.pulseFloor_le_nine s
  have h2 := lateCofFloor_le_two s
  unfold lateTotalFloor
  omega

/-- Above `12` the late-only ratchet is non-decreasing: it can never die. -/
theorem twelve_le_lateStep (s b : ℕ) (hb : 12 ≤ b) : 12 ≤ lateStep s b := by
  have h := lateTotalFloor_le_eleven s
  unfold lateStep
  rw [if_pos (by omega)]
  omega

theorem lateStep_zero (s : ℕ) : lateStep s 0 = 0 := by
  have h := Recon257.one_le_pulseFloor s
  unfold lateStep lateTotalFloor
  rw [if_neg (by omega)]

theorem lateRun_eq_zero_of_le {D j k : ℕ} (hjk : j ≤ k) (hj : lateRun D j = 0) :
    lateRun D k = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction i with
  | zero => simpa using hj
  | succ i ih => rw [show j + (i + 1) = (j + i) + 1 by ring, lateRun_succ, ih, lateStep_zero]

theorem twelve_le_lateRun_of_le {D k₀ k : ℕ} (h : 12 ≤ lateRun D k₀) (hk : k₀ ≤ k) :
    12 ≤ lateRun D k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => simpa using h
  | succ j ih =>
      rw [show k₀ + (j + 1) = (k₀ + j) + 1 by ring, lateRun_succ]
      exact twelve_le_lateStep _ _ ih

/-- Once the late-only budget passes `12` at depth `4` it is never `0`, at any
depth: `12` is above the fixed point of `b ↦ 4b - 3 * lateTotalFloor - 3`. -/
theorem lateRun_ne_zero_of_twelve_le_four {D : ℕ} (h : 12 ≤ lateRun D 4) (k : ℕ) :
    lateRun D k ≠ 0 := by
  intro hk
  rcases Nat.le_total k 4 with hle | hle
  · have := lateRun_eq_zero_of_le hle hk
    omega
  · have := twelve_le_lateRun_of_le h hle
    omega

section Escapes

set_option maxRecDepth 40000

theorem lateRun_20_four : lateRun 20 4 = 24 := by decide +kernel
theorem lateRun_314_four : lateRun 314 4 = 24 := by decide +kernel
theorem lateRun_545_four : lateRun 545 4 = 21 := by decide +kernel
theorem lateRun_629_four : lateRun 629 4 = 24 := by decide +kernel
theorem lateRun_1112_four : lateRun 1112 4 = 24 := by decide +kernel

/-- **PROVED, AUXILIARY COMPUTATION:** the late-only recurrence is zero at
depth `3` for `D = 101, 122, 164`.  This does not say that the concrete
`belowPulse` equals the late-only floor; in fact the selected-late-cofactor
hypothesis fails on these classes. -/
theorem lateRun_101_three : lateRun 101 3 = 0 := by decide +kernel
theorem lateRun_122_three : lateRun 122 3 = 0 := by decide +kernel
theorem lateRun_164_three : lateRun 164 3 = 0 := by decide +kernel

end Escapes

/-- **The late-only ratchet does not terminate.** -/
theorem lateRun_twenty_ne_zero (k : ℕ) : lateRun 20 k ≠ 0 :=
  lateRun_ne_zero_of_twelve_le_four (by rw [lateRun_20_four]; omega) k

/-- **Four of the seven measured survivor classes escape the late-only ratchet
outright**, at every depth.  For these, certifying the late three-cofactor at
every row of the window would still not close the branch. -/
theorem lateRun_314_ne_zero (k : ℕ) : lateRun 314 k ≠ 0 :=
  lateRun_ne_zero_of_twelve_le_four (by rw [lateRun_314_four]; omega) k

theorem lateRun_545_ne_zero (k : ℕ) : lateRun 545 k ≠ 0 :=
  lateRun_ne_zero_of_twelve_le_four (by rw [lateRun_545_four]; omega) k

theorem lateRun_629_ne_zero (k : ℕ) : lateRun 629 k ≠ 0 :=
  lateRun_ne_zero_of_twelve_le_four (by rw [lateRun_629_four]; omega) k

theorem lateRun_1112_ne_zero (k : ℕ) : lateRun 1112 k ≠ 0 :=
  lateRun_ne_zero_of_twelve_le_four (by rw [lateRun_1112_four]; omega) k

theorem lateCofFloor_add_period (s : ℕ) : lateCofFloor (s + 2730) = lateCofFloor s := by
  unfold lateCofFloor
  rw [show (s + 2730) % 3 = s % 3 by omega]

theorem lateTotalFloor_add_period (s : ℕ) : lateTotalFloor (s + 2730) = lateTotalFloor s := by
  unfold lateTotalFloor
  rw [Recon257.pulseFloor_add_period, lateCofFloor_add_period]

theorem lateRun_add_period (D k : ℕ) : lateRun (D + 2730) k = lateRun D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [lateRun_succ, lateRun_succ, ih]
      unfold lateStep
      rw [show D + 2730 + 1 + k = (D + 1 + k) + 2730 by ring, lateTotalFloor_add_period]

theorem lateRun_add_mul_period (D k n : ℕ) : lateRun (D + 2730 * n) k = lateRun D k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show D + 2730 * (n + 1) = (D + 2730 * n) + 2730 by ring, lateRun_add_period, ih]

/-- **An infinite arithmetic progression of classes the late-only ratchet
never kills.** -/
theorem lateRun_progression_ne_zero (n k : ℕ) : lateRun (20 + 2730 * n) k ≠ 0 := by
  rw [lateRun_add_mul_period]
  exact lateRun_twenty_ne_zero k

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
/-- **PROVED, FINITE COMPUTATION:** exactly `87` of the `2730` phases are
nonzero at depth `12` in the late-only recurrence.  Persistence at every depth
is proved separately above for phases satisfying the stated lower-bound
hypothesis; it is not part of this cardinality statement. -/
theorem lateRatchet_survivor_count :
    ((Finset.range 2730).filter (fun D => lateRun D 12 ≠ 0)).card = 87 := by
  decide +kernel

end LateRatchet

/-! ## 8. What a cofinal supply of right disjuncts buys

A single proof of `LargestSkipLateAt` does not supply the cofinal hypothesis
needed by the endpoint theorem.  **PROVED:** if such rows occur along a
sequence tending to infinity, they give unbounded skipped ranks and hence the
membership endpoint.  The corpus states that fan-in for the row sequence
`j ↦ 14 + j` behind `LargestSkipLateStepSocket`; below it is derived for an
arbitrary cofinal row sequence. -/

section Endpoint

open Filter

/-- **A cofinal supply of late rows already gives unbounded skipped ranks.** -/
theorem seamGreedyUnboundedSkippedRanksAlong_of_lateAlong
    (rows : ℕ → ℕ) (hrows : Tendsto rows atTop atTop)
    (hlate : ∀ j, LargestSkipLateAt (rows j)) :
    SeamGreedyUnboundedSkippedRanksAlong rows := by
  classical
  choose rank hrank using hlate
  let skip : ∀ j : ℕ, Fin (rows j - 2) := fun j =>
    ⟨rank j - 2, by
      rcases (hrank j).1 with ⟨_hd2, hds, _hdnot, _hfull⟩
      omega⟩
  refine ⟨skip, hrows, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro B
    filter_upwards [hrows.eventually (eventually_ge_atTop (3 * B))] with j hj
    rcases (hrank j).1 with ⟨hd2, _hds, _hdnot, _hfull⟩
    have hmargin := (hrank j).2
    have hrankEq : (skip j : ℕ) + 2 = rank j := by
      dsimp [skip]
      omega
    rw [hrankEq]
    omega
  · intro j
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    rcases (hrank j).1 with ⟨hd2, _hds, hdnot, _hfull⟩
    have hrankEq : rank j = (skip j : ℕ) + 2 := by
      dsimp [skip]
      omega
    exact hdnot (mem_seamWordSupport_iff.mpr ⟨skip j, htrue, hrankEq⟩)

/-- **Late rows along any cofinal sequence give the `#257` endpoint.** -/
theorem half_mem_of_lateAlong
    (rows : ℕ → ℕ) (hrows : Tendsto rows atTop atTop)
    (hlate : ∀ j, LargestSkipLateAt (rows j)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_unboundedSkippedRanks rows
    (seamGreedyUnboundedSkippedRanksAlong_of_lateAlong rows hrows hlate)

/-- Cofinally many late rows suffice; no induction and no step socket. -/
theorem half_mem_of_lateCofinal
    (h : ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ LargestSkipLateAt s) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  choose rows hge hlate using h
  exact half_mem_of_lateAlong rows (tendsto_atTop_mono hge tendsto_id) hlate

/-- **The global skip dichotomy.**  Either the two three-cofactor ranks are
selected by the concrete greedy at all but finitely many rows, or
`1/2 ∈ mersenneAchievementSet`.  There is no third possibility, and no
hypothesis: this is unconditional. -/
theorem eventually_threeCof_selected_or_half_mem :
    (∃ N : ℕ, ∀ s : ℕ, N ≤ s →
        ∀ m : ℕ, 3 * m = 2 * s + 1 ∨ 3 * m = 2 * s + 2 →
          m ∈ seamWordSupport (seamGreedyWord s))
      ∨ (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  by_cases h : ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      ∀ m : ℕ, 3 * m = 2 * s + 1 ∨ 3 * m = 2 * s + 2 →
        m ∈ seamWordSupport (seamGreedyWord s)
  · exact Or.inl h
  · right
    apply half_mem_of_lateCofinal
    intro N
    by_contra hcon
    refine h ⟨N + 5, ?_⟩
    intro s hs m hm
    by_contra hmem
    exact hcon ⟨s, by omega,
      largestSkipLateAt_of_late_skip (m := m) (by omega) (by omega) (by omega) hmem⟩

end Endpoint

/-!
## Verdict

**PROVED, FINITE:** the dichotomy holds through its right disjunct in all
twenty-one listed cases.

For every one of the seven classes `D = 101, 122, 164, 314, 545, 629, 1112` and
every one of the three rows `s = D+1, D+2, D+3` that `AngleB2.hcof` consumes,

  `AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s`

is proved (`skipDichotomy_survivors`), and the right disjunct is the one that
holds every time.  The concrete largest false ranks are

  `s`   `102 103 104 | 123 124 125 | 165 166 167 | 315 316 317`
  `d*`  `101 101 101 | 121 123 124 | 162 165 166 | 314 315 316`

  `s`   `546 547 548 | 630 631 632 | 1113 1114 1115`
  `d*`  `545 546 546 | 628 630 630 | 1111 1113 1114`

so `d*` always sits within four of the terminal rank `s-1`, and
`2 * s < 3 * d*` in every listed row.

**PROVED, FINITE:** the displayed skipped cofactor is not itself the largest
false rank in any of the seven windows.  It does not have to be: at one row of
every window a *three*-cofactor `(2s+1)/3` is skipped —

  `(103, 69), (124, 83), (166, 111), (316, 211), (547, 365), (631, 421),`
  `(1114, 743)`

— and `largestSkipLateAt_of_late_skip` promotes any late skip to a late
*largest* skip.  Thus the right disjunct in these seven rows follows both from
the concrete `rowChk` computation and from the cofactor-skip theorem
(`lateAt_103_via_cofactor` and its siblings).

**PROVED:** `AngleB2.hcof` is false on all seven
(`hcof_fails_survivors`).  The
witnesses are the cofactor ranks the greedy skips: `69` at row `103`, `62` at
`123`, `83` at `165`, `158` at `315`, `365` at `547`, `421` at `631`, `557` at
`1113`.  Thus the conditional Angle B2 connection theorem cannot be applied to
any of these seven classes.

**Two corrections to the dichotomy as originally posed.**

1.  With `AngleB2.cofRanks` on the left, this file proves the dichotomy only
    for the twenty-one listed rows.
    The rank `(s+1)/2` sits at half the row and is never late
    (`halfCof_not_late`), so skipping it says nothing about the largest false
    rank.  By `late_divisor_cofactor_three`, among divisors of `2s+1` and
    `2s+2`, cofactor `3` is the only one reaching the late zone, so adding
    cofactor `5`, `7`, and so on does not extend this particular late-divisor
    argument.  The unconditional proved form replaces `cofRanks` by the two
    three-cofactors (`threeCof_skipDichotomy`), and in that form it is
    unconditional at every row `s ≥ 5`.

2.  A single late row does not satisfy the endpoint's cofinal hypothesis.
    `half_mem_of_lateCofinal` proves that cofinally many late rows suffice,
    giving the unconditional disjunction

      `eventually_threeCof_selected_or_half_mem :`
      `  (∃ N, ∀ s ≥ N, both three-cofactors selected) ∨ 1/2 ∈ mersenneAchievementSet`.

**The all-right-tail branch does not close.**  There are two separate reasons.

* **MEASURED, NOT PROVED HERE:** on `D ∈ [60,700)`, the `hcof` cases add no
  exclusions beyond the direct concrete `belowPulse` computation.  Moreover,
  `Recon257.seamExcess s = 2` has no audited instance for `s ∈ [5,102]`, so
  `allRight_landingExcess_two_impossible` is unreachable on that range.
* **PROVED FOR THE AUXILIARY LATE-ONLY RECURRENCE:** in the left case of the
  global three-cofactor dichotomy the available certified floor is
  `lateTotalFloor`, not `AngleB2.totalFloor`.  Theorem
  `lateRatchet_survivor_count` finds exactly `87` nonzero phases at depth `12`;
  the persistence theorems certify an infinite progression and, among the
  seven listed classes, the four classes
  `lateRun_314_ne_zero`, `lateRun_545_ne_zero`, `lateRun_629_ne_zero`, and
  `lateRun_1112_ne_zero` as nonzero at every depth.  The other three auxiliary
  recurrences are zero at depth `3` (`lateRun_101_three`,
  `lateRun_122_three`, `lateRun_164_three`), but the hypotheses required to
  identify that auxiliary floor with selected concrete cofactor contributions
  fail there.

The honest conclusion is finite and conditional in scope: this file proves
the stated twenty-one late-skip certificates, seven `hcof` failures,
cofactor-divisor restrictions, auxiliary ratchet calculations, and cofinal
endpoint implications.  It neither supplies a cofinal sequence of late rows
nor makes the Angle B2 connection theorem applicable.  Erdős #257 remains
open.
-/

end SkipD3

end Erdos249257
