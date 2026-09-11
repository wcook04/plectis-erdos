/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Skip.D2
import ErdosProblems.Skip.D3

/-!
# Bit correspondence 3: the top take-run, and how far it is from what `#257` needs

`AngleD2.half_mem_iff_unboundedLargestSkipLate` reduces the `1/2` question of
Erdos `#257` to `LargestSkipLateAt s` holding at cofinally many rows.  This file
re-expresses that condition as a statement about **one number per row** — the
length of the run of consecutive *takes* at the top of the concrete greedy word —
and measures that number.

## The reformulation

Write `lateFloor s = 2 * s / 3 + 1` for the first rank of the late zone (rank `d`
is late exactly when `lateFloor s <= d`, `late_iff_lateFloor_le`), and

    runNeeded s = s - lateFloor s        (`K`, the width of the late zone)
    topTaken s r = true  <->  the ranks s-1, s-2, ..., s-r are all selected.

Then, for every `s >= 5`,

    `largestSkipLateAt_iff_topTaken_false` :
        LargestSkipLateAt s  <->  topTaken s (runNeeded s) = false

so `#257` becomes (`half_mem_iff_topRun_deficient`)

    (1/2 : R) in mersenneAchievementSet
      <->  for every N there is s >= N whose top take-run is shorter than K.

Equivalently: `1/2` is *missed* only if, from some row on, **every** row's greedy
word ends in a run of `K ~ s/3` consecutive takes — a maximal-length run, one
that fills the entire late zone.

## The measurement

Outside the kernel, an arbitrary-precision replication of `seamWeights`,
`seamSubsetTarget` and `integerGreedyBits` was run for every `s` in `[5, 3000]`
(2996 rows).  It reproduces this repository's earlier measurements exactly:
`H4`'s `d0(81) = 75`, `d0(3000) = 2996`, `d0(3001) = 3000`, its whole `[61,500]`
table, and `H3`'s "`LargestSkipLateAt` at every `s in [5,400]` except
`s = 5, 11, 12, 13`".  Over the full range `[5, 3000]`:

* `LargestSkipLateAt s` **holds at every row except `s = 5, 11, 12, 13`** — i.e.
  the forced maximal run occurs four times ever, all with `K <= 4`, and never
  once for `s >= 14`;
* the top take-run `r(s) = s - 1 - d0(s)` has distribution
  `0:1461, 1:759, 2:385, 3:191, 4:96, 5:51, 6:27, 7:14, 8:6, 9:2, 10:2, 11:1, 12:1`
  — counts consistent with a geometric ratio near `1/2` — and its **maximum over the whole
  range is 12**, attained at `s = 1148`, where `K = 382`;
* the longest run of consecutive takes anywhere inside the late zone (not just at
  the top) is `13`, at `s = 1703`, where `K = 567`;
* `K` grows linearly (`K = 166` at `s = 501`, `999` at `s = 3000`), and roughly
  **half of all late ranks are skipped**: 21 of 33 at `s = 100`, 64 of 133 at
  `s = 400`, 480 of 999 at `s = 3000`.

On this finite range, `r(s)` remains small while the required `K(s)` grows
linearly; the computation does not prove an asymptotic `O(log s)` bound.  The
ratio `r(s) / K(s)` attains `1` at `s = 5, 11, 12, 13` and nowhere else; over
`[14, 3000]` its maximum is `4/6` at `s = 19`, and over `[61, 3000]` its maximum
is `5/26 ~ 0.193` at `s = 81`.  No row of `[14, 3000]` even reaches `r = K - 1`.

The one further caveat the replication turned up: the "read the remainder's bits"
reading of the late word — the greedy's late take/skip word equals the binary
expansion of the remainder entering the late zone, read at bit positions
`2s - d` — is exact at **every** `s in [6, 3000]` and fails only at the
degenerate row `s = 5` (`K = 1`), where a borrow does occur.  This does not
affect the proved top-run equivalence: at `s = 5` the concrete top run has
length `1 = K`, so it correctly records the failure of `LargestSkipLateAt`.
What fails there is only the separate interpretation of the late word as the
entering remainder's binary digits.

## What is certified here, in the kernel

No `sorry`, no `native_decide`, no new axiom; `decide +kernel` only.

* `largestSkipLateAt_iff_topTaken_false`, `half_mem_iff_topRun_deficient` —
  proved for all rows in their stated range (`s ≥ 5` for the rowwise
  equivalence).  These are proofs, not computations.
* `topRun_le_twelve_block`, `largestSkipLateAt_block`,
  `topTaken_runNeeded_false_block` — for **every** `s` in `[501, 1200]`, an
  unbroken block of `700` rows disjoint from `H4`'s `[61, 500]`, the greedy has a
  largest false rank `d` with `s <= d + 13`, hence a top take-run of at most `12`,
  hence `topTaken s (runNeeded s) = false` and `LargestSkipLateAt s`.
* `topRun_deficit` — the quantitative form on the same block:
  `r(s) + s / 4 <= runNeeded s`.  The shortfall between the run the row has and
  the run the negative branch needs is at least `s / 4`, i.e. it grows linearly.
* `topRun_record_1148` — the extremal row is pinned exactly: `topTaken 1148 12`
  is `true` and `topTaken 1148 13` is `false`, so the record run over `[5, 3000]`
  is exactly `12`, against `runNeeded 1148 = 382`.
* `largestSkipLateAt_high` — rows far beyond anything previously certified here:
  `3500, 4000, 4500, 5000, 6000, 7000, 8000`.  At `s = 8000` the largest false
  rank is `7998`, so the top take-run is `1` while `runNeeded 8000 = 2666`.

## Finite witnesses

The rowwise hypotheses used below are exhibited by concrete kernel-checked
instances: `largestSkipLateAt_8000` and `topTaken_runNeeded_false_8000` witness
the two sides of the rowwise equivalence, and the `700`-row block witnesses
`501 ≤ s ≤ 1200`.  A single row at `8000` does not witness the cofinal
quantifier in `half_mem_iff_topRun_deficient`; cofinality is explicitly left
open below.

## What this does *not* prove

Cofinality.  A run of `700` consecutive rows, plus seven spot rows up to `8000`,
does not exclude a tail of rows on which the run is maximal.  What the file does
is convert `#257` into a single measurable quantity and show that the quantity
misses its target by a linearly growing margin everywhere it has been looked at.
The live target is an unconditional bound `r(s) < K(s)`, or even just
`r(s) <= s - 1 - lateFloor s` failing to be tight, for all large `s`.
-/

namespace Erdos249257

namespace BitCorr3

open HalfCylinderIntegerGreedy

/-! ## 1. The late zone as a run length -/

/-- The first rank of the late zone `(2s/3, s)`. -/
def lateFloor (s : ℕ) : ℕ := 2 * s / 3 + 1

/-- `K s`: the number of ranks in the late zone — the length of the run of
consecutive takes at the top of row `s` that `¬ LargestSkipLateAt s` forces. -/
def runNeeded (s : ℕ) : ℕ := s - lateFloor s

/-- Lateness is exactly `lateFloor s ≤ d`. -/
theorem late_iff_lateFloor_le {s d : ℕ} : 2 * s < 3 * d ↔ lateFloor s ≤ d := by
  unfold lateFloor
  omega

/-- `K` really is of order `s / 3`. -/
theorem runNeeded_lower_bound (s : ℕ) : s ≤ 3 * runNeeded s + 3 := by
  unfold runNeeded lateFloor
  omega

/-- `topTaken s r` : the top `r` ranks `s-1, s-2, …, s-r` are all selected by the
concrete integer seam greedy of row `s`. -/
def topTaken (s r : ℕ) : Bool :=
  (List.range r).all (fun k => (SkipD3.gb s).getD (s - 3 - k) false)

/-- Reading a `true` out of a top run. -/
theorem mem_of_topTaken {s r k : ℕ} (h : topTaken s r = true) (hk : k < r)
    (hks : k + 3 ≤ s) :
    (s - 1 - k) ∈ seamWordSupport (seamGreedyWord s) := by
  rw [topTaken, List.all_eq_true] at h
  have hbit := h k (List.mem_range.mpr hk)
  rw [SkipD3.mem_support_iff (by omega) (by omega),
    show s - 1 - k - 2 = s - 3 - k by omega]
  exact hbit

/-- A skipped rank inside the top `r` breaks the run. -/
theorem topTaken_eq_false_of_notMem {s r d : ℕ} (h2 : 2 ≤ d) (hds : d < s)
    (hr : s ≤ d + r) (hnot : d ∉ seamWordSupport (seamGreedyWord s)) :
    topTaken s r = false := by
  cases hb : topTaken s r with
  | false => rfl
  | true =>
      exfalso
      have hk : s - 1 - d < r := by omega
      have hks : (s - 1 - d) + 3 ≤ s := by omega
      have hmem := mem_of_topTaken hb hk hks
      rw [show s - 1 - (s - 1 - d) = d by omega] at hmem
      exact hnot hmem

/-! ## 2. The reformulation of the `#257` endpoint -/

/-- **The late largest skip is exactly a deficient top run.**  Row `s` has a late
largest false rank iff the greedy's run of takes at the top of the row is
*shorter* than the whole late zone. -/
theorem largestSkipLateAt_iff_topTaken_false {s : ℕ} (hs : 5 ≤ s) :
    LargestSkipLateAt s ↔ topTaken s (runNeeded s) = false := by
  constructor
  · rintro ⟨d, ⟨hd2, hds, hdnot, -⟩, hlate⟩
    have hfl : lateFloor s ≤ d := late_iff_lateFloor_le.mp hlate
    refine topTaken_eq_false_of_notMem hd2 hds ?_ hdnot
    unfold runNeeded
    omega
  · intro h
    by_contra hcon
    have hall : topTaken s (runNeeded s) = true := by
      rw [topTaken, List.all_eq_true]
      intro k hk
      have hkr : k < runNeeded s := List.mem_range.mp hk
      have hrn : runNeeded s = s - lateFloor s := rfl
      have hlf : lateFloor s = 2 * s / 3 + 1 := rfl
      have hfl : lateFloor s ≤ s - 1 - k := by omega
      have hlf2 : 2 ≤ lateFloor s := by omega
      have hmem := AngleD2.mem_of_late_of_not_largestSkipLateAt hcon
        (d := s - 1 - k) (by omega) (by omega) (late_iff_lateFloor_le.mpr hfl)
      rw [SkipD3.mem_support_iff (by omega) (by omega),
        show s - 1 - k - 2 = s - 3 - k by omega] at hmem
      exact hmem
    rw [hall] at h
    exact Bool.noConfusion h

/-- **Erdos `#257`, as a statement about one run length per row.**  `1/2` is
achieved iff the greedy's top take-run falls short of the full late zone at
cofinally many rows. -/
theorem half_mem_iff_topRun_deficient :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ topTaken s (runNeeded s) = false := by
  rw [AngleD2.half_mem_iff_unboundedLargestSkipLate]
  constructor
  · intro h N
    obtain ⟨s, hs, hlate⟩ := h (max N 5)
    exact ⟨s, le_trans (le_max_left _ _) hs,
      (largestSkipLateAt_iff_topTaken_false (le_trans (le_max_right _ _) hs)).mp hlate⟩
  · intro h N
    obtain ⟨s, hs, hfalse⟩ := h (max N 5)
    exact ⟨s, le_trans (le_max_left _ _) hs,
      (largestSkipLateAt_iff_topTaken_false (le_trans (le_max_right _ _) hs)).mpr hfalse⟩

/-! ## 3. The measured block `[501, 1200]`

`H4` certifies `[61, 500]`.  This is the next `700` rows, chosen so that the
record top run of the whole computed range `[5, 3000]` — `12`, at `s = 1148` —
lies inside the block. -/

/-- The measured largest false rank `d₀(501 + k)`, `k < 700`.  Every entry is
certified below by `SkipD3.rowChk`. -/
def d0Table : List ℕ :=
[
  500, 500, 502, 502, 502, 502, 502, 502, 502, 502, 502, 511, 511, 513, 514, 515, 516, 517,
  517, 519, 520, 520, 522, 522, 524, 525, 525, 527, 528, 529, 529, 529, 532, 533, 534, 535,
  535, 537, 538, 539, 539, 539, 539, 539, 539, 545, 546, 546, 546, 546, 546, 551, 552, 553,
  553, 553, 553, 553, 553, 559, 560, 560, 560, 563, 563, 563, 563, 563, 568, 568, 568, 571,
  571, 573, 574, 574, 574, 574, 574, 579, 580, 580, 582, 583, 583, 585, 585, 585, 585, 585,
  585, 585, 592, 592, 594, 594, 596, 597, 597, 597, 597, 601, 602, 602, 602, 602, 606, 606,
  606, 606, 606, 606, 606, 606, 606, 606, 606, 617, 618, 619, 620, 620, 620, 620, 624, 624,
  626, 627, 628, 628, 630, 630, 632, 633, 634, 634, 636, 637, 638, 639, 640, 641, 641, 643,
  643, 643, 646, 647, 647, 647, 650, 651, 652, 653, 654, 655, 656, 656, 658, 658, 660, 660,
  660, 660, 664, 664, 666, 666, 668, 669, 669, 671, 671, 673, 673, 673, 676, 677, 678, 678,
  680, 681, 682, 683, 684, 685, 686, 686, 686, 689, 690, 691, 692, 692, 692, 692, 692, 697,
  698, 699, 700, 700, 702, 703, 703, 705, 705, 705, 708, 709, 710, 710, 710, 710, 710, 715,
  716, 717, 717, 717, 717, 717, 722, 722, 724, 724, 724, 727, 727, 729, 730, 730, 730, 733,
  733, 733, 733, 733, 733, 733, 740, 740, 742, 743, 743, 743, 743, 747, 748, 748, 748, 751,
  752, 752, 752, 752, 752, 752, 758, 759, 760, 761, 762, 763, 763, 763, 766, 766, 768, 769,
  770, 771, 771, 771, 774, 774, 774, 774, 774, 779, 779, 779, 779, 779, 784, 784, 786, 786,
  788, 789, 789, 791, 791, 793, 794, 795, 796, 797, 798, 799, 799, 799, 799, 799, 804, 804,
  804, 807, 807, 807, 807, 807, 807, 813, 813, 813, 816, 816, 818, 818, 820, 821, 822, 822,
  824, 824, 824, 827, 828, 828, 830, 831, 832, 833, 833, 835, 836, 836, 838, 839, 840, 841,
  842, 842, 842, 842, 842, 847, 847, 849, 850, 850, 852, 852, 854, 854, 856, 857, 858, 858,
  858, 861, 862, 862, 864, 864, 864, 867, 867, 867, 870, 870, 872, 873, 874, 875, 876, 876,
  878, 879, 880, 881, 882, 883, 883, 883, 883, 887, 888, 888, 888, 891, 892, 892, 892, 892,
  896, 897, 897, 899, 899, 899, 899, 899, 904, 905, 905, 905, 908, 908, 908, 911, 911, 911,
  914, 914, 916, 916, 918, 919, 920, 921, 921, 923, 923, 925, 926, 927, 927, 927, 927, 931,
  931, 933, 933, 933, 933, 937, 937, 939, 940, 941, 942, 942, 942, 945, 946, 947, 947, 949,
  950, 951, 951, 951, 951, 951, 951, 951, 958, 959, 960, 961, 961, 963, 963, 963, 963, 963,
  968, 969, 969, 971, 971, 971, 971, 975, 975, 975, 975, 979, 980, 980, 982, 982, 982, 985,
  986, 987, 988, 989, 989, 991, 992, 992, 992, 992, 992, 992, 992, 992, 992, 1001, 1001,
  1001, 1004, 1004, 1006, 1006, 1006, 1006, 1010, 1011, 1012, 1012, 1014, 1015, 1015, 1017,
  1017, 1017, 1020, 1021, 1021, 1021, 1024, 1025, 1026, 1026, 1026, 1026, 1030, 1031, 1032,
  1033, 1033, 1033, 1033, 1037, 1038, 1039, 1039, 1039, 1039, 1039, 1044, 1044, 1044, 1047,
  1047, 1049, 1050, 1051, 1051, 1051, 1051, 1055, 1056, 1057, 1058, 1059, 1059, 1061, 1062,
  1063, 1064, 1064, 1064, 1067, 1068, 1069, 1070, 1070, 1072, 1073, 1074, 1074, 1076, 1076,
  1078, 1079, 1079, 1081, 1082, 1083, 1083, 1085, 1085, 1085, 1088, 1088, 1088, 1088, 1092,
  1092, 1092, 1092, 1096, 1097, 1097, 1097, 1097, 1101, 1101, 1101, 1104, 1105, 1106, 1106,
  1106, 1109, 1109, 1111, 1111, 1113, 1114, 1115, 1116, 1116, 1116, 1119, 1119, 1119, 1119,
  1123, 1124, 1125, 1125, 1127, 1128, 1129, 1130, 1130, 1132, 1132, 1134, 1135, 1135, 1135,
  1135, 1135, 1135, 1135, 1135, 1135, 1135, 1135, 1135, 1135, 1148, 1148, 1148, 1151, 1152,
  1152, 1154, 1155, 1156, 1156, 1156, 1159, 1159, 1161, 1161, 1161, 1161, 1161, 1161, 1161,
  1161, 1161, 1170, 1170, 1170, 1170, 1170, 1170, 1170, 1177, 1177, 1177, 1177, 1181, 1181,
  1183, 1183, 1185, 1186, 1186, 1188, 1188, 1188, 1191, 1192, 1193, 1194, 1194, 1196, 1196,
  1196, 1196]

/-- Lookup into `d0Table`. -/
def d0At (s : ℕ) : ℕ := d0Table.getD (s - 501) 0

/-- The row certificate: the tabulated rank is a genuine rank of the row, sits
within `13` of the row index (so the top take-run is at most `12`), is late, and
really is the largest false rank of the concrete greedy word. -/
def rowOk (s : ℕ) : Bool :=
  (2 ≤ d0At s) && (d0At s < s) && (s ≤ d0At s + 13) &&
    (2 * s < 3 * d0At s) && SkipD3.rowChk s (d0At s)

/-- Reading a single row out of a hundred-row kernel check. -/
theorem rowOk_of_chunk {b : ℕ} (hb : (List.range 100).all (fun k => rowOk (b + k)) = true)
    {s : ℕ} (h1 : b ≤ s) (h2 : s < b + 100) : rowOk s = true := by
  have hk := List.all_eq_true.mp hb (s - b) (List.mem_range.mpr (by omega))
  rwa [show b + (s - b) = s from by omega] at hk

/-! The block is checked in seven chunks of a hundred rows rather than in one
term of seven hundred: the kernel evaluation cache of a single `decide +kernel`
retains every intermediate, and one 700-row term needs many gigabytes, while each
chunk is checked in its own kernel call. -/

set_option maxRecDepth 8000000 in
theorem chunk0 : (List.range 100).all (fun k => rowOk (501 + k)) = true := by decide +kernel

set_option maxRecDepth 8000000 in
theorem chunk1 : (List.range 100).all (fun k => rowOk (601 + k)) = true := by decide +kernel

set_option maxRecDepth 8000000 in
theorem chunk2 : (List.range 100).all (fun k => rowOk (701 + k)) = true := by decide +kernel

set_option maxRecDepth 8000000 in
theorem chunk3 : (List.range 100).all (fun k => rowOk (801 + k)) = true := by decide +kernel

set_option maxRecDepth 8000000 in
theorem chunk4 : (List.range 100).all (fun k => rowOk (901 + k)) = true := by decide +kernel

set_option maxRecDepth 8000000 in
theorem chunk5 : (List.range 100).all (fun k => rowOk (1001 + k)) = true := by decide +kernel

set_option maxRecDepth 8000000 in
theorem chunk6 : (List.range 100).all (fun k => rowOk (1101 + k)) = true := by decide +kernel

/-- **The kernel check.**  All `700` rows `501, …, 1200` pass. -/
theorem rowOk_of_block {s : ℕ} (h1 : 501 ≤ s) (h2 : s ≤ 1200) : rowOk s = true := by
  rcases Nat.lt_or_ge s 601 with h | h
  · exact rowOk_of_chunk chunk0 h1 (by omega)
  rcases Nat.lt_or_ge s 701 with h' | h'
  · exact rowOk_of_chunk chunk1 h (by omega)
  rcases Nat.lt_or_ge s 801 with h'' | h''
  · exact rowOk_of_chunk chunk2 h' (by omega)
  rcases Nat.lt_or_ge s 901 with h3 | h3
  · exact rowOk_of_chunk chunk3 h'' (by omega)
  rcases Nat.lt_or_ge s 1001 with h4 | h4
  · exact rowOk_of_chunk chunk4 h3 (by omega)
  rcases Nat.lt_or_ge s 1101 with h5 | h5
  · exact rowOk_of_chunk chunk5 h4 (by omega)
  exact rowOk_of_chunk chunk6 h5 (by omega)

theorem exists_largestFalseRank_of_rowOk {s : ℕ} (h : rowOk s = true) :
    ∃ d : ℕ, IsLargestFalseRank (seamGreedyWord s) d ∧ s ≤ d + 13 ∧ 2 * s < 3 * d := by
  rw [rowOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h2, hds⟩, hnear⟩, hlate⟩, hchk⟩ := h
  exact ⟨d0At s, SkipD3.isLargestFalseRank_of_rowChk h2 hds hchk, hnear, hlate⟩

/-- **The measured top run.**  On every row of the block the greedy's run of
takes at the top has length at most `12`. -/
theorem topRun_le_twelve_block {s : ℕ} (h1 : 501 ≤ s) (h2 : s ≤ 1200) :
    ∃ d : ℕ, IsLargestFalseRank (seamGreedyWord s) d ∧ s - 1 - d ≤ 12 ∧ 2 * s < 3 * d := by
  obtain ⟨d, hmax, hnear, hlate⟩ := exists_largestFalseRank_of_rowOk (rowOk_of_block h1 h2)
  exact ⟨d, hmax, by omega, hlate⟩

theorem largestSkipLateAt_block {s : ℕ} (h1 : 501 ≤ s) (h2 : s ≤ 1200) :
    LargestSkipLateAt s := by
  obtain ⟨d, hmax, _hnear, hlate⟩ := exists_largestFalseRank_of_rowOk (rowOk_of_block h1 h2)
  exact ⟨d, hmax, hlate⟩

/-- The block, in the run language: the forced maximal run fails at every row. -/
theorem topTaken_runNeeded_false_block {s : ℕ} (h1 : 501 ≤ s) (h2 : s ≤ 1200) :
    topTaken s (runNeeded s) = false :=
  (largestSkipLateAt_iff_topTaken_false (by omega)).mp (largestSkipLateAt_block h1 h2)

/-- **The run deficit, quantified.**  On every row of the block the top take-run
falls short of the run the negative branch of `#257` needs by at least `s / 4`. -/
theorem topRun_deficit {s : ℕ} (h1 : 501 ≤ s) (h2 : s ≤ 1200) :
    ∃ d : ℕ, IsLargestFalseRank (seamGreedyWord s) d ∧
      (s - 1 - d) + s / 4 ≤ runNeeded s := by
  obtain ⟨d, hmax, hnear, _hlate⟩ := exists_largestFalseRank_of_rowOk (rowOk_of_block h1 h2)
  refine ⟨d, hmax, ?_⟩
  unfold runNeeded lateFloor
  omega

/-! ## 4. The extremal row, pinned -/

set_option maxRecDepth 8000000 in
/-- **The record run of `[5, 3000]`, exactly.**  At `s = 1148` the top twelve
ranks are selected and the thirteenth is not: the run is exactly `12`.  The
negative branch of `#257` would need `runNeeded 1148 = 382`. -/
theorem topRun_record_1148 :
    topTaken 1148 12 = true ∧ topTaken 1148 13 = false ∧ runNeeded 1148 = 382 :=
  ⟨by decide +kernel, by decide +kernel, by decide⟩

/-! ## 5. Rows far beyond the previously certified range -/

/-- Row / largest-false-rank pairs at rows well past `H4`'s highest sample
(`s = 3001`). -/
def highTable : List (ℕ × ℕ) :=
  [(3500, 3499), (4000, 3998), (4500, 4499), (5000, 4999), (6000, 5999),
    (7000, 6999), (8000, 7998)]

def pairOk (p : ℕ × ℕ) : Bool :=
  (2 ≤ p.2) && (p.2 < p.1) && (p.1 ≤ p.2 + 13) &&
    (2 * p.1 < 3 * p.2) && SkipD3.rowChk p.1 p.2

set_option maxRecDepth 8000000 in
/-- **The kernel check at scale**, up to `s = 8000`. -/
theorem highAll : ∀ p ∈ highTable, pairOk p = true :=
  List.all_eq_true.mp (by decide +kernel : highTable.all pairOk = true)

theorem largestSkipLateAt_high {s d : ℕ} (h : (s, d) ∈ highTable) : LargestSkipLateAt s := by
  have hp := highAll (s, d) h
  rw [pairOk] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨h2, hds⟩, _hnear⟩, hlate⟩, hchk⟩ := hp
  exact ⟨d, SkipD3.isLargestFalseRank_of_rowChk h2 hds hchk, hlate⟩

/-! ## 6. Non-vacuity witnesses

Concrete instances satisfying the hypotheses of every theorem above. -/

/-- `501 ≤ s ≤ 1200` is satisfiable — and the block conclusion holds there. -/
theorem largestSkipLateAt_1148 : LargestSkipLateAt 1148 :=
  largestSkipLateAt_block (by norm_num) (by norm_num)

/-- The right-hand side of `largestSkipLateAt_iff_topTaken_false` is satisfied at
a concrete row far outside the block. -/
theorem largestSkipLateAt_8000 : LargestSkipLateAt 8000 :=
  largestSkipLateAt_high (d := 7998) (by simp [highTable])

theorem topTaken_runNeeded_false_8000 : topTaken 8000 (runNeeded 8000) = false :=
  (largestSkipLateAt_iff_topTaken_false (by norm_num)).mp largestSkipLateAt_8000

theorem runNeeded_8000 : runNeeded 8000 = 2666 := by decide

/-- The body of `half_mem_iff_topRun_deficient` is satisfied at every `N ≤ 8000`:
the equivalence is not vacuous at the near end either. -/
theorem topRun_deficient_witness {N : ℕ} (hN : N ≤ 8000) :
    ∃ s : ℕ, N ≤ s ∧ topTaken s (runNeeded s) = false :=
  ⟨8000, hN, topTaken_runNeeded_false_8000⟩

end BitCorr3

end Erdos249257
