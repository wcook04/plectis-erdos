/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Skip.D1
import ErdosProblems.Skip.D3

/-!
# Angle H4: the largest false ranks, measured — and the half-band target refuted

`SkipD1.allRight_landingExcess_two_forces_halfSkip_landingRow` reduces the
all-right-tail branch of the `-2` final middle cell to a single inequality about
a single row: under an all-right tail from `D+1` the seam support is frozen, the
largest false rank of row `D+1` is frozen at some `d`, and the branch survives
exactly when

    `(D+1)/2 < d < D+1`,   i.e.   `SkipD1.LargestSkipHalfAt (D+1)`.

The programme was to *refute* that inequality — by size or by divisibility — and
so close the branch.  This file settles, by direct computation, that the
inequality cannot be refuted, because it is **true at every row that has been
looked at**.

## The measurement

For every `s` from `61` to `3001` the concrete integer seam greedy word
`seamGreedyWord s` was evaluated and its largest false rank `d₀(s)` extracted
(the greedy is `integerGreedyBits (seamWeights s) (seamSubsetTarget s)`, with
`seamWeights s` the descending list `4 ^ s / (2 ^ d - 1)` for `d = 2,…,s-1`).
The result, over all `2941` rows:

* `d₀(s)` exists at every single row — no row is fully selected;
* `s < 2 * d₀(s)` at **every** row: `d₀` is *always* in the half band;
* `2 * s < 3 * d₀(s)` at every row too: `d₀` is always in the strictly smaller
  two-thirds *late* zone, so even the stronger `LargestSkipLateAt` holds;
* the distance `s - d₀(s)` never exceeds `13`, and its distribution over the
  `2941` rows is
  `1:1442, 2:746, 3:378, 4:183, 5:92, 6:49, 7:26, 8:13, 9:6, 10:2, 11:2, 12:1, 13:1`
  — an almost exact geometric law with ratio `1/2`;
* the smallest ratio `d₀(s)/s` observed anywhere in the range is `75/81 ≈ 0.926`,
  attained at `s = 81`;
* the smallest late margin `3 * d₀(s) - 2 * s` observed on `61 ≤ s ≤ 500` is `56`.

So `d₀` does not merely clear the half boundary `s/2`, it sits within a bounded
distance of the terminal rank `s-1`.  There is no room at all for a size or
divisibility refutation of `(D+1)/2 < d₀ < D+1`: the true gap to the half
boundary is of order `s/2`, not `O(1)`.

The reason is visible in the tail weights.  For `d = s - k` with `3 * k < s` the
exact weight is `truncatedMersenneWeight s (s-k) = 2 ^ (s+k) + 2 ^ (2*k)`
(`truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank`), so the last
few ranks of the greedy behave like a binary place-value system with digits
`2^(s+1), 2^(s+2), …`.  A run of `k` consecutive selected ranks at the tail is a
run of `k` binary ones, which is what produces the geometric `2^{-k}` law and
pins `d₀` to within `O(log)` of `s`.  Pushing `d₀` down to `s/2` would require
`s/2` consecutive ones.

## What is certified here

The measurement above was performed outside the kernel.  What this file proves,
inside the kernel with `decide +kernel` and no `sorry`, `native_decide` or new
axiom, is the part that matters for the residue:

* `largestFalseRank_near_terminal` — for **every** `s` with `61 ≤ s ≤ 500`, the
  concrete greedy row has a largest false rank `d` with `s ≤ d + 8` and
  `2 * s < 3 * d`.  That is an unbroken run of `440` rows.
* `largestSkipHalfAt_landingRow` — hence `SkipD1.LargestSkipHalfAt (D+1)` holds
  **unconditionally**, with no tail hypothesis and no landing hypothesis, for
  every `D` with `60 ≤ D ≤ 499`.
* `largestSkipLateAt_high` — the same at a sample of far larger rows,
  `546, 547, 548, 630, 631, 632, 1113, 1114, 1115, 1500, 2000, 2500, 3000, 3001`.
* `largestSkipHalfAt_survivorWindow` — hence at **all twenty-one rows** of the
  three-row `AngleB2` landing windows of the seven surviving classes
  `D = 101, 122, 164, 314, 545, 629, 1112` of `SkipD3`.  (The first four lie
  inside the block; the last three are the high sample rows.)

## The consequence: a sharp negative

`no_refutation_on_block` records it: there is no `D` in `[60, 499]` at which
`LargestSkipHalfAt (D+1)` fails, so no argument refuting that inequality can be
valid on the range where the residue actually lives.  The refutation route is
dead.

**Vacuity check, stated plainly.**  This cuts both ways, and the second cut is
the more important one.  `largestSkipHalfAt_landingRow` proves the *conclusion*
of `SkipD1.allRight_landingExcess_two_forces_halfSkip_landingRow` outright, from
nothing, for all `60 ≤ D ≤ 499`.  A theorem whose conclusion is already a
theorem excludes no case.  Therefore
`SkipD1.allRight_landingExcess_two_forces_halfSkip_landingRow` — the file's own
description of it as "the real residue" notwithstanding — **excludes zero
classes on `60 ≤ D ≤ 499`**, and the sample rows show the same at every larger
row tested up to `3001`.  It is a true theorem carrying no exclusionary content
on any range that has been checked.

There is a stronger finite vacuity check on its antecedent: direct evaluation
of the corpus's concrete greedy finds `Recon257.seamExcess s ≠ 2` for every
`s ∈ [5,102]`.  Hence the landing hypothesis itself has no instance on that
range.  The certified largest-false-rank block in this file remains an
unconditional finite result; it must not be presented as repairing the
unreachable landing branch.

The adversarial verifier proves a stronger antecedent failure using this
file's row-`3001` certificate: an all-right tail cannot begin at any
`S ∈ [5,3000]`, because rank `3000` is skipped at row `3001`.  Consequently
the per-class all-right-tail premise is false for every `D ≤ 2999`.  This is a
finite theorem, not a refutation of an eventual tail starting after row
`3000`.

I could not exhibit a single `D ≥ 60` at which `LargestSkipHalfAt (D+1)` fails,
and the tail-weight heuristic above says none should exist.

## Which way the branch actually points

The measurement is not neutral.  `SkipD1.half_mem_of_cofinal_largestSkipHalfAt`
says that half-band largest skips at *cofinally many* rows already give
`1/2 ∈ mersenneAchievementSet`.  The measurement says the half-band skip fires
at **every** row from `61` to `3001` without exception.
`half_mem_of_eventually_largestSkipHalfAt` below packages the implication, and
`largestSkipHalfAt_block` verifies its hypothesis on `[61, 500]`.  The live
target is therefore not a refutation of the half band but a *proof* that the
largest false rank stays near the terminal rank — for instance, an unconditional
`s ≤ d₀(s) + c`, or merely `s < 2 * d₀(s)`, for all large `s`.
-/

namespace Erdos249257

namespace SkipH4

open HalfCylinderIntegerGreedy

noncomputable section

/-! ## 1. The measured block, rows `61` to `500` -/

/-- The measured largest false rank of row `61 + k`, for `k < 440`.  Each entry
is certified below by `SkipD3.rowChk`, which checks that the rank's greedy bit
is off and every greedy bit above it, up to the terminal rank `s-1`, is on. -/
def d0Table : List ℕ :=
[  60, 60, 62, 63, 64, 64, 66, 66, 66, 69, 70, 70, 70, 73, 73, 75, 75, 75, 75, 75, 75, 81, 82,
  82, 82, 85, 85, 87, 88, 89, 90, 91, 92, 93, 93, 95, 96, 97, 97, 97, 100, 101, 101, 101, 104,
  104, 106, 106, 108, 108, 108, 108, 112, 113, 113, 113, 113, 113, 113, 113, 113, 121, 121,
  123, 124, 124, 126, 126, 126, 129, 130, 130, 132, 133, 134, 135, 136, 137, 137, 137, 137,
  141, 141, 141, 144, 144, 144, 144, 144, 149, 149, 149, 149, 149, 149, 155, 155, 155, 158,
  158, 160, 160, 162, 162, 162, 165, 166, 166, 168, 168, 168, 168, 168, 173, 174, 174, 174,
  174, 174, 174, 174, 181, 181, 183, 184, 185, 186, 187, 188, 189, 189, 189, 192, 192, 192,
  192, 196, 196, 198, 199, 200, 201, 202, 202, 204, 204, 204, 204, 208, 209, 209, 209, 212,
  213, 213, 215, 215, 215, 218, 218, 220, 221, 221, 221, 224, 225, 225, 227, 227, 227, 230,
  230, 230, 233, 233, 235, 235, 235, 235, 239, 240, 240, 242, 242, 244, 244, 244, 247, 248,
  248, 250, 251, 251, 253, 254, 254, 254, 257, 257, 257, 260, 260, 262, 262, 262, 262, 266,
  267, 268, 268, 270, 271, 272, 273, 273, 273, 276, 276, 276, 276, 276, 281, 282, 282, 282,
  285, 286, 287, 287, 287, 290, 291, 291, 293, 294, 295, 296, 296, 296, 299, 299, 301, 301,
  301, 304, 304, 306, 307, 308, 308, 308, 308, 312, 312, 314, 315, 316, 317, 318, 319, 319,
  321, 321, 323, 323, 325, 325, 325, 325, 325, 325, 331, 332, 333, 334, 334, 336, 336, 336,
  336, 340, 341, 342, 342, 344, 345, 346, 346, 346, 346, 350, 351, 351, 353, 354, 354, 356,
  357, 358, 359, 360, 360, 360, 360, 360, 365, 365, 365, 365, 369, 370, 371, 372, 373, 373,
  373, 376, 376, 376, 376, 376, 381, 382, 382, 382, 385, 385, 387, 388, 389, 389, 389, 389,
  393, 394, 394, 394, 397, 397, 397, 400, 401, 402, 402, 404, 404, 406, 406, 406, 406, 406,
  406, 406, 413, 414, 415, 415, 415, 415, 415, 415, 421, 422, 422, 422, 425, 426, 426, 428,
  428, 428, 431, 432, 433, 433, 433, 436, 436, 438, 438, 438, 438, 442, 443, 444, 445, 446,
  447, 448, 449, 450, 450, 450, 453, 454, 454, 454, 457, 457, 459, 460, 460, 462, 462, 462,
  462, 466, 466, 466, 469, 469, 471, 472, 472, 474, 475, 475, 477, 477, 479, 480, 480, 482,
  483, 483, 485, 486, 487, 487, 487, 490, 490, 490, 493, 494, 494, 494, 497, 498, 498]

/-- Lookup into `d0Table`. -/
def d0At (s : ℕ) : ℕ := d0Table.getD (s - 61) 0

/-- The row certificate: the tabulated rank is a genuine rank, lies within `8`
of the row index, is in the two-thirds late zone, and really is the largest
false rank of the concrete greedy row. -/
def rowOk (s : ℕ) : Bool :=
  (2 ≤ d0At s) && (d0At s < s) && (s ≤ d0At s + 8) &&
    (2 * s < 3 * d0At s) && SkipD3.rowChk s (d0At s)

set_option maxRecDepth 8000000 in
/-- **The kernel check.**  All `440` rows `61,…,500` pass. -/
theorem blockAll : ∀ k ∈ List.range 440, rowOk (61 + k) = true :=
  List.all_eq_true.mp
    (by decide +kernel : (List.range 440).all (fun k => rowOk (61 + k)) = true)

theorem rowOk_of_block {s : ℕ} (h1 : 61 ≤ s) (h2 : s ≤ 500) : rowOk s = true := by
  have hk := blockAll (s - 61) (List.mem_range.mpr (by omega))
  rwa [show 61 + (s - 61) = s from by omega] at hk

/-- Unpacking a row certificate. -/
theorem exists_largestFalseRank_of_rowOk {s : ℕ} (h : rowOk s = true) :
    ∃ d : ℕ, IsLargestFalseRank (seamGreedyWord s) d ∧ s ≤ d + 8 ∧ 2 * s < 3 * d := by
  rw [rowOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h2, hds⟩, hnear⟩, hlate⟩, hchk⟩ := h
  exact ⟨d0At s, SkipD3.isLargestFalseRank_of_rowChk h2 hds hchk, hnear, hlate⟩

/-! ## 2. The certified statement about the block -/

/-- **The measurement, kernel-certified.**  On every row from `61` to `500` the
concrete integer seam greedy has a largest false rank lying within `8` of the
row index — and in particular deep inside the two-thirds late zone, hence far
above the half boundary `s / 2`. -/
theorem largestFalseRank_near_terminal {s : ℕ} (h1 : 61 ≤ s) (h2 : s ≤ 500) :
    ∃ d : ℕ, IsLargestFalseRank (seamGreedyWord s) d ∧ s ≤ d + 8 ∧ 2 * s < 3 * d :=
  exists_largestFalseRank_of_rowOk (rowOk_of_block h1 h2)

/-- The two-thirds form. -/
theorem largestSkipLateAt_block {s : ℕ} (h1 : 61 ≤ s) (h2 : s ≤ 500) :
    LargestSkipLateAt s := by
  obtain ⟨d, hmax, _hnear, hlate⟩ := largestFalseRank_near_terminal h1 h2
  exact ⟨d, hmax, hlate⟩

/-- The half form — the exact proposition `SkipD1` leaves as the residue. -/
theorem largestSkipHalfAt_block {s : ℕ} (h1 : 61 ≤ s) (h2 : s ≤ 500) :
    SkipD1.LargestSkipHalfAt s :=
  SkipD1.largestSkipHalfAt_of_largestSkipLateAt (largestSkipLateAt_block h1 h2)

/-! ## 3. Far larger rows, including the three surviving classes above the block -/

/-- Sample rows well beyond the block, with their measured largest false ranks.
The rows `546,547,548`, `630,631,632` and `1113,1114,1115` are the three-row
`AngleB2` landing windows of the surviving classes `D = 545, 629, 1112`; the
rest are spot checks up to `s = 3001`. -/
def highTable : List (ℕ × ℕ) :=
[  (546, 545), (547, 546), (548, 546), (630, 628), (631, 630), (632, 630),
  (1113, 1111), (1114, 1113), (1115, 1114), (1500, 1499), (2000, 1999),
  (2500, 2499), (3000, 2996), (3001, 3000)]

def pairOk (p : ℕ × ℕ) : Bool :=
  (2 ≤ p.2) && (p.2 < p.1) && (p.1 ≤ p.2 + 8) &&
    (2 * p.1 < 3 * p.2) && SkipD3.rowChk p.1 p.2

set_option maxRecDepth 8000000 in
/-- **The kernel check at scale.**  Every sampled high row passes, up to
`s = 3001`. -/
theorem highAll : ∀ p ∈ highTable, pairOk p = true :=
  List.all_eq_true.mp (by decide +kernel : highTable.all pairOk = true)

theorem largestFalseRank_near_terminal_high {s d : ℕ} (h : (s, d) ∈ highTable) :
    IsLargestFalseRank (seamGreedyWord s) d ∧ s ≤ d + 8 ∧ 2 * s < 3 * d := by
  have hp := highAll (s, d) h
  rw [pairOk] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨h2, hds⟩, hnear⟩, hlate⟩, hchk⟩ := hp
  exact ⟨SkipD3.isLargestFalseRank_of_rowChk h2 hds hchk, hnear, hlate⟩

theorem largestSkipLateAt_high {s d : ℕ} (h : (s, d) ∈ highTable) :
    LargestSkipLateAt s := by
  obtain ⟨hmax, _hnear, hlate⟩ := largestFalseRank_near_terminal_high h
  exact ⟨d, hmax, hlate⟩

theorem largestSkipHalfAt_high {s d : ℕ} (h : (s, d) ∈ highTable) :
    SkipD1.LargestSkipHalfAt s :=
  SkipD1.largestSkipHalfAt_of_largestSkipLateAt (largestSkipLateAt_high h)

/-- Explicitly: the largest false rank of row `3001` is `3000`, one below the
terminal rank, nowhere near `1500`. -/
theorem largestSkipHalfAt_3001 : SkipD1.LargestSkipHalfAt 3001 :=
  largestSkipHalfAt_high (d := 3000) (by decide)

/-- **All twenty-one rows of the seven surviving classes.**  `SkipD3` isolates
`D = 101, 122, 164, 314, 545, 629, 1112` as the classes below `1370` on which
the true below-pulse orbit stays positive to depth `25`.  At every row of every
one of their three-row `AngleB2` landing windows, the largest false rank sits in
the half band.  So the half-band residue is live on all seven — it excludes none
of them. -/
theorem largestSkipHalfAt_survivorWindow {D s : ℕ}
    (hD : D = 101 ∨ D = 122 ∨ D = 164 ∨ D = 314 ∨ D = 545 ∨ D = 629 ∨ D = 1112)
    (h1 : D + 1 ≤ s) (h2 : s < D + 4) :
    SkipD1.LargestSkipHalfAt s := by
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact largestSkipHalfAt_block (by omega) (by omega)
  · exact largestSkipHalfAt_block (by omega) (by omega)
  · exact largestSkipHalfAt_block (by omega) (by omega)
  · exact largestSkipHalfAt_block (by omega) (by omega)
  · interval_cases s
    · exact largestSkipHalfAt_high (d := 545) (by decide)
    · exact largestSkipHalfAt_high (d := 546) (by decide)
    · exact largestSkipHalfAt_high (d := 546) (by decide)
  · interval_cases s
    · exact largestSkipHalfAt_high (d := 628) (by decide)
    · exact largestSkipHalfAt_high (d := 630) (by decide)
    · exact largestSkipHalfAt_high (d := 630) (by decide)
  · interval_cases s
    · exact largestSkipHalfAt_high (d := 1111) (by decide)
    · exact largestSkipHalfAt_high (d := 1113) (by decide)
    · exact largestSkipHalfAt_high (d := 1114) (by decide)

/-! ## 4. The sharp negative -/

/-- **The residue holds unconditionally on the whole checked block.**  For every
`D` from `60` to `499`, `SkipD1.LargestSkipHalfAt (D+1)` is a theorem — with no
all-right-tail hypothesis and no landing hypothesis. -/
theorem largestSkipHalfAt_landingRow (D : ℕ) (hD : 60 ≤ D) (hD' : D ≤ 499) :
    SkipD1.LargestSkipHalfAt (D + 1) :=
  largestSkipHalfAt_block (by omega) (by omega)

/-- **The target inequality is not refutable.**  There is no `D` in the checked
range at which `LargestSkipHalfAt (D+1)` fails, so no size or divisibility
argument refuting it can be sound on that range. -/
theorem no_refutation_on_block :
    ¬ ∃ D : ℕ, 60 ≤ D ∧ D ≤ 499 ∧ ¬ SkipD1.LargestSkipHalfAt (D + 1) := by
  rintro ⟨D, hD, hD', hcon⟩
  exact hcon (largestSkipHalfAt_landingRow D hD hD')

/-- The global form: the refutation programme, as a universally quantified
statement over all `D ≥ 60`, is false. -/
theorem not_forall_not_largestSkipHalfAt_landingRow :
    ¬ ∀ D : ℕ, 60 ≤ D → ¬ SkipD1.LargestSkipHalfAt (D + 1) := by
  intro h
  exact h 60 le_rfl (largestSkipHalfAt_landingRow 60 le_rfl (by norm_num))

/-- **The vacuity statement, made formal.**  The conclusion of
`SkipD1.allRight_landingExcess_two_forces_halfSkip_landingRow` follows from its
hypotheses *and also* from nothing at all, on the entire checked range.  So on
`60 ≤ D ≤ 499` that theorem is exclusion-free: it rules out no class. -/
theorem allRight_landingRow_conclusion_is_unconditional
    (D : ℕ) (hD : 60 ≤ D) (hD' : D ≤ 499) :
    (∀ _h : (∀ s : ℕ, D + 1 ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true),
      ∀ _h' : Recon257.seamExcess (D + 1) = 2,
        SkipD1.LargestSkipHalfAt (D + 1)) ∧
      SkipD1.LargestSkipHalfAt (D + 1) :=
  ⟨fun hright hlanding =>
      SkipD1.allRight_landingExcess_two_forces_halfSkip_landingRow D hD hright hlanding,
    largestSkipHalfAt_landingRow D hD hD'⟩

/-! ## 5. Which way the branch points -/

/-- If the measured pattern persists to every row — the largest false rank stays
above half the row — then `1/2 ∈ mersenneAchievementSet`, by
`SkipD1.half_mem_of_cofinal_largestSkipHalfAt`.  The hypothesis is verified
above on `[61, 500]` (`largestSkipHalfAt_block`) and at every sampled row up to
`3001` (`largestSkipHalfAt_high`). -/
theorem half_mem_of_eventually_largestSkipHalfAt
    (h : ∀ s : ℕ, 61 ≤ s → SkipD1.LargestSkipHalfAt s) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  SkipD1.half_mem_of_cofinal_largestSkipHalfAt
    (fun B => ⟨max B 61, le_max_left _ _, h _ (le_max_right _ _)⟩)

/-- The same from the weaker, purely quantitative hypothesis that the largest
false rank stays within a bounded distance of the terminal rank — which is what
the measurement actually exhibits, with the constant `8` on the whole block. -/
theorem half_mem_of_largestFalseRank_near_terminal
    (c : ℕ)
    (h : ∀ s : ℕ, 61 ≤ s →
      ∃ d : ℕ, IsLargestFalseRank (seamGreedyWord s) d ∧ s ≤ d + c) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  refine SkipD1.half_mem_of_cofinal_largestSkipHalfAt (fun B => ?_)
  set s := max B (2 * c + 61) with hs
  have hBs : B ≤ s := le_max_left _ _
  have hcs : 2 * c + 61 ≤ s := le_max_right _ _
  obtain ⟨d, hmax, hnear⟩ := h s (by omega)
  exact ⟨s, hBs, ⟨d, hmax, by omega⟩⟩

end

end SkipH4

end Erdos249257
