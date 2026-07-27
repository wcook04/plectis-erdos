/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Decl.D4

/-!
# H2 — `hlow` is false, its failure set is `{(7,5)}`, and a failure is a *win*

The brief was: decide whether `T4`'s remaining side condition

    hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)

is true, and report its exact failure set over `s ∈ [6, 3000]` — at the first
late rank of each row, and separately at **all** late ranks.

## Answer, up front, with due credit

`hlow` is **false**, and this was already settled: `ErdosProblems/Decl/D4.lean`
proves `DeclD4.Seven.not_hlow_seven_five` — at `s = 7`, first late rank `d = 5`,
`lateEntryRemainder 7 5 = 263`, `263 % 2 ^ 8 = 7`, `lateCorrection 7 5 = 20`.
Nothing in this file re-proves that; it is imported and used.  This file records
(i) a scan extended to all late ranks and to `s ≤ 3000`, (ii) a theorem that
makes the all-ranks scan a consequence of the first-rank case, and (iii) a
sharper quantitative form of the already available fact that an `hlow` failure
is a hit certificate.

## What is proved here

**§1–2, propagation (`hlow_mono`).**  If `hlow` holds at a late rank `d` of row
`s`, it holds at *every* rank `e ∈ [d, s]`.  Both greedy branches preserve it:
a declined rank leaves the remainder alone while the budget shrinks, and a taken
rank removes `2 ^ (2*s-d) + 4 ^ (s-d)`, of which the leading term is a multiple
of `2 ^ (s+1)` and the correction is exactly the amount the budget drops by, with
no borrow out of the low block (`BitCorr.mod_sub_of_le_mod`).  The rank
recurrence `lateEntryRemainder_succ` needed for this is re-proved here from
`DeclD4.lateEntryRemainder_eq_seamResidualUpto`; the same recurrence already
appears as `DeclD3.lateEntryRemainder_succ`.

Consequences: `not_hlow_of_not_hlow_ge` — the failure set of `hlow` inside a row
is an **initial segment** of the late ranks; and `exists_not_hlow_iff` —
`hlow` fails *somewhere* in row `s` iff it fails at the *first* late rank.  So
`D4`'s first-late-rank scan was already complete, and the all-late-ranks scan
below could not have found anything new.  That is a theorem, not a hope.

**§3, what `hlow` actually says (`hlow_iff_skipCorrection_le_seamRemainder`).**
Define `skipCorrection s C d` as `∑ 4 ^ (s - e)` over the late ranks `e ≥ d`
whose bit `2*s - e` of `C` is **clear** — the ranks the late greedy declines.  It
is complementary to `DeclD4.bitCorrection`
(`skipCorrection_add_bitCorrection`).  Then at any `DeclD4.BitAdmissible` rank,

    hlow  ⟺  skipCorrection s (lateEntryRemainder s d) d ≤ ρ s .

`hlow` is not a bit-level technicality at all: it is exactly a **lower bound on
the seam remainder**.  It follows from `DeclD4.seamRemainder_eq_mod_sub`, the
exact identity `ρ s = R % 2 ^ (s+1) − bitCorrection s R d`.

**§4, the inversion.**  Since `skipCorrection ≤ lateCorrection < 2 ^ (2(s-d)+1)`
and `2*(s-d)+1 ≤ d ≤ s` in the late zone, a failure of `hlow` at a
`BitAdmissible` rank forces

    ρ s < skipCorrection s R d ≤ lateCorrection s d < 2 ^ s

(`seamRemainder_lt_skipCorrection_of_not_hlow`,
`seamRemainder_lt_two_pow_of_not_hlow`).  So **`hlow` can only fail on rows that
are half-point hits**, and its failure proves the hit.  The hit conclusion is
also a short corollary of `DeclD4.testBit_false_of_not_hlow` and the bit
criterion already proved in `Decl/D4`; the additional content here is the
explicit upper bound by `skipCorrection`.
`half_mem_of_not_hlow_cofinally` states the reduction: cofinally many
`BitAdmissible` failures of `hlow` would answer `#257`'s `1/2` question
positively.  `hlow` was being treated as a lemma to prove; the programme should
want it to be false as often as possible.

Be clear about what that is worth: the hypothesis of
`half_mem_of_not_hlow_cofinally` is measured to be violently false — one row in
`[6, 3000]`.  **Nothing here resolves Erdős #257.**  It is also weaker than it
sounds, since `DeclD4.testBit_false_of_not_hlow` + `DeclD4`'s bit criterion give
`ρ s < 2 ^ s` from `¬ hlow` by another route; §4's contribution is the sharper
constant `skipCorrection` and the `iff` that explains why.

**§5, examples.**  The principal `hlow`, `¬ hlow`, and `BitAdmissible`
hypotheses are discharged on the corpus object.  `hlow_mono`'s hypothesis holds
at `(20, 14)` (`BitCorr.Concrete`) and at `(7,6)`
(`DeclD4`), giving the new facts `hlow_twenty_seventeen` and `hlow_twenty_all`;
`row_seven_failure_set` proves the failure set of row `7` is exactly `{5}`;
`seven_sharp_value` gives `ρ 7 < 16` from the failure, cross-checked against
`DeclD4`'s `ρ 7 = 3`; and both directions of the §3 `iff` are witnessed
(`skipCorrection_le_seamRemainder_twenty`,
`not_skipCorrection_le_seamRemainder_seven`).  This section does not separately
instantiate `not_hlow_of_not_hlow_ge` or `exists_not_hlow_iff`; the former has
only the diagonal instance in the measured range because the sole failure is
already at the first late rank.

## Measured, not proved — independently re-run

Two implementations were written from the corpus definitions and cross-checked
against each other: one taking `truncatedMersenneWeight s d = 4 ^ s / (2 ^ d - 1)`
and the recursive `lateCorrection`, the other taking the divisor-indicator sum
`∑_{j < 2s-1} [d ∣ j+2] · 2 ^ (2s-2-j)` and the closed form
`3 · lateCorrection + 4 = 4 · 4 ^ (s-d)`.  Both were checked against the corpus's
own certified values (`lateEntryRemainder 20 14 = 67662313`,
`lateCorrection 20 14 = 5460`, `lateEntryRemainder 7 5 = 263`, `ρ 20 = 549353`,
`ρ 7 = 3`).  They agree everywhere tested: fully on `[6, 700]` and at
`s = 997, 1000, 1500, 2000, 2500, 2999, 3000`.

* **`s ∈ [6, 3000]`, first late rank `d₀ = ⌊2s/3⌋ + 1`.  Failure set = `{7}`.**
  Exactly one row, `(s, d) = (7, 5)`.  This reproduces `D4`'s `[6, 2200]` scan
  and extends it.
* **`s ∈ [6, 3000]`, ALL late ranks `d ∈ (2s/3, s]`.  Failure set = `{(7, 5)}`.**
  The same single pair — no row fails at a non-first late rank.  By
  `exists_not_hlow_iff` this had to be so.
* At the first late rank, the smallest surviving margin is `30`, at
  `(s, d) = (6, 5)`.  Across all late ranks, the smallest is `3`, at `(7, 6)`.
  The margin at `(14, 10)` is `52`:
  `lateCorrection 14 10 = 340` and
  `lateEntryRemainder 14 10 % 2 ^ 15 = 392`.  Equal binary length occurs at
  both `(7, 5)` and `(7, 6)`, not only at one pair.  Ranked by ratio
  `low / corr` at the first late rank, the tightest rows are
  `s = 7` (`0.35`, the failure), `s = 14` (`1.153`), `s = 6` (`8.5`),
  `s = 10` (`13.75`), `s = 8` (`14.05`), `s = 21` (`18.36`).  Only **two** rows
  in `[6, 3000]` come within a factor `4`, and only **five** within a factor `16`.
* Tightest *relative* margin `(low − corr) / 2 ^ (s+1)`: `0.000811` at
  `(s, d) = (502, 335)`.
* Heuristically the budget is `≈ (4/3) · 2 ^ (2s/3)` against a low block
  equidistributed in `[0, 2 ^ (s+1))`, so the expected number of further failures
  beyond `s = 3000` is about `3 · 10 ^ (-302)`.  That is a heuristic, not a
  proof: `hlow` is false, and no scan can show it becomes true.

None of the above is used in any proof below.

Checked with `lake env lean ErdosProblems/Hlow/H2.lean` (exit `0`, empty output).
No `sorry`, no `axiom`, no `native_decide`.
-/

namespace ErdosProblems.HlowH2

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open Erdos249257.BitCorr
open ErdosProblems.DeclD4

/-! ## 1. The rank recurrence for the entering remainder -/

theorem lateEntryRemainder_succ {s d : ℕ} (h2 : 2 ≤ d) (hds : d < s) :
    lateEntryRemainder s (d + 1) =
      if truncatedMersenneWeight s d ≤ lateEntryRemainder s d then
        lateEntryRemainder s d - truncatedMersenneWeight s d
      else
        lateEntryRemainder s d := by
  rw [lateEntryRemainder_eq_seamResidualUpto (by omega) (by omega),
    lateEntryRemainder_eq_seamResidualUpto h2 (by omega)]
  have hkey := Three.T1.seamResidualUpto_succ (s := s) (d := d - 1) (by omega)
  rw [show d - 1 + 1 = d by omega] at hkey
  rw [show d + 1 - 1 = d by omega]
  exact hkey

/-! ## 2. `hlow` propagates upward in the rank -/

/-- Subtracting a multiple of the modulus leaves the residue alone. -/
theorem sub_mul_mod_self {A M t : ℕ} (h : M * t ≤ A) : (A - M * t) % M = A % M := by
  conv_rhs => rw [show A = A - M * t + M * t by omega]
  rw [Nat.add_mul_mod_self_left]

theorem hlow_succ_of_hlow {s d : ℕ} (h2 : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d)
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)) :
    lateCorrection s (d + 1) ≤ lateEntryRemainder s (d + 1) % 2 ^ (s + 1) := by
  have hcorr := lateCorrection_eq_cons (s := s) (d := d) hds
  have hw := truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank h2 hds hlate
  have hrec := lateEntryRemainder_succ h2 hds
  by_cases htake : truncatedMersenneWeight s d ≤ lateEntryRemainder s d
  · rw [if_pos htake] at hrec
    obtain ⟨t, ht⟩ : (2 : ℕ) ^ (s + 1) ∣ 2 ^ (2 * s - d) := pow_dvd_pow 2 (by omega)
    have hge : 2 ^ (2 * s - d) ≤ lateEntryRemainder s d :=
      le_trans (by rw [hw]; exact Nat.le_add_right _ _) htake
    have hHle : 2 ^ (s + 1) * t ≤ lateEntryRemainder s d := ht ▸ hge
    have hstep1 : (lateEntryRemainder s d - 2 ^ (2 * s - d)) % 2 ^ (s + 1)
        = lateEntryRemainder s d % 2 ^ (s + 1) := by
      rw [ht]; exact sub_mul_mod_self hHle
    have hFle : 4 ^ (s - d) ≤ (lateEntryRemainder s d - 2 ^ (2 * s - d)) % 2 ^ (s + 1) := by
      rw [hstep1]
      exact le_trans (by rw [hcorr]; exact Nat.le_add_right _ _) hlow
    have hstep2 := mod_sub_of_le_mod (P := 2 ^ (s + 1)) (X := 4 ^ (s - d))
      (A := lateEntryRemainder s d - 2 ^ (2 * s - d)) (Nat.two_pow_pos _) hFle
    have hsplit : lateEntryRemainder s d - truncatedMersenneWeight s d
        = lateEntryRemainder s d - 2 ^ (2 * s - d) - 4 ^ (s - d) := by
      rw [hw, Nat.sub_sub]
    rw [hrec, hsplit, hstep2, hstep1]
    exact Nat.le_sub_of_add_le (by rw [Nat.add_comm, ← hcorr]; exact hlow)
  · rw [if_neg htake] at hrec
    rw [hrec]
    exact le_trans (lateCorrection_succ_le s d) hlow

/-- **`hlow` is upward closed in the rank.**  If the `T4` low-side condition holds
at a late rank `d` of row `s`, it holds at *every* rank from `d` to `s`. -/
theorem hlow_mono {s d : ℕ} (h2 : 2 ≤ d) (hlate : 2 * s < 3 * d)
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)) :
    ∀ e : ℕ, d ≤ e → e ≤ s →
      lateCorrection s e ≤ lateEntryRemainder s e % 2 ^ (s + 1) := by
  intro e hde
  induction e, hde using Nat.le_induction with
  | base => intro _; exact hlow
  | succ e hde ih =>
      intro hes
      exact hlow_succ_of_hlow (by omega) (by omega) (by omega) (ih (by omega))

/-- **The failure set of `hlow` inside a row is an initial segment of the late
ranks.**  Contrapositive of `hlow_mono`: a failure at any late rank `e` forces a
failure at every late rank below it — in particular at the *first* late rank. -/
theorem not_hlow_of_not_hlow_ge {s d e : ℕ} (h2 : 2 ≤ d) (hlate : 2 * s < 3 * d)
    (hde : d ≤ e) (hes : e ≤ s)
    (hfail : ¬ (lateCorrection s e ≤ lateEntryRemainder s e % 2 ^ (s + 1))) :
    ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)) :=
  fun hlow => hfail (hlow_mono h2 hlate hlow e hde hes)

/-- **Scanning the first late rank is complete.** -/
theorem exists_not_hlow_iff {s d₀ : ℕ} (h2 : 2 ≤ d₀) (hd0s : d₀ ≤ s) (hlate : 2 * s < 3 * d₀) :
    (∃ e : ℕ, d₀ ≤ e ∧ e ≤ s ∧
        ¬ (lateCorrection s e ≤ lateEntryRemainder s e % 2 ^ (s + 1))) ↔
      ¬ (lateCorrection s d₀ ≤ lateEntryRemainder s d₀ % 2 ^ (s + 1)) := by
  constructor
  · rintro ⟨e, hde, hes, hfail⟩
    exact not_hlow_of_not_hlow_ge h2 hlate hde hes hfail
  · intro hfail
    exact ⟨d₀, le_rfl, hd0s, hfail⟩

/-! ## 3. What `hlow` actually says: a lower bound on `ρ s` -/

/-- The correction the greedy does **not** incur: `∑ 4 ^ (s - e)` over the late
ranks `e ∈ [d, s)` whose bit `2 * s - e` of `C` is *clear*, i.e. the ranks the
late greedy declines.  Complementary to `DeclD4.bitCorrection`. -/
def skipCorrection (s C : ℕ) : ℕ → ℕ
  | d =>
      if h : d < s then
        (if Nat.testBit C (2 * s - d) then 0 else 4 ^ (s - d)) + skipCorrection s C (d + 1)
      else 0
termination_by d => s - d
decreasing_by omega

theorem skipCorrection_eq_zero {s C d : ℕ} (h : s ≤ d) : skipCorrection s C d = 0 := by
  rw [skipCorrection]
  simp [Nat.not_lt.mpr h]

theorem skipCorrection_eq_cons {s C d : ℕ} (h : d < s) :
    skipCorrection s C d =
      (if Nat.testBit C (2 * s - d) then 0 else 4 ^ (s - d)) + skipCorrection s C (d + 1) := by
  rw [skipCorrection]
  simp [h]

/-- Skipped plus taken is everything. -/
theorem skipCorrection_add_bitCorrection (s C d : ℕ) :
    skipCorrection s C d + bitCorrection s C d = lateCorrection s d := by
  by_cases hds : d < s
  · rw [skipCorrection_eq_cons hds, bitCorrection_eq_cons hds, lateCorrection_eq_cons hds]
    have ih := skipCorrection_add_bitCorrection s C (d + 1)
    obtain ⟨F, hF⟩ : ∃ F : ℕ, (4 : ℕ) ^ (s - d) = F := ⟨_, rfl⟩
    rw [hF]
    split_ifs <;> omega
  · rw [skipCorrection_eq_zero (by omega), bitCorrection_eq_zero (by omega),
      lateCorrection_eq_zero (by omega)]
termination_by s - d
decreasing_by omega

theorem skipCorrection_le_lateCorrection (s C d : ℕ) :
    skipCorrection s C d ≤ lateCorrection s d := by
  have := skipCorrection_add_bitCorrection s C d
  omega

/-- **`hlow` is exactly a lower bound on the seam remainder.**  At a
`BitAdmissible` late rank, `T4`'s low-side condition holds if and only if `ρ s`
is at least the `4 ^ k` budget of the late ranks the greedy *declines*. -/
theorem hlow_iff_skipCorrection_le_seamRemainder {s d : ℕ} (h : BitAdmissible s d) :
    (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)) ↔
      skipCorrection s (lateEntryRemainder s d) d ≤ seamIntegerGreedyRemainder s := by
  have hid := seamRemainder_eq_mod_sub h
  have hpay := h.2.2.2.2
  have hsum := skipCorrection_add_bitCorrection s (lateEntryRemainder s d) d
  omega

/-! ## 4. A failure of `hlow` is a half-point hit certificate -/

/-- **The sharp form.**  Where `hlow` fails at a `BitAdmissible` rank, `ρ s` is
strictly below the declined-rank budget. -/
theorem seamRemainder_lt_skipCorrection_of_not_hlow {s d : ℕ} (h : BitAdmissible s d)
    (hfail : ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))) :
    seamIntegerGreedyRemainder s < skipCorrection s (lateEntryRemainder s d) d := by
  by_contra hcon
  exact hfail ((hlow_iff_skipCorrection_le_seamRemainder h).mpr (by omega))

/-- **Every failure of `hlow` certifies a hit.**  `hlow` is not an obstruction
to be feared: at a `BitAdmissible` late rank its failure *proves* `ρ s < 2 ^ s`,
which is exactly the half-point condition `BitR2` consumes. -/
theorem seamRemainder_lt_two_pow_of_not_hlow {s d : ℕ} (h : BitAdmissible s d)
    (hfail : ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))) :
    seamIntegerGreedyRemainder s < 2 ^ s := by
  obtain ⟨-, hds, hlate, -, -⟩ := id h
  have hlt := seamRemainder_lt_skipCorrection_of_not_hlow h hfail
  have hle := skipCorrection_le_lateCorrection s (lateEntryRemainder s d) d
  have hbound := lateCorrection_lt_two_pow_two_mul (s := s) (d := d) hds
  have hmono : (2 : ℕ) ^ (2 * (s - d) + 1) ≤ 2 ^ s :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem seamRemainder_le_two_pow_of_not_hlow {s d : ℕ} (h : BitAdmissible s d)
    (hfail : ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))) :
    seamIntegerGreedyRemainder s ≤ 2 ^ s :=
  le_of_lt (seamRemainder_lt_two_pow_of_not_hlow h hfail)

/-- **The inversion, stated as a reduction.**  If `hlow` failed at
`BitAdmissible` ranks of arbitrarily large rows, Erdős `#257`'s `1/2` question
would be answered positively.  `hlow` is therefore not a lemma whose proof is
wanted: its *failure* is what the programme is looking for.

This is a conditional, and the condition is measured to be badly false — the
failure set over `s ∈ [6, 3000]` is the single row `7` (see the header).  Nothing
here resolves anything. -/
theorem half_mem_of_not_hlow_cofinally
    (h : ∀ N : ℕ, ∃ s d : ℕ, N ≤ s ∧ 5 ≤ s ∧ BitAdmissible s d ∧
      ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  refine ErdosProblems.BitR2.half_mem_of_remainderReachesHalfPointCofinally ?_
  intro N
  obtain ⟨s, d, hNs, hs5, hadm, hfail⟩ := h N
  exact ⟨s, hNs, hs5, seamRemainder_le_two_pow_of_not_hlow hadm hfail⟩

/-! ## 5. Non-vacuity

Every theorem above carries a non-trivial hypothesis, and every one of them is
discharged here on the corpus's own object. -/

namespace Concrete

/-! ### `hlow_mono`: the hypothesis holds, and the conclusion is new -/

/-- `hlow` at the first late rank of row `20`, from `BitCorr`'s own certificate. -/
theorem hlow_twenty_fourteen :
    lateCorrection 20 14 ≤ lateEntryRemainder 20 14 % 2 ^ (20 + 1) :=
  BitCorr.Concrete.actual_hypotheses_hold.2

/-- **Propagation, applied.**  `hlow` at rank `17` of row `20` — a fact not in
the corpus, obtained from rank `14` purely by `hlow_mono`, with no further
computation. -/
theorem hlow_twenty_seventeen :
    lateCorrection 20 17 ≤ lateEntryRemainder 20 17 % 2 ^ (20 + 1) :=
  hlow_mono (d := 14) (by norm_num) (by norm_num) hlow_twenty_fourteen 17
    (by norm_num) (by norm_num)

/-- The same at every remaining late rank of row `20`. -/
theorem hlow_twenty_all (e : ℕ) (he : 14 ≤ e) (hes : e ≤ 20) :
    lateCorrection 20 e ≤ lateEntryRemainder 20 e % 2 ^ (20 + 1) :=
  hlow_mono (d := 14) (by norm_num) (by norm_num) hlow_twenty_fourteen e he hes

/-! ### Row `7`: the exact failure set, as a theorem

`DeclD4` proves `hlow` fails at rank `5` and holds at rank `6`.  `hlow_mono`
turns those two facts into the *complete* picture for the row: the failure set of
row `7` is exactly `{5}`, and no computation at rank `7` is needed. -/

theorem hlow_seven_six : lateCorrection 7 6 ≤ lateEntryRemainder 7 6 % 2 ^ (7 + 1) :=
  DeclD4.Seven.admissible_seven_six.2.2.2.2

theorem hlow_seven_seven : lateCorrection 7 7 ≤ lateEntryRemainder 7 7 % 2 ^ (7 + 1) :=
  hlow_mono (d := 6) (by norm_num) (by norm_num) hlow_seven_six 7 (by norm_num) (by norm_num)

/-- **The failure set of row `7` is exactly `{5}`.** -/
theorem row_seven_failure_set :
    ¬ (lateCorrection 7 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1)) ∧
      (lateCorrection 7 6 ≤ lateEntryRemainder 7 6 % 2 ^ (7 + 1)) ∧
      (lateCorrection 7 7 ≤ lateEntryRemainder 7 7 % 2 ^ (7 + 1)) :=
  ⟨DeclD4.Seven.not_hlow_seven_five, hlow_seven_six, hlow_seven_seven⟩

/-! ### `skipCorrection` and the hit certificate -/

/-- Rank `5` of row `7` is declined (bit `9` of `263` is clear), rank `6` is
taken (bit `8` is set).  So the declined budget is `4 ^ 2 = 16`. -/
theorem skipCorrection_seven_five : skipCorrection 7 263 5 = 16 := by
  rw [skipCorrection_eq_cons (by norm_num), skipCorrection_eq_cons (by norm_num),
    skipCorrection_eq_zero (by norm_num)]
  norm_num only
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-- **The sharp hit certificate, applied.**  At the rank where `hlow` fails,
`ρ 7 < 16` — far sharper than `ρ 7 < 2 ^ 7`.  (`DeclD4` computes `ρ 7 = 3`.) -/
theorem seven_sharp :
    seamIntegerGreedyRemainder 7 < skipCorrection 7 (lateEntryRemainder 7 5) 5 :=
  seamRemainder_lt_skipCorrection_of_not_hlow DeclD4.Seven.bitAdmissible_seven_five
    DeclD4.Seven.not_hlow_seven_five

theorem seven_sharp_value : seamIntegerGreedyRemainder 7 < 16 := by
  have h := seven_sharp
  rwa [DeclD4.Seven.lateEntryRemainder_seven_five, skipCorrection_seven_five] at h

/-- **The hit certificate, applied.**  Row `7` is a half-point hit, proved from
the *failure* of `hlow` rather than in spite of it. -/
theorem seven_is_a_hit_from_failure : seamIntegerGreedyRemainder 7 < 2 ^ 7 :=
  seamRemainder_lt_two_pow_of_not_hlow DeclD4.Seven.bitAdmissible_seven_five
    DeclD4.Seven.not_hlow_seven_five

/-- Cross-check against `DeclD4`'s independently computed `ρ 7 = 3`. -/
theorem seven_consistency : seamIntegerGreedyRemainder 7 = 3 ∧
    seamIntegerGreedyRemainder 7 < 16 :=
  ⟨DeclD4.Seven.seamIntegerGreedyRemainder_seven, seven_sharp_value⟩

/-! ### The equivalence, both sides witnessed

`hlow_iff_skipCorrection_le_seamRemainder` is an `iff`; both directions are
instantiated on the genuine object. -/

/-- The `hlow`-holds side, at row `20`. -/
theorem skipCorrection_le_seamRemainder_twenty :
    skipCorrection 20 (lateEntryRemainder 20 14) 14 ≤ seamIntegerGreedyRemainder 20 :=
  (hlow_iff_skipCorrection_le_seamRemainder DeclD4.bitAdmissible_twenty).mp hlow_twenty_fourteen

/-- The `hlow`-fails side, at row `7`. -/
theorem not_skipCorrection_le_seamRemainder_seven :
    ¬ (skipCorrection 7 (lateEntryRemainder 7 5) 5 ≤ seamIntegerGreedyRemainder 7) :=
  fun hc => DeclD4.Seven.not_hlow_seven_five
    ((hlow_iff_skipCorrection_le_seamRemainder
      DeclD4.Seven.bitAdmissible_seven_five).mpr hc)

/-! ### `half_mem_of_not_hlow_cofinally` is not vacuously stated

The hypothesis is a cofinality claim, which no finite certificate can discharge;
what *can* be exhibited is that its body is satisfiable — there is a row with a
`BitAdmissible` rank at which `hlow` fails. -/

theorem not_hlow_witness :
    ∃ s d : ℕ, 5 ≤ s ∧ BitAdmissible s d ∧
      ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)) :=
  ⟨7, 5, by norm_num, DeclD4.Seven.bitAdmissible_seven_five,
    DeclD4.Seven.not_hlow_seven_five⟩

end Concrete

end ErdosProblems.HlowH2
