/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Decl.D1
import ErdosProblems.Three.T4

/-!
# H1 — `hlow` is false, and the bound it was guarding does not need it

The brief for this file was:

> Prove `hlow` directly.  `lateCorrection s d = (4·4^(s−d) − 4)/3` is explicit,
> and the condition says the low block `R % 2^(s+1)` of the entering remainder is
> at least that.

**`hlow` is not a theorem.  It is false, and the counterexample is inside the
range the corpus already scans.**  At `s = 7`, `d = 5` — the *first* late rank of
row `7`, and a rank the greedy declines, so `Decl.D1`'s `hhigh` discharge applies
there — the entering remainder is `lateEntryRemainder 7 5 = 263`, its low block is
`263 % 2 ^ 8 = 7`, and the correction budget is `lateCorrection 7 5 = 20 > 7`
(`hlow_fails_seven_five`).  The other side condition holds at that pair, so this
is a failure of `hlow` alone (`hhigh_holds_seven_five`, `declined_seven_five`).
Consequently

    not_hlow_of_hhigh : ¬ ∀ s d, 2 ≤ d → d ≤ s → 2*s < 3*d →
      lateEntryRemainder s d < 2 ^ (2*s-d+1) →
      lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s+1)

is proved.  `hlow` does **not** follow from `hhigh` plus lateness; §5 of `Decl.D1`
cannot be repeated for the second side condition, and no direct proof exists.

That is a sharp negative, so the rest of the file is about what survives.

## §1 — `hlow`, restated without division, and when it is forced (PROVED)

`hlow_iff` turns the side condition into the division-free
`4 * 4 ^ (s-d) ≤ 3 * (C % 2 ^ (s+1)) + 4`, straight off `Bit/Corr1`'s closed form
`3 * lateCorrection s d + 4 = 4 * 4 ^ (s-d)`.  Since
`lateCorrection s d < 2 * 4 ^ (s-d) = 2 ^ (2*(s-d)+1)`
(`lateCorrection_lt_two_mul_four_pow`), a **single set bit** of the capacity
anywhere in the closed window `[2*(s-d)+1, s]` already forces `hlow`
(`hlow_of_testBit`); the window is non-empty in the late zone and has width
exactly `2*d - s` (`window_width`), about `s/3` at the first late rank.

Contrapositive (`testBit_false_of_not_hlow`, `hlow_or_window_clear`): **`hlow` can
only fail on a capacity whose bits are solidly zero across that whole window.**
In particular `hlow` is automatic whenever bit `s` — the half point,
`Three/T4`'s decisive position — is set (`hlow_of_testBit_halfPoint`).

That last corollary is the structural obstruction, and it is worth stating
plainly: the bit criterion delivers `hlow` *exactly in the case where
`Three/T4`'s conclusion is uninteresting*.  `hlow` is at risk only in the good
case, where bit `s` is clear.  The criterion is also strictly weaker than `hlow`
itself: at row `14` (`d = 10`) `hlow` holds while every bit of the window
`[9, 14]` is clear (`fourteen_window_clear`, `fourteen_bit_route_silent`).

## §2 — the quantitative half of `Three/T4` does not need `hlow` (PROVED)

`Three/T4.lateGreedy_trapped` assumes both side conditions.  Here:

* `lateGreedy_lower` — the **lower** half is unconditional.  For every capacity
  and every late rank, with no `hhigh` and no `hlow`,

      C % 2 ^ (s+1) ≤ integerGreedyRemainder (seamWeightsFrom s d) C
                        + lateCorrection s d.

* `lateGreedy_lt_sharp` — the **upper** half survives `hlow`'s removal in
  weakened form: from `hhigh` alone,

      3 * integerGreedyRemainder (seamWeightsFrom s d) C
        < 3 * 2 ^ (s+1) + 2 * 4 ^ (s-d) + 4,

  i.e. `ρ < 2 ^ (s+1) + (2*4^(s-d)+4)/3`, and hence
  `ρ < 2 ^ (s+1) + 4 ^ (s-d)` (`lateGreedy_lt_two_pow_add`).  The constant is
  *exactly* the one `Decl.D1.remainder_lt_of_late_largest_skip_sharp` obtains, but
  the hypothesis is different: `D1` needs `d` to be the **largest declined rank**
  of the row, this needs only `hhigh` at `d`, which `D1` itself discharges at any
  declined rank.  So

      seamRemainder_lt_sharp_of_declined :
        rank `d` late and declined  ⟹  3 * ρ s < 3 * 2^(s+1) + 2 * 4^(s-d) + 4

  with **no side condition at all**.  The induction closes because the invariant
  carried is `3*C < 3*2^(2*s-e+1) + 2*B + 4*4^(s-e)` with `B` a *fixed* budget
  `≥ 4 ^ (s-e)` (`trap`): the skipped branch, which is where the naive induction
  breaks, is paid for out of `B` rather than out of the shrinking local term.

* `upper_trap_needs_hlow` — the **other** half of `T4`'s two-sided bound,
  `ρ ≤ C % 2 ^ (s+1)`, really does need `hlow`: at `s = 7`, `d = 6`, `C = 257`
  (which satisfies `hhigh`) the late greedy declines its only weight and returns
  `257`, while `257 % 2 ^ 8 = 1`.

## §3 — the payoff at the one row where `hlow` fails

Row `7` is the sole row of `[5, 400]` whose first late rank fails `hlow`, so
`Three/T4` §4 is silent there.  `seamRemainder_lt_sharp_of_declined` is not:
`seamRemainder_seven_lt` gives `3 * ρ 7 < 804`, i.e. `ρ 7 < 268`, from the
decline of rank `5` alone.  And row `7` is not lost to `T4` either — `hlow` holds
one rank later (`admissible_seven_six : LateEntryAdmissible 7 6`), so the failure
is a failure at a rank, not at a row.

## Anti-vacuity

Every hypothesis used above is exhibited on the genuine object.

* `hhigh` with `hlow` **failing**: `(s,d) = (7,5)` (§3 above).
* `hhigh` with `hlow` **holding**, via the §1 bit route rather than by evaluating
  the correction: `(s,d) = (17,12)`, `lateEntryRemainder 17 12 = 942537`, bit `17`
  set, hence `admissible_seventeen : LateEntryAdmissible 17 12`.  Row `17` is not
  one of the corpus's worked rows.
* the bit route **silent while `hlow` holds**: `(s,d) = (14,10)`.
* `trap` / `lateGreedy_lt_sharp` fire at `(7,5)`, `(17,12)` and at `Bit/Corr1`'s
  own `(20,14)`.

§7 instantiates the remaining general statements — `mod_lt_of_not_hlow`,
`window_width`, `hlow_or_window_clear`, `seamRemainder_lower`,
`lateGreedy_lt_two_pow_add`, `hlow_iff` — on the genuine object, so that no
theorem in the file rests on an unexhibited hypothesis.

## Measured, not proved — independently re-run

Reproducing the corpus definitions from scratch in an independent script
(`truncatedMersenneWeight s d = 4^s / (2^d - 1)`,
`seamSubsetTarget s = 2^(2s-1) - 2^s`, descending greedy over ranks `2 … s-1`):

* Over **every** pair `(s, d)` with `5 ≤ s ≤ 600` and `d` late, `hlow` fails at
  **exactly one** pair, `(7, 5)` — the pair proved false below — and `hhigh`
  fails at exactly one, `(5, 4)`.  `Three/T4`'s measurement note reports "the sole
  failure is `s = 7`" over `[6,800]` at the first late rank; this scan confirms it
  and adds that `(7,5)` is the only failure over *all* late ranks, not merely the
  first.
* Scanning only the first late rank over `[5, 800]` reproduces exactly the same
  two failures.
* `s = 5` is the only row of `[5, 600]` with no admissible late rank at all, so
  `LateEntryAdmissible` is inhabited at every row of `[6, 600]` — row `7` only
  through `d = 6`, not through its first late rank `d = 5`.
* The bounds of §2 were re-checked on 200000 random `(s, d, C)` with
  `6 ≤ s ≤ 40`, `d` late, `C < 2^(2s-d+1)`: no violation of
  `3*ρ < 3*2^(s+1) + 2*4^(s-d) + 4`, and none of the unconditional lower bound.
  `ρ ≤ C % 2^(s+1)` — `T4`'s other half — fails on `464` of those `200000`
  samples (`0.23 %`), which is why §2 keeps that half conditional and
  `upper_trap_needs_hlow` records an explicit witness.

## What is *not* claimed

Closing `hlow` was never going to resolve `#257`: `RemC1.exists_persistent_surplus_model`
proves that **no** bound of the form `ρ s ≤ C · 2 ^ s` — including
`ρ s < 2 ^ (s+1)` — suffices for the `1/2` question.  This file does not close
`hlow` (it refutes it), does not prove `ρ s < 2 ^ (s+1)` unconditionally, and does
not touch the cofinality of the half-point bit, which is where `#257` actually
lives.  What it removes is a *hypothesis*, not the obstruction.

Checked with `lake env lean ErdosProblems/Hlow/H1.lean` (exit `0`, empty output).
No `sorry`, no `axiom`, no `native_decide`.
-/

namespace ErdosProblems.HlowH1

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open Erdos249257.BitCorr

/-! ## 1. `hlow` without division, and the bit criterion that forces it -/

/-- **`hlow` restated with no division.**  Straight off `Bit/Corr1`'s closed form
`3 * lateCorrection s d + 4 = 4 * 4 ^ (s - d)`. -/
theorem hlow_iff {s d M : ℕ} (hds : d ≤ s) :
    lateCorrection s d ≤ M ↔ 4 * 4 ^ (s - d) ≤ 3 * M + 4 := by
  have h := three_mul_lateCorrection_add_four (s := s) (d := d) hds
  omega

/-- The whole correction budget stays below `2 ^ (2*(s-d)+1) = 2 * 4 ^ (s-d)`. -/
theorem lateCorrection_lt_two_mul_four_pow {s d : ℕ} (hds : d ≤ s) :
    lateCorrection s d < 2 * 4 ^ (s - d) := by
  have h := three_mul_lateCorrection_add_four (s := s) (d := d) hds
  have hpos : 0 < (4 : ℕ) ^ (s - d) := by positivity
  omega

theorem two_pow_eq_two_mul_four_pow (m : ℕ) : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
  rw [pow_succ, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring

/-- A set bit below the modulus survives truncation to the low block. -/
theorem two_pow_le_mod_of_testBit {C j n : ℕ} (hj : j < n)
    (h : Nat.testBit C j = true) : 2 ^ j ≤ C % 2 ^ n := by
  apply Nat.ge_two_pow_of_testBit
  rw [Nat.testBit_mod_two_pow]
  simp [hj, h]

/-- **The bit criterion for `hlow`.**  A single set bit of the capacity anywhere
in the closed window `[2*(s-d)+1, s]` already forces the low block past the whole
`4 ^ k` correction budget. -/
theorem hlow_of_testBit {s d C j : ℕ} (hds : d ≤ s)
    (hj1 : 2 * (s - d) + 1 ≤ j) (hj2 : j ≤ s) (h : Nat.testBit C j = true) :
    lateCorrection s d ≤ C % 2 ^ (s + 1) := by
  have hb := two_pow_le_mod_of_testBit (n := s + 1) (by omega) h
  have hmono : (2 : ℕ) ^ (2 * (s - d) + 1) ≤ 2 ^ j :=
    Nat.pow_le_pow_right (by norm_num) hj1
  rw [two_pow_eq_two_mul_four_pow] at hmono
  have := lateCorrection_lt_two_mul_four_pow (s := s) (d := d) hds
  omega

/-- The quantitative form: the low block only has to reach `2 * 4 ^ (s-d)`. -/
theorem hlow_of_two_mul_four_pow_le {s d C : ℕ} (hds : d ≤ s)
    (h : 2 * 4 ^ (s - d) ≤ C % 2 ^ (s + 1)) :
    lateCorrection s d ≤ C % 2 ^ (s + 1) :=
  le_of_lt (lt_of_lt_of_le (lateCorrection_lt_two_mul_four_pow hds) h)

/-- The window is non-empty in the late zone, and its width is exactly `2*d - s`
— about `s / 3` at the first late rank. -/
theorem window_width {s d : ℕ} (hds : d ≤ s) (hlate : 2 * s < 3 * d) :
    2 * (s - d) + 1 ≤ s ∧ s + 1 - (2 * (s - d) + 1) = 2 * d - s := by
  omega

/-- **`hlow` is automatic at a set half-point bit.**  Bit `s` is `Three/T4`'s
decisive position, so the bit criterion supplies `hlow` precisely in the case
where `T4`'s conclusion is uninteresting.  This is the structural reason the
route of §1 cannot discharge `hlow` where it is wanted. -/
theorem hlow_of_testBit_halfPoint {s d C : ℕ} (hds : d ≤ s) (hlate : 2 * s < 3 * d)
    (h : Nat.testBit C s = true) :
    lateCorrection s d ≤ C % 2 ^ (s + 1) :=
  hlow_of_testBit hds (by omega) le_rfl h

/-- **Rigidity.**  `hlow` can only fail on a capacity whose bits are solidly zero
across the entire window `[2*(s-d)+1, s]`. -/
theorem testBit_false_of_not_hlow {s d C j : ℕ} (hds : d ≤ s)
    (hbad : ¬ lateCorrection s d ≤ C % 2 ^ (s + 1))
    (hj1 : 2 * (s - d) + 1 ≤ j) (hj2 : j ≤ s) :
    Nat.testBit C j = false := by
  by_contra hb
  exact hbad (hlow_of_testBit hds hj1 hj2 (by simpa using hb))

/-- The dichotomy, assembled. -/
theorem hlow_or_window_clear {s d C : ℕ} (hds : d ≤ s) :
    lateCorrection s d ≤ C % 2 ^ (s + 1) ∨
      ∀ j : ℕ, 2 * (s - d) + 1 ≤ j → j ≤ s → Nat.testBit C j = false := by
  by_cases h : lateCorrection s d ≤ C % 2 ^ (s + 1)
  · exact Or.inl h
  · exact Or.inr fun j hj1 hj2 => testBit_false_of_not_hlow hds h hj1 hj2

/-- A failure of `hlow` pins the low block far below the half point. -/
theorem mod_lt_of_not_hlow {s d C : ℕ} (hds : d ≤ s)
    (hbad : ¬ lateCorrection s d ≤ C % 2 ^ (s + 1)) :
    C % 2 ^ (s + 1) < 2 * 4 ^ (s - d) := by
  by_contra hc
  exact hbad (hlow_of_two_mul_four_pow_le hds (by omega))

/-! ## 2. What the late greedy does without `hlow`

`Three/T4.lateGreedy_trapped` needs both side conditions.  The lower half needs
neither; the upper half needs only `hhigh`, at the cost of an additive
`(2*4^(s-d)+4)/3`. -/

/-- Subtracting anything moves a residue down by at most the amount subtracted. -/
theorem mod_le_mod_sub_add {y a m : ℕ} (hm : 0 < m) : y % m ≤ (y - a) % m + a := by
  by_cases h : a ≤ y % m
  · rw [mod_sub_of_le_mod hm h]; omega
  · omega

/-- Subtracting a multiple of the modulus leaves the residue alone. -/
theorem sub_multiple_mod {A M t : ℕ} (h : M * t ≤ A) : (A - M * t) % M = A % M := by
  conv_rhs => rw [show A = A - M * t + M * t by omega]
  rw [Nat.add_mul_mod_self_left]

/-- **The lower trapping bound, unconditionally.**  No `hhigh`, no `hlow`: at
every late rank and for every capacity, the late greedy cannot destroy more of
the low block than the correction budget.  This is
`Three/T4.seamRemainder_bounds`'s second component with both side conditions
removed. -/
theorem lateGreedy_lower (s : ℕ) : ∀ d C : ℕ, 2 * s < 3 * d →
    C % 2 ^ (s + 1)
      ≤ integerGreedyRemainder (seamWeightsFrom s d) C + lateCorrection s d := by
  intro d C hlate
  by_cases hds : d < s
  · have hd2 : 2 ≤ d := by omega
    have hw := truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank hd2 hds hlate
    have hcorr := lateCorrection_eq_cons (s := s) (d := d) hds
    rw [seamWeightsFrom_eq_cons hds, ErdosProblems.RemC6.integerGreedyRemainder_cons, hw]
    by_cases htk : 2 ^ (2 * s - d) + 4 ^ (s - d) ≤ C
    · rw [if_pos htk]
      have hIH := lateGreedy_lower s (d + 1) (C - (2 ^ (2 * s - d) + 4 ^ (s - d))) (by omega)
      have hCge : (2 : ℕ) ^ (2 * s - d) ≤ C := le_trans (Nat.le_add_right _ _) htk
      have h2 : (C - 2 ^ (2 * s - d)) % 2 ^ (s + 1) = C % 2 ^ (s + 1) := by
        obtain ⟨t, ht⟩ : (2 : ℕ) ^ (s + 1) ∣ 2 ^ (2 * s - d) := pow_dvd_pow 2 (by omega)
        rw [ht] at hCge ⊢
        exact sub_multiple_mod hCge
      have hkey : C % 2 ^ (s + 1)
          ≤ (C - (2 ^ (2 * s - d) + 4 ^ (s - d))) % 2 ^ (s + 1) + 4 ^ (s - d) := by
        have h1 : C - (2 ^ (2 * s - d) + 4 ^ (s - d))
            = (C - 2 ^ (2 * s - d)) - 4 ^ (s - d) := by omega
        rw [h1, ← h2]
        exact mod_le_mod_sub_add (Nat.two_pow_pos _)
      omega
    · rw [if_neg htk]
      have hIH := lateGreedy_lower s (d + 1) C (by omega)
      have hle := lateCorrection_succ_le s d
      omega
  · rw [seamWeightsFrom_eq_nil (by omega), ErdosProblems.RemC6.integerGreedyRemainder_nil]
    exact le_trans (Nat.mod_le _ _) (Nat.le_add_right _ _)
termination_by d => s - d
decreasing_by all_goals omega

/-- **The invariant that survives the declined branch.**  The naive induction
`C < 2 ^ (2*s-e+1)` breaks when the greedy skips a rank: a skip only gives
`C < w e`, which overshoots the halved ceiling by the weight's second bit.
Carrying a *fixed* budget `B ≥ 4 ^ (s-e)` alongside repairs it — the skipped
branch is paid out of `B`, the taken branch out of the local term, and neither
branch has to shrink the other. -/
theorem trap (s : ℕ) : ∀ e C B : ℕ, 2 * s < 3 * e → 4 ^ (s - e) ≤ B →
    3 * C < 3 * 2 ^ (2 * s - e + 1) + 2 * B + 4 * 4 ^ (s - e) →
    3 * integerGreedyRemainder (seamWeightsFrom s e) C
      < 3 * 2 ^ (s + 1) + 2 * B + 4 := by
  intro e C B hlate hB hC
  by_cases hes : e < s
  · have he2 : 2 ≤ e := by omega
    have hw := truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank he2 hes hlate
    obtain ⟨P, hP⟩ : ∃ P : ℕ, (2 : ℕ) ^ (2 * s - (e + 1)) = P := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : ℕ, (4 : ℕ) ^ (s - (e + 1)) = G := ⟨_, rfl⟩
    have hpow3 : (2 : ℕ) ^ (2 * s - e) = 2 * P := by
      rw [show 2 * s - e = (2 * s - (e + 1)) + 1 by omega, pow_succ, hP]; ring
    have hpow2 : (2 : ℕ) ^ (2 * s - e + 1) = 4 * P := by rw [pow_succ, hpow3]; ring
    have hpow1 : (2 : ℕ) ^ (2 * s - (e + 1) + 1) = 2 * P := by rw [pow_succ, hP]; ring
    have hpow4 : (4 : ℕ) ^ (s - e) = 4 * G := by
      rw [show s - e = (s - (e + 1)) + 1 by omega, pow_succ, hG]; ring
    rw [hpow2, hpow4] at hC
    rw [hpow4] at hB
    rw [seamWeightsFrom_eq_cons hes, ErdosProblems.RemC6.integerGreedyRemainder_cons, hw,
      hpow3, hpow4]
    by_cases htk : 2 * P + 4 * G ≤ C
    · rw [if_pos htk]
      refine trap s (e + 1) (C - (2 * P + 4 * G)) B (by omega) ?_ ?_
      · rw [hG]; omega
      · rw [hpow1, hG]; omega
    · rw [if_neg htk]
      refine trap s (e + 1) C B (by omega) ?_ ?_
      · rw [hG]; omega
      · rw [hpow1, hG]; omega
  · rw [seamWeightsFrom_eq_nil (by omega), ErdosProblems.RemC6.integerGreedyRemainder_nil]
    have hz : s - e = 0 := by omega
    rw [hz, pow_zero] at hC
    have hmono : (2 : ℕ) ^ (2 * s - e + 1) ≤ 2 ^ (s + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
termination_by e => s - e
decreasing_by all_goals omega

/-- **The upper trapping bound without `hlow`.**  `hhigh` alone gives the late
greedy remainder the bound `2 ^ (s+1) + (2*4^(s-d)+4)/3` — the same constant
`Decl.D1.remainder_lt_of_late_largest_skip_sharp` obtains from the
largest-declined-rank hypothesis. -/
theorem lateGreedy_lt_sharp {s d C : ℕ} (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1)) :
    3 * integerGreedyRemainder (seamWeightsFrom s d) C
      < 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 :=
  trap s d C (4 ^ (s - d)) hlate le_rfl (by omega)

/-- The same, in `RemC6`'s shape. -/
theorem lateGreedy_lt_two_pow_add {s d C : ℕ} (hds : d < s) (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1)) :
    integerGreedyRemainder (seamWeightsFrom s d) C < 2 ^ (s + 1) + 4 ^ (s - d) := by
  have h := lateGreedy_lt_sharp hlate hhigh
  have hbig : (4 : ℕ) ≤ 4 ^ (s - d) := by
    calc (4 : ℕ) = 4 ^ 1 := by norm_num
    _ ≤ 4 ^ (s - d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ### Transport to the corpus's own `ρ s` -/

/-- **`Three/T4` §4, with `hlow` deleted.**  At any late rank satisfying `hhigh`
— including the rows where every late rank is taken, which is exactly the case
`RemC6` cannot reach — the seam remainder obeys the sharp bound. -/
theorem seamRemainder_lt_sharp_of_hhigh {s d : ℕ} (h2 : 2 ≤ d) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1)) :
    3 * seamIntegerGreedyRemainder s < 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 := by
  rw [ErdosProblems.ThreeT4.seamIntegerGreedyRemainder_eq_lateGreedy h2]
  exact lateGreedy_lt_sharp hlate hhigh

/-- **No side conditions at all.**  Combining with
`Decl.D1.lateEntryRemainder_lt_two_pow_of_declined`, which supplies `hhigh` for
free at a declined rank: a single late declined rank bounds `ρ s`.  Compare
`Decl.D1.remainder_lt_of_late_largest_skip_sharp`, which needs `d` to be the
*largest* declined rank of the row. -/
theorem seamRemainder_lt_sharp_of_declined {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s)
    (hlate : 2 * s < 3 * d)
    (hdecl : lateEntryRemainder s d < truncatedMersenneWeight s d) :
    3 * seamIntegerGreedyRemainder s < 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 :=
  seamRemainder_lt_sharp_of_hhigh h2 hlate
    (ErdosProblems.Decl.D1.lateEntryRemainder_lt_two_pow_of_declined h2 hds hdecl)

/-- The unconditional lower half, transported. -/
theorem seamRemainder_lower {s d : ℕ} (h2 : 2 ≤ d) (hlate : 2 * s < 3 * d) :
    lateEntryRemainder s d % 2 ^ (s + 1)
      ≤ seamIntegerGreedyRemainder s + lateCorrection s d := by
  rw [ErdosProblems.ThreeT4.seamIntegerGreedyRemainder_eq_lateGreedy h2]
  exact lateGreedy_lower s d (lateEntryRemainder s d) hlate

/-! ## 3. `hlow` is false

`s = 7`, `d = 5`.  Rank `5` is the first late rank of row `7`, and it is declined
by the actual greedy — so `Decl.D1` discharges `hhigh` there — and `hlow`
nevertheless fails. -/

theorem five_is_first_late_seven : 2 * 7 < 3 * 5 ∧ ¬ (2 * 7 < 3 * 4) := by
  refine ⟨by norm_num, by norm_num⟩

theorem lateCorrection_seven_five : lateCorrection 7 5 = 20 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_zero (by norm_num)]
  decide +kernel

/-- The genuine remainder entering the late zone of row `7`. -/
theorem lateEntryRemainder_seven_five : lateEntryRemainder 7 5 = 263 := by
  rw [ErdosProblems.Decl.D1.lateEntryRemainder_eq (by norm_num) (by norm_num)]
  norm_num [ErdosProblems.Three.T1.seamResidualUpto, ErdosProblems.Three.T1.seamResidual,
    truncatedMersenneWeight, seamSubsetTarget]

/-- Rank `5` of row `7` is declined. -/
theorem declined_seven_five :
    lateEntryRemainder 7 5 < truncatedMersenneWeight 7 5 := by
  rw [lateEntryRemainder_seven_five]
  norm_num [truncatedMersenneWeight]

/-- `hhigh` holds at `(7,5)` — and not merely numerically: it is `Decl.D1`'s
theorem, applied to the decline just proved. -/
theorem hhigh_holds_seven_five : lateEntryRemainder 7 5 < 2 ^ (2 * 7 - 5 + 1) :=
  ErdosProblems.Decl.D1.lateEntryRemainder_lt_two_pow_of_declined
    (by norm_num) (by norm_num) declined_seven_five

/-- **`hlow` fails at `(7,5)`.**  The low block is `7`; the correction budget is
`20`. -/
theorem hlow_fails_seven_five :
    ¬ lateCorrection 7 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1) := by
  rw [lateCorrection_seven_five, lateEntryRemainder_seven_five]
  decide +kernel

/-- **The sharp negative.**  `hlow` does not follow from `hhigh` and lateness, so
the discharge of `Decl.D1` §5 cannot be repeated for the second side condition:
there is nothing to prove directly, because the statement is false. -/
theorem not_hlow_of_hhigh :
    ¬ ∀ s d : ℕ, 2 ≤ d → d ≤ s → 2 * s < 3 * d →
        lateEntryRemainder s d < 2 ^ (2 * s - d + 1) →
        lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1) := by
  intro h
  exact hlow_fails_seven_five
    (h 7 5 (by norm_num) (by norm_num) (by norm_num) hhigh_holds_seven_five)

/-- Row `7` at `d = 5` is therefore not admissible for `Three/T4`. -/
theorem not_admissible_seven_five : ¬ ErdosProblems.ThreeT4.LateEntryAdmissible 7 5 := by
  rintro ⟨-, -, -, -, hlow⟩
  exact hlow_fails_seven_five hlow

/-- The window rigidity of §1, checked on the counterexample: `hlow` fails, so
every bit of `lateEntryRemainder 7 5` in `[2*(7-5)+1, 7] = [5,7]` is clear. -/
theorem seven_five_window_clear :
    ∀ j : ℕ, 5 ≤ j → j ≤ 7 → Nat.testBit (lateEntryRemainder 7 5) j = false :=
  fun j hj1 hj2 =>
    testBit_false_of_not_hlow (d := 5) (by norm_num) hlow_fails_seven_five
      (by omega) hj2

/-! ## 4. The payoff: the bound still fires where `Three/T4` cannot

`Three/T4` §4 is silent at row `7`'s first late rank, because `hlow` fails there.
`seamRemainder_lt_sharp_of_declined` needs no side condition. -/

/-- `3 * ρ 7 < 3 * 2 ^ 8 + 2 * 4 ^ 2 + 4 = 804`, i.e. `ρ 7 < 268`, obtained from
the decline of rank `5` alone.  (The true value is `3`.) -/
theorem seamRemainder_seven_lt : 3 * seamIntegerGreedyRemainder 7 < 804 := by
  have h := seamRemainder_lt_sharp_of_declined (s := 7) (d := 5)
    (by norm_num) (by norm_num) (by norm_num) declined_seven_five
  norm_num at h
  omega

/-- **The other half of `T4`'s two-sided bound really needs `hlow`.**  At
`s = 7`, `d = 6`, `C = 257` — a capacity satisfying `hhigh` — the late greedy
declines its single weight `truncatedMersenneWeight 7 6 = 260` and returns `257`,
while the low block is `257 % 2 ^ 8 = 1`.  So `hlow` cannot simply be deleted
from `Three/T4.lateGreedy_trapped`'s first component. -/
theorem upper_trap_needs_hlow :
    (257 : ℕ) < 2 ^ (2 * 7 - 6 + 1) ∧
      ¬ integerGreedyRemainder (seamWeightsFrom 7 6) 257 ≤ 257 % 2 ^ (7 + 1) := by
  refine ⟨by norm_num, ?_⟩
  rw [seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_nil (by norm_num),
    ErdosProblems.RemC6.integerGreedyRemainder_cons,
    ErdosProblems.RemC6.integerGreedyRemainder_nil]
  simp only [truncatedMersenneWeight]
  decide +kernel

/-! ### Row `7` survives one rank later

The failure is at a rank, not at a row: `hlow` holds at `(7,6)`, so `Three/T4`'s
machinery does cover row `7`. -/

theorem lateCorrection_seven_six : lateCorrection 7 6 = 4 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_zero (by norm_num)]
  decide +kernel

theorem lateEntryRemainder_seven_six : lateEntryRemainder 7 6 = 263 := by
  rw [ErdosProblems.Decl.D1.lateEntryRemainder_eq (by norm_num) (by norm_num)]
  norm_num [ErdosProblems.Three.T1.seamResidualUpto, ErdosProblems.Three.T1.seamResidual,
    truncatedMersenneWeight, seamSubsetTarget]

theorem admissible_seven_six : ErdosProblems.ThreeT4.LateEntryAdmissible 7 6 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [lateEntryRemainder_seven_six]; norm_num
  · rw [lateEntryRemainder_seven_six, lateCorrection_seven_six]
    decide +kernel

/-! ## 5. Anti-vacuity for §1: the bit route on the genuine object

Row `17`, first late rank `d = 12`.  `hlow` is obtained here **by reading one
bit** of the entering remainder, not by evaluating the correction budget. -/

theorem twelve_is_first_late_seventeen : 2 * 17 < 3 * 12 ∧ ¬ (2 * 17 < 3 * 11) := by
  refine ⟨by norm_num, by norm_num⟩

theorem lateEntryRemainder_seventeen_twelve : lateEntryRemainder 17 12 = 942537 := by
  rw [ErdosProblems.Decl.D1.lateEntryRemainder_eq (by norm_num) (by norm_num)]
  norm_num [ErdosProblems.Three.T1.seamResidualUpto, ErdosProblems.Three.T1.seamResidual,
    truncatedMersenneWeight, seamSubsetTarget]

theorem testBit_seventeen_halfPoint :
    Nat.testBit (lateEntryRemainder 17 12) 17 = true := by
  rw [lateEntryRemainder_seventeen_twelve]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-- `hlow` at `(17,12)`, from the half-point bit alone. -/
theorem hlow_seventeen_twelve :
    lateCorrection 17 12 ≤ lateEntryRemainder 17 12 % 2 ^ (17 + 1) :=
  hlow_of_testBit_halfPoint (by norm_num) (by norm_num) testBit_seventeen_halfPoint

/-- **Anti-vacuity, row 17.**  A row outside the corpus's worked set, admissible
for `Three/T4`, with `hlow` supplied by §1's bit criterion. -/
theorem admissible_seventeen : ErdosProblems.ThreeT4.LateEntryAdmissible 17 12 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, hlow_seventeen_twelve⟩
  rw [lateEntryRemainder_seventeen_twelve]; norm_num

/-- The §2 bound fires at row `17` too. -/
theorem seamRemainder_seventeen_lt :
    3 * seamIntegerGreedyRemainder 17 < 3 * 2 ^ 18 + 2 * 4 ^ 5 + 4 :=
  seamRemainder_lt_sharp_of_hhigh (s := 17) (d := 12) (by norm_num) (by norm_num)
    (by rw [lateEntryRemainder_seventeen_twelve]; norm_num)

/-! ### The bit criterion is strictly weaker than `hlow`

Row `14`, `d = 10`: `hlow` holds (`lateCorrection 14 10 = 340 ≤ 392`) yet every
bit of the window `[2*(14-10)+1, 14] = [9,14]` is clear, so `hlow_of_testBit`
cannot see it.  The sufficient condition of §1 is genuinely sufficient only. -/

theorem fourteen_window_clear :
    ∀ j : ℕ, 9 ≤ j → j ≤ 14 → Nat.testBit (lateEntryRemainder 14 10) j = false := by
  intro j h1 h2
  rw [ErdosProblems.ThreeT4.Concrete.lateEntryRemainder_fourteen_ten]
  interval_cases j <;>
    (simp only [Nat.testBit_eq_decide_div_mod_eq]; decide +kernel)

/-- `hlow` holds at `(14,10)` although the whole window is clear: the bit route
of §1 is silent there. -/
theorem fourteen_bit_route_silent :
    lateCorrection 14 10 ≤ lateEntryRemainder 14 10 % 2 ^ (14 + 1) ∧
      ¬ 2 * 4 ^ (14 - 10) ≤ lateEntryRemainder 14 10 % 2 ^ (14 + 1) := by
  refine ⟨ErdosProblems.ThreeT4.Concrete.admissible_fourteen.2.2.2.2, ?_⟩
  rw [ErdosProblems.ThreeT4.Concrete.lateEntryRemainder_fourteen_ten]
  decide +kernel

/-! ## 6. `Bit/Corr1`'s own row, through §2

`Bit/Corr1` verifies both side conditions numerically at `(20,14)`.  §2 needs
only the first, so the bound below is independent of `Corr1`'s `hlow` check. -/

theorem seamRemainder_twenty_lt_sharp :
    3 * seamIntegerGreedyRemainder 20 < 3 * 2 ^ 21 + 2 * 4 ^ 6 + 4 :=
  seamRemainder_lt_sharp_of_hhigh (s := 20) (d := 14) (by norm_num) (by norm_num)
    BitCorr.Concrete.actual_hypotheses_hold.1

/-! ## 7. The remaining statements, instantiated

Every general theorem above is applied here to the genuine object, so that none
of them rests on an unexhibited hypothesis. -/

/-- `mod_lt_of_not_hlow` at the counterexample: row `7`'s low block is below
`2 * 4 ^ 2 = 32`. -/
theorem mod_lt_seven_five : lateEntryRemainder 7 5 % 2 ^ (7 + 1) < 2 * 4 ^ (7 - 5) :=
  mod_lt_of_not_hlow (by norm_num) hlow_fails_seven_five

/-- `window_width` at `(7,5)`: the forced-zero window is `[5,7]`, of width
`2*5 - 7 = 3`. -/
theorem window_width_seven_five :
    2 * (7 - 5) + 1 ≤ 7 ∧ 7 + 1 - (2 * (7 - 5) + 1) = 2 * 5 - 7 :=
  window_width (by norm_num) (by norm_num)

/-- `hlow_or_window_clear` at `(7,5)`: the second branch is the one that holds. -/
theorem hlow_or_window_clear_seven_five :
    lateCorrection 7 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1) ∨
      ∀ j : ℕ, 2 * (7 - 5) + 1 ≤ j → j ≤ 7 →
        Nat.testBit (lateEntryRemainder 7 5) j = false :=
  hlow_or_window_clear (by norm_num)

/-- The unconditional lower bound, on the genuine object at row `17`. -/
theorem seamRemainder_lower_seventeen :
    lateEntryRemainder 17 12 % 2 ^ (17 + 1)
      ≤ seamIntegerGreedyRemainder 17 + lateCorrection 17 12 :=
  seamRemainder_lower (by norm_num) (by norm_num)

/-- The `RemC6`-shaped upper bound, on the genuine object at row `17`. -/
theorem lateGreedy_lt_two_pow_add_seventeen :
    integerGreedyRemainder (seamWeightsFrom 17 12) (lateEntryRemainder 17 12)
      < 2 ^ 18 + 4 ^ 5 :=
  lateGreedy_lt_two_pow_add (by norm_num) (by norm_num)
    (by rw [lateEntryRemainder_seventeen_twelve]; norm_num)

/-- `hlow_iff` read both ways: false at `(7,5)`, true at `(17,12)`, with the
division-free right-hand side. -/
theorem hlow_iff_decided :
    (¬ 4 * 4 ^ (7 - 5) ≤ 3 * (lateEntryRemainder 7 5 % 2 ^ (7 + 1)) + 4) ∧
      4 * 4 ^ (17 - 12) ≤ 3 * (lateEntryRemainder 17 12 % 2 ^ (17 + 1)) + 4 := by
  refine ⟨fun h => hlow_fails_seven_five ?_, ?_⟩
  · exact (hlow_iff (s := 7) (d := 5)
      (M := lateEntryRemainder 7 5 % 2 ^ (7 + 1)) (by norm_num)).mpr h
  · exact (hlow_iff (s := 17) (d := 12)
      (M := lateEntryRemainder 17 12 % 2 ^ (17 + 1)) (by norm_num)).mp hlow_seventeen_twelve

end ErdosProblems.HlowH1
