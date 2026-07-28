import ErdosProblems.Three.T4

/-!
# Adversarial verification of `ErdosProblems/Three/T4.lean`

Section 1: axiom audit of every declaration of `T4`.
Section 2: satisfiability of every non-trivial hypothesis, on the real corpus
           objects, over a wide range of rows.
Section 3: independent re-derivation of the numeric claims in T4's docstring,
           and falsification tests of every proved conclusion.
Section 4: what is *not* established.
-/

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy Erdos249257.BitCorr
open ErdosProblems.ThreeT4

namespace ErdosProblems.ThreeT4.Verify

/-! ## 1. Axiom audit -/

#print axioms ErdosProblems.ThreeT4.mod_two_pow_succ_lt_of_testBit_false
#print axioms ErdosProblems.ThreeT4.two_pow_le_mod_two_pow_succ_of_testBit_true
#print axioms ErdosProblems.ThreeT4.lateGreedy_trapped
#print axioms ErdosProblems.ThreeT4.seamIntegerGreedyRemainder_eq_lateGreedy
#print axioms ErdosProblems.ThreeT4.seamRemainder_bounds
#print axioms ErdosProblems.ThreeT4.seamRemainder_lt_two_pow_succ
#print axioms ErdosProblems.ThreeT4.lateCorrection_lt_two_pow_of_late
#print axioms ErdosProblems.ThreeT4.largestSkipLateAt_of_zeroBit
#print axioms ErdosProblems.ThreeT4.seamRemainder_lt_two_pow_of_testBit_false
#print axioms ErdosProblems.ThreeT4.two_pow_le_seamRemainder_add_of_testBit_true
#print axioms ErdosProblems.ThreeT4.exists_largestSkipLateAt_of_zeroBit_window
#print axioms ErdosProblems.ThreeT4.testBit_true_of_not_largestSkipLateAt
#print axioms ErdosProblems.ThreeT4.testBit_true_of_badRun
#print axioms ErdosProblems.ThreeT4.two_pow_le_lateEntryRemainder_of_not_largestSkipLateAt
#print axioms ErdosProblems.ThreeT4.remainderReachesHalfPointCofinally_of_halfPointBitClear
#print axioms ErdosProblems.ThreeT4.half_mem_of_halfPointBitClearCofinally
#print axioms ErdosProblems.ThreeT4.half_mem_of_windowBitClearCofinally

#print axioms ErdosProblems.ThreeT4.Concrete.seamWeights_fourteen
#print axioms ErdosProblems.ThreeT4.Concrete.lateCorrection_fourteen_ten
#print axioms ErdosProblems.ThreeT4.Concrete.lateEntryRemainder_fourteen_ten
#print axioms ErdosProblems.ThreeT4.Concrete.admissible_fourteen
#print axioms ErdosProblems.ThreeT4.Concrete.testBit_fourteen_halfPoint
#print axioms ErdosProblems.ThreeT4.Concrete.testBit_fourteen_fifteen
#print axioms ErdosProblems.ThreeT4.Concrete.seamRemainder_fourteen_lt
#print axioms ErdosProblems.ThreeT4.Concrete.largestSkipLateAt_fourteen'
#print axioms ErdosProblems.ThreeT4.Concrete.admissible_twenty
#print axioms ErdosProblems.ThreeT4.Concrete.testBit_twenty_halfPoint
#print axioms ErdosProblems.ThreeT4.Concrete.seamRemainder_twenty_lt
#print axioms ErdosProblems.ThreeT4.Concrete.seamWeights_twelve
#print axioms ErdosProblems.ThreeT4.Concrete.lateCorrection_twelve_nine
#print axioms ErdosProblems.ThreeT4.Concrete.lateEntryRemainder_twelve_nine
#print axioms ErdosProblems.ThreeT4.Concrete.admissible_twelve
#print axioms ErdosProblems.ThreeT4.Concrete.testBit_twelve_window
#print axioms ErdosProblems.ThreeT4.Concrete.not_largestSkipLateAt_twelve

/-! ## 2. Satisfiability of the hypotheses, on real data

`LateEntryAdmissible` is the *entire* hypothesis load of the file (every theorem
of §2, §4, §6, §7 takes exactly its five conjuncts).  It is decidable, so it can
be evaluated on the genuine corpus objects rather than argued about. -/

instance decAdmissible (s d : ℕ) : Decidable (LateEntryAdmissible s d) := by
  unfold LateEntryAdmissible; infer_instance

/-! The first late rank of row `s`: the least `d` with `2 * s < 3 * d`. -/
def firstLate (s : ℕ) : ℕ := 2 * s / 3 + 1

example (s : ℕ) : 2 * s < 3 * firstLate s := by unfold firstLate; omega

/-- Sanity: `firstLate` really is the least late rank. -/
example (s : ℕ) (h : 1 ≤ firstLate s) : ¬ (2 * s < 3 * (firstLate s - 1)) := by
  unfold firstLate at *; omega

/-! **Satisfiability, first late rank, rows `6 … 800`.**  Rows where
`LateEntryAdmissible s (firstLate s)` FAILS.  Expected: `[7]` only — 794 of the
795 rows carrying a late rank are admissible, exactly as T4's docstring says. -/
#eval (List.range 795).filterMap (fun i =>
  let s := i + 6; let d := firstLate s
  if decide (LateEntryAdmissible s d) then none else some (s, d))

/-! **Satisfiability, all late ranks, rows `4 … 120`.**  For each row, the number
of late `d` with `LateEntryAdmissible s d`.  Reported as
`(rows with at least one admissible d, rows with none)`. -/
#eval
  let rows := (List.range 117).map (fun i => i + 4)
  let cnt := rows.map (fun s =>
    ((List.range (s + 1)).filter (fun d =>
      decide (2 * s < 3 * d) && decide (LateEntryAdmissible s d))).length)
  ((cnt.filter (fun c => c ≠ 0)).length, (cnt.filter (fun c => c = 0)).length,
    cnt.foldl (· + ·) 0,
    (rows.zip cnt).filterMap (fun p => if p.2 = 0 then some p.1 else none))

/-! **The hypothesis `hhigh` is load-bearing, not decoration.**  Row `5` is the
one row of `[4, 300]` where the conclusion of `seamRemainder_lt_two_pow_succ`
is FALSE: `ρ 5 = 71 ≥ 2 ^ 6 = 64`.  It is also inadmissible at every late rank,
so no instance of the theorem applies to it.  Printed:
`(ρ 5, 2 ^ 6, admissible at d = 4, admissible at d = 5)`. -/
#eval (seamIntegerGreedyRemainder 5, 2 ^ 6,
  decide (LateEntryAdmissible 5 4), decide (LateEntryAdmissible 5 5))

/-! ### The two cofinal hypotheses of §7 -/

/-! **`HalfPointBitClearCofinally`: per-row satisfiability.**  Rows `6 … 800`
at which *some* admissible late rank `d` (here: the first one) has bit `s` of
`lateEntryRemainder s d` clear — this is the condition the cofinal hypothesis
asks to recur.  Printed: `(hits, rows, maximal gap between consecutive hits)`. -/
#eval
  let hits := (List.range 795).filterMap (fun i =>
    let s := i + 6; let d := firstLate s
    if decide (LateEntryAdmissible s d) && !(Nat.testBit (lateEntryRemainder s d) s)
      then some s else none)
  let gaps := (hits.zip hits.tail).map (fun p => p.2 - p.1)
  (hits.length, 795, gaps.foldl max 0)

/-! **`WindowBitClearCofinally`: per-row satisfiability**, rows `6 … 200`, first
late rank.  Printed: `(hits, rows)`.  The window condition is far commoner than
the half-point condition. -/
#eval
  let hits := (List.range 195).filter (fun i =>
    let s := i + 6; let d := firstLate s
    decide (LateEntryAdmissible s d) &&
      ((List.range (2 * s - d + 1 - s)).any (fun k =>
        !(Nat.testBit (lateEntryRemainder s d) (s + k)))))
  (hits.length, 195)

/-! ### The hypothesis of `testBit_true_of_badRun` is NOT satisfiable in range

`testBit_true_of_badRun` assumes `∀ t ∈ [s, 2*s+1], ¬ LargestSkipLateAt t`, i.e.
a run of `s + 2` consecutive bad rows.  The bad rows of `[4, 300]` are computed
below directly from the corpus greedy word (a row is bad when its largest false
rank is not late).  There are four of them and the longest run has length 3, so
no `s ≥ 5` satisfies the hypothesis anywhere in range. -/

/-! The largest false rank of row `s`, as an option, from the corpus greedy. -/
def largestFalseRank (s : ℕ) : Option ℕ :=
  let bits := integerGreedyBits (seamWeights s) (seamSubsetTarget s)
  ((List.range (s - 2)).filterMap (fun i =>
    if bits[i]? = some false then some (i + 2) else none)).foldl
      (fun acc r => some (max r (acc.getD 0))) none

/-- Row `s` is good exactly when its largest false rank is late. -/
def rowGood (s : ℕ) : Bool :=
  match largestFalseRank s with
  | none => false
  | some d => decide (2 * s < 3 * d)

/-! Cross-check `rowGood` against the three rows T4 settles by proof:
`(rowGood 12, rowGood 14, rowGood 20)` must be `(false, true, true)`. -/
#eval (rowGood 12, rowGood 14, rowGood 20)

/-! The bad rows of `[4, 300]`, and the longest run of consecutive bad rows. -/
#eval
  let bad := (List.range 297).filterMap (fun i =>
    let s := i + 4; if rowGood s then none else some s)
  let runs := bad.foldl (fun (p : ℕ × ℕ × ℕ) s =>
    let (prev, cur, best) := p
    let cur' := if s = prev + 1 then cur + 1 else 1
    (s, cur', max best cur')) (0, 0, 0)
  (bad, runs.2.2)

/-! ## 3. Independent re-derivation of the docstring's measured claims -/

/-! Measured claim 1: the exact identity
`ρ s = R % 2 ^ (s+1) - ∑_{e taken} 4 ^ (s-e)` (T4 proves only the two-sided
*bound*).  Rows `6 … 400`, first late rank.  Printed:
`(rows actually tested, failures)` — the first component guards against a
vacuous sweep. -/
#eval
  let tested := (List.range 395).filter (fun i =>
    decide (LateEntryAdmissible (i + 6) (firstLate (i + 6))))
  let fails := (List.range 395).filterMap (fun i =>
    let s := i + 6; let d := firstLate s
    if !(decide (LateEntryAdmissible s d)) then none else
    let R := lateEntryRemainder s d
    let lw := seamWeightsFrom s d
    let bits := integerGreedyBits lw R
    let taken := ((List.range (s - d)).filterMap (fun k =>
      if bits[k]? = some true then some (4 ^ (s - (d + k))) else none)).foldl (· + ·) 0
    if seamIntegerGreedyRemainder s + taken = R % 2 ^ (s + 1) then none else some s)
  (tested.length, fails)

/-! Measured claim 2: `ρ s ≤ 2 ^ s ↔ bit s of R is clear`.  T4 proves only `←`.
Rows `6 … 400`, first late rank.  Printed:
`(rows tested, rows where the bit is clear, failures of the biconditional)`. -/
#eval
  let tested := (List.range 395).filter (fun i =>
    decide (LateEntryAdmissible (i + 6) (firstLate (i + 6))))
  let clear := tested.filter (fun i =>
    !(Nat.testBit (lateEntryRemainder (i + 6) (firstLate (i + 6))) (i + 6)))
  let bad := (List.range 395).filterMap (fun i =>
    let s := i + 6; let d := firstLate s
    if !(decide (LateEntryAdmissible s d)) then none else
    let R := lateEntryRemainder s d
    let lhs := decide (seamIntegerGreedyRemainder s ≤ 2 ^ s)
    let rhs := !(Nat.testBit R s)
    if lhs = rhs then none else some (s, lhs, rhs))
  (tested.length, clear.length, bad)

/-! Measured claim 3: the largest ratio `R / 2 ^ (2*s-d+1)` over rows `6 … 800`,
reported as `(s, numerator, denominator)` of the maximum of `R * 10000 / 2 ^ …`.
T4's docstring claims `0.9976` at `s = 65`. -/
#eval
  ((List.range 795).map (fun i =>
    let s := i + 6; let d := firstLate s
    (lateEntryRemainder s d * 10000 / 2 ^ (2 * s - d + 1), s))).foldl max (0, 0)

/-! The four concrete rows T4 certifies, recomputed from the definitions:
`(lateEntryRemainder, lateCorrection, ρ s)` for `s = 12, 14, 20`. -/
#eval ((lateEntryRemainder 12 9, lateCorrection 12 9, seamIntegerGreedyRemainder 12),
  (lateEntryRemainder 14 10, lateCorrection 14 10, seamIntegerGreedyRemainder 14),
  (lateEntryRemainder 20 14, lateCorrection 20 14, seamIntegerGreedyRemainder 20))

/-! Falsification sweep.  Over **every** admissible pair `(s, d)` with `s ≤ 150`,
check all four proved conclusions numerically:
`ρ s ≤ R % 2^(s+1) ≤ ρ s + lateCorrection` (`seamRemainder_bounds`),
`ρ s < 2 ^ (s+1)` (`seamRemainder_lt_two_pow_succ`),
`bit s clear → ρ s < 2 ^ s` (`seamRemainder_lt_two_pow_of_testBit_false`),
`clear bit above s → row good` (`largestSkipLateAt_of_zeroBit`).
Any output other than `[]` is a refutation of T4. -/
#eval
  (List.range 147).flatMap (fun i =>
    let s := i + 4
    (List.range (s + 1)).filterMap (fun d =>
      if !(decide (2 * s < 3 * d) && decide (LateEntryAdmissible s d)) then none else
      let R := lateEntryRemainder s d
      let lo := R % 2 ^ (s + 1)
      let r := seamIntegerGreedyRemainder s
      let c1 := decide (r ≤ lo) && decide (lo ≤ r + lateCorrection s d)
      let c2 := decide (r < 2 ^ (s + 1))
      let c3 := !(!(Nat.testBit R s)) || decide (r < 2 ^ s)
      let c4 := (List.range (2 * s - d + 1)).all (fun j =>
        !(decide (s + 1 ≤ j) && !(Nat.testBit R j)) || rowGood s)
      if c1 && c2 && c3 && c4 then none else some (s, d, c1, c2, c3, c4)))

/-! ## 4. What is not established

Nothing in `T4` inhabits `BitR2.RemainderReachesHalfPointCofinally`,
`HalfPointBitClearCofinally`, `WindowBitClearCofinally`, or
`(1/2 : ℝ) ∈ mersenneAchievementSet`.  Every §7 statement is an implication
*from* one of the first three.  The `#check`s below record the exact shapes. -/

#check @ErdosProblems.ThreeT4.half_mem_of_halfPointBitClearCofinally
#check @ErdosProblems.ThreeT4.half_mem_of_windowBitClearCofinally
#check @ErdosProblems.ThreeT4.remainderReachesHalfPointCofinally_of_halfPointBitClear

/-! Erdős #257's `1/2` question is **not** resolved by `T4`: the file proves
`HalfPointBitClearCofinally → 1/2 ∈ mersenneAchievementSet` and never discharges
the antecedent, and the antecedent additionally carries `LateEntryAdmissible`,
which is `RemC6`'s open invariant at one rank. -/
#eval "T4 does not resolve #257: no unconditional cofinality is proved."

/-! ## 5. Reduction 1 is a re-encoding, not a weakening

`HalfPointBitClearCofinally` existentially quantifies the late rank `d`, and
`d = s` is admissible whenever `2 ≤ s`: `seamWeightsFrom s s = []`,
`lateCorrection s s = 0`, and `lateEntryRemainder s s = ρ s`.  So the hypothesis
of §7's Reduction 1 is sandwiched between the strict and the non-strict form of
the endpoint `BitR2.RemainderReachesHalfPointCofinally` that the corpus already
had, and that `T4` itself imports:

    (∀ N, ∃ s ≥ N, 5 ≤ s ∧ ρ s < 2 ^ s)   →  HalfPointBitClearCofinally
                                          →  (∀ N, ∃ s ≥ N, 5 ≤ s ∧ ρ s ≤ 2 ^ s)

the first implication proved just below, the second being `T4`'s own
`remainderReachesHalfPointCofinally_of_halfPointBitClear`.  Consequently
`half_mem_of_halfPointBitClearCofinally` carries no more leverage than the
imported `BitR2.half_mem_of_remainderReachesHalfPointCofinally`.  (Reduction 2,
`half_mem_of_windowBitClearCofinally`, is *not* subject to this collapse: at
`d = s` its window degenerates to `{s}` and it becomes Reduction 1, but at a
genuinely late `d` it is implied by a skipped late rank at row `s` as well, so it
is strictly the weaker hypothesis.) -/

theorem lateEntryRemainder_self {s : ℕ} (hs : 2 ≤ s) :
    lateEntryRemainder s s = seamIntegerGreedyRemainder s := by
  have h := seamIntegerGreedyRemainder_eq_lateGreedy (s := s) (d := s) hs
  rw [seamWeightsFrom_eq_nil (le_refl s),
    ErdosProblems.RemC6.integerGreedyRemainder_nil] at h
  exact h.symm

/-- The degenerate late rank `d = s` is admissible at every row where
`ρ s < 2 ^ s`, and its half-point bit is then automatically clear. -/
theorem halfPointBitClearCofinally_of_remainder_lt
    (h : ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ 5 ≤ s ∧ seamIntegerGreedyRemainder s < 2 ^ s) :
    HalfPointBitClearCofinally := by
  intro N
  obtain ⟨s, hNs, hs5, hlt⟩ := h N
  have hEq := lateEntryRemainder_self (s := s) (by omega)
  have hp : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  refine ⟨s, s, hNs, hs5, ⟨by omega, le_rfl, by omega, ?_, ?_⟩, ?_⟩
  · rw [hEq, show 2 * s - s + 1 = s + 1 by omega]; omega
  · rw [lateCorrection_eq_zero (le_refl s)]; exact Nat.zero_le _
  · rw [hEq]
    have hz : seamIntegerGreedyRemainder s / 2 ^ s = 0 := Nat.div_eq_of_lt hlt
    simp [Nat.testBit_eq_decide_div_mod_eq, hz]

#print axioms lateEntryRemainder_self
#print axioms halfPointBitClearCofinally_of_remainder_lt

/-! The strict/non-strict gap in the sandwich is empty in range: rows of
`[5, 400]` with `ρ s = 2 ^ s` exactly. -/
#eval (List.range 396).filterMap (fun i =>
  let s := i + 5
  if seamIntegerGreedyRemainder s = 2 ^ s then some s else none)

end ErdosProblems.ThreeT4.Verify
