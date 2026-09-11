import Erdos249257.SuffixCylinderFeedbackFanIn

/-!
# Exact in-strip continuation of a suffix-cylinder feedback seam

When the feedback hole remains in the next protected strip, the live words
do not disappear: they split into two exact endpoint cylinders.  The lower
sheet is an ordinary initial selected window, while the upper sheet is a
selected interval.  The final theorem records both sheets, the exact missing
carry, and the canonical-parent law which turns one missing parent into two
adjacent missing children at the next common-coefficient row.
-/

namespace Erdos249257.SuffixCylinderInStrip

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.FixedCoeffRewind
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderPromotion
open Erdos249257.SuffixCylinderThreshold
open Erdos249257.SuffixCylinderGlobalProducer
open Erdos249257.SuffixCylinderTwoSheet

/-- Selected admissible words indexed by an arbitrary closed carry interval.
The interval may be empty; this lets the endpoint cases `hole = 1` and
`hole = stripBound` retain one uniform two-sheet interface. -/
structure SelectedHalfInterval (N L U : ℕ) where
  word : ∀ q : ℕ, L ≤ q → q ≤ U → HalfWord N
  admissible : ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
    HalfStripAdmissible N (word q hqL hqU)
  terminal : ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
    integerHalfCarry (wordSupport (word q hqL hqU)) (N - 1) = q

/-- Endpoint-indexed suffix cylinder over a shifted carry interval. -/
noncomputable def HasSuffixCylinderOnInterval
    {M N L U : ℕ} (W : SelectedHalfInterval N L U)
    (hMN : M ≤ N) (endpoint : ℕ) : Prop :=
  ∃ pfx : HalfWord M,
    ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
      restrictWord hMN (W.word q hqL hqU) = pfx ∧
        wordSuffixNumeral (W.word q hqL hqU) M (N - M) + q = endpoint

/-- Fixed-coefficient successor restricted to a shifted target interval.
Only canonical parents strictly above `δ` are used. -/
noncomputable def SelectedHalfInterval.stepTailExplicit
    {N R L U C δ : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hLpos : 1 ≤ L) (hUstrip : U ≤ halfStripBound (N + 1))
    (hbuffer : U + C ≤ 2 * R)
    (hparentTail : ∀ q : ℕ, L ≤ q → q ≤ U → δ < parent C q)
    (hcoeff : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R), δ < k →
      supportCoeff (wordSupport (W.word k hk hkR)) (N + 1) = C) :
    SelectedHalfInterval (N + 1) L U := by
  classical
  let bit (q : ℕ) : Bool := decide (explicitParentBitZ C q = 1)
  let child (q : ℕ) (hqL : L ≤ q) (hqU : q ≤ U) : HalfWord (N + 1) :=
    extendHalfWord
      (W.word (parent C q)
        (explicitParent_pos (hLpos.trans hqL))
        (explicitParent_le hqU hbuffer))
      (bit q)
  have childTerminal (q : ℕ) (hqL : L ≤ q) (hqU : q ≤ U) :
      integerHalfCarry (wordSupport (child q hqL hqU)) N = q := by
    let k := parent C q
    have hq : 1 ≤ q := hLpos.trans hqL
    have hk : 1 ≤ k := explicitParent_pos hq
    have hkR : k ≤ R := explicitParent_le hqU hbuffer
    have hkTail : δ < k := hparentTail q hqL hqU
    let a := W.word k hk hkR
    have hkcarry := W.terminal k hk hkR
    have hparentCarry :
        integerHalfCarry (wordSupport (child q hqL hqU)) (N - 1) = k := by
      have hfuture := integerHalfCarry_insert_future_eq (wordSupport a)
        (show N - 1 + 2 ≤ N + 1 by omega)
      dsimp [child, a, k]
      rw [wordSupport_extendHalfWord]
      cases hbit : bit q
      · simpa [hbit] using hkcarry
      · simpa [hbit] using hfuture.trans hkcarry
    have hbaseCoeff : supportCoeff (wordSupport a) (N + 1) = C := by
      simpa [a] using hcoeff k hk hkR hkTail
    have hchildCoeff :
        (supportCoeff (wordSupport (child q hqL hqU)) (N + 1) : ℤ) =
          C + explicitParentBitZ C q := by
      rcases explicitParentBitZ_zero_or_one C q with hb | hb
      · have hbit : bit q = false := by simp [bit, hb]
        have hsupp : wordSupport (child q hqL hqU) = wordSupport a := by
          change wordSupport (extendHalfWord a (bit q)) = wordSupport a
          rw [wordSupport_extendHalfWord]
          simp [hbit]
        rw [hsupp]
        have hbaseCoeffZ :
            (supportCoeff (wordSupport a) (N + 1) : ℤ) = C := by
          exact_mod_cast hbaseCoeff
        simpa [hb] using hbaseCoeffZ
      · have hbit : bit q = true := by simp [bit, hb]
        have hsupp : wordSupport (child q hqL hqU) =
            insert (N + 1) (wordSupport a) := by
          change wordSupport (extendHalfWord a (bit q)) =
            insert (N + 1) (wordSupport a)
          rw [wordSupport_extendHalfWord]
          simp [hbit]
        rw [hsupp]
        rw [Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_self
          _ (by omega)]
        · push_cast
          rw [hbaseCoeff]
          simp [hb]
        · intro hmem
          rcases hmem with ⟨hlt, -⟩
          omega
    have hrec := integerHalfCarry_succ
      (wordSupport (child q hqL hqU)) (N - 1)
    simp only [show N - 1 + 1 = N by omega,
      show N - 1 + 2 = N + 1 by omega] at hrec
    calc
      integerHalfCarry (wordSupport (child q hqL hqU)) N =
          2 * integerHalfCarry (wordSupport (child q hqL hqU)) (N - 1) -
            (supportCoeff (wordSupport (child q hqL hqU)) (N + 1) : ℤ) := hrec
      _ = 2 * (k : ℤ) - (C + explicitParentBitZ C q) := by
        rw [hparentCarry, hchildCoeff]
      _ = q := by
        dsimp [k]
        rw [explicitParent_recurrence C q]
        ring
  exact {
    word := child
    admissible := by
      intro q hqL hqU
      let k := parent C q
      have hq : 1 ≤ q := hLpos.trans hqL
      have hk : 1 ≤ k := explicitParent_pos hq
      have hkR : k ≤ R := explicitParent_le hqU hbuffer
      apply HalfStripAdmissible.extend hN (W.admissible k hk hkR)
      rw [childTerminal q hqL hqU]
      exact ⟨by exact_mod_cast hq, by exact_mod_cast hqU.trans hUstrip⟩
    terminal := by
      intro q hqL hqU
      simpa [show N + 1 - 1 = N by omega] using childTerminal q hqL hqU
  }

theorem SelectedHalfInterval.word_stepTailExplicit
    {N R L U C δ : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hLpos : 1 ≤ L) (hUstrip : U ≤ halfStripBound (N + 1))
    (hbuffer : U + C ≤ 2 * R)
    (hparentTail : ∀ q : ℕ, L ≤ q → q ≤ U → δ < parent C q)
    (hcoeff : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R), δ < k →
      supportCoeff (wordSupport (W.word k hk hkR)) (N + 1) = C)
    (q : ℕ) (hqL : L ≤ q) (hqU : q ≤ U) :
    (SelectedHalfInterval.stepTailExplicit hN W hLpos hUstrip hbuffer
      hparentTail hcoeff).word q hqL hqU =
      extendHalfWord
        (W.word (parent C q)
          (explicitParent_pos (hLpos.trans hqL))
          (explicitParent_le hqU hbuffer))
        (decide (explicitParentBitZ C q = 1)) := by
  rfl

/-- A single missing canonical parent produces exactly its two adjacent
fixed-coefficient children.  This is the iteration law for the seam gap. -/
theorem parent_eq_iff_eq_two_adjacent_children
    (C h q : ℕ) (_hq : 1 ≤ q) :
    parent C q = h ↔
      (q : ℤ) = 2 * (h : ℤ) - C ∨
      (q : ℤ) = 2 * (h : ℤ) - C - 1 := by
  have hrec := explicitParent_recurrence C q
  rcases explicitParentBitZ_zero_or_one C q with hb | hb
  · rw [hb] at hrec
    constructor
    · intro hp
      left
      rw [hp] at hrec
      omega
    · intro hor
      rcases hor with hq0 | hq1 <;> omega
  · rw [hb] at hrec
    constructor
    · intro hp
      right
      rw [hp] at hrec
      omega
    · intro hor
      rcases hor with hq0 | hq1 <;> omega

/-- Complementary operational form: after one common-coefficient row, a
target survives exactly when it avoids both adjacent children of the missing
parent. -/
theorem parent_ne_iff_avoids_two_adjacent_children
    (C h q : ℕ) (hq : 1 ≤ q) :
    parent C q ≠ h ↔
      (q : ℤ) ≠ 2 * (h : ℤ) - C ∧
      (q : ℤ) ≠ 2 * (h : ℤ) - C - 1 := by
  constructor
  · intro hne
    constructor
    · intro hq0
      exact hne ((parent_eq_iff_eq_two_adjacent_children C h q hq).2
        (Or.inl hq0))
    · intro hq1
      exact hne ((parent_eq_iff_eq_two_adjacent_children C h q hq).2
        (Or.inr hq1))
  · rintro ⟨hq0, hq1⟩ hp
    rcases (parent_eq_iff_eq_two_adjacent_children C h q hq).1 hp with
      h | h
    · exact hq0 h
    · exact hq1 h

/-- Interval iteration law.  A forbidden parent block `[a,b]` pulls back
under one canonical fixed-coefficient row to the consecutive child block
`[2a-C-1, 2b-C]`, whose untruncated integer width is exactly doubled. -/
theorem parent_mem_interval_iff_mem_doubled_child_interval
    (C a b q : ℕ) (_hab : a ≤ b) :
    (a ≤ parent C q ∧ parent C q ≤ b) ↔
      2 * (a : ℤ) - C - 1 ≤ (q : ℤ) ∧
      (q : ℤ) ≤ 2 * (b : ℤ) - C := by
  have hrec := explicitParent_recurrence C q
  rcases explicitParentBitZ_zero_or_one C q with hb | hb
  · rw [hb] at hrec
    constructor <;> intro h <;> omega
  · rw [hb] at hrec
    constructor <;> intro h <;> omega

/-- The complementary boundary bits have the same coefficient at the odd
row immediately after their doubled feedback row. -/
theorem supportCoeff_extend_true_eq_false_at_double_add_one
    {K : ℕ} (hK : 1 ≤ K) (a : HalfWord K) :
    supportCoeff (wordSupport (extendHalfWord a true))
        (2 * (K + 1) + 1) =
      supportCoeff (wordSupport (extendHalfWord a false))
        (2 * (K + 1) + 1) := by
  apply supportCoeff_eq_of_divisorAgreement
  intro d hddiv
  have hdne : d ≠ K + 1 := by
    intro heq
    subst d
    have hdvd : K + 1 ∣ 2 * (K + 1) + 1 :=
      Nat.dvd_of_mem_divisors hddiv
    have hbase : K + 1 ∣ 2 * (K + 1) := by
      exact ⟨2, by omega⟩
    have hone : K + 1 ∣ 1 := by
      have hsub := Nat.dvd_sub hdvd hbase
      simpa using hsub
    have hle := Nat.le_of_dvd (by omega : 0 < (1 : ℕ)) hone
    omega
  rw [wordSupport_extendHalfWord, wordSupport_extendHalfWord]
  simp [hdne]

/-- Exact data retained after a genuine crossing whose hole remains in the
next strip.  Both sheet endpoints and the scalar failure coordinate are
part of the structure, so subsequent rows can propagate the gap rather than
forgetting it behind an existential seam receipt. -/
structure InStripTwoSheetStage (K N : ℕ) where
  hK1N : K + 1 ≤ N
  hole : ℕ
  hole_pos : 1 ≤ hole
  hole_le : hole ≤ halfStripBound N
  boundaryPrefix : HalfWord K
  lower : SelectedHalfWindow N (hole - 1)
  lowerCylinder : HasSuffixCylinderAt lower hK1N (hole - 1)
  lowerLiteral : ∀ q (hq : 1 ≤ q) (hqR : q ≤ hole - 1),
    restrictWord hK1N (lower.word q hq hqR) =
      extendHalfWord boundaryPrefix true
  upperEndpoint : ℕ
  upper : SelectedHalfInterval N (hole + 1) (halfStripBound N)
  upperCylinder : HasSuffixCylinderOnInterval upper hK1N upperEndpoint
  upperLiteral : ∀ q (hqL : hole + 1 ≤ q)
      (hqU : q ≤ halfStripBound N),
    restrictWord hK1N (upper.word q hqL hqU) =
      extendHalfWord boundaryPrefix false
  upperCovers : halfStripBound N ≤ upperEndpoint
  endpointSeparation : upperEndpoint =
    hole + 2 ^ (N - (K + 1))
  seamCut : ℕ
  seamCoeff : ℕ
  hole_eq : (hole : ℤ) = 2 * (seamCut : ℤ) - (seamCoeff : ℤ)
  scalar_exact (q : ℕ) (hq : 1 ≤ q)
      (hqB : q ≤ halfStripBound N) :
    EvenSeamReachable (seamCut : ℤ) (seamCoeff : ℤ) q ↔ q ≠ hole

/-- Cross-sheet coefficient socket for the next row.  This is deliberately
explicit: retaining two cylinders does not by itself prove their next-row
coefficients agree. -/
def InStripTwoSheetStage.HasCommonNextCoeff
    {K N : ℕ} (T : InStripTwoSheetStage K N) (C : ℕ) : Prop :=
  (∀ q (hq : 1 ≤ q) (hqR : q ≤ T.hole - 1),
    supportCoeff (wordSupport (T.lower.word q hq hqR)) (N + 1) = C) ∧
  (∀ q (hqL : T.hole + 1 ≤ q) (hqU : q ≤ halfStripBound N),
    supportCoeff (wordSupport (T.upper.word q hqL hqU)) (N + 1) = C)

/-- The complementary literal prefixes discharge the next odd-row common
coefficient automatically. -/
theorem InStripTwoSheetStage.hasCommonNextCoeff_at_oddSuccessor
    {K N : ℕ} (T : InStripTwoSheetStage K N)
    (hK : 1 ≤ K) (hdepth : N = 2 * (K + 1)) :
    T.HasCommonNextCoeff
      (supportCoeff (wordSupport (extendHalfWord T.boundaryPrefix false))
        (N + 1)) := by
  have hprefixEq :
      supportCoeff (wordSupport (extendHalfWord T.boundaryPrefix true))
          (N + 1) =
        supportCoeff (wordSupport (extendHalfWord T.boundaryPrefix false))
          (N + 1) := by
    simpa only [hdepth] using
      (supportCoeff_extend_true_eq_false_at_double_add_one
        hK T.boundaryPrefix)
  constructor
  · intro q hq hqR
    have htransfer := supportCoeff_word_eq_of_restrict_before_feedback
      (n := N + 1)
      T.hK1N (T.lower.word q hq hqR)
      (extendHalfWord T.boundaryPrefix true) (T.lowerLiteral q hq hqR)
      (by omega) (by omega) (by omega)
    exact htransfer.trans hprefixEq
  · intro q hqL hqU
    exact supportCoeff_word_eq_of_restrict_before_feedback
      (n := N + 1)
      T.hK1N (T.upper.word q hqL hqU)
      (extendHalfWord T.boundaryPrefix false) (T.upperLiteral q hqL hqU)
      (by omega) (by omega) (by omega)

/-- One arbitrary admissible parent word can be extended through a specified
fixed coefficient and Boolean child.  This removes the artificial need for
an initial carry interval when advancing a shifted sheet. -/
theorem halfTerminalReachable_succ_of_admissibleParent
    {N h q C : ℕ} (hN : 1 ≤ N) (a : HalfWord N)
    (ha : HalfStripAdmissible N a)
    (hterminal : integerHalfCarry (wordSupport a) (N - 1) = h)
    (hcoeff : supportCoeff (wordSupport a) (N + 1) = C)
    (beta : Bool)
    (hqrec : (q : ℤ) = 2 * (h : ℤ) - (C : ℤ) -
      (if beta then 1 else 0))
    (hqpos : 1 ≤ q) (hqstrip : q ≤ halfStripBound (N + 1)) :
    HalfTerminalReachable (N + 1) q := by
  let child := extendHalfWord a beta
  have hparentCarry : integerHalfCarry (wordSupport child) (N - 1) = h := by
    have hfuture := integerHalfCarry_insert_future_eq (wordSupport a)
      (show N - 1 + 2 ≤ N + 1 by omega)
    dsimp [child]
    rw [wordSupport_extendHalfWord]
    cases beta with
    | false => simpa using hterminal
    | true => simpa using hfuture.trans hterminal
  have hchildCoeff :
      (supportCoeff (wordSupport child) (N + 1) : ℤ) =
        (C : ℤ) + (if beta then 1 else 0) := by
    dsimp [child]
    rw [wordSupport_extendHalfWord]
    cases beta with
    | false => simp [hcoeff]
    | true =>
        rw [if_pos rfl]
        rw [Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_self
          _ (by omega)]
        · push_cast
          simp [hcoeff]
        · intro hmem
          rcases hmem with ⟨hlt, -⟩
          omega
  have hchildTerminal : integerHalfCarry (wordSupport child) N = q := by
    have hrec := integerHalfCarry_succ (wordSupport child) (N - 1)
    simp only [show N - 1 + 1 = N by omega,
      show N - 1 + 2 = N + 1 by omega] at hrec
    rw [hrec, hparentCarry, hchildCoeff]
    omega
  refine ⟨child, ?_, ?_⟩
  · apply HalfStripAdmissible.extend hN ha beta
    rw [hchildTerminal]
    exact ⟨by exact_mod_cast hqpos, by exact_mod_cast hqstrip⟩
  · simpa [show N + 1 - 1 = N by omega] using hchildTerminal

/-- Exact one-row finite-gap transition.  Under a genuinely common next
coefficient, every target whose canonical parent is not the old hole is
realized one row later.  By `parent_ne_iff_avoids_two_adjacent_children`,
the sole parent hole becomes precisely the adjacent child gap
`{2*hole-C-1, 2*hole-C}` (after intersection with the target strip). -/
theorem InStripTwoSheetStage.halfTerminalReachable_succ_off_childGap
    {K N B C q : ℕ} (T : InStripTwoSheetStage K N)
    (hN : 1 ≤ N) (hBstrip : B ≤ halfStripBound (N + 1))
    (hbuffer : B + C ≤ 2 * halfStripBound N)
    (hcommon : T.HasCommonNextCoeff C)
    (hq : 1 ≤ q) (hqB : q ≤ B)
    (hparentGap : parent C q ≠ T.hole) :
    HalfTerminalReachable (N + 1) q := by
  let p := parent C q
  have hp : 1 ≤ p := explicitParent_pos hq
  have hpB : p ≤ halfStripBound N := explicitParent_le hqB hbuffer
  let beta : Bool := decide (explicitParentBitZ C q = 1)
  have hqrec : (q : ℤ) = 2 * (p : ℤ) - (C : ℤ) -
      (if beta then 1 else 0) := by
    have hrec := explicitParent_recurrence C q
    rcases explicitParentBitZ_zero_or_one C q with hb | hb
    · simpa [p, beta, hb] using hrec
    · simpa [p, beta, hb] using hrec
  by_cases hpLo : p < T.hole
  · have hpR : p ≤ T.hole - 1 := by omega
    exact halfTerminalReachable_succ_of_admissibleParent hN
      (T.lower.word p hp hpR) (T.lower.admissible p hp hpR)
      (T.lower.terminal p hp hpR) (hcommon.1 p hp hpR) beta hqrec hq
      (hqB.trans hBstrip)
  · have hpHi : T.hole + 1 ≤ p := by omega
    exact halfTerminalReachable_succ_of_admissibleParent hN
      (T.upper.word p hpHi hpB) (T.upper.admissible p hpHi hpB)
      (T.upper.terminal p hpHi hpB) (hcommon.2 p hpHi hpB) beta hqrec hq
      (hqB.trans hBstrip)

/-- The two sheets realize every carry in the full strip except their exact
hole.  This is stronger than the protected `3..27` realization interface. -/
theorem InStripTwoSheetStage.halfTerminalReachable_of_ne_hole
    {K N q : ℕ} (T : InStripTwoSheetStage K N)
    (hq : 1 ≤ q) (hqB : q ≤ halfStripBound N) (hqHole : q ≠ T.hole) :
    HalfTerminalReachable N q := by
  rcases lt_or_gt_of_ne hqHole with hqLo | hqHi
  · have hqR : q ≤ T.hole - 1 := by omega
    exact ⟨T.lower.word q hq hqR, T.lower.admissible q hq hqR,
      T.lower.terminal q hq hqR⟩
  · have hqL : T.hole + 1 ≤ q := by omega
    exact ⟨T.upper.word q hqL hqB, T.upper.admissible q hqL hqB,
      T.upper.terminal q hqL hqB⟩

/-- Compatibility projection to the existing localized one-hole consumer. -/
theorem InStripTwoSheetStage.protectedEvenSeamRealizedAt
    {K N : ℕ} (T : InStripTwoSheetStage K N)
    (h27 : 27 ≤ halfStripBound N) :
    ProtectedEvenSeamRealizedAt N (T.seamCut : ℤ) (T.seamCoeff : ℤ) := by
  intro q hq3 hq27 hreach
  have hqB : q ≤ halfStripBound N := hq27.trans h27
  have hqHole : q ≠ T.hole :=
    (T.scalar_exact q (by omega) hqB).1 hreach
  exact T.halfTerminalReachable_of_ne_hole (by omega) hqB hqHole

/-- A crossing with an in-strip hole canonically splits into two exact
suffix cylinders.  The lower sheet covers `1 .. hole-1` with endpoint
`hole-1`; the upper sheet covers `hole+1 .. stripBound` with endpoint
`2E-c`. -/
noncomputable def CylinderStage.feedbackSplitCrossingInStrip
    {K N : ℕ} (S : CylinderStage K N)
    (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hcrossLow : 2 ^ (N - (K + 1)) < S.endpoint)
    (hcrossHigh :
      S.endpoint < 2 ^ (N - (K + 1)) + halfStripBound N)
    (c : ℕ)
    (hprofile : ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound N),
      supportCoeff (wordSupport (S.window.word k hk hkR)) (N + 1) =
        if k ≤ S.endpoint - 2 ^ (N - (K + 1)) then c + 1 else c)
    (hholePos : 1 ≤
      2 * (S.endpoint - 2 ^ (N - (K + 1))) - c)
    (hholeStrip :
      2 * (S.endpoint - 2 ^ (N - (K + 1))) - c ≤
        halfStripBound (N + 1)) :
    InStripTwoSheetStage K (N + 1) := by
  classical
  let δ := S.endpoint - 2 ^ (N - (K + 1))
  let hole := 2 * δ - c
  have hδpos : 1 ≤ δ := by dsimp [δ]; omega
  have hδltR : δ < halfStripBound N := by dsimp [δ]; omega
  have hR : 1 ≤ halfStripBound N := hδpos.trans hδltR.le
  have hholePos' : 1 ≤ hole := by simpa [hole, δ] using hholePos
  have hholeStrip' : hole ≤ halfStripBound (N + 1) := by
    simpa [hole, δ] using hholeStrip
  let Wbase : SelectedHalfWindow N δ :=
    Erdos249257.SuffixCylinderTwoSheet.SelectedHalfWindow.take
      S.window δ hδltR.le
  have hcylK : HasSuffixCylinderAt Wbase S.hKN S.endpoint :=
    hasSuffixCylinderAt_take S.window S.hKN S.cylinder δ hδltR.le
  have hcylPromoted : HasSuffixCylinderAt Wbase hK1N δ ∧ δ ≤ δ := by
    have hmargin : 2 ^ (N - (K + 1)) + δ ≤ S.endpoint := by
      dsimp [δ]
      omega
    have hp :=
      promoteSuffixCylinderAt_succ_of_headThreshold_add_width_le_endpoint
        Wbase hK1N hδpos (by simpa using hcylK) hmargin
    simpa [δ] using hp
  have hpCommon : ∀ k : ℕ, 1 ≤ k → k ≤ δ →
      selectedRowCoeff Wbase k = (c + 1 : ℕ) := by
    intro k hk hkδ
    rw [selectedRowCoeff, dif_pos ⟨hk, hkδ⟩]
    have hp := hprofile k hk (hkδ.trans hδltR.le)
    rw [if_pos hkδ] at hp
    exact_mod_cast (show
      supportCoeff (wordSupport (Wbase.word k hk hkδ)) (N + 1) = c + 1 by
        simpa [Wbase,
          Erdos249257.SuffixCylinderTwoSheet.SelectedHalfWindow.take]
          using hp)
  let Rlo := hole - 1
  have hRloEq : Rlo = 2 * δ - (c + 1) := by
    dsimp [Rlo, hole]
    omega
  have hbufferLo : Rlo + (c + 1) ≤ 2 * δ := by
    rw [hRloEq]
    omega
  have hRloStrip : Rlo ≤ halfStripBound (N + 1) := by
    dsimp [Rlo]
    omega
  let Wlo : SelectedHalfWindow (N + 1) Rlo :=
    Wbase.stepExplicit hN hRloStrip hpCommon hbufferLo
  have hcylLo : HasSuffixCylinderAt Wlo
      (hK1N.trans (Nat.le_succ N)) Rlo := by
    have hp := SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit
      hN Wbase hK1N hRloStrip hpCommon hbufferLo
      hcylPromoted.1 hcylPromoted.2
    simpa [hRloEq] using hp.1
  have hcoeffR := hprofile (halfStripBound N) hR le_rfl
  rw [if_neg (by omega : ¬ halfStripBound N ≤ δ)] at hcoeffR
  let aR := S.window.word (halfStripBound N) hR le_rfl
  have hc : c ≤ 2 * Nat.sqrt (N + 1) := by
    rw [← hcoeffR]
    exact supportCoeff_le_two_mul_sqrt (wordSupport aR) (N + 1)
  have hbufferHi : halfStripBound (N + 1) + c ≤
      2 * halfStripBound N := by
    simpa using halfStripBound_add_coeff_le_two_mul_pred
      (n := N + 1) (c := c) (by omega) hc
  have hparentTail : ∀ q : ℕ, hole + 1 ≤ q →
      q ≤ halfStripBound (N + 1) → δ < parent c q := by
    intro q hqL hqU
    have hrec := explicitParent_bitNat_recurrence c q
    by_contra hnot
    have hle : parent c q ≤ δ := by omega
    dsimp [hole] at hqL
    omega
  have hcoeffTail : ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound N),
      δ < k →
      supportCoeff (wordSupport (S.window.word k hk hkR)) (N + 1) = c := by
    intro k hk hkR hkTail
    have hp := hprofile k hk hkR
    rw [if_neg (by omega : ¬ k ≤ δ)] at hp
    exact hp
  let Whi : SelectedHalfInterval (N + 1) (hole + 1)
      (halfStripBound (N + 1)) :=
    SelectedHalfInterval.stepTailExplicit hN S.window
      (by omega) le_rfl hbufferHi hparentTail hcoeffTail
  let pfx : HalfWord K := Classical.choose S.cylinder
  have hcyl := Classical.choose_spec S.cylinder
  have hbaseLiteralTrue : ∀ k (hk : 1 ≤ k) (hkδ : k ≤ δ),
      restrictWord hK1N (Wbase.word k hk hkδ) =
        extendHalfWord pfx true := by
    intro k hk hkδ
    have hkR : k ≤ halfStripBound N := hkδ.trans hδltR.le
    have hbitTrue : S.window.word k hk hkR ⟨K + 1, by omega⟩ = true :=
      (headBit_true_iff_le_crossingCut S.window hK1N
        ⟨pfx, hcyl⟩ hcrossLow hk hkR).2 (by simpa [δ] using hkδ)
    have horig := restrictWord_succ_eq_extendHalfWord hK1N
      (S.window.word k hk hkR) pfx true (hcyl k hk hkR).1 hbitTrue
    simpa [Wbase,
      Erdos249257.SuffixCylinderTwoSheet.SelectedHalfWindow.take]
      using horig
  have hloLiteral : ∀ q (hq : 1 ≤ q) (hqR : q ≤ Rlo),
      restrictWord (hK1N.trans (Nat.le_succ N)) (Wlo.word q hq hqR) =
        extendHalfWord pfx true := by
    intro q hq hqR
    simpa [Wlo] using
      (SelectedHalfWindow.stepExplicit_preserves_literalPrefix
        Wbase hK1N (extendHalfWord pfx true) hN hRloStrip hpCommon
        hbufferLo hbaseLiteralTrue q hq hqR)
  have hcylHiBody : ∀ q (hqL : hole + 1 ≤ q)
      (hqU : q ≤ halfStripBound (N + 1)),
      restrictWord (hK1N.trans (Nat.le_succ N)) (Whi.word q hqL hqU) =
          extendHalfWord pfx false ∧
        wordSuffixNumeral (Whi.word q hqL hqU) (K + 1)
            (N + 1 - (K + 1)) + q = 2 * S.endpoint - c := by
    intro q hqL hqU
    let k := parent c q
    have hq : 1 ≤ q := by omega
    have hk : 1 ≤ k := explicitParent_pos hq
    have hkR : k ≤ halfStripBound N := explicitParent_le hqU hbufferHi
    have hkTail : δ < k := hparentTail q hqL hqU
    have hparentPrefix := (hcyl k hk hkR).1
    have hparentEndpoint := (hcyl k hk hkR).2
    have hbitFalse : S.window.word k hk hkR ⟨K + 1, by omega⟩ = false := by
      cases hb : S.window.word k hk hkR ⟨K + 1, by omega⟩ with
      | false => rfl
      | true =>
          have hkle :=
            (headBit_true_iff_le_crossingCut S.window hK1N
              ⟨pfx, hcyl⟩ hcrossLow hk hkR).1 hb
          exact False.elim ((by omega : ¬ k ≤ δ) hkle)
    have hparentPromoted :
        restrictWord hK1N (S.window.word k hk hkR) =
          extendHalfWord pfx false :=
      restrictWord_succ_eq_extendHalfWord hK1N
        (S.window.word k hk hkR) pfx false hparentPrefix hbitFalse
    constructor
    · rw [SelectedHalfInterval.word_stepTailExplicit]
      rw [← restrictWord_trans hK1N (Nat.le_succ N)]
      rw [restrictWord_extendHalfWord]
      exact hparentPromoted
    · rw [SelectedHalfInterval.word_stepTailExplicit]
      rw [supportSuffixNumeral_extendHalfWord hK1N]
      change
        2 * wordSuffixNumeral (S.window.word k hk hkR)
              (K + 1) (N - (K + 1)) +
            (if decide (explicitParentBitZ c q = 1) then 1 else 0) + q =
          2 * S.endpoint - c
      have hsplit := wordSuffixNumeral_split_head hK1N
        (S.window.word k hk hkR)
      rw [hbitFalse] at hsplit
      have hbitRec := explicitParent_bitNat_recurrence c q
      change wordSuffixNumeral (S.window.word k hk hkR) K (N - K) + k =
        S.endpoint at hparentEndpoint
      change wordSuffixNumeral (S.window.word k hk hkR) K (N - K) =
        0 + wordSuffixNumeral (S.window.word k hk hkR)
          (K + 1) (N - (K + 1)) at hsplit
      omega
  have hcylHi : HasSuffixCylinderOnInterval Whi
      (hK1N.trans (Nat.le_succ N)) (2 * S.endpoint - c) :=
    ⟨extendHalfWord pfx false, hcylHiBody⟩
  have hcoverHi : halfStripBound (N + 1) ≤ 2 * S.endpoint - c := by
    have hbase := S.covers
    omega
  have hendpointSeparation :
      2 * S.endpoint - c = hole + 2 ^ (N + 1 - (K + 1)) := by
    have hpow : 2 ^ (N + 1 - (K + 1)) =
        2 * 2 ^ (N - (K + 1)) := by
      rw [show N + 1 - (K + 1) = (N - (K + 1)) + 1 by omega,
        pow_succ]
      omega
    rw [hpow]
    dsimp [hole, δ]
    omega
  refine {
    hK1N := hK1N.trans (Nat.le_succ N)
    hole := hole
    hole_pos := hholePos'
    hole_le := hholeStrip'
    boundaryPrefix := pfx
    lower := by simpa [Rlo] using Wlo
    lowerCylinder := by simpa [Rlo] using hcylLo
    lowerLiteral := by
      intro q hq hqR
      simpa [Rlo] using hloLiteral q hq hqR
    upperEndpoint := 2 * S.endpoint - c
    upper := Whi
    upperCylinder := hcylHi
    upperLiteral := fun q hqL hqU ↦ (hcylHiBody q hqL hqU).1
    upperCovers := hcoverHi
    endpointSeparation := hendpointSeparation
    seamCut := δ
    seamCoeff := c
    hole_eq := by
      dsimp [hole]
      have hc2 : c ≤ 2 * δ := by omega
      rw [Nat.cast_sub hc2]
      push_cast
      rfl
    scalar_exact := by
      intro q hq hqB
      rw [evenSeamReachable_iff]
      have hholeZ : (hole : ℤ) = 2 * (δ : ℤ) - (c : ℤ) := by
        dsimp [hole]
        have hc2 : c ≤ 2 * δ := by omega
        rw [Nat.cast_sub hc2]
        push_cast
        rfl
      rw [← hholeZ]
      exact_mod_cast (show q ≠ hole ↔ q ≠ hole from Iff.rfl)
  }

/-- **Operational one-depth feedback split.**  At an exact half-divisor horizon, a
full cylinder either advances as a full cylinder or produces the exact
two-sheet state above.  Unlike the protected-seam existential, the residual
branch retains every admissible word off the hole, both cylinder endpoints,
the complementary literal prefixes, and the canonical-parent failure
coordinate needed by the finite-gap iterator.  This theorem alone is not an
iteration closure: later rows still need `HasCommonNextCoeff` receipts. -/
theorem CylinderStage.feedbackAdvance_or_inStripTwoSheet
    {K N : ℕ} (S : CylinderStage K N)
    (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    Nonempty (CylinderStage (K + 1) (N + 1)) ∨
      Nonempty (InStripTwoSheetStage K (N + 1)) := by
  have hfeedback : (N + 1) / 2 ≤ K + 1 := by
    rw [hrow]
    omega
  by_cases hbelow : S.endpoint ≤ 2 ^ (N - (K + 1))
  · left
    exact ⟨
      (Erdos249257.SuffixCylinderGlobalProducer.CylinderStage.promoteLow
        S hK1N hbelow).advance hN hfeedback⟩
  · by_cases habove :
        2 ^ (N - (K + 1)) + halfStripBound N ≤ S.endpoint
    · left
      exact ⟨(S.promoteHigh hK1N habove).advance hN hfeedback⟩
    · have hcrossLow : 2 ^ (N - (K + 1)) < S.endpoint := by omega
      have hcrossHigh :
          S.endpoint < 2 ^ (N - (K + 1)) + halfStripBound N := by omega
      obtain ⟨c, hprofile⟩ :=
        supportCoeff_profile_of_crossingSuffixCylinder
          S.window hK1N hrow S.cylinder hcrossLow
      let δ := S.endpoint - 2 ^ (N - (K + 1))
      by_cases hholeBelow : 2 * δ - c < 1
      · left
        exact ⟨
          Erdos249257.SuffixCylinderBelow.CylinderStage.feedbackAdvanceCrossingBelow
            S hN hK1N hcrossLow hcrossHigh c
            (by simpa [δ] using hprofile) hholeBelow⟩
      · by_cases hholeAbove : halfStripBound (N + 1) < 2 * δ - c
        · left
          exact ⟨
            Erdos249257.SuffixCylinderTwoSheet.CylinderStage.feedbackAdvanceCrossingAbove
              S hN hK1N hcrossLow hcrossHigh c
              (by simpa [δ] using hprofile) hholeAbove⟩
        · right
          exact ⟨
            Erdos249257.SuffixCylinderInStrip.CylinderStage.feedbackSplitCrossingInStrip
              S hN hK1N hcrossLow hcrossHigh c (by simpa [δ] using hprofile)
              (by dsimp only [δ] at hholeBelow; omega)
              (by dsimp only [δ] at hholeAbove; omega)⟩

#print axioms parent_eq_iff_eq_two_adjacent_children
#print axioms parent_ne_iff_avoids_two_adjacent_children
#print axioms parent_mem_interval_iff_mem_doubled_child_interval
#print axioms InStripTwoSheetStage.halfTerminalReachable_of_ne_hole
#print axioms InStripTwoSheetStage.protectedEvenSeamRealizedAt
#print axioms CylinderStage.feedbackSplitCrossingInStrip
#print axioms CylinderStage.feedbackAdvance_or_inStripTwoSheet

end Erdos249257.SuffixCylinderInStrip
