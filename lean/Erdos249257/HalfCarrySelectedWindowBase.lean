import Erdos249257.HalfCarrySelectedWindow

/-!
# Computable depth-18 base for selected half-carry windows

The finite certificate is evaluated entirely on Boolean words.  Only the two
bridge theorems below mention `Set`-based support coefficients and carries.
-/

namespace Erdos249257.HalfCarrySelectedWindowBase

open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow

/-- Computable divisor coefficient of one finite Boolean word. -/
def wordCoeff {N : ℕ} (a : HalfWord N) (n : ℕ) : ℕ :=
  (n.divisors.filter fun d ↦
    if h : d < N + 1 then a ⟨d, h⟩ = true else False).card

/-- The computable finite-word coefficient is the existing support
coefficient of `wordSupport a`. -/
theorem wordCoeff_eq_supportCoeff_wordSupport
    {N : ℕ} (a : HalfWord N) (n : ℕ) :
    wordCoeff a n = supportCoeff (wordSupport a) n := by
  classical
  rw [wordCoeff, supportCoeff_eq_card_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hddiv, hdword⟩
    refine ⟨hddiv, ?_⟩
    by_cases hdN : d < N + 1
    · exact ⟨hdN, by simpa [hdN] using hdword⟩
    · simp [hdN] at hdword
  · rintro ⟨hddiv, hdword⟩
    rcases hdword with ⟨hdN, hbit⟩
    exact ⟨hddiv, by simp [hdN, hbit]⟩

/-- Executable integer half carry driven by `wordCoeff`. -/
def wordCarry {N : ℕ} (a : HalfWord N) : ℕ → ℤ
  | 0 => 1
  | m + 1 => 2 * wordCarry a m - (wordCoeff a (m + 2) : ℤ)

/-- The executable word carry agrees with the existing `Set`-based carry. -/
theorem wordCarry_eq_integerHalfCarry
    {N : ℕ} (a : HalfWord N) (m : ℕ) :
    wordCarry a m = integerHalfCarry (wordSupport a) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [wordCarry, integerHalfCarry_succ, ih,
        wordCoeff_eq_supportCoeff_wordSupport]

/-- The depth-18 cylinder word for terminal carry `k`.  Exponents
`2,3,6,7` form the common prefix; exponents `14,...,18` are the five-bit
big-endian encoding of `17-k`. -/
def depth18Word (k : ℕ) : HalfWord 18 := fun i ↦
  if i.val = 2 ∨ i.val = 3 ∨ i.val = 6 ∨ i.val = 7 then true
  else if 14 ≤ i.val then
    decide (((17 - k) / 2 ^ (18 - i.val)) % 2 = 1)
  else false

/-- Fully computable strip and terminal check for one depth-18 word. -/
def depth18EntryCheck (k : ℕ) : Bool :=
  ((List.range 18).all fun j ↦
    decide (
      (1 : ℤ) ≤ wordCarry (depth18Word k) j ∧
        wordCarry (depth18Word k) j ≤ halfStripBound (j + 1))) &&
  decide (wordCarry (depth18Word k) 17 = (k : ℤ))

/-- One Boolean table covers all twelve carries in the depth-18 strip. -/
def depth18TableCheck : Bool :=
  (List.range 12).all fun j ↦ depth18EntryCheck (j + 1)

/-- Kernel-reflected evaluation of the complete depth-18 table.  The strip
bound calls `Nat.sqrt`, whose well-founded recursion the elaborator will not
unfold, so the goal is discharged by kernel reduction rather than `decide`. -/
theorem depth18TableCheck_eq_true : depth18TableCheck = true := by
  decide +kernel

theorem depth18EntryCheck_eq_true
    {k : ℕ} (hk : 1 ≤ k) (hk12 : k ≤ 12) :
    depth18EntryCheck k = true := by
  have htable : ∀ j ∈ List.range 12,
      depth18EntryCheck (j + 1) = true := by
    simpa [depth18TableCheck] using depth18TableCheck_eq_true
  have hkpred : k - 1 ∈ List.range 12 := by
    rw [List.mem_range]
    omega
  simpa [Nat.sub_add_cancel hk] using htable (k - 1) hkpred

theorem depth18Word_carry_bounds
    {k n : ℕ} (hk : 1 ≤ k) (hk12 : k ≤ 12)
    (hn : 1 ≤ n) (hn18 : n ≤ 18) :
    (1 : ℤ) ≤ wordCarry (depth18Word k) (n - 1) ∧
      wordCarry (depth18Word k) (n - 1) ≤ halfStripBound n := by
  have hentry := depth18EntryCheck_eq_true hk hk12
  have hrows : ((List.range 18).all fun j ↦
      decide (
        (1 : ℤ) ≤ wordCarry (depth18Word k) j ∧
          wordCarry (depth18Word k) j ≤ halfStripBound (j + 1))) = true :=
    (Bool.and_eq_true_iff.mp hentry).1
  have hpred : n - 1 ∈ List.range 18 := by
    rw [List.mem_range]
    omega
  have hrow := (List.all_eq_true.mp hrows) (n - 1) hpred
  have hdecoded :
      (1 : ℤ) ≤ wordCarry (depth18Word k) (n - 1) ∧
        wordCarry (depth18Word k) (n - 1) ≤
          halfStripBound ((n - 1) + 1) :=
    of_decide_eq_true hrow
  simpa [Nat.sub_add_cancel hn] using hdecoded

theorem depth18Word_terminal
    {k : ℕ} (hk : 1 ≤ k) (hk12 : k ≤ 12) :
    wordCarry (depth18Word k) 17 = (k : ℤ) := by
  have hentry := depth18EntryCheck_eq_true hk hk12
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp hentry).2

theorem halfStripBound_eighteen : halfStripBound 18 = 12 := by
  have hsqrt : Nat.sqrt 18 = 4 := by
    symm
    exact Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩
  simp [halfStripBound, hsqrt]

/-- The exact depth-18 selected full strip used as the global induction
base. -/
noncomputable def depth18SelectedHalfWindow :
    SelectedHalfWindow 18 (halfStripBound 18) := by
  have hB : halfStripBound 18 = 12 := halfStripBound_eighteen
  refine ⟨fun k _ _ ↦ depth18Word k, ?_, ?_⟩
  · intro k hk hkR
    have hk12 : k ≤ 12 := by simpa [hB] using hkR
    refine ⟨by simp [depth18Word], ?_, ?_⟩
    · intro _
      simp [depth18Word]
    · intro n hn hn18
      rw [← wordCarry_eq_integerHalfCarry]
      exact depth18Word_carry_bounds hk hk12 hn hn18
  · intro k hk hkR
    have hk12 : k ≤ 12 := by simpa [hB] using hkR
    rw [← wordCarry_eq_integerHalfCarry]
    exact depth18Word_terminal hk hk12

/-- The literal common prefix shared by all twelve depth-18 words. -/
def depth18PrefixWord : HalfWord 13 := fun i ↦
  if i.val = 2 ∨ i.val = 3 ∨ i.val = 6 ∨ i.val = 7 then true else false

/-- Every certified depth-18 representative restricts to the same word at
depth 13; the five terminal encoding bits have all been removed. -/
theorem restrictWord_depth18Word_thirteen (k : ℕ) :
    restrictWord (by omega : 13 ≤ 18) (depth18Word k) =
      depth18PrefixWord := by
  funext i
  have hi : ¬ 14 ≤ i.val := by omega
  simp [restrictWord, depth18Word, depth18PrefixWord, hi]

/-- The finite base already carries the common-history invariant needed for
the first divisor-agreement step. -/
theorem depth18SelectedHalfWindow_commonRestrictionAt_thirteen :
    depth18SelectedHalfWindow.CommonRestrictionAt
      (by omega : 13 ≤ 18) := by
  refine ⟨depth18PrefixWord, ?_⟩
  intro k hk hkR
  change restrictWord (by omega : 13 ≤ 18) (depth18Word k) =
    depth18PrefixWord
  exact restrictWord_depth18Word_thirteen k

/-- Concrete initial coherent-history certificate: the depth-18 selected
window agrees on every divisor inspected by row 19. -/
theorem depth18SelectedHalfWindow_nextRowDivisorAgreement :
    depth18SelectedHalfWindow.NextRowDivisorAgreement :=
  depth18SelectedHalfWindow.nextRowDivisorAgreement_of_commonRestriction
    (by omega : 13 ≤ 18) (by norm_num)
    depth18SelectedHalfWindow_commonRestrictionAt_thirteen

#print axioms wordCoeff_eq_supportCoeff_wordSupport
#print axioms wordCarry_eq_integerHalfCarry
#print axioms depth18TableCheck_eq_true
#print axioms depth18EntryCheck_eq_true
#print axioms depth18Word_carry_bounds
#print axioms depth18Word_terminal
#print axioms halfStripBound_eighteen
#print axioms depth18SelectedHalfWindow
#print axioms restrictWord_depth18Word_thirteen
#print axioms depth18SelectedHalfWindow_commonRestrictionAt_thirteen
#print axioms depth18SelectedHalfWindow_nextRowDivisorAgreement

end Erdos249257.HalfCarrySelectedWindowBase
