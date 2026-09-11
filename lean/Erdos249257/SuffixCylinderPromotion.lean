import Erdos249257.SelectedSuffixCylinder
import Erdos249257.RewindHalfDivisorAdapter

/-!
# One-bit promotion of a selected suffix cylinder
-/

namespace Erdos249257.SuffixCylinderPromotion

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.FixedCoeffRewind
open Erdos249257.FixedCoeffRewindPhase
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.RewindHalfDivisorAdapter
open Erdos249257.RewindSeamOperationalBridge

theorem supportSuffixNumeral_lt_two_pow
    (A : Set ℕ) [DecidablePred (· ∈ A)] (M L : ℕ) :
    supportSuffixNumeral A M L < 2 ^ L := by
  induction L with
  | zero => simp [supportSuffixNumeral]
  | succ L ih =>
      rw [supportSuffixNumeral, pow_succ]
      by_cases h : M + L + 1 ∈ A <;> simp [h] <;> omega

theorem supportSuffixNumeral_split_head
    (A : Set ℕ) [DecidablePred (· ∈ A)] (M L : ℕ) :
    supportSuffixNumeral A M (L + 1) =
      (if M + 1 ∈ A then 2 ^ L else 0) +
        supportSuffixNumeral A (M + 1) L := by
  induction L with
  | zero => simp [supportSuffixNumeral]
  | succ L ih =>
      rw [supportSuffixNumeral, ih, supportSuffixNumeral]
      rw [pow_succ]
      have hindex : M + (L + 1) + 1 = M + 1 + L + 1 := by omega
      rw [hindex]
      by_cases h : M + 1 ∈ A
      · simp [h]
        omega
      · simp [h]

theorem wordSuffixNumeral_split_head
    {K M : ℕ} (hKM : K + 1 ≤ M) (w : HalfWord M) :
    wordSuffixNumeral w K (M - K) =
      (if w ⟨K + 1, by omega⟩ then 2 ^ (M - (K + 1)) else 0) +
        wordSuffixNumeral w (K + 1) (M - (K + 1)) := by
  classical
  unfold wordSuffixNumeral
  rw [show M - K = (M - (K + 1)) + 1 by omega]
  rw [supportSuffixNumeral_split_head]
  congr 1
  by_cases hbit : w ⟨K + 1, by omega⟩ = true
  · have hmem : K + 1 ∈ wordSupport w := ⟨by omega, hbit⟩
    simp [hmem, hbit]
  · have hmem : K + 1 ∉ wordSupport w := by
      rintro ⟨_hindex, hw⟩
      exact hbit hw
    have hwfalse : w ⟨K + 1, by omega⟩ = false := by
      cases h : w ⟨K + 1, by omega⟩ <;> simp_all
    simp [hmem, hwfalse]

theorem restrictWord_succ_eq_extendHalfWord
    {K M : ℕ} (hK1M : K + 1 ≤ M) (w : HalfWord M)
    (a : HalfWord K) (β : Bool)
    (hprefix : restrictWord ((Nat.le_succ K).trans hK1M) w = a)
    (hbit : w ⟨K + 1, by omega⟩ = β) :
    restrictWord hK1M w = extendHalfWord a β := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa [restrictWord] using hbit
  · have hj := congrFun hprefix j
    simpa [restrictWord] using hj

theorem wordSuffixNumeral_lt_two_pow
    {N : ℕ} (w : HalfWord N) (M L : ℕ) :
    wordSuffixNumeral w M L < 2 ^ L := by
  classical
  unfold wordSuffixNumeral
  exact supportSuffixNumeral_lt_two_pow (wordSupport w) M L

theorem wordSuffixNumeral_lt_headPower_of_false
    {K M : ℕ} (hK1M : K + 1 ≤ M) (w : HalfWord M)
    (hfalse : w ⟨K + 1, by omega⟩ = false) :
    wordSuffixNumeral w K (M - K) < 2 ^ (M - (K + 1)) := by
  rw [wordSuffixNumeral_split_head hK1M]
  simp [hfalse]
  exact wordSuffixNumeral_lt_two_pow w (K + 1) (M - (K + 1))

theorem headPower_le_wordSuffixNumeral_of_true
    {K M : ℕ} (hK1M : K + 1 ≤ M) (w : HalfWord M)
    (htrue : w ⟨K + 1, by omega⟩ = true) :
    2 ^ (M - (K + 1)) ≤ wordSuffixNumeral w K (M - K) := by
  rw [wordSuffixNumeral_split_head hK1M]
  simp [htrue]

/-- Consecutive endpoint-indexed suffixes can change their leading bit only
from true to false as the terminal index increases. -/
theorem adjacent_endpoint_head_orientation
    {K M E r : ℕ} (hK1M : K + 1 ≤ M)
    (left right : HalfWord M)
    (hleft : wordSuffixNumeral left K (M - K) + r = E)
    (hright : wordSuffixNumeral right K (M - K) + (r + 1) = E)
    (hne : left ⟨K + 1, by omega⟩ ≠ right ⟨K + 1, by omega⟩) :
    left ⟨K + 1, by omega⟩ = true ∧
      right ⟨K + 1, by omega⟩ = false := by
  have hsuffix :
      wordSuffixNumeral left K (M - K) =
        wordSuffixNumeral right K (M - K) + 1 := by
    omega
  cases hleftBit : left ⟨K + 1, by omega⟩ <;>
    cases hrightBit : right ⟨K + 1, by omega⟩
  · exact (hne (by simp [hleftBit, hrightBit])).elim
  · have hlt :=
        wordSuffixNumeral_lt_headPower_of_false hK1M left hleftBit
    have hle :=
        headPower_le_wordSuffixNumeral_of_true hK1M right hrightBit
    omega
  · exact ⟨rfl, rfl⟩
  · exact (hne (by simp [hleftBit, hrightBit])).elim

/-- At the next prefix bit, an exact suffix cylinder turns every scalar
rewind seam into the precise object-level dichotomy: either both ancestor
bits agree and the current window has a common promoted restriction, or the
two adjacent ancestors are the literal true/false boundary pair. -/
theorem commonRestrictionAt_succ_or_rewindBaseHalfDivisorBoundaryPairAt
    {K M N R₀ R E : ℕ}
    (W₀ : SelectedHalfWindow M R₀) (W : SelectedHalfWindow N R)
    (hK1M : K + 1 ≤ M) (hMN : M ≤ N) (cs : List ℕ)
    (hR : 1 ≤ R)
    (hcyl : HasSuffixCylinderAt W₀
      ((Nat.le_succ K).trans hK1M) E)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hseam : IsSeamPair cs R) :
    W.CommonRestrictionAt (hK1M.trans hMN) ∨
      ∃ a : HalfWord K,
        RewindBaseHalfDivisorBoundaryPairAt W₀ hK1M cs a := by
  classical
  rcases hcyl with ⟨a, hcyl⟩
  let r := rewind cs 1
  obtain ⟨hleftPos, hleftBound, _hleftProv⟩ :=
    hprov 1 (by omega) hR
  change 1 ≤ r at hleftPos
  change r ≤ R₀ at hleftBound
  obtain ⟨_hlastPos, hlastBound, _hlastProv⟩ :=
    hprov R hR (le_refl R)
  have hseamEq : rewind cs R = r + 1 := by
    simpa [IsSeamPair, r] using hseam
  have hrightPos : 1 ≤ r + 1 := by omega
  have hrightBound : r + 1 ≤ R₀ := by
    rw [← hseamEq]
    exact hlastBound
  let left : HalfWord M := W₀.word r hleftPos hleftBound
  let right : HalfWord M := W₀.word (r + 1) hrightPos hrightBound
  obtain ⟨hleftPrefix, hleftEndpoint⟩ :=
    hcyl r hleftPos hleftBound
  obtain ⟨hrightPrefix, hrightEndpoint⟩ :=
    hcyl (r + 1) hrightPos hrightBound
  change restrictWord ((Nat.le_succ K).trans hK1M) left = a at hleftPrefix
  change wordSuffixNumeral left K (M - K) + r = E at hleftEndpoint
  change restrictWord ((Nat.le_succ K).trans hK1M) right = a at hrightPrefix
  change wordSuffixNumeral right K (M - K) + (r + 1) = E at hrightEndpoint
  let leftBit := left ⟨K + 1, by omega⟩
  let rightBit := right ⟨K + 1, by omega⟩
  have hleftK1 :
      restrictWord hK1M left = extendHalfWord a leftBit :=
    restrictWord_succ_eq_extendHalfWord hK1M left a leftBit
      hleftPrefix rfl
  have hrightK1 :
      restrictWord hK1M right = extendHalfWord a rightBit :=
    restrictWord_succ_eq_extendHalfWord hK1M right a rightBit
      hrightPrefix rfl
  by_cases hbits : leftBit = rightBit
  · left
    refine ⟨extendHalfWord a leftBit, ?_⟩
    intro q hq hqR
    obtain ⟨hqPos, hqBound, hqRestrict⟩ := hprov q hq hqR
    rcases rewind_eq_left_or_right_of_isSeamPair cs hq hqR hseam with
      hqLeft | hqRight
    · change rewind cs q = r at hqLeft
      calc
        restrictWord (hK1M.trans hMN) (W.word q hq hqR) =
            restrictWord hK1M
              (restrictWord hMN (W.word q hq hqR)) :=
          (restrictWord_trans hK1M hMN _).symm
        _ = restrictWord hK1M
              (W₀.word (rewind cs q) hqPos hqBound) := by
          rw [hqRestrict]
        _ = restrictWord hK1M left := by
          apply congrArg (restrictWord hK1M)
          exact W₀.word_eq_of_index_eq hqLeft
            hqPos hqBound hleftPos hleftBound
        _ = extendHalfWord a leftBit := hleftK1
    · change rewind cs q = r + 1 at hqRight
      calc
        restrictWord (hK1M.trans hMN) (W.word q hq hqR) =
            restrictWord hK1M
              (restrictWord hMN (W.word q hq hqR)) :=
          (restrictWord_trans hK1M hMN _).symm
        _ = restrictWord hK1M
              (W₀.word (rewind cs q) hqPos hqBound) := by
          rw [hqRestrict]
        _ = restrictWord hK1M right := by
          apply congrArg (restrictWord hK1M)
          exact W₀.word_eq_of_index_eq hqRight
            hqPos hqBound hrightPos hrightBound
        _ = extendHalfWord a rightBit := hrightK1
        _ = extendHalfWord a leftBit := by rw [hbits]
  · have horient := adjacent_endpoint_head_orientation hK1M
        left right hleftEndpoint hrightEndpoint hbits
    rcases horient with ⟨hleftTrue, hrightFalse⟩
    have hleftBitTrue : leftBit = true := by
      simpa [leftBit] using hleftTrue
    have hrightBitFalse : rightBit = false := by
      simpa [rightBit] using hrightFalse
    right
    refine ⟨a, hleftPos, hleftBound, hrightPos, hrightBound, ?_, ?_⟩
    · change restrictWord hK1M left = extendHalfWord a true
      calc
        restrictWord hK1M left = extendHalfWord a leftBit := hleftK1
        _ = extendHalfWord a true := by rw [hleftBitTrue]
    · change restrictWord hK1M right = extendHalfWord a false
      calc
        restrictWord hK1M right = extendHalfWord a rightBit := hrightK1
        _ = extendHalfWord a false := by rw [hrightBitFalse]

/-- Once the next prefix bit is common, an endpoint-indexed cylinder promotes
to that cutoff. The shifted endpoint still covers the whole carry window. -/
theorem promoteSuffixCylinderAt_succ_of_commonRestriction
    {K N R E : ℕ} (W : SelectedHalfWindow N R)
    (hK1N : K + 1 ≤ N) (hR : 1 ≤ R)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E)
    (hcommon : W.CommonRestrictionAt hK1N) :
    ∃ E' : ℕ, HasSuffixCylinderAt W hK1N E' ∧ R ≤ E' := by
  classical
  rcases hcyl with ⟨pfx, hcyl⟩
  rcases hcommon with ⟨pfx', hpfx'⟩
  let β := pfx' (Fin.last (K + 1))
  let shift := if β then 2 ^ (N - (K + 1)) else 0
  have htailEndpoint : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      wordSuffixNumeral (W.word k hk hkR) (K + 1) (N - (K + 1)) + k =
        E - shift := by
    intro k hk hkR
    have hendpoint := (hcyl k hk hkR).2
    have hbitRaw := congrFun (hpfx' k hk hkR) (Fin.last (K + 1))
    have hbit : W.word k hk hkR ⟨K + 1, by omega⟩ = β := by
      simpa [restrictWord, β] using hbitRaw
    have hsplit := wordSuffixNumeral_split_head hK1N (W.word k hk hkR)
    rw [hbit] at hsplit
    change wordSuffixNumeral (W.word k hk hkR) K (N - K) =
      shift + wordSuffixNumeral (W.word k hk hkR)
        (K + 1) (N - (K + 1)) at hsplit
    omega
  refine ⟨E - shift, ?_, ?_⟩
  · refine ⟨pfx', ?_⟩
    intro k hk hkR
    exact ⟨hpfx' k hk hkR, htailEndpoint k hk hkR⟩
  · have hlast := htailEndpoint R hR (le_refl R)
    omega

/-- Common restriction descends to any earlier cutoff. -/
theorem commonRestrictionAt_mono
    {L M N R : ℕ} (W : SelectedHalfWindow N R)
    (hLM : L ≤ M) (hMN : M ≤ N)
    (hcommon : W.CommonRestrictionAt hMN) :
    W.CommonRestrictionAt (hLM.trans hMN) := by
  rcases hcommon with ⟨a, ha⟩
  refine ⟨restrictWord hLM a, ?_⟩
  intro k hk hkR
  calc
    restrictWord (hLM.trans hMN) (W.word k hk hkR) =
        restrictWord hLM (restrictWord hMN (W.word k hk hkR)) :=
      (restrictWord_trans hLM hMN _).symm
    _ = restrictWord hLM a := by rw [ha k hk hkR]

/-- A width-valid exact rewind promotes the cylinder by one bit unless the
two adjacent ancestors form the literal marked boundary pair. -/
theorem promoteSuffixCylinderAt_succ_or_boundaryPair_of_rewindHistory
    {K M N R₀ R E₀ E : ℕ}
    (W₀ : SelectedHalfWindow M R₀) (W : SelectedHalfWindow N R)
    (hK1M : K + 1 ≤ M) (hMN : M ≤ N) (cs : List ℕ)
    (hR : 1 ≤ R) (hwidth : R ≤ denom cs)
    (hcyl₀ : HasSuffixCylinderAt W₀
      ((Nat.le_succ K).trans hK1M) E₀)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans (hK1M.trans hMN)) E)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs) :
    (∃ E' : ℕ,
        HasSuffixCylinderAt W (hK1M.trans hMN) E' ∧ R ≤ E') ∨
      ∃ a : HalfWord K,
        IsSeamPair cs R ∧
          RewindBaseHalfDivisorBoundaryPairAt W₀ hK1M cs a := by
  rcases rewind_singleton_or_isSeamPair cs hR hwidth with hsingle | hseam
  · left
    have hcommonM := W.commonRestrictionAt_of_rewind_singleton
      W₀ hMN cs hR hprov hsingle
    have hcommonK1 := commonRestrictionAt_mono W hK1M hMN hcommonM
    exact promoteSuffixCylinderAt_succ_of_commonRestriction
      W (hK1M.trans hMN) hR hcyl hcommonK1
  · rcases commonRestrictionAt_succ_or_rewindBaseHalfDivisorBoundaryPairAt
        W₀ W hK1M hMN cs hR hcyl₀ hprov hseam with hcommon | ⟨a, hpair⟩
    · left
      exact promoteSuffixCylinderAt_succ_of_commonRestriction
        W (hK1M.trans hMN) hR hcyl hcommon
    · exact Or.inr ⟨a, hseam, hpair⟩

/-- Forgetting the endpoint data of a suffix cylinder leaves its common
restriction certificate. -/
theorem commonRestrictionAt_of_suffixCylinder
    {M N R E : ℕ} (W : SelectedHalfWindow N R) (hMN : M ≤ N)
    (hcyl : HasSuffixCylinderAt W hMN E) :
    W.CommonRestrictionAt hMN := by
  rcases hcyl with ⟨a, ha⟩
  exact ⟨a, fun k hk hkR ↦ (ha k hk hkR).1⟩

/-- Full operational feedback-row dichotomy. A width-valid exact history
either promotes the endpoint cylinder through the next half-divisor bit, or
it realizes the localized one-hole seam at the produced even row. -/
theorem promotedSuffixCylinder_or_protectedEvenSeamRealizedAt
    {K M N R₀ E₀ E : ℕ}
    (W₀ : SelectedHalfWindow M R₀)
    (W : SelectedHalfWindow N (halfStripBound N))
    (hK1M : K + 1 ≤ M) (hMlt : M < 2 * (K + 1))
    (hMN : M ≤ N) (hrow : N + 1 = 2 * (K + 1))
    (cs : List ℕ) (hN : 1 ≤ N)
    (hwidth : halfStripBound N ≤ denom cs)
    (hcyl₀ : HasSuffixCylinderAt W₀
      ((Nat.le_succ K).trans hK1M) E₀)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans (hK1M.trans hMN)) E)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (h27 : 27 ≤ halfStripBound (N + 1)) :
    (∃ E' : ℕ, HasSuffixCylinderAt W (hK1M.trans hMN) E' ∧
        halfStripBound N ≤ E') ∨
      ∃ δ c : ℤ, ProtectedEvenSeamRealizedAt (N + 1) δ c := by
  have hR : 1 ≤ halfStripBound N := by
    unfold halfStripBound
    omega
  have hhalf : (N + 1) / 2 ≤ M := by
    rw [hrow]
    omega
  rcases promoteSuffixCylinderAt_succ_or_boundaryPair_of_rewindHistory
      W₀ W hK1M hMN cs hR hwidth hcyl₀ hcyl hprov with
    hpromote | ⟨a, hseam, hpair⟩
  · exact Or.inl hpromote
  · right
    refine ⟨(seamCut cs : ℤ),
      (supportCoeff (wordSupport (extendHalfWord a false)) (N + 1) : ℤ), ?_⟩
    exact
      protectedEvenSeamRealizedAt_succ_of_fullStrip_rewindHalfDivisorBoundaryPair
        W₀ W hK1M hMlt hMN hhalf hrow cs a hN hwidth hprov
        hseam h27 hpair

#print axioms supportSuffixNumeral_lt_two_pow
#print axioms supportSuffixNumeral_split_head
#print axioms wordSuffixNumeral_split_head
#print axioms restrictWord_succ_eq_extendHalfWord
#print axioms wordSuffixNumeral_lt_two_pow
#print axioms wordSuffixNumeral_lt_headPower_of_false
#print axioms headPower_le_wordSuffixNumeral_of_true
#print axioms adjacent_endpoint_head_orientation
#print axioms commonRestrictionAt_succ_or_rewindBaseHalfDivisorBoundaryPairAt
#print axioms promoteSuffixCylinderAt_succ_of_commonRestriction
#print axioms commonRestrictionAt_mono
#print axioms promoteSuffixCylinderAt_succ_or_boundaryPair_of_rewindHistory
#print axioms commonRestrictionAt_of_suffixCylinder
#print axioms promotedSuffixCylinder_or_protectedEvenSeamRealizedAt

end Erdos249257.SuffixCylinderPromotion
