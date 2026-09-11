import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.HalfCarryCeilParentContraction

/-!
# Selected protected windows for the half carry

This module isolates the scalar and object-level induction step suggested by
the exact protected-window replay.  The object-level producer must still
supply the coherent-history alternative: a common next-row divisor cylinder
or its canonical adjacent seam.
-/

namespace Erdos249257.HalfCarrySelectedWindow

open Erdos249257.HalfCarryReachability
open Erdos249257.FixedCoeffRewind

/-- A row forcing term and the two Boolean children of parent carry `k`. -/
def ProtectedChild (p : ℕ → ℤ) (k q : ℕ) : Prop :=
  ∃ b : ℤ, (b = 0 ∨ b = 1) ∧
    (q : ℤ) = 2 * (k : ℤ) - p k - b

/-- Scalar protected-window coverage for the stronger invariant seen in the
exact replay: every selected parent has one common proper-divisor
coefficient `C`.  The children of consecutive parents are the adjacent pairs
`{2k-C-1, 2k-C}`, so `S+C ≤ 2R` tiles the whole positive target window. -/
theorem protectedChild_cover_Icc_of_constant
    (p : ℕ → ℤ) {R S C : ℕ}
    (hp_const : ∀ k : ℕ, 1 ≤ k → k ≤ R → p k = C)
    (hbuffer : S + C ≤ 2 * R) :
    ∀ q : ℕ, 1 ≤ q → q ≤ S →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ R ∧ ProtectedChild p k q := by
  classical
  intro q hq hqS
  let k := (q + C + 1) / 2
  have hkpos : 1 ≤ k := by
    dsimp [k]
    omega
  have hkR : k ≤ R := by
    dsimp [k]
    omega
  have hkLower : q + C ≤ 2 * k := by
    dsimp [k]
    omega
  have hkUpper : 2 * k ≤ q + C + 1 := by
    dsimp [k]
    omega
  refine ⟨k, hkpos, hkR, ?_⟩
  let b : ℤ := 2 * (k : ℤ) - C - q
  have hb : b = 0 ∨ b = 1 := by
    have hkLowerZ : (q : ℤ) + (C : ℤ) ≤ 2 * (k : ℤ) := by
      exact_mod_cast hkLower
    have hkUpperZ : 2 * (k : ℤ) ≤ (q : ℤ) + (C : ℤ) + 1 := by
      exact_mod_cast hkUpper
    dsimp [b]
    omega
  refine ⟨b, hb, ?_⟩
  rw [hp_const k hkpos hkR]
  dsimp [b]
  ring

/-! ## Object-level selected windows -/

/-- Append one Boolean bit to a finite half word. -/
def extendHalfWord {N : ℕ} (a : HalfWord N) (β : Bool) : HalfWord (N + 1) :=
  Fin.lastCases β a

@[simp] theorem extendHalfWord_castSucc
    {N : ℕ} (a : HalfWord N) (β : Bool) (i : Fin (N + 1)) :
    extendHalfWord a β i.castSucc = a i := by
  simp [extendHalfWord]

@[simp] theorem extendHalfWord_last
    {N : ℕ} (a : HalfWord N) (β : Bool) :
    extendHalfWord a β (Fin.last (N + 1)) = β := by
  simp [extendHalfWord]

/-- Membership in the support of an extended word is old membership or the
new terminal bit. -/
theorem mem_wordSupport_extendHalfWord_iff
    {N n : ℕ} (a : HalfWord N) (β : Bool) :
    n ∈ wordSupport (extendHalfWord a β) ↔
      n ∈ wordSupport a ∨ (n = N + 1 ∧ β = true) := by
  constructor
  · rintro ⟨hn, hbit⟩
    by_cases hle : n ≤ N
    · left
      refine ⟨Nat.lt_succ_of_le hle, ?_⟩
      have hi : (⟨n, hn⟩ : Fin (N + 2)) =
          (⟨n, Nat.lt_succ_of_le hle⟩ : Fin (N + 1)).castSucc := by
        apply Fin.ext
        rfl
      rw [hi, extendHalfWord_castSucc] at hbit
      exact hbit
    · right
      have hnlast : n = N + 1 := by omega
      subst n
      have hi : (⟨N + 1, hn⟩ : Fin (N + 2)) = Fin.last (N + 1) := by
        apply Fin.ext
        rfl
      rw [hi, extendHalfWord_last] at hbit
      exact ⟨rfl, hbit⟩
  · rintro (⟨hn, hbit⟩ | ⟨rfl, hβ⟩)
    · refine ⟨lt_of_lt_of_le hn (by omega), ?_⟩
      have hi : (⟨n, lt_of_lt_of_le hn (by omega)⟩ : Fin (N + 2)) =
          (⟨n, hn⟩ : Fin (N + 1)).castSucc := by
        apply Fin.ext
        rfl
      rw [hi, extendHalfWord_castSucc]
      exact hbit
    · refine ⟨by omega, ?_⟩
      have hi : (⟨N + 1, by omega⟩ : Fin (N + 2)) = Fin.last (N + 1) := by
        apply Fin.ext
        rfl
      rw [hi, extendHalfWord_last, hβ]

/-- Set-level support normal form for a one-bit extension. -/
theorem wordSupport_extendHalfWord
    {N : ℕ} (a : HalfWord N) (β : Bool) :
    wordSupport (extendHalfWord a β) =
      if β then insert (N + 1) (wordSupport a) else wordSupport a := by
  ext n
  rw [mem_wordSupport_extendHalfWord_iff]
  cases β <;> simp [or_comm]

/-- Restricting an extension recovers its parent word. -/
theorem restrictWord_extendHalfWord
    {N : ℕ} (a : HalfWord N) (β : Bool) :
    restrictWord (Nat.le_succ N) (extendHalfWord a β) = a := by
  funext i
  change extendHalfWord a β i.castSucc = a i
  exact extendHalfWord_castSucc a β i

/-- If the new terminal carry lies in the next strip, extending an
admissible word preserves all earlier strip inequalities and establishes the
new one. -/
theorem HalfStripAdmissible.extend
    {N : ℕ} (hN : 1 ≤ N) {a : HalfWord N}
    (ha : HalfStripAdmissible N a) (β : Bool)
    (hterminal : (1 : ℤ) ≤
        integerHalfCarry (wordSupport (extendHalfWord a β)) N ∧
      integerHalfCarry (wordSupport (extendHalfWord a β)) N ≤
        halfStripBound (N + 1)) :
    HalfStripAdmissible (N + 1) (extendHalfWord a β) := by
  refine ⟨?_, ?_, ?_⟩
  · have hz := congrFun (restrictWord_extendHalfWord a β)
        (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1))
    exact hz.trans ha.1
  · intro h
    have hone := congrFun (restrictWord_extendHalfWord a β)
      (⟨1, by omega⟩ : Fin (N + 1))
    exact hone.trans (ha.2.1 (by omega : 1 < N + 1))
  · intro n hn hnN
    by_cases hlast : n = N + 1
    · subst n
      simpa using hterminal
    · have hnold : n ≤ N := by omega
      have hold := ha.2.2 n hn hnold
      have hsupport :
          wordSupport a =
            wordSupport (extendHalfWord a β) ∩ Set.Iic N := by
        rw [← wordSupport_restrictWord (Nat.le_succ N),
          restrictWord_extendHalfWord]
      have hcarry := integerHalfCarry_inter_Iic_eq_of_succ_le
        (wordSupport (extendHalfWord a β)) N (n - 1) (by omega)
      rw [← hsupport] at hcarry
      rwa [← hcarry]

/-- A selected family contains one explicit admissible representative for
every carry in the protected initial window.  No global uniqueness claim is
built into this interface. -/
structure SelectedHalfWindow (N R : ℕ) where
  word : ∀ k : ℕ, 1 ≤ k → k ≤ R → HalfWord N
  admissible : ∀ k hk hkR, HalfStripAdmissible N (word k hk hkR)
  terminal : ∀ k hk hkR,
    integerHalfCarry (wordSupport (word k hk hkR)) (N - 1) = k

/-- The actual next-row proper-divisor coefficient of the selected
representative.  Values outside the protected window are set to zero only so
the scalar lemma can consume a total function. -/
noncomputable def selectedRowCoeff
    {N R : ℕ} (W : SelectedHalfWindow N R) (k : ℕ) : ℤ :=
  if h : 1 ≤ k ∧ k ≤ R then
    (supportCoeff (wordSupport (W.word k h.1 h.2)) (N + 1) : ℤ)
  else 0

/-! ## Coherent-history socket -/

/-- The chosen terminal representatives agree on every divisor inspected by
the next proper coefficient.  This is the exact cylinder-prefix consequence
needed by the common-coefficient one-step atom; it avoids claiming that the
whole words are equal. -/
def SelectedHalfWindow.NextRowDivisorAgreement
    {N R : ℕ} (W : SelectedHalfWindow N R) : Prop :=
  ∀ k hk hkR ℓ hℓ hℓR d,
    d ∈ (N + 1).divisors →
      (d ∈ wordSupport (W.word k hk hkR) ↔
        d ∈ wordSupport (W.word ℓ hℓ hℓR))

/-- Divisor-membership agreement is precisely enough to identify two
support coefficients. -/
theorem supportCoeff_eq_of_divisorAgreement
    (A B : Set ℕ) (n : ℕ)
    (hagree : ∀ d : ℕ, d ∈ n.divisors → (d ∈ A ↔ d ∈ B)) :
    supportCoeff A n = supportCoeff B n := by
  classical
  rw [supportCoeff_eq_card_filter, supportCoeff_eq_card_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hd, hdA⟩
    exact ⟨hd, (hagree d hd).mp hdA⟩
  · rintro ⟨hd, hdB⟩
    exact ⟨hd, (hagree d hd).mpr hdB⟩

/-- A coherent next-row divisor cylinder makes `selectedRowCoeff` genuinely
constant on the protected window. -/
theorem SelectedHalfWindow.selectedRowCoeff_eq
    {N R : ℕ} (W : SelectedHalfWindow N R)
    (hagree : W.NextRowDivisorAgreement)
    {k ℓ : ℕ} (hk : 1 ≤ k) (hkR : k ≤ R)
    (hℓ : 1 ≤ ℓ) (hℓR : ℓ ≤ R) :
    selectedRowCoeff W k = selectedRowCoeff W ℓ := by
  rw [selectedRowCoeff, dif_pos ⟨hk, hkR⟩,
    selectedRowCoeff, dif_pos ⟨hℓ, hℓR⟩]
  exact_mod_cast supportCoeff_eq_of_divisorAgreement _ _ (N + 1)
    (hagree k hk hkR ℓ hℓ hℓR)

/-- Exact unresolved global history alternative.  Repeated common inverse
maps contract a carry interval to either one ancestor or two adjacent
ancestors.  The singleton case must establish `NextRowDivisorAgreement`; the
adjacent-pair case must identify the actual transition with the already
landed canonical one-hole seam.  No false phase-free singleton claim is
encoded here. -/
def SelectedHalfWindow.HistoryAlternative
    {N R : ℕ} (W : SelectedHalfWindow N R) : Prop :=
  W.NextRowDivisorAgreement ∨
    ∃ d : ℕ, ∃ δ c : ℤ,
      N + 1 = 2 * d ∧ IsCanonicalEvenSeam d δ c

/-- Legacy existence-by-choice implementation of the object-level one-step
protected-window theorem.  The public `step` below uses the canonical
fixed-coefficient parent and exposes exact restriction provenance. -/
noncomputable def SelectedHalfWindow.stepOpaque
    {N R S C : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (_hR : 1 ≤ R) (_hS : 1 ≤ S)
    (hSstrip : S ≤ halfStripBound (N + 1))
    (hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ R →
      selectedRowCoeff W k = C)
    (hbuffer : S + C ≤ 2 * R) :
    SelectedHalfWindow (N + 1) S := by
  classical
  let p : ℕ → ℤ := selectedRowCoeff W
  have hp_common' : ∀ k : ℕ, 1 ≤ k → k ≤ R → p k = C := by
    intro k hk hkR
    simpa [p] using hp_common k hk hkR
  have hcover :=
    protectedChild_cover_Icc_of_constant p hp_common' hbuffer
  have chooseParent : ∀ q : ℕ, 1 ≤ q → q ≤ S →
      ∃ k : ℕ, ∃ b : ℤ,
        1 ≤ k ∧ k ≤ R ∧ (b = 0 ∨ b = 1) ∧
          (q : ℤ) = 2 * (k : ℤ) - p k - b := by
    intro q hq hqS
    obtain ⟨k, hk, hkR, b, hb, hqeq⟩ := hcover q hq hqS
    exact ⟨k, b, hk, hkR, hb, hqeq⟩
  let parent (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) : ℕ :=
    Classical.choose (chooseParent q hq hqS)
  let bitZ (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) : ℤ :=
    Classical.choose (Classical.choose_spec (chooseParent q hq hqS))
  have parentSpec (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) :
      1 ≤ parent q hq hqS ∧ parent q hq hqS ≤ R ∧
      (bitZ q hq hqS = 0 ∨ bitZ q hq hqS = 1) ∧
      (q : ℤ) = 2 * (parent q hq hqS : ℤ) -
        p (parent q hq hqS) - bitZ q hq hqS := by
    exact Classical.choose_spec
      (Classical.choose_spec (chooseParent q hq hqS))
  let bit (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) : Bool :=
    decide (bitZ q hq hqS = 1)
  let child (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) : HalfWord (N + 1) :=
    extendHalfWord
      (W.word (parent q hq hqS) (parentSpec q hq hqS).1
        (parentSpec q hq hqS).2.1)
      (bit q hq hqS)
  have childTerminal (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) :
      integerHalfCarry (wordSupport (child q hq hqS)) N = q := by
    let k := parent q hq hqS
    have hk := (parentSpec q hq hqS).1
    have hkR := (parentSpec q hq hqS).2.1
    let a := W.word k hk hkR
    have hkcarry := W.terminal k hk hkR
    have hparentCarry :
        integerHalfCarry (wordSupport (child q hq hqS)) (N - 1) = k := by
      have hfuture := integerHalfCarry_insert_future_eq (wordSupport a)
        (show N - 1 + 2 ≤ N + 1 by omega)
      dsimp [child, a]
      rw [wordSupport_extendHalfWord]
      cases hbit : bit q hq hqS
      · simpa [hbit] using hkcarry
      · simpa [hbit] using hfuture.trans hkcarry
    have hcoeff :
        (supportCoeff (wordSupport (child q hq hqS)) (N + 1) : ℤ) =
          p k + bitZ q hq hqS := by
      have hbaseCoeff :
          (supportCoeff (wordSupport a) (N + 1) : ℤ) = p k := by
        dsimp [a, p, selectedRowCoeff]
        rw [dif_pos ⟨hk, hkR⟩]
      rcases (parentSpec q hq hqS).2.2.1 with hb | hb
      · have hbit : bit q hq hqS = false := by simp [bit, hb]
        have hsupp : wordSupport (child q hq hqS) = wordSupport a := by
          change wordSupport (extendHalfWord a (bit q hq hqS)) = wordSupport a
          rw [wordSupport_extendHalfWord]
          simp [hbit]
        rw [hsupp]
        simpa [hb] using hbaseCoeff
      · have hbit : bit q hq hqS = true := by simp [bit, hb]
        have hsupp : wordSupport (child q hq hqS) =
            insert (N + 1) (wordSupport a) := by
          change wordSupport (extendHalfWord a (bit q hq hqS)) =
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
      (wordSupport (child q hq hqS)) (N - 1)
    simp only [show N - 1 + 1 = N by omega,
      show N - 1 + 2 = N + 1 by omega] at hrec
    have htarget := (parentSpec q hq hqS).2.2.2
    calc
      integerHalfCarry (wordSupport (child q hq hqS)) N =
          2 * integerHalfCarry (wordSupport (child q hq hqS)) (N - 1) -
            (supportCoeff (wordSupport (child q hq hqS)) (N + 1) : ℤ) := hrec
      _ = 2 * (k : ℤ) - (p k + bitZ q hq hqS) := by
        rw [hparentCarry, hcoeff]
      _ = q := by
        dsimp [k]
        rw [htarget]
        ring
  refine ⟨child, ?_, ?_⟩
  · intro q hq hqS
    let k := parent q hq hqS
    have hk := (parentSpec q hq hqS).1
    have hkR := (parentSpec q hq hqS).2.1
    let a := W.word k hk hkR
    have ha := W.admissible k hk hkR
    apply HalfStripAdmissible.extend hN ha
    rw [childTerminal q hq hqS]
    exact ⟨by exact_mod_cast hq, by exact_mod_cast hqS.trans hSstrip⟩
  · intro q hq hqS
    simpa [show N + 1 - 1 = N by omega] using childTerminal q hq hqS

/-! ## Canonical parent and exact one-row provenance -/

/-- Every positive target has a positive canonical fixed-coefficient
parent. -/
theorem explicitParent_pos {q C : ℕ} (hq : 1 ≤ q) :
    1 ≤ parent C q := by
  simp only [parent]
  omega

/-- The protected-window buffer inequality puts the canonical parent in the
preceding protected window. -/
theorem explicitParent_le
    {q R S C : ℕ} (hqS : q ≤ S) (hbuffer : S + C ≤ 2 * R) :
    parent C q ≤ R := by
  simp only [parent]
  omega

/-- Exact parity bit associated to the canonical parent. -/
def explicitParentBitZ (C q : ℕ) : ℤ :=
  2 * (parent C q : ℤ) - C - q

/-- The canonical parent leaves exactly one Boolean remainder bit. -/
theorem explicitParentBitZ_zero_or_one (C q : ℕ) :
    explicitParentBitZ C q = 0 ∨ explicitParentBitZ C q = 1 := by
  have hl : q + C ≤ 2 * parent C q := by
    simp only [parent]
    omega
  have hu : 2 * parent C q ≤ q + C + 1 := by
    simp only [parent]
    omega
  have hlZ : (q : ℤ) + (C : ℤ) ≤ 2 * (parent C q : ℤ) := by
    exact_mod_cast hl
  have huZ : 2 * (parent C q : ℤ) ≤ (q : ℤ) + (C : ℤ) + 1 := by
    exact_mod_cast hu
  simp only [explicitParentBitZ]
  omega

/-- The canonical parent and parity bit solve the scalar child recurrence. -/
theorem explicitParent_recurrence (C q : ℕ) :
    (q : ℤ) = 2 * (parent C q : ℤ) - C - explicitParentBitZ C q := by
  simp only [explicitParentBitZ]
  ring

/-- A selected window together with exact one-row provenance.  Keeping the
restriction equation in the constructor makes later rewind composition
independent of the implementation details of the data-producing proof. -/
structure SelectedHalfWindow.FixedCoeffSuccessor
    {N R S C : ℕ} (W : SelectedHalfWindow N R)
    (hbuffer : S + C ≤ 2 * R) where
  window : SelectedHalfWindow (N + 1) S
  restrict_parent : ∀ q (hq : 1 ≤ q) (hqS : q ≤ S),
    restrictWord (Nat.le_succ N) (window.word q hq hqS) =
      W.word (parent C q) (explicitParent_pos hq)
        (explicitParent_le hqS hbuffer)

/-- Explicit-parent selected-window step with its restriction provenance in
the same bundle. -/
noncomputable def SelectedHalfWindow.stepExplicitWithHistory
    {N R S C : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hSstrip : S ≤ halfStripBound (N + 1))
    (hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ R →
      selectedRowCoeff W k = C)
    (hbuffer : S + C ≤ 2 * R) :
    W.FixedCoeffSuccessor hbuffer := by
  classical
  let bit (q : ℕ) : Bool := decide (explicitParentBitZ C q = 1)
  let child (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) : HalfWord (N + 1) :=
    extendHalfWord
      (W.word (parent C q) (explicitParent_pos hq)
        (explicitParent_le hqS hbuffer))
      (bit q)
  have childTerminal (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) :
      integerHalfCarry (wordSupport (child q hq hqS)) N = q := by
    let k := parent C q
    have hk : 1 ≤ k := explicitParent_pos hq
    have hkR : k ≤ R := explicitParent_le hqS hbuffer
    let a := W.word k hk hkR
    have hkcarry := W.terminal k hk hkR
    have hparentCarry :
        integerHalfCarry (wordSupport (child q hq hqS)) (N - 1) = k := by
      have hfuture := integerHalfCarry_insert_future_eq (wordSupport a)
        (show N - 1 + 2 ≤ N + 1 by omega)
      dsimp [child, a, k]
      rw [wordSupport_extendHalfWord]
      cases hbit : bit q
      · simpa [hbit] using hkcarry
      · simpa [hbit] using hfuture.trans hkcarry
    have hbaseCoeff :
        (supportCoeff (wordSupport a) (N + 1) : ℤ) = C := by
      have hp := hp_common k hk hkR
      simpa [a, selectedRowCoeff, hk, hkR] using hp
    have hcoeff :
        (supportCoeff (wordSupport (child q hq hqS)) (N + 1) : ℤ) =
          C + explicitParentBitZ C q := by
      rcases explicitParentBitZ_zero_or_one C q with hb | hb
      · have hbit : bit q = false := by simp [bit, hb]
        have hsupp : wordSupport (child q hq hqS) = wordSupport a := by
          change wordSupport (extendHalfWord a (bit q)) = wordSupport a
          rw [wordSupport_extendHalfWord]
          simp [hbit]
        rw [hsupp]
        simpa [hb] using hbaseCoeff
      · have hbit : bit q = true := by simp [bit, hb]
        have hsupp : wordSupport (child q hq hqS) =
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
      (wordSupport (child q hq hqS)) (N - 1)
    simp only [show N - 1 + 1 = N by omega,
      show N - 1 + 2 = N + 1 by omega] at hrec
    calc
      integerHalfCarry (wordSupport (child q hq hqS)) N =
          2 * integerHalfCarry (wordSupport (child q hq hqS)) (N - 1) -
            (supportCoeff (wordSupport (child q hq hqS)) (N + 1) : ℤ) := hrec
      _ = 2 * (k : ℤ) - (C + explicitParentBitZ C q) := by
        rw [hparentCarry, hcoeff]
      _ = q := by
        dsimp [k]
        rw [explicitParent_recurrence C q]
        ring
  let next : SelectedHalfWindow (N + 1) S := {
    word := child
    admissible := by
      intro q hq hqS
      let k := parent C q
      have hk : 1 ≤ k := explicitParent_pos hq
      have hkR : k ≤ R := explicitParent_le hqS hbuffer
      let a := W.word k hk hkR
      have ha := W.admissible k hk hkR
      apply HalfStripAdmissible.extend hN ha
      rw [childTerminal q hq hqS]
      exact ⟨by exact_mod_cast hq, by exact_mod_cast hqS.trans hSstrip⟩
    terminal := by
      intro q hq hqS
      simpa [show N + 1 - 1 = N by omega] using childTerminal q hq hqS
  }
  refine ⟨next, ?_⟩
  intro q hq hqS
  change restrictWord (Nat.le_succ N) (child q hq hqS) =
    W.word (parent C q) (explicitParent_pos hq)
      (explicitParent_le hqS hbuffer)
  dsimp only [child]
  exact restrictWord_extendHalfWord _ _

/-- Data-only projection of the explicit-parent successor. -/
noncomputable def SelectedHalfWindow.stepExplicit
    {N R S C : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hSstrip : S ≤ halfStripBound (N + 1))
    (hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ R →
      selectedRowCoeff W k = C)
    (hbuffer : S + C ≤ 2 * R) :
    SelectedHalfWindow (N + 1) S :=
  (W.stepExplicitWithHistory hN hSstrip hp_common hbuffer).window

/-- One-step restriction provenance for the public explicit constructor. -/
theorem SelectedHalfWindow.restrictWord_stepExplicit
    {N R S C : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hSstrip : S ≤ halfStripBound (N + 1))
    (hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ R →
      selectedRowCoeff W k = C)
    (hbuffer : S + C ≤ 2 * R)
    (q : ℕ) (hq : 1 ≤ q) (hqS : q ≤ S) :
    restrictWord (Nat.le_succ N)
        ((W.stepExplicit hN hSstrip hp_common hbuffer).word q hq hqS) =
      W.word (parent C q) (explicitParent_pos hq)
        (explicitParent_le hqS hbuffer) := by
  exact (W.stepExplicitWithHistory hN hSstrip hp_common hbuffer).restrict_parent
    q hq hqS

/-- All selected representatives have the same prefix at cutoff `M`. -/
def SelectedHalfWindow.CommonRestrictionAt
    {M N R : ℕ} (W : SelectedHalfWindow N R) (hMN : M ≤ N) : Prop :=
  ∃ a : HalfWord M, ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
    restrictWord hMN (W.word k hk hkR) = a

/-- A common restriction beyond the half-depth cutoff forces the exact
next-row divisor-membership agreement required by `selectedRowCoeff_eq`.
Every proper divisor of `N + 1` is at most `(N + 1) / 2`; the remaining
divisor `N + 1` is absent from every depth-`N` word. -/
theorem SelectedHalfWindow.nextRowDivisorAgreement_of_commonRestriction
    {M N R : ℕ} (W : SelectedHalfWindow N R) (hMN : M ≤ N)
    (hhalf : (N + 1) / 2 ≤ M)
    (hcommon : W.CommonRestrictionAt hMN) :
    W.NextRowDivisorAgreement := by
  obtain ⟨a, ha⟩ := hcommon
  intro k hk hkR ell hell hellR d hddiv
  by_cases hdM : d ≤ M
  · have hkset := congrArg wordSupport (ha k hk hkR)
    have hellset := congrArg wordSupport (ha ell hell hellR)
    rw [wordSupport_restrictWord] at hkset hellset
    have hkMem :
        d ∈ wordSupport (W.word k hk hkR) ∩ Set.Iic M ↔
          d ∈ wordSupport a := by
      rw [hkset]
    have hellMem :
        d ∈ wordSupport (W.word ell hell hellR) ∩ Set.Iic M ↔
          d ∈ wordSupport a := by
      rw [hellset]
    have hkMem' : d ∈ wordSupport (W.word k hk hkR) ↔
        d ∈ wordSupport a := by
      simpa [hdM] using hkMem
    have hellMem' : d ∈ wordSupport (W.word ell hell hellR) ↔
        d ∈ wordSupport a := by
      simpa [hdM] using hellMem
    exact hkMem'.trans hellMem'.symm
  · have habsent (w : HalfWord N) : d ∉ wordSupport w := by
      intro hdw
      rcases hdw with ⟨hdlt, -⟩
      have hdvd : d ∣ N + 1 := Nat.dvd_of_mem_divisors hddiv
      obtain ⟨e, he⟩ := hdvd
      have he0 : e ≠ 0 := by
        intro hez
        subst e
        simp at he
      have he1 : e ≠ 1 := by
        intro heo
        subst e
        simp at he
        omega
      have he2 : 2 ≤ e := by omega
      have hmul : d * 2 ≤ N + 1 := by
        rw [he]
        exact Nat.mul_le_mul_left d he2
      have hdhalf : d ≤ (N + 1) / 2 :=
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 hmul
      exact hdM (hdhalf.trans hhalf)
    constructor
    · intro hdk
      exact (habsent (W.word k hk hkR) hdk).elim
    · intro hdell
      exact (habsent (W.word ell hell hellR) hdell).elim

/-- Composed one-step provenance, stated without exposing dependent bound
proofs.  Every selected word restricts to the base representative indexed by
its exact closed-form rewind ancestor. -/
def SelectedHalfWindow.HasRewindRestrictionAt
    {M N R₀ R : ℕ} (W : SelectedHalfWindow N R)
    (W₀ : SelectedHalfWindow M R₀) (hMN : M ≤ N) (cs : List ℕ) : Prop :=
  ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
    ∃ hpos : 1 ≤ rewind cs k, ∃ hbound : rewind cs k ≤ R₀,
      restrictWord hMN (W.word k hk hkR) =
        W₀.word (rewind cs k) hpos hbound

/-- Dependent proof arguments to `word` are irrelevant once the carry index
is identified. -/
theorem SelectedHalfWindow.word_eq_of_index_eq
    {N R k ell : ℕ} (W : SelectedHalfWindow N R) (h : k = ell)
    (hk : 1 ≤ k) (hkR : k ≤ R) (hell : 1 ≤ ell) (hellR : ell ≤ R) :
    W.word k hk hkR = W.word ell hell hellR := by
  subst ell
  rfl

/-- Reflexive rewind provenance at an empty coefficient history. -/
theorem SelectedHalfWindow.hasRewindRestrictionAt_nil
    {N R : ℕ} (W : SelectedHalfWindow N R) :
    W.HasRewindRestrictionAt W (le_refl N) [] := by
  intro k hk hkR
  refine ⟨?_, ?_, ?_⟩
  · simpa [rewind] using hk
  · simpa [rewind] using hkR
  · simp [rewind]

/-- One history-bearing explicit successor conses its coefficient onto exact
rewind provenance. -/
theorem SelectedHalfWindow.FixedCoeffSuccessor.hasRewindRestrictionAt_cons
    {M N R₀ R S C : ℕ} (W₀ : SelectedHalfWindow M R₀)
    (W : SelectedHalfWindow N R) (hMN : M ≤ N) (cs : List ℕ)
    (hbuffer : S + C ≤ 2 * R)
    (next : W.FixedCoeffSuccessor hbuffer)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs) :
    next.window.HasRewindRestrictionAt W₀
      (hMN.trans (Nat.le_succ N)) (C :: cs) := by
  intro q hq hqS
  let k := parent C q
  have hk : 1 ≤ k := explicitParent_pos hq
  have hkR : k ≤ R := explicitParent_le hqS hbuffer
  obtain ⟨hpos, hbound, hrestrict⟩ := hprov k hk hkR
  have hpos' : 1 ≤ rewind (C :: cs) q := by
    simpa [rewind, k] using hpos
  have hbound' : rewind (C :: cs) q ≤ R₀ := by
    simpa [rewind, k] using hbound
  refine ⟨hpos', hbound', ?_⟩
  calc
    restrictWord (hMN.trans (Nat.le_succ N))
        (next.window.word q hq hqS) =
        restrictWord hMN
          (restrictWord (Nat.le_succ N) (next.window.word q hq hqS)) := by
      symm
      exact restrictWord_trans hMN (Nat.le_succ N) _
    _ = restrictWord hMN (W.word k hk hkR) := by
      rw [next.restrict_parent q hq hqS]
    _ = W₀.word (rewind cs k) hpos hbound := hrestrict
    _ = W₀.word (rewind (C :: cs) q) hpos' hbound' := by
      apply W₀.word_eq_of_index_eq
      simp [rewind, k]

/-- The public explicit-parent step preserves rewind provenance with the new
coefficient at the head of the history list. -/
theorem SelectedHalfWindow.hasRewindRestrictionAt_stepExplicit
    {M N R₀ R S C : ℕ} (W₀ : SelectedHalfWindow M R₀)
    (W : SelectedHalfWindow N R) (hMN : M ≤ N) (cs : List ℕ)
    (hN : 1 ≤ N) (hSstrip : S ≤ halfStripBound (N + 1))
    (hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ R →
      selectedRowCoeff W k = C)
    (hbuffer : S + C ≤ 2 * R)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs) :
    (W.stepExplicit hN hSstrip hp_common hbuffer).HasRewindRestrictionAt W₀
      (hMN.trans (Nat.le_succ N)) (C :: cs) := by
  simpa [SelectedHalfWindow.stepExplicit] using
    (SelectedHalfWindow.FixedCoeffSuccessor.hasRewindRestrictionAt_cons
      W₀ W hMN cs hbuffer
      (W.stepExplicitWithHistory hN hSstrip hp_common hbuffer) hprov)

/-- If the rewind map is constant on the protected interval, composed
provenance supplies one literal common prefix. -/
theorem SelectedHalfWindow.commonRestrictionAt_of_rewind_singleton
    {M N R₀ R : ℕ} (W : SelectedHalfWindow N R)
    (W₀ : SelectedHalfWindow M R₀) (hMN : M ≤ N) (cs : List ℕ)
    (hR : 1 ≤ R)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hsingle : ∀ k : ℕ, 1 ≤ k → k ≤ R →
      rewind cs k = rewind cs 1) :
    W.CommonRestrictionAt hMN := by
  obtain ⟨h1pos, h1bound, h1eq⟩ := hprov 1 (by omega) hR
  refine ⟨W₀.word (rewind cs 1) h1pos h1bound, ?_⟩
  intro k hk hkR
  obtain ⟨hkpos, hkbound, hkeq⟩ := hprov k hk hkR
  have hrew := hsingle k hk hkR
  exact hkeq.trans
    (W₀.word_eq_of_index_eq hrew hkpos hkbound h1pos h1bound)

/-- Complete singleton fan-in: exact rewind provenance and the arithmetic
singleton branch imply common next-row proper-divisor coefficients through
the existing live interface. -/
theorem SelectedHalfWindow.nextRowDivisorAgreement_of_rewind_singleton
    {M N R₀ R : ℕ} (W : SelectedHalfWindow N R)
    (W₀ : SelectedHalfWindow M R₀) (hMN : M ≤ N) (cs : List ℕ)
    (hhalf : (N + 1) / 2 ≤ M) (hR : 1 ≤ R)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hsingle : ∀ k : ℕ, 1 ≤ k → k ≤ R →
      rewind cs k = rewind cs 1) :
    W.NextRowDivisorAgreement :=
  W.nextRowDivisorAgreement_of_commonRestriction hMN hhalf
    (W.commonRestrictionAt_of_rewind_singleton W₀ hMN cs hR hprov hsingle)

/-- Exact phase-fit fan-in from a composed history to the live common
coefficient interface. -/
theorem SelectedHalfWindow.nextRowDivisorAgreement_of_rewind_phaseFit
    {M N R₀ R : ℕ} (W : SelectedHalfWindow N R)
    (W₀ : SelectedHalfWindow M R₀) (hMN : M ≤ N) (cs : List ℕ)
    (hhalf : (N + 1) / 2 ≤ M) (hR : 1 ≤ R)
    (hwidth : R ≤ denom cs)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hphase : phase cs + (R - 1) < denom cs) :
    W.NextRowDivisorAgreement := by
  apply W.nextRowDivisorAgreement_of_rewind_singleton W₀ hMN cs hhalf hR hprov
  exact (rewind_interval_singleton_iff_phase_fit cs hR hwidth).2 hphase

/-- The exact arithmetic history alternative before semantic seam
identification. -/
def SelectedHalfWindow.ScalarHistoryAlternative
    {N R : ℕ} (W : SelectedHalfWindow N R) (cs : List ℕ) : Prop :=
  W.NextRowDivisorAgreement ∨ IsSeamPair cs R

/-- A sufficiently long exact rewind either lands in the live
common-coefficient interface or leaves precisely two adjacent scalar
ancestors. -/
theorem SelectedHalfWindow.scalarHistoryAlternative_of_rewindHistory
    {M N R₀ R : ℕ} (W : SelectedHalfWindow N R)
    (W₀ : SelectedHalfWindow M R₀) (hMN : M ≤ N) (cs : List ℕ)
    (hhalf : (N + 1) / 2 ≤ M) (hR : 1 ≤ R)
    (hwidth : R ≤ denom cs)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs) :
    W.ScalarHistoryAlternative cs := by
  rcases rewind_singleton_or_isSeamPair cs hR hwidth with hsingle | hseam
  · exact Or.inl
      (W.nextRowDivisorAgreement_of_rewind_singleton
        W₀ hMN cs hhalf hR hprov hsingle)
  · exact Or.inr hseam

/-- Once the adjacent scalar ancestors are identified with the actual
canonical one-hole seam at row `N + 1`, the existing object-level history
alternative follows with no further arithmetic work. -/
theorem SelectedHalfWindow.historyAlternative_of_rewindHistory
    {M N R₀ R : ℕ} (W : SelectedHalfWindow N R)
    (W₀ : SelectedHalfWindow M R₀) (hMN : M ≤ N) (cs : List ℕ)
    (hhalf : (N + 1) / 2 ≤ M) (hR : 1 ≤ R)
    (hwidth : R ≤ denom cs)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hseamBridge : IsSeamPair cs R →
      ∃ d : ℕ, ∃ δ c : ℤ,
        N + 1 = 2 * d ∧ IsCanonicalEvenSeam d δ c) :
    W.HistoryAlternative := by
  rcases W.scalarHistoryAlternative_of_rewindHistory
      W₀ hMN cs hhalf hR hwidth hprov with hagree | hpair
  · exact Or.inl hagree
  · exact Or.inr (hseamBridge hpair)

/-- Public object-level one-step theorem.  Unlike `stepOpaque`, this route
uses the canonical parent and therefore has the provenance theorem above. -/
noncomputable def SelectedHalfWindow.step
    {N R S C : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (_hR : 1 ≤ R) (_hS : 1 ≤ S)
    (hSstrip : S ≤ halfStripBound (N + 1))
    (hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ R →
      selectedRowCoeff W k = C)
    (hbuffer : S + C ≤ 2 * R) :
    SelectedHalfWindow (N + 1) S :=
  W.stepExplicit hN hSstrip hp_common hbuffer

/-- A coherent next-row divisor cylinder advances the entire square-root
strip.  The carry-`1` representative supplies the common coefficient; the
sharp divisor envelope and strip-headroom theorem discharge the scalar
buffer required by `SelectedHalfWindow.step`. -/
noncomputable def SelectedHalfWindow.stepOfAgreement
    {N : ℕ} (hN : 1 ≤ N)
    (W : SelectedHalfWindow N (halfStripBound N))
    (hagree : W.NextRowDivisorAgreement) :
    SelectedHalfWindow (N + 1) (halfStripBound (N + 1)) := by
  have hR : 1 ≤ halfStripBound N := by
    unfold halfStripBound
    omega
  have hS : 1 ≤ halfStripBound (N + 1) := by
    unfold halfStripBound
    omega
  let a₁ := W.word 1 (by omega) hR
  let C : ℕ := supportCoeff (wordSupport a₁) (N + 1)
  apply W.step hN hR hS le_rfl (C := C)
  · intro k hk hkR
    calc
      selectedRowCoeff W k = selectedRowCoeff W 1 :=
        W.selectedRowCoeff_eq hagree hk hkR (by omega) hR
      _ = C := by
        rw [selectedRowCoeff, dif_pos ⟨show 1 ≤ (1 : ℕ) by omega, hR⟩]
  · have hC : C ≤ 2 * Nat.sqrt (N + 1) := by
      exact supportCoeff_le_two_mul_sqrt (wordSupport a₁) (N + 1)
    simpa using halfStripBound_add_coeff_le_two_mul_pred
      (n := N + 1) (c := C) (by omega) hC

/-! ## Iteration and compactness adapter -/

/-- Iterate a data-producing selected-window step by an explicit number of
rows.  Using a data definition here (rather than Prop induction) preserves the
actual chosen words needed by the next coefficient row. -/
noncomputable def selectedHalfWindowIterate
    (N₀ : ℕ) (R : ℕ → ℕ)
    (hbase : SelectedHalfWindow N₀ (R N₀))
    (hstep : ∀ N : ℕ, N₀ ≤ N → SelectedHalfWindow N (R N) →
      SelectedHalfWindow (N + 1) (R (N + 1))) :
    (d : ℕ) → SelectedHalfWindow (N₀ + d) (R (N₀ + d))
  | 0 => by simpa using hbase
  | d + 1 => by
      have hnext := hstep (N₀ + d) (by omega)
        (selectedHalfWindowIterate N₀ R hbase hstep d)
      simpa [Nat.add_assoc] using hnext

/-- Protected selected windows at all sufficiently large levels imply the
landed minimal producer interface.  Only one representative (carry `1`) is
needed at each chosen level. -/
theorem cofinalAdmissibility_of_selectedHalfWindows
    (N₀ : ℕ) (R : ℕ → ℕ)
    (hR : ∀ N : ℕ, N₀ ≤ N → 1 ≤ R N)
    (hwindow : ∀ N : ℕ, N₀ ≤ N → SelectedHalfWindow N (R N)) :
    HalfCarryCofinalAdmissibility := by
  intro N
  let M := max N N₀
  have hNM : N ≤ M := le_max_left _ _
  have hN₀M : N₀ ≤ M := le_max_right _ _
  let W := hwindow M hN₀M
  have hRM : 1 ≤ R M := hR M hN₀M
  let a := W.word 1 (by omega) hRM
  exact ⟨M, hNM, a, W.admissible 1 (by omega) hRM⟩

/-- Packaged forward-induction route to the exact half-sum theorem's minimal
cofinal producer. -/
theorem cofinalAdmissibility_of_selectedHalfWindow_induction
    (N₀ : ℕ) (R : ℕ → ℕ)
    (hR : ∀ N : ℕ, N₀ ≤ N → 1 ≤ R N)
    (hbase : SelectedHalfWindow N₀ (R N₀))
    (hstep : ∀ N : ℕ, N₀ ≤ N → SelectedHalfWindow N (R N) →
      SelectedHalfWindow (N + 1) (R (N + 1))) :
    HalfCarryCofinalAdmissibility := by
  intro N
  let M := N₀ + N
  let W := selectedHalfWindowIterate N₀ R hbase hstep N
  have hN₀M : N₀ ≤ M := by simp [M]
  have hRM : 1 ≤ R M := hR M hN₀M
  let a := W.word 1 (by omega) hRM
  exact ⟨M, by simp [M], a, W.admissible 1 (by omega) hRM⟩

/-- A supply of selected protected windows already yields an infinite support
whose Mersenne achievement sum is exactly `1/2`. -/
theorem exists_infinite_support_half_of_selectedHalfWindows
    (N₀ : ℕ) (R : ℕ → ℕ)
    (hR : ∀ N : ℕ, N₀ ≤ N → 1 ≤ R N)
    (hwindow : ∀ N : ℕ, N₀ ≤ N → SelectedHalfWindow N (R N)) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_cofinalAdmissibility
    (cofinalAdmissibility_of_selectedHalfWindows N₀ R hR hwindow)

/-- A base selected window plus a forward selected-window induction closes
the exact infinite half-sum endpoint directly. -/
theorem exists_infinite_support_half_of_selectedHalfWindow_induction
    (N₀ : ℕ) (R : ℕ → ℕ)
    (hR : ∀ N : ℕ, N₀ ≤ N → 1 ≤ R N)
    (hbase : SelectedHalfWindow N₀ (R N₀))
    (hstep : ∀ N : ℕ, N₀ ≤ N → SelectedHalfWindow N (R N) →
      SelectedHalfWindow (N + 1) (R (N + 1))) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_cofinalAdmissibility
    (cofinalAdmissibility_of_selectedHalfWindow_induction
      N₀ R hR hbase hstep)

#print axioms protectedChild_cover_Icc_of_constant
#print axioms HalfStripAdmissible.extend
#print axioms supportCoeff_eq_of_divisorAgreement
#print axioms SelectedHalfWindow.selectedRowCoeff_eq
#print axioms SelectedHalfWindow.HistoryAlternative
#print axioms explicitParent_pos
#print axioms explicitParent_le
#print axioms explicitParentBitZ_zero_or_one
#print axioms explicitParent_recurrence
#print axioms SelectedHalfWindow.FixedCoeffSuccessor
#print axioms SelectedHalfWindow.stepExplicitWithHistory
#print axioms SelectedHalfWindow.stepExplicit
#print axioms SelectedHalfWindow.restrictWord_stepExplicit
#print axioms SelectedHalfWindow.CommonRestrictionAt
#print axioms SelectedHalfWindow.nextRowDivisorAgreement_of_commonRestriction
#print axioms SelectedHalfWindow.HasRewindRestrictionAt
#print axioms SelectedHalfWindow.word_eq_of_index_eq
#print axioms SelectedHalfWindow.hasRewindRestrictionAt_nil
#print axioms SelectedHalfWindow.FixedCoeffSuccessor.hasRewindRestrictionAt_cons
#print axioms SelectedHalfWindow.hasRewindRestrictionAt_stepExplicit
#print axioms SelectedHalfWindow.commonRestrictionAt_of_rewind_singleton
#print axioms SelectedHalfWindow.nextRowDivisorAgreement_of_rewind_singleton
#print axioms SelectedHalfWindow.nextRowDivisorAgreement_of_rewind_phaseFit
#print axioms SelectedHalfWindow.ScalarHistoryAlternative
#print axioms SelectedHalfWindow.scalarHistoryAlternative_of_rewindHistory
#print axioms SelectedHalfWindow.historyAlternative_of_rewindHistory
#print axioms SelectedHalfWindow.step
#print axioms SelectedHalfWindow.stepOfAgreement
#print axioms selectedHalfWindowIterate
#print axioms cofinalAdmissibility_of_selectedHalfWindows
#print axioms cofinalAdmissibility_of_selectedHalfWindow_induction
#print axioms exists_infinite_support_half_of_selectedHalfWindows
#print axioms exists_infinite_support_half_of_selectedHalfWindow_induction

end Erdos249257.HalfCarrySelectedWindow
