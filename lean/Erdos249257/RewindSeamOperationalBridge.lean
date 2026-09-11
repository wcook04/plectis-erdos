import Erdos249257.HalfCarrySelectedWindow
import Erdos249257.HalfCarryProtectedSeamConsumer

/-!
# Operational bridge from an exact rewind seam to a realized next-row seam

This module separates the arithmetic already forced by
`HasRewindRestrictionAt + IsSeamPair` from the one genuinely additional
object-level fact: the two adjacent base ancestors must have next-row
proper-divisor coefficients `c+1` and `c`.
-/

namespace Erdos249257.RewindSeamOperationalBridge

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.FixedCoeffRewind

/-- Last target carry which rewinds to the left ancestor. -/
def seamCut (cs : List ℕ) : ℕ := denom cs - phase cs

theorem phase_lt_denom (cs : List ℕ) : phase cs < denom cs := by
  exact Nat.mod_lt _ (denom_pos cs)

theorem seamCut_pos (cs : List ℕ) : 1 ≤ seamCut cs := by
  have hp := phase_lt_denom cs
  simp only [seamCut]
  omega

/-- The phase formula identifies the left side of the scalar seam exactly. -/
theorem rewind_eq_left_iff_le_seamCut
    (cs : List ℕ) {B k : ℕ}
    (hk : 1 ≤ k) (hkB : k ≤ B) (hwidth : B ≤ denom cs) :
    rewind cs k = rewind cs 1 ↔ k ≤ seamCut cs := by
  have hkD : k ≤ denom cs := hkB.trans hwidth
  have hp := phase_lt_denom cs
  constructor
  · intro heq
    have hfit :=
      (rewind_endpoint_eq_iff_phase_fit cs hk hkD).mp heq
    simp only [seamCut]
    omega
  · intro hkcut
    apply (rewind_endpoint_eq_iff_phase_fit cs hk hkD).2
    simp only [seamCut] at hkcut
    omega

/-- A genuine seam pair has a nonempty right side inside `[1,B]`. -/
theorem seamCut_lt_rightEndpoint
    (cs : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hwidth : B ≤ denom cs)
    (hseam : IsSeamPair cs B) :
    seamCut cs < B := by
  have hover :=
    (isSeamPair_iff_phase_overflow cs hB hwidth).mp hseam
  have hp := phase_lt_denom cs
  simp only [seamCut]
  omega

/-- Inside a seam pair, every target strictly after `seamCut` rewinds to the
right adjacent ancestor. -/
theorem rewind_eq_right_iff_seamCut_lt
    (cs : List ℕ) {B k : ℕ}
    (hk : 1 ≤ k) (hkB : k ≤ B) (hwidth : B ≤ denom cs)
    (hseam : IsSeamPair cs B) :
    rewind cs k = rewind cs 1 + 1 ↔ seamCut cs < k := by
  constructor
  · intro hright
    by_contra hnot
    have hkcut : k ≤ seamCut cs := by omega
    have hleft :=
      (rewind_eq_left_iff_le_seamCut cs hk hkB hwidth).2 hkcut
    omega
  · intro hkcut
    rcases rewind_eq_left_or_right_of_isSeamPair cs hk hkB hseam with
      hleft | hright
    · have hle :=
        (rewind_eq_left_iff_le_seamCut cs hk hkB hwidth).1 hleft
      omega
    · exact hright

/-- Equality of words after restriction beyond half-depth preserves the
next-row proper-divisor coefficient. -/
theorem supportCoeff_nextRow_eq_of_restriction
    {M N : ℕ} (hMN : M ≤ N) (hhalf : (N + 1) / 2 ≤ M)
    (a : HalfWord N) (b : HalfWord M)
    (hrestrict : restrictWord hMN a = b) :
    supportCoeff (wordSupport a) (N + 1) =
      supportCoeff (wordSupport b) (N + 1) := by
  apply supportCoeff_eq_of_divisorAgreement
  intro d hddiv
  by_cases hdM : d ≤ M
  · have hset := congrArg wordSupport hrestrict
    rw [wordSupport_restrictWord] at hset
    have hmem :
        d ∈ wordSupport a ∩ Set.Iic M ↔ d ∈ wordSupport b := by
      rw [hset]
    simpa [hdM] using hmem
  · have haAbsent : d ∉ wordSupport a := by
      intro hda
      rcases hda with ⟨hdlt, -⟩
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
    have hbAbsent : d ∉ wordSupport b := by
      intro hdb
      exact hdM (Nat.le_of_lt_succ hdb.1)
    simp [haAbsent, hbAbsent]

/-- The sole object-level datum not contained in a scalar rewind seam: at
the row being produced, the left adjacent base ancestor has coefficient
`c+1` and the right adjacent base ancestor has coefficient `c`. -/
def RewindBaseUnitDropAt
    {M R₀ : ℕ} (W₀ : SelectedHalfWindow M R₀)
    (n : ℕ) (cs : List ℕ) (c : ℕ) : Prop :=
  ∀ r (hr : 1 ≤ r) (hrR₀ : r ≤ R₀),
    (r = rewind cs 1 →
      supportCoeff (wordSupport (W₀.word r hr hrR₀)) n = c + 1) ∧
    (r = rewind cs 1 + 1 →
      supportCoeff (wordSupport (W₀.word r hr hrR₀)) n = c)

/-- Exact contribution of rewind provenance in the seam branch.  It turns a
two-coefficient fact about the adjacent base ancestors into the piecewise
coefficient profile of the live selected window. -/
theorem nextRow_profile_of_rewindSeam
    {M N R₀ R c : ℕ}
    (W₀ : SelectedHalfWindow M R₀) (W : SelectedHalfWindow N R)
    (hMN : M ≤ N) (hhalf : (N + 1) / 2 ≤ M) (cs : List ℕ)
    (hwidth : R ≤ denom cs)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hseam : IsSeamPair cs R)
    (hbaseProfile : RewindBaseUnitDropAt W₀ (N + 1) cs c) :
    ∀ h (hh : 1 ≤ h) (hhR : h ≤ R),
      supportCoeff (wordSupport (W.word h hh hhR)) (N + 1) =
        if h ≤ seamCut cs then c + 1 else c := by
  intro h hh hhR
  obtain ⟨hpos, hbound, hrestrict⟩ := hprov h hh hhR
  have htransfer := supportCoeff_nextRow_eq_of_restriction
    hMN hhalf (W.word h hh hhR)
      (W₀.word (rewind cs h) hpos hbound) hrestrict
  by_cases hcut : h ≤ seamCut cs
  · rw [if_pos hcut]
    have hrew :=
      (rewind_eq_left_iff_le_seamCut cs hh hhR hwidth).2 hcut
    exact htransfer.trans ((hbaseProfile (rewind cs h) hpos hbound).1 hrew)
  · rw [if_neg hcut]
    have hrew :=
      (rewind_eq_right_iff_seamCut_lt cs hh hhR hwidth hseam).2 (by omega)
    exact htransfer.trans ((hbaseProfile (rewind cs h) hpos hbound).2 hrew)

/-- One chosen parent word realizes either Boolean child at the next row. -/
theorem halfTerminalReachable_succ_of_selectedParent
    {N R h q C : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hh : 1 ≤ h) (hhR : h ≤ R)
    (hcoeff : supportCoeff (wordSupport (W.word h hh hhR)) (N + 1) = C)
    (β : Bool)
    (hq : (q : ℤ) = 2 * (h : ℤ) - (C : ℤ) - (if β then 1 else 0))
    (hqpos : 1 ≤ q) (hqstrip : q ≤ halfStripBound (N + 1)) :
    HalfTerminalReachable (N + 1) q := by
  let a := W.word h hh hhR
  let child := extendHalfWord a β
  have hparentCarry :
      integerHalfCarry (wordSupport child) (N - 1) = h := by
    have hfuture := integerHalfCarry_insert_future_eq (wordSupport a)
      (show N - 1 + 2 ≤ N + 1 by omega)
    dsimp [child]
    rw [wordSupport_extendHalfWord]
    cases β with
    | false => simpa [a] using W.terminal h hh hhR
    | true => simpa [a] using hfuture.trans (W.terminal h hh hhR)
  have hchildCoeff :
      (supportCoeff (wordSupport child) (N + 1) : ℤ) =
        (C : ℤ) + (if β then 1 else 0) := by
    dsimp [child]
    rw [wordSupport_extendHalfWord]
    cases β with
    | false => simp [a, hcoeff]
    | true =>
        rw [if_pos rfl]
        rw [Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_self
          _ (by omega)]
        · push_cast
          simp [a, hcoeff]
        · intro hmem
          rcases hmem with ⟨hlt, -⟩
          omega
  have hterminal : integerHalfCarry (wordSupport child) N = q := by
    have hrec := integerHalfCarry_succ (wordSupport child) (N - 1)
    simp only [show N - 1 + 1 = N by omega,
      show N - 1 + 2 = N + 1 by omega] at hrec
    rw [hrec, hparentCarry, hchildCoeff]
    omega
  refine ⟨child, ?_, ?_⟩
  · apply HalfStripAdmissible.extend hN (W.admissible h hh hhR) β
    rw [hterminal]
    exact ⟨by exact_mod_cast hqpos, by exact_mod_cast hqstrip⟩
  · simpa [show N + 1 - 1 = N by omega] using hterminal

/-- A two-valued next-row coefficient profile realizes the exact scalar
one-hole seam at the next depth.  The buffer is the usual selected-window
headroom, with `c+1` the larger of the two coefficients. -/
theorem protectedEvenSeamRealizedAt_succ_of_profile
    {N R S δ c : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hSstrip : S ≤ halfStripBound (N + 1)) (h27 : 27 ≤ S)
    (hbuffer : S + (c + 1) ≤ 2 * R)
    (hprofile : ∀ h (hh : 1 ≤ h) (hhR : h ≤ R),
      supportCoeff (wordSupport (W.word h hh hhR)) (N + 1) =
        if h ≤ δ then c + 1 else c) :
    ProtectedEvenSeamRealizedAt (N + 1) (δ : ℤ) (c : ℤ) := by
  intro q hq3 hq27 hreach
  have hqS : q ≤ S := hq27.trans h27
  have hqstrip : q ≤ halfStripBound (N + 1) := hqS.trans hSstrip
  have hbufferZ : (S : ℤ) + (c : ℤ) + 1 ≤ 2 * (R : ℤ) := by
    exact_mod_cast hbuffer
  have hqSZ : (q : ℤ) ≤ (S : ℤ) := by exact_mod_cast hqS
  rcases hreach with
      ⟨z, hzδ, hq0 | hq1⟩ | ⟨z, hδz, hq0 | hq1⟩
  · have hzpos : (1 : ℤ) ≤ z := by omega
    let h := z.toNat
    have hzcast : (h : ℤ) = z := by
      exact Int.toNat_of_nonneg (by omega)
    have hhZ : (1 : ℤ) ≤ (h : ℤ) := by simpa [hzcast] using hzpos
    have hh : 1 ≤ h := by exact_mod_cast hhZ
    have hhδZ : (h : ℤ) ≤ (δ : ℤ) := by simpa [hzcast] using hzδ
    have hhδ : h ≤ δ := by exact_mod_cast hhδZ
    have hhRZ : z ≤ (R : ℤ) := by omega
    have hhRZ' : (h : ℤ) ≤ (R : ℤ) := by simpa [hzcast] using hhRZ
    have hhR : h ≤ R := by exact_mod_cast hhRZ'
    have hcoeff := hprofile h hh hhR
    rw [if_pos hhδ] at hcoeff
    apply halfTerminalReachable_succ_of_selectedParent
      hN W hh hhR hcoeff false
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hzcast]
      omega
    · omega
    · exact hqstrip
  · have hzpos : (1 : ℤ) ≤ z := by omega
    let h := z.toNat
    have hzcast : (h : ℤ) = z := by
      exact Int.toNat_of_nonneg (by omega)
    have hhZ : (1 : ℤ) ≤ (h : ℤ) := by simpa [hzcast] using hzpos
    have hh : 1 ≤ h := by exact_mod_cast hhZ
    have hhδZ : (h : ℤ) ≤ (δ : ℤ) := by simpa [hzcast] using hzδ
    have hhδ : h ≤ δ := by exact_mod_cast hhδZ
    have hhRZ : z ≤ (R : ℤ) := by omega
    have hhRZ' : (h : ℤ) ≤ (R : ℤ) := by simpa [hzcast] using hhRZ
    have hhR : h ≤ R := by exact_mod_cast hhRZ'
    have hcoeff := hprofile h hh hhR
    rw [if_pos hhδ] at hcoeff
    apply halfTerminalReachable_succ_of_selectedParent
      hN W hh hhR hcoeff true
    · simp only [↓reduceIte]
      rw [hzcast]
      omega
    · omega
    · exact hqstrip
  · have hzpos : (1 : ℤ) ≤ z := by omega
    let h := z.toNat
    have hzcast : (h : ℤ) = z := by
      exact Int.toNat_of_nonneg (by omega)
    have hhZ : (1 : ℤ) ≤ (h : ℤ) := by simpa [hzcast] using hzpos
    have hh : 1 ≤ h := by exact_mod_cast hhZ
    have hδhZ : (δ : ℤ) < (h : ℤ) := by simpa [hzcast] using hδz
    have hδh : δ < h := by exact_mod_cast hδhZ
    have hhRZ : z ≤ (R : ℤ) := by omega
    have hhRZ' : (h : ℤ) ≤ (R : ℤ) := by simpa [hzcast] using hhRZ
    have hhR : h ≤ R := by exact_mod_cast hhRZ'
    have hcoeff := hprofile h hh hhR
    rw [if_neg (by omega : ¬ h ≤ δ)] at hcoeff
    apply halfTerminalReachable_succ_of_selectedParent
      hN W hh hhR hcoeff false
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hzcast]
      omega
    · omega
    · exact hqstrip
  · have hzpos : (1 : ℤ) ≤ z := by omega
    let h := z.toNat
    have hzcast : (h : ℤ) = z := by
      exact Int.toNat_of_nonneg (by omega)
    have hhZ : (1 : ℤ) ≤ (h : ℤ) := by simpa [hzcast] using hzpos
    have hh : 1 ≤ h := by exact_mod_cast hhZ
    have hδhZ : (δ : ℤ) < (h : ℤ) := by simpa [hzcast] using hδz
    have hδh : δ < h := by exact_mod_cast hδhZ
    have hhRZ : z ≤ (R : ℤ) := by omega
    have hhRZ' : (h : ℤ) ≤ (R : ℤ) := by simpa [hzcast] using hhRZ
    have hhR : h ≤ R := by exact_mod_cast hhRZ'
    have hcoeff := hprofile h hh hhR
    rw [if_neg (by omega : ¬ h ≤ δ)] at hcoeff
    apply halfTerminalReachable_succ_of_selectedParent
      hN W hh hhR hcoeff true
    · simp only [↓reduceIte]
      rw [hzcast]
      omega
    · omega
    · exact hqstrip

/-- Solver-facing threshold form in the existing `selectedRowCoeff`
coordinate.  This is the direct executable fan-in from a two-cylinder
selected window to the localized seam consumer. -/
theorem protectedEvenSeamRealizedAt_succ_of_selectedRowCoeff_threshold
    {N R S δ c : ℕ} (hN : 1 ≤ N) (W : SelectedHalfWindow N R)
    (hSstrip : S ≤ halfStripBound (N + 1)) (h27 : 27 ≤ S)
    (hbuffer : S + (c + 1) ≤ 2 * R)
    (hprofile : ∀ h (_hh : 1 ≤ h) (_hhR : h ≤ R),
      selectedRowCoeff W h =
        if h ≤ δ then ((c + 1 : ℕ) : ℤ) else (c : ℤ)) :
    ProtectedEvenSeamRealizedAt (N + 1) (δ : ℤ) (c : ℤ) := by
  apply protectedEvenSeamRealizedAt_succ_of_profile hN W hSstrip h27 hbuffer
  intro h hh hhR
  have hp := hprofile h hh hhR
  rw [selectedRowCoeff, dif_pos ⟨hh, hhR⟩] at hp
  by_cases hδ : h ≤ δ
  · rw [if_pos hδ] at hp ⊢
    exact_mod_cast hp
  · rw [if_neg hδ] at hp ⊢
    exact_mod_cast hp

/-- Operational seam fan-in.  Exact rewind provenance plus an actual scalar
seam pair produces a localized realized seam one row later, provided the
adjacent base ancestors have the required unit-drop next-row coefficient
profile.  No global `IsCanonicalEvenSeam` equivalence is needed. -/
theorem protectedEvenSeamRealizedAt_succ_of_rewindSeam
    {M N R₀ R S c : ℕ}
    (W₀ : SelectedHalfWindow M R₀) (W : SelectedHalfWindow N R)
    (hMN : M ≤ N) (hhalf : (N + 1) / 2 ≤ M) (cs : List ℕ)
    (hN : 1 ≤ N) (hwidth : R ≤ denom cs)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hseam : IsSeamPair cs R)
    (hSstrip : S ≤ halfStripBound (N + 1)) (h27 : 27 ≤ S)
    (hbuffer : S + (c + 1) ≤ 2 * R)
    (hbaseProfile : RewindBaseUnitDropAt W₀ (N + 1) cs c) :
    ProtectedEvenSeamRealizedAt (N + 1) (seamCut cs : ℤ) (c : ℤ) := by
  apply protectedEvenSeamRealizedAt_succ_of_profile hN W hSstrip h27 hbuffer
  exact nextRow_profile_of_rewindSeam W₀ W hMN hhalf cs hwidth
    hprov hseam hbaseProfile

/-- Full-strip specialization: the standard divisor envelope discharges the
buffer automatically.  Thus the only semantic input not already present in
`HasRewindRestrictionAt + IsSeamPair` is the unit coefficient drop between
the two adjacent base ancestors. -/
theorem protectedEvenSeamRealizedAt_succ_of_fullStrip_rewindSeam
    {M N R₀ c : ℕ}
    (W₀ : SelectedHalfWindow M R₀)
    (W : SelectedHalfWindow N (halfStripBound N))
    (hMN : M ≤ N) (hhalf : (N + 1) / 2 ≤ M) (cs : List ℕ)
    (hN : 1 ≤ N) (hwidth : halfStripBound N ≤ denom cs)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hseam : IsSeamPair cs (halfStripBound N))
    (h27 : 27 ≤ halfStripBound (N + 1))
    (hbaseProfile : RewindBaseUnitDropAt W₀ (N + 1) cs c) :
    ProtectedEvenSeamRealizedAt (N + 1) (seamCut cs : ℤ) (c : ℤ) := by
  have hR : 1 ≤ halfStripBound N := by
    unfold halfStripBound
    omega
  have hprofile := nextRow_profile_of_rewindSeam W₀ W hMN hhalf cs
    hwidth hprov hseam hbaseProfile
  have hcutOne : 1 ≤ seamCut cs := seamCut_pos cs
  have hcoeffOne := hprofile 1 (by omega) hR
  rw [if_pos hcutOne] at hcoeffOne
  let a₁ := W.word 1 (by omega) hR
  have hc : c + 1 ≤ 2 * Nat.sqrt (N + 1) := by
    rw [← hcoeffOne]
    exact supportCoeff_le_two_mul_sqrt (wordSupport a₁) (N + 1)
  have hbuffer :
      halfStripBound (N + 1) + (c + 1) ≤ 2 * halfStripBound N := by
    simpa using halfStripBound_add_coeff_le_two_mul_pred
      (n := N + 1) (c := c + 1) (by omega) hc
  exact protectedEvenSeamRealizedAt_succ_of_profile hN W le_rfl h27
    hbuffer hprofile

#print axioms seamCut_pos
#print axioms rewind_eq_left_iff_le_seamCut
#print axioms seamCut_lt_rightEndpoint
#print axioms rewind_eq_right_iff_seamCut_lt
#print axioms supportCoeff_nextRow_eq_of_restriction
#print axioms RewindBaseUnitDropAt
#print axioms nextRow_profile_of_rewindSeam
#print axioms halfTerminalReachable_succ_of_selectedParent
#print axioms protectedEvenSeamRealizedAt_succ_of_profile
#print axioms protectedEvenSeamRealizedAt_succ_of_selectedRowCoeff_threshold
#print axioms protectedEvenSeamRealizedAt_succ_of_rewindSeam
#print axioms protectedEvenSeamRealizedAt_succ_of_fullStrip_rewindSeam

end Erdos249257.RewindSeamOperationalBridge
