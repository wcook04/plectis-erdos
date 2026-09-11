import Erdos249257.LcmConeNonflat
import Mathlib.Tactic

/-!
# Sharp prime-jump four-vertex window

This file proves the direct finite consumer for
`D(pH) - p D(H)`.  Its exact deep-tail radius is
`3 * p * H + (p + 1) * (L + 2)`, not the larger `4pH` radius belonging
to the two-cell disjunction.  An unbounded supply theorem is exposed as a
conditional socket; no such supply and no resolution of Erdős #249 is claimed.
-/

namespace Erdos249257.PrimeJumpWindow

open TotientTailPeriodKiller

/-! ## Direct four-vertex window -/

/-- The diagonal tail difference `D(H) = R_(2H) - R_H`. -/
noncomputable def diagonalTailDifferenceAt (H : ℕ) : ℝ :=
  totientTail (2 * H) - totientTail H

/-- The prime-jump commutator `J(H,p) = D(pH) - p D(H)`. -/
noncomputable def primeJumpTailCommutator (H p : ℕ) : ℝ :=
  diagonalTailDifferenceAt (p * H) - p * diagonalTailDifferenceAt H

/-- Integer depth-`L` numerator of the four-vertex commutator, with vertices
ordered as `H, 2H, pH, 2pH`. -/
def primeJumpWindowCommutator (H p L : ℕ) : ℤ :=
  (windowNumerator (2 * p * H) L : ℤ) -
    (windowNumerator (p * H) L : ℤ) -
    p * (windowNumerator (2 * H) L : ℤ) +
    p * (windowNumerator H L : ℤ)

/-- Exact direct tail radius for the four-vertex commutator. -/
def primeJumpSharpRadius (H p L : ℕ) : ℤ :=
  3 * p * H + (p + 1) * (L + 2)

/-- Decidable direct consumer: the four-vertex window stays outside the sharp
tail band around the integer lattice. -/
def primeJumpSharpKill (H p L : ℕ) : Prop :=
  primeJumpSharpRadius H p L <
      primeJumpWindowCommutator H p L % 2 ^ L ∧
    primeJumpWindowCommutator H p L % 2 ^ L <
      2 ^ L - primeJumpSharpRadius H p L

instance (H p L : ℕ) : Decidable (primeJumpSharpKill H p L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Generic modular soundness lemma for an integer window with a real
remainder bounded after multiplication by `2^L`. -/
theorem notMem_int_of_window_remainder_bound
    {x e : ℝ} {A R : ℤ} {L : ℕ}
    (hsplit : x = (A : ℝ) / 2 ^ L + e)
    (hbound : |e * 2 ^ L| ≤ (R : ℝ))
    (hleft : R < A % 2 ^ L)
    (hright : A % 2 ^ L < 2 ^ L - R) :
    x ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨k, hk⟩
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hmulk : ((k : ℤ) : ℝ) * 2 ^ L = (A : ℝ) + e * 2 ^ L := by
    rw [hk, hsplit, add_mul, div_mul_cancel₀ _ h2L.ne']
  have hAk : (A : ℝ) - ((k : ℤ) : ℝ) * 2 ^ L = -(e * 2 ^ L) := by
    linarith [hmulk]
  have habs : |(A : ℝ) - ((k : ℤ) : ℝ) * 2 ^ L| ≤ (R : ℝ) := by
    rw [hAk, abs_neg]
    exact hbound
  have hint : |A - k * 2 ^ L| ≤ R := by exact_mod_cast habs
  set P : ℤ := 2 ^ L with hP
  have hPpos : (0 : ℤ) < P := by rw [hP]; positivity
  set y : ℤ := A - k * P with hy
  have hymod : y % P = A % P := by
    have hrw : y = A + P * (-k) := by rw [hy]; ring
    rw [hrw, Int.add_mul_emod_self_left]
  have hdm : P * (y / P) + A % P = y := by
    rw [← hymod]
    exact Int.mul_ediv_add_emod y P
  have habs' := abs_le.mp hint
  by_cases ht : 0 ≤ y / P
  · have hge : 0 ≤ P * (y / P) := mul_nonneg hPpos.le ht
    linarith [hleft, habs'.2, hdm, hge]
  · have ht1 : y / P ≤ -1 := by
      have h0 : y / P < 0 := not_le.mp ht
      linarith [Int.lt_iff_add_one_le.mp h0]
    have hle : P * (y / P) ≤ P * (-1) :=
      mul_le_mul_of_nonneg_left ht1 hPpos.le
    linarith [hright, habs'.1, hdm, hle]

/-- Exact partial-window decomposition of the prime-jump commutator. -/
theorem primeJumpTailCommutator_eq_window_add_remainder (H p L : ℕ) :
    ∃ e : ℝ,
      primeJumpTailCommutator H p =
        (primeJumpWindowCommutator H p L : ℝ) / 2 ^ L + e ∧
      |e * 2 ^ L| ≤ (primeJumpSharpRadius H p L : ℝ) := by
  have hdec2p := totientTail_eq_partial_add_tail (2 * p * H) L
  have hdecp := totientTail_eq_partial_add_tail (p * H) L
  have hdec2 := totientTail_eq_partial_add_tail (2 * H) L
  have hdec1 := totientTail_eq_partial_add_tail H L
  have hnum2p := windowNumerator_div_eq (2 * p * H) L
  have hnump := windowNumerator_div_eq (p * H) L
  have hnum2 := windowNumerator_div_eq (2 * H) L
  have hnum1 := windowNumerator_div_eq H L
  set T2p := ∑' j : ℕ,
    (Nat.totient (2 * p * H + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
  set Tp := ∑' j : ℕ,
    (Nat.totient (p * H + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
  set T2 := ∑' j : ℕ,
    (Nat.totient (2 * H + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
  set T1 := ∑' j : ℕ,
    (Nat.totient (H + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
  let e : ℝ := T2p - Tp - p * T2 + p * T1
  refine ⟨e, ?_, ?_⟩
  · unfold primeJumpTailCommutator diagonalTailDifferenceAt
    rw [show 2 * (p * H) = 2 * p * H by ring]
    rw [hdec2p, hdecp, hdec2, hdec1, ← hnum2p, ← hnump, ← hnum2, ← hnum1]
    unfold primeJumpWindowCommutator
    dsimp [e, T2p, Tp, T2, T1]
    push_cast
    ring
  · have h2L : (0 : ℝ) < 2 ^ L := by positivity
    have hT2pn := tail_after_nonneg (2 * p * H) L
    have hTpn := tail_after_nonneg (p * H) L
    have hT2n := tail_after_nonneg (2 * H) L
    have hT1n := tail_after_nonneg H L
    have hT2pu := tail_after_le (2 * p * H) L
    have hTpu := tail_after_le (p * H) L
    have hT2u := tail_after_le (2 * H) L
    have hT1u := tail_after_le H L
    change 0 ≤ T2p at hT2pn
    change 0 ≤ Tp at hTpn
    change 0 ≤ T2 at hT2n
    change 0 ≤ T1 at hT1n
    change T2p ≤ _ at hT2pu
    change Tp ≤ _ at hTpu
    change T2 ≤ _ at hT2u
    change T1 ≤ _ at hT1u
    have h2p : T2p * 2 ^ L ≤ (2 * p * H : ℝ) + L + 2 := by
      have h := mul_le_mul_of_nonneg_right hT2pu h2L.le
      rw [div_mul_cancel₀ _ h2L.ne'] at h
      convert h using 1 <;> push_cast <;> ring
    have hp : Tp * 2 ^ L ≤ (p * H : ℝ) + L + 2 := by
      have h := mul_le_mul_of_nonneg_right hTpu h2L.le
      rw [div_mul_cancel₀ _ h2L.ne'] at h
      convert h using 1 <;> push_cast <;> ring
    have h2 : T2 * 2 ^ L ≤ (2 * H : ℝ) + L + 2 := by
      have h := mul_le_mul_of_nonneg_right hT2u h2L.le
      rw [div_mul_cancel₀ _ h2L.ne'] at h
      norm_num at h ⊢
      exact h
    have h1 : T1 * 2 ^ L ≤ (H : ℝ) + L + 2 := by
      have h := mul_le_mul_of_nonneg_right hT1u h2L.le
      rwa [div_mul_cancel₀ _ h2L.ne'] at h
    have hn2p : 0 ≤ T2p * 2 ^ L := mul_nonneg hT2pn h2L.le
    have hnp : 0 ≤ Tp * 2 ^ L := mul_nonneg hTpn h2L.le
    have hn2 : 0 ≤ T2 * 2 ^ L := mul_nonneg hT2n h2L.le
    have hn1 : 0 ≤ T1 * 2 ^ L := mul_nonneg hT1n h2L.le
    have hp0 : (0 : ℝ) ≤ p := by positivity
    have hpos : e * 2 ^ L ≤
        (3 * p * H + (p + 1) * (L + 2) : ℕ) := by
      dsimp [e]
      push_cast
      nlinarith
    have hneg : -(3 * p * H + (p + 1) * (L + 2) : ℕ) ≤
        e * 2 ^ L := by
      dsimp [e]
      push_cast
      nlinarith
    rw [abs_le]
    unfold primeJumpSharpRadius
    constructor
    · exact_mod_cast hneg
    · exact_mod_cast hpos

/-- **Sharp direct soundness.**  A central four-vertex residue proves that the
actual prime-jump commutator is nonintegral.  The radius is `3pH`, not the
larger two-cell disjunction radius `4pH`. -/
theorem primeJumpTailCommutator_notMem_int_of_sharpKill
    {H p L : ℕ} (hkill : primeJumpSharpKill H p L) :
    primeJumpTailCommutator H p ∉ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨e, hsplit, hbound⟩ :=
    primeJumpTailCommutator_eq_window_add_remainder H p L
  exact notMem_int_of_window_remainder_bound hsplit hbound hkill.1 hkill.2

/-- A concrete new-prime-jump deposit. -/
theorem primeJumpSharpKill_twelve_five : primeJumpSharpKill 12 5 15 := by
  set_option maxRecDepth 100000 in
    decide

/-- An unbounded supply of sharp prime-jump window kills on the LCM cone would
prove Erdős #249.  This is the exact remaining consumer socket; the supply is
not asserted here. -/
theorem irrational_totient_series_of_primeJumpSharpKill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ,
      0 < p ∧ primeJumpSharpKill (periodLcm t) p L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨t, ht, p, L, hp, hkill⟩ := hsupply t₁
  obtain ⟨a, ha⟩ := hflat t ht 1 1 (by omega)
  obtain ⟨b, hb⟩ := hflat t ht p p hp
  apply primeJumpTailCommutator_notMem_int_of_sharpKill hkill
  refine ⟨b - p * a, ?_⟩
  unfold primeJumpTailCommutator diagonalTailDifferenceAt
  push_cast
  rw [show 1 * periodLcm t + 1 * periodLcm t = 2 * periodLcm t by ring,
    one_mul] at ha
  rw [show p * periodLcm t + p * periodLcm t = 2 * (p * periodLcm t) by ring]
    at hb
  rw [← ha, ← hb]


#print axioms primeJumpTailCommutator_eq_window_add_remainder
#print axioms primeJumpTailCommutator_notMem_int_of_sharpKill
#print axioms irrational_totient_series_of_primeJumpSharpKill_supply

end Erdos249257.PrimeJumpWindow
