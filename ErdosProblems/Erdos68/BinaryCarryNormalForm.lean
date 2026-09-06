import ErdosProblems.Erdos68.DivisorFactorialCentre
import ErdosProblems.Erdos68.FiniteDefectAutomaton
import ErdosProblems.Erdos68.CanonicalFactorialDigits
import Mathlib.Tactic

/-!
# Erdős #68: the finite centre is a noncanonical factorial expansion

`DivisorFactorialCentre` builds a finite rational centre `F_m` with an exact
factorial-gap recurrence, and `CanonicalFactorialDigits` builds the canonical
remainder/digit pair of a real number.  The tempting identification of the two
is **false**, and this file both kills it and supplies the correct relation.

## The identification dies at `m = 2`

`residualCentre 2 = 1`, while every canonical remainder is strictly below `1`.
So `residualCentre` is not the canonical remainder of anything
(`residualCentre_two_ne_canonicalRemainder`).  What is missing is the positive
scaled infinite tail — and one Boolean bit.

## The correct relation

Write `δ_m` for the centre gap and `T_m` for the scaled tail.  With
`0 ≤ δ_m < 1` and `0 < T_m < 1` the sum `T_m - δ_m` lies in `(-1, 1)`, so the
integer lift's floor has exactly two possibilities and

`θ_m = T_m - δ_m + w_m`,  `w_m ∈ {0,1}`

(`fract_eq_tail_sub_gap_add_binary_wrap` — a pure floor computation, no
series).  Feeding that into the three recurrences (canonical remainder, scaled
tail, centre gap) makes every real term cancel and leaves the **integer**
identity

`d_m + q_m = 1 + m·w_{m-1} - w_m`   (`binary_coboundary_of_bridge`).

That is the carry-normalisation law of a mixed-radix factorial expansion: the
finite centre emits a *raw signed digit* `1 - d_m`, and the single bit `w_m`
normalises it to the canonical digit `q_m`.  Because each `w` is `0` or `1`,
the pointwise sum is confined to a four-symbol alphabet
(`digitSum_mem_four_symbol_alphabet`): the two digit streams cannot move
independently.

Dividing by `m!` telescopes the law into a quantised finite identity
(`binary_coboundary_telescope`), whose partial sums take only two values.

## Claim ceiling

**Erdős #68 remains open.**  Nothing here asserts irrationality.  The
identification of `T_m` with an actual scaled tail of the factorial-gap series
is an analytic statement about that series and is *not* part of this module:
every theorem below is an algebraic consequence of the stated recurrences.
-/

namespace ErdosProblems.Erdos68.BinaryCarryNormalForm

open ErdosProblems.Erdos68

/-! ## The identification is false -/

@[simp] theorem residualCentre_two : residualCentre 2 = 1 := by
  norm_num [residualCentre, residualCentreTerm]

/-- **The naive identification dies immediately.**  The finite centre at `m = 2`
equals `1`, but every canonical factorial remainder is strictly below `1`. -/
theorem residualCentre_two_ne_canonicalRemainder (x : ℝ) :
    ((residualCentre 2 : ℚ) : ℝ) ≠ canonicalRemainder x 2 := by
  rw [residualCentre_two]
  push_cast
  exact ne_of_gt (canonicalRemainder_lt_one x 2)

/-! ## The one-bit bridge -/

/-- **The floor has exactly two possibilities.**  If a real number splits as an
integer plus a value within one of an integer ceiling plus a tail in `(0,1)`,
its fractional part is the tail minus the gap, corrected by a single bit.  This
is a pure floor computation. -/
theorem fract_eq_tail_sub_gap_add_binary_wrap {x F T : ℝ} {A c : ℤ}
    (hx : x = (A : ℝ) + F + T)
    (hFc : F ≤ (c : ℝ)) (hcF : (c : ℝ) < F + 1)
    (hT0 : 0 < T) (hT1 : T < 1) :
    Int.fract x = T - ((c : ℝ) - F)
      + (((if T < (c : ℝ) - F then (1 : ℤ) else 0) : ℤ) : ℝ) := by
  have hδ0 : (0 : ℝ) ≤ (c : ℝ) - F := by linarith
  have hδ1 : (c : ℝ) - F < 1 := by linarith
  by_cases hwrap : T < (c : ℝ) - F
  · have hfloor : ⌊x⌋ = A + c - 1 := by
      rw [hx]
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast; linarith
    rw [Int.fract, hfloor, hx]
    simp only [hwrap, if_true]
    push_cast
    ring
  · have hge : (c : ℝ) - F ≤ T := le_of_not_gt hwrap
    have hfloor : ⌊x⌋ = A + c := by
      rw [hx]
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast; linarith
    rw [Int.fract, hfloor, hx]
    simp only [hwrap, if_false]
    push_cast
    ring

/-- **The carry-normalisation law.**  Given the canonical-remainder, scaled-tail
and centre-gap recurrences together with the one-bit bridge at two adjacent
indices, the two integer digit codes differ by a binary factorial coboundary.
Every real term cancels: this is an identity in `ℤ`. -/
theorem binary_coboundary_of_bridge
    {θ θ' T T' δ δ' ε : ℝ} {m : ℕ} {q d w w' : ℤ}
    (hθ : θ = (m : ℝ) * θ' - (q : ℝ))
    (hT : T = (m : ℝ) * T' - 1 - ε)
    (hδ : δ = (m : ℝ) * δ' - ε - (d : ℝ))
    (hbridge : θ = T - δ + (w : ℝ))
    (hbridgePred : θ' = T' - δ' + (w' : ℝ)) :
    d + q = 1 + (m : ℤ) * w' - w := by
  have hcast : ((d + q : ℤ) : ℝ) = ((1 + (m : ℤ) * w' - w : ℤ) : ℝ) := by
    push_cast
    nlinarith [hθ, hT, hδ, hbridge, hbridgePred]
  exact_mod_cast hcast

/-- **The four-symbol alphabet.**  Because each wrap bit is `0` or `1`, the
pointwise sum of the centre defect and the canonical digit is confined to
`{0, 1, m, m+1}`: the two digit streams cannot move independently. -/
theorem digitSum_mem_four_symbol_alphabet {m : ℕ} {q d w w' : ℤ}
    (hlaw : d + q = 1 + (m : ℤ) * w' - w)
    (hw : w = 0 ∨ w = 1) (hw' : w' = 0 ∨ w' = 1) :
    d + q = 0 ∨ d + q = 1 ∨ d + q = (m : ℤ) ∨ d + q = (m : ℤ) + 1 := by
  rcases hw with rfl | rfl <;> rcases hw' with rfl | rfl <;> omega

/-- **The telescoped conservation law.**  Dividing the coboundary law by `m!`
telescopes: every partial sum of the normalised defect stream is `-w_N / N!`,
so it takes only two values. -/
theorem binary_coboundary_telescope {θ θ' T T' δ δ' ε : ℝ} {m : ℕ} {q d w w' : ℤ}
    (hm : 1 ≤ m)
    (hθ : θ = (m : ℝ) * θ' - (q : ℝ))
    (hT : T = (m : ℝ) * T' - 1 - ε)
    (hδ : δ = (m : ℝ) * δ' - ε - (d : ℝ))
    (hbridge : θ = T - δ + (w : ℝ))
    (hbridgePred : θ' = T' - δ' + (w' : ℝ)) :
    ((d + q - 1 : ℤ) : ℝ) / (m.factorial : ℝ)
      = (w' : ℝ) / ((m - 1).factorial : ℝ) - (w : ℝ) / (m.factorial : ℝ) := by
  have hlaw := binary_coboundary_of_bridge hθ hT hδ hbridge hbridgePred
  have hfac : (m.factorial : ℝ) = (m : ℝ) * ((m - 1).factorial : ℝ) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [Nat.factorial_succ]
  have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hpredpos : (0 : ℝ) < ((m - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - 1)
  have hcast : ((d + q - 1 : ℤ) : ℝ) = (m : ℝ) * (w' : ℝ) - (w : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hlaw
    push_cast at this ⊢
    linarith
  rw [hcast, hfac]
  field_simp

end ErdosProblems.Erdos68.BinaryCarryNormalForm
