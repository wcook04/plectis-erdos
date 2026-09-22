import Erdos249257.AllBaseReciprocalSupportIrrationality

/-! # Irrationality from arbitrarily close radix returns -/
namespace ErdosProblems.Erdos257
open Erdos249257 Filter
noncomputable section

/-- The all-base lattice endgame accepts the close-return property itself.
The weighted and fractional returns need no reciprocal-summability premise. -/
theorem irrational_erdosSupportSeries_of_radix_closeReturn
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      (∑' d : ℕ, shiftedRadixSupportAtom b A N d) <
        (∑' d : ℕ, shiftedRadixSupportAtom b A 0 d) + ε) :
    Irrational (erdosSupportSeries b A) := by
  by_contra hrat
  have hvalue : HasRationalValue (erdosSupportSeries b A) :=
    (hasRationalValue_iff_not_irrational _).2 hrat
  obtain ⟨p, v, hv, hratValue⟩ := hvalue
  let T : ℕ → ℝ := fun N =>
    ∑' d : ℕ, shiftedRadixSupportAtom b A N d
  let u : ℕ → ℤ := Nat.rec p
    (fun N z => (b : ℤ) * z - ((v * supportCoeff A (N + 1) : ℕ) : ℤ))
  have hu0 : u 0 = p := rfl
  have huSucc : ∀ N : ℕ,
      u (N + 1) =
        (b : ℤ) * u N - ((v * supportCoeff A (N + 1) : ℕ) : ℤ) := by
    intro N
    rfl
  have hT0 : T 0 = erdosSupportSeries b A := by
    exact tsum_shiftedRadixSupportAtom_zero b A
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have huCast : ∀ N : ℕ, ((u N).cast : ℝ) = (v : ℝ) * T N := by
    intro N
    induction N with
    | zero =>
        rw [hu0, hT0, hratValue]
        field_simp
    | succ N ih =>
        rw [huSucc]
        push_cast
        rw [ih]
        have hstep := tsum_shiftedRadixSupportAtom_step b A N hb
        change (b : ℝ) * ((v : ℝ) * T N) -
            (v : ℝ) * supportCoeff A (N + 1) = (v : ℝ) * T (N + 1)
        change (b : ℝ) * T N - T (N + 1) =
            supportCoeff A (N + 1) at hstep
        nlinarith
  obtain ⟨N, hN, hnear⟩ :=
    hclose (1 / (v : ℝ)) (by positivity)
  have hstrict :=
    shiftedRadixSupportAtom_zero_strictMinimum b A hb hA N hN
  have hstrictT : T 0 < T N := by
    simpa [T] using hstrict
  have hnearT : T N < T 0 + 1 / (v : ℝ) := by
    simpa [T] using hnear
  have hgapPos : (0 : ℝ) < ((u N - u 0 : ℤ) : ℝ) := by
    push_cast
    rw [huCast N, huCast 0]
    nlinarith [mul_pos hvR (sub_pos.mpr hstrictT)]
  have hgapLt : ((u N - u 0 : ℤ) : ℝ) < 1 := by
    push_cast
    rw [huCast N, huCast 0]
    have htailGap : T N - T 0 < 1 / (v : ℝ) := by
      exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hnearT)
    have hmul := mul_lt_mul_of_pos_left htailGap hvR
    have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
    rw [show (v : ℝ) * (1 / (v : ℝ)) = 1 by field_simp] at hmul
    nlinarith
  have hgapPosInt : 0 < u N - u 0 := by exact_mod_cast hgapPos
  have hgapLtInt : u N - u 0 < 1 := by exact_mod_cast hgapLt
  omega

end
end ErdosProblems.Erdos257
