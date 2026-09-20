import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos269.BoundedRadixTailEscape

/-!
# Uniform separation of dyadic tail differences

The #251 classifier identifies irrationality with nonintegrality of every
positive-length tail difference. The #269 bounded-radix escape theorem turns
this qualitative statement into cofinal separation by a common positive
constant. The bridge is a change of representation: a fixed-length difference
of a dyadic tail orbit is itself an integer-digit dyadic orbit.

The constant `1 / 31` is inherited from the #269 theorem for radices at most
30; it is not asserted to be optimal for the radix-two specialization. This
composition proves no irrationality assertion about the actual prime series:
it gives an exact quantitative form of the existing irrationality criterion.
-/

namespace ErdosProblems.Synthesis.DyadicShiftEscape

open ErdosProblems.Erdos251 ErdosProblems.Erdos269

/-- Taking a fixed-length tail difference preserves the dyadic recurrence;
the new integer digit is the corresponding difference of old digits. -/
theorem realTailShift_recurrence
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ) :
    realTailShift T h (N + 1) =
      2 * realTailShift T h N -
        ((g (N + h + 1) - g (N + 1) : ℤ) : ℝ) := by
  unfold realTailShift
  rw [show N + 1 + h = N + h + 1 by omega, hrec (N + h), hrec N]
  push_cast
  ring

/-- The qualitative nonintegrality criterion from #251 discharges the
integral alternative in #269, leaving uniform cofinal separation. -/
theorem cofinal_separated_tailShifts_of_irrational
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (hirr : Irrational (T 0)) :
    ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ∀ z : ℤ, (1 : ℝ) / 31 ≤ |realTailShift T h N - (z : ℝ)| := by
  intro h hh
  have hshift : ∀ N : ℕ,
      realTailShift T h (N + 1) =
        ((fun _ : ℕ => 2) N : ℝ) * realTailShift T h N -
          ((g (N + h + 1) - g (N + 1) : ℤ) : ℝ) := by
    intro N
    simpa using realTailShift_recurrence hrec h N
  rcases boundedRadix_zero_or_cofinal_far
      (fun _ => 2) (fun N => g (N + h + 1) - g (N + 1))
      (fun N => realTailShift T h N)
      (fun _ => by norm_num) (fun _ => by norm_num) hshift with hint | hfar
  · rcases hint with ⟨N, z, hz⟩
    exact ((irrational_initial_iff_all_positive_tailShifts_nonintegral hrec).1
      hirr h hh N ⟨z, hz⟩).elim
  · exact hfar

/-- Exact quantitative form of the #251 dyadic-tail classifier. The common
separation constant is independent of the positive shift length. -/
theorem irrational_initial_iff_cofinal_separated_tailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
        ∀ z : ℤ, (1 : ℝ) / 31 ≤ |realTailShift T h N - (z : ℝ)| := by
  constructor
  · exact cofinal_separated_tailShifts_of_irrational hrec
  · intro hfar
    apply irrational_initial_of_cofinalNonintegralTailShifts hrec
    intro h hh N₀
    obtain ⟨N, hN, hsep⟩ := hfar h hh N₀
    refine ⟨N, hN, ?_⟩
    rintro ⟨z, hz⟩
    have hbad := hsep z
    rw [hz, sub_self, abs_zero] at hbad
    norm_num at hbad

#print axioms realTailShift_recurrence
#print axioms cofinal_separated_tailShifts_of_irrational
#print axioms irrational_initial_iff_cofinal_separated_tailShifts

end ErdosProblems.Synthesis.DyadicShiftEscape
