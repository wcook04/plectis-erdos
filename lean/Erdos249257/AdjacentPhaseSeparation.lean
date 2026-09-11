import Erdos249257.FirstHarmonicPivot
import Erdos249257.CarrySurvivorExtinction

/-!
# Adjacent phase separation is translated endpoint data

At fixed depth, the displacement between adjacent window discrepancies does
not introduce a second arithmetic sample.  Modulo `2^L` it is the original
window residue translated by the known final totient-difference letter, and
that translation is exactly invertible.

The main deterministic consequence is stronger than a two-point harmonic
argument: if the adjacent displacement lies in the robust central arc, the
certificate fires at the original base `N`.  The commonly proposed middle
third lies inside this robust arc under the standard room hypothesis.

The cofinal middle-third predicate is retained as a useful normal form, but
only its implication to irrationality is asserted here.  No unconditional
cofinal separation theorem is claimed.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

noncomputable section

/-- Canonical residue of the displacement between adjacent fixed-depth
window discrepancies. -/
def adjacentStepResidue (h N L : ℕ) : ℤ :=
  (windowDiscrepancy h (N + 1) L - windowDiscrepancy h N L) % (2 ^ L : ℤ)

/-- The adjacent residue lies in the closed middle third of the dyadic
circle. -/
def AdjacentMiddleThirdAt (h N L : ℕ) : Prop :=
  let P : ℤ := 2 ^ L
  let d := adjacentStepResidue h N L
  P ≤ 6 * d ∧ 6 * d ≤ 5 * P

/-- A wider adjacent arc that already forces the original endpoint
certificate. -/
def AdjacentCertificateArcAt (h N L : ℕ) : Prop :=
  let P : ℤ := 2 ^ L
  let W : ℤ := ((N + h + L + 2 : ℕ) : ℤ)
  let d := adjacentStepResidue h N L
  2 * W ≤ d ∧ d ≤ P - 2 * W

/-- Cofinal adjacent middle-third separation.  This is a normal form for a
possible certificate supply, not an unconditional theorem. -/
def DTWAdjacentMiddleThirdSeparation : Prop :=
  ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ,
    ∃ X L N : ℕ,
      max X₀ 1 ≤ X ∧
      X ≤ N ∧
      N + 1 < 2 * X ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      AdjacentMiddleThirdAt h N L

/-- Cofinal separation of an adjacent pair by the norm-square threshold
consumed by the two-point first-harmonic argument. -/
def DTWAdjacentPhaseSeparation : Prop :=
  ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ,
    ∃ X L N : ℕ,
      max X₀ 1 ≤ X ∧
      X ≤ N ∧
      N + 1 < 2 * X ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      (19 / 25 : ℝ) ≤
        ‖windowFirstExp h (N + 1) L - windowFirstExp h N L‖ ^ 2

/-- Sliding by one base point translates the old residue by exactly the
fresh endpoint letter. -/
theorem adjacentStepResidue_eq_translated_windowResidue (h N L : ℕ) :
    adjacentStepResidue h N L =
      (windowDiscrepancy h N L + deltaTotient h (N + L + 1)) % (2 ^ L : ℤ) := by
  unfold adjacentStepResidue
  rw [windowDiscrepancy_slide]
  have hrearrange :
      2 * windowDiscrepancy h N L - deltaTotient h (N + 1) * (2 : ℤ) ^ L
          + deltaTotient h (N + L + 1) - windowDiscrepancy h N L =
        (windowDiscrepancy h N L + deltaTotient h (N + L + 1)) +
          (2 : ℤ) ^ L * (-deltaTotient h (N + 1)) := by
    ring
  rw [hrearrange, Int.add_mul_emod_self_left]

/-- Exact inverse translation: the adjacent datum together with the known
endpoint letter reconstructs the original window residue. -/
theorem windowResidue_eq_adjacentStepResidue_sub_endpoint (h N L : ℕ) :
    windowDiscrepancy h N L % (2 ^ L : ℤ) =
      (adjacentStepResidue h N L - deltaTotient h (N + L + 1)) % (2 ^ L : ℤ) := by
  rw [adjacentStepResidue_eq_translated_windowResidue]
  have hmod :=
    (Int.mod_modEq
      (windowDiscrepancy h N L + deltaTotient h (N + L + 1))
      ((2 : ℤ) ^ L)).sub
        (Int.ModEq.refl (deltaTotient h (N + L + 1)))
  have heq := Int.ModEq.eq hmod
  simpa only [add_sub_cancel_right] using heq.symm

/-- The robust adjacent arc forces the original certificate at the same
base `N`. -/
theorem certifiedKill_of_adjacentCertificateArc {h N L : ℕ}
    (harc : AdjacentCertificateArcAt h N L) :
    certifiedKill h N L := by
  set P : ℤ := 2 ^ L
  set W : ℤ := ((N + h + L + 2 : ℕ) : ℤ)
  set d : ℤ := adjacentStepResidue h N L
  set e : ℤ := deltaTotient h (N + L + 1)
  change 2 * W ≤ d ∧ d ≤ P - 2 * W at harc
  rcases harc with ⟨hdlow, hdhigh⟩
  have heabs : |e| ≤ W - 1 := by
    have h := abs_deltaTotient_le h (N + L + 1)
    dsimp [e, W]
    push_cast at h ⊢
    omega
  have hebounds := abs_le.mp heabs
  have hWpos : 0 < W := by
    dsimp [W]
    positivity
  have hx0 : 0 ≤ d - e := by linarith
  have hxP : d - e < P := by linarith
  have hreconstruct := windowResidue_eq_adjacentStepResidue_sub_endpoint h N L
  change windowDiscrepancy h N L % P = (d - e) % P at hreconstruct
  rw [Int.emod_eq_of_lt hx0 hxP] at hreconstruct
  unfold certifiedKill
  change W < windowDiscrepancy h N L % P ∧
    windowDiscrepancy h N L % P < P - W
  rw [hreconstruct]
  constructor <;> linarith

/-- Under the standard dyadic room bound, the middle third is contained in
the robust certificate arc. -/
theorem adjacentMiddleThird_implies_certificateArc {h X N L : ℕ}
    (hNlt : N < 2 * X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hmid : AdjacentMiddleThirdAt h N L) :
    AdjacentCertificateArcAt h N L := by
  set P : ℤ := 2 ^ L
  set W : ℤ := ((N + h + L + 2 : ℕ) : ℤ)
  set B : ℤ := ((2 * X + h + L + 2 : ℕ) : ℤ)
  set d : ℤ := adjacentStepResidue h N L
  change P ≤ 6 * d ∧ 6 * d ≤ 5 * P at hmid
  rcases hmid with ⟨hmidlow, hmidhigh⟩
  have hWB : W ≤ B := by
    dsimp [W, B]
    omega
  have hroomZ : 16 * B ≤ P := by
    dsimp [B, P]
    exact_mod_cast hroom
  have hWnonneg : 0 ≤ W := by positivity
  have hPW : 12 * W ≤ P := by linarith
  change 2 * W ≤ d ∧ d ≤ P - 2 * W
  constructor <;> linarith

/-- The middle-third event certifies the original base `N`, not merely one
member of the adjacent pair. -/
theorem certifiedKill_of_adjacentMiddleThird {h X N L : ℕ}
    (hNlt : N < 2 * X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hmid : AdjacentMiddleThirdAt h N L) :
    certifiedKill h N L :=
  certifiedKill_of_adjacentCertificateArc
    (adjacentMiddleThird_implies_certificateArc hNlt hroom hmid)

/-! ## Exact tail interpretation -/

/-- The finite discrepancy is the exact depth-`L` prefix of the tail
difference; the only omitted term is the translated tail difference itself. -/
theorem tail_diff_eq_windowDiscrepancy_div_add_shifted (h N L : ℕ) :
    totientTail (N + h) - totientTail N =
      ((windowDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L +
        (totientTail (N + L + h) - totientTail (N + L)) / 2 ^ L := by
  rw [totientTail_eq_partial_add_shifted (N + h) L,
    totientTail_eq_partial_add_shifted N L]
  have hA := windowDiscrepancy_div_eq h N L
  rw [show N + h + L = N + L + h by omega]
  calc
    ((∑ j ∈ Finset.range L,
          (Nat.totient (N + h + 1 + j) : ℝ) / 2 ^ (j + 1)) +
        totientTail (N + L + h) / 2 ^ L) -
        ((∑ j ∈ Finset.range L,
          (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)) +
        totientTail (N + L) / 2 ^ L) =
      ((∑ j ∈ Finset.range L,
          (Nat.totient (N + h + 1 + j) : ℝ) / 2 ^ (j + 1)) -
        ∑ j ∈ Finset.range L,
          (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)) +
        (totientTail (N + L + h) - totientTail (N + L)) / 2 ^ L := by ring
    _ = ((windowDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L +
        (totientTail (N + L + h) - totientTail (N + L)) / 2 ^ L := by
      rw [← hA]

/-- Exact adjacent-step approximation to the tail class.  Modulo integers,
the adjacent displacement is the current tail difference plus a translated
tail error; hence adjacency exposes no independent arithmetic coordinate. -/
theorem adjacent_step_div_eq_tail_diff_add_error (h N L : ℕ) :
    (((windowDiscrepancy h (N + 1) L - windowDiscrepancy h N L : ℤ) : ℝ) /
        2 ^ L) =
      (totientTail (N + h) - totientTail N) -
        (deltaTotient h (N + 1) : ℝ) +
      ((totientTail (N + L + h) - totientTail (N + L)) -
        (totientTail (N + L + 1 + h) - totientTail (N + L + 1))) / 2 ^ L := by
  have h0 := tail_diff_eq_windowDiscrepancy_div_add_shifted h N L
  have h1 := tail_diff_eq_windowDiscrepancy_div_add_shifted h (N + 1) L
  have hs := tail_diff_succ h N
  rw [show N + 1 + L + h = N + L + 1 + h by omega,
    show N + 1 + L = N + L + 1 by omega] at h1
  push_cast
  rw [sub_div]
  linear_combination -h1 + hs + h0

/-- The exact adjacent-step error is exponentially small at fixed base: its
numerator is bounded by the two adjacent tail strips. -/
theorem abs_adjacent_step_tail_error_lt (h N L : ℕ) :
    |((totientTail (N + L + h) - totientTail (N + L)) -
        (totientTail (N + L + 1 + h) - totientTail (N + L + 1))) / 2 ^ L| <
      (2 * (N : ℝ) + 2 * L + 2 * h + 5) / 2 ^ L := by
  have h0 := abs_tail_diff_lt h (N + L)
  have h1 := abs_tail_diff_lt h (N + L + 1)
  push_cast at h0 h1
  have hnum :
      |(totientTail (N + L + h) - totientTail (N + L)) -
        (totientTail (N + L + 1 + h) - totientTail (N + L + 1))| <
          2 * (N : ℝ) + 2 * L + 2 * h + 5 := by
    calc
      |(totientTail (N + L + h) - totientTail (N + L)) -
          (totientTail (N + L + 1 + h) - totientTail (N + L + 1))| ≤
          |totientTail (N + L + h) - totientTail (N + L)| +
            |totientTail (N + L + 1 + h) - totientTail (N + L + 1)| :=
        abs_sub _ _
      _ < 2 * (N : ℝ) + 2 * L + 2 * h + 5 := by linarith
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ L)]
  exact (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ L)).2 hnum

/-! ## Two-point harmonic consumer -/

/-- Sharp norm-only conversion from squared chord separation to the
`9/10` average consumed by the first-harmonic certificate theorem. -/
theorem re_add_le_nine_fifths_of_unit_sq_chord {z w : ℂ}
    (hz : ‖z‖ = 1)
    (hw : ‖w‖ = 1)
    (hsep : (19 / 25 : ℝ) ≤ ‖z - w‖ ^ 2) :
    (z + w).re ≤ 9 / 5 := by
  have hpar : ‖z + w‖ ^ 2 + ‖z - w‖ ^ 2 = 4 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, hz, hw]
    ring
  have hnormSq : ‖z + w‖ ^ 2 ≤ (9 / 5 : ℝ) ^ 2 := by
    nlinarith
  have hnorm : ‖z + w‖ ≤ (9 / 5 : ℝ) := by
    nlinarith [norm_nonneg (z + w)]
  exact (Complex.re_le_norm (z + w)).trans hnorm

/-- Separation of any two distinct phases in the standard dyadic block
forces a certificate at one member of the pair. -/
theorem exists_certifiedKill_of_phasePairSeparation {h X L N M : ℕ}
    (hNM : N ≠ M)
    (hNlt : N < 2 * X)
    (hMlt : M < 2 * X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hsep :
      (19 / 25 : ℝ) ≤
        ‖windowFirstExp h N L - windowFirstExp h M L‖ ^ 2) :
    ∃ K ∈ ({N, M} : Finset ℕ), certifiedKill h K L := by
  apply exists_certifiedKill_of_first_harmonic_gap_subset ({N, M} : Finset ℕ)
  · intro K hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl
    · exact hNlt
    · exact hMlt
  · exact ⟨N, by simp⟩
  · exact hroom
  · have hgeom := re_add_le_nine_fifths_of_unit_sq_chord
      (norm_windowFirstExp h N L) (norm_windowFirstExp h M L) hsep
    simp [hNM]
    norm_num at hgeom ⊢
    exact hgeom

/-- A cofinal adjacent middle-third supply proves irrationality through the
existing finite certificate consumer. -/
theorem irrational_totient_series_of_adjacentMiddleThirdSeparation
    (hsep : DTWAdjacentMiddleThirdSeparation) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_certificate_supply
  intro h hh N₀
  obtain ⟨X, L, N, hX, hXN, hNlt, hroom, hmid⟩ := hsep h hh N₀
  have hNlt' : N < 2 * X := by omega
  refine ⟨N, ?_, L, certifiedKill_of_adjacentMiddleThird hNlt' hroom hmid⟩
  exact (Nat.le_max_left N₀ 1).trans (hX.trans hXN)

/-- A cofinal adjacent chord-separation supply also proves irrationality,
via the two-element first-harmonic consumer. -/
theorem irrational_totient_series_of_adjacentPhaseSeparation
    (hsep : DTWAdjacentPhaseSeparation) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_certificate_supply
  intro h hh N₀
  obtain ⟨X, L, N, hX, hXN, hNlt, hroom, hphase⟩ := hsep h hh N₀
  have hne : N + 1 ≠ N := by omega
  have hNlt' : N < 2 * X := by omega
  obtain ⟨K, hK, hkill⟩ := exists_certifiedKill_of_phasePairSeparation
    hne hNlt hNlt' hroom hphase
  have hNK : N ≤ K := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl <;> omega
  exact ⟨K, (Nat.le_max_left N₀ 1).trans (hX.trans (hXN.trans hNK)), L, hkill⟩

#print axioms adjacentStepResidue_eq_translated_windowResidue
#print axioms windowResidue_eq_adjacentStepResidue_sub_endpoint
#print axioms certifiedKill_of_adjacentMiddleThird
#print axioms tail_diff_eq_windowDiscrepancy_div_add_shifted
#print axioms adjacent_step_div_eq_tail_diff_add_error
#print axioms abs_adjacent_step_tail_error_lt
#print axioms irrational_totient_series_of_adjacentMiddleThirdSeparation
#print axioms re_add_le_nine_fifths_of_unit_sq_chord
#print axioms exists_certifiedKill_of_phasePairSeparation
#print axioms irrational_totient_series_of_adjacentPhaseSeparation

end
end TotientTailPeriodKiller
end Erdos249257
