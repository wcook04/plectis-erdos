import Erdos249257.AdjacentPhaseSeparation

/-!
# Adjacent robust failures are the existing carry tube

Failure of the robust adjacent arc is not itself survival of the endpoint
certificate.  This module gives the canonical signed lift of an adjacent
failure, removes the modulus across consecutive failures, and identifies the
remaining strict branch with the existing `carryOrbit` at shifted base
`N + L`.

The paper-facing result is a trichotomy: a robust failure either gives the
original same-`N` `certifiedKill`, gives a boundary non-integrality
certificate, or lies strictly inside the existing carry strip.  Consequently
`survivorKill h (N + L) K` forces an adjacent exit within `K` steps.  This is a
bridge into `CarrySurvivorExtinction`, not a second extinction theory.
-/

set_option maxRecDepth 10000

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

noncomputable section

/-- Failure of the robust adjacent certificate arc. -/
def AdjacentRobustFailureAt (h N L : ℕ) : Prop :=
  ¬ AdjacentCertificateArcAt h N L

/-- The unique short signed representative selected by a robust adjacent
failure: the low residue itself, or the high residue translated by `-2^L`. -/
def adjacentSignedLift (h N L : ℕ) : ℤ :=
  let P : ℤ := 2 ^ L
  let W : ℤ := N + h + L + 2
  let d := adjacentStepResidue h N L
  if d < 2 * W then d else d - P

/-- The adjacent signed lift translated back to the original window
coordinate. -/
def adjacentWindowLift (h N L : ℕ) : ℤ :=
  adjacentSignedLift h N L - deltaTotient h (N + L + 1)

/-- The carry coordinate conjugate to the adjacent signed state. -/
def adjacentCarryState (h N L : ℕ) : ℤ :=
  deltaTotient h (N + L + 1) - adjacentSignedLift h N L

private lemma eq_of_modEq_of_strict_sub_bounds {P a b : ℤ}
    (hP : 0 < P) (hmod : a ≡ b [ZMOD P])
    (hlo : -P < b - a) (hhi : b - a < P) :
    a = b := by
  obtain ⟨k, hk⟩ := hmod.dvd
  by_cases hk0 : k = 0
  · simp [hk0] at hk
    omega
  have hkcases : k ≤ -1 ∨ 1 ≤ k := by omega
  rcases hkcases with hkneg | hkpos
  · have hmul : P * k ≤ P * (-1) :=
      mul_le_mul_of_nonneg_left hkneg hP.le
    nlinarith
  · have hmul : P * 1 ≤ P * k :=
      mul_le_mul_of_nonneg_left hkpos hP.le
    nlinarith

lemma adjacentStepResidue_nonneg (h N L : ℕ) :
    0 ≤ adjacentStepResidue h N L := by
  unfold adjacentStepResidue
  exact Int.emod_nonneg _ (by positivity)

lemma adjacentStepResidue_lt (h N L : ℕ) :
    adjacentStepResidue h N L < (2 ^ L : ℤ) := by
  unfold adjacentStepResidue
  exact Int.emod_lt_of_pos _ (by positivity)

/-- A robust failure lies on exactly one side of the closed robust arc. -/
lemma adjacentFailure_partition {h N L : ℕ}
    (hfail : AdjacentRobustFailureAt h N L) :
    adjacentStepResidue h N L < 2 * (N + h + L + 2 : ℤ) ∨
      (2 ^ L : ℤ) - 2 * (N + h + L + 2 : ℤ) <
        adjacentStepResidue h N L := by
  unfold AdjacentRobustFailureAt AdjacentCertificateArcAt at hfail
  dsimp at hfail
  omega

/-- The signed lift represents the adjacent residue modulo `2^L`. -/
lemma adjacentSignedLift_mod (h N L : ℕ) :
    adjacentSignedLift h N L ≡ adjacentStepResidue h N L [ZMOD (2 ^ L : ℤ)] := by
  unfold adjacentSignedLift
  dsimp
  split_ifs
  · exact Int.ModEq.rfl
  · rw [Int.modEq_iff_dvd]
    simp

/-- Every robust failure has a canonical representative in the strict
`2W` signed interval. -/
lemma adjacentSignedLift_abs_lt {h N L : ℕ}
    (hfail : AdjacentRobustFailureAt h N L) :
    |adjacentSignedLift h N L| < 2 * (N + h + L + 2 : ℤ) := by
  have hd0 := adjacentStepResidue_nonneg h N L
  have hdP := adjacentStepResidue_lt h N L
  by_cases hlow : adjacentStepResidue h N L <
      2 * (N + h + L + 2 : ℤ)
  · simp [adjacentSignedLift, hlow, abs_of_nonneg hd0]
  · have hhigh := (adjacentFailure_partition hfail).resolve_left hlow
    rw [adjacentSignedLift, if_neg hlow]
    have hnonpos : adjacentStepResidue h N L - (2 ^ L : ℤ) ≤ 0 := by
      omega
    rw [abs_of_nonpos hnonpos]
    omega

/-- Under `4W < 2^L`, the short representative is unique. -/
lemma adjacentSignedLift_exists_unique {h N L : ℕ}
    (hfail : AdjacentRobustFailureAt h N L)
    (hroom : 4 * (N + h + L + 2 : ℤ) < (2 ^ L : ℤ)) :
    ∀ t : ℤ,
      t ≡ adjacentStepResidue h N L [ZMOD (2 ^ L : ℤ)] →
      |t| < 2 * (N + h + L + 2 : ℤ) →
      t = adjacentSignedLift h N L := by
  intro t htmod ht
  have hs := adjacentSignedLift_abs_lt hfail
  have hmod := htmod.trans (adjacentSignedLift_mod h N L).symm
  have ht' := abs_lt.mp ht
  have hs' := abs_lt.mp hs
  apply eq_of_modEq_of_strict_sub_bounds (by positivity) hmod
  · omega
  · omega

/-- The spatial slide induces the exact adjacent-residue recurrence modulo
`2^L`. -/
lemma adjacentStepResidue_succ_mod (h N L : ℕ) :
    adjacentStepResidue h (N + 1) L =
      (2 * adjacentStepResidue h N L - deltaTotient h (N + L + 1) +
        deltaTotient h (N + L + 2)) % (2 ^ L : ℤ) := by
  rw [adjacentStepResidue_eq_translated_windowResidue,
    adjacentStepResidue_eq_translated_windowResidue,
    windowDiscrepancy_slide]
  set P : ℤ := 2 ^ L
  set A : ℤ := windowDiscrepancy h N L
  set q : ℤ := (A + deltaTotient h (N + L + 1)) / P
  set d : ℤ := (A + deltaTotient h (N + L + 1)) % P
  have hdecomp :
      P * q + d =
        A + deltaTotient h (N + L + 1) := by
    dsimp [q, d]
    exact Int.mul_ediv_add_emod _ _
  have hrearrange :
      2 * A - deltaTotient h (N + 1) * P +
          deltaTotient h (N + L + 1) + deltaTotient h (N + L + 2) =
        (2 * d - deltaTotient h (N + L + 1) +
          deltaTotient h (N + L + 2)) +
        P * (2 * q - deltaTotient h (N + 1)) := by
    have hA : A = P * q + d - deltaTotient h (N + L + 1) := by
      linarith [hdecomp]
    rw [hA]
    ring
  rw [show N + 1 + L + 1 = N + L + 2 by omega]
  change
    (2 * A - deltaTotient h (N + 1) * P +
        deltaTotient h (N + L + 1) + deltaTotient h (N + L + 2)) % P =
      (2 * d - deltaTotient h (N + L + 1) +
        deltaTotient h (N + L + 2)) % P
  rw [hrearrange, Int.add_mul_emod_self_left]

/-- Two consecutive robust failures cannot wrap when the next endpoint has
`8W` dyadic room. -/
lemma adjacentSignedLift_succ_of_two_failures {h N L : ℕ}
    (hfail : AdjacentRobustFailureAt h N L)
    (hfail' : AdjacentRobustFailureAt h (N + 1) L)
    (hroom : 8 * (N + h + L + 3 : ℤ) < (2 ^ L : ℤ)) :
    adjacentSignedLift h (N + 1) L =
      2 * adjacentSignedLift h N L - deltaTotient h (N + L + 1) +
        deltaTotient h (N + L + 2) := by
  set P : ℤ := 2 ^ L
  set s : ℤ := adjacentSignedLift h N L
  set s' : ℤ := adjacentSignedLift h (N + 1) L
  set e : ℤ := deltaTotient h (N + L + 1)
  set e' : ℤ := deltaTotient h (N + L + 2)
  have hsmod := adjacentSignedLift_mod h N L
  have hsmod' := adjacentSignedLift_mod h (N + 1) L
  have hdrec := adjacentStepResidue_succ_mod h N L
  have hdmod :
      adjacentStepResidue h (N + 1) L ≡
        2 * adjacentStepResidue h N L - e + e' [ZMOD P] := by
    rw [hdrec]
    exact Int.mod_modEq _ _
  have hrhs :
      2 * s - e + e' ≡
        2 * adjacentStepResidue h N L - e + e' [ZMOD P] := by
    exact ((hsmod.mul_left 2).sub Int.ModEq.rfl).add Int.ModEq.rfl
  have hmod : s' ≡ 2 * s - e + e' [ZMOD P] :=
    hsmod'.trans (hdmod.trans hrhs.symm)
  have hsabs := adjacentSignedLift_abs_lt hfail
  have hsabs' := adjacentSignedLift_abs_lt hfail'
  have heabs := abs_deltaTotient_le h (N + L + 1)
  have heabs' := abs_deltaTotient_le h (N + L + 2)
  have hsbd := abs_lt.mp hsabs
  have hsbd' := abs_lt.mp hsabs'
  have hebd := abs_le.mp heabs
  have hebd' := abs_le.mp heabs'
  apply eq_of_modEq_of_strict_sub_bounds (by positivity) hmod
  · dsimp [s, s', e, e', P] at *
    push_cast at *
    omega
  · dsimp [s, s', e, e', P] at *
    push_cast at *
    omega

/-- The original-window lift has the same residue as
`windowDiscrepancy`. -/
lemma adjacentWindowLift_mod_windowResidue (h N L : ℕ) :
    adjacentWindowLift h N L ≡ windowDiscrepancy h N L [ZMOD (2 ^ L : ℤ)] := by
  have hs := adjacentSignedLift_mod h N L
  have hsub := hs.sub (Int.ModEq.refl (deltaTotient h (N + L + 1)))
  unfold adjacentWindowLift
  exact hsub.trans
    (show adjacentStepResidue h N L - deltaTotient h (N + L + 1) ≡
        windowDiscrepancy h N L [ZMOD (2 ^ L : ℤ)] from
      windowResidue_eq_adjacentStepResidue_sub_endpoint h N L |>.symm)

/-- The low and high signed branches give asymmetric `3W` bounds for the
window lift. -/
lemma adjacentWindowLift_branch_bounds {h N L : ℕ}
    (hfail : AdjacentRobustFailureAt h N L) :
    (-(N + h + L + 2 : ℤ) < adjacentWindowLift h N L ∧
        adjacentWindowLift h N L < 3 * (N + h + L + 2 : ℤ)) ∨
      (-3 * (N + h + L + 2 : ℤ) < adjacentWindowLift h N L ∧
        adjacentWindowLift h N L < (N + h + L + 2 : ℤ)) := by
  have hd0 := adjacentStepResidue_nonneg h N L
  have hdP := adjacentStepResidue_lt h N L
  have heabs := abs_deltaTotient_le h (N + L + 1)
  have hebd := abs_le.mp heabs
  by_cases hlow : adjacentStepResidue h N L <
      2 * (N + h + L + 2 : ℤ)
  · left
    simp only [adjacentWindowLift, adjacentSignedLift, hlow, if_pos]
    push_cast at *
    omega
  · right
    have hhigh := (adjacentFailure_partition hfail).resolve_left hlow
    rw [adjacentWindowLift, adjacentSignedLift, if_neg hlow]
    push_cast at *
    omega

lemma adjacentWindowLift_abs_lt_three {h N L : ℕ}
    (hfail : AdjacentRobustFailureAt h N L) :
    |adjacentWindowLift h N L| < 3 * (N + h + L + 2 : ℤ) := by
  rcases adjacentWindowLift_branch_bounds hfail with hlow | hhigh
  · rw [abs_lt]
    omega
  · rw [abs_lt]
    omega

/-- If the centred original-window lift lies outside the endpoint strip, the
same-`N` endpoint certificate already fires. -/
theorem certifiedKill_of_adjacentWindowLift_abs_gt {h N L : ℕ}
    (hfail : AdjacentRobustFailureAt h N L)
    (hroom : 4 * (N + h + L + 2 : ℤ) < (2 ^ L : ℤ))
    (hout : (N + h + L + 2 : ℤ) < |adjacentWindowLift h N L|) :
    certifiedKill h N L := by
  apply certifiedKill_of_no_endpointSurvivor
  · omega
  intro t ht
  rcases ht with ⟨htabs, htmod⟩
  have hzabs := adjacentWindowLift_abs_lt_three hfail
  have hmod := (adjacentWindowLift_mod_windowResidue h N L).trans htmod.symm
  have htbd := abs_le.mp htabs
  have hzbd := abs_lt.mp hzabs
  have heq : adjacentWindowLift h N L = t := by
    apply eq_of_modEq_of_strict_sub_bounds (by positivity) hmod
    · omega
    · omega
  rw [heq] at hout
  omega

/-- Equality with the endpoint radius is itself a non-integrality
certificate, despite not satisfying the strict `certifiedKill` predicate. -/
theorem tail_diff_notMem_int_of_adjacentWindowLift_abs_eq {h N L : ℕ}
    (hroom : 2 * (N + h + L + 2 : ℤ) < (2 ^ L : ℤ))
    (heq : |adjacentWindowLift h N L| = (N + h + L + 2 : ℤ)) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨k, hk⟩
  set P : ℤ := 2 ^ L
  set A : ℤ := windowDiscrepancy h N L
  set z : ℤ := adjacentWindowLift h N L
  set q : ℤ := k * P - A
  have hsplit := tail_diff_eq_windowDiscrepancy_div_add_shifted h N L
  have hPposR : (0 : ℝ) < 2 ^ L := by positivity
  have hqcast : (q : ℝ) =
      totientTail (N + L + h) - totientTail (N + L) := by
    rw [← hk] at hsplit
    dsimp [q, P, A]
    push_cast
    field_simp [hPposR.ne'] at hsplit ⊢
    linarith
  have hqabsR := abs_tail_diff_lt h (N + L)
  rw [← hqcast] at hqabsR
  have hqabs' : |q| < (N + L + h + 2 : ℤ) := by
    exact_mod_cast hqabsR
  have hqabs : |q| < (N + h + L + 2 : ℤ) := by omega
  have hzmod := adjacentWindowLift_mod_windowResidue h N L
  have hqmod : -z ≡ q [ZMOD P] := by
    have hneg := hzmod.neg
    have hAmod : -A ≡ q [ZMOD P] := by
      rw [Int.modEq_iff_dvd]
      dsimp [q]
      ring_nf
      exact dvd_mul_left P k
    exact hneg.trans hAmod
  have hzabs : |z| = (N + h + L + 2 : ℤ) := by
    simpa [z] using heq
  have hzbd := abs_le.mp hzabs.le
  have hqbd := abs_lt.mp hqabs
  have hsame : -z = q := by
    apply eq_of_modEq_of_strict_sub_bounds (by positivity) hqmod
    · dsimp [P] at *
      omega
    · dsimp [P] at *
      omega
  have : |q| = (N + h + L + 2 : ℤ) := by
    rw [← hsame, abs_neg]
    simpa [z] using heq
  omega

/-- The third branch is the strict initial candidate box of `survivorKill`. -/
lemma adjacentCarryState_abs_le_of_windowLift_abs_lt {h N L : ℕ}
    (hin : |adjacentWindowLift h N L| < (N + h + L + 2 : ℤ)) :
    |adjacentCarryState h N L| ≤ (N + L + h + 1 : ℤ) := by
  have hneg : adjacentCarryState h N L = -adjacentWindowLift h N L := by
    simp [adjacentCarryState, adjacentWindowLift]
  rw [hneg, abs_neg]
  omega

/-- Correct pointwise interpretation of robust-arc failure. -/
theorem adjacentFailure_kill_or_boundaryKill_or_strictCarry {h N L : ℕ}
    (hfail : AdjacentRobustFailureAt h N L)
    (hroom : 4 * (N + h + L + 2 : ℤ) < (2 ^ L : ℤ)) :
    certifiedKill h N L ∨
      (totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) ∨
      |adjacentCarryState h N L| ≤ (N + L + h + 1 : ℤ) := by
  rcases lt_trichotomy |adjacentWindowLift h N L|
      (N + h + L + 2 : ℤ) with hin | heq | hout
  · exact Or.inr (Or.inr (adjacentCarryState_abs_le_of_windowLift_abs_lt hin))
  · exact Or.inr (Or.inl
      (tail_diff_notMem_int_of_adjacentWindowLift_abs_eq (by omega) heq))
  · exact Or.inl (certifiedKill_of_adjacentWindowLift_abs_gt hfail hroom hout)

/-- In the strict robust-failure tube, the adjacent carry state obeys the
existing carry recurrence. -/
lemma adjacentCarryState_succ {h N L : ℕ}
    (hfail : AdjacentRobustFailureAt h N L)
    (hfail' : AdjacentRobustFailureAt h (N + 1) L)
    (hroom : 8 * (N + h + L + 3 : ℤ) < (2 ^ L : ℤ)) :
    adjacentCarryState h (N + 1) L =
      2 * adjacentCarryState h N L - deltaTotient h (N + L + 1) := by
  rw [adjacentCarryState, adjacentCarryState,
    adjacentSignedLift_succ_of_two_failures hfail hfail' hroom]
  rw [show N + 1 + L + 1 = N + L + 2 by omega]
  ring

/-- Exact affine conjugacy with `carryOrbit` over any robust-failure run. -/
theorem adjacentCarryState_eq_carryOrbit {h N L i : ℕ}
    (hfail : ∀ j, j ≤ i → AdjacentRobustFailureAt h (N + j) L)
    (hroom : ∀ j, j < i →
      8 * (N + j + h + L + 3 : ℤ) < (2 ^ L : ℤ)) :
    adjacentCarryState h (N + i) L =
      carryOrbit h (N + L) (adjacentCarryState h N L) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      calc
        adjacentCarryState h (N + (i + 1)) L =
            adjacentCarryState h ((N + i) + 1) L := by
              rw [show N + (i + 1) = (N + i) + 1 by omega]
        _ = 2 * adjacentCarryState h (N + i) L -
              deltaTotient h (N + i + L + 1) :=
            adjacentCarryState_succ (hfail i (by omega))
              (hfail (i + 1) (by omega)) (hroom i (by omega))
        _ = 2 * carryOrbit h (N + L) (adjacentCarryState h N L) i -
              deltaTotient h (N + L + i + 1) := by
            rw [ih (fun j hj => hfail j (by omega))
              (fun j hj => hroom j (by omega))]
            rw [show N + i + L + 1 = N + L + i + 1 by omega]
        _ = carryOrbit h (N + L) (adjacentCarryState h N L) (i + 1) := by
            rw [carryOrbit]

/-- The existing finite carry certificate forces an adjacent endpoint or
boundary exit. -/
theorem exists_adjacent_exit_of_survivorKill {h N L K : ℕ}
    (hroom : ∀ i, i ≤ K →
      8 * (N + i + h + L + 3 : ℤ) < (2 ^ L : ℤ))
    (hkill : survivorKill h (N + L) K) :
    ∃ i ∈ Finset.range (K + 1),
      certifiedKill h (N + i) L ∨
      (totientTail (N + i + h) - totientTail (N + i) ∉
        Set.range ((↑) : ℤ → ℝ)) := by
  by_contra hnone
  push Not at hnone
  have hfail : ∀ i, i ≤ K → AdjacentRobustFailureAt h (N + i) L := by
    intro i hi harc
    exact (hnone i (by simpa [Finset.mem_range] using show i < K + 1 by omega)).1
      (certifiedKill_of_adjacentCertificateArc harc)
  have hstrict : ∀ i, i ≤ K →
      |adjacentCarryState h (N + i) L| ≤ (N + L + i + h + 1 : ℤ) := by
    intro i hi
    have htri := adjacentFailure_kill_or_boundaryKill_or_strictCarry
      (hfail i hi) (by have := hroom i hi; push_cast at *; omega)
    rcases htri with hcert | hboundary | hinside
    · exact False.elim ((hnone i (by simp [Finset.mem_range]; omega)).1 hcert)
    · exact False.elim (hboundary
        (hnone i (by simp [Finset.mem_range]; omega)).2)
    · simpa [add_assoc, add_left_comm, add_comm] using hinside
  set c : ℤ := adjacentCarryState h N L
  set R : ℤ := ((N + L + h + 1 : ℕ) : ℤ)
  have hcabs := hstrict 0 (by omega)
  have hcabs' : |c| ≤ R := by
    simpa [c, R, add_assoc, add_left_comm, add_comm] using hcabs
  have hcnonneg : 0 ≤ c + R := by
    have hclow : -R ≤ c := (abs_le.mp hcabs').1
    linarith
  have hcast : (((c + R).toNat : ℕ) : ℤ) = c + R :=
    Int.toNat_of_nonneg hcnonneg
  have hmem : (c + R).toNat ∈
      Finset.range (2 * ((N + L : ℕ) + h + 1) + 1) := by
    rw [Finset.mem_range]
    have hboundZ : (((c + R).toNat : ℕ) : ℤ) <
        ((2 * ((N + L : ℕ) + h + 1) + 1 : ℕ) : ℤ) := by
      rw [hcast]
      have := (abs_le.mp hcabs').2
      dsimp [R] at *
      push_cast at *
      omega
    exact_mod_cast hboundZ
  obtain ⟨i, hi, hesc⟩ := hkill
    (c + R).toNat hmem
  have hicand :
      (((c + R).toNat : ℕ) : ℤ) -
          ((N + L : ℕ) + h + 1) = c := by
    rw [hcast]
    dsimp [R]
    ring
  rw [hicand] at hesc
  have hiK : i ≤ K := by simpa [Finset.mem_range] using hi
  have horbit := adjacentCarryState_eq_carryOrbit
    (i := i)
    (fun j hj => hfail j (hj.trans hiK))
    (fun j hj => hroom j (by omega))
  have hibound := hstrict i hiK
  have hibound' : |adjacentCarryState h (N + i) L| ≤
      (N + i + L + h + 1 : ℤ) := by
    simpa [add_assoc, add_left_comm, add_comm] using hibound
  dsimp [c] at hesc
  rw [← horbit] at hesc
  rcases hesc with hlo | hhi <;>
    have := abs_le.mp hibound' <;> omega

#print axioms adjacentSignedLift_exists_unique
#print axioms adjacentSignedLift_succ_of_two_failures
#print axioms adjacentFailure_kill_or_boundaryKill_or_strictCarry
#print axioms adjacentCarryState_eq_carryOrbit
#print axioms exists_adjacent_exit_of_survivorKill

end
end TotientTailPeriodKiller
end Erdos249257
