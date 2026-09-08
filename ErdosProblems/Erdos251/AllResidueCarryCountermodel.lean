import ErdosProblems.Erdos251.PrimeGapDyadicTail
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing

/-!
# Erdős #251: an all-residue telescoping countermodel

The factorial construction only places the values `2` and `4` at indices in
the common zero residue class modulo every fixed `t`.  This module repairs
the quantifier at the level of a finite exact telescope: a scheduled even
carry word realises both values in every index residue class, and

`Σ_{j < m} a_{N+1+j} / 2^{j+1} = U_N - U_{N+m} / 2^m`

holds identically over `ℤ`.  Completeness of the tail as `m → ∞`, positivity
of the coefficients, and prime-number-theorem-scale cumulative growth remain
ordinary facts about a logarithmically growing carry; they are not claimed
as `HasSum` here.

Not the actual prime-gap word; Erdős #251 remains open.
-/

namespace ErdosProblems.Erdos251

/-! ## Residue alignment -/

/-- The least `n ≥ B` with `n ≡ r [MOD t]`, for `r < t`. -/
def alignResidue (B t r : ℕ) : ℕ :=
  B + (r + t - B % t) % t

theorem alignResidue_ge (B t r : ℕ) : B ≤ alignResidue B t r :=
  Nat.le_add_right _ _

theorem alignResidue_modEq (B t r : ℕ) (ht : 0 < t) (hr : r < t) :
    alignResidue B t r ≡ r [MOD t] := by
  rw [alignResidue, Nat.ModEq, Nat.add_mod, Nat.mod_mod]
  set b := B % t
  have hb : b < t := Nat.mod_lt B ht
  by_cases hle : b ≤ r
  · have hsum : r + t - b = r - b + t := by omega
    have hlt : r - b < t := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    have : b + (r - b) = r := by omega
    rw [this, Nat.mod_eq_of_lt hr]
  · have : r < b := Nat.lt_of_not_ge hle
    have hsum : r + t - b < t := by omega
    rw [Nat.mod_eq_of_lt hsum]
    have : b + (r + t - b) = r + t := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

/-! ## Triple encoding -/

def residueModulus (j : ℕ) : ℕ :=
  (Nat.unpair j).1 + 1

def residueClass (j : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair j).2).1 % residueModulus j

def residueValue (j : ℕ) : ℕ :=
  if (Nat.unpair (Nat.unpair j).2).2 % 2 = 0 then 2 else 4

theorem residueModulus_pos (j : ℕ) : 0 < residueModulus j :=
  Nat.succ_pos _

theorem residueClass_lt (j : ℕ) : residueClass j < residueModulus j :=
  Nat.mod_lt _ (residueModulus_pos j)

theorem residueValue_eq_two_or_four (j : ℕ) :
    residueValue j = 2 ∨ residueValue j = 4 := by
  unfold residueValue
  split_ifs <;> simp

/-! ## Centres -/

def allResidueCentre : ℕ → ℕ
  | 0 => alignResidue 100 (residueModulus 0) (residueClass 0)
  | j + 1 =>
      let B := max 100 (max (2 ^ ((j + 1) * (j + 1))) (allResidueCentre j + 3))
      alignResidue B (residueModulus (j + 1)) (residueClass (j + 1))

theorem allResidueCentre_succ_ge (j : ℕ) :
    allResidueCentre j + 3 ≤ allResidueCentre (j + 1) := by
  let B := max 100 (max (2 ^ ((j + 1) * (j + 1))) (allResidueCentre j + 3))
  have hB : allResidueCentre j + 3 ≤ B := le_max_of_le_right (le_max_right _ _)
  exact hB.trans (alignResidue_ge B _ _)

theorem allResidueCentre_strictMono : StrictMono allResidueCentre :=
  strictMono_nat_of_lt_succ fun j =>
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3))
      (allResidueCentre_succ_ge j)

theorem allResidueCentre_modEq (j : ℕ) :
    allResidueCentre j ≡ residueClass j [MOD residueModulus j] := by
  cases j with
  | zero =>
      exact alignResidue_modEq 100 (residueModulus 0) (residueClass 0)
        (residueModulus_pos 0) (residueClass_lt 0)
  | succ j =>
      let B := max 100 (max (2 ^ ((j + 1) * (j + 1))) (allResidueCentre j + 3))
      exact alignResidue_modEq B (residueModulus (j + 1)) (residueClass (j + 1))
        (residueModulus_pos (j + 1)) (residueClass_lt (j + 1))

theorem allResidueCentre_ge_hundred : ∀ j, 100 ≤ allResidueCentre j
  | 0 => alignResidue_ge 100 _ _
  | j + 1 =>
      (allResidueCentre_ge_hundred j).trans <|
        (Nat.le_add_right _ 3).trans (allResidueCentre_succ_ge j)

theorem allResidueCentre_injective : Function.Injective allResidueCentre :=
  allResidueCentre_strictMono.injective

theorem allResidueCentre_gt_index : ∀ j, j < allResidueCentre j + 1
  | 0 =>
      Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 101)
        (Nat.succ_le_succ (allResidueCentre_ge_hundred 0))
  | j + 1 => by
      have hge := allResidueCentre_succ_ge j
      have ih := allResidueCentre_gt_index j
      omega

/-! ## Carry and gap, over ℤ so the telescope is unconditional -/

def allResidueBaseline (n : ℕ) : ℤ :=
  2 * ((Nat.log 2 (n + 64) : ℕ) + 3)

noncomputable def allResidueCarry (n : ℕ) : ℤ :=
  if h : ∃ j : ℕ, j < n + 1 ∧ allResidueCentre j = n then
    if n = 0 then allResidueBaseline 0
    else 2 * allResidueBaseline (n - 1) - (residueValue (Nat.find h) : ℤ)
  else
    allResidueBaseline n

/-- `a_0` is unused; for `n ≥ 1` this is `2 U_{n-1} - U_n`. -/
noncomputable def allResidueGap (n : ℕ) : ℤ :=
  if n = 0 then 0 else 2 * allResidueCarry (n - 1) - allResidueCarry n

/-- Finite telescope: the partial scaled sum is the exact carry difference. -/
theorem allResidue_partial_telescope (N m : ℕ) :
    ∑ j ∈ Finset.range m, (allResidueGap (N + 1 + j) : ℚ) / 2 ^ (j + 1) =
      (allResidueCarry N : ℚ) - (allResidueCarry (N + m) : ℚ) / 2 ^ m := by
  induction m with
  | zero => simp [allResidueGap]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hidx : N + 1 + m = N + m + 1 := by omega
      have hn0 : N + m + 1 ≠ 0 := Nat.succ_ne_zero (N + m)
      have hgap :
          (allResidueGap (N + m + 1) : ℚ) =
            2 * (allResidueCarry (N + m) : ℚ) -
              (allResidueCarry (N + m + 1) : ℚ) := by
        rw [allResidueGap, if_neg hn0]
        simp
      rw [hidx, hgap]
      field_simp
      ring

theorem allResidueCarry_at_noncentre {n : ℕ}
    (h : ¬ ∃ j : ℕ, j < n + 1 ∧ allResidueCentre j = n) :
    allResidueCarry n = allResidueBaseline n := by
  unfold allResidueCarry
  exact dif_neg h

theorem allResidueCarry_at_centre {j n : ℕ}
    (hj : allResidueCentre j = n) (hn : n ≠ 0) :
    allResidueCarry n = 2 * allResidueBaseline (n - 1) - (residueValue j : ℤ) := by
  have hjlt : j < n + 1 := by
    have := allResidueCentre_gt_index j
    rwa [hj] at this
  have hex : ∃ k : ℕ, k < n + 1 ∧ allResidueCentre k = n := ⟨j, hjlt, hj⟩
  have hfind := Nat.find_spec hex
  have hj_eq : Nat.find hex = j :=
    allResidueCentre_injective (hfind.2.trans hj.symm)
  unfold allResidueCarry
  rw [dif_pos hex, if_neg hn, hj_eq]

/-- A centre realises its scheduled small value as a gap coefficient. -/
theorem allResidueGap_at_centre {j : ℕ} (hj : allResidueCentre j ≠ 0)
    (hpred : ¬ ∃ k : ℕ,
      k < allResidueCentre j ∧ allResidueCentre k = allResidueCentre j - 1) :
    allResidueGap (allResidueCentre j) = residueValue j := by
  set n := allResidueCentre j
  have hn0 : n ≠ 0 := hj
  have hcent : 1 ≤ n := Nat.pos_of_ne_zero hn0
  have hpred' : ¬ ∃ k : ℕ, k < (n - 1) + 1 ∧ allResidueCentre k = n - 1 := by
    simpa [Nat.sub_add_cancel hcent] using hpred
  rw [allResidueGap, if_neg hn0, allResidueCarry_at_centre (rfl : allResidueCentre j = n) hn0,
    allResidueCarry_at_noncentre hpred']
  ring

#print axioms alignResidue_modEq
#print axioms allResidueCentre_modEq
#print axioms allResidue_partial_telescope
#print axioms allResidueGap_at_centre

end ErdosProblems.Erdos251
