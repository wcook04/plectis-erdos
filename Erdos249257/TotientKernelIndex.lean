import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite indices for the all-base totient kernel

This module records the combinatorial part of the expected finite-level
all-base totient-kernel basis.  There are two distinguished zero-residue
indices, followed at level `j + 1` by residues written uniquely in the form

`k * q + (d + 1)`, with `q < k^j` and `d < k - 1`.

For `k ≥ 2`, these coordinates give positive residues below `k^(j+1)` that
are not divisible by `k`.  Their finite cardinality is

`2 + ∑ j in range e, k^j * (k - 1) = k^e + 1`.

This is only the index and cardinality layer.  It does not assert linear
independence of the corresponding totient sections; that theorem remains an
external mathematical input in the all-base argument.
-/

namespace Erdos249257

/-- The two distinguished zero-residue channels, conventionally denoted
`F00` and `F10`. -/
inductive TotientKernelHeadIndex
  | F00
  | F10
  deriving DecidableEq

instance : Fintype TotientKernelHeadIndex where
  elems := {.F00, .F10}
  complete := by
    intro i
    cases i <;> simp

/-- There are exactly two distinguished zero-residue indices. -/
theorem card_totientKernelHeadIndex :
    Fintype.card TotientKernelHeadIndex = 2 := by
  decide

/-- Coordinates for the nonzero canonical sections through levels
`1, ..., e`.  At the level represented by `j : Fin e`, the pair `(q,d)`
encodes the residue `k * q + (d + 1)`. -/
abbrev TotientKernelSectionIndex (k e : ℕ) :=
  Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)

/-- The complete finite-level all-base index: two distinguished channels and
all canonical nonzero section coordinates. -/
abbrev TotientKernelIndex (k e : ℕ) :=
  TotientKernelHeadIndex ⊕ TotientKernelSectionIndex k e

/-- The positive level represented by a section coordinate. -/
def totientKernelSectionLevel {k e : ℕ}
    (i : TotientKernelSectionIndex k e) : ℕ :=
  i.1.val + 1

/-- The residue represented by quotient `q` and nonzero last base-`k` digit
`d + 1`. -/
def totientKernelSectionResidue {k e : ℕ}
    (i : TotientKernelSectionIndex k e) : ℕ :=
  k * i.2.1.val + (i.2.2.val + 1)

/-- A section coordinate always represents one of the levels `1, ..., e`. -/
theorem totientKernelSectionLevel_bounds {k e : ℕ}
    (i : TotientKernelSectionIndex k e) :
    1 ≤ totientKernelSectionLevel i ∧ totientKernelSectionLevel i ≤ e := by
  rcases i with ⟨j, q, d⟩
  simp only [totientKernelSectionLevel]
  omega

/-- The encoded last digit is strictly between zero and the base. -/
theorem totientKernelSectionDigit_bounds {k e : ℕ} (hk : 2 ≤ k)
    (i : TotientKernelSectionIndex k e) :
    0 < i.2.2.val + 1 ∧ i.2.2.val + 1 < k := by
  exact ⟨by omega, by have := i.2.2.isLt; omega⟩

/-- The encoded residue is positive. -/
theorem totientKernelSectionResidue_pos {k e : ℕ}
    (i : TotientKernelSectionIndex k e) :
    0 < totientKernelSectionResidue i := by
  simp only [totientKernelSectionResidue]
  omega

/-- The quotient and digit bounds put the encoded residue below its level
modulus. -/
theorem totientKernelSectionResidue_lt_pow {k e : ℕ} (hk : 2 ≤ k)
    (i : TotientKernelSectionIndex k e) :
    totientKernelSectionResidue i < k ^ totientKernelSectionLevel i := by
  rcases i with ⟨j, q, d⟩
  have hdigit : d.val + 1 < k := by
    have := d.isLt
    omega
  have hq : q.val + 1 ≤ k ^ j.val := Nat.succ_le_iff.mpr q.isLt
  simp only [totientKernelSectionResidue, totientKernelSectionLevel]
  calc
    k * q.val + (d.val + 1) < k * q.val + k :=
      Nat.add_lt_add_left hdigit _
    _ = k * (q.val + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ k * k ^ j.val := Nat.mul_le_mul_left k hq
    _ = k ^ (j.val + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Reducing an encoded residue modulo `k` recovers its nonzero last digit. -/
theorem totientKernelSectionResidue_mod {k e : ℕ} (hk : 2 ≤ k)
    (i : TotientKernelSectionIndex k e) :
    totientKernelSectionResidue i % k = i.2.2.val + 1 := by
  have hdigit := (totientKernelSectionDigit_bounds hk i).2
  rw [totientKernelSectionResidue, Nat.add_comm,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdigit]

/-- The encoded residue is not divisible by the base. -/
theorem totientKernelSectionResidue_not_dvd {k e : ℕ} (hk : 2 ≤ k)
    (i : TotientKernelSectionIndex k e) :
    ¬k ∣ totientKernelSectionResidue i := by
  intro hdvd
  have hzero : totientKernelSectionResidue i % k = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  rw [totientKernelSectionResidue_mod hk i] at hzero
  omega

/-- Every section coordinate has the advertised level, residue, and
nondivisibility properties. -/
theorem totientKernelSectionIndex_spec {k e : ℕ} (hk : 2 ≤ k)
    (i : TotientKernelSectionIndex k e) :
    1 ≤ totientKernelSectionLevel i ∧
      totientKernelSectionLevel i ≤ e ∧
      1 ≤ totientKernelSectionResidue i ∧
      totientKernelSectionResidue i < k ^ totientKernelSectionLevel i ∧
      ¬k ∣ totientKernelSectionResidue i := by
  exact ⟨(totientKernelSectionLevel_bounds i).1,
    (totientKernelSectionLevel_bounds i).2,
    totientKernelSectionResidue_pos i,
    totientKernelSectionResidue_lt_pow hk i,
    totientKernelSectionResidue_not_dvd hk i⟩

/-! ## Exact fixed-level residue coordinates -/

/-- The residue represented by quotient/nonzero-digit coordinates at the
fixed positive level `j + 1`. -/
def totientKernelResidueAtLevel (k : ℕ) {j : ℕ}
    (qd : Fin (k ^ j) × Fin (k - 1)) : ℕ :=
  k * qd.1.val + (qd.2.val + 1)

/-- A fixed-level encoded residue is positive. -/
theorem totientKernelResidueAtLevel_pos (k : ℕ) {j : ℕ}
    (qd : Fin (k ^ j) × Fin (k - 1)) :
    0 < totientKernelResidueAtLevel k qd := by
  simp only [totientKernelResidueAtLevel]
  omega

/-- A fixed-level encoded residue lies below `k^(j+1)`. -/
theorem totientKernelResidueAtLevel_lt_pow (k : ℕ) {j : ℕ} (hk : 2 ≤ k)
    (qd : Fin (k ^ j) × Fin (k - 1)) :
    totientKernelResidueAtLevel k qd < k ^ (j + 1) := by
  have hdigit : qd.2.val + 1 < k := by
    have := qd.2.isLt
    omega
  have hq : qd.1.val + 1 ≤ k ^ j := Nat.succ_le_iff.mpr qd.1.isLt
  simp only [totientKernelResidueAtLevel]
  calc
    k * qd.1.val + (qd.2.val + 1) < k * qd.1.val + k :=
      Nat.add_lt_add_left hdigit _
    _ = k * (qd.1.val + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ k * k ^ j := Nat.mul_le_mul_left k hq
    _ = k ^ (j + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Modulo the base, a fixed-level encoded residue is exactly its nonzero
last digit. -/
theorem totientKernelResidueAtLevel_mod (k : ℕ) {j : ℕ} (hk : 2 ≤ k)
    (qd : Fin (k ^ j) × Fin (k - 1)) :
    totientKernelResidueAtLevel k qd % k = qd.2.val + 1 := by
  have hdigit : qd.2.val + 1 < k := by
    have := qd.2.isLt
    omega
  rw [totientKernelResidueAtLevel, Nat.add_comm,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdigit]

/-- A fixed-level encoded residue is not divisible by the base. -/
theorem totientKernelResidueAtLevel_not_dvd (k : ℕ) {j : ℕ} (hk : 2 ≤ k)
    (qd : Fin (k ^ j) × Fin (k - 1)) :
    ¬k ∣ totientKernelResidueAtLevel k qd := by
  intro hdvd
  have hzero : totientKernelResidueAtLevel k qd % k = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  rw [totientKernelResidueAtLevel_mod k hk qd] at hzero
  omega

/-- Quotient/nonzero-digit coordinates are injective at each fixed level. -/
theorem totientKernelResidueAtLevel_injective (k j : ℕ) (hk : 2 ≤ k) :
    Function.Injective
      (totientKernelResidueAtLevel k :
        Fin (k ^ j) × Fin (k - 1) → ℕ) := by
  intro a b hab
  have hdigit : a.2.val + 1 = b.2.val + 1 := by
    calc
      a.2.val + 1 = totientKernelResidueAtLevel k a % k :=
        (totientKernelResidueAtLevel_mod k hk a).symm
      _ = totientKernelResidueAtLevel k b % k := congrArg (fun n => n % k) hab
      _ = b.2.val + 1 := totientKernelResidueAtLevel_mod k hk b
  have hmul : k * a.1.val = k * b.1.val := by
    simp only [totientKernelResidueAtLevel] at hab
    omega
  apply Prod.ext
  · apply Fin.ext
    exact Nat.mul_left_cancel (by omega : 0 < k) hmul
  · apply Fin.ext
    omega

/-- Every positive nonmultiple below `k^(j+1)` has a unique fixed-level
quotient/nonzero-digit representation.  The representative is Euclidean:
`q = r / k` and `d = r % k - 1`. -/
theorem existsUnique_totientKernelResidueAtLevel
    (k j r : ℕ) (hk : 2 ≤ k) (_hrpos : 1 ≤ r)
    (hrlt : r < k ^ (j + 1)) (hnotdvd : ¬k ∣ r) :
    ∃! qd : Fin (k ^ j) × Fin (k - 1),
      totientKernelResidueAtLevel k qd = r := by
  have hkpos : 0 < k := by omega
  have hmodne : r % k ≠ 0 := by
    intro hzero
    exact hnotdvd (Nat.dvd_of_mod_eq_zero hzero)
  have hmodpos : 0 < r % k := Nat.pos_of_ne_zero hmodne
  have hmodlt : r % k < k := Nat.mod_lt r hkpos
  have hq : r / k < k ^ j := by
    exact (Nat.div_lt_iff_lt_mul hkpos).2 (by
      simpa only [pow_succ] using hrlt)
  have hd : r % k - 1 < k - 1 := by omega
  let q : Fin (k ^ j) := ⟨r / k, hq⟩
  let d : Fin (k - 1) := ⟨r % k - 1, hd⟩
  have hrepr : totientKernelResidueAtLevel k (q, d) = r := by
    simp only [totientKernelResidueAtLevel, q, d]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r % k), Nat.add_comm]
    exact Nat.mod_add_div r k
  refine ⟨(q, d), hrepr, ?_⟩
  intro qd hqd
  exact totientKernelResidueAtLevel_injective k j hk
    (hqd.trans hrepr.symm)

/-- At level `j + 1`, the quotient/nonzero-digit coordinates have cardinality
`k^(j+1) - k^j`. -/
theorem card_totientKernelSectionLevel (k j : ℕ) :
    Fintype.card (Fin (k ^ j) × Fin (k - 1)) =
      k ^ (j + 1) - k ^ j := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Nat.mul_sub_left_distrib, Nat.mul_one, pow_succ]

/-- The section-coordinate cardinality is the transparent telescoping sum
`sum_{j<e} (k^(j+1) - k^j)`. -/
theorem card_totientKernelSectionIndex (k e : ℕ) :
    Fintype.card (TotientKernelSectionIndex k e) =
      ∑ j ∈ Finset.range e, (k ^ (j + 1) - k ^ j) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [show (∑ j : Fin e, k ^ j.val * (k - 1)) =
      ∑ j ∈ Finset.range e, k ^ j * (k - 1) from
    Fin.sum_univ_eq_sum_range (fun j => k ^ j * (k - 1)) e]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    card_totientKernelSectionLevel k j

/-- Before telescoping, the complete index cardinality is two plus one block
of `k^j * (k - 1)` coordinates at every `j < e`. -/
theorem card_totientKernelIndex_eq_two_add_sum (k e : ℕ) :
    Fintype.card (TotientKernelIndex k e) =
      2 + ∑ j ∈ Finset.range e, k ^ j * (k - 1) := by
  rw [Fintype.card_sum, card_totientKernelHeadIndex,
    Fintype.card_sigma]
  simp only [Fintype.card_fin, Fintype.card_prod]
  rw [show (∑ j : Fin e, k ^ j.val * (k - 1)) =
      ∑ j ∈ Finset.range e, k ^ j * (k - 1) from
    Fin.sum_univ_eq_sum_range (fun j => k ^ j * (k - 1)) e]

/-- The all-base combinatorial index has cardinality `k^e + 1` for every
`k ≥ 2`.  The statement is valid also at `e = 0`; the intended finite-level
application uses `e ≥ 1`. -/
theorem card_totientKernelIndex (k e : ℕ) (hk : 2 ≤ k) :
    Fintype.card (TotientKernelIndex k e) = k ^ e + 1 := by
  rw [card_totientKernelIndex_eq_two_add_sum, ← Finset.sum_mul]
  have hgeom := geom_sum_mul_of_one_le (x := k) (by omega : 1 ≤ k) e
  rw [hgeom]
  have hpow : 1 ≤ k ^ e := Nat.one_le_pow e k (by omega)
  omega

end Erdos249257
