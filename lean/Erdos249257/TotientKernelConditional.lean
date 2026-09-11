import Erdos249257.TotientKernelReduction
import Erdos249257.TotientKernelIndex
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Conditional exact rank for the all-base totient kernel

This module separates the two layers of the expected all-base theorem.

* The arithmetic layer is unconditional: a composite-base residue divisible
  by `k` reduces to the corresponding lower-level section by an explicit
  nonzero rational scalar.  Iterating this relation proves that the
  filtration-compatible family indexed by `TotientKernelIndex k e` spans the
  complete kernel through level `e`.
* The exact-rank conclusion is conditional on linear independence of that
  canonical family.  That hypothesis is precisely the external mathematical
  input; no theorem of Martin is formalised or assumed as an axiom here.
-/

namespace Erdos249257

open Module

/-- The `(j,r)` base-`k` kernel channel of Euler's totient, viewed over `ℚ`. -/
def allBaseTotientKernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (k ^ j * n + r)

/-- The constant rational multiplier in the one-step composite-base residue
reduction.  Its denominator is nonzero whenever `k > 0`. -/
def totientKernelReductionScalar (k r : ℕ) : ℚ :=
  (Nat.totient k : ℚ) * Nat.gcd k r /
    (Nat.totient (Nat.gcd k r) : ℚ)

/-- The reduction scalar is nonzero for every positive base. -/
theorem totientKernelReductionScalar_ne_zero (k r : ℕ) (hk : 0 < k) :
    totientKernelReductionScalar k r ≠ 0 := by
  have hg : 0 < Nat.gcd k r := Nat.gcd_pos_of_pos_left r hk
  have hphiK : 0 < Nat.totient k := Nat.totient_pos.mpr hk
  have hphiG : 0 < Nat.totient (Nat.gcd k r) := Nat.totient_pos.mpr hg
  simp only [totientKernelReductionScalar]
  change
    (Nat.totient k : ℚ) * Nat.gcd k r /
      Nat.totient (Nat.gcd k r) ≠ 0
  exact div_ne_zero (mul_ne_zero (by exact_mod_cast hphiK.ne')
    (by exact_mod_cast hg.ne')) (by exact_mod_cast hphiG.ne')

/-- **Composite residue scalar reduction.**  Once the lower level is
positive, multiplying its residue and modulus by `k` scales the entire
totient section by a constant depending only on `k` and the residue `r`.

The factor is
`totient(k) * gcd(k,r) / totient(gcd(k,r))`; it is not in general
`totient(k)` for composite `k`. -/
theorem allBaseTotientKernelSeq_mul_residue_step
    (k j r : ℕ) (hk : 0 < k) (hj : 1 ≤ j) :
    allBaseTotientKernelSeq k (j + 1) (k * r) =
      totientKernelReductionScalar k r • allBaseTotientKernelSeq k j r := by
  funext n
  have hg : 0 < Nat.gcd k r := Nat.gcd_pos_of_pos_left r hk
  have hphiGNat : 0 < Nat.totient (Nat.gcd k r) := Nat.totient_pos.mpr hg
  have hphiG : (Nat.totient (Nat.gcd k r) : ℚ) ≠ 0 := by
    exact_mod_cast hphiGNat.ne'
  have hcross :=
    totient_pow_mul_affine_gcd_cross_eq k hk j n r 1 hj (by omega)
  norm_num at hcross
  simp only [allBaseTotientKernelSeq, Pi.smul_apply, smul_eq_mul,
    totientKernelReductionScalar]
  rw [show k ^ (j + 1) * n + k * r = k * (k ^ j * n + r) by ring]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hphiG).2
  have hcrossQ :
      (Nat.totient (Nat.gcd k r) : ℚ) *
          Nat.totient (k * (k ^ j * n + r)) =
        (Nat.totient k : ℚ) * Nat.gcd k r *
          Nat.totient (k ^ j * n + r) := by
    exact_mod_cast hcross
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hcrossQ

/-- The filtration-compatible all-base family: two distinguished zero
residue channels and every positive residue not divisible by `k`. -/
def canonicalAllBaseTotientKernelFamily (k e : ℕ) :
    TotientKernelIndex k e → ℕ → ℚ
  | Sum.inl .F00 => allBaseTotientKernelSeq k 0 0
  | Sum.inl .F10 => allBaseTotientKernelSeq k 1 0
  | Sum.inr i => allBaseTotientKernelSeq k
      (totientKernelSectionLevel i) (totientKernelSectionResidue i)

/-- Every base-`k` totient channel at levels `0,...,e`, before removing
reducible residue channels. -/
abbrev AllBaseTotientKernelThroughLevelIndex (k e : ℕ) :=
  Σ j : Fin (e + 1), Fin (k ^ j.val)

/-- The complete finite all-base kernel through level `e`. -/
def allBaseTotientKernelThroughLevelFamily (k e : ℕ) :
    AllBaseTotientKernelThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => allBaseTotientKernelSeq k j.val r.val

/-- Every channel through a positive depth belongs to the span of the
filtration-compatible canonical all-base family.  This spanning theorem is
unconditional: composite residues are reduced recursively by
`allBaseTotientKernelSeq_mul_residue_step`. -/
theorem allBaseTotientKernelSeq_mem_span_canonical_of_le
    {k e j r : ℕ} (hk : 2 ≤ k) (hj : j ≤ e)
    (hr : r < k ^ j) :
    allBaseTotientKernelSeq k j r ∈
      Submodule.span ℚ
        (Set.range (canonicalAllBaseTotientKernelFamily k e)) := by
  have hkpos : 0 < k := by omega
  induction j generalizing r with
  | zero =>
      have hr0 : r = 0 := by simpa using hr
      subst r
      exact Submodule.subset_span ⟨Sum.inl .F00, rfl⟩
  | succ j ih =>
      by_cases hr0 : r = 0
      · subst r
        have hbase : allBaseTotientKernelSeq k 1 0 ∈
            Submodule.span ℚ
              (Set.range (canonicalAllBaseTotientKernelFamily k e)) :=
          Submodule.subset_span ⟨Sum.inl .F10, rfl⟩
        have hzero : allBaseTotientKernelSeq k (j + 1) 0 =
            (k ^ j : ℚ) • allBaseTotientKernelSeq k 1 0 := by
          funext n
          simp only [allBaseTotientKernelSeq, Pi.smul_apply, smul_eq_mul,
            add_zero, pow_one]
          have hNat := totient_pow_mul_eq k hkpos n (j + 1) (by omega)
          rw [show j + 1 - 1 = j by omega] at hNat
          exact_mod_cast hNat
        rw [hzero]
        exact Submodule.smul_mem _ _ hbase
      · by_cases hdiv : k ∣ r
        · obtain ⟨s, rfl⟩ := hdiv
          have hjpos : 1 ≤ j := by
            by_contra h
            have hjzero : j = 0 := by omega
            subst j
            norm_num at hr
            have hsne : s ≠ 0 := by
              intro hs
              subst s
              simp at hr0
            have hspos : 0 < s := Nat.pos_of_ne_zero hsne
            have hle : k * 1 ≤ k * s :=
              Nat.mul_le_mul_left k (by omega)
            omega
          have hsBound : s < k ^ j := by
            have hmul : k * s < k * k ^ j := by
              simpa only [pow_succ, Nat.mul_comm] using hr
            exact (Nat.mul_lt_mul_left hkpos).mp hmul
          have hlower := ih (by omega) hsBound
          rw [allBaseTotientKernelSeq_mul_residue_step k j s hkpos hjpos]
          exact Submodule.smul_mem _ _ hlower
        · have hjlt : j < e := by omega
          obtain ⟨qd, hqd, _⟩ :=
            existsUnique_totientKernelResidueAtLevel k j r hk
              (by omega) hr hdiv
          let i : TotientKernelSectionIndex k e := ⟨⟨j, hjlt⟩, qd⟩
          refine Submodule.subset_span ⟨Sum.inr i, ?_⟩
          simp only [canonicalAllBaseTotientKernelFamily,
            totientKernelSectionLevel, totientKernelSectionResidue, i]
          rw [show k * qd.1.val + (qd.2.val + 1) = r from hqd]

/-- At positive depth, every canonical all-base channel occurs literally in
the complete finite truncation. -/
theorem range_canonicalAllBaseTotientKernelFamily_subset_throughLevel
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Set.range (canonicalAllBaseTotientKernelFamily k e) ⊆
      Set.range (allBaseTotientKernelThroughLevelFamily k e) := by
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i =>
      cases i with
      | F00 =>
          exact ⟨⟨⟨0, by omega⟩, ⟨0, by simp⟩⟩, rfl⟩
      | F10 =>
          exact ⟨⟨⟨1, by omega⟩, ⟨0, by positivity⟩⟩, rfl⟩
  | inr i =>
      have hlevel := totientKernelSectionLevel_bounds i
      have hres := totientKernelSectionResidue_lt_pow hk i
      exact ⟨⟨⟨totientKernelSectionLevel i, by omega⟩,
        ⟨totientKernelSectionResidue i, hres⟩⟩, rfl⟩

/-- The complete all-base kernel through a positive level and the canonical
filtration-compatible family span the same subspace. -/
theorem span_allBaseTotientKernelThroughLevelFamily_eq_canonical
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Submodule.span ℚ
        (Set.range (allBaseTotientKernelThroughLevelFamily k e)) =
      Submodule.span ℚ
        (Set.range (canonicalAllBaseTotientKernelFamily k e)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨j, r⟩, rfl⟩
    exact allBaseTotientKernelSeq_mem_span_canonical_of_le hk
      (Nat.le_of_lt_succ j.isLt) r.isLt
  · exact Submodule.span_mono
      (range_canonicalAllBaseTotientKernelFamily_subset_throughLevel
        k e hk he)

/-- Linear independence of the canonical all-base family implies the exact
cardinality-sized rank.  This is the explicit external-input boundary: the
hypothesis is not proved in this module. -/
theorem finrank_canonicalAllBaseTotientKernel_eq_of_linearIndependent
    (k e : ℕ) (hk : 2 ≤ k)
    (hcanon : LinearIndependent ℚ (canonicalAllBaseTotientKernelFamily k e)) :
    finrank ℚ (Submodule.span ℚ
      (Set.range (canonicalAllBaseTotientKernelFamily k e))) = k ^ e + 1 := by
  rw [finrank_span_eq_card hcanon]
  exact card_totientKernelIndex k e hk

/-- **Conditional exact rank of the actual all-base truncation.**  The
arithmetic spanning and index-cardinality layers are formalised above.  The
only hypothesis is linear independence of the explicit canonical family,
which is the external affine-ordering boundary and is not discharged here. -/
theorem finrank_allBaseTotientKernelThroughLevelFamily_eq_of_linearIndependent
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (hcanon : LinearIndependent ℚ (canonicalAllBaseTotientKernelFamily k e)) :
    finrank ℚ (Submodule.span ℚ
      (Set.range (allBaseTotientKernelThroughLevelFamily k e))) = k ^ e + 1 := by
  rw [span_allBaseTotientKernelThroughLevelFamily_eq_canonical k e hk he]
  exact finrank_canonicalAllBaseTotientKernel_eq_of_linearIndependent
    k e hk hcanon

#print axioms allBaseTotientKernelSeq_mul_residue_step
#print axioms span_allBaseTotientKernelThroughLevelFamily_eq_canonical
#print axioms finrank_allBaseTotientKernelThroughLevelFamily_eq_of_linearIndependent

end Erdos249257
