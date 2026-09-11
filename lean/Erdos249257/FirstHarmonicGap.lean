import Erdos249257.LcmConeFlatness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The first-harmonic certificate interface

This module isolates the deterministic part of the remaining analytic
frontier for Erdős #249.  At fixed `(h, N, L)`, `windowFirstCos` is the real
part of the first additive character of the endpoint discrepancy modulo
`2^L`.  If every `N` in a dyadic block failed the certificate, the room
inequality would put every phase within `π/8` of an integer turn, forcing
each cosine above `9/10`.  Therefore one constant-saving first-harmonic gap
produces a finite certificate.

The theorem `exists_certifiedKill_of_first_harmonic_gap` is elementary and
unconditional.  No estimate proving its `hgap` hypothesis is claimed here;
that cofinal analytic estimate remains the open frontier.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

/-- Real part of the first additive character of the endpoint discrepancy
modulo `2^L`. -/
noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))

private lemma nine_tenths_lt_cos_pi_div_eight :
    (9 / 10 : ℝ) < Real.cos (Real.pi / 8) := by
  rw [Real.cos_pi_div_eight]
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2gt : (7 / 5 : ℝ) < Real.sqrt 2 := by nlinarith
  have hs : 0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hssq : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith

private lemma windowFirstCos_gt_of_not_certifiedKill
    {h X L N : ℕ} (hN : N < 2 * X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hnot : ¬ certifiedKill h N L) :
    (9 / 10 : ℝ) < windowFirstCos h N L := by
  set P : ℤ := 2 ^ L
  set r : ℤ := windowDiscrepancy h N L % P
  set W : ℤ := N + h + L + 2
  set B : ℤ := 2 * X + h + L + 2
  have hPpos : 0 < P := by simp [P]
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hPpos.ne'
  have hrP : r < P := Int.emod_lt_of_pos _ hPpos
  have hWB : W ≤ B := by
    dsimp [W, B]
    omega
  have hroomZ : 16 * B ≤ P := by
    dsimp [B, P]
    exact_mod_cast hroom
  have hcases : r ≤ W ∨ P - W ≤ r := by
    unfold certifiedKill at hnot
    change ¬ (W < r ∧ r < P - W) at hnot
    omega
  have hPposR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
  have hnear_cos : ∀ s : ℤ, 0 ≤ s → s ≤ W →
      Real.cos (Real.pi / 8) ≤
        Real.cos (2 * Real.pi * ((s : ℝ) / (P : ℝ))) := by
    intro s hs0 hsW
    have hsB : s ≤ B := hsW.trans hWB
    have hsR0 : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs0
    have hratio : (s : ℝ) / (P : ℝ) ≤ 1 / 16 := by
      apply (div_le_iff₀ hPposR).2
      have hsBR : (16 : ℝ) * (s : ℝ) ≤ (P : ℝ) := by
        exact_mod_cast
          (le_trans (Int.mul_le_mul_of_nonneg_left hsB (by omega)) hroomZ)
      nlinarith
    have hangle0 : 0 ≤ 2 * Real.pi * ((s : ℝ) / (P : ℝ)) := by positivity
    have hangle8 : 2 * Real.pi * ((s : ℝ) / (P : ℝ)) ≤ Real.pi / 8 := by
      nlinarith [Real.pi_pos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hangle0
      (by nlinarith [Real.pi_pos]) hangle8
  unfold windowFirstCos
  change (9 / 10 : ℝ) < Real.cos (2 * Real.pi * ((r : ℝ) / (P : ℝ)))
  rcases hcases with hlow | hhigh
  · exact nine_tenths_lt_cos_pi_div_eight.trans_le (hnear_cos r hr0 hlow)
  · set s : ℤ := P - r
    have hs0 : 0 ≤ s := by dsimp [s]; omega
    have hsW : s ≤ W := by dsimp [s]; omega
    have hphase :
        2 * Real.pi * ((r : ℝ) / (P : ℝ)) =
          2 * Real.pi - 2 * Real.pi * ((s : ℝ) / (P : ℝ)) := by
      dsimp [s]
      push_cast
      field_simp
      ring
    rw [hphase, Real.cos_two_pi_sub]
    exact nine_tenths_lt_cos_pi_div_eight.trans_le (hnear_cos s hs0 hsW)

/-- A first-harmonic saving on any nonempty finite subset of a dyadic block
forces a certificate in that subset.  This is the subset consumer needed by
supplier-fibre arguments; no density or partition hypothesis is used. -/
theorem exists_certifiedKill_of_first_harmonic_gap_subset
    {h X L : ℕ} (T : Finset ℕ)
    (hTlt : ∀ N ∈ T, N < 2 * X)
    (hTne : T.Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ T, windowFirstCos h N L)
        ≤ (9 / 10 : ℝ) * T.card) :
    ∃ N ∈ T, certifiedKill h N L := by
  by_contra hnone
  push Not at hnone
  have hsum :
      (∑ _N ∈ T, (9 / 10 : ℝ)) <
        ∑ N ∈ T, windowFirstCos h N L :=
    Finset.sum_lt_sum_of_nonempty hTne fun N hN => by
      exact windowFirstCos_gt_of_not_certifiedKill
        (hTlt N hN) hroom (hnone N hN)
  rw [Finset.sum_const] at hsum
  simp only [nsmul_eq_mul] at hsum
  nlinarith

/-- A constant-saving first-harmonic gap on one dyadic block forces a finite
certificate somewhere in that block.  Establishing such gaps cofinally is
the analytic input still required for #249. -/
theorem exists_certifiedKill_of_first_harmonic_gap
    {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L)
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  by_contra hnone
  push Not at hnone
  have hs : (Finset.Ico X (2 * X)).Nonempty :=
    ⟨X, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  have hsum :
      (∑ _N ∈ Finset.Ico X (2 * X), (9 / 10 : ℝ)) <
        ∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L :=
    Finset.sum_lt_sum_of_nonempty hs fun N hN => by
      have hNIco := Finset.mem_Ico.mp hN
      exact windowFirstCos_gt_of_not_certifiedKill hNIco.2 hroom (hnone N hN)
  have hcard : (Finset.Ico X (2 * X)).card = X := by
    rw [Nat.card_Ico]
    omega
  rw [Finset.sum_const, hcard] at hsum
  simp only [nsmul_eq_mul] at hsum
  nlinarith

end TotientTailPeriodKiller
end Erdos249257
