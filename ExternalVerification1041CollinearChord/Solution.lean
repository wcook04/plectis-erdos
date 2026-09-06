/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1041.CollinearRootCase

/-!
# Source transport for the Erdős #1041 collinear straight-chord package

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

namespace Erdos249257.ExternalVerification1041CollinearChord

open Set
open Polynomial

def realSegment (a b : ℂ) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * a + (t : ℂ) * b

private theorem realSegment_eq (a b : ℂ) (t : ℝ) :
    realSegment a b t = ErdosProblems.Erdos1041.realSegment a b t := rfl

structure CollinearPeakCertificate (f : ℂ → ℂ) (a b c : ℂ) : Prop where
  endpoint_distance_lt_two : dist a b < 2
  critical_value_lt_one : ‖f c‖ < 1
  segment_control : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (realSegment a b t)‖ ≤ ‖f c‖

structure CollinearScaleCriticalFamily
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) (D M : ℝ) where
  critical : ι → ℂ
  leftRoot : ι → ℂ
  rightRoot : ι → ℂ
  left_isRoot : ∀ i, p.eval (leftRoot i) = 0
  right_isRoot : ∀ i, p.eval (rightRoot i) = 0
  roots_ne : ∀ i, leftRoot i ≠ rightRoot i
  endpoint_distance_le : ∀ i, dist (leftRoot i) (rightRoot i) ≤ D
  critical_product_le : ∏ i, ‖p.eval (critical i)‖ ≤ M ^ Fintype.card ι
  segment_control : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
    ‖p.eval (realSegment (leftRoot i) (rightRoot i) t)‖ ≤
      ‖p.eval (critical i)‖

/-- The challenge-local peak certificate is the source peak certificate. -/
def CollinearPeakCertificate.toSource
    {f : ℂ → ℂ} {a b c : ℂ} (h : CollinearPeakCertificate f a b c) :
    ErdosProblems.Erdos1041.CollinearPeakCertificate f a b c where
  endpoint_distance_lt_two := h.endpoint_distance_lt_two
  critical_value_lt_one := h.critical_value_lt_one
  segment_control := by
    intro t ht
    simpa only [← realSegment_eq] using h.segment_control t ht

/-- The challenge-local critical family is the source critical family. -/
@[reducible] def CollinearScaleCriticalFamily.toSource
    {ι : Type*} [Fintype ι] [Nonempty ι] {p : ℂ[X]} {D M : ℝ}
    (h : CollinearScaleCriticalFamily (ι := ι) p D M) :
    ErdosProblems.Erdos1041.CollinearScaleCriticalFamily (ι := ι) p D M where
  critical := h.critical
  leftRoot := h.leftRoot
  rightRoot := h.rightRoot
  left_isRoot := h.left_isRoot
  right_isRoot := h.right_isRoot
  roots_ne := h.roots_ne
  endpoint_distance_le := h.endpoint_distance_le
  critical_product_le := h.critical_product_le
  segment_control := by
    intro i t ht
    simpa only [← realSegment_eq] using h.segment_control i t ht

theorem CollinearScaleCriticalFamily.exists_erdos1041_chord
    {n : ℕ} (hn : 2 ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) {D : ℝ} (hD : 0 < D) (hD2 : D < 2)
    (h : CollinearScaleCriticalFamily p D
      ((D / 2) ^ n / (2 : ℝ) ^ (n - 2))) :
    ∃ i : ι,
      p.eval (h.leftRoot i) = 0 ∧
      p.eval (h.rightRoot i) = 0 ∧
      h.leftRoot i ≠ h.rightRoot i ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
          ‖p.eval (realSegment (h.leftRoot i) (h.rightRoot i) t)‖ < 1) ∧
        dist (h.leftRoot i) (h.rightRoot i) < 2 := by
  obtain ⟨i, hli, hri, hne, hseg, hdist⟩ :=
    ErdosProblems.Erdos1041.CollinearScaleCriticalFamily.exists_erdos1041_chord
      hn p hD hD2 h.toSource
  refine ⟨i, hli, hri, hne, ?_, hdist⟩
  intro t ht
  simpa only [← realSegment_eq] using hseg t ht

theorem CollinearScaleCriticalFamily.exists_diameter_chord
    {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) {D : ℝ} (hD : 0 < D)
    (h : CollinearScaleCriticalFamily p D
      ((D / 2) ^ n / (2 : ℝ) ^ (n - 2))) :
    ∃ i : ι,
      p.eval (h.leftRoot i) = 0 ∧
      p.eval (h.rightRoot i) = 0 ∧
      h.leftRoot i ≠ h.rightRoot i ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
          ‖p.eval (realSegment (h.leftRoot i) (h.rightRoot i) t)‖ ≤
            (D / 2) ^ n / (2 : ℝ) ^ (n - 2)) ∧
        dist (h.leftRoot i) (h.rightRoot i) ≤ D := by
  obtain ⟨i, hli, hri, hne, hseg, hdist⟩ :=
    ErdosProblems.Erdos1041.CollinearScaleCriticalFamily.exists_diameter_chord
      (n := n) p hD h.toSource
  refine ⟨i, hli, hri, hne, ?_, hdist⟩
  intro t ht
  simpa only [← realSegment_eq] using hseg t ht

theorem polynomial_straightSegment_solution_of_collinearPeak
    (p : ℂ[X]) {a b c : ℂ}
    (h : CollinearPeakCertificate p.eval a b c) :
    (∀ t ∈ Icc (0 : ℝ) 1, ‖p.eval (realSegment a b t)‖ < 1) ∧
      dist a b < 2 := by
  obtain ⟨hseg, hdist⟩ :=
    ErdosProblems.Erdos1041.polynomial_straightSegment_solution_of_collinearPeak
      p h.toSource
  refine ⟨?_, hdist⟩
  intro t ht
  simpa only [← realSegment_eq] using hseg t ht

end Erdos249257.ExternalVerification1041CollinearChord
