import ErdosProblems.Erdos68.DivisorChannelBasis
import Mathlib.Data.Int.GCD

/-!
Constructive integer-span tools for the attainable-moment theorem.
New compilation and axiom checks: UNRUN.  No unproved span hypothesis is used.
-/
namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp

def SupportedOn (z : ℕ →₀ ℤ) (s : Finset ℕ) : Prop :=
  ∀ i, i ∉ s → z i = 0

noncomputable def integerEvaluation (w : ℕ → ℤ) (z : ℕ →₀ ℤ) : ℤ :=
  z.sum (fun i c => c * w i)

lemma integerEvaluation_zero (w : ℕ → ℤ) : integerEvaluation w 0 = 0 := by
  simp [integerEvaluation]

lemma integerEvaluation_single (w : ℕ → ℤ) (i : ℕ) (c : ℤ) :
    integerEvaluation w (single i c) = c * w i := by
  unfold integerEvaluation
  exact Finsupp.sum_single_index (by simp)

lemma integerEvaluation_add (w : ℕ → ℤ) (a b : ℕ →₀ ℤ) :
    integerEvaluation w (a + b) = integerEvaluation w a + integerEvaluation w b := by
  unfold integerEvaluation
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

lemma integerEvaluation_smul (w : ℕ → ℤ) (c : ℤ) (a : ℕ →₀ ℤ) :
    integerEvaluation w (c • a) = c * integerEvaluation w a := by
  classical
  unfold integerEvaluation
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [smul_eq_mul, mul_assoc]
  unfold Finsupp.sum
  rw [Finset.mul_sum]

lemma integerEvaluation_dvd (w : ℕ → ℤ) (z : ℕ →₀ ℤ) (g : ℤ)
    (h : ∀ i ∈ z.support, g ∣ w i) : g ∣ integerEvaluation w z := by
  classical
  unfold integerEvaluation Finsupp.sum
  exact Finset.dvd_sum (fun i hi => dvd_mul_of_dvd_right (h i hi) _)

/-- The finite gcd is an attained integer combination, with a support witness. -/
theorem finite_gcd_bezout (s : Finset ℕ) (w : ℕ → ℤ) :
    ∃ z : ℕ →₀ ℤ, SupportedOn z s ∧
      integerEvaluation w z = ((s.gcd (fun i => (w i).natAbs) : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨0, ?_, ?_⟩
    · intro i hi
      rfl
    · simp [integerEvaluation]
  | @insert i s hi ih =>
    obtain ⟨z, hz, he⟩ := ih
    let g : ℕ := s.gcd (fun j => (w j).natAbs)
    let A : ℤ := Int.gcdA (w i) (g : ℤ)
    let B : ℤ := Int.gcdB (w i) (g : ℤ)
    refine ⟨single i A + B • z, ?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hj (Finset.mem_insert_self i s)
      have hjs : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
      simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
        hji, Ne.symm hji, hz j hjs]
    · rw [integerEvaluation_add, integerEvaluation_single,
        integerEvaluation_smul, he]
      have hbez := Int.gcd_eq_gcd_ab (w i) (g : ℤ)
      have hgcd : Int.gcd (w i) (g : ℤ) =
          (insert i s).gcd (fun j => (w j).natAbs) := by
        simp [Int.gcd_def, g, Finset.gcd_insert, gcd_eq_nat_gcd]
      rw [hgcd] at hbez
      dsimp [A, B, g] at *
      nlinarith [hbez]

/-- Exact cancellation in the support equation; a=0 and negative a,t are allowed. -/
theorem gcd_quotient_dvd_iff (g a t : ℤ) (hg : 0 < g) :
    g / (Int.gcd g a : ℤ) ∣ t ↔ g ∣ t * a := by
  let c : ℤ := Int.gcd g a
  have hcg : c ∣ g := Int.gcd_dvd_left g a
  have hca : c ∣ a := Int.gcd_dvd_right g a
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hcg
    omega
  have hmul : c * (g / c) = g := Int.mul_ediv_cancel' hcg
  change g / c ∣ t ↔ g ∣ t * a
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨r, hr⟩ := hca
    refine ⟨k * r, ?_⟩
    calc
      t * a = (g / c * k) * (c * r) := by rw [hk, hr]
      _ = (c * (g / c)) * (k * r) := by ring
      _ = g * (k * r) := by rw [hmul]
  · intro hga
    have hbez := Int.gcd_eq_gcd_ab g a
    have hgc : g ∣ t * c := by
      have heq : t * c =
          g * (t * Int.gcdA g a) + (t * a) * Int.gcdB g a := by
        dsimp [c]
        rw [hbez]
        ring
      rw [heq]
      exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hga _)
    obtain ⟨k, hk⟩ := hgc
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ hc0
    calc
      c * t = t * c := by ring
      _ = g * k := hk
      _ = (c * (g / c)) * k := congrArg (fun x : ℤ => x * k) hmul.symm
      _ = c * (g / c * k) := by ring

lemma gcd_quotient_pos (g a : ℤ) (hg : 0 < g) :
    0 < g / (Int.gcd g a : ℤ) := by
  have hd : (Int.gcd g a : ℤ) ∣ g := Int.gcd_dvd_left g a
  have hmul := Int.mul_ediv_cancel' hd
  have hc : (0 : ℤ) ≤ Int.gcd g a := by positivity
  by_contra h
  have hq : g / (Int.gcd g a : ℤ) ≤ 0 := by omega
  have hprod := mul_nonpos_of_nonneg_of_nonpos hc hq
  omega

end ErdosProblems.Erdos68.PaperComplete
