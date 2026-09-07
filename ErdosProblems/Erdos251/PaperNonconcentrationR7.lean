import ErdosProblems.Erdos251.PaperCoreR7
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Stability of fixed-block polynomial nonconcentration

This is proof source, not a compiler receipt. `finite_perturbation_stability`
is the GENERIC theorem `res:nonconcentration`, not a replacement of the
prime-specific Schlage-Puchta input by an axiom. The latter is an explicit
premise of the separate application theorem and remains a coverage gap.

Density zero is written in its epsilon/cardinality form. This avoids
implicit use of a density limit whose existence has not been established.
-/

open scoped BigOperators
open Finset

namespace ErdosProblems.Erdos251.PaperR7

noncomputable section

/-- Asymptotic density zero, with no assumption of existence of a density. -/
def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N

/-- Fixed-block polynomial nonconcentration for an integer word. -/
def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}

theorem zeroDensity_mono {s t : Set ℕ} (hst : s ⊆ t)
    (ht : ZeroDensity t) : ZeroDensity s := by
  classical
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := ht ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hs : (range N).filter (fun n => n ∈ s) ⊆
      (range N).filter (fun n => n ∈ t) := by
    intro n hn
    obtain ⟨hnN, hns⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN, hst hns⟩
  have hc : (((range N).filter (fun n => n ∈ s)).card : ℝ) ≤
      (((range N).filter (fun n => n ∈ t)).card : ℝ) := by
    exact_mod_cast card_le_card hs
  exact lt_of_le_of_lt hc (hN₀ N hN)

/-- Substitution `X_i ↦ X_i + v_i`, over the same integer coefficient ring. -/
def translatePolynomial {ι : Type*} (v : ι → ℤ) :
    MvPolynomial ι ℤ →+* MvPolynomial ι ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.X i + MvPolynomial.C (v i))

@[simp] theorem translatePolynomial_C {ι : Type*} (v : ι → ℤ) (c : ℤ) :
    translatePolynomial v (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [translatePolynomial]

@[simp] theorem translatePolynomial_X {ι : Type*} (v : ι → ℤ) (i : ι) :
    translatePolynomial v (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (v i) := by
  simp [translatePolynomial]

/-- Translation has an explicit inverse, hence cannot annihilate a
nonzero polynomial. This proves the nonzero condition for the product below. -/
theorem translatePolynomial_cancel {ι : Type*} (v : ι → ℤ)
    (F : MvPolynomial ι ℤ) :
    translatePolynomial (fun i => -v i) (translatePolynomial v F) = F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP, translatePolynomial_X, map_add, translatePolynomial_C]
      rw [add_assoc, ← MvPolynomial.C_add]
      simp

theorem translatePolynomial_ne_zero {ι : Type*} (v : ι → ℤ)
    {F : MvPolynomial ι ℤ} (hF : F ≠ 0) : translatePolynomial v F ≠ 0 := by
  intro hz
  have h := congrArg (translatePolynomial (fun i => -v i)) hz
  apply hF
  simpa only [translatePolynomial_cancel, map_zero] using h

/-- Evaluation of a translated polynomial is evaluation on the translated
block, with no coefficient-height or degree hypothesis. -/
theorem eval_translatePolynomial {ι : Type*} (x v : ι → ℤ)
    (F : MvPolynomial ι ℤ) :
    MvPolynomial.eval x (translatePolynomial v F) =
      MvPolynomial.eval (fun i => x i + v i) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP, translatePolynomial_X, map_add,
        MvPolynomial.eval_X, MvPolynomial.eval_C]

/-- `res:nonconcentration`. A single finite product converts every possible
perturbation block to one nonzero polynomial on the original word. -/
theorem finite_perturbation_stability
    (a b : ℕ → ℤ) (E : Finset ℤ)
    (ha : FixedBlockNonconcentration a)
    (hE : ∀ n, b n - a n ∈ E) :
    FixedBlockNonconcentration b := by
  classical
  intro m hm F hF
  let v : (Fin m → ↥E) → Fin m → ℤ := fun e i => (e i : ℤ)
  let Q : MvPolynomial (Fin m) ℤ :=
    ∏ e : Fin m → ↥E, translatePolynomial (v e) F
  have hQ : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro e _he
    exact translatePolynomial_ne_zero (v e) hF
  apply zeroDensity_mono (t :=
    {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) Q = 0})
    ?_ (ha m hm Q hQ)
  intro n hn
  let e : Fin m → ↥E := fun i =>
    ⟨b (n + i.val) - a (n + i.val), hE (n + i.val)⟩
  change MvPolynomial.eval (fun i : Fin m => a (n + i.val)) Q = 0
  dsimp [Q]
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  rw [eval_translatePolynomial]
  have hx : (fun i : Fin m => a (n + i.val) + v e i) =
      (fun i : Fin m => b (n + i.val)) := by
    funext i
    dsimp [v, e]
    ring
  rw [hx]
  exact hn

/-- The exact rationalisation and cumulative inequalities from
`res:nonconc-primes`, CONDITIONAL on the external actual-prime
nonconcentration theorem. The PNT asymptotic is not smuggled into this
statement. This is explicitly partial coverage of that corollary. -/
theorem prime_perturbation_of_nonconcentration
    (hNC : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ)))
    (M K : ℕ) (hM : 0 < M) :
    ∃ (b : ℕ → ℕ) (r : ℚ),
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ n < K, b n = primeGap0 n) ∧
      (∀ n, b n = primeGap0 n ∨ b n = primeGap0 n + M) ∧
      (∀ n, b n ≡ primeGap0 n [MOD M]) ∧
      FixedBlockNonconcentration (fun n => (b n : ℤ)) ∧
      (∀ n, prime0 n ≤ 2 + ∑ i ∈ range n, b i) ∧
      (∀ n, 2 + ∑ i ∈ range n, b i ≤ prime0 n + M * n) := by
  classical
  obtain ⟨δ, r, hδ, hprefix, hsum⟩ :=
    rational_bounded_perturbation summable_primeGapDyadicTerm M K hM
  let b : ℕ → ℕ := fun n => primeGap0 n + M * δ n
  have hδle : ∀ n, δ n ≤ 1 := by
    intro n
    rcases hδ n with h | h <;> omega
  have hbounds := perturbed_cumulative_bounds M δ hδle
  refine ⟨b, r, hsum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    simp [b, hprefix n hn]
  · intro n
    rcases hδ n with h | h
    · left; simp [b, h]
    · right; simp [b, h]
  · intro n
    simp [b, Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  · apply finite_perturbation_stability
      (fun n => (primeGap0 n : ℤ)) (fun n => (b n : ℤ)) {0, (M : ℤ)} hNC
    intro n
    rcases hδ n with h | h <;> simp [b, h]
  · intro n
    exact (hbounds n).1
  · intro n
    exact (hbounds n).2

/-- A fixed difference of two distinct coordinates is a nonzero polynomial.
This is the algebraic input for the long record's sparsity assertions. -/
def differencePolynomial (h : ℕ) (r : ℤ) : MvPolynomial (Fin (h + 2)) ℤ :=
  MvPolynomial.X ⟨h + 1, by omega⟩ - MvPolynomial.X ⟨1, by omega⟩ - MvPolynomial.C r

theorem differencePolynomial_ne_zero {h : ℕ} (hh : 0 < h) (r : ℤ) :
    differencePolynomial h r ≠ 0 := by
  classical
  intro hz
  have heval := congrArg (MvPolynomial.eval
    (fun k : Fin (h + 2) => if (k : ℕ) = h + 1 then r + 1 else 0)) hz
  rw [differencePolynomial] at heval
  simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, map_zero] at heval
  rw [if_pos trivial, if_neg (show ¬ (1 = h + 1) by omega)] at heval
  omega

/-- Density zero for each specified gap difference, with the missing
prime-specific analytic theorem exposed as one precise premise. -/
theorem gap_difference_zeroDensity_of_nonconcentration
    (hNC : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ)))
    (h : ℕ) (hh : 0 < h) (r : ℤ) :
    ZeroDensity {N | (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) = r} := by
  have h := hNC (h + 2) (by omega) (differencePolynomial h r)
    (differencePolynomial_ne_zero hh r)
  simpa only [differencePolynomial, MvPolynomial.eval_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C, Nat.add_assoc, sub_eq_zero] using h

/-- Nonconcentration excludes any finite list of specified difference
values. The analytic hypothesis remains explicit. -/
theorem gap_difference_mem_zeroDensity_of_nonconcentration
    (hNC : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ)))
    (h : ℕ) (hh : 0 < h) (R : Finset ℤ) :
    ZeroDensity {N | (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) ∈ R} := by
  classical
  let F : MvPolynomial (Fin (h + 2)) ℤ := ∏ r ∈ R, differencePolynomial h r
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun r _ => differencePolynomial_ne_zero hh r)
  apply zeroDensity_mono (t :=
    {n | MvPolynomial.eval (fun i : Fin (h + 2) => (primeGap0 (n + i.val) : ℤ)) F = 0})
    ?_ (hNC (h + 2) (by omega) F hF)
  intro n hn
  change MvPolynomial.eval (fun i : Fin (h + 2) => (primeGap0 (n + i.val) : ℤ)) F = 0
  dsimp [F]
  rw [map_prod]
  apply Finset.prod_eq_zero hn
  simp [differencePolynomial, MvPolynomial.eval_sub, Nat.add_assoc]

/-- Full algebraic consumer for `res:sparse`. Without parity, the integer
mismatch already lies in the four-element set {-2,-1,1,2}; the density
argument therefore does not need a separate prime-gap parity theorem. -/
theorem small_mismatch_zeroDensity_of_nonconcentration
    (hNC : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ)))
    (h : ℕ) (hh : 0 < h) :
    ZeroDensity {N | 1 ≤ N ∧
      (-1 < realTailShift realPrimeGapTail h N ∧ realTailShift realPrimeGapTail h N < 1) ∧
      (-1 < realTailShift realPrimeGapTail h (N + 1) ∧
        realTailShift realPrimeGapTail h (N + 1) < 1) ∧
      primeGap0 (N + h + 1) ≠ primeGap0 (N + 1)} ∧
    ZeroDensity {N | primeGap0 (N + h + 1) = primeGap0 (N + 1)} := by
  constructor
  · apply zeroDensity_mono (t :=
      {N | (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) ∈
        ({-2, -1, 1, 2} : Finset ℤ)}) ?_
      (gap_difference_mem_zeroDensity_of_nonconcentration hNC h hh {-2, -1, 1, 2})
    intro N hN
    obtain ⟨_hN, ⟨hlo, hhi⟩, ⟨hslo, hshi⟩, hne⟩ := hN
    have hstep := realTailShift_succ realPrimeGapTail_recurrence h N
    have hlow : (-3 : ℤ) < (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) := by
      have hlowR : (-3 : ℝ) < (primeGap0 (N + h + 1) : ℝ) - primeGap0 (N + 1) := by
        push_cast at hstep
        linarith
      exact_mod_cast hlowR
    have hupp : (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) < (3 : ℤ) := by
      have huppR : (primeGap0 (N + h + 1) : ℝ) - primeGap0 (N + 1) < (3 : ℝ) := by
        push_cast at hstep
        linarith
      exact_mod_cast huppR
    change (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) ∈ ({-2, -1, 1, 2} : Finset ℤ)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · apply zeroDensity_mono (t :=
      {N | (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) = 0}) ?_
      (gap_difference_zeroDensity_of_nonconcentration hNC h hh 0)
    intro N hN
    change (primeGap0 (N + h + 1) : ℤ) - primeGap0 (N + 1) = 0
    rw [hN]
    ring

end
end ErdosProblems.Erdos251.PaperR7
