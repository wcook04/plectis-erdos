import Mathlib

/-!
# Isolated fixed-block nonconcentration kernel

The two blocks ending at `finite_perturbation_stability` and
`differencePolynomial_ne_zero` below are copied verbatim from the supplied
checked PaperNonconcentrationR7.lean. Only the enclosing namespace/imports
change. This avoids importing unrelated PaperCoreR7 assemblies in the
standalone authoring target. Fresh compilation is still required.
-/
noncomputable section
open scoped BigOperators
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR11.Nonconcentration

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


end ErdosProblems.Erdos251.PaperR11.Nonconcentration
