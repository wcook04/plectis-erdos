import ErdosProblems.Erdos251.NonconcentrationCoreR11
import ErdosProblems.Erdos251.SparsePaperR11

/-! # Exact density-zero consumers and the limitation of the averaging remark
UNRUN. All generic conclusions are proved from fixed-block nonconcentration;
no growing-polynomial-family assertion is inferred from a fixed-block premise.
-/
noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR11.Nonconcentration
open PaperR8.SparseSchedule SparsePaper

def zeroCount (s : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter (fun n => n ∈ s)).card

theorem fixed_difference_zeroDensity (g : ℕ → ℤ) (hNC : FixedBlockNonconcentration g)
    (h : ℕ) (hh : 0 < h) (r : ℤ) :
    ZeroDensity {N | g (N + h + 1) - g (N + 1) = r} := by
  have hz := hNC (h + 2) (by omega) (differencePolynomial h r) (differencePolynomial_ne_zero hh r)
  simpa only [differencePolynomial, MvPolynomial.eval_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C, Nat.add_assoc, sub_eq_zero] using hz

theorem fixed_difference_mem_zeroDensity (g : ℕ → ℤ) (hNC : FixedBlockNonconcentration g)
    (h : ℕ) (hh : 0 < h) (R : Finset ℤ) :
    ZeroDensity {N | g (N + h + 1) - g (N + 1) ∈ R} := by
  classical
  let F : MvPolynomial (Fin (h + 2)) ℤ := ∏ r ∈ R, differencePolynomial h r
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun r _ => differencePolynomial_ne_zero hh r)
  apply zeroDensity_mono (t :=
    {n | MvPolynomial.eval (fun i : Fin (h + 2) => g (n + i.val)) F = 0})
    ?_ (hNC (h + 2) (by omega) F hF)
  intro n hn
  change MvPolynomial.eval (fun i : Fin (h + 2) => g (n + i.val)) F = 0
  dsimp [F]
  rw [map_prod]
  apply Finset.prod_eq_zero hn
  simp [differencePolynomial, MvPolynomial.eval_sub, Nat.add_assoc]

def shift (T : ℕ → ℝ) (h N : ℕ) : ℝ := T (N + h) - T N

def Recurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

theorem shift_succ {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : Recurrence g T) (h N : ℕ) :
    shift T h (N + 1) = 2 * shift T h N - (g (N + h + 1) - g (N + 1) : ℤ) := by
  unfold shift
  rw [show N + 1 + h = (N + h) + 1 by omega, hrec, hrec]
  push_cast
  ring

/-- Endpoint parity is needed only to sharpen the four possible integers to ±2. -/
theorem small_even_mismatch {d : ℤ} {x y : ℝ}
    (hd : (2 : ℤ) ∣ d) (hstep : (d : ℝ) = 2 * x - y)
    (hx : -1 < x ∧ x < 1) (hy : -1 < y ∧ y < 1) (hne : d ≠ 0) :
    d = 2 ∨ d = -2 := by
  have hlo : (-3 : ℤ) < d := by
    have : (-3 : ℝ) < d := by linarith
    exact_mod_cast this
  have hhi : d < (3 : ℤ) := by
    have : (d : ℝ) < 3 := by linarith
    exact_mod_cast this
  obtain ⟨k, hk⟩ := hd
  omega

theorem small_mismatch_zeroDensity (g : ℕ → ℤ) (T : ℕ → ℝ)
    (hNC : FixedBlockNonconcentration g) (hrec : Recurrence g T)
    (h : ℕ) (hh : 0 < h) :
    ZeroDensity {N | 1 ≤ N ∧ (-1 < shift T h N ∧ shift T h N < 1) ∧
      (-1 < shift T h (N + 1) ∧ shift T h (N + 1) < 1) ∧
      g (N + h + 1) ≠ g (N + 1)} ∧
    ZeroDensity {N | g (N + h + 1) = g (N + 1)} := by
  constructor
  · apply zeroDensity_mono (t := {N | g (N + h + 1) - g (N + 1) ∈ ({-2, -1, 1, 2} : Finset ℤ)})
      ?_ (fixed_difference_mem_zeroDensity g hNC h hh {-2, -1, 1, 2})
    intro N hN
    obtain ⟨_, ⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hne⟩ := hN
    have hstep := shift_succ hrec h N
    have hlo : (-3 : ℤ) < g (N + h + 1) - g (N + 1) := by
      have hR : (-3 : ℝ) < (g (N + h + 1) - g (N + 1) : ℤ) := by linarith
      exact_mod_cast hR
    have hhi : g (N + h + 1) - g (N + 1) < (3 : ℤ) := by
      have hR : ((g (N + h + 1) - g (N + 1) : ℤ) : ℝ) < 3 := by linarith
      exact_mod_cast hR
    simp only [Set.mem_setOf_eq, mem_insert, mem_singleton]
    omega
  · apply zeroDensity_mono (t := {N | g (N + h + 1) - g (N + 1) = 0}) ?_
      (fixed_difference_zeroDensity g hNC h hh 0)
    intro N hN
    change g (N + h + 1) - g (N + 1) = 0
    rw [hN]
    ring

/-- A density-zero event cannot have any eventually positive lower-density budget. -/
theorem zeroDensity_no_positive_lower_density {s : Set ℕ} (hs : ZeroDensity s) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → δ * N ≤ zeroCount s N := by
  rintro ⟨δ, hδ, N₀, hN₀⟩
  obtain ⟨N₁, hN₁⟩ := hs (δ / 2) (by positivity)
  let N := max 1 (max N₀ N₁)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by dsimp [N]; omega)
  have h0 := hN₀ N (by dsimp [N]; omega)
  have h1 := hN₁ N (by dsimp [N]; omega)
  change (zeroCount s N : ℝ) < (δ / 2) * N at h1
  nlinarith [mul_pos hδ hNpos]

theorem zeroDensity_complement_cofinal {s : Set ℕ} (hs : ZeroDensity s) :
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ N ∉ s := by
  classical
  intro N₀
  by_contra hnot
  have hall : ∀ N, N₀ ≤ N → N ∈ s := by
    intro N hN
    by_contra hn
    exact hnot ⟨N, hN, hn⟩
  obtain ⟨N₁, hN₁⟩ := hs (1 / 2) (by norm_num)
  let N := 2 * (N₀ + N₁ + 1)
  have hN0 : N₀ ≤ N := by dsimp [N]; omega
  have hN1 : N₁ ≤ N := by dsimp [N]; omega
  have hsub : Ico N₀ N ⊆ (range N).filter (fun n => n ∈ s) := by
    intro n hn
    obtain ⟨hn0, hn1⟩ := mem_Ico.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr hn1, hall n hn0⟩
  have hc : N - N₀ ≤ zeroCount s N := by
    simpa only [Nat.card_Ico, zeroCount] using card_le_card hsub
  have hcR : (N : ℝ) - N₀ ≤ zeroCount s N := by
    have hNat : N ≤ N₀ + zeroCount s N := by omega
    have hReal : (N : ℝ) ≤ N₀ + zeroCount s N := by exact_mod_cast hNat
    linarith
  have h1 := hN₁ N hN1
  change (zeroCount s N : ℝ) < (1 / 2 : ℝ) * N at h1
  have hNbig : 2 * (N₀ : ℝ) + 2 ≤ (N : ℝ) := by
    dsimp [N]
    push_cast
    nlinarith [(Nat.cast_nonneg N₁ : (0 : ℝ) ≤ N₁)]
  linarith

/-- The mismatch-only half of the producer holds cofinally, but the conjunction need not. -/
theorem fixed_offset_mismatch_cofinal (g : ℕ → ℤ) (hNC : FixedBlockNonconcentration g)
    (h : ℕ) (hh : 0 < h) :
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ g (N + h + 1) ≠ g (N + 1) := by
  have hz : ZeroDensity {N | g (N + h + 1) = g (N + 1)} := by
    simpa only [sub_eq_zero] using fixed_difference_zeroDensity g hNC h hh 0
  exact zeroDensity_complement_cofinal hz

theorem upperBanachZero_implies_zeroDensity {s : Set ℕ} (hs : UpperBanachZero s) : ZeroDensity s := by
  classical
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := (upperBanachZero_iff_uniform s).mp hs (ε / 2) (by positivity)
  refine ⟨max 1 L₀, ?_⟩
  intro N hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h := hL₀ 0 N ((le_max_right _ _).trans hN)
  simp only [Nat.zero_add, Nat.Ico_zero_eq_range] at h
  exact h.trans_lt (by nlinarith [mul_pos hε hN0])

/-- An explicit counterexample to identifying zero density with finitely many witnesses. -/
theorem cofinal_zeroDensity_example :
    ∃ s : Set ℕ, ZeroDensity s ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ N ∈ s := by
  let c : ℕ → ℕ := fun n => n ^ 2
  have hc : StrictMono c := by
    intro i j hij
    dsimp [c]
    nlinarith
  have hg : ∀ R, ∃ J, ∀ j, J ≤ j → R ≤ c (j + 1) - c j := by
    intro R
    refine ⟨R, ?_⟩
    intro j hj
    have he : c (j + 1) = c j + (2 * j + 1) := by dsimp [c]; ring
    rw [he, Nat.add_sub_cancel_left]
    omega
  refine ⟨Set.range c, upperBanachZero_implies_zeroDensity
    (upperBanachZero_of_eventual_spacing c hc hg), ?_⟩
  intro N₀
  exact ⟨c (N₀ + 1), by dsimp [c]; nlinarith, ⟨N₀ + 1, rfl⟩⟩

#print axioms small_mismatch_zeroDensity
#print axioms cofinal_zeroDensity_example
end ErdosProblems.Erdos251.PaperR11.Nonconcentration
