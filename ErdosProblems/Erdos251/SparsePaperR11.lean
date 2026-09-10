import ErdosProblems.Erdos251.GrowingBlocksR11

/-! # End-to-end sparse rationalisation and growing-block preservation
Candidate source, UNRUN. One support is chosen before the target value.
There is no density, overlap or statistical conclusion among the inputs.
-/
noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR11.SparsePaper
open PaperR8.SparseSchedule PaperR9.SparseAmbient SparsePolylog GrowingBlocks

/-- The reciprocal-integer and epsilon formulations agree uniformly in translation. -/
def UniformZeroDensity (S : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ a L : ℕ, L₀ ≤ L →
    (((Ico a (a + L)).filter (fun n => n ∈ S)).card : ℝ) ≤ ε * L

theorem upperBanachZero_iff_uniform (S : Set ℕ) :
    UpperBanachZero S ↔ UniformZeroDensity S := by
  classical
  constructor
  · intro h ε hε
    obtain ⟨R, hRbig⟩ := exists_nat_gt (1 / ε)
    have hRp : (0 : ℝ) < R := lt_trans (by positivity) hRbig
    have hRN : 0 < R := by exact_mod_cast hRp
    obtain ⟨L₀, hL₀⟩ := h R hRN
    refine ⟨L₀, ?_⟩
    intro a L hL
    have hc : (R : ℝ) * (((Ico a (a + L)).filter (fun n => n ∈ S)).card : ℝ) ≤ L := by
      exact_mod_cast hL₀ a L hL
    have hcoeff : 1 / (R : ℝ) ≤ ε := by
      apply (div_le_iff₀ hRp).mpr
      have h := (div_lt_iff₀ hε).mp hRbig
      nlinarith
    calc
      _ ≤ (L : ℝ) / R := (le_div_iff₀ hRp).mpr (by nlinarith [hc])
      _ = (1 / (R : ℝ)) * L := by ring
      _ ≤ ε * L := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)
  · intro h R hR
    have hRp : (0 : ℝ) < R := by exact_mod_cast hR
    obtain ⟨L₀, hL₀⟩ := h (1 / R) (by positivity)
    refine ⟨L₀, ?_⟩
    intro a L hL
    have hc := hL₀ a L hL
    have hc' : (R : ℝ) * (((Ico a (a + L)).filter (fun n => n ∈ S)).card : ℝ) ≤ L := by
      have hmul := mul_le_mul_of_nonneg_left hc hRp.le
      have heq : (R : ℝ) * ((1 / R) * L) = L := by field_simp
      rw [heq] at hmul
      exact hmul
    exact_mod_cast hc'

/-- A rational target really exists inside the common interval. -/
theorem arbitrary_word_sparse_rational_target (a : ℕ → ℕ) {A : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ S : Set ℕ, ∃ e : ℕ → ℕ, ∃ r : ℚ,
      S ⊆ Set.Ici K ∧ UpperBanachZero S ∧ A < (r : ℝ) ∧
      (∀ n, e n ≠ 0 → n ∈ S) ∧
      (∀ n < K, a n + e n = a n) ∧
      (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ f n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
      HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) := by
  obtain ⟨S, l, u, hSK, hSZ, hAl, hlu, hfill⟩ :=
    arbitrary_word_sparse_rationalisation a ha f hf K
  obtain ⟨r, hlr, hru⟩ := exists_rat_btwn hlu
  obtain ⟨e, heS, hef, heq, hes⟩ := hfill r hlr.le hru.le
  refine ⟨S, e, r, hSK, hSZ, hAl.trans hlr, heS, ?_, hef, heq, hes⟩
  intro n hn
  have he : e n = 0 := by
    by_contra hne
    have h := hSK (heS n hne)
    exact (not_le_of_gt hn) h
  simp [he]

/-- The polylogarithmic clause and the actual statistical endpoint, with the
support, interval and implied constant chosen before the target r. -/
theorem polylogarithmic_word_interval (a : ℕ → ℕ) {A ε : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (hε : 0 < ε) (K : ℕ) :
    ∃ start : ℕ, ∃ l u C : ℝ,
      (Set.range (centre (polylog ε) start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre (polylog ε) start)) ∧
      A < l ∧ l < u ∧ 0 < C ∧
      (∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
        ((supportSlice (centre (polylog ε) start) X L).card : ℝ) ≤ C * X / iterlog X) ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre (polylog ε) start)) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
        (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        (∀ n < K, a n + e n = a n) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r ∧
        ∀ m : ℕ → ℕ,
          Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0) →
          Tendsto (fun X => blockTV a (fun n => a n + e n) X (m X)) atTop (𝓝 0) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop,
            ∀ Φ : ℕ → (Fin (m X) → ℕ) → ℝ,
              (∀ N ∈ Ico X (2 * X), |Φ N (fun i => a (N + i.val))| ≤ 1) →
              (∀ N ∈ Ico X (2 * X), |Φ N (fun i => a (N + i.val) + e (N + i.val))| ≤ 1) →
              |testMean a X (m X) Φ - testMean (fun n => a n + e n) X (m X) Φ| < η := by
  have hf := polylog_tendsto_atTop hε
  obtain ⟨start, hK, hready, hSK, hSZ, hbudget⟩ := exists_sparse_budgeted_support (polylog ε) hf K
  obtain ⟨C, hC, hrate⟩ := polylog_extended_rate hε start
  refine ⟨start, A + lowerTail (polylog ε) start 0,
    A + upperTail (polylog ε) start 0, C, hSK, hSZ, ?_, ?_, hC, hrate, ?_⟩
  · linarith [lowerTail_positive (polylog ε) start hready]
  · linarith [generated_interval_nonempty (polylog ε) start hready]
  · intro r hrl hru
    obtain ⟨e, heS, hef, heq, hes⟩ := generated_ambient_filling (polylog ε) hf start hready
      (y := r - A) (by linarith) (by linarith)
    have hchange : ∀ n, a n ≠ a n + e n → n ∈ Set.range (centre (polylog ε) start) := by
      intro n hn
      apply heS n
      intro he
      exact hn (by simp [he])
    refine ⟨e, heS, hef, heq, ?_, ?_, ?_⟩
    · intro n hn
      have he : e n = 0 := by
        by_contra hne
        exact (not_le_of_gt hn) (hSK (heS n hne))
      simp [he]
    · have hsum := ha.add hes
      have hv : A + (r - A) = r := by ring
      rw [hv] at hsum
      convert hsum using 1
      funext n
      rw [Nat.cast_add, add_div]
    · intro m hm
      exact ⟨growing_block_TV a (fun n => a n + e n) hε start hchange m hm,
        growing_block_tests_uniform a (fun n => a n + e n) hε start hchange m hm⟩

/-- Every fixed congruence profile of the cumulative positions is preserved. -/
theorem cumulative_modEq (a e : ℕ → ℕ) (p₀ q n : ℕ)
    (he : q ∣ ∑ i ∈ range n, e i) :
    p₀ + ∑ i ∈ range n, (a i + e i) ≡ p₀ + ∑ i ∈ range n, a i [MOD q] := by
  rw [sum_add_distrib]
  obtain ⟨z, hz⟩ := he
  simp [Nat.ModEq, hz, Nat.add_mod, Nat.mul_mod, Nat.add_assoc]

#print axioms arbitrary_word_sparse_rational_target
#print axioms polylogarithmic_word_interval
end ErdosProblems.Erdos251.PaperR11.SparsePaper
