import ErdosProblems.Erdos269.PaperR8UniformRank

/-!
# Uniform finite-rank error from separated rows

A uniformly bounded matrix with arbitrarily large finite families of rows
separated by `δ` in supremum distance cannot be uniformly approximated by a
finite-separated-rank matrix with error below `δ / 2`. The separation may be
a supremum that no coordinate attains. Neither factor of the approximating
matrix is assumed bounded.

The proof reuses the finite-dimensional packing and bounded-column-space
lemmas from the #269 development. The additional interface isolates the
metric premise from the arithmetic construction of separated rows, so a
different source of separation can use the same obstruction. It states no
bound for mean error, and exact infinite rank alone is not a hypothesis that
supplies uniform separation.
-/

namespace ErdosProblems.Synthesis.UniformRankBarrier

open ErdosProblems.Erdos269.PaperR8
open scoped BigOperators Topology BoundedContinuousFunction ENNReal

/-- Transposing a separated representation swaps its two factor families. -/
theorem finiteSeparatedRank_transpose
    {A : ℕ → ℕ → ℝ} (hA : FiniteSeparatedRank A) :
    FiniteSeparatedRank (fun i j => A j i) := by
  obtain ⟨d, f, g, hrep⟩ := hA
  refine ⟨d, g, f, ?_⟩
  intro i j
  simpa only [mul_comm] using hrep j i

/-- Arbitrarily large finite packs suffice; no single infinite separated
subfamily and no attainment of a coordinate supremum are required. -/
theorem finite_rank_uniform_error_lower_of_row_packs
    (C : ℕ → ℕ → ℝ) (M δ : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |C i j| ≤ M)
    (hsep : ∀ n : ℕ, ∃ I : Fin n → ℕ,
      ∀ a b, a ≠ b → ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, δ - η < |C (I a) j - C (I b) j|)
    (A : ℕ → ℕ → ℝ) (hA : FiniteSeparatedRank A)
    (E : ℝ) (hE : 0 ≤ E)
    (herr : ∀ i j, |C i j - A i j| ≤ E) :
    δ / 2 ≤ E := by
  classical
  by_contra hnot
  have hsmall : E < δ / 2 := lt_of_not_ge hnot
  let η : ℝ := (δ - 2 * E) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hAbound : ∀ i j, |A i j| ≤ M + E := by
    intro i j
    calc
      |A i j| = |C i j - (C i j - A i j)| := by congr 1; ring
      _ ≤ |C i j| + |C i j - A i j| := abs_sub _ _
      _ ≤ M + E := add_le_add (hbound i j) (herr i j)
  obtain ⟨V, hV, v, hv, hvbound⟩ :=
    bounded_column_space (fun i j => A j i) (finiteSeparatedRank_transpose hA)
      (M + E) (add_nonneg hM hE) (fun i j => hAbound j i)
  letI : FiniteDimensional ℝ V := hV
  obtain ⟨n, hn⟩ := finite_packing_bound V (M + E) η hη
  obtain ⟨I, hI⟩ := hsep n
  obtain ⟨a, b, hab, hclose⟩ :=
    hn (fun a => v (I a)) (fun a => hvbound (I a))
  obtain ⟨j, hj⟩ := hI a b hab η hη
  have hpoint : |A (I a) j - A (I b) j| ≤ dist (v (I a)) (v (I b)) := by
    have h := BoundedContinuousFunction.dist_coe_le_dist
      (f := (v (I a) : BoundedColumn)) (g := (v (I b) : BoundedColumn)) j
    simpa only [hv, Real.dist_eq] using h
  -- `hpoint` measures the distance in `BoundedColumn`, `hclose` in the
  -- subtype `V`; the two agree definitionally but not syntactically.
  have hAclose : |A (I a) j - A (I b) j| < η := lt_of_le_of_lt hpoint hclose
  have htriangle :
      |C (I a) j - C (I b) j| ≤
        |C (I a) j - A (I a) j| + |A (I a) j - A (I b) j| +
          |A (I b) j - C (I b) j| := by
    calc
      _ = |(C (I a) j - A (I a) j) + (A (I a) j - A (I b) j) +
          (A (I b) j - C (I b) j)| := by congr 1; ring
      _ ≤ |C (I a) j - A (I a) j + (A (I a) j - A (I b) j)| +
          |A (I b) j - C (I b) j| := abs_add_le _ _
      _ ≤ _ := add_le_add (abs_add_le _ _) (le_refl _)
  have he1 := herr (I a) j
  have he2 : |A (I b) j - C (I b) j| ≤ E := by
    rw [abs_sub_comm]
    exact herr (I b) j
  dsimp [η] at hj hAclose
  linarith

/-- In particular, pairwise separation of all rows supplies the finite packs.
The `η` quantifier allows distinct rows whose supremum distance is `δ` but
whose coordinate distances are all strictly smaller than `δ`. -/
theorem finite_rank_uniform_error_lower_of_row_separation
    (C : ℕ → ℕ → ℝ) (M δ : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |C i j| ≤ M)
    (hsep : ∀ i k : ℕ, i ≠ k → ∀ η : ℝ, 0 < η →
      ∃ j : ℕ, δ - η < |C i j - C k j|)
    (A : ℕ → ℕ → ℝ) (hA : FiniteSeparatedRank A)
    (E : ℝ) (hE : 0 ≤ E)
    (herr : ∀ i j, |C i j - A i j| ≤ E) :
    δ / 2 ≤ E := by
  apply finite_rank_uniform_error_lower_of_row_packs C M δ hM hbound ?_ A hA E hE herr
  intro n
  refine ⟨fun i => i.val, ?_⟩
  intro a b hab η hη
  exact hsep a.val b.val (fun h => hab (Fin.ext h)) η hη

/-- The obstruction for the extended uniform error includes unbounded
approximants, whose error is infinite rather than a real-supremum default. -/
theorem uniformError_lower_of_row_separation
    (C : ℕ → ℕ → ℝ) (M δ : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |C i j| ≤ M)
    (hsep : ∀ i k : ℕ, i ≠ k → ∀ η : ℝ, 0 < η →
      ∃ j : ℕ, δ - η < |C i j - C k j|)
    (A : ℕ → ℕ → ℝ) (hA : FiniteSeparatedRank A) :
    ENNReal.ofReal (δ / 2) ≤ uniformError C A := by
  let E := uniformError C A
  change ENNReal.ofReal (δ / 2) ≤ E
  by_cases htop : E = ⊤
  · rw [htop]
    exact le_top
  have herr : ∀ i j, |C i j - A i j| ≤ E.toReal := by
    intro i j
    have he : ENNReal.ofReal |C i j - A i j| ≤ E :=
      le_iSup_of_le i (le_iSup_of_le j le_rfl)
    have h := ENNReal.toReal_mono htop he
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h
  exact ENNReal.ofReal_le_of_le_toReal
    (finite_rank_uniform_error_lower_of_row_separation C M δ hM hbound hsep
      A hA E.toReal ENNReal.toReal_nonneg herr)

/-- Boundedness and finite rank alone impose no positive error barrier:
the zero matrix is represented exactly and has no separated rows. -/
theorem separation_hypothesis_is_necessary :
    FiniteSeparatedRank (fun _ _ : ℕ => (0 : ℝ)) ∧
      (∀ i j : ℕ, |(fun _ _ : ℕ => (0 : ℝ)) i j| ≤ 1) ∧
      (∀ i j : ℕ, |(fun _ _ : ℕ => (0 : ℝ)) i j - 0| ≤ 0) ∧
      ¬ (∀ i k : ℕ, i ≠ k → ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, 1 - η <
          |(fun _ _ : ℕ => (0 : ℝ)) i j - (fun _ _ : ℕ => (0 : ℝ)) k j|) := by
  refine ⟨⟨0, (fun _ _ => 0), (fun _ _ => 0), by intros; simp⟩,
    (by intros; norm_num), (by intros; norm_num), ?_⟩
  intro hsep
  obtain ⟨j, hj⟩ := hsep 0 1 (by omega) (1 / 2) (by norm_num)
  norm_num at hj

/-- The matrix whose row `i` is constantly `i` has separated rows and rank
one, so it is an exact approximation to itself. Uniform boundedness is the
premise preventing this example in the obstruction theorem. -/
theorem boundedness_hypothesis_is_necessary :
    FiniteSeparatedRank (fun i _ : ℕ => (i : ℝ)) ∧
      (∀ i k : ℕ, i ≠ k → ∀ η : ℝ, 0 < η →
        ∃ j : ℕ, 1 - η <
          |(fun i _ : ℕ => (i : ℝ)) i j - (fun i _ : ℕ => (i : ℝ)) k j|) ∧
      (∀ i j : ℕ, |(fun i _ : ℕ => (i : ℝ)) i j - (i : ℝ)| ≤ 0) ∧
      ¬ (∃ M : ℝ, ∀ i j : ℕ, |(fun i _ : ℕ => (i : ℝ)) i j| ≤ M) := by
  refine ⟨⟨1, (fun _ i => (i : ℝ)), (fun _ _ => 1), by intros; simp⟩,
    ?_, (by intros; simp), ?_⟩
  · intro i k hik η hη
    refine ⟨0, ?_⟩
    change 1 - η < |(i : ℝ) - (k : ℝ)|
    have hgap : (1 : ℝ) ≤ |(i : ℝ) - (k : ℝ)| := by
      rcases lt_or_gt_of_ne hik with hlt | hgt
      · have hstep : (i : ℝ) + 1 ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr hlt)
        rw [abs_of_nonpos (by linarith : (i : ℝ) - k ≤ 0)]
        linarith
      · have hstep : (k : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_iff.mpr hgt)
        rw [abs_of_nonneg (by linarith : 0 ≤ (i : ℝ) - k)]
        linarith
    linarith
  · rintro ⟨M, hM⟩
    obtain ⟨i, hi⟩ := exists_nat_gt M
    have h := hM i 0
    change |(i : ℝ)| ≤ M at h
    rw [abs_of_nonneg (Nat.cast_nonneg i)] at h
    linarith

#print axioms finite_rank_uniform_error_lower_of_row_packs
#print axioms finite_rank_uniform_error_lower_of_row_separation
#print axioms uniformError_lower_of_row_separation
#print axioms separation_hypothesis_is_necessary
#print axioms boundedness_hypothesis_is_necessary

end ErdosProblems.Synthesis.UniformRankBarrier
