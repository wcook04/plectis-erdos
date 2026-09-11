import ErdosProblems.Erdos1049.AdelicHeightBridge

/-!
# Erdős #1049: the exact leading coefficient of Zudilin's normalized Hankel determinant

Zudilin (Res. Number Theory 2 (2016), Art. 15, §4) proves the *lower* bound
`ord_q V_N^* ≥ B_N = ∑_{j<N} j²` for the normalized Hankel determinant
`V_N^* = det (v_{i+j}^*)_{0 ≤ i,j < N}`.  Equality, and the exact leading
coefficient `C_N = ∏_{j<N} (j+1)²(j+2)/2 = (N!)² (N+1)! / 2^N`, are *not* in the
source; they are the new content, of which this module formalizes the
determinant-level half.

`AdelicHeightBridge.lean` already carries the order half of the bridge
(`order_det_eq_of_unique_minimizing_permutation`) together with the
associated-graded leading matrix, its Vandermonde determinant and its exact
order `∑_{j<N} j²`.  What was missing there, and is supplied here, is:

* `coeff_prod_eq_zero_of_lt_sum` / `coeff_prod_sum_eq_prod_coeff`: the
  filtered-product coefficient calculus — a finite product of power series has
  no coefficient below the sum of the entrywise thresholds, and at that degree
  its coefficient is the product of the entrywise threshold coefficients;
* `coeff_det_eq_of_unique_minimizing_permutation`: the *coefficient* analogue
  of the landed order principle, i.e. the Leibniz bridge which reads the first
  determinant coefficient off the entrywise initial monomials as soon as one
  permutation minimizes the entry-order weight strictly;
* `sum_zudilinLeadingEntryOrder_lt_of_ne_revPerm`: the reversing permutation is
  the *unique* minimizer of the Hankel entry-order weight
  `e (j, l) = j(j+1)/2 + j·l`, proved through the exact square identity
  `∑_i (σ i + i - (N-1))² = 2 ∑_i (σ i)·i - 2 ∑_i (rev i)·i`
  rather than through a rearrangement inequality;
* `sign_finRevPerm`: the sign of the reversal on `Fin N` is `(-1)^(N choose 2)`,
  obtained by comparing the two evaluations of one and the same leading
  determinant;
* `coeff_det_zudilinAssociatedLeadingMatrix`: the exact leading coefficient
  `∏_{j<N} (j+1)²(j+2)/2` of the associated-graded determinant, sharpening the
  landed nonvanishing statement to an exact value;
* `ZudilinRowInitialMonomial` and
  `zudilinSharpHankelOrderAndCoeff_of_rowInitialMonomial`: the exact remaining
  source-row hypothesis, and the kernel-checked deduction of the sharp order
  *and* the sharp leading coefficient of `V_N^*` from it.

The row hypothesis is discharged here for rows `j = 0`, `j = 1` and `j = 2`
(`zudilinRowInitialMonomial_of_le_two`); rows `j ≥ 3` remain open, so
`zudilinSharpHankelOrderAndCoeff_of_rowInitialMonomial` is deliberately
conditional and no unconditional determinant claim is made.  The row `j = 2`
initial monomial `18·q^(2l+3)` is new relative to `AdelicHeightBridge.lean`,
which stopped at row `j = 1`.

No theorem here decides the arithmetic nature of the Lambert value at `3 / 2`.
-/

namespace ErdosProblems.Erdos1049

/-! ## Coefficients of finite products of power series

The filtered calculus behind every initial-monomial argument below: if each
factor vanishes below its own threshold, the product vanishes below the sum of
the thresholds, and at that sum its coefficient is the product of the factorwise
threshold coefficients.
-/

/-- A finite product of power series has no coefficient strictly below the sum
of the entrywise vanishing thresholds. -/
theorem coeff_prod_eq_zero_of_lt_sum {ι : Type*} [DecidableEq ι]
    (f : ι → PowerSeries ℤ) (e : ι → ℕ) :
    ∀ s : Finset ι,
      (∀ i ∈ s, ∀ d, d < e i → PowerSeries.coeff d (f i) = 0) →
        ∀ d, d < ∑ i ∈ s, e i →
          PowerSeries.coeff d (∏ i ∈ s, f i) = 0 := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ d hd
      simp at hd
  | @insert a t ha ih =>
      intro hzero d hd
      rw [Finset.sum_insert ha] at hd
      rw [Finset.prod_insert ha, PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨p, q⟩ hp
      have hsum : p + q = d := Finset.mem_antidiagonal.mp hp
      by_cases h1 : p < e a
      · rw [hzero a (Finset.mem_insert_self a t) p h1, zero_mul]
      · have h2 : q < ∑ i ∈ t, e i := by omega
        rw [ih (fun i hi => hzero i (Finset.mem_insert_of_mem hi)) q h2, mul_zero]

/-- At the sum of the entrywise thresholds, the coefficient of a finite product
of power series is the product of the entrywise threshold coefficients. -/
theorem coeff_prod_sum_eq_prod_coeff {ι : Type*} [DecidableEq ι]
    (f : ι → PowerSeries ℤ) (e : ι → ℕ) :
    ∀ s : Finset ι,
      (∀ i ∈ s, ∀ d, d < e i → PowerSeries.coeff d (f i) = 0) →
        PowerSeries.coeff (∑ i ∈ s, e i) (∏ i ∈ s, f i) =
          ∏ i ∈ s, PowerSeries.coeff (e i) (f i) := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      intro hzero
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
        PowerSeries.coeff_mul,
        Finset.sum_eq_single_of_mem (e a, ∑ i ∈ t, e i)
          (Finset.mem_antidiagonal.mpr rfl)]
      · rw [ih (fun i hi => hzero i (Finset.mem_insert_of_mem hi))]
      · rintro ⟨p, q⟩ hp hne
        have hsum : p + q = e a + ∑ i ∈ t, e i := Finset.mem_antidiagonal.mp hp
        by_cases h1 : p < e a
        · rw [hzero a (Finset.mem_insert_self a t) p h1, zero_mul]
        · have h2 : q < ∑ i ∈ t, e i := by
            rcases Nat.lt_or_ge q (∑ i ∈ t, e i) with hq | hq
            · exact hq
            · exfalso
              refine hne ?_
              rw [Prod.mk.injEq]
              exact ⟨by omega, by omega⟩
          rw [coeff_prod_eq_zero_of_lt_sum f e t
            (fun i hi => hzero i (Finset.mem_insert_of_mem hi)) q h2, mul_zero]

/-- Two-factor form of the filtered product calculus.  Used repeatedly below to
peel a known initial monomial off a source tail. -/
theorem coeff_mul_first {φ ψ : PowerSeries ℤ} {m₁ m₂ : ℕ}
    (h₁ : ∀ d, d < m₁ → PowerSeries.coeff d φ = 0)
    (h₂ : ∀ d, d < m₂ → PowerSeries.coeff d ψ = 0) :
    (∀ d, d < m₁ + m₂ → PowerSeries.coeff d (φ * ψ) = 0) ∧
      PowerSeries.coeff (m₁ + m₂) (φ * ψ) =
        PowerSeries.coeff m₁ φ * PowerSeries.coeff m₂ ψ := by
  constructor
  · intro d hd
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨p, q⟩ hp
    have hsum : p + q = d := Finset.mem_antidiagonal.mp hp
    by_cases hpm : p < m₁
    · rw [h₁ p hpm, zero_mul]
    · rw [h₂ q (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul,
      Finset.sum_eq_single_of_mem (m₁, m₂) (Finset.mem_antidiagonal.mpr rfl)]
    rintro ⟨p, q⟩ hp hne
    have hsum : p + q = m₁ + m₂ := Finset.mem_antidiagonal.mp hp
    by_cases hpm : p < m₁
    · rw [h₁ p hpm, zero_mul]
    · have hq : q < m₂ := by
        rcases Nat.lt_or_ge q m₂ with hq | hq
        · exact hq
        · exfalso
          refine hne ?_
          rw [Prod.mk.injEq]
          exact ⟨by omega, by omega⟩
      rw [h₂ q hq, mul_zero]

/-! ## The coefficient analogue of the unique-minimum Leibniz bridge -/

/-- **Unique-minimum Leibniz coefficient bridge.**  If every entry of `M`
vanishes below its own threshold `e i j` and has coefficient `a i j` there, and
if one permutation `σ₀` minimizes the entry-order weight `∑ i, e (σ i) i`
strictly, then the first determinant coefficient is exactly the signed product
of the entrywise threshold coefficients.

This is the coefficient companion of
`order_det_eq_of_unique_minimizing_permutation`, and unlike that theorem it
needs no nonvanishing hypothesis on the `a i j`. -/
theorem coeff_det_eq_of_unique_minimizing_permutation {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (PowerSeries ℤ))
    (e : Fin N → Fin N → ℕ) (a : Fin N → Fin N → ℤ)
    (σ₀ : Equiv.Perm (Fin N)) (B : ℕ)
    (hzero : ∀ i j d, d < e i j → PowerSeries.coeff d (M i j) = 0)
    (hlead : ∀ i j, PowerSeries.coeff (e i j) (M i j) = a i j)
    (hmain : ∑ i, e (σ₀ i) i = B)
    (hother : ∀ σ : Equiv.Perm (Fin N), σ ≠ σ₀ → B < ∑ i, e (σ i) i) :
    PowerSeries.coeff B M.det =
      (Equiv.Perm.sign σ₀ : ℤ) * ∏ i, a (σ₀ i) i := by
  rw [det_eq_sum_zudilinDetTerm, map_sum,
    Finset.sum_eq_single_of_mem σ₀ (Finset.mem_univ σ₀)]
  · rw [zudilinDetTerm, PowerSeries.coeff_C_mul, ← hmain,
      coeff_prod_sum_eq_prod_coeff (fun i => M (σ₀ i) i)
        (fun i => e (σ₀ i) i) Finset.univ
        (fun i _ d hd => hzero (σ₀ i) i d hd)]
    exact congrArg _ (Finset.prod_congr rfl fun i _ => hlead (σ₀ i) i)
  · intro σ _ hne
    rw [zudilinDetTerm, PowerSeries.coeff_C_mul,
      coeff_prod_eq_zero_of_lt_sum (fun i => M (σ i) i) (fun i => e (σ i) i)
        Finset.univ (fun i _ d hd => hzero (σ i) i d hd) B (hother σ hne),
      mul_zero]

/-! ## The reversing permutation is the unique minimizer

The entry-order weight of the associated-graded Hankel matrix is
`e (j, l) = j(j+1)/2 + j·l`.  Its triangular part is permutation invariant, so
only `∑_i (σ i)·i` matters, and the exact square identity below identifies the
deviation from the reversal with a sum of squares.
-/

/-- The exact `X`-order of the associated-graded entry in row `j`, column `l`. -/
def zudilinLeadingEntryOrder {N : ℕ} (j l : Fin N) : ℕ :=
  (j : ℕ) * ((j : ℕ) + 1) / 2 + (j : ℕ) * (l : ℕ)

/-- The reversal is characterized pointwise by `rev i + i = N - 1`. -/
theorem val_revPerm_add_val {N : ℕ} (i : Fin N) :
    ((((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) : ℤ) + ((i : ℕ) : ℤ) =
      (N : ℤ) - 1 := by
  have hlt : (i : ℕ) + 1 ≤ N := i.isLt
  rw [Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub hlt]
  push_cast
  ring

/-- **The exact square identity.**  The entry-order excess of an arbitrary
permutation over the reversal is exactly a sum of squares.  This replaces the
usual transposition or rearrangement argument by a single algebraic identity. -/
theorem sum_sq_shift_eq_two_mul_sub {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (∑ i : Fin N, (((σ i : ℕ) : ℤ) + ((i : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2) =
      2 * (∑ i : Fin N, ((σ i : ℕ) : ℤ) * ((i : ℕ) : ℤ)) -
        2 * ∑ i : Fin N,
          ((((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) : ℤ) *
            ((i : ℕ) : ℤ) := by
  have key : ∀ τ : Equiv.Perm (Fin N),
      (∑ i : Fin N, (((τ i : ℕ) : ℤ) + ((i : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2) =
        2 * (∑ i : Fin N, ((τ i : ℕ) : ℤ) * ((i : ℕ) : ℤ)) +
          ((∑ i : Fin N, ((i : ℕ) : ℤ) ^ 2) -
              2 * ((N : ℤ) - 1) * (∑ i : Fin N, ((i : ℕ) : ℤ)) +
            ∑ i : Fin N, (((i : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2) := by
    intro τ
    have h1 : (∑ i : Fin N, ((τ i : ℕ) : ℤ) ^ 2) =
        ∑ i : Fin N, ((i : ℕ) : ℤ) ^ 2 :=
      Equiv.sum_comp τ fun j : Fin N => ((j : ℕ) : ℤ) ^ 2
    have h2 : (∑ i : Fin N, ((τ i : ℕ) : ℤ)) = ∑ i : Fin N, ((i : ℕ) : ℤ) :=
      Equiv.sum_comp τ fun j : Fin N => ((j : ℕ) : ℤ)
    calc
      (∑ i : Fin N, (((τ i : ℕ) : ℤ) + ((i : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2) =
          ∑ i : Fin N,
            (((τ i : ℕ) : ℤ) ^ 2 + 2 * (((τ i : ℕ) : ℤ) * ((i : ℕ) : ℤ)) -
              2 * ((N : ℤ) - 1) * ((τ i : ℕ) : ℤ) +
              (((i : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 2 * (∑ i : Fin N, ((τ i : ℕ) : ℤ) * ((i : ℕ) : ℤ)) +
            ((∑ i : Fin N, ((i : ℕ) : ℤ) ^ 2) -
                2 * ((N : ℤ) - 1) * (∑ i : Fin N, ((i : ℕ) : ℤ)) +
              ∑ i : Fin N, (((i : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2]
            ring
  have hrevsum :
      (∑ i : Fin N,
        (((((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) : ℤ) +
          ((i : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [val_revPerm_add_val i]
    ring
  have hσ := key σ
  have hr := key (Fin.revPerm : Equiv.Perm (Fin N))
  rw [hrevsum] at hr
  linarith

/-- **Strict uniqueness of the reversal.**  Every other permutation has strictly
larger column-index weight `∑_i (σ i)·i`. -/
theorem sum_val_mul_val_lt_of_ne_revPerm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : σ ≠ Fin.revPerm) :
    (∑ i : Fin N, (((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) * (i : ℕ)) <
      ∑ i : Fin N, ((σ i : ℕ)) * (i : ℕ) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin N, σ i ≠ (Fin.revPerm : Equiv.Perm (Fin N)) i := by
    by_contra hcon
    exact hσ (Equiv.ext (fun i => not_not.mp (fun h => hcon ⟨i, h⟩)))
  have hstrict : (0 : ℤ) <
      (((σ i₀ : ℕ) : ℤ) + ((i₀ : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2 := by
    rcases lt_or_eq_of_le (sq_nonneg
      (((σ i₀ : ℕ) : ℤ) + ((i₀ : ℕ) : ℤ) - ((N : ℤ) - 1))) with h | h
    · exact h
    · exfalso
      refine hi₀ ?_
      have hz : ((σ i₀ : ℕ) : ℤ) + ((i₀ : ℕ) : ℤ) - ((N : ℤ) - 1) = 0 :=
        sq_eq_zero_iff.mp h.symm
      have hrev := val_revPerm_add_val i₀
      have hval : ((σ i₀ : ℕ) : ℤ) =
          ((((Fin.revPerm : Equiv.Perm (Fin N)) i₀ : Fin N) : ℕ) : ℤ) := by
        linarith
      exact Fin.ext (by exact_mod_cast hval)
  have hpos : (0 : ℤ) <
      ∑ i : Fin N, (((σ i : ℕ) : ℤ) + ((i : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2 := by
    have hlt := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin N)))
      (f := fun _ : Fin N => (0 : ℤ))
      (g := fun i : Fin N =>
        (((σ i : ℕ) : ℤ) + ((i : ℕ) : ℤ) - ((N : ℤ) - 1)) ^ 2)
      (fun i _ => sq_nonneg _) ⟨i₀, Finset.mem_univ _, hstrict⟩
    simpa using hlt
  rw [sum_sq_shift_eq_two_mul_sub σ] at hpos
  have hcast :
      ((∑ i : Fin N,
          (((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) * (i : ℕ) : ℕ) : ℤ) <
        ((∑ i : Fin N, ((σ i : ℕ)) * (i : ℕ) : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast hcast

/-- The reversal's Hankel entry-order weight is exactly `∑_{j<N} j²`, i.e.
Zudilin's exponent `B_N`. -/
theorem sum_zudilinLeadingEntryOrder_revPerm (N : ℕ) :
    (∑ i : Fin N,
        zudilinLeadingEntryOrder ((Fin.revPerm : Equiv.Perm (Fin N)) i) i) =
      ∑ j ∈ Finset.range N, j ^ 2 := by
  have hsplit :
      (∑ i : Fin N,
          zudilinLeadingEntryOrder ((Fin.revPerm : Equiv.Perm (Fin N)) i) i) =
        (∑ i : Fin N,
            (((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) *
              ((((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) + 1) / 2) +
          ∑ i : Fin N,
            (((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) * (i : ℕ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have htri :
      (∑ i : Fin N,
          (((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) *
            ((((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) + 1) / 2) =
        ∑ j ∈ Finset.range N, j * (j + 1) / 2 := by
    rw [Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N))
      fun j : Fin N => (j : ℕ) * ((j : ℕ) + 1) / 2]
    exact Fin.sum_univ_eq_sum_range (fun j => j * (j + 1) / 2) N
  have hvan :
      (∑ i : Fin N,
          (((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) * (i : ℕ)) =
        ∑ i ∈ Finset.range N, i * (N - 1 - i) := by
    have hpt : ∀ i : Fin N,
        (((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N) : ℕ) * (i : ℕ) =
          (i : ℕ) * (N - 1 - (i : ℕ)) := by
      intro i
      have hlt : (i : ℕ) < N := i.isLt
      rw [Fin.revPerm_apply, Fin.val_rev,
        show N - ((i : ℕ) + 1) = N - 1 - (i : ℕ) by omega, Nat.mul_comm]
    rw [Finset.sum_congr rfl fun i _ => hpt i]
    exact Fin.sum_univ_eq_sum_range (fun i => i * (N - 1 - i)) N
  rw [hsplit, htri, hvan, ← zudilinAssociatedLeadingOrderNat,
    zudilinAssociatedLeadingOrderNat_eq_sum_sq]

/-- **The reversal is the unique minimizer of the Hankel entry-order weight.**
Every other permutation strictly exceeds Zudilin's exponent `B_N`, so no
cancellation can occur at degree `B_N`. -/
theorem sum_zudilinLeadingEntryOrder_lt_of_ne_revPerm {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (hσ : σ ≠ Fin.revPerm) :
    (∑ j ∈ Finset.range N, j ^ 2) <
      ∑ i : Fin N, zudilinLeadingEntryOrder (σ i) i := by
  have hsplit : ∀ τ : Equiv.Perm (Fin N),
      (∑ i : Fin N, zudilinLeadingEntryOrder (τ i) i) =
        (∑ j ∈ Finset.range N, j * (j + 1) / 2) +
          ∑ i : Fin N, ((τ i : ℕ)) * (i : ℕ) := by
    intro τ
    have h1 : (∑ i : Fin N, zudilinLeadingEntryOrder (τ i) i) =
        (∑ i : Fin N, ((τ i : ℕ)) * (((τ i : ℕ)) + 1) / 2) +
          ∑ i : Fin N, ((τ i : ℕ)) * (i : ℕ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    rw [h1, Equiv.sum_comp τ fun j : Fin N => (j : ℕ) * ((j : ℕ) + 1) / 2,
      Fin.sum_univ_eq_sum_range (fun j => j * (j + 1) / 2) N]
  rw [← sum_zudilinLeadingEntryOrder_revPerm N, hsplit σ,
    hsplit (Fin.revPerm : Equiv.Perm (Fin N))]
  exact Nat.add_lt_add_left (sum_val_mul_val_lt_of_ne_revPerm σ hσ) _

/-! ## The exact leading coefficient of the associated-graded determinant -/

/-- Every entry of the associated-graded leading matrix is a signed monomial. -/
theorem zudilinAssociatedLeadingMatrix_apply (N : ℕ) (j l : Fin N) :
    zudilinAssociatedLeadingMatrix N j l =
      PowerSeries.C
          (((-1 : ℤ) ^ (j : ℕ)) * (zudilinTransformedRowCoeff (j : ℕ) : ℤ)) *
        PowerSeries.X ^ zudilinLeadingEntryOrder j l := by
  simp only [zudilinAssociatedLeadingMatrix, zudilinAssociatedLeadingRowScale,
    zudilinLeadingEntryOrder]
  rw [← pow_mul, mul_assoc, ← pow_add]

theorem coeff_zudilinAssociatedLeadingMatrix_eq_zero_of_lt (N : ℕ) (j l : Fin N)
    (d : ℕ) (hd : d < zudilinLeadingEntryOrder j l) :
    PowerSeries.coeff d (zudilinAssociatedLeadingMatrix N j l) = 0 := by
  have hne' : ¬ d = zudilinLeadingEntryOrder j l := by omega
  rw [zudilinAssociatedLeadingMatrix_apply, PowerSeries.coeff_C_mul]
  simp [PowerSeries.coeff_X_pow, hne']

theorem coeff_zudilinAssociatedLeadingMatrix_first (N : ℕ) (j l : Fin N) :
    PowerSeries.coeff (zudilinLeadingEntryOrder j l)
        (zudilinAssociatedLeadingMatrix N j l) =
      ((-1 : ℤ) ^ (j : ℕ)) * (zudilinTransformedRowCoeff (j : ℕ) : ℤ) := by
  rw [zudilinAssociatedLeadingMatrix_apply, PowerSeries.coeff_C_mul]
  simp

private theorem coeff_X_pow_sub_X_pow_eq_zero_of_lt {a b d : ℕ} (hab : a < b)
    (hd : d < a) :
    PowerSeries.coeff d
        ((PowerSeries.X : PowerSeries ℤ) ^ b - PowerSeries.X ^ a) = 0 := by
  have h3 : ¬ d = b := by omega
  have h4 : ¬ d = a := by omega
  simp [PowerSeries.coeff_X_pow, h3, h4]

private theorem coeff_X_pow_sub_X_pow_first {a b : ℕ} (hab : a < b) :
    PowerSeries.coeff a
        ((PowerSeries.X : PowerSeries ℤ) ^ b - PowerSeries.X ^ a) = -1 := by
  have h2 : ¬ a = b := by omega
  simp [PowerSeries.coeff_X_pow, h2]

private theorem coeff_vandermondeRow_eq_zero_of_lt {N : ℕ} (i : Fin N)
    (d : ℕ) (hd : d < ∑ _j ∈ Finset.Ioi i, (i : ℕ)) :
    PowerSeries.coeff d
        (∏ j ∈ Finset.Ioi i,
          ((PowerSeries.X : PowerSeries ℤ) ^ (j : ℕ) -
            PowerSeries.X ^ (i : ℕ))) = 0 :=
  coeff_prod_eq_zero_of_lt_sum
    (fun j : Fin N =>
      (PowerSeries.X : PowerSeries ℤ) ^ (j : ℕ) - PowerSeries.X ^ (i : ℕ))
    (fun _ => (i : ℕ)) (Finset.Ioi i)
    (fun j hj d' hd' =>
      coeff_X_pow_sub_X_pow_eq_zero_of_lt
        (by exact_mod_cast Finset.mem_Ioi.mp hj) hd') d hd

private theorem coeff_vandermondeRow_first {N : ℕ} (i : Fin N) :
    PowerSeries.coeff (∑ _j ∈ Finset.Ioi i, (i : ℕ))
        (∏ j ∈ Finset.Ioi i,
          ((PowerSeries.X : PowerSeries ℤ) ^ (j : ℕ) -
            PowerSeries.X ^ (i : ℕ))) =
      (-1 : ℤ) ^ (Finset.Ioi i).card := by
  have hfac : ∀ j ∈ Finset.Ioi i,
      PowerSeries.coeff (i : ℕ)
          ((PowerSeries.X : PowerSeries ℤ) ^ (j : ℕ) -
            PowerSeries.X ^ (i : ℕ)) = (-1 : ℤ) := by
    intro j hj
    exact coeff_X_pow_sub_X_pow_first
      (by exact_mod_cast Finset.mem_Ioi.mp hj : (i : ℕ) < (j : ℕ))
  rw [coeff_prod_sum_eq_prod_coeff
    (fun j : Fin N =>
      (PowerSeries.X : PowerSeries ℤ) ^ (j : ℕ) - PowerSeries.X ^ (i : ℕ))
    (fun _ => (i : ℕ)) (Finset.Ioi i)
    (fun j hj d' hd' =>
      coeff_X_pow_sub_X_pow_eq_zero_of_lt
        (by exact_mod_cast Finset.mem_Ioi.mp hj) hd'),
    Finset.prod_congr rfl hfac, Finset.prod_const]

private theorem coeff_vandermondeProd_eq_zero_of_lt (N : ℕ)
    (d : ℕ) (hd : d < ∑ i : Fin N, ∑ _j ∈ Finset.Ioi i, (i : ℕ)) :
    PowerSeries.coeff d
        (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          ((PowerSeries.X : PowerSeries ℤ) ^ (j : ℕ) -
            PowerSeries.X ^ (i : ℕ))) = 0 :=
  coeff_prod_eq_zero_of_lt_sum _ _ Finset.univ
    (fun i _ d' hd' => coeff_vandermondeRow_eq_zero_of_lt i d' hd') d hd

private theorem coeff_vandermondeProd_first (N : ℕ) :
    PowerSeries.coeff (∑ i : Fin N, ∑ _j ∈ Finset.Ioi i, (i : ℕ))
        (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          ((PowerSeries.X : PowerSeries ℤ) ^ (j : ℕ) -
            PowerSeries.X ^ (i : ℕ))) =
      (-1 : ℤ) ^ (∑ i : Fin N, (Finset.Ioi i).card) := by
  rw [coeff_prod_sum_eq_prod_coeff _ _ Finset.univ
      (fun i _ d' hd' => coeff_vandermondeRow_eq_zero_of_lt i d' hd'),
    Finset.prod_congr rfl fun i _ => coeff_vandermondeRow_first i,
    Finset.prod_pow_eq_pow_sum]

private theorem prod_zudilinAssociatedLeadingRowScale (N : ℕ) :
    (∏ j : Fin N, zudilinAssociatedLeadingRowScale j) =
      PowerSeries.C
          (∏ j : Fin N,
            ((-1 : ℤ) ^ (j : ℕ) * (zudilinTransformedRowCoeff (j : ℕ) : ℤ))) *
        PowerSeries.X ^ (∑ j : Fin N, (j : ℕ) * ((j : ℕ) + 1) / 2) := by
  simp only [zudilinAssociatedLeadingRowScale]
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]

private theorem sum_card_Ioi_eq_sum_val (N : ℕ) :
    (∑ i : Fin N, (Finset.Ioi i).card) = ∑ j : Fin N, (j : ℕ) := by
  have h1 : (∑ i : Fin N, (Finset.Ioi i).card) =
      ∑ i ∈ Finset.range N, (N - 1 - i) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      Fin.card_Ioi i]
    exact Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N
  have h2 : (∑ j : Fin N, (j : ℕ)) = ∑ j ∈ Finset.range N, j :=
    Fin.sum_univ_eq_sum_range (fun j => j) N
  rw [h1, h2]
  exact Finset.sum_range_reflect (fun j => j) N

private theorem sum_vandermondeExponent (N : ℕ) :
    (∑ j : Fin N, (j : ℕ) * ((j : ℕ) + 1) / 2) +
        (∑ i : Fin N, ∑ _j ∈ Finset.Ioi i, (i : ℕ)) =
      ∑ j ∈ Finset.range N, j ^ 2 := by
  have h1 : (∑ j : Fin N, (j : ℕ) * ((j : ℕ) + 1) / 2) =
      ∑ j ∈ Finset.range N, j * (j + 1) / 2 :=
    Fin.sum_univ_eq_sum_range (fun j => j * (j + 1) / 2) N
  have h2 : (∑ i : Fin N, ∑ _j ∈ Finset.Ioi i, (i : ℕ)) =
      ∑ i ∈ Finset.range N, i * (N - 1 - i) := by
    have hpt : ∀ i : Fin N, (∑ _j ∈ Finset.Ioi i, (i : ℕ)) =
        (i : ℕ) * (N - 1 - (i : ℕ)) := by
      intro i
      rw [Finset.sum_const, smul_eq_mul, Fin.card_Ioi, Nat.mul_comm]
    rw [Finset.sum_congr rfl fun i _ => hpt i]
    exact Fin.sum_univ_eq_sum_range (fun i => i * (N - 1 - i)) N
  rw [h1, h2, ← zudilinAssociatedLeadingOrderNat,
    zudilinAssociatedLeadingOrderNat_eq_sum_sq]

/-- **Exact leading coefficient of the associated-graded determinant.**  This
sharpens the landed nonvanishing statement `det_zudilinAssociatedLeadingMatrix_ne_zero`
to the exact value `∏_{j<N} (j+1)²(j+2)/2 = (N!)²(N+1)!/2^N`, by reading the
Vandermonde product coefficientwise.  The two sign contributions
`∏_j (-1)^j` and `∏_{i<j} (-1)` cancel. -/
theorem coeff_det_zudilinAssociatedLeadingMatrix (N : ℕ) :
    PowerSeries.coeff (∑ j ∈ Finset.range N, j ^ 2)
        (zudilinAssociatedLeadingMatrix N).det =
      ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) := by
  classical
  set T : ℕ := ∑ j : Fin N, (j : ℕ) * ((j : ℕ) + 1) / 2 with hT
  set W : ℕ := ∑ i : Fin N, ∑ _j ∈ Finset.Ioi i, (i : ℕ) with hW
  set A : ℤ :=
    ∏ j : Fin N, ((-1 : ℤ) ^ (j : ℕ) * (zudilinTransformedRowCoeff (j : ℕ) : ℤ))
    with hA
  set V : PowerSeries ℤ :=
    ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      ((PowerSeries.X : PowerSeries ℤ) ^ (j : ℕ) - PowerSeries.X ^ (i : ℕ))
    with hV
  have hdet : (zudilinAssociatedLeadingMatrix N).det =
      PowerSeries.C A * (PowerSeries.X ^ T * V) := by
    rw [det_zudilinAssociatedLeadingMatrix, prod_zudilinAssociatedLeadingRowScale,
      mul_assoc]
  have hdeg : (∑ j ∈ Finset.range N, j ^ 2) = W + T := by
    rw [← sum_vandermondeExponent N, Nat.add_comm]
  rw [hdeg, hdet, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul,
    hV, coeff_vandermondeProd_first N, sum_card_Ioi_eq_sum_val N]
  have hAeq : A =
      (-1 : ℤ) ^ (∑ j : Fin N, (j : ℕ)) *
        ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) := by
    rw [hA, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    congr 1
    exact Fin.prod_univ_eq_prod_range
      (fun j => (zudilinTransformedRowCoeff j : ℤ)) N
  rw [hAeq, mul_assoc, mul_comm (∏ j ∈ Finset.range N,
      (zudilinTransformedRowCoeff j : ℤ)), ← mul_assoc, ← pow_add]
  have hsq : ((-1 : ℤ) ^ (∑ j : Fin N, (j : ℕ) + ∑ j : Fin N, (j : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [hsq, one_mul]

/-! ## The sign of the reversal

Comparing the Vandermonde evaluation of `det L_N` with its Leibniz evaluation at
the unique minimizing permutation determines `sgn` of the reversal, and shows
that this sign exactly cancels the product of the row signs `(-1)^j`.
-/

private theorem coeff_det_zudilinAssociatedLeadingMatrix_leibniz (N : ℕ) :
    PowerSeries.coeff (∑ j ∈ Finset.range N, j ^ 2)
        (zudilinAssociatedLeadingMatrix N).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤˣ) : ℤ) *
        ∏ i : Fin N,
          ((-1 : ℤ) ^ ((((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N)) : ℕ) *
            (zudilinTransformedRowCoeff
              ((((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N)) : ℕ) : ℤ)) :=
  coeff_det_eq_of_unique_minimizing_permutation
    (zudilinAssociatedLeadingMatrix N) zudilinLeadingEntryOrder
    (fun j _ => (-1 : ℤ) ^ (j : ℕ) * (zudilinTransformedRowCoeff (j : ℕ) : ℤ))
    (Fin.revPerm : Equiv.Perm (Fin N)) (∑ j ∈ Finset.range N, j ^ 2)
    (fun i j d hd =>
      coeff_zudilinAssociatedLeadingMatrix_eq_zero_of_lt N i j d hd)
    (fun i j => coeff_zudilinAssociatedLeadingMatrix_first N i j)
    (sum_zudilinLeadingEntryOrder_revPerm N)
    (fun σ hσ => sum_zudilinLeadingEntryOrder_lt_of_ne_revPerm σ hσ)

/-- **The reversal's sign cancels the row signs.**  Equating the two evaluations
of the same leading determinant coefficient leaves precisely the positive
product of row coefficients. -/
theorem signedRowProduct_revPerm (N : ℕ) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤˣ) : ℤ) *
        ∏ i : Fin N,
          ((-1 : ℤ) ^ ((((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N)) : ℕ) *
            (zudilinTransformedRowCoeff
              ((((Fin.revPerm : Equiv.Perm (Fin N)) i : Fin N)) : ℕ) : ℤ)) =
      ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) :=
  (coeff_det_zudilinAssociatedLeadingMatrix_leibniz N).symm.trans
    (coeff_det_zudilinAssociatedLeadingMatrix N)

theorem sum_range_id_eq_choose_two (N : ℕ) :
    (∑ j ∈ Finset.range N, j) = N.choose 2 := by
  have h := Finset.sum_range_id_mul_two N
  have h2 : N.choose 2 = N * (N - 1) / 2 := Nat.choose_two_right N
  omega

/-- The row signs assemble to `(-1)^(N choose 2)`. -/
theorem prod_neg_one_pow_range (N : ℕ) :
    (∏ j ∈ Finset.range N, (-1 : ℤ) ^ j) = (-1 : ℤ) ^ (N.choose 2) := by
  rw [Finset.prod_pow_eq_pow_sum, sum_range_id_eq_choose_two]

/-- **Sign of the reversing permutation on `Fin N`.**  Reading one and the same
leading determinant coefficient through the Vandermonde product and through the
Leibniz expansion at the unique minimizing permutation forces
`sgn(rev) = (-1)^(N choose 2)`, which is exactly the sign that cancels the row
signs `∏_j (-1)^j`. -/
theorem sign_finRevPerm (N : ℕ) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤˣ) : ℤ) =
      (-1 : ℤ) ^ (N.choose 2) := by
  have hprodval :
      (∏ j : Fin N, (zudilinTransformedRowCoeff (j : ℕ) : ℤ)) =
        ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) :=
    Fin.prod_univ_eq_prod_range
      (fun j => (zudilinTransformedRowCoeff j : ℤ)) N
  have hsum : (∑ j : Fin N, (j : ℕ)) = N.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => j) N, sum_range_id_eq_choose_two]
  have hkey := signedRowProduct_revPerm N
  rw [Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin N))
      fun j : Fin N =>
        (-1 : ℤ) ^ (j : ℕ) * (zudilinTransformedRowCoeff (j : ℕ) : ℤ),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hprodval,
    hsum] at hkey
  have hpos : (0 : ℤ) <
      ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) := by
    apply Finset.prod_pos
    intro j _
    exact_mod_cast zudilinTransformedRowCoeff_pos j
  have hne : (∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ)) ≠ 0 :=
    ne_of_gt hpos
  have hmul :
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤˣ) : ℤ) *
          (-1 : ℤ) ^ (N.choose 2)) *
          (∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ)) =
        1 * ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) := by
    rw [one_mul, mul_assoc]
    exact hkey
  have hcancel := mul_right_cancel₀ hne hmul
  have hsqinv : ((-1 : ℤ) ^ (N.choose 2)) * ((-1 : ℤ) ^ (N.choose 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤˣ) : ℤ)
      = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤˣ) : ℤ) *
          (((-1 : ℤ) ^ (N.choose 2)) * ((-1 : ℤ) ^ (N.choose 2))) := by
        rw [hsqinv, mul_one]
    _ = (-1 : ℤ) ^ (N.choose 2) := by
        rw [← mul_assoc, hcancel, one_mul]

/-! ## The matrix of transformed moments

The backward-shifted moment matrix of `AdelicHeightBridge.lean` is exactly the
matrix `(D_j v_{j+l}^*)_{j,l}` of transformed moments, so `V_N^*` may be read off
row by row.
-/

/-- Reindexing the lower-unitriangular row operation as the source operator
`D_j` applied to moment index `j+l`. -/
theorem zudilinBackwardShiftedMomentMatrix_apply (N : ℕ) (v : ℕ → PowerSeries ℤ)
    (j l : Fin N) :
    zudilinBackwardShiftedMomentMatrix N v j l =
      zudilinBackwardShiftApply (j : ℕ) ((j : ℕ) + (l : ℕ)) v := by
  have hreflect :
      (∑ k ∈ Finset.range ((j : ℕ) + 1),
          zudilinBackwardShiftCoeff (j : ℕ) k * v ((j : ℕ) + (l : ℕ) - k)) =
        ∑ k ∈ Finset.range ((j : ℕ) + 1),
          zudilinBackwardShiftCoeff (j : ℕ) ((j : ℕ) - k) * v (k + (l : ℕ)) := by
    rw [← Finset.sum_range_reflect
      (fun k => zudilinBackwardShiftCoeff (j : ℕ) k * v ((j : ℕ) + (l : ℕ) - k))
      ((j : ℕ) + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ (j : ℕ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show (j : ℕ) + 1 - 1 - k = (j : ℕ) - k by omega,
      show (j : ℕ) + (l : ℕ) - ((j : ℕ) - k) = k + (l : ℕ) by omega]
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range N :=
    Finset.range_subset_range.mpr j.isLt
  simp only [zudilinBackwardShiftedMomentMatrix, Matrix.mul_apply,
    zudilinBackwardShiftMatrix, zudilinMomentMatrix]
  rw [Fin.sum_univ_eq_sum_range
      (fun r => (if r ≤ (j : ℕ) then
        zudilinBackwardShiftCoeff (j : ℕ) ((j : ℕ) - r) else 0) *
          v (r + (l : ℕ))) N,
    ← Finset.sum_subset hsub
      (fun r _ hnr => by
        simp only [Finset.mem_range, Nat.lt_succ_iff, not_le] at hnr
        rw [if_neg (by omega), zero_mul]),
    zudilinBackwardShiftApply, hreflect]
  apply Finset.sum_congr rfl
  intro r hr
  rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))]

/-- Zudilin's normalized Hankel determinant `V_N^*`. -/
noncomputable def zudilinNormalizedHankelDet (N : ℕ) : PowerSeries ℤ :=
  (zudilinMomentMatrix N zudilinNormalizedMoment).det

/-- The matrix of source-transformed moments `D_j v_{j+l}^*`. -/
noncomputable def zudilinTransformedMomentMatrix (N : ℕ) :
    Matrix (Fin N) (Fin N) (PowerSeries ℤ) :=
  fun j l => zudilinTransformedNormalizedMoment (j : ℕ) (l : ℕ)

/-- The source row operations do not change the Hankel determinant. -/
theorem det_zudilinTransformedMomentMatrix (N : ℕ) :
    (zudilinTransformedMomentMatrix N).det = zudilinNormalizedHankelDet N := by
  rw [zudilinNormalizedHankelDet,
    ← det_zudilinBackwardShiftedMomentMatrix N zudilinNormalizedMoment]
  congr 1
  funext j l
  exact
    (zudilinBackwardShiftedMomentMatrix_apply N zudilinNormalizedMoment j l).symm

/-! ## Second-order coefficients of the zero-state tail step

Row `j = 2` needs one more coefficient of the source step unit than row `j = 1`
did: the `q^(2n+2)` coefficient of `𝓗_0(q^{n+1}) = (1-q^{n+1})^5 /
((1-q^{2n+2})(1-q^{2n+3}))`, which is `10 + 1 = 11`.
-/

private theorem one_sub_X_pow_fifth_expand (m : ℕ) :
    ((1 : PowerSeries ℤ) - PowerSeries.X ^ m) ^ 5 =
      1 - PowerSeries.C (5 : ℤ) * PowerSeries.X ^ m
        + PowerSeries.C (10 : ℤ) * PowerSeries.X ^ (2 * m)
        - PowerSeries.C (10 : ℤ) * PowerSeries.X ^ (3 * m)
        + PowerSeries.C (5 : ℤ) * PowerSeries.X ^ (4 * m)
        - PowerSeries.X ^ (5 * m) := by
  have h2 : (PowerSeries.X : PowerSeries ℤ) ^ (2 * m) =
      (PowerSeries.X ^ m) ^ 2 := by rw [Nat.mul_comm 2 m, pow_mul]
  have h3 : (PowerSeries.X : PowerSeries ℤ) ^ (3 * m) =
      (PowerSeries.X ^ m) ^ 3 := by rw [Nat.mul_comm 3 m, pow_mul]
  have h4 : (PowerSeries.X : PowerSeries ℤ) ^ (4 * m) =
      (PowerSeries.X ^ m) ^ 4 := by rw [Nat.mul_comm 4 m, pow_mul]
  have h5 : (PowerSeries.X : PowerSeries ℤ) ^ (5 * m) =
      (PowerSeries.X ^ m) ^ 5 := by rw [Nat.mul_comm 5 m, pow_mul]
  have hC5 : (PowerSeries.C (5 : ℤ)) = 5 := by simp
  have hC10 : (PowerSeries.C (10 : ℤ)) = 10 := by simp
  rw [h2, h3, h4, h5, hC5, hC10]
  ring

private theorem coeff_one_sub_X_pow_fifth_middle (m d : ℕ) (h1 : m < d)
    (h2 : d < 2 * m) :
    PowerSeries.coeff d ((1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 5) = 0 := by
  have e0 : ¬ d = 0 := by omega
  have f1 : ¬ d = m := by omega
  have f2 : ¬ d = 2 * m := by omega
  have f3 : ¬ d = 3 * m := by omega
  have f4 : ¬ d = 4 * m := by omega
  have f5 : ¬ d = 5 * m := by omega
  rw [one_sub_X_pow_fifth_expand]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  simp [e0, f1, f2, f3, f4, f5]

private theorem coeff_one_sub_X_pow_fifth_double (m d : ℕ) (hm : 0 < m)
    (hd : d = 2 * m) :
    PowerSeries.coeff d ((1 - PowerSeries.X ^ m : PowerSeries ℤ) ^ 5) = 10 := by
  subst hd
  have e0 : ¬ 2 * m = 0 := by omega
  have f1 : ¬ 2 * m = m := by omega
  have f3 : ¬ 2 * m = 3 * m := by omega
  have f4 : ¬ 2 * m = 4 * m := by omega
  have f5 : ¬ 2 * m = 5 * m := by omega
  rw [one_sub_X_pow_fifth_expand]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  simp [e0, f1, f3, f4, f5]

/-- Below the first moving denominator factor the source step unit agrees with
its exact numerator `(1-q^{n+1})^3 (1-q^{n+t+1})^2`. -/
theorem coeff_zudilinNormalizedTailStepUnit_eq_numerator (n t d : ℕ)
    (hd : d < 2 * n + t + 2) :
    PowerSeries.coeff d (zudilinNormalizedTailStepUnit n t) =
      PowerSeries.coeff d
        ((1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3 *
          (1 - PowerSeries.X ^ (n + t + 1)) ^ 2) := by
  have hCorder : (d : ℕ∞) <
      PowerSeries.order (PowerSeries.X ^ (2 * n + t + 2) : PowerSeries ℤ) := by
    rw [PowerSeries.order_X_pow]
    exact_mod_cast hd
  have hDorder : (d : ℕ∞) <
      PowerSeries.order (PowerSeries.X ^ (2 * n + t + 3) : PowerSeries ℤ) := by
    rw [PowerSeries.order_X_pow]
    exact_mod_cast (show d < 2 * n + t + 3 by omega)
  have hnum := congrArg (PowerSeries.coeff d)
    (zudilinNormalizedTailStepUnit_mul_denominators n t)
  rw [PowerSeries.coeff_mul_one_sub_of_lt_order d hDorder,
    PowerSeries.coeff_mul_one_sub_of_lt_order d hCorder] at hnum
  exact hnum

/-- Between its first and second associated grades the zero-state source step is
exactly the constant series. -/
theorem coeff_zudilinNormalizedTailStepUnit_zero_middle (n d : ℕ)
    (h1 : n + 1 < d) (h2 : d < 2 * n + 2) :
    PowerSeries.coeff d (zudilinNormalizedTailStepUnit n 0) = 0 := by
  rw [coeff_zudilinNormalizedTailStepUnit_eq_numerator n 0 d (by omega),
    show ((1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3 *
        (1 - PowerSeries.X ^ (n + 0 + 1)) ^ 2) =
      (1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 5 by
      simp only [Nat.add_zero]; ring]
  exact coeff_one_sub_X_pow_fifth_middle (n + 1) d (by omega) (by omega)

/-- **The second associated grade of the zero-state source step is `11`.**  Ten
from `(1-q^{n+1})^5` and one from the denominator factor `(1-q^{2n+2})^{-1}`. -/
theorem coeff_zudilinNormalizedTailStepUnit_zero_double (n : ℕ) :
    PowerSeries.coeff (2 * n + 2) (zudilinNormalizedTailStepUnit n 0) = 11 := by
  have hDorder : ((2 * n + 2 : ℕ) : ℕ∞) <
      PowerSeries.order (PowerSeries.X ^ (2 * n + 0 + 3) : PowerSeries ℤ) := by
    rw [PowerSeries.order_X_pow]
    exact_mod_cast (show 2 * n + 2 < 2 * n + 0 + 3 by omega)
  have hnum := congrArg (PowerSeries.coeff (2 * n + 2))
    (zudilinNormalizedTailStepUnit_mul_denominators n 0)
  rw [PowerSeries.coeff_mul_one_sub_of_lt_order (2 * n + 2) hDorder,
    mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow',
    if_pos (by omega), show 2 * n + 2 - (2 * n + 0 + 2) = 0 by omega,
    PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_zudilinNormalizedTailStepUnit,
    show ((1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 3 *
        (1 - PowerSeries.X ^ (n + 0 + 1)) ^ 2) =
      (1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) ^ 5 by
      simp only [Nat.add_zero]; ring,
    coeff_one_sub_X_pow_fifth_double (n + 1) (2 * n + 2) (by omega)
      (by omega)] at hnum
  linarith

/-! ### The source step unit minus one -/

private theorem coeff_step_sub_one_low (m t d : ℕ) (hd : d ≤ m) :
    PowerSeries.coeff d (zudilinNormalizedTailStepUnit m t - 1) = 0 := by
  rw [map_sub, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    rw [PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_zudilinNormalizedTailStepUnit]
    norm_num
  · rw [if_neg (by omega),
      coeff_zudilinNormalizedTailStepUnit_eq_zero_of_pos_lt m t d h (by omega)]
    ring

private theorem coeff_step_zero_sub_one_of_ne (m d : ℕ) (hd : d ≤ 2 * m + 1)
    (hne : d ≠ m + 1) :
    PowerSeries.coeff d (zudilinNormalizedTailStepUnit m 0 - 1) = 0 := by
  rcases Nat.lt_or_ge m d with h | h
  · rw [map_sub, PowerSeries.coeff_one, if_neg (by omega),
      coeff_zudilinNormalizedTailStepUnit_zero_middle m d (by omega) (by omega)]
    ring
  · exact coeff_step_sub_one_low m 0 d (by omega)

private theorem coeff_step_zero_sub_one_first (m d : ℕ) (hd : d = m + 1) :
    PowerSeries.coeff d (zudilinNormalizedTailStepUnit m 0 - 1) = -5 := by
  subst hd
  rw [map_sub, PowerSeries.coeff_one, if_neg (by omega),
    coeff_zudilinNormalizedTailStepUnit_first]
  norm_num

private theorem coeff_step_zero_sub_one_double (m d : ℕ) (hd : d = 2 * m + 2) :
    PowerSeries.coeff d (zudilinNormalizedTailStepUnit m 0 - 1) = 11 := by
  subst hd
  rw [map_sub, PowerSeries.coeff_one, if_neg (by omega),
    coeff_zudilinNormalizedTailStepUnit_zero_double]
  norm_num

private theorem coeff_step_pos_sub_one_first (m t d : ℕ) (ht : t ≠ 0)
    (hd : d = m + 1) :
    PowerSeries.coeff d (zudilinNormalizedTailStepUnit m t - 1) = -3 := by
  subst hd
  rw [map_sub, PowerSeries.coeff_one, if_neg (by omega),
    coeff_zudilinNormalizedTailStepUnit_first, if_neg ht]
  norm_num

/-! ## The second source row `D_2 v_{2+l}^*`

Two applications of the backward shift factor the `t`-th source tail as
`F_{n,t} · Φ_{n,t}` with
`Φ_{n,t} = q^{2t}𝓗_t(q^{n+1})𝓗_t(q^{n+2}) - (1+q) q^t 𝓗_t(q^{n+1}) + q`.
Only the states `t ≤ 2` reach the boundary degree `2n+3`, contributing
`14 + 3 + 1 = 18 = 3²·4/2`.
-/

/-- The exact two-step combination `D_2` applied to the `t`-th source tail. -/
noncomputable def zudilinTwoStepTail (n t : ℕ) : PowerSeries ℤ :=
  zudilinNormalizedTail (n + 1 + 1) t - zudilinNormalizedTail (n + 1) t -
    PowerSeries.X * (zudilinNormalizedTail (n + 1) t - zudilinNormalizedTail n t)

/-- The exact cofactor multiplying the `t`-th source tail after two backward
shifts. -/
noncomputable def zudilinTwoStepFactor (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ (2 * t) * zudilinNormalizedTailStepUnit n t *
      zudilinNormalizedTailStepUnit (n + 1) t -
    (1 + PowerSeries.X) * PowerSeries.X ^ t *
      zudilinNormalizedTailStepUnit n t +
    PowerSeries.X

theorem zudilinTwoStepTail_eq (n t : ℕ) :
    zudilinTwoStepTail n t =
      zudilinNormalizedTail n t * zudilinTwoStepFactor n t := by
  have h2 : zudilinNormalizedTail (n + 1 + 1) t =
      PowerSeries.X ^ t * zudilinNormalizedTail (n + 1) t *
        zudilinNormalizedTailStepUnit (n + 1) t :=
    zudilinNormalizedTail_succ (n + 1) t
  have h1 : zudilinNormalizedTail (n + 1) t =
      PowerSeries.X ^ t * zudilinNormalizedTail n t *
        zudilinNormalizedTailStepUnit n t :=
    zudilinNormalizedTail_succ n t
  have hpow : (PowerSeries.X : PowerSeries ℤ) ^ (2 * t) =
      PowerSeries.X ^ t * PowerSeries.X ^ t := by
    rw [two_mul, pow_add]
  rw [zudilinTwoStepTail, zudilinTwoStepFactor, h2, h1, hpow]
  ring

private theorem coeff_mul_first_at {φ ψ : PowerSeries ℤ} {m₁ m₂ D : ℕ}
    (h₁ : ∀ d, d < m₁ → PowerSeries.coeff d φ = 0)
    (h₂ : ∀ d, d < m₂ → PowerSeries.coeff d ψ = 0)
    (hD : D = m₁ + m₂) :
    PowerSeries.coeff D (φ * ψ) =
      PowerSeries.coeff m₁ φ * PowerSeries.coeff m₂ ψ := by
  subst hD
  exact (coeff_mul_first h₁ h₂).2

private theorem coeff_normalizedTail_leading' (n t d : ℕ)
    (hd : d = (n + 1) * t) :
    PowerSeries.coeff d (zudilinNormalizedTail n t) = 1 := by
  subst hd
  exact coeff_zudilinNormalizedTail_leading n t

/-- Every positive source state contributes a factor of `q`, so the two-step
cofactor has no constant term. -/
theorem coeff_zudilinTwoStepFactor_constant_of_pos (n t : ℕ) (ht : 0 < t) :
    PowerSeries.coeff 0 (zudilinTwoStepFactor n t) = 0 := by
  have h2t : 2 * t ≠ 0 := by omega
  have ht' : t ≠ 0 := by omega
  rw [zudilinTwoStepFactor, PowerSeries.coeff_zero_eq_constantCoeff]
  simp [h2t, ht']

/-! ### The zero state -/

private theorem zudilinTwoStepFactor_zero_eq (n : ℕ) :
    zudilinTwoStepFactor n 0 =
      (zudilinNormalizedTailStepUnit (n + 1) 0 - 1) -
        PowerSeries.X * (zudilinNormalizedTailStepUnit n 0 - 1) +
        (zudilinNormalizedTailStepUnit n 0 - 1) *
          (zudilinNormalizedTailStepUnit (n + 1) 0 - 1) := by
  rw [zudilinTwoStepFactor]
  simp only [Nat.mul_zero, pow_zero, one_mul, mul_one]
  ring

theorem coeff_zudilinTwoStepFactor_zero_eq_zero_of_lt (n d : ℕ)
    (hd : d < 2 * n + 3) :
    PowerSeries.coeff d (zudilinTwoStepFactor n 0) = 0 := by
  have hprod : PowerSeries.coeff d
      ((zudilinNormalizedTailStepUnit n 0 - 1) *
        (zudilinNormalizedTailStepUnit (n + 1) 0 - 1)) = 0 :=
    (coeff_mul_first
      (φ := zudilinNormalizedTailStepUnit n 0 - 1)
      (ψ := zudilinNormalizedTailStepUnit (n + 1) 0 - 1)
      (m₁ := n + 1) (m₂ := n + 2)
      (fun d' hd' => coeff_step_sub_one_low n 0 d' (by omega))
      (fun d' hd' => coeff_step_sub_one_low (n + 1) 0 d' (by omega))).1
      d (by omega)
  rw [zudilinTwoStepFactor_zero_eq n, map_add, map_sub, hprod, add_zero]
  cases d with
  | zero =>
      simp [coeff_step_sub_one_low (n + 1) 0 0 (by omega),
        PowerSeries.coeff_zero_eq_constantCoeff]
  | succ e =>
      rw [PowerSeries.coeff_succ_X_mul]
      by_cases he : e = n + 1
      · rw [coeff_step_zero_sub_one_first (n + 1) (e + 1) (by omega),
          coeff_step_zero_sub_one_first n e (by omega)]
        ring
      · rw [coeff_step_zero_sub_one_of_ne (n + 1) (e + 1) (by omega) (by omega),
          coeff_step_zero_sub_one_of_ne n e (by omega) (by omega)]
        ring

theorem coeff_zudilinTwoStepFactor_zero_first (n : ℕ) :
    PowerSeries.coeff (2 * n + 3) (zudilinTwoStepFactor n 0) = 14 := by
  have hprod : PowerSeries.coeff (2 * n + 3)
      ((zudilinNormalizedTailStepUnit n 0 - 1) *
        (zudilinNormalizedTailStepUnit (n + 1) 0 - 1)) = 25 := by
    rw [coeff_mul_first_at
      (φ := zudilinNormalizedTailStepUnit n 0 - 1)
      (ψ := zudilinNormalizedTailStepUnit (n + 1) 0 - 1)
      (m₁ := n + 1) (m₂ := n + 2)
      (fun d' hd' => coeff_step_sub_one_low n 0 d' (by omega))
      (fun d' hd' => coeff_step_sub_one_low (n + 1) 0 d' (by omega))
      (by omega),
      coeff_step_zero_sub_one_first n (n + 1) rfl,
      coeff_step_zero_sub_one_first (n + 1) (n + 2) (by omega)]
    norm_num
  rw [zudilinTwoStepFactor_zero_eq n, map_add, map_sub, hprod,
    show 2 * n + 3 = (2 * n + 2) + 1 by omega,
    PowerSeries.coeff_succ_X_mul,
    coeff_step_zero_sub_one_double n (2 * n + 2) rfl,
    coeff_step_zero_sub_one_of_ne (n + 1) (2 * n + 2 + 1) (by omega) (by omega)]
  norm_num

/-! ### The state `t = 1` -/

private theorem zudilinTwoStepFactor_one_eq (n : ℕ) :
    zudilinTwoStepFactor n 1 =
      PowerSeries.X ^ 2 * (zudilinNormalizedTailStepUnit (n + 1) 1 - 1) -
        PowerSeries.X * (zudilinNormalizedTailStepUnit n 1 - 1) +
        PowerSeries.X ^ 2 *
          ((zudilinNormalizedTailStepUnit n 1 - 1) *
            (zudilinNormalizedTailStepUnit (n + 1) 1 - 1)) := by
  rw [zudilinTwoStepFactor]
  simp only [Nat.mul_one, pow_one]
  ring

theorem coeff_zudilinTwoStepFactor_one_eq_zero_of_lt (n d : ℕ) (hd : d < n + 2) :
    PowerSeries.coeff d (zudilinTwoStepFactor n 1) = 0 := by
  have hA : PowerSeries.coeff d
      ((PowerSeries.X : PowerSeries ℤ) ^ 2 *
        (zudilinNormalizedTailStepUnit (n + 1) 1 - 1)) = 0 :=
    (coeff_mul_first (φ := (PowerSeries.X : PowerSeries ℤ) ^ 2)
      (ψ := zudilinNormalizedTailStepUnit (n + 1) 1 - 1) (m₁ := 2) (m₂ := n + 2)
      (fun d' hd' => by
        have h2b : ¬ d' = (2 : ℕ) := by omega
        simp [PowerSeries.coeff_X_pow, h2b])
      (fun d' hd' => coeff_step_sub_one_low (n + 1) 1 d' (by omega))).1
      d (by omega)
  have hB : PowerSeries.coeff d
      ((PowerSeries.X : PowerSeries ℤ) *
        (zudilinNormalizedTailStepUnit n 1 - 1)) = 0 :=
    (coeff_mul_first (φ := (PowerSeries.X : PowerSeries ℤ))
      (ψ := zudilinNormalizedTailStepUnit n 1 - 1) (m₁ := 1) (m₂ := n + 1)
      (fun d' hd' => by
        have h1b : ¬ d' = (1 : ℕ) := by omega
        simp [PowerSeries.coeff_X, h1b])
      (fun d' hd' => coeff_step_sub_one_low n 1 d' (by omega))).1 d (by omega)
  have hC : PowerSeries.coeff d
      ((PowerSeries.X : PowerSeries ℤ) ^ 2 *
        ((zudilinNormalizedTailStepUnit n 1 - 1) *
          (zudilinNormalizedTailStepUnit (n + 1) 1 - 1))) = 0 :=
    (coeff_mul_first (φ := (PowerSeries.X : PowerSeries ℤ) ^ 2)
      (ψ := (zudilinNormalizedTailStepUnit n 1 - 1) *
        (zudilinNormalizedTailStepUnit (n + 1) 1 - 1))
      (m₁ := 2) (m₂ := (n + 1) + (n + 2))
      (fun d' hd' => by
        have h2b : ¬ d' = (2 : ℕ) := by omega
        simp [PowerSeries.coeff_X_pow, h2b])
      (fun d' hd' =>
        (coeff_mul_first
          (φ := zudilinNormalizedTailStepUnit n 1 - 1)
          (ψ := zudilinNormalizedTailStepUnit (n + 1) 1 - 1)
          (m₁ := n + 1) (m₂ := n + 2)
          (fun d'' hd'' => coeff_step_sub_one_low n 1 d'' (by omega))
          (fun d'' hd'' =>
            coeff_step_sub_one_low (n + 1) 1 d'' (by omega))).1 d' hd')).1
      d (by omega)
  rw [zudilinTwoStepFactor_one_eq n, map_add, map_sub, hA, hB, hC]
  ring

theorem coeff_zudilinTwoStepFactor_one_first (n : ℕ) :
    PowerSeries.coeff (n + 2) (zudilinTwoStepFactor n 1) = 3 := by
  have hA : PowerSeries.coeff (n + 2)
      ((PowerSeries.X : PowerSeries ℤ) ^ 2 *
        (zudilinNormalizedTailStepUnit (n + 1) 1 - 1)) = 0 :=
    (coeff_mul_first (φ := (PowerSeries.X : PowerSeries ℤ) ^ 2)
      (ψ := zudilinNormalizedTailStepUnit (n + 1) 1 - 1) (m₁ := 2) (m₂ := n + 2)
      (fun d' hd' => by
        have h2b : ¬ d' = (2 : ℕ) := by omega
        simp [PowerSeries.coeff_X_pow, h2b])
      (fun d' hd' => coeff_step_sub_one_low (n + 1) 1 d' (by omega))).1
      (n + 2) (by omega)
  have hC : PowerSeries.coeff (n + 2)
      ((PowerSeries.X : PowerSeries ℤ) ^ 2 *
        ((zudilinNormalizedTailStepUnit n 1 - 1) *
          (zudilinNormalizedTailStepUnit (n + 1) 1 - 1))) = 0 :=
    (coeff_mul_first (φ := (PowerSeries.X : PowerSeries ℤ) ^ 2)
      (ψ := (zudilinNormalizedTailStepUnit n 1 - 1) *
        (zudilinNormalizedTailStepUnit (n + 1) 1 - 1))
      (m₁ := 2) (m₂ := (n + 1) + (n + 2))
      (fun d' hd' => by
        have h2b : ¬ d' = (2 : ℕ) := by omega
        simp [PowerSeries.coeff_X_pow, h2b])
      (fun d' hd' =>
        (coeff_mul_first
          (φ := zudilinNormalizedTailStepUnit n 1 - 1)
          (ψ := zudilinNormalizedTailStepUnit (n + 1) 1 - 1)
          (m₁ := n + 1) (m₂ := n + 2)
          (fun d'' hd'' => coeff_step_sub_one_low n 1 d'' (by omega))
          (fun d'' hd'' =>
            coeff_step_sub_one_low (n + 1) 1 d'' (by omega))).1 d' hd')).1
      (n + 2) (by omega)
  rw [zudilinTwoStepFactor_one_eq n, map_add, map_sub, hA, hC,
    show n + 2 = (n + 1) + 1 by omega, PowerSeries.coeff_succ_X_mul,
    coeff_step_pos_sub_one_first n 1 (n + 1) (by omega) rfl]
  ring

/-! ### The state `t = 2` -/

private theorem zudilinTwoStepFactor_two_eq (n : ℕ) :
    zudilinTwoStepFactor n 2 =
      (PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 +
          PowerSeries.X ^ 4) +
        PowerSeries.X ^ 2 *
          (PowerSeries.X ^ 2 * (zudilinNormalizedTailStepUnit n 2 - 1) +
            PowerSeries.X ^ 2 * (zudilinNormalizedTailStepUnit (n + 1) 2 - 1) +
            PowerSeries.X ^ 2 *
              ((zudilinNormalizedTailStepUnit n 2 - 1) *
                (zudilinNormalizedTailStepUnit (n + 1) 2 - 1)) -
            (zudilinNormalizedTailStepUnit n 2 - 1) -
            PowerSeries.X * (zudilinNormalizedTailStepUnit n 2 - 1)) := by
  rw [zudilinTwoStepFactor]
  norm_num
  ring

theorem coeff_zudilinTwoStepFactor_two_constant (n : ℕ) :
    PowerSeries.coeff 0 (zudilinTwoStepFactor n 2) = 0 :=
  coeff_zudilinTwoStepFactor_constant_of_pos n 2 (by omega)

theorem coeff_zudilinTwoStepFactor_two_first (n : ℕ) :
    PowerSeries.coeff 1 (zudilinTwoStepFactor n 2) = 1 := by
  rw [zudilinTwoStepFactor_two_eq n, map_add, PowerSeries.coeff_X_pow_mul',
    if_neg (by omega)]
  simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

/-! ### The complete second-row initial monomial -/

theorem coeff_zudilinTwoStepTail_eq_zero_of_lt (n t d : ℕ) (hd : d < 2 * n + 3) :
    PowerSeries.coeff d (zudilinTwoStepTail n t) = 0 := by
  rw [zudilinTwoStepTail_eq]
  by_cases h0 : t = 0
  · subst h0
    exact (coeff_mul_first (φ := zudilinNormalizedTail n 0)
      (ψ := zudilinTwoStepFactor n 0) (m₁ := 0) (m₂ := 2 * n + 3)
      (fun d' hd' => absurd hd' (by omega))
      (fun d' hd' =>
        coeff_zudilinTwoStepFactor_zero_eq_zero_of_lt n d' hd')).1 d (by omega)
  by_cases h1 : t = 1
  · subst h1
    exact (coeff_mul_first (φ := zudilinNormalizedTail n 1)
      (ψ := zudilinTwoStepFactor n 1) (m₁ := n + 1) (m₂ := n + 2)
      (fun d' hd' =>
        coeff_zudilinNormalizedTail_eq_zero_of_lt n 1 d' (by omega))
      (fun d' hd' =>
        coeff_zudilinTwoStepFactor_one_eq_zero_of_lt n d' hd')).1 d (by omega)
  by_cases h2 : t = 2
  · subst h2
    exact (coeff_mul_first (φ := zudilinNormalizedTail n 2)
      (ψ := zudilinTwoStepFactor n 2) (m₁ := 2 * n + 2) (m₂ := 1)
      (fun d' hd' =>
        coeff_zudilinNormalizedTail_eq_zero_of_lt n 2 d' (by omega))
      (fun d' hd' => by
        rw [show d' = 0 by omega]
        exact coeff_zudilinTwoStepFactor_two_constant n)).1 d (by omega)
  · have ht3 : 3 ≤ t := by omega
    have hle : (n + 1) * 3 ≤ (n + 1) * t := Nat.mul_le_mul (le_refl (n + 1)) ht3
    exact (coeff_mul_first (φ := zudilinNormalizedTail n t)
      (ψ := zudilinTwoStepFactor n t) (m₁ := (n + 1) * t) (m₂ := 1)
      (fun d' hd' => coeff_zudilinNormalizedTail_eq_zero_of_lt n t d' hd')
      (fun d' hd' => by
        rw [show d' = 0 by omega]
        exact coeff_zudilinTwoStepFactor_constant_of_pos n t (by omega))).1
      d (by omega)

theorem coeff_zudilinTwoStepTail_first (n t : ℕ) :
    PowerSeries.coeff (2 * n + 3) (zudilinTwoStepTail n t) =
      if t = 0 then 14 else if t = 1 then 3 else if t = 2 then 1 else 0 := by
  rw [zudilinTwoStepTail_eq]
  by_cases h0 : t = 0
  · subst h0
    rw [coeff_mul_first_at (φ := zudilinNormalizedTail n 0)
      (ψ := zudilinTwoStepFactor n 0) (m₁ := 0) (m₂ := 2 * n + 3)
      (fun d' hd' => absurd hd' (by omega))
      (fun d' hd' =>
        coeff_zudilinTwoStepFactor_zero_eq_zero_of_lt n d' hd') (by omega),
      coeff_zudilinTwoStepFactor_zero_first n,
      coeff_normalizedTail_leading' n 0 0 (by omega)]
    norm_num
  by_cases h1 : t = 1
  · subst h1
    rw [coeff_mul_first_at (φ := zudilinNormalizedTail n 1)
      (ψ := zudilinTwoStepFactor n 1) (m₁ := n + 1) (m₂ := n + 2)
      (fun d' hd' =>
        coeff_zudilinNormalizedTail_eq_zero_of_lt n 1 d' (by omega))
      (fun d' hd' =>
        coeff_zudilinTwoStepFactor_one_eq_zero_of_lt n d' hd') (by omega),
      coeff_zudilinTwoStepFactor_one_first n,
      coeff_normalizedTail_leading' n 1 (n + 1) (by omega)]
    norm_num
  by_cases h2 : t = 2
  · subst h2
    rw [coeff_mul_first_at (φ := zudilinNormalizedTail n 2)
      (ψ := zudilinTwoStepFactor n 2) (m₁ := 2 * n + 2) (m₂ := 1)
      (fun d' hd' =>
        coeff_zudilinNormalizedTail_eq_zero_of_lt n 2 d' (by omega))
      (fun d' hd' => by
        rw [show d' = 0 by omega]
        exact coeff_zudilinTwoStepFactor_two_constant n) (by omega),
      coeff_zudilinTwoStepFactor_two_first n,
      coeff_normalizedTail_leading' n 2 (2 * n + 2) (by omega)]
    norm_num
  · have ht3 : 3 ≤ t := by omega
    have hle : (n + 1) * 3 ≤ (n + 1) * t := Nat.mul_le_mul (le_refl (n + 1)) ht3
    rw [(coeff_mul_first (φ := zudilinNormalizedTail n t)
      (ψ := zudilinTwoStepFactor n t) (m₁ := (n + 1) * t) (m₂ := 1)
      (fun d' hd' => coeff_zudilinNormalizedTail_eq_zero_of_lt n t d' hd')
      (fun d' hd' => by
        rw [show d' = 0 by omega]
        exact coeff_zudilinTwoStepFactor_constant_of_pos n t (by omega))).1
      (2 * n + 3) (by omega)]
    rw [if_neg h0, if_neg h1, if_neg h2]

/-! ### Assembling the second transformed row -/

/-- Only finitely many source tails reach any fixed degree, so the exact moment
coefficient is any sufficiently long finite sum. -/
theorem coeff_zudilinNormalizedMoment_range (n d T : ℕ) (hT : d < (n + 1) * T) :
    PowerSeries.coeff d (zudilinNormalizedMoment n) =
      ∑ t ∈ Finset.range T, PowerSeries.coeff d (zudilinNormalizedTail n t) := by
  rw [coeff_zudilinNormalizedMoment]
  apply Finset.sum_subset
  · apply Finset.range_subset_range.mpr
    have hdiv : d / (n + 1) < T :=
      (Nat.div_lt_iff_lt_mul (show 0 < n + 1 by omega)).mpr
        (by rw [Nat.mul_comm] at hT; exact hT)
    omega
  · intro t _ hnot
    apply coeff_zudilinNormalizedTail_eq_zero_of_lt
    have hgt : d / (n + 1) < t := by
      simp only [Finset.mem_range, not_lt] at hnot
      omega
    have hlt := (Nat.div_lt_iff_lt_mul (show 0 < n + 1 by omega)).mp hgt
    rw [Nat.mul_comm]
    exact hlt

private theorem coeff_moment_eq_sum_range (m d e : ℕ) (he : e ≤ d) :
    PowerSeries.coeff e (zudilinNormalizedMoment m) =
      PowerSeries.coeff e
        (∑ t ∈ Finset.range (d + 1), zudilinNormalizedTail m t) := by
  rw [map_sum]
  apply coeff_zudilinNormalizedMoment_range
  have hle : 1 * (d + 1) ≤ (m + 1) * (d + 1) :=
    Nat.mul_le_mul (by omega) (le_refl (d + 1))
  omega

private theorem coeff_X_mul_congr (A B : PowerSeries ℤ) (d : ℕ)
    (h : ∀ e, e < d → PowerSeries.coeff e A = PowerSeries.coeff e B) :
    PowerSeries.coeff d (PowerSeries.X * A) =
      PowerSeries.coeff d (PowerSeries.X * B) := by
  cases d with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ e =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
        h e (by omega)]

private theorem sum_zudilinTwoStepTail (l T : ℕ) :
    (∑ t ∈ Finset.range T, zudilinTwoStepTail l t) =
      ((∑ t ∈ Finset.range T, zudilinNormalizedTail (l + 1 + 1) t) -
          ∑ t ∈ Finset.range T, zudilinNormalizedTail (l + 1) t) -
        PowerSeries.X *
          ((∑ t ∈ Finset.range T, zudilinNormalizedTail (l + 1) t) -
            ∑ t ∈ Finset.range T, zudilinNormalizedTail l t) := by
  simp only [zudilinTwoStepTail]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib]

/-- The second transformed row is the exact coefficientwise sum of two-step
source tails. -/
theorem coeff_zudilinTransformedNormalizedMoment_two_eq (l d : ℕ) :
    PowerSeries.coeff d (zudilinTransformedNormalizedMoment 2 l) =
      ∑ t ∈ Finset.range (d + 1),
        PowerSeries.coeff d (zudilinTwoStepTail l t) := by
  have hrow1 : ∀ m : ℕ, zudilinTransformedNormalizedMoment 1 m =
      zudilinNormalizedMoment (m + 1) - zudilinNormalizedMoment m := by
    intro m
    simpa using zudilinTransformedNormalizedMoment_succ 0 m
  have hrow2 : zudilinTransformedNormalizedMoment 2 l =
      zudilinTransformedNormalizedMoment 1 (l + 1) -
        PowerSeries.X ^ 1 * zudilinTransformedNormalizedMoment 1 l :=
    zudilinTransformedNormalizedMoment_succ 1 l
  have hexpand : zudilinTransformedNormalizedMoment 2 l =
      (zudilinNormalizedMoment (l + 1 + 1) - zudilinNormalizedMoment (l + 1)) -
        PowerSeries.X *
          (zudilinNormalizedMoment (l + 1) - zudilinNormalizedMoment l) := by
    rw [hrow2, hrow1 (l + 1), hrow1 l, pow_one]
  rw [hexpand, ← map_sum, sum_zudilinTwoStepTail l (d + 1),
    map_sub, map_sub, map_sub, map_sub,
    coeff_moment_eq_sum_range (l + 1 + 1) d d (le_refl d),
    coeff_moment_eq_sum_range (l + 1) d d (le_refl d)]
  congr 1
  apply coeff_X_mul_congr
  intro e he
  rw [map_sub, map_sub, coeff_moment_eq_sum_range (l + 1) d e (by omega),
    coeff_moment_eq_sum_range l d e (by omega)]

theorem coeff_zudilinTransformedNormalizedMoment_two_eq_zero_of_lt (l d : ℕ)
    (hd : d < 2 * l + 3) :
    PowerSeries.coeff d (zudilinTransformedNormalizedMoment 2 l) = 0 := by
  rw [coeff_zudilinTransformedNormalizedMoment_two_eq]
  apply Finset.sum_eq_zero
  intro t _
  exact coeff_zudilinTwoStepTail_eq_zero_of_lt l t d hd

/-- **The second transformed row, uniformly in the column.**  The exact
coefficient of `q^(2l+3)` in `D_2 v_{2+l}^*` is `18 = 3²·4/2`, assembled from the
three surviving source states `t = 0, 1, 2` as `14 + 3 + 1`. -/
theorem coeff_zudilinTransformedNormalizedMoment_two_first (l : ℕ) :
    PowerSeries.coeff (2 * l + 3)
        (zudilinTransformedNormalizedMoment 2 l) = 18 := by
  rw [coeff_zudilinTransformedNormalizedMoment_two_eq]
  have hval : ∀ t ∈ Finset.range (2 * l + 3 + 1),
      PowerSeries.coeff (2 * l + 3) (zudilinTwoStepTail l t) =
        if t = 0 then 14 else if t = 1 then 3 else if t = 2 then 1 else 0 :=
    fun t _ => coeff_zudilinTwoStepTail_first l t
  rw [Finset.sum_congr rfl hval,
    ← Finset.sum_subset
      (show Finset.range 3 ⊆ Finset.range (2 * l + 3 + 1) from
        Finset.range_subset_range.mpr (by omega))
      (fun t _ hnot => by
        simp only [Finset.mem_range, not_lt] at hnot
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)])]
  norm_num [Finset.sum_range_succ]

/-- The exact order of the second transformed row. -/
theorem order_zudilinTransformedNormalizedMoment_two (l : ℕ) :
    PowerSeries.order (zudilinTransformedNormalizedMoment 2 l) = 2 * l + 3 := by
  apply PowerSeries.order_eq_nat.mpr
  refine ⟨?_, fun d hd =>
    coeff_zudilinTransformedNormalizedMoment_two_eq_zero_of_lt l d hd⟩
  rw [coeff_zudilinTransformedNormalizedMoment_two_first]
  norm_num

/-- **Complete second transformed-row initial monomial, in every column.**  This
is the first row beyond `zudilinTransformedNormalizedMoment_one_initialMonomial`
of `AdelicHeightBridge.lean`; rows `j ≥ 3` remain open. -/
theorem zudilinTransformedNormalizedMoment_two_initialMonomial (l : ℕ) :
    PowerSeries.order (zudilinTransformedNormalizedMoment 2 l) = 2 * l + 3 ∧
      PowerSeries.coeff (2 * l + 3)
        (zudilinTransformedNormalizedMoment 2 l) = 18 :=
  ⟨order_zudilinTransformedNormalizedMoment_two l,
    coeff_zudilinTransformedNormalizedMoment_two_first l⟩

/-! ## The conditional sharp endpoint

The only input still missing is the row initial monomial for `j ≥ 3`.  Stating
it as a hypothesis makes the remaining gap exact and machine-checked, and the
determinant-level deduction below is unconditional.
-/

/-- The source-row input: in every column, transformed row `j` has initial
monomial `(-1)^j (j+1)²(j+2)/2 · q^{j(j+1)/2 + jl}`.  Rows `j ≤ 2` are proved
(`zudilinRowInitialMonomial_of_le_two`); rows `j ≥ 3` are open. -/
def ZudilinRowInitialMonomial (j : ℕ) : Prop :=
  ∀ l : ℕ,
    (∀ d, d < j * (j + 1) / 2 + j * l →
        PowerSeries.coeff d (zudilinTransformedNormalizedMoment j l) = 0) ∧
      PowerSeries.coeff (j * (j + 1) / 2 + j * l)
          (zudilinTransformedNormalizedMoment j l) =
        (-1 : ℤ) ^ j * (zudilinTransformedRowCoeff j : ℤ)

theorem zudilinRowInitialMonomial_zero : ZudilinRowInitialMonomial 0 := by
  intro l
  constructor
  · intro d hd
    exact absurd hd (by omega)
  · simp only [show 0 * (0 + 1) / 2 + 0 * l = 0 from by omega,
      zudilinTransformedNormalizedMoment_zero,
      PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_zudilinNormalizedMoment]
    norm_num [zudilinTransformedRowCoeff]

theorem zudilinRowInitialMonomial_one : ZudilinRowInitialMonomial 1 := by
  intro l
  constructor
  · intro d hd
    exact coeff_zudilinTransformedNormalizedMoment_one_eq_zero_of_lt l d
      (by omega)
  · simp only [show 1 * (1 + 1) / 2 + 1 * l = l + 1 from by omega,
      coeff_zudilinTransformedNormalizedMoment_one_first]
    norm_num [zudilinTransformedRowCoeff]

theorem zudilinRowInitialMonomial_two : ZudilinRowInitialMonomial 2 := by
  intro l
  constructor
  · intro d hd
    exact coeff_zudilinTransformedNormalizedMoment_two_eq_zero_of_lt l d
      (by omega)
  · simp only [show 2 * (2 + 1) / 2 + 2 * l = 2 * l + 3 from by omega,
      coeff_zudilinTransformedNormalizedMoment_two_first]
    norm_num [zudilinTransformedRowCoeff]

theorem zudilinRowInitialMonomial_of_le_two {j : ℕ} (hj : j ≤ 2) :
    ZudilinRowInitialMonomial j := by
  interval_cases j
  · exact zudilinRowInitialMonomial_zero
  · exact zudilinRowInitialMonomial_one
  · exact zudilinRowInitialMonomial_two

/-- **Conditional sharp order and leading coefficient of `V_N^*`.**  Given the
row initial monomials (proved above for `j ≤ 2`, open for `j ≥ 3`), the
normalized Hankel determinant has exactly Zudilin's exponent `∑_{j<N} j²` *and*
leading coefficient `∏_{j<N} (j+1)²(j+2)/2 = (N!)²(N+1)!/2^N`.

The hypothesis is purely row level; everything determinant level — the Leibniz
bridge, the unique-minimizer combinatorics and the sign cancellation — is
unconditional and proved in this module.  Feeding the closed forms of
`zudilinSharpHankelOrderAndCoeff_algebraicAssembly` then gives
`6·ord = N(N-1)(2N-1)` and `2^N·lc = (N!)²(N+1)!`. -/
theorem zudilinSharpHankelOrderAndCoeff_of_rowInitialMonomial
    (h : ∀ j : ℕ, ZudilinRowInitialMonomial j) (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
        ((∑ j ∈ Finset.range N, j ^ 2 : ℕ) : ℕ∞) ∧
      PowerSeries.coeff (∑ j ∈ Finset.range N, j ^ 2)
          (zudilinNormalizedHankelDet N) =
        ∏ j ∈ Finset.range N, (zudilinTransformedRowCoeff j : ℤ) := by
  have hzero : ∀ i j : Fin N, ∀ d, d < zudilinLeadingEntryOrder i j →
      PowerSeries.coeff d (zudilinTransformedMomentMatrix N i j) = 0 :=
    fun i j d hd => (h (i : ℕ) (j : ℕ)).1 d hd
  have hlead : ∀ i j : Fin N,
      PowerSeries.coeff (zudilinLeadingEntryOrder i j)
          (zudilinTransformedMomentMatrix N i j) =
        (-1 : ℤ) ^ (i : ℕ) * (zudilinTransformedRowCoeff (i : ℕ) : ℤ) :=
    fun i j => (h (i : ℕ) (j : ℕ)).2
  have hentry : ∀ i j : Fin N,
      PowerSeries.order (zudilinTransformedMomentMatrix N i j) =
        (zudilinLeadingEntryOrder i j : ℕ∞) := by
    intro i j
    apply PowerSeries.order_eq_nat.mpr
    refine ⟨?_, fun d hd => hzero i j d hd⟩
    rw [hlead i j]
    have hc : (zudilinTransformedRowCoeff (i : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (zudilinTransformedRowCoeff_pos (i : ℕ)).ne'
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hc
  constructor
  · rw [← det_zudilinTransformedMomentMatrix N]
    exact order_det_eq_of_unique_minimizing_permutation
      (zudilinTransformedMomentMatrix N) zudilinLeadingEntryOrder
      (Fin.revPerm : Equiv.Perm (Fin N)) (∑ j ∈ Finset.range N, j ^ 2)
      hentry (sum_zudilinLeadingEntryOrder_revPerm N)
      (fun σ hσ => sum_zudilinLeadingEntryOrder_lt_of_ne_revPerm σ hσ)
  · rw [← det_zudilinTransformedMomentMatrix N,
      coeff_det_eq_of_unique_minimizing_permutation
        (zudilinTransformedMomentMatrix N) zudilinLeadingEntryOrder
        (fun i _ =>
          (-1 : ℤ) ^ (i : ℕ) * (zudilinTransformedRowCoeff (i : ℕ) : ℤ))
        (Fin.revPerm : Equiv.Perm (Fin N)) (∑ j ∈ Finset.range N, j ^ 2)
        hzero hlead (sum_zudilinLeadingEntryOrder_revPerm N)
        (fun σ hσ => sum_zudilinLeadingEntryOrder_lt_of_ne_revPerm σ hσ)]
    exact signedRowProduct_revPerm N

end ErdosProblems.Erdos1049
