import ErdosProblems.Erdos68.FactorialZeroPlateau

/-!
# Erdős #68: affine-defect rigidity near `n! - 1`

For an integer sequence `b n`, write

* `e n = n! - 1 - b n` for its downward endpoint error, and
* `η n = b (n + 1) - (n + 1) b n - n` for its affine defect.

Then `η n = (n + 1) e n - e (n + 1)`.  A positive error whose future value
still lies below the quadratic envelope forces one of the next four affine
defects to be at least its index.  Thus a nontrivial cofinal downward
approximation inside that envelope has cofinally many large affine defects.

This is an exact rigidity theorem for integer approximants.  The reciprocal
transform that would turn it into an irrationality proof for Erdős #68 is a
separate open boundary.
-/

namespace ErdosProblems.Erdos68

open Filter

/-- The quadratic error envelope used by the affine-defect argument. -/
def endpointQuadraticBound (n : ℕ) : ℤ := (n : ℤ) ^ 2 + 2

/-- A four-step sublinear-defect run makes a positive error exceed the
quadratic envelope.  The lemma is abstract: only the affine recurrence is
used. -/
theorem four_step_affine_defect_blowup
    (e η : ℕ → ℤ) (n : ℕ)
    (hrec : ∀ k, η k = ((k : ℤ) + 1) * e k - e (k + 1))
    (hePos : 0 < e n)
    (hη0 : η n < (n : ℤ))
    (hη1 : η (n + 1) < ((n + 1 : ℕ) : ℤ))
    (hη2 : η (n + 2) < ((n + 2 : ℕ) : ℤ))
    (hη3 : η (n + 3) < ((n + 3 : ℕ) : ℤ)) :
    endpointQuadraticBound (n + 4) < e (n + 4) := by
  have hn : 0 ≤ (n : ℤ) := Nat.cast_nonneg n
  have hr0 := hrec n
  have hr1 := hrec (n + 1)
  have hr2 := hrec (n + 2)
  have hr3 := hrec (n + 3)
  push_cast at hr0 hr1 hr2 hr3 hη1 hη2 hη3 ⊢
  have he1 : (2 : ℤ) ≤ e (n + 1) := by
    nlinarith
  have hcoef1 : 0 ≤ (n : ℤ) + 2 := by omega
  have hmul1 : ((n : ℤ) + 2) * 2 ≤ ((n : ℤ) + 2) * e (n + 1) :=
    mul_le_mul_of_nonneg_left he1 hcoef1
  have he2raw : (n : ℤ) + 3 < e (n + 2) := by
    nlinarith
  have he2 : (n : ℤ) + 4 ≤ e (n + 2) := by omega
  have hcoef2 : 0 ≤ (n : ℤ) + 3 := by omega
  have hmul2 :
      ((n : ℤ) + 3) * ((n : ℤ) + 4) ≤
        ((n : ℤ) + 3) * e (n + 2) :=
    mul_le_mul_of_nonneg_left he2 hcoef2
  have he3raw :
      (n : ℤ) ^ 2 + 6 * (n : ℤ) + 10 < e (n + 3) := by
    nlinarith [sq_nonneg (n : ℤ)]
  have he3 :
      (n : ℤ) ^ 2 + 6 * (n : ℤ) + 11 ≤ e (n + 3) := by
    omega
  have hcoef3 : 0 ≤ (n : ℤ) + 4 := by omega
  have hmul3 :
      ((n : ℤ) + 4) * ((n : ℤ) ^ 2 + 6 * (n : ℤ) + 11) ≤
        ((n : ℤ) + 4) * e (n + 3) :=
    mul_le_mul_of_nonneg_left he3 hcoef3
  have he4raw :
      ((n : ℤ) + 4) * ((n : ℤ) ^ 2 + 6 * (n : ℤ) + 11) -
          ((n : ℤ) + 3) < e (n + 4) := by
    nlinarith
  unfold endpointQuadraticBound
  push_cast
  ring_nf at he4raw ⊢
  nlinarith [sq_nonneg ((n : ℤ) + 3)]

/-- Two-sided form of the four-step blow-up.  A nonzero signed error and
four defects of absolute value below their indices force the absolute error
past the same quadratic envelope. -/
theorem four_step_abs_affine_defect_blowup
    (e η : ℕ → ℤ) (n : ℕ)
    (hrec : ∀ k, η k = ((k : ℤ) + 1) * e k - e (k + 1))
    (heNe : e n ≠ 0)
    (hη0 : |η n| < (n : ℤ))
    (hη1 : |η (n + 1)| < ((n + 1 : ℕ) : ℤ))
    (hη2 : |η (n + 2)| < ((n + 2 : ℕ) : ℤ))
    (hη3 : |η (n + 3)| < ((n + 3 : ℕ) : ℤ)) :
    endpointQuadraticBound (n + 4) < |e (n + 4)| := by
  rcases lt_or_gt_of_ne heNe with heNeg | hePos
  · let e' : ℕ → ℤ := fun k => -e k
    let η' : ℕ → ℤ := fun k => -η k
    have hrec' : ∀ k, η' k = ((k : ℤ) + 1) * e' k - e' (k + 1) := by
      intro k
      dsimp [e', η']
      rw [hrec k]
      ring
    have hePos' : 0 < e' n := by dsimp [e']; omega
    have hη0' : η' n < (n : ℤ) := by
      dsimp [η']
      have := (abs_lt.mp hη0).1
      omega
    have hη1' : η' (n + 1) < ((n + 1 : ℕ) : ℤ) := by
      dsimp [η']
      have := (abs_lt.mp hη1).1
      omega
    have hη2' : η' (n + 2) < ((n + 2 : ℕ) : ℤ) := by
      dsimp [η']
      have := (abs_lt.mp hη2).1
      omega
    have hη3' : η' (n + 3) < ((n + 3 : ℕ) : ℤ) := by
      dsimp [η']
      have := (abs_lt.mp hη3).1
      omega
    have hblow := four_step_affine_defect_blowup
      e' η' n hrec' hePos' hη0' hη1' hη2' hη3'
    have he4Neg : e (n + 4) < 0 := by
      dsimp [e'] at hblow
      have hboundNonneg : 0 ≤ endpointQuadraticBound (n + 4) := by
        unfold endpointQuadraticBound
        positivity
      omega
    rw [abs_of_neg he4Neg]
    simpa [e'] using hblow
  · have hη0' : η n < (n : ℤ) := (abs_lt.mp hη0).2
    have hη1' : η (n + 1) < ((n + 1 : ℕ) : ℤ) := (abs_lt.mp hη1).2
    have hη2' : η (n + 2) < ((n + 2 : ℕ) : ℤ) := (abs_lt.mp hη2).2
    have hη3' : η (n + 3) < ((n + 3 : ℕ) : ℤ) := (abs_lt.mp hη3).2
    have hblow := four_step_affine_defect_blowup
      e η n hrec hePos hη0' hη1' hη2' hη3'
    have he4Pos : 0 < e (n + 4) := by
      have hboundNonneg : 0 ≤ endpointQuadraticBound (n + 4) := by
        unfold endpointQuadraticBound
        positivity
      omega
    rwa [abs_of_pos he4Pos]

/-- Endpoint error of an integer approximant to `n! - 1`. -/
def factorialEndpointError (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n.factorial : ℤ) - 1 - b n

/-- Defect in the exact affine recurrence satisfied by `n! - 1`. -/
def factorialAffineDefect (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  b (n + 1) - ((n : ℤ) + 1) * b n - n

/-- The affine defect is exactly the first-order transform of the endpoint
error. -/
theorem factorialAffineDefect_eq_error_transform
    (b : ℕ → ℤ) (n : ℕ) :
    factorialAffineDefect b n =
      ((n : ℤ) + 1) * factorialEndpointError b n -
        factorialEndpointError b (n + 1) := by
  simp only [factorialAffineDefect, factorialEndpointError,
    Nat.factorial_succ]
  push_cast
  ring

/-- Finite telescoping form of the affine-defect transform.  No convergence
hypothesis is needed: after division by the next factorial, every defect is
exactly the difference of two consecutive normalized endpoint errors. -/
theorem affineDefect_factorial_telescope
    (e η : ℕ → ℤ)
    (hrec : ∀ k, η k = ((k : ℤ) + 1) * e k - e (k + 1))
    (n k : ℕ) :
    ∑ j ∈ Finset.range k,
        ((η (n + j) : ℤ) : ℚ) /
          (((n + j + 1).factorial : ℕ) : ℚ) =
      ((e n : ℤ) : ℚ) / ((n.factorial : ℕ) : ℚ) -
        ((e (n + k) : ℤ) : ℚ) /
          (((n + k).factorial : ℕ) : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      rw [← Nat.add_assoc n k 1]
      have hr := hrec (n + k)
      have hfac :
          (n + k + 1).factorial = (n + k + 1) * (n + k).factorial := by
        rw [Nat.factorial_succ]
      rw [hfac]
      push_cast at hr ⊢
      have hrQ :
          ((η (n + k) : ℤ) : ℚ) =
            (((n + k : ℕ) : ℚ) + 1) * ((e (n + k) : ℤ) : ℚ) -
              ((e (n + k + 1) : ℤ) : ℚ) := by
        exact_mod_cast hr
      have hfacNe : ((((n + k).factorial : ℕ) : ℚ)) ≠ 0 := by
        positivity
      have hstepNe : (((n + k + 1 : ℕ) : ℚ)) ≠ 0 := by
        positivity
      rw [hrQ]
      field_simp [hfacNe, hstepNe]
      rw [Nat.cast_add]
      ring

/-- The concrete endpoint error and affine defect satisfy the preceding
finite factorial telescope. -/
theorem factorialAffineDefect_factorial_telescope
    (b : ℕ → ℤ) (n k : ℕ) :
    ∑ j ∈ Finset.range k,
        ((factorialAffineDefect b (n + j) : ℤ) : ℚ) /
          (((n + j + 1).factorial : ℕ) : ℚ) =
      ((factorialEndpointError b n : ℤ) : ℚ) /
          ((n.factorial : ℕ) : ℚ) -
        ((factorialEndpointError b (n + k) : ℤ) : ℚ) /
          (((n + k).factorial : ℕ) : ℚ) :=
  affineDefect_factorial_telescope
    (factorialEndpointError b) (factorialAffineDefect b)
    (factorialAffineDefect_eq_error_transform b) n k

/-- If a downward endpoint error is positive at `n` but is still inside the
quadratic envelope four steps later, one of the four intervening affine
defects is at least its index. -/
theorem exists_affineDefect_spike_in_four_block
    (b : ℕ → ℤ) (n : ℕ)
    (hePos : 0 < factorialEndpointError b n)
    (hbound4 :
      factorialEndpointError b (n + 4) ≤ endpointQuadraticBound (n + 4)) :
    ∃ k ∈ Finset.Icc n (n + 3),
      (k : ℤ) ≤ factorialAffineDefect b k := by
  by_contra h
  have hnone : ∀ k : ℕ, k ∈ Finset.Icc n (n + 3) →
      ¬((k : ℤ) ≤ factorialAffineDefect b k) := by
    intro k hk hle
    exact h ⟨k, hk, hle⟩
  have hη0 : factorialAffineDefect b n < (n : ℤ) := by
    exact lt_of_not_ge (hnone n (by simp))
  have hη1 :
      factorialAffineDefect b (n + 1) < ((n + 1 : ℕ) : ℤ) := by
    exact lt_of_not_ge (hnone (n + 1) (by
      simp only [Finset.mem_Icc]
      omega))
  have hη2 :
      factorialAffineDefect b (n + 2) < ((n + 2 : ℕ) : ℤ) := by
    exact lt_of_not_ge (hnone (n + 2) (by
      simp only [Finset.mem_Icc]
      omega))
  have hη3 :
      factorialAffineDefect b (n + 3) < ((n + 3 : ℕ) : ℤ) := by
    exact lt_of_not_ge (hnone (n + 3) (by
      simp only [Finset.mem_Icc]
      omega))
  have hblow := four_step_affine_defect_blowup
    (factorialEndpointError b) (factorialAffineDefect b) n
    (factorialAffineDefect_eq_error_transform b) hePos hη0 hη1 hη2 hη3
  omega

/-- Eventual nonnegative quadratic endpoint control plus eventual sublinear
affine defect forces the approximant to equal `n! - 1` eventually. -/
theorem eventually_factorialEndpointError_eq_zero
    (b : ℕ → ℤ)
    (hbound : ∀ᶠ n in atTop,
      0 ≤ factorialEndpointError b n ∧
        factorialEndpointError b n ≤ endpointQuadraticBound n)
    (hsublinear : ∀ᶠ n in atTop,
      factorialAffineDefect b n < (n : ℤ)) :
    ∀ᶠ n in atTop, factorialEndpointError b n = 0 := by
  rcases (eventually_atTop.1 hbound) with ⟨N₁, hN₁⟩
  rcases (eventually_atTop.1 hsublinear) with ⟨N₂, hN₂⟩
  refine eventually_atTop.2 ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hb0 := hN₁ n hn₁
  have hb4 := hN₁ (n + 4) (by omega)
  have hη0 := hN₂ n hn₂
  have hη1 := hN₂ (n + 1) (by omega)
  have hη2 := hN₂ (n + 2) (by omega)
  have hη3 := hN₂ (n + 3) (by omega)
  by_contra hne
  have hePos : 0 < factorialEndpointError b n := by omega
  have hblow := four_step_affine_defect_blowup
    (factorialEndpointError b) (factorialAffineDefect b) n
    (factorialAffineDefect_eq_error_transform b) hePos hη0 hη1 hη2 hη3
  omega

/-- The sharp two-sided rigidity theorem: inside the absolute quadratic
endpoint window, eventual strict sublinearity of the affine defect forces
eventual equality with `n! - 1`. -/
theorem eventually_factorialEndpointError_eq_zero_of_abs_sublinear
    (b : ℕ → ℤ)
    (hbound : ∀ᶠ n in atTop,
      |factorialEndpointError b n| ≤ endpointQuadraticBound n)
    (hsublinear : ∀ᶠ n in atTop,
      |factorialAffineDefect b n| < (n : ℤ)) :
    ∀ᶠ n in atTop, factorialEndpointError b n = 0 := by
  rcases (eventually_atTop.1 hbound) with ⟨N₁, hN₁⟩
  rcases (eventually_atTop.1 hsublinear) with ⟨N₂, hN₂⟩
  refine eventually_atTop.2 ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  by_contra hne
  have hblow := four_step_abs_affine_defect_blowup
    (factorialEndpointError b) (factorialAffineDefect b) n
    (factorialAffineDefect_eq_error_transform b) hne
    (hN₂ n hn₂)
    (hN₂ (n + 1) (by omega))
    (hN₂ (n + 2) (by omega))
    (hN₂ (n + 3) (by omega))
  have hbound4 := hN₁ (n + 4) (by omega)
  omega

/-- Equivalent eventual equality formulation of the preceding rigidity
theorem. -/
theorem eventually_eq_factorial_sub_one
    (b : ℕ → ℤ)
    (hbound : ∀ᶠ n in atTop,
      0 ≤ factorialEndpointError b n ∧
        factorialEndpointError b n ≤ endpointQuadraticBound n)
    (hsublinear : ∀ᶠ n in atTop,
      factorialAffineDefect b n < (n : ℤ)) :
    b =ᶠ[atTop] fun n => (n.factorial : ℤ) - 1 := by
  filter_upwards [eventually_factorialEndpointError_eq_zero b hbound hsublinear]
    with n hn
  unfold factorialEndpointError at hn
  omega

/-- Cofinal nontrivial downward perturbations inside the quadratic envelope
force cofinally many affine-defect spikes `η_k ≥ k`. -/
theorem cofinal_affineDefect_spikes
    (b : ℕ → ℤ)
    (hbound : ∀ᶠ n in atTop,
      0 ≤ factorialEndpointError b n ∧
        factorialEndpointError b n ≤ endpointQuadraticBound n)
    (hnontrivial : ∀ B : ℕ, ∃ n : ℕ,
      B ≤ n ∧ factorialEndpointError b n ≠ 0) :
    ∀ B : ℕ, ∃ k : ℕ,
      B ≤ k ∧ (k : ℤ) ≤ factorialAffineDefect b k := by
  rcases (eventually_atTop.1 hbound) with ⟨N, hN⟩
  intro B
  obtain ⟨n, hn, hne⟩ := hnontrivial (max B N)
  have hBN : B ≤ n := le_trans (le_max_left _ _) hn
  have hNN : N ≤ n := le_trans (le_max_right _ _) hn
  have hb0 := hN n hNN
  have hb4 := hN (n + 4) (by omega)
  have hePos : 0 < factorialEndpointError b n := by omega
  obtain ⟨k, hkBlock, hkSpike⟩ :=
    exists_affineDefect_spike_in_four_block b n hePos hb4.2
  exact ⟨k, le_trans hBN (Finset.mem_Icc.mp hkBlock).1, hkSpike⟩

end ErdosProblems.Erdos68
