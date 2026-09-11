import ErdosProblems.Erdos1049.ZudilinSharpHankelCoefficient

/-!
# Finite coefficient calculus for the all-row producer

Authored against the supplied v4.29.1 source surface and verified locally by
the focused all-row audit on 2026-09-09. No analytic convergence or unbounded
sum is used here.
-/

noncomputable section

namespace ErdosProblems.Erdos1049.AllRow

open scoped BigOperators

abbrev S := PowerSeries ℤ

/-- Explicit constant coefficient of a q-monomial, using only the supplied API. -/
@[simp] theorem constantCoeff_q_pow (e : ℕ) :
    PowerSeries.constantCoeff (PowerSeries.X ^ e : S) = if e = 0 then 1 else 0 := by
  rw [map_pow, PowerSeries.constantCoeff_X]
  by_cases he : e = 0 <;> simp [he]

/-- Equality of all coefficients strictly below `D`. -/
def Agree (D : ℕ) (f g : S) : Prop :=
  ∀ d, d < D → PowerSeries.coeff d f = PowerSeries.coeff d g

namespace Agree

variable {D : ℕ} {f g h f' g' : S}

@[refl] theorem refl (D : ℕ) (f : S) : Agree D f f := fun _ _ => rfl

theorem of_eq (h : f = g) : Agree D f g := by subst g; exact refl _ _

@[symm] theorem symm (h : Agree D f g) : Agree D g f :=
  fun d hd => (h d hd).symm

@[trans] theorem trans (h₁ : Agree D f g) (h₂ : Agree D g h) : Agree D f h :=
  fun d hd => (h₁ d hd).trans (h₂ d hd)

theorem mono {E : ℕ} (h : Agree D f g) (hED : E ≤ D) : Agree E f g :=
  fun d hd => h d (lt_of_lt_of_le hd hED)

theorem add (hf : Agree D f f') (hg : Agree D g g') :
    Agree D (f + g) (f' + g') := by
  intro d hd
  simp only [map_add, hf d hd, hg d hd]

theorem sub (hf : Agree D f f') (hg : Agree D g g') :
    Agree D (f - g) (f' - g') := by
  intro d hd
  simp only [map_sub, hf d hd, hg d hd]

theorem mul (hf : Agree D f f') (hg : Agree D g g') :
    Agree D (f * g) (f' * g') := by
  intro d hd
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = d := Finset.mem_antidiagonal.mp hij
  rw [hf ij.1 (by omega), hg ij.2 (by omega)]

theorem pow (hf : Agree D f f') (k : ℕ) : Agree D (f ^ k) (f' ^ k) := by
  induction k with
  | zero => exact refl _ _
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem sum {ι : Type*} (s : Finset ι) (f g : ι → S)
    (h : ∀ i ∈ s, Agree D (f i) (g i)) :
    Agree D (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro d hd
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi d hd)

/-- Multiplication by a monomial cannot spoil agreement. -/
theorem shift (hf : Agree D f f') (k : ℕ) :
    Agree D (PowerSeries.X ^ k * f) (PowerSeries.X ^ k * f') :=
  (refl _ _).mul hf

/-- Finite source backward differences preserve coefficient agreement. -/
theorem backward (j n : ℕ) (v w : ℕ → S)
    (h : ∀ m, Agree D (v m) (w m)) :
    Agree D (zudilinBackwardShiftApply j n v)
      (zudilinBackwardShiftApply j n w) := by
  unfold zudilinBackwardShiftApply
  apply sum
  intro k _
  exact (refl _ _).mul (h (n - k))

/-- A power above the cut-off is invisible. -/
theorem X_pow_zero (k : ℕ) (hD : D ≤ k) :
    Agree D (PowerSeries.X ^ k : S) 0 := by
  intro d hd
  simp [PowerSeries.coeff_X_pow, show d ≠ k by omega]

/-- Unit inversion is continuous for the finite coefficient filtration. -/
theorem inv (hf : Agree D f g)
    (hf0 : PowerSeries.constantCoeff f = 1)
    (hg0 : PowerSeries.constantCoeff g = 1) :
    Agree D (PowerSeries.invOfUnit f 1) (PowerSeries.invOfUnit g 1) := by
  have h := ((refl D (PowerSeries.invOfUnit f 1)).mul hf).mul
    (refl D (PowerSeries.invOfUnit g 1))
  have hi : PowerSeries.invOfUnit f 1 * f = 1 :=
    PowerSeries.invOfUnit_mul f 1 (by simpa using hf0)
  have hj : g * PowerSeries.invOfUnit g 1 = 1 :=
    PowerSeries.mul_invOfUnit g 1 (by simpa using hg0)
  rw [hi, one_mul, mul_assoc, hj, mul_one] at h
  exact h.symm

end Agree

/-- The finite geometric polynomial, over any commutative ring. -/
def geom {R : Type*} [CommRing R] (B : ℕ) (z : R) : R :=
  ∑ k ∈ Finset.range B, z ^ k

@[simp] theorem geom_zero {R : Type*} [CommRing R] (z : R) : geom 0 z = 0 := by
  simp [geom]

theorem geom_succ {R : Type*} [CommRing R] (B : ℕ) (z : R) :
    geom (B + 1) z = geom B z + z ^ B := by
  simp only [geom, Finset.sum_range_succ]

@[simp] theorem geom_at_zero {R : Type*} [CommRing R] (B : ℕ) (hB : 0 < B) :
    geom B (0 : R) = 1 := by
  cases B with
  | zero => omega
  | succ b =>
      rw [geom, Finset.sum_range_succ']
      simp

theorem map_geom {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (B : ℕ) (z : R) : f (geom B z) = geom B (f z) := by
  simp only [geom, map_sum, map_pow]

theorem one_sub_mul_geom {R : Type*} [CommRing R] (B : ℕ) (z : R) :
    (1 - z) * geom B z = 1 - z ^ B := by
  induction B with
  | zero => simp
  | succ B ih => rw [geom_succ, mul_add, ih, pow_succ]; ring

/-- Replace an inverse geometric factor by an explicitly finite sum. -/
theorem geom_agree_inverse (D B e : ℕ) (he : 0 < e) (hD : D ≤ e * B) :
    Agree D (geom B (PowerSeries.X ^ e : S))
      (PowerSeries.invOfUnit (1 - PowerSeries.X ^ e) 1) := by
  let z : S := PowerSeries.X ^ e
  let U : S := PowerSeries.invOfUnit (1 - z) 1
  have hz0 : PowerSeries.constantCoeff (1 - z) = 1 := by
    simp [z, constantCoeff_q_pow, Nat.ne_of_gt he]
  have hu : U * (1 - z) = 1 :=
    PowerSeries.invOfUnit_mul (1 - z) 1 (by simpa using hz0)
  have hp : Agree D ((1 - z) * geom B z) 1 := by
    rw [one_sub_mul_geom]
    have hz : Agree D (z ^ B) 0 := by
      dsimp [z]
      rw [← pow_mul]
      exact Agree.X_pow_zero (e * B) hD
    simpa using (Agree.refl D (1 : S)).sub hz
  have hm := (Agree.refl D U).mul hp
  rw [← mul_assoc, hu, one_mul, mul_one] at hm
  exact hm

/-- The canonical associated recurrence never brings a state down by more than
one per step. This is independent of any reciprocal hypothesis. -/
theorem associated_above (a : ℕ → ℤ) :
    ∀ j t, j < t → hankelAssociatedCoeff a j t = 0 := by
  intro j
  induction j with
  | zero =>
      intro t ht
      cases t with
      | zero => omega
      | succ t => rfl
  | succ j ih =>
      intro t ht
      cases t with
      | zero => omega
      | succ t =>
          rw [hankelAssociatedCoeff, ih t (by omega), neg_zero]

/-- Only the first `j` positive-index coefficients enter depth `j`. -/
theorem associated_congr (a b : ℕ → ℤ) :
    ∀ j, (∀ s, 0 < s → s ≤ j → a s = b s) →
      ∀ t, hankelAssociatedCoeff a j t = hankelAssociatedCoeff b j t := by
  intro j
  induction j with
  | zero => intro h t; cases t <;> rfl
  | succ j ih =>
      intro h t
      have hsmall : ∀ s, 0 < s → s ≤ j → a s = b s :=
        fun s hs hj => h s hs (by omega)
      cases t with
      | zero =>
          simp only [hankelAssociatedCoeff]
          apply Finset.sum_congr rfl
          intro s hs
          rw [h (s + 1) (by omega) (by
            have := Finset.mem_range.mp hs
            omega), ih hsmall s]
      | succ t => simp only [hankelAssociatedCoeff, ih hsmall t]

/-- Row exponent in a form compatible with the canonical row proposition. -/
def rowExponent (j l : ℕ) : ℕ := j * (j + 1) / 2 + j * l

theorem two_mul_triangle (j : ℕ) : 2 * (j * (j + 1) / 2) = j * (j + 1) := by
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self j).two_dvd

@[simp] theorem rowExponent_zero (l : ℕ) : rowExponent 0 l = 0 := by
  simp [rowExponent]

theorem rowExponent_column (j l : ℕ) :
    rowExponent j (l + 1) = rowExponent j l + j := by
  simp [rowExponent, Nat.mul_add, Nat.add_assoc]

theorem rowExponent_succ (j l : ℕ) :
    rowExponent (j + 1) l = rowExponent j l + j + l + 1 := by
  have h₀ := two_mul_triangle j
  have h₁ := two_mul_triangle (j + 1)
  dsimp [rowExponent]
  nlinarith

theorem rowExponent_ge_depth (j l : ℕ) : j ≤ rowExponent j l := by
  induction j with
  | zero => omega
  | succ j ih => rw [rowExponent_succ]; omega

/-- The source operator commutes with a finite sum of sequences. -/
theorem backward_sum {ι : Type*} (s : Finset ι) (v : ι → ℕ → S) (j n : ℕ) :
    zudilinBackwardShiftApply j n (fun m => ∑ t ∈ s, v t m) =
      ∑ t ∈ s, zudilinBackwardShiftApply j n (v t) := by
  simp only [zudilinBackwardShiftApply, Finset.mul_sum]
  rw [Finset.sum_comm]

end ErdosProblems.Erdos1049.AllRow
