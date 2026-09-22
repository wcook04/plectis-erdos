import Mathlib

/-!
# Coefficients of an integer polynomial from one evaluation

Let `T > 0` be an integer. A nonzero integer polynomial whose coefficients all
have absolute value below `T` cannot vanish at `T`: reducing modulo `T` removes
the constant coefficient, and dividing by `T` shifts the remaining ones. Hence
an integer polynomial whose coefficients have absolute value below `T / 2` is
determined by its value at `T`, and its coefficients are the base-`T` digits
of that value whenever those digits are all below `T / 2`.

The coefficient bound comes from majorants. If `|f_k| ≤ g_k` for every `k`
and the majorant `g` has nonnegative coefficients, the relation survives sums
and products. A determinant is a signed sum of products, so every coefficient
of a determinant is bounded by the value at `1` of the corresponding sum of
majorant products, and hence by `n!` times a product of column bounds.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Polynomial Finset
open scoped BigOperators

/-- `f` is dominated coefficientwise, in absolute value, by `g`. -/
def CoeffMajorant (f g : ℤ[X]) : Prop := ∀ k, |f.coeff k| ≤ g.coeff k

/-- Every coefficient of `g` is nonnegative. -/
def CoeffNonneg (g : ℤ[X]) : Prop := ∀ k, 0 ≤ g.coeff k

theorem CoeffMajorant.nonneg {f g : ℤ[X]} (h : CoeffMajorant f g) : CoeffNonneg g :=
  fun k => (abs_nonneg _).trans (h k)

theorem CoeffNonneg.majorant_self {g : ℤ[X]} (h : CoeffNonneg g) : CoeffMajorant g g :=
  fun k => by rw [abs_of_nonneg (h k)]

theorem CoeffMajorant.add {f₁ g₁ f₂ g₂ : ℤ[X]} (h₁ : CoeffMajorant f₁ g₁)
    (h₂ : CoeffMajorant f₂ g₂) : CoeffMajorant (f₁ + f₂) (g₁ + g₂) := fun k => by
  rw [coeff_add, coeff_add]
  exact (abs_add_le _ _).trans (add_le_add (h₁ k) (h₂ k))

theorem CoeffMajorant.mul {f₁ g₁ f₂ g₂ : ℤ[X]} (h₁ : CoeffMajorant f₁ g₁)
    (h₂ : CoeffMajorant f₂ g₂) : CoeffMajorant (f₁ * f₂) (g₁ * g₂) := fun k => by
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (h₁ _) (h₂ _) (abs_nonneg _) ((abs_nonneg _).trans (h₁ _))

theorem CoeffMajorant.units_smul (u : ℤˣ) {f g : ℤ[X]} (h : CoeffMajorant f g) :
    CoeffMajorant (u • f) g := fun k => by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using h k
  · simpa using h k

theorem CoeffMajorant.C_mul_of_abs_le_one {a : ℤ} (ha : |a| ≤ 1) {f g : ℤ[X]}
    (h : CoeffMajorant f g) : CoeffMajorant (C a * f) g := fun k => by
  rw [coeff_C_mul, abs_mul]
  calc |a| * |f.coeff k| ≤ 1 * |f.coeff k| :=
        mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    _ = |f.coeff k| := one_mul _
    _ ≤ g.coeff k := h k

theorem CoeffNonneg.zero : CoeffNonneg 0 := fun k => by simp

theorem CoeffNonneg.one : CoeffNonneg 1 := fun k => by
  rw [coeff_one]
  split_ifs <;> norm_num

theorem CoeffNonneg.X : CoeffNonneg (X : ℤ[X]) := fun k => by
  rw [coeff_X]
  split_ifs <;> norm_num

theorem CoeffNonneg.C {a : ℤ} (ha : 0 ≤ a) : CoeffNonneg (C a) := fun k => by
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact le_rfl

theorem CoeffNonneg.add {g₁ g₂ : ℤ[X]} (h₁ : CoeffNonneg g₁) (h₂ : CoeffNonneg g₂) :
    CoeffNonneg (g₁ + g₂) := fun k => by
  rw [coeff_add]
  exact add_nonneg (h₁ k) (h₂ k)

theorem CoeffNonneg.mul {g₁ g₂ : ℤ[X]} (h₁ : CoeffNonneg g₁) (h₂ : CoeffNonneg g₂) :
    CoeffNonneg (g₁ * g₂) :=
  (h₁.majorant_self.mul h₂.majorant_self).nonneg

theorem CoeffNonneg.pow {g : ℤ[X]} (h : CoeffNonneg g) (n : ℕ) : CoeffNonneg (g ^ n) := by
  induction n with
  | zero => simpa using CoeffNonneg.one
  | succ n ih => simpa [pow_succ] using ih.mul h

theorem CoeffNonneg.sum {ι : Type*} (s : Finset ι) {g : ι → ℤ[X]}
    (h : ∀ i ∈ s, CoeffNonneg (g i)) : CoeffNonneg (∑ i ∈ s, g i) := fun k => by
  rw [finset_sum_coeff]
  exact Finset.sum_nonneg fun i hi => h i hi k

theorem CoeffNonneg.prod {ι : Type*} (s : Finset ι) {g : ι → ℤ[X]}
    (h : ∀ i ∈ s, CoeffNonneg (g i)) : CoeffNonneg (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffNonneg.one
  | @insert a s ha ih =>
      rw [prod_insert ha]
      exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

theorem CoeffMajorant.sum {ι : Type*} (s : Finset ι) {f g : ι → ℤ[X]}
    (h : ∀ i ∈ s, CoeffMajorant (f i) (g i)) :
    CoeffMajorant (∑ i ∈ s, f i) (∑ i ∈ s, g i) := fun k => by
  rw [finset_sum_coeff, finset_sum_coeff]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => h i hi k)

theorem CoeffMajorant.prod {ι : Type*} (s : Finset ι) {f g : ι → ℤ[X]}
    (h : ∀ i ∈ s, CoeffMajorant (f i) (g i)) :
    CoeffMajorant (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffNonneg.one.majorant_self
  | @insert a s ha ih =>
      rw [prod_insert ha, prod_insert ha]
      exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

theorem CoeffNonneg.eval_one_nonneg {g : ℤ[X]} (hg : CoeffNonneg g) : 0 ≤ g.eval 1 := by
  rw [eval_eq_sum_range]
  exact Finset.sum_nonneg fun i _ => by simpa using hg i

theorem CoeffNonneg.coeff_le_eval_one {g : ℤ[X]} (hg : CoeffNonneg g) (k : ℕ) :
    g.coeff k ≤ g.eval 1 := by
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  by_cases hk : k ≤ g.natDegree
  · exact Finset.single_le_sum (f := fun i => g.coeff i) (fun i _ => hg i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hk)]
    exact Finset.sum_nonneg fun i _ => hg i

/-- Every coefficient of a determinant is bounded by `n!` times a product of
column bounds for the values at `1` of coefficientwise majorants. -/
theorem det_coeff_abs_le_of_majorant {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ[X])
    (hAB : ∀ i j, CoeffMajorant (A i j) (B i j)) (c : Fin n → ℤ)
    (hc : ∀ i j, (B i j).eval 1 ≤ c j) (k : ℕ) :
    |(A.det).coeff k| ≤ (n.factorial : ℤ) * ∏ j, c j := by
  rw [Matrix.det_apply, finset_sum_coeff]
  calc |∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ • ∏ i, A (σ i) i).coeff k|
      ≤ ∑ σ : Equiv.Perm (Fin n), |(Equiv.Perm.sign σ • ∏ i, A (σ i) i).coeff k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Equiv.Perm (Fin n), (∏ i, B (σ i) i).eval 1 := by
        apply Finset.sum_le_sum
        intro σ _
        have hm : CoeffMajorant (Equiv.Perm.sign σ • ∏ i, A (σ i) i) (∏ i, B (σ i) i) :=
          (CoeffMajorant.prod _ fun i _ => hAB (σ i) i).units_smul _
        exact (hm k).trans (hm.nonneg.coeff_le_eval_one k)
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ j, c j := by
        apply Finset.sum_le_sum
        intro σ _
        rw [eval_prod]
        apply Finset.prod_le_prod
        · intro i _
          exact (hAB (σ i) i).nonneg.eval_one_nonneg
        · intro i _
          exact hc (σ i) i
    _ = (n.factorial : ℤ) * ∏ j, c j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]

/-- A polynomial with all coefficients of absolute value below `T > 0` that
vanishes at `T` is zero. -/
theorem eq_zero_of_eval_eq_zero_of_coeff_abs_lt {T : ℤ} (hT : 0 < T) :
    ∀ (n : ℕ) (R : ℤ[X]), R.natDegree ≤ n → (∀ k, |R.coeff k| < T) →
      R.eval T = 0 → R = 0 := by
  intro n
  induction n with
  | zero =>
      intro R hdeg _ heval
      rw [eq_C_of_natDegree_le_zero hdeg] at heval ⊢
      rw [eval_C] at heval
      rw [heval, map_zero]
  | succ n ih =>
      intro R hdeg hcoeff heval
      have hsplit := X_mul_divX_add R
      have heval' : T * (divX R).eval T + R.coeff 0 = 0 := by
        have h := congrArg (eval T) hsplit
        rw [eval_add, eval_mul, eval_X, eval_C] at h
        rw [h]
        exact heval
      have hdvd : T ∣ R.coeff 0 := ⟨-(divX R).eval T, by linarith⟩
      have h0 : R.coeff 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (hcoeff 0)
      have hdiv_eval : (divX R).eval T = 0 := by
        have hmul : T * (divX R).eval T = 0 := by linarith
        exact (mul_eq_zero.mp hmul).resolve_left hT.ne'
      have hdiv : divX R = 0 := by
        apply ih (divX R)
        · rw [natDegree_divX_eq_natDegree_tsub_one]
          omega
        · intro k
          rw [coeff_divX]
          exact hcoeff (k + 1)
        · exact hdiv_eval
      rw [← hsplit, hdiv, h0]
      simp

/-- The base-`T` digit sum below `T ^ L` recovers `V` modulo `T ^ L`. -/
theorem sum_digits_mul_pow (T V : ℕ) :
    ∀ L : ℕ, ∑ i ∈ range L, (V / T ^ i % T) * T ^ i = V % T ^ L := by
  intro L
  induction L with
  | zero => simp [Nat.mod_one]
  | succ L ih =>
      rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]
      ring

/-- Coefficients from one evaluation. If `2|Q_k| < T` for every `k`, the value
`V = Q(T)` lies below `T ^ L`, and every base-`T` digit `d` of `V` below position
`L` satisfies `2d < T`, then the coefficients of `Q` are exactly those digits. -/
theorem coeff_eq_digit_of_eval (Q : ℤ[X]) (T V L : ℕ) (hT : 0 < T)
    (hQ : ∀ k, 2 * |Q.coeff k| < T) (heval : Q.eval (T : ℤ) = V)
    (hV : V < T ^ L) (hdig : ∀ i < L, 2 * (V / T ^ i % T) < T) :
    ∀ k, Q.coeff k = ((V / T ^ k % T : ℕ) : ℤ) := by
  set P : ℤ[X] := ∑ i ∈ range L, C ((V / T ^ i % T : ℕ) : ℤ) * X ^ i with hPdef
  have hPcoeff : ∀ k, P.coeff k = if k < L then ((V / T ^ k % T : ℕ) : ℤ) else 0 := by
    intro k
    rw [hPdef, finset_sum_coeff]
    simp only [coeff_C_mul_X_pow]
    by_cases hk : k < L
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [if_neg (Ne.symm hb)]
      · intro hk'
        exact absurd (Finset.mem_range.mpr hk) hk'
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg]
      intro hki
      have hiL := Finset.mem_range.mp hi
      omega
  have hPeval : P.eval (T : ℤ) = V := by
    rw [hPdef, eval_finset_sum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    have h := sum_digits_mul_pow T V L
    rw [Nat.mod_eq_of_lt hV] at h
    exact_mod_cast h
  have hR : Q - P = 0 := by
    apply eq_zero_of_eval_eq_zero_of_coeff_abs_lt (T := (T : ℤ)) (by exact_mod_cast hT)
      (Q - P).natDegree (Q - P) le_rfl
    · intro k
      rw [coeff_sub, hPcoeff k]
      have hq := hQ k
      split_ifs with hk
      · have hd := hdig k hk
        have hd' : (2 : ℤ) * ((V / T ^ k % T : ℕ) : ℤ) < T := by exact_mod_cast hd
        have hd0 : (0 : ℤ) ≤ ((V / T ^ k % T : ℕ) : ℤ) := Nat.cast_nonneg _
        have hq1 := le_abs_self (Q.coeff k)
        have hq2 := neg_abs_le (Q.coeff k)
        rw [abs_sub_lt_iff]
        constructor <;> linarith
      · rw [sub_zero]
        linarith [abs_nonneg (Q.coeff k)]
    · rw [eval_sub, heval, hPeval, sub_self]
  intro k
  have hk := congrArg (fun R : ℤ[X] => R.coeff k) hR
  simp only [coeff_sub, coeff_zero] at hk
  rw [sub_eq_zero.mp hk, hPcoeff k]
  split_ifs with hkL
  · rfl
  · have hpow : T ^ L ≤ T ^ k := Nat.pow_le_pow_right hT (by omega)
    have hzero : V / T ^ k = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hV hpow)
    rw [hzero, Nat.zero_mod, Nat.cast_zero]

end ErdosProblems.Erdos1049.PaperR20
