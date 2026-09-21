import ErdosProblems.Erdos243.PaperCompleteR20.CubicRatePositiveRationalProfile

/-!
# Erdős 243: integer extraction at a regular rate, at every exponent

The paper's Lemma `long243:res:extraction` reads: if `λ > 1` and `C n` are
positive integers with `C (n+1) / C n = 1 + λ/n + o(n^{-λ})`, then `λ` is an
integer `d ≥ 2` and `C n = A n(n+1)⋯(n+d-1) + B` eventually, with `A ∈ ℚ_{>0}`
and `B ∈ ℚ`.

The tree proves the `λ = 3` instance (`PaperCompleteR20.CubicRate*`).  The two
clauses it never states are the ones that make `λ` an integer at all.  This
file carries the general statement.

The comparison sequence is `F n = ∏_{1 ≤ k < n} (1 + λ/k)`, whose consecutive
ratio is `1 + λ/n` exactly.  It is the paper's `Γ(n+λ)/Γ(n)` up to the constant
`Γ(1+λ)`, but it needs no gamma-function asymptotics: two elementary
logarithmic inequalities give `c n^λ ≤ F n ≤ n^λ`, and an induction on the
recurrence gives the paper's iterated identity in the form

    `Δ^j F n = λ(λ-1)⋯(λ-j+1) · F n / (n(n+1)⋯(n+j-1))`.

This section of the file sets up that comparison sequence and the
`p`-series tail estimate the residual bound needs.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter Finset
open ErdosProblems.Erdos243.PaperCompleteR20

/-! ## The rising and falling factorials -/

/-- `risingPow d x = x (x+1) ⋯ (x + d - 1)`. -/
def risingPow (d : ℕ) (x : ℝ) : ℝ := ∏ i ∈ Finset.range d, (x + (i : ℝ))

/-- `fallingPow l j = l (l-1) ⋯ (l - j + 1)`. -/
def fallingPow (l : ℝ) (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (l - (i : ℝ))

@[simp] theorem risingPow_zero (x : ℝ) : risingPow 0 x = 1 := by simp [risingPow]

@[simp] theorem fallingPow_zero (l : ℝ) : fallingPow l 0 = 1 := by simp [fallingPow]

theorem risingPow_succ (d : ℕ) (x : ℝ) :
    risingPow (d + 1) x = risingPow d x * (x + (d : ℝ)) := by
  simp [risingPow, Finset.prod_range_succ]

theorem fallingPow_succ (l : ℝ) (j : ℕ) :
    fallingPow l (j + 1) = fallingPow l j * (l - (j : ℝ)) := by
  simp [fallingPow, Finset.prod_range_succ]

theorem risingPow_succ_left (d : ℕ) (x : ℝ) :
    risingPow (d + 1) x = x * risingPow d (x + 1) := by
  unfold risingPow
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  rw [mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by ring

/-- The shift relation that drives the iterated-difference identity. -/
theorem risingPow_shift (d : ℕ) (x : ℝ) :
    x * risingPow d (x + 1) = risingPow d x * (x + (d : ℝ)) := by
  rw [← risingPow_succ_left, risingPow_succ]

theorem risingPow_one_eq_factorial (d : ℕ) :
    risingPow d (1 : ℝ) = ((Nat.factorial d : ℕ) : ℝ) := by
  induction d with
  | zero => simp
  | succ p ihp =>
      rw [risingPow_succ, ihp, Nat.factorial_succ]
      push_cast
      ring

theorem risingPow_pos {x : ℝ} (hx : 0 < x) (d : ℕ) : 0 < risingPow d x := by
  apply Finset.prod_pos
  intro i _
  positivity

theorem pow_le_risingPow {x : ℝ} (hx : 0 ≤ x) (d : ℕ) : x ^ d ≤ risingPow d x := by
  have h : x ^ d = ∏ _i ∈ Finset.range d, x := by simp
  rw [h, risingPow]
  apply Finset.prod_le_prod
  · intro i _; exact hx
  · intro i _; simp

theorem risingPow_le_pow {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    risingPow d x ≤ (x + (d : ℝ)) ^ d := by
  have h : (x + (d : ℝ)) ^ d = ∏ _i ∈ Finset.range d, (x + (d : ℝ)) := by simp
  rw [h, risingPow]
  apply Finset.prod_le_prod
  · intro i _; positivity
  · intro i hi
    simp only [Finset.mem_range] at hi
    have : (i : ℝ) ≤ (d : ℝ) := by exact_mod_cast hi.le
    linarith

/-! ## The comparison sequence -/

/-- `rateModel l n = ∏_{1 ≤ k < n} (1 + l/k)`, the sequence whose consecutive
ratio is exactly `1 + l/n`. -/
def rateModel (l : ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.Ico 1 n, (1 + l / (k : ℝ))

@[simp] theorem rateModel_one (l : ℝ) : rateModel l 1 = 1 := by simp [rateModel]

@[simp] theorem rateModel_zero (l : ℝ) : rateModel l 0 = 1 := by simp [rateModel]

theorem rateModel_succ (l : ℝ) (n : ℕ) :
    rateModel l (n + 1) = rateModel l n * (1 + l / (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [rateModel]
  · simp only [rateModel]
    exact Finset.prod_Ico_succ_top hn (fun k => 1 + l / (k : ℝ))

theorem one_le_rateModel {l : ℝ} (hl : 0 ≤ l) (n : ℕ) : 1 ≤ rateModel l n := by
  calc (1 : ℝ) = ∏ _k ∈ Finset.Ico 1 n, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ ∏ k ∈ Finset.Ico 1 n, (1 + l / (k : ℝ)) := by
        apply Finset.prod_le_prod
        · intro i _; norm_num
        · intro k hk
          simp only [Finset.mem_Ico] at hk
          have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
          have : 0 ≤ l / (k : ℝ) := by positivity
          linarith
    _ = rateModel l n := rfl

theorem rateModel_pos {l : ℝ} (hl : 0 ≤ l) (n : ℕ) : 0 < rateModel l n :=
  lt_of_lt_of_le zero_lt_one (one_le_rateModel hl n)

/-- Bernoulli's inequality makes `F n / n^l` non-increasing, so `F n ≤ n^l`. -/
theorem rateModel_le_rpow {l : ℝ} (hl : 1 ≤ l) :
    ∀ n : ℕ, 1 ≤ n → rateModel l n ≤ (n : ℝ) ^ l := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
      intro _
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [Real.one_rpow]
      · have hm1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hs : (-1 : ℝ) ≤ 1 / (m : ℝ) := by
          have : (0 : ℝ) < 1 / (m : ℝ) := by positivity
          linarith
        have hber : 1 + l * (1 / (m : ℝ)) ≤ (1 + 1 / (m : ℝ)) ^ l :=
          one_add_mul_self_le_rpow_one_add hs hl
        have hsplit : ((m : ℝ) + 1) ^ l = (m : ℝ) ^ l * (1 + 1 / (m : ℝ)) ^ l := by
          rw [← Real.mul_rpow hm1.le (by positivity)]
          congr 1
          field_simp
        have hmodel : rateModel l (m + 1) = rateModel l m * (1 + l / (m : ℝ)) :=
          rateModel_succ l m
        have hfac : (0 : ℝ) < 1 + l / (m : ℝ) := by positivity
        have hih := ih hm
        have hmpos : (0 : ℝ) < (m : ℝ) ^ l := Real.rpow_pos_of_pos hm1 l
        have step : rateModel l m * (1 + l / (m : ℝ)) ≤ (m : ℝ) ^ l * (1 + 1 / (m : ℝ)) ^ l := by
          calc rateModel l m * (1 + l / (m : ℝ))
              ≤ (m : ℝ) ^ l * (1 + l / (m : ℝ)) := by
                exact mul_le_mul_of_nonneg_right hih hfac.le
            _ = (m : ℝ) ^ l * (1 + l * (1 / (m : ℝ))) := by ring_nf
            _ ≤ (m : ℝ) ^ l * (1 + 1 / (m : ℝ)) ^ l := by
                exact mul_le_mul_of_nonneg_left hber hmpos.le
        rw [hmodel]
        push_cast
        rw [hsplit]
        exact step

/-- `log (1 + u) ≤ u` and `log x ≥ 1 - 1/x` together give the reverse
comparison that makes `F n / (n+l)^l` non-decreasing. -/
theorem rpow_shift_le {l : ℝ} (hl : 0 ≤ l) {x : ℝ} (hx : 0 < x) :
    (1 + 1 / (x + l)) ^ l ≤ 1 + l / x := by
  have hxl : (0 : ℝ) < x + l := by linarith
  have hu : (0 : ℝ) < 1 + 1 / (x + l) := by positivity
  have hy : (0 : ℝ) < 1 + l / x := by positivity
  have hlog1 : Real.log (1 + 1 / (x + l)) ≤ 1 / (x + l) := by
    have := Real.log_le_sub_one_of_pos hu
    linarith
  have hlog2 : l / (x + l) ≤ Real.log (1 + l / x) := by
    have hinv : (0 : ℝ) < 1 / (1 + l / x) := by positivity
    have h := Real.log_le_sub_one_of_pos hinv
    rw [one_div, Real.log_inv] at h
    have hval : ((1 : ℝ) + l / x)⁻¹ = x / (x + l) := by
      field_simp
    rw [hval] at h
    have hsub : x / (x + l) - 1 = -(l / (x + l)) := by
      field_simp
      ring
    rw [hsub] at h
    linarith
  rw [Real.rpow_def_of_pos hu]
  have hexp : Real.log (1 + 1 / (x + l)) * l ≤ Real.log (1 + l / x) := by
    have h1 : Real.log (1 + 1 / (x + l)) * l ≤ (1 / (x + l)) * l :=
      mul_le_mul_of_nonneg_right hlog1 hl
    have h2 : (1 / (x + l)) * l = l / (x + l) := by ring
    linarith [hlog2]
  calc Real.exp (Real.log (1 + 1 / (x + l)) * l)
      ≤ Real.exp (Real.log (1 + l / x)) := Real.exp_le_exp.mpr hexp
    _ = 1 + l / x := Real.exp_log hy

/-- The matching lower bound: `(n+l)^l ≤ (1+l)^l · F n`. -/
theorem rpow_le_rateModel {l : ℝ} (hl : 0 ≤ l) :
    ∀ n : ℕ, 1 ≤ n → ((n : ℝ) + l) ^ l ≤ (1 + l) ^ l * rateModel l n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
      intro _
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · have hm1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hml : (0 : ℝ) < (m : ℝ) + l := by linarith
        have hfac : (0 : ℝ) < 1 + l / (m : ℝ) := by positivity
        have hsplit : (((m : ℝ) + 1) + l) ^ l
            = ((m : ℝ) + l) ^ l * (1 + 1 / ((m : ℝ) + l)) ^ l := by
          rw [← Real.mul_rpow hml.le (by positivity)]
          congr 1
          field_simp
          ring
        have hkey := rpow_shift_le hl hm1
        have hih := ih hm
        have hpow : (0 : ℝ) < ((m : ℝ) + l) ^ l := Real.rpow_pos_of_pos hml l
        rw [rateModel_succ]
        push_cast
        rw [hsplit]
        calc ((m : ℝ) + l) ^ l * (1 + 1 / ((m : ℝ) + l)) ^ l
            ≤ ((m : ℝ) + l) ^ l * (1 + l / (m : ℝ)) :=
              mul_le_mul_of_nonneg_left hkey hpow.le
          _ ≤ ((1 + l) ^ l * rateModel l m) * (1 + l / (m : ℝ)) :=
              mul_le_mul_of_nonneg_right hih hfac.le
          _ = (1 + l) ^ l * (rateModel l m * (1 + l / (m : ℝ))) := by ring

theorem rpow_le_const_mul_rateModel {l : ℝ} (hl : 0 ≤ l) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ l ≤ (1 + l) ^ l * rateModel l n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmono : (n : ℝ) ^ l ≤ ((n : ℝ) + l) ^ l := by
    apply Real.rpow_le_rpow (by linarith) (by linarith) hl
  exact hmono.trans (rpow_le_rateModel hl n hn)

/-! ## The iterated difference of the comparison sequence -/

/-- The paper's iterated gamma-ratio identity, in the form the product
definition proves by induction on `j`. -/
theorem iterRealForwardDiff_rateModel (l : ℝ) :
    ∀ (j n : ℕ), 1 ≤ n →
      iterRealForwardDiff j (rateModel l) n
        = fallingPow l j * rateModel l n / risingPow j (n : ℝ) := by
  intro j
  induction j with
  | zero => intro n _; simp
  | succ j ih =>
      intro n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hrj : (0 : ℝ) < risingPow j (n : ℝ) := risingPow_pos hn0 j
      have hrj1 : (0 : ℝ) < risingPow j ((n : ℝ) + 1) := risingPow_pos (by linarith) j
      have hnj : (0 : ℝ) < (n : ℝ) + (j : ℝ) := by positivity
      have hstep : iterRealForwardDiff (j + 1) (rateModel l) n
          = iterRealForwardDiff j (rateModel l) (n + 1)
            - iterRealForwardDiff j (rateModel l) n := rfl
      have h1 := ih (n + 1) (by omega)
      have h2 := ih n hn
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast] at h1
      have hshift := risingPow_shift j (n : ℝ)
      have hbval : risingPow j ((n : ℝ) + 1)
          = risingPow j (n : ℝ) * ((n : ℝ) + (j : ℝ)) / (n : ℝ) := by
        field_simp
        linarith [hshift]
      have hmodel : rateModel l (n + 1) = rateModel l n * (1 + l / (n : ℝ)) :=
        rateModel_succ l n
      rw [hstep, h1, h2, hmodel, hbval, risingPow_succ, fallingPow_succ]
      field_simp
      ring

/-! ## The `p`-series tail -/

/-- One telescoping step, from Bernoulli's inequality for real exponents. -/
theorem rpow_telescope_step {l : ℝ} (hl : 1 < l) {x : ℝ} (hx : 0 < x) :
    (l - 1) * (x + 1) ^ (-l) ≤ x ^ (1 - l) - (x + 1) ^ (1 - l) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hA : (0 : ℝ) < (x + 1) ^ l := Real.rpow_pos_of_pos hx1 l
  have hxl : (0 : ℝ) < x ^ l := Real.rpow_pos_of_pos hx l
  have e1 : (x + 1) ^ (-l) * (x + 1) ^ l = 1 := by
    rw [← Real.rpow_add hx1]; simp
  have e2 : (x + 1) ^ (1 - l) * (x + 1) ^ l = x + 1 := by
    rw [← Real.rpow_add hx1]
    norm_num
  have e3 : x ^ (1 - l) * (x + 1) ^ l = x * ((x + 1) ^ l / x ^ l) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp
  have hs : (-1 : ℝ) ≤ 1 / x := by
    have : (0 : ℝ) < 1 / x := by positivity
    linarith
  have hber : 1 + l * (1 / x) ≤ (1 + 1 / x) ^ l :=
    one_add_mul_self_le_rpow_one_add hs hl.le
  have hdiv : (1 + 1 / x) ^ l = (x + 1) ^ l / x ^ l := by
    have h1 : (1 : ℝ) + 1 / x = (x + 1) / x := by field_simp
    rw [h1, Real.div_rpow hx1.le hx.le]
  have hkey : x + l ≤ x * ((x + 1) ^ l / x ^ l) := by
    rw [← hdiv]
    have : x + l = x * (1 + l * (1 / x)) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hber hx.le
  have hl1 : (l - 1) * (x + 1) ^ (-l) * (x + 1) ^ l = l - 1 := by
    rw [mul_assoc, e1, mul_one]
  have hr1 : (x ^ (1 - l) - (x + 1) ^ (1 - l)) * (x + 1) ^ l
      = x * ((x + 1) ^ l / x ^ l) - (x + 1) := by
    rw [sub_mul, e2, e3]
  refine le_of_mul_le_mul_right ?_ hA
  rw [hl1, hr1]
  linarith

/-- The tail of the real-exponent `p`-series, with an explicit constant. -/
theorem rpow_neg_tail_le {l : ℝ} (hl : 1 < l) {n : ℕ} (hn : 1 ≤ n) :
    ∑' m : ℕ, (((n + m : ℕ) : ℝ)) ^ (-l) ≤ (1 + 1 / (l - 1)) * (n : ℝ) ^ (1 - l) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hl1 : (0 : ℝ) < l - 1 := by linarith
  have hnl : (0 : ℝ) < (n : ℝ) ^ (1 - l) := Real.rpow_pos_of_pos hn0 _
  apply Real.tsum_le_of_sum_range_le
  · intro m; positivity
  intro J
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hhead : (((n + 0 : ℕ) : ℝ)) ^ (-l) ≤ (n : ℝ) ^ (1 - l) := by
    simp only [Nat.add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have htail : (∑ m ∈ Finset.range J', (((n + (m + 1) : ℕ) : ℝ)) ^ (-l))
      ≤ (1 / (l - 1)) * (n : ℝ) ^ (1 - l) := by
    have hbound : ∀ m ∈ Finset.range J',
        (((n + (m + 1) : ℕ) : ℝ)) ^ (-l)
          ≤ (1 / (l - 1)) * ((((n + m : ℕ) : ℝ)) ^ (1 - l)
              - (((n + (m + 1) : ℕ) : ℝ)) ^ (1 - l)) := by
      intro m _
      have hx : (0 : ℝ) < ((n + m : ℕ) : ℝ) := by
        have : 0 < n + m := by omega
        exact_mod_cast this
      have hcast : (((n + (m + 1) : ℕ) : ℝ)) = (((n + m : ℕ) : ℝ)) + 1 := by
        push_cast; ring
      rw [hcast]
      have key := rpow_telescope_step hl hx
      have hstep : (1 / (l - 1)) * ((l - 1) * ((((n + m : ℕ) : ℝ)) + 1) ^ (-l))
          ≤ (1 / (l - 1)) * ((((n + m : ℕ) : ℝ)) ^ (1 - l)
              - ((((n + m : ℕ) : ℝ)) + 1) ^ (1 - l)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
      calc ((((n + m : ℕ) : ℝ)) + 1) ^ (-l)
          = (1 / (l - 1)) * ((l - 1) * ((((n + m : ℕ) : ℝ)) + 1) ^ (-l)) := by
            field_simp
        _ ≤ _ := hstep
    calc (∑ m ∈ Finset.range J', (((n + (m + 1) : ℕ) : ℝ)) ^ (-l))
        ≤ ∑ m ∈ Finset.range J', (1 / (l - 1)) * ((((n + m : ℕ) : ℝ)) ^ (1 - l)
            - (((n + (m + 1) : ℕ) : ℝ)) ^ (1 - l)) := Finset.sum_le_sum hbound
      _ = (1 / (l - 1)) * ∑ m ∈ Finset.range J', ((((n + m : ℕ) : ℝ)) ^ (1 - l)
            - (((n + (m + 1) : ℕ) : ℝ)) ^ (1 - l)) := by rw [Finset.mul_sum]
      _ = (1 / (l - 1)) * ((((n + 0 : ℕ) : ℝ)) ^ (1 - l)
            - (((n + J' : ℕ) : ℝ)) ^ (1 - l)) := by
            congr 1
            exact Finset.sum_range_sub' (fun m => (((n + m : ℕ) : ℝ)) ^ (1 - l)) J'
      _ ≤ (1 / (l - 1)) * (n : ℝ) ^ (1 - l) := by
            have hpos : (0 : ℝ) ≤ (((n + J' : ℕ) : ℝ)) ^ (1 - l) := by positivity
            have : (0 : ℝ) < 1 / (l - 1) := by positivity
            simp only [Nat.add_zero]
            nlinarith
  have : (1 + 1 / (l - 1)) * (n : ℝ) ^ (1 - l)
      = (n : ℝ) ^ (1 - l) + (1 / (l - 1)) * (n : ℝ) ^ (1 - l) := by ring
  rw [this]
  linarith

/-! ## The rate hypothesis and the normalised quotient -/

/-- The literal error in `C (n+1) / C n = 1 + l/n + ε_n`. -/
def rateError (l : ℝ) (C : ℕ → ℝ) (n : ℕ) : ℝ := C (n + 1) / C n - (1 + l / (n : ℝ))

/-- The paper's `z_n = C_n / F_n`. -/
def rateQuotient (l : ℝ) (C : ℕ → ℝ) (n : ℕ) : ℝ := C n / rateModel l n

/-- The relative increment of `z`. -/
def rateRelError (l : ℝ) (C : ℕ → ℝ) (n : ℕ) : ℝ := rateError l C n / (1 + l / (n : ℝ))

theorem rateQuotient_succ {l : ℝ} (hl : 0 ≤ l) (C : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hC : C n ≠ 0) :
    rateQuotient l C (n + 1) = rateQuotient l C n * (1 + rateRelError l C n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfac : (0 : ℝ) < 1 + l / (n : ℝ) := by positivity
  have hF : 0 < rateModel l n := rateModel_pos hl n
  simp only [rateQuotient, rateRelError, rateError, rateModel_succ]
  field_simp
  ring

theorem abs_rateRelError_le {l : ℝ} (hl : 0 ≤ l) (C : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |rateRelError l C n| ≤ |rateError l C n| := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfac : (1 : ℝ) ≤ 1 + l / (n : ℝ) := by
    have : 0 ≤ l / (n : ℝ) := by positivity
    linarith
  rw [rateRelError, abs_div, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + l / (n:ℝ))]
  exact div_le_self (abs_nonneg _) hfac

theorem rateError_eq_scaled {l : ℝ} (C : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    rateError l C n = ((n : ℝ) ^ l * rateError l C n) * ((n : ℝ) ^ (-l)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h : (n : ℝ) ^ l * (n : ℝ) ^ (-l) = 1 := by
    rw [← Real.rpow_add hn0]; simp
  calc rateError l C n = rateError l C n * ((n : ℝ) ^ l * (n : ℝ) ^ (-l)) := by rw [h, mul_one]
    _ = ((n : ℝ) ^ l * rateError l C n) * ((n : ℝ) ^ (-l)) := by ring

/-! ## Two general analytic steps -/

/-- A sequence with summable relative increments is bounded on its tail. -/
theorem abs_le_of_relative_increment (x e : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ n, N ≤ n → x (n + 1) = x n * (1 + e n))
    (he : Summable fun n => |e n|) :
    ∃ M : ℝ, ∀ n, N ≤ n → |x n| ≤ M := by
  have heN : Summable fun k : ℕ => |e (N + k)| :=
    he.comp_injective fun _ _ h => Nat.add_left_cancel h
  have hSle : ∀ j : ℕ, (∑ i ∈ Finset.range j, |e (N + i)|) ≤ ∑' k : ℕ, |e (N + k)| :=
    fun j => heN.sum_le_tsum _ (fun i _ => abs_nonneg _)
  have key : ∀ j : ℕ,
      |x (N + j)| ≤ |x N| * Real.exp (∑ i ∈ Finset.range j, |e (N + i)|) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hj := hstep (N + j) (Nat.le_add_right N j)
        have h1 : |x (N + (j + 1))| = |x (N + j)| * |1 + e (N + j)| := by
          rw [show N + (j + 1) = (N + j) + 1 by omega, hj, abs_mul]
        have h2 : |1 + e (N + j)| ≤ Real.exp |e (N + j)| := by
          have hexp := Real.add_one_le_exp |e (N + j)|
          have habs : |1 + e (N + j)| ≤ 1 + |e (N + j)| := by
            rw [abs_le]
            constructor <;>
              [linarith [neg_abs_le (e (N + j)), abs_nonneg (e (N + j))];
               linarith [le_abs_self (e (N + j))]]
          linarith
        calc |x (N + (j + 1))| = |x (N + j)| * |1 + e (N + j)| := h1
          _ ≤ (|x N| * Real.exp (∑ i ∈ Finset.range j, |e (N + i)|)) * Real.exp |e (N + j)| := by
              exact mul_le_mul ih h2 (abs_nonneg _) (by positivity)
          _ = |x N| * Real.exp (∑ i ∈ Finset.range (j + 1), |e (N + i)|) := by
              rw [Finset.sum_range_succ, Real.exp_add]; ring
  refine ⟨|x N| * Real.exp (∑' k : ℕ, |e (N + k)|), ?_⟩
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  calc |x (N + j)| ≤ |x N| * Real.exp (∑ i ∈ Finset.range j, |e (N + i)|) := key j
    _ ≤ |x N| * Real.exp (∑' k : ℕ, |e (N + k)|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hSle j)) (abs_nonneg _)

/-- Increments of size `M |w n| n^{-l}` with `w → 0` give a limit reached with
error `o(n^{1-l})`.  This is the quantitative summation the paper performs on
the logarithmic product. -/
theorem exists_limit_rpow_scaled_tail {l : ℝ} (hl : 1 < l) (x w : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (N : ℕ)
    (hbd : ∀ n, N ≤ n → 1 ≤ n → |x (n + 1) - x n| ≤ M * |w n| * ((n : ℝ) ^ (-l)))
    (hw : Tendsto w atTop (nhds 0)) :
    ∃ K : ℝ, Tendsto (fun n : ℕ => (n : ℝ) ^ (l - 1) * (x n - K)) atTop (nhds 0) := by
  have hl1 : (0 : ℝ) < l - 1 := by linarith
  have hps : Summable fun n : ℕ => (n : ℝ) ^ (-l) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hwabs : Tendsto (fun n => |w n|) atTop (nhds 0) := by simpa using hw.abs
  have hw1 : ∀ᶠ n : ℕ in atTop, |w n| ≤ 1 :=
    ((tendsto_order.1 hwabs).2 1 (by norm_num)).mono fun _ h => h.le
  have hdist : ∀ᶠ n : ℕ in atTop, dist (x n) (x (n + 1)) ≤ M * ((n : ℝ) ^ (-l)) := by
    filter_upwards [hw1, eventually_ge_atTop N, eventually_ge_atTop 1] with n hwn hnN hn1
    rw [Real.dist_eq, abs_sub_comm]
    have h := hbd n hnN hn1
    have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-l) := Real.rpow_nonneg (by positivity) _
    have hstep : M * |w n| * ((n : ℝ) ^ (-l)) ≤ M * 1 * ((n : ℝ) ^ (-l)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwn hM) hpow
    calc |x (n + 1) - x n| ≤ M * |w n| * ((n : ℝ) ^ (-l)) := h
      _ ≤ M * 1 * ((n : ℝ) ^ (-l)) := hstep
      _ = M * ((n : ℝ) ^ (-l)) := by ring
  have hsum : Summable fun n : ℕ => dist (x n) (x (n + 1)) :=
    Summable.of_norm_bounded_eventually_nat (hps.mul_left M) (by
      filter_upwards [hdist] with n hn
      simpa [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hn)
  obtain ⟨K, hK⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
  refine ⟨K, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  set c : ℝ := M * (1 + 1 / (l - 1)) + 1 with hcdef
  have hcpos : (0 : ℝ) < c := by positivity
  have hwsmall : ∀ᶠ n : ℕ in atTop, |w n| ≤ ε / c :=
    ((tendsto_order.1 hwabs).2 (ε / c) (by positivity)).mono fun _ h => h.le
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 hwsmall
  refine ⟨max (max N₃ N) 1, fun n hn => ?_⟩
  have hn3 : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN : N ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hpoint : ∀ m : ℕ,
      dist (x (n + m)) (x (n + m + 1)) ≤ (M * (ε / c)) * (((n + m : ℕ) : ℝ) ^ (-l)) := by
    intro m
    have hmN : N ≤ n + m := le_trans hnN (Nat.le_add_right n m)
    have hm3 : N₃ ≤ n + m := le_trans hn3 (Nat.le_add_right n m)
    have hm1 : 1 ≤ n + m := le_trans hn1 (Nat.le_add_right n m)
    have hmpos : (0 : ℝ) < ((n + m : ℕ) : ℝ) := by exact_mod_cast hm1
    have h := hbd (n + m) hmN hm1
    have hwm := hN₃ (n + m) hm3
    rw [Real.dist_eq, abs_sub_comm]
    calc |x (n + m + 1) - x (n + m)|
        ≤ M * |w (n + m)| * (((n + m : ℕ) : ℝ) ^ (-l)) := h
      _ ≤ (M * (ε / c)) * (((n + m : ℕ) : ℝ) ^ (-l)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwm hM)
            (Real.rpow_nonneg hmpos.le _)
  have hshift : Summable fun m : ℕ => dist (x (n + m)) (x (n + m + 1)) :=
    hsum.comp_injective fun _ _ h => Nat.add_left_cancel h
  have hmajsum : Summable fun m : ℕ => (M * (ε / c)) * (((n + m : ℕ) : ℝ) ^ (-l)) :=
    (hps.comp_injective fun _ _ h => Nat.add_left_cancel h).mul_left _
  have htail : dist (x n) K ≤ ∑' m : ℕ, dist (x (n + m)) (x (n + m + 1)) :=
    dist_le_tsum_dist_of_tendsto hsum hK n
  have hmaj : (∑' m : ℕ, dist (x (n + m)) (x (n + m + 1)))
      ≤ (M * (ε / c)) * ((1 + 1 / (l - 1)) * (n : ℝ) ^ (1 - l)) := by
    calc (∑' m : ℕ, dist (x (n + m)) (x (n + m + 1)))
        ≤ ∑' m : ℕ, (M * (ε / c)) * (((n + m : ℕ) : ℝ) ^ (-l)) :=
          Summable.tsum_le_tsum hpoint hshift hmajsum
      _ = (M * (ε / c)) * ∑' m : ℕ, (((n + m : ℕ) : ℝ) ^ (-l)) := tsum_mul_left
      _ ≤ (M * (ε / c)) * ((1 + 1 / (l - 1)) * (n : ℝ) ^ (1 - l)) :=
          mul_le_mul_of_nonneg_left (rpow_neg_tail_le hl hn1) (by positivity)
  rw [Real.dist_eq] at htail
  rw [Real.dist_eq, sub_zero, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hnpos.le (l - 1))]
  have hrp : (n : ℝ) ^ (l - 1) * (n : ℝ) ^ (1 - l) = 1 := by
    rw [← Real.rpow_add hnpos]; norm_num
  have hxK : |x n - K| ≤ (M * (ε / c)) * ((1 + 1 / (l - 1)) * (n : ℝ) ^ (1 - l)) :=
    le_trans htail hmaj
  have hdivlt : M * (1 + 1 / (l - 1)) / c < 1 := by
    rw [div_lt_one hcpos]; linarith
  calc (n : ℝ) ^ (l - 1) * |x n - K|
      ≤ (n : ℝ) ^ (l - 1) * ((M * (ε / c)) * ((1 + 1 / (l - 1)) * (n : ℝ) ^ (1 - l))) :=
        mul_le_mul_of_nonneg_left hxK (Real.rpow_nonneg hnpos.le _)
    _ = (M * (1 + 1 / (l - 1))) * (ε / c) * ((n : ℝ) ^ (l - 1) * (n : ℝ) ^ (1 - l)) := by
        ring
    _ = (M * (1 + 1 / (l - 1)) / c) * ε := by rw [hrp]; ring
    _ < 1 * ε := mul_lt_mul_of_pos_right hdivlt hε
    _ = ε := one_mul ε

/-! ## The residual decomposition -/

/-- The paper's `δ_n = C_n - K F_n = o(n)`. -/
theorem exists_residual_decomposition {l : ℝ} (hl : 1 < l) (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n)
      atTop (nhds 0)) :
    ∃ K : ℝ, ∃ r : ℕ → ℝ,
      (fun n : ℕ => (C n : ℝ)) = (fun n : ℕ => K * rateModel l n + r n) ∧
      Tendsto (fun n : ℕ => r n / (n : ℝ)) atTop (nhds 0) := by
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have hl1 : (1 : ℝ) ≤ l := by linarith
  set D : ℕ → ℝ := fun n => (C n : ℝ) with hD
  have hDne : ∀ n, D n ≠ 0 := fun n => by
    simp only [hD]
    exact_mod_cast (ne_of_gt (hpos n))
  set w : ℕ → ℝ := fun n : ℕ => (n : ℝ) ^ l * rateError l D n with hw
  have hwtend : Tendsto w atTop (nhds 0) := hratio
  have hwabs : Tendsto (fun n => |w n|) atTop (nhds 0) := by simpa using hwtend.abs
  have hw1 : ∀ᶠ n : ℕ in atTop, |w n| ≤ 1 :=
    ((tendsto_order.1 hwabs).2 1 (by norm_num)).mono fun _ h => h.le
  have herr : ∀ n : ℕ, 1 ≤ n → |rateRelError l D n| ≤ |w n| * ((n : ℝ) ^ (-l)) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 := abs_rateRelError_le hl0 D hn
    have h2 := rateError_eq_scaled (l := l) D hn
    rw [h2, abs_mul, abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at h1
    exact h1
  have hsummable : Summable fun n : ℕ => |rateRelError l D n| := by
    apply Summable.of_norm_bounded_eventually_nat
      (Real.summable_nat_rpow.mpr (show -l < -1 by linarith))
    filter_upwards [hw1, eventually_ge_atTop 1] with n hwn hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-l) := Real.rpow_nonneg hnpos.le _
    have := herr n hn
    have hle : |w n| * ((n : ℝ) ^ (-l)) ≤ 1 * ((n : ℝ) ^ (-l)) :=
      mul_le_mul_of_nonneg_right hwn hpow
    simp only [Real.norm_eq_abs, abs_abs]
    linarith
  obtain ⟨M, hM⟩ := abs_le_of_relative_increment (rateQuotient l D) (rateRelError l D) 1
    (fun n hn => rateQuotient_succ hl0 D hn (hDne n)) hsummable
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 1 le_rfl)
  obtain ⟨K, hK⟩ := exists_limit_rpow_scaled_tail hl (rateQuotient l D) w M hM0 1
    (by
      intro n _ hn1
      have hstep := rateQuotient_succ hl0 D hn1 (hDne n)
      have hdiff : rateQuotient l D (n + 1) - rateQuotient l D n
          = rateQuotient l D n * rateRelError l D n := by rw [hstep]; ring
      rw [hdiff, abs_mul]
      have hq := hM n hn1
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-l) := Real.rpow_nonneg hnpos.le _
      calc |rateQuotient l D n| * |rateRelError l D n|
          ≤ M * (|w n| * ((n : ℝ) ^ (-l))) :=
            mul_le_mul hq (herr n hn1) (abs_nonneg _) (le_trans (abs_nonneg _) hq)
        _ = M * |w n| * ((n : ℝ) ^ (-l)) := by ring)
    hwtend
  refine ⟨K, fun n : ℕ => (C n : ℝ) - K * rateModel l n, ?_, ?_⟩
  · funext n; ring
  · have hbound : ∀ᶠ n : ℕ in atTop,
        ‖((C n : ℝ) - K * rateModel l n) / (n : ℝ)‖
          ≤ |(n : ℝ) ^ (l - 1) * (rateQuotient l D n - K)| := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hF : 0 < rateModel l n := rateModel_pos hl0 n
      have hFle : rateModel l n ≤ (n : ℝ) ^ l := rateModel_le_rpow hl1 n hn
      have hres : (C n : ℝ) - K * rateModel l n
          = rateModel l n * (rateQuotient l D n - K) := by
        simp only [rateQuotient, hD]
        field_simp
      have hsplit : (n : ℝ) ^ (l - 1) = (n : ℝ) ^ l / (n : ℝ) := by
        rw [Real.rpow_sub hnpos, Real.rpow_one]
      rw [Real.norm_eq_abs, hres, abs_div, abs_mul, abs_of_nonneg hF.le,
        abs_of_nonneg hnpos.le, abs_mul, abs_of_nonneg (Real.rpow_nonneg hnpos.le _), hsplit]
      rw [div_le_iff₀ hnpos] at *
      calc rateModel l n * |rateQuotient l D n - K|
          ≤ (n : ℝ) ^ l * |rateQuotient l D n - K| :=
            mul_le_mul_of_nonneg_right hFle (abs_nonneg _)
        _ = (n : ℝ) ^ l / (n : ℝ) * |rateQuotient l D n - K| * (n : ℝ) := by
            field_simp
    have hKabs : Tendsto
        (fun n : ℕ => |(n : ℝ) ^ (l - 1) * (rateQuotient l D n - K)|) atTop (nhds 0) := by
      simpa using hK.abs
    exact squeeze_zero_norm' hbound hKabs

/-! ## Descent through the difference tower -/

theorem iterRealForwardDiff_succ' (k : ℕ) (u : ℕ → ℝ) :
    iterRealForwardDiff (k + 1) u = iterRealForwardDiff k (realForwardDiff u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show realForwardDiff (iterRealForwardDiff (k + 1) u)
        = iterRealForwardDiff (k + 1) (realForwardDiff u)
      rw [ih]
      rfl

theorem iterRealForwardDiff_tendsto_zero_of_first
    {u : ℕ → ℝ} (hu : Tendsto (realForwardDiff u) atTop (nhds 0)) (j : ℕ) :
    Tendsto (iterRealForwardDiff (j + 1) u) atTop (nhds 0) := by
  rw [iterRealForwardDiff_succ']
  exact iterRealForwardDiff_tendsto_zero hu j

theorem realForwardDiff_eventually_zero_of_iter
    {u : ℕ → ℝ} (hu : Tendsto (realForwardDiff u) atTop (nhds 0)) :
    ∀ i : ℕ, (∀ᶠ n in atTop, iterRealForwardDiff (i + 1) u n = 0) →
      (∀ᶠ n in atTop, realForwardDiff u n = 0) := by
  intro i
  induction i with
  | zero => intro h; simpa using h
  | succ i ih =>
      intro h
      apply ih
      refine eventually_zero_of_tendsto_zero_of_forwardDiff_eventually_zero
        (iterRealForwardDiff (i + 1) u) (iterRealForwardDiff_tendsto_zero_of_first hu i) ?_
      simpa using h

/-! ## The comparison sequence outgrows every lower rising factorial -/

theorem rateModel_div_risingPow_atTop {l : ℝ} (hl : 1 ≤ l) {m : ℕ} (hm : (m : ℝ) < l) :
    Tendsto (fun n : ℕ => rateModel l n / risingPow m (n : ℝ)) atTop atTop := by
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have hy : (0 : ℝ) < l - (m : ℝ) := by linarith
  have hc0 : (0 : ℝ) < 1 / ((1 + l) ^ l * 2 ^ m) := by
    have h1 : (0 : ℝ) < (1 + l) ^ l := Real.rpow_pos_of_pos (by linarith) l
    positivity
  have hrp : Tendsto (fun n : ℕ => (n : ℝ) ^ (l - (m : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop hy).comp tendsto_natCast_atTop_atTop
  have hmaj : Tendsto
      (fun n : ℕ => (1 / ((1 + l) ^ l * 2 ^ m)) * (n : ℝ) ^ (l - (m : ℝ))) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc0 hrp
  apply tendsto_atTop_mono' atTop _ hmaj
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop m] with n hn hnm
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnm' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
  have hR : (0 : ℝ) < risingPow m (n : ℝ) := risingPow_pos hn0 m
  have hRle : risingPow m (n : ℝ) ≤ (2 * (n : ℝ)) ^ m := by
    refine le_trans (risingPow_le_pow hn0.le m) ?_
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hFlow : (n : ℝ) ^ l / (1 + l) ^ l ≤ rateModel l n := by
    have h := rpow_le_const_mul_rateModel hl0 n hn
    have h1 : (0 : ℝ) < (1 + l) ^ l := Real.rpow_pos_of_pos (by linarith) l
    rw [div_le_iff₀ h1]
    linarith [h]
  have hsplit : (n : ℝ) ^ (l - (m : ℝ)) * ((n : ℝ) ^ m) = (n : ℝ) ^ l := by
    rw [← Real.rpow_natCast (n : ℝ) m, ← Real.rpow_add hn0]
    congr 1
    ring
  have h1 : (0 : ℝ) < (1 + l) ^ l := Real.rpow_pos_of_pos (by linarith) l
  rw [le_div_iff₀ hR]
  calc (1 / ((1 + l) ^ l * 2 ^ m)) * (n : ℝ) ^ (l - (m : ℝ)) * risingPow m (n : ℝ)
      ≤ (1 / ((1 + l) ^ l * 2 ^ m)) * (n : ℝ) ^ (l - (m : ℝ)) * (2 * (n : ℝ)) ^ m := by
        apply mul_le_mul_of_nonneg_left hRle
        have : (0 : ℝ) ≤ (n : ℝ) ^ (l - (m : ℝ)) := Real.rpow_nonneg hn0.le _
        positivity
    _ = (n : ℝ) ^ (l - (m : ℝ)) * ((n : ℝ) ^ m) / (1 + l) ^ l := by
        rw [mul_pow]
        field_simp
        all_goals ring
    _ = (n : ℝ) ^ l / (1 + l) ^ l := by rw [hsplit]
    _ ≤ rateModel l n := hFlow

/-- Above the exponent, the iterated difference of the comparison sequence
vanishes in the limit: this is the paper's `Δ^j F_n = O(n^{λ-j})`. -/
theorem rateModel_iterDiff_tendsto_zero {l : ℝ} (hl : 1 ≤ l) (j : ℕ) (hj : l < (j : ℝ)) :
    Tendsto (fun n : ℕ => fallingPow l j * rateModel l n / risingPow j (n : ℝ))
      atTop (nhds 0) := by
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have hy : (0 : ℝ) < (j : ℝ) - l := by linarith
  have hrp : Tendsto (fun n : ℕ => (n : ℝ) ^ (l - (j : ℝ))) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, neg_sub] using h
  have hmaj : Tendsto (fun n : ℕ => |fallingPow l j| * (n : ℝ) ^ (l - (j : ℝ)))
      atTop (nhds 0) := by
    simpa using hrp.const_mul |fallingPow l j|
  apply squeeze_zero_norm' _ hmaj
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hF : 0 < rateModel l n := rateModel_pos hl0 n
  have hFle : rateModel l n ≤ (n : ℝ) ^ l := rateModel_le_rpow hl n hn
  have hR : (0 : ℝ) < risingPow j (n : ℝ) := risingPow_pos hn0 j
  have hRge : (n : ℝ) ^ j ≤ risingPow j (n : ℝ) := pow_le_risingPow hn0.le j
  have hsplit : (n : ℝ) ^ (l - (j : ℝ)) * ((n : ℝ) ^ j) = (n : ℝ) ^ l := by
    rw [← Real.rpow_natCast (n : ℝ) j, ← Real.rpow_add hn0]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hF, abs_of_pos hR, div_le_iff₀ hR]
  calc |fallingPow l j| * rateModel l n
      ≤ |fallingPow l j| * (n : ℝ) ^ l :=
        mul_le_mul_of_nonneg_left hFle (abs_nonneg _)
    _ = |fallingPow l j| * ((n : ℝ) ^ (l - (j : ℝ)) * ((n : ℝ) ^ j)) := by rw [hsplit]
    _ ≤ |fallingPow l j| * ((n : ℝ) ^ (l - (j : ℝ)) * risingPow j (n : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left hRge (Real.rpow_nonneg hn0.le _)
    _ = |fallingPow l j| * (n : ℝ) ^ (l - (j : ℝ)) * risingPow j (n : ℝ) := by ring

/-! ## The residual difference -/

theorem residual_forwardDiff_tendsto_zero {l : ℝ} (hl : 1 < l) (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hpos : ∀ n, 0 < C n)
    (hdecomp : (fun n : ℕ => (C n : ℝ)) = fun n : ℕ => K * rateModel l n + r n)
    (hsub : Tendsto (fun n : ℕ => r n / (n : ℝ)) atTop (nhds 0))
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n)
      atTop (nhds 0)) :
    Tendsto (realForwardDiff r) atTop (nhds 0) := by
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have hl1 : (1 : ℝ) ≤ l := by linarith
  set D : ℕ → ℝ := fun n => (C n : ℝ) with hD
  have hDne : ∀ n, D n ≠ 0 := fun n => by
    simp only [hD]
    exact_mod_cast (ne_of_gt (hpos n))
  have hr : ∀ k : ℕ, r k = D k - K * rateModel l k := by
    intro k
    have h := congrFun hdecomp k
    simp only [hD] at h ⊢
    linarith
  have hid : ∀ n : ℕ, 1 ≤ n →
      realForwardDiff r n = (D n * ((n : ℝ) ^ (-l))) * ((n : ℝ) ^ l * rateError l D n)
        + l * (r n / (n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hscale : (D n * ((n : ℝ) ^ (-l))) * ((n : ℝ) ^ l * rateError l D n)
        = rateError l D n * D n := by
      have h : (n : ℝ) ^ (-l) * (n : ℝ) ^ l = 1 := by
        rw [← Real.rpow_add hn0]; simp
      calc (D n * ((n : ℝ) ^ (-l))) * ((n : ℝ) ^ l * rateError l D n)
          = (D n * rateError l D n) * ((n : ℝ) ^ (-l) * (n : ℝ) ^ l) := by ring
        _ = rateError l D n * D n := by rw [h]; ring
    rw [hscale]
    have hDn : D n ≠ 0 := hDne n
    simp only [realForwardDiff, rateError, hr, rateModel_succ]
    field_simp
    all_goals ring
  have hbdd : ∀ᶠ n : ℕ in atTop, |D n * ((n : ℝ) ^ (-l))| ≤ |K| + 1 := by
    have hsmall : ∀ᶠ n : ℕ in atTop, |r n / (n : ℝ)| ≤ 1 := by
      have habs : Tendsto (fun n : ℕ => |r n / (n : ℝ)|) atTop (nhds 0) := by
        simpa using hsub.abs
      exact ((tendsto_order.1 habs).2 1 (by norm_num)).mono fun _ h => h.le
    filter_upwards [hsmall, eventually_ge_atTop 1] with n hrn hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpowpos : (0 : ℝ) < (n : ℝ) ^ l := Real.rpow_pos_of_pos hn0 l
    have hneg : (n : ℝ) ^ (-l) = ((n : ℝ) ^ l)⁻¹ := Real.rpow_neg hn0.le l
    have hF : 0 < rateModel l n := rateModel_pos hl0 n
    have hFle : rateModel l n ≤ (n : ℝ) ^ l := rateModel_le_rpow hl1 n hn
    have hnle : (n : ℝ) ≤ (n : ℝ) ^ l := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ l := Real.rpow_le_rpow_of_exponent_le hn1 hl1
    have hDval : D n = K * rateModel l n + r n := congrFun hdecomp n
    have hsplit : D n * ((n : ℝ) ^ (-l))
        = K * (rateModel l n / (n : ℝ) ^ l) + (r n / (n : ℝ) ^ l) := by
      rw [hDval, hneg]; field_simp; all_goals ring
    have h1 : |K * (rateModel l n / (n : ℝ) ^ l)| ≤ |K| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ rateModel l n / (n : ℝ) ^ l)]
      have : rateModel l n / (n : ℝ) ^ l ≤ 1 := by
        rw [div_le_one hpowpos]; exact hFle
      nlinarith [abs_nonneg K]
    have h2 : |r n / (n : ℝ) ^ l| ≤ 1 := by
      rw [abs_div, abs_of_pos hpowpos]
      rw [abs_div, abs_of_pos hn0] at hrn
      rw [div_le_one hpowpos]
      rw [div_le_one hn0] at hrn
      linarith
    rw [hsplit]
    calc |K * (rateModel l n / (n : ℝ) ^ l) + (r n / (n : ℝ) ^ l)|
        ≤ |K * (rateModel l n / (n : ℝ) ^ l)| + |r n / (n : ℝ) ^ l| := by
          rw [abs_le]
          constructor <;>
            [linarith [neg_abs_le (K * (rateModel l n / (n : ℝ) ^ l)),
                neg_abs_le (r n / (n : ℝ) ^ l)];
             linarith [le_abs_self (K * (rateModel l n / (n : ℝ) ^ l)),
                le_abs_self (r n / (n : ℝ) ^ l)]]
      _ ≤ |K| + 1 := by linarith
  have hprod : Tendsto
      (fun n : ℕ => (D n * ((n : ℝ) ^ (-l))) * ((n : ℝ) ^ l * rateError l D n))
      atTop (nhds 0) := by
    have hmaj : Tendsto
        (fun n : ℕ => (|K| + 1) * |(n : ℝ) ^ l * rateError l D n|) atTop (nhds 0) := by
      have habs : Tendsto (fun n : ℕ => |(n : ℝ) ^ l * rateError l D n|) atTop (nhds 0) := by
        simpa using hratio.abs
      simpa using habs.const_mul (|K| + 1)
    apply squeeze_zero_norm' _ hmaj
    filter_upwards [hbdd] with n hn
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hn (abs_nonneg _)
  have hlin : Tendsto (fun n : ℕ => l * (r n / (n : ℝ))) atTop (nhds 0) := by
    simpa using hsub.const_mul l
  have hsum : Tendsto
      (fun n : ℕ => (D n * ((n : ℝ) ^ (-l))) * ((n : ℝ) ^ l * rateError l D n)
        + l * (r n / (n : ℝ))) atTop (nhds 0) := by
    simpa using hprod.add hlin
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hid n hn).symm

/-! ## No eventually constant orbit -/

theorem not_eventually_constant {l : ℝ} (hl : 1 < l) (C : ℕ → ℤ) (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n)
      atTop (nhds 0)) (N : ℕ) (hconst : ∀ n, N ≤ n → C n = C N) : False := by
  have habs : Tendsto
      (fun n : ℕ => |(n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n|) atTop (nhds 0) := by
    simpa using hratio.abs
  have hsmall : ∀ᶠ n : ℕ in atTop,
      |(n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n| < l :=
    (tendsto_order.1 habs).2 l (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hsmall
  set n : ℕ := max (max N N₁) 1 with hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
  have hnN₁ : N₁ ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn1 : 1 ≤ n := le_max_right _ _
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hCn : C n = C N := hconst n hnN
  have hCn1 : C (n + 1) = C N := hconst (n + 1) (by omega)
  have hCpos : (0 : ℝ) < ((C N : ℤ) : ℝ) := by exact_mod_cast hpos N
  have herr : rateError l (fun j => (C j : ℝ)) n = -(l / (n : ℝ)) := by
    simp only [rateError, hCn, hCn1]
    rw [div_self (ne_of_gt hCpos)]
    ring
  have hval : (n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n = -(l * (n : ℝ) ^ (l - 1)) := by
    rw [herr, Real.rpow_sub hn0, Real.rpow_one]
    field_simp
  have hge : (1 : ℝ) ≤ (n : ℝ) ^ (l - 1) := by
    calc (1 : ℝ) = (n : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (n : ℝ) ^ (l - 1) := Real.rpow_le_rpow_of_exponent_le hn1r (by linarith)
  have hbad := hN₁ n hnN₁
  rw [hval, abs_neg, abs_of_nonneg (by nlinarith : (0:ℝ) ≤ l * (n : ℝ) ^ (l - 1))] at hbad
  nlinarith

/-! ## The extraction lemma -/

/-- **Integer extraction at a regular rate** (`long243:res:extraction`).
If `l > 1` and the positive integers `C n` satisfy
`C (n+1) / C n = 1 + l/n + o(n^{-l})`, then `l` is an integer `d ≥ 2` and
`C n = A n(n+1)⋯(n+d-1) + B` for all large `n`, with `A` a positive rational
and `B` a rational. -/
theorem regular_rate_extraction {l : ℝ} (hl : 1 < l) (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n)
      atTop (nhds 0)) :
    ∃ d : ℕ, 2 ≤ d ∧ l = (d : ℝ) ∧
      ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℝ) = (A : ℝ) * risingPow d (n : ℝ) + (B : ℝ) := by
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have hl1 : (1 : ℝ) ≤ l := by linarith
  obtain ⟨K, r, hdecomp, hsub⟩ := exists_residual_decomposition hl C hpos hratio
  have hdiff := residual_forwardDiff_tendsto_zero hl C K r hpos hdecomp hsub hratio
  have hiter : ∀ j : ℕ, Tendsto (iterRealForwardDiff (j + 1) r) atTop (nhds 0) :=
    fun j => iterRealForwardDiff_tendsto_zero_of_first hdiff j
  -- The decomposition of the iterated difference.
  have hFdiff : ∀ (j n : ℕ), 1 ≤ n →
      (iterIntForwardDiff j C n : ℝ)
        = K * (fallingPow l j * rateModel l n / risingPow j (n : ℝ))
          + iterRealForwardDiff j r n := by
    intro j n hn
    rw [iterIntForwardDiff_cast, hdecomp]
    simp only [iterRealForwardDiff_add, iterRealForwardDiff_const_mul]
    rw [iterRealForwardDiff_rateModel l j n hn]
  -- The limit constant is nonzero.
  have hK0 : K ≠ 0 := by
    intro hKz
    have h1 : Tendsto (fun n : ℕ => (iterIntForwardDiff 1 C n : ℝ)) atTop (nhds 0) := by
      have heq : ∀ n : ℕ, 1 ≤ n →
          (iterIntForwardDiff 1 C n : ℝ) = iterRealForwardDiff 1 r n := by
        intro n hn
        rw [hFdiff 1 n hn, hKz]
        ring
      have h2 : Tendsto (fun n : ℕ => iterRealForwardDiff 1 r n) atTop (nhds 0) := hiter 0
      apply h2.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (heq n hn).symm
    obtain ⟨N, hN⟩ := eventually_constant_of_forwardDiff_eventually_zero C
      (by simpa using eventually_iterIntForwardDiff_eq_zero C 1 h1)
    exact not_eventually_constant hl C hpos hratio N hN
  -- The floor of `l`.
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌊l⌋₊ := ⟨⌊l⌋₊, rfl⟩
  have hm1 : 1 ≤ m := by rw [hmdef]; exact Nat.le_floor (by exact_mod_cast hl1)
  have hmle : (m : ℝ) ≤ l := by rw [hmdef]; exact Nat.floor_le hl0
  have hmlt : l < (m : ℝ) + 1 := by rw [hmdef]; exact Nat.lt_floor_add_one l
  have hjgt : l < ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  -- The `(m+1)`-st difference of `C` is eventually zero.
  have hCdiff : Tendsto (fun n : ℕ => (iterIntForwardDiff (m + 1) C n : ℝ)) atTop (nhds 0) := by
    have hsum : Tendsto (fun n : ℕ =>
        K * (fallingPow l (m + 1) * rateModel l n / risingPow (m + 1) (n : ℝ))
          + iterRealForwardDiff (m + 1) r n) atTop (nhds 0) := by
      have h1 := (rateModel_iterDiff_tendsto_zero hl1 (m + 1) hjgt).const_mul K
      have h2 := hiter m
      simpa using h1.add h2
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hFdiff (m + 1) n hn).symm
  have hzero := eventually_iterIntForwardDiff_eq_zero C (m + 1) hCdiff
  obtain ⟨N₁, hN₁⟩ := eventually_constant_of_forwardDiff_eventually_zero
    (iterIntForwardDiff m C) (by simpa using hzero)
  -- `l` is an integer.
  have hlm : l = (m : ℝ) := by
    by_contra hne
    have hlt : (m : ℝ) < l := lt_of_le_of_ne hmle (Ne.symm hne)
    have hmrdiff : Tendsto (iterRealForwardDiff m r) atTop (nhds 0) := by
      obtain ⟨i, hi⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
      rw [hi]
      exact hiter i
    have hg : Tendsto
        (fun n : ℕ => K * (fallingPow l m * rateModel l n / risingPow m (n : ℝ))) atTop
        (nhds ((iterIntForwardDiff m C N₁ : ℤ) : ℝ)) := by
      have hconst : Tendsto
          (fun n : ℕ => ((iterIntForwardDiff m C N₁ : ℤ) : ℝ) - iterRealForwardDiff m r n)
          atTop (nhds ((iterIntForwardDiff m C N₁ : ℤ) : ℝ)) := by
        simpa using tendsto_const_nhds.sub hmrdiff
      apply hconst.congr'
      filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop N₁] with n hn hnN
      rw [← hN₁ n hnN, hFdiff m n hn]
      ring
    have hPpos : 0 < fallingPow l m := by
      apply Finset.prod_pos
      intro i hi
      simp only [Finset.mem_range] at hi
      have : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hi
      linarith
    have hKpos : (0 : ℝ) < |K| := abs_pos.mpr hK0
    have hatTop : Tendsto
        (fun n : ℕ => |K * (fallingPow l m * rateModel l n / risingPow m (n : ℝ))|)
        atTop atTop := by
      have hbase := rateModel_div_risingPow_atTop hl1 hlt
      have hmul := Filter.Tendsto.const_mul_atTop (mul_pos hKpos hPpos) hbase
      apply hmul.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hF := rateModel_pos hl0 n
      have hR := risingPow_pos hn0 m
      rw [abs_mul, abs_div, abs_mul, abs_of_pos hPpos, abs_of_pos hF, abs_of_pos hR]
      field_simp
      all_goals ring
    exact not_tendsto_nhds_of_tendsto_atTop hatTop _ hg.abs
  -- Hence `d = m ≥ 2`.
  have hd2 : 2 ≤ m := by
    have : (1 : ℝ) < (m : ℝ) := by rw [← hlm]; exact hl
    exact_mod_cast this
  -- The comparison sequence is the rising factorial over `d!`.
  have hmodel : ∀ n : ℕ, 1 ≤ n →
      rateModel l n = risingPow m (n : ℝ) / ((Nat.factorial m : ℕ) : ℝ) := by
    have hfac : (0 : ℝ) < ((Nat.factorial m : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
    intro n
    induction n with
    | zero => intro h; exact absurd h (by omega)
    | succ k ih =>
        intro _
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [rateModel_one]
          have h1 : risingPow m ((1 : ℕ) : ℝ) = ((Nat.factorial m : ℕ) : ℝ) := by
            rw [Nat.cast_one, risingPow_one_eq_factorial]
          rw [h1]
          field_simp
        · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
          have hshift := risingPow_shift m (k : ℝ)
          rw [rateModel_succ, ih hk, hlm]
          push_cast
          field_simp
          linarith [hshift]
  -- The residual is eventually constant.
  have hrconst : ∃ N : ℕ, ∀ n, N ≤ n → r n = r N := by
    have hmrdiff : Tendsto (iterRealForwardDiff m r) atTop (nhds 0) := by
      obtain ⟨i, hi⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
      rw [hi]
      exact hiter i
    have hkappa : ∀ n : ℕ, 1 ≤ n →
        iterRealForwardDiff m r n
          = ((iterIntForwardDiff m C n : ℤ) : ℝ)
            - K * (fallingPow l m / ((Nat.factorial m : ℕ) : ℝ)) := by
      intro n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hR : (0 : ℝ) < risingPow m (n : ℝ) := risingPow_pos hn0 m
      have hfac : (0 : ℝ) < ((Nat.factorial m : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
      rw [hFdiff m n hn, hmodel n hn]
      field_simp
      ring
    have hconstdiff : ∀ᶠ n in atTop, iterRealForwardDiff m r n
        = ((iterIntForwardDiff m C N₁ : ℤ) : ℝ) - K * (fallingPow l m / ((Nat.factorial m : ℕ) : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop N₁] with n hn hnN
      rw [hkappa n hn, hN₁ n hnN]
    have hvanish : ((iterIntForwardDiff m C N₁ : ℤ) : ℝ)
        - K * (fallingPow l m / ((Nat.factorial m : ℕ) : ℝ)) = 0 := by
      have hc : Tendsto (fun _ : ℕ => ((iterIntForwardDiff m C N₁ : ℤ) : ℝ)
          - K * (fallingPow l m / ((Nat.factorial m : ℕ) : ℝ))) atTop (nhds 0) := hmrdiff.congr' hconstdiff
      exact tendsto_nhds_unique tendsto_const_nhds hc
    have hz : ∀ᶠ n in atTop, iterRealForwardDiff m r n = 0 := by
      filter_upwards [hconstdiff] with n hn
      rw [hn, hvanish]
    have hfirst : ∀ᶠ n in atTop, realForwardDiff r n = 0 := by
      obtain ⟨i, hi⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
      exact realForwardDiff_eventually_zero_of_iter hdiff i (by rw [← hi]; exact hz)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hfirst
    refine ⟨N₂, ?_⟩
    intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction j with
    | zero => simp
    | succ j ih =>
        have hz2 := hN₂ (N₂ + j) (by omega)
        simp only [realForwardDiff] at hz2
        have hstep : r (N₂ + j + 1) = r (N₂ + j) := by linarith
        rw [show N₂ + (j + 1) = N₂ + j + 1 by omega, hstep, ih (by omega)]
  obtain ⟨N₂, hN₂⟩ := hrconst
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = max N₂ 1 := ⟨_, rfl⟩
  have hNN₂ : N₂ ≤ N := by rw [hNdef]; exact le_max_left _ _
  have hN1 : 1 ≤ N := by rw [hNdef]; exact le_max_right _ _
  have hfacpos : (0 : ℝ) < ((Nat.factorial m : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  obtain ⟨Areal, hAreal⟩ : ∃ a : ℝ, a = K / ((Nat.factorial m : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨Breal, hBreal⟩ : ∃ b : ℝ, b = r N₂ := ⟨_, rfl⟩
  have hprofile : ∀ n, N ≤ n → (C n : ℝ) = Areal * risingPow m (n : ℝ) + Breal := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans hN1 hn
    have hrn : r n = r N₂ := hN₂ n (le_trans hNN₂ hn)
    have h := congrFun hdecomp n
    rw [hmodel n hn1] at h
    rw [h, hrn, hAreal, hBreal]
    field_simp
  -- The leading coefficient is positive.
  have hApos : 0 < Areal := by
    rcases lt_trichotomy Areal 0 with hneg | hzero | hposA
    · exfalso
      obtain ⟨t, ht⟩ := exists_nat_gt ((Breal - 1) / (-Areal))
      obtain ⟨n, hnN, hntr, hn1⟩ : ∃ n : ℕ, N ≤ n ∧ (t : ℝ) ≤ (n : ℝ) ∧ 1 ≤ n := by
        refine ⟨max (max N t) 1, le_trans (le_max_left _ _) (le_max_left _ _), ?_,
          le_max_right _ _⟩
        have : t ≤ max (max N t) 1 := le_trans (le_max_right N t) (le_max_left _ _)
        exact_mod_cast this
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hgt : (Breal - 1) / (-Areal) < (n : ℝ) := lt_of_lt_of_le ht hntr
      have hnlt : Breal - 1 < (-Areal) * (n : ℝ) := by
        rw [div_lt_iff₀ (by linarith)] at hgt
        linarith
      have hRge : (n : ℝ) ≤ risingPow m (n : ℝ) := by
        have ha : (n : ℝ) ^ m ≤ risingPow m (n : ℝ) := pow_le_risingPow hn0.le m
        have hb : (n : ℝ) ≤ (n : ℝ) ^ m := by
          calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (n : ℝ) ^ m := pow_le_pow_right₀ (by exact_mod_cast hn1) (by omega)
        linarith
      have hCn1 : (1 : ℤ) ≤ C n := by have := hpos n; omega
      have hCn : (1 : ℝ) ≤ (C n : ℝ) := by exact_mod_cast hCn1
      have hCval := hprofile n hnN
      have hmul : Areal * risingPow m (n : ℝ) ≤ Areal * (n : ℝ) := by
        nlinarith [mul_nonneg (le_of_lt (neg_pos.mpr hneg)) (sub_nonneg.mpr hRge)]
      linarith [hCval, hmul, hnlt, hCn]
    · exfalso
      apply hK0
      rw [hAreal, div_eq_zero_iff] at hzero
      rcases hzero with h | h
      · exact h
      · exact absurd h (ne_of_gt hfacpos)
    · exact hposA
  -- The rising factorial takes integer values, so the coefficients are rational.
  have hcast1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  obtain ⟨PN, hPN⟩ : ∃ z : ℤ, (z : ℝ) = risingPow m (N : ℝ) :=
    ⟨∏ i ∈ Finset.range m, ((N : ℤ) + (i : ℤ)), by
      simp only [risingPow]; push_cast; ring⟩
  obtain ⟨PN1, hPN1⟩ : ∃ z : ℤ, (z : ℝ) = risingPow m ((N : ℝ) + 1) :=
    ⟨∏ i ∈ Finset.range m, (((N : ℤ) + 1) + (i : ℤ)), by
      simp only [risingPow]; push_cast; ring⟩
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hRpos : (0 : ℝ) < risingPow m (N : ℝ) := risingPow_pos hN0 m
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hgap : risingPow m (N : ℝ) < risingPow m ((N : ℝ) + 1) := by
    have hshift := risingPow_shift m (N : ℝ)
    have hstep : (N : ℝ) * risingPow m ((N : ℝ) + 1)
        ≥ (N : ℝ) * risingPow m (N : ℝ) + risingPow m (N : ℝ) := by
      rw [hshift]; nlinarith [hRpos, hmr]
    nlinarith [hstep, hRpos, hN0]
  have hgapne : ((PN1 - PN : ℤ) : ℝ) ≠ 0 := by
    have hlt : (0 : ℝ) < ((PN1 - PN : ℤ) : ℝ) := by
      push_cast
      rw [hPN, hPN1]
      linarith
    exact ne_of_gt hlt
  have h0 := hprofile N le_rfl
  have h1 := hprofile (N + 1) (by omega)
  rw [hcast1, ← hPN1] at h1
  rw [← hPN] at h0
  have hAval : Areal = ((C (N + 1) - C N : ℤ) : ℝ) / ((PN1 - PN : ℤ) : ℝ) := by
    rw [eq_div_iff hgapne]
    push_cast
    push_cast at h0 h1
    linear_combination h0 - h1
  have hBval : Breal = (C N : ℝ) - Areal * (PN : ℝ) := by linarith [h0]
  obtain ⟨A, hA⟩ : ∃ A : ℚ, (A : ℝ) = Areal :=
    ⟨((C (N + 1) - C N : ℤ) : ℚ) / ((PN1 - PN : ℤ) : ℚ), by rw [hAval]; push_cast; ring⟩
  obtain ⟨B, hB⟩ : ∃ B : ℚ, (B : ℝ) = Breal :=
    ⟨(C N : ℚ) - A * ((PN : ℤ) : ℚ), by push_cast; rw [hA, hBval]⟩
  refine ⟨m, hd2, hlm, A, B, ?_, N, ?_⟩
  · have hpos' : (0 : ℝ) < (A : ℝ) := by rw [hA]; exact hApos
    exact_mod_cast hpos'
  · intro n hn
    rw [hA, hB]
    exact hprofile n hn

/-! ## The `λ = 3` specialisation

The tree proves the cubic instance through the `PaperCompleteR20.CubicRate*`
chain.  These two declarations check that the general lemma above really is a
generalisation of that chain: the hypothesis specialises to the tree's
`cubicRatioError` verbatim, and the conclusion to its `risingCubic` profile. -/

theorem rateError_three (C : ℕ → ℝ) (n : ℕ) :
    rateError 3 C n = cubicRatioError C n := rfl

theorem risingPow_three (x : ℝ) : risingPow 3 x = x * (x + 1) * (x + 2) := by
  simp only [risingPow, Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

/-- Specialising the general lemma at `λ = 3` recovers the tree's cubic-rate
profile theorem
`PaperCompleteR20.literal_ratio_error_gives_positive_rational_eventual_cubic`. -/
theorem regular_rate_extraction_cubic (C : ℕ → ℤ) (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (B : ℝ) := by
  have hratio' : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 : ℝ) *
      rateError 3 (fun j => (C j : ℝ)) n) atTop (nhds 0) := by
    apply hratio.congr'
    filter_upwards [] with n
    rw [rateError_three]
    congr 1
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  obtain ⟨d, _hd2, hld, A, B, hApos, N, hN⟩ :=
    regular_rate_extraction (by norm_num : (1 : ℝ) < 3) C hpos hratio'
  have hd3 : d = 3 := by exact_mod_cast hld.symm
  subst hd3
  refine ⟨A, B, hApos, N, fun n hn => ?_⟩
  rw [hN n hn, risingPow_three]
  simp [risingCubic]

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction_cubic

end ErdosProblems.Erdos243.PaperCompleteR21
