import ErdosProblems.Erdos1049.AllRow.Producer

/-!
# Erdős #1049: a coefficient of each transformed row, for the untruncated `H`

Paper restatement of `long1049:res:allrowinitial`:

> For `m ≥ j ≥ 0` one has `D_j W_m(t) ∈ q^{E(m,j)} A` and
> `[q^{E(m,j)}] D_j W_m(t) = (-1)^j h_{j-t}`.

Here, following the paper's display,

* `H(X) = 1 + ∑_{s ≥ 1} a_s(q) X^s` with arbitrary `a_s(q) ∈ ℤ[[q]]` and constant
  term `1` in `X`; the only normalisation imposed is that constant term;
* `W_m(t) = q^{(m+1)t} ∏_{r=1}^{m} H(q^r)`, which is `paperTail a m t` below;
* `D_j = ∏_{r=0}^{j-1}(I - q^r 𝒩)` with `𝒩` the backward shift in `m`, which is
  the tree's `zudilinBackwardShiftApply j m`;
* `E(m,j) = mj - j(j-1)/2`;
* `H̄ = H mod q` and `h_r = [X^r] H̄(X)^{-1}`, with `h_r = 0` for `r < 0` and
  `h_0 = 1`.

The tree's `AllRow.finite_row_initial` proves the same statement for the
`K`-truncated ratio `1 + ∑_{s < K} a_{s+1}(q) q^{(n+1)(s+1)}` under `j ≤ K`.  The
paper allows arbitrary `a_s(q)`, so `H(q^{n+1})` is an infinite sum.  This file
builds that untruncated series (`paperRatio`), proves it agrees with every
sufficiently long truncation coefficientwise (`paperRatio_agree`), and transports
the finite-state theorem across the coefficient filtration of `AllRow.Agree`.
The exponent identity `E(m,j) = rowExponent j (m-j)` is proved, not assumed.

`h_{j-t}` for `t > j` is `0` because `h_r = 0` for `r < 0`; this is the `else`
branch below.  No external theorem is used: every input is proved in the tree.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21

open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.AllRow
open scoped BigOperators

noncomputable section

/-! ## `H(q^{n+1})` as an untruncated formal series -/

private theorem coeff_ratio_term_eq_zero (a : ℕ → S) (n s d : ℕ)
    (h : d < (n + 1) * (s + 1)) :
    PowerSeries.coeff d (a (s + 1) * PowerSeries.X ^ ((n + 1) * (s + 1)) : S) = 0 := by
  rw [mul_comm, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr h]

/-- Lengthening the truncation cannot change a coefficient already visible. -/
theorem finiteRatio_agree_mono (a : ℕ → S) (n D K K' : ℕ)
    (hDK : D ≤ K) (hKK' : K ≤ K') :
    Agree D (finiteRatio a K n) (finiteRatio a K' n) := by
  intro d hd
  simp only [finiteRatio, map_add, map_sum]
  congr 1
  refine Finset.sum_subset (Finset.range_subset_range.mpr hKK') ?_
  intro s _ hs
  have hs' : K ≤ s := by simpa using hs
  refine coeff_ratio_term_eq_zero a n s d ?_
  have h1 : 1 * (s + 1) ≤ (n + 1) * (s + 1) := Nat.mul_le_mul_right _ (by omega)
  rw [one_mul] at h1
  omega

/-- `H(q^{n+1}) = 1 + ∑_{s ≥ 1} a_s(q) q^{(n+1)s}`, the untruncated ratio.  Each
coefficient is the corresponding coefficient of a long enough truncation, which
is exactly what the infinite sum means: the term of index `s` has order at least
`s + 1`. -/
def paperRatio (a : ℕ → S) (n : ℕ) : S :=
  PowerSeries.mk fun d => PowerSeries.coeff d (finiteRatio a (d + 1) n)

/-- The transcription property of `paperRatio`. -/
theorem paperRatio_agree (a : ℕ → S) (n D K : ℕ) (hDK : D ≤ K) :
    Agree D (paperRatio a n) (finiteRatio a K n) := by
  intro d hd
  unfold paperRatio
  rw [PowerSeries.coeff_mk]
  exact finiteRatio_agree_mono a n (d + 1) (d + 1) K (le_refl _) (by omega) d
    (by omega)

@[simp] theorem constantCoeff_paperRatio (a : ℕ → S) (n : ℕ) :
    PowerSeries.constantCoeff (paperRatio a n) = 1 := by
  have h := paperRatio_agree a n 1 1 (le_refl _) 0 (by omega)
  rw [PowerSeries.coeff_zero_eq_constantCoeff] at h
  rw [h, constantCoeff_finiteRatio]

/-! ## The paper's rows `W_m(t)` -/

/-- `∏_{r=1}^{m} H(q^r)`. -/
def paperUnit (a : ℕ → S) : ℕ → S
  | 0 => 1
  | n + 1 => paperUnit a n * paperRatio a n

/-- `W_m(t) = q^{(m+1)t} ∏_{r=1}^{m} H(q^r)`. -/
def paperTail (a : ℕ → S) (n t : ℕ) : S :=
  PowerSeries.X ^ ((n + 1) * t) * paperUnit a n

theorem paperUnit_agree (a : ℕ → S) (D K : ℕ) (hDK : D ≤ K) (n : ℕ) :
    Agree D (paperUnit a n) (finiteUnit a K 1 n) := by
  induction n with
  | zero => exact Agree.refl _ _
  | succ n ih => exact ih.mul (paperRatio_agree a n D K hDK)

theorem paperTail_agree (a : ℕ → S) (D K : ℕ) (hDK : D ≤ K) (n t : ℕ) :
    Agree D (paperTail a n t) (finiteTail a K 1 n t) := by
  unfold paperTail finiteTail
  exact Agree.shift (paperUnit_agree a D K hDK n) _

theorem paperRow_agree (a : ℕ → S) (D K : ℕ) (hDK : D ≤ K) (j m t : ℕ) :
    Agree D (zudilinBackwardShiftApply j m (fun n => paperTail a n t))
      (zudilinBackwardShiftApply j m (fun n => finiteTail a K 1 n t)) :=
  Agree.backward j m _ _ (fun n => paperTail_agree a D K hDK n t)

/-! ## The paper's exponent `E(m,j) = mj - j(j-1)/2` -/

theorem paperE_eq_rowExponent (m j : ℕ) (hjm : j ≤ m) :
    m * j - j * (j - 1) / 2 = rowExponent j (m - j) := by
  obtain ⟨l, rfl⟩ : ∃ l, m = j + l := ⟨m - j, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have hTU : j * (j + 1) / 2 + j * (j - 1) / 2 = j * j := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) ?_
    rw [Nat.mul_add, two_mul_triangle j]
    cases j with
    | zero => simp
    | succ k =>
        have hk : 2 * ((k + 1) * k / 2) = (k + 1) * k := by
          rw [mul_comm (k + 1) k]
          exact two_mul_triangle k
        simp only [Nat.add_sub_cancel]
        rw [hk]
        ring
  have hexp : (j + l) * j = j * j + j * l := by ring
  refine Nat.sub_eq_of_eq_add ?_
  rw [rowExponent, hexp, ← hTU]
  omega

/-! ## The reciprocal coefficients `h_r = [X^r] H̄(X)^{-1}` -/

/-- `H̄ = H mod q`, an ordinary power series in `X` over `ℤ`. -/
def paperReducedSeries (a : ℕ → S) : PowerSeries ℤ :=
  PowerSeries.mk fun s => if s = 0 then 1 else PowerSeries.constantCoeff (a s)

@[simp] theorem constantCoeff_paperReducedSeries (a : ℕ → S) :
    PowerSeries.constantCoeff (paperReducedSeries a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  unfold paperReducedSeries
  rw [PowerSeries.coeff_mk]
  simp

theorem coeff_paperReducedSeries_succ (a : ℕ → S) (s : ℕ) :
    PowerSeries.coeff (s + 1) (paperReducedSeries a) =
      PowerSeries.constantCoeff (a (s + 1)) := by
  unfold paperReducedSeries
  rw [PowerSeries.coeff_mk]
  simp

/-- `h_r = [X^r] H̄(X)^{-1}`. -/
def paperReciprocal (a : ℕ → S) (r : ℕ) : ℤ :=
  PowerSeries.coeff r (PowerSeries.invOfUnit (paperReducedSeries a) 1)

theorem paperReducedSeries_inv_mul (a : ℕ → S) :
    PowerSeries.invOfUnit (paperReducedSeries a) 1 * paperReducedSeries a = 1 :=
  PowerSeries.invOfUnit_mul _ 1 (by simp)

theorem paperReciprocal_zero (a : ℕ → S) : paperReciprocal a 0 = 1 := by
  have h := congrArg PowerSeries.constantCoeff (paperReducedSeries_inv_mul a)
  rw [map_mul, constantCoeff_paperReducedSeries, mul_one, map_one] at h
  rw [paperReciprocal, PowerSeries.coeff_zero_eq_constantCoeff]
  exact h

theorem paperReciprocal_rec (a : ℕ → S) (i : ℕ) :
    paperReciprocal a (i + 1) =
      -(∑ s ∈ Finset.range (i + 1),
          PowerSeries.constantCoeff (a (s + 1)) * paperReciprocal a (i - s)) := by
  have hc : PowerSeries.coeff (i + 1)
      (PowerSeries.invOfUnit (paperReducedSeries a) 1 * paperReducedSeries a) = 0 := by
    rw [paperReducedSeries_inv_mul]
    simp
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => PowerSeries.coeff x (PowerSeries.invOfUnit (paperReducedSeries a) 1) *
        PowerSeries.coeff y (paperReducedSeries a)) (i + 1)] at hc
  simp only [Nat.succ_eq_add_one] at hc
  rw [Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_paperReducedSeries, mul_one] at hc
  have hre : (∑ k ∈ Finset.range (i + 1),
      PowerSeries.coeff k (PowerSeries.invOfUnit (paperReducedSeries a) 1) *
        PowerSeries.coeff (i + 1 - k) (paperReducedSeries a)) =
      ∑ s ∈ Finset.range (i + 1),
        PowerSeries.constantCoeff (a (s + 1)) * paperReciprocal a (i - s) := by
    rw [← Finset.sum_range_reflect
      (fun s => PowerSeries.constantCoeff (a (s + 1)) * paperReciprocal a (i - s))
      (i + 1)]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have e1 : i + 1 - 1 - k = i - k := by omega
    have e2 : i + 1 - k = i - k + 1 := by omega
    have e3 : i - (i - k) = k := by omega
    simp only [e1, e2, e3, coeff_paperReducedSeries_succ, paperReciprocal]
    ring
  rw [hre] at hc
  rw [paperReciprocal]
  linarith

/-! ## The paper statement -/

/-- **`long1049:res:allrowinitial`.**  For `m ≥ j ≥ 0`, the transformed row
`D_j W_m(t)` is divisible by `q^{E(m,j)}` with `E(m,j) = mj - j(j-1)/2`, and its
coefficient there is `(-1)^j h_{j-t}`, where `h_r = [X^r] H̄(X)^{-1}` and `h_r = 0`
for `r < 0`.  `h` is given abstractly by its reciprocal recurrence; the
corollary below supplies the concrete `[X^r] H̄(X)^{-1}`. -/
theorem all_row_initial (a : ℕ → S) (h : ℕ → ℤ) (hzero : h 0 = 1)
    (hrec : ∀ i : ℕ, h (i + 1) =
      -(∑ s ∈ Finset.range (i + 1),
          PowerSeries.constantCoeff (a (s + 1)) * h (i - s)))
    (m j t : ℕ) (hjm : j ≤ m) :
    (∀ d, d < m * j - j * (j - 1) / 2 →
        PowerSeries.coeff d
          (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) = 0) ∧
      PowerSeries.coeff (m * j - j * (j - 1) / 2)
        (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) =
        (if t ≤ j then (-1 : ℤ) ^ j * h (j - t) else 0) := by
  have hE : m * j - j * (j - 1) / 2 = rowExponent j (m - j) :=
    paperE_eq_rowExponent m j hjm
  obtain ⟨l, rfl⟩ : ∃ l, m = j + l := ⟨m - j, by omega⟩
  rw [Nat.add_sub_cancel_left] at hE
  have hjE : j ≤ rowExponent j l := rowExponent_ge_depth j l
  have hfin := finite_row_initial a (rowExponent j l + 1) 1 (by simp) j l t (by omega)
  have hag := paperRow_agree a (rowExponent j l + 1) (rowExponent j l + 1)
    (le_refl _) j (j + l) t
  rw [hE]
  refine ⟨?_, ?_⟩
  · intro d hd
    rw [hag d (by omega)]
    exact hfin.1 d hd
  · rw [hag (rowExponent j l) (by omega), hfin.2,
      hankelAssociatedCoeff_eq_reciprocal
        (fun s => PowerSeries.constantCoeff (a s)) h hzero hrec j t]

/-- **`long1049:res:allrowinitial`, with `h_r` literally `[X^r] H̄(X)^{-1}`.** -/
theorem all_row_initial_reciprocal (a : ℕ → S) (m j t : ℕ) (hjm : j ≤ m) :
    (∀ d, d < m * j - j * (j - 1) / 2 →
        PowerSeries.coeff d
          (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) = 0) ∧
      PowerSeries.coeff (m * j - j * (j - 1) / 2)
        (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) =
        (if t ≤ j then (-1 : ℤ) ^ j * paperReciprocal a (j - t) else 0) :=
  all_row_initial a (paperReciprocal a) (paperReciprocal_zero a)
    (paperReciprocal_rec a) m j t hjm

/-- The first clause in its literal form `D_j W_m(t) ∈ q^{E(m,j)} A`: divisibility
by `q^{E(m,j)}` in `ℤ[[q]]` is exactly the vanishing of every lower
coefficient. -/
theorem all_row_initial_dvd (a : ℕ → S) (m j t : ℕ) (hjm : j ≤ m) :
    (PowerSeries.X : S) ^ (m * j - j * (j - 1) / 2) ∣
      zudilinBackwardShiftApply j m (fun n => paperTail a n t) :=
  PowerSeries.X_pow_dvd_iff.mpr (all_row_initial_reciprocal a m j t hjm).1

end

end ErdosProblems.Erdos1049.PaperCompleteR21

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.finiteRatio_agree_mono
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.paperRatio_agree
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.constantCoeff_paperRatio
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.paperUnit_agree
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.paperTail_agree
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.paperRow_agree
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.paperE_eq_rowExponent
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_zero
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_rec
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial_reciprocal
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial_dvd
