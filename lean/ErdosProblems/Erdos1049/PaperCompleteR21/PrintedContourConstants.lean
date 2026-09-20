import ErdosProblems.Erdos1049.MeasureConstantsR10
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Erdős #1049: the printed decimals of `θ*`, `μ` and `4^μ`

`res:rational-base-threshold`, `long1049:res:region` and `long1049:res:31over4`
print three truncated decimal constants built from Zudilin's trigamma constant

`J = ∑_{i=1}^{13} (ψ₁(uᵢ) - ψ₁(vᵢ))`,  `C₀ = 266 - (3/π²)(225 - J)`,
`C₁ = 1091/2`,  `θ* = C₀/C₁`,  `μ = C₁/C₀`:

* `θ* = 0.40568302138406054…` (the long paper; `0.4056830213840605…` in the
  short paper);
* `μ = 2.4649786835749750…`;
* `4^μ = 30.483515…`.

Pinning seventeen digits of `θ*` needs `J` to about `10^{-15}`, which the
`k = 0` and sixteen-term partial sums already in the tree cannot give.  The
tool built here is a closed two-sided rational bracket for the trigamma series,

`tailLow x ≤ ψ₁(x) ≤ tailHigh x`  for `x ≥ 1`,

with `tailLow x = (1/x + 1/(2x²) + 1/(6x³) - 1/(30x⁵) + 1/(42x⁷) - 1/(30x⁹))`
and `tailHigh x = tailLow x + 5/(66x¹¹)`.  Both are proved from scratch by an
exact telescoping certificate: the rational function `tailLow x - tailLow (x+1)
- 1/x²` has numerator `-(1925x¹⁰ + 9625x⁹ + 21274x⁸ + 27346x⁷ + 22462x⁶
+ 12100x⁵ + 4180x⁴ + 847x³ + 77x²)` over `2310x¹¹(x+1)¹¹`, hence is `≤ 0`, and
the corresponding numerator for `tailHigh` is `7601x⁸ + 30404x⁷ + 58388x⁶
+ 68750x⁵ + 53570x⁴ + 28028x³ + 9548x² + 1925x + 175 ≥ 0`.  No Euler–Maclaurin
theory, no Bernoulli numbers and no `native_decide` are used: the two
polynomials are single-signed for every `x > 0`, so telescoping the step
inequality bounds every partial sum.

Splitting each `ψ₁` off after thirty-two exact rational terms then gives each
of the thirteen differences to about `4 · 10^{-18}`, hence `J` to `5 · 10^{-17}`
and `θ*` to `3 · 10^{-20}`, which is thirty times the margin needed for the
seventeenth printed digit.  The value of `π` comes from `Real.pi_gt_d20` /
`Real.pi_lt_d20`, and `log 2` from Mathlib's Taylor estimate for `log (1 - x)`.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## A closed rational bracket for the trigamma series -/

/-- Numerator of the Euler–Maclaurin tail over `2310 x¹¹`. -/
noncomputable def tailNum (x : ℝ) : ℝ :=
  2310 * x ^ 10 + 1155 * x ^ 9 + 385 * x ^ 8 - 77 * x ^ 6 + 55 * x ^ 4 - 77 * x ^ 2

/-- `1/x + 1/(2x²) + 1/(6x³) - 1/(30x⁵) + 1/(42x⁷) - 1/(30x⁹)`. -/
noncomputable def tailLow (x : ℝ) : ℝ := tailNum x / (2310 * x ^ 11)

/-- `tailLow x + 5/(66x¹¹)`. -/
noncomputable def tailHigh (x : ℝ) : ℝ := (tailNum x + 175) / (2310 * x ^ 11)

theorem tailLow_step {x : ℝ} (hx : 0 < x) : tailLow x - tailLow (x + 1) ≤ 1 / x ^ 2 := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hxne : x ≠ 0 := hx.ne'
  have hx1ne : x + 1 ≠ 0 := hx1.ne'
  have hden : (0 : ℝ) < 2310 * x ^ 11 * (x + 1) ^ 11 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hx 11)) (pow_pos hx1 11)
  have hnum : (0 : ℝ) ≤ 1925 * x ^ 10 + 9625 * x ^ 9 + 21274 * x ^ 8 + 27346 * x ^ 7 +
      22462 * x ^ 6 + 12100 * x ^ 5 + 4180 * x ^ 4 + 847 * x ^ 3 + 77 * x ^ 2 := by
    have p2 := pow_pos hx 2
    have p3 := pow_pos hx 3
    have p4 := pow_pos hx 4
    have p5 := pow_pos hx 5
    have p6 := pow_pos hx 6
    have p7 := pow_pos hx 7
    have p8 := pow_pos hx 8
    have p9 := pow_pos hx 9
    have p10 := pow_pos hx 10
    linarith
  have key : 1 / x ^ 2 - (tailLow x - tailLow (x + 1)) =
      (1925 * x ^ 10 + 9625 * x ^ 9 + 21274 * x ^ 8 + 27346 * x ^ 7 + 22462 * x ^ 6 +
        12100 * x ^ 5 + 4180 * x ^ 4 + 847 * x ^ 3 + 77 * x ^ 2)
        / (2310 * x ^ 11 * (x + 1) ^ 11) := by
    unfold tailLow tailNum
    field_simp
    ring
  have hge : (0 : ℝ) ≤ 1 / x ^ 2 - (tailLow x - tailLow (x + 1)) := by
    rw [key]; exact div_nonneg hnum hden.le
  linarith

theorem tailHigh_step {x : ℝ} (hx : 0 < x) : 1 / x ^ 2 ≤ tailHigh x - tailHigh (x + 1) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hxne : x ≠ 0 := hx.ne'
  have hx1ne : x + 1 ≠ 0 := hx1.ne'
  have hden : (0 : ℝ) < 2310 * x ^ 11 * (x + 1) ^ 11 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hx 11)) (pow_pos hx1 11)
  have hnum : (0 : ℝ) ≤ 7601 * x ^ 8 + 30404 * x ^ 7 + 58388 * x ^ 6 + 68750 * x ^ 5 +
      53570 * x ^ 4 + 28028 * x ^ 3 + 9548 * x ^ 2 + 1925 * x + 175 := by
    have p2 := pow_pos hx 2
    have p3 := pow_pos hx 3
    have p4 := pow_pos hx 4
    have p5 := pow_pos hx 5
    have p6 := pow_pos hx 6
    have p7 := pow_pos hx 7
    have p8 := pow_pos hx 8
    linarith
  have key : tailHigh x - tailHigh (x + 1) - 1 / x ^ 2 =
      (7601 * x ^ 8 + 30404 * x ^ 7 + 58388 * x ^ 6 + 68750 * x ^ 5 + 53570 * x ^ 4 +
        28028 * x ^ 3 + 9548 * x ^ 2 + 1925 * x + 175)
        / (2310 * x ^ 11 * (x + 1) ^ 11) := by
    unfold tailHigh tailNum
    field_simp
    ring
  have hge : (0 : ℝ) ≤ tailHigh x - tailHigh (x + 1) - 1 / x ^ 2 := by
    rw [key]; exact div_nonneg hnum hden.le
  linarith

theorem tailHigh_nonneg {y : ℝ} (hy : 1 ≤ y) : 0 ≤ tailHigh y := by
  have hy0 : (0 : ℝ) < y := by linarith
  have ht : (0 : ℝ) ≤ y - 1 := by linarith
  have hexp : tailNum y + 175 =
      2310 * (y - 1) ^ 10 + 24255 * (y - 1) ^ 9 + 114730 * (y - 1) ^ 8 +
        321860 * (y - 1) ^ 7 + 592823 * (y - 1) ^ 6 + 748748 * (y - 1) ^ 5 +
        656480 * (y - 1) ^ 4 + 394460 * (y - 1) ^ 3 + 155408 * (y - 1) ^ 2 +
        36179 * (y - 1) + 3926 := by
    unfold tailNum; ring
  unfold tailHigh
  refine div_nonneg ?_ ?_
  · rw [hexp]
    linarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
      pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9, pow_nonneg ht 10]
  · linarith [pow_pos hy0 11]

theorem tailLow_le_two_div {y : ℝ} (hy : 1 ≤ y) : tailLow y ≤ 2 / y := by
  have hy0 : (0 : ℝ) < y := by linarith
  have ht : (0 : ℝ) ≤ y - 1 := by linarith
  have hexp : 4620 * y ^ 10 - tailNum y =
      2310 * (y - 1) ^ 10 + 21945 * (y - 1) ^ 9 + 93170 * (y - 1) ^ 8 +
        232540 * (y - 1) ^ 7 + 377377 * (y - 1) ^ 6 + 415492 * (y - 1) ^ 5 +
        313720 * (y - 1) ^ 4 + 159940 * (y - 1) ^ 3 + 52492 * (y - 1) ^ 2 +
        10021 * (y - 1) + 869 := by
    unfold tailNum; ring
  have hnn : (0 : ℝ) ≤ 4620 * y ^ 10 - tailNum y := by
    rw [hexp]
    linarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
      pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9, pow_nonneg ht 10]
  have hyne : y ≠ 0 := hy0.ne'
  have hd : (0 : ℝ) < 2310 * y ^ 11 := by linarith [pow_pos hy0 11]
  have key : 2 / y - tailLow y = (4620 * y ^ 10 - tailNum y) / (2310 * y ^ 11) := by
    unfold tailLow
    first
      | (field_simp; ring)
      | field_simp
  have hge : (0 : ℝ) ≤ 2 / y - tailLow y := by
    rw [key]; exact div_nonneg hnn hd.le
  linarith

/-- Upper half of the bracket: every partial sum telescopes below `tailHigh x`. -/
theorem trigammaSeries_le_tailHigh {x : ℝ} (hx : 1 ≤ x) : trigammaSeries x ≤ tailHigh x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have tel : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x) ^ 2 ≤
      tailHigh x - tailHigh (x + (n : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hxn : (0 : ℝ) < x + (n : ℝ) := by linarith
      have hstep := tailHigh_step hxn
      have hterm : (1 : ℝ) / ((n : ℝ) + x) ^ 2 = 1 / (x + (n : ℝ)) ^ 2 := by ring
      have harg : x + ((n + 1 : ℕ) : ℝ) = x + (n : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, harg, hterm]
      linarith
  have hb : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x) ^ 2 ≤ tailHigh x := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) ≤ tailHigh (x + (n : ℝ)) := tailHigh_nonneg (by linarith)
    linarith [tel n]
  have hsum := summable_trigammaTerm hx0
  have hts := hsum.hasSum.tendsto_sum_nat
  exact le_of_tendsto hts (Filter.Eventually.of_forall hb)

/-- Lower half of the bracket. -/
theorem tailLow_le_trigammaSeries {x : ℝ} (hx : 1 ≤ x) : tailLow x ≤ trigammaSeries x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsum := summable_trigammaTerm hx0
  have tel : ∀ n : ℕ, tailLow x - tailLow (x + (n : ℝ)) ≤
      ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hxn : (0 : ℝ) < x + (n : ℝ) := by linarith
      have hstep := tailLow_step hxn
      have hterm : (1 : ℝ) / ((n : ℝ) + x) ^ 2 = 1 / (x + (n : ℝ)) ^ 2 := by ring
      have harg : x + ((n + 1 : ℕ) : ℝ) = x + (n : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, harg, hterm]
      linarith
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x) ^ 2 ≤ trigammaSeries x := by
    intro n
    exact hsum.sum_le_tsum (Finset.range n) (fun k _ => by positivity)
  by_contra hcon
  push_neg at hcon
  have hdpos : (0 : ℝ) < tailLow x - trigammaSeries x := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / (tailLow x - trigammaSeries x))
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (div_pos (by norm_num) hdpos) hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
  have hxn1 : (1 : ℝ) ≤ x + (n : ℝ) := by linarith
  have hxn0 : (0 : ℝ) < x + (n : ℝ) := by linarith
  have hbd := tailLow_le_two_div hxn1
  have hkey : tailLow x - trigammaSeries x ≤ 2 / (x + (n : ℝ)) := by
    linarith [tel n, hpart n]
  rw [le_div_iff₀ hxn0] at hkey
  rw [div_lt_iff₀ hdpos] at hn
  nlinarith [mul_pos hdpos hx0]

/-! ## Splitting off thirty-two exact terms -/

theorem trigammaSeries_shift {w : ℝ} (hw : 0 < w) (K : ℕ) :
    trigammaSeries w =
      (∑ k ∈ Finset.range K, 1 / ((k : ℝ) + w) ^ 2) + trigammaSeries ((K : ℝ) + w) := by
  have hs := summable_trigammaTerm hw
  have h := Summable.sum_add_tsum_nat_add (f := fun k : ℕ => 1 / ((k : ℝ) + w) ^ 2) K hs
  unfold trigammaSeries
  rw [← h]
  congr 1
  refine tsum_congr fun i => ?_
  push_cast
  ring_nf

/-- The working bracket: thirty-two exact terms of each difference, plus the
closed tails. -/
theorem jterm_bracket {u v lo hi : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h1 : lo ≤ (∑ k ∈ Finset.range 32, (1 / ((k : ℝ) + u) ^ 2 - 1 / ((k : ℝ) + v) ^ 2))
      + tailLow (32 + u) - tailHigh (32 + v))
    (h2 : (∑ k ∈ Finset.range 32, (1 / ((k : ℝ) + u) ^ 2 - 1 / ((k : ℝ) + v) ^ 2))
      + tailHigh (32 + u) - tailLow (32 + v) ≤ hi) :
    lo ≤ zudilinJTerm u v ∧ zudilinJTerm u v ≤ hi := by
  have hsu := trigammaSeries_shift hu 32
  have hsv := trigammaSeries_shift hv 32
  push_cast at hsu hsv
  have hlu := tailLow_le_trigammaSeries (x := 32 + u) (by linarith)
  have hhu := trigammaSeries_le_tailHigh (x := 32 + u) (by linarith)
  have hlv := tailLow_le_trigammaSeries (x := 32 + v) (by linarith)
  have hhv := trigammaSeries_le_tailHigh (x := 32 + v) (by linarith)
  have hsplit : (∑ k ∈ Finset.range 32, (1 / ((k : ℝ) + u) ^ 2 - 1 / ((k : ℝ) + v) ^ 2)) =
      (∑ k ∈ Finset.range 32, 1 / ((k : ℝ) + u) ^ 2)
        - ∑ k ∈ Finset.range 32, 1 / ((k : ℝ) + v) ^ 2 := by
    rw [Finset.sum_sub_distrib]
  unfold zudilinJTerm
  constructor
  · linarith
  · linarith

/-! ## The thirteen intervals -/

theorem jterm_1 : (520234257944252983689065 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (1 / 14) (1 / 12) ∧
    zudilinJTerm (1 / 14) (1 / 12) ≤ (520234257944252983730018 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_2 : (130389583445620342664907 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (1 / 7) (1 / 6) ∧
    zudilinJTerm (1 / 7) (1 / 6) ≤ (130389583445620342704788 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_3 : (58270372574725805776611 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (3 / 14) (1 / 4) ∧
    zudilinJTerm (3 / 14) (1 / 4) ≤ (58270372574725805815452 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_4 : (33060256155096201542528 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (2 / 7) (1 / 3) ∧
    zudilinJTerm (2 / 7) (1 / 3) ≤ (33060256155096201580359 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_5 : (16341288387977575824500 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (5 / 14) (2 / 5) ∧
    zudilinJTerm (5 / 14) (2 / 5) ≤ (16341288387977575861453 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_6 : (8871944612662719520212 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (3 / 7) (7 / 15) ∧
    zudilinJTerm (3 / 7) (7 / 15) ≤ (8871944612662719556309 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_7 : (5112396152887661962364 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (1 / 2) (8 / 15) ∧
    zudilinJTerm (1 / 2) (8 / 15) ≤ (5112396152887661997627 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_8 : (3052877839467000279792 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (4 / 7) (3 / 5) ∧
    zudilinJTerm (4 / 7) (3 / 5) ≤ (3052877839467000314241 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_9 : (1851441174764463544560 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (9 / 14) (2 / 3) ∧
    zudilinJTerm (9 / 14) (2 / 3) ≤ (1851441174764463578216 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_10 : (1116095029136323534615 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (5 / 7) (11 / 15) ∧
    zudilinJTerm (5 / 7) (11 / 15) ≤ (1116095029136323567497 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_11 : (648929409578163447514 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (11 / 14) (4 / 5) ∧
    zudilinJTerm (11 / 14) (4 / 5) ≤ (648929409578163479643 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_12 : (343386774024217566531 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (6 / 7) (13 / 15) ∧
    zudilinJTerm (6 / 7) (13 / 15) ≤ (343386774024217597925 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_13 : (139015249897499641177 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (13 / 14) (14 / 15) ∧
    zudilinJTerm (13 / 14) (14 / 15) ≤ (139015249897499671854 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

/-- `J = 77.943184475009095…`, to eighteen decimal places. -/
theorem zudilinJ_enclosure :
    (77943184475009095899 : ℝ) / 10 ^ 18 ≤ zudilinJ ∧
      zudilinJ ≤ (77943184475009095946 : ℝ) / 10 ^ 18 := by
  have h1 := jterm_1
  have h2 := jterm_2
  have h3 := jterm_3
  have h4 := jterm_4
  have h5 := jterm_5
  have h6 := jterm_6
  have h7 := jterm_7
  have h8 := jterm_8
  have h9 := jterm_9
  have h10 := jterm_10
  have h11 := jterm_11
  have h12 := jterm_12
  have h13 := jterm_13
  unfold zudilinJ
  constructor
  · linarith [h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1, h8.1, h9.1, h10.1, h11.1, h12.1, h13.1]
  · linarith [h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2, h8.2, h9.2, h10.2, h11.2, h12.2, h13.2]

/-! ## `π²`, `C₀`, `θ*` and `μ` -/

theorem pi_sq_gt : (98696044010893586188 : ℝ) / 10 ^ 19 < Real.pi ^ 2 := by
  have h : (314159265358979323846 : ℝ) / 10 ^ 20 < Real.pi := by
    have hd := Real.pi_gt_d20
    norm_num at hd
    norm_num
    linarith
  have h0 : (0 : ℝ) ≤ (314159265358979323846 : ℝ) / 10 ^ 20 := by norm_num
  have hsq := mul_self_lt_mul_self h0 h
  rw [← sq, ← sq] at hsq
  have hnum : (98696044010893586188 : ℝ) / 10 ^ 19 <
      ((314159265358979323846 : ℝ) / 10 ^ 20) ^ 2 := by norm_num
  linarith

theorem pi_sq_lt : Real.pi ^ 2 < (98696044010893586189 : ℝ) / 10 ^ 19 := by
  have h : Real.pi < (314159265358979323847 : ℝ) / 10 ^ 20 := by
    have hd := Real.pi_lt_d20
    norm_num at hd
    norm_num
    linarith
  have hsq := mul_self_lt_mul_self Real.pi_pos.le h
  rw [← sq, ← sq] at hsq
  have hnum : ((314159265358979323847 : ℝ) / 10 ^ 20) ^ 2 <
      (98696044010893586189 : ℝ) / 10 ^ 19 := by norm_num
  linarith

/-- `C₀ = 221.300088165005025…`, to eighteen decimal places. -/
theorem zudilinC0_enclosure :
    (221300088165005025116 : ℝ) / 10 ^ 18 ≤ zudilinC0 ∧
      zudilinC0 ≤ (221300088165005025132 : ℝ) / 10 ^ 18 := by
  have hJ := zudilinJ_enclosure
  have hppos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hA : 3 / Real.pi ^ 2 < 3 / ((98696044010893586188 : ℝ) / 10 ^ 19) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) pi_sq_gt
  have hB : 3 / ((98696044010893586189 : ℝ) / 10 ^ 19) < 3 / Real.pi ^ 2 :=
    div_lt_div_of_pos_left (by norm_num) hppos pi_sq_lt
  have hhi : 3 / Real.pi ^ 2 * (225 - zudilinJ) ≤
      3 / ((98696044010893586188 : ℝ) / 10 ^ 19) *
        (225 - (77943184475009095899 : ℝ) / 10 ^ 18) :=
    mul_le_mul hA.le (by linarith [hJ.1]) (by linarith [hJ.2]) (by norm_num)
  have hlo : 3 / ((98696044010893586189 : ℝ) / 10 ^ 19) *
      (225 - (77943184475009095946 : ℝ) / 10 ^ 18) ≤
      3 / Real.pi ^ 2 * (225 - zudilinJ) :=
    mul_le_mul hB.le (by linarith [hJ.2]) (by norm_num) (by positivity)
  have n1 : (221300088165005025116 : ℝ) / 10 ^ 18 ≤
      266 - 3 / ((98696044010893586188 : ℝ) / 10 ^ 19) *
        (225 - (77943184475009095899 : ℝ) / 10 ^ 18) := by norm_num
  have n2 : 266 - 3 / ((98696044010893586189 : ℝ) / 10 ^ 19) *
      (225 - (77943184475009095946 : ℝ) / 10 ^ 18) ≤
      (221300088165005025132 : ℝ) / 10 ^ 18 := by norm_num
  unfold zudilinC0
  constructor
  · linarith
  · linarith

theorem zudilinC0_pos' : 0 < zudilinC0 := by
  have h := zudilinC0_enclosure.1
  have : (0 : ℝ) < (221300088165005025116 : ℝ) / 10 ^ 18 := by norm_num
  linarith

/-- **`res:rational-base-threshold` / `long1049:res:region`, printed decimal.**
The long paper prints `θ* = 0.40568302138406054…`. -/
theorem printed_contour :
    (40568302138406054 : ℝ) / 10 ^ 17 < zudilinContour ∧
      zudilinContour < (40568302138406055 : ℝ) / 10 ^ 17 := by
  have h := zudilinC0_enclosure
  have hc1 : (0 : ℝ) < zudilinC1 := zudilinC1_pos
  unfold zudilinContour
  constructor
  · rw [lt_div_iff₀ hc1]
    have : zudilinC1 = 1091 / 2 := rfl
    rw [this]
    have hnum : (40568302138406054 : ℝ) / 10 ^ 17 * (1091 / 2) <
        (221300088165005025116 : ℝ) / 10 ^ 18 := by norm_num
    linarith [h.1]
  · rw [div_lt_iff₀ hc1]
    have : zudilinC1 = 1091 / 2 := rfl
    rw [this]
    have hnum : (221300088165005025132 : ℝ) / 10 ^ 18 <
        (40568302138406055 : ℝ) / 10 ^ 17 * (1091 / 2) := by norm_num
    linarith [h.2]

/-- **`res:rational-base-threshold`, printed decimal in the short paper.**
The short paper prints `θ* = 0.4056830213840605…`. -/
theorem printed_contour_short :
    (4056830213840605 : ℝ) / 10 ^ 16 < zudilinContour ∧
      zudilinContour < (4056830213840606 : ℝ) / 10 ^ 16 := by
  have h := printed_contour
  have n1 : (4056830213840605 : ℝ) / 10 ^ 16 ≤ (40568302138406054 : ℝ) / 10 ^ 17 := by
    norm_num
  have n2 : (40568302138406055 : ℝ) / 10 ^ 17 ≤ (4056830213840606 : ℝ) / 10 ^ 16 := by
    norm_num
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `μ = C₁/C₀`, the irrationality-exponent constant printed in the theorem. -/
noncomputable def paperMu : ℝ := zudilinC1 / zudilinC0

theorem paperMu_eq_inv : paperMu = 1 / zudilinContour := by
  unfold paperMu zudilinContour
  rw [one_div, inv_div]

theorem paperMu_pos : 0 < paperMu := div_pos zudilinC1_pos zudilinC0_pos'

/-- **`res:rational-base-threshold`, printed decimal of `μ`.**
The paper prints `μ = C₁/C₀ = 2.4649786835749750…`. -/
theorem printed_mu :
    (24649786835749750 : ℝ) / 10 ^ 16 < paperMu ∧
      paperMu < (24649786835749751 : ℝ) / 10 ^ 16 := by
  have h := zudilinC0_enclosure
  have hc0 : (0 : ℝ) < zudilinC0 := zudilinC0_pos'
  have hC1 : zudilinC1 = 1091 / 2 := rfl
  unfold paperMu
  rw [hC1]
  constructor
  · rw [lt_div_iff₀ hc0]
    have hstep : (24649786835749750 : ℝ) / 10 ^ 16 * zudilinC0 ≤
        (24649786835749750 : ℝ) / 10 ^ 16 * ((221300088165005025132 : ℝ) / 10 ^ 18) :=
      mul_le_mul_of_nonneg_left h.2 (by norm_num)
    have hnum : (24649786835749750 : ℝ) / 10 ^ 16 *
        ((221300088165005025132 : ℝ) / 10 ^ 18) < 1091 / 2 := by norm_num
    linarith
  · rw [div_lt_iff₀ hc0]
    have hstep : (24649786835749751 : ℝ) / 10 ^ 16 *
        ((221300088165005025116 : ℝ) / 10 ^ 18) ≤
        (24649786835749751 : ℝ) / 10 ^ 16 * zudilinC0 :=
      mul_le_mul_of_nonneg_left h.1 (by norm_num)
    have hnum : (1091 : ℝ) / 2 < (24649786835749751 : ℝ) / 10 ^ 16 *
        ((221300088165005025116 : ℝ) / 10 ^ 18) := by norm_num
    linarith

/-- The twenty-place enclosure of `θ*` used for `4^μ`. -/
theorem contour_enclosure :
    (40568302138406054100 : ℝ) / 10 ^ 20 ≤ zudilinContour ∧
      zudilinContour ≤ (40568302138406054104 : ℝ) / 10 ^ 20 := by
  have h := zudilinC0_enclosure
  have hc1 : (0 : ℝ) < zudilinC1 := zudilinC1_pos
  have hC1 : zudilinC1 = 1091 / 2 := rfl
  unfold zudilinContour
  rw [hC1]
  constructor
  · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1091 / 2)]
    have hnum : (40568302138406054100 : ℝ) / 10 ^ 20 * (1091 / 2) ≤
        (221300088165005025116 : ℝ) / 10 ^ 18 := by norm_num
    linarith [h.1]
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1091 / 2)]
    have hnum : (221300088165005025132 : ℝ) / 10 ^ 18 ≤
        (40568302138406054104 : ℝ) / 10 ^ 20 * (1091 / 2) := by norm_num
    linarith [h.2]

theorem contour_pos : 0 < zudilinContour := by
  have h := contour_enclosure.1
  have : (0 : ℝ) < (40568302138406054100 : ℝ) / 10 ^ 20 := by norm_num
  linarith

/-! ## `4^μ = 30.483515…` -/

/-- Mathlib's Taylor estimate for `log (1 - x)`, in explicit two-sided form. -/
theorem log_one_sub_between {x : ℝ} (hx : |x| < 1) (n : ℕ) {slo shi E lo hi : ℝ}
    (h1 : slo ≤ ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1))
    (h2 : ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1) ≤ shi)
    (h3 : |x| ^ (n + 1) / (1 - |x|) ≤ E)
    (h4 : lo ≤ -shi - E) (h5 : -slo + E ≤ hi) :
    lo ≤ Real.log (1 - x) ∧ Real.log (1 - x) ≤ hi := by
  have H := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_le] at H
  exact ⟨by linarith [H.2], by linarith [H.1]⟩

theorem log_split {y t : ℝ} (ht : 0 < t) (hy : y = 32 * t) :
    Real.log y = 5 * Real.log 2 + Real.log t := by
  subst hy
  rw [Real.log_mul (by norm_num) ht.ne', show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
    Real.log_pow]
  norm_num

theorem log_two_enclosure :
    (6931471805599453094162203 : ℝ) / 10 ^ 25 ≤ Real.log 2 ∧
      Real.log 2 ≤ (6931471805599453094182204 : ℝ) / 10 ^ 25 := by
  have habs : |(1 : ℝ) / 2| = 1 / 2 := abs_of_pos (by norm_num)
  have hx : |(1 : ℝ) / 2| < 1 := by rw [habs]; norm_num
  have h1 : (6931471805599453094172203 : ℝ) / 10 ^ 25 ≤
      ∑ i ∈ Finset.range 70, ((1 : ℝ) / 2) ^ (i + 1) / (i + 1) := by
    norm_num [Finset.sum_range_succ]
  have h2 : ∑ i ∈ Finset.range 70, ((1 : ℝ) / 2) ^ (i + 1) / (i + 1) ≤
      (6931471805599453094172204 : ℝ) / 10 ^ 25 := by
    norm_num [Finset.sum_range_succ]
  have h3 : |(1 : ℝ) / 2| ^ (70 + 1) / (1 - |(1 : ℝ) / 2|) ≤ (1 : ℝ) / 10 ^ 21 := by
    rw [habs]; norm_num
  have key := log_one_sub_between (lo := (-6931471805599453094182204 : ℝ) / 10 ^ 25)
    (hi := (-6931471805599453094162203 : ℝ) / 10 ^ 25) hx 70 h1 h2 h3
    (by norm_num) (by norm_num)
  have hlog : Real.log (1 - (1 : ℝ) / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog] at key
  exact ⟨by linarith [key.2], by linarith [key.1]⟩

theorem log_four_enclosure :
    (13862943611198906188324406 : ℝ) / 10 ^ 25 ≤ Real.log 4 ∧
      Real.log 4 ≤ (13862943611198906188364408 : ℝ) / 10 ^ 25 := by
  have h := log_two_enclosure
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  norm_num
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `log 30.483515 = 5 log 2 + log (1 - 303297/6400000)`. -/
theorem log_30483515_enclosure :
    (34171860456917396600789033 : ℝ) / 10 ^ 25 ≤ Real.log ((30483515 : ℝ) / 10 ^ 6) ∧
      Real.log ((30483515 : ℝ) / 10 ^ 6) ≤
        (34171860456917396602889039 : ℝ) / 10 ^ 25 := by
  have habs : |(303297 : ℝ) / 6400000| = 303297 / 6400000 := abs_of_pos (by norm_num)
  have hx : |(303297 : ℝ) / 6400000| < 1 := by rw [habs]; norm_num
  have h1 : (485498571079868869021981 : ℝ) / 10 ^ 25 ≤
      ∑ i ∈ Finset.range 14, ((303297 : ℝ) / 6400000) ^ (i + 1) / (i + 1) := by
    norm_num [Finset.sum_range_succ]
  have h2 : ∑ i ∈ Finset.range 14, ((303297 : ℝ) / 6400000) ^ (i + 1) / (i + 1) ≤
      (485498571079868869021982 : ℝ) / 10 ^ 25 := by
    norm_num [Finset.sum_range_succ]
  have h3 : |(303297 : ℝ) / 6400000| ^ (14 + 1) / (1 - |(303297 : ℝ) / 6400000|) ≤
      (1 : ℝ) / 10 ^ 19 := by
    rw [habs]; norm_num
  have key := log_one_sub_between (lo := (-485498571079868870021982 : ℝ) / 10 ^ 25)
    (hi := (-485498571079868868021981 : ℝ) / 10 ^ 25) hx 14 h1 h2 h3
    (by norm_num) (by norm_num)
  have hsplit : Real.log ((30483515 : ℝ) / 10 ^ 6) =
      5 * Real.log 2 + Real.log (1 - (303297 : ℝ) / 6400000) :=
    log_split (by norm_num) (by norm_num)
  have h2e := log_two_enclosure
  rw [hsplit]
  exact ⟨by linarith [key.1, h2e.1], by linarith [key.2, h2e.2]⟩

/-- `log 30.483516 = 5 log 2 + log (1 - 379121/8000000)`. -/
theorem log_30483516_enclosure :
    (34171860784963549938976057 : ℝ) / 10 ^ 25 ≤ Real.log ((30483516 : ℝ) / 10 ^ 6) ∧
      Real.log ((30483516 : ℝ) / 10 ^ 6) ≤
        (34171860784963549941076063 : ℝ) / 10 ^ 25 := by
  have habs : |(379121 : ℝ) / 8000000| = 379121 / 8000000 := abs_of_pos (by norm_num)
  have hx : |(379121 : ℝ) / 8000000| < 1 := by rw [habs]; norm_num
  have h1 : (485498243033715530834957 : ℝ) / 10 ^ 25 ≤
      ∑ i ∈ Finset.range 14, ((379121 : ℝ) / 8000000) ^ (i + 1) / (i + 1) := by
    norm_num [Finset.sum_range_succ]
  have h2 : ∑ i ∈ Finset.range 14, ((379121 : ℝ) / 8000000) ^ (i + 1) / (i + 1) ≤
      (485498243033715530834958 : ℝ) / 10 ^ 25 := by
    norm_num [Finset.sum_range_succ]
  have h3 : |(379121 : ℝ) / 8000000| ^ (14 + 1) / (1 - |(379121 : ℝ) / 8000000|) ≤
      (1 : ℝ) / 10 ^ 19 := by
    rw [habs]; norm_num
  have key := log_one_sub_between (lo := (-485498243033715531834958 : ℝ) / 10 ^ 25)
    (hi := (-485498243033715529834957 : ℝ) / 10 ^ 25) hx 14 h1 h2 h3
    (by norm_num) (by norm_num)
  have hsplit : Real.log ((30483516 : ℝ) / 10 ^ 6) =
      5 * Real.log 2 + Real.log (1 - (379121 : ℝ) / 8000000) :=
    log_split (by norm_num) (by norm_num)
  have h2e := log_two_enclosure
  rw [hsplit]
  exact ⟨by linarith [key.1, h2e.1], by linarith [key.2, h2e.2]⟩

theorem lt_four_rpow {y c : ℝ} (hy : 0 < y) (h : Real.log y < c * Real.log 4) :
    y < (4 : ℝ) ^ c := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc y = Real.exp (Real.log y) := (Real.exp_log hy).symm
    _ < Real.exp (Real.log 4 * c) := Real.exp_lt_exp.mpr (by linarith)

theorem four_rpow_lt {y c : ℝ} (hy : 0 < y) (h : c * Real.log 4 < Real.log y) :
    (4 : ℝ) ^ c < y := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc Real.exp (Real.log 4 * c) < Real.exp (Real.log y) := Real.exp_lt_exp.mpr (by linarith)
    _ = y := Real.exp_log hy

/-- **`long1049:res:31over4`, printed decimal of `4^μ`.**
The paper prints `4^μ = 30.483515…`. -/
theorem printed_four_rpow_mu :
    (30483515 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperMu ∧
      (4 : ℝ) ^ paperMu < (30483516 : ℝ) / 10 ^ 6 := by
  have hth := contour_enclosure
  have hthpos := contour_pos
  have h4 := log_four_enclosure
  have hA := log_30483515_enclosure
  have hB := log_30483516_enclosure
  have hApos : (0 : ℝ) < Real.log ((30483515 : ℝ) / 10 ^ 6) := Real.log_pos (by norm_num)
  constructor
  · refine lt_four_rpow (by norm_num) ?_
    rw [paperMu_eq_inv, div_mul_eq_mul_div, one_mul, lt_div_iff₀ hthpos]
    have hstep : zudilinContour * Real.log ((30483515 : ℝ) / 10 ^ 6) ≤
        ((40568302138406054104 : ℝ) / 10 ^ 20) *
          ((34171860456917396602889039 : ℝ) / 10 ^ 25) :=
      mul_le_mul hth.2 hA.2 hApos.le (by norm_num)
    have hnum : ((40568302138406054104 : ℝ) / 10 ^ 20) *
        ((34171860456917396602889039 : ℝ) / 10 ^ 25) <
          (13862943611198906188324406 : ℝ) / 10 ^ 25 := by norm_num
    linarith [h4.1]
  · refine four_rpow_lt (by norm_num) ?_
    rw [paperMu_eq_inv, div_mul_eq_mul_div, one_mul, div_lt_iff₀ hthpos]
    have hstep : ((40568302138406054100 : ℝ) / 10 ^ 20) *
        ((34171860784963549938976057 : ℝ) / 10 ^ 25) ≤
          zudilinContour * Real.log ((30483516 : ℝ) / 10 ^ 6) :=
      mul_le_mul hth.1 hB.1 (by norm_num) hthpos.le
    have hnum : (13862943611198906188364408 : ℝ) / 10 ^ 25 <
        ((40568302138406054100 : ℝ) / 10 ^ 20) *
          ((34171860784963549938976057 : ℝ) / 10 ^ 25) := by norm_num
    linarith [h4.2]

/-- The left half of the paper's chain `4^μ < 31 < 4^{μ_BV}`, for the same `μ`
whose decimal is pinned above. -/
theorem four_rpow_mu_lt_thirtyOne : (4 : ℝ) ^ paperMu < 31 := by
  have h := printed_four_rpow_mu.2
  have : (30483516 : ℝ) / 10 ^ 6 < 31 := by norm_num
  linarith

end ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.four_rpow_mu_lt_thirtyOne
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow_step
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailHigh_step
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow_le_trigammaSeries
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_shift
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.jterm_bracket
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinJ_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinC0_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour_short
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_mu
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.contour_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.log_30483515_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.log_30483516_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_four_rpow_mu
