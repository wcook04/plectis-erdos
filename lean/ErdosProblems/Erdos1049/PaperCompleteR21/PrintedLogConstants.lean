import ErdosProblems.Erdos1049.RationalBaseContour
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Erdős #1049: the printed decimals that depend only on `log` and `π`

`long1049:res:31over4` prints four truncated decimal constants whose value does
not involve Zudilin's trigamma constant `J`:

* `log 4 / log 31 = 0.4036981731641997…`;
* `1/2 - 1/π² = 0.3986788163576622…`, the Bundschuh–Väänänen cutoff;
* `μ_BV = 2π²/(π² - 2) = 2.508284761994…`;
* `4^{μ_BV} = 32.369642…`.

Each is proved here as the two-sided bound that pins exactly the digits the
paper prints: for a printed `k`-digit truncation `d`, the statement is
`d < x < d + 10^{-k}`.

The logarithms are certified from Mathlib's Taylor estimate
`Real.abs_log_sub_add_sum_range_le` for `log (1 - x)` with its explicit
remainder, applied at `x = 1/2` (seventy terms, giving `log 2` to `10^{-21}`)
and at the small arguments `1 - y/32` for the values `y` near `32`.  The value
of `π` comes from `Real.pi_gt_d20` / `Real.pi_lt_d20`.

No floating point and no `native_decide` is used.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## Certified logarithms -/

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

/-- `log (32 t) = 5 log 2 + log t`. -/
theorem log_split {y t : ℝ} (ht : 0 < t) (hy : y = 32 * t) :
    Real.log y = 5 * Real.log 2 + Real.log t := by
  subst hy
  rw [Real.log_mul (by norm_num) ht.ne', show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
    Real.log_pow]
  norm_num

/-- `log 2` to twenty-five decimal places, from seventy Taylor terms at `x = 1/2`
and the remainder bound `2^{-70} < 10^{-21}`. -/
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

/-- `log 4 = 2 log 2`. -/
theorem log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  norm_num

theorem log_four_enclosure :
    (13862943611198906188324406 : ℝ) / 10 ^ 25 ≤ Real.log 4 ∧
      Real.log 4 ≤ (13862943611198906188364408 : ℝ) / 10 ^ 25 := by
  have h := log_two_enclosure
  rw [log_four_eq]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

theorem log_thirtyOne_pos : 0 < Real.log 31 := Real.log_pos (by norm_num)

/-- `log 31 = 5 log 2 + log (1 - 1/32)`, to twenty-five decimal places. -/
theorem log_thirtyOne_enclosure :
    (34339872044851462459240070 : ℝ) / 10 ^ 25 ≤ Real.log 31 ∧
      Real.log 31 ≤ (34339872044851462459342076 : ℝ) / 10 ^ 25 := by
  have habs : |(1 : ℝ) / 32| = 1 / 32 := abs_of_pos (by norm_num)
  have hx : |(1 : ℝ) / 32| < 1 := by rw [habs]; norm_num
  have h1 : (317486983145803011569944 : ℝ) / 10 ^ 25 ≤
      ∑ i ∈ Finset.range 14, ((1 : ℝ) / 32) ^ (i + 1) / (i + 1) := by
    norm_num [Finset.sum_range_succ]
  have h2 : ∑ i ∈ Finset.range 14, ((1 : ℝ) / 32) ^ (i + 1) / (i + 1) ≤
      (317486983145803011569945 : ℝ) / 10 ^ 25 := by
    norm_num [Finset.sum_range_succ]
  have h3 : |(1 : ℝ) / 32| ^ (14 + 1) / (1 - |(1 : ℝ) / 32|) ≤ (1 : ℝ) / 10 ^ 22 := by
    rw [habs]; norm_num
  have key := log_one_sub_between (lo := (-317486983145803011570945 : ℝ) / 10 ^ 25)
    (hi := (-317486983145803011568944 : ℝ) / 10 ^ 25) hx 14 h1 h2 h3
    (by norm_num) (by norm_num)
  have hsplit : Real.log 31 = 5 * Real.log 2 + Real.log (1 - (1 : ℝ) / 32) :=
    log_split (by norm_num) (by norm_num)
  have h2e := log_two_enclosure
  rw [hsplit]
  exact ⟨by linarith [key.1, h2e.1], by linarith [key.2, h2e.2]⟩

/-- **`long1049:res:31over4`, printed decimal of `log 4 / log 31`.**
The paper prints `log 4 / log 31 = 0.4036981731641997…`. -/
theorem printed_log_ratio :
    (4036981731641997 : ℝ) / 10 ^ 16 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (4036981731641998 : ℝ) / 10 ^ 16 := by
  have hp := log_thirtyOne_pos
  have h4 := log_four_enclosure
  have h31 := log_thirtyOne_enclosure
  constructor
  · rw [lt_div_iff₀ hp]
    have hstep : (4036981731641997 : ℝ) / 10 ^ 16 * Real.log 31 ≤
        (4036981731641997 : ℝ) / 10 ^ 16 * ((34339872044851462459342076 : ℝ) / 10 ^ 25) :=
      mul_le_mul_of_nonneg_left h31.2 (by norm_num)
    have hnum : (4036981731641997 : ℝ) / 10 ^ 16 *
        ((34339872044851462459342076 : ℝ) / 10 ^ 25) <
        (13862943611198906188324406 : ℝ) / 10 ^ 25 := by norm_num
    linarith [h4.1]
  · rw [div_lt_iff₀ hp]
    have hstep : (4036981731641998 : ℝ) / 10 ^ 16 *
        ((34339872044851462459240070 : ℝ) / 10 ^ 25) ≤
        (4036981731641998 : ℝ) / 10 ^ 16 * Real.log 31 :=
      mul_le_mul_of_nonneg_left h31.1 (by norm_num)
    have hnum : (13862943611198906188364408 : ℝ) / 10 ^ 25 <
        (4036981731641998 : ℝ) / 10 ^ 16 *
          ((34339872044851462459240070 : ℝ) / 10 ^ 25) := by norm_num
    linarith [h4.2]

/-! ## `π²`, the Bundschuh–Väänänen cutoff, and `μ_BV` -/

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

theorem pi_sq_pos' : (0 : ℝ) < Real.pi ^ 2 := by positivity

/-- The Bundschuh–Väänänen cutoff `1/2 - 1/π²` to twenty decimal places. -/
theorem bv_cutoff_enclosure :
    (39867881635766222855 : ℝ) / 10 ^ 20 ≤ 1 / 2 - 1 / Real.pi ^ 2 ∧
      1 / 2 - 1 / Real.pi ^ 2 ≤ (39867881635766222856 : ℝ) / 10 ^ 20 := by
  have h1 := pi_sq_gt
  have h2 := pi_sq_lt
  have hlo : 1 / Real.pi ^ 2 < 1 / ((98696044010893586188 : ℝ) / 10 ^ 19) :=
    one_div_lt_one_div_of_lt (by norm_num) h1
  have hhi : 1 / ((98696044010893586189 : ℝ) / 10 ^ 19) < 1 / Real.pi ^ 2 :=
    one_div_lt_one_div_of_lt pi_sq_pos' h2
  have n1 : (39867881635766222855 : ℝ) / 10 ^ 20 ≤
      1 / 2 - 1 / ((98696044010893586188 : ℝ) / 10 ^ 19) := by norm_num
  have n2 : 1 / 2 - 1 / ((98696044010893586189 : ℝ) / 10 ^ 19) ≤
      (39867881635766222856 : ℝ) / 10 ^ 20 := by norm_num
  exact ⟨by linarith, by linarith⟩

theorem bv_cutoff_pos : (0 : ℝ) < 1 / 2 - 1 / Real.pi ^ 2 := by
  have h := bv_cutoff_enclosure.1
  have : (0 : ℝ) < (39867881635766222855 : ℝ) / 10 ^ 20 := by norm_num
  linarith

/-- **`long1049:res:31over4`, printed decimal of `1/2 - 1/π²`.**
The paper prints `1/2 - 1/π² = 0.3986788163576622…`. -/
theorem printed_bv_cutoff :
    (3986788163576622 : ℝ) / 10 ^ 16 < 1 / 2 - 1 / Real.pi ^ 2 ∧
      1 / 2 - 1 / Real.pi ^ 2 < (3986788163576623 : ℝ) / 10 ^ 16 := by
  have h := bv_cutoff_enclosure
  have n1 : (3986788163576622 : ℝ) / 10 ^ 16 < (39867881635766222855 : ℝ) / 10 ^ 20 := by
    norm_num
  have n2 : (39867881635766222856 : ℝ) / 10 ^ 20 < (3986788163576623 : ℝ) / 10 ^ 16 := by
    norm_num
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `μ_BV = 2π²/(π² - 2)`, the Bundschuh–Väänänen exponent. -/
noncomputable def paperBvMu : ℝ := 2 * Real.pi ^ 2 / (Real.pi ^ 2 - 2)

theorem bv_cutoff_eq : 1 / 2 - 1 / Real.pi ^ 2 = (Real.pi ^ 2 - 2) / (2 * Real.pi ^ 2) := by
  have hp : (0 : ℝ) < Real.pi ^ 2 := pi_sq_pos'
  field_simp

theorem paperBvMu_eq : paperBvMu = 1 / (1 / 2 - 1 / Real.pi ^ 2) := by
  rw [bv_cutoff_eq, one_div_div]
  rfl

/-- **`long1049:res:31over4`, printed decimal of `μ_BV`.**
The paper prints `μ_BV = 2π²/(π² - 2) = 2.508284761994…`. -/
theorem printed_bvMu :
    (2508284761994 : ℝ) / 10 ^ 12 < paperBvMu ∧
      paperBvMu < (2508284761995 : ℝ) / 10 ^ 12 := by
  have h := bv_cutoff_enclosure
  have hpos := bv_cutoff_pos
  rw [paperBvMu_eq]
  constructor
  · have hstep : 1 / ((39867881635766222856 : ℝ) / 10 ^ 20) ≤
        1 / (1 / 2 - 1 / Real.pi ^ 2) :=
      one_div_le_one_div_of_le hpos h.2
    have hnum : (2508284761994 : ℝ) / 10 ^ 12 <
        1 / ((39867881635766222856 : ℝ) / 10 ^ 20) := by norm_num
    linarith
  · have hstep : 1 / (1 / 2 - 1 / Real.pi ^ 2) ≤
        1 / ((39867881635766222855 : ℝ) / 10 ^ 20) :=
      one_div_le_one_div_of_le (by norm_num) h.1
    have hnum : 1 / ((39867881635766222855 : ℝ) / 10 ^ 20) <
        (2508284761995 : ℝ) / 10 ^ 12 := by norm_num
    linarith

/-! ## `4^{μ_BV} = 32.369642…` -/

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

/-- `log 32.369642 = 5 log 2 + log (1 - x)` with `x = -184821/16000000`. -/
theorem log_32369642_enclosure :
    (34772210082538870844368173 : ℝ) / 10 ^ 25 ≤ Real.log ((32369642 : ℝ) / 10 ^ 6) ∧
      Real.log ((32369642 : ℝ) / 10 ^ 6) ≤
        (34772210082538870844468181 : ℝ) / 10 ^ 25 := by
  have habs : |(-184821 : ℝ) / 16000000| = 184821 / 16000000 := by
    rw [abs_of_nonpos (by norm_num)]; ring
  have hx : |(-184821 : ℝ) / 16000000| < 1 := by rw [habs]; norm_num
  have h1 : (-114851054541605373557160 : ℝ) / 10 ^ 25 ≤
      ∑ i ∈ Finset.range 14, ((-184821 : ℝ) / 16000000) ^ (i + 1) / (i + 1) := by
    norm_num [Finset.sum_range_succ]
  have h2 : ∑ i ∈ Finset.range 14, ((-184821 : ℝ) / 16000000) ^ (i + 1) / (i + 1) ≤
      (-114851054541605373557159 : ℝ) / 10 ^ 25 := by
    norm_num [Finset.sum_range_succ]
  have h3 : |(-184821 : ℝ) / 16000000| ^ (14 + 1) / (1 - |(-184821 : ℝ) / 16000000|) ≤
      (1 : ℝ) / 10 ^ 25 := by
    rw [habs]; norm_num
  have key := log_one_sub_between (lo := (114851054541605373557158 : ℝ) / 10 ^ 25)
    (hi := (114851054541605373557161 : ℝ) / 10 ^ 25) hx 14 h1 h2 h3
    (by norm_num) (by norm_num)
  have hsplit : Real.log ((32369642 : ℝ) / 10 ^ 6) =
      5 * Real.log 2 + Real.log (1 - (-184821 : ℝ) / 16000000) :=
    log_split (by norm_num) (by norm_num)
  have h2e := log_two_enclosure
  rw [hsplit]
  exact ⟨by linarith [key.1, h2e.1], by linarith [key.2, h2e.2]⟩

/-- `log 32.369643 = 5 log 2 + log (1 - x)` with `x = -369643/32000000`. -/
theorem log_32369643_enclosure :
    (34772210391470302509083061 : ℝ) / 10 ^ 25 ≤ Real.log ((32369643 : ℝ) / 10 ^ 6) ∧
      Real.log ((32369643 : ℝ) / 10 ^ 6) ≤
        (34772210391470302509183069 : ℝ) / 10 ^ 25 := by
  have habs : |(-369643 : ℝ) / 32000000| = 369643 / 32000000 := by
    rw [abs_of_nonpos (by norm_num)]; ring
  have hx : |(-369643 : ℝ) / 32000000| < 1 := by rw [habs]; norm_num
  have h1 : (-114851363473037038272048 : ℝ) / 10 ^ 25 ≤
      ∑ i ∈ Finset.range 14, ((-369643 : ℝ) / 32000000) ^ (i + 1) / (i + 1) := by
    norm_num [Finset.sum_range_succ]
  have h2 : ∑ i ∈ Finset.range 14, ((-369643 : ℝ) / 32000000) ^ (i + 1) / (i + 1) ≤
      (-114851363473037038272047 : ℝ) / 10 ^ 25 := by
    norm_num [Finset.sum_range_succ]
  have h3 : |(-369643 : ℝ) / 32000000| ^ (14 + 1) / (1 - |(-369643 : ℝ) / 32000000|) ≤
      (1 : ℝ) / 10 ^ 25 := by
    rw [habs]; norm_num
  have key := log_one_sub_between (lo := (114851363473037038272046 : ℝ) / 10 ^ 25)
    (hi := (114851363473037038272049 : ℝ) / 10 ^ 25) hx 14 h1 h2 h3
    (by norm_num) (by norm_num)
  have hsplit : Real.log ((32369643 : ℝ) / 10 ^ 6) =
      5 * Real.log 2 + Real.log (1 - (-369643 : ℝ) / 32000000) :=
    log_split (by norm_num) (by norm_num)
  have h2e := log_two_enclosure
  rw [hsplit]
  exact ⟨by linarith [key.1, h2e.1], by linarith [key.2, h2e.2]⟩

/-- **`long1049:res:31over4`, printed decimal of `4^{μ_BV}`.**
The paper prints `4^{μ_BV} = 32.369642…`. -/
theorem printed_four_rpow_bvMu :
    (32369642 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperBvMu ∧
      (4 : ℝ) ^ paperBvMu < (32369643 : ℝ) / 10 ^ 6 := by
  have hr := bv_cutoff_enclosure
  have hrpos := bv_cutoff_pos
  have h4 := log_four_enclosure
  have hA := log_32369642_enclosure
  have hB := log_32369643_enclosure
  have hApos : (0 : ℝ) < Real.log ((32369642 : ℝ) / 10 ^ 6) := Real.log_pos (by norm_num)
  constructor
  · refine lt_four_rpow (by norm_num) ?_
    rw [paperBvMu_eq, div_mul_eq_mul_div, one_mul, lt_div_iff₀ hrpos]
    have hstep : (1 / 2 - 1 / Real.pi ^ 2) * Real.log ((32369642 : ℝ) / 10 ^ 6) ≤
        ((39867881635766222856 : ℝ) / 10 ^ 20) *
          ((34772210082538870844468181 : ℝ) / 10 ^ 25) :=
      mul_le_mul hr.2 hA.2 hApos.le (by norm_num)
    have hnum : ((39867881635766222856 : ℝ) / 10 ^ 20) *
        ((34772210082538870844468181 : ℝ) / 10 ^ 25) <
          (13862943611198906188324406 : ℝ) / 10 ^ 25 := by norm_num
    linarith [h4.1]
  · refine four_rpow_lt (by norm_num) ?_
    rw [paperBvMu_eq, div_mul_eq_mul_div, one_mul, div_lt_iff₀ hrpos]
    have hstep : ((39867881635766222855 : ℝ) / 10 ^ 20) *
        ((34772210391470302509083061 : ℝ) / 10 ^ 25) ≤
          (1 / 2 - 1 / Real.pi ^ 2) * Real.log ((32369643 : ℝ) / 10 ^ 6) :=
      mul_le_mul hr.1 hB.1 (by norm_num) hrpos.le
    have hnum : (13862943611198906188364408 : ℝ) / 10 ^ 25 <
        ((39867881635766222855 : ℝ) / 10 ^ 20) *
          ((34772210391470302509083061 : ℝ) / 10 ^ 25) := by norm_num
    linarith [h4.2]

end ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.log_two_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.log_four_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.log_thirtyOne_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_log_ratio
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.pi_sq_gt
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.pi_sq_lt
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.bv_cutoff_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bv_cutoff
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bvMu
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.log_32369642_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.log_32369643_enclosure
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_four_rpow_bvMu
