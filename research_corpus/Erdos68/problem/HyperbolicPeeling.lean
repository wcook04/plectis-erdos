import ErdosProblems.Erdos68.PrimeZeroBranch
import ErdosProblems.Erdos68.DivisorFactorialCentre
import ErdosProblems.Erdos68.FiniteDefectAutomaton

/-!
# Erdős #68: the hyperbolic peeling, and the tail–centre collision normal form

`BinaryCarryNormalForm` proves the wrap-bit law for an *abstract* sequence
`T_m`, and states explicitly that identifying that `T_m` with a genuine
factorial-gap tail "is not part of this module".  `DivisorFactorialCentre`
carries the finite rational centre
`F_m = m!·∑_{2≤n≤m} 1/((n!)^⌊m/n⌋ (n!-1))` and the divisor-factorial
coefficients `C_m`, but only as recurrence artefacts.

This module supplies the missing identification, and it is a *finite* one — no
Fubini, no double `tsum`, no regrouping of a doubly-indexed family.

## The peeling

Cut the hyperbola `nj ≤ m` out of each geometric expansion separately.  For a
single `n`, with `K = ⌊m/n⌋`, the finite geometric identity

```
  m!/(n!-1) = ∑_{j=1}^{K} m!/(n!)^j  +  m!/((n!)^K (n!-1))
```

is exact (`factorial_div_sub_one_eq_peel`).  Summing over `2 ≤ n ≤ m` and
adding the analytic tail gives

```
  m!·S = peeledHead m + residualCentre m + factorialGapScaledTail m
```

(`factorial_mul_series_eq_peeledHead_add_centre_add_scaledTail`), where
`peeledHead m` is a genuine natural number because `(n!)^j ∣ m!` whenever
`nj ≤ m` (`factorial_pow_dvd_factorial_of_mul_le`).

So the finite centre was never a failed approximation to a canonical
remainder.  It is one of the three exact regions of a hyperbolic partition of
the lattice `{(n,j) : n ≥ 2, j ≥ 1}`:

* `nj ≤ m` — the integral head `peeledHead m`;
* `n ≤ m < nj` — the finite residual centre `residualCentre m`;
* `m < n` — the true analytic tail `factorialGapScaledTail m`.

## The consequence

With `E_m := factorialGapScaledTail m - centreGap residualCentre m` the
identity becomes `m!·S = peeledHead m + ⌈F_m⌉ + E_m` with `|E_m| < 1`, so

* `signedCentreTailError_eq_zero_iff_exists_int` — `E_m = 0` iff `m!·S ∈ ℤ`;
* `not_irrational_iff_exists_signedCentreTailError_eq_zero` — rationality of
  `S` is **one synchronisation event** between the true infinite tail and the
  ceiling gap of the finite rational centre;
* `not_irrational_iff_eventually_centreDefectCode_eq_one` — equivalently, the
  finite integer defect digit `d_m` is eventually constantly `1`.

The last normal form mentions no infinite object at all: `residualCentre`,
`centreCeil` and `factorialCoeffNat` are finite rational/integer data.

## Tail width

`factorialGapScaledTail_lt_two_div` is complemented on the lower side by
`one_div_succ_lt_factorialGapScaledTail`: `1/(m+1) < T_m`.  Together these pin
`T_m` into `(1/(m+1), 2/m)`, so at a collision the wholly finite centre gap is
confined to that same shrinking window
(`centreGap_window_of_signedCentreTailError_eq_zero`).

## Claim ceiling

**Erdős #68 remains open.**  This module proves the packet's named missing
producer — the identification of the abstract `T_m` with the actual scaled
factorial-gap tail — and converts it into a finite-data normal form.  It does
**not** prove that `E_m` never vanishes, nor that `d_m` is not eventually `1`.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-! ## Divisibility: the head is integral -/

/-- `(n!)^j` divides `(n·j)!`.  Induction on `j` through
`Nat.factorial_mul_factorial_dvd_factorial_add`. -/
theorem factorial_pow_dvd_factorial_mul (n j : ℕ) :
    (n.factorial) ^ j ∣ (n * j).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : (n * j).factorial * n.factorial ∣ (n * j + n).factorial :=
        Nat.factorial_mul_factorial_dvd_factorial_add _ _
      have hmul : (n.factorial) ^ j * n.factorial ∣ (n * j).factorial * n.factorial :=
        mul_dvd_mul ih dvd_rfl
      have : (n.factorial) ^ (j + 1) ∣ (n * j + n).factorial := by
        rw [pow_succ]
        exact hmul.trans hstep
      rwa [show n * j + n = n * (j + 1) by ring] at this

/-- `(n!)^j` divides `m!` whenever the hyperbolic constraint `n·j ≤ m` holds. -/
theorem factorial_pow_dvd_factorial_of_mul_le {m n j : ℕ} (h : n * j ≤ m) :
    (n.factorial) ^ j ∣ m.factorial :=
  (factorial_pow_dvd_factorial_mul n j).trans (Nat.factorial_dvd_factorial h)

/-- Membership in the head index rectangle implies the hyperbolic constraint. -/
theorem mul_le_of_mem_peelRange {m n j : ℕ} (hn : 1 ≤ n)
    (hj : j ∈ Finset.Icc 1 (m / n)) : n * j ≤ m := by
  have hjle : j ≤ m / n := (Finset.mem_Icc.mp hj).2
  calc n * j ≤ n * (m / n) := Nat.mul_le_mul_left _ hjle
    _ = m / n * n := Nat.mul_comm _ _
    _ ≤ m := Nat.div_mul_le_self m n

/-! ## The one-term finite geometric peel -/

/-- Exact finite geometric peel: the whole `1/(x-1)` splits into `K` integral
powers plus one residual centre term. -/
theorem geom_peel (a x : ℚ) (hx : x ≠ 0) (hx1 : x - 1 ≠ 0) (K : ℕ) :
    a / (x - 1) = (∑ j ∈ Finset.Icc 1 K, a / x ^ j) + a / (x ^ K * (x - 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih]
      have hxK : x ^ K ≠ 0 := pow_ne_zero _ hx
      have hxK1 : x ^ (K + 1) ≠ 0 := pow_ne_zero _ hx
      field_simp
      ring

/-! ## The peeled head -/

/-- The integral head of the hyperbolic peeling, as a natural number:
`∑_{2≤n≤m} ∑_{1≤j≤⌊m/n⌋} m!/(n!)^j`.  Every quotient is exact. -/
def peeledHead (m : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 m, ∑ j ∈ Finset.Icc 1 (m / n), m.factorial / (n.factorial) ^ j

/-- Rational form of the head. -/
def peeledHeadRat (m : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 2 m, ∑ j ∈ Finset.Icc 1 (m / n),
    (m.factorial : ℚ) / (n.factorial : ℚ) ^ j

theorem peeledHeadRat_eq_natCast (m : ℕ) :
    peeledHeadRat m = (peeledHead m : ℚ) := by
  unfold peeledHeadRat peeledHead
  push_cast
  refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun j hj => ?_
  have hn1 : 1 ≤ n := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  have hdvd : (n.factorial) ^ j ∣ m.factorial :=
    factorial_pow_dvd_factorial_of_mul_le (mul_le_of_mem_peelRange hn1 hj)
  have hne : ((n.factorial : ℚ)) ^ j ≠ 0 := by positivity
  rw [Nat.cast_div hdvd (by exact_mod_cast hne)]
  push_cast
  ring

/-! ## The peeling identity -/

/-- **One row of the peeling.**  For `2 ≤ n`, the full weight `m!/(n!-1)`
splits exactly into its integral head and its residual centre term. -/
theorem factorial_div_sub_one_eq_peel {m n : ℕ} (hn : 2 ≤ n) :
    (m.factorial : ℚ) / ((n.factorial : ℚ) - 1) =
      (∑ j ∈ Finset.Icc 1 (m / n), (m.factorial : ℚ) / (n.factorial : ℚ) ^ j) +
        residualCentreTerm m n := by
  have hfacGt : (1 : ℕ) < n.factorial := Nat.one_lt_factorial.mpr hn
  have hx1 : ((n.factorial : ℚ)) - 1 ≠ 0 := by
    have : (1 : ℚ) < (n.factorial : ℚ) := by exact_mod_cast hfacGt
    linarith
  have hx : ((n.factorial : ℚ)) ≠ 0 := by positivity
  simpa [residualCentreTerm] using
    geom_peel (m.factorial : ℚ) (n.factorial : ℚ) hx hx1 (m / n)

/-- The finite prefix of the Erdős series, scaled by `m!`, splits into the
integral head and the finite residual centre. -/
theorem factorial_mul_prefix_eq_peeledHead_add_centre (m : ℕ) :
    ∑ n ∈ Finset.Icc 2 m, (m.factorial : ℚ) / ((n.factorial : ℚ) - 1) =
      (peeledHead m : ℚ) + residualCentre m := by
  rw [← peeledHeadRat_eq_natCast]
  unfold peeledHeadRat residualCentre
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  exact factorial_div_sub_one_eq_peel (Finset.mem_Icc.mp hn).1

/-- **The hyperbolic peeling.**  The scaled Erdős #68 series is exactly the sum
of its integral head, its finite rational centre, and the *actual* scaled
factorial-gap tail.  This is the identification the wrap-bit module leaves
open. -/
theorem factorial_mul_series_eq_peeledHead_add_centre_add_scaledTail
    {m : ℕ} (hm : 2 ≤ m) :
    (m.factorial : ℝ) * _root_.Erdos68.factorialGapSeries =
      (peeledHead m : ℝ) + ((residualCentre m : ℚ) : ℝ) +
        factorialGapScaledTail m := by
  have hsplit := _root_.Erdos68.factorialGapSeries_eq_sum_add_tail hm
  have hprefix := factorial_mul_prefix_eq_peeledHead_add_centre m
  have hprefixR :
      ∑ n ∈ Finset.Icc 2 m,
          (m.factorial : ℝ) / ((n.factorial : ℝ) - 1) =
        (peeledHead m : ℝ) + ((residualCentre m : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hprefix
    push_cast at this
    simpa using this
  rw [hsplit]
  have hcast : ∀ d : ℕ,
      (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) =
        (1 : ℝ) / ((d.factorial : ℝ) - 1) := by
    intro d; norm_num
  rw [Finset.sum_congr rfl fun d _ => hcast d]
  rw [mul_add, Finset.mul_sum]
  have hterm : ∀ d : ℕ,
      (m.factorial : ℝ) * ((1 : ℝ) / ((d.factorial : ℝ) - 1)) =
        (m.factorial : ℝ) / ((d.factorial : ℝ) - 1) := by
    intro d; ring
  rw [Finset.sum_congr rfl fun d _ => hterm d, hprefixR]
  unfold factorialGapScaledTail
  ring

/-! ## The tail–centre collision -/

/-- The signed synchronisation error between the actual scaled tail and the
ceiling gap of the finite rational centre. -/
noncomputable def signedCentreTailError (m : ℕ) : ℝ :=
  factorialGapScaledTail m - ((centreGap residualCentre m : ℚ) : ℝ)

theorem abs_signedCentreTailError_lt_one {m : ℕ} (hm : 2 ≤ m) :
    |signedCentreTailError m| < 1 := by
  have hTpos := factorialGapScaledTail_pos hm
  have hTlt := factorialGapScaledTail_lt_one hm
  have hgnn : (0 : ℝ) ≤ ((centreGap residualCentre m : ℚ) : ℝ) := by
    exact_mod_cast centreGap_nonneg residualCentre m
  have hglt : ((centreGap residualCentre m : ℚ) : ℝ) < 1 := by
    exact_mod_cast centreGap_lt_one residualCentre m
  rw [abs_lt]
  constructor <;> · unfold signedCentreTailError; linarith

/-- **The wrap-free normal form.**  Peeling plus the ceiling decomposition of
the centre. -/
theorem factorial_mul_series_eq_peeledHead_add_centreCeil_add_error
    {m : ℕ} (hm : 2 ≤ m) :
    (m.factorial : ℝ) * _root_.Erdos68.factorialGapSeries =
      (peeledHead m : ℝ) + ((centreCeil residualCentre m : ℤ) : ℝ) +
        signedCentreTailError m := by
  have hpeel := factorial_mul_series_eq_peeledHead_add_centre_add_scaledTail hm
  have hgap : ((centreGap residualCentre m : ℚ) : ℝ) =
      ((centreCeil residualCentre m : ℤ) : ℝ) - ((residualCentre m : ℚ) : ℝ) := by
    unfold centreGap
    push_cast
    ring
  unfold signedCentreTailError
  rw [hgap]
  linarith [hpeel]

/-- **Single-hit criterion.**  The synchronisation error vanishes exactly when
the scaled series is an integer. -/
theorem signedCentreTailError_eq_zero_iff_exists_int {m : ℕ} (hm : 2 ≤ m) :
    signedCentreTailError m = 0 ↔
      ∃ z : ℤ, (m.factorial : ℝ) * _root_.Erdos68.factorialGapSeries = (z : ℝ) := by
  have hid := factorial_mul_series_eq_peeledHead_add_centreCeil_add_error hm
  constructor
  · intro h0
    exact ⟨(peeledHead m : ℤ) + centreCeil residualCentre m, by
      rw [hid, h0]; push_cast; ring⟩
  · rintro ⟨z, hz⟩
    have hEint : signedCentreTailError m =
        ((z - (peeledHead m : ℤ) - centreCeil residualCentre m : ℤ) : ℝ) := by
      rw [hz] at hid
      push_cast
      linarith [hid]
    have habs := abs_signedCentreTailError_lt_one hm
    rw [hEint] at habs ⊢
    have hlt : |(z - (peeledHead m : ℤ) - centreCeil residualCentre m : ℤ)| < 1 := by
      exact_mod_cast habs
    rw [abs_lt] at hlt
    have hzero : (z - (peeledHead m : ℤ) - centreCeil residualCentre m : ℤ) = 0 := by
      omega
    rw [hzero]
    norm_num

/-- **The collision normal form for #68.**  The series is rational precisely
when the true infinite tail meets the ceiling gap of the finite rational
centre at one single index. -/
theorem not_irrational_iff_exists_signedCentreTailError_eq_zero :
    ¬ Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ m : ℕ, 2 ≤ m ∧ signedCentreTailError m = 0 := by
  constructor
  · intro hrat
    rw [Irrational, not_not] at hrat
    obtain ⟨q, hq⟩ := hrat
    refine ⟨max 2 q.den, le_max_left _ _, ?_⟩
    rw [signedCentreTailError_eq_zero_iff_exists_int (le_max_left _ _)]
    have hdvd : (q.den : ℤ) ∣ ((max 2 q.den).factorial : ℤ) := by
      exact_mod_cast Nat.dvd_factorial q.pos (le_max_right _ _)
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨q.num * c, ?_⟩
    rw [← hq, Rat.cast_def]
    have hden : ((q.den : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_pos.ne'
    have hcR : (((max 2 q.den).factorial : ℕ) : ℝ) = (q.den : ℝ) * (c : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hc
    rw [hcR]
    push_cast
    field_simp
  · rintro ⟨m, hm, h0⟩
    rw [Irrational, not_not]
    obtain ⟨z, hz⟩ := (signedCentreTailError_eq_zero_iff_exists_int hm).mp h0
    have hfac : ((m.factorial : ℝ)) ≠ 0 := by positivity
    refine ⟨(z : ℚ) / (m.factorial : ℚ), ?_⟩
    push_cast
    field_simp
    linarith [hz]

/-! ## The finite defect-digit form -/

/-- **The error cocycle.**  Subtracting the landed centre-gap recurrence from
the landed scaled-tail recurrence leaves an exceptionally clean affine law
driven only by the finite integer defect digit. -/
theorem signedCentreTailError_recurrence {m : ℕ} (hm : 3 ≤ m) :
    signedCentreTailError m =
      (m : ℝ) * signedCentreTailError (m - 1) +
        ((centreDefectCode residualCentre
          (fun k => (factorialCoeffNat k : ℤ)) m : ℤ) : ℝ) - 1 := by
  have htail := factorialGapScaledTail_pred_recurrence hm
  have hgap := residualCentre_gap_factorial_recurrence m hm
  have hgapR := congrArg (fun q : ℚ => (q : ℝ)) hgap
  push_cast at hgapR
  unfold signedCentreTailError
  have hfacGt : (1 : ℕ) < m.factorial := Nat.one_lt_factorial.mpr (by omega)
  have hfacR : (1 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast hfacGt
  linarith [htail, hgapR]

/-- Under a collision at `M - 1`, the error stays zero forever after.  A
collision is absorbing. -/
theorem signedCentreTailError_eq_zero_of_le
    {M : ℕ} (hM : 2 ≤ M) (h0 : signedCentreTailError M = 0) :
    ∀ m, M ≤ m → signedCentreTailError m = 0 := by
  intro m hm
  rw [signedCentreTailError_eq_zero_iff_exists_int (le_trans hM hm)]
  obtain ⟨z, hz⟩ := (signedCentreTailError_eq_zero_iff_exists_int hM).mp h0
  have hdvd : (M.factorial : ℤ) ∣ (m.factorial : ℤ) := by
    exact_mod_cast Nat.factorial_dvd_factorial hm
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨z * c, ?_⟩
  have hcR : ((m.factorial : ℕ) : ℝ) = ((M.factorial : ℕ) : ℝ) * (c : ℝ) := by
    exact_mod_cast congrArg (fun w : ℤ => (w : ℝ)) hc
  rw [hcR]
  push_cast
  linear_combination (c : ℝ) * hz

/-! ## Tail width -/

/-- **A lower bound on the scaled tail.**  The single next summand already
exceeds `1/(m+1)` after scaling, so `T_m` is pinned into `(1/(m+1), 2/m)` by
the landed upper bound. -/
theorem one_div_succ_lt_factorialGapScaledTail {m : ℕ} (hm : 2 ≤ m) :
    1 / ((m : ℝ) + 1) < factorialGapScaledTail m := by
  have hsplit := factorialGapTail_eq_next_add_tail m
  have hposNext : 0 < _root_.Erdos68.factorialGapTail (m + 1) :=
    _root_.Erdos68.factorialGapTail_pos (by omega)
  have hfacNat : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
  have hfacR : (((m + 1).factorial : ℕ) : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [hfacNat]; push_cast; ring
  have hfacPos : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hmPos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hcast : ((((m + 1).factorial : ℤ) - 1 : ℤ) : ℝ)
      = ((m : ℝ) + 1) * (m.factorial : ℝ) - 1 := by
    push_cast [← hfacR]; push_cast; ring
  have hfac1 : (1 : ℝ) ≤ (m.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hm1 : (2 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hdpos : (0 : ℝ) < ((m : ℝ) + 1) * (m.factorial : ℝ) - 1 := by nlinarith
  have hkey : 1 / ((m : ℝ) + 1)
      < (m.factorial : ℝ) / (((m : ℝ) + 1) * (m.factorial : ℝ) - 1) := by
    rw [div_lt_div_iff₀ hmPos hdpos]
    nlinarith
  have hlow : (m.factorial : ℝ) / (((m : ℝ) + 1) * (m.factorial : ℝ) - 1)
      ≤ factorialGapScaledTail m := by
    unfold factorialGapScaledTail
    rw [hsplit, hcast]
    have : (m.factorial : ℝ) * (1 / (((m : ℝ) + 1) * (m.factorial : ℝ) - 1))
        = (m.factorial : ℝ) / (((m : ℝ) + 1) * (m.factorial : ℝ) - 1) := by ring
    nlinarith [mul_pos hfacPos hposNext]
  linarith

/-- At a collision the finite centre gap inherits the analytic tail window. -/
theorem centreGap_window_of_signedCentreTailError_eq_zero {m : ℕ} (hm : 2 ≤ m)
    (h0 : signedCentreTailError m = 0) :
    1 / ((m : ℝ) + 1) < ((centreGap residualCentre m : ℚ) : ℝ) ∧
      ((centreGap residualCentre m : ℚ) : ℝ) < 2 / (m : ℝ) := by
  have hgap : ((centreGap residualCentre m : ℚ) : ℝ) = factorialGapScaledTail m := by
    have := h0
    unfold signedCentreTailError at this
    linarith
  rw [hgap]
  exact ⟨one_div_succ_lt_factorialGapScaledTail hm,
    factorialGapScaledTail_lt_two_div hm⟩

/-! ## The finite defect-digit normal form -/

/-- **Erdős #68 as a statement about one finite integer digit.**  The series is
rational precisely when the centre defect code is eventually constantly `1`.
Every object named on the right is finite rational or integer data:
`residualCentre`, `centreCeil`, `factorialCoeffNat`. -/
theorem not_irrational_iff_eventually_centreDefectCode_eq_one :
    ¬ Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ M : ℕ, 3 ≤ M ∧ ∀ m, M ≤ m →
        centreDefectCode residualCentre
          (fun k => (factorialCoeffNat k : ℤ)) m = 1 := by
  constructor
  · intro hrat
    obtain ⟨m₀, hm₀, h0⟩ :=
      not_irrational_iff_exists_signedCentreTailError_eq_zero.mp hrat
    have habs := signedCentreTailError_eq_zero_of_le hm₀ h0
    refine ⟨max 3 (m₀ + 1), le_max_left _ _, fun m hm => ?_⟩
    have hm3 : 3 ≤ m := le_trans (le_max_left _ _) hm
    have hE : signedCentreTailError m = 0 := habs m (by omega)
    have hE' : signedCentreTailError (m - 1) = 0 := by
      refine habs (m - 1) ?_
      have : m₀ + 1 ≤ m := le_trans (le_max_right _ _) hm
      omega
    have hrec := signedCentreTailError_recurrence hm3
    rw [hE, hE'] at hrec
    have : ((centreDefectCode residualCentre
        (fun k => (factorialCoeffNat k : ℤ)) m : ℤ) : ℝ) = 1 := by linarith
    exact_mod_cast this
  · rintro ⟨M, hM, hone⟩
    have hstep : ∀ k : ℕ, signedCentreTailError (M + k)
        = ((M + k : ℕ) : ℝ) * signedCentreTailError (M - 1 + k) := by
      intro k
      have hrec := signedCentreTailError_recurrence (m := M + k) (by omega)
      rw [hone (M + k) (by omega)] at hrec
      rw [show M + k - 1 = M - 1 + k by omega] at hrec
      simpa using hrec
    have hgrow : ∀ k : ℕ,
        |signedCentreTailError (M - 1)| ≤ |signedCentreTailError (M - 1 + k)| := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [show M - 1 + (k + 1) = M + k by omega, hstep k, abs_mul]
          have hMk : (1 : ℝ) ≤ ((M + k : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 1 ≤ M + k)
          have habs0 : (0 : ℝ) ≤ |signedCentreTailError (M - 1 + k)| := abs_nonneg _
          have hcast : |((M + k : ℕ) : ℝ)| = ((M + k : ℕ) : ℝ) :=
            abs_of_nonneg (by positivity)
          rw [hcast]
          nlinarith
    have hzero : signedCentreTailError (M - 1) = 0 := by
      by_contra hne
      have hc : 0 < |signedCentreTailError (M - 1)| := abs_pos.mpr hne
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / |signedCentreTailError (M - 1)|)
      have hkc : (1 : ℝ) < (k : ℝ) * |signedCentreTailError (M - 1)| := by
        rw [div_lt_iff₀ hc] at hk
        linarith
      have hbig := hgrow k
      have hEq : |signedCentreTailError (M + k)|
          = ((M + k : ℕ) : ℝ) * |signedCentreTailError (M - 1 + k)| := by
        rw [hstep k, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((M + k : ℕ) : ℝ))]
      have hMk : (k : ℝ) ≤ ((M + k : ℕ) : ℝ) := by
        exact_mod_cast (by omega : k ≤ M + k)
      have hlt := abs_signedCentreTailError_lt_one (m := M + k) (by omega)
      nlinarith [abs_nonneg (signedCentreTailError (M - 1 + k))]
    refine not_irrational_iff_exists_signedCentreTailError_eq_zero.mpr
      ⟨M - 1, by omega, hzero⟩

end ErdosProblems.Erdos68
