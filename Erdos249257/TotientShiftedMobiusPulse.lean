import Erdos249257.MersenneLambertLadder
import Erdos249257.TotientTailPeriodKiller
import Mathlib.Tactic

/-!
# Shifted Möbius pulses for the totient tail

For `d > 0`, let `r_d(N)` be the least positive integer for which
`d ∣ N + r_d(N)`, and put `q_d(N) = N / d + 1`.  Thus
`1 ≤ r_d(N) ≤ d`, `N + r_d(N) = d * q_d(N)`, and `r_d(N) = d`
when `d ∣ N`.  The contribution of the multiples of `d` to the shifted
totient tail is the geometric-linear fibre

`sum_k μ(d) * (N / d + 1 + k) / 2^(r_d(N) + d*k)`.

The theorem `tsum_shiftedDivisorFiber` evaluates this fibre exactly as the
Mersenne pulse

`μ(d) * 2^(d-r_d(N)) * ((N/d+1)/(2^d-1) + 1/(2^d-1)^2)`.

The proof has three distinct steps.  Absolute summability permits a Lambert
double series, optionally restricted by a predicate on the product index, to
be regrouped over divisors.  Each fixed-`d` fibre is then evaluated by a
geometric-linear summation.  Finally Möbius inversion and multiplication by
`2^N` identify the resulting series with the literal totient tail:

`totientTail N = ∑' d : ℕ+, shiftedMobiusPulseTerm N d`.

This is an exact expansion, not an estimate.  A fibre may vanish because
`μ(d) = 0`, and fibres of opposite sign may cancel.  The module proves no
non-vanishing, sign or dominance statement, no effective remainder or tail
difference lower bound, no residue or carry escape, and no irrationality
conclusion for Erdős 249.  A separate bridge compares this expansion with the
residue-coordinate decomposition.
-/

namespace Erdos249257.TotientShiftedMobiusPulse

open ArithmeticFunction
open MersenneLambertLadder TotientTailPeriodKiller
open scoped BigOperators

/-- The least strictly positive shift from `N` to a multiple of `d` when
`d > 0`.  At a divisor of `N` it is `d`, rather than zero. -/
def forwardMultipleShift (N d : ℕ) : ℕ := d - N % d

/-- The quotient of the first multiple of `d` strictly above `N`. -/
def forwardMultipleQuotient (N d : ℕ) : ℕ := N / d + 1

theorem forwardMultipleShift_pos (N : ℕ) {d : ℕ} (hd : 0 < d) :
    0 < forwardMultipleShift N d := by
  unfold forwardMultipleShift
  exact Nat.sub_pos_of_lt (Nat.mod_lt N hd)

theorem forwardMultipleShift_le (N d : ℕ) :
    forwardMultipleShift N d ≤ d := by
  unfold forwardMultipleShift
  exact Nat.sub_le _ _

theorem add_forwardMultipleShift_eq (N : ℕ) {d : ℕ} (hd : 0 < d) :
    N + forwardMultipleShift N d = d * forwardMultipleQuotient N d := by
  unfold forwardMultipleShift forwardMultipleQuotient
  have hlt : N % d < d := Nat.mod_lt N hd
  calc
    N + (d - N % d) =
        (N % d + d * (N / d)) + (d - N % d) := by
          rw [Nat.mod_add_div]
    _ = d * (N / d) + (N % d + (d - N % d)) := by
          ac_rfl
    _ = d * (N / d) + d := by
          rw [Nat.add_sub_of_le hlt.le]
    _ = d * (N / d + 1) := by
          rw [Nat.mul_add, Nat.mul_one]

theorem forwardMultipleShift_dvd (N : ℕ) {d : ℕ} (hd : 0 < d) :
    d ∣ N + forwardMultipleShift N d := by
  rw [add_forwardMultipleShift_eq N hd]
  exact dvd_mul_right d (forwardMultipleQuotient N d)

theorem forwardMultipleQuotient_eq (N : ℕ) {d : ℕ} (hd : 0 < d) :
    forwardMultipleQuotient N d =
      (N + forwardMultipleShift N d) / d := by
  rw [add_forwardMultipleShift_eq N hd]
  simp [hd.ne']

theorem forwardMultipleShift_eq_self_of_dvd
    (N : ℕ) {d : ℕ} (hd : 0 < d) (hdN : d ∣ N) :
    forwardMultipleShift N d = d := by
  simp [forwardMultipleShift, Nat.mod_eq_zero_of_dvd hdN]

private lemma summable_const_add_mul_geometric (q x : ℝ) (hx : ‖x‖ < 1) :
    Summable (fun k : ℕ => (q + (k : ℝ)) * x ^ k) := by
  have hconst : Summable (fun k : ℕ => q * x ^ k) :=
    (summable_geometric_of_norm_lt_one hx).mul_left q
  have hlinear : Summable (fun k : ℕ => (k : ℝ) * x ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hx
  exact (hconst.add hlinear).congr fun k => by ring

private theorem tsum_const_add_mul_geometric (q x : ℝ) (hx : ‖x‖ < 1) :
    ∑' k : ℕ, (q + (k : ℝ)) * x ^ k =
      q / (1 - x) + x / (1 - x) ^ 2 := by
  have hconst : Summable (fun k : ℕ => q * x ^ k) :=
    (summable_geometric_of_norm_lt_one hx).mul_left q
  have hlinear : Summable (fun k : ℕ => (k : ℝ) * x ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hx
  calc
    ∑' k : ℕ, (q + (k : ℝ)) * x ^ k =
        ∑' k : ℕ, (q * x ^ k + (k : ℝ) * x ^ k) := by
          apply tsum_congr
          intro k
          ring
    _ = (∑' k : ℕ, q * x ^ k) + ∑' k : ℕ, (k : ℝ) * x ^ k :=
      Summable.tsum_add hconst hlinear
    _ = q * (∑' k : ℕ, x ^ k) + ∑' k : ℕ, (k : ℝ) * x ^ k := by
      rw [tsum_mul_left]
    _ = q / (1 - x) + x / (1 - x) ^ 2 := by
      rw [tsum_geometric_of_norm_lt_one hx,
        tsum_coe_mul_geometric_of_norm_lt_one hx]
      ring

/-- Product-to-divisor regrouping after restricting to an arbitrary predicate
of the product index.  Absolute summability makes the restriction and the
antidiagonal regroup unconditional. -/
theorem tsum_lambert_pair_regroup_if
    (w v : ℕ → ℝ)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    (hv : ∀ m : ℕ, 0 < m → |v m| ≤ (m : ℝ))
    (P : ℕ → Prop) [DecidablePred P]
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∑' p : ℕ+ × ℕ+,
      if P ((p.1 : ℕ) * (p.2 : ℕ)) then
        w (p.1 : ℕ) * v (p.2 : ℕ) *
          x ^ ((p.1 : ℕ) * (p.2 : ℕ))
      else 0) =
      ∑' n : ℕ+,
        if P (n : ℕ) then
          (∑ e ∈ (n : ℕ).divisors,
              w e * v ((n : ℕ) / e)) * x ^ (n : ℕ)
        else 0 := by
  have hprod := summable_lambert_pair w v hw hv hx0 hx1
  have hcut : Summable (fun p : ℕ+ × ℕ+ =>
      if P ((p.1 : ℕ) * (p.2 : ℕ)) then
        w (p.1 : ℕ) * v (p.2 : ℕ) *
          x ^ ((p.1 : ℕ) * (p.2 : ℕ))
      else 0) := by
    have h := hprod.indicator
      {p : ℕ+ × ℕ+ | P ((p.1 : ℕ) * (p.2 : ℕ))}
    refine h.congr fun p => ?_
    by_cases hp : P ((p.1 : ℕ) * (p.2 : ℕ)) <;>
      simp [Set.indicator, hp]
  have hsig : Summable
      (fun z : (Σ n : ℕ+,
          {y // y ∈ (n : ℕ).divisorsAntidiagonal}) =>
        if P (z.1 : ℕ) then
          w z.2.1.1 * v z.2.1.2 *
            x ^ (z.2.1.1 * z.2.1.2)
        else 0) := by
    have h := (Equiv.summable_iff sigmaAntidiagonalEquivProd).mpr hcut
    refine h.congr fun z => ?_
    rcases z with ⟨n, ⟨⟨a, b⟩, hab⟩⟩
    have habmul : a * b = (n : ℕ) :=
      (Nat.mem_divisorsAntidiagonal.mp hab).1
    simp [Function.comp, sigmaAntidiagonalEquivProd,
      divisorsAntidiagonalFactors, habmul]
  calc
    (∑' p : ℕ+ × ℕ+,
        if P ((p.1 : ℕ) * (p.2 : ℕ)) then
          w (p.1 : ℕ) * v (p.2 : ℕ) *
            x ^ ((p.1 : ℕ) * (p.2 : ℕ))
        else 0) =
        ∑' z : (Σ n : ℕ+,
          {y // y ∈ (n : ℕ).divisorsAntidiagonal}),
          if P (z.1 : ℕ) then
            w z.2.1.1 * v z.2.1.2 *
              x ^ (z.2.1.1 * z.2.1.2)
          else 0 := by
      rw [← sigmaAntidiagonalEquivProd.tsum_eq
        (f := fun p : ℕ+ × ℕ+ =>
          if P ((p.1 : ℕ) * (p.2 : ℕ)) then
            w (p.1 : ℕ) * v (p.2 : ℕ) *
              x ^ ((p.1 : ℕ) * (p.2 : ℕ))
          else 0)]
      refine tsum_congr fun z => ?_
      rcases z with ⟨n, ⟨⟨a, b⟩, hab⟩⟩
      have habmul : a * b = (n : ℕ) :=
        (Nat.mem_divisorsAntidiagonal.mp hab).1
      simp [sigmaAntidiagonalEquivProd,
        divisorsAntidiagonalFactors, habmul]
    _ = ∑' n : ℕ+,
          ∑' y : {y // y ∈ (n : ℕ).divisorsAntidiagonal},
            if P (n : ℕ) then
              w y.1.1 * v y.1.2 * x ^ (y.1.1 * y.1.2)
            else 0 := Summable.tsum_sigma hsig
    _ = ∑' n : ℕ+,
          if P (n : ℕ) then
            (∑ e ∈ (n : ℕ).divisors,
                w e * v ((n : ℕ) / e)) * x ^ (n : ℕ)
          else 0 := by
      refine tsum_congr fun n => ?_
      by_cases hn : P (n : ℕ)
      · simp only [if_pos hn]
        rw [tsum_fintype, Finset.univ_eq_attach,
          Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
            (fun y : ℕ × ℕ =>
              w y.1 * v y.2 * x ^ (y.1 * y.2)),
          Nat.sum_divisorsAntidiagonal
            (fun d e => w d * v e * x ^ (d * e))]
        have hstep : ∀ d ∈ (n : ℕ).divisors,
            w d * v ((n : ℕ) / d) *
                x ^ (d * ((n : ℕ) / d)) =
              w d * v ((n : ℕ) / d) * x ^ (n : ℕ) := by
          intro d hd
          rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
        rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
      · simp [hn]

/-- The closed contribution of one divisor `d` to the shifted tail at `N`. -/
noncomputable def shiftedMobiusPulseTerm (N d : ℕ) : ℝ :=
  (((moebius d : ℤ) : ℝ) * (2 : ℝ) ^ (d - forwardMultipleShift N d)) *
    (((forwardMultipleQuotient N d : ℕ) : ℝ) / ((2 : ℝ) ^ d - 1) +
      1 / ((2 : ℝ) ^ d - 1) ^ 2)

private lemma div_two_pow_eq (a : ℝ) (n : ℕ) :
    a / (2 : ℝ) ^ n = a * ((1 : ℝ) / 2) ^ n := by
  rw [div_pow, one_pow]
  ring

/-- Exact evaluation of a shifted divisor fibre.  This is the residue-class
geometric identity underlying the shifted Möbius formula for `totientTail`. -/
theorem tsum_shiftedDivisorFiber (N : ℕ) (d : ℕ+) :
    (∑' k : ℕ,
      ((moebius (d : ℕ) : ℤ) : ℝ) *
        (((forwardMultipleQuotient N d : ℕ) : ℝ) + (k : ℝ)) /
          (2 : ℝ) ^ (forwardMultipleShift N d + (d : ℕ) * k)) =
      shiftedMobiusPulseTerm N d := by
  let r : ℕ := forwardMultipleShift N d
  let q : ℕ := forwardMultipleQuotient N d
  let x : ℝ := ((1 : ℝ) / 2) ^ (d : ℕ)
  have hx : ‖x‖ < 1 := by
    dsimp [x]
    rw [abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)]
    exact pow_lt_one₀ (by norm_num) (by norm_num) d.ne_zero
  have hrle : r ≤ (d : ℕ) := forwardMultipleShift_le N d
  have hsplit : (2 : ℝ) ^ (d : ℕ) =
      (2 : ℝ) ^ ((d : ℕ) - r) * (2 : ℝ) ^ r := by
    rw [← pow_add]
    congr 1
    omega
  have hpow (k : ℕ) :
      ((((q : ℕ) : ℝ) + (k : ℝ)) /
          (2 : ℝ) ^ (r + (d : ℕ) * k)) =
        ((1 : ℝ) / 2) ^ r *
          ((((q : ℕ) : ℝ) + (k : ℝ)) * x ^ k) := by
    rw [div_two_pow_eq, pow_add, pow_mul]
    dsimp [x]
    ring
  rw [show forwardMultipleShift N d = r by rfl,
    show forwardMultipleQuotient N d = q by rfl]
  calc
    (∑' k : ℕ,
        ((moebius (d : ℕ) : ℤ) : ℝ) *
          (((q : ℕ) : ℝ) + (k : ℝ)) /
            (2 : ℝ) ^ (r + (d : ℕ) * k)) =
        (((moebius (d : ℕ) : ℤ) : ℝ) * ((1 : ℝ) / 2) ^ r) *
          (∑' k : ℕ, (((q : ℕ) : ℝ) + (k : ℝ)) * x ^ k) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      calc
        ((moebius (d : ℕ) : ℤ) : ℝ) *
              (((q : ℕ) : ℝ) + (k : ℝ)) /
                (2 : ℝ) ^ (r + (d : ℕ) * k) =
            ((moebius (d : ℕ) : ℤ) : ℝ) *
              ((((q : ℕ) : ℝ) + (k : ℝ)) /
                (2 : ℝ) ^ (r + (d : ℕ) * k)) := by ring
        _ = ((moebius (d : ℕ) : ℤ) : ℝ) *
              (((1 : ℝ) / 2) ^ r *
                ((((q : ℕ) : ℝ) + (k : ℝ)) * x ^ k)) := by rw [hpow]
        _ = (((moebius (d : ℕ) : ℤ) : ℝ) * ((1 : ℝ) / 2) ^ r) *
              ((((q : ℕ) : ℝ) + (k : ℝ)) * x ^ k) := by ring
    _ = (((moebius (d : ℕ) : ℤ) : ℝ) * ((1 : ℝ) / 2) ^ r) *
          ((((q : ℕ) : ℝ) / (1 - x)) + x / (1 - x) ^ 2) := by
      rw [tsum_const_add_mul_geometric _ _ hx]
    _ = shiftedMobiusPulseTerm N d := by
      unfold shiftedMobiusPulseTerm
      rw [show forwardMultipleShift N ↑d = r by rfl,
        show forwardMultipleQuotient N ↑d = q by rfl]
      dsimp [x]
      have hxpow : ((1 : ℝ) / 2) ^ (d : ℕ) =
          1 / (2 : ℝ) ^ (d : ℕ) := by
        rw [div_pow, one_pow]
      have hrpow : ((1 : ℝ) / 2) ^ r =
          1 / (2 : ℝ) ^ r := by
        rw [div_pow, one_pow]
      rw [hxpow, hrpow]
      have htwo : (2 : ℝ) ^ (d : ℕ) ≠ 0 := by positivity
      have hmersenne : (2 : ℝ) ^ (d : ℕ) - 1 ≠ 0 := by
        have : (1 : ℝ) < (2 : ℝ) ^ (d : ℕ) :=
          one_lt_pow₀ (by norm_num) d.ne_zero
        linarith
      field_simp [htwo, hmersenne]
      rw [hsplit]
      ring

private theorem abs_moebius_real_le (d : ℕ) (hd : 0 < d) :
    |((moebius d : ℤ) : ℝ)| ≤ (d : ℝ) := by
  have hμ : |moebius d| ≤ (d : ℤ) := by
    exact (abs_moebius_le_one d).trans (by exact_mod_cast hd)
  rw [← Int.cast_abs]
  exact_mod_cast hμ

private theorem abs_natCast_le (m : ℕ) (_hm : 0 < m) :
    |(m : ℝ)| ≤ (m : ℝ) := by
  rw [abs_of_nonneg]
  positivity

private theorem sum_divisors_moebius_mul_div_real (n : ℕ+) :
    (∑ e ∈ (n : ℕ).divisors,
        ((moebius e : ℤ) : ℝ) * ((((n : ℕ) / e : ℕ) : ℝ))) =
      (Nat.totient (n : ℕ) : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (sum_divisors_moebius_mul_div (n : ℕ) n.pos)
  push_cast at h
  simpa using h

/-- The absolutely summable product family whose product indices lie strictly
past `N`. -/
private noncomputable def tailMobiusPair (N : ℕ) (p : ℕ+ × ℕ+) : ℝ :=
  if N < (p.1 : ℕ) * (p.2 : ℕ) then
    ((moebius (p.1 : ℕ) : ℤ) : ℝ) * (p.2 : ℝ) *
      ((1 : ℝ) / 2) ^ ((p.1 : ℕ) * (p.2 : ℕ))
  else 0

private theorem summable_tailMobiusPair (N : ℕ) :
    Summable (tailMobiusPair N) := by
  have hbase := summable_lambert_pair
    (fun d => ((moebius d : ℤ) : ℝ))
    (fun m => (m : ℝ))
    abs_moebius_real_le abs_natCast_le
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)
  have hcut := hbase.indicator
    {p : ℕ+ × ℕ+ | N < (p.1 : ℕ) * (p.2 : ℕ)}
  refine hcut.congr fun p => ?_
  by_cases hp : N < (p.1 : ℕ) * (p.2 : ℕ) <;>
    simp [tailMobiusPair, Set.indicator, hp]

/-- Möbius inversion turns the restricted product family into the positive
totient tail in absolute binary coordinates. -/
theorem tsum_tailMobiusPair_eq_pnatTotientTail (N : ℕ) :
    (∑' p : ℕ+ × ℕ+, tailMobiusPair N p) =
      ∑' n : ℕ+,
        if N < (n : ℕ) then
          (Nat.totient (n : ℕ) : ℝ) *
            ((1 : ℝ) / 2) ^ (n : ℕ)
        else 0 := by
  unfold tailMobiusPair
  rw [tsum_lambert_pair_regroup_if
    (fun d => ((moebius d : ℤ) : ℝ))
    (fun m => (m : ℝ))
    abs_moebius_real_le abs_natCast_le
    (fun n => N < n)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)]
  refine tsum_congr fun n => ?_
  by_cases hn : N < (n : ℕ)
  · rw [if_pos hn, if_pos hn, sum_divisors_moebius_mul_div_real]
  · simp [hn]

/-- The positive-index form of the absolute totient tail. -/
noncomputable def pnatTotientTail (N : ℕ) : ℝ :=
  ∑' n : ℕ+,
    if N < (n : ℕ) then
      (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)
    else 0

private theorem summable_totient_half_pow :
    Summable (fun n : ℕ =>
      (Nat.totient n : ℝ) * ((1 : ℝ) / 2) ^ n) := by
  exact summable_totient_div_two_pow.congr fun n => div_two_pow_eq _ n

private theorem pnatTotientTail_eq_tsum_nat (N : ℕ) :
    pnatTotientTail N =
      ∑' j : ℕ,
        (Nat.totient (N + 1 + j) : ℝ) *
          ((1 : ℝ) / 2) ^ (N + 1 + j) := by
  let f : ℕ → ℝ := fun n =>
    if N < n + 1 then
      (Nat.totient (n + 1) : ℝ) * ((1 : ℝ) / 2) ^ (n + 1)
    else 0
  have hraw : Summable (fun n : ℕ =>
      (Nat.totient (n + 1) : ℝ) * ((1 : ℝ) / 2) ^ (n + 1)) := by
    have hshift := (summable_nat_add_iff 1).mpr summable_totient_half_pow
    simpa [Nat.add_comm] using hshift
  have hf : Summable f := by
    have hcut := hraw.indicator {n : ℕ | N < n + 1}
    refine hcut.congr fun n => ?_
    by_cases hn : N < n + 1 <;> simp [f, Set.indicator, hn]
  have hsplit := hf.sum_add_tsum_nat_add N
  have hprefix : ∑ n ∈ Finset.range N, f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnN : n < N := Finset.mem_range.mp hn
    have hnot : ¬ N < n + 1 := by omega
    change (if N < n + 1 then
      (Nat.totient (n + 1) : ℝ) * ((1 : ℝ) / 2) ^ (n + 1)
      else 0) = 0
    rw [if_neg hnot]
  unfold pnatTotientTail
  rw [tsum_pnat_eq_tsum_succ
    (f := fun n : ℕ =>
      if N < n then
        (Nat.totient n : ℝ) * ((1 : ℝ) / 2) ^ n
      else 0)]
  change (∑' n : ℕ, f n) = _
  rw [← hsplit, hprefix, zero_add]
  refine tsum_congr fun j => ?_
  have hj : N < j + N + 1 := by omega
  simp [f, hj, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Scaling the absolute positive-index tail by `2^N` recovers the local tail
`R_N`, whose exponent starts again at one. -/
theorem totientTail_eq_two_pow_mul_pnatTotientTail (N : ℕ) :
    totientTail N = (2 : ℝ) ^ N * pnatTotientTail N := by
  rw [pnatTotientTail_eq_tsum_nat, ← tsum_mul_left]
  unfold totientTail
  refine tsum_congr fun j => ?_
  rw [div_two_pow_eq]
  have hpow : ((1 : ℝ) / 2) ^ (N + 1 + j) =
      ((1 : ℝ) / 2) ^ N * ((1 : ℝ) / 2) ^ (j + 1) := by
    rw [show N + 1 + j = N + (j + 1) by omega, pow_add]
  rw [hpow]
  have hcancel :
      (2 : ℝ) ^ N * ((1 : ℝ) / 2) ^ N = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (Nat.totient (N + 1 + j) : ℝ) * ((1 : ℝ) / 2) ^ (j + 1) =
        ((2 : ℝ) ^ N * ((1 : ℝ) / 2) ^ N) *
          ((Nat.totient (N + 1 + j) : ℝ) *
            ((1 : ℝ) / 2) ^ (j + 1)) := by rw [hcancel, one_mul]
    _ = (2 : ℝ) ^ N *
        ((Nat.totient (N + 1 + j) : ℝ) *
          (((1 : ℝ) / 2) ^ N * ((1 : ℝ) / 2) ^ (j + 1))) := by ring

private theorem tailMobiusPair_fiber_reindex (N : ℕ) (d : ℕ+) :
    (∑' m : ℕ+, tailMobiusPair N (d, m)) =
      ∑' k : ℕ,
        ((moebius (d : ℕ) : ℤ) : ℝ) *
          (((forwardMultipleQuotient N d : ℕ) : ℝ) + (k : ℝ)) *
            ((1 : ℝ) / 2) ^
              ((d : ℕ) * (forwardMultipleQuotient N d + k)) := by
  let g : ℕ → ℝ := fun m =>
    if N < (d : ℕ) * m then
      ((moebius (d : ℕ) : ℤ) : ℝ) * (m : ℝ) *
        ((1 : ℝ) / 2) ^ ((d : ℕ) * m)
    else 0
  have hfiber := (summable_tailMobiusPair N).prod_factor d
  have hpnat : Summable (fun m : ℕ+ => g (m : ℕ)) := by
    exact hfiber.congr fun m => by simp [g, tailMobiusPair]
  have hnat : Summable (fun k : ℕ => g (k + 1)) := by
    rw [← summable_pnat_iff_summable_succ (f := g)]
    exact hpnat
  have hsplit := hnat.sum_add_tsum_nat_add (N / (d : ℕ))
  have hprefix :
      ∑ k ∈ Finset.range (N / (d : ℕ)), g (k + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < N / (d : ℕ) := Finset.mem_range.mp hk
    have hkle : k + 1 ≤ N / (d : ℕ) := by omega
    have hmul := Nat.mul_le_mul_left (d : ℕ) hkle
    have hdiv : (d : ℕ) * (N / (d : ℕ)) ≤ N := by
      simpa [Nat.mul_comm] using Nat.mul_div_le N (d : ℕ)
    simp [g, Nat.not_lt.mpr (hmul.trans hdiv)]
  change (∑' m : ℕ+, g (m : ℕ)) = _
  rw [tsum_pnat_eq_tsum_succ (f := g), ← hsplit, hprefix, zero_add]
  refine tsum_congr fun k => ?_
  have hfirst : N < (d : ℕ) * (N / (d : ℕ) + 1) :=
    Nat.lt_mul_div_succ N d.pos
  have hqle : N / (d : ℕ) + 1 ≤ k + N / (d : ℕ) + 1 := by omega
  have hmul := Nat.mul_le_mul_left (d : ℕ) hqle
  have htail : N < (d : ℕ) * (k + N / (d : ℕ) + 1) :=
    hfirst.trans_le hmul
  rw [show g (k + (N / (d : ℕ)) + 1) =
      ((moebius (d : ℕ) : ℤ) : ℝ) *
        ((k + (N / (d : ℕ)) + 1 : ℕ) : ℝ) *
          ((1 : ℝ) / 2) ^
            ((d : ℕ) * (k + (N / (d : ℕ)) + 1)) by
    simp only [g, if_pos htail]]
  have hidx : k + N / (d : ℕ) + 1 =
      forwardMultipleQuotient N d + k := by
    unfold forwardMultipleQuotient
    omega
  rw [hidx]
  simp

private theorem two_pow_mul_tailMobiusPair_fiber_eq
    (N : ℕ) (d : ℕ+) :
    (2 : ℝ) ^ N * (∑' m : ℕ+, tailMobiusPair N (d, m)) =
      shiftedMobiusPulseTerm N d := by
  rw [tailMobiusPair_fiber_reindex, ← tsum_mul_left]
  calc
    (∑' k : ℕ,
        (2 : ℝ) ^ N *
          (((moebius (d : ℕ) : ℤ) : ℝ) *
            (((forwardMultipleQuotient N d : ℕ) : ℝ) + (k : ℝ)) *
              ((1 : ℝ) / 2) ^
                ((d : ℕ) * (forwardMultipleQuotient N d + k)))) =
        ∑' k : ℕ,
          ((moebius (d : ℕ) : ℤ) : ℝ) *
            (((forwardMultipleQuotient N d : ℕ) : ℝ) + (k : ℝ)) /
              (2 : ℝ) ^
                (forwardMultipleShift N d + (d : ℕ) * k) := by
      refine tsum_congr fun k => ?_
      have hindex :
          (d : ℕ) * (forwardMultipleQuotient N d + k) =
            N + (forwardMultipleShift N d + (d : ℕ) * k) := by
        rw [Nat.mul_add, ← add_forwardMultipleShift_eq N d.pos]
        omega
      rw [div_two_pow_eq, hindex, pow_add]
      have hcancel :
          (2 : ℝ) ^ N * ((1 : ℝ) / 2) ^ N = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (2 : ℝ) ^ N *
            (((moebius (d : ℕ) : ℤ) : ℝ) *
              (((forwardMultipleQuotient N d : ℕ) : ℝ) + (k : ℝ)) *
                (((1 : ℝ) / 2) ^ N *
                  ((1 : ℝ) / 2) ^
                    (forwardMultipleShift N d + (d : ℕ) * k))) =
          ((2 : ℝ) ^ N * ((1 : ℝ) / 2) ^ N) *
            (((moebius (d : ℕ) : ℤ) : ℝ) *
              (((forwardMultipleQuotient N d : ℕ) : ℝ) + (k : ℝ)) *
                ((1 : ℝ) / 2) ^
                  (forwardMultipleShift N d + (d : ℕ) * k)) := by ring
        _ = ((moebius (d : ℕ) : ℤ) : ℝ) *
              (((forwardMultipleQuotient N d : ℕ) : ℝ) + (k : ℝ)) *
                ((1 : ℝ) / 2) ^
                  (forwardMultipleShift N d + (d : ℕ) * k) := by
              rw [hcancel, one_mul]
    _ = shiftedMobiusPulseTerm N d := tsum_shiftedDivisorFiber N d

/-- **Exact shifted Möbius formula for the literal totient tail.**  Every
divisor fibre is evaluated at its first multiple strictly past `N`; no foreign
term is defined by subtracting an approximation from the target. -/
theorem totientTail_eq_tsum_shiftedMobiusPulse (N : ℕ) :
    totientTail N =
      ∑' d : ℕ+, shiftedMobiusPulseTerm N d := by
  have htail := summable_tailMobiusPair N
  have hpair : (∑' p : ℕ+ × ℕ+, tailMobiusPair N p) =
      pnatTotientTail N := by
    simpa [pnatTotientTail] using tsum_tailMobiusPair_eq_pnatTotientTail N
  rw [totientTail_eq_two_pow_mul_pnatTotientTail, ← hpair,
    htail.tsum_prod, ← tsum_mul_left]
  exact tsum_congr fun d => two_pow_mul_tailMobiusPair_fiber_eq N d

end Erdos249257.TotientShiftedMobiusPulse
