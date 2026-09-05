import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The Mersenne–Lambert ladder for Erdős #249

`S = ∑ φ(n)/2ⁿ` (the #249 constant) is the Lambert-transform neighbour of two
*exactly rational* series and one *machine-checked irrational* one.  Writing
`L(f) = ∑_{n≥1} f(n)/(2ⁿ-1) = ∑_m (∑_{d∣m} f(d))/2^m`, the ladder is

* `L(μ) = 1/2`            (rational — `μ * ζ = ε`),
* `L(φ) = 2`              (rational — `φ * ζ = Id`, `∑ m/2^m = 2`),
* `L(1) = E`              (Erdős–Borwein; IRRATIONAL, machine-checked in
                           `CertificateKernel.irrational_erdosBorwein_series`),
* `L(A) = S`              (OPEN — this is #249), where `A = φ * μ ≥ 0` is the
                           primitive-conductor weight (`A(n)` counts primitive
                           Dirichlet characters of conductor `n`, OEIS A007431),
* `L(Id) = ∑ σ(m)/2^m`    (transcendental by Nesterenko 1996 via `E₂(1/2)`;
                           cited, NOT formalised here).

So one Dirichlet convolution by `ζ` separates the open constant from a trivially
rational value (`A * ζ = φ`), and one more separates rational from transcendental
(`φ * ζ = Id`, `Id * ζ = σ`).  This file machine-checks the two rational rungs,
the positive lift `L(A) = S`, and the signed Möbius-square lens

  `S = 1/2 + ∑_{d≥1} μ(d)/(2^d-1)²`.

It also checks the prime-wise integrality obstruction for the normalized
primitive coordinate: at every odd prime `p`, `p ∤ A(p)`, equivalently
`A(p) / p` is not an integer.  This is an obstruction to an ordinary integral
Euler/Witt realization, not an irrationality theorem for `S`.

The engine is a *signed, linear-growth* weighted Lambert rearrangement
(`tsum_lambert_pair_regroup`): the kernel's landed
`weighted_lambert_series_identity` requires `0 ≤ w ≤ 1`, which admits neither
`φ` (unbounded) nor `μ` (signed).  Summability rides Mathlib's
`summable_prod_mul_pow` through the AM–GM bound `d·m ≤ d² + m²`.

The honest boundary: every identity here is an *equality of convergent series* —
classical in shape (the `L(A) = S` form is recorded at OEIS A256936/A007431).
None of them decides irrationality of `S`; they relocate #249 into the positive
Erdős–Borwein family, where the kernel's own irrationality engine
(`irrational_erdosSum_full_support`) already handles the weight-1 member.
Whether the Erdős 1948 congruence mechanism tolerates the weight `A(p) = p - 2`
is exactly the open analytic core, and is NOT claimed.
-/

namespace MersenneLambertLadder

open ArithmeticFunction

/-! ## The signed linear-growth Lambert engine -/

/-- Summability of the product-weighted geometric family over `ℕ+ × ℕ+` for
weights of at most linear growth.  The majorant is AM–GM:
`|w(d)·v(m)| ≤ d·m ≤ d² + m²`, and each square rides Mathlib's
`summable_prod_mul_pow` (once directly, once through `Prod.swap`). -/
theorem summable_lambert_pair
    (w v : ℕ → ℝ)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    (hv : ∀ m : ℕ, 0 < m → |v m| ≤ (m : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun p : ℕ+ × ℕ+ =>
      w (p.1 : ℕ) * v (p.2 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hM2 : Summable (fun p : ℕ+ × ℕ+ =>
      ((p.2 : ℕ) : ℝ) ^ 2 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
    have h := summable_prod_mul_pow (𝕜 := ℝ) 2 hnorm
    exact h.congr fun p => by ring
  have hM1 : Summable (fun p : ℕ+ × ℕ+ =>
      ((p.1 : ℕ) : ℝ) ^ 2 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
    have h := (summable_prod_mul_pow (𝕜 := ℝ) 2 hnorm).prod_symm
    refine h.congr fun p => ?_
    show ((p.1 : ℕ) : ℝ) ^ 2 * r ^ ((p.2 : ℕ) * (p.1 : ℕ))
        = ((p.1 : ℕ) : ℝ) ^ 2 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))
    rw [Nat.mul_comm ((p.2 : ℕ)) ((p.1 : ℕ))]
  have hMaj : Summable (fun p : ℕ+ × ℕ+ =>
      (((p.1 : ℕ) : ℝ) ^ 2 + ((p.2 : ℕ) : ℝ) ^ 2) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
    refine (hM1.add hM2).congr fun p => ?_
    ring
  refine Summable.of_norm_bounded hMaj fun p => ?_
  have hp1 : (0 : ℝ) < ((p.1 : ℕ) : ℝ) := by exact_mod_cast p.1.pos
  have hp2 : (0 : ℝ) < ((p.2 : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hrp : (0 : ℝ) ≤ r ^ ((p.1 : ℕ) * (p.2 : ℕ)) := pow_nonneg hr0 _
  have hb : |w (p.1 : ℕ) * v (p.2 : ℕ)| ≤ ((p.1 : ℕ) : ℝ) * ((p.2 : ℕ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul (hw _ p.1.pos) (hv _ p.2.pos) (abs_nonneg _) hp1.le
  have hAMGM : ((p.1 : ℕ) : ℝ) * ((p.2 : ℕ) : ℝ)
      ≤ ((p.1 : ℕ) : ℝ) ^ 2 + ((p.2 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((p.1 : ℕ) : ℝ) - ((p.2 : ℕ) : ℝ))]
  calc ‖w (p.1 : ℕ) * v (p.2 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))‖
      = |w (p.1 : ℕ) * v (p.2 : ℕ)| * r ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrp]
    _ ≤ (((p.1 : ℕ) : ℝ) ^ 2 + ((p.2 : ℕ) : ℝ) ^ 2) * r ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
        mul_le_mul_of_nonneg_right (hb.trans hAMGM) hrp

/-- **Signed weighted product-to-divisor-sum rearrangement** with product
weight `w(d)·v(m)`, both of at most linear growth on positive arguments.
The double series over `ℕ+ × ℕ+` regroups along divisor antidiagonals into
`∑_n (∑_{e∣n} w(e)·v(n/e))·rⁿ` — the Dirichlet convolution appears as the
coefficient.  Signed analogue of the kernel's `[0,1]`-weight identity. -/
theorem tsum_lambert_pair_regroup
    (w v : ℕ → ℝ)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    (hv : ∀ m : ℕ, 0 < m → |v m| ≤ (m : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * v (p.2 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * v ((n : ℕ) / e)) * r ^ (n : ℕ) := by
  have hprod := summable_lambert_pair w v hw hv hr0 hr1
  have hsig : Summable
      (fun x : (Σ n : ℕ+, {y // y ∈ ((n : ℕ)).divisorsAntidiagonal}) =>
        w x.2.1.1 * v x.2.1.2 * r ^ (x.2.1.1 * x.2.1.2)) := by
    have h := (Equiv.summable_iff sigmaAntidiagonalEquivProd).mpr hprod
    refine h.congr fun x => ?_
    rcases x with ⟨n, ⟨⟨a, e⟩, hae⟩⟩
    simp [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]
  calc ∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * v (p.2 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))
      = ∑' x : (Σ n : ℕ+, {y // y ∈ ((n : ℕ)).divisorsAntidiagonal}),
          w x.2.1.1 * v x.2.1.2 * r ^ (x.2.1.1 * x.2.1.2) := by
        rw [← sigmaAntidiagonalEquivProd.tsum_eq
          (f := fun p : ℕ+ × ℕ+ =>
            w (p.1 : ℕ) * v (p.2 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ)))]
        refine tsum_congr fun x => ?_
        rcases x with ⟨n, ⟨⟨a, e⟩, hae⟩⟩
        simp [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]
    _ = ∑' n : ℕ+, ∑' y : {y // y ∈ ((n : ℕ)).divisorsAntidiagonal},
          w y.1.1 * v y.1.2 * r ^ (y.1.1 * y.1.2) := Summable.tsum_sigma hsig
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * v ((n : ℕ) / e)) * r ^ (n : ℕ) := by
        refine tsum_congr fun n => ?_
        rw [tsum_fintype, Finset.univ_eq_attach,
          Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
            (fun y : ℕ × ℕ => w y.1 * v y.2 * r ^ (y.1 * y.2)),
          Nat.sum_divisorsAntidiagonal (fun d e => w d * v e * r ^ (d * e))]
        have hstep : ∀ d ∈ (n : ℕ).divisors,
            w d * v ((n : ℕ) / d) * r ^ (d * ((n : ℕ) / d))
              = w d * v ((n : ℕ) / d) * r ^ (n : ℕ) := by
          intro d hd
          rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
        rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]

/-- **Signed linear-growth Lambert series identity**:
`∑_d w(d)·r^d/(1-r^d) = ∑_n (∑_{e∣n} w(e))·rⁿ` for `|w(d)| ≤ d`. -/
theorem tsum_lambert_linear_weight
    (w : ℕ → ℝ) (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)))
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e) * r ^ (n : ℕ) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hone : ∀ m : ℕ, 0 < m → |(1 : ℝ)| ≤ (m : ℝ) := by
    intro m hm
    rw [abs_one]
    exact_mod_cast hm
  have hprod := summable_lambert_pair w (fun _ => 1) hw hone hr0 hr1
  have hterm : ∀ d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)))
      = ∑' m : ℕ+, w (d : ℕ) * 1 * r ^ ((d : ℕ) * (m : ℕ)) := by
    intro d
    have hd0 : (d : ℕ) ≠ 0 := d.pos.ne'
    have hrd : ‖r ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]) hnorm hd0
    have hgeo := tsum_geometric_of_norm_lt_one hrd
    have h1 : r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) = ∑' j : ℕ, (r ^ (d : ℕ)) ^ (j + 1) := by
      rw [div_eq_mul_inv, ← hgeo, ← tsum_mul_left]
      exact tsum_congr fun j => (pow_succ' _ _).symm
    rw [h1, ← tsum_mul_left,
      ← tsum_pnat_eq_tsum_succ (f := fun j : ℕ => w (d : ℕ) * (r ^ (d : ℕ)) ^ j)]
    exact tsum_congr fun m => by rw [mul_one, ← pow_mul]
  calc ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)))
      = ∑' d : ℕ+, ∑' m : ℕ+, w (d : ℕ) * 1 * r ^ ((d : ℕ) * (m : ℕ)) :=
        tsum_congr hterm
    _ = ∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * 1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
        (hprod.tsum_prod).symm
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * 1) * r ^ (n : ℕ) :=
        tsum_lambert_pair_regroup w (fun _ => 1) hw hone hr0 hr1
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e) * r ^ (n : ℕ) := by
        simp [mul_one]

/-- **Signed linear-growth squared-Lambert identity**:
`∑_d w(d)·r^d/(1-r^d)² = ∑_n (∑_{e∣n} w(e)·(n/e))·rⁿ` for `|w(d)| ≤ d`.
The inner geometric weight `m` is the derivative structure that makes the
divisor coefficient a genuine Dirichlet convolution against `Id`. -/
theorem tsum_lambert_linear_weight_sq
    (w : ℕ → ℝ) (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2)
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * (((n : ℕ) / e : ℕ) : ℝ)) * r ^ (n : ℕ) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hid : ∀ m : ℕ, 0 < m → |((m : ℕ) : ℝ)| ≤ (m : ℝ) := by
    intro m _
    rw [abs_of_nonneg (by positivity)]
  have hprod := summable_lambert_pair w (fun m => (m : ℝ)) hw hid hr0 hr1
  have hterm : ∀ d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2)
      = ∑' m : ℕ+, w (d : ℕ) * ((m : ℕ) : ℝ) * r ^ ((d : ℕ) * (m : ℕ)) := by
    intro d
    have hd0 : (d : ℕ) ≠ 0 := d.pos.ne'
    have hrd : ‖r ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]) hnorm hd0
    have hsum1 : Summable (fun j : ℕ => (j : ℝ) * (r ^ (d : ℕ)) ^ j) := by
      have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrd
      exact h.congr fun j => by rw [pow_one]
    have hgeo : ∑' j : ℕ, (j : ℝ) * (r ^ (d : ℕ)) ^ j
        = r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2 :=
      tsum_coe_mul_geometric_of_norm_lt_one hrd
    have hpn : ∑' m : ℕ+, ((m : ℕ) : ℝ) * (r ^ (d : ℕ)) ^ (m : ℕ)
        = ∑' j : ℕ, (j : ℝ) * (r ^ (d : ℕ)) ^ j := by
      rw [tsum_pnat_eq_tsum_succ (f := fun j : ℕ => (j : ℝ) * (r ^ (d : ℕ)) ^ j),
        hsum1.tsum_eq_zero_add]
      push_cast
      simp
    rw [← hgeo, ← hpn, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [← mul_assoc, ← pow_mul]
  calc ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2)
      = ∑' d : ℕ+, ∑' m : ℕ+, w (d : ℕ) * ((m : ℕ) : ℝ) * r ^ ((d : ℕ) * (m : ℕ)) :=
        tsum_congr hterm
    _ = ∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * ((p.2 : ℕ) : ℝ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
        (hprod.tsum_prod).symm
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * (((n : ℕ) / e : ℕ) : ℝ)) * r ^ (n : ℕ) :=
        tsum_lambert_pair_regroup w (fun m => (m : ℝ)) hw hid hr0 hr1

/-! ## The primitive-conductor weight `A = φ * μ` -/

/-- The Euler totient as an integer-valued arithmetic function. -/
def totientZ : ArithmeticFunction ℤ :=
  ⟨fun n => (Nat.totient n : ℤ), by simp⟩

@[simp] theorem totientZ_apply (n : ℕ) : totientZ n = (Nat.totient n : ℤ) := rfl

theorem isMultiplicative_totientZ : totientZ.IsMultiplicative := by
  refine ⟨by simp, @fun m n h => ?_⟩
  simp [Nat.totient_mul h]

/-- **The primitive-conductor weight** `A = φ * μ` (Dirichlet convolution).
`A(n)` counts the primitive Dirichlet characters of conductor `n`
(OEIS A007431); it is multiplicative, nonnegative, vanishes exactly on
`n ≡ 2 (mod 4)`, and satisfies `A(p) = p - 2`, `A(p^e) = (p-1)²·p^(e-2)`. -/
def primWeight : ArithmeticFunction ℤ := totientZ * moebius

theorem isMultiplicative_primWeight : primWeight.IsMultiplicative :=
  isMultiplicative_totientZ.mul isMultiplicative_moebius

/-- `A * ζ = φ`: summing the primitive-conductor weight over divisors
recovers the totient — the inversion that makes `L(A) = S`. -/
theorem primWeight_mul_zeta :
    primWeight * (↑(zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) = totientZ := by
  rw [primWeight, mul_assoc, moebius_mul_coe_zeta, mul_one]

theorem sum_divisors_primWeight (n : ℕ) :
    ∑ e ∈ n.divisors, primWeight e = (Nat.totient n : ℤ) := by
  have h : (primWeight * (↑(zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) n
      = totientZ n := by
    rw [primWeight_mul_zeta]
  rwa [coe_mul_zeta_apply, totientZ_apply] at h

/-- Prime-power values: `A(p^k) = φ(p^k) - φ(p^(k-1))`.  Only the divisor
pairs `(p^k, 1)` and `(p^(k-1), p)` survive the Möbius factor. -/
theorem primWeight_apply_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    primWeight (p ^ k)
      = (Nat.totient (p ^ k) : ℤ) - (Nat.totient (p ^ (k - 1)) : ℤ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_ne_zero hk).symm⟩
  rw [primWeight, mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun a b => totientZ a * moebius b),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∑ i ∈ Finset.range j,
      totientZ (p ^ i) * moebius (p ^ (j + 1) / p ^ i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hilt : i < j := Finset.mem_range.mp hi
    rw [Nat.pow_div (by omega) hp.pos,
      moebius_apply_prime_pow hp (by omega : j + 1 - i ≠ 0), if_neg (by omega)]
    ring
  have htop : p ^ (j + 1) / p ^ (j + 1) = 1 :=
    Nat.div_self (pow_pos hp.pos _)
  have hsnd : p ^ (j + 1) / p ^ j = p := by
    rw [Nat.pow_div (by omega) hp.pos]
    simp
  rw [hzero, htop, hsnd, moebius_apply_one, moebius_apply_prime hp]
  simp only [totientZ_apply, Nat.add_sub_cancel]
  ring

theorem primWeight_apply_prime {p : ℕ} (hp : p.Prime) :
    primWeight p = (p : ℤ) - 2 := by
  have h := primWeight_apply_prime_pow hp (k := 1) one_ne_zero
  rw [pow_one] at h
  rw [h, Nat.totient_prime hp]
  simp only [Nat.sub_self, pow_zero, Nat.totient_one]
  have h2 : 2 ≤ p := hp.two_le
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
  ring

/-- The primitive-conductor weight is unbounded already on prime inputs.
This is the exact obstruction to feeding `primWeight` into the kernel's
bounded eventually-periodic weighted Erdős-series theorem: its periodic
support does not make its multiplicities periodic. -/
theorem primWeight_unbounded_on_primes (B : ℕ) :
    ∃ p : ℕ, p.Prime ∧ (B : ℤ) < primWeight p := by
  obtain ⟨p, hpLower, hp⟩ := Nat.exists_infinite_primes (B + 3)
  refine ⟨p, hp, ?_⟩
  rw [primWeight_apply_prime hp]
  have hpLowerZ : ((B + 3 : ℕ) : ℤ) ≤ (p : ℤ) := by
    exact_mod_cast hpLower
  omega

/-- No uniform natural bound exists for `primWeight`. -/
theorem primWeight_not_bounded :
    ¬ ∃ B : ℕ, ∀ n : ℕ, primWeight n ≤ (B : ℤ) := by
  rintro ⟨B, hB⟩
  obtain ⟨p, _hp, hpB⟩ := primWeight_unbounded_on_primes B
  exact (not_lt_of_ge (hB p)) hpB

/-- **Prime-wise Dold defect of the primitive-conductor weight.**  At every
odd prime `p`, the primitive-coordinate numerator `A(p) = p - 2` is not
divisible by `p`.  Equivalently, the normalized Euler/Witt coordinate
`A(p) / p` is not integral.  This is the local arithmetic obstruction behind
the global determinant contour for Erdős #249; it does not imply the
irrationality of the #249 value. -/
theorem primWeight_prime_dold_defect {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    ¬ (p : ℤ) ∣ primWeight p := by
  rw [primWeight_apply_prime hp]
  have hpgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hpodd)
  have hp3 : 3 ≤ p := hpgt
  have hcast : (p : ℤ) - 2 = ((p - 2 : ℕ) : ℤ) := by
    rw [Int.ofNat_sub (by omega : 2 ≤ p)]
    norm_num
  rw [hcast, Int.natCast_dvd_natCast]
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

/-- Rational-coordinate form of `primWeight_prime_dold_defect`: the normalized
primitive coordinate `A(p) / p` cannot be the image of an integer at an odd
prime. -/
theorem primWeight_div_prime_not_integer {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    ¬ ∃ z : ℤ, ((primWeight p : ℤ) : ℚ) / (p : ℚ) = (z : ℚ) := by
  intro h
  rcases h with ⟨z, hz⟩
  apply primWeight_prime_dold_defect hp hpodd
  refine ⟨z, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hrat : ((primWeight p : ℤ) : ℚ) = (p : ℚ) * (z : ℚ) := by
    calc
      ((primWeight p : ℤ) : ℚ) = (((primWeight p : ℤ) : ℚ) / (p : ℚ)) * (p : ℚ) := by
        field_simp
      _ = (z : ℚ) * (p : ℚ) := by rw [hz]
      _ = (p : ℚ) * (z : ℚ) := mul_comm _ _
  exact_mod_cast hrat

/-- The weight vanishes at `2` — primitive characters mod 2 do not exist.
This is the single local zero: `A(n) = 0` iff `n ≡ 2 (mod 4)`. -/
theorem primWeight_two : primWeight 2 = 0 := by
  have h := primWeight_apply_prime Nat.prime_two
  simpa using h

/-- **Nonnegativity of the primitive-conductor weight.**  Each prime-power
factor is `φ(p^k) - φ(p^(k-1)) ≥ 0` since `φ` respects divisibility. -/
theorem primWeight_nonneg (n : ℕ) : 0 ≤ primWeight n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [isMultiplicative_primWeight.multiplicative_factorization _ hn.ne']
    rw [Finsupp.prod]
    refine Finset.prod_nonneg fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by
      rwa [← Nat.support_factorization])
    have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    rw [primWeight_apply_prime_pow hpp hk, sub_nonneg]
    exact_mod_cast Nat.le_of_dvd
      (Nat.totient_pos.mpr (pow_pos hpp.pos _))
      (Nat.totient_dvd_of_dvd (pow_dvd_pow p (Nat.sub_le _ 1)))

/-- Upper growth: `A(n) ≤ φ(n)` (immediate from `A ≥ 0` and `A * ζ = φ`). -/
theorem primWeight_le_totient (n : ℕ) : primWeight n ≤ (Nat.totient n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc primWeight n
        ≤ ∑ e ∈ n.divisors, primWeight e :=
          Finset.single_le_sum (fun e _ => primWeight_nonneg e)
            (Nat.mem_divisors_self n hn.ne')
      _ = (Nat.totient n : ℤ) := sum_divisors_primWeight n

/-! ## Möbius divisor sums -/

theorem abs_moebius_le_one (n : ℕ) : |moebius n| ≤ 1 := by
  by_cases h : Squarefree n
  · rw [abs_moebius_eq_one_of_squarefree h]
  · rw [moebius_eq_zero_of_not_squarefree h]
    norm_num

theorem sum_divisors_moebius (n : ℕ) :
    ∑ e ∈ n.divisors, moebius e = if n = 1 then 1 else 0 := by
  have h : (moebius * (↑(zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) n
      = (1 : ArithmeticFunction ℤ) n := by
    rw [moebius_mul_coe_zeta]
  rwa [coe_mul_zeta_apply, one_apply] at h

/-- Möbius inversion of `∑_{d∣n} φ(d) = n`: the totient as the
`μ * Id` convolution, in exactly the divisor-sum shape the squared
Lambert engine emits. -/
theorem sum_divisors_moebius_mul_div (n : ℕ) (hn : 0 < n) :
    ∑ e ∈ n.divisors, moebius e * ((n / e : ℕ) : ℤ) = (Nat.totient n : ℤ) := by
  have hbase : ∀ m : ℕ, 0 < m →
      ∑ i ∈ m.divisors, (Nat.totient i : ℤ) = (m : ℤ) := by
    intro m _
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.sum_totient m)
  have h := (sum_eq_iff_sum_smul_moebius_eq
      (f := fun i => (Nat.totient i : ℤ)) (g := fun i => (i : ℤ))).mp hbase n hn
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun a b => moebius a • ((b : ℕ) : ℤ))] at h
  simpa [zsmul_eq_mul] using h

/-! ## The four ladder identities (generic `0 ≤ r < 1`) -/

/-- **`L(φ)`-rung, Lambert form**: `∑ φ(d)·r^d/(1-r^d) = ∑ n·rⁿ`.
The totient Lambert series collapses to the rational function `r/(1-r)²`. -/
theorem tsum_totient_lambert {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)))
      = ∑' n : ℕ+, ((n : ℕ) : ℝ) * r ^ (n : ℕ) := by
  rw [tsum_lambert_linear_weight (fun e => (Nat.totient e : ℝ))
    (fun d _ => by
      show |(Nat.totient d : ℝ)| ≤ (d : ℝ)
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast Nat.totient_le d) hr0 hr1]
  refine tsum_congr fun n => ?_
  congr 1
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_totient (n : ℕ))

/-- **`L(μ)`-rung, Lambert form**: `∑ μ(d)·r^d/(1-r^d) = r`.
Only the `n = 1` divisor sum survives (`μ * ζ = ε`). -/
theorem tsum_moebius_lambert {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)))
      = r := by
  rw [tsum_lambert_linear_weight (fun e => ((moebius e : ℤ) : ℝ))
    (fun d hd => by
      show |((moebius d : ℤ) : ℝ)| ≤ (d : ℝ)
      have h1 : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast abs_moebius_le_one d
      exact h1.trans (by exact_mod_cast hd)) hr0 hr1]
  have hcoeff : ∀ n : ℕ+, (∑ e ∈ (n : ℕ).divisors, ((moebius e : ℤ) : ℝ))
      = if (n : ℕ) = 1 then (1 : ℝ) else 0 := by
    intro n
    have h := congrArg (fun z : ℤ => (z : ℝ)) (sum_divisors_moebius (n : ℕ))
    push_cast at h
    simpa [apply_ite (fun z : ℤ => (z : ℝ))] using h
  calc ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, ((moebius e : ℤ) : ℝ)) * r ^ (n : ℕ)
      = ∑' n : ℕ+, (if (n : ℕ) = 1 then (1 : ℝ) else 0) * r ^ (n : ℕ) := by
        refine tsum_congr fun n => ?_
        rw [hcoeff]
    _ = r := by
        rw [tsum_eq_single (1 : ℕ+) (fun b hb => ?_)]
        · simp
        · have hb1 : (b : ℕ) ≠ 1 := fun h => hb (PNat.coe_injective (by simpa using h))
          simp [hb1]

/-- **The positive lift, Lambert form**: `∑ A(d)·r^d/(1-r^d) = ∑ φ(n)·rⁿ`.
The `#249` power series IS the Mersenne–Lambert transform of the
nonnegative primitive-conductor weight (`A * ζ = φ`). -/
theorem tsum_primWeight_lambert {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, ((primWeight (d : ℕ) : ℤ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)))
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * r ^ (n : ℕ) := by
  rw [tsum_lambert_linear_weight (fun e => ((primWeight e : ℤ) : ℝ))
    (fun d hd => by
      show |((primWeight d : ℤ) : ℝ)| ≤ (d : ℝ)
      have h0 : (0 : ℤ) ≤ primWeight d := primWeight_nonneg d
      have h1 : primWeight d ≤ (d : ℤ) :=
        (primWeight_le_totient d).trans (by exact_mod_cast Nat.totient_le d)
      rw [abs_of_nonneg (by exact_mod_cast h0)]
      exact_mod_cast h1) hr0 hr1]
  refine tsum_congr fun n => ?_
  congr 1
  have h := congrArg (fun z : ℤ => (z : ℝ)) (sum_divisors_primWeight (n : ℕ))
  push_cast at h
  simpa using h

/-- **Möbius-square lens, Lambert form**: `∑ μ(d)·r^d/(1-r^d)² = ∑ φ(n)·rⁿ`.
The `#249` power series as a signed squared-Mersenne Lambert series
(`μ * Id = φ`). -/
theorem tsum_moebius_lambert_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * r ^ (n : ℕ) := by
  rw [tsum_lambert_linear_weight_sq (fun e => ((moebius e : ℤ) : ℝ))
    (fun d hd => by
      show |((moebius d : ℤ) : ℝ)| ≤ (d : ℝ)
      have h1 : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast abs_moebius_le_one d
      exact h1.trans (by exact_mod_cast hd)) hr0 hr1]
  refine tsum_congr fun n => ?_
  congr 1
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (sum_divisors_moebius_mul_div (n : ℕ) n.pos)
  push_cast at h
  simpa using h

/-! ## Evaluations at `r = 1/2`: the Mersenne forms -/

private lemma two_pow_sub_one_pos (d : ℕ) (hd : 0 < d) : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
  have h1 : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ one_lt_two hd.ne'
  linarith

private lemma half_pow_term (d : ℕ) (hd : 0 < d) :
    ((1 : ℝ) / 2) ^ d / (1 - ((1 : ℝ) / 2) ^ d) = 1 / ((2 : ℝ) ^ d - 1) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have h1 := two_pow_sub_one_pos d hd
  have h2ne : (2 : ℝ) ^ d ≠ 0 := ne_of_gt h2
  have h1ne : (2 : ℝ) ^ d - 1 ≠ 0 := ne_of_gt h1
  have hmid : (1 : ℝ) - 1 / (2 : ℝ) ^ d ≠ 0 := by
    have hEq : (1 : ℝ) - 1 / (2 : ℝ) ^ d = ((2 : ℝ) ^ d - 1) / (2 : ℝ) ^ d := by
      field_simp
    rw [hEq]
    exact div_ne_zero h1ne h2ne
  rw [div_pow, one_pow]
  field_simp

private lemma half_pow_sq_term (d : ℕ) (hd : 0 < d) :
    ((1 : ℝ) / 2) ^ d / (1 - ((1 : ℝ) / 2) ^ d) ^ 2
      = (2 : ℝ) ^ d / ((2 : ℝ) ^ d - 1) ^ 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have h1 := two_pow_sub_one_pos d hd
  have h2ne : (2 : ℝ) ^ d ≠ 0 := ne_of_gt h2
  have h1ne : (2 : ℝ) ^ d - 1 ≠ 0 := ne_of_gt h1
  have hmid : (1 : ℝ) - 1 / (2 : ℝ) ^ d ≠ 0 := by
    have hEq : (1 : ℝ) - 1 / (2 : ℝ) ^ d = ((2 : ℝ) ^ d - 1) / (2 : ℝ) ^ d := by
      field_simp
    rw [hEq]
    exact div_ne_zero h1ne h2ne
  rw [div_pow, one_pow]
  field_simp

private lemma mersenne_split (d : ℕ) (hd : 0 < d) :
    (2 : ℝ) ^ d / ((2 : ℝ) ^ d - 1) ^ 2
      = 1 / ((2 : ℝ) ^ d - 1) + 1 / ((2 : ℝ) ^ d - 1) ^ 2 := by
  have h1 := two_pow_sub_one_pos d hd
  have h1ne : (2 : ℝ) ^ d - 1 ≠ 0 := ne_of_gt h1
  field_simp
  ring

/-- `∑_{n≥1} n/2ⁿ = 2` — the rational value the totient Lambert series hits. -/
private lemma tsum_pnat_mul_half_pow :
    ∑' n : ℕ+, ((n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) = 2 := by
  have hr : ‖(1 : ℝ) / 2‖ < 1 := by
    rw [Real.norm_eq_abs]
    norm_num
  have hsum : Summable (fun j : ℕ => (j : ℝ) * ((1 : ℝ) / 2) ^ j) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
    exact h.congr fun j => by rw [pow_one]
  have hgeo : ∑' j : ℕ, (j : ℝ) * ((1 : ℝ) / 2) ^ j = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one hr]
    norm_num
  calc ∑' n : ℕ+, ((n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)
      = ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (j + 1) :=
        tsum_pnat_eq_tsum_succ (f := fun j : ℕ => (j : ℝ) * ((1 : ℝ) / 2) ^ j)
    _ = ∑' j : ℕ, (j : ℝ) * ((1 : ℝ) / 2) ^ j := by
        rw [hsum.tsum_eq_zero_add]
        push_cast
        simp
    _ = 2 := hgeo

/-- **Rational rung `L(φ) = 2`**: `∑_{d≥1} φ(d)/(2^d - 1) = 2`, exactly.
The Lambert transform of the `#249` coefficients at the `#249` point is
rational — the entire difficulty of #249 lives on the power-series side. -/
theorem tsum_totient_div_two_pow_sub_one_eq_two :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 2 := by
  have h := tsum_totient_lambert (r := 1 / 2) (by norm_num) (by norm_num)
  calc ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1)
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ)
          * (((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ))) := by
        refine tsum_congr fun d => ?_
        rw [half_pow_term (d : ℕ) d.pos, mul_one_div]
    _ = ∑' n : ℕ+, ((n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) := h
    _ = 2 := tsum_pnat_mul_half_pow

/-- **Rational rung `L(μ) = 1/2`**: `∑_{d≥1} μ(d)/(2^d - 1) = 1/2`, exactly. -/
theorem tsum_moebius_div_two_pow_sub_one_eq_half :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2 := by
  have h := tsum_moebius_lambert (r := 1 / 2) (by norm_num) (by norm_num)
  calc ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1)
      = ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ)
          * (((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ))) := by
        refine tsum_congr fun d => ?_
        rw [half_pow_term (d : ℕ) d.pos, mul_one_div]
    _ = 1 / 2 := h

/-- **The positive lift at `1/2`**: `∑_{d≥1} A(d)/(2^d - 1) = ∑_{n≥1} φ(n)·(1/2)ⁿ`.
The `#249` constant IS a positive Erdős–Borwein-type constant: same shape as
`E = ∑ 1/(2^d - 1)` (irrational, machine-checked in the kernel), with the
weight `1` replaced by the primitive-conductor count `A ≥ 0`. -/
theorem tsum_primWeight_div_two_pow_sub_one :
    ∑' d : ℕ+, ((primWeight (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  have h := tsum_primWeight_lambert (r := 1 / 2) (by norm_num) (by norm_num)
  calc ∑' d : ℕ+, ((primWeight (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1)
      = ∑' d : ℕ+, ((primWeight (d : ℕ) : ℤ) : ℝ)
          * (((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ))) := by
        refine tsum_congr fun d => ?_
        rw [half_pow_term (d : ℕ) d.pos, mul_one_div]
    _ = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) := h

private lemma summable_moebius_div_mersenne :
    Summable (fun d : ℕ+ => ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1)) := by
  have hgeo : Summable (fun d : ℕ+ => 2 * ((1 : ℝ) / 2) ^ (d : ℕ)) := by
    have h : Summable (fun n : ℕ => 2 * ((1 : ℝ) / 2) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
    exact h.subtype _
  refine Summable.of_norm_bounded hgeo fun d => ?_
  have h1 := two_pow_sub_one_pos (d : ℕ) d.pos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (d : ℕ) := by positivity
  have hd2 : (2 : ℝ) ≤ (2 : ℝ) ^ (d : ℕ) := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ (d : ℕ) := pow_le_pow_right₀ (by norm_num) d.pos
  have hmu : |((moebius (d : ℕ) : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_moebius_le_one (d : ℕ)
  have hgeq : 2 * ((1 : ℝ) / 2) ^ (d : ℕ) = 2 / (2 : ℝ) ^ (d : ℕ) := by
    rw [div_pow, one_pow]
    ring
  rw [Real.norm_eq_abs, abs_div, abs_of_pos h1, hgeq,
    div_le_div_iff₀ h1 h2]
  nlinarith [mul_le_mul_of_nonneg_right hmu h2.le]

/-- Absolute convergence of the squared-Mersenne Möbius series.  This is
public because finite-enclosure owners need to split the series at a cutoff
without duplicating the Lambert-ladder convergence proof. -/
theorem summable_moebius_div_mersenne_sq :
    Summable (fun d : ℕ+ =>
      ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  have hgeo : Summable (fun d : ℕ+ => 2 * ((1 : ℝ) / 2) ^ (d : ℕ)) := by
    have h : Summable (fun n : ℕ => 2 * ((1 : ℝ) / 2) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
    exact h.subtype _
  refine Summable.of_norm_bounded hgeo fun d => ?_
  have h1 := two_pow_sub_one_pos (d : ℕ) d.pos
  have h1sq : (0 : ℝ) < ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (d : ℕ) := by positivity
  have hd2 : (2 : ℝ) ≤ (2 : ℝ) ^ (d : ℕ) := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ (d : ℕ) := pow_le_pow_right₀ (by norm_num) d.pos
  have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (d : ℕ) - 1 := by linarith
  have hmu : |((moebius (d : ℕ) : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_moebius_le_one (d : ℕ)
  have hgeq : 2 * ((1 : ℝ) / 2) ^ (d : ℕ) = 2 / (2 : ℝ) ^ (d : ℕ) := by
    rw [div_pow, one_pow]
    ring
  rw [Real.norm_eq_abs, abs_div, abs_of_pos h1sq, hgeq,
    div_le_div_iff₀ h1sq h2, pow_two]
  nlinarith [mul_le_mul_of_nonneg_right hmu h2.le,
    mul_le_mul_of_nonneg_right hge1 h1.le]

/-- **The Möbius-square lens at `1/2`**:
`∑ φ(n)·(1/2)ⁿ = 1/2 + ∑_{d≥1} μ(d)/(2^d - 1)²`. -/
theorem tsum_totient_half_pow_eq_half_add_moebius_sq :
    ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)
      = 1 / 2 + ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  have h := tsum_moebius_lambert_sq (r := 1 / 2) (by norm_num) (by norm_num)
  have hsplit : ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ)
      * (((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ)) ^ 2)
      = (∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1))
        + ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
    rw [← Summable.tsum_add summable_moebius_div_mersenne summable_moebius_div_mersenne_sq]
    refine tsum_congr fun d => ?_
    have h1 := two_pow_sub_one_pos (d : ℕ) d.pos
    rw [half_pow_sq_term (d : ℕ) d.pos, mersenne_split (d : ℕ) d.pos]
    rw [mul_add, mul_one_div, mul_one_div]
  rw [← h, hsplit, tsum_moebius_div_two_pow_sub_one_eq_half]

-- Axiom audit: every result must rest only on the foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms tsum_lambert_pair_regroup
#print axioms primWeight_prime_dold_defect
#print axioms primWeight_div_prime_not_integer
#print axioms primWeight_unbounded_on_primes
#print axioms primWeight_not_bounded
#print axioms primWeight_nonneg
#print axioms tsum_totient_div_two_pow_sub_one_eq_two
#print axioms tsum_moebius_div_two_pow_sub_one_eq_half
#print axioms tsum_primWeight_div_two_pow_sub_one
#print axioms tsum_totient_half_pow_eq_half_add_moebius_sq

end MersenneLambertLadder
