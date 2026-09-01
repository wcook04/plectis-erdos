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
import Erdos257PeriodNoncollapse.GeometricCoprimality

/-!
# The squared Lambert transform: gcd moments and Stern–Brocot cylinders

Wave 18 read `L(f) = ∑ f(d)/(2ᵈ-1)` as the divisor calculus of ONE fair-coin
waiting time `X` (`P(d ∣ X) = 1/(2ᵈ-1)`).  Wave 19 added the second variable:
`S - 1/2 = P(gcd(X,Y) = 1)` for independent fair-coin `X, Y`.  This file lands
the calculus that the pair `(X, Y)` actually carries — the SQUARED kernel

  `L₂(f) = ∑_{d≥1} f(d)/(2ᵈ-1)² = E[(f * ζ)(gcd(X,Y))]`,

because `P(d ∣ gcd(X,Y)) = P(d ∣ X)·P(d ∣ Y) = 1/(2ᵈ-1)²` — divisibility of
the gcd FACTORIZES through the independent coordinates
(`tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`).  The transfer engine is
wave 18's signed linear-growth pair regrouping with second weight `v(m) = m-1`
(the coefficient of the *pure square* `(x/(1-x))² = ∑_{m≥2}(m-1)xᵐ`), giving

  `∑ w(d)·(rᵈ/(1-rᵈ))² = ∑_n (∑_{e∣n} w(e)·(n/e - 1))·rⁿ`   for `|w(d)| ≤ d`.

The two-variable ladder this produces, at `r = 1/2` (all machine-checked):

* `L₂(μ) = S - 1/2 = P(gcd(X,Y) = 1)`     — the OPEN #249 atom (wave 18/19),
* `L₂(1) = ∑ (σ(n)-τ(n))/2ⁿ = E[τ(gcd)]`  — the q-zeta anchor `ζ_q(2)-ζ_q(1)`
  at `q = 1/2` (irrational by Postelmans–Van Assche q-Padé; cited, NOT
  formalised here — the identity is what this file proves),
* `L₂(φ) = ∑ (P(n)-n)/2ⁿ = E[gcd(X,Y)]`   — `P(n) = ∑_{e∣n} φ(e)·(n/e)` is
  Pillai's gcd-sum function (`id * φ`),
* `∑_{(a,b)=1} 1/(2^{a+b}-1) = 1`          — the reduced-direction law: every
  positive pair has a unique reduced slope, and the slope masses sum to one.

The MIRROR that makes #249 sharp: at level 1 the Möbius rung is trivially
rational (`L(μ) = 1/2`) and the ζ-rung is the hard irrational (Erdős 1948,
`L(1) = E`); at level 2 the ζ-rung is the known irrational (`L₂(1)`, q-Padé)
and the Möbius rung IS #249.  Möbius projection is the entire remaining wall.

The second half of the file is the **Stern–Brocot cylinder law**.  For the
mediant children `(a,b) ↦ (a+b, b)` and `(a,b) ↦ (a, a+b)` the closed form
`M(a,b) = 1/((2ᵃ-1)(2ᵇ-1))` satisfies the EXACT telescoping recursion

  `M(a,b) = 1/(2^{a+b}-1) + M(a+b, b) + M(a, a+b)`
  (`cylinderMass_split` — note `M(a,b) = P(a ∣ X)·P(b ∣ Y)`: cylinder masses
  of the reduced direction factorize through coordinate divisibility),

and the depth-`d` finite unfolding `sternBrocotDepthMass` converges to it with
explicit geometric rate `(2/3)ᵈ` (`sternBrocotDepthMass_error`,
`tendsto_sternBrocotDepthMass`) — the children-to-parent mass ratio is at most
`2/3`, with equality exactly at the root `(1,1)`.  All-left cusp cylinders
`(N,1)` have mass `1/(2ᴺ-1)`: near-Mersenne reciprocals, one exponential order
closer to the Erdős–Borwein engine than the raw totient coefficients.

The honest boundary: every statement is an equality/limit of convergent real
series (probability readings are the doc layer; no measure theory).  Nothing
here decides irrationality of `S`; `L₂(1)`'s irrationality is cited to the
q-Padé literature, not formalised; the full subtree-enumeration reading of
`cylinderMass` (that the recursion's limit is the subtree mass under the
slow-Euclid bijection) is wave-21 work — this file proves the recursion, its
closed form, and its rate, which is what a cusp-isolation attack consumes.
-/

namespace GcdMomentCalculus

open MersenneLambertLadder

/-! ## The pure-square geometric weight `v(m) = m - 1` -/

/-- `∑_{m≥1} (m-1)·xᵐ = (x/(1-x))²` — the pure square of the geometric tail,
with the `m = 1` term vanishing.  This is the second-weight profile that turns
the wave-18 pair engine into the squared-kernel transfer. -/
private lemma tsum_pnat_pred_mul_geometric {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' m : ℕ+, (((m : ℕ) : ℝ) - 1) * x ^ (m : ℕ) = (x / (1 - x)) ^ 2 := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  calc ∑' m : ℕ+, (((m : ℕ) : ℝ) - 1) * x ^ (m : ℕ)
      = ∑' j : ℕ, (((j + 1 : ℕ) : ℝ) - 1) * x ^ (j + 1) :=
        tsum_pnat_eq_tsum_succ (f := fun j : ℕ => ((j : ℝ) - 1) * x ^ j)
    _ = ∑' j : ℕ, (j : ℝ) * x ^ j * x := by
        refine tsum_congr fun j => ?_
        push_cast
        ring
    _ = (∑' j : ℕ, (j : ℝ) * x ^ j) * x := tsum_mul_right
    _ = (x / (1 - x) ^ 2) * x := by rw [tsum_coe_mul_geometric_of_norm_lt_one hnorm]
    _ = (x / (1 - x)) ^ 2 := by
        rw [div_pow]
        ring

/-! ## The squared-kernel transfer engine -/

/-- **Signed linear-growth PURE-squared-Lambert identity**:
`∑_d w(d)·(rᵈ/(1-rᵈ))² = ∑_n (∑_{e∣n} w(e)·(n/e - 1))·rⁿ` for `|w(d)| ≤ d`.
The divisor coefficient is `(w * Id)(n) - (w * ζ)(n)`: one theorem carries the
whole level-2 ladder.  Rides wave 18's `tsum_lambert_pair_regroup` with second
weight `v(m) = m - 1`. -/
theorem tsum_lambert_linear_weight_sq_pure
    (w : ℕ → ℝ) (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * ((((n : ℕ) / e : ℕ) : ℝ) - 1))
          * r ^ (n : ℕ) := by
  have hv : ∀ m : ℕ, 0 < m → |((m : ℝ) - 1)| ≤ (m : ℝ) := by
    intro m hm
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hprod := summable_lambert_pair w (fun m => (m : ℝ) - 1) hw hv hr0 hr1
  have hterm : ∀ d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' m : ℕ+, w (d : ℕ) * (((m : ℕ) : ℝ) - 1) * r ^ ((d : ℕ) * (m : ℕ)) := by
    intro d
    have hd0 : (d : ℕ) ≠ 0 := d.pos.ne'
    have hx0 : (0 : ℝ) ≤ r ^ (d : ℕ) := pow_nonneg hr0 _
    have hx1 : r ^ (d : ℕ) < 1 := pow_lt_one₀ hr0 hr1 hd0
    rw [← tsum_pnat_pred_mul_geometric hx0 hx1, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [← mul_assoc, ← pow_mul]
  calc ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' d : ℕ+, ∑' m : ℕ+, w (d : ℕ) * (((m : ℕ) : ℝ) - 1) * r ^ ((d : ℕ) * (m : ℕ)) :=
        tsum_congr hterm
    _ = ∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * (((p.2 : ℕ) : ℝ) - 1) * r ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
        (hprod.tsum_prod).symm
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * ((((n : ℕ) / e : ℕ) : ℝ) - 1))
          * r ^ (n : ℕ) :=
        tsum_lambert_pair_regroup w (fun m => (m : ℝ) - 1) hw hv hr0 hr1

/-! ## The two new rungs at generic `0 ≤ r < 1` -/

/-- **`L₂(1)`-rung, Lambert form**: `∑_d (rᵈ/(1-rᵈ))² = ∑_n (σ(n) - τ(n))·rⁿ`.
The coefficient is spelled as its divisor sums: `σ(n) = ∑_{e∣n} n/e` and
`τ(n) = #divisors(n)`. -/
theorem tsum_one_lambert_sq_pure {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (((n : ℕ) / e : ℕ) : ℝ)) - ((n : ℕ).divisors.card : ℝ))
            * r ^ (n : ℕ) := by
  have h := tsum_lambert_linear_weight_sq_pure (fun _ => 1)
    (fun d hd => by
      show |(1 : ℝ)| ≤ (d : ℝ)
      rw [abs_one]
      exact_mod_cast hd) hr0 hr1
  calc ∑' d : ℕ+, (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' d : ℕ+, (1 : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2 := by
        refine tsum_congr fun d => ?_
        rw [one_mul]
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, (1 : ℝ) * ((((n : ℕ) / e : ℕ) : ℝ) - 1))
          * r ^ (n : ℕ) := h
    _ = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (((n : ℕ) / e : ℕ) : ℝ)) - ((n : ℕ).divisors.card : ℝ))
            * r ^ (n : ℕ) := by
        refine tsum_congr fun n => ?_
        congr 1
        rw [Finset.sum_congr rfl (fun e _ => one_mul _), Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **`L₂(φ)`-rung, Lambert form**:
`∑_d φ(d)·(rᵈ/(1-rᵈ))² = ∑_n (P(n) - n)·rⁿ`, where `P(n) = ∑_{e∣n} φ(e)·(n/e)`
is Pillai's gcd-sum function (`φ * Id`); the subtracted `n` is `φ * ζ = Id`. -/
theorem tsum_totient_lambert_sq_pure {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * r ^ (n : ℕ) := by
  have h := tsum_lambert_linear_weight_sq_pure (fun e => (Nat.totient e : ℝ))
    (fun d _ => by
      show |(Nat.totient d : ℝ)| ≤ (d : ℝ)
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast Nat.totient_le d) hr0 hr1
  rw [h]
  refine tsum_congr fun n => ?_
  congr 1
  have hsplit : ∀ e ∈ (n : ℕ).divisors,
      (Nat.totient e : ℝ) * ((((n : ℕ) / e : ℕ) : ℝ) - 1)
        = (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ) - (Nat.totient e : ℝ) := by
    intro e _
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  congr 1
  exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (Nat.sum_totient (n : ℕ))

/-! ## Mersenne evaluations at `r = 1/2` -/

private lemma half_pow_term' (d : ℕ) (hd : 0 < d) :
    ((1 : ℝ) / 2) ^ d / (1 - ((1 : ℝ) / 2) ^ d) = 1 / ((2 : ℝ) ^ d - 1) := by
  have h1 : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ one_lt_two hd.ne'
  have h2 : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have h2ne : (2 : ℝ) ^ d ≠ 0 := ne_of_gt h2
  have h1ne : (2 : ℝ) ^ d - 1 ≠ 0 := by linarith
  have hmid : (1 : ℝ) - 1 / (2 : ℝ) ^ d ≠ 0 := by
    have hEq : (1 : ℝ) - 1 / (2 : ℝ) ^ d = ((2 : ℝ) ^ d - 1) / (2 : ℝ) ^ d := by
      field_simp
    rw [hEq]
    exact div_ne_zero h1ne h2ne
  rw [div_pow, one_pow]
  field_simp

private lemma half_pow_sq_term' (d : ℕ) (hd : 0 < d) :
    (((1 : ℝ) / 2) ^ d / (1 - ((1 : ℝ) / 2) ^ d)) ^ 2 = 1 / ((2 : ℝ) ^ d - 1) ^ 2 := by
  rw [half_pow_term' d hd, div_pow, one_pow]

/-- **The q-zeta anchor of the level-2 ladder**:
`∑_{d≥1} 1/(2ᵈ-1)² = ∑_{n≥1} (σ(n) - τ(n))·(1/2)ⁿ`, exactly.
Probability reading: `E[τ(gcd(X,Y))] = ∑_d P(d ∣ gcd)`.  In q-zeta terms this
value is `ζ_q(2) - ζ_q(1)` at `q = 1/2` (Jouhet–Mosaki convention), irrational
by the Postelmans–Van Assche q-Padé theorem — cited, NOT formalised; what is
machine-checked here is the identity. -/
theorem tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series :
    ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (((n : ℕ) / e : ℕ) : ℝ)) - ((n : ℕ).divisors.card : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  have h := tsum_one_lambert_sq_pure (r := 1 / 2) (by norm_num) (by norm_num)
  calc ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' d : ℕ+, (((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ))) ^ 2 := by
        refine tsum_congr fun d => ?_
        rw [half_pow_sq_term' (d : ℕ) d.pos]
    _ = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (((n : ℕ) / e : ℕ) : ℝ)) - ((n : ℕ).divisors.card : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ) := h

/-- **The first gcd moment**:
`∑_{d≥1} φ(d)/(2ᵈ-1)² = ∑_{n≥1} (P(n) - n)·(1/2)ⁿ` with `P` Pillai's gcd-sum
function.  Probability reading: `E[gcd(X,Y)] = ∑_d φ(d)·P(d ∣ gcd)` — the
expected gcd of two independent fair-coin waiting times, as a totient-weighted
squared-Mersenne series. -/
theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  have h := tsum_totient_lambert_sq_pure (r := 1 / 2) (by norm_num) (by norm_num)
  calc ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ)
          * (((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ))) ^ 2 := by
        refine tsum_congr fun d => ?_
        rw [half_pow_sq_term' (d : ℕ) d.pos, mul_one_div]
    _ = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := h

/-! ## The divisibility factorization: `P(d ∣ gcd(X,Y)) = P(d ∣ X)·P(d ∣ Y)` -/

private lemma tsum_pow_succ_geometric' {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' g : ℕ, x ^ (g + 1) = x / (1 - x) := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one hnorm, ← tsum_mul_left]
  exact tsum_congr fun g => pow_succ' x g

/-- **Divisibility of the pair factorizes**: the fair-coin mass of
`{(a,b) : a,b ≥ 1, d ∣ a, d ∣ b}` is exactly `1/(2ᵈ-1)²` — i.e.
`P(d ∣ gcd(X,Y)) = P(d ∣ X)·P(d ∣ Y)`.  This is the foundation stone of the
squared kernel: `L₂(f) = ∑ f(d)·P(d ∣ gcd)`, and it is also why the
Stern–Brocot cylinder closed form `1/((2ᵃ-1)(2ᵇ-1))` is a product of
one-variable divisor probabilities. -/
theorem tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2 := by
  have hy0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ d := by positivity
  have hy1 : ((1 : ℝ) / 2) ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hd.ne'
  have hi : Function.Injective
      (fun q : ℕ × ℕ => ((d * (q.1 + 1), d * (q.2 + 1)) : ℕ × ℕ)) := by
    intro q q' h
    dsimp only at h
    rw [Prod.ext_iff] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : q.1 + 1 = q'.1 + 1 := Nat.eq_of_mul_eq_mul_left hd h1
    have e2 : q.2 + 1 = q'.2 + 1 := Nat.eq_of_mul_eq_mul_left hd h2
    rw [Prod.ext_iff]
    exact ⟨by omega, by omega⟩
  have hsupp : Function.support (fun p : ℕ × ℕ =>
      if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2 then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      ⊆ Set.range (fun q : ℕ × ℕ => ((d * (q.1 + 1), d * (q.2 + 1)) : ℕ × ℕ)) := by
    intro p hp
    rw [Function.mem_support] at hp
    by_cases hg : 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
    · obtain ⟨hp1, hp2, ⟨k, hk⟩, ⟨l, hl⟩⟩ := hg
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · rw [Nat.mul_zero] at hk
          omega
        · exact h
      have hl0 : 0 < l := by
        rcases Nat.eq_zero_or_pos l with rfl | h
        · rw [Nat.mul_zero] at hl
          omega
        · exact h
      refine ⟨(k - 1, l - 1), ?_⟩
      have hkk : k - 1 + 1 = k := by omega
      have hll : l - 1 + 1 = l := by omega
      show (d * (k - 1 + 1), d * (l - 1 + 1)) = p
      rw [hkk, hll, ← hk, ← hl]
    · exact absurd (if_neg hg) hp
  have key := hi.tsum_eq hsupp
  have hterm : ∀ q : ℕ × ℕ,
      (if 0 < d * (q.1 + 1) ∧ 0 < d * (q.2 + 1) ∧ d ∣ d * (q.1 + 1) ∧ d ∣ d * (q.2 + 1)
        then ((1 : ℝ) / 2) ^ (d * (q.1 + 1) + d * (q.2 + 1)) else 0)
      = (((1 : ℝ) / 2) ^ d) ^ (q.1 + 1) * (((1 : ℝ) / 2) ^ d) ^ (q.2 + 1) := by
    intro q
    rw [if_pos ⟨Nat.mul_pos hd (Nat.succ_pos _), Nat.mul_pos hd (Nat.succ_pos _),
      ⟨q.1 + 1, rfl⟩, ⟨q.2 + 1, rfl⟩⟩]
    rw [pow_add, ← pow_mul, ← pow_mul]
  have hgy : Summable (fun x : ℕ => (((1 : ℝ) / 2) ^ d) ^ (x + 1)) := by
    have h := summable_geometric_of_lt_one hy0 hy1
    exact (h.mul_left (((1 : ℝ) / 2) ^ d)).congr fun x => (pow_succ' _ x).symm
  have hprod : Summable (fun q : ℕ × ℕ =>
      (((1 : ℝ) / 2) ^ d) ^ (q.1 + 1) * (((1 : ℝ) / 2) ^ d) ^ (q.2 + 1)) :=
    hgy.mul_of_nonneg hgy (fun x => by positivity) (fun x => by positivity)
  have hxsum : ∑' x : ℕ, (((1 : ℝ) / 2) ^ d) ^ (x + 1) = 1 / ((2 : ℝ) ^ d - 1) := by
    rw [tsum_pow_succ_geometric' hy0 hy1]
    exact half_pow_term' d hd
  calc (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' q : ℕ × ℕ,
          (if 0 < d * (q.1 + 1) ∧ 0 < d * (q.2 + 1) ∧ d ∣ d * (q.1 + 1) ∧ d ∣ d * (q.2 + 1)
            then ((1 : ℝ) / 2) ^ (d * (q.1 + 1) + d * (q.2 + 1)) else 0) := key.symm
    _ = ∑' q : ℕ × ℕ, (((1 : ℝ) / 2) ^ d) ^ (q.1 + 1) * (((1 : ℝ) / 2) ^ d) ^ (q.2 + 1) :=
        tsum_congr hterm
    _ = ∑' x : ℕ, ∑' z : ℕ, (((1 : ℝ) / 2) ^ d) ^ (x + 1) * (((1 : ℝ) / 2) ^ d) ^ (z + 1) :=
        hprod.tsum_prod
    _ = ∑' x : ℕ, (((1 : ℝ) / 2) ^ d) ^ (x + 1) * ∑' z : ℕ, (((1 : ℝ) / 2) ^ d) ^ (z + 1) := by
        refine tsum_congr fun x => ?_
        exact tsum_mul_left
    _ = (∑' x : ℕ, (((1 : ℝ) / 2) ^ d) ^ (x + 1)) * ∑' z : ℕ, (((1 : ℝ) / 2) ^ d) ^ (z + 1) :=
        tsum_mul_right
    _ = (1 / ((2 : ℝ) ^ d - 1)) * (1 / ((2 : ℝ) ^ d - 1)) := by rw [hxsum]
    _ = 1 / ((2 : ℝ) ^ d - 1) ^ 2 := by
        rw [div_mul_div_comm, one_mul, sq]

/-! ## The reduced-direction law: total slope mass is `1` -/

/-- **The reduced-direction law**: `∑_{(a,b) coprime, a,b ≥ 1} 1/(2^{a+b}-1) = 1`.
Every positive pair `(X,Y)` has a unique reduced slope, and
`P(slope = a/b) = ∑_g 2^{-g(a+b)} = 1/(2^{a+b}-1)` for coprime `(a,b)`; the
masses sum to one.  Proved by expanding each Mersenne reciprocal as its
geometric layer series and swapping with the wave-19 gcd-layer normalization.
This is the root cylinder of the Stern–Brocot law: `M(1,1) = 1`. -/
theorem tsum_pos_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1 := by
  have hF : Summable (fun q : (ℕ × ℕ) × ℕ =>
      if 0 < q.1.1 ∧ 0 < q.1.2 ∧ Nat.Coprime q.1.1 q.1.2
      then (((1 : ℝ) / 2) ^ (q.2 + 1)) ^ (q.1.1 + q.1.2) else 0) := by
    have hmaj : Summable (fun q : (ℕ × ℕ) × ℕ =>
        ((1 : ℝ) / 2) ^ (q.1.1 + q.1.2) * ((1 : ℝ) / 2) ^ q.2) :=
      (GeometricCoprimality.summable_pow_add (by norm_num) (by norm_num)).mul_of_nonneg
        (summable_geometric_of_lt_one (by norm_num) (by norm_num))
        (fun p => by positivity) (fun g => by positivity)
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hmaj
    · by_cases h : 0 < q.1.1 ∧ 0 < q.1.2 ∧ Nat.Coprime q.1.1 q.1.2
      · rw [if_pos h]
        positivity
      · rw [if_neg h]
    · by_cases h : 0 < q.1.1 ∧ 0 < q.1.2 ∧ Nat.Coprime q.1.1 q.1.2
      · rw [if_pos h]
        have hab : 2 ≤ q.1.1 + q.1.2 := by
          have h1 := h.1
          have h2 := h.2.1
          omega
        have hle : q.1.1 + q.1.2 + q.2 ≤ (q.2 + 1) * (q.1.1 + q.1.2) := by nlinarith
        calc (((1 : ℝ) / 2) ^ (q.2 + 1)) ^ (q.1.1 + q.1.2)
            = ((1 : ℝ) / 2) ^ ((q.2 + 1) * (q.1.1 + q.1.2)) := by rw [← pow_mul]
          _ ≤ ((1 : ℝ) / 2) ^ (q.1.1 + q.1.2 + q.2) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
          _ = ((1 : ℝ) / 2) ^ (q.1.1 + q.1.2) * ((1 : ℝ) / 2) ^ q.2 := by rw [pow_add]
      · rw [if_neg h]
        positivity
  have hpoint : ∀ p : ℕ × ℕ,
      (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0)
      = ∑' g : ℕ, (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0) := by
    intro p
    by_cases h : 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
    · rw [if_pos h]
      have hn : 0 < p.1 + p.2 := by
        have h1 := h.1
        omega
      have hx0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (p.1 + p.2) := by positivity
      have hx1 : ((1 : ℝ) / 2) ^ (p.1 + p.2) < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
      calc 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1)
          = ((1 : ℝ) / 2) ^ (p.1 + p.2) / (1 - ((1 : ℝ) / 2) ^ (p.1 + p.2)) :=
            (half_pow_term' (p.1 + p.2) hn).symm
        _ = ∑' g : ℕ, (((1 : ℝ) / 2) ^ (p.1 + p.2)) ^ (g + 1) :=
            (tsum_pow_succ_geometric' hx0 hx1).symm
        _ = ∑' g : ℕ, (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) := by
            refine tsum_congr fun g => ?_
            rw [← pow_mul, Nat.mul_comm, pow_mul]
        _ = ∑' g : ℕ, (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
              then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0) := by
            refine tsum_congr fun g => ?_
            rw [if_pos h]
    · rw [if_neg h]
      symm
      calc ∑' g : ℕ, (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
            then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0)
          = ∑' g : ℕ, (0 : ℝ) := tsum_congr fun g => if_neg h
        _ = 0 := tsum_zero
  have hF' : Summable (fun q : ℕ × (ℕ × ℕ) =>
      if 0 < q.2.1 ∧ 0 < q.2.2 ∧ Nat.Coprime q.2.1 q.2.2
      then (((1 : ℝ) / 2) ^ (q.1 + 1)) ^ (q.2.1 + q.2.2) else 0) := by
    have h := hF.prod_symm
    exact h.congr fun q => rfl
  have hswap : ∑' p : ℕ × ℕ, ∑' g : ℕ,
      (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = ∑' g : ℕ, ∑' p : ℕ × ℕ,
          (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
            then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0) := by
    calc ∑' p : ℕ × ℕ, ∑' g : ℕ,
        (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0)
        = ∑' q : (ℕ × ℕ) × ℕ,
            (if 0 < q.1.1 ∧ 0 < q.1.2 ∧ Nat.Coprime q.1.1 q.1.2
              then (((1 : ℝ) / 2) ^ (q.2 + 1)) ^ (q.1.1 + q.1.2) else 0) :=
          (hF.tsum_prod).symm
      _ = ∑' q : ℕ × (ℕ × ℕ),
            (if 0 < q.2.1 ∧ 0 < q.2.2 ∧ Nat.Coprime q.2.1 q.2.2
              then (((1 : ℝ) / 2) ^ (q.1 + 1)) ^ (q.2.1 + q.2.2) else 0) :=
          ((Equiv.prodComm ℕ (ℕ × ℕ)).tsum_eq (f := fun q : (ℕ × ℕ) × ℕ =>
            if 0 < q.1.1 ∧ 0 < q.1.2 ∧ Nat.Coprime q.1.1 q.1.2
            then (((1 : ℝ) / 2) ^ (q.2 + 1)) ^ (q.1.1 + q.1.2) else 0)).symm
      _ = ∑' g : ℕ, ∑' p : ℕ × ℕ,
            (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
              then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0) :=
          hF'.tsum_prod
  rw [tsum_congr hpoint, hswap]
  exact GeometricCoprimality.tsum_gcd_layer_pos_coprime_half_eq_one

/-! ## The Stern–Brocot cylinder law -/

/-- The closed-form cylinder mass at the coprime node `(a,b)`:
`M(a,b) = 1/((2ᵃ-1)(2ᵇ-1)) = P(a ∣ X)·P(b ∣ Y)`. -/
noncomputable def cylinderMass (a b : ℕ+) : ℝ :=
  1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))

/-- The depth-`d` finite unfolding of the mediant recursion: sum the stop mass
`1/(2^{a+b}-1)` at every node of the first `d` generations of the subtree
rooted at `(a,b)`, under the children `(a+b, b)` and `(a, a+b)`. -/
noncomputable def sternBrocotDepthMass : ℕ → ℕ+ → ℕ+ → ℝ
  | 0, _, _ => 0
  | (dp + 1), a, b =>
      1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + sternBrocotDepthMass dp (a + b) b + sternBrocotDepthMass dp a (a + b)

private lemma two_le_two_pow (a : ℕ+) : (2 : ℝ) ≤ (2 : ℝ) ^ (a : ℕ) := by
  calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
    _ ≤ (2 : ℝ) ^ (a : ℕ) := pow_le_pow_right₀ (by norm_num) a.pos

theorem cylinderMass_pos (a b : ℕ+) : 0 < cylinderMass a b := by
  have ha := two_le_two_pow a
  have hb := two_le_two_pow b
  have hprod : (0 : ℝ) < ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1) := by nlinarith
  unfold cylinderMass
  exact div_pos one_pos hprod

/-- **The exact telescoping recursion of the cylinder mass**:
`M(a,b) = 1/(2^{a+b}-1) + M(a+b, b) + M(a, a+b)`.  With `A = 2ᵃ`, `B = 2ᵇ`
this is `1/((A-1)(B-1)) = 1/(AB-1) + 1/((AB-1)(B-1)) + 1/((A-1)(AB-1))` —
the algebra that makes the reduced-direction distribution an exact rational
Markov measure on the Stern–Brocot tree. -/
theorem cylinderMass_split (a b : ℕ+) :
    cylinderMass a b
      = 1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + cylinderMass (a + b) b + cylinderMass a (a + b) := by
  have hA := two_le_two_pow a
  have hB := two_le_two_pow b
  have hApos : (0 : ℝ) < (2 : ℝ) ^ (a : ℕ) - 1 := by linarith
  have hBpos : (0 : ℝ) < (2 : ℝ) ^ (b : ℕ) - 1 := by linarith
  have hABpos : (0 : ℝ) < (2 : ℝ) ^ (a : ℕ) * (2 : ℝ) ^ (b : ℕ) - 1 := by nlinarith
  unfold cylinderMass
  simp only [PNat.add_coe]
  rw [pow_add]
  have hAne : (2 : ℝ) ^ (a : ℕ) - 1 ≠ 0 := ne_of_gt hApos
  have hBne : (2 : ℝ) ^ (b : ℕ) - 1 ≠ 0 := ne_of_gt hBpos
  have hABne : (2 : ℝ) ^ (a : ℕ) * (2 : ℝ) ^ (b : ℕ) - 1 ≠ 0 := ne_of_gt hABpos
  field_simp
  ring

/-- The stop mass at a node is at least a third of its cylinder mass:
`(1/3)·M(a,b) ≤ 1/(2^{a+b}-1)`, i.e. `2^{a+b} - 1 ≤ 3(2ᵃ-1)(2ᵇ-1)` —
equality exactly at the root `(1,1)`. -/
private lemma stop_ge_third_cylinderMass (a b : ℕ+) :
    (1 / 3) * cylinderMass a b ≤ 1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) := by
  have hA := two_le_two_pow a
  have hB := two_le_two_pow b
  have hApos : (0 : ℝ) < (2 : ℝ) ^ (a : ℕ) - 1 := by linarith
  have hBpos : (0 : ℝ) < (2 : ℝ) ^ (b : ℕ) - 1 := by linarith
  have hprod : (0 : ℝ) < ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1) :=
    mul_pos hApos hBpos
  have hABpos : (0 : ℝ) < (2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1 := by
    rw [pow_add]
    nlinarith
  unfold cylinderMass
  rw [div_mul_div_comm, one_mul]
  rw [div_le_div_iff₀ (by positivity) hABpos]
  rw [pow_add]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ (a : ℕ) - 2)
    (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ (b : ℕ) - 2)]

/-- The two children carry at most `2/3` of the parent cylinder mass. -/
theorem cylinderMass_children_le (a b : ℕ+) :
    cylinderMass (a + b) b + cylinderMass a (a + b) ≤ (2 / 3) * cylinderMass a b := by
  have hsplit := cylinderMass_split a b
  have hstop := stop_ge_third_cylinderMass a b
  linarith

/-- **Finite-depth cylinder approximation with explicit geometric rate**:
`0 ≤ M(a,b) - M_d(a,b) ≤ (2/3)ᵈ·M(a,b)`.  The depth-`d` unfolding of the
mediant recursion exhausts the closed form at rate `(2/3)ᵈ`, uniformly over
all nodes — the error at depth `d` is exactly the frontier mass, and each
generation retains at most `2/3` of its parent mass. -/
theorem sternBrocotDepthMass_error (dp : ℕ) :
    ∀ a b : ℕ+,
      0 ≤ cylinderMass a b - sternBrocotDepthMass dp a b
        ∧ cylinderMass a b - sternBrocotDepthMass dp a b
            ≤ (2 / 3 : ℝ) ^ dp * cylinderMass a b := by
  induction dp with
  | zero =>
      intro a b
      constructor
      · simpa [sternBrocotDepthMass] using (cylinderMass_pos a b).le
      · simp [sternBrocotDepthMass]
  | succ dp ih =>
      intro a b
      obtain ⟨hL0, hLe⟩ := ih (a + b) b
      obtain ⟨hR0, hRe⟩ := ih a (a + b)
      have hsplit := cylinderMass_split a b
      have hchild := cylinderMass_children_le a b
      have hpow : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ dp := by positivity
      have hstep : cylinderMass a b - sternBrocotDepthMass (dp + 1) a b
          = (cylinderMass (a + b) b - sternBrocotDepthMass dp (a + b) b)
            + (cylinderMass a (a + b) - sternBrocotDepthMass dp a (a + b)) := by
        simp only [sternBrocotDepthMass]
        linarith
      constructor
      · rw [hstep]
        linarith
      · have hmul := mul_le_mul_of_nonneg_left hchild hpow
        rw [hstep, pow_succ]
        nlinarith [hLe, hRe, hmul]

/-- **The Stern–Brocot cylinder law, limit form**: the depth-`d` unfolding of
the mediant recursion at `(a,b)` converges to the closed form
`M(a,b) = 1/((2ᵃ-1)(2ᵇ-1))`, with explicit rate `(2/3)ᵈ` from
`sternBrocotDepthMass_error`.  At the root: `M(1,1) = 1`, matching the
reduced-direction law `tsum_pos_coprime_inv_mersenne_eq_one`. -/
theorem tendsto_sternBrocotDepthMass (a b : ℕ+) :
    Filter.Tendsto (fun dp : ℕ => sternBrocotDepthMass dp a b)
      Filter.atTop (nhds (cylinderMass a b)) := by
  have herr : Filter.Tendsto (fun dp : ℕ => (2 / 3 : ℝ) ^ dp * cylinderMass a b)
      Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)
    have h2 := h.mul_const (cylinderMass a b)
    simpa using h2
  have hsq : Filter.Tendsto
      (fun dp : ℕ => cylinderMass a b - sternBrocotDepthMass dp a b)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr
      (fun dp => (sternBrocotDepthMass_error dp a b).1)
      (fun dp => (sternBrocotDepthMass_error dp a b).2)
  have hconst : Filter.Tendsto (fun _ : ℕ => cylinderMass a b)
      Filter.atTop (nhds (cylinderMass a b)) := tendsto_const_nhds
  have hfin := hconst.sub hsq
  simpa using hfin

-- Axiom audit: every result must rest only on the foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms tsum_lambert_linear_weight_sq_pure
#print axioms tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series
#print axioms tsum_totient_div_mersenne_sq_eq_gcd_moment_series
#print axioms tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq
#print axioms tsum_pos_coprime_inv_mersenne_eq_one
#print axioms cylinderMass_split
#print axioms sternBrocotDepthMass_error
#print axioms tendsto_sternBrocotDepthMass

end GcdMomentCalculus
