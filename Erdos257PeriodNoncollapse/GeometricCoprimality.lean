import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Erdos257PeriodNoncollapse.MersenneLambertLadder

/-!
# Geometric coprimality: the #249 constant as visible-lattice mass

Let `X` be the fair-coin waiting time: `P(X = n) = 2⁻ⁿ` on `n ≥ 1`.  Its divisor
calculus is exactly the Mersenne–Lambert ladder of wave 18: `P(d ∣ X) = 1/(2ᵈ-1)`,
so `L(f) = ∑ f(d)/(2ᵈ-1) = E[(f * ζ)(X)]`, and the ladder rungs read

* `L(μ) = 1/2  = P(X = 1)`          (Möbius indicator `μ * ζ = ε`),
* `L(φ) = 2    = E[X]`              (`φ * ζ = Id`),
* `L(1) = E    = E[τ(X)]`           (Erdős–Borwein; irrational, kernel),
* `L(A) = S    = E[φ(X)]`           (`A = φ * μ`; OPEN — this IS #249).

This file adds the *two-variable* coordinate.  The finite core is the visible-point
count on the addition antidiagonal:

  `#{(a,b) : a + b = n, 0 < a, gcd(a,b) = 1} = φ(n)`   for EVERY `n : ℕ`

(the half-open filter `0 < a`, `b ≥ 0` makes the identity uniform — no case split,
`φ(0) = 0` and `φ(1) = 1` included).  Summing it against `rⁿ` gives, for `0 ≤ r < 1`:

* half-open bridge:  `∑_{(a,b) coprime, a ≥ 1} r^(a+b) = ∑ φ(n)·rⁿ`
  — at `r = 1/2` the #249 constant IS a coprime-pair mass;
* positive bridge:   `∑_{(a,b) coprime, a,b ≥ 1} r^(a+b) = ∑ φ(n)·rⁿ - r`
  — at `r = 1/2` this is `P(gcd(X,Y) = 1) = S - 1/2` for independent fair-coin
  waiting times `X, Y` (`P(X=a)·P(Y=b) = 2^{-(a+b)}` exactly at the fair coin:
  base 2 is the unique self-normalizing point of the geometric law);
* gcd-layer normalization: `∑_{g≥1} [coprime mass at r^g] = (r/(1-r))²`
  — the unique factorization `(a,b) = g·(a',b')`, `gcd(a',b') = 1`, layer by layer;
  at `r = 1/2` the total is `1`: the gcd of two fair-coin waiting times is finite
  with probability one, and THAT is the probabilistic content of the wave-18
  rational rung `L(φ) = 2`.

The honest boundary: every statement here is an equality of convergent real series
(the probability readings are the doc layer — the tsums ARE the probabilities, no
measure theory is invoked).  Nothing here decides irrationality of `S`; the
coordinate change relocates #249 onto the visible lattice, where the open question
becomes positional: can the visible-pair mass `∑_{(a,b)=1} 2^{-(a+b)}` be forced to
have a non-eventually-periodic binary tail?
-/

namespace GeometricCoprimality

open MersenneLambertLadder

/-! ## The finite core: visible points on the addition antidiagonal -/

/-- **Visible-point count = totient, uniformly in `n`.**  The half-open filter
(`0 < a`, `b` free) makes the identity hypothesis-free: `n = 0` gives the empty
filter (`φ(0) = 0`), `n = 1` gives exactly `(1,0)` (`φ(1) = 1`), and for `n ≥ 2`
the pair `(a, n-a)` is coprime iff `a` is a totient witness of `n`. -/
theorem card_antidiagonal_filter_pos_coprime (n : ℕ) :
    ((Finset.antidiagonal n).filter fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2).card
      = Nat.totient n := by
  rw [Nat.totient_eq_card_coprime]
  refine Finset.card_bij' (fun p _ => p.2) (fun a _ => (n - a, a)) ?_ ?_ ?_ ?_
  · intro p hp
    dsimp only
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    obtain ⟨hsum, hpos, hcop⟩ := hp
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [← hsum]
    exact Nat.coprime_add_self_left.mpr hcop
  · intro a ha
    dsimp only
    rw [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨hlt, hcop⟩ := ha
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    refine ⟨by omega, by omega, ?_⟩
    exact (Nat.coprime_sub_self_left (by omega)).mpr hcop
  · intro p hp
    dsimp only
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    obtain ⟨hsum, hpos, -⟩ := hp
    rw [Prod.ext_iff]
    exact ⟨by omega, rfl⟩
  · intro a _
    rfl

/-! ## Summability of pair-power families -/

theorem summable_pow_add {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun p : ℕ × ℕ => r ^ (p.1 + p.2)) := by
  have hgeo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have h := hgeo.mul_of_nonneg hgeo (fun n => pow_nonneg hr0 n) (fun n => pow_nonneg hr0 n)
  exact h.congr fun p => by rw [← pow_add]

theorem summable_coprime_pair_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun p : ℕ × ℕ =>
      if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (summable_pow_add hr0 hr1)
  · by_cases h : 0 < p.1 ∧ Nat.Coprime p.1 p.2
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  · by_cases h : 0 < p.1 ∧ Nat.Coprime p.1 p.2
    · rw [if_pos h]
    · rw [if_neg h]; positivity

theorem summable_pos_coprime_pair_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun p : ℕ × ℕ =>
      if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (summable_pow_add hr0 hr1)
  · by_cases h : 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  · by_cases h : 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
    · rw [if_pos h]
    · rw [if_neg h]; positivity

/-! ## The half-open bridge: `∑_{(a,b) coprime, a ≥ 1} r^(a+b) = ∑ φ(n)·rⁿ` -/

/-- **Half-open visible-coprime bridge.**  Regrouping the coprime-pair power sum
along addition antidiagonals turns the visible-point count into the totient
coefficient: the #249 power series IS a lattice-point mass. -/
theorem tsum_coprime_pair_pow_eq_tsum_totient_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient n : ℝ) * r ^ n := by
  have hFsum := summable_coprime_pair_pow hr0 hr1
  have hsig : Summable (fun x : (Σ n : ℕ, {y // y ∈ Finset.antidiagonal n}) =>
      if 0 < (x.2 : ℕ × ℕ).1 ∧ Nat.Coprime (x.2 : ℕ × ℕ).1 (x.2 : ℕ × ℕ).2
      then r ^ ((x.2 : ℕ × ℕ).1 + (x.2 : ℕ × ℕ).2) else 0) := by
    have h := (Equiv.summable_iff Finset.sigmaAntidiagonalEquivProd).mpr hFsum
    exact h.congr fun x => rfl
  calc (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = ∑' x : (Σ n : ℕ, {y // y ∈ Finset.antidiagonal n}),
          (if 0 < (x.2 : ℕ × ℕ).1 ∧ Nat.Coprime (x.2 : ℕ × ℕ).1 (x.2 : ℕ × ℕ).2
           then r ^ ((x.2 : ℕ × ℕ).1 + (x.2 : ℕ × ℕ).2) else 0) := by
        rw [← Finset.sigmaAntidiagonalEquivProd.tsum_eq (f := fun p : ℕ × ℕ =>
          if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)]
        exact tsum_congr fun c => rfl
    _ = ∑' n : ℕ, ∑' y : {y // y ∈ Finset.antidiagonal n},
          (if 0 < (y : ℕ × ℕ).1 ∧ Nat.Coprime (y : ℕ × ℕ).1 (y : ℕ × ℕ).2
           then r ^ ((y : ℕ × ℕ).1 + (y : ℕ × ℕ).2) else 0) := Summable.tsum_sigma hsig
    _ = ∑' n : ℕ, (Nat.totient n : ℝ) * r ^ n := by
        refine tsum_congr fun n => ?_
        rw [tsum_fintype, Finset.univ_eq_attach,
          Finset.sum_attach (Finset.antidiagonal n) (fun p : ℕ × ℕ =>
            if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)]
        have hconst : ∀ p ∈ Finset.antidiagonal n,
            (if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
              = (if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ n else 0) := by
          intro p hp
          rw [Finset.mem_antidiagonal] at hp
          rw [hp]
        rw [Finset.sum_congr rfl hconst, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          card_antidiagonal_filter_pos_coprime]

/-! ## The positive bridge: subtracting the boundary pair `(1,0)` -/

private lemma halfopen_split (r : ℝ) (p : ℕ × ℕ) :
    (if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
        + (if p = ((1 : ℕ), (0 : ℕ)) then r else 0) := by
  rcases p with ⟨a, b⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [Prod.ext_iff]
    · by_cases h1 : a = 1
      · subst h1
        simp
      · have hnc : ¬ Nat.Coprime a 0 := by
          rw [Nat.coprime_zero_right]
          exact h1
        simp [hnc, h1, Prod.ext_iff]
  · have hne : ((a, b) : ℕ × ℕ) ≠ ((1 : ℕ), (0 : ℕ)) := by
      intro h
      rw [Prod.ext_iff] at h
      omega
    rw [if_neg hne, add_zero]
    simp [hb]

/-- **Positive visible-coprime bridge**: over strictly positive coprime pairs,
`∑ r^(a+b) = ∑ φ(n)·rⁿ - r`.  At `r = 1/2` the left side is the probability that
two independent fair-coin waiting times are coprime, and the boundary term `r`
that separates it from the #249 constant is `P(X = 1) = L(μ)` — the ladder's
Möbius rung. -/
theorem tsum_pos_coprime_pair_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) * r ^ n) - r := by
  have hpos := summable_pos_coprime_pair_pow hr0 hr1
  have hedge : Summable (fun p : ℕ × ℕ => if p = ((1 : ℕ), (0 : ℕ)) then r else 0) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (summable_pow_add hr0 hr1)
    · by_cases h : p = ((1 : ℕ), (0 : ℕ))
      · rw [if_pos h]; exact hr0
      · rw [if_neg h]
    · by_cases h : p = ((1 : ℕ), (0 : ℕ))
      · subst h
        simp
      · rw [if_neg h]
        positivity
  have hhalf := tsum_coprime_pair_pow_eq_tsum_totient_mul_pow hr0 hr1
  have hsplit : (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
        + ∑' p : ℕ × ℕ, (if p = ((1 : ℕ), (0 : ℕ)) then r else 0) := by
    rw [← hpos.tsum_add hedge]
    exact tsum_congr fun p => halfopen_split r p
  have hedge_val : (∑' p : ℕ × ℕ, if p = ((1 : ℕ), (0 : ℕ)) then r else 0) = r := by
    rw [tsum_eq_single ((1 : ℕ), (0 : ℕ)) (fun b hb => if_neg hb)]
    exact if_pos rfl
  rw [hhalf, hedge_val] at hsplit
  linarith

/-! ## The tail form `∑ φ(n)·xⁿ - x = ∑ φ(n+2)·x^(n+2)` -/

theorem summable_totient_mul_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun n : ℕ => (Nat.totient n : ℝ) * x ^ n) := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  have hpm : Summable (fun m : ℕ => (m : ℝ) * x ^ m) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    exact h.congr fun m => by rw [pow_one]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hpm
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le n) (pow_nonneg hx0 n)

private lemma tsum_totient_mul_pow_sub_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∑' n : ℕ, (Nat.totient n : ℝ) * x ^ n) - x
      = ∑' n : ℕ, (Nat.totient (n + 2) : ℝ) * x ^ (n + 2) := by
  have hsum := summable_totient_mul_pow hx0 hx1
  have hsum1 : Summable (fun n : ℕ => (Nat.totient (n + 1) : ℝ) * x ^ (n + 1)) :=
    (hsum.comp_injective (add_left_injective 1)).congr fun n => rfl
  rw [hsum.tsum_eq_zero_add, hsum1.tsum_eq_zero_add]
  simp only [Nat.totient_zero, Nat.totient_one, Nat.cast_zero, Nat.cast_one, pow_zero,
    zero_mul, one_mul, pow_one, zero_add]
  ring

/-! ## The gcd-layer decomposition -/

private lemma tsum_pow_succ_geometric {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' g : ℕ, x ^ (g + 1) = x / (1 - x) := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one hnorm, ← tsum_mul_left]
  exact tsum_congr fun g => pow_succ' x g

/-- `∑_{n≥1} n·rⁿ = r/(1-r)²` — the generic-`r` value of the totient Lambert
series (wave-18 `tsum_totient_lambert` lands here through `φ * ζ = Id`). -/
theorem tsum_pnat_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ+, ((n : ℕ) : ℝ) * r ^ (n : ℕ) = r / (1 - r) ^ 2 := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hsum : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    exact h.congr fun j => by rw [pow_one]
  calc ∑' n : ℕ+, ((n : ℕ) : ℝ) * r ^ (n : ℕ)
      = ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * r ^ (j + 1) :=
        tsum_pnat_eq_tsum_succ (f := fun j : ℕ => (j : ℝ) * r ^ j)
    _ = ∑' j : ℕ, (j : ℝ) * r ^ j := by
        rw [hsum.tsum_eq_zero_add]
        push_cast
        simp
    _ = r / (1 - r) ^ 2 := tsum_coe_mul_geometric_of_norm_lt_one hnorm

private lemma summable_totient_lambert_shift {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun j : ℕ => (Nat.totient (j + 1) : ℝ) * (r ^ (j + 1) / (1 - r ^ (j + 1)))) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hpm : Summable (fun m : ℕ => (m : ℝ) * r ^ m) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    exact h.congr fun m => by rw [pow_one]
  have hshift : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * r ^ (j + 1)) :=
    (hpm.comp_injective (add_left_injective 1)).congr fun j => rfl
  have hmaj : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ) * r ^ (j + 1)) * (1 - r)⁻¹) :=
    hshift.mul_right _
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hmaj
  · have hx1 : r ^ (j + 1) < 1 := pow_lt_one₀ hr0 hr1 (Nat.succ_ne_zero j)
    have hden : (0 : ℝ) < 1 - r ^ (j + 1) := by linarith
    positivity
  · have hx0 : (0 : ℝ) ≤ r ^ (j + 1) := pow_nonneg hr0 _
    have hx1 : r ^ (j + 1) < 1 := pow_lt_one₀ hr0 hr1 (Nat.succ_ne_zero j)
    have hden : (0 : ℝ) < 1 - r ^ (j + 1) := by linarith
    have hple : r ^ (j + 1) ≤ r := by
      calc r ^ (j + 1) ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1.le (by omega)
        _ = r := pow_one r
    have hfrac : r ^ (j + 1) / (1 - r ^ (j + 1)) ≤ r ^ (j + 1) / (1 - r) := by
      rw [div_le_div_iff₀ hden h1r]
      have hmul := mul_le_mul_of_nonneg_left
        (by linarith : (1 : ℝ) - r ≤ 1 - r ^ (j + 1)) hx0
      linarith
    have htot : (Nat.totient (j + 1) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.totient_le (j + 1)
    calc (Nat.totient (j + 1) : ℝ) * (r ^ (j + 1) / (1 - r ^ (j + 1)))
        ≤ ((j + 1 : ℕ) : ℝ) * (r ^ (j + 1) / (1 - r)) := by
          apply mul_le_mul htot hfrac (by positivity) (by positivity)
      _ = (((j + 1 : ℕ) : ℝ) * r ^ (j + 1)) * (1 - r)⁻¹ := by
          rw [div_eq_mul_inv]
          ring

/-- **Tail Lambert evaluation**: `∑_{n≥2} φ(n)·rⁿ/(1-rⁿ) = r/(1-r)² - r/(1-r)`.
This is the wave-18 rung `L(φ)` with its `d = 1` term peeled off — the analytic
identity behind the gcd-layer normalization. -/
theorem tsum_totient_lambert_tail {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ, (Nat.totient (n + 2) : ℝ) * (r ^ (n + 2) / (1 - r ^ (n + 2)))
      = r / (1 - r) ^ 2 - r / (1 - r) := by
  have hsummand := summable_totient_lambert_shift hr0 hr1
  have hL := MersenneLambertLadder.tsum_totient_lambert hr0 hr1
  have hval := tsum_pnat_mul_geometric hr0 hr1
  have hLchain : ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ)
      * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) = r / (1 - r) ^ 2 := by
    rw [hL]
    exact hval
  rw [tsum_pnat_eq_tsum_succ
    (f := fun j : ℕ => (Nat.totient j : ℝ) * (r ^ j / (1 - r ^ j)))] at hLchain
  have hpeel : ∑' j : ℕ, (Nat.totient (j + 1) : ℝ) * (r ^ (j + 1) / (1 - r ^ (j + 1)))
      = (Nat.totient 1 : ℝ) * (r ^ 1 / (1 - r ^ 1))
        + ∑' j : ℕ, (Nat.totient (j + 2) : ℝ) * (r ^ (j + 2) / (1 - r ^ (j + 2))) :=
    hsummand.tsum_eq_zero_add
  rw [hpeel] at hLchain
  have hphi1 : (Nat.totient 1 : ℝ) * (r ^ 1 / (1 - r ^ 1)) = r / (1 - r) := by
    simp
  rw [hphi1] at hLchain
  linarith

/-- **The gcd-layer decomposition, generic `0 ≤ r < 1`.**  Every positive pair
`(a,b)` factors uniquely as `g·(a',b')` with `gcd(a',b') = 1`, so summing the
positive coprime-pair mass at every scale `r, r², r³, …` recovers the full
positive-quadrant mass `(∑_{a≥1} rᵃ)² = (r/(1-r))²`.  Layer `g` is the mass of
`{gcd = g}`; the `g = 1` layer at `r = 1/2` is the open #249 value `S - 1/2`. -/
theorem tsum_gcd_layer_pos_coprime_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = (r / (1 - r)) ^ 2 := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hlayer : ∀ g : ℕ,
      (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then (r ^ (g + 1)) ^ (p.1 + p.2) else 0)
        = ∑' n : ℕ, (Nat.totient (n + 2) : ℝ) * (r ^ (g + 1)) ^ (n + 2) := by
    intro g
    have hx0 : (0 : ℝ) ≤ r ^ (g + 1) := pow_nonneg hr0 _
    have hx1 : r ^ (g + 1) < 1 := pow_lt_one₀ hr0 hr1 (Nat.succ_ne_zero g)
    rw [tsum_pos_coprime_pair_pow hx0 hx1, tsum_totient_mul_pow_sub_self hx0 hx1]
  rw [tsum_congr hlayer]
  have hF : Summable (fun q : ℕ × ℕ =>
      (Nat.totient (q.2 + 2) : ℝ) * (r ^ (q.1 + 1)) ^ (q.2 + 2)) := by
    have hnorm : ‖r‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
    have hgeo : Summable (fun g : ℕ => r ^ g) := summable_geometric_of_lt_one hr0 hr1
    have hpm : Summable (fun m : ℕ => (m : ℝ) * r ^ m) := by
      have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
      exact h.congr fun m => by rw [pow_one]
    have hshift : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * r ^ (n + 2)) :=
      (hpm.comp_injective (add_left_injective 2)).congr fun n => rfl
    have hmaj : Summable (fun q : ℕ × ℕ =>
        r ^ q.1 * (((q.2 + 2 : ℕ) : ℝ) * r ^ (q.2 + 2))) :=
      hgeo.mul_of_nonneg hshift (fun g => pow_nonneg hr0 g) (fun n => by positivity)
    refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_) hmaj
    rcases q with ⟨g, n⟩
    have hle : g + (n + 2) ≤ (g + 1) * (n + 2) := by nlinarith
    have hexp : (r ^ (g + 1)) ^ (n + 2) ≤ r ^ g * r ^ (n + 2) := by
      rw [← pow_mul, ← pow_add]
      exact pow_le_pow_of_le_one hr0 hr1.le hle
    have htot : (Nat.totient (n + 2) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.totient_le (n + 2)
    calc (Nat.totient (n + 2) : ℝ) * (r ^ (g + 1)) ^ (n + 2)
        ≤ ((n + 2 : ℕ) : ℝ) * (r ^ g * r ^ (n + 2)) := by
          apply mul_le_mul htot hexp (by positivity) (by positivity)
      _ = r ^ g * (((n + 2 : ℕ) : ℝ) * r ^ (n + 2)) := by ring
  have hswap : ∑' g : ℕ, ∑' n : ℕ, (Nat.totient (n + 2) : ℝ) * (r ^ (g + 1)) ^ (n + 2)
      = ∑' n : ℕ, ∑' g : ℕ, (Nat.totient (n + 2) : ℝ) * (r ^ (g + 1)) ^ (n + 2) := by
    have hF' : Summable (fun q : ℕ × ℕ =>
        (Nat.totient (q.1 + 2) : ℝ) * (r ^ (q.2 + 1)) ^ (q.1 + 2)) := by
      have h := hF.prod_symm
      exact h.congr fun q => rfl
    calc ∑' g : ℕ, ∑' n : ℕ, (Nat.totient (n + 2) : ℝ) * (r ^ (g + 1)) ^ (n + 2)
        = ∑' q : ℕ × ℕ, (Nat.totient (q.2 + 2) : ℝ) * (r ^ (q.1 + 1)) ^ (q.2 + 2) :=
          (hF.tsum_prod).symm
      _ = ∑' q : ℕ × ℕ, (Nat.totient (q.1 + 2) : ℝ) * (r ^ (q.2 + 1)) ^ (q.1 + 2) :=
          ((Equiv.prodComm ℕ ℕ).tsum_eq (f := fun q : ℕ × ℕ =>
            (Nat.totient (q.1 + 2) : ℝ) * (r ^ (q.2 + 1)) ^ (q.1 + 2)))
      _ = ∑' n : ℕ, ∑' g : ℕ, (Nat.totient (n + 2) : ℝ) * (r ^ (g + 1)) ^ (n + 2) :=
          hF'.tsum_prod
  rw [hswap]
  have hinner : ∀ n : ℕ,
      ∑' g : ℕ, (Nat.totient (n + 2) : ℝ) * (r ^ (g + 1)) ^ (n + 2)
        = (Nat.totient (n + 2) : ℝ) * (r ^ (n + 2) / (1 - r ^ (n + 2))) := by
    intro n
    have hx0 : (0 : ℝ) ≤ r ^ (n + 2) := pow_nonneg hr0 _
    have hx1 : r ^ (n + 2) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
    calc ∑' g : ℕ, (Nat.totient (n + 2) : ℝ) * (r ^ (g + 1)) ^ (n + 2)
        = ∑' g : ℕ, (Nat.totient (n + 2) : ℝ) * (r ^ (n + 2)) ^ (g + 1) := by
          refine tsum_congr fun g => ?_
          congr 1
          rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ = (Nat.totient (n + 2) : ℝ) * ∑' g : ℕ, (r ^ (n + 2)) ^ (g + 1) := tsum_mul_left
      _ = (Nat.totient (n + 2) : ℝ) * (r ^ (n + 2) / (1 - r ^ (n + 2))) := by
          rw [tsum_pow_succ_geometric hx0 hx1]
  rw [tsum_congr hinner, tsum_totient_lambert_tail hr0 hr1]
  have h1rne : (1 : ℝ) - r ≠ 0 := ne_of_gt h1r
  field_simp
  ring

/-- **Rational geometric-model falsifier.**  Summing the Lambert kernel over
strictly positive visible lattice points gives the elementary square
`(r / (1-r))^2` for every `0 ≤ r < 1`.  Thus coprime restriction, exact
Stern--Brocot splitting, and geometric cylinder decay alone cannot imply
irrationality at a rational parameter. -/
theorem tsum_pos_coprime_lambert_eq_sq
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ,
      if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
        r ^ (p.1 + p.2) / (1 - r ^ (p.1 + p.2))
      else 0) =
      (r / (1 - r)) ^ 2 := by
  let F : (ℕ × ℕ) → ℕ → ℝ := fun p g =>
    if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
      (r ^ (g + 1)) ^ (p.1 + p.2)
    else 0
  have hgeo : Summable (fun g : ℕ => r ^ g) :=
    summable_geometric_of_lt_one hr0 hr1
  have hpair := summable_pow_add hr0 hr1
  have hmajorant : Summable (fun q : (ℕ × ℕ) × ℕ =>
      r ^ (q.1.1 + q.1.2) * r ^ q.2) :=
    hpair.mul_of_nonneg hgeo
      (fun p => pow_nonneg hr0 _) (fun g => pow_nonneg hr0 _)
  have hF : Summable (Function.uncurry F) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hmajorant
    · rcases q with ⟨⟨a, b⟩, g⟩
      simp only [Function.uncurry_apply_pair]
      dsimp [F]
      split_ifs <;> positivity
    · rcases q with ⟨⟨a, b⟩, g⟩
      simp only [Function.uncurry_apply_pair]
      dsimp [F]
      by_cases h : 0 < a ∧ 0 < b ∧ Nat.Coprime a b
      · rw [if_pos h, ← pow_mul, ← pow_add]
        apply pow_le_pow_of_le_one hr0 hr1.le
        nlinarith [h.1, h.2.1]
      · rw [if_neg h]
        positivity
  have hinner : ∀ p : ℕ × ℕ,
      (∑' g : ℕ, F p g) =
        (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          r ^ (p.1 + p.2) / (1 - r ^ (p.1 + p.2))
        else 0) := by
    intro p
    by_cases hp : 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
    · rw [if_pos hp]
      dsimp [F]
      simp only [if_pos hp]
      calc
        (∑' g : ℕ, (r ^ (g + 1)) ^ (p.1 + p.2)) =
            ∑' g : ℕ, (r ^ (p.1 + p.2)) ^ (g + 1) := by
          apply tsum_congr
          intro g
          rw [← pow_mul, Nat.mul_comm, pow_mul]
        _ = r ^ (p.1 + p.2) / (1 - r ^ (p.1 + p.2)) := by
          apply tsum_pow_succ_geometric
          · positivity
          · exact pow_lt_one₀ hr0 hr1 (by omega)
    · rw [if_neg hp]
      simp [F, hp]
  calc
    (∑' p : ℕ × ℕ,
      if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
        r ^ (p.1 + p.2) / (1 - r ^ (p.1 + p.2))
      else 0) = ∑' p : ℕ × ℕ, ∑' g : ℕ, F p g := by
        apply tsum_congr
        intro p
        exact (hinner p).symm
    _ = ∑' g : ℕ, ∑' p : ℕ × ℕ, F p g :=
      Summable.tsum_comm hF.prod_symm
    _ = (r / (1 - r)) ^ 2 := by
      simpa only [F] using tsum_gcd_layer_pos_coprime_pow hr0 hr1

/-- **The fair-coin gcd law is exactly normalized.**  At `r = 1/2` the layer
masses are genuine probabilities — layer `g` is `P(gcd(X,Y) = g+1)` for
independent fair-coin waiting times — and they sum to `1`: the gcd is finite
almost surely.  Through the visible-coprime bridge this is precisely the
probabilistic content of the wave-18 rational rung `L(φ) = 2`. -/
theorem tsum_gcd_layer_pos_coprime_half_eq_one :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = 1 := by
  rw [tsum_gcd_layer_pos_coprime_pow (by norm_num) (by norm_num)]
  norm_num

-- Axiom audit: every result must rest only on the foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms card_antidiagonal_filter_pos_coprime
#print axioms tsum_coprime_pair_pow_eq_tsum_totient_mul_pow
#print axioms tsum_pos_coprime_pair_pow
#print axioms tsum_gcd_layer_pos_coprime_pow
#print axioms tsum_pos_coprime_lambert_eq_sq
#print axioms tsum_gcd_layer_pos_coprime_half_eq_one

end GeometricCoprimality
