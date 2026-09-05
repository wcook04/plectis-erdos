import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős #243: the negative orbit is a centred Euclidean remainder system

`OrientedFeedbackRoot` classifies the fake square roots and makes the reduced
step deterministic; `HorizonEscapeOfMass` kills bounded seeds;
`RepairEntropy` supplies the upper budget `K^L·M_I^2 < (K+1)^L`.  What the
remaining branch — an infinite, genuinely aperiodic orbit with cofinally
unbounded negative centred states — has lacked is a *closed form* for the
negative-to-negative step.

This module supplies two source-independent laws.

## 1. The step is an exact Euclidean division

Write a dynamically reduced step with primitive pair `(u, v)`, multiplier `a`,
cancellation `h`, and successor `(u', v')`, both centred states negative:

```
  v = (a-1)u - m,   v' = (a'-1)u' - m',   h·u' = a·u - v,   h·v' = a·v.
```

Then `negativeFeedback_squareDivision` gives the exact identity

```
  a²·m = (a² - a + 1 - a')·(u + m) + h·m'
```

and, after extracting the square cancellation `a² = h·A`,
`negativeFeedback_centeredQuotient` turns it into a literal quotient–remainder
equation

```
  A·m = k·u' + m',        k = a² - a + 1 - a'.
```

Under the strict centring condition `0 < m' < u'/2` this *is* the Euclidean
division of `A·m` by `u'` (`centeredQuotient_window`), so the negative orbit is
an iterated centred remainder system whose multiplier is the cancellation-free
part of `a²`.  The square determinants and square cancellation payments are the
continuant data of that system, not incidental.

## 2. The cumulative LCM has no scale gaps

`current_scale_anti_shadowing` objects that complete old multipliers may be far
larger than the recovery scale.  That is true of the multipliers; it is false
of their cumulative product.  `exists_divisor_between` shows that a
multiplicative chain `L_{n+1} = L_n·d_n` with `1 ≤ d_n ≤ L_n + 1` — which is
exactly what a cumulative LCM against a strictly centred state satisfies,
since `Λ ≥ a - 1` forces `lcm(Λ,a)/Λ = a/gcd(Λ,a) ≤ a ≤ Λ + 1` — contains a
divisor within a **fixed** factor `max(2, L_0)` of *every* requested real scale
in `[1, L_n]`.

So the remaining obstruction is not a shortage of current-scale old divisors.
It is the sharper problem of making a scale-matched divisor also satisfy the
required residue condition while surviving previous deletions.

## Claim ceiling

**Erdős #243 remains open.**  Nothing here proves the unrestricted conclusion
or the exponential overlap-debt lower bound `2^n ≤ M_n^K`.  The exact
statements above change the target from "produce current-scale old factors" to
"produce residue-compatible, scale-matched survivors, or charge their deletion
to overlap debt".
-/

namespace ErdosProblems.Erdos243

/-! ## The centred Euclidean feedback law -/

/-- **The square-division identity.**  A negative-to-negative reduced feedback
step satisfies an exact identity in which the cancellation `h` appears only as
the coefficient of the successor magnitude. -/
theorem negativeFeedback_squareDivision
    {a aNext h u uNext m mNext : ℤ}
    (huNext : h * uNext = u + m)
    (hvNext :
      h * ((aNext - 1) * uNext - mNext) = a * ((a - 1) * u - m)) :
    a ^ 2 * m = (a ^ 2 - a + 1 - aNext) * (u + m) + h * mNext := by
  linear_combination hvNext - (aNext - 1) * huNext

/-- **The Euclidean form.**  After extracting the exact square cancellation
`a² = h·A`, the next negative magnitude is a literal remainder:
`A·m = k·u' + m'` with `k = a² - a + 1 - a'`. -/
theorem negativeFeedback_centeredQuotient
    {a aNext h A u uNext m mNext k : ℤ}
    (hh : h ≠ 0)
    (hA : a ^ 2 = h * A)
    (hk : k = a ^ 2 - a + 1 - aNext)
    (huNext : h * uNext = u + m)
    (hvNext :
      h * ((aNext - 1) * uNext - mNext) = a * ((a - 1) * u - m)) :
    A * m = k * uNext + mNext := by
  refine mul_left_cancel₀ hh ?_
  calc
    h * (A * m) = a ^ 2 * m := by rw [← mul_assoc, ← hA]
    _ = (a ^ 2 - a + 1 - aNext) * (u + m) + h * mNext :=
        negativeFeedback_squareDivision huNext hvNext
    _ = h * (k * uNext + mNext) := by rw [hk, ← huNext]; ring

/-- **Half-window localisation.**  Strict centring places the Euclidean
remainder in the positive half of the residue window, so the quotient is
pinned by a two-sided inequality. -/
theorem centeredQuotient_window
    {A k u m r : ℤ}
    (hu : 0 < u) (hr : 0 < r) (hhalf : 2 * r < u)
    (hdiv : A * m = k * u + r) :
    2 * k * u < 2 * A * m ∧ 2 * A * m < (2 * k + 1) * u := by
  constructor <;> nlinarith

/-- A lower bound on the scaled magnitude becomes a lower bound on the integer
quotient. -/
theorem centeredQuotient_ge
    {A k u m r B : ℤ}
    (hu : 0 < u) (hr : 0 < r) (hhalf : 2 * r < u)
    (hdiv : A * m = k * u + r)
    (hlarge : (2 * B - 1) * u ≤ 2 * A * m) :
    B ≤ k := by
  have hw := centeredQuotient_window hu hr hhalf hdiv
  nlinarith [hw.1, hw.2]

/-- **Normalized negative mass need not descend.**  The primitive centred
feedback step `(u,v)=(6,11) -> (7,33)` has increasing multipliers `3 < 6`
and negative magnitudes `1 -> 2`, yet its normalized magnitude increases:
`1/6 < 2/7`.  Thus neither absolute nor normalized one-step descent can
exclude the remaining aperiodic negative branch. -/
theorem negativeFeedback_normalizedDescent_counterexample :
    Nat.Coprime 6 11 ∧ Nat.Coprime 7 33 ∧
      11 = (3 - 1) * 6 - 1 ∧
      1 * 7 = 6 + 1 ∧
      1 * 33 = 3 * 11 ∧
      33 = (6 - 1) * 7 - 2 ∧
      2 * 1 < 6 ∧ 2 * 2 < 7 ∧
      3 < 6 ∧ 1 ≤ 2 ∧ 1 * 7 < 2 * 6 := by
  norm_num [Nat.Coprime]

/-! ## The fixed-factor divisor net -/

/-- **No scale gaps in a multiplicative chain.**  If `L` grows by factors
`d_n` with `1 ≤ d_n ≤ L n + 1`, then for every real scale `x ∈ [1, L n]` there
is a divisor of `L n` within the *fixed* factor `Q = max(2, L 0)` of `x`.

This is the statement that removes the `current_scale_anti_shadowing`
objection: the cumulative bank always contains a divisor at every physical
scale, uniformly in `n`. -/
theorem exists_divisor_between {L : ℕ → ℕ} {Q : ℕ}
    (hQ : 2 ≤ Q) (hQ0 : L 0 ≤ Q) (hL0 : 1 ≤ L 0)
    (hstep : ∀ n, ∃ d : ℕ, 1 ≤ d ∧ d ≤ L n + 1 ∧ L (n + 1) = L n * d) :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ x → x ≤ (L n : ℝ) →
      ∃ s : ℕ, s ∣ L n ∧ x ≤ (s : ℝ) ∧ (s : ℝ) ≤ (Q : ℝ) * x := by
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  intro n
  induction n with
  | zero =>
      intro x hx1 hxL
      refine ⟨L 0, dvd_rfl, hxL, ?_⟩
      have h1 : ((L 0 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ0
      nlinarith
  | succ n ih =>
      obtain ⟨d, hd1, hdle, hLd⟩ := hstep n
      have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
      intro x hx1 hxL
      by_cases hxn : x ≤ (L n : ℝ)
      · obtain ⟨s, hsdvd, hsx, hsQ⟩ := ih x hx1 hxn
        exact ⟨s, hLd ▸ hsdvd.mul_right d, hsx, hsQ⟩
      · push_neg at hxn
        by_cases hxd : x < (d : ℝ)
        · refine ⟨d, hLd ▸ Dvd.intro_left (L n) rfl, le_of_lt hxd, ?_⟩
          have hdleR : (d : ℝ) ≤ (L n : ℝ) + 1 := by exact_mod_cast hdle
          nlinarith
        · push_neg at hxd
          have hyle : x / (d : ℝ) ≤ (L n : ℝ) := by
            rw [div_le_iff₀ hdpos]
            rw [hLd] at hxL
            push_cast at hxL
            linarith
          have hy1 : (1 : ℝ) ≤ x / (d : ℝ) := by
            rw [le_div_iff₀ hdpos]
            linarith
          obtain ⟨s, hsdvd, hsx, hsQ⟩ := ih (x / (d : ℝ)) hy1 hyle
          refine ⟨d * s, ?_, ?_, ?_⟩
          · rw [hLd, mul_comm (L n) d]
            exact mul_dvd_mul_left d hsdvd
          · push_cast
            rw [← div_le_iff₀' hdpos]
            exact hsx
          · push_cast
            have : (d : ℝ) * (s : ℝ) ≤ (d : ℝ) * ((Q : ℝ) * (x / (d : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hsQ (le_of_lt hdpos)
            calc (d : ℝ) * (s : ℝ)
                ≤ (d : ℝ) * ((Q : ℝ) * (x / (d : ℝ))) := this
              _ = (Q : ℝ) * x := by field_simp

/-- The cumulative-LCM step bound: against a strictly centred state the growth
factor of `lcm(Λ, a)` over `Λ` never exceeds `Λ + 1`, so `exists_divisor_between`
applies to every cumulative digit LCM. -/
theorem lcm_step_le_succ {Λ a : ℕ} (hΛ : 1 ≤ Λ) (ha : 1 ≤ a) (hle : a ≤ Λ + 1) :
    Nat.lcm Λ a / Λ ≤ Λ + 1 := by
  have hlcm : Nat.lcm Λ a ≤ Λ * a :=
    Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.lcm_dvd_mul Λ a)
  calc Nat.lcm Λ a / Λ ≤ (Λ * a) / Λ := Nat.div_le_div_right hlcm
    _ = a := by rw [Nat.mul_div_cancel_left a (by omega : 0 < Λ)]
    _ ≤ Λ + 1 := hle

end ErdosProblems.Erdos243
