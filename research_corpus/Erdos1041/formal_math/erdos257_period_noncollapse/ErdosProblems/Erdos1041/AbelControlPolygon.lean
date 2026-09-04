import Mathlib.Tactic

/-!
# Erdős #1041: the Abel control polygon and the all-degree monic trinomial family

**Claim boundary.**  Erdős #1041 (Erdős–Herzog–Piranian) asks whether, for every
monic polynomial whose zeros lie in the open unit disc, some two zeros can be
joined by a curve of length `< 2` inside `{|f| < 1}`.  **That problem remains
open, and nothing in this file proves it.**  What is proved here is a *solved
family* — the complete Schur-stable monic trinomial face `z^n + a z^m + b`, in
every degree and for every intermediate exponent — together with the general
Abel machinery that produces it and an explicit sextic showing where the radial
mechanism stops.

The file has four parts.

* **§1 The Abel control polygon.**  For a coefficient function `c : ℕ → ℂ` with
  degree bound `n` and a zero `ζ`, the evaluated coefficient truncations
  `S j = ∑_{k ≤ j} c k ζ^k` are control points of a Bézier-type representation
  of the whole radial segment:
  `∑_{j < n} (t^j - t^(j+1)) S j = p (t ζ)`.
  The weights are nonnegative on `[0,1]` and sum to `1 - t^n`.
* **§2 The finite radial containment certificate.**  If every control point has
  norm at most `R`, then `‖p (t ζ)‖ ≤ R (1 - t^n)` for `0 ≤ t ≤ 1`.  A continuum
  maximum over a segment has been replaced by finitely many algebraic numbers.
* **§3 The all-degree monic trinomial theorem.**  For `f z = z^n + a z^m + b`
  with `1 ≤ m < n` and every zero in the open unit disc, every radial segment
  from `0` to a zero lies in `{|f| < 1}`; two distinct zeros are therefore joined
  through the origin by a broken line of length `‖ζ₁‖ + ‖ζ₂‖ < 2`.  The
  hypothesis `‖b‖ < 1` is **derived**, not assumed: `norm_const_lt_one_of_roots_lt_one`
  obtains it from Vieta's product formula applied to `X^n + C a * X^m + C b`.
  The coefficient `a` is completely unrestricted.
* **§4 Pivot cancellation for a general polynomial.**  Eliminating one chosen
  coefficient `a m` at a zero leaves an identity in which that coefficient does
  not appear, and a scalar condition `N_m(t) ≤ t^n + δ (1 - t^m)` on the
  remaining modes (with `δ = 1 - ‖a 0‖`) certifies the whole radial segment.
  This is the anisotropic neighbourhood of the trinomial face.
* **§5 The sextic guardrail.**  For `f_r z = z^6 + (1/5) r^2 z^4 - (1/5) r^4 z^2 - r^6`
  every zero has modulus exactly `r`, yet `f_r (r/2) = -(327/320) r^6`, so the
  radial spoke to the zero `r` leaves `{|f| < 1}` as soon as `r^6 > 320/327`.
  Two active intermediate modes suffice to break the radial mechanism, which is
  exactly why §3 stops at trinomials.  The sextic is *not* a counterexample to
  Erdős #1041: a different pair of its zeros still admits a short path.  Only
  the prescribed radial spoke fails, and only that is claimed here.

Relation to the rest of the corpus.  `CyclicTrinomialFiberCase.lean` already
kernel-checks the three-term cancellation identity and its norm estimate in the
quotient variable, with `‖c‖ < 1` taken as a hypothesis;
`CyclicTetranomialCoefficientCase.lean` does the four-term case;
`TrinomialInterpolationSpoke.lean` records the endpoint-vanishing remainder.
What is new here is the identity at **arbitrary** degree with the partial-sum
control points, the `R (1 - t^n)` certificate, the derivation of `‖b‖ < 1` from
the root hypothesis, the packaged trinomial conclusion, the pivot sufficient
condition, and the sextic guardrail (previously only stated, in
`BarycentricEnvelope.md` §5).
-/

open Polynomial

namespace ErdosProblems.Erdos1041.AbelControlPolygon

open Finset

/-! ## 0. Scalar helpers -/

/-- The norm of a nonnegative real, viewed in `ℂ`. -/
private theorem norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]

/-- The Abel weights `t^j - t^(j+1)` are nonnegative on the unit interval. -/
theorem abelWeight_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j : ℕ) :
    0 ≤ t ^ j - t ^ (j + 1) := by
  have hj : 0 ≤ t ^ j := pow_nonneg ht0 j
  have : t ^ (j + 1) = t ^ j * t := by ring
  nlinarith

/-- The Abel weights telescope to `1 - t^n`. -/
theorem sum_abelWeight (t : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (t ^ j - t ^ (j + 1)) = 1 - t ^ n := by
  simpa using Finset.sum_range_sub' (fun j => t ^ j) n

/-! ## 1. The Abel control polygon -/

/-- The `j`-th **Abel control point** of the coefficient function `c` at `ζ`:
the evaluated coefficient truncation `S j = ∑_{k ≤ j} c k ζ^k`.  These are the
control points of the Bézier-type representation in `abel_controlPolygon`;
unlike a Taylor representation they are *not* derivatives. -/
noncomputable def controlPoint (c : ℕ → ℂ) (ζ : ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (j + 1), c k * ζ ^ k

/-- Evaluation of the coefficient function `c` as a polynomial of degree at
most `n`. -/
noncomputable def evalCoeff (c : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), c k * z ^ k

/-- Abel summation, before the root relation is used: the weighted sum of the
control points telescopes into the truncated radial evaluation minus `t^n`
times the truncated value at `ζ`. -/
theorem sum_abelWeight_mul_controlPoint (c : ℕ → ℂ) (ζ t : ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (t ^ j - t ^ (j + 1)) * controlPoint c ζ j
      = (∑ k ∈ Finset.range n, c k * ζ ^ k * t ^ k)
        - t ^ n * ∑ k ∈ Finset.range n, c k * ζ ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hc : controlPoint c ζ n
          = (∑ k ∈ Finset.range n, c k * ζ ^ k) + c n * ζ ^ n := by
        simp [controlPoint, Finset.sum_range_succ]
      rw [Finset.sum_range_succ
            (fun j => (t ^ j - t ^ (j + 1)) * controlPoint c ζ j) n, ih, hc,
        Finset.sum_range_succ (fun k => c k * ζ ^ k * t ^ k) n,
        Finset.sum_range_succ (fun k => c k * ζ ^ k) n]
      ring

/-- **The Abel control-polygon identity.**  If `ζ` is a zero of the polynomial
with coefficients `c` and degree bound `n`, then the value at every point `t ζ`
of the radial segment is the weighted sum of the `n` control points
`S 0, …, S (n-1)`, with weights `t^j - t^(j+1)`.

Combined with `abelWeight_nonneg` and `sum_abelWeight`, this exhibits
`p (t ζ) / (1 - t^n)` as a convex combination of the control points for
`0 ≤ t < 1`. -/
theorem abel_controlPolygon (c : ℕ → ℂ) (ζ t : ℂ) {n : ℕ}
    (hroot : evalCoeff c n ζ = 0) :
    ∑ j ∈ Finset.range n, (t ^ j - t ^ (j + 1)) * controlPoint c ζ j
      = evalCoeff c n (t * ζ) := by
  have hsplit : evalCoeff c n ζ
      = (∑ k ∈ Finset.range n, c k * ζ ^ k) + c n * ζ ^ n := by
    simp [evalCoeff, Finset.sum_range_succ]
  have htail : (∑ k ∈ Finset.range n, c k * ζ ^ k) = -(c n * ζ ^ n) := by
    rw [hsplit] at hroot
    linear_combination hroot
  have heval : evalCoeff c n (t * ζ)
      = (∑ k ∈ Finset.range n, c k * ζ ^ k * t ^ k) + c n * ζ ^ n * t ^ n := by
    rw [evalCoeff, Finset.sum_range_succ]
    congr 1
    · exact Finset.sum_congr rfl (fun k _ => by rw [mul_pow]; ring)
    · rw [mul_pow]; ring
  rw [sum_abelWeight_mul_controlPoint, htail, heval]
  ring

/-! ## 2. The finite radial containment certificate -/

/-- **Finite radial containment certificate.**  If every Abel control point of a
zero `ζ` has norm at most `R`, then the whole radial segment obeys
`‖p (t ζ)‖ ≤ R (1 - t^n)`.

This replaces a continuum maximum over the segment `[0, ζ]` by a bound on `n`
algebraic quantities.  In particular `R ≤ 1` and `n ≥ 1` force the closed
segment into the closed unit sublevel set. -/
theorem norm_evalCoeff_radial_le {c : ℕ → ℂ} {ζ : ℂ} {n : ℕ} {R t : ℝ}
    (hroot : evalCoeff c n ζ = 0)
    (hR : ∀ j < n, ‖controlPoint c ζ j‖ ≤ R)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖evalCoeff c n ((t : ℂ) * ζ)‖ ≤ R * (1 - t ^ n) := by
  rw [← abel_controlPolygon c ζ (t : ℂ) hroot]
  have hwt : ∀ j : ℕ,
      ((t : ℂ) ^ j - (t : ℂ) ^ (j + 1)) = ((t ^ j - t ^ (j + 1) : ℝ) : ℂ) := by
    intro j; push_cast; ring
  calc ‖∑ j ∈ Finset.range n,
          ((t : ℂ) ^ j - (t : ℂ) ^ (j + 1)) * controlPoint c ζ j‖
      ≤ ∑ j ∈ Finset.range n,
          ‖((t : ℂ) ^ j - (t : ℂ) ^ (j + 1)) * controlPoint c ζ j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n, (t ^ j - t ^ (j + 1)) * R := by
        refine Finset.sum_le_sum ?_
        intro j hj
        rw [norm_mul, hwt j, norm_ofReal_of_nonneg (abelWeight_nonneg ht0 ht1 j)]
        exact mul_le_mul_of_nonneg_left (hR j (Finset.mem_range.mp hj))
          (abelWeight_nonneg ht0 ht1 j)
    _ = R * (1 - t ^ n) := by
        rw [← Finset.sum_mul, sum_abelWeight]; ring

/-! ## 3. The all-degree monic trinomial theorem -/

/-- **Direct cancellation at a zero of a monic trinomial.**  Eliminating
`a ζ^m = -b - ζ^n` from the radial evaluation removes the middle coefficient
entirely:
`f (t ζ) = b (1 - t^m) + ζ^n (t^n - t^m)`. -/
theorem trinomial_radial_eval (n m : ℕ) (a b ζ t : ℂ)
    (hroot : ζ ^ n + a * ζ ^ m + b = 0) :
    (t * ζ) ^ n + a * (t * ζ) ^ m + b
      = b * (1 - t ^ m) + ζ ^ n * (t ^ n - t ^ m) := by
  rw [mul_pow, mul_pow]
  linear_combination t ^ m * hroot

/-- The sharp radial estimate for a monic trinomial with `‖b‖ < 1` and a zero
`ζ` in the open unit disc: on the half-open segment `0 ≤ t < 1`,
`‖f (t ζ)‖ < 1 - t^n`.  The middle coefficient `a` never appears. -/
theorem trinomial_norm_radial_lt {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {a b ζ : ℂ} (hb : ‖b‖ < 1) (hζ : ‖ζ‖ < 1)
    (hroot : ζ ^ n + a * ζ ^ m + b = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ‖((t : ℂ) * ζ) ^ n + a * ((t : ℂ) * ζ) ^ m + b‖ < 1 - t ^ n := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have htm1 : t ^ m < 1 := pow_lt_one₀ ht0 ht1 hm0
  have htnm : t ^ n ≤ t ^ m := pow_le_pow_of_le_one ht0 ht1.le hmn.le
  have hzn : ‖ζ‖ ^ n < 1 := pow_lt_one₀ (norm_nonneg ζ) hζ hn0
  have hcast1 : (1 - (t : ℂ) ^ m) = ((1 - t ^ m : ℝ) : ℂ) := by push_cast; ring
  have hcast2 : ((t : ℂ) ^ n - (t : ℂ) ^ m) = ((t ^ n - t ^ m : ℝ) : ℂ) := by
    push_cast; ring
  rw [trinomial_radial_eval n m a b ζ (t : ℂ) hroot]
  have hA : ‖b * (1 - (t : ℂ) ^ m)‖ = ‖b‖ * (1 - t ^ m) := by
    rw [norm_mul, hcast1, norm_ofReal_of_nonneg (by linarith)]
  have hB : ‖ζ ^ n * ((t : ℂ) ^ n - (t : ℂ) ^ m)‖ = ‖ζ‖ ^ n * (t ^ m - t ^ n) := by
    rw [norm_mul, norm_pow, hcast2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  calc ‖b * (1 - (t : ℂ) ^ m) + ζ ^ n * ((t : ℂ) ^ n - (t : ℂ) ^ m)‖
      ≤ ‖b * (1 - (t : ℂ) ^ m)‖ + ‖ζ ^ n * ((t : ℂ) ^ n - (t : ℂ) ^ m)‖ :=
        norm_add_le _ _
    _ = ‖b‖ * (1 - t ^ m) + ‖ζ‖ ^ n * (t ^ m - t ^ n) := by rw [hA, hB]
    _ < 1 - t ^ n := by nlinarith [norm_nonneg b, pow_nonneg (norm_nonneg ζ) n]

/-- The closed radial segment `[0, ζ]` from the origin to a zero of a monic
trinomial with `‖b‖ < 1` and `‖ζ‖ < 1` lies strictly inside `{|f| < 1}`.  At the
far endpoint the value is `0`, since `ζ` is a zero. -/
theorem trinomial_radial_norm_lt_one {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {a b ζ : ℂ} (hb : ‖b‖ < 1) (hζ : ‖ζ‖ < 1)
    (hroot : ζ ^ n + a * ζ ^ m + b = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((t : ℂ) * ζ) ^ n + a * ((t : ℂ) * ζ) ^ m + b‖ < 1 := by
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [h]
    push_cast
    rw [one_mul, hroot]
    simp
  · have hlt := trinomial_norm_radial_lt hm hmn hb hζ hroot ht0 h
    have : (0 : ℝ) ≤ t ^ n := pow_nonneg ht0 n
    linarith

/-! ### The constant term is small, by Vieta -/

/-- A product over a nonempty multiset of complex numbers, all of norm strictly
below one, has norm strictly below one. -/
private theorem multiset_prod_norm_lt_one {s : Multiset ℂ}
    (hlt : ∀ z ∈ s, ‖z‖ < 1) (hne : s ≠ 0) : ‖s.prod‖ < 1 := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl hne
  | cons a s ih =>
      have ha1 : ‖a‖ < 1 := hlt a (Multiset.mem_cons_self a s)
      have hsl : ∀ z ∈ s, ‖z‖ < 1 := fun z hz =>
        hlt z (Multiset.mem_cons.mpr (Or.inr hz))
      rw [Multiset.prod_cons, norm_mul]
      by_cases hs : s = 0
      · subst hs; simpa using ha1
      · have hsp : ‖s.prod‖ < 1 := ih hsl hs
        nlinarith [norm_nonneg a, norm_nonneg s.prod]

/-- **The constant term of a Schur-stable monic trinomial is small.**  If every
zero of `z^n + a z^m + b` lies in the open unit disc (`1 ≤ m < n`), then
`‖b‖ < 1`.

This is Vieta's product formula: `b` is `(-1)^n` times the product of the zeros
of the monic polynomial `X^n + C a * X^m + C b`, so `‖b‖` is the product of `n`
numbers each strictly below one.  Nothing is assumed; the bound is derived. -/
theorem norm_const_lt_one_of_roots_lt_one {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {a b : ℂ} (hroots : ∀ ζ : ℂ, ζ ^ n + a * ζ ^ m + b = 0 → ‖ζ‖ < 1) :
    ‖b‖ < 1 := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  set P : ℂ[X] := X ^ n + (C a * X ^ m + C b) with hP
  -- the tail has degree below `n`
  have h1 : (C a * X ^ m : ℂ[X]).degree ≤ (m : WithBot ℕ) :=
    degree_C_mul_X_pow_le m a
  have h2 : (C b : ℂ[X]).degree ≤ (m : WithBot ℕ) :=
    le_trans degree_C_le (by exact_mod_cast Nat.zero_le m)
  have h3 : (C a * X ^ m + C b : ℂ[X]).degree ≤ (m : WithBot ℕ) :=
    le_trans (degree_add_le _ _) (max_le h1 h2)
  have hlt : (C a * X ^ m + C b : ℂ[X]).degree < (X ^ n : ℂ[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt h3 (by exact_mod_cast hmn)
  have hmonic : P.Monic := (monic_X_pow n).add_of_left hlt
  have hdeg : P.degree = (n : WithBot ℕ) := by
    rw [hP, degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  have hnat : P.natDegree = n := natDegree_eq_of_degree_eq_some hdeg
  have hPne : P ≠ 0 := hmonic.ne_zero
  have hs : P.Splits := IsAlgClosed.splits P
  have hcard : P.roots.card = n := by
    rw [Polynomial.splits_iff_card_roots.mp hs, hnat]
  have heval0 : P.eval 0 = b := by simp [hP, zero_pow hn0, zero_pow hm0]
  -- every root of `P` is a root of the trinomial, hence in the open unit disc
  have hrootnorm : ∀ ζ ∈ P.roots, ‖ζ‖ < 1 := by
    intro ζ hζ
    refine hroots ζ ?_
    have hz : P.eval ζ = 0 := (Polynomial.mem_roots hPne).mp hζ
    rw [hP] at hz
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at hz
    linear_combination hz
  -- Vieta: `b = P.eval 0` is `(-1)^n` times the product of the roots
  have hsplit : P = C P.leadingCoeff * (P.roots.map fun ζ => X - C ζ).prod :=
    hs.eq_prod_roots
  have hP0 : P.eval 0 = ((P.roots.map fun ζ => X - C ζ).prod).eval 0 := by
    have h := congrArg (fun q : ℂ[X] => q.eval 0) hsplit
    simpa [hmonic.leadingCoeff] using h
  have hprodeval :
      ((P.roots.map fun ζ => X - C ζ).prod).eval 0
        = (P.roots.map fun ζ => -ζ).prod := by
    rw [eval_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro ζ _
    simp
  have hbprod : b = (P.roots.map fun ζ => -ζ).prod := by
    rw [← heval0, hP0, hprodeval]
  have hne : (P.roots.map fun ζ => -ζ) ≠ 0 := by
    intro hcon
    have hc : (P.roots.map fun ζ => -ζ).card = 0 := by rw [hcon]; simp
    rw [Multiset.card_map, hcard] at hc
    exact hn0 hc
  rw [hbprod]
  refine multiset_prod_norm_lt_one ?_ hne
  intro x hx
  obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
  rw [norm_neg]
  exact hrootnorm ζ hζ

/-- **The all-degree monic trinomial theorem (Erdős #1041 for a solved family).**
Let `f z = z^n + a z^m + b` with `1 ≤ m < n` and every zero in the open unit
disc.  Then for any two zeros `ζ₁, ζ₂`:

* the whole radial segment from the origin to `ζ₁` lies in `{|f| < 1}`;
* likewise for `ζ₂`;
* the broken line `ζ₁ → 0 → ζ₂` has length `‖ζ₁‖ + ‖ζ₂‖ < 2`.

Taking `ζ₁ ≠ ζ₂` these three facts are exactly the Erdős–Herzog–Piranian
conclusion for `f`.  The coefficient `a` is completely unrestricted beyond the
Schur-stability already contained in the root hypothesis.  The parent problem,
for polynomials with more than two non-leading terms, remains open. -/
theorem trinomial_erdos1041_conclusion {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {a b ζ₁ ζ₂ : ℂ}
    (hroots : ∀ ζ : ℂ, ζ ^ n + a * ζ ^ m + b = 0 → ‖ζ‖ < 1)
    (h₁ : ζ₁ ^ n + a * ζ₁ ^ m + b = 0) (h₂ : ζ₂ ^ n + a * ζ₂ ^ m + b = 0) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖((t : ℂ) * ζ₁) ^ n + a * ((t : ℂ) * ζ₁) ^ m + b‖ < 1) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖((t : ℂ) * ζ₂) ^ n + a * ((t : ℂ) * ζ₂) ^ m + b‖ < 1) ∧
      ‖ζ₁‖ + ‖ζ₂‖ < 2 := by
  have hb : ‖b‖ < 1 := norm_const_lt_one_of_roots_lt_one hm hmn hroots
  have hz₁ : ‖ζ₁‖ < 1 := hroots ζ₁ h₁
  have hz₂ : ‖ζ₂‖ < 1 := hroots ζ₂ h₂
  refine ⟨fun t ht0 ht1 => trinomial_radial_norm_lt_one hm hmn hb hz₁ h₁ ht0 ht1,
    fun t ht0 ht1 => trinomial_radial_norm_lt_one hm hmn hb hz₂ h₂ ht0 ht1, ?_⟩
  linarith

/-! ## 4. Pivot cancellation for a general polynomial -/

/-- **Pivot cancellation.**  For a monic polynomial with constant term `a0`,
leading term `z^n` and intermediate modes indexed by `insert m s`, eliminating
the pivot coefficient `aCoeff m` at a zero `ζ` gives an identity in which the
pivot coefficient does not occur:

`f (t ζ) = a0 (1 - t^m) + ζ^n (t^n - t^m) + ∑_{k ∈ s} a_k ζ^k (t^k - t^m)`.

Every remaining mode carries the factor `t^k - t^m`, which vanishes at `t = 0`
and (for the `k` in play) is controlled on `[0,1]`.  In the intended
application `m ∉ s` and `s ⊆ Ico 1 n`, but the identity needs neither. -/
theorem pivot_radial_eval {n m : ℕ} (s : Finset ℕ) {aCoeff : ℕ → ℂ} {a0 ζ t : ℂ}
    (hroot : ζ ^ n + aCoeff m * ζ ^ m + (∑ k ∈ s, aCoeff k * ζ ^ k) + a0 = 0) :
    (t * ζ) ^ n + aCoeff m * (t * ζ) ^ m
        + (∑ k ∈ s, aCoeff k * (t * ζ) ^ k) + a0
      = a0 * (1 - t ^ m) + ζ ^ n * (t ^ n - t ^ m)
        + ∑ k ∈ s, aCoeff k * ζ ^ k * (t ^ k - t ^ m) := by
  have hsum : (∑ k ∈ s, aCoeff k * (t * ζ) ^ k)
      = (∑ k ∈ s, aCoeff k * ζ ^ k * (t ^ k - t ^ m))
        + t ^ m * ∑ k ∈ s, aCoeff k * ζ ^ k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [mul_pow]; ring)
  rw [hsum, mul_pow, mul_pow]
  linear_combination t ^ m * hroot

/-- **The pivot sufficient condition.**  Write `δ = 1 - ‖a0‖` for the margin in
the constant term and
`N_m(t) = ∑_{k ∈ s} ‖a_k‖ ‖ζ‖^k |t^k - t^m|`
for the total non-pivot mass on the radial segment.  If

`N_m(t) ≤ t^n + δ (1 - t^m)`,

then the radial value obeys `‖f (t ζ)‖ ≤ 1 - (1 - ‖ζ‖^n)(t^m - t^n)`.  The pivot
coefficient `aCoeff m` is unrestricted; only the other modes are budgeted.  This
is the anisotropic neighbourhood of the trinomial face of §3, which is the case
`s = ∅`. -/
theorem pivot_norm_radial_le {n m : ℕ} (hmn : m ≤ n) (s : Finset ℕ)
    {aCoeff : ℕ → ℂ} {a0 ζ : ℂ} {t δ : ℝ}
    (hroot : ζ ^ n + aCoeff m * ζ ^ m + (∑ k ∈ s, aCoeff k * ζ ^ k) + a0 = 0)
    (hδ : ‖a0‖ = 1 - δ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hN : ∑ k ∈ s, ‖aCoeff k‖ * ‖ζ‖ ^ k * |t ^ k - t ^ m|
            ≤ t ^ n + δ * (1 - t ^ m)) :
    ‖((t : ℂ) * ζ) ^ n + aCoeff m * ((t : ℂ) * ζ) ^ m
        + (∑ k ∈ s, aCoeff k * ((t : ℂ) * ζ) ^ k) + a0‖
      ≤ 1 - (1 - ‖ζ‖ ^ n) * (t ^ m - t ^ n) := by
  have htm1 : t ^ m ≤ 1 := pow_le_one₀ ht0 ht1
  have htnm : t ^ n ≤ t ^ m := pow_le_pow_of_le_one ht0 ht1 hmn
  have hcast1 : (1 - (t : ℂ) ^ m) = ((1 - t ^ m : ℝ) : ℂ) := by push_cast; ring
  have hcast2 : ((t : ℂ) ^ n - (t : ℂ) ^ m) = ((t ^ n - t ^ m : ℝ) : ℂ) := by
    push_cast; ring
  rw [pivot_radial_eval s hroot]
  have hA : ‖a0 * (1 - (t : ℂ) ^ m)‖ = (1 - δ) * (1 - t ^ m) := by
    rw [norm_mul, hcast1, norm_ofReal_of_nonneg (by linarith), hδ]
  have hB : ‖ζ ^ n * ((t : ℂ) ^ n - (t : ℂ) ^ m)‖ = ‖ζ‖ ^ n * (t ^ m - t ^ n) := by
    rw [norm_mul, norm_pow, hcast2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have hC : ‖∑ k ∈ s, aCoeff k * ζ ^ k * ((t : ℂ) ^ k - (t : ℂ) ^ m)‖
      ≤ ∑ k ∈ s, ‖aCoeff k‖ * ‖ζ‖ ^ k * |t ^ k - t ^ m| := by
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hck : ((t : ℂ) ^ k - (t : ℂ) ^ m) = ((t ^ k - t ^ m : ℝ) : ℂ) := by
      push_cast; ring
    rw [norm_mul, norm_mul, norm_pow, hck, Complex.norm_real, Real.norm_eq_abs]
  calc ‖a0 * (1 - (t : ℂ) ^ m) + ζ ^ n * ((t : ℂ) ^ n - (t : ℂ) ^ m)
          + ∑ k ∈ s, aCoeff k * ζ ^ k * ((t : ℂ) ^ k - (t : ℂ) ^ m)‖
      ≤ ‖a0 * (1 - (t : ℂ) ^ m) + ζ ^ n * ((t : ℂ) ^ n - (t : ℂ) ^ m)‖
          + ‖∑ k ∈ s, aCoeff k * ζ ^ k * ((t : ℂ) ^ k - (t : ℂ) ^ m)‖ :=
        norm_add_le _ _
    _ ≤ (‖a0 * (1 - (t : ℂ) ^ m)‖ + ‖ζ ^ n * ((t : ℂ) ^ n - (t : ℂ) ^ m)‖)
          + ∑ k ∈ s, ‖aCoeff k‖ * ‖ζ‖ ^ k * |t ^ k - t ^ m| :=
        add_le_add (norm_add_le _ _) hC
    _ ≤ ((1 - δ) * (1 - t ^ m) + ‖ζ‖ ^ n * (t ^ m - t ^ n))
          + (t ^ n + δ * (1 - t ^ m)) := by
        rw [hA, hB]; linarith
    _ = 1 - (1 - ‖ζ‖ ^ n) * (t ^ m - t ^ n) := by ring

/-- Strict containment from the pivot condition: away from the two endpoints of
the radial segment the bound of `pivot_norm_radial_le` is strictly below one,
because `‖ζ‖ < 1` and `t^m > t^n`. -/
theorem pivot_norm_radial_lt_one {n m : ℕ} (hmn : m < n) (s : Finset ℕ)
    {aCoeff : ℕ → ℂ} {a0 ζ : ℂ} {t δ : ℝ}
    (hroot : ζ ^ n + aCoeff m * ζ ^ m + (∑ k ∈ s, aCoeff k * ζ ^ k) + a0 = 0)
    (hζ : ‖ζ‖ < 1) (hδ : ‖a0‖ = 1 - δ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hN : ∑ k ∈ s, ‖aCoeff k‖ * ‖ζ‖ ^ k * |t ^ k - t ^ m|
            ≤ t ^ n + δ * (1 - t ^ m)) :
    ‖((t : ℂ) * ζ) ^ n + aCoeff m * ((t : ℂ) * ζ) ^ m
        + (∑ k ∈ s, aCoeff k * ((t : ℂ) * ζ) ^ k) + a0‖ < 1 := by
  have hbound := pivot_norm_radial_le hmn.le s hroot hδ ht0.le ht1.le hN
  have hzn : ‖ζ‖ ^ n < 1 := pow_lt_one₀ (norm_nonneg ζ) hζ (by omega)
  have hstrict : t ^ n < t ^ m := by
    have hmn' : t ^ n = t ^ m * t ^ (n - m) := by
      rw [← pow_add]; congr 1; omega
    have h1 : t ^ (n - m) < 1 := pow_lt_one₀ ht0.le ht1 (by omega)
    have h2 : (0 : ℝ) < t ^ m := pow_pos ht0 m
    nlinarith
  nlinarith

/-! ## 5. The sextic guardrail -/

/-- The stored sextic guardrail family
`f_r z = z^6 + (1/5) r^2 z^4 - (1/5) r^4 z^2 - r^6`. -/
noncomputable def sextic (r z : ℂ) : ℂ :=
  z ^ 6 + (1 / 5) * r ^ 2 * z ^ 4 - (1 / 5) * r ^ 4 * z ^ 2 - r ^ 6

/-- `f_r` factors as `(z^2 - r^2)(z^4 + (6/5) r^2 z^2 + r^4)`. -/
theorem sextic_factor (r z : ℂ) :
    sextic r z = (z ^ 2 - r ^ 2) * (z ^ 4 + (6 / 5) * r ^ 2 * z ^ 2 + r ^ 4) := by
  unfold sextic; ring

/-- The exact midpoint value on the spoke to the zero `r`:
`f_r (r/2) = -(327/320) r^6`. -/
theorem sextic_half_value (r : ℂ) : sextic r (r / 2) = -(327 / 320) * r ^ 6 := by
  unfold sextic; ring

/-- Every zero of the quartic factor has modulus exactly `r`.  The quadratic in
`w^2` has non-real roots, so `w^2` and its conjugate are the two roots and
Vieta gives `‖w^2‖^2 = r^4`. -/
private theorem quadratic_conjugate_norm_sq {r : ℝ} (hr : 0 < r) {v : ℂ}
    (hv : v ^ 2 + (6 / 5) * (r : ℂ) ^ 2 * v + (r : ℂ) ^ 4 = 0) :
    ‖v‖ ^ 2 = r ^ 4 := by
  have hvbar : (starRingEnd ℂ) v ^ 2 + (6 / 5) * (r : ℂ) ^ 2 * (starRingEnd ℂ) v
      + (r : ℂ) ^ 4 = 0 := by
    have h := congrArg (starRingEnd ℂ) hv
    simpa [map_ofNat] using h
  have hne : (starRingEnd ℂ) v ≠ v := by
    intro hcon
    have hreal : ((v.re : ℝ) : ℂ) = v := Complex.conj_eq_iff_re.mp hcon
    have hcast : ((v.re ^ 2 + (6 / 5) * r ^ 2 * v.re + r ^ 4 : ℝ) : ℂ) = 0 := by
      push_cast
      rw [hreal]
      linear_combination hv
    have hR : v.re ^ 2 + (6 / 5) * r ^ 2 * v.re + r ^ 4 = 0 := by
      exact_mod_cast hcast
    nlinarith [sq_nonneg (v.re + (3 / 5) * r ^ 2), pow_pos hr 4]
  have hsum : (starRingEnd ℂ) v + v + (6 / 5) * (r : ℂ) ^ 2 = 0 := by
    have hd : ((starRingEnd ℂ) v - v)
        * ((starRingEnd ℂ) v + v + (6 / 5) * (r : ℂ) ^ 2) = 0 := by
      linear_combination hvbar - hv
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hprod : v * (starRingEnd ℂ) v = (r : ℂ) ^ 4 := by
    linear_combination v * hsum - hv
  have h := congrArg norm hprod
  rw [norm_mul, RCLike.norm_conj] at h
  have hrhs : ‖((r : ℂ)) ^ 4‖ = r ^ 4 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [hrhs] at h
  rw [pow_two]
  exact h

theorem sextic_quartic_root_norm {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hw : w ^ 4 + (6 / 5) * (r : ℂ) ^ 2 * w ^ 2 + (r : ℂ) ^ 4 = 0) :
    ‖w‖ = r := by
  have hv : (w ^ 2) ^ 2 + (6 / 5) * (r : ℂ) ^ 2 * (w ^ 2) + (r : ℂ) ^ 4 = 0 := by
    linear_combination hw
  have hnorm := quadratic_conjugate_norm_sq hr hv
  rw [norm_pow] at hnorm
  have h4 : ‖w‖ ^ 4 = r ^ 4 := by linear_combination hnorm
  have hfac : (‖w‖ - r) * ((‖w‖ + r) * (‖w‖ ^ 2 + r ^ 2)) = 0 := by
    linear_combination h4
  rcases mul_eq_zero.mp hfac with h | h
  · linarith [sub_eq_zero.mp h]
  · exfalso
    rcases mul_eq_zero.mp h with h' | h'
    · linarith [norm_nonneg w]
    · nlinarith [sq_nonneg ‖w‖, pow_pos hr 2]

/-- Every zero of `f_r` has modulus exactly `r`.  In particular, for `0 < r < 1`
all six zeros lie in the open unit disc. -/
theorem sextic_root_norm {r : ℝ} (hr : 0 < r) {w : ℂ}
    (hw : sextic (r : ℂ) w = 0) : ‖w‖ = r := by
  rw [sextic_factor] at hw
  rcases mul_eq_zero.mp hw with h | h
  · have hfac : (w - (r : ℂ)) * (w + (r : ℂ)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h' | h'
    · have hwr : w = (r : ℂ) := by linear_combination h'
      rw [hwr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    · have hwr : w = -(r : ℂ) := by linear_combination h'
      rw [hwr, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  · exact sextic_quartic_root_norm hr h

/-- The spoke from the origin to the zero `r` leaves the unit sublevel set once
`r^6 > 320/327`, because `‖f_r (r/2)‖ = (327/320) r^6`. -/
theorem sextic_half_norm_gt_one {r : ℝ} (hbig : 320 / 327 < r ^ 6) :
    1 < ‖sextic (r : ℂ) ((r : ℂ) / 2)‖ := by
  rw [sextic_half_value]
  have hcast : -(327 / 320 : ℂ) * (r : ℂ) ^ 6
      = ((-(327 / 320) * r ^ 6 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by nlinarith [sq_nonneg (r ^ 3)])]
  nlinarith

/-- **The sextic guardrail.**  For `320/327 < r^6` and `0 < r < 1`, every zero of
`f_r` lies in the open unit disc, yet the radial spoke from the origin to the
zero `r` leaves `{|f_r| < 1}` at the parameter `1/2`.

Two active intermediate modes are enough to destroy the radial mechanism that
solves the trinomial face in §3 — the Abel control polygon of the spoke to `r`
is `-r^6, -r^6, -(6/5) r^6, -(6/5) r^6, -r^6, -r^6`, which leaves the unit disc
and returns, a pattern impossible with a single intermediate coefficient.

This is **not** a counterexample to Erdős #1041: only the prescribed radial
spoke fails, and a different pair of zeros of `f_r` still admits a short path.
The statement below claims exactly the spoke failure and nothing more. -/
theorem sextic_guardrail {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hbig : 320 / 327 < r ^ 6) :
    (∀ w : ℂ, sextic (r : ℂ) w = 0 → ‖w‖ < 1) ∧
      1 < ‖sextic (r : ℂ) ((r : ℂ) / 2)‖ := by
  refine ⟨fun w hw => ?_, sextic_half_norm_gt_one hbig⟩
  rw [sextic_root_norm hr hw]
  exact hr1

end ErdosProblems.Erdos1041.AbelControlPolygon
