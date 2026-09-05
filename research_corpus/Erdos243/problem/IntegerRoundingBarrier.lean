import ErdosProblems.Erdos243.SparseResetRecovery

/-!
# Erdős #243: the integer-rounding linear barrier and the shifted negative mass

This module formalises the *rounding* half of the r01 return
(`r01_critical_boundary_integer_rounding.md`, Type B batch
`erdos243_20260905_eight_return_stream_01`), and settles the status of the
proposed `B`-shifted generalisation of the summable-negative-mass consumer.

## What is proved

* `psi_sub_le_supporting_line` — the periodic quadratic inequality (15).  The
  return proves it by concavity of `t ↦ Ψ(t) - t²/2`; the proof here is
  division-free and finite: after subtracting the supporting line at `s`, the
  whole inequality collapses to `f * u ≤ u(u+1)/2` for `f = {t} ∈ [0,1)` and the
  integer `u = ⌊s⌋ - ⌊t⌋` (`fract_mul_int_le`).  No concavity API is used.
* `fract_lower_bound_of_ratio` — the pointwise phase bound (16), in the *sharp*
  form `θ ≥ 1/2 - 1/(16R) + …` identified by wave-1 agent A, and with the
  hypothesis `A/B ≥ 1/2` (resp. `> 1/4`) **removed**: the completion of the
  square is `B(θ - 1/4)²/A ≥ 0`, which needs only `A, B > 0`.  The condition
  `R > 1/4` is exactly the condition for this bound to beat the return's `1/4`,
  not a condition for its validity.
* `linear_barrier_of_step_le` — the linear barrier (18).  Division-free: the
  envelope hypothesis `X_{k+1} ≤ r_k X_k` with `r_k = 1 + (1+η_k)/k` is written
  as `k · X_{k+1} ≤ (k + 1 + η_k) · X_k` over `ℝ`, with `X : ℕ → ℕ` (so
  integrality of the orbit is available) and `η : ℕ → ℝ` nonnegative and
  antitone from `n`.  Integrality is used exactly once, to turn the strict real
  bound `X_{k+1} < m(k+1) + 1` into `X_{k+1} ≤ m(k+1)`.
* `linear_barrier_of_div_succ` — the `m := ⌊X_n/n⌋ + 1` instance, which is the
  usable form of `m = ⌈X_n/n⌉` (`⌈x⌉ ≤ ⌊x⌋ + 1`, and the barrier hypothesis is
  monotone in the wrong direction only by that one unit).
* `step_rise_le_of_barrier` — the corollary (14): `(X_{k+1} - X_k)_+ ≤ m`
  eventually, again by integrality.
* `tail_growth_le_one_add_shiftedNegativeRelativeMass` and
  `tail_le_prod_mul_of_shifted_growth` — the `B`-shifted analogue of the
  growth/product machinery in `SparseResetRecovery.lean`.  Summable shifted mass
  gives `C n = O(n)`, **not** `C n = O(1)`.
* `shifted_negativeRelativeMass_consumer_false` — a kernel-checked
  counter-model showing that the naive `B`-shifted generalisation of
  `eventually_zero_of_summable_negativeRelativeMass` is **false**.

## The shifted consumer is not a direct generalisation

Wave-1 agent A recorded the target
`summable_shifted_negative_mass_sylvesterNext_eventually` as differing from the
landed `sylvesterNext_eventually_of_summable_negativeRelativeMass` "only in
replacing `min (E n) 0` by `min (E n + B) 0`".  At the level of the abstract
`C`/`E` interface that statement is false, and
`shifted_negativeRelativeMass_consumer_false` exhibits the counter-model:

  `C n = B·n + 1`,  `E n = -B`  (any `B ≥ 1`).

This satisfies every hypothesis of the `B = 0` theorem with the shift in place —
positivity, the exact update `C_{n+1} = C_n - E_n`, division-free normalised
vanishing (`K·|E n| = K·B < B·n + 1` for `n ≥ K`), and summability of the
shifted mass, which is *identically zero* — and yet `E n = -B ≠ 0` forever.

The obstruction is structural, and it is the one flagged in the task brief: the
shifted sum controls only the rises **above** `B`, and rises `≤ B` accumulate
freely.  The bounded-product argument of `SparseResetRecovery.lean` degrades
from `C n = O(1)` to `C n = O(n)`; `O(n)` is not enough for the endpoint, and
`tail_le_prod_mul_of_shifted_growth` shows `O(n)` is exactly what survives.

So r01 (47) is a genuine theorem only through r01 Theorem 4's *arithmetic*
dichotomy (contact with a fresh modulus, or a CRT wall crossing), never through
the product route.  The counter-model above is not an orbit: on a canonical
orbit `C_{n+1} = C_n - E_n` with `E_n = -B` constant would force `C_n ≡ C_N`
mod `B`, and Theorem 4 Case 1 then applies.  That is precisely the content the
Lean proof still has to supply.

## OPEN

The orbit-level statement, stated exactly, still to be proved (it needs
Theorem 4 Case 1 = `commonDivisor_persists` + `multiplierOverlap_persists` from
`SlowRiseBarrier.lean`, and Case 2 = `exists_consecutiveMultiples_between`
plus the wall-counting lemma `H(C_{n+1}) - H(C_n) ≤ (C_{n+1} - C_n - B)_+/C_n`):

```
theorem summable_shifted_negative_mass_sylvesterNext_eventually
    (a D : ℕ → ℤ) (C : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, (C (n + 1) : ℤ) = nextTailState (a n) (D n) (C n))
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) =
        (C n : ℤ) - centeredState (a n) (D n) (C n))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (centeredState (a n) (D n) (C n)) < C n)
    (hsum : ∃ B : ℕ, Summable
        (shiftedNegativeRelativeMass C
          (fun n ↦ centeredState (a n) (D n) (C n)) B)) :
    ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n)
```

Also OPEN, and now known to be the *only* remaining analytic bridge in the
rounding route: the contradiction branch of r01 Theorem 2 (Abel summation of
`(32)`, summability of the quadratic error `(33)`, and the divergence
`∑ 1/F_n = ∞`), which converts failure of the barrier at every large `n` into a
contradiction.  The barrier itself is finished here.

Nothing in this module settles Erdős #243.
-/

namespace ErdosProblems.Erdos243

open scoped BigOperators

/-! ## 1. The periodic quadratic inequality (15) -/

/-- The periodic quadratic `Ψ(t) = ({t}² - {t})/2` of the r01 return. -/
noncomputable def psi (t : ℝ) : ℝ :=
  (Int.fract t ^ 2 - Int.fract t) / 2

theorem psi_nonpos (t : ℝ) : psi t ≤ 0 := by
  have h0 := Int.fract_nonneg t
  have h1 := (Int.fract_lt_one t).le
  have : Int.fract t ^ 2 ≤ Int.fract t := by nlinarith
  simp only [psi]
  linarith

theorem neg_one_eighth_le_psi (t : ℝ) : -(1 / 8 : ℝ) ≤ psi t := by
  have : 0 ≤ (Int.fract t - 1 / 2) ^ 2 := sq_nonneg _
  simp only [psi]
  nlinarith

/-- The entire content of `(15)` after the supporting line at `s` is subtracted:
for a fractional part `f` and an integer `u`, `f · u ≤ u(u+1)/2`. -/
theorem fract_mul_int_le (u : ℤ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f < 1) :
    f * (u : ℝ) ≤ (u : ℝ) * ((u : ℝ) + 1) / 2 := by
  rcases le_or_gt 0 u with hu | hu
  · rcases eq_or_lt_of_le hu with h | h
    · rw [← h]
      norm_num
    · have h1u : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast h
      nlinarith
  · have hu' : (u : ℝ) ≤ -1 := by
      have : u ≤ -1 := by omega
      exact_mod_cast this
    nlinarith

/-- **(15)**.  For all real `s, t`, with `θ = {s}`,
`Ψ(t) - Ψ(s) ≤ (θ - 1/2)(t - s) + (t - s)²/2`.

There is no restriction on integer crossings.  The proof is the exact algebraic
identity that the difference of the two sides equals `{t}·u - u(u+1)/2` for the
integer `u = ⌊s⌋ - ⌊t⌋`, together with `fract_mul_int_le`. -/
theorem psi_sub_le_supporting_line (s t : ℝ) :
    psi t - psi s ≤ (Int.fract s - 1 / 2) * (t - s) + (t - s) ^ 2 / 2 := by
  have key :=
    fract_mul_int_le (⌊s⌋ - ⌊t⌋) (Int.fract t)
      (Int.fract_nonneg t) (Int.fract_lt_one t)
  push_cast at key
  have hft : Int.fract t = t - (⌊t⌋ : ℝ) := rfl
  have hfs : Int.fract s = s - (⌊s⌋ : ℝ) := rfl
  have hid :
      psi t - psi s - ((Int.fract s - 1 / 2) * (t - s) + (t - s) ^ 2 / 2)
        = Int.fract t * ((⌊s⌋ : ℝ) - (⌊t⌋ : ℝ))
          - ((⌊s⌋ : ℝ) - (⌊t⌋ : ℝ)) * (((⌊s⌋ : ℝ) - (⌊t⌋ : ℝ)) + 1) / 2 := by
    rw [psi, psi, hft, hfs]
    ring
  linarith [hid, key]

/-! ## 2. The pointwise phase bound (16), sharp form -/

/-- **(16), sharp form.**  For `A, B > 0`, `θ = {s}`, `Δ = A - Bθ`, and
`R = A/B`:
`θ ≥ 1/2 - 1/(16R) + (Ψ(s+Δ) - Ψ(s))/A - Δ²/(2A)`, written division-free in `R`
as `1/2 - B/(16A) + …`.

Two deviations from the return, both verified by wave-1 agent A on exact
rational grids: the constant is `1/2 - 1/(16R)` rather than `1/4` (tight,
equality at `θ = 1/4`), and the hypothesis `A/B ≥ 1/2` is unnecessary — the
completion of the square is `B(θ - 1/4)²/A ≥ 0`.  `R > 1/4` is the condition
under which this bound is *stronger* than the return's, not a hypothesis. -/
theorem fract_lower_bound_of_ratio (A B s : ℝ) (hA : 0 < A) (hB : 0 < B) :
    1 / 2 - B / (16 * A)
        + (psi (s + (A - B * Int.fract s)) - psi s) / A
        - (A - B * Int.fract s) ^ 2 / (2 * A)
      ≤ Int.fract s := by
  have hAne : A ≠ 0 := ne_of_gt hA
  set θ := Int.fract s with hθ
  set Δ : ℝ := A - B * θ with hΔ
  have h15 := psi_sub_le_supporting_line s (s + Δ)
  have hsimp : s + Δ - s = Δ := by ring
  rw [hsimp, ← hθ] at h15
  have hdiv :
      (psi (s + Δ) - psi s) / A
        ≤ ((θ - 1 / 2) * Δ + Δ ^ 2 / 2) / A := by
    gcongr
  have hfinal :
      1 / 2 - B / (16 * A)
          + ((θ - 1 / 2) * Δ + Δ ^ 2 / 2) / A
          - Δ ^ 2 / (2 * A)
        ≤ θ := by
    rw [← sub_nonneg]
    have hrw :
        θ - (1 / 2 - B / (16 * A)
              + ((θ - 1 / 2) * Δ + Δ ^ 2 / 2) / A
              - Δ ^ 2 / (2 * A))
          = B * (θ - 1 / 4) ^ 2 / A := by
      rw [hΔ]
      field_simp
      ring
    rw [hrw]
    positivity
  linarith

/-! ## 3. The linear barrier (18) -/

/-- **(18), the linear barrier.**  Let `X : ℕ → ℕ` satisfy the division-free
envelope step `k · X_{k+1} ≤ (k + 1 + η_k) · X_k` for `k ≥ n`, which is exactly
`X_{k+1} ≤ r_k X_k` for `r_k = 1 + (1 + η_k)/k`.  Let `η` be nonnegative and
antitone from `n`.  If `X_n ≤ m·n` and `m·η_n < 1`, then `X_k ≤ m·k` for every
`k ≥ n`.

Integrality of `X` is used exactly once, at the end of the induction step.
This is the half of r01 Theorem 2 that produces the usable constant `M`; it is
a general integer-rounding trap lemma, independent of #243. -/
theorem linear_barrier_of_step_le
    (X : ℕ → ℕ) (η : ℕ → ℝ) (m n : ℕ)
    (hn : 0 < n)
    (hηnonneg : ∀ k, n ≤ k → 0 ≤ η k)
    (hηanti : ∀ k, n ≤ k → η k ≤ η n)
    (hstep : ∀ k, n ≤ k → (k : ℝ) * X (k + 1) ≤ ((k : ℝ) + 1 + η k) * X k)
    (hbarrier : (m : ℝ) * η n < 1)
    (hbase : X n ≤ m * n) :
    ∀ k, n ≤ k → X k ≤ m * k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
      have hkpos : 0 < k := lt_of_lt_of_le hn hk
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
      have hXk : (X k : ℝ) ≤ (m : ℝ) * (k : ℝ) := by exact_mod_cast ih
      have hηk : 0 ≤ η k := hηnonneg k hk
      have hmη : (m : ℝ) * η k ≤ (m : ℝ) * η n :=
        mul_le_mul_of_nonneg_left (hηanti k hk) (Nat.cast_nonneg m)
      have hmηk : (m : ℝ) * η k < 1 := lt_of_le_of_lt hmη hbarrier
      have h1 : (k : ℝ) * X (k + 1) ≤ ((k : ℝ) + 1 + η k) * X k := hstep k hk
      have h2 : ((k : ℝ) + 1 + η k) * X k ≤ ((k : ℝ) + 1 + η k) * ((m : ℝ) * k) :=
        mul_le_mul_of_nonneg_left hXk (by linarith)
      have h3' : (k : ℝ) * ((m : ℝ) * η k) < (k : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hmηk hkR
      have h3 : ((k : ℝ) + 1 + η k) * ((m : ℝ) * k)
          < (k : ℝ) * ((m : ℝ) * ((k : ℝ) + 1) + 1) := by nlinarith [h3']
      have h4 : (k : ℝ) * X (k + 1) < (k : ℝ) * ((m : ℝ) * ((k : ℝ) + 1) + 1) := by
        linarith
      have h5 : (X (k + 1) : ℝ) < (m : ℝ) * ((k : ℝ) + 1) + 1 :=
        lt_of_mul_lt_mul_left h4 hkR.le
      have h6 : (X (k + 1) : ℝ) < ((m * (k + 1) + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      have h7 : X (k + 1) < m * (k + 1) + 1 := by exact_mod_cast h6
      omega

/-- The `m = ⌈X_n / n⌉` instance, in the usable form `m = ⌊X_n / n⌋ + 1`
(`⌈x⌉ ≤ ⌊x⌋ + 1`, with equality unless `n ∣ X n`). -/
theorem linear_barrier_of_div_succ
    (X : ℕ → ℕ) (η : ℕ → ℝ) (n : ℕ)
    (hn : 0 < n)
    (hηnonneg : ∀ k, n ≤ k → 0 ≤ η k)
    (hηanti : ∀ k, n ≤ k → η k ≤ η n)
    (hstep : ∀ k, n ≤ k → (k : ℝ) * X (k + 1) ≤ ((k : ℝ) + 1 + η k) * X k)
    (hbarrier : ((X n / n + 1 : ℕ) : ℝ) * η n < 1) :
    ∀ k, n ≤ k → X k ≤ (X n / n + 1) * k := by
  apply linear_barrier_of_step_le X η _ n hn hηnonneg hηanti hstep hbarrier
  have hdm := Nat.div_add_mod (X n) n
  have hmod := Nat.mod_lt (X n) hn
  nlinarith [hdm, hmod]

/-- **(14)**, the rise corollary.  Under the barrier hypotheses the forward
increments are bounded by `m`: `X_{k+1} ≤ X_k + m` for every `k ≥ n`.  Again the
last step is integrality: the real bound is `X_{k+1} - X_k < m(1 + η_k) < m + 1`. -/
theorem step_rise_le_of_barrier
    (X : ℕ → ℕ) (η : ℕ → ℝ) (m n : ℕ)
    (hn : 0 < n)
    (hηnonneg : ∀ k, n ≤ k → 0 ≤ η k)
    (hηanti : ∀ k, n ≤ k → η k ≤ η n)
    (hstep : ∀ k, n ≤ k → (k : ℝ) * X (k + 1) ≤ ((k : ℝ) + 1 + η k) * X k)
    (hbarrier : (m : ℝ) * η n < 1)
    (hbase : X n ≤ m * n) :
    ∀ k, n ≤ k → X (k + 1) ≤ X k + m := by
  have hlin := linear_barrier_of_step_le X η m n hn hηnonneg hηanti hstep hbarrier hbase
  intro k hk
  have hkpos : 0 < k := lt_of_lt_of_le hn hk
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hXk : (X k : ℝ) ≤ (m : ℝ) * (k : ℝ) := by exact_mod_cast hlin k hk
  have hηk : 0 ≤ η k := hηnonneg k hk
  have hmηk : (m : ℝ) * η k < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hηanti k hk) (Nat.cast_nonneg m)) hbarrier
  have h1 : (k : ℝ) * X (k + 1) ≤ ((k : ℝ) + 1 + η k) * X k := hstep k hk
  -- `(k + 1 + η k) X k = k X k + (1 + η k) X k ≤ k X k + (1 + η k) m k`
  have h2 : (1 + η k) * (X k : ℝ) ≤ (1 + η k) * ((m : ℝ) * k) :=
    mul_le_mul_of_nonneg_left hXk (by linarith)
  have h3' : (k : ℝ) * ((m : ℝ) * η k) < (k : ℝ) * 1 :=
    mul_lt_mul_of_pos_left hmηk hkR
  have h4 : (k : ℝ) * X (k + 1) < (k : ℝ) * ((X k : ℝ) + (m : ℝ) + 1) := by
    nlinarith [h3']
  have h5 : (X (k + 1) : ℝ) < (X k : ℝ) + (m : ℝ) + 1 :=
    lt_of_mul_lt_mul_left h4 hkR.le
  have h6 : (X (k + 1) : ℝ) < ((X k + m + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have h7 : X (k + 1) < X k + m + 1 := by exact_mod_cast h6
  omega

/-! ## 4. The `B`-shifted normalised negative mass -/

/-- The `B`-shifted normalised negative mass, `(-Eₙ - B)₊ / Cₙ`.  For `B = 0`
this is `negativeRelativeMass` of `SparseResetRecovery.lean`. -/
noncomputable def shiftedNegativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (B : ℕ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n + (B : ℤ)) 0) : ℝ) / C n

theorem shiftedNegativeRelativeMass_zero (C : ℕ → ℕ) (E : ℕ → ℤ) :
    shiftedNegativeRelativeMass C E 0 = negativeRelativeMass C E := by
  funext n
  simp [shiftedNegativeRelativeMass, negativeRelativeMass]

theorem shiftedNegativeRelativeMass_nonneg
    (C : ℕ → ℕ) (E : ℕ → ℤ) (B n : ℕ) :
    0 ≤ shiftedNegativeRelativeMass C E B n :=
  div_nonneg (by positivity) (by positivity)

/-- The shifted analogue of `tail_growth_le_one_add_negativeRelativeMass`: the
exact update `Cₙ₊₁ = Cₙ - Eₙ` is bounded by multiplication by
`1 + shiftedNegativeRelativeMass` **plus an additive `B`**.  The additive term
is unavoidable: rises up to `B` are invisible to the shifted mass. -/
theorem tail_growth_le_one_add_shiftedNegativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (B : ℕ)
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) :
    ∀ n,
      (C (n + 1) : ℝ) ≤
        C n * (1 + shiftedNegativeRelativeMass C E B n) + B := by
  intro n
  have hCne : (C n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hCpos n))
  have hstepR : (C (n + 1) : ℝ) = (C n : ℝ) - (E n : ℝ) := by
    exact_mod_cast hstep n
  by_cases he : E n + (B : ℤ) ≤ 0
  · have hmin : min (E n + (B : ℤ)) 0 = E n + (B : ℤ) := min_eq_left he
    have habscast : (Int.natAbs (E n + (B : ℤ)) : ℤ) = -(E n + (B : ℤ)) :=
      Int.ofNat_natAbs_of_nonpos he
    have habsR : (Int.natAbs (E n + (B : ℤ)) : ℝ) = -((E n : ℝ) + (B : ℝ)) := by
      calc
        (Int.natAbs (E n + (B : ℤ)) : ℝ)
            = (((Int.natAbs (E n + (B : ℤ)) : ℕ) : ℤ) : ℝ) := by norm_num
        _ = ((-(E n + (B : ℤ)) : ℤ) : ℝ) := by rw [habscast]
        _ = -((E n : ℝ) + (B : ℝ)) := by push_cast; ring
    rw [shiftedNegativeRelativeMass, hmin, habsR, hstepR]
    field_simp
    linarith
  · have hepos : 0 ≤ E n + (B : ℤ) := by omega
    have hmin : min (E n + (B : ℤ)) 0 = 0 := min_eq_right hepos
    have heposR : 0 ≤ (E n : ℝ) + (B : ℝ) := by exact_mod_cast hepos
    rw [shiftedNegativeRelativeMass, hmin]
    simp only [Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, mul_one]
    rw [hstepR]
    linarith

/-- Summable shifted mass gives only a **linear** bound on `C`.  This is the
exact point at which the `B = 0` argument of `SparseResetRecovery.lean` degrades:
there the same induction gives `C n ≤ C 0 · ∏(1 + δ)`, here it gives
`C n ≤ (C 0 + B·n) · ∏(1 + δ)`. -/
theorem tail_le_prod_mul_of_shifted_growth
    (C : ℕ → ℕ) (δ : ℕ → ℝ) (B : ℕ)
    (hδ : ∀ n, 0 ≤ δ n)
    (hgrowth : ∀ n, (C (n + 1) : ℝ) ≤ C n * (1 + δ n) + B) :
    ∀ N, (C N : ℝ) ≤ (∏ i ∈ Finset.range N, (1 + δ i)) * ((C 0 : ℝ) + B * N) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hprodpos : (0 : ℝ) ≤ ∏ i ∈ Finset.range N, (1 + δ i) :=
        Finset.prod_nonneg fun i _ ↦ by linarith [hδ i]
      have hprodone : (1 : ℝ) ≤ ∏ i ∈ Finset.range (N + 1), (1 + δ i) :=
        Finset.one_le_prod fun i _ ↦ by linarith [hδ i]
      have hstepN := hgrowth N
      have hmul :
          (C N : ℝ) * (1 + δ N)
            ≤ ((∏ i ∈ Finset.range N, (1 + δ i)) * ((C 0 : ℝ) + B * N)) * (1 + δ N) :=
        mul_le_mul_of_nonneg_right ih (by linarith [hδ N])
      have hrw :
          ((∏ i ∈ Finset.range N, (1 + δ i)) * ((C 0 : ℝ) + B * N)) * (1 + δ N)
            = (∏ i ∈ Finset.range (N + 1), (1 + δ i)) * ((C 0 : ℝ) + B * N) := by
        rw [Finset.prod_range_succ]
        ring
      have hBpos : (0 : ℝ) ≤ (B : ℝ) := by positivity
      have hlast :
          (∏ i ∈ Finset.range (N + 1), (1 + δ i)) * ((C 0 : ℝ) + B * N) + B
            ≤ (∏ i ∈ Finset.range (N + 1), (1 + δ i))
                * ((C 0 : ℝ) + B * ((N : ℝ) + 1)) := by
        have : (B : ℝ) ≤ (∏ i ∈ Finset.range (N + 1), (1 + δ i)) * B := by
          nlinarith
        nlinarith
      push_cast
      calc
        (C (N + 1) : ℝ) ≤ (C N : ℝ) * (1 + δ N) + B := hstepN
        _ ≤ ((∏ i ∈ Finset.range N, (1 + δ i)) * ((C 0 : ℝ) + B * N)) * (1 + δ N) + B := by
              linarith
        _ = (∏ i ∈ Finset.range (N + 1), (1 + δ i)) * ((C 0 : ℝ) + B * N) + B := by
              rw [hrw]
        _ ≤ (∏ i ∈ Finset.range (N + 1), (1 + δ i)) * ((C 0 : ℝ) + B * ((N : ℝ) + 1)) :=
              hlast

/-- **The proposed `B`-shifted consumer is FALSE at the `C`/`E` interface.**

Every hypothesis of `eventually_zero_of_summable_negativeRelativeMass` is met
with `negativeRelativeMass` replaced by `shiftedNegativeRelativeMass … B` — and
the conclusion fails.  Witness: `C n = B·n + 1`, `E n = -B`, for any `B ≥ 1`.
The shifted mass is identically zero.

Consequence: r01 (47) is not a generalisation of the landed theorem obtained by
substituting `min (E n + B) 0` for `min (E n) 0`; it requires the arithmetic of
r01 Theorem 4 (fresh-modulus contact, or CRT wall crossings).  See the module
docstring for the exact statement that remains OPEN. -/
theorem shifted_negativeRelativeMass_consumer_false (B : ℕ) (hB : 0 < B) :
    ∃ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) ∧
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) ∧
      (∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) ∧
      (∀ n, shiftedNegativeRelativeMass C E B n = 0) ∧
      Summable (shiftedNegativeRelativeMass C E B) ∧
      ¬ (∃ N, ∀ n, N ≤ n → E n = 0) := by
  classical
  refine ⟨fun n ↦ B * n + 1, fun _ ↦ -(B : ℤ), fun n ↦ by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    push_cast
    ring
  · intro K
    refine ⟨K, fun n hn ↦ ?_⟩
    show K * Int.natAbs (-(B : ℤ)) < B * n + 1
    have hnat : Int.natAbs (-(B : ℤ)) = B := by simp
    rw [hnat]
    have hKB : K * B ≤ B * n := by
      calc K * B = B * K := Nat.mul_comm _ _
        _ ≤ B * n := Nat.mul_le_mul_left B hn
    omega
  · intro n
    simp [shiftedNegativeRelativeMass]
  · have hzero :
        shiftedNegativeRelativeMass (fun n ↦ B * n + 1) (fun _ ↦ -(B : ℤ)) B
          = fun _ ↦ (0 : ℝ) := by
      funext n
      simp [shiftedNegativeRelativeMass]
    rw [hzero]
    exact summable_zero
  · rintro ⟨N, hN⟩
    have h : -(B : ℤ) = 0 := hN N le_rfl
    have hB0 : (B : ℤ) = 0 := by linarith
    have hB0' : B = 0 := by exact_mod_cast hB0
    omega

end ErdosProblems.Erdos243
