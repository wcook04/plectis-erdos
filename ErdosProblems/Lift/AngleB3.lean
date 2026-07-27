/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.Recon257

/-!
# Angle B3: conditional escape and no recurrence above a threshold

This file proves two conditional facts about the signed excess and a
bounded-pulse ratchet. It does **not** prove that all live ratchet states are
non-periodic, and it does not resolve Erdős problem #257.
All positive mathematical claims below are **PROVED**, with their hypotheses
shown; this module reports no measurements.

## Part 1: an escape barrier on an assumed right tail

On an eventual right tail, the signed excess

  `E s = seamIntegerGreedyRemainder s - 2 ^ s`

obeys the exact affine law

  `E (s+1) = 4 * E s - belowPulse s - 4`,   `0 < E s`.

Put `H s = 9 * E s - 6 * s - 2`. The only additional inequality used in the
escape calculation is the pulse cap
`seamAdjacentCut_belowPulse_le : belowPulse s ≤ 2 * (s - 2)`. Under the same
eventual-right-tail hypothesis this gives

  `4 * H s ≤ H (s+1)`                          (`four_mul_escapePotential_le`)

and hence:

* `escapePotential_geom` : `1 ≤ H s → 4 ^ n ≤ H (s + n)`;
* `belowPulse_lt_of_escaped` : once `1 ≤ H s`, at every later rank
  `belowPulse t + 4 < 4 * E t`.

`1 ≤ H s` is exactly `2 * s + 1 ≤ 3 * E s`. Thus, within an orbit already
assumed to remain on the right tail, crossing this barrier prevents the pulse
cap from contradicting next-step positivity. This is not a proof that the
right-tail hypothesis holds. Conversely, `band_of_never_escaping` records the
linear bound `3 * E s ≤ 2 * s` under the explicit hypothesis that the potential
never becomes positive.

## Part 2: no recurrence above the bounded-pulse threshold

For a bounded pulse `P ≤ Q`, the generic ratchet step is
`b ↦ 4 * b - 3 * P s - 3` while it remains live. The constant pulse `P ≡ Q`
has a fixed point at `b = Q + 1`. Uniformly for arbitrary `P ≤ Q`, the
theorems below require the strictly higher initial bound `Q + 2 ≤ b`:

* `ratchetOrbit_strictMono` : the budget gains at least `3` per step;
* `ratchetOrbit_geom` : the budget grows at least geometrically;
* `ratchetOrbit_no_recurrence` : a state starting at `b ≥ Q + 2` does not
  return to its initial budget.

For the local rank-`26` pulse-floor copy, a separate theorem shows that a budget
starting at `b ≥ 10` gains at least `3` over every two steps. The general
no-recurrence theorem starts at `b ≥ 11`, and the concrete two-step theorem
starts at `b ≥ 10`; neither analyzes live initial budgets `1, …, 9`. Therefore
this file does not establish the former headline claim that the ratchet has no
periodic orbit at all.

Unlike the original version of this file, the module now imports `Recon257`.
The local `seamExcess`, `pulseAt`, and `pulseFloor` copies and the specialization
of the generic `ratchetStep` are connected to the corresponding `Recon257`
definitions by explicit, kernel-checked definitional equalities below. Claims
about the concrete ratchet therefore use a Lean bridge rather than textual
identity alone.
-/

namespace Erdos249257

namespace AngleB3

open HalfCylinderIntegerGreedy

/-! ## Part 0.  The signed excess and its exact affine orbit -/

/-- The signed excess of the concrete greedy seam above the dyadic half point.
This local copy is connected to `Recon257.seamExcess` by
`seamExcess_eq_recon257` below. -/
def seamExcess (s : ℕ) : ℤ :=
  (seamIntegerGreedyRemainder s : ℤ) - ((2 ^ s : ℕ) : ℤ)

@[simp] theorem seamExcess_eq_recon257 (s : ℕ) :
    seamExcess s = Recon257.seamExcess s := by
  rfl

/-- On an eventual right tail the excess is strictly positive. -/
theorem seamExcess_pos
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (s : ℕ) (hs : S ≤ s) :
    0 < seamExcess s := by
  simpa [seamExcess] using
    (eventualRightTail_positive_affineExcess hS5 hright s hs).1

/-- On an eventual right tail the excess obeys the exact base-four affine law
driven by the below-pulse charge. -/
theorem seamExcess_succ_eq
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (s : ℕ) (hs : S ≤ s) (h5 : 5 ≤ s) :
    seamExcess (s + 1) =
      4 * seamExcess s - ((seamAdjacentCut s h5).belowPulse : ℤ) - 4 := by
  simpa [seamExcess] using
    (eventualRightTail_positive_affineExcess hS5 hright s hs).2

/-- The rowwise pulse cap in the form used below. Apart from the conditional
affine law, this is the only inequality used in the escape calculation. -/
theorem belowPulse_add_four_le {s : ℕ} (h5 : 5 ≤ s) :
    ((seamAdjacentCut s h5).belowPulse : ℤ) + 4 ≤ 2 * (s : ℤ) := by
  have h := seamAdjacentCut_belowPulse_le h5
  have h' : (seamAdjacentCut s h5).belowPulse + 4 ≤ 2 * s := by omega
  exact_mod_cast h'

/-! ## Part 1.  The escape barrier -/

/-- The escape potential of the signed excess.  `1 ≤ escapePotential s` is
exactly `2 * s + 1 ≤ 3 * seamExcess s`. -/
def escapePotential (s : ℕ) : ℤ :=
  9 * seamExcess s - 6 * (s : ℤ) - 2

theorem one_le_escapePotential_iff (s : ℕ) :
    1 ≤ escapePotential s ↔ 2 * (s : ℤ) + 1 ≤ 3 * seamExcess s := by
  unfold escapePotential
  omega

/-- **The potential expands by a factor four on the assumed right tail.** This
uses the conditional affine law and the cap `belowPulse s ≤ 2 * (s - 2)`. -/
theorem four_mul_escapePotential_le
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (s : ℕ) (hs : S ≤ s) :
    4 * escapePotential s ≤ escapePotential (s + 1) := by
  have h5 : 5 ≤ s := by omega
  have hrec := seamExcess_succ_eq hS5 hright s hs h5
  have hb := belowPulse_add_four_le h5
  unfold escapePotential
  push_cast
  omega

/-- **Geometric escape under the right-tail hypothesis.** Once the potential
is positive it grows at least like `4 ^ n` at every later rank. -/
theorem escapePotential_geom
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (s : ℕ) (hs : S ≤ s) (hesc : 1 ≤ escapePotential s) :
    ∀ n : ℕ, (4 : ℤ) ^ n ≤ escapePotential (s + n) := by
  intro n
  induction n with
  | zero => simpa using hesc
  | succ n ih =>
      have hstep := four_mul_escapePotential_le hS5 hright (s + n) (by omega)
      have hpow : (4 : ℤ) ^ (n + 1) = 4 * (4 : ℤ) ^ n := by ring
      have hgoal : s + (n + 1) = (s + n) + 1 := by ring
      rw [hgoal, hpow]
      omega

/-- The excess itself escapes: `9 * E (s + n) ≥ 4 ^ n + 6 * (s + n) + 2`. -/
theorem seamExcess_geom_lower
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (s : ℕ) (hs : S ≤ s) (hesc : 1 ≤ escapePotential s) (n : ℕ) :
    (4 : ℤ) ^ n + 6 * ((s : ℤ) + n) + 2 ≤ 9 * seamExcess (s + n) := by
  have h := escapePotential_geom hS5 hright s hs hesc n
  unfold escapePotential at h
  push_cast at h
  omega

/-- **No contradiction from the pulse cap after escape.** On the assumed
eventual right tail, once the barrier is crossed, at every later rank the exact
below-pulse is strictly too small to contradict next-step positivity. -/
theorem belowPulse_lt_of_escaped
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (s : ℕ) (hs : S ≤ s) (hesc : 1 ≤ escapePotential s) (n : ℕ) :
    ((seamAdjacentCut (s + n) (by omega : 5 ≤ s + n)).belowPulse : ℤ) + 4 <
      4 * seamExcess (s + n) := by
  have hlow := seamExcess_geom_lower hS5 hright s hs hesc n
  have hcap := belowPulse_add_four_le (by omega : 5 ≤ s + n)
  have hpow : (1 : ℤ) ≤ (4 : ℤ) ^ n := one_le_pow₀ (by norm_num)
  push_cast at hlow hcap ⊢
  omega

/-- **The non-escape band.** Under the explicit hypothesis that the potential
is never positive, the excess satisfies `3 * E s ≤ 2 * s` at every rank. -/
theorem band_of_never_escaping
    (S : ℕ) (hband : ∀ s : ℕ, S ≤ s → escapePotential s ≤ 0)
    (s : ℕ) (hs : S ≤ s) :
    3 * seamExcess s ≤ 2 * (s : ℤ) := by
  have h := hband s hs
  unfold escapePotential at h
  omega

/-- Under the right-tail hypothesis, at the selected rank the orbit is either
inside the linear band `3 * E ≤ 2 * s`, or its potential has escaped and grows
like `4 ^ n` at every later rank. -/
theorem escape_dichotomy
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (s : ℕ) (hs : S ≤ s) :
    3 * seamExcess s ≤ 2 * (s : ℤ) ∨
      ∀ n : ℕ, (4 : ℤ) ^ n ≤ escapePotential (s + n) := by
  by_cases hesc : 1 ≤ escapePotential s
  · exact Or.inr (escapePotential_geom hS5 hright s hs hesc)
  · left
    have h : escapePotential s ≤ 0 := by omega
    unfold escapePotential at h
    omega

/-! ## Part 2. Bounded-pulse ratchets do not recur above the threshold -/

/-- One step of a pulse-driven exclusion ratchet with pulse source `P`. The
state `b` is an upper bound for `3 * E s - 3`; `b = 0` is the absorbing dead
state. Its specialization to the local `pulseFloor` is definitionally equal
to `Recon257.ratchetStep`; see `ratchetStep_pulseFloor_eq_recon257`. -/
def ratchetStep (P : ℕ → ℕ) (s b : ℕ) : ℕ :=
  if 3 * P s + 4 ≤ 4 * b then 4 * b - (3 * P s + 3) else 0

/-- The orbit of the ratchet started at phase `t` with budget `b₀`. -/
def ratchetOrbit (P : ℕ → ℕ) (t b₀ : ℕ) : ℕ → ℕ
  | 0 => b₀
  | k + 1 => ratchetStep P (t + k) (ratchetOrbit P t b₀ k)

@[simp] theorem ratchetOrbit_zero (P : ℕ → ℕ) (t b₀ : ℕ) :
    ratchetOrbit P t b₀ 0 = b₀ := rfl

theorem ratchetOrbit_succ (P : ℕ → ℕ) (t b₀ k : ℕ) :
    ratchetOrbit P t b₀ (k + 1) =
      ratchetStep P (t + k) (ratchetOrbit P t b₀ k) := rfl

theorem ratchetStep_eq_of_le {P : ℕ → ℕ} {s b : ℕ} (h : 3 * P s + 4 ≤ 4 * b) :
    ratchetStep P s b = 4 * b - (3 * P s + 3) := by
  unfold ratchetStep
  rw [if_pos h]

/-- **The ratchet expands above the constant-pulse fixed point.** The map for
the constant pulse `P ≡ Q` fixes `Q + 1`. For any `P ≤ Q`, a budget
`b ≥ Q + 2` gains at least `3` in one step. -/
theorem ratchetStep_add_three_le
    {P : ℕ → ℕ} {Q : ℕ} (hQ : ∀ s, P s ≤ Q) (s b : ℕ) (hb : Q + 2 ≤ b) :
    b + 3 ≤ ratchetStep P s b := by
  have hp := hQ s
  unfold ratchetStep
  rw [if_pos (by omega)]
  omega

/-- An orbit starting at `b₀ ≥ Q + 2` never dies and gains at least `3` per
step. -/
theorem ratchetOrbit_strictMono
    {P : ℕ → ℕ} {Q : ℕ} (hQ : ∀ s, P s ≤ Q) (t b₀ : ℕ) (hb : Q + 2 ≤ b₀) :
    ∀ k : ℕ, b₀ + 3 * k ≤ ratchetOrbit P t b₀ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hge : Q + 2 ≤ ratchetOrbit P t b₀ k := by omega
      have hstep := ratchetStep_add_three_le hQ (t + k) _ hge
      rw [ratchetOrbit_succ]
      omega

/-- From `b₀ ≥ Q + 2`, the budget has the stated geometric lower bound. -/
theorem ratchetOrbit_geom
    {P : ℕ → ℕ} {Q : ℕ} (hQ : ∀ s, P s ≤ Q) (t b₀ : ℕ) (hb : Q + 2 ≤ b₀) :
    ∀ k : ℕ, 4 ^ k * (b₀ - (Q + 1)) + (Q + 1) ≤ ratchetOrbit P t b₀ k := by
  intro k
  induction k with
  | zero =>
      simp only [pow_zero, one_mul, ratchetOrbit_zero]
      omega
  | succ k ih =>
      have hmono := ratchetOrbit_strictMono hQ t b₀ hb k
      have hge : Q + 2 ≤ ratchetOrbit P t b₀ k := by omega
      have hp := hQ (t + k)
      have hval : ratchetOrbit P t b₀ (k + 1) =
          4 * ratchetOrbit P t b₀ k - (3 * P (t + k) + 3) := by
        rw [ratchetOrbit_succ, ratchetStep_eq_of_le (by omega)]
      have hpow : (4 : ℕ) ^ (k + 1) * (b₀ - (Q + 1)) =
          4 * (4 ^ k * (b₀ - (Q + 1))) := by ring
      rw [hval, hpow]
      omega

/-- **No recurrence above the threshold.** A state starting at
`b₀ ≥ Q + 2` cannot return to `b₀` at any positive depth. This theorem says
nothing about initial states `b₀ ≤ Q + 1`. -/
theorem ratchetOrbit_no_recurrence
    {P : ℕ → ℕ} {Q : ℕ} (hQ : ∀ s, P s ≤ Q) (t b₀ : ℕ) (hb : Q + 2 ≤ b₀)
    (k : ℕ) (hk : 0 < k) :
    ratchetOrbit P t b₀ k ≠ b₀ := by
  have h := ratchetOrbit_strictMono hQ t b₀ hb k
  omega

/-- More generally, an orbit starting at `b₀ ≥ Q + 2` is injective in depth. -/
theorem ratchetOrbit_injOn
    {P : ℕ → ℕ} {Q : ℕ} (hQ : ∀ s, P s ≤ Q) (t b₀ : ℕ) (hb : Q + 2 ≤ b₀)
    (j k : ℕ) (hjk : j < k) :
    ratchetOrbit P t b₀ j ≠ ratchetOrbit P t b₀ k := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt hjk
  have hbj : Q + 2 ≤ ratchetOrbit P t b₀ j := by
    have := ratchetOrbit_strictMono hQ t b₀ hb j
    omega
  have hshift : ∀ m : ℕ,
      ratchetOrbit P t b₀ (j + m) = ratchetOrbit P (t + j) (ratchetOrbit P t b₀ j) m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [show j + (m + 1) = (j + m) + 1 by ring, ratchetOrbit_succ,
          ratchetOrbit_succ, ih, show t + (j + m) = t + j + m by ring]
  have hgrow := ratchetOrbit_strictMono hQ (t + j) _ hbj (n + 1)
  have heq : ratchetOrbit P t b₀ k =
      ratchetOrbit P (t + j) (ratchetOrbit P t b₀ j) (n + 1) := by
    rw [show k = j + (n + 1) by omega]
    exact hshift (n + 1)
  rw [heq]
  omega

/-! ### A pointwise budget-side barrier, and a vacuous global formulation

`ratchetStep_expand_of_universal_cap` is a valid pointwise implication at any
row satisfying `P s + 4 ≤ 2 * s`. However, the hypothesis
`∀ s, P s + 4 ≤ 2 * s` in `ratchetOrbit_above_universal_barrier` is
unsatisfiable: at `s = 0` it requires `P 0 + 4 ≤ 0`. Consequently that orbit
theorem is vacuous as stated and supplies no information about any concrete
ratchet orbit. -/

theorem ratchetStep_expand_of_universal_cap
    {P : ℕ → ℕ} {s b : ℕ} (hcap : P s + 4 ≤ 2 * s) (hb : 2 * s ≤ b) :
    b + 3 ≤ ratchetStep P s b := by
  rw [ratchetStep_eq_of_le (by omega)]
  omega

/-- Under the unsatisfiable all-rows cap documented above, the displayed
budget lower bound propagates along the orbit. This theorem is vacuous as
stated. -/
theorem ratchetOrbit_above_universal_barrier
    {P : ℕ → ℕ} (hcap : ∀ s, P s + 4 ≤ 2 * s) (t b₀ : ℕ) (hb : 2 * t ≤ b₀) :
    ∀ k : ℕ, 2 * (t + k) + k ≤ ratchetOrbit P t b₀ k := by
  intro k
  induction k with
  | zero => simpa using hb
  | succ k ih =>
      have hstep := ratchetStep_expand_of_universal_cap (P := P) (s := t + k)
        (b := ratchetOrbit P t b₀ k) (hcap (t + k)) (by omega)
      rw [ratchetOrbit_succ]
      omega

/-! ### A local copy of the concrete rank-`26` pulse floor -/

/-- The row pulse of rank `d` at row `s`, in remainder form. This local copy
is linked to `Recon257.pulseAt` below. -/
def pulseAt (s d : ℕ) : ℕ :=
  (if (2 * s + 2) % d = 0 then 1 else 0) +
    2 * (if (2 * s + 1) % d = 0 then 1 else 0)

/-- The certified rank-`26` pulse-floor formula: the row-pulse contribution of
the eight forced greedy seam ranks `2, 3, 6, 7, 14, 20, 21, 26`. This local
copy is linked to `Recon257.pulseFloor` below. -/
def pulseFloor (s : ℕ) : ℕ :=
  pulseAt s 2 + pulseAt s 3 + pulseAt s 6 + pulseAt s 7 +
    pulseAt s 14 + pulseAt s 20 + pulseAt s 21 + pulseAt s 26

@[simp] theorem pulseAt_eq_recon257 (s d : ℕ) :
    pulseAt s d = Recon257.pulseAt s d := by
  rfl

@[simp] theorem pulseFloor_eq_recon257 (s : ℕ) :
    pulseFloor s = Recon257.pulseFloor s := by
  rfl

@[simp] theorem ratchetStep_pulseFloor_eq_recon257 (s b : ℕ) :
    ratchetStep pulseFloor s b = Recon257.ratchetStep s b := by
  rfl

/-- The generic orbit specialized to the local pulse floor is the concrete
`Recon257.ratchetRun`, with the same phase and initial budget. -/
theorem ratchetOrbit_pulseFloor_eq_recon257_ratchetRun (D k : ℕ) :
    ratchetOrbit pulseFloor (D + 1) 3 k = Recon257.ratchetRun D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [ratchetOrbit_succ, Recon257.ratchetRun_succ, ih,
        ratchetStep_pulseFloor_eq_recon257]

theorem pulseFloor_le_nine (s : ℕ) : pulseFloor s ≤ 9 := by
  have h2 : pulseAt s 2 = 1 := by unfold pulseAt; split_ifs <;> omega
  have h36 : pulseAt s 3 + pulseAt s 6 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h714 : pulseAt s 7 + pulseAt s 14 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h20 : pulseAt s 20 ≤ 1 := by unfold pulseAt; split_ifs <;> omega
  have h21 : pulseAt s 21 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h26 : pulseAt s 26 ≤ 1 := by unfold pulseAt; split_ifs <;> omega
  unfold pulseFloor
  omega

/-- Everything except the rank-`20` term contributes at most `8`. -/
theorem pulseFloor_le_eight_add_twenty (s : ℕ) :
    pulseFloor s ≤ 8 + pulseAt s 20 := by
  have h2 : pulseAt s 2 = 1 := by unfold pulseAt; split_ifs <;> omega
  have h36 : pulseAt s 3 + pulseAt s 6 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h714 : pulseAt s 7 + pulseAt s 14 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h21 : pulseAt s 21 ≤ 2 := by unfold pulseAt; split_ifs <;> omega
  have h26 : pulseAt s 26 ≤ 1 := by unfold pulseAt; split_ifs <;> omega
  unfold pulseFloor
  omega

/-- The rank-`20` term needs `10 ∣ s + 1`, so it cannot fire twice in a row. -/
theorem pulseAt_twenty_two_step (s : ℕ) :
    pulseAt s 20 + pulseAt (s + 1) 20 ≤ 1 := by
  unfold pulseAt
  split_ifs <;> omega

/-- Hence the forced pulse floor cannot be maximal twice in a row. -/
theorem pulseFloor_two_step_le (s : ℕ) :
    pulseFloor s + pulseFloor (s + 1) ≤ 17 := by
  have h1 := pulseFloor_le_eight_add_twenty s
  have h2 := pulseFloor_le_eight_add_twenty (s + 1)
  have h3 := pulseAt_twenty_two_step s
  omega

/-- **The local threshold state grows over two steps.** `b = 10` is the fixed
point of the constant pulse `P ≡ 9`. Because the local `pulseFloor` cannot be
`9` twice in a row, two steps from any `b ≥ 10` end at least `3` above `b`.
This excludes recurrence for such two-step blocks; it does not analyze initial
budgets `1, …, 9`. -/
theorem pulseFloor_ratchet_escape_from_ten (s b : ℕ) (hb : 10 ≤ b) :
    b + 3 ≤ ratchetStep pulseFloor (s + 1) (ratchetStep pulseFloor s b) := by
  have hp := pulseFloor_two_step_le s
  have hp1 := pulseFloor_le_nine s
  have hp2 := pulseFloor_le_nine (s + 1)
  have h1 : ratchetStep pulseFloor s b = 4 * b - (3 * pulseFloor s + 3) :=
    ratchetStep_eq_of_le (by omega)
  have h1' : 10 ≤ ratchetStep pulseFloor s b := by rw [h1]; omega
  have h2 : ratchetStep pulseFloor (s + 1) (ratchetStep pulseFloor s b) =
      4 * ratchetStep pulseFloor s b - (3 * pulseFloor (s + 1) + 3) :=
    ratchetStep_eq_of_le (by omega)
  rw [h2, h1]
  omega

/-- Iterating: from any initial budget at least `10`, the local rank-`26`
ratchet is unbounded along its even-depth subsequence, gaining at least `3`
every two steps. -/
theorem pulseFloor_ratchetOrbit_unbounded
    (t b₀ : ℕ) (hb : 10 ≤ b₀) :
    ∀ n : ℕ, b₀ + 3 * n ≤ ratchetOrbit pulseFloor t b₀ (2 * n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := pulseFloor_ratchet_escape_from_ten (t + 2 * n)
        (ratchetOrbit pulseFloor t b₀ (2 * n)) (by omega)
      have hval : ratchetOrbit pulseFloor t b₀ (2 * (n + 1)) =
          ratchetStep pulseFloor (t + 2 * n + 1)
            (ratchetStep pulseFloor (t + 2 * n)
              (ratchetOrbit pulseFloor t b₀ (2 * n))) := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, ratchetOrbit_succ,
          ratchetOrbit_succ, show t + (2 * n + 1) = t + 2 * n + 1 by ring]
      rw [hval]
      omega

end AngleB3

end Erdos249257
