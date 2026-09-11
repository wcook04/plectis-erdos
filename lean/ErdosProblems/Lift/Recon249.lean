/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.CarrySurvivorExtinction

/-!
# Reconnaissance for one coefficientwise #249 lift route

`DemandLedger.Discharge1G097.exists_diagonalKill_le_66` certifies every scale
`t ≤ 66` of the lcm ray `H t = periodLcm t = lcm (1, …, t)`, and
`irrational_totient_series_of_lcm_diagonal_certificate_supply` turns a cofinal
supply of diagonal kills into Erdős #249.  One proposed way to extend the
finite band is a **lift**

  `certifiedKill H H L → ∃ L', certifiedKill (p * H) (p * H) L'`

at each prime-power boundary, where the multiplier `p` is a prime.  This file
does not prove that lift.  It pins down, with kernel-checked statements, the
arithmetic seen by one coefficientwise approach, and it records a counterexample
to one coefficient-scaling guess.

**Current corpus status.**  This is a reconnaissance file about the older
`t ≤ 66` tranche, not the current certificate frontier.  Later modules prove
`ErdosProblems.Lift.certifiedKill_diagonal_t67` at depth `100` and
`ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82`.  Those are finite certificates;
they do not supply the cofinal lift required for #249.

## The diagonal window

At the diagonal the discrepancy is a weighted sum of the coefficients

  `c_H(d) = φ(2H + d) − φ(H + d)`,   `windowDiscrepancy H H L = ∑_{d=1}^{L} c_H(d) · 2^{L-d}`

(`diagCoeff`, `windowDiscrepancy_diagonal`).

## Result 1 (PROVED): termwise congruence is sufficient for residue agreement

`windowDiscrepancy_sub_dvd` / `certifiedKill_transfer`: if two cells have
coefficients agreeing `2`-adically to depth `d` at every position `d`, and the
target cell's exclusion radius is no larger, the certificate transfers.
The radius inequality points from a larger cell to a smaller cell.  It is false
in the desired upward direction `H → pH` for `p ≥ 2`, as proved explicitly by
`transfer_direction_blocks_lift` in `ErdosProblems/Lift/verify/Check12.lean`.
Thus this transfer lemma
does not itself implement a lift.

For this sufficient, coefficientwise route, the relevant data are the residues

  `c_{pH}(d) mod 2^d`,  `d = 1, …, L'`.

The theorems do not prove that every possible lift argument must determine
those residues separately, nor that the stated congruences are necessary.

## Result 2 (PROVED theorem, MEASURED comparison): a scale-invariant factor

`factorization_window`: for every prime `q`, every `m ≥ 1` and every `d` with
`v_q(d) < v_q(H)`, one has `v_q(m·H + d) = v_q(d)`.  Hence the `q`-part of every
window element is a function of the offset `d` alone, identical at `H`, at `2H`,
at `pH`, at `2pH`, and at every higher rung of the ladder
(`factorization_window_ladder`).  The window's smooth core is rigid.

**MEASURED on the recorded sample.**  The invariant part of
`c_H(d)` is `φ` of the rigid core; over `d = 1, …, 14` its 2-adic valuation is
the list `[0,0,1,1,2,1,1,2,1,2,0,2,0,1]` — identical at `t = 53, 59, 61, 64`, as
Result 2 forces — while the *observed* `v₂(c_H(d))` at those same scales ranges
over `2 … 10` with no pattern and no agreement between scales.  Over that range
the rigid-core valuation is at most `2`.  This finite comparison is not a
theorem that no argument can use the rigid factor more effectively.

## Result 3 (PROVED identities): exact formulas with side conditions

`diagCoeff_lift_coprime` / `diagCoeff_lift_dvd`: for `p` prime,

  `c_{pH}(p·e) = (p−1) · c_H(e)`  when `p ∤ H+e` and `p ∤ 2H+e`,
  `c_{pH}(p·e) = p · c_H(e)`      when `p ∣ H+e` and `p ∣ 2H+e`.

This is exact, not asymptotic.  (As corroboration it was also checked
numerically against the recorded totients of all 27 consecutive lift pairs in
the corpus, `t = 1→2→…→61→64`, at every offset of every window: no exceptions.)

Each identity concerns only offsets divisible by `p`, and it maps old offset `e` to
new offset `p·e` — a dilation of the base-2 place value, not a shift.  The
number of candidate offsets in an `L'`-deep window is exactly `⌊L'/p⌋`
(`lift_covered_card`); the number of offsets not divisible by `p` is
`L' − ⌊L'/p⌋` (`uncoveredOffsets_card`).  These cardinality theorems do not
discharge either identity's divisibility hypotheses.  At a prime frontier the
divisible branch is impossible: its two hypotheses imply `p ∣ H`
(`dvd_branch_needs_p_dvd_H` in `ErdosProblems/Lift/verify/Check12.lean`),
whereas the new frontier prime
does not divide the preceding lcm.

At the historical `t = 67` test cell, `H₆₇ = 67·H₆₆`;
`certifiedKill_periodLcm_67_depth` shows any certificate needs `L ≥ 98`.
`lift_coverage_at_67` counts one divisible offset among the first `98`, and
`lift_law_fires_at_67` in `ErdosProblems/Lift/verify/Check12.lean` separately
verifies the coprime side conditions for that offset.  `uncovered_at_67` counts the other `97`
offsets, to which neither exact identity applies.  Later work certifies this
cell directly at the minimal depth `100`; it does not derive that certificate
from the lift identities here.

## Result 4 (PROVED bounds, MEASURED sample): mandatory depth

`diagonal_depth_floor` : `certifiedKill H H L → 4H < 2^L`.  So `L ≥ log₂(4H)`
is mandatory, and depth is forced to grow along the ladder.

`lift_depth_floor_growth` (unconditional): `p ≥ 2^k`, `H ≥ 1` and a certificate
at `p·H` force `L' > log₂ H + k + 2`.  At the frontier (`H = H₆₆`,
`Nat.log 2 H₆₆ = 89`, `p = 67 ≥ 2^6`) this returns the necessary bound
`L' ≥ 98`.  It does not prove existence at depth `98`; later modules prove
depths `98` and `99` fail and depth `100` succeeds.

`lift_depth_growth` (relative): if the certificate at `H` is floor-tight
(`2^L ≤ 8H`) then `L + k ≤ L'`.  **MEASURED on the historical 28-deposit
sample:** only `6` deposits are floor-tight in that sense —

  measured minimal depths `L_t` vs the floor `⌈log₂(4H_t)⌉`, over the 28
  deposits, have excess `0` (×9), `1` (×11), `2` (×4), `3` (×3), `4` (×1);

and in every one of the 28 cases the *recorded* depth is the *minimal* depth
that works.  The relative theorem gives a `k`-bit increment only under its
floor-tightness hypothesis.  The unconditional theorem gives an absolute
lower bound in terms of `H` and `k`, not a lower bound on `L' - L`.

At `t = 67` this bites hard.  At the floor `L = 98` the admissible residue arc
has length `65125117500982681130892344` inside `2^98`
(`periodLcm_67_depth98_margin`) — relative width `≈ 2.06 × 10⁻⁴`.
The theorem computes this width; it makes no probabilistic claim.  Later
kernel-checked results show that depths `98` and `99` fail and `100` succeeds.

## Result 5 (PROVED): a counterexample to a coefficient-scaling guess

The guess `c_{pH}(d) ≡ p · c_H(d) (mod 2^d)` is **false at `d = 4`** already for the
easiest lift in the corpus, `H₆₁ → H₆₄ = 2·H₆₁`
(`natural_lift_guess_fails_at_four`).  The difference has 2-adic valuation
exactly `3`.  This scaled congruence is not the hypothesis of
`certifiedKill_transfer`, which instead compares `c_new(d)` directly with
`c_old(d)` and also has the wrong radius direction for an upward lift.
Multiplication does not preserve the excluded residue arc; see
`scaling_does_not_preserve_the_arc` in
`ErdosProblems/Lift/verify/Check12.lean`.  And
`diagCoeff_t64_four_eq` shows what is true instead: new position `4` is governed
by old position **`2`**, not old position `4`.

**MEASURED:** across all 27 historical corpus lift pairs the guess dies at
`d ∈ {2,…,6}` — always inside
the first six of the ~`L` positions it would have to survive.

## Result 6 (PROVED recurrence, MEASURED corpus usage): the base parameter

`irrational_totient_series_of_lcm_certificate_supply` asks for
`certifiedKill (periodLcm t) N L` at **some** large `N` — the diagonal
`N = periodLcm t` is a choice, not a requirement, and it is the only choice any
of the 28 deposits makes.  `windowDiscrepancy_shift` /
`windowDiscrepancy_shift_emod` give the exact affine recurrence along that
unused parameter:

  `A_{h,N+1,L} = 2·A_{h,N,L} − c(1)·2^L + c(L+1)`,
  `A_{h,N+1,L} ≡ 2·A_{h,N,L} + c(L+1)  (mod 2^L)`,  `c(d) = φ(N+h+d) − φ(N+d)`.

One new totient pair enters per step, against `2L` totient terms in the
definition of a fresh window.  The recurrence does not remove the need for
cofinally many `t`; it only supplies an exact way to update the discrepancy at
fixed `h` and `L`.

## What the coefficientwise route would still require

For a proof that uses the sufficient termwise-congruence route of Result 1, a lift

  `certifiedKill H H L → ∃ L', certifiedKill (pH) (pH) L'`,  `p` prime, `p > t`

would need, for some depth satisfying the proved lower bound, control of the
weighted sum of the `L'` residues

  `(φ(2pH + d) − φ(pH + d)) mod 2^d`,  `d = 1, …, L'`,

so that `∑_d c(d)·2^{L'-d}` avoids the arc of
half-width `2pH + L' + 2` about `0` mod `2^{L'}`.  Of those `L'` residues:

* `⌊L'/p⌋` positions are divisible by `p` and are candidates for the identities
  in Result 3; an application still has to prove the relevant side conditions;
* the remaining `L' − ⌊L'/p⌋` positions are not addressed by those identities;
* Result 2 proves valuation control for the rigid `q`-part.  The claim that this
  yields little coefficient information is supported here only by the finite
  measurement at `t = 53, 59, 61, 64`, not by a general impossibility theorem.

For the first `98` positions at `t = 67`, the count is one divisible position
whose coprime side conditions are separately verified, and `97` positions not
covered by these identities.  This file supplies no upward certificate-transfer
theorem from `H₆₆` to `H₆₇`.  The corpus now supplies a direct certificate at
`t = 67` and an unbroken finite band through `t = 82`, but no cofinal lift; Erdős
#249 remains open.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace ErdosProblems
namespace Lift
namespace Recon249

set_option maxRecDepth 100000

/-! ## The diagonal window written out -/

/-- The diagonal window coefficient at offset `d`:
`c_H(d) = φ(2H + d) − φ(H + d)`. -/
def diagCoeff (H d : ℕ) : ℤ :=
  (Nat.totient (2 * H + d) : ℤ) - (Nat.totient (H + d) : ℤ)

/-- **The diagonal discrepancy in offset form.**
`windowDiscrepancy H H L = ∑_{j<L} c_H(j+1) · 2^{L-1-j}`, i.e. the offsets run
over `d = 1, …, L` with place value `2^{L-d}`. -/
theorem windowDiscrepancy_diagonal (H L : ℕ) :
    windowDiscrepancy H H L
      = ∑ j ∈ Finset.range L, diagCoeff H (j + 1) * 2 ^ (L - 1 - j) := by
  unfold windowDiscrepancy diagCoeff
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : H + H + 1 + j = 2 * H + (j + 1) := by omega
  have h2 : H + 1 + j = H + (j + 1) := by omega
  rw [h1, h2]

/-! ## Result 1: the certificate reads only `c_H(d) mod 2^d` -/

/-- **2-adic sensitivity of the window discrepancy.**  If at every position
`j < L` the two cells' coefficients agree modulo `2^{j+1}`, then the two window
discrepancies agree modulo `2^L`.

Position `j` carries place value `2^{L-1-j}`, so it needs only `j+1` bits of its
coefficient to establish this sufficient congruence.  The theorem does not say
that a lift must establish these congruences term by term, or that they are
necessary for a certificate. -/
theorem windowDiscrepancy_sub_dvd {h N h' N' L : ℕ}
    (hc : ∀ j < L, (2 : ℤ) ^ (j + 1) ∣
      (((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ))
        - ((Nat.totient (N' + h' + 1 + j) : ℤ) - (Nat.totient (N' + 1 + j) : ℤ)))) :
    (2 : ℤ) ^ L ∣ windowDiscrepancy h N L - windowDiscrepancy h' N' L := by
  unfold windowDiscrepancy
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j hj => ?_
  have hjL : j < L := Finset.mem_range.mp hj
  have hsplit : (2 : ℤ) ^ L = 2 ^ (j + 1) * 2 ^ (L - 1 - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hexp :
      ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
        - ((Nat.totient (N' + h' + 1 + j) : ℤ) - (Nat.totient (N' + 1 + j) : ℤ))
            * 2 ^ (L - 1 - j)
      = (((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ))
          - ((Nat.totient (N' + h' + 1 + j) : ℤ) - (Nat.totient (N' + 1 + j) : ℤ)))
          * 2 ^ (L - 1 - j) := by ring
  rw [hexp, hsplit]
  exact mul_dvd_mul_right (hc j hjL) _

/-- **A certificate transfers toward a no-larger exclusion radius.**  Agreement
of every coefficient `c(d)` modulo `2^d`, together with `N' + h' ≤ N + h`,
carries `certifiedKill h N L` to `certifiedKill h' N' L`.

For the desired upward scaling from `(H,H)` to `(pH,pH)`, `p ≥ 2`, this radius
inequality points the wrong way.  The theorem is therefore not an upward lift. -/
theorem certifiedKill_transfer {h N h' N' L : ℕ}
    (hle : N' + h' ≤ N + h)
    (hc : ∀ j < L, (2 : ℤ) ^ (j + 1) ∣
      (((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ))
        - ((Nat.totient (N' + h' + 1 + j) : ℤ) - (Nat.totient (N' + 1 + j) : ℤ))))
    (hcert : certifiedKill h N L) : certifiedKill h' N' L := by
  have hdvd := windowDiscrepancy_sub_dvd (h := h) (N := N) (h' := h') (N' := N') (L := L) hc
  have hmod : windowDiscrepancy h N L % 2 ^ L = windowDiscrepancy h' N' L % 2 ^ L :=
    (Int.modEq_iff_dvd.mpr hdvd).symm
  obtain ⟨hl, hr⟩ := hcert
  have hcast : (N' + h' : ℤ) ≤ (N + h : ℤ) := by exact_mod_cast hle
  constructor
  · rw [← hmod]
    push_cast at hcast
    linarith
  · rw [← hmod]
    push_cast at hcast
    linarith

/-! ## Result 2: the scale-invariant core of the window -/

/-- The offset is all the window sees of the modulus: `gcd(m·H + d, H) = gcd(d, H)`.
For `d ≤ t` and `H = periodLcm t` this is `d` itself, at every `m` and every
rung of the ladder. -/
theorem gcd_window (m H d : ℕ) : Nat.gcd (m * H + d) H = Nat.gcd d H := by
  have hrw : m * H + d = d + H * m := by ring
  rw [hrw, Nat.gcd_add_mul_left_left]

/-- **The rigid part of the window.**  If `v_q(d) < v_q(H)` then
`v_q(m·H + d) = v_q(d)` for every `m ≥ 1`.

Consequence: for `H = periodLcm t`, every prime `q ≤ t` and every offset `d`
whose `q`-exponent is below `H`'s, the `q`-part of the window element `m·H + d`
is `q^{v_q(d)}` — determined by `d` alone, with no reference to the scale. -/
theorem factorization_window {q m H d : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hd : d ≠ 0)
    (hlt : d.factorization q < H.factorization q) :
    (m * H + d).factorization q = d.factorization q := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hlt
  have hn : m * H + d ≠ 0 := by positivity
  set a := d.factorization q with ha
  -- `q ^ (a+1)` divides `m * H`
  have hHdvd : q ^ (a + 1) ∣ m * H := by
    refine Dvd.dvd.mul_left ?_ m
    exact (Nat.Prime.pow_dvd_iff_le_factorization hq hH).mpr (by omega)
  -- `q ^ a` divides `d`
  have hdd : q ^ a ∣ d := Nat.ordProj_dvd d q
  have hdvd : q ^ a ∣ m * H + d :=
    Nat.dvd_add (dvd_trans (pow_dvd_pow q (by omega)) hHdvd) hdd
  have hle : a ≤ (m * H + d).factorization q :=
    (Nat.Prime.pow_dvd_iff_le_factorization hq hn).mp hdvd
  have hnot : ¬ q ^ (a + 1) ∣ m * H + d := by
    intro hcon
    have hdd' : q ^ (a + 1) ∣ d := (Nat.dvd_add_right hHdvd).mp hcon
    exact absurd ((Nat.Prime.pow_dvd_iff_le_factorization hq hd).mp hdd') (by omega)
  have hlt' : (m * H + d).factorization q < a + 1 := by
    by_contra hcon
    exact hnot ((Nat.Prime.pow_dvd_iff_le_factorization hq hn).mpr (by omega))
  omega

/-- **Ladder invariance.**  The rigid part does not merely survive one step: it
is the same at every rung above `H`.  If `H ∣ H'` and `v_q(d) < v_q(H)`, then
`v_q(m·H' + d) = v_q(d)` for all `m ≥ 1`.  In particular the `q`-parts at
`H, 2H, pH, 2pH, pqH, …` all coincide with the `q`-part of `d`. -/
theorem factorization_window_ladder {q m H H' d : ℕ} (hq : q.Prime) (hm : m ≠ 0)
    (hd : d ≠ 0) (hH' : H' ≠ 0) (hdvd : H ∣ H')
    (hlt : d.factorization q < H.factorization q) :
    (m * H' + d).factorization q = d.factorization q := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hlt
  have hmono : H.factorization q ≤ H'.factorization q :=
    (Nat.factorization_le_iff_dvd hH hH').mpr hdvd q
  exact factorization_window hq hm hd (lt_of_lt_of_le hlt hmono)

/-! ## Result 3: exact coefficient identities and their candidate offsets -/

/-- **Exact lift law, coprime case.**  For `p` prime with `p ∤ H+e` and
`p ∤ 2H+e`, the lifted coefficient at offset `p·e` is `(p−1)` times the old
coefficient at offset `e`.

Note what this does *not* say: it relates new offset `p·e` to old offset `e`.
The place value moves from `2^{L-e}` to `2^{L'-p·e}`, so the lift dilates the
window rather than translating it. -/
theorem diagCoeff_lift_coprime {p H e : ℕ} (hp : p.Prime)
    (h1 : ¬ p ∣ (H + e)) (h2 : ¬ p ∣ (2 * H + e)) :
    diagCoeff (p * H) (p * e) = ((p : ℤ) - 1) * diagCoeff H e := by
  unfold diagCoeff
  have e1 : 2 * (p * H) + p * e = p * (2 * H + e) := by ring
  have e2 : p * H + p * e = p * (H + e) := by ring
  rw [e1, e2]
  rw [Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hp).mpr h2),
      Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1),
      Nat.totient_prime hp]
  have hp1 : (1 : ℕ) ≤ p := hp.one_lt.le
  push_cast [hp1]
  ring

/-- **Exact lift law, divisible case.**  For `p` prime with `p ∣ H+e` and
`p ∣ 2H+e`, the lifted coefficient at offset `p·e` is `p` times the old
coefficient at offset `e`. -/
theorem diagCoeff_lift_dvd {p H e : ℕ} (hp : p.Prime)
    (h1 : p ∣ (H + e)) (h2 : p ∣ (2 * H + e)) :
    diagCoeff (p * H) (p * e) = (p : ℤ) * diagCoeff H e := by
  unfold diagCoeff
  have e1 : 2 * (p * H) + p * e = p * (2 * H + e) := by ring
  have e2 : p * H + p * e = p * (H + e) := by ring
  rw [e1, e2, Nat.totient_mul_of_prime_of_dvd hp h2,
      Nat.totient_mul_of_prime_of_dvd hp h1]
  push_cast
  ring

/-- The doubling lift at an even offset: new offset `2e` is `2 ×` old offset `e`. -/
theorem diagCoeff_double_even {H e : ℕ} (hH : 2 ∣ H) (he : 2 ∣ e) :
    diagCoeff (2 * H) (2 * e) = 2 * diagCoeff H e := by
  have h1 : (2 : ℕ) ∣ (H + e) := Nat.dvd_add hH he
  have h2 : (2 : ℕ) ∣ (2 * H + e) := Nat.dvd_add ⟨H, rfl⟩ he
  have := diagCoeff_lift_dvd (p := 2) (H := H) (e := e) Nat.prime_two h1 h2
  simpa using this

/-- The doubling lift at an odd offset: new offset `2e` *equals* old offset `e`. -/
theorem diagCoeff_double_odd {H e : ℕ} (hH : 2 ∣ H) (he : ¬ 2 ∣ e) :
    diagCoeff (2 * H) (2 * e) = diagCoeff H e := by
  have h1 : ¬ (2 : ℕ) ∣ (H + e) := by
    intro hcon
    exact he ((Nat.dvd_add_right hH).mp hcon)
  have h2 : ¬ (2 : ℕ) ∣ (2 * H + e) := by
    intro hcon
    exact he ((Nat.dvd_add_right ⟨H, rfl⟩).mp hcon)
  have := diagCoeff_lift_coprime (p := 2) (H := H) (e := e) Nat.prime_two h1 h2
  simpa using this

/-- **Count of candidate offsets for the exact identities.**  Of the `L'`
offsets `1, …, L'` in the lifted window, exactly `⌊L'/p⌋` are multiples of `p`.
Only such offsets can have the form `p·e`.  This cardinality theorem does not
prove the divisibility hypotheses of either coefficient identity. -/
theorem lift_covered_card (p L' : ℕ) :
    ((Finset.Ioc 0 L').filter (fun d => p ∣ d)).card = L' / p :=
  Nat.Ioc_filter_dvd_card_eq_div L' p

/-- The offsets of an `L'`-deep lifted window that the exact lift law does
**not** address: those not divisible by `p`.  Along the coefficientwise route,
each such position contributes `c_{pH}(d) mod 2^d`; this file proves no formula
for it from the lower cell.  No independence claim is made. -/
def uncoveredOffsets (p L' : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 L').filter (fun d => ¬ p ∣ d)

/-- **Count of offsets outside the identities' domain.**  There are
`L' − ⌊L'/p⌋` offsets not divisible by `p`. -/
theorem uncoveredOffsets_card (p L' : ℕ) :
    (uncoveredOffsets p L').card = L' - L' / p := by
  have hsplit :
      ((Finset.Ioc 0 L').filter (fun d => p ∣ d)).card
        + ((Finset.Ioc 0 L').filter (fun d => ¬ p ∣ d)).card = (Finset.Ioc 0 L').card :=
    Finset.card_filter_add_card_filter_not _
  rw [lift_covered_card] at hsplit
  have hcard : (Finset.Ioc 0 L').card = L' := by simp
  rw [hcard] at hsplit
  unfold uncoveredOffsets
  omega

/-! ## Result 4: the mandatory depth floor and its growth under the lift -/

/-- **Diagonal depth floor.**  A diagonal certificate at height `H` cannot be
shallower than `log₂(4H)`: the two excluded arcs must fit inside the circle. -/
theorem diagonal_depth_floor {H L : ℕ} (hcert : certifiedKill H H L) :
    (4 * H : ℤ) < 2 ^ L := by
  have h := certifiedKill_depth_floor hcert
  push_cast at h ⊢
  linarith

/-- **The lift must buy depth.**  If the certificate at `H` is floor-tight
(`2^L ≤ 8H`, i.e. at most one bit above the mandatory floor) and `p` is at least
`2^k`, then any certificate at `p·H` has depth at least `L + k`.

Under the stated floor-tightness hypothesis this gives a relative increment of
at least `k` bits.  Without that hypothesis, use `lift_depth_floor_growth`
below; this theorem alone does not give an unconditional bound on `L' - L`.
The `0 … 4` excess in the historical 28-deposit sample is MEASURED. -/
theorem lift_depth_growth {p H L L' k : ℕ} (hpk : 2 ^ k ≤ p)
    (htight : (2 : ℤ) ^ L ≤ 8 * H)
    (hcert : certifiedKill (p * H) (p * H) L') :
    L + k ≤ L' := by
  have hfloor : (4 * (p * H) : ℤ) < 2 ^ L' := diagonal_depth_floor hcert
  have hpk' : (2 : ℤ) ^ k ≤ (p : ℤ) := by exact_mod_cast hpk
  have hH0 : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg H
  have hstep : (2 : ℤ) ^ (L + k) ≤ 8 * (p * H) := by
    rw [pow_add]
    calc (2 : ℤ) ^ L * 2 ^ k ≤ (8 * H) * 2 ^ k := by
            exact mul_le_mul_of_nonneg_right htight (by positivity)
      _ ≤ (8 * H) * (p : ℤ) := by
            exact mul_le_mul_of_nonneg_left hpk' (by linarith)
      _ = 8 * ((p : ℤ) * H) := by ring

  have hlt : (2 : ℤ) ^ (L + k) < 2 ^ (L' + 1) := by
    calc (2 : ℤ) ^ (L + k) ≤ 8 * ((p : ℤ) * H) := by exact_mod_cast hstep
      _ = 2 * (4 * ((p : ℤ) * H)) := by ring
      _ < 2 * 2 ^ L' := by
            linarith
      _ = 2 ^ (L' + 1) := by ring
  have := (pow_lt_pow_iff_right₀ (a := (2 : ℤ)) (by norm_num)).mp hlt
  omega

/-- **Unconditional depth growth.**  No tightness hypothesis: for `p ≥ 2^k` and
`H ≥ 1`, every certificate at the lifted cell `p·H` has depth strictly greater
than `log₂ H + k + 2`.

This avoids the tightness hypothesis used in `lift_depth_growth`.  With
`H = H₆₆` (`Nat.log 2 H₆₆ = 89`) and `p = 67 ≥ 2^6`, it returns the necessary
bound `L' ≥ 98`, the same lower bound as
`certifiedKill_periodLcm_67_depth`.  It does not prove a certificate exists at
that depth. -/
theorem lift_depth_floor_growth {p H L' k : ℕ} (hpk : 2 ^ k ≤ p) (hH : H ≠ 0)
    (hcert : certifiedKill (p * H) (p * H) L') :
    Nat.log 2 H + k + 2 < L' := by
  have hfloorZ : (4 * (p * H) : ℤ) < 2 ^ L' := diagonal_depth_floor hcert
  have hfloor : 4 * (p * H) < 2 ^ L' := by exact_mod_cast hfloorZ
  have hlog : 2 ^ (Nat.log 2 H) ≤ H := Nat.pow_log_le_self 2 hH
  have hchain : 2 ^ (Nat.log 2 H + k + 2) ≤ 4 * (p * H) := by
    have : 2 ^ (Nat.log 2 H + k + 2) = 4 * (2 ^ k * 2 ^ (Nat.log 2 H)) := by
      rw [pow_add, pow_add]
      ring
    rw [this]
    exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul hpk hlog)
  have : (2 : ℕ) ^ (Nat.log 2 H + k + 2) < 2 ^ L' := lt_of_le_of_lt hchain hfloor
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this

/-! ## A historical test cell beyond the original band: `t = 67`

Later modules certify this cell at minimal depth `100`; the results below are
necessary bounds and counts used in the earlier reconnaissance.
-/

/-- `H₆₆ = lcm(1,…,66)`. -/
theorem periodLcm_66_val : periodLcm 66 = 1182266884102822267511361600 := by decide

/-- `H₆₇ = 67 · H₆₆`: the ladder multiplier at the frontier is the prime `67`. -/
theorem periodLcm_67_val : periodLcm 67 = 79211881234889091923261227200 := by decide

/-- `H₆₇ = 67 · H₆₆`, in the shape the lift consumes. -/
theorem periodLcm_67_eq_mul : periodLcm 67 = 67 * periodLcm 66 := by
  rw [periodLcm_66_val, periodLcm_67_val]

/-- `log₂ H₆₆ = 89`. -/
theorem log2_periodLcm_66 : Nat.log 2 (periodLcm 66) = 89 := by
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_ <;> rw [periodLcm_66_val] <;> norm_num

/-- **A necessary depth bound at `t = 67`.**  Any diagonal certificate at
`t = 67` has depth at least `98`.  The definition of a depth-`98` discrepancy
contains `196` totient terms, but this theorem does not prescribe factorisation
as the only possible proof method. -/
theorem certifiedKill_periodLcm_67_depth {L : ℕ}
    (hcert : certifiedKill (periodLcm 67) (periodLcm 67) L) : 98 ≤ L := by
  by_contra hcon
  have hL : L ≤ 97 := by omega
  have hfloor : (4 * (periodLcm 67 : ℤ)) < 2 ^ L := diagonal_depth_floor hcert
  have hmono : (2 : ℤ) ^ L ≤ 2 ^ 97 :=
    pow_le_pow_right₀ (by norm_num) hL
  rw [periodLcm_67_val] at hfloor
  norm_num at hfloor
  linarith

/-- **The general growth law recovers the direct lower bound.**  Instantiating
`lift_depth_floor_growth` at `H = H₆₆`, `k = 6` (`2^6 = 64 ≤ 67`) reproduces the
necessary depth bound `98` obtained above by direct evaluation of `H₆₇`.
Neither theorem proves existence at `98`; later results prove the minimal depth
is `100`. -/
theorem certifiedKill_periodLcm_67_depth_via_growth {L : ℕ}
    (hcert : certifiedKill (periodLcm 67) (periodLcm 67) L) : 98 ≤ L := by
  rw [periodLcm_67_eq_mul] at hcert
  have h66 : periodLcm 66 ≠ 0 := by rw [periodLcm_66_val]; norm_num
  have hgrow := lift_depth_floor_growth (p := 67) (H := periodLcm 66) (k := 6)
    (by norm_num) h66 hcert
  rw [log2_periodLcm_66] at hgrow
  omega

/-- **The depth-98 admissible interval size.**  At the mandatory floor `L = 98` the
admissible residue interval has length `65125117500982681130892344` inside a
circle of size `2^98 = 316912650057057350374175801344` — a relative width of
about `2.06 × 10⁻⁴`.  This is an exact arithmetic identity followed by a
decimal approximation, not a probability estimate or an existence result. -/
theorem periodLcm_67_depth98_margin :
    (2 : ℤ) ^ 98 - 2 * ((periodLcm 67 : ℤ) + (periodLcm 67 : ℤ) + 98 + 2)
      = 65125117500982681130892344 := by
  rw [periodLcm_67_val]
  norm_num

/-- **Candidate-offset count at `t = 67`.**  At `p = 67`, exactly one of the
first `98` offsets is divisible by `p`: `d = 67`.  This theorem proves only the
count.  `lift_law_fires_at_67` in `ErdosProblems/Lift/verify/Check12.lean`
separately verifies the coprime identity's side conditions for the
corresponding old offset `e = 1`. -/
theorem lift_coverage_at_67 :
    ((Finset.Ioc 0 98).filter (fun d => 67 ∣ d)).card = 1 := by
  rw [lift_covered_card]

/-- **Offsets outside the exact identities, counted.**  `97` of the first `98`
offsets at `t = 67` are not divisible by `67`, so neither coefficient identity
in this file applies to them. -/
theorem uncovered_at_67 : (uncoveredOffsets 67 98).card = 97 := by
  rw [uncoveredOffsets_card]

/-! ## Result 5: the smallest explicit counterexample to the natural guess -/

/-- `H₆₄ = 2 · H₆₁`: the easiest lift in the corpus. -/
theorem periodLcm_64_eq_two_mul_periodLcm_61 :
    periodLcm 64 = 2 * periodLcm 61 := by decide

/-- `H₆₁` is even. -/
theorem two_dvd_periodLcm_61 : 2 ∣ periodLcm 61 := by decide

/-- **What the lift actually controls at offset 4.**  Kernel-checked with no
totient evaluation whatsoever: at the lift `H₆₁ → H₆₄ = 2·H₆₁`, the new window's
offset-`4` coefficient is twice the *old window's offset-`2`* coefficient.

This is the dilation, made concrete.  The naive guess would relate new offset
`4` to old offset `4`; the truth relates it to old offset `2`, whose place value
in the old certificate was `2^{L-2}`, not `2^{L-4}`. -/
theorem diagCoeff_t64_four_eq :
    diagCoeff (periodLcm 64) 4 = 2 * diagCoeff (periodLcm 61) 2 := by
  have h4 : (4 : ℕ) = 2 * 2 := by norm_num
  rw [periodLcm_64_eq_two_mul_periodLcm_61, h4]
  exact diagCoeff_double_even two_dvd_periodLcm_61 ⟨1, rfl⟩

/-- **The natural guess dies at offset 4.**  Hypotheses `h1`–`h3` are the three
Euler totients recorded (kernel-checked, via Pratt certificates) in
`DiagonalPincerCertificatesT61` and `DiagonalPincerCertificatesT64`; note that
`H₆₄ + 4 = 2·H₆₁ + 4`, so the two windows share the value in `h2`.

Given them, the guess `c_{2H}(d) ≡ 2 · c_H(d) (mod 2^d)` holds modulo `2^3`
and fails modulo `2^4`.  This is not the congruence hypothesis consumed by
`certifiedKill_transfer`, and scaling a safe residue need not preserve the
excluded arc.  The theorem refutes this coefficient-scaling guess; it does not
by itself refute every possible certificate-transfer argument. -/
theorem natural_lift_guess_fails_at_four
    (h1 : Nat.totient 591133442051411133755680804 = 294019250239662992959575360)
    (h2 : Nat.totient 1182266884102822267511361604 = 591133413809049574662595584)
    (h3 : Nat.totient 2364533768205644535022723204 = 1182266883135824490764412200) :
    diagCoeff (periodLcm 61) 4 = 297114163569386581703020224
      ∧ diagCoeff (periodLcm 64) 4 = 591133469326774916101816616
      ∧ (2 : ℤ) ^ 3 ∣ (diagCoeff (periodLcm 64) 4 - 2 * diagCoeff (periodLcm 61) 4)
      ∧ ¬ ((2 : ℤ) ^ 4 ∣ (diagCoeff (periodLcm 64) 4 - 2 * diagCoeff (periodLcm 61) 4)) := by
  have h61 : periodLcm 61 = 591133442051411133755680800 := by decide
  have h64 : periodLcm 64 = 1182266884102822267511361600 := by decide
  have c61 : diagCoeff (periodLcm 61) 4 = 297114163569386581703020224 := by
    unfold diagCoeff
    rw [h61]
    norm_num [h1, h2]
  have c64 : diagCoeff (periodLcm 64) 4 = 591133469326774916101816616 := by
    unfold diagCoeff
    rw [h64]
    norm_num [h2, h3]
  refine ⟨c61, c64, ?_, ?_⟩
  · rw [c61, c64]; decide
  · rw [c61, c64]; decide

/-- **The counterexample is not an accident of `d = 4`.**  Recomputed from the
same recorded totients, the true relation at that position is
`c_{H₆₄}(4) = 2·c_{H₆₁}(2)` (`diagCoeff_t64_four_eq`), and
`c_{H₆₁}(2) = 295566734663387458050908308`, whereas
`c_{H₆₁}(4) = 297114163569386581703020224`.  The two old coefficients differ, so
the specific same-offset scaling guess cannot be repaired by identifying these
two old coefficients. -/
theorem diagCoeff_61_two_ne_four
    (h1 : Nat.totient 591133442051411133755680804 = 294019250239662992959575360)
    (h2 : Nat.totient 1182266884102822267511361604 = 591133413809049574662595584)
    (h3 : Nat.totient 2364533768205644535022723204 = 1182266883135824490764412200) :
    diagCoeff (periodLcm 61) 2 = 295566734663387458050908308
      ∧ diagCoeff (periodLcm 61) 2 ≠ diagCoeff (periodLcm 61) 4 := by
  have hfour := (natural_lift_guess_fails_at_four h1 h2 h3).1
  have hlift := diagCoeff_t64_four_eq
  have hc64 := (natural_lift_guess_fails_at_four h1 h2 h3).2.1
  have h2eq : diagCoeff (periodLcm 61) 2 = 295566734663387458050908308 := by
    rw [hc64] at hlift
    linarith
  exact ⟨h2eq, by rw [h2eq, hfour]; decide⟩

/-! ## Result 6: the free parameter the corpus never uses -/

private lemma shift_identity (f : ℕ → ℤ) (L : ℕ) :
    ∑ j ∈ Finset.range L, f (j + 1) * 2 ^ (L - 1 - j)
      = 2 * (∑ j ∈ Finset.range L, f j * 2 ^ (L - 1 - j)) - f 0 * 2 ^ L + f L := by
  rcases L with _ | M
  · simp
  · rw [Finset.sum_range_succ (f := fun j => f (j + 1) * 2 ^ (M + 1 - 1 - j)),
        Finset.sum_range_succ' (f := fun j => f j * 2 ^ (M + 1 - 1 - j))]
    have hmul : ∀ j ∈ Finset.range M,
        f (j + 1) * 2 ^ (M + 1 - 1 - j) = 2 * (f (j + 1) * 2 ^ (M + 1 - 1 - (j + 1))) := by
      intro j hj
      have hjM : j < M := Finset.mem_range.mp hj
      have hp : (2 : ℤ) ^ (M + 1 - 1 - j) = 2 * 2 ^ (M + 1 - 1 - (j + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hp]; ring
    rw [Finset.sum_congr rfl hmul, ← Finset.mul_sum]
    simp
    ring

/-- **The `N`-slide recurrence.**  At fixed shift `h` and fixed depth `L`,
advancing the base point by one is an exact affine step:

  `A_{h,N+1,L} = 2·A_{h,N,L} − c(1)·2^L + c(L+1)`,

where `c(d) = φ(N+h+d) − φ(N+d)`.  The window slides; only *one* new totient
pair enters per step, and the outgoing coefficient leaves through a multiple of
`2^L`. -/
theorem windowDiscrepancy_shift (h N L : ℕ) :
    windowDiscrepancy h (N + 1) L
      = 2 * windowDiscrepancy h N L
        - ((Nat.totient (N + h + 1) : ℤ) - (Nat.totient (N + 1) : ℤ)) * 2 ^ L
        + ((Nat.totient (N + h + 1 + L) : ℤ) - (Nat.totient (N + 1 + L) : ℤ)) := by
  have key := shift_identity
    (fun j => (Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) L
  simp only [] at key
  unfold windowDiscrepancy
  rw [← key]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : N + 1 + h + 1 + j = N + h + 1 + (j + 1) := by omega
  have e2 : N + 1 + 1 + j = N + 1 + (j + 1) := by omega
  rw [e1, e2]

/-- **The residue evolves by the doubling map.**  Modulo `2^L` the outgoing
coefficient vanishes entirely and the recurrence becomes

  `A_{h,N+1,L} ≡ 2·A_{h,N,L} + (φ(N+h+1+L) − φ(N+1+L))  (mod 2^L)`.

The supply hypothesis
`irrational_totient_series_of_lcm_certificate_supply` asks for
`certifiedKill (periodLcm t) N L` at *some* large `N`, not at `N = periodLcm t`.
The historical lcm-ray certificate tranche studied here uses the diagonal
`N = H_t`.  The corpus now also contains off-diagonal `FreePosition`
certificates for other shifts; those are finite and are not a cofinal lcm-ray
supply.  This recurrence updates the discrepancy at fixed `h` and `L` with one
new totient pair per step. -/
theorem windowDiscrepancy_shift_emod (h N L : ℕ) :
    windowDiscrepancy h (N + 1) L % 2 ^ L
      = (2 * windowDiscrepancy h N L
          + ((Nat.totient (N + h + 1 + L) : ℤ) - (Nat.totient (N + 1 + L) : ℤ))) % 2 ^ L := by
  rw [windowDiscrepancy_shift]
  have : 2 * windowDiscrepancy h N L
      - ((Nat.totient (N + h + 1) : ℤ) - (Nat.totient (N + 1) : ℤ)) * 2 ^ L
      + ((Nat.totient (N + h + 1 + L) : ℤ) - (Nat.totient (N + 1 + L) : ℤ))
    = (2 * windowDiscrepancy h N L
        + ((Nat.totient (N + h + 1 + L) : ℤ) - (Nat.totient (N + 1 + L) : ℤ)))
      + (-((Nat.totient (N + h + 1) : ℤ) - (Nat.totient (N + 1) : ℤ))) * 2 ^ L := by ring
  rw [this, Int.add_mul_emod_self_right]

end Recon249
end Lift
end ErdosProblems
