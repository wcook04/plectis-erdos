/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.LcmDiagonalReduction
import Mathlib.Tactic.NormNum.Prime

/-!
# Angle A4: the #249 lift in the non-integrality representation

The open content of #249 is a **lift**
`certifiedKill H H L → ∃ L', certifiedKill (p·H) (p·H) L'` along the prime-power
ladder `H_t = periodLcm t`.  This file asks whether the lift is easier in the
*non-integrality* representation — "`R_{2H} − R_H ∉ ℤ`" — than in the mod-`2^L`
residue representation.  The answer is a sharp **no**, and the file makes both
halves of that answer kernel-checked: the two representations are *pointwise
equivalent*, and the analogous implication for an arbitrary real number is
false.  The explicit rational counterexample is located at the historically
open `t = 67` rung; the actual totient-series cell is now certified at minimal
depth `100`.

## 1. The round trip closes, so nothing is gained

`tail_diff_notMem_int_of_certifiedKill` (repository) is one direction.
`exists_certifiedKill_of_tailDiff_notMem_int` supplies the converse: if
`D_{h,N} = R_{N+h} − R_N` is not an integer then a residue certificate fires at
that very `(h, N)`, at some depth.  The depth is produced from the gap
`δ = dist(D, ℤ)` by `2(N+h+L+2)/2^L → 0`; the approximation
`|2^L·D_{h,N} − A_{h,N,L}| ≤ N+h+L+2` is `tailDiff_approx`.

Consequence (`exists_certifiedKill_iff`): for every `(h, N)`,

  `(∃ L, certifiedKill h N L)  ↔  2^N(2^h − 1)·S ∉ ℤ`.

So `certifiedKill` carries *exactly* the information "`2^N(2^h−1)S ∉ ℤ`" and
nothing more.  `irrational_of_killsPeriod` checks that the reduction is faithful:
killing every period in this representation proves #249.  A4 is therefore not a
change of problem — it is a change of notation.

## 2. What the notation buys: the lift becomes a one-line statement

`R_{N+1} = 2·R_N − φ(N+1)` (`totientTail_succ`) makes the whole `N`-orbit a
single number's binary expansion (`tailDiff_shift_mod_int`:
`D_{h,N+k} ≡ 2^k·D_{h,N} (mod ℤ)`), and integrality is upward closed in `N`
(`tailDiff_mem_int_succ`).  Two consequences worth recording:

* **The free position parameter is a liability.**  A certificate at `N` implies
  one at every *smaller* `N` (`exists_certifiedKill_antitone`): the kill set of a
  period is a downward-closed initial segment.  Walking the `N`-orbit upward with
  `windowDiscrepancy_shift_emod` — one totient pair per step — walks strictly
  into the *harder* statements, and "cofinally many `N`" is the same demand as
  "every `N`".  The unused parameter is not a reserve of cheap certificates.
* **The rung `H → p·H` is multiplication by one integer.**  With
  `M = mersenneRatio p H = (2^{pH}−1)/(2^H−1) = ∑_{i<p} 2^{H·i}`,
  `killsPeriod_lift_iff` and `tailDiff_lift_mod_int` say

    `D_{pH,N} ≡ M · D_{H,N}  (mod ℤ)`,

  so the entire open content of the rung is the implication

    `x ∉ ℤ  ⟹  M·x ∉ ℤ`,   `x = 2^N(2^H − 1)·S`.

  This is the sharpest available statement of the lift.  It is *not* a
  transport of arithmetic: the covered fraction is not `1/p` (Recon249,
  Result 3) but the single scalar `M`.

## 3. The arbitrary-real implication is false at the historical frontier

`x ∉ ℤ ⟹ M·x ∉ ℤ` fails for any `x` whose denominator divides `M`.  Every such
denominator is genuinely new at its rung: `q ∣ M` with `q ∤ 2^H − 1` means
`ord_q(2) ∣ pH` but `ord_q(2) ∤ H`, i.e. `q` is a primitive-type divisor born at
that rung.  `killsPeriod_lift_fails` packages this; the smallest ladder instance
is `H₄ = 12 → H₅ = 60` with witness `1/11` (`ord₁₁(2) = 10 ∣ 60`, `∤ 12`).

The historical `t = 67` instance is explicit.
`2⁶⁷ − 1 = 193707721 · 761838257287`;
because `67` is prime, `ord_{193707721}(2) = 67` exactly
(`dvd_two_pow_sub_one_iff`).  And `67 ∤ lcm(1,…,66)` while `67 ∣ lcm(1,…,67)`.
Hence for `q₆₇ = frontierWitness = 193707721`:

* `frontierWitness_kills_upto_66` : for **every** `t ≤ 66` and (via
  `killsPeriod_iff`) every position `N`, the rational `1/q₆₇` satisfies the exact
  conclusion of a `certifiedKill` — `2^N(2^{H_t} − 1)·x ∉ ℤ`;
* `frontierWitness_fails_at_67` : it fails at `t = 67`.

So a single rational number satisfies the period-kill conclusions through
`t ≤ 66` and fails at `t = 67`.  This proves that those lower-rung conclusions
alone do not imply the next one for an arbitrary real number.  It does not say
that the concrete totient series lacks additional information: the repository
now certifies its `t = 67` cell directly and the finite diagonal band through
`t ≤ 82`.

## 4. How much localisation a certificate would have to supply

`exists_lattice_point`: the lattice `(1/M)·ℤ` is `1/(2M)`-dense, and
`frontier_multiplier_ge` shows `M₆₇ = ∑_{i<67} 2^{i·H₆₆} ≥ 2^L` for every
`L ≤ 66·H₆₆ ≈ 7.8·10²⁸`.  A depth-`L` certificate localises `D` to radius
`(N+h+L+2)/2^L`, never finer than `2^{−L}` (`tailDiff_approx`), and by
`frontier_ball_meets_lattice` every ball of radius `2^{−(L+1)}` already contains a
point of `(1/M₆₇)·ℤ` where the arbitrary-real lift implication fails.  Thus this
particular localisation argument cannot separate a point from that lattice at
depth `L ≤ 66·H₆₆`.  It is not a lower bound on every proof, and it does not
describe the depth needed by the concrete totient series, whose `t = 67` cell
is now certified at depth `100`.

## Not proved

No lift.  Nothing here weakens or replaces the open supply hypothesis; the
results are a closure of the A4 route, not progress along it.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace ErdosProblems
namespace Lift
namespace AngleA4

open Finset

set_option maxRecDepth 10000

/-- The #249 constant `S = ∑ φ(n)/2ⁿ`. -/
noncomputable def totientSeries : ℝ := ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n

/-- The shifted tail difference `D_{h,N} = R_{N+h} − R_N`, the quantity whose
non-integrality is the content of a certified kill. -/
noncomputable def tailDiff (h N : ℕ) : ℝ := totientTail (N + h) - totientTail N

/-! ## The exact one-step recurrence for the local tail -/

/-- `R_{N+1} = 2·R_N − φ(N+1)`. -/
theorem totientTail_succ (N : ℕ) :
    totientTail (N + 1) = 2 * totientTail N - (Nat.totient (N + 1) : ℝ) := by
  have hsum := summable_totientTail_terms N
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hrw : ∑' i : ℕ, (Nat.totient (N + 1 + (i + 1)) : ℝ) / 2 ^ ((i + 1) + 1)
      = totientTail (N + 1) / 2 := by
    unfold totientTail
    rw [← tsum_div_const]
    refine tsum_congr fun i => ?_
    have h1 : N + 1 + (i + 1) = N + 1 + 1 + i := by omega
    rw [h1]
    have h2 : (2 : ℝ) ^ ((i + 1) + 1) = 2 ^ (i + 1) * 2 := by ring
    rw [h2]
    field_simp
  rw [Finset.sum_range_one, hrw] at hsplit
  have hz : (Nat.totient (N + 1 + 0) : ℝ) / 2 ^ (0 + 1) = (Nat.totient (N + 1) : ℝ) / 2 := by
    norm_num
  rw [hz] at hsplit
  have hT : (∑' i : ℕ, (Nat.totient (N + 1 + i) : ℝ) / 2 ^ (i + 1)) = totientTail N := rfl
  rw [hT] at hsplit
  linarith

/-- `D_{h,N+1} = 2·D_{h,N} − (φ(N+h+1) − φ(N+1))`. -/
theorem tailDiff_succ (h N : ℕ) :
    tailDiff h (N + 1)
      = 2 * tailDiff h N - ((Nat.totient (N + h + 1) : ℝ) - (Nat.totient (N + 1) : ℝ)) := by
  unfold tailDiff
  have h1 : N + 1 + h = N + h + 1 := by omega
  rw [h1, totientTail_succ (N + h), totientTail_succ N]
  ring

/-- **Integrality of the tail difference is upward closed in `N`.**  Hence for a
fixed period `h` the positions carrying a certificate form a downward-closed
initial segment of `ℕ`, and "cofinally many `N`" is the same demand as "every
`N`". -/
theorem tailDiff_mem_int_succ {h N : ℕ}
    (hmem : tailDiff h N ∈ Set.range ((↑) : ℤ → ℝ)) :
    tailDiff h (N + 1) ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨k, hk⟩ := hmem
  refine ⟨2 * k - ((Nat.totient (N + h + 1) : ℤ) - (Nat.totient (N + 1) : ℤ)), ?_⟩
  rw [tailDiff_succ]
  push_cast
  rw [hk]

/-- Integrality propagates from any position to every later one. -/
theorem tailDiff_mem_int_mono {h M N : ℕ} (hMN : M ≤ N)
    (hmem : tailDiff h M ∈ Set.range ((↑) : ℤ → ℝ)) :
    tailDiff h N ∈ Set.range ((↑) : ℤ → ℝ) := by
  induction N, hMN using Nat.le_induction with
  | base => exact hmem
  | succ n _ ih => exact tailDiff_mem_int_succ ih

/-- **The whole `N`-orbit at a fixed period is one number's binary expansion.**
`D_{h,N+k} = 2^k·D_{h,N}` modulo `ℤ`.  Sliding the base point is the doubling
map on the fractional part; it manufactures no new arithmetic. -/
theorem tailDiff_shift_mod_int (h N k : ℕ) :
    tailDiff h (N + k) - (2 : ℝ) ^ k * tailDiff h N ∈ Set.range ((↑) : ℤ → ℝ) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨2 * c - ((Nat.totient (N + n + h + 1) : ℤ) - (Nat.totient (N + n + 1) : ℤ)), ?_⟩
      have harg : N + (n + 1) = N + n + 1 := by omega
      rw [harg, tailDiff_succ h (N + n), pow_succ]
      push_cast
      linarith

/-! ## The tail difference is a dyadic Mersenne multiple of `S` -/

/-- `D_{h,N} = 2^N·(2^h − 1)·S − (Φ_{N+h} − Φ_N)`. -/
theorem tailDiff_eq (h N : ℕ) :
    tailDiff h N
      = (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * totientSeries
        - (((totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℝ) := by
  have h1 := two_pow_mul_totient_series_eq (N + h)
  have h2 := two_pow_mul_totient_series_eq N
  have hp : (2 : ℝ) ^ (N + h) = 2 ^ N * 2 ^ h := pow_add 2 N h
  rw [hp] at h1
  unfold tailDiff totientSeries
  have hring : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (2 : ℝ) ^ N * 2 ^ h * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        - 2 ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by ring
  push_cast
  linarith

/-- **Certificate content, in closed form.**  A kill at `(h, N)` is exactly the
statement that `2^N·(2^h − 1)·S` is not an integer. -/
theorem tailDiff_mem_int_iff (h N : ℕ) :
    tailDiff h N ∈ Set.range ((↑) : ℤ → ℝ)
      ↔ (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * totientSeries ∈ Set.range ((↑) : ℤ → ℝ) := by
  have key := tailDiff_eq h N
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + ((totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ)), ?_⟩
    push_cast
    push_cast at key
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨k - ((totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ)), ?_⟩
    push_cast
    push_cast at key
    linarith

/-! ## The round trip: non-integrality produces a certificate -/

/-- The window discrepancy approximates `2^L · D_{h,N}` to within the exclusion
radius of the certificate. -/
theorem tailDiff_approx (h N L : ℕ) :
    |(2 : ℝ) ^ L * tailDiff h N - (windowDiscrepancy h N L : ℝ)|
      ≤ (N : ℝ) + h + L + 2 := by
  have hdec1 := totientTail_eq_partial_add_tail (N + h) L
  have hdec2 := totientTail_eq_partial_add_tail N L
  have hA := windowDiscrepancy_div_eq h N L
  have hT1n := tail_after_nonneg (N + h) L
  have hT2n := tail_after_nonneg N L
  have hT1u := tail_after_le (N + h) L
  have hT2u := tail_after_le N L
  push_cast at hT1u
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  set T1 := ∑' j : ℕ, (Nat.totient (N + h + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT1def
  set T2 := ∑' j : ℕ, (Nat.totient (N + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT2def
  have hsplit : tailDiff h N
      = ((windowDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L + (T1 - T2) := by
    unfold tailDiff
    rw [hdec1, hdec2, hA]
    ring
  have hs1 : T1 * 2 ^ L ≤ (N : ℝ) + h + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT1u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hs2 : T2 * 2 ^ L ≤ (N : ℝ) + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT2u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hn1 : 0 ≤ T1 * 2 ^ L := mul_nonneg hT1n h2L.le
  have hn2 : 0 ≤ T2 * 2 ^ L := mul_nonneg hT2n h2L.le
  have hkey : (2 : ℝ) ^ L * tailDiff h N - (windowDiscrepancy h N L : ℝ)
      = (T1 - T2) * 2 ^ L := by
    rw [hsplit]
    field_simp
    ring
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  rw [hkey, sub_mul, abs_le]
  constructor
  · linarith
  · linarith

private lemma exists_depth (C δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℕ, 2 * (C + L) < δ * 2 ^ L := by
  have hgeo : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hlin : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)
  have hsum : Summable (fun j : ℕ => (C + (j : ℝ)) * (1 / 2 : ℝ) ^ j) :=
    ((hgeo.mul_left C).add hlin).congr fun j => by ring
  have htend := hsum.tendsto_atTop_zero
  obtain ⟨L₀, hL₀⟩ := Metric.tendsto_atTop.mp htend (δ / 2) (by linarith)
  refine ⟨L₀, ?_⟩
  have hd := hL₀ L₀ le_rfl
  rw [Real.dist_eq, sub_zero] at hd
  have hlt : (C + (L₀ : ℝ)) * (1 / 2 : ℝ) ^ L₀ < δ / 2 := lt_of_abs_lt hd
  have hpow : (1 / 2 : ℝ) ^ L₀ = 1 / 2 ^ L₀ := by rw [div_pow, one_pow]
  rw [hpow] at hlt
  have h2 : (0 : ℝ) < 2 ^ L₀ := by positivity
  rw [mul_one_div, div_lt_iff₀ h2] at hlt
  linarith

/-- Failure of the residue certificate at depth `L` puts the window discrepancy
within the exclusion radius of a multiple of `2^L`. -/
private lemma exists_near_multiple {A : ℤ} {L : ℕ} {r : ℤ} (hr : 0 ≤ r)
    (hnc : ¬ (r < A % 2 ^ L ∧ A % 2 ^ L < 2 ^ L - r)) :
    ∃ k : ℤ, |A - k * 2 ^ L| ≤ r := by
  have hP : (0 : ℤ) < 2 ^ L := by positivity
  have hmodnn : 0 ≤ A % 2 ^ L := Int.emod_nonneg A hP.ne'
  have hmodlt : A % 2 ^ L < 2 ^ L := Int.emod_lt_of_pos A hP
  have hd := Int.emod_add_mul_ediv A (2 ^ L)
  rcases not_and_or.mp hnc with hx | hx
  · have hle : A % 2 ^ L ≤ r := not_lt.mp hx
    refine ⟨A / 2 ^ L, ?_⟩
    have hz : A - A / 2 ^ L * 2 ^ L = A % 2 ^ L := by linarith
    rw [hz, abs_le]
    exact ⟨by linarith, hle⟩
  · have hge : (2 : ℤ) ^ L - r ≤ A % 2 ^ L := not_lt.mp hx
    refine ⟨A / 2 ^ L + 1, ?_⟩
    have hz : A - (A / 2 ^ L + 1) * 2 ^ L = A % 2 ^ L - 2 ^ L := by linarith
    rw [hz, abs_le]
    exact ⟨by linarith, by linarith⟩

/-- **The converse bridge.**  Non-integrality of the tail difference at `(h, N)`
produces a `certifiedKill` at that very `(h, N)`, at some depth.  Together with
`tail_diff_notMem_int_of_certifiedKill` this makes the two representations
*pointwise equivalent*: the residue certificate carries exactly the information
"`D_{h,N} ∉ ℤ`" and nothing more. -/
theorem exists_certifiedKill_of_tailDiff_notMem_int {h N : ℕ}
    (hD : tailDiff h N ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ L, certifiedKill h N L := by
  set D := tailDiff h N with hDdef
  have hfrdef : Int.fract D = D - (⌊D⌋ : ℝ) := rfl
  have hfr0 : Int.fract D ≠ 0 := by
    intro hcon
    refine hD ⟨⌊D⌋, ?_⟩
    rw [hfrdef] at hcon
    linarith
  have hfrpos : 0 < Int.fract D := lt_of_le_of_ne (Int.fract_nonneg D) (Ne.symm hfr0)
  have hfrlt : Int.fract D < 1 := Int.fract_lt_one D
  set δ := min (Int.fract D) (1 - Int.fract D) with hδdef
  have hδpos : 0 < δ := lt_min hfrpos (by linarith)
  have hgap : ∀ k : ℤ, δ ≤ |D - (k : ℝ)| := by
    intro k
    rcases le_or_gt k ⌊D⌋ with hk | hk
    · have hkr : (k : ℝ) ≤ (⌊D⌋ : ℝ) := by exact_mod_cast hk
      have h1 : Int.fract D ≤ D - (k : ℝ) := by rw [hfrdef]; linarith
      have h2 : (0 : ℝ) ≤ D - (k : ℝ) := le_trans (Int.fract_nonneg D) h1
      rw [abs_of_nonneg h2]
      exact le_trans (min_le_left _ _) h1
    · have hk1 : (⌊D⌋ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
      have h1 : D - (k : ℝ) ≤ Int.fract D - 1 := by rw [hfrdef]; linarith
      have h2 : D - (k : ℝ) < 0 := by linarith
      rw [abs_of_neg h2]
      have h3 : 1 - Int.fract D ≤ -(D - (k : ℝ)) := by linarith
      exact le_trans (min_le_right _ _) h3
  obtain ⟨L, hL⟩ := exists_depth ((N : ℝ) + h + 2) δ hδpos
  refine ⟨L, ?_⟩
  by_contra hnc
  have hr0 : (0 : ℤ) ≤ (N : ℤ) + (h : ℤ) + (L : ℤ) + 2 := by positivity
  obtain ⟨k, hk⟩ := exists_near_multiple (A := windowDiscrepancy h N L) (L := L)
    (r := (N : ℤ) + (h : ℤ) + (L : ℤ) + 2) hr0 hnc
  have hkR : |((windowDiscrepancy h N L : ℤ) : ℝ) - (k : ℝ) * 2 ^ L|
      ≤ (N : ℝ) + (h : ℝ) + (L : ℝ) + 2 := by exact_mod_cast hk
  have happ := tailDiff_approx h N L
  rw [← hDdef] at happ
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hcomb : |(2 : ℝ) ^ L * D - (k : ℝ) * 2 ^ L| ≤ 2 * ((N : ℝ) + h + L + 2) := by
    have hsp : (2 : ℝ) ^ L * D - (k : ℝ) * 2 ^ L
        = ((2 : ℝ) ^ L * D - ((windowDiscrepancy h N L : ℤ) : ℝ))
          + (((windowDiscrepancy h N L : ℤ) : ℝ) - (k : ℝ) * 2 ^ L) := by ring
    rw [hsp]
    calc |((2 : ℝ) ^ L * D - ((windowDiscrepancy h N L : ℤ) : ℝ))
            + (((windowDiscrepancy h N L : ℤ) : ℝ) - (k : ℝ) * 2 ^ L)|
        ≤ |(2 : ℝ) ^ L * D - ((windowDiscrepancy h N L : ℤ) : ℝ)|
          + |((windowDiscrepancy h N L : ℤ) : ℝ) - (k : ℝ) * 2 ^ L| := abs_add_le _ _
      _ ≤ 2 * ((N : ℝ) + h + L + 2) := by linarith
  have hfac : (2 : ℝ) ^ L * D - (k : ℝ) * 2 ^ L = (D - (k : ℝ)) * 2 ^ L := by ring
  rw [hfac, abs_mul, abs_of_pos h2L] at hcomb
  have hg := hgap k
  have hlow : δ * 2 ^ L ≤ |D - (k : ℝ)| * 2 ^ L := mul_le_mul_of_nonneg_right hg h2L.le
  linarith

/-- **The two representations are pointwise the same.**  For every `(h, N)`,
"some depth-`L` residue certificate fires" is *equivalent* to
"`2^N(2^h−1)S ∉ ℤ`". -/
theorem exists_certifiedKill_iff (h N : ℕ) :
    (∃ L, certifiedKill h N L)
      ↔ (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * totientSeries ∉ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · rintro ⟨L, hcert⟩
    exact (tailDiff_mem_int_iff h N).not.mp (tail_diff_notMem_int_of_certifiedKill hcert)
  · intro hx
    exact exists_certifiedKill_of_tailDiff_notMem_int ((tailDiff_mem_int_iff h N).not.mpr hx)

/-- **The free position parameter is a liability, not an asset.**  A certificate
at position `N` implies a certificate at every *smaller* position: the kill set
of a fixed period is a downward-closed initial segment of `ℕ`.  So walking the
`N`-orbit upward — the cheap direction computationally, one totient pair per
step (`windowDiscrepancy_shift_emod`) — walks strictly *into* the harder
statements, and "cofinally many `N`" is the same demand as "every `N`". -/
theorem exists_certifiedKill_antitone {h M N : ℕ} (hMN : M ≤ N)
    (hkill : ∃ L, certifiedKill h N L) : ∃ L, certifiedKill h M L := by
  obtain ⟨L, hcert⟩ := hkill
  refine exists_certifiedKill_of_tailDiff_notMem_int fun hmem => ?_
  exact tail_diff_notMem_int_of_certifiedKill hcert (tailDiff_mem_int_mono hMN hmem)

/-! ## The abstract kill predicate and the faithful reduction of #249 -/

/-- `killsPeriod x h`: no dyadic multiple of `(2^h − 1)·x` is an integer. -/
def killsPeriod (x : ℝ) (h : ℕ) : Prop :=
  ∀ N : ℕ, (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * x ∉ Set.range ((↑) : ℤ → ℝ)

theorem killsPeriod_iff (h : ℕ) :
    killsPeriod totientSeries h ↔ ∀ N : ℕ, ∃ L, certifiedKill h N L := by
  unfold killsPeriod
  exact ⟨fun H N => (exists_certifiedKill_iff h N).mpr (H N),
    fun H N => (exists_certifiedKill_iff h N).mp (H N)⟩

/-- **The A4 reduction is faithful.**  Killing every period in the
non-integrality representation proves #249. -/
theorem irrational_of_killsPeriod (hk : ∀ h : ℕ, 0 < h → killsPeriod totientSeries h) :
    Irrational totientSeries := by
  show Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
  refine irrational_totient_series_of_certificate_supply fun h hpos N₀ => ?_
  exact ⟨N₀, le_rfl, (killsPeriod_iff h).mp (hk h hpos) N₀⟩

/-! ## The exact lift law in the non-integrality representation -/

/-- `mersenneRatio p H = (2^{pH} − 1)/(2^H − 1) = ∑_{i<p} 2^{H·i}`. -/
def mersenneRatio (p H : ℕ) : ℕ := ∑ i ∈ Finset.range p, 2 ^ (H * i)

theorem mersenneRatio_mul (p H : ℕ) :
    (mersenneRatio p H : ℝ) * ((2 : ℝ) ^ H - 1) = (2 : ℝ) ^ (p * H) - 1 := by
  unfold mersenneRatio
  have hgeo := geom_sum_mul ((2 : ℝ) ^ H) p
  have hcast : ((∑ i ∈ Finset.range p, 2 ^ (H * i) : ℕ) : ℝ)
      = ∑ i ∈ Finset.range p, ((2 : ℝ) ^ H) ^ i := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => pow_mul (2 : ℝ) H i
  rw [hcast, hgeo, ← pow_mul, mul_comm H p]

/-- **The lift, exactly.**  Passing from scale `H` to scale `p·H` multiplies the
tested quantity by the single integer `M = (2^{pH}−1)/(2^H−1)`.  So the whole
open content of the `H → pH` rung is the implication `x ∉ ℤ ⟹ M·x ∉ ℤ`, applied
to `x = 2^N(2^H − 1)S` at every `N`. -/
theorem killsPeriod_lift_iff (x : ℝ) (p H : ℕ) :
    killsPeriod x (p * H)
      ↔ ∀ N : ℕ, (mersenneRatio p H : ℝ) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ H - 1) * x)
          ∉ Set.range ((↑) : ℤ → ℝ) := by
  have heq : ∀ N : ℕ, (2 : ℝ) ^ N * ((2 : ℝ) ^ (p * H) - 1) * x
      = (mersenneRatio p H : ℝ) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ H - 1) * x) := by
    intro N
    rw [← mersenneRatio_mul p H]
    ring
  unfold killsPeriod
  constructor
  · intro H0 N hcon
    exact H0 N (by rw [heq N]; exact hcon)
  · intro H0 N hcon
    exact H0 N (by rw [← heq N]; exact hcon)

/-- Additive form: modulo `ℤ`, the tail difference at scale `p·H` is `M` times
the tail difference at scale `H`, at the *same* position `N`. -/
theorem tailDiff_lift_mod_int (p H N : ℕ) :
    tailDiff (p * H) N - (mersenneRatio p H : ℝ) * tailDiff H N
      ∈ Set.range ((↑) : ℤ → ℝ) := by
  have e1 := tailDiff_eq (p * H) N
  have e2 := tailDiff_eq H N
  have hprod : (mersenneRatio p H : ℝ) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ H - 1) * totientSeries)
      = (2 : ℝ) ^ N * ((2 : ℝ) ^ (p * H) - 1) * totientSeries := by
    rw [← mersenneRatio_mul p H]
    ring
  refine ⟨(mersenneRatio p H : ℤ) * ((totientPrefix (N + H) : ℤ) - (totientPrefix N : ℤ))
      - ((totientPrefix (N + p * H) : ℤ) - (totientPrefix N : ℤ)), ?_⟩
  rw [e1, e2]
  push_cast
  push_cast at hprod
  linarith

/-! ## The obstruction: the lift is false for a general real -/

/-- **The lift fails as an implication about real numbers.**  If `q` is an odd
prime dividing `2^{pH} − 1` but not `2^H − 1`, then `x = 1/q` kills period `H`
at *every* position `N`, and kills period `p·H` at *no* position.

Such a `q` exists at every rung: by Zsygmondy, `2^{pH} − 1` has a primitive
prime divisor for `pH > 6`, and every primitive divisor divides
`M = (2^{pH}−1)/(2^H−1)` and not `2^H − 1`.  The candidate denominators
introduced at each rung of the lcm ladder are therefore genuinely new: they were
not at issue at the scale below, so no information about the certified cell
below can exclude them. -/
theorem killsPeriod_one_div {q h : ℕ} (hq1 : 1 < q) (hodd : ¬ 2 ∣ q)
    (hnd : ¬ q ∣ 2 ^ h - 1) : killsPeriod (1 / (q : ℝ)) h := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcop : Nat.Coprime q 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  intro N
  rintro ⟨k, hk⟩
  have hcast : ((2 ^ h - 1 : ℕ) : ℝ) = (2 : ℝ) ^ h - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  have hR : (k : ℝ) * (q : ℝ) = ((2 ^ N * (2 ^ h - 1) : ℕ) : ℝ) := by
    push_cast
    rw [hcast]
    field_simp at hk
    linarith
  have hZ : (k * (q : ℤ) : ℤ) = ((2 ^ N * (2 ^ h - 1) : ℕ) : ℤ) := by exact_mod_cast hR
  have hdvdZ : (q : ℤ) ∣ ((2 ^ N * (2 ^ h - 1) : ℕ) : ℤ) := ⟨k, by rw [← hZ]; ring⟩
  have hdvdN : q ∣ 2 ^ N * (2 ^ h - 1) := by exact_mod_cast hdvdZ
  exact hnd ((Nat.Coprime.pow_right N hcop).dvd_of_dvd_mul_left hdvdN)

theorem not_killsPeriod_one_div {q h : ℕ} (hq1 : 1 < q) (hdvd : q ∣ 2 ^ h - 1) :
    ¬ killsPeriod (1 / (q : ℝ)) h := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  intro hcon
  obtain ⟨m, hm⟩ := hdvd
  refine hcon 0 ⟨(m : ℤ), ?_⟩
  have hcast : ((2 ^ h - 1 : ℕ) : ℝ) = (2 : ℝ) ^ h - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  have hmR : ((2 : ℝ) ^ h - 1) = (q : ℝ) * (m : ℝ) := by
    rw [← hcast, hm]
    push_cast
    ring
  push_cast
  rw [hmR]
  field_simp

theorem killsPeriod_lift_fails {H p q : ℕ} (hq1 : 1 < q) (hodd : ¬ 2 ∣ q)
    (hdvd : q ∣ 2 ^ (p * H) - 1) (hnd : ¬ q ∣ 2 ^ H - 1) :
    killsPeriod (1 / (q : ℝ)) H ∧ ¬ killsPeriod (1 / (q : ℝ)) (p * H) :=
  ⟨killsPeriod_one_div hq1 hodd hnd, not_killsPeriod_one_div hq1 hdvd⟩

/-- **The smallest instance on the actual lcm ladder.**  `H₄ = 12`,
`H₅ = 60 = 5·H₄`, and the real number `1/11` kills period `12` at every
position while killing period `60` at none — because `ord₁₁(2) = 10` divides
`60` but not `12`.

So the lift `certifiedKill H H L → ∃ L', certifiedKill (pH) (pH) L'`, read
through the pointwise-equivalent non-integrality representation, is *false* as a
statement about a general real number, already at the first odd-prime rung of
the ladder. -/
theorem lift_fails_periodLcm_four_to_five :
    killsPeriod (1 / ((11 : ℕ) : ℝ)) (periodLcm 4)
      ∧ ¬ killsPeriod (1 / ((11 : ℕ) : ℝ)) (periodLcm 5) := by
  have h4 : periodLcm 4 = 12 := by decide
  have h5 : periodLcm 5 = 5 * 12 := by decide
  rw [h4, h5]
  exact killsPeriod_lift_fails (q := 11) (by norm_num) (by norm_num) (by decide) (by decide)

/-! ## The frontier counterexample: the whole corpus is consistent with failure
at `t = 67` -/

/-- Periods are nested along the lcm ladder. -/
theorem periodLcm_dvd_of_le {s t : ℕ} (hst : s ≤ t) : periodLcm s ∣ periodLcm t := by
  induction t, hst using Nat.le_induction with
  | base => exact dvd_rfl
  | succ n _ ih => exact ih.trans (periodLcm_dvd_succ n)

/-- Killing a period kills all its divisors. -/
theorem killsPeriod_of_dvd {x : ℝ} {h₀ h : ℕ} (hdvd : h₀ ∣ h) (hk : killsPeriod x h) :
    killsPeriod x h₀ := by
  obtain ⟨m, hm⟩ := hdvd
  intro N hcon
  obtain ⟨k, hk'⟩ := hcon
  refine hk N ⟨(mersenneRatio m h₀ : ℤ) * k, ?_⟩
  have hM := mersenneRatio_mul m h₀
  push_cast
  rw [hk', hm, mul_comm h₀ m, ← hM]
  ring

/-- **Order transfer.**  If `q > 1` and `d` is prime with `q ∣ 2^d − 1`, then the
multiplicative order of `2` modulo `q` is exactly `d`, so `q ∣ 2^H − 1` holds
precisely when `d ∣ H`. -/
theorem dvd_two_pow_sub_one_iff {q d : ℕ} (hq1 : 1 < q) (hd : d.Prime)
    (hqd : q ∣ 2 ^ d - 1) (H : ℕ) : q ∣ 2 ^ H - 1 ↔ d ∣ H := by
  haveI : Fact (1 < q) := ⟨hq1⟩
  haveI : Fact d.Prime := ⟨hd⟩
  have hkey : ∀ m : ℕ, q ∣ 2 ^ m - 1 ↔ (2 : ZMod q) ^ m = 1 := by
    intro m
    have hcast : ((2 ^ m - 1 : ℕ) : ZMod q) = (2 : ZMod q) ^ m - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      ring
    rw [← ZMod.natCast_eq_zero_iff, hcast, sub_eq_zero]
  have h2ne : (2 : ZMod q) ≠ 1 := by
    intro hcon
    have h0 : ((1 : ℕ) : ZMod q) = 0 := by
      push_cast
      linear_combination hcon
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd one_pos h0) (by omega)
  have hord : orderOf (2 : ZMod q) = d := orderOf_eq_prime ((hkey d).mp hqd) h2ne
  rw [hkey H, ← orderOf_dvd_iff_pow_eq_one, hord]

/-- `q₆₇ = 193707721`, one of the two prime factors of
`2⁶⁷ − 1 = 193707721 · 761838257287`.  Since `67` is prime, the multiplicative
order of `2` modulo `q₆₇` is exactly `67`. -/
def frontierWitness : ℕ := 193707721

theorem frontierWitness_dvd : frontierWitness ∣ 2 ^ 67 - 1 := by
  unfold frontierWitness
  norm_num

/-- `H₆₆ = lcm(1,…,66)`. -/
theorem periodLcm_66_val : periodLcm 66 = 1182266884102822267511361600 := by decide

theorem not_dvd_67_periodLcm_66 : ¬ (67 ∣ periodLcm 66) := by
  rw [periodLcm_66_val]
  norm_num

/-- **The recorded corpus does not constrain the frontier cell at all.**  The
rational number `1/q₆₇` satisfies the conclusion of *every* deposit the
repository owns: for every scale `t ≤ 66` and — via `killsPeriod_iff` — every
position `N`, it makes `2^N(2^{H_t} − 1)·x` a non-integer, exactly as a
`certifiedKill` would.  It fails at `t = 67`. -/
theorem frontierWitness_kills_upto_66 {t : ℕ} (ht : t ≤ 66) :
    killsPeriod (1 / (frontierWitness : ℝ)) (periodLcm t) := by
  have hq1 : 1 < frontierWitness := by unfold frontierWitness; norm_num
  have hiff := dvd_two_pow_sub_one_iff hq1 (by norm_num) frontierWitness_dvd
  refine killsPeriod_of_dvd (periodLcm_dvd_of_le ht) ?_
  refine killsPeriod_one_div hq1 (by unfold frontierWitness; norm_num) ?_
  exact fun hcon => not_dvd_67_periodLcm_66 ((hiff (periodLcm 66)).mp hcon)

theorem frontierWitness_fails_at_67 :
    ¬ killsPeriod (1 / (frontierWitness : ℝ)) (periodLcm 67) := by
  have hq1 : 1 < frontierWitness := by unfold frontierWitness; norm_num
  have hiff := dvd_two_pow_sub_one_iff hq1 (by norm_num) frontierWitness_dvd
  exact not_killsPeriod_one_div hq1
    ((hiff (periodLcm 67)).mpr (dvd_periodLcm (by norm_num) (le_refl 67)))

/-! ## Why no depth-`L` certificate can settle the lift -/

/-- The lattice `(1/M)·ℤ` is `1/(2M)`-dense. -/
theorem exists_lattice_point (M : ℕ) (hM : 0 < M) (D : ℝ) :
    ∃ D' : ℝ, (M : ℝ) * D' ∈ Set.range ((↑) : ℤ → ℝ) ∧ |D - D'| ≤ 1 / (2 * M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨(round ((M : ℝ) * D) : ℝ) / M, ⟨round ((M : ℝ) * D), by field_simp⟩, ?_⟩
  have h2 : D - (round ((M : ℝ) * D) : ℝ) / M
      = ((M : ℝ) * D - (round ((M : ℝ) * D) : ℝ)) / M := by field_simp
  rw [h2, abs_div, abs_of_pos hM']
  calc |(M : ℝ) * D - (round ((M : ℝ) * D) : ℝ)| / M ≤ (1 / 2) / M := by
        gcongr
        exact abs_sub_round _
    _ = 1 / (2 * M) := by ring

/-- At the historically open `t = 67` rung the multiplier
`M₆₇ = ∑_{i<67} 2^{i·H₆₆}` dwarfs
`2^L` for every depth `L` up to `66·H₆₆ ≈ 7.8·10²⁸`. -/
theorem frontier_multiplier_ge {L : ℕ} (hL : L ≤ periodLcm 66 * 66) :
    (2 : ℝ) ^ L ≤ (mersenneRatio 67 (periodLcm 66) : ℝ) := by
  have hterm : 2 ^ (periodLcm 66 * 66) ≤ mersenneRatio 67 (periodLcm 66) := by
    unfold mersenneRatio
    exact Finset.single_le_sum (f := fun i => 2 ^ (periodLcm 66 * i))
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by norm_num))
  have hmono : (2 : ℕ) ^ L ≤ 2 ^ (periodLcm 66 * 66) := Nat.pow_le_pow_right (by norm_num) hL
  have hfin : (2 : ℕ) ^ L ≤ mersenneRatio 67 (periodLcm 66) := le_trans hmono hterm
  exact_mod_cast hfin

/-- **The quantitative obstruction.**  A depth-`L` certificate localises the tail
difference to an interval of radius `(N+h+L+2)/2^L` (`tailDiff_approx`), never
better than `2^{-L}`.  But every ball of radius `2^{-(L+1)}` already contains a
point of the lattice `(1/M₆₇)·ℤ`, on which the lift's conclusion `M₆₇·x ∉ ℤ`
fails.  So at the frontier no certificate of depth `L ≤ 66·H₆₆` — which includes
the mandatory depth `98` and every depth that could conceivably be computed —
localises well enough to decide the lift. -/
theorem frontier_ball_meets_lattice {L : ℕ} (hL : L ≤ periodLcm 66 * 66) (D : ℝ) :
    ∃ D' : ℝ, (mersenneRatio 67 (periodLcm 66) : ℝ) * D' ∈ Set.range ((↑) : ℤ → ℝ)
      ∧ |D - D'| ≤ 1 / (2 : ℝ) ^ (L + 1) := by
  have hMpos : 0 < mersenneRatio 67 (periodLcm 66) := by
    unfold mersenneRatio
    refine Finset.sum_pos (fun i _ => by positivity) ?_
    exact ⟨0, Finset.mem_range.mpr (by norm_num)⟩
  obtain ⟨D', hD'mem, hD'close⟩ := exists_lattice_point _ hMpos D
  refine ⟨D', hD'mem, le_trans hD'close ?_⟩
  have hge := frontier_multiplier_ge hL
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (L + 1) := by positivity
  have h1 : (2 : ℝ) ^ (L + 1) ≤ 2 * (mersenneRatio 67 (periodLcm 66) : ℝ) := by
    rw [pow_succ]
    linarith
  exact one_div_le_one_div_of_le hpos h1

end AngleA4
end Lift
end ErdosProblems
