/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.CarrySurvivorExtinction

/-!
# Angle A3: the shift-additive lift, and the exact obstruction that survives it

`irrational_totient_series_of_lcm_certificate_supply` (Erdos249257/LcmDiagonalReduction.lean)
derives #249 from a cofinal supply of kills `certifiedKill (periodLcm t) N L` at *some*
large `N` — the base point is a free parameter, and all 28 recorded deposits fix it on
the diagonal `N = periodLcm t`.  This file exploits that freedom.

## What is proved here

**1. Shift additivity (exact, unconditional).**  `windowDiscrepancy` is additive in the
shift along a base-point translation:

  `A_{h₁+h₂, N, L} = A_{h₁, N, L} + A_{h₂, N+h₁, L}`   (`windowDiscrepancy_add_shift`)

hence `A_{k·h, N, L} = ∑_{i<k} A_{h, N+i·h, L}` (`windowDiscrepancy_mul_shift`).  This is
an identity, not an estimate.  No uniqueness theorem for such decompositions is
proved here.  It differs from `Recon249`, which decomposes the
lifted **window** by offsets (`diagCoeff_lift_coprime`, coverage `⌊L'/p⌋`), whereas this
decomposes the lifted **discrepancy** by base points, with coverage `1`.

**2. The off-diagonal ladder step (the A3 payoff).**  Choosing the free base point to be
the *old* height `H` rather than the new height `k·H`,

  `A_{(k+1)H, H, L} = A_{H, H, L} + ∑_{i<k} A_{H, (2+i)H, L}`
      (`windowDiscrepancy_ladder_offDiagonal`),

and at a doubling boundary `t+1 = 2^k`, where `periodLcm (t+1) = 2 · periodLcm t`,

  `A_{2H, H, L} = A_{H, H, L} + A_{H, 2H, L}`  (`windowDiscrepancy_double_offDiagonal`).

The first summand is *literally the integer the certified cell below is a statement about*.
No other choice of base point does this, and the row accounting favours it too.  Write
"row `m`" for the totient block `φ(mH + d)`, `d = 1 … L`; the certified cell below read
rows `1` and `2`.  A deposit `certifiedKill (kH) (mH) L` reads rows `m` and `m + k`.

* off-diagonal, `m = 1`: rows `1` and `k+1` — **one** fresh row, for every multiplier `k`;
* diagonal, `m = k`: rows `k` and `2k` — one fresh row at `k = 2`, and **two** fresh rows
  at every `k ≥ 3`, since then `k > 2` and `2k > 2`.

So at the doubling boundaries the two placements cost the same and at every other
prime-power boundary — `p = 67` included — the off-diagonal placement halves the fresh
totient count, from `2L` to `L`.  (The decomposition above is a proof device, not the
evaluation route: evaluating its `k` summands would read rows `1 … k+1`.  The point of the
decomposition is that it exhibits `A_{H,H,L}` as an exact summand, which is what makes a
lift *law*, as opposed to a recomputation, possible at all.)

**3. A conditional residue criterion.**  `certifiedKill_ladder_lift`: if the fresh correction
`∑_{i<k} A_{H,(2+i)H,L}` is congruent mod `2^L` to some `e` with `|e| ≤ δ`, and the old
diagonal residue `A_{H,H,L} mod 2^L` clears the *new* exclusion radius by a further `δ`,
then `certifiedKill ((k+1)·H) H L`.  It is uniform in `k` and consumes the old
cell's residue, not merely its Boolean certificate.
`certifiedKill_double_lift` is the `k = 1` case.  The adversarial verifier shows
that once the honest symmetric correction allowance reaches `2^(L-1)`, the two
arc-margin hypotheses are contradictory; the criterion then carries no lift.
It packages direct knowledge of the new residue rather than deriving that
knowledge from the old certificate.

**4. A second, composable, sufficient criterion.**  `certifiedKill_of_two_pow_dvd`: if
`2^v ∣ A_{h,N,L}`, `2^L ∤ A_{h,N,L}` and `N+h+L+2 < 2^v`, then `certifiedKill h N L`.
Unlike the arc condition, 2-adic divisibility is *stable under addition*, so it survives
the decomposition of 1: `certifiedKill_lift_of_common_dvd` lifts a common divisibility on
all `k` summands to a certificate at the multiplied shift.  Some such strengthening is
forced: §3 exhibits two window discrepancies whose residues sum to exactly `0`, so the arc
condition itself does not survive the decomposition.

**5. The `(N, L)` plane collapses to anti-diagonals.**  `windowDiscrepancy_emod_pow`: for
`j ≤ L`, `A_{h,N,L} ≡ A_{h, N+(L-j), j} (mod 2^j)` — a cell sees its window only through
the right endpoint `N + L`.  Hence `certifiedKill_of_endpoint'`: at a fixed endpoint,
certification propagates from small depth to large depth, i.e. from large base point to
small.  The supply theorem wants *large* base point, so this trade runs the wrong way:
`Recon249`'s free-`N` parameter is free only in the direction that does not help.

## The obstruction, sharply

The lift of 3 needs one number: the fresh correction `A_{H,2H,L} mod 2^L`.  That number
is not a perturbation of anything below, and here is the smallest explicit proof.

*It can annihilate a certificate exactly.*  At `H = 2`, `L = 5`:
`A_{2,2,5} = 44`, residue `12`, exclusion radius `11` — `certifiedKill 2 2 5` holds
(`certifiedKill_two_two_five`).  The fresh correction is `A_{2,4,5} = 52`, residue `20`.
Their sum is `A_{4,2,5} = 96 ≡ 0 (mod 32)`: the correction moves the residue to the exact
centre of the forbidden zone and `certifiedKill 4 2 5` fails
(`not_certifiedKill_four_two_five`, `windowDiscrepancy_four_two_five_emod`).  So `δ` in
the lift law must be taken as large as `2^{L-1}`, i.e. the hypothesis degenerates.

*It can also create a certificate out of nothing.*  At the lcm doubling boundary
`t = 3 → 4` (`H = periodLcm 3 = 6`, `2H = periodLcm 4 = 12`), depth `6`:
`A_{6,6,6} = 270`, residue `14`, radius `20` — `certifiedKill 6 6 6` is **false**
(`not_certifiedKill_six_six_six`).  The correction `A_{6,12,6} = 278`, residue `22`,
carries the sum to `A_{12,6,6} = 548`, residue `36`, radius `26`, and
`certifiedKill 12 6 6` is **true** (`certifiedKill_twelve_six_six`).  The certificate at
the doubled shift is produced entirely by data the scale below does not contain.

*Its 2-adic valuation is generic, never large.*  The divisibility route of 4 needs
`2^v ∣ A_{H,2H,L}` with `2^v > 3H + L + 2`; the verbatim-transfer route (`e = δ = 0` in
the lift law) needs `v ≥ L`.  With `H = periodLcm t` and `L = L_t` the least certifying
diagonal depth, for `t = 1 … 25`:

  `L_t`                = `6,5,7,7,9,9,14,15,14,14,21,21,22,22,22,23,26,26,32,32,32,32,35,35,38`
  least admissible `v` = `4,4,5,6,8,8,11,12,13,13,17,17,21,21,21,22,26,26,30,30,30,30,34,34,37`
  measured `v₂(A_{H,2H,L_t})` = `1,2,1,2,3,3,4,3,2,2,4,4,3,3,3,4,6,6,2,2,2,2,4,4,5`

The measured valuation never exceeds `6` while the admissible threshold grows like
`log₂ H`; the deficit is `3,2,4,4,5,5,7,9,11,11,13,13,18,18,18,18,20,20,28,28,28,28,30,30,
32` and increasing.  Two of these are kernel-checked here: `two_dvd_correction_six` and
`not_four_dvd_correction_six` pin `v₂(A_{6,12,6}) = 1` where the transfer needs `≥ 6`.

## What the free base point does buy

At the `t = 7 → 8` doubling boundary, at the depth `14` of the recorded deposit
`certifiedKill_periodLcm_diagonal_at_seven`:

* `certifiedKill (periodLcm 8) (periodLcm 8) 14` is **false** (`not_certifiedKill_diagonal_at_eight_depth14`)
  — the diagonal route must buy a bit and go to depth `15`;
* `certifiedKill (periodLcm 8) (periodLcm 7) 14` is **true** (`certifiedKill_offDiagonal_at_eight_depth14`)
  — the off-diagonal route succeeds at the *same* depth as the deposit below.

That is one data point, not a law, and it is recorded as such.  But it is a legitimate
deposit for the free-`N` supply theorem, it is one bit cheaper than the diagonal one, and
it is the first instance in this repository of a #249 certificate placed off the diagonal.

## What is *not* proved

No infinite family, and hence nothing about #249 itself.  The conditional
criteria are uniform in the multiplier, but their hypothesis is a statement about one fresh
row of `L` Euler totients — `φ(3H+d)`, `d = 1 … L`, at a doubling boundary — and §3 shows
by MEASUREMENT that this row is 2-adically generic in the tested cases.  The
heuristic `2^{-L}` rate and the claim that it never fires are not proved.
The A3 question "which infinite family of `p` admits a provable lift" is
answered here only negatively: the shift-additive decomposition is uniform in `p`, so it
singles out no family at all, and the one thing it does buy — the halving of the fresh
totient count by moving the base point off the diagonal — is a constant-factor saving on
a computation, not a law.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace ErdosProblems
namespace Lift
namespace AngleA3

set_option maxRecDepth 100000

/-! ## 1. Shift additivity: the exact decomposition of a lifted cell -/

/-- A zero shift has zero discrepancy. -/
theorem windowDiscrepancy_zero_shift (N L : ℕ) : windowDiscrepancy 0 N L = 0 := by
  unfold windowDiscrepancy
  simp

/-- **Shift additivity.**  Splitting the shift `h₁ + h₂` splits the window discrepancy
into the `h₁`-cell at base point `N` and the `h₂`-cell at base point `N + h₁`.  Exact,
with no hypotheses: the middle totient row `φ(N+h₁+1+j)` cancels. -/
theorem windowDiscrepancy_add_shift (h₁ h₂ N L : ℕ) :
    windowDiscrepancy (h₁ + h₂) N L
      = windowDiscrepancy h₁ N L + windowDiscrepancy h₂ (N + h₁) L := by
  unfold windowDiscrepancy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : N + (h₁ + h₂) + 1 + j = N + h₁ + h₂ + 1 + j := by omega
  rw [e1]
  ring

/-- **The `k`-fold decomposition.**  A cell at the multiplied shift `k·h` is the sum of
`k` cells at the certified shift `h`, at the consecutive base points `N, N+h, …, N+(k-1)h`.

This is the base-point counterpart of the offset dilation `diagCoeff_lift_coprime` of
`Recon249`.  That law covers `⌊L'/p⌋` of the `L'` offsets exactly; this one covers all of
them, at the price of `k` unknown summands instead of one. -/
theorem windowDiscrepancy_mul_shift (k h N L : ℕ) :
    windowDiscrepancy (k * h) N L
      = ∑ i ∈ Finset.range k, windowDiscrepancy h (N + i * h) L := by
  induction k with
  | zero => simpa using windowDiscrepancy_zero_shift N L
  | succ k ih =>
      have hk : (k + 1) * h = k * h + h := by ring
      rw [hk, windowDiscrepancy_add_shift, ih, Finset.sum_range_succ]

/-- **The diagonal ladder step.**  The lifted *diagonal* cell at height `p·H` is a sum of
`p` cells at the old shift `H`, but at base points `pH, (p+1)H, …, (2p-1)H`: none of them
is the certified cell `N = H`, and together they read the totient rows `p, p+1, …, 2p`
where the direct computation reads only rows `p` and `2p`. -/
theorem windowDiscrepancy_ladder_diagonal (p H L : ℕ) :
    windowDiscrepancy (p * H) (p * H) L
      = ∑ i ∈ Finset.range p, windowDiscrepancy H ((p + i) * H) L := by
  rw [windowDiscrepancy_mul_shift]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show p * H + i * H = (p + i) * H from by ring]

/-- **The off-diagonal ladder step — the A3 identity.**  Placing the base point at the
*old* height `H` (legitimate: the supply theorem
`irrational_totient_series_of_lcm_certificate_supply` leaves `N` free) makes the certified
cell `A_{H,H,L}` an exact summand of the lifted cell. -/
theorem windowDiscrepancy_ladder_offDiagonal (k H L : ℕ) :
    windowDiscrepancy ((k + 1) * H) H L
      = windowDiscrepancy H H L
        + ∑ i ∈ Finset.range k, windowDiscrepancy H ((2 + i) * H) L := by
  have hsum : ∑ i ∈ Finset.range k, windowDiscrepancy H (H + (i + 1) * H) L
      = ∑ i ∈ Finset.range k, windowDiscrepancy H ((2 + i) * H) L :=
    Finset.sum_congr rfl fun i _ => by
      rw [show H + (i + 1) * H = (2 + i) * H from by ring]
  rw [windowDiscrepancy_mul_shift, Finset.sum_range_succ', hsum]
  simp only [Nat.zero_mul, Nat.add_zero]
  exact add_comm _ _

/-- The doubling case of the off-diagonal step: at a boundary `t+1 = 2^k` of the lcm
ladder, where `periodLcm (t+1) = 2 · periodLcm t`, the whole lift is one new integer. -/
theorem windowDiscrepancy_double_offDiagonal (H L : ℕ) :
    windowDiscrepancy (2 * H) H L
      = windowDiscrepancy H H L + windowDiscrepancy H (2 * H) L := by
  rw [show 2 * H = H + H from by ring]
  exact windowDiscrepancy_add_shift H H H L

/-- The doubling case of the diagonal step, for comparison: two new integers, and neither
of them is the certified cell. -/
theorem windowDiscrepancy_double_diagonal (H L : ℕ) :
    windowDiscrepancy (2 * H) (2 * H) L
      = windowDiscrepancy H (2 * H) L + windowDiscrepancy H (3 * H) L := by
  have h := windowDiscrepancy_add_shift H H (2 * H) L
  rw [show H + H = 2 * H from by ring, show 2 * H + H = 3 * H from by ring] at h
  exact h

/-! ## 2. Two sufficient criteria, one of them additively stable -/

/-- **The 2-adic criterion.**  A window discrepancy divisible by `2^v` but not by `2^L`
has residue at distance at least `2^v` from both ends of the circle, so it certifies as
soon as `2^v` exceeds the exclusion radius.

Unlike the arc condition of `certifiedKill`, this hypothesis is stable under addition,
which is what lets it pass through the decomposition of §1. -/
theorem certifiedKill_of_two_pow_dvd {h N L v : ℕ}
    (hdvd : (2 : ℤ) ^ v ∣ windowDiscrepancy h N L)
    (hne : ¬ ((2 : ℤ) ^ L ∣ windowDiscrepancy h N L))
    (hrad : ((N : ℤ) + h + L + 2) < 2 ^ v) :
    certifiedKill h N L := by
  set A := windowDiscrepancy h N L with hA
  have h2L : (0 : ℤ) < 2 ^ L := by positivity
  have hvL : v ≤ L := by
    by_contra hcon
    exact hne (dvd_trans (pow_dvd_pow 2 (by omega)) hdvd)
  have hR0 : 0 ≤ A % 2 ^ L := Int.emod_nonneg A (ne_of_gt h2L)
  have hRlt : A % 2 ^ L < 2 ^ L := Int.emod_lt_of_pos A h2L
  have hRne : A % 2 ^ L ≠ 0 := fun hcon => hne (Int.dvd_of_emod_eq_zero hcon)
  have hdvdR : (2 : ℤ) ^ v ∣ A % 2 ^ L := by
    have hsplit : A % 2 ^ L = A - 2 ^ L * (A / 2 ^ L) := by
      have := Int.mul_ediv_add_emod A (2 ^ L)
      linarith
    rw [hsplit]
    exact dvd_sub hdvd (Dvd.dvd.mul_right (pow_dvd_pow 2 hvL) _)
  have hge : (2 : ℤ) ^ v ≤ A % 2 ^ L :=
    Int.le_of_dvd (lt_of_le_of_ne hR0 (Ne.symm hRne)) hdvdR
  have hle : (2 : ℤ) ^ v ≤ 2 ^ L - A % 2 ^ L :=
    Int.le_of_dvd (by linarith) (dvd_sub (pow_dvd_pow 2 hvL) hdvdR)
  exact ⟨by linarith, by linarith⟩

/-- **The additively stable lift.**  If every one of the `k` summands of the decomposition
`windowDiscrepancy_mul_shift` is divisible by `2^v`, with `2^v` above the *new* exclusion
radius, and the total is not divisible by `2^L`, the multiplied shift is certified.

This is a lift in the strict sense: hypotheses only about cells at the old shift `h`, a
conclusion about the shift `k·h`, uniform in `k`.  Its cost is stated honestly in the
module docstring: `2^v` must exceed `N + k·h + L + 2`, and the measured valuations of
real window discrepancies along the lcm ray are `1 … 6`. -/
theorem certifiedKill_lift_of_common_dvd {k h N L v : ℕ}
    (hdvd : ∀ i < k, (2 : ℤ) ^ v ∣ windowDiscrepancy h (N + i * h) L)
    (hne : ¬ ((2 : ℤ) ^ L ∣ windowDiscrepancy (k * h) N L))
    (hrad : ((N : ℤ) + (k * h : ℕ) + L + 2) < 2 ^ v) :
    certifiedKill (k * h) N L := by
  refine certifiedKill_of_two_pow_dvd ?_ hne hrad
  rw [windowDiscrepancy_mul_shift]
  exact Finset.dvd_sum fun i hi => hdvd i (Finset.mem_range.mp hi)

/-- **The off-diagonal ladder lift.**  The A3 lift law.  `e` is the fresh correction read
modulo `2^L`, `δ` bounds it; the hypothesis on the old cell is its *residue* clearing the
new exclusion radius by a further `δ`.  With `e = δ = 0` this is the verbatim transfer
`2^L ∣ (fresh correction) → certifiedKill H H L → certifiedKill ((k+1)·H) H L`.

Uniform in `k`, hence available at every prime-power boundary of the lcm ladder and so on
any infinite subfamily of them. -/
theorem certifiedKill_ladder_lift {k H L : ℕ} {e δ : ℤ}
    (hδ : |e| ≤ δ)
    (hcorr : (2 : ℤ) ^ L ∣
      ((∑ i ∈ Finset.range k, windowDiscrepancy H ((2 + i) * H) L) - e))
    (hlow : ((H : ℤ) + ((k + 1) * H : ℕ) + L + 2) + δ < windowDiscrepancy H H L % 2 ^ L)
    (hhigh : windowDiscrepancy H H L % 2 ^ L
        < 2 ^ L - (((H : ℤ) + ((k + 1) * H : ℕ) + L + 2) + δ)) :
    certifiedKill ((k + 1) * H) H L := by
  have h2L : (0 : ℤ) < 2 ^ L := by positivity
  have hMpos : (0 : ℤ) ≤ (H : ℤ) + ((k + 1) * H : ℕ) + L + 2 := by positivity
  have hr0 : 0 ≤ windowDiscrepancy H H L % 2 ^ L := Int.emod_nonneg _ (ne_of_gt h2L)
  have habs := abs_le.mp hδ
  have hgt : 0 ≤ windowDiscrepancy H H L % 2 ^ L + e := by linarith [habs.1]
  have hlt : windowDiscrepancy H H L % 2 ^ L + e < 2 ^ L := by linarith [habs.2]
  have hred : (windowDiscrepancy H H L % 2 ^ L + e) % 2 ^ L
      = windowDiscrepancy H H L % 2 ^ L + e := Int.emod_eq_of_lt hgt hlt
  have hsplit := windowDiscrepancy_ladder_offDiagonal k H L
  have hdvd : (2 : ℤ) ^ L ∣
      windowDiscrepancy ((k + 1) * H) H L - (windowDiscrepancy H H L % 2 ^ L + e) := by
    have h1 : (2 : ℤ) ^ L ∣ windowDiscrepancy H H L - windowDiscrepancy H H L % 2 ^ L := by
      refine ⟨windowDiscrepancy H H L / 2 ^ L, ?_⟩
      have := Int.mul_ediv_add_emod (windowDiscrepancy H H L) ((2 : ℤ) ^ L)
      linarith
    have hrw : windowDiscrepancy ((k + 1) * H) H L - (windowDiscrepancy H H L % 2 ^ L + e)
        = (windowDiscrepancy H H L - windowDiscrepancy H H L % 2 ^ L)
          + ((∑ i ∈ Finset.range k, windowDiscrepancy H ((2 + i) * H) L) - e) := by
      rw [hsplit]; ring
    rw [hrw]
    exact dvd_add h1 hcorr
  have hmod : windowDiscrepancy ((k + 1) * H) H L % 2 ^ L
      = windowDiscrepancy H H L % 2 ^ L + e := by
    rw [← hred]
    exact (Int.modEq_iff_dvd.mpr hdvd).symm
  exact ⟨by rw [hmod]; linarith [habs.1], by rw [hmod]; linarith [habs.2]⟩

/-- The doubling case, written out: at an lcm boundary `t + 1 = 2^m` the entire lift is
the residue of the single fresh cell `A_{H, 2H, L}`. -/
theorem certifiedKill_double_lift {H L : ℕ} {e δ : ℤ}
    (hδ : |e| ≤ δ)
    (hcorr : (2 : ℤ) ^ L ∣ (windowDiscrepancy H (2 * H) L - e))
    (hlow : ((H : ℤ) + (2 * H : ℕ) + L + 2) + δ < windowDiscrepancy H H L % 2 ^ L)
    (hhigh : windowDiscrepancy H H L % 2 ^ L
        < 2 ^ L - (((H : ℤ) + (2 * H : ℕ) + L + 2) + δ)) :
    certifiedKill (2 * H) H L := by
  have hk : (1 + 1) * H = 2 * H := by ring
  have hsum : (∑ i ∈ Finset.range 1, windowDiscrepancy H ((2 + i) * H) L)
      = windowDiscrepancy H (2 * H) L := by simp
  have := certifiedKill_ladder_lift (k := 1) (H := H) (L := L) (e := e) (δ := δ) hδ
    (by rw [hsum]; exact hcorr) (by rw [hk]; exact hlow) (by rw [hk]; exact hhigh)
  rwa [hk] at this

/-! ## 3. The obstruction: the fresh correction is not a perturbation

Everything below is kernel-decided. -/

/-- The certified cell: `A_{2,2,5} = 44`, residue `12`, exclusion radius `11`. -/
theorem certifiedKill_two_two_five : certifiedKill 2 2 5 := by decide

/-- The fresh correction at that cell: `A_{2,4,5} = 52`. -/
theorem windowDiscrepancy_two_four_five : windowDiscrepancy 2 4 5 = 52 := by decide

/-- The two summands, and the sum. -/
theorem windowDiscrepancy_two_two_five : windowDiscrepancy 2 2 5 = 44 := by decide

/-- **The correction can annihilate a certificate exactly.**  `44 + 52 = 96 ≡ 0 (mod 32)`:
the fresh cell moves the certified residue `12` to the exact centre of the forbidden zone.
So no bound `δ` short of `2^{L-1}` makes `certifiedKill_double_lift` unconditional. -/
theorem windowDiscrepancy_four_two_five_emod : windowDiscrepancy 4 2 5 % 2 ^ 5 = 0 := by
  decide

theorem not_certifiedKill_four_two_five : ¬ certifiedKill 4 2 5 := by decide

/-- The annihilation is an instance of `windowDiscrepancy_double_offDiagonal`, not a
coincidence of the definition. -/
theorem annihilation_is_the_decomposition :
    windowDiscrepancy 4 2 5 = windowDiscrepancy 2 2 5 + windowDiscrepancy 2 4 5 := by
  have := windowDiscrepancy_double_offDiagonal 2 5
  norm_num at this ⊢
  exact this

/-! ### The reverse failure, on the lcm ray

`periodLcm 3 = 6`, `periodLcm 4 = 12 = 2 · periodLcm 3`: a genuine doubling boundary of
the ladder.  At depth `6` the cell below is **not** certified and the doubled cell **is**.
The certificate at the doubled shift is therefore produced by arithmetic that the
certified scale below does not contain, in either direction. -/

theorem periodLcm_three : periodLcm 3 = 6 := by decide

theorem periodLcm_four : periodLcm 4 = 12 := by decide

/-- The cell below fails at depth `6`: residue `14`, radius `20`. -/
theorem not_certifiedKill_six_six_six : ¬ certifiedKill 6 6 6 := by decide

/-- The doubled cell, at the *old* base point, succeeds at the same depth: residue `36`,
radius `26`. -/
theorem certifiedKill_twelve_six_six : certifiedKill 12 6 6 := by decide

/-- On the lcm ray: `certifiedKill (periodLcm 4) (periodLcm 3) 6`. -/
theorem certifiedKill_periodLcm_offDiagonal_at_four :
    certifiedKill (periodLcm 4) (periodLcm 3) 6 := by
  rw [periodLcm_three, periodLcm_four]
  exact certifiedKill_twelve_six_six

/-- The values behind it: `270 + 278 = 548`. -/
theorem windowDiscrepancy_six_values :
    windowDiscrepancy 6 6 6 = 270 ∧ windowDiscrepancy 6 12 6 = 278
      ∧ windowDiscrepancy 12 6 6 = 548 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The correction's 2-adic valuation at that boundary is exactly `1`, where a verbatim
transfer needs `≥ 6`.  This is the divisibility route of `certifiedKill_lift_of_common_dvd`
failing by five bits at the very first doubling boundary large enough to be interesting. -/
theorem two_dvd_correction_six : (2 : ℤ) ∣ windowDiscrepancy 6 12 6 := by decide

theorem not_four_dvd_correction_six : ¬ ((2 : ℤ) ^ 2 ∣ windowDiscrepancy 6 12 6) := by
  decide

/-! ### What the free base point buys, at a corpus scale

`t = 7 → 8` is a doubling boundary (`periodLcm 8 = 840 = 2 · 420 = 2 · periodLcm 7`) and
`certifiedKill_periodLcm_diagonal_at_seven` deposits depth `14` there.  At that same depth
the diagonal cell one rung up fails and the off-diagonal cell one rung up succeeds. -/

/-- The diagonal route must buy a bit: depth `14` does not certify at `t = 8`.
(`certifiedKill_periodLcm_diagonal_at_eight` uses depth `15`.) -/
theorem not_certifiedKill_diagonal_at_eight_depth14 :
    ¬ certifiedKill (periodLcm 8) (periodLcm 8) 14 := by decide

/-- **The off-diagonal deposit at `t = 8`, at the depth of the deposit below.**  A
legitimate instance of the free-`N` supply hypothesis
`irrational_totient_series_of_lcm_certificate_supply`, and the first certificate in this
repository placed off the diagonal. -/
theorem certifiedKill_offDiagonal_at_eight_depth14 :
    certifiedKill (periodLcm 8) (periodLcm 7) 14 := by decide

/-! ## 4. The base point and the depth are not independent parameters

`Recon249`'s Result 6 proposes exploiting the free base point `N` of
`irrational_totient_series_of_lcm_certificate_supply`.  This section says how much of that
plane is genuinely free.  A cell sees its window only through the *right endpoint*
`N + L`: the residue modulo `2^j` of a depth-`L` discrepancy is exactly the depth-`j`
discrepancy with the same endpoint.  Consequently certification propagates along an
anti-diagonal `N + L = const` in the direction of *decreasing* base point.

The supply theorem wants increasing base point, so this trade runs the wrong way: sliding
the base point up while holding the endpoint fixed costs depth one-for-one, and sliding it
up at fixed depth is new arithmetic at every step (`windowDiscrepancy_shift_emod` of
`Recon249` prices it at one fresh totient pair). -/

private lemma emod_le_self_of_nonneg {X b : ℤ} (hX : 0 ≤ X) (hb : 0 < b) : X % b ≤ X := by
  have h1 := Int.mul_ediv_add_emod X b
  have h2 : 0 ≤ X / b := Int.ediv_nonneg hX hb.le
  nlinarith

/-- **Only the right endpoint matters.**  Modulo `2^j`, a depth-`L` window discrepancy is
the depth-`j` window discrepancy with the same right endpoint `N + L`.  The first `L - j`
offsets carry place value at least `2^j` and drop out. -/
theorem windowDiscrepancy_emod_pow (h N L j : ℕ) (hj : j ≤ L) :
    windowDiscrepancy h N L % 2 ^ j = windowDiscrepancy h (N + (L - j)) j % 2 ^ j := by
  have key : (∑ i ∈ Finset.range L,
        ((Nat.totient (N + h + 1 + i) : ℤ) - (Nat.totient (N + 1 + i) : ℤ)) * 2 ^ (L - 1 - i))
      = (∑ i ∈ Finset.range (L - j),
          ((Nat.totient (N + h + 1 + i) : ℤ) - (Nat.totient (N + 1 + i) : ℤ)) * 2 ^ (L - 1 - i))
        + ∑ i ∈ Finset.range j,
          ((Nat.totient (N + h + 1 + ((L - j) + i)) : ℤ)
            - (Nat.totient (N + 1 + ((L - j) + i)) : ℤ)) * 2 ^ (L - 1 - ((L - j) + i)) := by
    have h0 := Finset.sum_range_add
      (fun i => ((Nat.totient (N + h + 1 + i) : ℤ) - (Nat.totient (N + 1 + i) : ℤ))
        * 2 ^ (L - 1 - i)) (L - j) j
    rw [show (L - j) + j = L from by omega] at h0
    exact h0
  have htail : (∑ i ∈ Finset.range j,
      ((Nat.totient (N + h + 1 + ((L - j) + i)) : ℤ)
        - (Nat.totient (N + 1 + ((L - j) + i)) : ℤ)) * 2 ^ (L - 1 - ((L - j) + i)))
      = windowDiscrepancy h (N + (L - j)) j := by
    unfold windowDiscrepancy
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i < j := Finset.mem_range.mp hi
    rw [show N + h + 1 + ((L - j) + i) = N + (L - j) + h + 1 + i from by omega,
        show N + 1 + ((L - j) + i) = N + (L - j) + 1 + i from by omega,
        show L - 1 - ((L - j) + i) = j - 1 - i from by omega]
  have hhead : (2 : ℤ) ^ j ∣ ∑ i ∈ Finset.range (L - j),
      ((Nat.totient (N + h + 1 + i) : ℤ) - (Nat.totient (N + 1 + i) : ℤ)) * 2 ^ (L - 1 - i) := by
    refine Finset.dvd_sum fun i hi => ?_
    have hij : i < L - j := Finset.mem_range.mp hi
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
  have hW : windowDiscrepancy h N L
      = (∑ i ∈ Finset.range (L - j),
          ((Nat.totient (N + h + 1 + i) : ℤ) - (Nat.totient (N + 1 + i) : ℤ)) * 2 ^ (L - 1 - i))
        + windowDiscrepancy h (N + (L - j)) j := by
    rw [← htail]
    exact key
  obtain ⟨c, hc⟩ := hhead
  rw [hW, hc, show (2 : ℤ) ^ j * c + windowDiscrepancy h (N + (L - j)) j
      = windowDiscrepancy h (N + (L - j)) j + 2 ^ j * c from by ring]
  exact Int.add_mul_emod_self_left _ _ _

/-- **Certification propagates down the anti-diagonal.**  A depth-`j` certificate at base
point `N + (L - j)` yields a depth-`L` certificate at base point `N`: same right endpoint,
same exclusion radius, more depth. -/
theorem certifiedKill_of_endpoint {h N L j : ℕ} (hj : j ≤ L)
    (hcert : certifiedKill h (N + (L - j)) j) : certifiedKill h N L := by
  obtain ⟨hlo, hhi⟩ := hcert
  have h2j : (0 : ℤ) < 2 ^ j := by positivity
  have h2L : (0 : ℤ) < 2 ^ L := by positivity
  have hcast : ((N + (L - j) : ℕ) : ℤ) + h + j + 2 = (N : ℤ) + h + L + 2 := by
    push_cast [Nat.cast_sub hj]
    ring
  rw [hcast] at hlo hhi
  have hMpos : (0 : ℤ) ≤ (N : ℤ) + h + L + 2 := by positivity
  set r := windowDiscrepancy h (N + (L - j)) j % 2 ^ j with hrdef
  set R := windowDiscrepancy h N L % 2 ^ L with hRdef
  have hR0 : 0 ≤ R := Int.emod_nonneg _ (ne_of_gt h2L)
  have hRlt : R < 2 ^ L := Int.emod_lt_of_pos _ h2L
  have hRj : R % 2 ^ j = r := by
    rw [hRdef, Int.emod_emod_of_dvd _ (pow_dvd_pow 2 hj), hrdef]
    exact windowDiscrepancy_emod_pow h N L j hj
  -- lower bound
  have hlow : (N : ℤ) + h + L + 2 < R := by
    have := emod_le_self_of_nonneg hR0 h2j
    rw [hRj] at this
    linarith
  -- upper bound
  have hdvdRr : (2 : ℤ) ^ j ∣ R - r := by
    refine ⟨R / 2 ^ j, ?_⟩
    have := Int.mul_ediv_add_emod R ((2 : ℤ) ^ j)
    rw [hRj] at this
    linarith
  have hU0 : 0 ≤ 2 ^ L - R := by linarith
  have hUmod : (2 ^ L - R) % 2 ^ j = 2 ^ j - r := by
    have hdvd : (2 : ℤ) ^ j ∣ (2 ^ L - R) - (2 ^ j - r) := by
      have hrw : ((2 : ℤ) ^ L - R) - (2 ^ j - r) = (2 ^ L - 2 ^ j) - (R - r) := by ring
      rw [hrw]
      exact dvd_sub (dvd_sub (pow_dvd_pow 2 hj) dvd_rfl) hdvdRr
    have hlt : (2 : ℤ) ^ j - r < 2 ^ j := by linarith
    have hge : (0 : ℤ) ≤ 2 ^ j - r := by linarith
    have heq := Int.emod_eq_of_lt hge hlt
    obtain ⟨d, hd⟩ := hdvd
    rw [← heq]
    exact Int.modEq_iff_dvd.mpr ⟨-d, by rw [mul_neg, ← hd]; ring⟩
  have hupper : (N : ℤ) + h + L + 2 < 2 ^ L - R := by
    have := emod_le_self_of_nonneg hU0 h2j
    rw [hUmod] at this
    linarith
  exact ⟨hlow, by linarith⟩

/-- The same statement with the endpoint written out: `N + L = N' + j`. -/
theorem certifiedKill_of_endpoint' {h N L N' j : ℕ} (hj : j ≤ L) (hend : N + L = N' + j)
    (hcert : certifiedKill h N' j) : certifiedKill h N L := by
  refine certifiedKill_of_endpoint hj ?_
  rwa [show N + (L - j) = N' from by omega]

end AngleA3
end Lift
end ErdosProblems
