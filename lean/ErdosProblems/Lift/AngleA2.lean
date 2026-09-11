/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.LcmConeFlatness

/-!
# Angle A2: the 2-adic anatomy of the window discrepancy, and window monotonicity

`certifiedKill h N L` is a statement modulo `2^L` about

  `A_{h,N,L} = ∑_{j<L} (φ(N+h+1+j) − φ(N+1+j)) · 2^{L-1-j}`,

the depth-`L` window based at `N`.  This file works out the `2`-adic structure of
`A` under the two moves a lift can make — change of base point and change of depth —
and extracts one positive law and one negative law.

## 1. Low bits are a top-of-window phenomenon (`windowDiscrepancy_emod_truncate`)

  `A_{h,N,k+j} ≡ A_{h,N+j,k}  (mod 2^k)`.

Offset `d` of an `L`-deep window carries place value `2^{L-d}`, so the residue
modulo `2^k` sees only the last `k` offsets — and those last `k` offsets *are* the
depth-`k` window based at `N+j`.  Hence every `2`-adic divisibility fact about a deep
window is a fact about the shallow window sitting at its far end
(`two_pow_dvd_windowDiscrepancy_iff`).  This is the head-peel identity
`windowDiscrepancy_head_peel` iterated; it is not the `±1` slide recurrence
(`windowDiscrepancy_slide`) nor the depth recurrence (`windowDiscrepancy_succ`),
both of which move one letter at a time and lose the closed form.

## 2. Window monotonicity (`certifiedKill_of_window_subset`) — the positive law

The exclusion radius of `certifiedKill h N L` is `N + h + L + 2`, which depends on
base and depth only through the window **top** `N + L`.  Combining that with §1 gives
the geometric law

  **a certificate on a window survives on every window containing it**:
  `N ≤ M`, `M + k ≤ N + L`, `certifiedKill h M k` ⟹ `certifiedKill h N L`.

The depth half (`N = M`) is the corpus lemma `certifiedKill_add`.  The base half is
new: `certifiedKill_base_descent : certifiedKill h (N+j) k → certifiedKill h N (k+j)`,
proved here from the truncation congruence with no analysis at all.  It is the
finite, depth-accounted shadow of the fact that `{N : R_{N+h} − R_N ∈ ℤ}` is upward
closed (`D_{N+1} = 2 D_N − (φ(N+h+1) − φ(N+1))`).

Consequence for the ray formulation:
`irrational_totient_series_of_lcm_ray_certificate_supply` asks only for
a certificate at **some** cell of the ray `{(N, k) : N ≥ H_t}` — the diagonal cell
`(H_t, H_t)` then comes for free.  Historically this enlarged the then-open
`t = 67` cell to a two-parameter family.  The repository now directly certifies
that diagonal cell at minimal depth `100` and certifies the finite band through
`t ≤ 82`; this file's ray theorem is structural, not an unresolved certificate
claim.

## 2b. The ladder is antitone (`exists_diagonalKill_antitone`) — the sharp negative

Base descent plus the corpus' period-ray telescoping (`tail_diff_mul_mem_int`) gives

  `t ≤ s → P s → P t`,  where `P t := ∃ L, certifiedKill (H_t) (H_t) L`.

If `P t` fails then `R_{2H_t} − R_{H_t} ∈ ℤ`; base descent makes every
`R_{N+H_t} − R_N` with `N ≥ H_t` integral; telescoping over `H_s = m·H_t` then makes
`R_{2H_s} − R_{H_s}` integral, so `P s` fails.

So `P` is a **threshold predicate**: it holds exactly on an initial segment of `ℕ`.
Three consequences, all sharp:

* The `28` corpus deposits and the plateau argument certifying every `t ≤ 66` are
  *formal consequences* of any single certified cell above them — of the `t = 67`
  cell in particular.  The seed is downstream of the frontier, not upstream of it.
* `diagonalKill_cofinal_iff_all`: the `∀ t₀, ∃ t ≥ t₀` shape of the reduction is
  cosmetic; cofinal supply and total supply are the same statement.
* A lift `P t → P (t+1)` therefore has no hypothesis to consume that is not already
  implied by its own conclusion.  "Seed + locality" cannot be the architecture: the
  ladder has no downward-transmitted arithmetic content, because the implication runs
  the other way.

## 3. The `2`-adic sufficient criterion, and why it is unusable

`certifiedKill_of_two_pow_dvd`: if `2^v ∣ A`, `2^L ∤ A` and `N + h + L + 2 < 2^v`,
then `certifiedKill h N L` — a nonzero residue divisible by `2^v` cannot sit within
`2^v` of `0` in `ℤ/2^L`.  This sufficient criterion demands
`v > log₂(N + h + L + 2)`, i.e. `v ≥ 97` at
`t = 67`.  Section 1 says exactly where such a `v` would have to come from:
`certifiedKill_of_far_end_valuation` shows the required datum is `2^k`-divisibility
of the depth-`k` window at the **far end** of the target window, `2k ≥ 194` totient
values not supplied by the coefficient-dilation law from the rung below.
Measured `v₂(c_H(d))` at the recorded corpus samples runs `2 … 10`; the
criterion asks for `97`.  This rules out that measured sufficient criterion at
those samples, not every possible valuation argument.

## 4. Base freedom does not buy coverage (`ray_coverage_card_le`)

The gain in §2 is real but does not touch the lift.  The exact dilation law
`c_{pH}(p·e) = (p−1)·c_H(e)` reaches the offsets divisible by `p`, and in *every*
window of depth `k`, at *every* base `N`, there are at most `k/p + 1` of them.
Sliding the base leaves the proved count at most `k/p + 1`, asymptotically a
fraction near `1/p` for fixed `p` and large `k`.  At
`p = 67`, depth `100`: at most `2` of `100` offsets, uniformly in `N`
(`ray_coverage_at_67`).

## What is *not* proved here

No lift.  §2 moves certificates to *smaller* base points; the supply needs
arbitrarily *large* ones, and §4 says the enlarged target set is uniformly as
uncovered as the single diagonal cell was.  `base_descent_converse_fails` shows the
descent is strictly one-directional, so it cannot be run backwards to climb, and
§2b shows the ladder's implications all run downwards as well.
-/

namespace ErdosProblems
namespace Lift
namespace AngleA2

open Erdos249257.TotientTailPeriodKiller

/-! ## 1. Head peel and the truncation congruence -/

/-- **Head peel.**  Deepening a window at its *base* end is exact: the depth-`L+1`
window at `N` is the depth-`L` window at `N+1` plus the head letter at place value
`2^L`.  (Contrast `windowDiscrepancy_succ`, which deepens at the *far* end.) -/
theorem windowDiscrepancy_head_peel (h N L : ℕ) :
    windowDiscrepancy h N (L + 1)
      = ((Nat.totient (N + h + 1) : ℤ) - (Nat.totient (N + 1) : ℤ)) * 2 ^ L
        + windowDiscrepancy h (N + 1) L := by
  unfold windowDiscrepancy
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : N + h + 1 + (i + 1) = N + 1 + h + 1 + i := by omega
  have e2 : N + 1 + (i + 1) = N + 1 + 1 + i := by omega
  have e3 : L + 1 - 1 - (i + 1) = L - 1 - i := by omega
  rw [e1, e2, e3]

/-- **Low bits are a top-of-window phenomenon.**  The residue of the depth-`k+j`
window based at `N`, modulo `2^k`, equals the residue of the depth-`k` window based
at `N+j`: the two windows share their last `k` offsets, and those are the only
offsets whose place value is below `2^k`.

This is the exact `2`-adic locality law — everything a lift could hope to control by
`2`-adic valuation lives at the far end of the window. -/
theorem windowDiscrepancy_emod_truncate (h : ℕ) : ∀ (j N k : ℕ),
    windowDiscrepancy h N (k + j) % 2 ^ k = windowDiscrepancy h (N + j) k % 2 ^ k := by
  intro j
  induction j with
  | zero => intro N k; simp
  | succ j ih =>
      intro N k
      have hstep : windowDiscrepancy h N (k + (j + 1))
          = ((Nat.totient (N + h + 1) : ℤ) - (Nat.totient (N + 1) : ℤ)) * 2 ^ (k + j)
            + windowDiscrepancy h (N + 1) (k + j) := by
        rw [show k + (j + 1) = k + j + 1 by omega]
        exact windowDiscrepancy_head_peel h N (k + j)
      have hrw : ((Nat.totient (N + h + 1) : ℤ) - (Nat.totient (N + 1) : ℤ)) * 2 ^ (k + j)
            + windowDiscrepancy h (N + 1) (k + j)
          = windowDiscrepancy h (N + 1) (k + j)
            + 2 ^ k * (((Nat.totient (N + h + 1) : ℤ) - (Nat.totient (N + 1) : ℤ)) * 2 ^ j) := by
        rw [pow_add]; ring
      rw [hstep, hrw, Int.add_mul_emod_self_left, ih (N + 1) k,
        show N + 1 + j = N + (j + 1) by omega]

/-- **All `2`-adic divisibility of a window is carried by its far end.**  Restated
from `windowDiscrepancy_emod_truncate`: `2^k ∣ A_{h,N,k+j}` iff `2^k ∣ A_{h,N+j,k}`.
The `j` shallowest offsets — including every offset the dilation law reaches when the
window is short — are irrelevant to every congruence modulo `2^k`. -/
theorem two_pow_dvd_windowDiscrepancy_iff (h N k j : ℕ) :
    ((2 : ℤ) ^ k ∣ windowDiscrepancy h N (k + j))
      ↔ ((2 : ℤ) ^ k ∣ windowDiscrepancy h (N + j) k) := by
  constructor <;> intro hd
  · refine Int.dvd_of_emod_eq_zero ?_
    rw [← windowDiscrepancy_emod_truncate h j N k]
    exact Int.emod_eq_zero_of_dvd hd
  · refine Int.dvd_of_emod_eq_zero ?_
    rw [windowDiscrepancy_emod_truncate h j N k]
    exact Int.emod_eq_zero_of_dvd hd

/-! ## 2. Window monotonicity -/

/-- **Base descent.**  A certificate at base `N+j` and depth `k` upgrades to a
certificate at base `N` and depth `k+j`.

Both cells have the same window top `N + (k+j) = (N+j) + k`, hence *the same*
exclusion radius `N + h + (k+j) + 2 = (N+j) + h + k + 2`; and by
`windowDiscrepancy_emod_truncate` the deep residue reduces to the shallow one modulo
`2^k`.  A residue in `(B, 2^k − B)` therefore lifts to a residue in
`(B, 2^{k+j} − B)`: reduction mod `2^k` can only decrease a nonnegative residue, and
can raise its distance from the top of the range by at most `2^{k+j} − 2^k`. -/
theorem certifiedKill_base_descent {h N k j : ℕ}
    (hcert : certifiedKill h (N + j) k) : certifiedKill h N (k + j) := by
  unfold certifiedKill at hcert ⊢
  obtain ⟨hlo, hhi⟩ := hcert
  push_cast at hlo hhi ⊢
  have h2k : (0 : ℤ) < 2 ^ k := by positivity
  have h2kj : (0 : ℤ) < 2 ^ (k + j) := by positivity
  set R : ℤ := windowDiscrepancy h N (k + j) % 2 ^ (k + j) with hR
  have hr0 : 0 ≤ R := Int.emod_nonneg _ (ne_of_gt h2kj)
  have hrlt : R < 2 ^ (k + j) := Int.emod_lt_of_pos _ h2kj
  have hdvd : (2 : ℤ) ^ k ∣ 2 ^ (k + j) := pow_dvd_pow 2 (Nat.le_add_right k j)
  have hs : R % 2 ^ k = windowDiscrepancy h (N + j) k % 2 ^ k := by
    rw [hR, Int.emod_emod_of_dvd _ hdvd, windowDiscrepancy_emod_truncate h j N k]
  have hS0 : 0 ≤ R % 2 ^ k := Int.emod_nonneg _ (ne_of_gt h2k)
  have hslo : ((N : ℤ) + (j : ℤ) + (h : ℤ) + (k : ℤ) + 2) < R % 2 ^ k := by
    rw [hs]; linarith
  have hshi : R % 2 ^ k < 2 ^ k - ((N : ℤ) + (j : ℤ) + (h : ℤ) + (k : ℤ) + 2) := by
    rw [hs]; linarith
  have hdm : 2 ^ k * (R / 2 ^ k) + R % 2 ^ k = R := by
    rw [Int.emod_def]; ring
  have hq0 : 0 ≤ R / 2 ^ k := Int.ediv_nonneg hr0 (le_of_lt h2k)
  have hqmul0 : 0 ≤ 2 ^ k * (R / 2 ^ k) := mul_nonneg (le_of_lt h2k) hq0
  have hpa : (2 : ℤ) ^ k * 2 ^ j = 2 ^ (k + j) := (pow_add 2 k j).symm
  have hqlt : R / 2 ^ k < 2 ^ j := by
    by_contra hcon
    have hcon' : (2 : ℤ) ^ j ≤ R / 2 ^ k := not_lt.mp hcon
    have h1 : (2 : ℤ) ^ k * 2 ^ j ≤ 2 ^ k * (R / 2 ^ k) :=
      mul_le_mul_of_nonneg_left hcon' (le_of_lt h2k)
    rw [hpa] at h1
    linarith
  have hqle : R / 2 ^ k ≤ 2 ^ j - 1 := by linarith
  have hupper : 2 ^ k * (R / 2 ^ k) ≤ 2 ^ (k + j) - 2 ^ k := by
    have := mul_le_mul_of_nonneg_left hqle (le_of_lt h2k)
    have hexp : (2 : ℤ) ^ k * (2 ^ j - 1) = 2 ^ (k + j) - 2 ^ k := by
      rw [← hpa]; ring
    linarith [hexp ▸ this]
  exact ⟨by linarith, by linarith⟩

/-- **Window monotonicity.**  A certificate on the window `[M+1, M+k]` holds on every
window `[N+1, N+L]` containing it: base down, top up.  The depth half (`N = M`) is
`certifiedKill_add`; the base half is `certifiedKill_base_descent`. -/
theorem certifiedKill_of_window_subset {h M k N L : ℕ}
    (hbase : N ≤ M) (htop : M + k ≤ N + L) (hcert : certifiedKill h M k) :
    certifiedKill h N L := by
  have hMN : N + (M - N) = M := by omega
  have h1 : certifiedKill h N (k + (M - N)) :=
    certifiedKill_base_descent (by rwa [hMN])
  have h2 := certifiedKill_add h1 (L - (k + (M - N)))
  rwa [show k + (M - N) + (L - (k + (M - N))) = L by omega] at h2

/-- Certificates descend in the base point. -/
theorem exists_certifiedKill_of_base_le {h N M : ℕ} (hNM : N ≤ M)
    (hcert : ∃ k, certifiedKill h M k) : ∃ L, certifiedKill h N L := by
  obtain ⟨k, hk⟩ := hcert
  exact ⟨k + (M - N), certifiedKill_of_window_subset hNM (by omega) hk⟩

/-- **The diagonal cell is free once any cell above it on the ray is certified.**
The corpus deposits all sit on the diagonal `N = H`; this says the diagonal is the
*easiest* point of the ray, not a distinguished one. -/
theorem exists_certifiedKill_diagonal_of_ray {H N : ℕ} (hHN : H ≤ N)
    (hcert : ∃ k, certifiedKill H N k) : ∃ L, certifiedKill H H L :=
  exists_certifiedKill_of_base_le hHN hcert

/-- **The lift target is a ray target.**  To lift a certificate across the rung
`H ↦ p·H` it suffices to certify *any* cell `(N, k)` with `N ≥ p·H` on the period ray
of `p·H`; the diagonal cell then follows. -/
theorem lift_target_of_ray_cell {p H N k : ℕ} (hle : p * H ≤ N)
    (hcert : certifiedKill (p * H) N k) : ∃ L, certifiedKill (p * H) (p * H) L :=
  exists_certifiedKill_of_base_le hle ⟨k, hcert⟩

/-- **The wave-23 reduction with base freedom.**  A cofinal supply of certificates
anywhere on or above the lcm diagonal proves #249.  Strictly weaker hypothesis than
`irrational_totient_series_of_lcm_diagonal_certificate_supply`, which pins the base
to `N = H_t`. -/
theorem irrational_totient_series_of_lcm_ray_certificate_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ N, periodLcm t ≤ N ∧ ∃ k,
      certifiedKill (periodLcm t) N k) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_lcm_diagonal_certificate_supply fun t₀ => ?_
  obtain ⟨t, ht, N, hN, k, hk⟩ := hsupply t₀
  exact ⟨t, ht, exists_certifiedKill_of_base_le hN ⟨k, hk⟩⟩

/-! ### The ladder is antitone: the seed is a consequence, not a premise -/

/-- **Integrality of the tail difference is upward closed in the base.**  The
real-analytic form of `certifiedKill_base_descent`. -/
theorem tail_diff_int_of_base_le {h N M : ℕ} (hNM : N ≤ M)
    (hint : totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    totientTail (M + h) - totientTail M ∈ Set.range ((↑) : ℤ → ℝ) := by
  by_contra hcon
  obtain ⟨L, hL⟩ := exists_certifiedKill_of_base_le hNM
    (exists_certifiedKill_of_tail_diff_notMem_int hcon)
  exact tail_diff_notMem_int_of_certifiedKill hL hint

/-- **The diagonal ladder is antitone.**  `P t := ∃ L, certifiedKill (H_t) (H_t) L`
satisfies `t ≤ s → P s → P t`.

Proof: if `P t` fails then `R_{2H_t} − R_{H_t} ∈ ℤ`; by base descent every
`R_{N+H_t} − R_N` with `N ≥ H_t` is an integer; by period-ray telescoping
(`tail_diff_mul_mem_int`) so is `R_{N + m·H_t} − R_N`, and `H_s = m·H_t` with
`H_s ≥ H_t`, so `R_{2H_s} − R_{H_s} ∈ ℤ` and `P s` fails too.

Consequence: `P` is a threshold predicate — it holds exactly on an initial segment
of `ℕ` (possibly all of `ℕ`).  The 28 corpus deposits and the plateau argument that
certifies every `t ≤ 66` are therefore *formal consequences* of any single certified
cell above them.  A "seed + lift" architecture has no seed content to climb on: the
whole force sits in the lift. -/
theorem exists_diagonalKill_antitone {t s : ℕ} (hts : t ≤ s)
    (hs : ∃ L, certifiedKill (periodLcm s) (periodLcm s) L) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L := by
  by_contra hcon
  obtain ⟨L, hL⟩ := hs
  obtain ⟨m, hm⟩ := periodLcm_dvd_periodLcm hts
  have hHtHs : periodLcm t ≤ periodLcm s :=
    Nat.le_of_dvd (periodLcm_pos s) (periodLcm_dvd_periodLcm hts)
  have hall : ∀ N, periodLcm t ≤ N →
      totientTail (N + periodLcm t) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro N hN
    by_contra hn
    exact hcon (exists_certifiedKill_of_base_le hN
      (exists_certifiedKill_of_tail_diff_notMem_int hn))
  have hmul := tail_diff_mul_mem_int hall m (periodLcm s) hHtHs
  have hHs : periodLcm s + m * periodLcm t = periodLcm s + periodLcm s := by
    rw [hm]; ring
  rw [hHs] at hmul
  exact tail_diff_notMem_int_of_certifiedKill hL hmul

/-- **Cofinality buys nothing.**  Because `P` is antitone, a supply of diagonal kills
at arbitrarily large scales is the same statement as a diagonal kill at *every*
scale.  The reduction's `∀ t₀, ∃ t ≥ t₀` shape is cosmetic. -/
theorem diagonalKill_cofinal_iff_all :
    (∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L, certifiedKill (periodLcm t) (periodLcm t) L)
      ↔ (∀ t : ℕ, ∃ L, certifiedKill (periodLcm t) (periodLcm t) L) := by
  constructor
  · intro hcof t
    obtain ⟨s, hs, hL⟩ := hcof t
    exact exists_diagonalKill_antitone hs hL
  · intro hall t₀
    exact ⟨t₀, le_rfl, hall t₀⟩

/-- **The descent is strictly one-directional.**  `certifiedKill 1 0 5` holds while
`certifiedKill 1 1 4` — the window it strictly contains — fails.  So window
monotonicity cannot be reversed to climb from a low base to a high one, which is the
direction the supply theorem needs. -/
theorem base_descent_converse_fails :
    certifiedKill 1 0 5 ∧ ¬ certifiedKill 1 1 4 := by
  constructor
  · decide
  · decide

/-- Kernel check of `certifiedKill_base_descent` on a live instance: the corpus cell
`(N, L) = (12, 16)` at period `5` descends twelve base points to `(0, 28)`. -/
theorem certifiedKill_five_zero_twentyeight : certifiedKill 5 0 28 :=
  certifiedKill_base_descent (N := 0) (j := 12) (k := 16) (by decide)

/-! ## 3. The 2-adic sufficient criterion -/

/-- **Valuation criterion.**  A nonzero residue divisible by `2^v` is at distance at
least `2^v` from `0` in `ℤ/2^L`.  So if the window discrepancy has `2`-adic valuation
at least `v` but less than `L`, and `2^v` exceeds the exclusion radius, the
certificate fires.

This is the only way pure `2`-adic valuation control certifies a kill; the price is
`v > log₂(N + h + L + 2)`, which at the `t = 67` frontier means `v ≥ 97`. -/
theorem certifiedKill_of_two_pow_dvd {h N L v : ℕ}
    (hrad : ((N : ℤ) + (h : ℤ) + (L : ℤ) + 2) < 2 ^ v)
    (hdvd : (2 : ℤ) ^ v ∣ windowDiscrepancy h N L)
    (hnd : ¬ ((2 : ℤ) ^ L ∣ windowDiscrepancy h N L)) :
    certifiedKill h N L := by
  unfold certifiedKill
  have h2L : (0 : ℤ) < 2 ^ L := by positivity
  have hvL : v ≤ L := by
    by_contra hc
    exact hnd (dvd_trans (pow_dvd_pow 2 (le_of_lt (not_le.mp hc))) hdvd)
  have hpow : (2 : ℤ) ^ v ∣ 2 ^ L := pow_dvd_pow 2 hvL
  set R : ℤ := windowDiscrepancy h N L % 2 ^ L with hR
  have hr0 : 0 ≤ R := Int.emod_nonneg _ (ne_of_gt h2L)
  have hrlt : R < 2 ^ L := Int.emod_lt_of_pos _ h2L
  have hdvr : (2 : ℤ) ^ v ∣ R := by
    refine Int.dvd_of_emod_eq_zero ?_
    rw [hR, Int.emod_emod_of_dvd _ hpow]
    exact Int.emod_eq_zero_of_dvd hdvd
  have hrne : R ≠ 0 := fun h0 => hnd (Int.dvd_of_emod_eq_zero (hR ▸ h0))
  have hlow : (2 : ℤ) ^ v ≤ R := Int.le_of_dvd (lt_of_le_of_ne hr0 (Ne.symm hrne)) hdvr
  have hsubpos : (0 : ℤ) < 2 ^ L - R := by linarith
  have hhigh : (2 : ℤ) ^ v ≤ 2 ^ L - R := Int.le_of_dvd hsubpos (dvd_sub hpow hdvr)
  exact ⟨by linarith, by linarith⟩

/-- **Where the valuation would have to come from.**  Combining
`certifiedKill_of_two_pow_dvd` with `two_pow_dvd_windowDiscrepancy_iff`: a kill at
`(N, k+j)` follows from exact `2^k`-divisibility of the depth-`k` window at the far
end `N+j`, together with non-divisibility at full depth.  The certifying data is the
`2k` totient values `φ(N+j+h+1+i)`, `φ(N+j+1+i)` for `i < k` — all at the top of the
window, none of them supplied by the rung below. -/
theorem certifiedKill_of_far_end_valuation {h N k j : ℕ}
    (hrad : ((N : ℤ) + (h : ℤ) + ((k : ℤ) + (j : ℤ)) + 2) < 2 ^ k)
    (hdvd : (2 : ℤ) ^ k ∣ windowDiscrepancy h (N + j) k)
    (hnd : ¬ ((2 : ℤ) ^ (k + j) ∣ windowDiscrepancy h N (k + j))) :
    certifiedKill h N (k + j) := by
  refine certifiedKill_of_two_pow_dvd (v := k) ?_ ?_ hnd
  · push_cast
    linarith
  · exact (two_pow_dvd_windowDiscrepancy_iff h N k j).mpr hdvd

/-! ## 4. Base freedom does not improve dilation coverage -/

/-- **Uniform coverage bound.**  The exact dilation law `c_{pH}(p·e) = (p−1)·c_H(e)`
reaches exactly the offsets divisible by `p`.  In the depth-`k` window based at `N`
those offsets number at most `k/p + 1`, *uniformly in `N`*.  The base freedom bought
by `certifiedKill_of_window_subset` therefore leaves the covered fraction at `1/p`. -/
theorem ray_coverage_card_le (p N k : ℕ) :
    (((Finset.range k).filter (fun i => p ∣ (N + 1 + i))).card) ≤ k / p + 1 := by
  classical
  have hmaps : ∀ i ∈ (Finset.range k).filter (fun i => p ∣ (N + 1 + i)),
      i / p ∈ Finset.range (k / p + 1) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hle : i / p ≤ k / p := Nat.div_le_div_right (le_of_lt hik)
    exact Finset.mem_range.mpr (by omega)
  have hinj : Set.InjOn (fun i => i / p)
      ((Finset.range k).filter (fun i => p ∣ (N + 1 + i)) : Finset ℕ) := by
    intro a ha b hb hab
    have hda : p ∣ (N + 1 + a) := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hdb : p ∣ (N + 1 + b) := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    have hab' : a / p = b / p := hab
    have h1 : N + 1 + a ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hda
    have h2 : N + 1 + b ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hdb
    have h3 : a ≡ b [MOD p] := Nat.ModEq.add_left_cancel' (N + 1) (h1.trans h2.symm)
    have h4 : a % p = b % p := h3
    have e1 : p * (a / p) + a % p = a := Nat.div_add_mod a p
    have e2 : p * (b / p) + b % p = b := Nat.div_add_mod b p
    rw [hab', h4] at e1
    exact e1.symm.trans e2
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

/-- **The dilation law in general position.**  For `p` prime coprime to both `m` and
`m + H`, `φ(p(m+H)) − φ(pm) = (p−1)·(φ(m+H) − φ(m))`.  This is the base-free form of
`Recon249.diagCoeff_lift_coprime`, which only covers the diagonal `m = 1`. -/
theorem window_letter_dilation {p m H : ℕ} (hp : p.Prime)
    (hm : ¬ p ∣ m) (hmH : ¬ p ∣ (m + H)) :
    (Nat.totient (p * (m + H)) : ℤ) - (Nat.totient (p * m) : ℤ)
      = ((p : ℤ) - 1) * ((Nat.totient (m + H) : ℤ) - (Nat.totient m : ℤ)) := by
  have hc1 : Nat.Coprime p (m + H) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hmH
  have hc2 : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  have h1 : Nat.totient (p * (m + H)) = (p - 1) * Nat.totient (m + H) := by
    rw [Nat.totient_mul hc1, Nat.totient_prime hp]
  have h2 : Nat.totient (p * m) = (p - 1) * Nat.totient m := by
    rw [Nat.totient_mul hc2, Nat.totient_prime hp]
  rw [h1, h2]
  have hp1 : 1 ≤ p := hp.one_lt.le
  push_cast [Nat.cast_sub hp1]
  ring

/-- **The covered letters of a lifted window, at every base.**  If the offset `i` of
the depth-`k` window based at `N` for the period `p·H` is covered — `N+1+i = p·m`
with `p ∤ m` and `p ∤ m+H` — then its letter is `(p−1)` times the period-`H` letter
at `m`.  `ray_coverage_card_le` bounds the number of such `i` by `k/p + 1`, uniformly
in `N`: the base freedom won in §2 buys no extra coverage. -/
theorem window_letter_dilation_at {p H N i m : ℕ} (hp : p.Prime)
    (hm : N + 1 + i = p * m) (hmp : ¬ p ∣ m) (hmHp : ¬ p ∣ (m + H)) :
    (Nat.totient (N + p * H + 1 + i) : ℤ) - (Nat.totient (N + 1 + i) : ℤ)
      = ((p : ℤ) - 1) * ((Nat.totient (m + H) : ℤ) - (Nat.totient m : ℤ)) := by
  have hdist : p * (m + H) = p * m + p * H := by ring
  have hrw : N + p * H + 1 + i = p * (m + H) := by omega
  rw [hrw, hm]
  exact window_letter_dilation hp hmp hmHp

/-- **Coverage at the historical `p = 67` cell.**  At depth `100`, now known to
be the exact minimal diagonal depth there, at most `2` of the `100` offsets are
reached by the exact dilation law at every base point `N`. -/
theorem ray_coverage_at_67 (N : ℕ) :
    (((Finset.range 100).filter (fun i => 67 ∣ (N + 1 + i))).card) ≤ 2 := by
  have h := ray_coverage_card_le 67 N 100
  norm_num at h
  exact h

end AngleA2
end Lift
end ErdosProblems
