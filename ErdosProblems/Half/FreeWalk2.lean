/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleA2

/-!
# The free-`N` walk: consecutive certificate failures, measured and bounded

The `#249` supply hypotheses
(`irrational_totient_series_of_lcm_certificate_supply` and its ray form
`irrational_totient_series_of_lcm_ray_certificate_supply`) all quantify
`∃ N ≥ N₀, ∃ L, certifiedKill h N L`.  The base point `N` is free, and the
`N`-slide recurrence `Recon249.windowDiscrepancy_shift_emod`

  `A_{h,N+1,L} ≡ 2·A_{h,N,L} + (φ(N+h+1+L) − φ(N+1+L))  (mod 2^L)`

advances it at a cost of **one** totient pair per step, against `2L` totients for a
fresh cell.  The certificate fails exactly when `A_{h,N,L}` lands within
`r = N+h+L+2` of `0` in `ℤ/2^L`; the step map is the doubling map, doubling expands
intervals, and the hope was that failures therefore cannot persist along `N` — i.e.
that some absolute constant `K` bounds the length of a run of consecutive failures.

**They can persist, and no absolute `K` exists.**  This file settles the question,
in both directions.

## What the walk actually is

The `N`-step at depth `L` and the depth-step at base `N` are *the same map*:

  `A_{h,N,L+1} = 2·A_{h,N,L} + (φ(N+h+1+L) − φ(N+1+L))`   (`windowDiscrepancy_succ`)
  `A_{h,N+1,L} = A_{h,N,L+1} − (φ(N+h+1) − φ(N+1))·2^L`   (`windowDiscrepancy_slide`)

so `A_{h,N+1,L} ≡ A_{h,N,L+1} (mod 2^L)`, and the two exclusion radii agree on the
nose: `(N+1)+h+L+2 = N+h+(L+1)+2`.  The corpus already exploits one direction of
this — `certifiedKill_add` (depth) and `AngleA2.certifiedKill_base_descent` (base),
combined in `AngleA2.certifiedKill_of_window_subset`.  What was missing is the
**converse**, and it is the converse that pins run lengths.

`certifiedKill_depth_split`: if `4·(N+h+L+2) < 2^L` then

  `certifiedKill h N (L+1) → certifiedKill h N L ∨ certifiedKill h (N+1) L`.

Under the displayed size hypothesis at every required step, iterating
(`exists_certifiedKill_shift`) and pairing with window monotonicity gives
`certifiedKill_window_iff`:

  `certifiedKill h N (L+K) ↔ ∃ j ≤ K, certifiedKill h (N+j) L`,

hence the conditional equivalence `consecutiveFail_iff`:

  **the `K+1` cells `(N, L), …, (N+K, L)` all fail  ⟺  the single cell `(N, L+K)`
  fails.**

Within that size regime, a run of consecutive failures along the free `N`
is equivalent to a single failure further up the depth ladder.  Outside it,
only the one-way implication from a deep failure to a consecutive run is
proved.  Therefore the unqualified claim that every run length equals
`Lmin(h,N) − L` is retracted.  The constant `4` is sharp for the split theorem:
the adversarial verifier gives a kernel-checked counterexample with `3`.

## The measurement (python3, sieved `φ` to `4·10⁶`)

Run lengths along `N` at fixed `(h, L)`, `N ∈ [10⁵, 1.1·10⁶)` (`T = 10⁶` bases):

| `h` | `L=24` | `26` | `28` | `30` | `32` | `34` | `36` | `38` | `40` |
|---|---|---|---|---|---|---|---|---|---|
| `1`       | 16 | 14 | 12 | 10 | 8 | 6 | 4 | 2 | 0 |
| `2`       | 17 | 15 | 13 | 11 | 9 | 7 | 5 | 3 | 1 |
| `6`       | 16 | 14 | 12 | 10 | 8 | 6 | 4 | 2 | 0 |
| `60`      | 16 | 14 | 12 | 10 | 8 | 6 | 4 | 2 | 0 |
| `2520`    | 15 | 13 | 11 |  9 | 7 | 5 | 3 | 1 | 0 |
| `1792560` | 18 | 16 | 14 | 12 | 10 | 8 | 6 | 4 | 2 |

Each row falls by exactly `1` per unit of depth, and the maximising base `N` is the
*same* at every depth (e.g. `N = 727170` for `h = 1`, `N = 647178` for `h = 2`).
That is `consecutiveFail_iff` in raw form.  The full run-length histograms are exactly
geometric with ratio `1/2`; for `h = 1, L = 24`: `18112, 8982, 4481, 2224, 1068, 532,
283, 138, 71, 31, 9, 8, 7, 0, 3, 1` for lengths `1 … 16`.

Equivalently, in terms of the least certifying depth `Lmin(h,N)` and the depth floor
`F(h,N) = min{L : 2(N+h+L+2) < 2^L}` forced by `certifiedKill_depth_floor`, the
excess `e = Lmin − F` over `N ∈ [10³, 2·10⁵)`:

  `h=1  : e=0:57767  1:70494  2:35291  3:17680  4:8859  5:4475  6:2197  7:1102`
  `       8:565  9:272  10:135  11:82  12:43  13:17  14:14  15:5  16:1  17:1`

— again a clean geometric `1/2` tail, maximum `e = 17` (`h=1`), `22` (`h=6`),
`21` (`h=2520`) over `199000` bases.  The run at depth `L = F + c` has length
`(e − c)⁺`, so the maximum run over `T` bases scales as `log₂ T − c`: it grows
without bound as the scan lengthens, and shrinks by exactly one per unit of depth
excess `c`.  A previous measurement finding "runs of at most 2 at depth `log₂+4`"
sampled only multiples of `h₀`, i.e. `T/h₀` bases rather than `T`; the shortfall is
about `log₂ h₀`.

Sharpness of the constant `4` in `certifiedKill_depth_split`, on the grid
`h ∈ {1,2,3,6,60,2520,1792560}`, `4 ≤ L ≤ 39`, `N < 1.2·10⁵` in steps of `331`,
restricted in each row to the stated hypothesis:
`2^L > 1·(N+h+L+2)`: 1034 counterexamples out of 59349;
`> 2·(…)`: 470 / 56809; `> 3·(…)`: 6 / 55055; `> 4·(…)`: **0** / 54267.
The first `κ = 3` counterexample is `(h, N, L) = (1, 10592, 15)`.

## The negative, plainly

**No absolute bound `K` on consecutive failures is proved here, and the data says
none exists.**  Three kernel-checked counterexamples, each at a depth `L` that is
*not* degenerate (`2(N+h+L+2) < 2^L`, so `certifiedKill_depth_floor` does not
already forbid a certificate there), and each terminated by an actual certificate
one step later:

* `freeWalk_run_13` : `13` consecutive failures, `h = 26`, `L = 7`, `N = 3 … 15`;
* `freeWalk_run_17` : `17` consecutive failures, `h = 22`, `L = 16`, `N = 4518 … 4534`;
* `freeWalk_run_19` : `19` consecutive failures, `h = 22`, `L = 14`, `N = 4518 … 4536`.

The `17`-run lies inside the size regime of `consecutiveFail_iff`.  The
`13`- and `19`-runs do not: for them only
`consecutiveFail_of_deep_fail` supplies the one-way certification.  Thus the
three examples are kernel-checked long runs, but not all are equivalences with
one deeper cell.  An absolute bound `K` on runs at the floor
would be exactly the statement `Lmin(h,N) ≤ F(h,N) + K` for all `h, N` — a
quantitative irrationality statement about `∑ φ(n)/2ⁿ` strictly stronger than #249
itself.  The doubling map does expand intervals, but it expands them *around the
fresh totient letter*, and `|φ(N+h+1+L) − φ(N+1+L)| ≤ N+h+L+1 = r − 1` places that
letter inside the failure corridor at every step: the failure set is carried forward
by the step map, halved but never emptied.  That is `certifiedKill_depth_split`
read backwards, and it is why the free-`N` walk cannot be cheaper than the depth
ladder it duplicates.

Nothing in this file assumes or implies anything about the value of `∑ φ(n)/2ⁿ`.
-/

namespace ErdosProblems
namespace Half
namespace FreeWalk2

open Erdos249257 Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Lift.AngleA2

/-! ## 1.  The depth split: the converse of window monotonicity -/

/-- The purely arithmetic core of the depth split.  `a` is the depth-`L` residue,
`d` the fresh totient letter, `u` the depth-`(L+1)` residue and `v` the residue of
the same integer modulo `2^L` — which by `windowDiscrepancy_emod_truncate` is the
base-`(N+1)`, depth-`L` residue.  If the depth-`(L+1)` cell certifies while both
depth-`L` cells fail, the size constraints are contradictory once `4r < P`. -/
private lemma split_arith {P r a d u v : ℤ}
    (hP : 4 * r < P) (hr : 2 ≤ r)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hdlo : -(r - 1) ≤ d) (hdhi : d ≤ r - 1)
    (hu : u = (2 * a + d) % (2 * P)) (hv : v = (2 * a + d) % P)
    (hc1 : r + 1 < u) (hc2 : u < 2 * P - (r + 1))
    (hfail1 : a ≤ r ∨ P - r ≤ a)
    (hfail2 : v ≤ r + 1 ∨ P - (r + 1) ≤ v) : False := by
  have hP0 : 0 < P := by omega
  rcases lt_or_ge (2 * a + d) 0 with hneg | hnn
  · -- `t < 0`: the deep residue sits just below `2P`, outside the certificate arc
    have h1 : (2 * a + d) % (2 * P) = 2 * a + d + 2 * P := by
      have e1 : (2 * a + d + 2 * P * 1) % (2 * P) = (2 * a + d) % (2 * P) :=
        Int.add_mul_emod_self_left _ _ _
      rw [mul_one] at e1
      rw [← e1]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    omega
  · rcases lt_or_ge (2 * a + d) P with hlow | hhigh
    · -- `0 ≤ t < P`
      have h1 : (2 * a + d) % (2 * P) = 2 * a + d :=
        Int.emod_eq_of_lt (by omega) (by omega)
      have h2 : (2 * a + d) % P = 2 * a + d := Int.emod_eq_of_lt (by omega) (by omega)
      omega
    · rcases lt_or_ge (2 * a + d) (2 * P) with hmid | htop
      · -- `P ≤ t < 2P`
        have h1 : (2 * a + d) % (2 * P) = 2 * a + d :=
          Int.emod_eq_of_lt (by omega) (by omega)
        have h2 : (2 * a + d) % P = 2 * a + d - P := by
          have e1 : (2 * a + d + P * (-1)) % P = (2 * a + d) % P :=
            Int.add_mul_emod_self_left _ _ _
          rw [show 2 * a + d + P * (-1) = 2 * a + d - P by ring] at e1
          rw [← e1]
          exact Int.emod_eq_of_lt (by omega) (by omega)
        omega
      · -- `2P ≤ t`
        have h1 : (2 * a + d) % (2 * P) = 2 * a + d - 2 * P := by
          have e1 : (2 * a + d + 2 * P * (-1)) % (2 * P) = (2 * a + d) % (2 * P) :=
            Int.add_mul_emod_self_left _ _ _
          rw [show 2 * a + d + 2 * P * (-1) = 2 * a + d - 2 * P by ring] at e1
          rw [← e1]
          exact Int.emod_eq_of_lt (by omega) (by omega)
        omega

/-- **Depth split.**  Below the doubling threshold `4·(N+h+L+2) < 2^L`, a certificate
at depth `L+1` based at `N` is *nothing but* a certificate at depth `L` based at `N`
or at `N+1`.

This is the exact converse of the two corpus monotonicities `certifiedKill_add`
(depth) and `AngleA2.certifiedKill_base_descent` (base): together they say the
depth ladder and the free-`N` walk are one and the same ladder. -/
theorem certifiedKill_depth_split {h N L : ℕ}
    (hdeep : 4 * ((N : ℤ) + (h : ℤ) + (L : ℤ) + 2) < 2 ^ L)
    (hcert : certifiedKill h N (L + 1)) :
    certifiedKill h N L ∨ certifiedKill h (N + 1) L := by
  by_contra hcon
  have hn1 : ¬ certifiedKill h N L := fun hk => hcon (Or.inl hk)
  have hn2 : ¬ certifiedKill h (N + 1) L := fun hk => hcon (Or.inr hk)
  have hQ : (2 : ℤ) ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have hAq := Int.mul_ediv_add_emod (windowDiscrepancy h N L) ((2 : ℤ) ^ L)
  have hsucc := windowDiscrepancy_succ h N L
  have hdabs := abs_deltaTotient_le h (N + L + 1)
  rw [abs_le] at hdabs
  push_cast at hdabs
  have htrunc : windowDiscrepancy h N (L + 1) % (2 : ℤ) ^ L
      = windowDiscrepancy h (N + 1) L % (2 : ℤ) ^ L := by
    simpa using windowDiscrepancy_emod_truncate h 1 N L
  have key2P : windowDiscrepancy h N (L + 1) % (2 * 2 ^ L)
      = (2 * (windowDiscrepancy h N L % 2 ^ L) + deltaTotient h (N + L + 1))
          % (2 * 2 ^ L) := by
    rw [hsucc]
    have hrw : 2 * windowDiscrepancy h N L + deltaTotient h (N + L + 1)
        = (2 * (windowDiscrepancy h N L % 2 ^ L) + deltaTotient h (N + L + 1))
          + 2 * 2 ^ L * (windowDiscrepancy h N L / 2 ^ L) := by linarith [hAq]
    rw [hrw, Int.add_mul_emod_self_left]
  have keyP : windowDiscrepancy h (N + 1) L % (2 : ℤ) ^ L
      = (2 * (windowDiscrepancy h N L % 2 ^ L) + deltaTotient h (N + L + 1)) % 2 ^ L := by
    rw [← htrunc, hsucc]
    have hrw : 2 * windowDiscrepancy h N L + deltaTotient h (N + L + 1)
        = (2 * (windowDiscrepancy h N L % 2 ^ L) + deltaTotient h (N + L + 1))
          + 2 ^ L * (2 * (windowDiscrepancy h N L / 2 ^ L)) := by linarith [hAq]
    rw [hrw, Int.add_mul_emod_self_left]
  have hP0 : (0 : ℤ) < 2 ^ L := by positivity
  obtain ⟨hc1, hc2⟩ := hcert
  rw [hQ, key2P] at hc1 hc2
  push_cast at hc1 hc2
  refine split_arith (P := (2 : ℤ) ^ L) (r := (N : ℤ) + (h : ℤ) + (L : ℤ) + 2)
      (a := windowDiscrepancy h N L % 2 ^ L) (d := deltaTotient h (N + L + 1))
      (u := (2 * (windowDiscrepancy h N L % 2 ^ L) + deltaTotient h (N + L + 1))
              % (2 * 2 ^ L))
      (v := windowDiscrepancy h (N + 1) L % 2 ^ L)
      hdeep (by omega) (Int.emod_nonneg _ (ne_of_gt hP0))
      (Int.emod_lt_of_pos _ hP0) (by omega) (by omega) rfl keyP (by omega) (by omega)
      ?_ ?_
  · rcases not_and_or.mp hn1 with hx | hx
    · exact Or.inl (not_lt.mp hx)
    · exact Or.inr (by have := not_lt.mp hx; omega)
  · rcases not_and_or.mp hn2 with hx | hx
    · exact Or.inl (by have := not_lt.mp hx; push_cast at this; omega)
    · exact Or.inr (by have := not_lt.mp hx; push_cast at this; omega)

/-- **The deep cell is the disjunction of the shallow walk.**  Iterated depth split:
a certificate at depth `L+K` based at `N` forces a certificate at depth `L` at one of
the `K+1` bases `N, N+1, …, N+K`. -/
theorem exists_certifiedKill_shift {h N L K : ℕ}
    (hdeep : 4 * ((N : ℤ) + (K : ℤ) + (h : ℤ) + (L : ℤ) + 2) < 2 ^ L)
    (hcert : certifiedKill h N (L + K)) :
    ∃ j ≤ K, certifiedKill h (N + j) L := by
  induction K generalizing N with
  | zero => exact ⟨0, le_refl 0, by simpa using hcert⟩
  | succ K ih =>
      have hpow : (2 : ℤ) ^ L ≤ 2 ^ (L + K) := by
        have hn : (2 : ℕ) ^ L ≤ 2 ^ (L + K) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right L K)
        exact_mod_cast hn
      have hstep : 4 * ((N : ℤ) + (h : ℤ) + ((L + K : ℕ) : ℤ) + 2) < 2 ^ (L + K) := by
        push_cast
        push_cast at hdeep
        omega
      have hcert' : certifiedKill h N ((L + K) + 1) := by
        rwa [show L + (K + 1) = L + K + 1 by omega] at hcert
      rcases certifiedKill_depth_split hstep hcert' with hA | hB
      · obtain ⟨j, hj, hjc⟩ := ih (N := N) (by push_cast at hdeep ⊢; omega) hA
        exact ⟨j, by omega, hjc⟩
      · obtain ⟨j, hj, hjc⟩ := ih (N := N + 1) (by push_cast at hdeep ⊢; omega) hB
        refine ⟨j + 1, by omega, ?_⟩
        rwa [show N + 1 + j = N + (j + 1) by omega] at hjc

/-- **The window law, both directions.**  Below the doubling threshold, a depth-`L+K`
certificate at base `N` is exactly a depth-`L` certificate somewhere on the free-`N`
walk `N, …, N+K`.  The `←` direction is `AngleA2.certifiedKill_of_window_subset`
and needs no hypothesis; the `→` direction is `exists_certifiedKill_shift`. -/
theorem certifiedKill_window_iff {h N L K : ℕ}
    (hdeep : 4 * ((N : ℤ) + (K : ℤ) + (h : ℤ) + (L : ℤ) + 2) < 2 ^ L) :
    certifiedKill h N (L + K) ↔ ∃ j ≤ K, certifiedKill h (N + j) L := by
  refine ⟨exists_certifiedKill_shift hdeep, ?_⟩
  rintro ⟨j, hj, hjc⟩
  exact certifiedKill_of_window_subset (Nat.le_add_right N j) (by omega) hjc

/-! ## 2.  Runs of consecutive failures along the free `N` -/

/-- `ConsecutiveFail h N L K`: the `K+1` cells `(N, L), (N+1, L), …, (N+K, L)` all
fail to certify — a run of `K+1` consecutive failures along the free base point. -/
def ConsecutiveFail (h N L K : ℕ) : Prop := ∀ j ≤ K, ¬ certifiedKill h (N + j) L

instance (h N L K : ℕ) : Decidable (ConsecutiveFail h N L K) :=
  inferInstanceAs (Decidable (∀ j ≤ K, _))

/-- **Long runs come from one deep failure.**  Hypothesis-free direction: a single
failure at `(N, L+K)` produces `K+1` consecutive failures along `N` at depth `L`. -/
theorem consecutiveFail_of_deep_fail {h N L K : ℕ}
    (hfail : ¬ certifiedKill h N (L + K)) : ConsecutiveFail h N L K := fun j hj hk =>
  hfail (certifiedKill_of_window_subset (Nat.le_add_right N j) (by omega) hk)

/-- **Runs are no longer than that.**  Below the doubling threshold, `K+1`
consecutive failures force the single deep failure back. -/
theorem deep_fail_of_consecutiveFail {h N L K : ℕ}
    (hdeep : 4 * ((N : ℤ) + (K : ℤ) + (h : ℤ) + (L : ℤ) + 2) < 2 ^ L)
    (hrun : ConsecutiveFail h N L K) : ¬ certifiedKill h N (L + K) := by
  intro hc
  obtain ⟨j, hj, hjc⟩ := exists_certifiedKill_shift hdeep hc
  exact hrun j hj hjc

/-- **The run law.**  `K+1` consecutive failures along the free `N` at depth `L`
*is* a single failure at depth `L+K`.  Consequently the run of failures starting at
`N` has length exactly `Lmin(h,N) − L`, where `Lmin(h,N)` is the least certifying
depth at base `N`: the free-`N` walk is the depth ladder in disguise. -/
theorem consecutiveFail_iff {h N L K : ℕ}
    (hdeep : 4 * ((N : ℤ) + (K : ℤ) + (h : ℤ) + (L : ℤ) + 2) < 2 ^ L) :
    ConsecutiveFail h N L K ↔ ¬ certifiedKill h N (L + K) :=
  ⟨deep_fail_of_consecutiveFail hdeep, consecutiveFail_of_deep_fail⟩

/-- An unending run at depth `L` from base `N` is exactly the failure of the whole
free-`N` walk at that depth.  Note the depth hypothesis of `consecutiveFail_iff`
degrades as `K` grows at fixed `L`, so this equivalence is the honest unconditional
one: it does *not* upgrade to `∀ K, ¬ certifiedKill h N (L+K)`. -/
theorem forall_consecutiveFail_iff {h N L : ℕ} :
    (∀ K, ConsecutiveFail h N L K) ↔ ∀ j, ¬ certifiedKill h (N + j) L := by
  constructor
  · intro hall j
    exact hall j j (le_refl j)
  · intro hall K j _
    exact hall j

/-! ## 3.  Kernel-checked long runs at non-degenerate depth

`certifiedKill_depth_floor` forbids any certificate at `(h, N, L)` with
`2^L ≤ 2(N+h+L+2)`.  Each witness below sits strictly above that floor, so the
failures are genuine failures and not an artefact of a depth that was never viable;
each is also terminated by an explicit certificate one step further along `N`. -/

/-- The deep failure behind the `h = 26` run. -/
theorem fail_26_3_19 : ¬ certifiedKill 26 3 19 := by decide +kernel

/-- Depth `7` is live at `(h, N) = (26, 3)`: the floor of `certifiedKill_depth_floor`
is cleared with room to spare. -/
theorem depth_seven_nondegenerate : 2 * ((3 : ℤ) + 26 + 7 + 2) < 2 ^ 7 := by norm_num

/-- **Thirteen consecutive failures** along the free `N`, at period `h = 26` and
depth `L = 7`: bases `N = 3, 4, …, 15`. -/
theorem freeWalk_run_13 : ConsecutiveFail 26 3 7 12 :=
  consecutiveFail_of_deep_fail fail_26_3_19

/-- The run ends: base `16` certifies at the same depth `7`. -/
theorem freeWalk_run_13_sharp : certifiedKill 26 16 7 := by decide +kernel

/-- The deep failure behind the `h = 22` runs; `Lmin(22, 4518) = 33`. -/
theorem fail_22_4518_32 : ¬ certifiedKill 22 4518 32 := by decide +kernel

/-- Depth `14` is live at `(h, N) = (22, 4518)`. -/
theorem depth_fourteen_nondegenerate : 2 * ((4518 : ℤ) + 22 + 14 + 2) < 2 ^ 14 := by
  norm_num

/-- **Nineteen consecutive failures** along the free `N`, at period `h = 22` and
depth `L = 14`: bases `N = 4518, …, 4536`.  Depth `14` is the certificate's own
floor at this scale, and it is live — `freeWalk_run_19_sharp` certifies at `4537`. -/
theorem freeWalk_run_19 : ConsecutiveFail 22 4518 14 18 :=
  consecutiveFail_of_deep_fail fail_22_4518_32

/-- The run ends: base `4537` certifies at depth `14`. -/
theorem freeWalk_run_19_sharp : certifiedKill 22 4537 14 := by decide +kernel

/-- The `h = 22`, `L = 14` run is exactly `19` long. -/
theorem freeWalk_run_19_exact :
    ConsecutiveFail 22 4518 14 18 ∧ ¬ ConsecutiveFail 22 4518 14 19 :=
  ⟨freeWalk_run_19, fun hrun => hrun 19 (le_refl 19) freeWalk_run_19_sharp⟩

/-- **Seventeen consecutive failures**, same period, at depth `L = 16` — where the
doubling threshold `4·(N+K+h+L+2) < 2^L` *does* hold, so `consecutiveFail_iff`
applies and the run length `17` is exactly `Lmin(22,4518) − 16 = 33 − 16`. -/
theorem freeWalk_run_17 : ConsecutiveFail 22 4518 16 16 :=
  consecutiveFail_of_deep_fail fail_22_4518_32

/-- The doubling threshold holds for `freeWalk_run_17`, so that run is governed by
the two-sided law `consecutiveFail_iff`. -/
theorem freeWalk_run_17_threshold :
    4 * ((4518 : ℤ) + 16 + 22 + 16 + 2) < 2 ^ 16 := by norm_num

/-- …and it is exactly `17` long: base `4535` certifies at depth `16`. -/
theorem freeWalk_run_17_sharp : certifiedKill 22 4535 16 := by decide +kernel

/-- The exact form of the previous three: at `(h, L) = (22, 16)` and base `4518`
the run of consecutive failures has length exactly `17`, established through the
two-sided law rather than by enumeration. -/
theorem freeWalk_run_17_exact :
    ConsecutiveFail 22 4518 16 16 ∧ ¬ ConsecutiveFail 22 4518 16 17 := by
  refine ⟨freeWalk_run_17, fun hrun => ?_⟩
  exact hrun 17 (le_refl 17) freeWalk_run_17_sharp

/-- **The negative, as a statement.**  For each `K ∈ {12, 16, 18}` there is a period
`h`, a base `N` and a depth `L` clearing the depth floor `2(N+h+L+2) < 2^L` at which
`K+1` consecutive bases all fail.  No absolute bound on run length is proved here,
and by `consecutiveFail_iff` any such bound `K` would be the assertion that the least
certifying depth never exceeds the floor by more than `K` — a quantitative statement
about `∑ φ(n)/2ⁿ` strictly stronger than Erdős #249. -/
theorem no_small_absolute_run_bound :
    (2 * ((3 : ℤ) + 26 + 7 + 2) < 2 ^ 7 ∧ ConsecutiveFail 26 3 7 12) ∧
    (4 * ((4518 : ℤ) + 16 + 22 + 16 + 2) < 2 ^ 16 ∧ ConsecutiveFail 22 4518 16 16) ∧
    (2 * ((4518 : ℤ) + 22 + 14 + 2) < 2 ^ 14 ∧ ConsecutiveFail 22 4518 14 18) :=
  ⟨⟨depth_seven_nondegenerate, freeWalk_run_13⟩,
   ⟨freeWalk_run_17_threshold, freeWalk_run_17⟩,
   ⟨depth_fourteen_nondegenerate, freeWalk_run_19⟩⟩

end FreeWalk2
end Half
end ErdosProblems
