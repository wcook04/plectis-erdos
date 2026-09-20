import ErdosProblems.Erdos243.PaperCompleteR11.PresievedCRT
import ErdosProblems.Erdos243.PaperCompleteR11.CRTObstructionDensity
import ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Erdős 243: the largest gaps between integers avoiding given multiples

This file formalises `long243:res:gapconstant`
(`paper/reasoning-parts/erdos243/core.tex`, line 3588):

> Let `m 0 < m 1 < ⋯` be pairwise coprime integers at least `2` with
> `ℓ (m j) = j + O(1)`, where `ℓ x = log₂ log₂ max (4, x)`.  Let
> `σ = ∏ j, (1 - 1/m j) > 0` and enumerate the positive integers divisible by
> no `m j` in increasing order as `(u n)`.  Then
> `limsup (u (n+1) - u n) / ℓ (u n) = σ⁻¹`.

The normaliser `ℓ` is the tree's `recordLogLog`.  The enumeration is
`Nat.nth (Avoids m)`.

The development follows the written proof.

* `prefixCount_window`: one full period `M T = ∏_{j<T} m j` contains exactly
  `∏_{j<T} (m j - 1)` integers avoiding the first `T` moduli (Chinese remainder
  theorem, via `PaperCompleteR11.exists_crt_union_residues`).
* `prefixCount_ge_real` / `prefixCount_le_real`: the interval form, with the
  paper's `M T` error term.
* `card_tailBad_le`: the moduli of index in `[T, B)` cover at most
  `L θ T + B` integers of a window of length `L`.
* `exists_avoids_in_short_window`: the upper-bound sieve step.  If
  `c (σ_T - θ_T) > 1` then every sufficiently late window
  `[x, x + ⌈c ℓ x⌉)` contains an admissible integer.  The paper's
  `k (x+L) = ℓ x + O(1)` is `scale_index_le` together with
  `recordLogLog_le_sq`.
* `exists_covered_block`: the lower-bound construction.  Fresh moduli are
  assigned to the `K` admissible offsets below `L` and a simultaneous
  congruence is solved in `[Q, 2Q)` (via
  `PaperCompleteR11.exists_presieved_crt_phase`); the paper's
  `ℓ (2 Q_L) ≤ T + K_L + O(1)` is `prod_moduli_le` plus `prod_binaryTower_le`.
* `gap_le_eventually` and `exists_late_large_gap` turn these into the two
  halves of the limsup, and `maximal_gap_limsup_eq_inv_sigma` is the theorem.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open scoped BigOperators Topology
open ErdosProblems.Erdos243.PaperCompleteR11

/-! ## The paper's objects -/

/-- The positive integers divisible by none of the moduli: the set the paper
enumerates as `(u n)`. -/
def Avoids (m : ℕ → ℕ) (n : ℕ) : Prop := 0 < n ∧ ∀ j, ¬ (m j ∣ n)

/-- `M T = ∏_{j < T} m j`. -/
def prefixModulus (m : ℕ → ℕ) (T : ℕ) : ℕ := ∏ j ∈ Finset.range T, m j

/-- `∏_{j < T} (m j - 1)`, the exact number of admissible residues mod `M T`. -/
def prefixResidues (m : ℕ → ℕ) (T : ℕ) : ℕ := ∏ j ∈ Finset.range T, (m j - 1)

/-- `σ_T = ∏_{j < T} (1 - 1/m j)`. -/
noncomputable def prefixDensity (m : ℕ → ℕ) (T : ℕ) : ℝ :=
  ∏ j ∈ Finset.range T, (1 - 1 / (m j : ℝ))

/-- The number of integers of `[x, x+L)` divisible by none of `m 0, …, m (T-1)`. -/
def prefixCount (m : ℕ → ℕ) (T x L : ℕ) : ℕ :=
  ((Finset.Ico x (x + L)).filter (fun n => ∀ j < T, ¬ (m j ∣ n))).card

/-! ## The log-log normaliser -/

theorem recordLogLog_eq_logb (x : ℝ) :
    recordLogLog x = Real.logb 2 (Real.logb 2 (max 4 x)) := rfl

theorem logb_two_four : Real.logb 2 (4 : ℝ) = 2 := by
  have h : ((2 : ℝ)) ^ (2 : ℕ) = (4 : ℝ) := by norm_num
  rw [← h, Real.logb_pow]
  simp [Real.logb_self_eq_one]

/-- If `ℓ x ≤ n` then `x ≤ 2 ^ (2 ^ n)`. -/
theorem le_binaryTower_of_recordLogLog_le {x : ℝ} {n : ℕ}
    (h : recordLogLog x ≤ (n : ℝ)) : x ≤ (binaryTower n : ℝ) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hv : (2 : ℝ) ≤ Real.logb 2 (max 4 x) := inner_logLog_ge_two x
  have hvpos : (0 : ℝ) < Real.logb 2 (max 4 x) := by linarith
  have hxpos : (0 : ℝ) < max 4 x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  rw [recordLogLog_eq_logb, Real.logb_le_iff_le_rpow hb hvpos] at h
  rw [Real.logb_le_iff_le_rpow hb hxpos] at h
  have h1 : ((2 : ℝ)) ^ ((n : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  rw [h1] at h
  have h2 : ((2 : ℝ)) ^ (((2 ^ n : ℕ) : ℝ)) = ((2 ^ (2 ^ n) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  rw [h2] at h
  exact (le_max_right (4 : ℝ) x).trans h

/-- If `2 ≤ n` and `n ≤ ℓ x` then `2 ^ (2 ^ n) ≤ x`. -/
theorem binaryTower_le_of_le_recordLogLog {x : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (h : (n : ℝ) ≤ recordLogLog x) : (binaryTower n : ℝ) ≤ x := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hv : (2 : ℝ) ≤ Real.logb 2 (max 4 x) := inner_logLog_ge_two x
  have hvpos : (0 : ℝ) < Real.logb 2 (max 4 x) := by linarith
  have hxpos : (0 : ℝ) < max 4 x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  rw [recordLogLog_eq_logb, Real.le_logb_iff_rpow_le hb hvpos] at h
  rw [Real.le_logb_iff_rpow_le hb hxpos] at h
  have h1 : ((2 : ℝ)) ^ ((n : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  rw [h1] at h
  have h2 : ((2 : ℝ)) ^ (((2 ^ n : ℕ) : ℝ)) = ((2 ^ (2 ^ n) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  rw [h2] at h
  have hbig : (16 : ℝ) ≤ (binaryTower n : ℝ) := by
    have : binaryTower 2 ≤ binaryTower n := binaryTower_mono hn
    have h16 : binaryTower 2 = 16 := by norm_num [binaryTower]
    have := (Nat.cast_le (α := ℝ)).mpr this
    rw [h16] at this
    exact_mod_cast this
  have hmax : max 4 x = x := by
    rcases max_cases (4 : ℝ) x with ⟨he, _⟩ | ⟨he, _⟩
    · exfalso
      have : (binaryTower n : ℝ) ≤ 4 := by rw [← he]; exact h
      linarith
    · exact he
  rw [hmax] at h
  exact h

/-- `ℓ` is bounded below on the tower: `n ≤ ℓ x` once `2 ^ (2 ^ n) ≤ x`. -/
theorem le_recordLogLog_of_binaryTower_le {x : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h : (binaryTower n : ℝ) ≤ x) : (n : ℝ) ≤ recordLogLog x := by
  have := recordLogLog_mono h
  rwa [recordLogLog_binaryTower n hn] at this

/-- Doubling raises `ℓ` by at most one. -/
theorem recordLogLog_two_mul_le {x : ℝ} (hx : (4 : ℝ) ≤ x) :
    recordLogLog (2 * x) ≤ recordLogLog x + 1 := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hxpos : (0 : ℝ) < x := by linarith
  have hmx : max 4 x = x := max_eq_right hx
  have hm2x : max 4 (2 * x) = 2 * x := max_eq_right (by linarith)
  have hv : (2 : ℝ) ≤ Real.logb 2 x := by
    have := Real.logb_le_logb_of_le hb (by norm_num : (0:ℝ) < 4) hx
    rw [logb_two_four] at this
    exact this
  have hsplit : Real.logb 2 (2 * x) = 1 + Real.logb 2 x := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt hxpos), Real.logb_self_eq_one] <;> norm_num
  have hle : (1 : ℝ) + Real.logb 2 x ≤ 2 * Real.logb 2 x := by linarith
  have hstep : Real.logb 2 (1 + Real.logb 2 x) ≤ Real.logb 2 (2 * Real.logb 2 x) :=
    Real.logb_le_logb_of_le hb (by linarith) hle
  have hfin : Real.logb 2 (2 * Real.logb 2 x) = 1 + Real.logb 2 (Real.logb 2 x) := by
    rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one] <;> norm_num
  rw [recordLogLog_eq_logb, recordLogLog_eq_logb, hmx, hm2x, hsplit]
  linarith [hstep, hfin.le, hfin.ge]

/-- Adding at most `x` to `x` raises `ℓ` by at most one. -/
theorem recordLogLog_add_le {x y : ℝ} (hx : (4 : ℝ) ≤ x) (hyx : y ≤ x) :
    recordLogLog (x + y) ≤ recordLogLog x + 1 :=
  (recordLogLog_mono (by linarith : x + y ≤ 2 * x)).trans (recordLogLog_two_mul_le hx)

/-- Squaring raises `ℓ` by exactly one. -/
theorem recordLogLog_sq {x : ℝ} (hx : (4 : ℝ) ≤ x) :
    recordLogLog (x ^ 2) = recordLogLog x + 1 := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hxpos : (0 : ℝ) < x := by linarith
  have hmx : max 4 x = x := max_eq_right hx
  have hsq : (4 : ℝ) ≤ x ^ 2 := by nlinarith
  have hmx2 : max 4 (x ^ 2) = x ^ 2 := max_eq_right hsq
  have hv : (2 : ℝ) ≤ Real.logb 2 x := by
    have := Real.logb_le_logb_of_le hb (by norm_num : (0:ℝ) < 4) hx
    rw [logb_two_four] at this
    exact this
  have hpow : Real.logb 2 (x ^ 2) = 2 * Real.logb 2 x := by
    rw [Real.logb_pow]
    norm_num
  have hfin : Real.logb 2 (2 * Real.logb 2 x) = 1 + Real.logb 2 (Real.logb 2 x) := by
    rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one] <;> norm_num
  rw [recordLogLog_eq_logb, recordLogLog_eq_logb, hmx, hmx2, hpow, hfin]
  ring

theorem recordLogLog_le_sq {x y : ℝ} (hx : (4 : ℝ) ≤ x) (hy : y ≤ x ^ 2) :
    recordLogLog y ≤ recordLogLog x + 1 :=
  (recordLogLog_mono hy).trans (recordLogLog_sq hx).le

/-- `log₂ y ≤ y` for `y ≥ 1`. -/
theorem logb_two_le_self {y : ℝ} (hy : 1 ≤ y) : Real.logb 2 y ≤ y := by
  have hb : (1 : ℝ) < 2 := by norm_num
  rw [Real.logb_le_iff_le_rpow hb (by linarith)]
  have h1 : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le (by linarith)
  have h2 : y < (⌊y⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one y
  have h3 : ((2 : ℝ)) ^ (((⌊y⌋₊ : ℕ) : ℝ)) ≤ (2 : ℝ) ^ y :=
    (Real.rpow_le_rpow_left_iff hb).mpr h1
  have h4 : ((2 : ℝ)) ^ (((⌊y⌋₊ : ℕ) : ℝ)) = ((2 ^ (⌊y⌋₊ : ℕ) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  have h5 : (⌊y⌋₊ : ℕ) + 1 ≤ 2 ^ (⌊y⌋₊ : ℕ) := index_succ_le_two_pow _
  have h6 : (((⌊y⌋₊ : ℕ) : ℝ)) + 1 ≤ ((2 ^ (⌊y⌋₊ : ℕ) : ℕ) : ℝ) := by exact_mod_cast h5
  rw [h4] at h3
  linarith

theorem recordLogLog_le_self {x : ℝ} (hx : (4 : ℝ) ≤ x) : recordLogLog x ≤ x := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hmx : max 4 x = x := max_eq_right hx
  have hv : (2 : ℝ) ≤ Real.logb 2 (max 4 x) := inner_logLog_ge_two x
  have h1 : Real.logb 2 (Real.logb 2 (max 4 x)) ≤ Real.logb 2 (max 4 x) :=
    logb_two_le_self (by linarith)
  have h2 : Real.logb 2 (max 4 x) ≤ max 4 x := logb_two_le_self (by rw [hmx]; linarith)
  rw [hmx] at h1 h2
  rw [recordLogLog_eq_logb, hmx]
  linarith

/-- `ℓ` diverges along the naturals. -/
theorem eventually_le_recordLogLog (K : ℝ) :
    ∀ᶠ x : ℕ in atTop, K ≤ recordLogLog (x : ℝ) := by
  filter_upwards [eventually_ge_atTop (binaryTower (⌈K⌉₊ + 1))] with x hx
  have h1 : ((binaryTower (⌈K⌉₊ + 1) : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h2 := le_recordLogLog_of_binaryTower_le (n := ⌈K⌉₊ + 1) (by omega) h1
  have h3 : K ≤ ((⌈K⌉₊ : ℕ) : ℝ) := Nat.le_ceil K
  have h4 : ((⌈K⌉₊ : ℕ) : ℝ) ≤ ((⌈K⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
  linarith

/-! ## The prefix Chinese-remainder count -/

/-- A window of `M` consecutive integers meets each residue class mod `M` once. -/
theorem card_window_filter_mod (M x : ℕ) (hM : 0 < M) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r < M) :
    ((Finset.Ico x (x + M)).filter (fun n => n % M ∈ R)).card = R.card := by
  classical
  refine Finset.card_bij (fun n _ => n % M) ?_ ?_ ?_
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha hb
    rcases le_total a b with h | h
    · have hd : M ∣ b - a := (Nat.modEq_iff_dvd' h).mp hab
      have hlt : b - a < M := by omega
      have := Nat.eq_zero_of_dvd_of_lt hd
      omega
    · have hd : M ∣ a - b := (Nat.modEq_iff_dvd' h).mp hab.symm
      have hlt : a - b < M := by omega
      have := Nat.eq_zero_of_dvd_of_lt hd
      omega
  · intro r hr
    have hrM : r < M := hR r hr
    have hs : x % M < M := Nat.mod_lt _ hM
    set d : ℕ := (M + r - x % M) % M with hd
    have hdlt : d < M := Nat.mod_lt _ hM
    have hkey : (x + d) % M = r := by
      have e1 : x + d ≡ x % M + (M + r - x % M) [MOD M] :=
        Nat.ModEq.add (Nat.mod_modEq x M).symm (Nat.mod_modEq _ M)
      have e2 : x % M + (M + r - x % M) = M + r := by omega
      have : (x + d) % M = (M + r) % M := by
        simpa only [e2] using e1
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hrM]
    refine ⟨x + d, ?_, hkey⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Nat.le_add_right _ _, by omega⟩, by rw [hkey]; exact hr⟩

/-- Exact Chinese-remainder count over one full period. -/
theorem prefixCount_window (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) (T x : ℕ) :
    prefixCount m T x (prefixModulus m T) = prefixResidues m T := by
  classical
  have hM : 0 < prefixModulus m T :=
    Finset.prod_pos (fun j _ => hm j)
  obtain ⟨R, hR1, hR2, hR3⟩ :=
    exists_crt_union_residues (ι := Fin T) (fun i => m i.val) (fun i => hm i.val)
      (fun i j hij => hcop i.val j.val (fun h => hij (Fin.val_injective h)))
      (fun _ => 0)
  have hprodM : (∏ i : Fin T, m i.val) = prefixModulus m T :=
    Fin.prod_univ_eq_prod_range (fun k => m k) T
  have hprodP : (∏ i : Fin T, (m i.val - 1)) = prefixResidues m T :=
    Fin.prod_univ_eq_prod_range (fun k => m k - 1) T
  rw [hprodM] at hR1 hR2 hR3
  rw [hprodP] at hR2
  have hdict : ∀ n : ℕ, (n % prefixModulus m T ∈ R) ↔ ∃ j < T, m j ∣ n := by
    intro n
    rw [hR3 n]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.val, i.isLt, (ZMod.natCast_eq_zero_iff n (m i.val)).mp hi⟩
    · rintro ⟨j, hjT, hj⟩
      exact ⟨⟨j, hjT⟩, (ZMod.natCast_eq_zero_iff n (m j)).mpr hj⟩
  have hbad : ((Finset.Ico x (x + prefixModulus m T)).filter
      (fun n => n % prefixModulus m T ∈ R)).card = R.card :=
    card_window_filter_mod _ _ hM R hR1
  have hgoodeq : ((Finset.Ico x (x + prefixModulus m T)).filter
      (fun n => ¬ (n % prefixModulus m T ∈ R))) =
      ((Finset.Ico x (x + prefixModulus m T)).filter (fun n => ∀ j < T, ¬ (m j ∣ n))) := by
    ext n
    constructor
    · intro hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, fun j hj hdvd => hn.2 ((hdict n).mpr ⟨j, hj, hdvd⟩)⟩
    · intro hn
      rw [Finset.mem_filter] at hn ⊢
      refine ⟨hn.1, fun hmem => ?_⟩
      obtain ⟨j, hj, hdvd⟩ := (hdict n).mp hmem
      exact hn.2 j hj hdvd
  have hsum := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.Ico x (x + prefixModulus m T))
    (p := fun n => n % prefixModulus m T ∈ R)
  rw [hbad, hgoodeq, Nat.card_Ico] at hsum
  have hIco : x + prefixModulus m T - x = prefixModulus m T := by omega
  rw [hIco] at hsum
  unfold prefixCount
  omega

/-- Counts over adjacent intervals add. -/
theorem prefixCount_add (m : ℕ → ℕ) (T x a b : ℕ) :
    prefixCount m T x (a + b) = prefixCount m T x a + prefixCount m T (x + a) b := by
  classical
  have hsplit : Finset.Ico x (x + (a + b)) =
      Finset.Ico x (x + a) ∪ Finset.Ico (x + a) (x + a + b) := by
    have hre : x + (a + b) = x + a + b := by omega
    rw [hre, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  have hdisj : Disjoint (Finset.Ico x (x + a)) (Finset.Ico (x + a) (x + a + b)) :=
    Finset.Ico_disjoint_Ico_consecutive _ _ _
  unfold prefixCount
  rw [hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]

/-- `q` full periods contain exactly `q ∏ (m j - 1)` prefix-avoiding integers. -/
theorem prefixCount_blocks (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) (T q : ℕ) :
    ∀ x : ℕ, prefixCount m T x (q * prefixModulus m T) = q * prefixResidues m T := by
  induction q with
  | zero => intro x; simp [prefixCount]
  | succ q ih =>
      intro x
      have hre : (q + 1) * prefixModulus m T =
          prefixModulus m T + q * prefixModulus m T := by ring
      rw [hre, prefixCount_add, prefixCount_window m hm hcop T x, ih]
      ring

theorem prefixCount_le_length (m : ℕ → ℕ) (T x L : ℕ) : prefixCount m T x L ≤ L := by
  unfold prefixCount
  calc ((Finset.Ico x (x + L)).filter (fun n => ∀ j < T, ¬ (m j ∣ n))).card
      ≤ (Finset.Ico x (x + L)).card := Finset.card_filter_le _ _
    _ = L := by rw [Nat.card_Ico]; omega

/-- Two-sided natural bound for an arbitrary interval. -/
theorem prefixCount_interval_bounds (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) (T x L : ℕ) :
    (L / prefixModulus m T) * prefixResidues m T ≤ prefixCount m T x L ∧
      prefixCount m T x L ≤
        (L / prefixModulus m T) * prefixResidues m T + L % prefixModulus m T := by
  have hM : 0 < prefixModulus m T := Finset.prod_pos (fun j _ => hm j)
  set q := L / prefixModulus m T with hq
  set r := L % prefixModulus m T with hr
  have hL : q * prefixModulus m T + r = L := by
    rw [hq, hr]; exact Nat.div_add_mod' L (prefixModulus m T)
  have hsplit : prefixCount m T x L =
      prefixCount m T x (q * prefixModulus m T) +
        prefixCount m T (x + q * prefixModulus m T) r := by
    rw [← prefixCount_add, hL]
  rw [hsplit, prefixCount_blocks m hm hcop T q x]
  have := prefixCount_le_length m T (x + q * prefixModulus m T) r
  omega

/-! ## Real form of the prefix count -/

theorem prefixDensity_nonneg (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (T : ℕ) :
    0 ≤ prefixDensity m T := by
  refine Finset.prod_nonneg (fun j _ => ?_)
  have h1 : (1 : ℝ) ≤ (m j : ℝ) := by exact_mod_cast hm j
  have h2 : 1 / (m j : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  linarith

theorem prefixDensity_le_one (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (T : ℕ) :
    prefixDensity m T ≤ 1 := by
  refine Finset.prod_le_one (fun j _ => ?_) (fun j _ => ?_)
  · have h1 : (1 : ℝ) ≤ (m j : ℝ) := by exact_mod_cast hm j
    have h2 : 1 / (m j : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  · have h1 : (0 : ℝ) < (m j : ℝ) := by exact_mod_cast hm j
    have : 0 ≤ 1 / (m j : ℝ) := by positivity
    linarith

theorem prefixDensity_mul_modulus (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (T : ℕ) :
    prefixDensity m T * (prefixModulus m T : ℝ) = (prefixResidues m T : ℝ) := by
  unfold prefixDensity prefixModulus prefixResidues
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have h1 : (0 : ℝ) < (m j : ℝ) := by exact_mod_cast hm j
  have hcast : ((m j - 1 : ℕ) : ℝ) = (m j : ℝ) - 1 := by
    have := hm j
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast]
  field_simp

theorem prefixDensity_pos (m : ℕ → ℕ) (hm : ∀ j, 2 ≤ m j) (T : ℕ) :
    0 < prefixDensity m T := by
  refine Finset.prod_pos (fun j _ => ?_)
  have h1 : (2 : ℝ) ≤ (m j : ℝ) := by exact_mod_cast hm j
  have h2 : 1 / (m j : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  linarith

theorem prefixCount_ge_real (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) (T x L : ℕ) :
    prefixDensity m T * (L : ℝ) - (prefixModulus m T : ℝ) ≤ (prefixCount m T x L : ℝ) := by
  obtain ⟨hlow, -⟩ := prefixCount_interval_bounds m hm hcop T x L
  have hM : 0 < prefixModulus m T := Finset.prod_pos (fun j _ => hm j)
  have hLsplit : (L / prefixModulus m T) * prefixModulus m T + L % prefixModulus m T = L :=
    Nat.div_add_mod' L (prefixModulus m T)
  have hr : L % prefixModulus m T < prefixModulus m T := Nat.mod_lt _ hM
  have hσ0 := prefixDensity_nonneg m hm T
  have hσ1 := prefixDensity_le_one m hm T
  have hkey : prefixDensity m T * (L : ℝ) =
      ((L / prefixModulus m T : ℕ) : ℝ) * (prefixResidues m T : ℝ) +
        prefixDensity m T * ((L % prefixModulus m T : ℕ) : ℝ) := by
    have : (L : ℝ) = ((L / prefixModulus m T : ℕ) : ℝ) * (prefixModulus m T : ℝ) +
        ((L % prefixModulus m T : ℕ) : ℝ) := by exact_mod_cast hLsplit.symm
    rw [this, mul_add, ← prefixDensity_mul_modulus m hm T]
    ring
  have hcast : (((L / prefixModulus m T) * prefixResidues m T : ℕ) : ℝ) ≤
      (prefixCount m T x L : ℝ) := by exact_mod_cast hlow
  push_cast at hcast
  have hrr : prefixDensity m T * ((L % prefixModulus m T : ℕ) : ℝ) ≤
      (prefixModulus m T : ℝ) := by
    have h1 : ((L % prefixModulus m T : ℕ) : ℝ) ≤ (prefixModulus m T : ℝ) := by
      exact_mod_cast hr.le
    have h2 : (0 : ℝ) ≤ ((L % prefixModulus m T : ℕ) : ℝ) := by positivity
    nlinarith
  linarith [hkey.ge, hkey.le]

theorem prefixCount_le_real (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) (T x L : ℕ) :
    (prefixCount m T x L : ℝ) ≤ prefixDensity m T * (L : ℝ) + (prefixModulus m T : ℝ) := by
  obtain ⟨-, hhigh⟩ := prefixCount_interval_bounds m hm hcop T x L
  have hM : 0 < prefixModulus m T := Finset.prod_pos (fun j _ => hm j)
  have hLsplit : (L / prefixModulus m T) * prefixModulus m T + L % prefixModulus m T = L :=
    Nat.div_add_mod' L (prefixModulus m T)
  have hr : L % prefixModulus m T < prefixModulus m T := Nat.mod_lt _ hM
  have hσ0 := prefixDensity_nonneg m hm T
  have hkey : prefixDensity m T * (L : ℝ) =
      ((L / prefixModulus m T : ℕ) : ℝ) * (prefixResidues m T : ℝ) +
        prefixDensity m T * ((L % prefixModulus m T : ℕ) : ℝ) := by
    have : (L : ℝ) = ((L / prefixModulus m T : ℕ) : ℝ) * (prefixModulus m T : ℝ) +
        ((L % prefixModulus m T : ℕ) : ℝ) := by exact_mod_cast hLsplit.symm
    rw [this, mul_add, ← prefixDensity_mul_modulus m hm T]
    ring
  have hcast : (prefixCount m T x L : ℝ) ≤
      (((L / prefixModulus m T) * prefixResidues m T + L % prefixModulus m T : ℕ) : ℝ) := by
    exact_mod_cast hhigh
  push_cast at hcast
  have hrr : (0 : ℝ) ≤ prefixDensity m T * ((L % prefixModulus m T : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((L % prefixModulus m T : ℕ) : ℝ) := by positivity
    nlinarith
  have h1 : ((L % prefixModulus m T : ℕ) : ℝ) ≤ (prefixModulus m T : ℝ) := by
    exact_mod_cast hr.le
  linarith [hkey.ge, hkey.le]

/-! ## The tail moduli cover few integers -/

/-- The multiples of `d` in an interval of length `L`. -/
theorem card_multiples_le (d x L : ℕ) (hd : 0 < d) :
    ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)).card ≤ L / d + 1 := by
  classical
  have key : ∀ u v : ℕ, x ≤ u → d ∣ u → d ∣ v → u ≤ v →
      (u - x) / d = (v - x) / d → u = v := by
    rintro u v hux ⟨p, rfl⟩ ⟨q, rfl⟩ huv heq
    have hpq : p ≤ q := Nat.le_of_mul_le_mul_left huv hd
    obtain ⟨t, rfl⟩ : ∃ t, q = p + t := ⟨q - p, by omega⟩
    have hvu : d * (p + t) = d * p + d * t := by ring
    rw [hvu] at heq
    have hsub : d * p + d * t - x = (d * p - x) + d * t := by omega
    rw [hsub, Nat.add_mul_div_left _ _ hd] at heq
    have ht : t = 0 := by omega
    simp [ht]
  have hcard := Finset.card_le_card_of_injOn (f := fun n => (n - x) / d)
    (s := (Finset.Ico x (x + L)).filter (fun n => d ∣ n))
    (t := Finset.range (L / d + 1)) ?_ ?_
  · rwa [Finset.card_range] at hcard
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hn
    simp only [Finset.mem_coe, Finset.mem_range]
    have h1 : n - x ≤ L := by omega
    have h2 := Nat.div_le_div_right (c := d) h1
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha hb
    rcases le_total a b with h | h
    · exact key a b ha.1.1 ha.2 hb.2 h hab
    · exact (key b a hb.1.1 hb.2 ha.2 h hab.symm).symm

/-- The integers of `[x, x+L)` divisible by one of `m T, …, m (B-1)`. -/
theorem card_tailBad_le (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (T B x L : ℕ) :
    ((((Finset.Ico T B).biUnion
        (fun j => (Finset.Ico x (x + L)).filter (fun n => m j ∣ n))).card : ℝ))
      ≤ (L : ℝ) * (∑ j ∈ Finset.Ico T B, 1 / (m j : ℝ)) + (B : ℝ) := by
  classical
  have h1 := Finset.card_biUnion_le (s := Finset.Ico T B)
    (t := fun j => (Finset.Ico x (x + L)).filter (fun n => m j ∣ n))
  have h2 : ∑ j ∈ Finset.Ico T B,
      ((Finset.Ico x (x + L)).filter (fun n => m j ∣ n)).card ≤
      ∑ j ∈ Finset.Ico T B, (L / m j + 1) :=
    Finset.sum_le_sum (fun j _ => card_multiples_le (m j) x L (hm j))
  have h3 : (((Finset.Ico T B).biUnion
      (fun j => (Finset.Ico x (x + L)).filter (fun n => m j ∣ n))).card : ℝ) ≤
      ((∑ j ∈ Finset.Ico T B, (L / m j + 1) : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  refine h3.trans ?_
  push_cast
  rw [Finset.sum_add_distrib]
  have h4 : ∑ j ∈ Finset.Ico T B, ((L / m j : ℕ) : ℝ) ≤
      (L : ℝ) * ∑ j ∈ Finset.Ico T B, 1 / (m j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := Nat.cast_div_le (α := ℝ) (m := L) (n := m j)
    calc ((L / m j : ℕ) : ℝ) ≤ (L : ℝ) / (m j : ℝ) := this
      _ = (L : ℝ) * (1 / (m j : ℝ)) := by ring
  have h5 : ∑ _j ∈ Finset.Ico T B, (1 : ℝ) ≤ (B : ℝ) := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    have : (B - T : ℕ) ≤ B := Nat.sub_le _ _
    exact_mod_cast this
  linarith

/-- If the prefix-avoiding integers of a window outnumber the integers covered by
the moduli `m T, …, m (B-1)`, and every later modulus already exceeds the window,
then the window contains an admissible integer. -/
theorem exists_avoids_in_window (m : ℕ → ℕ) (T B x L : ℕ) (hx : 0 < x)
    (hB : ∀ j, B ≤ j → x + L ≤ m j)
    (hcard : ((Finset.Ico T B).biUnion
        (fun j => (Finset.Ico x (x + L)).filter (fun n => m j ∣ n))).card <
      prefixCount m T x L) :
    ∃ n, x ≤ n ∧ n < x + L ∧ Avoids m n := by
  classical
  set S := (Finset.Ico x (x + L)).filter (fun n => ∀ j < T, ¬ (m j ∣ n)) with hS
  set Bad := (Finset.Ico T B).biUnion
      (fun j => (Finset.Ico x (x + L)).filter (fun n => m j ∣ n)) with hBad
  have hsub : S ⊆ (S \ Bad) ∪ Bad := by
    intro a ha
    by_cases h : a ∈ Bad
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, h⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (S \ Bad) Bad
  have hpos : 0 < (S \ Bad).card := by
    have : prefixCount m T x L = S.card := rfl
    omega
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_sdiff] at hn
  obtain ⟨hnS, hnB⟩ := hn
  rw [hS, Finset.mem_filter, Finset.mem_Ico] at hnS
  obtain ⟨⟨hxn, hnL⟩, hpref⟩ := hnS
  refine ⟨n, hxn, hnL, ⟨by omega, fun j hdvd => ?_⟩⟩
  rcases lt_or_ge j T with hjT | hjT
  · exact hpref j hjT hdvd
  rcases lt_or_ge j B with hjB | hjB
  · refine hnB ?_
    rw [hBad]
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Ico.mpr ⟨hjT, hjB⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hxn, hnL⟩, hdvd⟩⟩
  · have := hB j hjB
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-! ## Consequences of the scale hypothesis `ℓ (m j) = j + O(1)` -/

theorem scale_upper (m : ℕ → ℕ) (Cs : ℝ)
    (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (C : ℕ) (hC : Cs ≤ (C : ℝ)) (j : ℕ) : m j ≤ binaryTower (j + C) := by
  have h := abs_le.mp (hscale j)
  have h1 : recordLogLog (m j : ℝ) ≤ (((j + C : ℕ)) : ℝ) := by push_cast; linarith [h.2]
  have h2 := le_binaryTower_of_recordLogLog_le h1
  exact_mod_cast h2

theorem scale_lower (m : ℕ → ℕ) (Cs : ℝ)
    (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (C : ℕ) (hC : Cs ≤ (C : ℝ)) (j : ℕ) (hj : C + 2 ≤ j) :
    binaryTower (j - C) ≤ m j := by
  have h := abs_le.mp (hscale j)
  have hCj : C ≤ j := by omega
  have hcast : (((j - C : ℕ)) : ℝ) = (j : ℝ) - (C : ℝ) := by
    rw [Nat.cast_sub hCj]
  have h1 : (((j - C : ℕ)) : ℝ) ≤ recordLogLog (m j : ℝ) := by rw [hcast]; linarith [h.1]
  have h2 : 2 ≤ j - C := by omega
  have := binaryTower_le_of_le_recordLogLog h2 h1
  exact_mod_cast this

theorem scale_index_le (m : ℕ → ℕ) (Cs : ℝ)
    (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    {z : ℝ} {j : ℕ} (hz : (m j : ℝ) ≤ z) : (j : ℝ) ≤ recordLogLog z + Cs := by
  have h := abs_le.mp (hscale j)
  have := recordLogLog_mono hz
  linarith [h.1]

theorem two_pow_le_modulus (m : ℕ → ℕ) (Cs : ℝ)
    (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (C : ℕ) (hC : Cs ≤ (C : ℝ)) (j : ℕ) (hj : 2 * C + 2 ≤ j) : 2 ^ j ≤ m j := by
  have hb := scale_lower m Cs hscale C hC j (by omega)
  obtain ⟨s, hs⟩ : ∃ s, j - C = C + s := ⟨j - C - C, by omega⟩
  have hs2 : 2 ≤ s := by omega
  have hpow : C + s + C ≤ 2 ^ (C + s) := by
    have h1 : C + 1 ≤ 2 ^ C := index_succ_le_two_pow C
    have h2 : s + 1 ≤ 2 ^ s := index_succ_le_two_pow s
    have h3 : (2 : ℕ) ^ (C + s) = 2 ^ C * 2 ^ s := pow_add 2 C s
    nlinarith [h1, h2, h3]
  have hjle : j ≤ 2 ^ (j - C) := by rw [hs]; omega
  calc 2 ^ j ≤ 2 ^ (2 ^ (j - C)) := Nat.pow_le_pow_right (by norm_num) hjle
    _ = binaryTower (j - C) := rfl
    _ ≤ m j := hb

theorem summable_inv_modulus (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j) (Cs : ℝ)
    (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (C : ℕ) (hC : Cs ≤ (C : ℝ)) : Summable (fun j => 1 / (m j : ℝ)) := by
  rw [← summable_nat_add_iff (2 * C + 2)]
  refine Summable.of_nonneg_of_le (g := fun j => 1 / (m (j + (2 * C + 2)) : ℝ))
    (f := fun j => (1 / 2 : ℝ) ^ j) (fun j => ?_) (fun j => ?_) summable_geometric_two
  · have : (0 : ℝ) < (m (j + (2 * C + 2)) : ℝ) := by
      have := hm2 (j + (2 * C + 2)); positivity
    positivity
  · have hpow : 2 ^ (j + (2 * C + 2)) ≤ m (j + (2 * C + 2)) :=
      two_pow_le_modulus m Cs hscale C hC _ (by omega)
    have hcast : ((2 : ℝ)) ^ (j + (2 * C + 2)) ≤ (m (j + (2 * C + 2)) : ℝ) := by
      exact_mod_cast hpow
    have hbase : (0 : ℝ) < (2 : ℝ) ^ (j + (2 * C + 2)) := by positivity
    have hstep : (1 : ℝ) / (m (j + (2 * C + 2)) : ℝ) ≤ 1 / (2 : ℝ) ^ (j + (2 * C + 2)) :=
      one_div_le_one_div_of_le hbase hcast
    refine hstep.trans ?_
    have hmono : ((2 : ℝ)) ^ j ≤ (2 : ℝ) ^ (j + (2 * C + 2)) := by
      apply pow_le_pow_right₀ (by norm_num) (by omega)
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have : (1 : ℝ) / (2 : ℝ) ^ (j + (2 * C + 2)) ≤ 1 / (2 : ℝ) ^ j :=
      one_div_le_one_div_of_le h2j hmono
    refine this.trans ?_
    simp [div_pow]

/-- `θ T = ∑_{j ≥ T} 1 / m j`. -/
noncomputable def tailSum (m : ℕ → ℕ) (T : ℕ) : ℝ := ∑' k : ℕ, 1 / (m (k + T) : ℝ)

theorem tailSum_nonneg (m : ℕ → ℕ) (T : ℕ) : 0 ≤ tailSum m T :=
  tsum_nonneg (fun _ => by positivity)

theorem tailSum_tendsto_zero (m : ℕ → ℕ) :
    Tendsto (fun T => tailSum m T) atTop (nhds 0) :=
  tendsto_sum_nat_add (fun j => 1 / (m j : ℝ))

theorem sum_Ico_le_tailSum (m : ℕ → ℕ)
    (hsum : Summable (fun j => 1 / (m j : ℝ))) (T B : ℕ) :
    ∑ j ∈ Finset.Ico T B, 1 / (m j : ℝ) ≤ tailSum m T := by
  have hshift : Summable (fun k : ℕ => 1 / (m (k + T) : ℝ)) :=
    (summable_nat_add_iff T).mpr hsum
  have hre : ∑ j ∈ Finset.Ico T B, 1 / (m j : ℝ)
      = ∑ k ∈ Finset.range (B - T), 1 / (m (k + T) : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm])
  rw [hre]
  exact hshift.sum_le_tsum _ (fun k _ => by positivity)

/-! ## Upper bound: every sufficiently late short window meets the set -/

/-- The sieve step of the written proof.  If `c (σ_T - θ_T) > 1` then every
sufficiently late window `[x, x + ⌈c ℓ x⌉)` contains an admissible integer. -/
theorem exists_avoids_in_short_window (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (Cs : ℝ) (hCs : 0 ≤ Cs)
    (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (hsum : Summable (fun j => 1 / (m j : ℝ)))
    (T : ℕ) (c : ℝ) (hc0 : 0 < c)
    (hgap : 1 < c * (prefixDensity m T - tailSum m T)) :
    ∀ᶠ x : ℕ in atTop, ∃ n, x ≤ n ∧ n < x + ⌈c * recordLogLog (x : ℝ)⌉₊ ∧ Avoids m n := by
  classical
  have hm : ∀ j, 0 < m j := fun j => lt_of_lt_of_le (by norm_num) (hm2 j)
  set σT := prefixDensity m T with hσT
  set θT := tailSum m T with hθT
  set MT := prefixModulus m T with hMT
  set ε := c * (σT - θT) - 1 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hδpos : 0 < σT - θT := by nlinarith
  set K : ℝ := ((MT : ℝ) + Cs + 3) / ε with hK
  have hcastR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcastR.eventually_ge_atTop (4 : ℝ),
    hcastR.eventually_ge_atTop (c + 2), eventually_le_recordLogLog K] with x hx4 hxc hxK
  have hxpos : 0 < x := by
    by_contra h
    have : x = 0 := by omega
    rw [this] at hx4; norm_num at hx4
  set L : ℕ := ⌈c * recordLogLog (x : ℝ)⌉₊ with hLdef
  have hell1 : (1 : ℝ) ≤ recordLogLog (x : ℝ) := one_le_recordLogLog _
  have hellx : recordLogLog (x : ℝ) ≤ (x : ℝ) := recordLogLog_le_self hx4
  have hcell : 0 ≤ c * recordLogLog (x : ℝ) := by positivity
  have hL1 : c * recordLogLog (x : ℝ) ≤ (L : ℝ) := Nat.le_ceil _
  have hL2 : (L : ℝ) ≤ c * recordLogLog (x : ℝ) + 1 := (Nat.ceil_lt_add_one hcell).le
  have hLx : (L : ℝ) ≤ c * (x : ℝ) + 1 := by nlinarith
  have hsq : ((x : ℝ) + (L : ℝ)) ≤ (x : ℝ) ^ 2 := by nlinarith
  -- the index cut-off `B`
  set B : ℕ := ⌊recordLogLog ((x : ℝ) + (L : ℝ)) + Cs⌋₊ + 1 with hBdef
  have hellxL : recordLogLog ((x : ℝ) + (L : ℝ)) ≤ recordLogLog (x : ℝ) + 1 :=
    recordLogLog_le_sq hx4 hsq
  have hellxL0 : (0 : ℝ) ≤ recordLogLog ((x : ℝ) + (L : ℝ)) + Cs := by
    have := one_le_recordLogLog ((x : ℝ) + (L : ℝ)); linarith
  have hBbound : (B : ℝ) ≤ recordLogLog (x : ℝ) + Cs + 2 := by
    have h1 : ((⌊recordLogLog ((x : ℝ) + (L : ℝ)) + Cs⌋₊ : ℕ) : ℝ) ≤
        recordLogLog ((x : ℝ) + (L : ℝ)) + Cs := Nat.floor_le hellxL0
    rw [hBdef]
    push_cast
    linarith
  have hBtail : ∀ j, B ≤ j → x + L ≤ m j := by
    intro j hj
    by_contra hcon
    have hmj : (m j : ℝ) ≤ (x : ℝ) + (L : ℝ) := by
      have : m j ≤ x + L := by omega
      have := (Nat.cast_le (α := ℝ)).mpr this
      push_cast at this
      linarith
    have hjle := scale_index_le m Cs hscale hmj
    have : j ≤ ⌊recordLogLog ((x : ℝ) + (L : ℝ)) + Cs⌋₊ := Nat.le_floor hjle
    omega
  -- counting
  have hlow := prefixCount_ge_real m hm hcop T x L
  have hbad := card_tailBad_le m hm T B x L
  have hsumle := sum_Ico_le_tailSum m hsum T B
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hbad2 : ((((Finset.Ico T B).biUnion
      (fun j => (Finset.Ico x (x + L)).filter (fun n => m j ∣ n))).card : ℝ))
      ≤ (L : ℝ) * θT + (recordLogLog (x : ℝ) + Cs + 2) := by
    refine hbad.trans ?_
    have : (L : ℝ) * (∑ j ∈ Finset.Ico T B, 1 / (m j : ℝ)) ≤ (L : ℝ) * θT := by
      exact mul_le_mul_of_nonneg_left hsumle hL0
    linarith
  have hkey : (L : ℝ) * θT + (recordLogLog (x : ℝ) + Cs + 2) < σT * (L : ℝ) - (MT : ℝ) := by
    have hεell : (MT : ℝ) + Cs + 3 ≤ ε * recordLogLog (x : ℝ) := by
      have : K * ε ≤ recordLogLog (x : ℝ) * ε := by nlinarith
      rw [hK] at this
      field_simp at this
      nlinarith
    have hLlow : c * recordLogLog (x : ℝ) * (σT - θT) ≤ (L : ℝ) * (σT - θT) := by
      exact mul_le_mul_of_nonneg_right hL1 hδpos.le
    have hexp : c * recordLogLog (x : ℝ) * (σT - θT) = (1 + ε) * recordLogLog (x : ℝ) := by
      rw [hε]; ring
    nlinarith
  have hstrict : ((Finset.Ico T B).biUnion
      (fun j => (Finset.Ico x (x + L)).filter (fun n => m j ∣ n))).card <
      prefixCount m T x L := by
    have : ((((Finset.Ico T B).biUnion
        (fun j => (Finset.Ico x (x + L)).filter (fun n => m j ∣ n))).card : ℝ))
        < (prefixCount m T x L : ℝ) := by linarith
    exact_mod_cast this
  exact exists_avoids_in_window m T B x L hxpos hBtail hstrict

/-! ## Lower bound: covered blocks of arbitrary length -/

theorem two_le_binaryTower (n : ℕ) : 2 ≤ binaryTower n := by
  have h : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) h
    _ = binaryTower n := rfl

theorem prod_binaryTower_le (C : ℕ) :
    ∀ N : ℕ, ∏ k ∈ Finset.range N, binaryTower (k + C) ≤ binaryTower (N + C) := by
  intro N
  induction N with
  | zero => simpa using binaryTower_pos C
  | succ N ih =>
      rw [Finset.prod_range_succ]
      have h3 : binaryTower (N + C) * binaryTower (N + C) = binaryTower (N + C + 1) := by
        rw [binaryTower_succ]; ring
      have h4 : binaryTower (N + C + 1) = binaryTower (N + 1 + C) := by
        congr 1; omega
      calc (∏ k ∈ Finset.range N, binaryTower (k + C)) * binaryTower (N + C)
          ≤ binaryTower (N + C) * binaryTower (N + C) := Nat.mul_le_mul_right _ ih
        _ = binaryTower (N + C + 1) := h3
        _ = binaryTower (N + 1 + C) := h4

theorem prod_moduli_le (m : ℕ → ℕ) (Cs : ℝ)
    (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (C : ℕ) (hC : Cs ≤ (C : ℝ)) (N : ℕ) :
    ∏ k ∈ Finset.range N, m k ≤ binaryTower (N + C) :=
  le_trans (Finset.prod_le_prod' (fun k _ => scale_upper m Cs hscale C hC k))
    (prod_binaryTower_le C N)

theorem two_pow_le_prod (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j) (N : ℕ) :
    2 ^ N ≤ ∏ k ∈ Finset.range N, m k := by
  have h := Finset.prod_le_prod' (f := fun _ : ℕ => (2 : ℕ)) (g := m)
    (s := Finset.range N) (fun k _ => hm2 k)
  simpa [Finset.prod_const] using h

/-- The Chinese-remainder construction of the written proof: a block of length
`L` all of whose members are divisible by some modulus, with an explicit height
bound `2 ^ (T + K) ≤ x ≤ 2 ^ (2 ^ (T + K + C + 1))`, where `K` is the number of
offsets below `L` that avoid the first `T` moduli. -/
theorem exists_covered_block (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (Cs : ℝ) (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (C : ℕ) (hC : Cs ≤ (C : ℝ)) (T L : ℕ) :
    ∃ x : ℕ, 2 ^ (T + prefixCount m T 0 L) ≤ x ∧
      x ≤ binaryTower (T + prefixCount m T 0 L + C + 1) ∧
      ∀ i, i < L → ¬ Avoids m (x + i) := by
  classical
  have hm : ∀ j, 0 < m j := fun j => lt_of_lt_of_le (by norm_num) (hm2 j)
  set S : Finset ℕ := (Finset.range L).filter (fun r => ∀ j < T, ¬ (m j ∣ r)) with hS
  have hIco : Finset.Ico 0 (0 + L) = Finset.range L := by
    rw [Nat.zero_add, Finset.range_eq_Ico]
  have hSK : prefixCount m T 0 L = S.card := by
    rw [hS]; unfold prefixCount; rw [hIco]
  rw [hSK]
  set K := S.card with hK
  set W := prefixModulus m T with hW
  have hWpos : 0 < W := Finset.prod_pos (fun j _ => hm j)
  let e : {r // r ∈ S} ≃ Fin K := S.equivFin
  set idx : {r // r ∈ S} → ℕ := fun i => T + ((e i : Fin K) : ℕ) with hidx
  have hidxT : ∀ i, T ≤ idx i := fun i => Nat.le_add_right _ _
  have hidxinj : Function.Injective idx := by
    intro i j hij
    have hval : ((e i : Fin K) : ℕ) = ((e j : Fin K) : ℕ) := by
      simp only [hidx] at hij; omega
    exact e.injective (Fin.ext hval)
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ := exists_presieved_crt_phase (ι := {r // r ∈ S})
      W hWpos (fun i => m (idx i)) (fun i => (i : ℕ)) (fun i => hm (idx i))
      (fun i j hij => hcop (idx i) (idx j) (fun h => hij (hidxinj h)))
      (fun i => Nat.Coprime.prod_left (fun j hj => hcop j (idx i)
        (by have := Finset.mem_range.mp hj; have := hidxT i; omega)))
  have hprodι : (∏ i : {r // r ∈ S}, m (idx i)) = ∏ k ∈ Finset.range K, m (T + k) := by
    have h1 : (∏ i : {r // r ∈ S}, m (idx i)) = ∏ f : Fin K, m (T + (f : ℕ)) :=
      Equiv.prod_comp e (fun f : Fin K => m (T + (f : ℕ)))
    rw [h1]
    exact Fin.prod_univ_eq_prod_range (fun k => m (T + k)) K
  have hQ : W * (∏ i : {r // r ∈ S}, m (idx i)) = ∏ k ∈ Finset.range (T + K), m k := by
    rw [hprodι, hW, prefixModulus, Finset.prod_range_add]
  refine ⟨x, ?_, ?_, ?_⟩
  · calc 2 ^ (T + K) ≤ ∏ k ∈ Finset.range (T + K), m k := two_pow_le_prod m hm2 _
      _ = W * (∏ i : {r // r ∈ S}, m (idx i)) := hQ.symm
      _ ≤ x := hx1
  · have hle : ∏ k ∈ Finset.range (T + K), m k ≤ binaryTower (T + K + C) :=
      prod_moduli_le m Cs hscale C hC (T + K)
    have hbt := two_le_binaryTower (T + K + C)
    have h2 : 2 * binaryTower (T + K + C) ≤ binaryTower (T + K + C + 1) := by
      rw [binaryTower_succ]
      nlinarith [hbt]
    have hlt : x < 2 * (W * (∏ i : {r // r ∈ S}, m (idx i))) := hx2
    rw [hQ] at hlt
    have h3 : 2 * (∏ k ∈ Finset.range (T + K), m k) ≤ 2 * binaryTower (T + K + C) :=
      Nat.mul_le_mul_left 2 hle
    omega
  · intro i hiL hAv
    by_cases hmem : i ∈ S
    · exact hAv.2 (idx ⟨i, hmem⟩) (hx4 ⟨i, hmem⟩)
    · have hnot : ¬ (∀ j < T, ¬ (m j ∣ i)) := by
        intro hcon
        exact hmem (by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiL, hcon⟩)
      push_neg at hnot
      obtain ⟨j, hjT, hdvd⟩ := hnot
      have hjW : m j ∣ W := by
        rw [hW, prefixModulus]
        exact Finset.dvd_prod_of_mem m (Finset.mem_range.mpr hjT)
      exact hAv.2 j (dvd_add (hjW.trans hx3) hdvd)

/-! ## The enumeration -/

theorem avoids_one (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j) : Avoids m 1 := by
  refine ⟨one_pos, fun j hdvd => ?_⟩
  have h1 := Nat.le_of_dvd one_pos hdvd
  have h2 := hm2 j
  omega

theorem infinite_avoids (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (Cs : ℝ) (hCs : 0 ≤ Cs)
    (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (hsum : Summable (fun j => 1 / (m j : ℝ)))
    (T : ℕ) (hT : 0 < prefixDensity m T - tailSum m T) :
    {n | Avoids m n}.Infinite := by
  set c := 2 / (prefixDensity m T - tailSum m T) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hgap : 1 < c * (prefixDensity m T - tailSum m T) := by
    have hval : c * (prefixDensity m T - tailSum m T) = 2 := by
      rw [hc]; field_simp
    rw [hval]; norm_num
  have hw := exists_avoids_in_short_window m hm2 hcop Cs hCs hscale hsum T c hc0 hgap
  rw [Filter.eventually_atTop] at hw
  obtain ⟨N, hN⟩ := hw
  intro hfin
  obtain ⟨b, hb⟩ := hfin.bddAbove
  obtain ⟨n, hn1, hn2, hn3⟩ := hN (max N (b + 1)) (le_max_left _ _)
  have hnb : n ≤ b := hb hn3
  have := le_max_right N (b + 1)
  omega

/-! ## The two halves of the limsup -/

/-- Upper half: the gap after `u k` is at most `c ℓ (u k) + (c+2)` for all large `k`. -/
theorem gap_le_eventually (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (Cs : ℝ) (hCs : 0 ≤ Cs)
    (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (hsum : Summable (fun j => 1 / (m j : ℝ)))
    (T : ℕ) (c : ℝ) (hc0 : 0 < c)
    (hgap : 1 < c * (prefixDensity m T - tailSum m T))
    (hinf : {n | Avoids m n}.Infinite) :
    ∀ᶠ k : ℕ in atTop,
      ((Nat.nth (Avoids m) (k + 1) : ℝ) - (Nat.nth (Avoids m) k : ℝ)) ≤
        c * recordLogLog (Nat.nth (Avoids m) k : ℝ) + (c + 2) := by
  have hw := exists_avoids_in_short_window m hm2 hcop Cs hCs hscale hsum T c hc0 hgap
  have hsm : StrictMono (Nat.nth (Avoids m)) := Nat.nth_strictMono hinf
  have hut : Tendsto (Nat.nth (Avoids m)) atTop atTop := hsm.tendsto_atTop
  have hut1 : Tendsto (fun k => Nat.nth (Avoids m) k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_succ _) hut
  have h1 := hut1.eventually hw
  have h2 : ∀ᶠ k : ℕ in atTop, 4 ≤ Nat.nth (Avoids m) k := hut.eventually_ge_atTop 4
  filter_upwards [h1, h2] with k hk hk4
  obtain ⟨n, hn1, hn2, hn3⟩ := hk
  set u := Nat.nth (Avoids m) with hu
  have hnext : u (k + 1) ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hle := Nat.le_nth_of_lt_nth_succ hcon hn3
    rw [← hu] at hle
    omega
  have hu4 : (4 : ℝ) ≤ (u k : ℝ) := by exact_mod_cast hk4
  have hell : recordLogLog ((u k : ℝ) + 1) ≤ recordLogLog (u k : ℝ) + 1 :=
    recordLogLog_add_le hu4 (by linarith)
  have hcast : ((u k + 1 : ℕ) : ℝ) = (u k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hn2
  have hellnn : (0 : ℝ) ≤ recordLogLog ((u k : ℝ) + 1) :=
    le_trans zero_le_one (one_le_recordLogLog _)
  have hceil : ((⌈c * recordLogLog ((u k : ℝ) + 1)⌉₊ : ℕ) : ℝ) ≤
      c * recordLogLog ((u k : ℝ) + 1) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hc0.le hellnn)).le
  have hnR : (n : ℝ) < (u k : ℝ) + 1 + ((⌈c * recordLogLog ((u k : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
    have := (Nat.cast_lt (α := ℝ)).mpr hn2
    push_cast at this ⊢
    linarith
  have hnextR : ((u (k + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnext
  nlinarith [hell, hceil, hnR, hnextR, hc0]

/-- Lower half: a covered block of length `L` yields a late index `k` with a gap
of at least `L` and a height at most `T + K + C + 1`. -/
theorem exists_late_large_gap (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (Cs : ℝ) (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (C : ℕ) (hC : Cs ≤ (C : ℝ))
    (hinf : {n | Avoids m n}.Infinite) (T L N : ℕ)
    (hNbig : Nat.nth (Avoids m) N < 2 ^ (T + prefixCount m T 0 L)) :
    ∃ k, N ≤ k ∧
      (L : ℝ) ≤ (Nat.nth (Avoids m) (k + 1) : ℝ) - (Nat.nth (Avoids m) k : ℝ) ∧
      recordLogLog (Nat.nth (Avoids m) k : ℝ) ≤
        ((T + prefixCount m T 0 L + C + 1 : ℕ) : ℝ) := by
  classical
  haveI : DecidablePred (Avoids m) := Classical.decPred _
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_covered_block m hm2 hcop Cs hscale C hC T L
  set u := Nat.nth (Avoids m) with hu
  have hxgt : u N < x := lt_of_lt_of_le hNbig hx1
  have hcount1 : Nat.count (Avoids m) (u N + 1) = N + 1 :=
    Nat.count_nth_succ_of_infinite hinf N
  have hcm : Nat.count (Avoids m) (u N + 1) ≤ Nat.count (Avoids m) x :=
    Nat.count_monotone _ (by omega)
  set k := Nat.count (Avoids m) x - 1 with hk
  have hkN : N ≤ k := by omega
  have hcx : Nat.count (Avoids m) x = k + 1 := by omega
  have huk : u k < x := Nat.nth_lt_of_lt_count (by omega)
  have hxu : x ≤ u (k + 1) := by
    by_contra hcon
    push_neg at hcon
    have h1 : Nat.count (Avoids m) (u (k + 1) + 1) ≤ Nat.count (Avoids m) x :=
      Nat.count_monotone _ (by omega)
    rw [Nat.count_nth_succ_of_infinite hinf (k + 1)] at h1
    omega
  have hgapge : x + L ≤ u (k + 1) := by
    by_contra hcon
    push_neg at hcon
    refine hx3 (u (k + 1) - x) (by omega) ?_
    have hrw : x + (u (k + 1) - x) = u (k + 1) := by omega
    rw [hrw]
    exact Nat.nth_mem_of_infinite hinf (k + 1)
  refine ⟨k, hkN, ?_, ?_⟩
  · have h1 : (u k : ℝ) < (x : ℝ) := by exact_mod_cast huk
    have h2 : ((x + L : ℕ) : ℝ) ≤ ((u (k + 1) : ℕ) : ℝ) := by exact_mod_cast hgapge
    push_cast at h2
    linarith
  · have hxb : (x : ℝ) ≤ (binaryTower (T + prefixCount m T 0 L + C + 1) : ℝ) := by
      exact_mod_cast hx2
    have hukb : (u k : ℝ) ≤ (binaryTower (T + prefixCount m T 0 L + C + 1) : ℝ) := by
      have : (u k : ℝ) < (x : ℝ) := by exact_mod_cast huk
      linarith
    exact recordLogLog_le_of_le_binaryTower (by omega) hukb

/-! ## Assembling the limsup -/

/-- The elementary estimate behind `L / (T + K + C + 1) → σ_T⁻¹`. -/
theorem ratio_lower_bound_aux {A E ε L D σinv : ℝ}
    (hA : 0 < A) (hE : 0 < E) (hε : 0 < ε) (hL : 0 < L) (hD : 0 < D)
    (hT1 : σinv - ε / 2 < A⁻¹)
    (hL2 : 2 * E / (A ^ 2 * ε) ≤ L)
    (hDle : D ≤ A * L + E) :
    (σinv - ε) * D ≤ L := by
  have hAi : A⁻¹ * A = 1 := inv_mul_cancel₀ hA.ne'
  have h2E : 2 * E ≤ L * (A ^ 2 * ε) := (div_le_iff₀ (by positivity)).mp hL2
  have hAiE : A⁻¹ * E ≤ (ε / 2) * (A * L) := by
    have hEA : A⁻¹ * E = E / A := by rw [inv_mul_eq_div]
    rw [hEA, div_le_iff₀ hA]
    nlinarith [h2E]
  have hbA : (σinv - ε / 2) * A < 1 := by
    have h := mul_lt_mul_of_pos_right hT1 hA
    rwa [hAi] at h
  have hbAL : (σinv - ε / 2) * (A * L) ≤ L := by nlinarith [hbA, hL]
  have hbE : (σinv - ε / 2) * E ≤ A⁻¹ * E :=
    mul_le_mul_of_nonneg_right hT1.le hE.le
  have hmain : (σinv - ε) * (A * L + E) ≤ L := by
    nlinarith [hbAL, hbE, hAiE, mul_pos hε hE]
  rcases le_or_gt (σinv - ε) 0 with hs | hs
  · nlinarith [hs, hD, hL]
  · have := mul_le_mul_of_nonneg_left hDle hs.le
    linarith

/-- A two-sided characterisation of a real `limsup`. -/
theorem limsup_eq_of_bounds {g : ℕ → ℝ} {c : ℝ}
    (hA : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, g n ≤ c + ε)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, c - ε ≤ g n) :
    limsup g atTop = c := by
  rw [Filter.limsup_eq]
  set S := {a : ℝ | ∀ᶠ n in atTop, g n ≤ a} with hS
  have hlb : ∀ a ∈ S, c ≤ a := by
    intro a ha
    rw [hS, Set.mem_setOf_eq] at ha
    by_contra hcon
    push_neg at hcon
    obtain ⟨n, hn1, hn2⟩ :=
      (ha.and_frequently (hB ((c - a) / 2) (by linarith))).exists
    linarith
  have hne : S.Nonempty := ⟨c + 1, hA 1 one_pos⟩
  have hbdd : BddBelow S := ⟨c, hlb⟩
  refine le_antisymm ?_ (le_csInf hne hlb)
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < (sInf S - c) / 2 := by linarith
  have := csInf_le hbdd (hA _ hpos)
  linarith

/-! ## The paper's theorem -/

/-- **Erdős 243, `long243:res:gapconstant`.**  For pairwise coprime moduli
`m 0 < m 1 < ⋯`, all at least `2`, with `ℓ (m j) = j + O(1)`, and with
`σ = ∏ j (1 - 1/m j) > 0`, the increasing enumeration `u` of the positive
integers divisible by no `m j` satisfies
`limsup (u (n+1) - u n) / ℓ (u n) = σ⁻¹`. -/
theorem maximal_gap_limsup_eq_inv_sigma
    (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j) (hmono : StrictMono m)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (Cs : ℝ) (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (σ : ℝ) (hσpos : 0 < σ)
    (hσ : Tendsto (fun T => ∏ j ∈ Finset.range T, (1 - 1 / (m j : ℝ))) atTop (nhds σ)) :
    limsup (fun n : ℕ =>
        ((Nat.nth (Avoids m) (n + 1) : ℝ) - (Nat.nth (Avoids m) n : ℝ)) /
          recordLogLog (Nat.nth (Avoids m) n : ℝ)) atTop = σ⁻¹ := by
  classical
  have hm : ∀ j, 0 < m j := fun j => lt_of_lt_of_le (by norm_num) (hm2 j)
  have hCs : 0 ≤ Cs := le_trans (abs_nonneg _) (hscale 0)
  have hC : Cs ≤ ((⌈Cs⌉₊ : ℕ) : ℝ) := Nat.le_ceil Cs
  have hsum : Summable (fun j => 1 / (m j : ℝ)) :=
    summable_inv_modulus m hm2 Cs hscale ⌈Cs⌉₊ hC
  have hσ' : Tendsto (prefixDensity m) atTop (nhds σ) := hσ
  have hθ : Tendsto (tailSum m) atTop (nhds 0) := tailSum_tendsto_zero m
  have hdiff : Tendsto (fun T => prefixDensity m T - tailSum m T) atTop (nhds σ) := by
    simpa using hσ'.sub hθ
  obtain ⟨T₀, hT₀⟩ : ∃ T, 0 < prefixDensity m T - tailSum m T :=
    (hdiff.eventually_const_lt hσpos).exists
  have hinf : {n | Avoids m n}.Infinite :=
    infinite_avoids m hm2 hcop Cs hCs hscale hsum T₀ hT₀
  have hsm : StrictMono (Nat.nth (Avoids m)) := Nat.nth_strictMono hinf
  have hut : Tendsto (Nat.nth (Avoids m)) atTop atTop := hsm.tendsto_atTop
  have hσinvpos : (0 : ℝ) < σ⁻¹ := by positivity
  refine limsup_eq_of_bounds ?_ ?_
  · -- upper half
    intro ε hε
    have hinv : Tendsto (fun T => (prefixDensity m T - tailSum m T)⁻¹) atTop (nhds σ⁻¹) :=
      hdiff.inv₀ hσpos.ne'
    obtain ⟨T, hT1, hT2⟩ : ∃ T, (prefixDensity m T - tailSum m T)⁻¹ < σ⁻¹ + ε / 2 ∧
        0 < prefixDensity m T - tailSum m T :=
      ((hinv.eventually_lt_const (by linarith : σ⁻¹ < σ⁻¹ + ε / 2)).and
        (hdiff.eventually_const_lt hσpos)).exists
    have hc0 : (0 : ℝ) < σ⁻¹ + ε / 2 := by linarith
    have hgap : 1 < (σ⁻¹ + ε / 2) * (prefixDensity m T - tailSum m T) := by
      have h1 : (prefixDensity m T - tailSum m T)⁻¹ *
          (prefixDensity m T - tailSum m T) = 1 := inv_mul_cancel₀ hT2.ne'
      have h2 := mul_lt_mul_of_pos_right hT1 hT2
      rwa [h1] at h2
    have hgle := gap_le_eventually m hm2 hcop Cs hCs hscale hsum T (σ⁻¹ + ε / 2) hc0 hgap hinf
    have hKv : ∀ᶠ n : ℕ in atTop,
        2 * ((σ⁻¹ + ε / 2) + 2) / ε ≤ recordLogLog (Nat.nth (Avoids m) n : ℝ) :=
      hut.eventually (eventually_le_recordLogLog (2 * ((σ⁻¹ + ε / 2) + 2) / ε))
    filter_upwards [hgle, hKv] with n hn hK
    have hℓ1 : (1 : ℝ) ≤ recordLogLog (Nat.nth (Avoids m) n : ℝ) := one_le_recordLogLog _
    have hℓpos : (0 : ℝ) < recordLogLog (Nat.nth (Avoids m) n : ℝ) := by linarith
    have hid : (ε / 2) * (2 * ((σ⁻¹ + ε / 2) + 2) / ε) = (σ⁻¹ + ε / 2) + 2 := by
      field_simp
    have hstep : (σ⁻¹ + ε / 2) + 2 ≤
        (ε / 2) * recordLogLog (Nat.nth (Avoids m) n : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ ε / 2)
      linarith [hid.ge, hid.le]
    rw [div_le_iff₀ hℓpos]
    nlinarith [hn, hstep]
  · -- lower half
    intro ε hε
    have hσinvT : Tendsto (fun T => (prefixDensity m T)⁻¹) atTop (nhds σ⁻¹) :=
      hσ'.inv₀ hσpos.ne'
    obtain ⟨T, hT1⟩ : ∃ T, σ⁻¹ - ε / 2 < (prefixDensity m T)⁻¹ :=
      (hσinvT.eventually_const_lt (by linarith : σ⁻¹ - ε / 2 < σ⁻¹)).exists
    rw [Filter.frequently_atTop]
    intro N
    have hApos : 0 < prefixDensity m T := prefixDensity_pos m hm2 T
    have hMTpos : 0 < prefixModulus m T := Finset.prod_pos (fun j _ => hm j)
    have hEpos : (0 : ℝ) <
        (T : ℝ) + (prefixModulus m T : ℝ) + ((⌈Cs⌉₊ : ℕ) : ℝ) + 1 := by positivity
    obtain ⟨L, hL⟩ := exists_nat_ge
      (max (((Nat.nth (Avoids m) N : ℝ) + (prefixModulus m T : ℝ) + 1) / prefixDensity m T)
        (2 * ((T : ℝ) + (prefixModulus m T : ℝ) + ((⌈Cs⌉₊ : ℕ) : ℝ) + 1) /
          ((prefixDensity m T) ^ 2 * ε)))
    have hL1 := le_trans (le_max_left _ _) hL
    have hL2 := le_trans (le_max_right _ _) hL
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      have hq : (0 : ℝ) < ((Nat.nth (Avoids m) N : ℝ) + (prefixModulus m T : ℝ) + 1) /
          prefixDensity m T := by positivity
      linarith
    have hAL : (Nat.nth (Avoids m) N : ℝ) + (prefixModulus m T : ℝ) + 1 ≤
        prefixDensity m T * (L : ℝ) := by
      rw [div_le_iff₀ hApos] at hL1
      linarith
    have hKlow : prefixDensity m T * (L : ℝ) - (prefixModulus m T : ℝ) ≤
        (prefixCount m T 0 L : ℝ) := prefixCount_ge_real m hm hcop T 0 L
    have hKhigh : (prefixCount m T 0 L : ℝ) ≤
        prefixDensity m T * (L : ℝ) + (prefixModulus m T : ℝ) :=
      prefixCount_le_real m hm hcop T 0 L
    have huNK : Nat.nth (Avoids m) N < prefixCount m T 0 L := by
      have hr : ((Nat.nth (Avoids m) N : ℕ) : ℝ) < (prefixCount m T 0 L : ℝ) := by linarith
      exact_mod_cast hr
    have hNbig : Nat.nth (Avoids m) N < 2 ^ (T + prefixCount m T 0 L) := by
      have h1 : prefixCount m T 0 L + 1 ≤ 2 ^ (prefixCount m T 0 L) :=
        index_succ_le_two_pow _
      have h2 : (2 : ℕ) ^ (prefixCount m T 0 L) ≤ 2 ^ (T + prefixCount m T 0 L) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨k, hkN, hgapL, hℓD⟩ :=
      exists_late_large_gap m hm2 hcop Cs hscale ⌈Cs⌉₊ hC hinf T L N hNbig
    refine ⟨k, hkN, ?_⟩
    have hℓ1 : (1 : ℝ) ≤ recordLogLog (Nat.nth (Avoids m) k : ℝ) := one_le_recordLogLog _
    have hℓpos : (0 : ℝ) < recordLogLog (Nat.nth (Avoids m) k : ℝ) := by linarith
    have hDle : recordLogLog (Nat.nth (Avoids m) k : ℝ) ≤
        prefixDensity m T * (L : ℝ) +
          ((T : ℝ) + (prefixModulus m T : ℝ) + ((⌈Cs⌉₊ : ℕ) : ℝ) + 1) := by
      have hcast : ((T + prefixCount m T 0 L + ⌈Cs⌉₊ + 1 : ℕ) : ℝ)
          = (T : ℝ) + (prefixCount m T 0 L : ℝ) + ((⌈Cs⌉₊ : ℕ) : ℝ) + 1 := by
        push_cast; ring
      rw [hcast] at hℓD
      linarith
    have hkey := ratio_lower_bound_aux (A := prefixDensity m T)
      (E := (T : ℝ) + (prefixModulus m T : ℝ) + ((⌈Cs⌉₊ : ℕ) : ℝ) + 1) (ε := ε)
      (L := (L : ℝ)) (D := recordLogLog (Nat.nth (Avoids m) k : ℝ)) (σinv := σ⁻¹)
      hApos hEpos hε hLpos hℓpos hT1 hL2 hDle
    rw [le_div_iff₀ hℓpos]
    linarith

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.prefixCount_window
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exists_avoids_in_short_window
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exists_covered_block
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.gap_le_eventually
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exists_late_large_gap
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.maximal_gap_limsup_eq_inv_sigma

end ErdosProblems.Erdos243.PaperCompleteR21
