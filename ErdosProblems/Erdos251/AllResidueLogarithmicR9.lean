import ErdosProblems.Erdos251.AllResidueCarryCountermodel
import ErdosProblems.Erdos251.LogarithmicCarryAsymptoticsR8

/-!
# Complete every-residue logarithmic countermodel

Complete synthetic countermodel for the all-residue component of @paperresult:1.
Focused build and endpoint audit are recorded in the companion verification receipt.
It is not the factorial example with only zero-residue occurrences.
The already-supplied allResidueCentre and residue encoding are reused,
with the natural-log baseline from LogarithmicCarryR8. Every shifted
series is proved to have the displayed integral sum, and the reconstructed
positions have the exact asymptotic coefficient 1 in n log n.

Pinned additional API: Data/Nat/Pairing.lean, unpair_pair and right_le_pair.
All analytic APIs occur in the inspected R8 LogarithmicCarry modules.
-/

noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR9.AllResidueLog
open PaperR8.SparseSchedule

abbrev B := PaperR8.LogCarry.baseline
abbrev c := allResidueCentre

def Special (n : ℕ) : Prop := n ∈ Set.range c

def value : ℕ → ℕ := Function.extend c residueValue (fun _ => 2)

theorem value_at (j : ℕ) : value (c j) = residueValue j :=
  allResidueCentre_injective.extend_apply residueValue (fun _ => 2) j

theorem value_two_or_four (n : ℕ) : value n = 2 ∨ value n = 4 := by
  by_cases hs : Special n
  · obtain ⟨j, rfl⟩ := hs
    rw [value_at]
    exact residueValue_eq_two_or_four j
  · have he : value n = 2 := Function.extend_apply' residueValue (fun _ => 2) n hs
    exact Or.inl he

theorem special_ge_hundred {n : ℕ} (hs : Special n) : 100 ≤ n := by
  obtain ⟨j, rfl⟩ := hs
  exact allResidueCentre_ge_hundred j

theorem special_not_predecessor {n : ℕ} (hs : Special n) : ¬ Special (n - 1) := by
  obtain ⟨j, rfl⟩ := hs
  rintro ⟨i, hi⟩
  have hmin := allResidueCentre_ge_hundred j
  obtain hij | hij | hij := lt_trichotomy i j
  · have hsep := allResidueCentre_succ_ge i
    have hm := allResidueCentre_strictMono.monotone (Nat.succ_le_of_lt hij)
    simp only [c, Nat.succ_eq_add_one] at hi hm
    omega
  · subst i
    simp only [c] at hi
    omega
  · have hm := allResidueCentre_strictMono hij
    simp only [c] at hi
    omega

theorem special_not_successor {n : ℕ} (hs : Special n) : ¬ Special (n + 1) := by
  intro hnext
  have h := special_not_predecessor hnext
  apply h
  simpa only [Nat.add_sub_cancel] using hs

def carry (n : ℕ) : ℤ := by
  classical
  exact if Special n then 2 * B (n - 1) - (value n : ℤ) else B n

def digit (n : ℕ) : ℤ := if n = 0 then 0 else 2 * carry (n - 1) - carry n

def position (n : ℕ) : ℤ := 3 + ∑ j ∈ range n, digit (j + 1)

theorem carry_ordinary {n : ℕ} (hs : ¬ Special n) : carry n = B n := by
  classical
  exact if_neg hs

theorem carry_special {n : ℕ} (hs : Special n) :
    carry n = 2 * B (n - 1) - (value n : ℤ) := by
  classical
  exact if_pos hs

@[simp] theorem carry_zero : carry 0 = 6 := by
  have hs : ¬ Special 0 := by intro h; have := special_ge_hundred h; omega
  rw [carry_ordinary hs]
  exact PaperR8.LogCarry.baseline_zero

@[simp] theorem digit_zero : digit 0 = 0 := by simp [digit]
@[simp] theorem digit_succ (n : ℕ) : digit (n + 1) = 2 * carry n - carry (n + 1) := by
  simp only [digit, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    if_false, Nat.add_sub_cancel]

theorem carry_bounds (n : ℕ) : B n ≤ carry n ∧ carry n ≤ 2 * B n := by
  by_cases hs : Special n
  · have hn : 1 ≤ n := (by decide : 1 ≤ 100).trans (special_ge_hundred hs)
    have hstep : B n ≤ B (n - 1) + 2 := by
      simpa only [Nat.sub_add_cancel hn] using PaperR8.LogCarry.baseline_step (n - 1)
    have hmono := PaperR8.LogCarry.baseline_mono (Nat.sub_le n 1)
    have h6 := PaperR8.LogCarry.baseline_ge_six (n - 1)
    rw [carry_special hs]
    simp only [B] at hstep ⊢
    rcases value_two_or_four n with hv | hv <;> rw [hv] <;> constructor <;> omega
  · rw [carry_ordinary hs]
    have h6 := PaperR8.LogCarry.baseline_ge_six n
    simp only [B]
    constructor <;> omega

theorem carry_even (n : ℕ) : (2 : ℤ) ∣ carry n := by
  by_cases hs : Special n
  · rw [carry_special hs]
    have hv : (2 : ℤ) ∣ (value n : ℤ) := by
      rcases value_two_or_four n with hv | hv <;> rw [hv] <;> norm_num
    exact dvd_sub (dvd_mul_right 2 _) hv
  · rw [carry_ordinary hs]
    exact PaperR8.LogCarry.baseline_even n

theorem digit_at_centre (j : ℕ) : digit (c j) = (residueValue j : ℤ) := by
  have hs : Special (c j) := ⟨j, rfl⟩
  have hp := special_not_predecessor hs
  have hn : c j ≠ 0 := by have := special_ge_hundred hs; omega
  rw [digit, if_neg hn, carry_ordinary hp, carry_special hs, value_at]
  ring

theorem ordinary_digit_lower {n : ℕ} (hn : 1 ≤ n) (hs : ¬ Special n) :
    B (n - 1) - 2 ≤ digit n := by
  have hc := (carry_bounds (n - 1)).1
  have hb : B n ≤ B (n - 1) + 2 := by
    simpa only [Nat.sub_add_cancel hn] using PaperR8.LogCarry.baseline_step (n - 1)
  rw [digit, if_neg (by omega), carry_ordinary hs]
  omega

theorem digit_positive (n : ℕ) (hn : 1 ≤ n) : 0 < digit n := by
  by_cases hs : Special n
  · obtain ⟨j, rfl⟩ := hs
    rw [digit_at_centre]
    rcases residueValue_eq_two_or_four j with h | h <;> rw [h] <;> norm_num
  · have h := ordinary_digit_lower hn hs
    have hb := PaperR8.LogCarry.baseline_ge_six (n - 1)
    simp only [B] at h
    omega

theorem digit_nonnegative (n : ℕ) : 0 ≤ digit n := by
  cases n with
  | zero => simpa only [digit_zero] using (le_refl (0 : ℤ))
  | succ n => exact (digit_positive _ (by omega)).le

theorem digit_even (n : ℕ) : (2 : ℤ) ∣ digit n := by
  cases n with
  | zero => rw [digit_zero]; exact dvd_zero 2
  | succ n => rw [digit_succ]; exact dvd_sub (dvd_mul_right 2 _) (carry_even _)

theorem digit_log_bound (n : ℕ) :
    (digit n : ℝ) ≤ 4 * Real.log ((n : ℝ) + 1) + 24 := by
  have hup : digit n ≤ 4 * B n := by
    cases n with
    | zero =>
      rw [digit_zero]
      have := PaperR8.LogCarry.baseline_ge_six 0
      simp only [B]
      omega
    | succ n =>
      rw [digit_succ]
      have h1 := (carry_bounds n).2
      have h2 := (PaperR8.LogCarry.baseline_ge_six (n + 1)).trans (carry_bounds (n + 1)).1
      have h3 := PaperR8.LogCarry.baseline_mono (Nat.le_succ n)
      simp only [B, Nat.succ_eq_add_one] at h1 h3 ⊢
      omega
  have hcast : (digit n : ℝ) ≤ 4 * (B n : ℝ) := by exact_mod_cast hup
  have hb := (PaperR8.LogCarry.baseline_log_bounds n).2
  linarith

/-- Arbitrarily late occurrences in EVERY residue class. The third pairing
coordinate carries a freely growing repetition index; one occurrence per
class would not be enough. -/
theorem recurring_every_residue (t r N : ℕ) (ht : 0 < t) (hr : r < t) :
    ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ i % t = r ∧ j % t = r ∧
      digit i = 2 ∧ digit j = 4 := by
  let j₀ := Nat.pair (t - 1) (Nat.pair r (2 * N))
  let j₁ := Nat.pair (t - 1) (Nat.pair r (2 * N + 1))
  have hmod (b : ℕ) : residueModulus (Nat.pair (t - 1) (Nat.pair r b)) = t := by
    simp only [residueModulus, Nat.unpair_pair, Nat.sub_add_cancel ht]
  have hclass (b : ℕ) : residueClass (Nat.pair (t - 1) (Nat.pair r b)) = r := by
    simp only [residueClass, Nat.unpair_pair, hmod, Nat.mod_eq_of_lt hr]
  have hv₀ : residueValue j₀ = 2 := by
    have hb : (2 * N) % 2 = 0 := by omega
    simp [j₀, residueValue, Nat.unpair_pair, hb]
  have hv₁ : residueValue j₁ = 4 := by
    have hb : (2 * N + 1) % 2 ≠ 0 := by omega
    simp only [j₁, residueValue, Nat.unpair_pair, if_neg hb]
  have hN₀ : N ≤ c j₀ := by
    have h1 := Nat.right_le_pair r (2 * N)
    have h2 := Nat.right_le_pair (t - 1) (Nat.pair r (2 * N))
    have h3 := allResidueCentre_gt_index j₀
    dsimp [j₀, c] at h3 ⊢
    omega
  have hN₁ : N ≤ c j₁ := by
    have h1 := Nat.right_le_pair r (2 * N + 1)
    have h2 := Nat.right_le_pair (t - 1) (Nat.pair r (2 * N + 1))
    have h3 := allResidueCentre_gt_index j₁
    dsimp [j₁, c] at h3 ⊢
    omega
  have hc₀ : c j₀ % t = r := by
    have h := allResidueCentre_modEq j₀
    simpa only [j₀, Nat.ModEq, hmod, hclass, Nat.mod_eq_of_lt hr] using h
  have hc₁ : c j₁ % t = r := by
    have h := allResidueCentre_modEq j₁
    simpa only [j₁, Nat.ModEq, hmod, hclass, Nat.mod_eq_of_lt hr] using h
  refine ⟨c j₀, c j₁, hN₀, hN₁, hc₀, hc₁, ?_, ?_⟩
  · simp only [digit_at_centre, hv₀, Nat.cast_ofNat]
  · simp only [digit_at_centre, hv₁, Nat.cast_ofNat]

/-- Unbounded values occur immediately after the scheduled small values. -/
theorem digit_cofinally_unbounded (B₀ : ℤ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B₀ < digit n := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (PaperR8.LogCarry.baseline_tendsto_atTop.eventually_gt_atTop (B₀ + 2))
  let j := max N K
  have hcj : j ≤ c j := Nat.le_of_lt_succ (allResidueCentre_gt_index j)
  have hKN : K ≤ c j := (le_max_right _ _).trans hcj
  have hNN : N ≤ c j := (le_max_left _ _).trans hcj
  have hs : Special (c j) := ⟨j, rfl⟩
  have hn := ordinary_digit_lower (show 1 ≤ c j + 1 by omega)
    (special_not_successor hs)
  have hB := hK (c j) hKN
  simp only [Nat.add_sub_cancel, B] at hn
  exact ⟨c j + 1, by omega, by omega⟩

theorem digit_not_eventually_periodic (h : ℕ) (hh : 0 < h) :
    ¬ ∃ N₀, ∀ n, N₀ ≤ n → digit (n + h) = digit n := by
  rintro ⟨N₀, hperiod⟩
  let f : ℕ → ℤ := fun k => digit (N₀ + k)
  have hf : Function.Periodic f h := by
    intro k
    simpa only [f, Nat.add_assoc] using hperiod (N₀ + k) (Nat.le_add_right _ _)
  let B₀ : ℤ := ∑ k ∈ Finset.range h, f k
  obtain ⟨n, hn, hBn⟩ := digit_cofinally_unbounded B₀ N₀
  let k := n - N₀
  have hnk : N₀ + k = n := Nat.add_sub_of_le hn
  have hk : k % h ∈ Finset.range h := Finset.mem_range.mpr (Nat.mod_lt _ hh)
  have hbound : f k ≤ B₀ := by
    calc
      f k = f (k % h) := (hf.map_mod_nat k).symm
      _ ≤ B₀ := Finset.single_le_sum (fun i _ => digit_nonnegative (N₀ + i)) hk
  change digit (N₀ + k) ≤ B₀ at hbound
  rw [hnk] at hbound
  exact (not_lt_of_ge hbound) hBn

theorem position_succ (n : ℕ) : position (n + 1) = position n + digit (n + 1) := by
  simp only [position, sum_range_succ]
  ring

theorem position_strictMono : StrictMono position := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [position_succ]
  exact lt_add_of_pos_right _ (digit_positive _ (by omega))

theorem position_odd (n : ℕ) : ∃ z : ℤ, position n = 2 * z + 1 := by
  induction n with
  | zero => exact ⟨1, by simp only [position, sum_range_zero]; norm_num⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := digit_even (n + 1)
    exact ⟨z + w, by rw [position_succ, hz, hw]; ring⟩

/-- Positivity and complete sums require a vanishing terminal term.
The existing factorial-word limit is used only as a positive majorant. -/
theorem terminal_tendsto_zero (N : ℕ) :
    Tendsto (fun m : ℕ => (carry (N + m) : ℝ) / 2 ^ m) atTop (𝓝 0) := by
  have hu : Tendsto (fun m : ℕ => 2 * ((PaperR8.LogCarry.carry (N + m) : ℝ) / 2 ^ m))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (PaperR8.LogCarry.terminal_tendsto_zero N).const_mul 2
  apply squeeze_zero (g := fun m : ℕ =>
    2 * ((PaperR8.LogCarry.carry (N + m) : ℝ) / 2 ^ m)) ?_ ?_ hu
  · intro m
    have hp := (PaperR8.LogCarry.baseline_ge_six (N + m)).trans (carry_bounds (N + m)).1
    have hpR : (0 : ℝ) ≤ (carry (N + m) : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ carry (N + m) by omega)
    exact div_nonneg hpR (by positivity)
  · intro m
    have h1 := (carry_bounds (N + m)).2
    have h2 := (PaperR8.LogCarry.carry_bounds (N + m)).1
    simp only [B] at h1
    have h : (carry (N + m) : ℝ) ≤ 2 * (PaperR8.LogCarry.carry (N + m) : ℝ) := by
      exact_mod_cast (show carry (N + m) ≤ 2 * PaperR8.LogCarry.carry (N + m) by omega)
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h
      (show (0 : ℝ) ≤ 2 ^ m by positivity)

theorem partial_telescope (N m : ℕ) :
    ∑ j ∈ range m, (digit (N + j + 1) : ℝ) / 2 ^ (j + 1) =
      (carry N : ℝ) - (carry (N + m) : ℝ) / 2 ^ m := by
  induction m with
  | zero => simp only [Finset.sum_range_zero, Nat.add_zero, pow_zero, div_one, sub_self]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hd : (digit (N + m + 1) : ℝ) = 2 * (carry (N + m) : ℝ) - carry (N + m + 1) := by
      exact_mod_cast digit_succ (N + m)
    rw [hd, pow_succ, show N + (m + 1) = N + m + 1 by omega]
    field_simp <;> ring

theorem hasSum_tail (N : ℕ) :
    HasSum (fun j : ℕ => (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (carry N : ℝ) := by
  have hn : ∀ j, 0 ≤ (digit (N + j + 1) : ℝ) / 2 ^ (j + 1) := by
    intro j
    have hp : (0 : ℝ) ≤ (digit (N + j + 1) : ℝ) := by exact_mod_cast digit_nonnegative _
    exact div_nonneg hp (by positivity)
  rw [hasSum_iff_tendsto_nat_of_nonneg hn]
  have h := (tendsto_const_nhds (x := (carry N : ℝ))).sub (terminal_tendsto_zero N)
  simpa only [partial_telescope, sub_zero] using h

theorem hasSum_six : HasSum (fun j : ℕ => (digit (j + 1) : ℝ) / 2 ^ (j + 1)) 6 := by
  simpa using hasSum_tail 0

theorem all_tail_shifts_integral (N h : ℕ) :
    ∃ z : ℤ,
      (∑' j : ℕ, (digit (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
      (∑' j : ℕ, (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z := by
  refine ⟨carry (N + h) - carry N, ?_⟩
  rw [(hasSum_tail (N + h)).tsum_eq, (hasSum_tail N).tsum_eq]
  norm_cast

/-- The inherited exponentially delayed centres have a quadratic lower
bound, sufficient for the cumulative-growth proof. -/
theorem square_le_centre (j : ℕ) : j * j ≤ c j := by
  cases j with
  | zero => exact Nat.zero_le _
  | succ j =>
    have hp : (j + 1) * (j + 1) ≤ 2 ^ ((j + 1) * (j + 1)) :=
      (Nat.lt_pow_self (by decide : 1 < 2)).le
    have hmax : 2 ^ ((j + 1) * (j + 1)) ≤
        max 100 (max (2 ^ ((j + 1) * (j + 1))) (c j + 3)) :=
      le_max_of_le_right (le_max_left _ _)
    exact hp.trans (hmax.trans (alignResidue_ge _ _ _))

def specialCount (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter Special).card

theorem specialCount_bound (R N : ℕ) (hR : 0 < R) :
    specialCount N ≤ R + N / R + 1 := by
  classical
  have hcard : specialCount N = (indexSlice c 0 N).card := by
    simpa only [specialCount, Special, supportSlice, Nat.zero_add, Nat.Ico_zero_eq_range]
      using supportSlice_card c allResidueCentre_strictMono 0 N
  rw [hcard]
  have hsub : indexSlice c 0 N ⊆ range (R + N / R + 1) := by
    intro j hj
    have hb := (mem_filter.mp hj).2
    by_cases hjR : j < R
    · exact mem_range.mpr (hjR.trans_le
        ((Nat.le_add_right R (N / R)).trans (Nat.le_succ _)))
    · have hmul : j * R ≤ N := by
        have hsq := square_le_centre j
        have hRJ : R ≤ j := Nat.le_of_not_gt hjR
        have hprod := Nat.mul_le_mul_left j hRJ
        omega
      have hdiv : j ≤ N / R := (Nat.le_div_iff_mul_le hR).mpr hmul
      exact mem_range.mpr (by omega)
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem specialCount_budget (R : ℕ) (hR : 0 < R) :
    ∃ N₀, ∀ N, N₀ ≤ N → R * specialCount N ≤ N := by
  refine ⟨2 * R * (2 * R + 1), ?_⟩
  intro N hN
  have hc := specialCount_bound (2 * R) N (by omega)
  have hd := Nat.div_mul_le_self N (2 * R)
  have hs := Nat.mul_le_mul_left (2 * R) hc
  nlinarith

theorem specialCount_div_tendsto_zero :
    Tendsto (fun N : ℕ => (specialCount N : ℝ) / N) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R, hRε⟩ := exists_nat_gt (1 / ε)
  have hRP : (0 : ℝ) < R := lt_trans (by positivity) hRε
  have hRN : 0 < R := by exact_mod_cast hRP
  obtain ⟨N₀, hN₀⟩ := specialCount_budget R hRN
  refine ⟨max 1 N₀, ?_⟩
  intro N hN
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (R : ℝ) * specialCount N ≤ N := by
    exact_mod_cast hN₀ N ((le_max_right _ _).trans hN)
  have hr : (specialCount N : ℝ) / N ≤ 1 / (R : ℝ) := by
    apply (div_le_div_iff₀ hNP hRP).mpr
    nlinarith
  have he : 1 / (R : ℝ) < ε := by
    apply (div_lt_iff₀ hRP).mpr
    have h := (div_lt_iff₀ hε).mp hRε
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNP.le)]
  exact hr.trans_lt he

/-- The only change to the baseline is on the actual every-residue centres. -/
def excess (N : ℕ) : ℝ := ∑ j ∈ range N, ((carry j : ℝ) - B j)

theorem excess_bounds (N : ℕ) :
    0 ≤ excess N ∧ excess N ≤ (B N : ℝ) * specialCount N := by
  classical
  have hp (j : ℕ) : 0 ≤ (carry j : ℝ) - B j :=
    sub_nonneg.mpr (by exact_mod_cast (carry_bounds j).1)
  refine ⟨Finset.sum_nonneg (fun j _ => hp j), ?_⟩
  have ht : ∀ j ∈ range N,
      (carry j : ℝ) - B j ≤ if Special j then (B N : ℝ) else 0 := by
    intro j hj
    by_cases hs : Special j
    · rw [if_pos hs]
      have h1 : (carry j : ℝ) ≤ 2 * (B j : ℝ) := by exact_mod_cast (carry_bounds j).2
      have h2 : (B j : ℝ) ≤ B N := by
        exact_mod_cast PaperR8.LogCarry.baseline_mono (Nat.le_of_lt (mem_range.mp hj))
      linarith
    · rw [if_neg hs, carry_ordinary hs]
      simp only [sub_self, le_refl]
  have h := Finset.sum_le_sum ht
  have he : (∑ j ∈ range N, if Special j then (B N : ℝ) else 0) =
      (B N : ℝ) * specialCount N := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, specialCount, mul_comm]
  exact h.trans_eq he

theorem excess_normalized_zero :
    Tendsto (fun N : ℕ => excess N / ((N : ℝ) * Real.log N)) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => 3 * ((specialCount N : ℝ) / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using specialCount_div_tendsto_zero.const_mul 3
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
    exact div_nonneg (excess_bounds N).1
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ),
      PaperR8.LogCarry.baseline_le_three_log_eventually] with N hN hB
    have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hLP : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    apply (div_le_iff₀ (mul_pos hNP hLP)).mpr
    calc
      excess N ≤ (B N : ℝ) * specialCount N := (excess_bounds N).2
      _ ≤ (3 * Real.log N) * specialCount N :=
        mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg _)
      _ = (3 * ((specialCount N : ℝ) / N)) * ((N : ℝ) * Real.log N) := by
        field_simp [hNP.ne'] <;> ring

theorem endpoint_normalized_zero :
    Tendsto (fun N : ℕ => (carry N : ℝ) / ((N : ℝ) * Real.log N)) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => 2 * ((PaperR8.LogCarry.carry N : ℝ) /
      ((N : ℝ) * Real.log N))) atTop (𝓝 0) := by
    simpa only [mul_zero] using PaperR8.LogCarry.endpoint_normalized_tendsto_zero.const_mul 2
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
    have hc := (PaperR8.LogCarry.baseline_ge_six N).trans (carry_bounds N).1
    have hcR : (0 : ℝ) ≤ (carry N : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ carry N by omega)
    exact div_nonneg hcR
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
    have h1 := (carry_bounds N).2
    have h2 := (PaperR8.LogCarry.carry_bounds N).1
    simp only [B] at h1
    have hC : (carry N : ℝ) ≤ 2 * (PaperR8.LogCarry.carry N : ℝ) := by
      exact_mod_cast (show carry N ≤ 2 * PaperR8.LogCarry.carry N by omega)
    have hD : (0 : ℝ) ≤ (N : ℝ) * Real.log N :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hC hD

theorem position_identity (N : ℕ) :
    position N = 9 + ∑ j ∈ range N, carry j - carry N := by
  induction N with
  | zero => simp only [position, sum_range_zero, add_zero, carry_zero]; norm_num
  | succ N ih =>
    have hp : position (N + 1) = position N + digit (N + 1) := by
      simp only [position, sum_range_succ]
      ring
    rw [hp, ih, digit_succ, Finset.sum_range_succ]
    ring

theorem position_PNT_scale :
    Tendsto (fun N : ℕ => (position N : ℝ) / ((N : ℝ) * Real.log N)) atTop (𝓝 1) := by
  have h9 : Tendsto (fun N : ℕ => (9 : ℝ) / ((N : ℝ) * Real.log N)) atTop (𝓝 0) := by
    have hn : Tendsto (fun N : ℕ => (9 : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hl : Tendsto (fun N : ℕ => (1 : ℝ) / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop PaperR8.LogCarry.log_nat_tendsto_atTop
    simpa only [zero_mul, mul_one_div, div_div] using hn.mul hl
  have hm := PaperR8.LogCarry.baselineSum_asymptotic.add excess_normalized_zero
  have hlim := (h9.add hm).sub endpoint_normalized_zero
  have heq (N : ℕ) :
      (9 : ℝ) / ((N : ℝ) * Real.log N) +
        (PaperR8.LogCarry.baselineSum N / ((N : ℝ) * Real.log N) +
          excess N / ((N : ℝ) * Real.log N)) -
        (carry N : ℝ) / ((N : ℝ) * Real.log N) =
      (position N : ℝ) / ((N : ℝ) * Real.log N) := by
    have hp : (position N : ℝ) = 9 + (∑ j ∈ range N, (carry j : ℝ)) - carry N := by
      exact_mod_cast position_identity N
    have hs : PaperR8.LogCarry.baselineSum N + excess N = ∑ j ∈ range N, (carry j : ℝ) := by
      unfold PaperR8.LogCarry.baselineSum excess
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hp, ← hs]
    ring
  simpa only [heq, zero_add, add_zero, sub_zero] using hlim

/-- The precise missing summary-panel component, now including complete
tails and natural-logarithmic cumulative growth. It is a synthetic word. -/
theorem every_residue_countermodel :
    (∀ n, 1 ≤ n → 0 < digit n ∧ (2 : ℤ) ∣ digit n) ∧
    (∀ t r : ℕ, 0 < t → r < t → ∀ N : ℕ,
      ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ i % t = r ∧ j % t = r ∧ digit i = 2 ∧ digit j = 4) ∧
    (∀ B₀ : ℤ, ∀ N : ℕ, ∃ n, N ≤ n ∧ B₀ < digit n) ∧
    (∀ h : ℕ, 0 < h → ¬ ∃ N₀, ∀ n, N₀ ≤ n → digit (n + h) = digit n) ∧
    (∀ n : ℕ, (digit n : ℝ) ≤ 4 * Real.log ((n : ℝ) + 1) + 24) ∧
    StrictMono position ∧ (∀ n, ∃ z : ℤ, position n = 2 * z + 1) ∧
    HasSum (fun j : ℕ => (digit (j + 1) : ℝ) / 2 ^ (j + 1)) 6 ∧
    (∀ N : ℕ, HasSum (fun j : ℕ => (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (carry N : ℝ)) ∧
    (∀ N h : ℕ, ∃ z : ℤ,
      (∑' j : ℕ, (digit (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
      (∑' j : ℕ, (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z) ∧
    Tendsto (fun N : ℕ => (position N : ℝ) / ((N : ℝ) * Real.log N)) atTop (𝓝 1) := by
  exact ⟨fun n hn => ⟨digit_positive n hn, digit_even n⟩,
    fun t r ht hr N => recurring_every_residue t r N ht hr,
    digit_cofinally_unbounded, digit_not_eventually_periodic, digit_log_bound,
    position_strictMono, position_odd, hasSum_six, hasSum_tail, all_tail_shifts_integral, position_PNT_scale⟩

#print axioms every_residue_countermodel
#print axioms recurring_every_residue
#print axioms position_PNT_scale
end ErdosProblems.Erdos251.PaperR9.AllResidueLog
