import ErdosProblems.Erdos251.PaperBoundedCarryR7
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Data.Nat.Periodic

/-!
# The logarithmically growing value-6 countermodel

New UNCOMPILED proof source for the construction part of res:polignacfail.
This is not the already-checked bounded value-4 word.

The existential paper statement permits a different baseline from its proof:
we use B(n) = 6 + 2 floor(log(n+1)/2), so B(0)=6 is definitional up to simp.
All endpoint values, factorial locations, and eventual growth requirements
are unchanged. The PNT-scale cumulative assertion is in the companion file.

Pinned source APIs:
* Algebra/Order/Floor/Ring.lean: floor_mono, floor_add_one,
  lt_floor_add_one, floor_le (the latter imported from the floor definition).
* Analysis/SpecialFunctions/Log/Basic.lean: log_le_log, log_mul,
  log_le_sub_one_of_pos, tendsto_log_atTop.
* Data/Nat/Factorial/Basic.lean: factorial_pos, factorial_le, dvd_factorial.
* Order/Filter/AtTopBot/Archimedean.lean: tendsto_natCast_atTop_atTop.
-/

noncomputable section
open Filter Topology Finset

namespace ErdosProblems.Erdos251.PaperR8.LogCarry

/-- Natural-logarithmic, positive even baseline with initial value six. -/
def baseline (n : ℕ) : ℤ := 6 + 2 * Int.floor (Real.log ((n : ℝ) + 1) / 2)

@[simp] theorem baseline_zero : baseline 0 = 6 := by
  simp [baseline]

theorem baseline_ge_six (n : ℕ) : (6 : ℤ) ≤ baseline n := by
  have hl : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hf : (0 : ℤ) ≤ Int.floor (Real.log ((n : ℝ) + 1) / 2) :=
    Int.floor_nonneg.mpr (div_nonneg hl (by norm_num))
  unfold baseline
  omega

theorem baseline_even (n : ℕ) : (2 : ℤ) ∣ baseline n := by
  refine ⟨3 + Int.floor (Real.log ((n : ℝ) + 1) / 2), ?_⟩
  unfold baseline
  ring

theorem baseline_mono : Monotone baseline := by
  intro n m hnm
  have hcast : (n : ℝ) + 1 ≤ m + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  have hl := Real.log_le_log (by positivity : 0 < (n : ℝ) + 1) hcast
  have hd := div_le_div_of_nonneg_right hl (by norm_num : (0 : ℝ) ≤ 2)
  have hf := Int.floor_mono hd
  unfold baseline
  omega

/-- Two consecutive increments have total size at most two. -/
theorem baseline_two_step (n : ℕ) : baseline (n + 2) ≤ baseline n + 2 := by
  have hx : 0 < (n : ℝ) + 1 := by positivity
  have harg : (n : ℝ) + 3 ≤ 3 * ((n : ℝ) + 1) := by nlinarith
  have hl := Real.log_le_log (by positivity : 0 < (n : ℝ) + 3) harg
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx.ne'] at hl
  have h3 : Real.log 3 ≤ 2 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3) using 1 <;> norm_num
  have hdiv : Real.log ((n : ℝ) + 3) / 2 ≤ Real.log ((n : ℝ) + 1) / 2 + 1 := by
    linarith
  have hf := Int.floor_mono hdiv
  rw [Int.floor_add_one] at hf
  unfold baseline
  simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [show (n : ℝ) + 2 + 1 = (n : ℝ) + 3 by ring]
  omega

theorem baseline_step (n : ℕ) : baseline (n + 1) ≤ baseline n + 2 :=
  (baseline_mono (Nat.le_succ (n + 1))).trans (baseline_two_step n)

/-- The bounded error in the natural-logarithmic approximation. -/
theorem baseline_log_bounds (n : ℕ) :
    Real.log ((n : ℝ) + 1) + 4 ≤ (baseline n : ℝ) ∧
      (baseline n : ℝ) ≤ Real.log ((n : ℝ) + 1) + 6 := by
  have hf := Int.floor_le (Real.log ((n : ℝ) + 1) / 2)
  have hg := Int.lt_floor_add_one (Real.log ((n : ℝ) + 1) / 2)
  unfold baseline
  push_cast
  constructor <;> linarith

/-- A global linear bound used only to prove convergence of the tails. -/
theorem baseline_linear (n : ℕ) : baseline n ≤ (n : ℤ) + 6 := by
  have hl : Real.log ((n : ℝ) + 1) ≤ n := by
    simpa only [add_sub_cancel_right] using
      Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) + 1)
  have hb : (baseline n : ℝ) ≤ (n : ℝ) + 6 := (baseline_log_bounds n).2.trans (by linarith)
  exact_mod_cast hb

theorem baseline_tendsto_atTop : Tendsto baseline atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ n + 1)
    exact tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hb : Tendsto (fun n : ℕ => (baseline n : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono (f := fun n : ℕ => Real.log ((n : ℝ) + 1))
    · intro n
      linarith [(baseline_log_bounds n).1]
    · exact hl
  exact tendsto_intCast_atTop_iff.mp hb

def FirstSpike (n : ℕ) : Prop := ∃ k : ℕ, 5 ≤ k ∧ n = k.factorial
def SecondSpike (n : ℕ) : Prop := ∃ k : ℕ, 5 ≤ k ∧ n = 2 * k.factorial
def Special (n : ℕ) : Prop := FirstSpike n ∨ SecondSpike n

theorem special_ge (n : ℕ) (hn : Special n) : 120 ≤ n := by
  rcases hn with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · simpa using Nat.factorial_le hk
  · have h : 120 ≤ k.factorial := by simpa using Nat.factorial_le hk
    omega

theorem special_even (n : ℕ) (hn : Special n) : n % 2 = 0 := by
  rcases hn with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_factorial (by decide) (by omega))
  · omega

theorem special_not_predecessor {n : ℕ} (hn : Special n) : ¬ Special (n - 1) := by
  intro hp
  have h0 := special_even n hn
  have h1 := special_even (n - 1) hp
  have h2 := special_ge n hn
  omega

theorem first_second_disjoint {n : ℕ} (h1 : FirstSpike n) : ¬ SecondSpike n := by
  rintro ⟨k, hk, rfl⟩
  obtain ⟨j, hj, heq⟩ := h1
  apply PaperR7.not_factorial_spike_twice k (by omega)
  exact ⟨j, by omega, heq⟩

def carry (n : ℕ) : ℤ := by
  classical
  exact if FirstSpike n then 2 * baseline (n - 1) - 2
    else if SecondSpike n then 2 * baseline (n - 1) - 4
    else baseline n

def digit (n : ℕ) : ℤ := if n = 0 then 0 else 2 * carry (n - 1) - carry n

/-- The increasing odd synthetic position sequence in the paper. -/
def position (n : ℕ) : ℤ := 3 + ∑ j ∈ range n, digit (j + 1)

@[simp] theorem carry_zero : carry 0 = 6 := by
  classical
  have hn : ¬ Special 0 := by intro h; have := special_ge 0 h; omega
  have h1 : ¬ FirstSpike 0 := fun h => hn (Or.inl h)
  have h2 : ¬ SecondSpike 0 := fun h => hn (Or.inr h)
  simp [carry, h1, h2]

@[simp] theorem digit_zero : digit 0 = 0 := by simp [digit]
@[simp] theorem digit_succ (n : ℕ) : digit (n + 1) = 2 * carry n - carry (n + 1) := by
  simp [digit]

theorem carry_of_ordinary {n : ℕ} (h : ¬ Special n) : carry n = baseline n := by
  classical
  have h1 : ¬ FirstSpike n := fun hn => h (Or.inl hn)
  have h2 : ¬ SecondSpike n := fun hn => h (Or.inr hn)
  simp [carry, h1, h2]

theorem carry_bounds (n : ℕ) : baseline n ≤ carry n ∧ carry n ≤ 2 * baseline n := by
  classical
  by_cases hn : Special n
  · have hn1 : 1 ≤ n := (by decide : 1 ≤ 120).trans (special_ge n hn)
    have hstep : baseline n ≤ baseline (n - 1) + 2 := by
      simpa only [Nat.sub_add_cancel hn1] using baseline_step (n - 1)
    have hmono : baseline (n - 1) ≤ baseline n := baseline_mono (Nat.sub_le n 1)
    have h6 := baseline_ge_six (n - 1)
    unfold carry
    split_ifs <;> constructor <;> omega
  · rw [carry_of_ordinary hn]
    have h6 := baseline_ge_six n
    constructor <;> omega

theorem carry_even (n : ℕ) : (2 : ℤ) ∣ carry n := by
  classical
  unfold carry
  split_ifs
  · exact dvd_sub (dvd_mul_right 2 _) (dvd_refl 2)
  · exact dvd_sub (dvd_mul_right 2 _) (by norm_num)
  · exact baseline_even n

theorem digit_even (n : ℕ) : (2 : ℤ) ∣ digit n := by
  cases n with
  | zero => simp
  | succ n => rw [digit_succ]; exact dvd_sub (dvd_mul_right 2 _) (carry_even _)

theorem digit_at_first {n : ℕ} (h : FirstSpike n) : digit n = 2 := by
  classical
  have hs : Special n := Or.inl h
  have hp := carry_of_ordinary (special_not_predecessor hs)
  have hn : n ≠ 0 := by have := special_ge n hs; omega
  rw [digit, if_neg hn, hp]
  simp [carry, h]

theorem digit_at_second {n : ℕ} (h : SecondSpike n) : digit n = 4 := by
  classical
  have hs : Special n := Or.inr h
  have h1 : ¬ FirstSpike n := fun hn => first_second_disjoint hn h
  have hp := carry_of_ordinary (special_not_predecessor hs)
  have hn : n ≠ 0 := by have := special_ge n hs; omega
  rw [digit, if_neg hn, hp]
  simp [carry, h1, h]

theorem ordinary_digit_lower {n : ℕ} (hn : 1 ≤ n) (h : ¬ Special n) :
    baseline (n - 1) - 2 ≤ digit n := by
  have hc := (carry_bounds (n - 1)).1
  have hb : baseline n ≤ baseline (n - 1) + 2 := by
    simpa only [Nat.sub_add_cancel hn] using baseline_step (n - 1)
  have heq : digit n = 2 * carry (n - 1) - baseline n := by
    rw [digit, if_neg (by omega), carry_of_ordinary h]
  rw [heq]
  omega

theorem digit_positive (n : ℕ) (hn : 1 ≤ n) : 0 < digit n := by
  classical
  by_cases hs : Special n
  · rcases hs with h | h
    · rw [digit_at_first h]; norm_num
    · rw [digit_at_second h]; norm_num
  · have h1 := ordinary_digit_lower hn hs
    have h2 := baseline_ge_six (n - 1)
    omega

theorem digit_upper (n : ℕ) : digit n ≤ 4 * baseline n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [digit_succ]
      have h1 := (carry_bounds n).2
      have h2 := (baseline_ge_six (n + 1)).trans (carry_bounds (n + 1)).1
      have h3 : baseline n ≤ baseline (n + 1) := baseline_mono (Nat.le_succ n)
      omega

/-- Explicit pointwise logarithmic majorant; O(log n) follows for n>=2. -/
theorem digit_log_upper (n : ℕ) :
    (digit n : ℝ) ≤ 4 * Real.log ((n : ℝ) + 1) + 24 := by
  have hd : (digit n : ℝ) ≤ 4 * (baseline n : ℝ) := by exact_mod_cast digit_upper n
  linarith [(baseline_log_bounds n).2]

theorem digit_recurring_multiples (t N : ℕ) (ht : 0 < t) :
    ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧ digit i = 2 ∧ digit j = 4 := by
  let k := max 5 (max t (N + 1))
  have hk : 5 ≤ k := le_max_left _ _
  have ht' : t ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  have hN : N + 1 ≤ k := (le_max_right _ _).trans (le_max_right _ _)
  have hkf : k ≤ k.factorial := Nat.self_le_factorial k
  have hd : t ∣ k.factorial := Nat.dvd_factorial ht ht'
  exact ⟨k.factorial, 2 * k.factorial, by omega, by omega, hd,
    dvd_mul_of_dvd_right hd 2, digit_at_first ⟨k, hk, rfl⟩,
    digit_at_second ⟨k, hk, rfl⟩⟩

/-- Unboundedness occurs already at odd ordinary indices. -/
theorem digit_cofinally_unbounded (B : ℤ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B < digit n := by
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp
    (baseline_tendsto_atTop.eventually_gt_atTop (B + 2))
  let k := max J N
  have hkJ : J ≤ k := le_max_left _ _
  have hkN : N ≤ k := le_max_right _ _
  have hbase : B + 2 < baseline (2 * k) :=
    (hJ k hkJ).trans_le (baseline_mono (by omega))
  have ho : ¬ Special (2 * k + 1) := by
    intro hs
    have := special_even _ hs
    omega
  have hd := ordinary_digit_lower (n := 2 * k + 1) (by omega) ho
  simp only [Nat.add_sub_cancel] at hd
  exact ⟨2 * k + 1, by omega, by omega⟩

/-- Global nonnegativity, including the unused initial coefficient. -/
theorem digit_nonnegative (n : ℕ) : 0 ≤ digit n := by
  cases n with
  | zero => simp
  | succ n => exact (digit_positive (n + 1) (by omega)).le

/-- The unbounded word cannot become periodic. -/
theorem digit_not_eventually_periodic (h : ℕ) (hh : 0 < h) :
    ¬ ∃ N₀, ∀ n, N₀ ≤ n → digit (n + h) = digit n := by
  rintro ⟨N₀, hperiod⟩
  let f : ℕ → ℤ := fun k => digit (N₀ + k)
  have hf : Function.Periodic f h := by
    intro k
    simpa only [f, Nat.add_assoc] using hperiod (N₀ + k) (Nat.le_add_right _ _)
  let B : ℤ := ∑ k ∈ Finset.range h, f k
  obtain ⟨n, hn, hBn⟩ := digit_cofinally_unbounded B N₀
  let k := n - N₀
  have hnk : N₀ + k = n := Nat.add_sub_of_le hn
  have hk : k % h ∈ Finset.range h := Finset.mem_range.mpr (Nat.mod_lt _ hh)
  -- Mathlib/Data/Nat/Periodic.lean: Function.Periodic.map_mod_nat.
  have hbound : f k ≤ B := by
    calc
      f k = f (k % h) := (hf.map_mod_nat k).symm
      _ ≤ B := Finset.single_le_sum (fun i _ => digit_nonnegative (N₀ + i)) hk
  change digit (N₀ + k) ≤ B at hbound
  rw [hnk] at hbound
  exact (not_lt_of_ge hbound) hBn

/-- A literal eventual O(log n) inequality, with a fixed positive constant. -/
theorem digit_eventual_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → (digit n : ℝ) ≤ C * Real.log (n : ℝ) := by
  let l := Real.log 2
  have hl : 0 < l := Real.log_pos (by norm_num)
  refine ⟨8 + 24 / l, by positivity, ?_⟩
  intro n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : l ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hnR
  have harg : (n : ℝ) + 1 ≤ 2 * n := by linarith
  have hlog' := Real.log_le_log (by positivity : 0 < (n : ℝ) + 1) harg
  rw [Real.log_mul (by norm_num) (by positivity : (n : ℝ) ≠ 0)] at hlog'
  have hscale := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 24 / l)
  have hcancel : (24 / l) * l = (24 : ℝ) := div_mul_cancel₀ _ hl.ne'
  rw [hcancel] at hscale
  have hd := digit_log_upper n
  dsimp [l] at hlog hlog' hscale ⊢
  nlinarith

/-- Exact finite telescope, at every starting index. -/
theorem partial_telescope (N m : ℕ) :
    ∑ j ∈ range m, (digit (N + j + 1) : ℝ) / 2 ^ (j + 1) =
      (carry N : ℝ) - (carry (N + m) : ℝ) / 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hd : (digit (N + m + 1) : ℝ) =
          2 * (carry (N + m) : ℝ) - carry (N + m + 1) := by
        exact_mod_cast digit_succ (N + m)
      rw [hd, pow_succ]
      rw [show N + (m + 1) = N + m + 1 by omega]
      field_simp
      ring

/-- The terminal term vanishes by the global linear bound. -/
theorem terminal_tendsto_zero (N : ℕ) :
    Tendsto (fun m : ℕ => (carry (N + m) : ℝ) / 2 ^ m) atTop (𝓝 0) := by
  -- Analysis/SpecificLimits/Normed.lean, the same limit used by the desk's
  -- repaired PaperR7.factorialCarry_terminal_tendsto_zero.
  have h0 : Tendsto (fun m : ℕ => (m : ℝ)^0 / 2^m) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num)
  have h1 : Tendsto (fun m : ℕ => (m : ℝ)^1 / 2^m) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have hu : Tendsto (fun m : ℕ => 2 * ((N : ℝ) + m + 6) / 2 ^ m) atTop (𝓝 0) := by
    have h := (h1.const_mul 2).add (h0.const_mul (2 * ((N : ℝ) + 6)))
    convert h using 1 <;> simp only [pow_zero, pow_one, mul_zero, add_zero]
    funext m
    ring
  apply squeeze_zero (g := fun m : ℕ => 2 * ((N : ℝ) + m + 6) / 2 ^ m) ?_ ?_ hu
  · intro m
    have hc := (baseline_ge_six (N + m)).trans (carry_bounds (N + m)).1
    have hcR : (0 : ℝ) ≤ (carry (N + m) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ carry (N + m))
    exact div_nonneg hcR (by positivity)
  · intro m
    have h := (carry_bounds (N + m)).2
    have hb := baseline_linear (N + m)
    have ht : (carry (N + m) : ℝ) ≤ 2 * ((N : ℝ) + m + 6) := by
      exact_mod_cast (by omega : carry (N + m) ≤ 2 * ((N : ℤ) + m + 6))
    exact div_le_div_of_nonneg_right ht (by positivity)

/-- Complete tails, not merely formal recurrence values. -/
theorem hasSum_tail (N : ℕ) :
    HasSum (fun j : ℕ => (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (carry N : ℝ) := by
  have hpos : ∀ j : ℕ, 0 ≤ (digit (N + j + 1) : ℝ) / 2 ^ (j + 1) := by
    intro j
    have h : (0 : ℝ) ≤ (digit (N + j + 1) : ℝ) := by
      exact_mod_cast (digit_positive _ (by omega)).le
    exact div_nonneg h (by positivity)
  rw [hasSum_iff_tendsto_nat_of_nonneg hpos]
  have h := (tendsto_const_nhds (x := (carry N : ℝ))).sub (terminal_tendsto_zero N)
  simpa only [partial_telescope, sub_zero] using h

theorem hasSum_six :
    HasSum (fun j : ℕ => (digit (j + 1) : ℝ) / 2 ^ (j + 1)) 6 := by
  simpa using hasSum_tail 0

theorem all_tail_shifts_integral (N h : ℕ) :
    ∃ z : ℤ,
      (∑' j : ℕ, (digit (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
      (∑' j : ℕ, (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z := by
  refine ⟨carry (N + h) - carry N, ?_⟩
  rw [(hasSum_tail (N + h)).tsum_eq, (hasSum_tail N).tsum_eq]
  norm_cast

/-- The exact cumulative identity used for the separate asymptotic argument. -/
theorem position_identity (n : ℕ) :
    position n = 9 + ∑ j ∈ range n, carry j - carry n := by
  induction n with
  | zero => simp [position]
  | succ n ih =>
      have hpos : position (n + 1) = position n + digit (n + 1) := by
        simp only [position, Finset.sum_range_succ]
        ring
      rw [hpos, ih, digit_succ, Finset.sum_range_succ]
      ring

theorem position_strictMono : StrictMono position := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hd := digit_positive (n + 1) (by omega)
  have heq : position (n + 1) = position n + digit (n + 1) := by
    simp only [position, Finset.sum_range_succ]
    ring
  rw [heq]
  exact lt_add_of_pos_right _ hd

theorem position_odd (n : ℕ) : ∃ z : ℤ, position n = 2 * z + 1 := by
  have hd : (2 : ℤ) ∣ ∑ j ∈ range n, digit (j + 1) := by
    apply Finset.dvd_sum
    intro j hj
    exact digit_even (j + 1)
  obtain ⟨z, hz⟩ := hd
  refine ⟨z + 1, ?_⟩
  unfold position
  rw [hz]
  ring

#print axioms hasSum_six
#print axioms hasSum_tail
#print axioms digit_cofinally_unbounded
end ErdosProblems.Erdos251.PaperR8.LogCarry
