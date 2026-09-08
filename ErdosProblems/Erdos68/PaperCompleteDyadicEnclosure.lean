import ErdosProblems.Erdos68.PrimeUnitTranslator
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Round 8: finite dyadic enclosure interface for the actual factorial-gap series

No numerical target is assumed to be true in this file. `DyadicData.Valid` is a
finite integer predicate: a floor-sum equality and an explicit upper endpoint.
The analytic soundness proof uses the inherited positive tail and the bound
`factorialGapTail N < 1/N!`. This deliberately gives the slightly wider 80000-bit
interval of width 7056, rather than the historical interval of width 7053.
The returned Farey certificate is checked against the wider interval.

Status: proof text, not elaborated in the return environment.
Mathlib source pin: 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
-/

namespace ErdosProblems.Erdos68.PaperComplete.FiniteLead

open scoped BigOperators

/-- Every summation index is at least two: the term `1/(1!-1)` is absent. -/
def floorPrefix (scale cutoff : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 2 cutoff, scale / (n.factorial - 1)

structure DyadicData where
  bits : ℕ
  cutoff : ℕ
  lower : ℕ
  upper : ℕ
  deriving Repr

/-- Precise finite predicate for external replay and the separate kernel discharge. No real number,
rationality assertion or desired denominator exclusion occurs in this predicate. -/
def DyadicData.Valid (c : DyadicData) : Prop :=
  2 ≤ c.cutoff ∧
  c.lower = floorPrefix (2 ^ c.bits) c.cutoff ∧
  c.upper = c.lower + (Finset.Icc 2 c.cutoff).card +
    (2 ^ c.bits) / c.cutoff.factorial + 1

instance (c : DyadicData) : Decidable c.Valid := inferInstanceAs
  (Decidable (2 ≤ c.cutoff ∧
    c.lower = floorPrefix (2 ^ c.bits) c.cutoff ∧
    c.upper = c.lower + (Finset.Icc 2 c.cutoff).card +
      (2 ^ c.bits) / c.cutoff.factorial + 1))

/-- Natural Euclidean division gives the outward real rounding bounds. -/
private theorem nat_div_real_bounds (scale d : ℕ) (hd : 0 < d) :
    ((scale / d : ℕ) : ℝ) ≤ (scale : ℝ) / d ∧
      (scale : ℝ) / d < ((scale / d : ℕ) : ℝ) + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- Lean v4.29.1: Init/Data/Nat/Div/Basic.lean.
  have hloN : scale / d * d ≤ scale := Nat.div_mul_le_self scale d
  have hhiN : scale < (scale / d + 1) * d :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (scale / d))
  have hloR : ((scale / d : ℕ) : ℝ) * (d : ℝ) ≤ (scale : ℝ) := by
    exact_mod_cast hloN
  have hhiR : (scale : ℝ) < (((scale / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
    exact_mod_cast hhiN
  -- Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean,
  -- re-exported by Mathlib/Algebra/Order/Field/Basic.lean.
  exact ⟨(le_div_iff₀ hdR).mpr hloR, (div_lt_iff₀ hdR).mpr hhiR⟩

/-- Only the nonzero-denominator case is used. -/
private theorem factorial_gap_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < n.factorial - 1 := by
  -- Mathlib/Data/Nat/Factorial/Basic.lean (also used in the inherited library).
  have hn1 : 1 < n := by omega
  have hfac : 1 < n.factorial := Nat.one_lt_factorial.mpr hn1
  omega

private theorem factorial_gap_cast (n : ℕ) :
    ((n.factorial - 1 : ℕ) : ℝ) =
      ((((n.factorial : ℤ) - 1 : ℤ)) : ℝ) := by
  have hfac : 1 ≤ n.factorial := Nat.succ_le_of_lt (Nat.factorial_pos n)
  have hsub : n.factorial - 1 + 1 = n.factorial := Nat.sub_add_cancel hfac
  have hsubR : ((n.factorial - 1 : ℕ) : ℝ) + 1 = (n.factorial : ℝ) := by
    exact_mod_cast hsub
  push_cast
  all_goals linarith only [hsubR]

/-- Summing the outward rounding bounds loses at most one per prefix term. -/
private theorem scaled_prefix_bounds (scale cutoff : ℕ) :
    (floorPrefix scale cutoff : ℝ) ≤
      (scale : ℝ) *
        (∑ n ∈ Finset.Icc 2 cutoff, (1 : ℝ) / (n.factorial - 1 : ℕ)) ∧
    (scale : ℝ) *
        (∑ n ∈ Finset.Icc 2 cutoff, (1 : ℝ) / (n.factorial - 1 : ℕ)) ≤
      (floorPrefix scale cutoff : ℝ) + ((Finset.Icc 2 cutoff).card : ℝ) := by
  -- Mathlib/Order/Interval/Finset/Defs.lean: interval membership.
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 cutoff) :=
    nat_div_real_bounds scale (n.factorial - 1)
      (factorial_gap_pos (Finset.mem_Icc.mp hn).1)
  -- Mathlib/Algebra/Order/BigOperators/Group/Finset.lean: sum_le_sum.
  have hlo :
      (∑ n ∈ Finset.Icc 2 cutoff, ((scale / (n.factorial - 1) : ℕ) : ℝ)) ≤
        ∑ n ∈ Finset.Icc 2 cutoff, (scale : ℝ) / (n.factorial - 1 : ℕ) :=
    Finset.sum_le_sum (fun n hn => (hterm n hn).1)
  have hhi :
      (∑ n ∈ Finset.Icc 2 cutoff, (scale : ℝ) / (n.factorial - 1 : ℕ)) ≤
        ∑ n ∈ Finset.Icc 2 cutoff,
          (((scale / (n.factorial - 1) : ℕ) : ℝ) + 1) :=
    Finset.sum_le_sum (fun n hn => (hterm n hn).2.le)
  -- Mathlib/Algebra/BigOperators/Ring/Finset.lean: mul_sum and cast sums.
  have hscale :
      (∑ n ∈ Finset.Icc 2 cutoff, (scale : ℝ) / (n.factorial - 1 : ℕ)) =
        (scale : ℝ) *
          (∑ n ∈ Finset.Icc 2 cutoff, (1 : ℝ) / (n.factorial - 1 : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hcast :
      (∑ n ∈ Finset.Icc 2 cutoff, ((scale / (n.factorial - 1) : ℕ) : ℝ)) =
        (floorPrefix scale cutoff : ℝ) := by
    simp only [floorPrefix, Nat.cast_sum]
  have hone :
      (∑ n ∈ Finset.Icc 2 cutoff,
        (((scale / (n.factorial - 1) : ℕ) : ℝ) + 1)) =
        (floorPrefix scale cutoff : ℝ) + ((Finset.Icc 2 cutoff).card : ℝ) := by
    -- Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:
    -- sum_add_distrib is the additive form of prod_mul_distrib.
    rw [Finset.sum_add_distrib, hcast]
    simp
  rw [hcast, hscale] at hlo
  rw [hscale, hone] at hhi
  exact ⟨hlo, hhi⟩

/-- A valid finite floor-sum certificate encloses the actual series strictly. -/
theorem DyadicData.sound {c : DyadicData} (hc : c.Valid) :
    (c.lower : ℝ) / ((2 ^ c.bits : ℕ) : ℝ) < _root_.Erdos68.factorialGapSeries ∧
    _root_.Erdos68.factorialGapSeries < (c.upper : ℝ) / ((2 ^ c.bits : ℕ) : ℝ) := by
  obtain ⟨hN, hlo, hhi⟩ := hc
  have hscale : (0 : ℝ) < ((2 ^ c.bits : ℕ) : ℝ) := by positivity
  have hfac : 0 < c.cutoff.factorial := Nat.factorial_pos c.cutoff
  have hprefix := scaled_prefix_bounds (2 ^ c.bits) c.cutoff
  have hsplit : _root_.Erdos68.factorialGapSeries =
      (∑ n ∈ Finset.Icc 2 c.cutoff, (1 : ℝ) / (n.factorial - 1 : ℕ)) +
        _root_.Erdos68.factorialGapTail c.cutoff := by
    rw [_root_.Erdos68.factorialGapSeries_eq_sum_add_tail hN]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [factorial_gap_cast]
  have htailPos := _root_.Erdos68.factorialGapTail_pos hN
  have htailLt := _root_.Erdos68.factorialGapTail_lt_one_div_factorial hN
  have htailScaledPos :
      0 < ((2 ^ c.bits : ℕ) : ℝ) * (_root_.Erdos68.factorialGapTail c.cutoff : ℝ) :=
    mul_pos hscale htailPos
  have htailScaledLt :
      ((2 ^ c.bits : ℕ) : ℝ) * (_root_.Erdos68.factorialGapTail c.cutoff : ℝ) <
        ((2 ^ c.bits : ℕ) : ℝ) / (c.cutoff.factorial : ℝ) := by
    have h := mul_lt_mul_of_pos_left htailLt hscale
    convert h using 1 <;> ring
  have htailRound := (nat_div_real_bounds (2 ^ c.bits) c.cutoff.factorial hfac).2
  have hupperCast : (c.upper : ℝ) =
      (c.lower : ℝ) + ((Finset.Icc 2 c.cutoff).card : ℝ) +
        (((2 ^ c.bits) / c.cutoff.factorial : ℕ) : ℝ) + 1 := by
    exact_mod_cast hhi
  have hlowerCast : (c.lower : ℝ) = (floorPrefix (2 ^ c.bits) c.cutoff : ℝ) := by
    exact_mod_cast hlo
  have hscaledSplit :
      ((2 ^ c.bits : ℕ) : ℝ) * (_root_.Erdos68.factorialGapSeries : ℝ) =
        ((2 ^ c.bits : ℕ) : ℝ) *
          (∑ n ∈ Finset.Icc 2 c.cutoff, (1 : ℝ) / (n.factorial - 1 : ℕ)) +
        ((2 ^ c.bits : ℕ) : ℝ) * (_root_.Erdos68.factorialGapTail c.cutoff : ℝ) := by
    rw [hsplit]
    ring
  constructor
  · apply (div_lt_iff₀ hscale).mpr
    nlinarith only [hprefix.1, hlowerCast, htailScaledPos, hscaledSplit]
  · apply (lt_div_iff₀ hscale).mpr
    nlinarith only [hprefix.2, hlowerCast, hupperCast, htailScaledLt,
      htailRound, hscaledSplit]

end ErdosProblems.Erdos68.PaperComplete.FiniteLead
