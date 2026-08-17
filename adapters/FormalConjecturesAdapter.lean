/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.CertificateKernel

/-!
# Adapter: Formal Conjectures statement forms

Google DeepMind's Formal Conjectures records, for several Erdős problems, the
*known-true* statement whose formal proof it does not yet have. Three of those
declared holes are the same mathematics as `irrational_erdosSum_full_support`
(Erdős 1948, every integer base `b ≥ 2`), stated in three different index and
coefficient conventions.

A `formal_proof` link is only honest if the linked theorem is the *same
proposition* as the upstream statement, not a nearby one. This module therefore
states each upstream proposition verbatim and derives it from the corpus, so the
link target is the exact statement upstream carries.

Upstream targets, at `google-deepmind/formal-conjectures`
commit `398958d3964d738886bd24433918c365df4a2aab`:

| Upstream declaration | File:line | Category |
|---|---|---|
| `Erdos257.erdos_257.variants.tsum_top` | `ErdosProblems/257.lean:96` | `research solved` |
| `Erdos258.erdos_258.variants.constant` | `ErdosProblems/258.lean:65` | `research solved` |
| `Erdos1049.erdos_1049.variants.geq_2_integer` | `ErdosProblems/1049.lean:48` | `research solved` |

Boundary. Nothing here is a novelty claim. Erdős proved this in 1948 and the
corpus types it `formalised here`. The contribution is that upstream carries the
statement as an unfilled hole and this corpus carries a `sorry`-free, axiom-free
proof of it. Erdős #257 in its universal form, and #1049 for rational bases,
both remain open and are untouched by this module.

The bridging steps were independently machine-checked against Formal
Conjectures' own Mathlib pin (`leanprover/lean4:v4.27.0`) with the corpus
theorems supplied as axioms, so that what was checked was exactly the bridge.
Each target there depended on `propext`, `Classical.choice`, `Quot.sound` and
the corpus inputs only -- no `sorryAx`.
-/

namespace Erdos249257.FormalConjecturesAdapter

open Filter

/-! ## Summability facts for the two index conventions -/

/-- `∑ 1/(b^n - 1)` over all of `ℕ`; the `n = 0` term is `1/0 = 0`. -/
theorem summable_inv_pow_sub_one (b : ℕ) (hb : 2 ≤ b) :
    Summable (fun n : ℕ => (1 : ℝ) / ((b : ℝ) ^ n - 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hr : ‖(1 : ℝ) / (b : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one hbpos]; linarith
  have key : ∀ n : ℕ, 0 < n → (2 : ℝ) ≤ (b : ℝ) ^ n := fun n hn => by
    calc (2 : ℝ) = (b : ℝ) ^ 1 - ((b : ℝ) - 2) := by ring
      _ ≤ (b : ℝ) ^ n := by
          have : (b : ℝ) ^ 1 ≤ (b : ℝ) ^ n := pow_le_pow_right₀ (by linarith) hn
          linarith
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_geometric_of_norm_lt_one hr).mul_left 2)
  · rcases Nat.eq_zero_or_pos n with h | h
    · norm_num [h]
    · exact div_nonneg zero_le_one (by have := key n h; linarith)
  · rcases Nat.eq_zero_or_pos n with h | h
    · norm_num [h]
    · have hk := key n h
      have h1 : (0 : ℝ) < (b : ℝ) ^ n - 1 := by linarith
      have hbn : (0 : ℝ) < (b : ℝ) ^ n := by linarith
      rw [show (2 : ℝ) * ((1 : ℝ) / (b : ℝ)) ^ n = 2 / (b : ℝ) ^ n by
            rw [div_pow, one_pow]; ring,
        div_le_div_iff₀ h1 hbn]
      linarith

/-- `∑ τ(n)/b^n` over all of `ℕ`; the `n = 0` term is `0/1 = 0`. -/
theorem summable_divisor_count (b : ℕ) (hb : 2 ≤ b) :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) / (b : ℝ) ^ n) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hr : ‖(1 : ℝ) / (b : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one hbpos]; linarith
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_pow_mul_geometric_of_norm_lt_one 1 hr)
  have hτ : (n.divisors.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self n
  have hpow : ((1 : ℝ) / (b : ℝ)) ^ n = 1 / (b : ℝ) ^ n := by rw [div_pow, one_pow]
  rw [pow_one, hpow, mul_one_div]
  gcongr

/-! ## Upstream statement forms -/

/-- **Upstream `Erdos1049.erdos_1049.variants.geq_2_integer`.**  Integer base
`t ≥ 2`, `ℕ+`-indexed reciprocal form. -/
theorem erdos_1049_variants_geq_2_integer :
    ∀ t : ℤ, t ≥ 2 → Irrational (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) := by
  intro t ht
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = t := ⟨t.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hb2 : 2 ≤ b := by omega
  have hcast : ((b : ℕ) : ℝ) = (t : ℝ) := by rw [← hb]; push_cast; ring
  have hpnat := tsum_pnat_eq_tsum_succ
    (f := fun n : ℕ => (1 : ℝ) / ((b : ℝ) ^ n - 1))
  have hres : Irrational (∑' n : ℕ+, (1 : ℝ) / ((b : ℝ) ^ (n : ℕ) - 1)) := by
    rw [hpnat]; exact irrational_erdosSum_full_support b hb2
  rw [hcast] at hres
  exact hres

/-- **Upstream `Erdos258.erdos_258.variants.constant`.**  Natural base `t ≥ 2`,
divisor-count coefficients, `ℕ`-indexed with a `+1` shift.  Upstream states it
as `answer(True) ↔ ...`, which elaborates to `True ↔ ...`. -/
theorem erdos_258_variants_constant : True ↔ ∀ t ≥ (2 : ℕ),
    Irrational (∑' (n : ℕ), ((n + 1).divisors.card / t^(n + 1))) := by
  refine ⟨fun _ t ht => ?_, fun _ => trivial⟩
  have h := irrational_erdosSum_full_support t ht
  rw [erdosSum_full_support_eq_tsum_divisor_count t ht] at h
  convert h using 3

/-- **Upstream `Erdos257.erdos_257.variants.tsum_top`.**  Base 2, divisor-count
coefficients, `ℕ`-indexed from `0` (the `n = 0` term vanishes). -/
theorem erdos_257_variants_tsum_top :
    Irrational <| ∑' n, n.divisors.card / (2 ^ n : ℝ) := by
  have h := irrational_erdosSum_full_support 2 le_rfl
  rw [erdosSum_full_support_eq_tsum_divisor_count 2 le_rfl] at h
  have hsumm : Summable (fun n : ℕ => (n.divisors.card : ℝ) / ((2 : ℕ) : ℝ) ^ n) :=
    summable_divisor_count 2 le_rfl
  have hshift : (∑' n : ℕ, (n.divisors.card : ℝ) / ((2 : ℕ) : ℝ) ^ n)
      = ∑' k : ℕ, ((k + 1).divisors.card : ℝ) / ((2 : ℕ) : ℝ) ^ (k + 1) := by
    have := (Summable.sum_add_tsum_nat_add 1 hsumm).symm
    simpa [Finset.sum_range_one] using this
  have hres : Irrational (∑' n : ℕ, (n.divisors.card : ℝ) / ((2 : ℕ) : ℝ) ^ n) := by
    rw [hshift]; exact h
  norm_num at hres
  exact hres

end Erdos249257.FormalConjecturesAdapter
