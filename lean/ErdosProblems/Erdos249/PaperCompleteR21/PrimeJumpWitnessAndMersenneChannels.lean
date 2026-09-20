import Erdos249257.PrimeJumpWindow
import Erdos249257.MersenneShadowDenominatorGrowth
import Erdos249257.DiagonalPincerDecomposition
import Erdos249257.CertificateKernel

/-! Paper-form restatements of four long-paper environments of Erdős #249:

* the sharp four-vertex prime-jump criterion, its radius formula
  `B(H,p,L) = 3pH + (p+1)(L+2)`, and the exact `pH` saving over the
  two-cell radius `4pH + (p+1)(L+2)`;
* the explicit witness `H = H(4) = 12`, `p = 5`, `L = 15`, with the three
  displayed integers `W = 149906`, `W mod 32768 = 18834`, `B = 282`;
* the upper-half Mersenne channel bounds for `den(H_t β_{H_t})`;
* the rational-separation criterion for irrationality.

Here `H(t) = periodLcm t = lcmHeight t`, `J(H,p) = primeJumpTailCommutator H p`,
`W(H,p,L) = primeJumpWindowCommutator H p L` and
`B(H,p,L) = primeJumpSharpRadius H p L`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.PrimeJumpWindow
open Erdos249257.MersenneShadowDenominatorGrowth
open Erdos249257.MersenneShadowCyclotomicNoncollapse
open Erdos249257.DiagonalPincerDecomposition

/-! ### A certificate for a four-tail combination -/

/-- The sharp radius is `B(H,p,L) = 3pH + (p+1)(L+2)`. -/
theorem primeJumpSharpRadius_formula (H p L : ℕ) :
    primeJumpSharpRadius H p L = 3 * p * H + (p + 1) * (L + 2) := rfl

/-- **The sharp four-vertex criterion.**  For all `H, p, L ∈ ℕ`,
`B(H,p,L) < W(H,p,L) mod 2^L < 2^L - B(H,p,L)` implies `J(H,p) ∉ ℤ`. -/
theorem primeJumpTailCommutator_notMem_int_of_central_window (H p L : ℕ)
    (hleft : (primeJumpSharpRadius H p L) < primeJumpWindowCommutator H p L % 2 ^ L)
    (hright : primeJumpWindowCommutator H p L % 2 ^ L
      < 2 ^ L - primeJumpSharpRadius H p L) :
    primeJumpTailCommutator H p ∉ Set.range ((↑) : ℤ → ℝ) :=
  primeJumpTailCommutator_notMem_int_of_sharpKill ⟨hleft, hright⟩

/-- Compared with the `4pH + (p+1)(L+2)` radius obtained by treating the two
diagonal differences separately, the sharp radius saves exactly `pH`. -/
theorem primeJumpSharpRadius_saves_pH (H p L : ℕ) :
    (4 * p * H + (p + 1) * (L + 2) : ℤ) - primeJumpSharpRadius H p L = p * H := by
  unfold primeJumpSharpRadius
  push_cast
  ring

/-- The saving is a strict improvement exactly when `pH > 0`. -/
theorem primeJumpSharpRadius_lt_twoCellRadius {H p L : ℕ} (hpH : 0 < p * H) :
    primeJumpSharpRadius H p L < (4 * p * H + (p + 1) * (L + 2) : ℤ) := by
  have h : (0 : ℤ) < (p : ℤ) * H := by exact_mod_cast hpH
  have := primeJumpSharpRadius_saves_pH H p L
  push_cast at this ⊢
  linarith

/-! ### One explicit witness -/

/-- `H = H(4) = 12`. -/
theorem periodLcm_four_eq_twelve : periodLcm 4 = 12 := by decide

set_option maxRecDepth 100000 in
/-- **The explicit witness.**  For `H = 12`, `p = 5` and `L = 15`:
`W(12,5,15) = 149906`, `W(12,5,15) mod 32768 = 18834`, `B(12,5,15) = 282`,
so `282 < 18834 < 32486`. -/
theorem primeJump_witness_twelve_five_values :
    primeJumpWindowCommutator 12 5 15 = 149906 ∧
      primeJumpWindowCommutator 12 5 15 % 32768 = 18834 ∧
      primeJumpSharpRadius 12 5 15 = 282 ∧
      (282 : ℤ) < 18834 ∧ (18834 : ℤ) < 32486 := by
  refine ⟨by decide, by decide, by decide, by norm_num, by norm_num⟩

/-- `J(12,5) ∉ ℤ`. -/
theorem primeJumpTailCommutator_twelve_five_notMem_int :
    primeJumpTailCommutator 12 5 ∉ Set.range ((↑) : ℤ → ℝ) :=
  primeJumpTailCommutator_notMem_int_of_sharpKill primeJumpSharpKill_twelve_five

/-- The implication from a quantified family of sharp prime-jump kills. -/
theorem irrational_of_primeJumpSharp_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ,
      0 < p ∧ primeJumpSharpKill (periodLcm t) p L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_primeJumpSharpKill_supply hsupply

/-! ### Denominators of Möbius sums -/

/-- `H_t = lcm(1,…,t)` in both of the tree's spellings. -/
theorem lcmHeight_eq_periodLcm (t : ℕ) : lcmHeight t = periodLcm t :=
  (periodLcm_eq_lcmHeight t).symm

/-- `𝒫_t = {p prime : t/2 < p ≤ t}`. -/
theorem upperHalfPrimes_spec (t : ℕ) :
    upperHalfPrimes t = (Finset.Ioc (t / 2) t).filter Nat.Prime := rfl

/-- Bertrand's postulate makes `𝒫_t` nonempty for `t ≥ 2`. -/
theorem upperHalfPrimes_nonempty_paper {t : ℕ} (ht : 2 ≤ t) :
    (upperHalfPrimes t).Nonempty :=
  upperHalfPrimes_nonempty ht

/-- Its members satisfy `p - 1 ≥ ⌊t/2⌋` and `p ≤ t`. -/
theorem upperHalfPrimes_member_bounds {t p : ℕ} (hp : p ∈ upperHalfPrimes t) :
    t / 2 ≤ p - 1 ∧ p ≤ t := by
  have hb := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  exact ⟨by omega, hb.2⟩

/-- **The channel-product bounds.**  For every `t ≥ 5`,
`2^⌊t/2⌋ ≤ ∏_{p ∈ 𝒫_t} (2^p - 1) ≤ den(H_t β_{H_t})`. -/
theorem upperHalfMersenneProduct_between_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ ∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p ∧
      (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ≤
        ((lcmHeight t : ℚ) *
          RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den := by
  refine ⟨upperHalfMersenneProduct_lower_bound ht, ?_⟩
  exact Nat.le_of_dvd
    (Rat.pos ((lcmHeight t : ℚ) *
      RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)))
    (lcmHeight_upperHalf_product_dvd_den ht)

/-- **A single surviving channel.**  Some `p ∈ 𝒫_t` satisfies
`2^⌊t/2⌋ ≤ 2^p - 1 < 2^t` and `2^p - 1 ∣ den(H_t β_{H_t})`. -/
theorem exists_upperHalf_channel_paper {t : ℕ} (ht : 5 ≤ t) :
    ∃ p ∈ upperHalfPrimes t,
      2 ^ (t / 2) ≤ RadicalMobiusShadow.mersenne p ∧
      RadicalMobiusShadow.mersenne p < 2 ^ t ∧
      RadicalMobiusShadow.mersenne p ∣
        ((lcmHeight t : ℚ) *
          RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den :=
  exists_upperHalf_mersenne_channel_dvd_den_with_bounds ht

/-! ### The additional approximation hypothesis -/

/-- **The rational-separation criterion.**  A sequence of rationals `u_t` with
`u_t ≠ S` for all sufficiently large `t` and `den(u_t)|S - u_t| → 0` proves
`S ∉ ℚ`. -/
theorem irrational_totientSeries_of_rational_separation (u : ℕ → ℚ)
    (hne : ∀ᶠ t in Filter.atTop,
      ((u t : ℝ)) ≠ ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
    (h0 : Filter.Tendsto
      (fun t => ((u t).den : ℝ) *
        |(∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (u t : ℝ)|)
      Filter.atTop (nhds 0)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_of_den_mul_abs_sub_tendsto_zero hne h0

/-- The reason the criterion works: if `S = a/b` reduced, every unequal
rational `u` satisfies `den(u)·|S - u| ≥ 1/b`. -/
theorem den_mul_abs_sub_ge_one_div_den {q u : ℚ} (hqu : q ≠ u) :
    (1 : ℝ) / (q.den : ℝ) ≤ (u.den : ℝ) * |(q : ℝ) - (u : ℝ)| := by
  have hq : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hu : (0 : ℝ) < (u.den : ℝ) := by exact_mod_cast u.den_pos
  have hgap := one_div_den_mul_den_le_abs_sub hqu
  have hmul := mul_le_mul_of_nonneg_left hgap hu.le
  have hrw : (u.den : ℝ) * ((1 : ℝ) / ((q.den : ℝ) * (u.den : ℝ)))
      = (1 : ℝ) / (q.den : ℝ) := by
    field_simp
  linarith [hrw ▸ hmul]

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_formula
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.primeJumpTailCommutator_notMem_int_of_central_window
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_saves_pH
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_lt_twoCellRadius
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_four_eq_twelve
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.primeJump_witness_twelve_five_values
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.primeJumpTailCommutator_twelve_five_notMem_int
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_primeJumpSharp_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lcmHeight_eq_periodLcm
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_spec
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_nonempty_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_member_bounds
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.upperHalfMersenneProduct_between_bounds
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_upperHalf_channel_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_rational_separation
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.den_mul_abs_sub_ge_one_div_den
