import ErdosProblems.Erdos243.NewtonV8.GeneralRateExtractionBridge
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Sharp growth from the retained regular-rate hypothesis

Status: verified locally by the focused Newton-classification build on
2026-09-09. No project axiom or placeholder is
introduced.

This module supplies the missing analytic input to
`GeneralRateExtractionBridge`: the exact little-o ratio hypothesis, with
`lambda > 1`, implies the sharp bound `C n = O(n^lambda)`.  The proof uses an
absolutely summable multiplicative error and Bernoulli's inequality.  It does
not weaken the exponent to `lambda + epsilon`.
-/

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace Erdos243V8

/-- The nonnegative finite product which absorbs the ratio error.  Including
the harmless index `0` makes the induction start at `n = 1` uniform. -/
def regularRateErrorProduct (C : ℕ → ℕ) (lam : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + |regularRateError C lam k|)

/-- The exact little-o error in `RegularRateHypothesis` is absolutely
summable.  This is where the strict inequality `1 < lambda` is used. -/
theorem summable_abs_regularRateError
    (C : ℕ → ℕ) (lam : ℝ)
    (hreg : Erdos243V6.RegularRateHypothesis C lam) :
    Summable (fun n : ℕ => |regularRateError C lam n|) := by
  obtain ⟨_hpos, hlam, herr⟩ := hreg
  change regularRateError C lam =o[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) (-lam)) at herr
  have hscale : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-lam)) := by
    exact Real.summable_nat_rpow.mpr (by linarith)
  have he : Summable (regularRateError C lam) :=
    summable_of_isBigO_nat hscale herr.isBigO
  simpa only [Real.norm_eq_abs] using he.norm

/-- Absolute summability gives one positive bound for all sufficiently long
finite error products. -/
theorem regularRateErrorProduct_eventually_bounded
    (C : ℕ → ℕ) (lam : ℝ)
    (hreg : Erdos243V6.RegularRateHypothesis C lam) :
    ∃ M > 0, ∀ᶠ n : ℕ in atTop, regularRateErrorProduct C lam n ≤ M := by
  have hsum := summable_abs_regularRateError C lam hreg
  have hmul : Multipliable (fun n : ℕ => 1 + |regularRateError C lam n|) :=
    Real.multipliable_one_add_of_summable hsum
  obtain ⟨M, hM, s, hs⟩ := hmul.eventually_bounded_finset_prod
  obtain ⟨N, hNs⟩ := Finset.exists_nat_subset_range s
  refine ⟨M, hM, eventually_atTop.2 ⟨N, fun n hn => ?_⟩⟩
  exact hs (Finset.range n) (hNs.trans (Finset.range_mono hn))

/-- Bernoulli's inequality turns the exact baseline ratio into a telescoping
`Real.rpow` comparison. -/
theorem regularRateBaseline_mul_rpow_le_succ
    (lam : ℝ) (hlam : 1 < lam) (n : ℕ) (hn : 1 ≤ n) :
    (1 + lam / (n : ℝ)) * Real.rpow (n : ℝ) lam ≤
      Real.rpow ((n + 1 : ℕ) : ℝ) lam := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hbern : 1 + lam * ((n : ℝ)⁻¹) ≤
      Real.rpow (1 + (n : ℝ)⁻¹) lam := by
    exact one_add_mul_self_le_rpow_one_add
      (le_trans (by norm_num) (inv_nonneg.mpr hnpos.le)) hlam.le
  have hbase : 1 + lam / (n : ℝ) ≤
      Real.rpow (1 + (n : ℝ)⁻¹) lam := by
    simpa [div_eq_mul_inv] using hbern
  calc
    (1 + lam / (n : ℝ)) * Real.rpow (n : ℝ) lam
        ≤ Real.rpow (1 + (n : ℝ)⁻¹) lam * Real.rpow (n : ℝ) lam :=
          mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hnpos.le lam)
    _ = Real.rpow ((n + 1 : ℕ) : ℝ) lam := by
      have hquot : 1 + (n : ℝ)⁻¹ = ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
        norm_num [Nat.cast_add]
        field_simp [hnpos.ne']
      rw [hquot]
      calc
        Real.rpow (((n + 1 : ℕ) : ℝ) / (n : ℝ)) lam *
            Real.rpow (n : ℝ) lam =
            Real.rpow ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ)) lam := by
              symm
              exact Real.mul_rpow (div_nonneg (by positivity) hnpos.le) hnpos.le
        _ = Real.rpow ((n + 1 : ℕ) : ℝ) lam := by
          congr 1
          field_simp [hnpos.ne']

/-- Pointwise sharp comparison with the finite error product. -/
theorem regularRate_le_rpow_mul_errorProduct
    (C : ℕ → ℕ) (lam : ℝ)
    (hreg : Erdos243V6.RegularRateHypothesis C lam) :
    ∀ n, 1 ≤ n →
      (C n : ℝ) ≤ (C 1 : ℝ) * Real.rpow (n : ℝ) lam *
        regularRateErrorProduct C lam n := by
  obtain ⟨hpos, hlam, _herr⟩ := hreg
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have hC1 : (0 : ℝ) ≤ C 1 := by positivity
      have hfactor : (1 : ℝ) ≤ 1 + |regularRateError C lam 0| := by
        linarith [abs_nonneg (regularRateError C lam 0)]
      simpa [regularRateErrorProduct] using
        (mul_le_mul_of_nonneg_left hfactor hC1)
  | succ n hn ih =>
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hCnpos : (0 : ℝ) < C n := by exact_mod_cast hpos n hn
      let e : ℝ := regularRateError C lam n
      let b : ℝ := 1 + lam / (n : ℝ)
      have hb : 1 ≤ b := by
        dsimp [b]
        have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam.le
        exact le_add_of_nonneg_right (div_nonneg hlam0 hnpos.le)
      have hdiv : (C (n + 1) : ℝ) / (C n : ℝ) = b + e := by
        dsimp [b, e, regularRateError]
        ring
      have hrec : (C (n + 1) : ℝ) = (C n : ℝ) * (b + e) := by
        rw [div_eq_iff hCnpos.ne'] at hdiv
        simpa [mul_comm] using hdiv
      have hratio : b + e ≤ b * (1 + |e|) := by
        have he : e ≤ |e| := le_abs_self e
        have habs : 0 ≤ |e| := abs_nonneg e
        nlinarith
      have hratio0 : 0 ≤ b + e := by
        rw [← hdiv]
        positivity
      have hprod0 : 0 ≤ regularRateErrorProduct C lam n := by
        apply Finset.prod_nonneg
        intro i hi
        positivity
      have hbase := regularRateBaseline_mul_rpow_le_succ lam hlam n hn
      calc
        (C (n + 1) : ℝ) = (C n : ℝ) * (b + e) := hrec
        _ ≤ ((C 1 : ℝ) * Real.rpow (n : ℝ) lam *
              regularRateErrorProduct C lam n) * (b * (1 + |e|)) := by
            exact mul_le_mul ih hratio hratio0
              (mul_nonneg (mul_nonneg (by positivity)
                (Real.rpow_nonneg hnpos.le lam)) hprod0)
        _ = (C 1 : ℝ) *
              (b * Real.rpow (n : ℝ) lam) *
              (regularRateErrorProduct C lam n * (1 + |e|)) := by ring
        _ ≤ (C 1 : ℝ) * Real.rpow ((n + 1 : ℕ) : ℝ) lam *
              (regularRateErrorProduct C lam n * (1 + |e|)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by simpa [b] using hbase) (by positivity))
              (mul_nonneg hprod0 (by positivity))
        _ = (C 1 : ℝ) * Real.rpow ((n + 1 : ℕ) : ℝ) lam *
              regularRateErrorProduct C lam (n + 1) := by
            simp [regularRateErrorProduct, Finset.prod_range_succ, e]

/-- The sharp growth supplier needed by `GeneralRateExtractionBridge`.  Its
exponent is exactly `lambda`; no `lambda + epsilon` loss occurs. -/
theorem regularRateHypothesis_isBigO_rpow
    (C : ℕ → ℕ) (lam : ℝ)
    (hreg : Erdos243V6.RegularRateHypothesis C lam) :
    (fun n : ℕ => (C n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) lam) := by
  obtain ⟨M, hM, hprod⟩ :=
    regularRateErrorProduct_eventually_bounded C lam hreg
  have hC1 : (0 : ℝ) < C 1 := by exact_mod_cast hreg.1 1 (by omega)
  apply IsBigO.of_bound ((C 1 : ℝ) * M)
  filter_upwards [hprod, eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hPn hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hP0 : 0 ≤ regularRateErrorProduct C lam n := by
    apply Finset.prod_nonneg
    intro i hi
    positivity
  have hpoint := regularRate_le_rpow_mul_errorProduct C lam hreg n hn
  have hbound : (C n : ℝ) ≤
      ((C 1 : ℝ) * M) * Real.rpow (n : ℝ) lam := by
    calc
      (C n : ℝ) ≤ (C 1 : ℝ) * Real.rpow (n : ℝ) lam *
          regularRateErrorProduct C lam n := hpoint
      _ ≤ (C 1 : ℝ) * Real.rpow (n : ℝ) lam * M := by
        exact mul_le_mul_of_nonneg_left hPn
          (mul_nonneg hC1.le (Real.rpow_nonneg hnpos.le lam))
      _ = ((C 1 : ℝ) * M) * Real.rpow (n : ℝ) lam := by ring
  simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ C n),
    abs_of_nonneg (Real.rpow_nonneg hnpos.le lam)] using hbound

/-- Immediate composition with the already adopted finite-difference bridge.
This closes the growth premise locally while leaving Newton interpolation and
the final rising-factorial classification as the retained C010 residual. -/
theorem general_rate_difference_eventually_zero
    (C : ℕ → ℕ) (lam : ℝ)
    (hreg : Erdos243V6.RegularRateHypothesis C lam)
    (j : ℕ) (hj : lam < j) :
    ∃ N, ∀ n, N ≤ n → fd j (fun m => (C m : ℤ)) n = 0 := by
  exact general_rate_difference_eventually_zero_of_growth C lam j hj hreg
    (regularRateHypothesis_isBigO_rpow C lam hreg)

end Erdos243V8
