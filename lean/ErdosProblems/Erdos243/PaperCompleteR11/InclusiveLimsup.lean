import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveRecordAssembly
import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveBoundaryFinite
import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup

/-!
# Extended-real inclusive log-log endpoint


The limsup is taken in EReal, so an unbounded quotient is not silently
replaced by a real conditionally-complete-lattice default. The normaliser
is the paper's exact log_2(log_2(max(4,x))). All-index true running-maximum
increments are used, exactly as in the definition of Theta in the paper.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter PaperCompleteR7
open scoped Topology

/-- The true increment of a running maximum equals the truncated gap
above the previous maximum, even across a drawdown. -/
theorem runningMax_true_increment (U : ℕ → ℕ) (n : ℕ) :
    runningMax U (n + 1) - runningMax U n = U (n + 1) - runningMax U n := by
  change max (runningMax U n) (U (n + 1)) - runningMax U n = _
  by_cases h : U (n + 1) ≤ runningMax U n
  · rw [max_eq_left h, Nat.sub_self, Nat.sub_eq_zero_of_le h]
  · rw [max_eq_right (by omega : runningMax U n ≤ U (n + 1))]

/-- The paper's all-index record quotient, before passing to a limsup. -/
noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)

/-- The exact extended-real record coefficient Theta. -/
noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop

/-- A cofinally exceeded real coefficient is a lower bound on the
extended-real limsup; no boundedness hypothesis on the sequence is used. -/
theorem ereal_limsup_gt_one_of_cofinal (f : ℕ → ℝ)
    (h : ∃ c : ℝ, 1 < c ∧ ∀ T : ℕ, ∃ n, T ≤ n ∧ c < f n) :
    (1 : EReal) < limsup (fun n ↦ (f n : EReal)) atTop := by
  obtain ⟨c, hc, hcofinal⟩ := h
  have hf : ∃ᶠ n in atTop, (c : EReal) ≤ (f n : EReal) := by
    apply frequently_atTop.2
    intro T
    obtain ⟨n, hn, hcn⟩ := hcofinal T
    exact ⟨n, hn, EReal.coe_le_coe_iff.mpr hcn.le⟩
  have hcE : (1 : EReal) < (c : EReal) := by exact_mod_cast hc
  exact hcE.trans_le (le_limsup_of_frequently_le hf)

/-- Strict coefficient-one boundary in the paper's exact extended-real
record observable. -/
theorem canonical_recordTheta_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    (1 : EReal) < recordTheta (canonicalNaturalNumerator a p q) := by
  obtain ⟨c, hc, hcofinal⟩ := canonical_inclusive_record_boundary a ha hapos p q hq hs hgrowth hnot
  apply ereal_limsup_gt_one_of_cofinal
  refine ⟨c, hc, fun T ↦ ?_⟩
  obtain ⟨n, hn, hnew, hgap⟩ := hcofinal T
  refine ⟨n, hn, ?_⟩
  unfold recordLogLogCharge
  rw [runningMax_true_increment]
  have hden : 0 < recordLogLog (runningMax (canonicalNaturalNumerator a p q) n) :=
    lt_of_lt_of_le (by norm_num) (one_le_recordLogLog _)
  exact (lt_div_iff₀ hden).2 hgap

/-- The error observable in the inclusive corollary. The negative part is
formed in integers first, and then cast into the ordinary real quotient. -/
noncomputable def negativeErrorLogLogCharge (U : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  ((max (-E n) 0 : ℤ) : ℝ) / recordLogLog (U n)

/-- The global running maximum in the record denominator is larger than
the current numerator. Positivity of the exact normaliser makes the
error-to-record comparison valid, including arbitrary drawdowns. -/
theorem recordLogLogCharge_le_negativeError
    (U : ℕ → ℕ) (E : ℕ → ℤ)
    (hstep : ∀ n, (U (n + 1) : ℤ) = (U n : ℤ) - E n) (n : ℕ) :
    recordLogLogCharge U n ≤ negativeErrorLogLogCharge U E n := by
  have hgap : ((U (n + 1) - runningMax U n : ℕ) : ℝ) ≤ ((max (-E n) 0 : ℤ) : ℝ) := by
    exact_mod_cast record_increment_le_negative_part U E hstep n
  have hnum : (0 : ℝ) ≤ ((max (-E n) 0 : ℤ) : ℝ) := by
    exact_mod_cast (le_max_right (-E n) (0 : ℤ))
  have hCpos : 0 < recordLogLog (U n) :=
    lt_of_lt_of_le (by norm_num) (one_le_recordLogLog _)
  have hHpos : 0 < recordLogLog (runningMax U n) :=
    lt_of_lt_of_le (by norm_num) (one_le_recordLogLog _)
  have hden : recordLogLog (U n) ≤ recordLogLog (runningMax U n) :=
    recordLogLog_mono (by exact_mod_cast le_runningMax U (le_refl n))
  unfold recordLogLogCharge negativeErrorLogLogCharge
  rw [runningMax_true_increment]
  exact (div_le_div_of_nonneg_right hgap hHpos.le).trans
    (div_le_div_of_nonneg_left hnum hCpos hden)

/-- Comparison of the actual extended-real limsups, including +infinity. -/
theorem recordTheta_le_negativeError_limsup
    (U : ℕ → ℕ) (E : ℕ → ℤ)
    (hstep : ∀ n, (U (n + 1) : ℤ) = (U n : ℤ) - E n) :
    recordTheta U ≤ limsup (fun n ↦ (negativeErrorLogLogCharge U E n : EReal)) atTop := by
  exact limsup_le_limsup (Eventually.of_forall fun n ↦ EReal.coe_le_coe_iff.mpr
    (recordLogLogCharge_le_negativeError U E hstep n))

/-- Exact strict contrapositive of the printed inclusive log-log boundary. -/
theorem canonical_negativeError_limsup_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (1 : EReal) < limsup (fun n ↦ (negativeErrorLogLogCharge C E n : EReal)) atTop := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  have hC := (canonical_integer_tail a hapos p q hq hs).2.2.1
  have hstep : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n :=
    fun n ↦ natTail_eq_sub_centeredState a C D E hC (fun _ ↦ rfl) n
  exact (canonical_recordTheta_gt_one a ha hapos p q hq hs hgrowth hnot).trans_le
    (recordTheta_le_negativeError_limsup C E hstep)

/-- The inclusive inequality is ≤1, not <1. All the original analytic
hypotheses are retained; no conditional CRT or prime supplier is assumed. -/
theorem canonical_inclusive_logLog_criterion
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hlim : let C := canonicalNaturalNumerator a p q
      let D := canonicalDenominator a q
      let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
      limsup (fun n ↦ (negativeErrorLogLogCharge C E n : EReal)) atTop ≤ 1) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  by_contra hnot
  exact (not_lt_of_ge hlim) (canonical_negativeError_limsup_gt_one a ha hapos p q hq hs hgrowth hnot)

end ErdosProblems.Erdos243.PaperCompleteR11
