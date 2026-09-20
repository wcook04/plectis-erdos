import ErdosProblems.Erdos1041.PaperAnalyticTargets

/-!
# Erdős 1041: a sufficient condition for a length-`2` path

The short paper's corollary `res:separation-parent`
(`paper/1041/erdos-1041-lemniscate-newton-flow.tex`, line 691):

> Let `f` be monic of degree `n ≥ 3` with all roots in the open unit disc, and
> let `c` be a simple critical point with `v = f(c)` and `0 < |v| < 1`.  If some
> real centre `w₀ ∈ [0,1]` admits a radius `S ≥ 4/3` such that
> `|f(d)/v - w₀| ≥ S` for every other critical point `d`, then Erdős
> Problem #1041 holds for `f`.

"Erdős Problem #1041 holds for `f`" is the tree's own predicate
`PaperAnalyticTargets.HasDistinctConnection f 1 2`: two distinct roots of `f`
joined inside `{|f| < 1}` by a continuous rectifiable curve of extended
variation strictly below `2`.

The corollary's own argument — shrink `S` to `4/3`, feed the disc-family
length estimate, and check the numerical threshold — is proved here in full.
Its analytic input is the paper's Theorem `res:critical-value-separation`
(line 665), whose proof uses Pólya's area–capacity inequality, the EKS
component count and the Bergman segment inequality; none of these is in
Mathlib or in this tree.  That theorem therefore appears as ONE explicit,
named, faithfully stated hypothesis `CriticalValueSeparationTheorem`, so this
row is `covered_modulo_external`.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Set

namespace SeparationParent

/-- The paper's normalised critical-value separation at a real centre `w₀`:
every OTHER critical point `d` satisfies `|f(d)/f(c) - w₀| ≥ S`.  For `w₀ = 1`
this is `ConnectorR18.ValueSeparatedAt`. -/
def ValueSeparatedAtCentre (f : ℂ[X]) (c : ℂ) (w₀ S : ℝ) : Prop :=
  ∀ d : ℂ, f.derivative.eval d = 0 → d ≠ c → S ≤ ‖f.eval d / f.eval c - (w₀ : ℂ)‖

/-- The right side of the paper's displayed bound `eq:disk-family-length`,
without the `2|v|^{2/n}` prefactor:
`(S/(n-1))^{2/n} log((S² + S + p)/(S² - S + p))`. -/
def separationCoefficient (n : ℕ) (S p : ℝ) : ℝ :=
  (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
    Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))

/-- **The external analytic input**: the paper's Theorem
`res:critical-value-separation` (separation of one simple critical value).
`f` monic of degree `n ≥ 3`, `c` a simple critical point with `v = f(c) ≠ 0`,
`w₀ ∈ [0,1]`, `S > max(w₀, 1-w₀)`, and every other critical point `d` obeying
`|f(d)/v - w₀| ≥ S`; then two distinct roots are joined inside `{|f| ≤ |v|}`
by a curve `Γ` with
`length(Γ)² ≤ 2|v|^{2/n}(S/(n-1))^{2/n} log((S²+S+p)/(S²-S+p))`, `p = w₀(1-w₀)`. -/
def CriticalValueSeparationTheorem : Prop :=
  ∀ (f : ℂ[X]) (c : ℂ) (w₀ S : ℝ), f.Monic → 3 ≤ f.natDegree →
    f.derivative.eval c = 0 → f.derivative.derivative.eval c ≠ 0 →
    f.eval c ≠ 0 → 0 ≤ w₀ → w₀ ≤ 1 → max w₀ (1 - w₀) < S →
    ValueSeparatedAtCentre f c w₀ S →
    ∃ a b : ℂ, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      PaperAnalyticTargets.ConnectedAtMost f.eval ‖f.eval c‖
        (Real.sqrt (2 * ‖f.eval c‖ ^ ((2 : ℝ) / (f.natDegree : ℝ)) *
          separationCoefficient f.natDegree S (w₀ * (1 - w₀)))) a b

/-! ## The numerical threshold at radius `4/3` -/

private theorem seven_lt_exp_two : (7 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith [h, Real.exp_pos 1]

private theorem log_seven_lt_two : Real.log 7 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  exact seven_lt_exp_two

/-- The logarithmic ratio at `S = 4/3` is at most `7` for every `p ≥ 0`. -/
theorem ratio_le_seven {p : ℝ} (hp : 0 ≤ p) :
    ((4 / 3 : ℝ) ^ 2 + 4 / 3 + p) / ((4 / 3 : ℝ) ^ 2 - 4 / 3 + p) ≤ 7 := by
  have hden : (0 : ℝ) < (4 / 3 : ℝ) ^ 2 - 4 / 3 + p := by nlinarith
  rw [div_le_iff₀ hden]
  nlinarith

theorem ratio_ge_one {p : ℝ} (hp : 0 ≤ p) :
    (1 : ℝ) ≤ ((4 / 3 : ℝ) ^ 2 + 4 / 3 + p) / ((4 / 3 : ℝ) ^ 2 - 4 / 3 + p) := by
  have hden : (0 : ℝ) < (4 / 3 : ℝ) ^ 2 - 4 / 3 + p := by nlinarith
  rw [le_div_iff₀ hden]
  nlinarith

/-- **The corollary's numerical threshold.**
`separationCoefficient n (4/3) p < 2` for every degree `n ≥ 3` and `p ≥ 0`. -/
theorem separationCoefficient_lt_two {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : 0 ≤ p) :
    separationCoefficient n (4 / 3) p < 2 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hbase0 : (0 : ℝ) < (4 / 3 : ℝ) / ((n : ℝ) - 1) := by positivity
  have hbase1 : (4 / 3 : ℝ) / ((n : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hn1]; linarith
  have hexp : (0 : ℝ) ≤ (2 : ℝ) / (n : ℝ) := by positivity
  have hr0 : 0 < ((4 / 3 : ℝ) / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) :=
    Real.rpow_pos_of_pos hbase0 _
  have hr1 : ((4 / 3 : ℝ) / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) ≤ 1 :=
    Real.rpow_le_one hbase0.le hbase1 hexp
  have hden : (0 : ℝ) < (4 / 3 : ℝ) ^ 2 - 4 / 3 + p := by nlinarith
  have hratio_pos : (0 : ℝ) <
      ((4 / 3 : ℝ) ^ 2 + 4 / 3 + p) / ((4 / 3 : ℝ) ^ 2 - 4 / 3 + p) := by positivity
  have hlog0 : 0 ≤ Real.log
      (((4 / 3 : ℝ) ^ 2 + 4 / 3 + p) / ((4 / 3 : ℝ) ^ 2 - 4 / 3 + p)) :=
    Real.log_nonneg (ratio_ge_one hp)
  have hlog7 : Real.log
      (((4 / 3 : ℝ) ^ 2 + 4 / 3 + p) / ((4 / 3 : ℝ) ^ 2 - 4 / 3 + p)) ≤ Real.log 7 :=
    (Real.log_le_log_iff hratio_pos (by norm_num)).mpr (ratio_le_seven hp)
  unfold separationCoefficient
  nlinarith [log_seven_lt_two]

/-- The whole squared bound at `S = 4/3` stays below `4` once `|v| < 1`. -/
theorem squared_bound_lt_four {n : ℕ} (hn : 3 ≤ n) {v p : ℝ} (hv0 : 0 < v) (hv1 : v < 1)
    (hp : 0 ≤ p) :
    2 * v ^ ((2 : ℝ) / (n : ℝ)) * separationCoefficient n (4 / 3) p < 4 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp : (0 : ℝ) < (2 : ℝ) / (n : ℝ) := by positivity
  have hvp : v ^ ((2 : ℝ) / (n : ℝ)) < 1 := Real.rpow_lt_one hv0.le hv1 hexp
  have hvp0 : 0 < v ^ ((2 : ℝ) / (n : ℝ)) := Real.rpow_pos_of_pos hv0 _
  have hcoef := separationCoefficient_lt_two hn hp
  have hcoef0 : 0 ≤ separationCoefficient n (4 / 3) p := by
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hbase0 : (0 : ℝ) < (4 / 3 : ℝ) / ((n : ℝ) - 1) := by positivity
    have hden : (0 : ℝ) < (4 / 3 : ℝ) ^ 2 - 4 / 3 + p := by nlinarith
    have hratio_pos : (0 : ℝ) <
        ((4 / 3 : ℝ) ^ 2 + 4 / 3 + p) / ((4 / 3 : ℝ) ^ 2 - 4 / 3 + p) := by positivity
    have := Real.log_nonneg (ratio_ge_one hp)
    unfold separationCoefficient
    positivity
  nlinarith

/-! ## Transport from the closed sublevel connector to the open one -/

theorem connectedBelow_of_connectedAtMost {f : ℂ → ℂ} {R L R' L' : ℝ} {a b : ℂ}
    (h : PaperAnalyticTargets.ConnectedAtMost f R L a b) (hR : R < R') (hL : L < L')
    (hL0 : 0 ≤ L) : PaperCurve.ConnectedBelow f R' L' a b := by
  obtain ⟨γ, hc, h0, h2, hmem, hbv, hvar⟩ := h
  refine ⟨γ, hc, h0, h2, fun t ht => lt_of_le_of_lt (hmem t ht) hR, hbv, ?_⟩
  refine lt_of_le_of_lt hvar ?_
  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
  exact hL

/-! ## The corollary -/

/-- **`res:separation-parent`, modulo the named external separation theorem.**

`f` monic of degree `n ≥ 3` with all roots in the open unit disc, `c` a simple
critical point with `0 < |f(c)| < 1`, and a real centre `w₀ ∈ [0,1]` admitting
a radius `S ≥ 4/3` with `|f(d)/f(c) - w₀| ≥ S` at every other critical point.
Then Erdős Problem #1041 holds for `f`: two distinct roots of `f` are joined
inside `{|f| < 1}` by a rectifiable curve of length strictly below `2`. -/
theorem separation_parent (hSep : CriticalValueSeparationTheorem)
    {f : ℂ[X]} {c : ℂ} {w₀ S : ℝ}
    (hmonic : f.Monic) (hdeg : 3 ≤ f.natDegree)
    (hroots : PaperAnalyticTargets.RootsInOpenUnitDisc f)
    (hcrit : f.derivative.eval c = 0) (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv0 : f.eval c ≠ 0) (hv1 : ‖f.eval c‖ < 1)
    (hw0 : 0 ≤ w₀) (hw1 : w₀ ≤ 1) (hS : 4 / 3 ≤ S)
    (hsep : ValueSeparatedAtCentre f c w₀ S) :
    PaperAnalyticTargets.HasDistinctConnection f 1 2 := by
  -- shrinking the disc preserves the exclusion of the other critical values
  have hsep43 : ValueSeparatedAtCentre f c w₀ (4 / 3) := fun d hd hdc =>
    le_trans hS (hsep d hd hdc)
  have hmax : max w₀ (1 - w₀) < 4 / 3 := max_lt (by linarith) (by linarith)
  obtain ⟨a, b, hab, ha, hb, hconn⟩ :=
    hSep f c w₀ (4 / 3) hmonic hdeg hcrit hsimple hv0 hw0 hw1 hmax hsep43
  -- the squared length bound is strictly below `4`
  have hp : 0 ≤ w₀ * (1 - w₀) := mul_nonneg hw0 (by linarith)
  have hvpos : 0 < ‖f.eval c‖ := norm_pos_iff.mpr hv0
  have hbound := squared_bound_lt_four (n := f.natDegree) hdeg hvpos hv1 hp
  have hsqrt_lt : Real.sqrt (2 * ‖f.eval c‖ ^ ((2 : ℝ) / (f.natDegree : ℝ)) *
      separationCoefficient f.natDegree (4 / 3) (w₀ * (1 - w₀))) < 2 := by
    have h4 : Real.sqrt (2 * ‖f.eval c‖ ^ ((2 : ℝ) / (f.natDegree : ℝ)) *
        separationCoefficient f.natDegree (4 / 3) (w₀ * (1 - w₀)))
        < Real.sqrt 4 := by
      apply Real.sqrt_lt_sqrt _ hbound
      · -- the squared bound is nonnegative
        have hcoef0 : 0 ≤ separationCoefficient f.natDegree (4 / 3) (w₀ * (1 - w₀)) := by
          have hnR : (3 : ℝ) ≤ (f.natDegree : ℝ) := by exact_mod_cast hdeg
          have hn1 : (0 : ℝ) < (f.natDegree : ℝ) - 1 := by linarith
          have hbase0 : (0 : ℝ) < (4 / 3 : ℝ) / ((f.natDegree : ℝ) - 1) := by positivity
          have hden : (0 : ℝ) < (4 / 3 : ℝ) ^ 2 - 4 / 3 + w₀ * (1 - w₀) := by nlinarith
          have hratio_pos : (0 : ℝ) <
              ((4 / 3 : ℝ) ^ 2 + 4 / 3 + w₀ * (1 - w₀)) /
                ((4 / 3 : ℝ) ^ 2 - 4 / 3 + w₀ * (1 - w₀)) := by positivity
          have := Real.log_nonneg (ratio_ge_one hp)
          unfold separationCoefficient
          positivity
        have hvp0 : 0 < ‖f.eval c‖ ^ ((2 : ℝ) / (f.natDegree : ℝ)) :=
          Real.rpow_pos_of_pos hvpos _
        positivity
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rwa [hsqrt4] at h4
  refine ⟨a, b, hab, ha, hb, ?_⟩
  exact connectedBelow_of_connectedAtMost hconn hv1 hsqrt_lt (Real.sqrt_nonneg _)

end SeparationParent

#print axioms SeparationParent.separationCoefficient_lt_two
#print axioms SeparationParent.squared_bound_lt_four
#print axioms SeparationParent.connectedBelow_of_connectedAtMost
#print axioms SeparationParent.separation_parent

end ErdosProblems.Erdos1041.PaperCompleteR21
