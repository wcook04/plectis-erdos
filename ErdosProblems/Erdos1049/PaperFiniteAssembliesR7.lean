import ErdosProblems.Erdos1049.AdelicHeightBridge
import ErdosProblems.Erdos1049.BezoutPluckerJets
import ErdosProblems.Erdos1049.QuantitativeSelectorEscape
import ErdosProblems.Erdos1049.RationalPadeArithmetic

/-!
# R7: complete finite paper statements assembled from the live library

NOT compiler-checked in the return environment. No new axioms or admitted
proofs. These declarations collect all mathematical clauses of a displayed
result; they do not turn the unproved analytic statements into corollaries.

For directly matching single library declarations, theorem_coverage.json names
the originals instead of creating aliases. The genuinely additional pieces
here are the signed selector witness, the P-summand gap identity, and the
conjunctions needed to match multi-clause paper statements.
-/

namespace ErdosProblems.Erdos1049.PaperR7

open scoped BigOperators

/-- Long record, `res:powerbracket`. -/
theorem power_bracket :
    (2 : ℕ) ^ 64 < 3 ^ 41 ∧ 3 ^ 41 < 2 ^ 65 ∧
      (41 : ℝ) / 65 < Real.log 2 / Real.log 3 ∧
      Real.log 3 / Real.log 2 < (65 : ℝ) / 41 :=
  ⟨twoPow_sixtyFour_lt_threePow_fortyOne,
   threePow_fortyOne_lt_twoPow_sixtyFive,
   fortyOne_sixtyFive_lt_logTwo_div_logThree,
   logThree_div_logTwo_lt_sixtyFive_fortyOne⟩

/-- Long record, `res:sharpgaps`. The HP threshold is the actual live definition. -/
theorem height_and_hankel_deficits (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - (1 / 2 - 1 / Real.pi ^ 2) ∧
      (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma ∧
      (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 :=
  ⟨threeHalves_bv_height_gap_gt_threeThirteenths,
   threeHalves_rectangular_hp_gap_gt_threeThirteenths rho sigma hrho hsigma,
   threeHalves_hankelChargeThreshold_lt_eightFortyOne⟩

/-- Long record, `res:chargeceilings`, including both arbitrary-E consequences. -/
theorem charge_ceilings :
    (∀ N : ℤ, 0 < N →
      41 * (N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N : ℤ, 2 ≤ N →
      41 * (2 * N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 0 < N → E ≤ N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 2 ≤ N → E ≤ 2 * N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2)) :=
  ⟨zudilinScalarContent_ceiling_lt_required,
   zudilinScalarPlusBorder_ceiling_lt_required,
   zudilinScalarContent_cannot_meet_required_charge,
   zudilinScalarPlusBorder_cannot_meet_required_charge⟩

/-- Long record, `res:content`: all four algebraic assertions in one declaration. -/
theorem integer_scalar_content (S : ℝ) (cn cm Un Vn Um Vm : ℤ) :
    rationalPadeError S (cn * Un) (cn * Vn) =
      (cn : ℝ) * rationalPadeError S Un Vn ∧
    rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm) =
      cn * cm * rationalPadeExteriorDet Un Vn Um Vm ∧
    |rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm)| =
      |cn| * |cm| * |rationalPadeExteriorDet Un Vn Um Vm| ∧
    cn * cm ∣ rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm) := by
  refine ⟨rationalPadeError_mul S cn Un Vn,
    rationalPadeExteriorDet_mul_contents cn cm Un Vn Um Vm, ?_,
    contentProduct_dvd_rationalPadeExteriorDet cn cm Un Vn Um Vm⟩
  rw [rationalPadeExteriorDet_mul_contents]
  simp only [abs_mul]

/-- Long record, `res:endpoints`, including the stated unit-endpoint consequences. -/
theorem endpoint_residues (W : ℕ) (P : Polynomial ℤ) :
    (homEvalThreeTwo W P : ZMod 3) = (P.coeff 0 : ZMod 3) * 2 ^ W ∧
    (homEvalThreeTwo W P : ZMod 2) = (P.coeff W : ZMod 2) * 3 ^ W ∧
    ((P.coeff 0 = 1 ∨ P.coeff 0 = -1) →
      ¬ (3 : ℤ) ∣ homEvalThreeTwo W P) ∧
    ((P.coeff W = 1 ∨ P.coeff W = -1) →
      ¬ (2 : ℤ) ∣ homEvalThreeTwo W P) :=
  ⟨homEvalThreeTwo_mod_three W P, homEvalThreeTwo_mod_two W P,
   three_not_dvd_homEvalThreeTwo_of_const_unit W P,
   two_not_dvd_homEvalThreeTwo_of_top_unit W P⟩

/-- Difference of the two binary indicator vectors; this is not a polynomial pair. -/
def selectorDifference {ι : Type*} (s t : ι → Bool) : ι → ℤ :=
  fun i => (if s i then 1 else 0) - (if t i then 1 else 0)

theorem selectorDifference_values {ι : Type*} (s t : ι → Bool) (i : ι) :
    selectorDifference s t i = -1 ∨ selectorDifference s t i = 0 ∨
      selectorDifference s t i = 1 := by
  cases hs : s i <;> cases ht : t i <;> simp [selectorDifference, hs, ht]

theorem selectorDifference_ne_zero {ι : Type*} (s t : ι → Bool) (hst : s ≠ t) :
    selectorDifference s t ≠ 0 := by
  intro hz
  apply hst
  funext i
  have hi := congrFun hz i
  cases hs : s i <;> cases ht : t i <;> simp_all [selectorDifference]

/-- Subtract the two finite sums in an arbitrary additive commutative group. -/
theorem sum_selectorDifference {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (s t : ι → Bool) (w : ι → G) :
    (∑ i, selectorDifference s t i • w i) =
      (∑ i, if s i then w i else 0) - ∑ i, if t i then w i else 0 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : s i <;> cases ht : t i <;> simp [selectorDifference, hs, ht]

/-- The part of `res:jetkernel` not explicitly stated by the older library
interface: a nonzero signed coefficient vector, with every jet cancelled.
It deliberately does NOT assert a nonzero polynomial pair or real remainder. -/
theorem fourJet_signed_collision {M R S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ)
    (hcard : (3 ^ R) ^ 2 * (2 ^ S) ^ 2 < 2 ^ M) :
    ∃ s t : Fin M → Bool, s ≠ t ∧
      selectedFourJetSum R S W forms s = selectedFourJetSum R S W forms t ∧
      selectorDifference s t ≠ 0 ∧
      (∀ i, selectorDifference s t i = -1 ∨ selectorDifference s t i = 0 ∨
        selectorDifference s t i = 1) ∧
      (∑ i, selectorDifference s t i •
        fourJetSignature R S W (forms i).1 (forms i).2) = 0 := by
  obtain ⟨s, t, hst, heq⟩ := exists_distinct_binary_selectors_same_fourJet forms
    (by simpa only [fourJetSignature_card] using hcard)
  refine ⟨s, t, hst, heq, selectorDifference_ne_zero s t hst,
    selectorDifference_values s t, ?_⟩
  rw [sum_selectorDifference]
  change selectedFourJetSum R S W forms s - selectedFourJetSum R S W forms t = 0
  rw [heq, sub_self]

/-- The sufficient 4R+2S width, including its signed witness. -/
theorem fourJet_signed_collision_of_rank {M R S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ)
    (hR : 0 < R) (hM : 4 * R + 2 * S ≤ M) :
    ∃ c : Fin M → ℤ, c ≠ 0 ∧
      (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) ∧
      (∑ i, c i • fourJetSignature R S W (forms i).1 (forms i).2) = 0 := by
  obtain ⟨s, t, hst, heq⟩ :=
    exists_distinct_binary_selectors_same_fourJet_of_rank forms hR hM
  refine ⟨selectorDifference s t, selectorDifference_ne_zero s t hst,
    selectorDifference_values s t, ?_⟩
  rw [sum_selectorDifference]
  change selectedFourJetSum R S W forms s - selectedFourJetSum R S W forms t = 0
  rw [heq, sub_self]

/-- Long record, `res:rankfortyone`: both sufficiency and the T=1 lower count. -/
theorem rank_fortyone {M T S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ)
    (hT : 0 < T) (hM : 130 * T + 2 * S ≤ M) :
    (∃ s t : Fin M → Bool, s ≠ t ∧
      selectedFourJetSum (41 * T) S W forms s =
        selectedFourJetSum (41 * T) S W forms t) ∧
      2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) :=
  ⟨exists_distinct_binary_selectors_same_fourJet_of_rank_41 forms hT hM,
   fourJet_card_gt_two_pow_of_rank_41 S⟩

/-- Short and long records, `res:plucker-collapse`: the modular consequence
with pairwise minors and selector collision exposed together. The generic
commutative-ring clause is the existing
`BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero_of_isCoprime`. -/
theorem plucker_modular_tail {R S k : ℕ}
    (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R))
    (hu : ∀ n, IsCoprime (w n).1 (w n).2)
    (ha : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0)
    (hR : 0 < R) (hk : S + 2 * R ≤ k) :
    (∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0) ∧
      ∃ s t : Fin k → Bool, s ≠ t ∧
        (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  letI : NeZero (2 ^ S * 3 ^ R) := ⟨by positivity⟩
  exact ⟨BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero_of_isCoprime w hu ha,
    BezoutPluckerJets.zmod_binary_tail_collision_of_two_three_depth_of_isCoprime
      w hu ha hR hk⟩

/-- Long record, `res:scalar`, with the stronger positive-C0 branch. -/
theorem scalar_margin {C0 C1 : ℝ} (hC1 : 0 < C1)
    (hs : C0 ≤ 0 ∨ 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 < 0 ∧
      (0 < C0 → 2 * C0 ≤ C1 →
        C0 * Real.log 3 - C1 * Real.log 2 < -((17 : ℝ) / 41) * C0 * Real.log 2) :=
  ⟨three_two_scalar_margin_neg hC1 hs,
   fun h0 h2 => three_two_scalar_margin_lt_explicit h0 h2⟩

/-- Long record, `res:forcing`; both branches, without changing the coefficient index. -/
theorem forcing_term (B : ℕ) (c : ℕ → ℕ) (N : ℕ) :
    (∀ s : ℕ, 2 ≤ s → 1 ≤ B → 1 ≤ c (N + 1) →
      2 ^ (N + 1) ≤ rationalBaseForcingNat s B c N) ∧
      rationalBaseForcingNat 1 B c N = B * c (N + 1) :=
  ⟨fun _ hs hB hc => twoPow_le_rationalBaseForcingNat hs hB hc,
   rationalBaseForcingNat_one B c N⟩

/-- The exact P-gap in long-record `res:pade`; the library already had its sign. -/
theorem pade_P_gap (n k : ℤ) :
    rationalPadeDenExpTwice n - rationalPadePSummandDenExpTwice n k =
      (n - k) * (3 * n - k - 1) := by
  unfold rationalPadeDenExpTwice rationalPadePSummandDenExpTwice
  ring

/-- Long-record `res:pade`, all three items and the P-gap identity. -/
theorem pade_summand_bound_and_gap (n k m : ℤ) :
    (0 ≤ k → k ≤ n →
      rationalPadePSummandDenExpTwice n k ≤ rationalPadeDenExpTwice n) ∧
    rationalPadeDenExpTwice n - rationalPadePSummandDenExpTwice n k =
      (n - k) * (3 * n - k - 1) ∧
    rationalPadeDenExpTwice n - rationalPadeQMaxDenExpTwice n m =
      2 * (n + m * (m - 1)) ∧
    (0 ≤ n → 1 ≤ m →
      rationalPadeQMaxDenExpTwice n m ≤ rationalPadeDenExpTwice n) := by
  refine ⟨?_, pade_P_gap n k, rationalPadeQMaxDenExpTwice_gap n m, ?_⟩
  · intro hk hkn
    exact rationalPadePSummandDenExpTwice_le (hk.trans hkn) hk hkn
  · intro hn hm
    exact rationalPadeQMaxDenExpTwice_le hn hm

/-- Long record, `res:nomult`, reading scalar content as an actual common
factor of the displayed, endpoint-unit rows. Externally scaling the polynomials
can destroy the endpoint hypotheses; no assertion about that different input
is made here. The no-net-height-gain identity is `integer_scalar_content`. -/
theorem endpoint_scalar_content_exclusion (W : ℕ) (U V : Polynomial ℤ)
    (hU : U.coeff W = 1 ∨ U.coeff W = -1)
    (hV : V.coeff 0 = 1 ∨ V.coeff 0 = -1) :
    (∀ c U₀ V₀ : ℤ,
      homEvalThreeTwo W U = c * U₀ →
      homEvalThreeTwo W V = c * V₀ →
      ¬ (2 : ℤ) ∣ c ∧ ¬ (3 : ℤ) ∣ c) ∧
    (∀ c : ℤ, c ∣ homEvalThreeTwo W U → c ∣ homEvalThreeTwo W V →
      ¬ (2 : ℤ) ∣ c ∧ ¬ (3 : ℤ) ∣ c) := by
  constructor
  · intro c U₀ V₀ hleft hright
    exact commonMultiplier_not_two_not_three_of_endpoint_units c W U V hU hV
      ⟨U₀, hleft⟩ ⟨V₀, hright⟩
  · intro c hcU hcV
    exact commonMultiplier_not_two_not_three_of_endpoint_units c W U V hU hV hcU hcV

/-- One proposition containing every conclusion of the displayed jet theorem,
including its exact target cardinality and sufficient width. -/
def PaperJetWitness {M : ℕ} (R S W : ℕ)
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ) : Prop :=
  ∃ s t : Fin M → Bool, s ≠ t ∧
    selectedFourJetSum R S W forms s = selectedFourJetSum R S W forms t ∧
    selectorDifference s t ≠ 0 ∧
    (∀ i, selectorDifference s t i = -1 ∨ selectorDifference s t i = 0 ∨
      selectorDifference s t i = 1) ∧
    (∑ i, selectorDifference s t i •
      fourJetSignature R S W (forms i).1 (forms i).2) = 0

theorem fourJet_paper_statement {M R S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ) :
    Fintype.card (FourJetSignature R S) = (3 ^ R) ^ 2 * (2 ^ S) ^ 2 ∧
    (Fintype.card (FourJetSignature R S) < 2 ^ M → PaperJetWitness R S W forms) ∧
    (0 < R → 4 * R + 2 * S ≤ M → PaperJetWitness R S W forms) := by
  refine ⟨fourJetSignature_card R S, ?_, ?_⟩
  · intro hc
    exact fourJet_signed_collision forms (by simpa only [fourJetSignature_card] using hc)
  · intro hR hM
    obtain ⟨s, t, hst, heq⟩ :=
      exists_distinct_binary_selectors_same_fourJet_of_rank forms hR hM
    refine ⟨s, t, hst, heq, selectorDifference_ne_zero s t hst,
      selectorDifference_values s t, ?_⟩
    rw [sum_selectorDifference]
    change selectedFourJetSum R S W forms s - selectedFourJetSum R S W forms t = 0
    rw [heq, sub_self]

universe u

/-- One proposition for the complete ring-generic and finite-modulus
Bézout--Plücker theorem. Neither coordinate is assumed to be a unit. -/
theorem plucker_paper_statement :
    (∀ (R₀ : Type u) [CommRing R₀] (w : ℕ → R₀ × R₀),
      (∀ n, IsCoprime (w n).1 (w n).2) →
      (∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) →
      ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0) ∧
    (∀ (R S k : ℕ)
      (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R)),
      (∀ n, IsCoprime (w n).1 (w n).2) →
      (∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) →
      0 < R → S + 2 * R ≤ k →
      ∃ s t : Fin k → Bool, s ≠ t ∧
        (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0) := by
  constructor
  · intro R₀ _ w hu ha
    exact BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero_of_isCoprime w hu ha
  · intro R S k w hu ha hR hk
    exact (plucker_modular_tail w hu ha hR hk).2

end ErdosProblems.Erdos1049.PaperR7
