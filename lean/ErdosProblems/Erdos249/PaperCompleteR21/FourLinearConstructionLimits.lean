import Erdos249257.TotientMahlerDefect
import Erdos249257.TotientTailCarryPeriod
import Erdos249257.IncidenceQuotientHermitePade
import Erdos249257.LcmFactorIdealPulseObstruction
import Erdos249257.CertificateKernel
import ErdosProblems.Erdos249.RankOneSubrankObstruction

/-! Paper-form restatement of `prop:b6` of the long #249 manuscript, "Four
limits of particular linear constructions", together with the trailing
rank-one quotient bound of the same environment.

The environment asserts five things.

(i) *Dyadic sections and an integer identity.*  The retained family of
`2^e+1` dyadic sections is linearly independent over `ℚ` for `e ≥ 1`;
separately, positive integers `Q, v` and integers `A, b` cannot satisfy
`A ≠ 0`, `Q v A = b`, `|b| < Q v`.

(ii) *Möbius incidence.*  `U_N(i,j) = μ((i+1)/(j+1))` when `(j+1) ∣ (i+1)` and
`0` otherwise is lower triangular with unit diagonal, so `det U_N = 1` for
every `N`; hence multiplication by `U_N` is injective and the corresponding
coefficient transformation has no nonzero vector in its kernel.

(iii) *Adjugate reconstruction.*  For finite families `w i ∈ ℚ`, `x i ∈ ℕ`
with `∑ w i φ(x i) = 1`, the two-tail error bound `∑ |w i| (3 x i + 4)` is at
least `3`, via `1 ≤ ∑ |w i| φ(x i) ≤ ∑ |w i| x i`; consequently it cannot be
less than `1`, whatever the size of the evaluation matrix.

(iv) *Finite combinations of shifts.*  The synthetic sequence of
Observation `prop:B4b-kill` has the prescribed differences
`a_{(q-1)H-1} = φ(H)` for `2 ≤ q < t`, where `H = lcm(1,…,t)`; it is of the
form `a i = 2 c i - c (i+1)`; every finite integer combination of its shifts
has the same form with a correspondingly shifted state; and the uniform
bounds depend on the absolute coefficient sum `∑ |λ j|`.

(v) The trailing quotient bound: for `e ≥ 1` and `Y ≥ 4`,
`t(Y,e+2)^2 / t(Y,2e+2) - (S - 1/2) > 1/480`, where
`t(Y,r) = ∑_{d=1}^{Y} μ(d)/(2^d-1)^r`, proved by bounding each infinite sum
`∑_{d≥1} μ(d)/(2^d-1)^r` for `r ≥ 3` between `1429/1512` and `1` and its
truncation error after `Y ≥ 4` terms by `1/3584`.

Item (iv) is the one the paper records as "not replayed here"; its synthetic
sequence is the LCM anchor pulse of `LcmFactorIdealPulseObstruction`, whose
state is `-φ(periodLcm t)` exactly on the anchor set
`{(q-1)·periodLcm t : 2 ≤ q < t}` and zero elsewhere, and `periodLcm t` is
`lcm(1,…,t)` by definition.

Sentences of the environment left out because they are not propositions: the
opening caution that the four constructions must not be read as a claim that
every finite family of totient sections is independent, the three scope
remarks attached to items (i), (ii) and (iv) ("does not exclude every argument
using an adjugate matrix", "not just a finite list of computed examples" is
covered by the universally quantified statement, "does not assert that `a i`
equals the actual totient difference at other indices"), the status note that
item (iv) "has not been replayed here", and the closing remarks about
`prop:period-not-rank` and the separate `5/4` comparison, which are claims
about other environments. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.SignedQMomentObstruction
open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.RankOneSubrankObstruction

/-! ### (i) Dyadic sections and an integer identity -/

/-- **(i), first half.**  The retained canonical dyadic family at level `e`
has exactly `2^e + 1` indexed sections and they are linearly independent over
`ℚ`.  Stated for every `e`; `prop:b6` uses it for `e ≥ 1`. -/
theorem b6_retained_dyadic_sections_independent (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1
      ∧ LinearIndependent ℚ (canonicalTotientKernelFamily e) :=
  ⟨card_totientCanonicalIndex e, linearIndependent_canonicalTotientKernelFamily e⟩

/-- **(i), second half.**  Positive integers `Q, v` and integers `A, b` cannot
satisfy `A ≠ 0`, `Q v A = b` and `|b| < Q v`: from `|A| ≥ 1` the identity
forces `|b| ≥ Q v`. -/
theorem b6_compressed_adjoint_identity_impossible
    {Q v : ℕ} (hQ : 0 < Q) (hv : 0 < v) {A b : ℤ}
    (hA : A ≠ 0) (hid : (Q : ℤ) * (v : ℤ) * A = b) :
    ¬ |b| < (Q : ℤ) * (v : ℤ) := by
  intro hsmall
  exact false_of_compressedAdjointCertificate (v := v)
    { Q := Q
      A := A
      boundary := b
      v_pos := hv
      Q_pos := hQ
      A_ne_zero := hA
      identity := hid
      boundary_small := hsmall }

/-! ### (ii) Möbius incidence -/

/-- **(ii).**  The Möbius incidence matrix `U_N(i,j) = μ((i+1)/(j+1))` for
`(j+1) ∣ (i+1)` and `0` otherwise is lower triangular with unit diagonal, has
determinant `1` at every horizon `N`, acts injectively, and has only the zero
vector in its kernel. -/
theorem b6_mobius_incidence_unimodular_and_injective (N : ℕ) :
    (∀ i j : Fin N,
        IncidenceQuotientHermitePade.incidenceMobiusMatrix N i j =
          if (j : ℕ) + 1 ∣ (i : ℕ) + 1 then
            ArithmeticFunction.moebius (((i : ℕ) + 1) / ((j : ℕ) + 1)) else 0)
      ∧ (IncidenceQuotientHermitePade.incidenceMobiusMatrix N).BlockTriangular
          OrderDual.toDual
      ∧ (∀ i : Fin N,
          IncidenceQuotientHermitePade.incidenceMobiusMatrix N i i = 1)
      ∧ Matrix.det (IncidenceQuotientHermitePade.incidenceMobiusMatrix N) = 1
      ∧ Function.Injective
          (IncidenceQuotientHermitePade.incidenceMobiusMatrix N).mulVec
      ∧ ∀ c : Fin N → ℤ,
          (IncidenceQuotientHermitePade.incidenceMobiusMatrix N).mulVec c = 0
            ↔ c = 0 :=
  ⟨fun i j => IncidenceQuotientHermitePade.incidenceMobiusMatrix_apply N i j,
   IncidenceQuotientHermitePade.incidenceMobiusMatrix_lowerTriangular N,
   fun i => IncidenceQuotientHermitePade.incidenceMobiusMatrix_diagonal N i,
   IncidenceQuotientHermitePade.incidenceMobius_det_eq_one N,
   IncidenceQuotientHermitePade.mobiusCompanionJetMap_injective N,
   fun c => IncidenceQuotientHermitePade.mobiusCompanionJetMap_eq_zero_iff N c⟩

/-! ### (iii) Adjugate reconstruction -/

/-- **(iii).**  For a finite rational row isolating one totient channel, the
displayed chain `1 ≤ ∑ |w i| φ(x i) ≤ ∑ |w i| x i` holds, the two-tail cost is
literally `∑ |w i| (3 x i + 4)`, it is at least `3`, and therefore it is never
below `1`, at any evaluation-matrix height. -/
theorem b6_adjugate_tail_cost_floor
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ)
    (hisolate : ∑ i, w i * (Nat.totient (x i) : ℚ) = 1) :
    (1 : ℚ) ≤ ∑ i, |w i| * (Nat.totient (x i) : ℚ)
      ∧ (∑ i, |w i| * (Nat.totient (x i) : ℚ)) ≤ ∑ i, |w i| * (x i : ℚ)
      ∧ totientAdjugateTailCost w x = ∑ i, |w i| * (3 * (x i : ℚ) + 4)
      ∧ (3 : ℚ) ≤ totientAdjugateTailCost w x
      ∧ ¬ totientAdjugateTailCost w x < 1 := by
  classical
  refine ⟨?_, ?_, ?_, three_le_totientAdjugateTailCost w x hisolate,
    not_totientAdjugateTailCost_lt_one w x hisolate⟩
  · calc
      (1 : ℚ) = |∑ i, w i * (Nat.totient (x i) : ℚ)| := by
        rw [hisolate, abs_one]
      _ ≤ ∑ i, |w i * (Nat.totient (x i) : ℚ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |w i| * (Nat.totient (x i) : ℚ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        have hphi : (0 : ℚ) ≤ (Nat.totient (x i) : ℚ) := by positivity
        rw [abs_mul, abs_of_nonneg hphi]
  · refine Finset.sum_le_sum ?_
    intro i _
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (w i))
    exact_mod_cast Nat.totient_le (x i)
  · unfold totientAdjugateTailCost
    refine Finset.sum_congr rfl ?_
    intro i _
    ring

/-! ### (iv) Finite combinations of shifts -/

/-- **(iv), the construction.**  With `H = periodLcm t = lcm(1,…,t)` and
`A = φ(H)`, the synthetic state of Observation `prop:B4b-kill` is `-A` exactly
on the anchor set `{(q-1)H : 2 ≤ q < t}` and `0` elsewhere, its letter is the
dyadic coboundary `a i = 2 c i - c (i+1)`, and the letter entering each anchor
is `A = φ((q+1)H) - φ(qH)`. -/
theorem b6_synthetic_sequence_prescribed_differences {t : ℕ} (ht : 3 ≤ t) :
    (∀ k : ℕ, k ∈ lcmAnchorStates t →
        lcmAnchorPulseState t k = -(Nat.totient (periodLcm t) : ℤ))
      ∧ (∀ k : ℕ, k ∉ lcmAnchorStates t → lcmAnchorPulseState t k = 0)
      ∧ (∀ q : ℕ, 2 ≤ q → q < t →
          (q - 1) * periodLcm t ∈ lcmAnchorStates t)
      ∧ (∀ i : ℕ, lcmAnchorPulseLetter t i =
          2 * lcmAnchorPulseState t i - lcmAnchorPulseState t (i + 1))
      ∧ ∀ q : ℕ, 2 ≤ q → q < t →
          lcmAnchorPulseLetter t ((q - 1) * periodLcm t - 1)
              = (Nat.totient (periodLcm t) : ℤ)
            ∧ lcmAnchorPulseLetter t ((q - 1) * periodLcm t - 1)
              = deltaTotient (periodLcm t) (q * periodLcm t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp [lcmAnchorPulseState, sparsePulseState, hk]
  · intro k hk
    simp [lcmAnchorPulseState, sparsePulseState, hk]
  · intro q hq2 hqt
    exact lcmAnchorStates_mem hq2 hqt
  · intro i
    exact congrFun (lcmAnchorPulseLetter_eq_dyadicCoboundary t) i
  · intro q hq2 hqt
    exact ⟨lcmAnchorPulse_letter_at_anchor ht hq2 hqt,
      lcmAnchorPulse_letter_eq_deltaTotient ht hq2 hqt⟩

/-- **(iv), closure under finite shift combinations.**  For every finitely
supported integer weight list `terms`, the transformed state
`d = ∑ λ j c(· + h j)` and word `b = ∑ λ j a(· + h j)` again satisfy
`b i = 2 d i - d (i+1)`, the telescoped prefix identity
`∑_{r<L} 2^{L-1-r} b_{i+r} = 2^L d i - d (i+L)`, and the uniform bounds
`|d i| ≤ A ∑ |λ j|`, `|b i| ≤ 2A ∑ |λ j|` with `A = φ(periodLcm t)`.  The
bounds are uniform in `i`, not in the weights: the factor `∑ |λ j|` is
present. -/
theorem b6_synthetic_shift_combinations_same_form
    (t : ℕ) (terms : List (ℕ × ℤ)) :
    (∀ i : ℕ,
        lcmAnchorShiftPolynomialState t terms i =
          shiftLinearCombination terms (lcmAnchorPulseState t) i)
      ∧ (∀ i : ℕ,
          lcmAnchorShiftPolynomialLetter t terms i =
            shiftLinearCombination terms (lcmAnchorPulseLetter t) i)
      ∧ (∀ i : ℕ,
          lcmAnchorShiftPolynomialLetter t terms i =
            2 * lcmAnchorShiftPolynomialState t terms i -
              lcmAnchorShiftPolynomialState t terms (i + 1))
      ∧ (∀ n L : ℕ,
          dyadicClearedPrefix (lcmAnchorShiftPolynomialLetter t terms) n L =
            (2 : ℤ) ^ L * lcmAnchorShiftPolynomialState t terms n -
              lcmAnchorShiftPolynomialState t terms (n + L))
      ∧ (∀ i : ℕ, |lcmAnchorShiftPolynomialState t terms i| ≤
          shiftLinearWeight terms * (Nat.totient (periodLcm t) : ℤ))
      ∧ (∀ i : ℕ, |lcmAnchorShiftPolynomialLetter t terms i| ≤
          shiftLinearWeight terms * (2 * (Nat.totient (periodLcm t) : ℤ))) := by
  have hA : |(Nat.totient (periodLcm t) : ℤ)| = (Nat.totient (periodLcm t) : ℤ) :=
    abs_of_nonneg (by positivity)
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, lcmAnchorShiftPolynomial_clearedPrefix t terms,
    ?_, ?_⟩
  · intro i
    exact congrFun (lcmAnchorShiftPolynomialLetter_eq_dyadicCoboundary t terms) i
  · intro i
    have h := lcmAnchorShiftPolynomial_state_bound t terms i
    rwa [hA] at h
  · intro i
    have h := lcmAnchorShiftPolynomial_letter_bound t terms i
    rwa [hA] at h

/-! ### The trailing rank-one quotient bound -/

/-- The finite Möbius--Mersenne rung in the paper's index range:
`t(Y,r) = ∑_{d=1}^{Y} μ(d)/(2^d-1)^r`. -/
theorem b6_mobiusMersennePrefix_eq_icc_sum (Y r : ℕ) :
    mobiusMersennePrefix Y r =
      ∑ d ∈ Finset.Icc 1 Y,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ r := by
  have hIcc : Finset.Icc 1 Y = Finset.Ico 1 (Y + 1) := by
    ext d
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Nat.add_comm 1 i]
  rfl

/-- The two estimates the trailing bound's proof uses: every infinite rung
`Θ_r` with `r ≥ 3` lies between `1429/1512` and `1`, and its truncation error
after `Y ≥ 4` terms is at most `1/3584`. -/
theorem b6_mobiusMersenne_rung_estimates {r Y : ℕ} (hr : 3 ≤ r) (hY : 4 ≤ Y) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r
      ∧ mobiusMersenneTheta r < 1
      ∧ |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤ (1 : ℝ) / 3584 :=
  ⟨mobiusMersenneTheta_ge_alpha hr, mobiusMersenneTheta_lt_one hr,
   abs_mobiusMersenneTheta_sub_prefix_le hY hr⟩

/-- The second rung is the exact offset of the #249 constant:
`Θ₂ = S - 1/2`. -/
theorem b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half :
    mobiusMersenneTheta 2 = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := by
  rw [tsum_totient_div_pow_two_eq_pnat_half_pow]
  exact mobiusMersenneTheta_two_eq_totient_offset

/-- **The trailing bound of `prop:b6`.**  For every `e ≥ 1` and `Y ≥ 4`,
`t(Y,e+2)^2 / t(Y,2e+2) - (S - 1/2) > 1/480`.  The bound holds for every
stated pair `e, Y`, not merely for a finite list of computed examples. -/
theorem b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (e + 2)) ^ 2 /
        (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (2 * e + 2)) -
        ((∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2) := by
  have h := rankOneSubrankQuotient_sub_theta_two_gt he hY
  rw [b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half] at h
  unfold rankOneSubrankQuotient at h
  rwa [b6_mobiusMersennePrefix_eq_icc_sum Y (e + 2),
    b6_mobiusMersennePrefix_eq_icc_sum Y (2 * e + 2)] at h

#print axioms b6_retained_dyadic_sections_independent
#print axioms b6_compressed_adjoint_identity_impossible
#print axioms b6_mobius_incidence_unimodular_and_injective
#print axioms b6_adjugate_tail_cost_floor
#print axioms b6_synthetic_sequence_prescribed_differences
#print axioms b6_synthetic_shift_combinations_same_form
#print axioms b6_mobiusMersennePrefix_eq_icc_sum
#print axioms b6_mobiusMersenne_rung_estimates
#print axioms b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half
#print axioms b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt

end ErdosProblems.Erdos249.PaperCompleteR21
