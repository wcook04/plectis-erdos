import Erdos249257.ActualForeignResidueProjection
import Erdos249257.GeometricCoprimality
import Erdos249257.PivotAntiReconstruction

/-! Paper-form restatements of the long paper's squared-phase identities, of
the finite divisor sum `A_H`, of the exclusion consumer, and of the
coprime-pair count:

* *Squared distance from the phase one*;
* *Squared-distance bound for separated pairs*;
* *The finite divisor sum* — `A_H = H ∑_{d ∣ H} μ(d)/(d(2^d-1))`;
* *Separation larger than the error implies exclusion*;
* *Coprime-pair counting and the totient*.

Here `R_N = totientTail N`, `E(h,N,L) = windowFirstExp h N L`,
`κ_d(N) = foreignResidueKernel d N`, `a_d(N) = residueOffset d N`,
`P_{H,D} = projectedForeignDefect H D` and
`ε_{H,D} = foreignComplementBound H D`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open scoped BigOperators
open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.FullTargetPrimeAdjunctionNoGo
open Erdos249257.ActualForeignResidueProjection

/-! ### Squared distances between complex phases -/

/-- **Squared distance from the phase one.**
`∑_{N ∈ T} ‖E(h,N,L) - 1‖² = 2|T| - 2 ∑_{N ∈ T} Re E(h,N,L)`. -/
theorem sum_sq_dist_from_phase_one (h L : ℕ) (T : Finset ℕ) :
    ∑ N ∈ T, ‖windowFirstExp h N L - 1‖ ^ 2 =
      2 * (T.card : ℝ) - 2 * ∑ N ∈ T, (windowFirstExp h N L).re := by
  rw [← firstHarmonicAnchorDefect_eq_sum_norm_sq, firstHarmonicAnchorDefect_eq]
  simp only [windowFirstExp_re]

/-- **Squared-distance bound for separated pairs.**  For a finite family
`z : T → ℂ`, a real `δ ≥ 0` and any set of pairs `P ⊆ T × T` each separated by
at least `δ`, `|P|·δ² ≤ ∑_{i,j ∈ T} ‖z i - z j‖²`. -/
theorem card_mul_sq_le_pairwise_energy {α : Type*} [DecidableEq α]
    (T : Finset α) (z : α → ℂ) (P : Finset (α × α)) (δ : ℝ)
    (hP : P ⊆ T.product T) (hδ : 0 ≤ δ)
    (hsep : ∀ p ∈ P, δ ≤ ‖z p.1 - z p.2‖) :
    (P.card : ℝ) * δ ^ 2 ≤ ∑ i ∈ T, ∑ j ∈ T, ‖z i - z j‖ ^ 2 :=
  card_mul_sq_le_sum_pairwise_norm_sq_of_separatedPairs T z P δ hP hδ hsep

/-! ### The finite divisor sum -/

/-- For `d ∣ H` with `d ≥ 1`, both `a_d(H)` and `a_d(2H)` equal `d`. -/
theorem residueOffset_of_dvd {d H : ℕ} (_hd : 0 < d) (hdvd : d ∣ H) :
    residueOffset d H = d ∧ residueOffset d (2 * H) = d := by
  have h2 : d ∣ 2 * H := dvd_mul_of_dvd_right hdvd 2
  constructor
  · rw [residueOffset, Nat.mod_eq_zero_of_dvd hdvd, Nat.sub_zero]
  · rw [residueOffset, Nat.mod_eq_zero_of_dvd h2, Nat.sub_zero]

/-- For `d ∣ H` with `d ≥ 1`, `κ_d(2H) - κ_d(H) = H μ(d)/(d(2^d-1))`. -/
theorem residueKernel_increment_of_dvd {d H : ℕ} (hd : 0 < d) (hdvd : d ∣ H) :
    foreignResidueKernel d (2 * H) - foreignResidueKernel d H =
      (H : ℝ) * ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  have h := residueIncrement_of_dvd hd hdvd
  rw [residueIncrement] at h
  rw [h]
  ring

/-- **The finite divisor sum.**  For an integer `H > 0` the contribution of the
divisor indices to `R_{2H} - R_H` is `A_H = H ∑_{d ∣ H} μ(d)/(d(2^d-1))`. -/
theorem divisorChannels_sum_eq (H : ℕ) (_hH : 0 < H) :
    ∑ d ∈ H.divisors, residueIncrement d H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [residueIncrement_of_dvd (Nat.pos_of_mem_divisors hd)
    (Nat.dvd_of_mem_divisors hd)]
  ring

/-- The explicit shadow `A_H` used by the enclosure is exactly that divisor
contribution. -/
theorem scaleExplicitShadow_eq_divisorChannels {H : ℕ} (hH : 0 < H) :
    scaleExplicitShadow H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  rw [scaleExplicitShadow_eq_sum_divisors_residueIncrement hH,
    divisorChannels_sum_eq H hH]

/-! ### Separation larger than the error implies exclusion -/

private theorem diagonalCoefficient_cast_local (H : ℕ) :
    ((diagonalCoefficient H : ℕ) : ℝ) = (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) := by
  have h1 : (1 : ℕ) ≤ 2 ^ H := Nat.one_le_pow H 2 (by norm_num)
  rw [diagonalCoefficient, Nat.cast_mul, Nat.cast_sub h1]
  push_cast
  ring

/-- `P_{H,D} = ∑_{1 ≤ d ≤ D, d ∤ H} (κ_d(2H) - κ_d(H))`. -/
theorem projectedForeignDefect_paper (H D : ℕ) :
    projectedForeignDefect H D =
      ∑ d ∈ Finset.Icc 1 D,
        (if d ∣ H then 0
          else foreignResidueKernel d (2 * H) - foreignResidueKernel d H) := rfl

/-- `ε_{H,D} = 2^H(2^H-1)(2/2^D + 4/(3·4^D))`. -/
theorem foreignComplementBound_paper (H D : ℕ) :
    foreignComplementBound H D =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D)) := by
  rw [foreignComplementBound, diagonalCoefficient_cast_local]

/-- **Separation larger than the error implies exclusion.**  If
`|(R_{2H} - R_H) - (A_H + P_{H,D})| ≤ ε_{H,D}` and `|A_H + P_{H,D} - z| > ε_{H,D}`
for every integer `z`, then `R_{2H} - R_H ∉ ℤ`. -/
theorem tailDifference_not_integral_of_separation {H D : ℕ}
    (hbound :
      |totientTail (2 * H) - totientTail H -
        (scaleExplicitShadow H + projectedForeignDefect H D)| ≤
        foreignComplementBound H D)
    (hsep : ∀ z : ℤ,
      foreignComplementBound H D <
        |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|) :
    totientTail (2 * H) - totientTail H ∉ Set.range ((↑) : ℤ → ℝ) := by
  have hctrl : ControlledForeignProjection H D := by
    show |scaleForeignDefect H - projectedForeignDefect H D| ≤
      foreignComplementBound H D
    have heq :
        scaleForeignDefect H - projectedForeignDefect H D =
          totientTail (2 * H) - totientTail H -
            (scaleExplicitShadow H + projectedForeignDefect H D) := by
      rw [scaleForeignDefect, scaleDiagonalTailDifference]
      ring
    rw [heq]
    exact hbound
  have hmiss := scaleFullTarget_miss_of_projected_separation hctrl hsep
  rw [scaleFullTargetHit_iff_integral] at hmiss
  exact hmiss

/-! ### Coprime-pair counting -/

/-- **Coprime-pair counting and the totient.**  For every `n ∈ ℕ`,
`#{(a,b) ∈ ℕ² : a+b = n, a > 0, gcd(a,b) = 1} = φ(n)`. -/
theorem card_coprime_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2)).card = Nat.totient n :=
  GeometricCoprimality.card_antidiagonal_filter_pos_coprime n

/-- `b = 0` is allowed: the boundary pair `(1,0)` is counted, and it accounts
for the value `φ(1) = 1`. -/
theorem boundary_pair_at_one :
    (1, 0) ∈ (Finset.antidiagonal 1).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2) ∧
      ((Finset.antidiagonal 1).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2)).card = 1 := by
  constructor
  · simp
  · rw [GeometricCoprimality.card_antidiagonal_filter_pos_coprime 1, Nat.totient_one]

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.sum_sq_dist_from_phase_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.card_mul_sq_le_pairwise_energy
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.residueOffset_of_dvd
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.residueKernel_increment_of_dvd
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.divisorChannels_sum_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.scaleExplicitShadow_eq_divisorChannels
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.projectedForeignDefect_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.foreignComplementBound_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_not_integral_of_separation
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.card_coprime_antidiagonal
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.boundary_pair_at_one
