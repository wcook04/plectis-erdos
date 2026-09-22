import Erdos249257.TotientActualLcmShortKill
import Erdos249257.LcmConeFlatness
import Erdos249257.CertificateKernel

/-! Paper-form restatements of three long-paper environments of Erdős #249:

* the bounded short-window family through exponent six, with its single
  witness `(a,L) = (6,93)` and the identification of that witness with the
  `t = 64` diagonal certificate;
* the sufficient logarithmic-depth extension of the diagonal certificate
  table;
* the one common certificate `C(h,14,9)` for the sixteen shifts
  `h ∈ {1,…,16}`, its denominator consequence, and the earlier eight-shift
  computation at basepoint `12` and depth `16`.

Here `H(t) = periodLcm t`, `R_N = totientTail N`, `D(h,N,L) =
windowDiscrepancy h N L` and `C(h,N,L) = certifiedKill h N L`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine

/-! ### The short-window examples through exponent 6 -/

/-- **The bounded short-window statement.**
`∀ a₀ ≤ 6, ∃ a, L, a₀ ≤ a ∧ L < 2·2^a ∧ C(H_{2^a}, H_{2^a}, L)`. -/
theorem shortWindowSupply_through_six_paper (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L := by
  obtain ⟨a, L, ha, hL, hkill⟩ :=
    powerTwoActualLcmShortArithmeticKillSupply_through_six a₀ ha₀
  exact ⟨a, L, ha, hL, (lcmDiagonalArithmeticKill_iff_certifiedKill (2 ^ a) L).1 hkill⟩

/-- **The single witness.**  `(a,L) = (6,93)` satisfies the three displayed
clauses for every threshold `a₀ ≤ 6`. -/
theorem shortWindowSupply_single_witness_six_ninetyThree (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    a₀ ≤ 6 ∧ (93 : ℕ) < 2 * 2 ^ 6 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 :=
  ⟨ha₀, by norm_num,
    (lcmDiagonalArithmeticKill_iff_certifiedKill (2 ^ 6) 93).1
      lcmDiagonalArithmeticKill_two_pow_six⟩

/-- The witness certificate is the `t = 64` diagonal certificate: the finite
totient windows verified there are the ones the witness uses. -/
theorem shortWindowSupply_witness_eq_t64_certificate :
    certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ↔
      certifiedKill (periodLcm 64) (periodLcm 64) 93 := by
  norm_num

/-! ### A sufficient extension of the diagonal certificate table -/

/-- **A sufficient extension.**  If there is a constant `C` such that for every
`t₀` some `t ≥ t₀` carries a diagonal certificate at a depth
`L ≤ log₂(4·H_t) + C`, then `S ∉ ℚ`.  The depth restriction is only a
restriction: the cofinal diagonal supply it contains already suffices. -/
theorem irrational_of_logarithmicDepth_diagonal_supply
    (hsupply : ∃ C : ℕ, ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      L ≤ Nat.log2 (4 * periodLcm t) + C ∧
        certifiedKill (periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  obtain ⟨C, hC⟩ := hsupply
  refine irrational_totient_series_of_lcm_cone_certificate_supply ?_
  intro t₀
  obtain ⟨t, ht, L, _hL, hkill⟩ := hC t₀
  exact ⟨t, ht, 1, 1, L, Nat.one_pos, by simpa using hkill⟩

/-- The sufficiency does not depend on how the logarithmic depth bound
`L ≤ log₂(4·H_t) + C` is rendered: ANY depth restriction whatsoever leaves the
cofinal diagonal supply sufficient for `S ∉ ℚ`. -/
theorem irrational_of_restrictedDepth_diagonal_supply (depthBound : ℕ → ℕ → Prop)
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      depthBound t L ∧ certifiedKill (periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_lcm_cone_certificate_supply ?_
  intro t₀
  obtain ⟨t, ht, L, _hL, hkill⟩ := hsupply t₀
  exact ⟨t, ht, 1, 1, L, Nat.one_pos, by simpa using hkill⟩

/-! ### One common certificate for sixteen shifts -/

/-- **`C(h,14,9)` for `h ∈ {1,…,16}`.**  The basepoint `14` and the depth `9`
are common to all sixteen shifts. -/
theorem commonCertificate_sixteen_shifts_basepoint_fourteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9 :=
  certifiedKill_all_upto_sixteen

/-- **The denominator consequence.**  `S ≠ r` whenever `r ∈ ℚ` and
`den(r) ∣ 2¹⁴(2ʰ-1)` for some integer `h` with `1 ≤ h ≤ 16`. -/
theorem totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne
    (r : ℚ) (h : ℕ) (h1 : 1 ≤ h) (h16 : h ≤ 16)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) :=
  totient_series_ne_rat_of_den_dvd_pow_two_mul_mersenne_upto_sixteen r h h1 h16 hdvd

/-- **The earlier eight-shift computation** uses basepoint `12` and depth `16`. -/
theorem commonCertificate_eight_shifts_basepoint_twelve :
    ∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16 :=
  certifiedKill_all_small

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_through_six_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_single_witness_six_ninetyThree
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_witness_eq_t64_certificate
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_logarithmicDepth_diagonal_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_restrictedDepth_diagonal_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_sixteen_shifts_basepoint_fourteen
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_eight_shifts_basepoint_twelve
