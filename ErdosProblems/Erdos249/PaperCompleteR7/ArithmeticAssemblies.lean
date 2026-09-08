import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.SignedQMomentObstruction
import Erdos249257.AllBaseTotientKernel
import ErdosProblems.Erdos249.CyclotomicAnchoredKill
import Mathlib

/-!
# Exact arithmetic and endpoint assemblies for the two papers

Targets include long-record cert:d9 / prop:D9-inv, mob:a1b,
T7, prop:CP-04-kill, and the level-zero clause of short-note res:basis.
The canonical Mersenne theorem is restated with the quotient and oddness
as printed, instead of silently changing its quantifiers.

These are proof-source candidates; compilation was NOT available in this run.
The rational-gap proof reuses the existing exact separation inequality; the
same adapter is present under the older public namespace in
Erdos249257/PrimitiveRationalGapSupply.lean at the retained public pin.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7

open scoped BigOperators
open Erdos249257
open Erdos249257.SignedQMomentObstruction
open ErdosProblems.Erdos249.CyclotomicAnchoredKill

/-- Long-record cert:d9 and prop:D9-inv, using actual reduced denominators. -/
theorem positive_rational_gap {whole pfx : ℚ} (h : pfx < whole) :
    (1 : ℝ) / ((whole.den * pfx.den : ℕ) : ℝ) ≤
      (whole : ℝ) - (pfx : ℝ) := by
  have hgap := one_div_den_mul_den_le_abs_sub (ne_of_gt h)
  have hp : (0 : ℝ) < (whole : ℝ) - (pfx : ℝ) :=
    sub_pos.mpr (by exact_mod_cast h)
  rw [abs_of_pos hp] at hgap
  simpa only [Nat.cast_mul] using hgap

/-- The exact irrationality restatement, not merely the underlying identity. -/
theorem irrational_totient_iff_moebius_square :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) ↔
      Irrational (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  rw [totient_series_eq_half_add_moebius_mersenne_square]
  constructor
  · intro h
    have hh : Irrational (((1 / 2 : ℚ) : ℝ) +
      (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2)) := by simpa using h
    exact hh.of_ratCast_add (1 / 2 : ℚ)
  · intro h
    simpa using h.ratCast_add (1 / 2 : ℚ)

/-- Only the first rung is asserted rational. The second is the exact offset
of the unresolved value; the misleading plural in the long-record heading
is not promoted to a claim that the second rung is rational. -/
theorem low_rungs_with_literal_totient_series :
    mobiusMersenneTheta 1 = 1 / 2 ∧
    mobiusMersenneTheta 2 =
      (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) - 1 / 2 := by
  refine ⟨mobiusMersenneTheta_one, ?_⟩
  rw [tsum_totient_div_pow_two_eq_pnat_half_pow]
  exact mobiusMersenneTheta_two_eq_totient_offset

/-- Long-record T7: existence equivalence and rigidity in one endpoint. -/
theorem generic_tempered_equivalence_and_rigidity
    (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) :
    (HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u) ∧
    (∀ (v : ℕ) (u : ℕ → ℤ), IsTemperedBinaryOrbit c v u →
      ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N) := by
  exact ⟨binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit c hc,
    fun _ _ h => temperedBinaryOrbit_eq_scaledTail c hc h⟩

/-- The absolute-adjugate no-go, with the claimed c(n)<=n transfer included.
It is a bound on this exact triangle-inequality cost, not on all possible
reconstruction or cancellation arguments. -/
theorem generic_absolute_adjugate_floor
    {ι : Type*} [Fintype ι]
    (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (w : ι → ℚ) (x : ι → ℕ)
    (hisolate : ∑ i, w i * (c (x i) : ℚ) = 1) :
    (3 : ℚ) ≤ ∑ i, |w i| * (2 * ((x i : ℚ) + 1) + ((x i : ℚ) + 2)) := by
  classical
  have hmass : (1 : ℚ) ≤ ∑ i, |w i| * (c (x i) : ℚ) := by
    calc
      (1 : ℚ) = |∑ i, w i * (c (x i) : ℚ)| := by rw [hisolate]; norm_num
      _ ≤ ∑ i, |w i * (c (x i) : ℚ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |w i| * (c (x i) : ℚ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ c (x i))]
  have hmass' : (1 : ℚ) ≤ ∑ i, |w i| * (x i : ℚ) := by
    apply hmass.trans
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast hc (x i)) (abs_nonneg _))
  calc
    (3 : ℚ) ≤ 3 * (∑ i, |w i| * (x i : ℚ)) := by linarith
    _ = ∑ i, 3 * (|w i| * (x i : ℚ)) := Finset.mul_sum _ _ _
    _ ≤ ∑ i, |w i| * (2 * ((x i : ℚ) + 1) + ((x i : ℚ) + 2)) := by
      exact Finset.sum_le_sum (fun i _ => by nlinarith [abs_nonneg (w i)])

/-- The complete totient specialisation of prop:CP-04-kill. -/
theorem totient_absolute_adjugate_floor
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ)
    (hisolate : ∑ i, w i * (Nat.totient (x i) : ℚ) = 1) :
    (3 : ℚ) ≤ ∑ i, |w i| * (2 * ((x i : ℚ) + 1) + ((x i : ℚ) + 2)) :=
  generic_absolute_adjugate_floor Nat.totient Nat.totient_le w x hisolate

/-- The *complete* level-zero truncation contains only phi(n), whereas the
canonical family used at positive levels intentionally has two zero channels. -/
theorem complete_level_zero_rank (k : ℕ) :
    Module.finrank ℚ
      (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily k 0))) = 1 := by
  classical
  let v : Fin 1 → ℕ → ℚ := fun _ n => (Nat.totient n : ℚ)
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hh := congrFun ha 1
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [v, Fin.sum_univ_one, Pi.smul_apply, hi] using hh
  have hseq : ∀ i : AllBaseThroughLevelIndex k 0,
      allBaseThroughLevelFamily k 0 i = v 0 := by
    rintro ⟨⟨j, hj⟩, ⟨r, hr⟩⟩
    have hj0 : j = 0 := by omega
    subst j
    simp only [pow_zero] at hr
    have hr0 : r = 0 := by omega
    subst r
    funext n
    simp [allBaseThroughLevelFamily, allBaseTotientKernelSeq, v]
  have hrange : Set.range (allBaseThroughLevelFamily k 0) = Set.range v := by
    apply Set.Subset.antisymm
    · rintro f ⟨i, rfl⟩
      exact ⟨0, (hseq i).symm⟩
    · rintro f ⟨i, rfl⟩
      refine ⟨⟨⟨0, by omega⟩, ⟨0, by simp⟩⟩, ?_⟩
      simpa [v] using hseq (⟨⟨0, by omega⟩, ⟨0, by simp⟩⟩ : AllBaseThroughLevelIndex k 0)
  rw [hrange, finrank_span_eq_card hli]
  simp

/-! ## Canonical gap, with the exact printed quotient -/

/-- Euler multiples automatically give the Mersenne divisibility needed by
natural division. The quotient is never treated as an arbitrary modulus. -/
theorem odd_euler_multiple_mersenne_dvd {v H : ℕ}
    (hv : Nat.Coprime 2 v) (hH : Nat.totient v ∣ H) : v ∣ 2 ^ H - 1 := by
  have heuler : (2 : ℕ) ^ Nat.totient v ≡ 1 [MOD v] := Nat.ModEq.pow_totient hv
  have hbase : v ∣ 2 ^ Nat.totient v - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp heuler.symm
  exact hbase.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hH)

/-- Literal short-note res:canonicalmersenne. All residues are integer
remainders; the modulus is the natural quotient (2^H-1)/v. -/
theorem canonical_mersenne_gap_iff :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) ↔
      ∀ c v : ℕ, 0 < v → Odd v → ∃ H : ℕ,
        0 < H ∧ Nat.totient v ∣ H ∧
        ((c : ℤ) + H + 1 < (-totientBlock H c) % (((2 ^ H - 1) / v : ℕ) : ℤ) ∧
        (-totientBlock H c) % (((2 ^ H - 1) / v : ℕ) : ℤ) <
          (((2 ^ H - 1) / v : ℕ) : ℤ) - ((c : ℤ) + H + 1)) := by
  rw [← fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational]
  constructor
  · intro hs c v hv hodd
    have hc : Nat.Coprime 2 v :=
      Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat
    obtain ⟨H, M, hH, hperiod, hfactor, hgap⟩ := hs c v hv hc
    have hM : (2 ^ H - 1) / v = M := by
      rw [← hfactor, Nat.mul_div_cancel_left _ hv]
    refine ⟨H, hH, hperiod, ?_⟩
    rw [hM]
    exact hgap
  · intro hs c v hv hcop
    have hodd : Odd v := by
      apply Nat.odd_iff.mpr
      have hn : ¬ 2 ∣ v := Nat.prime_two.coprime_iff_not_dvd.mp hcop
      omega
    obtain ⟨H, hH, hperiod, hgap⟩ := hs c v hv hodd
    refine ⟨H, (2 ^ H - 1) / v, hH, hperiod, ?_, hgap⟩
    exact Nat.mul_div_cancel' (odd_euler_multiple_mersenne_dvd hcop hperiod)

/-- The common-window deposit and its exact denominator exclusion in one
endpoint, covering long-record environment 044 (also repeated at 201). -/
theorem common_window_upto_sixteen :
    (∀ h : ℕ, 1 ≤ h → h ≤ 16 →
      TotientTailPeriodKiller.certifiedKill h 14 9) ∧
    (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 16 →
      r.den ∣ 2 ^ 14 * (2 ^ h - 1) →
      (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) ≠ (r : ℝ)) := by
  constructor
  · intro h h1 h16
    exact TotientTailPeriodKiller.certifiedKill_all_upto_sixteen h
      (Finset.mem_Icc.mpr ⟨h1, h16⟩)
  · exact totient_series_ne_rat_of_den_dvd_pow_two_mul_mersenne_upto_sixteen

/-- Exact parity and nonvanishing together, for the unlabelled
unique-terminal lemma (long-record environment 219). -/
theorem unique_terminal_parity_and_nonzero
    {α : Type*} (s : Finset α) (u : α → ℤ) (e : α → ℕ)
    (m : α) (hm : m ∈ s) (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) % 2 = 1 ∧
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) ≠ 0 := by
  exact ⟨scaled_dyadic_sum_odd s u e m hm hu hmax,
    scaled_dyadic_sum_ne_zero s u e m hm hu hmax⟩

end ErdosProblems.Erdos249.PaperCompleteR7
