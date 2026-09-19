import ErdosProblems.Erdos243.PaperCompleteR11.RecordGcdReduction

/-!
# Inclusive coefficient-one record boundary


The exact conclusion is a fixed coefficient c>1 exceeded cofinally at
strict global records. This implies the paper's strict limsup inequality;
the separate extended-real presentation is not used in this proof.
Both gcd alternatives are handled by constructed quotient tails.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open PaperCompleteR7 Filter
open scoped Topology

/-- The exact tail gcd is a positive monotone divisibility chain. -/
theorem RecordGrowthOrbit.gcd_monotone (O : RecordGrowthOrbit) :
    Monotone (fun n ↦ Nat.gcd (O.U n) (O.D n)) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (O.U_pos _))
    (tailGcd_dvd_succ _ _ _ _ _ (O.U_step n) (O.D_step n))

/-- Full inclusive arithmetic assembly: an unbounded orbit has some fixed
coefficient strictly above one for which no eventual record cap exists. -/
theorem RecordGrowthOrbit.no_inclusive_record_cap (O : RecordGrowthOrbit) :
    ∃ c : ℝ, 1 < c ∧ ¬ ∃ T : ℕ, ∀ n, T ≤ n → runningMax O.U n < O.U (n + 1) →
      ((O.U (n + 1) - runningMax O.U n : ℕ) : ℝ) ≤ c * recordLogLog (runningMax O.U n) := by
  classical
  let G := fun n ↦ Nat.gcd (O.U n) (O.D n)
  have hGpos : ∀ n, 0 < G n := fun n ↦ Nat.gcd_pos_of_pos_left _ (O.U_pos n)
  by_cases hbounded : ∃ B : ℕ, ∀ n, G n ≤ B
  · obtain ⟨B, hB⟩ := hbounded
    obtain ⟨N, hN⟩ := dvdChain_eventuallyConstant_of_cofinally_bounded G B hGpos
      (fun n ↦ tailGcd_dvd_succ _ _ _ _ _ (O.U_step n) (O.D_step n))
      (fun n ↦ ⟨n, le_rfl, hB n⟩)
    obtain ⟨s, hNs, hs⟩ := exists_late_attained_record O.U O.unbounded N
    let g := G s
    have hg : 0 < g := hGpos s
    have hUg : g ∣ O.U s := Nat.gcd_dvd_left _ _
    have hDg : g ∣ O.D s := Nat.gcd_dvd_right _ _
    let V := O.quotientAt s g hg hUg hDg
    have hstable : ∀ n, G (s + n) = g := by
      intro n
      exact (hN (s + n) (by omega)).trans (hN s hNs).symm
    have hred : ∀ n, Nat.Coprime (V.U n) (V.D n) := by
      intro n
      have hh := Nat.coprime_div_gcd_div_gcd (hGpos (s + n))
      change Nat.Coprime (O.U (s + n) / g) (O.D (s + n) / g)
      simpa only [← hstable n] using hh
    let W := V.D 2
    have hW : 1 < W := by
      have ha2 : 2 ≤ V.a 1 := by
        have hmono := V.increasing (show 0 < 1 by omega)
        have hpos := V.a_pos 0
        omega
      have hmul := Nat.mul_le_mul ha2 (show 1 ≤ V.D 1 by have := V.D_pos 1; omega)
      have hstep := V.D_step 1
      dsimp [W]
      omega
    have hphi : (0 : ℝ) < Nat.totient W := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < W))
    let c : ℝ := (1 + (W : ℝ) / Nat.totient W) / 2
    have hratio := presieved_totient_ratio_gt_one W hW
    have hc1 : 1 < c := by dsimp [c]; linarith
    have hc0 : 0 ≤ c := by linarith
    have hcW : c * Nat.totient W < W := by
      apply (lt_div_iff₀ hphi).1
      dsimp [c]
      linarith
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
    have hcdiv : c / g ≤ c := by
      apply (div_le_iff₀ hgR).2
      have hh := mul_le_mul_of_nonneg_left hg1 hc0
      nlinarith
    refine ⟨c, hc1, ?_⟩
    rintro ⟨T, hcap⟩
    apply no_primitive_totient_record_cap V.a V.U V.D V.increasing
      V.a_pos V.U_pos V.D_pos V.U_step V.D_step hred
      V.lower V.record_bound V.den_bound V.unbounded W 2 hW (dvd_refl W)
      g (c / g) (div_nonneg hc0 hgR.le)
      ((mul_le_mul_of_nonneg_right hcdiv hphi.le).trans_lt hcW)
    exact ⟨T, O.quotient_record_cap s g hg hUg hDg hs c T hcap⟩
  · have hex : ∃ n, 3 ≤ G n := by
      by_contra hnot
      apply hbounded
      refine ⟨2, fun n ↦ ?_⟩
      by_contra hn
      exact hnot ⟨n, by omega⟩
    obtain ⟨N, hGN⟩ := hex
    obtain ⟨s, hNs, hs⟩ := exists_late_attained_record O.U O.unbounded N
    let g := G s
    have hg3 : 3 ≤ g := hGN.trans (O.gcd_monotone hNs)
    have hg : 0 < g := by omega
    have hUg : g ∣ O.U s := Nat.gcd_dvd_left _ _
    have hDg : g ∣ O.D s := Nat.gcd_dvd_right _ _
    let V := O.quotientAt s g hg hUg hDg
    refine ⟨2, by norm_num, ?_⟩
    rintro ⟨T, hcap⟩
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg
    have hsmall : (2 : ℝ) / g < 1 := by
      apply (div_lt_iff₀ hgR).2
      have hh : (3 : ℝ) ≤ g := by exact_mod_cast hg3
      linarith
    apply no_subcritical_record_cap V.a V.U V.D V.increasing V.a_pos V.U_pos V.D_pos
      V.U_step V.D_step V.lower V.record_bound V.den_bound V.unbounded
      g (2 / g) (by positivity) hsmall
    exact ⟨T, O.quotient_record_cap s g hg hUg hDg hs 2 T hcap⟩

/-- The strict improvement occurs cofinally at actual global records. -/
theorem RecordGrowthOrbit.cofinal_inclusive_record (O : RecordGrowthOrbit) :
    ∃ c : ℝ, 1 < c ∧ ∀ T : ℕ, ∃ n, T ≤ n ∧ runningMax O.U n < O.U (n + 1) ∧
      c * recordLogLog (runningMax O.U n) <
        ((O.U (n + 1) - runningMax O.U n : ℕ) : ℝ) := by
  obtain ⟨c, hc, hnocap⟩ := O.no_inclusive_record_cap
  refine ⟨c, hc, fun T ↦ ?_⟩
  by_contra hnot
  apply hnocap
  refine ⟨T, fun n hn hnew ↦ ?_⟩
  by_contra hh
  exact hnot ⟨n, hn, hnew, lt_of_not_ge hh⟩

/-- With normalised integer vanishing, a bounded canonical numerator
forces exact eventual Sylvester recursion; no bounded-error assumption is added. -/
theorem canonical_unbounded_of_not_sylvester
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    ∀ H : ℕ, ∃ n, H ≤ canonicalNaturalNumerator a p q n := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  obtain ⟨hCpos, hDpos, hC, hD, htail, hvanish, hcentred⟩ :=
    canonical_integer_tail_normalized a ha hapos p q hq hs hgrowth
  intro H
  by_contra hno
  have hbound : ∀ n, C n < H := by
    intro n
    by_contra hn
    exact hno ⟨n, le_of_not_gt hn⟩
  obtain ⟨N, hN⟩ := hvanish H
  have hzero : ∀ n, N ≤ n → E n = 0 := by
    intro n hn
    by_contra hne
    have habs : 1 ≤ Int.natAbs (E n) := by
      have hh := Int.natAbs_pos.mpr hne
      omega
    have hmul := Nat.mul_le_mul_left H habs
    have hh := hN n hn
    have hb := hbound n
    omega
  apply hnot
  apply sylvesterNext_eventually_of_centered_zero
    (fun n ↦ (a n : ℤ)) (fun n ↦ (D n : ℤ)) (fun n ↦ (C n : ℤ))
  · intro n
    exact natDen_eq_nextDenState a D hD n
  · intro n
    exact natTail_eq_nextTailState a C D hC n
  · exact ⟨N, hzero⟩
  · exact ⟨0, fun n _ ↦ by exact_mod_cast (hCpos (n + 1)).ne'⟩

/-- Canonical construction from the paper's original hypotheses alone. -/
noncomputable def canonicalRecordGrowthOrbit
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    RecordGrowthOrbit := by
  obtain ⟨hCpos, hDpos, hC, hD, htail⟩ := canonical_integer_tail a hapos p q hq hs
  refine {
    a := a, U := canonicalNaturalNumerator a p q, D := canonicalDenominator a q
    increasing := ha, a_pos := hapos, U_pos := hCpos, D_pos := hDpos
    U_step := hC, D_step := hD
    lower := ?_
    record_bound := canonical_runningMax_binary_exponent a ha hapos p q hq hs hgrowth
    den_bound := canonical_denominator_binaryTower_bound a ha hapos q hgrowth
    unbounded := canonical_unbounded_of_not_sylvester a ha hapos p q hq hs hgrowth hnot }
  obtain ⟨N, A, hN, hA, hbounds⟩ := quadratic_double_exponential_bounds a ha hapos hgrowth
  exact ⟨N, fun k ↦ (hbounds k).1⟩

/-- The inclusive record theorem in cofinal form, with the canonical
cleared numerator, the original global maximum and the exact base-two
normaliser. There are no extra arithmetic, growth or block hypotheses. -/
theorem canonical_inclusive_record_boundary
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    ∃ c : ℝ, 1 < c ∧ ∀ T : ℕ, ∃ n, T ≤ n ∧
      runningMax (canonicalNaturalNumerator a p q) n < canonicalNaturalNumerator a p q (n + 1) ∧
      c * recordLogLog (runningMax (canonicalNaturalNumerator a p q) n) <
        ((canonicalNaturalNumerator a p q (n + 1) -
          runningMax (canonicalNaturalNumerator a p q) n : ℕ) : ℝ) :=
  (canonicalRecordGrowthOrbit a ha hapos p q hq hs hgrowth hnot).cofinal_inclusive_record

end ErdosProblems.Erdos243.PaperCompleteR11
