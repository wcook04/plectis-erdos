import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup
import ErdosProblems.Erdos243.PaperCompleteR11.CanonicalRecords

/-!
# The quantitative branches of the global record dichotomy


This file retains the actual all-index running maximum. In particular the
quotient begins at an attained original record, and the normaliser is
`recordLogLog (g * runningMax V.U n)`, not an asymptotic replacement.
The primitive estimate applies to every sufficiently late denominator,
not just to one selected denominator.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter PaperCompleteR7
open scoped Topology

/-- A real threshold exceeded cofinally is below the extended-real limsup. -/
theorem ereal_le_limsup_of_cofinal_lt (f : ℕ → ℝ) (c : ℝ)
    (h : ∀ T : ℕ, ∃ n, T ≤ n ∧ c < f n) :
    (c : EReal) ≤ limsup (fun n ↦ (f n : EReal)) atTop := by
  apply le_limsup_of_frequently_le
  apply frequently_atTop.2
  intro T
  obtain ⟨n, hn, hc⟩ := h T
  exact ⟨n, hn, EReal.coe_le_coe_iff.mpr hc.le⟩

/-- Taking all strict real lower bounds does not require boundedness of the sequence. -/
theorem ereal_le_of_all_real_lt (x : ℝ) (z : EReal)
    (h : ∀ c : ℝ, c < x → (c : EReal) ≤ z) : (x : EReal) ≤ z := by
  cases z using EReal.rec with
  | bot =>
      exact False.elim ((not_le_of_gt (EReal.bot_lt_coe (x - 1)))
        (h (x - 1) (by linarith)))
  | coe y =>
      apply EReal.coe_le_coe_iff.mpr
      by_contra hxy
      have hyx : y < x := lt_of_not_ge hxy
      have hc := h ((x + y) / 2) (by linarith)
      have hc' := EReal.coe_le_coe_iff.mp hc
      linarith
  | top => exact le_top

/-- The only extended real above every nonnegative real number is positive infinity. -/
theorem ereal_eq_top_of_nonneg_real_bounds (z : EReal)
    (h : ∀ c : ℝ, 0 ≤ c → (c : EReal) ≤ z) : z = ⊤ := by
  cases z using EReal.rec with
  | bot =>
      exact False.elim ((not_le_of_gt (EReal.bot_lt_coe 0)) (h 0 le_rfl))
  | coe y =>
      have hc := EReal.coe_le_coe_iff.mp (h (max y 0 + 1) (by
        linarith [le_max_right y 0]))
      have hh := le_max_left y 0
      linarith
  | top => rfl

/-- Nonnegativity of the actual record quotient, also on a drawdown. -/
theorem recordLogLogCharge_nonneg (U : ℕ → ℕ) (n : ℕ) :
    0 ≤ recordLogLogCharge U n := by
  exact div_nonneg (Nat.cast_nonneg _) ((by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_recordLogLog _))

theorem recordTheta_nonneg (U : ℕ → ℕ) : (0 : EReal) ≤ recordTheta U := by
  apply le_limsup_of_frequently_le
  have h : ∀ᶠ n in atTop, (0 : EReal) ≤ (recordLogLogCharge U n : EReal) :=
    Eventually.of_forall fun n ↦ by exact_mod_cast recordLogLogCharge_nonneg U n
  exact h.frequently

/-- Absence of an eventual cap gives frequent large values of the original charge. -/
theorem cofinal_charge_of_no_record_cap (U : ℕ → ℕ) (c : ℝ)
    (h : ¬ ∃ T : ℕ, ∀ n, T ≤ n → runningMax U n < U (n + 1) →
      ((U (n + 1) - runningMax U n : ℕ) : ℝ) ≤ c * recordLogLog (runningMax U n)) :
    ∀ T : ℕ, ∃ n, T ≤ n ∧ c < recordLogLogCharge U n := by
  intro T
  by_contra hbad
  apply h
  refine ⟨T, fun n hn hnew ↦ ?_⟩
  have hnot : ¬ c < recordLogLogCharge U n := fun hc ↦ hbad ⟨n, hn, hc⟩
  have hden : 0 < recordLogLog (runningMax U n) :=
    lt_of_lt_of_le zero_lt_one (one_le_recordLogLog _)
  have hh := (div_le_iff₀ hden).mp (le_of_not_gt hnot)
  simpa only [recordLogLogCharge, runningMax_true_increment] using hh

/-- Arbitrarily large common divisors exclude every finite nonnegative cap. -/
theorem RecordGrowthOrbit.no_finite_cap_of_unbounded_gcd (O : RecordGrowthOrbit)
    (hG : ∀ B : ℕ, ∃ n, B < Nat.gcd (O.U n) (O.D n))
    (c : ℝ) (hc : 0 ≤ c) :
    ¬ ∃ T : ℕ, ∀ n, T ≤ n → runningMax O.U n < O.U (n + 1) →
      ((O.U (n + 1) - runningMax O.U n : ℕ) : ℝ) ≤ c * recordLogLog (runningMax O.U n) := by
  obtain ⟨B, hB⟩ := exists_nat_gt c
  obtain ⟨N, hN⟩ := hG B
  obtain ⟨s, hNs, hs⟩ := exists_late_attained_record O.U O.unbounded N
  let g := Nat.gcd (O.U s) (O.D s)
  have hgB : B < g := hN.trans_le (O.gcd_monotone hNs)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (O.U_pos s)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hcG : c < g := hB.trans (by exact_mod_cast hgB)
  have hUg : g ∣ O.U s := Nat.gcd_dvd_left _ _
  have hDg : g ∣ O.D s := Nat.gcd_dvd_right _ _
  let V := O.quotientAt s g hg hUg hDg
  rintro ⟨T, hcap⟩
  apply no_subcritical_record_cap V.a V.U V.D V.increasing V.a_pos V.U_pos V.D_pos
    V.U_step V.D_step V.lower V.record_bound V.den_bound V.unbounded
    g (c / g) (div_nonneg hc hgR.le) ((div_lt_iff₀ hgR).mpr (by simpa using hcG))
  exact ⟨T, O.quotient_record_cap s g hg hUg hDg hs c T hcap⟩

/-- The unbounded-gcd branch has Theta = positive infinity, not merely Theta > 1. -/
theorem RecordGrowthOrbit.recordTheta_eq_top_of_unbounded_gcd (O : RecordGrowthOrbit)
    (hG : ∀ B : ℕ, ∃ n, B < Nat.gcd (O.U n) (O.D n)) :
    recordTheta O.U = ⊤ := by
  apply ereal_eq_top_of_nonneg_real_bounds
  intro c hc
  exact ereal_le_limsup_of_cofinal_lt (recordLogLogCharge O.U) c
    (cofinal_charge_of_no_record_cap O.U c (O.no_finite_cap_of_unbounded_gcd hG c hc))

/-- Division preserves a divisibility relation when the common factor divides the source. -/
theorem quotient_dvd_quotient (d x y : ℕ) (hd : 0 < d)
    (hdx : d ∣ x) (hxy : x ∣ y) : x / d ∣ y / d := by
  obtain ⟨k, hk⟩ := hxy
  refine ⟨k, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hd
  rw [Nat.mul_div_cancel' (hdx.trans ⟨k, hk⟩)]
  calc
    y = x * k := hk
    _ = d * ((x / d) * k) := by rw [← mul_assoc, Nat.mul_div_cancel' hdx]

/-- Once the gcd stabilises, every old primitive denominator supplies its full coefficient. -/
theorem RecordGrowthOrbit.no_stable_totient_cap (O : RecordGrowthOrbit)
    (N g : ℕ) (hg : 0 < g)
    (hstable : ∀ n, N ≤ n → Nat.gcd (O.U n) (O.D n) = g)
    (T : ℕ) (hNT : N ≤ T) (hW : 1 < O.D T / g)
    (c : ℝ) (hc : 0 ≤ c)
    (hcW : c * Nat.totient (O.D T / g) < (g : ℝ) * (O.D T / g : ℕ)) :
    ¬ ∃ R : ℕ, ∀ n, R ≤ n → runningMax O.U n < O.U (n + 1) →
      ((O.U (n + 1) - runningMax O.U n : ℕ) : ℝ) ≤ c * recordLogLog (runningMax O.U n) := by
  obtain ⟨s, hTs, hs⟩ := exists_late_attained_record O.U O.unbounded T
  have hNs : N ≤ s := hNT.trans hTs
  have hUg : g ∣ O.U s := by rw [← hstable s hNs]; exact Nat.gcd_dvd_left _ _
  have hDg : g ∣ O.D s := by rw [← hstable s hNs]; exact Nat.gcd_dvd_right _ _
  have hDgT : g ∣ O.D T := by rw [← hstable T hNT]; exact Nat.gcd_dvd_right _ _
  let V := O.quotientAt s g hg hUg hDg
  have hred : ∀ n, Nat.Coprime (V.U n) (V.D n) := by
    intro n
    have hp := Nat.gcd_pos_of_pos_left (O.D (s + n)) (O.U_pos (s + n))
    have hh := Nat.coprime_div_gcd_div_gcd hp
    change Nat.Coprime (O.U (s + n) / g) (O.D (s + n) / g)
    simpa only [hstable (s + n) (by omega)] using hh
  have hDTs : O.D T ∣ O.D s := dvd_denState_of_le O.a O.D 0 (O.D T) T
    (fun n _ ↦ O.D_step n) (Nat.zero_le _) (dvd_refl _) s hTs
  have hWold : O.D T / g ∣ V.D 0 := by
    simpa only [V, RecordGrowthOrbit.quotientAt, Nat.add_zero] using
      quotient_dvd_quotient g (O.D T) (O.D s) hg hDgT hDTs
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hcdiv : (c / g) * Nat.totient (O.D T / g) < (O.D T / g : ℕ) := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hgR).2
    simpa only [mul_comm] using hcW
  rintro ⟨R, hcap⟩
  apply no_primitive_totient_record_cap V.a V.U V.D V.increasing V.a_pos V.U_pos V.D_pos
    V.U_step V.D_step hred V.lower V.record_bound V.den_bound V.unbounded
    (O.D T / g) 0 hW hWold g (c / g) (div_nonneg hc hgR.le) hcdiv
  exact ⟨R, O.quotient_record_cap s g hg hUg hDg hs c R hcap⟩

/-- Exact extended-real version of the full stable-gcd lower bound. -/
theorem RecordGrowthOrbit.stable_totient_le_recordTheta (O : RecordGrowthOrbit)
    (N g : ℕ) (hg : 0 < g)
    (hstable : ∀ n, N ≤ n → Nat.gcd (O.U n) (O.D n) = g)
    (T : ℕ) (hNT : N ≤ T) (hW : 1 < O.D T / g) :
    (((g : ℝ) * (O.D T / g : ℕ) / Nat.totient (O.D T / g) : ℝ) : EReal) ≤
      recordTheta O.U := by
  apply ereal_le_of_all_real_lt
  intro c hc
  by_cases hc0 : 0 ≤ c
  · have hphi : (0 : ℝ) < Nat.totient (O.D T / g) := by
      exact_mod_cast Nat.totient_pos.mpr (show 0 < O.D T / g by omega)
    have hcap := O.no_stable_totient_cap N g hg hstable T hNT hW c hc0
      ((lt_div_iff₀ hphi).mp hc)
    exact ereal_le_limsup_of_cofinal_lt (recordLogLogCharge O.U) c
      (cofinal_charge_of_no_record_cap O.U c hcap)
  · exact (by exact_mod_cast (lt_of_not_ge hc0).le : (c : EReal) ≤ 0).trans
      (recordTheta_nonneg O.U)

/-- On a stable-gcd tail the primitive denominator is eventually greater than one. -/
theorem RecordGrowthOrbit.late_primitive_denominator_gt_one (O : RecordGrowthOrbit)
    (N g : ℕ) (hg : 0 < g)
    (hstable : ∀ n, N ≤ n → Nat.gcd (O.U n) (O.D n) = g) :
    ∀ T : ℕ, N + 2 ≤ T → 1 < O.D T / g := by
  intro T hT
  have hgN : g ∣ O.D N := by rw [← hstable N le_rfl]; exact Nat.gcd_dvd_right _ _
  have hgDN : g ≤ O.D N := Nat.le_of_dvd (O.D_pos N) hgN
  have ha2 : 2 ≤ O.a (N + 1) := by
    have h := O.increasing (show 0 < N + 1 by omega)
    have hp := O.a_pos 0
    omega
  have hDN : O.D N ≤ O.D (N + 1) := by
    rw [O.D_step]
    simpa only [one_mul] using Nat.mul_le_mul_right (O.D N)
      (show 1 ≤ O.a N by have := O.a_pos N; omega)
  have hDN2 : 2 * g ≤ O.D (N + 2) := by
    rw [show N + 2 = (N + 1) + 1 by omega, O.D_step]
    exact Nat.mul_le_mul ha2 (hgDN.trans hDN)
  have hdiv : O.D (N + 2) ∣ O.D T := dvd_denState_of_le O.a O.D 0
    (O.D (N + 2)) (N + 2) (fun n _ ↦ O.D_step n) (Nat.zero_le _)
    (dvd_refl _) T hT
  have hlarge : 2 * g ≤ O.D T := hDN2.trans (Nat.le_of_dvd (O.D_pos T) hdiv)
  have hgT : g ∣ O.D T := by rw [← hstable T (by omega)]; exact Nat.gcd_dvd_right _ _
  have heq := Nat.mul_div_cancel' hgT
  have ht : 2 ≤ O.D T / g := by
    by_contra h
    have hsmall : O.D T / g ≤ 1 := by omega
    have hm := Nat.mul_le_mul_left g hsmall
    nlinarith
  omega

/-- Both nonterminating arithmetic alternatives, with the every-late-index quantifier. -/
theorem RecordGrowthOrbit.quantitative_dichotomy (O : RecordGrowthOrbit) :
    ((∀ B : ℕ, ∃ n, B < Nat.gcd (O.U n) (O.D n)) ∧ recordTheta O.U = ⊤) ∨
    ∃ N g : ℕ, 0 < g ∧
      (∀ n, N ≤ n → Nat.gcd (O.U n) (O.D n) = g) ∧
      (∀ T : ℕ, N + 2 ≤ T →
        (((g : ℝ) * (O.D T / g : ℕ) / Nat.totient (O.D T / g) : ℝ) : EReal) ≤
          recordTheta O.U) ∧ (g : EReal) < recordTheta O.U := by
  classical
  by_cases hb : ∃ B : ℕ, ∀ n, Nat.gcd (O.U n) (O.D n) ≤ B
  · obtain ⟨B, hB⟩ := hb
    obtain ⟨N, hN⟩ := dvdChain_eventuallyConstant_of_cofinally_bounded
      (fun n ↦ Nat.gcd (O.U n) (O.D n)) B
      (fun n ↦ Nat.gcd_pos_of_pos_left _ (O.U_pos n))
      (fun n ↦ tailGcd_dvd_succ _ _ _ _ _ (O.U_step n) (O.D_step n))
      (fun n ↦ ⟨n, le_rfl, hB n⟩)
    let g := Nat.gcd (O.U N) (O.D N)
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (O.U_pos N)
    have hstable : ∀ n, N ≤ n → Nat.gcd (O.U n) (O.D n) = g := hN
    have hbound : ∀ T : ℕ, N + 2 ≤ T →
        (((g : ℝ) * (O.D T / g : ℕ) / Nat.totient (O.D T / g) : ℝ) : EReal) ≤
          recordTheta O.U := fun T hT ↦ O.stable_totient_le_recordTheta N g hg hstable
            T (by omega) (O.late_primitive_denominator_gt_one N g hg hstable T hT)
    right
    refine ⟨N, g, hg, hstable, hbound, ?_⟩
    let W := O.D (N + 2) / g
    have hW : 1 < W := O.late_primitive_denominator_gt_one N g hg hstable (N + 2) le_rfl
    have hphi : (0 : ℝ) < Nat.totient W := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < W)
    have hstrict : (g : ℝ) < (g : ℝ) * W / Nat.totient W := by
      apply (lt_div_iff₀ hphi).2
      have ht : (Nat.totient W : ℝ) < W := by exact_mod_cast Nat.totient_lt W hW
      exact mul_lt_mul_of_pos_left ht (by exact_mod_cast hg)
    exact (by exact_mod_cast hstrict).trans_le (hbound (N + 2) le_rfl)
  · have hunbounded : ∀ B : ℕ, ∃ n, B < Nat.gcd (O.U n) (O.D n) := by
      intro B
      by_contra h
      apply hb
      exact ⟨B, fun n ↦ le_of_not_gt (fun hn ↦ h ⟨n, hn⟩)⟩
    exact Or.inl ⟨hunbounded, O.recordTheta_eq_top_of_unbounded_gcd hunbounded⟩

/-- Bounded original numerator gives exactly zero record limsup. -/
theorem recordTheta_eq_zero_of_bounded (U : ℕ → ℕ)
    (hb : ∃ H : ℕ, ∀ n, U n ≤ H) : recordTheta U = 0 := by
  obtain ⟨N, hN⟩ := eventually_no_records_of_bounded U hb
  have heq : (fun n ↦ (recordLogLogCharge U n : EReal)) =ᶠ[atTop] fun _ ↦ 0 := by
    apply eventually_atTop.2
    refine ⟨N, fun n hn ↦ ?_⟩
    have hnnew : ¬ runningMax U n < U (n + 1) := by
      intro h
      apply hN n hn
      intro i hi
      exact (le_runningMax U hi).trans_lt h
    have hg : U (n + 1) - runningMax U n = 0 := Nat.sub_eq_zero_of_le (le_of_not_gt hnnew)
    simp only [recordLogLogCharge, runningMax_true_increment, hg, Nat.cast_zero,
      zero_div, EReal.coe_zero]
  unfold recordTheta
  rw [limsup_congr heq]
  simp

/-- Canonical eventual Sylvester recursion gives a bounded original numerator. -/
theorem canonical_bounded_of_eventual_sylvester
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hrec : ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    ∃ H : ℕ, ∀ n, canonicalNaturalNumerator a p q n ≤ H := by
  obtain ⟨Nr, hNr⟩ := hrec
  obtain ⟨Na, hNa⟩ := strictMono_eventually_ge_two a ha hapos
  let N := max Nr Na
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  obtain ⟨hCpos, hDpos, hC, hD, hrep⟩ := canonical_integer_tail a hapos p q hq hs
  have htail := realTail_eq_of_eventual_sylvester a ha hapos hs.summable N
    (fun n hn ↦ hNa n ((le_max_right Nr Na).trans hn))
    (fun n hn ↦ hNr n ((le_max_left Nr Na).trans hn))
  apply bounded_of_eventually_nonincreasing C
  refine ⟨N, fun n hn ↦ ?_⟩
  have hr := hrep n
  rw [htail n hn] at hr
  have haR : (1 : ℝ) < a n := by
    exact_mod_cast (show 1 < a n by have := hNa n ((le_max_right Nr Na).trans hn); omega)
  have hden : (a n : ℝ) - 1 ≠ 0 := by linarith
  have hm : ((a n : ℝ) - 1) * (C n : ℝ) = (D n : ℝ) := by
    rw [hr]
    field_simp [hden]
    ring
  have hstep : (C (n + 1) : ℝ) + D n = (a n : ℝ) * C n := by exact_mod_cast hC n
  have heq : (C (n + 1) : ℝ) = C n := by nlinarith
  exact_mod_cast heq.le

/-- The literal zero-versus-strictly-above-one dichotomy, including terminating tails. -/
theorem canonical_recordTheta_zero_or_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)) :
    recordTheta (canonicalNaturalNumerator a p q) = 0 ∨
      (1 : EReal) < recordTheta (canonicalNaturalNumerator a p q) := by
  by_cases hrec : ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)
  · exact Or.inl (recordTheta_eq_zero_of_bounded _
      (canonical_bounded_of_eventual_sylvester a ha hapos p q hq hs hrec))
  · exact Or.inr (canonical_recordTheta_gt_one a ha hapos p q hq hs hgrowth hrec)

/-- Zero record limsup is equivalent to eventual Sylvester recursion under the original hypotheses. -/
theorem canonical_recordTheta_eq_zero_iff
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)) :
    recordTheta (canonicalNaturalNumerator a p q) = 0 ↔
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  constructor
  · intro hz
    by_contra hnot
    have hh := canonical_recordTheta_gt_one a ha hapos p q hq hs hgrowth hnot
    rw [hz] at hh
    norm_num at hh
  · intro hrec
    exact recordTheta_eq_zero_of_bounded _
      (canonical_bounded_of_eventual_sylvester a ha hapos p q hq hs hrec)

/-- The complete quantitative statement on the actual canonical orbit. -/
theorem canonical_quantitative_record_dichotomy
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    ((∀ B : ℕ, ∃ n, B < Nat.gcd (C n) (D n)) ∧ recordTheta C = ⊤) ∨
    ∃ N g : ℕ, 0 < g ∧ (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
      (∀ T : ℕ, N + 2 ≤ T →
        (((g : ℝ) * (D T / g : ℕ) / Nat.totient (D T / g) : ℝ) : EReal) ≤ recordTheta C) ∧
      (g : EReal) < recordTheta C :=
  (canonicalRecordGrowthOrbit a ha hapos p q hq hs hgrowth hnot).quantitative_dichotomy

end ErdosProblems.Erdos243.PaperCompleteR11
