import ErdosProblems.Erdos68.PaperCompleteLowKernel
import ErdosProblems.Erdos68.PaperCompleteMomentHorizon

/-!
Exact attainable moments, finite Bezout attainment and primitive minimisers.
The endpoint uses the actual isolated-channel recurrence and its proved finite
horizon, not an assumed lattice/span supplier.  All new Lean checks are UNRUN.
-/
namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp

lemma tail_one_eq_integerEvaluation {D : ℕ} (hD : 1 ≤ D)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    channelSynthesis z 1 = integerEvaluation (fun j => channelScalar (j + 1)) z := by
  classical
  unfold channelSynthesis integerEvaluation Finsupp.sum
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjD : D ≤ j := by
    by_contra h
    have hjz := hz j (by omega)
    exact (Finsupp.mem_support_iff.mp hj) hjz
  have hj0 : j ≠ 0 := by omega
  simp [channelBasisColumn, hj0, channelScalar, Finsupp.smul_apply, smul_eq_mul]

lemma shifted_scalar_gcd_eq {D H : ℕ} (hD : 1 ≤ D) (hDH : D < H) :
    (Finset.Icc D (H - 1)).gcd (fun j => (channelScalar (j + 1)).natAbs) =
      finiteScalarGcd D H := by
  apply Nat.dvd_antisymm
  · apply (finiteScalarGcd_dvd_iff D H _).mpr
    intro n hn hnH
    have hm : n - 1 ∈ Finset.Icc D (H - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hdiv := Finset.gcd_dvd
      (f := fun j => (channelScalar (j + 1)).natAbs) hm
    have he : n - 1 + 1 = n := by omega
    dsimp only at hdiv
    rw [he] at hdiv
    exact Int.natCast_dvd.mpr hdiv
  · apply Finset.dvd_gcd
    intro j hj
    have hjD := (Finset.mem_Icc.mp hj).1
    have hjH := (Finset.mem_Icc.mp hj).2
    apply Int.natCast_dvd.mp
    exact (finiteScalarGcd_dvd_iff D H _).mp (dvd_refl _) (j + 1)
      (by omega) (by omega)

/-- An explicit finite support exists for a Bezout generator of the actual gcd. -/
theorem finite_tail_gcd_attained {D H : ℕ} (hD : 1 ≤ D) (hDH : D < H) :
    ∃ z : ℕ →₀ ℤ, TailCoordinates D z ∧
      channelSynthesis z 1 = (finiteScalarGcd D H : ℤ) ∧
      SupportedOn z (Finset.Icc D (H - 1)) := by
  obtain ⟨z, hs, he⟩ := finite_gcd_bezout (Finset.Icc D (H - 1))
    (fun j => channelScalar (j + 1))
  have hz : TailCoordinates D z := by
    intro j hj
    apply hs j
    intro hmem
    have := (Finset.mem_Icc.mp hmem).1
    omega
  refine ⟨z, hz, ?_, hs⟩
  rw [tail_one_eq_integerEvaluation hD hz, he, shifted_scalar_gcd_eq hD hDH]

lemma tail_gcd_dvd_one {D G : ℕ} (hD : 1 ≤ D)
    (hG : IsScalarTailGcd D G) {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    (G : ℤ) ∣ channelSynthesis z 1 := by
  rw [tail_one_eq_integerEvaluation hD hz]
  apply integerEvaluation_dvd
  intro j hj
  have hjD : D ≤ j := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hj) (hz j (by omega))
  exact (hG G).mp (dvd_refl G) (j + 1) (by omega)

/-- Integer combinations in the entire tail form precisely G Z. -/
theorem exists_tail_one_iff {D H : ℕ} (hD : 1 ≤ D) (hDH : D < H)
    (hG : IsScalarTailGcd D (finiteScalarGcd D H)) (q : ℤ) :
    (∃ z : ℕ →₀ ℤ, TailCoordinates D z ∧ channelSynthesis z 1 = q) ↔
      (finiteScalarGcd D H : ℤ) ∣ q := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact tail_gcd_dvd_one hD hG hz
  · rintro ⟨k, hk⟩
    obtain ⟨z, hz, he, _⟩ := finite_tail_gcd_attained hD hDH
    refine ⟨k • z, ?_, ?_⟩
    · intro j hj
      simp [Finsupp.smul_apply, hz j hj]
    · rw [channelSynthesis_smul, Finsupp.smul_apply, smul_eq_mul, he, hk]
      ring

/-- Existence on the literal coefficient domain n>=2. -/
def AttainsMoment (D : ℕ) (m : ℤ) : Prop :=
  ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧ factorialMoment f = m

lemma attainsMoment_iff_support_divisibility {D H : ℕ}
    (hD : 2 ≤ D) (hDH : D < H)
    (hG : IsScalarTailGcd D (finiteScalarGcd D H)) (m : ℤ) :
    AttainsMoment D m ↔ ∃ t : ℤ,
      m = (channelLCM D : ℤ) * t ∧ (finiteScalarGcd D H : ℤ) ∣ t * kernelOne D := by
  constructor
  · rintro ⟨f, hf, hc, hm⟩
    obtain ⟨t, z, hz, he⟩ :=
      (low_channel_classification hD f ((admissible_iff f).mp hf).1).mp hc
    have hsupport : t * kernelOne D + channelSynthesis z 1 = 0 :=
      support_equation.mp (he ▸ hf)
    have hdiv := tail_gcd_dvd_one (by omega) hG hz
    refine ⟨t, ?_, ?_⟩
    · rw [he, factorialMoment_add, factorialMoment_smul, canonicalKernel_moment,
        tail_moment (by omega) hz, add_zero] at hm
      nlinarith [hm]
    · have hneg : t * kernelOne D = -channelSynthesis z 1 := by omega
      rw [hneg]
      exact dvd_neg.mpr hdiv
  · rintro ⟨t, hm, hdiv⟩
    obtain ⟨z, hz, he⟩ := (exists_tail_one_iff (by omega) hDH hG
      (-(t * kernelOne D))).mpr (dvd_neg.mpr hdiv)
    let f := t • canonicalKernel D + channelSynthesis z
    refine ⟨f, ?_, ?_, ?_⟩
    · apply support_equation.mpr
      rw [he]
      ring
    · have hf0 : f 0 = 0 := by
        simp [f, Finsupp.add_apply, Finsupp.smul_apply,
          canonicalKernel_at_zero, synthesis_at_zero]
      exact (low_channel_classification hD f hf0).mpr ⟨t, z, hz, rfl⟩
    · dsimp [f]
      rw [factorialMoment_add, factorialMoment_smul, canonicalKernel_moment,
        tail_moment (by omega) hz, add_zero, hm]
      ring

noncomputable def minimumMoment (D p : ℕ) : ℤ :=
  let G : ℤ := finiteScalarGcd D (D * (2 * p - 1))
  (channelLCM D : ℤ) * (G / (Int.gcd G (kernelOne D) : ℤ))

/-- Exact ideal formula, with the paper's actual finite horizon substituted. -/
theorem attainable_moment_ideal {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) (m : ℤ) :
    AttainsMoment D m ↔ minimumMoment D p ∣ m := by
  let H := D * (2 * p - 1)
  have hcert := finite_channel_moment_certificate hD hp hDp hpD
  have hDH : D < H := by
    have hp2 := hp.two_le
    have hp3 : 3 ≤ 2 * p - 1 := by omega
    dsimp [H]
    calc
      D < D * 3 := by omega
      _ ≤ D * (2 * p - 1) := Nat.mul_le_mul_left D hp3
  have hg : (0 : ℤ) < finiteScalarGcd D H := by exact_mod_cast hcert.1
  rw [attainsMoment_iff_support_divisibility hD hDH hcert.2.1]
  change (∃ t : ℤ, m = (channelLCM D : ℤ) * t ∧
    (finiteScalarGcd D H : ℤ) ∣ t * kernelOne D) ↔
    (channelLCM D : ℤ) * ((finiteScalarGcd D H : ℤ) /
      (Int.gcd (finiteScalarGcd D H : ℤ) (kernelOne D) : ℤ)) ∣ m
  constructor
  · rintro ⟨t, hm, ht⟩
    obtain ⟨k, hk⟩ := (gcd_quotient_dvd_iff _ _ t hg).mpr ht
    refine ⟨k, ?_⟩
    rw [hm, hk]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨((finiteScalarGcd D H : ℤ) /
      (Int.gcd (finiteScalarGcd D H : ℤ) (kernelOne D) : ℤ)) * k, ?_, ?_⟩
    · rw [hk]
      ring
    · exact (gcd_quotient_dvd_iff _ _ _ hg).mp (dvd_mul_right _ _)

lemma minimumMoment_pos {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p := by
  have hcert := finite_channel_moment_certificate hD hp hDp hpD
  unfold minimumMoment
  apply mul_pos
  · exact_mod_cast local_channelLCM_pos D
  · apply gcd_quotient_pos
    exact_mod_cast hcert.1

/-- The positive generator is attained, rather than just a necessary divisor. -/
theorem minimumMoment_attained {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    AttainsMoment D (minimumMoment D p) :=
  (attainable_moment_ideal hD hp hDp hpD _).mpr (dvd_refl _)

theorem minimum_positive_moment {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    {m : ℤ} (hm : AttainsMoment D m) (hpos : 0 < m) : minimumMoment D p ≤ m := by
  obtain ⟨k, hk⟩ := (attainable_moment_ideal hD hp hDp hpD m).mp hm
  have hmu := minimumMoment_pos hD hp hDp hpD
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k ≤ 0 := by omega
    have hz := mul_nonpos_of_nonneg_of_nonpos hmu.le hk0
    omega
  calc
    minimumMoment D p = minimumMoment D p * 1 := by ring
    _ ≤ minimumMoment D p * k := mul_le_mul_of_nonneg_left hkpos hmu.le
    _ = m := hk.symm

/-- For a nonzero finite integer vector this is equivalent to coefficient content 1. -/
def PrimitiveVector (f : ℕ →₀ ℤ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ¬ ∃ g : ℕ →₀ ℤ, f = (k : ℤ) • g

/-- Every vector attaining the least positive moment is primitive. -/
theorem minimum_moment_vector_primitive {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    {f : ℕ →₀ ℤ} (hf : Admissible f) (hc : LowChannels D f)
    (hm : factorialMoment f = minimumMoment D p) : PrimitiveVector f := by
  intro k hk
  rintro ⟨g, he⟩
  have hkZ : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℤ) ≠ 0 := by omega
  have hf01 := (admissible_iff f).mp hf
  have hg : Admissible g := by
    apply (admissible_iff g).mpr
    constructor
    · have hz : (k : ℤ) * g 0 = 0 := by
        simpa [he, Finsupp.smul_apply, smul_eq_mul] using hf01.1
      exact (mul_eq_zero.mp hz).resolve_left hk0
    · have hz : (k : ℤ) * g 1 = 0 := by
        simpa [he, Finsupp.smul_apply, smul_eq_mul] using hf01.2
      exact (mul_eq_zero.mp hz).resolve_left hk0
  have hgc : LowChannels D g := by
    intro d hd
    have hz := hc d hd
    rw [he, channelNumerator_smul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hk0
  rw [he, factorialMoment_smul] at hm
  have hmu := minimumMoment_pos hD hp hDp hpD
  have hgm : 0 < factorialMoment g := by
    by_contra h
    have hz := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ k by omega)
      (show factorialMoment g ≤ 0 by omega)
    omega
  have hmin := minimum_positive_moment hD hp hDp hpD
    (show AttainsMoment D (factorialMoment g) from ⟨g, hg, hgc, rfl⟩) hgm
  have hkMul := mul_le_mul_of_nonneg_right hkZ hgm.le
  nlinarith [hm, hkMul]

/-- One endpoint packages positivity, the exact ideal and primitive attainment. -/
theorem exact_moment_ideal_with_primitive_attainment {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p ∧
    (∀ m : ℤ, AttainsMoment D m ↔ minimumMoment D p ∣ m) ∧
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ PrimitiveVector f := by
  obtain ⟨f, hf, hc, hm⟩ := minimumMoment_attained hD hp hDp hpD
  exact ⟨minimumMoment_pos hD hp hDp hpD,
    attainable_moment_ideal hD hp hDp hpD,
    f, hf, hc, hm, minimum_moment_vector_primitive hD hp hDp hpD hf hc hm⟩

/-- Literal coefficient content, including the empty-vector convention gcd(empty)=0. -/
noncomputable def coefficientContent (f : ℕ →₀ ℤ) : ℕ :=
  f.support.gcd (fun n => (f n).natAbs)

lemma coefficientContent_dvd (f : ℕ →₀ ℤ) (n : ℕ) :
    (coefficientContent f : ℤ) ∣ f n := by
  classical
  by_cases hn : f n = 0
  · rw [hn]
    exact dvd_zero _
  · exact Int.natCast_dvd.mpr
      (Finset.gcd_dvd (f := fun j => (f j).natAbs) (Finsupp.mem_support_iff.mpr hn))

lemma coefficientContent_pos {f : ℕ →₀ ℤ} (hf : f ≠ 0) :
    0 < coefficientContent f := by
  by_contra h
  have hc : coefficientContent f = 0 := by omega
  apply hf
  ext n
  have hd := coefficientContent_dvd f n
  rw [hc, Nat.cast_zero, zero_dvd_iff] at hd
  simpa using hd

/-- The no-dilation definition of primitive is exactly content one for nonzero vectors. -/
theorem primitive_iff_content_one {f : ℕ →₀ ℤ} (hf : f ≠ 0) :
    PrimitiveVector f ↔ coefficientContent f = 1 := by
  classical
  constructor
  · intro hp
    have hcpos := coefficientContent_pos hf
    by_contra hne
    have hc2 : 2 ≤ coefficientContent f := by omega
    let g : ℕ →₀ ℤ := Finsupp.mapRange
      (fun z : ℤ => z / (coefficientContent f : ℤ)) (by simp) f
    apply hp (coefficientContent f) hc2
    refine ⟨g, ?_⟩
    ext n
    simp only [Finsupp.smul_apply, smul_eq_mul]
    change f n = (coefficientContent f : ℤ) *
      (f n / (coefficientContent f : ℤ))
    exact (Int.mul_ediv_cancel' (coefficientContent_dvd f n)).symm
  · intro hc k hk
    rintro ⟨g, he⟩
    have hd : k ∣ coefficientContent f := by
      apply Finset.dvd_gcd
      intro n hn
      apply Int.natCast_dvd.mp
      refine ⟨g n, ?_⟩
      simp [he, Finsupp.smul_apply, smul_eq_mul]
    rw [hc] at hd
    have hkle := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hd
    omega

/-- Least moment and literal coefficient content one, without a primitiveness convention. -/
theorem minimum_moment_content_one {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ coefficientContent f = 1 := by
  obtain ⟨f, hf, hc, hm⟩ := minimumMoment_attained hD hp hDp hpD
  have hfne : f ≠ 0 := by
    intro hz
    rw [hz, factorialMoment_zero] at hm
    have := minimumMoment_pos hD hp hDp hpD
    omega
  exact ⟨f, hf, hc, hm, (primitive_iff_content_one hfne).mp
    (minimum_moment_vector_primitive hD hp hDp hpD hf hc hm)⟩

/-- A different admissible Bertrand prime gives the same positive generator. -/
theorem minimumMoment_independent_prime {D p q : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hq : q.Prime) (hDq : D / 2 < q) (hqD : q ≤ D) :
    minimumMoment D p = minimumMoment D q := by
  apply le_antisymm
  · exact minimum_positive_moment hD hp hDp hpD
      (minimumMoment_attained hD hq hDq hqD) (minimumMoment_pos hD hq hDq hqD)
  · exact minimum_positive_moment hD hq hDq hqD
      (minimumMoment_attained hD hp hDp hpD) (minimumMoment_pos hD hp hDp hpD)

end ErdosProblems.Erdos68.PaperComplete
