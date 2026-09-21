import ErdosProblems.Erdos243.PaperCompleteR11.CubicRationalScale
import ErdosProblems.Erdos243.PaperCompleteR11.CubicModularDensity
import ErdosProblems.Erdos243.PaperCompleteR11.CubicFieldCoordinates
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Complete rational-root classification for unit-constant cubic profiles

Authored proof candidates, UNRUN. For m > 0 and c = ±1, a rational root of
m*(X^3-X)+6*c forces m = 1 or m = 16. The reduced numerator and denominator
are constructed from the root. The resulting entire reducible unit branch
has exceptional lower density at least 1/5, by the existing explicit prime.
The unit premise is retained: it is NOT inferred from a positive-density bound.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- The difference of squares of distinct positive integer coordinates is
at least their sum. This formulation also handles a zero smaller coordinate. -/
theorem nat_square_difference_ge_sum (s t : ℕ) (hst : s < t) :
    s + t ≤ t ^ 2 - s ^ 2 := by
  have hle : s ≤ t := Nat.le_of_lt hst
  have hpow : s ^ 2 ≤ t ^ 2 := by nlinarith
  have hid : (t - s) * (s + t) + s ^ 2 = t ^ 2 := by
    calc
      (t - s) * (s + t) + s ^ 2 = (t - s) * t + s * (t - s + s) := by ring
      _ = (t - s) * t + s * t := by rw [Nat.sub_add_cancel hle]
      _ = (t - s + s) * t := by ring
      _ = t ^ 2 := by rw [Nat.sub_add_cancel hle]; ring
  have hdiff : (t - s) * (s + t) = t ^ 2 - s ^ 2 := by omega
  have hh := Nat.mul_le_mul_right (s + t) (show 1 ≤ t - s by omega)
  simpa only [one_mul, hdiff] using hh

/-- The coprime denominator leaves a divisor of six, on either side of one. -/
theorem unit_cubic_root_difference_dvd_six
    (m s t : ℕ) (hcop : Nat.Coprime s t)
    (heq : (s < t ∧ m * s * (t ^ 2 - s ^ 2) = 6 * t ^ 3) ∨
      (t < s ∧ m * s * (s ^ 2 - t ^ 2) = 6 * t ^ 3)) :
    (s < t ∧ s * (t ^ 2 - s ^ 2) ∣ 6) ∨
      (t < s ∧ s * (s ^ 2 - t ^ 2) ∣ 6) := by
  have hpow : Nat.Coprime (s ^ 2) (t ^ 2) := (hcop.pow_left 2).pow_right 2
  have ht : t ∣ t ^ 2 := ⟨t, by ring⟩
  rcases heq with ⟨hlt, heq⟩ | ⟨hlt, heq⟩
  · left
    refine ⟨hlt, ?_⟩
    have hle : s ^ 2 ≤ t ^ 2 := by nlinarith
    have hd : Nat.Coprime (t ^ 2 - s ^ 2) (t ^ 2) :=
      (Nat.coprime_self_sub_left hle).mpr hpow
    have hc : Nat.Coprime (s * (t ^ 2 - s ^ 2)) (t ^ 3) :=
      (Nat.coprime_mul_iff_left.mpr ⟨hcop, hd.coprime_dvd_right ht⟩).pow_right 3
    apply hc.dvd_of_dvd_mul_right
    refine ⟨m, ?_⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using heq.symm
  · right
    refine ⟨hlt, ?_⟩
    have hle : t ^ 2 ≤ s ^ 2 := by nlinarith
    have hd : Nat.Coprime (s ^ 2 - t ^ 2) (t ^ 2) :=
      (Nat.coprime_sub_self_left hle).mpr hpow
    have hc : Nat.Coprime (s * (s ^ 2 - t ^ 2)) (t ^ 3) :=
      (Nat.coprime_mul_iff_left.mpr ⟨hcop, hd.coprime_dvd_right ht⟩).pow_right 3
    apply hc.dvd_of_dvd_mul_right
    refine ⟨m, ?_⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using heq.symm

/-- The complete finite integer end of the rational-root argument. -/
theorem unit_cubic_root_nat_classification
    (m s t : ℕ) (hs : 0 < s) (ht : 0 < t) (hcop : Nat.Coprime s t)
    (heq : (s < t ∧ m * s * (t ^ 2 - s ^ 2) = 6 * t ^ 3) ∨
      (t < s ∧ m * s * (s ^ 2 - t ^ 2) = 6 * t ^ 3)) :
    (s = 1 ∧ t = 2 ∧ m = 16) ∨ (s = 2 ∧ t = 1 ∧ m = 1) := by
  have hd := unit_cubic_root_difference_dvd_six m s t hcop heq
  rcases hd with ⟨hlt, hd⟩ | ⟨hlt, hd⟩
  · have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
    have hgap := nat_square_difference_ge_sum s t hlt
    have hs1 : s = 1 := by
      by_contra h
      have hs2 : 2 ≤ s := by omega
      have hgap5 : 5 ≤ t ^ 2 - s ^ 2 := by omega
      have hh := Nat.mul_le_mul hs2 hgap5
      omega
    have ht2 : t = 2 := by
      subst s
      have htge : 2 ≤ t := by omega
      have hpow : 1 ≤ t ^ 2 := by nlinarith
      have hsub := Nat.sub_add_cancel hpow
      norm_num at hb hsub
      by_contra h
      have hge : 3 ≤ t := by omega
      have hh := Nat.mul_le_mul hge hge
      nlinarith
    left
    refine ⟨hs1, ht2, ?_⟩
    rcases heq with ⟨_, hh⟩ | ⟨hh, _⟩
    · rw [hs1, ht2] at hh
      norm_num at hh
      omega
    · omega
  · have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
    have hgap := nat_square_difference_ge_sum t s hlt
    have hs2 : s ≤ 2 := by
      by_contra h
      have hs3 : 3 ≤ s := by omega
      have hgap4 : 4 ≤ s ^ 2 - t ^ 2 := by omega
      have hh := Nat.mul_le_mul hs3 hgap4
      omega
    have hsEq : s = 2 := by omega
    have htEq : t = 1 := by omega
    right
    refine ⟨hsEq, htEq, ?_⟩
    rcases heq with ⟨hh, _⟩ | ⟨_, hh⟩
    · omega
    · rw [hsEq, htEq] at hh
      norm_num at hh
      omega

/-- Actual root reduction gives the two exact natural-number equations. -/
theorem unit_cubic_rational_root_clearing
    (m : ℕ) (c r : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (hroot : (m : ℚ) * (r ^ 3 - r) + 6 * c = 0) :
    (r.num.natAbs < r.den ∧
      m * r.num.natAbs * (r.den ^ 2 - r.num.natAbs ^ 2) = 6 * r.den ^ 3) ∨
    (r.den < r.num.natAbs ∧
      m * r.num.natAbs * (r.num.natAbs ^ 2 - r.den ^ 2) = 6 * r.den ^ 3) := by
  have hr : r ≠ 0 := by
    intro hz
    rw [hz] at hroot
    rcases hc with rfl | rfl <;> norm_num at hroot
  obtain ⟨hs, ht, _, habs⟩ := rational_abs_reduced_positive r hr
  have hmR : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have htR : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast ht
  have ht0 : (r.den : ℚ) ≠ 0 := ne_of_gt htR
  have hcabs : |c| = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hfac : (m : ℚ) * r * (r ^ 2 - 1) = -6 * c := by
    linear_combination hroot
  have hA : (m : ℚ) * |r| * |(|r| ^ 2 - 1)| = 6 := by
    calc
      (m : ℚ) * |r| * |(|r| ^ 2 - 1)| = |(m : ℚ) * r * (r ^ 2 - 1)| := by
        rw [abs_mul, abs_mul, abs_of_pos hmR, sq_abs]
      _ = |-6 * c| := congrArg abs hfac
      _ = 6 := by rw [abs_mul, hcabs]; norm_num
  rw [habs] at hA
  have hne : r.num.natAbs ≠ r.den := by
    intro heq
    rw [heq, div_self ht0] at hA
    norm_num at hA
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · left
    refine ⟨hlt, ?_⟩
    have hpow : r.num.natAbs ^ 2 ≤ r.den ^ 2 := by nlinarith
    have hpowR : (r.num.natAbs : ℚ) ^ 2 ≤ (r.den : ℚ) ^ 2 := by exact_mod_cast hpow
    have hsq : ((r.num.natAbs : ℚ) / (r.den : ℚ)) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_iff₀ (sq_pos_of_pos htR)]
      simpa using hpowR
    have habsdiff : |((r.num.natAbs : ℚ) / (r.den : ℚ)) ^ 2 - 1| =
        ((r.den ^ 2 - r.num.natAbs ^ 2 : ℕ) : ℚ) / (r.den : ℚ) ^ 2 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hsq), Nat.cast_sub hpow]
      push_cast
      field_simp [ht0]
      <;> ring
    rw [habsdiff] at hA
    have hQ : (m : ℚ) * (r.num.natAbs : ℚ) *
        ((r.den ^ 2 - r.num.natAbs ^ 2 : ℕ) : ℚ) = 6 * (r.den : ℚ) ^ 3 := by
      field_simp [ht0] at hA
      nlinarith [hA]
    exact_mod_cast hQ
  · right
    refine ⟨hlt, ?_⟩
    have hpow : r.den ^ 2 ≤ r.num.natAbs ^ 2 := by nlinarith
    have hpowR : (r.den : ℚ) ^ 2 ≤ (r.num.natAbs : ℚ) ^ 2 := by exact_mod_cast hpow
    have hsq : 1 ≤ ((r.num.natAbs : ℚ) / (r.den : ℚ)) ^ 2 := by
      rw [div_pow, le_div_iff₀ (sq_pos_of_pos htR)]
      simpa using hpowR
    have habsdiff : |((r.num.natAbs : ℚ) / (r.den : ℚ)) ^ 2 - 1| =
        ((r.num.natAbs ^ 2 - r.den ^ 2 : ℕ) : ℚ) / (r.den : ℚ) ^ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsq), Nat.cast_sub hpow]
      push_cast
      field_simp [ht0]
      <;> ring
    rw [habsdiff] at hA
    have hQ : (m : ℚ) * (r.num.natAbs : ℚ) *
        ((r.num.natAbs ^ 2 - r.den ^ 2 : ℕ) : ℚ) = 6 * (r.den : ℚ) ^ 3 := by
      field_simp [ht0] at hA
      nlinarith [hA]
    exact_mod_cast hQ

/-- A root of a positive-scale, unit-constant cubic forces precisely these
scales; no reducibility classification is supplied as an assumption. -/
theorem unit_cubic_rational_root_scale
    (m : ℕ) (c r : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (hroot : (m : ℚ) * (r ^ 3 - r) + 6 * c = 0) : m = 1 ∨ m = 16 := by
  have hr : r ≠ 0 := by
    intro hz
    rw [hz] at hroot
    rcases hc with rfl | rfl <;> norm_num at hroot
  obtain ⟨hs, ht, hcop, _⟩ := rational_abs_reduced_positive r hr
  have h := unit_cubic_root_nat_classification m r.num.natAbs r.den hs ht hcop
    (unit_cubic_rational_root_clearing m c r hm hc hroot)
  rcases h with ⟨_, _, hh⟩ | ⟨_, _, hh⟩
  · exact Or.inr hh
  · exact Or.inl hh

/-- Both exceptional scales really have rational roots, for either sign. -/
theorem unit_cubic_exists_rational_root_iff
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1) :
    (∃ r : ℚ, (m : ℚ) * (r ^ 3 - r) + 6 * c = 0) ↔ m = 1 ∨ m = 16 := by
  constructor
  · rintro ⟨r, hr⟩
    exact unit_cubic_rational_root_scale m c r hm hc hr
  · intro hh
    rcases hh with rfl | rfl <;> rcases hc with rfl | rfl
    · exact ⟨-2, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨1 / 2, by norm_num⟩
    · exact ⟨-1 / 2, by norm_num⟩

/-- Irreducibility outside the two completely classified root scales. -/
theorem unit_cubic_irreducible_of_scale
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (hm1 : m ≠ 1) (hm16 : m ≠ 16) :
    Irreducible (cubicScalePolynomial (6 * c / (m : ℚ))) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp only [cubicScalePolynomial_natDegree, Finset.mem_Icc]
    omega
  · intro r hr
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    have hroot : (m : ℚ) * (r ^ 3 - r) + 6 * c = 0 := by
      have hh : r ^ 3 - r + 6 * c / (m : ℚ) = 0 := by
        simpa [Polynomial.IsRoot.def, cubicScalePolynomial] using hr
      field_simp [hm0] at hh
      linear_combination hh
    exact (unit_cubic_rational_root_scale m c r hm hc hroot).elim hm1 hm16

/-- Entire rational-root unit branch, with a strictly stronger density bound
than 1/28 and with no global prime-existence hypothesis. -/
theorem integral_cubic_unit_rational_root_density
    (a u v : ℕ → ℤ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ℚ) (hroot : (m : ℚ) * (r ^ 3 - r) + 6 * (c : ℚ) = 0) :
    LowerDensityAtLeast {n : ℕ | u n ≠ (m : ℤ) * risingBinomial n + c} (1 / 5) := by
  have hcQ : (c : ℚ) = 1 ∨ (c : ℚ) = -1 := by
    rcases hc with rfl | rfl <;> norm_num
  have hmcase := unit_cubic_rational_root_scale m (c : ℚ) r hm hcQ hroot
  apply integral_cubic_mod_five_density a u v (m : ℤ) c T hnum hden
  · rcases hmcase with rfl | rfl <;> decide
  · rcases hmcase with rfl | rfl <;> rcases hc with rfl | rfl <;> decide

/-- A positive-scale integral unit profile below the fixed threshold must be
irreducible. This does not use the zero-density argument for its unit premise. -/
theorem integral_cubic_unit_irreducible_below_uniform
    (a u v : ℕ → ℤ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | u n ≠ (m : ℤ) * risingBinomial n + c}
      (1 / 28)) :
    Irreducible (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))) := by
  have hnroot : ¬ ∃ r : ℚ, (m : ℚ) * (r ^ 3 - r) + 6 * (c : ℚ) = 0 := by
    rintro ⟨r, hr⟩
    exact hlow ((integral_cubic_unit_rational_root_density a u v m c T hm hc
      hnum hden r hr).mono_bound (by norm_num))
  have hcQ : (c : ℚ) = 1 ∨ (c : ℚ) = -1 := by
    rcases hc with rfl | rfl <;> norm_num
  have hcase : ¬ (m = 1 ∨ m = 16) :=
    fun hh ↦ hnroot ((unit_cubic_exists_rational_root_iff m (c : ℚ) hm hcQ).mpr hh)
  exact unit_cubic_irreducible_of_scale m (c : ℚ) hm hcQ
    (fun hh ↦ hcase (Or.inl hh)) (fun hh ↦ hcase (Or.inr hh))

/-- The literal unshifted polynomial printed as Q_{m,c} in the paper. -/
noncomputable def rationalBinomialCubic (m c : ℚ) : Polynomial ℚ :=
  Polynomial.C (m / 6) * Polynomial.X * (Polynomial.X + 1) *
    (Polynomial.X + 2) + Polynomial.C c

/-- Nonzero scale gives the literal paper polynomial degree three. -/
theorem rationalBinomialCubic_natDegree (m c : ℚ) (hm : m ≠ 0) :
    (rationalBinomialCubic m c).natDegree = 3 := by
  unfold rationalBinomialCubic
  compute_degree <;> norm_num [hm]

/-- A root of the literal unshifted polynomial is shifted and cleared into
exactly the equation used in the rational-root classification. -/
theorem rationalBinomialCubic_root_clearing (m c r : ℚ)
    (hr : Polynomial.IsRoot (rationalBinomialCubic m c) r) :
    m * ((r + 1) ^ 3 - (r + 1)) + 6 * c = 0 := by
  have hh : m / 6 * r * (r + 1) * (r + 2) + c = 0 := by
    simpa [Polynomial.IsRoot.def, rationalBinomialCubic] using hr
  linear_combination 6 * hh

/-- The literal Q_{m,c}, not only its centred monic associate, is irreducible
on the unit branch below the fixed threshold. -/
theorem integral_cubic_unit_unshifted_irreducible_below_uniform
    (a u v : ℕ → ℤ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | u n ≠ (m : ℤ) * risingBinomial n + c}
      (1 / 28)) :
    Irreducible (rationalBinomialCubic (m : ℚ) (c : ℚ)) := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [rationalBinomialCubic_natDegree _ _ hm0]
    decide
  · intro r hr
    have hh := rationalBinomialCubic_root_clearing (m : ℚ) (c : ℚ) r hr
    exact hlow ((integral_cubic_unit_rational_root_density a u v m c T hm hc
      hnum hden (r + 1) hh).mono_bound (by norm_num))

end ErdosProblems.Erdos243.PaperCompleteR11
