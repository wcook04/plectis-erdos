import ErdosProblems.Erdos243.PaperCompleteR11.CubicPrimitiveNormalisation
import ErdosProblems.Erdos243.PaperCompleteR11.CubicRationalRoots
import ErdosProblems.Erdos243.PaperCompleteR11.CubicZeroDensityShape

/-!
# The full primitive multiplier supply

Authored proof candidates; Lean and actual axiom audits are UNRUN.
The prime supply in this file consists of prime factors of actual multipliers.
It is NOT a Chebotarev supply and is not substituted for one. Positivity and
the two exact state equations give all multiplier facts used in the paper.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- Positive next denominators force positive multipliers. -/
theorem primitive_multiplier_positive (a v : ℕ → ℕ) (T : ℕ)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n) :
    ∀ n, T ≤ n → 0 < a n := by
  intro n hn
  have hh := hv (n + 1) (by omega)
  rw [hden n hn] at hh
  by_contra h
  have hz : a n = 0 := by omega
  simp only [hz, zero_mul, lt_self_iff_false] at hh

/-- A common divisor of a multiplier and its denominator would divide both
coordinates at the next state, contradicting the actual primitive tail. -/
theorem primitive_multiplier_coprime_denominator
    (a u v : ℕ → ℕ) (T : ℕ)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n)) :
    ∀ n, T ≤ n → Nat.Coprime (a n) (v n) := by
  intro n hn
  let d := Nat.gcd (a n) (v n)
  have hda : d ∣ a n := Nat.gcd_dvd_left _ _
  have hdv : d ∣ v n := Nat.gcd_dvd_right _ _
  have hsum : d ∣ u (n + 1) + v n := by
    rw [hnum n hn]
    exact dvd_mul_of_dvd_left hda _
  have hdu : d ∣ u (n + 1) := (Nat.dvd_add_iff_left hdv).mpr hsum
  have hdv' : d ∣ v (n + 1) := by
    rw [hden n hn]
    exact dvd_mul_of_dvd_left hda _
  change d = 1
  exact Nat.eq_one_of_dvd_coprimes (hcop (n + 1) (by omega)) hdu hdv'

/-- Every earlier multiplier divides every later denominator, with the
original natural indices retained. -/
theorem earlier_multiplier_dvd_later_denominator
    (a v : ℕ → ℕ) (T : ℕ)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (i j : ℕ) (hi : T ≤ i) (hij : i < j) : a i ∣ v j := by
  have h : ∀ k : ℕ, a i ∣ v (i + 1 + k) := by
    intro k
    induction k with
    | zero =>
        simp only [Nat.add_zero]
        rw [hden i hi]
        exact dvd_mul_right _ _
    | succ k ih =>
        rw [show i + 1 + (k + 1) = (i + 1 + k) + 1 by omega,
          hden (i + 1 + k) (by omega)]
        exact dvd_mul_of_dvd_right ih _
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ j by omega)
  simpa only [← hk] using h k

/-- Actual multipliers at distinct primitive-tail indices are coprime. -/
theorem primitive_multipliers_pairwise_coprime
    (a u v : ℕ → ℕ) (T : ℕ)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n)) :
    ∀ i j, T ≤ i → T ≤ j → i ≠ j → Nat.Coprime (a i) (a j) := by
  intro i j hi hj hne
  have hmult := primitive_multiplier_coprime_denominator a u v T hnum hden hcop
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ((hmult j hj).coprime_dvd_right
      (earlier_multiplier_dvd_later_denominator a v T hden i j hi hlt)).symm
  · exact (hmult i hi).coprime_dvd_right
      (earlier_multiplier_dvd_later_denominator a v T hden j i hj hlt)

/-- Exact descent formula if every multiplier on a tail is one. -/
theorem multiplier_one_tail_descent
    (a u v : ℕ → ℕ) (T : ℕ)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (ha : ∀ n, T ≤ n → a n = 1) :
    ∀ k : ℕ, u (T + k) + k * v T = u T ∧ v (T + k) = v T := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : u (T + k + 1) + v T = u (T + k) := by
        simpa only [ha (T + k) (by omega), one_mul, ih.2] using
          hnum (T + k) (by omega)
      constructor
      · calc
          u (T + (k + 1)) + (k + 1) * v T =
              (u (T + k + 1) + v T) + k * v T := by
                rw [show T + (k + 1) = T + k + 1 by omega]
                ring
          _ = u (T + k) + k * v T := by rw [hstep]
          _ = u T := ih.1
      · rw [show T + (k + 1) = T + k + 1 by omega,
          hden (T + k) (by omega), ha (T + k) (by omega), one_mul, ih.2]

/-- Infinitely many actual multipliers exceed one. The argument does not
assume growth of the numerator, only positivity of the denominators. -/
theorem primitive_multiplier_arbitrarily_late_nonunit
    (a u v : ℕ → ℕ) (T : ℕ)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (N : ℕ) : ∃ n, max T N ≤ n ∧ 1 < a n := by
  by_contra h
  push_neg at h
  let S := max T N
  have ha : ∀ n, S ≤ n → a n = 1 := by
    intro n hn
    have hnT : T ≤ n := le_trans (le_max_left T N) hn
    have hpos := primitive_multiplier_positive a v T hv hden n hnT
    have hle := h n hn
    omega
  have hnumS : ∀ n, S ≤ n → u (n + 1) + v n = a n * u n :=
    fun n hn ↦ hnum n (le_trans (le_max_left T N) hn)
  have hdenS : ∀ n, S ≤ n → v (n + 1) = a n * v n :=
    fun n hn ↦ hden n (le_trans (le_max_left T N) hn)
  have hh := (multiplier_one_tail_descent a u v S hnumS hdenS ha (u S + 1)).1
  have hvS : 1 ≤ v S := hv S (le_max_left T N)
  have hb := Nat.mul_le_mul_left (u S + 1) hvS
  nlinarith

/-- For a finite initial segment of possible divisors, all occurring divisors
have a bounded-index witness. This finite bound is proved, not postulated. -/
theorem finite_multiplier_divisors_have_bounded_witnesses
    (a : ℕ → ℕ) (T B : ℕ) :
    ∃ N : ℕ, ∀ p : ℕ, p ≤ B → (∃ i, T ≤ i ∧ p ∣ a i) →
      ∃ i, T ≤ i ∧ i ≤ N ∧ p ∣ a i := by
  classical
  induction B with
  | zero =>
      by_cases h : ∃ i, T ≤ i ∧ 0 ∣ a i
      · obtain ⟨i, hi, hd⟩ := h
        refine ⟨i, ?_⟩
        intro p hp _
        have hp0 : p = 0 := by omega
        subst p
        exact ⟨i, hi, le_refl i, hd⟩
      · refine ⟨0, ?_⟩
        intro p hp he
        have hp0 : p = 0 := by omega
        subst p
        exact False.elim (h he)
  | succ B ih =>
      obtain ⟨N, hN⟩ := ih
      by_cases h : ∃ i, T ≤ i ∧ (B + 1) ∣ a i
      · obtain ⟨i, hi, hd⟩ := h
        refine ⟨max N i, ?_⟩
        intro p hp he
        by_cases hpB : p ≤ B
        · obtain ⟨j, hj, hjN, hjd⟩ := hN p hpB he
          exact ⟨j, hj, le_trans hjN (le_max_left N i), hjd⟩
        · have hpeq : p = B + 1 := by omega
          subst p
          exact ⟨i, hi, le_max_right N i, hd⟩
      · refine ⟨N, ?_⟩
        intro p hp he
        by_cases hpB : p ≤ B
        · exact hN p hpB he
        · have hpeq : p = B + 1 := by omega
          subst p
          exact False.elim (h he)

/-- Arbitrarily large distinct primes divide arbitrarily late multipliers.
Both the size bound and the index bound are independently prescribed. -/
theorem primitive_multiplier_prime_supply
    (a u v : ℕ → ℕ) (T : ℕ)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (B N : ℕ) : ∃ p j : ℕ,
      Nat.Prime p ∧ B < p ∧ max T N ≤ j ∧ p ∣ a j := by
  obtain ⟨K, hK⟩ := finite_multiplier_divisors_have_bounded_witnesses a T B
  obtain ⟨j, hj, hunit⟩ := primitive_multiplier_arbitrarily_late_nonunit a u v T hv
    hnum hden (max N (K + 1))
  have hjT : T ≤ j := le_trans (le_max_left T _) hj
  have hjN : N ≤ j := by omega
  have hKj : K < j := by omega
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (show a j ≠ 1 by omega)
  have hpB : B < p := by
    by_contra h
    have hp_le : p ≤ B := by omega
    obtain ⟨i, hi, hiK, hpi⟩ := hK p hp_le ⟨j, hjT, hpa⟩
    have hij : i ≠ j := by omega
    have hc := primitive_multipliers_pairwise_coprime a u v T hnum hden hcop
      i j hi hjT hij
    have hp1 := Nat.eq_one_of_dvd_coprimes hc hpi hpa
    have hp2 := hp.two_le
    omega
  exact ⟨p, j, hp, hpB, max_le hjT hjN, hpa⟩

/-- The complete multiplier/irreducibility conclusion on the actual primitive
zero-density tail. Unit constant and irreducibility are both derived here.
The positive scale is a natural number, with its integer cast in the profile. -/
theorem primitive_zero_density_multiplier_irreducibility
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c}) :
    (c = 1 ∨ c = -1) ∧
    (∀ n, T ≤ n → Nat.Coprime (a n) (v n)) ∧
    (∀ i j, T ≤ i → T ≤ j → i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ N, ∃ n, max T N ≤ n ∧ 1 < a n) ∧
    (∀ B N, ∃ p j : ℕ, Nat.Prime p ∧ B < p ∧ max T N ≤ j ∧ p ∣ a j) ∧
    Irreducible (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))) := by
  have hadj : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1)) := by
    intro n hn
    exact primitive_step_adjacent_coprime (a n) (u n) (v n) (u (n + 1))
      (hnum n hn) (hcop n hn)
  have hc := primitive_cubic_unit_constant_of_zero_lower_density u (m : ℤ) c T hadj hzero
  have hnumZ : ∀ n, T ≤ n → (u (n + 1) : ℤ) + (v n : ℤ) = (a n : ℤ) * (u n : ℤ) := by
    intro n hn
    exact_mod_cast hnum n hn
  have hdenZ : ∀ n, T ≤ n → (v (n + 1) : ℤ) = (a n : ℤ) * (v n : ℤ) := by
    intro n hn
    exact_mod_cast hden n hn
  refine ⟨hc, primitive_multiplier_coprime_denominator a u v T hnum hden hcop,
    primitive_multipliers_pairwise_coprime a u v T hnum hden hcop,
    primitive_multiplier_arbitrarily_late_nonunit a u v T hv hnum hden,
    primitive_multiplier_prime_supply a u v T hv hnum hden hcop, ?_⟩
  exact integral_cubic_unit_irreducible_below_uniform
    (fun n ↦ (a n : ℤ)) (fun n ↦ (u n : ℤ)) (fun n ↦ (v n : ℤ)) m c T hm hc
    hnumZ hdenZ (hzero.not_positive_lower_bound (1 / 28) (by norm_num))

/-- Integer-scale form of the full paper lemma, with the exact unshifted
polynomial and the original zero-density hypothesis. All scale conversions
are performed in the body, and the unit conclusion is proved before use. -/
theorem primitive_zero_density_paper_multiplier_lemma
    (a u v : ℕ → ℕ) (m c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}) :
    (c = 1 ∨ c = -1) ∧
    (∀ n, T ≤ n → Nat.Coprime (a n) (v n)) ∧
    (∀ i j, T ≤ i → T ≤ j → i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ N, ∃ n, max T N ≤ n ∧ 1 < a n) ∧
    (∀ B N, ∃ p j : ℕ, Nat.Prime p ∧ B < p ∧ max T N ≤ j ∧ p ∣ a j) ∧
    Irreducible (rationalBinomialCubic (m : ℚ) (c : ℚ)) := by
  have hcast : (m.toNat : ℤ) = m := by omega
  have hmNat : 0 < m.toNat := by omega
  have hcastQ : (m.toNat : ℚ) = (m : ℚ) := by exact_mod_cast hcast
  have hz : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m.toNat : ℤ) * risingBinomial n + c} := by
    simpa only [hcast] using hzero
  obtain ⟨hc, hcd, hpair, hlate, hprimes, _⟩ :=
    primitive_zero_density_multiplier_irreducibility a u v m.toNat c T hmNat
      hv hnum hden hcop hz
  refine ⟨hc, hcd, hpair, hlate, hprimes, ?_⟩
  have hnumZ : ∀ n, T ≤ n → (u (n + 1) : ℤ) + (v n : ℤ) = (a n : ℤ) * (u n : ℤ) := by
    intro n hn
    exact_mod_cast hnum n hn
  have hdenZ : ∀ n, T ≤ n → (v (n + 1) : ℤ) = (a n : ℤ) * (v n : ℤ) := by
    intro n hn
    exact_mod_cast hden n hn
  have hh := integral_cubic_unit_unshifted_irreducible_below_uniform
    (fun n ↦ (a n : ℤ)) (fun n ↦ (u n : ℤ)) (fun n ↦ (v n : ℤ)) m.toNat c T hmNat hc
    hnumZ hdenZ (hz.not_positive_lower_bound (1 / 28) (by norm_num))
  simpa only [hcastQ] using hh

end ErdosProblems.Erdos243.PaperCompleteR11
