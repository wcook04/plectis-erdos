import Erdos249257.GcdMomentCalculus

/-! The long #249 manuscript's Stern--Brocot recursion with stopping
(`catalogue:mob:a9a`): the closed-form cylinder mass
`M(a,b) = 1/((2ᵃ-1)(2ᵇ-1))`, its exact mediant splitting, the root values,
the stopping and two transition probabilities together with the fact that
they sum to one and that the stopping probability is at least `1/3`, and the
factorisation `M(a,b) = P(a ∣ X)·P(b ∣ Y)` for the two independent fair-coin
waiting times. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open GcdMomentCalculus
open scoped BigOperators

private lemma two_le_two_pow_pnat (a : ℕ+) : (2 : ℝ) ≤ (2 : ℝ) ^ (a : ℕ) := by
  calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
    _ ≤ (2 : ℝ) ^ (a : ℕ) := pow_le_pow_right₀ (by norm_num) a.pos

private lemma tsum_pow_succ_of_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' j : ℕ, x ^ (j + 1) = x / (1 - x) := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one hnorm, ← tsum_mul_left]
  exact tsum_congr fun j => pow_succ' x j

private lemma half_pow_quotient (a : ℕ) (ha : 0 < a) :
    ((1 : ℝ) / 2) ^ a / (1 - ((1 : ℝ) / 2) ^ a) = 1 / ((2 : ℝ) ^ a - 1) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ a := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) ha
  have hpow : ((1 : ℝ) / 2) ^ a = 1 / (2 : ℝ) ^ a := by rw [div_pow, one_pow]
  have hden : (1 : ℝ) - ((1 : ℝ) / 2) ^ a = ((2 : ℝ) ^ a - 1) / (2 : ℝ) ^ a := by
    rw [hpow]
    field_simp
  rw [hden, hpow, div_div_eq_mul_div, one_div_mul_cancel (ne_of_gt hpos)]

/-- **`P(a ∣ X) = 1/(2ᵃ-1)`**: the mass the fair-coin waiting time
`P(X = k) = 2⁻ᵏ` (`k ≥ 1`) puts on the positive multiples of `a`. -/
theorem divisibility_mass (a : ℕ) (ha : 0 < a) :
    (∑' k : ℕ, if 0 < k ∧ a ∣ k then ((1 : ℝ) / 2) ^ k else 0)
      = 1 / ((2 : ℝ) ^ a - 1) := by
  have hy0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ a := by positivity
  have hy1 : ((1 : ℝ) / 2) ^ a < 1 := pow_lt_one₀ (by norm_num) (by norm_num) ha.ne'
  have hi : Function.Injective (fun j : ℕ => a * (j + 1)) := by
    intro j j' h
    dsimp only at h
    have := Nat.eq_of_mul_eq_mul_left ha h
    omega
  have hsupp : Function.support
      (fun k : ℕ => if 0 < k ∧ a ∣ k then ((1 : ℝ) / 2) ^ k else 0)
      ⊆ Set.range (fun j : ℕ => a * (j + 1)) := by
    intro k hk
    rw [Function.mem_support] at hk
    by_cases hg : 0 < k ∧ a ∣ k
    · obtain ⟨hk0, ⟨m, hm⟩⟩ := hg
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · rw [Nat.mul_zero] at hm
          omega
        · exact h
      refine ⟨m - 1, ?_⟩
      have hmm : m - 1 + 1 = m := by omega
      show a * (m - 1 + 1) = k
      rw [hmm, ← hm]
    · exact absurd (if_neg hg) hk
  have key := hi.tsum_eq hsupp
  have hterm : ∀ j : ℕ,
      (if 0 < a * (j + 1) ∧ a ∣ a * (j + 1) then ((1 : ℝ) / 2) ^ (a * (j + 1)) else 0)
        = (((1 : ℝ) / 2) ^ a) ^ (j + 1) := by
    intro j
    rw [if_pos ⟨Nat.mul_pos ha (Nat.succ_pos _), ⟨j + 1, rfl⟩⟩, ← pow_mul]
  have hgeo : ∑' j : ℕ, (((1 : ℝ) / 2) ^ a) ^ (j + 1)
      = ((1 : ℝ) / 2) ^ a / (1 - ((1 : ℝ) / 2) ^ a) :=
    tsum_pow_succ_of_lt_one hy0 hy1
  calc (∑' k : ℕ, if 0 < k ∧ a ∣ k then ((1 : ℝ) / 2) ^ k else 0)
      = ∑' j : ℕ, (if 0 < a * (j + 1) ∧ a ∣ a * (j + 1)
          then ((1 : ℝ) / 2) ^ (a * (j + 1)) else 0) := key.symm
    _ = ∑' j : ℕ, (((1 : ℝ) / 2) ^ a) ^ (j + 1) := tsum_congr hterm
    _ = ((1 : ℝ) / 2) ^ a / (1 - ((1 : ℝ) / 2) ^ a) := hgeo
    _ = 1 / ((2 : ℝ) ^ a - 1) := half_pow_quotient a ha

/-- **The cylinder mass factorises**: `M(a,b) = P(a ∣ X)·P(b ∣ Y)`. -/
theorem cylinderMass_eq_divisibility_mass_mul (a b : ℕ+) :
    cylinderMass a b
      = (∑' k : ℕ, if 0 < k ∧ (a : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0)
        * (∑' k : ℕ, if 0 < k ∧ (b : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0) := by
  rw [divisibility_mass (a : ℕ) a.pos, divisibility_mass (b : ℕ) b.pos, cylinderMass,
    div_mul_div_comm, one_mul]

/-- **The mediant recursion with stopping** (`catalogue:mob:a9a`):
`M(a,b) = 1/(2^{a+b}-1) + M(a+b,b) + M(a,a+b)`. -/
theorem cylinder_mediant_split (a b : ℕ+) :
    cylinderMass a b
      = 1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + cylinderMass (a + b) b + cylinderMass a (a + b) :=
  cylinderMass_split a b

/-- **The root**: `M(1,1) = 1` and each of the three terms on the right of the
recursion at `(1,1)` equals `1/3`. -/
theorem cylinder_root_values :
    cylinderMass 1 1 = 1 ∧
      1 / ((2 : ℝ) ^ (((1 : ℕ+) : ℕ) + ((1 : ℕ+) : ℕ)) - 1) = 1 / 3 ∧
      cylinderMass (1 + 1) 1 = 1 / 3 ∧ cylinderMass 1 (1 + 1) = 1 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [cylinderMass]
  · norm_num
  · norm_num [cylinderMass, PNat.add_coe]
  · norm_num [cylinderMass, PNat.add_coe]

/-- **The stopping and two transition probabilities sum to one.** -/
theorem stopping_transition_probabilities_sum_one (a b : ℕ+) :
    ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
        / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (a : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (b : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) = 1 := by
  have hA := two_le_two_pow_pnat a
  have hB := two_le_two_pow_pnat b
  have hpow : (2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) = (2 : ℝ) ^ (a : ℕ) * (2 : ℝ) ^ (b : ℕ) :=
    pow_add 2 _ _
  rw [hpow]
  have hAB : (0 : ℝ) < (2 : ℝ) ^ (a : ℕ) * (2 : ℝ) ^ (b : ℕ) - 1 := by nlinarith
  rw [← add_div, ← add_div, div_eq_iff (ne_of_gt hAB)]
  ring

/-- **The stopping probability is at least `1/3`.** -/
theorem stopping_probability_ge_third (a b : ℕ+) :
    (1 : ℝ) / 3 ≤ ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
      / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) := by
  have hA := two_le_two_pow_pnat a
  have hB := two_le_two_pow_pnat b
  have hpow : (2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) = (2 : ℝ) ^ (a : ℕ) * (2 : ℝ) ^ (b : ℕ) :=
    pow_add 2 _ _
  rw [hpow]
  have hAB : (0 : ℝ) < (2 : ℝ) ^ (a : ℕ) * (2 : ℝ) ^ (b : ℕ) - 1 := by nlinarith
  rw [le_div_iff₀ hAB]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ (a : ℕ) - 2)
    (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ (b : ℕ) - 2)]

#print axioms divisibility_mass
#print axioms cylinderMass_eq_divisibility_mass_mul
#print axioms cylinder_mediant_split
#print axioms cylinder_root_values
#print axioms stopping_transition_probabilities_sum_one
#print axioms stopping_probability_ge_third
end ErdosProblems.Erdos249.PaperCompleteR21
