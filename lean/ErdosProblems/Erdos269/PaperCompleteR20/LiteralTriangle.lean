import ErdosProblems.Erdos269.DyadicShellSummability

/-!
# The actual shell numerator as a finite weighted triangle

The map below identifies each odd exponent pair with its unique binary
multiple in the dyadic shell. All inequalities are exact integer inequalities.
The logarithmic coordinates and asymptotic bounds are separate consumers.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators

def triangleOddPart (v : ℕ × ℕ) : ℕ := 3 ^ v.1 * 5 ^ v.2

def literalTriangle (a : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (a + 1)).product (Finset.range (a + 1))).filter
    (fun v => triangleOddPart v < 2 ^ (a + 1))

theorem mem_literalTriangle_iff {a : ℕ} {v : ℕ × ℕ} :
    v ∈ literalTriangle a ↔ triangleOddPart v < 2 ^ (a + 1) := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hj : v.1 < a + 1 := by
      by_contra hn
      have h1 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_of_not_gt hn)
      have h2 := Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) v.1
      have h3 : 3 ^ v.1 ≤ triangleOddPart v := by
        exact Nat.le_mul_of_pos_right _ (by positivity)
      exact (not_lt_of_ge (h1.trans (h2.trans h3))) h
    have hk : v.2 < a + 1 := by
      by_contra hn
      have h1 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_of_not_gt hn)
      have h2 := Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 5) v.2
      have h3 : 5 ^ v.2 ≤ triangleOddPart v := by
        exact Nat.le_mul_of_pos_left _ (by positivity)
      exact (not_lt_of_ge (h1.trans (h2.trans h3))) h
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hk⟩, h⟩

def triangleShellLift (a : ℕ) (v : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (a - Nat.log 2 (triangleOddPart v), v)

theorem triangleShellLift_mem {a : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ literalTriangle a) : triangleShellLift a v ∈ dyadicSmoothShell235 a := by
  have hm : triangleOddPart v ≠ 0 := by simp [triangleOddPart]
  have hk : Nat.log 2 (triangleOddPart v) ≤ a := by
    have := Nat.log_lt_of_lt_pow hm (mem_literalTriangle_iff.mp hv)
    omega
  apply mem_dyadicSmoothShell235_iff.mpr
  change 2 ^ a ≤ 2 ^ (a - Nat.log 2 (triangleOddPart v)) * 3 ^ v.1 * 5 ^ v.2 ∧
    2 ^ (a - Nat.log 2 (triangleOddPart v)) * 3 ^ v.1 * 5 ^ v.2 < 2 ^ (a + 1)
  have he : a - Nat.log 2 (triangleOddPart v) + Nat.log 2 (triangleOddPart v) = a :=
    Nat.sub_add_cancel hk
  constructor
  · have h := Nat.mul_le_mul_left (2 ^ (a - Nat.log 2 (triangleOddPart v)))
      (Nat.pow_log_le_self 2 hm)
    rw [← pow_add, he] at h
    simpa only [triangleOddPart, mul_assoc] using h
  · have h := Nat.mul_lt_mul_of_pos_left
      (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (triangleOddPart v))
      (by positivity : 0 < (2 : ℕ) ^ (a - Nat.log 2 (triangleOddPart v)))
    rw [← pow_add, Nat.succ_eq_add_one, ← Nat.add_assoc, he] at h
    simpa only [triangleOddPart, mul_assoc] using h

theorem shell_projection_mem_triangle {a : ℕ} {e : ℕ × ℕ × ℕ}
    (he : e ∈ dyadicSmoothShell235 a) : e.2 ∈ literalTriangle a := by
  apply mem_literalTriangle_iff.mpr
  have hs := (mem_dyadicSmoothShell235_iff.mp he).2
  have hle : triangleOddPart e.2 ≤ smooth3Val 2 3 5 e.1 e.2.1 e.2.2 := by
    simpa only [triangleOddPart, smooth3Val, mul_assoc] using
      (Nat.le_mul_of_pos_left (triangleOddPart e.2) (by positivity : 0 < (2 : ℕ) ^ e.1))
  exact hle.trans_lt hs

theorem shell_projection_injective {a : ℕ} {e f : ℕ × ℕ × ℕ}
    (he : e ∈ dyadicSmoothShell235 a) (hf : f ∈ dyadicSmoothShell235 a)
    (h : e.2 = f.2) : e = f := by
  rcases e with ⟨i, v⟩
  rcases f with ⟨j, w⟩
  change v = w at h
  subst w
  have hi := mem_dyadicSmoothShell235_iff.mp he
  have hj := mem_dyadicSmoothShell235_iff.mp hf
  have hij : i = j := exponent_unique_in_short_interval
    (base := 2) (lo := 2 ^ a) (hi := 2 ^ (a + 1)) (weight := triangleOddPart v)
    (by norm_num) (by rw [pow_succ]; omega)
    (by simpa [smooth3Val, triangleOddPart, mul_assoc] using hi.1)
    (by simpa [smooth3Val, triangleOddPart, mul_assoc] using hi.2)
    (by simpa [smooth3Val, triangleOddPart, mul_assoc] using hj.1)
    (by simpa [smooth3Val, triangleOddPart, mul_assoc] using hj.2)
  subst j
  rfl

theorem triangleShellLift_projection {a : ℕ} {e : ℕ × ℕ × ℕ}
    (he : e ∈ dyadicSmoothShell235 a) : triangleShellLift a e.2 = e :=
  shell_projection_injective (triangleShellLift_mem (shell_projection_mem_triangle he)) he rfl

def literalTriangleWeight (a : ℕ) (v : ℕ × ℕ) : ℕ :=
  oddHeightSuffix235 a (triangleShellLift a v)

theorem actual_numerator_eq_literal_triangle (a : ℕ) :
    dyadicOrderedBlockDigit235 a =
      ∑ v ∈ literalTriangle a, literalTriangleWeight a v := by
  rw [← dyadicHalfClearedMass235_eq_orderedBlockDigit235]
  unfold dyadicHalfClearedMass235
  refine Finset.sum_bij (fun e _ => e.2)
    (fun _ he => shell_projection_mem_triangle he)
    (fun _ he _ hf h => shell_projection_injective he hf h) ?_ ?_
  · intro v hv
    exact ⟨triangleShellLift a v, triangleShellLift_mem hv, rfl⟩
  · intro e he
    simp only [literalTriangleWeight, triangleShellLift_projection he]

theorem literalTriangleWeight_four_values {a : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ literalTriangle a) :
    literalTriangleWeight a v = 1 ∨ literalTriangleWeight a v = 3 ∨
      literalTriangleWeight a v = 5 ∨ literalTriangleWeight a v = 15 := by
  unfold literalTriangleWeight
  rw [oddHeightSuffix235_eq_thresholdFactors (triangleShellLift_mem hv)]
  split_ifs <;> norm_num

theorem literalTriangleWeight_pos {a : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ literalTriangle a) : 1 ≤ literalTriangleWeight a v := by
  rcases literalTriangleWeight_four_values hv with h | h | h | h <;> omega

theorem triangle_card_le_actual_numerator (a : ℕ) :
    (literalTriangle a).card ≤ dyadicOrderedBlockDigit235 a := by
  rw [actual_numerator_eq_literal_triangle]
  simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
    (Finset.sum_le_sum (fun v hv => literalTriangleWeight_pos hv))

#print axioms actual_numerator_eq_literal_triangle
#print axioms literalTriangleWeight_four_values
#print axioms triangle_card_le_actual_numerator

end ErdosProblems.Erdos269.PaperCompleteR20
