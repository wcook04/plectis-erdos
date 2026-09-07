import ErdosProblems.Erdos243.PaperCompleteR7.Arithmetic

/-!
# Full paper assemblies for reduced tails and gcd stabilisation

Uncompiled source candidates.  The stable gcd is not merely named: the
positivity, reducedness, and both exact quotient recurrences are concluded.
No extra positivity assumption is imposed in the cofinal-negative version;
it is derived from the supplied signed-error hypotheses.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

/-- Both papers, `res:reduced`: one declaration for all three conclusions.
In the second conclusion `i ≠ j` is used, not just the ordered half. -/
theorem persistent_coprimality
    (a u v : ℕ → ℕ)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n) :
    (∀ n, Nat.Coprime (a n) (v n)) ∧
    (∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ i t, i < t → Nat.Coprime (a i) (u t)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact reducedStep_coprime_currentFactor (hred (n + 1)) (hu n) (hv n)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact reducedTail_pairwiseCoprime a u v hred hu hv hlt
    · exact (reducedTail_pairwiseCoprime a u v hred hu hv hgt).symm
  · intro i t hit
    exact reducedTail_wholeModulusAvoidance a u v hred hv hit

/-- A zero natural numerator propagates forward under positive-coefficient
natural dynamics.  Used only to recover positivity omitted from the long
record's local wording. -/
theorem tail_zero_propagates
    (a C D : ℕ → ℕ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    {n : ℕ} (hz : C n = 0) :
    ∀ t, n ≤ t → C t = 0 := by
  intro t hnt
  induction t, hnt using Nat.le_induction with
  | base => exact hz
  | succ t hnt ih =>
      have hs := hC t
      rw [ih, Nat.mul_zero] at hs
      omega

/-- Cofinal negative centred errors rule out zero numerators at every
index.  No assumption about normalised vanishing is used. -/
theorem positive_tail_of_cofinal_negative
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hneg : ∀ N, ∃ t, N ≤ t ∧ E t < 0) :
    ∀ n, 0 < C n := by
  intro n
  by_contra hn
  have hz : C n = 0 := by omega
  obtain ⟨t, hnt, ht⟩ := hneg n
  have hzt := tail_zero_propagates a C D hC hz t hnt
  have he := hE t
  simp only [centeredState, hzt, Nat.cast_zero, mul_zero, sub_zero] at he
  have hd : (0 : ℤ) ≤ D t := by positivity
  omega

/-- Natural form of a bounded negative signed error, with the
`a - 1` cast justified from positivity of the next numerator. -/
theorem negative_error_shape
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (t B : ℕ) (hneg : E t < 0) (hbound : -(B : ℤ) ≤ E t) :
    ∃ e : ℕ, 0 < e ∧ e ≤ B ∧ D t + e = (a t - 1) * C t := by
  have ha : 1 ≤ a t := by
    by_contra hnot
    have haz : a t = 0 := by omega
    have hs := hC t
    rw [haz, Nat.zero_mul] at hs
    have hc := hCpos (t + 1)
    omega
  let e : ℕ := (-E t).toNat
  have hecast : (e : ℤ) = -E t := by
    dsimp [e]
    exact Int.toNat_of_nonneg (by omega)
  have hepos : 0 < e := by omega
  have heB : e ≤ B := by omega
  have hacast : ((a t - 1 : ℕ) : ℤ) = (a t : ℤ) - 1 := by omega
  have hshape : (D t : ℤ) + (e : ℤ) =
      ((a t - 1 : ℕ) : ℤ) * (C t : ℤ) := by
    rw [hacast, hecast, hE t]
    simp only [centeredState]
    ring
  refine ⟨e, hepos, heB, ?_⟩
  exact_mod_cast hshape

/-- Both papers, `res:gcdstab`: complete signed cofinal-negative statement.
The tuple includes the stable gcd and the positive reduced exact tail.
Only natural denominator nonnegativity, not strict denominator positivity,
is required by the definition of a reduced tail in the short note. -/
theorem gcd_stabilises_and_reduces
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hnegative : ∃ B : ℕ, ∀ N, ∃ t,
      N ≤ t ∧ E t < 0 ∧ -(B : ℤ) ≤ E t) :
    ∃ N g : ℕ, 0 < g ∧
      (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
      (∀ n, N ≤ n → 0 < C n / g) ∧
      (∀ n, N ≤ n → Nat.Coprime (C n / g) (D n / g)) ∧
      (∀ n, N ≤ n → C (n + 1) / g + D n / g = a n * (C n / g)) ∧
      (∀ n, N ≤ n → D (n + 1) / g = a n * (D n / g)) := by
  obtain ⟨B, hB⟩ := hnegative
  have hCpos : ∀ n, 0 < C n := by
    apply positive_tail_of_cofinal_negative a C D E hC hE
    intro N
    obtain ⟨t, hNt, ht, _⟩ := hB N
    exact ⟨t, hNt, ht⟩
  have hshape : ∀ N, ∃ t e : ℕ,
      N ≤ t ∧ 0 < e ∧ e ≤ B ∧ D t + e = (a t - 1) * C t := by
    intro N
    obtain ⟨t, hNt, ht, htB⟩ := hB N
    obtain ⟨e, he, heB, hs⟩ :=
      negative_error_shape a C D E hCpos hC hE t B ht htB
    exact ⟨t, e, hNt, he, heB, hs⟩
  obtain ⟨N, hN⟩ :=
    tailGcd_eventuallyConstant_of_cofinally_boundedNegative
      a C D B hCpos hC hD hshape
  let g := Nat.gcd (C N) (D N)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left (D N) (hCpos N)
  have hG : ∀ n, N ≤ n → Nat.gcd (C n) (D n) = g := hN
  have hgC : ∀ n, N ≤ n → g ∣ C n := by
    intro n hn
    rw [← hG n hn]
    exact Nat.gcd_dvd_left (C n) (D n)
  have hgD : ∀ n, N ≤ n → g ∣ D n := by
    intro n hn
    rw [← hG n hn]
    exact Nat.gcd_dvd_right (C n) (D n)
  refine ⟨N, g, hgpos, hG, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact Nat.div_pos (Nat.le_of_dvd (hCpos n) (hgC n hn)) hgpos
  · intro n hn
    have hc := Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left (D n) (hCpos n))
    simpa only [hG n hn] using hc
  · intro n hn
    apply Nat.eq_of_mul_eq_mul_left hgpos
    calc
      g * (C (n + 1) / g + D n / g) = C (n + 1) + D n := by
        rw [Nat.mul_add, Nat.mul_div_cancel' (hgC (n + 1) (by omega)),
          Nat.mul_div_cancel' (hgD n hn)]
      _ = a n * C n := hC n
      _ = g * (a n * (C n / g)) := by
        have hc : C n = g * (C n / g) := (Nat.mul_div_cancel' (hgC n hn)).symm
        calc
          a n * C n = a n * (g * (C n / g)) := congrArg (fun x ↦ a n * x) hc
          _ = g * (a n * (C n / g)) := by ring
  · intro n hn
    rw [hD n]
    exact Nat.mul_div_assoc (a n) (hgD n hn)

end ErdosProblems.Erdos243.PaperCompleteR7
