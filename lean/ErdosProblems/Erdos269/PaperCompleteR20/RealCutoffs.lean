import ErdosProblems.Erdos269.RealCutoffR10

/-!
# Literal real cutoffs for the Erdős 269 paper

The paper quantifies its prefix cutoffs and shell endpoints over the reals.
This module transports the existing natural-cutoff arithmetic through
`Nat.floor` and proves the short-shell injection directly for real endpoints.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open Finset
open scoped BigOperators

noncomputable section

open PaperR10

/-- `Nat.log p ⌊x⌋₊` is exactly the largest natural exponent whose real prime
power does not exceed the real cutoff. -/
theorem pow_le_real_cutoff_iff_le_natLog_floor
    {p e : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x) :
    (((p ^ e : ℕ) : ℝ) ≤ x) ↔ e ≤ Nat.log p ⌊x⌋₊ := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hn : ⌊x⌋₊ ≠ 0 := by
    have := (Nat.one_le_floor_iff x).mpr hx
    omega
  rw [← Nat.le_floor_iff hx0, Nat.le_log_iff_pow_le hp hn]

/-- The natural logarithm of the natural floor is the unique maximal exponent
described in the paper's definition of `⌊log_p x⌋`. -/
theorem natLog_floor_isGreatest_real_power
    {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x) :
    (((p ^ Nat.log p ⌊x⌋₊ : ℕ) : ℝ) ≤ x) ∧
      ∀ e : ℕ, (((p ^ e : ℕ) : ℝ) ≤ x) → e ≤ Nat.log p ⌊x⌋₊ := by
  constructor
  · exact (pow_le_real_cutoff_iff_le_natLog_floor hp hx).2 le_rfl
  · intro e he
    exact (pow_le_real_cutoff_iff_le_natLog_floor hp hx).1 he

/-- Literal real logarithmic-cell relation from the paper. -/
def SameThreePrimeRealLogCell (p q r : ℕ) (x y : ℝ) : Prop :=
  ⌊Real.logb p x⌋₊ = ⌊Real.logb p y⌋₊ ∧
    ⌊Real.logb q x⌋₊ = ⌊Real.logb q y⌋₊ ∧
      ⌊Real.logb r x⌋₊ = ⌊Real.logb r y⌋₊

/-- The paper's real-cutoff running LCM theorem. -/
theorem running_lcm_real_cutoff_exact {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x : ℝ} (hx : 1 ≤ x) :
    realPrefixLcm p q r x = realThreePrimeHeight p q r x :=
  running_lcm_real_cutoff hp hq hr hpq hpr hqr hx

/-- The height is constant on a literal real logarithmic cell. -/
theorem realThreePrimeHeight_eq_of_sameLogCell
    {p q r : ℕ} {x y : ℝ}
    (hcell : SameThreePrimeRealLogCell p q r x y) :
    realThreePrimeHeight p q r x = realThreePrimeHeight p q r y := by
  rcases hcell with ⟨hp, hq, hr⟩
  simp [realThreePrimeHeight, hp, hq, hr]

/-- The literal real-cutoff running LCM is constant on logarithmic cells. -/
theorem realPrefixLcm_eq_of_sameLogCell
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hcell : SameThreePrimeRealLogCell p q r x y) :
    realPrefixLcm p q r x = realPrefixLcm p q r y := by
  rw [running_lcm_real_cutoff_exact hp hq hr hpq hpr hqr hx,
    running_lcm_real_cutoff_exact hp hq hr hpq hpr hqr hy]
  exact realThreePrimeHeight_eq_of_sameLogCell hcell

/-- Advancing only the first real logarithmic coordinate multiplies the
running height by its base. -/
theorem realThreePrimeHeight_jump_first
    {p q r : ℕ} {x y : ℝ}
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊ + 1)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realThreePrimeHeight p q r y = p * realThreePrimeHeight p q r x := by
  simp [realThreePrimeHeight, hp, hq, hr, pow_succ]
  ring

/-- The corresponding literal jump ratio for the real-cutoff running LCM. -/
theorem realPrefixLcm_jump_first
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊ + 1)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = p * realPrefixLcm p q r x := by
  rw [running_lcm_real_cutoff_exact pPrime qPrime rPrime hpq hpr hqr hy,
    running_lcm_real_cutoff_exact pPrime qPrime rPrime hpq hpr hqr hx]
  exact realThreePrimeHeight_jump_first hp hq hr

theorem realThreePrimeHeight_jump_second
    {p q r : ℕ} {x y : ℝ}
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊ + 1)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realThreePrimeHeight p q r y = q * realThreePrimeHeight p q r x := by
  simp [realThreePrimeHeight, hp, hq, hr, pow_succ]
  ring

theorem realThreePrimeHeight_jump_third
    {p q r : ℕ} {x y : ℝ}
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊ + 1) :
    realThreePrimeHeight p q r y = r * realThreePrimeHeight p q r x := by
  simp [realThreePrimeHeight, hp, hq, hr, pow_succ]
  ring

theorem realPrefixLcm_jump_second
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊ + 1)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = q * realPrefixLcm p q r x := by
  rw [running_lcm_real_cutoff_exact pPrime qPrime rPrime hpq hpr hqr hy,
    running_lcm_real_cutoff_exact pPrime qPrime rPrime hpq hpr hqr hx]
  exact realThreePrimeHeight_jump_second hp hq hr

theorem realPrefixLcm_jump_third
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊ + 1) :
    realPrefixLcm p q r y = r * realPrefixLcm p q r x := by
  rw [running_lcm_real_cutoff_exact pPrime qPrime rPrime hpq hpr hqr hy,
    running_lcm_real_cutoff_exact pPrime qPrime rPrime hpq hpr hqr hx]
  exact realThreePrimeHeight_jump_third hp hq hr

/-- Kernel constancy for two literal smooth real points in one real cell. -/
theorem threePrimeKernelQ_eq_of_sameRealLogCell
    {p q r i j k i' j' k' : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hcell : SameThreePrimeRealLogCell p q r
      (smooth3Val p q r i j k : ℝ) (smooth3Val p q r i' j' k' : ℝ)) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  have hx : 1 ≤ smooth3Val p q r i j k := by
    unfold smooth3Val
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hy : 1 ≤ smooth3Val p q r i' j' k' := by
    unfold smooth3Val
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hxR : (1 : ℝ) ≤ (smooth3Val p q r i j k : ℕ) := by exact_mod_cast hx
  have hyR : (1 : ℝ) ≤ (smooth3Val p q r i' j' k' : ℕ) := by exact_mod_cast hy
  have hheight := realThreePrimeHeight_eq_of_sameLogCell hcell
  rw [realThreePrimeHeight_eq hp hq hr hxR,
    realThreePrimeHeight_eq hp hq hr hyR] at hheight
  simp only [Nat.floor_natCast] at hheight
  simp only [threePrimeKernelQ, hheight]

/-- Literal real-endpoint form of uniqueness in a short multiplicative
interval.  The exponent and base remain natural, as in the paper. -/
theorem exponent_unique_in_real_short_interval
    {base a b : ℕ} {lo hi weight : ℝ}
    (hbase : 0 < base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ (base : ℝ) * lo)
    (haLo : lo ≤ (base : ℝ) ^ a * weight)
    (haHi : (base : ℝ) ^ a * weight < hi)
    (hbLo : lo ≤ (base : ℝ) ^ b * weight)
    (hbHi : (base : ℝ) ^ b * weight < hi) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hpowNat : base ^ (a + 1) ≤ base ^ b :=
      Nat.pow_le_pow_right hbase (by omega)
    have hpow : (base : ℝ) ^ (a + 1) ≤ (base : ℝ) ^ b := by
      exact_mod_cast hpowNat
    have hbaseR : (0 : ℝ) ≤ base := by positivity
    have hcontra : hi < hi := calc
      hi ≤ (base : ℝ) * lo := hwidth
      _ ≤ (base : ℝ) * ((base : ℝ) ^ a * weight) :=
        mul_le_mul_of_nonneg_left haLo hbaseR
      _ = (base : ℝ) ^ (a + 1) * weight := by rw [pow_succ]; ring
      _ ≤ (base : ℝ) ^ b * weight := mul_le_mul_of_nonneg_right hpow hweight
      _ < hi := hbHi
    exact (lt_irrefl hi hcontra).elim
  · exact hab
  · have hpowNat : base ^ (b + 1) ≤ base ^ a :=
      Nat.pow_le_pow_right hbase (by omega)
    have hpow : (base : ℝ) ^ (b + 1) ≤ (base : ℝ) ^ a := by
      exact_mod_cast hpowNat
    have hbaseR : (0 : ℝ) ≤ base := by positivity
    have hcontra : hi < hi := calc
      hi ≤ (base : ℝ) * lo := hwidth
      _ ≤ (base : ℝ) * ((base : ℝ) ^ b * weight) :=
        mul_le_mul_of_nonneg_left hbLo hbaseR
      _ = (base : ℝ) ^ (b + 1) * weight := by rw [pow_succ]; ring
      _ ≤ (base : ℝ) ^ a * weight := mul_le_mul_of_nonneg_right hpow hweight
      _ < hi := haHi
    exact (lt_irrefl hi hcontra).elim

/-- Exponent triples in the paper's real half-open shell. -/
def realSmoothExponentShell
    (p q r : ℕ) (lo hi : ℝ) (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (hp + 1)).product
      ((range (hq + 1)).product (range (hr + 1)))).filter
    fun e => lo ≤ (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ∧
      (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) < hi

/-- Real-shell projection after forgetting the first exponent. -/
theorem realSmoothExponentShell_card_le_dropFirst
    {p q r hp hq hr : ℕ} {lo hi : ℝ}
    (hpPos : 0 < p) (hwidth : hi ≤ (p : ℝ) * lo) :
    (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
      (hq + 1) * (hr + 1) := by
  classical
  let target := (range (hq + 1)).product (range (hr + 1))
  have hcard :
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn
      (fun e : ℕ × ℕ × ℕ => e.2) ?_ ?_
    · intro e he
      rcases e with ⟨a, b, c⟩
      simp only [Finset.mem_coe, realSmoothExponentShell, Finset.mem_filter] at he
      have houter := Finset.mem_product.mp he.1
      have hinner := Finset.mem_product.mp houter.2
      exact Finset.mem_product.mpr ⟨hinner.1, hinner.2⟩
    · intro e₁ he₁ e₂ he₂ hproj
      rcases e₁ with ⟨a₁, b₁, c₁⟩
      rcases e₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      simp only [Finset.mem_coe, realSmoothExponentShell, Finset.mem_filter] at he₁ he₂
      have hw : 0 ≤ (q : ℝ) ^ b₁ * (r : ℝ) ^ c₁ := by positivity
      have ha : a₁ = a₂ := exponent_unique_in_real_short_interval
        hpPos hw hwidth
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc] using he₁.2.1)
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc] using he₁.2.2)
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc] using he₂.2.1)
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc] using he₂.2.2)
      simp [ha]
  simpa [target] using hcard

/-- Real-shell projection after forgetting the third exponent. -/
theorem realSmoothExponentShell_card_le_dropThird
    {p q r hp hq hr : ℕ} {lo hi : ℝ}
    (hrPos : 0 < r) (hwidth : hi ≤ (r : ℝ) * lo) :
    (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
      (hp + 1) * (hq + 1) := by
  classical
  let target := (range (hp + 1)).product (range (hq + 1))
  have hcard :
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn
      (fun e : ℕ × ℕ × ℕ => (e.1, e.2.1)) ?_ ?_
    · intro e he
      rcases e with ⟨a, b, c⟩
      simp only [Finset.mem_coe, realSmoothExponentShell, Finset.mem_filter] at he
      have houter := Finset.mem_product.mp he.1
      have hinner := Finset.mem_product.mp houter.2
      exact Finset.mem_product.mpr ⟨houter.1, hinner.1⟩
    · intro e₁ he₁ e₂ he₂ hproj
      rcases e₁ with ⟨a₁, b₁, c₁⟩
      rcases e₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      simp only [Finset.mem_coe, realSmoothExponentShell, Finset.mem_filter] at he₁ he₂
      have hw : 0 ≤ (p : ℝ) ^ a₁ * (q : ℝ) ^ b₁ := by positivity
      have hc : c₁ = c₂ := exponent_unique_in_real_short_interval
        hrPos hw hwidth
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc,
          mul_comm, mul_left_comm] using he₁.2.1)
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc,
          mul_comm, mul_left_comm] using he₁.2.2)
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc,
          mul_comm, mul_left_comm] using he₂.2.1)
        (by simpa [smooth3Val, Nat.cast_mul, Nat.cast_pow, mul_assoc,
          mul_comm, mul_left_comm] using he₂.2.2)
      simp [hc]
  simpa [target] using hcard

/-- The full literal real-shell proposition from the paper, including its
quadratic consequence under sorted height coordinates. -/
theorem realSmoothExponentShell_bounds
    {p q r hp hq hr j : ℕ} {lo hi : ℝ}
    (hpPos : 0 < p) (hrPos : 0 < r) :
    (hi ≤ (r : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hp + 1) * (hq + 1)) ∧
    (hi ≤ (p : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hq + 1) * (hr + 1)) ∧
    (hi ≤ (r : ℝ) * lo → hp ≤ hq → hq ≤ hr → hp + hq + hr = j →
      9 * (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (j + 3) ^ 2) := by
  constructor
  · intro hwidth
    exact realSmoothExponentShell_card_le_dropThird hrPos hwidth
  constructor
  · intro hwidth
    exact realSmoothExponentShell_card_le_dropFirst hpPos hwidth
  · intro hwidth hpq hqr hsum
    exact (Nat.mul_le_mul_left 9
      (realSmoothExponentShell_card_le_dropThird hrPos hwidth)).trans
        (sorted_pair_quadratic hpq hqr hsum)

#print axioms pow_le_real_cutoff_iff_le_natLog_floor
#print axioms running_lcm_real_cutoff_exact
#print axioms realPrefixLcm_eq_of_sameLogCell
#print axioms realPrefixLcm_jump_first
#print axioms realPrefixLcm_jump_second
#print axioms realPrefixLcm_jump_third
#print axioms threePrimeKernelQ_eq_of_sameRealLogCell
#print axioms exponent_unique_in_real_short_interval
#print axioms realSmoothExponentShell_card_le_dropFirst
#print axioms realSmoothExponentShell_card_le_dropThird
#print axioms realSmoothExponentShell_bounds

end
end ErdosProblems.Erdos269.PaperCompleteR20
