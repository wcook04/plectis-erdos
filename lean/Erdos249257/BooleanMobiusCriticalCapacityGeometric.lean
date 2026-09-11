import Erdos249257.BooleanMobiusSkippedCoreCriticalCapacity

/-!
# Geometric expansion of the skipped-core critical quotient

This companion module exposes the integral Mersenne quotients in the critical
capacity socket as finite shifted geometric sums.
-/

namespace Erdos249257

open scoped BigOperators

/-! ## Exact finite geometric coordinates -/

/-- The quotient of one scaled Mersenne weight written without division: a
shift by the Euclidean remainder times a finite geometric word. -/
def localMersenneGeometricQuotient (M d : ℕ) : ℕ :=
  2 ^ (M % d) * ∑ j ∈ Finset.range (M / d), (2 ^ d) ^ j

/-- The corresponding geometric normal form of a finite prefix quotient. -/
def localGeometricPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneGeometricQuotient M d

/-- Euclidean division by `2^d-1` is exactly the shifted finite geometric
word with ones at spacings `d`. -/
theorem localMersenneQuotient_eq_geometric
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = localMersenneGeometricQuotient M d := by
  let r := M % d
  let q := M / d
  let B := 2 ^ d
  let G := ∑ j ∈ Finset.range q, B ^ j
  let R := 2 ^ r
  let Q := R * G
  have hdpos : 0 < d := by omega
  have hrlt : r < d := by
    dsimp [r]
    exact Nat.mod_lt M hdpos
  have hM : M = d * q + r := by
    calc
      M = d * (M / d) + M % d := (Nat.div_add_mod M d).symm
      _ = d * q + r := by rfl
  have hpow : 2 ^ M = R * B ^ q := by
    calc
      2 ^ M = 2 ^ (d * q + r) := by rw [hM]
      _ = 2 ^ (d * q) * 2 ^ r := by rw [pow_add]
      _ = B ^ q * R := by rw [pow_mul]
      _ = R * B ^ q := by rw [Nat.mul_comm]
  have hBone : 1 ≤ B := by
    dsimp [B]
    exact Nat.one_le_pow d 2 (by norm_num)
  have hgeom : G * (B - 1) + 1 = B ^ q := by
    have h := geom_sum_mul_add (B - 1) q
    simpa [G, Nat.sub_add_cancel hBone] using h
  have hdecomp : 2 ^ M = Q * (B - 1) + R := by
    rw [hpow, ← hgeom]
    dsimp [Q]
    ring
  have hrle : r ≤ d - 1 := by omega
  have hRle : R ≤ 2 ^ (d - 1) := by
    dsimp [R]
    exact Nat.pow_le_pow_right (by norm_num) hrle
  have hsplit : B = 2 ^ (d - 1) * 2 := by
    dsimp [B]
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (d - 1) * 2 := by rw [pow_succ]
  have htwo : 2 ≤ 2 ^ (d - 1) := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ d - 1))
  have hrem : R < B - 1 := by omega
  unfold localMersenneQuotient localMersenneGeometricQuotient
  change 2 ^ M / (B - 1) = Q
  apply Nat.div_eq_of_lt_le
  · rw [hdecomp]
    exact Nat.le_add_right _ _
  · rw [hdecomp]
    calc
      Q * (B - 1) + R < Q * (B - 1) + (B - 1) :=
        Nat.add_lt_add_left hrem _
      _ = (Q + 1) * (B - 1) := by ring

/-- The same quotient word, reindexed from its highest occupied binary
position down through the positive multiples of `d`. -/
theorem localMersenneGeometricQuotient_eq_descendingMultiples
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneGeometricQuotient M d =
      ∑ i ∈ Finset.range (M / d), 2 ^ (M - d * (i + 1)) := by
  let q := M / d
  let r := M % d
  have hdivmod : M = d * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod M d).symm
  unfold localMersenneGeometricQuotient
  change
    2 ^ r * (∑ i ∈ Finset.range q, (2 ^ d) ^ i) =
      ∑ i ∈ Finset.range q, 2 ^ (M - d * (i + 1))
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hiq : i < q := Finset.mem_range.mp hi
  have hdi : d * (i + 1) ≤ d * q :=
    Nat.mul_le_mul_left d (by omega)
  have hexponent :
      r + d * (q - 1 - i) = M - d * (i + 1) := by
    calc
      r + d * (q - 1 - i) = r + (d * q - d * (i + 1)) := by
        rw [show q - 1 - i = q - (i + 1) by omega,
          Nat.mul_sub_left_distrib]
      _ = (d * q + r) - d * (i + 1) := by
        rw [add_comm (d * q) r, add_tsub_assoc_of_le hdi]
      _ = M - d * (i + 1) := by rw [← hdivmod]
  rw [← pow_mul, ← pow_add, hexponent]

/-- Division-free descending-multiple form of one integral Mersenne
quotient. -/
theorem localMersenneQuotient_eq_descendingMultiples
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d =
      ∑ i ∈ Finset.range (M / d), 2 ^ (M - d * (i + 1)) := by
  rw [localMersenneQuotient_eq_geometric hd,
    localMersenneGeometricQuotient_eq_descendingMultiples hd]

/-- Summing the pointwise normal form removes every floor division from a
finite local prefix quotient. -/
theorem localPrefixQuotient_eq_geometric
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D M = localGeometricPrefixQuotient D M := by
  unfold localPrefixQuotient localGeometricPrefixQuotient
  apply Finset.sum_congr rfl
  intro d hd
  exact localMersenneQuotient_eq_geometric (hD d hd)

/-! ## Critical-capacity normal form -/

/-- At endpoint `2c-2`, the newly inserted crossing rank contributes exactly
the single binary coin `2^(c-2)`. -/
theorem localMersenneGeometricQuotient_critical_self
    {c : ℕ} (hc : 4 ≤ c) :
    localMersenneGeometricQuotient (2 * c - 2) c = 2 ^ (c - 2) := by
  calc
    localMersenneGeometricQuotient (2 * c - 2) c =
        localMersenneQuotient (2 * c - 2) c :=
      (localMersenneQuotient_eq_geometric (by omega)).symm
    _ = 2 ^ (c - 2) := localMersenneQuotient_two_mul_sub_two_self hc

/-- Splitting off the crossing rank leaves a core-only geometric quotient. -/
theorem localGeometricPrefixQuotient_insert_critical
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c) :
    localGeometricPrefixQuotient (insert c D) (2 * c - 2) =
      2 ^ (c - 2) + localGeometricPrefixQuotient D (2 * c - 2) := by
  have hcnot : c ∉ D := by
    intro hcD
    exact (Nat.lt_irrefl c) (hD c hcD).2
  simp [localGeometricPrefixQuotient, hcnot,
    localMersenneGeometricQuotient_critical_self hc]

/-- The remaining integral crossing test is equivalently an explicit finite
sum of shifted powers of two. -/
theorem criticalQuotient_iff_geometric
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c) :
    2 ^ ((2 * c - 2) - 1) ≤
        localPrefixQuotient (insert c D) (2 * c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localGeometricPrefixQuotient (insert c D) (2 * c - 2) := by
  rw [localPrefixQuotient_eq_geometric]
  intro d hd
  rw [Finset.mem_insert] at hd
  rcases hd with rfl | hd
  · omega
  · exact (hD d hd).1

/-- After removing the crossing coin, the sharp capacity socket is a single
lower bound on the old core's explicit geometric word. -/
theorem criticalQuotient_iff_geometricCore_deficit
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c) :
    2 ^ ((2 * c - 2) - 1) ≤
        localPrefixQuotient (insert c D) (2 * c - 2) ↔
      2 ^ ((2 * c - 2) - 1) - 2 ^ (c - 2) ≤
        localGeometricPrefixQuotient D (2 * c - 2) := by
  rw [criticalQuotient_iff_geometric hc hD,
    localGeometricPrefixQuotient_insert_critical hc hD]
  omega

/-- Geometric-series form of
`localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff`: the sharp strict
upper fill is now reduced to one explicit binary carry inequality. -/
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localGeometricPrefixQuotient (insert c D) (2 * c - 2) := by
  rw [localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff hc hD hbelow,
    criticalQuotient_iff_geometric hc hD]

/-- Core-only form of the same sharp skipped-core capacity test. -/
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) - 2 ^ (c - 2) ≤
        localGeometricPrefixQuotient D (2 * c - 2) := by
  rw [localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff hc hD hbelow,
    criticalQuotient_iff_geometricCore_deficit hc hD]

end Erdos249257
