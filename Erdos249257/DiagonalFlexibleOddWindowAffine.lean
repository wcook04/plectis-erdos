import Erdos249257.DiagonalFlexibleOddWindowSupply

namespace Erdos249257.DiagonalFreshLossBridge
namespace PowerTwoOddWindowAffine

open TotientTailPeriodKiller

/-!
An exact affine form of the flexible three-rank #249 endpoint.

Once the current actual centered state is in the edge tube, the elementary
post-canonical correction bounds exclude modular wrapping at each of the next
two ranks.  The three half-word predicates are therefore equivalent to one
three-scale affine escape disjunction involving the actual state and its next
two corrections.

The generic zero-start orbit at the end of this file records the limit of this
reduction: a uniform correction envelope below twice the canonical edge is
compatible with staying in every scaled edge tube for arbitrarily many ranks.
The remaining cofinal theorem must use arithmetic correlation between the
actual state and its corrections, not their magnitudes alone.
-/

def edge (q : ℕ) : ℤ := (4 : ℤ) ^ q / 32

def state (a q : ℕ) : ℤ := actualOddHalfCenteredLift a q

def ThreeRankBandAt (a q : ℕ) : Prop :=
  PowerTwoOddHalfWordBandAt a q ∨
    PowerTwoOddHalfWordBandAt a (q + 1) ∨
      PowerTwoOddHalfWordBandAt a (q + 2)

def ThreeScaleAffineEscapeAt (a q : ℕ) : Prop :=
  edge q ≤ |state a q| ∨
    4 * edge q ≤ |4 * state a q + actualOddHalfCorrection a q| ∨
      16 * edge q ≤
        |16 * state a q + 4 * actualOddHalfCorrection a q +
          actualOddHalfCorrection a (q + 1)|

/-- Two representatives in the signed half-cell are equal when one is
strictly inside it.  Strictness removes the positive/negative midpoint tie. -/
theorem eq_of_modEq_of_centered_bounds
    {M x y : ℤ} (hM : 0 < M) (hmod : Int.ModEq M x y)
    (hx : |x| ≤ M / 2) (hy : |y| < M / 2) :
    x = y := by
  have hx' := abs_le.mp hx
  have hy' := abs_lt.mp hy
  have hlo : -M < y - x := by omega
  have hhi : y - x < M := by omega
  obtain ⟨k, hk⟩ := hmod.dvd
  by_cases hk0 : k = 0
  · simp [hk0] at hk
    omega
  have hkcases : k ≤ -1 ∨ 1 ≤ k := by omega
  rcases hkcases with hkneg | hkpos
  · have hmul : M * k ≤ M * (-1) :=
      mul_le_mul_of_nonneg_left hkneg hM.le
    nlinarith
  · have hmul : M * 1 ≤ M * k :=
      mul_le_mul_of_nonneg_left hkpos hM.le
    nlinarith

/-- `4^q` is exactly 32 times its `1/32` edge once `q ≥ 3`. -/
theorem fourPow_eq_thirtyTwo_mul_edge {q : ℕ} (hq : 3 ≤ q) :
    (4 : ℤ) ^ q = 32 * edge q := by
  have hpow :
      (4 : ℤ) ^ q = (4 : ℤ) ^ (q - 1) * 4 := by
    conv_lhs =>
      rw [show q = (q - 1) + 1 by omega, pow_succ]
  calc
    (4 : ℤ) ^ q = (4 : ℤ) ^ (q - 1) * 4 := hpow
    _ = (8 * edge q) * 4 := by
      simp only [edge]
      rw [fourPow_pred_eq_eight_mul_edge hq]
    _ = 32 * edge q := by ring

theorem edge_succ {q : ℕ} (hq : 3 ≤ q) :
    edge (q + 1) = 4 * edge q := by
  have hscale := fourPow_eq_thirtyTwo_mul_edge hq
  calc
    edge (q + 1) = ((4 : ℤ) ^ q * 4) / 32 := by
      simp only [edge, pow_succ]
    _ = (32 * edge q * 4) / 32 := by rw [hscale]
    _ = (32 * (4 * edge q)) / 32 := by ring
    _ = 4 * edge q :=
      Int.mul_ediv_cancel_left _ (by norm_num : (32 : ℤ) ≠ 0)

theorem edge_add_two {q : ℕ} (hq : 3 ≤ q) :
    edge (q + 2) = 16 * edge q := by
  calc
    edge (q + 2) = edge ((q + 1) + 1) := by rfl
    _ = 4 * edge (q + 1) := edge_succ (q := q + 1) (by omega)
    _ = 16 * edge q := by rw [edge_succ hq]; ring

theorem edge_pos {q : ℕ} (hq : 3 ≤ q) : 0 < edge q := by
  have hpow : (0 : ℤ) < (4 : ℤ) ^ q := by positivity
  rw [fourPow_eq_thirtyTwo_mul_edge hq] at hpow
  omega

/-- Closed central Euclidean band versus absolute value of a centered
representative. -/
theorem centeredBand_iff_abs
    {M e z : ℤ} (hM : 0 < M)
    (hscale : M = 32 * e) (hz : |z| ≤ M / 2) :
    (M ≤ 32 * (z % M) ∧ 32 * (z % M) ≤ 31 * M) ↔ e ≤ |z| := by
  have hzBounds := abs_le.mp hz
  by_cases hz0 : 0 ≤ z
  · have hzM : z < M := by omega
    rw [Int.emod_eq_of_lt hz0 hzM, abs_of_nonneg hz0]
    omega
  · have hzn : z < 0 := lt_of_not_ge hz0
    have hzPlus0 : 0 ≤ z + M := by omega
    have hzPlusM : z + M < M := by omega
    have hzShift : z % M = (z + M) % M := by simp
    rw [hzShift, Int.emod_eq_of_lt hzPlus0 hzPlusM, abs_of_neg hzn]
    omega

/-- At every odd rank at least three, the half-word band is literally
escape of the actual centered state from its scale edge. -/
theorem halfWordBandAt_iff_state_abs
    {a q : ℕ} (ha : 2 ≤ a) (hq : 3 ≤ q) :
    PowerTwoOddHalfWordBandAt a q ↔ edge q ≤ |state a q| := by
  let M : ℤ := (4 : ℤ) ^ q
  have hM : 0 < M := by positivity
  have hscale : M = 32 * edge q := by
    simpa [M] using fourPow_eq_thirtyTwo_mul_edge hq
  have hz : |state a q| ≤ M / 2 := by
    simpa [state, M, actualOddHalfCenteredLift] using
      (abs_actualCenteredLift_le_half
        (A := diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
        (M := (4 : ℤ) ^ q) (by positivity))
  have hword :
      state a q % M = powerTwoOddHalfCorrectionWord a q % M := by
    simpa [state, M] using
      (actualOddHalfCenteredLift_modEq_halfCorrectionWord
        (a := a) (q := q) ha).eq
  change
    (M ≤ 32 * (powerTwoOddHalfCorrectionWord a q % M) ∧
      32 * (powerTwoOddHalfCorrectionWord a q % M) ≤ 31 * M) ↔
      edge q ≤ |state a q|
  rw [← hword]
  exact centeredBand_iff_abs hM hscale hz

/-- If the unwrapped affine successor is strictly in the target half-cell,
the actual centered successor equals it, not merely modulo that cell. -/
theorem state_succ_eq_affine_of_abs_lt_half
    {a q : ℕ} (ha : 2 ≤ a)
    (haffine :
      |4 * state a q + actualOddHalfCorrection a q| <
        (4 : ℤ) ^ (q + 1) / 2) :
    state a (q + 1) = 4 * state a q + actualOddHalfCorrection a q := by
  have hM : (0 : ℤ) < (4 : ℤ) ^ (q + 1) := by positivity
  have hstate : |state a (q + 1)| ≤ (4 : ℤ) ^ (q + 1) / 2 := by
    simpa [state, actualOddHalfCenteredLift] using
      (abs_actualCenteredLift_le_half
        (A := diagonalAdjacentSuffixRawBlock
          (2 ^ a) 0 (2 * (q + 1) + 1) / 2)
        (M := (4 : ℤ) ^ (q + 1)) hM)
  have hmod : Int.ModEq ((4 : ℤ) ^ (q + 1))
      (state a (q + 1))
      (4 * state a q + actualOddHalfCorrection a q) := by
    simpa [state] using
      ((actualOddHalfCenteredLift_modEq_halfCorrectionWord
        (a := a) (q := q + 1) ha).trans
        (actualOddHalf_affine_modEq_halfCorrectionWord_succ a q ha).symm)
  exact eq_of_modEq_of_centered_bounds hM hmod hstate haffine

/-- An edge state and a correction shorter than twice that edge cannot wrap
at the next base-four step. -/
theorem state_succ_eq_affine_of_edge_of_shortCorrection
    {a q : ℕ} (ha : 2 ≤ a) (hq : 3 ≤ q)
    (hstate : |state a q| < edge q)
    (hcorr : |actualOddHalfCorrection a q| < 2 * edge q) :
    state a (q + 1) = 4 * state a q + actualOddHalfCorrection a q := by
  have he : 0 < edge q := edge_pos hq
  have htriangle :
      |4 * state a q + actualOddHalfCorrection a q| ≤
        4 * |state a q| + |actualOddHalfCorrection a q| := by
    calc
      |4 * state a q + actualOddHalfCorrection a q| ≤
          |4 * state a q| + |actualOddHalfCorrection a q| := abs_add_le _ _
      _ = 4 * |state a q| + |actualOddHalfCorrection a q| := by
        rw [abs_mul]
        norm_num
  have hhalf : (4 : ℤ) ^ (q + 1) / 2 = 64 * edge q := by
    rw [pow_succ, fourPow_eq_thirtyTwo_mul_edge hq]
    rw [show 32 * edge q * 4 = 2 * (64 * edge q) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  apply state_succ_eq_affine_of_abs_lt_half ha
  rw [hhalf]
  omega

/-- A uniform `< 2e` correction envelope admits an all-edge affine orbit
starting at zero. -/
def zeroAffineOrbit (C : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => 4 * zeroAffineOrbit C n + C n

theorem zeroAffineOrbit_geometric_bound
    {e : ℤ} (C : ℕ → ℤ)
    (hC : ∀ n, |C n| < 2 * e) :
    ∀ j : ℕ,
      3 * |zeroAffineOrbit C j| ≤ 2 * e * ((4 : ℤ) ^ j - 1) := by
  intro j
  induction j with
  | zero => simp [zeroAffineOrbit]
  | succ j ih =>
      have htriangle :
          |zeroAffineOrbit C (j + 1)| ≤
            4 * |zeroAffineOrbit C j| + |C j| := by
        rw [zeroAffineOrbit]
        calc
          |4 * zeroAffineOrbit C j + C j| ≤
              |4 * zeroAffineOrbit C j| + |C j| := abs_add_le _ _
          _ = 4 * |zeroAffineOrbit C j| + |C j| := by
            rw [abs_mul]
            norm_num
      have hc := hC j
      rw [pow_succ]
      nlinarith

/-- The zero-start affine orbit remains inside every scaled edge tube.  Thus
no theorem using only a uniform `< 2e` correction envelope can force escape
by increasing the number of inspected ranks. -/
theorem zeroAffineOrbit_stays_in_scaled_edge
    {e : ℤ} (he : 0 < e) (C : ℕ → ℤ)
    (hC : ∀ n, |C n| < 2 * e) (j : ℕ) :
    |zeroAffineOrbit C j| < (4 : ℤ) ^ j * e := by
  have hgeom := zeroAffineOrbit_geometric_bound C hC j
  have hpow : (0 : ℤ) < (4 : ℤ) ^ j := by positivity
  nlinarith

/-- Exact replacement of the three half-word predicates by one affine
three-scale escape predicate.  Wrapping disappears conditionally on the
preceding edge hits. -/
theorem threeRankBandAt_iff_threeScaleAffineEscapeAt_of_shortCorrections
    {a q : ℕ} (ha : 2 ≤ a) (hq : 3 ≤ q)
    (hC : |actualOddHalfCorrection a q| < 2 * edge q)
    (hF : |actualOddHalfCorrection a (q + 1)| < 2 * edge q) :
    ThreeRankBandAt a q ↔ ThreeScaleAffineEscapeAt a q := by
  have hb0 := halfWordBandAt_iff_state_abs (a := a) (q := q) ha hq
  have hb1 :=
    halfWordBandAt_iff_state_abs (a := a) (q := q + 1) ha (by omega)
  have hb2 :=
    halfWordBandAt_iff_state_abs (a := a) (q := q + 2) ha (by omega)
  have he1 := edge_succ hq
  have he2 := edge_add_two hq
  have unwrap0 :
      ¬ PowerTwoOddHalfWordBandAt a q →
        state a (q + 1) = 4 * state a q + actualOddHalfCorrection a q := by
    intro hnot
    apply state_succ_eq_affine_of_edge_of_shortCorrection ha hq
    · have : ¬ edge q ≤ |state a q| := (not_congr hb0).mp hnot
      omega
    · exact hC
  have unwrap1 :
      ¬ PowerTwoOddHalfWordBandAt a (q + 1) →
        state a (q + 2) =
          4 * state a (q + 1) + actualOddHalfCorrection a (q + 1) := by
    intro hnot
    apply state_succ_eq_affine_of_edge_of_shortCorrection ha (by omega)
    · have : ¬ edge (q + 1) ≤ |state a (q + 1)| :=
        (not_congr hb1).mp hnot
      omega
    · rw [he1]
      have he := edge_pos hq
      omega
  constructor
  · intro hwindow
    by_cases h0 : PowerTwoOddHalfWordBandAt a q
    · exact Or.inl (hb0.mp h0)
    by_cases h1 : PowerTwoOddHalfWordBandAt a (q + 1)
    · right; left
      rw [← unwrap0 h0, ← he1]
      exact hb1.mp h1
    · right; right
      rcases hwindow with hwindow | hwindow | h2
      · exact (h0 hwindow).elim
      · exact (h1 hwindow).elim
      have hu0 := unwrap0 h0
      have hu1 := unwrap1 h1
      have hu2 :
          state a (q + 2) =
            16 * state a q + 4 * actualOddHalfCorrection a q +
              actualOddHalfCorrection a (q + 1) := by
        calc
          state a (q + 2) =
              4 * state a (q + 1) + actualOddHalfCorrection a (q + 1) := hu1
          _ = 4 * (4 * state a q + actualOddHalfCorrection a q) +
              actualOddHalfCorrection a (q + 1) := by rw [hu0]
          _ = 16 * state a q + 4 * actualOddHalfCorrection a q +
              actualOddHalfCorrection a (q + 1) := by ring
      rw [← hu2, ← he2]
      exact hb2.mp h2
  · intro hescape
    by_cases h0 : PowerTwoOddHalfWordBandAt a q
    · exact Or.inl h0
    by_cases h1 : PowerTwoOddHalfWordBandAt a (q + 1)
    · exact Or.inr (Or.inl h1)
    · right; right
      rcases hescape with hescape | hescape | hescape
      · exact (h0 (hb0.mpr hescape)).elim
      · have hu0 := unwrap0 h0
        rw [← hu0, ← he1] at hescape
        exact (h1 (hb1.mpr hescape)).elim
      · have hu0 := unwrap0 h0
        have hu1 := unwrap1 h1
        have hu2 :
            state a (q + 2) =
              16 * state a q + 4 * actualOddHalfCorrection a q +
                actualOddHalfCorrection a (q + 1) := by
          calc
            state a (q + 2) =
                4 * state a (q + 1) +
                  actualOddHalfCorrection a (q + 1) := hu1
            _ = 4 * (4 * state a q + actualOddHalfCorrection a q) +
                actualOddHalfCorrection a (q + 1) := by rw [hu0]
            _ = 16 * state a q + 4 * actualOddHalfCorrection a q +
                actualOddHalfCorrection a (q + 1) := by ring
        rw [← hu2, ← he2] at hescape
        exact hb2.mpr hescape

/-- Canonical wrapper: the elementary production bound supplies both short
corrections, so no additional magnitude premise remains. -/
theorem threeRankBandAt_iff_threeScaleAffineEscapeAt
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth :
      oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1) :
    ThreeRankBandAt a q ↔ ThreeScaleAffineEscapeAt a q := by
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hle := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hle
    omega
  obtain ⟨hC, hF⟩ :=
    abs_actualOddHalfCorrection_next_two_lt_two_canonicalEdge ha hdepth
  exact
    threeRankBandAt_iff_threeScaleAffineEscapeAt_of_shortCorrections
      ha hq hC hF

def ThreeScaleAffineEscapeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 2 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
      ThreeScaleAffineEscapeAt a q

/-- The flexible cofinal producer has no hidden residual beyond actual-state
three-scale affine escape. -/
theorem powerTwoOddGuardThreeRankBandSupply_iff_threeScaleAffineEscapeSupply :
    PowerTwoOddGuardThreeRankBandSupply ↔ ThreeScaleAffineEscapeSupply := by
  constructor
  · intro hsupply a₀
    obtain ⟨a, q, ha, hdepth, hband⟩ := hsupply a₀
    have ha2 : 2 ≤ a := (le_max_left 2 a₀).trans ha
    exact ⟨a, q, ha, hdepth,
      (threeRankBandAt_iff_threeScaleAffineEscapeAt ha2 hdepth).mp hband⟩
  · intro hsupply a₀
    obtain ⟨a, q, ha, hdepth, hescape⟩ := hsupply a₀
    have ha2 : 2 ≤ a := (le_max_left 2 a₀).trans ha
    exact ⟨a, q, ha, hdepth,
      (threeRankBandAt_iff_threeScaleAffineEscapeAt ha2 hdepth).mpr hescape⟩

/-- The exact affine escape supply closes Erdős #249 through the already
landed flexible three-rank consumer. -/
theorem irrational_totientSeries_of_threeScaleAffineEscapeSupply
    (hsupply : ThreeScaleAffineEscapeSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totientSeries_of_powerTwoOddGuardThreeRankBandSupply
  exact
    powerTwoOddGuardThreeRankBandSupply_iff_threeScaleAffineEscapeSupply.mpr
      hsupply

#print axioms eq_of_modEq_of_centered_bounds
#print axioms halfWordBandAt_iff_state_abs
#print axioms state_succ_eq_affine_of_edge_of_shortCorrection
#print axioms zeroAffineOrbit_stays_in_scaled_edge
#print axioms threeRankBandAt_iff_threeScaleAffineEscapeAt
#print axioms powerTwoOddGuardThreeRankBandSupply_iff_threeScaleAffineEscapeSupply
#print axioms irrational_totientSeries_of_threeScaleAffineEscapeSupply

end PowerTwoOddWindowAffine
end Erdos249257.DiagonalFreshLossBridge
