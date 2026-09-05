import Erdos249257.DiagonalFreshLossBridge

namespace Erdos249257.DiagonalFreshLossBridge

open TotientTailPeriodKiller

/-! A flexible three-rank #249 producer.

The canonical odd rank is only the first admissible analytic depth.  Once
the width inequality holds it persists under every later binary rank.  Thus
centrality at any of the first three odd ranks (the canonical odd rank and
the next two base-four ranks) feeds the existing adjacent-gap consumer.

This production adapter isolates the unresolved arithmetic theorem exactly as
exclusion of three consecutive edge hits in that window.
-/

/-- The analytic adjacent-gap width inequality persists for one more binary
rank. -/
theorem adjacentDyadicWidth_succ
    {t m : ℕ}
    (hwidth :
      32 * (3 * periodLcm t + 2 * (m + 3) : ℤ) < (2 : ℤ) ^ m) :
    32 * (3 * periodLcm t + 2 * ((m + 1) + 3) : ℤ) <
      (2 : ℤ) ^ (m + 1) := by
  let A : ℤ := 32 * (3 * periodLcm t + 2 * (m + 3) : ℤ)
  have hH : (0 : ℤ) < periodLcm t := by
    exact_mod_cast periodLcm_pos t
  have hA : 64 < A := by
    dsimp [A]
    omega
  have hnextA :
      (32 * (3 * periodLcm t + 2 * ((m + 1) + 3) : ℤ)) = A + 64 := by
    dsimp [A]
    ring
  have hnextPow : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by
    rw [pow_succ]
    ring
  rw [hnextA, hnextPow]
  change A < (2 : ℤ) ^ m at hwidth
  omega

/-- In particular the width remains valid at the next odd/base-four rank. -/
theorem adjacentDyadicWidth_add_two
    {t m : ℕ}
    (hwidth :
      32 * (3 * periodLcm t + 2 * (m + 3) : ℤ) < (2 : ℤ) ^ m) :
    32 * (3 * periodLcm t + 2 * ((m + 2) + 3) : ℤ) <
      (2 : ℤ) ^ (m + 2) := by
  have h1 := adjacentDyadicWidth_succ hwidth
  have h2 := adjacentDyadicWidth_succ h1
  simpa [Nat.add_assoc] using h2

/-- The exact half-word central band at one odd rank. -/
def PowerTwoOddHalfWordBandAt (a q : ℕ) : Prop :=
  (4 : ℤ) ^ q ≤
      32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ∧
    32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ≤
      31 * (4 : ℤ) ^ q

/-- One half-word band witness at an analytically admissible odd rank is an
exact witness for the existing adjacent-suffix gap interface. -/
theorem diagonalAdjacentSuffixGapWitness_of_powerTwoOddHalfWordBandAt
    {a q : ℕ} (ha : 2 ≤ a) (hq : 3 ≤ q)
    (hwidth :
      32 * (3 * periodLcm (2 ^ a) + 2 * ((2 * q + 1) + 3) : ℤ) <
        (2 : ℤ) ^ (2 * q + 1))
    (hband : PowerTwoOddHalfWordBandAt a q) :
    ∃ m : ℕ,
      5 ≤ m ∧
        32 * (3 * periodLcm (2 ^ a) + 2 * (m + 3) : ℤ) <
          (2 : ℤ) ^ m ∧
        (2 : ℤ) ^ (m - 5) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
          (2 : ℤ) ^ m - 2 ^ (m - 5) := by
  refine ⟨2 * q + 1, by omega, hwidth, ?_⟩
  exact
    (diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand
      ha hq).2 hband

/-- Cofinal centrality at any of the canonical odd rank or its next two
base-four successors.  This is strictly weaker than requiring the canonical
rank itself to be central. -/
def PowerTwoOddGuardThreeRankBandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 2 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    (PowerTwoOddHalfWordBandAt a q ∨
      PowerTwoOddHalfWordBandAt a (q + 1) ∨
      PowerTwoOddHalfWordBandAt a (q + 2))

/-- The three-rank producer supplies the landed adjacent-gap interface. -/
theorem diagonalAdjacentSuffixGapSupply_of_powerTwoOddGuardThreeRankBand
    (hsupply : PowerTwoOddGuardThreeRankBandSupply) :
    DiagonalAdjacentSuffixGapSupply := by
  intro t₀
  obtain ⟨a, q, ha, hdepth, hwindow⟩ := hsupply t₀
  have ha2 : 2 ≤ a := (le_max_left 2 t₀).trans ha
  have ht₀a : t₀ ≤ a := (le_max_right 2 t₀).trans ha
  have hat : a < 2 ^ a := Nat.lt_two_pow_self
  have ht : 3 ≤ 2 ^ a := by
    have hpow4 : 4 ≤ 2 ^ a := by
      simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) ha2)
    omega
  obtain ⟨hm, hwidth⟩ :=
    oddGuardedCanonicalAdjacentSuffixDepth_width ht
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hle := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hle
    omega
  rw [hdepth] at hm hwidth
  have hwidth1 :
      32 * (3 * periodLcm (2 ^ a) +
          2 * ((2 * (q + 1) + 1) + 3) : ℤ) <
        (2 : ℤ) ^ (2 * (q + 1) + 1) := by
    have h := adjacentDyadicWidth_add_two hwidth
    convert h using 1
  have hwidth2 :
      32 * (3 * periodLcm (2 ^ a) +
          2 * ((2 * (q + 2) + 1) + 3) : ℤ) <
        (2 : ℤ) ^ (2 * (q + 2) + 1) := by
    have h := adjacentDyadicWidth_add_two hwidth1
    convert h using 1
  refine ⟨2 ^ a, by omega, ?_⟩
  rcases hwindow with hq0 | hq1 | hq2
  · exact diagonalAdjacentSuffixGapWitness_of_powerTwoOddHalfWordBandAt
      ha2 hq hwidth hq0
  · exact diagonalAdjacentSuffixGapWitness_of_powerTwoOddHalfWordBandAt
      ha2 (by omega) hwidth1 hq1
  · exact diagonalAdjacentSuffixGapWitness_of_powerTwoOddHalfWordBandAt
      ha2 (by omega) hwidth2 hq2

/-- The flexible three-rank band producer therefore closes Erdős #249. -/
theorem irrational_totientSeries_of_powerTwoOddGuardThreeRankBandSupply
    (hsupply : PowerTwoOddGuardThreeRankBandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply
    (diagonalAdjacentSuffixGapSupply_of_powerTwoOddGuardThreeRankBand hsupply)

/-- The two corrections after the canonical odd rank are each below twice
the canonical edge.  This is the uniform magnitude input for the exact
three-edge core obstruction below. -/
theorem abs_actualOddHalfCorrection_next_two_lt_two_canonicalEdge
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth :
      oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1) :
    |actualOddHalfCorrection a q| < 2 * ((4 : ℤ) ^ q / 32) ∧
      |actualOddHalfCorrection a (q + 1)| <
        2 * ((4 : ℤ) ^ q / 32) := by
  let H := periodLcm (2 ^ a)
  let e : ℤ := (4 : ℤ) ^ q / 32
  let E : ℤ := 4 * H + 4 * q + 1
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hcanonGuard := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hcanonGuard
    omega
  have hH : (0 : ℤ) < H := by
    exact_mod_cast periodLcm_pos (2 ^ a)
  have hedge := canonicalActualOddHalfCorrectionEnvelope_lt_edge ha hdepth
  have hE : E < e := by
    dsimp [E, e, H]
    convert hedge using 1
    ring
  have hE8 : 8 < E := by
    dsimp [E]
    omega
  have hq0 := abs_actualOddHalfCorrection_le (a := a) (n := q) ha
  have hq1 := abs_actualOddHalfCorrection_le (a := a) (n := q + 1) ha
  dsimp [E, H] at hq0 hq1
  change |actualOddHalfCorrection a q| < 2 * e ∧
    |actualOddHalfCorrection a (q + 1)| < 2 * e
  constructor <;> omega

/-- Edge occupation is exactly failure of the closed central half-word
band. -/
def PowerTwoOddHalfWordEdgeAt (a q : ℕ) : Prop :=
  ¬ PowerTwoOddHalfWordBandAt a q

/-- The arithmetic boundary of the flexible producer is literally a run of
three consecutive edge occupations; no extra modular or width condition is
hidden in this reformulation. -/
theorem not_three_consecutive_edge_iff_threeRankBand
    (a q : ℕ) :
    ¬ (PowerTwoOddHalfWordEdgeAt a q ∧
        PowerTwoOddHalfWordEdgeAt a (q + 1) ∧
        PowerTwoOddHalfWordEdgeAt a (q + 2)) ↔
      (PowerTwoOddHalfWordBandAt a q ∨
        PowerTwoOddHalfWordBandAt a (q + 1) ∨
        PowerTwoOddHalfWordBandAt a (q + 2)) := by
  simp only [PowerTwoOddHalfWordEdgeAt]
  tauto

/-- Exact local no-go for a correction-envelope-only proof of the new
three-rank producer.  Even two nonzero sub-edge corrections are compatible
with three consecutive edge tubes: the old state may sit at the zero lift.
Any proof of no-three for the actual power-two orbit must therefore use an
arithmetic state/correction relation, not only the two magnitude envelopes. -/
theorem threeEdgeWindow_feasible_at_zero_of_subedge
    {e C F : ℤ} (he : 0 < e)
    (hC : |C| < e) (hF : |F| < 4 * e) :
    |(0 : ℤ)| < e ∧
      |4 * (0 : ℤ) + C| < 4 * e ∧
      |16 * (0 : ℤ) + 4 * C + F| < 16 * e := by
  have hCF : |4 * C + F| ≤ 4 * |C| + |F| := by
    calc
      |4 * C + F| ≤ |4 * C| + |F| := abs_add_le _ _
      _ = 4 * |C| + |F| := by
        rw [abs_mul]
        norm_num
  constructor
  · simpa using he
  constructor
  · simpa using (lt_of_lt_of_le hC (by omega : e ≤ 4 * e))
  · simpa using hCF.trans_lt (by omega)

/-- A quantitative version of the same no-go.  The whole radius-`e/2` core
of the canonical edge is trapped for three ranks by sub-edge corrections.
Consequently, any no-three theorem obtained in this window must at least
exclude `2 * |state| < e`; the flexible producer relaxes the old radius `e`
obstruction, but it does not turn into a correction-only argument. -/
theorem threeEdgeWindow_forced_of_halfEdgeCore
    {e s C F : ℤ} (he : 0 < e)
    (hs : 2 * |s| < e)
    (hC : |C| < e) (hF : |F| < 4 * e) :
    |s| < e ∧
      |4 * s + C| < 4 * e ∧
      |16 * s + 4 * C + F| < 16 * e := by
  have hfirst : |s| < e := by
    have hs0 : 0 ≤ |s| := abs_nonneg s
    omega
  have hsecondBound : |4 * s + C| ≤ 4 * |s| + |C| := by
    calc
      |4 * s + C| ≤ |4 * s| + |C| := abs_add_le _ _
      _ = 4 * |s| + |C| := by
        rw [abs_mul]
        norm_num
  have hthirdBound :
      |16 * s + 4 * C + F| ≤ 16 * |s| + 4 * |C| + |F| := by
    calc
      |16 * s + 4 * C + F| ≤ |16 * s + 4 * C| + |F| :=
        abs_add_le _ _
      _ ≤ (|16 * s| + |4 * C|) + |F| := by
        gcongr
        exact abs_add_le _ _
      _ = 16 * |s| + 4 * |C| + |F| := by
        rw [abs_mul, abs_mul]
        norm_num
  refine ⟨hfirst, hsecondBound.trans_lt ?_, hthirdBound.trans_lt ?_⟩ <;>
    omega

/-- Version tuned to the elementary post-canonical correction bounds.  If
each of the next two corrections is only known to be below `2e`, the radius
`3e/8` core still forces all three edge hits. -/
theorem threeEdgeWindow_forced_of_threeEighthCore
    {e s C F : ℤ} (he : 0 < e)
    (hs : 8 * |s| < 3 * e)
    (hC : |C| < 2 * e) (hF : |F| < 2 * e) :
    |s| < e ∧
      |4 * s + C| < 4 * e ∧
      |16 * s + 4 * C + F| < 16 * e := by
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hsecondBound : |4 * s + C| ≤ 4 * |s| + |C| := by
    calc
      |4 * s + C| ≤ |4 * s| + |C| := abs_add_le _ _
      _ = 4 * |s| + |C| := by
        rw [abs_mul]
        norm_num
  have hthirdBound :
      |16 * s + 4 * C + F| ≤ 16 * |s| + 4 * |C| + |F| := by
    calc
      |16 * s + 4 * C + F| ≤ |16 * s + 4 * C| + |F| :=
        abs_add_le _ _
      _ ≤ (|16 * s| + |4 * C|) + |F| := by
        gcongr
        exact abs_add_le _ _
      _ = 16 * |s| + 4 * |C| + |F| := by
        rw [abs_mul, abs_mul]
        norm_num
  refine ⟨by omega, hsecondBound.trans_lt ?_, hthirdBound.trans_lt ?_⟩ <;>
    omega

#print axioms adjacentDyadicWidth_succ
#print axioms diagonalAdjacentSuffixGapSupply_of_powerTwoOddGuardThreeRankBand
#print axioms irrational_totientSeries_of_powerTwoOddGuardThreeRankBandSupply
#print axioms abs_actualOddHalfCorrection_next_two_lt_two_canonicalEdge
#print axioms not_three_consecutive_edge_iff_threeRankBand
#print axioms threeEdgeWindow_feasible_at_zero_of_subedge
#print axioms threeEdgeWindow_forced_of_halfEdgeCore
#print axioms threeEdgeWindow_forced_of_threeEighthCore

end Erdos249257.DiagonalFreshLossBridge
