import Erdos257PeriodNoncollapse.SignedQMomentObstruction
import Mathlib.Tactic

/-!
# Erdős #249: a uniform obstruction to rank-one subrank extraction

Let `Θᵣ` be the Möbius--Mersenne ladder and let `t Y r` be its first `Y`
atoms.  The rank-one monomial Schur quotient

`(t Y (e + 2))² / t Y (2 * e + 2)`

does not approach `Θ₂`: for every `e ≥ 1` and `Y ≥ 4` it lies more than
`1 / 480` above `Θ₂`.  Thus this entire strict-subrank family cannot supply
the primitive rational linear forms needed to prove irrationality of the
binary totient series.

The proof is deliberately uniform.  Every rung `r ≥ 3` lies in the interval
`[1429/1512, 1)`, and every prefix after four atoms is within `1/3584` of
its rung.  Those two interval facts already force the quotient gap.
-/

namespace ErdosProblems.Erdos249.RankOneSubrankObstruction

open scoped BigOperators
open ArithmeticFunction
open Erdos257PeriodNoncollapse.SignedQMomentObstruction

/-- The first `Y` atoms of the Möbius--Mersenne rung `r`. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n

/-- The tail beginning immediately after the first `Y` atoms. -/
noncomputable def mobiusMersenneTailAfter (Y r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r (n + Y)

/-- The rank-one strict-subrank quotient from the first `Y` atoms. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)

private lemma two_pow_three_le_two_pow {r : ℕ} (hr : 3 ≤ r) :
    (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ r := by
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hr

private lemma geometric_base_le_eighth {r : ℕ} (hr : 3 ≤ r) :
    (1 : ℝ) / (2 : ℝ) ^ r ≤ 1 / 8 := by
  have hp := two_pow_three_le_two_pow hr
  norm_num at hp ⊢
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by positivity) hp)

private lemma norm_term_le_eighth_geometric
    {r : ℕ} (hr : 3 ≤ r) (n : ℕ) :
    ‖mobiusMersenneTerm r n‖ ≤ ((1 : ℝ) / 8) ^ n := by
  calc
    ‖mobiusMersenneTerm r n‖
        ≤ ((1 : ℝ) / (2 : ℝ) ^ r) ^ n :=
      norm_mobiusMersenneTerm_le_geometric r n
    _ ≤ ((1 : ℝ) / 8) ^ n :=
      pow_le_pow_left₀ (by positivity) (geometric_base_le_eighth hr) n

theorem mobiusMersenneTheta_eq_prefix_add_tail
    (Y r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r =
      mobiusMersennePrefix Y r + mobiusMersenneTailAfter Y r := by
  have hsplit :=
    (summable_mobiusMersenneTerm r hr).sum_add_tsum_nat_add Y
  rw [mobiusMersenneTheta, ← hsplit, mobiusMersennePrefix,
    mobiusMersenneTailAfter]

/-- Uniform prefix error: after four atoms, every rung `r ≥ 3` is within
`1/3584` of its finite prefix. -/
theorem abs_mobiusMersenneTheta_sub_prefix_le
    {Y r : ℕ} (hY : 4 ≤ Y) (hr : 3 ≤ r) :
    |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤
      (1 : ℝ) / 3584 := by
  have hsummable : Summable (mobiusMersenneTerm r) :=
    summable_mobiusMersenneTerm r (by omega)
  have htailSummable :
      Summable (fun n : ℕ => mobiusMersenneTerm r (n + Y)) :=
    hsummable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hgeo :
      Summable (fun n : ℕ => ((1 : ℝ) / 8) ^ (n + Y)) := by
    have h := summable_geometric_of_lt_one
      (by positivity : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
    exact (h.mul_left (((1 : ℝ) / 8) ^ Y)).congr
      (fun n => by rw [pow_add]; ring)
  have hterm : ∀ n : ℕ,
      |mobiusMersenneTerm r (n + Y)| ≤
        ((1 : ℝ) / 8) ^ (n + Y) := by
    intro n
    rw [← Real.norm_eq_abs]
    exact norm_term_le_eighth_geometric hr (n + Y)
  have habs :
      Summable (fun n : ℕ => |mobiusMersenneTerm r (n + Y)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hgeo
  have htail :
      |mobiusMersenneTailAfter Y r| ≤
        ∑' n : ℕ, ((1 : ℝ) / 8) ^ (n + Y) := by
    rw [mobiusMersenneTailAfter]
    have hupper :
        (∑' n : ℕ, mobiusMersenneTerm r (n + Y)) ≤
          ∑' n : ℕ, |mobiusMersenneTerm r (n + Y)| :=
      htailSummable.tsum_le_tsum (fun n => le_abs_self _) habs
    have hlower :
        -(∑' n : ℕ, mobiusMersenneTerm r (n + Y)) ≤
          ∑' n : ℕ, |mobiusMersenneTerm r (n + Y)| := by
      rw [← tsum_neg]
      exact htailSummable.neg.tsum_le_tsum
        (fun n => neg_le_abs _) habs
    calc
      |∑' n : ℕ, mobiusMersenneTerm r (n + Y)|
          ≤ ∑' n : ℕ, |mobiusMersenneTerm r (n + Y)| := by
        exact abs_le.mpr ⟨by linarith, hupper⟩
      _ ≤ ∑' n : ℕ, ((1 : ℝ) / 8) ^ (n + Y) :=
        habs.tsum_le_tsum hterm hgeo
  have hgeoValue :
      (∑' n : ℕ, ((1 : ℝ) / 8) ^ (n + Y)) =
        ((1 : ℝ) / 8) ^ Y / (1 - (1 : ℝ) / 8) := by
    calc
      (∑' n : ℕ, ((1 : ℝ) / 8) ^ (n + Y)) =
          ∑' n : ℕ, ((1 : ℝ) / 8) ^ Y * ((1 : ℝ) / 8) ^ n := by
            apply tsum_congr
            intro n
            rw [pow_add]
            ring
      _ = ((1 : ℝ) / 8) ^ Y *
          ∑' n : ℕ, ((1 : ℝ) / 8) ^ n := tsum_mul_left
      _ = ((1 : ℝ) / 8) ^ Y / (1 - (1 : ℝ) / 8) := by
        rw [tsum_geometric_of_lt_one
          (by positivity : (0 : ℝ) ≤ 1 / 8)
          (by norm_num : (1 : ℝ) / 8 < 1)]
        simp only [div_eq_mul_inv]
  have hpow :
      ((1 : ℝ) / 8) ^ Y ≤ ((1 : ℝ) / 8) ^ 4 :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hY
  rw [mobiusMersenneTheta_eq_prefix_add_tail Y r (by omega)]
  simp only [add_sub_cancel_left]
  rw [hgeoValue] at htail
  calc
    |mobiusMersenneTailAfter Y r|
        ≤ ((1 : ℝ) / 8) ^ Y / (1 - (1 : ℝ) / 8) := htail
    _ ≤ ((1 : ℝ) / 8) ^ 4 / (1 - (1 : ℝ) / 8) := by
      gcongr
    _ = (1 : ℝ) / 3584 := by norm_num

private lemma three_pow_lt_mersenne_product :
    ∀ r : ℕ, 3 ≤ r →
      (3 : ℝ) ^ r < (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) := by
  intro r hr
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction k with
  | zero => norm_num
  | succ k ih =>
      simp only [Nat.add_succ, pow_succ]
      have ih' := ih (by omega)
      have hpow : (1 : ℝ) ≤ 2 ^ (3 + k) :=
        one_le_pow₀ (by norm_num)
      nlinarith [sq_nonneg ((2 : ℝ) ^ (3 + k))]

/-- Every rung `r ≥ 3` is bounded below by the fixed rational
`1429/1512`. -/
theorem mobiusMersenneTheta_ge_alpha
    {r : ℕ} (hr : 3 ≤ r) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r := by
  have hsplit := mobiusMersenneTheta_eq_twoAtom_add_tail r (by omega)
  have htail := abs_mobiusMersenneTailAfterTwo_le_bound r (by omega)
  have hpow := two_pow_three_le_two_pow hr
  have hthreeNat : 3 ^ 3 ≤ 3 ^ r :=
    Nat.pow_le_pow_right (by norm_num : 0 < 3) hr
  have hthree : (27 : ℝ) ≤ (3 : ℝ) ^ r := by
    exact_mod_cast hthreeNat
  have hbound :
      mobiusMersenneTailBound r ≤ (1 : ℝ) / 56 := by
    unfold mobiusMersenneTailBound
    have hp8 : (8 : ℝ) ≤ (2 : ℝ) ^ r := by norm_num at hpow ⊢; exact hpow
    have hsub : (7 : ℝ) ≤ (2 : ℝ) ^ r - 1 := by linarith
    have hprod : (56 : ℝ) ≤
        (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) := by
      have hmul :=
        mul_le_mul hp8 hsub (by norm_num : (0 : ℝ) ≤ 7) (by positivity)
      norm_num at hmul
      exact hmul
    exact one_div_le_one_div_of_le (by norm_num) hprod
  unfold mobiusMersenneTwoAtom at hsplit
  have htailLower :
      -(mobiusMersenneTailBound r) ≤ mobiusMersenneTailAfterTwo r :=
    (abs_le.mp htail).1
  have hinv : 1 / (3 : ℝ) ^ r ≤ 1 / 27 :=
    one_div_le_one_div_of_le (by norm_num) hthree
  rw [hsplit]
  norm_num at *
  linarith

/-- Every rung `r ≥ 3` is strictly below `1`. -/
theorem mobiusMersenneTheta_lt_one
    {r : ℕ} (hr : 3 ≤ r) :
    mobiusMersenneTheta r < 1 := by
  have hsplit := mobiusMersenneTheta_eq_twoAtom_add_tail r (by omega)
  have htail := abs_mobiusMersenneTailAfterTwo_le_bound r (by omega)
  have hreal :
      (3 : ℝ) ^ r <
        (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) := by
    exact three_pow_lt_mersenne_product r hr
  have hden3 : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  have hden2 :
      (0 : ℝ) < (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) := by
    have : (1 : ℝ) < (2 : ℝ) ^ r :=
      one_lt_pow₀ (by norm_num) (by omega)
    exact mul_pos (by positivity) (sub_pos.mpr this)
  have hinv :
      mobiusMersenneTailBound r < 1 / (3 : ℝ) ^ r := by
    unfold mobiusMersenneTailBound
    exact one_div_lt_one_div_of_lt hden3 hreal
  have htailUpper :
      mobiusMersenneTailAfterTwo r ≤ mobiusMersenneTailBound r :=
    (abs_le.mp htail).2
  rw [hsplit]
  unfold mobiusMersenneTwoAtom
  linarith

/-- The target rung itself lies strictly below `8/9`. -/
theorem mobiusMersenneTheta_two_lt_eight_ninths :
    mobiusMersenneTheta 2 < (8 : ℝ) / 9 := by
  have hsplit := mobiusMersenneTheta_eq_prefixFive_add_tail 2 (by omega)
  have htail := abs_mobiusMersenneTailAfterFive_le 2 (by omega)
  have hupper :
      mobiusMersenneTailAfterFive 2 ≤
        mobiusMersenneTailBoundFive 2 :=
    (abs_le.mp htail).2
  rw [hsplit]
  unfold mobiusMersennePrefixFive mobiusMersenneTailBoundFive at *
  norm_num at *
  linarith

/-- **Uniform rank-one no-go.**  Every strict-subrank monomial quotient in
this family overshoots `Θ₂` by more than `1/480`. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  let a := mobiusMersennePrefix Y (e + 2)
  let b := mobiusMersennePrefix Y (2 * e + 2)
  let A := mobiusMersenneTheta (e + 2)
  let B := mobiusMersenneTheta (2 * e + 2)
  have hre : 3 ≤ e + 2 := by omega
  have hrb : 3 ≤ 2 * e + 2 := by omega
  have haerr :
      |A - a| ≤ (1 : ℝ) / 3584 :=
    abs_mobiusMersenneTheta_sub_prefix_le hY hre
  have hberr :
      |B - b| ≤ (1 : ℝ) / 3584 :=
    abs_mobiusMersenneTheta_sub_prefix_le hY hrb
  have hAlo : (1429 : ℝ) / 1512 ≤ A :=
    mobiusMersenneTheta_ge_alpha hre
  have hBlo : (1429 : ℝ) / 1512 ≤ B :=
    mobiusMersenneTheta_ge_alpha hrb
  have hBhi : B < 1 := mobiusMersenneTheta_lt_one hrb
  have halo :
      (1429 : ℝ) / 1512 - 1 / 3584 ≤ a := by
    have := (abs_le.mp haerr).2
    linarith
  have hbhi : b ≤ 1 + (1 : ℝ) / 3584 := by
    have := (abs_le.mp hberr).1
    linarith
  have hblo :
      (1429 : ℝ) / 1512 - 1 / 3584 ≤ b := by
    have := (abs_le.mp hberr).2
    linarith
  have hbpos : 0 < b := by
    norm_num at hblo ⊢
    linarith
  have hasq :
      ((1429 : ℝ) / 1512 - 1 / 3584) ^ 2 ≤ a ^ 2 := by
    have hapos :
        0 ≤ (1429 : ℝ) / 1512 - 1 / 3584 := by norm_num
    nlinarith
  have hnumeric :
      ((1 : ℝ) / 480 + 8 / 9) * (1 + 1 / 3584) <
        ((1429 : ℝ) / 1512 - 1 / 3584) ^ 2 := by
    norm_num
  have hcoeff :
      0 < (1 : ℝ) / 480 + 8 / 9 := by norm_num
  have hratio :
      (1 : ℝ) / 480 + 8 / 9 < a ^ 2 / b := by
    rw [lt_div_iff₀ hbpos]
    have hmul :
        ((1 : ℝ) / 480 + 8 / 9) * b ≤
          ((1 : ℝ) / 480 + 8 / 9) * (1 + 1 / 3584) :=
      mul_le_mul_of_nonneg_left hbhi hcoeff.le
    linarith
  have htheta := mobiusMersenneTheta_two_lt_eight_ninths
  unfold rankOneSubrankQuotient
  change (1 : ℝ) / 480 < a ^ 2 / b - mobiusMersenneTheta 2
  linarith

/-- Positive finite direct sums do not evade the obstruction: a positively
weighted average of admissible rank-one quotients still overshoots `Θ₂` by
more than `1/480`. -/
theorem positive_direct_sum_sub_theta_two_gt
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (1 : ℝ) / 480 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2 := by
  have hweight : 0 < ∑ i ∈ s, w i :=
    Finset.sum_pos hw hs
  have hsum :
      (∑ i ∈ s, w i *
          (mobiusMersenneTheta 2 + (1 : ℝ) / 480)) <
        ∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i) :=
    Finset.sum_lt_sum_of_nonempty hs fun i hi => by
      have hgap :=
        rankOneSubrankQuotient_sub_theta_two_gt
          (he i hi) (hY i hi)
      exact mul_lt_mul_of_pos_left (by linarith) (hw i hi)
  have hratio :
      mobiusMersenneTheta 2 + (1 : ℝ) / 480 <
        (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) := by
    rw [lt_div_iff₀ hweight]
    calc
      (mobiusMersenneTheta 2 + (1 : ℝ) / 480) * ∑ i ∈ s, w i =
          ∑ i ∈ s, w i *
            (mobiusMersenneTheta 2 + (1 : ℝ) / 480) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ < ∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i) := hsum
  linarith

/-- Primitive integer linear forms arising from these quotients are bounded
away from zero.  In fact the lower bound grows linearly with the denominator.
-/
theorem primitive_form_abs_gt
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot :
      rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) / 480 <
      |(q : ℝ) * mobiusMersenneTheta 2 - p| := by
  have hgap := rankOneSubrankQuotient_sub_theta_two_gt he hY
  rw [hquot] at hgap
  have hqpos : (0 : ℝ) < q := by positivity
  have hsigned :
      (q : ℝ) / 480 <
        (p : ℝ) - (q : ℝ) * mobiusMersenneTheta 2 := by
    have hrewrite :
        (p : ℝ) / q - mobiusMersenneTheta 2 =
          ((p : ℝ) - (q : ℝ) * mobiusMersenneTheta 2) / q := by
      field_simp [hqpos.ne']
    rw [hrewrite] at hgap
    have hm := (lt_div_iff₀ hqpos).mp hgap
    convert hm using 1 <;> ring
  rw [abs_sub_comm]
  exact lt_of_lt_of_le hsigned (le_abs_self _)

#print axioms abs_mobiusMersenneTheta_sub_prefix_le
#print axioms mobiusMersenneTheta_ge_alpha
#print axioms mobiusMersenneTheta_lt_one
#print axioms mobiusMersenneTheta_two_lt_eight_ninths
#print axioms rankOneSubrankQuotient_sub_theta_two_gt
#print axioms positive_direct_sum_sub_theta_two_gt
#print axioms primitive_form_abs_gt

end ErdosProblems.Erdos249.RankOneSubrankObstruction
