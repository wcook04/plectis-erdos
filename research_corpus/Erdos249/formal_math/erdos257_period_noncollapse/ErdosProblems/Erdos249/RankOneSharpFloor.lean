import ErdosProblems.Erdos249.RankOneSubrankObstruction

/-!
# Erdős #249: the sharp floor of the positive rank-one Schur cone

The uniform interval argument in `RankOneSubrankObstruction` certifies a gap
of more than `1/480`.  Exact finite prefixes give a sharper picture: among
all admissible pairs `e ≥ 1`, `Y ≥ 4`, the monomial quotient is uniquely
minimised at the five-atom first-depth kernel `(e, Y) = (1, 5)`, and the
gap to `Θ₂` is more than `21/320`.  Consequently `1/16` is a uniform unit
fraction lower bound, while `1/15` fails at the minimiser.

This does not decide Erdős #249.  It only prices the positive rank-one
family exactly.
-/

namespace ErdosProblems.Erdos249.RankOneSubrankObstruction

open scoped BigOperators
open ArithmeticFunction
open Erdos257PeriodNoncollapse.SignedQMomentObstruction

/-! ## Möbius atoms `d = 1, …, 7` -/

private lemma moebius_one : moebius 1 = 1 := moebius_apply_one

private lemma moebius_two : moebius 2 = -1 :=
  moebius_apply_prime (by norm_num : Nat.Prime 2)

private lemma moebius_three : moebius 3 = -1 :=
  moebius_apply_prime (by norm_num : Nat.Prime 3)

private lemma moebius_four : moebius 4 = 0 := by
  have h := moebius_apply_prime_pow (p := 2) (k := 2)
    (by norm_num : Nat.Prime 2) (by norm_num)
  norm_num at h
  simpa using h

private lemma moebius_five : moebius 5 = -1 :=
  moebius_apply_prime (by norm_num : Nat.Prime 5)

private lemma moebius_six : moebius 6 = 1 := by
  calc
    moebius 6 = moebius 2 * moebius 3 := by
      simpa using
        isMultiplicative_moebius.map_mul_of_coprime
          (by norm_num : Nat.Coprime 2 3)
    _ = 1 := by
      rw [moebius_two, moebius_three]
      norm_num

private lemma moebius_seven : moebius 7 = -1 :=
  moebius_apply_prime (by norm_num : Nat.Prime 7)

private lemma term_zero (r : ℕ) : mobiusMersenneTerm r 0 = 1 := by
  rw [mobiusMersenneTerm, moebius_one]
  norm_num [one_pow]

private lemma term_one (r : ℕ) :
    mobiusMersenneTerm r 1 = -(1 / (3 : ℝ) ^ r) := by
  rw [mobiusMersenneTerm, moebius_two]
  norm_num [div_eq_mul_inv]

private lemma term_two (r : ℕ) :
    mobiusMersenneTerm r 2 = -(1 / (7 : ℝ) ^ r) := by
  rw [mobiusMersenneTerm, moebius_three]
  norm_num [div_eq_mul_inv]

private lemma term_three (r : ℕ) : mobiusMersenneTerm r 3 = 0 := by
  simp [mobiusMersenneTerm, moebius_four]

private lemma term_four (r : ℕ) :
    mobiusMersenneTerm r 4 = -(1 / (31 : ℝ) ^ r) := by
  rw [mobiusMersenneTerm, moebius_five]
  norm_num [div_eq_mul_inv]

private lemma term_five (r : ℕ) :
    mobiusMersenneTerm r 5 = 1 / (63 : ℝ) ^ r := by
  rw [mobiusMersenneTerm, moebius_six]
  norm_num [div_eq_mul_inv]

private lemma term_six (r : ℕ) :
    mobiusMersenneTerm r 6 = -(1 / (127 : ℝ) ^ r) := by
  rw [mobiusMersenneTerm, moebius_seven]
  norm_num [div_eq_mul_inv]

/-! ## Closed prefixes -/

theorem mobiusMersennePrefix_four (r : ℕ) :
    mobiusMersennePrefix 4 r =
      1 - 1 / (3 : ℝ) ^ r - 1 / (7 : ℝ) ^ r := by
  unfold mobiusMersennePrefix
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    term_zero, term_one, term_two, term_three]
  ring

theorem mobiusMersennePrefix_five_eq (r : ℕ) :
    mobiusMersennePrefix 5 r = mobiusMersennePrefixFive r := by
  unfold mobiusMersennePrefix mobiusMersennePrefixFive
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, term_zero, term_one, term_two, term_three, term_four]
  ring

theorem mobiusMersennePrefix_six (r : ℕ) :
    mobiusMersennePrefix 6 r =
      mobiusMersennePrefixFive r + 1 / (63 : ℝ) ^ r := by
  unfold mobiusMersennePrefix
  rw [Finset.sum_range_succ]
  change mobiusMersennePrefix 5 r + mobiusMersenneTerm r 5 = _
  rw [mobiusMersennePrefix_five_eq, term_five]

theorem mobiusMersennePrefix_seven (r : ℕ) :
    mobiusMersennePrefix 7 r =
      mobiusMersennePrefixFive r + 1 / (63 : ℝ) ^ r -
        1 / (127 : ℝ) ^ r := by
  unfold mobiusMersennePrefix
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  change
      mobiusMersennePrefix 5 r + mobiusMersenneTerm r 5 +
          mobiusMersenneTerm r 6 =
        _
  rw [mobiusMersennePrefix_five_eq, term_five, term_six]
  ring

/-! ## Geometric tail of a finite prefix -/

/-- Geometric majorant of the tail after the first `Y` atoms. -/
noncomputable def geometricPrefixTail (r Y : ℕ) : ℝ :=
  ((1 : ℝ) / (2 : ℝ) ^ r) ^ Y / (1 - (1 : ℝ) / (2 : ℝ) ^ r)

theorem abs_mobiusMersenneTheta_sub_prefix_le_geometric
    (Y r : ℕ) (hr : 1 ≤ r) :
    |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤
      geometricPrefixTail r Y := by
  let q : ℝ := (1 : ℝ) / (2 : ℝ) ^ r
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
      one_lt_pow₀ (by norm_num) (by omega)
    exact (div_lt_one (by positivity)).2 hp
  have hsummable : Summable (mobiusMersenneTerm r) :=
    summable_mobiusMersenneTerm r hr
  have htailSummable :
      Summable (fun n : ℕ => mobiusMersenneTerm r (n + Y)) :=
    hsummable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hgeo : Summable (fun n : ℕ => q ^ (n + Y)) := by
    have h := summable_geometric_of_lt_one hq0 hq1
    exact (h.mul_left (q ^ Y)).congr (fun n => by rw [pow_add]; ring)
  have hterm : ∀ n : ℕ,
      |mobiusMersenneTerm r (n + Y)| ≤ q ^ (n + Y) := by
    intro n
    rw [← Real.norm_eq_abs]
    simpa [q] using norm_mobiusMersenneTerm_le_geometric r (n + Y)
  have habs :
      Summable (fun n : ℕ => |mobiusMersenneTerm r (n + Y)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hgeo
  have htail :
      |mobiusMersenneTailAfter Y r| ≤ ∑' n : ℕ, q ^ (n + Y) := by
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
          ≤ ∑' n : ℕ, |mobiusMersenneTerm r (n + Y)| :=
        abs_le.mpr ⟨by linarith, hupper⟩
      _ ≤ ∑' n : ℕ, q ^ (n + Y) :=
        habs.tsum_le_tsum hterm hgeo
  have hgeoValue :
      (∑' n : ℕ, q ^ (n + Y)) = q ^ Y / (1 - q) := by
    calc
      (∑' n : ℕ, q ^ (n + Y)) =
          ∑' n : ℕ, q ^ Y * q ^ n := by
            apply tsum_congr
            intro n
            rw [pow_add]
            ring
      _ = q ^ Y * ∑' n : ℕ, q ^ n := tsum_mul_left
      _ = q ^ Y / (1 - q) := by
        rw [tsum_geometric_of_lt_one hq0 hq1]
        simp only [div_eq_mul_inv]
  rw [mobiusMersenneTheta_eq_prefix_add_tail Y r hr]
  simp only [add_sub_cancel_left]
  unfold geometricPrefixTail
  simpa [q] using (htail.trans_eq hgeoValue)

private lemma prefix_sub_of_le {Y Z r : ℕ} (h : Z ≤ Y) :
    mobiusMersennePrefix Y r - mobiusMersennePrefix Z r =
      ∑ n ∈ Finset.Ico Z Y, mobiusMersenneTerm r n := by
  unfold mobiusMersennePrefix
  have hsum :=
    Finset.sum_range_add_sum_Ico (f := mobiusMersenneTerm r) h
  linarith

theorem abs_prefix_sub_le_geometric
    {Y Z r : ℕ} (hYZ : Z ≤ Y) (hr : 1 ≤ r) :
    |mobiusMersennePrefix Y r - mobiusMersennePrefix Z r| ≤
      geometricPrefixTail r Z := by
  let q : ℝ := (1 : ℝ) / (2 : ℝ) ^ r
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    have hp : (1 : ℝ) < (2 : ℝ) ^ r :=
      one_lt_pow₀ (by norm_num) (by omega)
    exact (div_lt_one (by positivity)).2 hp
  have hgeo : Summable fun n : ℕ => q ^ n :=
    summable_geometric_of_lt_one hq0 hq1
  have hdiff := prefix_sub_of_le (r := r) hYZ
  have hterm : ∀ n, |mobiusMersenneTerm r n| ≤ q ^ n := by
    intro n
    rw [← Real.norm_eq_abs]
    simpa [q] using norm_mobiusMersenneTerm_le_geometric r n
  have habs :
      |∑ n ∈ Finset.Ico Z Y, mobiusMersenneTerm r n| ≤
        ∑ n ∈ Finset.Ico Z Y, q ^ n :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun n _ => hterm n)
  have hshift :
      ∑ n ∈ Finset.Ico Z Y, q ^ n =
        q ^ Z * ∑ i ∈ Finset.range (Y - Z), q ^ i := by
    have hIco :
        ∑ n ∈ Finset.Ico Z Y, q ^ n =
          ∑ i ∈ Finset.range (Y - Z), q ^ (Z + i) :=
      Finset.sum_Ico_eq_sum_range (fun n => q ^ n) Z Y
    rw [hIco, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add]
  have hgeom :
      ∑ i ∈ Finset.range (Y - Z), q ^ i ≤ ∑' i : ℕ, q ^ i :=
    hgeo.sum_le_tsum _ (fun i _ => pow_nonneg hq0 i)
  have htsum : (∑' i : ℕ, q ^ i) = (1 - q)⁻¹ :=
    tsum_geometric_of_lt_one hq0 hq1
  have hbound :
      ∑ n ∈ Finset.Ico Z Y, q ^ n ≤ q ^ Z / (1 - q) := by
    calc
      ∑ n ∈ Finset.Ico Z Y, q ^ n =
          q ^ Z * ∑ i ∈ Finset.range (Y - Z), q ^ i := hshift
      _ ≤ q ^ Z * ∑' i : ℕ, q ^ i :=
        mul_le_mul_of_nonneg_left hgeom (pow_nonneg hq0 Z)
      _ = q ^ Z / (1 - q) := by
        rw [htsum, inv_eq_one_div]
        ring
  rw [hdiff]
  unfold geometricPrefixTail
  simpa [q] using habs.trans hbound

/-! ## Exact five-atom first-depth quotient -/

theorem rankOneSubrankQuotient_one_five :
    rankOneSubrankQuotient 1 5 =
      (35076077250375200 : ℝ) / 37573118933633199 := by
  have ha :
      mobiusMersennePrefix 5 3 = (264862520 : ℝ) / 275894451 := by
    rw [mobiusMersennePrefix_five_eq]
    unfold mobiusMersennePrefixFive
    norm_num
  have hb :
      mobiusMersennePrefix 5 4 = (177314913998 : ℝ) / 179607287601 := by
    rw [mobiusMersennePrefix_five_eq]
    unfold mobiusMersennePrefixFive
    norm_num
  unfold rankOneSubrankQuotient
  rw [ha, hb]
  norm_num

/-! ## Unique minimiser: the `e = 1` ray -/

theorem rankOneSubrankQuotient_one_four_gt_one_five :
    rankOneSubrankQuotient 1 5 < rankOneSubrankQuotient 1 4 := by
  have ha4 :
      mobiusMersennePrefix 4 3 = (8891 : ℝ) / 9261 := by
    rw [mobiusMersennePrefix_four]; norm_num
  have hb4 :
      mobiusMersennePrefix 4 4 = (191999 : ℝ) / 194481 := by
    rw [mobiusMersennePrefix_four]; norm_num
  have hQ4 :
      rankOneSubrankQuotient 1 4 = (79049881 : ℝ) / 84671559 := by
    unfold rankOneSubrankQuotient
    rw [ha4, hb4]
    norm_num
  rw [rankOneSubrankQuotient_one_five, hQ4]
  norm_num

theorem rankOneSubrankQuotient_one_six_gt_one_five :
    rankOneSubrankQuotient 1 5 < rankOneSubrankQuotient 1 6 := by
  have ha6 :
      mobiusMersennePrefix 6 3 = (1021616833 : ℝ) / 1064164311 := by
    rw [mobiusMersennePrefix_six]
    unfold mobiusMersennePrefixFive
    norm_num
  have hb6 :
      mobiusMersennePrefix 6 4 =
        (14362508957359 : ℝ) / 14548190295681 := by
    rw [mobiusMersennePrefix_six]
    unfold mobiusMersennePrefixFive
    norm_num
  have hQ6 :
      rankOneSubrankQuotient 1 6 =
        (1043700953468949889 : ℝ) / 1117992059749781919 := by
    unfold rankOneSubrankQuotient
    rw [ha6, hb6]
    norm_num
  rw [rankOneSubrankQuotient_one_five, hQ6]
  norm_num

private lemma prefix_seven_three :
    mobiusMersennePrefix 7 3 =
      (2092661489066728 : ℝ) / 2179816083859113 := by
  rw [mobiusMersennePrefix_seven]
  unfold mobiusMersennePrefixFive
  norm_num

private lemma prefix_seven_four :
    mobiusMersennePrefix 7 4 =
      (3736329722023251067438 : ℝ) / 3784633741669617595521 := by
  rw [mobiusMersennePrefix_seven]
  unfold mobiusMersennePrefixFive
  norm_num

private lemma geometricPrefixTail_three_seven :
    geometricPrefixTail 3 7 = (1 : ℝ) / 1835008 := by
  unfold geometricPrefixTail
  norm_num

private lemma geometricPrefixTail_four_seven :
    geometricPrefixTail 4 7 = (1 : ℝ) / 251658240 := by
  unfold geometricPrefixTail
  norm_num

theorem rankOneSubrankQuotient_one_ge_seven_gt_one_five
    {Y : ℕ} (hY : 7 ≤ Y) :
    rankOneSubrankQuotient 1 5 < rankOneSubrankQuotient 1 Y := by
  let a := mobiusMersennePrefix Y 3
  let b := mobiusMersennePrefix Y 4
  have haerr :=
    abs_prefix_sub_le_geometric (Y := Y) (Z := 7) (r := 3) hY (by omega)
  have hberr :=
    abs_prefix_sub_le_geometric (Y := Y) (Z := 7) (r := 4) hY (by omega)
  have halo :
      (2092661489066728 : ℝ) / 2179816083859113 - 1 / 1835008 ≤ a := by
    have := (abs_le.mp haerr).1
    rw [prefix_seven_three, geometricPrefixTail_three_seven] at this
    linarith
  have hbhi :
      b ≤
        (3736329722023251067438 : ℝ) / 3784633741669617595521 +
          1 / 251658240 := by
    have := (abs_le.mp hberr).2
    rw [prefix_seven_four, geometricPrefixTail_four_seven] at this
    linarith
  have hblo :
      (3736329722023251067438 : ℝ) / 3784633741669617595521 -
          1 / 251658240 ≤ b := by
    have := (abs_le.mp hberr).1
    rw [prefix_seven_four, geometricPrefixTail_four_seven] at this
    linarith
  have ha0pos :
      0 ≤
        (2092661489066728 : ℝ) / 2179816083859113 - 1 / 1835008 := by
    norm_num
  have hbpos : 0 < b := by
    have : 0 <
        (3736329722023251067438 : ℝ) / 3784633741669617595521 -
          1 / 251658240 := by
      norm_num
    linarith
  have hasq :
      ((2092661489066728 : ℝ) / 2179816083859113 - 1 / 1835008) ^ 2 ≤
        a ^ 2 := by
    nlinarith
  have hfloor :
      ((2092661489066728 : ℝ) / 2179816083859113 - 1 / 1835008) ^ 2 /
          ((3736329722023251067438 : ℝ) / 3784633741669617595521 +
            1 / 251658240) >
        (35076077250375200 : ℝ) / 37573118933633199 := by
    norm_num
  have h1 :
      ((2092661489066728 : ℝ) / 2179816083859113 - 1 / 1835008) ^ 2 /
          ((3736329722023251067438 : ℝ) / 3784633741669617595521 +
            1 / 251658240) ≤
        ((2092661489066728 : ℝ) / 2179816083859113 - 1 / 1835008) ^ 2 /
          b :=
    div_le_div_of_nonneg_left (sq_nonneg _) hbpos hbhi
  have h2 :
      ((2092661489066728 : ℝ) / 2179816083859113 - 1 / 1835008) ^ 2 / b ≤
        a ^ 2 / b :=
    div_le_div_of_nonneg_right hasq hbpos.le
  have hQeq := rankOneSubrankQuotient_one_five
  have hQ : rankOneSubrankQuotient 1 Y = a ^ 2 / b := rfl
  rw [hQeq, hQ]
  linarith

/-! ## Unique minimiser: depths `e ≥ 2` -/

theorem mobiusMersenneTheta_ge_alpha4 {r : ℕ} (hr : 4 ≤ r) :
    (6373 : ℝ) / 6480 ≤ mobiusMersenneTheta r := by
  have hsplit := mobiusMersenneTheta_eq_twoAtom_add_tail r (by omega)
  have htail := abs_mobiusMersenneTailAfterTwo_le_bound r (by omega)
  have hpow3 : (81 : ℝ) ≤ (3 : ℝ) ^ r := by
    have h := Nat.pow_le_pow_right (by norm_num : 0 < 3) hr
    exact_mod_cast h
  have hpow2 : (16 : ℝ) ≤ (2 : ℝ) ^ r := by
    have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) hr
    exact_mod_cast h
  have hinv3 : 1 / (3 : ℝ) ^ r ≤ 1 / 81 :=
    one_div_le_one_div_of_le (by positivity) hpow3
  have htb : mobiusMersenneTailBound r ≤ (1 : ℝ) / 240 := by
    unfold mobiusMersenneTailBound
    have hsub : (15 : ℝ) ≤ (2 : ℝ) ^ r - 1 := by linarith
    have hprod : (240 : ℝ) ≤ (2 : ℝ) ^ r * ((2 : ℝ) ^ r - 1) := by
      have := mul_le_mul hpow2 hsub (by norm_num) (by positivity)
      norm_num at this ⊢
      exact this
    exact one_div_le_one_div_of_le (by positivity) hprod
  have htailLower :
      -(mobiusMersenneTailBound r) ≤ mobiusMersenneTailAfterTwo r :=
    (abs_le.mp htail).1
  rw [hsplit]
  unfold mobiusMersenneTwoAtom
  linarith

private lemma two_pow_four_le {r : ℕ} (hr : 4 ≤ r) :
    (16 : ℝ) ≤ (2 : ℝ) ^ r := by
  have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) hr
  exact_mod_cast h

theorem abs_theta_sub_prefix_le_of_rung_four
    {Y r : ℕ} (hY : 4 ≤ Y) (hr : 4 ≤ r) :
    |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤
      (1 : ℝ) / 61440 := by
  have hgeo :=
    abs_mobiusMersenneTheta_sub_prefix_le_geometric Y r (by omega)
  have hq : (1 : ℝ) / (2 : ℝ) ^ r ≤ 1 / 16 :=
    one_div_le_one_div_of_le (by positivity) (two_pow_four_le hr)
  have hq0 : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ r := by positivity
  have hpow :
      ((1 : ℝ) / (2 : ℝ) ^ r) ^ Y ≤ ((1 : ℝ) / 16) ^ Y :=
    pow_le_pow_left₀ hq0 hq Y
  have hpowY :
      ((1 : ℝ) / 16) ^ Y ≤ ((1 : ℝ) / 16) ^ 4 :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hY
  have hden :
      1 - (1 : ℝ) / 16 ≤ 1 - (1 : ℝ) / (2 : ℝ) ^ r := by linarith
  have hden16 : (0 : ℝ) < 1 - (1 : ℝ) / 16 := by norm_num
  have hfrac :
      geometricPrefixTail r Y ≤
        ((1 : ℝ) / 16) ^ 4 / (1 - 1 / 16) := by
    unfold geometricPrefixTail
    have hnum := hpow.trans hpowY
    have hleft :
        ((1 : ℝ) / (2 : ℝ) ^ r) ^ Y / (1 - (1 : ℝ) / (2 : ℝ) ^ r) ≤
          ((1 : ℝ) / (2 : ℝ) ^ r) ^ Y / (1 - 1 / 16) :=
      div_le_div_of_nonneg_left (pow_nonneg hq0 Y) hden16 hden
    have hright :
        ((1 : ℝ) / (2 : ℝ) ^ r) ^ Y / (1 - 1 / 16) ≤
          ((1 : ℝ) / 16) ^ 4 / (1 - 1 / 16) :=
      div_le_div_of_nonneg_right hnum hden16.le
    exact hleft.trans hright
  have hval : ((1 : ℝ) / 16) ^ 4 / (1 - 1 / 16) = 1 / 61440 := by
    norm_num
  exact hgeo.trans (hfrac.trans_eq hval)

theorem rankOneSubrankQuotient_two_le_e_gt_one_five
    {e Y : ℕ} (he : 2 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient 1 5 < rankOneSubrankQuotient e Y := by
  let a := mobiusMersennePrefix Y (e + 2)
  let b := mobiusMersennePrefix Y (2 * e + 2)
  have hre : 4 ≤ e + 2 := by omega
  have haerr := abs_theta_sub_prefix_le_of_rung_four hY hre
  have hberr :=
    abs_theta_sub_prefix_le_of_rung_four hY (by omega : 4 ≤ 2 * e + 2)
  have hAlo := mobiusMersenneTheta_ge_alpha4 hre
  have hBhi := mobiusMersenneTheta_lt_one (by omega : 3 ≤ 2 * e + 2)
  have halo : (6373 : ℝ) / 6480 - 1 / 61440 ≤ a := by
    have := (abs_le.mp haerr).2
    linarith
  have hbhi : b ≤ 1 + (1 : ℝ) / 61440 := by
    have := (abs_le.mp hberr).1
    linarith
  have hblo : (6373 : ℝ) / 6480 - 1 / 61440 ≤ b := by
    have hBlo :=
      mobiusMersenneTheta_ge_alpha4 (by omega : 4 ≤ 2 * e + 2)
    have := (abs_le.mp hberr).2
    linarith
  have hbpos : 0 < b := by
    have : 0 < (6373 : ℝ) / 6480 - 1 / 61440 := by norm_num
    linarith
  have hasq :
      ((6373 : ℝ) / 6480 - 1 / 61440) ^ 2 ≤ a ^ 2 := by
    have ha0pos : 0 ≤ (6373 : ℝ) / 6480 - 1 / 61440 := by norm_num
    nlinarith
  have hfloor :
      ((6373 : ℝ) / 6480 - 1 / 61440) ^ 2 / (1 + (1 : ℝ) / 61440) >
        (35076077250375200 : ℝ) / 37573118933633199 := by
    norm_num
  have h1 :
      ((6373 : ℝ) / 6480 - 1 / 61440) ^ 2 / (1 + 1 / 61440) ≤
        ((6373 : ℝ) / 6480 - 1 / 61440) ^ 2 / b :=
    div_le_div_of_nonneg_left (sq_nonneg _) hbpos hbhi
  have h2 :
      ((6373 : ℝ) / 6480 - 1 / 61440) ^ 2 / b ≤ a ^ 2 / b :=
    div_le_div_of_nonneg_right hasq hbpos.le
  have hQeq := rankOneSubrankQuotient_one_five
  have hQ : rankOneSubrankQuotient e Y = a ^ 2 / b := rfl
  rw [hQeq, hQ]
  linarith

theorem rankOneSubrankQuotient_ge_one_five
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient 1 5 ≤ rankOneSubrankQuotient e Y := by
  rcases le_iff_eq_or_lt.mp he with heq | hlt
  · subst heq
    have hcases : Y = 4 ∨ Y = 5 ∨ Y = 6 ∨ 7 ≤ Y := by omega
    rcases hcases with rfl | rfl | rfl | hY7
    · exact rankOneSubrankQuotient_one_four_gt_one_five.le
    · exact le_rfl
    · exact rankOneSubrankQuotient_one_six_gt_one_five.le
    · exact (rankOneSubrankQuotient_one_ge_seven_gt_one_five hY7).le
  · exact
      (rankOneSubrankQuotient_two_le_e_gt_one_five
          (Nat.succ_le_of_lt hlt) hY).le

/-- The five-atom first-depth kernel is the unique minimiser. -/
theorem rankOneSubrankQuotient_eq_one_five_iff
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔
      e = 1 ∧ Y = 5 := by
  constructor
  · intro heq
    rcases le_iff_eq_or_lt.mp he with heqE | hltE
    · subst heqE
      have hcases : Y = 4 ∨ Y = 5 ∨ Y = 6 ∨ 7 ≤ Y := by omega
      rcases hcases with rfl | rfl | rfl | hY7
      · have hgt := rankOneSubrankQuotient_one_four_gt_one_five
        rw [heq] at hgt
        exact (lt_irrefl _ hgt).elim
      · exact ⟨rfl, rfl⟩
      · have hgt := rankOneSubrankQuotient_one_six_gt_one_five
        rw [heq] at hgt
        exact (lt_irrefl _ hgt).elim
      · have hgt := rankOneSubrankQuotient_one_ge_seven_gt_one_five hY7
        rw [heq] at hgt
        exact (lt_irrefl _ hgt).elim
    · have hgt :=
        rankOneSubrankQuotient_two_le_e_gt_one_five
          (Nat.succ_le_of_lt hltE) hY
      rw [heq] at hgt
      exact (lt_irrefl _ hgt).elim
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## Enclosures of `Θ₂` and the sharp gap -/

private lemma prefix_seven_two :
    mobiusMersennePrefix 7 2 = (53376062902 : ℝ) / 61519376961 := by
  rw [mobiusMersennePrefix_seven]
  unfold mobiusMersennePrefixFive
  norm_num

private lemma geometricPrefixTail_two_seven :
    geometricPrefixTail 2 7 = (1 : ℝ) / 12288 := by
  unfold geometricPrefixTail
  norm_num

private lemma prefix_six_two :
    mobiusMersennePrefix 6 2 = (3309559 : ℝ) / 3814209 := by
  rw [mobiusMersennePrefix_six]
  unfold mobiusMersennePrefixFive
  norm_num

private lemma geometricPrefixTail_two_six :
    geometricPrefixTail 2 6 = (1 : ℝ) / 3072 := by
  unfold geometricPrefixTail
  norm_num

theorem rankOneSubrankQuotient_one_five_sub_theta_two_gt_twentyOne_div_threeTwenty :
    (21 : ℝ) / 320 <
      rankOneSubrankQuotient 1 5 - mobiusMersenneTheta 2 := by
  have htheta :
      mobiusMersenneTheta 2 ≤
        (53376062902 : ℝ) / 61519376961 + 1 / 12288 := by
    have herr :=
      abs_mobiusMersenneTheta_sub_prefix_le_geometric 7 2 (by omega)
    have := (abs_le.mp herr).2
    rw [prefix_seven_two, geometricPrefixTail_two_seven] at this
    linarith
  have hnum :
      (21 : ℝ) / 320 <
        (35076077250375200 : ℝ) / 37573118933633199 -
          ((53376062902 : ℝ) / 61519376961 + 1 / 12288) := by
    norm_num
  rw [rankOneSubrankQuotient_one_five]
  linarith

theorem rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen :
    rankOneSubrankQuotient 1 5 - mobiusMersenneTheta 2 <
      (1 : ℝ) / 15 := by
  have htheta :
      (3309559 : ℝ) / 3814209 - 1 / 3072 ≤ mobiusMersenneTheta 2 := by
    have herr :=
      abs_mobiusMersenneTheta_sub_prefix_le_geometric 6 2 (by omega)
    have := (abs_le.mp herr).1
    rw [prefix_six_two, geometricPrefixTail_two_six] at this
    linarith
  have hnum :
      (35076077250375200 : ℝ) / 37573118933633199 -
          ((3309559 : ℝ) / 3814209 - 1 / 3072) < (1 : ℝ) / 15 := by
    norm_num
  rw [rankOneSubrankQuotient_one_five]
  linarith

/-- **Sharp uniform rank-one floor.**  Every admissible monomial quotient
overshoots `Θ₂` by more than `21/320`. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (21 : ℝ) / 320 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  have hmin := rankOneSubrankQuotient_ge_one_five he hY
  have hgap :=
    rankOneSubrankQuotient_one_five_sub_theta_two_gt_twentyOne_div_threeTwenty
  linarith

/-- `1/16` is a uniform unit-fraction lower bound. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 16 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  have h :=
    rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty he hY
  have : (1 : ℝ) / 16 < (21 : ℝ) / 320 := by norm_num
  linarith

/-- `1/15` is not a uniform unit-fraction lower bound: it already fails at
the unique minimiser. -/
theorem not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen :
    ¬ ∀ {e Y : ℕ}, 1 ≤ e → 4 ≤ Y →
      (1 : ℝ) / 15 <
        rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  intro h
  have := h (by omega : 1 ≤ (1 : ℕ)) (by omega : 4 ≤ (5 : ℕ))
  have hlt :=
    rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen
  linarith

theorem positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (21 : ℝ) / 320 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2 := by
  have hweight : 0 < ∑ i ∈ s, w i :=
    Finset.sum_pos hw hs
  have hsum :
      (∑ i ∈ s, w i *
          (mobiusMersenneTheta 2 + (21 : ℝ) / 320)) <
        ∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i) :=
    Finset.sum_lt_sum_of_nonempty hs fun i hi => by
      have hgap :=
        rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
          (he i hi) (hY i hi)
      exact mul_lt_mul_of_pos_left (by linarith) (hw i hi)
  have hratio :
      mobiusMersenneTheta 2 + (21 : ℝ) / 320 <
        (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) := by
    rw [lt_div_iff₀ hweight]
    calc
      (mobiusMersenneTheta 2 + (21 : ℝ) / 320) * ∑ i ∈ s, w i =
          ∑ i ∈ s, w i *
            (mobiusMersenneTheta 2 + (21 : ℝ) / 320) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ < ∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i) := hsum
  linarith

theorem primitive_form_abs_gt_twentyOne_div_threeTwenty
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot :
      rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) * (21 : ℝ) / 320 <
      |(q : ℝ) * mobiusMersenneTheta 2 - p| := by
  have hgap :=
    rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty he hY
  rw [hquot] at hgap
  have hqpos : (0 : ℝ) < q := by positivity
  have hsigned :
      (q : ℝ) * (21 : ℝ) / 320 <
        (p : ℝ) - (q : ℝ) * mobiusMersenneTheta 2 := by
    have hrewrite :
        (p : ℝ) / q - mobiusMersenneTheta 2 =
          ((p : ℝ) - (q : ℝ) * mobiusMersenneTheta 2) / q := by
      field_simp [hqpos.ne']
    rw [hrewrite] at hgap
    have hm := (lt_div_iff₀ hqpos).mp hgap
    convert hm using 1; ring
  rw [abs_sub_comm]
  exact lt_of_lt_of_le hsigned (le_abs_self _)

#print axioms rankOneSubrankQuotient_one_five
#print axioms rankOneSubrankQuotient_eq_one_five_iff
#print axioms rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
#print axioms rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
#print axioms not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen
#print axioms positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
#print axioms primitive_form_abs_gt_twentyOne_div_threeTwenty

end ErdosProblems.Erdos249.RankOneSubrankObstruction
