import Erdos249257.HalfCarryReachability

/-!
# First-wrap seam as one integer-greedy remainder

This module packages the exact truncated Mersenne weights at a first
half-cylinder wrap, proves their quantitative superincreasing gap, and gives
an abstract proof that a small
positive subset-sum defect exists exactly when the descending integer-greedy
remainder is itself small and positive.

The only remaining arithmetic input after this reduction is an unbounded
lower bound for that one deterministic remainder sequence.
-/

namespace Erdos249257.HalfCylinderIntegerGreedy

open HalfCarryReachability
open scoped BigOperators

/-! ## Exact truncated weights -/

/-- The exact integer weight contributed at seam rank `s` by selecting a
proper divisor rank `d < s`. -/
def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

/-- Quotient form, with the Euclidean remainder made explicit. -/
theorem truncatedMersenneWeight_eq_geometricCore
    {s d : ℕ} (hd : 2 ≤ d) :
    truncatedMersenneWeight s d =
      2 ^ ((2 * s) % d) *
        ∑ i ∈ Finset.range ((2 * s) / d), (2 ^ d) ^ i := by
  let q := (2 * s) / d
  let r := (2 * s) % d
  let G := 2 ^ r * ∑ i ∈ Finset.range q, (2 ^ d) ^ i
  have hdpos : 0 < d := by omega
  have hdivmod : 2 * s = d * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod (2 * s) d).symm
  have hrlt : r < d := by
    dsimp [r]
    exact Nat.mod_lt _ hdpos
  have hpowOne : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have hgeom :
      (∑ i ∈ Finset.range q, (2 ^ d) ^ i) * (2 ^ d - 1) + 1 =
        (2 ^ d) ^ q := by
    simpa only [Nat.sub_add_cancel hpowOne] using
      (geom_sum_mul_add (R := ℕ) (2 ^ d - 1) q)
  have hdecomp : 4 ^ s = G * (2 ^ d - 1) + 2 ^ r := by
    calc
      4 ^ s = 2 ^ (2 * s) := by
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
      _ = 2 ^ (d * q + r) := by rw [hdivmod]
      _ = 2 ^ r * (2 ^ d) ^ q := by
        rw [pow_add, pow_mul]
        ring
      _ = 2 ^ r *
          ((∑ i ∈ Finset.range q, (2 ^ d) ^ i) * (2 ^ d - 1) + 1) := by
        rw [hgeom]
      _ = G * (2 ^ d - 1) + 2 ^ r := by
        dsimp [G]
        ring
  have hrle : r ≤ d - 1 := by omega
  have hpowle : 2 ^ r ≤ 2 ^ (d - 1) :=
    Nat.pow_le_pow_right (by norm_num) hrle
  have hpowSplit : 2 ^ d = 2 ^ (d - 1) * 2 := by
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (d - 1) * 2 := by rw [pow_succ]
  have hrem : 2 ^ r < 2 ^ d - 1 := by
    have hhalfTwo : 2 ≤ 2 ^ (d - 1) := by
      simpa using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ d - 1))
    omega
  change 4 ^ s / (2 ^ d - 1) = G
  apply Nat.div_eq_of_lt_le
  · calc
      G * (2 ^ d - 1) ≤ G * (2 ^ d - 1) + 2 ^ r :=
        Nat.le_add_right _ _
      _ = 4 ^ s := hdecomp.symm
  · rw [hdecomp]
    calc
      G * (2 ^ d - 1) + 2 ^ r <
          G * (2 ^ d - 1) + (2 ^ d - 1) := Nat.add_lt_add_left hrem _
      _ = (G + 1) * (2 ^ d - 1) := by ring

/-- Descending-multiple form used by the carry-incidence swap. -/
theorem truncatedMersenneWeight_eq_descendingMultiples
    {s d : ℕ} (hd : 2 ≤ d) :
    truncatedMersenneWeight s d =
      ∑ i ∈ Finset.range ((2 * s) / d),
        2 ^ (2 * s - d * (i + 1)) := by
  let q := (2 * s) / d
  let r := (2 * s) % d
  have hdivmod : 2 * s = d * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod (2 * s) d).symm
  rw [truncatedMersenneWeight_eq_geometricCore hd]
  change
    2 ^ r * (∑ i ∈ Finset.range q, (2 ^ d) ^ i) =
      ∑ i ∈ Finset.range q, 2 ^ (2 * s - d * (i + 1))
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hiq : i < q := Finset.mem_range.mp hi
  have hdi : d * (i + 1) ≤ d * q :=
    Nat.mul_le_mul_left d (by omega)
  have hexponent :
      r + d * (q - 1 - i) = 2 * s - d * (i + 1) := by
    calc
      r + d * (q - 1 - i) = r + (d * q - d * (i + 1)) := by
        rw [show q - 1 - i = q - (i + 1) by omega,
          Nat.mul_sub_left_distrib]
      _ = (d * q + r) - d * (i + 1) := by
        rw [add_comm (d * q) r, add_tsub_assoc_of_le hdi]
      _ = 2 * s - d * (i + 1) := by rw [← hdivmod]
  rw [← pow_mul, ← pow_add, hexponent]

/-- Reindex descending multiples as precisely the rows divisible by `d`. -/
theorem descendingMultiples_eq_divisorIndicatorSum
    {s d : ℕ} (hd : 2 ≤ d) :
    (∑ i ∈ Finset.range ((2 * s) / d),
        2 ^ (2 * s - d * (i + 1))) =
      ∑ j ∈ Finset.range (2 * s - 1),
        if d ∈ (j + 2).divisors then 2 ^ (2 * s - 2 - j) else 0 := by
  rw [← Finset.sum_filter]
  let q := (2 * s) / d
  change
    (∑ i ∈ Finset.range q, 2 ^ (2 * s - d * (i + 1))) =
      ∑ j ∈ (Finset.range (2 * s - 1)).filter
        (fun j => d ∈ (j + 2).divisors), 2 ^ (2 * s - 2 - j)
  refine Finset.sum_bij (fun i _hi => d * (i + 1) - 2) ?_ ?_ ?_ ?_
  · intro i hi
    have hiq : i < q := Finset.mem_range.mp hi
    have hqmul : d * q ≤ 2 * s := by
      dsimp [q]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (2 * s) d
    have himul : d * (i + 1) ≤ 2 * s := by
      exact le_trans (Nat.mul_le_mul_left d (by omega)) hqmul
    have hprod2 : 2 ≤ d * (i + 1) := by nlinarith
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      change d * (i + 1) - 2 < 2 * s - 1
      omega
    · apply Nat.mem_divisors.mpr
      rw [Nat.sub_add_cancel hprod2]
      exact ⟨⟨i + 1, rfl⟩, by positivity⟩
  · intro a ha b hb hab
    change d * (a + 1) - 2 = d * (b + 1) - 2 at hab
    have ha2 : 2 ≤ d * (a + 1) := by nlinarith
    have hb2 : 2 ≤ d * (b + 1) := by nlinarith
    have hprod : d * (a + 1) = d * (b + 1) := by
      calc
        d * (a + 1) = (d * (a + 1) - 2) + 2 :=
          (Nat.sub_add_cancel ha2).symm
        _ = (d * (b + 1) - 2) + 2 := by rw [hab]
        _ = d * (b + 1) := Nat.sub_add_cancel hb2
    have hab' : a + 1 = b + 1 :=
      Nat.eq_of_mul_eq_mul_left (by omega) hprod
    omega
  · intro j hj
    have hjfilter := Finset.mem_filter.mp hj
    have hjlt : j < 2 * s - 1 := Finset.mem_range.mp hjfilter.1
    have hdvd : d ∣ j + 2 := (Nat.mem_divisors.mp hjfilter.2).1
    rcases hdvd with ⟨k, hk⟩
    have hkpos : 0 < k := by
      by_contra hknot
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hknot
      rw [hkzero, mul_zero] at hk
      omega
    have hkmul : d * k ≤ 2 * s := by omega
    have hkle : k ≤ q := by
      dsimp [q]
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by
        simpa [Nat.mul_comm] using hkmul)
    refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    have hprod2 : 2 ≤ d * k := by nlinarith
    change d * (k - 1 + 1) - 2 = j
    rw [show k - 1 + 1 = k by omega, ← hk]
    omega
  · intro i hi
    have hiq : i < q := Finset.mem_range.mp hi
    have hqmul : d * q ≤ 2 * s := by
      dsimp [q]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (2 * s) d
    have himul : d * (i + 1) ≤ 2 * s := by
      exact le_trans (Nat.mul_le_mul_left d (by omega)) hqmul
    have hprod2 : 2 ≤ d * (i + 1) := by nlinarith
    change
      2 ^ (2 * s - d * (i + 1)) =
        2 ^ (2 * s - 2 - (d * (i + 1) - 2))
    congr 1
    omega

theorem truncatedMersenneWeight_eq_divisorIndicatorSum
    {s d : ℕ} (hd : 2 ≤ d) :
    truncatedMersenneWeight s d =
      ∑ j ∈ Finset.range (2 * s - 1),
        if d ∈ (j + 2).divisors then 2 ^ (2 * s - 2 - j) else 0 := by
  rw [truncatedMersenneWeight_eq_descendingMultiples hd,
    descendingMultiples_eq_divisorIndicatorSum hd]

/-- The binary-boundary target before any selected divisor weights are
removed. -/
def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

/-- The weights with indices `d,d+1,…,s-1`, in descending size order. -/
def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

/-- The actual proper-divisor weight word, indexed by `2,…,s-1`. -/
def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2

theorem seamWeightsFrom_eq_nil {s d : ℕ} (h : s ≤ d) :
    seamWeightsFrom s d = [] := by
  rw [seamWeightsFrom]
  simp [Nat.not_lt.mpr h]

theorem seamWeightsFrom_eq_cons {s d : ℕ} (h : d < s) :
    seamWeightsFrom s d =
      truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1) := by
  rw [seamWeightsFrom]
  simp [h]

/-! ## Floor enclosures and the concrete dominance gap -/

theorem truncatedMersenneWeight_cast_le_scaled
    {s d : ℕ} (hd : 1 ≤ d) :
    ((truncatedMersenneWeight s d : ℕ) : ℝ) ≤
      (4 : ℝ) ^ s * mersenneWeight d := by
  have hpowNat : 1 < 2 ^ d := one_lt_pow₀ (by omega) (by omega)
  have hdenNat : 0 < 2 ^ d - 1 := Nat.sub_pos_of_lt hpowNat
  have hdenReal : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
    have hpowReal : (1 : ℝ) < (2 : ℝ) ^ d :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hdenCast :
      (((2 ^ d - 1 : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ d - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hmulNat :
      (4 ^ s / (2 ^ d - 1)) * (2 ^ d - 1) ≤ 4 ^ s := by
    simpa [Nat.mul_comm] using Nat.mul_div_le (4 ^ s) (2 ^ d - 1)
  have hmulReal :
      (((4 ^ s / (2 ^ d - 1) : ℕ) : ℕ) : ℝ) *
          (((2 ^ d - 1 : ℕ) : ℕ) : ℝ) ≤
        (((4 ^ s : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hmulNat
  change (((4 ^ s / (2 ^ d - 1) : ℕ) : ℕ) : ℝ) ≤
    (4 : ℝ) ^ s * (1 / ((2 : ℝ) ^ d - 1))
  rw [show (4 : ℝ) ^ s * (1 / ((2 : ℝ) ^ d - 1)) =
      (4 : ℝ) ^ s / ((2 : ℝ) ^ d - 1) by ring]
  rw [le_div_iff₀ hdenReal]
  simpa only [hdenCast, Nat.cast_pow, Nat.cast_ofNat] using hmulReal

theorem scaled_lt_truncatedMersenneWeight_cast_add_one
    {s d : ℕ} (hd : 1 ≤ d) :
    (4 : ℝ) ^ s * mersenneWeight d <
      (((truncatedMersenneWeight s d + 1 : ℕ) : ℕ) : ℝ) := by
  have hpowNat : 1 < 2 ^ d := one_lt_pow₀ (by omega) (by omega)
  have hdenNat : 0 < 2 ^ d - 1 := Nat.sub_pos_of_lt hpowNat
  have hdenReal : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
    have hpowReal : (1 : ℝ) < (2 : ℝ) ^ d :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hdenCast :
      (((2 ^ d - 1 : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ d - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hquot :
      4 ^ s < (4 ^ s / (2 ^ d - 1) + 1) * (2 ^ d - 1) :=
    (Nat.div_lt_iff_lt_mul hdenNat).1
      (Nat.lt_succ_self (4 ^ s / (2 ^ d - 1)))
  have hquotReal :
      (((4 ^ s : ℕ) : ℕ) : ℝ) <
        (((4 ^ s / (2 ^ d - 1) + 1 : ℕ) : ℕ) : ℝ) *
          (((2 ^ d - 1 : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hquot
  change (4 : ℝ) ^ s * (1 / ((2 : ℝ) ^ d - 1)) <
    (((4 ^ s / (2 ^ d - 1) + 1 : ℕ) : ℕ) : ℝ)
  rw [show (4 : ℝ) ^ s * (1 / ((2 : ℝ) ^ d - 1)) =
      (4 : ℝ) ^ s / ((2 : ℝ) ^ d - 1) by ring]
  rw [div_lt_iff₀ hdenReal]
  simpa only [hdenCast, Nat.cast_pow, Nat.cast_ofNat] using hquotReal

theorem four_pow_mul_half_pow_pred {s : ℕ} (hs : 1 ≤ s) :
    (4 : ℝ) ^ s * ((1 : ℝ) / 2) ^ (s - 1) =
      (2 : ℝ) ^ (s + 1) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      have hhalf :
          ((1 : ℝ) / 2) ^ s =
            ((1 : ℝ) / 2) ^ (s - 1) * ((1 : ℝ) / 2) := by
        conv_lhs => rw [← Nat.sub_add_cancel hs]
        rw [pow_succ]
      rw [show s + 1 - 1 = s by omega, pow_succ, hhalf]
      calc
        (4 : ℝ) ^ s * 4 *
              (((1 : ℝ) / 2) ^ (s - 1) * ((1 : ℝ) / 2))
            = 2 * ((4 : ℝ) ^ s *
                ((1 : ℝ) / 2) ^ (s - 1)) := by ring
        _ = 2 * (2 : ℝ) ^ (s + 1) := by rw [ih]
        _ = (2 : ℝ) ^ (s + 1 + 1) := by rw [pow_succ]; ring

/-- The recursively listed floor weights are bounded by the matching scaled
finite Mersenne tail.  The infinite tail at `s-1` is retained explicitly;
this is what later supplies the quantitative `2^(s+1)` gap. -/
theorem seamWeightsFrom_cast_sum_add_tail_le
    (s d : ℕ) (hd : 1 ≤ d) (hds : d ≤ s) :
    (((seamWeightsFrom s d).sum : ℕ) : ℝ) +
        (4 : ℝ) ^ s * mersenneTail (s - 1) ≤
      (4 : ℝ) ^ s * mersenneTail (d - 1) := by
  by_cases heq : d = s
  · subst d
    simp [seamWeightsFrom]
  · have hlt : d < s := by omega
    have hnext :
        (((seamWeightsFrom s (d + 1)).sum : ℕ) : ℝ) +
            (4 : ℝ) ^ s * mersenneTail (s - 1) ≤
          (4 : ℝ) ^ s * mersenneTail d := by
      simpa [show d + 1 - 1 = d by omega] using
        seamWeightsFrom_cast_sum_add_tail_le
          s (d + 1) (by omega) (by omega)
    have hhead := truncatedMersenneWeight_cast_le_scaled
      (s := s) (d := d) hd
    have htailRec :
        mersenneTail (d - 1) = mersenneWeight d + mersenneTail d := by
      simpa [show d - 1 + 1 = d by omega] using
        mersenneTail_eq_weight_add (d - 1)
    rw [seamWeightsFrom_eq_cons hlt, List.sum_cons, Nat.cast_add]
    calc
      ((truncatedMersenneWeight s d : ℕ) : ℝ) +
            (((seamWeightsFrom s (d + 1)).sum : ℕ) : ℝ) +
            (4 : ℝ) ^ s * mersenneTail (s - 1)
          ≤ (4 : ℝ) ^ s * mersenneWeight d +
              ((((seamWeightsFrom s (d + 1)).sum : ℕ) : ℝ) +
                (4 : ℝ) ^ s * mersenneTail (s - 1)) := by
              linarith
      _ ≤ (4 : ℝ) ^ s * mersenneWeight d +
            (4 : ℝ) ^ s * mersenneTail d := by
              linarith
      _ = (4 : ℝ) ^ s * mersenneTail (d - 1) := by
            rw [htailRec]
            ring
termination_by s - d
decreasing_by omega

/-- Quantitative strict superincreasingness of the actual truncated weights.
The entire later integer tail plus `2^(s+1)` still fits under the current
weight. -/
theorem truncatedMersenneWeight_dominanceGap
    {s d : ℕ} (hs : 2 ≤ s) (hd : 1 ≤ d) (hds : d < s) :
    2 ^ (s + 1) + (seamWeightsFrom s (d + 1)).sum ≤
      truncatedMersenneWeight s d := by
  have htail :
      (((seamWeightsFrom s (d + 1)).sum : ℕ) : ℝ) +
          (4 : ℝ) ^ s * mersenneTail (s - 1) ≤
        (4 : ℝ) ^ s * mersenneTail d := by
    simpa [show d + 1 - 1 = d by omega] using
      seamWeightsFrom_cast_sum_add_tail_le
        s (d + 1) (by omega) (by omega)
  have hcorr := mersenneCorrectionTail_pos (s - 1)
  have hdyadic :
      ((1 : ℝ) / 2) ^ (s - 1) < mersenneTail (s - 1) := by
    unfold mersenneCorrectionTail at hcorr
    linarith
  have hscale := four_pow_mul_half_pow_pred (s := s) (by omega)
  have hscaledTail :
      (2 : ℝ) ^ (s + 1) <
        (4 : ℝ) ^ s * mersenneTail (s - 1) := by
    rw [← hscale]
    exact mul_lt_mul_of_pos_left hdyadic (by positivity)
  have hsuper := mersenneTail_lt_weight (n := d) (by omega)
  have hhead := scaled_lt_truncatedMersenneWeight_cast_add_one
    (s := s) (d := d) hd
  have hreal :
      (2 : ℝ) ^ (s + 1) +
          (((seamWeightsFrom s (d + 1)).sum : ℕ) : ℝ) <
        (((truncatedMersenneWeight s d + 1 : ℕ) : ℕ) : ℝ) := by
    nlinarith [mul_lt_mul_of_pos_left hsuper
      (show 0 < (4 : ℝ) ^ s by positivity)]
  have hnat :
      2 ^ (s + 1) + (seamWeightsFrom s (d + 1)).sum <
        truncatedMersenneWeight s d + 1 := by
    exact_mod_cast hreal
  omega

/-! ## Abstract superincreasing words -/

/-- Every head exceeds the sum of its complete tail by at least `gap`. -/
def GapDominates (gap : ℕ) : List ℕ → Prop
  | [] => True
  | w :: ws => gap + ws.sum ≤ w ∧ GapDominates gap ws

theorem seamWeightsFrom_gapDominates
    {s d : ℕ} (hs : 2 ≤ s) (hd : 1 ≤ d) :
    GapDominates (2 ^ (s + 1)) (seamWeightsFrom s d) := by
  by_cases hds : d < s
  · rw [seamWeightsFrom_eq_cons hds, GapDominates]
    exact ⟨truncatedMersenneWeight_dominanceGap hs hd hds,
      seamWeightsFrom_gapDominates hs (by omega)⟩
  · have hnil : seamWeightsFrom s d = [] :=
      seamWeightsFrom_eq_nil (by omega)
    rw [hnil]
    trivial
termination_by s - d
decreasing_by omega

theorem seamWeights_gapDominates {s : ℕ} (hs : 2 ≤ s) :
    GapDominates (2 ^ (s + 1)) (seamWeights s) := by
  exact seamWeightsFrom_gapDominates hs (by omega)

/-- Weighted sum of a Boolean word.  The equal-length hypotheses below make
the two fallback equations irrelevant. -/
def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0

theorem weightedBoolSum_le_sum (weights : List ℕ) (bits : List Bool) :
    weightedBoolSum weights bits ≤ weights.sum := by
  induction weights generalizing bits with
  | nil => simp [weightedBoolSum]
  | cons w ws ih =>
      cases bits with
      | nil => simp [weightedBoolSum]
      | cons b bs =>
          cases b
          · have h := ih bs
            simp only [weightedBoolSum, List.sum_cons]
            omega
          · simp [weightedBoolSum, ih]

/-- Distinct Boolean subset sums of a gap-dominating word differ by at least
the gap. -/
theorem weightedBoolSum_separated
    {gap : ℕ} {weights : List ℕ}
    (hgap : 0 < gap) (hdom : GapDominates gap weights)
    {a b : List Bool}
    (ha : a.length = weights.length)
    (hb : b.length = weights.length)
    (hne : a ≠ b) :
    weightedBoolSum weights a + gap ≤ weightedBoolSum weights b ∨
      weightedBoolSum weights b + gap ≤ weightedBoolSum weights a := by
  induction weights generalizing a b with
  | nil =>
      simp at ha hb
      subst a
      subst b
      exact (hne rfl).elim
  | cons w ws ih =>
      cases a with
      | nil => simp at ha
      | cons ba as =>
          cases b with
          | nil => simp at hb
          | cons bb bs =>
              simp only [List.length_cons, Nat.succ.injEq] at ha hb
              rcases hdom with ⟨hhead, htail⟩
              have hasa := weightedBoolSum_le_sum ws as
              have hasb := weightedBoolSum_le_sum ws bs
              cases ba <;> cases bb
              · have hneTail : as ≠ bs := by
                  intro h
                  apply hne
                  simp [h]
                simpa [weightedBoolSum] using ih htail ha hb hneTail
              · left
                simp [weightedBoolSum]
                omega
              · right
                simp [weightedBoolSum]
                omega
              · have hneTail : as ≠ bs := by
                  intro h
                  apply hne
                  simp [h]
                rcases ih htail ha hb hneTail with h | h
                · left
                  simp only [weightedBoolSum]
                  omega
                · right
                  simp only [weightedBoolSum]
                  omega

/-! ## Descending integer greedy and the unique-window reduction -/

/-- Descending greedy subset for an integer capacity. -/
def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

theorem integerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (integerGreedyBits weights C).length = weights.length := by
  induction weights generalizing C with
  | nil => simp [integerGreedyBits]
  | cons w ws ih =>
      simp only [integerGreedyBits]
      split <;> simp [ih]

theorem integerGreedyBits_admissible (weights : List ℕ) (C : ℕ) :
    weightedBoolSum weights (integerGreedyBits weights C) ≤ C := by
  induction weights generalizing C with
  | nil => simp [integerGreedyBits, weightedBoolSum]
  | cons w ws ih =>
      rw [integerGreedyBits]
      split_ifs with hw
      · change w + weightedBoolSum ws (integerGreedyBits ws (C - w)) ≤ C
        have htail := ih (C - w)
        omega
      · change weightedBoolSum ws (integerGreedyBits ws C) ≤ C
        exact ih C

/-- For a strictly gap-dominating word, descending greedy is the maximal
subset sum not exceeding `C`. -/
theorem integerGreedyBits_maximal
    {gap : ℕ} (hgap : 0 < gap)
    {weights : List ℕ} (hdom : GapDominates gap weights)
    {C : ℕ} {bits : List Bool}
    (hlen : bits.length = weights.length)
    (hadm : weightedBoolSum weights bits ≤ C) :
    weightedBoolSum weights bits ≤
      weightedBoolSum weights (integerGreedyBits weights C) := by
  induction weights generalizing C bits with
  | nil => simp [weightedBoolSum, integerGreedyBits]
  | cons w ws ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rcases hdom with ⟨hhead, htail⟩
          by_cases hw : w ≤ C
          · rw [integerGreedyBits]
            rw [if_pos hw]
            cases b
            · change weightedBoolSum ws bs ≤
                  w + weightedBoolSum ws (integerGreedyBits ws (C - w))
              have hbits := weightedBoolSum_le_sum ws bs
              omega
            · change w + weightedBoolSum ws bs ≤
                  w + weightedBoolSum ws (integerGreedyBits ws (C - w))
              change w + weightedBoolSum ws bs ≤ C at hadm
              have htailAdm : weightedBoolSum ws bs ≤ C - w := by omega
              have hmax := ih htail hlen htailAdm
              omega
          · rw [integerGreedyBits]
            rw [if_neg hw]
            cases b
            · change weightedBoolSum ws bs ≤
                  weightedBoolSum ws (integerGreedyBits ws C)
              change weightedBoolSum ws bs ≤ C at hadm
              exact ih htail hlen hadm
            · change w + weightedBoolSum ws bs ≤ C at hadm
              omega

/-- Exact abstract reduction.  If the subset sums are separated by a gap
strictly larger than the target window, then a positive defect in that window
exists iff the descending greedy remainder is itself positive and in the
window. -/
theorem exists_smallPositiveDefect_iff_integerGreedyRemainder
    {gap B C : ℕ} (hgap : 0 < gap) (hB : B < gap)
    {weights : List ℕ} (hdom : GapDominates gap weights) :
    (∃ bits : List Bool,
        bits.length = weights.length ∧
        weightedBoolSum weights bits < C ∧
        C - weightedBoolSum weights bits ≤ B) ↔
      1 ≤ integerGreedyRemainder weights C ∧
        integerGreedyRemainder weights C ≤ B := by
  let greedy := integerGreedyBits weights C
  let gsum := weightedBoolSum weights greedy
  have hgreedyLen : greedy.length = weights.length := by
    exact integerGreedyBits_length weights C
  have hgreedyAdm : gsum ≤ C := by
    exact integerGreedyBits_admissible weights C
  have hremEq : integerGreedyRemainder weights C = C - gsum := rfl
  constructor
  · rintro ⟨bits, hlen, hlt, hdef⟩
    have hmax : weightedBoolSum weights bits ≤ gsum :=
      integerGreedyBits_maximal hgap hdom hlen (by omega)
    have hupper : integerGreedyRemainder weights C ≤ B := by
      rw [hremEq]
      omega
    refine ⟨?_, hupper⟩
    by_contra hzero
    have hremZero : integerGreedyRemainder weights C = 0 := by omega
    have hsumEq : gsum = C := by
      rw [hremEq] at hremZero
      omega
    have hne : bits ≠ greedy := by
      intro heq
      subst bits
      change gsum < C at hlt
      omega
    rcases weightedBoolSum_separated hgap hdom hlen hgreedyLen hne with
      hsep | hsep
    · have : gap ≤ C - weightedBoolSum weights bits := by omega
      omega
    · omega
  · rintro ⟨hlow, hupp⟩
    rw [hremEq] at hlow hupp
    refine ⟨greedy, hgreedyLen, ?_, hupp⟩
    change gsum < C
    omega

/-! ## Concrete first-wrap socket -/

def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)

theorem two_mul_add_four_lt_two_pow_succ
    {s : ℕ} (hs : 3 ≤ s) :
    2 * s + 4 < 2 ^ (s + 1) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        2 * (s + 1) + 4 < 2 * (2 * s + 4) := by omega
        _ < 2 * 2 ^ (s + 1) := by omega
        _ = 2 ^ (s + 1 + 1) := by rw [pow_succ]; ring

theorem halfStripBound_lt_truncatedWeightGap
    {s : ℕ} (hs : 3 ≤ s) :
    halfStripBound (2 * s) < 2 ^ (s + 1) := by
  have hquad : 2 * s ≤ s ^ 2 := by nlinarith
  have hsqrt : Nat.sqrt (2 * s) ≤ s := by
    calc
      Nat.sqrt (2 * s) ≤ Nat.sqrt (s ^ 2) := Nat.sqrt_le_sqrt hquad
      _ = s := Nat.sqrt_eq' s
  unfold halfStripBound
  have hlin := two_mul_add_four_lt_two_pow_succ hs
  omega

/-- Universal first-wrap reduction for every `s ≥ 3`: arbitrary Boolean
divisor incidence has a seam defect in the carry strip exactly when the one
descending integer-greedy residual does. -/
theorem seam_smallPositiveDefect_iff_integerGreedyRemainder
    {s : ℕ} (hs : 3 ≤ s) :
    (∃ bits : List Bool,
        bits.length = (seamWeights s).length ∧
        weightedBoolSum (seamWeights s) bits < seamSubsetTarget s ∧
        seamSubsetTarget s - weightedBoolSum (seamWeights s) bits ≤
          halfStripBound (2 * s)) ↔
      1 ≤ seamIntegerGreedyRemainder s ∧
        seamIntegerGreedyRemainder s ≤ halfStripBound (2 * s) := by
  exact exists_smallPositiveDefect_iff_integerGreedyRemainder
    (gap := 2 ^ (s + 1)) (B := halfStripBound (2 * s))
    (C := seamSubsetTarget s)
    (by positivity) (halfStripBound_lt_truncatedWeightGap hs)
    (seamWeights_gapDominates (by omega))

/-! ## Semantic socket: actual Boolean stems -/

/-- Closed form of the affine half-carry. -/
theorem integerHalfCarry_eq_pow_sub_sum (A : Set ℕ) (N : ℕ) :
    integerHalfCarry A N =
      (2 : ℤ) ^ N -
        ∑ j ∈ Finset.range N,
          (2 : ℤ) ^ (N - 1 - j) * (supportCoeff A (j + 2) : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [integerHalfCarry_succ, ih, Finset.sum_range_succ]
      have hsum :
          (∑ j ∈ Finset.range N,
              (2 : ℤ) ^ (N - j) * (supportCoeff A (j + 2) : ℤ)) =
            2 * (∑ j ∈ Finset.range N,
              (2 : ℤ) ^ (N - 1 - j) *
                (supportCoeff A (j + 2) : ℤ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjN : j < N := Finset.mem_range.mp hj
        rw [show N - j = (N - 1 - j) + 1 by omega, pow_succ]
        ring
      rw [show N + 1 - 1 = N by omega]
      rw [hsum]
      simp only [Nat.sub_self, pow_zero, one_mul]
      ring

/-- Boolean incidence word aligned with `seamWeightsFrom`. -/
def stemBitsFrom (s : ℕ) (P : Finset ℕ) : ℕ → List Bool
  | d =>
      if h : d < s then
        decide (d ∈ P) :: stemBitsFrom s P (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

def stemBits (s : ℕ) (P : Finset ℕ) : List Bool :=
  stemBitsFrom s P 2

theorem stemBitsFrom_eq_nil {s d : ℕ} {P : Finset ℕ} (h : s ≤ d) :
    stemBitsFrom s P d = [] := by
  rw [stemBitsFrom]
  simp [Nat.not_lt.mpr h]

theorem stemBitsFrom_eq_cons {s d : ℕ} {P : Finset ℕ} (h : d < s) :
    stemBitsFrom s P d = decide (d ∈ P) :: stemBitsFrom s P (d + 1) := by
  rw [stemBitsFrom]
  simp [h]

theorem stemBitsFrom_length_eq_seamWeightsFrom_length
    (s d : ℕ) (P : Finset ℕ) :
    (stemBitsFrom s P d).length = (seamWeightsFrom s d).length := by
  by_cases hds : d < s
  · rw [stemBitsFrom_eq_cons hds, seamWeightsFrom_eq_cons hds]
    simp only [List.length_cons, Nat.succ.injEq]
    exact stemBitsFrom_length_eq_seamWeightsFrom_length s (d + 1) P
  · rw [stemBitsFrom_eq_nil (by omega),
      seamWeightsFrom_eq_nil (by omega)]
    rfl
termination_by s - d
decreasing_by omega

theorem stemBits_length_eq_seamWeights_length (s : ℕ) (P : Finset ℕ) :
    (stemBits s P).length = (seamWeights s).length :=
  stemBitsFrom_length_eq_seamWeightsFrom_length s 2 P

/-- Recursive form of the selected truncated-weight sum. -/
def stemTruncatedSumFrom (s : ℕ) (P : Finset ℕ) : ℕ → ℕ
  | d =>
      if h : d < s then
        (if d ∈ P then truncatedMersenneWeight s d else 0) +
          stemTruncatedSumFrom s P (d + 1)
      else
        0
termination_by d => s - d
decreasing_by omega

def stemTruncatedSum (s : ℕ) (P : Finset ℕ) : ℕ :=
  stemTruncatedSumFrom s P 2

theorem stemTruncatedSumFrom_eq_Ico (s d : ℕ) (P : Finset ℕ) :
    stemTruncatedSumFrom s P d =
      ∑ e ∈ Finset.Ico d s,
        if e ∈ P then truncatedMersenneWeight s e else 0 := by
  by_cases hds : d < s
  · rw [stemTruncatedSumFrom]
    simp only [hds, dite_true]
    rw [Finset.sum_eq_sum_Ico_succ_bot hds]
    rw [stemTruncatedSumFrom_eq_Ico s (d + 1) P]
  · rw [stemTruncatedSumFrom]
    simp only [hds, dite_false]
    have hempty : Finset.Ico d s = ∅ := Finset.Ico_eq_empty hds
    rw [hempty]
    simp
termination_by s - d
decreasing_by omega

theorem stemTruncatedSum_eq_sum_support
    {s : ℕ} {P : Finset ℕ}
    (hbelow : ∀ d ∈ P, 2 ≤ d ∧ d < s) :
    stemTruncatedSum s P = ∑ d ∈ P, truncatedMersenneWeight s d := by
  rw [stemTruncatedSum, stemTruncatedSumFrom_eq_Ico]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Ico 2 s).filter (fun d => d ∈ P) = P := by
    ext d
    constructor
    · intro hd
      exact (Finset.mem_filter.mp hd).2
    · intro hdP
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ico.mpr (hbelow d hdP), hdP⟩
  rw [hfilter]

theorem weightedBoolSum_stemBitsFrom
    (s d : ℕ) (P : Finset ℕ) :
    weightedBoolSum (seamWeightsFrom s d) (stemBitsFrom s P d) =
      stemTruncatedSumFrom s P d := by
  by_cases hds : d < s
  · rw [seamWeightsFrom_eq_cons hds, stemBitsFrom_eq_cons hds,
      stemTruncatedSumFrom]
    simp only [hds, dite_true]
    have hnext := weightedBoolSum_stemBitsFrom s (d + 1) P
    by_cases hdP : d ∈ P
    · simp [hdP, weightedBoolSum]
      exact hnext
    · simp [hdP, weightedBoolSum]
      exact hnext
  · rw [seamWeightsFrom_eq_nil (by omega),
      stemBitsFrom_eq_nil (by omega), stemTruncatedSumFrom]
    simp [hds, weightedBoolSum]
termination_by s - d
decreasing_by omega

theorem weightedBoolSum_stemBits (s : ℕ) (P : Finset ℕ) :
    weightedBoolSum (seamWeights s) (stemBits s P) =
      stemTruncatedSum s P :=
  weightedBoolSum_stemBitsFrom s 2 P

/-- The finite divisor/multiple reindexing needed to connect the affine
carry expansion to the truncated-weight word.  Keeping it as a named socket
makes the remaining semantic dependency exact: it contains neither the
inserted seam rank nor the terminal row twice. -/
def StemIncidenceSwap (s : ℕ) (P : Finset ℕ) : Prop :=
  (∑ j ∈ Finset.range (2 * s - 1),
      (2 : ℤ) ^ (2 * s - 2 - j) *
        (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) =
    (stemTruncatedSum s P : ℤ)

theorem supportCoeff_finset_eq_indicatorSum (P : Finset ℕ) (n : ℕ) :
    supportCoeff (↑P : Set ℕ) n =
      ∑ d ∈ P, if d ∈ n.divisors then 1 else 0 := by
  classical
  rw [supportCoeff_eq_card_filter]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  apply congrArg Finset.card
  ext d
  simp [and_comm]

theorem supportIncidenceTotal_eq_sum_weights
    {s : ℕ} {P : Finset ℕ}
    (hbelow : ∀ d ∈ P, 2 ≤ d ∧ d < s) :
    (∑ j ∈ Finset.range (2 * s - 1),
        2 ^ (2 * s - 2 - j) * supportCoeff (↑P : Set ℕ) (j + 2)) =
      ∑ d ∈ P, truncatedMersenneWeight s d := by
  classical
  calc
    _ = ∑ j ∈ Finset.range (2 * s - 1),
        ∑ d ∈ P,
          2 ^ (2 * s - 2 - j) *
            (if d ∈ (j + 2).divisors then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [supportCoeff_finset_eq_indicatorSum, Finset.mul_sum]
    _ = ∑ d ∈ P,
        ∑ j ∈ Finset.range (2 * s - 1),
          2 ^ (2 * s - 2 - j) *
            (if d ∈ (j + 2).divisors then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdP
      rw [truncatedMersenneWeight_eq_divisorIndicatorSum
        (hbelow d hdP).1]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hdj : d ∈ (j + 2).divisors <;> simp [hdj]

/-- The finite divisor/multiple swap is unconditional for a Boolean stem
supported on the proper ranks `2,…,s-1`. -/
theorem stemIncidenceSwap
    {s : ℕ} {P : Finset ℕ}
    (hbelow : ∀ d ∈ P, 2 ≤ d ∧ d < s) :
    StemIncidenceSwap s P := by
  have hnat :
      (∑ j ∈ Finset.range (2 * s - 1),
          2 ^ (2 * s - 2 - j) * supportCoeff (↑P : Set ℕ) (j + 2)) =
        stemTruncatedSum s P := by
    rw [supportIncidenceTotal_eq_sum_weights hbelow,
      stemTruncatedSum_eq_sum_support hbelow]
  change
    (∑ j ∈ Finset.range (2 * s - 1),
        (2 : ℤ) ^ (2 * s - 2 - j) *
          (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) =
      (stemTruncatedSum s P : ℤ)
  exact_mod_cast hnat

/-- Inserting an absent support rank changes a Boolean divisor coefficient
by exactly the indicator that the inserted rank divides the row. -/
theorem supportCoeff_insert_eq_add_indicator
    (A : Set ℕ) {d n : ℕ} (hdA : d ∉ A) :
    supportCoeff (insert d A) n =
      supportCoeff A n + if d ∈ n.divisors then 1 else 0 := by
  classical
  by_cases hdiv : d ∈ n.divisors
  · rw [supportCoeff_eq_card_filter, supportCoeff_eq_card_filter]
    have hfilter :
        n.divisors.filter (fun e => e ∈ insert d A) =
          insert d (n.divisors.filter fun e => e ∈ A) := by
      ext e
      by_cases hed : e = d
      · subst e
        simp [hdiv]
      · simp [hed]
    rw [hfilter]
    simp [hdA, hdiv]
  · rw [supportCoeff_eq_card_filter, supportCoeff_eq_card_filter]
    have hfilter :
        n.divisors.filter (fun e => e ∈ insert d A) =
          n.divisors.filter (fun e => e ∈ A) := by
      ext e
      by_cases hed : e = d
      · subst e
        simp [hdiv]
      · simp [hed]
    rw [hfilter]
    simp [hdiv]

/-- Once the finite incidence swap is supplied, the actual first-wrap seam
hole is exactly the abstract subset-sum defect classified above. -/
theorem actualSeamHole_eq_target_sub_stemTruncatedSum
    (s : ℕ) (P : Finset ℕ) (hs : 2 ≤ s) (hsP : s ∉ P)
    (hbelow : ∀ d ∈ P, 2 ≤ d ∧ d < s)
    (hswap : StemIncidenceSwap s P) :
    2 * integerHalfCarry (insert s (↑P : Set ℕ)) (2 * s - 2) -
        (supportCoeff (↑P : Set ℕ) (2 * s) : ℤ) =
      (seamSubsetTarget s : ℤ) - (stemTruncatedSum s P : ℤ) := by
  have hsPset : s ∉ (↑P : Set ℕ) := by
    simpa using hsP
  have hinsertCoeff : ∀ j ∈ Finset.range (2 * s - 2),
      supportCoeff (insert s (↑P : Set ℕ)) (j + 2) =
        supportCoeff (↑P : Set ℕ) (j + 2) +
          if j = s - 2 then 1 else 0 := by
    intro j hj
    have hjlt : j < 2 * s - 2 := Finset.mem_range.mp hj
    have hdiv_iff : s ∈ (j + 2).divisors ↔ j + 2 = s := by
      constructor
      · intro hdiv
        have hdvd : s ∣ j + 2 := (Nat.mem_divisors.mp hdiv).1
        rcases hdvd with ⟨k, hk⟩
        have hkpos : 0 < k := by
          by_contra hknot
          have hkzero : k = 0 := Nat.eq_zero_of_not_pos hknot
          rw [hkzero, mul_zero] at hk
          omega
        have hklt : k < 2 := by
          by_contra hknot
          have htwo : 2 ≤ k := by omega
          have hmul : s * 2 ≤ s * k := Nat.mul_le_mul_left s htwo
          have hjrowlt : j + 2 < 2 * s := by omega
          omega
        have hkone : k = 1 := by omega
        simpa [hkone] using hk
      · intro hrow
        rw [hrow]
        exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
    rw [supportCoeff_insert_eq_add_indicator _ hsPset]
    by_cases hjs : j = s - 2
    · subst j
      rw [show s - 2 + 2 = s by omega]
      simp [Nat.mem_divisors, show s ≠ 0 by omega]
    · have hrow : j + 2 ≠ s := by omega
      have hnotdiv : s ∉ (j + 2).divisors :=
        fun hdiv => hrow (hdiv_iff.mp hdiv)
      simp [hnotdiv, hjs]
  have hindicator :
      (∑ j ∈ Finset.range (2 * s - 2),
          if j = s - 2 then
            (2 : ℤ) ^ (2 * s - 2 - 1 - j)
          else 0) =
        (2 : ℤ) ^ (s - 1) := by
    have hmem : s - 2 ∈ Finset.range (2 * s - 2) := by
      simp only [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single (s - 2)]
    · simp only [if_pos]
      congr 1
      omega
    · intro b hb hba
      simp [hba]
    · intro hnotmem
      exact (hnotmem hmem).elim
  have hselected :
      (∑ j ∈ Finset.range (2 * s - 2),
          (2 : ℤ) ^ (2 * s - 2 - 1 - j) *
            (supportCoeff (insert s (↑P : Set ℕ)) (j + 2) : ℤ)) =
        (∑ j ∈ Finset.range (2 * s - 2),
          (2 : ℤ) ^ (2 * s - 2 - 1 - j) *
            (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) +
          (2 : ℤ) ^ (s - 1) := by
    calc
      _ = ∑ j ∈ Finset.range (2 * s - 2),
          ((2 : ℤ) ^ (2 * s - 2 - 1 - j) *
              (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ) +
            if j = s - 2 then
              (2 : ℤ) ^ (2 * s - 2 - 1 - j)
            else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hinsertCoeff j hj]
        split <;> push_cast <;> ring
      _ = (∑ j ∈ Finset.range (2 * s - 2),
            (2 : ℤ) ^ (2 * s - 2 - 1 - j) *
              (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) +
          ∑ j ∈ Finset.range (2 * s - 2),
            if j = s - 2 then
              (2 : ℤ) ^ (2 * s - 2 - 1 - j)
            else 0 := by
        rw [Finset.sum_add_distrib]
      _ = _ := by
        rw [hindicator]
  have hscale :
      (∑ j ∈ Finset.range (2 * s - 2),
          (2 : ℤ) ^ (2 * s - 2 - j) *
            (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) =
        2 * (∑ j ∈ Finset.range (2 * s - 2),
          (2 : ℤ) ^ (2 * s - 2 - 1 - j) *
            (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < 2 * s - 2 := Finset.mem_range.mp hj
    rw [show 2 * s - 2 - j = (2 * s - 2 - 1 - j) + 1 by omega,
      pow_succ]
    ring
  have hbase :
      2 * (∑ j ∈ Finset.range (2 * s - 2),
          (2 : ℤ) ^ (2 * s - 2 - 1 - j) *
            (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) +
          (supportCoeff (↑P : Set ℕ) (2 * s) : ℤ) =
        (stemTruncatedSum s P : ℤ) := by
    change
      (∑ j ∈ Finset.range (2 * s - 1),
          (2 : ℤ) ^ (2 * s - 2 - j) *
            (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) =
        (stemTruncatedSum s P : ℤ) at hswap
    rw [show 2 * s - 1 = (2 * s - 2) + 1 by omega,
      Finset.sum_range_succ] at hswap
    rw [show 2 * s - 2 + 2 = 2 * s by omega,
      show 2 * s - 2 - (2 * s - 2) = 0 by omega,
      pow_zero, one_mul, hscale] at hswap
    exact hswap
  have htargetCast :
      (seamSubsetTarget s : ℤ) =
        (2 : ℤ) ^ (2 * s - 1) - (2 : ℤ) ^ s := by
    have hpowle : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold seamSubsetTarget
    rw [Nat.cast_sub hpowle]
    norm_num
  have hpowTop :
      2 * (2 : ℤ) ^ (2 * s - 2) = (2 : ℤ) ^ (2 * s - 1) := by
    calc
      2 * (2 : ℤ) ^ (2 * s - 2) =
          (2 : ℤ) ^ (2 * s - 2) * 2 := by ring
      _ = (2 : ℤ) ^ ((2 * s - 2) + 1) := by rw [pow_succ]
      _ = (2 : ℤ) ^ (2 * s - 1) := by congr 1 <;> omega
  have hpowInserted :
      2 * (2 : ℤ) ^ (s - 1) = (2 : ℤ) ^ s := by
    calc
      2 * (2 : ℤ) ^ (s - 1) = (2 : ℤ) ^ (s - 1) * 2 := by ring
      _ = (2 : ℤ) ^ ((s - 1) + 1) := by rw [pow_succ]
      _ = (2 : ℤ) ^ s := by congr 1 <;> omega
  have hpowTop' :
      2 * (2 : ℤ) ^ (s * 2 - 2) = (2 : ℤ) ^ (s * 2 - 1) := by
    simpa [Nat.mul_comm] using hpowTop
  rw [integerHalfCarry_eq_pow_sub_sum, hselected, htargetCast]
  calc
    2 * ((2 : ℤ) ^ (2 * s - 2) -
          ((∑ j ∈ Finset.range (2 * s - 2),
              (2 : ℤ) ^ (2 * s - 2 - 1 - j) *
                (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) +
            (2 : ℤ) ^ (s - 1))) -
        (supportCoeff (↑P : Set ℕ) (2 * s) : ℤ) =
      (2 : ℤ) ^ (2 * s - 1) - (2 : ℤ) ^ s -
        (2 * (∑ j ∈ Finset.range (2 * s - 2),
            (2 : ℤ) ^ (2 * s - 2 - 1 - j) *
              (supportCoeff (↑P : Set ℕ) (j + 2) : ℤ)) +
          (supportCoeff (↑P : Set ℕ) (2 * s) : ℤ)) := by
        ring_nf
        linear_combination hpowTop' - hpowInserted
    _ = (2 : ℤ) ^ (2 * s - 1) - (2 : ℤ) ^ s -
          (stemTruncatedSum s P : ℤ) := by rw [hbase]

/-- Fully discharged semantic socket: every Boolean proper-rank stem has its
actual first-wrap seam hole equal to the abstract integer subset-sum defect. -/
theorem actualSeamHole_eq_target_sub_stemTruncatedSum_unconditional
    (s : ℕ) (P : Finset ℕ) (hs : 2 ≤ s) (hsP : s ∉ P)
    (hbelow : ∀ d ∈ P, 2 ≤ d ∧ d < s) :
    2 * integerHalfCarry (insert s (↑P : Set ℕ)) (2 * s - 2) -
        (supportCoeff (↑P : Set ℕ) (2 * s) : ℤ) =
      (seamSubsetTarget s : ℤ) - (stemTruncatedSum s P : ℤ) := by
  exact actualSeamHole_eq_target_sub_stemTruncatedSum
    s P hs hsP hbelow (stemIncidenceSwap hbelow)

/-! ## Carry-safe row recurrence -/

/-- The exact quotient digit created when the row is multiplied by four. -/
def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)

/-- Exact row recurrence for every old truncated Mersenne weight. -/
theorem truncatedMersenneWeight_succ
    {s d : ℕ} (hs : 2 ≤ s) (hd : 2 ≤ d) :
    truncatedMersenneWeight (s + 1) d =
      4 * truncatedMersenneWeight s d + rowPulse s d := by
  rw [truncatedMersenneWeight_eq_divisorIndicatorSum hd,
    truncatedMersenneWeight_eq_divisorIndicatorSum hd]
  have htop : 2 * (s + 1) - 1 = (2 * s - 1) + 2 := by omega
  rw [htop, show (2 * s - 1) + 2 = ((2 * s - 1) + 1) + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have hold :
      (∑ j ∈ Finset.range (2 * s - 1),
          if d ∈ (j + 2).divisors then
            2 ^ (2 * (s + 1) - 2 - j)
          else 0) =
        4 * (∑ j ∈ Finset.range (2 * s - 1),
          if d ∈ (j + 2).divisors then
            2 ^ (2 * s - 2 - j)
          else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < 2 * s - 1 := Finset.mem_range.mp hj
    by_cases hdiv : d ∈ (j + 2).divisors
    · simp only [if_pos hdiv]
      rw [show 2 * (s + 1) - 2 - j = (2 * s - 2 - j) + 2 by omega,
        pow_add]
      ring
    · simp [hdiv]
  rw [hold]
  unfold rowPulse
  have hmem1 : d ∈ (2 * s + 1).divisors ↔ d ∣ 2 * s + 1 := by
    simp [Nat.mem_divisors]
  have hmem2 : d ∈ (2 * s + 2).divisors ↔ d ∣ 2 * s + 2 := by
    simp [Nat.mem_divisors]
  simp only [show 2 * s - 1 + 2 = 2 * s + 1 by omega,
    show 2 * (s + 1) - 2 - (2 * s - 1) = 1 by omega,
    show 2 * s - 1 + 1 + 2 = 2 * s + 2 by omega,
    show 2 * (s + 1) - 2 - (2 * s - 1 + 1) = 0 by omega,
    pow_one, pow_zero, hmem1, hmem2]
  split <;> split <;> omega

/-- The seam target itself has an exact affine row recurrence. -/
theorem seamSubsetTarget_succ {s : ℕ} (hs : 2 ≤ s) :
    seamSubsetTarget (s + 1) = 4 * seamSubsetTarget s + 2 ^ (s + 1) := by
  unfold seamSubsetTarget
  have hsmall : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have htop : 2 ^ (2 * (s + 1) - 1) = 4 * 2 ^ (2 * s - 1) := by
    rw [show 2 * (s + 1) - 1 = (2 * s - 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hside : 2 ^ (s + 1) = 2 * 2 ^ s := by
    rw [pow_succ]
    ring
  rw [htop, hside]
  omega

/-- The new terminal weight has a closed form once `s ≥ 3`. -/
theorem truncatedMersenneWeight_newRank
    {s : ℕ} (hs : 3 ≤ s) :
    truncatedMersenneWeight (s + 1) s = 2 ^ (s + 2) + 4 := by
  rw [truncatedMersenneWeight_eq_geometricCore (by omega : 2 ≤ s)]
  have hdiv : (2 * (s + 1)) / s = 2 := by
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  have hmod : (2 * (s + 1)) % s = 2 := by
    rw [show 2 * (s + 1) = s * 2 + 2 by ring,
      Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [hdiv, hmod]
  norm_num [Finset.sum_range_succ, pow_succ]
  ring

/-- A Boolean word with its new rank overwritten by `beta`. -/
def extendWord (s : ℕ) (beta : Bool) (b : ℕ → Bool) : ℕ → Bool :=
  fun d => if d = s then beta else b d

/-- The selected weight sum of a Boolean word on ranks `2,...,s-1`. -/
def wordWeightSum (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then truncatedMersenneWeight s (i + 2) else 0

/-- The accumulated quotient-digit pulse of a Boolean word. -/
def wordPulse (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then rowPulse s (i + 2) else 0

/-- Signed subset-sum defect of an arbitrary Boolean row word. -/
def wordDefect (s : ℕ) (b : ℕ → Bool) : ℤ :=
  (seamSubsetTarget s : ℤ) - (wordWeightSum s b : ℤ)

theorem wordWeightSum_succ
    {s : ℕ} (hs : 3 ≤ s) (b : ℕ → Bool) (beta : Bool) :
    wordWeightSum (s + 1) (extendWord s beta b) =
      4 * wordWeightSum s b + wordPulse s b +
        if beta then 2 ^ (s + 2) + 4 else 0 := by
  unfold wordWeightSum wordPulse
  rw [show s + 1 - 2 = (s - 2) + 1 by omega, Finset.sum_range_succ]
  have hold :
      (∑ i ∈ Finset.range (s - 2),
          if extendWord s beta b (i + 2) then
            truncatedMersenneWeight (s + 1) (i + 2)
          else 0) =
        4 * (∑ i ∈ Finset.range (s - 2),
          if b (i + 2) then truncatedMersenneWeight s (i + 2) else 0) +
        ∑ i ∈ Finset.range (s - 2),
          if b (i + 2) then rowPulse s (i + 2) else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hilt : i < s - 2 := Finset.mem_range.mp hi
    have hne : i + 2 ≠ s := by omega
    rw [show extendWord s beta b (i + 2) = b (i + 2) by
      simp [extendWord, hne]]
    by_cases hb : b (i + 2)
    · simp only [hb, if_true]
      rw [truncatedMersenneWeight_succ (by omega) (by omega)]
    · simp [hb]
  rw [hold]
  have hterminal :
      extendWord s beta b (s - 2 + 2) = beta := by
    simp [extendWord, show s - 2 + 2 = s by omega]
  rw [hterminal]
  by_cases hbeta : beta
  · simp only [hbeta, if_true]
    rw [show s - 2 + 2 = s by omega, truncatedMersenneWeight_newRank hs]
  · simp [hbeta]

/-- Carry-safe affine extension formula for every Boolean word. -/
theorem wordDefect_succ
    {s : ℕ} (hs : 3 ≤ s) (b : ℕ → Bool) (beta : Bool) :
    wordDefect (s + 1) (extendWord s beta b) =
      4 * wordDefect s b + 2 ^ (s + 1) - wordPulse s b -
        (if beta then 2 ^ (s + 2) + 4 else 0) := by
  unfold wordDefect
  rw [wordWeightSum_succ hs b beta, seamSubsetTarget_succ (by omega)]
  push_cast
  ring

/-! ## Carry-safe one-successor and quarter-band reduction -/

theorem rowPulse_le_two (s d : ℕ) (hd : 2 ≤ d) :
    rowPulse s d ≤ 2 := by
  unfold rowPulse
  by_cases h₁ : d ∣ 2 * s + 2
  · have h₂ : ¬ d ∣ 2 * s + 1 := by
      intro hbad
      have hsub : d ∣ (2 * s + 2) - (2 * s + 1) := Nat.dvd_sub h₁ hbad
      have hone : (2 * s + 2) - (2 * s + 1) = 1 := by omega
      rw [hone] at hsub
      have hdle : d ≤ 1 := Nat.le_of_dvd (by omega) hsub
      omega
    simp [h₁, h₂]
  · simp only [h₁, if_false, zero_add]
    split <;> omega

theorem wordPulse_le (s : ℕ) (b : ℕ → Bool) :
    wordPulse s b ≤ 2 * (s - 2) := by
  unfold wordPulse
  calc
    (∑ i ∈ Finset.range (s - 2),
        if b (i + 2) then rowPulse s (i + 2) else 0)
        ≤ ∑ _i ∈ Finset.range (s - 2), 2 := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hb : b (i + 2)
          · simp only [hb, if_true]
            exact rowPulse_le_two s (i + 2) (by omega)
          · simp [hb]
    _ = 2 * (s - 2) := by simp [Nat.mul_comm]

/-- Old-word order survives the row perturbation whenever the landed
superincreasing gap separates the two old sums. -/
theorem oldRank_order_preserved
    {s : ℕ} (hs : 3 ≤ s) {b c : ℕ → Bool}
    (hsep : wordWeightSum s b + 2 ^ (s + 1) ≤ wordWeightSum s c) :
    wordWeightSum (s + 1) (extendWord s false b) <
      wordWeightSum (s + 1) (extendWord s false c) := by
  rw [wordWeightSum_succ hs b false, wordWeightSum_succ hs c false]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  have hb := wordPulse_le s b
  have hc : 0 ≤ wordPulse s c := Nat.zero_le _
  have hsmall : 2 * (s - 2) < 4 * 2 ^ (s + 1) := by
    have hlin : 2 * s + 4 < 2 ^ (s + 1) :=
      two_mul_add_four_lt_two_pow_succ hs
    omega
  omega

/-! ### Abstract adjacent-cut packet -/

structure PerturbedFamily (α : Type*) where
  oldSum : α → ℕ
  pulse : α → ℕ
  gap : ℕ
  pulseCap : ℕ
  gap_pos : 0 < gap
  pulse_le : ∀ x, pulse x ≤ pulseCap
  oldSum_injective : Function.Injective oldSum
  separated : ∀ {x y}, oldSum x < oldSum y →
    oldSum x + gap ≤ oldSum y
  pulseCap_lt_three_gap : pulseCap < 3 * gap

namespace PerturbedFamily

variable {α : Type*} (F : PerturbedFamily α)

def newSum (x : α) : ℕ := 4 * F.oldSum x + F.pulse x

theorem newSum_strictMono {x y : α} (hxy : F.oldSum x < F.oldSum y) :
    F.newSum x < F.newSum y := by
  have hsep := F.separated hxy
  have hx := F.pulse_le x
  have hy : 0 ≤ F.pulse y := Nat.zero_le _
  have hcap := F.pulseCap_lt_three_gap
  unfold newSum
  omega

theorem newSum_mono {x y : α} (hxy : F.oldSum x ≤ F.oldSum y) :
    F.newSum x ≤ F.newSum y := by
  rcases hxy.eq_or_lt with h | h
  · have hsame : x = y := F.oldSum_injective h
    simp [hsame]
  · exact (F.newSum_strictMono h).le

structure AdjacentCut (C : ℕ) where
  below : α
  above : α
  below_admissible : F.oldSum below ≤ C
  below_maximal : ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below
  above_strict : C < F.oldSum above
  above_minimal : ∀ x, C < F.oldSum x → F.oldSum above ≤ F.oldSum x

namespace AdjacentCut

variable {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C)

def remainder : ℕ := C - F.oldSum K.below

def overshoot : ℕ := F.oldSum K.above - C

def belowPulse : ℕ := F.pulse K.below

def abovePulse : ℕ := F.pulse K.above

def newCapacity (_K : F.AdjacentCut C) : ℕ := 4 * C + F.gap

def successorCarries : Prop :=
  4 * K.overshoot + K.abovePulse ≤ F.gap

def prefixChoice [Decidable K.successorCarries] : α :=
  if K.successorCarries then K.above else K.below

theorem old_below_add_remainder :
    F.oldSum K.below + K.remainder = C := by
  unfold remainder
  have h := K.below_admissible
  omega

theorem capacity_add_overshoot :
    C + K.overshoot = F.oldSum K.above := by
  unfold overshoot
  have h := K.above_strict
  omega

theorem below_newSum_le_capacity
    (hcap : F.pulseCap < F.gap) :
    F.newSum K.below ≤ K.newCapacity := by
  have hp := F.pulse_le K.below
  have hb := K.below_admissible
  unfold PerturbedFamily.newSum newCapacity
  omega

theorem above_newSum_le_capacity_iff :
    F.newSum K.above ≤ K.newCapacity ↔ K.successorCarries := by
  unfold PerturbedFamily.newSum newCapacity successorCarries abovePulse overshoot
  have ha := K.above_strict
  omega

theorem above_residual_eq :
    K.newCapacity - F.newSum K.above =
      F.gap - (4 * K.overshoot + K.abovePulse) := by
  unfold PerturbedFamily.newSum newCapacity abovePulse overshoot
  have ha := K.above_strict
  omega

theorem below_residual_eq :
    K.newCapacity - F.newSum K.below =
      4 * K.remainder + F.gap - K.belowPulse := by
  unfold PerturbedFamily.newSum newCapacity belowPulse remainder
  have hb := K.below_admissible
  omega

/-- The updated old-rank prefix is the old greedy word or its immediate
successor. No later word can remain admissible. -/
theorem prefixChoice_maximal
    (hcap : F.pulseCap < F.gap)
    [Decidable K.successorCarries]
    {x : α} (hx : F.newSum x ≤ K.newCapacity) :
    F.newSum x ≤ F.newSum K.prefixChoice := by
  by_cases hcarry : K.successorCarries
  · rw [prefixChoice, if_pos hcarry]
    by_cases hxold : F.oldSum x ≤ C
    · have hxb := K.below_maximal x hxold
      have hba : F.oldSum K.below < F.oldSum K.above :=
        lt_of_le_of_lt K.below_admissible K.above_strict
      exact (F.newSum_mono hxb).trans (F.newSum_strictMono hba).le
    · have hCx : C < F.oldSum x := Nat.lt_of_not_ge hxold
      have hax := K.above_minimal x hCx
      rcases hax.eq_or_lt with heq | hlt
      · have hsame : K.above = x := F.oldSum_injective heq
        subst x
        exact le_rfl
      · have hsep := F.separated hlt
        have hpAbove := F.pulse_le K.above
        have hnewAbove := (K.above_newSum_le_capacity_iff).2 hcarry
        have hres := K.above_residual_eq
        have hresle : K.newCapacity - F.newSum K.above ≤ F.gap := by
          rw [hres]
          omega
        have hxgt : K.newCapacity < F.newSum x := by
          unfold PerturbedFamily.newSum at hx hnewAbove hresle ⊢
          omega
        exact False.elim (Nat.not_lt_of_ge hx hxgt)
  · rw [prefixChoice, if_neg hcarry]
    by_cases hxold : F.oldSum x ≤ C
    · exact F.newSum_mono (K.below_maximal x hxold)
    · have hCx : C < F.oldSum x := Nat.lt_of_not_ge hxold
      have hax := K.above_minimal x hCx
      have hnew : F.newSum K.above ≤ F.newSum x := F.newSum_mono hax
      have hnAbove : ¬ F.newSum K.above ≤ K.newCapacity := by
        rw [K.above_newSum_le_capacity_iff]
        exact hcarry
      exact False.elim (hnAbove (hnew.trans hx))

/-! ### Exact terminal-bit trichotomy -/

def terminalWeight (_K : F.AdjacentCut C) : ℕ := 2 * F.gap + 4

def prefixRemainder [Decidable K.successorCarries] : ℕ :=
  if K.successorCarries then
    F.gap - (4 * K.overshoot + K.abovePulse)
  else
    4 * K.remainder + F.gap - K.belowPulse

def nextRemainder [Decidable K.successorCarries] : ℕ :=
  if K.terminalWeight ≤ K.prefixRemainder then
    K.prefixRemainder - K.terminalWeight
  else
    K.prefixRemainder

theorem prefixRemainder_eq_capacity_sub_choice
    [Decidable K.successorCarries] :
    K.prefixRemainder = K.newCapacity - F.newSum K.prefixChoice := by
  by_cases hcarry : K.successorCarries
  · simpa [prefixRemainder, prefixChoice, hcarry] using
      K.above_residual_eq.symm
  · simpa [prefixRemainder, prefixChoice, hcarry] using
      K.below_residual_eq.symm

theorem carry_prefix_lt_terminal
    [Decidable K.successorCarries] (hcarry : K.successorCarries) :
    K.prefixRemainder < K.terminalWeight := by
  rw [prefixRemainder, if_pos hcarry]
  unfold terminalWeight
  omega

/-- Exact carry-safe three-branch recurrence. -/
theorem nextRemainder_trichotomy
    [Decidable K.successorCarries] :
    K.nextRemainder =
      if K.successorCarries then
        F.gap - (4 * K.overshoot + K.abovePulse)
      else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
        4 * K.remainder + F.gap - K.belowPulse
      else
        4 * K.remainder - F.gap - K.belowPulse - 4 := by
  by_cases hcarry : K.successorCarries
  · have hlt := K.carry_prefix_lt_terminal hcarry
    have hlt' : F.gap - (4 * K.overshoot + K.abovePulse) <
        K.terminalWeight := by
      simpa [prefixRemainder, hcarry] using hlt
    have hnle : ¬ K.terminalWeight ≤
        F.gap - (4 * K.overshoot + K.abovePulse) := Nat.not_le_of_lt hlt'
    simp [nextRemainder, prefixRemainder, hcarry, hnle]
  ·
    by_cases hterminal :
        4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight
    · have hnle : ¬ K.terminalWeight ≤
          4 * K.remainder + F.gap - K.belowPulse :=
        Nat.not_le_of_lt hterminal
      simp [nextRemainder, prefixRemainder, hcarry, hterminal, hnle]
    · have hle : K.terminalWeight ≤
          4 * K.remainder + F.gap - K.belowPulse := Nat.le_of_not_gt hterminal
      simp only [nextRemainder, prefixRemainder, if_neg hcarry,
        if_pos hle, if_neg hterminal]
      unfold terminalWeight
      omega

/-! ### The sole remaining arithmetic hypothesis -/

def QuarterBandEscapeAt (B : ℕ) : Prop :=
  (K.successorCarries →
      B < F.gap - (4 * K.overshoot + K.abovePulse)) ∧
    (¬ K.successorCarries →
      K.terminalWeight ≤ 4 * K.remainder + F.gap - K.belowPulse →
      B < 4 * K.remainder - F.gap - K.belowPulse - 4)

/-- Once the two pulse-correlated quarter bands are excluded, every branch
of the exact recurrence lies above the target strip. -/
theorem bound_lt_nextRemainder_of_quarterBandEscape
    [Decidable K.successorCarries]
    {B : ℕ} (hcap : F.pulseCap < F.gap)
    (hmiddle : B < F.gap - F.pulseCap)
    (hquarter : K.QuarterBandEscapeAt B) :
    B < K.nextRemainder := by
  rw [K.nextRemainder_trichotomy]
  by_cases hcarry : K.successorCarries
  · rw [if_pos hcarry]
    exact hquarter.1 hcarry
  · rw [if_neg hcarry]
    by_cases hterminal :
        4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight
    · rw [if_pos hterminal]
      have hp : K.belowPulse ≤ F.pulseCap := by
        simpa [belowPulse] using F.pulse_le K.below
      omega
    · rw [if_neg hterminal]
      exact hquarter.2 hcarry (Nat.le_of_not_gt hterminal)

/-- Under the already-landed middle-branch separation, the two quarter-band
clauses are not merely sufficient: they are exactly the assertion that the
updated residual escapes the target strip. -/
theorem quarterBandEscape_iff_bound_lt_nextRemainder
    [Decidable K.successorCarries]
    {B : ℕ} (hcap : F.pulseCap < F.gap)
    (hmiddle : B < F.gap - F.pulseCap) :
    K.QuarterBandEscapeAt B ↔ B < K.nextRemainder := by
  constructor
  · intro hquarter
    exact K.bound_lt_nextRemainder_of_quarterBandEscape
      hcap hmiddle hquarter
  · intro hnext
    constructor
    · intro hcarry
      rw [K.nextRemainder_trichotomy, if_pos hcarry] at hnext
      exact hnext
    · intro hcarry hterminal
      have hnlt : ¬ 4 * K.remainder + F.gap - K.belowPulse <
          K.terminalWeight := Nat.not_lt_of_ge hterminal
      rw [K.nextRemainder_trichotomy, if_neg hcarry, if_neg hnlt] at hnext
      exact hnext

end AdjacentCut
end PerturbedFamily

#print axioms truncatedMersenneWeight_dominanceGap
#print axioms weightedBoolSum_separated
#print axioms integerGreedyBits_maximal
#print axioms seam_smallPositiveDefect_iff_integerGreedyRemainder
#print axioms integerHalfCarry_eq_pow_sub_sum
#print axioms weightedBoolSum_stemBits
#print axioms truncatedMersenneWeight_eq_geometricCore
#print axioms truncatedMersenneWeight_eq_descendingMultiples
#print axioms truncatedMersenneWeight_eq_divisorIndicatorSum
#print axioms stemIncidenceSwap
#print axioms supportCoeff_insert_eq_add_indicator
#print axioms actualSeamHole_eq_target_sub_stemTruncatedSum
#print axioms actualSeamHole_eq_target_sub_stemTruncatedSum_unconditional
#print axioms truncatedMersenneWeight_succ
#print axioms seamSubsetTarget_succ
#print axioms truncatedMersenneWeight_newRank
#print axioms wordWeightSum_succ
#print axioms wordDefect_succ
#print axioms rowPulse_le_two
#print axioms wordPulse_le
#print axioms oldRank_order_preserved
#print axioms PerturbedFamily.newSum_strictMono
#print axioms PerturbedFamily.AdjacentCut.prefixChoice_maximal
#print axioms PerturbedFamily.AdjacentCut.nextRemainder_trichotomy
#print axioms PerturbedFamily.AdjacentCut.bound_lt_nextRemainder_of_quarterBandEscape
#print axioms PerturbedFamily.AdjacentCut.quarterBandEscape_iff_bound_lt_nextRemainder

end Erdos249257.HalfCylinderIntegerGreedy
