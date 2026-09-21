import Erdos249257.GreedyAchievementSet

/-!
The greedy-orbit half of the "Successive tail truncations" subsection of the
long Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

The subsection fixes `J ≥ 2` and works with the truncated geometric weights

* `rungWeight J n = w_n^{(J)} = ∑_{q=1}^{J} 2^{-qn}`,
* `rungTail J n = T_{n+1}^{(J)} = ∑_{q=1}^{J} 2^{-qn}/(2^q-1)`, which is the
  complete mass of those weights at the ranks `> n`
  (`rungTail_succ` is the peeling identity `T_{n+1} = w_{n+1} + T_{n+2}`),
* `rungMisalign J M = μ_J(M) = ∑_{q=2}^{J} 2^{M mod q}/(2^q-1)`,
* `rungLcm J = L_J = lcm(2,3,…,J)`,
* `HalfRung J` ⟺ some `A ⊆ {2,3,…}` has `∑_{n ∈ A} w_n^{(J)} = 1/2`.

Covered here:

* `lem:tr-forced-greedy` (line 5974) in full — `w_n > T_{n+1}` for every `n`
  (`paper_forced_greedy_tail_lt_weight'`); the greedy support is the *unique*
  candidate support and `HalfRung J` holds iff the greedy orbit never lands in
  a fatal interval `(T_{n+1}^{(J)}, w_n^{(J)})`
  (`paper_forced_greedy_unique_support_and_criterion`); rank `1` is a safe skip
  and ranks `2` and `3` are takes (`paper_forced_greedy_low_ranks`).
* `thm:tr-finite-decision` (line 6065) — with `B(J) = max(bad ∪ {3})` over the
  bad ranks of `[4, L_J/2]`, `HalfRung J` holds iff the greedy orbit survives
  every rank from `2` through `B(J)` (`paper_rung_finite_decision`), a finite
  exact decision procedure.

The witness-exclusion theorem and the half-LCM horizon corollary that
`thm:tr-finite-decision` consumes are reproved here as private lemmas
(`rung_witness_exclusion`, `rung_half_lcm_horizon`), at `J ≥ 2` rather than
`J ≥ 3`, since the manuscript records that the same calculation covers `J = 2`.
All names are `rung`-prefixed so that this module and
`TruncatedRungWitnessHorizon` can coexist in one namespace.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Filter Topology

/-! ## The truncated weight system -/

/-- The manuscript's `w_n^{(J)} = ∑_{q=1}^{J} 2^{-qn}`. -/
noncomputable def rungWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)

/-- The manuscript's `T_{n+1}^{(J)} = ∑_{q=1}^{J} 2^{-qn}/(2^q-1)`. -/
noncomputable def rungTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))

/-- The manuscript's misalignment mass `μ_J(M) = ∑_{q=2}^{J} 2^{M mod q}/(2^q-1)`. -/
noncomputable def rungMisalign (J M : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 J, (2 : ℝ) ^ (M % q) / (2 ^ q - 1)

/-- The manuscript's `L_J = lcm(2,3,…,J)`. -/
def rungLcm (J : ℕ) : ℕ := (Finset.Icc 2 J).lcm id

/-! ## Elementary geometric bounds -/

private theorem two_le_two_pow {q : ℕ} (hq : 1 ≤ q) : (2 : ℝ) ≤ 2 ^ q := by
  calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq

private theorem inv_pow_eq (n q : ℕ) : ((1 : ℝ) / 2 ^ n) ^ q = 1 / 2 ^ (q * n) := by
  rw [div_pow, one_pow, ← pow_mul, mul_comm]

private theorem geom_range_mul (x : ℝ) (K : ℕ) :
    (∑ i ∈ Finset.range K, x ^ i) * (1 - x) = 1 - x ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      ring

private theorem geom_range_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (K : ℕ) :
    ∑ i ∈ Finset.range K, x ^ i ≤ 1 / (1 - x) := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hg : (∑ i ∈ Finset.range K, x ^ i) * (1 - x) = 1 - x ^ K := geom_range_mul x K
  rw [le_div_iff₀ hpos, hg]
  have : (0 : ℝ) ≤ x ^ K := pow_nonneg hx0 K
  linarith

private theorem sum_pow_le_of_le_index {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (a : ℕ)
    (s : Finset ℕ) (hs : ∀ q ∈ s, a ≤ q) :
    ∑ q ∈ s, x ^ q ≤ x ^ a / (1 - x) := by
  classical
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hsub : s ⊆ Finset.Ico a (s.sup id + 1) := by
    intro q hq
    exact Finset.mem_Ico.2 ⟨hs q hq, Nat.lt_succ_of_le (Finset.le_sup (f := id) hq)⟩
  have h1 : ∑ q ∈ s, x ^ q ≤ ∑ q ∈ Finset.Ico a (s.sup id + 1), x ^ q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => pow_nonneg hx0 i
  have h2 : ∑ q ∈ Finset.Ico a (s.sup id + 1), x ^ q
      = x ^ a * ∑ i ∈ Finset.range (s.sup id + 1 - a), x ^ i := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
  have h3 : ∑ i ∈ Finset.range (s.sup id + 1 - a), x ^ i ≤ 1 / (1 - x) :=
    geom_range_le hx0 hx1 _
  calc ∑ q ∈ s, x ^ q ≤ x ^ a * ∑ i ∈ Finset.range (s.sup id + 1 - a), x ^ i := by
        rw [← h2]; exact h1
    _ ≤ x ^ a * (1 / (1 - x)) := mul_le_mul_of_nonneg_left h3 (pow_nonneg hx0 a)
    _ = x ^ a / (1 - x) := by ring

private theorem rungWeight_le_inv {J n : ℕ} (hn : 1 ≤ n) :
    rungWeight J n ≤ 1 / (2 ^ n - 1) := by
  have h2 : (2 : ℝ) ≤ 2 ^ n := two_le_two_pow hn
  have hx1 : (1 : ℝ) / 2 ^ n < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hx0 : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
  have hrw : rungWeight J n = ∑ q ∈ Finset.Icc 1 J, ((1 : ℝ) / 2 ^ n) ^ q := by
    rw [rungWeight]
    exact Finset.sum_congr rfl fun q _ => (inv_pow_eq n q).symm
  have hbd := sum_pow_le_of_le_index hx0 hx1 1 (Finset.Icc 1 J)
    (fun q hq => (Finset.mem_Icc.1 hq).1)
  rw [hrw]
  refine hbd.trans (le_of_eq ?_)
  have hne : (2 : ℝ) ^ n - 1 ≠ 0 := by intro h; linarith
  have hne2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-! ## Basic facts about the weights and the tail -/

theorem rungWeight_nonneg (J n : ℕ) : 0 ≤ rungWeight J n :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem rungTail_nonneg (J n : ℕ) : 0 ≤ rungTail J n := by
  refine Finset.sum_nonneg fun q hq => ?_
  have h2 : (2 : ℝ) ≤ 2 ^ q := two_le_two_pow (Finset.mem_Icc.1 hq).1
  have hp : (0 : ℝ) < 2 ^ (q * q) := by positivity
  have hpos : (0 : ℝ) < 2 ^ (q * n) * (2 ^ q - 1) := by
    have : (0 : ℝ) < 2 ^ (q * n) := by positivity
    nlinarith
  exact div_nonneg zero_le_one hpos.le

private theorem rungWeight_zero (J : ℕ) : rungWeight J 0 = (J : ℝ) := by
  rw [rungWeight]
  have hcongr : ∀ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * 0) = 1 := by
    intro q _; norm_num
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
    Nat.add_sub_cancel]

/-- Long `lem:tr-forced-greedy`, first clause.  For every `J ≥ 2` and every
`n`, the truncated weight `w_n^{(J)}` strictly exceeds the complete later tail
`T_{n+1}^{(J)}`: the `q = 1` terms agree and every `q ≥ 2` tail term is
strictly smaller than the matching weight term. -/
theorem paper_forced_greedy_tail_lt_weight' {J : ℕ} (hJ : 2 ≤ J) (n : ℕ) :
    rungTail J n < rungWeight J n := by
  rw [rungTail, rungWeight]
  refine Finset.sum_lt_sum ?_ ?_
  · intro q hq
    rw [Finset.mem_Icc] at hq
    have h2 : (2 : ℝ) ≤ 2 ^ q := two_le_two_pow hq.1
    have hpos : (0 : ℝ) < 2 ^ (q * n) := by positivity
    have hge : (2 : ℝ) ^ (q * n) ≤ 2 ^ (q * n) * (2 ^ q - 1) := by nlinarith
    exact one_div_le_one_div_of_le hpos hge
  · refine ⟨2, Finset.mem_Icc.2 ⟨by norm_num, hJ⟩, ?_⟩
    have hpos : (0 : ℝ) < 2 ^ (2 * n) := by positivity
    have hlt : (2 : ℝ) ^ (2 * n) < 2 ^ (2 * n) * (2 ^ 2 - 1) := by nlinarith
    exact one_div_lt_one_div_of_lt hpos hlt

/-- The tail peels its head: `T_{n+1}^{(J)} = w_{n+1}^{(J)} + T_{n+2}^{(J)}`. -/
theorem rungTail_succ (J n : ℕ) :
    rungTail J n = rungWeight J (n + 1) + rungTail J (n + 1) := by
  rw [rungTail, rungWeight, rungTail, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
  have h2 : (2 : ℝ) ≤ 2 ^ q := two_le_two_pow hq1
  have hne : (2 : ℝ) ^ q - 1 ≠ 0 := by intro h; linarith
  have hpow : (2 : ℝ) ^ (q * (n + 1)) = 2 ^ (q * n) * 2 ^ q := by
    rw [← pow_add, Nat.mul_succ]
  have hne1 : (2 : ℝ) ^ (q * n) ≠ 0 := by positivity
  have hne2 : (2 : ℝ) ^ q ≠ 0 := by positivity
  rw [hpow]
  field_simp
  ring

/-- The `q = 1` term already gives `2^{-n} ≤ T_{n+1}^{(J)}`. -/
private theorem inv_pow_le_rungTail {J : ℕ} (hJ : 1 ≤ J) (n : ℕ) :
    (1 : ℝ) / 2 ^ n ≤ rungTail J n := by
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 J := Finset.mem_Icc.2 ⟨le_refl 1, hJ⟩
  have hnn : ∀ i ∈ Finset.Icc 1 J, (0 : ℝ) ≤ 1 / (2 ^ (i * n) * (2 ^ i - 1)) := by
    intro i hi
    have h2 : (2 : ℝ) ≤ 2 ^ i := two_le_two_pow (Finset.mem_Icc.1 hi).1
    have hp : (0 : ℝ) < 2 ^ (i * n) := by positivity
    have hpos : (0 : ℝ) < 2 ^ (i * n) * (2 ^ i - 1) := by nlinarith
    exact div_nonneg zero_le_one hpos.le
  rw [rungTail]
  calc (1 : ℝ) / 2 ^ n = 1 / (2 ^ (1 * n) * (2 ^ 1 - 1)) := by norm_num
    _ ≤ ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1)) :=
        Finset.single_le_sum hnn hmem

private theorem half_lt_rungWeight_one {J : ℕ} (hJ : 2 ≤ J) :
    (1 : ℝ) / 2 < rungWeight J 1 := by
  have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 J := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_Icc.2 (by omega)
  have hle : ∑ q ∈ ({1, 2} : Finset ℕ), (1 : ℝ) / 2 ^ (q * 1) ≤ rungWeight J 1 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
  have hval : ∑ q ∈ ({1, 2} : Finset ℕ), (1 : ℝ) / 2 ^ (q * 1) = 3 / 4 := by norm_num
  rw [hval] at hle
  linarith

private theorem rungWeight_le_geom (J n : ℕ) : rungWeight J n ≤ (J : ℝ) * ((1 : ℝ) / 2) ^ n := by
  have hterm : ∀ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n) ≤ ((1 : ℝ) / 2) ^ n := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
    have hle : n ≤ q * n := Nat.le_mul_of_pos_left n (by omega)
    have h1 : (2 : ℝ) ^ n ≤ 2 ^ (q * n) := pow_le_pow_right₀ (by norm_num) hle
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le h2 h1
  calc rungWeight J n ≤ ∑ q ∈ Finset.Icc 1 J, ((1 : ℝ) / 2) ^ n := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 1 J).card : ℝ) * ((1 : ℝ) / 2) ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (J : ℝ) * ((1 : ℝ) / 2) ^ n := by rw [Nat.card_Icc, Nat.add_sub_cancel]

private theorem rungTail_le_geom (J n : ℕ) : rungTail J n ≤ (J : ℝ) / 2 ^ n := by
  have hterm : ∀ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1)) ≤ 1 / 2 ^ n := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
    have h2q : (2 : ℝ) ≤ 2 ^ q := two_le_two_pow hq1
    have hle : n ≤ q * n := Nat.le_mul_of_pos_left n (by omega)
    have h1 : (2 : ℝ) ^ n ≤ 2 ^ (q * n) := pow_le_pow_right₀ (by norm_num) hle
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have hp : (0 : ℝ) < 2 ^ (q * n) := by positivity
    have h3 : (2 : ℝ) ^ n ≤ 2 ^ (q * n) * (2 ^ q - 1) := by nlinarith
    exact one_div_le_one_div_of_le h2 h3
  rw [rungTail]
  calc ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))
      ≤ ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ n := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 1 J).card : ℝ) * ((1 : ℝ) / 2 ^ n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (J : ℝ) / 2 ^ n := by rw [Nat.card_Icc, Nat.add_sub_cancel]; ring

theorem rungWeight_summable (J : ℕ) : Summable (rungWeight J) := by
  have hg : Summable (fun n : ℕ => (J : ℝ) * ((1 : ℝ) / 2) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (J : ℝ)
  exact Summable.of_nonneg_of_le (fun n => rungWeight_nonneg J n)
    (fun n => rungWeight_le_geom J n) hg

/-- The weights strictly after rank `n` never sum past the tail `T_{n+1}^{(J)}`;
in fact the partial sums telescope. -/
private theorem rungWeight_range_shift_eq (J n K : ℕ) :
    ∑ k ∈ Finset.range K, rungWeight J (k + (n + 1)) = rungTail J n - rungTail J (n + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have h := rungTail_succ J (n + K)
      have he : n + K + 1 = K + (n + 1) := by omega
      rw [he] at h
      have he2 : n + (K + 1) = K + (n + 1) := by omega
      rw [he2]
      linarith

private theorem rungWeight_range_shift_le (J n K : ℕ) :
    ∑ k ∈ Finset.range K, rungWeight J (k + (n + 1)) ≤ rungTail J n := by
  rw [rungWeight_range_shift_eq]
  have := rungTail_nonneg J (n + K)
  linarith

/-! ## Supports and the manuscript's `HalfRung(J)` -/

open Classical in
/-- The mass that the support `A` puts at rank `n`: this is
`Set.indicator A (rungWeight J)`, so `∑' n, rungSupportWeight J A n` is the
manuscript's `∑_{n ∈ A} w_n^{(J)}`. -/
noncomputable def rungSupportWeight (J : ℕ) (A : Set ℕ) (n : ℕ) : ℝ :=
  if n ∈ A then rungWeight J n else 0

theorem rungSupportWeight_of_mem {J : ℕ} {A : Set ℕ} {n : ℕ} (h : n ∈ A) :
    rungSupportWeight J A n = rungWeight J n := by
  rw [rungSupportWeight, if_pos h]

theorem rungSupportWeight_of_notMem {J : ℕ} {A : Set ℕ} {n : ℕ} (h : n ∉ A) :
    rungSupportWeight J A n = 0 := by
  rw [rungSupportWeight, if_neg h]

theorem rungSupportWeight_nonneg (J : ℕ) (A : Set ℕ) (n : ℕ) :
    0 ≤ rungSupportWeight J A n := by
  by_cases h : n ∈ A
  · rw [rungSupportWeight_of_mem h]; exact rungWeight_nonneg J n
  · rw [rungSupportWeight_of_notMem h]

theorem rungSupportWeight_le (J : ℕ) (A : Set ℕ) (n : ℕ) :
    rungSupportWeight J A n ≤ rungWeight J n := by
  by_cases h : n ∈ A
  · rw [rungSupportWeight_of_mem h]
  · rw [rungSupportWeight_of_notMem h]; exact rungWeight_nonneg J n

theorem rungSupportWeight_summable (J : ℕ) (A : Set ℕ) :
    Summable (rungSupportWeight J A) :=
  Summable.of_nonneg_of_le (rungSupportWeight_nonneg J A) (rungSupportWeight_le J A)
    (rungWeight_summable J)

/-- The manuscript's `HalfRung(J)`: some `A ⊆ {2,3,…}` has
`∑_{n ∈ A} w_n^{(J)} = 1/2`. -/
def HalfRung (J : ℕ) : Prop :=
  ∃ A : Set ℕ, (∀ n ∈ A, 2 ≤ n) ∧ ∑' n : ℕ, rungSupportWeight J A n = 1 / 2

/-- The residual of the support `A` after the ranks below `n`. -/
noncomputable def rungSupportRem (J : ℕ) (A : Set ℕ) (n : ℕ) : ℝ :=
  1 / 2 - ∑ i ∈ Finset.range n, rungSupportWeight J A i

private theorem rungSupportRem_succ (J : ℕ) (A : Set ℕ) (n : ℕ) :
    rungSupportRem J A (n + 1) = rungSupportRem J A n - rungSupportWeight J A n := by
  rw [rungSupportRem, rungSupportRem, Finset.sum_range_succ]
  ring

/-! ## The greedy orbit for target `1/2` under the weights `w_n^{(J)}` -/

/-- The greedy residual just before rank `n` is examined; `rungRem J 0 = 1/2`. -/
noncomputable def rungRem (J : ℕ) : ℕ → ℝ
  | 0 => 1 / 2
  | n + 1 => if rungWeight J n ≤ rungRem J n then rungRem J n - rungWeight J n else rungRem J n

theorem rungRem_zero (J : ℕ) : rungRem J 0 = 1 / 2 := by simp only [rungRem]

theorem rungRem_succ (J n : ℕ) :
    rungRem J (n + 1) =
      if rungWeight J n ≤ rungRem J n then rungRem J n - rungWeight J n
      else rungRem J n := by
  simp only [rungRem]

/-- The greedy support: the ranks the greedy rule takes. -/
def rungGreedySupport (J : ℕ) : Set ℕ := {n | rungWeight J n ≤ rungRem J n}

theorem mem_rungGreedySupport {J n : ℕ} :
    n ∈ rungGreedySupport J ↔ rungWeight J n ≤ rungRem J n := Iff.rfl

/-- Rank `n` is **fatal** when the residual sits strictly inside the gap
`(T_{n+1}^{(J)}, w_n^{(J)})`, which no later tail can repair. -/
def RungFatal (J n : ℕ) : Prop :=
  rungTail J n < rungRem J n ∧ rungRem J n < rungWeight J n

theorem rungRem_nonneg (J n : ℕ) : 0 ≤ rungRem J n := by
  induction n with
  | zero => rw [rungRem_zero]; norm_num
  | succ n ih =>
      rw [rungRem_succ]
      by_cases h : rungWeight J n ≤ rungRem J n
      · rw [if_pos h]; linarith
      · rw [if_neg h]; exact ih

/-- Rank `0` is skipped: its weight is `J ≥ 2`. -/
theorem rungRem_one {J : ℕ} (hJ : 2 ≤ J) : rungRem J 1 = 1 / 2 := by
  have hw : rungWeight J 0 = (J : ℝ) := rungWeight_zero J
  have hJR : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hnot : ¬ (rungWeight J 0 ≤ rungRem J 0) := by
    rw [hw, rungRem_zero]; intro h; linarith
  rw [rungRem_succ, if_neg hnot, rungRem_zero]

theorem zero_notMem_rungGreedySupport {J : ℕ} (hJ : 2 ≤ J) : 0 ∉ rungGreedySupport J := by
  rw [mem_rungGreedySupport, rungWeight_zero, rungRem_zero]
  have hJR : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  intro h; linarith

theorem one_notMem_rungGreedySupport {J : ℕ} (hJ : 2 ≤ J) : 1 ∉ rungGreedySupport J := by
  rw [mem_rungGreedySupport, rungRem_one hJ]
  have := half_lt_rungWeight_one hJ
  intro h; linarith

/-- The greedy residual as `1/2` minus the mass already taken. -/
theorem rungRem_eq_supportRem_greedy (J n : ℕ) :
    rungRem J n = rungSupportRem J (rungGreedySupport J) n := by
  induction n with
  | zero => rw [rungRem_zero, rungSupportRem]; simp
  | succ n ih =>
      rw [rungRem_succ, ih, rungSupportRem_succ]
      by_cases h : rungWeight J n ≤ rungRem J n
      · have hmem : n ∈ rungGreedySupport J := h
        rw [if_pos (ih ▸ h), rungSupportWeight_of_mem hmem]
      · have hmem : n ∉ rungGreedySupport J := h
        rw [if_neg (fun hc => h (ih ▸ hc)), rungSupportWeight_of_notMem hmem]
        ring

/-! ## The survival invariant and the limit -/

private theorem rungRem_succ_le_tail {J : ℕ} (hJ : 2 ≤ J)
    (hsurv : ∀ n, ¬ RungFatal J n) (n : ℕ) : rungRem J (n + 1) ≤ rungTail J n := by
  induction n with
  | zero =>
      rw [rungRem_one hJ]
      have h := inv_pow_le_rungTail (J := J) (by omega) 0
      norm_num at h
      linarith
  | succ n ih =>
      have hpeel := rungTail_succ J n
      rw [rungRem_succ]
      by_cases h : rungWeight J (n + 1) ≤ rungRem J (n + 1)
      · rw [if_pos h]; linarith
      · rw [if_neg h]
        have hlt : rungRem J (n + 1) < rungWeight J (n + 1) := lt_of_not_ge h
        have hnf := hsurv (n + 1)
        have hnl : ¬ (rungTail J (n + 1) < rungRem J (n + 1)) := fun hT => hnf ⟨hT, hlt⟩
        exact not_lt.1 hnl

private theorem rungRem_tendsto_zero {J : ℕ} (hJ : 2 ≤ J)
    (hsurv : ∀ n, ¬ RungFatal J n) :
    Tendsto (fun n => rungRem J n) atTop (nhds 0) := by
  have hmaj : Tendsto (fun n : ℕ => (J : ℝ) / 2 ^ n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hshift : Tendsto (fun n => rungRem J (n + 1)) atTop (nhds 0) := by
    refine squeeze_zero (fun n => rungRem_nonneg J (n + 1)) (fun n => ?_) hmaj
    exact (rungRem_succ_le_tail hJ hsurv n).trans (rungTail_le_geom J n)
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hshift

/-! ## `lem:tr-forced-greedy`, clause two -/

/-- Survival at every rank makes the greedy support achieve the target. -/
private theorem rungGreedy_tsum_eq_half {J : ℕ} (hJ : 2 ≤ J)
    (hsurv : ∀ n, ¬ RungFatal J n) :
    ∑' n : ℕ, rungSupportWeight J (rungGreedySupport J) n = 1 / 2 := by
  have hsummable := rungSupportWeight_summable J (rungGreedySupport J)
  have hpart : ∀ n : ℕ,
      ∑ m ∈ Finset.range n, rungSupportWeight J (rungGreedySupport J) m
        = 1 / 2 - rungRem J n := by
    intro n
    rw [rungRem_eq_supportRem_greedy, rungSupportRem]
    ring
  have h1 : Tendsto
      (fun n => ∑ m ∈ Finset.range n, rungSupportWeight J (rungGreedySupport J) m)
      atTop (nhds (1 / 2)) := by
    have hz := rungRem_tendsto_zero hJ hsurv
    have := tendsto_const_nhds.sub hz (f := fun _ : ℕ => (1 / 2 : ℝ))
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    rw [hpart n]
  exact tendsto_nhds_unique hsummable.hasSum.tendsto_sum_nat h1

/-- Any support achieving the target runs in lockstep with the greedy orbit. -/
private theorem rungRem_eq_of_tsum {J : ℕ} (hJ : 2 ≤ J) {A : Set ℕ}
    (hsum : ∑' n : ℕ, rungSupportWeight J A n = 1 / 2) :
    ∀ n, rungRem J n = rungSupportRem J A n := by
  have hf := rungSupportWeight_summable J A
  have htail : ∀ n, rungSupportRem J A n = ∑' k : ℕ, rungSupportWeight J A (k + n) := by
    intro n
    have h := hf.sum_add_tsum_nat_add n
    rw [hsum] at h
    rw [rungSupportRem]
    linarith
  have hnn : ∀ n, 0 ≤ rungSupportRem J A n := by
    intro n
    rw [htail n]
    exact tsum_nonneg fun k => rungSupportWeight_nonneg J A (k + n)
  have htake : ∀ n, n ∈ A → rungWeight J n ≤ rungSupportRem J A n := by
    intro n hmem
    have h0 := hnn (n + 1)
    rw [rungSupportRem_succ, rungSupportWeight_of_mem hmem] at h0
    linarith
  have hskip : ∀ n, n ∉ A → rungSupportRem J A n ≤ rungTail J n := by
    intro n hmem
    have hstep := rungSupportRem_succ J A n
    rw [rungSupportWeight_of_notMem hmem] at hstep
    have heq : rungSupportRem J A n = rungSupportRem J A (n + 1) := by linarith
    rw [heq, htail (n + 1)]
    refine Real.tsum_le_of_sum_range_le
      (fun k => rungSupportWeight_nonneg J A (k + (n + 1))) ?_
    intro K
    calc ∑ k ∈ Finset.range K, rungSupportWeight J A (k + (n + 1))
        ≤ ∑ k ∈ Finset.range K, rungWeight J (k + (n + 1)) :=
          Finset.sum_le_sum fun k _ => rungSupportWeight_le J A (k + (n + 1))
      _ ≤ rungTail J n := rungWeight_range_shift_le J n K
  have hnot : ∀ n, n ∉ A → ¬ (rungWeight J n ≤ rungSupportRem J A n) := by
    intro n hmem hle
    have h1 := hskip n hmem
    have h2 := paper_forced_greedy_tail_lt_weight' hJ n
    linarith
  intro n
  induction n with
  | zero => rw [rungRem_zero, rungSupportRem]; simp
  | succ n ih =>
      rw [rungRem_succ, ih, rungSupportRem_succ]
      by_cases hmem : n ∈ A
      · rw [if_pos (htake n hmem), rungSupportWeight_of_mem hmem]
      · rw [if_neg (hnot n hmem), rungSupportWeight_of_notMem hmem]
        ring

/-- **Long `lem:tr-forced-greedy`, clause two.**  For `J ≥ 2` the greedy
support is the unique candidate support, and `HalfRung(J)` holds exactly when
the greedy orbit for `1/2` under the weights `w_n^{(J)}` never lands in a fatal
interval `(T_{n+1}^{(J)}, w_n^{(J)})`. -/
theorem paper_forced_greedy_unique_support_and_criterion {J : ℕ} (hJ : 2 ≤ J) :
    (∀ A : Set ℕ, ∑' n : ℕ, rungSupportWeight J A n = 1 / 2 → A = rungGreedySupport J) ∧
      (HalfRung J ↔ ∀ n : ℕ, ¬ RungFatal J n) := by
  have huniq : ∀ A : Set ℕ, ∑' n : ℕ, rungSupportWeight J A n = 1 / 2 →
      A = rungGreedySupport J := by
    intro A hsum
    have hrem := rungRem_eq_of_tsum hJ hsum
    have hf := rungSupportWeight_summable J A
    have htail : ∀ n, rungSupportRem J A n = ∑' k : ℕ, rungSupportWeight J A (k + n) := by
      intro n
      have h := hf.sum_add_tsum_nat_add n
      rw [hsum] at h
      rw [rungSupportRem]
      linarith
    have hnn : ∀ n, 0 ≤ rungSupportRem J A n := by
      intro n
      rw [htail n]
      exact tsum_nonneg fun k => rungSupportWeight_nonneg J A (k + n)
    ext n
    rw [mem_rungGreedySupport, hrem n]
    constructor
    · intro hmem
      have h0 := hnn (n + 1)
      rw [rungSupportRem_succ, rungSupportWeight_of_mem hmem] at h0
      linarith
    · intro hle
      by_contra hmem
      have hstep := rungSupportRem_succ J A n
      rw [rungSupportWeight_of_notMem hmem] at hstep
      have heq : rungSupportRem J A n = rungSupportRem J A (n + 1) := by linarith
      have hbound : rungSupportRem J A n ≤ rungTail J n := by
        rw [heq, htail (n + 1)]
        refine Real.tsum_le_of_sum_range_le
          (fun k => rungSupportWeight_nonneg J A (k + (n + 1))) ?_
        intro K
        calc ∑ k ∈ Finset.range K, rungSupportWeight J A (k + (n + 1))
            ≤ ∑ k ∈ Finset.range K, rungWeight J (k + (n + 1)) :=
              Finset.sum_le_sum fun k _ => rungSupportWeight_le J A (k + (n + 1))
          _ ≤ rungTail J n := rungWeight_range_shift_le J n K
      have := paper_forced_greedy_tail_lt_weight' hJ n
      linarith
  refine ⟨huniq, ?_, ?_⟩
  · rintro ⟨A, hA, hsum⟩ n hfatal
    have hrem := rungRem_eq_of_tsum hJ hsum n
    have hA' := huniq A hsum
    by_cases hmem : n ∈ rungGreedySupport J
    · exact absurd (mem_rungGreedySupport.1 hmem) (not_le_of_gt hfatal.2)
    · -- a skipped rank has residual bounded by the later tail
      have hf := rungSupportWeight_summable J A
      have htail : ∀ m, rungSupportRem J A m = ∑' k : ℕ, rungSupportWeight J A (k + m) := by
        intro m
        have h := hf.sum_add_tsum_nat_add m
        rw [hsum] at h
        rw [rungSupportRem]
        linarith
      have hmemA : n ∉ A := by rw [hA']; exact hmem
      have hstep := rungSupportRem_succ J A n
      rw [rungSupportWeight_of_notMem hmemA] at hstep
      have heq : rungSupportRem J A n = rungSupportRem J A (n + 1) := by linarith
      have hbound : rungSupportRem J A n ≤ rungTail J n := by
        rw [heq, htail (n + 1)]
        refine Real.tsum_le_of_sum_range_le
          (fun k => rungSupportWeight_nonneg J A (k + (n + 1))) ?_
        intro K
        calc ∑ k ∈ Finset.range K, rungSupportWeight J A (k + (n + 1))
            ≤ ∑ k ∈ Finset.range K, rungWeight J (k + (n + 1)) :=
              Finset.sum_le_sum fun k _ => rungSupportWeight_le J A (k + (n + 1))
          _ ≤ rungTail J n := rungWeight_range_shift_le J n K
      have hfat1 := hfatal.1
      rw [hrem] at hfat1
      linarith
  · intro hsurv
    refine ⟨rungGreedySupport J, ?_, rungGreedy_tsum_eq_half hJ hsurv⟩
    intro n hn
    by_contra hlt
    interval_cases n
    · exact zero_notMem_rungGreedySupport hJ hn
    · exact one_notMem_rungGreedySupport hJ hn

/-- **Long `lem:tr-forced-greedy`, clause three.**  Rank `1` is a safe skip and
ranks `2` and `3` are takes. -/
theorem paper_forced_greedy_low_ranks {J : ℕ} (hJ : 2 ≤ J) :
    (1 ∉ rungGreedySupport J ∧ rungRem J 1 ≤ rungTail J 1) ∧
      2 ∈ rungGreedySupport J ∧ 3 ∈ rungGreedySupport J := by
  have hw2 : rungWeight J 2 ≤ 1 / 3 := by
    have := rungWeight_le_inv (J := J) (n := 2) (by norm_num)
    norm_num at this
    linarith
  have hw3 : rungWeight J 3 ≤ 1 / 7 := by
    have := rungWeight_le_inv (J := J) (n := 3) (by norm_num)
    norm_num at this
    linarith
  have hr1 : rungRem J 1 = 1 / 2 := rungRem_one hJ
  have hr2 : rungRem J 2 = 1 / 2 := by
    have hnot : ¬ (rungWeight J 1 ≤ rungRem J 1) := by
      rw [hr1]; have := half_lt_rungWeight_one hJ; intro h; linarith
    rw [rungRem_succ, if_neg hnot, hr1]
  have hmem2 : 2 ∈ rungGreedySupport J := by
    rw [mem_rungGreedySupport, hr2]; linarith
  have hr3 : rungRem J 3 = 1 / 2 - rungWeight J 2 := by
    have hyes : rungWeight J 2 ≤ rungRem J 2 := hmem2
    rw [rungRem_succ, if_pos hyes, hr2]
  refine ⟨⟨one_notMem_rungGreedySupport hJ, ?_⟩, hmem2, ?_⟩
  · rw [hr1]
    have h := inv_pow_le_rungTail (J := J) (by omega) 1
    norm_num at h
    linarith
  · rw [mem_rungGreedySupport, hr3]; linarith

/-! ## Witness exclusion and the half-LCM horizon, at `J ≥ 2` -/

private theorem rung_witness_exclusion {J n M : ℕ} (hJ : 2 ≤ J) (hn : 4 ≤ n)
    (hMlow : n ≤ M) (hMhigh : M + 2 ≤ 2 * n)
    (hmu : rungMisalign J M ≤ 11 / 15)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 2 ≤ d ∧ d + 1 ≤ n) :
    ¬ (rungTail J n < 1 / 2 - ∑ d ∈ D, rungWeight J d ∧
        1 / 2 - ∑ d ∈ D, rungWeight J d < rungWeight J n) := by
  classical
  rintro ⟨h1, h2⟩
  set ρ : ℝ := 1 / 2 - ∑ d ∈ D, rungWeight J d with hρ
  have hA : (1 : ℝ) / 2 ^ n ≤ rungTail J n := inv_pow_le_rungTail (by omega) n
  set Nnat : ℕ := ∑ d ∈ D, ∑ q ∈ (Finset.Icc 1 J).filter (fun q => q * d ≤ M),
      2 ^ (M - q * d) with hNdef
  set F : ℝ := ∑ d ∈ D, ∑ q ∈ (Finset.Icc 1 J).filter (fun q => ¬ (q * d ≤ M)),
      (2 : ℝ) ^ M / 2 ^ (q * d) with hFdef
  have hdecomp : (2 : ℝ) ^ M * ∑ d ∈ D, rungWeight J d = (Nnat : ℝ) + F := by
    have hcast : (Nnat : ℝ)
        = ∑ d ∈ D, ∑ q ∈ (Finset.Icc 1 J).filter (fun q => q * d ≤ M),
            ((2 : ℝ) ^ (M - q * d)) := by
      rw [hNdef]; push_cast; rfl
    rw [hcast, hFdef, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [rungWeight, Finset.mul_sum,
      ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 J) (fun q => q * d ≤ M)
        (fun q => (2 : ℝ) ^ M * (1 / 2 ^ (q * d)))]
    congr 1
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.mem_filter] at hq
      have h2' : (2 : ℝ) ^ M = 2 ^ (M - q * d) * 2 ^ (q * d) := by
        rw [← pow_add]; congr 1; omega
      rw [h2']
      field_simp
    · exact Finset.sum_congr rfl fun q _ => by ring
  have hFnonneg : 0 ≤ F := by
    rw [hFdef]
    refine Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun q _ => by positivity
  have hscaled : (2 : ℝ) ^ M * ρ = 2 ^ (M - 1) - (Nnat : ℝ) - F := by
    rw [hρ, mul_sub, hdecomp]
    have hhalf : (2 : ℝ) ^ M * (1 / 2) = 2 ^ (M - 1) := by
      have h2' : (2 : ℝ) ^ M = 2 ^ (M - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      rw [h2']; ring
    rw [hhalf]; ring
  have hposside : (2 : ℝ) ^ (M - n) < 2 ^ M * ρ := by
    have hAρ : (1 : ℝ) / 2 ^ n < ρ := lt_of_le_of_lt hA h1
    have hpowpos : (0 : ℝ) < 2 ^ M := by positivity
    have hmul := mul_lt_mul_of_pos_left hAρ hpowpos
    have heq : (2 : ℝ) ^ M * (1 / 2 ^ n) = 2 ^ (M - n) := by
      have h2' : (2 : ℝ) ^ M = 2 ^ (M - n) * 2 ^ n := by
        rw [← pow_add]; congr 1; omega
      rw [h2']; field_simp
    rw [heq] at hmul
    exact hmul
  have hnegside : (2 : ℝ) ^ M * ρ - 2 ^ (M - n) < 4 / 15 := by
    have hins : Finset.Icc 1 J = insert 1 (Finset.Icc 2 J) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 J := by
      simp only [Finset.mem_Icc]; omega
    have hw : rungWeight J n = 1 / 2 ^ n + ∑ q ∈ Finset.Icc 2 J, (1 : ℝ) / 2 ^ (q * n) := by
      rw [rungWeight, hins, Finset.sum_insert hnotmem]
      norm_num
    have h2n : (16 : ℝ) ≤ 2 ^ n := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hx1 : (1 : ℝ) / 2 ^ n < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have hx0 : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
    have hrw : ∑ q ∈ Finset.Icc 2 J, (1 : ℝ) / 2 ^ (q * n)
        = ∑ q ∈ Finset.Icc 2 J, ((1 : ℝ) / 2 ^ n) ^ q :=
      Finset.sum_congr rfl fun q _ => (inv_pow_eq n q).symm
    have htail : ∑ q ∈ Finset.Icc 2 J, ((1 : ℝ) / 2 ^ n) ^ q
        ≤ ((1 : ℝ) / 2 ^ n) ^ 2 / (1 - 1 / 2 ^ n) :=
      sum_pow_le_of_le_index hx0 hx1 2 _ fun q hq => (Finset.mem_Icc.1 hq).1
    have hpowpos : (0 : ℝ) < 2 ^ M := by positivity
    have hstep : ρ - 1 / 2 ^ n < ((1 : ℝ) / 2 ^ n) ^ 2 / (1 - 1 / 2 ^ n) := by
      rw [hw, hrw] at h2
      linarith
    have hmul := mul_lt_mul_of_pos_left hstep hpowpos
    have heq1 : (2 : ℝ) ^ M * (ρ - 1 / 2 ^ n) = 2 ^ M * ρ - 2 ^ (M - n) := by
      have h2' : (2 : ℝ) ^ M = 2 ^ (M - n) * 2 ^ n := by
        rw [← pow_add]; congr 1; omega
      have hh : (2 : ℝ) ^ M * (1 / 2 ^ n) = 2 ^ (M - n) := by
        rw [h2']; field_simp
      rw [mul_sub, hh]
    have hsplitpow : (2 : ℝ) ^ M = 2 ^ (M - n) * 2 ^ n := by
      rw [← pow_add]; congr 1; omega
    have hMn : (2 : ℝ) ^ (M - n) * 4 ≤ 2 ^ n := by
      have hle : M - n + 2 ≤ n := by omega
      calc (2 : ℝ) ^ (M - n) * 4 = 2 ^ (M - n + 2) := by rw [pow_add]; norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hle
    have hne : (2 : ℝ) ^ n - 1 ≠ 0 := by intro h; linarith
    have heq2 : (2 : ℝ) ^ M * (((1 : ℝ) / 2 ^ n) ^ 2 / (1 - 1 / 2 ^ n))
        = 2 ^ (M - n) / (2 ^ n - 1) := by
      rw [hsplitpow]
      have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp
    rw [heq1, heq2] at hmul
    have hfinal : (2 : ℝ) ^ (M - n) / (2 ^ n - 1) ≤ 4 / 15 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hFmu : F ≤ rungMisalign J M := by
    have hF1 : F = ∑ d ∈ D, ∑ q ∈ Finset.Icc 1 J,
        (if q * d ≤ M then (0 : ℝ) else (2 : ℝ) ^ M / 2 ^ (q * d)) := by
      rw [hFdef]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun q _ => by by_cases h : q * d ≤ M <;> simp [h]
    have hF2 : F = ∑ q ∈ Finset.Icc 1 J, ∑ d ∈ D,
        (if q * d ≤ M then (0 : ℝ) else (2 : ℝ) ^ M / 2 ^ (q * d)) := by
      rw [hF1, Finset.sum_comm]
    have hins : Finset.Icc 1 J = insert 1 (Finset.Icc 2 J) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 J := by
      simp only [Finset.mem_Icc]; omega
    have hq1 : ∑ d ∈ D, (if 1 * d ≤ M then (0 : ℝ) else (2 : ℝ) ^ M / 2 ^ (1 * d)) = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      have := hD d hd
      rw [if_pos (by omega)]
    have hterm : ∀ q ∈ Finset.Icc 2 J,
        ∑ d ∈ D, (if q * d ≤ M then (0 : ℝ) else (2 : ℝ) ^ M / 2 ^ (q * d))
          ≤ (2 : ℝ) ^ (M % q) / (2 ^ q - 1) := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      have hq0 : 0 < q := by omega
      have h2q : (4 : ℝ) ≤ 2 ^ q := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq.1
      have hy1 : (1 : ℝ) / 2 ^ q < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      have hy0 : (0 : ℝ) ≤ 1 / 2 ^ q := by positivity
      have hfilter : ∑ d ∈ D, (if q * d ≤ M then (0 : ℝ) else (2 : ℝ) ^ M / 2 ^ (q * d))
          = (2 : ℝ) ^ M * ∑ d ∈ D.filter (fun d => ¬ (q * d ≤ M)),
              ((1 : ℝ) / 2 ^ q) ^ d := by
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        by_cases h : q * d ≤ M
        · simp [h]
        · rw [if_neg h, if_pos h, inv_pow_eq, Nat.mul_comm d q]
          ring
      have hlow : ∀ d ∈ D.filter (fun d => ¬ (q * d ≤ M)), M / q + 1 ≤ d := by
        intro d hd
        rw [Finset.mem_filter] at hd
        have hMd : M < q * d := by omega
        have hdiv : M / q < d := by
          rw [Nat.div_lt_iff_lt_mul hq0, Nat.mul_comm d q]
          exact hMd
        omega
      have hgeo := sum_pow_le_of_le_index hy0 hy1 (M / q + 1) _ hlow
      have hdm : q * (M / q) + M % q = M := Nat.div_add_mod M q
      have hpq : (2 : ℝ) ^ q ≠ 0 := by positivity
      have hpk : (2 : ℝ) ^ (q * (M / q)) ≠ 0 := by positivity
      have hqm : (2 : ℝ) ^ q - 1 ≠ 0 := by intro h; linarith
      have hkey : (2 : ℝ) ^ M * (((1 : ℝ) / 2 ^ q) ^ (M / q + 1) / (1 - 1 / 2 ^ q))
          = 2 ^ (M % q) / (2 ^ q - 1) := by
        have e1 : ((1 : ℝ) / 2 ^ q) ^ (M / q + 1) = 1 / (2 ^ (q * (M / q)) * 2 ^ q) := by
          rw [inv_pow_eq, ← pow_add]
          congr 2
          ring
        have e2 : (2 : ℝ) ^ M = 2 ^ (M % q) * 2 ^ (q * (M / q)) := by
          rw [← pow_add]; congr 1; omega
        rw [e1, e2]
        field_simp
      calc ∑ d ∈ D, (if q * d ≤ M then (0 : ℝ) else (2 : ℝ) ^ M / 2 ^ (q * d))
          = (2 : ℝ) ^ M * ∑ d ∈ D.filter (fun d => ¬ (q * d ≤ M)),
              ((1 : ℝ) / 2 ^ q) ^ d := hfilter
        _ ≤ (2 : ℝ) ^ M * (((1 : ℝ) / 2 ^ q) ^ (M / q + 1) / (1 - 1 / 2 ^ q)) := by
            exact mul_le_mul_of_nonneg_left hgeo (by positivity)
        _ = (2 : ℝ) ^ (M % q) / (2 ^ q - 1) := hkey
    calc F = ∑ q ∈ Finset.Icc 1 J, ∑ d ∈ D,
            (if q * d ≤ M then (0 : ℝ) else (2 : ℝ) ^ M / 2 ^ (q * d)) := hF2
      _ = ∑ d ∈ D, (if 1 * d ≤ M then (0 : ℝ) else (2 : ℝ) ^ M / 2 ^ (1 * d))
          + ∑ q ∈ Finset.Icc 2 J, ∑ d ∈ D,
            (if q * d ≤ M then (0 : ℝ) else (2 : ℝ) ^ M / 2 ^ (q * d)) := by
          rw [hins, Finset.sum_insert hnotmem]
      _ ≤ 0 + rungMisalign J M := by
          rw [hq1, rungMisalign]
          simpa using Finset.sum_le_sum hterm
      _ = rungMisalign J M := by ring
  have hZ : ((2 ^ (M - 1) - (Nnat : ℤ) - 2 ^ (M - n) : ℤ) : ℝ)
      = (2 : ℝ) ^ M * ρ + F - 2 ^ (M - n) := by
    push_cast
    rw [hscaled]
    ring
  have hZpos : (0 : ℝ) < ((2 ^ (M - 1) - (Nnat : ℤ) - 2 ^ (M - n) : ℤ) : ℝ) := by
    rw [hZ]; linarith
  have hZlt : ((2 ^ (M - 1) - (Nnat : ℤ) - 2 ^ (M - n) : ℤ) : ℝ) < 1 := by
    rw [hZ]; linarith
  have h0 : (0 : ℤ) < 2 ^ (M - 1) - (Nnat : ℤ) - 2 ^ (M - n) := by exact_mod_cast hZpos
  have h1' : (2 ^ (M - 1) - (Nnat : ℤ) - 2 ^ (M - n) : ℤ) < 1 := by exact_mod_cast hZlt
  omega

private theorem rung_half_lcm_horizon {J n : ℕ} (hJ : 2 ≤ J) (hn4 : 4 ≤ n)
    (hn : rungLcm J / 2 + 1 ≤ n) :
    ∃ M : ℕ, n ≤ M ∧ M + 2 ≤ 2 * n ∧ rungMisalign J M < 11 / 15 := by
  classical
  set L := rungLcm J with hLdef
  have hmem2 : (2 : ℕ) ∈ Finset.Icc 2 J := Finset.mem_Icc.2 ⟨le_refl 2, hJ⟩
  have hdvd2 : (2 : ℕ) ∣ L := by
    rw [hLdef, rungLcm]
    simpa using Finset.dvd_lcm (f := (id : ℕ → ℕ)) hmem2
  have hL0 : L ≠ 0 := by
    rw [hLdef, rungLcm, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨q, hq, hq0⟩
    rw [Finset.mem_Icc] at hq
    simp only [id_eq] at hq0
    omega
  obtain ⟨t, ht⟩ := hdvd2
  set k := (n - 1) / L with hkdef
  set r := (n - 1) % L with hrdef
  have hdm : L * k + r = n - 1 := Nat.div_add_mod (n - 1) L
  have hrlt : r < L := Nat.mod_lt _ (Nat.pos_of_ne_zero hL0)
  refine ⟨L * (k + 1), ?_, ?_, ?_⟩
  · have hexp : L * (k + 1) = L * k + L := by ring
    omega
  · rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · have hexp : L * (k + 1) = L * k + L := by ring
      have hk : L * k = 0 := by rw [hk0]; ring
      omega
    · have hexp : L * (k + 1) = L * k + L := by ring
      have hLk : L ≤ L * k := Nat.le_mul_of_pos_right L hk1
      omega
  · have hmod : ∀ q ∈ Finset.Icc 2 J, (L * (k + 1)) % q = 0 := by
      intro q hq
      have hqL : q ∣ L := by
        rw [hLdef, rungLcm]
        simpa using Finset.dvd_lcm (f := (id : ℕ → ℕ)) hq
      obtain ⟨c, hc⟩ := hqL
      rw [hc, mul_assoc]
      exact Nat.mul_mod_right q (c * (k + 1))
    have hval : rungMisalign J (L * (k + 1))
        = ∑ q ∈ Finset.Icc 2 J, (1 : ℝ) / (2 ^ q - 1) := by
      rw [rungMisalign]
      exact Finset.sum_congr rfl fun q hq => by rw [hmod q hq]; norm_num
    rw [hval]
    have hstep : ∀ q ∈ Finset.Icc 2 J,
        (1 : ℝ) / (2 ^ q - 1) ≤ (4 / 3) * ((1 : ℝ) / 2) ^ q := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      have h4 : (4 : ℝ) ≤ 2 ^ q := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq.1
      have hp : (0 : ℝ) < 2 ^ q := by positivity
      have hq1 : (0 : ℝ) < 2 ^ q - 1 := by linarith
      have hpow : ((1 : ℝ) / 2) ^ q = 1 / 2 ^ q := by rw [div_pow, one_pow]
      rw [hpow, div_le_iff₀ hq1]
      have hmul : (4 / 3 : ℝ) * (1 / 2 ^ q) * (2 ^ q - 1) = 4 / 3 - 4 / (3 * 2 ^ q) := by
        field_simp
      rw [hmul]
      have : (4 : ℝ) / (3 * 2 ^ q) ≤ 1 / 3 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
    have hgeo : ∑ q ∈ Finset.Icc 2 J, ((1 : ℝ) / 2) ^ q ≤ ((1 : ℝ) / 2) ^ 2 / (1 - 1 / 2) :=
      sum_pow_le_of_le_index (by norm_num) (by norm_num) 2 _
        fun q hq => (Finset.mem_Icc.1 hq).1
    have hsum : ∑ q ∈ Finset.Icc 2 J, (1 : ℝ) / (2 ^ q - 1)
        ≤ ∑ q ∈ Finset.Icc 2 J, (4 / 3) * ((1 : ℝ) / 2) ^ q :=
      Finset.sum_le_sum hstep
    rw [← Finset.mul_sum] at hsum
    have hnum : ((1 : ℝ) / 2) ^ 2 / (1 - 1 / 2) = 1 / 2 := by norm_num
    rw [hnum] at hgeo
    nlinarith [hsum, hgeo]

/-! ## `thm:tr-finite-decision` -/

/-- A rank `n` is **bad** for `J` when no `M ∈ [n, 2n-2]` passes the witness
test `μ_J(M) ≤ 11/15`. -/
def RungBad (J n : ℕ) : Prop :=
  ∀ M : ℕ, n ≤ M → M + 2 ≤ 2 * n → ¬ (rungMisalign J M ≤ 11 / 15)

open Classical in
/-- The bad ranks inside the manuscript's finite window `[4, L_J/2]`. -/
noncomputable def rungBadFinset (J : ℕ) : Finset ℕ :=
  (Finset.Icc 4 (rungLcm J / 2)).filter (fun n => RungBad J n)

open Classical in
theorem mem_rungBadFinset {J n : ℕ} :
    n ∈ rungBadFinset J ↔ (4 ≤ n ∧ n ≤ rungLcm J / 2) ∧ RungBad J n := by
  rw [rungBadFinset, Finset.mem_filter, Finset.mem_Icc]

/-- The manuscript's `B(J) = max(bad ∪ {3})`. -/
noncomputable def rungDecisionHorizon (J : ℕ) : ℕ :=
  (insert 3 (rungBadFinset J)).max' ⟨3, Finset.mem_insert_self 3 _⟩

theorem three_le_rungDecisionHorizon (J : ℕ) : 3 ≤ rungDecisionHorizon J :=
  Finset.le_max' _ 3 (Finset.mem_insert_self 3 _)

theorem rungBad_le_horizon {J n : ℕ} (h : n ∈ rungBadFinset J) :
    n ≤ rungDecisionHorizon J :=
  Finset.le_max' _ n (Finset.mem_insert_of_mem h)

/-- **Long `thm:tr-finite-decision`.**  For `J ≥ 2`, `HalfRung(J)` holds iff
the greedy orbit for `1/2` under the weights `w_n^{(J)}` survives every rank
from `2` through `B(J)`.  Since `B(J)` is computed from the finite window
`[4, L_J/2]`, this is a finite exact decision procedure. -/
theorem paper_rung_finite_decision {J : ℕ} (hJ : 2 ≤ J) :
    HalfRung J ↔ ∀ n : ℕ, 2 ≤ n → n ≤ rungDecisionHorizon J → ¬ RungFatal J n := by
  classical
  constructor
  · intro hhalf n _ _
    exact ((paper_forced_greedy_unique_support_and_criterion hJ).2.1 hhalf) n
  · intro hwindow
    refine (paper_forced_greedy_unique_support_and_criterion hJ).2.2 ?_
    intro n
    by_cases hsmall : n ≤ rungDecisionHorizon J
    · rcases Nat.lt_or_ge n 2 with hlt | hge
      · -- ranks `0` and `1` are safe outright
        interval_cases n
        · rintro ⟨hfat, -⟩
          have h := inv_pow_le_rungTail (J := J) (by omega) 0
          rw [rungRem_zero] at hfat
          norm_num at h
          linarith
        · rintro ⟨hfat, -⟩
          have h := inv_pow_le_rungTail (J := J) (by omega) 1
          rw [rungRem_one hJ] at hfat
          norm_num at h
          linarith
      · exact hwindow n hge hsmall
    · -- past the horizon a witness always exists
      push_neg at hsmall
      have hn4 : 4 ≤ n := by
        have := three_le_rungDecisionHorizon J
        omega
      have hwit : ∃ M : ℕ, n ≤ M ∧ M + 2 ≤ 2 * n ∧ rungMisalign J M ≤ 11 / 15 := by
        by_cases hwin : n ≤ rungLcm J / 2
        · by_cases hbad : RungBad J n
          · exact absurd (rungBad_le_horizon (mem_rungBadFinset.2 ⟨⟨hn4, hwin⟩, hbad⟩))
              (by omega)
          · rw [RungBad] at hbad
            push_neg at hbad
            obtain ⟨M, hM1, hM2, hM3⟩ := hbad
            exact ⟨M, hM1, hM2, hM3⟩
        · push_neg at hwin
          obtain ⟨M, hM1, hM2, hM3⟩ := rung_half_lcm_horizon hJ hn4 (by omega)
          exact ⟨M, hM1, hM2, le_of_lt hM3⟩
      obtain ⟨M, hM1, hM2, hM3⟩ := hwit
      have hD : ∀ d ∈ (Finset.range n).filter (fun d => d ∈ rungGreedySupport J),
          2 ≤ d ∧ d + 1 ≤ n := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_range] at hd
        refine ⟨?_, by omega⟩
        by_contra hlt
        interval_cases d
        · exact zero_notMem_rungGreedySupport hJ hd.2
        · exact one_notMem_rungGreedySupport hJ hd.2
      have hsum : ∑ d ∈ (Finset.range n).filter (fun d => d ∈ rungGreedySupport J),
            rungWeight J d
          = ∑ m ∈ Finset.range n, rungSupportWeight J (rungGreedySupport J) m := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        by_cases hm : m ∈ rungGreedySupport J
        · rw [if_pos hm, rungSupportWeight_of_mem hm]
        · rw [if_neg hm, rungSupportWeight_of_notMem hm]
      have hrem : rungRem J n
          = 1 / 2 - ∑ d ∈ (Finset.range n).filter (fun d => d ∈ rungGreedySupport J),
              rungWeight J d := by
        rw [hsum, rungRem_eq_supportRem_greedy, rungSupportRem]
      rw [RungFatal, hrem]
      exact rung_witness_exclusion hJ hn4 hM1 hM2 hM3 _ hD

#print axioms paper_forced_greedy_tail_lt_weight'
#print axioms paper_forced_greedy_unique_support_and_criterion
#print axioms paper_forced_greedy_low_ranks
#print axioms paper_rung_finite_decision
#print axioms rungWeight_summable
#print axioms rungTail_succ
#print axioms rungRem_eq_supportRem_greedy

end ErdosProblems.Erdos257.PaperCompleteR21
