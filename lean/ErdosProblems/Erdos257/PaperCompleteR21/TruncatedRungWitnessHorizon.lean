import Erdos249257.GreedyAchievementSet
import Erdos249257.DiagonalPincerDecomposition

/-!
Paper-form restatements from the "Successive tail truncations" subsection of
the long Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`
(lines 5950–6110).  The subsection fixes `J ≥ 2` and works with the truncated
geometric weights

* `truncWeight J n = w_n^{(J)} = ∑_{q=1}^{J} 2^{-qn}`,
* `truncTail J n = T_{n+1}^{(J)} = ∑_{q=1}^{J} 2^{-qn}/(2^q-1)`, the complete
  mass of those weights at ranks `> n`,
* `misalignMass J M = μ_J(M) = ∑_{q=2}^{J} 2^{M mod q}/(2^q-1)`,
* `truncLcm J = L_J = lcm(2,3,…,J)`.

Covered here:

* `lem:tr-forced-greedy` (line 5974), first and third clauses — `w_n > T_{n+1}`
  for every `n`, rank `1` is a safe skip, ranks `2` and `3` are takes;
* `lem:tr-parity` (line 5983) — no finite `A ⊆ {2,3,…}` attains `1/2`;
* `thm:tr-witness-exclusion` (line 5995) — the misalignment-mass witness test;
* `cor:tr-half-lcm` (line 6027) — a witness exists past the half-LCM horizon;
* `lem:tr-mod12` (line 6050) — for `J ≥ 7` a witness index is a multiple of 12.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

/-- The manuscript's `w_n^{(J)} = ∑_{q=1}^{J} 2^{-qn}`. -/
noncomputable def truncWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)

/-- The manuscript's `T_{n+1}^{(J)} = ∑_{q=1}^{J} 2^{-qn}/(2^q-1)`. -/
noncomputable def truncTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))

/-- The manuscript's misalignment mass `μ_J(M) = ∑_{q=2}^{J} 2^{M mod q}/(2^q-1)`. -/
noncomputable def misalignMass (J M : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 J, (2 : ℝ) ^ (M % q) / (2 ^ q - 1)

/-- The manuscript's `L_J = lcm(2,3,…,J)`. -/
def truncLcm (J : ℕ) : ℕ := (Finset.Icc 2 J).lcm id

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

/-- Geometric tail bound over an arbitrary finite index set bounded below. -/
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

private theorem truncWeight_le_inv {J n : ℕ} (hn : 1 ≤ n) :
    truncWeight J n ≤ 1 / (2 ^ n - 1) := by
  have h2 : (2 : ℝ) ≤ 2 ^ n := two_le_two_pow hn
  have hx1 : (1 : ℝ) / 2 ^ n < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hx0 : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
  have hrw : truncWeight J n = ∑ q ∈ Finset.Icc 1 J, ((1 : ℝ) / 2 ^ n) ^ q := by
    rw [truncWeight]
    exact Finset.sum_congr rfl fun q _ => (inv_pow_eq n q).symm
  have hbd := sum_pow_le_of_le_index hx0 hx1 1 (Finset.Icc 1 J)
    (fun q hq => (Finset.mem_Icc.1 hq).1)
  rw [hrw]
  refine hbd.trans (le_of_eq ?_)
  have hne : (2 : ℝ) ^ n - 1 ≠ 0 := by intro h; linarith
  have hne2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-! ## `lem:tr-forced-greedy`: the weight dominates the whole later tail -/

/-- Long `lem:tr-forced-greedy`, first clause.  For every `J ≥ 2` and every
`n`, the truncated weight `w_n^{(J)}` strictly exceeds the complete later tail
`T_{n+1}^{(J)}`: the `q = 1` terms agree and every `q ≥ 2` tail term is
strictly smaller than the matching weight term. -/
theorem paper_forced_greedy_tail_lt_weight {J : ℕ} (hJ : 2 ≤ J) (n : ℕ) :
    truncTail J n < truncWeight J n := by
  rw [truncTail, truncWeight]
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

/-- Long `lem:tr-forced-greedy`, third clause, rank one.  The rank-`1` weight
exceeds the target `1/2`, so the greedy rule skips it, and the skip is safe:
the whole later tail `T_2^{(J)}` is still at least `1/2`. -/
theorem paper_forced_greedy_rank_one_safe_skip {J : ℕ} (hJ : 2 ≤ J) :
    (1 : ℝ) / 2 < truncWeight J 1 ∧ (1 : ℝ) / 2 ≤ truncTail J 1 := by
  constructor
  · have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 J := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_Icc.2 (by omega)
    have hle : ∑ q ∈ ({1, 2} : Finset ℕ), (1 : ℝ) / 2 ^ (q * 1) ≤ truncWeight J 1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
    have hval : ∑ q ∈ ({1, 2} : Finset ℕ), (1 : ℝ) / 2 ^ (q * 1) = 3 / 4 := by
      norm_num
    rw [hval] at hle
    linarith
  · have hmem : (1 : ℕ) ∈ Finset.Icc 1 J := Finset.mem_Icc.2 (by omega)
    have hnn : ∀ i ∈ Finset.Icc 1 J, (0 : ℝ) ≤ 1 / (2 ^ (i * 1) * (2 ^ i - 1)) := by
      intro i hi
      have h2 : (2 : ℝ) ≤ 2 ^ i := two_le_two_pow (Finset.mem_Icc.1 hi).1
      have hp : (0 : ℝ) < 2 ^ (i * 1) := by positivity
      have : (0 : ℝ) < 2 ^ (i * 1) * (2 ^ i - 1) := by nlinarith
      positivity
    calc (1 : ℝ) / 2 = 1 / (2 ^ (1 * 1) * (2 ^ 1 - 1)) := by norm_num
      _ ≤ ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * 1) * (2 ^ q - 1)) :=
          Finset.single_le_sum hnn hmem
      _ = truncTail J 1 := rfl

/-- Long `lem:tr-forced-greedy`, third clause, ranks two and three.  With
target `1/2` the greedy rule takes rank `2` (its weight is at most the
residual `1/2`) and then takes rank `3` (its weight is at most the new
residual `1/2 - w_2^{(J)}`). -/
theorem paper_forced_greedy_ranks_two_three_taken (J : ℕ) :
    truncWeight J 2 ≤ 1 / 2 ∧ truncWeight J 3 ≤ 1 / 2 - truncWeight J 2 := by
  have h2 : truncWeight J 2 ≤ 1 / 3 := by
    have := truncWeight_le_inv (J := J) (n := 2) (by norm_num)
    norm_num at this
    linarith
  have h3 : truncWeight J 3 ≤ 1 / 7 := by
    have := truncWeight_le_inv (J := J) (n := 3) (by norm_num)
    norm_num at this
    linarith
  exact ⟨by linarith, by linarith⟩

/-! ## `lem:tr-parity`: finite supports never attain the target -/

/-- Long `lem:tr-parity`.  For every `J ≥ 2`, no finite `A ⊆ {2,3,…}` has
`∑_{n ∈ A} w_n^{(J)} = 1/2`. -/
theorem paper_parity_excludes_finite_support {J : ℕ} (hJ : 2 ≤ J)
    (A : Finset ℕ) (hA : ∀ n ∈ A, 2 ≤ n) :
    ∑ n ∈ A, truncWeight J n ≠ 1 / 2 := by
  classical
  intro hsum
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty] at hsum
    norm_num at hsum
  set m := A.max' hne with hmdef
  have hmA : m ∈ A := A.max'_mem hne
  have hmax : ∀ n ∈ A, n ≤ m := fun n hn => A.le_max' n hn
  have hm2 : 2 ≤ m := hA m hmA
  have hJm : 4 ≤ J * m := Nat.mul_le_mul hJ hm2
  set S : ℕ := ∑ n ∈ A, ∑ q ∈ Finset.Icc 1 J, 2 ^ (J * m - q * n) with hSdef
  have hSreal : (S : ℝ) = 2 ^ (J * m) * ∑ n ∈ A, truncWeight J n := by
    rw [hSdef, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [truncWeight, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_Icc] at hq
    have hle : q * n ≤ J * m := Nat.mul_le_mul hq.2 (hmax n hn)
    have h2 : (2 : ℝ) ^ (J * m) = 2 ^ (J * m - q * n) * 2 ^ (q * n) := by
      rw [← pow_add]; congr 1; omega
    rw [h2]
    field_simp
  have hSval : S = 2 ^ (J * m - 1) := by
    have hreal : (S : ℝ) = 2 ^ (J * m - 1) := by
      rw [hSreal, hsum]
      have h2 : (2 : ℝ) ^ (J * m) = 2 ^ (J * m - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      rw [h2]; ring
    exact_mod_cast hreal
  have hfar : (2 : ℕ) ∣ ∑ n ∈ A.erase m, ∑ q ∈ Finset.Icc 1 J, 2 ^ (J * m - q * n) := by
    refine Finset.dvd_sum fun n hn => Finset.dvd_sum fun q hq => ?_
    rw [Finset.mem_erase] at hn
    rw [Finset.mem_Icc] at hq
    have hnm : n < m := lt_of_le_of_ne (hmax n hn.2) hn.1
    have h4 : q * n ≤ J * n := Nat.mul_le_mul hq.2 (le_refl n)
    have h5 : J * (n + 1) ≤ J * m := Nat.mul_le_mul (le_refl J) (by omega)
    have h6 : J * n + J ≤ J * m := by
      have : J * (n + 1) = J * n + J := by ring
      omega
    exact dvd_pow_self 2 (by omega)
  have hnear : (2 : ℕ) ∣ ∑ q ∈ (Finset.Icc 1 J).erase J, 2 ^ (J * m - q * m) := by
    refine Finset.dvd_sum fun q hq => ?_
    rw [Finset.mem_erase, Finset.mem_Icc] at hq
    have h7 : (q + 1) * m ≤ J * m := Nat.mul_le_mul (by omega) (le_refl m)
    have h8 : (q + 1) * m = q * m + m := by ring
    exact dvd_pow_self 2 (by omega)
  have hJmem : J ∈ Finset.Icc 1 J := Finset.mem_Icc.2 (by omega)
  have hmid : ∑ q ∈ Finset.Icc 1 J, 2 ^ (J * m - q * m)
      = 1 + ∑ q ∈ (Finset.Icc 1 J).erase J, 2 ^ (J * m - q * m) := by
    rw [← Finset.add_sum_erase _ _ hJmem]
    congr 1
    simp
  have hsplit : S = (1 + ∑ q ∈ (Finset.Icc 1 J).erase J, 2 ^ (J * m - q * m))
      + ∑ n ∈ A.erase m, ∑ q ∈ Finset.Icc 1 J, 2 ^ (J * m - q * n) := by
    rw [hSdef, ← Finset.add_sum_erase _ _ hmA, hmid]
  have hev : (2 : ℕ) ∣ S := by
    rw [hSval]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨a, ha⟩ := hfar
  obtain ⟨b, hb⟩ := hnear
  obtain ⟨c, hc⟩ := hev
  omega

/-! ## `thm:tr-witness-exclusion` -/

/-- Long `thm:tr-witness-exclusion`.  Let `J ≥ 3`, `n ≥ 4`, and suppose some
`M ∈ [n, 2n-2]` has `μ_J(M) ≤ 11/15`.  Then no Boolean prefix
`D ⊆ {2,…,n-1}` leaves a residual strictly inside the fatal gap
`(T_{n+1}^{(J)}, w_n^{(J)})`.  The exclusion is for every prefix, not only the
greedy one. -/
theorem paper_witness_exclusion {J n M : ℕ} (hJ : 3 ≤ J) (hn : 4 ≤ n)
    (hMlow : n ≤ M) (hMhigh : M + 2 ≤ 2 * n)
    (hmu : misalignMass J M ≤ 11 / 15)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 2 ≤ d ∧ d + 1 ≤ n) :
    ¬ (truncTail J n < 1 / 2 - ∑ d ∈ D, truncWeight J d ∧
        1 / 2 - ∑ d ∈ D, truncWeight J d < truncWeight J n) := by
  classical
  rintro ⟨h1, h2⟩
  set ρ : ℝ := 1 / 2 - ∑ d ∈ D, truncWeight J d with hρ
  -- the `q = 1` term of the tail is `2^{-n}`
  have hA : (1 : ℝ) / 2 ^ n ≤ truncTail J n := by
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 J := Finset.mem_Icc.2 (by omega)
    have hnn : ∀ i ∈ Finset.Icc 1 J, (0 : ℝ) ≤ 1 / (2 ^ (i * n) * (2 ^ i - 1)) := by
      intro i hi
      have h2i : (2 : ℝ) ≤ 2 ^ i := two_le_two_pow (Finset.mem_Icc.1 hi).1
      have hp : (0 : ℝ) < 2 ^ (i * n) := by positivity
      have : (0 : ℝ) < 2 ^ (i * n) * (2 ^ i - 1) := by nlinarith
      positivity
    calc (1 : ℝ) / 2 ^ n = 1 / (2 ^ (1 * n) * (2 ^ 1 - 1)) := by norm_num
      _ ≤ ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1)) :=
          Finset.single_le_sum hnn hmem
      _ = truncTail J n := rfl
  -- the integer part and the fractional part of the scaled prefix value
  set Nnat : ℕ := ∑ d ∈ D, ∑ q ∈ (Finset.Icc 1 J).filter (fun q => q * d ≤ M),
      2 ^ (M - q * d) with hNdef
  set F : ℝ := ∑ d ∈ D, ∑ q ∈ (Finset.Icc 1 J).filter (fun q => ¬ (q * d ≤ M)),
      (2 : ℝ) ^ M / 2 ^ (q * d) with hFdef
  have hdecomp : (2 : ℝ) ^ M * ∑ d ∈ D, truncWeight J d = (Nnat : ℝ) + F := by
    have hcast : (Nnat : ℝ)
        = ∑ d ∈ D, ∑ q ∈ (Finset.Icc 1 J).filter (fun q => q * d ≤ M),
            ((2 : ℝ) ^ (M - q * d)) := by
      rw [hNdef]; push_cast; rfl
    rw [hcast, hFdef, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [truncWeight, Finset.mul_sum,
      ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 J) (fun q => q * d ≤ M)
        (fun q => (2 : ℝ) ^ M * (1 / 2 ^ (q * d)))]
    congr 1
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.mem_filter] at hq
      have h2 : (2 : ℝ) ^ M = 2 ^ (M - q * d) * 2 ^ (q * d) := by
        rw [← pow_add]; congr 1; omega
      rw [h2]
      field_simp
    · exact Finset.sum_congr rfl fun q _ => by ring
  have hFnonneg : 0 ≤ F := by
    rw [hFdef]
    refine Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun q _ => by positivity
  have hscaled : (2 : ℝ) ^ M * ρ = 2 ^ (M - 1) - (Nnat : ℝ) - F := by
    rw [hρ, mul_sub, hdecomp]
    have hhalf : (2 : ℝ) ^ M * (1 / 2) = 2 ^ (M - 1) := by
      have h2 : (2 : ℝ) ^ M = 2 ^ (M - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      rw [h2]; ring
    rw [hhalf]; ring
  -- strictly positive side
  have hposside : (2 : ℝ) ^ (M - n) < 2 ^ M * ρ := by
    have hAρ : (1 : ℝ) / 2 ^ n < ρ := lt_of_le_of_lt hA h1
    have hpowpos : (0 : ℝ) < 2 ^ M := by positivity
    have hmul := mul_lt_mul_of_pos_left hAρ hpowpos
    have heq : (2 : ℝ) ^ M * (1 / 2 ^ n) = 2 ^ (M - n) := by
      have h2 : (2 : ℝ) ^ M = 2 ^ (M - n) * 2 ^ n := by
        rw [← pow_add]; congr 1; omega
      rw [h2]; field_simp
    rw [heq] at hmul
    exact hmul
  -- strictly bounded side
  have hnegside : (2 : ℝ) ^ M * ρ - 2 ^ (M - n) < 4 / 15 := by
    have hins : Finset.Icc 1 J = insert 1 (Finset.Icc 2 J) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 J := by
      simp only [Finset.mem_Icc]; omega
    have hw : truncWeight J n = 1 / 2 ^ n + ∑ q ∈ Finset.Icc 2 J, (1 : ℝ) / 2 ^ (q * n) := by
      rw [truncWeight, hins, Finset.sum_insert hnotmem]
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
      have h2 : (2 : ℝ) ^ M = 2 ^ (M - n) * 2 ^ n := by
        rw [← pow_add]; congr 1; omega
      have : (2 : ℝ) ^ M * (1 / 2 ^ n) = 2 ^ (M - n) := by
        rw [h2]; field_simp
      rw [mul_sub, this]
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
  -- the fractional part is bounded by the misalignment mass
  have hFmu : F ≤ misalignMass J M := by
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
        have : M / q < d := by
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
      _ ≤ 0 + misalignMass J M := by
          rw [hq1, misalignMass]
          simpa using Finset.sum_le_sum hterm
      _ = misalignMass J M := by ring
  -- an integer strictly between zero and one
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

/-! ## `cor:tr-half-lcm` -/

/-- Long `cor:tr-half-lcm`.  For `J ≥ 2` and every `n ≥ max{4, L_J/2 + 1}`
there is a witness `M ∈ [n, 2n-2]` with `μ_J(M) < 11/15`; only the finite
window `[4, L_J/2]` can escape the witness test. -/
theorem paper_half_lcm_horizon {J n : ℕ} (hJ : 2 ≤ J) (hn4 : 4 ≤ n)
    (hn : truncLcm J / 2 + 1 ≤ n) :
    ∃ M : ℕ, n ≤ M ∧ M + 2 ≤ 2 * n ∧ misalignMass J M < 11 / 15 := by
  classical
  set L := truncLcm J with hLdef
  have hmem2 : (2 : ℕ) ∈ Finset.Icc 2 J := Finset.mem_Icc.2 ⟨le_refl 2, hJ⟩
  have hdvd2 : (2 : ℕ) ∣ L := by
    rw [hLdef, truncLcm]
    simpa using Finset.dvd_lcm (f := (id : ℕ → ℕ)) hmem2
  have hL0 : L ≠ 0 := by
    rw [hLdef, truncLcm, Ne, Finset.lcm_eq_zero_iff]
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
        rw [hLdef, truncLcm]
        simpa using Finset.dvd_lcm (f := (id : ℕ → ℕ)) hq
      obtain ⟨c, hc⟩ := hqL
      rw [hc, mul_assoc]
      exact Nat.mul_mod_right q (c * (k + 1))
    have hval : misalignMass J (L * (k + 1))
        = ∑ q ∈ Finset.Icc 2 J, (1 : ℝ) / (2 ^ q - 1) := by
      rw [misalignMass]
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

/-! ## `lem:tr-mod12` -/

/-- Long `lem:tr-mod12`.  For `J ≥ 7`, the witness inequality
`μ_J(M) ≤ 11/15` forces `12 ∣ M`, so only multiples of `12` need to be tested
as witnesses. -/
theorem paper_mod_twelve_filter {J M : ℕ} (hJ : 7 ≤ J)
    (hmu : misalignMass J M ≤ 11 / 15) : 12 ∣ M := by
  classical
  by_contra hdvd
  have hsub : ({2, 3, 4, 6} : Finset ℕ) ⊆ Finset.Icc 2 J := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Finset.mem_Icc.2 (by omega)
  have hlow : ∑ q ∈ ({2, 3, 4, 6} : Finset ℕ), (2 : ℝ) ^ (M % q) / (2 ^ q - 1)
      ≤ misalignMass J M := by
    rw [misalignMass]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi _ => ?_
    have h2 : (2 : ℝ) ≤ 2 ^ i := two_le_two_pow (by
      have := Finset.mem_Icc.1 hi; omega)
    exact div_nonneg (by positivity) (by linarith)
  have hexp : ∑ q ∈ ({2, 3, 4, 6} : Finset ℕ), (2 : ℝ) ^ (M % q) / (2 ^ q - 1)
      = 2 ^ (M % 2) / 3 + 2 ^ (M % 3) / 7 + 2 ^ (M % 4) / 15 + 2 ^ (M % 6) / 63 := by
    norm_num [Finset.sum_insert, Finset.mem_insert]
    ring
  obtain ⟨r, hr⟩ : ∃ r, M % 12 = r := ⟨M % 12, rfl⟩
  have hrlt : r < 12 := by rw [← hr]; exact Nat.mod_lt _ (by norm_num)
  have hrne : r ≠ 0 := by
    rintro rfl
    exact hdvd (Nat.dvd_of_mod_eq_zero hr)
  have e2 : M % 2 = r % 2 := by
    rw [← hr, Nat.mod_mod_of_dvd M (by norm_num : (2 : ℕ) ∣ 12)]
  have e3 : M % 3 = r % 3 := by
    rw [← hr, Nat.mod_mod_of_dvd M (by norm_num : (3 : ℕ) ∣ 12)]
  have e4 : M % 4 = r % 4 := by
    rw [← hr, Nat.mod_mod_of_dvd M (by norm_num : (4 : ℕ) ∣ 12)]
  have e6 : M % 6 = r % 6 := by
    rw [← hr, Nat.mod_mod_of_dvd M (by norm_num : (6 : ℕ) ∣ 12)]
  have hbig : (11 : ℝ) / 15
      < ∑ q ∈ ({2, 3, 4, 6} : Finset ℕ), (2 : ℝ) ^ (M % q) / (2 ^ q - 1) := by
    rw [hexp, e2, e3, e4, e6]
    interval_cases r
    · exact absurd rfl hrne
    all_goals norm_num
  linarith

#print axioms paper_forced_greedy_tail_lt_weight
#print axioms paper_forced_greedy_rank_one_safe_skip
#print axioms paper_forced_greedy_ranks_two_three_taken
#print axioms paper_parity_excludes_finite_support
#print axioms paper_witness_exclusion
#print axioms paper_half_lcm_horizon
#print axioms paper_mod_twelve_filter

end ErdosProblems.Erdos257.PaperCompleteR21
