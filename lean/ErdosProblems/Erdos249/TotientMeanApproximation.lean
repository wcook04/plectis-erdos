import Erdos249257.MersenneLambertLadder
import ErdosProblems.Erdos269.PaperR8UniformRank
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Normalized totient: finite-rank mean approximation

The arithmetic matrix `φ(i+n)/(i+n)` has finite-rank approximants obtained by
truncating its Möbius divisor expansion.  The final finite-square estimate is
uniform in the size of the square; it concerns mean error, not uniform error.
-/

namespace ErdosProblems.Erdos249.TotientMeanApproximation

open scoped BigOperators
open ArithmeticFunction

/-- The normalized totient on positive integers. -/
noncomputable def normalizedTotient (m : ℕ) : ℝ :=
  (Nat.totient m : ℝ) / m

/-- The `D`-term Möbius approximation to the normalized totient. -/
noncomputable def truncatedTotient (D m : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D,
    if d ∣ m then ((moebius d : ℤ) : ℝ) / d else 0

/-- A modular divisibility test is a sum of `d` separated residue tests. -/
private theorem divisor_indicator_factor (d i n : ℕ) (hd : 0 < d) :
    (if d ∣ i + n then (1 : ℝ) else 0) =
      ∑ a : Fin d,
        (if i % d = a.val then (1 : ℝ) else 0) *
          (if (n : ZMod d) = -(a.val : ZMod d) then (1 : ℝ) else 0) := by
  let a : Fin d := ⟨i % d, Nat.mod_lt _ hd⟩
  have heq : ((n : ZMod d) = -(i : ZMod d)) ↔ d ∣ i + n := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← Nat.cast_add,
      ZMod.natCast_eq_zero_iff]
  have hcast : ((a.val : ℕ) : ZMod d) = (i : ZMod d) :=
    ZMod.natCast_mod i d
  rw [Finset.sum_eq_single a]
  · show (if d ∣ i + n then (1 : ℝ) else 0) =
      (if i % d = i % d then (1 : ℝ) else 0) *
        (if (n : ZMod d) = -((a.val : ℕ) : ZMod d) then (1 : ℝ) else 0)
    rw [if_pos rfl, one_mul, hcast]
    by_cases h : d ∣ i + n
    · rw [if_pos h, if_pos (heq.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (heq.mp h'))]
  · intro b _ hb
    have hne : i % d ≠ b.val := fun h => hb (Fin.ext h.symm)
    rw [if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The explicit residue expansion of the truncated Hankel matrix. -/
theorem truncatedTotient_factor (D i n : ℕ) :
    truncatedTotient D (i + n) =
      ∑ d ∈ Finset.Icc 1 D, ∑ a : Fin d,
        (((moebius d : ℤ) : ℝ) / d *
          (if i % d = a.val then 1 else 0)) *
          (if (n : ZMod d) = -(a.val : ZMod d) then 1 else 0) := by
  unfold truncatedTotient
  apply Finset.sum_congr rfl
  intro d hdmem
  have hd : 0 < d := by
    have h := (Finset.mem_Icc.mp hdmem).1
    omega
  calc
    (if d ∣ i + n then ((moebius d : ℤ) : ℝ) / d else 0) =
        ((moebius d : ℤ) : ℝ) / d *
          (if d ∣ i + n then (1 : ℝ) else 0) := by
            split_ifs <;> simp
    _ = ((moebius d : ℤ) : ℝ) / d *
          ∑ a : Fin d,
            (if i % d = a.val then (1 : ℝ) else 0) *
              (if (n : ZMod d) = -(a.val : ZMod d) then (1 : ℝ) else 0) := by
            rw [divisor_indicator_factor d i n hd]
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring

/-- An explicit finite separated representation, with one factor for every
residue class modulo every `d ≤ D`. -/
theorem truncatedTotient_separated (D : ℕ) :
    ∃ r : ℕ, r = ∑ d ∈ Finset.Icc 1 D, d ∧
      ∃ f g : Fin r → ℕ → ℝ,
        ∀ i n, truncatedTotient D (i + n) =
          ∑ k : Fin r, f k i * g k n := by
  classical
  let I := Σ d : {d : ℕ // d ∈ Finset.Icc 1 D}, Fin d.val
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hcard : Fintype.card I = ∑ d ∈ Finset.Icc 1 D, d := by
    dsimp [I]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact Finset.sum_coe_sort (Finset.Icc 1 D) (fun d => d)
  refine ⟨Fintype.card I, hcard, ?_, ?_, ?_⟩
  · exact fun k i =>
      let x := e.symm k
      (((moebius x.1.val : ℤ) : ℝ) / x.1.val) *
        (if i % x.1.val = x.2.val then 1 else 0)
  · exact fun k n =>
      let x := e.symm k
      if (n : ZMod x.1.val) = -(x.2.val : ZMod x.1.val) then 1 else 0
  · intro i n
    rw [truncatedTotient_factor]
    change (∑ d ∈ Finset.Icc 1 D, ∑ a : Fin d,
      (((moebius d : ℤ) : ℝ) / d *
        (if i % d = a.val then 1 else 0)) *
        (if (n : ZMod d) = -(a.val : ZMod d) then 1 else 0)) =
      ∑ k : Fin (Fintype.card I),
        (((moebius (e.symm k).1.val : ℤ) : ℝ) / (e.symm k).1.val *
          (if i % (e.symm k).1.val = (e.symm k).2.val then 1 else 0)) *
          (if (n : ZMod (e.symm k).1.val) = -((e.symm k).2.val : ZMod (e.symm k).1.val)
            then 1 else 0)
    let F : I → ℝ := fun x =>
      (((moebius x.1.val : ℤ) : ℝ) / x.1.val *
        (if i % x.1.val = x.2.val then 1 else 0)) *
        (if (n : ZMod x.1.val) = -(x.2.val : ZMod x.1.val) then 1 else 0)
    change _ = ∑ k : Fin (Fintype.card I), F (e.symm k)
    rw [Equiv.sum_comp e.symm F, Fintype.sum_sigma]
    exact (Finset.sum_coe_sort (Finset.Icc 1 D) (fun m => ∑ a : Fin m,
      (((moebius m : ℤ) : ℝ) / m * (if i % m = a.val then 1 else 0)) *
        (if (n : ZMod m) = -(a.val : ZMod m) then 1 else 0))).symm

/-- The Möbius truncations are finite-rank matrices in the #269 interface. -/
theorem truncatedTotient_finite_rank (D : ℕ) :
    ErdosProblems.Erdos269.PaperR8.FiniteSeparatedRank
      (fun i n => truncatedTotient D (i + n)) := by
  obtain ⟨r, _, f, g, h⟩ := truncatedTotient_separated D
  exact ⟨r, f, g, h⟩

/-- The number of displayed residue factors is the triangular number. -/
theorem truncatedTotient_factor_count (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, d) = D * (D + 1) / 2 := by
  have h2 : ∀ D : ℕ, (∑ d ∈ Finset.Icc 1 D, d) * 2 = D * (D + 1) := by
    intro D
    induction D with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), add_mul, ih]
      ring
  exact (Nat.div_eq_of_eq_mul_left (by norm_num) (h2 D).symm).symm

/-- A concrete separated-rank budget for every Möbius truncation. -/
theorem truncatedTotient_triangular_rank (D : ℕ) :
    ∃ f g : Fin (D * (D + 1) / 2) → ℕ → ℝ,
      ∀ i n, truncatedTotient D (i + n) =
        ∑ k : Fin (D * (D + 1) / 2), f k i * g k n := by
  obtain ⟨r, hr, f, g, h⟩ := truncatedTotient_separated D
  rw [truncatedTotient_factor_count] at hr
  subst r
  exact ⟨f, g, h⟩

/-- Möbius inversion in the normalized form needed by the matrix estimate. -/
theorem normalizedTotient_eq_divisor_sum (m : ℕ) (hm : 0 < m) :
    normalizedTotient m =
      ∑ d ∈ m.divisors, ((moebius d : ℤ) : ℝ) / d := by
  have hμ := MersenneLambertLadder.sum_divisors_moebius_mul_div m hm
  have hμR := congrArg (fun z : ℤ => (z : ℝ)) hμ
  have hsum : (Nat.totient m : ℝ) =
      ∑ d ∈ m.divisors, ((moebius d : ℤ) : ℝ) * ((m / d : ℕ) : ℝ) := by
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] using hμR.symm
  rw [normalizedTotient, hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Nat.cast_div_charZero hdm]
  field_simp [hdR, hmR]

/-- The discarded Möbius divisors dominate the pointwise truncation error. -/
theorem abs_normalizedTotient_sub_truncated_le (D m : ℕ)
    (hD : 0 < D) (hm : 0 < m) :
    |normalizedTotient m - truncatedTotient D m| ≤
      ∑ d ∈ Finset.Ioc D m, if d ∣ m then (1 : ℝ) / d else 0 := by
  classical
  let S := Finset.Icc 1 (max D m)
  let T := Finset.Icc 1 D
  let f : ℕ → ℝ := fun d => if d ∣ m then ((moebius d : ℤ) : ℝ) / d else 0
  have hT : T ⊆ S := by
    intro d hd
    simp only [T, S, Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, hd.2.trans (le_max_left _ _)⟩
  have hdiff : S \ T = Finset.Ioc D m := by
    ext d
    simp only [S, T, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdiv : S.filter (fun d => d ∣ m) = m.divisors := by
    ext d
    simp only [S, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨h.2, hm.ne'⟩
    · intro h
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos h.1 hm
      exact ⟨⟨hdpos, (Nat.le_of_dvd hm h.1).trans (le_max_right _ _)⟩, h.1⟩
  have hfull : normalizedTotient m = ∑ d ∈ S, f d := by
    rw [normalizedTotient_eq_divisor_sum m hm]
    simp only [f, ← Finset.sum_filter, hdiv]
  have htrunc : truncatedTotient D m = ∑ d ∈ T, f d := rfl
  have htail : normalizedTotient m - truncatedTotient D m =
      ∑ d ∈ Finset.Ioc D m, f d := by
    rw [hfull, htrunc, ← Finset.sum_sdiff_eq_sub hT, hdiff]
  rw [htail]
  calc
    |∑ d ∈ Finset.Ioc D m, f d| ≤
        ∑ d ∈ Finset.Ioc D m, |f d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioc D m,
          if d ∣ m then (1 : ℝ) / d else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := lt_of_le_of_lt hD.le (Finset.mem_Ioc.mp hd).1
      by_cases hdm : d ∣ m
      · simp only [f, hdm, ↓reduceIte]
        have hμ : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]
          exact_mod_cast MersenneLambertLadder.abs_moebius_le_one d
        rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) d)]
        exact div_le_div_of_nonneg_right hμ (Nat.cast_nonneg d)
      · simp [f, hdm]

/-- Each antidiagonal in a leading `N × N` square has at most `N` cells. -/
private theorem square_translate_sum_le (N : ℕ) (hN : 0 < N)
    (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) :
    (∑ i ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, f (i + n)) ≤
      (N : ℝ) * ∑ m ∈ Finset.Icc 1 (2 * N), f m := by
  have hrow (i : ℕ) (hi : i ∈ Finset.Icc 1 N) :
      (∑ n ∈ Finset.Icc 1 N, f (i + n)) ≤
        ∑ m ∈ Finset.Icc 1 (2 * N), f m := by
    let s := Finset.Icc 1 N
    have hinj : ∀ a ∈ s, ∀ b ∈ s, i + a = i + b → a = b := by
      intro a _ b _ h
      omega
    have hsubset : s.image (fun n => i + n) ⊆ Finset.Icc 1 (2 * N) := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      have hi' := Finset.mem_Icc.mp hi
      have hn' := Finset.mem_Icc.mp hn
      simp only [Finset.mem_Icc]
      omega
    calc
      (∑ n ∈ s, f (i + n)) = ∑ m ∈ s.image (fun n => i + n), f m := by
        rw [Finset.sum_image hinj]
      _ ≤ ∑ m ∈ Finset.Icc 1 (2 * N), f m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun m _ _ => hf m)
  calc
    (∑ i ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, f (i + n)) ≤
        ∑ _i ∈ Finset.Icc 1 N,
          ∑ m ∈ Finset.Icc 1 (2 * N), f m :=
      Finset.sum_le_sum (fun i hi => hrow i hi)
    _ = (N : ℝ) * ∑ m ∈ Finset.Icc 1 (2 * N), f m := by
      have hcard : (Finset.Icc 1 N).card = N := by
        rw [Nat.card_Icc]
        omega
      simp [hcard]

private noncomputable def tailWeight (D m : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc D m, if d ∣ m then (1 : ℝ) / d else 0

/-- Divisibility counting and the square-summable tail give an `N`-independent
bound after averaging the antidiagonals. -/
private theorem tailWeight_prefix_sum_le (D N : ℕ) (hD : 0 < D) :
    (∑ m ∈ Finset.Icc 1 (2 * N), tailWeight D m) ≤
      (2 * N : ℝ) / D := by
  classical
  by_cases hDN : D ≤ 2 * N
  · have hsum :
        (∑ m ∈ Finset.Icc 1 (2 * N), tailWeight D m) ≤
          ∑ d ∈ Finset.Ioc D (2 * N),
            (((2 * N / d : ℕ) : ℝ) / d) := by
      calc
        (∑ m ∈ Finset.Icc 1 (2 * N), tailWeight D m) ≤
            ∑ m ∈ Finset.Icc 1 (2 * N),
              ∑ d ∈ Finset.Ioc D (2 * N),
                if d ∣ m then (1 : ℝ) / d else 0 := by
          apply Finset.sum_le_sum
          intro m hm
          unfold tailWeight
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            have hm' := (Finset.mem_Icc.mp hm).2
            simp only [Finset.mem_Ioc] at hd ⊢
            exact ⟨hd.1, hd.2.trans hm'⟩
          · intro d _ _
            split_ifs <;> positivity
        _ = ∑ d ∈ Finset.Ioc D (2 * N),
              (((2 * N / d : ℕ) : ℝ) / d) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d _
          have hI : Finset.Icc 1 (2 * N) = Finset.Ioc 0 (2 * N) := by
            ext x
            simp only [Finset.mem_Icc, Finset.mem_Ioc]
            omega
          rw [hI, ← Finset.sum_filter, Finset.sum_const,
            Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_one_div]
    have hsq :
        (∑ d ∈ Finset.Ioc D (2 * N),
            (((2 * N / d : ℕ) : ℝ) / d)) ≤
          (2 * N : ℝ) *
            ∑ d ∈ Finset.Ioc D (2 * N), ((d : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < (d : ℝ) := by
        exact_mod_cast (lt_of_le_of_lt hD.le (Finset.mem_Ioc.mp hd).1)
      calc
        (((2 * N / d : ℕ) : ℝ) / d) ≤ ((2 * N : ℝ) / d) / d :=
          by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
            (div_le_div_of_nonneg_right
              (Nat.cast_div_le (m := 2 * N) (n := d) (α := ℝ)) hdpos.le)
        _ = (2 * N : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
          field_simp [ne_of_gt hdpos]
    have hp := sum_Ioc_inv_sq_le_sub (α := ℝ) hD.ne' hDN
    have htail :
        (∑ d ∈ Finset.Ioc D (2 * N), ((d : ℝ) ^ 2)⁻¹) ≤
          (D : ℝ)⁻¹ :=
      hp.trans (sub_le_self _ (inv_nonneg.mpr (by positivity)))
    calc
      (∑ m ∈ Finset.Icc 1 (2 * N), tailWeight D m) ≤
          (2 * N : ℝ) *
            ∑ d ∈ Finset.Ioc D (2 * N), ((d : ℝ) ^ 2)⁻¹ :=
        hsum.trans hsq
      _ ≤ (2 * N : ℝ) * (D : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (2 * N : ℝ) / D := by ring
  · have hempty (m : ℕ) (hm : m ∈ Finset.Icc 1 (2 * N)) :
        tailWeight D m = 0 := by
      unfold tailWeight
      have : Finset.Ioc D m = ∅ := by
        apply Finset.Ioc_eq_empty_of_le
        have hm' := (Finset.mem_Icc.mp hm).2
        omega
      simp [this]
    have hzero : (∑ m ∈ Finset.Icc 1 (2 * N), tailWeight D m) = 0 :=
      Finset.sum_eq_zero hempty
    rw [hzero]
    positivity

/-- Every leading square has mean absolute error at most `2/D`, regardless of
its size `N`.  The approximation has the separated representation above. -/
theorem normalizedTotient_mean_error_le (D N : ℕ) (hD : 0 < D) (hN : 0 < N) :
    (∑ i ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      |normalizedTotient (i + n) - truncatedTotient D (i + n)|) /
        ((N : ℝ) ^ 2) ≤ 2 / (D : ℝ) := by
  have hpoint (m : ℕ) (hm : 0 < m) :
      |normalizedTotient m - truncatedTotient D m| ≤ tailWeight D m :=
    abs_normalizedTotient_sub_truncated_le D m hD hm
  have htail_nonneg (m : ℕ) : 0 ≤ tailWeight D m := by
    unfold tailWeight
    apply Finset.sum_nonneg
    intro d _
    split_ifs <;> positivity
  have hsquare :
      (∑ i ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        |normalizedTotient (i + n) - truncatedTotient D (i + n)|) ≤
        (N : ℝ) * ((2 * N : ℝ) / D) := by
    calc
      (∑ i ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        |normalizedTotient (i + n) - truncatedTotient D (i + n)|) ≤
          ∑ i ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            tailWeight D (i + n) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro n hn
        have hi' := (Finset.mem_Icc.mp hi).1
        exact hpoint (i + n) (by omega)
      _ ≤ (N : ℝ) *
            ∑ m ∈ Finset.Icc 1 (2 * N), tailWeight D m :=
        square_translate_sum_le N hN (tailWeight D) htail_nonneg
      _ ≤ (N : ℝ) * ((2 * N : ℝ) / D) :=
        mul_le_mul_of_nonneg_left (tailWeight_prefix_sum_le D N hD) (by positivity)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  calc
    (∑ i ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        |normalizedTotient (i + n) - truncatedTotient D (i + n)|) /
          ((N : ℝ) ^ 2) ≤
        ((N : ℝ) * ((2 * N : ℝ) / D)) / ((N : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hsquare (sq_nonneg (N : ℝ))
    _ = 2 / (D : ℝ) := by
      field_simp [ne_of_gt hNreal, ne_of_gt hDreal]

end ErdosProblems.Erdos249.TotientMeanApproximation
