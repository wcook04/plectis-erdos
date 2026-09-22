import ErdosProblems.Erdos1049.PaperCompleteR21.SimultaneousMahlerSystem
import ErdosProblems.Erdos1049.PaperR16.MahlerBoundary

/-!
# Erdős #1049: no finite simultaneous `2`/`3`-system, with no hypothesis

Lean form of `long1049:res:nomahler`
(`paper/reasoning-parts/erdos1049/core.tex`, line 3573):

> Let `ℒ(z) = ∑_{n ≥ 1} zⁿ/(1 - zⁿ)`.  There is no finite-dimensional
> `ℚ(z)`-vector space that contains `ℒ` and is stable under both `z ↦ z²` and
> `z ↦ z³`.

`no_finite_simultaneous_two_three_system` in `SimultaneousMahlerSystem.lean`
states this proposition and proves it from the cited theorem of Adamczewski and
Bell, taken there as the hypothesis `AdamczewskiBell`.  The theorem
`no_finite_simultaneous_two_three_system_unconditional` below has the same
statement with that hypothesis removed.  It is the case `k = 2` of
`no_finite_single_base_system`: for every `k ≥ 2`, no finite-dimensional
`ℚ(z)`-subspace containing `ℒ` is stable under `z ↦ z^k` alone.

## Proof

`mahler_of_stable` turns a finite-dimensional subspace stable under `z ↦ z^k`
into a `k`-Mahler equation `∑_{i ≤ d} pᵢ(z) ℒ(z^{k^{i+j}}) = 0` in the field
`ℚ((z))` of formal Laurent series, with `p₀ ≠ 0`.
`PaperR16.no_polynomial_mahler_relation` says that `ℒ` satisfies no nontrivial
polynomial `k`-Mahler equation as a function on the open complex unit disc; it
is proved from the boundary behaviour of `ℒ` at roots of unity, with no
hypothesis beyond `k ≥ 2`.  The two statements live in different worlds, and
this file supplies the bridge between them:

* `subs_divisorLambert_eq_ofPowerSeries`: `ℒ(z^M)` is the power series whose
  coefficient at `n` is `τ(n/M)` when `M ∣ n` and `0` otherwise;
* `tsum_divisors_eq_lambert`: for `|w| < 1`, `∑ τ(n) wⁿ` is the Lambert sum
  `∑_{n ≥ 1} wⁿ/(1 - wⁿ)`, by Mathlib's `tsum_pow_div_one_sub_eq_tsum_sigma`;
* `relation_eval_eq_zero`: a polynomial relation among power series whose
  evaluations at `z` converge absolutely holds between their values at `z`;
* `laurent_relation_eval`: a polynomial relation in `ℚ((z))` among the
  substitutes `ℒ(z^{M_i})` holds pointwise on the open unit disc.

Shifting the coefficients by `j` then gives the forbidden equation.  Stability
under `z ↦ z³` is not used.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21

open scoped LaurentSeries PowerSeries Polynomial RatFunc

noncomputable section NoMahlerUnconditional

namespace FormalLambertEvaluation

/-! ## `ℒ(z^M)` as a formal power series -/

/-- The coefficients of `ℒ(z^M)`: `τ(n/M)` when `M ∣ n`, and `0` otherwise. -/
def orbitCoeff (M n : ℕ) : ℚ :=
  if M ∣ n then ((n / M).divisors.card : ℚ) else 0

/-- `ℒ(z^M)` as a formal power series over `ℚ`. -/
def orbitSeries (M : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk (orbitCoeff M)

/-- The substitution `z ↦ z^M` sends `ℒ` to the power series `orbitSeries M`. -/
theorem subs_divisorLambert_eq_ofPowerSeries {M : ℕ} (hM : 1 ≤ M) :
    subs M divisorLambert = HahnSeries.ofPowerSeries ℤ ℚ (orbitSeries M) := by
  have hMZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have hL : ∀ m : ℤ,
      divisorLambert.coeff m = if m < 0 then 0 else (m.natAbs.divisors.card : ℚ) := by
    intro m
    rw [divisorLambert, PowerSeries.coeff_coe, PowerSeries.coeff_mk]
  ext n
  rw [subs_coeff hM, PowerSeries.coeff_coe, orbitSeries, PowerSeries.coeff_mk]
  by_cases hn : n < 0
  · rw [if_pos hn]
    by_cases hd : (M : ℤ) ∣ n
    · rw [if_pos hd, hL, if_pos (Int.ediv_neg_of_neg_of_pos hn hMZ)]
    · rw [if_neg hd]
  · rw [if_neg hn]
    lift n to ℕ using (not_lt.mp hn) with m
    rw [Int.natAbs_natCast, orbitCoeff]
    by_cases hd : M ∣ m
    · obtain ⟨t, rfl⟩ := hd
      have hZ : (M : ℤ) ∣ ((M * t : ℕ) : ℤ) := ⟨(t : ℤ), by push_cast; ring⟩
      have hq : ((M * t : ℕ) : ℤ) / (M : ℤ) = (t : ℤ) := by
        push_cast
        exact Int.mul_ediv_cancel_left _ hMZ.ne'
      rw [if_pos hZ, if_pos ⟨t, rfl⟩, hq, hL, if_neg (not_lt.mpr (Int.natCast_nonneg t)),
        Int.natAbs_natCast, Nat.mul_div_cancel_left t (by omega)]
    · have hZ : ¬ (M : ℤ) ∣ (m : ℤ) := fun hc => hd (by exact_mod_cast hc)
      rw [if_neg hZ, if_neg hd]

/-! ## Evaluating a convergent power series at a complex point -/

/-- The `n`th term of the rational power series `f` evaluated at `z ∈ ℂ`. -/
def evalTerm (f : ℚ⟦X⟧) (z : ℂ) (n : ℕ) : ℂ :=
  ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n

lemma evalTerm_poly_eq_zero (p : ℚ[X]) (z : ℂ) {n : ℕ} (hn : p.natDegree < n) :
    evalTerm (p : ℚ⟦X⟧) z n = 0 := by
  rw [evalTerm, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hn,
    Rat.cast_zero, zero_mul]

lemma evalTerm_poly_norm_summable (p : ℚ[X]) (z : ℂ) :
    Summable fun n => ‖evalTerm (p : ℚ⟦X⟧) z n‖ := by
  refine summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  rw [evalTerm_poly_eq_zero p z (by omega), norm_zero]

/-- The evaluation of a polynomial, read as a power series, is its value. -/
lemma tsum_evalTerm_poly (p : ℚ[X]) (z : ℂ) :
    ∑' n, evalTerm (p : ℚ⟦X⟧) z n = (p.map (algebraMap ℚ ℂ)).eval z := by
  rw [tsum_eq_sum (s := Finset.range (p.natDegree + 1)) fun n hn => ?_,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [evalTerm, Polynomial.coeff_coe, Polynomial.coeff_map, eq_ratCast]
  · rw [Finset.mem_range, not_lt] at hn
    exact evalTerm_poly_eq_zero p z (by omega)

lemma evalTerm_mul_poly (p : ℚ[X]) (f : ℚ⟦X⟧) (z : ℂ) (n : ℕ) :
    evalTerm ((p : ℚ⟦X⟧) * f) z n
      = ∑ kl ∈ Finset.antidiagonal n, evalTerm (p : ℚ⟦X⟧) z kl.1 * evalTerm f z kl.2 := by
  simp only [evalTerm, PowerSeries.coeff_mul, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

/-- Multiplying an absolutely convergent evaluation by a polynomial keeps it
convergent and multiplies its value by the value of the polynomial. -/
lemma evalTerm_mul_poly_summable_tsum (p : ℚ[X]) (f : ℚ⟦X⟧) (z : ℂ)
    (hf : Summable fun n => ‖evalTerm f z n‖) :
    (Summable fun n => evalTerm ((p : ℚ⟦X⟧) * f) z n) ∧
      ∑' n, evalTerm ((p : ℚ⟦X⟧) * f) z n
        = (p.map (algebraMap ℚ ℂ)).eval z * ∑' n, evalTerm f z n := by
  have hp := evalTerm_poly_norm_summable p z
  refine ⟨Summable.of_norm ?_, ?_⟩
  · simpa only [evalTerm_mul_poly] using
      summable_norm_sum_mul_antidiagonal_of_summable_norm hp hf
  · rw [← tsum_evalTerm_poly p z,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hp hf]
    exact tsum_congr fun n => evalTerm_mul_poly p f z n

/-- A polynomial relation among rational power series whose evaluations at `z`
converge absolutely holds between the values at `z`. -/
theorem relation_eval_eq_zero {ι : Type*} (s : Finset ι) (p : ι → ℚ[X]) (f : ι → ℚ⟦X⟧)
    (z : ℂ) (hf : ∀ i ∈ s, Summable fun n => ‖evalTerm (f i) z n‖)
    (hrel : ∑ i ∈ s, (p i : ℚ⟦X⟧) * f i = 0) :
    ∑ i ∈ s, ((p i).map (algebraMap ℚ ℂ)).eval z * ∑' n, evalTerm (f i) z n = 0 := by
  have hcoeff : ∀ n, ∑ i ∈ s, evalTerm ((p i : ℚ⟦X⟧) * f i) z n = 0 := by
    intro n
    have h := congrArg (fun φ : ℚ⟦X⟧ => PowerSeries.coeff n φ) hrel
    simp only [map_sum, map_zero] at h
    simp only [evalTerm, ← Finset.sum_mul, ← Rat.cast_sum, h, Rat.cast_zero, zero_mul]
  calc ∑ i ∈ s, ((p i).map (algebraMap ℚ ℂ)).eval z * ∑' n, evalTerm (f i) z n
      = ∑ i ∈ s, ∑' n, evalTerm ((p i : ℚ⟦X⟧) * f i) z n :=
        Finset.sum_congr rfl fun i hi =>
          (evalTerm_mul_poly_summable_tsum (p i) (f i) z (hf i hi)).2.symm
    _ = ∑' n, ∑ i ∈ s, evalTerm ((p i : ℚ⟦X⟧) * f i) z n :=
        (Summable.tsum_finsetSum fun i hi =>
          (evalTerm_mul_poly_summable_tsum (p i) (f i) z (hf i hi)).1).symm
    _ = 0 := by simp only [hcoeff, tsum_zero]

/-! ## The divisor series is the Lambert series -/

lemma divisors_norm_summable (w : ℂ) (hw : ‖w‖ < 1) :
    Summable fun n : ℕ => ‖(n.divisors.card : ℂ) * w ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hw)
  simp only [norm_mul, norm_pow, Complex.norm_natCast, pow_one]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n)
    (pow_nonneg (norm_nonneg w) n)

/-- For `|w| < 1` the divisor series `∑ τ(n) wⁿ` equals the Lambert series
`∑_{n ≥ 1} wⁿ/(1 - wⁿ)`, in the form `PaperR16.lambert` that the boundary
theorem uses. -/
theorem tsum_divisors_eq_lambert (w : ℂ) (hw : ‖w‖ < 1) :
    ∑' n : ℕ, (n.divisors.card : ℂ) * w ^ n = PaperR16.lambert w := by
  have hsum : Summable fun n : ℕ => (n.divisors.card : ℂ) * w ^ n :=
    (divisors_norm_summable w hw).of_norm
  have hid : ∑' n : ℕ+, w ^ (n : ℕ) / (1 - w ^ (n : ℕ))
      = ∑' n : ℕ+, ((n : ℕ).divisors.card : ℂ) * w ^ (n : ℕ) := by
    simpa only [pow_zero, one_mul, ArithmeticFunction.sigma_zero_apply]
      using tsum_pow_div_one_sub_eq_tsum_sigma hw 0
  calc ∑' n : ℕ, (n.divisors.card : ℂ) * w ^ n
      = ∑' n : ℕ+, ((n : ℕ).divisors.card : ℂ) * w ^ (n : ℕ) := by
        rw [← tsum_zero_pnat_eq_tsum_nat hsum]
        simp
    _ = ∑' n : ℕ+, w ^ (n : ℕ) / (1 - w ^ (n : ℕ)) := hid.symm
    _ = ∑' n : ℕ, w ^ (n + 1) / (1 - w ^ (n + 1)) :=
        tsum_pnat_eq_tsum_succ (f := fun n : ℕ => w ^ n / (1 - w ^ n))
    _ = PaperR16.lambert w := (PaperR16.lambert_eq_tsum_positive w hw).symm

/-! ## `ℒ(z^M)` evaluates to the Lambert series at `z^M` -/

lemma evalTerm_orbit_mul {M : ℕ} (hM : 1 ≤ M) (z : ℂ) (m : ℕ) :
    evalTerm (orbitSeries M) z (M * m) = (m.divisors.card : ℂ) * (z ^ M) ^ m := by
  rw [evalTerm, orbitSeries, PowerSeries.coeff_mk, orbitCoeff, if_pos (dvd_mul_right M m),
    Nat.mul_div_cancel_left m (by omega), Rat.cast_natCast, pow_mul]

lemma evalTerm_orbit_off {M : ℕ} (z : ℂ) {n : ℕ}
    (hn : n ∉ Set.range (fun m : ℕ => M * m)) : evalTerm (orbitSeries M) z n = 0 := by
  have hd : ¬ M ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
  rw [evalTerm, orbitSeries, PowerSeries.coeff_mk, orbitCoeff, if_neg hd, Rat.cast_zero,
    zero_mul]

/-- For `|z| < 1` the evaluation of `ℒ(z^M)` at `z` converges absolutely, to the
Lambert series at `z^M`. -/
theorem orbitSeries_eval {M : ℕ} (hM : 1 ≤ M) (z : ℂ) (hz : ‖z‖ < 1) :
    (Summable fun n => ‖evalTerm (orbitSeries M) z n‖) ∧
      ∑' n, evalTerm (orbitSeries M) z n = PaperR16.lambert (z ^ M) := by
  have hzM : ‖z ^ M‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hz (by omega)
  have hinj : Function.Injective (fun m : ℕ => M * m) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (by omega) h
  refine ⟨?_, ?_⟩
  · refine (hinj.summable_iff (f := fun n => ‖evalTerm (orbitSeries M) z n‖)
      fun n hn => (congrArg norm (evalTerm_orbit_off z hn)).trans norm_zero).mp ?_
    simpa only [Function.comp_def, evalTerm_orbit_mul hM z] using divisors_norm_summable _ hzM
  · have hs : HasSum (fun n => evalTerm (orbitSeries M) z n)
        (∑' m : ℕ, (m.divisors.card : ℂ) * (z ^ M) ^ m) := by
      refine (hinj.hasSum_iff fun n hn => evalTerm_orbit_off z hn).mp ?_
      simpa only [Function.comp_def, evalTerm_orbit_mul hM z] using
        (divisors_norm_summable _ hzM).of_norm.hasSum
    rw [hs.tsum_eq, tsum_divisors_eq_lambert _ hzM]

/-! ## From a relation in `ℚ((z))` to a relation on the unit disc -/

/-- A polynomial relation in `ℚ((z))` among substitutes `ℒ(z^{M_i})`, `M_i ≥ 1`,
holds between their complex values throughout the open unit disc. -/
theorem laurent_relation_eval {ι : Type*} (s : Finset ι) (q : ι → ℚ[X]) (M : ι → ℕ)
    (hM : ∀ i ∈ s, 1 ≤ M i)
    (h : ∑ i ∈ s, algebraMap ℚ[X] ℚ⸨X⸩ (q i) * subs (M i) divisorLambert = 0)
    (z : ℂ) (hz : ‖z‖ < 1) :
    ∑ i ∈ s, ((q i).map (algebraMap ℚ ℂ)).eval z * PaperR16.lambert (z ^ M i) = 0 := by
  have hps : ∑ i ∈ s, (q i : ℚ⟦X⟧) * orbitSeries (M i) = 0 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
    rw [map_sum, map_zero]
    refine Eq.trans (Finset.sum_congr rfl fun i hi => ?_) h
    rw [map_mul, subs_divisorLambert_eq_ofPowerSeries (hM i hi)]
    rfl
  refine Eq.trans (Finset.sum_congr rfl fun i hi => ?_)
    (relation_eval_eq_zero s q (fun i => orbitSeries (M i)) z
      (fun i hi => (orbitSeries_eval (hM i hi) z hz).1) hps)
  rw [(orbitSeries_eval (hM i hi) z hz).2]

/-- The coefficient family `p` shifted up by `j` places and read over `ℂ`. -/
def shiftCoeff (j : ℕ) (p : ℕ → ℚ[X]) (m : ℕ) : ℂ[X] :=
  if j ≤ m then (p (m - j)).map (algebraMap ℚ ℂ) else 0

end FormalLambertEvaluation

open FormalLambertEvaluation in
/-- For every `k ≥ 2`, no finite-dimensional `ℚ(z)`-subspace of `ℚ((z))` contains
the divisor generating series `ℒ(z) = ∑_{n ≥ 1} zⁿ/(1 - zⁿ)` and is stable under
`z ↦ z^k`.

`mahler_of_stable` gives a `k`-Mahler equation for some `ℒ(z^{k^j})` in
`ℚ((z))`, `laurent_relation_eval` turns it into a nontrivial polynomial
`k`-Mahler equation for `ℒ` on the open unit disc, and
`PaperR16.no_polynomial_mahler_relation` rules that out. -/
theorem no_finite_single_base_system {k : ℕ} (hk : 2 ≤ k) :
    ¬ ∃ V : Submodule (RatFunc ℚ) ℚ⸨X⸩,
        Module.Finite (RatFunc ℚ) V ∧ divisorLambert ∈ V ∧ (∀ f ∈ V, subs k f ∈ V) := by
  rintro ⟨V, hVfin, hL, hstab⟩
  haveI := hVfin
  obtain ⟨j, d, p, hp0, hsum⟩ := mahler_of_stable (k := k) (by omega) V hL hstab
  have hpow : ∀ i : ℕ, 1 ≤ k ^ i := fun i => Nat.one_le_pow _ _ (by omega)
  have hrel : ∑ i ∈ Finset.range (d + 1),
      algebraMap ℚ[X] ℚ⸨X⸩ (p i) * subs (k ^ i * k ^ j) divisorLambert = 0 := by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
    rw [subs_comp (hpow i) (hpow j)]
  apply PaperR16.no_polynomial_mahler_relation k hk
  refine ⟨j + d, shiftCoeff j p, ⟨j, Nat.le_add_right j d, ?_⟩, ?_⟩
  · rw [shiftCoeff, if_pos le_rfl, Nat.sub_self]
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hp0
  · intro z hz
    have hev := laurent_relation_eval (Finset.range (d + 1)) p (fun i => k ^ i * k ^ j)
      (fun i _ => (hpow (i + j)).trans_eq (pow_add k i j)) hrel z hz
    have hlow : ∑ m ∈ Finset.range j,
        (shiftCoeff j p m).eval z * PaperR16.lambert (z ^ k ^ m) = 0 :=
      Finset.sum_eq_zero fun m hm => by
        rw [shiftCoeff, if_neg (not_le.mpr (Finset.mem_range.mp hm)), Polynomial.eval_zero,
          zero_mul]
    rw [show j + d + 1 = j + (d + 1) by omega, Finset.sum_range_add, hlow, zero_add]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hev
    rw [shiftCoeff, if_pos (Nat.le_add_right j i), Nat.add_sub_cancel_left, pow_add,
      mul_comm (k ^ j)]

/-- `long1049:res:nomahler`, with no hypothesis.  There is no finite-dimensional
`ℚ(z)`-subspace of `ℚ((z))` containing the divisor generating series
`ℒ(z) = ∑_{n ≥ 1} zⁿ/(1 - zⁿ)` and stable under both `z ↦ z²` and `z ↦ z³`.

The statement is that of `no_finite_simultaneous_two_three_system` without its
`AdamczewskiBell` hypothesis.  Stability under `z ↦ z²` alone already fails, by
`no_finite_single_base_system` with `k = 2`. -/
theorem no_finite_simultaneous_two_three_system_unconditional :
    ¬ ∃ V : Submodule (RatFunc ℚ) ℚ⸨X⸩,
        Module.Finite (RatFunc ℚ) V ∧
        divisorLambert ∈ V ∧
        (∀ f ∈ V, subs 2 f ∈ V) ∧ (∀ f ∈ V, subs 3 f ∈ V) := by
  rintro ⟨V, hVfin, hL, h2, -⟩
  exact no_finite_single_base_system (k := 2) le_rfl ⟨V, hVfin, hL, h2⟩

end NoMahlerUnconditional

end ErdosProblems.Erdos1049.PaperCompleteR21
