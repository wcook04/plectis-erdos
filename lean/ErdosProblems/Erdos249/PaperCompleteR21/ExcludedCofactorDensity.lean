import Mathlib

/-! The density side of the long #249 paper's `prop:badcof` ("The
excluded-cofactor estimate", `paper/reasoning-parts/erdos249/a249_front.tex`),
and the elementary remark after its proof.  Nothing here uses the prime number
theorem; the estimate itself is `prop_badcof` in `ExcludedCofactorEstimate`.

* `excludedCofactorSet η` is the paper's `B(η) = {m ≥ 1 : φ(m) < η m}`.
* `HasNaturalDensity A D` is "`A` has natural density `D`":
  `#(A ∩ [1, x]) / x → D`.  `UpperDensityLE A D` is the one-sided form
  "`#(A ∩ [1, x]) ≤ (D + ε) x` for all large `x`, for every `ε > 0`", which is
  all the estimate uses.
* `upper_density_harmonic_bound` is the partial summation step of the proof:
  `∑_{m ≤ M, m ∈ A} 1/m ≤ (D + ε) log (M + 1) + C_ε`.  The paper states the
  asymptotic `(D/2 + o(1)) log X` at `M = √X/2`; only this upper half is used.
* `card_excludedCofactorSet_lt` is the paper's unconditional remark
  `#(B(η) ∩ [1, x]) < 3ηx` for `η > 0`, `x ≥ 1`, proved as written: the mean of
  `n/φ(n)` over `[1, x]` is at most `∏_p (1 + 1/(p(p - 1))) ≤ e < 3`
  (`sum_div_totient_le`), then Markov's inequality.  Hence `D(η) ≤ 3η` whenever
  the density exists (`density_le_three_mul`), and `B(η)` always has upper
  density at most `3η` (`excludedCofactorSet_upperDensityLE`).

The expansion used for the mean is `n/φ(n) = ∏_{p ∣ n} (1 + 1/(p - 1))`
multiplied out over the subsets of the prime factors, which is the paper's
`∑_{d ∣ n} μ(d)²/φ(d)` indexed by the squarefree divisor `d = ∏ S`. -/

namespace ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor

open Finset Filter Topology

/-! ## The paper's `B(η)` and natural density -/

/-- The paper's excluded-cofactor set `B(η) = {m ≥ 1 : φ(m) < η m}`. -/
def excludedCofactorSet (η : ℝ) : Set ℕ := {m | 1 ≤ m ∧ (Nat.totient m : ℝ) < η * m}

@[simp] theorem mem_excludedCofactorSet {η : ℝ} {m : ℕ} :
    m ∈ excludedCofactorSet η ↔ 1 ≤ m ∧ (Nat.totient m : ℝ) < η * m := Iff.rfl

noncomputable instance (η : ℝ) : DecidablePred (· ∈ excludedCofactorSet η) := fun m =>
  inferInstanceAs (Decidable (1 ≤ m ∧ (Nat.totient m : ℝ) < η * m))

/-- `A ⊆ ℕ` has natural density `D`: `#(A ∩ [1, x]) / x → D` as `x → ∞`. -/
def HasNaturalDensity (A : Set ℕ) [DecidablePred (· ∈ A)] (D : ℝ) : Prop :=
  Tendsto (fun x : ℕ => ((((Icc 1 x).filter (· ∈ A)).card : ℕ) : ℝ) / x) atTop (𝓝 D)

/-- `A ⊆ ℕ` has upper density at most `D`: for every `ε > 0`,
`#(A ∩ [1, x]) ≤ (D + ε) x` for all large `x`. -/
def UpperDensityLE (A : Set ℕ) [DecidablePred (· ∈ A)] (D : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
    ((((Icc 1 x).filter (· ∈ A)).card : ℕ) : ℝ) ≤ (D + ε) * x

/-- `#(A ∩ [1, x]) ≤ x`. -/
theorem card_filter_Icc_le (A : Set ℕ) [DecidablePred (· ∈ A)] (x : ℕ) :
    ((((Icc 1 x).filter (· ∈ A)).card : ℕ) : ℝ) ≤ x := by
  have h1 : ((Icc 1 x).filter (· ∈ A)).card ≤ (Icc 1 x).card := Finset.card_filter_le _ _
  rw [Nat.card_Icc] at h1
  exact_mod_cast (show ((Icc 1 x).filter (· ∈ A)).card ≤ x by omega)

theorem HasNaturalDensity.nonneg {A : Set ℕ} [DecidablePred (· ∈ A)] {D : ℝ}
    (hD : HasNaturalDensity A D) : 0 ≤ D :=
  ge_of_tendsto hD (Eventually.of_forall fun x => by positivity)

theorem HasNaturalDensity.le_one {A : Set ℕ} [DecidablePred (· ∈ A)] {D : ℝ}
    (hD : HasNaturalDensity A D) : D ≤ 1 :=
  le_of_tendsto hD (Eventually.of_forall fun x =>
    div_le_one_of_le₀ (card_filter_Icc_le A x) (Nat.cast_nonneg x))

theorem HasNaturalDensity.upperDensityLE {A : Set ℕ} [DecidablePred (· ∈ A)] {D : ℝ}
    (hD : HasNaturalDensity A D) : UpperDensityLE A D := by
  intro ε hε
  filter_upwards [hD.eventually_lt_const (show D < D + ε by linarith), eventually_ge_atTop 1]
    with x hx hx1
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
  rw [div_lt_iff₀ hx0] at hx
  exact hx.le

/-! ## Partial summation -/

/-- Discrete partial summation over `[1, M]`. -/
theorem sum_Icc_div_eq (b : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ Icc 1 M, b m / m
      = (∑ i ∈ Icc 1 M, b i) / ((M : ℝ) + 1)
        + ∑ m ∈ Icc 1 M, (∑ i ∈ Icc 1 m, b i) / ((m : ℝ) * ((m : ℝ) + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have e1 : ∑ m ∈ Icc 1 (M + 1), b m / m
        = ∑ m ∈ Icc 1 M, b m / m + b (M + 1) / ((M + 1 : ℕ) : ℝ) :=
      Finset.sum_Icc_succ_top (by omega) _
    have e2 : ∑ i ∈ Icc 1 (M + 1), b i = ∑ i ∈ Icc 1 M, b i + b (M + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have e3 : ∑ m ∈ Icc 1 (M + 1), (∑ i ∈ Icc 1 m, b i) / ((m : ℝ) * ((m : ℝ) + 1))
        = ∑ m ∈ Icc 1 M, (∑ i ∈ Icc 1 m, b i) / ((m : ℝ) * ((m : ℝ) + 1))
          + (∑ i ∈ Icc 1 (M + 1), b i)
            / (((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) + 1)) :=
      Finset.sum_Icc_succ_top (by omega) _
    rw [e1, e3, e2, ih]
    have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
    have hM2 : (M : ℝ) + 1 + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- `∑_{m=1}^{M} 1/(m+1) ≤ log (M + 1)`. -/
theorem sum_Icc_inv_succ_le_log (M : ℕ) :
    ∑ m ∈ Icc 1 M, (1 : ℝ) / ((m : ℝ) + 1) ≤ Real.log ((M : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hM2 : (0 : ℝ) < (M : ℝ) + 1 + 1 := by positivity
    have hkey : 1 / ((M : ℝ) + 1 + 1) ≤ Real.log ((M : ℝ) + 1 + 1) - Real.log ((M : ℝ) + 1) := by
      rw [← Real.log_div hM2.ne' hM.ne']
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hM2 hM)
      have hform : 1 - (((M : ℝ) + 1 + 1) / ((M : ℝ) + 1))⁻¹ = 1 / ((M : ℝ) + 1 + 1) := by
        field_simp
        ring
      rw [hform] at h
      exact h
    push_cast
    linarith

/-- **Partial summation from a density bound.**  If `A` has upper density at
most `D ≥ 0`, then for every `ε > 0` there is `C ≥ 0` with
`∑_{m ≤ M, m ∈ A} 1/m ≤ (D + ε) log (M + 1) + C` for every `M`. -/
theorem upper_density_harmonic_bound (A : Set ℕ) [DecidablePred (· ∈ A)] {D : ℝ}
    (hD0 : 0 ≤ D) (hup : UpperDensityLE A D) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      ∑ m ∈ (Icc 1 M).filter (· ∈ A), (1 : ℝ) / m
        ≤ (D + ε) * Real.log ((M : ℝ) + 1) + C := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hup ε hε)
  refine ⟨1 + n₀, by positivity, fun M => ?_⟩
  -- indicator form
  set b : ℕ → ℝ := fun m => if m ∈ A then 1 else 0 with hb
  have hsumb : ∀ x : ℕ, ∑ i ∈ Icc 1 x, b i = (((Icc 1 x).filter (· ∈ A)).card : ℝ) := by
    intro x
    simp only [hb]
    rw [Finset.sum_boole]
  have hlhs : ∑ m ∈ (Icc 1 M).filter (· ∈ A), (1 : ℝ) / m = ∑ m ∈ Icc 1 M, b m / m := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    simp only [hb]
    split_ifs <;> simp
  rw [hlhs, sum_Icc_div_eq]
  simp only [hsumb]
  -- the boundary term is at most `1`
  have hbd : (((Icc 1 M).filter (· ∈ A)).card : ℝ) / ((M : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [card_filter_Icc_le A M]
  -- pointwise bound on the partial-summation terms
  have hpt : ∀ m ∈ Icc 1 M,
      (((Icc 1 m).filter (· ∈ A)).card : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))
        ≤ (D + ε) * (1 / ((m : ℝ) + 1)) + (if m < n₀ then 1 else 0) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hpos : 0 < (m : ℝ) * ((m : ℝ) + 1) := by positivity
    have hDe : 0 ≤ (D + ε) * (1 / ((m : ℝ) + 1)) := by
      apply mul_nonneg (by linarith) (by positivity)
    split_ifs with hlt
    · -- `C(m) / (m (m + 1)) ≤ 1`
      rw [div_le_iff₀ hpos]
      have := card_filter_Icc_le A m
      nlinarith
    · -- `C(m) ≤ (D + ε) m`
      have hge : n₀ ≤ m := by omega
      have hle := hn₀ m hge
      rw [div_le_iff₀ hpos, add_zero]
      have hform : (D + ε) * (1 / ((m : ℝ) + 1)) * ((m : ℝ) * ((m : ℝ) + 1))
          = (D + ε) * m := by
        field_simp
      rw [hform]
      exact hle
  have hsum_pt := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_pt
  have hharm := sum_Icc_inv_succ_le_log M
  have hind : ∑ m ∈ Icc 1 M, (if m < n₀ then (1 : ℝ) else 0) ≤ n₀ := by
    rw [Finset.sum_boole]
    have hsub : (Icc 1 M).filter (· < n₀) ⊆ range n₀ := by
      intro m hm
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hDe : 0 ≤ D + ε := by linarith
  have := mul_le_mul_of_nonneg_left hharm hDe
  linarith

/-! ## The elementary bound `#(B(η) ∩ [1, x]) < 3ηx` -/

/-- `n / φ(n) = ∏_{p ∣ n} (1 + 1/(p - 1))`. -/
theorem div_totient_eq_prod {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) / Nat.totient n = ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
  have h := Nat.totient_mul_prod_primeFactors n
  have hφ : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have hR : (Nat.totient n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ)
      = (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have hc := congrArg (fun k : ℕ => (k : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at hc
    rw [hc]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hpos : ∀ p ∈ n.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hprod_pos : (0 : ℝ) < ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hpos
  have hform : ∀ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have := (hpos p hp).ne'
    field_simp
    ring
  rw [Finset.prod_congr rfl hform, Finset.prod_div_distrib,
    div_eq_div_iff hφ.ne' hprod_pos.ne']
  linarith [hR]

/-- `∑_{2 ≤ n ≤ x+1} 1/((n - 1) n) = 1 - 1/(x + 1)`. -/
theorem sum_Icc_two_inv_mul_pred (x : ℕ) :
    ∑ n ∈ Icc 2 (x + 1), (1 : ℝ) / (((n : ℝ) - 1) * n) = 1 - 1 / ((x : ℝ) + 1) := by
  induction x with
  | zero => norm_num
  | succ x ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have h1 : (x : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (x : ℝ) + 1 + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- `∏_{p ≤ x} (1 + 1/(p(p - 1))) ≤ e`, via `1 + u ≤ exp u` and the telescoping
bound `∑_{2 ≤ n ≤ x} 1/(n(n - 1)) ≤ 1`. -/
theorem prod_primes_one_add_le_exp_one (x : ℕ) :
    ∏ p ∈ (Icc 1 x).filter Nat.Prime, (1 + 1 / (((p : ℝ) - 1) * p)) ≤ Real.exp 1 := by
  have hnn : ∀ p ∈ (Icc 1 x).filter Nat.Prime, (0 : ℝ) ≤ 1 / (((p : ℝ) - 1) * p) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    apply div_nonneg zero_le_one
    apply mul_nonneg <;> linarith
  have hexp : ∏ p ∈ (Icc 1 x).filter Nat.Prime, (1 + 1 / (((p : ℝ) - 1) * p))
      ≤ Real.exp (∑ p ∈ (Icc 1 x).filter Nat.Prime, 1 / (((p : ℝ) - 1) * p)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      linarith [hnn p hp]
    · intro p _
      linarith [Real.add_one_le_exp (1 / (((p : ℝ) - 1) * p))]
  have hsum : ∑ p ∈ (Icc 1 x).filter Nat.Prime, 1 / (((p : ℝ) - 1) * p) ≤ 1 := by
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      simp
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    have hsub : (Icc 1 (y + 1)).filter Nat.Prime ⊆ Icc 2 (y + 1) := by
      intro p hp
      obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨hpp.two_le, (Finset.mem_Icc.mp hpI).2⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun n : ℕ => (1 : ℝ) / (((n : ℝ) - 1) * n)) hsub (fun n hn _ => by
        have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        apply div_nonneg zero_le_one
        apply mul_nonneg <;> linarith)
    rw [sum_Icc_two_inv_mul_pred] at hle
    have : 0 ≤ 1 / ((y : ℝ) + 1) := by positivity
    linarith
  calc _ ≤ _ := hexp
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum

/-- On `[1, x]`, the number of multiples of `d` is at most `x / d`. -/
theorem card_filter_dvd_le (d x : ℕ) :
    (((Icc 1 x).filter (fun n => d ∣ n)).card : ℝ) ≤ (x : ℝ) / d := by
  have hIcc : Icc 1 x = Ioc 0 x := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le

/-- **The mean of `n/φ(n)`.**  `∑_{n ≤ x} n/φ(n) ≤ e x`. -/
theorem sum_div_totient_le (x : ℕ) :
    ∑ n ∈ Icc 1 x, (n : ℝ) / Nat.totient n ≤ Real.exp 1 * x := by
  classical
  set P := (Icc 1 x).filter Nat.Prime with hPdef
  set f : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1) with hfdef
  -- expand each term over the subsets of the primes up to `x`
  have hexpand : ∀ n ∈ Icc 1 x, (n : ℝ) / Nat.totient n
      = ∑ S ∈ P.powerset, if S ⊆ n.primeFactors then ∏ p ∈ S, f p else 0 := by
    intro n hn
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    rw [div_totient_eq_prod (by omega), Finset.prod_one_add, ← Finset.sum_filter]
    have hsubP : n.primeFactors ⊆ P := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpn : p ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.one_le, by omega⟩, hpp⟩
    congr 1
    ext S
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · intro hS
      exact ⟨hS.trans hsubP, hS⟩
    · rintro ⟨_, hS⟩
      exact hS
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  -- each subset `S` is counted on the multiples of `∏ S`
  have hS : ∀ S ∈ P.powerset,
      ∑ n ∈ Icc 1 x, (if S ⊆ n.primeFactors then ∏ p ∈ S, f p else 0)
        ≤ (x : ℝ) * ∏ p ∈ S, (1 / (((p : ℝ) - 1) * p)) := by
    intro S hSP
    have hSP' : S ⊆ P := Finset.mem_powerset.mp hSP
    have hprime : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp (hSP' hp)).2
    have hf0 : 0 ≤ ∏ p ∈ S, f p := by
      apply Finset.prod_nonneg
      intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
      simp only [hfdef]
      apply div_nonneg zero_le_one
      linarith
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((((Icc 1 x).filter (fun n => S ⊆ n.primeFactors)).card : ℕ) : ℝ)
        ≤ (x : ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) := by
      have hsub : (Icc 1 x).filter (fun n => S ⊆ n.primeFactors)
          ⊆ (Icc 1 x).filter (fun n => (∏ p ∈ S, p) ∣ n) := by
        intro n hn
        obtain ⟨hnI, hSn⟩ := Finset.mem_filter.mp hn
        refine Finset.mem_filter.mpr ⟨hnI, ?_⟩
        exact Finset.prod_primes_dvd n (fun p hp => (hprime p hp).prime)
          (fun p hp => Nat.dvd_of_mem_primeFactors (hSn hp))
      exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (card_filter_dvd_le _ x)
    have hprodR : ((∏ p ∈ S, p : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by push_cast; rfl
    rw [hprodR] at hcard
    calc ((((Icc 1 x).filter (fun n => S ⊆ n.primeFactors)).card : ℕ) : ℝ) * ∏ p ∈ S, f p
        ≤ (x : ℝ) / (∏ p ∈ S, (p : ℝ)) * ∏ p ∈ S, f p :=
          mul_le_mul_of_nonneg_right hcard hf0
      _ = (x : ℝ) * ∏ p ∈ S, (1 / (((p : ℝ) - 1) * p)) := by
          rw [div_mul_eq_mul_div, mul_div_assoc]
          congr 1
          rw [← Finset.prod_div_distrib]
          apply Finset.prod_congr rfl
          intro p hp
          simp only [hfdef]
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
          have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
          have h0 : (p : ℝ) ≠ 0 := by linarith
          field_simp
  calc ∑ S ∈ P.powerset, ∑ n ∈ Icc 1 x, (if S ⊆ n.primeFactors then ∏ p ∈ S, f p else 0)
      ≤ ∑ S ∈ P.powerset, (x : ℝ) * ∏ p ∈ S, (1 / (((p : ℝ) - 1) * p)) :=
        Finset.sum_le_sum hS
    _ = (x : ℝ) * ∏ p ∈ P, (1 + 1 / (((p : ℝ) - 1) * p)) := by
        rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ (x : ℝ) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (prod_primes_one_add_le_exp_one x) (Nat.cast_nonneg _)
    _ = Real.exp 1 * x := by ring

/-- **The elementary remark after `prop:badcof`.**  For `η > 0` and `x ≥ 1`,
`#(B(η) ∩ [1, x]) < 3ηx`, by Markov's inequality applied to the mean of
`n/φ(n)`. -/
theorem card_excludedCofactorSet_lt {η : ℝ} (hη : 0 < η) {x : ℕ} (hx : 1 ≤ x) :
    ((((Icc 1 x).filter (· ∈ excludedCofactorSet η)).card : ℕ) : ℝ) < 3 * η * x := by
  have hkey : ((((Icc 1 x).filter (· ∈ excludedCofactorSet η)).card : ℕ) : ℝ)
      ≤ η * ∑ n ∈ Icc 1 x, (n : ℝ) / Nat.totient n := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    calc ∑ n ∈ (Icc 1 x).filter (· ∈ excludedCofactorSet η), ((1 : ℕ) : ℝ)
        ≤ ∑ n ∈ (Icc 1 x).filter (· ∈ excludedCofactorSet η),
            η * ((n : ℝ) / Nat.totient n) := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨_, hn1, hlt⟩ := Finset.mem_filter.mp hn
          have hφ : (0 : ℝ) < Nat.totient n := by
            exact_mod_cast Nat.totient_pos.mpr (by omega)
          rw [Nat.cast_one, mul_div_assoc', le_div_iff₀ hφ, one_mul]
          exact hlt.le
      _ ≤ ∑ n ∈ Icc 1 x, η * ((n : ℝ) / Nat.totient n) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro n _ _
          positivity
  have hsum := sum_div_totient_le x
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have h1 : η * ∑ n ∈ Icc 1 x, (n : ℝ) / Nat.totient n ≤ η * (Real.exp 1 * x) :=
    mul_le_mul_of_nonneg_left hsum hη.le
  have h2 : η * (Real.exp 1 * x) < η * (3 * x) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right he hxR) hη
  linarith

/-- `B(η)` has upper density at most `3η`, with no appeal to the existence of a
density. -/
theorem excludedCofactorSet_upperDensityLE {η : ℝ} (hη : 0 < η) :
    UpperDensityLE (excludedCofactorSet η) (3 * η) := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 1] with x hx
  have h := card_excludedCofactorSet_lt hη hx
  have hεx : 0 ≤ ε * (x : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg x)
  linarith

/-- **Hence `D(η) ≤ 3η`** whenever `B(η)` has a natural density `D(η)`. -/
theorem density_le_three_mul {η D : ℝ} (hη : 0 < η)
    (hD : HasNaturalDensity (excludedCofactorSet η) D) : D ≤ 3 * η := by
  apply le_of_tendsto hD
  filter_upwards [eventually_ge_atTop 1] with x hx
  have h := card_excludedCofactorSet_lt hη hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  rw [div_le_iff₀ hxR]
  linarith

end ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.upper_density_harmonic_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.card_excludedCofactorSet_lt
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.density_le_three_mul
