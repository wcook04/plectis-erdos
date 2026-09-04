import Erdos257PeriodNoncollapse.TotientCarryKernelRigidity

/-!
# A parity-perturbed rational control for the binary totient series

Let `S = ∑_{n≥1} φ(n)/2^n` (Erdős #249 asks whether `S` is irrational).  This
module constructs a coefficient sequence `c : ℕ → ℕ` with

* `c n ≤ n` for every `n` (the growth hypothesis of the tempered-orbit
  equivalence);
* `c n = φ n` for every **odd** `n`;
* `|c n - φ n| ≤ 2` for every `n` (in fact `-2 ≤ c n - φ n ≤ 1`);
* `∑_{n≥1} c(n)/2^n = 5/4`, a rational number.

The construction is a centred base-four expansion.  Put `ξ = 5/4 - S`; the
elementary bounds `9/8 ≤ S ≤ 3/2` place `ξ` in the remainder interval
`J = [-2/3, 1/3)` of the digit set `{-2,-1,0,1}`, which is a complete residue
system modulo `4`.  The digits `d_m = ⌊4 x_{m-1} + 2/3⌋`, `x_m = 4 x_{m-1} - d_m`
satisfy `ξ = ∑_{m≥1} d_m 4^{-m}`, and `c(2m) = φ(2m) + d_m`, `c(odd) = φ(odd)`.

## What this retires

Because `c` agrees with `φ` at every odd argument, every odd dyadic section of
`c` **is** the corresponding odd totient section.  Those sections are linearly
independent (`linearIndependent_canonicalTotientKernelFamily`), and they are
exactly the source of the carry anti-compression bound
`finrank_canonicalCarryKernel_ge_of_linearIndependent`.  Hence every
hypothesis of that theorem, and its conclusion (a tempered integral carry whose
dyadic section rank is at least `2^e - 1` at every level), holds for `c`,
while the series is rational.  The paper's open problem "totient carry-rank
compression" therefore cannot be answered positively by any argument whose
only inputs are the recurrence, temperedness, the growth bound, and the odd
totient channels: such an argument would also apply to `c`.

More generally: any irrationality proof for `S` must distinguish `φ` from a
sequence that coincides with it on all odd integers and differs by at most two
on the even ones.  Nothing here bears on whether `S` itself is irrational.
-/

namespace ErdosProblems.Erdos249.ParityPerturbedRationalControl

open Erdos257PeriodNoncollapse Module Filter Topology

/-! ## Centred base-four digits with digit set `{-2,-1,0,1}` -/

/-- The digit extracted from `x`: `⌊4x + 2/3⌋`. -/
noncomputable def digit (x : ℝ) : ℤ := ⌊4 * x + 2 / 3⌋

/-- One centred base-four step: `x ↦ 4x - ⌊4x + 2/3⌋`. -/
noncomputable def step (x : ℝ) : ℝ := 4 * x - (digit x : ℝ)

/-- Iterated remainders. -/
noncomputable def rem (x : ℝ) : ℕ → ℝ
  | 0 => x
  | m + 1 => step (rem x m)

/-- The `m`-th digit (`m ≥ 0`), carrying weight `4^{-(m+1)}`. -/
noncomputable def dig (x : ℝ) (m : ℕ) : ℤ := digit (rem x m)

/-- The remainder interval `J = [-2/3, 1/3)`. -/
def InJ (x : ℝ) : Prop := -2 / 3 ≤ x ∧ x < 1 / 3

theorem digit_bounds {x : ℝ} (hx : InJ x) : -2 ≤ digit x ∧ digit x ≤ 1 := by
  obtain ⟨h1, h2⟩ := hx
  constructor
  · rw [digit, Int.le_floor]
    push_cast
    linarith
  · have h : digit x < 2 := by
      rw [digit, Int.floor_lt]
      push_cast
      linarith
    omega

theorem step_mem (x : ℝ) : InJ (step x) := by
  have h1 := Int.floor_le (4 * x + 2 / 3)
  have h2 := Int.lt_floor_add_one (4 * x + 2 / 3)
  constructor
  · simp only [step, digit]
    linarith
  · simp only [step, digit]
    linarith

theorem rem_mem {x : ℝ} (hx : InJ x) (m : ℕ) : InJ (rem x m) := by
  induction m with
  | zero => exact hx
  | succ _ _ => exact step_mem _

theorem dig_bounds {x : ℝ} (hx : InJ x) (m : ℕ) : -2 ≤ dig x m ∧ dig x m ≤ 1 :=
  digit_bounds (rem_mem hx m)

theorem rem_succ (x : ℝ) (m : ℕ) :
    rem x (m + 1) = 4 * rem x m - (dig x m : ℝ) := rfl

theorem abs_rem_le {x : ℝ} (hx : InJ x) (m : ℕ) : |rem x m| ≤ 2 / 3 := by
  obtain ⟨h1, h2⟩ := rem_mem hx m
  rw [abs_le]
  constructor <;> linarith

/-- Finite expansion with exact remainder. -/
theorem expansion (x : ℝ) (M : ℕ) :
    x = (∑ m ∈ Finset.range M, (dig x m : ℝ) / 4 ^ (m + 1)) + rem x M / 4 ^ M := by
  induction M with
  | zero => simp [rem]
  | succ M ih =>
      rw [Finset.sum_range_succ, rem_succ]
      have h4 : (4 : ℝ) ^ (M + 1) = 4 * 4 ^ M := by ring
      have hpos : (0 : ℝ) < 4 ^ M := pow_pos (by norm_num) M
      have hsplit : rem x M / 4 ^ M =
          (dig x M : ℝ) / 4 ^ (M + 1) + (4 * rem x M - (dig x M : ℝ)) / 4 ^ (M + 1) := by
        rw [h4]
        field_simp
        ring
      linarith [ih, hsplit]

theorem abs_dig_le {x : ℝ} (hx : InJ x) (m : ℕ) : |(dig x m : ℝ)| ≤ 2 := by
  obtain ⟨h1, h2⟩ := dig_bounds hx m
  rw [abs_le]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast (by omega : dig x m ≤ 2)⟩

theorem summable_digits {x : ℝ} (hx : InJ x) :
    Summable (fun m : ℕ => (dig x m : ℝ) / 4 ^ (m + 1)) := by
  refine Summable.of_norm_bounded
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)) ?_
  intro m
  have hpos : (0 : ℝ) < 4 ^ (m + 1) := pow_pos (by norm_num) _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
  calc |(dig x m : ℝ)| / 4 ^ (m + 1) ≤ 2 / 4 ^ (m + 1) := by
        gcongr
        exact abs_dig_le hx m
    _ = (1 / 2) * (1 / 4) ^ m := by
        rw [one_div_pow, pow_succ]
        field_simp
        norm_num
    _ ≤ (1 / 4) ^ m := by
        have : (0 : ℝ) ≤ (1 / 4) ^ m := pow_nonneg (by norm_num) m
        linarith

/-- The centred digits sum to `x`. -/
theorem hasSum_digits {x : ℝ} (hx : InJ x) :
    HasSum (fun m : ℕ => (dig x m : ℝ) / 4 ^ (m + 1)) x := by
  have hs := summable_digits hx
  rw [hs.hasSum_iff_tendsto_nat]
  have key : ∀ M : ℕ, ∑ m ∈ Finset.range M, (dig x m : ℝ) / 4 ^ (m + 1) =
      x - rem x M / 4 ^ M := fun M => by linarith [expansion x M]
  simp_rw [key]
  have h0 : Tendsto (fun M : ℕ => rem x M / 4 ^ M) atTop (𝓝 0) := by
    have hg : Tendsto (fun M : ℕ => (2 / 3 : ℝ) * (1 / 4) ^ M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).const_mul (2 / 3 : ℝ)
    refine squeeze_zero_norm (fun M => ?_) hg
    have hpos : (0 : ℝ) < 4 ^ M := pow_pos (by norm_num) M
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    calc |rem x M| / 4 ^ M ≤ (2 / 3) / 4 ^ M := by
          gcongr
          exact abs_rem_le hx M
      _ = (2 / 3) * (1 / 4) ^ M := by
          rw [one_div_pow]
          ring
  simpa using tendsto_const_nhds.sub h0

/-! ## Elementary bounds on the totient series -/

/-- The binary totient series in the repository's coefficient-series
coordinate: `∑' n, φ(n+1)/2^(n+1)`. -/
noncomputable abbrev S : ℝ := binaryCoeffSeries Nat.totient

theorem summable_totientTerm :
    Summable (fun n : ℕ => (Nat.totient (n + 1) : ℝ) / 2 ^ (n + 1)) := by
  have h := summable_coeff_shift_tail 2 0 Nat.totient (by norm_num) Nat.totient_le
  simpa using h

theorem S_ge : (9 / 8 : ℝ) ≤ S := by
  have h := Summable.sum_le_tsum (Finset.range 4) (fun n _ => by positivity) summable_totientTerm
  have h3 : Nat.totient 3 = 2 := by decide
  have h4 : Nat.totient 4 = 2 := by decide
  have hval : ∑ n ∈ Finset.range 4, (Nat.totient (n + 1) : ℝ) / 2 ^ (n + 1) = 9 / 8 := by
    simp [Finset.sum_range_succ, Nat.totient_one, Nat.totient_two, h3, h4]
    norm_num
  unfold S binaryCoeffSeries
  linarith

theorem summable_idTerm :
    Summable (fun n : ℕ => (n : ℝ) / 2 ^ (n + 1)) := by
  have h := summable_coeff_shift_tail 2 0 id (by norm_num) (fun m => le_rfl)
  simp only [id, zero_add] at h
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
  push_cast
  gcongr
  linarith

theorem tsum_idTerm : ∑' n : ℕ, (n : ℝ) / 2 ^ (n + 1) = 1 := by
  have hgeom := tsum_coe_mul_geometric_of_norm_lt_one
    (show ‖(1 / 2 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)
  have hrw : (fun n : ℕ => (n : ℝ) / 2 ^ (n + 1)) =
      fun n : ℕ => (1 / 2 : ℝ) * ((n : ℝ) * (1 / 2) ^ n) := by
    funext n
    rw [one_div_pow, pow_succ]
    field_simp
  rw [hrw, tsum_mul_left, hgeom]
  norm_num

theorem S_le : S ≤ 3 / 2 := by
  have hite : Summable (fun n : ℕ => if n = 0 then (1 / 2 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℕ) (1 / 2 : ℝ)).summable
  have hg : Summable (fun n : ℕ => (if n = 0 then (1 / 2 : ℝ) else 0) + (n : ℝ) / 2 ^ (n + 1)) :=
    hite.add summable_idTerm
  have hle : ∀ n : ℕ, (Nat.totient (n + 1) : ℝ) / 2 ^ (n + 1) ≤
      (if n = 0 then (1 / 2 : ℝ) else 0) + (n : ℝ) / 2 ^ (n + 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.totient_one]
    · have hlt : Nat.totient (n + 1) < n + 1 := Nat.totient_lt (n + 1) (by omega)
      have hle' : (Nat.totient (n + 1) : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hlt
      simp only [hn.ne', if_false, zero_add]
      gcongr
  have hsum : ∑' n : ℕ, ((if n = 0 then (1 / 2 : ℝ) else 0) + (n : ℝ) / 2 ^ (n + 1)) = 3 / 2 := by
    rw [hite.tsum_add summable_idTerm, tsum_ite_eq, tsum_idTerm]
    norm_num
  unfold S binaryCoeffSeries
  calc ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) / 2 ^ (n + 1)
      ≤ ∑' n : ℕ, ((if n = 0 then (1 / 2 : ℝ) else 0) + (n : ℝ) / 2 ^ (n + 1)) :=
        Summable.tsum_le_tsum hle summable_totientTerm hg
    _ = 3 / 2 := hsum

/-! ## The control sequence -/

/-- `ξ = 5/4 - S`, the quantity expanded in centred base four. -/
noncomputable def xi : ℝ := 5 / 4 - S

theorem xi_mem : InJ xi := by
  unfold InJ xi
  constructor
  · linarith [S_le]
  · linarith [S_ge]

theorem xi_ge : -5 / 12 ≤ xi := by
  unfold xi
  linarith [S_le]

/-- The perturbation: the `m`-th centred digit at the even argument `2m`, zero
at odd arguments and at `0`. -/
noncomputable def delta (n : ℕ) : ℤ :=
  if n % 2 = 0 ∧ 2 ≤ n then dig xi (n / 2 - 1) else 0

/-- The control coefficient sequence `c = φ + δ`. -/
noncomputable def control (n : ℕ) : ℕ := ((Nat.totient n : ℤ) + delta n).toNat

theorem delta_odd {n : ℕ} (hn : n % 2 = 1) : delta n = 0 := by
  simp [delta, hn]

theorem delta_zero : delta 0 = 0 := by
  simp [delta]

theorem delta_even (m : ℕ) : delta (2 * m + 2) = dig xi m := by
  have h1 : (2 * m + 2) % 2 = 0 := by omega
  simp [delta, h1]

theorem delta_bounds (n : ℕ) : -2 ≤ delta n ∧ delta n ≤ 1 := by
  unfold delta
  split_ifs with h
  · exact dig_bounds xi_mem _
  · omega

theorem delta_two : -1 ≤ delta 2 := by
  have h : delta 2 = dig xi 0 := by simpa using delta_even 0
  rw [h, dig, rem, digit, Int.le_floor]
  push_cast
  linarith [xi_ge]

theorem totient_ge_two_of_even {n : ℕ} (hn : n % 2 = 0) (h4 : 4 ≤ n) :
    2 ≤ Nat.totient n := by
  have hev := Nat.totient_even (show 2 < n by omega)
  have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  obtain ⟨k, hk⟩ := hev
  omega

theorem totient_add_delta_nonneg (n : ℕ) : 0 ≤ (Nat.totient n : ℤ) + delta n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [delta_zero]
  by_cases hodd : n % 2 = 1
  · rw [delta_odd hodd]
    positivity
  have heven : n % 2 = 0 := by omega
  by_cases h2 : n = 2
  · subst h2
    have := delta_two
    simp only [Nat.totient_two, Nat.cast_one]
    omega
  · have h4 : 4 ≤ n := by omega
    have := totient_ge_two_of_even heven h4
    have := (delta_bounds n).1
    omega

theorem control_cast (n : ℕ) : (control n : ℤ) = (Nat.totient n : ℤ) + delta n := by
  unfold control
  exact Int.toNat_of_nonneg (totient_add_delta_nonneg n)

theorem control_cast_real (n : ℕ) :
    (control n : ℝ) = (Nat.totient n : ℝ) + (delta n : ℝ) := by
  have h := control_cast n
  exact_mod_cast h

theorem control_odd {n : ℕ} (hn : n % 2 = 1) : control n = Nat.totient n := by
  have h := control_cast n
  rw [delta_odd hn, add_zero] at h
  exact_mod_cast h

theorem control_le (n : ℕ) : control n ≤ n := by
  have h := control_cast n
  have hb := delta_bounds n
  have htot : Nat.totient n ≤ n := Nat.totient_le n
  by_cases hd : delta n ≤ 0
  · omega
  · have hd1 : delta n = 1 := by omega
    have hn : n % 2 = 0 ∧ 2 ≤ n := by
      by_contra hcon
      have : delta n = 0 := by simp [delta, hcon]
      omega
    have hlt : Nat.totient n < n := Nat.totient_lt n (by omega)
    omega

theorem control_sub_totient_bounds (n : ℕ) :
    -2 ≤ (control n : ℤ) - Nat.totient n ∧ (control n : ℤ) - Nat.totient n ≤ 1 := by
  rw [control_cast]
  have := delta_bounds n
  omega

theorem abs_control_sub_totient_le (n : ℕ) : |(control n : ℤ) - Nat.totient n| ≤ 2 := by
  have := control_sub_totient_bounds n
  rw [abs_le]
  omega

/-! ## The series of the control is `5/4` -/

theorem summable_deltaTerm :
    Summable (fun n : ℕ => (delta (n + 1) : ℝ) / 2 ^ (n + 1)) := by
  refine Summable.of_norm_bounded
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) ?_
  intro n
  have hpos : (0 : ℝ) < 2 ^ (n + 1) := pow_pos (by norm_num) _
  have hb : |(delta (n + 1) : ℝ)| ≤ 2 := by
    obtain ⟨h1, h2⟩ := delta_bounds (n + 1)
    rw [abs_le]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast (by omega : delta (n + 1) ≤ 2)⟩
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
  calc |(delta (n + 1) : ℝ)| / 2 ^ (n + 1) ≤ 2 / 2 ^ (n + 1) := by
        gcongr
    _ = (1 / 2) ^ n := by
        rw [one_div_pow, pow_succ]
        field_simp

theorem tsum_deltaTerm : ∑' n : ℕ, (delta (n + 1) : ℝ) / 2 ^ (n + 1) = xi := by
  have hf := summable_deltaTerm
  have he : Summable (fun k : ℕ => (delta (2 * k + 1) : ℝ) / 2 ^ (2 * k + 1)) :=
    hf.comp_injective (fun a b h => by simp only at h; omega : Function.Injective (fun k : ℕ => 2 * k))
  have ho : Summable (fun k : ℕ => (delta (2 * k + 1 + 1) : ℝ) / 2 ^ (2 * k + 1 + 1)) :=
    hf.comp_injective
      (fun a b h => by simp only at h; omega : Function.Injective (fun k : ℕ => 2 * k + 1))
  have hsplit := tsum_even_add_odd (f := fun n : ℕ => (delta (n + 1) : ℝ) / 2 ^ (n + 1)) he ho
  simp only at hsplit
  rw [← hsplit]
  have hzero : ∑' k : ℕ, (delta (2 * k + 1) : ℝ) / 2 ^ (2 * k + 1) = 0 := by
    have : (fun k : ℕ => (delta (2 * k + 1) : ℝ) / 2 ^ (2 * k + 1)) = fun _ => 0 := by
      funext k
      rw [delta_odd (by omega)]
      simp
    rw [this, tsum_zero]
  have hodd : (fun k : ℕ => (delta (2 * k + 1 + 1) : ℝ) / 2 ^ (2 * k + 1 + 1)) =
      fun k : ℕ => (dig xi k : ℝ) / 4 ^ (k + 1) := by
    funext k
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, delta_even,
      show (2 : ℝ) ^ (2 * k + 2) = 4 ^ (k + 1) by
        rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
        norm_num]
  rw [hzero, hodd, zero_add, (hasSum_digits xi_mem).tsum_eq]

/-- **Main identity.**  The control series is exactly `5/4`. -/
theorem control_series : binaryCoeffSeries control = 5 / 4 := by
  unfold binaryCoeffSeries
  have hrw : (fun n : ℕ => (control (n + 1) : ℝ) / 2 ^ (n + 1)) =
      fun n : ℕ => (Nat.totient (n + 1) : ℝ) / 2 ^ (n + 1) + (delta (n + 1) : ℝ) / 2 ^ (n + 1) := by
    funext n
    rw [control_cast_real, add_div]
  rw [hrw, summable_totientTerm.tsum_add summable_deltaTerm, tsum_deltaTerm]
  unfold xi S binaryCoeffSeries
  ring

theorem not_irrational_control : ¬ Irrational (binaryCoeffSeries control) := by
  rw [control_series]
  intro h
  exact h ⟨(5 / 4 : ℚ), by push_cast; norm_num⟩

/-- **Summary.**  A coefficient sequence bounded by `n`, equal to `φ` at every
odd argument, within `2` of `φ` everywhere, with rational binary series. -/
theorem parity_perturbed_rational_control :
    (∀ n, control n ≤ n) ∧ (∀ n, n % 2 = 1 → control n = Nat.totient n) ∧
      (∀ n, |(control n : ℤ) - Nat.totient n| ≤ 2) ∧
      binaryCoeffSeries control = 5 / 4 :=
  ⟨control_le, fun _ hn => control_odd hn, abs_control_sub_totient_le, control_series⟩

/-! ## Carry-rank transfer for any coefficient agreeing with `φ` on odd arguments -/

/-- For a tempered orbit of any coefficient sequence that agrees with `φ` on
odd arguments, every odd totient channel at a positive level is a two-term
difference of carry sections. -/
theorem oddAgree_carryKernel_diff {c : ℕ → ℕ}
    (hodd : ∀ n, n % 2 = 1 → c n = Nat.totient n)
    {v : ℕ} {u : ℕ → ℤ} (hu : IsTemperedBinaryOrbit c v u) (j r : ℕ) :
    (fun n => (v : ℚ) * totientKernelSeq (j + 1) (2 * r + 1) n) =
      fun n => 2 * carryKernelSeq u (j + 1) (2 * r + 1 - 1) n -
        carryKernelSeq u (j + 1) (2 * r + 1) n := by
  funext n
  have hpos : 0 < 2 ^ (j + 1) * n + (2 * r + 1) := by omega
  have h := carryDerivative_eq_scaledCoeff_of_recurrence hu.1 hpos
  have hidx : 2 ^ (j + 1) * n + (2 * r + 1) - 1 = 2 ^ (j + 1) * n + (2 * r + 1 - 1) := by omega
  obtain ⟨t, ht⟩ : 2 ∣ 2 ^ (j + 1) * n := dvd_mul_of_dvd_left (dvd_pow_self 2 (Nat.succ_ne_zero j)) n
  have hparity : (2 ^ (j + 1) * n + (2 * r + 1)) % 2 = 1 := by omega
  have hc : c (2 ^ (j + 1) * n + (2 * r + 1)) = Nat.totient (2 ^ (j + 1) * n + (2 * r + 1)) :=
    hodd _ hparity
  rw [hc] at h
  simpa [carryDerivative, carryKernelSeq, totientKernelSeq, hidx] using
    congrArg (fun z : ℤ => (z : ℚ)) h.symm

theorem canonicalCarryDifferenceFamily_eq_smul_totient_of_oddAgree {c : ℕ → ℕ}
    (hodd : ∀ n, n % 2 = 1 → c n = Nat.totient n)
    {v : ℕ} {u : ℕ → ℤ} (hu : IsTemperedBinaryOrbit c v u) (e : ℕ) :
    canonicalCarryDifferenceFamily u e =
      fun i => (v : ℚ) • canonicalTotientOddKernelFamily e i := by
  funext i
  rcases i with ⟨j, r⟩
  have h := oddAgree_carryKernel_diff hodd hu j.val r.val
  simpa [canonicalCarryDifferenceFamily, canonicalCarryKernelFamily,
    canonicalTotientOddKernelFamily, carryEvenIndex, carryOddIndex,
    Pi.smul_apply, smul_eq_mul] using h.symm

/-- **Carry anti-compression for odd-agreeing coefficients.**  The finite-level
carry sections of any tempered orbit of a coefficient sequence agreeing with
`φ` at odd arguments have rank at least `2^e - 1`.  This is the existing
totient theorem with its only totient input, the odd channels, kept. -/
theorem finrank_canonicalCarryKernel_ge_of_oddAgree {c : ℕ → ℕ}
    (hodd : ∀ n, n % 2 = 1 → c n = Nat.totient n)
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit c v u) (e : ℕ) :
    2 ^ e - 1 ≤
      finrank ℚ
        (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  have hcanon := linearIndependent_canonicalTotientKernelFamily e
  have hoddind := linearIndependent_totientOddKernelFamily e hcanon
  let q : ℚˣ := Units.mk0 (v : ℚ) (by exact_mod_cast (Nat.ne_of_gt hv))
  have hscaled : LinearIndependent ℚ
      ((fun _ : TotientOddIndex e => q) • canonicalTotientOddKernelFamily e) :=
    hoddind.units_smul (fun _ => q)
  have hscale_eq :
      ((fun _ : TotientOddIndex e => q) • canonicalTotientOddKernelFamily e) =
        (fun i => (v : ℚ) • canonicalTotientOddKernelFamily e i) := by
    funext i n
    simp [q]
  rw [hscale_eq] at hscaled
  have hdiff : LinearIndependent ℚ (canonicalCarryDifferenceFamily u e) := by
    rw [canonicalCarryDifferenceFamily_eq_smul_totient_of_oddAgree hodd hu e]
    exact hscaled
  letI : Module.Finite ℚ
      (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range _)
  rw [← card_totientOddIndex e]
  have hrank := finrank_span_eq_card hdiff
  rw [← hrank]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact canonicalCarryDifferenceFamily_mem_span u e i

/-- **The control satisfies the whole anti-compression architecture.**  It has
a tempered integral binary carry whose dyadic section rank is at least
`2^e - 1` at every level, exactly as a rational value of the totient series
would force; and its series is the rational number `5/4`. -/
theorem control_temperedOrbit_carryRank_unbounded :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit control v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  obtain ⟨v, hv, u, hu⟩ :=
    (not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit control control_le).mp
      not_irrational_control
  exact ⟨v, hv, u, hu, fun e =>
    finrank_canonicalCarryKernel_ge_of_oddAgree (fun _ hn => control_odd hn) hv hu e⟩

#print axioms parity_perturbed_rational_control
#print axioms control_series
#print axioms not_irrational_control
#print axioms finrank_canonicalCarryKernel_ge_of_oddAgree
#print axioms control_temperedOrbit_carryRank_unbounded

end ErdosProblems.Erdos249.ParityPerturbedRationalControl
