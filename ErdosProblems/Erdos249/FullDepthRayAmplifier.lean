import ErdosProblems.Erdos249.PeriodMultipleEscape

/-!
# Erdős #249: the full-depth ray amplifier

`PeriodMultipleEscape` records `ApFullDepthEscape` — the depth-locked variant
`L = h` of the kill supply — as "sufficient, and the cleanest single open
statement this programme has produced, **but not known necessary**".  This
file removes that gap.

## What is proved

The certificate is upgraded from a Boolean to a *metric* statement.  A kill at
`(h, N, L)` does not merely refute integrality of the shift
`Δ_h(N) = R_{N+h} - R_N`: it separates `Δ_h(N)` from **every** integer by
`2^{-L}` (`one_le_pow_mul_abs_shift_sub_int`), and conversely a failed
certificate pins `Δ_h(N)` within `2(N+h+L+2)/2^L` of some integer
(`exists_abs_shift_sub_int_le_of_not_certifiedKill`).  Between the two sits an
exact converse: a shift that is `2(N+h+L+2)/2^L`-separated from every integer
*is* certified (`certifiedKill_of_forall_dist`).

The second ingredient is that consecutive multiples of a period are **not
independent phase tests**.  The shift concatenates,
`Δ_{a+b}(N) = 2^b·Δ_a(N) + Δ_b(N) + z` with `z ∈ ℤ`
(`exists_int_shift_concat`), so if `Δ_{td}` and `Δ_{(t+1)d}` were both within
`ε` of integers then `Δ_d` would be within `(1+2^d)ε` of one.

Combining: one seed certificate on a ray forces a **fixed** separation
constant `c/(1+2^d)` to be attained by at least one of every adjacent pair of
multiples, and exponential depth then beats the linear arc radius.  Hence

* `exists_adjacent_fullDepthKill_of_seed` — beyond an explicit threshold every
  adjacent pair `{td, (t+1)d}` contains a **depth = period** certificate.  The
  successful multipliers are eventually `2`-syndetic; in particular they have
  lower density at least `1/2`.
* `exists_fullDepthKill_on_ray_iff_shift_notMem_int` — pointwise equivalence.
* `apFullDepthEscape_iff_irrational` — the depth lock is free.
* `cofinalFullDepthKillSupply_iff_periodMultipleKillSupply` — the depth
  quantifier can be deleted from the exact supply.

## Claim ceiling

**Erdős #249 remains open.**  Nothing here produces a seed.  What is settled
is that matching certificate depth to period is *not* an additional arithmetic
obstruction: after one seed on a ray, full-depth certificates recur with
bounded gaps.  The whole remaining producer is arbitrary-ray seed supply,
which `periodMultipleKillSupply_iff_irrational` already identifies with
irrationality itself.
-/

namespace ErdosProblems.Erdos249.FullDepthRayAmplifier

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.TotientTailPeriodKiller
open ErdosProblems.Erdos249.PeriodMultipleEscape

/-- The `h`-shift of the local totient tail at basepoint `N`. -/
noncomputable def shift (h N : ℕ) : ℝ :=
  totientTail (N + h) - totientTail N

@[simp] theorem shift_zero (N : ℕ) : shift 0 N = 0 := by
  simp [shift]

/-! ## The metric form of the certificate -/

/-- **Coarea bound.**  The depth-`L` window integer approximates the scaled
shift to within the arc radius.  This is the analytic content of certificate
soundness, isolated as a two-sided estimate. -/
theorem abs_pow_mul_shift_sub_windowDiscrepancy_le (h N L : ℕ) :
    |(2 : ℝ) ^ L * shift h N - (windowDiscrepancy h N L : ℝ)|
      ≤ (N : ℝ) + h + L + 2 := by
  have hdec1 := totientTail_eq_partial_add_tail (N + h) L
  have hdec2 := totientTail_eq_partial_add_tail N L
  have hA := windowDiscrepancy_div_eq h N L
  have hT1n := tail_after_nonneg (N + h) L
  have hT2n := tail_after_nonneg N L
  have hT1u := tail_after_le (N + h) L
  have hT2u := tail_after_le N L
  push_cast at hT1u
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  set W1 := ∑ j ∈ Finset.range L, (Nat.totient (N + h + 1 + j) : ℝ) / 2 ^ (j + 1) with hW1
  set W2 := ∑ j ∈ Finset.range L, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1) with hW2
  set T1 := ∑' j : ℕ, (Nat.totient (N + h + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT1
  set T2 := ∑' j : ℕ, (Nat.totient (N + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT2
  have hAeq : ((windowDiscrepancy h N L : ℤ) : ℝ) = (W1 - W2) * 2 ^ L := by
    rw [← hA]
    field_simp
  have hkey : (2 : ℝ) ^ L * shift h N - (windowDiscrepancy h N L : ℝ)
      = T1 * 2 ^ L - T2 * 2 ^ L := by
    unfold shift
    rw [hdec1, hdec2, hAeq]
    ring
  have hs1 : T1 * 2 ^ L ≤ (N : ℝ) + h + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT1u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hs2 : T2 * 2 ^ L ≤ (N : ℝ) + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT2u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hn1 : 0 ≤ T1 * 2 ^ L := mul_nonneg hT1n h2L.le
  have hn2 : 0 ≤ T2 * 2 ^ L := mul_nonneg hT2n h2L.le
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  rw [hkey]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Integer separation supplied by a certificate: the window integer is at
least `radius + 1` away from every multiple of the modulus. -/
theorem add_one_le_abs_sub_mul_of_certifiedKill {h N L : ℕ}
    (hcert : certifiedKill h N L) (k : ℤ) :
    (N : ℤ) + h + L + 2 + 1 ≤ |windowDiscrepancy h N L - k * 2 ^ L| := by
  obtain ⟨hlow, hhigh⟩ := hcert
  have hPpos : (0 : ℤ) < 2 ^ L := by positivity
  have hxmod : (windowDiscrepancy h N L - k * 2 ^ L) % 2 ^ L
      = windowDiscrepancy h N L % 2 ^ L := by
    have hrw : windowDiscrepancy h N L - k * 2 ^ L
        = windowDiscrepancy h N L + 2 ^ L * (-k) := by ring
    rw [hrw, Int.add_mul_emod_self_left]
  have hdm := Int.mul_ediv_add_emod (windowDiscrepancy h N L - k * 2 ^ L) ((2 : ℤ) ^ L)
  rw [hxmod] at hdm
  rcases le_or_gt 0 ((windowDiscrepancy h N L - k * 2 ^ L) / 2 ^ L) with ht | ht
  · have hge : 0 ≤ (2 : ℤ) ^ L * ((windowDiscrepancy h N L - k * 2 ^ L) / 2 ^ L) :=
      mul_nonneg hPpos.le ht
    have hxge : (N : ℤ) + h + L + 2 + 1 ≤ windowDiscrepancy h N L - k * 2 ^ L := by omega
    exact hxge.trans (le_abs_self _)
  · have ht1 : (windowDiscrepancy h N L - k * 2 ^ L) / 2 ^ L ≤ -1 := by omega
    have hle : (2 : ℤ) ^ L * ((windowDiscrepancy h N L - k * 2 ^ L) / 2 ^ L)
        ≤ (2 : ℤ) ^ L * (-1) := mul_le_mul_of_nonneg_left ht1 hPpos.le
    have hneg : (2 : ℤ) ^ L * (-1) = -(2 : ℤ) ^ L := by ring
    have hxle : (N : ℤ) + h + L + 2 + 1 ≤ -(windowDiscrepancy h N L - k * 2 ^ L) := by omega
    exact hxle.trans (neg_le_abs _)

/-- Absence of a certificate pins the window integer inside the arc radius of
some multiple of the modulus. -/
theorem exists_abs_sub_mul_le_of_not_certifiedKill (h N L : ℕ)
    (hnot : ¬ certifiedKill h N L) :
    ∃ k : ℤ, |windowDiscrepancy h N L - k * 2 ^ L| ≤ (N : ℤ) + h + L + 2 := by
  have hPpos : (0 : ℤ) < 2 ^ L := by positivity
  have hr0 : 0 ≤ windowDiscrepancy h N L % 2 ^ L := Int.emod_nonneg _ hPpos.ne'
  have hrP : windowDiscrepancy h N L % 2 ^ L < 2 ^ L := Int.emod_lt_of_pos _ hPpos
  have hdm := Int.mul_ediv_add_emod (windowDiscrepancy h N L) ((2 : ℤ) ^ L)
  rcases not_and_or.mp hnot with hbad | hbad
  · refine ⟨windowDiscrepancy h N L / 2 ^ L, ?_⟩
    have hle : windowDiscrepancy h N L % 2 ^ L ≤ (N : ℤ) + h + L + 2 := by
      simpa using not_lt.mp hbad
    have heq : windowDiscrepancy h N L - windowDiscrepancy h N L / 2 ^ L * 2 ^ L
        = windowDiscrepancy h N L % 2 ^ L := by
      have hcomm : windowDiscrepancy h N L / 2 ^ L * (2 : ℤ) ^ L
          = (2 : ℤ) ^ L * (windowDiscrepancy h N L / 2 ^ L) := by ring
      omega
    rw [heq, abs_of_nonneg hr0]
    exact hle
  · refine ⟨windowDiscrepancy h N L / 2 ^ L + 1, ?_⟩
    have hge : (2 : ℤ) ^ L - ((N : ℤ) + h + L + 2) ≤ windowDiscrepancy h N L % 2 ^ L := by
      simpa using not_lt.mp hbad
    have heq : windowDiscrepancy h N L - (windowDiscrepancy h N L / 2 ^ L + 1) * 2 ^ L
        = windowDiscrepancy h N L % 2 ^ L - 2 ^ L := by
      have hexp : (windowDiscrepancy h N L / 2 ^ L + 1) * (2 : ℤ) ^ L
          = (2 : ℤ) ^ L * (windowDiscrepancy h N L / 2 ^ L) + 2 ^ L := by ring
      omega
    rw [heq, abs_of_nonpos (by omega)]
    omega

/-- **Quantitative certificate soundness.**  A certified kill separates the
shift from *every* integer by the reciprocal of its own depth. -/
theorem one_le_pow_mul_abs_shift_sub_int {h N L : ℕ}
    (hcert : certifiedKill h N L) (k : ℤ) :
    1 ≤ (2 : ℝ) ^ L * |shift h N - (k : ℝ)| := by
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hcoarea := abs_pow_mul_shift_sub_windowDiscrepancy_le h N L
  have hint := add_one_le_abs_sub_mul_of_certifiedKill hcert k
  have hcast : ((N : ℝ) + h + L + 2) + 1
      ≤ |(windowDiscrepancy h N L : ℝ) - (k : ℝ) * 2 ^ L| := by
    have h0 : ((|windowDiscrepancy h N L - k * 2 ^ L| : ℤ) : ℝ)
        = |(windowDiscrepancy h N L : ℝ) - (k : ℝ) * 2 ^ L| := by
      rw [Int.cast_abs]; push_cast; ring_nf
    rw [← h0]
    exact_mod_cast hint
  set X := (2 : ℝ) ^ L * shift h N with hX
  set A := ((windowDiscrepancy h N L : ℤ) : ℝ) with hA
  set Y := (k : ℝ) * 2 ^ L with hY
  have htri : |A - Y| ≤ |A - X| + |X - Y| := abs_sub_le A X Y
  have hAX : |A - X| ≤ (N : ℝ) + h + L + 2 := by
    rw [abs_sub_comm]; exact hcoarea
  have hXY : 1 ≤ |X - Y| := by linarith
  have hfac : X - Y = (2 : ℝ) ^ L * (shift h N - (k : ℝ)) := by
    rw [hX, hY]; ring
  rw [hfac, abs_mul, abs_of_pos h2L] at hXY
  exact hXY

/-- **Exact converse.**  A shift separated from every integer by more than
twice the arc radius over the modulus is certified at that depth. -/
theorem certifiedKill_of_forall_dist {h N L : ℕ}
    (hsep : ∀ k : ℤ, 2 * ((N : ℝ) + h + L + 2)
      < (2 : ℝ) ^ L * |shift h N - (k : ℝ)|) :
    certifiedKill h N L := by
  by_contra hnot
  obtain ⟨k, hk⟩ := exists_abs_sub_mul_le_of_not_certifiedKill h N L hnot
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hcoarea := abs_pow_mul_shift_sub_windowDiscrepancy_le h N L
  have hkR : |(windowDiscrepancy h N L : ℝ) - (k : ℝ) * 2 ^ L|
      ≤ (N : ℝ) + h + L + 2 := by
    have h0 : ((|windowDiscrepancy h N L - k * 2 ^ L| : ℤ) : ℝ)
        = |(windowDiscrepancy h N L : ℝ) - (k : ℝ) * 2 ^ L| := by
      rw [Int.cast_abs]; push_cast; ring_nf
    rw [← h0]
    exact_mod_cast hk
  set X := (2 : ℝ) ^ L * shift h N with hX
  set A := ((windowDiscrepancy h N L : ℤ) : ℝ) with hA
  set Y := (k : ℝ) * 2 ^ L with hY
  have htri : |X - Y| ≤ |X - A| + |A - Y| := abs_sub_le X A Y
  have hfac : X - Y = (2 : ℝ) ^ L * (shift h N - (k : ℝ)) := by rw [hX, hY]; ring
  have := hsep k
  rw [hfac, abs_mul, abs_of_pos h2L] at htri
  nlinarith [htri, hcoarea, hkR, this]

/-! ## The ray recurrence -/

/-- The shift is an affine function of the series with an integer offset. -/
theorem shift_eq_series (h N : ℕ) :
    shift h N = (2 : ℝ) ^ N * (2 ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      - ((totientPrefix (N + h) : ℝ) - (totientPrefix N : ℝ)) := by
  have h1 := two_pow_mul_totient_series_eq (N + h)
  have h2 := two_pow_mul_totient_series_eq N
  unfold shift
  linear_combination h2 - h1

/-- **Shift concatenation.**  Consecutive blocks along a ray are not
independent: they differ by an integer after one dyadic scaling. -/
theorem exists_int_shift_concat (a b N : ℕ) :
    ∃ z : ℤ, shift (a + b) N
      = (2 : ℝ) ^ b * shift a N + shift b N + (z : ℝ) := by
  refine ⟨(2 : ℤ) ^ b * ((totientPrefix (N + a) : ℤ) - (totientPrefix N : ℤ))
      + ((totientPrefix (N + b) : ℤ) - (totientPrefix N : ℤ))
      - ((totientPrefix (N + (a + b)) : ℤ) - (totientPrefix N : ℤ)), ?_⟩
  rw [shift_eq_series, shift_eq_series, shift_eq_series]
  push_cast
  ring

/-- Integrality of one step propagates to every multiple along its ray. -/
theorem exists_int_shift_mul_of_exists_int_shift {d N : ℕ}
    (hd : ∃ k : ℤ, shift d N = (k : ℝ)) (t : ℕ) :
    ∃ k : ℤ, shift (t * d) N = (k : ℝ) := by
  induction t with
  | zero => exact ⟨0, by simp⟩
  | succ t ih =>
      obtain ⟨k₁, hk₁⟩ := ih
      obtain ⟨k₀, hk₀⟩ := hd
      obtain ⟨z, hz⟩ := exists_int_shift_concat (t * d) d N
      refine ⟨(2 : ℤ) ^ d * k₁ + k₀ + z, ?_⟩
      have harr : (t + 1) * d = t * d + d := by ring
      rw [harr, hz, hk₁, hk₀]
      push_cast
      ring

/-- **The two-of-adjacent separation.**  A fixed separation of the seed forces
a fixed (smaller) separation on at least one of every adjacent pair of
multiples. -/
theorem forall_dist_adjacent_of_seed {d N : ℕ} {c : ℝ}
    (hseed : ∀ k : ℤ, c ≤ |shift d N - (k : ℝ)|) (t : ℕ) :
    (∀ k : ℤ, c / (1 + 2 ^ d) ≤ |shift (t * d) N - (k : ℝ)|) ∨
      (∀ k : ℤ, c / (1 + 2 ^ d) ≤ |shift ((t + 1) * d) N - (k : ℝ)|) := by
  have hden : (0 : ℝ) < 1 + 2 ^ d := by positivity
  by_contra hbad
  push_neg at hbad
  obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ := hbad
  obtain ⟨z, hz⟩ := exists_int_shift_concat (t * d) d N
  have harr : (t + 1) * d = t * d + d := by ring
  rw [harr] at hk₂
  have hd_eq : shift d N = shift (t * d + d) N - (2 : ℝ) ^ d * shift (t * d) N - (z : ℝ) := by
    rw [hz]; ring
  have hkey := hseed (k₂ - (2 : ℤ) ^ d * k₁ - z)
  have hsplit : shift d N - ((k₂ - (2 : ℤ) ^ d * k₁ - z : ℤ) : ℝ)
      = (shift (t * d + d) N - (k₂ : ℝ))
        - (2 : ℝ) ^ d * (shift (t * d) N - (k₁ : ℝ)) := by
    rw [hd_eq]; push_cast; ring
  rw [hsplit] at hkey
  have hb1 : |shift (t * d + d) N - (k₂ : ℝ)| < c / (1 + 2 ^ d) := hk₂
  have hb2 : |(2 : ℝ) ^ d * (shift (t * d) N - (k₁ : ℝ))| < 2 ^ d * (c / (1 + 2 ^ d)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2:ℝ) ^ d)]
    exact mul_lt_mul_of_pos_left hk₁ (by positivity : (0:ℝ) < (2:ℝ) ^ d)
  have htri := abs_sub (shift (t * d + d) N - (k₂ : ℝ))
    ((2 : ℝ) ^ d * (shift (t * d) N - (k₁ : ℝ)))
  have hc : c / (1 + 2 ^ d) + 2 ^ d * (c / (1 + 2 ^ d)) = c := by
    field_simp
  linarith [hkey, htri, hb1, hb2, hc]

/-! ## Exponential depth beats the linear arc radius -/

private theorem eventually_affine_mul_half_pow_lt {α β c : ℝ} (hc : 0 < c) :
    ∃ T : ℕ, ∀ m : ℕ, T ≤ m → (α + β * (m : ℝ)) * (1 / 2 : ℝ) ^ m < c := by
  have h1 : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 : Filter.Tendsto (fun m : ℕ => (m : ℝ) * (1 / 2 : ℝ) ^ m) Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have hsum : Filter.Tendsto (fun m : ℕ => (α + β * (m : ℝ)) * (1 / 2 : ℝ) ^ m)
      Filter.atTop (nhds 0) := by
    have := (h1.const_mul α).add (h2.const_mul β)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun m => ?_
    ring
  obtain ⟨T, hT⟩ := (hsum.eventually (gt_mem_nhds hc)).exists_forall_of_atTop
  exact ⟨T, hT⟩

/-- **The full-depth ray amplifier.**  One certificate anywhere on a ray forces
a **depth = period** certificate in every adjacent pair of multiples beyond an
explicit threshold: the successful multipliers are eventually `2`-syndetic. -/
theorem exists_adjacent_fullDepthKill_of_seed {d N L : ℕ} (hd : 0 < d)
    (hseed : certifiedKill d N L) :
    ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
      certifiedKill (t * d) N (t * d) ∨
        certifiedKill ((t + 1) * d) N ((t + 1) * d) := by
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  set c : ℝ := 1 / 2 ^ L with hcdef
  have hc : 0 < c := by rw [hcdef]; positivity
  have hsep : ∀ k : ℤ, c ≤ |shift d N - (k : ℝ)| := by
    intro k
    have := one_le_pow_mul_abs_shift_sub_int hseed k
    rw [hcdef, div_le_iff₀ h2L]
    nlinarith [this]
  set c' : ℝ := c / (1 + 2 ^ d) with hc'def
  have hc' : 0 < c' := by rw [hc'def]; positivity
  obtain ⟨T₀, hT₀⟩ := eventually_affine_mul_half_pow_lt
    (α := 2 * (N : ℝ) + 4) (β := 4 * (d : ℝ)) hc'
  refine ⟨T₀ + 1, by omega, ?_⟩
  intro t ht
  -- the separated member of the adjacent pair is certified at its own depth
  have hstep : ∀ m : ℕ, T₀ ≤ m →
      (∀ k : ℤ, c' ≤ |shift (m * d) N - (k : ℝ)|) → certifiedKill (m * d) N (m * d) := by
    intro m hm hdist
    refine certifiedKill_of_forall_dist fun k => ?_
    have hbound := hT₀ m hm
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have hcancel : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by
      rw [div_pow, one_pow]
      field_simp
    have hb : 2 * (N : ℝ) + 4 + 4 * (d : ℝ) * (m : ℝ) < c' * 2 ^ m := by
      have hmul := mul_lt_mul_of_pos_right hbound h2m
      rw [mul_assoc, hcancel, mul_one] at hmul
      exact hmul
    have hmd : m ≤ m * d := Nat.le_mul_of_pos_right m hd
    have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m * d) := pow_le_pow_right₀ (by norm_num) hmd
    have hlin : 2 * ((N : ℝ) + ((m * d : ℕ) : ℝ) + ((m * d : ℕ) : ℝ) + 2)
        = 2 * (N : ℝ) + 4 + 4 * (d : ℝ) * (m : ℝ) := by push_cast; ring
    have hdk := hdist k
    calc 2 * ((N : ℝ) + ((m * d : ℕ) : ℝ) + ((m * d : ℕ) : ℝ) + 2)
        = 2 * (N : ℝ) + 4 + 4 * (d : ℝ) * (m : ℝ) := hlin
      _ < c' * 2 ^ m := hb
      _ ≤ c' * 2 ^ (m * d) := by nlinarith [hpow, hc']
      _ ≤ (2 : ℝ) ^ (m * d) * |shift (m * d) N - (k : ℝ)| := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hdk (by positivity)
  rcases forall_dist_adjacent_of_seed hsep t with hcase | hcase
  · exact Or.inl (hstep t (by omega) hcase)
  · exact Or.inr (hstep (t + 1) (by omega) hcase)

/-- One seed yields one **depth = period** certificate on the same ray. -/
theorem exists_fullDepthKill_on_ray_of_seed {d N L : ℕ} (hd : 0 < d)
    (hseed : certifiedKill d N L) :
    ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d) := by
  obtain ⟨T, hTpos, hT⟩ := exists_adjacent_fullDepthKill_of_seed hd hseed
  rcases hT T le_rfl with hc | hc
  · exact ⟨T, hTpos, hc⟩
  · exact ⟨T + 1, by omega, hc⟩

/-- **Pointwise equivalence.**  Depth-locked certificates on a ray exist
exactly when the ray's own shift is non-integral. -/
theorem exists_fullDepthKill_on_ray_iff_shift_notMem_int {d N : ℕ} (hd : 0 < d) :
    (∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · rintro ⟨t, ht, hkill⟩ ⟨k, hk⟩
    refine tail_diff_notMem_int_of_certifiedKill hkill ?_
    have hshift : shift d N = (k : ℝ) := by rw [shift]; exact hk.symm
    obtain ⟨k', hk'⟩ := exists_int_shift_mul_of_exists_int_shift ⟨k, hshift⟩ t
    exact ⟨k', hk'.symm⟩
  · intro hnotint
    obtain ⟨L, hL⟩ := exists_certifiedKill_of_tail_diff_notMem_int hnotint
    exact exists_fullDepthKill_on_ray_of_seed hd hL

/-! ## The depth quantifier is free -/

/-- **The depth lock costs nothing.**  `ApFullDepthEscape` — depth locked to
the period — is *equivalent* to irrationality, not merely sufficient for it.
This closes the "not known necessary" gap recorded in `PeriodMultipleEscape`. -/
theorem apFullDepthEscape_iff_irrational :
    ApFullDepthEscape ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  constructor
  · exact irrational_totient_series_of_apFullDepthEscape
  · intro hirr d hd N
    have hnot := irrational_totient_series_iff_all_tail_diffs_nonintegral.mp hirr d hd N
    exact (exists_fullDepthKill_on_ray_iff_shift_notMem_int hd).mpr hnot

/-- The depth-locked cofinal supply. -/
def CofinalFullDepthKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ, ∃ t N : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N (t * d)

/-- **The depth parameter can be deleted from the exact supply.**  Demanding
depth = period cofinally is the same demand as the original arbitrary-depth
period-multiple supply. -/
theorem cofinalFullDepthKillSupply_iff_periodMultipleKillSupply :
    CofinalFullDepthKillSupply ↔ PeriodMultipleKillSupply := by
  constructor
  · intro hsupply d hd c
    obtain ⟨t, N, ht, hN, hkill⟩ := hsupply d hd c
    exact ⟨t, N, t * d, ht, hN, hkill⟩
  · intro hsupply d hd c
    obtain ⟨t, N, L, ht, hN, hkill⟩ := hsupply d hd c
    have hd' : 0 < t * d := Nat.mul_pos ht hd
    obtain ⟨s, hs, hkill'⟩ := exists_fullDepthKill_on_ray_of_seed hd' hkill
    refine ⟨s * t, N, Nat.mul_pos hs ht, hN, ?_⟩
    have : s * t * d = s * (t * d) := by ring
    rw [this]
    exact hkill'

/-- The full chain, in one statement: depth-locked cofinal supply is exactly
irrationality. -/
theorem cofinalFullDepthKillSupply_iff_irrational :
    CofinalFullDepthKillSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  cofinalFullDepthKillSupply_iff_periodMultipleKillSupply.trans
    periodMultipleKillSupply_iff_irrational

end ErdosProblems.Erdos249.FullDepthRayAmplifier
