import Erdos249257.LcmDiagonalReduction

/-!
# Wave 24: the lcm-cone flatness law and the annihilator calculus

Wave 23 collapsed #249 onto one decidable sequence: `P t := ∃ L,
certifiedKill (H_t, H_t, L)` with `H_t = lcm(1..t)`.  This file spends the
rationality hypothesis ALL the way.

**1. The cone flatness law.**  Rationality does not merely constrain the
diagonal pair `(H_t, 2H_t)`: it forces ONE fractional constant on the entire
lcm cone `{k·H_t : k ≥ 1}`.  Once `t ≥ h₀` and `q·H_t ≥ N₀`, every difference
`R_{(q+m)H_t} - R_{qH_t}` is an integer
(`rational_totient_series_forces_lcm_cone_flatness`).  Since
`periodLcm t ∣ periodLcm u` for `t ≤ u` (`periodLcm_dvd_periodLcm`), the
cones at all scales form one directed system: every cross-scale pair
`(q·H_t, r·H_u)` is a same-scale pair on the `t`-ray.  So the two-multiplier
form is the WHOLE lattice.

**2. The cone annihilator umbrella.**  One certified kill anywhere on the
cone — `(h, N) = (m·H_t, q·H_t)` at arbitrarily large `t` — contradicts
flatness and proves #249
(`irrational_totient_series_of_lcm_cone_certificate_supply`).  The wave-23
diagonal is the cell `q = m = 1`; q-ray steps are `m = 1`; q-gaps are free
`m`; prime-jump pairs `H_{t+1} - H_t` are `(q, m) = (1, p-1)`.  All the
advisory families are cells of this one theorem.

**3. Certificate completeness.**  The endpoint certificate is COMPLETE, not
just sound: some depth `L` certifies `(h, N)` IFF the tail difference
`R_{N+h} - R_N` is a non-integer
(`exists_certifiedKill_iff_tail_diff_notMem_int`).  Non-integrality is the
mathematical object; certificates are its finite receipts.  The frontier of
#249 in pure form: the diagonal (or any cone) tail differences are
non-integral at arbitrarily large scales
(`irrational_totient_series_of_lcm_diagonal_nonintegrality_supply`,
`…_of_lcm_cone_nonintegrality_supply`).

**4. Rank-2 second differences — sound, and measured NOT shallower.**
`certifiedRank2Kill` certifies `(R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N) ∉ ℤ`
with a doubled band radius (`second_diff_notMem_int_of_certifiedRank2Kill`);
on q-rays rationality forces both first differences integral, so rank-2 kills
also prove #249 (`irrational_totient_series_of_lcm_qray_rank2_supply`).  The
wave-24 probe measured the advisory-1 hope that cancelling the `H·C` shadow
makes kills easier: the cancellation is real (median `|D₂|/(H·C)` ≈ 0.15)
but rank-1 certifies at least as shallow in 30 of 40 cells (median depth
delta +1) — the certificate band scales with the position, not the shadow.
The verdict is kernel-checked at a fixture cell
(`rank2_kill_sound_but_not_shallower_at_cell`).

The supply hypotheses (`∀ t₀, ∃ t ≥ t₀, …`) remain the open content of #249
and are NOT claimed.  Everything here is elementary: lcm divisibility, the
tail-period law, geometric tails, and integer window arithmetic.
-/

set_option maxRecDepth 10000

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

/-! ## The scale ladder is a divisibility chain -/

/-- `lcm(1..t) ∣ lcm(1..u)` for `t ≤ u`: the cones at all scales fit into one
directed system, so every cross-scale pair `(q·H_t, r·H_u)` is a same-scale
pair on the `t`-ray. -/
lemma periodLcm_dvd_periodLcm {t u : ℕ} (htu : t ≤ u) :
    periodLcm t ∣ periodLcm u := by
  induction u with
  | zero =>
      have ht0 : t = 0 := Nat.le_zero.mp htu
      subst ht0
      exact dvd_rfl
  | succ u ih =>
      show periodLcm t ∣ Nat.lcm (periodLcm u) (u + 1)
      rcases Nat.lt_or_ge t (u + 1) with hlt | hge
      · exact (ih (by omega)).trans (Nat.dvd_lcm_left _ _)
      · have heq : t = u + 1 := by omega
        subst heq
        exact dvd_rfl

/-! ## The cone flatness law: rationality flattens the whole lcm cone -/

/-- **The lcm-cone flatness law.**  If the totient series is rational, then
from some scale on, the ENTIRE lcm cone is fractionally flat: every difference
`R_{q·H_t + m·H_t} - R_{q·H_t}` is an integer, for every `t` past the
threshold, every base multiplier `q ≥ 1`, and every step multiplier `m`.
One constant fractional part governs every cone point — the maximal spend of
the rationality hypothesis on the lcm lattice. -/
theorem rational_totient_series_forces_lcm_cone_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail (q * periodLcm t + m * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨h₀, hpos, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  refine ⟨max h₀ N₀, fun t ht q m hq => ?_⟩
  have hdvdH : h₀ ∣ periodLcm t := dvd_periodLcm hpos (le_trans (le_max_left _ _) ht)
  have hdvd : h₀ ∣ m * periodLcm t := hdvdH.mul_left m
  have hN : N₀ ≤ q * periodLcm t := by
    have h1 : N₀ ≤ t := le_trans (le_max_right _ _) ht
    have h2 : t ≤ periodLcm t := le_periodLcm t
    have h3 : periodLcm t ≤ q * periodLcm t := by
      calc periodLcm t = 1 * periodLcm t := (one_mul _).symm
        _ ≤ q * periodLcm t := Nat.mul_le_mul_right _ hq
    omega
  obtain ⟨c, hc⟩ := hdvd
  have hmem := tail_diff_mul_mem_int hint c (q * periodLcm t) hN
  have heq : c * h₀ = m * periodLcm t := by
    rw [hc]
    ring
  rwa [heq] at hmem

/-! ## The cone annihilator umbrella -/

/-- **The wave-24 cone collapse.**  #249 follows from certified kills anywhere
on the two-multiplier lcm cone: `(h, N) = (m·H_t, q·H_t)` at arbitrarily
large `t`.  Subsumes the wave-23 diagonal (`q = m = 1`), every q-ray step
(`m = 1`), every q-gap (free `m`), and — via `periodLcm_dvd_periodLcm` —
every cross-scale pair, since `H_u` is itself a multiple of `H_t` for
`u ≥ t`.  Rationality flattens the cone; one certified annihilator at
arbitrarily large scale is a contradiction. -/
theorem irrational_totient_series_of_lcm_cone_certificate_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
      certifiedKill (m * periodLcm t) (q * periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨t, ht, q, m, L, hq, hkill⟩ := hsupply t₁
  exact tail_diff_notMem_int_of_certifiedKill hkill (hflat t ht q m hq)

/-! ## Certificate completeness: kills exist exactly at non-integers -/

private lemma summable_linear_half' :
    Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
  simpa using summable_pow_mul_geometric_of_norm_lt_one 1
    (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)

private lemma summable_const_add_mul_half' (C : ℝ) :
    Summable (fun j : ℕ => (C + (j : ℝ)) * (1 / 2 : ℝ) ^ j) := by
  have h1 : Summable (fun j : ℕ => C * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  exact (h1.add summable_linear_half').congr fun j => by ring

private lemma exists_depth_lt (C δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℕ, (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L < δ := by
  have htend := (summable_const_add_mul_half' C).tendsto_atTop_zero
  have hev : ∀ᶠ L : ℕ in Filter.atTop, (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L ∈ Set.Iio δ :=
    htend.eventually_mem (Iio_mem_nhds hδ)
  obtain ⟨L, hL⟩ := hev.exists
  exact ⟨L, hL⟩

/-- **Certificate completeness (the converse of wave 21).**  If the tail
difference `R_{N+h} - R_N` is a non-integer, some finite depth certifies it:
its distance `δ` to the nearest integer is positive, and any window depth `L`
with `2·(N+h+L+2) < δ·2^L` places the residue outside the forbidden band. -/
theorem exists_certifiedKill_of_tail_diff_notMem_int {h N : ℕ}
    (hD : totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ L, certifiedKill h N L := by
  set D := totientTail (N + h) - totientTail N with hDdef
  -- floor and fractional gap without a FloorRing detour
  obtain ⟨g, hg⟩ := exists_floor D
  have hgle : (g : ℝ) ≤ D := (hg g).mp le_rfl
  have hglt : D < (g : ℝ) + 1 := by
    by_contra hle
    have hle' : (g : ℝ) + 1 ≤ D := not_lt.mp hle
    have h1 : ((g + 1 : ℤ) : ℝ) ≤ D := by push_cast; linarith
    have h2 : g + 1 ≤ g := (hg (g + 1)).mpr h1
    omega
  have hf0 : 0 < D - (g : ℝ) := by
    rcases eq_or_lt_of_le (show 0 ≤ D - (g : ℝ) by linarith) with heq | hlt
    · exfalso
      exact hD ⟨g, by linarith⟩
    · exact hlt
  have hf1 : D - (g : ℝ) < 1 := by linarith
  set δ := min (D - (g : ℝ)) (1 - (D - (g : ℝ))) with hδdef
  have hδ0 : 0 < δ := lt_min hf0 (by linarith)
  have hδlo : δ ≤ D - (g : ℝ) := min_le_left _ _
  have hδhi : δ ≤ 1 - (D - (g : ℝ)) := min_le_right _ _
  -- distance to every integer is at least δ
  have hdist : ∀ z : ℤ, δ ≤ |D - (z : ℝ)| := by
    intro z
    by_cases hz : z ≤ g
    · have hz' : (z : ℝ) ≤ (g : ℝ) := by exact_mod_cast hz
      have hlow : δ ≤ D - (z : ℝ) := by linarith
      exact hlow.trans (le_abs_self _)
    · have hz1 : g + 1 ≤ z := Int.lt_iff_add_one_le.mp (not_le.mp hz)
      have hz' : (g : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz1
      have hup : δ ≤ (z : ℝ) - D := by linarith
      calc δ ≤ (z : ℝ) - D := hup
        _ ≤ |(z : ℝ) - D| := le_abs_self _
        _ = |D - (z : ℝ)| := abs_sub_comm _ _
  -- choose the depth
  obtain ⟨L, hL⟩ := exists_depth_lt ((N : ℝ) + h + 2) (δ / 2) (by positivity)
  have hB2 : ((N : ℝ) + h + L + 2) / 2 ^ L < δ / 2 := by
    have hrw : ((N : ℝ) + h + L + 2) / 2 ^ L
        = ((N : ℝ) + (h : ℝ) + 2 + (L : ℝ)) * (1 / 2 : ℝ) ^ L := by
      rw [div_pow, one_pow]
      ring
    rw [hrw]
    exact hL
  -- window decomposition at depth L
  have hdec1 := totientTail_eq_partial_add_tail (N + h) L
  have hdec2 := totientTail_eq_partial_add_tail N L
  have hA := windowDiscrepancy_div_eq h N L
  have hT1n := tail_after_nonneg (N + h) L
  have hT2n := tail_after_nonneg N L
  have hT1u := tail_after_le (N + h) L
  have hT2u := tail_after_le N L
  push_cast at hT1u
  set A := windowDiscrepancy h N L with hAdef
  set T1 := ∑' j : ℕ, (Nat.totient (N + h + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT1def
  set T2 := ∑' j : ℕ, (Nat.totient (N + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT2def
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hDsum : D = (A : ℝ) / 2 ^ L + (T1 - T2) := by
    rw [hDdef, hdec1, hdec2, hA]
    ring
  have hmul : D * 2 ^ L = (A : ℝ) + (T1 - T2) * 2 ^ L := by
    rw [hDsum, add_mul, div_mul_cancel₀ _ h2L.ne']
  have hs1 : T1 * 2 ^ L ≤ (N : ℝ) + h + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT1u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hs2 : T2 * 2 ^ L ≤ (N : ℝ) + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT2u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hn1 : 0 ≤ T1 * 2 ^ L := mul_nonneg hT1n h2L.le
  have hn2 : 0 ≤ T2 * 2 ^ L := mul_nonneg hT2n h2L.le
  have habs2 : |(T1 - T2) * 2 ^ L| ≤ (N : ℝ) + h + L + 2 := by
    rw [sub_mul, abs_sub_le_iff]
    refine ⟨by linarith, ?_⟩
    have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    linarith
  set P : ℤ := 2 ^ L with hP
  have hPpos : (0 : ℤ) < P := by rw [hP]; positivity
  have hPreal : (P : ℝ) = 2 ^ L := by rw [hP]; push_cast; ring
  set r := A % P with hrdef
  set k' := A / P with hk'def
  have hdm : P * k' + r = A := Int.mul_ediv_add_emod A P
  have hr0 : (0 : ℤ) ≤ r := Int.emod_nonneg A hPpos.ne'
  have hrP : r < P := Int.emod_lt_of_pos A hPpos
  have hAreal : (A : ℝ) = (P : ℝ) * (k' : ℝ) + (r : ℝ) := by exact_mod_cast hdm.symm
  have hkey : (D - (k' : ℝ)) * 2 ^ L = (r : ℝ) + (T1 - T2) * 2 ^ L := by
    rw [sub_mul, hmul, hAreal, hPreal]
    ring
  have hbig : 2 * ((N : ℝ) + h + L + 2) < δ * 2 ^ L := by
    have hm := mul_lt_mul_of_pos_left hB2 (show (0 : ℝ) < 2 * 2 ^ L by positivity)
    have e1 : 2 * 2 ^ L * (((N : ℝ) + h + L + 2) / 2 ^ L) = 2 * ((N : ℝ) + h + L + 2) := by
      field_simp
    have e2 : 2 * 2 ^ L * (δ / 2) = δ * 2 ^ L := by ring
    rwa [e1, e2] at hm
  refine ⟨L, ?_, ?_⟩
  · -- lower band edge: (N+h+L+2 : ℤ) < r
    by_contra hcon
    have hle : r ≤ (N : ℤ) + h + L + 2 := not_lt.mp hcon
    have hrR : (r : ℝ) ≤ (N : ℝ) + h + L + 2 := by
      have h' : ((r : ℤ) : ℝ) ≤ (((N : ℤ) + h + L + 2 : ℤ) : ℝ) := Int.cast_le.mpr hle
      push_cast at h'
      linarith
    have habsm : |D - (k' : ℝ)| * 2 ^ L = |(D - (k' : ℝ)) * 2 ^ L| := by
      rw [abs_mul, abs_of_pos h2L]
    have hclose : |D - (k' : ℝ)| * 2 ^ L < δ * 2 ^ L := by
      rw [habsm, hkey]
      have hrw : (r : ℝ) + (T1 - T2) * 2 ^ L
          = (r : ℝ) - (-((T1 - T2) * 2 ^ L)) := by ring
      rw [hrw]
      calc |(r : ℝ) - (-((T1 - T2) * 2 ^ L))|
          ≤ |(r : ℝ)| + |(-((T1 - T2) * 2 ^ L))| := abs_sub _ _
        _ = |(r : ℝ)| + |(T1 - T2) * 2 ^ L| := by rw [abs_neg]
        _ ≤ (r : ℝ) + ((N : ℝ) + h + L + 2) := by
            have habsr : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg (by exact_mod_cast hr0)
            linarith [habs2]
        _ ≤ 2 * ((N : ℝ) + h + L + 2) := by linarith
        _ < δ * 2 ^ L := hbig
    have hlt : |D - (k' : ℝ)| < δ := lt_of_mul_lt_mul_right hclose h2L.le
    exact absurd (hdist k') (not_le.mpr hlt)
  · -- upper band edge: r < 2^L - (N+h+L+2 : ℤ)
    by_contra hcon
    have hle : P - ((N : ℤ) + h + L + 2) ≤ r := not_lt.mp hcon
    have hPrR : (P : ℝ) - (r : ℝ) ≤ (N : ℝ) + h + L + 2 := by
      have h' : ((P - ((N : ℤ) + h + L + 2) : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) :=
        Int.cast_le.mpr hle
      push_cast at h'
      linarith
    have hPr0 : (0 : ℝ) ≤ (P : ℝ) - (r : ℝ) := by
      have h' : ((r : ℤ) : ℝ) ≤ ((P : ℤ) : ℝ) := Int.cast_le.mpr hrP.le
      linarith
    have hkey2 : (D - ((k' : ℝ) + 1)) * 2 ^ L = ((r : ℝ) - (P : ℝ)) + (T1 - T2) * 2 ^ L := by
      have hstep : (D - ((k' : ℝ) + 1)) * 2 ^ L = (D - (k' : ℝ)) * 2 ^ L - 2 ^ L := by
        ring
      rw [hstep, hkey, ← hPreal]
      ring
    have habsm : |D - ((k' : ℝ) + 1)| * 2 ^ L = |(D - ((k' : ℝ) + 1)) * 2 ^ L| := by
      rw [abs_mul, abs_of_pos h2L]
    have hclose : |D - ((k' : ℝ) + 1)| * 2 ^ L < δ * 2 ^ L := by
      rw [habsm, hkey2]
      have hrw : ((r : ℝ) - (P : ℝ)) + (T1 - T2) * 2 ^ L
          = ((r : ℝ) - (P : ℝ)) - (-((T1 - T2) * 2 ^ L)) := by ring
      rw [hrw]
      calc |((r : ℝ) - (P : ℝ)) - (-((T1 - T2) * 2 ^ L))|
          ≤ |(r : ℝ) - (P : ℝ)| + |(-((T1 - T2) * 2 ^ L))| := abs_sub _ _
        _ = |(r : ℝ) - (P : ℝ)| + |(T1 - T2) * 2 ^ L| := by rw [abs_neg]
        _ ≤ ((P : ℝ) - (r : ℝ)) + ((N : ℝ) + h + L + 2) := by
            have habs_pr : |(r : ℝ) - (P : ℝ)| = (P : ℝ) - (r : ℝ) := by
              rw [abs_sub_comm]
              exact abs_of_nonneg hPr0
            linarith [habs2]
        _ ≤ 2 * ((N : ℝ) + h + L + 2) := by linarith
        _ < δ * 2 ^ L := hbig
    have hlt : |D - ((k' : ℝ) + 1)| < δ := lt_of_mul_lt_mul_right hclose h2L.le
    have hd := hdist (k' + 1)
    push_cast at hd
    exact absurd hd (not_le.mpr hlt)

/-- **Certificate completeness, iff form.**  Some depth certifies `(h, N)`
exactly when the tail difference is a non-integer.  Finite certificates are
receipts; non-integrality is the object. -/
theorem exists_certifiedKill_iff_tail_diff_notMem_int (h N : ℕ) :
    (∃ L, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) :=
  ⟨fun ⟨_, hkill⟩ => tail_diff_notMem_int_of_certifiedKill hkill,
    exists_certifiedKill_of_tail_diff_notMem_int⟩

/-! ## The exact irrationality normal form -/

/-- Integrality of one shifted tail difference is exactly integrality of the
corresponding integer multiple `2^N (2^h - 1) S` of the #249 constant.
This is the algebraic converse left implicit by the period-killer reduction. -/
theorem tail_diff_mem_int_iff_scaled_series_mem_int (h N : ℕ) :
    (totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ↔
    ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      ∈ Set.range ((↑) : ℤ → ℝ)) := by
  have h1 := two_pow_mul_totient_series_eq (N + h)
  have h2 := two_pow_mul_totient_series_eq N
  have hrel :
      (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        = ((totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) +
          (totientTail (N + h) - totientTail N) := by
    rw [show (2 : ℝ) ^ (N + h) = 2 ^ N * 2 ^ h by rw [pow_add]] at h1
    push_cast
    linarith
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨((totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ)) + z, ?_⟩
    rw [hrel, ← hz]
    push_cast
    ring
  · rintro ⟨z, hz⟩
    refine ⟨z - ((totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ)), ?_⟩
    rw [hrel] at hz
    push_cast at hz ⊢
    linarith

/-- One integral tail difference at a positive shift already makes the #249
constant rational.  Thus a perpetually trapped single pair is not merely a
failure of the certificate route: it resolves #249 in the opposite direction. -/
theorem not_irrational_of_tail_diff_mem_int {h N : ℕ} (hh : 0 < h)
    (hint : totientTail (N + h) - totientTail N ∈
      Set.range ((↑) : ℤ → ℝ)) :
    ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  obtain ⟨z, hz⟩ := (tail_diff_mem_int_iff_scaled_series_mem_int h N).mp hint
  intro hirr
  apply hirr
  let K : ℕ := 2 ^ N * (2 ^ h - 1)
  have hKpos : 0 < K := by
    dsimp [K]
    have hpow : 1 < 2 ^ h := one_lt_pow₀ (by omega) hh.ne'
    exact Nat.mul_pos (by positivity) (Nat.sub_pos_of_lt hpow)
  refine ⟨(z : ℚ) / K, ?_⟩
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  have hKreal : (K : ℝ) = (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) := by
    dsimp [K]
    rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow h 2 (by omega))]
    push_cast
    norm_num
  rw [hKreal]
  have hKrealpos : 0 < (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) := by
    rw [← hKreal]
    exact_mod_cast hKpos
  apply (div_eq_iff hKrealpos.ne').2
  rw [hz]
  ring

/-- #249 is equivalent to pointwise non-integrality of every positive shifted
tail difference. -/
theorem irrational_totient_series_iff_all_tail_diffs_nonintegral :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro hirr h hh N hint
    exact not_irrational_of_tail_diff_mem_int hh hint hirr
  · intro hnon
    refine irrational_totient_series_of_certificate_supply fun h hh N₀ => ?_
    exact ⟨N₀, le_rfl, exists_certifiedKill_of_tail_diff_notMem_int (hnon h hh N₀)⟩

/-- Certificate completeness turns the pointwise non-integrality normal form
into a pointwise finite-receipt normal form. -/
theorem irrational_totient_series_iff_pointwise_certificates :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ, ∃ L, certifiedKill h N L := by
  constructor
  · intro hirr h hh N
    exact exists_certifiedKill_of_tail_diff_notMem_int
      (irrational_totient_series_iff_all_tail_diffs_nonintegral.mp hirr h hh N)
  · intro hpoint
    exact irrational_totient_series_of_certificate_supply fun h hh N₀ =>
      ⟨N₀, le_rfl, hpoint h hh N₀⟩

/-- The wave-21 cofinal certificate supply is not a weaker large-measure
surrogate: together with completeness it is exactly equivalent to #249. -/
theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L := by
  constructor
  · intro hirr h hh N₀
    exact ⟨N₀, le_rfl,
      (irrational_totient_series_iff_pointwise_certificates.mp hirr) h hh N₀⟩
  · exact irrational_totient_series_of_certificate_supply

/-- The one-parameter lcm-diagonal certificate supply is an exact normal
form for #249, not only a sufficient criterion.  In the forward direction,
pointwise certificate completeness supplies the diagonal certificate already
at `t = t₀`; the reverse direction is the diagonal collapse. -/
theorem irrational_totient_series_iff_lcm_diagonal_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
        certifiedKill (periodLcm t) (periodLcm t) L := by
  constructor
  · intro hirr t₀
    refine ⟨t₀, le_rfl, ?_⟩
    exact (irrational_totient_series_iff_pointwise_certificates.mp hirr)
      (periodLcm t₀) (periodLcm_pos t₀) (periodLcm t₀)
  · exact irrational_totient_series_of_lcm_diagonal_certificate_supply

/-- The wave-23 predicate `P t` in pure form: a diagonal certificate depth
exists iff the diagonal tail difference is a non-integer. -/
theorem periodLcm_diagonal_kill_iff_tail_diff_notMem_int (t : ℕ) :
    (∃ L, certifiedKill (periodLcm t) (periodLcm t) L) ↔
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ) :=
  exists_certifiedKill_iff_tail_diff_notMem_int (periodLcm t) (periodLcm t)

/-! ## The frontier in pure form: non-integrality supply -/

/-- **The diagonal frontier without certificate vocabulary.**  If the
diagonal tail difference `R_{2H_t} - R_{H_t}` is a non-integer for
arbitrarily large `t`, the totient series is irrational.  (Completeness
converts each non-integrality into a finite decidable certificate.) -/
theorem irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_lcm_diagonal_certificate_supply fun t₀ => ?_
  obtain ⟨t, ht, hnon⟩ := hsupply t₀
  exact ⟨t, ht, exists_certifiedKill_of_tail_diff_notMem_int hnon⟩

/-- **The cone frontier in pure form**: one non-integral cone difference at
arbitrarily large scale proves #249 — no certificate vocabulary at all. -/
theorem irrational_totient_series_of_lcm_cone_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m : ℕ, 0 < q ∧
      totientTail (q * periodLcm t + m * periodLcm t) - totientTail (q * periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨t, ht, q, m, hq, hnon⟩ := hsupply t₁
  exact hnon (hflat t ht q m hq)

/-! ## Rank-2: the second-difference certificate -/

/-- Second-difference window discrepancy
`A₂ = A(h, N+h, L) - A(h, N, L)`: the depth-`L` truncation of
`2^L·((R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N))`. -/
def windowDiscrepancy2 (h N L : ℕ) : ℤ :=
  windowDiscrepancy h (N + h) L - windowDiscrepancy h N L

/-- The decidable rank-2 certificate: the residue of `A₂` modulo `2^L` avoids
the radius-`2(N+2h+L+2)` neighbourhood of `0`.  The doubled radius pays for
two window truncations; in exchange the second difference cancels the whole
`H·C` clean shadow on the lcm cone. -/
def certifiedRank2Kill (h N L : ℕ) : Prop :=
  (2 * ((N : ℤ) + 2 * h + L + 2)) < windowDiscrepancy2 h N L % 2 ^ L ∧
    windowDiscrepancy2 h N L % 2 ^ L < 2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)

instance (h N L : ℕ) : Decidable (certifiedRank2Kill h N L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Rank-2 soundness.**  A certified rank-2 residue proves the second
difference `(R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N)` is not an integer. -/
theorem second_diff_notMem_int_of_certifiedRank2Kill {h N L : ℕ}
    (hcert : certifiedRank2Kill h N L) :
    (totientTail (N + 2 * h) - totientTail (N + h))
        - (totientTail (N + h) - totientTail N) ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨k, hk⟩
  obtain ⟨hlow, hhigh⟩ := hcert
  rw [show N + 2 * h = N + h + h from by omega] at hk
  have hdecA := totientTail_eq_partial_add_tail (N + h + h) L
  have hdecB := totientTail_eq_partial_add_tail (N + h) L
  have hdecC := totientTail_eq_partial_add_tail N L
  have hAtop := windowDiscrepancy_div_eq h (N + h) L
  have hAbot := windowDiscrepancy_div_eq h N L
  have hTAn := tail_after_nonneg (N + h + h) L
  have hTBn := tail_after_nonneg (N + h) L
  have hTCn := tail_after_nonneg N L
  have hTAu := tail_after_le (N + h + h) L
  have hTBu := tail_after_le (N + h) L
  have hTCu := tail_after_le N L
  push_cast at hTAu hTBu
  set A2 := windowDiscrepancy2 h N L with hA2def
  set TA := ∑' j : ℕ, (Nat.totient (N + h + h + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
    with hTAdef
  set TB := ∑' j : ℕ, (Nat.totient (N + h + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
    with hTBdef
  set TC := ∑' j : ℕ, (Nat.totient (N + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
    with hTCdef
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hsplit : (A2 : ℝ) / 2 ^ L
      = ((windowDiscrepancy h (N + h) L : ℤ) : ℝ) / 2 ^ L
        - ((windowDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L := by
    rw [hA2def]
    unfold windowDiscrepancy2
    push_cast
    ring
  have hk' : ((k : ℤ) : ℝ) = (A2 : ℝ) / 2 ^ L + ((TA - TB) - (TB - TC)) := by
    rw [hk, hsplit, hAtop, hAbot, hdecA, hdecB, hdecC]
    ring
  have hsA : TA * 2 ^ L ≤ (N : ℝ) + h + h + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hTAu h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hsB : TB * 2 ^ L ≤ (N : ℝ) + h + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hTBu h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hsC : TC * 2 ^ L ≤ (N : ℝ) + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hTCu h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hnA : 0 ≤ TA * 2 ^ L := mul_nonneg hTAn h2L.le
  have hnB : 0 ≤ TB * 2 ^ L := mul_nonneg hTBn h2L.le
  have hnC : 0 ≤ TC * 2 ^ L := mul_nonneg hTCn h2L.le
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have habsAB : |(TA - TB) * 2 ^ L| ≤ (N : ℝ) + h + h + L + 2 := by
    rw [sub_mul, abs_sub_le_iff]
    refine ⟨by linarith, by linarith⟩
  have habsBC : |(TB - TC) * 2 ^ L| ≤ (N : ℝ) + h + L + 2 := by
    rw [sub_mul, abs_sub_le_iff]
    refine ⟨by linarith, by linarith⟩
  have habsτ : |((TA - TB) - (TB - TC)) * 2 ^ L| ≤ 2 * ((N : ℝ) + 2 * h + L + 2) := by
    have hexp : ((TA - TB) - (TB - TC)) * 2 ^ L
        = (TA - TB) * 2 ^ L - (TB - TC) * 2 ^ L := by ring
    rw [hexp]
    have htri : |(TA - TB) * 2 ^ L - (TB - TC) * 2 ^ L|
        ≤ |(TA - TB) * 2 ^ L| + |(TB - TC) * 2 ^ L| := abs_sub _ _
    linarith [htri, habsAB, habsBC]
  have hmulk : ((k : ℤ) : ℝ) * 2 ^ L = (A2 : ℝ) + ((TA - TB) - (TB - TC)) * 2 ^ L := by
    rw [hk', add_mul, div_mul_cancel₀ _ h2L.ne']
  have hAk : (A2 : ℝ) - ((k : ℤ) : ℝ) * 2 ^ L = -(((TA - TB) - (TB - TC)) * 2 ^ L) := by
    linarith [hmulk]
  have habs : |(A2 : ℝ) - ((k : ℤ) : ℝ) * 2 ^ L| ≤ 2 * ((N : ℝ) + 2 * h + L + 2) := by
    rw [hAk, abs_neg]
    exact habsτ
  have hint : |A2 - k * 2 ^ L| ≤ 2 * ((N : ℤ) + 2 * h + L + 2) := by exact_mod_cast habs
  set P : ℤ := 2 ^ L with hP
  have hPpos : (0 : ℤ) < P := by rw [hP]; positivity
  set x : ℤ := A2 - k * P with hx
  have hxmod : x % P = A2 % P := by
    have hrw : x = A2 + P * (-k) := by rw [hx]; ring
    rw [hrw, Int.add_mul_emod_self_left]
  have hdm : P * (x / P) + A2 % P = x := by
    rw [← hxmod]
    exact Int.mul_ediv_add_emod x P
  have habs' := abs_le.mp hint
  by_cases ht : 0 ≤ x / P
  · have hge : 0 ≤ P * (x / P) := mul_nonneg hPpos.le ht
    linarith [hlow, habs'.2, hdm, hge]
  · have ht1 : x / P ≤ -1 := by
      have h0 : x / P < 0 := not_le.mp ht
      linarith [Int.lt_iff_add_one_le.mp h0]
    have hle : P * (x / P) ≤ P * (-1) := mul_le_mul_of_nonneg_left ht1 hPpos.le
    linarith [hhigh, habs'.1, hdm, hle]

/-- **Rank-2 cone supply.**  Certified second-difference kills along the
q-rays of the lcm cone — `(h, N) = (H_t, q·H_t)` — at arbitrarily large `t`
prove #249: rationality flattens the cone, so BOTH first differences are
forced integral and their difference is an integer. -/
theorem irrational_totient_series_of_lcm_qray_rank2_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q L : ℕ, 0 < q ∧
      certifiedRank2Kill (periodLcm t) (q * periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨t, ht, q, L, hq, hkill⟩ := hsupply t₁
  obtain ⟨a, ha⟩ := hflat t ht q 1 hq
  obtain ⟨b, hb⟩ := hflat t ht (q + 1) 1 (by omega)
  rw [show q * periodLcm t + 1 * periodLcm t = q * periodLcm t + periodLcm t from by
    ring] at ha
  rw [show (q + 1) * periodLcm t + 1 * periodLcm t = q * periodLcm t + 2 * periodLcm t
      from by ring,
    show (q + 1) * periodLcm t = q * periodLcm t + periodLcm t from by ring] at hb
  refine second_diff_notMem_int_of_certifiedRank2Kill hkill ⟨b - a, ?_⟩
  push_cast
  linarith [ha, hb]

/-! ## Kernel-decided deposits: the measured verdicts, machine-checked -/

/-- Cone-lattice deposits beyond the diagonal: kills at
`(h, N) = (m·H_t, q·H_t)` for `(t, q, m) = (2, 3, 1)`, `(3, 2, 2)`,
`(3, 1, 3)` — the first machine-checked annihilators off the diagonal,
witnessing the cone supply shape at its probe-tabulated depths. -/
theorem certifiedKill_lcm_cone_cells :
    certifiedKill (1 * periodLcm 2) (3 * periodLcm 2) 6
      ∧ certifiedKill (2 * periodLcm 3) (2 * periodLcm 3) 7
      ∧ certifiedKill (3 * periodLcm 3) (1 * periodLcm 3) 8 := by decide

/-- A machine-checked rank-2 kill: the second difference at `(h, N) = (1, 8)`
is certified non-integral at depth `9` (totient arguments ≤ 19). -/
theorem certifiedRank2Kill_example : certifiedRank2Kill 1 8 9 := by decide

/-- **The measured wave-24 verdict, kernel-checked at the fixture cell**:
rank-2 is SOUND but NOT shallower.  At `(h, N) = (1, 8)` the rank-1
certificate fires at depth `8` while no rank-2 certificate exists at any
depth `≤ 8`.  (Probe, `t ≤ 20`: rank-1 at least as shallow in 30 of 40
cells, median depth delta `+1` against rank-2 — the advisory-1 promotion
gate is measured and denied.) -/
theorem rank2_kill_sound_but_not_shallower_at_cell :
    certifiedKill 1 8 8
      ∧ (∀ L ∈ Finset.Icc 1 8, ¬ certifiedRank2Kill 1 8 L)
      ∧ certifiedRank2Kill 1 8 9 := by decide

/-- Concrete rank-2 non-integrality: `(R₁₀ - R₉) - (R₉ - R₈)` is not an
integer — the first machine-checked second-difference obstruction. -/
theorem second_diff_not_int_example :
    (totientTail (8 + 2 * 1) - totientTail (8 + 1))
        - (totientTail (8 + 1) - totientTail 8) ∉ Set.range ((↑) : ℤ → ℝ) :=
  second_diff_notMem_int_of_certifiedRank2Kill certifiedRank2Kill_example

/-- The diagonal tail differences at `t = 7` and `t = 8` are non-integers —
extending the wave-23 corollary past its `t ≤ 6` decide ceiling via the
`_at_seven` / `_at_eight` deposits. -/
theorem tail_diff_not_int_periodLcm_diagonal_seven_eight :
    (totientTail (periodLcm 7 + periodLcm 7) - totientTail (periodLcm 7)
        ∉ Set.range ((↑) : ℤ → ℝ))
      ∧ (totientTail (periodLcm 8 + periodLcm 8) - totientTail (periodLcm 8)
        ∉ Set.range ((↑) : ℤ → ℝ)) :=
  ⟨tail_diff_notMem_int_of_certifiedKill certifiedKill_periodLcm_diagonal_at_seven,
    tail_diff_notMem_int_of_certifiedKill certifiedKill_periodLcm_diagonal_at_eight⟩

end TotientTailPeriodKiller
end Erdos249257
