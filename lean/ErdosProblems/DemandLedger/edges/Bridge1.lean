import ErdosProblems.DemandLedger.Basic

/-!
# Bridge set 1: the survivor / rank-2 vocabulary meets the `certifiedKill` cluster

Left set (all phrased with the endpoint certificate `certifiedKill`):

* `G082` — `∀ h₀ > 0, ∀ N₀, ∃ m > 0, ∃ N ≥ N₀, ∃ L, certifiedKill (m*h₀) N L`
* `G096` — `∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (H (t+1) - H t) (H t) L`
* `G097` — `∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (H t) (H t) L`
* `G100` — `∀ t₀, ∃ t ≥ t₀, ∃ q m L, 0 < q ∧ certifiedKill (m*H t) (q*H t) L`
* `G103` — `∀ t₀ N₀, ∃ t ≥ t₀, ∃ N ≥ N₀, ∃ L, certifiedKill (H t) N L`

Right set (a *different* certificate vocabulary each):

* `G081` — `∀ h₀ > 0, ∀ N₀, ∃ m > 0, ∃ N ≥ N₀, ∃ K, survivorKill (m*h₀) N K`
* `G102` — `∀ t₀ N₀, ∃ t ≥ t₀, ∃ N ≥ N₀, ∃ K, survivorKill (H t) N K`
* `G094` — `∀ t₀, ∃ t ≥ t₀, ∃ K, survivorKill (H t) (H t) K`
* `G099` — `∀ t₀, ∃ t ≥ t₀, ∃ q L, 0 < q ∧ certifiedRank2Kill (H t) (q*H t) L`

where `H t = periodLcm t = lcm(1..t)`.  `survivorKill h N K` is the bounded-orbit
certificate (every integer candidate in the initial box escapes the linear strip
within `K` doubling steps); `certifiedRank2Kill h N L` is the *second*-difference
residue certificate.  Neither mentions `certifiedKill`.

**Result: the two sets collapse into each other.  All 40 ordered cross pairs are
edges — 20 in each direction — so all nine gaps are mutually equivalent, and each
is equivalent to Erdős #249 itself.**

The Right → Left direction rests on two facts:

1. every Right statement is a corpus supply theorem for #249, so it implies
   `Irrational S`;
2. `certifiedKill` is *complete* — `∃ L, certifiedKill h N L` iff
   `R_{N+h} - R_N ∉ ℤ` — and irrationality of `S` makes every window with `h > 0`
   non-integral at once (one integral window with `h > 0` rearranges into
   `2^N(2^h-1)·S ∈ ℤ`, i.e. `S` rational).

The Left → Right direction needed two completeness theorems that the corpus does
*not* contain — it has soundness for both species and no converse for either.
Both are proved here:

* `existsCertifiedRank2Kill_of_second_diff_notMem_int` — rank-2 completeness.  The
  three truncations contribute a deep-tail error `T₂ - 2T₁ + T₀` bounded by
  `2(N+2h+L+2)/2^L`, which is exactly the doubled radius `certifiedRank2Kill`
  already charges, so the same depth-choice argument as rank 1 goes through.
* `existsSurvivorKill_of_tail_diff_notMem_int` — survivor completeness.  The new
  ingredient is `carryOrbit_eq_shift`: for an arbitrary integer launch value `d`,
  `orbit i = 2^i·(d - D_h(N)) + D_h(N+i)`.  The corpus only had the case
  `d = D_h(N)`, where the displacement vanishes.  Once the displacement is
  visible, a non-integral `D_h(N)` gives every candidate a nonzero gap that
  doubles while the strip widens only linearly, so each escapes; the step budget
  is the sup over the finitely many candidates.

Four of the Right → Left edges are additionally proved **directly**, cell by cell, with no
detour through irrationality; these are the honest vocabulary bridges, since they
exhibit the same lattice cell `(h, N)` carrying both certificate species:

* `e_G081_G082_direct`, `e_G102_G103_direct`, `e_G094_G097_direct` — survivor
  soundness (`tail_diff_notMem_int_of_survivorKill`) followed by certificate
  completeness converts a survivor receipt into an endpoint receipt *at the same
  cell*.  So `survivorKill h N K → ∃ L, certifiedKill h N L` pointwise: the
  survivor lane is a refinement of the endpoint lane, never an alternative to it.
* `e_G099_G100_direct` — a rank-2 kill at `(H t, q·H t)` says the *second*
  difference is non-integral, hence at least one of the two consecutive first
  differences is; each is a cone cell (`(q, 1)` or `(q+1, 1)`), so the rank-2
  q-ray lands inside the wave-24 cone supply after a two-way case split.

The practical reading: `survivorKill`, `certifiedRank2Kill` and `certifiedKill` are
three receipt formats for one and the same fact, `R_{N+h} - R_N ∉ ℤ`.  Choosing
between them is an engineering decision about certificate depth, not a choice of
research programme, and a frontier record for one of these nine gaps is a frontier
record for all nine.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace DemandLedger.Bridge1

namespace Bridge1

/-! ## Infrastructure -/

/-- **The necessity bridge.**  If `S = ∑ φ(n)/2ⁿ` is irrational then no tail
difference with a positive window is an integer: by the shift identity
`2^N·S = Φ_N + R_N`, an integral `R_{N+h} - R_N` rearranges into
`2^N(2^h-1)·S ∈ ℤ`, exhibiting `S` as a rational. -/
theorem tailDiff_notMem_int_of_irr {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨d, hd⟩
  have h1 := two_pow_mul_totient_series_eq (N + h)
  have h2 := two_pow_mul_totient_series_eq N
  have hnat : (2 : ℕ) ^ 1 ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hlt : (1 : ℝ) < (2 : ℝ) ^ h := by
    have hc : ((2 ^ 1 : ℕ) : ℝ) ≤ ((2 ^ h : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at hc
    linarith
  have h2N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hden : ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1)) ≠ 0 :=
    ne_of_gt (mul_pos h2N (by linarith))
  have hkey : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = ((d + (totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℝ) := by
    have expand : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        = (2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
          - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
      rw [pow_add]; ring
    rw [expand, h1, h2]
    push_cast
    linarith
  refine hirr ⟨((d + (totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℚ)
      / ((2 : ℚ) ^ N * ((2 : ℚ) ^ h - 1)), ?_⟩
  push_cast
  rw [div_eq_iff hden]
  push_cast at hkey
  linear_combination -hkey

/-- Irrationality supplies a firing endpoint certificate at every cell with a
positive window: the necessity bridge plus certificate completeness. -/
theorem existsCertifiedKill_of_irr {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ L, certifiedKill h N L :=
  exists_certifiedKill_of_tail_diff_notMem_int (tailDiff_notMem_int_of_irr hh hirr)

/-- The lcm ladder climbs infinitely often: `H t < H (t+1)` for arbitrarily large
`t`.  Otherwise `H` would be eventually constant, contradicting `t ≤ H t`. -/
theorem existsStrictJump (t₀ : ℕ) :
    ∃ t, t₀ ≤ t ∧ periodLcm t < periodLcm (t + 1) := by
  by_contra hcon
  have hcon' : ∀ t, t₀ ≤ t → periodLcm (t + 1) ≤ periodLcm t := fun t ht =>
    not_lt.mp fun hlt => hcon ⟨t, ht, hlt⟩
  have hconst : ∀ k, periodLcm (t₀ + k) = periodLcm t₀ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hle := hcon' (t₀ + k) (Nat.le_add_right _ _)
        have hdvd := periodLcm_dvd_succ (t₀ + k)
        have hge : periodLcm (t₀ + k) ≤ periodLcm (t₀ + k + 1) :=
          Nat.le_of_dvd (periodLcm_pos _) hdvd
        have heq : periodLcm (t₀ + k + 1) = periodLcm (t₀ + k) := le_antisymm hle hge
        rw [show t₀ + (k + 1) = t₀ + k + 1 from rfl, heq, ih]
  have hbig := le_periodLcm (t₀ + (periodLcm t₀ + 1))
  rw [hconst] at hbig
  omega

/-! ## Each Right gap implies #249 (the corpus supply theorems) -/

theorem irr_of_G081 (h : G081) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G081 at h
  exact Erdos249257.irrational_totient_series_of_multiple_period_kill_supply h

theorem irr_of_G102 (h : G102) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G102 at h
  exact Erdos249257.irrational_totient_series_of_lcm_period_kill_supply h

theorem irr_of_G094 (h : G094) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G094 at h
  exact irrational_totient_series_of_lcm_diagonal_survivor_supply h

theorem irr_of_G099 (h : G099) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G099 at h
  exact irrational_totient_series_of_lcm_qray_rank2_supply h

/-! ## #249 implies each Left gap -/

theorem G082_of_irr (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G082 := by
  unfold G082
  intro h₀ hpos N₀
  exact ⟨1, Nat.one_pos, N₀, le_rfl, existsCertifiedKill_of_irr (by simpa using hpos) hirr⟩

theorem G096_of_irr (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G096 := by
  unfold G096
  intro t₀
  obtain ⟨t, ht, hjump⟩ := existsStrictJump t₀
  exact ⟨t, ht, existsCertifiedKill_of_irr (Nat.sub_pos_of_lt hjump) hirr⟩

theorem G097_of_irr (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G097 := by
  unfold G097
  intro t₀
  exact ⟨t₀, le_rfl, existsCertifiedKill_of_irr (periodLcm_pos t₀) hirr⟩

theorem G100_of_irr (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G100 := by
  unfold G100
  intro t₀
  obtain ⟨L, hL⟩ := existsCertifiedKill_of_irr
    (h := 1 * periodLcm t₀) (N := 1 * periodLcm t₀) (by simpa using periodLcm_pos t₀) hirr
  exact ⟨t₀, le_rfl, 1, 1, L, Nat.one_pos, hL⟩

theorem G103_of_irr (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G103 := by
  unfold G103
  intro t₀ N₀
  exact ⟨t₀, le_rfl, N₀, le_rfl, existsCertifiedKill_of_irr (periodLcm_pos t₀) hirr⟩

/-! ## Rank-2 completeness

The corpus has rank-2 *soundness* (`second_diff_notMem_int_of_certifiedRank2Kill`)
but no converse.  The converse is proved here; it is what turns the rank-2 q-ray
supply `G099` from a sufficient criterion into an exact normal form for #249. -/

private lemma summableLinearHalf : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
  simpa using summable_pow_mul_geometric_of_norm_lt_one 1
    (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)

private lemma summableConstAddMulHalf (C : ℝ) :
    Summable (fun j : ℕ => (C + (j : ℝ)) * (1 / 2 : ℝ) ^ j) := by
  have h1 : Summable (fun j : ℕ => C * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  exact (h1.add summableLinearHalf).congr fun j => by ring

/-- Depths are cofinal against any linear-over-geometric threshold. -/
theorem existsDepthLt (C δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℕ, (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L < δ := by
  have htend := (summableConstAddMulHalf C).tendsto_atTop_zero
  have hev : ∀ᶠ L : ℕ in Filter.atTop, (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L ∈ Set.Iio δ :=
    htend.eventually_mem (Iio_mem_nhds hδ)
  obtain ⟨L, hL⟩ := hev.exists
  exact ⟨L, hL⟩

/-- **Rank-2 certificate completeness.**  If the second difference
`(R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N)` is a non-integer then some finite depth
certifies it.  Three truncations contribute the deep-tail error `T₂ - 2T₁ + T₀`,
whose modulus is at most `2(N+2h+L+2)/2^L` — *exactly* the doubled radius that
`certifiedRank2Kill` charges — so any depth `L` with `4(N+2h+L+2) < δ·2^L`, where
`δ` is the distance from the second difference to the nearest integer, places the
residue of `A₂` outside the forbidden band. -/
theorem existsCertifiedRank2Kill_of_second_diff_notMem_int {h N : ℕ}
    (hD2 : (totientTail (N + 2 * h) - totientTail (N + h))
        - (totientTail (N + h) - totientTail N) ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ L, certifiedRank2Kill h N L := by
  rw [show N + 2 * h = N + h + h from by omega] at hD2
  set D := (totientTail (N + h + h) - totientTail (N + h))
      - (totientTail (N + h) - totientTail N) with hDdef
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
      exact hD2 ⟨g, by linarith⟩
    · exact hlt
  have hf1 : D - (g : ℝ) < 1 := by linarith
  set δ := min (D - (g : ℝ)) (1 - (D - (g : ℝ))) with hδdef
  have hδ0 : 0 < δ := lt_min hf0 (by linarith)
  have hδlo : δ ≤ D - (g : ℝ) := min_le_left _ _
  have hδhi : δ ≤ 1 - (D - (g : ℝ)) := min_le_right _ _
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
  obtain ⟨L, hL⟩ := existsDepthLt ((N : ℝ) + 2 * (h : ℝ) + 2) (δ / 4) (by positivity)
  have hB2 : ((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2) / 2 ^ L < δ / 4 := by
    have hrw : ((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2) / 2 ^ L
        = ((N : ℝ) + 2 * (h : ℝ) + 2 + (L : ℝ)) * (1 / 2 : ℝ) ^ L := by
      rw [div_pow, one_pow]
      ring
    rw [hrw]
    exact hL
  refine ⟨L, ?_⟩
  have hdec2 := totientTail_eq_partial_add_tail (N + h + h) L
  have hdec1 := totientTail_eq_partial_add_tail (N + h) L
  have hdec0 := totientTail_eq_partial_add_tail N L
  have hAtop := windowDiscrepancy_div_eq h (N + h) L
  have hAbot := windowDiscrepancy_div_eq h N L
  have hA2 : ((windowDiscrepancy2 h N L : ℤ) : ℝ) / 2 ^ L
      = ((windowDiscrepancy h (N + h) L : ℤ) : ℝ) / 2 ^ L
        - ((windowDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L := by
    unfold windowDiscrepancy2
    push_cast
    ring
  have hT2n := tail_after_nonneg (N + h + h) L
  have hT1n := tail_after_nonneg (N + h) L
  have hT0n := tail_after_nonneg N L
  have hT2u := tail_after_le (N + h + h) L
  have hT1u := tail_after_le (N + h) L
  have hT0u := tail_after_le N L
  push_cast at hT2u hT1u
  set A := windowDiscrepancy2 h N L with hAdef
  set T2 := ∑' j : ℕ, (Nat.totient (N + h + h + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
    with hT2def
  set T1 := ∑' j : ℕ, (Nat.totient (N + h + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
    with hT1def
  set T0 := ∑' j : ℕ, (Nat.totient (N + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
    with hT0def
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hDsum : D = (A : ℝ) / 2 ^ L + (T2 - 2 * T1 + T0) := by
    rw [hDdef, hdec2, hdec1, hdec0, hA2, hAtop, hAbot]
    ring
  have hmul : D * 2 ^ L = (A : ℝ) + (T2 - 2 * T1 + T0) * 2 ^ L := by
    rw [hDsum, add_mul, div_mul_cancel₀ _ h2L.ne']
  have hs2 : T2 * 2 ^ L ≤ (N : ℝ) + (h : ℝ) + (h : ℝ) + (L : ℝ) + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT2u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hs1 : T1 * 2 ^ L ≤ (N : ℝ) + (h : ℝ) + (L : ℝ) + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT1u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hs0 : T0 * 2 ^ L ≤ (N : ℝ) + (L : ℝ) + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT0u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hn2 : 0 ≤ T2 * 2 ^ L := mul_nonneg hT2n h2L.le
  have hn1 : 0 ≤ T1 * 2 ^ L := mul_nonneg hT1n h2L.le
  have hn0 : 0 ≤ T0 * 2 ^ L := mul_nonneg hT0n h2L.le
  have hhn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hexpand : (T2 - 2 * T1 + T0) * 2 ^ L
      = T2 * 2 ^ L - 2 * (T1 * 2 ^ L) + T0 * 2 ^ L := by ring
  have habs2 : |(T2 - 2 * T1 + T0) * 2 ^ L|
      ≤ 2 * ((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2) := by
    rw [hexpand, abs_le]
    exact ⟨by linarith, by linarith⟩
  set P : ℤ := 2 ^ L with hP
  have hPpos : (0 : ℤ) < P := by rw [hP]; positivity
  have hPreal : (P : ℝ) = 2 ^ L := by rw [hP]; push_cast; ring
  set r := A % P with hrdef
  set k' := A / P with hk'def
  have hdm : P * k' + r = A := Int.mul_ediv_add_emod A P
  have hr0 : (0 : ℤ) ≤ r := Int.emod_nonneg A hPpos.ne'
  have hrP : r < P := Int.emod_lt_of_pos A hPpos
  have hAreal : (A : ℝ) = (P : ℝ) * (k' : ℝ) + (r : ℝ) := by exact_mod_cast hdm.symm
  have hkey : (D - (k' : ℝ)) * 2 ^ L = (r : ℝ) + (T2 - 2 * T1 + T0) * 2 ^ L := by
    rw [sub_mul, hmul, hAreal, hPreal]
    ring
  have hbig : 2 * (2 * ((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2)) < δ * 2 ^ L := by
    have hm := mul_lt_mul_of_pos_left hB2 (show (0 : ℝ) < 4 * 2 ^ L by positivity)
    have e1 : 4 * 2 ^ L * (((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2) / 2 ^ L)
        = 4 * ((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2) := by
      field_simp
    have e2 : 4 * 2 ^ L * (δ / 4) = δ * 2 ^ L := by ring
    rw [e1, e2] at hm
    linarith
  refine ⟨?_, ?_⟩
  · -- lower band edge
    by_contra hcon
    have hle : r ≤ 2 * ((N : ℤ) + 2 * (h : ℤ) + (L : ℤ) + 2) := not_lt.mp hcon
    have hrR : (r : ℝ) ≤ 2 * ((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2) := by
      have h' : ((r : ℤ) : ℝ)
          ≤ ((2 * ((N : ℤ) + 2 * (h : ℤ) + (L : ℤ) + 2) : ℤ) : ℝ) := Int.cast_le.mpr hle
      push_cast at h'
      linarith
    have habsm : |D - (k' : ℝ)| * 2 ^ L = |(D - (k' : ℝ)) * 2 ^ L| := by
      rw [abs_mul, abs_of_pos h2L]
    have hclose : |D - (k' : ℝ)| * 2 ^ L < δ * 2 ^ L := by
      rw [habsm, hkey]
      have hrw : (r : ℝ) + (T2 - 2 * T1 + T0) * 2 ^ L
          = (r : ℝ) - (-((T2 - 2 * T1 + T0) * 2 ^ L)) := by ring
      rw [hrw]
      calc |(r : ℝ) - (-((T2 - 2 * T1 + T0) * 2 ^ L))|
          ≤ |(r : ℝ)| + |(-((T2 - 2 * T1 + T0) * 2 ^ L))| := abs_sub _ _
        _ = |(r : ℝ)| + |(T2 - 2 * T1 + T0) * 2 ^ L| := by rw [abs_neg]
        _ ≤ 2 * (2 * ((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2)) := by
            have habsr : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg (by exact_mod_cast hr0)
            linarith [habs2]
        _ < δ * 2 ^ L := hbig
    have hlt : |D - (k' : ℝ)| < δ := lt_of_mul_lt_mul_right hclose h2L.le
    exact absurd (hdist k') (not_le.mpr hlt)
  · -- upper band edge
    by_contra hcon
    have hle : P - 2 * ((N : ℤ) + 2 * (h : ℤ) + (L : ℤ) + 2) ≤ r := not_lt.mp hcon
    have hPrR : (P : ℝ) - (r : ℝ) ≤ 2 * ((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2) := by
      have h' : ((P - 2 * ((N : ℤ) + 2 * (h : ℤ) + (L : ℤ) + 2) : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) :=
        Int.cast_le.mpr hle
      push_cast at h'
      linarith
    have hPr0 : (0 : ℝ) ≤ (P : ℝ) - (r : ℝ) := by
      have h' : ((r : ℤ) : ℝ) ≤ ((P : ℤ) : ℝ) := Int.cast_le.mpr hrP.le
      linarith
    have hkey2 : (D - ((k' : ℝ) + 1)) * 2 ^ L
        = ((r : ℝ) - (P : ℝ)) + (T2 - 2 * T1 + T0) * 2 ^ L := by
      have hstep : (D - ((k' : ℝ) + 1)) * 2 ^ L = (D - (k' : ℝ)) * 2 ^ L - 2 ^ L := by
        ring
      rw [hstep, hkey, ← hPreal]
      ring
    have habsm : |D - ((k' : ℝ) + 1)| * 2 ^ L = |(D - ((k' : ℝ) + 1)) * 2 ^ L| := by
      rw [abs_mul, abs_of_pos h2L]
    have hclose : |D - ((k' : ℝ) + 1)| * 2 ^ L < δ * 2 ^ L := by
      rw [habsm, hkey2]
      have hrw : ((r : ℝ) - (P : ℝ)) + (T2 - 2 * T1 + T0) * 2 ^ L
          = ((r : ℝ) - (P : ℝ)) - (-((T2 - 2 * T1 + T0) * 2 ^ L)) := by ring
      rw [hrw]
      calc |((r : ℝ) - (P : ℝ)) - (-((T2 - 2 * T1 + T0) * 2 ^ L))|
          ≤ |(r : ℝ) - (P : ℝ)| + |(-((T2 - 2 * T1 + T0) * 2 ^ L))| := abs_sub _ _
        _ = |(r : ℝ) - (P : ℝ)| + |(T2 - 2 * T1 + T0) * 2 ^ L| := by rw [abs_neg]
        _ ≤ 2 * (2 * ((N : ℝ) + 2 * (h : ℝ) + (L : ℝ) + 2)) := by
            have habs_pr : |(r : ℝ) - (P : ℝ)| = (P : ℝ) - (r : ℝ) := by
              rw [abs_sub_comm]
              exact abs_of_nonneg hPr0
            linarith [habs2]
        _ < δ * 2 ^ L := hbig
    have hlt : |D - ((k' : ℝ) + 1)| < δ := lt_of_mul_lt_mul_right hclose h2L.le
    have hd := hdist (k' + 1)
    push_cast at hd
    exact absurd hd (not_le.mpr hlt)

/-- Irrationality makes every rank-2 cell with a positive window non-integral:
`(R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N) = 2^N(2^h-1)²·S - (integer)`, and the
coefficient `2^N(2^h-1)²` is a nonzero rational for `h > 0`. -/
theorem secondDiff_notMem_int_of_irr {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    (totientTail (N + 2 * h) - totientTail (N + h))
      - (totientTail (N + h) - totientTail N) ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨d, hd⟩
  have hE2 := two_pow_mul_totient_series_eq (N + 2 * h)
  have hE1 := two_pow_mul_totient_series_eq (N + h)
  have hE0 := two_pow_mul_totient_series_eq N
  have hnat : (2 : ℕ) ^ 1 ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hlt : (1 : ℝ) < (2 : ℝ) ^ h := by
    have hc : ((2 ^ 1 : ℕ) : ℝ) ≤ ((2 ^ h : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at hc
    linarith
  have h2N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hden : ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) ^ 2) ≠ 0 :=
    ne_of_gt (mul_pos h2N (pow_pos (by linarith) 2))
  have e2h : (2 : ℝ) ^ (N + 2 * h) = (2 : ℝ) ^ N * ((2 : ℝ) ^ h) ^ 2 := by
    have hrw : N + 2 * h = N + h + h := by omega
    rw [hrw, pow_add, pow_add]
    ring
  have hkey : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) ^ 2
        * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = ((d + (totientPrefix (N + 2 * h) : ℤ) - 2 * (totientPrefix (N + h) : ℤ)
            + (totientPrefix N : ℤ) : ℤ) : ℝ) := by
    have expand : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) ^ 2
          * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        = (2 : ℝ) ^ (N + 2 * h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
          - 2 * ((2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
          + (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
      rw [e2h, pow_add]
      ring
    rw [expand, hE2, hE1, hE0]
    push_cast
    linarith
  refine hirr ⟨((d + (totientPrefix (N + 2 * h) : ℤ) - 2 * (totientPrefix (N + h) : ℤ)
      + (totientPrefix N : ℤ) : ℤ) : ℚ) / ((2 : ℚ) ^ N * ((2 : ℚ) ^ h - 1) ^ 2), ?_⟩
  push_cast
  rw [div_eq_iff hden]
  push_cast at hkey
  linear_combination -hkey

theorem G099_of_irr (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G099 := by
  unfold G099
  intro t₀
  obtain ⟨L, hL⟩ := existsCertifiedRank2Kill_of_second_diff_notMem_int
    (h := periodLcm t₀) (N := 1 * periodLcm t₀)
    (secondDiff_notMem_int_of_irr (periodLcm_pos t₀) hirr)
  exact ⟨t₀, le_rfl, 1, L, Nat.one_pos, hL⟩

/-! ## Survivor completeness

Again the corpus has only soundness (`tail_diff_notMem_int_of_survivorKill`).
The converse below is what turns the three survivor gaps into normal forms. -/

/-- **Orbit displacement.**  For an *arbitrary* integer launch value `d` the carry
orbit is the true tail-difference sequence displaced by a pure doubling term:
`orbit i = 2^i·(d - D_h(N)) + D_h(N+i)`.  The corpus lemma
`carryOrbit_eq_tail_diff` is the special case `d = D_h(N)`, where the displacement
vanishes; this is the general law that makes every *other* candidate escape. -/
theorem carryOrbit_eq_shift (h N : ℕ) (d : ℤ) (i : ℕ) :
    (carryOrbit h N d i : ℝ)
      = 2 ^ i * ((d : ℝ) - (totientTail (N + h) - totientTail N))
        + (totientTail (N + i + h) - totientTail (N + i)) := by
  induction i with
  | zero =>
      have h0 : carryOrbit h N d 0 = d := rfl
      rw [h0, Nat.add_zero]
      ring
  | succ i ih =>
      have hrec := tail_diff_succ h (N + i)
      have hstep : carryOrbit h N d (i + 1)
          = 2 * carryOrbit h N d i - deltaTotient h (N + i + 1) := rfl
      rw [hstep]
      push_cast
      rw [ih, show N + (i + 1) + h = N + i + 1 + h from by omega,
        show N + (i + 1) = N + i + 1 from by omega, hrec]
      ring

/-- **Survivor completeness.**  If the tail difference is a non-integer then some
finite step budget kills every candidate.  The displacement law makes the gap
`|d - D_h(N)|` double at every step while the strip only widens linearly, so each
of the finitely many integer candidates escapes; the budget is the sup. -/
theorem existsSurvivorKill_of_tail_diff_notMem_int {h N : ℕ}
    (hD : totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ K, survivorKill h N K := by
  have hstep : ∀ j : ℕ, ∃ i : ℕ,
      carryOrbit h N ((j : ℤ) - (N + h + 1)) i ≤ -(N + i + h + 2 : ℤ)
        ∨ (N + i + h + 2 : ℤ) ≤ carryOrbit h N ((j : ℤ) - (N + h + 1)) i := by
    intro j
    set d : ℤ := (j : ℤ) - (N + h + 1) with hddef
    set x : ℝ := (d : ℝ) - (totientTail (N + h) - totientTail N) with hxdef
    have hxne : x ≠ 0 := by
      rw [hxdef, sub_ne_zero]
      intro hEq
      exact hD ⟨d, hEq⟩
    have hε0 : 0 < |x| := abs_pos.mpr hxne
    obtain ⟨i, hi⟩ := existsDepthLt ((N : ℝ) + (h : ℝ) + 2) (|x| / 2) (by linarith)
    have hrw : ((N : ℝ) + (h : ℝ) + 2 + (i : ℝ)) * (1 / 2 : ℝ) ^ i
        = ((N : ℝ) + (i : ℝ) + (h : ℝ) + 2) / 2 ^ i := by
      rw [div_pow, one_pow]
      ring
    rw [hrw] at hi
    have hgrow : 2 * ((N : ℝ) + (i : ℝ) + (h : ℝ) + 2) < |x| * 2 ^ i := by
      have hm := mul_lt_mul_of_pos_left hi (show (0 : ℝ) < 2 * 2 ^ i by positivity)
      have e1 : 2 * 2 ^ i * (((N : ℝ) + (i : ℝ) + (h : ℝ) + 2) / 2 ^ i)
          = 2 * ((N : ℝ) + (i : ℝ) + (h : ℝ) + 2) := by field_simp
      have e2 : 2 * 2 ^ i * (|x| / 2) = |x| * 2 ^ i := by ring
      rwa [e1, e2] at hm
    have htrack := carryOrbit_eq_shift h N d i
    rw [← hxdef] at htrack
    have hstrip := abs_tail_diff_lt h (N + i)
    push_cast at hstrip
    rw [abs_lt] at hstrip
    refine ⟨i, ?_⟩
    rcases lt_or_gt_of_ne hxne with hneg | hpos
    · left
      have hax : |x| = -x := abs_of_neg hneg
      rw [hax] at hgrow
      have hR : ((carryOrbit h N d i : ℤ) : ℝ)
          ≤ ((-(N + i + h + 2 : ℤ) : ℤ) : ℝ) := by
        rw [htrack]
        push_cast
        linarith [hstrip.1, hstrip.2]
      exact_mod_cast hR
    · right
      have hax : |x| = x := abs_of_pos hpos
      rw [hax] at hgrow
      have hR : (((N + i + h + 2 : ℤ) : ℤ) : ℝ) ≤ ((carryOrbit h N d i : ℤ) : ℝ) := by
        rw [htrack]
        push_cast
        linarith [hstrip.1, hstrip.2]
      exact_mod_cast hR
  choose K hK using hstep
  refine ⟨(Finset.range (2 * (N + h + 1) + 1)).sup K, ?_⟩
  intro j hj
  exact ⟨K j, Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hj)), hK j⟩

/-- Irrationality supplies a firing survivor certificate at every cell with a
positive window. -/
theorem existsSurvivorKill_of_irr {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ K, survivorKill h N K :=
  existsSurvivorKill_of_tail_diff_notMem_int (tailDiff_notMem_int_of_irr hh hirr)

theorem G081_of_irr (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G081 := by
  unfold G081
  intro h₀ hpos N₀
  exact ⟨1, Nat.one_pos, N₀, le_rfl, existsSurvivorKill_of_irr (by simpa using hpos) hirr⟩

theorem G102_of_irr (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G102 := by
  unfold G102
  intro t₀ N₀
  exact ⟨t₀, le_rfl, N₀, le_rfl, existsSurvivorKill_of_irr (periodLcm_pos t₀) hirr⟩

theorem G094_of_irr (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G094 := by
  unfold G094
  intro t₀
  exact ⟨t₀, le_rfl, existsSurvivorKill_of_irr (periodLcm_pos t₀) hirr⟩

/-! ## Each Left gap implies #249 (the corpus supply theorems) -/

theorem irr_of_G082 (h : G082) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G082 at h
  exact Erdos249257.irrational_totient_series_of_multiple_window_kill_supply h

theorem irr_of_G096 (h : G096) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G096 at h
  exact Erdos249257.irrational_totient_series_of_lcm_jump_window_kill_supply h

theorem irr_of_G097 (h : G097) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G097 at h
  exact irrational_totient_series_of_lcm_diagonal_certificate_supply h

theorem irr_of_G100 (h : G100) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G100 at h
  exact Erdos249257.irrational_totient_series_of_lcm_cone_window_kill_supply h

theorem irr_of_G103 (h : G103) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G103 at h
  exact Erdos249257.irrational_totient_series_of_lcm_window_kill_supply h

end Bridge1

open Bridge1

/-! ## The direct vocabulary bridges (no detour through irrationality)

`survivorKill h N K → ∃ L, certifiedKill h N L`, cell by cell: survivor soundness
proves the *same* tail difference non-integral, and certificate completeness turns
that non-integrality back into an endpoint receipt.  The three edges below are the
image of that pointwise implication on the three matching supply shapes. -/

/-- **G081 → G082, directly.**  Same multiple-period ray, same `(m·h₀, N)` cell:
only the certificate species changes. -/
theorem e_G081_G082_direct : G081 → G082 := by
  unfold G081 G082
  intro hsup h₀ hpos N₀
  obtain ⟨m, hm, N, hN, K, hkill⟩ := hsup h₀ hpos N₀
  exact ⟨m, hm, N, hN,
    exists_certifiedKill_of_tail_diff_notMem_int
      (tail_diff_notMem_int_of_survivorKill hkill)⟩

/-- **G102 → G103, directly.**  Same lcm ray in general position. -/
theorem e_G102_G103_direct : G102 → G103 := by
  unfold G102 G103
  intro hsup t₀ N₀
  obtain ⟨t, ht, N, hN, K, hkill⟩ := hsup t₀ N₀
  exact ⟨t, ht, N, hN,
    exists_certifiedKill_of_tail_diff_notMem_int
      (tail_diff_notMem_int_of_survivorKill hkill)⟩

/-- **G094 → G097, directly.**  Same diagonal cell `(H t, H t)`. -/
theorem e_G094_G097_direct : G094 → G097 := by
  unfold G094 G097
  intro hsup t₀
  obtain ⟨t, ht, K, hkill⟩ := hsup t₀
  exact ⟨t, ht,
    exists_certifiedKill_of_tail_diff_notMem_int
      (tail_diff_notMem_int_of_survivorKill hkill)⟩

/-- **G099 → G100, directly.**  A rank-2 kill at `(H t, q·H t)` says the second
difference `(R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N)` is not an integer, so at least
one of the two consecutive first differences is not an integer.  Each of those is a
wave-24 cone cell with `m = 1`: the lower one at `q`, the upper one at `q + 1`.
Certificate completeness then supplies the endpoint receipt. -/
theorem e_G099_G100_direct : G099 → G100 := by
  unfold G099 G100
  intro hsup t₀
  obtain ⟨t, ht, q, L, hq, hcert⟩ := hsup t₀
  have hrank2 := second_diff_notMem_int_of_certifiedRank2Kill hcert
  by_cases hlow : totientTail (q * periodLcm t + periodLcm t)
      - totientTail (q * periodLcm t) ∈ Set.range ((↑) : ℤ → ℝ)
  · -- the lower difference is an integer, so the upper one is not: cell `(q+1, 1)`
    obtain ⟨a, ha⟩ := hlow
    have hup : totientTail ((q + 1) * periodLcm t + 1 * periodLcm t)
        - totientTail ((q + 1) * periodLcm t) ∉ Set.range ((↑) : ℤ → ℝ) := by
      rintro ⟨b, hb⟩
      rw [show (q + 1) * periodLcm t + 1 * periodLcm t
            = q * periodLcm t + 2 * periodLcm t from by ring,
          show (q + 1) * periodLcm t = q * periodLcm t + periodLcm t from by ring] at hb
      exact hrank2 ⟨b - a, by push_cast; linarith⟩
    obtain ⟨L', hL'⟩ := exists_certifiedKill_of_tail_diff_notMem_int
      (h := 1 * periodLcm t) (N := (q + 1) * periodLcm t) hup
    exact ⟨t, ht, q + 1, 1, L', by omega, hL'⟩
  · -- the lower difference is already non-integral: cell `(q, 1)`
    obtain ⟨L', hL'⟩ := exists_certifiedKill_of_tail_diff_notMem_int
      (h := 1 * periodLcm t) (N := q * periodLcm t)
      (by rwa [show q * periodLcm t + 1 * periodLcm t
            = q * periodLcm t + periodLcm t from by ring])
    exact ⟨t, ht, q, 1, L', hq, hL'⟩

/-! ## All 20 Right → Left edges

Each Right gap is a supply theorem for #249; #249 restores every Left gap. -/

theorem e_G081_G082 : G081 → G082 := fun h => G082_of_irr (irr_of_G081 h)
theorem e_G081_G096 : G081 → G096 := fun h => G096_of_irr (irr_of_G081 h)
theorem e_G081_G097 : G081 → G097 := fun h => G097_of_irr (irr_of_G081 h)
theorem e_G081_G100 : G081 → G100 := fun h => G100_of_irr (irr_of_G081 h)
theorem e_G081_G103 : G081 → G103 := fun h => G103_of_irr (irr_of_G081 h)

theorem e_G102_G082 : G102 → G082 := fun h => G082_of_irr (irr_of_G102 h)
theorem e_G102_G096 : G102 → G096 := fun h => G096_of_irr (irr_of_G102 h)
theorem e_G102_G097 : G102 → G097 := fun h => G097_of_irr (irr_of_G102 h)
theorem e_G102_G100 : G102 → G100 := fun h => G100_of_irr (irr_of_G102 h)
theorem e_G102_G103 : G102 → G103 := fun h => G103_of_irr (irr_of_G102 h)

theorem e_G094_G082 : G094 → G082 := fun h => G082_of_irr (irr_of_G094 h)
theorem e_G094_G096 : G094 → G096 := fun h => G096_of_irr (irr_of_G094 h)
theorem e_G094_G097 : G094 → G097 := fun h => G097_of_irr (irr_of_G094 h)
theorem e_G094_G100 : G094 → G100 := fun h => G100_of_irr (irr_of_G094 h)
theorem e_G094_G103 : G094 → G103 := fun h => G103_of_irr (irr_of_G094 h)

theorem e_G099_G082 : G099 → G082 := fun h => G082_of_irr (irr_of_G099 h)
theorem e_G099_G096 : G099 → G096 := fun h => G096_of_irr (irr_of_G099 h)
theorem e_G099_G097 : G099 → G097 := fun h => G097_of_irr (irr_of_G099 h)
theorem e_G099_G100 : G099 → G100 := fun h => G100_of_irr (irr_of_G099 h)
theorem e_G099_G103 : G099 → G103 := fun h => G103_of_irr (irr_of_G099 h)

/-! ## The five Left → G099 edges: the rank-2 programme collapses onto #249

With rank-2 completeness proved above, `G099` is no longer only *sufficient* for
#249 — it is *equivalent* to it, hence to every gap of the `certifiedKill`
cluster.  The rank-2 second-difference lane and the rank-1 endpoint lane are the
same open problem in two notations. -/

theorem e_G082_G099 : G082 → G099 := fun h => G099_of_irr (irr_of_G082 h)
theorem e_G096_G099 : G096 → G099 := fun h => G099_of_irr (irr_of_G096 h)
theorem e_G097_G099 : G097 → G099 := fun h => G099_of_irr (irr_of_G097 h)
theorem e_G100_G099 : G100 → G099 := fun h => G099_of_irr (irr_of_G100 h)
theorem e_G103_G099 : G103 → G099 := fun h => G099_of_irr (irr_of_G103 h)

/-! ## The fifteen Left → survivor edges: the survivor programme collapses too

Survivor completeness closes the last gap.  All nine statements of this bridge
set — five in `certifiedKill`, three in `survivorKill`, one in
`certifiedRank2Kill` — are mutually equivalent, and each is equivalent to
Erdős #249.  The three "vocabularies" are three notations for one problem. -/

theorem e_G082_G081 : G082 → G081 := fun h => G081_of_irr (irr_of_G082 h)
theorem e_G096_G081 : G096 → G081 := fun h => G081_of_irr (irr_of_G096 h)
theorem e_G097_G081 : G097 → G081 := fun h => G081_of_irr (irr_of_G097 h)
theorem e_G100_G081 : G100 → G081 := fun h => G081_of_irr (irr_of_G100 h)
theorem e_G103_G081 : G103 → G081 := fun h => G081_of_irr (irr_of_G103 h)

theorem e_G082_G102 : G082 → G102 := fun h => G102_of_irr (irr_of_G082 h)
theorem e_G096_G102 : G096 → G102 := fun h => G102_of_irr (irr_of_G096 h)
theorem e_G097_G102 : G097 → G102 := fun h => G102_of_irr (irr_of_G097 h)
theorem e_G100_G102 : G100 → G102 := fun h => G102_of_irr (irr_of_G100 h)
theorem e_G103_G102 : G103 → G102 := fun h => G102_of_irr (irr_of_G103 h)

theorem e_G082_G094 : G082 → G094 := fun h => G094_of_irr (irr_of_G082 h)
theorem e_G096_G094 : G096 → G094 := fun h => G094_of_irr (irr_of_G096 h)
theorem e_G097_G094 : G097 → G094 := fun h => G094_of_irr (irr_of_G097 h)
theorem e_G100_G094 : G100 → G094 := fun h => G094_of_irr (irr_of_G100 h)
theorem e_G103_G094 : G103 → G094 := fun h => G094_of_irr (irr_of_G103 h)

end DemandLedger.Bridge1
