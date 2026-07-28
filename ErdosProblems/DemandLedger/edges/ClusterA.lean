import ErdosProblems.DemandLedger.Basic

/-!
# Cluster A of the demand ledger: the `certifiedKill` supply gaps

The five gaps `G082, G096, G097, G100, G103` are all *supply* hypotheses phrased
in the endpoint-certificate vocabulary `certifiedKill`:

* `G082` — `∀ h₀ > 0, ∀ N₀, ∃ m > 0, ∃ N ≥ N₀, ∃ L, certifiedKill (m*h₀) N L`
  (multiple-period ray, wave 22)
* `G103` — `∀ t₀ N₀, ∃ t ≥ t₀, ∃ N ≥ N₀, ∃ L, certifiedKill (H t) N L`
  (lcm ray in general position, wave 23)
* `G097` — `∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (H t) (H t) L`
  (the diagonal, wave 23)
* `G100` — `∀ t₀, ∃ t ≥ t₀, ∃ q m L, 0 < q ∧ certifiedKill (m*H t) (q*H t) L`
  (the two-multiplier cone, wave 24)
* `G096` — `∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (H (t+1) - H t) (H t) L`
  (the lcm jumps, wave 25)

where `H t = periodLcm t = lcm(1..t)`.

**Result: the cluster collapses completely — all five are mutually equivalent,
and each is equivalent to Erdős #249 itself.**  All 20 ordered pairs are edges.

The forward halves (`gap → #249`) are the corpus supply theorems.  The reverse
halves are new here and rest on one observation, `tail_diff_notMem_int_of_irrational`
below: by the shift identity `2^N·S = Φ_N + R_N`, a *single* integral tail
difference `R_{N+h} - R_N ∈ ℤ` with `h > 0` rearranges into
`2^N·(2^h - 1)·S ∈ ℤ`, so it forces `S` rational outright.  There is no
"eventually", no pre-period and no period ray in that direction: irrationality
makes *every* cell of the lattice with `h > 0` non-integral at once, and
certificate completeness (`exists_certifiedKill_of_tail_diff_notMem_int`)
turns each such cell into a firing certificate.  Every supply statement in this
vocabulary whose window `h` can be forced positive is therefore not merely
sufficient for #249 but necessary, hence equivalent to it and to every other
such statement.

For `G096` positivity of the window is not automatic — `H (t+1) - H t = 0`
whenever `t+1` is not a prime power — so the reverse direction there needs
`exists_strict_jump`: the lcm ladder climbs infinitely often, since it is
unbounded (`t ≤ H t`).

Four edges (`G097 → G103`, `G103 → G082`, `G097 → G100`, `G096 → G100`) and
one more (`G100 → G103`, by period-ray telescoping plus certificate
completeness) are additionally proved *directly*, i.e. without routing through
irrationality; they are recorded as `…_direct` and are the structural spine of
the cluster.  The remaining edges are, as far as this file can tell, available
only through the hub.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace DemandLedger.ClusterA

/-! ## Infrastructure: irrationality forces every window non-integral -/

/-- **The necessity bridge.**  If `S = ∑ φ(n)/2ⁿ` is irrational then NO tail
difference with a positive window is an integer.  One integral difference is
already fatal: `R_{N+h} - R_N = 2^N(2^h-1)·S - (Φ_{N+h} - Φ_N)` by the shift
identity, so `R_{N+h} - R_N ∈ ℤ` exhibits `S` as a rational with denominator
`2^N(2^h-1) ≠ 0`.  (Contrast `eventual_period_of_not_irrational`, which spends
rationality in the other direction and only from a pre-period on.) -/
theorem tail_diff_notMem_int_of_irrational {h N : ℕ} (hh : 0 < h)
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

/-- Irrationality supplies a firing endpoint certificate at EVERY cell with a
positive window: the bridge above plus certificate completeness. -/
theorem exists_certifiedKill_of_irrational {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ L, certifiedKill h N L :=
  exists_certifiedKill_of_tail_diff_notMem_int (tail_diff_notMem_int_of_irrational hh hirr)

/-- The lcm ladder climbs infinitely often: `H t < H (t+1)` for arbitrarily
large `t`.  Otherwise `H` would be eventually constant while `t ≤ H t`. -/
theorem exists_strict_jump (t₀ : ℕ) :
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

/-- A finite sum of integers is an integer (in the `Set.range Int.cast` form
used throughout the corpus). -/
theorem sum_mem_range_int {m : ℕ} {f : ℕ → ℝ}
    (hf : ∀ i ∈ Finset.range m, f i ∈ Set.range ((↑) : ℤ → ℝ)) :
    (∑ i ∈ Finset.range m, f i) ∈ Set.range ((↑) : ℤ → ℝ) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      rw [Finset.sum_range_succ]
      obtain ⟨a, ha⟩ := ih fun i hi =>
        hf i (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self m)))
      obtain ⟨b, hb⟩ := hf m (Finset.mem_range.mpr (Nat.lt_succ_self m))
      exact ⟨a + b, by push_cast; rw [ha, hb]⟩

/-! ## Each gap implies #249 (the corpus supply theorems) -/

theorem irrational_of_G082 (h : G082) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G082 at h
  exact Erdos249257.irrational_totient_series_of_multiple_window_kill_supply h

theorem irrational_of_G096 (h : G096) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G096 at h
  exact Erdos249257.irrational_totient_series_of_lcm_jump_window_kill_supply h

theorem irrational_of_G097 (h : G097) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G097 at h
  exact irrational_totient_series_of_lcm_diagonal_certificate_supply h

theorem irrational_of_G100 (h : G100) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G100 at h
  exact Erdos249257.irrational_totient_series_of_lcm_cone_window_kill_supply h

theorem irrational_of_G103 (h : G103) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G103 at h
  exact Erdos249257.irrational_totient_series_of_lcm_window_kill_supply h

/-! ## #249 implies each gap (the converse halves, new) -/

theorem G082_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G082 := by
  unfold G082
  intro h₀ hpos N₀
  exact ⟨1, Nat.one_pos, N₀, le_rfl,
    exists_certifiedKill_of_irrational (by simpa using hpos) hirr⟩

theorem G096_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G096 := by
  unfold G096
  intro t₀
  obtain ⟨t, ht, hjump⟩ := exists_strict_jump t₀
  exact ⟨t, ht, exists_certifiedKill_of_irrational (Nat.sub_pos_of_lt hjump) hirr⟩

theorem G097_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G097 := by
  unfold G097
  intro t₀
  exact ⟨t₀, le_rfl, exists_certifiedKill_of_irrational (periodLcm_pos t₀) hirr⟩

theorem G100_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G100 := by
  unfold G100
  intro t₀
  obtain ⟨L, hL⟩ := exists_certifiedKill_of_irrational
    (h := 1 * periodLcm t₀) (N := 1 * periodLcm t₀) (by simpa using periodLcm_pos t₀) hirr
  exact ⟨t₀, le_rfl, 1, 1, L, Nat.one_pos, hL⟩

theorem G103_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G103 := by
  unfold G103
  intro t₀ N₀
  exact ⟨t₀, le_rfl, N₀, le_rfl,
    exists_certifiedKill_of_irrational (periodLcm_pos t₀) hirr⟩

/-! ## The structural edges, proved directly (no rationality hub) -/

/-- Diagonal ⟹ general position: standing at `N = H t` is a legal choice of the
free endpoint, because `H t ≥ t`. -/
theorem e_G097_G103_direct : G097 → G103 := by
  unfold G097 G103
  intro h t₀ N₀
  obtain ⟨t, ht, L, hkill⟩ := h (max t₀ N₀)
  exact ⟨t, le_trans (le_max_left _ _) ht, periodLcm t,
    le_trans (le_trans (le_max_right _ _) ht) (le_periodLcm t), L, hkill⟩

/-- Lcm ray ⟹ multiple ray: `H t` is itself a multiple of every `h₀ ≤ t`. -/
theorem e_G103_G082_direct : G103 → G082 := by
  unfold G103 G082
  intro h h₀ hpos N₀
  obtain ⟨t, ht, N, hN, L, hkill⟩ := h h₀ N₀
  have hdvd : h₀ ∣ periodLcm t := dvd_periodLcm hpos ht
  refine ⟨periodLcm t / h₀,
    Nat.div_pos (Nat.le_of_dvd (periodLcm_pos t) hdvd) hpos, N, hN, L, ?_⟩
  rwa [Nat.div_mul_cancel hdvd]

/-- Diagonal ⟹ cone: the diagonal is the cone cell `q = m = 1`. -/
theorem e_G097_G100_direct : G097 → G100 := by
  unfold G097 G100
  intro h t₀
  obtain ⟨t, ht, L, hkill⟩ := h t₀
  refine ⟨t, ht, 1, 1, L, Nat.one_pos, ?_⟩
  rwa [one_mul]

/-- Jump ⟹ cone: the jump `H (t+1) - H t` is the cone cell `(q, m) = (1, k-1)`
where `H (t+1) = k · H t`. -/
theorem e_G096_G100_direct : G096 → G100 := by
  unfold G096 G100
  intro h t₀
  obtain ⟨t, ht, L, hkill⟩ := h t₀
  obtain ⟨k, hk⟩ := periodLcm_dvd_succ t
  refine ⟨t, ht, 1, k - 1, L, Nat.one_pos, ?_⟩
  have hm : (k - 1) * periodLcm t = periodLcm (t + 1) - periodLcm t := by
    rw [hk, Nat.sub_one_mul, mul_comm k (periodLcm t)]
  rw [hm, one_mul]
  exact hkill

/-- Cone ⟹ lcm ray: period-ray telescoping.  A non-integral cone difference
`R_{qH + mH} - R_{qH}` is a sum of `m` single-step differences along the ray, so
one of them is non-integral, and certificate completeness turns it back into a
firing certificate at window exactly `H t`. -/
theorem e_G100_G103_direct : G100 → G103 := by
  unfold G100 G103
  intro h t₀ N₀
  obtain ⟨t, ht, q, m, L, hq, hkill⟩ := h (max t₀ N₀)
  have hnot := tail_diff_notMem_int_of_certifiedKill hkill
  rw [tail_diff_mul (periodLcm t) (q * periodLcm t) m] at hnot
  have hex : ∃ i, i ∈ Finset.range m ∧
      (totientTail (q * periodLcm t + i * periodLcm t + periodLcm t)
        - totientTail (q * periodLcm t + i * periodLcm t)) ∉ Set.range ((↑) : ℤ → ℝ) := by
    by_contra hall
    exact hnot (sum_mem_range_int fun i hi =>
      Classical.byContradiction fun hc => hall ⟨i, hi, hc⟩)
  obtain ⟨i, _, hfi⟩ := hex
  have h1 : N₀ ≤ t := le_trans (le_max_right _ _) ht
  have h2 : t ≤ periodLcm t := le_periodLcm t
  have h3 : periodLcm t ≤ q * periodLcm t := by
    calc periodLcm t = 1 * periodLcm t := (one_mul _).symm
      _ ≤ q * periodLcm t := Nat.mul_le_mul_right _ hq
  exact ⟨t, le_trans (le_max_left _ _) ht, q * periodLcm t + i * periodLcm t, by omega,
    exists_certifiedKill_of_tail_diff_notMem_int hfi⟩

/-! ## All 20 ordered pairs

Every gap in this cluster is equivalent to every other, and to #249 itself.
-/

theorem e_G082_G096 : G082 → G096 := fun h => G096_of_irrational (irrational_of_G082 h)
theorem e_G082_G097 : G082 → G097 := fun h => G097_of_irrational (irrational_of_G082 h)
theorem e_G082_G100 : G082 → G100 := fun h => G100_of_irrational (irrational_of_G082 h)
theorem e_G082_G103 : G082 → G103 := fun h => G103_of_irrational (irrational_of_G082 h)

theorem e_G096_G082 : G096 → G082 := fun h => G082_of_irrational (irrational_of_G096 h)
theorem e_G096_G097 : G096 → G097 := fun h => G097_of_irrational (irrational_of_G096 h)
theorem e_G096_G100 : G096 → G100 := e_G096_G100_direct
theorem e_G096_G103 : G096 → G103 := fun h => G103_of_irrational (irrational_of_G096 h)

theorem e_G097_G082 : G097 → G082 := e_G103_G082_direct ∘ e_G097_G103_direct
theorem e_G097_G096 : G097 → G096 := fun h => G096_of_irrational (irrational_of_G097 h)
theorem e_G097_G100 : G097 → G100 := e_G097_G100_direct
theorem e_G097_G103 : G097 → G103 := e_G097_G103_direct

theorem e_G100_G082 : G100 → G082 := e_G103_G082_direct ∘ e_G100_G103_direct
theorem e_G100_G096 : G100 → G096 := fun h => G096_of_irrational (irrational_of_G100 h)
theorem e_G100_G097 : G100 → G097 := fun h => G097_of_irrational (irrational_of_G100 h)
theorem e_G100_G103 : G100 → G103 := e_G100_G103_direct

theorem e_G103_G082 : G103 → G082 := e_G103_G082_direct
theorem e_G103_G096 : G103 → G096 := fun h => G096_of_irrational (irrational_of_G103 h)
theorem e_G103_G097 : G103 → G097 := fun h => G097_of_irrational (irrational_of_G103 h)
theorem e_G103_G100 : G103 → G100 := fun h => G100_of_irrational (irrational_of_G103 h)

/-! ## The collapse, stated once

All five gaps are equivalent to Erdős #249 and hence to each other: the cluster
is a single frontier record, not five. -/

theorem G082_iff_irrational :
    G082 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨irrational_of_G082, G082_of_irrational⟩

theorem G096_iff_irrational :
    G096 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨irrational_of_G096, G096_of_irrational⟩

theorem G097_iff_irrational :
    G097 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨irrational_of_G097, G097_of_irrational⟩

theorem G100_iff_irrational :
    G100 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨irrational_of_G100, G100_of_irrational⟩

theorem G103_iff_irrational :
    G103 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨irrational_of_G103, G103_of_irrational⟩

end DemandLedger.ClusterA
