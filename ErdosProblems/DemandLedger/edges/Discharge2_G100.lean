import ErdosProblems.DemandLedger.Basic

/-!
# Supply-side attack on `G100`

`G100` is the wave-24 two-multiplier lcm-cone supply hypothesis

```
∀ t₀, ∃ t ≥ t₀, ∃ q m L, 0 < q ∧ certifiedKill (m * H t) (q * H t) L
```

with `H t = periodLcm t = lcm(1..t)`.  It is cofinal in `t`, so no finite set of
certificates can discharge it.  This file records the finite supply imported
when it was written; later modules extend the repository's diagonal band.

For this module's imported snapshot:

* the imported corpus records certificates at 29 scales, namely
  `t ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32,
  37, 41, 43, 47, 49, 53, 59, 61, 64}`.  Up to `t = 6` that is a `decide`; from
  `t = 7` on it is exactly `{1} ∪ {prime powers ≤ 64}`, which is the ladder
  `diagonalPincerCertificateScalesThroughT64`;
* `H` is constant between consecutive prime powers, so those certificates
  already fire the body of `G100` at **every** scale `1 ≤ t ≤ 66` — including
  the 37 scales `10, 12, 14, 15, 18, 20, 21, 22, 24, 26, 28, 30, 33, 34, 35, 36,
  38, 39, 40, 42, 44, 45, 46, 48, 50, 51, 52, 54, 55, 56, 57, 58, 60, 62, 63,
  65, 66` at which no certificate is recorded anywhere in the corpus;
* the plateau-transfer argument in this file stops at `t = 67`.  `67` is prime,
  so no reindexing of the older cells reaches it
  (`periodLcm_lt_periodLcm_67`).  `depth_floor_beyond_66` gives the stated depth
  floor for later cells.  The repository now certifies `t = 67` at minimal
  depth `100` and extends the finite diagonal band through `t ≤ 82`.

So `G100` is *not* discharged.  `G100_iff_beyond_66` remains a valid
cofinal-tail equivalence, but `67` is no longer the current finite boundary;
the remaining issue is cofinal supply, not any particular finite cell.

Along the way several existing corpus theorems are shown to be instances of the
`G100` body at parameters that do not look like it syntactically — the argument
coincidences of §3.
-/

set_option maxRecDepth 40000

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace DemandLedger.Discharge2G100

/-! ## 1.  Normal form: the body of `G100` at a single scale -/

/-- The body of `G100` at scale `t`: some cell of the two-multiplier lcm cone
`{(m·H t, q·H t) : q > 0}` carries an endpoint certificate. -/
def ConeCell (t : ℕ) : Prop :=
  ∃ q m L : ℕ, 0 < q ∧ certifiedKill (m * periodLcm t) (q * periodLcm t) L

/-- `G100` is exactly cofinality of `ConeCell`.  Definitional — the extracted
antecedent is this statement on the nose. -/
theorem G100_iff_coneCell_cofinal : G100 ↔ ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ConeCell t := by
  unfold G100 ConeCell
  exact Iff.rfl

/-- The diagonal is the cell `q = m = 1`. -/
theorem coneCell_of_diagonalKill {t L : ℕ}
    (h : certifiedKill (periodLcm t) (periodLcm t) L) : ConeCell t :=
  ⟨1, 1, L, Nat.one_pos, by simpa using h⟩

/-- `ConeCell` only sees the *height* `H t`, never `t`. -/
theorem coneCell_of_periodLcm_eq {t u : ℕ} (h : periodLcm t = periodLcm u)
    (hc : ConeCell u) : ConeCell t := by
  obtain ⟨q, m, L, hq, hk⟩ := hc
  exact ⟨q, m, L, hq, by rw [h]; exact hk⟩

/-- **Cone cells are inherited downwards.**  A diagonal certificate at scale `u`
is simultaneously a cone cell at *every* scale `t ≤ u`, with multiplier
`q = m = H u / H t`.  This is the first argument coincidence: the 29 recorded
diagonal certificates are, jointly, 29 distinct cells of the `t = 1` cone, 28 of
the `t = 2` cone, and so on. -/
theorem coneCell_of_diagonalKill_of_le {t u L : ℕ} (htu : t ≤ u)
    (h : certifiedKill (periodLcm u) (periodLcm u) L) : ConeCell t := by
  obtain ⟨k, hk⟩ := periodLcm_dvd_periodLcm htu
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h'
    · rw [Nat.mul_zero] at hk
      exact absurd hk (periodLcm_pos u).ne'
    · exact h'
  refine ⟨k, k, L, hkpos, ?_⟩
  have hmul : k * periodLcm t = periodLcm u := by rw [hk]; ring
  rw [hmul]
  exact h

/-! ## 2.  The plateau law: `H` does not move at a non-prime-power scale -/

/-- If `a, b ≤ t` are coprime then their product divides `H t`, even when the
product exceeds `t`. -/
theorem mul_dvd_periodLcm_of_coprime {a b t : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hat : a ≤ t) (hbt : b ≤ t) (hab : Nat.Coprime a b) : a * b ∣ periodLcm t :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd hab (dvd_periodLcm ha hat) (dvd_periodLcm hb hbt)

/-- **Plateau law.**  If every endpoint in `(t, u]` already divides `H t`, the
lcm ladder does not move between `t` and `u`. -/
theorem periodLcm_eq_of_forall_dvd {t u : ℕ} (htu : t ≤ u)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ u → k ∣ periodLcm t) : periodLcm u = periodLcm t :=
  Nat.dvd_antisymm
    (Erdos249257.DiagonalFreshLossBridge.periodLcm_dvd_of_forall_pos_le h)
    (periodLcm_dvd_periodLcm htu)

/-- `65 = 5·13` and `66 = 6·11` are not prime powers, so the ladder is flat from
`64` to `66`: `lcm(1..66) = lcm(1..64)`.  Consequently the `t = 64` diagonal
certificate lives at scale `66` as well. -/
theorem periodLcm_66_eq_periodLcm_64 : periodLcm 66 = periodLcm 64 := by
  refine periodLcm_eq_of_forall_dvd (by norm_num) ?_
  intro k hk1 hk66
  rcases Nat.lt_or_ge k 65 with hlt | hge
  · exact dvd_periodLcm hk1 (by omega)
  · interval_cases k
    · exact (show (65 : ℕ) = 5 * 13 by norm_num) ▸
        mul_dvd_periodLcm_of_coprime (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by decide)
    · exact (show (66 : ℕ) = 6 * 11 by norm_num) ▸
        mul_dvd_periodLcm_of_coprime (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by decide)

/-! ## 3.  Argument coincidences: corpus theorems that already *are* `G100` cells

Each of the following is an existing kernel-checked corpus theorem, re-read as an
instance of the `G100` body.  None of them is stated in the `G100` vocabulary.
-/

/-- `H 8 = 2 · H 7` (840 = 2·420), so the wave-23 **diagonal** certificate at
`t = 8` is *also* the off-diagonal cone cell `(t, q, m) = (7, 2, 2)`. -/
theorem coneCell_7_from_t8_diagonal :
    certifiedKill (2 * periodLcm 7) (2 * periodLcm 7) 15 := by
  have h := certifiedKill_diagonal_t8
  have hval : periodLcm 8 = 2 * periodLcm 7 := by decide
  rwa [hval] at h

/-- `H 9 = 6 · H 7` (2520 = 6·420): the `t = 9` diagonal certificate is the cone
cell `(7, 6, 6)`, at depth `14` — *shallower* than the `t = 8` cell at the same
scale. -/
theorem coneCell_7_from_t9_diagonal :
    certifiedKill (6 * periodLcm 7) (6 * periodLcm 7) 14 := by
  have h := certifiedKill_diagonal_t9
  have hval : periodLcm 9 = 6 * periodLcm 7 := by decide
  rwa [hval] at h

/-- The wave-21 deposit `certifiedKill h 12 16` for `h ≤ 8` carries **no lcm
vocabulary at all**, yet `12 = 2·H 3` and `6 = 1·H 3`, so its `h = 6` instance is
the cone cell `(t, q, m) = (3, 2, 1)` — a cell absent from
`certifiedKill_lcm_cone_cells`. -/
theorem coneCell_3_from_period_killed_upto_eight :
    certifiedKill (1 * periodLcm 3) (2 * periodLcm 3) 16 := by
  have h := totient_tail_period_killed_upto_eight 6 (by decide)
  have h1 : (1 : ℕ) * periodLcm 3 = 6 := by decide
  have h2 : (2 : ℕ) * periodLcm 3 = 12 := by decide
  rw [h1, h2]
  exact h

/-- Same deposit, read at `t = 2`: `12 = 6·H 2` and `8 = 4·H 2`, giving the cell
`(2, 6, 4)`. -/
theorem coneCell_2_from_period_killed_upto_eight :
    certifiedKill (4 * periodLcm 2) (6 * periodLcm 2) 16 := by
  have h := totient_tail_period_killed_upto_eight 8 (by decide)
  have h1 : (4 : ℕ) * periodLcm 2 = 8 := by decide
  have h2 : (6 : ℕ) * periodLcm 2 = 12 := by decide
  rw [h1, h2]
  exact h

/-- The wave-22 deposit `certifiedKill h 14 9` for `h ≤ 16`: `14 = 7·H 2`, so
every even `h ≤ 16` gives a cone cell `(2, 7, m)` with `m ≤ 8`. -/
theorem coneCell_2_from_period_killed_upto_sixteen (m : ℕ) (hm : 1 ≤ m) (hm8 : m ≤ 8) :
    certifiedKill (m * periodLcm 2) (7 * periodLcm 2) 9 := by
  have h := certifiedKill_all_upto_sixteen (2 * m) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have h1 : m * periodLcm 2 = 2 * m := by
    have : periodLcm 2 = 2 := by decide
    rw [this]; ring
  have h2 : (7 : ℕ) * periodLcm 2 = 14 := by decide
  rw [h1, h2]
  exact h

/-- Recorded off-diagonal cone cells (wave 24). -/
theorem coneCell_2_offdiagonal : ConeCell 2 :=
  ⟨3, 1, 6, by norm_num, certifiedKill_lcm_cone_cells.1⟩

theorem coneCell_3_offdiagonal : ConeCell 3 :=
  ⟨1, 3, 8, by norm_num, certifiedKill_lcm_cone_cells.2.2⟩

/-- The wave-25 non-flatness witness is the cone cell `(2, 1, 2)`. -/
theorem coneCell_2_from_nonflat : ConeCell 2 :=
  ⟨1, 2, 9, by norm_num, cone_nonflat_strict_win_at_cell.2.2⟩

/-! ## 4.  Coverage: the body of `G100` holds at **every** scale `t ≤ 66` -/

/-- The largest scale carrying a recorded diagonal certificate that is `≤ t`. -/
def certScale (t : ℕ) : ℕ :=
  diagonalPincerCertificateScalesThroughT64.foldl
    (fun acc u => if u ≤ t then max acc u else acc) 1

theorem certScale_mem :
    ∀ t ∈ Finset.Icc 1 66, certScale t ∈ diagonalPincerCertificateScalesThroughT64 := by
  decide

/-- **The plateau table, machine-checked.**  Every scale `t ≤ 66` has the same
lcm height as a certified scale. -/
theorem periodLcm_certScale :
    ∀ t ∈ Finset.Icc 1 66, periodLcm t = periodLcm (certScale t) := by
  decide

/-- **Coverage theorem.**  The body of `G100` fires at *every* scale
`1 ≤ t ≤ 66`, not merely at the 29 scales where a certificate is recorded.  The
37 scales `10, 12, 14, 15, 18, 20, 21, 22, 24, 26, 28, 30, 33, …, 65, 66` carry
no certificate anywhere in the corpus and are nonetheless instances. -/
theorem coneCell_of_le_66 : ∀ t ∈ Finset.Icc 1 66, ConeCell t := by
  intro t ht
  refine coneCell_of_periodLcm_eq (periodLcm_certScale t ht) ?_
  exact coneCell_of_diagonalKill
    (certifiedKill_diagonal_all_imported_through_t64 _ (certScale_mem t ht))

/-- Named form of the top of the covered range: scale `66`, served by the `t = 64`
certificate at depth `93` because `lcm(1..66) = lcm(1..64)`. -/
theorem coneCell_66 : ConeCell 66 :=
  coneCell_of_periodLcm_eq periodLcm_66_eq_periodLcm_64
    (coneCell_of_diagonalKill certifiedKill_diagonal_t64)

/-! ## 5.  The discharged fragment of `G100`, and its exact complement -/

/-- **What the proved supply reaches.**  Every obligation of `G100` whose
threshold is `≤ 66` is met, unconditionally. -/
theorem G100_for_threshold_le_66 (t₀ : ℕ) (h : t₀ ≤ 66) :
    ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
      certifiedKill (m * periodLcm t) (q * periodLcm t) L :=
  ⟨66, h, coneCell_66⟩

/-- **Where it stops.**  All of `G100` below threshold `67` is already proved, so
`G100` is equivalent to its tail from `67` on.  This is the precise residue. -/
theorem G100_iff_beyond_66 :
    G100 ↔ ∀ t₀ : ℕ, 67 ≤ t₀ → ∃ t, t₀ ≤ t ∧ ConeCell t := by
  rw [G100_iff_coneCell_cofinal]
  constructor
  · intro h t₀ _
    exact h t₀
  · intro h t₀
    rcases Nat.lt_or_ge t₀ 67 with hlt | hge
    · exact ⟨66, by omega, coneCell_66⟩
    · exact h t₀ hge

/-! ## 6.  Why `67` is a wall and not a gap -/

/-- A zero window has zero discrepancy. -/
theorem windowDiscrepancy_zero_window (N L : ℕ) : windowDiscrepancy 0 N L = 0 := by
  unfold windowDiscrepancy
  refine Finset.sum_eq_zero ?_
  intro j _
  simp

/-- **The degenerate cells never fire.**  `G100` demands `0 < q` but places no
constraint on `m`, so `m = 0` is a formally admissible cell; it is however never
certifiable, since `R_{N+0} - R_N = 0` is an integer.  Every witness for `G100`
therefore carries a genuinely positive window. -/
theorem not_certifiedKill_zero_window (N L : ℕ) : ¬ certifiedKill 0 N L := by
  intro h
  have h1 := h.1
  rw [windowDiscrepancy_zero_window, Int.zero_emod] at h1
  have hpos : (0 : ℤ) ≤ (N : ℤ) + (0 : ℕ) + (L : ℤ) + 2 := by positivity
  linarith

/-- `67` is prime, so it divides no smaller height: the ladder strictly climbs at
`66`.  No reindexing of any existing certificate reaches scale `67`. -/
theorem periodLcm_lt_periodLcm_67 : periodLcm 66 < periodLcm 67 := by
  refine (Erdos249257.DiagonalFreshLossBridge.periodLcm_strict_jump_iff_succ_not_dvd 66).2 ?_
  rw [periodLcm_66_eq_periodLcm_64]
  decide

/-- The first uncovered height, explicitly: `H 67 = 67 · H 64`. -/
theorem periodLcm_67_eq : periodLcm 67 = 67 * periodLcm 64 := by decide

theorem periodLcm_67_val : periodLcm 67 = 79211881234889091923261227200 := by decide

/-- **Depth floor at the wall.**  Every certificate discharging the body of
`G100` at any scale `t ≥ 67` has depth at least `98`: the certificate window must
outrun `4 · H 67 ≈ 3.17 · 10²⁹`, and `2⁹⁷ < 4 · H 67`.  For comparison the whole
corpus tops out at depth `94` (the `t = 61` certificate), and the `t = 64`
certificate sits at depth `93`. -/
theorem depth_floor_beyond_66 {t q m L : ℕ} (ht : 67 ≤ t) (hq : 0 < q) (hm : 0 < m)
    (hcert : certifiedKill (m * periodLcm t) (q * periodLcm t) L) : 98 ≤ L := by
  by_contra hLnot
  have hL : L ≤ 97 := by omega
  have hfloor := certifiedKill_depth_floor hcert
  have hdvd : periodLcm 67 ≤ periodLcm t :=
    Nat.le_of_dvd (periodLcm_pos t) (periodLcm_dvd_periodLcm ht)
  have hval : (79211881234889091923261227200 : ℕ) ≤ periodLcm t := by
    rw [← periodLcm_67_val]; exact hdvd
  have hq1 : periodLcm t ≤ q * periodLcm t := Nat.le_mul_of_pos_left _ hq
  have hm1 : periodLcm t ≤ m * periodLcm t := Nat.le_mul_of_pos_left _ hm
  have hpow : (2 : ℤ) ^ L ≤ 2 ^ 97 := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hbig : (79211881234889091923261227200 : ℤ) ≤ (q * periodLcm t : ℕ) := by
    exact_mod_cast le_trans hval hq1
  have hbig' : (79211881234889091923261227200 : ℤ) ≤ (m * periodLcm t : ℕ) := by
    exact_mod_cast le_trans hval hm1
  have h97 : (2 : ℤ) ^ 97 = 158456325028528675187087900672 := by norm_num
  have hLnn : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  push_cast at hfloor hbig hbig'
  rw [h97] at hpow
  linarith

/-- **Unconditional depth floor at the wall.**  Combining the two previous
results: *every* witness for the body of `G100` at any scale `t ≥ 67` — diagonal
or not, at any multipliers — needs certificate depth `L ≥ 98`. -/
theorem depth_floor_of_coneCell_beyond_66 {t : ℕ} (ht : 67 ≤ t) :
    ∀ q m L : ℕ, 0 < q →
      certifiedKill (m * periodLcm t) (q * periodLcm t) L → 98 ≤ L := by
  intro q m L hq hcert
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.zero_mul] at hcert
    exact absurd hcert (not_certifiedKill_zero_window _ _)
  · exact depth_floor_beyond_66 ht hq hm hcert

/-! ## 7.  What is actually still demanded -/

/-- Only prime-power scales carry content: a diagonal supply restricted to prime
powers already gives `G100`.  Combined with §4, the *first* open obligation of
`G100` is a single certificate at `t = 67`. -/
theorem G100_of_prime_pow_diagonal_supply
    (h : ∀ t₀ : ℕ, ∃ p k : ℕ, Nat.Prime p ∧ t₀ ≤ p ^ k ∧
      ∃ L, certifiedKill (periodLcm (p ^ k)) (periodLcm (p ^ k)) L) : G100 := by
  rw [G100_iff_coneCell_cofinal]
  intro t₀
  obtain ⟨p, k, _, hle, L, hL⟩ := h t₀
  exact ⟨p ^ k, hle, coneCell_of_diagonalKill hL⟩

/-- A non-prime-power scale is redundant outright: if `n + 1` splits into coprime
factors `≤ n`, the cone at `n + 1` **is** the cone at `n`. -/
theorem coneCell_succ_of_coprime_split {t a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hat : a ≤ t) (hbt : b ≤ t) (hab : Nat.Coprime a b) (hsplit : t + 1 = a * b)
    (hc : ConeCell t) : ConeCell (t + 1) := by
  refine coneCell_of_periodLcm_eq ?_ hc
  refine periodLcm_eq_of_forall_dvd (Nat.le_succ t) ?_
  intro k hk1 hk
  rcases Nat.lt_or_ge k (t + 1) with hlt | hge
  · exact dvd_periodLcm hk1 (by omega)
  · have hkt : k = t + 1 := by omega
    rw [hkt, hsplit]
    exact mul_dvd_periodLcm_of_coprime ha hb hat hbt hab

end DemandLedger.Discharge2G100
