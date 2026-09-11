/-
Supply-side attack on `DemandLedger.G103`.

`G103` is the antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_lcm_window_kill_supply`, i.e.

    ∀ t₀ N₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ L,
      certifiedKill (periodLcm t) N L

The predicate to instantiate is `TotientTailPeriodKiller.certifiedKill` at the
one-parameter period ray `periodLcm t = lcm (1..t)`.

This file records three things.

1.  `G103` is not a proper antecedent of Erdős #249 at all: it is *equivalent*
    to it.  The corpus already proves certificate completeness
    (`irrational_totient_series_iff_pointwise_certificates`), which supplies the
    reverse direction.  So `G103` collapses onto the target, and onto `G097`.

2.  What the proved supply actually reaches: the recorded diagonal pincer
    certificates stop at `t = 64`.  An argument coincidence pushes that to
    `t = 66` for free — `periodLcm 64 = periodLcm 65 = periodLcm 66`, because
    `65 = 5·13` and `66 = 2·3·11` already divide `lcm (1..64)` — and the
    plateau is exactly `{64, 65, 66}` since `67` is prime.

3.  Why no finite supply ever discharges it: the certificate's own dyadic room
    condition forbids a supply at any fixed depth.
-/
import ErdosProblems.DemandLedger.Basic

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace DemandLedger.Discharge3G103

/-! ## 1.  `G103` is a normal form for #249, not a strictly stronger antecedent -/

/-- Forward direction: this is the kernel's own wave-23 endpoint collapse. -/
theorem G103_imp_erdos249 :
    G103 → Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G103
  intro h
  exact Erdos249257.irrational_totient_series_of_lcm_window_kill_supply h

/-- Reverse direction.  Certificate completeness
(`irrational_totient_series_iff_pointwise_certificates`) turns irrationality
into a certificate at *every* `(h, N)` with `h > 0`; taking `h = periodLcm t₀`
(positive) and `N = N₀` discharges the supply at `t = t₀`, `N = N₀`. -/
theorem erdos249_imp_G103 :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) → G103 := by
  unfold G103
  intro hirr t₀ N₀
  refine ⟨t₀, le_rfl, N₀, le_rfl, ?_⟩
  exact irrational_totient_series_iff_pointwise_certificates.mp hirr
    (periodLcm t₀) (periodLcm_pos t₀) N₀

/-- **`G103` is Erdős #249.**  The ledger entry is a restatement of the target,
so no supply argument can discharge it without proving #249. -/
theorem G103_iff_erdos249 :
    G103 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨G103_imp_erdos249, erdos249_imp_G103⟩

/-- **Collapse of two ledger records.**  `G097` (the diagonal certificate
supply) and `G103` (the general-position window supply) are mutually implied:
both are normal forms for #249. -/
theorem G103_iff_G097 : G103 ↔ G097 := by
  unfold G097
  constructor
  · intro h
    exact irrational_totient_series_iff_lcm_diagonal_certificate_supply.mp
      (G103_imp_erdos249 h)
  · intro h
    exact erdos249_imp_G103
      (irrational_totient_series_of_lcm_diagonal_certificate_supply h)

theorem G097_imp_G103 : G097 → G103 := G103_iff_G097.mpr

theorem G103_imp_G097 : G103 → G097 := G103_iff_G097.mp

/-! ## 2.  How far the proved supply reaches

The recorded certificates for the predicate `certifiedKill (periodLcm t) N L`
are the diagonal pincer deposits `certifiedKill_diagonal_t*`, whose largest
scale is `t = 64` (`certifiedKill (periodLcm 64) (periodLcm 64) 93`).
-/

/-- The complete recorded supply for the `G103` predicate: `28` diagonal
deposits, at scales `1,2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,
43,47,49,53,59,61,64`.  Every one of them sits on the diagonal `N = periodLcm t`. -/
theorem G103_recorded_supply :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t)
        (diagonalPincerKillDepthThroughT64 t) :=
  certifiedKill_diagonal_all_imported_through_t64

/-- The deepest recorded deposit, and the one that fixes the whole reach. -/
theorem G103_deepest_recorded_deposit :
    certifiedKill (periodLcm 64) (periodLcm 64) 93 :=
  certifiedKill_diagonal_t64

/-- `periodLcm` is flat across an endpoint that already divides it. -/
theorem periodLcm_stable {t : ℕ} (hdvd : (t + 1) ∣ periodLcm t) :
    periodLcm (t + 1) = periodLcm t := by
  change Nat.lcm (periodLcm t) (t + 1) = periodLcm t
  exact Nat.lcm_eq_left_iff_dvd.mpr hdvd

/-- `65 = 5 · 13` and both factors are `≤ 64`. -/
theorem dvd_sixtyfive_periodLcm : (65 : ℕ) ∣ periodLcm 64 := by
  have h5 : (5 : ℕ) ∣ periodLcm 64 := dvd_periodLcm (by norm_num) (by norm_num)
  have h13 : (13 : ℕ) ∣ periodLcm 64 := dvd_periodLcm (by norm_num) (by norm_num)
  have hcop : Nat.Coprime 5 13 := by decide
  simpa using hcop.mul_dvd_of_dvd_of_dvd h5 h13

/-- `66 = 6 · 11` and both factors are `≤ 64`. -/
theorem dvd_sixtysix_periodLcm : (66 : ℕ) ∣ periodLcm 64 := by
  have h6 : (6 : ℕ) ∣ periodLcm 64 := dvd_periodLcm (by norm_num) (by norm_num)
  have h11 : (11 : ℕ) ∣ periodLcm 64 := dvd_periodLcm (by norm_num) (by norm_num)
  have hcop : Nat.Coprime 6 11 := by decide
  simpa using hcop.mul_dvd_of_dvd_of_dvd h6 h11

theorem periodLcm_65_eq_64 : periodLcm 65 = periodLcm 64 :=
  periodLcm_stable (t := 64) (by simpa using dvd_sixtyfive_periodLcm)

theorem periodLcm_66_eq_64 : periodLcm 66 = periodLcm 64 := by
  have h : periodLcm 66 = periodLcm 65 :=
    periodLcm_stable (t := 65)
      (by rw [periodLcm_65_eq_64]; simpa using dvd_sixtysix_periodLcm)
  rw [h, periodLcm_65_eq_64]

/-- **Argument coincidence, new instance.**  The corpus records the endpoint
certificate at `periodLcm 64`; the same natural number is `periodLcm 65`, so
the deposit is simultaneously a diagonal kill at scale `t = 65`. -/
theorem certifiedKill_diagonal_t65 :
    certifiedKill (periodLcm 65) (periodLcm 65) 93 := by
  rw [periodLcm_65_eq_64]
  exact certifiedKill_diagonal_t64

/-- Likewise at `t = 66`, the top of the plateau. -/
theorem certifiedKill_diagonal_t66 :
    certifiedKill (periodLcm 66) (periodLcm 66) 93 := by
  rw [periodLcm_66_eq_64]
  exact certifiedKill_diagonal_t64

/-- The plateau really stops at `66`: `67` is prime, so it does not divide
`lcm (1..64)` and `periodLcm 67` is a strictly larger height. -/
theorem periodLcm_67_gt : periodLcm 66 < periodLcm 67 := by
  refine (Erdos249257.DiagonalFreshLossBridge.periodLcm_strict_jump_iff_succ_not_dvd 66).2 ?_
  rw [periodLcm_66_eq_64]
  intro hdvd
  have hval : periodLcm 64 = 1182266884102822267511361600 := by
    norm_num [periodLcm]
  rw [hval] at hdvd
  norm_num at hdvd

/-- **The exact reach of the proved supply.**  The body of `G103` is
kernel-proved at every `(t₀, N₀)` with `t₀ ≤ 66` and
`N₀ ≤ periodLcm 64 = 1182266884102822267511361600`. -/
theorem G103_body_at_reach (t₀ N₀ : ℕ) (ht : t₀ ≤ 66) (hN : N₀ ≤ periodLcm 66) :
    ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (periodLcm t) N L :=
  ⟨66, ht, periodLcm 66, hN, 93, certifiedKill_diagonal_t66⟩

/-- The same reach with the `N` bound as an explicit numeral. -/
theorem G103_body_at_reach_numeral (t₀ N₀ : ℕ) (ht : t₀ ≤ 66)
    (hN : N₀ ≤ 1182266884102822267511361600) :
    ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (periodLcm t) N L := by
  refine G103_body_at_reach t₀ N₀ ht ?_
  have hval : periodLcm 64 = 1182266884102822267511361600 := by
    norm_num [periodLcm]
  rw [periodLcm_66_eq_64, hval]
  exact hN

/-! ## 3.  Where it stops, and why finitely many deposits never suffice -/

/-- **No fixed-depth supply.**  The certificate's own dyadic room condition
(`certifiedKill_depth_floor`: `2·(N + h + L + 2) < 2^L`) makes a `G103`-shaped
supply at a *fixed* depth `L` contradictory, because it would have to fire at
some `N ≥ 2^L`.  Hence any supply discharging `G103` has depths tending to
infinity, and no finite set of deposits — the corpus records `28` of them,
maximal depth `94` — can be extended to one by bookkeeping alone. -/
theorem G103_no_fixed_depth_supply (L : ℕ) :
    ¬ ∀ t₀ N₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ certifiedKill (periodLcm t) N L := by
  intro hsup
  obtain ⟨t, -, N, hN, hcert⟩ := hsup 0 (2 ^ L)
  have hfloor := certifiedKill_depth_floor hcert
  have hNz : ((2 : ℤ) ^ L) ≤ (N : ℤ) := by exact_mod_cast hN
  have h1 : (0 : ℤ) ≤ (periodLcm t : ℤ) := Int.natCast_nonneg _
  have h2 : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg _
  have h3 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg _
  push_cast at hfloor
  linarith

/-- The same obstruction in `G103`'s own words: a genuine supply must produce
certificates at unbounded depth. -/
theorem G103_forces_unbounded_depth (h : G103) :
    ∀ L₀ : ℕ, ∃ t N L, L₀ ≤ L ∧ certifiedKill (periodLcm t) N L := by
  unfold G103 at h
  intro L₀
  obtain ⟨t, -, N, hN, L, hcert⟩ := h 0 (2 ^ L₀)
  refine ⟨t, N, L, ?_, hcert⟩
  by_contra hge
  have hlt : L < L₀ := by omega
  have hfloor := certifiedKill_depth_floor hcert
  have hNz : ((2 : ℤ) ^ L₀) ≤ (N : ℤ) := by exact_mod_cast hN
  have hmono : ((2 : ℤ) ^ L) ≤ (2 : ℤ) ^ L₀ :=
    pow_le_pow_right₀ (by norm_num) (le_of_lt hlt)
  have h1 : (0 : ℤ) ≤ (periodLcm t : ℤ) := Int.natCast_nonneg _
  have h2 : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg _
  have h3 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg _
  push_cast at hfloor
  linarith

/-- `G103` also forces the *period* to be unbounded, so the reach in `t` — not
only the reach in `N` — is the binding constraint: the proved supply stops at
`t = 66`, i.e. at period height `1182266884102822267511361600`. -/
theorem G103_forces_unbounded_period (h : G103) :
    ∀ H : ℕ, ∃ t N L, H ≤ periodLcm t ∧ certifiedKill (periodLcm t) N L := by
  unfold G103 at h
  intro H
  obtain ⟨t, ht, N, -, L, hcert⟩ := h H 0
  exact ⟨t, N, L, le_trans ht (le_periodLcm t), hcert⟩

end DemandLedger.Discharge3G103
