/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.DemandLedger.Basic

/-!
# Historical finite-band discharge for `G097`

`G097` is the wave-23 lcm-diagonal certificate supply

  `∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (H t) (H t) L`,   `H t = periodLcm t = lcm(1..t)`,

the antecedent `hsupply` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_certificate_supply`.
This file records how far the supply available at the time reached.  Later
modules `Lift/Recon67.lean`, `Lift/CertT67.lean`, and `Skip/LadderT67.lean`
extend the current finite diagonal band through `t ≤ 82`.

## What the corpus records

Twenty-eight kernel-checked diagonal deposits
`certifiedKill_diagonal_t1 … certifiedKill_diagonal_t64`, at the scales

  `1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47,`
  `49, 53, 59, 61, 64`

— which is exactly `{1} ∪ {prime powers ≤ 64}`.  These are the deposits imported
by this module, not the current repository-wide total.

## What the corpus actually proves

`periodLcm` is a step function: `H (s+1) = H s` unless `s+1` is a prime power,
because a composite `s+1 = a·b` with `gcd(a,b) = 1` and `a, b ≤ s` already divides
`H s` (`periodLcm_plateau_of_coprime_factors`).  The predicate
`P t := ∃ L, certifiedKill (H t) (H t) L` depends on `t` only through the *value*
`H t`, so it is constant along every plateau.  Consequently the 28 deposits prove
`P t` for **every** `t ≤ 66` with no holes at all (`exists_diagonalKill_le_66`),
and in particular at the two scales `t = 65, 66` that lie beyond the corpus'
largest deposit.  The 37 "missing" scales below 64 were never missing.

## Where this module's imported band stops

`67` is the next prime power after `64`, so the plateau carrying the `t = 64`
deposit is `[64, 66]` and it ends there: `H 66 = 1182266884102822267511361600 <`
`H 67 = 79211881234889091923261227200` (`periodLcm_66_lt_periodLcm_67`).
`G097_of_diagonal_supply_above_66` is a sufficient cofinal-tail reduction at
that historical boundary.  `Lift/Recon67.lean` later certifies `t = 67`, and the
current finite band reaches `t ≤ 82`.

No finite extension can finish the job — `ClusterA.lean` proves `G097` equivalent to
Erdős #249 itself, and `G097` is a cofinal statement.  This file measures its
then-current boundary; it does not prove a cofinal supply.

## Argument coincidence found

`certifiedKill_lcm_cone_cells` advertises three cells "off the diagonal".  Its
middle cell `(t, q, m) = (3, 2, 2)` is `certifiedKill (2·H 3) (2·H 3) 7`, and
`2·H 3 = 2·6 = 12 = H 4`: that cell **is** the diagonal cell at scale `4`, at the
same depth `7` as `certifiedKill_diagonal_t4`.  Two corpus records, one fact
(`cone_cell_3_2_2_is_diagonal_t4`).
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace DemandLedger.Discharge1G097

set_option maxRecDepth 100000

/-! ## The plateau structure of the lcm ray -/

/-- **Plateau step.**  If `s + 1` factors as a product of two coprime numbers that
both already lie in the range `[1, s]`, then `s + 1` divides `lcm(1..s)` and the lcm
ray does not move: `H (s+1) = H s`.  (The converse direction is the classical fact
that `H` jumps exactly at prime powers.) -/
theorem periodLcm_plateau_of_coprime_factors {a b s : ℕ} (hcop : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hat : a ≤ s) (hbt : b ≤ s) (hab : a * b = s + 1) :
    periodLcm (s + 1) = periodLcm s := by
  have hdvd : (s + 1) ∣ periodLcm s := by
    rw [← hab]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (dvd_periodLcm ha hat) (dvd_periodLcm hb hbt)
  have h1 : periodLcm (s + 1) ∣ periodLcm s := by
    change Nat.lcm (periodLcm s) (s + 1) ∣ periodLcm s
    exact Nat.lcm_dvd dvd_rfl hdvd
  exact Nat.dvd_antisymm h1 (periodLcm_dvd_succ s)

/-- **Plateau transfer.**  The wave-23 predicate `P t` sees `t` only through the
value `H t`, so a deposit at any scale carrying the same lcm value discharges it. -/
theorem exists_diagonalKill_of_periodLcm_eq {t s L : ℕ} (h : periodLcm t = periodLcm s)
    (hk : certifiedKill (periodLcm s) (periodLcm s) L) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L :=
  ⟨L, by rw [h]; exact hk⟩

/-! ## The 38 plateaus below 67

Every non-prime-power `t ∈ [2, 66]` carries a coprime splitting `t = a·b` with
`a, b ≤ t - 1`, hence `H t = H (t-1)`.  These are the only scales at which the
corpus records no diagonal deposit. -/

/-- `H 0 = H 1 = 1`: the ray starts flat. -/
theorem pl0 : periodLcm 0 = periodLcm 1 := by decide

/-- `6 = 2 · 3`, coprime factors below `6`, so `H 6 = H 5`. -/
theorem pl6 : periodLcm 6 = periodLcm 5 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 3) (s := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `10 = 2 · 5`, coprime factors below `10`, so `H 10 = H 9`. -/
theorem pl10 : periodLcm 10 = periodLcm 9 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 5) (s := 9)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `12 = 3 · 4`, coprime factors below `12`, so `H 12 = H 11`. -/
theorem pl12 : periodLcm 12 = periodLcm 11 :=
  periodLcm_plateau_of_coprime_factors (a := 3) (b := 4) (s := 11)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `14 = 2 · 7`, coprime factors below `14`, so `H 14 = H 13`. -/
theorem pl14 : periodLcm 14 = periodLcm 13 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 7) (s := 13)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `15 = 3 · 5`, coprime factors below `15`, so `H 15 = H 14`. -/
theorem pl15 : periodLcm 15 = periodLcm 14 :=
  periodLcm_plateau_of_coprime_factors (a := 3) (b := 5) (s := 14)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `18 = 2 · 9`, coprime factors below `18`, so `H 18 = H 17`. -/
theorem pl18 : periodLcm 18 = periodLcm 17 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 9) (s := 17)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `20 = 4 · 5`, coprime factors below `20`, so `H 20 = H 19`. -/
theorem pl20 : periodLcm 20 = periodLcm 19 :=
  periodLcm_plateau_of_coprime_factors (a := 4) (b := 5) (s := 19)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `21 = 3 · 7`, coprime factors below `21`, so `H 21 = H 20`. -/
theorem pl21 : periodLcm 21 = periodLcm 20 :=
  periodLcm_plateau_of_coprime_factors (a := 3) (b := 7) (s := 20)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `22 = 2 · 11`, coprime factors below `22`, so `H 22 = H 21`. -/
theorem pl22 : periodLcm 22 = periodLcm 21 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 11) (s := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `24 = 3 · 8`, coprime factors below `24`, so `H 24 = H 23`. -/
theorem pl24 : periodLcm 24 = periodLcm 23 :=
  periodLcm_plateau_of_coprime_factors (a := 3) (b := 8) (s := 23)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `26 = 2 · 13`, coprime factors below `26`, so `H 26 = H 25`. -/
theorem pl26 : periodLcm 26 = periodLcm 25 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 13) (s := 25)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `28 = 4 · 7`, coprime factors below `28`, so `H 28 = H 27`. -/
theorem pl28 : periodLcm 28 = periodLcm 27 :=
  periodLcm_plateau_of_coprime_factors (a := 4) (b := 7) (s := 27)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `30 = 2 · 15`, coprime factors below `30`, so `H 30 = H 29`. -/
theorem pl30 : periodLcm 30 = periodLcm 29 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 15) (s := 29)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `33 = 3 · 11`, coprime factors below `33`, so `H 33 = H 32`. -/
theorem pl33 : periodLcm 33 = periodLcm 32 :=
  periodLcm_plateau_of_coprime_factors (a := 3) (b := 11) (s := 32)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `34 = 2 · 17`, coprime factors below `34`, so `H 34 = H 33`. -/
theorem pl34 : periodLcm 34 = periodLcm 33 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 17) (s := 33)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `35 = 5 · 7`, coprime factors below `35`, so `H 35 = H 34`. -/
theorem pl35 : periodLcm 35 = periodLcm 34 :=
  periodLcm_plateau_of_coprime_factors (a := 5) (b := 7) (s := 34)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `36 = 4 · 9`, coprime factors below `36`, so `H 36 = H 35`. -/
theorem pl36 : periodLcm 36 = periodLcm 35 :=
  periodLcm_plateau_of_coprime_factors (a := 4) (b := 9) (s := 35)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `38 = 2 · 19`, coprime factors below `38`, so `H 38 = H 37`. -/
theorem pl38 : periodLcm 38 = periodLcm 37 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 19) (s := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `39 = 3 · 13`, coprime factors below `39`, so `H 39 = H 38`. -/
theorem pl39 : periodLcm 39 = periodLcm 38 :=
  periodLcm_plateau_of_coprime_factors (a := 3) (b := 13) (s := 38)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `40 = 5 · 8`, coprime factors below `40`, so `H 40 = H 39`. -/
theorem pl40 : periodLcm 40 = periodLcm 39 :=
  periodLcm_plateau_of_coprime_factors (a := 5) (b := 8) (s := 39)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `42 = 2 · 21`, coprime factors below `42`, so `H 42 = H 41`. -/
theorem pl42 : periodLcm 42 = periodLcm 41 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 21) (s := 41)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `44 = 4 · 11`, coprime factors below `44`, so `H 44 = H 43`. -/
theorem pl44 : periodLcm 44 = periodLcm 43 :=
  periodLcm_plateau_of_coprime_factors (a := 4) (b := 11) (s := 43)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `45 = 5 · 9`, coprime factors below `45`, so `H 45 = H 44`. -/
theorem pl45 : periodLcm 45 = periodLcm 44 :=
  periodLcm_plateau_of_coprime_factors (a := 5) (b := 9) (s := 44)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `46 = 2 · 23`, coprime factors below `46`, so `H 46 = H 45`. -/
theorem pl46 : periodLcm 46 = periodLcm 45 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 23) (s := 45)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `48 = 3 · 16`, coprime factors below `48`, so `H 48 = H 47`. -/
theorem pl48 : periodLcm 48 = periodLcm 47 :=
  periodLcm_plateau_of_coprime_factors (a := 3) (b := 16) (s := 47)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `50 = 2 · 25`, coprime factors below `50`, so `H 50 = H 49`. -/
theorem pl50 : periodLcm 50 = periodLcm 49 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 25) (s := 49)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `51 = 3 · 17`, coprime factors below `51`, so `H 51 = H 50`. -/
theorem pl51 : periodLcm 51 = periodLcm 50 :=
  periodLcm_plateau_of_coprime_factors (a := 3) (b := 17) (s := 50)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `52 = 4 · 13`, coprime factors below `52`, so `H 52 = H 51`. -/
theorem pl52 : periodLcm 52 = periodLcm 51 :=
  periodLcm_plateau_of_coprime_factors (a := 4) (b := 13) (s := 51)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `54 = 2 · 27`, coprime factors below `54`, so `H 54 = H 53`. -/
theorem pl54 : periodLcm 54 = periodLcm 53 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 27) (s := 53)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `55 = 5 · 11`, coprime factors below `55`, so `H 55 = H 54`. -/
theorem pl55 : periodLcm 55 = periodLcm 54 :=
  periodLcm_plateau_of_coprime_factors (a := 5) (b := 11) (s := 54)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `56 = 7 · 8`, coprime factors below `56`, so `H 56 = H 55`. -/
theorem pl56 : periodLcm 56 = periodLcm 55 :=
  periodLcm_plateau_of_coprime_factors (a := 7) (b := 8) (s := 55)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `57 = 3 · 19`, coprime factors below `57`, so `H 57 = H 56`. -/
theorem pl57 : periodLcm 57 = periodLcm 56 :=
  periodLcm_plateau_of_coprime_factors (a := 3) (b := 19) (s := 56)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `58 = 2 · 29`, coprime factors below `58`, so `H 58 = H 57`. -/
theorem pl58 : periodLcm 58 = periodLcm 57 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 29) (s := 57)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `60 = 4 · 15`, coprime factors below `60`, so `H 60 = H 59`. -/
theorem pl60 : periodLcm 60 = periodLcm 59 :=
  periodLcm_plateau_of_coprime_factors (a := 4) (b := 15) (s := 59)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `62 = 2 · 31`, coprime factors below `62`, so `H 62 = H 61`. -/
theorem pl62 : periodLcm 62 = periodLcm 61 :=
  periodLcm_plateau_of_coprime_factors (a := 2) (b := 31) (s := 61)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `63 = 7 · 9`, coprime factors below `63`, so `H 63 = H 62`. -/
theorem pl63 : periodLcm 63 = periodLcm 62 :=
  periodLcm_plateau_of_coprime_factors (a := 7) (b := 9) (s := 62)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `65 = 5 · 13`, coprime factors below `65`, so `H 65 = H 64`. -/
theorem pl65 : periodLcm 65 = periodLcm 64 :=
  periodLcm_plateau_of_coprime_factors (a := 5) (b := 13) (s := 64)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `66 = 6 · 11`, coprime factors below `66`, so `H 66 = H 65`. -/
theorem pl66 : periodLcm 66 = periodLcm 65 :=
  periodLcm_plateau_of_coprime_factors (a := 6) (b := 11) (s := 65)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## The reach: every scale `t ≤ 66` fires -/

/-- **The supply reach.**  The wave-23 diagonal predicate
`P t := ∃ L, certifiedKill (H t) (H t) L` holds at EVERY `t ≤ 66` — not merely at
the 28 scales where the corpus deposits a certificate.  Prime-power scales use
their own deposit; the other 38 scales inherit it across the plateau `H t = H (t-1)`.
Two of these scales, `t = 65` and `t = 66`, lie strictly above the largest corpus
deposit `certifiedKill_diagonal_t64`. -/
theorem exists_diagonalKill_le_66 (t : ℕ) (ht : t ≤ 66) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L := by
  interval_cases t
  · exact exists_diagonalKill_of_periodLcm_eq pl0 certifiedKill_diagonal_t1
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t1
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t2
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t3
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t4
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t5
  · exact exists_diagonalKill_of_periodLcm_eq (pl6) certifiedKill_diagonal_t5
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t7
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t8
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t9
  · exact exists_diagonalKill_of_periodLcm_eq (pl10) certifiedKill_diagonal_t9
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t11
  · exact exists_diagonalKill_of_periodLcm_eq (pl12) certifiedKill_diagonal_t11
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t13
  · exact exists_diagonalKill_of_periodLcm_eq (pl14) certifiedKill_diagonal_t13
  · exact exists_diagonalKill_of_periodLcm_eq (pl15.trans pl14) certifiedKill_diagonal_t13
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t16
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t17
  · exact exists_diagonalKill_of_periodLcm_eq (pl18) certifiedKill_diagonal_t17
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t19
  · exact exists_diagonalKill_of_periodLcm_eq (pl20) certifiedKill_diagonal_t19
  · exact exists_diagonalKill_of_periodLcm_eq (pl21.trans pl20) certifiedKill_diagonal_t19
  · exact exists_diagonalKill_of_periodLcm_eq (pl22.trans (pl21.trans pl20)) certifiedKill_diagonal_t19
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t23
  · exact exists_diagonalKill_of_periodLcm_eq (pl24) certifiedKill_diagonal_t23
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t25
  · exact exists_diagonalKill_of_periodLcm_eq (pl26) certifiedKill_diagonal_t25
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t27
  · exact exists_diagonalKill_of_periodLcm_eq (pl28) certifiedKill_diagonal_t27
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t29
  · exact exists_diagonalKill_of_periodLcm_eq (pl30) certifiedKill_diagonal_t29
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t31
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t32
  · exact exists_diagonalKill_of_periodLcm_eq (pl33) certifiedKill_diagonal_t32
  · exact exists_diagonalKill_of_periodLcm_eq (pl34.trans pl33) certifiedKill_diagonal_t32
  · exact exists_diagonalKill_of_periodLcm_eq (pl35.trans (pl34.trans pl33)) certifiedKill_diagonal_t32
  · exact exists_diagonalKill_of_periodLcm_eq (pl36.trans (pl35.trans (pl34.trans pl33))) certifiedKill_diagonal_t32
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t37
  · exact exists_diagonalKill_of_periodLcm_eq (pl38) certifiedKill_diagonal_t37
  · exact exists_diagonalKill_of_periodLcm_eq (pl39.trans pl38) certifiedKill_diagonal_t37
  · exact exists_diagonalKill_of_periodLcm_eq (pl40.trans (pl39.trans pl38)) certifiedKill_diagonal_t37
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t41
  · exact exists_diagonalKill_of_periodLcm_eq (pl42) certifiedKill_diagonal_t41
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t43
  · exact exists_diagonalKill_of_periodLcm_eq (pl44) certifiedKill_diagonal_t43
  · exact exists_diagonalKill_of_periodLcm_eq (pl45.trans pl44) certifiedKill_diagonal_t43
  · exact exists_diagonalKill_of_periodLcm_eq (pl46.trans (pl45.trans pl44)) certifiedKill_diagonal_t43
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t47
  · exact exists_diagonalKill_of_periodLcm_eq (pl48) certifiedKill_diagonal_t47
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t49
  · exact exists_diagonalKill_of_periodLcm_eq (pl50) certifiedKill_diagonal_t49
  · exact exists_diagonalKill_of_periodLcm_eq (pl51.trans pl50) certifiedKill_diagonal_t49
  · exact exists_diagonalKill_of_periodLcm_eq (pl52.trans (pl51.trans pl50)) certifiedKill_diagonal_t49
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t53
  · exact exists_diagonalKill_of_periodLcm_eq (pl54) certifiedKill_diagonal_t53
  · exact exists_diagonalKill_of_periodLcm_eq (pl55.trans pl54) certifiedKill_diagonal_t53
  · exact exists_diagonalKill_of_periodLcm_eq (pl56.trans (pl55.trans pl54)) certifiedKill_diagonal_t53
  · exact exists_diagonalKill_of_periodLcm_eq (pl57.trans (pl56.trans (pl55.trans pl54))) certifiedKill_diagonal_t53
  · exact exists_diagonalKill_of_periodLcm_eq (pl58.trans (pl57.trans (pl56.trans (pl55.trans pl54)))) certifiedKill_diagonal_t53
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t59
  · exact exists_diagonalKill_of_periodLcm_eq (pl60) certifiedKill_diagonal_t59
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t61
  · exact exists_diagonalKill_of_periodLcm_eq (pl62) certifiedKill_diagonal_t61
  · exact exists_diagonalKill_of_periodLcm_eq (pl63.trans pl62) certifiedKill_diagonal_t61
  · exact exists_diagonalKill_of_periodLcm_eq (rfl) certifiedKill_diagonal_t64
  · exact exists_diagonalKill_of_periodLcm_eq (pl65) certifiedKill_diagonal_t64
  · exact exists_diagonalKill_of_periodLcm_eq (pl66.trans pl65) certifiedKill_diagonal_t64

/-! ## The two scales added by this module, isolated -/

/-- `t = 65`: `H 65 = H 64` because `65 = 5·13`. -/
theorem exists_diagonalKill_at_65 : ∃ L, certifiedKill (periodLcm 65) (periodLcm 65) L :=
  exists_diagonalKill_of_periodLcm_eq pl65 certifiedKill_diagonal_t64

/-- `t = 66`: `H 66 = H 65 = H 64` because `66 = 6·11` and `65 = 5·13`. -/
theorem exists_diagonalKill_at_66 : ∃ L, certifiedKill (periodLcm 66) (periodLcm 66) L :=
  exists_diagonalKill_of_periodLcm_eq (pl66.trans pl65) certifiedKill_diagonal_t64

/-! ## The historical wall at 67 -/

/-- The plateau carrying the `t = 64` deposit is exactly `[64, 66]`. -/
theorem periodLcm_plateau_64_66 :
    periodLcm 64 = 1182266884102822267511361600 ∧
      periodLcm 65 = periodLcm 64 ∧ periodLcm 66 = periodLcm 64 :=
  ⟨by decide, pl65, pl66.trans pl65⟩

/-- `67` is prime, so the ray jumps relative to the band constructed in this
module.  Later modules certify this modulus and extend the band through `t ≤ 82`. -/
theorem periodLcm_66_lt_periodLcm_67 : periodLcm 66 < periodLcm 67 := by decide

/-- The exact size of the next diagonal jump after this module's band.
`Lift/Recon67.lean` later certifies this cell. -/
theorem periodLcm_67_eq : periodLcm 67 = 79211881234889091923261227200 := by decide

/-- And it is `67` times the last certified one. -/
theorem periodLcm_67_eq_67_mul_periodLcm_66 : periodLcm 67 = 67 * periodLcm 66 := by decide

/-! ## What remains of `G097` -/

/-- **A sufficient residual obligation at this module's historical boundary.**
`G097` follows from diagonal kills at
scales `≥ 67` alone: every threshold `t₀ ≤ 66` is already met by the deposits, using
the witness `t = 66`.  Later modules close additional finite cells through
`t ≤ 82`; the cofinal obligation remains open. -/
theorem G097_of_diagonal_supply_above_66
    (h : ∀ t₀ : ℕ, 67 ≤ t₀ → ∃ t, t₀ ≤ t ∧ ∃ L, certifiedKill (periodLcm t) (periodLcm t) L) :
    G097 := by
  unfold G097
  intro t₀
  rcases Nat.lt_or_ge t₀ 67 with hlt | hge
  · exact ⟨66, by omega, exists_diagonalKill_at_66⟩
  · exact h t₀ hge

/-- The bounded form of `G097`: true, and kernel-checked, for every threshold up to
`66`.  This is the precise strength of the proved supply — one more step and it is
`G097` itself, hence Erdős #249. -/
theorem G097_bounded (t₀ : ℕ) (ht₀ : t₀ ≤ 66) :
    ∃ t, t₀ ≤ t ∧ ∃ L, certifiedKill (periodLcm t) (periodLcm t) L :=
  ⟨66, ht₀, exists_diagonalKill_at_66⟩

/-! ## An argument coincidence in the recorded supply -/

/-- `2 · H 3 = 12 = H 4`. -/
theorem two_mul_periodLcm_three : 2 * periodLcm 3 = periodLcm 4 := by decide

/-- **The cone cell `(t, q, m) = (3, 2, 2)` is the diagonal cell at `t = 4`.**
`certifiedKill_lcm_cone_cells` is documented as recording "the first machine-checked
annihilators off the diagonal", but its middle conjunct has `h = N = 2·H 3 = 12`,
and `H 4 = 12`.  It is `certifiedKill_diagonal_t4` again, at the same depth `7`. -/
theorem cone_cell_3_2_2_is_diagonal_t4 : certifiedKill (periodLcm 4) (periodLcm 4) 7 := by
  have h := certifiedKill_lcm_cone_cells.2.1
  rwa [two_mul_periodLcm_three] at h

/-- The two records inhabit the *same* proposition.  The proof is `rfl` by proof
irrelevance, so the content is entirely in well-formedness: this equation typechecks
only because `certifiedKill (2 · H 3) (2 · H 3) 7` and `certifiedKill (H 4) (H 4) 7`
are literally one statement.  Two frontier deposits, one fact. -/
theorem cone_cell_eq_diagonal_deposit :
    cone_cell_3_2_2_is_diagonal_t4 = certifiedKill_diagonal_t4 := rfl

/-! ## The measurement, in one statement -/

/-- **How far the proved supply for `G097` reaches, and where it stops.**  The 28
recorded diagonal deposits certify 28 distinct lcm values; the plateau structure of
the ray turns them into an unbroken run of 67 consecutive scales `t = 0, …, 66`, two
of them (`65, 66`) above the largest deposit.  And there the run ends: `67` is the
next prime power, `H` jumps, and the corpus contains no declaration about the cell
`(H 67, H 67)`.  `G097` is cofinal, so this — or any finite extension of it — leaves
the gap exactly where it was. -/
theorem G097_supply_reach :
    (∀ t : ℕ, t ≤ 66 → ∃ L, certifiedKill (periodLcm t) (periodLcm t) L)
      ∧ periodLcm 66 < periodLcm 67 :=
  ⟨exists_diagonalKill_le_66, periodLcm_66_lt_periodLcm_67⟩

end DemandLedger.Discharge1G097
