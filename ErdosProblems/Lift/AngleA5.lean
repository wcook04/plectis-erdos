/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.LcmDiagonalReduction

/-!
# Angle A5: a restricted no-lift theorem for the lcm ladder

`DemandLedger.Discharge1G097.exists_diagonalKill_le_66` certifies every rung
`t ≤ 66` of the lcm ray `H t = periodLcm t`, and
`irrational_totient_series_of_lcm_diagonal_certificate_supply` converts a
cofinal supply of diagonal kills into Erdős #249.  Later modules extend the
finite certified band, but the cofinal supply remains open.  One proposed route
to that supply is a uniform **lift**

  `certifiedKill H H L → ⟨conditions on p, H⟩ → ∃ L', certifiedKill (p*H) (p*H) L'`

at each prime-power boundary.

**PROVED here:** one precise uniform lift schema does not follow from only
(i) the size bound `a n ≤ n`, (ii) agreement with `φ` through twice the new
rung, and (iii) a lower-rung certificate whose window lies in that range.
This does not rule out a lift using additional properties specific to `φ`,
direct certificates at later rungs, or every other kind of upward argument.

## The construction

The window predicate reads the digit source only at its `2L` window positions.
The uniform lift schema formalized below also assumes the size bound
`a n ≤ n`, which `φ` satisfies.  No soundness theorem for an arbitrary source
`a` is asserted here.  Fix a rung `m` and define the **surrogate**

  `surrogate m n = φ n`                                  if `n ≤ 2m`
  `surrogate m n = φ (m + 1 + ((n-1) % m))`              if `n > 2m`

i.e. copy `φ` verbatim up to `2m`, then repeat the block `(m, 2m]` forever.
Then:

* `surrogate_le`      : `surrogate m n ≤ n` — it is an admissible digit source;
* `surrogate_of_le`   : it agrees with `φ` on **all** of `[0, 2m]`, hence
  reproduces every certificate whose full window lies in `[0, 2m]`
  (`surrogate_inherits_low_certificates`);
* `surrogate_no_certificate_at_multiple` : it has **no** certificate at `m`,
  nor at any multiple of `m`, at **any** depth `L` and **any** position
  `N ≥ m`.

The last item is forced: the diagonal cell at rung `m` compares the windows
`(m, m+L]` and `(2m, 2m+L]`, and the surrogate makes those two windows equal,
so `absWindowDiscrepancy = 0` identically.

## What this rules out

`no_lift_from_lower_totient_data` is the headline: the schema

  "for every admissible digit source `a` that agrees with `φ` below
   `2·H_{t+1}`, a certificate at rung `t` yields a certificate at rung `t+1`"

is **false**, witnessed at the genuine prime-power boundary
`t = 2 → t+1 = 3` (`p = 3`, `H_2 = 2`, `H_3 = 6`) using the kernel-checked
deposit `certifiedKill 2 2 8`.

For every rung, `no_lift_from_data_below` constructs an admissible surrogate
with the same lower data and no abstract certificate at that rung or any
multiple.  `no_lift_at_lcm_rung` specializes this obstruction to
`m = periodLcm (t+1)`.  At a particular boundary it refutes a lift only when a
lower certificate satisfying the displayed window bound is also available;
the headline theorem supplies such a witness at `t = 2 → 3`.

At the `t = 66 → 67` boundary, the same surrogate shows that the rung-66
certificate, agreement below `2·H_67`, and the size bound alone do not force a
rung-67 certificate for an arbitrary admissible source.  This is a limitation
of that inference schema, not a negative statement about the genuine totient
sequence: `Lift.Recon67.certifiedKill_diagonal_t67` later proves the genuine
rung-67 certificate directly at depth `100` (the necessary depth floor is
`98`).

## The companion positive law

The last section proves the implication that *is* available, and it runs the
other way: `tail_diff_notMem_int_of_certifiedKill_dvd` shows a single
certificate at period `h`, position `N` refutes integrality at **every divisor
of `h`** at the same `N` (via forward propagation of integrality along the
carry recurrence, `tail_diff_mem_int_of_le`).  So one diagonal deposit at `H_t`
already carries every period dividing `H_t`
(`periodLcm_diagonal_kills_all_small_periods`).  Thus the implications proved
in this file run downward under divisibility of the period and forward in
`N`; the restricted reverse schema above fails.  No classification of every
possible implication between certificates is claimed.

This is a negative result and it is unconditional: nothing here assumes or
implies anything about the value of `∑ φ(n)/2ⁿ`.
-/

namespace ErdosProblems
namespace Lift
namespace AngleA5

open Erdos249257.TotientTailPeriodKiller
open Finset

/-! ## The certificate predicate for an arbitrary digit source -/

/-- The window discrepancy of an arbitrary digit source `a : ℕ → ℕ`.  Taking
`a = Nat.totient` gives `windowDiscrepancy` on the nose. -/
def absWindowDiscrepancy (a : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((a (N + h + 1 + j) : ℤ) - (a (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

/-- The certificate predicate for an arbitrary digit source `a : ℕ → ℕ`.
Taking `a = Nat.totient` gives `certifiedKill` on the nose. -/
def absCertifiedKill (a : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < absWindowDiscrepancy a h N L % 2 ^ L ∧
    absWindowDiscrepancy a h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

/-- Faithfulness: the abstract discrepancy at `a = φ` *is* `windowDiscrepancy`. -/
theorem absWindowDiscrepancy_totient (h N L : ℕ) :
    absWindowDiscrepancy Nat.totient h N L = windowDiscrepancy h N L := rfl

/-- Faithfulness: the abstract certificate at `a = φ` *is* `certifiedKill`. -/
theorem absCertifiedKill_totient (h N L : ℕ) :
    absCertifiedKill Nat.totient h N L ↔ certifiedKill h N L := Iff.rfl

/-- The certificate at `(h, N, L)` depends on the digit source only through its
values at indices `≤ N + h + L`. -/
theorem absWindowDiscrepancy_congr {a b : ℕ → ℕ} {h N L : ℕ}
    (hab : ∀ n, n ≤ N + h + L → a n = b n) :
    absWindowDiscrepancy a h N L = absWindowDiscrepancy b h N L := by
  unfold absWindowDiscrepancy
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjL : j < L := Finset.mem_range.mp hj
  rw [hab _ (by omega), hab _ (by omega)]

/-- A vanishing discrepancy is never a certificate: the exclusion radius is
strictly positive, so residue `0` always sits in the forbidden zone. -/
theorem not_absCertifiedKill_of_eq_zero {a : ℕ → ℕ} {h N L : ℕ}
    (h0 : absWindowDiscrepancy a h N L = 0) : ¬ absCertifiedKill a h N L := by
  rintro ⟨hlow, -⟩
  rw [h0, Int.zero_emod] at hlow
  have hN : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hh : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  have hL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  linarith

/-- **Periodic annihilation.**  If the digit source repeats with period `m`
from position `m + 1` on, then every window at a period divisible by `m` has
discrepancy exactly `0`, at every position `N ≥ m` and every depth. -/
theorem absWindowDiscrepancy_eq_zero_of_periodic {a : ℕ → ℕ} {m h N L : ℕ}
    (hdvd : m ∣ h) (hper : ∀ k n, m + 1 ≤ n → a (n + k * m) = a n) (hN : m ≤ N) :
    absWindowDiscrepancy a h N L = 0 := by
  obtain ⟨k, rfl⟩ := hdvd
  unfold absWindowDiscrepancy
  refine Finset.sum_eq_zero fun j _ => ?_
  have hrw : N + m * k + 1 + j = (N + 1 + j) + k * m := by ring
  have hval : a (N + m * k + 1 + j) = a (N + 1 + j) := by
    rw [hrw]; exact hper k _ (by omega)
  rw [hval]
  ring

/-! ## The surrogate: copy `φ` below `2m`, then repeat the block `(m, 2m]` -/

/-- The **surrogate digit source at rung `m`**: identical to `φ` on `[0, 2m]`,
and `m`-periodic above.  It is admissible (`surrogate_le`) and it is blind to
every certificate at a multiple of `m`. -/
def surrogate (m n : ℕ) : ℕ :=
  if n ≤ 2 * m then Nat.totient n else Nat.totient (m + 1 + ((n - 1) % m))

theorem surrogate_of_le {m n : ℕ} (h : n ≤ 2 * m) : surrogate m n = Nat.totient n :=
  if_pos h

theorem surrogate_of_gt {m n : ℕ} (h : 2 * m < n) :
    surrogate m n = Nat.totient (m + 1 + ((n - 1) % m)) :=
  if_neg (Nat.not_le.mpr h)

/-- The surrogate is an admissible digit source: `a n ≤ n`, which is the only
analytic property of `φ` used anywhere in the certificate soundness spine. -/
theorem surrogate_le (m : ℕ) (hm : 0 < m) (n : ℕ) : surrogate m n ≤ n := by
  rcases Nat.lt_or_ge (2 * m) n with hgt | hle
  · rw [surrogate_of_gt hgt]
    have hmod : (n - 1) % m < m := Nat.mod_lt _ hm
    calc Nat.totient (m + 1 + ((n - 1) % m)) ≤ m + 1 + ((n - 1) % m) := Nat.totient_le _
      _ ≤ n := by omega
  · rw [surrogate_of_le hle]; exact Nat.totient_le n

/-- **The surrogate takes only genuine totient values, in the right residue
class.**  At every position `n` it equals `φ k` for some `1 ≤ k ≤ n` with
`k ≡ n [MOD m]`.  Consequently a property that is known to depend only on
that value and residue can be transferred after its dependence has been
proved.  This theorem does not assert that the surrogate shares every
analytic or factorization property of `φ`; parity is established separately
by `surrogate_even`. -/
theorem surrogate_eq_totient_congr (m : ℕ) (hm : 0 < m) {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ k % m = n % m ∧ surrogate m n = Nat.totient k := by
  rcases Nat.lt_or_ge (2 * m) n with hgt | hle
  · have hmod : (n - 1) % m < m := Nat.mod_lt _ hm
    refine ⟨m + 1 + ((n - 1) % m), by omega, by omega, ?_, surrogate_of_gt hgt⟩
    show Nat.ModEq m (m + 1 + ((n - 1) % m)) n
    calc m + 1 + ((n - 1) % m)
        ≡ m + 1 + (n - 1) [MOD m] := Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
      _ = m + n := by omega
      _ ≡ 0 + n [MOD m] := Nat.ModEq.add_right _ (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
      _ = n := by omega
  · exact ⟨n, hn, le_rfl, rfl, surrogate_of_le hle⟩

/-- At every position `n ≥ 3`, both the surrogate and `φ` are even.  Thus this
basic parity test does not distinguish them on the stated range. -/
theorem surrogate_even (m : ℕ) (hm : 2 ≤ m) {n : ℕ} (hn : 3 ≤ n) :
    Even (surrogate m n) := by
  rcases Nat.lt_or_ge (2 * m) n with hgt | hle
  · rw [surrogate_of_gt hgt]; exact Nat.totient_even (by omega)
  · rw [surrogate_of_le hle]; exact Nat.totient_even (by omega)

/-- One period step. -/
theorem surrogate_add (m : ℕ) (hm : 0 < m) {n : ℕ} (hn : m + 1 ≤ n) :
    surrogate m (n + m) = surrogate m n := by
  have hgt : 2 * m < n + m := by omega
  rw [surrogate_of_gt hgt]
  have hshift : n + m - 1 = (n - 1) + m := by omega
  rw [hshift, Nat.add_mod_right]
  rcases Nat.lt_or_ge (2 * m) n with hgt2 | hle
  · rw [surrogate_of_gt hgt2]
  · rw [surrogate_of_le hle]
    have h1 : (n - 1) % m = n - 1 - m := by
      rw [Nat.mod_eq_sub_mod (by omega : m ≤ n - 1), Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    congr 1
    omega

/-- Full periodicity above `m`. -/
theorem surrogate_add_mul (m : ℕ) (hm : 0 < m) (k : ℕ) {n : ℕ} (hn : m + 1 ≤ n) :
    surrogate m (n + k * m) = surrogate m n := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hrw : n + (k + 1) * m = (n + k * m) + m := by ring
      rw [hrw, surrogate_add m hm (le_trans hn (Nat.le_add_right n (k * m))), ih]

/-! ## The two halves of the no-go -/

/-- **Every certificate below the rung survives.**  Any `certifiedKill h N L`
whose whole window sits below `2m` is inherited verbatim by the surrogate.  In
particular the surrogate reproduces every deposit of
`exists_diagonalKill_le_66` when `m` is the next rung. -/
theorem surrogate_inherits_low_certificates {m h N L : ℕ} (hb : N + h + L ≤ 2 * m)
    (hcert : certifiedKill h N L) : absCertifiedKill (surrogate m) h N L := by
  have hw : absWindowDiscrepancy (surrogate m) h N L = windowDiscrepancy h N L := by
    rw [← absWindowDiscrepancy_totient]
    exact absWindowDiscrepancy_congr fun n hn => surrogate_of_le (by omega)
  exact ⟨by rw [hw]; exact hcert.1, by rw [hw]; exact hcert.2⟩

/-- **No certificate at the rung, or above it.**  For every period divisible by
`m`, every position `N ≥ m` and every depth `L`, the surrogate has no
certificate.  In particular the entire remaining lcm ladder
`periodLcm t' , t' ≥ t+1` is dead for the surrogate at rung `periodLcm (t+1)`. -/
theorem surrogate_no_certificate_at_multiple {m h N L : ℕ} (hm : 0 < m) (hdvd : m ∣ h)
    (hN : m ≤ N) : ¬ absCertifiedKill (surrogate m) h N L :=
  not_absCertifiedKill_of_eq_zero
    (absWindowDiscrepancy_eq_zero_of_periodic hdvd
      (fun k _ hn => surrogate_add_mul m hm k hn) hN)

/-- **The obstruction, packaged.**  At every rung `m` there is an admissible digit
source that (i) agrees with `φ` on all of `[0, 2m]`, (ii) therefore inherits
every certificate whose window lies below `2m`, and (iii) has no certificate
whatsoever at `m` or at any multiple of `m`, at any depth and any position
`N ≥ m`.  Therefore the corresponding uniform implication is not a
consequence of only lower agreement, inherited certificates, and the size
bound. -/
theorem no_lift_from_data_below (m : ℕ) (hm : 0 < m) :
    ∃ a : ℕ → ℕ,
      (∀ n, a n ≤ n) ∧
      (∀ n, n ≤ 2 * m → a n = Nat.totient n) ∧
      (∀ h N L, N + h + L ≤ 2 * m → certifiedKill h N L → absCertifiedKill a h N L) ∧
      (∀ h, m ∣ h → ∀ N, m ≤ N → ∀ L, ¬ absCertifiedKill a h N L) :=
  ⟨surrogate m, surrogate_le m hm, fun _ hn => surrogate_of_le hn,
    fun _ _ _ hb hcert => surrogate_inherits_low_certificates hb hcert,
    fun _ hdvd _ hN _ => surrogate_no_certificate_at_multiple hm hdvd hN⟩

/-- The same statement placed on the lcm ladder: at the boundary `t → t+1` the
surrogate at `m = periodLcm (t+1)` copies `φ` up to `2 · periodLcm (t+1)`,
inherits every rung-`≤ t` deposit of depth `L ≤ 2·periodLcm (t+1) - 2·periodLcm t`,
and has no abstract certificate at any later lcm period, at positions
`N ≥ periodLcm (t+1)`. -/
theorem no_lift_at_lcm_rung (t : ℕ) :
    ∃ a : ℕ → ℕ,
      (∀ n, a n ≤ n) ∧
      (∀ n, n ≤ 2 * periodLcm (t + 1) → a n = Nat.totient n) ∧
      (∀ L, 2 * periodLcm t + L ≤ 2 * periodLcm (t + 1) →
        certifiedKill (periodLcm t) (periodLcm t) L →
        absCertifiedKill a (periodLcm t) (periodLcm t) L) ∧
      (∀ t', t + 1 ≤ t' → ∀ N, periodLcm (t + 1) ≤ N → ∀ L,
        ¬ absCertifiedKill a (periodLcm t') N L) := by
  obtain ⟨a, hle, heq, hlow, hkill⟩ := no_lift_from_data_below _ (periodLcm_pos (t + 1))
  refine ⟨a, hle, heq, fun L hL hcert => hlow _ _ _ (by omega) hcert, fun t' ht' N hN L => ?_⟩
  refine hkill _ ?_ N hN L
  -- `periodLcm` is monotone under divisibility along the ladder
  clear hN
  induction t' with
  | zero => omega
  | succ s ih =>
      rcases Nat.lt_or_ge (t + 1) (s + 1) with hlt | hge
      · exact dvd_trans (ih (by omega)) (periodLcm_dvd_succ s)
      · have : t + 1 = s + 1 := by omega
        rw [this]

/-! ## The refutation of the lift schema -/

/-- A kernel-checked diagonal deposit at the rung `t = 2` of the lcm ray
(`periodLcm 2 = 2`), at depth `8`. -/
theorem certifiedKill_two_two_eight : certifiedKill 2 2 8 := by decide

theorem periodLcm_two : periodLcm 2 = 2 := by decide

theorem periodLcm_three : periodLcm 3 = 6 := by decide

/-- **The headline no-go.**  There is no lift law of the shape

  `⟨a admissible⟩ → ⟨a agrees with φ below 2·H_{t+1}⟩ →
   ⟨depth of the rung-t certificate fits below 2·H_{t+1}⟩ →
   certificate at rung t → certificate at rung t+1`,

even when `p` is required to be prime and the rungs are required to be genuine
prime-power boundaries of the lcm ray.  The witness is the boundary
`t = 2 → 3`, `p = 3`, `H_2 = 2`, `H_3 = 6`, with the deposit
`certifiedKill 2 2 8`.

Read arithmetically: lower totient values, the size bound, and one fitted
lower-rung certificate do not make the displayed uniform conclusion valid for
all admissible sources.  The theorem does not identify a unique missing input
or rule out a stronger schema using additional facts specific to `φ`. -/
theorem no_lift_from_lower_totient_data
    (lift : ∀ (a : ℕ → ℕ), (∀ n, a n ≤ n) →
      ∀ t p L : ℕ, Nat.Prime p → periodLcm (t + 1) = p * periodLcm t →
        2 * periodLcm t + L ≤ 2 * periodLcm (t + 1) →
        (∀ n, n ≤ 2 * periodLcm (t + 1) → a n = Nat.totient n) →
        absCertifiedKill a (periodLcm t) (periodLcm t) L →
        ∃ L', absCertifiedKill a (periodLcm (t + 1)) (periodLcm (t + 1)) L') :
    False := by
  obtain ⟨a, hle, heq, hlow, hkill⟩ := no_lift_from_data_below 6 (by norm_num)
  have hcert : absCertifiedKill a (periodLcm 2) (periodLcm 2) 8 := by
    rw [periodLcm_two]
    exact hlow 2 2 8 (by norm_num) certifiedKill_two_two_eight
  obtain ⟨L', hL'⟩ :=
    lift a hle 2 3 8 Nat.prime_three (by rw [periodLcm_two, periodLcm_three])
      (by rw [periodLcm_two, periodLcm_three])
      (by rw [periodLcm_three]; exact heq) hcert
  rw [periodLcm_three] at hL'
  exact hkill 6 dvd_rfl 6 le_rfl L' hL'

/-! ## The companion positive law: certificates descend

The no-go above refutes one way of climbing the certificate lattice from
below.  Certificates *can* be descended, and the descent is unconditional and
local.  Together the two results prove downward propagation and refute the
particular upward schema formalized above; they do not rule out every stronger
upward principle. -/

/-- **Forward propagation of integrality.**  An integer tail difference at
period `d` and position `N` stays integral at every later position: the carry
recurrence `D_d(M+1) = 2·D_d(M) − δ` preserves `ℤ`. -/
theorem tail_diff_mem_int_of_le {d N M : ℕ} (hNM : N ≤ M)
    (hmem : totientTail (N + d) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    totientTail (M + d) - totientTail M ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hNM
  clear hNM
  induction i with
  | zero => simpa using hmem
  | succ i ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨2 * k - deltaTotient d (N + i + 1), ?_⟩
      have hrec := tail_diff_succ d (N + i)
      rw [show N + (i + 1) = N + i + 1 from by omega, hrec, ← hk]
      push_cast
      ring

/-- **Divisor descent for the certificate.**  A single certificate at period
`h` and position `N` refutes integrality of the tail difference at *every*
divisor of `h`, at the same position `N`.  So the certificate lattice is closed
downward under divisibility of the period: one diagonal deposit at `H_t`
already carries every period dividing `H_t`. -/
theorem tail_diff_notMem_int_of_certifiedKill_dvd {h N L d : ℕ}
    (hcert : certifiedKill h N L) (hdvd : d ∣ h) :
    totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  intro hmem
  obtain ⟨m, rfl⟩ := hdvd
  refine tail_diff_notMem_int_of_certifiedKill hcert ?_
  have hall : ∀ M, N ≤ M →
      totientTail (M + d) - totientTail M ∈ Set.range ((↑) : ℤ → ℝ) :=
    fun _ hM => tail_diff_mem_int_of_le hM hmem
  have hmul := tail_diff_mul_mem_int hall m N le_rfl
  rwa [show N + m * d = N + d * m from by ring] at hmul

/-- Amplification of the recorded deposits: a diagonal certificate at rung `t`
refutes integrality at every period `d ≤ t`, all at the single position
`N = H_t`.  The restricted reverse implication formalized by
`no_lift_from_lower_totient_data` is not a consequence of lower agreement and
the size bound alone. -/
theorem periodLcm_diagonal_kills_all_small_periods {t d L : ℕ}
    (hcert : certifiedKill (periodLcm t) (periodLcm t) L) (hd : 0 < d) (hdt : d ≤ t) :
    totientTail (periodLcm t + d) - totientTail (periodLcm t)
      ∉ Set.range ((↑) : ℤ → ℝ) :=
  tail_diff_notMem_int_of_certifiedKill_dvd hcert (dvd_periodLcm hd hdt)

end AngleA5
end Lift
end ErdosProblems
