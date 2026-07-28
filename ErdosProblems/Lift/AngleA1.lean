/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.LcmDiagonalReduction

/-!
# Angle A1: the totient across the lcm boundary — proved transport and fixed-depth comparisons

`irrational_totient_series_of_lcm_certificate_supply` reduces Erdős #249 to a cofinal
supply of `certifiedKill (periodLcm t) N L`.  The 28 diagonal deposits available when this
module was written all took `N = periodLcm t`.  The repository now contains the larger
finite band `Skip.LadderT67.exists_diagonalKill_le_82`; that later band remains finite and
does not supply the cofinal hypothesis.  This file records four groups of results.

## 1.  PROVED: the scale-free divisibility law (and its ceiling)

`totient_gcd_dvd_window` :  `φ(gcd(h, m)) ∣ φ(m + h) − φ(m)`, for **all** `h, m`.

This is a scale-free form of what the totient transports across a scale change: it holds at
every rung of the lcm ladder simultaneously, with no coprimality, no cleanliness, and no
`v_q(d) < v_q(H)` side condition.  At offset `d = 17` of any window whose shift is divisible
by `17` it proves a factor of `16` (`sixteen_dvd_diagCoeff_offset_seventeen`), including the
case `v₁₇(17) = v₁₇(H) = 1`, which is outside the hypothesis of the exact-valuation result in
`Lift/Recon249.lean`.  **MEASURED:** over the depth-`98`, `t = 67` window, the two counts are
`114` for that exact-valuation rule and `210` for this gcd rule.  **PROVED:** the uniform
upper bound below is `588`.

`scaleFree_bit_ceiling` :  `2^k ∣ φ(gcd(h, m))  →  2^k ≤ m`.

So the law supplies at most `log₂ m` divisibility bits at offset `m`.
`coeffDiscrepancy_congr` gives a sufficient coordinatewise precision for fixing the complete
discrepancy residue, and `coeffDiscrepancy_update_not_dvd` proves sensitivity to one specific
single-coordinate perturbation.  It does **not** prove that a certificate needs `j+1`
independent bits at every position: correlated coefficient errors can cancel, actual totient
coefficients are constrained, and `certifiedKill` asks only for membership in an arc rather
than for the whole residue.  At depth `98`:

  * the residue-precision benchmark is `∑_{d=1}^{98} d = 4851` (`frontier_demand`);
  * scale-free supply `≤ ∑_{d=1}^{98} 6 = 588` bits  (`frontier_supply_ledger`),
    for **every** shift `h` whatsoever.

Thus this particular gcd rule supplies at most `12%` of that residue-precision benchmark.
This is not a lower bound on the information needed to establish `certifiedKill`, and hence
is not by itself an obstruction to a certificate.

## 2.  PROVED: a base-`t` reduction and fixed-depth arithmetic comparisons

The diagonal is a choice, not a requirement.  Taking `N = t` is also cofinal, so

`irrational_totient_series_of_lcm_base_supply` :
  `(∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (periodLcm t) t L) → Irrational (∑ φ(n)/2ⁿ)`

is a second one-parameter reduction.  Both discrepancies contain `2L` totient values:

  * a depth-`L` diagonal cell reads two blocks of `L` values at integers
    `≥ periodLcm t`;
  * a depth-`L` base cell reads one block of `L` values at integers `≥ periodLcm t` and one
    block of `L` values at integers `≤ t + L` (`base_window_low_block`).

At the `t = 67` cell the exclusion radius drops from `2H + L + 2` to
`H + t + L + 2`.  This was the first uncertified cell when the comparison was written; it
is now included in `Skip.LadderT67.exists_diagonalKill_le_82`.
**PROVED, at the fixed depth `98`:**

  * diagonal, depth `98`: arc `65125117500982681130892344` inside `2^98` — `2.05 × 10⁻⁴`;
  * base, depth `98`:     arc `158488887587279166527653346610` inside `2^98` — `0.500`.

`base_margin_98_beats_diagonal_98` records the factor (`> 2433×`) at this one common depth.
The comparison is not uniform in depth: `Lift/verify/Check1.lean` checks that the diagonal
arc at depth `99` already exceeds half of `2^99`.  Any base certificate at `t = 67` has
depth at least `97` (`base_depth_floor_at_67`), and
`base_depth_97_is_admissible` proves only that the defining arc is nonempty at depth `97`;
it does not prove a certificate there.

Kernel-checked deposits in the base form: `certifiedKill (periodLcm t) t L` for every
`t ≤ 10` (`exists_baseKill_le_ten`), at depths `5,6,5,7,8,10,9,11,13,15,14`; at `t = 7`
and `t = 8` the displayed depths are below the recorded diagonal depths.  The bridge proved
in `Lift/verify/Check1.lean` derives
each base cell from a diagonal certificate at the same scale.  These deposits therefore add
no new certified scale beyond the recorded diagonal deposits.

## 3.  PROVED: the ladder implication runs downward

A diagonal certificate at `H` is equivalent to the statement
`2^H(2^H − 1)·S ∉ ℤ` (`exists_certifiedKill_diagonal_iff` plus `mem_int_iff_scaled`): the
converse of `tail_diff_notMem_int_of_certifiedKill` is proved here.  Thus existence of some
certificate depth is equivalent to that non-integrality statement.
Since `2^H(2^H − 1) ∣ 2^{mH}(2^{mH} − 1)` (`scaled_dvd`), integrality transports **upward**,
hence non-integrality transports **downward**:

`exists_certifiedKill_descends` :
  `(∃ L, certifiedKill (m·H) (m·H) L) → (∃ L, certifiedKill H H L)`,  `m ≥ 1`.

`diagonal_certified_downward_closed` : the certified region of the lcm ladder is
downward closed.

The proposed lift `certifiedKill H H L → ∃ L', certifiedKill (p·H) (p·H) L'` runs in the
opposite direction from the theorem proved here.  A higher rung is at least as strong as all rungs below it.
In particular, the 28 deposits then recorded at `t ≤ 66` are logical consequences of a
deposit at `t = 67` (`frontier_certificate_implies_all_seed`).  The repository now contains
such a deposit as part of `Skip.LadderT67.exists_diagonalKill_le_82`.  Thus those lower
deposits are logically redundant as hypotheses for the proposed upward implication.
`irrational_iff_all_diagonal_certified` records the resulting
dichotomy: #249 holds iff *every* rung is certified, and fails iff the certified region is a
bounded initial segment `[0, t*]`.

This does not say the upward implication is false.  It says only that the already-proved
lower-rung hypothesis is implied by the desired higher-rung conclusion, so it cannot supply
independent logical strength.

## 4.  PROVED: constant-window replacement models do not certify

`constant_model_never_kills` : if a replacement `g` for `φ` has constant window difference
`g(N+h+1+j) − g(N+1+j) = c ≤ N+h+L+2` for `j < L`, then `g` certifies **nothing**, at any
depth.  The identity `g = id` (`identity_model_never_kills`) is the extreme case: `c = h`.

Thus any replacement whose window differences satisfy the theorem's constant-difference
hypothesis is blind to `certifiedKill` on that window.  The theorem does not prove that every
bounded-prime or bounded-level approximation satisfies this hypothesis, and it is not a
general no-go theorem for such models.

Everything here is elementary: `φ(a) ∣ φ(b)` for `a ∣ b`, geometric sums, and integer window
arithmetic.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace ErdosProblems
namespace Lift
namespace AngleA1

set_option maxRecDepth 1000000

/-! ## Part 0: sufficient residue precision and a single-coordinate sensitivity result -/

/-- The window discrepancy as a functional of its coefficient sequence:
`D(c, L) = ∑_{j<L} c(j)·2^{L-1-j}`. -/
def coeffDiscrepancy (c : ℕ → ℤ) (L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, c j * 2 ^ (L - 1 - j)

/-- `windowDiscrepancy` is `coeffDiscrepancy` of the totient window coefficients. -/
theorem windowDiscrepancy_eq_coeffDiscrepancy (h N L : ℕ) :
    windowDiscrepancy h N L
      = coeffDiscrepancy
          (fun j => (Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) L :=
  rfl

/-- **PROVED (sufficiency for residue equality).**  Agreement of every coefficient modulo
`2^{j+1}` forces agreement of the discrepancies modulo `2^L`. -/
theorem coeffDiscrepancy_congr {c c' : ℕ → ℤ} {L : ℕ}
    (hc : ∀ j < L, (2 : ℤ) ^ (j + 1) ∣ (c j - c' j)) :
    (2 : ℤ) ^ L ∣ coeffDiscrepancy c L - coeffDiscrepancy c' L := by
  unfold coeffDiscrepancy
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun j hj => ?_
  have hjL : j < L := Finset.mem_range.mp hj
  have hsplit : (2 : ℤ) ^ L = 2 ^ (j + 1) * 2 ^ (L - 1 - j) := by
    rw [← pow_add]; congr 1; omega
  have hring : c j * 2 ^ (L - 1 - j) - c' j * 2 ^ (L - 1 - j)
      = (c j - c' j) * 2 ^ (L - 1 - j) := by ring
  rw [hring, hsplit]
  exact mul_dvd_mul_right (hc j hjL) _

/-- Perturbing a single coefficient at position `j₀` by exactly `2^{j₀}` moves the
discrepancy by exactly `2^{L-1}`. -/
theorem coeffDiscrepancy_update {c : ℕ → ℤ} {L j₀ : ℕ} (hj : j₀ < L) :
    coeffDiscrepancy (Function.update c j₀ (c j₀ + 2 ^ j₀)) L - coeffDiscrepancy c L
      = 2 ^ (L - 1) := by
  unfold coeffDiscrepancy
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j₀]
  · have hupd : Function.update c j₀ (c j₀ + 2 ^ j₀) j₀ = c j₀ + 2 ^ j₀ :=
      Function.update_self _ _ _
    rw [hupd]
    have hpow : (2 : ℤ) ^ j₀ * 2 ^ (L - 1 - j₀) = 2 ^ (L - 1) := by
      rw [← pow_add]; congr 1; omega
    calc (c j₀ + 2 ^ j₀) * 2 ^ (L - 1 - j₀) - c j₀ * 2 ^ (L - 1 - j₀)
        = (2 : ℤ) ^ j₀ * 2 ^ (L - 1 - j₀) := by ring
      _ = 2 ^ (L - 1) := hpow
  · intro b _ hb
    rw [Function.update_of_ne hb]
    ring
  · intro hmem
    exact absurd (Finset.mem_range.mpr hj) hmem

/-- **PROVED (single-coordinate residue sensitivity).**  Perturbing one coefficient by
`2^{j₀}` changes the discrepancy residue modulo `2^L`.

This is not a necessity theorem for `certifiedKill`: it neither excludes cancellations
between several coefficient errors nor shows that the coarser admissible-arc predicate
requires the complete residue. -/
theorem coeffDiscrepancy_update_not_dvd {c : ℕ → ℤ} {L j₀ : ℕ} (hL : 0 < L) (hj : j₀ < L) :
    ¬ (2 : ℤ) ^ L ∣
        coeffDiscrepancy (Function.update c j₀ (c j₀ + 2 ^ j₀)) L - coeffDiscrepancy c L := by
  rw [coeffDiscrepancy_update hj]
  intro hdvd
  have hpos : (0 : ℤ) < 2 ^ (L - 1) := by positivity
  have hle : (2 : ℤ) ^ L ≤ 2 ^ (L - 1) := Int.le_of_dvd hpos hdvd
  have hlt : (2 : ℤ) ^ (L - 1) < 2 ^ L := by
    apply pow_lt_pow_right₀ (by norm_num)
    omega
  linarith

/-! ## Part 1: the scale-free divisibility law -/

/-- **The A1 transport law.**  For every shift `h` and every window position `m`,

  `φ(gcd(h, m)) ∣ φ(m + h) − φ(m)`.

No hypotheses at all.  `gcd(h, m)` divides `m` and divides `m + h`, and `φ` is monotone for
divisibility, so both totients carry the factor.  Because the divisor depends on `h` only
through `gcd(h, m)`, this holds *identically* at `H`, `2H`, `pH`, `2pH` and every higher rung
of the lcm ladder: it is the scale-free part of the window. -/
theorem totient_gcd_dvd_window (h m : ℕ) :
    (Nat.totient (Nat.gcd h m) : ℤ) ∣ (Nat.totient (m + h) : ℤ) - (Nat.totient m : ℤ) := by
  have hg1 : Nat.gcd h m ∣ m := Nat.gcd_dvd_right h m
  have hg2 : Nat.gcd h m ∣ m + h := Nat.dvd_add hg1 (Nat.gcd_dvd_left h m)
  have d1 : (Nat.totient (Nat.gcd h m) : ℤ) ∣ (Nat.totient m : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.totient_dvd_of_dvd hg1)
  have d2 : (Nat.totient (Nat.gcd h m) : ℤ) ∣ (Nat.totient (m + h) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.totient_dvd_of_dvd hg2)
  exact dvd_sub d2 d1

/-- The transport law on the coefficient at position `j` of the `(h, N)` window. -/
theorem totient_gcd_dvd_windowCoeff (h N j : ℕ) :
    (Nat.totient (Nat.gcd h (N + 1 + j)) : ℤ) ∣
      (Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ) := by
  have hw := totient_gcd_dvd_window h (N + 1 + j)
  have e : N + 1 + j + h = N + h + 1 + j := by omega
  rwa [e] at hw

/-- The transport law on the diagonal window coefficient
`c_H(d) = φ(2H + d) − φ(H + d)`: `φ(gcd(d, H)) ∣ c_H(d)`. -/
theorem totient_gcd_dvd_diagCoeff (H d : ℕ) :
    (Nat.totient (Nat.gcd d H) : ℤ) ∣
      (Nat.totient (2 * H + d) : ℤ) - (Nat.totient (H + d) : ℤ) := by
  have hw := totient_gcd_dvd_window H (H + d)
  have e : H + d + H = 2 * H + d := by ring
  rw [e] at hw
  have hg : Nat.gcd H (H + d) = Nat.gcd d H := by
    have hcomm : Nat.gcd H (H + d) = Nat.gcd (H + d) H := Nat.gcd_comm _ _
    rw [hcomm, show H + d = d + H from Nat.add_comm H d]
    exact Nat.gcd_add_self_left H d
  rwa [hg] at hw

/-- **Four bits the exact-valuation core misses.**  For every `H` divisible by `17`,
`16 ∣ c_H(17)`.  `Recon249.factorization_window` cannot see this: it needs
`v₁₇(17) < v₁₇(H)`, which fails whenever `17 ∥ H` — and `17 ∥ lcm(1..t)` for every
`t < 289`.  Divisibility does not need the valuation to be strict. -/
theorem sixteen_dvd_diagCoeff_offset_seventeen {H : ℕ} (h17 : 17 ∣ H) :
    (16 : ℤ) ∣ (Nat.totient (2 * H + 17) : ℤ) - (Nat.totient (H + 17) : ℤ) := by
  have hw := totient_gcd_dvd_diagCoeff H 17
  have hg : Nat.gcd 17 H = 17 := Nat.gcd_eq_left h17
  rw [hg] at hw
  have h17t : Nat.totient 17 = 16 := by decide
  rwa [h17t] at hw

/-- **PROVED: the ceiling on the transport law.**  If `2^k` divides
`φ(gcd(h, m))` then `2^k ≤ m`.  Thus this law supplies at most `log₂ m` divisibility bits at
position `m`.  No certificate-wide information lower bound is asserted. -/
theorem scaleFree_bit_ceiling {h m k : ℕ} (hm : 0 < m)
    (hk : 2 ^ k ∣ Nat.totient (Nat.gcd h m)) : 2 ^ k ≤ m := by
  have hg : 0 < Nat.gcd h m := Nat.gcd_pos_of_pos_right h hm
  have h1 : 0 < Nat.totient (Nat.gcd h m) := Nat.totient_pos.mpr hg
  have h2 : 2 ^ k ≤ Nat.totient (Nat.gcd h m) := Nat.le_of_dvd h1 hk
  have h3 : Nat.totient (Nat.gcd h m) ≤ Nat.gcd h m := Nat.totient_le _
  have h4 : Nat.gcd h m ≤ m := Nat.le_of_dvd hm (Nat.gcd_dvd_right h m)
  omega

/-- The number of 2-adic bits of the window coefficient at position `m` that the scale-free
law forces, for shift `h`. -/
def supplyBits (h m : ℕ) : ℕ := (Nat.totient (Nat.gcd h m)).factorization 2

theorem two_pow_supplyBits_le {h m : ℕ} (hm : 0 < m) : 2 ^ supplyBits h m ≤ m :=
  scaleFree_bit_ceiling hm (Nat.ordProj_dvd _ 2)

theorem supplyBits_le_six {h m : ℕ} (h1 : 0 < m) (h2 : m ≤ 98) : supplyBits h m ≤ 6 := by
  by_contra hcon
  have h7 : 7 ≤ supplyBits h m := by omega
  have hmono : (2 : ℕ) ^ 7 ≤ 2 ^ supplyBits h m := Nat.pow_le_pow_right (by norm_num) h7
  have hle := two_pow_supplyBits_le (h := h) h1
  have : (2 : ℕ) ^ 7 = 128 := by norm_num
  omega

/-- **PROVED arithmetic benchmark.**  The sum of the sufficient per-coordinate residue
precisions through depth `98` is `∑_{d=1}^{98} d = 4851`.

This equality is pure finite arithmetic.  It is not a theorem that every depth-`98`
certificate requires `4851` independent bits.  The declaration name is historical:
`t = 67` is now certified. -/
theorem frontier_demand : ∑ d ∈ Finset.Icc 1 98, d = 4851 := by decide

/-- **PROVED, uniform in the scale.**  For
*every* shift `h`, the total 2-adic information the scale-free divisibility law forces over
the depth-`98` window is at most `588`.

**MEASURED outside Lean:** at `h = periodLcm 67`, this sum is `210`, versus `114` for the
exact-valuation rule in `Recon249` Result 2.  The figures `4%` and `12%` compare these values
with the `4851` residue-precision benchmark; they do not measure a proved information demand
for `certifiedKill`.  The declaration name is historical: `t = 67` is now certified. -/
theorem frontier_supply_ledger (h : ℕ) : ∑ d ∈ Finset.Icc 1 98, supplyBits h d ≤ 588 := by
  have hbound : ∀ d ∈ Finset.Icc 1 98, supplyBits h d ≤ 6 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    exact supplyBits_le_six (by omega) hd.2
  calc ∑ d ∈ Finset.Icc 1 98, supplyBits h d ≤ ∑ _d ∈ Finset.Icc 1 98, 6 :=
        Finset.sum_le_sum hbound
    _ = 588 := by decide

/-! ## Part 2: the base-`t` collapse -/

/-- **PROVED: a base-`t` supply reduction.**  A second one-parameter reduction of #249,
alongside the
diagonal one.  The supply theorem wants `certifiedKill (periodLcm t) N L` at *some* large
`N`; `N = t` is already cofinal.  The low block then consists of totients of integers
`≤ t + L`.  This theorem does not compare the computational cost of proving the required
certificates. -/
theorem irrational_totient_series_of_lcm_base_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L, certifiedKill (periodLcm t) t L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_lcm_certificate_supply fun t₀ N₀ => ?_
  obtain ⟨t, ht, L, hkill⟩ := hsupply (max t₀ N₀)
  exact ⟨t, le_trans (le_max_left _ _) ht, t,
    le_trans (le_max_right _ _) ht, L, hkill⟩

/-- **PROVED index-range asymmetry.**  In the base cell every index of the low block is at
most `t + L`; in the diagonal cell every index of the low block is at least `periodLcm t`.
Both cells read `L` indices of the high block, all `≥ periodLcm t`.  The theorem itself
asserts only the displayed index bound; “hard” versus “easy” evaluation is not formalized. -/
theorem base_window_low_block {t L j : ℕ} (hj : j < L) : t + 1 + j ≤ t + L := by omega

theorem diagonal_window_low_block {t j : ℕ} : periodLcm t ≤ periodLcm t + 1 + j := by omega

/-- The base-cell depth floor: `2·periodLcm t < 2^L`.  (The diagonal floor is
`4·periodLcm t < 2^L` — exactly one bit more.) -/
theorem base_depth_floor {t N L : ℕ} (hcert : certifiedKill (periodLcm t) N L) :
    (2 * periodLcm t : ℤ) < 2 ^ L := by
  have hfl := certifiedKill_depth_floor hcert
  have hN : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  push_cast at hfl ⊢
  linarith

theorem periodLcm_67_val : periodLcm 67 = 79211881234889091923261227200 := by decide

/-- **PROVED lower bound.**  Any base certificate at the frontier has depth at least `97`,
one below the corresponding proved diagonal lower bound `98`
(`Recon249.certifiedKill_periodLcm_67_depth`).  This does not prove existence at depth
`97`. -/
theorem base_depth_floor_at_67 {L : ℕ} (hcert : certifiedKill (periodLcm 67) 67 L) :
    97 ≤ L := by
  by_contra hcon
  have hL : L ≤ 96 := by omega
  have hfl := base_depth_floor hcert
  have hmono : (2 : ℤ) ^ L ≤ 2 ^ 96 := pow_le_pow_right₀ (by norm_num) hL
  rw [periodLcm_67_val] at hfl
  norm_num at hfl
  linarith

/-- **PROVED numerical admissibility only.**  At depth `97` the base cell's defining arc is
nonempty.  This does not prove that its actual discrepancy lies in that arc. -/
theorem base_depth_97_is_admissible :
    2 * ((67 : ℤ) + (periodLcm 67 : ℤ) + 97 + 2) < 2 ^ 97 := by
  rw [periodLcm_67_val]
  norm_num

/-- The base cell's admissible arc at depth `98`: half the circle. -/
theorem base_margin_98 :
    (2 : ℤ) ^ 98 - 2 * ((67 : ℤ) + (periodLcm 67 : ℤ) + 98 + 2)
      = 158488887587279166527653346610 := by
  rw [periodLcm_67_val]
  norm_num

/-- The diagonal cell's admissible arc at depth `98`: a needle
(`Recon249.periodLcm_67_depth98_margin`, restated here for the comparison). -/
theorem diagonal_margin_98 :
    (2 : ℤ) ^ 98 - 2 * ((periodLcm 67 : ℤ) + (periodLcm 67 : ℤ) + 98 + 2)
      = 65125117500982681130892344 := by
  rw [periodLcm_67_val]
  norm_num

/-- **PROVED fixed-depth comparison.**  At depth `98`, the base cell's admissible arc is
more than `2433` times the diagonal cell's admissible arc.  This theorem compares only the
two integer margins at that depth; it proves neither a certificate nor a uniform
computational-cost advantage. -/
theorem base_margin_98_beats_diagonal_98 :
    2433 * ((2 : ℤ) ^ 98 - 2 * ((periodLcm 67 : ℤ) + (periodLcm 67 : ℤ) + 98 + 2))
      < (2 : ℤ) ^ 98 - 2 * ((67 : ℤ) + (periodLcm 67 : ℤ) + 98 + 2) := by
  rw [base_margin_98, diagonal_margin_98]
  norm_num

/-! ### Kernel-checked deposits in the base form -/

theorem baseKill_0 : certifiedKill (periodLcm 0) 0 5 := by decide
theorem baseKill_1 : certifiedKill (periodLcm 1) 1 6 := by decide
theorem baseKill_2 : certifiedKill (periodLcm 2) 2 5 := by decide
theorem baseKill_3 : certifiedKill (periodLcm 3) 3 7 := by decide
theorem baseKill_4 : certifiedKill (periodLcm 4) 4 8 := by decide
theorem baseKill_5 : certifiedKill (periodLcm 5) 5 10 := by decide
theorem baseKill_6 : certifiedKill (periodLcm 6) 6 9 := by decide
theorem baseKill_7 : certifiedKill (periodLcm 7) 7 11 := by decide
theorem baseKill_8 : certifiedKill (periodLcm 8) 8 13 := by decide
theorem baseKill_9 : certifiedKill (periodLcm 9) 9 15 := by decide
theorem baseKill_10 : certifiedKill (periodLcm 10) 10 14 := by decide

/-- Every scale `t ≤ 10` carries a base-form certificate.  Depths
`5, 6, 5, 7, 8, 10, 9, 11, 13, 15, 14` — at `t = 7` and `t = 8` these are `11` and `13`
against the recorded diagonal depths `14` and `15`. -/
theorem exists_baseKill_le_ten (t : ℕ) (ht : t ≤ 10) :
    ∃ L, certifiedKill (periodLcm t) t L := by
  interval_cases t
  · exact ⟨5, baseKill_0⟩
  · exact ⟨6, baseKill_1⟩
  · exact ⟨5, baseKill_2⟩
  · exact ⟨7, baseKill_3⟩
  · exact ⟨8, baseKill_4⟩
  · exact ⟨10, baseKill_5⟩
  · exact ⟨9, baseKill_6⟩
  · exact ⟨11, baseKill_7⟩
  · exact ⟨13, baseKill_8⟩
  · exact ⟨15, baseKill_9⟩
  · exact ⟨14, baseKill_10⟩

/-! ## Part 3: constant-window replacement models certify nothing -/

/-- The window discrepancy of an arbitrary replacement `g` for the totient. -/
def modelDiscrepancy (g : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, ((g (N + h + 1 + j) : ℤ) - (g (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

/-- The certificate predicate of an arbitrary replacement `g` for the totient. -/
def modelKill (g : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < modelDiscrepancy g h N L % 2 ^ L ∧
    modelDiscrepancy g h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

/-- The model predicate at `g = φ` is the real certificate predicate. -/
theorem modelKill_totient (h N L : ℕ) : modelKill Nat.totient h N L ↔ certifiedKill h N L :=
  Iff.rfl

private lemma sum_two_pow (L : ℕ) : ∑ j ∈ Finset.range L, (2 : ℤ) ^ j = 2 ^ L - 1 := by
  induction L with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

private lemma sum_two_pow_rev (L : ℕ) :
    ∑ j ∈ Finset.range L, (2 : ℤ) ^ (L - 1 - j) = 2 ^ L - 1 := by
  rw [Finset.sum_range_reflect (fun j => (2 : ℤ) ^ j) L]
  exact sum_two_pow L

/-- **PROVED: constant-window models certify nothing.**  If a replacement `g` for the totient has
constant window difference `c` across the depth-`L` window, with `c ≤ N + h + L + 2`, then
`modelKill g h N L` is false — at every depth, at every scale.

The reason is structural, not numerical: a constant window difference makes the discrepancy
`c·(2^L − 1) ≡ −c`, which lands in the excluded arc by construction.  A model affine in the
shift satisfies the constant-difference hypothesis.  No claim is made here that every
finite-prime truncation or bounded-level model is affine on the required windows. -/
theorem constant_model_never_kills {g : ℕ → ℕ} {h N L c : ℕ}
    (hc : ∀ j < L, (g (N + h + 1 + j) : ℤ) - (g (N + 1 + j) : ℤ) = (c : ℤ))
    (hcle : c ≤ N + h + L + 2) : ¬ modelKill g h N L := by
  rintro ⟨hlow, hhigh⟩
  -- the discrepancy is `c · (2^L - 1)`
  have hD : modelDiscrepancy g h N L = (c : ℤ) * (2 ^ L - 1) := by
    unfold modelDiscrepancy
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [hc j (Finset.mem_range.mp hj)]), ← Finset.mul_sum, sum_two_pow_rev]
  -- depth floor
  have hfloor : 2 * ((N : ℤ) + h + L + 2) < 2 ^ L := by linarith
  have hcle' : (c : ℤ) ≤ (N : ℤ) + h + L + 2 := by exact_mod_cast hcle
  have h2L : (0 : ℤ) < 2 ^ L := by positivity
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · subst hc0
    rw [hD] at hlow
    simp at hlow
    have hN : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
    have hh : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
    have hLL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
    linarith
  · have hcpos' : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hcpos
    have hrw : (c : ℤ) * (2 ^ L - 1) = (2 ^ L - (c : ℤ)) + 2 ^ L * ((c : ℤ) - 1) := by ring
    have hmod : modelDiscrepancy g h N L % 2 ^ L = 2 ^ L - (c : ℤ) := by
      rw [hD, hrw, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
    rw [hmod] at hhigh
    linarith

/-- The identity model: `g = id` has constant window difference `h`, so it certifies
nothing at any depth or scale. -/
theorem identity_model_never_kills (h N L : ℕ) : ¬ modelKill id h N L := by
  refine constant_model_never_kills (c := h) (fun j _ => ?_) (by omega)
  simp only [id]
  push_cast
  ring

/-! ## Part 4: the ladder implication provably runs downward -/

/-- The diagonal tail difference in closed form:
`R_{2H} − R_H = 2^H(2^H − 1)·S − (Φ_{2H} − Φ_H)`. -/
private lemma tail_diff_eq_scaled (H : ℕ) :
    totientTail (H + H) - totientTail H
      = (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        - ((totientPrefix (H + H) : ℝ) - (totientPrefix H : ℝ)) := by
  have h1 := two_pow_mul_totient_series_eq (H + H)
  have h2 := two_pow_mul_totient_series_eq H
  rw [pow_add] at h1
  have hexp : (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (2 : ℝ) ^ H * (2 : ℝ) ^ H * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        - (2 : ℝ) ^ H * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by ring
  rw [hexp]
  linarith

/-- `R_{2H} − R_H` is an integer exactly when `2^H(2^H − 1)·S` is. -/
private lemma mem_int_iff_scaled (H : ℕ) :
    (totientTail (H + H) - totientTail H ∈ Set.range ((↑) : ℤ → ℝ))
      ↔ ((2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
            ∈ Set.range ((↑) : ℤ → ℝ)) := by
  rw [tail_diff_eq_scaled]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j + (totientPrefix (H + H) : ℤ) - (totientPrefix H : ℤ), by push_cast; linarith⟩
  · rintro ⟨j, hj⟩
    exact ⟨j - (totientPrefix (H + H) : ℤ) + (totientPrefix H : ℤ), by push_cast; linarith⟩

/-- `2^H(2^H − 1) ∣ 2^{mH}(2^{mH} − 1)`: the certificate moduli are nested upward along the
divisibility order of the shifts. -/
private lemma scaled_dvd (H m : ℕ) (hm : 0 < m) :
    ((2 : ℤ) ^ H * ((2 : ℤ) ^ H - 1)) ∣ ((2 : ℤ) ^ (m * H) * ((2 : ℤ) ^ (m * H) - 1)) := by
  have hpow : (2 : ℤ) ^ (m * H) = ((2 : ℤ) ^ H) ^ m := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hpow]
  refine IsCoprime.mul_dvd ⟨1, -1, by ring⟩ ?_ ?_
  · exact Dvd.dvd.mul_right (dvd_pow_self _ hm.ne') _
  · have hd := sub_dvd_pow_sub_pow ((2 : ℤ) ^ H) 1 m
    rw [one_pow] at hd
    exact Dvd.dvd.mul_left hd _

/-- **Integrality transports upward.**  If the diagonal tail difference at `H` is an integer
then so is the one at every multiple `m·H`.  This is the automatic direction, and it is the
contrapositive of the lift. -/
theorem tail_diff_int_scale_up {H m : ℕ} (hm : 0 < m)
    (h : totientTail (H + H) - totientTail H ∈ Set.range ((↑) : ℤ → ℝ)) :
    totientTail (m * H + m * H) - totientTail (m * H) ∈ Set.range ((↑) : ℤ → ℝ) := by
  rw [mem_int_iff_scaled] at h ⊢
  obtain ⟨K, hK⟩ := h
  obtain ⟨c, hc⟩ := scaled_dvd H m hm
  have hcast : ((2 : ℝ) ^ (m * H) * ((2 : ℝ) ^ (m * H) - 1))
      = ((2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1)) * (c : ℝ) := by exact_mod_cast hc
  refine ⟨c * K, ?_⟩
  rw [hcast]
  have hreassoc : (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) * (c : ℝ)
        * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (c : ℝ) * ((2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1)
        * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by ring
  rw [hreassoc, ← hK]
  push_cast
  ring

private lemma certifiedKill_of_emod {h N L : ℕ} {r : ℤ}
    (hmod : windowDiscrepancy h N L % 2 ^ L = r)
    (h1 : ((N : ℤ) + h + L + 2) < r)
    (h2 : r < 2 ^ L - ((N : ℤ) + h + L + 2)) :
    certifiedKill h N L :=
  ⟨by rw [hmod]; exact h1, by rw [hmod]; exact h2⟩

private lemma exists_depth (H : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ L : ℕ, 2 * ((H : ℝ) + H + L + 2) < c * 2 ^ L := by
  have hgeo : Filter.Tendsto (fun L : ℕ => (1 / 2 : ℝ) ^ L) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsum : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)
  have hlin : Filter.Tendsto (fun L : ℕ => (L : ℝ) * (1 / 2 : ℝ) ^ L) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have htot : Filter.Tendsto
      (fun L : ℕ => (2 * ((H : ℝ) + H + 2)) * (1 / 2 : ℝ) ^ L + 2 * ((L : ℝ) * (1 / 2 : ℝ) ^ L))
      Filter.atTop (nhds 0) := by
    have h1 := hgeo.const_mul (2 * ((H : ℝ) + H + 2))
    have h2 := hlin.const_mul (2 : ℝ)
    simpa using h1.add h2
  obtain ⟨L, hL⟩ := (htot.eventually_lt_const hc).exists
  refine ⟨L, ?_⟩
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hrw : (2 * ((H : ℝ) + H + 2)) * (1 / 2 : ℝ) ^ L + 2 * ((L : ℝ) * (1 / 2 : ℝ) ^ L)
      = (2 * ((H : ℝ) + H + L + 2)) / 2 ^ L := by
    rw [div_pow, one_pow]
    field_simp
    ring
  rw [hrw, div_lt_iff₀ h2L] at hL
  linarith

/-- **The certificate is exactly the non-integrality of the tail difference.**  The converse
of `tail_diff_notMem_int_of_certifiedKill`: if the diagonal tail difference at `H` is not an
integer, some depth certifies it.  Depth is therefore never the obstruction — the only
question at a given scale is whether the real number `R_{2H} − R_H` is an integer. -/
theorem exists_certifiedKill_of_tail_diff_notMem_int {H : ℕ}
    (hd : totientTail (H + H) - totientTail H ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ L, certifiedKill H H L := by
  obtain ⟨k, u, hu0, hu1, hDk⟩ :
      ∃ (k : ℤ) (u : ℝ), 0 < u ∧ u < 1 ∧
        totientTail (H + H) - totientTail H = (k : ℝ) + u := by
    refine ⟨⌊totientTail (H + H) - totientTail H⌋,
      totientTail (H + H) - totientTail H - (⌊totientTail (H + H) - totientTail H⌋ : ℝ),
      ?_, ?_, by ring⟩
    · rcases lt_or_eq_of_le (Int.floor_le (totientTail (H + H) - totientTail H)) with hlt | heq
      · linarith
      · exact absurd ⟨⌊totientTail (H + H) - totientTail H⌋, heq⟩ hd
    · have h2 := Int.lt_floor_add_one (totientTail (H + H) - totientTail H)
      linarith
  have hc0 : 0 < min u (1 - u) := lt_min hu0 (by linarith)
  obtain ⟨L, hL⟩ := exists_depth H hc0
  have hcu : min u (1 - u) ≤ u := min_le_left _ _
  have hc1 : min u (1 - u) ≤ 1 - u := min_le_right _ _
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hdec1 := totientTail_eq_partial_add_tail (H + H) L
  have hdec2 := totientTail_eq_partial_add_tail H L
  have hA := windowDiscrepancy_div_eq H H L
  have hT1n := tail_after_nonneg (H + H) L
  have hT2n := tail_after_nonneg H L
  have hT1u := tail_after_le (H + H) L
  have hT2u := tail_after_le H L
  push_cast at hT1u
  rw [hdec1, hdec2] at hDk
  have hAreal : ((windowDiscrepancy H H L : ℤ) : ℝ) / 2 ^ L
      = ((k : ℝ) + u)
        - ((∑' j : ℕ, (Nat.totient (H + H + 1 + (j + L)) : ℝ) / 2 ^ (j + L + 1))
            - ∑' j : ℕ, (Nat.totient (H + 1 + (j + L)) : ℝ) / 2 ^ (j + L + 1)) := by
    rw [hA]; linarith
  have hAeq := (div_eq_iff h2L.ne').mp hAreal
  have hs1 : (∑' j : ℕ, (Nat.totient (H + H + 1 + (j + L)) : ℝ) / 2 ^ (j + L + 1)) * 2 ^ L
      ≤ (H : ℝ) + H + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT1u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hs2 : (∑' j : ℕ, (Nat.totient (H + 1 + (j + L)) : ℝ) / 2 ^ (j + L + 1)) * 2 ^ L
      ≤ (H : ℝ) + L + 2 := by
    have h' := mul_le_mul_of_nonneg_right hT2u h2L.le
    rwa [div_mul_cancel₀ _ h2L.ne'] at h'
  have hn1 : 0 ≤ (∑' j : ℕ, (Nat.totient (H + H + 1 + (j + L)) : ℝ) / 2 ^ (j + L + 1)) * 2 ^ L :=
    mul_nonneg hT1n h2L.le
  have hn2 : 0 ≤ (∑' j : ℕ, (Nat.totient (H + 1 + (j + L)) : ℝ) / 2 ^ (j + L + 1)) * 2 ^ L :=
    mul_nonneg hT2n h2L.le
  have hcu2 : min u (1 - u) * 2 ^ L ≤ u * 2 ^ L := mul_le_mul_of_nonneg_right hcu h2L.le
  have hc12 : min u (1 - u) * 2 ^ L ≤ (1 - u) * 2 ^ L := mul_le_mul_of_nonneg_right hc1 h2L.le
  have hexp : (1 - u) * 2 ^ L = 2 ^ L - u * 2 ^ L := by ring
  set r : ℤ := windowDiscrepancy H H L - k * 2 ^ L with hrd
  have hrreal : (r : ℝ)
      = u * 2 ^ L
        - ((∑' j : ℕ, (Nat.totient (H + H + 1 + (j + L)) : ℝ) / 2 ^ (j + L + 1))
            - ∑' j : ℕ, (Nat.totient (H + 1 + (j + L)) : ℝ) / 2 ^ (j + L + 1)) * 2 ^ L := by
    have hcast : (r : ℝ) = ((windowDiscrepancy H H L : ℤ) : ℝ) - (k : ℝ) * 2 ^ L := by
      rw [hrd]; push_cast; ring
    rw [hcast, hAeq]; ring
  have hlow : (H : ℝ) + H + L + 2 < (r : ℝ) := by rw [hrreal]; nlinarith
  have hhigh : (r : ℝ) < 2 ^ L - ((H : ℝ) + H + L + 2) := by rw [hrreal]; nlinarith
  refine ⟨L, certifiedKill_of_emod (r := r) ?_ ?_ ?_⟩
  · have hsplit : windowDiscrepancy H H L = r + 2 ^ L * k := by rw [hrd]; ring
    rw [hsplit, Int.add_mul_emod_self_left]
    refine Int.emod_eq_of_lt ?_ ?_
    · have hr0 : (0 : ℝ) ≤ (r : ℝ) := by
        have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
        have hLc : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
        linarith
      exact_mod_cast hr0
    · have hcast2 : (r : ℝ) < ((2 ^ L : ℤ) : ℝ) := by
        push_cast
        have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
        have hLc : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
        linarith
      exact_mod_cast hcast2
  · have hcl : (((H : ℤ) + H + L + 2 : ℤ) : ℝ) < (r : ℝ) := by push_cast; linarith
    exact_mod_cast hcl
  · have hch : (r : ℝ) < ((2 ^ L - ((H : ℤ) + H + L + 2) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast hch

/-- **The exact content of a diagonal certificate.** -/
theorem exists_certifiedKill_diagonal_iff (H : ℕ) :
    (∃ L, certifiedKill H H L)
      ↔ totientTail (H + H) - totientTail H ∉ Set.range ((↑) : ℤ → ℝ) :=
  ⟨fun ⟨_, hL⟩ => tail_diff_notMem_int_of_certifiedKill hL,
    exists_certifiedKill_of_tail_diff_notMem_int⟩

/-- **PROVED: the ladder implication runs downward.**  A diagonal certificate at any
multiple `m·H` *implies* a diagonal certificate at `H`.

This runs in the reverse direction from the proposed lift
`certifiedKill H H L → ∃ L', certifiedKill (p·H) (p·H) L'`.  The lift is therefore not an
ordinary induction step over an already-established base: the desired conclusion implies
the proposed base hypothesis.  Every higher rung is therefore at least as strong as all
rungs below it.  Strictness is not proved. -/
theorem exists_certifiedKill_descends {m H : ℕ} (hm : 0 < m)
    (hcert : ∃ L, certifiedKill (m * H) (m * H) L) : ∃ L, certifiedKill H H L := by
  obtain ⟨L, hL⟩ := hcert
  exact exists_certifiedKill_of_tail_diff_notMem_int
    (fun hmem => tail_diff_notMem_int_of_certifiedKill hL (tail_diff_int_scale_up hm hmem))

theorem periodLcm_dvd_of_le {s t : ℕ} (hst : s ≤ t) : periodLcm s ∣ periodLcm t := by
  induction t with
  | zero =>
      have : s = 0 := by omega
      subst this
      exact dvd_rfl
  | succ n ih =>
      rcases Nat.lt_or_ge s (n + 1) with hlt | hge
      · exact dvd_trans (ih (by omega)) (periodLcm_dvd_succ n)
      · have hs : s = n + 1 := by omega
        subst hs
        exact dvd_rfl

/-- **PROVED: the certified region is downward closed.**  If
any scale `t` of the lcm ray carries a diagonal certificate, then so does every `s ≤ t`.

The 28 deposits recorded when this result was written at `t ≤ 66` are logical consequences
of a deposit at `t = 67` or above.  The later band through `t = 82` supplies such a deposit.
This theorem proves downward closure; strictness between consecutive rungs is not claimed. -/
theorem diagonal_certified_downward_closed {s t : ℕ} (hst : s ≤ t)
    (h : ∃ L, certifiedKill (periodLcm t) (periodLcm t) L) :
    ∃ L, certifiedKill (periodLcm s) (periodLcm s) L := by
  obtain ⟨m, hm⟩ := periodLcm_dvd_of_le hst
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      have := periodLcm_pos t
      rw [hm, h0, Nat.mul_zero] at this
      omega
    · exact hpos
  refine exists_certifiedKill_descends (m := m) (H := periodLcm s) hmpos ?_
  rw [Nat.mul_comm] at hm
  rwa [← hm]

/-- **PROVED historical-frontier corollary.**  A diagonal certificate at `t = 67` implies
one at every `t ≤ 67`.  The name records the former frontier; the current finite band extends
through `t = 82`. -/
theorem frontier_certificate_implies_all_seed {L : ℕ}
    (hcert : certifiedKill (periodLcm 67) (periodLcm 67) L) (t : ℕ) (ht : t ≤ 67) :
    ∃ L', certifiedKill (periodLcm t) (periodLcm t) L' :=
  diagonal_certified_downward_closed ht ⟨L, hcert⟩

/-- **PROVED equivalence.**  Because the certified region is downward closed, "certified for
cofinally many `t`" collapses to "certified at every `t`".  So #249 is equivalent to the
diagonal certificate holding at *every* rung — and its failure means the certified region is
a bounded initial segment `[0, t*]`.  (Stated for precision; the content of this section is
the downward closure, not this equivalence.) -/
theorem irrational_iff_all_diagonal_certified :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      ↔ ∀ t : ℕ, ∃ L, certifiedKill (periodLcm t) (periodLcm t) L := by
  constructor
  · intro hirr t
    refine exists_certifiedKill_of_tail_diff_notMem_int ?_
    intro hmem
    rw [mem_int_iff_scaled] at hmem
    obtain ⟨K, hK⟩ := hmem
    have hHpos : 0 < periodLcm t := periodLcm_pos t
    have hone : (1 : ℝ) < (2 : ℝ) ^ periodLcm t := by
      apply one_lt_pow₀ (by norm_num)
      omega
    have hne1 : ((2 : ℝ) ^ periodLcm t - 1) ≠ 0 := by linarith
    have hne2 : ((2 : ℝ) ^ periodLcm t) ≠ 0 := by positivity
    have hq : (((K : ℚ) / ((2 : ℚ) ^ periodLcm t * ((2 : ℚ) ^ periodLcm t - 1)) : ℚ) : ℝ)
        = (K : ℝ) / ((2 : ℝ) ^ periodLcm t * ((2 : ℝ) ^ periodLcm t - 1)) := by
      push_cast
      ring
    refine hirr ⟨(K : ℚ) / ((2 : ℚ) ^ periodLcm t * ((2 : ℚ) ^ periodLcm t - 1)), ?_⟩
    rw [hq, hK]
    field_simp
  · intro hall
    refine irrational_totient_series_of_lcm_diagonal_certificate_supply fun t₀ => ?_
    obtain ⟨L, hL⟩ := hall t₀
    exact ⟨t₀, le_rfl, L, hL⟩

end AngleA1
end Lift
end ErdosProblems
