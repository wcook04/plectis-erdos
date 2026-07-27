/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.DemandLedger.edges.Discharge1_G097

/-!
# The t = 67 cell: reconstruction probe and first new diagonal deposit

`Erdos249257/DiagonalPincerCertificatesT64.lean` certifies the diagonal cell at
`t = 64`, and `DemandLedger.Discharge1G097.exists_diagonalKill_le_66` closes every
scale `t ≤ 66` by plateau transfer.  The first cell the corpus had never touched is

  `H 67 = 67 * H 66 = 79211881234889091923261227200`.

This module does three things.

## 1. A depth law for the lift (no factorisation needed)

`certifiedKill_four_mul_lt` extracts `4*H < 2^L` from any diagonal certificate;
`certifiedKill_lift_depth_ladder` turns that into the local cost law for a rung:
if `L` sits at its floor for `H` (`2^L ≤ 8*H`) and the rung multiplier `p` is at
least `2^k`, then **every** certificate at `p*H` has depth at least `L + k`.
No lift can be depth-preserving; the window deepens by `⌊log₂ p⌋` per rung.
Specialised at `p = 67` this gives `t67_depth_floor : 98 ≤ L`, and hence
`t67_not_certifiedKill_at_t64_depth`, the sharp negative that the `t = 64`
depth `93` is dead at `t = 67`.

## 2. The certificate itself

The window `[H+1, H+100] ∪ [2H+1, 2H+100]` is 200 integers of 29–30 digits.  Each
is fully factored, every prime factor above `10^7` carries a Lucas certificate
(411 new ones, closed recursively through their `p-1` factorisations), and each
totient is reconstructed through `totient_factorBlocks`.  Nothing is decided by
`native_decide`; nothing is axiomatised.

`certifiedKill_diagonal_t67 : certifiedKill (periodLcm 67) (periodLcm 67) 100`.

## 3. Minimality and the new plateau

`not_certifiedKill_diagonal_t67_98` and `..._99` show the two depths permitted by
the floor both fail, so `t67_minimal_depth` pins the least certified depth at
`t = 67` to exactly `100`.  Since `68 = 4·17`, `69 = 3·23`, `70 = 2·35` are all
plateau steps, `exists_diagonalKill_le_70` extends the unbroken certified band
from `t ≤ 66` to `t ≤ 70`.  The next jump is the prime `71`.

This is one rung, not the ladder: the cofinal supply that
`irrational_totient_series_of_lcm_diagonal_certificate_supply` consumes is still
open.  What this module supplies is the empirical price of a rung and a law
saying the price cannot stay flat.
-/

namespace ErdosProblems
namespace Lift

open Erdos249257 Erdos249257.TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## 1. The depth law -/

/-- Every diagonal certificate at scale `H` forces its modulus past `4*H`:
the forbidden zone has radius `2H + L + 2`, and both excluded arcs must fit. -/
theorem certifiedKill_four_mul_lt {H L : ℕ} (h : certifiedKill H H L) :
    4 * H < 2 ^ L := by
  have hz := certifiedKill_depth_floor h
  have h4 : ((4 * H : ℕ) : ℤ) < ((2 ^ L : ℕ) : ℤ) := by push_cast; push_cast at hz; linarith
  exact_mod_cast h4

/-- Scaling the cell by `p ≥ 2^k` scales the required modulus by `2^k`. -/
theorem certifiedKill_lift_depth {p H L' k : ℕ} (hk : 2 ^ k ≤ p)
    (h : certifiedKill (p * H) (p * H) L') : 2 ^ (k + 2) * H < 2 ^ L' := by
  have h4 := certifiedKill_four_mul_lt h
  calc 2 ^ (k + 2) * H = 2 ^ k * (4 * H) := by ring
    _ ≤ p * (4 * H) := Nat.mul_le_mul_right _ hk
    _ = 4 * (p * H) := by ring
    _ < 2 ^ L' := h4

/-- **Depth ladder.**  If `L` is at its floor for the cell `H` (`2^L ≤ 8*H`) and the
rung multiplier `p` is at least `2^k`, then every certificate at the scaled cell
`p*H` has depth at least `L + k`.  A depth-preserving lift is impossible. -/
theorem certifiedKill_lift_depth_ladder {p H L L' k : ℕ} (hk : 2 ^ k ≤ p)
    (hfloor : 2 ^ L ≤ 8 * H) (h : certifiedKill (p * H) (p * H) L') :
    L + k ≤ L' := by
  have h1 : 2 ^ (k + 2) * H < 2 ^ L' := certifiedKill_lift_depth hk h
  have h2 : 2 ^ (L + k + 2) ≤ 8 * (2 ^ (k + 2) * H) := by
    calc 2 ^ (L + k + 2) = 2 ^ (k + 2) * 2 ^ L := by ring
      _ ≤ 2 ^ (k + 2) * (8 * H) := Nat.mul_le_mul_left _ hfloor
      _ = 8 * (2 ^ (k + 2) * H) := by ring
  have h3 : 2 ^ (L + k + 2) < 2 ^ (L' + 3) := by
    calc 2 ^ (L + k + 2) ≤ 8 * (2 ^ (k + 2) * H) := h2
      _ < 8 * 2 ^ L' := by omega
      _ = 2 ^ (L' + 3) := by ring
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp h3
  omega

theorem periodLcm_67_value : periodLcm 67 = 79211881234889091923261227200 := by decide

/-- The `t = 67` cell admits no certificate of depth below `98`. -/
theorem t67_depth_floor {L : ℕ} (h : certifiedKill (periodLcm 67) (periodLcm 67) L) :
    98 ≤ L := by
  rcases Nat.lt_or_ge L 98 with hlt | hge
  swap
  · exact hge
  exfalso
  have h4 := certifiedKill_four_mul_lt h
  rw [periodLcm_67_value] at h4
  have hle : (2 : ℕ) ^ L ≤ 2 ^ 97 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbad : (4 * 79211881234889091923261227200 : ℕ) < 2 ^ 97 := lt_of_lt_of_le h4 hle
  norm_num at hbad

/-- **Sharp negative.**  The depth that certifies `t = 64` is dead at `t = 67`. -/
theorem t67_not_certifiedKill_at_t64_depth :
    ¬ certifiedKill (periodLcm 67) (periodLcm 67) 93 := fun h => by
  have := t67_depth_floor h; omega

/-! ## 2. Primality leaves for the t = 67 window -/

theorem natCast_zmod_eq_one_iff' (a m : ℕ) :
    (a : ZMod m) = 1 ↔ a % m = 1 % m := by
  simpa using ZMod.natCast_eq_natCast_iff' a 1 m

theorem natCast_zmod_ne_one_iff' (a m : ℕ) :
    (a : ZMod m) ≠ 1 ↔ a % m ≠ 1 % m :=
  not_congr (natCast_zmod_eq_one_iff' a m)

private theorem prime_small_2 : Nat.Prime 2 := by norm_num
private theorem prime_small_3 : Nat.Prime 3 := by norm_num
private theorem prime_small_5 : Nat.Prime 5 := by norm_num
private theorem prime_small_7 : Nat.Prime 7 := by norm_num
private theorem prime_small_11 : Nat.Prime 11 := by norm_num
private theorem prime_small_13 : Nat.Prime 13 := by norm_num
private theorem prime_small_17 : Nat.Prime 17 := by norm_num
private theorem prime_small_19 : Nat.Prime 19 := by norm_num
private theorem prime_small_23 : Nat.Prime 23 := by norm_num
private theorem prime_small_29 : Nat.Prime 29 := by norm_num
private theorem prime_small_31 : Nat.Prime 31 := by norm_num
private theorem prime_small_37 : Nat.Prime 37 := by norm_num
private theorem prime_small_41 : Nat.Prime 41 := by norm_num
private theorem prime_small_43 : Nat.Prime 43 := by norm_num
private theorem prime_small_47 : Nat.Prime 47 := by norm_num
private theorem prime_small_53 : Nat.Prime 53 := by norm_num
private theorem prime_small_59 : Nat.Prime 59 := by norm_num
private theorem prime_small_61 : Nat.Prime 61 := by norm_num
private theorem prime_small_67 : Nat.Prime 67 := by norm_num
private theorem prime_small_71 : Nat.Prime 71 := by norm_num
private theorem prime_small_73 : Nat.Prime 73 := by norm_num
private theorem prime_small_79 : Nat.Prime 79 := by norm_num
private theorem prime_small_83 : Nat.Prime 83 := by norm_num
private theorem prime_small_89 : Nat.Prime 89 := by norm_num
private theorem prime_small_97 : Nat.Prime 97 := by norm_num
private theorem prime_small_101 : Nat.Prime 101 := by norm_num
private theorem prime_small_103 : Nat.Prime 103 := by norm_num
private theorem prime_small_107 : Nat.Prime 107 := by norm_num
private theorem prime_small_109 : Nat.Prime 109 := by norm_num
private theorem prime_small_113 : Nat.Prime 113 := by norm_num
private theorem prime_small_127 : Nat.Prime 127 := by norm_num
private theorem prime_small_131 : Nat.Prime 131 := by norm_num
private theorem prime_small_137 : Nat.Prime 137 := by norm_num
private theorem prime_small_139 : Nat.Prime 139 := by norm_num
private theorem prime_small_149 : Nat.Prime 149 := by norm_num
private theorem prime_small_151 : Nat.Prime 151 := by norm_num
private theorem prime_small_157 : Nat.Prime 157 := by norm_num
private theorem prime_small_163 : Nat.Prime 163 := by norm_num
private theorem prime_small_167 : Nat.Prime 167 := by norm_num
private theorem prime_small_173 : Nat.Prime 173 := by norm_num
private theorem prime_small_179 : Nat.Prime 179 := by norm_num
private theorem prime_small_181 : Nat.Prime 181 := by norm_num
private theorem prime_small_193 : Nat.Prime 193 := by norm_num
private theorem prime_small_197 : Nat.Prime 197 := by norm_num
private theorem prime_small_211 : Nat.Prime 211 := by norm_num
private theorem prime_small_223 : Nat.Prime 223 := by norm_num
private theorem prime_small_227 : Nat.Prime 227 := by norm_num
private theorem prime_small_233 : Nat.Prime 233 := by norm_num
private theorem prime_small_239 : Nat.Prime 239 := by norm_num
private theorem prime_small_241 : Nat.Prime 241 := by norm_num
private theorem prime_small_251 : Nat.Prime 251 := by norm_num
private theorem prime_small_257 : Nat.Prime 257 := by norm_num
private theorem prime_small_263 : Nat.Prime 263 := by norm_num
private theorem prime_small_269 : Nat.Prime 269 := by norm_num
private theorem prime_small_281 : Nat.Prime 281 := by norm_num
private theorem prime_small_293 : Nat.Prime 293 := by norm_num
private theorem prime_small_311 : Nat.Prime 311 := by norm_num
private theorem prime_small_313 : Nat.Prime 313 := by norm_num
private theorem prime_small_317 : Nat.Prime 317 := by norm_num
private theorem prime_small_331 : Nat.Prime 331 := by norm_num
private theorem prime_small_359 : Nat.Prime 359 := by norm_num
private theorem prime_small_379 : Nat.Prime 379 := by norm_num
private theorem prime_small_389 : Nat.Prime 389 := by norm_num
private theorem prime_small_433 : Nat.Prime 433 := by norm_num
private theorem prime_small_449 : Nat.Prime 449 := by norm_num
private theorem prime_small_457 : Nat.Prime 457 := by norm_num
private theorem prime_small_461 : Nat.Prime 461 := by norm_num
private theorem prime_small_467 : Nat.Prime 467 := by norm_num
private theorem prime_small_479 : Nat.Prime 479 := by norm_num
private theorem prime_small_491 : Nat.Prime 491 := by norm_num
private theorem prime_small_499 : Nat.Prime 499 := by norm_num
private theorem prime_small_503 : Nat.Prime 503 := by norm_num
private theorem prime_small_557 : Nat.Prime 557 := by norm_num
private theorem prime_small_593 : Nat.Prime 593 := by norm_num
private theorem prime_small_683 : Nat.Prime 683 := by norm_num
private theorem prime_small_811 : Nat.Prime 811 := by norm_num
private theorem prime_small_911 : Nat.Prime 911 := by norm_num
private theorem prime_small_919 : Nat.Prime 919 := by norm_num
private theorem prime_small_929 : Nat.Prime 929 := by norm_num
private theorem prime_small_953 : Nat.Prime 953 := by norm_num
private theorem prime_small_983 : Nat.Prime 983 := by norm_num
private theorem prime_small_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_small_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_small_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_small_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_small_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_small_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_small_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_small_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_small_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_small_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_small_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_small_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_small_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_small_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_small_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_small_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_small_2339 : Nat.Prime 2339 := by norm_num
private theorem prime_small_2633 : Nat.Prime 2633 := by norm_num
private theorem prime_small_2659 : Nat.Prime 2659 := by norm_num
private theorem prime_small_2803 : Nat.Prime 2803 := by norm_num
private theorem prime_small_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_small_3037 : Nat.Prime 3037 := by norm_num
private theorem prime_small_3329 : Nat.Prime 3329 := by norm_num
private theorem prime_small_3593 : Nat.Prime 3593 := by norm_num
private theorem prime_small_3947 : Nat.Prime 3947 := by norm_num
private theorem prime_small_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_small_5077 : Nat.Prime 5077 := by norm_num
private theorem prime_small_5419 : Nat.Prime 5419 := by norm_num
private theorem prime_small_5851 : Nat.Prime 5851 := by norm_num
private theorem prime_small_6073 : Nat.Prime 6073 := by norm_num
private theorem prime_small_7417 : Nat.Prime 7417 := by norm_num
private theorem prime_small_7823 : Nat.Prime 7823 := by norm_num
private theorem prime_small_7949 : Nat.Prime 7949 := by norm_num
private theorem prime_small_9013 : Nat.Prime 9013 := by norm_num
private theorem prime_small_9181 : Nat.Prime 9181 := by norm_num
private theorem prime_small_9397 : Nat.Prime 9397 := by norm_num
private theorem prime_small_11177 : Nat.Prime 11177 := by norm_num
private theorem prime_small_11909 : Nat.Prime 11909 := by norm_num
private theorem prime_small_12101 : Nat.Prime 12101 := by norm_num
private theorem prime_small_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_small_14251 : Nat.Prime 14251 := by norm_num
private theorem prime_small_14639 : Nat.Prime 14639 := by norm_num
private theorem prime_small_15277 : Nat.Prime 15277 := by norm_num
private theorem prime_small_15971 : Nat.Prime 15971 := by norm_num
private theorem prime_small_16763 : Nat.Prime 16763 := by norm_num
private theorem prime_small_16943 : Nat.Prime 16943 := by norm_num
private theorem prime_small_18457 : Nat.Prime 18457 := by norm_num
private theorem prime_small_19213 : Nat.Prime 19213 := by norm_num
private theorem prime_small_19727 : Nat.Prime 19727 := by norm_num
private theorem prime_small_19973 : Nat.Prime 19973 := by norm_num
private theorem prime_small_20483 : Nat.Prime 20483 := by norm_num
private theorem prime_small_21569 : Nat.Prime 21569 := by norm_num
private theorem prime_small_24889 : Nat.Prime 24889 := by norm_num
private theorem prime_small_29401 : Nat.Prime 29401 := by norm_num
private theorem prime_small_30391 : Nat.Prime 30391 := by norm_num
private theorem prime_small_31321 : Nat.Prime 31321 := by norm_num
private theorem prime_small_34061 : Nat.Prime 34061 := by norm_num
private theorem prime_small_35591 : Nat.Prime 35591 := by norm_num
private theorem prime_small_35801 : Nat.Prime 35801 := by norm_num
private theorem prime_small_35993 : Nat.Prime 35993 := by norm_num
private theorem prime_small_37511 : Nat.Prime 37511 := by norm_num
private theorem prime_small_37591 : Nat.Prime 37591 := by norm_num
private theorem prime_small_38261 : Nat.Prime 38261 := by norm_num
private theorem prime_small_38333 : Nat.Prime 38333 := by norm_num
private theorem prime_small_42209 : Nat.Prime 42209 := by norm_num
private theorem prime_small_49783 : Nat.Prime 49783 := by norm_num
private theorem prime_small_50077 : Nat.Prime 50077 := by norm_num
private theorem prime_small_51419 : Nat.Prime 51419 := by norm_num
private theorem prime_small_52747 : Nat.Prime 52747 := by norm_num
private theorem prime_small_58921 : Nat.Prime 58921 := by norm_num
private theorem prime_small_59693 : Nat.Prime 59693 := by norm_num
private theorem prime_small_87049 : Nat.Prime 87049 := by norm_num
private theorem prime_small_89387 : Nat.Prime 89387 := by norm_num
private theorem prime_small_132749 : Nat.Prime 132749 := by norm_num
private theorem prime_small_150659 : Nat.Prime 150659 := by norm_num
private theorem prime_small_161059 : Nat.Prime 161059 := by norm_num
private theorem prime_small_166319 : Nat.Prime 166319 := by norm_num
private theorem prime_small_181141 : Nat.Prime 181141 := by norm_num
private theorem prime_small_181199 : Nat.Prime 181199 := by norm_num
private theorem prime_small_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_small_214891 : Nat.Prime 214891 := by norm_num
private theorem prime_small_252029 : Nat.Prime 252029 := by norm_num
private theorem prime_small_256279 : Nat.Prime 256279 := by norm_num
private theorem prime_small_271571 : Nat.Prime 271571 := by norm_num
private theorem prime_small_274403 : Nat.Prime 274403 := by norm_num
private theorem prime_small_279007 : Nat.Prime 279007 := by norm_num
private theorem prime_small_300557 : Nat.Prime 300557 := by norm_num
private theorem prime_small_305237 : Nat.Prime 305237 := by norm_num
private theorem prime_small_337969 : Nat.Prime 337969 := by norm_num
private theorem prime_small_448309 : Nat.Prime 448309 := by norm_num
private theorem prime_small_464171 : Nat.Prime 464171 := by norm_num
private theorem prime_small_493457 : Nat.Prime 493457 := by norm_num
private theorem prime_small_549323 : Nat.Prime 549323 := by norm_num
private theorem prime_small_562997 : Nat.Prime 562997 := by norm_num
private theorem prime_small_586501 : Nat.Prime 586501 := by norm_num
private theorem prime_small_644977 : Nat.Prime 644977 := by norm_num
private theorem prime_small_656809 : Nat.Prime 656809 := by norm_num
private theorem prime_small_761983 : Nat.Prime 761983 := by norm_num
private theorem prime_small_829627 : Nat.Prime 829627 := by norm_num
private theorem prime_small_1067879 : Nat.Prime 1067879 := by norm_num
private theorem prime_small_1155829 : Nat.Prime 1155829 := by norm_num
private theorem prime_small_1197953 : Nat.Prime 1197953 := by norm_num
private theorem prime_small_1749031 : Nat.Prime 1749031 := by norm_num
private theorem prime_small_2213147 : Nat.Prime 2213147 := by norm_num
private theorem prime_small_2406941 : Nat.Prime 2406941 := by norm_num
private theorem prime_small_2418613 : Nat.Prime 2418613 := by norm_num
private theorem prime_small_2545013 : Nat.Prime 2545013 := by norm_num
private theorem prime_small_2721133 : Nat.Prime 2721133 := by norm_num
private theorem prime_small_3342679 : Nat.Prime 3342679 := by norm_num
private theorem prime_small_3422179 : Nat.Prime 3422179 := by norm_num
private theorem prime_small_3422501 : Nat.Prime 3422501 := by norm_num
private theorem prime_small_3673367 : Nat.Prime 3673367 := by norm_num
private theorem prime_small_4128253 : Nat.Prime 4128253 := by norm_num
private theorem prime_small_4324669 : Nat.Prime 4324669 := by norm_num
private theorem prime_small_4360417 : Nat.Prime 4360417 := by norm_num
private theorem prime_small_5075633 : Nat.Prime 5075633 := by norm_num
private theorem prime_small_6455221 : Nat.Prime 6455221 := by norm_num
private theorem prime_small_8212951 : Nat.Prime 8212951 := by norm_num
private theorem prime_small_9501517 : Nat.Prime 9501517 := by norm_num

/-! ### Lucas roots and their recursive Pratt dependencies -/

theorem prime_lucas_10181683 : Nat.Prime 10181683 := by
  have hfermat : (3 : ZMod 10181683) ^ (10181683 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 10181683) ^ ((10181683 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 10181683) ^ ((10181683 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 10181683) ^ ((10181683 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 10181683) ^ ((10181683 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 10181683) ^ ((10181683 - 1) / 4253) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10181683 (3 : ZMod 10181683)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (19, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (19, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod = 10181683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_10213733 : Nat.Prime 10213733 := by
  have hfermat : (2 : ZMod 10213733) ^ (10213733 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 10213733) ^ ((10213733 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 10213733) ^ ((10213733 - 1) / 2553433) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10213733 (2 : ZMod 10213733)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2553433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2553433, 1)] : List FactorBlock).map factorBlockValue).prod = 10213733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_10638713 : Nat.Prime 10638713 := by
  have hfermat : (3 : ZMod 10638713) ^ (10638713 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 10638713) ^ ((10638713 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 10638713) ^ ((10638713 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 10638713) ^ ((10638713 - 1) / 189977) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10638713 (3 : ZMod 10638713)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (189977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (189977, 1)] : List FactorBlock).map factorBlockValue).prod = 10638713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_10700387 : Nat.Prime 10700387 := by
  have hfermat : (2 : ZMod 10700387) ^ (10700387 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 10700387) ^ ((10700387 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 10700387) ^ ((10700387 - 1) / 5350193) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10700387 (2 : ZMod 10700387)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5350193, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5350193, 1)] : List FactorBlock).map factorBlockValue).prod = 10700387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_10818389 : Nat.Prime 10818389 := by
  have hfermat : (2 : ZMod 10818389) ^ (10818389 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 10818389) ^ ((10818389 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 10818389) ^ ((10818389 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 10818389) ^ ((10818389 - 1) / 386371) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10818389 (2 : ZMod 10818389)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (386371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (386371, 1)] : List FactorBlock).map factorBlockValue).prod = 10818389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_10922987 : Nat.Prime 10922987 := by
  have hfermat : (2 : ZMod 10922987) ^ (10922987 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 10922987) ^ ((10922987 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 10922987) ^ ((10922987 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 10922987) ^ ((10922987 - 1) / 223) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 10922987) ^ ((10922987 - 1) / 1289) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10922987 (2 : ZMod 10922987)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (223, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (223, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod = 10922987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_11160307 : Nat.Prime 11160307 := by
  have hfermat : (2 : ZMod 11160307) ^ (11160307 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 11160307) ^ ((11160307 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 11160307) ^ ((11160307 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 11160307) ^ ((11160307 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 11160307) ^ ((11160307 - 1) / 14419) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11160307 (2 : ZMod 11160307)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (43, 1), (14419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (43, 1), (14419, 1)] : List FactorBlock).map factorBlockValue).prod = 11160307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_11267563 : Nat.Prime 11267563 := by
  have hfermat : (2 : ZMod 11267563) ^ (11267563 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 11267563) ^ ((11267563 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 11267563) ^ ((11267563 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 11267563) ^ ((11267563 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 11267563) ^ ((11267563 - 1) / 81649) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11267563 (2 : ZMod 11267563)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (81649, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (81649, 1)] : List FactorBlock).map factorBlockValue).prod = 11267563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_11412523 : Nat.Prime 11412523 := by
  have hfermat : (2 : ZMod 11412523) ^ (11412523 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 11412523) ^ ((11412523 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 11412523) ^ ((11412523 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 11412523) ^ ((11412523 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 11412523) ^ ((11412523 - 1) / 19213) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11412523 (2 : ZMod 11412523)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (11, 1), (19213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (11, 1), (19213, 1)] : List FactorBlock).map factorBlockValue).prod = 11412523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_11535547 : Nat.Prime 11535547 := by
  have hfermat : (2 : ZMod 11535547) ^ (11535547 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 11535547) ^ ((11535547 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 11535547) ^ ((11535547 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 11535547) ^ ((11535547 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 11535547) ^ ((11535547 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 11535547) ^ ((11535547 - 1) / 9199) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11535547 (2 : ZMod 11535547)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (19, 1), (9199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (19, 1), (9199, 1)] : List FactorBlock).map factorBlockValue).prod = 11535547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_11666833 : Nat.Prime 11666833 := by
  have hfermat : (5 : ZMod 11666833) ^ (11666833 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 11666833) ^ ((11666833 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 11666833) ^ ((11666833 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 11666833) ^ ((11666833 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 11666833) ^ ((11666833 - 1) / 2731) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11666833 (5 : ZMod 11666833)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (89, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (89, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod = 11666833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_12013949 : Nat.Prime 12013949 := by
  have hfermat : (2 : ZMod 12013949) ^ (12013949 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 12013949) ^ ((12013949 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 12013949) ^ ((12013949 - 1) / 3003487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12013949 (2 : ZMod 12013949)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3003487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3003487, 1)] : List FactorBlock).map factorBlockValue).prod = 12013949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_12022291 : Nat.Prime 12022291 := by
  have hfermat : (3 : ZMod 12022291) ^ (12022291 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 12022291) ^ ((12022291 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 12022291) ^ ((12022291 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 12022291) ^ ((12022291 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 12022291) ^ ((12022291 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 12022291) ^ ((12022291 - 1) / 6361) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12022291 (3 : ZMod 12022291)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (7, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (7, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod = 12022291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_12035197 : Nat.Prime 12035197 := by
  have hfermat : (2 : ZMod 12035197) ^ (12035197 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 12035197) ^ ((12035197 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 12035197) ^ ((12035197 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 12035197) ^ ((12035197 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 12035197) ^ ((12035197 - 1) / 2371) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12035197 (2 : ZMod 12035197)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (47, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (47, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod = 12035197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_12334013 : Nat.Prime 12334013 := by
  have hfermat : (2 : ZMod 12334013) ^ (12334013 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 12334013) ^ ((12334013 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 12334013) ^ ((12334013 - 1) / 3083503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12334013 (2 : ZMod 12334013)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3083503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3083503, 1)] : List FactorBlock).map factorBlockValue).prod = 12334013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_13047029 : Nat.Prime 13047029 := by
  have hfermat : (2 : ZMod 13047029) ^ (13047029 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 13047029) ^ ((13047029 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 13047029) ^ ((13047029 - 1) / 1213) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 13047029) ^ ((13047029 - 1) / 2689) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 13047029 (2 : ZMod 13047029)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1213, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1213, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod = 13047029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_13285717 : Nat.Prime 13285717 := by
  have hfermat : (2 : ZMod 13285717) ^ (13285717 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 13285717) ^ ((13285717 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 13285717) ^ ((13285717 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 13285717) ^ ((13285717 - 1) / 683) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 13285717) ^ ((13285717 - 1) / 1621) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 13285717 (2 : ZMod 13285717)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (683, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (683, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod = 13285717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_13818191 : Nat.Prime 13818191 := by
  have hfermat : (7 : ZMod 13818191) ^ (13818191 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 13818191) ^ ((13818191 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 13818191) ^ ((13818191 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 13818191) ^ ((13818191 - 1) / 1381819) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 13818191 (7 : ZMod 13818191)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (1381819, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (1381819, 1)] : List FactorBlock).map factorBlockValue).prod = 13818191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_13912193 : Nat.Prime 13912193 := by
  have hfermat : (3 : ZMod 13912193) ^ (13912193 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 13912193) ^ ((13912193 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 13912193) ^ ((13912193 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 13912193) ^ ((13912193 - 1) / 15527) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 13912193 (3 : ZMod 13912193)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (7, 1), (15527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (7, 1), (15527, 1)] : List FactorBlock).map factorBlockValue).prod = 13912193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_13954663 : Nat.Prime 13954663 := by
  have hfermat : (5 : ZMod 13954663) ^ (13954663 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 13954663) ^ ((13954663 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 13954663) ^ ((13954663 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 13954663) ^ ((13954663 - 1) / 775259) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 13954663 (5 : ZMod 13954663)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (775259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (775259, 1)] : List FactorBlock).map factorBlockValue).prod = 13954663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_13974437 : Nat.Prime 13974437 := by
  have hfermat : (2 : ZMod 13974437) ^ (13974437 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 13974437) ^ ((13974437 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 13974437) ^ ((13974437 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 13974437) ^ ((13974437 - 1) / 389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 13974437) ^ ((13974437 - 1) / 1283) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 13974437 (2 : ZMod 13974437)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (389, 1), (1283, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (389, 1), (1283, 1)] : List FactorBlock).map factorBlockValue).prod = 13974437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_13991203 : Nat.Prime 13991203 := by
  have hfermat : (2 : ZMod 13991203) ^ (13991203 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 13991203) ^ ((13991203 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 13991203) ^ ((13991203 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 13991203) ^ ((13991203 - 1) / 173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 13991203) ^ ((13991203 - 1) / 4493) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 13991203 (2 : ZMod 13991203)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (173, 1), (4493, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (173, 1), (4493, 1)] : List FactorBlock).map factorBlockValue).prod = 13991203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_14547479 : Nat.Prime 14547479 := by
  have hfermat : (7 : ZMod 14547479) ^ (14547479 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 14547479) ^ ((14547479 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 14547479) ^ ((14547479 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 14547479) ^ ((14547479 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 14547479) ^ ((14547479 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 14547479) ^ ((14547479 - 1) / 401) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 14547479 (7 : ZMod 14547479)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (97, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (97, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod = 14547479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_16159217 : Nat.Prime 16159217 := by
  have hfermat : (3 : ZMod 16159217) ^ (16159217 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 16159217) ^ ((16159217 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 16159217) ^ ((16159217 - 1) / 1009951) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 16159217 (3 : ZMod 16159217)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (1009951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (1009951, 1)] : List FactorBlock).map factorBlockValue).prod = 16159217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_16179727 : Nat.Prime 16179727 := by
  have hfermat : (3 : ZMod 16179727) ^ (16179727 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 16179727) ^ ((16179727 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 16179727) ^ ((16179727 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 16179727) ^ ((16179727 - 1) / 2696621) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 16179727 (3 : ZMod 16179727)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (2696621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (2696621, 1)] : List FactorBlock).map factorBlockValue).prod = 16179727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_16360037 : Nat.Prime 16360037 := by
  have hfermat : (2 : ZMod 16360037) ^ (16360037 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 16360037) ^ ((16360037 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 16360037) ^ ((16360037 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 16360037) ^ ((16360037 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 16360037) ^ ((16360037 - 1) / 53117) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 16360037 (2 : ZMod 16360037)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (11, 1), (53117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (11, 1), (53117, 1)] : List FactorBlock).map factorBlockValue).prod = 16360037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_16372409 : Nat.Prime 16372409 := by
  have hfermat : (3 : ZMod 16372409) ^ (16372409 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 16372409) ^ ((16372409 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 16372409) ^ ((16372409 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 16372409) ^ ((16372409 - 1) / 157427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 16372409 (3 : ZMod 16372409)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (157427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (157427, 1)] : List FactorBlock).map factorBlockValue).prod = 16372409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_16645627 : Nat.Prime 16645627 := by
  have hfermat : (2 : ZMod 16645627) ^ (16645627 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 16645627) ^ ((16645627 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 16645627) ^ ((16645627 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 16645627) ^ ((16645627 - 1) / 924757) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 16645627 (2 : ZMod 16645627)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (924757, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (924757, 1)] : List FactorBlock).map factorBlockValue).prod = 16645627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_17130167 : Nat.Prime 17130167 := by
  have hfermat : (5 : ZMod 17130167) ^ (17130167 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 17130167) ^ ((17130167 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 17130167) ^ ((17130167 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 17130167) ^ ((17130167 - 1) / 276293) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 17130167 (5 : ZMod 17130167)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (276293, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (276293, 1)] : List FactorBlock).map factorBlockValue).prod = 17130167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_17846863 : Nat.Prime 17846863 := by
  have hfermat : (3 : ZMod 17846863) ^ (17846863 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 17846863) ^ ((17846863 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 17846863) ^ ((17846863 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 17846863) ^ ((17846863 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 17846863) ^ ((17846863 - 1) / 270407) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 17846863 (3 : ZMod 17846863)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (270407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (270407, 1)] : List FactorBlock).map factorBlockValue).prod = 17846863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_18361589 : Nat.Prime 18361589 := by
  have hfermat : (3 : ZMod 18361589) ^ (18361589 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 18361589) ^ ((18361589 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 18361589) ^ ((18361589 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 18361589) ^ ((18361589 - 1) / 349) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 18361589) ^ ((18361589 - 1) / 1879) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 18361589 (3 : ZMod 18361589)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (349, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (349, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod = 18361589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_18370691 : Nat.Prime 18370691 := by
  have hfermat : (11 : ZMod 18370691) ^ (18370691 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (11 : ZMod 18370691) ^ ((18370691 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (11 : ZMod 18370691) ^ ((18370691 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (11 : ZMod 18370691) ^ ((18370691 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (11 : ZMod 18370691) ^ ((18370691 - 1) / 251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (11 : ZMod 18370691) ^ ((18370691 - 1) / 563) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 18370691 (11 : ZMod 18370691)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (251, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (251, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod = 18370691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_18439909 : Nat.Prime 18439909 := by
  have hfermat : (6 : ZMod 18439909) ^ (18439909 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 18439909) ^ ((18439909 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 18439909) ^ ((18439909 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 18439909) ^ ((18439909 - 1) / 1536659) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 18439909 (6 : ZMod 18439909)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1536659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1536659, 1)] : List FactorBlock).map factorBlockValue).prod = 18439909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_18462557 : Nat.Prime 18462557 := by
  have hfermat : (2 : ZMod 18462557) ^ (18462557 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 18462557) ^ ((18462557 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 18462557) ^ ((18462557 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 18462557) ^ ((18462557 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 18462557) ^ ((18462557 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 18462557) ^ ((18462557 - 1) / 251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 18462557 (2 : ZMod 18462557)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (37, 1), (71, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (37, 1), (71, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod = 18462557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_20138089 : Nat.Prime 20138089 := by
  have hfermat : (14 : ZMod 20138089) ^ (20138089 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (14 : ZMod 20138089) ^ ((20138089 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (14 : ZMod 20138089) ^ ((20138089 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (14 : ZMod 20138089) ^ ((20138089 - 1) / 839087) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 20138089 (14 : ZMod 20138089)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (839087, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (839087, 1)] : List FactorBlock).map factorBlockValue).prod = 20138089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_22326211 : Nat.Prime 22326211 := by
  have hfermat : (3 : ZMod 22326211) ^ (22326211 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 22326211) ^ ((22326211 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 22326211) ^ ((22326211 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 22326211) ^ ((22326211 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 22326211) ^ ((22326211 - 1) / 359) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 22326211) ^ ((22326211 - 1) / 691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 22326211 (3 : ZMod 22326211)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (359, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (359, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod = 22326211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_24096307 : Nat.Prime 24096307 := by
  have hfermat : (2 : ZMod 24096307) ^ (24096307 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 24096307) ^ ((24096307 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 24096307) ^ ((24096307 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 24096307) ^ ((24096307 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 24096307) ^ ((24096307 - 1) / 308927) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 24096307 (2 : ZMod 24096307)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (308927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (308927, 1)] : List FactorBlock).map factorBlockValue).prod = 24096307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_25969253 : Nat.Prime 25969253 := by
  have hfermat : (2 : ZMod 25969253) ^ (25969253 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 25969253) ^ ((25969253 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 25969253) ^ ((25969253 - 1) / 709) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 25969253) ^ ((25969253 - 1) / 9157) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 25969253 (2 : ZMod 25969253)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (709, 1), (9157, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (709, 1), (9157, 1)] : List FactorBlock).map factorBlockValue).prod = 25969253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_26094059 : Nat.Prime 26094059 := by
  have hfermat : (2 : ZMod 26094059) ^ (26094059 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 26094059) ^ ((26094059 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 26094059) ^ ((26094059 - 1) / 13047029) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 26094059 (2 : ZMod 26094059)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13047029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13047029, 1)] : List FactorBlock).map factorBlockValue).prod = 26094059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_13047029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_26241511 : Nat.Prime 26241511 := by
  have hfermat : (3 : ZMod 26241511) ^ (26241511 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 26241511) ^ ((26241511 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 26241511) ^ ((26241511 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 26241511) ^ ((26241511 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 26241511) ^ ((26241511 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 26241511) ^ ((26241511 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 26241511) ^ ((26241511 - 1) / 503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 26241511 (3 : ZMod 26241511)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (37, 1), (47, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (37, 1), (47, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod = 26241511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_27257491 : Nat.Prime 27257491 := by
  have hfermat : (3 : ZMod 27257491) ^ (27257491 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 27257491) ^ ((27257491 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 27257491) ^ ((27257491 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 27257491) ^ ((27257491 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 27257491) ^ ((27257491 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 27257491) ^ ((27257491 - 1) / 23297) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 27257491 (3 : ZMod 27257491)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (13, 1), (23297, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (13, 1), (23297, 1)] : List FactorBlock).map factorBlockValue).prod = 27257491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_29176943 : Nat.Prime 29176943 := by
  have hfermat : (5 : ZMod 29176943) ^ (29176943 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 29176943) ^ ((29176943 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 29176943) ^ ((29176943 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 29176943) ^ ((29176943 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 29176943) ^ ((29176943 - 1) / 8389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 29176943 (5 : ZMod 29176943)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (47, 1), (8389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (47, 1), (8389, 1)] : List FactorBlock).map factorBlockValue).prod = 29176943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_32039879 : Nat.Prime 32039879 := by
  have hfermat : (7 : ZMod 32039879) ^ (32039879 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 32039879) ^ ((32039879 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 32039879) ^ ((32039879 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 32039879) ^ ((32039879 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 32039879) ^ ((32039879 - 1) / 23251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 32039879 (7 : ZMod 32039879)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (53, 1), (23251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (53, 1), (23251, 1)] : List FactorBlock).map factorBlockValue).prod = 32039879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_33930539 : Nat.Prime 33930539 := by
  have hfermat : (2 : ZMod 33930539) ^ (33930539 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 33930539) ^ ((33930539 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 33930539) ^ ((33930539 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 33930539) ^ ((33930539 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 33930539) ^ ((33930539 - 1) / 11213) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 33930539 (2 : ZMod 33930539)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (89, 1), (11213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (89, 1), (11213, 1)] : List FactorBlock).map factorBlockValue).prod = 33930539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_34161091 : Nat.Prime 34161091 := by
  have hfermat : (2 : ZMod 34161091) ^ (34161091 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 34161091) ^ ((34161091 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 34161091) ^ ((34161091 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 34161091) ^ ((34161091 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 34161091) ^ ((34161091 - 1) / 1138703) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 34161091 (2 : ZMod 34161091)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (1138703, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (1138703, 1)] : List FactorBlock).map factorBlockValue).prod = 34161091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_34182751 : Nat.Prime 34182751 := by
  have hfermat : (3 : ZMod 34182751) ^ (34182751 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 34182751) ^ ((34182751 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 34182751) ^ ((34182751 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 34182751) ^ ((34182751 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 34182751) ^ ((34182751 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 34182751) ^ ((34182751 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 34182751) ^ ((34182751 - 1) / 383) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 34182751 (3 : ZMod 34182751)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 3), (7, 1), (17, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 3), (7, 1), (17, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod = 34182751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_34362949 : Nat.Prime 34362949 := by
  have hfermat : (7 : ZMod 34362949) ^ (34362949 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 34362949) ^ ((34362949 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 34362949) ^ ((34362949 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 34362949) ^ ((34362949 - 1) / 503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 34362949) ^ ((34362949 - 1) / 5693) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 34362949 (7 : ZMod 34362949)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (503, 1), (5693, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (503, 1), (5693, 1)] : List FactorBlock).map factorBlockValue).prod = 34362949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_38150129 : Nat.Prime 38150129 := by
  have hfermat : (3 : ZMod 38150129) ^ (38150129 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 38150129) ^ ((38150129 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 38150129) ^ ((38150129 - 1) / 2384383) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 38150129 (3 : ZMod 38150129)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (2384383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (2384383, 1)] : List FactorBlock).map factorBlockValue).prod = 38150129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_38208361 : Nat.Prime 38208361 := by
  have hfermat : (17 : ZMod 38208361) ^ (38208361 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (17 : ZMod 38208361) ^ ((38208361 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (17 : ZMod 38208361) ^ ((38208361 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (17 : ZMod 38208361) ^ ((38208361 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (17 : ZMod 38208361) ^ ((38208361 - 1) / 318403) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 38208361 (17 : ZMod 38208361)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (318403, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (318403, 1)] : List FactorBlock).map factorBlockValue).prod = 38208361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_39993221 : Nat.Prime 39993221 := by
  have hfermat : (2 : ZMod 39993221) ^ (39993221 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 39993221) ^ ((39993221 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 39993221) ^ ((39993221 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 39993221) ^ ((39993221 - 1) / 1999661) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 39993221 (2 : ZMod 39993221)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (1999661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (1999661, 1)] : List FactorBlock).map factorBlockValue).prod = 39993221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_40181971 : Nat.Prime 40181971 := by
  have hfermat : (3 : ZMod 40181971) ^ (40181971 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 40181971) ^ ((40181971 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 40181971) ^ ((40181971 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 40181971) ^ ((40181971 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 40181971) ^ ((40181971 - 1) / 1339399) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 40181971 (3 : ZMod 40181971)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (1339399, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (1339399, 1)] : List FactorBlock).map factorBlockValue).prod = 40181971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_40288723 : Nat.Prime 40288723 := by
  have hfermat : (2 : ZMod 40288723) ^ (40288723 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 40288723) ^ ((40288723 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 40288723) ^ ((40288723 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 40288723) ^ ((40288723 - 1) / 6714787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 40288723 (2 : ZMod 40288723)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (6714787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (6714787, 1)] : List FactorBlock).map factorBlockValue).prod = 40288723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_42879077 : Nat.Prime 42879077 := by
  have hfermat : (2 : ZMod 42879077) ^ (42879077 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 42879077) ^ ((42879077 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 42879077) ^ ((42879077 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 42879077) ^ ((42879077 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 42879077) ^ ((42879077 - 1) / 5861) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 42879077 (2 : ZMod 42879077)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (59, 1), (5861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (59, 1), (5861, 1)] : List FactorBlock).map factorBlockValue).prod = 42879077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_43963039 : Nat.Prime 43963039 := by
  have hfermat : (6 : ZMod 43963039) ^ (43963039 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 43963039) ^ ((43963039 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 43963039) ^ ((43963039 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 43963039) ^ ((43963039 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 43963039) ^ ((43963039 - 1) / 383) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 43963039) ^ ((43963039 - 1) / 911) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 43963039 (6 : ZMod 43963039)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (383, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (383, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod = 43963039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_44305501 : Nat.Prime 44305501 := by
  have hfermat : (2 : ZMod 44305501) ^ (44305501 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 44305501) ^ ((44305501 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 44305501) ^ ((44305501 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 44305501) ^ ((44305501 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 44305501) ^ ((44305501 - 1) / 29537) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 44305501 (2 : ZMod 44305501)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 3), (29537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 3), (29537, 1)] : List FactorBlock).map factorBlockValue).prod = 44305501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_44380291 : Nat.Prime 44380291 := by
  have hfermat : (2 : ZMod 44380291) ^ (44380291 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 44380291) ^ ((44380291 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 44380291) ^ ((44380291 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 44380291) ^ ((44380291 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 44380291) ^ ((44380291 - 1) / 1479343) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 44380291 (2 : ZMod 44380291)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (1479343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (1479343, 1)] : List FactorBlock).map factorBlockValue).prod = 44380291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_47080037 : Nat.Prime 47080037 := by
  have hfermat : (2 : ZMod 47080037) ^ (47080037 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 47080037) ^ ((47080037 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 47080037) ^ ((47080037 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 47080037) ^ ((47080037 - 1) / 161233) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 47080037 (2 : ZMod 47080037)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (73, 1), (161233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (73, 1), (161233, 1)] : List FactorBlock).map factorBlockValue).prod = 47080037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_50202227 : Nat.Prime 50202227 := by
  have hfermat : (2 : ZMod 50202227) ^ (50202227 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 50202227) ^ ((50202227 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 50202227) ^ ((50202227 - 1) / 3607) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 50202227) ^ ((50202227 - 1) / 6959) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 50202227 (2 : ZMod 50202227)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3607, 1), (6959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3607, 1), (6959, 1)] : List FactorBlock).map factorBlockValue).prod = 50202227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_50226469 : Nat.Prime 50226469 := by
  have hfermat : (2 : ZMod 50226469) ^ (50226469 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 50226469) ^ ((50226469 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 50226469) ^ ((50226469 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 50226469) ^ ((50226469 - 1) / 127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 50226469) ^ ((50226469 - 1) / 32957) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 50226469 (2 : ZMod 50226469)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (127, 1), (32957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (127, 1), (32957, 1)] : List FactorBlock).map factorBlockValue).prod = 50226469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_50474527 : Nat.Prime 50474527 := by
  have hfermat : (5 : ZMod 50474527) ^ (50474527 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 50474527) ^ ((50474527 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 50474527) ^ ((50474527 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 50474527) ^ ((50474527 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 50474527) ^ ((50474527 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 50474527) ^ ((50474527 - 1) / 10799) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 50474527 (5 : ZMod 50474527)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (41, 1), (10799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (41, 1), (10799, 1)] : List FactorBlock).map factorBlockValue).prod = 50474527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_52188119 : Nat.Prime 52188119 := by
  have hfermat : (7 : ZMod 52188119) ^ (52188119 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 52188119) ^ ((52188119 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 52188119) ^ ((52188119 - 1) / 26094059) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 52188119 (7 : ZMod 52188119)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (26094059, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (26094059, 1)] : List FactorBlock).map factorBlockValue).prod = 52188119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_26094059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_56506031 : Nat.Prime 56506031 := by
  have hfermat : (7 : ZMod 56506031) ^ (56506031 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 56506031) ^ ((56506031 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 56506031) ^ ((56506031 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 56506031) ^ ((56506031 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 56506031) ^ ((56506031 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 56506031) ^ ((56506031 - 1) / 21817) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 56506031 (7 : ZMod 56506031)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (37, 1), (21817, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (37, 1), (21817, 1)] : List FactorBlock).map factorBlockValue).prod = 56506031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_65754961 : Nat.Prime 65754961 := by
  have hfermat : (7 : ZMod 65754961) ^ (65754961 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 65754961) ^ ((65754961 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 65754961) ^ ((65754961 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 65754961) ^ ((65754961 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 65754961) ^ ((65754961 - 1) / 273979) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 65754961 (7 : ZMod 65754961)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (273979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (273979, 1)] : List FactorBlock).map factorBlockValue).prod = 65754961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_68782979 : Nat.Prime 68782979 := by
  have hfermat : (2 : ZMod 68782979) ^ (68782979 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 68782979) ^ ((68782979 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 68782979) ^ ((68782979 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 68782979) ^ ((68782979 - 1) / 277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 68782979) ^ ((68782979 - 1) / 11287) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 68782979 (2 : ZMod 68782979)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (277, 1), (11287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (277, 1), (11287, 1)] : List FactorBlock).map factorBlockValue).prod = 68782979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_73296611 : Nat.Prime 73296611 := by
  have hfermat : (6 : ZMod 73296611) ^ (73296611 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 73296611) ^ ((73296611 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 73296611) ^ ((73296611 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 73296611) ^ ((73296611 - 1) / 7329661) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 73296611 (6 : ZMod 73296611)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7329661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7329661, 1)] : List FactorBlock).map factorBlockValue).prod = 73296611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_75392963 : Nat.Prime 75392963 := by
  have hfermat : (2 : ZMod 75392963) ^ (75392963 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 75392963) ^ ((75392963 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 75392963) ^ ((75392963 - 1) / 619) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 75392963) ^ ((75392963 - 1) / 60899) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 75392963 (2 : ZMod 75392963)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (619, 1), (60899, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (619, 1), (60899, 1)] : List FactorBlock).map factorBlockValue).prod = 75392963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_81294557 : Nat.Prime 81294557 := by
  have hfermat : (3 : ZMod 81294557) ^ (81294557 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 81294557) ^ ((81294557 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 81294557) ^ ((81294557 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 81294557) ^ ((81294557 - 1) / 1087) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 81294557) ^ ((81294557 - 1) / 2671) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 81294557 (3 : ZMod 81294557)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (1087, 1), (2671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (1087, 1), (2671, 1)] : List FactorBlock).map factorBlockValue).prod = 81294557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_82220659 : Nat.Prime 82220659 := by
  have hfermat : (2 : ZMod 82220659) ^ (82220659 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 82220659) ^ ((82220659 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 82220659) ^ ((82220659 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 82220659) ^ ((82220659 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 82220659) ^ ((82220659 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 82220659) ^ ((82220659 - 1) / 15733) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 82220659 (2 : ZMod 82220659)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (67, 1), (15733, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (67, 1), (15733, 1)] : List FactorBlock).map factorBlockValue).prod = 82220659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_83215481 : Nat.Prime 83215481 := by
  have hfermat : (3 : ZMod 83215481) ^ (83215481 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 83215481) ^ ((83215481 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 83215481) ^ ((83215481 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 83215481) ^ ((83215481 - 1) / 127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 83215481) ^ ((83215481 - 1) / 16381) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 83215481 (3 : ZMod 83215481)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (127, 1), (16381, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (127, 1), (16381, 1)] : List FactorBlock).map factorBlockValue).prod = 83215481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_83533451 : Nat.Prime 83533451 := by
  have hfermat : (2 : ZMod 83533451) ^ (83533451 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 83533451) ^ ((83533451 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 83533451) ^ ((83533451 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 83533451) ^ ((83533451 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 83533451) ^ ((83533451 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 83533451) ^ ((83533451 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 83533451) ^ ((83533451 - 1) / 1669) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 83533451 (2 : ZMod 83533451)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (7, 1), (11, 1), (13, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (7, 1), (11, 1), (13, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod = 83533451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_83652677 : Nat.Prime 83652677 := by
  have hfermat : (2 : ZMod 83652677) ^ (83652677 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 83652677) ^ ((83652677 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 83652677) ^ ((83652677 - 1) / 2797) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 83652677) ^ ((83652677 - 1) / 7477) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 83652677 (2 : ZMod 83652677)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2797, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2797, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod = 83652677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_88562657 : Nat.Prime 88562657 := by
  have hfermat : (3 : ZMod 88562657) ^ (88562657 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 88562657) ^ ((88562657 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 88562657) ^ ((88562657 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 88562657) ^ ((88562657 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 88562657) ^ ((88562657 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 88562657) ^ ((88562657 - 1) / 1789) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 88562657 (3 : ZMod 88562657)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (7, 1), (13, 1), (17, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (7, 1), (13, 1), (17, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod = 88562657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_100297643 : Nat.Prime 100297643 := by
  have hfermat : (2 : ZMod 100297643) ^ (100297643 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 100297643) ^ ((100297643 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 100297643) ^ ((100297643 - 1) / 271) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 100297643) ^ ((100297643 - 1) / 185051) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 100297643 (2 : ZMod 100297643)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (271, 1), (185051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (271, 1), (185051, 1)] : List FactorBlock).map factorBlockValue).prod = 100297643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_107038651 : Nat.Prime 107038651 := by
  have hfermat : (3 : ZMod 107038651) ^ (107038651 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 107038651) ^ ((107038651 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 107038651) ^ ((107038651 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 107038651) ^ ((107038651 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 107038651) ^ ((107038651 - 1) / 167) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 107038651) ^ ((107038651 - 1) / 4273) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 107038651 (3 : ZMod 107038651)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (167, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (167, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod = 107038651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_107697571 : Nat.Prime 107697571 := by
  have hfermat : (2 : ZMod 107697571) ^ (107697571 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 107697571) ^ ((107697571 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 107697571) ^ ((107697571 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 107697571) ^ ((107697571 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 107697571) ^ ((107697571 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 107697571) ^ ((107697571 - 1) / 87559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 107697571 (2 : ZMod 107697571)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (41, 1), (87559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (41, 1), (87559, 1)] : List FactorBlock).map factorBlockValue).prod = 107697571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_112736581 : Nat.Prime 112736581 := by
  have hfermat : (2 : ZMod 112736581) ^ (112736581 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 112736581) ^ ((112736581 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 112736581) ^ ((112736581 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 112736581) ^ ((112736581 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 112736581) ^ ((112736581 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 112736581) ^ ((112736581 - 1) / 170813) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 112736581 (2 : ZMod 112736581)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (11, 1), (170813, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (11, 1), (170813, 1)] : List FactorBlock).map factorBlockValue).prod = 112736581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_117039913 : Nat.Prime 117039913 := by
  have hfermat : (5 : ZMod 117039913) ^ (117039913 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 117039913) ^ ((117039913 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 117039913) ^ ((117039913 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 117039913) ^ ((117039913 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 117039913) ^ ((117039913 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 117039913) ^ ((117039913 - 1) / 983) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 117039913 (5 : ZMod 117039913)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 2), (41, 1), (983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 2), (41, 1), (983, 1)] : List FactorBlock).map factorBlockValue).prod = 117039913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_129273737 : Nat.Prime 129273737 := by
  have hfermat : (3 : ZMod 129273737) ^ (129273737 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 129273737) ^ ((129273737 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 129273737) ^ ((129273737 - 1) / 16159217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 129273737 (3 : ZMod 129273737)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (16159217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (16159217, 1)] : List FactorBlock).map factorBlockValue).prod = 129273737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_16159217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_136950277 : Nat.Prime 136950277 := by
  have hfermat : (2 : ZMod 136950277) ^ (136950277 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 136950277) ^ ((136950277 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 136950277) ^ ((136950277 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 136950277) ^ ((136950277 - 1) / 11412523) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 136950277 (2 : ZMod 136950277)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11412523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11412523, 1)] : List FactorBlock).map factorBlockValue).prod = 136950277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_11412523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_137565959 : Nat.Prime 137565959 := by
  have hfermat : (11 : ZMod 137565959) ^ (137565959 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (11 : ZMod 137565959) ^ ((137565959 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (11 : ZMod 137565959) ^ ((137565959 - 1) / 68782979) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 137565959 (11 : ZMod 137565959)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (68782979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (68782979, 1)] : List FactorBlock).map factorBlockValue).prod = 137565959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_68782979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_139352131 : Nat.Prime 139352131 := by
  have hfermat : (2 : ZMod 139352131) ^ (139352131 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 139352131) ^ ((139352131 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 139352131) ^ ((139352131 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 139352131) ^ ((139352131 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 139352131) ^ ((139352131 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 139352131) ^ ((139352131 - 1) / 16649) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 139352131 (2 : ZMod 139352131)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (31, 1), (16649, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (31, 1), (16649, 1)] : List FactorBlock).map factorBlockValue).prod = 139352131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_147862763 : Nat.Prime 147862763 := by
  have hfermat : (2 : ZMod 147862763) ^ (147862763 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 147862763) ^ ((147862763 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 147862763) ^ ((147862763 - 1) / 281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 147862763) ^ ((147862763 - 1) / 263101) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 147862763 (2 : ZMod 147862763)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (281, 1), (263101, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (281, 1), (263101, 1)] : List FactorBlock).map factorBlockValue).prod = 147862763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_148539203 : Nat.Prime 148539203 := by
  have hfermat : (2 : ZMod 148539203) ^ (148539203 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 148539203) ^ ((148539203 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 148539203) ^ ((148539203 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 148539203) ^ ((148539203 - 1) / 1033) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 148539203) ^ ((148539203 - 1) / 10271) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 148539203 (2 : ZMod 148539203)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (1033, 1), (10271, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (1033, 1), (10271, 1)] : List FactorBlock).map factorBlockValue).prod = 148539203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_166430963 : Nat.Prime 166430963 := by
  have hfermat : (2 : ZMod 166430963) ^ (166430963 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 166430963) ^ ((166430963 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 166430963) ^ ((166430963 - 1) / 83215481) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 166430963 (2 : ZMod 166430963)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (83215481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (83215481, 1)] : List FactorBlock).map factorBlockValue).prod = 166430963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_83215481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_169969277 : Nat.Prime 169969277 := by
  have hfermat : (2 : ZMod 169969277) ^ (169969277 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 169969277) ^ ((169969277 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 169969277) ^ ((169969277 - 1) / 2111) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 169969277) ^ ((169969277 - 1) / 20129) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 169969277 (2 : ZMod 169969277)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2111, 1), (20129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2111, 1), (20129, 1)] : List FactorBlock).map factorBlockValue).prod = 169969277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_175693457 : Nat.Prime 175693457 := by
  have hfermat : (3 : ZMod 175693457) ^ (175693457 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 175693457) ^ ((175693457 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 175693457) ^ ((175693457 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 175693457) ^ ((175693457 - 1) / 577939) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 175693457 (3 : ZMod 175693457)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (19, 1), (577939, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (19, 1), (577939, 1)] : List FactorBlock).map factorBlockValue).prod = 175693457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_191204753 : Nat.Prime 191204753 := by
  have hfermat : (3 : ZMod 191204753) ^ (191204753 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 191204753) ^ ((191204753 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 191204753) ^ ((191204753 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 191204753) ^ ((191204753 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 191204753) ^ ((191204753 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 191204753) ^ ((191204753 - 1) / 191) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 191204753 (3 : ZMod 191204753)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (19, 1), (37, 1), (89, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (19, 1), (37, 1), (89, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod = 191204753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_200595287 : Nat.Prime 200595287 := by
  have hfermat : (5 : ZMod 200595287) ^ (200595287 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 200595287) ^ ((200595287 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 200595287) ^ ((200595287 - 1) / 100297643) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 200595287 (5 : ZMod 200595287)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (100297643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (100297643, 1)] : List FactorBlock).map factorBlockValue).prod = 200595287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_100297643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_229047163 : Nat.Prime 229047163 := by
  have hfermat : (2 : ZMod 229047163) ^ (229047163 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 229047163) ^ ((229047163 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 229047163) ^ ((229047163 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 229047163) ^ ((229047163 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 229047163) ^ ((229047163 - 1) / 1316363) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 229047163 (2 : ZMod 229047163)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (1316363, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (1316363, 1)] : List FactorBlock).map factorBlockValue).prod = 229047163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_270421513 : Nat.Prime 270421513 := by
  have hfermat : (10 : ZMod 270421513) ^ (270421513 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (10 : ZMod 270421513) ^ ((270421513 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (10 : ZMod 270421513) ^ ((270421513 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (10 : ZMod 270421513) ^ ((270421513 - 1) / 11267563) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 270421513 (10 : ZMod 270421513)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11267563, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11267563, 1)] : List FactorBlock).map factorBlockValue).prod = 270421513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_11267563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_271512061 : Nat.Prime 271512061 := by
  have hfermat : (6 : ZMod 271512061) ^ (271512061 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 271512061) ^ ((271512061 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 271512061) ^ ((271512061 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 271512061) ^ ((271512061 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 271512061) ^ ((271512061 - 1) / 4525201) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 271512061 (6 : ZMod 271512061)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (4525201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (4525201, 1)] : List FactorBlock).map factorBlockValue).prod = 271512061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_274132373 : Nat.Prime 274132373 := by
  have hfermat : (2 : ZMod 274132373) ^ (274132373 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 274132373) ^ ((274132373 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 274132373) ^ ((274132373 - 1) / 2713) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 274132373) ^ ((274132373 - 1) / 25261) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 274132373 (2 : ZMod 274132373)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2713, 1), (25261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2713, 1), (25261, 1)] : List FactorBlock).map factorBlockValue).prod = 274132373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_275131919 : Nat.Prime 275131919 := by
  have hfermat : (19 : ZMod 275131919) ^ (275131919 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (19 : ZMod 275131919) ^ ((275131919 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (19 : ZMod 275131919) ^ ((275131919 - 1) / 137565959) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 275131919 (19 : ZMod 275131919)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (137565959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (137565959, 1)] : List FactorBlock).map factorBlockValue).prod = 275131919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_137565959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_289578043 : Nat.Prime 289578043 := by
  have hfermat : (14 : ZMod 289578043) ^ (289578043 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (14 : ZMod 289578043) ^ ((289578043 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (14 : ZMod 289578043) ^ ((289578043 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (14 : ZMod 289578043) ^ ((289578043 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (14 : ZMod 289578043) ^ ((289578043 - 1) / 1237513) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 289578043 (14 : ZMod 289578043)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (13, 1), (1237513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (13, 1), (1237513, 1)] : List FactorBlock).map factorBlockValue).prod = 289578043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_318017939 : Nat.Prime 318017939 := by
  have hfermat : (2 : ZMod 318017939) ^ (318017939 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 318017939) ^ ((318017939 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 318017939) ^ ((318017939 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 318017939) ^ ((318017939 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 318017939) ^ ((318017939 - 1) / 10781) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 318017939 (2 : ZMod 318017939)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 3), (43, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 3), (43, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod = 318017939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_319660259 : Nat.Prime 319660259 := by
  have hfermat : (2 : ZMod 319660259) ^ (319660259 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 319660259) ^ ((319660259 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 319660259) ^ ((319660259 - 1) / 1493) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 319660259) ^ ((319660259 - 1) / 107053) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 319660259 (2 : ZMod 319660259)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1493, 1), (107053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1493, 1), (107053, 1)] : List FactorBlock).map factorBlockValue).prod = 319660259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_352155959 : Nat.Prime 352155959 := by
  have hfermat : (7 : ZMod 352155959) ^ (352155959 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 352155959) ^ ((352155959 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 352155959) ^ ((352155959 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 352155959) ^ ((352155959 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 352155959) ^ ((352155959 - 1) / 163) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 352155959) ^ ((352155959 - 1) / 14029) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 352155959 (7 : ZMod 352155959)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (11, 1), (163, 1), (14029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (11, 1), (163, 1), (14029, 1)] : List FactorBlock).map factorBlockValue).prod = 352155959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_368419669 : Nat.Prime 368419669 := by
  have hfermat : (2 : ZMod 368419669) ^ (368419669 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 368419669) ^ ((368419669 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 368419669) ^ ((368419669 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 368419669) ^ ((368419669 - 1) / 2543) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 368419669) ^ ((368419669 - 1) / 12073) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 368419669 (2 : ZMod 368419669)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2543, 1), (12073, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2543, 1), (12073, 1)] : List FactorBlock).map factorBlockValue).prod = 368419669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_394688417 : Nat.Prime 394688417 := by
  have hfermat : (3 : ZMod 394688417) ^ (394688417 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 394688417) ^ ((394688417 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 394688417) ^ ((394688417 - 1) / 12334013) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 394688417 (3 : ZMod 394688417)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (12334013, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (12334013, 1)] : List FactorBlock).map factorBlockValue).prod = 394688417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_12334013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_407908439 : Nat.Prime 407908439 := by
  have hfermat : (7 : ZMod 407908439) ^ (407908439 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 407908439) ^ ((407908439 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 407908439) ^ ((407908439 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 407908439) ^ ((407908439 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 407908439) ^ ((407908439 - 1) / 244843) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 407908439 (7 : ZMod 407908439)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (17, 1), (244843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (17, 1), (244843, 1)] : List FactorBlock).map factorBlockValue).prod = 407908439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_469056127 : Nat.Prime 469056127 := by
  have hfermat : (5 : ZMod 469056127) ^ (469056127 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 469056127) ^ ((469056127 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 469056127) ^ ((469056127 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 469056127) ^ ((469056127 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 469056127) ^ ((469056127 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 469056127) ^ ((469056127 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (5 : ZMod 469056127) ^ ((469056127 - 1) / 3373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 469056127 (5 : ZMod 469056127)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (11, 1), (43, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (11, 1), (43, 1), (3373, 1)] : List FactorBlock).map factorBlockValue).prod = 469056127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_478448171 : Nat.Prime 478448171 := by
  have hfermat : (6 : ZMod 478448171) ^ (478448171 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 478448171) ^ ((478448171 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 478448171) ^ ((478448171 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 478448171) ^ ((478448171 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 478448171) ^ ((478448171 - 1) / 165553) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 478448171 (6 : ZMod 478448171)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 2), (165553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 2), (165553, 1)] : List FactorBlock).map factorBlockValue).prod = 478448171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_484580539 : Nat.Prime 484580539 := by
  have hfermat : (2 : ZMod 484580539) ^ (484580539 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 484580539) ^ ((484580539 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 484580539) ^ ((484580539 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 484580539) ^ ((484580539 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 484580539) ^ ((484580539 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 484580539) ^ ((484580539 - 1) / 29167) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 484580539 (2 : ZMod 484580539)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (13, 1), (71, 1), (29167, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (13, 1), (71, 1), (29167, 1)] : List FactorBlock).map factorBlockValue).prod = 484580539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_512005567 : Nat.Prime 512005567 := by
  have hfermat : (5 : ZMod 512005567) ^ (512005567 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 512005567) ^ ((512005567 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 512005567) ^ ((512005567 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 512005567) ^ ((512005567 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 512005567) ^ ((512005567 - 1) / 577) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 512005567) ^ ((512005567 - 1) / 2083) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 512005567 (5 : ZMod 512005567)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (71, 1), (577, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (71, 1), (577, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod = 512005567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_524850437 : Nat.Prime 524850437 := by
  have hfermat : (2 : ZMod 524850437) ^ (524850437 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 524850437) ^ ((524850437 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 524850437) ^ ((524850437 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 524850437) ^ ((524850437 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 524850437) ^ ((524850437 - 1) / 163403) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 524850437 (2 : ZMod 524850437)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (73, 1), (163403, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (73, 1), (163403, 1)] : List FactorBlock).map factorBlockValue).prod = 524850437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_548968039 : Nat.Prime 548968039 := by
  have hfermat : (3 : ZMod 548968039) ^ (548968039 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 548968039) ^ ((548968039 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 548968039) ^ ((548968039 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 548968039) ^ ((548968039 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 548968039) ^ ((548968039 - 1) / 233) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 548968039) ^ ((548968039 - 1) / 10613) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 548968039 (3 : ZMod 548968039)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (37, 1), (233, 1), (10613, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (37, 1), (233, 1), (10613, 1)] : List FactorBlock).map factorBlockValue).prod = 548968039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_578104421 : Nat.Prime 578104421 := by
  have hfermat : (2 : ZMod 578104421) ^ (578104421 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 578104421) ^ ((578104421 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 578104421) ^ ((578104421 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 578104421) ^ ((578104421 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 578104421) ^ ((578104421 - 1) / 691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 578104421) ^ ((578104421 - 1) / 709) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 578104421 (2 : ZMod 578104421)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (59, 1), (691, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (59, 1), (691, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod = 578104421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_582470173 : Nat.Prime 582470173 := by
  have hfermat : (5 : ZMod 582470173) ^ (582470173 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 582470173) ^ ((582470173 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 582470173) ^ ((582470173 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 582470173) ^ ((582470173 - 1) / 16179727) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 582470173 (5 : ZMod 582470173)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (16179727, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (16179727, 1)] : List FactorBlock).map factorBlockValue).prod = 582470173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_16179727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_617887373 : Nat.Prime 617887373 := by
  have hfermat : (2 : ZMod 617887373) ^ (617887373 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 617887373) ^ ((617887373 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 617887373) ^ ((617887373 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 617887373) ^ ((617887373 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 617887373) ^ ((617887373 - 1) / 478241) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 617887373 (2 : ZMod 617887373)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (19, 1), (478241, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (19, 1), (478241, 1)] : List FactorBlock).map factorBlockValue).prod = 617887373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_630008983 : Nat.Prime 630008983 := by
  have hfermat : (3 : ZMod 630008983) ^ (630008983 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 630008983) ^ ((630008983 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 630008983) ^ ((630008983 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 630008983) ^ ((630008983 - 1) / 11666833) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 630008983 (3 : ZMod 630008983)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (11666833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (11666833, 1)] : List FactorBlock).map factorBlockValue).prod = 630008983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_11666833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_676419487 : Nat.Prime 676419487 := by
  have hfermat : (7 : ZMod 676419487) ^ (676419487 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 676419487) ^ ((676419487 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 676419487) ^ ((676419487 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 676419487) ^ ((676419487 - 1) / 112736581) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 676419487 (7 : ZMod 676419487)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (112736581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (112736581, 1)] : List FactorBlock).map factorBlockValue).prod = 676419487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_112736581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_702831179 : Nat.Prime 702831179 := by
  have hfermat : (2 : ZMod 702831179) ^ (702831179 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 702831179) ^ ((702831179 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 702831179) ^ ((702831179 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 702831179) ^ ((702831179 - 1) / 50202227) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 702831179 (2 : ZMod 702831179)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (50202227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (50202227, 1)] : List FactorBlock).map factorBlockValue).prod = 702831179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_50202227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_728383589 : Nat.Prime 728383589 := by
  have hfermat : (2 : ZMod 728383589) ^ (728383589 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 728383589) ^ ((728383589 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 728383589) ^ ((728383589 - 1) / 571) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 728383589) ^ ((728383589 - 1) / 318907) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 728383589 (2 : ZMod 728383589)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (571, 1), (318907, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (571, 1), (318907, 1)] : List FactorBlock).map factorBlockValue).prod = 728383589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_746174833 : Nat.Prime 746174833 := by
  have hfermat : (5 : ZMod 746174833) ^ (746174833 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 746174833) ^ ((746174833 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 746174833) ^ ((746174833 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 746174833) ^ ((746174833 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 746174833) ^ ((746174833 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 746174833) ^ ((746174833 - 1) / 51991) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 746174833 (5 : ZMod 746174833)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (13, 1), (23, 1), (51991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (13, 1), (23, 1), (51991, 1)] : List FactorBlock).map factorBlockValue).prod = 746174833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_771186739 : Nat.Prime 771186739 := by
  have hfermat : (2 : ZMod 771186739) ^ (771186739 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 771186739) ^ ((771186739 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 771186739) ^ ((771186739 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 771186739) ^ ((771186739 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 771186739) ^ ((771186739 - 1) / 18361589) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 771186739 (2 : ZMod 771186739)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (18361589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (18361589, 1)] : List FactorBlock).map factorBlockValue).prod = 771186739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_18361589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_853323017 : Nat.Prime 853323017 := by
  have hfermat : (3 : ZMod 853323017) ^ (853323017 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 853323017) ^ ((853323017 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 853323017) ^ ((853323017 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 853323017) ^ ((853323017 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 853323017) ^ ((853323017 - 1) / 1172147) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 853323017 (3 : ZMod 853323017)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (13, 1), (1172147, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (13, 1), (1172147, 1)] : List FactorBlock).map factorBlockValue).prod = 853323017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_915603097 : Nat.Prime 915603097 := by
  have hfermat : (5 : ZMod 915603097) ^ (915603097 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 915603097) ^ ((915603097 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 915603097) ^ ((915603097 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 915603097) ^ ((915603097 - 1) / 38150129) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 915603097 (5 : ZMod 915603097)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (38150129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (38150129, 1)] : List FactorBlock).map factorBlockValue).prod = 915603097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_38150129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_987389833 : Nat.Prime 987389833 := by
  have hfermat : (5 : ZMod 987389833) ^ (987389833 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 987389833) ^ ((987389833 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 987389833) ^ ((987389833 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 987389833) ^ ((987389833 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 987389833) ^ ((987389833 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 987389833) ^ ((987389833 - 1) / 287701) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 987389833 (5 : ZMod 987389833)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (13, 1), (287701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (13, 1), (287701, 1)] : List FactorBlock).map factorBlockValue).prod = 987389833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1054160743 : Nat.Prime 1054160743 := by
  have hfermat : (5 : ZMod 1054160743) ^ (1054160743 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 1054160743) ^ ((1054160743 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 1054160743) ^ ((1054160743 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 1054160743) ^ ((1054160743 - 1) / 175693457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1054160743 (5 : ZMod 1054160743)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (175693457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (175693457, 1)] : List FactorBlock).map factorBlockValue).prod = 1054160743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_175693457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_1080926401 : Nat.Prime 1080926401 := by
  have hfermat : (37 : ZMod 1080926401) ^ (1080926401 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (37 : ZMod 1080926401) ^ ((1080926401 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (37 : ZMod 1080926401) ^ ((1080926401 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (37 : ZMod 1080926401) ^ ((1080926401 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (37 : ZMod 1080926401) ^ ((1080926401 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (37 : ZMod 1080926401) ^ ((1080926401 - 1) / 9791) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1080926401 (37 : ZMod 1080926401)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 2), (23, 1), (9791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 2), (23, 1), (9791, 1)] : List FactorBlock).map factorBlockValue).prod = 1080926401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1245757057 : Nat.Prime 1245757057 := by
  have hfermat : (5 : ZMod 1245757057) ^ (1245757057 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 1245757057) ^ ((1245757057 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 1245757057) ^ ((1245757057 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 1245757057) ^ ((1245757057 - 1) / 3244159) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1245757057 (5 : ZMod 1245757057)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (3244159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (3244159, 1)] : List FactorBlock).map factorBlockValue).prod = 1245757057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_1405662359 : Nat.Prime 1405662359 := by
  have hfermat : (31 : ZMod 1405662359) ^ (1405662359 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (31 : ZMod 1405662359) ^ ((1405662359 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (31 : ZMod 1405662359) ^ ((1405662359 - 1) / 702831179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1405662359 (31 : ZMod 1405662359)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (702831179, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (702831179, 1)] : List FactorBlock).map factorBlockValue).prod = 1405662359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_702831179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_1457201299 : Nat.Prime 1457201299 := by
  have hfermat : (11 : ZMod 1457201299) ^ (1457201299 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (11 : ZMod 1457201299) ^ ((1457201299 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (11 : ZMod 1457201299) ^ ((1457201299 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (11 : ZMod 1457201299) ^ ((1457201299 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (11 : ZMod 1457201299) ^ ((1457201299 - 1) / 4956467) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1457201299 (11 : ZMod 1457201299)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (4956467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (4956467, 1)] : List FactorBlock).map factorBlockValue).prod = 1457201299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1495500161 : Nat.Prime 1495500161 := by
  have hfermat : (6 : ZMod 1495500161) ^ (1495500161 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 1495500161) ^ ((1495500161 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 1495500161) ^ ((1495500161 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 1495500161) ^ ((1495500161 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 1495500161) ^ ((1495500161 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 1495500161) ^ ((1495500161 - 1) / 30347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1495500161 (6 : ZMod 1495500161)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (5, 1), (7, 1), (11, 1), (30347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (5, 1), (7, 1), (11, 1), (30347, 1)] : List FactorBlock).map factorBlockValue).prod = 1495500161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1567714607 : Nat.Prime 1567714607 := by
  have hfermat : (5 : ZMod 1567714607) ^ (1567714607 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 1567714607) ^ ((1567714607 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 1567714607) ^ ((1567714607 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 1567714607) ^ ((1567714607 - 1) / 13285717) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1567714607 (5 : ZMod 1567714607)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (59, 1), (13285717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (59, 1), (13285717, 1)] : List FactorBlock).map factorBlockValue).prod = 1567714607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_13285717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_1664081357 : Nat.Prime 1664081357 := by
  have hfermat : (2 : ZMod 1664081357) ^ (1664081357 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1664081357) ^ ((1664081357 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1664081357) ^ ((1664081357 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1664081357) ^ ((1664081357 - 1) / 317) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1664081357) ^ ((1664081357 - 1) / 26783) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1664081357 (2 : ZMod 1664081357)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 2), (317, 1), (26783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 2), (317, 1), (26783, 1)] : List FactorBlock).map factorBlockValue).prod = 1664081357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1692126367 : Nat.Prime 1692126367 := by
  have hfermat : (3 : ZMod 1692126367) ^ (1692126367 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 1692126367) ^ ((1692126367 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 1692126367) ^ ((1692126367 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 1692126367) ^ ((1692126367 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 1692126367) ^ ((1692126367 - 1) / 40288723) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1692126367 (3 : ZMod 1692126367)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (40288723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (40288723, 1)] : List FactorBlock).map factorBlockValue).prod = 1692126367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_40288723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2415267221 : Nat.Prime 2415267221 := by
  have hfermat : (2 : ZMod 2415267221) ^ (2415267221 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 2415267221) ^ ((2415267221 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 2415267221) ^ ((2415267221 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 2415267221) ^ ((2415267221 - 1) / 1429) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 2415267221) ^ ((2415267221 - 1) / 84509) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2415267221 (2 : ZMod 2415267221)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (1429, 1), (84509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (1429, 1), (84509, 1)] : List FactorBlock).map factorBlockValue).prod = 2415267221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2462005703 : Nat.Prime 2462005703 := by
  have hfermat : (5 : ZMod 2462005703) ^ (2462005703 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 2462005703) ^ ((2462005703 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 2462005703) ^ ((2462005703 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 2462005703) ^ ((2462005703 - 1) / 9241) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 2462005703) ^ ((2462005703 - 1) / 10247) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2462005703 (5 : ZMod 2462005703)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (9241, 1), (10247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (9241, 1), (10247, 1)] : List FactorBlock).map factorBlockValue).prod = 2462005703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2514146683 : Nat.Prime 2514146683 := by
  have hfermat : (2 : ZMod 2514146683) ^ (2514146683 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 2514146683) ^ ((2514146683 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 2514146683) ^ ((2514146683 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 2514146683) ^ ((2514146683 - 1) / 1663) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 2514146683) ^ ((2514146683 - 1) / 251969) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2514146683 (2 : ZMod 2514146683)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1663, 1), (251969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1663, 1), (251969, 1)] : List FactorBlock).map factorBlockValue).prod = 2514146683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2547131033 : Nat.Prime 2547131033 := by
  have hfermat : (3 : ZMod 2547131033) ^ (2547131033 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 2547131033) ^ ((2547131033 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 2547131033) ^ ((2547131033 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 2547131033) ^ ((2547131033 - 1) / 691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 2547131033) ^ ((2547131033 - 1) / 24251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2547131033 (3 : ZMod 2547131033)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (19, 1), (691, 1), (24251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (19, 1), (691, 1), (24251, 1)] : List FactorBlock).map factorBlockValue).prod = 2547131033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2620303549 : Nat.Prime 2620303549 := by
  have hfermat : (2 : ZMod 2620303549) ^ (2620303549 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 2620303549) ^ ((2620303549 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 2620303549) ^ ((2620303549 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 2620303549) ^ ((2620303549 - 1) / 653) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 2620303549) ^ ((2620303549 - 1) / 334393) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2620303549 (2 : ZMod 2620303549)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (653, 1), (334393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (653, 1), (334393, 1)] : List FactorBlock).map factorBlockValue).prod = 2620303549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2731871323 : Nat.Prime 2731871323 := by
  have hfermat : (3 : ZMod 2731871323) ^ (2731871323 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 2731871323) ^ ((2731871323 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 2731871323) ^ ((2731871323 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 2731871323) ^ ((2731871323 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 2731871323) ^ ((2731871323 - 1) / 281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 2731871323) ^ ((2731871323 - 1) / 1021) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2731871323 (3 : ZMod 2731871323)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (23, 2), (281, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (23, 2), (281, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod = 2731871323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3015416923 : Nat.Prime 3015416923 := by
  have hfermat : (2 : ZMod 3015416923) ^ (3015416923 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 3015416923) ^ ((3015416923 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 3015416923) ^ ((3015416923 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 3015416923) ^ ((3015416923 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 3015416923) ^ ((3015416923 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 3015416923) ^ ((3015416923 - 1) / 181) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 3015416923) ^ ((3015416923 - 1) / 23333) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3015416923 (2 : ZMod 3015416923)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (17, 1), (181, 1), (23333, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (17, 1), (181, 1), (23333, 1)] : List FactorBlock).map factorBlockValue).prod = 3015416923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_3174366751 : Nat.Prime 3174366751 := by
  have hfermat : (6 : ZMod 3174366751) ^ (3174366751 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 3174366751) ^ ((3174366751 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 3174366751) ^ ((3174366751 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 3174366751) ^ ((3174366751 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 3174366751) ^ ((3174366751 - 1) / 1867) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 3174366751) ^ ((3174366751 - 1) / 2267) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3174366751 (6 : ZMod 3174366751)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 3), (1867, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 3), (1867, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod = 3174366751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3175358677 : Nat.Prime 3175358677 := by
  have hfermat : (2 : ZMod 3175358677) ^ (3175358677 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 3175358677) ^ ((3175358677 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 3175358677) ^ ((3175358677 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 3175358677) ^ ((3175358677 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 3175358677) ^ ((3175358677 - 1) / 2053) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 3175358677) ^ ((3175358677 - 1) / 18413) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3175358677 (2 : ZMod 3175358677)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (2053, 1), (18413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (2053, 1), (18413, 1)] : List FactorBlock).map factorBlockValue).prod = 3175358677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3228629717 : Nat.Prime 3228629717 := by
  have hfermat : (2 : ZMod 3228629717) ^ (3228629717 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 3228629717) ^ ((3228629717 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 3228629717) ^ ((3228629717 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 3228629717) ^ ((3228629717 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 3228629717) ^ ((3228629717 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 3228629717) ^ ((3228629717 - 1) / 23671) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3228629717 (2 : ZMod 3228629717)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (43, 1), (61, 1), (23671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (43, 1), (61, 1), (23671, 1)] : List FactorBlock).map factorBlockValue).prod = 3228629717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3672002891 : Nat.Prime 3672002891 := by
  have hfermat : (2 : ZMod 3672002891) ^ (3672002891 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 3672002891) ^ ((3672002891 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 3672002891) ^ ((3672002891 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 3672002891) ^ ((3672002891 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 3672002891) ^ ((3672002891 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 3672002891) ^ ((3672002891 - 1) / 1136843) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3672002891 (2 : ZMod 3672002891)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (19, 1), (1136843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (19, 1), (1136843, 1)] : List FactorBlock).map factorBlockValue).prod = 3672002891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3741210059 : Nat.Prime 3741210059 := by
  have hfermat : (2 : ZMod 3741210059) ^ (3741210059 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 3741210059) ^ ((3741210059 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 3741210059) ^ ((3741210059 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 3741210059) ^ ((3741210059 - 1) / 197) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 3741210059) ^ ((3741210059 - 1) / 202031) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3741210059 (2 : ZMod 3741210059)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (47, 1), (197, 1), (202031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (47, 1), (197, 1), (202031, 1)] : List FactorBlock).map factorBlockValue).prod = 3741210059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_3880113001 : Nat.Prime 3880113001 := by
  have hfermat : (19 : ZMod 3880113001) ^ (3880113001 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (19 : ZMod 3880113001) ^ ((3880113001 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (19 : ZMod 3880113001) ^ ((3880113001 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (19 : ZMod 3880113001) ^ ((3880113001 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (19 : ZMod 3880113001) ^ ((3880113001 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (19 : ZMod 3880113001) ^ ((3880113001 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (19 : ZMod 3880113001) ^ ((3880113001 - 1) / 433) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3880113001 (19 : ZMod 3880113001)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 3), (29, 1), (103, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 3), (29, 1), (103, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod = 3880113001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_4029825743 : Nat.Prime 4029825743 := by
  have hfermat : (5 : ZMod 4029825743) ^ (4029825743 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 4029825743) ^ ((4029825743 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 4029825743) ^ ((4029825743 - 1) / 673) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 4029825743) ^ ((4029825743 - 1) / 2993927) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4029825743 (5 : ZMod 4029825743)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (673, 1), (2993927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (673, 1), (2993927, 1)] : List FactorBlock).map factorBlockValue).prod = 4029825743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_4541022221 : Nat.Prime 4541022221 := by
  have hfermat : (2 : ZMod 4541022221) ^ (4541022221 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 4541022221) ^ ((4541022221 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 4541022221) ^ ((4541022221 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 4541022221) ^ ((4541022221 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 4541022221) ^ ((4541022221 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 4541022221) ^ ((4541022221 - 1) / 303139) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4541022221 (2 : ZMod 4541022221)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (107, 1), (303139, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (107, 1), (303139, 1)] : List FactorBlock).map factorBlockValue).prod = 4541022221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_4823128433 : Nat.Prime 4823128433 := by
  have hfermat : (3 : ZMod 4823128433) ^ (4823128433 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 4823128433) ^ ((4823128433 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 4823128433) ^ ((4823128433 - 1) / 277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 4823128433) ^ ((4823128433 - 1) / 1088251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4823128433 (3 : ZMod 4823128433)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (277, 1), (1088251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (277, 1), (1088251, 1)] : List FactorBlock).map factorBlockValue).prod = 4823128433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_5077314049 : Nat.Prime 5077314049 := by
  have hfermat : (7 : ZMod 5077314049) ^ (5077314049 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 5077314049) ^ ((5077314049 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 5077314049) ^ ((5077314049 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 5077314049) ^ ((5077314049 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 5077314049) ^ ((5077314049 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 5077314049) ^ ((5077314049 - 1) / 2179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 5077314049 (7 : ZMod 5077314049)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (3, 1), (37, 1), (41, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (3, 1), (37, 1), (41, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod = 5077314049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_5685900611 : Nat.Prime 5685900611 := by
  have hfermat : (10 : ZMod 5685900611) ^ (5685900611 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (10 : ZMod 5685900611) ^ ((5685900611 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (10 : ZMod 5685900611) ^ ((5685900611 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (10 : ZMod 5685900611) ^ ((5685900611 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (10 : ZMod 5685900611) ^ ((5685900611 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (10 : ZMod 5685900611) ^ ((5685900611 - 1) / 1901639) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 5685900611 (10 : ZMod 5685900611)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (23, 1), (1901639, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (23, 1), (1901639, 1)] : List FactorBlock).map factorBlockValue).prod = 5685900611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_6215632481 : Nat.Prime 6215632481 := by
  have hfermat : (13 : ZMod 6215632481) ^ (6215632481 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (13 : ZMod 6215632481) ^ ((6215632481 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (13 : ZMod 6215632481) ^ ((6215632481 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (13 : ZMod 6215632481) ^ ((6215632481 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (13 : ZMod 6215632481) ^ ((6215632481 - 1) / 2285159) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6215632481 (13 : ZMod 6215632481)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (17, 1), (2285159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (17, 1), (2285159, 1)] : List FactorBlock).map factorBlockValue).prod = 6215632481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_6299924627 : Nat.Prime 6299924627 := by
  have hfermat : (2 : ZMod 6299924627) ^ (6299924627 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 6299924627) ^ ((6299924627 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 6299924627) ^ ((6299924627 - 1) / 3119) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 6299924627) ^ ((6299924627 - 1) / 1009927) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6299924627 (2 : ZMod 6299924627)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3119, 1), (1009927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3119, 1), (1009927, 1)] : List FactorBlock).map factorBlockValue).prod = 6299924627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_6522112699 : Nat.Prime 6522112699 := by
  have hfermat : (3 : ZMod 6522112699) ^ (6522112699 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 6522112699) ^ ((6522112699 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 6522112699) ^ ((6522112699 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 6522112699) ^ ((6522112699 - 1) / 227) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 6522112699) ^ ((6522112699 - 1) / 349) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 6522112699) ^ ((6522112699 - 1) / 13721) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6522112699 (3 : ZMod 6522112699)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (227, 1), (349, 1), (13721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (227, 1), (349, 1), (13721, 1)] : List FactorBlock).map factorBlockValue).prod = 6522112699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_6957872087 : Nat.Prime 6957872087 := by
  have hfermat : (5 : ZMod 6957872087) ^ (6957872087 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 6957872087) ^ ((6957872087 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 6957872087) ^ ((6957872087 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 6957872087) ^ ((6957872087 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 6957872087) ^ ((6957872087 - 1) / 16645627) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6957872087 (5 : ZMod 6957872087)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (19, 1), (16645627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (19, 1), (16645627, 1)] : List FactorBlock).map factorBlockValue).prod = 6957872087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_16645627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_7193542211 : Nat.Prime 7193542211 := by
  have hfermat : (6 : ZMod 7193542211) ^ (7193542211 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 7193542211) ^ ((7193542211 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 7193542211) ^ ((7193542211 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 7193542211) ^ ((7193542211 - 1) / 673) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 7193542211) ^ ((7193542211 - 1) / 1068877) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7193542211 (6 : ZMod 7193542211)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (673, 1), (1068877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (673, 1), (1068877, 1)] : List FactorBlock).map factorBlockValue).prod = 7193542211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_7344005783 : Nat.Prime 7344005783 := by
  have hfermat : (5 : ZMod 7344005783) ^ (7344005783 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 7344005783) ^ ((7344005783 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 7344005783) ^ ((7344005783 - 1) / 3672002891) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7344005783 (5 : ZMod 7344005783)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3672002891, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3672002891, 1)] : List FactorBlock).map factorBlockValue).prod = 7344005783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_3672002891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_7539351613 : Nat.Prime 7539351613 := by
  have hfermat : (2 : ZMod 7539351613) ^ (7539351613 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 7539351613) ^ ((7539351613 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 7539351613) ^ ((7539351613 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 7539351613) ^ ((7539351613 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 7539351613) ^ ((7539351613 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 7539351613) ^ ((7539351613 - 1) / 55487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7539351613 (2 : ZMod 7539351613)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 2), (67, 1), (55487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 2), (67, 1), (55487, 1)] : List FactorBlock).map factorBlockValue).prod = 7539351613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_7628294221 : Nat.Prime 7628294221 := by
  have hfermat : (2 : ZMod 7628294221) ^ (7628294221 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 7628294221) ^ ((7628294221 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 7628294221) ^ ((7628294221 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 7628294221) ^ ((7628294221 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 7628294221) ^ ((7628294221 - 1) / 797) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 7628294221) ^ ((7628294221 - 1) / 159521) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7628294221 (2 : ZMod 7628294221)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (797, 1), (159521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (797, 1), (159521, 1)] : List FactorBlock).map factorBlockValue).prod = 7628294221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_8096359153 : Nat.Prime 8096359153 := by
  have hfermat : (5 : ZMod 8096359153) ^ (8096359153 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 8096359153) ^ ((8096359153 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 8096359153) ^ ((8096359153 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 8096359153) ^ ((8096359153 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 8096359153) ^ ((8096359153 - 1) / 24096307) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 8096359153 (5 : ZMod 8096359153)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (7, 1), (24096307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (7, 1), (24096307, 1)] : List FactorBlock).map factorBlockValue).prod = 8096359153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_24096307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_8248945261 : Nat.Prime 8248945261 := by
  have hfermat : (11 : ZMod 8248945261) ^ (8248945261 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (11 : ZMod 8248945261) ^ ((8248945261 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (11 : ZMod 8248945261) ^ ((8248945261 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (11 : ZMod 8248945261) ^ ((8248945261 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (11 : ZMod 8248945261) ^ ((8248945261 - 1) / 991) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (11 : ZMod 8248945261) ^ ((8248945261 - 1) / 138731) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 8248945261 (11 : ZMod 8248945261)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (991, 1), (138731, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (991, 1), (138731, 1)] : List FactorBlock).map factorBlockValue).prod = 8248945261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_9825249617 : Nat.Prime 9825249617 := by
  have hfermat : (3 : ZMod 9825249617) ^ (9825249617 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 9825249617) ^ ((9825249617 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 9825249617) ^ ((9825249617 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 9825249617) ^ ((9825249617 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 9825249617) ^ ((9825249617 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 9825249617) ^ ((9825249617 - 1) / 217681) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 9825249617 (3 : ZMod 9825249617)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (13, 1), (31, 1), (217681, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (13, 1), (31, 1), (217681, 1)] : List FactorBlock).map factorBlockValue).prod = 9825249617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_10927485293 : Nat.Prime 10927485293 := by
  have hfermat : (2 : ZMod 10927485293) ^ (10927485293 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 10927485293) ^ ((10927485293 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 10927485293) ^ ((10927485293 - 1) / 2731871323) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10927485293 (2 : ZMod 10927485293)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2731871323, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2731871323, 1)] : List FactorBlock).map factorBlockValue).prod = 10927485293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_2731871323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_11335084337 : Nat.Prime 11335084337 := by
  have hfermat : (3 : ZMod 11335084337) ^ (11335084337 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 11335084337) ^ ((11335084337 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 11335084337) ^ ((11335084337 - 1) / 457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 11335084337) ^ ((11335084337 - 1) / 1550203) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11335084337 (3 : ZMod 11335084337)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (457, 1), (1550203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (457, 1), (1550203, 1)] : List FactorBlock).map factorBlockValue).prod = 11335084337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_11559693121 : Nat.Prime 11559693121 := by
  have hfermat : (13 : ZMod 11559693121) ^ (11559693121 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (13 : ZMod 11559693121) ^ ((11559693121 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (13 : ZMod 11559693121) ^ ((11559693121 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (13 : ZMod 11559693121) ^ ((11559693121 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (13 : ZMod 11559693121) ^ ((11559693121 - 1) / 337) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (13 : ZMod 11559693121) ^ ((11559693121 - 1) / 35731) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11559693121 (13 : ZMod 11559693121)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 1), (337, 1), (35731, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 1), (337, 1), (35731, 1)] : List FactorBlock).map factorBlockValue).prod = 11559693121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_11624840291 : Nat.Prime 11624840291 := by
  have hfermat : (6 : ZMod 11624840291) ^ (11624840291 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 11624840291) ^ ((11624840291 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 11624840291) ^ ((11624840291 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 11624840291) ^ ((11624840291 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 11624840291) ^ ((11624840291 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 11624840291) ^ ((11624840291 - 1) / 541) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (6 : ZMod 11624840291) ^ ((11624840291 - 1) / 7487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11624840291 (6 : ZMod 11624840291)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (41, 1), (541, 1), (7487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (41, 1), (541, 1), (7487, 1)] : List FactorBlock).map factorBlockValue).prod = 11624840291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_12445339003 : Nat.Prime 12445339003 := by
  have hfermat : (3 : ZMod 12445339003) ^ (12445339003 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 12445339003) ^ ((12445339003 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 12445339003) ^ ((12445339003 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 12445339003) ^ ((12445339003 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 12445339003) ^ ((12445339003 - 1) / 20138089) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12445339003 (3 : ZMod 12445339003)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (103, 1), (20138089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (103, 1), (20138089, 1)] : List FactorBlock).map factorBlockValue).prod = 12445339003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_20138089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_12670723057 : Nat.Prime 12670723057 := by
  have hfermat : (7 : ZMod 12670723057) ^ (12670723057 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 12670723057) ^ ((12670723057 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 12670723057) ^ ((12670723057 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 12670723057) ^ ((12670723057 - 1) / 761) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 12670723057) ^ ((12670723057 - 1) / 346877) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12670723057 (7 : ZMod 12670723057)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (761, 1), (346877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (761, 1), (346877, 1)] : List FactorBlock).map factorBlockValue).prod = 12670723057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_13889164981 : Nat.Prime 13889164981 := by
  have hfermat : (2 : ZMod 13889164981) ^ (13889164981 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 13889164981) ^ ((13889164981 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 13889164981) ^ ((13889164981 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 13889164981) ^ ((13889164981 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 13889164981) ^ ((13889164981 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 13889164981) ^ ((13889164981 - 1) / 1039) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 13889164981) ^ ((13889164981 - 1) / 7187) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 13889164981 (2 : ZMod 13889164981)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (31, 1), (1039, 1), (7187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (31, 1), (1039, 1), (7187, 1)] : List FactorBlock).map factorBlockValue).prod = 13889164981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_14206672321 : Nat.Prime 14206672321 := by
  have hfermat : (33 : ZMod 14206672321) ^ (14206672321 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (33 : ZMod 14206672321) ^ ((14206672321 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (33 : ZMod 14206672321) ^ ((14206672321 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (33 : ZMod 14206672321) ^ ((14206672321 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (33 : ZMod 14206672321) ^ ((14206672321 - 1) / 2699) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (33 : ZMod 14206672321) ^ ((14206672321 - 1) / 5483) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 14206672321 (33 : ZMod 14206672321)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 1), (2699, 1), (5483, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 1), (2699, 1), (5483, 1)] : List FactorBlock).map factorBlockValue).prod = 14206672321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_14772034219 : Nat.Prime 14772034219 := by
  have hfermat : (10 : ZMod 14772034219) ^ (14772034219 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (10 : ZMod 14772034219) ^ ((14772034219 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (10 : ZMod 14772034219) ^ ((14772034219 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (10 : ZMod 14772034219) ^ ((14772034219 - 1) / 2462005703) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 14772034219 (10 : ZMod 14772034219)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (2462005703, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (2462005703, 1)] : List FactorBlock).map factorBlockValue).prod = 14772034219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_2462005703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_15958288253 : Nat.Prime 15958288253 := by
  have hfermat : (2 : ZMod 15958288253) ^ (15958288253 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 15958288253) ^ ((15958288253 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 15958288253) ^ ((15958288253 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 15958288253) ^ ((15958288253 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 15958288253) ^ ((15958288253 - 1) / 6773467) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 15958288253 (2 : ZMod 15958288253)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (31, 1), (6773467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (31, 1), (6773467, 1)] : List FactorBlock).map factorBlockValue).prod = 15958288253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_16046165917 : Nat.Prime 16046165917 := by
  have hfermat : (6 : ZMod 16046165917) ^ (16046165917 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 16046165917) ^ ((16046165917 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 16046165917) ^ ((16046165917 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 16046165917) ^ ((16046165917 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 16046165917) ^ ((16046165917 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 16046165917) ^ ((16046165917 - 1) / 555077) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 16046165917 (6 : ZMod 16046165917)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (11, 1), (73, 1), (555077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (11, 1), (73, 1), (555077, 1)] : List FactorBlock).map factorBlockValue).prod = 16046165917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_17599703299 : Nat.Prime 17599703299 := by
  have hfermat : (2 : ZMod 17599703299) ^ (17599703299 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 17599703299) ^ ((17599703299 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 17599703299) ^ ((17599703299 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 17599703299) ^ ((17599703299 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 17599703299) ^ ((17599703299 - 1) / 40181971) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 17599703299 (2 : ZMod 17599703299)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (73, 1), (40181971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (73, 1), (40181971, 1)] : List FactorBlock).map factorBlockValue).prod = 17599703299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_40181971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_17952493613 : Nat.Prime 17952493613 := by
  have hfermat : (3 : ZMod 17952493613) ^ (17952493613 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 17952493613) ^ ((17952493613 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 17952493613) ^ ((17952493613 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 17952493613) ^ ((17952493613 - 1) / 983) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 17952493613) ^ ((17952493613 - 1) / 268573) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 17952493613 (3 : ZMod 17952493613)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (983, 1), (268573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (983, 1), (268573, 1)] : List FactorBlock).map factorBlockValue).prod = 17952493613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_18229969099 : Nat.Prime 18229969099 := by
  have hfermat : (2 : ZMod 18229969099) ^ (18229969099 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 18229969099) ^ ((18229969099 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 18229969099) ^ ((18229969099 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 18229969099) ^ ((18229969099 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 18229969099) ^ ((18229969099 - 1) / 347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 18229969099) ^ ((18229969099 - 1) / 265333) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 18229969099 (2 : ZMod 18229969099)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (347, 1), (265333, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (347, 1), (265333, 1)] : List FactorBlock).map factorBlockValue).prod = 18229969099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_19286964097 : Nat.Prime 19286964097 := by
  have hfermat : (13 : ZMod 19286964097) ^ (19286964097 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (13 : ZMod 19286964097) ^ ((19286964097 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (13 : ZMod 19286964097) ^ ((19286964097 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (13 : ZMod 19286964097) ^ ((19286964097 - 1) / 50226469) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 19286964097 (13 : ZMod 19286964097)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (50226469, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (50226469, 1)] : List FactorBlock).map factorBlockValue).prod = 19286964097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_50226469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_19442460871 : Nat.Prime 19442460871 := by
  have hfermat : (6 : ZMod 19442460871) ^ (19442460871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 19442460871) ^ ((19442460871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 19442460871) ^ ((19442460871 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 19442460871) ^ ((19442460871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 19442460871) ^ ((19442460871 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 19442460871) ^ ((19442460871 - 1) / 3301) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (6 : ZMod 19442460871) ^ ((19442460871 - 1) / 9349) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 19442460871 (6 : ZMod 19442460871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (7, 1), (3301, 1), (9349, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (7, 1), (3301, 1), (9349, 1)] : List FactorBlock).map factorBlockValue).prod = 19442460871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_19815068969 : Nat.Prime 19815068969 := by
  have hfermat : (3 : ZMod 19815068969) ^ (19815068969 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 19815068969) ^ ((19815068969 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 19815068969) ^ ((19815068969 - 1) / 317) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 19815068969) ^ ((19815068969 - 1) / 7813513) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 19815068969 (3 : ZMod 19815068969)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (317, 1), (7813513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (317, 1), (7813513, 1)] : List FactorBlock).map factorBlockValue).prod = 19815068969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_21233391061 : Nat.Prime 21233391061 := by
  have hfermat : (14 : ZMod 21233391061) ^ (21233391061 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (14 : ZMod 21233391061) ^ ((21233391061 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (14 : ZMod 21233391061) ^ ((21233391061 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (14 : ZMod 21233391061) ^ ((21233391061 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (14 : ZMod 21233391061) ^ ((21233391061 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (14 : ZMod 21233391061) ^ ((21233391061 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (14 : ZMod 21233391061) ^ ((21233391061 - 1) / 953881) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 21233391061 (14 : ZMod 21233391061)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 1), (53, 1), (953881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 1), (53, 1), (953881, 1)] : List FactorBlock).map factorBlockValue).prod = 21233391061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_21404250797 : Nat.Prime 21404250797 := by
  have hfermat : (2 : ZMod 21404250797) ^ (21404250797 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 21404250797) ^ ((21404250797 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 21404250797) ^ ((21404250797 - 1) / 653) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 21404250797) ^ ((21404250797 - 1) / 8194583) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 21404250797 (2 : ZMod 21404250797)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (653, 1), (8194583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (653, 1), (8194583, 1)] : List FactorBlock).map factorBlockValue).prod = 21404250797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_21427789441 : Nat.Prime 21427789441 := by
  have hfermat : (13 : ZMod 21427789441) ^ (21427789441 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (13 : ZMod 21427789441) ^ ((21427789441 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (13 : ZMod 21427789441) ^ ((21427789441 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (13 : ZMod 21427789441) ^ ((21427789441 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (13 : ZMod 21427789441) ^ ((21427789441 - 1) / 11160307) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 21427789441 (13 : ZMod 21427789441)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (5, 1), (11160307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (5, 1), (11160307, 1)] : List FactorBlock).map factorBlockValue).prod = 21427789441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_11160307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_22174564067 : Nat.Prime 22174564067 := by
  have hfermat : (2 : ZMod 22174564067) ^ (22174564067 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 22174564067) ^ ((22174564067 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 22174564067) ^ ((22174564067 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 22174564067) ^ ((22174564067 - 1) / 270421513) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 22174564067 (2 : ZMod 22174564067)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (270421513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (270421513, 1)] : List FactorBlock).map factorBlockValue).prod = 22174564067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_270421513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_23455760227 : Nat.Prime 23455760227 := by
  have hfermat : (2 : ZMod 23455760227) ^ (23455760227 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 23455760227) ^ ((23455760227 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 23455760227) ^ ((23455760227 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 23455760227) ^ ((23455760227 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 23455760227) ^ ((23455760227 - 1) / 169969277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 23455760227 (2 : ZMod 23455760227)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (169969277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (169969277, 1)] : List FactorBlock).map factorBlockValue).prod = 23455760227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_169969277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_29088477217 : Nat.Prime 29088477217 := by
  have hfermat : (10 : ZMod 29088477217) ^ (29088477217 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (10 : ZMod 29088477217) ^ ((29088477217 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (10 : ZMod 29088477217) ^ ((29088477217 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (10 : ZMod 29088477217) ^ ((29088477217 - 1) / 313) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (10 : ZMod 29088477217) ^ ((29088477217 - 1) / 107563) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 29088477217 (10 : ZMod 29088477217)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (313, 1), (107563, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (313, 1), (107563, 1)] : List FactorBlock).map factorBlockValue).prod = 29088477217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_30019592129 : Nat.Prime 30019592129 := by
  have hfermat : (3 : ZMod 30019592129) ^ (30019592129 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 30019592129) ^ ((30019592129 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 30019592129) ^ ((30019592129 - 1) / 469056127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 30019592129 (3 : ZMod 30019592129)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (469056127, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (469056127, 1)] : List FactorBlock).map factorBlockValue).prod = 30019592129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_469056127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_30557409041 : Nat.Prime 30557409041 := by
  have hfermat : (3 : ZMod 30557409041) ^ (30557409041 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 30557409041) ^ ((30557409041 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 30557409041) ^ ((30557409041 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 30557409041) ^ ((30557409041 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 30557409041) ^ ((30557409041 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 30557409041) ^ ((30557409041 - 1) / 127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 30557409041) ^ ((30557409041 - 1) / 2803) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 30557409041 (3 : ZMod 30557409041)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (29, 1), (37, 1), (127, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (29, 1), (37, 1), (127, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod = 30557409041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_32534475629 : Nat.Prime 32534475629 := by
  have hfermat : (2 : ZMod 32534475629) ^ (32534475629 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 32534475629) ^ ((32534475629 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 32534475629) ^ ((32534475629 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 32534475629) ^ ((32534475629 - 1) / 478448171) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 32534475629 (2 : ZMod 32534475629)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (478448171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (478448171, 1)] : List FactorBlock).map factorBlockValue).prod = 32534475629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_478448171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_36396309533 : Nat.Prime 36396309533 := by
  have hfermat : (2 : ZMod 36396309533) ^ (36396309533 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 36396309533) ^ ((36396309533 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 36396309533) ^ ((36396309533 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 36396309533) ^ ((36396309533 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 36396309533) ^ ((36396309533 - 1) / 647) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 36396309533) ^ ((36396309533 - 1) / 20959) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 36396309533 (2 : ZMod 36396309533)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (61, 1), (647, 1), (20959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (61, 1), (647, 1), (20959, 1)] : List FactorBlock).map factorBlockValue).prod = 36396309533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_42375749371 : Nat.Prime 42375749371 := by
  have hfermat : (2 : ZMod 42375749371) ^ (42375749371 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 42375749371) ^ ((42375749371 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 42375749371) ^ ((42375749371 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 42375749371) ^ ((42375749371 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 42375749371) ^ ((42375749371 - 1) / 179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 42375749371) ^ ((42375749371 - 1) / 227) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 42375749371) ^ ((42375749371 - 1) / 34763) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 42375749371 (2 : ZMod 42375749371)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (179, 1), (227, 1), (34763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (179, 1), (227, 1), (34763, 1)] : List FactorBlock).map factorBlockValue).prod = 42375749371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_42584398427 : Nat.Prime 42584398427 := by
  have hfermat : (2 : ZMod 42584398427) ^ (42584398427 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 42584398427) ^ ((42584398427 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 42584398427) ^ ((42584398427 - 1) / 30211) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 42584398427) ^ ((42584398427 - 1) / 704783) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 42584398427 (2 : ZMod 42584398427)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (30211, 1), (704783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (30211, 1), (704783, 1)] : List FactorBlock).map factorBlockValue).prod = 42584398427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_44202405761 : Nat.Prime 44202405761 := by
  have hfermat : (3 : ZMod 44202405761) ^ (44202405761 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 44202405761) ^ ((44202405761 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 44202405761) ^ ((44202405761 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 44202405761) ^ ((44202405761 - 1) / 971) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 44202405761) ^ ((44202405761 - 1) / 71129) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 44202405761 (3 : ZMod 44202405761)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (5, 1), (971, 1), (71129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (5, 1), (971, 1), (71129, 1)] : List FactorBlock).map factorBlockValue).prod = 44202405761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_50629403777 : Nat.Prime 50629403777 := by
  have hfermat : (3 : ZMod 50629403777) ^ (50629403777 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 50629403777) ^ ((50629403777 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 50629403777) ^ ((50629403777 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 50629403777) ^ ((50629403777 - 1) / 56506031) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 50629403777 (3 : ZMod 50629403777)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (7, 1), (56506031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (7, 1), (56506031, 1)] : List FactorBlock).map factorBlockValue).prod = 50629403777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_56506031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_70398813197 : Nat.Prime 70398813197 := by
  have hfermat : (2 : ZMod 70398813197) ^ (70398813197 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 70398813197) ^ ((70398813197 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 70398813197) ^ ((70398813197 - 1) / 17599703299) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 70398813197 (2 : ZMod 70398813197)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17599703299, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17599703299, 1)] : List FactorBlock).map factorBlockValue).prod = 70398813197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_17599703299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_74057312561 : Nat.Prime 74057312561 := by
  have hfermat : (3 : ZMod 74057312561) ^ (74057312561 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 74057312561) ^ ((74057312561 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 74057312561) ^ ((74057312561 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 74057312561) ^ ((74057312561 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 74057312561) ^ ((74057312561 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 74057312561) ^ ((74057312561 - 1) / 12022291) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 74057312561 (3 : ZMod 74057312561)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (7, 1), (11, 1), (12022291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (7, 1), (11, 1), (12022291, 1)] : List FactorBlock).map factorBlockValue).prod = 74057312561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_12022291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_77147856389 : Nat.Prime 77147856389 := by
  have hfermat : (2 : ZMod 77147856389) ^ (77147856389 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 77147856389) ^ ((77147856389 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 77147856389) ^ ((77147856389 - 1) / 19286964097) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 77147856389 (2 : ZMod 77147856389)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19286964097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19286964097, 1)] : List FactorBlock).map factorBlockValue).prod = 77147856389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_19286964097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_84201718609 : Nat.Prime 84201718609 := by
  have hfermat : (11 : ZMod 84201718609) ^ (84201718609 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (11 : ZMod 84201718609) ^ ((84201718609 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (11 : ZMod 84201718609) ^ ((84201718609 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (11 : ZMod 84201718609) ^ ((84201718609 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (11 : ZMod 84201718609) ^ ((84201718609 - 1) / 83533451) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 84201718609 (11 : ZMod 84201718609)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (83533451, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (83533451, 1)] : List FactorBlock).map factorBlockValue).prod = 84201718609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_83533451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_87358364393 : Nat.Prime 87358364393 := by
  have hfermat : (3 : ZMod 87358364393) ^ (87358364393 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 87358364393) ^ ((87358364393 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 87358364393) ^ ((87358364393 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 87358364393) ^ ((87358364393 - 1) / 2503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 87358364393) ^ ((87358364393 - 1) / 335591) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 87358364393 (3 : ZMod 87358364393)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (2503, 1), (335591, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (2503, 1), (335591, 1)] : List FactorBlock).map factorBlockValue).prod = 87358364393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_133931058427 : Nat.Prime 133931058427 := by
  have hfermat : (5 : ZMod 133931058427) ^ (133931058427 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 133931058427) ^ ((133931058427 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 133931058427) ^ ((133931058427 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 133931058427) ^ ((133931058427 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 133931058427) ^ ((133931058427 - 1) / 676419487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 133931058427 (5 : ZMod 133931058427)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (676419487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (676419487, 1)] : List FactorBlock).map factorBlockValue).prod = 133931058427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_676419487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_170577018331 : Nat.Prime 170577018331 := by
  have hfermat : (2 : ZMod 170577018331) ^ (170577018331 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 170577018331) ^ ((170577018331 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 170577018331) ^ ((170577018331 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 170577018331) ^ ((170577018331 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 170577018331) ^ ((170577018331 - 1) / 5685900611) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 170577018331 (2 : ZMod 170577018331)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (5685900611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (5685900611, 1)] : List FactorBlock).map factorBlockValue).prod = 170577018331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_5685900611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_200084271251 : Nat.Prime 200084271251 := by
  have hfermat : (2 : ZMod 200084271251) ^ (200084271251 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 200084271251) ^ ((200084271251 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 200084271251) ^ ((200084271251 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 200084271251) ^ ((200084271251 - 1) / 367) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 200084271251) ^ ((200084271251 - 1) / 436151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 200084271251 (2 : ZMod 200084271251)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 4), (367, 1), (436151, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 4), (367, 1), (436151, 1)] : List FactorBlock).map factorBlockValue).prod = 200084271251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_201503181427 : Nat.Prime 201503181427 := by
  have hfermat : (3 : ZMod 201503181427) ^ (201503181427 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 201503181427) ^ ((201503181427 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 201503181427) ^ ((201503181427 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 201503181427) ^ ((201503181427 - 1) / 241) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 201503181427) ^ ((201503181427 - 1) / 139352131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 201503181427 (3 : ZMod 201503181427)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (241, 1), (139352131, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (241, 1), (139352131, 1)] : List FactorBlock).map factorBlockValue).prod = 201503181427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_139352131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_217272655601 : Nat.Prime 217272655601 := by
  have hfermat : (3 : ZMod 217272655601) ^ (217272655601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 217272655601) ^ ((217272655601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 217272655601) ^ ((217272655601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 217272655601) ^ ((217272655601 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 217272655601) ^ ((217272655601 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 217272655601) ^ ((217272655601 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 217272655601) ^ ((217272655601 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (3 : ZMod 217272655601) ^ ((217272655601 - 1) / 23593) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 217272655601 (3 : ZMod 217272655601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 2), (7, 1), (11, 1), (13, 1), (23, 1), (23593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 2), (7, 1), (11, 1), (13, 1), (23, 1), (23593, 1)] : List FactorBlock).map factorBlockValue).prod = 217272655601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_226607654719 : Nat.Prime 226607654719 := by
  have hfermat : (3 : ZMod 226607654719) ^ (226607654719 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 226607654719) ^ ((226607654719 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 226607654719) ^ ((226607654719 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 226607654719) ^ ((226607654719 - 1) / 193) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 226607654719) ^ ((226607654719 - 1) / 751) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 226607654719) ^ ((226607654719 - 1) / 86857) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 226607654719 (3 : ZMod 226607654719)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (193, 1), (751, 1), (86857, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (193, 1), (751, 1), (86857, 1)] : List FactorBlock).map factorBlockValue).prod = 226607654719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_228156592751 : Nat.Prime 228156592751 := by
  have hfermat : (17 : ZMod 228156592751) ^ (228156592751 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (17 : ZMod 228156592751) ^ ((228156592751 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (17 : ZMod 228156592751) ^ ((228156592751 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (17 : ZMod 228156592751) ^ ((228156592751 - 1) / 109) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (17 : ZMod 228156592751) ^ ((228156592751 - 1) / 877) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (17 : ZMod 228156592751) ^ ((228156592751 - 1) / 9547) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 228156592751 (17 : ZMod 228156592751)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 3), (109, 1), (877, 1), (9547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 3), (109, 1), (877, 1), (9547, 1)] : List FactorBlock).map factorBlockValue).prod = 228156592751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_241102710169 : Nat.Prime 241102710169 := by
  have hfermat : (7 : ZMod 241102710169) ^ (241102710169 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 241102710169) ^ ((241102710169 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 241102710169) ^ ((241102710169 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 241102710169) ^ ((241102710169 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 241102710169) ^ ((241102710169 - 1) / 271512061) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 241102710169 (7 : ZMod 241102710169)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (37, 1), (271512061, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (37, 1), (271512061, 1)] : List FactorBlock).map factorBlockValue).prod = 241102710169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_271512061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_255506390563 : Nat.Prime 255506390563 := by
  have hfermat : (2 : ZMod 255506390563) ^ (255506390563 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 255506390563) ^ ((255506390563 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 255506390563) ^ ((255506390563 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 255506390563) ^ ((255506390563 - 1) / 42584398427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 255506390563 (2 : ZMod 255506390563)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (42584398427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (42584398427, 1)] : List FactorBlock).map factorBlockValue).prod = 255506390563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_42584398427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_262829050597 : Nat.Prime 262829050597 := by
  have hfermat : (5 : ZMod 262829050597) ^ (262829050597 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 262829050597) ^ ((262829050597 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 262829050597) ^ ((262829050597 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 262829050597) ^ ((262829050597 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 262829050597) ^ ((262829050597 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 262829050597) ^ ((262829050597 - 1) / 3853) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (5 : ZMod 262829050597) ^ ((262829050597 - 1) / 15923) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 262829050597 (5 : ZMod 262829050597)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (7, 1), (17, 1), (3853, 1), (15923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (7, 1), (17, 1), (3853, 1), (15923, 1)] : List FactorBlock).map factorBlockValue).prod = 262829050597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_316611692209 : Nat.Prime 316611692209 := by
  have hfermat : (19 : ZMod 316611692209) ^ (316611692209 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (19 : ZMod 316611692209) ^ ((316611692209 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (19 : ZMod 316611692209) ^ ((316611692209 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (19 : ZMod 316611692209) ^ ((316611692209 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (19 : ZMod 316611692209) ^ ((316611692209 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (19 : ZMod 316611692209) ^ ((316611692209 - 1) / 3238133) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 316611692209 (19 : ZMod 316611692209)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (97, 1), (3238133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (97, 1), (3238133, 1)] : List FactorBlock).map factorBlockValue).prod = 316611692209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_317861289353 : Nat.Prime 317861289353 := by
  have hfermat : (3 : ZMod 317861289353) ^ (317861289353 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 317861289353) ^ ((317861289353 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 317861289353) ^ ((317861289353 - 1) / 1171) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 317861289353) ^ ((317861289353 - 1) / 33930539) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 317861289353 (3 : ZMod 317861289353)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (1171, 1), (33930539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (1171, 1), (33930539, 1)] : List FactorBlock).map factorBlockValue).prod = 317861289353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_33930539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_320464865873 : Nat.Prime 320464865873 := by
  have hfermat : (3 : ZMod 320464865873) ^ (320464865873 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 320464865873) ^ ((320464865873 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 320464865873) ^ ((320464865873 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 320464865873) ^ ((320464865873 - 1) / 1054160743) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 320464865873 (3 : ZMod 320464865873)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (19, 1), (1054160743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (19, 1), (1054160743, 1)] : List FactorBlock).map factorBlockValue).prod = 320464865873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1054160743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_411878481853 : Nat.Prime 411878481853 := by
  have hfermat : (2 : ZMod 411878481853) ^ (411878481853 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 411878481853) ^ ((411878481853 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 411878481853) ^ ((411878481853 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 411878481853) ^ ((411878481853 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 411878481853) ^ ((411878481853 - 1) / 3617) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 411878481853) ^ ((411878481853 - 1) / 97829) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 411878481853 (2 : ZMod 411878481853)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (97, 1), (3617, 1), (97829, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (97, 1), (3617, 1), (97829, 1)] : List FactorBlock).map factorBlockValue).prod = 411878481853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_453583065203 : Nat.Prime 453583065203 := by
  have hfermat : (2 : ZMod 453583065203) ^ (453583065203 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 453583065203) ^ ((453583065203 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 453583065203) ^ ((453583065203 - 1) / 140977) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 453583065203) ^ ((453583065203 - 1) / 1608713) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 453583065203 (2 : ZMod 453583065203)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (140977, 1), (1608713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (140977, 1), (1608713, 1)] : List FactorBlock).map factorBlockValue).prod = 453583065203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_466364133493 : Nat.Prime 466364133493 := by
  have hfermat : (2 : ZMod 466364133493) ^ (466364133493 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 466364133493) ^ ((466364133493 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 466364133493) ^ ((466364133493 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 466364133493) ^ ((466364133493 - 1) / 1481) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 466364133493) ^ ((466364133493 - 1) / 26241511) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 466364133493 (2 : ZMod 466364133493)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1481, 1), (26241511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1481, 1), (26241511, 1)] : List FactorBlock).map factorBlockValue).prod = 466364133493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_26241511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_474732788359 : Nat.Prime 474732788359 := by
  have hfermat : (3 : ZMod 474732788359) ^ (474732788359 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 474732788359) ^ ((474732788359 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 474732788359) ^ ((474732788359 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 474732788359) ^ ((474732788359 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 474732788359) ^ ((474732788359 - 1) / 317) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 474732788359) ^ ((474732788359 - 1) / 3159451) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 474732788359 (3 : ZMod 474732788359)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (79, 1), (317, 1), (3159451, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (79, 1), (317, 1), (3159451, 1)] : List FactorBlock).map factorBlockValue).prod = 474732788359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_503145247667 : Nat.Prime 503145247667 := by
  have hfermat : (2 : ZMod 503145247667) ^ (503145247667 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 503145247667) ^ ((503145247667 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 503145247667) ^ ((503145247667 - 1) / 787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 503145247667) ^ ((503145247667 - 1) / 319660259) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 503145247667 (2 : ZMod 503145247667)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (787, 1), (319660259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (787, 1), (319660259, 1)] : List FactorBlock).map factorBlockValue).prod = 503145247667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_319660259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_522260354879 : Nat.Prime 522260354879 := by
  have hfermat : (7 : ZMod 522260354879) ^ (522260354879 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 522260354879) ^ ((522260354879 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 522260354879) ^ ((522260354879 - 1) / 22637) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 522260354879) ^ ((522260354879 - 1) / 11535547) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 522260354879 (7 : ZMod 522260354879)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (22637, 1), (11535547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (22637, 1), (11535547, 1)] : List FactorBlock).map factorBlockValue).prod = 522260354879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_11535547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_544698394417 : Nat.Prime 544698394417 := by
  have hfermat : (5 : ZMod 544698394417) ^ (544698394417 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 544698394417) ^ ((544698394417 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 544698394417) ^ ((544698394417 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 544698394417) ^ ((544698394417 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 544698394417) ^ ((544698394417 - 1) / 38208361) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 544698394417 (5 : ZMod 544698394417)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 4), (11, 1), (38208361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 4), (11, 1), (38208361, 1)] : List FactorBlock).map factorBlockValue).prod = 544698394417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_38208361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_548336645671 : Nat.Prime 548336645671 := by
  have hfermat : (3 : ZMod 548336645671) ^ (548336645671 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 548336645671) ^ ((548336645671 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 548336645671) ^ ((548336645671 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 548336645671) ^ ((548336645671 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 548336645671) ^ ((548336645671 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 548336645671) ^ ((548336645671 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 548336645671) ^ ((548336645671 - 1) / 17130167) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 548336645671 (3 : ZMod 548336645671)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (97, 1), (17130167, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (97, 1), (17130167, 1)] : List FactorBlock).map factorBlockValue).prod = 548336645671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_17130167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_635722578707 : Nat.Prime 635722578707 := by
  have hfermat : (2 : ZMod 635722578707) ^ (635722578707 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 635722578707) ^ ((635722578707 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 635722578707) ^ ((635722578707 - 1) / 317861289353) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 635722578707 (2 : ZMod 635722578707)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (317861289353, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (317861289353, 1)] : List FactorBlock).map factorBlockValue).prod = 635722578707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_317861289353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_692628529423 : Nat.Prime 692628529423 := by
  have hfermat : (3 : ZMod 692628529423) ^ (692628529423 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 692628529423) ^ ((692628529423 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 692628529423) ^ ((692628529423 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 692628529423) ^ ((692628529423 - 1) / 283) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 692628529423) ^ ((692628529423 - 1) / 407908439) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 692628529423 (3 : ZMod 692628529423)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (283, 1), (407908439, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (283, 1), (407908439, 1)] : List FactorBlock).map factorBlockValue).prod = 692628529423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_407908439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_759308540957 : Nat.Prime 759308540957 := by
  have hfermat : (2 : ZMod 759308540957) ^ (759308540957 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 759308540957) ^ ((759308540957 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 759308540957) ^ ((759308540957 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 759308540957) ^ ((759308540957 - 1) / 51341) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 759308540957) ^ ((759308540957 - 1) / 528197) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 759308540957 (2 : ZMod 759308540957)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (51341, 1), (528197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (51341, 1), (528197, 1)] : List FactorBlock).map factorBlockValue).prod = 759308540957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_793790503003 : Nat.Prime 793790503003 := by
  have hfermat : (11 : ZMod 793790503003) ^ (793790503003 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (11 : ZMod 793790503003) ^ ((793790503003 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (11 : ZMod 793790503003) ^ ((793790503003 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (11 : ZMod 793790503003) ^ ((793790503003 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (11 : ZMod 793790503003) ^ ((793790503003 - 1) / 6299924627) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 793790503003 (11 : ZMod 793790503003)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (6299924627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (6299924627, 1)] : List FactorBlock).map factorBlockValue).prod = 793790503003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_6299924627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_819194892233 : Nat.Prime 819194892233 := by
  have hfermat : (3 : ZMod 819194892233) ^ (819194892233 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 819194892233) ^ ((819194892233 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 819194892233) ^ ((819194892233 - 1) / 51593) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 819194892233) ^ ((819194892233 - 1) / 1984753) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 819194892233 (3 : ZMod 819194892233)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (51593, 1), (1984753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (51593, 1), (1984753, 1)] : List FactorBlock).map factorBlockValue).prod = 819194892233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_848091156019 : Nat.Prime 848091156019 := by
  have hfermat : (2 : ZMod 848091156019) ^ (848091156019 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 848091156019) ^ ((848091156019 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 848091156019) ^ ((848091156019 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 848091156019) ^ ((848091156019 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 848091156019) ^ ((848091156019 - 1) / 1457201299) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 848091156019 (2 : ZMod 848091156019)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (97, 1), (1457201299, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (97, 1), (1457201299, 1)] : List FactorBlock).map factorBlockValue).prod = 848091156019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1457201299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1274032631393 : Nat.Prime 1274032631393 := by
  have hfermat : (3 : ZMod 1274032631393) ^ (1274032631393 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 1274032631393) ^ ((1274032631393 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 1274032631393) ^ ((1274032631393 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 1274032631393) ^ ((1274032631393 - 1) / 193) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 1274032631393) ^ ((1274032631393 - 1) / 8969029) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1274032631393 (3 : ZMod 1274032631393)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (23, 1), (193, 1), (8969029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (23, 1), (193, 1), (8969029, 1)] : List FactorBlock).map factorBlockValue).prod = 1274032631393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1370308810103 : Nat.Prime 1370308810103 := by
  have hfermat : (5 : ZMod 1370308810103) ^ (1370308810103 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 1370308810103) ^ ((1370308810103 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 1370308810103) ^ ((1370308810103 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 1370308810103) ^ ((1370308810103 - 1) / 173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 1370308810103) ^ ((1370308810103 - 1) / 107038651) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1370308810103 (5 : ZMod 1370308810103)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (173, 1), (107038651, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (173, 1), (107038651, 1)] : List FactorBlock).map factorBlockValue).prod = 1370308810103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_107038651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1410893565619 : Nat.Prime 1410893565619 := by
  have hfermat : (2 : ZMod 1410893565619) ^ (1410893565619 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1410893565619) ^ ((1410893565619 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1410893565619) ^ ((1410893565619 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1410893565619) ^ ((1410893565619 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1410893565619) ^ ((1410893565619 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 1410893565619) ^ ((1410893565619 - 1) / 129273737) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1410893565619 (2 : ZMod 1410893565619)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (107, 1), (129273737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (107, 1), (129273737, 1)] : List FactorBlock).map factorBlockValue).prod = 1410893565619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_129273737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1470695022571 : Nat.Prime 1470695022571 := by
  have hfermat : (3 : ZMod 1470695022571) ^ (1470695022571 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 1470695022571) ^ ((1470695022571 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 1470695022571) ^ ((1470695022571 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 1470695022571) ^ ((1470695022571 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 1470695022571) ^ ((1470695022571 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 1470695022571) ^ ((1470695022571 - 1) / 10331) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 1470695022571) ^ ((1470695022571 - 1) / 89533) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1470695022571 (3 : ZMod 1470695022571)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (53, 1), (10331, 1), (89533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (53, 1), (10331, 1), (89533, 1)] : List FactorBlock).map factorBlockValue).prod = 1470695022571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_1617677674451 : Nat.Prime 1617677674451 := by
  have hfermat : (2 : ZMod 1617677674451) ^ (1617677674451 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1617677674451) ^ ((1617677674451 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1617677674451) ^ ((1617677674451 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1617677674451) ^ ((1617677674451 - 1) / 169583) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1617677674451) ^ ((1617677674451 - 1) / 190783) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1617677674451 (2 : ZMod 1617677674451)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (169583, 1), (190783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (169583, 1), (190783, 1)] : List FactorBlock).map factorBlockValue).prod = 1617677674451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1642057812533 : Nat.Prime 1642057812533 := by
  have hfermat : (2 : ZMod 1642057812533) ^ (1642057812533 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1642057812533) ^ ((1642057812533 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1642057812533) ^ ((1642057812533 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1642057812533) ^ ((1642057812533 - 1) / 6957872087) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1642057812533 (2 : ZMod 1642057812533)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (59, 1), (6957872087, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (59, 1), (6957872087, 1)] : List FactorBlock).map factorBlockValue).prod = 1642057812533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_6957872087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_1661047798483 : Nat.Prime 1661047798483 := by
  have hfermat : (2 : ZMod 1661047798483) ^ (1661047798483 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1661047798483) ^ ((1661047798483 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1661047798483) ^ ((1661047798483 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1661047798483) ^ ((1661047798483 - 1) / 1259) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1661047798483) ^ ((1661047798483 - 1) / 73296611) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1661047798483 (2 : ZMod 1661047798483)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1259, 1), (73296611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1259, 1), (73296611, 1)] : List FactorBlock).map factorBlockValue).prod = 1661047798483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_73296611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1841187124877 : Nat.Prime 1841187124877 := by
  have hfermat : (2 : ZMod 1841187124877) ^ (1841187124877 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1841187124877) ^ ((1841187124877 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1841187124877) ^ ((1841187124877 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1841187124877) ^ ((1841187124877 - 1) / 283) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1841187124877) ^ ((1841187124877 - 1) / 147862763) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1841187124877 (2 : ZMod 1841187124877)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (283, 1), (147862763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (283, 1), (147862763, 1)] : List FactorBlock).map factorBlockValue).prod = 1841187124877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_147862763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1850847830203 : Nat.Prime 1850847830203 := by
  have hfermat : (2 : ZMod 1850847830203) ^ (1850847830203 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1850847830203) ^ ((1850847830203 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1850847830203) ^ ((1850847830203 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1850847830203) ^ ((1850847830203 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1850847830203) ^ ((1850847830203 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 1850847830203) ^ ((1850847830203 - 1) / 1324511) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1850847830203 (2 : ZMod 1850847830203)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 4), (97, 1), (1324511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 4), (97, 1), (1324511, 1)] : List FactorBlock).map factorBlockValue).prod = 1850847830203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1861662541889 : Nat.Prime 1861662541889 := by
  have hfermat : (3 : ZMod 1861662541889) ^ (1861662541889 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 1861662541889) ^ ((1861662541889 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 1861662541889) ^ ((1861662541889 - 1) / 29088477217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1861662541889 (3 : ZMod 1861662541889)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (29088477217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (29088477217, 1)] : List FactorBlock).map factorBlockValue).prod = 1861662541889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_29088477217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_1987009439351 : Nat.Prime 1987009439351 := by
  have hfermat : (19 : ZMod 1987009439351) ^ (1987009439351 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (19 : ZMod 1987009439351) ^ ((1987009439351 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (19 : ZMod 1987009439351) ^ ((1987009439351 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (19 : ZMod 1987009439351) ^ ((1987009439351 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (19 : ZMod 1987009439351) ^ ((1987009439351 - 1) / 8233) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (19 : ZMod 1987009439351) ^ ((1987009439351 - 1) / 371303) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1987009439351 (19 : ZMod 1987009439351)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (13, 1), (8233, 1), (371303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (13, 1), (8233, 1), (371303, 1)] : List FactorBlock).map factorBlockValue).prod = 1987009439351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_2366938408301 : Nat.Prime 2366938408301 := by
  have hfermat : (2 : ZMod 2366938408301) ^ (2366938408301 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 2366938408301) ^ ((2366938408301 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 2366938408301) ^ ((2366938408301 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 2366938408301) ^ ((2366938408301 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 2366938408301) ^ ((2366938408301 - 1) / 1245757057) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2366938408301 (2 : ZMod 2366938408301)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (19, 1), (1245757057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (19, 1), (1245757057, 1)] : List FactorBlock).map factorBlockValue).prod = 2366938408301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1245757057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_3268190366503 : Nat.Prime 3268190366503 := by
  have hfermat : (6 : ZMod 3268190366503) ^ (3268190366503 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 3268190366503) ^ ((3268190366503 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 3268190366503) ^ ((3268190366503 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 3268190366503) ^ ((3268190366503 - 1) / 544698394417) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3268190366503 (6 : ZMod 3268190366503)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (544698394417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (544698394417, 1)] : List FactorBlock).map factorBlockValue).prod = 3268190366503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_544698394417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_3383075540359 : Nat.Prime 3383075540359 := by
  have hfermat : (3 : ZMod 3383075540359) ^ (3383075540359 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 3383075540359) ^ ((3383075540359 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 3383075540359) ^ ((3383075540359 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 3383075540359) ^ ((3383075540359 - 1) / 991) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 3383075540359) ^ ((3383075540359 - 1) / 4349) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 3383075540359) ^ ((3383075540359 - 1) / 43609) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3383075540359 (3 : ZMod 3383075540359)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (991, 1), (4349, 1), (43609, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (991, 1), (4349, 1), (43609, 1)] : List FactorBlock).map factorBlockValue).prod = 3383075540359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3384882720949 : Nat.Prime 3384882720949 := by
  have hfermat : (10 : ZMod 3384882720949) ^ (3384882720949 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (10 : ZMod 3384882720949) ^ ((3384882720949 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (10 : ZMod 3384882720949) ^ ((3384882720949 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (10 : ZMod 3384882720949) ^ ((3384882720949 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (10 : ZMod 3384882720949) ^ ((3384882720949 - 1) / 181) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (10 : ZMod 3384882720949) ^ ((3384882720949 - 1) / 2143) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (10 : ZMod 3384882720949) ^ ((3384882720949 - 1) / 13721) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3384882720949 (10 : ZMod 3384882720949)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (53, 1), (181, 1), (2143, 1), (13721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (53, 1), (181, 1), (2143, 1), (13721, 1)] : List FactorBlock).map factorBlockValue).prod = 3384882720949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_3710260517861 : Nat.Prime 3710260517861 := by
  have hfermat : (2 : ZMod 3710260517861) ^ (3710260517861 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 3710260517861) ^ ((3710260517861 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 3710260517861) ^ ((3710260517861 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 3710260517861) ^ ((3710260517861 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 3710260517861) ^ ((3710260517861 - 1) / 1993) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 3710260517861) ^ ((3710260517861 - 1) / 7160177) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3710260517861 (2 : ZMod 3710260517861)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (1993, 1), (7160177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (1993, 1), (7160177, 1)] : List FactorBlock).map factorBlockValue).prod = 3710260517861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3949677043943 : Nat.Prime 3949677043943 := by
  have hfermat : (5 : ZMod 3949677043943) ^ (3949677043943 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 3949677043943) ^ ((3949677043943 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 3949677043943) ^ ((3949677043943 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 3949677043943) ^ ((3949677043943 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 3949677043943) ^ ((3949677043943 - 1) / 13001) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 3949677043943) ^ ((3949677043943 - 1) / 65957) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3949677043943 (5 : ZMod 3949677043943)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (47, 1), (13001, 1), (65957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (47, 1), (13001, 1), (65957, 1)] : List FactorBlock).map factorBlockValue).prod = 3949677043943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_4088102249009 : Nat.Prime 4088102249009 := by
  have hfermat : (3 : ZMod 4088102249009) ^ (4088102249009 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 4088102249009) ^ ((4088102249009 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 4088102249009) ^ ((4088102249009 - 1) / 255506390563) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4088102249009 (3 : ZMod 4088102249009)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (255506390563, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (255506390563, 1)] : List FactorBlock).map factorBlockValue).prod = 4088102249009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_255506390563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_5334602577361 : Nat.Prime 5334602577361 := by
  have hfermat : (22 : ZMod 5334602577361) ^ (5334602577361 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (22 : ZMod 5334602577361) ^ ((5334602577361 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (22 : ZMod 5334602577361) ^ ((5334602577361 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (22 : ZMod 5334602577361) ^ ((5334602577361 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (22 : ZMod 5334602577361) ^ ((5334602577361 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (22 : ZMod 5334602577361) ^ ((5334602577361 - 1) / 3175358677) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 5334602577361 (22 : ZMod 5334602577361)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (7, 1), (3175358677, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (7, 1), (3175358677, 1)] : List FactorBlock).map factorBlockValue).prod = 5334602577361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_3175358677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_6761255075213 : Nat.Prime 6761255075213 := by
  have hfermat : (2 : ZMod 6761255075213) ^ (6761255075213 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 6761255075213) ^ ((6761255075213 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 6761255075213) ^ ((6761255075213 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 6761255075213) ^ ((6761255075213 - 1) / 63389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 6761255075213) ^ ((6761255075213 - 1) / 2424157) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6761255075213 (2 : ZMod 6761255075213)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (63389, 1), (2424157, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (63389, 1), (2424157, 1)] : List FactorBlock).map factorBlockValue).prod = 6761255075213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_6811937979991 : Nat.Prime 6811937979991 := by
  have hfermat : (6 : ZMod 6811937979991) ^ (6811937979991 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 6811937979991) ^ ((6811937979991 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 6811937979991) ^ ((6811937979991 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 6811937979991) ^ ((6811937979991 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 6811937979991) ^ ((6811937979991 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 6811937979991) ^ ((6811937979991 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (6 : ZMod 6811937979991) ^ ((6811937979991 - 1) / 1013) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (6 : ZMod 6811937979991) ^ ((6811937979991 - 1) / 1567487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6811937979991 (6 : ZMod 6811937979991)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (1013, 1), (1567487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (1013, 1), (1567487, 1)] : List FactorBlock).map factorBlockValue).prod = 6811937979991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_7123124792713 : Nat.Prime 7123124792713 := by
  have hfermat : (7 : ZMod 7123124792713) ^ (7123124792713 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 7123124792713) ^ ((7123124792713 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 7123124792713) ^ ((7123124792713 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 7123124792713) ^ ((7123124792713 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 7123124792713) ^ ((7123124792713 - 1) / 1459) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 7123124792713) ^ ((7123124792713 - 1) / 8844559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7123124792713 (7 : ZMod 7123124792713)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (23, 1), (1459, 1), (8844559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (23, 1), (1459, 1), (8844559, 1)] : List FactorBlock).map factorBlockValue).prod = 7123124792713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_7265496855919 : Nat.Prime 7265496855919 := by
  have hfermat : (6 : ZMod 7265496855919) ^ (7265496855919 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 7265496855919) ^ ((7265496855919 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 7265496855919) ^ ((7265496855919 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 7265496855919) ^ ((7265496855919 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 7265496855919) ^ ((7265496855919 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 7265496855919) ^ ((7265496855919 - 1) / 151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (6 : ZMod 7265496855919) ^ ((7265496855919 - 1) / 359) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (6 : ZMod 7265496855919) ^ ((7265496855919 - 1) / 110039) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7265496855919 (6 : ZMod 7265496855919)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (29, 1), (151, 1), (359, 1), (110039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (29, 1), (151, 1), (359, 1), (110039, 1)] : List FactorBlock).map factorBlockValue).prod = 7265496855919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_7937905030031 : Nat.Prime 7937905030031 := by
  have hfermat : (7 : ZMod 7937905030031) ^ (7937905030031 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 7937905030031) ^ ((7937905030031 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 7937905030031) ^ ((7937905030031 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 7937905030031) ^ ((7937905030031 - 1) / 793790503003) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7937905030031 (7 : ZMod 7937905030031)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (793790503003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (793790503003, 1)] : List FactorBlock).map factorBlockValue).prod = 7937905030031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_793790503003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_8951127024071 : Nat.Prime 8951127024071 := by
  have hfermat : (7 : ZMod 8951127024071) ^ (8951127024071 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 8951127024071) ^ ((8951127024071 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 8951127024071) ^ ((8951127024071 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 8951127024071) ^ ((8951127024071 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 8951127024071) ^ ((8951127024071 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 8951127024071) ^ ((8951127024071 - 1) / 11624840291) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 8951127024071 (7 : ZMod 8951127024071)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (11, 1), (11624840291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (11, 1), (11624840291, 1)] : List FactorBlock).map factorBlockValue).prod = 8951127024071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_11624840291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_9674589779851 : Nat.Prime 9674589779851 := by
  have hfermat : (3 : ZMod 9674589779851) ^ (9674589779851 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 9674589779851) ^ ((9674589779851 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 9674589779851) ^ ((9674589779851 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 9674589779851) ^ ((9674589779851 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 9674589779851) ^ ((9674589779851 - 1) / 28409) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 9674589779851) ^ ((9674589779851 - 1) / 2270311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 9674589779851 (3 : ZMod 9674589779851)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (28409, 1), (2270311, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (28409, 1), (2270311, 1)] : List FactorBlock).map factorBlockValue).prod = 9674589779851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_10903801029829 : Nat.Prime 10903801029829 := by
  have hfermat : (2 : ZMod 10903801029829) ^ (10903801029829 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 10903801029829) ^ ((10903801029829 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 10903801029829) ^ ((10903801029829 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 10903801029829) ^ ((10903801029829 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 10903801029829) ^ ((10903801029829 - 1) / 8923) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 10903801029829) ^ ((10903801029829 - 1) / 14547479) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10903801029829 (2 : ZMod 10903801029829)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (8923, 1), (14547479, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (8923, 1), (14547479, 1)] : List FactorBlock).map factorBlockValue).prod = 10903801029829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_14547479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_14629164082913 : Nat.Prime 14629164082913 := by
  have hfermat : (3 : ZMod 14629164082913) ^ (14629164082913 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 14629164082913) ^ ((14629164082913 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 14629164082913) ^ ((14629164082913 - 1) / 10301) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 14629164082913) ^ ((14629164082913 - 1) / 44380291) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 14629164082913 (3 : ZMod 14629164082913)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (10301, 1), (44380291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (10301, 1), (44380291, 1)] : List FactorBlock).map factorBlockValue).prod = 14629164082913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_44380291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_15931683165883 : Nat.Prime 15931683165883 := by
  have hfermat : (2 : ZMod 15931683165883) ^ (15931683165883 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 15931683165883) ^ ((15931683165883 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 15931683165883) ^ ((15931683165883 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 15931683165883) ^ ((15931683165883 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 15931683165883) ^ ((15931683165883 - 1) / 467) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 15931683165883) ^ ((15931683165883 - 1) / 22277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 15931683165883) ^ ((15931683165883 - 1) / 23203) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 15931683165883 (2 : ZMod 15931683165883)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (467, 1), (22277, 1), (23203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (467, 1), (22277, 1), (23203, 1)] : List FactorBlock).map factorBlockValue).prod = 15931683165883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_16657651522049 : Nat.Prime 16657651522049 := by
  have hfermat : (3 : ZMod 16657651522049) ^ (16657651522049 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 16657651522049) ^ ((16657651522049 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 16657651522049) ^ ((16657651522049 - 1) / 32534475629) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 16657651522049 (3 : ZMod 16657651522049)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (32534475629, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (32534475629, 1)] : List FactorBlock).map factorBlockValue).prod = 16657651522049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_32534475629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_17554557034513 : Nat.Prime 17554557034513 := by
  have hfermat : (17 : ZMod 17554557034513) ^ (17554557034513 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (17 : ZMod 17554557034513) ^ ((17554557034513 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (17 : ZMod 17554557034513) ^ ((17554557034513 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (17 : ZMod 17554557034513) ^ ((17554557034513 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (17 : ZMod 17554557034513) ^ ((17554557034513 - 1) / 109) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (17 : ZMod 17554557034513) ^ ((17554557034513 - 1) / 6540407) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 17554557034513 (17 : ZMod 17554557034513)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 4), (19, 1), (109, 1), (6540407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 4), (19, 1), (109, 1), (6540407, 1)] : List FactorBlock).map factorBlockValue).prod = 17554557034513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_32437102901719 : Nat.Prime 32437102901719 := by
  have hfermat : (6 : ZMod 32437102901719) ^ (32437102901719 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 32437102901719) ^ ((32437102901719 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 32437102901719) ^ ((32437102901719 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 32437102901719) ^ ((32437102901719 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 32437102901719) ^ ((32437102901719 - 1) / 74057312561) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 32437102901719 (6 : ZMod 32437102901719)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (73, 1), (74057312561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (73, 1), (74057312561, 1)] : List FactorBlock).map factorBlockValue).prod = 32437102901719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_74057312561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_32913275436683 : Nat.Prime 32913275436683 := by
  have hfermat : (2 : ZMod 32913275436683) ^ (32913275436683 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 32913275436683) ^ ((32913275436683 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 32913275436683) ^ ((32913275436683 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 32913275436683) ^ ((32913275436683 - 1) / 4253) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 32913275436683) ^ ((32913275436683 - 1) / 25969253) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 32913275436683 (2 : ZMod 32913275436683)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (149, 1), (4253, 1), (25969253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (149, 1), (4253, 1), (25969253, 1)] : List FactorBlock).map factorBlockValue).prod = 32913275436683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_25969253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_36721678125373 : Nat.Prime 36721678125373 := by
  have hfermat : (2 : ZMod 36721678125373) ^ (36721678125373 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 36721678125373) ^ ((36721678125373 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 36721678125373) ^ ((36721678125373 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 36721678125373) ^ ((36721678125373 - 1) / 317) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 36721678125373) ^ ((36721678125373 - 1) / 30259) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 36721678125373) ^ ((36721678125373 - 1) / 319027) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 36721678125373 (2 : ZMod 36721678125373)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (317, 1), (30259, 1), (319027, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (317, 1), (30259, 1), (319027, 1)] : List FactorBlock).map factorBlockValue).prod = 36721678125373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_36886027359263 : Nat.Prime 36886027359263 := by
  have hfermat : (5 : ZMod 36886027359263) ^ (36886027359263 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 36886027359263) ^ ((36886027359263 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 36886027359263) ^ ((36886027359263 - 1) / 11083) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 36886027359263) ^ ((36886027359263 - 1) / 1664081357) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 36886027359263 (5 : ZMod 36886027359263)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11083, 1), (1664081357, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11083, 1), (1664081357, 1)] : List FactorBlock).map factorBlockValue).prod = 36886027359263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1664081357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_45200079401833 : Nat.Prime 45200079401833 := by
  have hfermat : (7 : ZMod 45200079401833) ^ (45200079401833 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 45200079401833) ^ ((45200079401833 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 45200079401833) ^ ((45200079401833 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 45200079401833) ^ ((45200079401833 - 1) / 101) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 45200079401833) ^ ((45200079401833 - 1) / 6215632481) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 45200079401833 (7 : ZMod 45200079401833)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (101, 1), (6215632481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (101, 1), (6215632481, 1)] : List FactorBlock).map factorBlockValue).prod = 45200079401833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_6215632481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_45864087586061 : Nat.Prime 45864087586061 := by
  have hfermat : (3 : ZMod 45864087586061) ^ (45864087586061 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 45864087586061) ^ ((45864087586061 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 45864087586061) ^ ((45864087586061 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 45864087586061) ^ ((45864087586061 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 45864087586061) ^ ((45864087586061 - 1) / 199) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 45864087586061) ^ ((45864087586061 - 1) / 107697571) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 45864087586061 (3 : ZMod 45864087586061)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (107, 1), (199, 1), (107697571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (107, 1), (199, 1), (107697571, 1)] : List FactorBlock).map factorBlockValue).prod = 45864087586061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_107697571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_52768837020239 : Nat.Prime 52768837020239 := by
  have hfermat : (7 : ZMod 52768837020239) ^ (52768837020239 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 52768837020239) ^ ((52768837020239 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 52768837020239) ^ ((52768837020239 - 1) / 197) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 52768837020239) ^ ((52768837020239 - 1) / 133931058427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 52768837020239 (7 : ZMod 52768837020239)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (197, 1), (133931058427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (197, 1), (133931058427, 1)] : List FactorBlock).map factorBlockValue).prod = 52768837020239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_133931058427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_52984461259069 : Nat.Prime 52984461259069 := by
  have hfermat : (2 : ZMod 52984461259069) ^ (52984461259069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 52984461259069) ^ ((52984461259069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 52984461259069) ^ ((52984461259069 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 52984461259069) ^ ((52984461259069 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 52984461259069) ^ ((52984461259069 - 1) / 62633) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 52984461259069) ^ ((52984461259069 - 1) / 1719413) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 52984461259069 (2 : ZMod 52984461259069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (41, 1), (62633, 1), (1719413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (41, 1), (62633, 1), (1719413, 1)] : List FactorBlock).map factorBlockValue).prod = 52984461259069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_65646822185533 : Nat.Prime 65646822185533 := by
  have hfermat : (2 : ZMod 65646822185533) ^ (65646822185533 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 65646822185533) ^ ((65646822185533 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 65646822185533) ^ ((65646822185533 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 65646822185533) ^ ((65646822185533 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 65646822185533) ^ ((65646822185533 - 1) / 241) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 65646822185533) ^ ((65646822185533 - 1) / 1080926401) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 65646822185533 (2 : ZMod 65646822185533)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (7, 1), (241, 1), (1080926401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (7, 1), (241, 1), (1080926401, 1)] : List FactorBlock).map factorBlockValue).prod = 65646822185533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1080926401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_78479782841237 : Nat.Prime 78479782841237 := by
  have hfermat : (2 : ZMod 78479782841237) ^ (78479782841237 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 78479782841237) ^ ((78479782841237 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 78479782841237) ^ ((78479782841237 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 78479782841237) ^ ((78479782841237 - 1) / 137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 78479782841237) ^ ((78479782841237 - 1) / 1873) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 78479782841237) ^ ((78479782841237 - 1) / 10922987) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 78479782841237 (2 : ZMod 78479782841237)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (137, 1), (1873, 1), (10922987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (137, 1), (1873, 1), (10922987, 1)] : List FactorBlock).map factorBlockValue).prod = 78479782841237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_10922987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_87742269655769 : Nat.Prime 87742269655769 := by
  have hfermat : (3 : ZMod 87742269655769) ^ (87742269655769 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 87742269655769) ^ ((87742269655769 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 87742269655769) ^ ((87742269655769 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 87742269655769) ^ ((87742269655769 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 87742269655769) ^ ((87742269655769 - 1) / 25933) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 87742269655769) ^ ((87742269655769 - 1) / 4647557) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 87742269655769 (3 : ZMod 87742269655769)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (13, 1), (25933, 1), (4647557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (13, 1), (25933, 1), (4647557, 1)] : List FactorBlock).map factorBlockValue).prod = 87742269655769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_104187177352007 : Nat.Prime 104187177352007 := by
  have hfermat : (5 : ZMod 104187177352007) ^ (104187177352007 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 104187177352007) ^ ((104187177352007 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 104187177352007) ^ ((104187177352007 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 104187177352007) ^ ((104187177352007 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 104187177352007) ^ ((104187177352007 - 1) / 101) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 104187177352007) ^ ((104187177352007 - 1) / 1567714607) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 104187177352007 (5 : ZMod 104187177352007)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (47, 1), (101, 1), (1567714607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (47, 1), (101, 1), (1567714607, 1)] : List FactorBlock).map factorBlockValue).prod = 104187177352007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1567714607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_117563593122667 : Nat.Prime 117563593122667 := by
  have hfermat : (2 : ZMod 117563593122667) ^ (117563593122667 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 117563593122667) ^ ((117563593122667 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 117563593122667) ^ ((117563593122667 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 117563593122667) ^ ((117563593122667 - 1) / 263) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 117563593122667) ^ ((117563593122667 - 1) / 503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 117563593122667) ^ ((117563593122667 - 1) / 6007) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 117563593122667) ^ ((117563593122667 - 1) / 8219) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 117563593122667 (2 : ZMod 117563593122667)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (263, 1), (503, 1), (6007, 1), (8219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (263, 1), (503, 1), (6007, 1), (8219, 1)] : List FactorBlock).map factorBlockValue).prod = 117563593122667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_119091996133069 : Nat.Prime 119091996133069 := by
  have hfermat : (14 : ZMod 119091996133069) ^ (119091996133069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (14 : ZMod 119091996133069) ^ ((119091996133069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (14 : ZMod 119091996133069) ^ ((119091996133069 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (14 : ZMod 119091996133069) ^ ((119091996133069 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (14 : ZMod 119091996133069) ^ ((119091996133069 - 1) / 587) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (14 : ZMod 119091996133069) ^ ((119091996133069 - 1) / 2415267221) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 119091996133069 (14 : ZMod 119091996133069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (587, 1), (2415267221, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (587, 1), (2415267221, 1)] : List FactorBlock).map factorBlockValue).prod = 119091996133069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_2415267221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_125342485170961 : Nat.Prime 125342485170961 := by
  have hfermat : (13 : ZMod 125342485170961) ^ (125342485170961 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (13 : ZMod 125342485170961) ^ ((125342485170961 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (13 : ZMod 125342485170961) ^ ((125342485170961 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (13 : ZMod 125342485170961) ^ ((125342485170961 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (13 : ZMod 125342485170961) ^ ((125342485170961 - 1) / 522260354879) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 125342485170961 (13 : ZMod 125342485170961)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (522260354879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (522260354879, 1)] : List FactorBlock).map factorBlockValue).prod = 125342485170961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_522260354879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_137823541684513 : Nat.Prime 137823541684513 := by
  have hfermat : (5 : ZMod 137823541684513) ^ (137823541684513 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 137823541684513) ^ ((137823541684513 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 137823541684513) ^ ((137823541684513 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 137823541684513) ^ ((137823541684513 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 137823541684513) ^ ((137823541684513 - 1) / 21427789441) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 137823541684513 (5 : ZMod 137823541684513)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (67, 1), (21427789441, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (67, 1), (21427789441, 1)] : List FactorBlock).map factorBlockValue).prod = 137823541684513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_21427789441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_150063148293689 : Nat.Prime 150063148293689 := by
  have hfermat : (3 : ZMod 150063148293689) ^ (150063148293689 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 150063148293689) ^ ((150063148293689 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 150063148293689) ^ ((150063148293689 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 150063148293689) ^ ((150063148293689 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 150063148293689) ^ ((150063148293689 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 150063148293689) ^ ((150063148293689 - 1) / 283) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 150063148293689) ^ ((150063148293689 - 1) / 2889503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 150063148293689 (3 : ZMod 150063148293689)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (29, 1), (113, 1), (283, 1), (2889503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (29, 1), (113, 1), (283, 1), (2889503, 1)] : List FactorBlock).map factorBlockValue).prod = 150063148293689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_155291585045269 : Nat.Prime 155291585045269 := by
  have hfermat : (10 : ZMod 155291585045269) ^ (155291585045269 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (10 : ZMod 155291585045269) ^ ((155291585045269 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (10 : ZMod 155291585045269) ^ ((155291585045269 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (10 : ZMod 155291585045269) ^ ((155291585045269 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (10 : ZMod 155291585045269) ^ ((155291585045269 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (10 : ZMod 155291585045269) ^ ((155291585045269 - 1) / 46957) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (10 : ZMod 155291585045269) ^ ((155291585045269 - 1) / 296017) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 155291585045269 (10 : ZMod 155291585045269)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (19, 1), (46957, 1), (296017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (19, 1), (46957, 1), (296017, 1)] : List FactorBlock).map factorBlockValue).prod = 155291585045269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_180832908465763 : Nat.Prime 180832908465763 := by
  have hfermat : (3 : ZMod 180832908465763) ^ (180832908465763 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 180832908465763) ^ ((180832908465763 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 180832908465763) ^ ((180832908465763 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 180832908465763) ^ ((180832908465763 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 180832908465763) ^ ((180832908465763 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 180832908465763) ^ ((180832908465763 - 1) / 226607654719) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 180832908465763 (3 : ZMod 180832908465763)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (19, 1), (226607654719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (19, 1), (226607654719, 1)] : List FactorBlock).map factorBlockValue).prod = 180832908465763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_226607654719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_183023526559339 : Nat.Prime 183023526559339 := by
  have hfermat : (3 : ZMod 183023526559339) ^ (183023526559339 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 183023526559339) ^ ((183023526559339 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 183023526559339) ^ ((183023526559339 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 183023526559339) ^ ((183023526559339 - 1) / 1559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 183023526559339) ^ ((183023526559339 - 1) / 6522112699) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 183023526559339 (3 : ZMod 183023526559339)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1559, 1), (6522112699, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1559, 1), (6522112699, 1)] : List FactorBlock).map factorBlockValue).prod = 183023526559339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_6522112699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_210654684414157 : Nat.Prime 210654684414157 := by
  have hfermat : (5 : ZMod 210654684414157) ^ (210654684414157 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 210654684414157) ^ ((210654684414157 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 210654684414157) ^ ((210654684414157 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 210654684414157) ^ ((210654684414157 - 1) / 17554557034513) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 210654684414157 (5 : ZMod 210654684414157)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17554557034513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17554557034513, 1)] : List FactorBlock).map factorBlockValue).prod = 210654684414157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_17554557034513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_213282560372923 : Nat.Prime 213282560372923 := by
  have hfermat : (2 : ZMod 213282560372923) ^ (213282560372923 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 213282560372923) ^ ((213282560372923 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 213282560372923) ^ ((213282560372923 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 213282560372923) ^ ((213282560372923 - 1) / 3949677043943) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 213282560372923 (2 : ZMod 213282560372923)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (3949677043943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (3949677043943, 1)] : List FactorBlock).map factorBlockValue).prod = 213282560372923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_3949677043943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_215643625631789 : Nat.Prime 215643625631789 := by
  have hfermat : (2 : ZMod 215643625631789) ^ (215643625631789 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 215643625631789) ^ ((215643625631789 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 215643625631789) ^ ((215643625631789 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 215643625631789) ^ ((215643625631789 - 1) / 759308540957) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 215643625631789 (2 : ZMod 215643625631789)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (71, 1), (759308540957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (71, 1), (759308540957, 1)] : List FactorBlock).map factorBlockValue).prod = 215643625631789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_759308540957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_259536097677977 : Nat.Prime 259536097677977 := by
  have hfermat : (3 : ZMod 259536097677977) ^ (259536097677977 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 259536097677977) ^ ((259536097677977 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 259536097677977) ^ ((259536097677977 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 259536097677977) ^ ((259536097677977 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 259536097677977) ^ ((259536097677977 - 1) / 201503181427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 259536097677977 (3 : ZMod 259536097677977)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (23, 1), (201503181427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (23, 1), (201503181427, 1)] : List FactorBlock).map factorBlockValue).prod = 259536097677977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_201503181427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_261085043611289 : Nat.Prime 261085043611289 := by
  have hfermat : (3 : ZMod 261085043611289) ^ (261085043611289 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 261085043611289) ^ ((261085043611289 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 261085043611289) ^ ((261085043611289 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 261085043611289) ^ ((261085043611289 - 1) / 647) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 261085043611289) ^ ((261085043611289 - 1) / 3880113001) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 261085043611289 (3 : ZMod 261085043611289)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (647, 1), (3880113001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (647, 1), (3880113001, 1)] : List FactorBlock).map factorBlockValue).prod = 261085043611289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_3880113001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_303438258668759 : Nat.Prime 303438258668759 := by
  have hfermat : (7 : ZMod 303438258668759) ^ (303438258668759 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 303438258668759) ^ ((303438258668759 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 303438258668759) ^ ((303438258668759 - 1) / 3451061) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 303438258668759) ^ ((303438258668759 - 1) / 43963039) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 303438258668759 (7 : ZMod 303438258668759)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3451061, 1), (43963039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3451061, 1), (43963039, 1)] : List FactorBlock).map factorBlockValue).prod = 303438258668759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_43963039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_341414284385441 : Nat.Prime 341414284385441 := by
  have hfermat : (3 : ZMod 341414284385441) ^ (341414284385441 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 341414284385441) ^ ((341414284385441 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 341414284385441) ^ ((341414284385441 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 341414284385441) ^ ((341414284385441 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 341414284385441) ^ ((341414284385441 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 341414284385441) ^ ((341414284385441 - 1) / 373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 341414284385441) ^ ((341414284385441 - 1) / 1979) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (3 : ZMod 341414284385441) ^ ((341414284385441 - 1) / 5657) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 341414284385441 (3 : ZMod 341414284385441)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (7, 1), (73, 1), (373, 1), (1979, 1), (5657, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (7, 1), (73, 1), (373, 1), (1979, 1), (5657, 1)] : List FactorBlock).map factorBlockValue).prod = 341414284385441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_424635761913071 : Nat.Prime 424635761913071 := by
  have hfermat : (11 : ZMod 424635761913071) ^ (424635761913071 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (11 : ZMod 424635761913071) ^ ((424635761913071 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (11 : ZMod 424635761913071) ^ ((424635761913071 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (11 : ZMod 424635761913071) ^ ((424635761913071 - 1) / 179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (11 : ZMod 424635761913071) ^ ((424635761913071 - 1) / 293) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (11 : ZMod 424635761913071) ^ ((424635761913071 - 1) / 20369) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (11 : ZMod 424635761913071) ^ ((424635761913071 - 1) / 39749) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 424635761913071 (11 : ZMod 424635761913071)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (179, 1), (293, 1), (20369, 1), (39749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (179, 1), (293, 1), (20369, 1), (39749, 1)] : List FactorBlock).map factorBlockValue).prod = 424635761913071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_524826545839549 : Nat.Prime 524826545839549 := by
  have hfermat : (10 : ZMod 524826545839549) ^ (524826545839549 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (10 : ZMod 524826545839549) ^ ((524826545839549 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (10 : ZMod 524826545839549) ^ ((524826545839549 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (10 : ZMod 524826545839549) ^ ((524826545839549 - 1) / 58613) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (10 : ZMod 524826545839549) ^ ((524826545839549 - 1) / 746174833) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 524826545839549 (10 : ZMod 524826545839549)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (58613, 1), (746174833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (58613, 1), (746174833, 1)] : List FactorBlock).map factorBlockValue).prod = 524826545839549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_746174833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_558330047988179 : Nat.Prime 558330047988179 := by
  have hfermat : (2 : ZMod 558330047988179) ^ (558330047988179 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 558330047988179) ^ ((558330047988179 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 558330047988179) ^ ((558330047988179 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 558330047988179) ^ ((558330047988179 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 558330047988179) ^ ((558330047988179 - 1) / 929) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 558330047988179) ^ ((558330047988179 - 1) / 34182751) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 558330047988179 (2 : ZMod 558330047988179)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (59, 1), (149, 1), (929, 1), (34182751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (59, 1), (149, 1), (929, 1), (34182751, 1)] : List FactorBlock).map factorBlockValue).prod = 558330047988179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_34182751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_597114222286237 : Nat.Prime 597114222286237 := by
  have hfermat : (2 : ZMod 597114222286237) ^ (597114222286237 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 597114222286237) ^ ((597114222286237 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 597114222286237) ^ ((597114222286237 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 597114222286237) ^ ((597114222286237 - 1) / 6760693) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 597114222286237) ^ ((597114222286237 - 1) / 7360121) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 597114222286237 (2 : ZMod 597114222286237)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (6760693, 1), (7360121, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (6760693, 1), (7360121, 1)] : List FactorBlock).map factorBlockValue).prod = 597114222286237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_598305796865503 : Nat.Prime 598305796865503 := by
  have hfermat : (5 : ZMod 598305796865503) ^ (598305796865503 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 598305796865503) ^ ((598305796865503 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 598305796865503) ^ ((598305796865503 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 598305796865503) ^ ((598305796865503 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 598305796865503) ^ ((598305796865503 - 1) / 3559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 598305796865503) ^ ((598305796865503 - 1) / 2547131033) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 598305796865503 (5 : ZMod 598305796865503)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (3559, 1), (2547131033, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (3559, 1), (2547131033, 1)] : List FactorBlock).map factorBlockValue).prod = 598305796865503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_2547131033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_718041816493973 : Nat.Prime 718041816493973 := by
  have hfermat : (2 : ZMod 718041816493973) ^ (718041816493973 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 718041816493973) ^ ((718041816493973 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 718041816493973) ^ ((718041816493973 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 718041816493973) ^ ((718041816493973 - 1) / 1370308810103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 718041816493973 (2 : ZMod 718041816493973)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (131, 1), (1370308810103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (131, 1), (1370308810103, 1)] : List FactorBlock).map factorBlockValue).prod = 718041816493973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1370308810103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_898128266586653 : Nat.Prime 898128266586653 := by
  have hfermat : (2 : ZMod 898128266586653) ^ (898128266586653 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 898128266586653) ^ ((898128266586653 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 898128266586653) ^ ((898128266586653 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 898128266586653) ^ ((898128266586653 - 1) / 1987009439351) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 898128266586653 (2 : ZMod 898128266586653)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (113, 1), (1987009439351, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (113, 1), (1987009439351, 1)] : List FactorBlock).map factorBlockValue).prod = 898128266586653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1987009439351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_1238336121476507 : Nat.Prime 1238336121476507 := by
  have hfermat : (2 : ZMod 1238336121476507) ^ (1238336121476507 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1238336121476507) ^ ((1238336121476507 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1238336121476507) ^ ((1238336121476507 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1238336121476507) ^ ((1238336121476507 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1238336121476507) ^ ((1238336121476507 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 1238336121476507) ^ ((1238336121476507 - 1) / 12445339003) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1238336121476507 (2 : ZMod 1238336121476507)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (43, 1), (89, 1), (12445339003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (43, 1), (89, 1), (12445339003, 1)] : List FactorBlock).map factorBlockValue).prod = 1238336121476507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_12445339003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1465764408851173 : Nat.Prime 1465764408851173 := by
  have hfermat : (2 : ZMod 1465764408851173) ^ (1465764408851173 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1465764408851173) ^ ((1465764408851173 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1465764408851173) ^ ((1465764408851173 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1465764408851173) ^ ((1465764408851173 - 1) / 123707) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1465764408851173) ^ ((1465764408851173 - 1) / 987389833) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1465764408851173 (2 : ZMod 1465764408851173)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (123707, 1), (987389833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (123707, 1), (987389833, 1)] : List FactorBlock).map factorBlockValue).prod = 1465764408851173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_987389833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2781138763680623 : Nat.Prime 2781138763680623 := by
  have hfermat : (5 : ZMod 2781138763680623) ^ (2781138763680623 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 2781138763680623) ^ ((2781138763680623 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 2781138763680623) ^ ((2781138763680623 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 2781138763680623) ^ ((2781138763680623 - 1) / 10723) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 2781138763680623) ^ ((2781138763680623 - 1) / 7628294221) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2781138763680623 (5 : ZMod 2781138763680623)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (10723, 1), (7628294221, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (10723, 1), (7628294221, 1)] : List FactorBlock).map factorBlockValue).prod = 2781138763680623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_7628294221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2821526234944009 : Nat.Prime 2821526234944009 := by
  have hfermat : (14 : ZMod 2821526234944009) ^ (2821526234944009 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (14 : ZMod 2821526234944009) ^ ((2821526234944009 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (14 : ZMod 2821526234944009) ^ ((2821526234944009 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (14 : ZMod 2821526234944009) ^ ((2821526234944009 - 1) / 117563593122667) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2821526234944009 (14 : ZMod 2821526234944009)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (117563593122667, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (117563593122667, 1)] : List FactorBlock).map factorBlockValue).prod = 2821526234944009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_117563593122667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_3083493800933647 : Nat.Prime 3083493800933647 := by
  have hfermat : (3 : ZMod 3083493800933647) ^ (3083493800933647 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 3083493800933647) ^ ((3083493800933647 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 3083493800933647) ^ ((3083493800933647 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 3083493800933647) ^ ((3083493800933647 - 1) / 10181683) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 3083493800933647) ^ ((3083493800933647 - 1) / 50474527) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3083493800933647 (3 : ZMod 3083493800933647)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (10181683, 1), (50474527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (10181683, 1), (50474527, 1)] : List FactorBlock).map factorBlockValue).prod = 3083493800933647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_10181683
      · exact prime_lucas_50474527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_3582685333717423 : Nat.Prime 3582685333717423 := by
  have hfermat : (5 : ZMod 3582685333717423) ^ (3582685333717423 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 3582685333717423) ^ ((3582685333717423 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 3582685333717423) ^ ((3582685333717423 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 3582685333717423) ^ ((3582685333717423 - 1) / 597114222286237) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3582685333717423 (5 : ZMod 3582685333717423)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (597114222286237, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (597114222286237, 1)] : List FactorBlock).map factorBlockValue).prod = 3582685333717423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_597114222286237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_3923312791804327 : Nat.Prime 3923312791804327 := by
  have hfermat : (3 : ZMod 3923312791804327) ^ (3923312791804327 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 3923312791804327) ^ ((3923312791804327 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 3923312791804327) ^ ((3923312791804327 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 3923312791804327) ^ ((3923312791804327 - 1) / 54347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 3923312791804327) ^ ((3923312791804327 - 1) / 148539203) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3923312791804327 (3 : ZMod 3923312791804327)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (54347, 1), (148539203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (54347, 1), (148539203, 1)] : List FactorBlock).map factorBlockValue).prod = 3923312791804327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_148539203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_4093111581118951 : Nat.Prime 4093111581118951 := by
  have hfermat : (17 : ZMod 4093111581118951) ^ (4093111581118951 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (17 : ZMod 4093111581118951) ^ ((4093111581118951 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (17 : ZMod 4093111581118951) ^ ((4093111581118951 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (17 : ZMod 4093111581118951) ^ ((4093111581118951 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (17 : ZMod 4093111581118951) ^ ((4093111581118951 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (17 : ZMod 4093111581118951) ^ ((4093111581118951 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (17 : ZMod 4093111581118951) ^ ((4093111581118951 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (17 : ZMod 4093111581118951) ^ ((4093111581118951 - 1) / 274132373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4093111581118951 (17 : ZMod 4093111581118951)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (13, 2), (19, 1), (31, 1), (274132373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (13, 2), (19, 1), (31, 1), (274132373, 1)] : List FactorBlock).map factorBlockValue).prod = 4093111581118951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_274132373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_4802020745398049 : Nat.Prime 4802020745398049 := by
  have hfermat : (3 : ZMod 4802020745398049) ^ (4802020745398049 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 4802020745398049) ^ ((4802020745398049 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 4802020745398049) ^ ((4802020745398049 - 1) / 150063148293689) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4802020745398049 (3 : ZMod 4802020745398049)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (150063148293689, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (150063148293689, 1)] : List FactorBlock).map factorBlockValue).prod = 4802020745398049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_150063148293689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_6683405989312453 : Nat.Prime 6683405989312453 := by
  have hfermat : (2 : ZMod 6683405989312453) ^ (6683405989312453 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 6683405989312453) ^ ((6683405989312453 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 6683405989312453) ^ ((6683405989312453 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 6683405989312453) ^ ((6683405989312453 - 1) / 139) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 6683405989312453) ^ ((6683405989312453 - 1) / 5501) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 6683405989312453) ^ ((6683405989312453 - 1) / 728383589) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6683405989312453 (2 : ZMod 6683405989312453)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (139, 1), (5501, 1), (728383589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (139, 1), (5501, 1), (728383589, 1)] : List FactorBlock).map factorBlockValue).prod = 6683405989312453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_728383589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_6775653207579911 : Nat.Prime 6775653207579911 := by
  have hfermat : (7 : ZMod 6775653207579911) ^ (6775653207579911 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 6775653207579911) ^ ((6775653207579911 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 6775653207579911) ^ ((6775653207579911 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 6775653207579911) ^ ((6775653207579911 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 6775653207579911) ^ ((6775653207579911 - 1) / 32611) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 6775653207579911) ^ ((6775653207579911 - 1) / 352155959) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6775653207579911 (7 : ZMod 6775653207579911)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (59, 1), (32611, 1), (352155959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (59, 1), (32611, 1), (352155959, 1)] : List FactorBlock).map factorBlockValue).prod = 6775653207579911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_352155959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_8904551051724217 : Nat.Prime 8904551051724217 := by
  have hfermat : (5 : ZMod 8904551051724217) ^ (8904551051724217 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 8904551051724217) ^ ((8904551051724217 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 8904551051724217) ^ ((8904551051724217 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 8904551051724217) ^ ((8904551051724217 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 8904551051724217) ^ ((8904551051724217 - 1) / 3788329) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 8904551051724217) ^ ((8904551051724217 - 1) / 13991203) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 8904551051724217 (5 : ZMod 8904551051724217)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (3788329, 1), (13991203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (3788329, 1), (13991203, 1)] : List FactorBlock).map factorBlockValue).prod = 8904551051724217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_13991203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_10902472715318479 : Nat.Prime 10902472715318479 := by
  have hfermat : (3 : ZMod 10902472715318479) ^ (10902472715318479 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 10902472715318479) ^ ((10902472715318479 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 10902472715318479) ^ ((10902472715318479 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 10902472715318479) ^ ((10902472715318479 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 10902472715318479) ^ ((10902472715318479 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 10902472715318479) ^ ((10902472715318479 - 1) / 8951127024071) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10902472715318479 (3 : ZMod 10902472715318479)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (29, 1), (8951127024071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (29, 1), (8951127024071, 1)] : List FactorBlock).map factorBlockValue).prod = 10902472715318479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_8951127024071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_16148003883585551 : Nat.Prime 16148003883585551 := by
  have hfermat : (17 : ZMod 16148003883585551) ^ (16148003883585551 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (17 : ZMod 16148003883585551) ^ ((16148003883585551 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (17 : ZMod 16148003883585551) ^ ((16148003883585551 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (17 : ZMod 16148003883585551) ^ ((16148003883585551 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (17 : ZMod 16148003883585551) ^ ((16148003883585551 - 1) / 4088102249009) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 16148003883585551 (17 : ZMod 16148003883585551)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (79, 1), (4088102249009, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (79, 1), (4088102249009, 1)] : List FactorBlock).map factorBlockValue).prod = 16148003883585551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_4088102249009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_19993273248689861 : Nat.Prime 19993273248689861 := by
  have hfermat : (2 : ZMod 19993273248689861) ^ (19993273248689861 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 19993273248689861) ^ ((19993273248689861 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 19993273248689861) ^ ((19993273248689861 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 19993273248689861) ^ ((19993273248689861 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 19993273248689861) ^ ((19993273248689861 - 1) / 5309) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 19993273248689861) ^ ((19993273248689861 - 1) / 548968039) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 19993273248689861 (2 : ZMod 19993273248689861)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 3), (5309, 1), (548968039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 3), (5309, 1), (548968039, 1)] : List FactorBlock).map factorBlockValue).prod = 19993273248689861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_548968039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_20498634974645969 : Nat.Prime 20498634974645969 := by
  have hfermat : (3 : ZMod 20498634974645969) ^ (20498634974645969 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 20498634974645969) ^ ((20498634974645969 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 20498634974645969) ^ ((20498634974645969 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 20498634974645969) ^ ((20498634974645969 - 1) / 183023526559339) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 20498634974645969 (3 : ZMod 20498634974645969)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (183023526559339, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (183023526559339, 1)] : List FactorBlock).map factorBlockValue).prod = 20498634974645969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_183023526559339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_23102061724805051 : Nat.Prime 23102061724805051 := by
  have hfermat : (2 : ZMod 23102061724805051) ^ (23102061724805051 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 23102061724805051) ^ ((23102061724805051 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 23102061724805051) ^ ((23102061724805051 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 23102061724805051) ^ ((23102061724805051 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 23102061724805051) ^ ((23102061724805051 - 1) / 7369) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 23102061724805051) ^ ((23102061724805051 - 1) / 4823128433) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 23102061724805051 (2 : ZMod 23102061724805051)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (13, 1), (7369, 1), (4823128433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (13, 1), (7369, 1), (4823128433, 1)] : List FactorBlock).map factorBlockValue).prod = 23102061724805051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_4823128433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_25888808655739969 : Nat.Prime 25888808655739969 := by
  have hfermat : (29 : ZMod 25888808655739969) ^ (25888808655739969 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (29 : ZMod 25888808655739969) ^ ((25888808655739969 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (29 : ZMod 25888808655739969) ^ ((25888808655739969 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (29 : ZMod 25888808655739969) ^ ((25888808655739969 - 1) / 2591) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (29 : ZMod 25888808655739969) ^ ((25888808655739969 - 1) / 61627) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (29 : ZMod 25888808655739969) ^ ((25888808655739969 - 1) / 844447) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 25888808655739969 (29 : ZMod 25888808655739969)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (2591, 1), (61627, 1), (844447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (2591, 1), (61627, 1), (844447, 1)] : List FactorBlock).map factorBlockValue).prod = 25888808655739969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_33819599447151131 : Nat.Prime 33819599447151131 := by
  have hfermat : (2 : ZMod 33819599447151131) ^ (33819599447151131 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 33819599447151131) ^ ((33819599447151131 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 33819599447151131) ^ ((33819599447151131 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 33819599447151131) ^ ((33819599447151131 - 1) / 8017) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 33819599447151131) ^ ((33819599447151131 - 1) / 595817) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 33819599447151131) ^ ((33819599447151131 - 1) / 708017) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 33819599447151131 (2 : ZMod 33819599447151131)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (8017, 1), (595817, 1), (708017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (8017, 1), (595817, 1), (708017, 1)] : List FactorBlock).map factorBlockValue).prod = 33819599447151131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_35618204206896869 : Nat.Prime 35618204206896869 := by
  have hfermat : (2 : ZMod 35618204206896869) ^ (35618204206896869 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 35618204206896869) ^ ((35618204206896869 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 35618204206896869) ^ ((35618204206896869 - 1) / 8904551051724217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 35618204206896869 (2 : ZMod 35618204206896869)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (8904551051724217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (8904551051724217, 1)] : List FactorBlock).map factorBlockValue).prod = 35618204206896869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_8904551051724217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_46839176590082237 : Nat.Prime 46839176590082237 := by
  have hfermat : (2 : ZMod 46839176590082237) ^ (46839176590082237 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 46839176590082237) ^ ((46839176590082237 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 46839176590082237) ^ ((46839176590082237 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 46839176590082237) ^ ((46839176590082237 - 1) / 32437102901719) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 46839176590082237 (2 : ZMod 46839176590082237)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 2), (32437102901719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 2), (32437102901719, 1)] : List FactorBlock).map factorBlockValue).prod = 46839176590082237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_32437102901719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_71236408413793739 : Nat.Prime 71236408413793739 := by
  have hfermat : (2 : ZMod 71236408413793739) ^ (71236408413793739 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 71236408413793739) ^ ((71236408413793739 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 71236408413793739) ^ ((71236408413793739 - 1) / 35618204206896869) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 71236408413793739 (2 : ZMod 71236408413793739)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (35618204206896869, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (35618204206896869, 1)] : List FactorBlock).map factorBlockValue).prod = 71236408413793739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_35618204206896869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_96159285717625717 : Nat.Prime 96159285717625717 := by
  have hfermat : (2 : ZMod 96159285717625717) ^ (96159285717625717 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 96159285717625717) ^ ((96159285717625717 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 96159285717625717) ^ ((96159285717625717 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 96159285717625717) ^ ((96159285717625717 - 1) / 727) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 96159285717625717) ^ ((96159285717625717 - 1) / 1079173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 96159285717625717) ^ ((96159285717625717 - 1) / 10213733) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 96159285717625717 (2 : ZMod 96159285717625717)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (727, 1), (1079173, 1), (10213733, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (727, 1), (1079173, 1), (10213733, 1)] : List FactorBlock).map factorBlockValue).prod = 96159285717625717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_10213733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_103555234622959877 : Nat.Prime 103555234622959877 := by
  have hfermat : (2 : ZMod 103555234622959877) ^ (103555234622959877 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 103555234622959877) ^ ((103555234622959877 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 103555234622959877) ^ ((103555234622959877 - 1) / 25888808655739969) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 103555234622959877 (2 : ZMod 103555234622959877)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (25888808655739969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (25888808655739969, 1)] : List FactorBlock).map factorBlockValue).prod = 103555234622959877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_25888808655739969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_105890264413236701 : Nat.Prime 105890264413236701 := by
  have hfermat : (2 : ZMod 105890264413236701) ^ (105890264413236701 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 105890264413236701) ^ ((105890264413236701 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 105890264413236701) ^ ((105890264413236701 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 105890264413236701) ^ ((105890264413236701 - 1) / 313) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 105890264413236701) ^ ((105890264413236701 - 1) / 3383075540359) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 105890264413236701 (2 : ZMod 105890264413236701)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (313, 1), (3383075540359, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (313, 1), (3383075540359, 1)] : List FactorBlock).map factorBlockValue).prod = 105890264413236701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_3383075540359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_185750418221476051 : Nat.Prime 185750418221476051 := by
  have hfermat : (2 : ZMod 185750418221476051) ^ (185750418221476051 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 185750418221476051) ^ ((185750418221476051 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 185750418221476051) ^ ((185750418221476051 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 185750418221476051) ^ ((185750418221476051 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 185750418221476051) ^ ((185750418221476051 - 1) / 1238336121476507) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 185750418221476051 (2 : ZMod 185750418221476051)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (1238336121476507, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (1238336121476507, 1)] : List FactorBlock).map factorBlockValue).prod = 185750418221476051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1238336121476507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_210110911827666907 : Nat.Prime 210110911827666907 := by
  have hfermat : (2 : ZMod 210110911827666907) ^ (210110911827666907 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 210110911827666907) ^ ((210110911827666907 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 210110911827666907) ^ ((210110911827666907 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 210110911827666907) ^ ((210110911827666907 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 210110911827666907) ^ ((210110911827666907 - 1) / 98809) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 210110911827666907) ^ ((210110911827666907 - 1) / 50629403777) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 210110911827666907 (2 : ZMod 210110911827666907)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (98809, 1), (50629403777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (98809, 1), (50629403777, 1)] : List FactorBlock).map factorBlockValue).prod = 210110911827666907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_50629403777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_222110141675359409 : Nat.Prime 222110141675359409 := by
  have hfermat : (3 : ZMod 222110141675359409) ^ (222110141675359409 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 222110141675359409) ^ ((222110141675359409 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 222110141675359409) ^ ((222110141675359409 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 222110141675359409) ^ ((222110141675359409 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 222110141675359409) ^ ((222110141675359409 - 1) / 3389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 222110141675359409) ^ ((222110141675359409 - 1) / 484580539) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 222110141675359409 (3 : ZMod 222110141675359409)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (79, 1), (107, 1), (3389, 1), (484580539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (79, 1), (107, 1), (3389, 1), (484580539, 1)] : List FactorBlock).map factorBlockValue).prod = 222110141675359409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_484580539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_244700590586689451 : Nat.Prime 244700590586689451 := by
  have hfermat : (2 : ZMod 244700590586689451) ^ (244700590586689451 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 244700590586689451) ^ ((244700590586689451 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 244700590586689451) ^ ((244700590586689451 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 244700590586689451) ^ ((244700590586689451 - 1) / 1515817) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 244700590586689451) ^ ((244700590586689451 - 1) / 3228629717) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 244700590586689451 (2 : ZMod 244700590586689451)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (1515817, 1), (3228629717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (1515817, 1), (3228629717, 1)] : List FactorBlock).map factorBlockValue).prod = 244700590586689451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_3228629717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_265560458835600329 : Nat.Prime 265560458835600329 := by
  have hfermat : (3 : ZMod 265560458835600329) ^ (265560458835600329 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 265560458835600329) ^ ((265560458835600329 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 265560458835600329) ^ ((265560458835600329 - 1) / 22571) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 265560458835600329) ^ ((265560458835600329 - 1) / 1470695022571) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 265560458835600329 (3 : ZMod 265560458835600329)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (22571, 1), (1470695022571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (22571, 1), (1470695022571, 1)] : List FactorBlock).map factorBlockValue).prod = 265560458835600329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1470695022571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_375674299123933031 : Nat.Prime 375674299123933031 := by
  have hfermat : (29 : ZMod 375674299123933031) ^ (375674299123933031 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (29 : ZMod 375674299123933031) ^ ((375674299123933031 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (29 : ZMod 375674299123933031) ^ ((375674299123933031 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (29 : ZMod 375674299123933031) ^ ((375674299123933031 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (29 : ZMod 375674299123933031) ^ ((375674299123933031 - 1) / 2687) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (29 : ZMod 375674299123933031) ^ ((375674299123933031 - 1) / 58543) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (29 : ZMod 375674299123933031) ^ ((375674299123933031 - 1) / 18370691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 375674299123933031 (29 : ZMod 375674299123933031)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (2687, 1), (58543, 1), (18370691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (2687, 1), (58543, 1), (18370691, 1)] : List FactorBlock).map factorBlockValue).prod = 375674299123933031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_18370691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_403249829858894861 : Nat.Prime 403249829858894861 := by
  have hfermat : (2 : ZMod 403249829858894861) ^ (403249829858894861 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 403249829858894861) ^ ((403249829858894861 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 403249829858894861) ^ ((403249829858894861 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 403249829858894861) ^ ((403249829858894861 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 403249829858894861) ^ ((403249829858894861 - 1) / 197) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 403249829858894861) ^ ((403249829858894861 - 1) / 129497) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 403249829858894861) ^ ((403249829858894861 - 1) / 34362949) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 403249829858894861 (2 : ZMod 403249829858894861)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (23, 1), (197, 1), (129497, 1), (34362949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (23, 1), (197, 1), (129497, 1), (34362949, 1)] : List FactorBlock).map factorBlockValue).prod = 403249829858894861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_34362949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_667849920908295871 : Nat.Prime 667849920908295871 := by
  have hfermat : (3 : ZMod 667849920908295871) ^ (667849920908295871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 667849920908295871) ^ ((667849920908295871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 667849920908295871) ^ ((667849920908295871 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 667849920908295871) ^ ((667849920908295871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 667849920908295871) ^ ((667849920908295871 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 667849920908295871) ^ ((667849920908295871 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 667849920908295871) ^ ((667849920908295871 - 1) / 100447) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (3 : ZMod 667849920908295871) ^ ((667849920908295871 - 1) / 4854151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 667849920908295871 (3 : ZMod 667849920908295871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (5, 1), (19, 1), (89, 1), (100447, 1), (4854151, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (5, 1), (19, 1), (89, 1), (100447, 1), (4854151, 1)] : List FactorBlock).map factorBlockValue).prod = 667849920908295871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_1088652011356783903 : Nat.Prime 1088652011356783903 := by
  have hfermat : (3 : ZMod 1088652011356783903) ^ (1088652011356783903 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 1088652011356783903) ^ ((1088652011356783903 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 1088652011356783903) ^ ((1088652011356783903 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 1088652011356783903) ^ ((1088652011356783903 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 1088652011356783903) ^ ((1088652011356783903 - 1) / 18439909) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 1088652011356783903) ^ ((1088652011356783903 - 1) / 1405662359) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1088652011356783903 (3 : ZMod 1088652011356783903)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (18439909, 1), (1405662359, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (18439909, 1), (1405662359, 1)] : List FactorBlock).map factorBlockValue).prod = 1088652011356783903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_18439909
      · exact prime_lucas_1405662359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1194043857971451187 : Nat.Prime 1194043857971451187 := by
  have hfermat : (3 : ZMod 1194043857971451187) ^ (1194043857971451187 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 1194043857971451187) ^ ((1194043857971451187 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 1194043857971451187) ^ ((1194043857971451187 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 1194043857971451187) ^ ((1194043857971451187 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 1194043857971451187) ^ ((1194043857971451187 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 1194043857971451187) ^ ((1194043857971451187 - 1) / 19861) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 1194043857971451187) ^ ((1194043857971451187 - 1) / 84201718609) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1194043857971451187 (3 : ZMod 1194043857971451187)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (17, 1), (19861, 1), (84201718609, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (17, 1), (19861, 1), (84201718609, 1)] : List FactorBlock).map factorBlockValue).prod = 1194043857971451187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_84201718609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_1684218309306738157 : Nat.Prime 1684218309306738157 := by
  have hfermat : (5 : ZMod 1684218309306738157) ^ (1684218309306738157 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 1684218309306738157) ^ ((1684218309306738157 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 1684218309306738157) ^ ((1684218309306738157 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 1684218309306738157) ^ ((1684218309306738157 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 1684218309306738157) ^ ((1684218309306738157 - 1) / 6683405989312453) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1684218309306738157 (5 : ZMod 1684218309306738157)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (7, 1), (6683405989312453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (7, 1), (6683405989312453, 1)] : List FactorBlock).map factorBlockValue).prod = 1684218309306738157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_6683405989312453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1968630936296891047 : Nat.Prime 1968630936296891047 := by
  have hfermat : (5 : ZMod 1968630936296891047) ^ (1968630936296891047 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 1968630936296891047) ^ ((1968630936296891047 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 1968630936296891047) ^ ((1968630936296891047 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 1968630936296891047) ^ ((1968630936296891047 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 1968630936296891047) ^ ((1968630936296891047 - 1) / 421) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 1968630936296891047) ^ ((1968630936296891047 - 1) / 128981) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (5 : ZMod 1968630936296891047) ^ ((1968630936296891047 - 1) / 318017939) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1968630936296891047 (5 : ZMod 1968630936296891047)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (421, 1), (128981, 1), (318017939, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (421, 1), (128981, 1), (318017939, 1)] : List FactorBlock).map factorBlockValue).prod = 1968630936296891047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_318017939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_2656056057371325113 : Nat.Prime 2656056057371325113 := by
  have hfermat : (5 : ZMod 2656056057371325113) ^ (2656056057371325113 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 2656056057371325113) ^ ((2656056057371325113 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 2656056057371325113) ^ ((2656056057371325113 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 2656056057371325113) ^ ((2656056057371325113 - 1) / 6775653207579911) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2656056057371325113 (5 : ZMod 2656056057371325113)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 2), (6775653207579911, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 2), (6775653207579911, 1)] : List FactorBlock).map factorBlockValue).prod = 2656056057371325113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_6775653207579911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_4613671718187120353 : Nat.Prime 4613671718187120353 := by
  have hfermat : (3 : ZMod 4613671718187120353) ^ (4613671718187120353 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 4613671718187120353) ^ ((4613671718187120353 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 4613671718187120353) ^ ((4613671718187120353 - 1) / 151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 4613671718187120353) ^ ((4613671718187120353 - 1) / 21601) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 4613671718187120353) ^ ((4613671718187120353 - 1) / 44202405761) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4613671718187120353 (3 : ZMod 4613671718187120353)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (151, 1), (21601, 1), (44202405761, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (151, 1), (21601, 1), (44202405761, 1)] : List FactorBlock).map factorBlockValue).prod = 4613671718187120353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_44202405761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_5156250895325744483 : Nat.Prime 5156250895325744483 := by
  have hfermat : (2 : ZMod 5156250895325744483) ^ (5156250895325744483 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 5156250895325744483) ^ ((5156250895325744483 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 5156250895325744483) ^ ((5156250895325744483 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 5156250895325744483) ^ ((5156250895325744483 - 1) / 2003) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 5156250895325744483) ^ ((5156250895325744483 - 1) / 7523) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 5156250895325744483) ^ ((5156250895325744483 - 1) / 25639) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 5156250895325744483) ^ ((5156250895325744483 - 1) / 290137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 5156250895325744483 (2 : ZMod 5156250895325744483)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (2003, 1), (7523, 1), (25639, 1), (290137, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (2003, 1), (7523, 1), (25639, 1), (290137, 1)] : List FactorBlock).map factorBlockValue).prod = 5156250895325744483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_7397764714063735589 : Nat.Prime 7397764714063735589 := by
  have hfermat : (2 : ZMod 7397764714063735589) ^ (7397764714063735589 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 7397764714063735589) ^ ((7397764714063735589 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 7397764714063735589) ^ ((7397764714063735589 - 1) / 5417) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 7397764714063735589) ^ ((7397764714063735589 - 1) / 341414284385441) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7397764714063735589 (2 : ZMod 7397764714063735589)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5417, 1), (341414284385441, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5417, 1), (341414284385441, 1)] : List FactorBlock).map factorBlockValue).prod = 7397764714063735589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_341414284385441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_7800296316823861871 : Nat.Prime 7800296316823861871 := by
  have hfermat : (13 : ZMod 7800296316823861871) ^ (7800296316823861871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (13 : ZMod 7800296316823861871) ^ ((7800296316823861871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (13 : ZMod 7800296316823861871) ^ ((7800296316823861871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (13 : ZMod 7800296316823861871) ^ ((7800296316823861871 - 1) / 5023) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (13 : ZMod 7800296316823861871) ^ ((7800296316823861871 - 1) / 155291585045269) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7800296316823861871 (13 : ZMod 7800296316823861871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (5023, 1), (155291585045269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (5023, 1), (155291585045269, 1)] : List FactorBlock).map factorBlockValue).prod = 7800296316823861871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_155291585045269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_10372631410840922203 : Nat.Prime 10372631410840922203 := by
  have hfermat : (7 : ZMod 10372631410840922203) ^ (10372631410840922203 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 10372631410840922203) ^ ((10372631410840922203 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 10372631410840922203) ^ ((10372631410840922203 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 10372631410840922203) ^ ((10372631410840922203 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 10372631410840922203) ^ ((10372631410840922203 - 1) / 388483) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 10372631410840922203) ^ ((10372631410840922203 - 1) / 635722578707) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10372631410840922203 (7 : ZMod 10372631410840922203)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (388483, 1), (635722578707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (388483, 1), (635722578707, 1)] : List FactorBlock).map factorBlockValue).prod = 10372631410840922203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_635722578707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_12894713954982603113 : Nat.Prime 12894713954982603113 := by
  have hfermat : (3 : ZMod 12894713954982603113) ^ (12894713954982603113 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 12894713954982603113) ^ ((12894713954982603113 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 12894713954982603113) ^ ((12894713954982603113 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 12894713954982603113) ^ ((12894713954982603113 - 1) / 4001237) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 12894713954982603113) ^ ((12894713954982603113 - 1) / 9825249617) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12894713954982603113 (3 : ZMod 12894713954982603113)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (41, 1), (4001237, 1), (9825249617, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (41, 1), (4001237, 1), (9825249617, 1)] : List FactorBlock).map factorBlockValue).prod = 12894713954982603113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_9825249617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_14536062572962072817 : Nat.Prime 14536062572962072817 := by
  have hfermat : (3 : ZMod 14536062572962072817) ^ (14536062572962072817 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 14536062572962072817) ^ ((14536062572962072817 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 14536062572962072817) ^ ((14536062572962072817 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 14536062572962072817) ^ ((14536062572962072817 - 1) / 25367) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 14536062572962072817) ^ ((14536062572962072817 - 1) / 30211) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 14536062572962072817) ^ ((14536062572962072817 - 1) / 32039879) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 14536062572962072817 (3 : ZMod 14536062572962072817)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (37, 1), (25367, 1), (30211, 1), (32039879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (37, 1), (25367, 1), (30211, 1), (32039879, 1)] : List FactorBlock).map factorBlockValue).prod = 14536062572962072817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_32039879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_18533799619388085871 : Nat.Prime 18533799619388085871 := by
  have hfermat : (3 : ZMod 18533799619388085871) ^ (18533799619388085871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 18533799619388085871) ^ ((18533799619388085871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 18533799619388085871) ^ ((18533799619388085871 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 18533799619388085871) ^ ((18533799619388085871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 18533799619388085871) ^ ((18533799619388085871 - 1) / 2347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 18533799619388085871) ^ ((18533799619388085871 - 1) / 87742269655769) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 18533799619388085871 (3 : ZMod 18533799619388085871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (2347, 1), (87742269655769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (2347, 1), (87742269655769, 1)] : List FactorBlock).map factorBlockValue).prod = 18533799619388085871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_87742269655769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_25048686373187790479 : Nat.Prime 25048686373187790479 := by
  have hfermat : (11 : ZMod 25048686373187790479) ^ (25048686373187790479 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (11 : ZMod 25048686373187790479) ^ ((25048686373187790479 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (11 : ZMod 25048686373187790479) ^ ((25048686373187790479 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (11 : ZMod 25048686373187790479) ^ ((25048686373187790479 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (11 : ZMod 25048686373187790479) ^ ((25048686373187790479 - 1) / 117039913) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (11 : ZMod 25048686373187790479) ^ ((25048686373187790479 - 1) / 512005567) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 25048686373187790479 (11 : ZMod 25048686373187790479)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (19, 1), (117039913, 1), (512005567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (19, 1), (117039913, 1), (512005567, 1)] : List FactorBlock).map factorBlockValue).prod = 25048686373187790479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_117039913
      · exact prime_lucas_512005567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_43786908338927870449 : Nat.Prime 43786908338927870449 := by
  have hfermat : (13 : ZMod 43786908338927870449) ^ (43786908338927870449 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (13 : ZMod 43786908338927870449) ^ ((43786908338927870449 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (13 : ZMod 43786908338927870449) ^ ((43786908338927870449 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (13 : ZMod 43786908338927870449) ^ ((43786908338927870449 - 1) / 579251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (13 : ZMod 43786908338927870449) ^ ((43786908338927870449 - 1) / 19442460871) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 43786908338927870449 (13 : ZMod 43786908338927870449)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 5), (579251, 1), (19442460871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 5), (579251, 1), (19442460871, 1)] : List FactorBlock).map factorBlockValue).prod = 43786908338927870449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_19442460871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_44616760993439968241 : Nat.Prime 44616760993439968241 := by
  have hfermat : (6 : ZMod 44616760993439968241) ^ (44616760993439968241 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 44616760993439968241) ^ ((44616760993439968241 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 44616760993439968241) ^ ((44616760993439968241 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 44616760993439968241) ^ ((44616760993439968241 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 44616760993439968241) ^ ((44616760993439968241 - 1) / 489529) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 44616760993439968241) ^ ((44616760993439968241 - 1) / 16046165917) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 44616760993439968241 (6 : ZMod 44616760993439968241)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (71, 1), (489529, 1), (16046165917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (71, 1), (489529, 1), (16046165917, 1)] : List FactorBlock).map factorBlockValue).prod = 44616760993439968241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_16046165917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_46995417618581185339 : Nat.Prime 46995417618581185339 := by
  have hfermat : (23 : ZMod 46995417618581185339) ^ (46995417618581185339 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (23 : ZMod 46995417618581185339) ^ ((46995417618581185339 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (23 : ZMod 46995417618581185339) ^ ((46995417618581185339 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (23 : ZMod 46995417618581185339) ^ ((46995417618581185339 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (23 : ZMod 46995417618581185339) ^ ((46995417618581185339 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (23 : ZMod 46995417618581185339) ^ ((46995417618581185339 - 1) / 9293) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (23 : ZMod 46995417618581185339) ^ ((46995417618581185339 - 1) / 21841) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (23 : ZMod 46995417618581185339) ^ ((46995417618581185339 - 1) / 44305501) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 46995417618581185339 (23 : ZMod 46995417618581185339)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (67, 1), (9293, 1), (21841, 1), (44305501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (67, 1), (9293, 1), (21841, 1), (44305501, 1)] : List FactorBlock).map factorBlockValue).prod = 46995417618581185339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_44305501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_59182117712509884713 : Nat.Prime 59182117712509884713 := by
  have hfermat : (3 : ZMod 59182117712509884713) ^ (59182117712509884713 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 59182117712509884713) ^ ((59182117712509884713 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 59182117712509884713) ^ ((59182117712509884713 - 1) / 7397764714063735589) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 59182117712509884713 (3 : ZMod 59182117712509884713)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7397764714063735589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7397764714063735589, 1)] : List FactorBlock).map factorBlockValue).prod = 59182117712509884713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_7397764714063735589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_78863960059692249863 : Nat.Prime 78863960059692249863 := by
  have hfermat : (5 : ZMod 78863960059692249863) ^ (78863960059692249863 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 78863960059692249863) ^ ((78863960059692249863 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 78863960059692249863) ^ ((78863960059692249863 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 78863960059692249863) ^ ((78863960059692249863 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 78863960059692249863) ^ ((78863960059692249863 - 1) / 5521) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 78863960059692249863) ^ ((78863960059692249863 - 1) / 32913275436683) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 78863960059692249863 (5 : ZMod 78863960059692249863)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (31, 1), (5521, 1), (32913275436683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (31, 1), (5521, 1), (32913275436683, 1)] : List FactorBlock).map factorBlockValue).prod = 78863960059692249863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_32913275436683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_92227638942914506907 : Nat.Prime 92227638942914506907 := by
  have hfermat : (2 : ZMod 92227638942914506907) ^ (92227638942914506907 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 92227638942914506907) ^ ((92227638942914506907 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 92227638942914506907) ^ ((92227638942914506907 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 92227638942914506907) ^ ((92227638942914506907 - 1) / 12013949) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 92227638942914506907) ^ ((92227638942914506907 - 1) / 548336645671) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 92227638942914506907 (2 : ZMod 92227638942914506907)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (12013949, 1), (548336645671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (12013949, 1), (548336645671, 1)] : List FactorBlock).map factorBlockValue).prod = 92227638942914506907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_12013949
      · exact prime_lucas_548336645671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_159363363442279506781 : Nat.Prime 159363363442279506781 := by
  have hfermat : (2 : ZMod 159363363442279506781) ^ (159363363442279506781 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 159363363442279506781) ^ ((159363363442279506781 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 159363363442279506781) ^ ((159363363442279506781 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 159363363442279506781) ^ ((159363363442279506781 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 159363363442279506781) ^ ((159363363442279506781 - 1) / 2656056057371325113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 159363363442279506781 (2 : ZMod 159363363442279506781)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (2656056057371325113, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (2656056057371325113, 1)] : List FactorBlock).map factorBlockValue).prod = 159363363442279506781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_2656056057371325113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_162746073594876543923 : Nat.Prime 162746073594876543923 := by
  have hfermat : (2 : ZMod 162746073594876543923) ^ (162746073594876543923 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 162746073594876543923) ^ ((162746073594876543923 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 162746073594876543923) ^ ((162746073594876543923 - 1) / 12035197) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 162746073594876543923) ^ ((162746073594876543923 - 1) / 6761255075213) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 162746073594876543923 (2 : ZMod 162746073594876543923)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (12035197, 1), (6761255075213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (12035197, 1), (6761255075213, 1)] : List FactorBlock).map factorBlockValue).prod = 162746073594876543923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · exact prime_lucas_12035197
      · exact prime_lucas_6761255075213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_173150287583619764833 : Nat.Prime 173150287583619764833 := by
  have hfermat : (31 : ZMod 173150287583619764833) ^ (173150287583619764833 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (31 : ZMod 173150287583619764833) ^ ((173150287583619764833 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (31 : ZMod 173150287583619764833) ^ ((173150287583619764833 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (31 : ZMod 173150287583619764833) ^ ((173150287583619764833 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (31 : ZMod 173150287583619764833) ^ ((173150287583619764833 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (31 : ZMod 173150287583619764833) ^ ((173150287583619764833 - 1) / 7019) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (31 : ZMod 173150287583619764833) ^ ((173150287583619764833 - 1) / 466364133493) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 173150287583619764833 (31 : ZMod 173150287583619764833)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (19, 1), (29, 1), (7019, 1), (466364133493, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (19, 1), (29, 1), (7019, 1), (466364133493, 1)] : List FactorBlock).map factorBlockValue).prod = 173150287583619764833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_466364133493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_200389490985502323833 : Nat.Prime 200389490985502323833 := by
  have hfermat : (3 : ZMod 200389490985502323833) ^ (200389490985502323833 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 200389490985502323833) ^ ((200389490985502323833 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 200389490985502323833) ^ ((200389490985502323833 - 1) / 25048686373187790479) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 200389490985502323833 (3 : ZMod 200389490985502323833)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (25048686373187790479, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (25048686373187790479, 1)] : List FactorBlock).map factorBlockValue).prod = 200389490985502323833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_25048686373187790479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_325492147189753087847 : Nat.Prime 325492147189753087847 := by
  have hfermat : (5 : ZMod 325492147189753087847) ^ (325492147189753087847 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 325492147189753087847) ^ ((325492147189753087847 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 325492147189753087847) ^ ((325492147189753087847 - 1) / 162746073594876543923) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 325492147189753087847 (5 : ZMod 325492147189753087847)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (162746073594876543923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (162746073594876543923, 1)] : List FactorBlock).map factorBlockValue).prod = 325492147189753087847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_162746073594876543923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_629815722609068193773 : Nat.Prime 629815722609068193773 := by
  have hfermat : (2 : ZMod 629815722609068193773) ^ (629815722609068193773 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 629815722609068193773) ^ ((629815722609068193773 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 629815722609068193773) ^ ((629815722609068193773 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 629815722609068193773) ^ ((629815722609068193773 - 1) / 263) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 629815722609068193773) ^ ((629815722609068193773 - 1) / 401) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 629815722609068193773) ^ ((629815722609068193773 - 1) / 213282560372923) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 629815722609068193773 (2 : ZMod 629815722609068193773)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (263, 1), (401, 1), (213282560372923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (263, 1), (401, 1), (213282560372923, 1)] : List FactorBlock).map factorBlockValue).prod = 629815722609068193773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_213282560372923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_683309107403746987363 : Nat.Prime 683309107403746987363 := by
  have hfermat : (2 : ZMod 683309107403746987363) ^ (683309107403746987363 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 683309107403746987363) ^ ((683309107403746987363 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 683309107403746987363) ^ ((683309107403746987363 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 683309107403746987363) ^ ((683309107403746987363 - 1) / 40949) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 683309107403746987363) ^ ((683309107403746987363 - 1) / 2781138763680623) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 683309107403746987363 (2 : ZMod 683309107403746987363)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (40949, 1), (2781138763680623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (40949, 1), (2781138763680623, 1)] : List FactorBlock).map factorBlockValue).prod = 683309107403746987363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_2781138763680623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_798060315533818107677 : Nat.Prime 798060315533818107677 := by
  have hfermat : (2 : ZMod 798060315533818107677) ^ (798060315533818107677 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 798060315533818107677) ^ ((798060315533818107677 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 798060315533818107677) ^ ((798060315533818107677 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 798060315533818107677) ^ ((798060315533818107677 - 1) / 293) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 798060315533818107677) ^ ((798060315533818107677 - 1) / 311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 798060315533818107677) ^ ((798060315533818107677 - 1) / 6241691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 798060315533818107677) ^ ((798060315533818107677 - 1) / 18462557) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 798060315533818107677 (2 : ZMod 798060315533818107677)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (293, 1), (311, 1), (6241691, 1), (18462557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (293, 1), (311, 1), (6241691, 1), (18462557, 1)] : List FactorBlock).map factorBlockValue).prod = 798060315533818107677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_18462557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_910634610394437306857 : Nat.Prime 910634610394437306857 := by
  have hfermat : (3 : ZMod 910634610394437306857) ^ (910634610394437306857 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 910634610394437306857) ^ ((910634610394437306857 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 910634610394437306857) ^ ((910634610394437306857 - 1) / 2148353) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 910634610394437306857) ^ ((910634610394437306857 - 1) / 52984461259069) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 910634610394437306857 (3 : ZMod 910634610394437306857)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (2148353, 1), (52984461259069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (2148353, 1), (52984461259069, 1)] : List FactorBlock).map factorBlockValue).prod = 910634610394437306857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_52984461259069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_960514331081427865447 : Nat.Prime 960514331081427865447 := by
  have hfermat : (6 : ZMod 960514331081427865447) ^ (960514331081427865447 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 960514331081427865447) ^ ((960514331081427865447 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 960514331081427865447) ^ ((960514331081427865447 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 960514331081427865447) ^ ((960514331081427865447 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 960514331081427865447) ^ ((960514331081427865447 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 960514331081427865447) ^ ((960514331081427865447 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (6 : ZMod 960514331081427865447) ^ ((960514331081427865447 - 1) / 569) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (6 : ZMod 960514331081427865447) ^ ((960514331081427865447 - 1) / 941) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (6 : ZMod 960514331081427865447) ^ ((960514331081427865447 - 1) / 22073) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (6 : ZMod 960514331081427865447) ^ ((960514331081427865447 - 1) / 212419) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 960514331081427865447 (6 : ZMod 960514331081427865447)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 2), (17, 1), (31, 1), (569, 1), (941, 1), (22073, 1), (212419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 2), (17, 1), (31, 1), (569, 1), (941, 1), (22073, 1), (212419, 1)] : List FactorBlock).map factorBlockValue).prod = 960514331081427865447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
theorem prime_lucas_1068595601196333123553 : Nat.Prime 1068595601196333123553 := by
  have hfermat : (5 : ZMod 1068595601196333123553) ^ (1068595601196333123553 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 1068595601196333123553) ^ ((1068595601196333123553 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 1068595601196333123553) ^ ((1068595601196333123553 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 1068595601196333123553) ^ ((1068595601196333123553 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 1068595601196333123553) ^ ((1068595601196333123553 - 1) / 997) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 1068595601196333123553) ^ ((1068595601196333123553 - 1) / 210654684414157) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1068595601196333123553 (5 : ZMod 1068595601196333123553)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (53, 1), (997, 1), (210654684414157, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (53, 1), (997, 1), (210654684414157, 1)] : List FactorBlock).map factorBlockValue).prod = 1068595601196333123553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_210654684414157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1188120256076643679787 : Nat.Prime 1188120256076643679787 := by
  have hfermat : (2 : ZMod 1188120256076643679787) ^ (1188120256076643679787 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1188120256076643679787) ^ ((1188120256076643679787 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1188120256076643679787) ^ ((1188120256076643679787 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1188120256076643679787) ^ ((1188120256076643679787 - 1) / 691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1188120256076643679787) ^ ((1188120256076643679787 - 1) / 19993273248689861) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1188120256076643679787 (2 : ZMod 1188120256076643679787)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (43, 1), (691, 1), (19993273248689861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (43, 1), (691, 1), (19993273248689861, 1)] : List FactorBlock).map factorBlockValue).prod = 1188120256076643679787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_19993273248689861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1394059191531732258737 : Nat.Prime 1394059191531732258737 := by
  have hfermat : (3 : ZMod 1394059191531732258737) ^ (1394059191531732258737 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 1394059191531732258737) ^ ((1394059191531732258737 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 1394059191531732258737) ^ ((1394059191531732258737 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 1394059191531732258737) ^ ((1394059191531732258737 - 1) / 109) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 1394059191531732258737) ^ ((1394059191531732258737 - 1) / 569) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 1394059191531732258737) ^ ((1394059191531732258737 - 1) / 1841187124877) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1394059191531732258737 (3 : ZMod 1394059191531732258737)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (109, 2), (569, 1), (1841187124877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (109, 2), (569, 1), (1841187124877, 1)] : List FactorBlock).map factorBlockValue).prod = 1394059191531732258737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1841187124877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_2318774925393603264113 : Nat.Prime 2318774925393603264113 := by
  have hfermat : (5 : ZMod 2318774925393603264113) ^ (2318774925393603264113 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 2318774925393603264113) ^ ((2318774925393603264113 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 2318774925393603264113) ^ ((2318774925393603264113 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 2318774925393603264113) ^ ((2318774925393603264113 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 2318774925393603264113) ^ ((2318774925393603264113 - 1) / 667849920908295871) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2318774925393603264113 (5 : ZMod 2318774925393603264113)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (31, 1), (667849920908295871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (31, 1), (667849920908295871, 1)] : List FactorBlock).map factorBlockValue).prod = 2318774925393603264113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_667849920908295871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_3125508632188182161699 : Nat.Prime 3125508632188182161699 := by
  have hfermat : (2 : ZMod 3125508632188182161699) ^ (3125508632188182161699 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 3125508632188182161699) ^ ((3125508632188182161699 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 3125508632188182161699) ^ ((3125508632188182161699 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 3125508632188182161699) ^ ((3125508632188182161699 - 1) / 5689) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 3125508632188182161699) ^ ((3125508632188182161699 - 1) / 2152637) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 3125508632188182161699) ^ ((3125508632188182161699 - 1) / 18229969099) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3125508632188182161699 (2 : ZMod 3125508632188182161699)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (5689, 1), (2152637, 1), (18229969099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (5689, 1), (2152637, 1), (18229969099, 1)] : List FactorBlock).map factorBlockValue).prod = 3125508632188182161699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_18229969099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3134763004916529742787 : Nat.Prime 3134763004916529742787 := by
  have hfermat : (2 : ZMod 3134763004916529742787) ^ (3134763004916529742787 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 3134763004916529742787) ^ ((3134763004916529742787 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 3134763004916529742787) ^ ((3134763004916529742787 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 3134763004916529742787) ^ ((3134763004916529742787 - 1) / 45827) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 3134763004916529742787) ^ ((3134763004916529742787 - 1) / 261085043611289) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3134763004916529742787 (2 : ZMod 3134763004916529742787)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (131, 1), (45827, 1), (261085043611289, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (131, 1), (45827, 1), (261085043611289, 1)] : List FactorBlock).map factorBlockValue).prod = 3134763004916529742787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_261085043611289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_3740958109059732294463 : Nat.Prime 3740958109059732294463 := by
  have hfermat : (3 : ZMod 3740958109059732294463) ^ (3740958109059732294463 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 3740958109059732294463) ^ ((3740958109059732294463 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 3740958109059732294463) ^ ((3740958109059732294463 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 3740958109059732294463) ^ ((3740958109059732294463 - 1) / 29176943) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 3740958109059732294463) ^ ((3740958109059732294463 - 1) / 7123124792713) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3740958109059732294463 (3 : ZMod 3740958109059732294463)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (29176943, 1), (7123124792713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (29176943, 1), (7123124792713, 1)] : List FactorBlock).map factorBlockValue).prod = 3740958109059732294463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_29176943
      · exact prime_lucas_7123124792713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_3855659211768797360947 : Nat.Prime 3855659211768797360947 := by
  have hfermat : (2 : ZMod 3855659211768797360947) ^ (3855659211768797360947 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 3855659211768797360947) ^ ((3855659211768797360947 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 3855659211768797360947) ^ ((3855659211768797360947 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 3855659211768797360947) ^ ((3855659211768797360947 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 3855659211768797360947) ^ ((3855659211768797360947 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 3855659211768797360947) ^ ((3855659211768797360947 - 1) / 2557) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 3855659211768797360947) ^ ((3855659211768797360947 - 1) / 16657651522049) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3855659211768797360947 (2 : ZMod 3855659211768797360947)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (47, 1), (107, 1), (2557, 1), (16657651522049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (47, 1), (107, 1), (2557, 1), (16657651522049, 1)] : List FactorBlock).map factorBlockValue).prod = 3855659211768797360947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_16657651522049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_4392424760226720031979 : Nat.Prime 4392424760226720031979 := by
  have hfermat : (2 : ZMod 4392424760226720031979) ^ (4392424760226720031979 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 4392424760226720031979) ^ ((4392424760226720031979 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 4392424760226720031979) ^ ((4392424760226720031979 - 1) / 39251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 4392424760226720031979) ^ ((4392424760226720031979 - 1) / 1831079) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 4392424760226720031979) ^ ((4392424760226720031979 - 1) / 30557409041) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4392424760226720031979 (2 : ZMod 4392424760226720031979)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (39251, 1), (1831079, 1), (30557409041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (39251, 1), (1831079, 1), (30557409041, 1)] : List FactorBlock).map factorBlockValue).prod = 4392424760226720031979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_30557409041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_4838132325847044984233 : Nat.Prime 4838132325847044984233 := by
  have hfermat : (3 : ZMod 4838132325847044984233) ^ (4838132325847044984233 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 4838132325847044984233) ^ ((4838132325847044984233 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 4838132325847044984233) ^ ((4838132325847044984233 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 4838132325847044984233) ^ ((4838132325847044984233 - 1) / 401) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 4838132325847044984233) ^ ((4838132325847044984233 - 1) / 1747) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 4838132325847044984233) ^ ((4838132325847044984233 - 1) / 78479782841237) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4838132325847044984233 (3 : ZMod 4838132325847044984233)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (401, 1), (1747, 1), (78479782841237, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (401, 1), (1747, 1), (78479782841237, 1)] : List FactorBlock).map factorBlockValue).prod = 4838132325847044984233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_78479782841237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_4901429297023217652403 : Nat.Prime 4901429297023217652403 := by
  have hfermat : (2 : ZMod 4901429297023217652403) ^ (4901429297023217652403 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 4901429297023217652403) ^ ((4901429297023217652403 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 4901429297023217652403) ^ ((4901429297023217652403 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 4901429297023217652403) ^ ((4901429297023217652403 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 4901429297023217652403) ^ ((4901429297023217652403 - 1) / 43189) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 4901429297023217652403) ^ ((4901429297023217652403 - 1) / 122939) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 4901429297023217652403) ^ ((4901429297023217652403 - 1) / 617887373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4901429297023217652403 (2 : ZMod 4901429297023217652403)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (83, 1), (43189, 1), (122939, 1), (617887373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (83, 1), (43189, 1), (122939, 1), (617887373, 1)] : List FactorBlock).map factorBlockValue).prod = 4901429297023217652403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_617887373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_5606333954813291920861 : Nat.Prime 5606333954813291920861 := by
  have hfermat : (2 : ZMod 5606333954813291920861) ^ (5606333954813291920861 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 5606333954813291920861) ^ ((5606333954813291920861 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 5606333954813291920861) ^ ((5606333954813291920861 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 5606333954813291920861) ^ ((5606333954813291920861 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 5606333954813291920861) ^ ((5606333954813291920861 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 5606333954813291920861) ^ ((5606333954813291920861 - 1) / 631) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 5606333954813291920861) ^ ((5606333954813291920861 - 1) / 94771) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (2 : ZMod 5606333954813291920861) ^ ((5606333954813291920861 - 1) / 21404250797) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 5606333954813291920861 (2 : ZMod 5606333954813291920861)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (73, 1), (631, 1), (94771, 1), (21404250797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (73, 1), (631, 1), (94771, 1), (21404250797, 1)] : List FactorBlock).map factorBlockValue).prod = 5606333954813291920861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_21404250797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_5933184479296523639689 : Nat.Prime 5933184479296523639689 := by
  have hfermat : (17 : ZMod 5933184479296523639689) ^ (5933184479296523639689 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (17 : ZMod 5933184479296523639689) ^ ((5933184479296523639689 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (17 : ZMod 5933184479296523639689) ^ ((5933184479296523639689 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (17 : ZMod 5933184479296523639689) ^ ((5933184479296523639689 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (17 : ZMod 5933184479296523639689) ^ ((5933184479296523639689 - 1) / 686911) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (17 : ZMod 5933184479296523639689) ^ ((5933184479296523639689 - 1) / 3710260517861) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 5933184479296523639689 (17 : ZMod 5933184479296523639689)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (97, 1), (686911, 1), (3710260517861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (97, 1), (686911, 1), (3710260517861, 1)] : List FactorBlock).map factorBlockValue).prod = 5933184479296523639689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_3710260517861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_6752919537638392084861 : Nat.Prime 6752919537638392084861 := by
  have hfermat : (2 : ZMod 6752919537638392084861) ^ (6752919537638392084861 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 6752919537638392084861) ^ ((6752919537638392084861 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 6752919537638392084861) ^ ((6752919537638392084861 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 6752919537638392084861) ^ ((6752919537638392084861 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 6752919537638392084861) ^ ((6752919537638392084861 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 6752919537638392084861) ^ ((6752919537638392084861 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 6752919537638392084861) ^ ((6752919537638392084861 - 1) / 9588679) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (2 : ZMod 6752919537638392084861) ^ ((6752919537638392084861 - 1) / 30019592129) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6752919537638392084861 (2 : ZMod 6752919537638392084861)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (17, 1), (23, 1), (9588679, 1), (30019592129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (17, 1), (23, 1), (9588679, 1), (30019592129, 1)] : List FactorBlock).map factorBlockValue).prod = 6752919537638392084861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_30019592129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_8947878432260610334883 : Nat.Prime 8947878432260610334883 := by
  have hfermat : (2 : ZMod 8947878432260610334883) ^ (8947878432260610334883 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 8947878432260610334883) ^ ((8947878432260610334883 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 8947878432260610334883) ^ ((8947878432260610334883 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 8947878432260610334883) ^ ((8947878432260610334883 - 1) / 96059) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 8947878432260610334883) ^ ((8947878432260610334883 - 1) / 3582685333717423) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 8947878432260610334883 (2 : ZMod 8947878432260610334883)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (96059, 1), (3582685333717423, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (96059, 1), (3582685333717423, 1)] : List FactorBlock).map factorBlockValue).prod = 8947878432260610334883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_3582685333717423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_9064988419256124635339 : Nat.Prime 9064988419256124635339 := by
  have hfermat : (2 : ZMod 9064988419256124635339) ^ (9064988419256124635339 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 9064988419256124635339) ^ ((9064988419256124635339 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 9064988419256124635339) ^ ((9064988419256124635339 - 1) / 137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 9064988419256124635339) ^ ((9064988419256124635339 - 1) / 2897) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 9064988419256124635339) ^ ((9064988419256124635339 - 1) / 51803) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 9064988419256124635339) ^ ((9064988419256124635339 - 1) / 248867) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 9064988419256124635339) ^ ((9064988419256124635339 - 1) / 885821) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 9064988419256124635339 (2 : ZMod 9064988419256124635339)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (137, 1), (2897, 1), (51803, 1), (248867, 1), (885821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (137, 1), (2897, 1), (51803, 1), (248867, 1), (885821, 1)] : List FactorBlock).map factorBlockValue).prod = 9064988419256124635339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_11700081671881298012549 : Nat.Prime 11700081671881298012549 := by
  have hfermat : (2 : ZMod 11700081671881298012549) ^ (11700081671881298012549 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 11700081671881298012549) ^ ((11700081671881298012549 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 11700081671881298012549) ^ ((11700081671881298012549 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 11700081671881298012549) ^ ((11700081671881298012549 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 11700081671881298012549) ^ ((11700081671881298012549 - 1) / 257) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 11700081671881298012549) ^ ((11700081671881298012549 - 1) / 79397) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 11700081671881298012549) ^ ((11700081671881298012549 - 1) / 1861662541889) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11700081671881298012549 (2 : ZMod 11700081671881298012549)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (11, 1), (257, 1), (79397, 1), (1861662541889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (11, 1), (257, 1), (79397, 1), (1861662541889, 1)] : List FactorBlock).map factorBlockValue).prod = 11700081671881298012549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1861662541889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_14643932887768981485739 : Nat.Prime 14643932887768981485739 := by
  have hfermat : (3 : ZMod 14643932887768981485739) ^ (14643932887768981485739 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 14643932887768981485739) ^ ((14643932887768981485739 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 14643932887768981485739) ^ ((14643932887768981485739 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 14643932887768981485739) ^ ((14643932887768981485739 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 14643932887768981485739) ^ ((14643932887768981485739 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 14643932887768981485739) ^ ((14643932887768981485739 - 1) / 1789) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 14643932887768981485739) ^ ((14643932887768981485739 - 1) / 898128266586653) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 14643932887768981485739 (3 : ZMod 14643932887768981485739)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (31, 1), (1789, 1), (898128266586653, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (31, 1), (1789, 1), (898128266586653, 1)] : List FactorBlock).map factorBlockValue).prod = 14643932887768981485739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_898128266586653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_15204875355977603031317 : Nat.Prime 15204875355977603031317 := by
  have hfermat : (5 : ZMod 15204875355977603031317) ^ (15204875355977603031317 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 15204875355977603031317) ^ ((15204875355977603031317 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 15204875355977603031317) ^ ((15204875355977603031317 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 15204875355977603031317) ^ ((15204875355977603031317 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 15204875355977603031317) ^ ((15204875355977603031317 - 1) / 474899) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 15204875355977603031317) ^ ((15204875355977603031317 - 1) / 36886027359263) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 15204875355977603031317 (5 : ZMod 15204875355977603031317)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (31, 1), (474899, 1), (36886027359263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (31, 1), (474899, 1), (36886027359263, 1)] : List FactorBlock).map factorBlockValue).prod = 15204875355977603031317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_36886027359263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_58847542153734042263033 : Nat.Prime 58847542153734042263033 := by
  have hfermat : (3 : ZMod 58847542153734042263033) ^ (58847542153734042263033 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 58847542153734042263033) ^ ((58847542153734042263033 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 58847542153734042263033) ^ ((58847542153734042263033 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 58847542153734042263033) ^ ((58847542153734042263033 - 1) / 3331) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 58847542153734042263033) ^ ((58847542153734042263033 - 1) / 71236408413793739) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 58847542153734042263033 (3 : ZMod 58847542153734042263033)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (3331, 1), (71236408413793739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (3331, 1), (71236408413793739, 1)] : List FactorBlock).map factorBlockValue).prod = 58847542153734042263033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_71236408413793739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_61295201804601396750883 : Nat.Prime 61295201804601396750883 := by
  have hfermat : (2 : ZMod 61295201804601396750883) ^ (61295201804601396750883 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 61295201804601396750883) ^ ((61295201804601396750883 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 61295201804601396750883) ^ ((61295201804601396750883 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 61295201804601396750883) ^ ((61295201804601396750883 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 61295201804601396750883) ^ ((61295201804601396750883 - 1) / 173150287583619764833) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 61295201804601396750883 (2 : ZMod 61295201804601396750883)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (59, 1), (173150287583619764833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (59, 1), (173150287583619764833, 1)] : List FactorBlock).map factorBlockValue).prod = 61295201804601396750883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_173150287583619764833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_121163918812296127807631 : Nat.Prime 121163918812296127807631 := by
  have hfermat : (7 : ZMod 121163918812296127807631) ^ (121163918812296127807631 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 121163918812296127807631) ^ ((121163918812296127807631 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 121163918812296127807631) ^ ((121163918812296127807631 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 121163918812296127807631) ^ ((121163918812296127807631 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 121163918812296127807631) ^ ((121163918812296127807631 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 121163918812296127807631) ^ ((121163918812296127807631 - 1) / 2591) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (7 : ZMod 121163918812296127807631) ^ ((121163918812296127807631 - 1) / 5503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (7 : ZMod 121163918812296127807631) ^ ((121163918812296127807631 - 1) / 1274032631393) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 121163918812296127807631 (7 : ZMod 121163918812296127807631)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (23, 1), (29, 1), (2591, 1), (5503, 1), (1274032631393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (23, 1), (29, 1), (2591, 1), (5503, 1), (1274032631393, 1)] : List FactorBlock).map factorBlockValue).prod = 121163918812296127807631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1274032631393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_596495221862857490828087 : Nat.Prime 596495221862857490828087 := by
  have hfermat : (5 : ZMod 596495221862857490828087) ^ (596495221862857490828087 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 596495221862857490828087) ^ ((596495221862857490828087 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 596495221862857490828087) ^ ((596495221862857490828087 - 1) / 1487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 596495221862857490828087) ^ ((596495221862857490828087 - 1) / 289578043) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 596495221862857490828087) ^ ((596495221862857490828087 - 1) / 692628529423) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 596495221862857490828087 (5 : ZMod 596495221862857490828087)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1487, 1), (289578043, 1), (692628529423, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1487, 1), (289578043, 1), (692628529423, 1)] : List FactorBlock).map factorBlockValue).prod = 596495221862857490828087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_289578043
      · exact prime_lucas_692628529423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1198019952432569940913523 : Nat.Prime 1198019952432569940913523 := by
  have hfermat : (2 : ZMod 1198019952432569940913523) ^ (1198019952432569940913523 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1198019952432569940913523) ^ ((1198019952432569940913523 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1198019952432569940913523) ^ ((1198019952432569940913523 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1198019952432569940913523) ^ ((1198019952432569940913523 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1198019952432569940913523) ^ ((1198019952432569940913523 - 1) / 14321) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 1198019952432569940913523) ^ ((1198019952432569940913523 - 1) / 46839176590082237) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1198019952432569940913523 (2 : ZMod 1198019952432569940913523)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (47, 1), (14321, 1), (46839176590082237, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (47, 1), (14321, 1), (46839176590082237, 1)] : List FactorBlock).map factorBlockValue).prod = 1198019952432569940913523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_46839176590082237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1296844021166969686287133 : Nat.Prime 1296844021166969686287133 := by
  have hfermat : (2 : ZMod 1296844021166969686287133) ^ (1296844021166969686287133 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1296844021166969686287133) ^ ((1296844021166969686287133 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1296844021166969686287133) ^ ((1296844021166969686287133 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1296844021166969686287133) ^ ((1296844021166969686287133 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 1296844021166969686287133) ^ ((1296844021166969686287133 - 1) / 7867) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 1296844021166969686287133) ^ ((1296844021166969686287133 - 1) / 3298151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 1296844021166969686287133) ^ ((1296844021166969686287133 - 1) / 15958288253) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1296844021166969686287133 (2 : ZMod 1296844021166969686287133)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (29, 1), (7867, 1), (3298151, 1), (15958288253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (29, 1), (7867, 1), (3298151, 1), (15958288253, 1)] : List FactorBlock).map factorBlockValue).prod = 1296844021166969686287133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_15958288253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_1734288243527807766415493 : Nat.Prime 1734288243527807766415493 := by
  have hfermat : (2 : ZMod 1734288243527807766415493) ^ (1734288243527807766415493 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 1734288243527807766415493) ^ ((1734288243527807766415493 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 1734288243527807766415493) ^ ((1734288243527807766415493 - 1) / 2063539) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 1734288243527807766415493) ^ ((1734288243527807766415493 - 1) / 210110911827666907) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1734288243527807766415493 (2 : ZMod 1734288243527807766415493)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2063539, 1), (210110911827666907, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2063539, 1), (210110911827666907, 1)] : List FactorBlock).map factorBlockValue).prod = 1734288243527807766415493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_210110911827666907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_1789532831079186063691967 : Nat.Prime 1789532831079186063691967 := by
  have hfermat : (5 : ZMod 1789532831079186063691967) ^ (1789532831079186063691967 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 1789532831079186063691967) ^ ((1789532831079186063691967 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 1789532831079186063691967) ^ ((1789532831079186063691967 - 1) / 1495500161) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 1789532831079186063691967) ^ ((1789532831079186063691967 - 1) / 598305796865503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1789532831079186063691967 (5 : ZMod 1789532831079186063691967)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1495500161, 1), (598305796865503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1495500161, 1), (598305796865503, 1)] : List FactorBlock).map factorBlockValue).prod = 1789532831079186063691967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · exact prime_lucas_1495500161
      · exact prime_lucas_598305796865503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_1938664216816101517982849 : Nat.Prime 1938664216816101517982849 := by
  have hfermat : (6 : ZMod 1938664216816101517982849) ^ (1938664216816101517982849 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (6 : ZMod 1938664216816101517982849) ^ ((1938664216816101517982849 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (6 : ZMod 1938664216816101517982849) ^ ((1938664216816101517982849 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (6 : ZMod 1938664216816101517982849) ^ ((1938664216816101517982849 - 1) / 1553) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (6 : ZMod 1938664216816101517982849) ^ ((1938664216816101517982849 - 1) / 6963221) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (6 : ZMod 1938664216816101517982849) ^ ((1938664216816101517982849 - 1) / 200084271251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 1938664216816101517982849 (6 : ZMod 1938664216816101517982849)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (7, 1), (1553, 1), (6963221, 1), (200084271251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (7, 1), (1553, 1), (6963221, 1), (200084271251, 1)] : List FactorBlock).map factorBlockValue).prod = 1938664216816101517982849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_200084271251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_2540796806353896969568297 : Nat.Prime 2540796806353896969568297 := by
  have hfermat : (5 : ZMod 2540796806353896969568297) ^ (2540796806353896969568297 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 2540796806353896969568297) ^ ((2540796806353896969568297 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 2540796806353896969568297) ^ ((2540796806353896969568297 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 2540796806353896969568297) ^ ((2540796806353896969568297 - 1) / 223) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 2540796806353896969568297) ^ ((2540796806353896969568297 - 1) / 823) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 2540796806353896969568297) ^ ((2540796806353896969568297 - 1) / 630008983) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (5 : ZMod 2540796806353896969568297) ^ ((2540796806353896969568297 - 1) / 915603097) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2540796806353896969568297 (5 : ZMod 2540796806353896969568297)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (223, 1), (823, 1), (630008983, 1), (915603097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (223, 1), (823, 1), (630008983, 1), (915603097, 1)] : List FactorBlock).map factorBlockValue).prod = 2540796806353896969568297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_630008983
      · exact prime_lucas_915603097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_3132204323331386224451303 : Nat.Prime 3132204323331386224451303 := by
  have hfermat : (5 : ZMod 3132204323331386224451303) ^ (3132204323331386224451303 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 3132204323331386224451303) ^ ((3132204323331386224451303 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 3132204323331386224451303) ^ ((3132204323331386224451303 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 3132204323331386224451303) ^ ((3132204323331386224451303 - 1) / 15204875355977603031317) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3132204323331386224451303 (5 : ZMod 3132204323331386224451303)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (103, 1), (15204875355977603031317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (103, 1), (15204875355977603031317, 1)] : List FactorBlock).map factorBlockValue).prod = 3132204323331386224451303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_15204875355977603031317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_4750052844500425277240419 : Nat.Prime 4750052844500425277240419 := by
  have hfermat : (3 : ZMod 4750052844500425277240419) ^ (4750052844500425277240419 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 4750052844500425277240419) ^ ((4750052844500425277240419 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 4750052844500425277240419) ^ ((4750052844500425277240419 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 4750052844500425277240419) ^ ((4750052844500425277240419 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 4750052844500425277240419) ^ ((4750052844500425277240419 - 1) / 179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 4750052844500425277240419) ^ ((4750052844500425277240419 - 1) / 7800296316823861871) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 4750052844500425277240419 (3 : ZMod 4750052844500425277240419)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (7, 1), (179, 1), (7800296316823861871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (7, 1), (179, 1), (7800296316823861871, 1)] : List FactorBlock).map factorBlockValue).prod = 4750052844500425277240419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_7800296316823861871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_10349082993844929699929609 : Nat.Prime 10349082993844929699929609 := by
  have hfermat : (3 : ZMod 10349082993844929699929609) ^ (10349082993844929699929609 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 10349082993844929699929609) ^ ((10349082993844929699929609 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 10349082993844929699929609) ^ ((10349082993844929699929609 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 10349082993844929699929609) ^ ((10349082993844929699929609 - 1) / 709) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 10349082993844929699929609) ^ ((10349082993844929699929609 - 1) / 316051) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 10349082993844929699929609) ^ ((10349082993844929699929609 - 1) / 524826545839549) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 10349082993844929699929609 (3 : ZMod 10349082993844929699929609)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (709, 1), (316051, 1), (524826545839549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (709, 1), (316051, 1), (524826545839549, 1)] : List FactorBlock).map factorBlockValue).prod = 10349082993844929699929609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_524826545839549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_12009078416447709509287633 : Nat.Prime 12009078416447709509287633 := by
  have hfermat : (5 : ZMod 12009078416447709509287633) ^ (12009078416447709509287633 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 12009078416447709509287633) ^ ((12009078416447709509287633 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 12009078416447709509287633) ^ ((12009078416447709509287633 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 12009078416447709509287633) ^ ((12009078416447709509287633 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 12009078416447709509287633) ^ ((12009078416447709509287633 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 12009078416447709509287633) ^ ((12009078416447709509287633 - 1) / 1129) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (5 : ZMod 12009078416447709509287633) ^ ((12009078416447709509287633 - 1) / 284161) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (5 : ZMod 12009078416447709509287633) ^ ((12009078416447709509287633 - 1) / 87358364393) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12009078416447709509287633 (5 : ZMod 12009078416447709509287633)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (79, 1), (113, 1), (1129, 1), (284161, 1), (87358364393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (79, 1), (113, 1), (1129, 1), (284161, 1), (87358364393, 1)] : List FactorBlock).map factorBlockValue).prod = 12009078416447709509287633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_87358364393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_12269498332541680905090029 : Nat.Prime 12269498332541680905090029 := by
  have hfermat : (2 : ZMod 12269498332541680905090029) ^ (12269498332541680905090029 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 12269498332541680905090029) ^ ((12269498332541680905090029 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 12269498332541680905090029) ^ ((12269498332541680905090029 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 12269498332541680905090029) ^ ((12269498332541680905090029 - 1) / 683309107403746987363) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12269498332541680905090029 (2 : ZMod 12269498332541680905090029)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (67, 2), (683309107403746987363, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (67, 2), (683309107403746987363, 1)] : List FactorBlock).map factorBlockValue).prod = 12269498332541680905090029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_683309107403746987363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_12896756957813267978388347 : Nat.Prime 12896756957813267978388347 := by
  have hfermat : (2 : ZMod 12896756957813267978388347) ^ (12896756957813267978388347 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 12896756957813267978388347) ^ ((12896756957813267978388347 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 12896756957813267978388347) ^ ((12896756957813267978388347 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 12896756957813267978388347) ^ ((12896756957813267978388347 - 1) / 2333) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 12896756957813267978388347) ^ ((12896756957813267978388347 - 1) / 17183) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 12896756957813267978388347) ^ ((12896756957813267978388347 - 1) / 3923312791804327) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12896756957813267978388347 (2 : ZMod 12896756957813267978388347)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (2333, 1), (17183, 1), (3923312791804327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (2333, 1), (17183, 1), (3923312791804327, 1)] : List FactorBlock).map factorBlockValue).prod = 12896756957813267978388347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_3923312791804327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_12987683429232512202535043 : Nat.Prime 12987683429232512202535043 := by
  have hfermat : (2 : ZMod 12987683429232512202535043) ^ (12987683429232512202535043 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 12987683429232512202535043) ^ ((12987683429232512202535043 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 12987683429232512202535043) ^ ((12987683429232512202535043 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 12987683429232512202535043) ^ ((12987683429232512202535043 - 1) / 881) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 12987683429232512202535043) ^ ((12987683429232512202535043 - 1) / 535861) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 12987683429232512202535043) ^ ((12987683429232512202535043 - 1) / 259536097677977) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 12987683429232512202535043 (2 : ZMod 12987683429232512202535043)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (881, 1), (535861, 1), (259536097677977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (881, 1), (535861, 1), (259536097677977, 1)] : List FactorBlock).map factorBlockValue).prod = 12987683429232512202535043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_259536097677977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_21478275822909189783964541 : Nat.Prime 21478275822909189783964541 := by
  have hfermat : (2 : ZMod 21478275822909189783964541) ^ (21478275822909189783964541 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 21478275822909189783964541) ^ ((21478275822909189783964541 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 21478275822909189783964541) ^ ((21478275822909189783964541 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 21478275822909189783964541) ^ ((21478275822909189783964541 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 21478275822909189783964541) ^ ((21478275822909189783964541 - 1) / 2503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 21478275822909189783964541) ^ ((21478275822909189783964541 - 1) / 5707861) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 21478275822909189783964541) ^ ((21478275822909189783964541 - 1) / 3268190366503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 21478275822909189783964541 (2 : ZMod 21478275822909189783964541)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (23, 1), (2503, 1), (5707861, 1), (3268190366503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (23, 1), (2503, 1), (5707861, 1), (3268190366503, 1)] : List FactorBlock).map factorBlockValue).prod = 21478275822909189783964541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_3268190366503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_39379508443892166007089847 : Nat.Prime 39379508443892166007089847 := by
  have hfermat : (3 : ZMod 39379508443892166007089847) ^ (39379508443892166007089847 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 39379508443892166007089847) ^ ((39379508443892166007089847 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 39379508443892166007089847) ^ ((39379508443892166007089847 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 39379508443892166007089847) ^ ((39379508443892166007089847 - 1) / 632747) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 39379508443892166007089847) ^ ((39379508443892166007089847 - 1) / 10372631410840922203) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 39379508443892166007089847 (3 : ZMod 39379508443892166007089847)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (632747, 1), (10372631410840922203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (632747, 1), (10372631410840922203, 1)] : List FactorBlock).map factorBlockValue).prod = 39379508443892166007089847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_10372631410840922203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_41877811913766371622131233 : Nat.Prime 41877811913766371622131233 := by
  have hfermat : (5 : ZMod 41877811913766371622131233) ^ (41877811913766371622131233 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 41877811913766371622131233) ^ ((41877811913766371622131233 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 41877811913766371622131233) ^ ((41877811913766371622131233 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 41877811913766371622131233) ^ ((41877811913766371622131233 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 41877811913766371622131233) ^ ((41877811913766371622131233 - 1) / 4901429297023217652403) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 41877811913766371622131233 (5 : ZMod 41877811913766371622131233)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (89, 1), (4901429297023217652403, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (89, 1), (4901429297023217652403, 1)] : List FactorBlock).map factorBlockValue).prod = 41877811913766371622131233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_4901429297023217652403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_50614620597373221676205257 : Nat.Prime 50614620597373221676205257 := by
  have hfermat : (10 : ZMod 50614620597373221676205257) ^ (50614620597373221676205257 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (10 : ZMod 50614620597373221676205257) ^ ((50614620597373221676205257 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (10 : ZMod 50614620597373221676205257) ^ ((50614620597373221676205257 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (10 : ZMod 50614620597373221676205257) ^ ((50614620597373221676205257 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (10 : ZMod 50614620597373221676205257) ^ ((50614620597373221676205257 - 1) / 8753) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (10 : ZMod 50614620597373221676205257) ^ ((50614620597373221676205257 - 1) / 18533799619388085871) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 50614620597373221676205257 (10 : ZMod 50614620597373221676205257)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13, 1), (8753, 1), (18533799619388085871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13, 1), (8753, 1), (18533799619388085871, 1)] : List FactorBlock).map factorBlockValue).prod = 50614620597373221676205257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_18533799619388085871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_78935606611747974014211487 : Nat.Prime 78935606611747974014211487 := by
  have hfermat : (3 : ZMod 78935606611747974014211487) ^ (78935606611747974014211487 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 78935606611747974014211487) ^ ((78935606611747974014211487 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 78935606611747974014211487) ^ ((78935606611747974014211487 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 78935606611747974014211487) ^ ((78935606611747974014211487 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 78935606611747974014211487) ^ ((78935606611747974014211487 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 78935606611747974014211487) ^ ((78935606611747974014211487 - 1) / 229047163) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (3 : ZMod 78935606611747974014211487) ^ ((78935606611747974014211487 - 1) / 5334602577361) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 78935606611747974014211487 (3 : ZMod 78935606611747974014211487)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (37, 1), (97, 1), (229047163, 1), (5334602577361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (37, 1), (97, 1), (229047163, 1), (5334602577361, 1)] : List FactorBlock).map factorBlockValue).prod = 78935606611747974014211487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_229047163
      · exact prime_lucas_5334602577361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_98644933044693763291732537 : Nat.Prime 98644933044693763291732537 := by
  have hfermat : (7 : ZMod 98644933044693763291732537) ^ (98644933044693763291732537 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (7 : ZMod 98644933044693763291732537) ^ ((98644933044693763291732537 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (7 : ZMod 98644933044693763291732537) ^ ((98644933044693763291732537 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (7 : ZMod 98644933044693763291732537) ^ ((98644933044693763291732537 - 1) / 337153) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (7 : ZMod 98644933044693763291732537) ^ ((98644933044693763291732537 - 1) / 2512021) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (7 : ZMod 98644933044693763291732537) ^ ((98644933044693763291732537 - 1) / 1617677674451) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 98644933044693763291732537 (7 : ZMod 98644933044693763291732537)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (337153, 1), (2512021, 1), (1617677674451, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (337153, 1), (2512021, 1), (1617677674451, 1)] : List FactorBlock).map factorBlockValue).prod = 98644933044693763291732537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1617677674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_165369271889121277501589201 : Nat.Prime 165369271889121277501589201 := by
  have hfermat : (3 : ZMod 165369271889121277501589201) ^ (165369271889121277501589201 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 165369271889121277501589201) ^ ((165369271889121277501589201 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 165369271889121277501589201) ^ ((165369271889121277501589201 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 165369271889121277501589201) ^ ((165369271889121277501589201 - 1) / 1100483) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 165369271889121277501589201) ^ ((165369271889121277501589201 - 1) / 375674299123933031) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 165369271889121277501589201 (3 : ZMod 165369271889121277501589201)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 2), (1100483, 1), (375674299123933031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 2), (1100483, 1), (375674299123933031, 1)] : List FactorBlock).map factorBlockValue).prod = 165369271889121277501589201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_375674299123933031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_800120012473627191144052801 : Nat.Prime 800120012473627191144052801 := by
  have hfermat : (22 : ZMod 800120012473627191144052801) ^ (800120012473627191144052801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (22 : ZMod 800120012473627191144052801) ^ ((800120012473627191144052801 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 800120012473627191144052801 (22 : ZMod 800120012473627191144052801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 800120012473627191144052801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
theorem prime_lucas_825123762863428040867304451 : Nat.Prime 825123762863428040867304451 := by
  have hfermat : (12 : ZMod 825123762863428040867304451) ^ (825123762863428040867304451 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (12 : ZMod 825123762863428040867304451) ^ ((825123762863428040867304451 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 825123762863428040867304451 (12 : ZMod 825123762863428040867304451)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 825123762863428040867304451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_851740658439667655088830401 : Nat.Prime 851740658439667655088830401 := by
  have hfermat : (31 : ZMod 851740658439667655088830401) ^ (851740658439667655088830401 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (31 : ZMod 851740658439667655088830401) ^ ((851740658439667655088830401 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 851740658439667655088830401 (31 : ZMod 851740658439667655088830401)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 851740658439667655088830401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
theorem prime_lucas_880132013720989910258458081 : Nat.Prime 880132013720989910258458081 := by
  have hfermat : (71 : ZMod 880132013720989910258458081) ^ (880132013720989910258458081 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (71 : ZMod 880132013720989910258458081) ^ ((880132013720989910258458081 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 880132013720989910258458081 (71 : ZMod 880132013720989910258458081)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 880132013720989910258458081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_910481393504472320957025601 : Nat.Prime 910481393504472320957025601 := by
  have hfermat : (58 : ZMod 910481393504472320957025601) ^ (910481393504472320957025601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (58 : ZMod 910481393504472320957025601) ^ ((910481393504472320957025601 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 910481393504472320957025601 (58 : ZMod 910481393504472320957025601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 910481393504472320957025601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
theorem prime_lucas_990148515436113649040765341 : Nat.Prime 990148515436113649040765341 := by
  have hfermat : (2 : ZMod 990148515436113649040765341) ^ (990148515436113649040765341 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (2 : ZMod 990148515436113649040765341) ^ ((990148515436113649040765341 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 990148515436113649040765341 (2 : ZMod 990148515436113649040765341)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 990148515436113649040765341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_2514662896345685457881308801 : Nat.Prime 2514662896345685457881308801 := by
  have hfermat : (71 : ZMod 2514662896345685457881308801) ^ (2514662896345685457881308801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (71 : ZMod 2514662896345685457881308801) ^ ((2514662896345685457881308801 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 2514662896345685457881308801 (71 : ZMod 2514662896345685457881308801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 2514662896345685457881308801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_3106348283721140859735734401 : Nat.Prime 3106348283721140859735734401 := by
  have hfermat : (17 : ZMod 3106348283721140859735734401) ^ (3106348283721140859735734401 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (17 : ZMod 3106348283721140859735734401) ^ ((3106348283721140859735734401 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3106348283721140859735734401 (17 : ZMod 3106348283721140859735734401)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 3106348283721140859735734401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
theorem prime_lucas_3771994344518528186821963201 : Nat.Prime 3771994344518528186821963201 := by
  have hfermat : (97 : ZMod 3771994344518528186821963201) ^ (3771994344518528186821963201 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (97 : ZMod 3771994344518528186821963201) ^ ((3771994344518528186821963201 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 3771994344518528186821963201 (97 : ZMod 3771994344518528186821963201)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 3771994344518528186821963201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_5462888361026833925742153601 : Nat.Prime 5462888361026833925742153601 := by
  have hfermat : (79 : ZMod 5462888361026833925742153601) ^ (5462888361026833925742153601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (79 : ZMod 5462888361026833925742153601) ^ ((5462888361026833925742153601 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 5462888361026833925742153601 (79 : ZMod 5462888361026833925742153601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 5462888361026833925742153601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
theorem prime_lucas_6093221633453007071020094401 : Nat.Prime 6093221633453007071020094401 := by
  have hfermat : (71 : ZMod 6093221633453007071020094401) ^ (6093221633453007071020094401 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (71 : ZMod 6093221633453007071020094401) ^ ((6093221633453007071020094401 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6093221633453007071020094401 (71 : ZMod 6093221633453007071020094401)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 6093221633453007071020094401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
theorem prime_lucas_6600990102907424326938435601 : Nat.Prime 6600990102907424326938435601 := by
  have hfermat : (71 : ZMod 6600990102907424326938435601) ^ (6600990102907424326938435601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (71 : ZMod 6600990102907424326938435601) ^ ((6600990102907424326938435601 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6600990102907424326938435601 (71 : ZMod 6600990102907424326938435601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 6600990102907424326938435601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_6887989672599051471587932801 : Nat.Prime 6887989672599051471587932801 := by
  have hfermat : (23 : ZMod 6887989672599051471587932801) ^ (6887989672599051471587932801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (23 : ZMod 6887989672599051471587932801) ^ ((6887989672599051471587932801 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 6887989672599051471587932801 (23 : ZMod 6887989672599051471587932801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 6887989672599051471587932801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
theorem prime_lucas_7921188123488909192326122721 : Nat.Prime 7921188123488909192326122721 := by
  have hfermat : (71 : ZMod 7921188123488909192326122721) ^ (7921188123488909192326122721 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (71 : ZMod 7921188123488909192326122721) ^ ((7921188123488909192326122721 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 7921188123488909192326122721 (71 : ZMod 7921188123488909192326122721)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 7921188123488909192326122721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_11315983033555584560465889601 : Nat.Prime 11315983033555584560465889601 := by
  have hfermat : (71 : ZMod 11315983033555584560465889601) ^ (11315983033555584560465889601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (71 : ZMod 11315983033555584560465889601) ^ ((11315983033555584560465889601 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 11315983033555584560465889601 (71 : ZMod 11315983033555584560465889601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 11315983033555584560465889601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_13201980205814848653876871201 : Nat.Prime 13201980205814848653876871201 := by
  have hfermat : (89 : ZMod 13201980205814848653876871201) ^ (13201980205814848653876871201 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (89 : ZMod 13201980205814848653876871201) ^ ((13201980205814848653876871201 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 13201980205814848653876871201 (89 : ZMod 13201980205814848653876871201)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 13201980205814848653876871201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_52807920823259394615507484801 : Nat.Prime 52807920823259394615507484801 := by
  have hfermat : (89 : ZMod 52807920823259394615507484801) ^ (52807920823259394615507484801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_7 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_8 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_9 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_10 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_11 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_12 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_13 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_14 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_15 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_16 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_17 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_18 : (89 : ZMod 52807920823259394615507484801) ^ ((52807920823259394615507484801 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 52807920823259394615507484801 (89 : ZMod 52807920823259394615507484801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod = 52807920823259394615507484801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17
    · exact hfactor_18
theorem prime_lucas_79211881234889091923261227273 : Nat.Prime 79211881234889091923261227273 := by
  have hfermat : (10 : ZMod 79211881234889091923261227273) ^ (79211881234889091923261227273 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (10 : ZMod 79211881234889091923261227273) ^ ((79211881234889091923261227273 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (10 : ZMod 79211881234889091923261227273) ^ ((79211881234889091923261227273 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (10 : ZMod 79211881234889091923261227273) ^ ((79211881234889091923261227273 - 1) / 433) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (10 : ZMod 79211881234889091923261227273) ^ ((79211881234889091923261227273 - 1) / 2540796806353896969568297) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 79211881234889091923261227273 (10 : ZMod 79211881234889091923261227273)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (433, 1), (2540796806353896969568297, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (433, 1), (2540796806353896969568297, 1)] : List FactorBlock).map factorBlockValue).prod = 79211881234889091923261227273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_2540796806353896969568297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_158423762469778183846522454473 : Nat.Prime 158423762469778183846522454473 := by
  have hfermat : (5 : ZMod 158423762469778183846522454473) ^ (158423762469778183846522454473 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (5 : ZMod 158423762469778183846522454473) ^ ((158423762469778183846522454473 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (5 : ZMod 158423762469778183846522454473) ^ ((158423762469778183846522454473 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (5 : ZMod 158423762469778183846522454473) ^ ((158423762469778183846522454473 - 1) / 359) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (5 : ZMod 158423762469778183846522454473) ^ ((158423762469778183846522454473 - 1) / 50077) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (5 : ZMod 158423762469778183846522454473) ^ ((158423762469778183846522454473 - 1) / 214891) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (5 : ZMod 158423762469778183846522454473) ^ ((158423762469778183846522454473 - 1) / 3422179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_6 : (5 : ZMod 158423762469778183846522454473) ^ ((158423762469778183846522454473 - 1) / 166430963) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 158423762469778183846522454473 (5 : ZMod 158423762469778183846522454473)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (359, 1), (50077, 1), (214891, 1), (3422179, 1), (166430963, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (359, 1), (50077, 1), (214891, 1), (3422179, 1), (166430963, 1)] : List FactorBlock).map factorBlockValue).prod = 158423762469778183846522454473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_166430963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_158423762469778183846522454479 : Nat.Prime 158423762469778183846522454479 := by
  have hfermat : (3 : ZMod 158423762469778183846522454479) ^ (158423762469778183846522454479 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (3 : ZMod 158423762469778183846522454479) ^ ((158423762469778183846522454479 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (3 : ZMod 158423762469778183846522454479) ^ ((158423762469778183846522454479 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (3 : ZMod 158423762469778183846522454479) ^ ((158423762469778183846522454479 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (3 : ZMod 158423762469778183846522454479) ^ ((158423762469778183846522454479 - 1) / 2545013) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (3 : ZMod 158423762469778183846522454479) ^ ((158423762469778183846522454479 - 1) / 798060315533818107677) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 158423762469778183846522454479 (3 : ZMod 158423762469778183846522454479)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (2545013, 1), (798060315533818107677, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (2545013, 1), (798060315533818107677, 1)] : List FactorBlock).map factorBlockValue).prod = 158423762469778183846522454479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_798060315533818107677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_158423762469778183846522454497 : Nat.Prime 158423762469778183846522454497 := by
  have hfermat : (13 : ZMod 158423762469778183846522454497) ^ (158423762469778183846522454497 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff']
    decide +kernel
  have hfactor_0 : (13 : ZMod 158423762469778183846522454497) ^ ((158423762469778183846522454497 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_1 : (13 : ZMod 158423762469778183846522454497) ^ ((158423762469778183846522454497 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_2 : (13 : ZMod 158423762469778183846522454497) ^ ((158423762469778183846522454497 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_3 : (13 : ZMod 158423762469778183846522454497) ^ ((158423762469778183846522454497 - 1) / 239) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_4 : (13 : ZMod 158423762469778183846522454497) ^ ((158423762469778183846522454497 - 1) / 2221) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  have hfactor_5 : (13 : ZMod 158423762469778183846522454497) ^ ((158423762469778183846522454497 - 1) / 43786908338927870449) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff']
    decide +kernel
  apply lucas_primality 158423762469778183846522454497 (13 : ZMod 158423762469778183846522454497)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (71, 1), (239, 1), (2221, 1), (43786908338927870449, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (71, 1), (239, 1), (2221, 1), (43786908338927870449, 1)] : List FactorBlock).map factorBlockValue).prod = 158423762469778183846522454497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_43786908338927870449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
/-! ## 3. Exact totients of the 200 window integers -/

private theorem phi67_79211881234889091923261227201 : Nat.totient 79211881234889091923261227201 = 79211881234878182185049052804 := by
  rw [← show ((([(7265496855919, 1), (10902472715318479, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_7265496855919, prime_lucas_10902472715318479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227202 : Nat.totient 79211881234889091923261227202 = 39605940617348386264034506032 := by
  rw [← show ((([(2, 1), (411878481853, 1), (96159285717625717, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_lucas_411878481853, prime_lucas_96159285717625717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227203 : Nat.totient 79211881234889091923261227203 = 52602441524179268066197211136 := by
  rw [← show ((([(3, 1), (257, 1), (52188119, 1), (1968630936296891047, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_257, prime_lucas_52188119, prime_lucas_1968630936296891047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227204 : Nat.totient 79211881234889091923261227204 = 39605922721687681440405517544 := by
  rw [← show ((([(2, 2), (2213147, 1), (8947878432260610334883, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_2213147, prime_lucas_8947878432260610334883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227205 : Nat.totient 79211881234889091923261227205 = 63167046505521780651904159488 := by
  rw [← show ((([(5, 1), (313, 1), (50614620597373221676205257, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_313, prime_lucas_50614620597373221676205257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227206 : Nat.totient 79211881234889091923261227206 = 26403960411629697307753742400 := by
  rw [← show ((([(2, 1), (3, 1), (13201980205814848653876871201, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_lucas_13201980205814848653876871201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227207 : Nat.totient 79211881234889091923261227207 = 67895898201333507362795337600 := by
  rw [← show ((([(7, 1), (11315983033555584560465889601, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_7, prime_lucas_11315983033555584560465889601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227208 : Nat.totient 79211881234889091923261227208 = 39520027514152909202494753600 := by
  rw [← show ((([(2, 3), (461, 1), (21478275822909189783964541, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_461, prime_lucas_21478275822909189783964541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227209 : Nat.totient 79211881234889091923261227209 = 52807917044365058961014475552 := by
  rw [← show ((([(3, 2), (13974437, 1), (629815722609068193773, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_lucas_13974437, prime_lucas_629815722609068193773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227210 : Nat.totient 79211881234889091923261227210 = 31684752493955636769304490880 := by
  rw [← show ((([(2, 1), (5, 1), (7921188123488909192326122721, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_lucas_7921188123488909192326122721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227211 : Nat.totient 79211881234889091923261227211 = 71024351792179509570047425920 := by
  rw [← show ((([(11, 1), (73, 1), (98644933044693763291732537, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_11, prime_small_73, prime_lucas_98644933044693763291732537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227212 : Nat.totient 79211881234889091923261227212 = 26403960411629697307753742400 := by
  rw [← show ((([(2, 2), (3, 1), (6600990102907424326938435601, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_lucas_6600990102907424326938435601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227213 : Nat.totient 79211881234889091923261227213 = 73118659601436084852241132800 := by
  rw [← show ((([(13, 1), (6093221633453007071020094401, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_13, prime_lucas_6093221633453007071020094401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227214 : Nat.totient 79211881234889091923261227214 = 33873664746621231642329742528 := by
  rw [← show ((([(2, 1), (7, 1), (457, 1), (22174564067, 1), (558330047988179, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_7, prime_small_457, prime_lucas_22174564067, prime_lucas_558330047988179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227215 : Nat.totient 79211881234889091923261227215 = 41722489596920327072696843264 := by
  rw [← show ((([(3, 1), (5, 1), (179, 1), (233, 1), (389, 1), (325492147189753087847, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_5, prime_small_179, prime_small_233, prime_small_389, prime_lucas_325492147189753087847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227216 : Nat.totient 79211881234889091923261227216 = 39605940143987604260882314496 := by
  rw [← show ((([(2, 4), (83652677, 1), (59182117712509884713, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_lucas_83652677, prime_lucas_59182117712509884713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227217 : Nat.totient 79211881234889091923261227217 = 74552341711777761492257882112 := by
  rw [← show ((([(17, 1), (4360417, 1), (1068595601196333123553, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_17, prime_small_4360417, prime_lucas_1068595601196333123553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227218 : Nat.totient 79211881234889091923261227218 = 26303330273374717262738438400 := by
  rw [← show ((([(2, 1), (3, 2), (281, 1), (3947, 1), (582470173, 1), (6811937979991, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_281, prime_small_3947, prime_lucas_582470173, prime_lucas_6811937979991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227219 : Nat.totient 79211881234889091923261227219 = 74876416766174725698627279360 := by
  rw [← show ((([(19, 1), (593, 1), (1879, 1), (8248945261, 1), (453583065203, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_19, prime_small_593, prime_small_1879, prime_lucas_8248945261, prime_lucas_453583065203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227220 : Nat.totient 79211881234889091923261227220 = 31684698470599335662163120000 := by
  rw [← show ((([(2, 2), (5, 1), (586501, 1), (6752919537638392084861, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_586501, prime_lucas_6752919537638392084861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227221 : Nat.totient 79211881234889091923261227221 = 45263932134222338241863558400 := by
  rw [← show ((([(3, 1), (7, 1), (3771994344518528186821963201, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_7, prime_lucas_3771994344518528186821963201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227222 : Nat.totient 79211881234889091923261227222 = 36005400549372784991613694920 := by
  rw [← show ((([(2, 1), (11, 1), (3015416923, 1), (1194043857971451187, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_11, prime_lucas_3015416923, prime_lucas_1194043857971451187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227223 : Nat.totient 79211881234889091923261227223 = 75516289204715681899790653440 := by
  rw [← show ((([(23, 1), (331, 1), (3329, 1), (3125508632188182161699, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_23, prime_small_331, prime_small_3329, prime_lucas_3125508632188182161699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227224 : Nat.totient 79211881234889091923261227224 = 26305804424969363860513020032 := by
  rw [← show ((([(2, 3), (3, 1), (269, 1), (12269498332541680905090029, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_269, prime_lucas_12269498332541680905090029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227225 : Nat.totient 79211881234889091923261227225 = 63367816164564638991029207040 := by
  rw [← show ((([(5, 2), (42209, 1), (337969, 1), (222110141675359409, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_42209, prime_small_337969, prime_lucas_222110141675359409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227226 : Nat.totient 79211881234889091923261227226 = 35987295844540782503163601920 := by
  rw [← show ((([(2, 1), (13, 1), (113, 1), (163, 1), (1427, 1), (37591, 1), (3083493800933647, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_13, prime_small_113, prime_small_163, prime_small_1427, prime_small_37591, prime_lucas_3083493800933647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227227 : Nat.totient 79211881234889091923261227227 = 52807920020157696732404467200 := by
  rw [← show ((([(3, 3), (65754961, 1), (44616760993439968241, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_lucas_65754961, prime_lucas_44616760993439968241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227228 : Nat.totient 79211881234889091923261227228 = 33720613204158028081613661696 := by
  rw [← show ((([(2, 2), (7, 1), (157, 1), (3037, 1), (5933184479296523639689, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_7, prime_small_157, prime_small_3037, prime_lucas_5933184479296523639689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227229 : Nat.totient 79211881234889091923261227229 = 75129017183007728150419372800 := by
  rw [← show ((([(29, 1), (79, 1), (197, 1), (42879077, 1), (4093111581118951, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_29, prime_small_79, prime_small_197, prime_lucas_42879077, prime_lucas_4093111581118951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227230 : Nat.totient 79211881234889091923261227230 = 20900194203683569266697089024 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (109, 1), (1213, 1), (1753, 1), (771186739, 1), (14772034219, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_5, prime_small_109, prime_small_1213, prime_small_1753, prime_lucas_771186739, prime_lucas_14772034219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227231 : Nat.totient 79211881234889091923261227231 = 76652209164623322154850835840 := by
  rw [← show ((([(31, 1), (19973, 1), (161059, 1), (562997, 1), (1410893565619, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_31, prime_small_19973, prime_small_161059, prime_small_562997, prime_lucas_1410893565619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227232 : Nat.totient 79211881234889091923261227232 = 39457029805691431069132308480 := by
  rw [← show ((([(2, 5), (317, 1), (1721, 1), (38333, 1), (47080037, 1), (2514146683, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_317, prime_small_1721, prime_small_38333, prime_lucas_47080037, prime_lucas_2514146683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227233 : Nat.totient 79211881234889091923261227233 = 48006236244726474448068419040 := by
  rw [← show ((([(3, 1), (11, 2), (49783, 1), (275131919, 1), (15931683165883, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_11, prime_small_49783, prime_lucas_275131919, prime_lucas_15931683165883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227234 : Nat.totient 79211881234889091923261227234 = 37027131766326136446610444800 := by
  rw [← show ((([(2, 1), (17, 1), (151, 1), (16943, 1), (910634610394437306857, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_17, prime_small_151, prime_small_16943, prime_lucas_910634610394437306857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227235 : Nat.totient 79211881234889091923261227235 = 54315267869889632327597136000 := by
  rw [← show ((([(5, 1), (7, 1), (38261, 1), (1749031, 1), (33819599447151131, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_7, prime_small_38261, prime_small_1749031, prime_lucas_33819599447151131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227236 : Nat.totient 79211881234889091923261227236 = 26329755598114178928835203840 := by
  rw [← show ((([(2, 2), (3, 2), (359, 1), (50077, 1), (214891, 1), (3422179, 1), (166430963, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_359, prime_small_50077, prime_small_214891, prime_small_3422179, prime_lucas_166430963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227237 : Nat.totient 79211881234889091923261227237 = 77027890861604516920975810512 := by
  rw [← show ((([(37, 1), (1787, 1), (1198019952432569940913523, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_37, prime_small_1787, prime_lucas_1198019952432569940913523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227238 : Nat.totient 79211881234889091923261227238 = 37521267173122844946883819680 := by
  rw [← show ((([(2, 1), (19, 1), (252029, 1), (27257491, 1), (303438258668759, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_19, prime_small_252029, prime_lucas_27257491, prime_lucas_303438258668759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227239 : Nat.totient 79211881234889091923261227239 = 48745753914176483756465090688 := by
  rw [← show ((([(3, 1), (13, 1), (2545013, 1), (798060315533818107677, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_13, prime_small_2545013, prime_lucas_798060315533818107677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227240 : Nat.totient 79211881234889091923261227240 = 31333939599837944565987778560 := by
  rw [← show ((([(2, 3), (5, 1), (131, 2), (293, 1), (19213, 1), (20498634974645969, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_131, prime_small_293, prime_small_19213, prime_lucas_20498634974645969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227241 : Nat.totient 79211881234889091923261227241 = 77267094474341132433070817280 := by
  rw [← show ((([(41, 1), (6073, 1), (1197953, 1), (265560458835600329, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_41, prime_small_6073, prime_small_1197953, prime_lucas_265560458835600329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227242 : Nat.totient 79211881234889091923261227242 = 22630534841524038639121679040 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (16763, 1), (279007, 1), (403249829858894861, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_7, prime_small_16763, prime_small_279007, prime_lucas_403249829858894861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227243 : Nat.totient 79211881234889091923261227243 = 77369744416261309888619525544 := by
  rw [← show ((([(43, 1), (1692126367, 1), (1088652011356783903, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_43, prime_lucas_1692126367, prime_lucas_1088652011356783903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227244 : Nat.totient 79211881234889091923261227244 = 35910399504423215095937560080 := by
  rw [← show ((([(2, 2), (11, 1), (379, 1), (4750052844500425277240419, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_11, prime_small_379, prime_lucas_4750052844500425277240419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227245 : Nat.totient 79211881234889091923261227245 = 42246336652734701345680428000 := by
  rw [← show ((([(3, 2), (5, 1), (7193542211, 1), (244700590586689451, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_5, prime_lucas_7193542211, prime_lucas_244700590586689451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227246 : Nat.totient 79211881234889091923261227246 = 37883874234508674930067204024 := by
  rw [← show ((([(2, 1), (23, 1), (549323, 1), (3134763004916529742787, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_23, prime_small_549323, prime_lucas_3134763004916529742787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227247 : Nat.totient 79211881234889091923261227247 = 77184917666096749984032903520 := by
  rw [← show ((([(47, 1), (227, 1), (1067879, 1), (13818191, 1), (503145247667, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_47, prime_small_227, prime_small_1067879, prime_lucas_13818191, prime_lucas_503145247667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227248 : Nat.totient 79211881234889091923261227248 = 25911480996750641185493913600 := by
  rw [← show ((([(2, 4), (3, 1), (71, 1), (239, 1), (2221, 1), (43786908338927870449, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_71, prime_small_239, prime_small_2221, prime_lucas_43786908338927870449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227249 : Nat.totient 79211881234889091923261227249 = 67513938896482290576048029184 := by
  rw [← show ((([(7, 2), (193, 1), (2239, 1), (3740958109059732294463, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_7, prime_small_193, prime_small_2239, prime_lucas_3740958109059732294463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227250 : Nat.totient 79211881234889091923261227250 = 31370768718950110030244352000 := by
  rw [← show ((([(2, 1), (5, 3), (173, 1), (241, 1), (274403, 1), (3673367, 1), (7539351613, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_173, prime_small_241, prime_small_274403, prime_small_3673367, prime_lucas_7539351613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227251 : Nat.totient 79211881234889091923261227251 = 49701198136924753554231100928 := by
  rw [← show ((([(3, 1), (17, 1), (132749, 1), (11700081671881298012549, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_17, prime_small_132749, prime_lucas_11700081671881298012549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227252 : Nat.totient 79211881234889091923261227252 = 36558126835043970561334469280 := by
  rw [← show ((([(2, 2), (13, 2), (30391, 1), (3855659211768797360947, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_13, prime_small_30391, prime_lucas_3855659211768797360947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227253 : Nat.totient 79211881234889091923261227253 = 77578739843816636663351592960 := by
  rw [← show ((([(53, 1), (1091, 1), (1153, 1), (1188120256076643679787, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_53, prime_small_1091, prime_small_1153, prime_lucas_1188120256076643679787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227254 : Nat.totient 79211881234889091923261227254 = 26386733119420722611228126976 := by
  rw [← show ((([(2, 1), (3, 4), (1549, 1), (166319, 1), (1155829, 1), (1642057812533, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_1549, prime_small_166319, prime_small_1155829, prime_lucas_1642057812533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227255 : Nat.totient 79211881234889091923261227255 = 57608631373430993162377728000 := by
  rw [← show ((([(5, 1), (11, 1), (10700387, 1), (13912193, 1), (9674589779851, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_11, prime_lucas_10700387, prime_lucas_13912193, prime_lucas_9674589779851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227256 : Nat.totient 79211881234889091923261227256 = 33876431368001995493689920000 := by
  rw [← show ((([(2, 3), (7, 1), (491, 1), (14251, 1), (2620303549, 1), (77147856389, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_7, prime_small_491, prime_small_14251, prime_lucas_2620303549, prime_lucas_77147856389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227257 : Nat.totient 79211881234889091923261227257 = 49560999965951266564873720272 := by
  rw [← show ((([(3, 1), (19, 1), (107, 1), (12987683429232512202535043, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_19, prime_small_107, prime_lucas_12987683429232512202535043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227258 : Nat.totient 79211881234889091923261227258 = 38239964707512098308701067312 := by
  rw [← show ((([(2, 1), (29, 1), (150659, 1), (9064988419256124635339, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_29, prime_small_150659, prime_lucas_9064988419256124635339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227259 : Nat.totient 79211881234889091923261227259 = 77280021627814075720874194944 := by
  rw [← show ((([(59, 1), (139, 1), (2659, 1), (11335084337, 1), (320464865873, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_59, prime_small_139, prime_small_2659, prime_lucas_11335084337, prime_lucas_320464865873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227260 : Nat.totient 79211881234889091923261227260 = 20956811666111160097112064000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (127, 1), (644977, 1), (3174366751, 1), (5077314049, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_5, prime_small_127, prime_small_644977, prime_lucas_3174366751, prime_lucas_5077314049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227261 : Nat.totient 79211881234889091923261227261 = 77913325804801143127509138240 := by
  rw [← show ((([(61, 1), (10903801029829, 1), (119091996133069, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_61, prime_lucas_10903801029829, prime_lucas_119091996133069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227262 : Nat.totient 79211881234889091923261227262 = 38307253547944071300298199040 := by
  rw [← show ((([(2, 1), (31, 1), (2833, 1), (5077, 1), (368419669, 1), (241102710169, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_31, prime_small_2833, prime_small_5077, prime_lucas_368419669, prime_lucas_241102710169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227263 : Nat.totient 79211881234889091923261227263 = 45243207536440407213868948800 := by
  rw [← show ((([(3, 2), (7, 1), (2339, 1), (37511, 1), (271571, 1), (52768837020239, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_7, prime_small_2339, prime_small_37511, prime_small_271571, prime_lucas_52768837020239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227264 : Nat.totient 79211881234889091923261227264 = 39213802588768833173864448000 := by
  rw [← show ((([(2, 8), (101, 1), (14206672321, 1), (215643625631789, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_101, prime_lucas_14206672321, prime_lucas_215643625631789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227265 : Nat.totient 79211881234889091923261227265 = 58487307417490599764666726400 := by
  rw [← show ((([(5, 1), (13, 1), (15971, 1), (19727, 1), (58921, 1), (65646822185533, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_13, prime_small_15971, prime_small_19727, prime_small_58921, prime_lucas_65646822185533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227266 : Nat.totient 79211881234889091923261227266 = 24002027682354043008764098560 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (15277, 1), (16360037, 1), (4802020745398049, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_11, prime_small_15277, prime_lucas_16360037, prime_lucas_4802020745398049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227267 : Nat.totient 79211881234889091923261227267 = 77256618638317512207064428672 := by
  rw [← show ((([(67, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_67, prime_small_103, prime_small_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227268 : Nat.totient 79211881234889091923261227268 = 36891888895327363612531605504 := by
  rw [← show ((([(2, 2), (17, 1), (97, 1), (12009078416447709509287633, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_17, prime_small_97, prime_lucas_12009078416447709509287633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227269 : Nat.totient 79211881234889091923261227269 = 50480616671410815699249508992 := by
  rw [← show ((([(3, 1), (23, 1), (2297, 1), (5419, 1), (92227638942914506907, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_23, prime_small_2297, prime_small_5419, prime_lucas_92227638942914506907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227270 : Nat.totient 79211881234889091923261227270 = 27158359278048077051907451008 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (10927485293, 1), (103555234622959877, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_7, prime_lucas_10927485293, prime_lucas_103555234622959877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227271 : Nat.totient 79211881234889091923261227271 = 79179268891805884202863271040 := by
  rw [← show ((([(2633, 1), (31321, 1), (960514331081427865447, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2633, prime_small_31321, prime_lucas_960514331081427865447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227272 : Nat.totient 79211881234889091923261227272 = 26342981288277203780484092928 := by
  rw [← show ((([(2, 3), (3, 2), (433, 1), (2540796806353896969568297, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_433, prime_lucas_2540796806353896969568297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227273 : Nat.totient 79211881234889091923261227273 = 79211881234889091923261227272 := by
  rw [← show ((([(79211881234889091923261227273, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_79211881234889091923261227273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227274 : Nat.totient 79211881234889091923261227274 = 38071226539464767072202397392 := by
  rw [← show ((([(2, 1), (37, 1), (83, 1), (12896756957813267978388347, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_37, prime_small_83, prime_lucas_12896756957813267978388347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227275 : Nat.totient 79211881234889091923261227275 = 41992532461158246658496148480 := by
  rw [← show ((([(3, 1), (5, 2), (167, 1), (51419, 1), (2721133, 1), (45200079401833, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_5, prime_small_167, prime_small_51419, prime_small_2721133, prime_lucas_45200079401833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227276 : Nat.totient 79211881234889091923261227276 = 37521413900177115343037633856 := by
  rw [← show ((([(2, 2), (19, 2), (10638713, 1), (5156250895325744483, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_19, prime_lucas_10638713, prime_lucas_5156250895325744483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227277 : Nat.totient 79211881234889091923261227277 = 61723534257592291065383496000 := by
  rw [← show ((([(7, 1), (11, 1), (6455221, 1), (159363363442279506781, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_7, prime_small_11, prime_small_6455221, prime_lucas_159363363442279506781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227278 : Nat.totient 79211881234889091923261227278 = 24372751981797112765069929600 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (181141, 1), (5606333954813291920861, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_13, prime_small_181141, prime_lucas_5606333954813291920861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227279 : Nat.totient 79211881234889091923261227279 = 79046511962999970645759637600 := by
  rw [← show ((([(479, 1), (165369271889121277501589201, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_479, prime_lucas_165369271889121277501589201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227280 : Nat.totient 79211881234889091923261227280 = 31684752493955636769304490880 := by
  rw [← show ((([(2, 4), (5, 1), (990148515436113649040765341, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_lucas_990148515436113649040765341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227281 : Nat.totient 79211881234889091923261227281 = 52400870214808389207813734400 := by
  rw [← show ((([(3, 3), (181, 1), (467, 1), (18457, 1), (88562657, 1), (21233391061, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_181, prime_small_467, prime_small_18457, prime_lucas_88562657, prime_lucas_21233391061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227282 : Nat.totient 79211881234889091923261227282 = 38570570536058444725080542080 := by
  rw [← show ((([(2, 1), (41, 1), (557, 1), (1734288243527807766415493, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_41, prime_small_557, prime_lucas_1734288243527807766415493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227283 : Nat.totient 79211881234889091923261227283 = 79211878916114166529623802080 := by
  rw [← show ((([(34161091, 1), (2318774925393603264113, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_34161091, prime_lucas_2318774925393603264113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227284 : Nat.totient 79211881234889091923261227284 = 22319085760140853934621531136 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (73, 1), (7823, 1), (23455760227, 1), (70398813197, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_7, prime_small_73, prime_small_7823, prime_lucas_23455760227, prime_lucas_70398813197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227285 : Nat.totient 79211881234889091923261227285 = 59625287579595749193516515328 := by
  rw [← show ((([(5, 1), (17, 1), (3593, 1), (316611692209, 1), (819194892233, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_17, prime_small_3593, prime_lucas_316611692209, prime_lucas_819194892233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227286 : Nat.totient 79211881234889091923261227286 = 38250210745250860170939831168 := by
  rw [← show ((([(2, 1), (43, 1), (89, 1), (10349082993844929699929609, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_43, prime_small_89, prime_lucas_10349082993844929699929609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227287 : Nat.totient 79211881234889091923261227287 = 50986958036250449973593433600 := by
  rw [← show ((([(3, 1), (29, 1), (910481393504472320957025601, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_29, prime_lucas_910481393504472320957025601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227288 : Nat.totient 79211881234889091923261227288 = 35933819248070056158934677280 := by
  rw [← show ((([(2, 3), (11, 1), (503, 1), (1789532831079186063691967, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_11, prime_small_503, prime_lucas_1789532831079186063691967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227289 : Nat.totient 79211881234889091923261227289 = 79201916222416296940959328000 := by
  rw [← show ((([(7949, 1), (217272655601, 1), (45864087586061, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_7949, prime_lucas_217272655601, prime_lucas_45864087586061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227290 : Nat.totient 79211881234889091923261227290 = 21123168329303757846202993920 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (880132013720989910258458081, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_5, prime_lucas_880132013720989910258458081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227291 : Nat.totient 79211881234889091923261227291 = 62533552977620170564054745088 := by
  rw [← show ((([(7, 1), (13, 1), (449, 1), (1938664216816101517982849, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_7, prime_small_13, prime_small_449, prime_lucas_1938664216816101517982849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227292 : Nat.totient 79211881234889091923261227292 = 37663812440011260792602396160 := by
  rw [← show ((([(2, 2), (23, 1), (211, 1), (929, 1), (4392424760226720031979, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_23, prime_small_211, prime_small_929, prime_lucas_4392424760226720031979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227293 : Nat.totient 79211881234889091923261227293 = 51104439506380059305329824000 := by
  rw [← show ((([(3, 1), (31, 1), (851740658439667655088830401, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_31, prime_lucas_851740658439667655088830401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227294 : Nat.totient 79211881234889091923261227294 = 38759395617450455743054828800 := by
  rw [← show ((([(2, 1), (47, 1), (13901, 1), (35993, 1), (1684218309306738157, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_47, prime_small_13901, prime_small_35993, prime_lucas_1684218309306738157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227295 : Nat.totient 79211881234889091923261227295 = 59805182640665084554008000000 := by
  rw [← show ((([(5, 1), (19, 1), (263, 1), (89387, 1), (464171, 1), (3422501, 1), (22326211, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_19, prime_small_263, prime_small_89387, prime_small_464171, prime_small_3422501, prime_lucas_22326211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227296 : Nat.totient 79211881234889091923261227296 = 26403960411629697307753742400 := by
  rw [← show ((([(2, 5), (3, 1), (825123762863428040867304451, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_lucas_825123762863428040867304451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227297 : Nat.totient 79211881234889091923261227297 = 79211876396756766076199870656 := by
  rw [← show ((([(16372409, 1), (4838132325847044984233, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_16372409, prime_lucas_4838132325847044984233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227298 : Nat.totient 79211881234889091923261227298 = 33912326908535938619821945440 := by
  rw [← show ((([(2, 1), (7, 3), (953, 1), (121163918812296127807631, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_7, prime_small_953, prime_lucas_121163918812296127807631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227299 : Nat.totient 79211881234889091923261227299 = 48007200748417631468643168000 := by
  rw [← show ((([(3, 2), (11, 1), (800120012473627191144052801, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_11, prime_lucas_800120012473627191144052801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_79211881234889091923261227300 : Nat.totient 79211881234889091923261227300 = 31683374035671557837368704000 := by
  rw [← show ((([(2, 2), (5, 2), (24889, 1), (300557, 1), (105890264413236701, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889091923261227300 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_24889, prime_small_300557, prime_lucas_105890264413236701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454401 : Nat.totient 158423762469778183846522454401 = 158270399679203682100559898912 := by
  rw [← show ((([(1033, 1), (848091156019, 1), (180832908465763, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_1033, prime_lucas_848091156019, prime_lucas_180832908465763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454402 : Nat.totient 158423762469778183846522454402 = 79211881234878182185049052804 := by
  rw [← show ((([(2, 1), (7265496855919, 1), (10902472715318479, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_lucas_7265496855919, prime_lucas_10902472715318479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454403 : Nat.totient 158423762469778183846522454403 = 105615841646518789231014969600 := by
  rw [← show ((([(3, 1), (52807920823259394615507484801, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_lucas_52807920823259394615507484801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454404 : Nat.totient 158423762469778183846522454404 = 79211881234696772528069012064 := by
  rw [← show ((([(2, 2), (411878481853, 1), (96159285717625717, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_lucas_411878481853, prime_lucas_96159285717625717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454405 : Nat.totient 158423762469778183846522454405 = 126739009975079544722023986000 := by
  rw [← show ((([(5, 1), (170577018331, 1), (185750418221476051, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_lucas_170577018331, prime_lucas_185750418221476051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454406 : Nat.totient 158423762469778183846522454406 = 52602441524179268066197211136 := by
  rw [← show ((([(2, 1), (3, 1), (257, 1), (52188119, 1), (1968630936296891047, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_257, prime_lucas_52188119, prime_lucas_1968630936296891047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454407 : Nat.totient 158423762469778183846522454407 = 134370008001910856455519896576 := by
  rw [← show ((([(7, 1), (107, 1), (983, 1), (9013, 1), (181199, 1), (656809, 1), (200595287, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_7, prime_small_107, prime_small_983, prime_small_9013, prime_small_181199, prime_small_656809, prime_lucas_200595287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454408 : Nat.totient 158423762469778183846522454408 = 79211845443375362880811035088 := by
  rw [← show ((([(2, 3), (2213147, 1), (8947878432260610334883, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_2213147, prime_lucas_8947878432260610334883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454409 : Nat.totient 158423762469778183846522454409 = 105142228006848301386929699352 := by
  rw [← show ((([(3, 2), (223, 1), (78935606611747974014211487, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_223, prime_lucas_78935606611747974014211487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454410 : Nat.totient 158423762469778183846522454410 = 63167046505521780651904159488 := by
  rw [← show ((([(2, 1), (5, 1), (313, 1), (50614620597373221676205257, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_313, prime_lucas_50614620597373221676205257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454411 : Nat.totient 158423762469778183846522454411 = 144021568930997329366410631680 := by
  rw [← show ((([(11, 1), (4324669, 1), (12670723057, 1), (262829050597, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_11, prime_small_4324669, prime_lucas_12670723057, prime_lucas_262829050597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454412 : Nat.totient 158423762469778183846522454412 = 52807920823259394615507484800 := by
  rw [← show ((([(2, 2), (3, 1), (13201980205814848653876871201, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_lucas_13201980205814848653876871201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454413 : Nat.totient 158423762469778183846522454413 = 146221757074618166068246707264 := by
  rw [← show ((([(13, 1), (9397, 1), (1296844021166969686287133, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_13, prime_small_9397, prime_lucas_1296844021166969686287133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454414 : Nat.totient 158423762469778183846522454414 = 67895898201333507362795337600 := by
  rw [← show ((([(2, 1), (7, 1), (11315983033555584560465889601, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_7, prime_lucas_11315983033555584560465889601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454415 : Nat.totient 158423762469778183846522454415 = 84488548280067067272118219776 := by
  rw [← show ((([(3, 1), (5, 1), (20483, 1), (3741210059, 1), (137823541684513, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_5, prime_small_20483, prime_lucas_3741210059, prime_lucas_137823541684513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454416 : Nat.totient 158423762469778183846522454416 = 79040055028305818404989507200 := by
  rw [← show ((([(2, 4), (461, 1), (21478275822909189783964541, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_461, prime_lucas_21478275822909189783964541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454417 : Nat.totient 158423762469778183846522454417 = 148942470918268064029809761856 := by
  rw [← show ((([(17, 2), (919, 1), (596495221862857490828087, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_17, prime_small_919, prime_lucas_596495221862857490828087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454418 : Nat.totient 158423762469778183846522454418 = 52807917044365058961014475552 := by
  rw [← show ((([(2, 1), (3, 2), (13974437, 1), (629815722609068193773, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_lucas_13974437, prime_lucas_629815722609068193773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454419 : Nat.totient 158423762469778183846522454419 = 150085633176529348662854380800 := by
  rw [← show ((([(19, 1), (4128253, 1), (853323017, 1), (2366938408301, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_19, prime_small_4128253, prime_lucas_853323017, prime_lucas_2366938408301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454420 : Nat.totient 158423762469778183846522454420 = 63369504987911273538608981760 := by
  rw [← show ((([(2, 2), (5, 1), (7921188123488909192326122721, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_lucas_7921188123488909192326122721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454421 : Nat.totient 158423762469778183846522454421 = 90455410586533725359674444800 := by
  rw [← show ((([(3, 1), (7, 1), (1297, 1), (34061, 1), (4029825743, 1), (42375749371, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_7, prime_small_1297, prime_small_34061, prime_lucas_4029825743, prime_lucas_42375749371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454422 : Nat.totient 158423762469778183846522454422 = 71024351792179509570047425920 := by
  rw [← show ((([(2, 1), (11, 1), (73, 1), (98644933044693763291732537, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_11, prime_small_73, prime_lucas_98644933044693763291732537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454423 : Nat.totient 158423762469778183846522454423 = 151535772797179132374934521600 := by
  rw [← show ((([(23, 1), (6887989672599051471587932801, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_23, prime_lucas_6887989672599051471587932801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454424 : Nat.totient 158423762469778183846522454424 = 52807920823259394615507484800 := by
  rw [← show ((([(2, 3), (3, 1), (6600990102907424326938435601, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_lucas_6600990102907424326938435601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454425 : Nat.totient 158423762469778183846522454425 = 124953428546048898083908065600 := by
  rw [← show ((([(5, 2), (71, 1), (256279, 1), (3342679, 1), (104187177352007, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_71, prime_small_256279, prime_small_3342679, prime_lucas_104187177352007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454426 : Nat.totient 158423762469778183846522454426 = 73118659601436084852241132800 := by
  rw [← show ((([(2, 1), (13, 1), (6093221633453007071020094401, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_13, prime_lucas_6093221633453007071020094401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454427 : Nat.totient 158423762469778183846522454427 = 104559925060198324226345472000 := by
  rw [← show ((([(3, 5), (101, 1), (11909, 1), (87049, 1), (448309, 1), (13889164981, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_101, prime_small_11909, prime_small_87049, prime_small_448309, prime_lucas_13889164981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454428 : Nat.totient 158423762469778183846522454428 = 67747329493242463284659485056 := by
  rw [← show ((([(2, 2), (7, 1), (457, 1), (22174564067, 1), (558330047988179, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_7, prime_small_457, prime_lucas_22174564067, prime_lucas_558330047988179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454429 : Nat.totient 158423762469778183846522454429 = 152960874108751349920780300800 := by
  rw [← show ((([(29, 1), (5462888361026833925742153601, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_29, prime_lucas_5462888361026833925742153601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454430 : Nat.totient 158423762469778183846522454430 = 41722489596920327072696843264 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (179, 1), (233, 1), (389, 1), (325492147189753087847, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_5, prime_small_179, prime_small_233, prime_small_389, prime_lucas_325492147189753087847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454431 : Nat.totient 158423762469778183846522454431 = 151820573877439914330547574400 := by
  rw [← show ((([(31, 1), (103, 1), (35591, 1), (1394059191531732258737, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_31, prime_small_103, prime_small_35591, prime_lucas_1394059191531732258737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454432 : Nat.totient 158423762469778183846522454432 = 79211880287975208521764628992 := by
  rw [← show ((([(2, 5), (83652677, 1), (59182117712509884713, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_lucas_83652677, prime_lucas_59182117712509884713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454433 : Nat.totient 158423762469778183846522454433 = 95891565182275539115531776000 := by
  rw [← show ((([(3, 1), (11, 1), (811, 1), (21569, 1), (578104421, 1), (474732788359, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_11, prime_small_811, prime_small_21569, prime_lucas_578104421, prime_lucas_474732788359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454434 : Nat.totient 158423762469778183846522454434 = 74552341711777761492257882112 := by
  rw [← show ((([(2, 1), (17, 1), (4360417, 1), (1068595601196333123553, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_17, prime_small_4360417, prime_lucas_1068595601196333123553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454435 : Nat.totient 158423762469778183846522454435 = 108555617065646337865484214528 := by
  rw [← show ((([(5, 1), (7, 1), (1543, 1), (14639, 1), (200389490985502323833, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_7, prime_small_1543, prime_small_14639, prime_lucas_200389490985502323833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454436 : Nat.totient 158423762469778183846522454436 = 52606660546749434525476876800 := by
  rw [← show ((([(2, 2), (3, 2), (281, 1), (3947, 1), (582470173, 1), (6811937979991, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_281, prime_small_3947, prime_lucas_582470173, prime_lucas_6811937979991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454437 : Nat.totient 158423762469778183846522454437 = 154029279804144248973617227152 := by
  rw [← show ((([(37, 1), (1367, 1), (3132204323331386224451303, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_37, prime_small_1367, prime_lucas_3132204323331386224451303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454438 : Nat.totient 158423762469778183846522454438 = 74876416766174725698627279360 := by
  rw [← show ((([(2, 1), (19, 1), (593, 1), (1879, 1), (8248945261, 1), (453583065203, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_19, prime_small_593, prime_small_1879, prime_lucas_8248945261, prime_lucas_453583065203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454439 : Nat.totient 158423762469778183846522454439 = 96486478649317720217390358528 := by
  rw [← show ((([(3, 1), (13, 1), (97, 1), (41877811913766371622131233, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_13, prime_small_97, prime_lucas_41877811913766371622131233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454440 : Nat.totient 158423762469778183846522454440 = 63369396941198671324326240000 := by
  rw [← show ((([(2, 3), (5, 1), (586501, 1), (6752919537638392084861, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_586501, prime_lucas_6752919537638392084861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454441 : Nat.totient 158423762469778183846522454441 = 154559766383381523396412496160 := by
  rw [← show ((([(41, 1), (82220659, 1), (46995417618581185339, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_41, prime_lucas_82220659, prime_lucas_46995417618581185339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454442 : Nat.totient 158423762469778183846522454442 = 45263932134222338241863558400 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (3771994344518528186821963201, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_7, prime_lucas_3771994344518528186821963201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454443 : Nat.totient 158423762469778183846522454443 = 154739488923291163127660025000 := by
  rw [← show ((([(43, 1), (228156592751, 1), (16148003883585551, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_43, prime_lucas_228156592751, prime_lucas_16148003883585551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454444 : Nat.totient 158423762469778183846522454444 = 72010801098745569983227389840 := by
  rw [← show ((([(2, 2), (11, 1), (3015416923, 1), (1194043857971451187, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_11, prime_lucas_3015416923, prime_lucas_1194043857971451187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454445 : Nat.totient 158423762469778183846522454445 = 84490312635657390599004902400 := by
  rw [← show ((([(3, 2), (5, 1), (35801, 1), (136950277, 1), (718041816493973, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_5, prime_small_35801, prime_lucas_136950277, prime_lucas_718041816493973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454446 : Nat.totient 158423762469778183846522454446 = 75516289204715681899790653440 := by
  rw [← show ((([(2, 1), (23, 1), (331, 1), (3329, 1), (3125508632188182161699, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_23, prime_small_331, prime_small_3329, prime_lucas_3125508632188182161699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454447 : Nat.totient 158423762469778183846522454447 = 155053044119337473035576636600 := by
  rw [← show ((([(47, 1), (7937905030031, 1), (424635761913071, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_47, prime_lucas_7937905030031, prime_lucas_424635761913071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454448 : Nat.totient 158423762469778183846522454448 = 52611608849938727721026040064 := by
  rw [← show ((([(2, 4), (3, 1), (269, 1), (12269498332541680905090029, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_269, prime_lucas_12269498332541680905090029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454449 : Nat.totient 158423762469778183846522454449 = 135789222004191221466924922824 := by
  rw [← show ((([(7, 2), (52747, 1), (61295201804601396750883, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_7, prime_small_52747, prime_lucas_61295201804601396750883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454450 : Nat.totient 158423762469778183846522454450 = 63367816164564638991029207040 := by
  rw [← show ((([(2, 1), (5, 2), (42209, 1), (337969, 1), (222110141675359409, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_42209, prime_small_337969, prime_lucas_222110141675359409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454451 : Nat.totient 158423762469778183846522454451 = 99403145079076507511543500800 := by
  rw [← show ((([(3, 1), (17, 1), (3106348283721140859735734401, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_17, prime_lucas_3106348283721140859735734401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454452 : Nat.totient 158423762469778183846522454452 = 71974591689081565006327203840 := by
  rw [← show ((([(2, 2), (13, 1), (113, 1), (163, 1), (1427, 1), (37591, 1), (3083493800933647, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_13, prime_small_113, prime_small_163, prime_small_1427, prime_small_37591, prime_lucas_3083493800933647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454453 : Nat.totient 158423762469778183846522454453 = 154858684817140240527691776000 := by
  rw [← show ((([(53, 1), (311, 1), (2803, 1), (7417, 1), (39993221, 1), (11559693121, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_53, prime_small_311, prime_small_2803, prime_small_7417, prime_lucas_39993221, prime_lucas_11559693121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454454 : Nat.totient 158423762469778183846522454454 = 52807920020157696732404467200 := by
  rw [← show ((([(2, 1), (3, 3), (65754961, 1), (44616760993439968241, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_lucas_65754961, prime_lucas_44616760993439968241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454455 : Nat.totient 158423762469778183846522454455 = 115217222032257699567832012800 := by
  rw [← show ((([(5, 1), (11, 1), (2418613, 1), (9501517, 1), (125342485170961, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_11, prime_small_2418613, prime_small_9501517, prime_lucas_125342485170961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454456 : Nat.totient 158423762469778183846522454456 = 67441226408316056163227323392 := by
  rw [← show ((([(2, 3), (7, 1), (157, 1), (3037, 1), (5933184479296523639689, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_7, prime_small_157, prime_small_3037, prime_lucas_5933184479296523639689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454457 : Nat.totient 158423762469778183846522454457 = 100057112615509021374811978752 := by
  rw [← show ((([(3, 1), (19, 1), (191204753, 1), (14536062572962072817, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_19, prime_lucas_191204753, prime_lucas_14536062572962072817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454458 : Nat.totient 158423762469778183846522454458 = 75129017183007728150419372800 := by
  rw [← show ((([(2, 1), (29, 1), (79, 1), (197, 1), (42879077, 1), (4093111581118951, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_29, prime_small_79, prime_small_197, prime_lucas_42879077, prime_lucas_4093111581118951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454459 : Nat.totient 158423762469778183846522454459 = 155117954414437757796243624000 := by
  rw [← show ((([(59, 1), (251, 1), (829627, 1), (12894713954982603113, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_59, prime_small_251, prime_small_829627, prime_lucas_12894713954982603113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454460 : Nat.totient 158423762469778183846522454460 = 41800388407367138533394178048 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (109, 1), (1213, 1), (1753, 1), (771186739, 1), (14772034219, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_5, prime_small_109, prime_small_1213, prime_small_1753, prime_lucas_771186739, prime_lucas_14772034219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454461 : Nat.totient 158423762469778183846522454461 = 155826642849216764270160078720 := by
  rw [← show ((([(61, 1), (17846863, 1), (7344005783, 1), (19815068969, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_61, prime_lucas_17846863, prime_lucas_7344005783, prime_lucas_19815068969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454462 : Nat.totient 158423762469778183846522454462 = 76652209164623322154850835840 := by
  rw [← show ((([(2, 1), (31, 1), (19973, 1), (161059, 1), (562997, 1), (1410893565619, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_31, prime_small_19973, prime_small_161059, prime_small_562997, prime_lucas_1410893565619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454463 : Nat.totient 158423762469778183846522454463 = 90527864268444676483727116800 := by
  rw [← show ((([(3, 2), (7, 1), (2514662896345685457881308801, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_7, prime_lucas_2514662896345685457881308801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454464 : Nat.totient 158423762469778183846522454464 = 78914059611382862138264616960 := by
  rw [← show ((([(2, 6), (317, 1), (1721, 1), (38333, 1), (47080037, 1), (2514146683, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_317, prime_small_1721, prime_small_38333, prime_lucas_47080037, prime_lucas_2514146683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454465 : Nat.totient 158423762469778183846522454465 = 115348715106714400792952388096 := by
  rw [← show ((([(5, 1), (13, 1), (83, 1), (499, 1), (58847542153734042263033, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_13, prime_small_83, prime_small_499, prime_lucas_58847542153734042263033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454466 : Nat.totient 158423762469778183846522454466 = 48006236244726474448068419040 := by
  rw [← show ((([(2, 1), (3, 1), (11, 2), (49783, 1), (275131919, 1), (15931683165883, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_11, prime_small_49783, prime_lucas_275131919, prime_lucas_15931683165883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454467 : Nat.totient 158423762469778183846522454467 = 156058486244741428986502098432 := by
  rw [← show ((([(67, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_67, prime_small_210193, prime_lucas_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454468 : Nat.totient 158423762469778183846522454468 = 74054263532652272893220889600 := by
  rw [← show ((([(2, 2), (17, 1), (151, 1), (16943, 1), (910634610394437306857, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_17, prime_small_151, prime_small_16943, prime_lucas_910634610394437306857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454469 : Nat.totient 158423762469778183846522454469 = 101015487843473517085629000000 := by
  rw [← show ((([(3, 1), (23, 1), (12101, 1), (8212951, 1), (23102061724805051, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_23, prime_small_12101, prime_small_8212951, prime_lucas_23102061724805051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454470 : Nat.totient 158423762469778183846522454470 = 54315267869889632327597136000 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (38261, 1), (1749031, 1), (33819599447151131, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_7, prime_small_38261, prime_small_1749031, prime_lucas_33819599447151131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454471 : Nat.totient 158423762469778183846522454471 = 158423747825845296077530150344 := by
  rw [← show ((([(10818389, 1), (14643932887768981485739, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_10818389, prime_lucas_14643932887768981485739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454472 : Nat.totient 158423762469778183846522454472 = 52659511196228357857670407680 := by
  rw [← show ((([(2, 3), (3, 2), (359, 1), (50077, 1), (214891, 1), (3422179, 1), (166430963, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_359, prime_small_50077, prime_small_214891, prime_small_3422179, prime_lucas_166430963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454473 : Nat.totient 158423762469778183846522454473 = 158423762469778183846522454472 := by
  rw [← show ((([(158423762469778183846522454473, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_158423762469778183846522454473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454474 : Nat.totient 158423762469778183846522454474 = 77027890861604516920975810512 := by
  rw [← show ((([(2, 1), (37, 1), (1787, 1), (1198019952432569940913523, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_37, prime_small_1787, prime_lucas_1198019952432569940913523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454475 : Nat.totient 158423762469778183846522454475 = 84397055497480258112317920000 := by
  rw [← show ((([(3, 1), (5, 2), (911, 1), (29401, 1), (78863960059692249863, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_5, prime_small_911, prime_small_29401, prime_lucas_78863960059692249863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454476 : Nat.totient 158423762469778183846522454476 = 75042534346245689893767639360 := by
  rw [← show ((([(2, 2), (19, 1), (252029, 1), (27257491, 1), (303438258668759, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_19, prime_small_252029, prime_lucas_27257491, prime_lucas_303438258668759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454477 : Nat.totient 158423762469778183846522454477 = 122545988351603244508088279040 := by
  rw [← show ((([(7, 1), (11, 1), (137, 1), (5075633, 1), (81294557, 1), (36396309533, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_7, prime_small_11, prime_small_137, prime_small_5075633, prime_lucas_81294557, prime_lucas_36396309533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454478 : Nat.totient 158423762469778183846522454478 = 48745753914176483756465090688 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (2545013, 1), (798060315533818107677, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_13, prime_small_2545013, prime_lucas_798060315533818107677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454479 : Nat.totient 158423762469778183846522454479 = 158423762469778183846522454478 := by
  rw [← show ((([(158423762469778183846522454479, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_158423762469778183846522454479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454480 : Nat.totient 158423762469778183846522454480 = 62667879199675889131975557120 := by
  rw [← show ((([(2, 4), (5, 1), (131, 2), (293, 1), (19213, 1), (20498634974645969, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_131, prime_small_293, prime_small_19213, prime_lucas_20498634974645969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454481 : Nat.totient 158423762469778183846522454481 = 104907010494528730242887349744 := by
  rw [← show ((([(3, 3), (149, 1), (39379508443892166007089847, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_149, prime_lucas_39379508443892166007089847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454482 : Nat.totient 158423762469778183846522454482 = 77267094474341132433070817280 := by
  rw [← show ((([(2, 1), (41, 1), (6073, 1), (1197953, 1), (265560458835600329, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_41, prime_small_6073, prime_small_1197953, prime_lucas_265560458835600329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454483 : Nat.totient 158423762469778183846522454483 = 156641096030417844488154065664 := by
  rw [← show ((([(89, 1), (59693, 1), (17952493613, 1), (1661047798483, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_89, prime_small_59693, prime_lucas_17952493613, prime_lucas_1661047798483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454484 : Nat.totient 158423762469778183846522454484 = 45261069683048077278243358080 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (16763, 1), (279007, 1), (403249829858894861, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_7, prime_small_16763, prime_small_279007, prime_lucas_403249829858894861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454485 : Nat.totient 158423762469778183846522454485 = 119273101815415843982785781760 := by
  rw [← show ((([(5, 1), (17, 1), (11177, 1), (4541022221, 1), (36721678125373, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_17, prime_small_11177, prime_lucas_4541022221, prime_lucas_36721678125373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454486 : Nat.totient 158423762469778183846522454486 = 77369744416261309888619525544 := by
  rw [← show ((([(2, 1), (43, 1), (1692126367, 1), (1088652011356783903, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_43, prime_lucas_1692126367, prime_lucas_1088652011356783903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454487 : Nat.totient 158423762469778183846522454487 = 101973915814135283706605576192 := by
  rw [← show ((([(3, 1), (29, 1), (394688417, 1), (4613671718187120353, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_29, prime_lucas_394688417, prime_lucas_4613671718187120353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454488 : Nat.totient 158423762469778183846522454488 = 71820799008846430191875120160 := by
  rw [← show ((([(2, 3), (11, 1), (379, 1), (4750052844500425277240419, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_11, prime_small_379, prime_lucas_4750052844500425277240419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454489 : Nat.totient 158423762469778183846522454489 = 158396686113081232590393110400 := by
  rw [← show ((([(5851, 1), (1850847830203, 1), (14629164082913, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5851, prime_lucas_1850847830203, prime_lucas_14629164082913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454490 : Nat.totient 158423762469778183846522454490 = 42246336652734701345680428000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (7193542211, 1), (244700590586689451, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_5, prime_lucas_7193542211, prime_lucas_244700590586689451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454491 : Nat.totient 158423762469778183846522454491 = 125345967508955796243407861760 := by
  rw [← show ((([(7, 1), (13, 1), (493457, 1), (2406941, 1), (1465764408851173, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_7, prime_small_13, prime_small_493457, prime_small_2406941, prime_lucas_1465764408851173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454492 : Nat.totient 158423762469778183846522454492 = 75767748469017349860134408048 := by
  rw [← show ((([(2, 2), (23, 1), (549323, 1), (3134763004916529742787, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_23, prime_small_549323, prime_lucas_3134763004916529742787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454493 : Nat.totient 158423762469778183846522454493 = 102208402507879134027259395840 := by
  rw [← show ((([(3, 1), (31, 1), (305237, 1), (761983, 1), (13954663, 1), (524850437, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_31, prime_small_305237, prime_small_761983, prime_lucas_13954663, prime_lucas_524850437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454494 : Nat.totient 158423762469778183846522454494 = 77184917666096749984032903520 := by
  rw [← show ((([(2, 1), (47, 1), (227, 1), (1067879, 1), (13818191, 1), (503145247667, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_47, prime_small_227, prime_small_1067879, prime_lucas_13818191, prime_lucas_503145247667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454495 : Nat.totient 158423762469778183846522454495 = 118423761289386158825424543744 := by
  rw [← show ((([(5, 1), (19, 1), (73, 1), (8096359153, 1), (2821526234944009, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_5, prime_small_19, prime_small_73, prime_lucas_8096359153, prime_lucas_2821526234944009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454496 : Nat.totient 158423762469778183846522454496 = 51822961993501282370987827200 := by
  rw [← show ((([(2, 5), (3, 1), (71, 1), (239, 1), (2221, 1), (43786908338927870449, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_3, prime_small_71, prime_small_239, prime_small_2221, prime_lucas_43786908338927870449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454497 : Nat.totient 158423762469778183846522454497 = 158423762469778183846522454496 := by
  rw [← show ((([(158423762469778183846522454497, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_158423762469778183846522454497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454498 : Nat.totient 158423762469778183846522454498 = 67513938896482290576048029184 := by
  rw [← show ((([(2, 1), (7, 2), (193, 1), (2239, 1), (3740958109059732294463, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_7, prime_small_193, prime_small_2239, prime_lucas_3740958109059732294463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454499 : Nat.totient 158423762469778183846522454499 = 95863380136542954437845305600 := by
  rw [← show ((([(3, 2), (11, 1), (683, 1), (9181, 1), (75392963, 1), (3384882720949, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_3, prime_small_11, prime_small_683, prime_small_9181, prime_lucas_75392963, prime_lucas_3384882720949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
private theorem phi67_158423762469778183846522454500 : Nat.totient 158423762469778183846522454500 = 62741537437900220060488704000 := by
  rw [← show ((([(2, 2), (5, 3), (173, 1), (241, 1), (274403, 1), (3673367, 1), (7539351613, 1)] : List FactorBlock).map factorBlockValue).prod) = 158423762469778183846522454500 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_small_2, prime_small_5, prime_small_173, prime_small_241, prime_small_274403, prime_small_3673367, prime_lucas_7539351613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide
/-! ## 4. The certificate, its minimality, and the new plateau -/

/-- Depth `98` is admitted by the floor but the residue lands inside the
forbidden neighbourhood. -/
theorem not_certifiedKill_diagonal_t67_98 :
    ¬ certifiedKill (periodLcm 67) (periodLcm 67) 98 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi67_79211881234889091923261227201, phi67_79211881234889091923261227202, phi67_79211881234889091923261227203, phi67_79211881234889091923261227204, phi67_79211881234889091923261227205, phi67_79211881234889091923261227206, phi67_79211881234889091923261227207, phi67_79211881234889091923261227208, phi67_79211881234889091923261227209, phi67_79211881234889091923261227210, phi67_79211881234889091923261227211, phi67_79211881234889091923261227212, phi67_79211881234889091923261227213, phi67_79211881234889091923261227214, phi67_79211881234889091923261227215, phi67_79211881234889091923261227216, phi67_79211881234889091923261227217, phi67_79211881234889091923261227218, phi67_79211881234889091923261227219, phi67_79211881234889091923261227220, phi67_79211881234889091923261227221, phi67_79211881234889091923261227222, phi67_79211881234889091923261227223, phi67_79211881234889091923261227224, phi67_79211881234889091923261227225, phi67_79211881234889091923261227226, phi67_79211881234889091923261227227, phi67_79211881234889091923261227228, phi67_79211881234889091923261227229, phi67_79211881234889091923261227230, phi67_79211881234889091923261227231, phi67_79211881234889091923261227232, phi67_79211881234889091923261227233, phi67_79211881234889091923261227234, phi67_79211881234889091923261227235, phi67_79211881234889091923261227236, phi67_79211881234889091923261227237, phi67_79211881234889091923261227238, phi67_79211881234889091923261227239, phi67_79211881234889091923261227240, phi67_79211881234889091923261227241, phi67_79211881234889091923261227242, phi67_79211881234889091923261227243, phi67_79211881234889091923261227244, phi67_79211881234889091923261227245, phi67_79211881234889091923261227246, phi67_79211881234889091923261227247, phi67_79211881234889091923261227248, phi67_79211881234889091923261227249, phi67_79211881234889091923261227250, phi67_79211881234889091923261227251, phi67_79211881234889091923261227252, phi67_79211881234889091923261227253, phi67_79211881234889091923261227254, phi67_79211881234889091923261227255, phi67_79211881234889091923261227256, phi67_79211881234889091923261227257, phi67_79211881234889091923261227258, phi67_79211881234889091923261227259, phi67_79211881234889091923261227260, phi67_79211881234889091923261227261, phi67_79211881234889091923261227262, phi67_79211881234889091923261227263, phi67_79211881234889091923261227264, phi67_79211881234889091923261227265, phi67_79211881234889091923261227266, phi67_79211881234889091923261227267, phi67_79211881234889091923261227268, phi67_79211881234889091923261227269, phi67_79211881234889091923261227270, phi67_79211881234889091923261227271, phi67_79211881234889091923261227272, phi67_79211881234889091923261227273, phi67_79211881234889091923261227274, phi67_79211881234889091923261227275, phi67_79211881234889091923261227276, phi67_79211881234889091923261227277, phi67_79211881234889091923261227278, phi67_79211881234889091923261227279, phi67_79211881234889091923261227280, phi67_79211881234889091923261227281, phi67_79211881234889091923261227282, phi67_79211881234889091923261227283, phi67_79211881234889091923261227284, phi67_79211881234889091923261227285, phi67_79211881234889091923261227286, phi67_79211881234889091923261227287, phi67_79211881234889091923261227288, phi67_79211881234889091923261227289, phi67_79211881234889091923261227290, phi67_79211881234889091923261227291, phi67_79211881234889091923261227292, phi67_79211881234889091923261227293, phi67_79211881234889091923261227294, phi67_79211881234889091923261227295, phi67_79211881234889091923261227296, phi67_79211881234889091923261227297, phi67_79211881234889091923261227298, phi67_79211881234889091923261227299, phi67_79211881234889091923261227300, phi67_158423762469778183846522454401, phi67_158423762469778183846522454402, phi67_158423762469778183846522454403, phi67_158423762469778183846522454404, phi67_158423762469778183846522454405, phi67_158423762469778183846522454406, phi67_158423762469778183846522454407, phi67_158423762469778183846522454408, phi67_158423762469778183846522454409, phi67_158423762469778183846522454410, phi67_158423762469778183846522454411, phi67_158423762469778183846522454412, phi67_158423762469778183846522454413, phi67_158423762469778183846522454414, phi67_158423762469778183846522454415, phi67_158423762469778183846522454416, phi67_158423762469778183846522454417, phi67_158423762469778183846522454418, phi67_158423762469778183846522454419, phi67_158423762469778183846522454420, phi67_158423762469778183846522454421, phi67_158423762469778183846522454422, phi67_158423762469778183846522454423, phi67_158423762469778183846522454424, phi67_158423762469778183846522454425, phi67_158423762469778183846522454426, phi67_158423762469778183846522454427, phi67_158423762469778183846522454428, phi67_158423762469778183846522454429, phi67_158423762469778183846522454430, phi67_158423762469778183846522454431, phi67_158423762469778183846522454432, phi67_158423762469778183846522454433, phi67_158423762469778183846522454434, phi67_158423762469778183846522454435, phi67_158423762469778183846522454436, phi67_158423762469778183846522454437, phi67_158423762469778183846522454438, phi67_158423762469778183846522454439, phi67_158423762469778183846522454440, phi67_158423762469778183846522454441, phi67_158423762469778183846522454442, phi67_158423762469778183846522454443, phi67_158423762469778183846522454444, phi67_158423762469778183846522454445, phi67_158423762469778183846522454446, phi67_158423762469778183846522454447, phi67_158423762469778183846522454448, phi67_158423762469778183846522454449, phi67_158423762469778183846522454450, phi67_158423762469778183846522454451, phi67_158423762469778183846522454452, phi67_158423762469778183846522454453, phi67_158423762469778183846522454454, phi67_158423762469778183846522454455, phi67_158423762469778183846522454456, phi67_158423762469778183846522454457, phi67_158423762469778183846522454458, phi67_158423762469778183846522454459, phi67_158423762469778183846522454460, phi67_158423762469778183846522454461, phi67_158423762469778183846522454462, phi67_158423762469778183846522454463, phi67_158423762469778183846522454464, phi67_158423762469778183846522454465, phi67_158423762469778183846522454466, phi67_158423762469778183846522454467, phi67_158423762469778183846522454468, phi67_158423762469778183846522454469, phi67_158423762469778183846522454470, phi67_158423762469778183846522454471, phi67_158423762469778183846522454472, phi67_158423762469778183846522454473, phi67_158423762469778183846522454474, phi67_158423762469778183846522454475, phi67_158423762469778183846522454476, phi67_158423762469778183846522454477, phi67_158423762469778183846522454478, phi67_158423762469778183846522454479, phi67_158423762469778183846522454480, phi67_158423762469778183846522454481, phi67_158423762469778183846522454482, phi67_158423762469778183846522454483, phi67_158423762469778183846522454484, phi67_158423762469778183846522454485, phi67_158423762469778183846522454486, phi67_158423762469778183846522454487, phi67_158423762469778183846522454488, phi67_158423762469778183846522454489, phi67_158423762469778183846522454490, phi67_158423762469778183846522454491, phi67_158423762469778183846522454492, phi67_158423762469778183846522454493, phi67_158423762469778183846522454494, phi67_158423762469778183846522454495, phi67_158423762469778183846522454496, phi67_158423762469778183846522454497, phi67_158423762469778183846522454498, phi67_158423762469778183846522454499, phi67_158423762469778183846522454500]

/-- Depth `99` fails for the same reason. -/
theorem not_certifiedKill_diagonal_t67_99 :
    ¬ certifiedKill (periodLcm 67) (periodLcm 67) 99 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi67_79211881234889091923261227201, phi67_79211881234889091923261227202, phi67_79211881234889091923261227203, phi67_79211881234889091923261227204, phi67_79211881234889091923261227205, phi67_79211881234889091923261227206, phi67_79211881234889091923261227207, phi67_79211881234889091923261227208, phi67_79211881234889091923261227209, phi67_79211881234889091923261227210, phi67_79211881234889091923261227211, phi67_79211881234889091923261227212, phi67_79211881234889091923261227213, phi67_79211881234889091923261227214, phi67_79211881234889091923261227215, phi67_79211881234889091923261227216, phi67_79211881234889091923261227217, phi67_79211881234889091923261227218, phi67_79211881234889091923261227219, phi67_79211881234889091923261227220, phi67_79211881234889091923261227221, phi67_79211881234889091923261227222, phi67_79211881234889091923261227223, phi67_79211881234889091923261227224, phi67_79211881234889091923261227225, phi67_79211881234889091923261227226, phi67_79211881234889091923261227227, phi67_79211881234889091923261227228, phi67_79211881234889091923261227229, phi67_79211881234889091923261227230, phi67_79211881234889091923261227231, phi67_79211881234889091923261227232, phi67_79211881234889091923261227233, phi67_79211881234889091923261227234, phi67_79211881234889091923261227235, phi67_79211881234889091923261227236, phi67_79211881234889091923261227237, phi67_79211881234889091923261227238, phi67_79211881234889091923261227239, phi67_79211881234889091923261227240, phi67_79211881234889091923261227241, phi67_79211881234889091923261227242, phi67_79211881234889091923261227243, phi67_79211881234889091923261227244, phi67_79211881234889091923261227245, phi67_79211881234889091923261227246, phi67_79211881234889091923261227247, phi67_79211881234889091923261227248, phi67_79211881234889091923261227249, phi67_79211881234889091923261227250, phi67_79211881234889091923261227251, phi67_79211881234889091923261227252, phi67_79211881234889091923261227253, phi67_79211881234889091923261227254, phi67_79211881234889091923261227255, phi67_79211881234889091923261227256, phi67_79211881234889091923261227257, phi67_79211881234889091923261227258, phi67_79211881234889091923261227259, phi67_79211881234889091923261227260, phi67_79211881234889091923261227261, phi67_79211881234889091923261227262, phi67_79211881234889091923261227263, phi67_79211881234889091923261227264, phi67_79211881234889091923261227265, phi67_79211881234889091923261227266, phi67_79211881234889091923261227267, phi67_79211881234889091923261227268, phi67_79211881234889091923261227269, phi67_79211881234889091923261227270, phi67_79211881234889091923261227271, phi67_79211881234889091923261227272, phi67_79211881234889091923261227273, phi67_79211881234889091923261227274, phi67_79211881234889091923261227275, phi67_79211881234889091923261227276, phi67_79211881234889091923261227277, phi67_79211881234889091923261227278, phi67_79211881234889091923261227279, phi67_79211881234889091923261227280, phi67_79211881234889091923261227281, phi67_79211881234889091923261227282, phi67_79211881234889091923261227283, phi67_79211881234889091923261227284, phi67_79211881234889091923261227285, phi67_79211881234889091923261227286, phi67_79211881234889091923261227287, phi67_79211881234889091923261227288, phi67_79211881234889091923261227289, phi67_79211881234889091923261227290, phi67_79211881234889091923261227291, phi67_79211881234889091923261227292, phi67_79211881234889091923261227293, phi67_79211881234889091923261227294, phi67_79211881234889091923261227295, phi67_79211881234889091923261227296, phi67_79211881234889091923261227297, phi67_79211881234889091923261227298, phi67_79211881234889091923261227299, phi67_79211881234889091923261227300, phi67_158423762469778183846522454401, phi67_158423762469778183846522454402, phi67_158423762469778183846522454403, phi67_158423762469778183846522454404, phi67_158423762469778183846522454405, phi67_158423762469778183846522454406, phi67_158423762469778183846522454407, phi67_158423762469778183846522454408, phi67_158423762469778183846522454409, phi67_158423762469778183846522454410, phi67_158423762469778183846522454411, phi67_158423762469778183846522454412, phi67_158423762469778183846522454413, phi67_158423762469778183846522454414, phi67_158423762469778183846522454415, phi67_158423762469778183846522454416, phi67_158423762469778183846522454417, phi67_158423762469778183846522454418, phi67_158423762469778183846522454419, phi67_158423762469778183846522454420, phi67_158423762469778183846522454421, phi67_158423762469778183846522454422, phi67_158423762469778183846522454423, phi67_158423762469778183846522454424, phi67_158423762469778183846522454425, phi67_158423762469778183846522454426, phi67_158423762469778183846522454427, phi67_158423762469778183846522454428, phi67_158423762469778183846522454429, phi67_158423762469778183846522454430, phi67_158423762469778183846522454431, phi67_158423762469778183846522454432, phi67_158423762469778183846522454433, phi67_158423762469778183846522454434, phi67_158423762469778183846522454435, phi67_158423762469778183846522454436, phi67_158423762469778183846522454437, phi67_158423762469778183846522454438, phi67_158423762469778183846522454439, phi67_158423762469778183846522454440, phi67_158423762469778183846522454441, phi67_158423762469778183846522454442, phi67_158423762469778183846522454443, phi67_158423762469778183846522454444, phi67_158423762469778183846522454445, phi67_158423762469778183846522454446, phi67_158423762469778183846522454447, phi67_158423762469778183846522454448, phi67_158423762469778183846522454449, phi67_158423762469778183846522454450, phi67_158423762469778183846522454451, phi67_158423762469778183846522454452, phi67_158423762469778183846522454453, phi67_158423762469778183846522454454, phi67_158423762469778183846522454455, phi67_158423762469778183846522454456, phi67_158423762469778183846522454457, phi67_158423762469778183846522454458, phi67_158423762469778183846522454459, phi67_158423762469778183846522454460, phi67_158423762469778183846522454461, phi67_158423762469778183846522454462, phi67_158423762469778183846522454463, phi67_158423762469778183846522454464, phi67_158423762469778183846522454465, phi67_158423762469778183846522454466, phi67_158423762469778183846522454467, phi67_158423762469778183846522454468, phi67_158423762469778183846522454469, phi67_158423762469778183846522454470, phi67_158423762469778183846522454471, phi67_158423762469778183846522454472, phi67_158423762469778183846522454473, phi67_158423762469778183846522454474, phi67_158423762469778183846522454475, phi67_158423762469778183846522454476, phi67_158423762469778183846522454477, phi67_158423762469778183846522454478, phi67_158423762469778183846522454479, phi67_158423762469778183846522454480, phi67_158423762469778183846522454481, phi67_158423762469778183846522454482, phi67_158423762469778183846522454483, phi67_158423762469778183846522454484, phi67_158423762469778183846522454485, phi67_158423762469778183846522454486, phi67_158423762469778183846522454487, phi67_158423762469778183846522454488, phi67_158423762469778183846522454489, phi67_158423762469778183846522454490, phi67_158423762469778183846522454491, phi67_158423762469778183846522454492, phi67_158423762469778183846522454493, phi67_158423762469778183846522454494, phi67_158423762469778183846522454495, phi67_158423762469778183846522454496, phi67_158423762469778183846522454497, phi67_158423762469778183846522454498, phi67_158423762469778183846522454499, phi67_158423762469778183846522454500]

/-- **The twenty-ninth diagonal certificate.**  The first cell above the
`t ≤ 66` band fires at depth `100`. -/
theorem certifiedKill_diagonal_t67 :
    certifiedKill (periodLcm 67) (periodLcm 67) 100 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi67_79211881234889091923261227201, phi67_79211881234889091923261227202, phi67_79211881234889091923261227203, phi67_79211881234889091923261227204, phi67_79211881234889091923261227205, phi67_79211881234889091923261227206, phi67_79211881234889091923261227207, phi67_79211881234889091923261227208, phi67_79211881234889091923261227209, phi67_79211881234889091923261227210, phi67_79211881234889091923261227211, phi67_79211881234889091923261227212, phi67_79211881234889091923261227213, phi67_79211881234889091923261227214, phi67_79211881234889091923261227215, phi67_79211881234889091923261227216, phi67_79211881234889091923261227217, phi67_79211881234889091923261227218, phi67_79211881234889091923261227219, phi67_79211881234889091923261227220, phi67_79211881234889091923261227221, phi67_79211881234889091923261227222, phi67_79211881234889091923261227223, phi67_79211881234889091923261227224, phi67_79211881234889091923261227225, phi67_79211881234889091923261227226, phi67_79211881234889091923261227227, phi67_79211881234889091923261227228, phi67_79211881234889091923261227229, phi67_79211881234889091923261227230, phi67_79211881234889091923261227231, phi67_79211881234889091923261227232, phi67_79211881234889091923261227233, phi67_79211881234889091923261227234, phi67_79211881234889091923261227235, phi67_79211881234889091923261227236, phi67_79211881234889091923261227237, phi67_79211881234889091923261227238, phi67_79211881234889091923261227239, phi67_79211881234889091923261227240, phi67_79211881234889091923261227241, phi67_79211881234889091923261227242, phi67_79211881234889091923261227243, phi67_79211881234889091923261227244, phi67_79211881234889091923261227245, phi67_79211881234889091923261227246, phi67_79211881234889091923261227247, phi67_79211881234889091923261227248, phi67_79211881234889091923261227249, phi67_79211881234889091923261227250, phi67_79211881234889091923261227251, phi67_79211881234889091923261227252, phi67_79211881234889091923261227253, phi67_79211881234889091923261227254, phi67_79211881234889091923261227255, phi67_79211881234889091923261227256, phi67_79211881234889091923261227257, phi67_79211881234889091923261227258, phi67_79211881234889091923261227259, phi67_79211881234889091923261227260, phi67_79211881234889091923261227261, phi67_79211881234889091923261227262, phi67_79211881234889091923261227263, phi67_79211881234889091923261227264, phi67_79211881234889091923261227265, phi67_79211881234889091923261227266, phi67_79211881234889091923261227267, phi67_79211881234889091923261227268, phi67_79211881234889091923261227269, phi67_79211881234889091923261227270, phi67_79211881234889091923261227271, phi67_79211881234889091923261227272, phi67_79211881234889091923261227273, phi67_79211881234889091923261227274, phi67_79211881234889091923261227275, phi67_79211881234889091923261227276, phi67_79211881234889091923261227277, phi67_79211881234889091923261227278, phi67_79211881234889091923261227279, phi67_79211881234889091923261227280, phi67_79211881234889091923261227281, phi67_79211881234889091923261227282, phi67_79211881234889091923261227283, phi67_79211881234889091923261227284, phi67_79211881234889091923261227285, phi67_79211881234889091923261227286, phi67_79211881234889091923261227287, phi67_79211881234889091923261227288, phi67_79211881234889091923261227289, phi67_79211881234889091923261227290, phi67_79211881234889091923261227291, phi67_79211881234889091923261227292, phi67_79211881234889091923261227293, phi67_79211881234889091923261227294, phi67_79211881234889091923261227295, phi67_79211881234889091923261227296, phi67_79211881234889091923261227297, phi67_79211881234889091923261227298, phi67_79211881234889091923261227299, phi67_79211881234889091923261227300, phi67_158423762469778183846522454401, phi67_158423762469778183846522454402, phi67_158423762469778183846522454403, phi67_158423762469778183846522454404, phi67_158423762469778183846522454405, phi67_158423762469778183846522454406, phi67_158423762469778183846522454407, phi67_158423762469778183846522454408, phi67_158423762469778183846522454409, phi67_158423762469778183846522454410, phi67_158423762469778183846522454411, phi67_158423762469778183846522454412, phi67_158423762469778183846522454413, phi67_158423762469778183846522454414, phi67_158423762469778183846522454415, phi67_158423762469778183846522454416, phi67_158423762469778183846522454417, phi67_158423762469778183846522454418, phi67_158423762469778183846522454419, phi67_158423762469778183846522454420, phi67_158423762469778183846522454421, phi67_158423762469778183846522454422, phi67_158423762469778183846522454423, phi67_158423762469778183846522454424, phi67_158423762469778183846522454425, phi67_158423762469778183846522454426, phi67_158423762469778183846522454427, phi67_158423762469778183846522454428, phi67_158423762469778183846522454429, phi67_158423762469778183846522454430, phi67_158423762469778183846522454431, phi67_158423762469778183846522454432, phi67_158423762469778183846522454433, phi67_158423762469778183846522454434, phi67_158423762469778183846522454435, phi67_158423762469778183846522454436, phi67_158423762469778183846522454437, phi67_158423762469778183846522454438, phi67_158423762469778183846522454439, phi67_158423762469778183846522454440, phi67_158423762469778183846522454441, phi67_158423762469778183846522454442, phi67_158423762469778183846522454443, phi67_158423762469778183846522454444, phi67_158423762469778183846522454445, phi67_158423762469778183846522454446, phi67_158423762469778183846522454447, phi67_158423762469778183846522454448, phi67_158423762469778183846522454449, phi67_158423762469778183846522454450, phi67_158423762469778183846522454451, phi67_158423762469778183846522454452, phi67_158423762469778183846522454453, phi67_158423762469778183846522454454, phi67_158423762469778183846522454455, phi67_158423762469778183846522454456, phi67_158423762469778183846522454457, phi67_158423762469778183846522454458, phi67_158423762469778183846522454459, phi67_158423762469778183846522454460, phi67_158423762469778183846522454461, phi67_158423762469778183846522454462, phi67_158423762469778183846522454463, phi67_158423762469778183846522454464, phi67_158423762469778183846522454465, phi67_158423762469778183846522454466, phi67_158423762469778183846522454467, phi67_158423762469778183846522454468, phi67_158423762469778183846522454469, phi67_158423762469778183846522454470, phi67_158423762469778183846522454471, phi67_158423762469778183846522454472, phi67_158423762469778183846522454473, phi67_158423762469778183846522454474, phi67_158423762469778183846522454475, phi67_158423762469778183846522454476, phi67_158423762469778183846522454477, phi67_158423762469778183846522454478, phi67_158423762469778183846522454479, phi67_158423762469778183846522454480, phi67_158423762469778183846522454481, phi67_158423762469778183846522454482, phi67_158423762469778183846522454483, phi67_158423762469778183846522454484, phi67_158423762469778183846522454485, phi67_158423762469778183846522454486, phi67_158423762469778183846522454487, phi67_158423762469778183846522454488, phi67_158423762469778183846522454489, phi67_158423762469778183846522454490, phi67_158423762469778183846522454491, phi67_158423762469778183846522454492, phi67_158423762469778183846522454493, phi67_158423762469778183846522454494, phi67_158423762469778183846522454495, phi67_158423762469778183846522454496, phi67_158423762469778183846522454497, phi67_158423762469778183846522454498, phi67_158423762469778183846522454499, phi67_158423762469778183846522454500]

/-- The least certified depth at `t = 67` is exactly `100`. -/
theorem t67_minimal_depth :
    certifiedKill (periodLcm 67) (periodLcm 67) 100 ∧
      ∀ L : ℕ, L < 100 → ¬ certifiedKill (periodLcm 67) (periodLcm 67) L := by
  refine ⟨certifiedKill_diagonal_t67, fun L hL hc => ?_⟩
  have h98 := t67_depth_floor hc
  interval_cases L
  · exact not_certifiedKill_diagonal_t67_98 hc
  · exact not_certifiedKill_diagonal_t67_99 hc

/-! ### The plateau 68, 69, 70 -/

theorem pl68 : periodLcm 68 = periodLcm 67 :=
  DemandLedger.Discharge1G097.periodLcm_plateau_of_coprime_factors (a := 4) (b := 17) (s := 67)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pl69 : periodLcm 69 = periodLcm 68 :=
  DemandLedger.Discharge1G097.periodLcm_plateau_of_coprime_factors (a := 3) (b := 23) (s := 68)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pl70 : periodLcm 70 = periodLcm 69 :=
  DemandLedger.Discharge1G097.periodLcm_plateau_of_coprime_factors (a := 2) (b := 35) (s := 69)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The certified band extends from `t ≤ 66` to `t ≤ 70`.**  The next prime-power
rung is `71`. -/
theorem exists_diagonalKill_le_70 (t : ℕ) (ht : t ≤ 70) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L := by
  rcases Nat.lt_or_ge t 67 with h | h
  · exact DemandLedger.Discharge1G097.exists_diagonalKill_le_66 t (by omega)
  · interval_cases t
    · exact ⟨100, certifiedKill_diagonal_t67⟩
    · exact ⟨100, by rw [pl68]; exact certifiedKill_diagonal_t67⟩
    · exact ⟨100, by rw [pl69, pl68]; exact certifiedKill_diagonal_t67⟩
    · exact ⟨100, by rw [pl70, pl69, pl68]; exact certifiedKill_diagonal_t67⟩

end Lift
end ErdosProblems
