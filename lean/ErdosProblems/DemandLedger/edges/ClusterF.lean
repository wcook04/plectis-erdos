/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.DemandLedger.Basic

/-!
# Demand-ledger edges, cluster F — Erdős #249 totient block certificates

The four gaps `G088`, `G089`, `G090`, `G091` are the open certificate-supply
antecedents of the four #249 sockets in `Erdos249257.CertificateKernel`.
Writing

* `T K N = ∑ r ∈ Icc 1 K, φ(N+r)·2^(K-r)`  (the first-block carry sum),
* `V K N = T K N % 2^K`                     (the carry residue),
* `M K L N = ∑ r ∈ Icc (K+1) L, φ(N+r)·2^(L-r)` (the middle window),

they read

* `G088` (wave 14, digitwise): `∀ q > 0, ∃ N K L C, K ≤ L ∧ (∀ r ∈ Icc 1 K, 2^r ∣ φ(N+r))
  ∧ M K L N ≤ C ∧ q·(C + (N+L+2)) < 2^L`;
* `G089` (wave 14, carry-aware): the same with the `K` slotwise divisibilities replaced
  by the single congruence `2^K ∣ T K N`;
* `G090` (wave 15, low carry): no divisibility at all, the residue is instead paid for
  inside the height inequality, `q·(V K N·2^(L-K) + C + (N+L+2)) < 2^L`;
* `G091` (wave 17, gap): `∀ q > 0, ∃ N K, (q·V K N) % 2^K + q·(N+K+2) < 2^K` — avoid one
  thin *top* band after scaling by `q`, instead of landing in a thin bottom band.

This file establishes that the four are **totally ordered**, in the chain

  `G088 → G089 → G090 → G091`,

so `G091` is a weakest member in the implication order proved here:
a proof of `G091` discharges nothing else, but a proof of any of the other three
discharges `G091`, and a proof of `G091` alone would already give the #249
irrationality through
`Erdos249257.irrational_tsum_totient_div_pow_two_of_gap_certificate_supply`.
No strict non-implication between these statements is proved by this chain.

The three step edges are, respectively: slotwise divisibility packs into the carry sum
(`2^r ∣ φ(N+r)` and `2^(K-r)` multiply to `2^K`); an exact carry is the residue `0`;
and — the substantial one — a low-carry certificate at `(N,K,L,C)` is a gap certificate
at the *widened* window `(N,L)`, because the height inequality forces the widening
`V L N = 2^(L-K)·V K N + M K L N` to happen without wraparound, and then forces
`q·V L N < 2^L` so the outer `% 2^L` in the gap statement is the identity.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace DemandLedger.ClusterF

/-! ## Window widening for the totient carry sum -/

/-- **Carry-sum widening.**  For `K ≤ L` the `L`-window carry sum decomposes into the
scaled `K`-window carry sum plus the middle window:
`T L N = 2^(L-K)·T K N + M K L N`. -/
private lemma totient_carry_sum_widen (N K L : ℕ) (hKL : K ≤ L) :
    (∑ r ∈ Finset.Icc 1 L, Nat.totient (N + r) * 2 ^ (L - r))
      = 2 ^ (L - K) * (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r))
        + ∑ r ∈ Finset.Icc (K + 1) L, Nat.totient (N + r) * 2 ^ (L - r) := by
  have hIccL : Finset.Icc 1 L = Finset.Ico 1 (L + 1) := by
    ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hIccK : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
    ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hIccM : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
    ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hsplit : (∑ r ∈ Finset.Ico 1 (L + 1), Nat.totient (N + r) * 2 ^ (L - r))
      = (∑ r ∈ Finset.Ico 1 (K + 1), Nat.totient (N + r) * 2 ^ (L - r))
        + ∑ r ∈ Finset.Ico (K + 1) (L + 1), Nat.totient (N + r) * 2 ^ (L - r) :=
    (Finset.sum_Ico_consecutive _ (by omega) (by omega)).symm
  have hpart : (∑ r ∈ Finset.Ico 1 (K + 1), Nat.totient (N + r) * 2 ^ (L - r))
      = 2 ^ (L - K) * (∑ r ∈ Finset.Ico 1 (K + 1), Nat.totient (N + r) * 2 ^ (K - r)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrK : r ≤ K := by
      have := Finset.mem_Ico.mp hr
      omega
    have hpow : (2 : ℕ) ^ (L - r) = 2 ^ (L - K) * 2 ^ (K - r) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    ring
  rw [hIccL, hIccK, hIccM, hsplit, hpart]

/-- **Carry-sum widening, residue form.**  The `L`-window carry sum, written so that its
class mod `2^L` is visible: `T L N = (2^(L-K)·V K N + M K L N) + 2^L·⌊T K N / 2^K⌋`. -/
private lemma totient_carry_sum_widen_residue (N K L : ℕ) (hKL : K ≤ L) :
    (∑ r ∈ Finset.Icc 1 L, Nat.totient (N + r) * 2 ^ (L - r))
      = 2 ^ (L - K) * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K)
          + (∑ r ∈ Finset.Icc (K + 1) L, Nat.totient (N + r) * 2 ^ (L - r))
          + 2 ^ L * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) / 2 ^ K) := by
  rw [totient_carry_sum_widen N K L hKL]
  generalize (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) = S
  generalize (∑ r ∈ Finset.Icc (K + 1) L, Nat.totient (N + r) * 2 ^ (L - r)) = M
  have hdm : 2 ^ K * (S / 2 ^ K) + S % 2 ^ K = S := Nat.div_add_mod S (2 ^ K)
  have hpow : (2 : ℕ) ^ (L - K) * 2 ^ K = 2 ^ L := by
    rw [← pow_add]
    congr 1
    omega
  calc 2 ^ (L - K) * S + M
      = 2 ^ (L - K) * (2 ^ K * (S / 2 ^ K) + S % 2 ^ K) + M := by rw [hdm]
    _ = 2 ^ (L - K) * (S % 2 ^ K) + M + 2 ^ (L - K) * 2 ^ K * (S / 2 ^ K) := by ring
    _ = 2 ^ (L - K) * (S % 2 ^ K) + M + 2 ^ L * (S / 2 ^ K) := by rw [hpow]

/-- **The arithmetic core of `G090 → G091`.**  Purely about naturals: if the low-carry
height inequality `q·(V·P + C + (N+L+2)) < 2^L` holds and the middle window `M` is
bounded by `C`, then the widened residue `P·V + M` is already reduced mod `2^L`, its
`q`-multiple is still below `2^L`, and the gap inequality follows. -/
private lemma gap_band_of_low_carry_arith (q V P M C N L z : ℕ) (hq : 0 < q)
    (hM : M ≤ C) (harith : q * (V * P + C + (N + L + 2)) < 2 ^ L) :
    q * ((P * V + M + 2 ^ L * z) % 2 ^ L) % 2 ^ L + q * (N + L + 2) < 2 ^ L := by
  have hPV : P * V = V * P := Nat.mul_comm P V
  have hbase : V * P + M + (N + L + 2) ≤ q * (V * P + C + (N + L + 2)) := by
    refine le_trans ?_ (Nat.le_mul_of_pos_left _ hq)
    omega
  have hsmall : P * V + M < 2 ^ L := by omega
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]
  have hle : q * (P * V + M) ≤ q * (V * P + C) := Nat.mul_le_mul (le_refl q) (by omega)
  have hsplitq : q * (V * P + C + (N + L + 2))
      = q * (V * P + C) + q * (N + L + 2) := by ring
  have hlt : q * (P * V + M) < 2 ^ L := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-! ## The chain -/

/-- **Edge `G088 → G089`.**  Slotwise first-block divisibility packs into a single
congruence on the carry sum: `2^r ∣ φ(N+r)` and the slot weight `2^(K-r)` multiply to
`2^K` in every term of `T K N`, so `2^K ∣ T K N`.  Same window, same `L`, same `C`. -/
theorem e_G088_G089 : G088 → G089 := by
  unfold G088 G089
  intro h q hq
  obtain ⟨N, K, L, C, hKL, hblock, hmid, harith⟩ := h q hq
  refine ⟨N, K, L, C, hKL, ?_, hmid, harith⟩
  refine Finset.dvd_sum fun r hr => ?_
  have hrK : r ≤ K := (Finset.mem_Icc.mp hr).2
  obtain ⟨m, hm⟩ := hblock r hr
  refine ⟨m, ?_⟩
  have hpow : (2 : ℕ) ^ r * 2 ^ (K - r) = 2 ^ K := by
    rw [← pow_add]
    congr 1
    omega
  rw [hm, ← hpow]
  ring

/-- **Edge `G089 → G090`.**  An exact first-block carry is the residue `0`, and the
low-carry height inequality at residue `0` is literally the wave-14 one.  This is the
ledger-level shadow of `Erdos249257.irrational_coeff_series_of_carry_via_low_carry`. -/
theorem e_G089_G090 : G089 → G090 := by
  unfold G089 G090
  intro h q hq
  obtain ⟨N, K, L, C, hKL, hcarry, hmid, harith⟩ := h q hq
  refine ⟨N, K, L, C, hKL, hmid, ?_⟩
  obtain ⟨m, hm⟩ := hcarry
  have hV0 : (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K = 0 := by
    rw [hm]
    exact Nat.mul_mod_right (2 ^ K) m
  simpa [hV0] using harith

/-- **Edge `G090 → G091`.**  A low-carry certificate at `(N, K, L, C)` is a gap
certificate at the widened window `(N, L)`.

The height inequality `q·(V K N·2^(L-K) + C + (N+L+2)) < 2^L` already forces
`2^(L-K)·V K N + M K L N < 2^L`, so the widening
`T L N ≡ 2^(L-K)·V K N + M K L N (mod 2^L)` is exact: `V L N = 2^(L-K)·V K N + M K L N`.
The same inequality then gives `q·V L N + q·(N+L+2) < 2^L`, so the outer reduction
`(q·V L N) % 2^L` in the gap statement does nothing and the gap inequality holds.

This is the ledger-level counterpart of
`Erdos249257.totient_gap_certificate_of_low_carry_certificate`, which handles only the
already-widened case `L = K`. -/
theorem e_G090_G091 : G090 → G091 := by
  unfold G090 G091
  intro h q hq
  obtain ⟨N, K, L, C, hKL, hmid, harith⟩ := h q hq
  refine ⟨N, L, ?_⟩
  rw [totient_carry_sum_widen_residue N K L hKL]
  exact gap_band_of_low_carry_arith q _ _ _ C N L _ hq hmid harith

/-- **Edge `G088 → G090`** (composite). -/
theorem e_G088_G090 : G088 → G090 := fun h => e_G089_G090 (e_G088_G089 h)

/-- **Edge `G089 → G091`** (composite). -/
theorem e_G089_G091 : G089 → G091 := fun h => e_G090_G091 (e_G089_G090 h)

/-- **Edge `G088 → G091`** (composite).  The digitwise wave-14 certificate supply is the
strongest of the four and discharges the whole cluster. -/
theorem e_G088_G091 : G088 → G091 := fun h => e_G090_G091 (e_G088_G090 h)

/-! ## Off-cluster: `G090` and `G092` are the same demand

`G092` is the antecedent of
`Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_low_carry_full_block_certificates`,
the `L = K, C = 0` specialisation of `G090`.  It carries its own frontier records, but it
is not a separate level of the ladder: the middle window and the free constant `C` in
`G090` buy nothing, because widening the window from `K` to `L` absorbs them.  Names are
suffixed `_clusterF` so this file can coexist with a cluster that owns `G092`. -/

/-- **The arithmetic core of `G090 → G092`.**  Same widening as
`gap_band_of_low_carry_arith`, landing in the full-block (bottom-band) shape. -/
private lemma full_block_of_low_carry_arith (q V P M C N L z : ℕ) (hq : 0 < q)
    (hM : M ≤ C) (harith : q * (V * P + C + (N + L + 2)) < 2 ^ L) :
    q * ((P * V + M + 2 ^ L * z) % 2 ^ L + (N + L + 2)) < 2 ^ L := by
  have hPV : P * V = V * P := Nat.mul_comm P V
  have hbase : V * P + M + (N + L + 2) ≤ q * (V * P + C + (N + L + 2)) := by
    refine le_trans ?_ (Nat.le_mul_of_pos_left _ hq)
    omega
  have hsmall : P * V + M < 2 ^ L := by omega
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]
  have hle : q * (P * V + M + (N + L + 2)) ≤ q * (V * P + C + (N + L + 2)) :=
    Nat.mul_le_mul (le_refl q) (by omega)
  omega

/-- **Edge `G092 → G090`.**  A full-block certificate is the `L = K, C = 0` case. -/
theorem e_G092_G090_clusterF : G092 → G090 := by
  unfold G092 G090
  intro h q hq
  obtain ⟨N, K, hcert⟩ := h q hq
  refine ⟨N, K, K, 0, le_refl K, ?_, ?_⟩
  · rw [Finset.Icc_eq_empty (by omega)]
    simp
  · simpa [Nat.sub_self] using hcert

/-- **Edge `G090 → G092`.**  Widening the window to `L` folds the middle window and the
constant `C` back into the residue, so the general low-carry demand is no weaker than its
own full-block specialisation. -/
theorem e_G090_G092_clusterF : G090 → G092 := by
  unfold G090 G092
  intro h q hq
  obtain ⟨N, K, L, C, hKL, hmid, harith⟩ := h q hq
  refine ⟨N, L, ?_⟩
  rw [totient_carry_sum_widen_residue N K L hKL]
  exact full_block_of_low_carry_arith q _ _ _ C N L _ hq hmid harith

/-- **`G090` and `G092` are equivalent.**  Two frontier records, one demand. -/
theorem e_G090_iff_G092_clusterF : G090 ↔ G092 :=
  ⟨e_G090_G092_clusterF, e_G092_G090_clusterF⟩

end DemandLedger.ClusterF
