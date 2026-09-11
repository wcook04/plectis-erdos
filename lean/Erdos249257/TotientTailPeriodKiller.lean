import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# The totient-tail period killer: attacking #249 through the period, not the digits

Every earlier wave asked the Erdős–Borwein question of `S = ∑ φ(n)/2ⁿ`: force a
long block of zero binary digits.  Wave 20 measured why that fails — the
totient's 2-adic staircase affords `√(2·log₂ N)` silent positions where the
proof engine needs `log₂ N`.  This file changes the TARGET.  Rationality of `S`
is equivalent to *eventual periodicity* of its binary expansion, and
periodicity is a statement about the local totient tail

  `R_N = ∑_{j≥1} φ(N+j)/2ʲ`,      because `2^N·S = Φ_N + R_N` with `Φ_N ∈ ℕ`.

If `S = P/Q` then for `h` with `oddPart Q ∣ 2ʰ - 1` and every `N ≥ v₂(Q)`,

  `R_{N+h} - R_N ∈ ℤ`   —   the **tail-period law**.

Killing a period is a FINITE, decidable act.  With the window discrepancy

  `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`

we get `R_{N+h} - R_N = A/2^L + E`, `|E| ≤ (N+h+L+2)/2^L`, so whenever the
residue `A mod 2^L` lands outside the radius-`(N+h+L+2)` neighbourhood of `0`,
the difference is provably NOT an integer (`tail_diff_notMem_int_of_certifiedKill`).
The forbidden zone has width `O(N)` inside a modulus `2^L ≈ N³`: the old proof
had to HIT a measure-zero target, this one only has to MISS a vanishing one.

The reduction is complete (`irrational_totient_series_of_certificate_supply`):
a supply of certified kills — for every period `h` and every threshold `N₀`
some certified `(N ≥ N₀, L)` — proves #249.  As a first unconditional deposit,
`certifiedKill_all_small` machine-checks kills for every `h ≤ 8` at `N = 12`,
`L = 16`, so `S` is not a rational whose denominator divides `2¹²·(2ʰ-1)` for
any `h ≤ 8` (`totient_series_ne_rat_of_den_dvd`).

Everything here is elementary: `φ(n) ≤ n`, geometric tails, and integer
window arithmetic.  No q-Padé, no Stern–Brocot, no unformalised citations.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`:
the fractional layer of `2^N · S`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. -/
def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)

/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`:
the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. -/
def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L`
avoids the radius-`(N+h+L+2)` neighbourhood of `0`. -/
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

/-- Every endpoint certificate has enough dyadic room for both excluded
boundary arcs.  In particular, certificate depth cannot remain fixed while
`N+h` tends to infinity. -/
theorem certifiedKill_depth_floor {h N L : ℕ} (hcert : certifiedKill h N L) :
    (2 * (N + h + L + 2) : ℤ) < 2 ^ L := by
  rcases hcert with ⟨hleft, hright⟩
  linarith

instance (h N L : ℕ) : Decidable (certifiedKill h N L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Geometric-linear summability spine -/

private lemma div_two_pow_eq (a : ℝ) (n : ℕ) : a / 2 ^ n = a * (1 / 2 : ℝ) ^ n := by
  rw [div_pow, one_pow]
  ring

private lemma summable_linear_half : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
  simpa using summable_pow_mul_geometric_of_norm_lt_one 1
    (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)

private lemma summable_const_add_mul_half (C : ℝ) :
    Summable (fun j : ℕ => (C + (j : ℝ)) * (1 / 2 : ℝ) ^ j) := by
  have h1 : Summable (fun j : ℕ => C * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  exact (h1.add summable_linear_half).congr fun j => by ring

private lemma tsum_const_add_mul_half (C : ℝ) :
    ∑' j : ℕ, (C + (j : ℝ)) * (1 / 2 : ℝ) ^ j = 2 * C + 2 := by
  have h1 : Summable (fun j : ℕ => C * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have hgeo : ∑' j : ℕ, (1 / 2 : ℝ) ^ j = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hlin : ∑' j : ℕ, (j : ℝ) * (1 / 2 : ℝ) ^ j = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs]; norm_num)]
    norm_num
  calc ∑' j : ℕ, (C + (j : ℝ)) * (1 / 2 : ℝ) ^ j
      = ∑' j : ℕ, (C * (1 / 2 : ℝ) ^ j + (j : ℝ) * (1 / 2 : ℝ) ^ j) :=
        tsum_congr fun j => by ring
    _ = (∑' j : ℕ, C * (1 / 2 : ℝ) ^ j) + ∑' j : ℕ, (j : ℝ) * (1 / 2 : ℝ) ^ j :=
        Summable.tsum_add h1 summable_linear_half
    _ = C * (∑' j : ℕ, (1 / 2 : ℝ) ^ j) + 2 := by rw [tsum_mul_left, hlin]
    _ = 2 * C + 2 := by rw [hgeo]; ring

/-- The tail terms of `totientTail` are summable. -/
lemma summable_totientTail_terms (M : ℕ) :
    Summable (fun j : ℕ => (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1)) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (((summable_const_add_mul_half ((M : ℝ) + 1)).mul_right (1 / 2)))
  have hb : (Nat.totient (M + 1 + j) : ℝ) ≤ (M : ℝ) + 1 + (j : ℝ) := by
    have h0 : (Nat.totient (M + 1 + j) : ℝ) ≤ ((M + 1 + j : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.totient_le _)
    push_cast at h0
    linarith
  calc (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1)
      ≤ ((M : ℝ) + 1 + (j : ℝ)) / 2 ^ (j + 1) := by gcongr
    _ = ((M : ℝ) + 1 + (j : ℝ)) * (1 / 2 : ℝ) ^ j * (1 / 2) := by
        rw [div_pow, one_pow, pow_succ]
        ring

/-- The full totient series is summable. -/
lemma summable_totient_div_two_pow :
    Summable (fun n : ℕ => (Nat.totient n : ℝ) / 2 ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) summable_linear_half
  have hb : (Nat.totient n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.totient_le n
  calc (Nat.totient n : ℝ) / 2 ^ n ≤ (n : ℝ) / 2 ^ n := by gcongr
    _ = (n : ℝ) * (1 / 2 : ℝ) ^ n := div_two_pow_eq _ n

/-! ## The shift identity: `2^N · S = Φ_N + R_N` -/

/-- **Shift identity.** `2^N` times the #249 constant splits as integer prefix plus
the local totient tail.  This is what makes the binary expansion of `S` a statement
about `R_N`. -/
theorem two_pow_mul_totient_series_eq (N : ℕ) :
    (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (totientPrefix N : ℝ) + totientTail N := by
  have hS := summable_totient_div_two_pow
  have hsplit := hS.sum_add_tsum_nat_add (N + 1)
  rw [← hsplit, mul_add]
  congr 1
  · -- prefix: 2^N · ∑_{n<N+1} φ(n)/2^n = Φ_N
    rw [Finset.mul_sum]
    unfold totientPrefix
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hpow : (2 : ℝ) ^ N = 2 ^ (N - n) * 2 ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
    rw [hpow, mul_assoc, mul_comm ((2 : ℝ) ^ n), div_mul_cancel₀ _ h2n, mul_comm]
  · -- tail: 2^N · ∑' j, φ(j+(N+1))/2^(j+(N+1)) = totientTail N
    rw [← tsum_mul_left]
    unfold totientTail
    refine tsum_congr fun j => ?_
    have harg : j + (N + 1) = N + 1 + j := by omega
    rw [harg]
    have hexp : (2 : ℝ) ^ (N + 1 + j) = 2 ^ (j + 1) * 2 ^ N := by
      rw [← pow_add]
      congr 1
      omega
    have h2 : (2 : ℝ) ^ N ≠ 0 := by positivity
    rw [hexp, div_mul_eq_div_div, mul_comm, div_mul_cancel₀ _ h2]

/-! ## Truncation: partial window plus bounded tail -/

/-- Exact decomposition of the tail at window depth `L`. -/
lemma totientTail_eq_partial_add_tail (M L : ℕ) :
    totientTail M
      = (∑ j ∈ Finset.range L, (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1))
        + ∑' j : ℕ, (Nat.totient (M + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) :=
  ((summable_totientTail_terms M).sum_add_tsum_nat_add L).symm

/-- The deep tail is nonnegative. -/
lemma tail_after_nonneg (M L : ℕ) :
    0 ≤ ∑' j : ℕ, (Nat.totient (M + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) :=
  tsum_nonneg fun j => by positivity

/-- The deep tail after `L` window terms is at most `(M+L+2)/2^L` — the only
analytic input is `φ(n) ≤ n` against a geometric-linear majorant. -/
lemma tail_after_le (M L : ℕ) :
    ∑' j : ℕ, (Nat.totient (M + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
      ≤ ((M : ℝ) + L + 2) / 2 ^ L := by
  have hsum : Summable (fun j : ℕ => (Nat.totient (M + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)) :=
    (summable_nat_add_iff L).mpr (summable_totientTail_terms M)
  have hmaj : Summable
      (fun j : ℕ => (((M : ℝ) + L + 1) + (j : ℝ)) * (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (L + 1)) :=
    (summable_const_add_mul_half ((M : ℝ) + L + 1)).mul_right _
  have hle : ∀ j : ℕ,
      (Nat.totient (M + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
        ≤ (((M : ℝ) + L + 1) + (j : ℝ)) * (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (L + 1) := by
    intro j
    have hb : (Nat.totient (M + 1 + (j + L)) : ℝ) ≤ ((M : ℝ) + L + 1) + (j : ℝ) := by
      have h0 : (Nat.totient (M + 1 + (j + L)) : ℝ) ≤ ((M + 1 + (j + L) : ℕ) : ℝ) :=
        Nat.cast_le.mpr (Nat.totient_le _)
      push_cast at h0
      linarith
    calc (Nat.totient (M + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
        ≤ (((M : ℝ) + L + 1) + (j : ℝ)) / 2 ^ ((j + L) + 1) := by gcongr
      _ = (((M : ℝ) + L + 1) + (j : ℝ)) * (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (L + 1) := by
          rw [div_pow, one_pow, div_pow, one_pow]
          have : (2 : ℝ) ^ ((j + L) + 1) = 2 ^ j * 2 ^ (L + 1) := by
            rw [show j + L + 1 = j + (L + 1) from by omega, pow_add]
          rw [this]
          ring
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have h2L1 : (0 : ℝ) < 2 ^ (L + 1) := by positivity
  calc ∑' j : ℕ, (Nat.totient (M + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
      ≤ ∑' j : ℕ, (((M : ℝ) + L + 1) + (j : ℝ)) * (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (L + 1) :=
        Summable.tsum_le_tsum hle hsum hmaj
    _ = (∑' j : ℕ, (((M : ℝ) + L + 1) + (j : ℝ)) * (1 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ (L + 1) :=
        tsum_mul_right
    _ = (2 * ((M : ℝ) + L + 1) + 2) * (1 / 2 : ℝ) ^ (L + 1) := by
        rw [tsum_const_add_mul_half]
    _ = ((M : ℝ) + L + 2) / 2 ^ L := by
        rw [div_pow, one_pow]
        rw [show (2 : ℝ) ^ (L + 1) = 2 ^ L * 2 from by rw [pow_succ]]
        field_simp [h2L.ne']
        ring

/-! ## Certificate soundness: a good residue kills integrality -/

/-- The window discrepancy over `2^L` is the difference of the two partial windows. -/
lemma windowDiscrepancy_div_eq (h N L : ℕ) :
    ((windowDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L
      = (∑ j ∈ Finset.range L, (Nat.totient (N + h + 1 + j) : ℝ) / 2 ^ (j + 1))
        - ∑ j ∈ Finset.range L, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1) := by
  unfold windowDiscrepancy
  push_cast
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjL : j < L := Finset.mem_range.mp hj
  have hsplit : (2 : ℝ) ^ L = 2 ^ (L - 1 - j) * 2 ^ (j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : (2 : ℝ) ^ (j + 1) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ (L - 1 - j) ≠ 0 := by positivity
  rw [hsplit]
  field_simp

/-- **Certificate soundness.**  If the residue of `A_{h,N,L}` modulo `2^L` avoids the
radius-`(N+h+L+2)` neighbourhood of `0`, then `R_{N+h} - R_N` is not an integer:
period `h` is dead at position `N`. -/
theorem tail_diff_notMem_int_of_certifiedKill {h N L : ℕ} (hcert : certifiedKill h N L) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨k, hk⟩
  obtain ⟨hlow, hhigh⟩ := hcert
  have hdec1 := totientTail_eq_partial_add_tail (N + h) L
  have hdec2 := totientTail_eq_partial_add_tail N L
  have hA := windowDiscrepancy_div_eq h N L
  have hT1n := tail_after_nonneg (N + h) L
  have hT2n := tail_after_nonneg N L
  have hT1u := tail_after_le (N + h) L
  have hT2u := tail_after_le N L
  push_cast at hT1u
  rw [hdec1, hdec2] at hk
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  set A := windowDiscrepancy h N L with hAdef
  set T1 := ∑' j : ℕ, (Nat.totient (N + h + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT1def
  set T2 := ∑' j : ℕ, (Nat.totient (N + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT2def
  have hk' : ((k : ℤ) : ℝ) = (A : ℝ) / 2 ^ L + (T1 - T2) := by
    rw [hA]
    linarith [hk]
  have hmul : ((k : ℤ) : ℝ) * 2 ^ L = (A : ℝ) + (T1 - T2) * 2 ^ L := by
    rw [hk', add_mul, div_mul_cancel₀ _ h2L.ne']
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
  have hAk : (A : ℝ) - ((k : ℤ) : ℝ) * 2 ^ L = -((T1 - T2) * 2 ^ L) := by
    linarith [hmul]
  have habs : |(A : ℝ) - ((k : ℤ) : ℝ) * 2 ^ L| ≤ (N : ℝ) + h + L + 2 := by
    rw [hAk, abs_neg]
    exact habs2
  have hint : |A - k * 2 ^ L| ≤ (N : ℤ) + h + L + 2 := by exact_mod_cast habs
  set P : ℤ := 2 ^ L with hP
  have hPpos : (0 : ℤ) < P := by rw [hP]; positivity
  set x : ℤ := A - k * P with hx
  have hxmod : x % P = A % P := by
    have hrw : x = A + P * (-k) := by rw [hx]; ring
    rw [hrw, Int.add_mul_emod_self_left]
  have hdm : P * (x / P) + A % P = x := by
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

/-! ## Rationality forces the tail-period law -/

/-- If `S = r ∈ ℚ` and `r.den ∣ 2^N·(2^h - 1)`, the `(h, N)` tail difference is an
integer.  This is the sharp form: any `h` whose Mersenne number kills the odd part
of the denominator works, with pre-period exactly `v₂(den)`. -/
theorem tail_diff_int_of_den_dvd (r : ℚ)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (r : ℝ))
    (h N : ℕ) (hdvd : (r.den : ℕ) ∣ 2 ^ N * (2 ^ h - 1)) :
    totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  have h1 := two_pow_mul_totient_series_eq (N + h)
  have h2 := two_pow_mul_totient_series_eq N
  rw [hS] at h1 h2
  have ht1 : totientTail (N + h)
      = (2 : ℝ) ^ N * 2 ^ h * (r : ℝ) - (totientPrefix (N + h) : ℝ) := by
    rw [← pow_add]
    linarith [h1]
  have ht2 : totientTail N = (2 : ℝ) ^ N * (r : ℝ) - (totientPrefix N : ℝ) := by
    linarith [h2]
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨(c : ℤ) * r.num + (totientPrefix N : ℤ) - (totientPrefix (N + h) : ℤ), ?_⟩
  have hden : ((r.den : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_pos.ne'
  have hpow1 : (1 : ℕ) ≤ 2 ^ h := Nat.one_le_pow _ _ (by norm_num)
  have hcastK : ((2 ^ N * (2 ^ h - 1) : ℕ) : ℝ) = (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hpow1]
    push_cast
    ring
  have hKr : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * (r : ℝ) = (((c : ℤ) * r.num : ℤ) : ℝ) := by
    rw [← hcastK, hc, Rat.cast_def]
    push_cast
    field_simp
  rw [ht1, ht2]
  push_cast at hKr ⊢
  linarith [hKr]

/-- **Tail-period law.**  If the totient series is rational, some period `h ≥ 1`
makes every shifted tail difference an integer from the pre-period `v₂(den)` on. -/
theorem eventual_period_of_not_irrational
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  have hmem : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ∈ Set.range ((↑) : ℚ → ℝ) := by
    by_contra hmem
    exact hrat hmem
  obtain ⟨r, hr⟩ := hmem
  have hq0 : r.den ≠ 0 := r.den_pos.ne'
  have hm0 : 0 < ordCompl[2] r.den := Nat.ordCompl_pos 2 hq0
  have hcop : Nat.Coprime 2 (ordCompl[2] r.den) :=
    Nat.coprime_ordCompl Nat.prime_two hq0
  refine ⟨Nat.totient (ordCompl[2] r.den), Nat.totient_pos.mpr hm0,
    r.den.factorization 2, fun N hN => ?_⟩
  apply tail_diff_int_of_den_dvd r hr.symm
  have heuler : (2 : ℕ) ^ Nat.totient (ordCompl[2] r.den) ≡ 1 [MOD ordCompl[2] r.den] :=
    Nat.ModEq.pow_totient hcop
  have hmdvd : ordCompl[2] r.den ∣ 2 ^ Nat.totient (ordCompl[2] r.den) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp heuler.symm
  have h2a : (2 : ℕ) ^ r.den.factorization 2 ∣ 2 ^ N := pow_dvd_pow 2 hN
  have hqfact : 2 ^ r.den.factorization 2 * ordCompl[2] r.den = r.den :=
    Nat.ordProj_mul_ordCompl_eq_self r.den 2
  have hcop2 : Nat.Coprime (2 ^ r.den.factorization 2) (ordCompl[2] r.den) :=
    Nat.Coprime.pow_left _ hcop
  have hmul : 2 ^ r.den.factorization 2 * ordCompl[2] r.den
      ∣ 2 ^ N * (2 ^ Nat.totient (ordCompl[2] r.den) - 1) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2
      (dvd_mul_of_dvd_left h2a _) (dvd_mul_of_dvd_right hmdvd _)
  rwa [hqfact] at hmul

/-! ## The reduction, and the first unconditional deposits -/

/-- **The wave-21 reduction (the throat of #249).**  A certified period-kill supply —
for every period `h ≥ 1` and every threshold `N₀`, a certified kill at some
`(N ≥ N₀, L)` — proves the totient series irrational.  Each individual certificate
is a finite, decidable residue computation. -/
theorem irrational_totient_series_of_certificate_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨h, hpos, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  obtain ⟨N, hN, L, hkill⟩ := hsupply h hpos N₀
  exact tail_diff_notMem_int_of_certifiedKill hkill (hint N hN)

/-- Machine-checked kills: for every period `h ∈ [1,8]` the residue certificate
holds at `(N, L) = (12, 16)`.  Kernel-decidable: 256 totient values below 37. -/
theorem certifiedKill_all_small : ∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16 := by decide

/-- No shifted tail difference with period `h ≤ 8` is an integer at `N = 12`. -/
theorem tail_diff_not_int_small (h : ℕ) (h1 : 1 ≤ h) (h8 : h ≤ 8) :
    totientTail (12 + h) - totientTail 12 ∉ Set.range ((↑) : ℤ → ℝ) :=
  tail_diff_notMem_int_of_certifiedKill
    (certifiedKill_all_small h (Finset.mem_Icc.mpr ⟨h1, h8⟩))

/-- **Concrete denominator exclusion.**  The totient series equals no rational whose
denominator divides `2¹²·(2ʰ-1)` for some `1 ≤ h ≤ 8`: no dyadic rational with
denominator up to `2¹²`, and no `k/(2ᵃ·m)` with `a ≤ 12` and the multiplicative
order of `2` mod `m` at most `8`. -/
theorem totient_series_ne_rat_of_den_dvd (r : ℚ) (h : ℕ) (h1 : 1 ≤ h) (h8 : h ≤ 8)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 12 * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := fun hS =>
  tail_diff_not_int_small h h1 h8 (tail_diff_int_of_den_dvd r hS h 12 hdvd)

end TotientTailPeriodKiller
end Erdos249257
