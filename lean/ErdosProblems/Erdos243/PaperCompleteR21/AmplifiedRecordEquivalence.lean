import ErdosProblems.Erdos243.PaperCompleteR21.ReducedDenominatorPrimePowers
import ErdosProblems.Erdos243.SlowRiseBarrier
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Order.LiminfLimsup

/-!
# Erdős 243: amplified record increments and the critical rate

This file proves the two remaining environments of
`paper/reasoning-parts/erdos243/core.tex`, §`long243:sec:records`:

* `long243:res:recordamplified` — under the standing hypotheses, eventual
  Sylvester behaviour, `limsup 𝒜 n < ∞` and `limsup (R n * δ n) < ∞` are
  equivalent, and each of those two limits superior is `0` or `+∞`;
* `long243:res:criticalrate` — under the standing hypotheses and
  `δ n = O(1/n)`, eventual Sylvester behaviour is equivalent to `u n = O(n)`
  and to `(-ẽ n)₊ = O(1)`, so a counterexample at the critical rate has
  `limsup u n / n = ∞` and `limsup (-ẽ n)₊ = ∞`.

The standing hypotheses and the objects `C`, `D`, `E`, `G`, `u`, `v`, `ẽ`, `h`,
`w`, `R`, `H`, `m`, `𝒜`, `δ` are the ones transcribed in
`ReducedDenominatorPrimePowers.lean` (structure `StandingOrbit`), whose
`oddpowersupply` and `unitrecord` theorems that file already proves.

The mathematical content added here, in the paper's own order, is:

1. *The multiplier supply.*  With `L n = lcm (q, a 0, …, a (n-1))` and
   `M n = D n / L n`, the finite telescoping identity gives `M n ∣ C n`,
   `M 0 = 1` and `M (n+1) = gcd (L n) (a n) * M n`.  Since `log C n = o(n)`
   (already available as `Hmax_pow_envelope`), `gcd (a n, D n) = 1` cannot fail
   from some index on: a multiplier coprime to the accumulated denominator
   occurs at arbitrarily late indices.  The paper takes a density-one count from
   Bado's Theorem 9.1; only cofinality is used below, and it needs nothing more
   than the same telescoping identity.
2. *The general-`h` release.*  At such a step `h n = 1` and `a n ∣ v (n+1)`; the
   chosen multipliers are pairwise coprime, and a pigeonhole on their smallest
   prime factors (all distinct, and a prime that has already entered `D` can
   never divide a later coprime multiplier) supplies multipliers with a prime
   factor above any fixed bound.
3. *The `K`-increment cut for an arbitrarily cancelled reduced orbit.*  Under
   `𝒜 n ≤ K` one gets `m n ≤ K`, hence `u (n+1) ≤ u n + K`, and `2 h s ≤ 3 K`,
   hence `h s < 2K`, from the estimate at the first later negative error.
   Primes `p > 2K` dividing some `v T` are then never removed, `K` of them are
   collected at a common late index, and a CRT block of `K` consecutive integers
   above `R T` — placed by the tree's `exists_consecutiveMultiples_between` and
   translated by the block product — cannot be crossed.
4. *The comparison with `δ`.*  The exact identity
   `h n * w (n+1) + a n ^ 2 * u n = a (n+1) * w n + a n * w n`
   (Duverney's recurrence in the reduced coordinates) gives
   `|δ n - m n / u n| ≤ 3 / a n`, and `R n / a n → 0`, so `R n δ n - 𝒜 n → 0`.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter Asymptotics
open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR11
open scoped BigOperators Topology

/-! ## 0. Reading `limsup < ∞` and `limsup ∈ {0, +∞}` off a real sequence

`EReal` is the value space in which `limsup` of a real sequence is always
defined, so the paper's `limsup 𝒜 n < ∞` is `limsup (𝒜 n : EReal) ≠ ⊤`. -/

/-- `limsup f < ∞`, read in `EReal`, is eventual boundedness above. -/
theorem erealLimsup_ne_top_iff (f : ℕ → ℝ) :
    Filter.limsup (fun n ↦ ((f n : ℝ) : EReal)) Filter.atTop ≠ ⊤ ↔
      ∃ K : ℝ, ∀ᶠ n in Filter.atTop, f n ≤ K := by
  constructor
  · intro h
    have hlt : Filter.limsup (fun n ↦ ((f n : ℝ) : EReal)) Filter.atTop < ⊤ :=
      lt_of_le_of_ne le_top h
    obtain ⟨x, hx, -⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    refine ⟨x, ?_⟩
    have hev := Filter.eventually_lt_of_limsup_lt hx
    filter_upwards [hev] with n hn
    exact le_of_lt (EReal.coe_lt_coe_iff.mp hn)
  · rintro ⟨K, hK⟩
    have hle : Filter.limsup (fun n ↦ ((f n : ℝ) : EReal)) Filter.atTop ≤ (K : EReal) := by
      refine Filter.limsup_le_of_le Filter.isCobounded_le_of_bot ?_
      filter_upwards [hK] with n hn
      exact EReal.coe_le_coe_iff.mpr hn
    intro htop
    rw [htop] at hle
    exact (EReal.coe_ne_top K) (top_le_iff.mp hle)

/-- A real sequence tending to `0` has `EReal` limsup `0`. -/
theorem erealLimsup_eq_zero_of_tendsto {f : ℕ → ℝ}
    (h : Filter.Tendsto f Filter.atTop (nhds 0)) :
    Filter.limsup (fun n ↦ ((f n : ℝ) : EReal)) Filter.atTop = 0 := by
  have h' : Filter.Tendsto (fun n ↦ ((f n : ℝ) : EReal)) Filter.atTop
      (nhds (((0 : ℝ) : EReal))) := EReal.tendsto_coe.mpr h
  have h2 := h'.limsup_eq
  simpa using h2

/-- A real sequence that is not eventually bounded above has `EReal` limsup `⊤`. -/
theorem erealLimsup_eq_top {f : ℕ → ℝ}
    (h : ¬ ∃ K : ℝ, ∀ᶠ n in Filter.atTop, f n ≤ K) :
    Filter.limsup (fun n ↦ ((f n : ℝ) : EReal)) Filter.atTop = ⊤ := by
  by_contra hc
  exact h ((erealLimsup_ne_top_iff f).mp hc)

namespace StandingOrbit

variable (O : StandingOrbit)

/-! ## 1. The denominator, the LCM and the telescoping quotient -/

theorem D_eq_den_mul_prefix (n : ℕ) : O.D n = O.den * prefixProduct O.a n := rfl

theorem v_dvd_D (n : ℕ) : O.v n ∣ O.D n := ⟨O.G n, (O.v_mul n).symm⟩

theorem D_dvd_D_succ (n : ℕ) : O.D n ∣ O.D (n + 1) := ⟨O.a n, by rw [O.D_step n]; ring⟩

theorem D_dvd_D_of_le {m n : ℕ} (h : m ≤ n) : O.D m ∣ O.D n := by
  induction n, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ k _ ih => exact ih.trans (O.D_dvd_D_succ k)

theorem lcmUpTo_dvd_D (n : ℕ) : lcmUpTo O.den O.a n ∣ O.D n := by
  induction n with
  | zero =>
      have h0 : O.D 0 = O.den * prefixProduct O.a 0 := rfl
      have h1 : prefixProduct O.a 0 = 1 := by simp [prefixProduct]
      have h2 : lcmUpTo O.den O.a 0 = O.den := rfl
      rw [h0, h1, Nat.mul_one, h2]
  | succ n ih =>
      have hstep : O.D (n + 1) = O.a n * O.D n := O.D_step n
      show Nat.lcm (lcmUpTo O.den O.a n) (O.a n) ∣ O.D (n + 1)
      refine Nat.lcm_dvd ?_ ?_
      · exact ih.trans ⟨O.a n, by rw [hstep]; ring⟩
      · exact ⟨O.D n, hstep⟩

/-- `M n = D n / L n`, the paper's telescoping quotient. -/
def lcmQuot (n : ℕ) : ℕ := O.D n / lcmUpTo O.den O.a n

theorem lcmQuot_mul (n : ℕ) : lcmUpTo O.den O.a n * O.lcmQuot n = O.D n :=
  Nat.mul_div_cancel' (O.lcmUpTo_dvd_D n)

theorem lcmQuot_pos (n : ℕ) : 0 < O.lcmQuot n := by
  rcases Nat.eq_zero_or_pos (O.lcmQuot n) with h | h
  · have hm := O.lcmQuot_mul n
    rw [h, Nat.mul_zero] at hm
    have := O.D_pos n
    omega
  · exact h

theorem lcmQuot_dvd_C (n : ℕ) : O.lcmQuot n ∣ O.C n := by
  have h := O.D_dvd_lcm_mul_C n
  rw [← O.lcmQuot_mul n] at h
  exact (Nat.mul_dvd_mul_iff_left (lcmUpTo_pos O.den_pos O.a_pos n)).mp h

theorem lcmQuot_succ (n : ℕ) :
    O.lcmQuot (n + 1) = Nat.gcd (lcmUpTo O.den O.a n) (O.a n) * O.lcmQuot n := by
  have hL : lcmUpTo O.den O.a (n + 1) = Nat.lcm (lcmUpTo O.den O.a n) (O.a n) := rfl
  have hgl : Nat.gcd (lcmUpTo O.den O.a n) (O.a n) * Nat.lcm (lcmUpTo O.den O.a n) (O.a n)
      = lcmUpTo O.den O.a n * O.a n := Nat.gcd_mul_lcm _ _
  refine Nat.eq_of_mul_eq_mul_left (lcmUpTo_pos O.den_pos O.a_pos (n + 1)) ?_
  calc lcmUpTo O.den O.a (n + 1) * O.lcmQuot (n + 1) = O.D (n + 1) := O.lcmQuot_mul (n + 1)
    _ = O.a n * O.D n := O.D_step n
    _ = O.a n * (lcmUpTo O.den O.a n * O.lcmQuot n) := by rw [O.lcmQuot_mul n]
    _ = (lcmUpTo O.den O.a n * O.a n) * O.lcmQuot n := by ring
    _ = (Nat.gcd (lcmUpTo O.den O.a n) (O.a n)
          * Nat.lcm (lcmUpTo O.den O.a n) (O.a n)) * O.lcmQuot n := by rw [hgl]
    _ = lcmUpTo O.den O.a (n + 1)
          * (Nat.gcd (lcmUpTo O.den O.a n) (O.a n) * O.lcmQuot n) := by rw [hL]; ring

/-! ## 2. Multipliers coprime to the accumulated denominator -/

theorem coprime_D_of_coprime_lcmUpTo (n : ℕ)
    (h : Nat.Coprime (O.a n) (lcmUpTo O.den O.a n)) : Nat.Coprime (O.a n) (O.D n) := by
  have hD : O.D n = O.den * prefixProduct O.a n := rfl
  rw [hD]
  refine Nat.Coprime.mul_right (h.of_dvd_right (den_dvd_lcmUpTo O.den O.a n)) ?_
  show Nat.Coprime (O.a n) (∏ j ∈ Finset.range n, O.a j)
  refine Nat.Coprime.prod_right ?_
  intro j hj
  exact h.of_dvd_right (term_dvd_lcmUpTo O.den O.a n j (Finset.mem_range.mp hj))

/-- **Cofinal supply of coprime multipliers.**  A multiplier coprime to the
accumulated denominator occurs at arbitrarily late indices.  This is the
qualitative content of the density-one count in the proof of
`long243:res:recorddichotomy`; only the finite telescoping identity is used. -/
theorem coprimeMultiplier_cofinal (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) := by
  by_contra hcon
  push_neg at hcon
  have hbig : ∀ n, N ≤ n → 2 ≤ Nat.gcd (lcmUpTo O.den O.a n) (O.a n) := by
    intro n hn
    have hne : Nat.gcd (lcmUpTo O.den O.a n) (O.a n) ≠ 1 := by
      intro h1
      exact hcon n hn (O.coprime_D_of_coprime_lcmUpTo n (Nat.Coprime.symm h1))
    have hz : Nat.gcd (lcmUpTo O.den O.a n) (O.a n) ≠ 0 := by
      intro h0
      rw [Nat.gcd_eq_zero_iff] at h0
      exact absurd h0.2 (O.a_pos n).ne'
    omega
  have hgrow : ∀ k, 2 ^ k ≤ O.lcmQuot (N + k) := by
    intro k
    induction k with
    | zero => simpa using O.lcmQuot_pos N
    | succ k ih =>
        have h2 := hbig (N + k) (by omega)
        have hsucc := O.lcmQuot_succ (N + k)
        have hidx : N + (k + 1) = (N + k) + 1 := by omega
        rw [hidx, hsucc]
        calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
          _ ≤ Nat.gcd (lcmUpTo O.den O.a (N + k)) (O.a (N + k)) * O.lcmQuot (N + k) :=
              Nat.mul_le_mul h2 ih
  obtain ⟨Kc, hKcpos, hKcle⟩ := O.Hmax_pow_envelope 1
  have hkey : ∀ k : ℕ, (4 / 3 : ℝ) ^ k ≤ Kc * (3 / 2 : ℝ) ^ N := by
    intro k
    have h1 : (2 : ℕ) ^ k ≤ O.Hmax (N + k) := by
      refine le_trans (hgrow k) (le_trans ?_ (le_runningMax O.C (le_refl (N + k))))
      exact Nat.le_of_dvd (O.C_pos (N + k)) (O.lcmQuot_dvd_C (N + k))
    have h2 : ((O.Hmax (N + k) : ℕ) : ℝ) ≤ Kc * (3 / 2 : ℝ) ^ (N + k) := by
      simpa using hKcle (N + k)
    have h1' : ((2 : ℝ)) ^ k ≤ ((O.Hmax (N + k) : ℕ) : ℝ) := by exact_mod_cast h1
    have hpow : (3 / 2 : ℝ) ^ (N + k) = (3 / 2 : ℝ) ^ N * (3 / 2 : ℝ) ^ k := pow_add _ _ _
    rw [hpow] at h2
    have hp : (0 : ℝ) < (3 / 2 : ℝ) ^ k := by positivity
    have hid : (4 / 3 : ℝ) ^ k = (2 : ℝ) ^ k / (3 / 2 : ℝ) ^ k := by
      rw [← div_pow]; norm_num
    rw [hid, div_le_iff₀ hp]
    nlinarith [h1', h2]
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp
      (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 4 / 3 by norm_num)))
      (Kc * (3 / 2 : ℝ) ^ N + 1))
  have hA := hkey k
  have hB := hk k le_rfl
  linarith

/-! ## 3. The release at a coprime multiplier step -/

theorem coprime_w_v_of_coprimeMultiplier {n : ℕ} (h : Nat.Coprime (O.a n) (O.D n)) :
    Nat.Coprime (O.w n) (O.v n) := by
  have hav : Nat.Coprime (O.a n) (O.v n) := h.of_dvd_right (O.v_dvd_D n)
  have hd1 : Nat.gcd (O.w n) (O.v n) ∣ O.a n * O.u n := by
    rw [← O.w_add_v n]
    exact dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  have hd2 : Nat.gcd (O.w n) (O.v n) ∣ O.v n := Nat.gcd_dvd_right _ _
  have hcop : Nat.Coprime (O.v n) (O.a n * O.u n) :=
    Nat.Coprime.mul_right hav.symm (O.coprime_u_v n).symm
  have hh := Nat.dvd_gcd hd2 hd1
  rw [hcop.gcd_eq_one] at hh
  exact Nat.dvd_one.mp hh

theorem coprime_w_a_of_coprimeMultiplier {n : ℕ} (h : Nat.Coprime (O.a n) (O.D n)) :
    Nat.Coprime (O.w n) (O.a n) := by
  have hav : Nat.Coprime (O.a n) (O.v n) := h.of_dvd_right (O.v_dvd_D n)
  have hd1 : Nat.gcd (O.w n) (O.a n) ∣ O.v n := by
    have hwd : Nat.gcd (O.w n) (O.a n) ∣ O.w n := Nat.gcd_dvd_left _ _
    have hsum : Nat.gcd (O.w n) (O.a n) ∣ O.v n + O.w n := by
      have h := O.w_add_v n
      have h' : O.v n + O.w n = O.a n * O.u n := by omega
      rw [h']
      exact Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _
    exact (Nat.dvd_add_iff_left hwd).mpr hsum
  have hd2 : Nat.gcd (O.w n) (O.a n) ∣ O.a n := Nat.gcd_dvd_right _ _
  have hh := Nat.dvd_gcd hd2 hd1
  rw [hav.gcd_eq_one] at hh
  exact Nat.dvd_one.mp hh

/-- At a step whose multiplier is coprime to the accumulated denominator, the
cancellation factor is trivial: `h n = 1`. -/
theorem canc_eq_one_of_coprimeMultiplier {n : ℕ} (h : Nat.Coprime (O.a n) (O.D n)) :
    O.canc n = 1 := by
  have hdvd1 : O.canc n ∣ O.w n := ⟨O.u (n + 1), O.num_step n⟩
  have hdvd2 : O.canc n ∣ O.a n * O.v n := ⟨O.v (n + 1), O.den_step n⟩
  have hcop2 : Nat.Coprime (O.w n) (O.a n * O.v n) :=
    Nat.Coprime.mul_right (O.coprime_w_a_of_coprimeMultiplier h)
      (O.coprime_w_v_of_coprimeMultiplier h)
  have hh := Nat.dvd_gcd hdvd1 hdvd2
  rw [hcop2.gcd_eq_one] at hh
  exact Nat.dvd_one.mp hh

/-- At such a step the multiplier enters the reduced denominator. -/
theorem a_dvd_v_succ_of_coprimeMultiplier {n : ℕ} (h : Nat.Coprime (O.a n) (O.D n)) :
    O.a n ∣ O.v (n + 1) := by
  have h1 := O.den_step n
  rw [O.canc_eq_one_of_coprimeMultiplier h, Nat.one_mul] at h1
  exact ⟨O.v n, h1.symm⟩

/-- **Coprime multipliers with a large prime factor occur cofinally.**

Distinct coprime-multiplier steps use disjoint sets of primes, because a prime
that has already entered the accumulated denominator cannot divide a later
coprime multiplier.  Only finitely many primes lie below `B`, so beyond every
index there is a coprime multiplier step whose multiplier has a prime factor
exceeding `B`. -/
theorem largePrime_coprimeMultiplier (B : ℕ) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) ∧
      ∃ p, Nat.Prime p ∧ p ∣ O.a n ∧ B < p := by
  classical
  set S : ℕ → Finset ℕ :=
    fun M ↦ (Finset.range (B + 1)).filter (fun p ↦ Nat.Prime p ∧ ¬ p ∣ O.D M) with hS
  have hanti : ∀ m k : ℕ, m ≤ k → (S k).card ≤ (S m).card := by
    intro m k hmk
    refine Finset.card_le_card ?_
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2.1, fun hd ↦ hp.2.2 (dvd_trans hd (O.D_dvd_D_of_le hmk))⟩
  obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ k, (S N₂).card ≤ (S k).card := by
    have hne : (Set.range (fun k ↦ (S k).card)).Nonempty := ⟨(S 0).card, 0, rfl⟩
    obtain ⟨N₂, hN₂⟩ := Nat.sInf_mem hne
    refine ⟨N₂, fun k ↦ ?_⟩
    have h1 : (S N₂).card = sInf (Set.range (fun k ↦ (S k).card)) := hN₂
    rw [h1]
    exact Nat.sInf_le ⟨k, rfl⟩
  obtain ⟨Na, hNa⟩ := strictMono_eventually_ge_two O.a O.a_strictMono O.a_pos
  obtain ⟨n, hn, hco⟩ := O.coprimeMultiplier_cofinal (max (max N N₂) Na)
  refine ⟨n, le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn, hco, ?_⟩
  have ha2 : 2 ≤ O.a n := hNa n (le_trans (le_max_right _ _) hn)
  have hne1 : O.a n ≠ 1 := by omega
  have hp : Nat.Prime (Nat.minFac (O.a n)) := Nat.minFac_prime hne1
  have hpd : Nat.minFac (O.a n) ∣ O.a n := Nat.minFac_dvd _
  refine ⟨Nat.minFac (O.a n), hp, hpd, ?_⟩
  by_contra hle
  push_neg at hle
  have hpnD : ¬ (Nat.minFac (O.a n) ∣ O.D n) := by
    intro hdvd
    have hg : Nat.minFac (O.a n) ∣ Nat.gcd (O.a n) (O.D n) := Nat.dvd_gcd hpd hdvd
    rw [hco.gcd_eq_one] at hg
    have := Nat.le_of_dvd Nat.one_pos hg
    have := hp.two_le
    omega
  have hpD1 : Nat.minFac (O.a n) ∣ O.D (n + 1) := by
    rw [O.D_step n]; exact Dvd.dvd.mul_right hpd _
  have hsubset : S (n + 1) ⊆ S n := by
    intro p hp'
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hp' ⊢
    exact ⟨hp'.1, hp'.2.1, fun hd ↦ hp'.2.2 (dvd_trans hd (O.D_dvd_D_succ n))⟩
  have hmemn : Nat.minFac (O.a n) ∈ S n := by
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp, hpnD⟩
  have hnotmem : Nat.minFac (O.a n) ∉ S (n + 1) := by
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    rintro ⟨-, -, hnd⟩
    exact hnd hpD1
  have hss : S (n + 1) ⊂ S n :=
    (Finset.ssubset_iff_of_subset hsubset).mpr ⟨_, hmemn, hnotmem⟩
  have hcard : (S (n + 1)).card < (S n).card := Finset.card_lt_card hss
  have h1 : (S n).card ≤ (S N₂).card :=
    hanti N₂ n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
  have h2 : (S N₂).card ≤ (S (n + 1)).card := hN₂ (n + 1)
  omega

/-! ## 4. Normalisation consequences on a non-Sylvester tail -/

/-- Eventual Sylvester behaviour: `a (n+1) = a n ^ 2 - a n + 1` for all large `n`. -/
def EventuallySylvester : Prop :=
  ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1

/-- The nearest-integer normalisation gives the unconditional slow-rise bound. -/
theorem slowRise_bound : ∃ N, ∀ n, N ≤ n → 2 * O.w n ≤ 3 * O.u n := by
  obtain ⟨N, hN⟩ := O.redErr_vanishing 2
  refine ⟨N, fun n hn ↦ ?_⟩
  have hb : 2 * (O.redErr n).natAbs < O.u n := hN n hn
  have hw : (O.w n : ℤ) = (O.u n : ℤ) - O.redErr n := O.w_eq_sub_redErr n
  have hcast : ((2 * (O.redErr n).natAbs : ℕ) : ℤ) < ((O.u n : ℕ) : ℤ) := by exact_mod_cast hb
  push_cast at hcast
  have hsplit := Int.natAbs_eq (O.redErr n)
  have hgoal : (2 * (O.w n : ℤ)) ≤ 3 * (O.u n : ℤ) := by
    rcases hsplit with h | h <;> omega
  exact_mod_cast hgoal

/-- A vanishing reduced error is absorbing, and two consecutive zeros pin the
Sylvester step. -/
theorem eventuallySylvester_of_redErr_zero {Nc n₀ : ℕ}
    (hNc : ∀ n, Nc ≤ n → 2 * (O.redErr n).natAbs < O.u n)
    (hn₀ : Nc ≤ n₀) (hz : O.redErr n₀ = 0) : O.EventuallySylvester := by
  have habs : ∀ m, n₀ ≤ m → O.redErr m = 0 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hz
    | succ k hk ih =>
        have hkN : Nc ≤ k := le_trans hn₀ hk
        have hzero : (O.v k : ℤ) - ((O.a k : ℤ) - 1) * (O.u k : ℤ) = 0 := by
          rw [← O.redErr_eq k]; exact ih
        obtain ⟨-, -, -, hu1⟩ :=
          centeredZero_forces_unit (O.coprime_u_v k) (O.w_add_v k) (O.num_step k) hzero
        have hb := hNc (k + 1) (by omega)
        rw [hu1] at hb
        have hz0 : (O.redErr (k + 1)).natAbs = 0 := by omega
        exact Int.natAbs_eq_zero.mp hz0
  refine ⟨n₀, fun m hm ↦ ?_⟩
  have hz1 : (O.v m : ℤ) - ((O.a m : ℤ) - 1) * (O.u m : ℤ) = 0 := by
    rw [← O.redErr_eq m]; exact habs m hm
  have hz2 : (O.v (m + 1) : ℤ) - ((O.a (m + 1) : ℤ) - 1) * (O.u (m + 1) : ℤ) = 0 := by
    rw [← O.redErr_eq (m + 1)]; exact habs (m + 1) (by omega)
  have h := sylvesterStep_of_centeredZero_pair (O.coprime_u_v m) (O.w_add_v m)
    (O.num_step m) (O.den_step m) hz1 hz2
  simpa [sylvesterNext] using h

theorem redErr_ne_zero_of_not_sylvester (hns : ¬ O.EventuallySylvester) :
    ∃ N, ∀ n, N ≤ n → O.redErr n ≠ 0 := by
  obtain ⟨Nc, hNc⟩ := O.redErr_vanishing 2
  exact ⟨Nc, fun n hn hz ↦ hns (O.eventuallySylvester_of_redErr_zero hNc hn hz)⟩

/-- Absorption and the vanishing normalised error make the reduced numerator
diverge on a non-Sylvester tail. -/
theorem u_tendsto_atTop_of_not_sylvester (hns : ¬ O.EventuallySylvester) :
    Tendsto O.u atTop atTop := by
  obtain ⟨Nz, hNz⟩ := O.redErr_ne_zero_of_not_sylvester hns
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨M, hM⟩ := O.redErr_vanishing b
  refine ⟨max M Nz, fun n hn ↦ ?_⟩
  have h1 : b * (O.redErr n).natAbs < O.u n := hM n (le_trans (le_max_left _ _) hn)
  have h2 : O.redErr n ≠ 0 := hNz n (le_trans (le_max_right _ _) hn)
  have h3 : 1 ≤ (O.redErr n).natAbs := by
    rcases Nat.eq_zero_or_pos (O.redErr n).natAbs with h | h
    · exact absurd (Int.natAbs_eq_zero.mp h) h2
    · exact h
  have h4 : b * 1 ≤ b * (O.redErr n).natAbs := Nat.mul_le_mul (le_refl b) h3
  omega

theorem u_succ_le_of_redErr_nonneg {n : ℕ} (h : 0 ≤ O.redErr n) : O.u (n + 1) ≤ O.u n := by
  have hw : (O.w n : ℤ) = (O.u n : ℤ) - O.redErr n := O.w_eq_sub_redErr n
  have hwle : O.w n ≤ O.u n := by
    have hz : (O.w n : ℤ) ≤ (O.u n : ℤ) := by omega
    exact_mod_cast hz
  have h1 : O.u (n + 1) ≤ O.w n := by
    rw [O.num_step n]
    exact Nat.le_mul_of_pos_left _ (O.canc_pos n)
  omega

/-- Negative reduced errors occur arbitrarily late, since otherwise the reduced
numerator would be eventually nonincreasing. -/
theorem negative_redErr_cofinal (hns : ¬ O.EventuallySylvester) (M : ℕ) :
    ∃ t, M ≤ t ∧ O.redErr t < 0 := by
  by_contra hcon
  push_neg at hcon
  have hmono : ∀ n, M ≤ n → O.u n ≤ O.u M := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact le_trans (O.u_succ_le_of_redErr_nonneg (hcon k hk)) ih
  obtain ⟨M', hM'⟩ :=
    (tendsto_atTop_atTop.mp (O.u_tendsto_atTop_of_not_sylvester hns)) (O.u M + 1)
  have h1 := hM' (max M M') (le_max_right _ _)
  have h2 := hmono (max M M') (le_max_left _ _)
  omega

/-! ## 5. The amplified bound controls cancellation as well as upward motion -/

theorem negPart_le_of_amp_le {n K : ℕ} (h : O.amp n ≤ (K : ℝ)) : O.negPart n ≤ K := by
  have h1 := O.negPart_le_amp n
  have h2 : ((O.negPart n : ℕ) : ℝ) ≤ (K : ℝ) := le_trans h1 h
  exact_mod_cast h2

theorem u_succ_le_of_amp_le {n K : ℕ} (h : O.amp n ≤ (K : ℝ)) : O.u (n + 1) ≤ O.u n + K :=
  le_trans (O.u_succ_le n) (Nat.add_le_add_left (O.negPart_le_of_amp_le h) _)

/-- **The estimate at the first later negative error.**  With `𝒜 n ≤ K`
eventually, `𝒜 t ≥ u s / u (s+1)` at the first later negative-error index `t`,
so `2 h s ≤ 3 K` and hence `h s < 2 K`. -/
theorem canc_lt_of_amp_le (hns : ¬ O.EventuallySylvester) (K : ℕ) (hK1 : 1 ≤ K)
    (N₀ : ℕ) (hbd : ∀ n, N₀ ≤ n → O.amp n ≤ (K : ℝ)) :
    ∃ N, ∀ s, N ≤ s → O.canc s < 2 * K := by
  classical
  obtain ⟨Nc, hNc⟩ := O.slowRise_bound
  refine ⟨max N₀ Nc, fun s hs ↦ ?_⟩
  have hsN₀ : N₀ ≤ s := le_trans (le_max_left _ _) hs
  have hsNc : Nc ≤ s := le_trans (le_max_right _ _) hs
  have hQ : ∃ t, s + 1 ≤ t ∧ O.redErr t < 0 := O.negative_redErr_cofinal hns (s + 1)
  obtain ⟨t, hst, hEt, hnonneg⟩ :
      ∃ t, s + 1 ≤ t ∧ O.redErr t < 0 ∧ ∀ j, s + 1 ≤ j → j < t → 0 ≤ O.redErr j := by
    refine ⟨Nat.find hQ, (Nat.find_spec hQ).1, (Nat.find_spec hQ).2, ?_⟩
    intro j hj hjt
    by_contra hc
    push_neg at hc
    exact absurd (Nat.find_min' hQ ⟨hj, hc⟩) (by omega)
  have hut : O.u t ≤ O.u (s + 1) := by
    have hchain : ∀ m, s + 1 ≤ m → m ≤ t → O.u m ≤ O.u (s + 1) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hk ih =>
          intro hkt
          have hprev := ih (by omega)
          have h0 : 0 ≤ O.redErr k := hnonneg k hk (by omega)
          exact le_trans (O.u_succ_le_of_redErr_nonneg h0) hprev
    exact hchain t hst le_rfl
  have hRt : O.u s ≤ O.R t := le_runningMax O.u (by omega)
  have hmt : 1 ≤ O.negPart t := by
    have hnn : (0 : ℤ) ≤ -O.redErr t := by omega
    have hcast : ((O.negPart t : ℕ) : ℤ) = -O.redErr t := by
      show (((-O.redErr t).toNat : ℕ) : ℤ) = -O.redErr t
      exact Int.toNat_of_nonneg hnn
    omega
  have hampt : O.amp t ≤ (K : ℝ) := hbd t (by omega)
  have hupos : (0 : ℝ) < (O.u t : ℝ) := by exact_mod_cast O.u_pos t
  have hprod : O.R t * O.negPart t ≤ K * O.u t := by
    simp only [amp] at hampt
    rw [div_le_iff₀ hupos] at hampt
    have hr : ((O.R t * O.negPart t : ℕ) : ℝ) ≤ ((K * O.u t : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hr
  have hus : O.u s ≤ K * O.u (s + 1) := by
    calc O.u s = O.u s * 1 := by ring
      _ ≤ O.R t * O.negPart t := Nat.mul_le_mul hRt hmt
      _ ≤ K * O.u t := hprod
      _ ≤ K * O.u (s + 1) := Nat.mul_le_mul (le_refl K) hut
  have hsl : 2 * O.w s ≤ 3 * O.u s := hNc s hsNc
  have hws : O.w s = O.canc s * O.u (s + 1) := O.num_step s
  have hu1pos : 0 < O.u (s + 1) := O.u_pos (s + 1)
  have h2 : (2 * O.canc s) * O.u (s + 1) ≤ (3 * K) * O.u (s + 1) := by
    calc (2 * O.canc s) * O.u (s + 1) = 2 * (O.canc s * O.u (s + 1)) := by ring
      _ = 2 * O.w s := by rw [hws]
      _ ≤ 3 * O.u s := hsl
      _ ≤ 3 * (K * O.u (s + 1)) := Nat.mul_le_mul (le_refl 3) hus
      _ = (3 * K) * O.u (s + 1) := by ring
  have h3 : 2 * O.canc s ≤ 3 * K := Nat.le_of_mul_le_mul_right h2 hu1pos
  omega

/-! ## 6. Protected primes and the `K`-prime block -/

/-- A prime larger than every cancellation factor is never removed from the
reduced denominator: `h n v (n+1) = a n v n` and `h n < p` prevent its removal. -/
theorem protectedPrime_persists {p N₀ : ℕ} (hp : Nat.Prime p)
    (hcanc : ∀ m, N₀ ≤ m → O.canc m < p) :
    ∀ T, N₀ ≤ T → p ∣ O.v T → ∀ m, T ≤ m → p ∣ O.v m := by
  intro T hT hpT m hm
  induction m, hm using Nat.le_induction with
  | base => exact hpT
  | succ k hk ih =>
      have hck : O.canc k < p := hcanc k (le_trans hT hk)
      have hnd : ¬ (p ∣ O.canc k) := by
        intro hd
        have := Nat.le_of_dvd (O.canc_pos k) hd
        omega
      have hdd : p ∣ O.canc k * O.v (k + 1) := by
        rw [← O.den_step k]
        exact Dvd.dvd.mul_left ih _
      exact (hp.dvd_mul.mp hdd).resolve_left hnd

/-- **The protected prime block.**  If every cancellation factor beyond `N₀` is
at most `B`, then for every `j` there is an index `T ≥ N₀` and a set of `j`
distinct primes above `B`, all dividing `v T`. -/
theorem primeBlock_supply (B N₀ : ℕ) (hcanc : ∀ m, N₀ ≤ m → O.canc m ≤ B) :
    ∀ j : ℕ, ∃ T, N₀ ≤ T ∧ ∃ P : Finset ℕ, P.card = j ∧
      ∀ p ∈ P, Nat.Prime p ∧ B < p ∧ p ∣ O.v T := by
  intro j
  induction j with
  | zero => exact ⟨N₀, le_rfl, ∅, rfl, by simp⟩
  | succ j ih =>
      obtain ⟨T, hT, P, hcard, hP⟩ := ih
      obtain ⟨n, hn, hco, p, hp, hpa, hpB⟩ := O.largePrime_coprimeMultiplier B (max T N₀)
      have hTn : T ≤ n := le_trans (le_max_left _ _) hn
      have hN₀n : N₀ ≤ n := le_trans (le_max_right _ _) hn
      have hpnotmem : p ∉ P := by
        intro hmem
        obtain ⟨-, -, hdv⟩ := hP p hmem
        have h1 : p ∣ O.D n :=
          dvd_trans (dvd_trans hdv (O.v_dvd_D T)) (O.D_dvd_D_of_le hTn)
        have h2 : p ∣ Nat.gcd (O.a n) (O.D n) := Nat.dvd_gcd hpa h1
        rw [hco.gcd_eq_one] at h2
        have h3 := Nat.le_of_dvd Nat.one_pos h2
        have h4 := hp.two_le
        omega
      refine ⟨n + 1, by omega, insert p P, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hpnotmem, hcard]
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq'
        · exact ⟨hp, hpB, dvd_trans hpa (O.a_dvd_v_succ_of_coprimeMultiplier hco)⟩
        · obtain ⟨hq1, hq2, hq3⟩ := hP q hq'
          refine ⟨hq1, hq2, ?_⟩
          refine O.protectedPrime_persists hq1 (fun m hm ↦ ?_) T hT hq3 (n + 1) (by omega)
          have := hcanc m hm
          omega

/-! ## 7. The `K`-increment cut -/

/-- **`𝒜 n ≤ K` eventually forces an eventually Sylvester tail.**

This is the `K`-increment cut for an arbitrarily cancelled reduced orbit: the
bound gives `m n ≤ K`, hence `u (n+1) ≤ u n + K`, and `h s < 2K`; `K` distinct
primes above `2K` are then locked into the reduced denominator at a common late
index `T`, a CRT block of `K` consecutive integers above `R T` is placed on
them, and the forced first crossing must land inside the block. -/
theorem eventuallySylvester_of_amp_le (K : ℕ) (hK1 : 1 ≤ K) (N₀ : ℕ)
    (hbd : ∀ n, N₀ ≤ n → O.amp n ≤ (K : ℝ)) : O.EventuallySylvester := by
  classical
  by_contra hns
  obtain ⟨N₁, hN₁⟩ := O.canc_lt_of_amp_le hns K hK1 N₀ hbd
  have hcancle : ∀ m, max N₀ N₁ ≤ m → O.canc m ≤ 2 * K := by
    intro m hm
    have := hN₁ m (le_trans (le_max_right _ _) hm)
    omega
  obtain ⟨T, hTNs, P, hcard, hP⟩ := O.primeBlock_supply (2 * K) (max N₀ N₁) hcancle K
  have hmemP : ∀ i : Fin K, (P.orderIsoOfFin hcard i).1 ∈ P :=
    fun i ↦ (P.orderIsoOfFin hcard i).2
  set mm : Fin K → ℕ := fun i ↦ (P.orderIsoOfFin hcard i).1 with hmm
  have hmprime : ∀ i, Nat.Prime (mm i) := fun i ↦ (hP _ (hmemP i)).1
  have hmB : ∀ i, 2 * K < mm i := fun i ↦ (hP _ (hmemP i)).2.1
  have hmdvd : ∀ i, mm i ∣ O.v T := fun i ↦ (hP _ (hmemP i)).2.2
  have hm1 : ∀ i, 1 < mm i := fun i ↦ (hmprime i).one_lt
  have hpair : ∀ i i', i ≠ i' → Nat.Coprime (mm i) (mm i') := by
    intro i i' hne
    refine (Nat.coprime_primes (hmprime i) (hmprime i')).mpr ?_
    intro heq
    exact hne ((P.orderIsoOfFin hcard).injective (Subtype.ext heq))
  obtain ⟨x, hxP, hx2P, hxdvd⟩ := exists_consecutiveMultiples_between mm hm1 hpair
  have hPrpos : 0 < ∏ i, mm i := Finset.prod_pos (fun i _ ↦ by have := hm1 i; omega)
  have hyR : O.R T < x + (∏ i, mm i) * O.R T := by
    have h2 : O.R T ≤ (∏ i, mm i) * O.R T := Nat.le_mul_of_pos_left _ hPrpos
    omega
  have hydvd : ∀ i : Fin K, mm i ∣ (x + (∏ i, mm i) * O.R T) + i.1 := by
    intro i
    have h1 : mm i ∣ x + i.1 := hxdvd i
    have h2 : mm i ∣ (∏ i, mm i) * O.R T :=
      Dvd.dvd.mul_right (Finset.dvd_prod_of_mem mm (Finset.mem_univ i)) _
    have he : (x + (∏ i, mm i) * O.R T) + i.1 = (x + i.1) + (∏ i, mm i) * O.R T := by ring
    rw [he]
    exact dvd_add h1 h2
  have hutop := O.u_tendsto_atTop_of_not_sylvester hns
  have hQ : ∃ n, T ≤ n ∧ (x + (∏ i, mm i) * O.R T) ≤ O.u n := by
    obtain ⟨M, hM⟩ := (tendsto_atTop_atTop.mp hutop) (x + (∏ i, mm i) * O.R T)
    exact ⟨max M T, le_max_right _ _, hM _ (le_max_left _ _)⟩
  obtain ⟨τ, hτT, hτy, hmin⟩ :
      ∃ τ, T ≤ τ ∧ (x + (∏ i, mm i) * O.R T) ≤ O.u τ ∧
        ∀ k, T ≤ k → k < τ → O.u k < x + (∏ i, mm i) * O.R T := by
    refine ⟨Nat.find hQ, (Nat.find_spec hQ).1, (Nat.find_spec hQ).2, ?_⟩
    intro k hk hkτ
    by_contra hc
    push_neg at hc
    exact absurd (Nat.find_min' hQ ⟨hk, hc⟩) (by omega)
  have hτne : τ ≠ T := by
    intro h
    rw [h] at hτy
    have : O.u T ≤ O.R T := le_runningMax O.u (le_refl T)
    omega
  obtain ⟨t, rfl⟩ : ∃ t, τ = t + 1 := ⟨τ - 1, by omega⟩
  have htT : T ≤ t := by omega
  have hbelow : O.u t < x + (∏ i, mm i) * O.R T := hmin t htT (by omega)
  have hstep : O.u (t + 1) ≤ O.u t + K :=
    O.u_succ_le_of_amp_le (hbd t (le_trans (le_trans (le_max_left N₀ N₁) hTNs) htT))
  have hrK : O.u (t + 1) - (x + (∏ i, mm i) * O.R T) < K := by omega
  obtain ⟨idx, hyr⟩ : ∃ idx : Fin K, (x + (∏ i, mm i) * O.R T) + idx.1 = O.u (t + 1) := by
    refine ⟨⟨O.u (t + 1) - (x + (∏ i, mm i) * O.R T), hrK⟩, ?_⟩
    show (x + (∏ i, mm i) * O.R T) + (O.u (t + 1) - (x + (∏ i, mm i) * O.R T)) = O.u (t + 1)
    omega
  have hdvdu : mm idx ∣ O.u (t + 1) := by
    rw [← hyr]
    exact hydvd idx
  have hdvdv : mm idx ∣ O.v (t + 1) := by
    refine O.protectedPrime_persists (hmprime idx) (fun m hm ↦ ?_) T hTNs (hmdvd idx) (t + 1)
      (by omega)
    have h1 := hN₁ m (le_trans (le_max_right N₀ N₁) hm)
    have h2 := hmB idx
    omega
  have hg : mm idx ∣ Nat.gcd (O.u (t + 1)) (O.v (t + 1)) := Nat.dvd_gcd hdvdu hdvdv
  rw [(O.coprime_u_v (t + 1)).gcd_eq_one] at hg
  have h1 := Nat.le_of_dvd Nat.one_pos hg
  have h2 := hm1 idx
  omega

/-! ## 8. Duverney's recurrence in the reduced coordinates, and the comparison
with `δ` -/

/-- The exact reduced form of Duverney's recurrence
`a (n+1) = (u n / w n) a n ^ 2 - a n + w (n+1) / u (n+1)`, cleared of
denominators. -/
theorem duverney_identity (n : ℕ) :
    O.canc n * O.w (n + 1) + O.a n ^ 2 * O.u n
      = O.a (n + 1) * O.w n + O.a n * O.w n := by
  have h1 : O.canc n * O.w (n + 1) + O.canc n * O.v (n + 1) = O.a (n + 1) * O.w n := by
    have hA := O.w_add_v (n + 1)
    have hB := O.num_step n
    calc O.canc n * O.w (n + 1) + O.canc n * O.v (n + 1)
        = O.canc n * (O.w (n + 1) + O.v (n + 1)) := by ring
      _ = O.canc n * (O.a (n + 1) * O.u (n + 1)) := by rw [hA]
      _ = O.a (n + 1) * (O.canc n * O.u (n + 1)) := by ring
      _ = O.a (n + 1) * O.w n := by rw [← hB]
  have h3 := O.den_step n
  have h5 : O.a n ^ 2 * O.u n = O.a n * O.w n + O.a n * O.v n := by
    have h4 := O.w_add_v n
    calc O.a n ^ 2 * O.u n = O.a n * (O.a n * O.u n) := by ring
      _ = O.a n * (O.w n + O.v n) := by rw [h4]
      _ = O.a n * O.w n + O.a n * O.v n := by ring
  omega

/-- `h n w (n+1) / w n = w (n+1) / u (n+1) ≤ 3/2` under the centring bound. -/
theorem canc_w_succ_bound {n : ℕ} (hc : 2 * O.w (n + 1) ≤ 3 * O.u (n + 1)) :
    2 * (O.canc n * O.w (n + 1)) ≤ 3 * O.w n := by
  have hnum := O.num_step n
  have hpos : 0 < O.u (n + 1) := O.u_pos (n + 1)
  have key : (2 * (O.canc n * O.w (n + 1))) * O.u (n + 1) ≤ (3 * O.w n) * O.u (n + 1) := by
    calc (2 * (O.canc n * O.w (n + 1))) * O.u (n + 1)
        = (O.canc n * O.u (n + 1)) * (2 * O.w (n + 1)) := by ring
      _ = O.w n * (2 * O.w (n + 1)) := by rw [← hnum]
      _ ≤ O.w n * (3 * O.u (n + 1)) := Nat.mul_le_mul (le_refl (O.w n)) hc
      _ = (3 * O.w n) * O.u (n + 1) := by ring
  exact Nat.le_of_mul_le_mul_right key hpos

theorem negPart_eq_w_sub_u (n : ℕ) : O.negPart n = O.w n - O.u n := by
  have h := O.w_eq_sub_redErr n
  show (-(O.redErr n)).toNat = O.w n - O.u n
  omega

theorem negPart_cast (n : ℕ) :
    ((O.negPart n : ℕ) : ℝ) = max 0 ((O.w n : ℝ) - (O.u n : ℝ)) := by
  rw [O.negPart_eq_w_sub_u n]
  rcases le_total (O.u n) (O.w n) with hle | hle
  · have hR : ((O.u n : ℕ) : ℝ) ≤ ((O.w n : ℕ) : ℝ) := by exact_mod_cast hle
    rw [max_eq_right (by linarith)]
    push_cast [Nat.cast_sub hle]
    ring
  · have hR : ((O.w n : ℕ) : ℝ) ≤ ((O.u n : ℕ) : ℝ) := by exact_mod_cast hle
    have h0 : O.w n - O.u n = 0 := by omega
    rw [h0, max_eq_left (by linarith)]
    norm_num

theorem negPart_div_u (n : ℕ) :
    ((O.negPart n : ℕ) : ℝ) / (O.u n : ℝ)
      = max 0 (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ)) := by
  have hu : (0 : ℝ) < (O.u n : ℝ) := by exact_mod_cast O.u_pos n
  rcases le_total ((O.w n : ℝ)) ((O.u n : ℝ)) with hle | hle
  · have hneg : ((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ) ≤ 0 := by
      rw [div_le_iff₀ hu]; linarith
    rw [O.negPart_cast n, max_eq_left (by linarith), max_eq_left hneg, zero_div]
  · have hnn : (0 : ℝ) ≤ ((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ) := by
      rw [le_div_iff₀ hu]; linarith
    rw [O.negPart_cast n, max_eq_right (by linarith), max_eq_right hnn]

/-- `|x₊ - y₊| ≤ |x - y|`. -/
theorem abs_posPart_sub_le (x y : ℝ) : |max 0 x - max 0 y| ≤ |x - y| := by
  rw [max_comm 0 x, max_comm 0 y]
  exact abs_max_sub_max_le_abs x y 0

/-- **The comparison `|δ n - m n / u n| ≤ 3 / a n`.** -/
theorem delta_negPart_comparison :
    ∃ N, ∀ n, N ≤ n →
      |O.delta n - (O.negPart n : ℝ) / (O.u n : ℝ)| ≤ 3 / (O.a n : ℝ) := by
  obtain ⟨Nc, hNc⟩ := O.slowRise_bound
  obtain ⟨Nb, hNb⟩ := quadratic_brackets_of_limit O.a O.a_pos O.growth
  obtain ⟨Na, hNa⟩ := strictMono_eventually_ge_two O.a O.a_strictMono O.a_pos
  refine ⟨max (max Nc Nb) Na, fun n hn ↦ ?_⟩
  have hnc : Nc ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnb : Nb ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hna : Na ≤ n := le_trans (le_max_right _ _) hn
  have hu : (0 : ℝ) < (O.u n : ℝ) := by exact_mod_cast O.u_pos n
  have ha : (0 : ℝ) < (O.a n : ℝ) := by exact_mod_cast O.a_pos n
  have ha' : (0 : ℝ) < (O.a (n + 1) : ℝ) := by exact_mod_cast O.a_pos (n + 1)
  have hidN := O.duverney_identity n
  have hid : (O.canc n : ℝ) * (O.w (n + 1) : ℝ) + (O.a n : ℝ) ^ 2 * (O.u n : ℝ)
      = (O.a (n + 1) : ℝ) * (O.w n : ℝ) + (O.a n : ℝ) * (O.w n : ℝ) := by
    exact_mod_cast hidN
  have hmul : (((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
        - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ)))
      * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))
      = (O.a n : ℝ) * (O.w n : ℝ) - (O.canc n : ℝ) * (O.w (n + 1) : ℝ) := by
    have e1 : (O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))
        = (O.a n : ℝ) ^ 2 * (O.u n : ℝ) := by field_simp
    have e2 : (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ)) * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))
        = ((O.w n : ℝ) - (O.u n : ℝ)) * (O.a (n + 1) : ℝ) := by field_simp
    calc (((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
            - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ)))
          * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))
        = (O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))
          - 1 * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))
          - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ))
            * ((O.a (n + 1) : ℝ) * (O.u n : ℝ)) := by ring
      _ = (O.a n : ℝ) ^ 2 * (O.u n : ℝ) - (O.a (n + 1) : ℝ) * (O.u n : ℝ)
          - ((O.w n : ℝ) - (O.u n : ℝ)) * (O.a (n + 1) : ℝ) := by rw [e1, e2]; ring
      _ = (O.a n : ℝ) ^ 2 * (O.u n : ℝ) - (O.a (n + 1) : ℝ) * (O.w n : ℝ) := by ring
      _ = (O.a n : ℝ) * (O.w n : ℝ) - (O.canc n : ℝ) * (O.w (n + 1) : ℝ) := by linarith
  have hcw : 2 * (O.canc n * O.w (n + 1)) ≤ 3 * O.w n :=
    O.canc_w_succ_bound (hNc (n + 1) (by omega))
  have h2w : 2 * O.w n ≤ 3 * O.u n := hNc n hnc
  have ha2 : 2 ≤ O.a n := hNa n hna
  have hbr : O.a n ^ 2 ≤ 2 * O.a (n + 1) := (hNb n hnb).1
  have hcwR : 2 * ((O.canc n : ℝ) * (O.w (n + 1) : ℝ)) ≤ 3 * (O.w n : ℝ) := by exact_mod_cast hcw
  have h2wR : 2 * (O.w n : ℝ) ≤ 3 * (O.u n : ℝ) := by exact_mod_cast h2w
  have ha2R : (2 : ℝ) ≤ (O.a n : ℝ) := by exact_mod_cast ha2
  have hbrR : (O.a n : ℝ) ^ 2 ≤ 2 * (O.a (n + 1) : ℝ) := by exact_mod_cast hbr
  have hw0 : (0 : ℝ) ≤ (O.w n : ℝ) := Nat.cast_nonneg _
  have hcw0 : (0 : ℝ) ≤ (O.canc n : ℝ) * (O.w (n + 1) : ℝ) := by positivity
  have haw : 2 * (O.w n : ℝ) ≤ (O.a n : ℝ) * (O.w n : ℝ) := by nlinarith
  have hnum1 : |(O.a n : ℝ) * (O.w n : ℝ) - (O.canc n : ℝ) * (O.w (n + 1) : ℝ)|
      ≤ (O.a n : ℝ) * (O.w n : ℝ) := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hD : (0 : ℝ) < (O.a (n + 1) : ℝ) * (O.u n : ℝ) := by positivity
  have habs : |((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
        - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ))| * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))
      = |(O.a n : ℝ) * (O.w n : ℝ) - (O.canc n : ℝ) * (O.w (n + 1) : ℝ)| := by
    calc |((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
          - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ))| * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))
        = |((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
          - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ))|
          * |(O.a (n + 1) : ℝ) * (O.u n : ℝ)| := by rw [abs_of_pos hD]
      _ = |(((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
          - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ)))
          * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))| := (abs_mul _ _).symm
      _ = |(O.a n : ℝ) * (O.w n : ℝ) - (O.canc n : ℝ) * (O.w (n + 1) : ℝ)| := by rw [hmul]
  have hfin : |((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
        - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ))| * (O.a n : ℝ) ≤ 3 := by
    have hstep : (|((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
          - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ))| * (O.a n : ℝ))
        * ((O.a (n + 1) : ℝ) * (O.u n : ℝ)) ≤ 3 * ((O.a (n + 1) : ℝ) * (O.u n : ℝ)) := by
      have e : (|((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
            - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ))| * (O.a n : ℝ))
          * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))
          = (O.a n : ℝ) * (|((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
            - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ))|
            * ((O.a (n + 1) : ℝ) * (O.u n : ℝ))) := by ring
      rw [e, habs]
      nlinarith [mul_le_mul_of_nonneg_left hnum1 ha.le,
        mul_le_mul_of_nonneg_right hbrR hw0,
        mul_le_mul_of_nonneg_left h2wR ha'.le]
    exact le_of_mul_le_mul_right hstep hD
  have hdiv : |((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
      - (((O.w n : ℝ) - (O.u n : ℝ)) / (O.u n : ℝ))| ≤ 3 / (O.a n : ℝ) :=
    (le_div_iff₀ ha).mpr hfin
  refine le_trans ?_ hdiv
  rw [show O.delta n = max 0 ((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1) from rfl,
    O.negPart_div_u n]
  exact abs_posPart_sub_le _ _

/-- `R n / a n → 0`: the running maximum is subexponential while the multipliers
grow doubly exponentially. -/
theorem R_div_a_tendsto_zero :
    Tendsto (fun n ↦ (O.R n : ℝ) / (O.a n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Kc, hKcpos, hKcle⟩ := O.Hmax_pow_envelope 1
  obtain ⟨N₁, Aq, hAq4, hAqdef, hdbl⟩ :=
    quadratic_double_exponential_bounds O.a O.a_strictMono O.a_pos O.growth
  refine squeeze_zero' (g := fun n ↦ Kc * (2 : ℝ) ^ N₁ * (3 / 4 : ℝ) ^ n)
    (Filter.Eventually.of_forall (fun n ↦ by positivity)) ?_ ?_
  · filter_upwards [eventually_ge_atTop N₁] with n hn
    have hane : (0 : ℝ) < (O.a n : ℝ) := by exact_mod_cast O.a_pos n
    have hnat : (2 : ℕ) ^ (n - N₁) ≤ O.a n := by
      have h := (hdbl (n - N₁)).1
      rw [show N₁ + (n - N₁) = n from by omega] at h
      have hj : n - N₁ ≤ 2 ^ (n - N₁) := Nat.le_of_lt Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (n - N₁) ≤ 2 ^ (2 ^ (n - N₁)) := Nat.pow_le_pow_right (by norm_num) hj
      omega
    have hlow : ((2 : ℝ)) ^ (n - N₁) ≤ (O.a n : ℝ) := by exact_mod_cast hnat
    have hup : (O.R n : ℝ) ≤ Kc * (3 / 2 : ℝ) ^ n := by
      have h1 : ((O.R n : ℕ) : ℝ) ≤ ((O.Hmax n : ℕ) : ℝ) := by exact_mod_cast O.R_le_Hmax n
      have h2 : ((O.Hmax n : ℕ) : ℝ) ≤ Kc * (3 / 2 : ℝ) ^ n := by simpa using hKcle n
      linarith
    rw [div_le_iff₀ hane]
    have hsplit : (2 : ℝ) ^ N₁ * (2 : ℝ) ^ (n - N₁) = (2 : ℝ) ^ n := by
      rw [← pow_add]; congr 1; omega
    have h34 : (3 / 4 : ℝ) ^ n * (2 : ℝ) ^ n = (3 / 2 : ℝ) ^ n := by
      rw [← mul_pow]; norm_num
    have key : (Kc * (2 : ℝ) ^ N₁ * (3 / 4 : ℝ) ^ n) * ((2 : ℝ) ^ (n - N₁))
        = Kc * (3 / 2 : ℝ) ^ n := by
      calc (Kc * (2 : ℝ) ^ N₁ * (3 / 4 : ℝ) ^ n) * ((2 : ℝ) ^ (n - N₁))
          = Kc * ((3 / 4 : ℝ) ^ n * ((2 : ℝ) ^ N₁ * (2 : ℝ) ^ (n - N₁))) := by ring
        _ = Kc * ((3 / 4 : ℝ) ^ n * (2 : ℝ) ^ n) := by rw [hsplit]
        _ = Kc * (3 / 2 : ℝ) ^ n := by rw [h34]
    have hmulle : (Kc * (2 : ℝ) ^ N₁ * (3 / 4 : ℝ) ^ n) * ((2 : ℝ) ^ (n - N₁))
        ≤ (Kc * (2 : ℝ) ^ N₁ * (3 / 4 : ℝ) ^ n) * (O.a n : ℝ) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    rw [key] at hmulle
    linarith
  · have h1 : Tendsto (fun n : ℕ ↦ (3 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h1.const_mul (Kc * (2 : ℝ) ^ N₁)

/-- `|R n δ n - 𝒜 n| ≤ 3 R n / a n → 0`. -/
theorem R_delta_sub_amp_tendsto_zero :
    Tendsto (fun n ↦ (O.R n : ℝ) * O.delta n - O.amp n) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := O.delta_negPart_comparison
  have hmaj : Tendsto (fun n ↦ 3 * ((O.R n : ℝ) / (O.a n : ℝ))) atTop (𝓝 0) := by
    simpa using O.R_div_a_tendsto_zero.const_mul 3
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop N] with n hn
  have hu : (0 : ℝ) < (O.u n : ℝ) := by exact_mod_cast O.u_pos n
  have ha : (0 : ℝ) < (O.a n : ℝ) := by exact_mod_cast O.a_pos n
  have hR0 : (0 : ℝ) ≤ ((O.R n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hamp : O.amp n = (O.R n : ℝ) * ((O.negPart n : ℝ) / (O.u n : ℝ)) := by
    simp only [amp]; ring
  have h1 : (O.R n : ℝ) * O.delta n - O.amp n
      = (O.R n : ℝ) * (O.delta n - (O.negPart n : ℝ) / (O.u n : ℝ)) := by
    rw [hamp]; ring
  rw [Real.norm_eq_abs, h1, abs_mul, abs_of_nonneg hR0]
  have h2 := hN n hn
  have h3 : ((O.R n : ℕ) : ℝ) * |O.delta n - (O.negPart n : ℝ) / (O.u n : ℝ)|
      ≤ ((O.R n : ℕ) : ℝ) * (3 / (O.a n : ℝ)) := mul_le_mul_of_nonneg_left h2 hR0
  have h4 : ((O.R n : ℕ) : ℝ) * (3 / (O.a n : ℝ)) = 3 * (((O.R n : ℕ) : ℝ) / (O.a n : ℝ)) := by
    field_simp
  linarith [h3, h4.le, h4.ge]

/-! ## 9. The Sylvester side -/

theorem amp_eventually_zero_of_sylvester (h : O.EventuallySylvester) :
    ∃ N, ∀ n, N ≤ n → O.amp n = 0 := by
  obtain ⟨N, hN⟩ := O.reduced_trivial_of_eventual_sylvester h
  exact ⟨N, fun n hn ↦ (hN n hn).2.2.2.2⟩

theorem R_eventually_const_of_sylvester (h : O.EventuallySylvester) :
    ∃ N, ∀ n, N ≤ n → O.R n = O.R N := by
  obtain ⟨N, hN⟩ := O.u_eq_one_of_eventual_sylvester h
  refine ⟨N, fun n hn ↦ ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
      have h1 : O.u (k + 1) = 1 := hN (k + 1) (by omega)
      have h2 : 1 ≤ runningMax O.u k :=
        le_trans (O.u_pos 0) (le_runningMax O.u (Nat.zero_le k))
      have h3 : O.R k = runningMax O.u k := rfl
      show max (runningMax O.u k) (O.u (k + 1)) = O.R N
      rw [h1]
      omega

theorem delta_tendsto_zero : Tendsto O.delta atTop (𝓝 0) := by
  have hinv : Tendsto (fun n ↦ (O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ)) atTop (𝓝 1) := by
    have h := O.growth.inv₀ (by norm_num)
    rw [inv_one] at h
    refine h.congr (fun n ↦ ?_)
    have h1 : (O.a n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (O.a_pos n).ne'
    have h2 : (O.a (n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (O.a_pos (n + 1)).ne'
    field_simp
  have h0 : Tendsto (fun n ↦ max 0 ((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)) atTop
      (𝓝 (max 0 ((1 : ℝ) - 1))) := tendsto_const_nhds.max (hinv.sub_const 1)
  have hz : max (0 : ℝ) ((1 : ℝ) - 1) = 0 := by norm_num
  rw [hz] at h0
  exact h0

/-! ## 10. `long243:res:recordamplified` -/

theorem amp_bddAbove_iff_sylvester :
    O.EventuallySylvester ↔ ∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := O.amp_eventually_zero_of_sylvester h
    refine ⟨0, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [hN n hn]
  · rintro ⟨K, hK⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hK
    refine O.eventuallySylvester_of_amp_le (max 1 ⌈K⌉₊) (le_max_left _ _) N (fun n hn ↦ ?_)
    have h1 : O.amp n ≤ K := hN n hn
    have h2 : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
    have h3 : ((⌈K⌉₊ : ℕ) : ℝ) ≤ ((max 1 ⌈K⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 1 ⌈K⌉₊
    linarith

theorem Rdelta_bddAbove_iff_amp :
    (∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K) ↔
      (∃ K : ℝ, ∀ᶠ n in atTop, (O.R n : ℝ) * O.delta n ≤ K) := by
  have hdiff := O.R_delta_sub_amp_tendsto_zero
  have hev : ∀ᶠ n in atTop, |(O.R n : ℝ) * O.delta n - O.amp n| ≤ 1 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiff 1 (by norm_num)
    filter_upwards [eventually_ge_atTop N] with n hn
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    linarith
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K + 1, ?_⟩
    filter_upwards [hK, hev] with n h1 h2
    have h3 := abs_le.mp h2
    linarith [h3.2]
  · rintro ⟨K, hK⟩
    refine ⟨K + 1, ?_⟩
    filter_upwards [hK, hev] with n h1 h2
    have h3 := abs_le.mp h2
    linarith [h3.1]

/-- **`long243:res:recordamplified` (bounds allowing for previous decreases).**

Under the standing hypotheses the following are equivalent: eventual Sylvester
behaviour; `limsup 𝒜 n < ∞`; `limsup (R n δ n) < ∞`.  Each of those two limits
superior is `0` or `+∞`. -/
theorem recordAmplified :
    (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = ⊤) ∧
      (Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = ⊤) := by
  have h1 : O.EventuallySylvester ↔
      Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop ≠ ⊤ := by
    rw [erealLimsup_ne_top_iff]
    exact O.amp_bddAbove_iff_sylvester
  have h2 : O.EventuallySylvester ↔
      Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop ≠ ⊤ := by
    rw [erealLimsup_ne_top_iff]
    exact O.amp_bddAbove_iff_sylvester.trans O.Rdelta_bddAbove_iff_amp
  refine ⟨h1, h2, ?_, ?_⟩
  · by_cases hs : O.EventuallySylvester
    · left
      obtain ⟨N, hN⟩ := O.amp_eventually_zero_of_sylvester hs
      refine erealLimsup_eq_zero_of_tendsto ?_
      refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hN n hn).symm
    · right
      exact erealLimsup_eq_top (fun hc ↦ hs (h1.mpr ((erealLimsup_ne_top_iff _).mpr hc)))
  · by_cases hs : O.EventuallySylvester
    · left
      refine erealLimsup_eq_zero_of_tendsto ?_
      obtain ⟨N, hN⟩ := O.R_eventually_const_of_sylvester hs
      have hconst : Tendsto (fun n ↦ ((O.R N : ℕ) : ℝ) * O.delta n) atTop (𝓝 0) := by
        simpa using O.delta_tendsto_zero.const_mul ((O.R N : ℕ) : ℝ)
      refine hconst.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [hN n hn]
    · right
      exact erealLimsup_eq_top (fun hc ↦ hs (h2.mpr ((erealLimsup_ne_top_iff _).mpr hc)))

/-! ## 11. `long243:res:criticalrate` -/

theorem R_le_of_u_le {c N : ℕ} (h : ∀ n, N ≤ n → O.u n ≤ c * n) :
    ∀ n, N ≤ n → O.R n ≤ O.R N + c * n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => omega
  | succ k hk ih =>
      have h1 : O.u (k + 1) ≤ c * (k + 1) := h (k + 1) (by omega)
      have h2 : O.R k = runningMax O.u k := rfl
      have h3 : c * k ≤ c * (k + 1) := Nat.mul_le_mul (le_refl c) (by omega)
      show max (runningMax O.u k) (O.u (k + 1)) ≤ O.R N + c * (k + 1)
      omega

/-- **`long243:res:criticalrate` (the critical rate).**

Under the standing hypotheses and `δ n = O(1/n)`, with no convergence of
`n δ n` assumed, eventual Sylvester behaviour is equivalent to `u n = O(n)` and
to `(-ẽ n)₊ = O(1)`. -/
theorem criticalRate
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ))) :
    (O.EventuallySylvester ↔ (fun n : ℕ ↦ (O.u n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ))) ∧
      (O.EventuallySylvester ↔
        (fun n : ℕ ↦ (O.negPart n : ℝ)) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ))) := by
  have hS2 : O.EventuallySylvester →
      (fun n : ℕ ↦ (O.u n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    intro h
    obtain ⟨N, hN⟩ := O.u_eq_one_of_eventual_sylvester h
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have h1 : O.u n = 1 := hN n (le_trans (le_max_left _ _) hn)
    have h2 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hun : ((O.u n : ℕ) : ℝ) = 1 := by rw [h1]; norm_num
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hun, abs_one, abs_of_nonneg hnn, one_mul]
    exact_mod_cast h2
  have hS3 : O.EventuallySylvester →
      (fun n : ℕ ↦ (O.negPart n : ℝ)) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) := by
    intro h
    obtain ⟨N, hN⟩ := O.reduced_trivial_of_eventual_sylvester h
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : O.negPart n = 0 := (hN n hn).2.2.2.1
    rw [Real.norm_eq_abs, h1]
    simp
  have h32 : (fun n : ℕ ↦ (O.negPart n : ℝ)) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) →
      (fun n : ℕ ↦ (O.u n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    intro h
    obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp h
    obtain ⟨N, hN⟩ := eventually_atTop.mp hc
    have hnat : ∀ n, N ≤ n → O.negPart n ≤ ⌈c⌉₊ := by
      intro n hn
      have h1 := hN n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_one, mul_one] at h1
      have h3 : ((O.negPart n : ℕ) : ℝ) ≤ ((⌈c⌉₊ : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil c)
      exact_mod_cast h3
    have hstep : ∀ n, N ≤ n → O.u (n + 1) ≤ O.u n + ⌈c⌉₊ := fun n hn ↦
      le_trans (O.u_succ_le n) (Nat.add_le_add_left (hnat n hn) _)
    have hlin : ∀ n, N ≤ n → O.u n ≤ O.u N + ⌈c⌉₊ * n := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => omega
      | succ k hk ih =>
          have h4 := hstep k hk
          have h5 : ⌈c⌉₊ * k + ⌈c⌉₊ = ⌈c⌉₊ * (k + 1) := by ring
          omega
    rw [Asymptotics.isBigO_iff]
    refine ⟨((O.u N : ℕ) : ℝ) + ((⌈c⌉₊ : ℕ) : ℝ), ?_⟩
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have h5 : O.u n ≤ O.u N + ⌈c⌉₊ * n := hlin n hnN
    have h5R : ((O.u n : ℕ) : ℝ) ≤ ((O.u N : ℕ) : ℝ) + ((⌈c⌉₊ : ℕ) : ℝ) * (n : ℝ) := by
      exact_mod_cast h5
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have huN0 : (0 : ℝ) ≤ ((O.u N : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg hnn]
    nlinarith [h5R, mul_le_mul_of_nonneg_left hn1R huN0]
  have h21 : (fun n : ℕ ↦ (O.u n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ)) →
      O.EventuallySylvester := by
    intro h
    obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp h
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hc
    have hnat : ∀ n, N₁ ≤ n → O.u n ≤ ⌈c⌉₊ * n := by
      intro n hn
      have h1 := hN₁ n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (Nat.cast_nonneg n)] at h1
      have h2 : ((O.u n : ℕ) : ℝ) ≤ ((⌈c⌉₊ : ℕ) : ℝ) * (n : ℝ) :=
        le_trans h1 (mul_le_mul_of_nonneg_right (Nat.le_ceil c) (Nat.cast_nonneg n))
      exact_mod_cast h2
    have hR := O.R_le_of_u_le hnat
    obtain ⟨cd, hcd⟩ := Asymptotics.isBigO_iff.mp hδ
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hcd
    obtain ⟨N₃, hN₃⟩ := O.delta_negPart_comparison
    refine O.amp_bddAbove_iff_sylvester.mpr ⟨((O.R N₁ : ℕ) : ℝ) * cd + ((⌈c⌉₊ : ℕ) : ℝ) * cd
      + 3 * ((O.R N₁ : ℕ) : ℝ) + 3 * ((⌈c⌉₊ : ℕ) : ℝ), ?_⟩
    filter_upwards [eventually_ge_atTop (max (max N₁ N₂) (max N₃ 1))] with n hn
    have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn3 : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hnpos : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    have hu : (0 : ℝ) < (O.u n : ℝ) := by exact_mod_cast O.u_pos n
    have ha : (0 : ℝ) < (O.a n : ℝ) := by exact_mod_cast O.a_pos n
    have han : (n : ℝ) ≤ (O.a n : ℝ) := by
      have hlin := strictMono_nat_linear_lower O.a O.a_strictMono n
      have h0 := O.a_pos 0
      have hnat2 : n ≤ O.a n := by omega
      exact_mod_cast hnat2
    have hd0 : 0 ≤ O.delta n := le_max_left _ _
    have hdb : (n : ℝ) * O.delta n ≤ cd := by
      have h1 := hN₂ n hn2
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hd0,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))] at h1
      have h3 : (n : ℝ) * O.delta n ≤ (n : ℝ) * (cd * (1 / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h4 : (n : ℝ) * (cd * (1 / (n : ℝ))) = cd := by field_simp
      linarith
    have hdle : O.delta n ≤ cd := by
      nlinarith [hdb, mul_le_mul_of_nonneg_right hnR hd0]
    have hcmp := hN₃ n hn3
    have hnpu : (O.negPart n : ℝ) / (O.u n : ℝ) ≤ O.delta n + 3 / (O.a n : ℝ) := by
      have hh := abs_le.mp hcmp
      linarith [hh.1]
    have hRn : O.R n ≤ O.R N₁ + ⌈c⌉₊ * n := hR n hn1
    have hRnR : ((O.R n : ℕ) : ℝ) ≤ ((O.R N₁ : ℕ) : ℝ) + ((⌈c⌉₊ : ℕ) : ℝ) * (n : ℝ) := by
      exact_mod_cast hRn
    have hR0 : (0 : ℝ) ≤ ((O.R n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hRN0 : (0 : ℝ) ≤ ((O.R N₁ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hC0 : (0 : ℝ) ≤ ((⌈c⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hamp : O.amp n = (O.R n : ℝ) * ((O.negPart n : ℝ) / (O.u n : ℝ)) := by
      simp only [amp]; ring
    have hinv : 3 / (O.a n : ℝ) ≤ 3 := by
      rw [div_le_iff₀ ha]; linarith
    have hna : (n : ℝ) / (O.a n : ℝ) ≤ 1 := by
      rw [div_le_one ha]; exact han
    have hA : (O.R n : ℝ) * O.delta n
        ≤ ((O.R N₁ : ℕ) : ℝ) * cd + ((⌈c⌉₊ : ℕ) : ℝ) * cd := by
      have h1 : ((O.R n : ℕ) : ℝ) * O.delta n
          ≤ (((O.R N₁ : ℕ) : ℝ) + ((⌈c⌉₊ : ℕ) : ℝ) * (n : ℝ)) * O.delta n :=
        mul_le_mul_of_nonneg_right hRnR hd0
      have h2 : (((O.R N₁ : ℕ) : ℝ) + ((⌈c⌉₊ : ℕ) : ℝ) * (n : ℝ)) * O.delta n
          = ((O.R N₁ : ℕ) : ℝ) * O.delta n
            + ((⌈c⌉₊ : ℕ) : ℝ) * ((n : ℝ) * O.delta n) := by ring
      have h3 : ((O.R N₁ : ℕ) : ℝ) * O.delta n ≤ ((O.R N₁ : ℕ) : ℝ) * cd :=
        mul_le_mul_of_nonneg_left hdle hRN0
      have h4 : ((⌈c⌉₊ : ℕ) : ℝ) * ((n : ℝ) * O.delta n) ≤ ((⌈c⌉₊ : ℕ) : ℝ) * cd :=
        mul_le_mul_of_nonneg_left hdb hC0
      linarith
    have hB : (O.R n : ℝ) * (3 / (O.a n : ℝ))
        ≤ 3 * ((O.R N₁ : ℕ) : ℝ) + 3 * ((⌈c⌉₊ : ℕ) : ℝ) := by
      have hpos : (0 : ℝ) ≤ 3 / (O.a n : ℝ) := by positivity
      have h1 : ((O.R n : ℕ) : ℝ) * (3 / (O.a n : ℝ))
          ≤ (((O.R N₁ : ℕ) : ℝ) + ((⌈c⌉₊ : ℕ) : ℝ) * (n : ℝ)) * (3 / (O.a n : ℝ)) :=
        mul_le_mul_of_nonneg_right hRnR hpos
      have h2 : (((O.R N₁ : ℕ) : ℝ) + ((⌈c⌉₊ : ℕ) : ℝ) * (n : ℝ)) * (3 / (O.a n : ℝ))
          = ((O.R N₁ : ℕ) : ℝ) * (3 / (O.a n : ℝ))
            + 3 * ((⌈c⌉₊ : ℕ) : ℝ) * ((n : ℝ) / (O.a n : ℝ)) := by
        field_simp
      have h3 : ((O.R N₁ : ℕ) : ℝ) * (3 / (O.a n : ℝ)) ≤ ((O.R N₁ : ℕ) : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left hinv hRN0
      have h4 : 3 * ((⌈c⌉₊ : ℕ) : ℝ) * ((n : ℝ) / (O.a n : ℝ))
          ≤ 3 * ((⌈c⌉₊ : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hna (by linarith)
      linarith
    have hfin : O.amp n ≤ (O.R n : ℝ) * O.delta n + (O.R n : ℝ) * (3 / (O.a n : ℝ)) := by
      rw [hamp]
      have h1 : ((O.R n : ℕ) : ℝ) * ((O.negPart n : ℝ) / (O.u n : ℝ))
          ≤ ((O.R n : ℕ) : ℝ) * (O.delta n + 3 / (O.a n : ℝ)) :=
        mul_le_mul_of_nonneg_left hnpu hR0
      have h2 : ((O.R n : ℕ) : ℝ) * (O.delta n + 3 / (O.a n : ℝ))
          = ((O.R n : ℕ) : ℝ) * O.delta n + ((O.R n : ℕ) : ℝ) * (3 / (O.a n : ℝ)) := by ring
      linarith
    linarith
  exact ⟨⟨hS2, h21⟩, ⟨hS3, fun h ↦ h21 (h32 h)⟩⟩

/-- A counterexample at the critical rate has `limsup u n / n = ∞` and
`limsup (-ẽ n)₊ = ∞`. -/
theorem criticalRate_counterexample
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)))
    (hns : ¬ O.EventuallySylvester) :
    Filter.limsup (fun n ↦ (((O.u n : ℝ) / (n : ℝ) : ℝ) : EReal)) atTop = ⊤ ∧
      Filter.limsup (fun n ↦ ((O.negPart n : ℝ) : EReal)) atTop = ⊤ := by
  obtain ⟨h1, h2⟩ := O.criticalRate hδ
  constructor
  · refine erealLimsup_eq_top ?_
    rintro ⟨K, hK⟩
    refine hns (h1.mpr ?_)
    rw [Asymptotics.isBigO_iff]
    refine ⟨max K 0, ?_⟩
    filter_upwards [hK, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg hnpos.le]
    rw [div_le_iff₀ hnpos] at hn
    have h3 : K * (n : ℝ) ≤ max K 0 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left K 0) hnpos.le
    linarith
  · refine erealLimsup_eq_top ?_
    rintro ⟨K, hK⟩
    refine hns (h2.mpr ?_)
    rw [Asymptotics.isBigO_iff]
    refine ⟨max K 0, ?_⟩
    filter_upwards [hK] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), abs_one,
      mul_one]
    have h3 : K ≤ max K 0 := le_max_left _ _
    linarith

end StandingOrbit

end ErdosProblems.Erdos243.PaperCompleteR21

#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.recordAmplified
#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate
#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate_counterexample
#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.eventuallySylvester_of_amp_le
#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.coprimeMultiplier_cofinal
#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.largePrime_coprimeMultiplier
#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta_negPart_comparison
