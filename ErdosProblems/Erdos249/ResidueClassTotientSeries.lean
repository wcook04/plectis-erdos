import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Erdős #249: residue-class totient series and the isolated-pulse separation

This file formalises the reusable core of the "fixed resolution" attack on

`S = ∑_{n ≥ 1} φ(n) / 2 ^ n`.

Nothing here proves that `S` is irrational.  What is proved is the exact
mechanism that makes every *fixed-resolution* projection of the totient word
irrational, together with the quantitative separation it supplies.

## Main results

* `isolated_pulse_separation` — the abstract Diophantine core.  If `a : ℕ → ℤ`
  is bounded by `C`, and `a` has a nonzero letter `t` at position `p = N+1+L`
  surrounded on both sides by a block of `L` zeros, then for every `q ≥ 1` with
  `2 ^ L > 2 * q * C` the real number `q * ∑ a n / 2 ^ n` stays at distance at
  least `q * (|t| - C / 2 ^ L) / 2 ^ p` from every integer.  Both the left and
  the right zero block are used: the right block makes the tail nonzero, the
  left block makes the tail small enough to be the distance to `ℤ`.

* `two_sided_prime_isolation` — the arithmetic supply.  For `m ≥ 2` and any `r`
  with `gcd (r+1, m) = 1` there are arbitrarily large primes `p` with
  `φ p ≡ r [MOD m]` and `m ∣ φ (p ± j)` for every `0 < j ≤ L`.  Auxiliary
  primes `ℓ_j ≡ 1 [MOD m]` are produced by Dirichlet's theorem and glued by the
  Chinese remainder theorem; `ℓ_j ∣ p ± j` forces `ℓ_j - 1 ∣ φ (p ± j)`.

* `irrational_totientObservable_of_isolated_residue` — the same pulse
  consumer with isolation as a hypothesis, so residues with `gcd(r+1,m) ≠ 1`
  (for example `2` modulo `12`) become eligible once an independent isolation
  argument is supplied.  `irrational_totientObservable` is the special case
  in which `two_sided_prime_isolation` discharges that hypothesis from
  `gcd(r+1,m)=1`.  `fixed_resolution_observable_irrational` is the `m = 2 ^ k`
  specialisation (r02 Theorem 1, forward direction), where the unit condition is
  automatic for every even `r`.

* `residue_series_irrational` — the headline consequence.  For every `m ≥ 3`
  the least-residue series `A_m = ∑_{n} (φ n mod m) / 2 ^ n` is irrational.
  (`A_1 = 0` and `A_2 = 3/4` are rational, so `m ≥ 3` is sharp.)

Not formalised here: the *converse* half of r02 Theorem 1 (rational-valued
letter maps, denominator clearing, and `∑_{r even} V_{k,r} = 1/4`), and the
bit-plane independence Corollary 4 that follows from it.

The mechanism — a bounded integer coefficient sequence with arbitrarily long
two-sided isolated nonzero digits has irrational binary value — is Erdős's 1948
Lambert-series mechanism (P. Erdős, *On arithmetical properties of Lambert
series*, J. Indian Math. Soc. **12** (1948)).  The results here are auxiliary:
they concern the reduced sequences `φ n mod m`, not `φ n` itself, and the
separation they give is of scale `2 ^ (-p)` at the pulse centre `p`, which is
far weaker than what the parent problem needs.
-/

namespace ErdosProblems.Erdos249

open Finset

/-! ## Binary values of bounded integer sequences -/

/-- The binary value `∑ a n / 2 ^ n` of an integer coefficient sequence. -/
noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n

/-- The exact tail `R_N = ∑_{j ≥ 1} a (N + j) / 2 ^ j`. -/
noncomputable def dyadicTail (a : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (a (N + 1 + j) : ℝ) / 2 ^ (j + 1)

theorem summable_const_div_two_pow (c : ℝ) : Summable fun n : ℕ => c / 2 ^ n := by
  refine (summable_geometric_two' (2 * c)).congr fun n => ?_
  ring

theorem summable_const_div_two_pow_succ (c : ℝ) : Summable fun j : ℕ => c / 2 ^ (j + 1) := by
  refine (summable_geometric_two' c).congr fun j => ?_
  rw [pow_succ]
  ring

theorem tsum_const_div_two_pow_succ (c : ℝ) : (∑' j : ℕ, c / 2 ^ (j + 1)) = c := by
  have h : ∀ j : ℕ, c / 2 ^ (j + 1) = c / 2 / 2 ^ j := fun j => by rw [pow_succ]; ring
  rw [tsum_congr h, tsum_geometric_two']

section Dyadic

variable {a : ℕ → ℤ} {C : ℝ}

theorem summable_dyadicTerm (hC : ∀ n, |(a n : ℝ)| ≤ C) :
    Summable fun n : ℕ => (a n : ℝ) / 2 ^ n := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => C / 2 ^ n) (summable_const_div_two_pow C) ?_
  intro n
  dsimp only
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos h2]
  gcongr
  exact hC n

theorem summable_dyadicTailTerm (hC : ∀ n, |(a n : ℝ)| ≤ C) (N : ℕ) :
    Summable fun j : ℕ => (a (N + 1 + j) : ℝ) / 2 ^ (j + 1) := by
  refine Summable.of_norm_bounded (g := fun j : ℕ => C / 2 ^ (j + 1))
    (summable_const_div_two_pow_succ C) ?_
  intro j
  dsimp only
  have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos h2]
  gcongr
  exact hC _

/-- The tail is bounded by the same constant that bounds the coefficients. -/
theorem abs_dyadicTail_le (hC : ∀ n, |(a n : ℝ)| ≤ C) (N : ℕ) : |dyadicTail a N| ≤ C := by
  have hs := summable_dyadicTailTerm hC N
  have hub : ∀ j : ℕ, (a (N + 1 + j) : ℝ) / 2 ^ (j + 1) ≤ C / 2 ^ (j + 1) := by
    intro j
    have h3 : ((a (N + 1 + j) : ℤ) : ℝ) ≤ C := le_trans (le_abs_self _) (hC _)
    gcongr
  have hlb : ∀ j : ℕ, (-C) / 2 ^ (j + 1) ≤ (a (N + 1 + j) : ℝ) / 2 ^ (j + 1) := by
    intro j
    have h3 : -C ≤ ((a (N + 1 + j) : ℤ) : ℝ) := neg_le_of_abs_le (hC _)
    gcongr
  have h1 : dyadicTail a N ≤ C := by
    have h := Summable.tsum_le_tsum hub hs (summable_const_div_two_pow_succ C)
    rwa [tsum_const_div_two_pow_succ C] at h
  have h2 : -C ≤ dyadicTail a N := by
    have h := Summable.tsum_le_tsum hlb (summable_const_div_two_pow_succ (-C)) hs
    rwa [tsum_const_div_two_pow_succ (-C)] at h
  exact abs_le.mpr ⟨h2, h1⟩

/-- `2 ^ N * value = integer + tail`. -/
theorem exists_int_add_dyadicTail (hC : ∀ n, |(a n : ℝ)| ≤ C) (N : ℕ) :
    ∃ P : ℤ, (2 : ℝ) ^ N * dyadicValue a = (P : ℝ) + dyadicTail a N := by
  refine ⟨∑ i ∈ Finset.range (N + 1), a i * 2 ^ (N - i), ?_⟩
  have hs := summable_dyadicTerm hC
  have h := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => (a n : ℝ) / 2 ^ n) (N + 1) hs
  have hpre : (2 : ℝ) ^ N * (∑ i ∈ Finset.range (N + 1), (a i : ℝ) / 2 ^ i)
      = ((∑ i ∈ Finset.range (N + 1), a i * 2 ^ (N - i) : ℤ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N + 1 := Finset.mem_range.mp hi
    have hsp : (2 : ℝ) ^ N = 2 ^ i * 2 ^ (N - i) := by rw [← pow_add]; congr 1; omega
    have h2 : (2 : ℝ) ^ i ≠ 0 := by positivity
    rw [hsp]
    field_simp
  have htail : (2 : ℝ) ^ N * (∑' s : ℕ, (a (s + (N + 1)) : ℝ) / 2 ^ (s + (N + 1)))
      = dyadicTail a N := by
    rw [← tsum_mul_left]
    refine tsum_congr fun s => ?_
    have hidx : s + (N + 1) = N + 1 + s := by omega
    rw [hidx]
    have hpow : (2 : ℝ) ^ (N + 1 + s) = 2 ^ N * 2 ^ (s + 1) := by
      rw [← pow_add]; congr 1; omega
    have h2 : (2 : ℝ) ^ N ≠ 0 := by positivity
    rw [hpow]
    field_simp
  calc (2 : ℝ) ^ N * dyadicValue a
      = (2 : ℝ) ^ N * (∑' n : ℕ, (a n : ℝ) / 2 ^ n) := rfl
    _ = (2 : ℝ) ^ N * ((∑ i ∈ Finset.range (N + 1), (a i : ℝ) / 2 ^ i)
          + ∑' s : ℕ, (a (s + (N + 1)) : ℝ) / 2 ^ (s + (N + 1))) := by rw [← h]
    _ = (2 : ℝ) ^ N * (∑ i ∈ Finset.range (N + 1), (a i : ℝ) / 2 ^ i)
          + (2 : ℝ) ^ N * (∑' s : ℕ, (a (s + (N + 1)) : ℝ) / 2 ^ (s + (N + 1))) := by ring
    _ = _ := by rw [hpre, htail]

/-- Splitting the tail at an isolated pulse: a `2L+1`-window whose only nonzero
letter is the centre `t`, plus a rescaled remainder. -/
theorem dyadicTail_pulse (hC : ∀ n, |(a n : ℝ)| ≤ C) {N L : ℕ} {t : ℤ}
    (hcentre : a (N + 1 + L) = t)
    (hzero : ∀ i, i ≤ 2 * L → i ≠ L → a (N + 1 + i) = 0) :
    dyadicTail a N
      = (t : ℝ) / 2 ^ (L + 1) + dyadicTail a (N + 2 * L + 1) / 2 ^ (2 * L + 1) := by
  have hs := summable_dyadicTailTerm hC N
  have h := Summable.sum_add_tsum_nat_add
    (f := fun j : ℕ => (a (N + 1 + j) : ℝ) / 2 ^ (j + 1)) (2 * L + 1) hs
  have hfin : (∑ i ∈ Finset.range (2 * L + 1), (a (N + 1 + i) : ℝ) / 2 ^ (i + 1))
      = (t : ℝ) / 2 ^ (L + 1) := by
    rw [Finset.sum_eq_single L]
    · rw [hcentre]
    · intro i hi hiL
      have hi' : i < 2 * L + 1 := Finset.mem_range.mp hi
      rw [hzero i (by omega) hiL]
      simp
    · intro hcon
      exact absurd (Finset.mem_range.mpr (by omega)) hcon
  have hkey : ∀ s : ℕ, (a (N + 1 + (s + (2 * L + 1))) : ℝ) / 2 ^ (s + (2 * L + 1) + 1)
      = (1 / 2 ^ (2 * L + 1) : ℝ) * ((a (N + 2 * L + 1 + 1 + s) : ℝ) / 2 ^ (s + 1)) := by
    intro s
    have hidx : N + 1 + (s + (2 * L + 1)) = N + 2 * L + 1 + 1 + s := by omega
    have hpow : (2 : ℝ) ^ (s + (2 * L + 1) + 1) = 2 ^ (2 * L + 1) * 2 ^ (s + 1) := by
      rw [← pow_add]; congr 1; omega
    have h2 : (2 : ℝ) ^ (2 * L + 1) ≠ 0 := by positivity
    rw [hidx, hpow]
    field_simp
  have htail : (∑' s : ℕ, (a (N + 1 + (s + (2 * L + 1))) : ℝ) / 2 ^ (s + (2 * L + 1) + 1))
      = dyadicTail a (N + 2 * L + 1) / 2 ^ (2 * L + 1) :=
    calc (∑' s : ℕ, (a (N + 1 + (s + (2 * L + 1))) : ℝ) / 2 ^ (s + (2 * L + 1) + 1))
        = ∑' s : ℕ, (1 / 2 ^ (2 * L + 1) : ℝ) * ((a (N + 2 * L + 1 + 1 + s) : ℝ) / 2 ^ (s + 1)) :=
          tsum_congr hkey
      _ = (1 / 2 ^ (2 * L + 1) : ℝ) * dyadicTail a (N + 2 * L + 1) := tsum_mul_left
      _ = dyadicTail a (N + 2 * L + 1) / 2 ^ (2 * L + 1) := by ring
  calc dyadicTail a N = ∑' j : ℕ, (a (N + 1 + j) : ℝ) / 2 ^ (j + 1) := rfl
    _ = (∑ i ∈ Finset.range (2 * L + 1), (a (N + 1 + i) : ℝ) / 2 ^ (i + 1))
          + ∑' s : ℕ, (a (N + 1 + (s + (2 * L + 1))) : ℝ) / 2 ^ (s + (2 * L + 1) + 1) := h.symm
    _ = (t : ℝ) / 2 ^ (L + 1) + dyadicTail a (N + 2 * L + 1) / 2 ^ (2 * L + 1) := by
          rw [hfin, htail]

private theorem abs_le_abs_add_abs (X Y : ℝ) : |X| ≤ |X + Y| + |Y| := by
  have h := abs_add_le (X + Y) (-Y)
  simpa using h

private theorem abs_int_add_ge (M : ℤ) {x : ℝ} (hx : |x| < 1 / 2) : |x| ≤ |(M : ℝ) + x| := by
  rcases eq_or_ne M 0 with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ |(M : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h
    have h2 : |(M : ℝ)| ≤ |(M : ℝ) + x| + |x| := abs_le_abs_add_abs _ _
    linarith

/-- **Isolated pulse separation** (r02 Lemma 3, quantitative form).

If the bounded integer sequence `a` has a nonzero letter `t` at `p = N + 1 + L`
with a two-sided block of `L` zeros around it, then for every `q ≥ 1` with
`2 ^ L > 2 * q * C` the number `q * dyadicValue a` stays at distance at least
`q * (|t| - C / 2 ^ L) / 2 ^ p` from every integer `k`. -/
theorem isolated_pulse_separation (hC : ∀ n, |(a n : ℝ)| ≤ C)
    {N L q : ℕ} {t : ℤ} (hq : 1 ≤ q) (hL : 2 * (q : ℝ) * C < 2 ^ L)
    (hcentre : a (N + 1 + L) = t) (ht : t ≠ 0)
    (hzero : ∀ i, i ≤ 2 * L → i ≠ L → a (N + 1 + i) = 0) (k : ℤ) :
    (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (N + 1 + L)
      ≤ |(q : ℝ) * dyadicValue a - (k : ℝ)| := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hLpos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have h2Npos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hLsucc : (0 : ℝ) < (2 : ℝ) ^ (L + 1) := by positivity
  have hL2 : (0 : ℝ) < (2 : ℝ) ^ (2 * L + 1) := by positivity
  -- `q * C / 2 ^ L < 1 / 2`
  have hkey : (q : ℝ) * C / 2 ^ L < 1 / 2 := by
    rw [div_lt_iff₀ hLpos]
    linarith
  have hCsmall : C / 2 ^ L < 1 / 2 := by
    have hle : C ≤ (q : ℝ) * C := by nlinarith
    have : C / 2 ^ L ≤ (q : ℝ) * C / 2 ^ L := by gcongr
    linarith
  have ht1 : (1 : ℝ) ≤ |(t : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs ht
  have htC : |(t : ℝ)| ≤ C := by
    have h := hC (N + 1 + L)
    rwa [hcentre] at h
  -- structure of the tail
  have hsp := dyadicTail_pulse hC hcentre hzero
  have hrem : |dyadicTail a (N + 2 * L + 1) / 2 ^ (2 * L + 1)| ≤ C / 2 ^ (2 * L + 1) := by
    rw [abs_div, abs_of_pos hL2]
    gcongr
    exact abs_dyadicTail_le hC _
  have hctr : |(t : ℝ) / 2 ^ (L + 1)| = |(t : ℝ)| / 2 ^ (L + 1) := by
    rw [abs_div, abs_of_pos hLsucc]
  have hprod : (2 : ℝ) ^ L * 2 ^ (L + 1) = 2 ^ (2 * L + 1) := by
    rw [← pow_add]; congr 1; omega
  -- lower bound on the tail
  have hlower : (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (L + 1) ≤ |dyadicTail a N| := by
    have hh := abs_le_abs_add_abs ((t : ℝ) / 2 ^ (L + 1))
      (dyadicTail a (N + 2 * L + 1) / 2 ^ (2 * L + 1))
    rw [← hsp] at hh
    have hsplit : (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (L + 1)
        = |(t : ℝ)| / 2 ^ (L + 1) - C / 2 ^ (2 * L + 1) := by
      rw [sub_div, div_div, hprod]
    rw [hsplit]
    rw [hctr] at hh
    linarith
  -- upper bound on the tail
  have hupper : |dyadicTail a N| ≤ C / 2 ^ L := by
    have hple : (2 : ℝ) ^ (L + 1) ≤ 2 ^ (2 * L + 1) := by
      apply pow_le_pow_right₀ (by norm_num) (by omega)
    have h5 : C / 2 ^ (2 * L + 1) ≤ C / 2 ^ (L + 1) := by gcongr
    have h6 : |(t : ℝ)| / 2 ^ (L + 1) ≤ C / 2 ^ (L + 1) := by gcongr
    have h7 : C / 2 ^ (L + 1) + C / 2 ^ (L + 1) = C / 2 ^ L := by
      have h2L : (2 : ℝ) ^ L ≠ 0 := by positivity
      rw [pow_succ]
      field_simp
      ring
    calc |dyadicTail a N|
        = |(t : ℝ) / 2 ^ (L + 1) + dyadicTail a (N + 2 * L + 1) / 2 ^ (2 * L + 1)| := by rw [hsp]
      _ ≤ |(t : ℝ) / 2 ^ (L + 1)| + |dyadicTail a (N + 2 * L + 1) / 2 ^ (2 * L + 1)| :=
          abs_add_le _ _
      _ ≤ C / 2 ^ (L + 1) + C / 2 ^ (L + 1) := by rw [hctr]; linarith
      _ = C / 2 ^ L := h7
  -- the integer shift
  obtain ⟨P, hP⟩ := exists_int_add_dyadicTail hC N
  have hEq : (2 : ℝ) ^ N * ((q : ℝ) * dyadicValue a - (k : ℝ))
      = (((q : ℤ) * P - 2 ^ N * k : ℤ) : ℝ) + (q : ℝ) * dyadicTail a N := by
    have hrw : (2 : ℝ) ^ N * ((q : ℝ) * dyadicValue a - (k : ℝ))
        = (q : ℝ) * ((2 : ℝ) ^ N * dyadicValue a) - (2 : ℝ) ^ N * (k : ℝ) := by ring
    rw [hrw, hP]
    push_cast
    ring
  have hsmall : |(q : ℝ) * dyadicTail a N| < 1 / 2 := by
    rw [abs_mul, abs_of_pos hqpos]
    calc (q : ℝ) * |dyadicTail a N| ≤ (q : ℝ) * (C / 2 ^ L) := by gcongr
      _ < 1 / 2 := by rw [← mul_div_assoc]; exact hkey
  have hge : |(q : ℝ) * dyadicTail a N|
      ≤ |(2 : ℝ) ^ N * ((q : ℝ) * dyadicValue a - (k : ℝ))| := by
    rw [hEq]
    exact abs_int_add_ge _ hsmall
  have hfrom : (q : ℝ) * ((|(t : ℝ)| - C / 2 ^ L) / 2 ^ (L + 1))
      ≤ |(q : ℝ) * dyadicTail a N| := by
    rw [abs_mul, abs_of_pos hqpos]
    gcongr
  have habs : |(2 : ℝ) ^ N * ((q : ℝ) * dyadicValue a - (k : ℝ))|
      = 2 ^ N * |(q : ℝ) * dyadicValue a - (k : ℝ)| := by
    rw [abs_mul, abs_of_pos h2Npos]
  have hstep : (q : ℝ) * ((|(t : ℝ)| - C / 2 ^ L) / 2 ^ (L + 1))
      ≤ 2 ^ N * |(q : ℝ) * dyadicValue a - (k : ℝ)| := by
    calc (q : ℝ) * ((|(t : ℝ)| - C / 2 ^ L) / 2 ^ (L + 1))
        ≤ |(q : ℝ) * dyadicTail a N| := hfrom
      _ ≤ |(2 : ℝ) ^ N * ((q : ℝ) * dyadicValue a - (k : ℝ))| := hge
      _ = 2 ^ N * |(q : ℝ) * dyadicValue a - (k : ℝ)| := habs
  have hstep' : (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L)
      ≤ 2 ^ N * |(q : ℝ) * dyadicValue a - (k : ℝ)| * 2 ^ (L + 1) := by
    rw [← mul_div_assoc, div_le_iff₀ hLsucc] at hstep
    linarith
  have hpow : (2 : ℝ) ^ (N + 1 + L) = 2 ^ N * 2 ^ (L + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, div_le_iff₀ (by positivity)]
  calc (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L)
      ≤ 2 ^ N * |(q : ℝ) * dyadicValue a - (k : ℝ)| * 2 ^ (L + 1) := hstep'
    _ = |(q : ℝ) * dyadicValue a - (k : ℝ)| * (2 ^ N * 2 ^ (L + 1)) := by ring

/-- Arbitrarily long two-sided isolated pulses force irrationality of the binary
value.  This is the packaged consumer of `isolated_pulse_separation`. -/
theorem irrational_dyadicValue_of_pulses (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0) :
    Irrational (dyadicValue a) := by
  rintro ⟨x, hx⟩
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hqpos : 0 < x.den := x.pos
  have hq1 : 1 ≤ x.den := hqpos
  have hqR : (1 : ℝ) ≤ (x.den : ℝ) := by exact_mod_cast hq1
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (2 * (x.den : ℝ) * C) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨p, hp, hane, hzero⟩ := hpulse L
  have hNc : p - L - 1 + 1 + L = p := by omega
  have hcentre : a (p - L - 1 + 1 + L) = a p := by rw [hNc]
  have hwin : ∀ i, i ≤ 2 * L → i ≠ L → a (p - L - 1 + 1 + i) = 0 := by
    intro i hi hiL
    rcases Nat.lt_or_ge i L with h | h
    · have hidx : p - L - 1 + 1 + i = p - (L - i) := by omega
      rw [hidx]
      exact (hzero (L - i) (by omega) (by omega)).1
    · have hidx : p - L - 1 + 1 + i = p + (i - L) := by omega
      rw [hidx]
      exact (hzero (i - L) (by omega) (by omega)).2
  have key := isolated_pulse_separation hC hq1 hL hcentre hane hwin x.num
  have hdR : (x.den : ℝ) ≠ 0 := by positivity
  have hvanish : (x.den : ℝ) * dyadicValue a - ((x.num : ℤ) : ℝ) = 0 := by
    rw [← hx, Rat.cast_def]
    field_simp
    ring
  rw [hvanish, abs_zero] at key
  have hLpos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hCsmall : C / 2 ^ L < 1 / 2 := by
    rw [div_lt_iff₀ hLpos]
    nlinarith
  have ht1 : (1 : ℝ) ≤ |((a p : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hane
  have hpos : 0 < (x.den : ℝ) * (|((a p : ℤ) : ℝ)| - C / 2 ^ L) / 2 ^ (p - L - 1 + 1 + L) := by
    apply div_pos
    · apply mul_pos
      · linarith
      · linarith
    · positivity
  linarith

end Dyadic

/-! ## CRT + Dirichlet: two-sided prime isolation -/

private theorem coprime_of_modEq {x y n : ℕ} (h : x ≡ y [MOD n]) (hy : Nat.Coprime y n) :
    Nat.Coprime x n := by
  have h' : x % n = y % n := h
  have h1 : Nat.gcd n x = Nat.gcd n y := by
    rw [Nat.gcd_rec n x, Nat.gcd_rec n y, h']
  have hy' : Nat.gcd n y = 1 := by rw [Nat.gcd_comm]; exact hy
  show Nat.gcd x n = 1
  rw [Nat.gcd_comm, h1]
  exact hy'

private theorem coprime_prime_of_lt {l n : ℕ} (hl : l.Prime) (hn0 : 0 < n) (hn : n < l) :
    Nat.Coprime l n :=
  (Nat.Prime.coprime_iff_not_dvd hl).mpr fun hd => absurd (Nat.le_of_dvd hn0 hd) (by omega)

private theorem dvd_totient_of_prime_dvd {m l n : ℕ} (hl : l.Prime) (hlm : l ≡ 1 [MOD m])
    (hdvd : l ∣ n) : m ∣ Nat.totient n := by
  have h1 : Nat.totient l ∣ Nat.totient n := Nat.totient_dvd_of_dvd hdvd
  rw [Nat.totient_prime hl] at h1
  exact (Nat.modEq_iff_dvd' hl.one_lt.le).mp hlm.symm |>.trans h1

/-- The Chinese-remainder modulus that forces `m ∣ φ (p ± j)` on a window of
half-width `L` around any `p` in a prescribed residue class. -/
theorem exists_isolation_modulus (m : ℕ) (hm : 0 < m) (L : ℕ) :
    ∃ Q b : ℕ, 0 < Q ∧ Nat.Coprime Q m ∧ Nat.Coprime b Q ∧
      ∀ p : ℕ, L < p → p ≡ b [MOD Q] →
        ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (p - j) ∧ m ∣ Nat.totient (p + j) := by
  induction L with
  | zero =>
      refine ⟨1, 1, one_pos, Nat.coprime_one_left m, Nat.coprime_one_left 1, ?_⟩
      intro p _ _ j hj hjL
      exact absurd hjL (by omega)
  | succ L ih =>
      obtain ⟨Q, b, hQ0, hQm, hbQ, hmain⟩ := ih
      obtain ⟨l1, hl1gt, hl1p, hl1m⟩ :=
        Nat.forall_exists_prime_gt_and_modEq (max (max Q m) (L + 1)) (q := m) (a := 1)
          hm.ne' (Nat.coprime_one_left m)
      obtain ⟨l2, hl2gt, hl2p, hl2m⟩ :=
        Nat.forall_exists_prime_gt_and_modEq (max (max (max Q m) (L + 1)) l1) (q := m) (a := 1)
          hm.ne' (Nat.coprime_one_left m)
      simp only [gt_iff_lt, max_lt_iff] at hl1gt hl2gt
      obtain ⟨⟨hQl1, hml1⟩, hLl1⟩ := hl1gt
      obtain ⟨⟨⟨hQl2, hml2⟩, hLl2⟩, hl1l2⟩ := hl2gt
      have cl1Q : Nat.Coprime l1 Q := coprime_prime_of_lt hl1p hQ0 hQl1
      have cl1m : Nat.Coprime l1 m := coprime_prime_of_lt hl1p hm hml1
      have cl1L : Nat.Coprime l1 (L + 1) := coprime_prime_of_lt hl1p (by omega) hLl1
      have cl2Q : Nat.Coprime l2 Q := coprime_prime_of_lt hl2p hQ0 hQl2
      have cl2m : Nat.Coprime l2 m := coprime_prime_of_lt hl2p hm hml2
      have cl2l1 : Nat.Coprime l2 l1 := coprime_prime_of_lt hl2p hl1p.pos hl1l2
      have cl2sub : Nat.Coprime l2 (l2 - (L + 1)) :=
        coprime_prime_of_lt hl2p (by omega) (by omega)
      obtain ⟨k1, hk1a, hk1b⟩ := Nat.chineseRemainder cl1Q.symm b (L + 1)
      have cQl1l2 : Nat.Coprime (Q * l1) l2 := (cl2Q.mul_right cl2l1).symm
      obtain ⟨b', hb'1, hb'2⟩ := Nat.chineseRemainder cQl1l2 k1 (l2 - (L + 1))
      have hb'Q : Nat.Coprime b' Q :=
        coprime_of_modEq ((hb'1.of_dvd ⟨l1, rfl⟩).trans hk1a) hbQ
      have hb'l1 : Nat.Coprime b' l1 :=
        coprime_of_modEq ((hb'1.of_dvd ⟨Q, mul_comm Q l1⟩).trans hk1b) cl1L.symm
      have hb'l2 : Nat.Coprime b' l2 := coprime_of_modEq hb'2 cl2sub.symm
      refine ⟨Q * l1 * l2, b', Nat.mul_pos (Nat.mul_pos hQ0 hl1p.pos) hl2p.pos, ?_, (hb'Q.mul_right hb'l1).mul_right hb'l2, ?_⟩
      · exact ((hQm.symm.mul_right cl1m.symm).mul_right cl2m.symm).symm
      · intro p hp hpb
        have hpQ : p ≡ b [MOD Q] :=
          (((hpb.of_dvd ⟨l1 * l2, by ring⟩).trans (hb'1.of_dvd ⟨l1, rfl⟩)).trans hk1a)
        have hpl1 : p ≡ L + 1 [MOD l1] :=
          (((hpb.of_dvd ⟨Q * l2, by ring⟩).trans
            (hb'1.of_dvd ⟨Q, mul_comm Q l1⟩)).trans hk1b)
        have hpl2 : p ≡ l2 - (L + 1) [MOD l2] :=
          ((hpb.of_dvd ⟨Q * l1, by ring⟩).trans hb'2)
        have hd1 : l1 ∣ p - (L + 1) :=
          (Nat.modEq_iff_dvd' (by omega)).mp hpl1.symm
        have hd2 : l2 ∣ p + (L + 1) := by
          have h5 : p + (L + 1) ≡ l2 - (L + 1) + (L + 1) [MOD l2] := hpl2.add_right (L + 1)
          rw [show l2 - (L + 1) + (L + 1) = l2 from by omega] at h5
          exact Nat.modEq_zero_iff_dvd.mp (h5.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
        intro j hj hjL
        rcases Nat.lt_or_ge j (L + 1) with hcase | hcase
        · exact hmain p (by omega) hpQ j hj (by omega)
        · have hjeq : j = L + 1 := by omega
          subst hjeq
          exact ⟨dvd_totient_of_prime_dvd hl1p hl1m hd1,
            dvd_totient_of_prime_dvd hl2p hl2m hd2⟩

/-- **Two-sided prime isolation** (r02 Lemma 2).

For `m ≥ 2` and any `r` with `gcd (r+1, m) = 1` there are arbitrarily large
primes `p` with `φ p ≡ r [MOD m]` and `m ∣ φ (p ± j)` for every `0 < j ≤ L`. -/
theorem two_sided_prime_isolation {m : ℕ} (hm : 2 ≤ m) (L N r : ℕ)
    (hr : Nat.Coprime (r + 1) m) :
    ∃ p : ℕ, N < p ∧ L + 1 < p ∧ p.Prime ∧ Nat.totient p ≡ r [MOD m] ∧
      ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (p - j) ∧ m ∣ Nat.totient (p + j) := by
  obtain ⟨Q, b, hQ0, hQm, hbQ, hmain⟩ := exists_isolation_modulus m (by omega) L
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hQm b (r + 1)
  have hcQ : Nat.Coprime c Q := coprime_of_modEq hc1 hbQ
  have hcm : Nat.Coprime c m := coprime_of_modEq hc2 hr
  obtain ⟨p, hpgt, hpp, hpc⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N (L + 1)) (q := Q * m) (a := c)
      (Nat.mul_ne_zero hQ0.ne' (by omega)) (hcQ.mul_right hcm)
  rw [gt_iff_lt, max_lt_iff] at hpgt
  refine ⟨p, hpgt.1, hpgt.2, hpp, ?_, ?_⟩
  · have h1 : p ≡ r + 1 [MOD m] := (hpc.of_dvd ⟨Q, mul_comm Q m⟩).trans hc2
    rw [Nat.totient_prime hpp]
    refine Nat.ModEq.add_right_cancel' 1 ?_
    rw [show p - 1 + 1 = p from by omega]
    exact h1
  · intro j hj hjL
    exact hmain p (by omega) ((hpc.of_dvd ⟨m, rfl⟩).trans hc1) j hj hjL

/-! ## Fixed-resolution observables of the totient word -/

/-- The coefficient sequence of a fixed-resolution observable: read the totient
word at resolution `m` and apply an integer-valued letter map `f`. -/
def totientObservableCoeff (f : ℕ → ℤ) (m n : ℕ) : ℤ := f (Nat.totient n % m)

/-- The binary value of a fixed-resolution observable of the totient word. -/
noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n

/-- Coefficient bound used by every isolated-pulse consumer below. -/
theorem abs_totientObservableCoeff_le (f : ℕ → ℤ) {m n : ℕ} (hm : 0 < m) :
    |((totientObservableCoeff f m n : ℤ) : ℝ)|
      ≤ ((∑ i ∈ Finset.range m, |f i| : ℤ) : ℝ) := by
  have hmem : Nat.totient n % m ∈ Finset.range m :=
    Finset.mem_range.mpr (Nat.mod_lt _ hm)
  have hz : |f (Nat.totient n % m)| ≤ ∑ i ∈ Finset.range m, |f i| :=
    Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _) hmem
  calc |((totientObservableCoeff f m n : ℤ) : ℝ)|
      = ((|f (Nat.totient n % m)| : ℤ) : ℝ) := by
        simp only [totientObservableCoeff, Int.cast_abs]
    _ ≤ ((∑ i ∈ Finset.range m, |f i| : ℤ) : ℝ) := by exact_mod_cast hz

/-- **Pulse-criterion application without a unit-centre hypothesis.**

If some residue `r` is attained at centres isolated by arbitrarily long
windows on which `φ` is `0` modulo `m`, then every integer letter map vanishing
at `0` and nonzero at `r` has irrational binary value.  This is the packaged
consumer of `irrational_dyadicValue_of_pulses` for totient observables.
`irrational_totientObservable` is the special case in which
`two_sided_prime_isolation` supplies the windows from `gcd(r+1,m)=1`. -/
theorem irrational_totientObservable_of_isolated_residue
    {m : ℕ} (hm : 0 < m) (f : ℕ → ℤ) (hf0 : f 0 = 0)
    {r : ℕ} (hr : r < m) (hfr : f r ≠ 0)
    (hiso : ∀ L : ℕ, ∃ n : ℕ, L + 1 < n ∧ Nat.totient n ≡ r [MOD m] ∧
      ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (n - j) ∧ m ∣ Nat.totient (n + j)) :
    Irrational (totientObservableValue f m) := by
  have hval : totientObservableValue f m = dyadicValue (totientObservableCoeff f m) := rfl
  have hC : ∀ n : ℕ, |((totientObservableCoeff f m n : ℤ) : ℝ)|
      ≤ ((∑ i ∈ Finset.range m, |f i| : ℤ) : ℝ) := fun n =>
    abs_totientObservableCoeff_le f hm
  have hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ totientObservableCoeff f m p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → totientObservableCoeff f m (p - j) = 0
        ∧ totientObservableCoeff f m (p + j) = 0 := by
    intro L
    obtain ⟨p, hpL, hres, hnb⟩ := hiso L
    refine ⟨p, hpL, ?_, ?_⟩
    · have hmod : Nat.totient p % m = r % m := hres
      simp only [totientObservableCoeff, hmod, Nat.mod_eq_of_lt hr]
      exact hfr
    · intro j hj hjL
      obtain ⟨hd1, hd2⟩ := hnb j hj hjL
      obtain ⟨c1, hc1⟩ := hd1
      obtain ⟨c2, hc2⟩ := hd2
      simp only [totientObservableCoeff]
      exact ⟨by rw [hc1, Nat.mul_mod_right, hf0], by rw [hc2, Nat.mul_mod_right, hf0]⟩
  rw [hval]
  exact irrational_dyadicValue_of_pulses hC hpulse

/-- **The special-value irrationality theorem for fixed-resolution observables.**

If `f` vanishes at the zero residue and is nonzero at some residue `r < m` with
`gcd (r + 1, m) = 1`, then `∑ f (φ n mod m) / 2 ^ n` is irrational.  This is the
strongest correct form of r02 Theorem 1: the classification at `m = 2 ^ k` is
complete precisely because there the unit condition `gcd (r+1, m) = 1` is
automatic for every even `r`. -/
theorem irrational_totientObservable {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℤ) (hf0 : f 0 = 0)
    {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f m) :=
  irrational_totientObservable_of_isolated_residue (by omega) f hf0 hr hfr fun L => by
    obtain ⟨p, -, hpL, -, hres, hnb⟩ := two_sided_prime_isolation hm L 0 r hcop
    exact ⟨p, hpL, hres, hnb⟩

/-- **r02 Theorem 1, forward direction.**  At dyadic resolution `2 ^ k` every
integer-valued letter map that vanishes on the zero residue and is nonzero on
some even residue has irrational binary value.  Here the unit condition of
`irrational_totientObservable` is automatic: `r` even makes `r + 1` odd.

This is the substantive half of the complete rational-relation classification.
The remaining half — clearing denominators of a rational-valued letter map, and
the converse direction supplied by `∑_{r even} V_{k,r} = 1/4` — is not
formalised here. -/
theorem fixed_resolution_observable_irrational {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℤ)
    (hf0 : f 0 = 0) {r : ℕ} (hr : r < 2 ^ k) (hreven : r % 2 = 0) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f (2 ^ k)) := by
  have hm : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : Nat.Coprime 2 (r + 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  exact irrational_totientObservable hm f hf0 hr (Nat.Coprime.pow_right k h2.symm) hfr

/-! ## The least-residue totient series -/

/-- `A_m = ∑_{n} (φ n mod m) / 2 ^ n`, least nonnegative residues. -/
noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n

theorem totientResidueValue_eq (m : ℕ) :
    totientResidueValue m = totientObservableValue (fun x => (x : ℤ)) m := by
  unfold totientResidueValue totientObservableValue
  refine tsum_congr fun n => ?_
  simp only [Int.cast_natCast]

/-- **Corollary 5 of r02.**  For every `m ≥ 3` the least-residue totient series
`A_m = ∑ (φ n mod m) / 2 ^ n` is irrational.

(`A_1 = 0` and `A_2 = 3/4`, so the hypothesis `3 ≤ m` is sharp.) -/
theorem residue_series_irrational {m : ℕ} (hm : 3 ≤ m) :
    Irrational (totientResidueValue m) := by
  have hcop : Nat.Coprime (m - 2 + 1) m := by
    have h : Nat.Coprime (m - 1) (m - 1 + 1) := by simp
    rw [show m - 1 + 1 = m from by omega] at h
    rw [show m - 2 + 1 = m - 1 from by omega]
    exact h
  rw [totientResidueValue_eq]
  refine irrational_totientObservable (by omega) _ (by simp) (by omega) hcop ?_
  simp only [ne_eq, Int.natCast_eq_zero]
  omega

end ErdosProblems.Erdos249
