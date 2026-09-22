import ErdosProblems.Erdos243.PrimitiveRecordBarrier
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.GCD

open scoped BigOperators

/-!
# Erdős 243: the true-record-increment barrier and the historical square payment

This module formalises the finite arithmetic of return `r01`
(`r01_historical_square_payment_true_record_increment`) of the weighted-record
octuple, in the same division-free primitive coordinates as
`PrimitiveRecordBarrier`:

* `w n + v n = a n * u n`        (raw next numerator),
* `w n = hc n * u (n + 1)`       (reduced next numerator),
* `a n * v n = hc n * v (n + 1)` (reduced next denominator),
* `Nat.Coprime (u n) (v n)`, `0 < v n`, `0 < w n`.

The centred error is `e n = v n - (a n - 1) * u n = u n - w n`, and the
nearest-integer normalisation `2 * |e n| < u n` yields the slow-rise bound
`2 * w n ≤ 3 * u n` exactly as in `recordRiseTwo_sylvesterNext_eventually`.

## True record increment versus record-setting jump

Write `R n = runningMax u n` for the running maximum of the primitive
numerators.  Two quantities must be kept apart:

* the **true record increment** `R (n+1) - R n`, and
* the **record-setting jump** `u (n+1) - u n` at an index where a new record is
  set, which decomposes as
  `u (n+1) - u n = (R (n+1) - R n) + (R n - u n)`.

The second summand is the *drawdown* accumulated since the last record.  A
record-setting jump can therefore be large even when the true record increment
is small, because the orbit first has to climb back out of a drawdown.

`PrimitiveRecordBarrier.odd_record_cut` constrains the *jump*
(`u (n+1) ≤ u n + 2` at record steps) and needs `H` odd, because its endgame
excludes the landing `(H - 1, H + 1)` by a parity argument on adjacent coprime
numerators.  The theorem proved here constrains the *increment*
(`R (n+1) ≤ R n + 1`) and needs no parity at all: under a unit increment bound
the crossing lands exactly on `H`, and `p ∣ H` together with `p ∣ v` at the
crossing contradicts primitivity directly.

`r01` §6 supplies the exact fixture that keeps the two hypotheses apart.  The
centred orbit segment

  `(u, v) = (8, 177) →[a = 23] (7, 4071) →[a = 583] (10, 2373393)`

has `23 * 8 - 177 = 7` and `583 * 7 - 4071 = 10`, with cancellation factors
`hc = 1` at both steps.  Its successive record heights are `8` and `10`, so the
true record increment is `2`, while the record-setting jump is `10 - 7 = 3`.
Since `Nat.gcd 8 10 = 2`, successive *record heights* need not be coprime even
though adjacent primitive numerators are.  The fixture does not refute a
true-record-increment theorem; it refutes the transfer of the odd-cut proof
step from jumps to increments.  It is checked below in `example`s.

## Contents

1. `valuation_drop_le_half_cancellation` — the per-step form of the historical
   square payment (`r01` Lemma 1, equations (13)–(15)): erasing one unit of
   `p`-valuation from the reduced denominator costs two units in the
   cancellation factor.  Proved for an arbitrary prime `p`, with no oddness and
   no bound on `hc`.
2. `factorization_drop_telescope`, `cumulative_erasure_factorization_sum`,
   `cumulative_erasure_square` — the telescoped form (`r01` Lemma 1,
   equations (11)–(12)): if `p ^ b ∣ v T` and `p` has disappeared by `s`, then
   `p ^ (2 * b)` divides the product of the cancellation factors over
   `[T, s)`.
3. `unit_recordIncrement_cut` — the finite core of `r01` Theorem 4: a protected
   prime power plus eventual unit record increments bounds the numerators.
4. `recordIncrementOne_sylvesterNext_eventually` — the composed consumer,
   mirroring `recordRiseTwo_sylvesterNext_eventually`.
5. `centeredZero_eventually_runningMax_const` — the converse direction's finite
   content: on a vanishing-error tail the numerators are `1`, so the running
   maximum is eventually constant and the unit-increment hypothesis holds.

## Claim ceiling

Erdős #243 remains open, and nothing here changes that.  The supply of fresh
large prime powers is an explicit hypothesis (`hsupply`), exactly as in
`PrimitiveRecordBarrier`.  Its ordinary proof (`r01` Theorem 4, equations
(36)–(38)) argues that a late fresh multiplier `a j` must carry an exact prime
power exceeding `B = R (j+1) + 2`, since otherwise `a j ∣ lcm (1, …, B)` and
`log a j ≤ B log B = exp (o j)`, contradicting `log a j ≥ c * 2 ^ j`.  That
argument needs `log (R n) = o n` and the doubly exponential multiplier growth,
neither of which is available in this Lean development.  The unit-increment
hypothesis `hinc` is likewise assumed, not derived: `r01` §7 records explicitly
that the original assumptions have not been shown to force it.
-/

namespace ErdosProblems.Erdos243

/-! ## 0. The exact fixture of `r01` §6

These `example`s check that the segment quoted in the module docstring really
is an exact centred primitive orbit segment with trivial cancellation, that its
true record increment is `2` while its record-setting jump is `3`, and that its
successive record heights share the factor `2`. -/

/-- The two steps of the fixture satisfy the division-free cocycle exactly,
with cancellation factor `1` at both steps. -/
example :
    (7 : ℕ) + 177 = 23 * 8 ∧ (7 : ℕ) = 1 * 7 ∧ (23 : ℕ) * 177 = 1 * 4071 ∧
    (10 : ℕ) + 4071 = 583 * 7 ∧ (10 : ℕ) = 1 * 10 ∧
    (583 : ℕ) * 4071 = 1 * 2373393 := by
  norm_num

/-- Each state of the fixture is primitive. -/
example :
    Nat.gcd 8 177 = 1 ∧ Nat.gcd 7 4071 = 1 ∧ Nat.gcd 10 2373393 = 1 := by
  norm_num

/-- The fixture satisfies the nearest-integer normalisation `2 * |e| < u` at
both steps: `e = u - w` is `8 - 7 = 1` and `7 - 10 = -3`. -/
example : 2 * (1 : ℕ) < 8 ∧ 2 * (3 : ℕ) < 7 := by
  norm_num

/-- The running record heights are `8`, `8`, `10`: the true record increment is
`2` and the record-setting jump is `3`.  The two record heights are not
coprime, so the odd-cut parity step does not transfer from jumps to
increments. -/
example :
    max (8 : ℕ) 7 = 8 ∧ max (max (8 : ℕ) 7) 10 = 10 ∧
    (10 : ℕ) - 7 = 3 ∧ (10 : ℕ) - max (8 : ℕ) 7 = 2 ∧ Nat.gcd 8 10 = 2 := by
  norm_num

/-! ## 1. The historical square payment, one step

`r01` Lemma 1, equations (13)–(15), in divisibility form.  The proof of
`primitive_valuation_no_drop` shows that a valuation drop requires
`ν_p (hc) > ν_p a`; the present statement quantifies the cost of that drop
against the cancellation factor, using only `hc ∣ Nat.gcd (w) (a * v)` and the
exact square identity `Nat.gcd w (a * v) = Nat.gcd w (a ^ 2)` of
`rawNext_gcd_eq_gcd_sq`. -/

/-- **Per-step historical square payment.**  For one primitive step with an
arbitrary cancellation factor `hc`, the positive part of the `p`-valuation drop
in the reduced denominator is at most half the `p`-valuation of `hc`:

`2 * (ν_p (v) - ν_p (v')) ≤ ν_p (hc)`

(the subtraction is truncated, so this is exactly the positive part).

No oddness, no bound on `hc`, and no hypothesis on `p` beyond primality.  The
mechanism is: `hc ∣ w` and `hc ∣ a * v` force `hc ∣ Nat.gcd w (a ^ 2) ∣ a ^ 2`,
hence `ν_p hc ≤ 2 * ν_p a`; and the denominator cocycle gives
`ν_p hc + ν_p v' = ν_p a + ν_p v`, so a drop of `d > 0` means
`ν_p hc = ν_p a + d`, whence `2 * d ≤ ν_p hc`. -/
theorem valuation_drop_le_half_cancellation
    {a u v w hc u' v' p : ℕ}
    (hp : p.Prime)
    (hcop : Nat.Coprime u v)
    (hvpos : 0 < v)
    (hq : w + v = a * u)
    (hwpos : 0 < w)
    (hnum : w = hc * u')
    (hden : a * v = hc * v') :
    2 * (v.factorization p - v'.factorization p) ≤ hc.factorization p := by
  have hau : 0 < a * u := by omega
  have ha0 : a ≠ 0 := by rintro rfl; simp at hau
  have hu0 : u ≠ 0 := by rintro rfl; simp at hau
  have hw0 : w ≠ 0 := by omega
  have hv0 : v ≠ 0 := by omega
  have hhc0 : hc ≠ 0 := by rintro rfl; simp at hnum; omega
  have hv'0 : v' ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hden
    exact (Nat.mul_ne_zero ha0 hv0) hden
  have ha20 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
  -- The cancellation factor divides the square of the multiplier.
  have hhcw : hc ∣ w := ⟨u', hnum⟩
  have hhcav : hc ∣ a * v := ⟨v', hden⟩
  have hhcsq : hc ∣ a ^ 2 := by
    have hg : hc ∣ Nat.gcd w (a * v) := Nat.dvd_gcd hhcw hhcav
    rw [rawNext_gcd_eq_gcd_sq hcop hq] at hg
    exact hg.trans (Nat.gcd_dvd_right w (a ^ 2))
  have hgamma2 : hc.factorization p ≤ 2 * a.factorization p := by
    have hdvd : p ^ hc.factorization p ∣ a ^ 2 :=
      dvd_trans (Nat.ordProj_dvd hc p) hhcsq
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp ha20).mp hdvd
    have hsq : (a ^ 2).factorization p = a.factorization p + a.factorization p := by
      rw [pow_two, Nat.factorization_mul ha0 ha0, Finsupp.add_apply]
    omega
  -- The denominator cocycle is an exact valuation identity.
  have hprod :
      hc.factorization p + v'.factorization p
        = a.factorization p + v.factorization p := by
    have h1 : (hc * v').factorization p = (a * v).factorization p := by rw [← hden]
    rwa [Nat.factorization_mul hhc0 hv'0, Nat.factorization_mul ha0 hv0,
      Finsupp.add_apply, Finsupp.add_apply] at h1
  omega

/-! ## 2. The telescoped square payment

`r01` Lemma 1, equations (11)–(12).  Summing the per-step bound over a window
converts historical *disappearance* of a prime from the reduced denominator
into a square divisibility for the accumulated cancellation content
`G = ∏ hc`. -/

/-- Telescoped form of `valuation_drop_le_half_cancellation`: twice the net
`p`-valuation drop of the reduced denominator across `[T, s)` is at most the
total `p`-valuation of the cancellation factors on that window. -/
theorem factorization_drop_telescope
    (a u v w hc : ℕ → ℕ) (p T : ℕ)
    (hp : p.Prime)
    (hred : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, T ≤ n → 0 < v n)
    (hw : ∀ n, T ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, T ≤ n → 0 < w n)
    (hnum : ∀ n, T ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, T ≤ n → a n * v n = hc n * v (n + 1)) :
    ∀ s, T ≤ s →
      2 * ((v T).factorization p - (v s).factorization p)
        ≤ ∑ n ∈ Finset.Ico T s, (hc n).factorization p := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      have hstep :=
        valuation_drop_le_half_cancellation hp (hred k hk) (hvpos k hk) (hw k hk)
          (hwpos k hk) (hnum k hk) (hden k hk)
      rw [Finset.sum_Ico_succ_top hk]
      omega

/-- **Historical square payment, valuation form** (`r01` (11)).  If the prime
`p` has disappeared from the reduced denominator by index `s`, then twice its
valuation at `T` is paid inside the cancellation factors on `[T, s)`.

The prime may re-enter the denominator after `s`; the statement is about the
window `[T, s)` only, and the divisibility it yields (below) persists in every
longer product because the cancellation factors are positive. -/
theorem cumulative_erasure_factorization_sum
    (a u v w hc : ℕ → ℕ) (p T s : ℕ)
    (hp : p.Prime)
    (hred : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, T ≤ n → 0 < v n)
    (hw : ∀ n, T ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, T ≤ n → 0 < w n)
    (hnum : ∀ n, T ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, T ≤ n → a n * v n = hc n * v (n + 1))
    (hTs : T ≤ s)
    (hgone : ¬ p ∣ v s) :
    2 * (v T).factorization p ≤ ∑ n ∈ Finset.Ico T s, (hc n).factorization p := by
  have hzero : (v s).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hgone
  have htel :=
    factorization_drop_telescope a u v w hc p T hp hred hvpos hw hwpos hnum hden s hTs
  omega

/-- **Historical square payment, divisibility form** (`r01` (11)–(12)).  If
`p ^ b ∣ v T` and `p` has disappeared from the reduced denominator by some
`s > T`, then `p ^ (2 * b)` divides the accumulated cancellation content
`∏ n ∈ [T, s), hc n`.

Erasing a prime power from the primitive denominator costs its square in the
cancellation product.  The prime is free to re-enter the denominator at a later
index; the divisibility already banked on `[T, s)` is not undone by that, and
it persists in any longer product `∏ n ∈ [T, s')` with `s ≤ s'` because every
`hc n` is a positive factor. -/
theorem cumulative_erasure_square
    (a u v w hc : ℕ → ℕ) (p b T s : ℕ)
    (hp : p.Prime)
    (hred : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, T ≤ n → 0 < v n)
    (hw : ∀ n, T ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, T ≤ n → 0 < w n)
    (hnum : ∀ n, T ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, T ≤ n → a n * v n = hc n * v (n + 1))
    (hTs : T ≤ s)
    (hb : p ^ b ∣ v T)
    (hgone : ¬ p ∣ v s) :
    p ^ (2 * b) ∣ ∏ n ∈ Finset.Ico T s, hc n := by
  have hvT0 : v T ≠ 0 := by have := hvpos T le_rfl; omega
  have hble : b ≤ (v T).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hvT0).mp hb
  have hsum :=
    cumulative_erasure_factorization_sum a u v w hc p T s hp hred hvpos hw hwpos
      hnum hden hTs hgone
  have hcne : ∀ n ∈ Finset.Ico T s, hc n ≠ 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have h1 := hwpos n hn.1
    have h2 := hnum n hn.1
    rintro h0
    rw [h0] at h2
    simp at h2
    omega
  have hprodne : (∏ n ∈ Finset.Ico T s, hc n) ≠ 0 := Finset.prod_ne_zero_iff.mpr hcne
  have hfact : (∏ n ∈ Finset.Ico T s, hc n).factorization p
      = ∑ n ∈ Finset.Ico T s, (hc n).factorization p := by
    rw [Nat.factorization_prod hcne]
    exact Finset.sum_apply' p
  exact (Nat.Prime.pow_dvd_iff_le_factorization hp hprodne).mpr (by omega)

/-! ## 3. The unit-increment cut

`r01` Theorem 4, equations (38)–(44).  This is the finite core: it replaces the
parity endgame of `odd_record_cut` by an exact landing forced by the unit
record increment. -/

/-- The least multiple of `p` strictly above `R` lies in `(R, R + p]`. -/
theorem exists_multipleOfPrime_just_above (p R : ℕ) (hp : 0 < p) :
    ∃ H, p ∣ H ∧ R < H ∧ H ≤ R + p := by
  refine ⟨p * (R / p) + p, ⟨R / p + 1, by ring⟩, ?_, ?_⟩ <;>
  · have hdm : p * (R / p) + R % p = R := Nat.div_add_mod R p
    have hlt : R % p < p := Nat.mod_lt _ hp
    omega

/-- **Unit-increment protected cut** (`r01` Theorem 4, finite part).

Along a primitive orbit with arbitrary cancellation satisfying the centring
bound `2 * w n ≤ 3 * u n` from index `s`, suppose

* `p` is a prime (odd is *not* required) with `1 ≤ l` and `p ^ l ∣ v s`,
* the prime power dominates the current record, `runningMax u s + 3 ≤ p ^ l`,
* every step increases the running maximum by at most one:
  `runningMax u (n + 1) ≤ runningMax u n + 1` for `n ≥ s`.

Then the numerators are bounded from `s` onward.

The hypothesis is on *increments of the running maximum*, not on record-setting
jumps: the jump `u (n+1) - u n` at a record step may be arbitrarily large,
because it can be recovering a drawdown.  This is exactly the difference from
`odd_record_cut`, and it is why no parity argument appears: the unit increment
forces the first crossing of the trap height `H` to land exactly on `H`, and
`p ∣ H` together with the protected `p ∣ v` contradicts primitivity at once. -/
theorem unit_recordIncrement_cut
    (a u v w hc : ℕ → ℕ) (p l s : ℕ)
    (hp : p.Prime)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hbig : runningMax u s + 3 ≤ p ^ l)
    (hinc : ∀ n, s ≤ n → runningMax u (n + 1) ≤ runningMax u n + 1) :
    ∃ H, ∀ n, s ≤ n → u n < H := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨H, hpH, hRH, hHle⟩ :=
    exists_multipleOfPrime_just_above p (runningMax u s) hp.pos
  -- `3 * H < 2 * p ^ (l + 1)`: the protection height clears the trap height.
  have hheight : 3 * H < 2 * p ^ (l + 1) := by
    have hstep : p ^ (l + 1) = p * p ^ l := by rw [pow_succ, Nat.mul_comm]
    have h1 : p * (runningMax u s + 3) ≤ p * p ^ l := Nat.mul_le_mul_left p hbig
    have h2 : p * (runningMax u s + 3) = p * runningMax u s + 3 * p := by ring
    have h3 : 2 * runningMax u s ≤ p * runningMax u s :=
      Nat.mul_le_mul_right _ hp2
    omega
  refine ⟨H, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨n₀, hn₀s, hn₀H⟩ := hcon
  have hQex : ∃ n, s ≤ n ∧ H ≤ u n := ⟨n₀, hn₀s, by omega⟩
  obtain ⟨τ, hτs, hτH, hbelow⟩ :
      ∃ τ, s ≤ τ ∧ H ≤ u τ ∧ ∀ k, s ≤ k → k < τ → u k < H := by
    refine ⟨Nat.find hQex, (Nat.find_spec hQex).1, (Nat.find_spec hQex).2, ?_⟩
    intro k hk hkτ
    by_contra hcon2
    exact absurd (Nat.find_min' hQex ⟨hk, by omega⟩) (by omega)
  -- The crossing cannot happen at `s` itself.
  have hτne : τ ≠ s := by
    intro hEq
    have h1 : u s ≤ runningMax u s := le_runningMax u (le_refl s)
    rw [hEq] at hτH
    omega
  obtain ⟨t, rfl⟩ : ∃ t, τ = t + 1 := ⟨τ - 1, by omega⟩
  have hts : s ≤ t := by omega
  -- The prime power still divides the denominator at the crossing.
  have hprotτ : p ^ l ∣ v (t + 1) :=
    protectedPrimePower_persists a u v w hc p l s H hp hred hvpos hw hwpos hnum hden
      hslow hheight hprot (t + 1) hτs hbelow
  have hpvτ : p ∣ v (t + 1) := dvd_trans (dvd_pow_self p (by omega)) hprotτ
  -- Everything before the crossing is below `H`, so the record is too.
  have hRt : runningMax u t < H := by
    refine runningMax_lt u (fun k hk ↦ ?_)
    rcases Nat.lt_or_ge k s with hks | hks
    · exact lt_of_le_of_lt (le_runningMax u (by omega)) hRH
    · exact hbelow k hks (by omega)
  -- The unit increment forces the landing to be exactly `H`.
  have hRt1 : runningMax u (t + 1) ≤ H := by
    have := hinc t hts
    omega
  have huH : u (t + 1) = H := by
    have h1 : u (t + 1) ≤ runningMax u (t + 1) := le_runningMax u (le_refl (t + 1))
    omega
  have hpu : p ∣ u (t + 1) := by rw [huH]; exact hpH
  have hgcd : p ∣ Nat.gcd (u (t + 1)) (v (t + 1)) := Nat.dvd_gcd hpu hpvτ
  rw [(hred (t + 1) (by omega)).gcd_eq_one] at hgcd
  have := Nat.le_of_dvd Nat.one_pos hgcd
  omega

/-! ## 4. The composed consumer

Mirrors `recordRiseTwo_sylvesterNext_eventually` verbatim in shape.  Only two
hypotheses change: the record condition is on increments of the running maximum
rather than on record-setting jumps, and the prime-power supply drops the
oddness requirement and asks for `runningMax u s + 3 ≤ p ^ l` in place of
`3 * runningMax u s < p ^ l`. -/

/-- **True-record-increment rigidity, conditional on the fresh prime-power
supply** (`r01` Theorem 4).

Along a dynamically reduced primitive reciprocal tail with *arbitrary*
cancellation, if

* the nearest-integer normalisation `2 * |e n| < u n` holds eventually,
* the normalised error vanishes (`∀ K, eventually K * |e n| < u n`),
* the running maximum increases by at most one at every late step, and
* fresh prime powers `p ^ l ∣ v s` with `runningMax u s + 3 ≤ p ^ l` occur at
  arbitrarily late indices `s`,

then `a (n + 1) = a n ^ 2 - a n + 1` from some index onward.

The first two hypotheses are the packet's normalisation facts, shared with
`recordRiseTwo_sylvesterNext_eventually`.  `hinc` is the record condition of
`r01` (35) and is *assumed*, not derived.  `hsupply` is the analytic bridge of
`r01` (36)–(38) and is likewise assumed.  No parity hypothesis appears. -/
theorem recordIncrementOne_sylvesterNext_eventually
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (N : ℕ)
    (hvpos : ∀ n, N ≤ n → 0 < v n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, N ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, N ≤ n → 0 < w n)
    (hnum : ∀ n, N ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, N ≤ n → a n * v n = hc n * v (n + 1))
    (he : ∀ n, N ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hcentre : ∀ n, N ≤ n → 2 * (e n).natAbs < u n)
    (hvanish : ∀ K, ∃ M, ∀ n, M ≤ n → K * (e n).natAbs < u n)
    (hinc : ∀ n, N ≤ n → runningMax u (n + 1) ≤ runningMax u n + 1)
    (hsupply : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ runningMax u s + 3 ≤ p ^ l) :
    ∃ M, ∀ n, M ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  classical
  -- The centring bound gives the unconditional slow-rise estimate `2 w ≤ 3 u`.
  have hslow : ∀ n, N ≤ n → 2 * w n ≤ 3 * u n := by
    intro n hn
    have hE : e n = (u n : ℤ) - (w n : ℤ) := by
      rw [he n hn]; exact primitiveError_eq_sub (hw n hn)
    have hb := hcentre n hn
    have habs : (e n).natAbs = ((u n : ℤ) - (w n : ℤ)).natAbs := by rw [hE]
    rcases Nat.lt_or_ge (u n) (w n) with hlt | hle
    · have : ((u n : ℤ) - (w n : ℤ)).natAbs = w n - u n := by
        rw [Int.natAbs_eq_iff]
        right
        push_cast
        omega
      omega
    · omega
  -- Step 1: a late vanishing centred error must exist.
  have hzeroExists : ∃ n, N ≤ n ∧ e n = 0 := by
    by_contra hcon
    push_neg at hcon
    -- Otherwise the numerator is unbounded.
    have hunb : ∀ K, ∃ M, ∀ n, M ≤ n → K ≤ u n := by
      intro K
      obtain ⟨M, hM⟩ := hvanish K
      refine ⟨max M N, fun n hn ↦ ?_⟩
      have hnM : M ≤ n := le_trans (le_max_left _ _) hn
      have hnN : N ≤ n := le_trans (le_max_right _ _) hn
      have hne : e n ≠ 0 := hcon n hnN
      have h1 : 1 ≤ (e n).natAbs := by
        rcases Nat.eq_zero_or_pos (e n).natAbs with h | h
        · exact absurd (Int.natAbs_eq_zero.mp h) hne
        · exact h
      have := hM n hnM
      nlinarith
    -- But the unit-increment cut bounds it from a late fresh source.
    obtain ⟨s, hsN, p, l, hp, hl, hprot, hbig⟩ := hsupply N
    obtain ⟨H, hH⟩ :=
      unit_recordIncrement_cut a u v w hc p l s hp hl
        (fun n hn ↦ hred n (by omega)) (fun n hn ↦ hvpos n (by omega))
        (fun n hn ↦ hw n (by omega)) (fun n hn ↦ hwpos n (by omega))
        (fun n hn ↦ hnum n (by omega)) (fun n hn ↦ hden n (by omega))
        (fun n hn ↦ hslow n (by omega)) hprot hbig
        (fun n hn ↦ hinc n (by omega))
    obtain ⟨M, hM⟩ := hunb H
    have := hM (max M s) (le_max_left _ _)
    have := hH (max M s) (le_max_right _ _)
    omega
  obtain ⟨n₀, hn₀N, hn₀⟩ := hzeroExists
  -- Step 2: a vanishing centred error is absorbing.
  have habsorb : ∀ n, n₀ ≤ n → e n = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hn₀
    | succ k hk ih =>
        have hkN : N ≤ k := by omega
        have hzero : (v k : ℤ) - ((a k : ℤ) - 1) * (u k : ℤ) = 0 := by
          rw [← he k hkN]; exact ih
        obtain ⟨_, _, _, hu'1⟩ :=
          centeredZero_forces_unit (hred k hkN) (hw k hkN) (hnum k hkN) hzero
        have hb := hcentre (k + 1) (by omega)
        rw [hu'1] at hb
        have : (e (k + 1)).natAbs = 0 := by omega
        exact Int.natAbs_eq_zero.mp this
  -- Step 3: consecutive zeros pin the Sylvester step.
  refine ⟨max n₀ N, fun n hn ↦ ?_⟩
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hz : (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ) = 0 := by
    rw [← he n hnN]; exact habsorb n hn0
  have hz' : (v (n + 1) : ℤ) - ((a (n + 1) : ℤ) - 1) * (u (n + 1) : ℤ) = 0 := by
    rw [← he (n + 1) (by omega)]; exact habsorb (n + 1) (by omega)
  exact sylvesterStep_of_centeredZero_pair (hred n hnN)
    (hw n hnN) (hnum n hnN) (hden n hnN) hz hz'

/-! ## 5. The converse direction's finite content

`r01` §5 closing paragraph: on a Sylvester tail `x n = 1 / (a n - 1)`, so the
primitive numerator is eventually `1` and the running maximum stops moving.
That is the finite half of the exact criterion
`(S) ↔ #{n : R (n+1) - R n ≥ 2} < ∞`; the analytic half is not proved here. -/

/-- On a tail where the centred error vanishes identically, every primitive
numerator equals `1`. -/
theorem centeredZero_eventually_numerator_one
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (n₀ : ℕ)
    (hred : ∀ n, n₀ ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, n₀ ≤ n → w n + v n = a n * u n)
    (hnum : ∀ n, n₀ ≤ n → w n = hc n * u (n + 1))
    (he : ∀ n, n₀ ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hzero : ∀ n, n₀ ≤ n → e n = 0) :
    ∀ n, n₀ ≤ n → u n = 1 := by
  intro n hn
  have hz : (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ) = 0 := by
    rw [← he n hn]; exact hzero n hn
  exact (centeredZero_forces_unit (hred n hn) (hw n hn) (hnum n hn) hz).1

/-- Consequently the running maximum is eventually constant, so the
true-record-increment hypothesis `hinc` of
`recordIncrementOne_sylvesterNext_eventually` holds on such a tail with
increment `0`.  This is the easy converse of `r01` (45). -/
theorem centeredZero_eventually_runningMax_const
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (n₀ : ℕ)
    (hred : ∀ n, n₀ ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, n₀ ≤ n → w n + v n = a n * u n)
    (hnum : ∀ n, n₀ ≤ n → w n = hc n * u (n + 1))
    (he : ∀ n, n₀ ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hzero : ∀ n, n₀ ≤ n → e n = 0) :
    ∀ n, n₀ ≤ n → runningMax u (n + 1) = runningMax u n := by
  have hone := centeredZero_eventually_numerator_one a u v w hc e n₀ hred hw hnum he hzero
  intro n hn
  have h1 : u n₀ ≤ runningMax u n := le_runningMax u hn
  have h2 : u (n + 1) = 1 := hone (n + 1) (by omega)
  have h3 : u n₀ = 1 := hone n₀ le_rfl
  simp only [runningMax]
  omega

/-!
## Remaining bridges and the claim ceiling

`recordIncrementOne_sylvesterNext_eventually` is fully proved from its
hypotheses.  Three of those hypotheses are inputs this module does **not**
derive:

* `hsupply` — the fresh large prime-power supply.  `r01` (36)–(38) argues that
  a late fresh multiplier `a j` carries an exact prime power above
  `R (j+1) + 2`, because otherwise `a j ∣ lcm (1, …, B)` with `B = R (j+1) + 2`
  and `log a j ≤ B log B = exp (o j)`, contradicting `log a j ≥ c * 2 ^ j`.
  That needs `log (R n) = o n` and the doubly exponential multiplier growth,
  neither of which is formalised in this root.  Note the supply here is weaker
  than the one in `PrimitiveRecordBarrier`: no oddness is required, and the
  height demand is `runningMax u s + 3 ≤ p ^ l` rather than
  `3 * runningMax u s < p ^ l`.
* `hinc` — the true record increment bound `R (n+1) - R n ≤ 1`.  `r01` §7 states
  explicitly that the original assumptions have not been shown to force it, and
  that small record increments can coexist with large accumulated cancellation.
* `hvanish` — the normalised vanishing `∀ K, eventually K * |e n| < u n`, the
  same hypothesis carried by `recordRiseTwo_sylvesterNext_eventually` and by
  `boundedNegativePart_sylvesterNext_eventually` in `ReciprocalTailRigidity`.

Erdős #243 therefore remains open.  Nothing in this module bounds the
cancellation factors, and nothing derives either record hypothesis.

-- OPEN: `r01` Theorem 2, the finite record–retirement dichotomy.  Statement:
-- for fresh indices `j₁ < … < j_m < T < N` with `Q = ∏ a (j i)`, if
-- `R N ≥ R T + Q` then either the retired sources pay their square into `G N`
-- (which is `cumulative_erasure_square` above) or some `n ∈ [T, N)` has record
-- increment `≥ k + 1` where `k` counts the unretired sources.  Not formalised:
-- the second alternative needs a Chinese-remainder construction of a forbidden
-- block `x, x+1, …, x+k-1` of numerator values (r01 (21)–(22)) together with a
-- freshness notion for the multipliers, neither of which exists in these
-- primitive coordinates yet.

-- OPEN: `r01` Theorem 3, primitive record growth versus accumulated
-- cancellation.  It spends the square payment against the freshness and height
-- estimates and needs the same analytic growth inputs as `hsupply`.

-- CHECKED: the fixture of `r01` §6 is exact (see the `example`s at the head of
-- this module).  It confirms that `odd_record_cut`'s parity endgame cannot be
-- reused for true record increments, and it is the reason
-- `unit_recordIncrement_cut` is proved by an exact-landing argument instead.
-- It is a finite fixture, not a counterexample to anything.
-/

end ErdosProblems.Erdos243
