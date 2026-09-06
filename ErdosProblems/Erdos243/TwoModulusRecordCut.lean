import ErdosProblems.Erdos243.PrimitiveRecordBarrier
import Mathlib.Tactic.NormNum.GCD

/-!
# Erdős 243: the two-modulus record cut

This module formalises return `r06` Lemma 3 (the "two-modulus cut").  It
extends the odd protected cut `odd_record_cut` of `PrimitiveRecordBarrier`
from record jumps of size at most `2` to record jumps of size at most `4`, by
using **two** forbidden landings instead of one.

## The mechanism

`odd_record_cut` blocks a first crossing of an odd height `H` with `p ∣ H`
using one forbidden landing (`u' = H`, killed by `p ∣ v'`) plus the parity of
the single surviving pair `(H - 1, H + 1)`.  With jumps up to `4` there are
five candidate landings, and one forbidden landing no longer suffices.

Take `H ≡ 5 (mod 6)` and two moduli `m > 1`, `l > 1` that persist in the
reduced denominator, with `m ∣ H` and `l ∣ H + 2`.  Then

* `u' = H`     is killed by `m ∣ u'`, `m ∣ v'` and `Nat.Coprime u' v'`;
* `u' = H + 2` is killed by `l` in exactly the same way;
* `u' = H + 4` would force `u ≥ H`, contradicting `u < H`;
* `u' = H + 1` leaves `u ∈ {H-3, H-2, H-1}`; since `H ≡ 5 (mod 6)`, the pairs
  `(H-3, H+1)` and `(H-1, H+1)` are both even and `(H-2, H+1)` are both
  divisible by `3`, each contradicting `Nat.Coprime u u'`;
* `u' = H + 3` forces `u = H - 1`, and `H - 1`, `H + 3` are both even.

The congruence `H ≡ 5 (mod 6)` is doing all the parity work: it makes `H + 1`
divisible by `6`, so it collides with `H - 3`, `H - 2` and `H - 1` in turn.

## Where this stops

The cut does **not** extend unchanged to jumps of size `5`.  A genuine
primitive step realises the escape:

`u = 33`, `v = 5 * 37 * 41 = 7585`, `a = 231`, `w = 38`, `hc = 1`,
`u' = 38`, `v' = 231 * 7585`, centred error `e = u - w = -5`.

Take `H = 35`: `35 % 6 = 5`, `m = 5 ∣ 35`, `l = 37 ∣ 37 = H + 2`, both moduli
divide `v` and `v'`, both pairs are coprime, `u < H ≤ u'`, and the jump is
`u' - u = 5`.  Both forbidden landings are crossed in a single step.  See the
`example` below, which checks every hypothesis of `two_modulus_cut` except
`hjump`.

Claim ceiling: Erdős #243 remains open.  Persistence of the two moduli in the
reduced denominator is a **hypothesis** here; in `r06` it is discharged for
primes that never disappear from the denominator, which is itself an open
analytic input of the same shape as `hsupply` in `PrimitiveRecordBarrier`.
-/

namespace ErdosProblems.Erdos243

/-! ## 1. The finite two-modulus cut (r06 Lemma 3) -/

/-- **Two-modulus cut.**  With `H ≡ 5 (mod 6)`, a modulus `m > 1` dividing
both `H` and the next reduced denominator, and a modulus `l > 1` dividing both
`H + 2` and the next reduced denominator, no primitive step can cross `H` with
a jump of at most `4`.

The hypotheses `m ∣ v`, `l ∣ v` and `Nat.Coprime u v` of the return's
statement are not needed: only the *next* pair carries the forbidden-landing
obstruction, and the current pair contributes only through adjacent
coprimality `Nat.Coprime u u'`.  This is a strengthening, not a weakening. -/
theorem two_modulus_cut
    {H m l u u' v' : ℕ}
    (hH : H % 6 = 5)
    (hmH : m ∣ H) (hlH : l ∣ H + 2)
    (hm1 : 1 < m) (hl1 : 1 < l)
    (hmv' : m ∣ v') (hlv' : l ∣ v')
    (hcop' : Nat.Coprime u' v')
    (hadj : Nat.Coprime u u')
    (hlo : u < H) (hhi : H ≤ u') (hjump : u' ≤ u + 4) :
    False := by
  have hgcd1 : Nat.gcd u u' = 1 := hadj.gcd_eq_one
  have habs2 : u % 2 = 0 → u' % 2 = 0 → False := by
    intro h1 h2
    have hdvd : 2 ∣ Nat.gcd u u' :=
      Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
    rw [hgcd1] at hdvd
    have := Nat.le_of_dvd Nat.one_pos hdvd
    omega
  have habs3 : u % 3 = 0 → u' % 3 = 0 → False := by
    intro h1 h2
    have hdvd : 3 ∣ Nat.gcd u u' :=
      Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
    rw [hgcd1] at hdvd
    have := Nat.le_of_dvd Nat.one_pos hdvd
    omega
  have hkillH : u' = H → False := by
    intro hEq
    have hmu : m ∣ u' := by rw [hEq]; exact hmH
    have hdvd : m ∣ Nat.gcd u' v' := Nat.dvd_gcd hmu hmv'
    rw [hcop'.gcd_eq_one] at hdvd
    have := Nat.le_of_dvd Nat.one_pos hdvd
    omega
  have hkillH2 : u' = H + 2 → False := by
    intro hEq
    have hlu : l ∣ u' := by rw [hEq]; exact hlH
    have hdvd : l ∣ Nat.gcd u' v' := Nat.dvd_gcd hlu hlv'
    rw [hcop'.gcd_eq_one] at hdvd
    have := Nat.le_of_dvd Nat.one_pos hdvd
    omega
  have hcases : u' = H ∨ u' = H + 1 ∨ u' = H + 2 ∨ u' = H + 3 ∨ u' = H + 4 := by
    omega
  rcases hcases with h | h | h | h | h
  · exact hkillH h
  · have hsub : u + 3 = H ∨ u + 2 = H ∨ u + 1 = H := by omega
    rcases hsub with hu | hu | hu
    · exact habs2 (by omega) (by omega)
    · exact habs3 (by omega) (by omega)
    · exact habs2 (by omega) (by omega)
  · exact hkillH2 h
  · exact habs2 (by omega) (by omega)
  · omega

/-- The five-unit escape fixture: a genuine primitive step
`(u, v) = (33, 7585)`, `a = 231`, `w = 38`, `hc = 1`, `u' = 38`,
`v' = 231 * 7585`, crossing both forbidden landings of `H = 35` in one jump of
size `5` with coprime endpoints.  Every hypothesis of `two_modulus_cut` holds
except `hjump : u' ≤ u + 4`. -/
example :
    (35 : ℕ) % 6 = 5 ∧ (5 : ℕ) ∣ 35 ∧ (37 : ℕ) ∣ 35 + 2 ∧
      (5 : ℕ) ∣ 7585 ∧ (37 : ℕ) ∣ 7585 ∧
      (5 : ℕ) ∣ 231 * 7585 ∧ (37 : ℕ) ∣ 231 * 7585 ∧
      Nat.Coprime 33 7585 ∧ Nat.Coprime 38 (231 * 7585) ∧ Nat.Coprime 33 38 ∧
      (38 : ℕ) + 7585 = 231 * 33 ∧
      (33 : ℕ) < 35 ∧ (35 : ℕ) ≤ 38 ∧ (38 : ℕ) = 33 + 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

-- OPEN: the two-modulus cut is sharp at jump 4.  Extending it to jump 5 would
-- need a third forbidden landing (a modulus dividing `H + 4`, say), and the
-- fixture above shows no purely congruential strengthening of the present
-- hypotheses can do it: `(33, 38)` crosses `H = 35` past both `m = 5` and
-- `l = 37` with coprime endpoints on both sides.

/-! ## 2. The orbit-level cut, in the shape of `odd_record_cut` -/

/-- **Two-modulus record cut.**  If two moduli `m, l > 1` persist in the
reduced denominator from index `s` onward, `H ≡ 5 (mod 6)` sits above the
running numerator maximum at `s` with `m ∣ H` and `l ∣ H + 2`, and every
record-setting step from `s` onward rises by at most `4`, then the orbit never
reaches `H`.

Compared with `odd_record_cut`: the jump budget is `4` rather than `2`, and
the prime-power protection machinery (`primitive_valuation_no_drop`,
`protectedPrimePower_persists`, the centring bound `2 * w n ≤ 3 * u n` and the
height condition `3 * H < 2 * p ^ (l + 1)`) is replaced by the bare
persistence hypotheses `hmv` and `hlv`.  Persistence is therefore assumed,
not derived: this theorem is a cut, not a supply lemma.

No hypothesis is imposed at non-record steps, and no bound is imposed on the
cancellation factors `hc n`. -/
theorem two_modulus_record_cut
    (a u v w hc : ℕ → ℕ) (m l s H : ℕ)
    (hm1 : 1 < m) (hl1 : 1 < l)
    (hH : H % 6 = 5)
    (hmH : m ∣ H) (hlH : l ∣ H + 2)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hmv : ∀ n, s ≤ n → m ∣ v n)
    (hlv : ∀ n, s ≤ n → l ∣ v n)
    (hRs : runningMax u s < H)
    (hrec : ∀ n, s ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 4) :
    ∀ n, s ≤ n → u n < H := by
  classical
  by_contra hcon
  push Not at hcon
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
  -- The crossing is a global record, so the jump budget applies.
  have hRt : runningMax u t < H := by
    refine runningMax_lt u (fun k hk ↦ ?_)
    rcases Nat.lt_or_ge k s with hks | hks
    · exact lt_of_le_of_lt (le_runningMax u (by omega)) hRs
    · exact hbelow k hks (by omega)
  have hrecord : runningMax u t < u (t + 1) := by omega
  have hjump := hrec t hts hrecord
  have hut : u t < H := hbelow t hts (by omega)
  -- Adjacent reduced numerators are coprime.
  have hcopnum : Nat.Coprime (u t) (u (t + 1)) := by
    have h1 : Nat.Coprime (u t) (w t) :=
      rawNext_coprime_currentNumerator (hred t hts) (hw t hts)
    exact h1.coprime_dvd_right ⟨hc t, by rw [hnum t hts]; ring⟩
  exact two_modulus_cut hH hmH hlH hm1 hl1 (hmv (t + 1) (by omega))
    (hlv (t + 1) (by omega)) (hred (t + 1) (by omega)) hcopnum hut hτH hjump

end ErdosProblems.Erdos243
