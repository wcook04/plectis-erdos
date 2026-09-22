import ErdosProblems.Erdos243.DynamicCancellation
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Erdős 243: prime-power barriers for record numerator jumps

This module formalises the finite arithmetic of the record-jump barrier for a
*dynamically reduced* reciprocal tail, i.e. one in which an arbitrary
cancellation factor `hc n` is removed at every step.  Writing the reduced tail
as `u n / v n` in lowest terms, the step is the division-free cocycle

* `w n + v n = a n * u n`      (raw next numerator),
* `w n = hc n * u (n + 1)`     (reduced next numerator),
* `a n * v n = hc n * v (n + 1)` (reduced next denominator).

`DynamicCancellation` already supplies the primitive identities
`Nat.gcd (w n) (a n * v n) = Nat.gcd (w n) (a n ^ 2)` and
`Nat.Coprime (u n) (w n)`; the second gives `Nat.Coprime (u n) (u (n + 1))`
because `u (n + 1) ∣ w n`.

The chain proved here is:

1. `primitive_valuation_no_drop` — a prime power `p ^ l ∣ v n` cannot leave the
   reduced denominator while the *raw* numerator stays below `p ^ (l + 1)`.
   This is the only place where arbitrary cancellation is controlled: no bound
   on `hc n` is used anywhere.
2. `protectedPrimePower_persists` — the persistence of that prime power up to
   and including the first index at which `u` reaches a height `H` with
   `3 * H < 2 * p ^ (l + 1)`.
3. `odd_record_cut` — if `H` is an *odd* multiple of `p` above the running
   numerator maximum, the orbit can never reach `H` at all, provided every
   record-setting step rises by at most `2`.  The first crossing would have to
   be a record; `p ∣ v` kills the landing `u = H`, and the only other option
   `(H - 1, H + 1)` has both endpoints even, contradicting adjacent-numerator
   coprimality.
4. `recordRiseTwo_sylvesterNext_eventually` — the composed consumer.  The
   analytic *supply* of fresh odd large prime powers is an explicit hypothesis;
   see the module note at the end for exactly which bridges remain open.

Nothing in this module is conditional on a bound for the cancellation factors,
and no hypothesis is imposed at non-record steps.
-/

namespace ErdosProblems.Erdos243

/-! ## 1. The valuation-loss threshold

r07 Lemma 1 / r08 Lemma 2.  Stated with `p ^ l ∣ v` rather than `p ^ l ‖ v`:
the divisibility form is strictly stronger, because `w < p ^ (l + 1)` is then
also below `p ^ (ν_p v + 1)`. -/

/-- **Valuation-loss threshold.**  For one primitive step with arbitrary
cancellation `hc`, a prime power dividing the reduced denominator survives the
step as long as the raw numerator stays below the next power of `p`.

Only `hc ∣ w` (via `hnum`) and the denominator cocycle `hden` are used, so this
holds for every admissible cancellation factor, not only for
`hc = Nat.gcd w (a * v)`. -/
theorem primitive_valuation_no_drop
    {a u v w hc u' v' p l : ℕ}
    (hp : p.Prime)
    (hcop : Nat.Coprime u v)
    (hvpos : 0 < v)
    (hq : w + v = a * u)
    (hwpos : 0 < w)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (hl : p ^ l ∣ v)
    (hlt : w < p ^ (l + 1)) :
    p ^ l ∣ v' := by
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · simp
  -- Positivity bookkeeping.
  have hau : 0 < a * u := by omega
  have ha0 : a ≠ 0 := by rintro rfl; simp at hau
  have hu0 : u ≠ 0 := by rintro rfl; simp at hau
  have hw0 : w ≠ 0 := by omega
  have hv0 : v ≠ 0 := by omega
  have hhc0 : hc ≠ 0 := by rintro rfl; simp at hnum; omega
  have hv'0 : v' ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hden
    have : a * v ≠ 0 := Nat.mul_ne_zero ha0 hv0
    exact this hden
  -- `p` cannot divide the reduced numerator.
  have hpv : p ∣ v := dvd_trans (dvd_pow_self p (by omega)) hl
  have hpu : ¬ p ∣ u := by
    intro hpu
    have hgcd : p ∣ Nat.gcd u v := Nat.dvd_gcd hpu hpv
    rw [hcop.gcd_eq_one] at hgcd
    have := Nat.le_of_dvd Nat.one_pos hgcd
    exact absurd this (by have := hp.two_le; omega)
  -- Valuations.
  have hlmu : l ≤ v.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hv0).mp hl
  have hbeta : w.factorization p ≤ l := by
    by_contra hcon
    have hdvd : p ^ (l + 1) ∣ w :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hw0).mpr (by omega)
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hhcw : hc ∣ w := ⟨u', hnum⟩
  have hgamma : hc.factorization p ≤ w.factorization p := by
    have hdvd : p ^ (hc.factorization p) ∣ w :=
      dvd_trans (Nat.ordProj_dvd hc p) hhcw
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hw0).mp hdvd
  have hprod :
      hc.factorization p + v'.factorization p
        = a.factorization p + v.factorization p := by
    have h1 : (hc * v').factorization p = (a * v).factorization p := by rw [← hden]
    rwa [Nat.factorization_mul hhc0 hv'0, Nat.factorization_mul ha0 hv0,
      Finsupp.add_apply, Finsupp.add_apply] at h1
  -- The two cases of r07 Lemma 1, packaged as a single inequality on `ν_p v'`.
  have hkey : l ≤ v'.factorization p := by
    by_cases hcase : l ≤ a.factorization p
    · omega
    · -- `ν_p a < l ≤ ν_p v` forces `ν_p (hc) ≤ ν_p w = ν_p a`.
      have hgammaA : hc.factorization p ≤ a.factorization p := by
        by_contra hcon
        set α := a.factorization p with hα
        have hpaw : p ^ (α + 1) ∣ w :=
          dvd_trans (pow_dvd_pow p (by omega)) (dvd_trans (Nat.ordProj_dvd hc p) hhcw)
        have hpav : p ^ (α + 1) ∣ v :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp hv0).mpr (by omega)
        have hpasum : p ^ (α + 1) ∣ a * u := by
          rw [← hq]; exact Nat.dvd_add hpaw hpav
        have hcopu : Nat.Coprime (p ^ (α + 1)) u :=
          Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu)
        have hpa : p ^ (α + 1) ∣ a := hcopu.dvd_of_dvd_mul_right hpasum
        have := (Nat.Prime.pow_dvd_iff_le_factorization hp ha0).mp hpa
        omega
      omega
  exact (Nat.Prime.pow_dvd_iff_le_factorization hp hv'0).mpr hkey

/-! ## 2. Persistence up to a first height crossing (r07 Lemma 2) -/

/-- **Protected prime power.**  Along a primitive orbit with arbitrary
cancellation satisfying the centring bound `2 * w n ≤ 3 * u n` from index `s`,
a prime power `p ^ l ∣ v s` divides `v n` at every index `n ≥ s` such that
every strictly earlier index of the window has `u k < H`, provided
`3 * H < 2 * p ^ (l + 1)`.

The window hypothesis is stated without a first-crossing primitive, so the
conclusion also holds *at* the crossing index itself. -/
theorem protectedPrimePower_persists
    (a u v w hc : ℕ → ℕ) (p l s H : ℕ)
    (hp : p.Prime)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hheight : 3 * H < 2 * p ^ (l + 1))
    (hprot : p ^ l ∣ v s) :
    ∀ n, s ≤ n → (∀ k, s ≤ k → k < n → u k < H) → p ^ l ∣ v n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; exact hprot
  | succ k hk ih =>
      intro hwin
      have hprev : p ^ l ∣ v k := ih (fun j hj hjk ↦ hwin j hj (by omega))
      have huk : u k < H := hwin k hk (by omega)
      have hwk : w k < p ^ (l + 1) := by
        have h1 := hslow k hk
        omega
      exact primitive_valuation_no_drop hp (hred k hk) (hvpos k hk) (hw k hk)
        (hwpos k hk) (hnum k hk) (hden k hk) hprev hwk

/-! ## 3. The running numerator maximum -/

/-- Running maximum `R n = max_{k ≤ n} u k` of a numerator sequence. -/
def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

theorem le_runningMax (u : ℕ → ℕ) {k n : ℕ} (h : k ≤ n) : u k ≤ runningMax u n := by
  induction n with
  | zero => have : k = 0 := by omega
            subst this; exact le_rfl
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (le_max_left _ _)
      · have : k = m + 1 := by omega
        subst this
        exact le_max_right _ _

theorem runningMax_lt (u : ℕ → ℕ) {n H : ℕ} (h : ∀ k, k ≤ n → u k < H) :
    runningMax u n < H := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ m ih =>
      have h1 : runningMax u m < H := ih (fun k hk ↦ h k (by omega))
      have h2 : u (m + 1) < H := h (m + 1) le_rfl
      simp only [runningMax]
      omega

/-! ## 4. The odd protected cut (r07 Lemma 3) -/

/-- **Odd protected cut.**  Suppose the primitive orbit satisfies the centring
bound from index `s`, that `p ^ l ∣ v s` for an odd height `H` that is a
multiple of `p` with `runningMax u s < H` and `3 * H < 2 * p ^ (l + 1)`, and
that every record-setting step from `s` onward rises by at most `2`.  Then the
orbit never reaches `H`.

No hypothesis whatsoever is imposed at non-record steps, and no bound is
imposed on the cancellation factors `hc n`. -/
theorem odd_record_cut
    (a u v w hc : ℕ → ℕ) (p l s H : ℕ)
    (hp : p.Prime)
    (hl : 1 ≤ l)
    (hHodd : Odd H)
    (hpH : p ∣ H)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hheight : 3 * H < 2 * p ^ (l + 1))
    (hprot : p ^ l ∣ v s)
    (hRs : runningMax u s < H)
    (hrec : ∀ n, s ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 2) :
    ∀ n, s ≤ n → u n < H := by
  classical
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
  obtain ⟨t, rfl⟩ : ∃ t, τ = t + 1 := by
    refine ⟨τ - 1, ?_⟩
    have : 0 < τ := by omega
    omega
  have hts : s ≤ t := by omega
  -- The prime power still divides the denominator at the crossing.
  have hprotτ : p ^ l ∣ v (t + 1) :=
    protectedPrimePower_persists a u v w hc p l s H hp hred hvpos hw hwpos hnum hden
      hslow hheight hprot (t + 1) hτs hbelow
  have hpvτ : p ∣ v (t + 1) := dvd_trans (dvd_pow_self p (by omega)) hprotτ
  -- The crossing is a global record.
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
  -- Landing exactly on `H` is impossible: `p` divides `H` and `v (t+1)`.
  have hne : u (t + 1) ≠ H := by
    intro hEq
    have hpu : p ∣ u (t + 1) := by rw [hEq]; exact hpH
    have hgcd : p ∣ Nat.gcd (u (t + 1)) (v (t + 1)) := Nat.dvd_gcd hpu hpvτ
    rw [(hred (t + 1) (by omega)).gcd_eq_one] at hgcd
    have := Nat.le_of_dvd Nat.one_pos hgcd
    have := hp.two_le
    omega
  -- The only remaining crossing is `(H - 1, H + 1)`, both even.
  obtain ⟨m, hm⟩ := hHodd
  have hxy : u t = H - 1 ∧ u (t + 1) = H + 1 := by omega
  have htwo : 2 ∣ Nat.gcd (u t) (u (t + 1)) := by
    refine Nat.dvd_gcd ?_ ?_
    · omega
    · omega
  rw [hcopnum.gcd_eq_one] at htwo
  omega

/-! ## 5. The prime-power trap (r07 Corollary 4) -/

/-- A large odd prime power above `3 * R` supplies an odd multiple of `p` that
is both above `R` and below the protection height `2 * p ^ (l + 1) / 3`. -/
theorem exists_oddMultiple_trapHeight
    {p l R : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) (hl : 1 ≤ l)
    (hbig : 3 * R < p ^ l) :
    ∃ H, Odd H ∧ p ∣ H ∧ R < H ∧ 3 * H < 2 * p ^ (l + 1) := by
  classical
  have hex : ∃ j, R < p * (2 * j + 1) := by
    refine ⟨R, ?_⟩
    calc R < 2 * (2 * R + 1) := by omega
      _ ≤ p * (2 * R + 1) := Nat.mul_le_mul_right _ hp2
  obtain ⟨j, hjspec, hjmin⟩ :
      ∃ j, R < p * (2 * j + 1) ∧ ∀ i, i < j → ¬ R < p * (2 * i + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi ↦ Nat.find_min hex hi⟩
  refine ⟨p * (2 * j + 1), ?_, ⟨2 * j + 1, rfl⟩, hjspec, ?_⟩
  · exact hpodd.mul ⟨j, by ring⟩
  · -- `H ≤ p ^ l`, then `3 * p ^ l < 2 * p ^ (l + 1)`.
    have hple : p * (2 * j + 1) ≤ p ^ l := by
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        calc p * (2 * 0 + 1) = p := by ring
          _ ≤ p ^ l := Nat.le_self_pow (by omega) p
      · -- `j > 0`, so `j - 1` fails the predicate and `p ≤ R`.
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hmin : ¬ R < p * (2 * k + 1) := hjmin k (by omega)
        have hzero : ¬ R < p * (2 * 0 + 1) := hjmin 0 (by omega)
        have hpR : p ≤ R := by
          have : p * (2 * 0 + 1) = p := by ring
          omega
        have hk1 : p * (2 * k + 1) ≤ R := by omega
        calc p * (2 * (k + 1) + 1) = p * (2 * k + 1) + 2 * p := by ring
          _ ≤ R + 2 * R := Nat.add_le_add hk1 (by omega)
          _ = 3 * R := by ring
          _ ≤ p ^ l := Nat.le_of_lt hbig
    have hppos : 0 < p ^ l := pow_pos (by omega) l
    have hstep : p ^ (l + 1) = p * p ^ l := by rw [pow_succ]; ring
    have hlt2 : 3 * p ^ l < 2 * (p * p ^ l) := by nlinarith
    omega

/-! ## 6. Bounded numerator from a single fresh odd source -/

/-- The odd cut, fed by a prime power above `3 * runningMax u s`.  This is the
form the supply lemma produces. -/
theorem numerator_bounded_of_oddPrimePower
    (a u v w hc : ℕ → ℕ) (p l s : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hbig : 3 * runningMax u s < p ^ l)
    (hrec : ∀ n, s ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 2) :
    ∃ H, ∀ n, s ≤ n → u n < H := by
  obtain ⟨H, hHodd, hpH, hRs, hheight⟩ :=
    exists_oddMultiple_trapHeight (p := p) (l := l) (R := runningMax u s)
      hp.two_le hpodd hl hbig
  exact ⟨H, odd_record_cut a u v w hc p l s H hp hl hHodd hpH hred hvpos hw hwpos
    hnum hden hslow hheight hprot hRs hrec⟩

/-! ## 7. Composition to the Sylvester endpoint

The primitive centred error is `e n = v n - (a n - 1) * u n`, so that
`e n = u n - w n` as integers.  A vanishing centred error is absorbing under
the nearest-integer normalisation `2 * |e n| < u n`, and it pins the multiplier
exactly. -/

/-- The primitive centred error is the numerator deficit `u n - w n`. -/
theorem primitiveError_eq_sub
    {a u v w : ℕ} (hq : w + v = a * u) :
    ((v : ℤ) - ((a : ℤ) - 1) * (u : ℤ)) = (u : ℤ) - (w : ℤ) := by
  have hcast : (w : ℤ) + (v : ℤ) = (a : ℤ) * (u : ℤ) := by exact_mod_cast hq
  linarith

/-- Under the nearest-integer normalisation, a vanishing centred error forces
`u n = 1` and `w n = 1`, hence `u (n + 1) = 1` and `hc n = 1`. -/
theorem centeredZero_forces_unit
    {a u v w hc u' : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hzero : (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ) = 0) :
    u = 1 ∧ w = 1 ∧ hc = 1 ∧ u' = 1 := by
  have hstep : (u : ℤ) - (w : ℤ) = 0 := by
    rw [← primitiveError_eq_sub (a := a) (u := u) (v := v) (w := w) hq]; exact hzero
  have huw : u = w := by exact_mod_cast (by linarith : (u : ℤ) = (w : ℤ))
  have hcopw : Nat.Coprime u w := rawNext_coprime_currentNumerator hcop hq
  have hu1 : u = 1 := by
    have : Nat.gcd u w = 1 := hcopw.gcd_eq_one
    rw [← huw, Nat.gcd_self] at this
    exact this
  have hw1 : w = 1 := by omega
  have : hc * u' = 1 := by omega
  have := Nat.eq_one_of_mul_eq_one_right this
  refine ⟨hu1, hw1, this, ?_⟩
  have h2 : hc * u' = 1 := by omega
  exact Nat.eq_one_of_mul_eq_one_left h2

/-- Two consecutive vanishing centred errors pin the Sylvester step exactly. -/
theorem sylvesterStep_of_centeredZero_pair
    {a a' u v w hc u' v' : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (hzero : (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ) = 0)
    (hzero' : (v' : ℤ) - ((a' : ℤ) - 1) * (u' : ℤ) = 0) :
    (a' : ℤ) = sylvesterNext (a : ℤ) := by
  obtain ⟨hu1, hw1, hhc1, hu'1⟩ :=
    centeredZero_forces_unit hcop hq hnum hzero
  subst hu1
  have hv : (v : ℤ) = (a : ℤ) - 1 := by linarith [hzero]
  have hv' : (v' : ℤ) = (a' : ℤ) - 1 := by
    rw [hu'1] at hzero'
    push_cast at hzero' ⊢
    linarith
  have hdenZ : (a : ℤ) * (v : ℤ) = (hc : ℤ) * (v' : ℤ) := by exact_mod_cast hden
  rw [hhc1] at hdenZ
  push_cast at hdenZ
  rw [hv, hv'] at hdenZ
  simp only [sylvesterNext]
  nlinarith [hdenZ]

/-! ## 8. The composed consumer -/

/-- **Record-jump rigidity, conditional on the fresh odd prime-power supply.**

Along a dynamically reduced primitive reciprocal tail with *arbitrary*
cancellation, if

* the nearest-integer normalisation `2 * |e n| < u n` holds eventually,
* the normalised error vanishes (`∀ K, eventually K * |e n| < u n`),
* every record-setting step rises by at most `2`, and
* fresh odd prime powers `p ^ l ∣ v s` with `3 * runningMax u s < p ^ l` occur
  at arbitrarily late indices `s`,

then `a (n + 1) = a n ^ 2 - a n + 1` from some index onward.

The first three hypotheses are the packet's own normalisation facts.  The
fourth is the *analytic bridge* (r07 Lemmas 5-7 / r08 Lemma 4): it is stated
here, not derived.  See the closing note. -/
theorem recordRiseTwo_sylvesterNext_eventually
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
    (hrec : ∀ n, N ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 2)
    (hsupply : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ Odd p ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ 3 * runningMax u s < p ^ l) :
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
    -- But the odd cut bounds it from a late fresh source.
    obtain ⟨s, hsN, p, l, hp, hpodd, hl, hprot, hbig⟩ := hsupply N
    obtain ⟨H, hH⟩ :=
      numerator_bounded_of_oddPrimePower a u v w hc p l s hp hpodd hl
        (fun n hn ↦ hred n (by omega)) (fun n hn ↦ hvpos n (by omega))
        (fun n hn ↦ hw n (by omega)) (fun n hn ↦ hwpos n (by omega))
        (fun n hn ↦ hnum n (by omega)) (fun n hn ↦ hden n (by omega))
        (fun n hn ↦ hslow n (by omega)) hprot hbig
        (fun n hn ↦ hrec n (by omega))
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

/-!
## Remaining analytic bridges

`recordRiseTwo_sylvesterNext_eventually` is fully proved from its hypotheses.
Two of those hypotheses are analytic inputs that this module does **not**
derive:

* `hsupply` — the fresh odd large prime-power supply (r07 Lemmas 5-7, r08
  Lemma 4).  Its ordinary proof needs `log R n = o n`, `log (a n) = κ 2 ^ n`
  with `κ > 0`, the factorial separation `a j > (3 * R (j+1))!`, and the
  cumulative-lcm freshness budget of `CumulativeLcmTransfer`.  This is the same
  shape of input that the corpus row `bounded_lcm_negative_arithmetic_core`
  records as an open prime-supply bridge.
* `hvanish` — the normalised vanishing `∀ K, eventually K * |e n| < u n`, i.e.
  `E n / C n → 0` in primitive coordinates.  It is the same hypothesis carried
  by `boundedNegativePart_sylvesterNext_eventually` in `ReciprocalTailRigidity`.

`hcentre` (the nearest-integer normalisation `2 * |e n| < u n`) is a
consequence of `hvanish` at `K = 2` and is kept separate only to keep the
absorption step free of an index maximisation.

-- OPEN: the quantitative record-excess obligation (r07 Theorem 8).  Statement:
-- given the hypotheses of `numerator_bounded_of_oddPrimePower` minus `hrec`,
-- with `L = p ^ (l + 1) / 2` and `τ` the first index `≥ s` with `L ≤ u τ`,
--   `p ^ l / 6 - 2 ≤ ∑ n in recordSteps s τ, (u (n + 1) - u n - 2)`
-- where `recordSteps s τ = {n | s ≤ n < τ ∧ runningMax u n < u (n + 1)}`.
-- Not formalised here: it needs a counting argument over the odd multiples of
-- `p` in `(runningMax u s, L]` together with the per-jump capacity bound
-- `⌊(d - 1) / 2⌋` for a coprime pair at distance `d`, which is a separate
-- finite-combinatorics development.

-- CHECKED, NEGATIVE: the wave-1 suggestion that the open prime supply of
-- `no_boundedNegative_lcmState_of_oldPrimeSupply` (`LcmCriticalBoundary.lean`)
-- closes from `CumulativeLcmTransfer` by an index-shift wrapper alone does not
-- hold against the actual Lean statements.  That theorem needs
-- `Nat.Prime (m i)` and `B < m i` for every `i ≥ N`, with `m i ∣ D t` for all
-- `t > i`.  `CumulativeLcmTransfer` supplies the multiplier facts
-- `digit_dvd_cumulativeDigitLcm_of_lt` (old-divisor persistence) and
-- `lcmFresh_pairwiseCoprime` (pairwise coprimality *at fresh indices*), plus a
-- density-one freshness budget.  Two gaps survive an index shift: the
-- multipliers `a i` are not prime and nothing in the corpus extracts from them
-- a prime factor exceeding `B` (that extraction is exactly r07 Lemma 6-7, an
-- analytic growth input); and reindexing to a fresh subsequence breaks
-- `hmOld`, whose divisibility is keyed to the same index as the orbit step.
-- So no wrapper was added.
-/

end ErdosProblems.Erdos243
