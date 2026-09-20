import Mathlib

/-!
# Erdős 243: two local finite-arithmetic statements about one reduced step

Paper-form restatements of two environments of the long note
`paper/reasoning-parts/erdos243/core.tex`:

* `long243:res:oldmodulussaturation` (saturation modulo an old denominator):
  every finite word of units modulo `M` is realised by the cancellation-free
  recurrences modulo `M` with all reduced denominator residues zero.  The
  multipliers are free, so the eliminated two-step identity is satisfied as
  well; that is the mathematical content of the lemma's second sentence.
* `long243:res:valuationtransition` (the denominator valuation transition):
  the exact `p`-adic valuation of the reduced denominator after one step,
  together with the two "in particular" clauses.

The reduced step is the paper's: `u, v, a` positive with `gcd (u, v) = 1`,
`w = a * u - v > 0`, `h = gcd (w, a * v)` and `v' = a * v / h`.  Natural
subtraction is avoided by writing `w + v = a * u` with `0 < w`.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

/-! ## 1. Saturation modulo an old denominator

The paper's recurrences, read modulo `M` with no cancellation, are
`r (i+1) + v i = a i * r i` and `v (i+1) = a i * v i`; eliminating `v` gives
`r (i+2) = (a i + a (i+1)) * r (i+1) - (a i)^2 * r i`.  The lemma asserts that
a word `r 0, …, r k` of units is compatible with all of these, with every
reduced denominator residue equal to zero. -/

/-- **Saturation modulo an old denominator (`long243:res:oldmodulussaturation`).**
Let `M ≥ 2` and let `r 0, …, r k` be any word of units modulo `M`.  Then there
are multiplier residues `a` and denominator residues `v` modulo `M`, with every
`v i` equal to zero, satisfying the cancellation-free recurrences on the word;
the eliminated two-step identity then holds automatically, so it alone imposes
no restriction on the unit word. -/
theorem unit_word_saturates_old_modulus
    (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (r : ℕ → ZMod M)
    (hr : ∀ i, i ≤ k → IsUnit (r i)) :
    ∃ a v : ℕ → ZMod M,
      (∀ i, i ≤ k → v i = 0) ∧
      (∀ i, i < k → r (i + 1) + v i = a i * r i) ∧
      (∀ i, i < k → v (i + 1) = a i * v i) ∧
      (∀ i, i + 2 ≤ k →
        r (i + 2) = (a i + a (i + 1)) * r (i + 1) - a i ^ 2 * r i) := by
  classical
  refine ⟨fun i => r (i + 1) * Ring.inverse (r i), fun _ => 0,
      fun _ _ => rfl, ?_, ?_, ?_⟩
  · -- the numerator recurrence: the chosen multiplier moves `r i` onto `r (i+1)`
    intro i hi
    have hu : IsUnit (r i) := hr i (by omega)
    have hstep : r (i + 1) * Ring.inverse (r i) * r i = r (i + 1) := by
      rw [mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]
    rw [hstep, add_zero]
  · intro i _
    simp
  · -- the eliminated two-step identity
    intro i hi
    have hu0 : IsUnit (r i) := hr i (by omega)
    have hu1 : IsUnit (r (i + 1)) := hr (i + 1) (by omega)
    have h0 : r (i + 1) * Ring.inverse (r i) * r i = r (i + 1) := by
      rw [mul_assoc, Ring.inverse_mul_cancel _ hu0, mul_one]
    have h1 : r (i + 1 + 1) * Ring.inverse (r (i + 1)) * r (i + 1) = r (i + 1 + 1) := by
      rw [mul_assoc, Ring.inverse_mul_cancel _ hu1, mul_one]
    have hidx : i + 1 + 1 = i + 2 := by omega
    rw [hidx] at h1
    set A0 := r (i + 1) * Ring.inverse (r i) with hA0
    set A1 := r (i + 2) * Ring.inverse (r (i + 1)) with hA1
    linear_combination -h1 + A0 * h0

/-! ## 2. The denominator valuation transition -/

/-- If `x + y = z` and `y` and `z` have different `p`-adic valuations, then the
valuation of `x` is the smaller of the two. -/
private theorem valuation_of_summand {p x y z : ℕ} (hp : p.Prime)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hsum : x + y = z)
    (hne : y.factorization p ≠ z.factorization p) :
    x.factorization p = min (y.factorization p) (z.factorization p) := by
  set s := y.factorization p with hs
  set t := z.factorization p with ht
  have hxz : x = z - y := by omega
  have hyz : y = z - x := by omega
  have hzxy : z = x + y := hsum.symm
  have hdy : p ^ min s t ∣ y :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hy).mpr (min_le_left _ _)
  have hdz : p ^ min s t ∣ z :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hz).mpr (min_le_right _ _)
  have hdx : p ^ min s t ∣ x := by
    rw [hxz]; exact Nat.dvd_sub hdz hdy
  have hlow : min s t ≤ x.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hx).mp hdx
  by_contra hcon
  have hgt : min s t < x.factorization p := by omega
  have hdx' : p ^ (min s t + 1) ∣ x :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hx).mpr (by omega)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `s < t`: then `p ^ (s+1)` divides `z` and `x`, hence `y`
    have hdz' : p ^ (min s t + 1) ∣ z :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hz).mpr (by omega)
    have hdy' : p ^ (min s t + 1) ∣ y := by
      rw [hyz]; exact Nat.dvd_sub hdz' hdx'
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp hy).mp hdy'
    omega
  · -- `t < s`: then `p ^ (t+1)` divides `y` and `x`, hence `z`
    have hdy' : p ^ (min s t + 1) ∣ y :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hy).mpr (by omega)
    have hdz' : p ^ (min s t + 1) ∣ z := by
      rw [hzxy]; exact Nat.dvd_add hdx' hdy'
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp hz).mp hdz'
    omega

/-- The three facts about one reduced step from which the paper's valuation
formula and both of its "in particular" clauses follow. -/
private theorem valuation_transition_core
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h) :
    v'.factorization p
        + min (w.factorization p) (a.factorization p + v.factorization p)
      = a.factorization p + v.factorization p
    ∧ (a.factorization p ≠ v.factorization p →
        w.factorization p = min (a.factorization p) (v.factorization p))
    ∧ (a.factorization p = v.factorization p →
        v.factorization p ≤ w.factorization p) := by
  have hw0 : w ≠ 0 := by omega
  have hv0 : v ≠ 0 := by omega
  have ha0 : a ≠ 0 := by omega
  have hu0 : u ≠ 0 := by omega
  have hav0 : a * v ≠ 0 := Nat.mul_ne_zero ha0 hv0
  have hau0 : a * u ≠ 0 := Nat.mul_ne_zero ha0 hu0
  have hh0 : h ≠ 0 := by
    rw [hh]
    exact Nat.gcd_ne_zero_left hw0
  have hdvd : h ∣ a * v := by rw [hh]; exact Nat.gcd_dvd_right _ _
  have hdvdw : h ∣ w := by rw [hh]; exact Nat.gcd_dvd_left _ _
  have hmul : h * v' = a * v := by rw [hv'def]; exact Nat.mul_div_cancel' hdvd
  have hv'0 : v' ≠ 0 := by
    intro hzero
    rw [hzero, Nat.mul_zero] at hmul
    exact hav0 hmul.symm
  -- valuation of the product `a * v`
  have hav : (a * v).factorization p = a.factorization p + v.factorization p := by
    rw [Nat.factorization_mul ha0 hv0, Finsupp.add_apply]
  -- valuation of the cancellation factor
  have hgcdle : h.factorization p ≤ min (w.factorization p) ((a * v).factorization p) := by
    have hd : p ^ (h.factorization p) ∣ h := Nat.ordProj_dvd h p
    exact le_min
      ((Nat.Prime.pow_dvd_iff_le_factorization hp hw0).mp (hd.trans hdvdw))
      ((Nat.Prime.pow_dvd_iff_le_factorization hp hav0).mp (hd.trans hdvd))
  have hgcdge : min (w.factorization p) ((a * v).factorization p) ≤ h.factorization p := by
    have h1 : p ^ (min (w.factorization p) ((a * v).factorization p)) ∣ w :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hw0).mpr (min_le_left _ _)
    have h2 : p ^ (min (w.factorization p) ((a * v).factorization p)) ∣ a * v :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hav0).mpr (min_le_right _ _)
    have h3 : p ^ (min (w.factorization p) ((a * v).factorization p)) ∣ h := by
      rw [hh]; exact Nat.dvd_gcd h1 h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hh0).mp h3
  have hgcd : h.factorization p
      = min (w.factorization p) (a.factorization p + v.factorization p) := by
    rw [← hav]; omega
  -- the product relation `h * v' = a * v`
  have hsum : h.factorization p + v'.factorization p
      = a.factorization p + v.factorization p := by
    have h1 : (h * v').factorization p = (a * v).factorization p := by rw [hmul]
    rw [Nat.factorization_mul hh0 hv'0, Finsupp.add_apply, hav] at h1
    exact h1
  refine ⟨by omega, ?_, ?_⟩
  · -- the case `ν_p a ≠ ν_p v`
    intro hne
    by_cases hs : v.factorization p = 0
    · -- `s = 0 < r`: `p` divides `a` but not `v`, hence not `w`
      have hr1 : 1 ≤ a.factorization p := by omega
      have hpa : p ∣ a := by
        have := (Nat.Prime.pow_dvd_iff_le_factorization hp ha0).mpr hr1
        simpa using this
      have hnpv : ¬ p ∣ v := by
        intro hpv
        have : 1 ≤ v.factorization p :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp hv0).mp (by simpa using hpv)
        omega
      have hnpw : ¬ p ∣ w := by
        intro hpw
        have hpau : p ∣ a * u := Dvd.dvd.mul_right hpa u
        have : p ∣ v := by
          have hvw : v = a * u - w := by omega
          rw [hvw]; exact Nat.dvd_sub hpau hpw
        exact hnpv this
      have : w.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnpw
      omega
    · -- `s ≥ 1`: `p` cannot divide `u`, so `ν_p (a * u) = ν_p a`
      have hpv : p ∣ v := by
        have : 1 ≤ v.factorization p := by omega
        simpa using (Nat.Prime.pow_dvd_iff_le_factorization hp hv0).mpr this
      have hnpu : ¬ p ∣ u := by
        intro hpu
        have hg : p ∣ Nat.gcd u v := Nat.dvd_gcd hpu hpv
        rw [hcop.gcd_eq_one] at hg
        have := Nat.le_of_dvd Nat.one_pos hg
        have := hp.two_le
        omega
      have hufac : u.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnpu
      have haufac : (a * u).factorization p = a.factorization p := by
        rw [Nat.factorization_mul ha0 hu0, Finsupp.add_apply, hufac, Nat.add_zero]
      have := valuation_of_summand (p := p) hp hw0 hv0 hau0 hw
        (by rw [haufac]; exact fun hcon => hne hcon.symm)
      rw [haufac] at this
      rw [this, min_comm]
  · -- the case `ν_p a = ν_p v`
    intro heq
    by_cases hs : v.factorization p = 0
    · omega
    · have hpv : p ∣ v := by
        have : 1 ≤ v.factorization p := by omega
        simpa using (Nat.Prime.pow_dvd_iff_le_factorization hp hv0).mpr this
      have hnpu : ¬ p ∣ u := by
        intro hpu
        have hg : p ∣ Nat.gcd u v := Nat.dvd_gcd hpu hpv
        rw [hcop.gcd_eq_one] at hg
        have := Nat.le_of_dvd Nat.one_pos hg
        have := hp.two_le
        omega
      have hufac : u.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnpu
      have haufac : (a * u).factorization p = a.factorization p := by
        rw [Nat.factorization_mul ha0 hu0, Finsupp.add_apply, hufac, Nat.add_zero]
      -- both terms of `w = a * u - v` are divisible by `p ^ s`
      have h1 : p ^ (v.factorization p) ∣ a * u :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hau0).mpr (by omega)
      have h2 : p ^ (v.factorization p) ∣ v :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hv0).mpr le_rfl
      have h3 : p ^ (v.factorization p) ∣ w := by
        have hwv : w = a * u - v := by omega
        rw [hwv]; exact Nat.dvd_sub h1 h2
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp hw0).mp h3

/-- **The denominator valuation transition (`long243:res:valuationtransition`).**
With `r = ν_p a`, `s = ν_p v` and `t = ν_p w`, the reduced denominator
`v' = a * v / gcd (w, a * v)` has `ν_p v' = max (r, s)` when `r ≠ s` and
`ν_p v' = max (0, 2 * s - t)` when `r = s`. -/
theorem reduced_denominator_valuation_transition
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h) :
    (a.factorization p ≠ v.factorization p →
        v'.factorization p = max (a.factorization p) (v.factorization p))
    ∧ (a.factorization p = v.factorization p →
        v'.factorization p
          = max 0 (2 * v.factorization p - w.factorization p)) := by
  obtain ⟨hmain, hne, heq⟩ :=
    valuation_transition_core (p := p) hp hu hv ha hcop hw hwpos hh hv'def
  exact ⟨fun hh1 => by have := hne hh1; omega, fun hh2 => by have := heq hh2; omega⟩

/-- **In particular (`long243:res:valuationtransition`).**  The reduced
denominator valuation never exceeds `max (ν_p a, ν_p v)`. -/
theorem reduced_denominator_valuation_le_max
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h) :
    v'.factorization p ≤ max (a.factorization p) (v.factorization p) := by
  obtain ⟨hmain, hne, heq⟩ :=
    valuation_transition_core (p := p) hp hu hv ha hcop hw hwpos hh hv'def
  by_cases hc : a.factorization p = v.factorization p
  · have := heq hc; omega
  · have := hne hc; omega

/-- **In particular (`long243:res:valuationtransition`).**  A strict loss of
denominator valuation relative to `s = ν_p v` requires `ν_p a = ν_p v ≥ 1` and
`ν_p w > ν_p v`. -/
theorem reduced_denominator_valuation_strict_loss
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h)
    (hloss : v'.factorization p < v.factorization p) :
    a.factorization p = v.factorization p ∧ 1 ≤ v.factorization p ∧
      v.factorization p < w.factorization p := by
  obtain ⟨hmain, hne, heq⟩ :=
    valuation_transition_core (p := p) hp hu hv ha hcop hw hwpos hh hv'def
  by_cases hc : a.factorization p = v.factorization p
  · have := heq hc; omega
  · have := hne hc; omega

/-- The paper's worked instance: `(u, v, a) = (2, 15, 9)` gives `w = 3`,
`h = 3` and `(u', v') = (1, 45)`, so the numerator before reduction exceeds
`u` by only `w - u = 1` while the `3`-adic valuation of the reduced
denominator rises from `1` to `2`. -/
theorem valuation_transition_worked_instance :
    (9 : ℕ) * 2 - 15 = 3 ∧ Nat.gcd 3 (9 * 15) = 3 ∧
      (9 * 2 - 15) / Nat.gcd 3 (9 * 15) = 1 ∧
      9 * 15 / Nat.gcd 3 (9 * 15) = 45 ∧
      (9 * 2 - 15) - 2 = 1 ∧
      (15 : ℕ).factorization 3 = 1 ∧ (45 : ℕ).factorization 3 = 2 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have key : ∀ n k : ℕ, n ≠ 0 → 3 ^ k ∣ n → ¬ (3 ^ (k + 1) ∣ n) →
      n.factorization 3 = k := by
    intro n k hn h1 h2
    have hge := (Nat.Prime.pow_dvd_iff_le_factorization hp3 hn).mp h1
    have hlt : ¬ (k + 1 ≤ n.factorization 3) := fun hc =>
      h2 ((Nat.Prime.pow_dvd_iff_le_factorization hp3 hn).mpr hc)
    omega
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · exact key 15 1 (by norm_num) (by decide) (by decide)
  · exact key 45 2 (by norm_num) (by decide) (by decide)

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.unit_word_saturates_old_modulus
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_transition
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_le_max
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_strict_loss
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.valuation_transition_worked_instance

end ErdosProblems.Erdos243.PaperCompleteR21
