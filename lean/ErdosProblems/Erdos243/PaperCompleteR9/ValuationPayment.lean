import ErdosProblems.Erdos243.CumulativeLcmTransfer

/-!
Prime-power payment at a first contact is stated using power divisibility, so
no convention for the valuation of zero is involved.
The coefficient is exactly one; the statement is not silently generalised
to arbitrary coefficients.
-/
namespace ErdosProblems.Erdos243.PaperCompleteR9

/-- At a contact, both coprime reduced cofactors are p-units. -/
theorem reduced_contact_units (p A B u v : ℕ) (hp : Nat.Prime p)
    (hAB : Nat.Coprime A B) (hu : ¬ p ∣ u) (hv : p ∣ v)
    (hstep : v + B = A * u) : ¬ p ∣ A ∧ ¬ p ∣ B := by
  have hno : ¬ (p ∣ A ∧ p ∣ B) := by
    rintro ⟨hA, hB⟩
    have hd : p ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
    rw [hAB.gcd_eq_one] at hd
    have hh := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hd
    have hp2 := hp.two_le
    omega
  have hA : ¬ p ∣ A := by
    intro hh
    have hd : p ∣ v + B := by rw [hstep]; exact dvd_mul_of_dvd_left hh u
    exact hno ⟨hh, (Nat.dvd_add_iff_right hv).mpr hd⟩
  refine ⟨hA, ?_⟩
  intro hB
  have hd : p ∣ A * u := by rw [← hstep]; exact dvd_add hv hB
  rcases hp.dvd_mul.mp hd with h | h
  · exact hA h
  · exact hu h

/-- Elementary construction of the coprime cofactors, not an added supplier. -/
theorem gcd_cofactors_coprime (a L : ℕ) (hL : 0 < L) :
    Nat.Coprime (a / Nat.gcd L a) (L / Nat.gcd L a) := by
  let g := Nat.gcd L a
  let A := a / g
  let B := L / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left a hL
  have hA : g * A = a := Nat.mul_div_cancel' (Nat.gcd_dvd_right L a)
  have hB : g * B = L := Nat.mul_div_cancel' (Nat.gcd_dvd_left L a)
  let d := Nat.gcd A B
  have hda : g * d ∣ a := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left A B
    refine ⟨k, ?_⟩
    calc a = g * A := hA.symm
      _ = g * (d * k) := congrArg (fun x => g * x) hk
      _ = (g * d) * k := by ring
  have hdL : g * d ∣ L := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_right A B
    refine ⟨k, ?_⟩
    calc L = g * B := hB.symm
      _ = g * (d * k) := congrArg (fun x => g * x) hk
      _ = (g * d) * k := by ring
  have hdg : g * d ∣ g := Nat.dvd_gcd hdL hda
  obtain ⟨k, hk⟩ := hdg
  have hcancel : 1 = d * k := by
    apply Nat.eq_of_mul_eq_mul_left hg
    nlinarith [hk]
  have hd1 : d ∣ 1 := ⟨k, hcancel⟩
  change d = 1
  exact Nat.dvd_one.mp hd1

/-- All p-powers in either multiplier or old denominator are in the overlap:
this is the exact equality of their finite p-adic valuations. -/
theorem contact_full_overlap (p a L u v : ℕ) (hp : Nat.Prime p)
    (hL : 0 < L) (hu : ¬ p ∣ u) (hv : p ∣ v)
    (hstep : Nat.gcd L a * v + L = a * u) :
    (¬ p ∣ a / Nat.gcd L a) ∧ (¬ p ∣ L / Nat.gcd L a) ∧
    ∀ e : ℕ,
      (p ^ e ∣ a ↔ p ^ e ∣ Nat.gcd L a) ∧
      (p ^ e ∣ L ↔ p ^ e ∣ Nat.gcd L a) := by
  let g := Nat.gcd L a
  let A := a / g
  let B := L / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left a hL
  have hA : g * A = a := Nat.mul_div_cancel' (Nat.gcd_dvd_right L a)
  have hB : g * B = L := Nat.mul_div_cancel' (Nat.gcd_dvd_left L a)
  have hred : v + B = A * u := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc g * (v + B) = g * v + L := by rw [← hB]; ring
      _ = a * u := hstep
      _ = g * (A * u) := by rw [← hA]; ring
  obtain ⟨hpA, hpB⟩ := reduced_contact_units p A B u v hp
    (gcd_cofactors_coprime a L hL) hu hv hred
  refine ⟨hpA, hpB, fun e ↦ ?_⟩
  have hcA : Nat.Coprime (p ^ e) A := (hp.coprime_iff_not_dvd.mpr hpA).pow_left e
  have hcB : Nat.Coprime (p ^ e) B := (hp.coprime_iff_not_dvd.mpr hpB).pow_left e
  constructor
  · constructor
    · intro hd
      rw [← hA] at hd
      exact hcA.dvd_of_dvd_mul_left (by simpa [mul_comm, g] using hd)
    · intro hd
      exact hd.trans (Nat.gcd_dvd_right L a)
  · constructor
    · intro hd
      rw [← hB] at hd
      exact hcB.dvd_of_dvd_mul_left (by simpa [mul_comm, g] using hd)
    · intro hd
      exact hd.trans (Nat.gcd_dvd_left L a)

/-- An old prime power is paid in full at any transition from a p-unit to a
p-divisible numerator. Minimality of the first contact supplies the unit. -/
theorem old_digit_full_payment (q : ℕ) (a U : ℕ → ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n)
    (hstep : ∀ n, lcmOverlap q a n * U (n + 1) + cumulativeDigitLcm q a n = a n * U n)
    (p e i n : ℕ) (hp : Nat.Prime p) (hin : i < n) (hsource : p ^ e ∣ a i)
    (hu : ¬ p ∣ U n) (hv : p ∣ U (n + 1)) : p ^ e ∣ lcmOverlap q a n := by
  have hOld : p ^ e ∣ cumulativeDigitLcm q a n :=
    hsource.trans (digit_dvd_cumulativeDigitLcm_of_lt q a hin)
  have hcontact := contact_full_overlap p (a n) (cumulativeDigitLcm q a n)
    (U n) (U (n + 1)) hp (cumulativeDigitLcm_pos hq ha n) hu hv (hstep n)
  exact ((hcontact.2.2 e).2).mp hOld

/-- Full payment enters the cumulative cancellation debt at this same step. -/
theorem old_digit_cumulative_payment (q : ℕ) (a U : ℕ → ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n)
    (hstep : ∀ n, lcmOverlap q a n * U (n + 1) + cumulativeDigitLcm q a n = a n * U n)
    (p e i n : ℕ) (hp : Nat.Prime p) (hin : i < n) (hsource : p ^ e ∣ a i)
    (hu : ¬ p ∣ U n) (hv : p ∣ U (n + 1)) :
    p ^ e ∣ cumulativeOverlapDebt q a (n + 1) := by
  have hpρ := old_digit_full_payment q a U hq ha hstep p e i n hp hin hsource hu hv
  rw [cumulativeOverlapDebt_succ' q a n]
  exact dvd_mul_of_dvd_right hpρ _

end ErdosProblems.Erdos243.PaperCompleteR9
