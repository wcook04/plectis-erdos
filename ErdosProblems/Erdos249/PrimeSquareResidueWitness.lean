import ErdosProblems.Erdos249.ResidueClassTotientSeries

/-!
# Erdős #249: prime-square witness that unit centres miss a recurrent residue

Residue `2` modulo `12` is attained infinitely often by Euler's totient, but
never as `φ(a)(s-1)` with `gcd(s,12)=1`.  The smallest convenient witness is
`φ(121)=110`.  Prime centres `ap` are therefore strictly weaker than
prime-power centres `ap^ν`.

This file does **not** prove isolation of those prime-square centres, and it
does **not** prove the all-modulus rationality classification.  Isolation at
`ap^ν` remains an ordinary lemma.  The pulse-criterion consumer
`irrational_totientObservable_of_isolated_residue` is applied here only under
an isolation hypothesis.
-/

namespace ErdosProblems.Erdos249

/-- `φ(121) = 110`. -/
theorem totient_oneTwoOne : Nat.totient 121 = 110 := by
  have hp : Nat.Prime 11 := by decide
  rw [show (121 : ℕ) = 11 ^ 2 from by decide,
    Nat.totient_prime_pow hp (by decide : 0 < 2)]
  decide

/-- The explicit residue: `φ(121) ≡ 2 [MOD 12]`. -/
theorem totient_oneTwoOne_mod_twelve : Nat.totient 121 ≡ 2 [MOD 12] := by
  rw [totient_oneTwoOne]
  decide

lemma coprime_twelve_ne_zero {s : ℕ} (hs : Nat.Coprime s 12) : 0 < s :=
  Nat.pos_of_ne_zero fun h => by
    subst h
    have : Nat.Coprime 0 12 := hs
    simp [Nat.coprime_zero_left] at this

lemma coprime_twelve_odd {s : ℕ} (hs : Nat.Coprime s 12) : Odd s := by
  refine Nat.odd_iff.mpr ?_
  have hne : s % 2 ≠ 0 := by
    intro h0
    have h2s : 2 ∣ s := (Nat.dvd_iff_mod_eq_zero).2 h0
    have : 2 ∣ Nat.gcd s 12 := Nat.dvd_gcd h2s (by decide)
    have hg : Nat.gcd s 12 = 1 := hs
    omega
  omega

/-- A unit modulo `12` cannot realise residue `2` through a prime centre. -/
theorem no_unit_centre_two_mod_twelve (a s : ℕ) (hs : Nat.Coprime s 12) :
    ¬ Nat.totient a * (s - 1) ≡ 2 [MOD 12] := by
  intro hcon
  rcases lt_or_ge a 3 with ha | ha
  · have hspos : 1 ≤ s := Nat.succ_le_of_lt (coprime_twelve_ne_zero hs)
    have hphi1 : Nat.totient a = 0 ∨ Nat.totient a = 1 := by
      interval_cases a <;> simp [Nat.totient_zero, Nat.totient_one, Nat.totient_two]
    rcases hphi1 with h0 | h1
    · have : (0 : ℕ) ≡ 2 [MOD 12] := by simpa [h0] using hcon
      exact absurd this (by decide)
    · have hs1 : s - 1 ≡ 2 [MOD 12] := by simpa [h1] using hcon
      have hs3 : s ≡ 3 [MOD 12] := by
        have hadd : s - 1 + 1 ≡ 2 + 1 [MOD 12] := hs1.add_right 1
        simpa [Nat.sub_add_cancel hspos] using hadd
      have hmod : s % 12 = 3 := hs3
      have hk : s = 12 * (s / 12) + 3 := by
        have := Nat.div_add_mod s 12
        rw [hmod] at this
        exact this.symm
      have hg : Nat.gcd s 12 = 3 := by
        rw [hk, Nat.gcd_comm]
        simpa [Nat.add_comm, Nat.mul_comm] using
          (Nat.gcd_add_mul_right_right 12 3 (s / 12))
      have : Nat.gcd s 12 = 1 := hs
      omega
  · have h2φ : 2 ∣ Nat.totient a := by
      have heφ : Even (Nat.totient a) :=
        Nat.totient_even (Nat.lt_of_lt_of_le (by decide : 2 < 3) ha)
      exact (Nat.dvd_iff_mod_eq_zero).2 (Nat.even_iff.mp heφ)
    have h2s : 2 ∣ s - 1 := by
      have hodd : s % 2 = 1 := Nat.odd_iff.mp (coprime_twelve_odd hs)
      have hspos : 0 < s := coprime_twelve_ne_zero hs
      have hmod : (s - 1) % 2 = 0 := by omega
      exact (Nat.dvd_iff_mod_eq_zero).2 hmod
    obtain ⟨k, hk⟩ := h2φ
    obtain ⟨m, hm⟩ := h2s
    have hdiv : 4 ∣ Nat.totient a * (s - 1) :=
      ⟨k * m, by
        calc
          Nat.totient a * (s - 1) = (2 * k) * (2 * m) := by rw [hk, hm]
          _ = 4 * (k * m) := by ring⟩
    have hmod4 : Nat.totient a * (s - 1) ≡ 2 [MOD 4] :=
      hcon.of_dvd (by decide : 4 ∣ 12)
    have h0 : Nat.totient a * (s - 1) ≡ 0 [MOD 4] :=
      Nat.modEq_zero_iff_dvd.mpr hdiv
    have : (2 : ℕ) ≡ 0 [MOD 4] := hmod4.symm.trans h0
    exact absurd this (by decide)

/-- For every prime `p ≡ 11 [MOD 12]`, the square realises residue `2`. -/
theorem totient_prime_sq_eleven_mod_twelve {p : ℕ}
    (hp : Nat.Prime p) (hcong : p ≡ 11 [MOD 12]) :
    Nat.totient (p ^ 2) ≡ 2 [MOD 12] := by
  have hp1 : 1 ≤ p := hp.one_le
  rw [Nat.totient_prime_pow hp (by decide : 0 < 2)]
  have hpow : p ^ (2 - 1) = p := by simp
  rw [hpow]
  have hpm1 : p - 1 ≡ 10 [MOD 12] := by
    apply Nat.ModEq.add_right_cancel' 1
    simpa [Nat.sub_add_cancel hp1] using hcong
  have hmul : p * (p - 1) ≡ 11 * 10 [MOD 12] := Nat.ModEq.mul hcong hpm1
  exact hmul.trans (by decide)

/-- Dirichlet: infinitely many primes `≡ 11 [MOD 12]`. -/
theorem exists_prime_gt_eleven_mod_twelve (N : ℕ) :
    ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ p ≡ 11 [MOD 12] :=
  Nat.forall_exists_prime_gt_and_modEq N (q := 12) (a := 11)
    (by decide : (12 : ℕ) ≠ 0) (by decide : Nat.Coprime 11 12)

/-- Residue `2` modulo `12` is recurrent, via prime squares rather than primes. -/
theorem two_mod_twelve_recurrent_via_prime_squares (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Nat.totient n ≡ 2 [MOD 12] ∧
      ∃ p : ℕ, Nat.Prime p ∧ n = p ^ 2 := by
  obtain ⟨p, hpN, hpp, hcong⟩ := exists_prime_gt_eleven_mod_twelve (max N 1)
  refine ⟨p ^ 2, ?_, totient_prime_sq_eleven_mod_twelve hpp hcong, ⟨p, hpp, rfl⟩⟩
  have hp2 : 2 ≤ p := hpp.two_le
  have hpgt : 1 < p := Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hp2
  have hN : N < p := lt_of_le_of_lt (le_max_left N 1) hpN
  have : p < p ^ 2 := by
    have hppos : 0 < p := Nat.zero_lt_of_lt hpgt
    calc
      p = p * 1 := (Nat.mul_one p).symm
      _ < p * p := Nat.mul_lt_mul_of_pos_left hpgt hppos
      _ = p ^ 2 := (pow_two p).symm
  exact hN.trans this

/-- Pulse-criterion consumer at residue `2` modulo `12`, under isolation.

The isolation hypothesis is the ordinary prime-power-centre lemma specialised
to `a=1`, `ν=2`, `s≡11 [MOD 12]`.  It is not discharged in Lean. -/
theorem irrational_twoModTwelveIndicator_of_isolation
    (hiso : ∀ L : ℕ, ∃ n : ℕ, L + 1 < n ∧ Nat.totient n ≡ 2 [MOD 12] ∧
      ∀ j, 0 < j → j ≤ L → 12 ∣ Nat.totient (n - j) ∧ 12 ∣ Nat.totient (n + j)) :
    Irrational (totientObservableValue (fun r => if r = 2 then (1 : ℤ) else 0) 12) := by
  refine irrational_totientObservable_of_isolated_residue
    (by decide : (0 : ℕ) < 12)
    (fun r => if r = 2 then (1 : ℤ) else 0)
    (by decide)
    (by decide : (2 : ℕ) < 12)
    (by decide : ((1 : ℤ) ≠ 0))
    fun L => ?_
  obtain ⟨n, hn, hres, hnb⟩ := hiso L
  exact ⟨n, hn, hres, hnb⟩

end ErdosProblems.Erdos249
