import ErdosProblems.Erdos251.KernelDenominatorFloor

/-!
# Primality by one gcd below `1013 ^ 2`

The large certificate for Erdős Problem #251 scans every integer below
`1023068` and decides which of them are prime (`PaperStreamingCertificateV5`).
With trial division that scan needs hours of kernel time. This module gives a
primality test that the kernel evaluates with one gcd per integer on the
scanned range, and proves that it agrees with trial division everywhere.

The criterion is `prime_iff_gcd`: for `1012 ≤ m < 1013 ^ 2`, the integer `m`
is prime exactly when `gcd m P = 1`, where `P` is the product of the primes
below `1012`. Every prime factor of `P` is below `1012`, so a prime `m ≥ 1012`
does not divide `P` and is coprime to it. A composite `m` in the range has a
prime factor `q` with `q ^ 2 ≤ m < 1013 ^ 2`. Then `q ≤ 1012`, and `q < 1012`
because `1012` is not prime, so `q` divides both `m` and `P`.

`P` is written as the literal `P1011`. The kernel recomputes the product from
the trial-division test `isPrimeTD` and checks that it equals the literal
(`primeProd_1012`), so no supplied list of primes is trusted. The test
`isPrimeG` uses the gcd on `[1012, 1013 ^ 2)` and trial division elsewhere,
and `isPrimeG_eq` proves `isPrimeG m = isPrimeTD m` for every natural number
`m`. Replacing one test by the other in the certificate changes the cost of
the check and leaves every statement unchanged.
-/

namespace ErdosProblems.Erdos251.PaperV5.Fast

open ErdosProblems.Erdos251

/-- The product of the primes below `n`, with primality decided by trial
division. -/
def primeProd : ℕ → ℕ
  | 0 => 1
  | n + 1 => if isPrimeTD n then n * primeProd n else primeProd n

/-- Every prime below `n` divides `primeProd n`. -/
theorem dvd_primeProd {p : ℕ} (hp : p.Prime) : ∀ {n : ℕ}, p < n → p ∣ primeProd n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
      · have ih := dvd_primeProd hp h'
        rw [primeProd]
        split
        · exact Dvd.dvd.mul_left ih n
        · exact ih
      · rw [primeProd, if_pos ((isPrimeTD_eq_true_iff p).2 hp)]
        exact Dvd.intro _ rfl

/-- Every prime factor of `primeProd n` is below `n`. -/
theorem lt_of_prime_dvd_primeProd {q : ℕ} (hq : q.Prime) :
    ∀ {n : ℕ}, q ∣ primeProd n → q < n
  | 0, h => by
      rw [primeProd] at h
      exact absurd (Nat.dvd_one.mp h) hq.one_lt.ne'
  | n + 1, h => by
      rw [primeProd] at h
      split at h
      · rename_i hb
        rcases (Nat.Prime.dvd_mul hq).1 h with h1 | h1
        · have hn : n.Prime := (isPrimeTD_eq_true_iff n).1 hb
          have : q = n := (Nat.prime_dvd_prime_iff_eq hq hn).1 h1
          omega
        · have := lt_of_prime_dvd_primeProd hq h1
          omega
      · have := lt_of_prime_dvd_primeProd hq h
        omega

/-- For `1012 ≤ m < 1013 ^ 2`, the integer `m` is prime exactly when it is
coprime to the product of the primes below `1012`. -/
theorem prime_iff_gcd {m : ℕ} (h1 : 1012 ≤ m) (h2 : m < 1013 * 1013) :
    Nat.Prime m ↔ Nat.gcd m (primeProd 1012) = 1 := by
  constructor
  · intro hm
    have hnd : ¬ m ∣ primeProd 1012 := fun hd =>
      absurd (lt_of_prime_dvd_primeProd hm hd) (by omega)
    exact (Nat.Prime.coprime_iff_not_dvd hm).2 hnd
  · intro hg
    by_contra hnp
    have hm1 : m ≠ 1 := by omega
    have hp : (Nat.minFac m).Prime := Nat.minFac_prime hm1
    have hsq : (Nat.minFac m) ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
    have h13 : Nat.minFac m < 1013 := by
      by_contra hge
      have hge' : 1013 ≤ Nat.minFac m := by omega
      have : 1013 * 1013 ≤ (Nat.minFac m) ^ 2 := by
        rw [pow_two]; exact Nat.mul_le_mul hge' hge'
      omega
    have hne : Nat.minFac m ≠ 1012 := by
      intro he
      rw [he] at hp
      norm_num at hp
    have hlt : Nat.minFac m < 1012 := by omega
    have hd : Nat.minFac m ∣ Nat.gcd m (primeProd 1012) :=
      Nat.dvd_gcd (Nat.minFac_dvd m) (dvd_primeProd hp hlt)
    rw [hg] at hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hd)

/-- The product of the 169 primes below `1012`, a literal of 1390 bits. -/
def P1011 : ℕ :=
  19766653710804075182143870771990238475539088142104672537897548776929384313227289497808619213628587662490595625147474943321532235492742204128846913537770322864572995974935654100594289056885746177674106727111011492167293600757722582873710083333409221248630824126186603003458015947013676475012954103807759699698139884769988141115940629691053820740641161140263635520790129447288872867072881843138566340347306438762146043190

/-- The kernel recomputes the product by trial division and checks the
literal. -/
theorem primeProd_1012 : primeProd 1012 = P1011 := by
  decide +kernel

/-- Primality with one gcd on `[1012, 1013 ^ 2)` and trial division
elsewhere. -/
def isPrimeG (m : ℕ) : Bool :=
  bif Nat.blt m 1012 then isPrimeTD m
  else bif Nat.blt m 1026169 then Nat.beq (Nat.gcd m P1011) 1
  else isPrimeTD m

private theorem blt_true {m n : ℕ} (h : m < n) : Nat.blt m n = true := by
  simpa [Nat.blt_eq] using h

private theorem blt_false {m n : ℕ} (h : ¬ m < n) : Nat.blt m n = false := by
  cases h' : Nat.blt m n
  · rfl
  · simp only [Nat.blt_eq] at h'
    exact absurd h' h

/-- `isPrimeG` and the trial-division test `isPrimeTD` agree at every natural
number. -/
theorem isPrimeG_eq (m : ℕ) : isPrimeG m = isPrimeTD m := by
  unfold isPrimeG
  by_cases hm : m < 1012
  · rw [blt_true hm, cond_true]
  · rw [blt_false hm, cond_false]
    by_cases hm2 : m < 1026169
    · rw [blt_true hm2, cond_true, Bool.eq_iff_iff, isPrimeTD_eq_true_iff,
        prime_iff_gcd (by omega) (by omega), primeProd_1012]
      constructor
      · exact Nat.eq_of_beq_eq_true
      · intro he
        rw [he]
        rfl
    · rw [blt_false hm2, cond_false]

/-- `isPrimeG` decides primality. -/
theorem isPrimeG_eq_true_iff (m : ℕ) : isPrimeG m = true ↔ Nat.Prime m := by
  rw [isPrimeG_eq]
  exact isPrimeTD_eq_true_iff m

end ErdosProblems.Erdos251.PaperV5.Fast
