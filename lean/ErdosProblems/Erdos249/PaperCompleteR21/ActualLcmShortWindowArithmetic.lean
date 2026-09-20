import Erdos249257.TotientActualLcmOrbitArithmetic

/-! Paper-form restatements of the "further exact identities" block of the long
#249 manuscript: the exact totient difference on an LCM progression
(`prop:AR-04-inv`), the rough-integer totient bound (`prop:AR-03-inv`),
positivity of the short-window differences (`prop:AR-05-inv`), and the
identification of the accumulated weighted sum with the window discrepancy
(`prop:AR-06-inv`).  Every statement is about the literal totient differences
`δ_t(j) = φ(2H(t)+j) - φ(H(t)+j)`, with `H(t) = lcm(1,…,t)`. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine

/-! ### Helpers -/

/-- The integral overlap factor, written with an exact rational division:
`totientOverlapFactor j x = gcd(j,x)·φ(j)/φ(gcd(j,x))`. -/
private lemma gcd_pos_of_left_pos {j : ℕ} (x : ℕ) (hj : 0 < j) :
    0 < Nat.gcd j x := by
  rcases Nat.eq_zero_or_pos (Nat.gcd j x) with h | h
  · rw [Nat.gcd_eq_zero_iff] at h
    omega
  · exact h

private lemma cast_totientOverlapFactor {j : ℕ} (x : ℕ) (hj : 0 < j) :
    ((totientOverlapFactor j x : ℕ) : ℚ)
      = (Nat.gcd j x : ℚ) * (Nat.totient j : ℚ)
          / (Nat.totient (Nat.gcd j x) : ℚ) := by
  have hg : 0 < Nat.gcd j x := gcd_pos_of_left_pos x hj
  have hdvd : Nat.totient (Nat.gcd j x) ∣ Nat.totient j :=
    Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left j x)
  have hne : ((Nat.totient (Nat.gcd j x) : ℚ)) ≠ 0 := by
    have hp : 0 < Nat.totient (Nat.gcd j x) := Nat.totient_pos.mpr hg
    exact_mod_cast hp.ne'
  unfold totientOverlapFactor
  rw [Nat.cast_mul, Nat.cast_div hdvd hne]
  ring

/-- If every prime divisor of `j` divides `x`, then `j` is coprime to `x+1`. -/
private lemma gcd_succ_eq_one_of_forall_prime_dvd {j x : ℕ}
    (hx : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ x) :
    Nat.gcd j (x + 1) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpj : p ∣ j := hpd.trans (Nat.gcd_dvd_left _ _)
  have hp1 : p ∣ x + 1 := hpd.trans (Nat.gcd_dvd_right _ _)
  have hpx : p ∣ x := hx p hp hpj
  have hone : p ∣ 1 := (Nat.dvd_add_right hpx).mp hp1
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

/-- The arithmetic LCM-ray letter is the literal totient difference
`δ_t(j) = φ(2H+j) - φ(H+j)`. -/
theorem lcmRayArithmeticLetter_eq_totient_difference (t j : ℕ) :
    lcmRayArithmeticLetter t j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ) := by
  rw [lcmRayArithmeticLetter_eq_deltaTotient]
  unfold deltaTotient
  rw [show periodLcm t + j + periodLcm t = 2 * periodLcm t + j from by omega]

/-! ### `prop:AR-04-inv` -- the exact totient difference on an LCM progression -/

/-- **The exact totient difference on an LCM progression** (`prop:AR-04-inv`),
the product law the identity follows from:
`φ(jx) = φ(j)φ(x)gcd(j,x)/φ(gcd(j,x))`, which retains all primes shared by
`j` and `x`. -/
theorem totient_mul_eq_totient_mul_gcd_div_totient_gcd {j x : ℕ} (hj : 0 < j)
    (hx : 0 < x) :
    (Nat.totient (j * x) : ℚ)
      = (Nat.totient j : ℚ) * (Nat.totient x : ℚ) * (Nat.gcd j x : ℚ)
          / (Nat.totient (Nat.gcd j x) : ℚ) := by
  have h := totient_mul_eq_overlapFactor_mul j x hx
  have hQ : ((Nat.totient (j * x) : ℕ) : ℚ)
      = ((totientOverlapFactor j x : ℕ) : ℚ) * (Nat.totient x : ℚ) := by
    rw [h]; push_cast; ring
  rw [hQ, cast_totientOverlapFactor x hj]
  ring

/-- **The exact totient difference on an LCM progression** (`prop:AR-04-inv`),
well-formedness of the product formula: for a divisor offset `j ∣ H` we have
`j ≥ 1` because `H > 0`, so both denominators `φ(g₁)` and `φ(g₂)` are
nonzero. -/
theorem lcmRay_divisor_denominators_pos {t j : ℕ} (hjdvd : j ∣ periodLcm t) :
    0 < j
      ∧ 0 < Nat.totient (Nat.gcd j (periodLcm t / j + 1))
      ∧ 0 < Nat.totient (Nat.gcd j (2 * (periodLcm t / j) + 1)) := by
  have hHpos : 0 < periodLcm t := periodLcm_pos t
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact absurd (Nat.eq_zero_of_zero_dvd hjdvd) hHpos.ne'
    · exact h
  exact ⟨hjpos,
    Nat.totient_pos.mpr (gcd_pos_of_left_pos _ hjpos),
    Nat.totient_pos.mpr (gcd_pos_of_left_pos _ hjpos)⟩

/-- **The exact totient difference on an LCM progression** (`prop:AR-04-inv`),
divisor case.  With `H = H(t)`, `j ∣ H`, `a = H/j`,
`g₁ = gcd(j,a+1)` and `g₂ = gcd(j,2a+1)`,
`δ_t(j) = φ(j)·(g₂φ(2a+1)/φ(g₂) - g₁φ(a+1)/φ(g₁))`.
Here `j ≥ 1` because `H > 0`, so both denominators are nonzero. -/
theorem lcmRay_divisor_product_formula {t j : ℕ} (hjdvd : j ∣ periodLcm t) :
    ((Nat.totient (2 * periodLcm t + j) : ℚ)
        - (Nat.totient (periodLcm t + j) : ℚ))
      = (Nat.totient j : ℚ) *
          ((Nat.gcd j (2 * (periodLcm t / j) + 1) : ℚ)
                * (Nat.totient (2 * (periodLcm t / j) + 1) : ℚ)
                / (Nat.totient (Nat.gcd j (2 * (periodLcm t / j) + 1)) : ℚ)
            - (Nat.gcd j (periodLcm t / j + 1) : ℚ)
                * (Nat.totient (periodLcm t / j + 1) : ℚ)
                / (Nat.totient (Nat.gcd j (periodLcm t / j + 1)) : ℚ)) := by
  have hHpos : 0 < periodLcm t := periodLcm_pos t
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact absurd (Nat.eq_zero_of_zero_dvd hjdvd) hHpos.ne'
    · exact h
  have hletter : lcmRayArithmeticLetter t j
      = lcmDivisorRayLetter (periodLcm t) j := by
    unfold lcmRayArithmeticLetter
    rw [if_pos hjdvd]
  have hZ : lcmDivisorRayLetter (periodLcm t) j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ) := by
    rw [← hletter]
    exact lcmRayArithmeticLetter_eq_totient_difference t j
  have hQ : ((lcmDivisorRayLetter (periodLcm t) j : ℤ) : ℚ)
      = (Nat.totient (2 * periodLcm t + j) : ℚ)
        - (Nat.totient (periodLcm t + j) : ℚ) := by
    rw [hZ]; push_cast; ring
  rw [← hQ]
  unfold lcmDivisorRayLetter
  dsimp only
  push_cast
  rw [cast_totientOverlapFactor (2 * (periodLcm t / j) + 1) hjpos,
    cast_totientOverlapFactor (periodLcm t / j + 1) hjpos]
  ring

/-- **The exact totient difference on an LCM progression** (`prop:AR-04-inv`),
nondivisor case: for `j ∤ H` the arithmetic source retains the literal
totient difference, so no coprimality assumption is imposed on the full
expression. -/
theorem lcmRay_nondivisor_literal {t j : ℕ} (hjdvd : ¬ j ∣ periodLcm t) :
    lcmRayArithmeticLetter t j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ) ∧
      lcmRayArithmeticLetter t j = deltaTotient (periodLcm t) (periodLcm t + j) := by
  refine ⟨lcmRayArithmeticLetter_eq_totient_difference t j, ?_⟩
  unfold lcmRayArithmeticLetter
  rw [if_neg hjdvd]

/-- **The exact totient difference on an LCM progression** (`prop:AR-04-inv`),
clean case: if every prime dividing `j` also divides `a = H/j`, then
`g₁ = g₂ = 1` and the formula reduces to `φ(j)(φ(2a+1) - φ(a+1))`. -/
theorem lcmRay_divisor_clean_formula {t j : ℕ} (hjdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm t / j) :
    Nat.gcd j (periodLcm t / j + 1) = 1
      ∧ Nat.gcd j (2 * (periodLcm t / j) + 1) = 1
      ∧ (Nat.totient (2 * periodLcm t + j) : ℤ)
            - (Nat.totient (periodLcm t + j) : ℤ)
          = (Nat.totient j : ℤ)
              * ((Nat.totient (2 * (periodLcm t / j) + 1) : ℤ)
                  - (Nat.totient (periodLcm t / j + 1) : ℤ)) := by
  have hg1 : Nat.gcd j (periodLcm t / j + 1) = 1 :=
    gcd_succ_eq_one_of_forall_prime_dvd hclean
  have hg2 : Nat.gcd j (2 * (periodLcm t / j) + 1) = 1 :=
    gcd_succ_eq_one_of_forall_prime_dvd
      (fun p hp hpj => (hclean p hp hpj).mul_left 2)
  refine ⟨hg1, hg2, ?_⟩
  have hQ := lcmRay_divisor_product_formula hjdvd
  rw [hg1, hg2] at hQ
  simp only [Nat.totient_one, Nat.cast_one, one_mul, div_one] at hQ
  exact_mod_cast hQ

/-- **The exact totient difference on an LCM progression** (`prop:AR-04-inv`),
the worked example.  At `H = j = 2` the two gcds are `g₁ = 2` and `g₂ = 1`;
the exact difference is `φ(6) - φ(4) = 0`, whereas discarding the gcd factors
would give `1`. -/
theorem lcmRay_divisor_gcd_example :
    periodLcm 2 = 2
      ∧ Nat.gcd 2 (periodLcm 2 / 2 + 1) = 2
      ∧ Nat.gcd 2 (2 * (periodLcm 2 / 2) + 1) = 1
      ∧ (Nat.totient (2 * periodLcm 2 + 2) : ℤ)
            - (Nat.totient (periodLcm 2 + 2) : ℤ) = 0
      ∧ (Nat.totient 2 : ℤ)
            * ((Nat.totient (2 * (periodLcm 2 / 2) + 1) : ℤ)
                - (Nat.totient (periodLcm 2 / 2 + 1) : ℤ)) = 1 := by
  have hL : periodLcm 2 = 2 := by
    show Nat.lcm (periodLcm 1) 2 = 2
    show Nat.lcm (Nat.lcm (periodLcm 0) 1) 2 = 2
    show Nat.lcm (Nat.lcm 1 1) 2 = 2
    norm_num [Nat.lcm]
  have h2 : Nat.totient 2 = 1 := by
    rw [Nat.totient_prime Nat.prime_two]
  have h3 : Nat.totient 3 = 2 := by
    rw [Nat.totient_prime (by norm_num)]
  have h4 : Nat.totient 4 = 2 := by
    have h := Nat.totient_prime_pow (p := 2) (n := 2) Nat.prime_two (by norm_num)
    norm_num at h
    exact h
  have h6 : Nat.totient 6 = 2 := by
    have h := Nat.totient_mul (m := 2) (n := 3) (by norm_num [Nat.Coprime])
    rw [h2, h3] at h
    norm_num at h
    exact h
  refine ⟨hL, ?_, ?_, ?_, ?_⟩ <;> rw [hL] <;> norm_num [h2, h3, h4, h6]

/-! ### `prop:AR-03-inv` -- a lower bound for the totient of a rough integer -/

/-- **A lower bound for the totient of a rough integer** (`prop:AR-03-inv`).
Let `a ≥ 8`, `t = 2^a`, and let `n > 0` have all prime factors greater than
`t`.  If `n < 2^(2t)`, then `n` has fewer than `t/4` distinct prime factors
and `φ(n) > (3/4)·n`. -/
theorem rough_integer_prime_count_and_totient_bound {a n : ℕ} (ha : 8 ≤ a)
    (hnPos : 0 < n) (hrough : ∀ r : ℕ, Nat.Prime r → r ∣ n → 2 ^ a < r)
    (hnPow : n < 2 ^ (2 * 2 ^ a)) :
    n.primeFactors.card < 2 ^ a / 4
      ∧ (3 / 4 : ℚ) * (n : ℚ) < (Nat.totient n : ℚ) :=
  ⟨rough_primeFactors_card_lt_quarter_of_lt_two_pow ha hnPos hrough hnPow,
    three_quarters_mul_lt_totient_of_rough_lt_two_pow ha hnPos hrough hnPow⟩

/-! ### `prop:AR-05-inv` -- positivity of the short-window differences -/

/-- **Positivity of the short-window differences** (`prop:AR-05-inv`).
For `a ≥ 8` and `1 ≤ j < 2·2^a`,
`δ_{2^a}(j) = φ(2H+j) - φ(H+j) > 0` with `H = H(2^a)`.
No rationality hypothesis is used. -/
theorem shortWindow_totient_difference_pos {a j : ℕ} (ha : 8 ≤ a)
    (hjpos : 0 < j) (hjlt : j < 2 * 2 ^ a) :
    0 < (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
          - (Nat.totient (periodLcm (2 ^ a) + j) : ℤ) := by
  have h := lcmRayArithmeticLetter_pos_of_lt_two_mul ha hjpos hjlt
  rwa [lcmRayArithmeticLetter_eq_totient_difference] at h

/-! ### `prop:AR-06-inv` -- the accumulated sum is the discrepancy -/

/-- **The accumulated sum is the discrepancy** (`prop:AR-06-inv`).
For all `t, L`, the weighted diagonal sum `∑_{j=1}^{L} δ_t(j)2^{L-j}` is
exactly `D(H(t), H(t), L)`. -/
theorem weighted_shortWindow_sum_eq_windowDiscrepancy (t L : ℕ) :
    (∑ r ∈ Finset.range L,
        ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
            - (Nat.totient (periodLcm t + (r + 1)) : ℤ)) * 2 ^ (L - 1 - r))
      = windowDiscrepancy (periodLcm t) (periodLcm t) L := by
  have hword : lcmDiagonalArithmeticWord t L
      = ∑ r ∈ Finset.range L,
          lcmRayArithmeticLetter t (r + 1) * 2 ^ (L - 1 - r) := rfl
  have hcongr : (∑ r ∈ Finset.range L,
        ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
            - (Nat.totient (periodLcm t + (r + 1)) : ℤ)) * 2 ^ (L - 1 - r))
      = ∑ r ∈ Finset.range L,
          lcmRayArithmeticLetter t (r + 1) * 2 ^ (L - 1 - r) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [lcmRayArithmeticLetter_eq_totient_difference]
  rw [hcongr, ← hword]
  exact lcmDiagonalArithmeticWord_eq_windowDiscrepancy t L

/-- **The accumulated sum is the discrepancy** (`prop:AR-06-inv`), second
clause: the two-sided residue inequality for that weighted sum is precisely
the certificate `𝒞(H(t), H(t), L)`. -/
theorem weighted_shortWindow_band_iff_certifiedKill (t L : ℕ) :
    ((2 * (periodLcm t : ℤ) + L + 2 <
          (∑ r ∈ Finset.range L,
              ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
                  - (Nat.totient (periodLcm t + (r + 1)) : ℤ))
                * 2 ^ (L - 1 - r)) % 2 ^ L)
        ∧ (∑ r ∈ Finset.range L,
              ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
                  - (Nat.totient (periodLcm t + (r + 1)) : ℤ))
                * 2 ^ (L - 1 - r)) % 2 ^ L
            < 2 ^ L - (2 * (periodLcm t : ℤ) + L + 2))
      ↔ certifiedKill (periodLcm t) (periodLcm t) L := by
  rw [weighted_shortWindow_sum_eq_windowDiscrepancy]
  unfold certifiedKill
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

#print axioms lcmRayArithmeticLetter_eq_totient_difference
#print axioms totient_mul_eq_totient_mul_gcd_div_totient_gcd
#print axioms lcmRay_divisor_denominators_pos
#print axioms lcmRay_divisor_product_formula
#print axioms lcmRay_nondivisor_literal
#print axioms lcmRay_divisor_clean_formula
#print axioms lcmRay_divisor_gcd_example
#print axioms rough_integer_prime_count_and_totient_bound
#print axioms shortWindow_totient_difference_pos
#print axioms weighted_shortWindow_sum_eq_windowDiscrepancy
#print axioms weighted_shortWindow_band_iff_certifiedKill
end ErdosProblems.Erdos249.PaperCompleteR21
