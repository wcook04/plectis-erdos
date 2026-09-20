import Erdos249257.MersenneShadowCyclotomicNoncollapse
import Erdos249257.RepunitMobiusNumerator
import Mathlib.Tactic

/-!
Paper-form restatement of `thm:mersenne-channel-survival` ("Denominators of
finite Mersenne sums") from the long Erdős #257 manuscript
`paper/reasoning-parts/erdos257/a257_front.tex:2980`.

The paper writes `M_r = 2^r - 1` and, for positive squarefree `r`,

  `A_r = ∑_{d ∣ r} μ(d) (r/d) (M_r / M_d) ∈ ℤ`,
  `B(r) = A_r / M_r = ∑_{d ∣ r} μ(d)(r/d) / (2^d - 1)`.

Both displayed forms are transcribed here as `paperA` and `paperB`, and shown
to agree (`paperB_eq_divInt_paperA`).  The theorem itself asserts, for integers
`t ≥ 1`, `h ≥ 1` and squarefree `r ≥ 1` all of whose prime factors are at most
`t`, and for a set `P` of prime divisors of `r` with `t < 2p` for each `p ∈ P`,
that `C / gcd(C, h)` divides `den(h B(r))`, where `C = ∏_{p ∈ P} (2^p - 1)`;
that `C` itself divides that reduced denominator when `gcd(C, h) = 1`; and that
the factors of `C` are pairwise coprime because
`gcd(2^p - 1, 2^q - 1) = 2^{gcd(p,q)} - 1 = 1` for distinct primes.

The existing tree theorems `upperHalfChannel_survivorProduct_dvd_den` and
`upperHalfChannel_product_dvd_den_of_coprime_scale` carry `5 ≤ t`, which is
strictly stronger than the paper's `t ≥ 1`, and speak about
`Rat.divInt (h * mobiusNumerator r) (mersenne r)` rather than about `B(r)`.
This file removes both gaps: `coprime_mersenneTwo_mobiusNumerator` settles the
residual channel `p = 2` (which forces `t ∈ {2, 3}`), and
`paperB_eq_baseMobiusShadow` identifies the paper's divisor sum with the tree's
`baseMobiusShadow`.
-/

open scoped BigOperators

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257

/-! ### The paper's objects `A_r` and `B(r)` -/

/-- The paper's integral Möbius numerator
`A_r = ∑_{d ∣ r} μ(d) (r/d) (M_r / M_d)`. -/
def paperA (r : ℕ) : ℤ :=
  ∑ d ∈ r.divisors,
    ArithmeticFunction.moebius d * (((r / d : ℕ)) : ℤ) *
      (((RadicalMobiusShadow.mersenne r /
        RadicalMobiusShadow.mersenne d : ℕ)) : ℤ)

/-- The paper's finite rational sum `B(r) = ∑_{d ∣ r} μ(d)(r/d) / (2^d - 1)`. -/
noncomputable def paperB (r : ℕ) : ℚ :=
  ∑ d ∈ r.divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℚ) * ((r : ℚ) / (d : ℚ)) /
      ((2 : ℚ) ^ d - 1)

/-- For `s ⊆ primeFactors r` with `r` squarefree, `μ(∏ s) = (-1)^{|s|}`. -/
private theorem moebius_prod_subset_primeFactors {r : ℕ}
    (hr : Squarefree r) {s : Finset ℕ} (hs : s ⊆ r.primeFactors) :
    ArithmeticFunction.moebius (s.prod id) = (-1 : ℤ) ^ s.card := by
  have hsprime : ∀ p ∈ s, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (hs hp)
  have hproddiv : s.prod id ∣ r := by
    calc
      s.prod id ∣ r.primeFactors.prod id :=
        Finset.prod_dvd_prod_of_subset s r.primeFactors id hs
      _ = r := Nat.prod_primeFactors_of_squarefree hr
  have hsq : Squarefree (s.prod id) := hr.squarefree_of_dvd hproddiv
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
  congr 1
  rw [ArithmeticFunction.cardFactors_apply]
  calc
    (s.prod id).primeFactorsList.length =
        (s.prod id).primeFactors.card := by
          exact (List.toFinset_card_of_nodup hsq.nodup_primeFactorsList).symm
    _ = s.card := by
      simpa [Function.id_def] using
        congrArg Finset.card (Nat.primeFactors_prod hsprime)

/-- The paper's `A_r` is the tree's `mobiusNumerator r`: the nonsquarefree
divisors contribute zero, and the remaining divisors are exactly the products
over subsets of the prime factors. -/
theorem paperA_eq_mobiusNumerator {r : ℕ} (hr : Squarefree r) :
    paperA r = RadicalMobiusShadow.mobiusNumerator r := by
  unfold paperA
  rw [← Nat.divisors_filter_squarefree_of_squarefree hr,
    Nat.sum_divisors_filter_squarefree hr.ne_zero, Nat.factors_eq]
  unfold RadicalMobiusShadow.mobiusNumerator
  apply Finset.sum_congr rfl
  intro s hs
  have hmobius :=
    moebius_prod_subset_primeFactors hr (Finset.mem_powerset.mp hs)
  rw [s.prod_val, Function.id_def]
  have hmobius' :
      ArithmeticFunction.moebius (∏ x ∈ s, x) = (-1 : ℤ) ^ s.card := by
    simpa [Function.id_def] using hmobius
  rw [hmobius']

/-- The paper's `B(r)` is the tree's unscaled radical shadow. -/
theorem paperB_eq_baseMobiusShadow {r : ℕ} (hr : Squarefree r) :
    paperB r = RadicalMobiusShadow.baseMobiusShadow r := by
  rw [← RepunitMobiusNumerator.sum_divisors_moebius_ratio_eq_baseMobiusShadow hr]
  unfold paperB
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  have hdvd : d ∣ r := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hrpos
  have hone : (1 : ℕ) ≤ 2 ^ d := Nat.one_le_pow d 2 (by norm_num)
  have hMd : ((RadicalMobiusShadow.mersenne d : ℕ) : ℚ) = (2 : ℚ) ^ d - 1 := by
    simp only [RadicalMobiusShadow.mersenne]
    rw [Nat.cast_sub hone]
    push_cast
    ring
  rw [hMd, ← mul_div_assoc, div_div]

/-- The paper's two displays of `B(r)` agree: the divisor sum is `A_r / M_r`. -/
theorem paperB_eq_divInt_paperA {r : ℕ} (hr : Squarefree r) :
    paperB r = Rat.divInt (paperA r) (RadicalMobiusShadow.mersenne r : ℤ) := by
  rw [paperB_eq_baseMobiusShadow hr, paperA_eq_mobiusNumerator hr,
    RadicalMobiusShadow.baseMobiusShadow]

/-! ### Removing the `5 ≤ t` hypothesis: the residual channel `p = 2` -/

/-- The channel `p = 2` is the only one the tree's `5 ≤ t` argument misses.
It forces `t ≤ 3`, hence every prime factor of `r / 2` equals `3`, and
`gcd(2^2 - 1, 3^2 - 1) = gcd(3, 8) = 1`. -/
private theorem coprime_mersenneTwo_mobiusNumerator {r : ℕ}
    (hr : Squarefree r) (h2r : 2 ∣ r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ 3) :
    Nat.Coprime (RadicalMobiusShadow.mersenne 2)
      (RadicalMobiusShadow.mobiusNumerator r).natAbs := by
  have hquot : r / 2 ∣ r := Nat.div_dvd_of_dvd h2r
  have hsq : Squarefree (r / 2) := hr.squarefree_of_dvd hquot
  refine MersenneShadowCyclotomicNoncollapse.coprime_natAbs_of_sum_dvd
    (MersenneShadowCyclotomicNoncollapse.mobiusNumerator_mod_mersenne_prime hr
      Nat.prime_two h2r) ?_
  rw [MersenneShadowCyclotomicNoncollapse.jordanTotientTwo_natAbs_eq_prod hsq,
    Nat.coprime_prod_right_iff]
  intro q hq
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqr : q ∣ r := (Nat.dvd_of_mem_primeFactors hq).trans hquot
  have hq3 : q ≤ 3 := hcut q hqprime hqr
  have hq2 : 2 ≤ q := hqprime.two_le
  have hqne2 : q ≠ 2 := by
    rintro rfl
    have h2half : 2 ∣ r / 2 := Nat.dvd_of_mem_primeFactors hq
    have hr2 : 2 * (r / 2) = r := Nat.mul_div_cancel' h2r
    obtain ⟨k, hk⟩ := h2half
    have h4 : 2 * 2 ∣ r := ⟨k, by omega⟩
    have hu := hr 2 h4
    rw [Nat.isUnit_iff] at hu
    omega
  have hq3' : q = 3 := by omega
  subst hq3'
  have h3 : RadicalMobiusShadow.mersenne 2 = 3 := rfl
  have h8 : 3 ^ 2 - 1 = 8 := by norm_num
  rw [h3, h8]
  decide

/-- The tree's channel coprimality with the paper's hypothesis `t ≥ 1` in place
of `5 ≤ t`. -/
theorem channelProduct_coprime_mobiusNumerator_of_one_le
    {P : Finset ℕ} {t r : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (∏ p ∈ P, RadicalMobiusShadow.mersenne p)
      (RadicalMobiusShadow.mobiusNumerator r).natAbs := by
  apply Nat.Coprime.prod_left
  intro p hpP
  have hp : p.Prime := hprime p hpP
  have hpr' : p ∣ r := hpr p hpP
  have hupper' : t < 2 * p := hupper p hpP
  rcases Nat.lt_or_ge p 3 with hlt | hge
  · have hp2 : p = 2 := by
      have := hp.two_le
      omega
    subst hp2
    have ht3 : t ≤ 3 := by omega
    exact coprime_mersenneTwo_mobiusNumerator hr hpr'
      (fun q hq hqr => le_trans (hcut q hq hqr) ht3)
  · exact MersenneShadowCyclotomicNoncollapse.coprime_mersenne_mobiusNumerator
      hr hp hge hpr' hupper' hcut

/-- The tree's aggregate survivor theorem with `t ≥ 1` in place of `5 ≤ t`. -/
theorem upperHalfChannel_survivorProduct_dvd_den_of_one_le
    (P : Finset ℕ) {t r h : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    (∏ p ∈ P, RadicalMobiusShadow.mersenne p) /
        Nat.gcd (∏ p ∈ P, RadicalMobiusShadow.mersenne p) h ∣
      (Rat.divInt ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
        (RadicalMobiusShadow.mersenne r : ℤ)).den := by
  apply RationalDenominatorSurvival.survivingDivisor_dvd_scaled_divInt_den
  · exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hr.ne_zero)
  · exact MersenneShadowCyclotomicNoncollapse.channelProduct_dvd_mersenne
      hprime hpr
  · exact channelProduct_coprime_mobiusNumerator_of_one_le hr hprime hpr
      hupper hcut

/-! ### Paper statements -/

/-- Paper display of `thm:mersenne-channel-survival`, main clause: for integers
`t ≥ 1`, `h ≥ 1` and squarefree `r ≥ 1` whose prime factors are all at most `t`,
and a set `P` of prime divisors of `r` with `t < 2p` for every `p ∈ P`, the
channel product `C = ∏_{p ∈ P} (2^p - 1)` satisfies
`C / gcd(C, h) ∣ den(h B(r))`. -/
theorem paper_mersenne_channel_survival
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p) :
    (∏ p ∈ P, (2 ^ p - 1)) / Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h ∣
      ((h : ℚ) * paperB r).den := by
  have hB : (h : ℚ) * paperB r =
      Rat.divInt ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
        (RadicalMobiusShadow.mersenne r : ℤ) := by
    rw [paperB_eq_baseMobiusShadow hrsf, RadicalMobiusShadow.baseMobiusShadow,
      Rat.divInt_eq_div, Rat.divInt_eq_div]
    push_cast
    ring
  have hprod :
      (∏ p ∈ P, (2 ^ p - 1)) =
        ∏ p ∈ P, RadicalMobiusShadow.mersenne p := rfl
  rw [hB, hprod]
  exact upperHalfChannel_survivorProduct_dvd_den_of_one_le P hrsf hprime hpr
    hupper hcut

/-- Paper display of the "in particular" clause: `C` itself divides the reduced
denominator when `gcd(C, h) = 1`. -/
theorem paper_mersenne_channel_survival_of_coprime_scale
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hscale : Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h = 1) :
    (∏ p ∈ P, (2 ^ p - 1)) ∣ ((h : ℚ) * paperB r).den := by
  have hmain :=
    paper_mersenne_channel_survival P ht hh hr1 hrsf hcut hprime hpr hupper
  rwa [hscale, Nat.div_one] at hmain

/-- Paper display of the coprimality clause, with the displayed identity:
`gcd(2^p - 1, 2^q - 1) = 2^{gcd(p,q)} - 1 = 1` for distinct primes `p`, `q`. -/
theorem paper_channel_factor_gcd_eq_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 2 ^ Nat.gcd p q - 1 ∧
      Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 1 := by
  have hid : Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 2 ^ Nat.gcd p q - 1 :=
    Nat.pow_sub_one_gcd_pow_sub_one 2 p q
  refine ⟨hid, ?_⟩
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [hid, hcop.gcd_eq_one]
  norm_num

/-- The factors of `C` are pairwise coprime. -/
theorem paper_channel_factors_pairwise_coprime
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    (P : Set ℕ).Pairwise fun p q => Nat.Coprime (2 ^ p - 1) (2 ^ q - 1) := by
  intro p hp q hq hpq
  exact (paper_channel_factor_gcd_eq_one (hprime p (by simpa using hp))
    (hprime q (by simpa using hq)) hpq).2

#print axioms paperA_eq_mobiusNumerator
#print axioms paperB_eq_baseMobiusShadow
#print axioms paperB_eq_divInt_paperA
#print axioms channelProduct_coprime_mobiusNumerator_of_one_le
#print axioms upperHalfChannel_survivorProduct_dvd_den_of_one_le
#print axioms paper_mersenne_channel_survival
#print axioms paper_mersenne_channel_survival_of_coprime_scale
#print axioms paper_channel_factor_gcd_eq_one
#print axioms paper_channel_factors_pairwise_coprime

end ErdosProblems.Erdos257.PaperCompleteR21
