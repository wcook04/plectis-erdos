import ErdosProblems.Erdos249.CyclotomicAnchoredKill

/-! Paper-form restatements of the long #249 paper's prime-support block:

* "Unbounded prime support in Mersenne factors" — every prime divisor of
  `2^q - 1` at prime index `q` has `ord_p(2) = q` and hence `q ∣ p - 1`, and
  the prime divisors of the layers `2^n - 1` are unbounded unconditionally;
* "A prime satisfying the stated cyclotomic conditions" — for every period
  `h > 0` and threshold `N₀` a clean prime factor of `|Φ_{hq}(2)|`, together
  with the cyclotomic order decomposition it rests on;
* "A sufficient order hypothesis for unbounded prime support" — the
  bounded-degree order hypothesis, the forced coprimality, the equivalence
  with `ord_{mq}(p) ≤ d`, the inequality `mq < p^d`, escape from every fixed
  finite prime set, the unbounded-divisor conclusion under nontrivial layers,
  the `C(n) = 2^n - 1` instance with `m = d = 1`, the eventual form used by
  the binary cyclotomic family, and the failure of the all-prime form at
  `Φ₆(2) = 3`.

Here `C` is a layer function, `|Φ_n(2)|` is
`((Polynomial.cyclotomic n ℤ).eval 2).natAbs`, and `ord_n(x)` is
`orderOf ((x : ℕ) : ZMod n)`. -/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature
open ErdosProblems.Erdos249.CyclotomicAnchoredKill

/-! ### "Unbounded prime support in Mersenne factors" -/

/-- **Prime-index Mersenne divisors.**  If `q` and `p` are prime and
`p ∣ 2^q - 1`, then the order of `2` modulo `p` is exactly `q`, and
consequently `q ∣ p - 1`. -/
theorem mersenneLayer_prime_divisor_order {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ q - 1) :
    orderOf ((2 : ℕ) : ZMod p) = q ∧ q ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hone : 1 ≤ 2 ^ q := Nat.one_le_pow _ _ (by norm_num)
  have hmodeq : (1 : ℕ) ≡ 2 ^ q [MOD p] := (Nat.modEq_iff_dvd' hone).mpr hdvd
  have hcast : ((1 : ℕ) : ZMod p) = ((2 ^ q : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodeq
  have hpow : ((2 : ℕ) : ZMod p) ^ q = 1 := by
    have h := hcast.symm
    push_cast at h ⊢
    exact h
  have hdvdOrd : orderOf ((2 : ℕ) : ZMod p) ∣ q := orderOf_dvd_of_pow_eq_one hpow
  have hord : orderOf ((2 : ℕ) : ZMod p) = q := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hdvdOrd) with h1 | hq'
    · exfalso
      have h2 : ((2 : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.mp h1
      have hcast2 : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        rw [h2, Nat.cast_one]
      have hmod2 : (2 : ℕ) ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast2
      have hdvd1 : p ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod2.symm
      have hp1 : p = 1 := Nat.dvd_one.mp hdvd1
      have := hp.one_lt
      omega
    · exact hq'
  exact ⟨hord, prime_index_dvd_pred hq hp (by simpa [mersenneLayer] using hdvd)⟩

/-- **Unbounded prime support in the Mersenne layers, unconditionally.**
For every size bound `B` and index threshold `N₀` there are a prime `q ≥ N₀`
and a prime `p > B` with `p ∣ 2^q - 1`. -/
theorem mersenneLayer_unbounded_prime_support (B N₀ : ℕ) :
    ∃ q p : ℕ, q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ 2 ^ q - 1 ∧ B < p := by
  obtain ⟨q, p, hq, hN, hp, hdvd, hB⟩ := mersenneLayer_unboundedPrimeDivisorSupply B N₀
  exact ⟨q, p, hq, hN, hp, by simpa [mersenneLayer] using hdvd, hB⟩

/-! ### "A prime satisfying the stated cyclotomic conditions" -/

/-- **A clean binary cyclotomic anchor.**  For every period `h > 0` and every
threshold `N₀` there are a prime `q` and a prime factor `p` of `|Φ_{hq}(2)|`
with `p` coprime to `hq`, `hq ∣ p - 1`, and `p - 1 ≥ N₀`. -/
theorem exists_clean_cyclotomic_anchor_paper (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ, q.Prime ∧ p.Prime ∧
      p ∣ ((Polynomial.cyclotomic (h * q) ℤ).eval 2).natAbs ∧
      Nat.Coprime p (h * q) ∧ h * q ∣ p - 1 ∧ N₀ ≤ p - 1 := by
  obtain ⟨q, p, hq, hp, hcop, hlayer, hdvd, hN⟩ :=
    exists_clean_binaryCyclotomicAnchor h N₀ hh
  exact ⟨q, p, hq, hp, by simpa [binaryCyclotomicLayer] using hlayer, hcop, hdvd, hN⟩

/-- **The cyclotomic order decomposition.**  A prime divisor `p` of `Φ_n(2)`
satisfies `n = p^a · ord_p(2)` for some `a`; the exceptional characteristic
case is exactly `a > 0`. -/
theorem cyclotomic_layer_prime_order_decomposition_paper {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime)
    (hpdvd : p ∣ ((Polynomial.cyclotomic n ℤ).eval 2).natAbs) :
    ∃ a : ℕ, n = p ^ a * orderOf ((2 : ℕ) : ZMod p) :=
  binaryCyclotomicLayer_prime_order_decomposition hn hp
    (by simpa [binaryCyclotomicLayer] using hpdvd)

/-! ### "A sufficient order hypothesis for unbounded prime support" -/

/-- The displayed hypothesis, written out. -/
theorem boundedDegreeOrderConsumer_unfolded (C : ℕ → ℕ) (m d : ℕ) :
    BoundedDegreeOrderConsumer C m d ↔
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ C (m * q) →
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1 :=
  Iff.rfl

/-- **The divisibility forces `gcd(p, mq) = 1`.** -/
theorem coprime_of_dvd_pow_sub_one {n p k : ℕ} (hp : 0 < p) (hk : 1 ≤ k)
    (hdvd : n ∣ p ^ k - 1) : Nat.Coprime p n := by
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp
  have h1 : Nat.gcd p n ∣ p ^ k :=
    dvd_trans (Nat.gcd_dvd_left p n) (dvd_pow_self p (by omega))
  have h2 : Nat.gcd p n ∣ p ^ k - 1 := dvd_trans (Nat.gcd_dvd_right p n) hdvd
  have h3 : Nat.gcd p n ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub h1 h2
  have heq : p ^ k - (p ^ k - 1) = 1 := by omega
  rw [heq] at h3
  exact Nat.dvd_one.mp h3

/-- The divisibility `n ∣ p^k - 1` is exactly `ord_n(p) ∣ k`. -/
theorem dvd_pow_sub_one_iff_orderOf_dvd {n p k : ℕ} (hn : 0 < n) (hp : 0 < p) :
    n ∣ p ^ k - 1 ↔ orderOf ((p : ℕ) : ZMod n) ∣ k := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp
  rw [← Nat.modEq_iff_dvd' hpk]
  constructor
  · intro hmod
    refine orderOf_dvd_of_pow_eq_one ?_
    have hcast : ((1 : ℕ) : ZMod n) = ((p ^ k : ℕ) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    have h := hcast.symm
    push_cast at h ⊢
    exact h
  · intro hord
    have hpow : ((p : ℕ) : ZMod n) ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
    have hcast : ((p ^ k : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      push_cast
      exact hpow
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hcast).symm

/-- **The witness range is equivalent to a bound on the order.**  For `p`
coprime to `n > 0`, a `k` with `1 ≤ k ≤ d` and `n ∣ p^k - 1` exists exactly
when `ord_n(p) ≤ d`. -/
theorem boundedOrder_witness_iff_orderOf_le {n p d : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hcop : Nat.Coprime p n) :
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ n ∣ p ^ k - 1) ↔ orderOf ((p : ℕ) : ZMod n) ≤ d := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have heuler : n ∣ p ^ Nat.totient n - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp)).mp
      (Nat.ModEq.pow_totient hcop).symm
  have hordpos : 0 < orderOf ((p : ℕ) : ZMod n) := by
    have hdvd := (dvd_pow_sub_one_iff_orderOf_dvd hn hp).mp heuler
    have htpos : 0 < Nat.totient n := Nat.totient_pos.mpr hn
    by_contra hcon
    have h0 : orderOf ((p : ℕ) : ZMod n) = 0 := by omega
    rw [h0] at hdvd
    have := Nat.eq_zero_of_zero_dvd hdvd
    omega
  constructor
  · rintro ⟨k, hk1, hkd, hdvd⟩
    have hord := (dvd_pow_sub_one_iff_orderOf_dvd hn hp).mp hdvd
    exact le_trans (Nat.le_of_dvd (by omega) hord) hkd
  · intro hle
    exact ⟨orderOf ((p : ℕ) : ZMod n), hordpos, hle,
      (dvd_pow_sub_one_iff_orderOf_dvd hn hp).mpr dvd_rfl⟩

/-- **The hypothesis forces `mq < p^d`.** -/
theorem orderConsumer_index_lt_pow {C : ℕ → ℕ} {m d q p : ℕ}
    (horder : BoundedDegreeOrderConsumer C m d)
    (hq : q.Prime) (hp : p.Prime) (hpC : p ∣ C (m * q)) :
    m * q < p ^ d :=
  primeRay_divisor_pow_gt horder hq hp hpC

/-- **Every fixed finite set of primes is disjoint from the prime divisors of
`C(mq)` for all sufficiently large prime `q`.** -/
theorem orderConsumer_finite_prime_escape {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q) :=
  finitePrimeSupportEscape_of_orderConsumer hm horder

/-- **Nontrivial layers give arbitrarily large prime divisors.**  If in
addition `C(mq) > 1` and `gcd(C(mq), mq) = 1` for all sufficiently large
prime `q`, then for every `B, N₀` there are primes `q ≥ N₀` and `p > B` with
`p ∣ C(mq)`. -/
theorem orderConsumer_unbounded_prime_divisors {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m)
    (hlayer : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q))
    (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p :=
  unboundedPrimeDivisorSupply_of_orderConsumer hm hlayer horder

/-- **The extraction step uses only `C(mq) > 1`.**  Finite-support escape
together with eventual nontriviality already gives unbounded prime divisors;
the coprimality clause of the layer hypothesis is not needed here. -/
theorem unbounded_prime_divisors_of_escape_of_nontrivial {C : ℕ → ℕ} {m : ℕ}
    (hnontrivial : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q → 1 < C (m * q))
    (hescape : FinitePrimeSupportEscape C m) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p := by
  intro B N₀
  obtain ⟨Qs, hnontrivial⟩ := hnontrivial
  obtain ⟨Qe, hescape⟩ := hescape (Finset.range (B + 1))
  obtain ⟨q, hqLower, hq⟩ := Nat.exists_infinite_primes (max N₀ (max Qs Qe))
  have hN₀q : N₀ ≤ q := le_trans (le_max_left _ _) hqLower
  have hQsq : Qs ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right N₀ _)) hqLower
  have hQeq : Qe ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right N₀ _)) hqLower
  have hC := hnontrivial q hq hQsq
  obtain ⟨p, hp, hpC⟩ := Nat.exists_prime_and_dvd (by omega : C (m * q) ≠ 1)
  have hp_not_small : p ∉ Finset.range (B + 1) := fun hpRange =>
    hescape q hq hQeq p hpRange hp hpC
  rw [Finset.mem_range] at hp_not_small
  exact ⟨q, p, hq, hN₀q, hp, hpC, by omega⟩

/-- **The instance `C(n) = 2^n - 1` with `m = d = 1`.**  The hypothesis holds,
and for a prime divisor `p` of `2^q - 1` the order of `p` modulo `q` is `1`
while the order of `2` modulo `p` is `q`. -/
theorem mersenneLayer_orderConsumer_instance :
    BoundedDegreeOrderConsumer (fun n => 2 ^ n - 1) 1 1 ∧
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ 2 ^ q - 1 →
        orderOf ((p : ℕ) : ZMod q) = 1 ∧ orderOf ((2 : ℕ) : ZMod p) = q := by
  constructor
  · intro q p hq hp hdvd
    exact mersenneLayer_orderConsumer q p hq hp (by simpa [mersenneLayer] using hdvd)
  · intro q p hq hp hdvd
    obtain ⟨hord2, hqp⟩ := mersenneLayer_prime_divisor_order hq hp hdvd
    refine ⟨?_, hord2⟩
    haveI : NeZero q := ⟨hq.pos.ne'⟩
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hmod : (1 : ℕ) ≡ p [MOD q] := (Nat.modEq_iff_dvd' hp1).mpr hqp
    have hcast : ((1 : ℕ) : ZMod q) = ((p : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    exact orderOf_eq_one_iff.mpr (by simpa using hcast.symm)

/-- **The eventual form is what the binary cyclotomic family satisfies.**
Beyond `q > max(m, 2^m)` the binary cyclotomic layer has degree-one order
witnesses, and the same escape and unboundedness conclusions follow. -/
theorem eventual_orderConsumer_conclusions {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : EventualBoundedDegreeOrderConsumer C m d) :
    FinitePrimeSupportEscape C m ∧
      (∀ hsupply : PrimeRayLayerSupply C m, UnboundedPrimeDivisorSupply C m) :=
  ⟨finitePrimeSupportEscape_of_eventualOrderConsumer hm horder,
    fun hsupply => unboundedPrimeDivisorSupply_of_eventualOrderConsumer hm hsupply horder⟩

/-- The binary cyclotomic layer satisfies the eventual hypothesis with
`d = 1`, past the explicit threshold `max (m+1) (2^m+1)`. -/
theorem binaryCyclotomicLayer_eventual_instance (m : ℕ) (hm : 0 < m) :
    EventualBoundedDegreeOrderConsumer binaryCyclotomicLayer m 1 :=
  binaryCyclotomicLayer_eventualOrderConsumer m hm

/-- **The all-prime form fails.**  `|Φ₆(2)| = 3` and `6 ∤ 3 - 1`, so the
global bounded-degree hypothesis is false at `m = 2`, `d = 1`. -/
theorem binaryCyclotomic_allPrime_form_fails :
    ((Polynomial.cyclotomic 6 ℤ).eval 2).natAbs = 3 ∧ ¬ (6 ∣ 3 - 1) ∧
      ¬ BoundedDegreeOrderConsumer binaryCyclotomicLayer 2 1 := by
  refine ⟨?_, by norm_num, binaryCyclotomicLayer_not_globalOrderConsumer⟩
  norm_num [Polynomial.cyclotomic_six]

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_prime_divisor_order
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_unbounded_prime_support
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_clean_cyclotomic_anchor_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_layer_prime_order_decomposition_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.boundedDegreeOrderConsumer_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprime_of_dvd_pow_sub_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dvd_pow_sub_one_iff_orderOf_dvd
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.boundedOrder_witness_iff_orderOf_le
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_index_lt_pow
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_finite_prime_escape
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_unbounded_prime_divisors
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.unbounded_prime_divisors_of_escape_of_nontrivial
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_orderConsumer_instance
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.eventual_orderConsumer_conclusions
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomicLayer_eventual_instance
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomic_allPrime_form_fails
