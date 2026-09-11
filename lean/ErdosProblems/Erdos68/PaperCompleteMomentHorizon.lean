import ErdosProblems.Erdos68.DivisorChannelBasis
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# The actual factorial specialisation of the quadratic tail-gcd theorem

Short-note label: res:finite-channel-moment-certificate.

This file does not assume a recurrence for an arbitrary sequence or assume
unordered-block divisibility. It derives the recurrence for U_n(1) from the
supplied definition and obtains the block identity from Mathlib's
Nat.uniformBell_mul_eq. The gcd of an infinite family is represented by its
universal property (all common divisors), avoiding an arbitrary choice of a
generator in Z. This is the exact gcd assertion, not a weaker bound.

STATUS: uncompiled proof candidate. No new axioms, no proof placeholders.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators

noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1

lemma channelScalar_two : channelScalar 2 = 2 := by
  simp [channelScalar, isolatedChannelUnit_two, adjacentDifference]

lemma channelScalar_odd {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) :
    channelScalar n = 0 :=
  isolatedChannelUnit_apply_one_of_odd hn hodd

/-- The scalar recurrence for the actual isolated-channel units. -/
lemma channelScalar_recurrence {n : ℕ} (hn : 2 < n) :
    channelScalar n = -∑ d ∈ Finset.Ico 2 n,
      if d ∣ n then (channelWeight n d : ℤ) * channelScalar d else 0 := by
  classical
  have hT : adjacentDifference n 1 = 0 := by
    have hn1 : n ≠ 1 := by omega
    have hp1 : n - 1 ≠ 1 := by omega
    simp [adjacentDifference, hn1, hp1, Ne.symm hn1, Ne.symm hp1]
  unfold channelScalar
  rw [isolatedChannelUnit_of_two_le (by omega), Finsupp.sub_apply, hT,
    zero_sub, Finsupp.finset_sum_apply]
  congr 1
  rw [← Finset.sum_attach (s := Finset.Ico 2 n)
      (f := fun d => if d ∣ n then
        (channelWeight n d : ℤ) * isolatedChannelUnit d 1 else 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : (d : ℕ) ∣ n
  · simp [hd]
  · simp [hd]

/-- A block quotient is an integer multiple of k!, not merely an integer. -/
lemma factorial_dvd_channelWeight_mul (d k : ℕ) (hd : 0 < d) :
    k.factorial ∣ channelWeight (d * k) d := by
  have hblock := Nat.uniformBell_mul_eq k (Nat.ne_of_gt hd)
  have heq : channelWeight (d * k) d = Nat.uniformBell k d * k.factorial := by
    unfold channelWeight
    rw [Nat.mul_div_cancel_left _ hd]
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hblock.symm
  rw [heq]
  exact dvd_mul_left _ _

lemma factorial_dvd_channelWeight_of_dvd {d n : ℕ}
    (hd : 0 < d) (hdn : d ∣ n) :
    (n / d).factorial ∣ channelWeight n d := by
  have heq : d * (n / d) = n := Nat.mul_div_cancel' hdn
  simpa only [heq] using factorial_dvd_channelWeight_mul d (n / d) hd

/-- The only proper divisors >=2 of 2p are 2 and p. -/
lemma divisor_twice_prime {p d : ℕ} (hp : p.Prime)
    (hd : 2 ≤ d) (hlt : d < 2 * p) (hdiv : d ∣ 2 * p) :
    d = 2 ∨ d = p := by
  obtain ⟨k, hk⟩ := hdiv
  have hpdk : p ∣ d * k := by
    rw [← hk]
    exact dvd_mul_left _ _
  rcases hp.dvd_mul.mp hpdk with hpd | hpk
  · obtain ⟨j, hj⟩ := hpd
    have hjpos : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      simp [this] at hj
      omega
    have hjle : j < 2 := by
      by_contra h
      have : 2 ≤ j := by omega
      nlinarith [hp.pos]
    have : j = 1 := by omega
    exact Or.inr (by simpa [this] using hj)
  · obtain ⟨j, hj⟩ := hpk
    have heq : p * 2 = p * (d * j) := by
      calc
        p * 2 = 2 * p := by ring
        _ = d * k := hk
        _ = p * (d * j) := by rw [hj]; ring
    have heq' : 2 = d * j := mul_left_cancel₀ hp.ne_zero heq
    have hjpos : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      simp [this] at heq'
    left
    nlinarith

lemma channelScalar_twice_prime {p : ℕ} (hp : p.Prime) :
    channelScalar (2 * p) = -2 * (channelWeight (2 * p) 2 : ℤ) := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  rw [channelScalar_recurrence (by omega)]
  have h2mem : 2 ∈ Finset.Ico 2 (2 * p) := by
    simp only [Finset.mem_Ico]; omega
  rw [Finset.sum_eq_single 2]
  · simp [channelScalar_two]
    ring
  · intro d hd hne
    by_cases hdn : d ∣ 2 * p
    · have hd2 : 2 ≤ d := (Finset.mem_Ico.mp hd).1
      have hdlt : d < 2 * p := (Finset.mem_Ico.mp hd).2
      rcases divisor_twice_prime hp hd2 hdlt hdn with h | h
      · exact (hne h).elim
      · subst d
        have hpne : p ≠ 2 := hne
        have hodd : Odd p := hp.odd_of_ne_two hpne
        simp [hdn, channelScalar_odd hp2 hodd]
    · simp [hdn]
  · exact fun h => (h h2mem).elim

lemma channelScalar_twice_prime_ne_zero {p : ℕ} (hp : p.Prime) :
    channelScalar (2 * p) ≠ 0 := by
  have hden := channelWeight_mul_denominator (2 * p) 2 (by decide)
  have hw : channelWeight (2 * p) 2 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hden
    exact (Nat.factorial_ne_zero (2 * p)) hden.symm
  rw [channelScalar_twice_prime hp]
  exact mul_ne_zero (by norm_num) (by exact_mod_cast hw)

/-- The prime anchor divides its factorial, including the exceptional prime 2. -/
lemma channelScalar_twice_prime_dvd_factorial {p : ℕ} (hp : p.Prime) :
    channelScalar (2 * p) ∣ ((2 * p).factorial : ℤ) := by
  have hp1 : 1 ≤ p := le_trans (by decide) hp.two_le
  have hden : 2 ^ p * channelWeight (2 * p) 2 = (2 * p).factorial := by
    simpa using channelWeight_mul_denominator (2 * p) 2 (by decide)
  have hpow : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hp1, pow_succ]
    ring
  refine ⟨-((2 : ℤ) ^ (p - 1)), ?_⟩
  rw [channelScalar_twice_prime hp]
  have hdenZ : (2 : ℤ) ^ p * (channelWeight (2 * p) 2 : ℤ) =
      ((2 * p).factorial : ℤ) := by exact_mod_cast hden
  rw [← hdenZ, hpow]
  ring

noncomputable def finiteScalarGcd (D N : ℕ) : ℕ :=
  (Finset.Icc (D + 1) N).gcd (fun n => (channelScalar n).natAbs)

/-- The universal property that uniquely specifies the positive tail gcd. -/
def IsScalarTailGcd (D G : ℕ) : Prop :=
  ∀ b : ℕ, b ∣ G ↔ ∀ n : ℕ, D < n → (b : ℤ) ∣ channelScalar n

lemma finiteScalarGcd_dvd_iff (D N b : ℕ) :
    b ∣ finiteScalarGcd D N ↔
      ∀ n : ℕ, D < n → n ≤ N → (b : ℤ) ∣ channelScalar n := by
  simp only [finiteScalarGcd, Finset.dvd_gcd_iff, Finset.mem_Icc]
  constructor
  · intro h n hn hN
    exact Int.natCast_dvd.mpr (h n ⟨by omega, hN⟩)
  · intro h n hn
    exact Int.natCast_dvd.mp (h n (by omega) hn.2)

/-- An integer divisor of the computed tail propagates if it divides q!,
with the explicit cutoff D(q-1). No scalar recurrence is assumed. -/
theorem factorial_tail_divisor_closure {D N q : ℕ} {g : ℤ}
    (hD : 2 ≤ D) (hN : D * (q - 1) ≤ N)
    (hq : g ∣ (q.factorial : ℤ))
    (hprefix : ∀ n : ℕ, D < n → n ≤ N → g ∣ channelScalar n) :
    ∀ n : ℕ, D < n → g ∣ channelScalar n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hnN : n ≤ N
    · exact hprefix n hn hnN
    · have hNn : N < n := by omega
      rw [channelScalar_recurrence (by omega)]
      apply dvd_neg.mpr
      apply Finset.dvd_sum
      intro d hd
      by_cases hdn : d ∣ n
      · simp only [if_pos hdn]
        have hd2 : 2 ≤ d := (Finset.mem_Ico.mp hd).1
        have hdlt : d < n := (Finset.mem_Ico.mp hd).2
        by_cases hdD : d ≤ D
        · have heq : d * (n / d) = n := Nat.mul_div_cancel' hdn
          have hqk : q ≤ n / d := by
            by_contra h
            have hk : n / d ≤ q - 1 := by omega
            have hnle : n ≤ D * (q - 1) := by
              calc n = d * (n / d) := heq.symm
                   _ ≤ D * (q - 1) := Nat.mul_le_mul hdD hk
            omega
          have hqW : q.factorial ∣ channelWeight n d :=
            dvd_trans (Nat.factorial_dvd_factorial hqk)
              (factorial_dvd_channelWeight_of_dvd (by omega) hdn)
          have hgW : g ∣ (channelWeight n d : ℤ) :=
            dvd_trans hq (by exact_mod_cast hqW)
          exact dvd_mul_of_dvd_left hgW _
        · exact dvd_mul_of_dvd_right (ih d hdlt (by omega)) _
      · simp [hdn]

/-- Exact finite determination of the infinite-tail gcd. The hypothesis
D/2<p is written in the equivalent division-free form D<2p. -/
theorem quadratic_scalar_tail_gcd {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < 2 * p) (hpD : p ≤ D) :
    let H := D * (2 * p - 1)
    0 < finiteScalarGcd D H ∧
      IsScalarTailGcd D (finiteScalarGcd D H) ∧ H < 2 * D ^ 2 := by
  dsimp only
  let H := D * (2 * p - 1)
  have hp2 := hp.two_le
  have hanchor : 2 * p ≤ H := by
    dsimp [H]
    have hsub : 2 * p - 1 + 1 = 2 * p := by omega
    nlinarith
  have hgAnchor : ((finiteScalarGcd D H : ℕ) : ℤ) ∣ channelScalar (2 * p) :=
    (finiteScalarGcd_dvd_iff D H (finiteScalarGcd D H)).mp (dvd_refl _) _ hDp hanchor
  have hgpos : 0 < finiteScalarGcd D H := by
    by_contra h
    have hz : finiteScalarGcd D H = 0 := by omega
    rw [hz, Nat.cast_zero, zero_dvd_iff] at hgAnchor
    exact channelScalar_twice_prime_ne_zero hp hgAnchor
  have hfull : ∀ n : ℕ, D < n →
      ((finiteScalarGcd D H : ℕ) : ℤ) ∣ channelScalar n := by
    apply factorial_tail_divisor_closure (q := 2 * p) hD (le_refl _)
    · exact dvd_trans hgAnchor (channelScalar_twice_prime_dvd_factorial hp)
    · exact (finiteScalarGcd_dvd_iff D H _).mp (dvd_refl _)
  refine ⟨hgpos, ?_, ?_⟩
  · intro b
    constructor
    · intro hb n hn
      exact dvd_trans (by exact_mod_cast hb) (hfull n hn)
    · intro hb
      exact (finiteScalarGcd_dvd_iff D H b).mpr (fun n hn _ => hb n hn)
  · dsimp [H]
    have hsub : 2 * p - 1 + 1 = 2 * p := by omega
    nlinarith

/-- Literal floor-division version of the displayed short-note hypothesis. -/
theorem finite_channel_moment_certificate {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    let H := D * (2 * p - 1)
    0 < finiteScalarGcd D H ∧
      IsScalarTailGcd D (finiteScalarGcd D H) ∧ H < 2 * D ^ 2 := by
  exact quadratic_scalar_tail_gcd hD hp (by omega) hpD

/-- Universal properties give literal equality with any already named tail gcd. -/
theorem finite_channel_moment_certificate_eq {D p G : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hG : IsScalarTailGcd D G) :
    G = finiteScalarGcd D (D * (2 * p - 1)) := by
  have hg := (finite_channel_moment_certificate hD hp hDp hpD).2.1
  apply Nat.dvd_antisymm
  · exact (hg G).mpr ((hG G).mp (dvd_refl _))
  · exact (hG _).mpr ((hg _).mp (dvd_refl _))

end ErdosProblems.Erdos68.PaperComplete
