import Erdos257PeriodNoncollapse.TropicalCurvatureCarry
import Mathlib.Tactic

/-!
# Erdős #249: prime-ray cyclotomic curvature

This module isolates finite consequences of two explicit hypotheses.
`BoundedDegreeOrderConsumer C m d` gives bounded-degree multiplicative-order
witnesses for prime divisors of `C (m*q)`, while `PrimeRayLayerSupply C m`
asserts that nontrivial layers persist along a prime ray.  The first
hypothesis forces quantitative growth and escape from every fixed finite
prime support; together the two hypotheses give unbounded prime divisors.

Neither hypothesis is constructed here for the totient series.  In
particular, these results provide no carry escape, tail discrepancy,
irrationality theorem, or solution of Erdős #249.
-/

namespace ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature

/-- Mixed Boolean curvature on a two-anchor rectangle. -/
def checkerboard (F : Bool → Bool → ℤ) : ℤ :=
  F true true - F true false - F false true + F false false

/-- The checkerboard kills every sum of one-coordinate backgrounds. -/
theorem checkerboard_separable (u v : Bool → ℤ) :
    checkerboard (fun i j => u i + v j) = 0 := by
  simp [checkerboard]
  ring

/-- The checkerboard is the unique two-by-two joint annihilator up to scale. -/
theorem checkerboard_unique
    (c00 c10 c01 c11 : ℤ)
    (hrow0 : c00 + c01 = 0)
    (hrow1 : c10 + c11 = 0)
    (hcol0 : c00 + c10 = 0)
    (hcol1 : c01 + c11 = 0) :
    c10 = -c00 ∧ c01 = -c00 ∧ c11 = c00 := by
  constructor
  · omega
  · constructor <;> omega

/-- Abstract squarefree divisor-layer cancellation.  The hypotheses are the
four explicit divisor factorizations, so no resultant API is hidden here. -/
theorem fourPoint_layer_identity
    (A C : ℕ → ℕ) (r s q : ℕ)
    (hq : A q = C 1 * C q)
    (hrq : A (r * q) = C 1 * C r * C q * C (r * q))
    (hsq : A (s * q) = C 1 * C s * C q * C (s * q))
    (hrsq :
      A (r * s * q) =
        C 1 * C r * C s * C q *
          C (r * s) * C (r * q) * C (s * q) * C (r * s * q)) :
    A (r * s * q) * A q =
      A (r * q) * A (s * q) * C (r * s) * C (r * s * q) := by
  rw [hrsq, hq, hrq, hsq]
  ring

/-- Any prescribed residue class modulo an even modulus admits a digit which
recentres an affine carry step.  This generalises the legacy fixed-precision
valuation/unit completion no-go. -/
theorem residueClass_step_has_centred_completion
    (b a e M R : ℤ) (hR : 0 < R) (hM : M = 2 * R) :
    ∃ c e' : ℤ,
      (∃ z : ℤ, c = a + M * z) ∧
      e' = b * e + c ∧
      |e'| ≤ R := by
  let y := b * e + a + R
  let e' := y % M - R
  let c := e' - b * e
  have hMpos : 0 < M := by omega
  have hrem_nonneg : 0 ≤ y % M :=
    Int.emod_nonneg y (ne_of_gt hMpos)
  have hrem_lt : y % M < M :=
    Int.emod_lt_of_pos y hMpos
  have hdiv := Int.mul_ediv_add_emod y M
  have hclass : ∃ z : ℤ, c = a + M * z := by
    refine ⟨-(y / M), ?_⟩
    have hrem : y % M = y - M * (y / M) := by
      linarith [hdiv]
    dsimp [c, e']
    rw [hrem]
    dsimp [y]
    ring
  have hstep : e' = b * e + c := by
    dsimp [c]
    ring
  have hbound : |e'| ≤ R := by
    rw [abs_le]
    dsimp [e']
    omega
  exact ⟨c, e', hclass, hstep, hbound⟩

/-- Eventual nontrivial, clean cyclotomic layers on the prime ray `m*q`. -/
def PrimeRayLayerSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q)

/-- Every rational prime divisor of a layer supplies an exact-order witness
in extension degree at most `d`. -/
def BoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∀ q p : ℕ,
    q.Prime → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1

/-- Bounded-degree order witnesses beyond a prime-index cutoff.  Unlike
`BoundedDegreeOrderConsumer`, this permits the finitely many characteristic
primes that occur naturally in cyclotomic layers. -/
def EventualBoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q p : ℕ,
    q.Prime → Q₀ ≤ q → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1

/-- If a prime `p` divides `C (m*q)`, then a bounded-degree order witness
forces the exact natural-number inequality `m * q < p ^ d`. -/
theorem primeRay_divisor_pow_gt
    {C : ℕ → ℕ} {m d q p : ℕ}
    (horder : BoundedDegreeOrderConsumer C m d)
    (hq : q.Prime)
    (hp : p.Prime)
    (hpC : p ∣ C (m * q)) :
    m * q < p ^ d := by
  obtain ⟨k, hk1, hkd, horderDvd⟩ := horder q p hq hp hpC
  have hpk_sub_pos : 0 < p ^ k - 1 :=
    Nat.sub_pos_of_lt (one_lt_pow₀ hp.one_lt (by omega))
  have hmq_le : m * q ≤ p ^ k - 1 :=
    Nat.le_of_dvd hpk_sub_pos horderDvd
  have hpk_le_hpd : p ^ k ≤ p ^ d :=
    Nat.pow_le_pow_right hp.pos hkd
  omega

/-- If in addition `B ^ d ≤ m * q`, then the prime divisor `p` is strictly
larger than `B`. -/
theorem primeRay_divisor_gt_of_pow_le
    {C : ℕ → ℕ} {m d q p B : ℕ}
    (horder : BoundedDegreeOrderConsumer C m d)
    (hq : q.Prime)
    (hp : p.Prime)
    (hpC : p ∣ C (m * q))
    (hB : B ^ d ≤ m * q) :
    B < p := by
  have hpow : B ^ d < p ^ d :=
    hB.trans_lt (primeRay_divisor_pow_gt horder hq hp hpC)
  by_contra hBp
  exact (not_lt_of_ge (Nat.pow_le_pow_left (Nat.le_of_not_gt hBp) d)) hpow

/-- Large prime-ray layers escape every prescribed finite prime support. -/
def FinitePrimeSupportEscape (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)

/-- The prime divisors appearing on the ray `m*q` are unbounded, even after
imposing an arbitrary lower bound on the prime index `q`. -/
def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p

/-- Bounded-degree exact-order realisability already excludes every fixed
finite set of characteristics on a sufficiently remote prime ray.  The
Archimedean layer-supply hypothesis is not needed for this exclusion step. -/
theorem finitePrimeSupportEscape_of_orderConsumer
    {C : ℕ → ℕ} {m d : ℕ}
    (hm : 0 < m)
    (horder : BoundedDegreeOrderConsumer C m d) :
    FinitePrimeSupportEscape C m := by
  intro S
  let B := ∑ p ∈ S, p ^ d
  refine ⟨B + 1, ?_⟩
  intro q hq hqB p hpS hp
  intro hpC
  have hpd_le_B : p ^ d ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun x _ => Nat.zero_le (x ^ d)) hpS
  have hpd_lt_q : p ^ d < q := by omega
  have hmq_lt_q : m * q < q :=
    (primeRay_divisor_pow_gt horder hq hp hpC).trans hpd_lt_q
  exact (not_lt_of_ge (Nat.le_mul_of_pos_left q hm)) hmq_lt_q

/-- Eventual bounded-degree order realisability is already enough to exclude
every fixed finite set of characteristics on a sufficiently remote prime ray.
This is the version matched by actual cyclotomic layers. -/
theorem finitePrimeSupportEscape_of_eventualOrderConsumer
    {C : ℕ → ℕ} {m d : ℕ}
    (hm : 0 < m)
    (horder : EventualBoundedDegreeOrderConsumer C m d) :
    FinitePrimeSupportEscape C m := by
  obtain ⟨Qo, horder⟩ := horder
  intro S
  let B := ∑ p ∈ S, p ^ d
  refine ⟨max Qo (B + 1), ?_⟩
  intro q hq hqB p hpS hp hpC
  obtain ⟨k, hk1, hkd, horderDvd⟩ :=
    horder q p hq (le_trans (le_max_left _ _) hqB) hp hpC
  have hpk_sub_pos : 0 < p ^ k - 1 :=
    Nat.sub_pos_of_lt (one_lt_pow₀ hp.one_lt (by omega))
  have hmq_le : m * q ≤ p ^ k - 1 :=
    Nat.le_of_dvd hpk_sub_pos horderDvd
  have hpk_le_hpd : p ^ k ≤ p ^ d :=
    Nat.pow_le_pow_right hp.pos hkd
  have hpd_le_B : p ^ d ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun x _ => Nat.zero_le (x ^ d)) hpS
  have hpd_lt_q : p ^ d < q := by
    have hBq : B + 1 ≤ q := le_trans (le_max_right _ _) hqB
    omega
  have hmq_lt_q : m * q < q := by omega
  exact (not_lt_of_ge (Nat.le_mul_of_pos_left q hm)) hmq_lt_q

/-- Nontrivial layers together with finite-support escape force genuinely new,
arbitrarily large prime divisors on cofinally large prime indices. -/
theorem unboundedPrimeDivisorSupply_of_layerSupply_of_finitePrimeSupportEscape
    {C : ℕ → ℕ} {m : ℕ}
    (hsupply : PrimeRayLayerSupply C m)
    (hescape : FinitePrimeSupportEscape C m) :
    UnboundedPrimeDivisorSupply C m := by
  intro B N₀
  obtain ⟨Qs, hsupply⟩ := hsupply
  obtain ⟨Qe, hescape⟩ := hescape (Finset.range (B + 1))
  obtain ⟨q, hqLower, hq⟩ :=
    Nat.exists_infinite_primes (max N₀ (max Qs Qe))
  have hN₀q : N₀ ≤ q := le_trans (le_max_left _ _) hqLower
  have hQsq : Qs ≤ q := by
    exact le_trans (le_trans (le_max_left _ _) (le_max_right N₀ _)) hqLower
  have hQeq : Qe ≤ q := by
    exact le_trans (le_trans (le_max_right _ _) (le_max_right N₀ _)) hqLower
  obtain ⟨hC, -⟩ := hsupply q hq hQsq
  obtain ⟨p, hp, hpC⟩ := Nat.exists_prime_and_dvd (by omega : C (m * q) ≠ 1)
  have hp_not_small : p ∉ Finset.range (B + 1) := by
    intro hpRange
    exact hescape q hq hQeq p hpRange hp hpC
  have hBp : B < p := by
    rw [Finset.mem_range] at hp_not_small
    omega
  exact ⟨q, p, hq, hN₀q, hp, hpC, hBp⟩

/-- Bounded-degree order witnesses give finite-support escape; if nontrivial
prime-ray layers are also supplied, their prime divisors are unbounded. -/
theorem unboundedPrimeDivisorSupply_of_orderConsumer
    {C : ℕ → ℕ} {m d : ℕ}
    (hm : 0 < m)
    (hsupply : PrimeRayLayerSupply C m)
    (horder : BoundedDegreeOrderConsumer C m d) :
    UnboundedPrimeDivisorSupply C m :=
  unboundedPrimeDivisorSupply_of_layerSupply_of_finitePrimeSupportEscape
    hsupply (finitePrimeSupportEscape_of_orderConsumer hm horder)

/-- Eventual order witnesses and eventual nontrivial layers suffice for
cofinally unbounded prime divisors.  No conclusion about phase escape or
irrationality is asserted. -/
theorem unboundedPrimeDivisorSupply_of_eventualOrderConsumer
    {C : ℕ → ℕ} {m d : ℕ}
    (hm : 0 < m)
    (hsupply : PrimeRayLayerSupply C m)
    (horder : EventualBoundedDegreeOrderConsumer C m d) :
    UnboundedPrimeDivisorSupply C m :=
  unboundedPrimeDivisorSupply_of_layerSupply_of_finitePrimeSupportEscape
    hsupply (finitePrimeSupportEscape_of_eventualOrderConsumer hm horder)

#print axioms finitePrimeSupportEscape_of_orderConsumer
#print axioms finitePrimeSupportEscape_of_eventualOrderConsumer
#print axioms unboundedPrimeDivisorSupply_of_orderConsumer
#print axioms unboundedPrimeDivisorSupply_of_eventualOrderConsumer

end ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature
