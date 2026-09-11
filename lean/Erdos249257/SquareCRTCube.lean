import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic

/-!
# Square-CRT correction suppression for the totient series

This module formalizes the elementary part of the square-CRT proposal for
Erdős #249.  A square congruence fixes the cofactor modulo a prime, so the
weighted correction in the prime-dilation cocycle can be removed on any
prescribed finite horizon.  Pairwise-coprime square moduli can be imposed
simultaneously with a least representative below their product.

The final examples record both behaviours that any future analytic argument
must respect: a clean one-dimensional cube can have a nonzero coefficient,
but correction suppression alone does not force this—the smallest returned
countermodel has its whole two-step finite block equal to zero.

No irrationality claim is made here.  The missing input remains a residue or
anti-concentration estimate strong enough to beat the raw totient tail.  The
Dirichlet construction below gives isolated adjacent separations in one fixed
class modulo nine; it gives neither a density statement nor a quantitative
gap at a prescribed orbit scale.
-/

namespace Erdos249257
namespace SquareCRTCube

open Finset

/-! ## Exact prime-dilation arithmetic -/

/-- Exact prime-dilation cocycle for Euler's totient.  The second summand is
the weighted correction which square localization removes on a finite
horizon. -/
theorem totient_mul_prime_cocycle {p m : ℕ} (hp : p.Prime) :
    Nat.totient (p * m) =
      (p - 1) * Nat.totient m +
        if p ∣ m then Nat.totient m else 0 := by
  by_cases hpm : p ∣ m
  · rw [if_pos hpm, Nat.totient_mul_of_prime_of_dvd hp hpm]
    nth_rewrite 1 [← Nat.sub_add_cancel hp.one_le]
    ring
  · rw [if_neg hpm, Nat.totient_mul_of_prime_of_not_dvd hp hpm]
    simp

/-! ## Normalized cocycle and correlation order

The normalization `g(n) = φ(n) / n` gives scale-free rational coordinates
for the finite cube identities below.  Prime dilation remains linear in the
single value `g(m)`: divisibility changes only the rational coefficient.
Consequently, the exact square of any finite linear statistic expands into
pairwise products of normalized totients.  This algebraic identity supplies
no two-point estimate, cancellation bound, or analytic parameter range.
-/

/-- Euler's totient in the usual rational normalization.  The field
convention gives `normalizedTotient 0 = 0`. -/
def normalizedTotient (n : ℕ) : ℚ := (Nat.totient n : ℚ) / n

/-- Exact prime-dilation cocycle after normalization.  The right-hand side is
linear in the single normalized value at `m`; the divisibility correction is
absorbed into its rational coefficient. -/
theorem normalizedTotient_mul_prime_cocycle {p m : ℕ} (hp : p.Prime) :
    normalizedTotient (p * m) =
      (((p - 1 : ℕ) : ℚ) / p + if p ∣ m then (1 : ℚ) / p else 0) *
        normalizedTotient m := by
  by_cases hm : m = 0
  · simp [hm, normalizedTotient]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  rw [normalizedTotient, normalizedTotient, totient_mul_prime_cocycle hp]
  by_cases hpm : p ∣ m
  · simp only [if_pos hpm]
    push_cast [hp.one_le]
    field_simp [hp0, hm0]
  · simp only [if_neg hpm]
    push_cast [hp.one_le]
    field_simp [hp0, hm0]
    ring

/-- The algebraic second moment of a finite normalized-totient statistic
closes at correlation order two: its exact expansion contains only products
`g(n i) * g(n j)`, never a triple product. -/
theorem sq_normalizedTotient_linearForm_eq_pairwise
    {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (c : ι → ℚ) (n : ι → ℕ) :
    (∑ i ∈ E, c i * normalizedTotient (n i)) ^ 2 =
      ∑ i ∈ E, ∑ j ∈ E,
        (c i * c j) *
          (normalizedTotient (n i) * normalizedTotient (n j)) := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The affine weights in the smallest two-dimensional cube separate into
the main alternating term and two edge differences without raising
correlation order. -/
theorem affineTwoCube_eq_main_add_edges
    (x a b g₀ g₁ g₂ g₁₂ : ℚ) :
    x * g₀ - (x + a) * g₁ - (x + b) * g₂ +
        (x + a + b) * g₁₂ =
      x * (g₀ - g₁ - g₂ + g₁₂) +
        a * (g₁₂ - g₁) + b * (g₁₂ - g₂) := by
  ring

/-- After removing pure cubes and repeated-index terms, the cube of a
four-term linear statistic retains exactly the four distinct-index triple
products.  Any estimate based on this cubic expansion must therefore account
for those triple products; the identity itself supplies no estimate. -/
theorem cube_four_terms_distinctTriple_part
    (u₀ u₁ u₂ u₁₂ : ℚ) :
    (u₀ + u₁ + u₂ + u₁₂) ^ 3 -
        (u₀ ^ 3 + u₁ ^ 3 + u₂ ^ 3 + u₁₂ ^ 3) -
        3 * (u₀ ^ 2 * (u₁ + u₂ + u₁₂) +
          u₁ ^ 2 * (u₀ + u₂ + u₁₂) +
          u₂ ^ 2 * (u₀ + u₁ + u₁₂) +
          u₁₂ ^ 2 * (u₀ + u₁ + u₂)) =
      6 * (u₀ * u₁ * u₂ + u₀ * u₁ * u₁₂ +
        u₀ * u₂ * u₁₂ + u₁ * u₂ * u₁₂) := by
  ring

/-- The distinct-shift cubic terms for the affine two-cube have the displayed
coefficients, which may vanish for special parameter choices.  The sign
pattern comes from the two negative cube vertices. -/
theorem affineTwoCube_distinctTriple_part
    (x a b g₀ g₁ g₂ g₁₂ : ℚ) :
    6 * ((x * g₀) * (-(x + a) * g₁) * (-(x + b) * g₂) +
        (x * g₀) * (-(x + a) * g₁) * ((x + a + b) * g₁₂) +
        (x * g₀) * (-(x + b) * g₂) * ((x + a + b) * g₁₂) +
        (-(x + a) * g₁) * (-(x + b) * g₂) *
          ((x + a + b) * g₁₂)) =
      6 * (x * (x + a) * (x + b) * g₀ * g₁ * g₂ -
        x * (x + a) * (x + a + b) * g₀ * g₁ * g₁₂ -
        x * (x + b) * (x + a + b) * g₀ * g₂ * g₁₂ +
        (x + a) * (x + b) * (x + a + b) * g₁ * g₂ * g₁₂) := by
  ring

/-- General square-witness form.  The equality
`n = A + p * (a + p*t)` is the quotient-bearing form of
`n ≡ A + p*a [MOD p^2]`.  If `p ∤ a+h`, the cofactor at shift `h` is clean. -/
theorem totient_dilation_clean_of_square_residue
    {p A a t h : ℕ} (hp : p.Prime) (hclean : ¬p ∣ a + h) :
    Nat.totient (A + p * (a + p * t) + p * h - A) =
      (p - 1) * Nat.totient (a + p * t + h) := by
  have hpt : p ∣ p * t := dvd_mul_right p t
  have hcofactor : ¬p ∣ a + p * t + h := by
    intro hdvd
    apply hclean
    have hreorder : a + p * t + h = p * t + (a + h) := by omega
    rw [hreorder] at hdvd
    exact (Nat.dvd_add_iff_right hpt).mpr hdvd
  have harg : A + p * (a + p * t) + p * h - A =
      p * (a + p * t + h) := by
    calc
      A + p * (a + p * t) + p * h - A =
          p * (a + p * t) + p * h := by omega
      _ = p * (a + p * t + h) := by ring
  rw [harg]
  exact Nat.totient_mul_of_prime_of_not_dvd hp hcofactor

/-- Canonical anchor residue `a = 0`.  The hypotheses `0 < h < p` make the
whole horizon `1 ≤ h ≤ J < p` clean after imposing `n = A + p^2*t`. -/
theorem totient_dilation_clean_of_square_witness
    {p A t h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    Nat.totient (A + p ^ 2 * t + p * h - A) =
      (p - 1) * Nat.totient (p * t + h) := by
  have hclean : ¬p ∣ 0 + h := by
    simp only [zero_add]
    intro hdvd
    exact (not_le_of_gt hhp) (Nat.le_of_dvd hh hdvd)
  have hbase : p ^ 2 * t = p * (0 + p * t) := by
    ring
  rw [hbase]
  simpa [pow_two] using
    (totient_dilation_clean_of_square_residue
      (p := p) (A := A) (a := 0) (t := t) (h := h) hp hclean)

/-- An ordered square congruence has the quotient witness used by the clean
dilation theorem. -/
theorem exists_square_witness_of_modEq
    {p r n : ℕ} (hrn : r ≤ n) (hmod : n ≡ r [MOD p ^ 2]) :
    ∃ t : ℕ, n = r + p ^ 2 * t := by
  obtain ⟨t, ht⟩ : p ^ 2 ∣ n - r :=
    (Nat.modEq_iff_dvd' hrn).mp hmod.symm
  refine ⟨t, ?_⟩
  omega

/-- Direct `Nat.ModEq` adapter: once the CRT representative is at least its
target residue, the congruence produces a cofactor and the correction-free
totient identity at every clean shift. -/
theorem totient_dilation_clean_of_square_modEq
    {p A a n h : ℕ} (hp : p.Prime)
    (hresidue : A + p * a ≤ n)
    (hmod : n ≡ A + p * a [MOD p ^ 2])
    (hclean : ¬p ∣ a + h) :
    ∃ t : ℕ,
      n = A + p * (a + p * t) ∧
      Nat.totient (n + p * h - A) =
        (p - 1) * Nat.totient (a + p * t + h) := by
  obtain ⟨t, ht⟩ := exists_square_witness_of_modEq hresidue hmod
  have hn : n = A + p * (a + p * t) := by
    rw [ht]
    ring
  refine ⟨t, hn, ?_⟩
  rw [hn]
  exact totient_dilation_clean_of_square_residue hp hclean

/-! ## Finite simultaneous square CRT -/

/-- Distinct prime labels have pairwise-coprime square moduli. -/
theorem pairwise_coprime_prime_squares
    {ι : Type*} {E : Finset ι} {p : ι → ℕ}
    (hprime : ∀ i ∈ E, (p i).Prime)
    (hinj : Set.InjOn p (E : Set ι)) :
    Set.Pairwise (E : Set ι)
      (fun i j => Nat.Coprime (p i ^ 2) (p j ^ 2)) := by
  intro i hi j hj hij
  apply Nat.coprime_pow_primes 2 2 (hprime i hi) (hprime j hj)
  intro hpij
  exact hij (hinj hi hj hpij)

/-- A finite family of pairwise-coprime square congruences has a simultaneous
representative strictly below the product of the square moduli. -/
theorem exists_squareCRT_base
    {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p A a : ι → ℕ)
    (hmod : ∀ i ∈ E, p i ^ 2 ≠ 0)
    (hcop : Set.Pairwise (E : Set ι)
      (fun i j => Nat.Coprime (p i ^ 2) (p j ^ 2))) :
    ∃ n : ℕ,
      n < ∏ i ∈ E, p i ^ 2 ∧
      ∀ i ∈ E, n ≡ A i + p i * a i [MOD p i ^ 2] := by
  let n := Nat.chineseRemainderOfFinset
    (fun i => A i + p i * a i) (fun i => p i ^ 2) E hmod hcop
  refine ⟨n, ?_, ?_⟩
  · exact Nat.chineseRemainderOfFinset_lt_prod
      (fun i => A i + p i * a i) (fun i => p i ^ 2) hmod hcop
  · exact n.property

/-- Prime-specialized square CRT, including the least-base bound. -/
theorem exists_squareCRT_base_of_distinct_primes
    {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p A a : ι → ℕ)
    (hprime : ∀ i ∈ E, (p i).Prime)
    (hinj : Set.InjOn p (E : Set ι)) :
    ∃ n : ℕ,
      n < ∏ i ∈ E, p i ^ 2 ∧
      ∀ i ∈ E, n ≡ A i + p i * a i [MOD p i ^ 2] := by
  apply exists_squareCRT_base E p A a
  · intro i hi
    exact pow_ne_zero _ (hprime i hi).ne_zero
  · exact pairwise_coprime_prime_squares hprime hinj

/-- The least CRT representative can be lifted above any prescribed anchor
floor at a cost of less than one additional block of `B+1` square moduli.
This is the exact finite-family version of the least-admissible-base ledger. -/
theorem exists_large_squareCRT_base
    {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p A a : ι → ℕ) (B : ℕ)
    (hmod : ∀ i ∈ E, p i ^ 2 ≠ 0)
    (hcop : Set.Pairwise (E : Set ι)
      (fun i j => Nat.Coprime (p i ^ 2) (p j ^ 2))) :
    ∃ n : ℕ,
      B < n ∧
      n < (∏ i ∈ E, p i ^ 2) * (B + 2) ∧
      ∀ i ∈ E, n ≡ A i + p i * a i [MOD p i ^ 2] := by
  obtain ⟨n₀, hn₀lt, hn₀mod⟩ := exists_squareCRT_base E p A a hmod hcop
  let Q := ∏ i ∈ E, p i ^ 2
  have hQne : Q ≠ 0 := by
    dsimp [Q]
    exact Finset.prod_ne_zero_iff.mpr hmod
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQne
  let n := n₀ + Q * (B + 1)
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [n]
    nlinarith
  · dsimp [n, Q] at hn₀lt ⊢
    nlinarith
  · intro i hi
    have hdiv : p i ^ 2 ∣ Q := by
      dsimp [Q]
      exact Finset.dvd_prod_of_mem (fun j => p j ^ 2) hi
    have hzero : Q * (B + 1) ≡ 0 [MOD p i ^ 2] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hdiv (B + 1))
    dsimp [n]
    simpa using (hn₀mod i hi).add hzero

/-- Simultaneous square-CRT correction suppression on a finite family.  One
common base works at every label and every shift whose chosen cofactor residue
avoids zero modulo the corresponding prime. -/
theorem exists_squareCRT_clean_totient_family
    {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p A a : ι → ℕ)
    (hprime : ∀ i ∈ E, (p i).Prime)
    (hinj : Set.InjOn p (E : Set ι)) :
    ∃ n : ℕ,
      n < (∏ i ∈ E, p i ^ 2) *
        (E.sup (fun i => A i + p i * a i) + 2) ∧
      ∀ i ∈ E, ∀ h : ℕ, ¬p i ∣ a i + h →
        ∃ t : ℕ,
          n = A i + p i * (a i + p i * t) ∧
          Nat.totient (n + p i * h - A i) =
            (p i - 1) * Nat.totient (a i + p i * t + h) := by
  let B := E.sup (fun i => A i + p i * a i)
  have hmod : ∀ i ∈ E, p i ^ 2 ≠ 0 := fun i hi =>
    pow_ne_zero _ (hprime i hi).ne_zero
  have hcop := pairwise_coprime_prime_squares hprime hinj
  obtain ⟨n, hBn, hnlt, hnmod⟩ :=
    exists_large_squareCRT_base E p A a B hmod hcop
  refine ⟨n, ?_, ?_⟩
  · simpa [B] using hnlt
  · intro i hi h hclean
    have hresidue : A i + p i * a i ≤ n := by
      exact (Finset.le_sup (f := fun j => A j + p j * a j) hi).trans hBn.le
    exact totient_dilation_clean_of_square_modEq
      (hprime i hi) hresidue (hnmod i hi) hclean

/-- Canonical finite-horizon corollary.  If every distinct construction prime
exceeds `J`, the residue choice `a = 0` removes every totient dilation
correction simultaneously for all `1 ≤ h ≤ J`. -/
theorem exists_squareCRT_clean_horizon
    {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p A : ι → ℕ) (J : ℕ)
    (hprime : ∀ i ∈ E, (p i).Prime)
    (hinj : Set.InjOn p (E : Set ι))
    (horizon : ∀ i ∈ E, J < p i) :
    ∃ n : ℕ,
      n < (∏ i ∈ E, p i ^ 2) * (E.sup A + 2) ∧
      ∀ i ∈ E, ∀ h : ℕ, 0 < h → h ≤ J →
        ∃ t : ℕ,
          n = A i + p i ^ 2 * t ∧
          Nat.totient (n + p i * h - A i) =
            (p i - 1) * Nat.totient (p i * t + h) := by
  obtain ⟨n, hnlt, hclean⟩ :=
    exists_squareCRT_clean_totient_family E p A (fun _ => 0) hprime hinj
  refine ⟨n, ?_, ?_⟩
  · simpa using hnlt
  · intro i hi h hh hhJ
    have hhp : h < p i := lt_of_le_of_lt hhJ (horizon i hi)
    have hnot : ¬p i ∣ 0 + h := by
      simp only [zero_add]
      intro hdvd
      exact (not_le_of_gt hhp) (Nat.le_of_dvd hh hdvd)
    obtain ⟨t, hn, htot⟩ := hclean i hi h hnot
    refine ⟨t, ?_, ?_⟩
    · calc
        n = A i + p i * (0 + p i * t) := hn
        _ = A i + p i ^ 2 * t := by ring
    · simpa using htot

/-! ## Abstract cube pairing -/

/-- Alternating Boolean-cube terms cancel exactly when insertion of one
coordinate does not change the underlying term.  This is the algebraic core
of the first-`k` Hilbert-cube cancellation, separated from all totient and CRT
hypotheses. -/
theorem alternating_powerset_sum_eq_zero_of_insert_invariant
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∉ s) (f : Finset ι → ℤ)
    (hinv : ∀ t ∈ s.powerset, f (insert i t) = f t) :
    ∑ t ∈ (insert i s).powerset, (-1 : ℤ) ^ t.card * f t = 0 := by
  rw [Finset.sum_powerset_insert hi]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro t ht
  have hit : i ∉ t := notMem_mono (Finset.mem_powerset.mp ht) hi
  rw [Finset.card_insert_of_notMem hit, pow_succ, hinv t ht]
  ring

/-! ## Exact regression witnesses -/

/-- One-dimensional actual-totient cube coefficient. -/
def actualOneCubeCoeff (n r0 r1 : ℕ) : ℤ :=
  (Nat.totient (n + r0) : ℤ) - Nat.totient (n + r1)

/-- A raw one-cube coefficient is exactly the corresponding affine-weighted
normalized-totient coefficient.  The positivity assumptions only discharge
the two denominators introduced by `normalizedTotient`. -/
theorem actualOneCubeCoeff_cast_eq_weighted_normalizedTotient
    {n r0 r1 : ℕ} (h0 : 0 < n + r0) (h1 : 0 < n + r1) :
    (actualOneCubeCoeff n r0 r1 : ℚ) =
      (n + r0 : ℕ) * normalizedTotient (n + r0) -
        (n + r1 : ℕ) * normalizedTotient (n + r1) := by
  have h0q : (((n + r0 : ℕ) : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt h0)
  have h1q : (((n + r1 : ℕ) : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt h1)
  unfold actualOneCubeCoeff normalizedTotient
  push_cast at h0q h1q ⊢
  rw [mul_div_cancel₀ _ h0q, mul_div_cancel₀ _ h1q]

/-- Adjacent totients separate arbitrarily far out inside the fixed prime-square
class `n ≡ -1 (mod 3²)`.  Dirichlet supplies a prime `n` in that class.
Then `φ(n) = n - 1` is not divisible by `3`, whereas `3² ∣ n + 1`
forces `φ(3²) = 6 ∣ φ(n + 1)`.  This is an infinite square-class
separation result, rather than a single finite witness. -/
theorem exists_gt_actualOneCubeCoeff_ne_zero_in_squareClass (B : ℕ) :
    ∃ n > B, n ≡ 8 [MOD 9] ∧ actualOneCubeCoeff n 0 1 ≠ 0 := by
  obtain ⟨n, hnB, hnprime, hnmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq B (q := 9) (a := 8)
      (by norm_num) (by norm_num)
  refine ⟨n, hnB, hnmod, ?_⟩
  have hnmod3 : n ≡ 8 [MOD 3] := hnmod.of_dvd (by norm_num)
  have hthree_not_dvd : ¬3 ∣ n - 1 := by
    intro hthree
    have hzero : n - 1 ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr hthree
    have hone : n ≡ 1 [MOD 3] := by
      have hadd := hzero.add_right 1
      simpa [Nat.sub_add_cancel hnprime.one_le] using hadd
    have hbad : 1 ≡ 8 [MOD 3] := hone.symm.trans hnmod3
    norm_num [Nat.ModEq] at hbad
  have hnadd : n + 1 ≡ 0 [MOD 9] := by
    have hadd := hnmod.add_right 1
    norm_num at hadd
    simpa [Nat.ModEq] using hadd
  have hnine_dvd : 9 ∣ n + 1 := Nat.modEq_zero_iff_dvd.mp hnadd
  have hsix_dvd : 6 ∣ Nat.totient (n + 1) := by
    have htotient_dvd := Nat.totient_dvd_of_dvd hnine_dvd
    norm_num at htotient_dvd
    exact htotient_dvd
  have hthree_dvd : 3 ∣ Nat.totient (n + 1) :=
    (by norm_num : 3 ∣ 6).trans hsix_dvd
  intro hzero
  have htotient_eq : Nat.totient n = Nat.totient (n + 1) := by
    unfold actualOneCubeCoeff at hzero
    norm_num only [Nat.add_zero, Nat.add_one] at hzero
    exact_mod_cast (sub_eq_zero.mp hzero)
  rw [Nat.totient_prime hnprime] at htotient_eq
  apply hthree_not_dvd
  rw [htotient_eq]
  exact hthree_dvd

/-- The same square-class separation in normalized coordinates.  Affine
weights recover the raw totient coefficient exactly, so no correlation
hypothesis is needed.  The free choice of `n` supplies neither a prescribed
square-CRT base nor a residue gap at the `periodLcm (2 ^ a)` height. -/
theorem exists_gt_weightedNormalizedTotient_ne_zero_in_squareClass (B : ℕ) :
    ∃ n > B, n ≡ 8 [MOD 9] ∧
      (n : ℚ) * normalizedTotient n -
          (n + 1 : ℕ) * normalizedTotient (n + 1) ≠ 0 := by
  obtain ⟨n, hnB, hnmod, hcoeff⟩ :=
    exists_gt_actualOneCubeCoeff_ne_zero_in_squareClass B
  refine ⟨n, hnB, hnmod, ?_⟩
  have hweighted := actualOneCubeCoeff_cast_eq_weighted_normalizedTotient
    (n := n) (r0 := 0) (r1 := 1) (by omega) (by omega)
  simp only [Nat.add_zero, Nat.cast_add, Nat.cast_one] at hweighted
  push_cast
  rw [← hweighted]
  exact_mod_cast hcoeff

/-- A clean square-localized cube need not separate: the returned minimal
`k = 1`, `J = 2` model has both finite coefficients equal to zero. -/
theorem squareCRT_clean_block_can_vanish :
    (13 : ℕ).Prime ∧ (5 : ℕ).Prime ∧
    52 ≡ 52 [MOD 13 ^ 2] ∧
    52 ≡ 2 [MOD 5 ^ 2] ∧
    actualOneCubeCoeff 52 13 13 = 0 ∧
    actualOneCubeCoeff 52 26 18 = 0 := by decide

/-- The vanishing witness is genuinely correction-free at both vertices and
both controlled shifts, not merely an equality of unrelated totient values. -/
theorem squareCRT_vanishing_countermodel_is_clean :
    Nat.totient (13 * (4 + 1)) = (13 - 1) * Nat.totient (4 + 1) ∧
    Nat.totient (5 * (12 + 1)) = (5 - 1) * Nat.totient (12 + 1) ∧
    Nat.totient (13 * (4 + 2)) = (13 - 1) * Nat.totient (4 + 2) ∧
    Nat.totient (5 * (12 + 2)) = (5 - 1) * Nat.totient (12 + 2) := by
  decide

/-- Correction suppression is not identically trivial: a nearby clean cube
has a nonzero second coefficient. -/
theorem squareCRT_clean_block_can_be_nonzero :
    (3 : ℕ).Prime ∧ (5 : ℕ).Prime ∧
    27 ≡ 0 [MOD 3 ^ 2] ∧
    27 ≡ 2 [MOD 5 ^ 2] ∧
    actualOneCubeCoeff 27 3 3 = 0 ∧
    actualOneCubeCoeff 27 6 8 = -4 := by decide

/-- The nonzero witness is also clean at both vertices and both shifts. -/
theorem squareCRT_nonzero_countermodel_is_clean :
    Nat.totient (3 * (9 + 1)) = (3 - 1) * Nat.totient (9 + 1) ∧
    Nat.totient (5 * (5 + 1)) = (5 - 1) * Nat.totient (5 + 1) ∧
    Nat.totient (3 * (9 + 2)) = (3 - 1) * Nat.totient (9 + 2) ∧
    Nat.totient (5 * (5 + 2)) = (5 - 1) * Nat.totient (5 + 2) := by
  decide

#print axioms totient_mul_prime_cocycle
#print axioms normalizedTotient_mul_prime_cocycle
#print axioms sq_normalizedTotient_linearForm_eq_pairwise
#print axioms affineTwoCube_eq_main_add_edges
#print axioms cube_four_terms_distinctTriple_part
#print axioms affineTwoCube_distinctTriple_part
#print axioms totient_dilation_clean_of_square_witness
#print axioms totient_dilation_clean_of_square_modEq
#print axioms exists_squareCRT_base_of_distinct_primes
#print axioms exists_large_squareCRT_base
#print axioms exists_squareCRT_clean_totient_family
#print axioms exists_squareCRT_clean_horizon
#print axioms alternating_powerset_sum_eq_zero_of_insert_invariant
#print axioms actualOneCubeCoeff_cast_eq_weighted_normalizedTotient
#print axioms exists_gt_actualOneCubeCoeff_ne_zero_in_squareClass
#print axioms exists_gt_weightedNormalizedTotient_ne_zero_in_squareClass
#print axioms squareCRT_clean_block_can_vanish
#print axioms squareCRT_vanishing_countermodel_is_clean
#print axioms squareCRT_clean_block_can_be_nonzero
#print axioms squareCRT_nonzero_countermodel_is_clean

end SquareCRTCube
end Erdos249257
