import Erdos257PeriodNoncollapse.RadicalMobiusShadow
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic

/-!
# The repunit Möbius numerator is a positive gcd word

This file proves the finite polynomial identity recorded as T1 in the private
Erdős #249 development.  On the intended boundary `Squarefree r`, the signed
repunit numerator

`∑ d ∣ r, μ(d) (r / d) (1 + X^d + ... + X^(r-d))`

is the gcd word whose coefficient at `X^k`, for `k < r`, is

`(r / gcd r k) * φ (gcd r k)`.

Thus every coefficient in the stated range is strictly positive and every
coefficient outside it is zero.  The squarefree hypothesis is kept explicit:
this module does not promote the formal development.s radical claim to a statement about
arbitrary nonsquarefree exponents.
-/

open scoped BigOperators ArithmeticFunction.Moebius Polynomial

namespace Erdos257PeriodNoncollapse.RepunitMobiusNumerator

/-- `1 + X^d + ... + X^((q - 1)d)`. -/
noncomputable def spacedRepunit (d q : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.monomial (d * j) 1

/-- The divisor-signed polynomial numerator.  For positive `r`, evaluation at
`X = 2` is the common-denominator Möbius numerator; the public bridge below is
stated only on the formal development.s squarefree boundary. -/
noncomputable def mobiusNumeratorPolynomial (r : ℕ) : ℤ[X] :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
      spacedRepunit d (r / d)

/-- The natural coefficient in the gcd-word presentation. -/
def gcdWordCoeff (r k : ℕ) : ℕ :=
  (r / r.gcd k) * (r.gcd k).totient

/-- The positive gcd word, represented by its first `r` coefficients. -/
noncomputable def gcdWord (r : ℕ) : ℤ[X] :=
  Polynomial.ofFn r fun k ↦ (gcdWordCoeff r k : ℤ)

private theorem coeff_spacedRepunit_of_lt {r d k : ℕ}
    (hr : 0 < r) (hd : d ∣ r) (hk : k < r) :
    (spacedRepunit d (r / d)).coeff k = if d ∣ k then 1 else 0 := by
  classical
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  rw [spacedRepunit, Polynomial.finset_sum_coeff]
  by_cases hdk : d ∣ k
  · have hmul : d * (k / d) = k := Nat.mul_div_cancel' hdk
    have hjlt : k / d < r / d := by
      rw [Nat.div_lt_iff_lt_mul hdpos, Nat.div_mul_cancel hd]
      exact hk
    have heq (j : ℕ) : d * j = k ↔ j = k / d := by
      constructor
      · intro h
        exact Nat.mul_left_cancel hdpos (h.trans hmul.symm)
      · rintro rfl
        exact hmul
    simp only [Polynomial.coeff_monomial]
    simp_rw [heq]
    simp [hjlt, hdk]
  · have heq (j : ℕ) : d * j ≠ k := by
      intro h
      exact hdk ⟨j, h.symm⟩
    simp [Polynomial.coeff_monomial, heq, hdk]

private theorem coeff_spacedRepunit_eq_zero_of_le {r d k : ℕ}
    (hr : 0 < r) (hd : d ∣ r) (hk : r ≤ k) :
    (spacedRepunit d (r / d)).coeff k = 0 := by
  classical
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  rw [spacedRepunit, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Polynomial.coeff_monomial, if_neg]
  have hjlt : d * j < r := by
    calc
      d * j < d * (r / d) :=
        (Nat.mul_lt_mul_left hdpos).2 (Finset.mem_range.mp hj)
      _ = r := Nat.mul_div_cancel' hd
  exact ne_of_lt (hjlt.trans_le hk)

private theorem moebius_divisor_sum_eq_totient (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors,
        ArithmeticFunction.moebius d * (((n / d : ℕ) : ℤ)) =
      (n.totient : ℤ) := by
  have hbase : ∀ m : ℕ, 0 < m →
      (∑ d ∈ m.divisors, (d.totient : ℤ)) = (m : ℤ) := by
    intro m _hm
    exact_mod_cast Nat.sum_totient m
  have hinv :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (R := ℤ) (f := fun m ↦ (m.totient : ℤ))
      (g := fun m ↦ (m : ℤ))).mp hbase n hn
  calc
    ∑ d ∈ n.divisors,
        ArithmeticFunction.moebius d * (((n / d : ℕ) : ℤ)) =
        ∑ x ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℤ) * (x.2 : ℤ) := by
            symm
            exact Nat.sum_divisorsAntidiagonal
              (fun d q ↦ (ArithmeticFunction.moebius d : ℤ) * (q : ℤ))
    _ = (n.totient : ℤ) := hinv

private theorem scaled_moebius_divisor_sum_eq (r g : ℕ)
    (hgpos : 0 < g) (hgr : g ∣ r) :
    ∑ d ∈ g.divisors,
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) =
      ((r / g : ℕ) : ℤ) * (g.totient : ℤ) := by
  calc
    ∑ d ∈ g.divisors,
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) =
        ∑ d ∈ g.divisors,
          ((r / g : ℕ) : ℤ) *
            (ArithmeticFunction.moebius d * (((g / d : ℕ) : ℤ))) := by
              apply Finset.sum_congr rfl
              intro d hd
              have hdg : d ∣ g := Nat.dvd_of_mem_divisors hd
              rw [← Nat.div_mul_div hgr hdg, Nat.cast_mul]
              ring
    _ = ((r / g : ℕ) : ℤ) *
        ∑ d ∈ g.divisors,
          ArithmeticFunction.moebius d * (((g / d : ℕ) : ℤ)) := by
            rw [Finset.mul_sum]
    _ = ((r / g : ℕ) : ℤ) * (g.totient : ℤ) := by
          rw [moebius_divisor_sum_eq_totient g hgpos]

private theorem mobiusNumeratorPolynomial_coeff_of_lt {r k : ℕ}
    (hr : 0 < r) (hk : k < r) :
    (mobiusNumeratorPolynomial r).coeff k = (gcdWordCoeff r k : ℤ) := by
  classical
  let g := r.gcd k
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left k hr
  have hgr : g ∣ r := Nat.gcd_dvd_left r k
  have hfilter : {d ∈ r.divisors | d ∣ k} = g.divisors := by
    ext d
    constructor
    · intro hd
      have hdr : d ∈ r.divisors := (Finset.mem_filter.mp hd).1
      have hdk : d ∣ k := (Finset.mem_filter.mp hd).2
      exact Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd (Nat.dvd_of_mem_divisors hdr) hdk, hgpos.ne'⟩
    · intro hd
      have hdg : d ∣ g := Nat.dvd_of_mem_divisors hd
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdg.trans hgr, hr.ne'⟩,
          hdg.trans (Nat.gcd_dvd_right r k)⟩
  rw [mobiusNumeratorPolynomial, Polynomial.finset_sum_coeff]
  calc
    ∑ d ∈ r.divisors,
        (Polynomial.C
          (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
            spacedRepunit d (r / d)).coeff k =
        ∑ d ∈ r.divisors,
          (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
            (if d ∣ k then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro d hd
              rw [Polynomial.coeff_C_mul,
                coeff_spacedRepunit_of_lt hr
                  (Nat.dvd_of_mem_divisors hd) hk]
    _ = ∑ d ∈ {d ∈ r.divisors | d ∣ k},
          ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro d _hd
            by_cases hdk : d ∣ k <;> simp [hdk]
    _ = ∑ d ∈ g.divisors,
          ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) := by
            rw [hfilter]
    _ = ((r / g : ℕ) : ℤ) * (g.totient : ℤ) :=
      scaled_moebius_divisor_sum_eq r g hgpos hgr
    _ = (gcdWordCoeff r k : ℤ) := by
      simp [gcdWordCoeff, g]

private theorem mobiusNumeratorPolynomial_coeff_eq_zero_of_le {r k : ℕ}
    (hr : 0 < r) (hk : r ≤ k) :
    (mobiusNumeratorPolynomial r).coeff k = 0 := by
  classical
  rw [mobiusNumeratorPolynomial, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro d hd
  rw [Polynomial.coeff_C_mul,
    coeff_spacedRepunit_eq_zero_of_le hr (Nat.dvd_of_mem_divisors hd) hk,
    mul_zero]

@[simp]
theorem gcdWord_coeff_of_lt {r k : ℕ} (hk : k < r) :
    (gcdWord r).coeff k = (gcdWordCoeff r k : ℤ) := by
  rw [gcdWord, Polynomial.ofFn_coeff_eq_val_of_lt _ hk]

@[simp]
theorem gcdWord_coeff_eq_zero_of_le {r k : ℕ} (hk : r ≤ k) :
    (gcdWord r).coeff k = 0 := by
  rw [gcdWord, Polynomial.ofFn_coeff_eq_zero_of_ge _ hk]

/-- T1: on the squarefree-positive stated boundary, the signed repunit
numerator is exactly the positive gcd word. -/
theorem mobiusNumeratorPolynomial_eq_gcdWord {r : ℕ} (hr : Squarefree r) :
    mobiusNumeratorPolynomial r = gcdWord r := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  ext k
  by_cases hk : k < r
  · rw [mobiusNumeratorPolynomial_coeff_of_lt hrpos hk,
      gcdWord_coeff_of_lt hk]
  · have hrk : r ≤ k := Nat.le_of_not_gt hk
    rw [mobiusNumeratorPolynomial_coeff_eq_zero_of_le hrpos hrk,
      gcdWord_coeff_eq_zero_of_le hrk]

/-- Coefficient form of T1, including the exact zero tail. -/
theorem mobiusNumeratorPolynomial_coeff {r k : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).coeff k =
      if k < r then (gcdWordCoeff r k : ℤ) else 0 := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  by_cases hk : k < r
  · rw [if_pos hk, mobiusNumeratorPolynomial_coeff_of_lt hrpos hk]
  · rw [if_neg hk, mobiusNumeratorPolynomial_coeff_eq_zero_of_le hrpos
      (Nat.le_of_not_gt hk)]

theorem gcdWordCoeff_pos {r k : ℕ} (hr : 0 < r) :
    0 < gcdWordCoeff r k := by
  have hgpos : 0 < r.gcd k := Nat.gcd_pos_of_pos_left k hr
  have hqpos : 0 < r / r.gcd k :=
    Nat.div_pos (Nat.gcd_le_left k hr) hgpos
  exact Nat.mul_pos hqpos (Nat.totient_pos.mpr hgpos)

/-- Every coefficient in the stated range is strictly positive. -/
theorem mobiusNumeratorPolynomial_coeff_pos {r k : ℕ}
    (hr : Squarefree r) (hk : k < r) :
    0 < (mobiusNumeratorPolynomial r).coeff k := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  rw [mobiusNumeratorPolynomial_coeff_of_lt hrpos hk]
  exact_mod_cast gcdWordCoeff_pos hrpos

/-- There are no negative coefficients; beyond degree `r - 1` they are
exactly zero. -/
theorem mobiusNumeratorPolynomial_coeff_nonneg {r k : ℕ}
    (hr : Squarefree r) :
    0 ≤ (mobiusNumeratorPolynomial r).coeff k := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  by_cases hk : k < r
  · exact (mobiusNumeratorPolynomial_coeff_pos hr hk).le
  · rw [mobiusNumeratorPolynomial_coeff_eq_zero_of_le hrpos
      (Nat.le_of_not_gt hk)]

private theorem eval_spacedRepunit_two {r d : ℕ}
    (hr : 0 < r) (hd : d ∣ r) :
    (spacedRepunit d (r / d)).eval 2 =
      (((RadicalMobiusShadow.mersenne r /
          RadicalMobiusShadow.mersenne d : ℕ) : ℤ)) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  have htwo : 2 ≤ 2 ^ d := by
    have := Nat.one_lt_two_pow hdpos.ne'
    omega
  have hp : (2 ^ d) ^ (r / d) = 2 ^ r := by
    rw [← pow_mul, Nat.mul_div_cancel' hd]
  have hnat :
      ∑ j ∈ Finset.range (r / d), 2 ^ (d * j) =
        RadicalMobiusShadow.mersenne r /
          RadicalMobiusShadow.mersenne d := by
    simp_rw [pow_mul]
    rw [Nat.geomSum_eq htwo, hp]
    rfl
  rw [spacedRepunit, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial, one_mul]
  exact_mod_cast hnat

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

theorem divisor_mobiusNumerator_eq_subset {r : ℕ}
    (hr : Squarefree r) :
    (∑ d ∈ r.divisors,
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) *
          (((RadicalMobiusShadow.mersenne r /
            RadicalMobiusShadow.mersenne d : ℕ) : ℤ))) =
      RadicalMobiusShadow.mobiusNumerator r := by
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

/-- The integral divisor expansion, normalized term-by-term as the rational
Möbius/Mersenne sum.  This is the finite identity needed to identify the
divisor residue channels with the explicit radical shadow. -/
theorem sum_divisors_moebius_ratio_eq_baseMobiusShadow {r : ℕ}
    (hr : Squarefree r) :
    (∑ d ∈ r.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℚ) * (r : ℚ) /
          ((d : ℚ) * (RadicalMobiusShadow.mersenne d : ℚ))) =
      RadicalMobiusShadow.baseMobiusShadow r := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  have hnum :
      (∑ d ∈ r.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) *
            ((r / d : ℕ) : ℚ) *
              ((RadicalMobiusShadow.mersenne r /
                RadicalMobiusShadow.mersenne d : ℕ) : ℚ)) =
        (RadicalMobiusShadow.mobiusNumerator r : ℚ) := by
    have hnumZ := congrArg (fun z : ℤ => (z : ℚ))
      (divisor_mobiusNumerator_eq_subset hr)
    push_cast at hnumZ
    convert hnumZ using 1 <;> simp
  rw [RadicalMobiusShadow.baseMobiusShadow, Rat.divInt_eq_div,
    ← hnum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hdmem
  have hdvd : d ∣ r := Nat.dvd_of_mem_divisors hdmem
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hrpos
  have hMdiv : RadicalMobiusShadow.mersenne d ∣
      RadicalMobiusShadow.mersenne r := by
    simpa [RadicalMobiusShadow.mersenne] using
      (Nat.pow_sub_one_dvd_pow_sub_one 2 hdvd)
  have hMdpos : 0 < RadicalMobiusShadow.mersenne d := by
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hdpos.ne')
  have hMrpos : 0 < RadicalMobiusShadow.mersenne r := by
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hrpos.ne')
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hMdQ : (RadicalMobiusShadow.mersenne d : ℚ) ≠ 0 := by
    exact_mod_cast hMdpos.ne'
  have hMrQ : (RadicalMobiusShadow.mersenne r : ℚ) ≠ 0 := by
    exact_mod_cast hMrpos.ne'
  rw [Nat.cast_div hdvd hdQ, Nat.cast_div hMdiv hMdQ]
  field_simp [hdQ, hMdQ, hMrQ]
  norm_cast

/-- The same divisor formula at an arbitrary positive scale.  The Möbius
coefficient kills every nonsquarefree divisor of `H`, so the remaining
divisor set is exactly the divisor set of `rad(H)`. -/
theorem sum_divisors_moebius_ratio_eq_scaledMobiusShadow
    (H : ℕ) (hH : 0 < H) :
    (∑ d ∈ H.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℚ) * (H : ℚ) /
          ((d : ℚ) * (RadicalMobiusShadow.mersenne d : ℚ))) =
      (H : ℚ) * RadicalMobiusShadow.numericMobiusShadow H := by
  let r := RadicalMobiusShadow.squarefreeKernel H
  have hrpos : 0 < r := RadicalMobiusShadow.squarefreeKernel_pos H
  have hrsf : Squarefree r :=
    RadicalMobiusShadow.squarefreeKernel_squarefree H
  have hrdvd : r ∣ H := RadicalMobiusShadow.squarefreeKernel_dvd H
  have hdivisors :
      H.divisors.filter Squarefree = r.divisors := by
    ext d
    constructor
    · intro hdmem
      have hdH := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdmem).1
      have hdsf := (Finset.mem_filter.mp hdmem).2
      have hpf : d.primeFactors ⊆ H.primeFactors :=
        Nat.primeFactors_mono hdH hH.ne'
      have hdker : d ∣ r := by
        calc
          d = d.primeFactors.prod id :=
            (Nat.prod_primeFactors_of_squarefree hdsf).symm
          _ ∣ H.primeFactors.prod id :=
            Finset.prod_dvd_prod_of_subset
              d.primeFactors H.primeFactors id hpf
          _ = r := by
            simp [r, RadicalMobiusShadow.squarefreeKernel]
      exact Nat.mem_divisors.mpr ⟨hdker, hrpos.ne'⟩
    · intro hdmem
      have hdr : d ∣ r := Nat.dvd_of_mem_divisors hdmem
      apply Finset.mem_filter.mpr
      exact ⟨Nat.mem_divisors.mpr ⟨hdr.trans hrdvd, hH.ne'⟩,
        hrsf.squarefree_of_dvd hdr⟩
  have hfilter :
      (∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) * (H : ℚ) /
            ((d : ℚ) * (RadicalMobiusShadow.mersenne d : ℚ))) =
        ∑ d ∈ H.divisors.filter Squarefree,
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) * (H : ℚ) /
            ((d : ℚ) * (RadicalMobiusShadow.mersenne d : ℚ)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hdH hdnot
    have hdsf : ¬ Squarefree d := by
      intro hsq
      exact hdnot (Finset.mem_filter.mpr ⟨hdH, hsq⟩)
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsf]
  have hHcast : (H : ℚ) = ((H / r : ℕ) : ℚ) * (r : ℚ) := by
    exact_mod_cast (Nat.div_mul_cancel hrdvd).symm
  calc
    (∑ d ∈ H.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℚ) * (H : ℚ) /
          ((d : ℚ) * (RadicalMobiusShadow.mersenne d : ℚ))) =
        ∑ d ∈ H.divisors.filter Squarefree,
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) * (H : ℚ) /
            ((d : ℚ) * (RadicalMobiusShadow.mersenne d : ℚ)) := hfilter
    _ = ∑ d ∈ r.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) * (H : ℚ) /
            ((d : ℚ) * (RadicalMobiusShadow.mersenne d : ℚ)) := by
      rw [hdivisors]
    _ = ((H / r : ℕ) : ℚ) *
          (∑ d ∈ r.divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℚ) * (r : ℚ) /
              ((d : ℚ) * (RadicalMobiusShadow.mersenne d : ℚ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [hHcast]
      ring
    _ = ((H / r : ℕ) : ℚ) *
          RadicalMobiusShadow.baseMobiusShadow r := by
      rw [sum_divisors_moebius_ratio_eq_baseMobiusShadow hrsf]
    _ = (H : ℚ) * RadicalMobiusShadow.numericMobiusShadow H := by
      simpa [r] using
        (RadicalMobiusShadow.scaledMobiusShadow_eq_radicalBase H hH).symm

/-- Evaluation at `X = 2` recovers the integral numerator already owned by
`RadicalMobiusShadow`.  The theorem deliberately retains the squarefree
boundary of T1. -/
theorem mobiusNumeratorPolynomial_eval_two {r : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      RadicalMobiusShadow.mobiusNumerator r := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  rw [mobiusNumeratorPolynomial, Polynomial.eval_finset_sum]
  calc
    ∑ d ∈ r.divisors,
        (Polynomial.C
          (ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ))) *
            spacedRepunit d (r / d)).eval 2 =
        ∑ d ∈ r.divisors,
          ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) *
            (((RadicalMobiusShadow.mersenne r /
              RadicalMobiusShadow.mersenne d : ℕ) : ℤ)) := by
                apply Finset.sum_congr rfl
                intro d hd
                rw [Polynomial.eval_C_mul,
                  eval_spacedRepunit_two hrpos
                    (Nat.dvd_of_mem_divisors hd)]
    _ = RadicalMobiusShadow.mobiusNumerator r :=
      divisor_mobiusNumerator_eq_subset hr

#print axioms mobiusNumeratorPolynomial_eq_gcdWord
#print axioms mobiusNumeratorPolynomial_coeff
#print axioms mobiusNumeratorPolynomial_coeff_pos
#print axioms mobiusNumeratorPolynomial_eval_two

end Erdos257PeriodNoncollapse.RepunitMobiusNumerator
