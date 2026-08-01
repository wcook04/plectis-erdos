import ErdosProblems.Erdos68.ChannelIntegralCongruence
import ErdosProblems.Erdos68.FactorialChannelCertificate
import ErdosProblems.Erdos68.FactorialZeroPlateau
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Erdős 68: weighted private-support projections

This module formalizes the deterministic CRT projection core for bounded
factorial-tail endpoint numerators.
-/

namespace ErdosProblems.Erdos68

/-- Every prime divisor of a factorial gap `n! - 1` is strictly larger than
the source index `n`.  This is the basic support separation behind the
collision-core construction. -/
theorem prime_dvd_factorial_sub_one_gt
    {p n : ℕ}
    (hp : p.Prime)
    (hdiv : p ∣ n.factorial - 1) :
    n < p := by
  by_contra hnp
  have hpn : p ≤ n := Nat.le_of_not_gt hnp
  have hpfac : p ∣ n.factorial :=
    Nat.dvd_factorial hp.pos hpn
  have hpone : p ∣ 1 := by
    have hsub := Nat.dvd_sub hpfac hdiv
    have hfacPos : 0 < n.factorial := Nat.factorial_pos n
    have hdiff : n.factorial - (n.factorial - 1) = 1 := by
      omega
    simpa [hdiff] using hsub
  exact hp.ne_one (Nat.dvd_one.mp hpone)

/-- Exact shared-support identity for two factorial gaps.  The previously
checked divisibility bound is sharpened here to equality: every common
factor is already visible in the intervening descending factorial minus
one, and conversely. -/
theorem gcd_factorial_sub_one_eq_descFactorial_sub_one
    {m n : ℕ}
    (hmn : m < n) :
    Nat.gcd (m.factorial - 1) (n.factorial - 1) =
      Nat.gcd (m.factorial - 1)
        (n.descFactorial (n - m) - 1) := by
  let q := n.descFactorial (n - m)
  have hk : n - m ≤ n := Nat.sub_le _ _
  have hfactorial :
      m.factorial * q = n.factorial := by
    have h := Nat.factorial_mul_descFactorial hk
    simpa [q, Nat.sub_sub_self (Nat.le_of_lt hmn)] using h
  have hqPos : 0 < q := by
    dsimp [q]
    exact Nat.descFactorial_pos.mpr hk
  have hqDvd : q ∣ n.factorial :=
    ⟨m.factorial, by simpa [Nat.mul_comm] using hfactorial.symm⟩
  have hqLe : q ≤ n.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos n) hqDvd
  have hdecomp :
      n.factorial - 1 =
        (q - 1) + (m.factorial - 1) * q := by
    rw [Nat.sub_mul, one_mul, hfactorial]
    omega
  rw [hdecomp]
  exact Nat.gcd_add_mul_left_right
    (m.factorial - 1) (q - 1) q

/-- If a collision core contains the full gcd of two denominators, then
removing from each denominator the part visible in that core leaves coprime
quotients.  The proof factors both residual quotients through the standard
coprime pair obtained by dividing by their common gcd. -/
theorem privateQuotients_coprime_of_gcd_dvd_core
    {a b C : ℕ}
    (hgPos : 0 < Nat.gcd a b)
    (hcollision : Nat.gcd a b ∣ C) :
    Nat.Coprime
      (a / Nat.gcd a C)
      (b / Nat.gcd b C) := by
  have hga : Nat.gcd a b ∣ Nat.gcd a C :=
    Nat.dvd_gcd (Nat.gcd_dvd_left a b) hcollision
  have hgb : Nat.gcd a b ∣ Nat.gcd b C :=
    Nat.dvd_gcd (Nat.gcd_dvd_right a b) hcollision
  have haDiv :
      a / Nat.gcd a C ∣ a / Nat.gcd a b :=
    Nat.div_dvd_div_left (Nat.gcd_dvd_left a C) hga
  have hbDiv :
      b / Nat.gcd b C ∣ b / Nat.gcd a b :=
    Nat.div_dvd_div_left (Nat.gcd_dvd_left b C) hgb
  exact Nat.Coprime.of_dvd haDiv hbDiv
    (Nat.coprime_div_gcd_div_gcd hgPos)

/-- Factorial-gap specialization of the collision-core quotient theorem.
Any core containing the pairwise gcd makes the two corresponding private
quotients coprime. -/
theorem factorialGap_privateQuotients_coprime_of_collision
    {m n C : ℕ}
    (hm : 2 ≤ m)
    (hcollision :
      Nat.gcd (m.factorial - 1) (n.factorial - 1) ∣ C) :
    Nat.Coprime
      ((m.factorial - 1) /
        Nat.gcd (m.factorial - 1) C)
      ((n.factorial - 1) /
        Nat.gcd (n.factorial - 1) C) := by
  have hmfac : 1 < m.factorial :=
    (Nat.one_lt_factorial).2 hm
  have hgapPos : 0 < m.factorial - 1 :=
    Nat.sub_pos_of_lt hmfac
  exact privateQuotients_coprime_of_gcd_dvd_core
    (Nat.gcd_pos_of_pos_left _ hgapPos) hcollision

/-- Lcm of all off-diagonal pairwise gcds in a finite denominator family.
Each index is omitted from its own inner lcm, so diagonal terms do not erase
the private support. -/
def pairwiseCollisionCore
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.lcm fun i =>
    (s.erase i).lcm fun j => Nat.gcd (d i) (d j)

/-- The collision core used by the endpoint decomposition also contains a
distinguished base denominator. -/
def collisionCore
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (pairwiseCollisionCore s d)

/-- Common denominator for the distinguished base and the finite
denominator family. -/
def endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (s.lcm d)

/-- Numerator of the reciprocal tail after placing every denominator over
the common endpoint lcm. -/
def endpointTailNumerator
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.sum fun i => endpointDenominatorLcm base s d / d i

/-- Positive base contribution to the displayed endpoint numerator over
the full common denominator. -/
def endpointBaseNumerator
    {ι : Type*} [DecidableEq ι]
    (K base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  K * (endpointDenominatorLcm base s d / base)

/-- Displayed natural endpoint numerator.  The intended endpoint
application supplies the inequality making this truncated subtraction an
ordinary positive difference. -/
def endpointNumerator
    {ι : Type*} [DecidableEq ι]
    (K base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  endpointBaseNumerator K base s d -
    endpointTailNumerator base s d

/-- Positivity of every displayed denominator makes the full endpoint lcm
strictly positive. -/
theorem endpointDenominatorLcm_pos
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    0 < endpointDenominatorLcm base s d := by
  unfold endpointDenominatorLcm
  apply Nat.pos_of_ne_zero
  exact Nat.lcm_ne_zero hbase.ne'
    ((Finset.lcm_ne_zero_iff).2 fun i hi => (hpos i hi).ne')

/-- Every displayed denominator divides the full endpoint lcm. -/
theorem endpointDenominator_dvd_endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {i : ι}
    (hi : i ∈ s) :
    d i ∣ endpointDenominatorLcm base s d := by
  exact (Finset.dvd_lcm hi).trans
    (Nat.dvd_lcm_right base (s.lcm d))

/-- Clearing the full endpoint lcm and then dividing back recovers the
literal reciprocal sum. -/
theorem endpointTailNumerator_div_endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    (endpointTailNumerator base s d : ℚ) /
        endpointDenominatorLcm base s d =
      ∑ i ∈ s, 1 / (d i : ℚ) := by
  have hLpos :=
    endpointDenominatorLcm_pos hbase hpos
  have hLne :
      (endpointDenominatorLcm base s d : ℚ) ≠ 0 := by
    exact_mod_cast hLpos.ne'
  unfold endpointTailNumerator
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_div_charZero
    (endpointDenominator_dvd_endpointDenominatorLcm hi)]
  have hdne : (d i : ℚ) ≠ 0 := by
    exact_mod_cast (hpos i hi).ne'
  field_simp

/-- The distinguished contribution has the same exact common-denominator
interpretation. -/
theorem endpointBaseNumerator_div_endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    (endpointBaseNumerator K base s d : ℚ) /
        endpointDenominatorLcm base s d =
      (K : ℚ) / base := by
  have hLpos :=
    endpointDenominatorLcm_pos hbase hpos
  have hLne :
      (endpointDenominatorLcm base s d : ℚ) ≠ 0 := by
    exact_mod_cast hLpos.ne'
  have hbaseNe : (base : ℚ) ≠ 0 := by
    exact_mod_cast hbase.ne'
  have hLcmNe :
      (Nat.lcm base (s.lcm d) : ℚ) ≠ 0 := by
    simpa [endpointDenominatorLcm] using hLne
  unfold endpointBaseNumerator endpointDenominatorLcm
  rw [Nat.cast_mul, Nat.cast_div_charZero
    (Nat.dvd_lcm_left base (s.lcm d))]
  field_simp

/-- Nonnegativity of the rational endpoint gap is exactly the side
condition that makes the displayed natural subtraction ordinary. -/
theorem endpointTailNumerator_le_endpointBaseNumerator_of_gap_nonneg
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (hgap :
      0 ≤ (K : ℚ) / base - ∑ i ∈ s, 1 / (d i : ℚ)) :
    endpointTailNumerator base s d ≤
      endpointBaseNumerator K base s d := by
  have hLpos :=
    endpointDenominatorLcm_pos hbase hpos
  have hLposQ :
      (0 : ℚ) < endpointDenominatorLcm base s d := by
    exact_mod_cast hLpos
  have hfrac :
      (endpointTailNumerator base s d : ℚ) /
          endpointDenominatorLcm base s d ≤
        (endpointBaseNumerator K base s d : ℚ) /
          endpointDenominatorLcm base s d := by
    rw [
      endpointTailNumerator_div_endpointDenominatorLcm hbase hpos,
      endpointBaseNumerator_div_endpointDenominatorLcm hbase hpos
    ]
    linarith
  rw [div_le_div_iff_of_pos_right hLposQ] at hfrac
  exact_mod_cast hfrac

/-- Under the ordinary-subtraction side condition, the displayed natural
endpoint numerator divided by its lcm is exactly the rational endpoint
gap. -/
theorem endpointNumerator_div_endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d) :
    (endpointNumerator K base s d : ℚ) /
        endpointDenominatorLcm base s d =
      (K : ℚ) / base - ∑ i ∈ s, 1 / (d i : ℚ) := by
  calc
    (endpointNumerator K base s d : ℚ) /
          endpointDenominatorLcm base s d =
        ((endpointBaseNumerator K base s d : ℚ) -
          (endpointTailNumerator base s d : ℚ)) /
            endpointDenominatorLcm base s d := by
              rw [endpointNumerator, Nat.cast_sub htail]
    _ =
        (endpointBaseNumerator K base s d : ℚ) /
            endpointDenominatorLcm base s d -
          (endpointTailNumerator base s d : ℚ) /
            endpointDenominatorLcm base s d := by ring
    _ = (K : ℚ) / base - ∑ i ∈ s, 1 / (d i : ℚ) := by
      rw [
        endpointBaseNumerator_div_endpointDenominatorLcm hbase hpos,
        endpointTailNumerator_div_endpointDenominatorLcm hbase hpos
      ]

/-- The pairwise collision core of a positive denominator family is
positive, including for the empty family where the finite lcm is `1`. -/
theorem pairwiseCollisionCore_pos
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ}
    (hpos : ∀ i ∈ s, 0 < d i) :
    0 < pairwiseCollisionCore s d := by
  apply Nat.pos_of_ne_zero
  apply (Finset.lcm_ne_zero_iff).2
  intro i hi
  apply (Finset.lcm_ne_zero_iff).2
  intro j _
  exact (Nat.gcd_pos_of_pos_left (d j) (hpos i hi)).ne'

/-- If every member of a positive finite family has `q`-valuation below
`e`, then so does their least common multiple. -/
theorem finset_lcm_factorization_lt_of_all_lt
    {α : Type*} {s : Finset α} {f : α → ℕ} {q e : ℕ}
    (he : 0 < e)
    (hpos : ∀ x ∈ s, 0 < f x)
    (hlt : ∀ x ∈ s, (f x).factorization q < e) :
    (s.lcm f).factorization q < e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using he
  | @insert a s ha ih =>
      have haPos :
          0 < f a :=
        hpos a (Finset.mem_insert_self a s)
      have hsPos :
          ∀ x ∈ s, 0 < f x := by
        intro x hx
        exact hpos x (Finset.mem_insert_of_mem hx)
      have hsLt :
          ∀ x ∈ s, (f x).factorization q < e := by
        intro x hx
        exact hlt x (Finset.mem_insert_of_mem hx)
      have hlcmNe :
          s.lcm f ≠ 0 :=
        (Finset.lcm_ne_zero_iff).2 fun x hx => (hsPos x hx).ne'
      rw [Finset.lcm_insert]
      change
        (Nat.lcm (f a) (s.lcm f)).factorization q < e
      rw [Nat.factorization_lcm haPos.ne' hlcmNe]
      change
        max ((f a).factorization q)
            ((s.lcm f).factorization q) < e
      exact max_lt
        (hlt a (Finset.mem_insert_self a s))
        (ih hsPos hsLt)

/-- Adjoining a positive distinguished base keeps the full collision core
positive. -/
theorem collisionCore_pos
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    0 < collisionCore base s d := by
  exact Nat.pos_of_ne_zero
    (Nat.lcm_ne_zero hbase.ne' (pairwiseCollisionCore_pos hpos).ne')

/-- Every pairwise collision factor already occurs in the lcm of the
denominator family. -/
theorem pairwiseCollisionCore_dvd_denominatorLcm
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ} :
    pairwiseCollisionCore s d ∣ s.lcm d := by
  unfold pairwiseCollisionCore
  apply Finset.lcm_dvd
  intro i hi
  apply Finset.lcm_dvd
  intro j _
  exact (Nat.gcd_dvd_left (d i) (d j)).trans
    (Finset.dvd_lcm hi)

/-- The full collision core divides the common endpoint denominator. -/
theorem collisionCore_dvd_endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ} :
    collisionCore base s d ∣ endpointDenominatorLcm base s d := by
  unfold collisionCore endpointDenominatorLcm
  apply Nat.lcm_dvd
  · exact Nat.dvd_lcm_left base (s.lcm d)
  · exact (pairwiseCollisionCore_dvd_denominatorLcm
      (s := s) (d := d)).trans
        (Nat.dvd_lcm_right base (s.lcm d))

/-- Every off-diagonal pairwise gcd divides the finite pairwise collision
core. -/
theorem gcd_dvd_pairwiseCollisionCore
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ}
    {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    Nat.gcd (d i) (d j) ∣ pairwiseCollisionCore s d := by
  have hjErase : j ∈ s.erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hinner :
      Nat.gcd (d i) (d j) ∣
        (s.erase i).lcm fun k => Nat.gcd (d i) (d k) :=
    Finset.dvd_lcm hjErase
  exact hinner.trans (Finset.dvd_lcm hi)

/-- Binary distributivity underlying the incremental collision recurrence:
the lcm of the parts of two positive denominators shared with `a` is the
part of their lcm shared with `a`. -/
theorem lcm_gcd_left_distrib
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Nat.lcm (Nat.gcd a b) (Nat.gcd a c) =
      Nat.gcd a (Nat.lcm b c) := by
  have hab : 0 < Nat.gcd a b :=
    Nat.gcd_pos_of_pos_left b ha
  have hac : 0 < Nat.gcd a c :=
    Nat.gcd_pos_of_pos_left c ha
  have hbc : 0 < Nat.lcm b c :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hb.ne' hc.ne')
  have hlhs :
      0 < Nat.lcm (Nat.gcd a b) (Nat.gcd a c) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hab.ne' hac.ne')
  have hrhs :
      0 < Nat.gcd a (Nat.lcm b c) :=
    Nat.gcd_pos_of_pos_left (Nat.lcm b c) ha
  apply Nat.eq_of_factorization_eq hlhs.ne' hrhs.ne'
  intro p
  rw [
    Nat.factorization_lcm hab.ne' hac.ne',
    Nat.factorization_gcd ha.ne' hb.ne',
    Nat.factorization_gcd ha.ne' hc.ne',
    Nat.factorization_gcd ha.ne' hbc.ne',
    Nat.factorization_lcm hb.ne' hc.ne'
  ]
  simp only [Finsupp.sup_apply, Finsupp.inf_apply]
  exact (min_max_distrib_left _ _ _).symm

/-- Finite-family form of `lcm_gcd_left_distrib`.  All collisions of one
positive denominator with a positive finite family collapse exactly to its
gcd with the family lcm. -/
theorem finset_lcm_gcd_left
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ℕ} {d : ι → ℕ}
    (ha : 0 < a)
    (hpos : ∀ i ∈ s, 0 < d i) :
    s.lcm (fun i => Nat.gcd a (d i)) =
      Nat.gcd a (s.lcm d) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.lcm_insert, Finset.lcm_insert]
      rw [ih (fun j hj =>
        hpos j (Finset.mem_insert_of_mem hj))]
      apply lcm_gcd_left_distrib ha
      · exact hpos i (Finset.mem_insert_self i s)
      · exact Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff).2
          (fun j hj =>
            (hpos j (Finset.mem_insert_of_mem hj)).ne'))

/-- Adjoining one denominator updates the pairwise collision core by the
lcm of the old core and the new denominator's collisions with the old
family.  This is the exact finite-family recurrence used by the incremental
Erdős 68 collision scan; it replaces a quadratic rescan by one new lcm. -/
theorem pairwiseCollisionCore_insert
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ} {a : ι}
    (ha : a ∉ s) :
    pairwiseCollisionCore (insert a s) d =
      Nat.lcm
        (pairwiseCollisionCore s d)
        (s.lcm fun j => Nat.gcd (d a) (d j)) := by
  apply Nat.dvd_antisymm
  · unfold pairwiseCollisionCore
    apply Finset.lcm_dvd
    intro i hi
    apply Finset.lcm_dvd
    intro j hj
    have hjData := Finset.mem_erase.mp hj
    by_cases hia : i = a
    · subst i
      have hjS : j ∈ s := by
        rcases Finset.mem_insert.mp hjData.2 with hja | hjs
        · exact False.elim (hjData.1 hja)
        · exact hjs
      exact (Finset.dvd_lcm hjS).trans
        (Nat.dvd_lcm_right _ _)
    · have hiS : i ∈ s := by
        rcases Finset.mem_insert.mp hi with hia' | his
        · exact False.elim (hia hia')
        · exact his
      by_cases hja : j = a
      · subst j
        have hcross :
            Nat.gcd (d i) (d a) ∣
              s.lcm fun k => Nat.gcd (d a) (d k) := by
          simpa [Nat.gcd_comm] using
            (Finset.dvd_lcm hiS :
              Nat.gcd (d a) (d i) ∣
                s.lcm fun k => Nat.gcd (d a) (d k))
        exact hcross.trans (Nat.dvd_lcm_right _ _)
      · have hjS : j ∈ s := by
          rcases Finset.mem_insert.mp hjData.2 with hja' | hjs
          · exact False.elim (hja hja')
          · exact hjs
        exact
          (gcd_dvd_pairwiseCollisionCore
            hiS hjS hjData.1.symm).trans
              (Nat.dvd_lcm_left _ _)
  · apply Nat.lcm_dvd
    · unfold pairwiseCollisionCore
      apply Finset.lcm_dvd
      intro i hi
      apply Finset.lcm_dvd
      intro j hj
      have hjData := Finset.mem_erase.mp hj
      exact gcd_dvd_pairwiseCollisionCore
        (Finset.mem_insert_of_mem hi)
        (Finset.mem_insert_of_mem hjData.2)
        hjData.1.symm
    · apply Finset.lcm_dvd
      intro j hj
      have haj : a ≠ j := by
        intro h
        subst j
        exact ha hj
      exact gcd_dvd_pairwiseCollisionCore
        (Finset.mem_insert_self a s)
        (Finset.mem_insert_of_mem hj)
        haj

/-- Sharpened one-step collision recurrence.  For positive denominators,
the entire new collision inflow is the single repeated part
`gcd (d a) (s.lcm d)`, so no pairwise rescan remains. -/
theorem pairwiseCollisionCore_insert_gcd_lcm
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ} {a : ι}
    (ha : a ∉ s)
    (hda : 0 < d a)
    (hpos : ∀ i ∈ s, 0 < d i) :
    pairwiseCollisionCore (insert a s) d =
      Nat.lcm
        (pairwiseCollisionCore s d)
        (Nat.gcd (d a) (s.lcm d)) := by
  rw [pairwiseCollisionCore_insert ha,
    finset_lcm_gcd_left hda hpos]

/-- The same one-step recurrence after adjoining the distinguished base.
This is the form consumed by the literal factorial-block collision core. -/
theorem collisionCore_insert
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ} {a : ι}
    (ha : a ∉ s) :
    collisionCore base (insert a s) d =
      Nat.lcm
        (collisionCore base s d)
        (s.lcm fun j => Nat.gcd (d a) (d j)) := by
  unfold collisionCore
  rw [pairwiseCollisionCore_insert ha]
  ac_rfl

/-- Positive-denominator sharpening of `collisionCore_insert`: the new
full-core inflow is exactly the gcd of the added denominator with the
previous denominator lcm. -/
theorem collisionCore_insert_gcd_lcm
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ} {a : ι}
    (ha : a ∉ s)
    (hda : 0 < d a)
    (hpos : ∀ i ∈ s, 0 < d i) :
    collisionCore base (insert a s) d =
      Nat.lcm
        (collisionCore base s d)
        (Nat.gcd (d a) (s.lcm d)) := by
  rw [collisionCore_insert ha,
    finset_lcm_gcd_left hda hpos]

/-- The repeated-support core and the denominator lcm together divide the
full denominator product.  Primewise, their exponents are respectively the
second-largest and largest displayed valuations, whose sum is bounded by
the total valuation.  The insertion proof exposes the same fact directly
through the exact gcd-with-prior-lcm recurrence. -/
theorem pairwiseCollisionCore_mul_denominatorLcm_dvd_denominatorProd
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ}
    (hpos : ∀ i ∈ s, 0 < d i) :
    pairwiseCollisionCore s d * s.lcm d ∣ s.prod d := by
  induction s using Finset.induction_on with
  | empty =>
      simp [pairwiseCollisionCore]
  | @insert a s ha ih =>
      have hda : 0 < d a :=
        hpos a (Finset.mem_insert_self a s)
      have hspos : ∀ i ∈ s, 0 < d i := fun i hi =>
        hpos i (Finset.mem_insert_of_mem hi)
      have hCpos : 0 < pairwiseCollisionCore s d :=
        pairwiseCollisionCore_pos hspos
      have hLpos : 0 < s.lcm d :=
        Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff).2
          (fun i hi => (hspos i hi).ne'))
      have hPpos : 0 < s.prod d :=
        Finset.prod_pos fun i hi => hspos i hi
      have hGpos : 0 < Nat.gcd (d a) (s.lcm d) :=
        Nat.gcd_pos_of_pos_left (s.lcm d) hda
      have hCnewPos :
          0 < Nat.lcm (pairwiseCollisionCore s d)
            (Nat.gcd (d a) (s.lcm d)) :=
        Nat.pos_of_ne_zero
          (Nat.lcm_ne_zero hCpos.ne' hGpos.ne')
      have hLnewPos : 0 < Nat.lcm (d a) (s.lcm d) :=
        Nat.pos_of_ne_zero
          (Nat.lcm_ne_zero hda.ne' hLpos.ne')
      rw [pairwiseCollisionCore_insert_gcd_lcm ha hda hspos,
        Finset.lcm_insert, Finset.prod_insert ha]
      apply (Nat.factorization_le_iff_dvd
        (Nat.mul_ne_zero hCnewPos.ne' hLnewPos.ne')
        (Nat.mul_ne_zero hda.ne' hPpos.ne')).1
      intro q
      have hihFac :=
        (Nat.factorization_le_iff_dvd
          (Nat.mul_ne_zero hCpos.ne' hLpos.ne')
          hPpos.ne').2 (ih hspos)
      have hcoreDvd :
          pairwiseCollisionCore s d ∣ s.lcm d :=
        pairwiseCollisionCore_dvd_denominatorLcm
      have hcoreFac :=
        (Nat.factorization_le_iff_dvd
          hCpos.ne' hLpos.ne').2 hcoreDvd
      rw [
        Nat.factorization_mul hCnewPos.ne' hLnewPos.ne',
        Nat.factorization_mul hda.ne' hPpos.ne',
        Nat.factorization_lcm hCpos.ne' hGpos.ne',
        Nat.factorization_gcd hda.ne' hLpos.ne',
        Nat.factorization_lcm hda.ne' hLpos.ne'
      ]
      simp only [
        Finsupp.add_apply,
        Finsupp.sup_apply,
        Finsupp.inf_apply
      ]
      have hihQ := hihFac q
      rw [Nat.factorization_mul hCpos.ne' hLpos.ne'] at hihQ
      simp only [Finsupp.add_apply] at hihQ
      have hcoreQ := hcoreFac q
      by_cases hAL :
          (d a).factorization q ≤
            (s.lcm d).factorization q
      · rw [max_eq_right hAL, min_eq_left hAL]
        omega
      · have hLA :
            (s.lcm d).factorization q ≤
              (d a).factorization q :=
          le_of_not_ge hAL
        rw [max_eq_left hLA, min_eq_right hLA]
        omega

/-- Cancelling a positive distinguished base from the full collision core
leaves a divisor of the pairwise collision core. -/
theorem collisionCore_div_base_dvd_pairwiseCollisionCore
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base) :
    collisionCore base s d / base ∣
      pairwiseCollisionCore s d := by
  unfold collisionCore
  rw [Nat.lcm_eq_mul_div,
    Nat.mul_div_assoc base
      (Nat.gcd_dvd_right base (pairwiseCollisionCore s d)),
    Nat.mul_div_cancel_left _ hbase]
  exact Nat.div_dvd_of_dvd
    (Nat.gcd_dvd_right base (pairwiseCollisionCore s d))

/-- Exact form of base cancellation in the collision core.  Normalization
removes precisely the part of the pairwise repeated-support core already
visible in the distinguished base, rather than merely producing an
unspecified divisor of that core. -/
theorem collisionCore_div_base_eq_pairwiseCollisionCore_div_gcd
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base) :
    collisionCore base s d / base =
      pairwiseCollisionCore s d /
        Nat.gcd base (pairwiseCollisionCore s d) := by
  let C := pairwiseCollisionCore s d
  have hgPos : 0 < Nat.gcd base C :=
    Nat.gcd_pos_of_pos_left C hbase
  have hgDvdC : Nat.gcd base C ∣ C :=
    Nat.gcd_dvd_right base C
  have hC :
      Nat.gcd base C * (C / Nat.gcd base C) = C :=
    Nat.mul_div_cancel' hgDvdC
  have hbaseC :
      base * C =
        base * (Nat.gcd base C * (C / Nat.gcd base C)) :=
    congrArg (fun x => base * x) hC.symm
  have hlcmEq :
      Nat.lcm base C =
        base * (C / Nat.gcd base C) := by
    apply Nat.eq_of_mul_eq_mul_left hgPos
    calc
      Nat.gcd base C * Nat.lcm base C = base * C :=
        Nat.gcd_mul_lcm base C
      _ = base * (Nat.gcd base C * (C / Nat.gcd base C)) :=
        hbaseC
      _ = Nat.gcd base C * (base * (C / Nat.gcd base C)) := by
        ac_rfl
  unfold collisionCore
  change Nat.lcm base C / base = C / Nat.gcd base C
  apply
    (Nat.div_eq_iff_eq_mul_left hbase
      (Nat.dvd_lcm_left base C)).2
  rw [hlcmEq]
  ac_rfl

/-- Primewise form of exact base cancellation.  The normalized collision
valuation is the repeated-support valuation in the denominator family
minus the valuation already absorbed by the distinguished base. -/
theorem collisionCore_div_base_factorization
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ} {q : ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    (collisionCore base s d / base).factorization q =
      (pairwiseCollisionCore s d).factorization q -
        base.factorization q := by
  have hpairPos : 0 < pairwiseCollisionCore s d :=
    pairwiseCollisionCore_pos hpos
  rw [collisionCore_div_base_eq_pairwiseCollisionCore_div_gcd hbase]
  rw [Nat.factorization_div (Nat.gcd_dvd_right _ _)]
  rw [Nat.factorization_gcd hbase.ne' hpairPos.ne']
  change
    (pairwiseCollisionCore s d).factorization q -
          min (base.factorization q)
            ((pairwiseCollisionCore s d).factorization q) =
      (pairwiseCollisionCore s d).factorization q -
        base.factorization q
  omega

/-- A prime power survives base normalization exactly when the pairwise
collision core contains that power on top of the complete base valuation.
This turns normalized collision mass into a higher-power repeated-hit
condition. -/
theorem primePower_dvd_collisionCore_div_base_iff
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    q ^ e ∣ collisionCore base s d / base ↔
      q ^ (e + base.factorization q) ∣
        pairwiseCollisionCore s d := by
  have hpairPos : 0 < pairwiseCollisionCore s d :=
    pairwiseCollisionCore_pos hpos
  have hgPos :
      0 < Nat.gcd base (pairwiseCollisionCore s d) :=
    Nat.gcd_pos_of_pos_left _ hbase
  have hgLe :
      Nat.gcd base (pairwiseCollisionCore s d) ≤
        pairwiseCollisionCore s d :=
    Nat.le_of_dvd hpairPos
      (Nat.gcd_dvd_right base (pairwiseCollisionCore s d))
  have hnormPos :
      0 < collisionCore base s d / base := by
    rw [collisionCore_div_base_eq_pairwiseCollisionCore_div_gcd hbase]
    exact Nat.div_pos hgLe hgPos
  rw [
    hq.pow_dvd_iff_le_factorization hnormPos.ne',
    hq.pow_dvd_iff_le_factorization hpairPos.ne',
    collisionCore_div_base_factorization hbase hpos
  ]
  omega

/-- Product/lcm control in the normalized endpoint form: after cancelling
the distinguished base, the remaining collision core times the denominator
lcm divides the literal denominator product.  This is the interface for
combining factorial-gap lcm estimates with collision-cap bounds. -/
theorem collisionCore_div_base_mul_denominatorLcm_dvd_denominatorProd
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    (collisionCore base s d / base) * s.lcm d ∣
      s.prod d := by
  exact
    (Nat.mul_dvd_mul_right
      (collisionCore_div_base_dvd_pairwiseCollisionCore
        (base := base) (s := s) (d := d) hbase)
      (s.lcm d)).trans
        (pairwiseCollisionCore_mul_denominatorLcm_dvd_denominatorProd
          hpos)

/-- Every positive prime power visible in the pairwise collision core is
visible to full multiplicity in two distinct denominators.  This is the
valuation-sensitive converse to `gcd_dvd_pairwiseCollisionCore` and is the
interface needed by prime-power hit-count estimates. -/
theorem exists_pairwise_primePower_support_of_dvd_pairwiseCollisionCore
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ}
    {q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpos : ∀ i ∈ s, 0 < d i)
    (hpow : q ^ e ∣ pairwiseCollisionCore s d) :
    ∃ i ∈ s, ∃ j ∈ s,
      i ≠ j ∧ q ^ e ∣ d i ∧ q ^ e ∣ d j := by
  by_contra hnone
  push Not at hnone
  have hpairLt :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        (d i).factorization q < e ∨
          (d j).factorization q < e := by
    intro i hi j hj hij
    by_contra hnot
    push Not at hnot
    exact hnone i hi j hj hij
      ((hq.pow_dvd_iff_le_factorization (hpos i hi).ne').2 hnot.1)
      ((hq.pow_dvd_iff_le_factorization (hpos j hj).ne').2 hnot.2)
  have hinnerPos :
      ∀ i ∈ s, 0 <
        (s.erase i).lcm fun j => Nat.gcd (d i) (d j) := by
    intro i hi
    apply Nat.pos_of_ne_zero
    apply (Finset.lcm_ne_zero_iff).2
    intro j hj
    exact (Nat.gcd_pos_of_pos_left (d j) (hpos i hi)).ne'
  have hinnerLt :
      ∀ i ∈ s,
        ((s.erase i).lcm fun j =>
          Nat.gcd (d i) (d j)).factorization q < e := by
    intro i hi
    apply finset_lcm_factorization_lt_of_all_lt he
    · intro j hj
      exact Nat.gcd_pos_of_pos_left (d j) (hpos i hi)
    · intro j hj
      have hjData := Finset.mem_erase.mp hj
      rw [Nat.factorization_gcd
        (hpos i hi).ne' (hpos j hjData.2).ne']
      change
        min ((d i).factorization q)
            ((d j).factorization q) < e
      rcases hpairLt i hi j hjData.2 hjData.1.symm with hiLt | hjLt
      · exact lt_of_le_of_lt (min_le_left _ _) hiLt
      · exact lt_of_le_of_lt (min_le_right _ _) hjLt
  have hcoreLt :
      (pairwiseCollisionCore s d).factorization q < e := by
    unfold pairwiseCollisionCore
    exact finset_lcm_factorization_lt_of_all_lt
      he hinnerPos hinnerLt
  have hcoreNe :
      pairwiseCollisionCore s d ≠ 0 :=
    (pairwiseCollisionCore_pos hpos).ne'
  have hle :
      e ≤ (pairwiseCollisionCore s d).factorization q :=
    (hq.pow_dvd_iff_le_factorization hcoreNe).1 hpow
  omega

/-- Prime-power divisibility of the pairwise collision core is exactly
repeated full-power support in the denominator family. -/
theorem primePower_dvd_pairwiseCollisionCore_iff
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ}
    {q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpos : ∀ i ∈ s, 0 < d i) :
    q ^ e ∣ pairwiseCollisionCore s d ↔
      ∃ i ∈ s, ∃ j ∈ s,
        i ≠ j ∧ q ^ e ∣ d i ∧ q ^ e ∣ d j := by
  constructor
  · exact
      exists_pairwise_primePower_support_of_dvd_pairwiseCollisionCore
        hq he hpos
  · rintro ⟨i, hi, j, hj, hij, hiPow, hjPow⟩
    exact (Nat.dvd_gcd hiPow hjPow).trans
      (gcd_dvd_pairwiseCollisionCore hi hj hij)

/-- Every off-diagonal pairwise gcd also divides the full collision core
after adjoining the distinguished base denominator. -/
theorem gcd_dvd_collisionCore
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    Nat.gcd (d i) (d j) ∣ collisionCore base s d := by
  exact Nat.dvd_lcm_of_dvd_right
    (gcd_dvd_pairwiseCollisionCore hi hj hij) base

/-- Away from the distinguished base, every prime power in the full
collision core comes from two full-multiplicity denominator hits. -/
theorem exists_pairwise_primePower_support_of_dvd_collisionCore
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (hpowBase : ¬q ^ e ∣ base)
    (hpow : q ^ e ∣ collisionCore base s d) :
    ∃ i ∈ s, ∃ j ∈ s,
      i ≠ j ∧ q ^ e ∣ d i ∧ q ^ e ∣ d j := by
  have hbaseLt :
      base.factorization q < e := by
    by_contra hnot
    exact hpowBase
      ((hq.pow_dvd_iff_le_factorization hbase.ne').2
        (Nat.le_of_not_gt hnot))
  have hpairPos :
      0 < pairwiseCollisionCore s d :=
    pairwiseCollisionCore_pos hpos
  have hcoreFac :
      e ≤ (collisionCore base s d).factorization q :=
    (hq.pow_dvd_iff_le_factorization
      (collisionCore_pos hbase hpos).ne').1 hpow
  unfold collisionCore at hcoreFac
  rw [Nat.factorization_lcm hbase.ne' hpairPos.ne'] at hcoreFac
  change
    e ≤ max (base.factorization q)
      ((pairwiseCollisionCore s d).factorization q) at hcoreFac
  have hpairFac :
      e ≤ (pairwiseCollisionCore s d).factorization q := by
    omega
  exact
    exists_pairwise_primePower_support_of_dvd_pairwiseCollisionCore
      hq he hpos
      ((hq.pow_dvd_iff_le_factorization hpairPos.ne').2 hpairFac)

/-- If the distinguished base omits `q^e`, full collision-core support is
equivalent to two distinct full-power denominator hits. -/
theorem primePower_dvd_collisionCore_iff
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (hpowBase : ¬q ^ e ∣ base) :
    q ^ e ∣ collisionCore base s d ↔
      ∃ i ∈ s, ∃ j ∈ s,
        i ≠ j ∧ q ^ e ∣ d i ∧ q ^ e ∣ d j := by
  constructor
  · exact
      exists_pairwise_primePower_support_of_dvd_collisionCore
        hq he hbase hpos hpowBase
  · rintro ⟨i, hi, j, hj, hij, hiPow, hjPow⟩
    exact (Nat.dvd_gcd hiPow hjPow).trans
      (gcd_dvd_collisionCore hi hj hij)

/-- A prime occurring in at most one displayed denominator cannot enter the
pairwise collision core. -/
theorem prime_not_dvd_pairwiseCollisionCore_of_unique_support
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ}
    {q : ℕ} {i : ι}
    (hq : q.Prime)
    (hunique :
      ∀ j ∈ s, j ≠ i → ¬q ∣ d j) :
    ¬q ∣ pairwiseCollisionCore s d := by
  intro hqCore
  have hqOuterProduct :
      q ∣ s.prod fun j =>
        (s.erase j).lcm fun k => Nat.gcd (d j) (d k) :=
    hqCore.trans
      (Finset.lcm_dvd_prod s fun j =>
        (s.erase j).lcm fun k => Nat.gcd (d j) (d k))
  obtain ⟨j, hj, hqInner⟩ :=
    (hq.prime.dvd_finset_prod_iff
      (fun j =>
        (s.erase j).lcm fun k => Nat.gcd (d j) (d k))).mp
      hqOuterProduct
  have hqInnerProduct :
      q ∣ (s.erase j).prod fun k => Nat.gcd (d j) (d k) :=
    hqInner.trans
      (Finset.lcm_dvd_prod (s.erase j)
        fun k => Nat.gcd (d j) (d k))
  obtain ⟨k, hk, hqGcd⟩ :=
    (hq.prime.dvd_finset_prod_iff
      (fun k => Nat.gcd (d j) (d k))).mp hqInnerProduct
  have hkData := Finset.mem_erase.mp hk
  have hqj : q ∣ d j :=
    hqGcd.trans (Nat.gcd_dvd_left (d j) (d k))
  have hqk : q ∣ d k :=
    hqGcd.trans (Nat.gcd_dvd_right (d j) (d k))
  have hji : j = i := by
    by_contra hne
    exact hunique j hj hne hqj
  have hki : k = i := by
    by_contra hne
    exact hunique k hkData.2 hne hqk
  exact hkData.1 (hki.trans hji.symm)

/-- If that uniquely supported prime also misses the distinguished base,
it misses the full collision core. -/
theorem prime_not_dvd_collisionCore_of_unique_support
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {q : ℕ} {i : ι}
    (hq : q.Prime)
    (hqbase : ¬q ∣ base)
    (hunique :
      ∀ j ∈ s, j ≠ i → ¬q ∣ d j) :
    ¬q ∣ collisionCore base s d := by
  unfold collisionCore
  exact hq.prime.not_dvd_lcm hqbase
    (prime_not_dvd_pairwiseCollisionCore_of_unique_support
      hq hunique)

/-- Removing from every positive denominator the portion visible in the
finite collision core produces a pairwise-coprime family.  This is the
finite-family form of the private-support separation theorem. -/
theorem collisionCore_privateQuotients_pairwise_coprime
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hpos : ∀ i ∈ s, 0 < d i) :
    (s : Set ι).Pairwise fun i j =>
      Nat.Coprime
        (d i / Nat.gcd (d i) (collisionCore base s d))
        (d j / Nat.gcd (d j) (collisionCore base s d)) := by
  intro i hi j hj hij
  apply privateQuotients_coprime_of_gcd_dvd_core
  · exact Nat.gcd_pos_of_pos_left (d j) (hpos i hi)
  · exact gcd_dvd_collisionCore hi hj hij

/-- Private quotient owned by one denominator after deleting all support
visible in the collision core. -/
def privateQuotient
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) (i : ι) : ℕ :=
  d i / Nat.gcd (d i) (collisionCore base s d)

/-- An owner already contained in the distinguished base has no surviving
private quotient.  This is the generic absorption mechanism behind the
fact that a fixed owner cannot remain useful on factorial blocks whose base
grows without bound. -/
theorem privateQuotient_eq_one_of_dvd_base
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ} {i : ι}
    (hpos : 0 < d i)
    (hdiv : d i ∣ base) :
    privateQuotient base s d i = 1 := by
  have hcore :
      d i ∣ collisionCore base s d :=
    hdiv.trans (Nat.dvd_lcm_left base (pairwiseCollisionCore s d))
  have hgcd :
      Nat.gcd (d i) (collisionCore base s d) = d i :=
    Nat.gcd_eq_left_iff_dvd.mpr hcore
  unfold privateQuotient
  rw [hgcd]
  exact Nat.div_self hpos

/-- Product of all finite-family private quotients. -/
def privateModulus
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.prod (privateQuotient base s d)

/-- The private modulus is also the lcm of the private quotients.  Pairwise
coprimality is exactly what converts the lcm into the product. -/
theorem privateQuotient_lcm_eq_privateModulus
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hpos : ∀ i ∈ s, 0 < d i) :
    s.lcm (privateQuotient base s d) =
      privateModulus base s d := by
  unfold privateModulus
  apply Finset.lcm_eq_prod
  simpa [privateQuotient, Function.onFun] using
    (collisionCore_privateQuotients_pairwise_coprime
      (base := base) (s := s) (d := d) hpos)

/-- A positive denominator family has positive private modulus, even when
all collision deletion quotients equal one. -/
theorem privateModulus_pos
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hpos : ∀ i ∈ s, 0 < d i) :
    0 < privateModulus base s d := by
  unfold privateModulus
  apply Finset.prod_pos
  intro i hi
  unfold privateQuotient
  have hgDvd :
      Nat.gcd (d i) (collisionCore base s d) ∣ d i :=
    Nat.gcd_dvd_left _ _
  have hgPos :
      0 < Nat.gcd (d i) (collisionCore base s d) :=
    Nat.gcd_pos_of_pos_left _ (hpos i hi)
  exact Nat.div_pos
    (Nat.le_of_dvd (hpos i hi) hgDvd) hgPos

/-- A prime uniquely supported on one denominator survives in that
denominator's private quotient. -/
theorem prime_dvd_privateQuotient_of_unique_support
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {q : ℕ} {i : ι}
    (hq : q.Prime)
    (hqdi : q ∣ d i)
    (hqbase : ¬q ∣ base)
    (hunique :
      ∀ j ∈ s, j ≠ i → ¬q ∣ d j) :
    q ∣ privateQuotient base s d i := by
  have hqCore :
      ¬q ∣ collisionCore base s d :=
    prime_not_dvd_collisionCore_of_unique_support
      hq hqbase hunique
  have hqGcd :
      ¬q ∣ Nat.gcd (d i) (collisionCore base s d) := by
    intro h
    exact hqCore (h.trans (Nat.gcd_dvd_right _ _))
  have hfactor :
      Nat.gcd (d i) (collisionCore base s d) *
          privateQuotient base s d i =
        d i := by
    unfold privateQuotient
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hqProduct :
      q ∣ Nat.gcd (d i) (collisionCore base s d) *
        privateQuotient base s d i := by
    rw [hfactor]
    exact hqdi
  exact (hq.dvd_mul.mp hqProduct).resolve_left hqGcd

/-- Unique support preserves the complete displayed prime power, not only
one copy of its prime.  This is the multiplicity-sensitive bridge needed
to feed a canonical prefix-private power modulus into a split-factor CRT
certificate. -/
theorem primePow_dvd_privateQuotient_of_unique_support
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {q e : ℕ} {i : ι}
    (hq : q.Prime)
    (hqPowDi : q ^ e ∣ d i)
    (hqbase : ¬q ∣ base)
    (hunique :
      ∀ j ∈ s, j ≠ i → ¬q ∣ d j) :
    q ^ e ∣ privateQuotient base s d i := by
  have hqCore :
      ¬q ∣ collisionCore base s d :=
    prime_not_dvd_collisionCore_of_unique_support
      hq hqbase hunique
  have hqGcd :
      ¬q ∣ Nat.gcd (d i) (collisionCore base s d) := by
    intro h
    exact hqCore (h.trans (Nat.gcd_dvd_right _ _))
  have hpowCoprime :
      Nat.Coprime
        (q ^ e)
        (Nat.gcd (d i) (collisionCore base s d)) :=
    (hq.coprime_iff_not_dvd.mpr hqGcd).pow_left e
  have hgDvd :
      Nat.gcd (d i) (collisionCore base s d) ∣ d i :=
    Nat.gcd_dvd_left _ _
  unfold privateQuotient
  rw [Nat.dvd_div_iff_mul_dvd hgDvd]
  simpa [Nat.mul_comm] using
    hpowCoprime.mul_dvd_of_dvd_of_dvd
      hqPowDi hgDvd

/-- Consequently a uniquely supported prime makes the full private modulus
nontrivial. -/
theorem privateModulus_one_lt_of_unique_prime_support
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {q : ℕ} {i : ι}
    (hq : q.Prime)
    (hi : i ∈ s)
    (hqdi : q ∣ d i)
    (hqbase : ¬q ∣ base)
    (hunique :
      ∀ j ∈ s, j ≠ i → ¬q ∣ d j)
    (hpos : ∀ j ∈ s, 0 < d j) :
    1 < privateModulus base s d := by
  have hqPrivate :
      q ∣ privateQuotient base s d i :=
    prime_dvd_privateQuotient_of_unique_support
      hq hqdi hqbase hunique
  have hqModulus :
      q ∣ privateModulus base s d := by
    unfold privateModulus
    exact hqPrivate.trans
      (Finset.dvd_prod_of_mem
        (privateQuotient base s d) hi)
  exact hq.one_lt.trans_le
    (Nat.le_of_dvd (privateModulus_pos hpos) hqModulus)

/-- Weighted leave-one-out CRT numerator for a finite modulus family.  The
term owned by `i` omits exactly the modulus `r i`. -/
def weightedPrivateNumerator
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r a : ι → ℕ) : ℕ :=
  s.sum fun i => a i * (s.erase i).prod r

/-- Modulo one owned factor, every other leave-one-out term vanishes.
Thus the full weighted numerator projects to the single owner term. -/
theorem weightedPrivateNumerator_modEq_owner
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {r a : ι → ℕ}
    {i : ι}
    (hi : i ∈ s) :
    weightedPrivateNumerator s r a ≡
      a i * (s.erase i).prod r [MOD r i] := by
  have hrest :
      r i ∣ ∑ j ∈ s.erase i,
        a j * (s.erase j).prod r := by
    apply Finset.dvd_sum
    intro j hj
    have hjData := Finset.mem_erase.mp hj
    have hiErase : i ∈ s.erase j :=
      Finset.mem_erase.mpr ⟨hjData.1.symm, hi⟩
    exact dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem r hiErase) (a j)
  unfold weightedPrivateNumerator
  rw [← s.sum_erase_add _ hi]
  simpa using
    (Nat.modEq_zero_iff_dvd.mpr hrest).add_right
      (a i * (s.erase i).prod r)

/-- Private-support CRT lemma.  If the moduli are pairwise coprime and each
weight is coprime to its own modulus, then the weighted leave-one-out
numerator is coprime to the full modulus product.  Thus none of the private
prime-power support can disappear in primitive reduction. -/
theorem weightedPrivateNumerator_coprime_product
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {r a : ι → ℕ}
    (hpair :
      (s : Set ι).Pairwise fun i j =>
        Nat.Coprime (r i) (r j))
    (hweight : ∀ i ∈ s, Nat.Coprime (a i) (r i)) :
    Nat.Coprime
      (weightedPrivateNumerator s r a)
      (s.prod r) := by
  by_contra hnot
  rw [Nat.Prime.not_coprime_iff_dvd] at hnot
  obtain ⟨p, hp, hpNumerator, hpProduct⟩ := hnot
  obtain ⟨i, hi, hpri⟩ :=
    (hp.prime.dvd_finset_prod_iff r).mp hpProduct
  have hpOther :
      ∀ j ∈ s.erase i, ¬p ∣ r j := by
    intro j hj
    have hjData := Finset.mem_erase.mp hj
    have hcop : Nat.Coprime (r i) (r j) :=
      hpair hi hjData.2 hjData.1.symm
    have hpcop : Nat.Coprime p (r j) :=
      hcop.of_dvd_left hpri
    exact hp.coprime_iff_not_dvd.mp hpcop
  have hpOtherProduct :
      ¬p ∣ (s.erase i).prod r :=
    hp.prime.not_dvd_finset_prod hpOther
  have hpWeight :
      ¬p ∣ a i := by
    have hpcop : Nat.Coprime p (a i) :=
      (hweight i hi).symm.of_dvd_left hpri
    exact hp.coprime_iff_not_dvd.mp hpcop
  have hpOwner :
      ¬p ∣ a i * (s.erase i).prod r :=
    hp.not_dvd_mul hpWeight hpOtherProduct
  have hpRestTerm :
      ∀ j ∈ s.erase i,
        p ∣ a j * (s.erase j).prod r := by
    intro j hj
    have hjData := Finset.mem_erase.mp hj
    have hiErase : i ∈ s.erase j :=
      Finset.mem_erase.mpr ⟨hjData.1.symm, hi⟩
    have hpLeaveOneOut :
        p ∣ (s.erase j).prod r :=
      hpri.trans (Finset.dvd_prod_of_mem r hiErase)
    exact dvd_mul_of_dvd_right hpLeaveOneOut (a j)
  have hpRest :
      p ∣ ∑ j ∈ s.erase i,
        a j * (s.erase j).prod r :=
    Finset.dvd_sum hpRestTerm
  have hpOwnerDvd :
      p ∣ a i * (s.erase i).prod r := by
    unfold weightedPrivateNumerator at hpNumerator
    rw [← s.sum_erase_add _ hi] at hpNumerator
    exact (Nat.dvd_add_iff_right hpRest).mpr hpNumerator
  exact hpOwner hpOwnerDvd

/-- Canonical weight paired with one private quotient. -/
def privateWeight
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) (i : ι) : ℕ :=
  collisionCore base s d /
    Nat.gcd (d i) (collisionCore base s d)

/-- Canonical weighted numerator attached to the finite collision core. -/
def collisionWeightedPrivateNumerator
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  weightedPrivateNumerator s
    (privateQuotient base s d)
    (privateWeight base s d)

/-- The collision-weighted numerator has an exact one-owner projection
modulo each private quotient. -/
theorem collisionWeightedPrivateNumerator_modEq_owner
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {i : ι}
    (hi : i ∈ s) :
    collisionWeightedPrivateNumerator base s d ≡
      privateWeight base s d i *
        (s.erase i).prod (privateQuotient base s d)
      [MOD privateQuotient base s d i] := by
  exact weightedPrivateNumerator_modEq_owner hi

/-- A canonical collision-core weight is coprime to its private quotient.
Both are the standard gcd-reduced quotients of the core and the owned
denominator. -/
theorem privateWeight_coprime_privateQuotient
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {i : ι}
    (hpos : 0 < d i) :
    Nat.Coprime
      (privateWeight base s d i)
      (privateQuotient base s d i) := by
  have hgPos :
      0 < Nat.gcd (collisionCore base s d) (d i) :=
    Nat.gcd_pos_of_pos_right _ hpos
  simpa [privateWeight, privateQuotient, Nat.gcd_comm] using
    (Nat.coprime_div_gcd_div_gcd hgPos)

/-- A prime owned by one canonical private quotient cannot divide that
quotient's one-owner weighted term.  Pairwise private support excludes the
leave-one-out product, while the gcd-reduced canonical weight excludes the
remaining factor. -/
theorem privateOwnerTerm_mod_prime_pos
    {ι : Type*} [DecidableEq ι]
    {base q : ℕ} {s : Finset ι} {d : ι → ℕ} {i : ι}
    (hq : q.Prime)
    (hi : i ∈ s)
    (hpos : ∀ j ∈ s, 0 < d j)
    (hqdvd : q ∣ privateQuotient base s d i) :
    0 <
      (privateWeight base s d i *
        (s.erase i).prod (privateQuotient base s d)) % q := by
  have hpair :=
    collisionCore_privateQuotients_pairwise_coprime
      (base := base) (s := s) (d := d) hpos
  have hqOther :
      ∀ j ∈ s.erase i, ¬q ∣ privateQuotient base s d j := by
    intro j hj
    have hjData := Finset.mem_erase.mp hj
    have hcop :
        Nat.Coprime
          (privateQuotient base s d i)
          (privateQuotient base s d j) :=
      hpair hi hjData.2 hjData.1.symm
    have hqcop :
        Nat.Coprime q (privateQuotient base s d j) :=
      hcop.of_dvd_left hqdvd
    exact hq.coprime_iff_not_dvd.mp hqcop
  have hqOthers :
      ¬q ∣ (s.erase i).prod (privateQuotient base s d) :=
    hq.prime.not_dvd_finset_prod hqOther
  have hqWeight :
      ¬q ∣ privateWeight base s d i := by
    have hcop :=
      privateWeight_coprime_privateQuotient
        (base := base) (s := s) (d := d) (i := i)
        (hpos i hi)
    have hqcop :
        Nat.Coprime q (privateWeight base s d i) :=
      hcop.symm.of_dvd_left hqdvd
    exact hq.coprime_iff_not_dvd.mp hqcop
  have hqOwner :
      ¬q ∣ privateWeight base s d i *
        (s.erase i).prod (privateQuotient base s d) :=
    hq.not_dvd_mul hqWeight hqOthers
  have hmodNe :
      (privateWeight base s d i *
        (s.erase i).prod (privateQuotient base s d)) % q ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hqOwner
  exact Nat.pos_of_ne_zero hmodNe

/-- Complete abstract private-support survival theorem for the canonical
collision core: its canonical weighted numerator is coprime to the entire
private modulus. -/
theorem collisionWeightedPrivateNumerator_coprime_privateModulus
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hpos : ∀ i ∈ s, 0 < d i) :
    Nat.Coprime
      (collisionWeightedPrivateNumerator base s d)
      (privateModulus base s d) := by
  unfold collisionWeightedPrivateNumerator privateModulus
  apply weightedPrivateNumerator_coprime_product
  · simpa [privateQuotient] using
      (collisionCore_privateQuotients_pairwise_coprime
        (base := base) (s := s) (d := d) hpos)
  · intro i hi
    exact privateWeight_coprime_privateQuotient (hpos i hi)

/-- Pairwise lcm commutes with deleting the prime-power component shared
with a fixed positive core.  This is the reusable factorization identity
behind the endpoint equation `R = L / C`. -/
theorem lcm_div_gcd_right_distrib
    {a b C : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    Nat.lcm
        (a / Nat.gcd a C)
        (b / Nat.gcd b C) =
      Nat.lcm a b / Nat.gcd (Nat.lcm a b) C := by
  have hgaDvd : Nat.gcd a C ∣ a :=
    Nat.gcd_dvd_left a C
  have hgbDvd : Nat.gcd b C ∣ b :=
    Nat.gcd_dvd_left b C
  have hgaPos : 0 < Nat.gcd a C :=
    Nat.gcd_pos_of_pos_left C ha
  have hgbPos : 0 < Nat.gcd b C :=
    Nat.gcd_pos_of_pos_left C hb
  have haQPos : 0 < a / Nat.gcd a C :=
    Nat.div_pos (Nat.le_of_dvd ha hgaDvd) hgaPos
  have hbQPos : 0 < b / Nat.gcd b C :=
    Nat.div_pos (Nat.le_of_dvd hb hgbDvd) hgbPos
  have hLNe : Nat.lcm a b ≠ 0 :=
    Nat.lcm_ne_zero ha.ne' hb.ne'
  have hLPos : 0 < Nat.lcm a b :=
    Nat.pos_of_ne_zero hLNe
  have hLgDvd :
      Nat.gcd (Nat.lcm a b) C ∣ Nat.lcm a b :=
    Nat.gcd_dvd_left _ _
  have hLgPos :
      0 < Nat.gcd (Nat.lcm a b) C :=
    Nat.gcd_pos_of_pos_left C hLPos
  have hRhsPos :
      0 < Nat.lcm a b / Nat.gcd (Nat.lcm a b) C :=
    Nat.div_pos (Nat.le_of_dvd hLPos hLgDvd) hLgPos
  apply Nat.eq_of_factorization_eq
    (Nat.lcm_ne_zero haQPos.ne' hbQPos.ne')
    hRhsPos.ne'
  intro p
  rw [
    Nat.factorization_lcm haQPos.ne' hbQPos.ne',
    Nat.factorization_div hgaDvd,
    Nat.factorization_div hgbDvd,
    Nat.factorization_gcd ha.ne' hC.ne',
    Nat.factorization_gcd hb.ne' hC.ne',
    Nat.factorization_div hLgDvd,
    Nat.factorization_gcd hLNe hC.ne',
    Nat.factorization_lcm ha.ne' hb.ne'
  ]
  change
    max
        (a.factorization p - min (a.factorization p) (C.factorization p))
        (b.factorization p - min (b.factorization p) (C.factorization p)) =
      max (a.factorization p) (b.factorization p) -
        min (max (a.factorization p) (b.factorization p))
          (C.factorization p)
  omega

/-- Finite-family lift of `lcm_div_gcd_right_distrib`: removing the part
shared with a fixed positive collision core commutes with taking the lcm of
a finite family of positive denominators. -/
theorem finset_lcm_div_gcd_right_distrib
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {d : ι → ℕ} {C : ℕ}
    (hC : 0 < C)
    (hpos : ∀ i ∈ s, 0 < d i) :
    s.lcm (fun i => d i / Nat.gcd (d i) C) =
      s.lcm d / Nat.gcd (s.lcm d) C := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.lcm_insert, Finset.lcm_insert]
      rw [ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))]
      apply lcm_div_gcd_right_distrib
      · exact hpos i (Finset.mem_insert_self i s)
      · exact Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff).2
          (fun j hj =>
            (hpos j (Finset.mem_insert_of_mem hj)).ne'))
      · exact hC

/-- The canonical private modulus is exactly the denominator-family lcm
after deleting the prime-power support visible in the collision core. -/
theorem privateModulus_eq_lcm_div_gcd_collisionCore
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    privateModulus base s d =
      s.lcm d /
        Nat.gcd (s.lcm d) (collisionCore base s d) := by
  rw [← privateQuotient_lcm_eq_privateModulus hpos]
  simpa [privateQuotient] using
    (finset_lcm_div_gcd_right_distrib
      (C := collisionCore base s d)
      (collisionCore_pos hbase hpos) hpos)

/-- With the distinguished base included, the canonical private modulus is
the full endpoint common denominator divided by the collision core. -/
theorem privateModulus_eq_endpointDenominatorLcm_div_collisionCore
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    privateModulus base s d =
      endpointDenominatorLcm base s d /
        collisionCore base s d := by
  have hDPos : 0 < s.lcm d :=
    Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff).2
      (fun i hi => (hpos i hi).ne'))
  have hbaseCore :
      base ∣ collisionCore base s d := by
    exact Nat.dvd_lcm_left _ _
  have hcoreEndpoint :
      collisionCore base s d ∣
        endpointDenominatorLcm base s d :=
    collisionCore_dvd_endpointDenominatorLcm
  have hbinary :=
    lcm_div_gcd_right_distrib hbase hDPos
      (collisionCore_pos hbase hpos)
  have hbaseGcd :
      Nat.gcd base (collisionCore base s d) = base :=
    Nat.gcd_eq_left_iff_dvd.mpr hbaseCore
  have hendpointGcd :
      Nat.gcd (endpointDenominatorLcm base s d)
          (collisionCore base s d) =
        collisionCore base s d :=
    Nat.gcd_eq_right_iff_dvd.mpr hcoreEndpoint
  have hbaseDiv :
      base / Nat.gcd base (collisionCore base s d) = 1 := by
    rw [hbaseGcd]
    exact Nat.div_self hbase
  have hendpointGcd' :
      Nat.gcd (Nat.lcm base (s.lcm d))
          (collisionCore base s d) =
        collisionCore base s d := by
    simpa [endpointDenominatorLcm] using hendpointGcd
  rw [privateModulus_eq_lcm_div_gcd_collisionCore hbase hpos]
  rw [hbaseDiv, hendpointGcd'] at hbinary
  simpa [endpointDenominatorLcm] using hbinary

/-- The private modulus divides the common-denominator multiplier of the
distinguished base. -/
theorem privateModulus_dvd_endpointDenominatorLcm_div_base
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    privateModulus base s d ∣
      endpointDenominatorLcm base s d / base := by
  rw [privateModulus_eq_endpointDenominatorLcm_div_collisionCore
    hbase hpos]
  exact Nat.div_dvd_div_left
    collisionCore_dvd_endpointDenominatorLcm
    (Nat.dvd_lcm_left base (pairwiseCollisionCore s d))

/-- Hence the private modulus divides the entire positive base
contribution, independently of the displayed coefficient `K`. -/
theorem privateModulus_dvd_endpointBaseNumerator
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    privateModulus base s d ∣
      endpointBaseNumerator K base s d := by
  unfold endpointBaseNumerator
  exact dvd_mul_of_dvd_right
    (privateModulus_dvd_endpointDenominatorLcm_div_base
      hbase hpos) K

/-- Each common-denominator tail term is exactly its canonical collision
weight times the product of every other private quotient. -/
theorem endpointDenominatorTerm_eq_privateWeight_mul_leaveOneOut
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {i : ι}
    (hbase : 0 < base)
    (hpos : ∀ j ∈ s, 0 < d j)
    (hi : i ∈ s) :
    endpointDenominatorLcm base s d / d i =
      privateWeight base s d i *
        (s.erase i).prod (privateQuotient base s d) := by
  have hciDvdD :
      Nat.gcd (d i) (collisionCore base s d) ∣ d i :=
    Nat.gcd_dvd_left _ _
  have hciDvdC :
      Nat.gcd (d i) (collisionCore base s d) ∣
        collisionCore base s d :=
    Nat.gcd_dvd_right _ _
  have hdFactor :
      Nat.gcd (d i) (collisionCore base s d) *
          privateQuotient base s d i =
        d i := by
    exact Nat.mul_div_cancel' hciDvdD
  have hcoreFactor :
      Nat.gcd (d i) (collisionCore base s d) *
          privateWeight base s d i =
        collisionCore base s d := by
    exact Nat.mul_div_cancel' hciDvdC
  have hprivateFactor :
      privateQuotient base s d i *
          (s.erase i).prod (privateQuotient base s d) =
        privateModulus base s d := by
    exact Finset.mul_prod_erase s (privateQuotient base s d) hi
  have hendpointFactor :
      collisionCore base s d * privateModulus base s d =
        endpointDenominatorLcm base s d := by
    rw [privateModulus_eq_endpointDenominatorLcm_div_collisionCore
      hbase hpos]
    exact Nat.mul_div_cancel'
      collisionCore_dvd_endpointDenominatorLcm
  have hmul :
      d i *
          (privateWeight base s d i *
            (s.erase i).prod (privateQuotient base s d)) =
        endpointDenominatorLcm base s d := by
    calc
      d i *
            (privateWeight base s d i *
              (s.erase i).prod (privateQuotient base s d)) =
          (Nat.gcd (d i) (collisionCore base s d) *
              privateQuotient base s d i) *
            (privateWeight base s d i *
              (s.erase i).prod (privateQuotient base s d)) := by
                rw [hdFactor]
      _ =
          (Nat.gcd (d i) (collisionCore base s d) *
              privateWeight base s d i) *
            (privateQuotient base s d i *
              (s.erase i).prod (privateQuotient base s d)) := by
                ac_rfl
      _ =
          collisionCore base s d * privateModulus base s d := by
            rw [hcoreFactor, hprivateFactor]
      _ = endpointDenominatorLcm base s d :=
        hendpointFactor
  exact (Nat.eq_div_of_mul_eq_right (hpos i hi).ne' hmul).symm

/-- The canonical collision-weighted numerator is literally the tail
numerator over the full endpoint common denominator. -/
theorem endpointTailNumerator_eq_collisionWeightedPrivateNumerator
    {ι : Type*} [DecidableEq ι]
    {base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i) :
    endpointTailNumerator base s d =
      collisionWeightedPrivateNumerator base s d := by
  unfold endpointTailNumerator collisionWeightedPrivateNumerator
    weightedPrivateNumerator
  apply Finset.sum_congr rfl
  intro i hi
  exact endpointDenominatorTerm_eq_privateWeight_mul_leaveOneOut
    hbase hpos hi

/-- Under the positive-endpoint ordering, the displayed numerator plus its
tail numerator recovers the base contribution exactly. -/
theorem endpointNumerator_add_tail_eq_endpointBaseNumerator
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d) :
    endpointNumerator K base s d +
        endpointTailNumerator base s d =
      endpointBaseNumerator K base s d := by
  unfold endpointNumerator
  exact Nat.sub_add_cancel htail

/-- Exact negative-residue transport for the displayed endpoint numerator:
`Z + T` is zero modulo the private modulus. -/
theorem endpointNumerator_add_tail_modEq_zero
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d) :
    endpointNumerator K base s d +
        endpointTailNumerator base s d ≡
      0 [MOD privateModulus base s d] := by
  rw [endpointNumerator_add_tail_eq_endpointBaseNumerator htail]
  exact Nat.modEq_zero_iff_dvd.mpr
    (privateModulus_dvd_endpointBaseNumerator hbase hpos)

/-- The same negative-residue congruence stated with the canonical
collision-weighted CRT numerator. -/
theorem endpointNumerator_add_collisionWeightedPrivateNumerator_modEq_zero
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d) :
    endpointNumerator K base s d +
        collisionWeightedPrivateNumerator base s d ≡
      0 [MOD privateModulus base s d] := by
  rw [← endpointTailNumerator_eq_collisionWeightedPrivateNumerator
    hbase hpos]
  exact endpointNumerator_add_tail_modEq_zero hbase hpos htail

/-- If `Z + T` vanishes modulo `R` and `T` is coprime to `R`, then `Z`
is also coprime to `R`. -/
theorem coprime_left_of_add_modEq_zero
    {Z T R : ℕ}
    (hmod : Z + T ≡ 0 [MOD R])
    (hcop : Nat.Coprime T R) :
    Nat.Coprime Z R := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  have hRsum : R ∣ Z + T :=
    Nat.modEq_zero_iff_dvd.mp hmod
  have hgZ : Nat.gcd Z R ∣ Z :=
    Nat.gcd_dvd_left Z R
  have hgR : Nat.gcd Z R ∣ R :=
    Nat.gcd_dvd_right Z R
  have hgSum : Nat.gcd Z R ∣ Z + T :=
    hgR.trans hRsum
  have hgT : Nat.gcd Z R ∣ T :=
    (Nat.dvd_add_iff_right hgZ).mpr hgSum
  have hgOne : Nat.gcd Z R ∣ 1 := by
    simpa [Nat.Coprime.gcd_eq_one hcop] using
      (Nat.dvd_gcd hgT hgR)
  exact Nat.dvd_one.mp hgOne

/-- Complete private-support survival statement for the displayed endpoint:
under the positive-endpoint ordering, its numerator is coprime to the whole
private modulus. -/
theorem endpointNumerator_coprime_privateModulus
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d) :
    Nat.Coprime
      (endpointNumerator K base s d)
      (privateModulus base s d) := by
  apply coprime_left_of_add_modEq_zero
    (endpointNumerator_add_collisionWeightedPrivateNumerator_modEq_zero
      hbase hpos htail)
  exact collisionWeightedPrivateNumerator_coprime_privateModulus hpos

/-- A large prime divisor of a factorial gap becomes prefix-private at its
first occurrence. The size bound transfers from the source index `n` to the
minimal hit `m`, which is the bridge needed to turn large-prime-divisor
results for `n! - 1` into weighted private-support anchors. -/
theorem exists_large_prefix_private_factorialGap_hit
    {p n C : ℕ}
    (hp : p.Prime)
    (hn2 : 2 ≤ n)
    (hpn : p ∣ n.factorial - 1)
    (hlarge : C * n < p) :
    ∃ m, 2 ≤ m ∧ m ≤ n ∧ C * m < p ∧
      p ∣ m.factorial - 1 ∧
      ∀ k, 2 ≤ k → k < m → Nat.Coprime p (k.factorial - 1) := by
  let P : ℕ → Prop := fun m =>
    2 ≤ m ∧ m ≤ n ∧ p ∣ m.factorial - 1
  have hP : ∃ m, P m := ⟨n, hn2, le_rfl, hpn⟩
  let m := Nat.find hP
  have hmP : P m := Nat.find_spec hP
  refine ⟨m, hmP.1, hmP.2.1, ?_, hmP.2.2, ?_⟩
  · exact (Nat.mul_le_mul_left C hmP.2.1).trans_lt hlarge
  · intro k hk2 hkm
    apply hp.coprime_iff_not_dvd.mpr
    intro hpk
    have hmle : m ≤ k :=
      Nat.find_min' hP
        ⟨hk2, (Nat.le_of_lt hkm).trans hmP.2.1, hpk⟩
    omega

/-- A prime dividing `n! - 1` cannot also divide the immediately following
factorial gap.  Modulo that prime, `(n+1)! - 1` reduces to `n`, while every
prime divisor of `n! - 1` is larger than `n`. -/
theorem prime_not_dvd_succ_factorial_sub_one_of_dvd
    {q n : ℕ}
    (hq : q.Prime)
    (hn : 1 ≤ n)
    (hqdvd : q ∣ n.factorial - 1) :
    ¬q ∣ (n + 1).factorial - 1 := by
  intro hqSucc
  have hdecomp :
      (n + 1).factorial - 1 =
        (n + 1) * (n.factorial - 1) + n := by
    have hfacOne : 1 ≤ n.factorial :=
      Nat.factorial_pos n
    calc
      (n + 1).factorial - 1 =
          (n + 1) * n.factorial - 1 := by
            rw [Nat.factorial_succ]
      _ = (n + 1) * ((n.factorial - 1) + 1) - 1 := by
            rw [Nat.sub_add_cancel hfacOne]
      _ = ((n + 1) * (n.factorial - 1) + (n + 1)) - 1 := by
            rw [Nat.mul_add, Nat.mul_one]
      _ = (n + 1) * (n.factorial - 1) + n := by
            omega
  have hqFirst :
      q ∣ (n + 1) * (n.factorial - 1) :=
    dvd_mul_of_dvd_right hqdvd (n + 1)
  have hqn : q ∣ n := by
    rw [hdecomp] at hqSucc
    exact (Nat.dvd_add_iff_right hqFirst).mpr hqSucc
  exact (Nat.not_dvd_of_pos_of_lt (by omega)
    (prime_dvd_factorial_sub_one_gt hq hqdvd)) hqn

/-- Canonical projection of a weighted support numerator modulo `Q`. -/
def projectedResidue (T Q : ℕ) : ℕ :=
  T % Q

/-- Canonical projection of the additive inverse of a natural numerator.
The outer remainder sends the zero residue to zero rather than to `Q`. -/
def complementaryProjectedResidue (T Q : ℕ) : ℕ :=
  projectedResidue (Q - projectedResidue T Q) Q

/-- If `Z + T` vanishes modulo a positive modulus, the projection of `Z`
is the complementary projection of `T`. -/
theorem projectedResidue_eq_complementary_of_add_modEq_zero
    {Z T Q : ℕ}
    (hQ : 0 < Q)
    (hmod : Z + T ≡ 0 [MOD Q]) :
    projectedResidue Z Q =
      complementaryProjectedResidue T Q := by
  have hremLe : T % Q ≤ Q :=
    (Nat.mod_lt T hQ).le
  have hcomplement :
      (Q - T % Q) + T ≡ 0 [MOD Q] := by
    calc
      (Q - T % Q) + T ≡
          (Q - T % Q) + T % Q [MOD Q] :=
        Nat.ModEq.rfl.add (Nat.mod_modEq T Q).symm
      _ = Q := Nat.sub_add_cancel hremLe
      _ ≡ 0 [MOD Q] := by simp
  have hZT :
      Z ≡ Q - T % Q [MOD Q] :=
    Nat.ModEq.add_right_cancel' T
      (hmod.trans hcomplement.symm)
  simpa [projectedResidue, complementaryProjectedResidue] using hZT

/-- Least nonnegative private-modulus residue of the displayed endpoint
numerator.  Under a nontrivial private modulus, coprimality makes it the
least positive residue. -/
def endpointPrivateResidue
    {ι : Type*} [DecidableEq ι]
    (K base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  projectedResidue
    (endpointNumerator K base s d)
    (privateModulus base s d)

/-- Reducing the least residue modulo a divisor of the full private modulus
is the same as reducing the original endpoint numerator directly. -/
theorem projectedResidue_endpointPrivateResidue_eq_of_dvd
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {Q : ℕ}
    (hQ :
      Q ∣ privateModulus base s d) :
    projectedResidue
        (endpointPrivateResidue K base s d) Q =
      projectedResidue
        (endpointNumerator K base s d) Q := by
  unfold endpointPrivateResidue projectedResidue
  exact Nat.mod_mod_of_dvd _ hQ

/-- A residue of a number coprime to a nontrivial modulus is positive,
bounded above by the number, and strictly below the modulus. -/
theorem projectedResidue_bounds_of_coprime
    {Z R : ℕ}
    (hR : 1 < R)
    (hcop : Nat.Coprime Z R) :
    0 < projectedResidue Z R ∧
      projectedResidue Z R ≤ Z ∧
      projectedResidue Z R < R := by
  have hRPos : 0 < R := by omega
  have hresNe : Z % R ≠ 0 := by
    intro hzero
    have hRdvdZ : R ∣ Z :=
      Nat.dvd_iff_mod_eq_zero.mpr hzero
    have hgcdR : Nat.gcd Z R = R :=
      Nat.gcd_eq_right_iff_dvd.mpr hRdvdZ
    have hgcdOne : Nat.gcd Z R = 1 :=
      Nat.Coprime.gcd_eq_one hcop
    omega
  simpa [projectedResidue] using
    And.intro (Nat.pos_of_ne_zero hresNe)
      (And.intro (Nat.mod_le Z R) (Nat.mod_lt Z hRPos))

/-- For a coprime numerator and a nontrivial modulus, the complementary
projection is the literal positive complement of the ordinary remainder. -/
theorem complementaryProjectedResidue_eq_sub_of_coprime
    {T R : ℕ}
    (hR : 1 < R)
    (hcop : Nat.Coprime T R) :
    complementaryProjectedResidue T R = R - T % R := by
  have hresPos :
      0 < T % R := by
    simpa [projectedResidue] using
      (projectedResidue_bounds_of_coprime hR hcop).1
  unfold complementaryProjectedResidue projectedResidue
  apply Nat.mod_eq_of_lt
  omega

/-- Adding that complementary projection advances the Euclidean quotient
by exactly one.  This is the natural-number form of the distance from
`T / R` to its next integer. -/
theorem add_complementaryProjectedResidue_eq_succ_div_mul
    {T R : ℕ}
    (hR : 1 < R)
    (hcop : Nat.Coprime T R) :
    T + complementaryProjectedResidue T R =
      (T / R + 1) * R := by
  rw [complementaryProjectedResidue_eq_sub_of_coprime hR hcop]
  have hmodLe : T % R ≤ R :=
    (Nat.mod_lt T (by omega)).le
  calc
    T + (R - T % R) =
        (T % R + R * (T / R)) + (R - T % R) := by
          rw [Nat.mod_add_div]
    _ = R * (T / R) + R := by omega
    _ = (T / R + 1) * R := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (T / R) R]

/-- The actual displayed endpoint residue satisfies the same sharp natural
bounds once the private modulus is nontrivial. -/
theorem endpointPrivateResidue_bounds
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d)
    (hR : 1 < privateModulus base s d) :
    0 < endpointPrivateResidue K base s d ∧
      endpointPrivateResidue K base s d ≤
        endpointNumerator K base s d ∧
      endpointPrivateResidue K base s d <
        privateModulus base s d := by
  exact projectedResidue_bounds_of_coprime hR
    (endpointNumerator_coprime_privateModulus hbase hpos htail)

/-- The least positive endpoint residue carries the same negative-tail
congruence as the displayed endpoint numerator. -/
theorem endpointPrivateResidue_add_tail_modEq_zero
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d) :
    endpointPrivateResidue K base s d +
        endpointTailNumerator base s d ≡
      0 [MOD privateModulus base s d] := by
  have hproject :
      endpointPrivateResidue K base s d ≡
        endpointNumerator K base s d
          [MOD privateModulus base s d] := by
    simpa [endpointPrivateResidue, projectedResidue] using
      (Nat.mod_modEq
        (endpointNumerator K base s d)
        (privateModulus base s d))
  exact
    (hproject.add_right (endpointTailNumerator base s d)).trans
      (endpointNumerator_add_tail_modEq_zero hbase hpos htail)

/-- Projecting further to one private quotient leaves a single explicit
owner term in the negative-tail congruence. -/
theorem endpointPrivateResidue_add_owner_modEq_zero
    {ι : Type*} [DecidableEq ι]
    {K base : ℕ} {s : Finset ι} {d : ι → ℕ}
    {i : ι}
    (hbase : 0 < base)
    (hpos : ∀ j ∈ s, 0 < d j)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d)
    (hi : i ∈ s) :
    endpointPrivateResidue K base s d +
        privateWeight base s d i *
          (s.erase i).prod (privateQuotient base s d) ≡
      0 [MOD privateQuotient base s d i] := by
  have howner :
      endpointTailNumerator base s d ≡
        privateWeight base s d i *
          (s.erase i).prod (privateQuotient base s d)
        [MOD privateQuotient base s d i] := by
    rw [endpointTailNumerator_eq_collisionWeightedPrivateNumerator
      hbase hpos]
    exact collisionWeightedPrivateNumerator_modEq_owner hi
  have hprivateDvd :
      privateQuotient base s d i ∣
        privateModulus base s d := by
    unfold privateModulus
    exact Finset.dvd_prod_of_mem
      (privateQuotient base s d) hi
  exact
    (howner.add_left
      (endpointPrivateResidue K base s d)).symm.trans
      ((endpointPrivateResidue_add_tail_modEq_zero
        hbase hpos htail).of_dvd hprivateDvd)

/-- The same owner congruence descends to every divisor of the owned
private quotient. -/
theorem endpointPrivateResidue_add_owner_modEq_zero_of_dvd
    {ι : Type*} [DecidableEq ι]
    {K base q : ℕ} {s : Finset ι} {d : ι → ℕ}
    {i : ι}
    (hbase : 0 < base)
    (hpos : ∀ j ∈ s, 0 < d j)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d)
    (hi : i ∈ s)
    (hq :
      q ∣ privateQuotient base s d i) :
    endpointPrivateResidue K base s d +
        privateWeight base s d i *
          (s.erase i).prod (privateQuotient base s d) ≡
      0 [MOD q] := by
  exact
    (endpointPrivateResidue_add_owner_modEq_zero
      hbase hpos htail hi).of_dvd hq

/-- If `ρ` is the additive complement of a nonzero residue `T mod q`,
then `ρ` is at least the explicit complementary residue `q - T mod q`. -/
theorem complementary_residue_lower_bound
    {ρ T q : ℕ}
    (hmod : ρ + T ≡ 0 [MOD q])
    (hTpos : 0 < T % q) :
    q - T % q ≤ ρ := by
  have hsumZero :
      (ρ + T) % q = 0 := by
    simpa [Nat.ModEq] using hmod
  have hadd := Nat.add_mod_add_ite ρ T q
  rw [hsumZero] at hadd
  have hwrap :
      q ≤ ρ % q + T % q := by
    by_contra hnot
    have hzero :
        0 = ρ % q + T % q := by
      simpa [hnot] using hadd
    omega
  have hcomplement :
      q = ρ % q + T % q := by
    simpa [hwrap] using hadd
  have hρmod : ρ % q ≤ ρ :=
    Nat.mod_le ρ q
  omega

/-- A nonzero one-owner projection gives a concrete numerical lower bound
for the full endpoint private residue. -/
theorem endpointPrivateResidue_owner_lower_bound
    {ι : Type*} [DecidableEq ι]
    {K base q : ℕ} {s : Finset ι} {d : ι → ℕ}
    {i : ι}
    (hbase : 0 < base)
    (hpos : ∀ j ∈ s, 0 < d j)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d)
    (hi : i ∈ s)
    (hq :
      q ∣ privateQuotient base s d i)
    (howner :
      0 <
        (privateWeight base s d i *
          (s.erase i).prod (privateQuotient base s d)) % q) :
    q -
        (privateWeight base s d i *
          (s.erase i).prod (privateQuotient base s d)) % q ≤
      endpointPrivateResidue K base s d := by
  exact complementary_residue_lower_bound
    (endpointPrivateResidue_add_owner_modEq_zero_of_dvd
      hbase hpos htail hi hq)
    howner

/-- Integral Archimedean--CRT closing criterion: an upper bound on a scaled
endpoint numerator is incompatible with a larger scaled least residue. -/
theorem scaled_endpoint_upper_bound_excluded_by_residue
    {ρ Z L scale budget : ℕ}
    (hρZ : ρ ≤ Z)
    (hupper : scale * Z ≤ budget * L)
    (hlarge : budget * L < scale * ρ) :
    False := by
  have hscaled : scale * ρ ≤ scale * Z :=
    Nat.mul_le_mul_left scale hρZ
  omega

/-- Collision-core specialization of the integral closing criterion.  This
is the direct formal target for a factorial-block residue estimate. -/
theorem endpoint_scaled_upper_bound_false_of_privateResidue
    {ι : Type*} [DecidableEq ι]
    {K base scale budget : ℕ}
    {s : Finset ι} {d : ι → ℕ}
    (hbase : 0 < base)
    (hpos : ∀ i ∈ s, 0 < d i)
    (htail :
      endpointTailNumerator base s d ≤
        endpointBaseNumerator K base s d)
    (hR : 1 < privateModulus base s d)
    (hupper :
      scale * endpointNumerator K base s d ≤
        budget * endpointDenominatorLcm base s d)
    (hlarge :
      budget * endpointDenominatorLcm base s d <
        scale * endpointPrivateResidue K base s d) :
    False := by
  exact scaled_endpoint_upper_bound_excluded_by_residue
    (endpointPrivateResidue_bounds hbase hpos htail hR).2.1
    hupper hlarge

/-- Modulus obtained by omitting one private quotient. -/
def leaveOneOutModulus (R r : ℕ) : ℕ :=
  R / r

/-- Two divisors of a positive modulus satisfy the exact order-reversing
deletion identity: the smaller leave-one-out modulus times the larger
deleted factor recovers the full modulus. -/
theorem min_leaveOneOutModulus_mul_max_eq
    {R r₁ r₂ : ℕ}
    (hR : 0 < R)
    (hr₁ : r₁ ∣ R)
    (hr₂ : r₂ ∣ R) :
    min
        (leaveOneOutModulus R r₁)
        (leaveOneOutModulus R r₂) *
      max r₁ r₂ =
    R := by
  have hr₁Pos : 0 < r₁ :=
    Nat.pos_of_dvd_of_pos hr₁ hR
  have hr₂Pos : 0 < r₂ :=
    Nat.pos_of_dvd_of_pos hr₂ hR
  unfold leaveOneOutModulus
  rcases le_total r₁ r₂ with hr₁r₂ | hr₂r₁
  · rw [
      max_eq_right hr₁r₂,
      min_eq_right (Nat.div_le_div_left hr₁r₂ hr₁Pos),
      Nat.div_mul_cancel hr₂
    ]
  · rw [
      max_eq_left hr₂r₁,
      min_eq_left (Nat.div_le_div_left hr₂r₁ hr₂Pos),
      Nat.div_mul_cancel hr₁
    ]

/-- Deleting two coprime divisors of a modulus produces two projection
moduli whose lcm recovers the full modulus.  Unlike the owner-indexed
specialization below, the deleted factors may come from the same private
quotient. -/
theorem leaveOneOut_lcm_eq_of_coprime_divisors
    {R a b : ℕ}
    (ha : a ∣ R)
    (hb : b ∣ R)
    (hab : Nat.Coprime a b) :
    Nat.lcm
        (leaveOneOutModulus R a)
        (leaveOneOutModulus R b) =
      R := by
  unfold leaveOneOutModulus
  rw [
    Nat.div_lcm_eq_div_gcd ha hb,
    hab.gcd_eq_one,
    Nat.div_one
  ]

/-- Any residue below both projection moduli has identical projections.
Thus disagreement forces it above the prescribed budget. -/
theorem projection_disagreement_forces_gt
    {ρ B Q₁ Q₂ : ℕ}
    (hQ₁ : B < Q₁)
    (hQ₂ : B < Q₂)
    (hneq : projectedResidue ρ Q₁ ≠ projectedResidue ρ Q₂) :
    B < ρ := by
  by_contra h
  have hρB : ρ ≤ B := Nat.le_of_not_gt h
  apply hneq
  simp only [projectedResidue]
  rw [
    Nat.mod_eq_of_lt (lt_of_le_of_lt hρB hQ₁),
    Nat.mod_eq_of_lt (lt_of_le_of_lt hρB hQ₂)
  ]

/-- Quantitative form: unequal projections force the true residue to reach
at least the smaller modulus. -/
theorem projection_disagreement_forces_min_modulus_le_residue
    {ρ Q₁ Q₂ : ℕ}
    (hneq : projectedResidue ρ Q₁ ≠ projectedResidue ρ Q₂) :
    min Q₁ Q₂ ≤ ρ := by
  by_contra h
  have hρmin : ρ < min Q₁ Q₂ := Nat.lt_of_not_ge h
  have hρQ₁ : ρ < Q₁ := hρmin.trans_le (min_le_left Q₁ Q₂)
  have hρQ₂ : ρ < Q₂ := hρmin.trans_le (min_le_right Q₁ Q₂)
  apply hneq
  simp [projectedResidue, Nat.mod_eq_of_lt hρQ₁,
    Nat.mod_eq_of_lt hρQ₂]

/-- Leave-one-out specialization of the quantitative projection theorem. -/
theorem leaveOneOut_disagreement_forces_min_modulus_le_residue
    {R ρ r₁ r₂ : ℕ}
    (hneq :
      projectedResidue ρ (leaveOneOutModulus R r₁) ≠
        projectedResidue ρ (leaveOneOutModulus R r₂)) :
    min (leaveOneOutModulus R r₁) (leaveOneOutModulus R r₂) ≤ ρ :=
  projection_disagreement_forces_min_modulus_le_residue hneq

/-- Complementary projection commutes with passage from a full positive
modulus to any positive divisor.  This is the coefficient-free transport
needed to compare the global private residue with leave-one-out views. -/
theorem projectedResidue_complementaryProjectedResidue_eq_of_dvd
    {T Q R : ℕ}
    (hR : 0 < R)
    (hQ : 0 < Q)
    (hQR : Q ∣ R) :
    projectedResidue (complementaryProjectedResidue T R) Q =
      complementaryProjectedResidue T Q := by
  have hremLe : T % R ≤ R :=
    (Nat.mod_lt T hR).le
  have hmodR :
      complementaryProjectedResidue T R + T ≡ 0 [MOD R] := by
    unfold complementaryProjectedResidue projectedResidue
    calc
      (R - T % R) % R + T ≡
          (R - T % R) + T [MOD R] :=
        (Nat.mod_modEq (R - T % R) R).add_right T
      _ ≡ (R - T % R) + T % R [MOD R] :=
        Nat.ModEq.rfl.add (Nat.mod_modEq T R).symm
      _ = R := Nat.sub_add_cancel hremLe
      _ ≡ 0 [MOD R] := by simp
  exact
    projectedResidue_eq_complementary_of_add_modEq_zero
      hQ (hmodR.of_dvd hQR)

/-- If two projection moduli jointly recover the full modulus, equal
projections are not merely compatible: their common value is the full
least residue.  Thus a leave-one-out pair whose lcm is `R` has an exact
dichotomy between disagreement and a genuinely small global residue. -/
theorem projectedResidue_eq_residue_of_eq_of_lcm
    {ρ Q₁ Q₂ R : ℕ}
    (hρR : ρ < R)
    (hlcm : Nat.lcm Q₁ Q₂ = R)
    (heq : projectedResidue ρ Q₁ = projectedResidue ρ Q₂) :
    projectedResidue ρ Q₁ = ρ := by
  by_cases hQ₁ : Q₁ = 0
  · subst Q₁
    simp [projectedResidue]
  have hmod₁ :
      ρ ≡ projectedResidue ρ Q₁ [MOD Q₁] := by
    simp [projectedResidue, Nat.ModEq]
  have hmod₂ :
      ρ ≡ projectedResidue ρ Q₁ [MOD Q₂] := by
    rw [heq]
    simp [projectedResidue, Nat.ModEq]
  have hmodR :
      ρ ≡ projectedResidue ρ Q₁ [MOD R] := by
    rw [← hlcm]
    exact Nat.mod_lcm hmod₁ hmod₂
  have hprojQ₁ :
      projectedResidue ρ Q₁ < Q₁ := by
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero hQ₁)
  have hQ₁R : Q₁ ≤ R := by
    rw [← hlcm]
    have hlcmPos : 0 < Nat.lcm Q₁ Q₂ := by
      rw [hlcm]
      omega
    exact Nat.le_lcm_left Q₁ (Nat.lcm_pos_iff.mp hlcmPos).2
  have hprojR :
      projectedResidue ρ Q₁ < R :=
    hprojQ₁.trans_le hQ₁R
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hρR,
    Nat.mod_eq_of_lt hprojR] using hmodR.symm

/-- A branch-free lower certificate extracted from two projections: use
their common value when they agree, and otherwise use the smaller modulus. -/
def projectionPairFloor (ρ Q₁ Q₂ : ℕ) : ℕ :=
  if projectedResidue ρ Q₁ = projectedResidue ρ Q₂ then
    projectedResidue ρ Q₁
  else
    min Q₁ Q₂

/-- Pairing the full modulus with one positive divisor has no hidden CRT
branch: the pair floor is exactly the smaller of the full least residue and
that divisor. -/
theorem projectionPairFloor_full_divisor_eq_min
    {ρ Q R : ℕ}
    (hρR : ρ < R)
    (hQ : 0 < Q)
    (hQR : Q ∣ R) :
    projectionPairFloor ρ R Q = min ρ Q := by
  have hR : 0 < R := by omega
  have hQRle : Q ≤ R := Nat.le_of_dvd hR hQR
  unfold projectionPairFloor projectedResidue
  rw [Nat.mod_eq_of_lt hρR]
  by_cases hρQ : ρ < Q
  · rw [Nat.mod_eq_of_lt hρQ, if_pos rfl, min_eq_left hρQ.le]
  · have hQρ : Q ≤ ρ := Nat.le_of_not_gt hρQ
    have hmodLt : ρ % Q < Q := Nat.mod_lt ρ hQ
    rw [if_neg (by omega), min_eq_right hQRle, min_eq_right hQρ]

/-- A product exceeds a scaled minimum exactly when it exceeds both scaled
entries.  This elementary split is useful for exposing the two independent
arithmetic obligations hidden by a branch-free projection floor. -/
theorem lt_mul_min_iff
    {A S x y : ℕ} :
    A < S * min x y ↔ A < S * x ∧ A < S * y := by
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy]
    constructor
    · intro hx
      exact ⟨hx, hx.trans_le (Nat.mul_le_mul_left S hxy)⟩
    · exact fun h => h.1
  · rw [min_eq_right hyx]
    constructor
    · intro hy
      exact ⟨hy.trans_le (Nat.mul_le_mul_left S hyx), hy⟩
    · exact fun h => h.2

/-- When the two moduli recover `R`, the computable pair floor is always
bounded by the full least residue.  This packages the equality and
disagreement branches into one unconditional CRT certificate. -/
theorem projectionPairFloor_le_residue_of_lt_of_lcm
    {ρ Q₁ Q₂ R : ℕ}
    (hρR : ρ < R)
    (hlcm : Nat.lcm Q₁ Q₂ = R) :
    projectionPairFloor ρ Q₁ Q₂ ≤ ρ := by
  unfold projectionPairFloor
  by_cases heq :
      projectedResidue ρ Q₁ = projectedResidue ρ Q₂
  · rw [if_pos heq]
    exact
      (projectedResidue_eq_residue_of_eq_of_lcm
        hρR hlcm heq).le
  · rw [if_neg heq]
    exact projection_disagreement_forces_min_modulus_le_residue heq

/-- A congruent endpoint numerator smaller than a projection modulus is
exactly the corresponding projected residue. -/
theorem projectedResidue_eq_of_congruent_bounded
    {Z T Q B : ℕ}
    (hmod : Z ≡ T [MOD Q])
    (hZle : Z ≤ B)
    (hBQ : B < Q) :
    projectedResidue T Q = Z := by
  have hZQ : Z < Q := hZle.trans_lt hBQ
  calc
    projectedResidue T Q = T % Q := rfl
    _ = Z % Q := hmod.symm
    _ = Z := Nat.mod_eq_of_lt hZQ

/-- Congruence modulo `R` descends to every divisor `Q` of `R`, so a
bounded endpoint identifies every sufficiently large projected residue. -/
theorem large_projection_identifies_endpoint
    {Z T R Q B : ℕ}
    (hmod : Z ≡ T [MOD R])
    (hQR : Q ∣ R)
    (hZle : Z ≤ B)
    (hBQ : B < Q) :
    projectedResidue T Q = Z := by
  exact projectedResidue_eq_of_congruent_bounded
    (hmod.of_dvd hQR) hZle hBQ

/-- One projected residue above the endpoint budget excludes every positive
endpoint numerator in that budget. -/
theorem large_projection_excludes_bounded_endpoint
    {Z T R Q B : ℕ}
    (hmod : Z ≡ T [MOD R])
    (hQR : Q ∣ R)
    (hZle : Z ≤ B)
    (hBQ : B < Q)
    (hproj : B < projectedResidue T Q) :
    False := by
  have hident :=
    large_projection_identifies_endpoint hmod hQR hZle hBQ
  rw [hident] at hproj
  omega

/-- Deterministic two-projection certificate: unequal sufficiently large
projections rule out a bounded endpoint numerator congruent to the weighted
support numerator modulo the full private modulus. -/
theorem projection_disagreement_excludes_bounded_endpoint
    {Z T R Q₁ Q₂ B : ℕ}
    (hmod : Z ≡ T [MOD R])
    (hQ₁R : Q₁ ∣ R)
    (hQ₂R : Q₂ ∣ R)
    (hZle : Z ≤ B)
    (hBQ₁ : B < Q₁)
    (hBQ₂ : B < Q₂)
    (hneq : projectedResidue T Q₁ ≠ projectedResidue T Q₂) :
    False := by
  have h₁ :=
    large_projection_identifies_endpoint hmod hQ₁R hZle hBQ₁
  have h₂ :=
    large_projection_identifies_endpoint hmod hQ₂R hZle hBQ₂
  exact hneq (h₁.trans h₂.symm)

/-- Leave-one-out form consumed by the weighted private-support endpoint
construction. -/
theorem leaveOneOut_disagreement_excludes_bounded_endpoint
    {Z T R r₁ r₂ B : ℕ}
    (hmod : Z ≡ T [MOD R])
    (hr₁ : r₁ ∣ R)
    (hr₂ : r₂ ∣ R)
    (hZle : Z ≤ B)
    (hB₁ : B < leaveOneOutModulus R r₁)
    (hB₂ : B < leaveOneOutModulus R r₂)
    (hneq :
      projectedResidue T (leaveOneOutModulus R r₁) ≠
        projectedResidue T (leaveOneOutModulus R r₂)) :
    False := by
  apply projection_disagreement_excludes_bounded_endpoint
    hmod (Nat.div_dvd_of_dvd hr₁) (Nat.div_dvd_of_dvd hr₂)
    hZle hB₁ hB₂ hneq

/-- Splitting off the first omitted factorial-gap term advances the
universal tail cutoff by one. -/
theorem factorialGapTail_eq_next_add_tail (D : ℕ) :
    _root_.Erdos68.factorialGapTail D =
      (1 : ℝ) /
          (((((D + 1).factorial : ℤ) - 1 : ℤ)) : ℝ) +
        _root_.Erdos68.factorialGapTail (D + 1) := by
  let source : ℕ → ℝ := fun k =>
    (1 : ℝ) /
      ((((D + 1 + k).factorial : ℤ) - 1 : ℤ) : ℝ)
  have hsummable : Summable source := by
    have h :=
      (summable_nat_add_iff (D + 1)).2
        _root_.Erdos68.summable_one_div_factorial_sub_one
    simpa [source, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hsplit := hsummable.sum_add_tsum_nat_add 1
  rw [
    _root_.Erdos68.factorialGapTail_eq_shifted_tsum D,
    _root_.Erdos68.factorialGapTail_eq_shifted_tsum (D + 1)
  ]
  simpa [source, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    hsplit.symm

/-- Literal reciprocal-denominator index block for the prime-endpoint route:
`2, …, 2p-1`. -/
def factorialBlockIndices (p : ℕ) : Finset ℕ :=
  Finset.Icc 2 (2 * p - 1)

/-- Literal Erdős #68 reciprocal denominator. -/
def factorialGapDenominator (n : ℕ) : ℕ :=
  n.factorial - 1

/-- A prefix-private prime hit becomes genuinely unique on the tailored
factorial block with parameter `n / 2 + 1`.  The hit lies at the block's
upper endpoint when `n` is odd and one below it when `n` is even; prefix
privacy handles every earlier index and the successor lemma handles the
only possible later index. -/
theorem prefixPrivate_factorialGap_unique_in_tailoredBlock
    {q n : ℕ}
    (hq : q.Prime)
    (hn2 : 2 ≤ n)
    (hqdvd : q ∣ n.factorial - 1)
    (hprefix :
      ∀ k, 2 ≤ k → k < n →
        Nat.Coprime q (k.factorial - 1)) :
    n / 2 + 1 ≤ n ∧
      n ∈ factorialBlockIndices (n / 2 + 1) ∧
      ∀ m ∈ factorialBlockIndices (n / 2 + 1), m ≠ n →
        ¬q ∣ factorialGapDenominator m := by
  have hpLe : n / 2 + 1 ≤ n := by omega
  have hnMem :
      n ∈ factorialBlockIndices (n / 2 + 1) := by
    unfold factorialBlockIndices
    simp only [Finset.mem_Icc]
    omega
  refine ⟨hpLe, hnMem, ?_⟩
  intro m hm hmn
  have hmBounds : 2 ≤ m ∧ m ≤ 2 * (n / 2 + 1) - 1 := by
    simpa [factorialBlockIndices] using Finset.mem_Icc.mp hm
  by_cases hlt : m < n
  · unfold factorialGapDenominator
    exact hq.coprime_iff_not_dvd.mp
      (hprefix m hmBounds.1 hlt)
  · have hmEq : m = n + 1 := by omega
    simpa [factorialGapDenominator, hmEq] using
      prime_not_dvd_succ_factorial_sub_one_of_dvd hq (by omega) hqdvd

/-- The least-hit bridge therefore promotes every large shifted-factorial
prime supplied by an external source to a uniquely supported upper-half
prime on an explicit tailored endpoint block. -/
theorem exists_large_unique_factorialBlock_hit
    {q n C : ℕ}
    (hq : q.Prime)
    (hn2 : 2 ≤ n)
    (hqdvd : q ∣ n.factorial - 1)
    (hlarge : C * n < q) :
    ∃ m p, 2 ≤ m ∧ m ≤ n ∧
      p = m / 2 + 1 ∧
      C * m < q ∧
      p ≤ m ∧
      m ∈ factorialBlockIndices p ∧
      q ∣ factorialGapDenominator m ∧
      ∀ k ∈ factorialBlockIndices p, k ≠ m →
        ¬q ∣ factorialGapDenominator k := by
  obtain ⟨m, hm2, hmn, hqm, hqHit, hprefix⟩ :=
    exists_large_prefix_private_factorialGap_hit
      hq hn2 hqdvd hlarge
  obtain ⟨hpLe, hmMem, hunique⟩ :=
    prefixPrivate_factorialGap_unique_in_tailoredBlock
      hq hm2 hqHit hprefix
  exact
    ⟨m, m / 2 + 1, hm2, hmn, rfl, hqm, hpLe, hmMem,
      by simpa [factorialGapDenominator] using hqHit, hunique⟩

/-- A cofinal supply of prime divisors `q > n` of factorial gaps promotes
to cofinally many tailored blocks with a uniquely supported upper-half
prime.  The factorial threshold in the source request forces the least hit
past `2B+1`, hence its tailored block parameter past `B`. -/
theorem cofinal_unique_factorialBlock_hits_of_cofinal_large_primes
    (hsource :
      ∀ A : ℕ, ∃ q n : ℕ,
        q.Prime ∧
        2 ≤ n ∧
        A < n ∧
        q ∣ n.factorial - 1 ∧
        n < q) :
    ∀ B : ℕ, ∃ p m q : ℕ,
      B < p ∧
      q.Prime ∧
      p ≤ m ∧
      m ∈ factorialBlockIndices p ∧
      q ∣ factorialGapDenominator m ∧
      ∀ k ∈ factorialBlockIndices p, k ≠ m →
        ¬q ∣ factorialGapDenominator k := by
  intro B
  obtain ⟨q, n, hq, hn2, hnLarge, hqden, hnq⟩ :=
    hsource (2 * B + 1).factorial
  obtain ⟨m, p, hm2, _hmn, hpEq, _hmq, hpm, hmMem,
      hqm, hunique⟩ :=
    exists_large_unique_factorialBlock_hit
      (C := 1) hq hn2 hqden (by simpa using hnq)
  have hmLarge : 2 * B + 1 < m := by
    by_contra hnot
    have hmLe : m ≤ 2 * B + 1 :=
      Nat.le_of_not_gt hnot
    have hfacLe :
        m.factorial ≤ (2 * B + 1).factorial :=
      Nat.factorial_le hmLe
    have hgapPos : 0 < m.factorial - 1 := by
      have hfacLower : (2 : ℕ).factorial ≤ m.factorial :=
        Nat.factorial_le hm2
      norm_num at hfacLower
      omega
    have hqLe : q ≤ m.factorial - 1 :=
      Nat.le_of_dvd hgapPos
        (by simpa [factorialGapDenominator] using hqm)
    omega
  have hBp : B < p := by
    rw [hpEq]
    omega
  exact ⟨p, m, q, hBp, hq, hpm, hmMem, hqm, hunique⟩

/-- Distinguished predecessor-factorial denominator in the prime block. -/
def factorialBlockBase (p : ℕ) : ℕ :=
  (p - 1).factorial

/-- Actual strict-successor coefficient at the predecessor prefix, converted
to a natural number for the displayed positive endpoint numerator. -/
noncomputable def factorialBlockCoefficient (p : ℕ) : ℕ :=
  Int.toNat
    (strictFacTop
      ((factorialGapPrefix (p - 1) : ℚ) : ℝ)
      (p - 1))

/-- Full literal common denominator `L_p`. -/
def factorialBlockEndpointLcm (p : ℕ) : ℕ :=
  endpointDenominatorLcm
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

/-- Literal collision core `C_p`. -/
def factorialBlockCollisionCore (p : ℕ) : ℕ :=
  collisionCore
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

/-- Collision core after cancelling the forced predecessor-factorial base. -/
def factorialBlockNormalizedCollisionCore (p : ℕ) : ℕ :=
  factorialBlockCollisionCore p / factorialBlockBase p

/-- Product of the upper factorial block `p⋯(2p-1)`, which remains after
cancelling `(p-1)!` from `(2p-1)!`. -/
def factorialBlockUpperDescFactorial (p : ℕ) : ℕ :=
  (2 * p - 1).descFactorial p

/-- Literal private modulus `R_p = L_p / C_p`. -/
def factorialBlockPrivateModulus (p : ℕ) : ℕ :=
  privateModulus
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

/-- Common-denominator reciprocal-tail numerator `T_p`. -/
def factorialBlockTailNumerator (p : ℕ) : ℕ :=
  endpointTailNumerator
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

/-- Positive predecessor contribution to the displayed block numerator. -/
noncomputable def factorialBlockBaseNumerator (p : ℕ) : ℕ :=
  endpointBaseNumerator
    (factorialBlockCoefficient p)
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

/-- Literal displayed endpoint numerator `Z_p`. -/
noncomputable def factorialBlockEndpointNumerator (p : ℕ) : ℕ :=
  endpointNumerator
    (factorialBlockCoefficient p)
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

/-- Literal least private-modulus residue `ρ_p`. -/
noncomputable def factorialBlockPrivateResidue (p : ℕ) : ℕ :=
  endpointPrivateResidue
    (factorialBlockCoefficient p)
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

/-- Literal private quotient owned by the factorial-gap denominator at
index `n`. -/
def factorialBlockPrivateQuotient (p n : ℕ) : ℕ :=
  privateQuotient
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator n

/-- Once the growing predecessor-factorial base passes a fixed
factorial-gap denominator, that denominator divides the base. -/
theorem factorialGapDenominator_dvd_factorialBlockBase_of_lt
    {p n : ℕ}
    (hn : 2 ≤ n)
    (hlt : factorialGapDenominator n < p) :
    factorialGapDenominator n ∣ factorialBlockBase p := by
  have hgapPos :
      0 < factorialGapDenominator n := by
    unfold factorialGapDenominator
    exact Nat.sub_pos_of_lt ((Nat.one_lt_factorial).2 hn)
  unfold factorialBlockBase
  exact Nat.dvd_factorial hgapPos (by omega)

/-- Every fixed factorial-gap owner is eventually absorbed by the growing
base: for all `p > n! - 1`, its literal private quotient is exactly one.
Thus a cofinal two-owner argument must use indices (or prime factors)
escaping with the block parameter rather than a fixed pair seen in a finite
scan. -/
theorem factorialBlockPrivateQuotient_eq_one_of_gap_lt
    {p n : ℕ}
    (hn : 2 ≤ n)
    (hlt : factorialGapDenominator n < p) :
    factorialBlockPrivateQuotient p n = 1 := by
  have hgapPos :
      0 < factorialGapDenominator n := by
    unfold factorialGapDenominator
    exact Nat.sub_pos_of_lt ((Nat.one_lt_factorial).2 hn)
  unfold factorialBlockPrivateQuotient
  exact privateQuotient_eq_one_of_dvd_base
    hgapPos
    (factorialGapDenominator_dvd_factorialBlockBase_of_lt hn hlt)

/-- Contrapositive form of fixed-owner absorption: a nontrivial private
quotient can survive only while the block parameter has not passed its
source denominator. -/
theorem factorialBlockParameter_le_gap_of_privateQuotient_ne_one
    {p n : ℕ}
    (hn : 2 ≤ n)
    (hne : factorialBlockPrivateQuotient p n ≠ 1) :
    p ≤ factorialGapDenominator n := by
  by_contra hnot
  exact hne
    (factorialBlockPrivateQuotient_eq_one_of_gap_lt
      hn (Nat.lt_of_not_ge hnot))

/-- Direct fixed-pair no-go form: after the block parameter passes the two
source denominators, both private quotients are simultaneously absorbed.
-/
theorem factorialBlockFixedPairPrivateQuotients_eq_one
    {p i j : ℕ}
    (hi : 2 ≤ i)
    (hj : 2 ≤ j)
    (hlt :
      max (factorialGapDenominator i)
          (factorialGapDenominator j) < p) :
    factorialBlockPrivateQuotient p i = 1 ∧
      factorialBlockPrivateQuotient p j = 1 := by
  constructor
  · exact factorialBlockPrivateQuotient_eq_one_of_gap_lt hi
      (lt_of_le_of_lt (le_max_left _ _) hlt)
  · exact factorialBlockPrivateQuotient_eq_one_of_gap_lt hj
      (lt_of_le_of_lt (le_max_right _ _) hlt)

/-- Literal projection modulus obtained by deleting the private quotient
owned by index `n` from the full private modulus. -/
def factorialBlockLeaveOneOutModulus (p n : ℕ) : ℕ :=
  leaveOneOutModulus
    (factorialBlockPrivateModulus p)
    (factorialBlockPrivateQuotient p n)

/-- Literal projection modulus obtained by deleting any selected divisor
of the full private modulus.  This factor-level view can split one owner's
private quotient into several CRT channels. -/
def factorialBlockFactorProjectionModulus (p a : ℕ) : ℕ :=
  leaveOneOutModulus (factorialBlockPrivateModulus p) a

/-- Literal one-owner term attached to index `n` in the private CRT
projection of the factorial block. -/
def factorialBlockPrivateOwnerTerm (p n : ℕ) : ℕ :=
  privateWeight
      (factorialBlockBase p)
      (factorialBlockIndices p)
      factorialGapDenominator n *
    ((factorialBlockIndices p).erase n).prod
      (privateQuotient
        (factorialBlockBase p)
        (factorialBlockIndices p)
        factorialGapDenominator)

/-- Exact scale `2p²(2p-1)!` in the integral endpoint closing test. -/
def factorialBlockScale (p : ℕ) : ℕ :=
  2 * p ^ 2 * (2 * p - 1).factorial

/-- Exact budget numerator `2p+1` in the endpoint upper bound. -/
def factorialBlockBudget (p : ℕ) : ℕ :=
  2 * p + 1

/-- Literal rational endpoint gap
`K_{p-1}/(p-1)! - s_{2p-1}`. -/
noncomputable def factorialBlockEndpointGap (p : ℕ) : ℚ :=
  (factorialBlockCoefficient p : ℚ) / factorialBlockBase p -
    factorialGapPrefix (2 * p - 1)

/-- Literal Archimedean endpoint allowance
`(2p+1)/(2p²(2p-1)!)`. -/
def factorialBlockEndpointUpperBound (p : ℕ) : ℚ :=
  (factorialBlockBudget p : ℚ) / factorialBlockScale p

/-- The actual tail beyond `2p-1` lies below the literal prime-block
allowance.  Splitting off the first term gains the factor missing from the
coarser bound `tail D < 1/D!`. -/
theorem factorialGapTail_lt_factorialBlockEndpointUpperBound
    {p : ℕ}
    (hp : 2 ≤ p) :
    _root_.Erdos68.factorialGapTail (2 * p - 1) <
      (factorialBlockEndpointUpperBound p : ℝ) := by
  have htwoP : 2 ≤ 2 * p := by omega
  have htailNext :=
    _root_.Erdos68.factorialGapTail_lt_one_div_factorial htwoP
  have hsplit :=
    factorialGapTail_eq_next_add_tail (2 * p - 1)
  have hsucc : 2 * p - 1 + 1 = 2 * p := by omega
  have htailTwoTerm :
      _root_.Erdos68.factorialGapTail (2 * p - 1) <
        (1 : ℝ) /
            ((((2 * p).factorial : ℤ) - 1 : ℤ) : ℝ) +
          1 / (((2 * p).factorial : ℕ) : ℝ) := by
    rw [hsplit, hsucc]
    exact add_lt_add_right htailNext _
  have hcastSub :
      ((((2 * p).factorial : ℤ) - 1 : ℤ) : ℝ) =
        ((2 * p).factorial : ℝ) - 1 := by
    norm_num
  rw [hcastSub] at htailTwoTerm
  have hfacNat :
      (2 * p).factorial =
        2 * p * (2 * p - 1).factorial := by
    calc
      (2 * p).factorial =
          (2 * p - 1 + 1).factorial := by congr 1 <;> omega
      _ = (2 * p - 1 + 1) *
          (2 * p - 1).factorial := Nat.factorial_succ _
      _ = 2 * p * (2 * p - 1).factorial := by
        congr 1 <;> omega
  have hfacGeNat :
      p + 1 ≤ (2 * p).factorial := by
    calc
      p + 1 ≤ 2 * p := by omega
      _ ≤ (2 * p).factorial := Nat.self_le_factorial _
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hfacR : (0 : ℝ) < (2 * p).factorial := by positivity
  have hfacSubR : (0 : ℝ) < (2 * p).factorial - 1 := by
    have hfacGtNat : 1 < (2 * p).factorial :=
      Nat.one_lt_factorial.mpr htwoP
    have hfacGtR :
        (1 : ℝ) < ((2 * p).factorial : ℝ) := by
      exact_mod_cast hfacGtNat
    linarith
  have hfacGeR :
      (p : ℝ) + 1 ≤ ((2 * p).factorial : ℝ) := by
    exact_mod_cast hfacGeNat
  have hscaleEq :
      (factorialBlockScale p : ℝ) =
        (p : ℝ) * ((2 * p).factorial : ℝ) := by
    unfold factorialBlockScale
    rw [hfacNat]
    push_cast
    ring
  have hbudgetEq :
      (factorialBlockBudget p : ℝ) =
        2 * (p : ℝ) + 1 := by
    unfold factorialBlockBudget
    push_cast
    ring
  have htwoTermLe :
      (1 : ℝ) / (((2 * p).factorial : ℝ) - 1) +
          1 / ((2 * p).factorial : ℝ) ≤
        (2 * (p : ℝ) + 1) /
          ((p : ℝ) * ((2 * p).factorial : ℝ)) := by
    have hfacNe :
        ((2 * p).factorial : ℝ) ≠ 0 :=
      ne_of_gt hfacR
    have hfacSubNe :
        ((2 * p).factorial : ℝ) - 1 ≠ 0 :=
      ne_of_gt hfacSubR
    have hsumEq :
        (1 : ℝ) / (((2 * p).factorial : ℝ) - 1) +
            1 / ((2 * p).factorial : ℝ) =
          (2 * ((2 * p).factorial : ℝ) - 1) /
            ((((2 * p).factorial : ℝ) - 1) *
              ((2 * p).factorial : ℝ)) := by
      field_simp [hfacNe, hfacSubNe]
      ring
    rw [
      hsumEq,
      div_le_div_iff₀
        (mul_pos hfacSubR hfacR)
        (mul_pos hpR hfacR)
    ]
    have hnonneg :
        0 ≤ ((2 * p).factorial : ℝ) *
          (((2 * p).factorial : ℝ) - (p : ℝ) - 1) :=
      mul_nonneg hfacR.le (by linarith)
    nlinarith
  apply htailTwoTerm.trans_le
  rw [show
    (factorialBlockEndpointUpperBound p : ℝ) =
      (factorialBlockBudget p : ℝ) /
        (factorialBlockScale p : ℝ) by
      unfold factorialBlockEndpointUpperBound
      push_cast
      rfl]
  rw [hscaleEq, hbudgetEq]
  exact htwoTermLe

/-- The newly added `2p`-th factorial-gap term plus one full `2p`-factorial
grid cell still fits inside the prime-block endpoint allowance. -/
theorem factorialBlock_addedTerm_add_gridCell_le_endpointUpperBound
    {p : ℕ}
    (hp : 2 ≤ p) :
    (1 : ℝ) / (((2 * p).factorial : ℝ) - 1) +
        1 / ((2 * p).factorial : ℝ) ≤
      (factorialBlockEndpointUpperBound p : ℝ) := by
  have htwoP : 2 ≤ 2 * p := by omega
  have hfacNat :
      (2 * p).factorial =
        2 * p * (2 * p - 1).factorial := by
    calc
      (2 * p).factorial =
          (2 * p - 1 + 1).factorial := by congr 1 <;> omega
      _ = (2 * p - 1 + 1) *
          (2 * p - 1).factorial := Nat.factorial_succ _
      _ = 2 * p * (2 * p - 1).factorial := by
        congr 1 <;> omega
  have hfacGeNat :
      p + 1 ≤ (2 * p).factorial := by
    calc
      p + 1 ≤ 2 * p := by omega
      _ ≤ (2 * p).factorial := Nat.self_le_factorial _
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hfacR : (0 : ℝ) < (2 * p).factorial := by positivity
  have hfacSubR : (0 : ℝ) < (2 * p).factorial - 1 := by
    have hfacGtNat : 1 < (2 * p).factorial :=
      Nat.one_lt_factorial.mpr htwoP
    have hfacGtR :
        (1 : ℝ) < ((2 * p).factorial : ℝ) := by
      exact_mod_cast hfacGtNat
    linarith
  have hfacGeR :
      (p : ℝ) + 1 ≤ ((2 * p).factorial : ℝ) := by
    exact_mod_cast hfacGeNat
  have hscaleEq :
      (factorialBlockScale p : ℝ) =
        (p : ℝ) * ((2 * p).factorial : ℝ) := by
    unfold factorialBlockScale
    rw [hfacNat]
    push_cast
    ring
  have hbudgetEq :
      (factorialBlockBudget p : ℝ) =
        2 * (p : ℝ) + 1 := by
    unfold factorialBlockBudget
    push_cast
    ring
  have hsumEq :
      (1 : ℝ) / (((2 * p).factorial : ℝ) - 1) +
          1 / ((2 * p).factorial : ℝ) =
        (2 * ((2 * p).factorial : ℝ) - 1) /
          ((((2 * p).factorial : ℝ) - 1) *
            ((2 * p).factorial : ℝ)) := by
    field_simp [ne_of_gt hfacR, ne_of_gt hfacSubR]
    ring
  have htwoTermLe :
      (1 : ℝ) / (((2 * p).factorial : ℝ) - 1) +
          1 / ((2 * p).factorial : ℝ) ≤
        (2 * (p : ℝ) + 1) /
          ((p : ℝ) * ((2 * p).factorial : ℝ)) := by
    rw [
      hsumEq,
      div_le_div_iff₀
        (mul_pos hfacSubR hfacR)
        (mul_pos hpR hfacR)
    ]
    nlinarith
  rw [show
    (factorialBlockEndpointUpperBound p : ℝ) =
      (factorialBlockBudget p : ℝ) /
        (factorialBlockScale p : ℝ) by
      unfold factorialBlockEndpointUpperBound
      push_cast
      rfl]
  rw [hscaleEq, hbudgetEq]
  exact htwoTermLe

/-- The exact positive endpoint window targeted by a full prime block. -/
def factorialBlockEndpointWindow (p : ℕ) : Prop :=
  0 < factorialBlockEndpointGap p ∧
    factorialBlockEndpointGap p ≤
      factorialBlockEndpointUpperBound p

/-- The strict successor of every genuine factorial-gap prefix is a
positive integer. -/
theorem strictFacTop_factorialGapPrefix_pos
    (n : ℕ) :
    (0 : ℤ) <
      strictFacTop ((factorialGapPrefix n : ℚ) : ℝ) n := by
  have hprefixQ :
      (0 : ℚ) ≤ factorialGapPrefix n := by
    unfold factorialGapPrefix
    apply Finset.sum_nonneg
    intro k _
    exact one_div_nonneg.mpr (show
      (0 : ℚ) ≤ (k.factorial : ℚ) - 1 by
        have hfac : 1 ≤ k.factorial :=
          Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
        have hfacQ : (1 : ℚ) ≤ (k.factorial : ℚ) := by
          exact_mod_cast hfac
        linarith)
  have hprefixR :
      (0 : ℝ) ≤ ((factorialGapPrefix n : ℚ) : ℝ) := by
    exact_mod_cast hprefixQ
  have hbounds :=
    strictFacTop_div_factorial_bounds
      ((factorialGapPrefix n : ℚ) : ℝ) n
  have hquotPos :
      (0 : ℝ) <
        (strictFacTop
            ((factorialGapPrefix n : ℚ) : ℝ) n : ℝ) /
          (n.factorial : ℝ) :=
    hprefixR.trans_lt hbounds.1
  have hfacPos : (0 : ℝ) < n.factorial := by positivity
  have hstrictR :
      (0 : ℝ) <
        (strictFacTop
          ((factorialGapPrefix n : ℚ) : ℝ) n : ℝ) := by
    rcases (div_pos_iff.mp hquotPos) with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hfacPos.le hneg.2).elim
  exact_mod_cast hstrictR

/-- The natural coefficient wrapper does not alter the positive strict
successor at the predecessor prefix. -/
theorem factorialBlockCoefficient_cast_eq_strictFacTop
    {p : ℕ} :
    (factorialBlockCoefficient p : ℤ) =
      strictFacTop
        ((factorialGapPrefix (p - 1) : ℚ) : ℝ)
        (p - 1) := by
  unfold factorialBlockCoefficient
  simpa using Int.toNat_of_nonneg
    (strictFacTop_factorialGapPrefix_pos (p - 1)).le

/-- If every strict-successor carry from `p` through `2p` is the unit
carry, the normalized strict successor stays fixed across the whole block.
The final prefix is then trapped in the literal prime-block endpoint
window. -/
theorem factorialBlockEndpointWindow_of_unitCarryBlock
    {p : ℕ}
    (hp : 3 ≤ p)
    (hunit :
      ∀ m ∈ Finset.Icc p (2 * p),
        factorialGapStepCarry m = 1) :
    factorialBlockEndpointWindow p := by
  let A : ℕ → ℝ := fun n =>
    (strictFacTop
          ((factorialGapPrefix n : ℚ) : ℝ) n : ℝ) /
      (n.factorial : ℝ)
  have hconstAux :
      ∀ k : ℕ, k ≤ p + 1 →
        A (p - 1 + k) = A (p - 1) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp
    | succ k ih =>
        intro hk
        let m := p - 1 + (k + 1)
        have hm3 : 3 ≤ m := by
          dsimp [m]
          omega
        have hmMem : m ∈ Finset.Icc p (2 * p) := by
          apply Finset.mem_Icc.mpr
          dsimp [m]
          omega
        have hstep :=
          strictFacTop_factorialGapPrefix_div_factorial_step
            (m := m) hm3
        have hcarry := hunit m hmMem
        rw [hcarry] at hstep
        norm_num at hstep
        have hmPred :
            m - 1 = p - 1 + k := by
          dsimp [m]
        change A m = A (m - 1) at hstep
        rw [hmPred] at hstep
        exact hstep.trans (ih (by omega))
  have hAeq :
      A (2 * p) = A (p - 1) := by
    have h := hconstAux (p + 1) (by omega)
    have hindex : p - 1 + (p + 1) = 2 * p := by omega
    simpa [hindex] using h
  have hcoeffInt :=
    factorialBlockCoefficient_cast_eq_strictFacTop (p := p)
  have hcoeffReal :
      (factorialBlockCoefficient p : ℝ) =
        (strictFacTop
          ((factorialGapPrefix (p - 1) : ℚ) : ℝ)
          (p - 1) : ℝ) := by
    exact_mod_cast hcoeffInt
  have hgapReal :
      ((factorialBlockEndpointGap p : ℚ) : ℝ) =
        A (2 * p) -
          ((factorialGapPrefix (2 * p - 1) : ℚ) : ℝ) := by
    unfold factorialBlockEndpointGap factorialBlockBase
    push_cast
    rw [hcoeffReal]
    change
      A (p - 1) -
          ((factorialGapPrefix (2 * p - 1) : ℚ) : ℝ) =
        A (2 * p) -
          ((factorialGapPrefix (2 * p - 1) : ℚ) : ℝ)
    rw [hAeq]
  have htwoP : 2 ≤ 2 * p := by omega
  have hprefixStep :
      ((factorialGapPrefix (2 * p) : ℚ) : ℝ) =
        ((factorialGapPrefix (2 * p - 1) : ℚ) : ℝ) +
          1 / (((2 * p).factorial : ℝ) - 1) := by
    exact_mod_cast
      (factorialGapPrefix_eq_prev_add (τ := 2 * p) htwoP)
  have hbounds :=
    strictFacTop_div_factorial_bounds
      ((factorialGapPrefix (2 * p) : ℚ) : ℝ) (2 * p)
  change
    ((factorialGapPrefix (2 * p) : ℚ) : ℝ) < A (2 * p) ∧
      A (2 * p) ≤
        ((factorialGapPrefix (2 * p) : ℚ) : ℝ) +
          1 / ((2 * p).factorial : ℝ) at hbounds
  have hgapPosR :
      (0 : ℝ) <
        ((factorialBlockEndpointGap p : ℚ) : ℝ) := by
    have hbounds' := hbounds
    rw [hprefixStep] at hbounds'
    have hfacGt :
        (1 : ℝ) < ((2 * p).factorial : ℝ) := by
      exact_mod_cast
        (Nat.one_lt_factorial.mpr (show 2 ≤ 2 * p by omega))
    have htermPos :
        (0 : ℝ) <
          1 / (((2 * p).factorial : ℝ) - 1) :=
      one_div_pos.mpr (by linarith)
    rw [hgapReal]
    linarith [hbounds'.1, htermPos]
  have hgapUpperR :
      ((factorialBlockEndpointGap p : ℚ) : ℝ) ≤
        (factorialBlockEndpointUpperBound p : ℝ) := by
    have hbounds' := hbounds
    rw [hprefixStep] at hbounds'
    rw [hgapReal]
    exact
      (show
          A (2 * p) -
                ((factorialGapPrefix (2 * p - 1) : ℚ) : ℝ) ≤
                1 / (((2 * p).factorial : ℝ) - 1) +
                1 / ((2 * p).factorial : ℝ) by
            linarith [hbounds'.2]).trans
        (factorialBlock_addedTerm_add_gridCell_le_endpointUpperBound
          (p := p) (by omega))
  constructor
  · exact_mod_cast hgapPosR
  · exact_mod_cast hgapUpperR

/-- If a displayed rational denominator already clears at `(p-1)!`, then
the literal strict-successor endpoint is the series itself.  Consequently
its gap above the prefix through `2p-1` is exactly the analytic tail and
lies in the endpoint window consumed by the private-projection criteria. -/
theorem factorialBlockEndpointWindow_of_series_eq_rat
    {p q : ℕ}
    {a : ℤ}
    (hp : 3 ≤ p)
    (hq : 0 < q)
    (hqp : q ≤ p - 1)
    (hseries :
      _root_.Erdos68.factorialGapSeries =
        (a : ℝ) / (q : ℝ)) :
    factorialBlockEndpointWindow p := by
  have hn : 2 ≤ p - 1 := by omega
  have hstrict :=
    strictFacTop_factorialGapPrefix_eq_cleared_rational
      hn hq hqp hseries
  have hdecompTwo :=
    _root_.Erdos68.factorialGapSeries_eq_sum_add_tail
      (D := 2) (by omega)
  have htwoSum :
      (∑ d ∈ Finset.Icc 2 2,
          (1 : ℝ) /
            ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))) = 1 := by
    norm_num
  have htailTwoPos :=
    _root_.Erdos68.factorialGapTail_pos (D := 2) (by omega)
  have hseriesPos :
      0 < _root_.Erdos68.factorialGapSeries := by
    rw [hdecompTwo, htwoSum]
    linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by
    rw [hseries] at hseriesPos
    rcases (div_pos_iff.mp hseriesPos) with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hqR.le hneg.2).elim
  have ha : (0 : ℤ) < a := by exact_mod_cast haR
  have hqDvd :
      q ∣ factorialBlockBase p := by
    unfold factorialBlockBase
    exact Nat.dvd_factorial hq hqp
  have hqMul :
      q * (factorialBlockBase p / q) =
        factorialBlockBase p :=
    Nat.mul_div_cancel' hqDvd
  have hquotPos :
      0 < factorialBlockBase p / q := by
    by_contra hnot
    have hzero :
        factorialBlockBase p / q = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hzero, Nat.mul_zero] at hqMul
    have hbasePos :
        0 < factorialBlockBase p := by
      unfold factorialBlockBase
      exact Nat.factorial_pos _
    omega
  have hstrictPos :
      (0 : ℤ) <
        strictFacTop
          ((factorialGapPrefix (p - 1) : ℚ) : ℝ)
          (p - 1) := by
    rw [hstrict]
    exact mul_pos (by exact_mod_cast hquotPos) ha
  have hcoeffInt :
      (factorialBlockCoefficient p : ℤ) =
        strictFacTop
          ((factorialGapPrefix (p - 1) : ℚ) : ℝ)
          (p - 1) := by
    unfold factorialBlockCoefficient
    simpa using Int.toNat_of_nonneg hstrictPos.le
  have hcoeffReal :
      (factorialBlockCoefficient p : ℝ) =
        (((factorialBlockBase p / q : ℕ) : ℤ) * a : ℤ) := by
    calc
      (factorialBlockCoefficient p : ℝ) =
          ((factorialBlockCoefficient p : ℤ) : ℝ) := by norm_num
      _ =
          (strictFacTop
            ((factorialGapPrefix (p - 1) : ℚ) : ℝ)
            (p - 1) : ℝ) := by rw [hcoeffInt]
      _ =
          ((((factorialBlockBase p / q : ℕ) : ℤ) * a : ℤ) : ℝ) := by
        rw [hstrict]
        unfold factorialBlockBase
        rfl
  have hqMulR :
      (q : ℝ) *
          ((factorialBlockBase p / q : ℕ) : ℝ) =
        (factorialBlockBase p : ℝ) := by
    exact_mod_cast hqMul
  have hratioEq :
      (factorialBlockCoefficient p : ℝ) /
          (factorialBlockBase p : ℝ) =
        _root_.Erdos68.factorialGapSeries := by
    have hbaseR :
        (0 : ℝ) < factorialBlockBase p := by
      unfold factorialBlockBase
      positivity
    rw [hseries]
    apply (div_eq_iff (ne_of_gt hbaseR)).2
    rw [hcoeffReal]
    norm_num only [Int.cast_mul, Int.cast_natCast]
    rw [← hqMulR]
    field_simp [ne_of_gt hqR]
  have hD : 2 ≤ 2 * p - 1 := by omega
  have hdecomp :=
    _root_.Erdos68.factorialGapSeries_eq_sum_add_tail hD
  have hprefix := factorialGapPrefix_cast (2 * p - 1)
  have hgapReal :
      ((factorialBlockEndpointGap p : ℚ) : ℝ) =
        _root_.Erdos68.factorialGapTail (2 * p - 1) := by
    unfold factorialBlockEndpointGap
    push_cast
    rw [hratioEq, hdecomp, ← hprefix]
    ring
  have htailPos :=
    _root_.Erdos68.factorialGapTail_pos hD
  have htailUpper :=
    factorialGapTail_lt_factorialBlockEndpointUpperBound
      (p := p) (by omega)
  constructor
  · exact_mod_cast (show
      (0 : ℝ) <
        ((factorialBlockEndpointGap p : ℚ) : ℝ) by
          rw [hgapReal]
          exact htailPos)
  · exact_mod_cast (show
      ((factorialBlockEndpointGap p : ℚ) : ℝ) ≤
        ((factorialBlockEndpointUpperBound p : ℚ) : ℝ) by
          rw [hgapReal]
          exact htailUpper.le)

/-- Casting a literal factorial-gap denominator into the rationals
recovers the denominator appearing in the Erdős #68 prefix. -/
theorem factorialGapDenominator_cast
    {n : ℕ} :
    (factorialGapDenominator n : ℚ) =
      (n.factorial : ℚ) - 1 := by
  unfold factorialGapDenominator
  rw [Nat.cast_sub (Nat.succ_le_of_lt (Nat.factorial_pos n))]
  norm_num

/-- The reciprocal sum over the literal prime block is exactly the actual
factorial-gap prefix through `2p-1`. -/
theorem factorialBlock_reciprocalSum_eq_factorialGapPrefix
    {p : ℕ} :
    (∑ n ∈ factorialBlockIndices p,
        1 / (factorialGapDenominator n : ℚ)) =
      factorialGapPrefix (2 * p - 1) := by
  unfold factorialBlockIndices factorialGapPrefix
  apply Finset.sum_congr rfl
  intro n _
  rw [factorialGapDenominator_cast]

/-- Every literal block denominator is positive. -/
theorem factorialGapDenominator_pos_of_mem
    {p n : ℕ}
    (hn : n ∈ factorialBlockIndices p) :
    0 < factorialGapDenominator n := by
  have hn2 : 2 ≤ n :=
    (Finset.mem_Icc.mp hn).1
  exact Nat.sub_pos_of_lt ((Nat.one_lt_factorial).2 hn2)

/-- The literal private modulus is always positive. -/
theorem factorialBlockPrivateModulus_pos
    {p : ℕ} :
    0 < factorialBlockPrivateModulus p := by
  unfold factorialBlockPrivateModulus
  apply privateModulus_pos
  intro n hn
  exact factorialGapDenominator_pos_of_mem hn

/-- Literal factorial-block specialization of the normalized collision
product/lcm bound. -/
theorem
    factorialBlockNormalizedCollisionCore_mul_gapLcm_dvd_gapProd
    {p : ℕ} :
    factorialBlockNormalizedCollisionCore p *
        (factorialBlockIndices p).lcm factorialGapDenominator ∣
      (factorialBlockIndices p).prod factorialGapDenominator := by
  unfold factorialBlockNormalizedCollisionCore
  apply
    collisionCore_div_base_mul_denominatorLcm_dvd_denominatorProd
  · unfold factorialBlockBase
    exact Nat.factorial_pos _
  · intro n hn
    exact factorialGapDenominator_pos_of_mem hn

/-- Explicit upper-bound form of the factorial-block product/lcm
divisibility.  Any stronger lower estimate for the literal factorial-gap
lcm now feeds directly into an upper estimate for the normalized collision
core. -/
theorem factorialBlockNormalizedCollisionCore_le_gapProd_div_gapLcm
    {p : ℕ} :
    factorialBlockNormalizedCollisionCore p ≤
      (factorialBlockIndices p).prod factorialGapDenominator /
        (factorialBlockIndices p).lcm factorialGapDenominator := by
  have hLpos :
      0 <
        (factorialBlockIndices p).lcm
          factorialGapDenominator :=
    Nat.pos_of_ne_zero ((Finset.lcm_ne_zero_iff).2 fun n hn =>
      (factorialGapDenominator_pos_of_mem hn).ne')
  have hPpos :
      0 <
        (factorialBlockIndices p).prod
          factorialGapDenominator :=
    Finset.prod_pos fun n hn =>
      factorialGapDenominator_pos_of_mem hn
  apply (Nat.le_div_iff_mul_le hLpos).2
  exact Nat.le_of_dvd hPpos
    factorialBlockNormalizedCollisionCore_mul_gapLcm_dvd_gapProd

/-- The normalized factorial-block collision core is always positive. -/
theorem factorialBlockNormalizedCollisionCore_pos
    {p : ℕ} :
    0 < factorialBlockNormalizedCollisionCore p := by
  have hbase : 0 < factorialBlockBase p := by
    unfold factorialBlockBase
    exact Nat.factorial_pos _
  have hpos :
      ∀ n ∈ factorialBlockIndices p,
        0 < factorialGapDenominator n := by
    intro n hn
    exact factorialGapDenominator_pos_of_mem hn
  have hpairPos :
      0 <
        pairwiseCollisionCore
          (factorialBlockIndices p)
          factorialGapDenominator :=
    pairwiseCollisionCore_pos hpos
  have hgPos :
      0 <
        Nat.gcd
          (factorialBlockBase p)
          (pairwiseCollisionCore
            (factorialBlockIndices p)
            factorialGapDenominator) :=
    Nat.gcd_pos_of_pos_left _ hbase
  have hgLe :
      Nat.gcd
          (factorialBlockBase p)
          (pairwiseCollisionCore
            (factorialBlockIndices p)
            factorialGapDenominator) ≤
        pairwiseCollisionCore
          (factorialBlockIndices p)
          factorialGapDenominator :=
    Nat.le_of_dvd hpairPos
      (Nat.gcd_dvd_right _ _)
  unfold factorialBlockNormalizedCollisionCore
    factorialBlockCollisionCore
  rw [collisionCore_div_base_eq_pairwiseCollisionCore_div_gcd hbase]
  exact Nat.div_pos hgLe hgPos

/-- The factorial-block normalized collision valuation is exactly the
pairwise repeated-support valuation above the amount already carried by
the predecessor-factorial base.  This is the valuation interface for
prime-power incidence estimates. -/
theorem factorialBlockNormalizedCollisionCore_factorization
    {p q : ℕ} :
    (factorialBlockNormalizedCollisionCore p).factorization q =
      (pairwiseCollisionCore
          (factorialBlockIndices p)
          factorialGapDenominator).factorization q -
        (factorialBlockBase p).factorization q := by
  unfold factorialBlockNormalizedCollisionCore
    factorialBlockCollisionCore
  apply collisionCore_div_base_factorization
  · unfold factorialBlockBase
    exact Nat.factorial_pos _
  · intro n hn
    exact factorialGapDenominator_pos_of_mem hn

/-- A normalized factorial-block prime power is exactly a repeated
factorial-gap hit at the exponent obtained by adding the full
predecessor-factorial base valuation.  This is the direct bridge from
normalized collision growth to prime-power incidence estimates. -/
theorem
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_two_hits
    {p q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e) :
    q ^ e ∣ factorialBlockNormalizedCollisionCore p ↔
      ∃ i ∈ factorialBlockIndices p,
        ∃ j ∈ factorialBlockIndices p,
          i ≠ j ∧
          q ^ (e + (factorialBlockBase p).factorization q) ∣
            factorialGapDenominator i ∧
          q ^ (e + (factorialBlockBase p).factorization q) ∣
            factorialGapDenominator j := by
  have hbasePos : 0 < factorialBlockBase p := by
    unfold factorialBlockBase
    exact Nat.factorial_pos _
  have hpos :
      ∀ n ∈ factorialBlockIndices p,
        0 < factorialGapDenominator n := by
    intro n hn
    exact factorialGapDenominator_pos_of_mem hn
  unfold factorialBlockNormalizedCollisionCore
    factorialBlockCollisionCore
  rw [
    primePower_dvd_collisionCore_div_base_iff hq he hbasePos hpos,
    primePower_dvd_pairwiseCollisionCore_iff hq (by omega) hpos
  ]

/-- Any prime power shared by two displayed factorial gaps is at most the
power of the later index whose exponent is their separation.  This is the
pairwise metric form of the factorial-gap gcd bound. -/
theorem factorialBlock_primePower_le_gapPow_of_two_hits
    {p q e i j : ℕ}
    (hi : i ∈ factorialBlockIndices p)
    (hij : i < j)
    (hiPow : q ^ e ∣ factorialGapDenominator i)
    (hjPow : q ^ e ∣ factorialGapDenominator j) :
    q ^ e ≤ j ^ (j - i) := by
  have hqGcd :
      q ^ e ∣ Nat.gcd (i.factorial - 1) (j.factorial - 1) := by
    exact Nat.dvd_gcd
      (by simpa [factorialGapDenominator] using hiPow)
      (by simpa [factorialGapDenominator] using hjPow)
  have hiGapPos : 0 < i.factorial - 1 := by
    simpa [factorialGapDenominator] using
      factorialGapDenominator_pos_of_mem hi
  have hGcdPos :
      0 < Nat.gcd (i.factorial - 1) (j.factorial - 1) :=
    Nat.gcd_pos_of_pos_left _ hiGapPos
  have hGcdLe :
      Nat.gcd (i.factorial - 1) (j.factorial - 1) ≤
        j ^ (j - i) :=
    _root_.Erdos68.gcd_factorial_sub_one_le_pow_gap
      (Finset.mem_Icc.mp hi).1 hij
  exact (Nat.le_of_dvd hGcdPos hqGcd).trans hGcdLe

/-- Prime-power hits are universally farther apart than their exponent.
No block-endpoint hypothesis is needed: a prime dividing `j! - 1` is
automatically larger than `j`, and the factorial-gap gcd bound then
compares `q^e` with `j^(j-i)`. -/
theorem factorialBlock_prime_hitPair_distance_gt_exponent
    {p q e i j : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hi : i ∈ factorialBlockIndices p)
    (hij : i < j)
    (hiPow : q ^ e ∣ factorialGapDenominator i)
    (hjPow : q ^ e ∣ factorialGapDenominator j) :
    e < j - i := by
  have hpairBound :
      q ^ e ≤ j ^ (j - i) :=
    factorialBlock_primePower_le_gapPow_of_two_hits hi hij hiPow hjPow
  have hqDvdGap :
      q ∣ factorialGapDenominator j :=
    (dvd_pow_self q he.ne').trans hjPow
  have hjLtQ : j < q := by
    apply prime_dvd_factorial_sub_one_gt hq
    simpa [factorialGapDenominator] using hqDvdGap
  by_contra hnot
  have hdistanceLe : j - i ≤ e :=
    Nat.le_of_not_gt hnot
  have hgapPowLe :
      j ^ (j - i) ≤ j ^ e :=
    Nat.pow_le_pow_right (by omega) hdistanceLe
  have hjPowLtQPow :
      j ^ e < q ^ e :=
    Nat.pow_lt_pow_left hjLtQ he.ne'
  exact (not_lt_of_ge (hpairBound.trans hgapPowLe)) hjPowLtQPow

/-- Above the displayed block endpoint, every pair of `q^e` factorial-gap
hits—not merely one selected pair—is separated by more than `e` indices.
This is the universal packing interface for bounding high prime-power hit
counts inside a factorial block. -/
theorem factorialBlock_hitPair_distance_gt_exponent_of_endpoint_lt_base
    {p q e i j : ℕ}
    (he : 0 < e)
    (hendpoint : 2 * p - 1 < q)
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p)
    (hij : i < j)
    (hiPow : q ^ e ∣ factorialGapDenominator i)
    (hjPow : q ^ e ∣ factorialGapDenominator j) :
    e < j - i := by
  have hpairBound :
      q ^ e ≤ j ^ (j - i) :=
    factorialBlock_primePower_le_gapPow_of_two_hits hi hij hiPow hjPow
  have hjBounds : 2 ≤ j ∧ j ≤ 2 * p - 1 :=
    Finset.mem_Icc.mp hj
  have hjLtQ : j < q :=
    hjBounds.2.trans_lt hendpoint
  by_contra hnot
  have hdistanceLe : j - i ≤ e :=
    Nat.le_of_not_gt hnot
  have hgapPowLe :
      j ^ (j - i) ≤ j ^ e :=
    Nat.pow_le_pow_right (by omega) hdistanceLe
  have hjPowLtQPow :
      j ^ e < q ^ e :=
    Nat.pow_lt_pow_left hjLtQ he.ne'
  exact (not_lt_of_ge (hpairBound.trans hgapPowLe)) hjPowLtQPow

/-- Quantitative packing consequence of universal hit spacing.  When the
power base exceeds the block endpoint, thickening every `q^e`-hit by the
interval of length `e+1` starting there produces disjoint intervals inside
`[2, 2p-1+e]`.  Hence the number of hits times `e+1` is bounded by the
length `2p+e-2` of that enlarged block. -/
theorem factorialBlock_primePowerHitCount_mul_succ_le_of_endpoint_lt_base
    {p q e : ℕ}
    (hp : 2 ≤ p)
    (he : 0 < e)
    (hendpoint : 2 * p - 1 < q) :
    ((factorialBlockIndices p).filter fun i =>
        q ^ e ∣ factorialGapDenominator i).card * (e + 1) ≤
      2 * p + e - 2 := by
  let hits :=
    (factorialBlockIndices p).filter fun i =>
      q ^ e ∣ factorialGapDenominator i
  have hdisjoint :
      (hits : Set ℕ).PairwiseDisjoint fun i =>
        Finset.Icc i (i + e) := by
    intro i hi j hj hij
    have hi' : i ∈ hits := hi
    have hj' : j ∈ hits := hj
    have hiData := Finset.mem_filter.mp hi'
    have hjData := Finset.mem_filter.mp hj'
    refine Finset.disjoint_left.2 ?_
    intro x hxi hxj
    have hxiBounds := Finset.mem_Icc.mp hxi
    have hxjBounds := Finset.mem_Icc.mp hxj
    rcases lt_or_gt_of_ne hij with hijLt | hjiLt
    · have hspacing :
          e < j - i :=
        factorialBlock_hitPair_distance_gt_exponent_of_endpoint_lt_base
          he hendpoint hiData.1 hjData.1 hijLt hiData.2 hjData.2
      omega
    · have hspacing :
          e < i - j :=
        factorialBlock_hitPair_distance_gt_exponent_of_endpoint_lt_base
          he hendpoint hjData.1 hiData.1 hjiLt hjData.2 hiData.2
      omega
  have hunionSubset :
      hits.biUnion (fun i => Finset.Icc i (i + e)) ⊆
        Finset.Icc 2 (2 * p - 1 + e) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    have hiBlock :
        i ∈ factorialBlockIndices p :=
      (Finset.mem_filter.mp hi).1
    have hiBounds := Finset.mem_Icc.mp hiBlock
    have hxiBounds := Finset.mem_Icc.mp hxi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hintervalCard :
      ∀ i : ℕ, (Finset.Icc i (i + e)).card = e + 1 := by
    intro i
    rw [Nat.card_Icc]
    omega
  calc
    hits.card * (e + 1) =
        ∑ i ∈ hits, (Finset.Icc i (i + e)).card := by
      simp [hintervalCard]
    _ = (hits.biUnion fun i => Finset.Icc i (i + e)).card :=
      (Finset.card_biUnion hdisjoint).symm
    _ ≤ (Finset.Icc 2 (2 * p - 1 + e)).card :=
      Finset.card_le_card hunionSubset
    _ = 2 * p + e - 2 := by
      rw [Nat.card_Icc]
      omega

/-- Universal prime-power packing bound.  For a prime base, the automatic
inequality `j < q` at every factorial-gap hit removes the endpoint
hypothesis from the preceding estimate. -/
theorem factorialBlock_primePowerHitCount_mul_succ_le
    {p q e : ℕ}
    (hp : 2 ≤ p)
    (hq : q.Prime)
    (he : 0 < e) :
    ((factorialBlockIndices p).filter fun i =>
        q ^ e ∣ factorialGapDenominator i).card * (e + 1) ≤
      2 * p + e - 2 := by
  let hits :=
    (factorialBlockIndices p).filter fun i =>
      q ^ e ∣ factorialGapDenominator i
  have hdisjoint :
      (hits : Set ℕ).PairwiseDisjoint fun i =>
        Finset.Icc i (i + e) := by
    intro i hi j hj hij
    have hi' : i ∈ hits := hi
    have hj' : j ∈ hits := hj
    have hiData := Finset.mem_filter.mp hi'
    have hjData := Finset.mem_filter.mp hj'
    refine Finset.disjoint_left.2 ?_
    intro x hxi hxj
    have hxiBounds := Finset.mem_Icc.mp hxi
    have hxjBounds := Finset.mem_Icc.mp hxj
    rcases lt_or_gt_of_ne hij with hijLt | hjiLt
    · have hspacing :
        e < j - i :=
      factorialBlock_prime_hitPair_distance_gt_exponent
          hq he hiData.1 hijLt hiData.2 hjData.2
      omega
    · have hspacing :
        e < i - j :=
      factorialBlock_prime_hitPair_distance_gt_exponent
          hq he hjData.1 hjiLt hjData.2 hiData.2
      omega
  have hunionSubset :
      hits.biUnion (fun i => Finset.Icc i (i + e)) ⊆
        Finset.Icc 2 (2 * p - 1 + e) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    have hiBlock :
        i ∈ factorialBlockIndices p :=
      (Finset.mem_filter.mp hi).1
    have hiBounds := Finset.mem_Icc.mp hiBlock
    have hxiBounds := Finset.mem_Icc.mp hxi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hintervalCard :
      ∀ i : ℕ, (Finset.Icc i (i + e)).card = e + 1 := by
    intro i
    rw [Nat.card_Icc]
    omega
  calc
    hits.card * (e + 1) =
        ∑ i ∈ hits, (Finset.Icc i (i + e)).card := by
      simp [hintervalCard]
    _ = (hits.biUnion fun i => Finset.Icc i (i + e)).card :=
      (Finset.card_biUnion hdisjoint).symm
    _ ≤ (Finset.Icc 2 (2 * p - 1 + e)).card :=
      Finset.card_le_card hunionSubset
    _ = 2 * p + e - 2 := by
      rw [Nat.card_Icc]
      omega

/-- Distance-sensitive witness for a normalized collision prime power.
The full surviving exponent together with the predecessor-factorial base
valuation divides two displayed gaps, hence is bounded by the intervening
descending-factorial collision cost.  This is the explicit pair-spacing
interface behind general-modulus factorial-hit estimates. -/
theorem
    exists_factorialBlock_hitPair_with_normalizedPrimePower_le_gapPow
    {p q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpow : q ^ e ∣ factorialBlockNormalizedCollisionCore p) :
    ∃ i ∈ factorialBlockIndices p,
      ∃ j ∈ factorialBlockIndices p,
        i < j ∧
          q ^ (e + (factorialBlockBase p).factorization q) ∣
            factorialGapDenominator i ∧
          q ^ (e + (factorialBlockBase p).factorization q) ∣
            factorialGapDenominator j ∧
          q ^ (e + (factorialBlockBase p).factorization q) ≤
            j ^ (j - i) := by
  obtain ⟨i, hi, j, hj, hij, hiPow, hjPow⟩ :=
    (factorialBlock_primePower_dvd_normalizedCollisionCore_iff_two_hits
      (p := p) (q := q) (e := e) hq he).1 hpow
  rcases lt_or_gt_of_ne hij with hijLt | hjiLt
  · exact ⟨i, hi, j, hj, hijLt, hiPow, hjPow,
      factorialBlock_primePower_le_gapPow_of_two_hits
        hi hijLt hiPow hjPow⟩
  · exact ⟨j, hj, i, hi, hjiLt, hjPow, hiPow,
      factorialBlock_primePower_le_gapPow_of_two_hits
        hj hjiLt hjPow hiPow⟩

/-- A normalized collision prime power that exceeds the `d`-th power of the
block endpoint can only be witnessed by hits more than `d` indices apart.
Thus a source-level bound on the spacing of prime-power factorial hits gives
exactly the kind of collision exclusion needed by the private-modulus route. -/
theorem
    exists_factorialBlock_hitPair_distance_gt_of_endpointPow_lt_normalizedPrimePower
    {p q e d : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpow : q ^ e ∣ factorialBlockNormalizedCollisionCore p)
    (hlarge :
      (2 * p - 1) ^ d <
        q ^ (e + (factorialBlockBase p).factorization q)) :
    ∃ i ∈ factorialBlockIndices p,
      ∃ j ∈ factorialBlockIndices p,
        i < j ∧
          d < j - i ∧
          q ^ (e + (factorialBlockBase p).factorization q) ∣
            factorialGapDenominator i ∧
          q ^ (e + (factorialBlockBase p).factorization q) ∣
            factorialGapDenominator j := by
  obtain ⟨i, hi, j, hj, hij, hiPow, hjPow, hpairBound⟩ :=
    exists_factorialBlock_hitPair_with_normalizedPrimePower_le_gapPow
      hq he hpow
  have hjBounds : 2 ≤ j ∧ j ≤ 2 * p - 1 :=
    Finset.mem_Icc.mp hj
  have hendpointPos : 0 < 2 * p - 1 := by omega
  have hdistance : d < j - i := by
    by_contra hnot
    have hdistanceLe : j - i ≤ d := Nat.le_of_not_gt hnot
    have hjPowLeEndpointPow :
        j ^ (j - i) ≤ (2 * p - 1) ^ (j - i) :=
      Nat.pow_le_pow_left hjBounds.2 _
    have hgapPowLeCap :
        (2 * p - 1) ^ (j - i) ≤ (2 * p - 1) ^ d :=
      Nat.pow_le_pow_right hendpointPos hdistanceLe
    exact (not_lt_of_ge (hpairBound.trans
      (hjPowLeEndpointPow.trans hgapPowLeCap))) hlarge
  exact ⟨i, hi, j, hj, hij, hdistance, hiPow, hjPow⟩

/-- Exact excess-exponent ceiling for a normalized collision prime power.
The surviving exponent plus the full predecessor-factorial valuation stays
strictly below `q`; otherwise `q^q` would divide a displayed gap `i! - 1`,
while every such `q`-hit has `i < q` and hence `i! - 1 < q^q`. -/
theorem
    factorialBlock_normalizedCollision_exponent_add_base_factorization_lt_prime
    {p q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpow : q ^ e ∣ factorialBlockNormalizedCollisionCore p) :
    e + (factorialBlockBase p).factorization q < q := by
  obtain ⟨i, hi, _j, _hj, _hij, hiHigh, _hjHigh⟩ :=
    (factorialBlock_primePower_dvd_normalizedCollisionCore_iff_two_hits
      (p := p) (q := q) (e := e) hq he).1 hpow
  have hqDvdGap :
      q ∣ factorialGapDenominator i :=
    (dvd_pow_self q (by omega)).trans hiHigh
  have hiq : i < q := by
    apply prime_dvd_factorial_sub_one_gt hq
    simpa [factorialGapDenominator] using hqDvdGap
  by_contra hnot
  have hqLeExponent :
      q ≤ e + (factorialBlockBase p).factorization q :=
    Nat.le_of_not_gt hnot
  have hqPowDvdHigh :
      q ^ q ∣
        q ^ (e + (factorialBlockBase p).factorization q) :=
    pow_dvd_pow q hqLeExponent
  have hqPowDvdGap :
      q ^ q ∣ factorialGapDenominator i :=
    hqPowDvdHigh.trans hiHigh
  have hgapPos :
      0 < factorialGapDenominator i :=
    factorialGapDenominator_pos_of_mem hi
  have hqPowLeGap :
      q ^ q ≤ factorialGapDenominator i :=
    Nat.le_of_dvd hgapPos hqPowDvdGap
  have hgapLtFac :
      factorialGapDenominator i < i.factorial := by
    unfold factorialGapDenominator
    have hfacPos : 0 < i.factorial :=
      Nat.factorial_pos i
    omega
  have hiPowLe :
      i ^ i ≤ q ^ q :=
    (Nat.pow_le_pow_left hiq.le i).trans
      (Nat.pow_le_pow_right hq.pos hiq.le)
  have hgapLtPow :
      factorialGapDenominator i < q ^ q :=
    hgapLtFac.trans_le
      ((Nat.factorial_le_pow i).trans hiPowLe)
  exact (not_lt_of_ge hqPowLeGap) hgapLtPow

/-- Primewise form of the exact excess-exponent ceiling: the complete
normalized-core valuation plus the predecessor-factorial valuation is
strictly smaller than the prime itself. -/
theorem
    factorialBlock_normalizedCollision_factorization_add_base_lt_prime
    {p q : ℕ}
    (hq : q.Prime)
    (hdiv : q ∣ factorialBlockNormalizedCollisionCore p) :
    (factorialBlockNormalizedCollisionCore p).factorization q +
        (factorialBlockBase p).factorization q < q := by
  have hcoreNe :
      factorialBlockNormalizedCollisionCore p ≠ 0 :=
    factorialBlockNormalizedCollisionCore_pos.ne'
  have he :
      0 <
        (factorialBlockNormalizedCollisionCore p).factorization q :=
    hq.factorization_pos_of_dvd hcoreNe hdiv
  have hpow :
      q ^ (factorialBlockNormalizedCollisionCore p).factorization q ∣
        factorialBlockNormalizedCollisionCore p :=
    (hq.pow_dvd_iff_le_factorization hcoreNe).2 le_rfl
  exact
    factorialBlock_normalizedCollision_exponent_add_base_factorization_lt_prime
      hq he hpow

/-- Global block-diameter ceiling for every normalized collision prime.
The complete surviving exponent and the predecessor-factorial base
valuation occur together in two displayed gaps.  Universal prime-hit
spacing therefore bounds their sum by the diameter of `[2,2p-1]`,
without any assumption that `q` lies above the endpoint. -/
theorem
    factorialBlock_normalizedCollision_exponent_add_base_factorization_lt_blockDiameter
    {p q e : ℕ}
    (hp : 2 ≤ p)
    (hq : q.Prime)
    (he : 0 < e)
    (hpow : q ^ e ∣ factorialBlockNormalizedCollisionCore p) :
    e + (factorialBlockBase p).factorization q <
      2 * p - 3 := by
  obtain ⟨i, hi, j, hj, hij, hiPow, hjPow⟩ :=
    (factorialBlock_primePower_dvd_normalizedCollisionCore_iff_two_hits
      (p := p) (q := q) (e := e) hq he).1 hpow
  rcases lt_or_gt_of_ne hij with hijLt | hjiLt
  · have hspacing :
        e + (factorialBlockBase p).factorization q < j - i :=
      factorialBlock_prime_hitPair_distance_gt_exponent
        hq (by omega) hi hijLt hiPow hjPow
    have hiBounds := Finset.mem_Icc.mp hi
    have hjBounds := Finset.mem_Icc.mp hj
    omega
  · have hspacing :
        e + (factorialBlockBase p).factorization q < i - j :=
      factorialBlock_prime_hitPair_distance_gt_exponent
        hq (by omega) hj hjiLt hjPow hiPow
    have hiBounds := Finset.mem_Icc.mp hi
    have hjBounds := Finset.mem_Icc.mp hj
    omega

/-- Primewise form of the global diameter ceiling.  For every prime in
the normalized core, its complete normalized valuation plus its full
base valuation is strictly smaller than `2p-3`. -/
theorem
    factorialBlock_normalizedCollision_factorization_add_base_lt_blockDiameter
    {p q : ℕ}
    (hp : 2 ≤ p)
    (hq : q.Prime)
    (hdiv : q ∣ factorialBlockNormalizedCollisionCore p) :
    (factorialBlockNormalizedCollisionCore p).factorization q +
        (factorialBlockBase p).factorization q <
      2 * p - 3 := by
  have hcoreNe :
      factorialBlockNormalizedCollisionCore p ≠ 0 :=
    factorialBlockNormalizedCollisionCore_pos.ne'
  have he :
      0 <
        (factorialBlockNormalizedCollisionCore p).factorization q :=
    hq.factorization_pos_of_dvd hcoreNe hdiv
  have hpow :
      q ^ (factorialBlockNormalizedCollisionCore p).factorization q ∣
        factorialBlockNormalizedCollisionCore p :=
    (hq.pow_dvd_iff_le_factorization hcoreNe).2 le_rfl
  exact
    factorialBlock_normalizedCollision_exponent_add_base_factorization_lt_blockDiameter
      hp hq he hpow

/-- For a collision prime above the entire displayed block, the complete
normalized valuation is bounded by the block diameter, not merely by the
prime.  Indeed the full valuation survives as a prime power, while the
predecessor-factorial base has zero `q`-valuation.  The resulting repeated
hits must be farther apart than that valuation, but both lie in
`[2, 2p-1]`.  This is the valuation cutoff naturally matched to
least-prime-factor inputs with `2p-1 < q`. -/
theorem
    factorialBlock_normalizedCollision_factorization_lt_blockDiameter_of_endpoint_lt_prime
    {p q : ℕ}
    (hq : q.Prime)
    (hendpoint : 2 * p - 1 < q)
    (hdiv : q ∣ factorialBlockNormalizedCollisionCore p) :
    (factorialBlockNormalizedCollisionCore p).factorization q <
      2 * p - 3 := by
  have hcoreNe :
      factorialBlockNormalizedCollisionCore p ≠ 0 :=
    factorialBlockNormalizedCollisionCore_pos.ne'
  have hvaluationPos :
      0 < (factorialBlockNormalizedCollisionCore p).factorization q :=
    hq.factorization_pos_of_dvd hcoreNe hdiv
  have hpow :
      q ^ (factorialBlockNormalizedCollisionCore p).factorization q ∣
        factorialBlockNormalizedCollisionCore p :=
    (hq.pow_dvd_iff_le_factorization hcoreNe).2 le_rfl
  have hqNotBase : ¬q ∣ factorialBlockBase p := by
    unfold factorialBlockBase
    rw [Nat.Prime.dvd_factorial hq]
    omega
  have hbaseZero :
      (factorialBlockBase p).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqNotBase
  have hlarge :
      (2 * p - 1) ^
          (factorialBlockNormalizedCollisionCore p).factorization q <
        q ^ ((factorialBlockNormalizedCollisionCore p).factorization q +
          (factorialBlockBase p).factorization q) := by
    rw [hbaseZero, add_zero]
    exact Nat.pow_lt_pow_left hendpoint hvaluationPos.ne'
  obtain ⟨i, hi, j, hj, _hij, hdistance, _hiPow, _hjPow⟩ :=
    exists_factorialBlock_hitPair_distance_gt_of_endpointPow_lt_normalizedPrimePower
      hq hvaluationPos hpow hlarge
  have hiBounds : 2 ≤ i ∧ i ≤ 2 * p - 1 :=
    Finset.mem_Icc.mp hi
  have hjBounds : 2 ≤ j ∧ j ≤ 2 * p - 1 :=
    Finset.mem_Icc.mp hj
  have hdiameter : j - i ≤ 2 * p - 3 := by omega
  exact hdistance.trans_le hdiameter

/-- Prime-support specialization of the exact excess-exponent ceiling. -/
theorem
    factorialBlock_base_factorization_lt_pred_of_dvd_normalizedCollisionCore
    {p q : ℕ}
    (hq : q.Prime)
    (hdiv : q ∣ factorialBlockNormalizedCollisionCore p) :
    (factorialBlockBase p).factorization q < q - 1 := by
  have hqOne :
      q ^ 1 ∣ factorialBlockNormalizedCollisionCore p := by
    simpa using hdiv
  have hceiling :=
    factorialBlock_normalizedCollision_exponent_add_base_factorization_lt_prime
      hq (by omega) hqOne
  omega

/-- Every prime surviving predecessor-factorial normalization lies above
the sharp factorial-channel square-root threshold.  If
`q * (q - 1) ≤ p - 1`, then `q^(q-1)` already divides `(p - 1)!`,
contradicting the exact local valuation ceiling. -/
theorem
    factorialBlock_prime_mul_pred_gt_pred_of_dvd_normalizedCollisionCore
    {p q : ℕ}
    (hq : q.Prime)
    (hdiv : q ∣ factorialBlockNormalizedCollisionCore p) :
    p - 1 < q * (q - 1) := by
  by_contra hnot
  have hqmul : q * (q - 1) ≤ p - 1 :=
    Nat.le_of_not_gt hnot
  have hqDvdQfac : q ∣ q.factorial :=
    Nat.dvd_factorial hq.pos le_rfl
  have hqPowDvdQfacPow :
      q ^ (q - 1) ∣ q.factorial ^ (q - 1) :=
    pow_dvd_pow_of_dvd hqDvdQfac (q - 1)
  have hqfacPowDvd :
      q.factorial ^ (q - 1) ∣
        (q * (q - 1)).factorial := by
    have hfloor : q * (q - 1) / q = q - 1 := by
      simpa [Nat.mul_comm] using Nat.mul_div_left (q - 1) hq.pos
    simpa [hfloor] using
      (factorial_pow_floor_dvd_factorial (q * (q - 1)) q hq.pos)
  have hmulFacDvdBase :
      (q * (q - 1)).factorial ∣ factorialBlockBase p := by
    unfold factorialBlockBase
    exact Nat.factorial_dvd_factorial hqmul
  have hqPowDvdBase :
      q ^ (q - 1) ∣ factorialBlockBase p :=
    hqPowDvdQfacPow.trans
      (hqfacPowDvd.trans hmulFacDvdBase)
  have hbasePos : 0 < factorialBlockBase p := by
    unfold factorialBlockBase
    exact Nat.factorial_pos _
  have hqLeBaseVal :
      q - 1 ≤ (factorialBlockBase p).factorization q :=
    (hq.pow_dvd_iff_le_factorization hbasePos.ne').1
      hqPowDvdBase
  exact
    (not_lt_of_ge hqLeBaseVal)
      (factorialBlock_base_factorization_lt_pred_of_dvd_normalizedCollisionCore
        hq hdiv)

/-- Coarser square form of the sharp normalized-collision cutoff. -/
theorem factorialBlock_prime_sq_gt_pred_of_dvd_normalizedCollisionCore
    {p q : ℕ}
    (hq : q.Prime)
    (hdiv : q ∣ factorialBlockNormalizedCollisionCore p) :
    p - 1 < q ^ 2 := by
  have hsharp :=
    factorialBlock_prime_mul_pred_gt_pred_of_dvd_normalizedCollisionCore
      hq hdiv
  have hmulLeSq : q * (q - 1) ≤ q ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_left q (Nat.sub_le q 1)
  exact hsharp.trans_le hmulLeSq

/-- The normalized collision core has no prime support in any complete
factorial channel lying below the sharp cutoff. -/
theorem factorialBlockNormalizedCollisionCore_coprime_factorial_of_mul_pred_le
    {p k : ℕ}
    (hcut : k * (k - 1) ≤ p - 1) :
    Nat.Coprime
      (factorialBlockNormalizedCollisionCore p)
      k.factorial := by
  by_contra hnot
  obtain ⟨q, hq, hqCore, hqFac⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hqLe : q ≤ k :=
    hq.dvd_factorial.mp hqFac
  have hqPredLe : q - 1 ≤ k - 1 := by
    omega
  have hqMulLe :
      q * (q - 1) ≤ k * (k - 1) :=
    Nat.mul_le_mul hqLe hqPredLe
  have hlarge :
      p - 1 < q * (q - 1) :=
    factorialBlock_prime_mul_pred_gt_pred_of_dvd_normalizedCollisionCore
      hq hqCore
  exact (not_lt_of_ge (hqMulLe.trans hcut)) hlarge

/-- The predecessor-factorial base is a literal factor of the collision
core, so the normalized core reconstructs it without truncation. -/
theorem factorialBlockBase_mul_normalizedCollisionCore
    {p : ℕ} :
    factorialBlockBase p *
        factorialBlockNormalizedCollisionCore p =
      factorialBlockCollisionCore p := by
  unfold factorialBlockNormalizedCollisionCore
  exact Nat.mul_div_cancel' (by
    unfold factorialBlockCollisionCore collisionCore
    exact Nat.dvd_lcm_left _ _)

/-- Exact factorial cancellation across the prime block. -/
theorem factorialBlockBase_mul_upperDescFactorial
    {p : ℕ}
    (hp : 0 < p) :
    factorialBlockBase p *
        factorialBlockUpperDescFactorial p =
      (2 * p - 1).factorial := by
  have hle : p ≤ 2 * p - 1 := by omega
  have hsub : 2 * p - 1 - p = p - 1 := by omega
  simpa [
    factorialBlockBase,
    factorialBlockUpperDescFactorial,
    hsub
  ] using Nat.factorial_mul_descFactorial hle

/-- Base cancellation for arbitrary selected factors of the private
modulus.  The deleted factors need not be complete owner quotients. -/
theorem factorialBlock_factorCollisionCap_of_normalizedCollisionCap
    {p a b : ℕ}
    (hp : 0 < p)
    (hcap :
      factorialBlockBudget p *
            factorialBlockNormalizedCollisionCore p *
          max a b <
        2 * p ^ 2 * factorialBlockUpperDescFactorial p) :
    factorialBlockBudget p *
          factorialBlockCollisionCore p *
        max a b <
      factorialBlockScale p := by
  have hbasePos :
      0 < factorialBlockBase p := by
    unfold factorialBlockBase
    exact Nat.factorial_pos _
  have hmul :=
    (Nat.mul_lt_mul_left hbasePos).2 hcap
  calc
    factorialBlockBudget p *
          factorialBlockCollisionCore p *
        max a b =
        factorialBlockBase p *
          (factorialBlockBudget p *
              factorialBlockNormalizedCollisionCore p *
            max a b) := by
        rw [← factorialBlockBase_mul_normalizedCollisionCore]
        ac_rfl
    _ <
        factorialBlockBase p *
          (2 * p ^ 2 * factorialBlockUpperDescFactorial p) :=
      hmul
    _ = factorialBlockScale p := by
      rw [factorialBlockScale,
        ← factorialBlockBase_mul_upperDescFactorial hp]
      ac_rfl

/-- Cancelling the forced `(p-1)!` factor reduces the collision-cap
comparison to the normalized collision core against the upper factorial
block `p⋯(2p-1)`. -/
theorem factorialBlock_collisionCap_of_normalizedCollisionCap
    {p i j : ℕ}
    (hp : 0 < p)
    (hcap :
      factorialBlockBudget p *
            factorialBlockNormalizedCollisionCore p *
          max
            (factorialBlockPrivateQuotient p i)
            (factorialBlockPrivateQuotient p j) <
        2 * p ^ 2 * factorialBlockUpperDescFactorial p) :
    factorialBlockBudget p *
          factorialBlockCollisionCore p *
        max
          (factorialBlockPrivateQuotient p i)
          (factorialBlockPrivateQuotient p j) <
      factorialBlockScale p := by
  have hbasePos :
      0 < factorialBlockBase p := by
    unfold factorialBlockBase
    exact Nat.factorial_pos _
  have hmul :=
    (Nat.mul_lt_mul_left hbasePos).2 hcap
  calc
    factorialBlockBudget p *
          factorialBlockCollisionCore p *
        max
          (factorialBlockPrivateQuotient p i)
          (factorialBlockPrivateQuotient p j) =
        factorialBlockBase p *
          (factorialBlockBudget p *
              factorialBlockNormalizedCollisionCore p *
            max
              (factorialBlockPrivateQuotient p i)
              (factorialBlockPrivateQuotient p j)) := by
        rw [← factorialBlockBase_mul_normalizedCollisionCore]
        ac_rfl
    _ <
        factorialBlockBase p *
          (2 * p ^ 2 * factorialBlockUpperDescFactorial p) :=
      hmul
    _ = factorialBlockScale p := by
      rw [factorialBlockScale,
        ← factorialBlockBase_mul_upperDescFactorial hp]
      ac_rfl

/-- The collision core and private modulus exactly factor the literal
endpoint lcm. -/
theorem factorialBlockCollisionCore_mul_privateModulus
    {p : ℕ} :
    factorialBlockCollisionCore p *
        factorialBlockPrivateModulus p =
      factorialBlockEndpointLcm p := by
  unfold factorialBlockCollisionCore
    factorialBlockPrivateModulus
    factorialBlockEndpointLcm
  rw [privateModulus_eq_endpointDenominatorLcm_div_collisionCore
    (base := factorialBlockBase p)
    (s := factorialBlockIndices p)
    (d := factorialGapDenominator)
    (Nat.factorial_pos _)
    (fun n hn => factorialGapDenominator_pos_of_mem hn)]
  exact Nat.mul_div_cancel'
    collisionCore_dvd_endpointDenominatorLcm

/-- Dividing the explicit tail numerator by the private modulus exposes
the collision core times the exact factorial-gap prefix. -/
theorem factorialBlockTailNumerator_div_privateModulus_eq_collisionScaledPrefix
    {p : ℕ} :
    (factorialBlockTailNumerator p : ℚ) /
        factorialBlockPrivateModulus p =
      (factorialBlockCollisionCore p : ℚ) *
        factorialGapPrefix (2 * p - 1) := by
  have htail :=
    endpointTailNumerator_div_endpointDenominatorLcm
      (base := factorialBlockBase p)
      (s := factorialBlockIndices p)
      (d := factorialGapDenominator)
      (Nat.factorial_pos _)
      (fun n hn => factorialGapDenominator_pos_of_mem hn)
  rw [factorialBlock_reciprocalSum_eq_factorialGapPrefix] at htail
  have hR :
      (factorialBlockPrivateModulus p : ℚ) ≠ 0 := by
    exact_mod_cast
      (factorialBlockPrivateModulus_pos (p := p)).ne'
  have hC :
      (factorialBlockCollisionCore p : ℚ) ≠ 0 := by
    unfold factorialBlockCollisionCore
    exact_mod_cast
      (collisionCore_pos
        (Nat.factorial_pos _)
        (fun n hn => factorialGapDenominator_pos_of_mem hn)).ne'
  have hfactor :
      (factorialBlockCollisionCore p : ℚ) *
          (factorialBlockPrivateModulus p : ℚ) =
        (factorialBlockEndpointLcm p : ℚ) := by
    exact_mod_cast
      (factorialBlockCollisionCore_mul_privateModulus (p := p))
  calc
    (factorialBlockTailNumerator p : ℚ) /
          factorialBlockPrivateModulus p =
        (factorialBlockTailNumerator p : ℚ) /
            factorialBlockEndpointLcm p *
          factorialBlockCollisionCore p := by
            rw [← hfactor]
            field_simp
    _ =
        (factorialBlockCollisionCore p : ℚ) *
          factorialGapPrefix (2 * p - 1) := by
            have htailLiteral :
                (factorialBlockTailNumerator p : ℚ) /
                    factorialBlockEndpointLcm p =
                  factorialGapPrefix (2 * p - 1) := by
              simpa [
                factorialBlockTailNumerator,
                factorialBlockEndpointLcm
              ] using htail
            rw [htailLiteral]
            ring

/-- The literal block tail numerator is coprime to the literal private
modulus. -/
theorem factorialBlockTailNumerator_coprime_privateModulus
    {p : ℕ} :
    Nat.Coprime
      (factorialBlockTailNumerator p)
      (factorialBlockPrivateModulus p) := by
  unfold factorialBlockTailNumerator factorialBlockPrivateModulus
  rw [endpointTailNumerator_eq_collisionWeightedPrivateNumerator
    (base := factorialBlockBase p)
    (s := factorialBlockIndices p)
    (d := factorialGapDenominator)
    (Nat.factorial_pos _)
    (fun n hn => factorialGapDenominator_pos_of_mem hn)]
  exact collisionWeightedPrivateNumerator_coprime_privateModulus
    (fun n hn => factorialGapDenominator_pos_of_mem hn)

/-- The normalized complementary tail residue is exactly the gap from the
collision-scaled factorial-gap prefix to its next integer. -/
theorem factorialBlock_complementaryTailFraction_eq_ceilingGap
    {p : ℕ}
    (hR : 1 < factorialBlockPrivateModulus p) :
    (complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) : ℚ) /
        factorialBlockPrivateModulus p =
      (((factorialBlockTailNumerator p /
            factorialBlockPrivateModulus p + 1 : ℕ) : ℚ) -
        (factorialBlockCollisionCore p : ℚ) *
          factorialGapPrefix (2 * p - 1)) := by
  have hcop :=
    factorialBlockTailNumerator_coprime_privateModulus (p := p)
  have hsum :=
    add_complementaryProjectedResidue_eq_succ_div_mul hR hcop
  have hRNe :
      (factorialBlockPrivateModulus p : ℚ) ≠ 0 := by
    exact_mod_cast (show
      factorialBlockPrivateModulus p ≠ 0 by omega)
  have hsumQ :
      (factorialBlockTailNumerator p : ℚ) /
            factorialBlockPrivateModulus p +
          (complementaryProjectedResidue
              (factorialBlockTailNumerator p)
              (factorialBlockPrivateModulus p) : ℚ) /
            factorialBlockPrivateModulus p =
        ((factorialBlockTailNumerator p /
              factorialBlockPrivateModulus p + 1 : ℕ) : ℚ) := by
    rw [← add_div]
    rw [← Nat.cast_add]
    rw [hsum]
    push_cast
    field_simp
  rw [
    factorialBlockTailNumerator_div_privateModulus_eq_collisionScaledPrefix
  ] at hsumQ
  linarith

/-- A lower bound for the collision-scaled prefix's gap to its next integer
is exactly strong enough to imply the original integral complementary
residue inequality. -/
theorem factorialBlock_globalComplementaryTail_inequality_of_ceilingGap
    {p : ℕ}
    (hR : 1 < factorialBlockPrivateModulus p)
    (hgap :
      ((factorialBlockBudget p *
            factorialBlockCollisionCore p : ℕ) : ℚ) <
        (factorialBlockScale p : ℚ) *
          (((factorialBlockTailNumerator p /
                factorialBlockPrivateModulus p + 1 : ℕ) : ℚ) -
            (factorialBlockCollisionCore p : ℚ) *
              factorialGapPrefix (2 * p - 1))) :
    factorialBlockBudget p *
          factorialBlockEndpointLcm p <
      factorialBlockScale p *
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) := by
  rw [
    ← factorialBlock_complementaryTailFraction_eq_ceilingGap hR
  ] at hgap
  have hRPosQ :
      (0 : ℚ) < factorialBlockPrivateModulus p := by
    exact_mod_cast (show
      0 < factorialBlockPrivateModulus p by omega)
  have hgap' :
      ((factorialBlockBudget p *
            factorialBlockCollisionCore p : ℕ) : ℚ) <
        ((factorialBlockScale p *
              complementaryProjectedResidue
                (factorialBlockTailNumerator p)
                (factorialBlockPrivateModulus p) : ℕ) : ℚ) /
          factorialBlockPrivateModulus p := by
    calc
      ((factorialBlockBudget p *
            factorialBlockCollisionCore p : ℕ) : ℚ) <
          (factorialBlockScale p : ℚ) *
            ((complementaryProjectedResidue
                  (factorialBlockTailNumerator p)
                  (factorialBlockPrivateModulus p) : ℚ) /
              factorialBlockPrivateModulus p) :=
        hgap
      _ =
          ((factorialBlockScale p *
                complementaryProjectedResidue
                  (factorialBlockTailNumerator p)
                  (factorialBlockPrivateModulus p) : ℕ) : ℚ) /
            factorialBlockPrivateModulus p := by
        push_cast
        ring
  have hmul :=
    (lt_div_iff₀ hRPosQ).mp hgap'
  have hfactorQ :
      (factorialBlockCollisionCore p : ℚ) *
          factorialBlockPrivateModulus p =
        factorialBlockEndpointLcm p := by
    exact_mod_cast
      (factorialBlockCollisionCore_mul_privateModulus (p := p))
  have hlargeQ :
      ((factorialBlockBudget p *
            factorialBlockEndpointLcm p : ℕ) : ℚ) <
        ((factorialBlockScale p *
              complementaryProjectedResidue
                (factorialBlockTailNumerator p)
                (factorialBlockPrivateModulus p) : ℕ) : ℚ) := by
    calc
      ((factorialBlockBudget p *
            factorialBlockEndpointLcm p : ℕ) : ℚ) =
          (factorialBlockBudget p : ℚ) *
            ((factorialBlockCollisionCore p : ℚ) *
              factorialBlockPrivateModulus p) := by
        push_cast
        rw [hfactorQ]
      _ <
          ((factorialBlockScale p *
                complementaryProjectedResidue
                  (factorialBlockTailNumerator p)
                  (factorialBlockPrivateModulus p) : ℕ) : ℚ) := by
        simpa [mul_assoc] using hmul
  exact_mod_cast hlargeQ

/-- Every private quotient indexed by the literal block divides the full
private modulus. -/
theorem factorialBlockPrivateQuotient_dvd_privateModulus
    {p n : ℕ}
    (hn : n ∈ factorialBlockIndices p) :
    factorialBlockPrivateQuotient p n ∣
      factorialBlockPrivateModulus p := by
  unfold factorialBlockPrivateQuotient
    factorialBlockPrivateModulus privateModulus
  exact Finset.dvd_prod_of_mem _ hn

/-- Every factor projection modulus selected by a divisor of `R_p` is
itself a divisor of `R_p`. -/
theorem factorialBlockFactorProjectionModulus_dvd_privateModulus
    {p a : ℕ}
    (ha : a ∣ factorialBlockPrivateModulus p) :
    factorialBlockFactorProjectionModulus p a ∣
      factorialBlockPrivateModulus p := by
  unfold factorialBlockFactorProjectionModulus
  exact Nat.div_dvd_of_dvd ha

/-- Exact factor-level deletion identity.  This is the owner-free version
of the quotient cancellation used in the collision-cap comparison. -/
theorem factorialBlock_min_factorProjection_mul_max_eq_privateModulus
    {p a b : ℕ}
    (ha : a ∣ factorialBlockPrivateModulus p)
    (hb : b ∣ factorialBlockPrivateModulus p) :
    min
        (factorialBlockFactorProjectionModulus p a)
        (factorialBlockFactorProjectionModulus p b) *
      max a b =
    factorialBlockPrivateModulus p := by
  exact
    min_leaveOneOutModulus_mul_max_eq
      factorialBlockPrivateModulus_pos ha hb

/-- Coprime factor deletions jointly recover the full private modulus,
even when the two factors were split from one owner quotient. -/
theorem factorialBlock_factorProjection_lcm_eq_privateModulus
    {p a b : ℕ}
    (ha : a ∣ factorialBlockPrivateModulus p)
    (hb : b ∣ factorialBlockPrivateModulus p)
    (hab : Nat.Coprime a b) :
    Nat.lcm
        (factorialBlockFactorProjectionModulus p a)
        (factorialBlockFactorProjectionModulus p b) =
      factorialBlockPrivateModulus p := by
  exact leaveOneOut_lcm_eq_of_coprime_divisors ha hb hab

/-- For two literal owners, deleting the larger private quotient produces
the smaller leave-one-out modulus, and their product is exactly `R_p`. -/
theorem factorialBlock_min_leaveOneOut_mul_max_privateQuotient_eq_privateModulus
    {p i j : ℕ}
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p) :
    min
        (factorialBlockLeaveOneOutModulus p i)
        (factorialBlockLeaveOneOutModulus p j) *
      max
        (factorialBlockPrivateQuotient p i)
        (factorialBlockPrivateQuotient p j) =
      factorialBlockPrivateModulus p := by
  exact
    min_leaveOneOutModulus_mul_max_eq
      factorialBlockPrivateModulus_pos
      (factorialBlockPrivateQuotient_dvd_privateModulus hi)
      (factorialBlockPrivateQuotient_dvd_privateModulus hj)

/-- Hence every literal leave-one-out modulus is a divisor of the full
private modulus. -/
theorem factorialBlockLeaveOneOutModulus_dvd_privateModulus
    {p n : ℕ}
    (hn : n ∈ factorialBlockIndices p) :
    factorialBlockLeaveOneOutModulus p n ∣
      factorialBlockPrivateModulus p := by
  unfold factorialBlockLeaveOneOutModulus
  exact Nat.div_dvd_of_dvd
    (factorialBlockPrivateQuotient_dvd_privateModulus hn)

/-- Cancelling `R_p` works for any two selected divisor factors, not only
for two full owner quotients.  Hence a split private quotient can supply
both factor projections in the quantitative comparison. -/
theorem factorialBlock_scaled_min_factorProjection_of_collisionCap
    {p a b : ℕ}
    (ha : a ∣ factorialBlockPrivateModulus p)
    (hb : b ∣ factorialBlockPrivateModulus p)
    (hcap :
      factorialBlockBudget p *
            factorialBlockCollisionCore p *
          max a b <
        factorialBlockScale p) :
    factorialBlockBudget p *
          factorialBlockEndpointLcm p <
      factorialBlockScale p *
        min
          (factorialBlockFactorProjectionModulus p a)
          (factorialBlockFactorProjectionModulus p b) := by
  have hminPos :
      0 <
        min
          (factorialBlockFactorProjectionModulus p a)
          (factorialBlockFactorProjectionModulus p b) := by
    have hQaPos :
        0 < factorialBlockFactorProjectionModulus p a :=
      Nat.pos_of_dvd_of_pos
        (factorialBlockFactorProjectionModulus_dvd_privateModulus ha)
        factorialBlockPrivateModulus_pos
    have hQbPos :
        0 < factorialBlockFactorProjectionModulus p b :=
      Nat.pos_of_dvd_of_pos
        (factorialBlockFactorProjectionModulus_dvd_privateModulus hb)
        factorialBlockPrivateModulus_pos
    omega
  have hmul :=
    (Nat.mul_lt_mul_right hminPos).2 hcap
  calc
    factorialBlockBudget p *
          factorialBlockEndpointLcm p =
        (factorialBlockBudget p *
            factorialBlockCollisionCore p) *
          factorialBlockPrivateModulus p := by
      rw [← factorialBlockCollisionCore_mul_privateModulus]
      ring
    _ =
        (factorialBlockBudget p *
              factorialBlockCollisionCore p *
            max a b) *
          min
            (factorialBlockFactorProjectionModulus p a)
            (factorialBlockFactorProjectionModulus p b) := by
      rw [
        ←
          factorialBlock_min_factorProjection_mul_max_eq_privateModulus
            ha hb
      ]
      ring
    _ <
        factorialBlockScale p *
          min
            (factorialBlockFactorProjectionModulus p a)
            (factorialBlockFactorProjectionModulus p b) := by
      simpa [mul_assoc] using hmul

/-- Cancelling the full private modulus turns the enormous literal
two-projection scale inequality into a local collision-core bound. -/
theorem factorialBlock_scaled_min_leaveOneOut_of_collisionCap
    {p i j : ℕ}
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p)
    (hcap :
      factorialBlockBudget p *
            factorialBlockCollisionCore p *
          max
            (factorialBlockPrivateQuotient p i)
            (factorialBlockPrivateQuotient p j) <
        factorialBlockScale p) :
    factorialBlockBudget p *
          factorialBlockEndpointLcm p <
      factorialBlockScale p *
        min
          (factorialBlockLeaveOneOutModulus p i)
          (factorialBlockLeaveOneOutModulus p j) := by
  have hminPos :
      0 <
        min
          (factorialBlockLeaveOneOutModulus p i)
          (factorialBlockLeaveOneOutModulus p j) := by
    have hQiPos :
        0 < factorialBlockLeaveOneOutModulus p i :=
      Nat.pos_of_dvd_of_pos
        (factorialBlockLeaveOneOutModulus_dvd_privateModulus hi)
        factorialBlockPrivateModulus_pos
    have hQjPos :
        0 < factorialBlockLeaveOneOutModulus p j :=
      Nat.pos_of_dvd_of_pos
        (factorialBlockLeaveOneOutModulus_dvd_privateModulus hj)
        factorialBlockPrivateModulus_pos
    omega
  have hmul :=
    (Nat.mul_lt_mul_right hminPos).2 hcap
  calc
    factorialBlockBudget p *
          factorialBlockEndpointLcm p =
        (factorialBlockBudget p *
            factorialBlockCollisionCore p) *
          factorialBlockPrivateModulus p := by
      rw [← factorialBlockCollisionCore_mul_privateModulus]
      ring
    _ =
        (factorialBlockBudget p *
              factorialBlockCollisionCore p *
            max
              (factorialBlockPrivateQuotient p i)
              (factorialBlockPrivateQuotient p j)) *
          min
            (factorialBlockLeaveOneOutModulus p i)
            (factorialBlockLeaveOneOutModulus p j) := by
      rw [
        ←
          factorialBlock_min_leaveOneOut_mul_max_privateQuotient_eq_privateModulus
            hi hj
      ]
      ring
    _ <
        factorialBlockScale p *
          min
            (factorialBlockLeaveOneOutModulus p i)
            (factorialBlockLeaveOneOutModulus p j) := by
      simpa [mul_assoc] using hmul

/-- Deleting two distinct private quotients gives projection moduli whose
lcm recovers the full private modulus.  Pairwise collision deletion is
exactly the coprimality input needed for this reconstruction. -/
theorem factorialBlock_leaveOneOut_lcm_eq_privateModulus
    {p i j : ℕ}
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p)
    (hij : i ≠ j) :
    Nat.lcm
        (factorialBlockLeaveOneOutModulus p i)
        (factorialBlockLeaveOneOutModulus p j) =
      factorialBlockPrivateModulus p := by
  have hri :=
    factorialBlockPrivateQuotient_dvd_privateModulus hi
  have hrj :=
    factorialBlockPrivateQuotient_dvd_privateModulus hj
  have hpair :=
    collisionCore_privateQuotients_pairwise_coprime
      (base := factorialBlockBase p)
      (s := factorialBlockIndices p)
      (d := factorialGapDenominator)
      (fun n hn => factorialGapDenominator_pos_of_mem hn)
  have hcop :
      Nat.Coprime
        (factorialBlockPrivateQuotient p i)
        (factorialBlockPrivateQuotient p j) := by
    simpa [factorialBlockPrivateQuotient, privateQuotient] using
      hpair hi hj hij
  unfold factorialBlockLeaveOneOutModulus leaveOneOutModulus
  rw [
    Nat.div_lcm_eq_div_gcd hri hrj,
    hcop.gcd_eq_one,
    Nat.div_one
  ]

/-- For two distinct literal owners, equality of the coefficient-free
leave-one-out projections means that their common value is exactly the
global complementary residue.  Together with the disagreement theorem,
this identifies the two exhaustive CRT branches used by the finite scan. -/
theorem factorialBlock_complementaryLeaveOneOut_eq_global_of_eq
    {p i j : ℕ}
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p)
    (hij : i ≠ j)
    (hR : 1 < factorialBlockPrivateModulus p)
    (heq :
      complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockLeaveOneOutModulus p i) =
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockLeaveOneOutModulus p j)) :
    complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockLeaveOneOutModulus p i) =
      complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockPrivateModulus p) := by
  have hRPos : 0 < factorialBlockPrivateModulus p := by
    omega
  have hQiDvd :=
    factorialBlockLeaveOneOutModulus_dvd_privateModulus hi
  have hQjDvd :=
    factorialBlockLeaveOneOutModulus_dvd_privateModulus hj
  have hQiPos :
      0 < factorialBlockLeaveOneOutModulus p i :=
    Nat.pos_of_dvd_of_pos hQiDvd hRPos
  have hQjPos :
      0 < factorialBlockLeaveOneOutModulus p j :=
    Nat.pos_of_dvd_of_pos hQjDvd hRPos
  have hprojI :=
    projectedResidue_complementaryProjectedResidue_eq_of_dvd
      (T := factorialBlockTailNumerator p)
      hRPos hQiPos hQiDvd
  have hprojJ :=
    projectedResidue_complementaryProjectedResidue_eq_of_dvd
      (T := factorialBlockTailNumerator p)
      hRPos hQjPos hQjDvd
  have hprojEq :
      projectedResidue
          (complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p))
          (factorialBlockLeaveOneOutModulus p i) =
        projectedResidue
          (complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p))
          (factorialBlockLeaveOneOutModulus p j) := by
    rw [hprojI, hprojJ]
    exact heq
  have hglobalLt :
      complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) <
        factorialBlockPrivateModulus p := by
    unfold complementaryProjectedResidue projectedResidue
    exact Nat.mod_lt _ hRPos
  have hcollapse :=
    projectedResidue_eq_residue_of_eq_of_lcm
      hglobalLt
      (factorialBlock_leaveOneOut_lcm_eq_privateModulus
        hi hj hij)
      hprojEq
  calc
    complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockLeaveOneOutModulus p i) =
        projectedResidue
          (complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p))
          (factorialBlockLeaveOneOutModulus p i) :=
      hprojI.symm
    _ =
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) :=
      hcollapse

/-- Coefficient-free score from two arbitrary factor projections.  The
deleted factors can be chosen inside a single private owner quotient. -/
def factorialBlockComplementaryFactorPairFloor
    (p a b : ℕ) : ℕ :=
  if complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockFactorProjectionModulus p a) =
      complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockFactorProjectionModulus p b) then
    complementaryProjectedResidue
      (factorialBlockTailNumerator p)
      (factorialBlockFactorProjectionModulus p a)
  else
    min
      (factorialBlockFactorProjectionModulus p a)
      (factorialBlockFactorProjectionModulus p b)

/-- For the source-natural unit factor pair `(1,q)`, the branch-free floor
is exactly the minimum of the global complementary residue and `R_p / q`.
Thus its scale condition is transparently the conjunction of a global
residue bound and a collision-cap bound for `q`. -/
theorem factorialBlock_unitFactorPairFloor_eq_min
    {p q : ℕ}
    (hq : q ∣ factorialBlockPrivateModulus p) :
    factorialBlockComplementaryFactorPairFloor p 1 q =
      min
        (complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p))
        (factorialBlockPrivateModulus p / q) := by
  have hR : 0 < factorialBlockPrivateModulus p :=
    factorialBlockPrivateModulus_pos
  have hQ :
      0 < factorialBlockPrivateModulus p / q := by
    exact Nat.div_pos (Nat.le_of_dvd hR hq) (Nat.pos_of_dvd_of_pos hq hR)
  have hQdvd :
      factorialBlockPrivateModulus p / q ∣
        factorialBlockPrivateModulus p :=
    Nat.div_dvd_of_dvd hq
  have hglobalLt :
      complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) <
        factorialBlockPrivateModulus p := by
    unfold complementaryProjectedResidue projectedResidue
    exact Nat.mod_lt _ hR
  have hprojFull :
      projectedResidue
          (complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p))
          (factorialBlockPrivateModulus p) =
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) := by
    exact Nat.mod_eq_of_lt hglobalLt
  have hprojQ :
      projectedResidue
          (complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p))
          (factorialBlockPrivateModulus p / q) =
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p / q) := by
    exact
      (projectedResidue_complementaryProjectedResidue_eq_of_dvd
        (T := factorialBlockTailNumerator p)
        hR hQ hQdvd)
  have hfloor :=
    projectionPairFloor_full_divisor_eq_min
      hglobalLt hQ hQdvd
  simpa only [
    projectionPairFloor,
    factorialBlockComplementaryFactorPairFloor,
    factorialBlockFactorProjectionModulus,
    leaveOneOutModulus,
    Nat.div_one,
    hprojFull,
    hprojQ
  ] using hfloor

/-- The unit-factor scale test splits exactly into the original global
complementary-residue inequality and the local collision-core cap for `q`.
Consequently the `(1,q)` reduction removes the need for a second private
prime without concealing either remaining quantitative obligation. -/
theorem factorialBlock_unitFactorPairFloor_scale_iff
    {p q : ℕ}
    (hq : q ∣ factorialBlockPrivateModulus p) :
    factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          factorialBlockComplementaryFactorPairFloor p 1 q ↔
      (factorialBlockBudget p *
            factorialBlockEndpointLcm p <
          factorialBlockScale p *
            complementaryProjectedResidue
              (factorialBlockTailNumerator p)
              (factorialBlockPrivateModulus p) ∧
        factorialBlockBudget p *
              factorialBlockCollisionCore p * q <
            factorialBlockScale p) := by
  rw [factorialBlock_unitFactorPairFloor_eq_min hq, lt_mul_min_iff]
  apply and_congr Iff.rfl
  have hR : 0 < factorialBlockPrivateModulus p :=
    factorialBlockPrivateModulus_pos
  have hqPos : 0 < q := Nat.pos_of_dvd_of_pos hq hR
  have hQ :
      0 < factorialBlockPrivateModulus p / q :=
    Nat.div_pos (Nat.le_of_dvd hR hq) hqPos
  have hRq :
      factorialBlockPrivateModulus p / q * q =
        factorialBlockPrivateModulus p :=
    Nat.div_mul_cancel hq
  have hqR :
      q * (factorialBlockPrivateModulus p / q) =
        factorialBlockPrivateModulus p := by
    rw [Nat.mul_comm, hRq]
  have hL :
      factorialBlockCollisionCore p *
          factorialBlockPrivateModulus p =
        factorialBlockEndpointLcm p :=
    factorialBlockCollisionCore_mul_privateModulus
  constructor
  · intro hscale
    apply (Nat.mul_lt_mul_right hQ).1
    calc
      (factorialBlockBudget p *
              factorialBlockCollisionCore p * q) *
            (factorialBlockPrivateModulus p / q) =
          factorialBlockBudget p *
            factorialBlockCollisionCore p *
              (q * (factorialBlockPrivateModulus p / q)) := by ring
      _ =
          factorialBlockBudget p *
            factorialBlockCollisionCore p *
              factorialBlockPrivateModulus p := by rw [hqR]
      _ =
          factorialBlockBudget p *
            factorialBlockEndpointLcm p := by
        simpa [mul_assoc] using
          congrArg (fun n => factorialBlockBudget p * n) hL
      _ <
          factorialBlockScale p *
            (factorialBlockPrivateModulus p / q) :=
        hscale
  · intro hcap
    have hscaled :=
      (Nat.mul_lt_mul_right hQ).2 hcap
    calc
      factorialBlockBudget p *
            factorialBlockEndpointLcm p =
          factorialBlockBudget p *
            factorialBlockCollisionCore p *
              factorialBlockPrivateModulus p := by
        simpa [mul_assoc] using
          (congrArg (fun n => factorialBlockBudget p * n) hL).symm
      _ =
          factorialBlockBudget p *
            factorialBlockCollisionCore p *
              (q * (factorialBlockPrivateModulus p / q)) := by rw [hqR]
      _ =
          (factorialBlockBudget p *
              factorialBlockCollisionCore p * q) *
            (factorialBlockPrivateModulus p / q) := by ring
      _ <
          factorialBlockScale p *
            (factorialBlockPrivateModulus p / q) :=
        hscaled

/-- Two coprime divisor factors give an unconditional lower certificate
for the global complementary residue.  This strictly generalizes the
distinct-owner pair floor: the factors need not be full owner quotients
or belong to different denominators. -/
theorem factorialBlock_complementaryFactorPairFloor_le_global
    {p a b : ℕ}
    (ha : a ∣ factorialBlockPrivateModulus p)
    (hb : b ∣ factorialBlockPrivateModulus p)
    (hab : Nat.Coprime a b)
    (hR : 1 < factorialBlockPrivateModulus p) :
    factorialBlockComplementaryFactorPairFloor p a b ≤
      complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockPrivateModulus p) := by
  have hRPos : 0 < factorialBlockPrivateModulus p := by
    omega
  have hQaDvd :=
    factorialBlockFactorProjectionModulus_dvd_privateModulus ha
  have hQbDvd :=
    factorialBlockFactorProjectionModulus_dvd_privateModulus hb
  have hQaPos :
      0 < factorialBlockFactorProjectionModulus p a :=
    Nat.pos_of_dvd_of_pos hQaDvd hRPos
  have hQbPos :
      0 < factorialBlockFactorProjectionModulus p b :=
    Nat.pos_of_dvd_of_pos hQbDvd hRPos
  have hprojA :=
    projectedResidue_complementaryProjectedResidue_eq_of_dvd
      (T := factorialBlockTailNumerator p)
      hRPos hQaPos hQaDvd
  have hprojB :=
    projectedResidue_complementaryProjectedResidue_eq_of_dvd
      (T := factorialBlockTailNumerator p)
      hRPos hQbPos hQbDvd
  have hglobalLt :
      complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) <
        factorialBlockPrivateModulus p := by
    unfold complementaryProjectedResidue projectedResidue
    exact Nat.mod_lt _ hRPos
  have hfloor :
      projectionPairFloor
          (complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p))
          (factorialBlockFactorProjectionModulus p a)
          (factorialBlockFactorProjectionModulus p b) ≤
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) :=
    projectionPairFloor_le_residue_of_lt_of_lcm
      hglobalLt
      (factorialBlock_factorProjection_lcm_eq_privateModulus
        ha hb hab)
  simpa only [
    projectionPairFloor,
    factorialBlockComplementaryFactorPairFloor,
    hprojA,
    hprojB
  ] using hfloor

/-- Coefficient-free two-owner score for a literal block.  An agreeing
pair contributes its common complementary projection; a disagreeing pair
contributes the smaller leave-one-out modulus. -/
def factorialBlockComplementaryPairFloor
    (p i j : ℕ) : ℕ :=
  if complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockLeaveOneOutModulus p i) =
      complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockLeaveOneOutModulus p j) then
    complementaryProjectedResidue
      (factorialBlockTailNumerator p)
      (factorialBlockLeaveOneOutModulus p i)
  else
    min
      (factorialBlockLeaveOneOutModulus p i)
      (factorialBlockLeaveOneOutModulus p j)

/-- Every distinct pair floor is an unconditional lower bound for the
single global complementary residue.  No projection-disagreement
hypothesis remains. -/
theorem factorialBlock_complementaryPairFloor_le_global
    {p i j : ℕ}
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p)
    (hij : i ≠ j)
    (hR : 1 < factorialBlockPrivateModulus p) :
    factorialBlockComplementaryPairFloor p i j ≤
      complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockPrivateModulus p) := by
  have hRPos : 0 < factorialBlockPrivateModulus p := by
    omega
  have hQiDvd :=
    factorialBlockLeaveOneOutModulus_dvd_privateModulus hi
  have hQjDvd :=
    factorialBlockLeaveOneOutModulus_dvd_privateModulus hj
  have hQiPos :
      0 < factorialBlockLeaveOneOutModulus p i :=
    Nat.pos_of_dvd_of_pos hQiDvd hRPos
  have hQjPos :
      0 < factorialBlockLeaveOneOutModulus p j :=
    Nat.pos_of_dvd_of_pos hQjDvd hRPos
  have hprojI :=
    projectedResidue_complementaryProjectedResidue_eq_of_dvd
      (T := factorialBlockTailNumerator p)
      hRPos hQiPos hQiDvd
  have hprojJ :=
    projectedResidue_complementaryProjectedResidue_eq_of_dvd
      (T := factorialBlockTailNumerator p)
      hRPos hQjPos hQjDvd
  have hglobalLt :
      complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) <
        factorialBlockPrivateModulus p := by
    unfold complementaryProjectedResidue projectedResidue
    exact Nat.mod_lt _ hRPos
  have hfloor :
      projectionPairFloor
          (complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p))
          (factorialBlockLeaveOneOutModulus p i)
          (factorialBlockLeaveOneOutModulus p j) ≤
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockPrivateModulus p) :=
    projectionPairFloor_le_residue_of_lt_of_lcm
      hglobalLt
      (factorialBlock_leaveOneOut_lcm_eq_privateModulus
        hi hj hij)
  simpa only [
    projectionPairFloor,
    factorialBlockComplementaryPairFloor,
    hprojI,
    hprojJ
  ] using hfloor

/-- Literal leave-one-out projections of the least private residue can be
computed directly from the displayed endpoint numerator. -/
theorem factorialBlockPrivateResidue_projected_eq_endpointNumerator
    {p n : ℕ}
    (hn : n ∈ factorialBlockIndices p) :
    projectedResidue
        (factorialBlockPrivateResidue p)
        (factorialBlockLeaveOneOutModulus p n) =
      projectedResidue
        (factorialBlockEndpointNumerator p)
        (factorialBlockLeaveOneOutModulus p n) := by
  unfold factorialBlockPrivateResidue
    factorialBlockEndpointNumerator
  exact projectedResidue_endpointPrivateResidue_eq_of_dvd
    (factorialBlockLeaveOneOutModulus_dvd_privateModulus hn)

/-- A prime hit in the upper half of the literal block is too large to
divide the distinguished predecessor-factorial base. -/
theorem factorialBlockPrime_not_dvd_base_of_upper_hit
    {p n q : ℕ}
    (hq : q.Prime)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n) :
    ¬q ∣ factorialBlockBase p := by
  have hnq : n < q := by
    apply prime_dvd_factorial_sub_one_gt hq
    simpa [factorialGapDenominator] using hqden
  unfold factorialBlockBase
  rw [Nat.Prime.dvd_factorial hq]
  omega

/-- A collision prime that also hits an upper-half factorial gap survives
predecessor-factorial normalization.  This is the direct consumer for a
source-supplied repeated upper-half hit: collision membership plus the
automatic omission from `(p - 1)!` puts the prime into `Ctilde_p`. -/
theorem
    factorialBlockPrime_dvd_normalizedCollisionCore_of_upper_hit_of_dvd_collisionCore
    {p n q : ℕ}
    (hq : q.Prime)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n)
    (hcore : q ∣ factorialBlockCollisionCore p) :
    q ∣ factorialBlockNormalizedCollisionCore p := by
  have hqBase :
      ¬q ∣ factorialBlockBase p :=
    factorialBlockPrime_not_dvd_base_of_upper_hit
      hq hpn hqden
  have hfactor :
      q ∣
        factorialBlockBase p *
          factorialBlockNormalizedCollisionCore p := by
    rw [factorialBlockBase_mul_normalizedCollisionCore]
    exact hcore
  exact (hq.dvd_mul.mp hfactor).resolve_left hqBase

/-- A prime power in the literal block collision core, when its prime also
hits an upper-half factorial gap, must occur to full multiplicity in two
distinct displayed factorial gaps.  This is the exact bridge from the
collision core to general-modulus hit counts. -/
theorem exists_two_factorialBlock_hits_of_primePower_dvd_collisionCore
    {p n q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n)
    (hpow : q ^ e ∣ factorialBlockCollisionCore p) :
    ∃ i ∈ factorialBlockIndices p,
      ∃ j ∈ factorialBlockIndices p,
        i ≠ j ∧
          q ^ e ∣ factorialGapDenominator i ∧
          q ^ e ∣ factorialGapDenominator j := by
  have hqBase :
      ¬q ∣ factorialBlockBase p :=
    factorialBlockPrime_not_dvd_base_of_upper_hit
      hq hpn hqden
  have hpowBase :
      ¬q ^ e ∣ factorialBlockBase p := by
    intro hdiv
    exact hqBase ((dvd_pow_self q he.ne').trans hdiv)
  unfold factorialBlockCollisionCore at hpow
  exact
    exists_pairwise_primePower_support_of_dvd_collisionCore
      hq he (Nat.factorial_pos _) (fun i hi =>
        factorialGapDenominator_pos_of_mem hi)
      hpowBase hpow

/-- On a block carrying an upper-half `q`-hit, the exponent of `q` in the
collision core is characterized exactly by two distinct full-power hits.
Equivalently, its `q`-valuation is the second-largest displayed valuation. -/
theorem factorialBlock_primePower_dvd_collisionCore_iff_two_hits
    {p n q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n) :
    q ^ e ∣ factorialBlockCollisionCore p ↔
      ∃ i ∈ factorialBlockIndices p,
        ∃ j ∈ factorialBlockIndices p,
          i ≠ j ∧
            q ^ e ∣ factorialGapDenominator i ∧
            q ^ e ∣ factorialGapDenominator j := by
  have hqBase :
      ¬q ∣ factorialBlockBase p :=
    factorialBlockPrime_not_dvd_base_of_upper_hit
      hq hpn hqden
  have hpowBase :
      ¬q ^ e ∣ factorialBlockBase p := by
    intro hdiv
    exact hqBase ((dvd_pow_self q he.ne').trans hdiv)
  unfold factorialBlockCollisionCore
  exact primePower_dvd_collisionCore_iff
    hq he (Nat.factorial_pos _) (fun i hi =>
      factorialGapDenominator_pos_of_mem hi)
    hpowBase

/-- An upper-half `q`-hit removes the only difference between the full
collision core and its predecessor-factorial normalization at every
positive `q`-power.  Thus Stewart/Wilson-style reflected collisions enter
`Ctilde_p` with their complete collision multiplicity, not merely at the
prime-support level. -/
theorem
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_of_upper_hit
    {p n q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n) :
    q ^ e ∣ factorialBlockNormalizedCollisionCore p ↔
      q ^ e ∣ factorialBlockCollisionCore p := by
  have hqBase :
      ¬q ∣ factorialBlockBase p :=
    factorialBlockPrime_not_dvd_base_of_upper_hit
      hq hpn hqden
  have hbaseZero :
      (factorialBlockBase p).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqBase
  rw [
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_two_hits
      hq he,
    hbaseZero,
    add_zero,
    factorialBlock_primePower_dvd_collisionCore_iff_two_hits
      hq he hpn hqden
  ]

/-- Exact incidence-count form of the upper-hit normalization theorem.
For a prime already known to hit the upper half of the block, a positive
prime power survives in the normalized collision core exactly when that
power hits at least two displayed factorial gaps.  Thus any external
prime-power hit-count bound of at most one deletes that exponent from
`Ctilde_p` directly. -/
theorem
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount
    {p n q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n) :
    q ^ e ∣ factorialBlockNormalizedCollisionCore p ↔
      1 <
        ((factorialBlockIndices p).filter fun i =>
          q ^ e ∣ factorialGapDenominator i).card := by
  rw [
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_of_upper_hit
      hq he hpn hqden,
    factorialBlock_primePower_dvd_collisionCore_iff_two_hits
      hq he hpn hqden,
    Finset.one_lt_card
  ]
  simp only [Finset.mem_filter]
  aesop

/-- A source-level bound of at most one `q^e`-hit on the block excludes
`q^e` from the normalized collision core. -/
theorem
    factorialBlock_primePower_not_dvd_normalizedCollisionCore_of_hitCount_le_one
    {p n q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n)
    (hcount :
      ((factorialBlockIndices p).filter fun i =>
        q ^ e ∣ factorialGapDenominator i).card ≤ 1) :
    ¬q ^ e ∣ factorialBlockNormalizedCollisionCore p := by
  rw [
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount
      hq he hpn hqden
  ]
  omega

/-- Valuation form of the hit-count consumer: an at-most-one incidence
bound at exponent `e` forces the normalized collision valuation below
`e`. -/
theorem
    factorialBlock_normalizedCollisionCore_factorization_lt_of_hitCount_le_one
    {p n q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n)
    (hcount :
      ((factorialBlockIndices p).filter fun i =>
        q ^ e ∣ factorialGapDenominator i).card ≤ 1) :
    (factorialBlockNormalizedCollisionCore p).factorization q < e := by
  have hnot :
      ¬q ^ e ∣ factorialBlockNormalizedCollisionCore p :=
    factorialBlock_primePower_not_dvd_normalizedCollisionCore_of_hitCount_le_one
      hq he hpn hqden hcount
  by_contra hfac
  exact hnot
    ((hq.pow_dvd_iff_le_factorization
      factorialBlockNormalizedCollisionCore_pos.ne').2
        (Nat.le_of_not_gt hfac))

/-- Layer-count form of the normalized collision valuation.  Once `q`
hits an upper-half factorial gap, its complete valuation in `Ctilde_p`
is exactly the number of positive prime-power layers below `q` that hit
at least two displayed gaps.  This aggregates prime-power incidence
bounds into the precise local collision load used by the scale split. -/
theorem
    factorialBlock_normalizedCollisionCore_factorization_eq_repeatedHitLayerCount
    {p n q : ℕ}
    (hq : q.Prime)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n) :
    (factorialBlockNormalizedCollisionCore p).factorization q =
      ((Finset.Icc 1 (q - 1)).filter fun e =>
        1 <
          ((factorialBlockIndices p).filter fun i =>
            q ^ e ∣ factorialGapDenominator i).card).card := by
  let v :=
    (factorialBlockNormalizedCollisionCore p).factorization q
  have hcoreNe :
      factorialBlockNormalizedCollisionCore p ≠ 0 :=
    factorialBlockNormalizedCollisionCore_pos.ne'
  have hvq : v < q := by
    by_cases hv : v = 0
    · simpa [hv] using hq.pos
    · have hvPos : 0 < v := Nat.pos_of_ne_zero hv
      have hpow :
          q ^ v ∣ factorialBlockNormalizedCollisionCore p :=
        (hq.pow_dvd_iff_le_factorization hcoreNe).2
          (by simp [v])
      have hdiv :
          q ∣ factorialBlockNormalizedCollisionCore p :=
        (dvd_pow_self q hvPos.ne').trans hpow
      have hceiling :=
        factorialBlock_normalizedCollision_factorization_add_base_lt_prime
          hq hdiv
      dsimp [v]
      omega
  have hfilter :
      ((Finset.Icc 1 (q - 1)).filter fun e =>
        1 <
          ((factorialBlockIndices p).filter fun i =>
            q ^ e ∣ factorialGapDenominator i).card) =
        Finset.Icc 1 v := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hePos, _heUpper⟩, hcount⟩
      have hpow :
          q ^ e ∣ factorialBlockNormalizedCollisionCore p :=
        (factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount
          hq (by omega) hpn hqden).2 hcount
      exact ⟨hePos,
        (hq.pow_dvd_iff_le_factorization hcoreNe).1 hpow⟩
    · rintro ⟨hePos, hev⟩
      have heUpper : e ≤ q - 1 := by omega
      have hpow :
          q ^ e ∣ factorialBlockNormalizedCollisionCore p :=
        (hq.pow_dvd_iff_le_factorization hcoreNe).2 hev
      exact ⟨⟨hePos, heUpper⟩,
        (factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount
          hq (by omega) hpn hqden).1 hpow⟩
  change v = _
  rw [hfilter, Nat.card_Icc]
  omega

/-- For a prime above the displayed endpoint, the exact repeated-hit layer
count truncates at the block diameter.  Thus aggregation over endpoint
primes never needs the a priori layer range up to `q-1`: every surviving
layer already lies in `[1, 2p-4]`. -/
theorem
    factorialBlock_normalizedCollisionCore_factorization_eq_truncatedRepeatedHitLayerCount
    {p n q : ℕ}
    (hp : 2 ≤ p)
    (hq : q.Prime)
    (hendpoint : 2 * p - 1 < q)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n) :
    (factorialBlockNormalizedCollisionCore p).factorization q =
      ((Finset.Icc 1 (2 * p - 4)).filter fun e =>
        1 <
          ((factorialBlockIndices p).filter fun i =>
            q ^ e ∣ factorialGapDenominator i).card).card := by
  rw [
    factorialBlock_normalizedCollisionCore_factorization_eq_repeatedHitLayerCount
      hq hpn hqden
  ]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hePos, _heUpper⟩, hcount⟩
    have hpacking :=
      factorialBlock_primePowerHitCount_mul_succ_le_of_endpoint_lt_base
        hp hePos hendpoint
    have htwoMul :
        2 * (e + 1) ≤
          ((factorialBlockIndices p).filter fun i =>
            q ^ e ∣ factorialGapDenominator i).card * (e + 1) :=
      Nat.mul_le_mul_right (e + 1) (by omega)
    have heDiameter : e ≤ 2 * p - 4 := by
      omega
    exact ⟨⟨hePos, heDiameter⟩, hcount⟩
  · rintro ⟨⟨hePos, heDiameter⟩, hcount⟩
    have heUpper : e ≤ q - 1 := by omega
    exact ⟨⟨hePos, heUpper⟩, hcount⟩

/-- Whenever `q` is absent from the predecessor-factorial base, base
normalization is invisible at every positive `q`-power.  Thus `q^e`
survives in the normalized collision core exactly when two displayed
factorial gaps contain that full power.  This is the anchor-free interface
for all base-omitted primes, not only primes above the block endpoint. -/
theorem
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount_of_not_dvd_base
    {p q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hqBase : ¬q ∣ factorialBlockBase p) :
    q ^ e ∣ factorialBlockNormalizedCollisionCore p ↔
      1 <
        ((factorialBlockIndices p).filter fun i =>
          q ^ e ∣ factorialGapDenominator i).card := by
  have hbaseZero :
      (factorialBlockBase p).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqBase
  rw [
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_two_hits
      hq he,
    hbaseZero,
    add_zero,
    Finset.one_lt_card
  ]
  simp only [Finset.mem_filter]
  aesop

/-- A base-omitted prime has normalized valuation below `e` as soon as
its `q^e` layer occurs at most once on the full factorial block. -/
theorem
    factorialBlock_normalizedCollisionCore_factorization_lt_of_not_dvd_base_of_hitCount_le_one
    {p q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hqBase : ¬q ∣ factorialBlockBase p)
    (hcount :
      ((factorialBlockIndices p).filter fun i =>
        q ^ e ∣ factorialGapDenominator i).card ≤ 1) :
    (factorialBlockNormalizedCollisionCore p).factorization q < e := by
  have hnot :
      ¬q ^ e ∣ factorialBlockNormalizedCollisionCore p := by
    rw [
      factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount_of_not_dvd_base
        hq he hqBase
    ]
    omega
  by_contra hfac
  exact hnot
    ((hq.pow_dvd_iff_le_factorization
      factorialBlockNormalizedCollisionCore_pos.ne').2
        (Nat.le_of_not_gt hfac))

/-- In particular, an at-most-one `q^2` incidence estimate makes every
base-omitted normalized collision prime squarefree.  This covers every
prime `q ≥ p`, since such a prime is absent from `(p-1)!`. -/
theorem
    factorialBlock_normalizedCollisionCore_factorization_le_one_of_not_dvd_base_of_primeSqHitCount_le_one
    {p q : ℕ}
    (hq : q.Prime)
    (hqBase : ¬q ∣ factorialBlockBase p)
    (hcount :
      ((factorialBlockIndices p).filter fun i =>
        q ^ 2 ∣ factorialGapDenominator i).card ≤ 1) :
    (factorialBlockNormalizedCollisionCore p).factorization q ≤ 1 := by
  have hlt :=
    factorialBlock_normalizedCollisionCore_factorization_lt_of_not_dvd_base_of_hitCount_le_one
      hq (by omega) hqBase hcount
  omega

/-- Above the displayed endpoint, predecessor-factorial normalization is
invisible at `q`.  Consequently a positive `q^e`-layer survives in the
normalized collision core exactly when that layer hits two displayed
factorial gaps.  Unlike the upper-hit interface, this requires no chosen
anchor: it applies to every endpoint prime in the collision core. -/
theorem
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount_of_endpoint_lt_base
    {p q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hendpoint : 2 * p - 1 < q) :
    q ^ e ∣ factorialBlockNormalizedCollisionCore p ↔
      1 <
        ((factorialBlockIndices p).filter fun i =>
          q ^ e ∣ factorialGapDenominator i).card := by
  have hqNotBase : ¬q ∣ factorialBlockBase p := by
    unfold factorialBlockBase
    rw [Nat.Prime.dvd_factorial hq]
    omega
  exact
    factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount_of_not_dvd_base
      hq he hqNotBase

/-- Endpoint-prime valuation cutoff with no preselected upper-half hit.
Any at-most-one incidence estimate for `q^e` on the full block forces the
complete normalized `q`-valuation below `e`. -/
theorem
    factorialBlock_normalizedCollisionCore_factorization_lt_of_endpoint_lt_base_of_hitCount_le_one
    {p q e : ℕ}
    (hq : q.Prime)
    (he : 0 < e)
    (hendpoint : 2 * p - 1 < q)
    (hcount :
      ((factorialBlockIndices p).filter fun i =>
        q ^ e ∣ factorialGapDenominator i).card ≤ 1) :
    (factorialBlockNormalizedCollisionCore p).factorization q < e := by
  have hnot :
      ¬q ^ e ∣ factorialBlockNormalizedCollisionCore p := by
    rw [
      factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount_of_endpoint_lt_base
        hq he hendpoint
    ]
    omega
  by_contra hfac
  exact hnot
    ((hq.pow_dvd_iff_le_factorization
      factorialBlockNormalizedCollisionCore_pos.ne').2
        (Nat.le_of_not_gt hfac))

/-- Prime-square specialization of the endpoint incidence cutoff.  Thus
the endpoint-prime part of the normalized collision core is squarefree as
soon as every `q^2` layer has at most one factorial-gap hit. -/
theorem
    factorialBlock_normalizedCollisionCore_factorization_le_one_of_endpoint_lt_base_of_primeSqHitCount_le_one
    {p q : ℕ}
    (hq : q.Prime)
    (hendpoint : 2 * p - 1 < q)
    (hcount :
      ((factorialBlockIndices p).filter fun i =>
        q ^ 2 ∣ factorialGapDenominator i).card ≤ 1) :
    (factorialBlockNormalizedCollisionCore p).factorization q ≤ 1 := by
  have hlt :=
    factorialBlock_normalizedCollisionCore_factorization_lt_of_endpoint_lt_base_of_hitCount_le_one
      hq (by omega) hendpoint hcount
  omega

/-- Under unique support, the upper-half prime divides its literal private
quotient after collision deletion. -/
theorem factorialBlockPrime_dvd_privateQuotient_of_unique_upper_prime
    {p n q : ℕ}
    (hq : q.Prime)
    (hpn : p ≤ n)
    (hqden : q ∣ factorialGapDenominator n)
    (hunique :
      ∀ m ∈ factorialBlockIndices p, m ≠ n →
        ¬q ∣ factorialGapDenominator m) :
    q ∣ privateQuotient
      (factorialBlockBase p)
      (factorialBlockIndices p)
      factorialGapDenominator n := by
  exact prime_dvd_privateQuotient_of_unique_support
    hq hqden
    (factorialBlockPrime_not_dvd_base_of_upper_hit
      hq hpn hqden)
    hunique

/-- A prime occurring exactly once in the upper half of the literal
factorial block survives the collision core and makes `R_p` nontrivial. -/
theorem factorialBlockPrivateModulus_one_lt_of_unique_upper_prime
    {p n q : ℕ}
    (hq : q.Prime)
    (hpn : p ≤ n)
    (hn : n ∈ factorialBlockIndices p)
    (hqden : q ∣ factorialGapDenominator n)
    (hunique :
      ∀ m ∈ factorialBlockIndices p, m ≠ n →
        ¬q ∣ factorialGapDenominator m) :
    1 < factorialBlockPrivateModulus p := by
  apply privateModulus_one_lt_of_unique_prime_support
    (base := factorialBlockBase p)
    (s := factorialBlockIndices p)
    (d := factorialGapDenominator)
    hq hn hqden
    (factorialBlockPrime_not_dvd_base_of_upper_hit
      hq hpn hqden)
    hunique
  intro m hm
  exact factorialGapDenominator_pos_of_mem hm

/-- Unique support of an upper-half prime makes its literal one-owner
projection automatically nonzero.  No separate residue hypothesis is
needed in the one-owner closing criterion. -/
theorem factorialBlockPrivateOwnerTerm_mod_pos_of_unique_upper_prime
    {p n q : ℕ}
    (hq : q.Prime)
    (hpn : p ≤ n)
    (hn : n ∈ factorialBlockIndices p)
    (hqden : q ∣ factorialGapDenominator n)
    (hunique :
      ∀ m ∈ factorialBlockIndices p, m ≠ n →
        ¬q ∣ factorialGapDenominator m) :
    0 < factorialBlockPrivateOwnerTerm p n % q := by
  unfold factorialBlockPrivateOwnerTerm
  exact privateOwnerTerm_mod_prime_pos
    hq hn
    (fun m hm => factorialGapDenominator_pos_of_mem hm)
    (factorialBlockPrime_dvd_privateQuotient_of_unique_upper_prime
      hq hpn hqden hunique)

/-- A positive literal endpoint gap already supplies the natural
ordinary-subtraction side condition. -/
theorem factorialBlock_tail_le_baseNumerator_of_endpointGap_pos
    {p : ℕ}
    (hgap : 0 < factorialBlockEndpointGap p) :
    factorialBlockTailNumerator p ≤
      factorialBlockBaseNumerator p := by
  apply endpointTailNumerator_le_endpointBaseNumerator_of_gap_nonneg
    (K := factorialBlockCoefficient p)
    (base := factorialBlockBase p)
    (s := factorialBlockIndices p)
    (d := factorialGapDenominator)
  · exact Nat.factorial_pos _
  · intro n hn
    exact factorialGapDenominator_pos_of_mem hn
  · rw [factorialBlock_reciprocalSum_eq_factorialGapPrefix]
    exact hgap.le

/-- On every literal leave-one-out divisor, the displayed endpoint
numerator is the complementary projection of the explicit reciprocal-tail
numerator. -/
theorem factorialBlockEndpointNumerator_projected_eq_complementaryTail
    {p n : ℕ}
    (hgap : 0 < factorialBlockEndpointGap p)
    (hn : n ∈ factorialBlockIndices p)
    (hQ :
      0 < factorialBlockLeaveOneOutModulus p n) :
    projectedResidue
        (factorialBlockEndpointNumerator p)
        (factorialBlockLeaveOneOutModulus p n) =
      complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockLeaveOneOutModulus p n) := by
  apply projectedResidue_eq_complementary_of_add_modEq_zero
    hQ
  apply
    (endpointNumerator_add_tail_modEq_zero
      (K := factorialBlockCoefficient p)
      (base := factorialBlockBase p)
      (s := factorialBlockIndices p)
      (d := factorialGapDenominator)
      (Nat.factorial_pos _)
      (fun m hm => factorialGapDenominator_pos_of_mem hm)
      (factorialBlock_tail_le_baseNumerator_of_endpointGap_pos
        hgap)).of_dvd
  exact factorialBlockLeaveOneOutModulus_dvd_privateModulus hn

/-- The full private residue itself is coefficient-free: once the literal
endpoint gap is positive, it is exactly the complementary residue of the
explicit reciprocal-tail numerator modulo `R_p`. -/
theorem factorialBlockPrivateResidue_eq_complementaryTail
    {p : ℕ}
    (hgap : 0 < factorialBlockEndpointGap p)
    (hR : 0 < factorialBlockPrivateModulus p) :
    factorialBlockPrivateResidue p =
      complementaryProjectedResidue
        (factorialBlockTailNumerator p)
        (factorialBlockPrivateModulus p) := by
  unfold factorialBlockPrivateResidue
    endpointPrivateResidue
    factorialBlockTailNumerator
    factorialBlockPrivateModulus
  apply projectedResidue_eq_complementary_of_add_modEq_zero
    hR
  exact
    endpointNumerator_add_tail_modEq_zero
      (K := factorialBlockCoefficient p)
      (base := factorialBlockBase p)
      (s := factorialBlockIndices p)
      (d := factorialGapDenominator)
      (Nat.factorial_pos _)
      (fun m hm => factorialGapDenominator_pos_of_mem hm)
      (factorialBlock_tail_le_baseNumerator_of_endpointGap_pos
        hgap)

/-- The same unique prime gives an explicit lower bound for the literal
least private residue: the complement of its one-owner projection. -/
theorem factorialBlockPrivateResidue_owner_lower_bound_of_unique_upper_prime
    {p n q : ℕ}
    (hgap : 0 < factorialBlockEndpointGap p)
    (hq : q.Prime)
    (hpn : p ≤ n)
    (hn : n ∈ factorialBlockIndices p)
    (hqden : q ∣ factorialGapDenominator n)
    (hunique :
      ∀ m ∈ factorialBlockIndices p, m ≠ n →
        ¬q ∣ factorialGapDenominator m) :
    q - factorialBlockPrivateOwnerTerm p n % q ≤
      factorialBlockPrivateResidue p := by
  unfold factorialBlockPrivateResidue
    factorialBlockPrivateOwnerTerm
  apply endpointPrivateResidue_owner_lower_bound
  · exact Nat.factorial_pos _
  · intro m hm
    exact factorialGapDenominator_pos_of_mem hm
  · exact
      factorialBlock_tail_le_baseNumerator_of_endpointGap_pos
        hgap
  · exact hn
  · exact
      factorialBlockPrime_dvd_privateQuotient_of_unique_upper_prime
        hq hpn hqden hunique
  · exact
      factorialBlockPrivateOwnerTerm_mod_pos_of_unique_upper_prime
        hq hpn hn hqden hunique

/-- The literal natural endpoint numerator over its lcm is exactly the
analytic endpoint gap. -/
theorem factorialBlockEndpointNumerator_div_endpointLcm_eq_gap
    {p : ℕ}
    (htail :
      factorialBlockTailNumerator p ≤
        factorialBlockBaseNumerator p) :
    (factorialBlockEndpointNumerator p : ℚ) /
        factorialBlockEndpointLcm p =
      factorialBlockEndpointGap p := by
  have hident :=
    endpointNumerator_div_endpointDenominatorLcm
      (K := factorialBlockCoefficient p)
      (base := factorialBlockBase p)
      (s := factorialBlockIndices p)
      (d := factorialGapDenominator)
      (Nat.factorial_pos _)
      (fun n hn => factorialGapDenominator_pos_of_mem hn)
      htail
  rw [factorialBlock_reciprocalSum_eq_factorialGapPrefix] at hident
  simpa [
    factorialBlockEndpointNumerator,
    factorialBlockEndpointLcm,
    factorialBlockEndpointGap
  ] using hident

/-- The literal scale in the endpoint window is positive for every
nonzero block parameter. -/
theorem factorialBlockScale_pos
    {p : ℕ} (hp : 0 < p) :
    0 < factorialBlockScale p := by
  unfold factorialBlockScale
  positivity

/-- The analytic upper endpoint of the literal window cross-multiplies
exactly to the natural inequality consumed by the CRT closing theorem. -/
theorem factorialBlock_scaled_upper_bound_of_endpointWindow
    {p : ℕ}
    (hp : 0 < p)
    (hwindow : factorialBlockEndpointWindow p) :
    factorialBlockScale p *
        factorialBlockEndpointNumerator p ≤
      factorialBlockBudget p *
        factorialBlockEndpointLcm p := by
  have htail :=
    factorialBlock_tail_le_baseNumerator_of_endpointGap_pos
      hwindow.1
  have hratio :=
    factorialBlockEndpointNumerator_div_endpointLcm_eq_gap
      htail
  have hLpos :
      0 < factorialBlockEndpointLcm p := by
    apply endpointDenominatorLcm_pos
      (base := factorialBlockBase p)
      (s := factorialBlockIndices p)
      (d := factorialGapDenominator)
    · exact Nat.factorial_pos _
    · intro n hn
      exact factorialGapDenominator_pos_of_mem hn
  have hLposQ :
      (0 : ℚ) < factorialBlockEndpointLcm p := by
    exact_mod_cast hLpos
  have hscalePosQ :
      (0 : ℚ) < factorialBlockScale p := by
    exact_mod_cast factorialBlockScale_pos hp
  have hgapUpper := hwindow.2
  rw [← hratio] at hgapUpper
  unfold factorialBlockEndpointUpperBound at hgapUpper
  rw [div_le_div_iff₀ hLposQ hscalePosQ] at hgapUpper
  exact_mod_cast (show
    (factorialBlockScale p : ℚ) *
          factorialBlockEndpointNumerator p ≤
        (factorialBlockBudget p : ℚ) *
          factorialBlockEndpointLcm p by
      simpa [mul_comm] using hgapUpper)

/-- Direct factorial-block form of the integral Archimedean--CRT closing
criterion.  The only problem-specific inputs left are the endpoint upper
bound and the strict residue inequality. -/
theorem factorialBlock_scaled_upper_bound_false
    {p : ℕ}
    (htail :
      factorialBlockTailNumerator p ≤
        factorialBlockBaseNumerator p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hupper :
      factorialBlockScale p *
          factorialBlockEndpointNumerator p ≤
        factorialBlockBudget p *
          factorialBlockEndpointLcm p)
    (hlarge :
      factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          factorialBlockPrivateResidue p) :
    False := by
  apply endpoint_scaled_upper_bound_false_of_privateResidue
    (K := factorialBlockCoefficient p)
    (base := factorialBlockBase p)
    (s := factorialBlockIndices p)
    (d := factorialGapDenominator)
  · exact Nat.factorial_pos _
  · intro n hn
    exact factorialGapDenominator_pos_of_mem hn
  · exact htail
  · exact hR
  · exact hupper
  · exact hlarge

/-- Once the literal endpoint window holds, its positivity and upper
endpoint are internal: only nontrivial private support and the strict
residue lower bound remain as closing inputs. -/
theorem factorialBlock_endpointWindow_false_of_privateResidue
    {p : ℕ}
    (hp : 0 < p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hwindow : factorialBlockEndpointWindow p)
    (hlarge :
      factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          factorialBlockPrivateResidue p) :
    False := by
  apply factorialBlock_scaled_upper_bound_false
  · exact
      factorialBlock_tail_le_baseNumerator_of_endpointGap_pos
        hwindow.1
  · exact hR
  · exact
      factorialBlock_scaled_upper_bound_of_endpointWindow hp hwindow
  · exact hlarge

/-- Coefficient-free global form of the literal closing criterion.  The
strict-successor coefficient disappears entirely: only the reciprocal-tail
numerator and the private modulus remain. -/
theorem factorialBlock_endpointWindow_false_of_global_complementaryTail
    {p : ℕ}
    (hp : 0 < p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hwindow : factorialBlockEndpointWindow p)
    (hlarge :
      factorialBlockBudget p *
            factorialBlockEndpointLcm p <
        factorialBlockScale p *
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p)) :
    False := by
  apply factorialBlock_endpointWindow_false_of_privateResidue
    hp hR hwindow
  rw [factorialBlockPrivateResidue_eq_complementaryTail
    hwindow.1 (by omega)]
  exact hlarge

/-- Any global complementary-tail certificate excludes a full block of
unit carries: at least one carry from `p` through `2p` must be non-unit. -/
theorem exists_nonunitCarry_in_primeBlock_of_global_complementaryTail
    {p : ℕ}
    (hp : 3 ≤ p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hlarge :
      factorialBlockBudget p *
            factorialBlockEndpointLcm p <
        factorialBlockScale p *
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p)) :
    ∃ m ∈ Finset.Icc p (2 * p),
      factorialGapStepCarry m ≠ 1 := by
  by_contra hnone
  have hunit :
      ∀ m ∈ Finset.Icc p (2 * p),
        factorialGapStepCarry m = 1 := by
    intro m hm
    by_contra hne
    exact hnone ⟨m, hm, hne⟩
  exact
    factorialBlock_endpointWindow_false_of_global_complementaryTail
      (by omega) hR
      (factorialBlockEndpointWindow_of_unitCarryBlock hp hunit)
      hlarge

/-- Fractional-part specialization of the carry bridge.  A collision-scaled
prefix that stays above the explicit ceiling-gap threshold certifies a
non-unit carry in the same dyadic prime block. -/
theorem exists_nonunitCarry_in_primeBlock_of_collisionCeilingGap
    {p : ℕ}
    (hp : 3 ≤ p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hgap :
      ((factorialBlockBudget p *
            factorialBlockCollisionCore p : ℕ) : ℚ) <
        (factorialBlockScale p : ℚ) *
          (((factorialBlockTailNumerator p /
                factorialBlockPrivateModulus p + 1 : ℕ) : ℚ) -
            (factorialBlockCollisionCore p : ℚ) *
              factorialGapPrefix (2 * p - 1))) :
    ∃ m ∈ Finset.Icc p (2 * p),
      factorialGapStepCarry m ≠ 1 := by
  apply exists_nonunitCarry_in_primeBlock_of_global_complementaryTail
    hp hR
  exact
    factorialBlock_globalComplementaryTail_inequality_of_ceilingGap
      hR hgap

/-- Exact rational-prefix form of the collision-ceiling bridge.  The same
certificate produces an index in the prime block at which the computable
strict successor is not divisible by its index. -/
theorem exists_not_dvd_strictFacTopRat_in_primeBlock_of_collisionCeilingGap
    {p : ℕ}
    (hp : 3 ≤ p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hgap :
      ((factorialBlockBudget p *
            factorialBlockCollisionCore p : ℕ) : ℚ) <
        (factorialBlockScale p : ℚ) *
          (((factorialBlockTailNumerator p /
                factorialBlockPrivateModulus p + 1 : ℕ) : ℚ) -
            (factorialBlockCollisionCore p : ℚ) *
              factorialGapPrefix (2 * p - 1))) :
    ∃ m ∈ Finset.Icc p (2 * p),
      ¬(m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m := by
  obtain ⟨m, hm, hcarry⟩ :=
    exists_nonunitCarry_in_primeBlock_of_collisionCeilingGap
      hp hR hgap
  refine ⟨m, hm, ?_⟩
  intro hdvd
  apply hcarry
  apply
    (factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat
      (m := m) (by
        have hmLower := (Finset.mem_Icc.mp hm).1
        omega)).2
  exact hdvd

/-- Two unequal literal leave-one-out projections turn their smaller
modulus into a certified lower bound for the true private residue.  This
is the direct two-projection closing criterion for the Erdős #68 endpoint
window. -/
theorem factorialBlock_endpointWindow_false_of_leaveOneOut_disagreement
    {p i j : ℕ}
    (hp : 0 < p)
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hwindow : factorialBlockEndpointWindow p)
    (hneq :
      projectedResidue
          (factorialBlockEndpointNumerator p)
          (factorialBlockLeaveOneOutModulus p i) ≠
        projectedResidue
          (factorialBlockEndpointNumerator p)
          (factorialBlockLeaveOneOutModulus p j))
    (hlarge :
      factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          min
            (factorialBlockLeaveOneOutModulus p i)
            (factorialBlockLeaveOneOutModulus p j)) :
    False := by
  have hneqPrivate :
      projectedResidue
          (factorialBlockPrivateResidue p)
          (factorialBlockLeaveOneOutModulus p i) ≠
        projectedResidue
          (factorialBlockPrivateResidue p)
          (factorialBlockLeaveOneOutModulus p j) := by
    intro heq
    apply hneq
    calc
      projectedResidue
            (factorialBlockEndpointNumerator p)
            (factorialBlockLeaveOneOutModulus p i) =
          projectedResidue
            (factorialBlockPrivateResidue p)
            (factorialBlockLeaveOneOutModulus p i) :=
        (factorialBlockPrivateResidue_projected_eq_endpointNumerator
          hi).symm
      _ =
          projectedResidue
            (factorialBlockPrivateResidue p)
            (factorialBlockLeaveOneOutModulus p j) :=
        heq
      _ =
          projectedResidue
            (factorialBlockEndpointNumerator p)
            (factorialBlockLeaveOneOutModulus p j) :=
        factorialBlockPrivateResidue_projected_eq_endpointNumerator hj
  apply factorialBlock_endpointWindow_false_of_privateResidue
    hp hR hwindow
  exact hlarge.trans_le
    (Nat.mul_le_mul_left
      (factorialBlockScale p)
      (leaveOneOut_disagreement_forces_min_modulus_le_residue
        hneqPrivate))

/-- Fully computable two-projection form: disagreement is checked on the
complementary reciprocal-tail projections, which do not contain the
strict-successor coefficient. -/
theorem factorialBlock_endpointWindow_false_of_complementary_leaveOneOut_disagreement
    {p i j : ℕ}
    (hp : 0 < p)
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hwindow : factorialBlockEndpointWindow p)
    (hneq :
      complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockLeaveOneOutModulus p i) ≠
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockLeaveOneOutModulus p j))
    (hlarge :
      factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          min
            (factorialBlockLeaveOneOutModulus p i)
            (factorialBlockLeaveOneOutModulus p j)) :
    False := by
  have hLpos :
      0 < factorialBlockEndpointLcm p := by
    apply endpointDenominatorLcm_pos
      (base := factorialBlockBase p)
      (s := factorialBlockIndices p)
      (d := factorialGapDenominator)
    · exact Nat.factorial_pos _
    · intro n hn
      exact factorialGapDenominator_pos_of_mem hn
  have hbudgetPos :
      0 < factorialBlockBudget p := by
    unfold factorialBlockBudget
    omega
  have hscaledMinPos :
      0 <
        factorialBlockScale p *
          min
            (factorialBlockLeaveOneOutModulus p i)
            (factorialBlockLeaveOneOutModulus p j) :=
    (Nat.mul_pos hbudgetPos hLpos).trans hlarge
  have hminPos :
      0 <
        min
          (factorialBlockLeaveOneOutModulus p i)
          (factorialBlockLeaveOneOutModulus p j) :=
    pos_of_mul_pos_right hscaledMinPos (Nat.zero_le _)
  have hQi :
      0 < factorialBlockLeaveOneOutModulus p i :=
    hminPos.trans_le (min_le_left _ _)
  have hQj :
      0 < factorialBlockLeaveOneOutModulus p j :=
    hminPos.trans_le (min_le_right _ _)
  apply factorialBlock_endpointWindow_false_of_leaveOneOut_disagreement
    hp hi hj hR hwindow
  · simpa only [
      factorialBlockEndpointNumerator_projected_eq_complementaryTail
        hwindow.1 hi hQi,
      factorialBlockEndpointNumerator_projected_eq_complementaryTail
        hwindow.1 hj hQj
    ] using hneq
  · exact hlarge

/-- Factor-level two-projection criterion.  Any two divisor factors of
`R_p` with disagreeing complementary views give the same residue lower
bound as two full owner quotients. -/
theorem factorialBlock_endpointWindow_false_of_complementary_factor_disagreement
    {p a b : ℕ}
    (hp : 0 < p)
    (ha : a ∣ factorialBlockPrivateModulus p)
    (hb : b ∣ factorialBlockPrivateModulus p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hwindow : factorialBlockEndpointWindow p)
    (hneq :
      complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockFactorProjectionModulus p a) ≠
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockFactorProjectionModulus p b))
    (hlarge :
      factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          min
            (factorialBlockFactorProjectionModulus p a)
            (factorialBlockFactorProjectionModulus p b)) :
    False := by
  have hRPos : 0 < factorialBlockPrivateModulus p := by
    omega
  have hQaDvd :=
    factorialBlockFactorProjectionModulus_dvd_privateModulus ha
  have hQbDvd :=
    factorialBlockFactorProjectionModulus_dvd_privateModulus hb
  have hQaPos :
      0 < factorialBlockFactorProjectionModulus p a :=
    Nat.pos_of_dvd_of_pos hQaDvd hRPos
  have hQbPos :
      0 < factorialBlockFactorProjectionModulus p b :=
    Nat.pos_of_dvd_of_pos hQbDvd hRPos
  have hglobalEq :=
    factorialBlockPrivateResidue_eq_complementaryTail
      hwindow.1 hRPos
  have hprojA :=
    projectedResidue_complementaryProjectedResidue_eq_of_dvd
      (T := factorialBlockTailNumerator p)
      hRPos hQaPos hQaDvd
  have hprojB :=
    projectedResidue_complementaryProjectedResidue_eq_of_dvd
      (T := factorialBlockTailNumerator p)
      hRPos hQbPos hQbDvd
  have hneqPrivate :
      projectedResidue
          (factorialBlockPrivateResidue p)
          (factorialBlockFactorProjectionModulus p a) ≠
        projectedResidue
          (factorialBlockPrivateResidue p)
          (factorialBlockFactorProjectionModulus p b) := by
    rw [hglobalEq, hprojA, hprojB]
    exact hneq
  apply factorialBlock_endpointWindow_false_of_privateResidue
    hp hR hwindow
  exact hlarge.trans_le
    (Nat.mul_le_mul_left
      (factorialBlockScale p)
      (projection_disagreement_forces_min_modulus_le_residue
        hneqPrivate))

/-- Quotient-cancelled factor-level criterion.  The selected factors may
split a single moving owner quotient, so the remaining producer no longer
requires two moving denominator indices. -/
theorem factorialBlock_endpointWindow_false_of_complementary_factor_disagreement_collisionCap
    {p a b : ℕ}
    (hp : 0 < p)
    (ha : a ∣ factorialBlockPrivateModulus p)
    (hb : b ∣ factorialBlockPrivateModulus p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hwindow : factorialBlockEndpointWindow p)
    (hneq :
      complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockFactorProjectionModulus p a) ≠
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockFactorProjectionModulus p b))
    (hcap :
      factorialBlockBudget p *
            factorialBlockCollisionCore p *
          max a b <
        factorialBlockScale p) :
    False := by
  exact
    factorialBlock_endpointWindow_false_of_complementary_factor_disagreement
      hp ha hb hR hwindow hneq
      (factorialBlock_scaled_min_factorProjection_of_collisionCap
        ha hb hcap)

/-- Quotient-cancelled two-projection criterion.  Instead of comparing
against the near-full leave-one-out moduli, it is enough to bound the
collision core times the larger of the two deleted private quotients. -/
theorem factorialBlock_endpointWindow_false_of_complementary_disagreement_collisionCap
    {p i j : ℕ}
    (hp : 0 < p)
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hwindow : factorialBlockEndpointWindow p)
    (hneq :
      complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockLeaveOneOutModulus p i) ≠
        complementaryProjectedResidue
          (factorialBlockTailNumerator p)
          (factorialBlockLeaveOneOutModulus p j))
    (hcap :
      factorialBlockBudget p *
            factorialBlockCollisionCore p *
          max
            (factorialBlockPrivateQuotient p i)
            (factorialBlockPrivateQuotient p j) <
        factorialBlockScale p) :
    False := by
  exact
    factorialBlock_endpointWindow_false_of_complementary_leaveOneOut_disagreement
      hp hi hj hR hwindow hneq
      (factorialBlock_scaled_min_leaveOneOut_of_collisionCap
        hi hj hcap)

/-- Unconditional factor-pair closing criterion.  Coprimality makes the
two factor projections jointly recover `R_p`; the pair floor then handles
both equality and disagreement without requiring distinct owner indices. -/
theorem factorialBlock_endpointWindow_false_of_complementaryFactorPairFloor
    {p a b : ℕ}
    (hp : 0 < p)
    (ha : a ∣ factorialBlockPrivateModulus p)
    (hb : b ∣ factorialBlockPrivateModulus p)
    (hab : Nat.Coprime a b)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hwindow : factorialBlockEndpointWindow p)
    (hlarge :
      factorialBlockBudget p *
            factorialBlockEndpointLcm p <
        factorialBlockScale p *
          factorialBlockComplementaryFactorPairFloor p a b) :
    False := by
  apply
    factorialBlock_endpointWindow_false_of_global_complementaryTail
      hp hR hwindow
  exact hlarge.trans_le
    (Nat.mul_le_mul_left
      (factorialBlockScale p)
      (factorialBlock_complementaryFactorPairFloor_le_global
        ha hb hab hR))

/-- Unconditional two-owner closing criterion.  The pair floor internally
chooses the exact equality or disagreement branch, so callers only provide
two distinct owners and one coefficient-free scale inequality. -/
theorem factorialBlock_endpointWindow_false_of_complementaryPairFloor
    {p i j : ℕ}
    (hp : 0 < p)
    (hi : i ∈ factorialBlockIndices p)
    (hj : j ∈ factorialBlockIndices p)
    (hij : i ≠ j)
    (hR : 1 < factorialBlockPrivateModulus p)
    (hwindow : factorialBlockEndpointWindow p)
    (hlarge :
      factorialBlockBudget p *
            factorialBlockEndpointLcm p <
        factorialBlockScale p *
          factorialBlockComplementaryPairFloor p i j) :
    False := by
  apply
    factorialBlock_endpointWindow_false_of_global_complementaryTail
      hp hR hwindow
  exact hlarge.trans_le
    (Nat.mul_le_mul_left
      (factorialBlockScale p)
      (factorialBlock_complementaryPairFloor_le_global
        hi hj hij hR))

/-- A cofinal lower bound for the single coefficient-free complementary
tail residue is already sufficient for irrationality.  This is the most
compressed global residue producer exposed by the literal block route. -/
theorem irrational_factorialGapSeries_of_cofinal_global_complementaryTail
    (hcert :
      ∀ B : ℕ, ∃ p : ℕ,
        p.Prime ∧
        B < p ∧
        1 < factorialBlockPrivateModulus p ∧
        factorialBlockBudget p *
              factorialBlockEndpointLcm p <
          factorialBlockScale p *
            complementaryProjectedResidue
              (factorialBlockTailNumerator p)
              (factorialBlockPrivateModulus p)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  by_contra hrat
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  obtain ⟨p, hpPrime, hpLarge, hR, hscale⟩ :=
    hcert (max 3 (r.den + 1))
  have hp3 : 3 ≤ p := by omega
  have hden : r.den ≤ p - 1 := by omega
  have hseries :
      _root_.Erdos68.factorialGapSeries =
        (r.num : ℝ) / (r.den : ℝ) := by
    rw [hr, Rat.cast_def]
  have hwindow :=
    factorialBlockEndpointWindow_of_series_eq_rat
      hp3 r.den_pos hden hseries
  exact
    factorialBlock_endpointWindow_false_of_global_complementaryTail
      hpPrime.pos hR hwindow hscale

/-- Cofinal collision-ceiling certificates produce cofinally many non-unit
carries, with one witness localized inside each corresponding dyadic prime
block. -/
theorem cofinal_nonunitCarries_of_cofinal_collisionCeilingGap
    (hcert :
      ∀ B : ℕ, ∃ p : ℕ,
        p.Prime ∧
        B < p ∧
        1 < factorialBlockPrivateModulus p ∧
        ((factorialBlockBudget p *
              factorialBlockCollisionCore p : ℕ) : ℚ) <
          (factorialBlockScale p : ℚ) *
            (((factorialBlockTailNumerator p /
                  factorialBlockPrivateModulus p + 1 : ℕ) : ℚ) -
              (factorialBlockCollisionCore p : ℚ) *
                factorialGapPrefix (2 * p - 1))) :
    ∀ B : ℕ, ∃ m : ℕ,
      B < m ∧ factorialGapStepCarry m ≠ 1 := by
  intro B
  obtain ⟨p, hpPrime, hpLarge, hR, hgap⟩ :=
    hcert (max 3 B)
  obtain ⟨m, hm, hne⟩ :=
    exists_nonunitCarry_in_primeBlock_of_collisionCeilingGap
      (p := p) (by omega) hR hgap
  have hmBounds := Finset.mem_Icc.mp hm
  exact ⟨m, by omega, hne⟩

/-- Cofinal collision-ceiling certificates produce cofinally many failures
of the exact rational-prefix divisibility test.  This is the direct
integral producer consumed by
`irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses`. -/
theorem cofinal_strictFacTopRat_misses_of_cofinal_collisionCeilingGap
    (hcert :
      ∀ B : ℕ, ∃ p : ℕ,
        p.Prime ∧
        B < p ∧
        1 < factorialBlockPrivateModulus p ∧
        ((factorialBlockBudget p *
              factorialBlockCollisionCore p : ℕ) : ℚ) <
          (factorialBlockScale p : ℚ) *
            (((factorialBlockTailNumerator p /
                  factorialBlockPrivateModulus p + 1 : ℕ) : ℚ) -
              (factorialBlockCollisionCore p : ℚ) *
                factorialGapPrefix (2 * p - 1))) :
    ∀ B : ℕ, ∃ m : ℕ,
      B < m ∧
        ¬(m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m := by
  intro B
  obtain ⟨m, hm, hcarry⟩ :=
    cofinal_nonunitCarries_of_cofinal_collisionCeilingGap
      hcert (max 3 B)
  refine ⟨m, by omega, ?_⟩
  intro hdvd
  apply hcarry
  exact
    (factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat
      (m := m) (by omega)).2 hdvd

/-- Fractional-part form of the complete irrationality reduction.  It is
enough to prove cofinally that the collision-scaled genuine prefix stays
far enough below its next integer. -/
theorem irrational_factorialGapSeries_of_cofinal_collisionCeilingGap
    (hcert :
      ∀ B : ℕ, ∃ p : ℕ,
        p.Prime ∧
        B < p ∧
        1 < factorialBlockPrivateModulus p ∧
        ((factorialBlockBudget p *
              factorialBlockCollisionCore p : ℕ) : ℚ) <
          (factorialBlockScale p : ℚ) *
            (((factorialBlockTailNumerator p /
                  factorialBlockPrivateModulus p + 1 : ℕ) : ℚ) -
              (factorialBlockCollisionCore p : ℚ) *
                factorialGapPrefix (2 * p - 1))) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply irrational_factorialGapSeries_of_cofinal_nonunit_carries
  exact
    cofinal_nonunitCarries_of_cofinal_collisionCeilingGap hcert

/-- A cofinal family of literal two-projection certificates proves the
irrationality of the Erdős #68 series.  All analytic and rational-grid
steps are discharged here; the remaining producer is purely integral:
find arbitrarily large prime blocks with two disagreeing complementary
leave-one-out projections and the displayed scale separation. -/
theorem irrational_factorialGapSeries_of_cofinal_complementary_leaveOneOut_disagreement
    (hcert :
      ∀ B : ℕ, ∃ p i j : ℕ,
        p.Prime ∧
        B < p ∧
        i ∈ factorialBlockIndices p ∧
        j ∈ factorialBlockIndices p ∧
        1 < factorialBlockPrivateModulus p ∧
        complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockLeaveOneOutModulus p i) ≠
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockLeaveOneOutModulus p j) ∧
        factorialBlockBudget p *
              factorialBlockEndpointLcm p <
          factorialBlockScale p *
            min
              (factorialBlockLeaveOneOutModulus p i)
              (factorialBlockLeaveOneOutModulus p j)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  by_contra hrat
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  obtain ⟨p, i, j, hpPrime, hpLarge, hi, hj, hR, hneq, hscale⟩ :=
    hcert (max 3 (r.den + 1))
  have hp3 : 3 ≤ p := by omega
  have hden : r.den ≤ p - 1 := by omega
  have hseries :
      _root_.Erdos68.factorialGapSeries =
        (r.num : ℝ) / (r.den : ℝ) := by
    rw [hr, Rat.cast_def]
  have hwindow :=
    factorialBlockEndpointWindow_of_series_eq_rat
      hp3 r.den_pos hden hseries
  exact
    factorialBlock_endpointWindow_false_of_complementary_leaveOneOut_disagreement
      hpPrime.pos hi hj hR hwindow hneq hscale

/-- Complete quotient-cancelled irrationality reduction.  The remaining
cofinal producer now has no full private modulus or endpoint lcm: it asks
for two disagreeing coefficient-free projections and the local bound
`(2p+1) C_p max(r_i,r_j) < 2p^2(2p-1)!`. -/
theorem irrational_factorialGapSeries_of_cofinal_complementary_disagreement_collisionCap
    (hcert :
      ∀ B : ℕ, ∃ p i j : ℕ,
        p.Prime ∧
        B < p ∧
        i ∈ factorialBlockIndices p ∧
        j ∈ factorialBlockIndices p ∧
        1 < factorialBlockPrivateModulus p ∧
        complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockLeaveOneOutModulus p i) ≠
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockLeaveOneOutModulus p j) ∧
        factorialBlockBudget p *
              factorialBlockCollisionCore p *
            max
              (factorialBlockPrivateQuotient p i)
              (factorialBlockPrivateQuotient p j) <
          factorialBlockScale p) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_complementary_leaveOneOut_disagreement
  intro B
  obtain ⟨p, i, j, hpPrime, hpLarge, hi, hj, hR, hneq, hcap⟩ :=
    hcert B
  refine ⟨p, i, j, hpPrime, hpLarge, hi, hj, hR, hneq, ?_⟩
  exact
    factorialBlock_scaled_min_leaveOneOut_of_collisionCap
      hi hj hcap

/-- Factor-split form of the base-cancelled irrationality reduction.  A
cofinal certificate may now select any two factors of `R_p`; in particular
both can lie inside one moving private owner quotient. -/
theorem
    irrational_factorialGapSeries_of_cofinal_complementary_factor_disagreement_normalizedCollisionCap
    (hcert :
      ∀ B : ℕ, ∃ p a b : ℕ,
        p.Prime ∧
        B < p ∧
        a ∣ factorialBlockPrivateModulus p ∧
        b ∣ factorialBlockPrivateModulus p ∧
        1 < factorialBlockPrivateModulus p ∧
        complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p a) ≠
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p b) ∧
        factorialBlockBudget p *
              factorialBlockNormalizedCollisionCore p *
            max a b <
          2 * p ^ 2 * factorialBlockUpperDescFactorial p) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  by_contra hrat
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  obtain ⟨p, a, b, hpPrime, hpLarge, ha, hb, hR, hneq, hcap⟩ :=
    hcert (max 3 (r.den + 1))
  have hp3 : 3 ≤ p := by omega
  have hden : r.den ≤ p - 1 := by omega
  have hseries :
      _root_.Erdos68.factorialGapSeries =
        (r.num : ℝ) / (r.den : ℝ) := by
    rw [hr, Rat.cast_def]
  have hwindow :=
    factorialBlockEndpointWindow_of_series_eq_rat
      hp3 r.den_pos hden hseries
  exact
    factorialBlock_endpointWindow_false_of_complementary_factor_disagreement_collisionCap
      hpPrime.pos ha hb hR hwindow hneq
      (factorialBlock_factorCollisionCap_of_normalizedCollisionCap
        hpPrime.pos hcap)

/-- Base-cancelled form of the complete two-projection reduction.  Its
quantitative producer compares only the normalized collision core against
the upper factorial block `p⋯(2p-1)`. -/
theorem
    irrational_factorialGapSeries_of_cofinal_complementary_disagreement_normalizedCollisionCap
    (hcert :
      ∀ B : ℕ, ∃ p i j : ℕ,
        p.Prime ∧
        B < p ∧
        i ∈ factorialBlockIndices p ∧
        j ∈ factorialBlockIndices p ∧
        1 < factorialBlockPrivateModulus p ∧
        complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockLeaveOneOutModulus p i) ≠
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockLeaveOneOutModulus p j) ∧
        factorialBlockBudget p *
              factorialBlockNormalizedCollisionCore p *
            max
              (factorialBlockPrivateQuotient p i)
              (factorialBlockPrivateQuotient p j) <
          2 * p ^ 2 * factorialBlockUpperDescFactorial p) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_complementary_disagreement_collisionCap
  intro B
  obtain ⟨p, i, j, hpPrime, hpLarge, hi, hj, hR, hneq, hcap⟩ :=
    hcert B
  refine ⟨p, i, j, hpPrime, hpLarge, hi, hj, hR, hneq, ?_⟩
  exact
    factorialBlock_collisionCap_of_normalizedCollisionCap
      hpPrime.pos hcap

/-- Cofinal coprime factor-pair floors on arbitrary natural block
parameters prove irrationality.  No primality of the parameter is used by
the endpoint-window contradiction: `3 ≤ p` is the exact local hypothesis.
This form accepts the tailored blocks produced by least factorial-gap hits. -/
theorem irrational_factorialGapSeries_of_cofinal_complementaryFactorPairFloor_nat
    (hcert :
      ∀ B : ℕ, ∃ p a b : ℕ,
        3 ≤ p ∧
        B < p ∧
        a ∣ factorialBlockPrivateModulus p ∧
        b ∣ factorialBlockPrivateModulus p ∧
        Nat.Coprime a b ∧
        1 < factorialBlockPrivateModulus p ∧
        factorialBlockBudget p *
              factorialBlockEndpointLcm p <
          factorialBlockScale p *
            factorialBlockComplementaryFactorPairFloor p a b) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  by_contra hrat
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hrat
  obtain ⟨p, a, b, hp3, hpLarge, ha, hb, hab, hR, hscale⟩ :=
    hcert (max 3 (r.den + 1))
  have hden : r.den ≤ p - 1 := by omega
  have hseries :
      _root_.Erdos68.factorialGapSeries =
        (r.num : ℝ) / (r.den : ℝ) := by
    rw [hr, Rat.cast_def]
  have hwindow :=
    factorialBlockEndpointWindow_of_series_eq_rat
      hp3 r.den_pos hden hseries
  exact
    factorialBlock_endpointWindow_false_of_complementaryFactorPairFloor
      (by omega) ha hb hab hR hwindow hscale

/-- Cofinal coprime factor-pair floors on prime parameters prove
irrationality.  This compatibility form retains the historical
prime-endpoint interface; the natural-parameter theorem above is strictly
more general and accepts tailored least-hit blocks. -/
theorem irrational_factorialGapSeries_of_cofinal_complementaryFactorPairFloor
    (hcert :
      ∀ B : ℕ, ∃ p a b : ℕ,
        p.Prime ∧
        B < p ∧
        a ∣ factorialBlockPrivateModulus p ∧
        b ∣ factorialBlockPrivateModulus p ∧
        Nat.Coprime a b ∧
        1 < factorialBlockPrivateModulus p ∧
        factorialBlockBudget p *
              factorialBlockEndpointLcm p <
          factorialBlockScale p *
            factorialBlockComplementaryFactorPairFloor p a b) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_global_complementaryTail
  intro B
  obtain ⟨p, a, b, hpPrime, hpLarge, ha, hb, hab, hR, hscale⟩ :=
    hcert B
  refine ⟨p, hpPrime, hpLarge, hR, ?_⟩
  exact hscale.trans_le
    (Nat.mul_le_mul_left
      (factorialBlockScale p)
      (factorialBlock_complementaryFactorPairFloor_le_global
        ha hb hab hR))

/-- Cofinal unconditional pair-floor certificates prove irrationality.
Unlike the older two-projection interface, this producer does not require
the caller to establish projection disagreement: equality is converted
exactly into the global complementary residue branch. -/
theorem irrational_factorialGapSeries_of_cofinal_complementaryPairFloor
    (hcert :
      ∀ B : ℕ, ∃ p i j : ℕ,
        p.Prime ∧
        B < p ∧
        i ∈ factorialBlockIndices p ∧
        j ∈ factorialBlockIndices p ∧
        i ≠ j ∧
        1 < factorialBlockPrivateModulus p ∧
        factorialBlockBudget p *
              factorialBlockEndpointLcm p <
          factorialBlockScale p *
            factorialBlockComplementaryPairFloor p i j) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply
    irrational_factorialGapSeries_of_cofinal_global_complementaryTail
  intro B
  obtain ⟨p, i, j, hpPrime, hpLarge, hi, hj, hij, hR, hscale⟩ :=
    hcert B
  refine ⟨p, hpPrime, hpLarge, hR, ?_⟩
  exact hscale.trans_le
    (Nat.mul_le_mul_left
      (factorialBlockScale p)
      (factorialBlock_complementaryPairFloor_le_global
        hi hj hij hR))

/-- Any one-owner size certificate forces the full endpoint lcm below an
explicit squared-factorial scale.  The complementary owner residue is at
most `q`, while a supported `q` is at most its owned denominator and hence
strictly below the endpoint factorial. -/
theorem factorialBlock_unique_owner_projection_lcm_ceiling
    {p n q : ℕ}
    (hn : n ∈ factorialBlockIndices p)
    (hqden : q ∣ factorialGapDenominator n)
    (hlarge :
      factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          (q - factorialBlockPrivateOwnerTerm p n % q)) :
    factorialBlockBudget p *
          factorialBlockEndpointLcm p <
      factorialBlockScale p * (2 * p - 1).factorial := by
  have hqLe : q ≤ factorialGapDenominator n :=
    Nat.le_of_dvd
      (factorialGapDenominator_pos_of_mem hn)
      hqden
  have hdenLt : factorialGapDenominator n < n.factorial := by
    unfold factorialGapDenominator
    have hfacPos := Nat.factorial_pos n
    omega
  have hnLe : n ≤ 2 * p - 1 := by
    exact (Finset.mem_Icc.mp hn).2
  have hfacLe : n.factorial ≤ (2 * p - 1).factorial :=
    Nat.factorial_le hnLe
  have hresidueLe :
      q - factorialBlockPrivateOwnerTerm p n % q ≤
        (2 * p - 1).factorial :=
    (Nat.sub_le q _).trans
      (hqLe.trans (hdenLt.le.trans hfacLe))
  exact hlarge.trans_le
    (Nat.mul_le_mul_left (factorialBlockScale p) hresidueLe)

/-- Therefore a reverse squared-factorial lcm bound excludes every
one-owner comparison on that block, independently of how its unique prime
was produced. -/
theorem factorialBlock_not_unique_owner_projection_of_lcm_ge
    {p n q : ℕ}
    (hn : n ∈ factorialBlockIndices p)
    (hqden : q ∣ factorialGapDenominator n)
    (hLcm :
      factorialBlockScale p * (2 * p - 1).factorial ≤
        factorialBlockBudget p *
          factorialBlockEndpointLcm p) :
    ¬factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          (q - factorialBlockPrivateOwnerTerm p n % q) := by
  intro hlarge
  exact (Nat.not_lt_of_ge hLcm)
    (factorialBlock_unique_owner_projection_lcm_ceiling
      hn hqden hlarge)

/-- One uniquely supported upper-half prime now gives a fully explicit
single-projection closing criterion.  Its owner residue is automatically
nonzero; only the final integer comparison remains to be estimated. -/
theorem factorialBlock_endpointWindow_false_of_unique_owner_projection
    {p n q : ℕ}
    (hp : 0 < p)
    (hq : q.Prime)
    (hpn : p ≤ n)
    (hn : n ∈ factorialBlockIndices p)
    (hqden : q ∣ factorialGapDenominator n)
    (hunique :
      ∀ m ∈ factorialBlockIndices p, m ≠ n →
        ¬q ∣ factorialGapDenominator m)
    (hwindow : factorialBlockEndpointWindow p)
    (hlarge :
      factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          (q - factorialBlockPrivateOwnerTerm p n % q)) :
    False := by
  apply factorialBlock_endpointWindow_false_of_privateResidue
    hp
    (factorialBlockPrivateModulus_one_lt_of_unique_upper_prime
      hq hpn hn hqden hunique)
    hwindow
  exact hlarge.trans_le
    (Nat.mul_le_mul_left
      (factorialBlockScale p)
      (factorialBlockPrivateResidue_owner_lower_bound_of_unique_upper_prime
        hwindow.1 hq hpn hn hqden hunique))

/-- A uniquely supported upper-half prime satisfying the one remaining
owner-size inequality already produces a failure of the exact rational
prefix divisibility test inside the same dyadic block. -/
theorem exists_not_dvd_strictFacTopRat_in_primeBlock_of_unique_owner_projection
    {p n q : ℕ}
    (hp : 3 ≤ p)
    (hq : q.Prime)
    (hpn : p ≤ n)
    (hn : n ∈ factorialBlockIndices p)
    (hqden : q ∣ factorialGapDenominator n)
    (hunique :
      ∀ m ∈ factorialBlockIndices p, m ≠ n →
        ¬q ∣ factorialGapDenominator m)
    (hlarge :
      factorialBlockBudget p *
          factorialBlockEndpointLcm p <
        factorialBlockScale p *
          (q - factorialBlockPrivateOwnerTerm p n % q)) :
    ∃ m ∈ Finset.Icc p (2 * p),
      ¬(m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m := by
  by_contra hnone
  have hunit :
      ∀ m ∈ Finset.Icc p (2 * p),
        factorialGapStepCarry m = 1 := by
    intro m hm
    apply
      (factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat
        (m := m) (by
          have hmLower := (Finset.mem_Icc.mp hm).1
          omega)).2
    by_contra hnot
    exact hnone ⟨m, hm, hnot⟩
  exact
    factorialBlock_endpointWindow_false_of_unique_owner_projection
      (by omega) hq hpn hn hqden hunique
      (factorialBlockEndpointWindow_of_unitCarryBlock hp hunit)
      hlarge

/-- Cofinal uniquely supported owner-size certificates land directly in
the exact cofinal miss predicate equivalent to Erdős #68. -/
theorem cofinal_strictFacTopRat_misses_of_cofinal_unique_owner_projection
    (hcert :
      ∀ B : ℕ, ∃ p n q : ℕ,
        B < p ∧
        q.Prime ∧
        p ≤ n ∧
        n ∈ factorialBlockIndices p ∧
        q ∣ factorialGapDenominator n ∧
        (∀ m ∈ factorialBlockIndices p, m ≠ n →
          ¬q ∣ factorialGapDenominator m) ∧
        factorialBlockBudget p *
              factorialBlockEndpointLcm p <
          factorialBlockScale p *
            (q - factorialBlockPrivateOwnerTerm p n % q)) :
    ∀ B : ℕ, ∃ m : ℕ,
      B < m ∧
        ¬(m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m := by
  intro B
  obtain ⟨p, n, q, hpLarge, hq, hpn, hn, hqden, hunique, hlarge⟩ :=
    hcert (max 3 B)
  obtain ⟨m, hm, hmiss⟩ :=
    exists_not_dvd_strictFacTopRat_in_primeBlock_of_unique_owner_projection
      (p := p) (n := n) (q := q)
      (by omega) hq hpn hn hqden hunique hlarge
  have hmBounds := Finset.mem_Icc.mp hm
  exact ⟨m, by omega, hmiss⟩

#print axioms prime_dvd_factorial_sub_one_gt
#print axioms prime_not_dvd_succ_factorial_sub_one_of_dvd
#print axioms prefixPrivate_factorialGap_unique_in_tailoredBlock
#print axioms exists_large_unique_factorialBlock_hit
#print axioms cofinal_unique_factorialBlock_hits_of_cofinal_large_primes
#print axioms gcd_factorial_sub_one_eq_descFactorial_sub_one
#print axioms privateQuotients_coprime_of_gcd_dvd_core
#print axioms factorialGap_privateQuotients_coprime_of_collision
#print axioms finset_lcm_factorization_lt_of_all_lt
#print axioms gcd_dvd_pairwiseCollisionCore
#print axioms gcd_dvd_collisionCore
#print axioms exists_pairwise_primePower_support_of_dvd_pairwiseCollisionCore
#print axioms exists_pairwise_primePower_support_of_dvd_collisionCore
#print axioms primePower_dvd_pairwiseCollisionCore_iff
#print axioms primePower_dvd_collisionCore_iff
#print axioms prime_not_dvd_pairwiseCollisionCore_of_unique_support
#print axioms prime_not_dvd_collisionCore_of_unique_support
#print axioms pairwiseCollisionCore_pos
#print axioms collisionCore_pos
#print axioms pairwiseCollisionCore_dvd_denominatorLcm
#print axioms collisionCore_dvd_endpointDenominatorLcm
#print axioms collisionCore_privateQuotients_pairwise_coprime
#print axioms privateQuotient_eq_one_of_dvd_base
#print axioms privateQuotient_lcm_eq_privateModulus
#print axioms privateModulus_pos
#print axioms prime_dvd_privateQuotient_of_unique_support
#print axioms primePow_dvd_privateQuotient_of_unique_support
#print axioms privateModulus_one_lt_of_unique_prime_support
#print axioms weightedPrivateNumerator_modEq_owner
#print axioms weightedPrivateNumerator_coprime_product
#print axioms collisionWeightedPrivateNumerator_modEq_owner
#print axioms privateWeight_coprime_privateQuotient
#print axioms privateOwnerTerm_mod_prime_pos
#print axioms collisionWeightedPrivateNumerator_coprime_privateModulus
#print axioms lcm_div_gcd_right_distrib
#print axioms finset_lcm_div_gcd_right_distrib
#print axioms privateModulus_eq_lcm_div_gcd_collisionCore
#print axioms privateModulus_eq_endpointDenominatorLcm_div_collisionCore
#print axioms privateModulus_dvd_endpointDenominatorLcm_div_base
#print axioms privateModulus_dvd_endpointBaseNumerator
#print axioms endpointDenominatorTerm_eq_privateWeight_mul_leaveOneOut
#print axioms endpointTailNumerator_eq_collisionWeightedPrivateNumerator
#print axioms endpointNumerator_add_tail_eq_endpointBaseNumerator
#print axioms endpointNumerator_add_tail_modEq_zero
#print axioms endpointNumerator_add_collisionWeightedPrivateNumerator_modEq_zero
#print axioms coprime_left_of_add_modEq_zero
#print axioms endpointNumerator_coprime_privateModulus
#print axioms projectedResidue_eq_complementary_of_add_modEq_zero
#print axioms projectedResidue_endpointPrivateResidue_eq_of_dvd
#print axioms projectedResidue_bounds_of_coprime
#print axioms complementaryProjectedResidue_eq_sub_of_coprime
#print axioms add_complementaryProjectedResidue_eq_succ_div_mul
#print axioms endpointPrivateResidue_bounds
#print axioms endpointPrivateResidue_add_tail_modEq_zero
#print axioms endpointPrivateResidue_add_owner_modEq_zero
#print axioms endpointPrivateResidue_add_owner_modEq_zero_of_dvd
#print axioms complementary_residue_lower_bound
#print axioms endpointPrivateResidue_owner_lower_bound
#print axioms scaled_endpoint_upper_bound_excluded_by_residue
#print axioms endpoint_scaled_upper_bound_false_of_privateResidue
#print axioms min_leaveOneOutModulus_mul_max_eq
#print axioms leaveOneOut_lcm_eq_of_coprime_divisors
#print axioms projectedResidue_complementaryProjectedResidue_eq_of_dvd
#print axioms projectedResidue_eq_residue_of_eq_of_lcm
#print axioms projectionPairFloor_full_divisor_eq_min
#print axioms lt_mul_min_iff
#print axioms projectionPairFloor_le_residue_of_lt_of_lcm
#print axioms factorialBlock_min_factorProjection_mul_max_eq_privateModulus
#print axioms factorialBlock_scaled_min_factorProjection_of_collisionCap
#print axioms factorialBlock_factorProjection_lcm_eq_privateModulus
#print axioms factorialBlock_min_leaveOneOut_mul_max_privateQuotient_eq_privateModulus
#print axioms factorialBlock_scaled_min_leaveOneOut_of_collisionCap
#print axioms factorialBlock_leaveOneOut_lcm_eq_privateModulus
#print axioms factorialBlock_complementaryLeaveOneOut_eq_global_of_eq
#print axioms factorialBlock_unitFactorPairFloor_eq_min
#print axioms factorialBlock_unitFactorPairFloor_scale_iff
#print axioms factorialBlock_complementaryFactorPairFloor_le_global
#print axioms factorialBlock_complementaryPairFloor_le_global
#print axioms factorialBlock_endpointWindow_false_of_complementary_factor_disagreement
#print axioms factorialBlock_endpointWindow_false_of_complementary_factor_disagreement_collisionCap
#print axioms factorialBlock_endpointWindow_false_of_complementary_disagreement_collisionCap
#print axioms factorialBlock_endpointWindow_false_of_complementaryFactorPairFloor
#print axioms factorialBlock_endpointWindow_false_of_complementaryPairFloor
#print axioms irrational_factorialGapSeries_of_cofinal_complementary_factor_disagreement_normalizedCollisionCap
#print axioms irrational_factorialGapSeries_of_cofinal_complementary_disagreement_collisionCap
#print axioms irrational_factorialGapSeries_of_cofinal_complementary_disagreement_normalizedCollisionCap
#print axioms irrational_factorialGapSeries_of_cofinal_complementaryFactorPairFloor_nat
#print axioms irrational_factorialGapSeries_of_cofinal_complementaryFactorPairFloor
#print axioms irrational_factorialGapSeries_of_cofinal_complementaryPairFloor
#print axioms factorialGapTail_eq_next_add_tail
#print axioms factorialGapTail_lt_factorialBlockEndpointUpperBound
#print axioms factorialBlock_addedTerm_add_gridCell_le_endpointUpperBound
#print axioms strictFacTop_factorialGapPrefix_pos
#print axioms factorialBlockCoefficient_cast_eq_strictFacTop
#print axioms factorialBlockEndpointWindow_of_unitCarryBlock
#print axioms factorialBlockEndpointWindow_of_series_eq_rat
#print axioms factorialGapDenominator_pos_of_mem
#print axioms factorialBlockPrivateModulus_pos
#print axioms factorialBlockNormalizedCollisionCore_mul_gapLcm_dvd_gapProd
#print axioms factorialBlockNormalizedCollisionCore_le_gapProd_div_gapLcm
#print axioms factorialBlockNormalizedCollisionCore_pos
#print axioms collisionCore_div_base_eq_pairwiseCollisionCore_div_gcd
#print axioms collisionCore_div_base_factorization
#print axioms primePower_dvd_collisionCore_div_base_iff
#print axioms factorialBlockNormalizedCollisionCore_factorization
#print axioms factorialBlock_primePower_dvd_normalizedCollisionCore_iff_two_hits
#print axioms factorialBlock_primePower_le_gapPow_of_two_hits
#print axioms factorialBlock_prime_hitPair_distance_gt_exponent
#print axioms factorialBlock_hitPair_distance_gt_exponent_of_endpoint_lt_base
#print axioms factorialBlock_primePowerHitCount_mul_succ_le
#print axioms factorialBlock_primePowerHitCount_mul_succ_le_of_endpoint_lt_base
#print axioms exists_factorialBlock_hitPair_with_normalizedPrimePower_le_gapPow
#print axioms exists_factorialBlock_hitPair_distance_gt_of_endpointPow_lt_normalizedPrimePower
#print axioms factorialBlock_normalizedCollision_exponent_add_base_factorization_lt_prime
#print axioms factorialBlock_normalizedCollision_factorization_add_base_lt_prime
#print axioms factorialBlock_normalizedCollision_exponent_add_base_factorization_lt_blockDiameter
#print axioms factorialBlock_normalizedCollision_factorization_add_base_lt_blockDiameter
#print axioms factorialBlock_normalizedCollision_factorization_lt_blockDiameter_of_endpoint_lt_prime
#print axioms factorialBlock_base_factorization_lt_pred_of_dvd_normalizedCollisionCore
#print axioms factorialBlock_prime_mul_pred_gt_pred_of_dvd_normalizedCollisionCore
#print axioms factorialBlock_prime_sq_gt_pred_of_dvd_normalizedCollisionCore
#print axioms factorialBlockNormalizedCollisionCore_coprime_factorial_of_mul_pred_le
#print axioms factorialBlockBase_mul_normalizedCollisionCore
#print axioms factorialBlockBase_mul_upperDescFactorial
#print axioms factorialBlock_factorCollisionCap_of_normalizedCollisionCap
#print axioms factorialBlock_collisionCap_of_normalizedCollisionCap
#print axioms factorialBlockCollisionCore_mul_privateModulus
#print axioms lcm_gcd_left_distrib
#print axioms finset_lcm_gcd_left
#print axioms pairwiseCollisionCore_insert
#print axioms pairwiseCollisionCore_insert_gcd_lcm
#print axioms collisionCore_insert
#print axioms collisionCore_insert_gcd_lcm
#print axioms pairwiseCollisionCore_mul_denominatorLcm_dvd_denominatorProd
#print axioms collisionCore_div_base_dvd_pairwiseCollisionCore
#print axioms collisionCore_div_base_mul_denominatorLcm_dvd_denominatorProd
#print axioms factorialBlockTailNumerator_div_privateModulus_eq_collisionScaledPrefix
#print axioms factorialBlockTailNumerator_coprime_privateModulus
#print axioms factorialBlock_complementaryTailFraction_eq_ceilingGap
#print axioms factorialBlock_globalComplementaryTail_inequality_of_ceilingGap
#print axioms factorialGapDenominator_dvd_factorialBlockBase_of_lt
#print axioms factorialBlockPrivateQuotient_eq_one_of_gap_lt
#print axioms factorialBlockParameter_le_gap_of_privateQuotient_ne_one
#print axioms factorialBlockFixedPairPrivateQuotients_eq_one
#print axioms factorialBlockPrivateQuotient_dvd_privateModulus
#print axioms factorialBlockFactorProjectionModulus_dvd_privateModulus
#print axioms factorialBlockLeaveOneOutModulus_dvd_privateModulus
#print axioms factorialBlockPrivateResidue_projected_eq_endpointNumerator
#print axioms factorialBlockEndpointNumerator_projected_eq_complementaryTail
#print axioms factorialBlockPrivateResidue_eq_complementaryTail
#print axioms factorialBlockPrime_not_dvd_base_of_upper_hit
#print axioms factorialBlockPrime_dvd_normalizedCollisionCore_of_upper_hit_of_dvd_collisionCore
#print axioms exists_two_factorialBlock_hits_of_primePower_dvd_collisionCore
#print axioms factorialBlock_primePower_dvd_collisionCore_iff_two_hits
#print axioms factorialBlock_primePower_dvd_normalizedCollisionCore_iff_of_upper_hit
#print axioms factorialBlock_primePower_dvd_normalizedCollisionCore_iff_one_lt_hitCount
#print axioms factorialBlock_primePower_not_dvd_normalizedCollisionCore_of_hitCount_le_one
#print axioms factorialBlock_normalizedCollisionCore_factorization_lt_of_hitCount_le_one
#print axioms factorialBlock_normalizedCollisionCore_factorization_eq_repeatedHitLayerCount
#print axioms factorialBlock_normalizedCollisionCore_factorization_eq_truncatedRepeatedHitLayerCount
#print axioms factorialBlockPrime_dvd_privateQuotient_of_unique_upper_prime
#print axioms factorialBlockPrivateModulus_one_lt_of_unique_upper_prime
#print axioms factorialBlockPrivateOwnerTerm_mod_pos_of_unique_upper_prime
#print axioms factorialBlockPrivateResidue_owner_lower_bound_of_unique_upper_prime
#print axioms factorialBlockEndpointNumerator_div_endpointLcm_eq_gap
#print axioms factorialBlock_scaled_upper_bound_of_endpointWindow
#print axioms factorialBlock_scaled_upper_bound_false
#print axioms factorialBlock_endpointWindow_false_of_privateResidue
#print axioms factorialBlock_endpointWindow_false_of_global_complementaryTail
#print axioms exists_nonunitCarry_in_primeBlock_of_global_complementaryTail
#print axioms exists_nonunitCarry_in_primeBlock_of_collisionCeilingGap
#print axioms exists_not_dvd_strictFacTopRat_in_primeBlock_of_collisionCeilingGap
#print axioms factorialBlock_endpointWindow_false_of_leaveOneOut_disagreement
#print axioms factorialBlock_endpointWindow_false_of_complementary_leaveOneOut_disagreement
#print axioms irrational_factorialGapSeries_of_cofinal_global_complementaryTail
#print axioms cofinal_nonunitCarries_of_cofinal_collisionCeilingGap
#print axioms cofinal_strictFacTopRat_misses_of_cofinal_collisionCeilingGap
#print axioms irrational_factorialGapSeries_of_cofinal_collisionCeilingGap
#print axioms irrational_factorialGapSeries_of_cofinal_complementary_leaveOneOut_disagreement
#print axioms factorialBlock_unique_owner_projection_lcm_ceiling
#print axioms factorialBlock_not_unique_owner_projection_of_lcm_ge
#print axioms factorialBlock_endpointWindow_false_of_unique_owner_projection
#print axioms exists_not_dvd_strictFacTopRat_in_primeBlock_of_unique_owner_projection
#print axioms cofinal_strictFacTopRat_misses_of_cofinal_unique_owner_projection

end ErdosProblems.Erdos68
