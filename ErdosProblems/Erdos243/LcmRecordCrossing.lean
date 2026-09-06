import ErdosProblems.Erdos243.LcmRecordExcess
import ErdosProblems.Erdos243.SlowRiseBarrier

/-!
# Counting the CRT heights crossed by one arithmetic step

The heights are the actual arithmetic progression `x + k * P`, not an
assumed cardinality bound. This supplies the finite local charging step in
the weighted-record argument of `LcmRecordExcess.md`. First-crossing existence,
uniqueness, and the finite partition across time require no monotonicity of
the numerator sequence. The existing CRT construction supplies the covering
from any finite family of sufficiently large pairwise-coprime old divisors.
Producing that family from an infinite canonical orbit and the analytic
divergence argument are not asserted by this module.
-/

namespace ErdosProblems.Erdos243.LcmRecordCrossing

open LcmRecordExcess

/-- CRT residues cover every integer immediately below every translated
wall, using the same old divisors throughout the progression. -/
theorem covering_of_crt_block {B : ℕ} (m : Fin B → ℕ)
    (x P k : ℕ) (L : ℤ)
    (hm : ∀ i, B < m i) (hmP : ∀ i, m i ∣ P)
    (hmL : ∀ i, (m i : ℤ) ∣ L)
    (hresidue : ∀ i, m i ∣ x + i.1) :
    ∀ z : ℤ, (x + B + k * P : ℕ) - (B : ℤ) ≤ z →
      z < (x + B + k * P : ℕ) →
      ∃ d : ℤ, (B : ℤ) < d ∧ d ∣ L ∧ d ∣ z := by
  intro z hlo hhi
  let base := x + k * P
  have hwall : x + B + k * P = base + B := by dsimp [base]; omega
  rw [hwall] at hlo hhi
  have hnonneg : 0 ≤ z - (base : ℤ) := by omega
  have hindex : (z - (base : ℤ)).toNat < B := by omega
  let i : Fin B := ⟨(z - (base : ℤ)).toNat, hindex⟩
  have hi : (i.1 : ℤ) = z - (base : ℤ) := by
    dsimp [i]
    exact Int.toNat_of_nonneg hnonneg
  have hz : z = ((x + i.1 : ℕ) : ℤ) + ((k * P : ℕ) : ℤ) := by
    calc
      z = (base : ℤ) + (i.1 : ℤ) := by omega
      _ = _ := by dsimp [base]; ring
  refine ⟨m i, by exact_mod_cast hm i, hmL i, ?_⟩
  rw [hz]
  exact dvd_add (Int.natCast_dvd_natCast.mpr (hresidue i))
    (Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right (hmP i) k))

/-- The block product exceeds the baseline, including the empty B=0 block. -/
theorem baseline_lt_block_product {B : ℕ} (m : Fin B → ℕ)
    (hm : ∀ i, B < m i) : B < ∏ i, m i := by
  by_cases hB : B = 0
  · subst B
    simp
  · have hBpos : 0 < B := by omega
    let i : Fin B := ⟨0, hBpos⟩
    have hprodpos : 0 < ∏ j, m j :=
      Finset.prod_pos (fun j _ => lt_of_le_of_lt (Nat.zero_le B) (hm j))
    have hdiv : m i ∣ ∏ j, m j := by
      simpa using Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    exact (hm i).trans_le (Nat.le_of_dvd hprodpos hdiv)

/-- One CRT block provides all translated coverings for every later
denominator divisible by its old moduli. Neither primality nor any
persistence of numerator divisors is assumed. -/
theorem exists_crt_covering_progression {B : ℕ} (m : Fin B → ℕ)
    (hm : ∀ i, B < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) :
    ∃ x, B < (∏ i, m i) ∧ (∏ i, m i) ≤ x ∧ x < 2 * ∏ i, m i ∧
      ∀ L : ℤ, (∀ i, (m i : ℤ) ∣ L) → ∀ k : ℕ, ∀ z : ℤ,
        (x + B + k * (∏ i, m i) : ℕ) - (B : ℤ) ≤ z →
        z < (x + B + k * (∏ i, m i) : ℕ) →
        ∃ d : ℤ, (B : ℤ) < d ∧ d ∣ L ∧ d ∣ z := by
  have hm1 : ∀ i, 1 < m i := by
    intro i
    have := i.isLt
    have := hm i
    omega
  obtain ⟨x, hxlo, hxhi, hresidue⟩ :=
    exists_consecutiveMultiples_between m hm1 hpair
  refine ⟨x, baseline_lt_block_product m hm, hxlo, hxhi, ?_⟩
  intro L hL k
  exact covering_of_crt_block m x (∏ i, m i) k L hm
    (fun i => by simpa using Finset.dvd_prod_of_mem m (Finset.mem_univ i)) hL hresidue

/-- The step ending at `U (n+1)` first reaches height `t`: every earlier
state, including its source, was strictly below that height. -/
def FirstCrossing (U : ℕ → ℕ) (t n : ℕ) : Prop :=
  (∀ j ≤ n, U j < t) ∧ t ≤ U (n + 1)

noncomputable instance (U : ℕ → ℕ) (t n : ℕ) : Decidable (FirstCrossing U t n) :=
  Classical.propDecidable _

/-- Every height above the initial state and reached by time N has exactly
one first crossing before N. Arbitrary downward excursions are allowed. -/
theorem exists_unique_firstCrossing (U : ℕ → ℕ) (t N : ℕ)
    (hzero : U 0 < t) (hN : ∃ j ≤ N, t ≤ U j) :
    ∃! n, n < N ∧ FirstCrossing U t n := by
  obtain ⟨j, hjN, hj⟩ := hN
  let reached : ∃ j, t ≤ U j := ⟨j, hj⟩
  have hreach := Nat.find_spec reached
  have hbound := Nat.find_min' reached hj
  have hpositive : 0 < Nat.find reached := by
    by_contra h
    have hzeroindex : Nat.find reached = 0 := by omega
    rw [hzeroindex] at hreach
    omega
  have hsucc : Nat.find reached - 1 + 1 = Nat.find reached := by omega
  have hfirst : FirstCrossing U t (Nat.find reached - 1) := by
    constructor
    · intro j hj
      have hnot := Nat.find_min reached (show j < Nat.find reached by omega)
      omega
    · simpa only [hsucc] using hreach
  refine ⟨Nat.find reached - 1, ⟨by omega, hfirst⟩, ?_⟩
  intro m hm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hlow := hfirst.1 (m + 1) (by omega)
    have hhigh := hm.2.2
    omega
  · have hlow := hm.2.1 (Nat.find reached - 1 + 1) (by omega)
    have hhigh := hfirst.2
    omega

/-- A first crossing is automatically a strict record, not merely a rise
after a drawdown. -/
theorem FirstCrossing.is_record {U : ℕ → ℕ} {t n : ℕ}
    (h : FirstCrossing U t n) : ∀ j ≤ n, U j < U (n + 1) := by
  intro j hj
  exact (h.1 j hj).trans_le h.2

/-- Each indexed height contributes exactly once to the finite sum over
first-crossing times. No monotonicity or positivity of the weights is needed
for this exact partition identity. -/
theorem sum_firstCrossing_partition (s : Finset ℕ) (U t : ℕ → ℕ)
    (N : ℕ) (w : ℕ → ℝ)
    (hzero : ∀ k ∈ s, U 0 < t k)
    (hN : ∀ k ∈ s, ∃ j ≤ N, t k ≤ U j) :
    ∑ k ∈ s, w k =
      ∑ n ∈ Finset.range N, ∑ k ∈ s,
        if FirstCrossing U (t k) n then w k else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨n, hn, hunique⟩ := exists_unique_firstCrossing U (t k) N
    (hzero k hk) (hN k hk)
  have hiff : ∀ m ∈ Finset.range N, FirstCrossing U (t k) m ↔ m = n := by
    intro m hm
    constructor
    · intro h
      exact hunique m ⟨Finset.mem_range.mp hm, h⟩
    · intro h
      simpa only [h] using hn.2
  symm
  calc
    ∑ m ∈ Finset.range N, (if FirstCrossing U (t k) m then w k else 0) =
        ∑ m ∈ Finset.range N, (if m = n then w k else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [hiff m hm]
    _ = w k := by simp [Finset.mem_range.mpr hn.1]

/-- A finite set of indices in an arithmetic progression has the spacing
bound required by the excess lemma, even if some intermediate heights are
absent from the set. -/
theorem crossed_progression_spacing (s : Finset ℕ) (hs : s.Nonempty)
    (x P U d : ℕ)
    (hlo : ∀ k ∈ s, U < x + k * P)
    (hhi : ∀ k ∈ s, x + k * P ≤ U + d) :
    (s.card - 1) * P < d := by
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨s.min'_le k hk, s.le_max' k hk⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hminmax := s.min'_le_max' hs
  have hspan : s.card - 1 ≤ s.max' hs - s.min' hs := by omega
  have hmul := Nat.mul_le_mul_right P hspan
  have hsplit : s.max' hs = s.min' hs + (s.max' hs - s.min' hs) := by omega
  have hleft := hlo (s.min' hs) (s.min'_mem hs)
  have hright := hhi (s.max' hs) (s.max'_mem hs)
  rw [hsplit, Nat.add_mul] at hright
  omega

/-- The actual crossed heights, together with the arithmetic feedback and
the B-integer covering immediately below each height, bound their own count.
The covering is supplied by CRT in the ordinary global argument. -/
theorem crossed_progression_card_le_excess (s : Finset ℕ)
    (x P U d B : ℕ) (a L : ℤ) (hP : B < P)
    (hlo : ∀ k ∈ s, U < x + k * P)
    (hhi : ∀ k ∈ s, x + k * P ≤ U + d)
    (hfeedback : (d : ℤ) = (a - 1) * U - L)
    (hcover : ∀ k ∈ s, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L ∧ m ∣ z) :
    s.card ≤ d - B := by
  by_cases hs : s.Nonempty
  · obtain ⟨k, hk⟩ := hs
    have hd : 0 < d := by have := hlo k hk; have := hhi k hk; omega
    have hexcess : (B : ℤ) < d :=
      covered_wall_forces_excess (U := U) (d := d) (L := L) (a := a)
        (tau := (x + k * P : ℕ)) (B := B)
        (by exact_mod_cast hd) (by exact_mod_cast hlo k hk)
        (by exact_mod_cast hhi k hk) hfeedback (hcover k hk)
    apply wall_count_le_excess hP (by exact_mod_cast hexcess)
    exact crossed_progression_spacing s ⟨k, hk⟩ x P U d hlo hhi
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

/-- The full local weighted charge, with no assumed wall-count inequality.
The source can lie below the previous record: only the heights crossed by
this actual step enter the hypotheses. -/
theorem crossed_progression_weighted_charge (s : Finset ℕ)
    (x P U d B : ℕ) (a L : ℤ) (hP : B < P)
    (hlo : ∀ k ∈ s, U < x + k * P)
    (hhi : ∀ k ∈ s, x + k * P ≤ U + d)
    (hfeedback : (d : ℤ) = (a - 1) * U - L)
    (hcover : ∀ k ∈ s, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : 0 ≤ f U) :
    ∑ k ∈ s, f (x + k * P) ≤ ((d - B : ℕ) : ℝ) * f U := by
  have hc := crossed_progression_card_le_excess s x P U d B a L hP hlo hhi
    hfeedback hcover
  calc
    ∑ k ∈ s, f (x + k * P) ≤ ∑ _k ∈ s, f U :=
      Finset.sum_le_sum (fun k hk => hf (Nat.le_of_lt (hlo k hk)))
    _ = (s.card : ℝ) * f U := by simp
    _ ≤ ((d - B : ℕ) : ℝ) * f U :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hpos

/-- Finite weighted first-crossing bound, restricted to actual record steps.

The numerator sequence can move down and finish below an earlier record.
Every selected CRT height need only have been reached by time N. Arithmetic
feedback is required only at record steps; the charge is derived from actual
progression spacing and covering, not assumed as a budget hypothesis. -/
theorem finite_record_weighted_bound (s : Finset ℕ) (U : ℕ → ℕ)
    (a L : ℕ → ℤ) (x P B N : ℕ) (hP : B < P)
    (hzero : ∀ k ∈ s, U 0 < x + k * P)
    (hN : ∀ k ∈ s, ∃ j ≤ N, x + k * P ≤ U j)
    (hfeedback : ∀ n < N, (∀ j ≤ n, U j < U (n + 1)) →
      ((U (n + 1) - U n : ℕ) : ℤ) = (a n - 1) * U n - L n)
    (hcover : ∀ n < N, ∀ k ∈ s, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L n ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u) :
    ∑ k ∈ s, f (x + k * P) ≤
      ∑ n ∈ Finset.range N,
        if (∀ j ≤ n, U j < U (n + 1)) then
          ((U (n + 1) - U n - B : ℕ) : ℝ) * f (U n) else 0 := by
  classical
  rw [sum_firstCrossing_partition s U (fun k => x + k * P) N
    (fun k => f (x + k * P)) hzero hN]
  apply Finset.sum_le_sum
  intro n hn
  have hnN := Finset.mem_range.mp hn
  by_cases hr : ∀ j ≤ n, U j < U (n + 1)
  · rw [if_pos hr]
    let crossed := s.filter (fun k => FirstCrossing U (x + k * P) n)
    have hlocal := crossed_progression_weighted_charge crossed x P (U n)
      (U (n + 1) - U n) B (a n) (L n) hP
      (by
        intro k hk
        have hcross := (Finset.mem_filter.mp hk).2
        exact hcross.1 n (Nat.le_refl n))
      (by
        intro k hk
        have hcross := (Finset.mem_filter.mp hk).2.2
        have hrise := hr n (Nat.le_refl n)
        omega)
      (hfeedback n hnN hr)
      (by
        intro k hk
        exact hcover n hnN k (Finset.mem_filter.mp hk).1)
      f hf (hpos (U n))
    simpa only [crossed, Finset.sum_filter] using hlocal
  · rw [if_neg hr]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k hk
    exact if_neg (fun h => hr h.is_record)

/-- The finite discrete record bound from explicit pairwise-coprime old
moduli. The CRT phase, coverings, first-crossing partition, and weighted
charges are all constructed in the proof. -/
theorem finite_record_bound_of_old_coprime_moduli
    (B N : ℕ) (m : Fin B → ℕ) (U : ℕ → ℕ) (a L : ℕ → ℤ)
    (hm : ∀ i, B < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (hmOld : ∀ n < N, ∀ i, (m i : ℤ) ∣ L n)
    (hfeedback : ∀ n < N, (∀ j ≤ n, U j < U (n + 1)) →
      ((U (n + 1) - U n : ℕ) : ℤ) = (a n - 1) * U n - L n)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u) :
    ∃ x, (∏ i, m i) ≤ x ∧ x < 2 * ∏ i, m i ∧
      ∀ s : Finset ℕ,
        (∀ k ∈ s, U 0 < x + B + k * (∏ i, m i)) →
        (∀ k ∈ s, ∃ j ≤ N, x + B + k * (∏ i, m i) ≤ U j) →
        ∑ k ∈ s, f (x + B + k * (∏ i, m i)) ≤
          ∑ n ∈ Finset.range N,
            if (∀ j ≤ n, U j < U (n + 1)) then
              ((U (n + 1) - U n - B : ℕ) : ℝ) * f (U n) else 0 := by
  classical
  obtain ⟨x, hBP, hxlo, hxhi, hcover⟩ := exists_crt_covering_progression m hm hpair
  refine ⟨x, hxlo, hxhi, ?_⟩
  intro s hzero hN
  exact finite_record_weighted_bound s U a L (x + B) (∏ i, m i) B N hBP
    hzero hN hfeedback
    (fun n hn k _hk => hcover (L n) (hmOld n hn) k) f hf hpos

end ErdosProblems.Erdos243.LcmRecordCrossing
