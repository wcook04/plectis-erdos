import ErdosProblems.Erdos243.PaperCompleteR8.WeightedRecords
import ErdosProblems.Erdos243.PaperCompleteR7.LcmDefect
import ErdosProblems.Erdos243.PaperCompleteR7.Arithmetic

/-!
# The canonical weighted-record equivalence

Complete uncompiled candidates for both occurrences of `res:weightedrecord`.
The rational value is supplied as `HasSum ... (p/q)`, exactly as in the
repaired r7 canonical-state theorem. All tail integrality and small-error
facts come from that theorem; none are additional hypotheses here.

The eventual-centred arithmetic theorem is obtained by shifting at a genuine
running maximum. Shifting at an arbitrary index would change the record set.
The converse implication uses the exact squared-error transport on a
Sylvester tail, rather than presuming zero error from the recurrence.

Mathlib facts used for casts and products also occur in the repaired r7
`LcmDefect.lean`: Int.natAbs_mul, Int.natAbs_natCast,
Nat.mul_lt_mul_left. All substantial arithmetic imports are supplied sources.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR8

open Filter Classical
open scoped BigOperators

/-- The full record theorem with the paper's eventual centring. No record
supply or global excess bound is assumed. -/
theorem arithmetic_weighted_record_eventually_centred
    (o : LcmOrbit)
    (hc : ∃ N, ∀ n, N ≤ n → -(o.U n : ℤ) ≤ 2 * o.V n)
    (B : ℕ) (f : ℕ → ℝ) (hf : Antitone f)
    (hpos : ∀ n, 0 ≤ f n) (hdiv : ¬ Summable f) :
    HeightBounded o.U ↔ Summable (rawRecordWeight o.U o.V B f) := by
  constructor
  · intro hb
    apply summable_of_eventually_zero_nonneg _ (rawRecordWeight_nonneg _ _ _ _ hpos)
    obtain ⟨T, hT⟩ := bounded_eventually_no_record o.U hb
    refine ⟨T, fun n hn => ?_⟩
    exact if_neg (hT n hn)
  · intro hs
    by_contra hb
    have hu := (not_bounded_iff_unbounded o.U).mp hb
    obtain ⟨N, hN⟩ := hc
    obtain ⟨r, hNr, hr⟩ := cofinal_records o.U hu N
    let T := r + 1
    have hTmax : ∀ j, j ≤ T → o.U j ≤ o.U T := by
      intro j hj
      by_cases heq : j = T
      · rw [heq]
      · exact (hr j (by dsimp [T] at *; omega)).le
    have hct : ∀ n, -((o.shift T).U n : ℤ) ≤ 2 * (o.shift T).V n := by
      intro n
      exact hN (T + n) (by dsimp [T]; omega)
    have heq : rawRecordWeight (o.shift T).U (o.shift T).V B f =
        fun n => rawRecordWeight o.U o.V B f (T + n) := by
      funext n
      change (if Record (fun k => o.U (T + k)) n then
        (((-o.V (T + n) - B).toNat : ℕ) : ℝ) * f (o.U (T + n)) else 0) = _
      rw [record_shift_iff o.U T n hTmax]
      rfl
    have ht : Summable (rawRecordWeight (o.shift T).U (o.shift T).V B f) := by
      rw [heq]
      exact (summable_shift_iff _ T).mpr hs
    exact unbounded_record_charge_not_summable (o.shift T) hct
      (shift_unbounded o.U hu T) B f hf hpos hdiv ht

/-- On an exact Sylvester tail the error is multiplied by a squared digit.
This is the missing converse transport in a state-level equivalence. -/
theorem error_square_transport_of_sylvester
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hS : (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    E (n + 1) = (a n : ℤ) ^ 2 * E n := by
  have hh := sylvesterDefect_mul_nextTailState
    (a n : ℤ) (a (n + 1) : ℤ) (D n : ℤ) (C n : ℤ)
  rw [← natTail_eq_nextTailState a C D hC n,
    ← natDen_eq_nextDenState a D hD n, ← hE n, ← hE (n + 1)] at hh
  have hd : sylvesterDefect (a n : ℤ) (a (n + 1) : ℤ) = 0 := by
    unfold sylvesterDefect
    rw [hS]
    exact sub_self _
  rw [hd, zero_mul] at hh
  omega

/-- Normalised vanishing rules out a nonzero error on a Sylvester tail.
The argument is purely integer arithmetic, with no tail-limit assumption. -/
theorem eventual_zero_of_sylvester_and_normalized
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 0 < a n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hv : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hS : ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨N, ?_⟩
  intro n hNn
  by_contra hne
  have habspos : 1 ≤ Int.natAbs (E n) := by
    have hnabs : Int.natAbs (E n) ≠ 0 := by
      intro hz
      exact hne (Int.natAbs_eq_zero.mp hz)
    omega
  have htransport : ∀ t, n ≤ t →
      Int.natAbs (E (t + 1)) = (a t) ^ 2 * Int.natAbs (E t) := by
    intro t hnt
    have he := error_square_transport_of_sylvester a C D E hC hD hE t
      (hN t (hNn.trans hnt))
    have hcast : (a t : ℤ) ^ 2 = ((a t ^ 2 : ℕ) : ℤ) := by norm_cast
    rw [he, hcast, Int.natAbs_mul, Int.natAbs_natCast]
  have hbound : ∀ t, n ≤ t → C t ≤ C n * Int.natAbs (E t) := by
    intro t hnt
    induction t, hnt using Nat.le_induction with
    | base => nlinarith [habspos]
    | succ t hnt ih =>
        have hCstep : C (t + 1) ≤ a t * C t := by
          have hh := hC t
          omega
        have ha1 : 1 ≤ a t := ha t
        have hasq : a t ≤ a t ^ 2 := by nlinarith
        have hscaled := Nat.mul_le_mul_right (C t) hasq
        have hscaled' := Nat.mul_le_mul_left (a t ^ 2) ih
        rw [htransport t hnt]
        calc
          C (t + 1) ≤ a t * C t := hCstep
          _ ≤ a t ^ 2 * C t := hscaled
          _ ≤ a t ^ 2 * (C n * Int.natAbs (E t)) := hscaled'
          _ = C n * (a t ^ 2 * Int.natAbs (E t)) := by ring
  obtain ⟨T, hT⟩ := hv (C n)
  have hh := hT (max T n) (le_max_left _ _)
  have hb := hbound (max T n) (le_max_right _ _)
  omega

/-- The exact canonical LCM state. Its data are definitions; its validity
proof reuses r7's compiled denominator-clearing theorem. -/
noncomputable def canonicalLcmOrbit
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (nhds 1)) :
    LcmOrbit := by
  let C := PaperCompleteR7.canonicalNaturalNumerator a p q
  let D := PaperCompleteR7.canonicalDenominator a q
  refine {
    a := a
    L := cumulativeDigitLcm q a
    U := lcmLiftedNumerator q a C
    V := lcmLiftedDigit q a C
    apos := hapos
    Lpos := cumulativeDigitLcm_pos hq hapos
    Upos := ?_
    nextL := fun _ => rfl
    step := ?_
    digit := fun _ => rfl
  }
  · obtain ⟨hCp, _, hC, _, _, _, _⟩ :=
      PaperCompleteR7.canonical_integer_tail_normalized a ha hapos p q hq hs hg
    have hscale : ∀ n, D n = digitProductScale q a n :=
      fun n => (PaperCompleteR7.productScale_eq_canonicalDenominator q a n).symm
    intro n
    have heq := lcmLiftedNumerator_spec q a C D hscale hC n
    by_contra hn
    have hz : lcmLiftedNumerator q a C n = 0 := by omega
    rw [hz, mul_zero] at heq
    exact (hCp n).ne' heq.symm
  · obtain ⟨_, _, hC, _, _, _, _⟩ :=
      PaperCompleteR7.canonical_integer_tail_normalized a ha hapos p q hq hs hg
    have hscale : ∀ n, D n = digitProductScale q a n :=
      fun n => (PaperCompleteR7.productScale_eq_canonicalDenominator q a n).symm
    exact lcmLifted_step C D hq hapos hscale hC

/-- Normalised vanishing transports through the actual integer LCM quotient.
Cancellation occurs only after the overlap factor has been shown positive. -/
theorem canonicalLcmOrbit_normalized
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (nhds 1)) :
    let o := canonicalLcmOrbit a ha hapos p q hq hs hg
    ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (o.V n) < o.U n := by
  let C := PaperCompleteR7.canonicalNaturalNumerator a p q
  let D := PaperCompleteR7.canonicalDenominator a q
  obtain ⟨_, _, hC, _, _, hv, _⟩ :=
    PaperCompleteR7.canonical_integer_tail_normalized a ha hapos p q hq hs hg
  have hscale : ∀ n, D n = digitProductScale q a n :=
    fun n => (PaperCompleteR7.productScale_eq_canonicalDenominator q a n).symm
  dsimp only
  intro K
  obtain ⟨N, hN⟩ := hv K
  refine ⟨N, ?_⟩
  intro n hn
  have hM := cumulativeOverlapDebt_pos hq hapos n
  have hUeq := lcmLiftedNumerator_spec q a C D hscale hC n
  have hVeq := lcmLiftedDigit_mul_overlapDebt q a C D hscale hC n
  have hh := hN n hn
  change K * Int.natAbs (centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) < C n at hh
  rw [← hVeq, ← hUeq, Int.natAbs_mul, Int.natAbs_natCast] at hh
  change K * Int.natAbs (lcmLiftedDigit q a C n) < lcmLiftedNumerator q a C n
  apply (Nat.mul_lt_mul_left hM).mp
  calc
    cumulativeOverlapDebt q a n * (K * Int.natAbs (lcmLiftedDigit q a C n)) =
      K * (cumulativeOverlapDebt q a n * Int.natAbs (lcmLiftedDigit q a C n)) := by ring
    _ < cumulativeOverlapDebt q a n * lcmLiftedNumerator q a C n := hh

/-- Both short- and long-note `res:weightedrecord`, in the natural-weight
vocabulary that is independently transported from the improper integral. -/
theorem canonical_weighted_record_nat
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (nhds 1))
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ n, 0 ≤ f n) (hdiv : ¬ Summable f) :
    let o := canonicalLcmOrbit a ha hapos p q hq hs hg
    (∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) ↔
      ∃ B : ℕ, Summable (rawRecordWeight o.U o.V B f) := by
  let o := canonicalLcmOrbit a ha hapos p q hq hs hg
  let C := PaperCompleteR7.canonicalNaturalNumerator a p q
  let D := PaperCompleteR7.canonicalDenominator a q
  let E := fun n => centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  obtain ⟨hCp, _hDp, hC, hD, _hrep, hv, _hc⟩ :=
    PaperCompleteR7.canonical_integer_tail_normalized a ha hapos p q hq hs hg
  have hscale : ∀ n, D n = digitProductScale q a n :=
    fun n => (PaperCompleteR7.productScale_eq_canonicalDenominator q a n).symm
  have hVeq : ∀ n, (cumulativeOverlapDebt q a n : ℤ) * o.V n = E n :=
    lcmLiftedDigit_mul_overlapDebt q a C D hscale hC
  have hVo := canonicalLcmOrbit_normalized a ha hapos p q hq hs hg
  have hcent : ∃ N, ∀ n, N ≤ n → -(o.U n : ℤ) ≤ 2 * o.V n := by
    obtain ⟨N, hN⟩ := hVo 2
    refine ⟨N, ?_⟩
    intro n hn
    have hb : (2 : ℤ) * Int.natAbs (o.V n) < o.U n := by
      exact_mod_cast hN n hn
    have hl := (integer_abs_bounds (o.V n)).1
    omega
  constructor
  · intro hS
    have hz := eventual_zero_of_sylvester_and_normalized a C D E hapos hC hD
      (fun _ => rfl) hv hS
    obtain ⟨N, hN⟩ := hz
    refine ⟨0, summable_of_eventually_zero_nonneg _
      (rawRecordWeight_nonneg _ _ _ _ hpos) ⟨N, ?_⟩⟩
    intro n hn
    have hM : (cumulativeOverlapDebt q a n : ℤ) ≠ 0 := by
      exact_mod_cast (cumulativeOverlapDebt_pos hq hapos n).ne'
    have hzero : o.V n = 0 := by
      have hh := hVeq n
      rw [hN n hn] at hh
      exact (mul_eq_zero.mp hh).resolve_left hM
    unfold rawRecordWeight
    rw [hzero]
    simp only [neg_zero, Nat.cast_zero, sub_zero, Int.toNat_zero,
      Nat.cast_zero, zero_mul, ite_self]
  · rintro ⟨B, hB⟩
    have hbound := (arithmetic_weighted_record_eventually_centred o hcent B f hf hpos hdiv).mpr hB
    obtain ⟨N, hN⟩ := PaperCompleteR7.zero_digit_of_bounded_height o.U o.V hbound hVo
    have hzero : ∃ N, ∀ n, N ≤ n → E n = 0 := by
      refine ⟨N, fun n hn => ?_⟩
      rw [← hVeq n, hN n hn, mul_zero]
    exact PaperCompleteR7.natural_sylvester_of_eventual_zero a C D E hCp hC hD
      (fun _ => rfl) hzero

/-- Paper-facing real-weight theorem, with no sampled-weight premise. -/
theorem canonical_weighted_record
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (nhds 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : DivergentIntegral f) :
    let o := canonicalLcmOrbit a ha hapos p q hq hs hg
    (∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) ↔
      ∃ B : ℕ, Summable (fun n : ℕ => if Record o.U n then
        (((-o.V n - B).toNat : ℕ) : ℝ) * f (o.U n) else 0) := by
  let o := canonicalLcmOrbit a ha hapos p q hq hs hg
  have hh := canonical_weighted_record_nat a ha hapos p q hq hs hg
    (heightWeight f) (heightWeight_antitone f hf) (heightWeight_nonneg f hpos)
    (not_summable_heightWeight f hf hpos hdiv)
  have heq : ∀ B : ℕ, rawRecordWeight o.U o.V B (heightWeight f) =
      fun n : ℕ => if Record o.U n then
        (((-o.V n - B).toNat : ℕ) : ℝ) * f (o.U n) else 0 := by
    intro B
    funext n
    unfold rawRecordWeight
    rw [heightWeight_eq f (o.U n) (o.Upos n)]
  change (∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) ↔
    ∃ B : ℕ, Summable (rawRecordWeight o.U o.V B (heightWeight f)) at hh
  simpa only [heq] using hh

end ErdosProblems.Erdos243.PaperCompleteR8
