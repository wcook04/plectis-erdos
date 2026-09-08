import ErdosProblems.Erdos243.PaperCompleteR8.WeightAnalysis
import ErdosProblems.Erdos243.LcmRecordDivergence
import ErdosProblems.Erdos243.PrimitiveRecordBarrier

/-!
# Global arithmetic weighted-record theorem

Round 8: complete candidate for long-record `res:arithmeticrecord`.
The finite crossing and CRT lemmas are reused. The proof below supplies the
old large coprime moduli from the *actual record indices*. No supply, global
budget, rate, or normalised-vanishing premise is added.

The natural-weight theorem uses nonsummability. The final theorem derives
that premise from the paper's improper integral through `WeightAnalysis`.
All declarations in this file are uncompiled candidates.

Pinned Mathlib references used below:
* Data/Nat/GCD/Basic.lean: Nat.Coprime.of_dvd_left, Nat.lcm_dvd.
  Nat.dvd_lcm_left/right and Nat.dvd_gcd are imported Nat/Batteries facts.
* Algebra/Order/BigOperators/Group/Finset.lean: Finset.single_le_sum.
* Topology/Algebra/InfiniteSum/Group.lean: Summable.comp_injective,
  Summable.congr.
Other substantial calls are to the supplied, repaired corpus, not guessed APIs.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR8

open Filter Classical
open scoped BigOperators

/-- Bundles exactly the integer arithmetic in the displayed theorem.
The centring bound is separate so its eventual version can be used later. -/
structure LcmOrbit where
  a : ℕ → ℕ
  L : ℕ → ℕ
  U : ℕ → ℕ
  V : ℕ → ℤ
  apos : ∀ n, 0 < a n
  Lpos : ∀ n, 0 < L n
  Upos : ∀ n, 0 < U n
  nextL : ∀ n, L (n + 1) = Nat.lcm (L n) (a n)
  step : ∀ n, (Nat.gcd (L n) (a n) : ℤ) * (U (n + 1) : ℤ) = (U n : ℤ) - V n
  digit : ∀ n, V n = (L n : ℤ) - ((a n : ℤ) - 1) * (U n : ℤ)

def Record (U : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j ≤ n, U j < U (n + 1)

noncomputable def rawRecordWeight (U : ℕ → ℕ) (V : ℕ → ℤ)
    (B : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if Record U n then (((-V n - B).toNat : ℕ) : ℝ) * f (U n) else 0

def HeightBounded (U : ℕ → ℕ) : Prop := ∃ H : ℕ, ∀ n, U n ≤ H

def HeightUnbounded (U : ℕ → ℕ) : Prop := ∀ H : ℕ, ∃ n, H < U n

/-- Classical negation of an integer upper bound, explicitly transported. -/
theorem not_bounded_iff_unbounded (U : ℕ → ℕ) :
    ¬ HeightBounded U ↔ HeightUnbounded U := by
  constructor
  · intro h H
    by_contra hn
    apply h
    refine ⟨H, ?_⟩
    intro n
    by_contra hh
    exact hn ⟨n, by omega⟩
  · intro h ⟨H, hH⟩
    obtain ⟨n, hn⟩ := h H
    exact (not_lt_of_ge (hH n)) hn

/-- Every sufficiently high first crossing is a genuine running record. -/
theorem cofinal_records (U : ℕ → ℕ) (hu : HeightUnbounded U) (T : ℕ) :
    ∃ n, T ≤ n ∧ Record U n := by
  let z := runningMax U T + 1
  obtain ⟨K, hK⟩ := hu z
  have hzero : U 0 < z := by
    have h := le_runningMax U (Nat.zero_le T)
    dsimp [z]
    omega
  obtain ⟨n, hn, _⟩ := LcmRecordCrossing.exists_unique_firstCrossing
    U z K hzero ⟨K, le_rfl, hK.le⟩
  have hfirst := hn.2
  have hTn : T ≤ n := by
    by_contra hh
    have hle := le_runningMax U (show n + 1 ≤ T by omega)
    have hz := hfirst.2
    dsimp [z] at hz
    omega
  refine ⟨n, hTn, ?_⟩
  intro j hj
  exact (hfirst.1 j hj).trans_le hfirst.2

namespace LcmOrbit

theorem L_dvd_of_le (o : LcmOrbit) {s t : ℕ} (hst : s ≤ t) : o.L s ∣ o.L t := by
  induction t, hst using Nat.le_induction with
  | base => exact dvd_rfl
  | succ t _ ih =>
      rw [o.nextL t]
      exact ih.trans (Nat.dvd_lcm_left _ _)

theorem old_digit_dvd (o : LcmOrbit) {s t : ℕ} (hst : s < t) : o.a s ∣ o.L t := by
  have hd : o.a s ∣ o.L (s + 1) := by
    rw [o.nextL s]
    exact Nat.dvd_lcm_right _ _
  exact hd.trans (o.L_dvd_of_le (by omega))

theorem record_fresh (o : LcmOrbit)
    (hc : ∀ n, -(o.U n : ℤ) ≤ 2 * o.V n)
    {n : ℕ} (hn : Record o.U n) : Nat.gcd (o.L n) (o.a n) = 1 := by
  have hrho : 1 ≤ (Nat.gcd (o.L n) (o.a n) : ℤ) := by
    have hnat : (1 : ℕ) ≤ Nat.gcd (o.L n) (o.a n) :=
      Nat.succ_le_iff.mpr (Nat.gcd_pos_of_pos_left (o.a n) (o.Lpos n))
    exact_mod_cast hnat
  have hs := LcmRecordExcess.rise_is_fresh
    (by exact_mod_cast o.Upos n) hrho (hc n) (o.step n)
    (by exact_mod_cast hn n le_rfl)
  exact_mod_cast hs.1

theorem record_digit_gt_one (o : LcmOrbit)
    (hc : ∀ n, -(o.U n : ℤ) ≤ 2 * o.V n)
    {n : ℕ} (hn : Record o.U n) : 1 < o.a n := by
  have hs := o.step n
  rw [o.record_fresh hc hn, Nat.cast_one, one_mul, o.digit n] at hs
  have hr : (o.U n : ℤ) < o.U (n + 1) := by exact_mod_cast hn n le_rfl
  have hL : (0 : ℤ) < o.L n := by exact_mod_cast o.Lpos n
  by_contra ha
  have hsmall : (o.a n : ℤ) ≤ 1 := by exact_mod_cast (show o.a n ≤ 1 by omega)
  have hU : (0 : ℤ) ≤ o.U n := by positivity
  have hm := mul_le_mul_of_nonneg_right hsmall hU
  nlinarith [hs]

theorem record_digits_coprime (o : LcmOrbit)
    (hc : ∀ n, -(o.U n : ℤ) ≤ 2 * o.V n)
    {s t : ℕ} (hs : Record o.U s) (ht : Record o.U t) (hst : s < t) :
    Nat.Coprime (o.a s) (o.a t) := by
  have hcop : Nat.Coprime (o.L t) (o.a t) := o.record_fresh hc ht
  -- Mathlib/Data/Nat/GCD/Basic.lean.
  exact hcop.of_dvd_left (o.old_digit_dvd hst)

/-- The finite list of small digits can be exhausted. This is where the
proof obtains large moduli without assuming that the entire digit sequence
is increasing, or using a prime-distribution hypothesis. -/
theorem cofinal_large_records (o : LcmOrbit)
    (hc : ∀ n, -(o.U n : ℤ) ≤ 2 * o.V n)
    (hu : HeightUnbounded o.U) (B T : ℕ) :
    ∃ n, T ≤ n ∧ Record o.U n ∧ B < o.a n := by
  classical
  let old : Fin (B + 1) → ℕ := fun i =>
    if hi : ∃ n, Record o.U n ∧ o.a n = i.val then Nat.find hi else 0
  let cutoff := T + (∑ i : Fin (B + 1), old i) + 1
  obtain ⟨n, hcut, hn⟩ := cofinal_records o.U hu cutoff
  refine ⟨n, by dsimp [cutoff] at hcut; omega, hn, ?_⟩
  by_contra hlarge
  have han : o.a n ≤ B := by omega
  let i : Fin (B + 1) := ⟨o.a n, by omega⟩
  have hex : ∃ k, Record o.U k ∧ o.a k = i.val := ⟨n, hn, rfl⟩
  have hold : old i = Nat.find hex := by simp only [old, dif_pos hex]
  have hspec : Record o.U (old i) ∧ o.a (old i) = o.a n := by
    rw [hold]
    exact Nat.find_spec hex
  have hsum : old i ≤ ∑ j : Fin (B + 1), old j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hbefore : old i < n := by dsimp [cutoff] at hcut; omega
  have hd : o.a n ∣ o.L n := by
    rw [← hspec.2]
    exact o.old_digit_dvd hbefore
  have hdone : o.a n ∣ 1 := by
    have hgg := Nat.dvd_gcd hd (dvd_refl (o.a n))
    rwa [o.record_fresh hc hn] at hgg
  have hsmall := Nat.le_of_dvd Nat.one_pos hdone
  have hgt := o.record_digit_gt_one hc hn
  omega

/-- Shift keeps the exact data, not merely their inequalities. -/
def shift (o : LcmOrbit) (T : ℕ) : LcmOrbit where
  a n := o.a (T + n)
  L n := o.L (T + n)
  U n := o.U (T + n)
  V n := o.V (T + n)
  apos n := o.apos (T + n)
  Lpos n := o.Lpos (T + n)
  Upos n := o.Upos (T + n)
  nextL n := by simpa only [Nat.add_assoc] using o.nextL (T + n)
  step n := by simpa only [Nat.add_assoc] using o.step (T + n)
  digit n := o.digit (T + n)

end LcmOrbit

/-- Start a shifted orbit at an attained running maximum. Then shifted
records are exactly the original records, not a spurious new record set. -/
theorem record_shift_iff
    (U : ℕ → ℕ) (T n : ℕ) (hT : ∀ j, j ≤ T → U j ≤ U T) :
    Record (fun k => U (T + k)) n ↔ Record U (T + n) := by
  constructor
  · intro hr j hj
    by_cases hbefore : j ≤ T
    · have h0 := hr 0 (Nat.zero_le n)
      simp only [Nat.add_zero] at h0
      exact (hT j hbefore).trans_lt (by simpa only [Nat.add_assoc] using h0)
    · have hTj : T ≤ j := by omega
      have hidx : j - T ≤ n := by omega
      have hh := hr (j - T) hidx
      dsimp only at hh
      rw [Nat.add_sub_of_le hTj] at hh
      simpa only [Nat.add_assoc] using hh
  · intro hr k hk
    have hh := hr (T + k) (by omega)
    simpa only [Nat.add_assoc] using hh

theorem shift_unbounded
    (U : ℕ → ℕ) (hu : HeightUnbounded U) (T : ℕ) :
    HeightUnbounded (fun k => U (T + k)) := by
  intro H
  obtain ⟨n, hn⟩ := hu (max H (runningMax U T))
  have hTn : T ≤ n := by
    by_contra hnot
    have hle := le_runningMax U (show n ≤ T by omega)
    have hhi := le_max_right H (runningMax U T)
    omega
  refine ⟨n - T, ?_⟩
  dsimp only
  rw [Nat.add_sub_of_le hTn]
  exact (le_max_left _ _).trans_lt hn

/-- Bounded integer height has an attained maximum and finitely many records. -/
theorem bounded_eventually_no_record (U : ℕ → ℕ) (hb : HeightBounded U) :
    ∃ N, ∀ n, N ≤ n → ¬ Record U n := by
  classical
  let H := Nat.find hb
  have hH : ∀ n, U n ≤ H := Nat.find_spec hb
  have hhit : ∃ t, U t = H := by
    by_contra hn
    by_cases hzero : H = 0
    · exact hn ⟨0, by have := hH 0; omega⟩
    · have hsmall : ∀ n, U n ≤ H - 1 := by
        intro n
        have hle := hH n
        have hne : U n ≠ H := fun he => hn ⟨n, he⟩
        omega
      exact Nat.find_min hb (show H - 1 < Nat.find hb by dsimp [H] at *; omega) hsmall
  obtain ⟨t, ht⟩ := hhit
  refine ⟨t, ?_⟩
  intro n htn hr
  have hlt := hr t htn
  have hle := hH (n + 1)
  rw [ht] at hlt
  omega

theorem rawRecordWeight_nonneg
    (U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (n : ℕ) : 0 ≤ rawRecordWeight U V B f n := by
  unfold rawRecordWeight
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (hf _)
  · exact le_rfl

/-- Actual and raw record charges coincide under the lower centring bound. -/
theorem rawRecordWeight_eq_actual
    (o : LcmOrbit) (hc : ∀ n, -(o.U n : ℤ) ≤ 2 * o.V n)
    (B : ℕ) (f : ℕ → ℝ) :
    rawRecordWeight o.U o.V B f =
      LcmRecordCrossing.recordExcessWeight o.U B f := by
  funext n
  classical
  unfold rawRecordWeight LcmRecordCrossing.recordExcessWeight Record
  split_ifs with hr
  · have hs := o.step n
    rw [o.record_fresh hc hr, Nat.cast_one, one_mul] at hs
    have hn := hr n le_rfl
    have heq : (-o.V n - (B : ℤ)).toNat = o.U (n + 1) - o.U n - B := by omega
    rw [heq]
  · rfl

/-- Full global construction and charge: an unbounded centred LCM orbit
has nonsummable record excess for every decreasing divergent weight. -/
theorem unbounded_record_charge_not_summable
    (o : LcmOrbit) (hc : ∀ n, -(o.U n : ℤ) ≤ 2 * o.V n)
    (hu : HeightUnbounded o.U)
    (B : ℕ) (f : ℕ → ℝ) (hf : Antitone f)
    (hpos : ∀ n, 0 ≤ f n) (hdiv : ¬ Summable f) :
    ¬ Summable (rawRecordWeight o.U o.V B f) := by
  classical
  intro hsum
  let pick : ℕ → ℕ := fun T => Classical.choose (o.cofinal_large_records hc hu B T)
  have hpick : ∀ T, T ≤ pick T ∧ Record o.U (pick T) ∧ B < o.a (pick T) :=
    fun T => Classical.choose_spec (o.cofinal_large_records hc hu B T)
  let s : ℕ → ℕ := Nat.rec (pick 0) (fun _ prev => pick (prev + 1))
  have hs0 : s 0 = pick 0 := rfl
  have hss : ∀ i, s (i + 1) = pick (s i + 1) := fun _ => rfl
  have hsmono : StrictMono s := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hss]
    have hh := (hpick (s i + 1)).1
    omega
  have hsdata : ∀ i, Record o.U (s i) ∧ B < o.a (s i) := by
    intro i
    cases i with
    | zero => exact (hpick 0).2
    | succ i => exact (hpick (s i + 1)).2
  let m : Fin B → ℕ := fun i => o.a (s i.val)
  have hm : ∀ i, B < m i := fun i => (hsdata i.val).2
  have hpair : ∀ i j : Fin B, i ≠ j → Nat.Coprime (m i) (m j) := by
    intro i j hij
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hij' with hlt | hgt
    · exact o.record_digits_coprime hc (hsdata i.val).1 (hsdata j.val).1 (hsmono hlt)
    · exact (o.record_digits_coprime hc (hsdata j.val).1 (hsdata i.val).1 (hsmono hgt)).symm
  let T := s B + 1
  have hTmax : ∀ j, j ≤ T → o.U j ≤ o.U T := by
    intro j hj
    by_cases heq : j = T
    · rw [heq]
    · exact ((hsdata B).1 j (by dsimp [T] at *; omega)).le
  have hmold : ∀ n, ∀ i : Fin B, m i ∣ o.L (T + n) := by
    intro n i
    apply o.old_digit_dvd
    have hi := hsmono i.isLt
    dsimp [T]
    omega
  obtain ⟨x, hBP, hxP, _hxhi, hcover⟩ :=
    LcmRecordCrossing.exists_crt_covering_progression m hm hpair
  let P : ℕ := ∏ i, m i
  let k0 := o.U T + 1
  let x0 := x + B + k0 * P
  have hP : 0 < P := by dsimp [P]; omega
  have hstart : o.U T < x0 := by
    have hk : k0 ≤ k0 * P := by nlinarith
    dsimp [x0, k0] at *
    omega
  have hweightshift : rawRecordWeight (fun n => o.U (T + n))
      (fun n => o.V (T + n)) B f = fun n => rawRecordWeight o.U o.V B f (T + n) := by
    funext n
    unfold rawRecordWeight
    rw [record_shift_iff o.U T n hTmax]
  have htail : Summable (rawRecordWeight (o.shift T).U (o.shift T).V B f) := by
    change Summable (rawRecordWeight (fun n => o.U (T + n))
      (fun n => o.V (T + n)) B f)
    rw [hweightshift]
    exact (summable_shift_iff _ T).mpr hsum
  have hctail : ∀ n, -((o.shift T).U n : ℤ) ≤ 2 * (o.shift T).V n :=
    fun n => hc (T + n)
  rw [rawRecordWeight_eq_actual (o.shift T) hctail B f] at htail
  apply LcmRecordCrossing.not_summable_recordExcessWeight_of_progression
    (fun n => o.U (T + n)) (fun n => (o.a (T + n) : ℤ))
    (fun n => (o.L (T + n) : ℤ)) x0 P B hBP
    (by simpa only [Nat.add_zero] using hstart)
    (fun H => by
      obtain ⟨n, hn⟩ := shift_unbounded o.U hu T H
      exact ⟨n, hn.le⟩)
    ?_ ?_ f hf hpos (progression_not_summable f hf hpos hdiv x0 P hP) htail
  · intro n hr
    have hrecord := (record_shift_iff o.U T n hTmax).mp hr
    have hs := o.step (T + n)
    rw [o.record_fresh hc hrecord, Nat.cast_one, one_mul, o.digit (T + n)] at hs
    have hle : o.U (T + n) ≤ o.U (T + n + 1) := (hrecord _ le_rfl).le
    have hcast : ((o.U (T + n + 1) - o.U (T + n) : ℕ) : ℤ) =
        (o.U (T + n + 1) : ℤ) - o.U (T + n) := Int.ofNat_sub hle
    simpa only [Nat.add_assoc] using (show
      ((o.U (T + n + 1) - o.U (T + n) : ℕ) : ℤ) =
        ((o.a (T + n) : ℤ) - 1) * o.U (T + n) - o.L (T + n) by
          rw [hcast]
          nlinarith [hs])
  · intro n k z hlo hhi
    have hwall : x0 + k * P = x + B + (k0 + k) * P := by dsimp [x0]; ring
    rw [hwall] at hlo hhi
    exact hcover (o.L (T + n)) (fun i => by exact_mod_cast hmold n i)
      (k0 + k) z hlo hhi

/-- The complete arithmetic dichotomy in natural-height vocabulary. -/
theorem arithmetic_weighted_record_nat
    (o : LcmOrbit) (hc : ∀ n, -(o.U n : ℤ) ≤ 2 * o.V n)
    (B : ℕ) (f : ℕ → ℝ) (hf : Antitone f)
    (hpos : ∀ n, 0 ≤ f n) (hdiv : ¬ Summable f) :
    HeightBounded o.U ↔ Summable (rawRecordWeight o.U o.V B f) := by
  constructor
  · intro hb
    apply summable_of_eventually_zero_nonneg _ (rawRecordWeight_nonneg _ _ _ _ hpos)
    obtain ⟨N, hN⟩ := bounded_eventually_no_record o.U hb
    refine ⟨N, fun n hn => ?_⟩
    exact if_neg (hN n hn)
  · intro hs
    by_contra hb
    exact unbounded_record_charge_not_summable o hc
      ((not_bounded_iff_unbounded o.U).mp hb) B f hf hpos hdiv hs

/-- Long-record `res:arithmeticrecord`, with exactly its improper-integral
hypothesis. The natural positive part is cast to the real summand. -/
theorem arithmetic_weighted_record
    (o : LcmOrbit) (hc : ∀ n, -(o.U n : ℤ) ≤ 2 * o.V n)
    (B : ℕ) (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : DivergentIntegral f) :
    HeightBounded o.U ↔
      Summable (fun n : ℕ => if Record o.U n then
        (((-o.V n - B).toNat : ℕ) : ℝ) * f (o.U n) else 0) := by
  have hh := arithmetic_weighted_record_nat o hc B (heightWeight f)
    (heightWeight_antitone f hf) (heightWeight_nonneg f hpos)
    (not_summable_heightWeight f hf hpos hdiv)
  have heq : rawRecordWeight o.U o.V B (heightWeight f) =
      fun n : ℕ => if Record o.U n then
        (((-o.V n - B).toNat : ℕ) : ℝ) * f (o.U n) else 0 := by
    funext n
    unfold rawRecordWeight
    rw [heightWeight_eq f (o.U n) (o.Upos n)]
  rwa [heq] at hh

end ErdosProblems.Erdos243.PaperCompleteR8
