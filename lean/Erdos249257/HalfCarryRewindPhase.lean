import Erdos249257.HalfCarrySelectedWindow

/-!
# Exact phase of a realized fixed-coefficient rewind

This module identifies the dyadic phase with the complementary binary
numeral of the realized terminal-carry-one suffix. It deliberately does not
assert that the required suffix inequality holds globally.
-/

namespace Erdos249257.FixedCoeffRewindPhase

open Erdos249257.FixedCoeffRewind
open Erdos249257.HalfCarryReachability
open Set

/-- Binary numeral in the same reverse-chronological order as `rewind`:
the newest row is the low bit and every older row is one place higher. -/
def suffixNumeral : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * suffixNumeral bs

/-- A Boolean suffix numeral fits in exactly the dyadic denominator
determined by its length. -/
theorem suffixNumeral_lt_two_pow_length (bits : List Bool) :
    suffixNumeral bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [suffixNumeral]
  | cons b bits ih =>
      cases b <;> simp [suffixNumeral, pow_succ] <;> omega

/-- Exact phase identity for a realized carry-one history.  The equation
`offset + suffix + 2 = denom * (ancestor + 1)` is the natural-number form
obtained by unrolling

`1 = denom * ancestor - coefficientNumeral - suffixNumeral`

and using `offset = coefficientNumeral + denom - 1`. -/
theorem phase_eq_denom_sub_one_sub_suffixNumeral
    (cs : List ℕ) (bits : List Bool) (ancestor : ℕ)
    (hlen : bits.length = cs.length)
    (hrealized :
      offset cs + suffixNumeral bits + 2 =
        denom cs * (ancestor + 1)) :
    phase cs = denom cs - 1 - suffixNumeral bits := by
  have hsuffix : suffixNumeral bits < denom cs := by
    rw [denom, ← hlen]
    exact suffixNumeral_lt_two_pow_length bits
  have hdecomp :
      1 + offset cs =
        denom cs * ancestor + (denom cs - 1 - suffixNumeral bits) := by
    rw [Nat.mul_add] at hrealized
    simp only [Nat.mul_one, Nat.add_assoc] at hrealized
    omega
  have hremainder :
      denom cs - 1 - suffixNumeral bits < denom cs := by
    have hD := denom_pos cs
    omega
  rw [phase, hdecomp]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hremainder]

/-- The exact fixed-coefficient singleton criterion in support-history
coordinates: the terminal interval `[1,B]` rewinds to one ancestor exactly
when the carry-one suffix numeral covers the other `B-1` targets. -/
theorem rewind_interval_singleton_iff_suffixNumeral_covers
    (cs : List ℕ) (bits : List Bool) (ancestor B : ℕ)
    (hlen : bits.length = cs.length)
    (hrealized :
      offset cs + suffixNumeral bits + 2 =
        denom cs * (ancestor + 1))
    (hB : 1 ≤ B) (hwidth : B ≤ denom cs) :
    (∀ k : ℕ, 1 ≤ k → k ≤ B → rewind cs k = rewind cs 1) ↔
      B - 1 ≤ suffixNumeral bits := by
  rw [rewind_interval_singleton_iff_phase_fit cs hB hwidth,
    phase_eq_denom_sub_one_sub_suffixNumeral cs bits ancestor hlen hrealized]
  have hsuffix : suffixNumeral bits < denom cs := by
    rw [denom, ← hlen]
    exact suffixNumeral_lt_two_pow_length bits
  omega

/-! ## Feedback-free support bridge -/

/-- The actual suffix bits in reverse chronological order. -/
def supportSuffixBits (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M : ℕ) : ℕ → List Bool
  | 0 => []
  | L + 1 => decide (M + L + 1 ∈ A) :: supportSuffixBits A M L

@[simp] theorem supportSuffixBits_length
    (A : Set ℕ) [DecidablePred (· ∈ A)] (M L : ℕ) :
    (supportSuffixBits A M L).length = L := by
  induction L with
  | zero => simp [supportSuffixBits]
  | succ L ih => simp [supportSuffixBits, ih]

/-- Recursive binary value of the support suffix. -/
def supportSuffixNumeral (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 =>
      2 * supportSuffixNumeral A M L +
        if M + L + 1 ∈ A then 1 else 0

theorem suffixNumeral_supportSuffixBits
    (A : Set ℕ) [DecidablePred (· ∈ A)] (M L : ℕ) :
    suffixNumeral (supportSuffixBits A M L) =
      supportSuffixNumeral A M L := by
  induction L with
  | zero => simp [supportSuffixBits, supportSuffixNumeral, suffixNumeral]
  | succ L ih =>
      simp only [supportSuffixBits, suffixNumeral, supportSuffixNumeral, ih]
      by_cases hmem : M + L + 1 ∈ A <;> simp [hmem, Nat.add_comm]

/-- Before the first possible feedback row, truncating at `M` removes from
row `n` only the current bit `n` itself. -/
theorem supportCoeff_eq_prefix_add_currentBit
    (A : Set ℕ) [DecidablePred (· ∈ A)]
    {M n : ℕ} (hMn : M < n)
    (hnfeedback : n ≤ 2 * M + 1) :
    supportCoeff A n = supportCoeff (A ∩ Set.Iic M) n +
      if n ∈ A then 1 else 0 := by
  classical
  let P : Set ℕ := A ∩ Set.Iic M
  have hnpos : 0 < n := by omega
  have hnP : n ∉ P := by
    intro hnPmem
    have hnle : n ≤ M := hnPmem.2
    omega
  have hlarge_divisor {d : ℕ} (hddiv : d ∈ n.divisors)
      (hdM : M < d) : d = n := by
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
    have hdle : d ≤ n := Nat.le_of_dvd hnpos hdvd
    by_contra hdne
    have hdlt : d < n := lt_of_le_of_ne hdle hdne
    obtain ⟨q, hq⟩ := hdvd
    have hqpos : 0 < q := by
      by_contra hq0
      have hqz : q = 0 := Nat.eq_zero_of_not_pos hq0
      subst q
      simp at hq
      omega
    have hq2 : 2 ≤ q := by
      by_contra hqnot
      have hq1 : q = 1 := by omega
      subst q
      have hnd : n = d := by simpa using hq
      exact hdne hnd.symm
    have htwod : 2 * d ≤ n := by
      rw [hq]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left d hq2
    omega
  have hcoeff : supportCoeff A n =
      supportCoeff (if n ∈ A then insert n P else P) n := by
    rw [supportCoeff_eq_card_filter, supportCoeff_eq_card_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      refine ⟨hddiv, ?_⟩
      by_cases hdM : d ≤ M
      · by_cases hnA : n ∈ A <;> simp [hnA, P, hdA, hdM]
      · have hdn : d = n := hlarge_divisor hddiv (by omega)
        subst d
        simp [hdA]
    · rintro ⟨hddiv, hdmem⟩
      refine ⟨hddiv, ?_⟩
      by_cases hnA : n ∈ A
      · simp only [if_pos hnA, Set.mem_insert_iff] at hdmem
        rcases hdmem with (rfl | hdP)
        · assumption
        · exact hdP.1
      · simp only [if_neg hnA] at hdmem
        exact hdmem.1
  rw [hcoeff]
  split_ifs with hnA
  · exact Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_self
      P hnpos hnP
  · rfl

/-- On a horizon `M+L ≤ 2M+1`, the prefix-zero-extension carry exceeds the
actual carry by exactly the binary numeral of the removed suffix. -/
theorem integerHalfCarry_prefix_eq_add_supportSuffixNumeral
    (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M L : ℕ) (hM : 1 ≤ M)
    (hhorizon : M + L ≤ 2 * M + 1) :
    integerHalfCarry (A ∩ Set.Iic M) (M + L - 1) =
      integerHalfCarry A (M + L - 1) +
        (supportSuffixNumeral A M L : ℤ) := by
  induction L with
  | zero =>
      simpa using integerHalfCarry_inter_Iic_eq_of_succ_le
        A M (M - 1) (by omega)
  | succ L ih =>
      have hprev : M + L ≤ 2 * M + 1 := by omega
      have hih := ih hprev
      have hcoeff := supportCoeff_eq_prefix_add_currentBit A
        (show M < M + L + 1 by omega)
        (show M + L + 1 ≤ 2 * M + 1 by omega)
      rw [show M + (L + 1) - 1 = (M + L - 1) + 1 by omega,
        integerHalfCarry_succ, integerHalfCarry_succ,
        show M + L - 1 + 2 = M + L + 1 by omega,
        hih, hcoeff]
      simp only [supportSuffixNumeral]
      split_ifs <;> push_cast <;> ring

/-- Terminal carry one turns the support bridge into the exact frozen-prefix
endpoint `Z = 1 + X` used by the phase criterion. -/
theorem integerHalfCarry_prefix_eq_one_add_supportSuffixNumeral
    (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M L : ℕ) (hM : 1 ≤ M)
    (hhorizon : M + L ≤ 2 * M + 1)
    (hterminal : integerHalfCarry A (M + L - 1) = 1) :
    integerHalfCarry (A ∩ Set.Iic M) (M + L - 1) =
      1 + (supportSuffixNumeral A M L : ℤ) := by
  rw [integerHalfCarry_prefix_eq_add_supportSuffixNumeral
    A M L hM hhorizon, hterminal]

/-! ## Actual-history realization -/

/-- Proper-coefficient history for rewinding from row `M+L` to row `M`,
newest coefficient first, exactly as `FixedCoeffRewind.rewind` consumes it. -/
noncomputable def supportCoeffRewindHistory
    (P : Set ℕ) (M : ℕ) : ℕ → List ℕ
  | 0 => []
  | L + 1 =>
      supportCoeff P (M + L + 1) :: supportCoeffRewindHistory P M L

@[simp] theorem supportCoeffRewindHistory_length
    (P : Set ℕ) (M L : ℕ) :
    (supportCoeffRewindHistory P M L).length = L := by
  induction L with
  | zero => simp [supportCoeffRewindHistory]
  | succ L ih => simp [supportCoeffRewindHistory, ih]

/-- Exact affine realization of an actual coefficient history.  This is the
integer identity behind the natural-number phase equation; it uses the live
`integerHalfCarry` recurrence rather than an independently described orbit. -/
theorem integerHalfCarry_add_offset_eq_denom_mul_initial
    (P : Set ℕ) (M L : ℕ) (hM : 1 ≤ M) :
    integerHalfCarry P (M + L - 1) +
          (offset (supportCoeffRewindHistory P M L) : ℤ) + 1 =
      (denom (supportCoeffRewindHistory P M L) : ℤ) *
        (integerHalfCarry P (M - 1) + 1) := by
  induction L with
  | zero => simp [supportCoeffRewindHistory, offset, denom]
  | succ L ih =>
      rw [show M + (L + 1) - 1 = (M + L - 1) + 1 by omega,
        integerHalfCarry_succ,
        show M + L - 1 + 2 = M + L + 1 by omega,
        supportCoeffRewindHistory, offset]
      push_cast
      calc
        2 * integerHalfCarry P (M + L - 1) -
                (supportCoeff P (M + L + 1) : ℤ) +
              ((supportCoeff P (M + L + 1) : ℤ) + 1 +
                2 * (offset (supportCoeffRewindHistory P M L) : ℤ)) + 1 =
            2 * (integerHalfCarry P (M + L - 1) +
              (offset (supportCoeffRewindHistory P M L) : ℤ) + 1) := by
          ring
        _ = 2 * ((denom (supportCoeffRewindHistory P M L) : ℤ) *
              (integerHalfCarry P (M - 1) + 1)) := by rw [ih]
        _ = (denom (supportCoeff P (M + L + 1) ::
              supportCoeffRewindHistory P M L) : ℤ) *
              (integerHalfCarry P (M - 1) + 1) := by
          simp only [denom, List.length_cons, pow_succ]
          push_cast
          ring

/-- The terminal-carry-one support history satisfies the exact realization
equation required by `phase_eq_denom_sub_one_sub_suffixNumeral`. -/
theorem supportHistory_realization
    (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M L ancestor : ℕ) (hM : 1 ≤ M)
    (hhorizon : M + L ≤ 2 * M + 1)
    (hterminal : integerHalfCarry A (M + L - 1) = 1)
    (hancestor : integerHalfCarry A (M - 1) = (ancestor : ℤ)) :
    offset (supportCoeffRewindHistory (A ∩ Set.Iic M) M L) +
          supportSuffixNumeral A M L + 2 =
      denom (supportCoeffRewindHistory (A ∩ Set.Iic M) M L) *
        (ancestor + 1) := by
  let P : Set ℕ := A ∩ Set.Iic M
  let cs := supportCoeffRewindHistory P M L
  have hendpoint := integerHalfCarry_prefix_eq_one_add_supportSuffixNumeral
    A M L hM hhorizon hterminal
  have hinitial : integerHalfCarry P (M - 1) = (ancestor : ℤ) := by
    rw [show P = A ∩ Set.Iic M by rfl,
      integerHalfCarry_inter_Iic_eq_of_succ_le A M (M - 1) (by omega),
      hancestor]
  have haffine := integerHalfCarry_add_offset_eq_denom_mul_initial
    P M L hM
  change integerHalfCarry P (M + L - 1) =
      1 + (supportSuffixNumeral A M L : ℤ) at hendpoint
  change integerHalfCarry P (M + L - 1) + (offset cs : ℤ) + 1 =
      (denom cs : ℤ) * (integerHalfCarry P (M - 1) + 1) at haffine
  rw [hendpoint, hinitial] at haffine
  change offset cs + supportSuffixNumeral A M L + 2 =
      denom cs * (ancestor + 1)
  have hn :
      1 + supportSuffixNumeral A M L + offset cs + 1 =
        denom cs * (ancestor + 1) := by
    exact_mod_cast haffine
  omega

/-- Exact live-support phase identity before feedback can return from the
removed suffix. -/
theorem phase_supportCoeffRewindHistory_eq
    (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M L ancestor : ℕ) (hM : 1 ≤ M)
    (hhorizon : M + L ≤ 2 * M + 1)
    (hterminal : integerHalfCarry A (M + L - 1) = 1)
    (hancestor : integerHalfCarry A (M - 1) = (ancestor : ℤ)) :
    phase (supportCoeffRewindHistory (A ∩ Set.Iic M) M L) =
      denom (supportCoeffRewindHistory (A ∩ Set.Iic M) M L) - 1 -
        supportSuffixNumeral A M L := by
  let cs := supportCoeffRewindHistory (A ∩ Set.Iic M) M L
  have hlen : (supportSuffixBits A M L).length = cs.length := by
    simp [cs]
  have hrealized := supportHistory_realization A M L ancestor hM hhorizon
    hterminal hancestor
  rw [← suffixNumeral_supportSuffixBits A M L] at hrealized ⊢
  exact phase_eq_denom_sub_one_sub_suffixNumeral cs
    (supportSuffixBits A M L) ancestor hlen hrealized

/-- Exact support-history singleton criterion.  It reduces the whole rewind
interval question to the single frozen-prefix inequality `B - 1 ≤ X`. -/
theorem rewind_supportCoeffHistory_singleton_iff
    (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M L ancestor B : ℕ) (hM : 1 ≤ M)
    (hhorizon : M + L ≤ 2 * M + 1)
    (hterminal : integerHalfCarry A (M + L - 1) = 1)
    (hancestor : integerHalfCarry A (M - 1) = (ancestor : ℤ))
    (hB : 1 ≤ B)
    (hwidth : B ≤ denom
      (supportCoeffRewindHistory (A ∩ Set.Iic M) M L)) :
    (∀ k : ℕ, 1 ≤ k → k ≤ B →
      rewind (supportCoeffRewindHistory (A ∩ Set.Iic M) M L) k =
        rewind (supportCoeffRewindHistory (A ∩ Set.Iic M) M L) 1) ↔
      B - 1 ≤ supportSuffixNumeral A M L := by
  let cs := supportCoeffRewindHistory (A ∩ Set.Iic M) M L
  have hlen : (supportSuffixBits A M L).length = cs.length := by
    simp [cs]
  have hrealized := supportHistory_realization A M L ancestor hM hhorizon
    hterminal hancestor
  rw [← suffixNumeral_supportSuffixBits A M L] at hrealized ⊢
  exact rewind_interval_singleton_iff_suffixNumeral_covers cs
    (supportSuffixBits A M L) ancestor B hlen hrealized hB hwidth

/-- Equivalent frozen-prefix form of the exact criterion.  Under terminal
carry one the prefix-zero-extension endpoint is `Z = 1 + X`, so singleton
rewind is exactly `B ≤ Z`; no phase or suffix encoding remains downstream. -/
theorem rewind_supportCoeffHistory_singleton_iff_prefixCarry_covers
    (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M L ancestor B : ℕ) (hM : 1 ≤ M)
    (hhorizon : M + L ≤ 2 * M + 1)
    (hterminal : integerHalfCarry A (M + L - 1) = 1)
    (hancestor : integerHalfCarry A (M - 1) = (ancestor : ℤ))
    (hB : 1 ≤ B)
    (hwidth : B ≤ denom
      (supportCoeffRewindHistory (A ∩ Set.Iic M) M L)) :
    (∀ k : ℕ, 1 ≤ k → k ≤ B →
      rewind (supportCoeffRewindHistory (A ∩ Set.Iic M) M L) k =
        rewind (supportCoeffRewindHistory (A ∩ Set.Iic M) M L) 1) ↔
      (B : ℤ) ≤ integerHalfCarry (A ∩ Set.Iic M) (M + L - 1) := by
  rw [rewind_supportCoeffHistory_singleton_iff A M L ancestor B hM
    hhorizon hterminal hancestor hB hwidth,
    integerHalfCarry_prefix_eq_one_add_supportSuffixNumeral
      A M L hM hhorizon hterminal]
  norm_cast
  omega

#print axioms suffixNumeral_lt_two_pow_length
#print axioms phase_eq_denom_sub_one_sub_suffixNumeral
#print axioms rewind_interval_singleton_iff_suffixNumeral_covers
#print axioms supportCoeff_eq_prefix_add_currentBit
#print axioms integerHalfCarry_prefix_eq_add_supportSuffixNumeral
#print axioms integerHalfCarry_prefix_eq_one_add_supportSuffixNumeral
#print axioms integerHalfCarry_add_offset_eq_denom_mul_initial
#print axioms supportHistory_realization
#print axioms phase_supportCoeffRewindHistory_eq
#print axioms rewind_supportCoeffHistory_singleton_iff
#print axioms rewind_supportCoeffHistory_singleton_iff_prefixCarry_covers

end Erdos249257.FixedCoeffRewindPhase
