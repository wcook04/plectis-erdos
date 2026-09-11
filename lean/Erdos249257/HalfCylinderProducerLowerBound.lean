import Erdos249257.HalfCylinderBoundaryPulse
import Erdos249257.HalfCylinderSeamProducerAlignment

/-!
# Concrete producer coordinates as affine carries

The upper and middle coordinates in the concrete seam recurrence are not
merely analogous to the producer carry: they are exactly its two signed
forms.  For a row word `b`, inserting the terminal rank `s` into its support
gives

`producerCarry = 4 * (wordDefect - 1) - wordPulse`.

At the actual adjacent cut this specializes to

* the below/middle coordinate `4 * remainder - belowPulse - 4`; and
* the negative upper coordinate
  `-(4 * overshoot + abovePulse + 4)`.

Thus any exponential lower bound for the concrete producer coordinates is
precisely a quantitative affine-carry separation theorem.  The identities
below make that remaining arithmetic input explicit; they do not assert the
unproved exponential bounds.
-/

namespace Erdos249257

open Set
open HalfCarryReachability
open HalfCylinderFiniteShadow
open HalfCylinderIntegerGreedy
open scoped BigOperators

noncomputable section

/-! ## Pulse/incidence adapter -/

/-- The row pulse is exactly the paired odd/even divisor incidence at the
two new coefficient rows. -/
theorem wordPulse_eq_pairedSupportCoeff
    {s : ℕ} (b : SeamRowWord s) :
    wordPulse s b.toNatWord =
      supportCoeff (↑(seamWordSupport b) : Set ℕ) (2 * s + 2) +
        2 * supportCoeff (↑(seamWordSupport b) : Set ℕ) (2 * s + 1) := by
  classical
  rw [wordPulse_eq_sum_seamWordSupport]
  rw [supportCoeff_finset_eq_indicatorSum,
    supportCoeff_finset_eq_indicatorSum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  unfold rowPulse
  simp [Nat.mem_divisors]

/-- Inserting the terminal rank does not affect either pulse row: for
`s ≥ 5`, the rank `s` divides neither `2s+1` nor `2s+2`. -/
theorem pairedSupportCoeff_insert_terminal_eq_wordPulse
    {s : ℕ} (hs : 5 ≤ s) (b : SeamRowWord s) :
    2 * supportCoeff
          (insert s (↑(seamWordSupport b) : Set ℕ)) (2 * s + 1) +
        supportCoeff
          (insert s (↑(seamWordSupport b) : Set ℕ)) (2 * s + 2) =
      wordPulse s b.toNatWord := by
  have hsP : s ∉ seamWordSupport b := by
    intro hsupp
    exact (Nat.lt_irrefl s) (seamWordSupport_below hsupp).2
  have hsPset : s ∉ (↑(seamWordSupport b) : Set ℕ) := by
    simpa using hsP
  have hsnotdvdOdd : ¬ s ∣ 2 * s + 1 := by
    rintro ⟨k, hk⟩
    have hkgt : 2 < k := by
      by_contra hnot
      have hkle : k ≤ 2 := by omega
      nlinarith
    have hklt : k < 3 := by
      by_contra hnot
      have hkge : 3 ≤ k := by omega
      nlinarith
    omega
  have hsnotdvdEven : ¬ s ∣ 2 * s + 2 := by
    rintro ⟨k, hk⟩
    have hkgt : 2 < k := by
      by_contra hnot
      have hkle : k ≤ 2 := by omega
      nlinarith
    have hklt : k < 3 := by
      by_contra hnot
      have hkge : 3 ≤ k := by omega
      nlinarith
    omega
  have hsnotmemOdd : s ∉ (2 * s + 1).divisors := by
    simpa [Nat.mem_divisors] using hsnotdvdOdd
  have hsnotmemEven : s ∉ (2 * s + 2).divisors := by
    simpa [Nat.mem_divisors] using hsnotdvdEven
  rw [supportCoeff_insert_eq_add_indicator _ hsPset,
    supportCoeff_insert_eq_add_indicator _ hsPset]
  simp only [hsnotmemOdd, hsnotmemEven, if_false, add_zero]
  rw [wordPulse_eq_pairedSupportCoeff]
  omega

/-! ## Generic row-word carry identity -/

/-- Inserting the terminal rank into any concrete seam word turns its
signed integer subset-sum defect into the producer-aligned affine carry. -/
theorem producerCarry_insert_seamWordSupport_eq
    {s : ℕ} (hs : 5 ≤ s) (b : SeamRowWord s) :
    producerCarry
        (insert s (↑(seamWordSupport b) : Set ℕ)) s =
      4 * (wordDefect s b.toNatWord - 1) -
        (wordPulse s b.toNatWord : ℤ) := by
  let P := seamWordSupport b
  let A : Set ℕ := insert s (↑P : Set ℕ)
  let δ := integerHalfCarry A (2 * s - 2)
  have hsP : s ∉ P := by
    intro hsupp
    exact (Nat.lt_irrefl s) (seamWordSupport_below hsupp).2
  have hbelow : ∀ d ∈ P, 2 ≤ d ∧ d < s := by
    intro d hd
    exact seamWordSupport_below hd
  have hhole :=
    actualSeamHole_eq_target_sub_stemTruncatedSum_unconditional
      s P (by omega) hsP hbelow
  have hsum :
      stemTruncatedSum s P = wordWeightSum s b.toNatWord := by
    rw [stemTruncatedSum_eq_sum_support hbelow,
      wordWeightSum_eq_sum_seamWordSupport]
  have hdefect :
      2 * δ - (supportCoeff (↑P : Set ℕ) (2 * s) : ℤ) =
        wordDefect s b.toNatWord := by
    change
      2 * integerHalfCarry (insert s (↑P : Set ℕ)) (2 * s - 2) -
          (supportCoeff (↑P : Set ℕ) (2 * s) : ℤ) = _
    rw [hhole, hsum]
    rfl
  have hcarry := producerCarry_insert_eq_four_mul_shiftedHole_sub_pulse
    (↑P : Set ℕ) s (by omega) (by simpa using hsP) δ (by rfl)
  have hpulse := pairedSupportCoeff_insert_terminal_eq_wordPulse hs b
  change producerCarry A s = _
  rw [hcarry, hdefect]
  change
    4 * (wordDefect s b.toNatWord - 1) -
        ((2 * supportCoeff A (2 * s + 1) +
          supportCoeff A (2 * s + 2) : ℕ) : ℤ) = _
  rw [← hpulse]

/-! ## The two concrete adjacent-cut coordinates -/

/-- The middle-producer coordinate is exactly the producer carry of the
terminal-augmented below support. -/
theorem producerCarry_insert_seamBelowSupport_eq_middleCoordinate
    (s : ℕ) (hs : 5 ≤ s) :
    producerCarry
        (insert s
          (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)) s =
      4 * ((seamAdjacentCut s hs).remainder : ℤ) -
        ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hcarry := producerCarry_insert_seamWordSupport_eq hs K.below
  have hrem := K.old_below_add_remainder
  change
    F.oldSum K.below + K.remainder = seamSubsetTarget s at hrem
  have hdefect :
      wordDefect s K.below.toNatWord = (K.remainder : ℤ) := by
    unfold wordDefect
    change
      (seamSubsetTarget s : ℤ) - (F.oldSum K.below : ℤ) =
        (K.remainder : ℤ)
    have hremZ :
        (F.oldSum K.below : ℤ) + (K.remainder : ℤ) =
          (seamSubsetTarget s : ℤ) := by
      exact_mod_cast hrem
    omega
  have hpulse : wordPulse s K.below.toNatWord = K.belowPulse := rfl
  change producerCarry
      (insert s (↑(seamWordSupport K.below) : Set ℕ)) s = _
  rw [hcarry, hdefect, hpulse]
  ring

/-- The upper-producer coordinate, with the unavoidable four-unit terminal
shift, is the negative producer carry of the terminal-augmented above
support. -/
theorem producerCarry_insert_seamAboveSupport_eq_neg_upperCoordinate
    (s : ℕ) (hs : 5 ≤ s) :
    producerCarry
        (insert s
          (↑(seamWordSupport (seamAdjacentCut s hs).above) : Set ℕ)) s =
      -((4 * (seamAdjacentCut s hs).overshoot +
          (seamAdjacentCut s hs).abovePulse + 4 : ℕ) : ℤ) := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hcarry := producerCarry_insert_seamWordSupport_eq hs K.above
  have hover := K.capacity_add_overshoot
  change
    seamSubsetTarget s + K.overshoot = F.oldSum K.above at hover
  have hdefect :
      wordDefect s K.above.toNatWord = -((K.overshoot : ℕ) : ℤ) := by
    unfold wordDefect
    change
      (seamSubsetTarget s : ℤ) - (F.oldSum K.above : ℤ) =
        -((K.overshoot : ℕ) : ℤ)
    have hoverZ :
        (seamSubsetTarget s : ℤ) + (K.overshoot : ℤ) =
          (F.oldSum K.above : ℤ) := by
      exact_mod_cast hover
    omega
  have hpulse : wordPulse s K.above.toNatWord = K.abovePulse := rfl
  change producerCarry
      (insert s (↑(seamWordSupport K.above) : Set ℕ)) s = _
  rw [hcarry, hdefect, hpulse]
  push_cast
  ring

#print axioms wordPulse_eq_pairedSupportCoeff
#print axioms producerCarry_insert_seamWordSupport_eq
#print axioms producerCarry_insert_seamBelowSupport_eq_middleCoordinate
#print axioms producerCarry_insert_seamAboveSupport_eq_neg_upperCoordinate

end

end Erdos249257
