import Erdos249257.CurvatureCarry
import Erdos249257.ExponentOnlyTransport

/-!
# The balanced `(1,2,3,6)` totient-tail boundary word

This module packages

`(R_(6H) - R_(3H)) - 3 * (R_(2H) - R_H)`

as one exact dyadic residue certificate.  Its shifted remainder has the sharp
elementary radius `9H + 4L + 4`.  The finite certificate at `H = 60`,
`L = 12` is checked by kernel reduction below, while the arbitrarily-large
certificate supply remains an explicit hypothesis.  Thus this module is a
reduction and finite receipt, not a proof of Erdős problem #249.
-/

set_option maxRecDepth 10000

namespace Erdos249257
namespace TotientTailPeriodKiller

/-- The balanced four-ray tail word on multipliers `(1,2,3,6)`. -/
noncomputable def threeTransportTail (H : ℕ) : ℝ :=
  (totientTail (6 * H) - totientTail (3 * H)) -
    3 * (totientTail (2 * H) - totientTail H)

/-- The exact integer letter at boundary offset `s`. -/
def threeTransportDrive (H s : ℕ) : ℤ :=
  (Nat.totient (6 * H + s) : ℤ) - Nat.totient (3 * H + s) -
    3 * Nat.totient (2 * H + s) + 3 * Nat.totient (H + s)

/-- The dyadic depth-`L` boundary window. -/
def threeTransportWindow (H L : ℕ) : ℤ :=
  windowDiscrepancy (3 * H) (3 * H) L - 3 * windowDiscrepancy H H L

/-- The shifted tail left after truncating at depth `L`. -/
noncomputable def threeTransportShiftedTail (H L : ℕ) : ℝ :=
  (totientTail (6 * H + L) - totientTail (3 * H + L)) -
    3 * (totientTail (2 * H + L) - totientTail (H + L))

/-- The symmetric edge radius forced by the positive and negative stencil
masses: both sides have multiplier mass `4` and first moment `9`. -/
def threeTransportRadius (H L : ℕ) : ℤ := 9 * H + 4 * L + 4

/-- The boundary letter itself already has the sharp elementary pointwise
bound obtained by grouping the positive and negative stencil parts. -/
theorem abs_threeTransportDrive_le (H s : ℕ) :
    |threeTransportDrive H s| ≤ (9 * H + 4 * s : ℤ) := by
  have h6 : (Nat.totient (6 * H + s) : ℤ) ≤ (6 * H + s : ℕ) := by
    exact_mod_cast Nat.totient_le (6 * H + s)
  have h3 : (Nat.totient (3 * H + s) : ℤ) ≤ (3 * H + s : ℕ) := by
    exact_mod_cast Nat.totient_le (3 * H + s)
  have h2 : (Nat.totient (2 * H + s) : ℤ) ≤ (2 * H + s : ℕ) := by
    exact_mod_cast Nat.totient_le (2 * H + s)
  have h1 : (Nat.totient (H + s) : ℤ) ≤ (H + s : ℕ) := by
    exact_mod_cast Nat.totient_le (H + s)
  have h6n : 0 ≤ (Nat.totient (6 * H + s) : ℤ) := by positivity
  have h3n : 0 ≤ (Nat.totient (3 * H + s) : ℤ) := by positivity
  have h2n : 0 ≤ (Nat.totient (2 * H + s) : ℤ) := by positivity
  have h1n : 0 ≤ (Nat.totient (H + s) : ℤ) := by positivity
  unfold threeTransportDrive
  rw [abs_le]
  constructor <;> push_cast at * <;> omega

/-- Exact prefix/tail split for the balanced four-ray word. -/
theorem two_pow_mul_threeTransport_eq_window_add_shifted (H L : ℕ) :
    (2 : ℝ) ^ L * threeTransportTail H =
      (threeTransportWindow H L : ℝ) + threeTransportShiftedTail H L := by
  have htop := windowDiscrepancy_div_eq (3 * H) (3 * H) L
  have hbot := windowDiscrepancy_div_eq H H L
  have h6 := totientTail_eq_partial_add_shifted (6 * H) L
  have h3 := totientTail_eq_partial_add_shifted (3 * H) L
  have h2 := totientTail_eq_partial_add_shifted (2 * H) L
  have h1 := totientTail_eq_partial_add_shifted H L
  have hpow : (0 : ℝ) < 2 ^ L := by positivity
  unfold threeTransportTail threeTransportWindow threeTransportShiftedTail
  push_cast
  rw [show 3 * H + 3 * H = 6 * H by ring] at htop
  rw [show H + H = 2 * H by ring] at hbot
  rw [h6, h3, h2, h1]
  field_simp [hpow.ne'] at htop hbot ⊢
  linarith

/-- The shifted tail lies in the sharp symmetric strip. -/
theorem abs_threeTransportShiftedTail_le (H L : ℕ) (hH : 1 ≤ H) :
    |threeTransportShiftedTail H L| ≤ (threeTransportRadius H L : ℝ) := by
  have h6p := totientTail_pos (6 * H + L)
  have h3p := totientTail_pos (3 * H + L)
  have h2p := totientTail_pos (2 * H + L)
  have h1p := totientTail_pos (H + L)
  have h6u := totientTail_le_succ (6 * H + L) (by omega)
  have h3u := totientTail_le_succ (3 * H + L) (by omega)
  have h2u := totientTail_le_succ (2 * H + L) (by omega)
  have h1u := totientTail_le_succ (H + L) (by omega)
  unfold threeTransportShiftedTail threeTransportRadius
  push_cast at h6u h3u h2u h1u ⊢
  rw [abs_le]
  constructor <;> linarith

/-- The boundary word is an exact input-driven doubling recurrence. -/
theorem threeTransportWindow_succ (H L : ℕ) :
    threeTransportWindow H (L + 1) =
      2 * threeTransportWindow H L + threeTransportDrive H (L + 1) := by
  unfold threeTransportWindow threeTransportDrive
  rw [windowDiscrepancy_succ, windowDiscrepancy_succ]
  unfold deltaTotient
  ring_nf

/-- The exact decidable lattice-separation certificate. -/
def sharpThreeTransportCert (H L : ℕ) : Prop :=
  threeTransportRadius H L < threeTransportWindow H L % 2 ^ L ∧
    threeTransportWindow H L % 2 ^ L < 2 ^ L - threeTransportRadius H L

instance (H L : ℕ) : Decidable (sharpThreeTransportCert H L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every certificate has enough dyadic room for both excluded boundary arcs. -/
theorem sharpThreeTransportCert_depth_floor {H L : ℕ}
    (hcert : sharpThreeTransportCert H L) :
    (2 * threeTransportRadius H L : ℤ) < 2 ^ L := by
  rcases hcert with ⟨hleft, hright⟩
  linarith

/-- A sharp residue gap excludes integral three-transport curvature. -/
theorem threeTransport_notMem_int_of_cert {H L : ℕ} (hH : 1 ≤ H)
    (hcert : sharpThreeTransportCert H L) :
    threeTransportTail H ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨k, hk⟩
  obtain ⟨hlow, hhigh⟩ := hcert
  have hsplit := two_pow_mul_threeTransport_eq_window_add_shifted H L
  have htail := abs_threeTransportShiftedTail_le H L hH
  set A : ℤ := threeTransportWindow H L
  set P : ℤ := 2 ^ L
  set B : ℤ := threeTransportRadius H L
  have hPpos : 0 < P := by simp [P]
  have hclose : |A - k * P| ≤ B := by
    have heq : ((A - k * P : ℤ) : ℝ) = -threeTransportShiftedTail H L := by
      rw [← hk] at hsplit
      change (2 : ℝ) ^ L * (k : ℝ) =
        (A : ℝ) + threeTransportShiftedTail H L at hsplit
      rw [Int.cast_sub, Int.cast_mul]
      simp only [P, Int.cast_pow, Int.cast_ofNat]
      linarith
    exact_mod_cast (show |((A - k * P : ℤ) : ℝ)| ≤ (B : ℝ) by
      rw [heq, abs_neg]
      exact htail)
  set x : ℤ := A - k * P
  have hxmod : x % P = A % P := by
    have hrw : x = A + P * (-k) := by rw [show x = A - k * P by rfl]; ring
    rw [hrw, Int.add_mul_emod_self_left]
  have hdm : P * (x / P) + A % P = x := by
    rw [← hxmod]
    exact Int.mul_ediv_add_emod x P
  have habs := abs_le.mp (show |x| ≤ B by simpa [x] using hclose)
  by_cases ht : 0 ≤ x / P
  · have hge : 0 ≤ P * (x / P) := mul_nonneg hPpos.le ht
    linarith
  · have ht1 : x / P ≤ -1 := by omega
    have hle : P * (x / P) ≤ P * (-1) :=
      mul_le_mul_of_nonneg_left ht1 hPpos.le
    linarith

/-- The new boundary word agrees definitionally with the earlier
exponent-only transport commutator. -/
theorem threeTransportTail_eq_commutator (H : ℕ) :
    threeTransportTail H =
      ExponentOnlyTransport.threeTransportTailCommutator H := by
  rfl

/-- Arbitrarily large exact boundary certificates.  This is the sole open
producer socket in this module. -/
def RoughnessBoundaryLatticeSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t L, t₀ ≤ t ∧ sharpThreeTransportCert (periodLcm t) L

/-- The boundary-certificate supply contradicts eventual LCM-cone flatness. -/
theorem irrational_totientSeries_of_roughnessBoundaryLatticeSupply
    (hsupply : RoughnessBoundaryLatticeSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨t, L, ht, hcert⟩ := hsupply (max t₁ 1)
  have ht₁ : t₁ ≤ t := (le_max_left _ _).trans ht
  obtain ⟨x, hx⟩ := hflat t ht₁ 1 1 (by omega)
  obtain ⟨y, hy⟩ := hflat t ht₁ 3 3 (by omega)
  have hHpos : 1 ≤ periodLcm t := periodLcm_pos t
  apply threeTransport_notMem_int_of_cert hHpos hcert
  refine ⟨y - 3 * x, ?_⟩
  unfold threeTransportTail
  push_cast
  rw [show 1 * periodLcm t + 1 * periodLcm t = 2 * periodLcm t by ring,
    one_mul] at hx
  rw [show 3 * periodLcm t + 3 * periodLcm t = 6 * periodLcm t by ring] at hy
  linarith [hx, hy]

/-- An exact balanced boundary word at the lcm height `H = lcm(1,…,6)`. -/
theorem threeTransportWindow_60_12 :
    threeTransportWindow 60 12 = 19316 := by
  set_option maxRecDepth 10000 in
    decide

/-- Kernel-checked finite lattice separation at `t = 6`, `H = 60`. -/
theorem sharpThreeTransportCert_60_12 :
    sharpThreeTransportCert 60 12 := by
  rw [sharpThreeTransportCert, threeTransportWindow_60_12]
  norm_num [threeTransportRadius]

#print axioms threeTransport_notMem_int_of_cert
#print axioms irrational_totientSeries_of_roughnessBoundaryLatticeSupply
#print axioms sharpThreeTransportCert_60_12

end TotientTailPeriodKiller
end Erdos249257
