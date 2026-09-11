import Erdos249257.CurvatureCarry
import Erdos249257.ExponentOnlyTransport

/-!
# Anchored joint `(3,5)` exponent transport

This module packages the primitive four-vertex affine annihilator

`q(X,Y) = X * Y - 3 * X - 2 * Y + 4`.

Its two moments vanish (`q(1,1) = q(3,5) = 0`) while its quadratic response
is `q(9,25) = 152`.  The first section records the resulting universal
old-channel obstruction: every divisor channel already present at an LCM
height is killed exactly.  The second section turns the same coefficients
into a sharp dyadic window certificate and a conditional irrationality
endpoint.

The unbounded certificate supply remains open.  In particular, the finite
kernel and window checks accompanying this file are regression evidence, not
a proof of that supply.
-/

set_option maxRecDepth 10000

namespace Erdos249257.JointExponentTransport

open Finset
open TotientTailPeriodKiller
open ExponentOnlyTransport

/-! ## The two-moment old-channel obstruction -/

/-- Any finite real combination with zero constant and first moments kills an
old affine residue channel.  This is independent of the particular `(3,5)`
operator. -/
theorem oldChannel_affine_moment_annihilation
    {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (c : ι → ℝ)
    (hzero : ∑ i, c i = 0)
    (hfirst : ∑ i, c i * (m i : ℝ) = 0)
    {d H : ℕ} (hd : 0 < d) (hdH : d ∣ H) :
    ∑ i, c i * transportResidueKernel d (m i * H) = 0 := by
  have haffine (i : ι) :
      transportResidueKernel d (m i * H) =
        ((m i : ℝ) * (H : ℝ)) * residueSlope d 0 + residueIntercept d 0 := by
    have hdmi : d ∣ m i * H := hdH.mul_left (m i)
    have hmod : (m i * H) % d = 0 := Nat.mod_eq_zero_of_dvd hdmi
    rw [transportResidueKernel_eq_affineState hd]
    simp [residueSlope, residueIntercept, transportResidueOffset, hmod]
  simp_rw [haffine, mul_add]
  rw [sum_add_distrib]
  have hslope :
      (∑ i, c i * (((m i : ℝ) * (H : ℝ)) * residueSlope d 0)) =
        (∑ i, c i * (m i : ℝ)) * ((H : ℝ) * residueSlope d 0) := by
    calc
      (∑ i, c i * (((m i : ℝ) * (H : ℝ)) * residueSlope d 0)) =
          ∑ i, (c i * (m i : ℝ)) * ((H : ℝ) * residueSlope d 0) := by
            apply sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i, c i * (m i : ℝ)) * ((H : ℝ) * residueSlope d 0) := by
        exact (Finset.sum_mul Finset.univ
          (fun i => c i * (m i : ℝ)) ((H : ℝ) * residueSlope d 0)).symm
  have hintercept :
      (∑ i, c i * residueIntercept d 0) =
        (∑ i, c i) * residueIntercept d 0 := by rw [sum_mul]
  rw [hslope, hintercept, hzero, hfirst]
  ring

/-- The primitive joint `(3,5)` observable kills every old divisor channel. -/
theorem joint35_oldChannel_zero
    {d H : ℕ} (hd : 0 < d) (hdH : d ∣ H) :
    transportResidueKernel d (15 * H)
      - 3 * transportResidueKernel d (3 * H)
      - 2 * transportResidueKernel d (5 * H)
      + 4 * transportResidueKernel d H = 0 := by
  have h15 : d ∣ 15 * H := hdH.mul_left 15
  have h3 : d ∣ 3 * H := hdH.mul_left 3
  have h5 : d ∣ 5 * H := hdH.mul_left 5
  have h1 : d ∣ H := hdH
  rw [transportResidueKernel_eq_affineState hd,
    transportResidueKernel_eq_affineState hd,
    transportResidueKernel_eq_affineState hd,
    transportResidueKernel_eq_affineState hd]
  have hs15 : residueSlope d (15 * H) = residueSlope d 0 := by
    simp [residueSlope, Nat.mod_eq_zero_of_dvd h15]
  have hs3 : residueSlope d (3 * H) = residueSlope d 0 := by
    simp [residueSlope, Nat.mod_eq_zero_of_dvd h3]
  have hs5 : residueSlope d (5 * H) = residueSlope d 0 := by
    simp [residueSlope, Nat.mod_eq_zero_of_dvd h5]
  have hs1 : residueSlope d H = residueSlope d 0 := by
    simp [residueSlope, Nat.mod_eq_zero_of_dvd h1]
  have hb15 : residueIntercept d (15 * H) = residueIntercept d 0 := by
    simp [residueIntercept, transportResidueOffset, Nat.mod_eq_zero_of_dvd h15]
  have hb3 : residueIntercept d (3 * H) = residueIntercept d 0 := by
    simp [residueIntercept, transportResidueOffset, Nat.mod_eq_zero_of_dvd h3]
  have hb5 : residueIntercept d (5 * H) = residueIntercept d 0 := by
    simp [residueIntercept, transportResidueOffset, Nat.mod_eq_zero_of_dvd h5]
  have hb1 : residueIntercept d H = residueIntercept d 0 := by
    simp [residueIntercept, transportResidueOffset, Nat.mod_eq_zero_of_dvd h1]
  rw [hs15, hs3, hs5, hs1, hb15, hb3, hb5, hb1]
  push_cast
  ring

/-! ## Four-vertex tail and exact dyadic certificate -/

/-- The curvature-preserving four-vertex cone observable. -/
noncomputable def joint35ConeTail (H : ℕ) : ℝ :=
  totientTail (15 * H) - 3 * totientTail (3 * H) -
    2 * totientTail (5 * H) + 4 * totientTail H

/-- The integer window obtained from the three cone differences based at `H`. -/
def joint35ConeWindow (H L : ℕ) : ℤ :=
  windowDiscrepancy (14 * H) H L -
    3 * windowDiscrepancy (2 * H) H L -
    2 * windowDiscrepancy (4 * H) H L

/-- The shifted tail left after truncating the joint observable at depth `L`. -/
noncomputable def joint35ConeShiftedTail (H L : ℕ) : ℝ :=
  totientTail (15 * H + L) - 3 * totientTail (3 * H + L) -
    2 * totientTail (5 * H + L) + 4 * totientTail (H + L)

/-- Sharp symmetric error radius for the joint four-vertex window. -/
def sharpJoint35ConeRadius (H L : ℕ) : ℤ := 19 * H + 5 * L + 5

/-- Exact joint prefix/tail split. -/
theorem two_pow_mul_joint35Cone_eq_window_add_shifted (H L : ℕ) :
    (2 : ℝ) ^ L * joint35ConeTail H =
      (joint35ConeWindow H L : ℝ) + joint35ConeShiftedTail H L := by
  have h15 := windowDiscrepancy_div_eq (14 * H) H L
  have h3 := windowDiscrepancy_div_eq (2 * H) H L
  have h5 := windowDiscrepancy_div_eq (4 * H) H L
  have ht15 := totientTail_eq_partial_add_shifted (15 * H) L
  have ht3 := totientTail_eq_partial_add_shifted (3 * H) L
  have ht5 := totientTail_eq_partial_add_shifted (5 * H) L
  have ht1 := totientTail_eq_partial_add_shifted H L
  have hpow : (0 : ℝ) < 2 ^ L := by positivity
  unfold joint35ConeTail joint35ConeWindow joint35ConeShiftedTail
  push_cast
  rw [show H + 14 * H = 15 * H by ring] at h15
  rw [show H + 2 * H = 3 * H by ring] at h3
  rw [show H + 4 * H = 5 * H by ring] at h5
  rw [ht15, ht3, ht5, ht1]
  field_simp [hpow.ne'] at h15 h3 h5 ⊢
  linarith

/-- The shifted joint tail lies in the sharp symmetric strip. -/
theorem abs_joint35ConeShiftedTail_le (H L : ℕ) (hH : 1 ≤ H) :
    |joint35ConeShiftedTail H L| ≤ (sharpJoint35ConeRadius H L : ℝ) := by
  have h15p := totientTail_pos (15 * H + L)
  have h3p := totientTail_pos (3 * H + L)
  have h5p := totientTail_pos (5 * H + L)
  have h1p := totientTail_pos (H + L)
  have h15u := totientTail_le_succ (15 * H + L) (by omega)
  have h3u := totientTail_le_succ (3 * H + L) (by omega)
  have h5u := totientTail_le_succ (5 * H + L) (by omega)
  have h1u := totientTail_le_succ (H + L) (by omega)
  unfold joint35ConeShiftedTail sharpJoint35ConeRadius
  push_cast at h15u h3u h5u h1u ⊢
  rw [abs_le]
  constructor <;> linarith

/-- A dyadic residue separated from both endpoint error bands. -/
def sharpJoint35ConeCert (H L : ℕ) : Prop :=
  sharpJoint35ConeRadius H L < joint35ConeWindow H L % 2 ^ L ∧
    joint35ConeWindow H L % 2 ^ L < 2 ^ L - sharpJoint35ConeRadius H L

instance (H L : ℕ) : Decidable (sharpJoint35ConeCert H L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A sharp joint residue gap excludes integral four-vertex curvature. -/
theorem joint35Cone_notMem_int_of_cert {H L : ℕ} (hH : 1 ≤ H)
    (hcert : sharpJoint35ConeCert H L) :
    joint35ConeTail H ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨k, hk⟩
  obtain ⟨hlow, hhigh⟩ := hcert
  have hsplit := two_pow_mul_joint35Cone_eq_window_add_shifted H L
  have htail := abs_joint35ConeShiftedTail_le H L hH
  set A : ℤ := joint35ConeWindow H L
  set P : ℤ := 2 ^ L
  set B : ℤ := sharpJoint35ConeRadius H L
  have hPpos : 0 < P := by simp [P]
  have hclose : |A - k * P| ≤ B := by
    have heq : ((A - k * P : ℤ) : ℝ) = -joint35ConeShiftedTail H L := by
      rw [← hk] at hsplit
      change (2 : ℝ) ^ L * (k : ℝ) =
        (A : ℝ) + joint35ConeShiftedTail H L at hsplit
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

/-- The only open arithmetic throat for this anchored joint observable. -/
def AnchoredJoint35ConeSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t L : ℕ,
    max t₀ 5 ≤ t ∧ sharpJoint35ConeCert (periodLcm t) L

/-- An unbounded joint certificate supply contradicts rational LCM-cone
flatness and proves irrationality of the totient series. -/
theorem irrational_totient_series_of_anchoredJoint35ConeSupply
    (hsupply : AnchoredJoint35ConeSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨t, L, ht, hcert⟩ := hsupply t₁
  have ht₁ : t₁ ≤ t := (le_max_left _ _).trans ht
  obtain ⟨a, ha⟩ := hflat t ht₁ 1 14 (by omega)
  obtain ⟨b, hb⟩ := hflat t ht₁ 1 2 (by omega)
  obtain ⟨c, hc⟩ := hflat t ht₁ 1 4 (by omega)
  have hHpos : 1 ≤ periodLcm t := periodLcm_pos t
  apply joint35Cone_notMem_int_of_cert hHpos hcert
  refine ⟨a - 3 * b - 2 * c, ?_⟩
  unfold joint35ConeTail
  push_cast
  norm_num at ha hb hc
  rw [show periodLcm t + 14 * periodLcm t = 15 * periodLcm t by ring] at ha
  rw [show periodLcm t + 2 * periodLcm t = 3 * periodLcm t by ring] at hb
  rw [show periodLcm t + 4 * periodLcm t = 5 * periodLcm t by ring] at hc
  linarith [ha, hb, hc]

/-! ## Recurrence and compatibility with diagonal transport -/

/-- The new integer letter appended to the joint window at offset `s`. -/
def joint35ConeDrive (H s : ℕ) : ℤ :=
  (Nat.totient (15 * H + s) : ℤ) - 3 * Nat.totient (3 * H + s) -
    2 * Nat.totient (5 * H + s) + 4 * Nat.totient (H + s)

/-- The joint window is an exact input-driven doubling recurrence. -/
theorem joint35ConeWindow_succ (H L : ℕ) :
    joint35ConeWindow H (L + 1) =
      2 * joint35ConeWindow H L + joint35ConeDrive H (L + 1) := by
  unfold joint35ConeWindow joint35ConeDrive
  rw [windowDiscrepancy_succ, windowDiscrepancy_succ, windowDiscrepancy_succ]
  unfold deltaTotient
  ring_nf

/-- Eight-vertex compatibility object for the existing diagonal increment
owner.  It is not a second supply hypothesis. -/
noncomputable def joint35TransportTail (H : ℕ) : ℝ :=
  joint35ConeTail (2 * H) - joint35ConeTail H

theorem joint35TransportTail_expand (H : ℕ) :
    joint35TransportTail H =
      (totientTail (30 * H) - totientTail (15 * H)) -
      3 * (totientTail (6 * H) - totientTail (3 * H)) -
      2 * (totientTail (10 * H) - totientTail (5 * H)) +
      4 * (totientTail (2 * H) - totientTail H) := by
  unfold joint35TransportTail joint35ConeTail
  ring_nf

#print axioms oldChannel_affine_moment_annihilation
#print axioms joint35_oldChannel_zero
#print axioms joint35Cone_notMem_int_of_cert
#print axioms irrational_totient_series_of_anchoredJoint35ConeSupply

end Erdos249257.JointExponentTransport
