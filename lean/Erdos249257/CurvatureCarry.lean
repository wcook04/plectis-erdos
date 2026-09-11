import Erdos249257.LcmConeFlatness

/-!
# Curvature carry for the totient tail

This module packages the affine second difference

`Q H = R_(4H) - 3 R_(2H) + 2 R_H`

as one direct dyadic certificate.  Its truncation error has radius
`6H + 3L + 3`, so the consumer does not need to pigeonhole through either
of the two first-difference certificates.  The module also records the exact
input-driven depth recurrence and a denominator-free common-carrier identity.

These are reductions, not an unbounded escape theorem.  In particular they do
not settle Erdős problem #249.
-/

set_option maxRecDepth 10000

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

/-- The affine curvature of the three LCM-cone tail vertices `H, 2H, 4H`. -/
noncomputable def curvatureTail (H : ℕ) : ℝ :=
  totientTail (4 * H) - 3 * totientTail (2 * H) + 2 * totientTail H

/-- The signed depth-`L` integer window for `curvatureTail`. -/
def curvatureWindow (H L : ℕ) : ℤ :=
  windowDiscrepancy (2 * H) (2 * H) L - 2 * windowDiscrepancy H H L

/-- The shifted tail left after truncating `curvatureTail` at depth `L`. -/
noncomputable def curvatureShiftedTail (H L : ℕ) : ℝ :=
  totientTail (4 * H + L) - 3 * totientTail (2 * H + L) +
    2 * totientTail (H + L)

/-- The fresh integer letter appended to the curvature word at offset `s`. -/
def curvatureDrive (H s : ℕ) : ℤ :=
  (Nat.totient (4 * H + s) : ℤ) - 3 * Nat.totient (2 * H + s) +
    2 * Nat.totient (H + s)

/-- The curvature drive has a uniform elementary bound.  This deliberately
uses only `Nat.totient_le`; no factorisation or finite fixture enters. -/
theorem abs_curvatureDrive_le (H s : ℕ) :
    |curvatureDrive H s| ≤ (6 * H + 3 * s : ℤ) := by
  have h4 : (Nat.totient (4 * H + s) : ℤ) ≤ (4 * H + s : ℕ) := by
    exact_mod_cast Nat.totient_le (4 * H + s)
  have h2 : (Nat.totient (2 * H + s) : ℤ) ≤ (2 * H + s : ℕ) := by
    exact_mod_cast Nat.totient_le (2 * H + s)
  have h1 : (Nat.totient (H + s) : ℤ) ≤ (H + s : ℕ) := by
    exact_mod_cast Nat.totient_le (H + s)
  have h4nonneg : 0 ≤ (Nat.totient (4 * H + s) : ℤ) := by positivity
  have h2nonneg : 0 ≤ (Nat.totient (2 * H + s) : ℤ) := by positivity
  have h1nonneg : 0 ≤ (Nat.totient (H + s) : ℤ) := by positivity
  unfold curvatureDrive
  rw [abs_le]
  constructor <;> push_cast at * <;> omega

/-- The sharp direct curvature edge radius. -/
def sharpCurvatureRadius (H L : ℕ) : ℤ := 6 * H + 3 * L + 3

/-- For a positive starting index, the elementary totient tail bound improves
from `R_M <= M + 2` to `R_M <= M + 1`, using `phi(n) <= n - 1` termwise. -/
lemma totientTail_le_succ (M : ℕ) (hM : 1 ≤ M) :
    totientTail M ≤ (M : ℝ) + 1 := by
  have hterms := summable_totientTail_terms M
  have hconst : Summable (fun j : ℕ => (M : ℝ) * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (M : ℝ)
  have hlin : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)
  have hgeo : Summable (fun j : ℕ => (((M : ℝ) + j) / 2 ^ (j + 1))) := by
    have hadd := hconst.add hlin
    exact (hadd.mul_right (1 / 2 : ℝ)).congr (fun j => by
      rw [div_pow, one_pow, pow_succ]
      ring)
  have hle : ∀ j : ℕ,
      (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1)
        ≤ ((M : ℝ) + j) / 2 ^ (j + 1) := by
    intro j
    have harg : 1 < M + 1 + j := by omega
    have hphi : Nat.totient (M + 1 + j) ≤ M + j := by
      have := Nat.totient_lt (M + 1 + j) harg
      omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast hphi) (by positivity)
  have hsum := Summable.tsum_le_tsum hle hterms hgeo
  have hconstsum : (∑' j : ℕ, (M : ℝ) * (1 / 2 : ℝ) ^ j) = 2 * M := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)]
    ring
  have hlinsum : (∑' j : ℕ, (j : ℝ) * (1 / 2 : ℝ) ^ j) = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs]; norm_num)]
    norm_num
  have hmajorant :
      (∑' j : ℕ, ((M : ℝ) + j) / 2 ^ (j + 1)) = (M : ℝ) + 1 := by
    calc
      (∑' j : ℕ, ((M : ℝ) + j) / 2 ^ (j + 1))
          = ∑' j : ℕ, (((M : ℝ) * (1 / 2 : ℝ) ^ j +
              (j : ℝ) * (1 / 2 : ℝ) ^ j) * (1 / 2)) := by
            apply tsum_congr
            intro j
            rw [div_pow, one_pow, pow_succ]
            ring
      _ = (∑' j : ℕ, ((M : ℝ) * (1 / 2 : ℝ) ^ j +
              (j : ℝ) * (1 / 2 : ℝ) ^ j)) * (1 / 2) := tsum_mul_right
      _ = ((∑' j : ℕ, (M : ℝ) * (1 / 2 : ℝ) ^ j) +
              ∑' j : ℕ, (j : ℝ) * (1 / 2 : ℝ) ^ j) * (1 / 2) := by
            rw [Summable.tsum_add hconst hlin]
      _ = (M : ℝ) + 1 := by rw [hconstsum, hlinsum]; ring
  calc
    totientTail M
        ≤ ∑' j : ℕ, ((M : ℝ) + j) / 2 ^ (j + 1) := hsum
    _ = (M : ℝ) + 1 := hmajorant

/-- Exact curvature prefix/tail split. -/
theorem two_pow_mul_curvature_eq_window_add_shifted (H L : ℕ) :
    (2 : ℝ) ^ L * curvatureTail H =
      (curvatureWindow H L : ℝ) + curvatureShiftedTail H L := by
  have htop := windowDiscrepancy_div_eq (2 * H) (2 * H) L
  have hbot := windowDiscrepancy_div_eq H H L
  have h4 := totientTail_eq_partial_add_shifted (4 * H) L
  have h2 := totientTail_eq_partial_add_shifted (2 * H) L
  have h1 := totientTail_eq_partial_add_shifted H L
  have hpow : (0 : ℝ) < 2 ^ L := by positivity
  unfold curvatureTail curvatureWindow curvatureShiftedTail
  push_cast
  rw [show 2 * H + 2 * H = 4 * H by ring] at htop
  rw [show H + H = 2 * H by ring] at hbot
  rw [h4, h2, h1]
  field_simp [hpow.ne'] at htop hbot ⊢
  linarith

/-- The direct shifted curvature tail lies in the sharp symmetric strip. -/
theorem abs_curvatureShiftedTail_le (H L : ℕ) (hH : 1 ≤ H) :
    |curvatureShiftedTail H L| ≤ (sharpCurvatureRadius H L : ℝ) := by
  have h4p := totientTail_pos (4 * H + L)
  have h2p := totientTail_pos (2 * H + L)
  have h1p := totientTail_pos (H + L)
  have h4u := totientTail_le_succ (4 * H + L) (by omega)
  have h2u := totientTail_le_succ (2 * H + L) (by omega)
  have h1u := totientTail_le_succ (H + L) (by omega)
  unfold curvatureShiftedTail sharpCurvatureRadius
  push_cast at h4u h2u h1u ⊢
  rw [abs_le]
  constructor <;> linarith

/-- The direct residue-gap certificate for curvature. -/
def sharpCurvatureCert (H L : ℕ) : Prop :=
  sharpCurvatureRadius H L < curvatureWindow H L % 2 ^ L ∧
    curvatureWindow H L % 2 ^ L < 2 ^ L - sharpCurvatureRadius H L

instance (H L : ℕ) : Decidable (sharpCurvatureCert H L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A sharp curvature residue gap directly excludes integral curvature. -/
theorem curvature_notMem_int_of_sharpCurvatureCert {H L : ℕ} (hH : 1 ≤ H)
    (hcert : sharpCurvatureCert H L) :
    curvatureTail H ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨k, hk⟩
  obtain ⟨hlow, hhigh⟩ := hcert
  have hsplit := two_pow_mul_curvature_eq_window_add_shifted H L
  have htail := abs_curvatureShiftedTail_le H L hH
  set A : ℤ := curvatureWindow H L
  set P : ℤ := 2 ^ L
  set B : ℤ := sharpCurvatureRadius H L
  have hPpos : 0 < P := by simp [P]
  have hclose : |A - k * P| ≤ B := by
    have heq : ((A - k * P : ℤ) : ℝ) = -curvatureShiftedTail H L := by
      rw [← hk] at hsplit
      change (2 : ℝ) ^ L * (k : ℝ) = (A : ℝ) + curvatureShiftedTail H L at hsplit
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

/-- The unbounded direct-curvature certificate supply. -/
def SharpCurvatureSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ sharpCurvatureCert (periodLcm t) (Nat.log2 (periodLcm t) + 10)

/-- The depth need not be tied to the old LCM height.  This is the correct
consumer for a phase-separation certificate found later in a successor block. -/
def SharpCurvatureAnyDepthSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t L, t₀ ≤ t ∧ sharpCurvatureCert (periodLcm t) L

/-- The sharp curvature supply is a complete proof socket for #249. -/
theorem irrational_totientSeries_of_sharpCurvatureSupply
    (hsupply : SharpCurvatureSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨t, ht, hcert⟩ := hsupply (max t₁ 1)
  have ht₁ : t₁ ≤ t := (le_max_left _ _).trans ht
  have htpos : 1 ≤ t := (le_max_right _ _).trans ht
  obtain ⟨a, ha⟩ := hflat t ht₁ 1 1 (by omega)
  obtain ⟨b, hb⟩ := hflat t ht₁ 2 2 (by omega)
  have hHpos : 1 ≤ periodLcm t := periodLcm_pos t
  apply curvature_notMem_int_of_sharpCurvatureCert hHpos hcert
  refine ⟨b - 2 * a, ?_⟩
  unfold curvatureTail
  push_cast
  have htwo : periodLcm t + periodLcm t = 2 * periodLcm t := by omega
  have hfour : 2 * periodLcm t + 2 * periodLcm t = 4 * periodLcm t := by omega
  norm_num at ha hb
  rw [htwo] at ha
  rw [hfour] at hb
  have ha' : (a : ℝ) = totientTail (2 * periodLcm t) - totientTail (periodLcm t) := by
    exact ha
  have hb' : (b : ℝ) = totientTail (4 * periodLcm t) - totientTail (2 * periodLcm t) := by
    exact hb
  linarith [ha', hb']

/-- Arbitrarily large sharp curvature certificates at arbitrary depths still
contradict the same LCM-cone flatness conclusion. -/
theorem irrational_totientSeries_of_sharpCurvatureAnyDepthSupply
    (hsupply : SharpCurvatureAnyDepthSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨t, L, ht, hcert⟩ := hsupply (max t₁ 1)
  have ht₁ : t₁ ≤ t := (le_max_left _ _).trans ht
  have htpos : 1 ≤ t := (le_max_right _ _).trans ht
  obtain ⟨a, ha⟩ := hflat t ht₁ 1 1 (by omega)
  obtain ⟨b, hb⟩ := hflat t ht₁ 2 2 (by omega)
  have hHpos : 1 ≤ periodLcm t := periodLcm_pos t
  apply curvature_notMem_int_of_sharpCurvatureCert hHpos hcert
  refine ⟨b - 2 * a, ?_⟩
  unfold curvatureTail
  push_cast
  have htwo : periodLcm t + periodLcm t = 2 * periodLcm t := by omega
  have hfour : 2 * periodLcm t + 2 * periodLcm t = 4 * periodLcm t := by omega
  norm_num at ha hb
  rw [htwo] at ha
  rw [hfour] at hb
  have ha' : (a : ℝ) = totientTail (2 * periodLcm t) - totientTail (periodLcm t) := ha
  have hb' : (b : ℝ) = totientTail (4 * periodLcm t) - totientTail (2 * periodLcm t) := hb
  linarith [ha', hb']

/-- The curvature word is an exact input-driven doubling recurrence. -/
theorem curvatureWindow_succ (H L : ℕ) :
    curvatureWindow H (L + 1) =
      2 * curvatureWindow H L + curvatureDrive H (L + 1) := by
  unfold curvatureWindow curvatureDrive
  rw [windowDiscrepancy_succ, windowDiscrepancy_succ]
  unfold deltaTotient
  ring_nf

/-- Exact affine curvature orbit launched at depth `m`. -/
def curvatureCarryOrbit (H m : ℕ) (e : ℤ) : ℕ → ℤ
  | 0 => e
  | j + 1 => 2 * curvatureCarryOrbit H m e j + curvatureDrive H (m + j + 1)

/-- An entering phase remains inside the sharp corridor throughout a block. -/
def curvatureBlockLocked (H m r : ℕ) (e : ℤ) : Prop :=
  ∀ j, j ≤ r → |curvatureCarryOrbit H m e j| ≤ sharpCurvatureRadius H (m + j)

/-- Signed survivor fibre at one depth.  The congruence records the complete
prefix history exposed to a suffix checker. -/
def curvatureEndpointSurvivor (H L : ℕ) (e : ℤ) : Prop :=
  |e| ≤ sharpCurvatureRadius H L ∧ e % (2 : ℤ) ^ L = curvatureWindow H L % (2 : ℤ) ^ L

/-- The affine orbit starting from the genuine prefix window is exactly the
curvature window at every later depth. -/
theorem curvatureCarryOrbit_curvatureWindow (H m j : ℕ) :
    curvatureCarryOrbit H m (curvatureWindow H m) j = curvatureWindow H (m + j) := by
  induction j with
  | zero => simp [curvatureCarryOrbit]
  | succ j ih =>
      rw [curvatureCarryOrbit, ih]
      simpa [Nat.add_assoc] using (curvatureWindow_succ H (m + j)).symm

/-- Proof-valued phase-fibre certificate.  A future reflected checker may
produce this structure from exact arithmetic receipts; the final `sharp`
field is the small kernel-facing conclusion. -/
structure CurvaturePhaseCertificate (H m r : ℕ) where
  prefixPhase : ℤ
  prefixSurvivor : curvatureEndpointSurvivor H m prefixPhase
  outsideLockedPreimage : ¬ curvatureBlockLocked H m r prefixPhase
  exitOffset : ℕ
  exitOffset_le : exitOffset ≤ r
  sharp : sharpCurvatureCert H (m + exitOffset)

/-- Arbitrarily large proof-producing phase certificates. -/
def CurvaturePhaseCertificateSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t m r, t₀ ≤ t ∧
    Nonempty (CurvaturePhaseCertificate (periodLcm t) m r)

/-- Phase-certificate supply feeds the any-depth curvature consumer. -/
theorem irrational_totientSeries_of_phaseCertificateSupply
    (hsupply : CurvaturePhaseCertificateSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totientSeries_of_sharpCurvatureAnyDepthSupply
  intro t₀
  obtain ⟨t, m, r, ht, ⟨cert⟩⟩ := hsupply t₀
  exact ⟨t, m + cert.exitOffset, ht, cert.sharp⟩

/-- A denominator-free rough loss scaled by an arbitrary common carrier `g`. -/
def scaledRoughLoss (g n : ℕ) : ℤ :=
  (Nat.totient g : ℤ) * n - g * Nat.totient n

/-- The exact common-carrier identity.  No divisibility or factorisation
hypothesis is needed at this scaled level; choosing `g` as a smooth carrier
can be deferred to downstream arithmetic. -/
theorem curvatureDrive_commonCarrier (g H s : ℕ) :
    (g : ℤ) * curvatureDrive H s =
      3 * scaledRoughLoss g (2 * H + s) -
        2 * scaledRoughLoss g (H + s) -
        scaledRoughLoss g (4 * H + s) := by
  unfold curvatureDrive scaledRoughLoss
  push_cast
  ring

#print axioms curvature_notMem_int_of_sharpCurvatureCert
#print axioms irrational_totientSeries_of_sharpCurvatureSupply
#print axioms abs_curvatureDrive_le
#print axioms irrational_totientSeries_of_sharpCurvatureAnyDepthSupply
#print axioms curvatureCarryOrbit_curvatureWindow
#print axioms irrational_totientSeries_of_phaseCertificateSupply
#print axioms curvatureWindow_succ
#print axioms curvatureDrive_commonCarrier

end TotientTailPeriodKiller
end Erdos249257
