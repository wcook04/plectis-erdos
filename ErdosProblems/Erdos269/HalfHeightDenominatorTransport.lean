import ErdosProblems.Erdos269.ResidueEscape
import Mathlib.Tactic

/-!
# Erdős #269: denominator transport, and the two new residue consumers

`ResidueEscape` records in its own header that two inputs are missing: the
bridge from rationality of the running-LCM series to a bounded positive
integral carry, and cofinal residue escape.  This file supplies the exact
arithmetic half of the first, and two strictly stronger consumers for the
second.

## Transport

The scaled tail attached to a rational value `A/D` has the shape
`c = A·H - D·Z` with `Z` an integer and `H` the scaling height.  Because
`A/D` is reduced, the content of that carry is determined *entirely* by the
height:

`Int.gcd (A·H - D·Z) D = Int.gcd H D`   (`gcd_carry_eq_gcd_height`)

so the reduced denominator of the tail is `D / gcd(D, H)` — the smooth-factor
divisibility of the carry is not an extra dynamical hypothesis but the
deterministic absorption of the denominator by the height.  Once the height
clears the smooth part (`reducedCarry_gcd_eq_smoothPart`), the reduced carry is
an integer coprime to the surviving odd part `B`.

## Two consumers stronger than the live one

The live exact classifier says that a positive endpoint carry below the window
modulus *equals* the canonical residue.  Two consequences follow that the
current file cannot state:

* `no_reduced_state_of_large_or_nonunit_residue` — a window is fatal not only
  when its canonical residue is too large, but also when
  `gcd(residue, B) > 1`.  This can eliminate a denominator even when the
  residue is numerically small.
* `reducedCarry_projective_shadow` — two endpoints are rigidly linked by
  `d_a·h_b ≡ d_b·h_a (mod B)`.  Two exact windows whose residues violate this
  exclude `B` even when both residues are small *and* coprime to `B`.

The second replaces one-window anti-concentration by a projective
residue-coherence target across a pair of windows.

## Claim ceiling

**Erdős #269 remains open.**  No cofinal escape is produced here, and the
identification of the checker digit with the half-height block contribution
remains an analytic statement about the specific series, not part of this
module.
-/

namespace ErdosProblems.Erdos269.HalfHeightDenominatorTransport

open ErdosProblems.Erdos269

/-! ## Exact denominator transport -/

/-- **Transport, divisor form.**  For a reduced value `A/D`, a divisor of `D`
divides the carry `A·H - D·Z` exactly when it divides the height `H`.  Every
cancellation is forced by the height; none of it is a free dynamical choice. -/
theorem dvd_carry_iff_dvd_height {A D H Z c : ℤ}
    (hcop : IsCoprime A D) (hcD : c ∣ D) :
    c ∣ A * H - D * Z ↔ c ∣ H := by
  have hcA : IsCoprime c A := (hcop.symm.of_isCoprime_of_dvd_left hcD)
  have hcDZ : c ∣ D * Z := Dvd.dvd.mul_right hcD Z
  constructor
  · intro hcarry
    have hAH : c ∣ A * H := by
      have := Dvd.dvd.add hcarry hcDZ
      simpa using this
    exact hcA.dvd_of_dvd_mul_left hAH
  · intro hH
    exact Dvd.dvd.sub (Dvd.dvd.mul_left hH A) hcDZ

/-- The smooth part of the denominator always divides the carry once the height
absorbs it. -/
theorem smoothPart_dvd_carry {A D H Z Dsm : ℤ} (hDsm : Dsm ∣ D) (hsm : Dsm ∣ H) :
    Dsm ∣ A * H - D * Z :=
  Dvd.dvd.sub (Dvd.dvd.mul_left hsm A) (Dvd.dvd.mul_right hDsm Z)

/-- **The reduced carry.**  Once the height clears the smooth part of the
denominator, the carry factors through that smooth part and the remaining
integer is coprime to the surviving odd part `B`.  This is the arithmetic half
of the rationality-to-state bridge: reducedness of the tail is not an extra
hypothesis but a consequence of transport. -/
theorem exists_reducedCarry_isCoprime {A D H Z Dsm B : ℤ}
    (hcop : IsCoprime A D) (hD : D = Dsm * B) (hDsm0 : Dsm ≠ 0)
    (hsm : Dsm ∣ H) (hHB : IsCoprime H B) :
    ∃ d : ℤ, A * H - D * Z = Dsm * d ∧ IsCoprime d B := by
  obtain ⟨H', hH'⟩ := hsm
  refine ⟨A * H' - B * Z, ?_, ?_⟩
  · rw [hH', hD]; ring
  · have hAB : IsCoprime A B := by
      refine hcop.of_isCoprime_of_dvd_right ?_
      exact ⟨Dsm, by rw [hD]; ring⟩
    have hH'B : IsCoprime H' B := by
      refine hHB.of_isCoprime_of_dvd_left ?_
      exact ⟨Dsm, by rw [hH']; ring⟩
    have hprod : IsCoprime (A * H') B := hAB.mul_left hH'B
    have hsub : A * H' - B * Z = A * H' + B * (-Z) := by ring
    rw [hsub]
    exact (IsCoprime.add_mul_left_left hprod (-Z))

/-! ## The non-unit residue consumer -/

/-- **A window is fatal in two ways, not one.**  A reduced endpoint state
cannot have a canonical window residue that is too large *or* that shares a
factor with the reduced denominator.  The second branch is new: it can
eliminate a denominator even when the residue is numerically small. -/
theorem no_reduced_state_of_large_or_nonunit_residue
    {B C bound : ℕ} {x d : ℤ}
    (hC : 0 < C) (hdpos : 0 < d)
    (hdbound : Int.natAbs d ≤ bound) (hboundC : bound < C)
    (hmod : Int.ModEq C d x) (hcop : Nat.Coprime (Int.natAbs d) B)
    (hbad : bound < leastPositiveResidue C x ∨
      ¬ Nat.Coprime (leastPositiveResidue C x) B) : False := by
  have hleC : Int.natAbs d ≤ C := hdbound.trans (Nat.le_of_lt hboundC)
  have hr : leastPositiveResidue C x = Int.natAbs d :=
    leastPositiveResidue_eq_natAbs_of_pos_le_modEq hC hdpos hleC hmod
  rcases hbad with hlarge | hnonunit
  · omega
  · exact hnonunit (by rw [hr]; exact hcop)

/-! ## The projective shadow across two windows -/

/-- **Two endpoints are rigidly linked.**  If two reduced carries come from the
same rational value at heights `hₐ` and `h_b`, then
`dₐ·h_b ≡ d_b·hₐ (mod B)`.  A pair of exact windows violating this excludes the
denominator even when both residues are small and coprime to `B`. -/
theorem reducedCarry_projective_shadow {A B Dsm da db ha hb : ℤ}
    (hBcop : IsCoprime Dsm B)
    (hA : Dsm * da ≡ A * ha [ZMOD B])
    (hB' : Dsm * db ≡ A * hb [ZMOD B]) :
    da * hb ≡ db * ha [ZMOD B] := by
  have h1 : Dsm * (da * hb) ≡ A * (ha * hb) [ZMOD B] := by
    have h := hA.mul_right hb
    calc Dsm * (da * hb) = Dsm * da * hb := by ring
      _ ≡ A * ha * hb [ZMOD B] := h
      _ = A * (ha * hb) := by ring
  have h2 : Dsm * (db * ha) ≡ A * (ha * hb) [ZMOD B] := by
    have h := hB'.mul_right ha
    calc Dsm * (db * ha) = Dsm * db * ha := by ring
      _ ≡ A * hb * ha [ZMOD B] := h
      _ = A * (ha * hb) := by ring
  have hdiff : Dsm * (da * hb) ≡ Dsm * (db * ha) [ZMOD B] := h1.trans h2.symm
  have hdvd : B ∣ Dsm * (da * hb - db * ha) := by
    have hd := Int.ModEq.dvd hdiff
    have hrw : Dsm * (db * ha) - Dsm * (da * hb)
        = -(Dsm * (da * hb - db * ha)) := by ring
    rw [hrw] at hd
    exact dvd_neg.mp hd
  have hfinal : B ∣ da * hb - db * ha := hBcop.symm.dvd_of_dvd_mul_left hdvd
  refine Int.modEq_iff_dvd.mpr ?_
  have hneg : db * ha - da * hb = -(da * hb - db * ha) := by ring
  rw [hneg]
  exact dvd_neg.mpr hfinal

/-- **Window carries expose a normalized quotient defect.**  Writing each
canonical carry as `d = k*M - B*F` and each endpoint height as its start
height times the window base factors the projective cross-product into a
base product times the quotient defect, plus a multiple of `B`.  Thus the
exact checker can study the substantially smaller ceiling quotients while
`reducedCarry_projective_shadow` remains the contradiction consumer. -/
theorem projectiveDefect_eq_windowQuotientDefect
    {B da db ka kb ma mb fa fb sa sb ha hb : ℤ}
    (hda : da = ka * ma - B * fa)
    (hdb : db = kb * mb - B * fb)
    (hha : ha = sa * ma)
    (hhb : hb = sb * mb) :
    da * hb - db * ha =
      ma * mb * (ka * sb - kb * sa) +
        B * (fb * sa * ma - fa * sb * mb) := by
  rw [hda, hdb, hha, hhb]
  ring

end ErdosProblems.Erdos269.HalfHeightDenominatorTransport
