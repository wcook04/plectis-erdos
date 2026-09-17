import ErdosProblems.Erdos243.PrimitiveRecordBarrier
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Erdős 243: saturated square transport across one primitive cancellation

This module formalises return `r04` Proposition 1 ("saturated square
transport") and its Legendre-defect corollary `r04 (13)`, together with
`r04` Lemma 2 (the record-amplified error after a cancellation).

## What is saturated here

The corpus lemma `S1` transports the centred-error product only modulo `d_n`,
the largest divisor of `u (n+1)` coprime to the removed content `G (n+1)`.
The statements below are strictly stronger: they transport modulo the
**whole** next numerator `u'`, with the *full* content removed.

`saturated_square_transport_raw` does this with **no hypothesis at all** beyond
the two cocycle equations: `u' ∣ hc * e * e' - v ^ 2`.  That already saturates
`S1`.  The normalised forms additionally use the exact square-cancellation
normal form of `DynamicCancellation` (`rawNext_gcd_exact_overlap`,
`cancellationOverlap_normalForm_explicit`,
`cancellation_denominator_transport_explicit`), which writes one primitive
step as

* `a  = b * c * ℓ`,
* `v  = b * c * s`,
* `hc = b * c ^ 2`,
* `v' = b * ℓ * s`,

so that the removed content `hc` and the raw numerator `w = hc * u'` share the
*same* square factor `b * c ^ 2` that appears in `v ^ 2`.  Cancelling it is
exact, and no coprimality-to-`G` hypothesis survives.

## The two orientation identities

Both are pure ring identities from the cocycle, with no sign or size side
condition:

* `(v : ℤ) - a * e = (a - 1) * w`, i.e. `a * e ≡ v (mod w)`;
* `hc * e' = a * v - (a' - 1) * w`, i.e. `hc * e' ≡ a * v (mod w)`.

Multiplying and using `a * u = w + v` to remove the spurious `a` gives the
*exact* identity `hc * e * e' - v ^ 2 = w * κ` for an explicit integer `κ`
(`squareTransport_core_identity`), which is the whole content of the
proposition.  Everything else is bookkeeping.

## Limitation, recorded deliberately

The congruence `b * e * e' ≡ (b * s) ^ 2 (mod u')` is blind to a *pure square*
payment.  If `b = 1` — that is, `hc = c ^ 2` — then the congruence degenerates
to `e * e' ≡ s ^ 2`, which carries no quadratic-character information at all.
Quadratic-character counting can therefore never detect square deletion, and
`legendre_defect_forces_nonsquare_content` correspondingly only obstructs
`b = 1`, never `hc = 1` and never a square `hc`.

Claim ceiling: Erdős #243 remains open.  Nothing here bounds the cancellation
factors or the orbit.
-/

namespace ErdosProblems.Erdos243

/-! ## 1. The multiplier/raw-numerator gcd is the multiplier/denominator gcd

A one-line consequence of the cocycle, needed to manufacture the normal-form
factors in the gcd-level wrapper. -/

/-- On a primitive step, `gcd (a, w) = gcd (a, v)`: the raw numerator and the
reduced denominator have the same overlap with the multiplier. -/
theorem gcd_multiplier_rawNumerator
    {a u v w : ℕ} (hq : w + v = a * u) :
    Nat.gcd a w = Nat.gcd a v := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left a w)
    have hkA : Nat.gcd a w ∣ a := Nat.gcd_dvd_left a w
    have hkW : Nat.gcd a w ∣ w := Nat.gcd_dvd_right a w
    have hkSum : Nat.gcd a w ∣ w + v := by
      rw [hq]; exact dvd_mul_of_dvd_left hkA u
    exact (Nat.dvd_add_iff_right hkW).mpr hkSum
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left a v)
    have hkA : Nat.gcd a v ∣ a := Nat.gcd_dvd_left a v
    have hkV : Nat.gcd a v ∣ v := Nat.gcd_dvd_right a v
    have hkSum : Nat.gcd a v ∣ w + v := by
      rw [hq]; exact dvd_mul_of_dvd_left hkA u
    exact (Nat.dvd_add_iff_left hkV).mpr hkSum

/-! ## 2. Saturated square transport (r04 Proposition 1) -/

/-- **Core exact transport identity.**  Multiplying the two orientation
identities `e = u - w` and `hc * e' = a * v - (a' - 1) * w`, then using
`a * u = w + v` to clear the spurious factor `a`, gives an *exact*
factorisation of the square defect through the raw numerator `w`.

No positivity, coprimality, primitivity or normal-form hypothesis is used, and
the next multiplier `a'` is arbitrary. -/
theorem squareTransport_core_identity
    {a u v w hc u' v' : ℕ} {a' e e' : ℤ}
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (he : e = (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ))
    (he' : e' = (v' : ℤ) - (a' - 1) * (u' : ℤ)) :
    (hc : ℤ) * e * e' - (v : ℤ) ^ 2 =
      (w : ℤ) * ((v : ℤ) - (u : ℤ) * (a' - 1) - (a : ℤ) * (v : ℤ)
        + (a' - 1) * (w : ℤ)) := by
  have hqZ : (w : ℤ) + (v : ℤ) = (a : ℤ) * (u : ℤ) := by exact_mod_cast hq
  have hnumZ : (w : ℤ) = (hc : ℤ) * (u' : ℤ) := by exact_mod_cast hnum
  have hdenZ : (a : ℤ) * (v : ℤ) = (hc : ℤ) * (v' : ℤ) := by exact_mod_cast hden
  have heU : e = (u : ℤ) - (w : ℤ) := by rw [he]; exact primitiveError_eq_sub hq
  have hce' : (hc : ℤ) * e' = (a : ℤ) * (v : ℤ) - (a' - 1) * (w : ℤ) := by
    rw [he', hnumZ, hdenZ]; ring
  have hav : (a : ℤ) * (u : ℤ) * (v : ℤ) = ((w : ℤ) + (v : ℤ)) * (v : ℤ) := by
    rw [hqZ]
  have hsplit : (hc : ℤ) * e * e' = e * ((hc : ℤ) * e') := by ring
  rw [hsplit, hce', heU]
  linear_combination hav

/-- **Saturated square transport, unnormalised form.**  The whole next reduced
numerator `u'` divides `hc * e * e' - v ^ 2`.

This is already strictly stronger than the corpus lemma `S1`, which transports
only modulo `d_n`, the largest divisor of `u (n+1)` coprime to the removed
content `G (n+1)` (see the `research_packet.json` row "Unconditional primitive
square transport and the Legendre defect charge").  Here the modulus is `u'`
itself, and the statement carries no hypothesis beyond the two cocycle
equations and the definitions of the two centred errors — no primitivity, no
positivity, no coprimality, no cleanliness. -/
theorem saturated_square_transport_raw
    {a u v w hc u' v' : ℕ} {a' e e' : ℤ}
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (he : e = (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ))
    (he' : e' = (v' : ℤ) - (a' - 1) * (u' : ℤ)) :
    (u' : ℤ) ∣ (hc : ℤ) * e * e' - (v : ℤ) ^ 2 := by
  have hnumZ : (w : ℤ) = (hc : ℤ) * (u' : ℤ) := by exact_mod_cast hnum
  refine ⟨(hc : ℤ) * ((v : ℤ) - (u : ℤ) * (a' - 1) - (a : ℤ) * (v : ℤ)
    + (a' - 1) * (w : ℤ)), ?_⟩
  rw [squareTransport_core_identity hq hnum hden he he', hnumZ]
  ring

/-- **Saturated square transport (explicit factors).**

One primitive step with the *full* content `hc` removed, written in the exact
square-cancellation normal form `a = b*c*ℓ`, `v = b*c*s`, `hc = b*c^2`.  With
the centred errors `e = v - (a-1)u` and `e' = v' - (a'-1)u'` (for an arbitrary
next multiplier `a'`), the whole next numerator `u'` divides the square defect

`b * e * e' - (b * s) ^ 2`,

and `b`, `s`, `ℓ` are each coprime to `u'`.

Two remarks on the hypotheses, both strengthenings relative to the return:

* the raw-next relation for the *following* step (`w' + v' = a' * u'`) is never
  used — the successor orientation identity only needs the definition of `e'`
  and the two cocycle equations of the current step, so the conclusion holds
  for every integer `a'`;
* the transport is modulo `u'` itself, not modulo the part of `u'` coprime to
  the removed content. -/
theorem saturated_square_transport_explicit
    {a u v w hc u' v' b c ℓ s : ℕ} {a' e e' : ℤ}
    (hbpos : 0 < b) (hcpos : 0 < c)
    (ha : a = b * c * ℓ)
    (hv : v = b * c * s)
    (hh : hc = b * c ^ 2)
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (hcop' : Nat.Coprime u' v')
    (he : e = (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ))
    (he' : e' = (v' : ℤ) - (a' - 1) * (u' : ℤ)) :
    (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2 ∧
      Nat.Coprime b u' ∧ Nat.Coprime s u' ∧ Nat.Coprime ℓ u' := by
  -- Denominator transport in the explicit factors: `v' = b * ℓ * s`.
  have hbc2pos : 0 < b * c ^ 2 := Nat.mul_pos hbpos (pow_pos hcpos 2)
  have hv' : v' = b * ℓ * s := by
    apply Nat.eq_of_mul_eq_mul_left hbc2pos
    calc b * c ^ 2 * v' = a * v := by rw [← hh]; exact hden.symm
      _ = (b * c * ℓ) * (b * c * s) := by rw [ha, hv]
      _ = b * c ^ 2 * (b * ℓ * s) := by ring
  -- Integer casts of the exact normal form.
  have hnumZ : (w : ℤ) = (hc : ℤ) * (u' : ℤ) := by exact_mod_cast hnum
  have hhZ : (hc : ℤ) = (b : ℤ) * (c : ℤ) ^ 2 := by rw [hh]; push_cast; ring
  have hvZ : (v : ℤ) = (b : ℤ) * (c : ℤ) * (s : ℤ) := by rw [hv]; push_cast; ring
  have hwZ : (w : ℤ) = (b : ℤ) * (c : ℤ) ^ 2 * (u' : ℤ) := by rw [hnumZ, hhZ]
  -- The exact (non-modular) transport identity.
  obtain ⟨κ, hκ⟩ : ∃ κ : ℤ, (hc : ℤ) * e * e' - (v : ℤ) ^ 2 = (w : ℤ) * κ :=
    ⟨_, squareTransport_core_identity hq hnum hden he he'⟩
  -- Cancel the exact square factor `b * c ^ 2`.
  have hb0 : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hbpos
  have hc0 : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hcpos
  have hbcZ : ((b : ℤ) * (c : ℤ) ^ 2) ≠ 0 := ne_of_gt (mul_pos hb0 (pow_pos hc0 2))
  have hstep : e * e' - (b : ℤ) * (s : ℤ) ^ 2 = (u' : ℤ) * κ := by
    apply mul_left_cancel₀ hbcZ
    calc (b : ℤ) * (c : ℤ) ^ 2 * (e * e' - (b : ℤ) * (s : ℤ) ^ 2)
        = (hc : ℤ) * e * e' - (v : ℤ) ^ 2 := by rw [hhZ, hvZ]; ring
      _ = (w : ℤ) * κ := hκ
      _ = (b : ℤ) * (c : ℤ) ^ 2 * ((u' : ℤ) * κ) := by rw [hwZ]; ring
  refine ⟨⟨(b : ℤ) * κ, ?_⟩, ?_, ?_, ?_⟩
  · calc (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2
        = (b : ℤ) * (e * e' - (b : ℤ) * (s : ℤ) ^ 2) := by ring
      _ = (b : ℤ) * ((u' : ℤ) * κ) := by rw [hstep]
      _ = (u' : ℤ) * ((b : ℤ) * κ) := by ring
  · have h1 : Nat.Coprime u' (b * ℓ * s) := by rw [← hv']; exact hcop'
    exact (Nat.Coprime.coprime_dvd_right ⟨ℓ * s, by ring⟩ h1).symm
  · have h1 : Nat.Coprime u' (b * ℓ * s) := by rw [← hv']; exact hcop'
    exact (Nat.Coprime.coprime_dvd_right ⟨b * ℓ, by ring⟩ h1).symm
  · have h1 : Nat.Coprime u' (b * ℓ * s) := by rw [← hv']; exact hcop'
    exact (Nat.Coprime.coprime_dvd_right ⟨b * s, by ring⟩ h1).symm

/-! ## 3. Saturated square transport, gcd-level wrapper -/

/-- **Saturated square transport (gcd form).**  Only the primitive-step data
is assumed; the normal-form factors are manufactured from the gcd bookkeeping
of `DynamicCancellation`:

`d = gcd a v`, `c = gcd (w / d) d`, `b = d / c`, `ℓ = a / d`, `s = v / d`.

The hypothesis `hcop'` forces `hc` to be the *full* removed content, which is
exactly what makes the transport saturated. -/
theorem saturated_square_transport
    {a u v w hc u' v' : ℕ} {a' e e' : ℤ}
    (hvpos : 0 < v)
    (hcop : Nat.Coprime u v)
    (hcop' : Nat.Coprime u' v')
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (he : e = (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ))
    (he' : e' = (v' : ℤ) - (a' - 1) * (u' : ℤ)) :
    ∃ b c ℓ s : ℕ,
      0 < b ∧ 0 < c ∧ a = b * c * ℓ ∧ v = b * c * s ∧ hc = b * c ^ 2 ∧
        (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2 ∧
        Nat.Coprime b u' ∧ Nat.Coprime s u' ∧ Nat.Coprime ℓ u' := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.gcd a v := ⟨_, rfl⟩
  have hdpos : 0 < d := by rw [hd]; exact Nat.gcd_pos_of_pos_right a hvpos
  have hdA : d ∣ a := by rw [hd]; exact Nat.gcd_dvd_left a v
  have hdV : d ∣ v := by rw [hd]; exact Nat.gcd_dvd_right a v
  have hdSum : d ∣ w + v := by rw [hq]; exact dvd_mul_of_dvd_left hdA u
  have hdW : d ∣ w := (Nat.dvd_add_iff_left hdV).mpr hdSum
  have hgcdAW : Nat.gcd a w = d := by rw [gcd_multiplier_rawNumerator hq, hd]
  obtain ⟨α, hα⟩ : ∃ α, α = a / d := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω, ω = w / d := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = Nat.gcd ω d := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = d / c := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t, t = v / d := ⟨_, rfl⟩
  have haFac : a = d * α := by rw [hα]; exact (Nat.mul_div_cancel' hdA).symm
  have hwFac : w = d * ω := by rw [hω]; exact (Nat.mul_div_cancel' hdW).symm
  have hvFac : v = d * t := by rw [htdef]; exact (Nat.mul_div_cancel' hdV).symm
  have hαω : Nat.Coprime α ω := by
    have hgpos : 0 < Nat.gcd a w := by rw [hgcdAW]; exact hdpos
    have h := Nat.coprime_div_gcd_div_gcd hgpos
    rw [hgcdAW] at h
    rw [hα, hω]
    exact h
  have hcdvd : c ∣ d := by rw [hcdef]; exact Nat.gcd_dvd_right ω d
  have hcpos : 0 < c := by rw [hcdef]; exact Nat.gcd_pos_of_pos_right ω hdpos
  have hdbc : d = b * c := by rw [hbdef]; exact (Nat.div_mul_cancel hcdvd).symm
  have hbpos : 0 < b := by
    rw [hbdef]; exact Nat.div_pos (Nat.le_of_dvd hdpos hcdvd) hcpos
  -- `hc` is the full content removed from the raw next pair.
  have hcontent : hc = Nat.gcd w (a ^ 2) :=
    reducedStep_cancellationFactor_eq_square hcop hcop' hq hnum hden
  obtain ⟨hhFac, haFac2, _⟩ :=
    cancellationOverlap_normalForm_explicit (a := a) (w := w) (h := hc) (d := d)
      (α := α) (ω := ω) (c := c) (b := b) haFac hwFac hαω hcdef hdbc hcontent
  have hvFac2 : v = b * c * t := by rw [hvFac, hdbc]
  refine ⟨b, c, α, t, hbpos, hcpos, haFac2, hvFac2, hhFac, ?_⟩
  exact saturated_square_transport_explicit hbpos hcpos haFac2 hvFac2 hhFac hq hnum
    hden hcop' he he'

/-! ## 4. Legendre defect (r04 (13))

The square defect is invisible to a pure-square payment: see the module
docstring. -/

/-- **Legendre defect.**  For any prime (indeed any) `p` dividing the next
numerator, `b * e * e'` is a square in `ZMod p`. -/
theorem isSquare_content_defect_mod_prime
    {b s u' p : ℕ} {e e' : ℤ}
    (hdvd : (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2)
    (hpu : p ∣ u') :
    IsSquare ((b : ZMod p) * (e : ZMod p) * (e' : ZMod p)) := by
  have hpZ : (p : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2 :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hpu) hdvd
  have hzero : (((b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpZ
  refine ⟨(((b : ℤ) * (s : ℤ) : ℤ) : ZMod p), ?_⟩
  push_cast at hzero ⊢
  linear_combination hzero

/-- **The Legendre defect obstructs `b = 1`, and nothing more.**  If the
centred-error product `e * e'` is a quadratic non-residue mod an odd prime
`p ∣ u'`, then the non-square part `b` of the removed content cannot be `1`,
so the payment `hc = b * c ^ 2` is not a pure square `c ^ 2`.

This is the honest reach of `r04 (13)`: it excludes `b = 1`, i.e. it excludes
`hc` being a *pure* square, and it says nothing whatever about the size of
`hc` beyond `hc ≠ c ^ 2`. -/
theorem legendre_defect_forces_nonsquare_content
    {b s u' p : ℕ} {e e' : ℤ}
    (hdvd : (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2)
    (hpu : p ∣ u')
    (hnr : ¬ IsSquare ((e : ZMod p) * (e' : ZMod p))) :
    b ≠ 1 := by
  intro hb
  apply hnr
  have hsq := isSquare_content_defect_mod_prime hdvd hpu
  rw [hb] at hsq
  simpa using hsq

/-- Sharper Legendre form over a prime modulus: if `b` is a nonzero square in
`ZMod p` then so is `e * e'`.  Contrapositive: a non-residue `e * e'` forces
`b` to be a non-residue, hence not a perfect square in `ℕ` either. -/
theorem isSquare_error_product_of_isSquare_content
    {b s u' p : ℕ} {e e' : ℤ} [Fact (Nat.Prime p)]
    (hdvd : (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2)
    (hpu : p ∣ u')
    (hbne : (b : ZMod p) ≠ 0)
    (hbsq : IsSquare ((b : ZMod p))) :
    IsSquare ((e : ZMod p) * (e' : ZMod p)) := by
  obtain ⟨t, ht⟩ := hbsq
  obtain ⟨y, hy⟩ := isSquare_content_defect_mod_prime hdvd hpu
  have ht0 : t ≠ 0 := by
    intro h
    apply hbne
    rw [ht, h, mul_zero]
  have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
  refine ⟨y * t⁻¹, ?_⟩
  calc (e : ZMod p) * (e' : ZMod p)
      = ((e : ZMod p) * (e' : ZMod p)) * ((t * t⁻¹) * (t * t⁻¹)) := by
        rw [htt]; ring
    _ = ((b : ZMod p) * (e : ZMod p) * (e' : ZMod p)) * (t⁻¹ * t⁻¹) := by
        rw [ht]; ring
    _ = (y * y) * (t⁻¹ * t⁻¹) := by rw [hy]
    _ = (y * t⁻¹) * (y * t⁻¹) := by ring

/-- A non-square `b` makes the whole payment `hc = b * c ^ 2` a non-square in
`ℕ`.  Combined with `isSquare_error_product_of_isSquare_content` this is the
full `r04 (13)` conclusion. -/
theorem not_isSquare_payment_of_not_isSquare_content
    {b c hc : ℕ} (hcpos : 0 < c)
    (hh : hc = b * c ^ 2) (hb : ¬ IsSquare b) :
    ¬ IsSquare hc := by
  rintro ⟨k, hk⟩
  apply hb
  have hksq : b * c ^ 2 = k ^ 2 := by rw [← hh, hk]; ring
  have hdvd : c ^ 2 ∣ k ^ 2 := ⟨b, by rw [← hksq]; ring⟩
  obtain ⟨m, hm⟩ := (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp hdvd
  refine ⟨m, ?_⟩
  have hc2pos : 0 < c ^ 2 := pow_pos hcpos 2
  apply Nat.eq_of_mul_eq_mul_left hc2pos
  calc c ^ 2 * b = b * c ^ 2 := by ring
    _ = k ^ 2 := hksq
    _ = c ^ 2 * (m * m) := by rw [hm]; ring

/-! ## 5. Record-amplified error after a cancellation (r04 Lemma 2) -/

/-- **Record-amplified error after a cancellation.**

Along the orbit from `s`, suppose the centred error is nonnegative strictly
between `s` and `t` and negative at `t`.  A nonnegative centred error means
`w n ≤ u n` (because `e n = u n - w n`), and `u (n+1) ∣ w n`, so the numerator
is nonincreasing across every such step.  Hence `u t ≤ u (s+1)`, and

`u s * u t ≤ runningMax u t * |e t| * u (s + 1)`.

Read as an amplification factor, `A t := R t * m t / u t ≥ u s / u (s+1) =
hc s / (1 - e s / u s)`: the cancellation performed at step `s` is still
visible at the first later negative error.

The estimate carries **no excursion-length control**: `t - s` is unbounded by
anything here, so this does not by itself convert a single large payment into
a record. -/
theorem recordAmplified_error_after_cancellation
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (s t : ℕ)
    (hst : s + 1 ≤ t)
    (he : ∀ n, s ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnonneg : ∀ j, s < j → j < t → 0 ≤ e j)
    (hneg : e t < 0) :
    u t ≤ u (s + 1) ∧
      u s * u t ≤ runningMax u t * (e t).natAbs * u (s + 1) := by
  have hmono : ∀ k, s + 1 ≤ k → k ≤ t → u k ≤ u (s + 1) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ m hm ih =>
        intro hmt
        have hprev : u m ≤ u (s + 1) := ih (by omega)
        have hms : s ≤ m := by omega
        have hE : e m = (u m : ℤ) - (w m : ℤ) := by
          rw [he m hms]; exact primitiveError_eq_sub (hw m hms)
        have h0 : 0 ≤ e m := hnonneg m (by omega) (by omega)
        rw [hE] at h0
        have hwu : w m ≤ u m := by exact_mod_cast (by linarith : (w m : ℤ) ≤ (u m : ℤ))
        have hdvd : u (m + 1) ∣ w m := ⟨hc m, by rw [hnum m hms]; ring⟩
        have hle : u (m + 1) ≤ w m := Nat.le_of_dvd (hwpos m hms) hdvd
        omega
  have hut : u t ≤ u (s + 1) := hmono t hst le_rfl
  refine ⟨hut, ?_⟩
  have hRs : u s ≤ runningMax u t := le_runningMax u (by omega)
  have habs : 0 < (e t).natAbs := Int.natAbs_pos.mpr (ne_of_lt hneg)
  calc u s * u t ≤ runningMax u t * u (s + 1) := Nat.mul_le_mul hRs hut
    _ ≤ runningMax u t * (e t).natAbs * u (s + 1) :=
        Nat.mul_le_mul (Nat.le_mul_of_pos_right _ habs) le_rfl

end ErdosProblems.Erdos243
