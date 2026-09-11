import ErdosProblems.DemandLedger.Basic
open Erdos249257 Erdos249257.TotientTailPeriodKiller
namespace DemandLedger.ClusterC

/-!
# Cluster C: the totient-tail non-integrality supplies

Two gaps, both stated with no certificate vocabulary at all — pure
non-integrality of `totientTail` differences on the lcm lattice.

* `G093` (diagonal): `∀ t₀, ∃ t ≥ t₀,  R_{H_t + H_t} - R_{H_t} ∉ ℤ`
* `G101` (cone):     `∀ t₀, ∃ t ≥ t₀, ∃ q m, 0 < q,  R_{qH_t + mH_t} - R_{qH_t} ∉ ℤ`

with `H_t = periodLcm t = lcm(1,…,t)` and `R = totientTail`.

The diagonal is the cell `q = m = 1` of the cone, so `G093 → G101` and `G101`
is the weaker of the two.
-/

/-- **Cluster C edge.**  The diagonal non-integrality supply is literally the
`q = m = 1` cell of the cone non-integrality supply:
`1 * periodLcm t + 1 * periodLcm t` reduces to `periodLcm t + periodLcm t`.
So `G093` is the stronger demand and `G101` the weaker one — `G101` is the
gap to attack, since discharging it discharges nothing above but is implied
by everything on the diagonal. -/
theorem e_G093_G101 : G093 → G101 := by
  unfold G093 G101
  intro h t₀
  obtain ⟨t, ht, hkill⟩ := h t₀
  refine ⟨t, ht, 1, 1, Nat.one_pos, ?_⟩
  rw [one_mul]
  exact hkill

/-- **The cofinality quantifier in `G101` is vacuous.**  Cone kills are
inherited *downward* in scale: `periodLcm t ∣ periodLcm u` for `t ≤ u`, so a
cone cell `(q, m)` at scale `u` is the cone cell `(qc, mc)` at scale `t`,
where `c = H_u / H_t`.  Hence `G101` is equivalent to demanding a cone kill at
*every* scale, with no "arbitrarily large `t`" content.

This is the structural obstruction to the reverse edge `G101 → G093`:
`G101` carries no cofinality information to spend, while `G093` names one
single point `(H_t, H_t)` per scale and genuinely needs infinitely many of
them.  Re-indexing the scale cannot manufacture the diagonal cell, because the
diagonal cells `(q, m) = (c, c)` with `c = H_u/H_t` are a measure-zero
sub-family of the cone cells. -/
theorem G101_iff_forall_scale :
    G101 ↔ ∀ t : ℕ, ∃ q m : ℕ, 0 < q ∧
      totientTail (q * periodLcm t + m * periodLcm t)
        - totientTail (q * periodLcm t) ∉ Set.range ((↑) : ℤ → ℝ) := by
  unfold G101
  constructor
  · intro h t
    obtain ⟨u, hu, q, m, hq, hkill⟩ := h t
    obtain ⟨c, hc⟩ := periodLcm_dvd_periodLcm hu
    have hupos : 0 < periodLcm u := periodLcm_pos u
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · rw [Nat.mul_zero] at hc; omega
      · exact hpos
    refine ⟨q * c, m * c, Nat.mul_pos hq hcpos, ?_⟩
    have h1 : q * c * periodLcm t = q * periodLcm u := by rw [hc]; ring
    have h2 : m * c * periodLcm t = m * periodLcm u := by rw [hc]; ring
    rw [h1, h2]
    exact hkill
  · intro h t₀
    obtain ⟨q, m, hq, hkill⟩ := h t₀
    exact ⟨t₀, le_rfl, q, m, hq, hkill⟩

/-- The sharpened form of the edge: `G093` supplies a cone kill at **every**
scale, not merely at cofinally many.  (Immediate from `e_G093_G101` and
`G101_iff_forall_scale`; recorded because it is the statement one actually
wants when feeding the cone machinery.) -/
theorem G093_gives_cone_kill_at_every_scale (h : G093) :
    ∀ t : ℕ, ∃ q m : ℕ, 0 < q ∧
      totientTail (q * periodLcm t + m * periodLcm t)
        - totientTail (q * periodLcm t) ∉ Set.range ((↑) : ℤ → ℝ) :=
  G101_iff_forall_scale.mp (e_G093_G101 h)

end DemandLedger.ClusterC
