import Mathlib.Data.Nat.Choose.Factorization
import Erdos257PeriodNoncollapse.DiagonalPincerDecomposition
import Erdos257PeriodNoncollapse.LcmConeNonflat
import Erdos257PeriodNoncollapse.LcmFactorIdealPulseObstruction
import Erdos257PeriodNoncollapse.RepunitMobiusNumerator

/-!
# Diagonal fresh-loss bridge

This module connects the operational binary window at the two LCM vertices
`[1, 2]` to the constitutional full-target pincer.  The certificate itself is
the existing one-sided cone certificate; the point of this file is the direct
consumer theorem

`diagonalFreshLossProjectionCert t L ->
  not ForeignDiagonalDefectHitsFullTarget t`.

The bridge is denominator-free.  It does not claim an avoidance supply and it
does not identify the foreign defect with a fresh-prime loss series.  That
analytic representation remains a separate theorem-development lane.  What is
proved here is that the exact `[1, 2]` binary projection is already the right
finite consumer for the full reduced target.  The adjacent-suffix route is
further reduced to centrality of one canonical depth at arbitrarily large LCM
heights (or just at strict LCM jumps); the guard-bit width is automatic.
-/

namespace Erdos257PeriodNoncollapse.DiagonalFreshLossBridge

open scoped BigOperators
open TotientTailPeriodKiller
open DiagonalPincerDecomposition

/-- The exact two-vertex operational projection at the LCM height `H_t`.

For this menu, the two rows of `coneNonflatCert` are precisely the asymmetric
safe-interval test on the residue of
`windowNumerator (2 * H_t) L - windowNumerator H_t L`. -/
def diagonalFreshLossProjectionCert (t L : ℕ) : Prop :=
  coneNonflatCert (periodLcm t) L [1, 2]

instance (t L : ℕ) : Decidable (diagonalFreshLossProjectionCert t L) :=
  inferInstanceAs (Decidable (coneNonflatCert (periodLcm t) L [1, 2]))

/-- The signed depth-`L` binary window residue on the diagonal pair. -/
def diagonalWindowResidue (t L : ℕ) : ℤ :=
  ((windowNumerator (2 * periodLcm t) L : ℤ) -
    (windowNumerator (periodLcm t) L : ℤ)) % 2 ^ L

/-- The explicit asymmetric safe interval for the diagonal residue.  This is
the denominator-free form of the finite full-target certificate. -/
def diagonalFreshLossResidueCert (t L : ℕ) : Prop :=
  (periodLcm t + L + 2 : ℤ) < diagonalWindowResidue t L ∧
    diagonalWindowResidue t L < 2 ^ L - (2 * periodLcm t + L + 2)

/-- Symmetric strengthening of the diagonal residue band.  Unlike the
one-sided fresh-loss certificate, this keeps two full LCM heights clear on
both edges.  The actual-LCM arithmetic surface identifies this predicate
with its short arithmetic kill. -/
def diagonalSymmetricResidueCert (t L : ℕ) : Prop :=
  (2 * periodLcm t + L + 2 : ℤ) < diagonalWindowResidue t L ∧
    diagonalWindowResidue t L < 2 ^ L - (2 * periodLcm t + L + 2)

instance (t L : ℕ) : Decidable (diagonalFreshLossResidueCert t L) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (t L : ℕ) : Decidable (diagonalSymmetricResidueCert t L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- On the two-vertex menu, the generic cone certificate is exactly the
asymmetric residue-safe interval.  This pins the operational shape used by
the diagnostic probe to a kernel theorem rather than a comment-level analogy. -/
theorem diagonalFreshLossResidueCert_iff_projectionCert (t L : ℕ) :
    diagonalFreshLossResidueCert t L ↔
      diagonalFreshLossProjectionCert t L := by
  let H := periodLcm t
  let P1 : ℤ := windowNumerator H L
  let P2 : ℤ := windowNumerator (2 * H) L
  let W : ℤ := P2 - P1
  let M : ℤ := 2 ^ L
  have hMpos : 0 < M := by simp [M]
  constructor
  · intro hres
    have hleft : (H + L + 2 : ℤ) < W % M := by
      simpa [diagonalFreshLossResidueCert, diagonalWindowResidue, H, P1, P2, W, M]
        using hres.1
    have hright : W % M < M - (2 * H + L + 2) := by
      simpa [diagonalFreshLossResidueCert, diagonalWindowResidue, H, P1, P2, W, M]
        using hres.2
    have hWpos : 0 < W % M := by omega
    have hMnotDvdW : ¬M ∣ W := by
      intro hdvd
      rw [Int.emod_eq_zero_of_dvd hdvd] at hWpos
      omega
    intro qi hqi
    simp at hqi
    rcases hqi with rfl | rfl
    · refine ⟨2, by simp, ?_⟩
      have hneg : (2 * H + L + 2 : ℤ) < (P1 - P2) % M := by
        rw [show P1 - P2 = -W by simp [W], Int.neg_emod,
          if_neg hMnotDvdW]
        rw [Int.natAbs_of_nonneg hMpos.le]
        omega
      simpa [H, P1, P2, M] using hneg
    · refine ⟨1, by simp, ?_⟩
      simpa [H, P1, P2, W, M] using hleft
  · intro hcert
    have hrow2 := hcert 2 (by simp)
    obtain ⟨qj, hqj, hgap2⟩ := hrow2
    simp at hqj
    have hleft : (H + L + 2 : ℤ) < W % M := by
      rcases hqj with rfl | rfl
      · simpa [W] using hgap2
      · exfalso
        have : (2 * H + L + 2 : ℤ) < 0 := by
          simpa [H, P2, M] using hgap2
        omega
    have hWpos : 0 < W % M := by omega
    have hMnotDvdW : ¬M ∣ W := by
      intro hdvd
      rw [Int.emod_eq_zero_of_dvd hdvd] at hWpos
      omega
    have hrow1 := hcert 1 (by simp)
    obtain ⟨qj, hqj, hgap1⟩ := hrow1
    simp at hqj
    have hright : W % M < M - (2 * H + L + 2) := by
      rcases hqj with rfl | rfl
      · exfalso
        have : (H + L + 2 : ℤ) < 0 := by
          simpa [H, P1, M] using hgap1
        omega
      · have hgap1' : (2 * H + L + 2 : ℤ) < (P1 - P2) % M := by
          simpa [H, P1, P2, M] using hgap1
        rw [show P1 - P2 = -W by simp [W], Int.neg_emod,
          if_neg hMnotDvdW] at hgap1'
        rw [Int.natAbs_of_nonneg hMpos.le] at hgap1'
        omega
    constructor
    · simpa [diagonalFreshLossResidueCert, diagonalWindowResidue, H, P1, P2, W, M]
        using hleft
    · simpa [diagonalFreshLossResidueCert, diagonalWindowResidue, H, P1, P2, W, M]
        using hright

/-- A firing exact `[1, 2]` projection misses the complete reduced pincer
target.  Only the largest one-sided floor is needed; the `q = 1` floor follows
from it.

This is the proof-bearing composition seam between the cone/window owner and
the complement-free pincer owner. -/
theorem foreignDiagonalDefect_misses_fullTarget_of_projectionCert
    {t L : ℕ}
    (hfloor : (2 * periodLcm t + L + 2 : ℤ) < 2 ^ L)
    (hcert : diagonalFreshLossProjectionCert t L) :
    ¬ForeignDiagonalDefectHitsFullTarget t := by
  have hfloorAll : ∀ q ∈ ([1, 2] : List ℕ),
      (q * periodLcm t + L + 2 : ℤ) < 2 ^ L := by
    intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · omega
    · exact hfloor
  have hdiag :
      diagonalTailDifference t ∉ Set.range ((↑) : ℤ → ℝ) := by
    intro hint
    obtain ⟨qi, hqi, qj, hqj, hnon⟩ :=
      exists_nonintegral_pair_of_coneNonflatCert
        (H := periodLcm t) (L := L) (Q := [1, 2])
        (by simp) hfloorAll hcert
    simp at hqi hqj
    apply hnon
    rcases hqi with rfl | rfl <;> rcases hqj with rfl | rfl
    · exact ⟨0, by simp⟩
    · simpa [diagonalTailDifference, two_mul] using hint
    · obtain ⟨k, hk⟩ := hint
      refine ⟨-k, ?_⟩
      simp only [Int.cast_neg]
      simpa [diagonalTailDifference, two_mul] using congrArg Neg.neg hk
    · exact ⟨0, by simp⟩
  exact
    (diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget t).mp hdiag

/-- The explicit asymmetric residue certificate alone is a complete finite
consumer: its right-hand inequality already implies the largest one-sided
floor required by the generic cone soundness theorem. -/
theorem foreignDiagonalDefect_misses_fullTarget_of_residueCert
    {t L : ℕ} (hcert : diagonalFreshLossResidueCert t L) :
    ¬ForeignDiagonalDefectHitsFullTarget t := by
  have hresNonneg : (0 : ℤ) ≤ diagonalWindowResidue t L := by
    apply Int.emod_nonneg
    positivity
  have hfloor : (2 * periodLcm t + L + 2 : ℤ) < 2 ^ L := by
    have hright := hcert.2
    omega
  exact foreignDiagonalDefect_misses_fullTarget_of_projectionCert hfloor
    ((diagonalFreshLossResidueCert_iff_projectionCert t L).mp hcert)

/-- The exact unresolved operational supply exposed by this bridge. -/
def DiagonalFreshLossProjectionSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, diagonalFreshLossResidueCert t L

/-- Unbounded exact `[1, 2]` projection certificates feed the full-target
avoidance consumer and therefore prove irrationality of the totient series. -/
theorem irrational_totientSeries_of_diagonalFreshLossProjectionSupply
    (hsupply : DiagonalFreshLossProjectionSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totientSeries_of_full_target_avoidance_supply
  intro t₀
  obtain ⟨t, ht, L, hcert⟩ := hsupply t₀
  exact ⟨t, ht, foreignDiagonalDefect_misses_fullTarget_of_residueCert hcert⟩

/-! ## Sliding-suffix projection

The last `m` binary places of the depth-`(J + m)` diagonal window do not
depend on its first `J` offsets: the window numerator splits as
`P_{J+m}(M) = 2^m * P_J(M) + P_m(M + J)`, so the depth-`(J + m)` residue
reduces modulo `2^m` to the residue of a translated depth-`m` window.  A
central residue in those `m` suffix bits already excludes both edge bands of
the full window.  The cut remains operationally useful for finding finite
certificates, but the exact endpoint identities below show that it is not an
independent arithmetic averaging variable: it reads successive digits of one
dyadic orbit. -/

/-- Prefix–suffix split of the window numerator: the depth-`(J + m)` window
is `2^m` times its depth-`J` prefix plus the depth-`m` window at the
translated base `M + J`. -/
theorem windowNumerator_prefix_suffix (M J m : ℕ) :
    windowNumerator M (J + m)
      = 2 ^ m * windowNumerator M J + windowNumerator (M + J) m := by
  induction m with
  | zero => simp [windowNumerator]
  | succ m ih =>
    have h1 : J + (m + 1) = (J + m) + 1 := by omega
    have h2 : M + J + 1 + m = M + 1 + (J + m) := by omega
    rw [h1, windowNumerator_succ, ih, windowNumerator_succ, h2]
    ring

/-- The signed diagonal window increment `φ(2·H_t+s) − φ(H_t+s)` at offset
`s`. -/
def diagonalWindowIncrement (t s : ℕ) : ℤ :=
  (Nat.totient (2 * periodLcm t + s) : ℤ) -
    (Nat.totient (periodLcm t + s) : ℤ)

/-- Height-parametrized form of the signed window increment.  This separates
the arithmetic seam from the LCM indexing used by the final producer. -/
def diagonalHeightIncrement (H s : ℕ) : ℤ :=
  (Nat.totient (2 * H + s) : ℤ) - (Nat.totient (H + s) : ℤ)

theorem diagonalWindowIncrement_eq_heightIncrement (t s : ℕ) :
    diagonalWindowIncrement t s = diagonalHeightIncrement (periodLcm t) s :=
  rfl

/-- Every diagonal height letter has the elementary pointwise bound supplied
by `φ(k) ≤ k`.  This deliberately avoids factorisation hypotheses so it can
be used as a uniform envelope for the parity-free one-step correction. -/
theorem abs_diagonalHeightIncrement_le (H s : ℕ) :
    |diagonalHeightIncrement H s| ≤ (2 * H + s : ℤ) := by
  have htop : (Nat.totient (2 * H + s) : ℤ) ≤ (2 * H + s : ℕ) := by
    exact_mod_cast Nat.totient_le (2 * H + s)
  have hbot : (Nat.totient (H + s) : ℤ) ≤ (H + s : ℕ) := by
    exact_mod_cast Nat.totient_le (H + s)
  have htop0 : 0 ≤ (Nat.totient (2 * H + s) : ℤ) := by positivity
  have hbot0 : 0 ≤ (Nat.totient (H + s) : ℤ) := by positivity
  unfold diagonalHeightIncrement
  rw [abs_le]
  constructor <;> push_cast at * <;> omega

theorem abs_diagonalWindowIncrement_le (t s : ℕ) :
    |diagonalWindowIncrement t s| ≤ (2 * periodLcm t + s : ℤ) := by
  simpa only [diagonalWindowIncrement_eq_heightIncrement] using
    abs_diagonalHeightIncrement_le (periodLcm t) s

/-- The signed correction appended when an adjacent suffix reaches target
depth `m`.  This definition is parity-free and applies at every LCM height. -/
def diagonalTargetDepthCorrection (t m : ℕ) : ℤ :=
  diagonalWindowIncrement t (m + 1) - diagonalWindowIncrement t m

/-- The one-step correction has a sharper elementary envelope than the sum of
the two separate increment bounds: after expansion, each sign group contains
only three copies of the LCM height. -/
theorem abs_diagonalTargetDepthCorrection_le (t m : ℕ) :
    |diagonalTargetDepthCorrection t m| ≤
      (3 * periodLcm t + 2 * m + 1 : ℤ) := by
  let H := periodLcm t
  have h₂₁ : (Nat.totient (2 * H + (m + 1)) : ℤ) ≤
      (2 * H + (m + 1) : ℕ) := by
    exact_mod_cast Nat.totient_le (2 * H + (m + 1))
  have h₁₁ : (Nat.totient (H + (m + 1)) : ℤ) ≤
      (H + (m + 1) : ℕ) := by
    exact_mod_cast Nat.totient_le (H + (m + 1))
  have h₂₀ : (Nat.totient (2 * H + m) : ℤ) ≤ (2 * H + m : ℕ) := by
    exact_mod_cast Nat.totient_le (2 * H + m)
  have h₁₀ : (Nat.totient (H + m) : ℤ) ≤ (H + m : ℕ) := by
    exact_mod_cast Nat.totient_le (H + m)
  have h₂₁0 : 0 ≤ (Nat.totient (2 * H + (m + 1)) : ℤ) := by positivity
  have h₁₁0 : 0 ≤ (Nat.totient (H + (m + 1)) : ℤ) := by positivity
  have h₂₀0 : 0 ≤ (Nat.totient (2 * H + m) : ℤ) := by positivity
  have h₁₀0 : 0 ≤ (Nat.totient (H + m) : ℤ) := by positivity
  change
    |((Nat.totient (2 * H + (m + 1)) : ℤ) -
        (Nat.totient (H + (m + 1)) : ℤ)) -
      ((Nat.totient (2 * H + m) : ℤ) -
        (Nat.totient (H + m) : ℤ))| ≤
      (3 * H + 2 * m + 1 : ℤ)
  rw [abs_le]
  constructor <;> push_cast at * <;> omega

/-- Exact even-seam inheritance when both the old height and the reduced
offset are even. -/
theorem diagonalHeightIncrement_two_mul_even
    {H r : ℕ} (hH : Even H) (hr : Even r) :
    diagonalHeightIncrement (2 * H) (2 * r) =
      2 * diagonalHeightIncrement H r := by
  have houter : Even (2 * H + r) := (even_two_mul H).add hr
  have hinner : Even (H + r) := hH.add hr
  unfold diagonalHeightIncrement
  rw [show 2 * (2 * H) + 2 * r = 2 * (2 * H + r) by ring,
    show 2 * H + 2 * r = 2 * (H + r) by ring,
    Nat.totient_two_mul_of_even houter,
    Nat.totient_two_mul_of_even hinner]
  push_cast
  ring

/-- Exact even-seam inheritance when the reduced offset is odd. -/
theorem diagonalHeightIncrement_two_mul_odd
    {H r : ℕ} (hH : Even H) (hr : Odd r) :
    diagonalHeightIncrement (2 * H) (2 * r) =
      diagonalHeightIncrement H r := by
  have houter : Odd (2 * H + r) := (even_two_mul H).add_odd hr
  have hinner : Odd (H + r) := hH.add_odd hr
  unfold diagonalHeightIncrement
  rw [show 2 * (2 * H) + 2 * r = 2 * (2 * H + r) by ring,
    show 2 * H + 2 * r = 2 * (H + r) by ring,
    Nat.totient_two_mul_of_odd houter,
    Nat.totient_two_mul_of_odd hinner]

/-- The power-of-two seam at the indexed LCM level.  Once the new LCM height
is twice the old one, every even offset is inherited from the old height,
with multiplier two exactly when the reduced offset is even. -/
theorem diagonalWindowIncrement_evenSeam_even
    {t u r : ℕ} (ht : 2 ≤ t)
    (hheight : periodLcm u = 2 * periodLcm t) (hr : Even r) :
    diagonalWindowIncrement u (2 * r) =
      2 * diagonalWindowIncrement t r := by
  have hH : Even (periodLcm t) :=
    even_iff_two_dvd.mpr (dvd_periodLcm (by omega) ht)
  simpa [diagonalWindowIncrement_eq_heightIncrement, hheight] using
    (diagonalHeightIncrement_two_mul_even hH hr)

theorem diagonalWindowIncrement_evenSeam_odd
    {t u r : ℕ} (ht : 2 ≤ t)
    (hheight : periodLcm u = 2 * periodLcm t) (hr : Odd r) :
    diagonalWindowIncrement u (2 * r) =
      diagonalWindowIncrement t r := by
  have hH : Even (periodLcm t) :=
    even_iff_two_dvd.mpr (dvd_periodLcm (by omega) ht)
  simpa [diagonalWindowIncrement_eq_heightIncrement, hheight] using
    (diagonalHeightIncrement_two_mul_odd hH hr)

/-- The depth-`m` binary residue of the diagonal window suffix that starts
after the cut `J`: the last `m` bits of the depth-`(J + m)` diagonal window,
computed from the translated windows alone. -/
def diagonalSuffixResidue (t J m : ℕ) : ℤ :=
  ((windowNumerator (2 * periodLcm t + J) m : ℤ) -
    (windowNumerator (periodLcm t + J) m : ℤ)) % 2 ^ m

/-- The suffix residue is the dyadically weighted sum of the signed window
increments strictly after the cut — the operational shape used by the
sliding-suffix probe. -/
theorem diagonalSuffixResidue_eq_increment_sum (t J m : ℕ) :
    diagonalSuffixResidue t J m
      = (∑ r ∈ Finset.range m,
          diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) % 2 ^ m := by
  unfold diagonalSuffixResidue diagonalWindowIncrement windowNumerator
  push_cast
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have h1 : 2 * periodLcm t + J + 1 + r = 2 * periodLcm t + (J + 1 + r) := by
    omega
  have h2 : periodLcm t + J + 1 + r = periodLcm t + (J + 1 + r) := by omega
  rw [h1, h2]
  ring

/-- Low-bit projection: the depth-`(J + m)` diagonal residue reduces modulo
`2^m` to the sliding-suffix residue at cut `J`.  The `J`-bit prefix vanishes;
no estimate of it is required. -/
theorem diagonalWindowResidue_mod_suffix (t J m : ℕ) :
    diagonalWindowResidue t (J + m) % 2 ^ m = diagonalSuffixResidue t J m := by
  have hdvd : ((2 : ℤ) ^ m) ∣ 2 ^ (J + m) :=
    pow_dvd_pow 2 (Nat.le_add_left m J)
  have hsplit :
      ((windowNumerator (2 * periodLcm t) (J + m) : ℤ) -
          (windowNumerator (periodLcm t) (J + m) : ℤ))
        = ((windowNumerator (2 * periodLcm t + J) m : ℤ) -
              (windowNumerator (periodLcm t + J) m : ℤ))
          + 2 ^ m * ((windowNumerator (2 * periodLcm t) J : ℤ) -
              (windowNumerator (periodLcm t) J : ℤ)) := by
    rw [windowNumerator_prefix_suffix (2 * periodLcm t) J m,
      windowNumerator_prefix_suffix (periodLcm t) J m]
    push_cast
    ring
  unfold diagonalWindowResidue diagonalSuffixResidue
  rw [Int.emod_emod_of_dvd _ hdvd, hsplit, Int.add_mul_emod_self_left]

/-- **Sliding-suffix transference.**  A central residue in the last `m` bits
of the depth-`(J + m)` diagonal window already implies the full asymmetric
safe-interval certificate at depth `J + m`: both excluded edge bands of the
full window reduce into the corresponding edge bands of the suffix
modulus. -/
theorem diagonalFreshLossResidueCert_of_suffix_central {t J m : ℕ}
    (hleft : (periodLcm t + (J + m) + 2 : ℤ) < diagonalSuffixResidue t J m)
    (hright : diagonalSuffixResidue t J m
        < 2 ^ m - (2 * periodLcm t + (J + m) + 2)) :
    diagonalFreshLossResidueCert t (J + m) := by
  have hmod := diagonalWindowResidue_mod_suffix t J m
  have hM2pos : (0 : ℤ) < 2 ^ m := by positivity
  have hRlo : (0 : ℤ) ≤ diagonalWindowResidue t (J + m) := by
    unfold diagonalWindowResidue
    exact Int.emod_nonneg _ (by positivity)
  have hRhi : diagonalWindowResidue t (J + m) < 2 ^ (J + m) := by
    unfold diagonalWindowResidue
    exact Int.emod_lt_of_pos _ (by positivity)
  have hdvd : ((2 : ℤ) ^ m) ∣ 2 ^ (J + m) :=
    pow_dvd_pow 2 (Nat.le_add_left m J)
  unfold diagonalFreshLossResidueCert
  constructor
  · -- a left-band full residue would be its own suffix residue
    by_contra hnot
    have hRle : diagonalWindowResidue t (J + m) ≤ periodLcm t + (J + m) + 2 :=
      not_lt.mp hnot
    have hσlt : diagonalSuffixResidue t J m < 2 ^ m := by
      rw [← hmod]
      exact Int.emod_lt_of_pos _ hM2pos
    have hRltM2 : diagonalWindowResidue t (J + m) < 2 ^ m := by omega
    have hRfix : diagonalWindowResidue t (J + m) % 2 ^ m
        = diagonalWindowResidue t (J + m) := Int.emod_eq_of_lt hRlo hRltM2
    omega
  · -- a right-band full residue reappears in the suffix top band
    by_contra hnot
    have hRge : 2 ^ (J + m) - (2 * periodLcm t + (J + m) + 2)
        ≤ diagonalWindowResidue t (J + m) := not_lt.mp hnot
    have hσnn : (0 : ℤ) ≤ diagonalSuffixResidue t J m := by
      rw [← hmod]
      exact Int.emod_nonneg _ (by positivity)
    have hband : (2 * periodLcm t + (J + m) + 2 : ℤ) < 2 ^ m := by omega
    have hσeq : diagonalSuffixResidue t J m
        = 2 ^ m - (2 ^ (J + m) - diagonalWindowResidue t (J + m)) := by
      set k : ℤ := 2 ^ (J + m) - diagonalWindowResidue t (J + m) with hk
      have hkpos : (0 : ℤ) < k := by omega
      have hklt : k < 2 ^ m := by omega
      have h1 : diagonalWindowResidue t (J + m) = 2 ^ (J + m) - k := by omega
      have h2 : ((2 : ℤ) ^ (J + m) - k) % 2 ^ m = ((2 : ℤ) ^ m - k) % 2 ^ m := by
        obtain ⟨c, hc⟩ := hdvd
        rw [hc,
          show (2 ^ m * c - k : ℤ) = (2 ^ m - k) + 2 ^ m * (c - 1) by ring,
          Int.add_mul_emod_self_left]
      have h3 : ((2 : ℤ) ^ m - k) % 2 ^ m = 2 ^ m - k :=
        Int.emod_eq_of_lt (by omega) (by omega)
      rw [← hmod, h1, h2, h3]
    omega

/-- Sliding-suffix transference with the symmetric `2H` edge retained. -/
theorem diagonalSymmetricResidueCert_of_suffix_central {t J m : ℕ}
    (hleft : (2 * periodLcm t + (J + m) + 2 : ℤ) <
      diagonalSuffixResidue t J m)
    (hright : diagonalSuffixResidue t J m
        < 2 ^ m - (2 * periodLcm t + (J + m) + 2)) :
    diagonalSymmetricResidueCert t (J + m) := by
  have hmod := diagonalWindowResidue_mod_suffix t J m
  have hM2pos : (0 : ℤ) < 2 ^ m := by positivity
  have hRlo : (0 : ℤ) ≤ diagonalWindowResidue t (J + m) := by
    unfold diagonalWindowResidue
    exact Int.emod_nonneg _ (by positivity)
  have hRhi : diagonalWindowResidue t (J + m) < 2 ^ (J + m) := by
    unfold diagonalWindowResidue
    exact Int.emod_lt_of_pos _ (by positivity)
  have hdvd : ((2 : ℤ) ^ m) ∣ 2 ^ (J + m) :=
    pow_dvd_pow 2 (Nat.le_add_left m J)
  unfold diagonalSymmetricResidueCert
  constructor
  · by_contra hnot
    have hRle : diagonalWindowResidue t (J + m) ≤
        2 * periodLcm t + (J + m) + 2 := not_lt.mp hnot
    have hσlt : diagonalSuffixResidue t J m < 2 ^ m := by
      rw [← hmod]
      exact Int.emod_lt_of_pos _ hM2pos
    have hRltM2 : diagonalWindowResidue t (J + m) < 2 ^ m := by omega
    have hRfix : diagonalWindowResidue t (J + m) % 2 ^ m
        = diagonalWindowResidue t (J + m) := Int.emod_eq_of_lt hRlo hRltM2
    omega
  · by_contra hnot
    have hRge : 2 ^ (J + m) - (2 * periodLcm t + (J + m) + 2)
        ≤ diagonalWindowResidue t (J + m) := not_lt.mp hnot
    have hσnn : (0 : ℤ) ≤ diagonalSuffixResidue t J m := by
      rw [← hmod]
      exact Int.emod_nonneg _ (by positivity)
    have hband : (2 * periodLcm t + (J + m) + 2 : ℤ) < 2 ^ m := by omega
    have hσeq : diagonalSuffixResidue t J m
        = 2 ^ m - (2 ^ (J + m) - diagonalWindowResidue t (J + m)) := by
      set k : ℤ := 2 ^ (J + m) - diagonalWindowResidue t (J + m) with hk
      have hkpos : (0 : ℤ) < k := by omega
      have hklt : k < 2 ^ m := by omega
      have h1 : diagonalWindowResidue t (J + m) = 2 ^ (J + m) - k := by omega
      have h2 : ((2 : ℤ) ^ (J + m) - k) % 2 ^ m =
          ((2 : ℤ) ^ m - k) % 2 ^ m := by
        obtain ⟨c, hc⟩ := hdvd
        rw [hc,
          show (2 ^ m * c - k : ℤ) =
            (2 ^ m - k) + 2 ^ m * (c - 1) by ring,
          Int.add_mul_emod_self_left]
      have h3 : ((2 : ℤ) ^ m - k) % 2 ^ m = 2 ^ m - k :=
        Int.emod_eq_of_lt (by omega) (by omega)
      rw [← hmod, h1, h2, h3]
    omega

/-! ## Adjacent-suffix separation

Two adjacent cuts already contain the finite geometry needed by the
sliding-suffix consumer.  Their difference is represented in the canonical
interval `[0, 2^m)`, so a residue outside the sum of the two edge widths
forces at least one suffix into its central interval.  This is an integer-only
replacement for averaging a larger family of complex phases. -/

/-- The canonical modular displacement from the suffix at cut `J` to the
suffix at cut `J + 1`. -/
def diagonalAdjacentSuffixResidue (t J m : ℕ) : ℤ :=
  (diagonalSuffixResidue t (J + 1) m -
    diagonalSuffixResidue t J m) % 2 ^ m

/-- Sliding the cut once doubles the retained suffix and appends the next
diagonal increment. -/
theorem diagonalSuffixResidue_succ_cut (t J m : ℕ) :
    diagonalSuffixResidue t (J + 1) m =
      (2 * diagonalSuffixResidue t J m +
        diagonalWindowIncrement t (J + m + 1)) % 2 ^ m := by
  let H := periodLcm t
  let P := 2 * H + J
  let Q := H + J
  let M : ℤ := 2 ^ m
  let A : ℤ := windowNumerator P m
  let B : ℤ := windowNumerator Q m
  let A' : ℤ := windowNumerator (P + 1) m
  let B' : ℤ := windowNumerator (Q + 1) m
  let E : ℤ := Nat.totient (P + m + 1)
  let F : ℤ := Nat.totient (Q + m + 1)
  let U : ℤ := Nat.totient (P + 1)
  let V : ℤ := Nat.totient (Q + 1)
  have hshift (N : ℕ) :
      windowNumerator (N + 1) m + 2 ^ m * Nat.totient (N + 1) =
        windowNumerator N (m + 1) := by
    rw [show m + 1 = 1 + m by omega, windowNumerator_prefix_suffix N 1 m]
    simp [windowNumerator, Nat.add_comm, Nat.add_left_comm]
  have hA : A' + M * U = 2 * A + E := by
    have hNat := (calc
      windowNumerator (P + 1) m + 2 ^ m * Nat.totient (P + 1) =
          windowNumerator P (m + 1) := hshift P
      _ = 2 * windowNumerator P m + Nat.totient (P + m + 1) := by
        rw [windowNumerator_succ]
        congr 2 <;> omega)
    simpa [A', M, U, A, E] using congrArg (fun n : ℕ => (n : ℤ)) hNat
  have hB : B' + M * V = 2 * B + F := by
    have hNat := (calc
      windowNumerator (Q + 1) m + 2 ^ m * Nat.totient (Q + 1) =
          windowNumerator Q (m + 1) := hshift Q
      _ = 2 * windowNumerator Q m + Nat.totient (Q + m + 1) := by
        rw [windowNumerator_succ]
        congr 2 <;> omega)
    simpa [B', M, V, B, F] using congrArg (fun n : ℕ => (n : ℤ)) hNat
  have hAmod : A' ≡ 2 * A + E [ZMOD M] := by
    rw [Int.modEq_iff_dvd]
    use U
    linarith
  have hBmod : B' ≡ 2 * B + F [ZMOD M] := by
    rw [Int.modEq_iff_dvd]
    use V
    linarith
  have hraw : A' - B' ≡ 2 * (A - B) + (E - F) [ZMOD M] := by
    convert hAmod.sub hBmod using 1 <;> ring
  have hreduced :
      2 * ((A - B) % M) + (E - F) ≡
        2 * (A - B) + (E - F) [ZMOD M] :=
    ((Int.mod_modEq (A - B) M).mul_left 2).add (Int.ModEq.refl _)
  have hEq : (A' - B') % M =
      (2 * ((A - B) % M) + (E - F)) % M :=
    Int.ModEq.eq (hraw.trans hreduced.symm)
  simpa [diagonalSuffixResidue, diagonalWindowIncrement, A', B', M, A, B,
    E, F, P, Q, H, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hEq

/-- The adjacent displacement is the terminal-corrected suffix residue. -/
theorem diagonalAdjacentSuffixResidue_eq_terminal_corrected (t J m : ℕ) :
    diagonalAdjacentSuffixResidue t J m =
      (diagonalSuffixResidue t J m +
        diagonalWindowIncrement t (J + m + 1)) % 2 ^ m := by
  have hfix : diagonalSuffixResidue t J m % 2 ^ m =
      diagonalSuffixResidue t J m := by
    unfold diagonalSuffixResidue
    rw [Int.emod_emod]
  unfold diagonalAdjacentSuffixResidue
  rw [diagonalSuffixResidue_succ_cut]
  apply Int.ModEq.eq
  have h := (Int.mod_modEq
    (2 * diagonalSuffixResidue t J m +
      diagonalWindowIncrement t (J + m + 1)) (2 ^ m)).sub
        (Int.ModEq.refl (diagonalSuffixResidue t J m))
  convert h using 1 <;> ring

/-- Unreduced integer block underlying the adjacent suffix displacement.  It
is the exact target-specific scalar evaluated by the canonical jump probe. -/
def diagonalAdjacentSuffixRawBlock (t J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) +
    diagonalWindowIncrement t (J + m + 1)

/-! ## Exact finite old/foreign Möbius split -/

/-- The literal contribution at offset `s` of all Möbius channels whose
indices divide the LCM height `H`. -/
noncomputable def oldMobiusIncrement (H s : ℕ) : ℤ :=
  ∑ d ∈ H.divisors,
    if d ∣ s then
      ArithmeticFunction.moebius d * (((H / d : ℕ) : ℤ))
    else 0

/-- The old-channel formula is exactly the sum of the landed totalized
Möbius channels after one height-`H` forward difference at `H + s`. -/
theorem oldMobiusIncrement_eq_sum_forwardDifference_channel
    (H s : ℕ) (hH : 0 < H) :
    oldMobiusIncrement H s =
      ∑ d ∈ H.divisors,
        forwardDifference H (mobiusTotientChannel d) (H + s) := by
  unfold oldMobiusIncrement
  apply Finset.sum_congr rfl
  intro d hd
  have hdH : d ∣ H := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdH hH
  rw [forwardDifference_mobiusTotientChannel_of_dvd hdpos hdH]
  simp only
  have hdAdd : d ∣ H + s ↔ d ∣ s := (Nat.dvd_add_iff_right hdH).symm
  simp only [hdAdd]

/-- A squarefree divisor of `H` divides the canonical radical of `H`. -/
theorem squarefree_dvd_squarefreeKernel {d H : ℕ}
    (hH : 0 < H) (hdH : d ∣ H) (hd : Squarefree d) :
    d ∣ RadicalMobiusShadow.squarefreeKernel H := by
  have hsubset : d.primeFactors ⊆ H.primeFactors :=
    Nat.primeFactors_mono hdH hH.ne'
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  simpa [RadicalMobiusShadow.squarefreeKernel] using
    (Finset.prod_dvd_prod_of_subset d.primeFactors H.primeFactors
      (fun p : ℕ => p) hsubset)

/-- Exact offsetwise old-channel identity: the literal divisor-channel sum is
`H / rad(H)` times the positive gcd-word coefficient at the same offset. -/
theorem oldMobiusIncrement_eq_scale_gcdWordCoeff
    (H s : ℕ) (hH : 0 < H) :
    oldMobiusIncrement H s =
      (((H / RadicalMobiusShadow.squarefreeKernel H : ℕ) : ℤ)) *
        (RepunitMobiusNumerator.gcdWordCoeff
          (RadicalMobiusShadow.squarefreeKernel H) s : ℤ) := by
  classical
  let R := RadicalMobiusShadow.squarefreeKernel H
  let g := R.gcd s
  have hRpos : 0 < R := RadicalMobiusShadow.squarefreeKernel_pos H
  have hRdH : R ∣ H := RadicalMobiusShadow.squarefreeKernel_dvd H
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left s hRpos
  have hgdR : g ∣ R := Nat.gcd_dvd_left R s
  have hgds : g ∣ s := Nat.gcd_dvd_right R s
  have hgdH : g ∣ H := hgdR.trans hRdH
  have hsubset :
      g.divisors ⊆ {d ∈ H.divisors | d ∣ s} := by
    intro d hdg
    have hdvdg : d ∣ g := Nat.dvd_of_mem_divisors hdg
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdvdg.trans hgdH, hH.ne'⟩,
        hdvdg.trans hgds⟩
  have hsupport :
      (∑ d ∈ {d ∈ H.divisors | d ∣ s},
          ArithmeticFunction.moebius d * (((H / d : ℕ) : ℤ))) =
        ∑ d ∈ g.divisors,
          ArithmeticFunction.moebius d * (((H / d : ℕ) : ℤ)) := by
    symm
    apply Finset.sum_subset hsubset
    intro d hdOld hdNotG
    have hdH : d ∣ H :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdOld).1
    have hds : d ∣ s := (Finset.mem_filter.mp hdOld).2
    have hnotSquarefree : ¬Squarefree d := by
      intro hdSquarefree
      have hdR : d ∣ R := by
        simpa [R] using squarefree_dvd_squarefreeKernel hH hdH hdSquarefree
      exact hdNotG (Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd hdR hds, hgpos.ne'⟩)
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnotSquarefree]
    simp
  have hscaled :
      (∑ d ∈ g.divisors,
          ArithmeticFunction.moebius d * (((H / d : ℕ) : ℤ))) =
        (((H / g : ℕ) : ℤ)) * (g.totient : ℤ) := by
    calc
      (∑ d ∈ g.divisors,
          ArithmeticFunction.moebius d * (((H / d : ℕ) : ℤ))) =
          ∑ d ∈ g.divisors,
            (((H / g : ℕ) : ℤ)) *
              (ArithmeticFunction.moebius d * (((g / d : ℕ) : ℤ))) := by
                apply Finset.sum_congr rfl
                intro d hd
                have hdg : d ∣ g := Nat.dvd_of_mem_divisors hd
                rw [← Nat.div_mul_div hgdH hdg, Nat.cast_mul]
                ring
      _ = (((H / g : ℕ) : ℤ)) *
          ∑ d ∈ g.divisors,
            ArithmeticFunction.moebius d * (((g / d : ℕ) : ℤ)) := by
              rw [Finset.mul_sum]
      _ = (((H / g : ℕ) : ℤ)) * (g.totient : ℤ) := by
            rw [MersenneLambertLadder.sum_divisors_moebius_mul_div g hgpos]
  rw [oldMobiusIncrement, ← Finset.sum_filter, hsupport, hscaled]
  change (((H / g : ℕ) : ℤ)) * (g.totient : ℤ) =
    (((H / R : ℕ) : ℤ)) *
      (RepunitMobiusNumerator.gcdWordCoeff R s : ℤ)
  rw [RepunitMobiusNumerator.gcdWordCoeff]
  change (((H / g : ℕ) : ℤ)) * (g.totient : ℤ) =
    (((H / R : ℕ) : ℤ)) * ((((R / g) * g.totient : ℕ) : ℤ))
  calc
    (((H / g : ℕ) : ℤ)) * (g.totient : ℤ) =
        ((((H / R) * (R / g) : ℕ) : ℤ)) * (g.totient : ℤ) := by
          rw [Nat.div_mul_div hRdH hgdR]
    _ = (((H / R : ℕ) : ℤ)) * ((((R / g) * g.totient : ℕ) : ℤ)) := by
      push_cast
      ring

/-- A common finite channel cutoff containing every divisor channel of
`φ(n)` whenever `0 < n ≤ D`. -/
noncomputable def boundedMobiusChannelSum (D n : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (D + 1), mobiusTotientChannel d n

/-- Extending the landed divisor-channel expansion to a common finite cutoff
adds only totalized zero channels. -/
theorem totient_eq_boundedMobiusChannelSum
    {D n : ℕ} (hn : 0 < n) (hnD : n ≤ D) :
    (Nat.totient n : ℤ) = boundedMobiusChannelSum D n := by
  rw [totient_eq_sum_mobiusTotientChannel n hn]
  unfold boundedMobiusChannelSum
  apply Finset.sum_subset
  · intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hle : d ≤ n := Nat.le_of_dvd hn hdn
    exact Finset.mem_range.mpr (by omega)
  · intro d _hdRange hdNotDivisor
    have hnot : ¬d ∣ n := by
      intro hdn
      exact hdNotDivisor (Nat.mem_divisors.mpr ⟨hdn, hn.ne'⟩)
    simp [mobiusTotientChannel, hnot]

/-- The literal finite foreign complement at one offset: exactly the channel
differences whose indices do not divide the LCM height. -/
noncomputable def finiteForeignChannelIncrement (H s : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (2 * H + s + 1),
    if d ∣ H then 0
    else forwardDifference H (mobiusTotientChannel d) (H + s)

/-- The actual finite height increment is the sum of all totalized channel
differences under one common cutoff. -/
theorem diagonalHeightIncrement_eq_sum_channelDifferences
    (H s : ℕ) (hH : 0 < H) :
    diagonalHeightIncrement H s =
      ∑ d ∈ Finset.range (2 * H + s + 1),
        forwardDifference H (mobiusTotientChannel d) (H + s) := by
  have hTopPos : 0 < 2 * H + s := by omega
  have hLowPos : 0 < H + s := by omega
  have hLowLe : H + s ≤ 2 * H + s := by omega
  calc
    diagonalHeightIncrement H s =
        boundedMobiusChannelSum (2 * H + s) (2 * H + s) -
          boundedMobiusChannelSum (2 * H + s) (H + s) := by
            rw [diagonalHeightIncrement,
              ← totient_eq_boundedMobiusChannelSum hTopPos le_rfl,
              ← totient_eq_boundedMobiusChannelSum hLowPos hLowLe]
    _ = ∑ d ∈ Finset.range (2 * H + s + 1),
          (mobiusTotientChannel d (2 * H + s) -
            mobiusTotientChannel d (H + s)) := by
            unfold boundedMobiusChannelSum
            rw [← Finset.sum_sub_distrib]
    _ = ∑ d ∈ Finset.range (2 * H + s + 1),
          forwardDifference H (mobiusTotientChannel d) (H + s) := by
            apply Finset.sum_congr rfl
            intro d _hd
            unfold forwardDifference
            rw [show H + s + H = 2 * H + s by omega]

/-- The old part of the common cutoff is exactly `oldMobiusIncrement`; this
is a theorem, not a second old-channel definition. -/
theorem boundedOldChannelSum_eq_oldMobiusIncrement
    (H s : ℕ) (hH : 0 < H) :
    (∑ d ∈ Finset.range (2 * H + s + 1),
        if d ∣ H then
          forwardDifference H (mobiusTotientChannel d) (H + s)
        else 0) = oldMobiusIncrement H s := by
  have hsubset :
      H.divisors ⊆ Finset.range (2 * H + s + 1) := by
    intro d hd
    have hdH : d ∣ H := Nat.dvd_of_mem_divisors hd
    have hle : d ≤ H := Nat.le_of_dvd hH hdH
    exact Finset.mem_range.mpr (by omega)
  calc
    (∑ d ∈ Finset.range (2 * H + s + 1),
        if d ∣ H then
          forwardDifference H (mobiusTotientChannel d) (H + s)
        else 0) =
        ∑ d ∈ H.divisors,
          if d ∣ H then
            forwardDifference H (mobiusTotientChannel d) (H + s)
          else 0 := by
            symm
            apply Finset.sum_subset hsubset
            intro d _hdRange hdNotDivisor
            have hnot : ¬d ∣ H := by
              intro hdH
              exact hdNotDivisor (Nat.mem_divisors.mpr ⟨hdH, hH.ne'⟩)
            simp [hnot]
    _ = ∑ d ∈ H.divisors,
          forwardDifference H (mobiusTotientChannel d) (H + s) := by
            apply Finset.sum_congr rfl
            intro d hd
            simp [Nat.dvd_of_mem_divisors hd]
    _ = oldMobiusIncrement H s :=
      (oldMobiusIncrement_eq_sum_forwardDifference_channel H s hH).symm

/-- Exact finite offset split into the scaled-gcd-word old channel and the
literal `d ∤ H` foreign channel sum. -/
theorem diagonalHeightIncrement_eq_oldMobius_add_finiteForeign
    (H s : ℕ) (hH : 0 < H) :
    diagonalHeightIncrement H s =
      oldMobiusIncrement H s + finiteForeignChannelIncrement H s := by
  rw [diagonalHeightIncrement_eq_sum_channelDifferences H s hH]
  unfold finiteForeignChannelIncrement
  rw [← boundedOldChannelSum_eq_oldMobiusIncrement H s hH]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdH : d ∣ H <;> simp [hdH]

/-! ### Pointwise phase normal form for the literal foreign sum -/

/-- Explicit three-way phase form of one foreign channel. -/
noncomputable def foreignChannelPhaseTerm (d H s : ℕ) : ℤ :=
  if d ∣ 2 * H + s then
    ArithmeticFunction.moebius d * ((((2 * H + s) / d : ℕ) : ℤ))
  else if d ∣ H + s then
    -(ArithmeticFunction.moebius d * ((((H + s) / d : ℕ) : ℤ)))
  else 0

/-- Outside the old divisor set, an index cannot divide both endpoints. -/
theorem foreign_endpoint_support_disjoint
    {d H s : ℕ} (hdH : ¬d ∣ H) :
    ¬(d ∣ 2 * H + s ∧ d ∣ H + s) := by
  rintro ⟨hTop, hLow⟩
  apply hdH
  have hTop' : d ∣ (H + s) + H := by
    rw [show (H + s) + H = 2 * H + s by omega]
    exact hTop
  exact (Nat.dvd_add_iff_right hLow).mpr hTop'

/-- Exact pointwise phase normal form of a foreign channel difference. -/
theorem forwardDifference_mobiusTotientChannel_of_not_dvd
    {d H s : ℕ} (hdH : ¬d ∣ H) :
    forwardDifference H (mobiusTotientChannel d) (H + s) =
      foreignChannelPhaseTerm d H s := by
  have hdisjoint := foreign_endpoint_support_disjoint (s := s) hdH
  unfold forwardDifference mobiusTotientChannel foreignChannelPhaseTerm
  rw [show H + s + H = 2 * H + s by omega]
  by_cases hTop : d ∣ 2 * H + s
  · have hLow : ¬d ∣ H + s := by
      intro h
      exact hdisjoint ⟨hTop, h⟩
    simp [hTop, hLow]
  · by_cases hLow : d ∣ H + s
    · simp [hTop, hLow]
    · simp [hTop, hLow]

/-- The whole finite foreign increment is the sum of the explicit disjoint
endpoint phase terms. -/
theorem finiteForeignChannelIncrement_eq_phaseSum (H s : ℕ) :
    finiteForeignChannelIncrement H s =
      ∑ d ∈ Finset.range (2 * H + s + 1),
        if d ∣ H then 0 else foreignChannelPhaseTerm d H s := by
  unfold finiteForeignChannelIncrement
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdH : d ∣ H
  · simp [hdH]
  · simp only [if_neg hdH]
    exact forwardDifference_mobiusTotientChannel_of_not_dvd hdH

/-- A nonzero foreign phase term is supported at exactly one endpoint. -/
theorem foreignChannelPhaseTerm_ne_zero_support
    {d H s : ℕ} (hdH : ¬d ∣ H)
    (hne : foreignChannelPhaseTerm d H s ≠ 0) :
    (d ∣ 2 * H + s ∧ ¬d ∣ H + s) ∨
      (¬d ∣ 2 * H + s ∧ d ∣ H + s) := by
  have hdisjoint := foreign_endpoint_support_disjoint (s := s) hdH
  by_cases hTop : d ∣ 2 * H + s
  · left
    exact ⟨hTop, fun hLow => hdisjoint ⟨hTop, hLow⟩⟩
  · right
    refine ⟨hTop, ?_⟩
    by_contra hLow
    exact hne (by simp [foreignChannelPhaseTerm, hTop, hLow])

/-- Every nonzero foreign phase term comes from a squarefree index. -/
theorem squarefree_of_foreignChannelPhaseTerm_ne_zero
    {d H s : ℕ} (hne : foreignChannelPhaseTerm d H s ≠ 0) :
    Squarefree d := by
  by_contra hnotSquarefree
  have hmu : ArithmeticFunction.moebius d = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnotSquarefree
  exact hne (by simp [foreignChannelPhaseTerm, hmu])

/-! ### Dyadic phase echo and sparse-channel spacing -/

/-- A supported lower endpoint has the negative branch of the phase term. -/
theorem foreignChannelPhaseTerm_eq_neg_of_low
    {d H s : ℕ} (hdH : ¬d ∣ H) (hLow : d ∣ H + s) :
    foreignChannelPhaseTerm d H s =
      -(ArithmeticFunction.moebius d * ((((H + s) / d : ℕ) : ℤ))) := by
  have hTop : ¬d ∣ 2 * H + s := by
    intro hTop
    exact foreign_endpoint_support_disjoint hdH ⟨hTop, hLow⟩
  simp [foreignChannelPhaseTerm, hTop, hLow]

/-- A supported top endpoint has the positive branch of the phase term. -/
theorem foreignChannelPhaseTerm_eq_of_top
    {d H s : ℕ} (hdH : ¬d ∣ H) (hTop : d ∣ 2 * H + s) :
    foreignChannelPhaseTerm d H s =
      ArithmeticFunction.moebius d * ((((2 * H + s) / d : ℕ) : ℤ)) := by
  have hLow : ¬d ∣ H + s := by
    intro hLow
    exact foreign_endpoint_support_disjoint hdH ⟨hTop, hLow⟩
  simp [foreignChannelPhaseTerm, hTop]

/-- Every lower pulse at offset `s` has a top echo at offset `2s`; the top
quotient, and hence the top phase value, is exactly twice the lower one. -/
theorem foreignChannelPhaseTerm_low_double_echo
    {d H s : ℕ} (hdH : ¬d ∣ H) (hLow : d ∣ H + s) :
    foreignChannelPhaseTerm d H s =
        -(ArithmeticFunction.moebius d * ((((H + s) / d : ℕ) : ℤ))) ∧
      foreignChannelPhaseTerm d H (2 * s) =
        2 * (ArithmeticFunction.moebius d * ((((H + s) / d : ℕ) : ℤ))) := by
  constructor
  · exact foreignChannelPhaseTerm_eq_neg_of_low hdH hLow
  · have hTop : d ∣ 2 * H + 2 * s := by
      have h := hLow.mul_left 2
      simpa [Nat.mul_add] using h
    have hquot : (2 * H + 2 * s) / d = 2 * ((H + s) / d) := by
      rw [show 2 * H + 2 * s = 2 * (H + s) by omega,
        Nat.mul_div_assoc 2 hLow]
    rw [foreignChannelPhaseTerm_eq_of_top hdH hTop, hquot]
    push_cast
    ring

/-- The exact two-position contribution of a lower pulse and its doubled top
echo inside a binary-reversed block. -/
theorem foreignChannelPhaseTerm_weighted_low_double_echo
    {d H s m : ℕ} (hdH : ¬d ∣ H) (hLow : d ∣ H + s)
    (_hsm : 2 * s ≤ m) :
    foreignChannelPhaseTerm d H s * 2 ^ (m - s) +
        foreignChannelPhaseTerm d H (2 * s) * 2 ^ (m - 2 * s) =
      (ArithmeticFunction.moebius d * ((((H + s) / d : ℕ) : ℤ))) *
        (2 * 2 ^ (m - 2 * s) - 2 ^ (m - s)) := by
  obtain ⟨hLowValue, hTopValue⟩ :=
    foreignChannelPhaseTerm_low_double_echo hdH hLow
  rw [hLowValue, hTopValue]
  ring

/-- Two lower-endpoint hits of one channel are separated by a multiple of the
channel index. -/
theorem dvd_offset_sub_of_two_low_supports
    {d H s r : ℕ} (hsr : s ≤ r)
    (hs : d ∣ H + s) (hr : d ∣ H + r) :
    d ∣ r - s := by
  have hsub : (H + r) - (H + s) = r - s := by omega
  rw [← hsub]
  exact Nat.dvd_sub hr hs

/-- Distinct lower-endpoint hits are at least `d` offsets apart. -/
theorem channel_le_offset_sub_of_two_low_supports
    {d H s r : ℕ} (_hd : 0 < d) (hsr : s < r)
    (hs : d ∣ H + s) (hr : d ∣ H + r) :
    d ≤ r - s := by
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hsr)
    (dvd_offset_sub_of_two_low_supports hsr.le hs hr)

/-- Two top-endpoint hits of one channel are separated by a multiple of the
channel index. -/
theorem dvd_offset_sub_of_two_top_supports
    {d H s r : ℕ} (hsr : s ≤ r)
    (hs : d ∣ 2 * H + s) (hr : d ∣ 2 * H + r) :
    d ∣ r - s := by
  have hsub : (2 * H + r) - (2 * H + s) = r - s := by omega
  rw [← hsub]
  exact Nat.dvd_sub hr hs

/-- Distinct top-endpoint hits are at least `d` offsets apart. -/
theorem channel_le_offset_sub_of_two_top_supports
    {d H s r : ℕ} (_hd : 0 < d) (hsr : s < r)
    (hs : d ∣ 2 * H + s) (hr : d ∣ 2 * H + r) :
    d ≤ r - s := by
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hsr)
    (dvd_offset_sub_of_two_top_supports hsr.le hs hr)

/-- Every positive channel missing from `periodLcm t` lies strictly above the
LCM scale `t`. -/
theorem lt_of_not_dvd_periodLcm
    {t d : ℕ} (hd : 0 < d) (hnd : ¬d ∣ periodLcm t) :
    t < d := by
  by_contra hle
  exact hnd (dvd_periodLcm hd (not_lt.mp hle))

/-- A squarefree foreign channel below `2t` is a prime, not merely a prime
power. -/
theorem prime_of_squarefree_not_dvd_periodLcm_lt_two_mul
    {t d : ℕ} (hsq : Squarefree d) (hd : 0 < d) (hlt : d < 2 * t)
    (hnd : ¬d ∣ periodLcm t) :
    Nat.Prime d := by
  obtain ⟨p, k, hp, hpk, _htd⟩ :=
    eq_prime_pow_of_not_dvd_periodLcm hd hlt hnd
  subst d
  have hk : k ≠ 0 := by
    intro hk
    subst k
    simp at hnd
  have hkOne : k = 1 := (Nat.squarefree_pow_iff hp.ne_one hk).mp hsq |>.2
  simpa [hkOne] using hp

/-- If one lower endpoint repeats inside offsets `1..m+1` and `m < 2t`,
then its foreign channel is a prime power in `(t,2t)`. -/
theorem repeated_low_support_primePow_of_short_periodLcm_window
    {t d s r m : ℕ} (hsPos : 1 ≤ s) (hsr : s < r)
    (hrm : r ≤ m + 1) (hm : m < 2 * t)
    (hnd : ¬d ∣ periodLcm t)
    (hs : d ∣ periodLcm t + s) (hr : d ∣ periodLcm t + r) :
    ∃ p k : ℕ, Nat.Prime p ∧ d = p ^ k ∧ t < d := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hs (by
    have hH := periodLcm_pos t
    omega)
  have hdGap : d ≤ r - s :=
    channel_le_offset_sub_of_two_low_supports hd hsr hs hr
  have hgap : r - s ≤ m := by omega
  have hlt : d < 2 * t := lt_of_le_of_lt (hdGap.trans hgap) hm
  exact eq_prime_pow_of_not_dvd_periodLcm hd hlt hnd

/-- The squarefree channels that can actually carry a nonzero Möbius phase
therefore reduce to primes whenever a lower endpoint repeats in the short
window. -/
theorem prime_of_squarefree_repeated_low_support_in_short_periodLcm_window
    {t d s r m : ℕ} (hsq : Squarefree d)
    (hsPos : 1 ≤ s) (hsr : s < r)
    (hrm : r ≤ m + 1) (hm : m < 2 * t)
    (hnd : ¬d ∣ periodLcm t)
    (hs : d ∣ periodLcm t + s) (hr : d ∣ periodLcm t + r) :
    Nat.Prime d := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hs (by
    have hH := periodLcm_pos t
    omega)
  have hdGap : d ≤ r - s :=
    channel_le_offset_sub_of_two_low_supports hd hsr hs hr
  have hgap : r - s ≤ m := by omega
  exact prime_of_squarefree_not_dvd_periodLcm_lt_two_mul
    hsq hd (lt_of_le_of_lt (hdGap.trans hgap) hm) hnd

/-- The same prime-power confinement holds for repeated top-endpoint hits. -/
theorem repeated_top_support_primePow_of_short_periodLcm_window
    {t d s r m : ℕ} (hsPos : 1 ≤ s) (hsr : s < r)
    (hrm : r ≤ m + 1) (hm : m < 2 * t)
    (hnd : ¬d ∣ periodLcm t)
    (hs : d ∣ 2 * periodLcm t + s)
    (hr : d ∣ 2 * periodLcm t + r) :
    ∃ p k : ℕ, Nat.Prime p ∧ d = p ^ k ∧ t < d := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hs (by
    have hH := periodLcm_pos t
    omega)
  have hdGap : d ≤ r - s :=
    channel_le_offset_sub_of_two_top_supports hd hsr hs hr
  have hgap : r - s ≤ m := by omega
  have hlt : d < 2 * t := lt_of_le_of_lt (hdGap.trans hgap) hm
  exact eq_prime_pow_of_not_dvd_periodLcm hd hlt hnd

/-- A repeated squarefree top channel in the short window is prime. -/
theorem prime_of_squarefree_repeated_top_support_in_short_periodLcm_window
    {t d s r m : ℕ} (hsq : Squarefree d)
    (hsPos : 1 ≤ s) (hsr : s < r)
    (hrm : r ≤ m + 1) (hm : m < 2 * t)
    (hnd : ¬d ∣ periodLcm t)
    (hs : d ∣ 2 * periodLcm t + s)
    (hr : d ∣ 2 * periodLcm t + r) :
    Nat.Prime d := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hs (by
    have hH := periodLcm_pos t
    omega)
  have hdGap : d ≤ r - s :=
    channel_le_offset_sub_of_two_top_supports hd hsr hs hr
  have hgap : r - s ≤ m := by omega
  exact prime_of_squarefree_not_dvd_periodLcm_lt_two_mul
    hsq hd (lt_of_le_of_lt (hdGap.trans hgap) hm) hnd

/-! ### Reversed finite-window split -/

/-- The exact binary-reversed block made only from old Möbius channels. -/
noncomputable def oldMobiusRawBlock (H J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      oldMobiusIncrement H (J + 1 + r) * 2 ^ (m - 1 - r)) +
    oldMobiusIncrement H (J + m + 1)

/-- The positive gcd-word block before multiplication by `H / rad(H)`. -/
def gcdWordRawBlock (R J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      (RepunitMobiusNumerator.gcdWordCoeff R (J + 1 + r) : ℤ) *
        2 ^ (m - 1 - r)) +
    (RepunitMobiusNumerator.gcdWordCoeff R (J + m + 1) : ℤ)

/-- The old reversed block is one fixed scale times the positive gcd-word
block. -/
theorem oldMobiusRawBlock_eq_scale_gcdWordRawBlock
    (H J m : ℕ) (hH : 0 < H) :
    oldMobiusRawBlock H J m =
      (((H / RadicalMobiusShadow.squarefreeKernel H : ℕ) : ℤ)) *
        gcdWordRawBlock (RadicalMobiusShadow.squarefreeKernel H) J m := by
  unfold oldMobiusRawBlock gcdWordRawBlock
  simp_rw [oldMobiusIncrement_eq_scale_gcdWordCoeff H _ hH, mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- The exact binary-reversed block of literal `d ∤ H` channel increments. -/
noncomputable def finiteForeignChannelRawBlock (H J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      finiteForeignChannelIncrement H (J + 1 + r) * 2 ^ (m - 1 - r)) +
    finiteForeignChannelIncrement H (J + m + 1)

/-- Exact finite-window identification of the actual reversed numerator. -/
theorem diagonalAdjacentSuffixRawBlock_eq_oldMobius_add_finiteForeign
    (t J m : ℕ) :
    diagonalAdjacentSuffixRawBlock t J m =
      oldMobiusRawBlock (periodLcm t) J m +
        finiteForeignChannelRawBlock (periodLcm t) J m := by
  unfold diagonalAdjacentSuffixRawBlock oldMobiusRawBlock
    finiteForeignChannelRawBlock
  simp_rw [diagonalWindowIncrement_eq_heightIncrement,
    diagonalHeightIncrement_eq_oldMobius_add_finiteForeign
      (periodLcm t) _ (periodLcm_pos t), add_mul]
  rw [Finset.sum_add_distrib]
  ring

/-- The actual-minus-old complement is definitionally the literal foreign
channel raw block; no unidentified production complement remains. -/
theorem diagonalAdjacentSuffixRawBlock_sub_oldMobius_eq_finiteForeign
    (t J m : ℕ) :
    diagonalAdjacentSuffixRawBlock t J m -
        oldMobiusRawBlock (periodLcm t) J m =
      finiteForeignChannelRawBlock (periodLcm t) J m := by
  rw [diagonalAdjacentSuffixRawBlock_eq_oldMobius_add_finiteForeign]
  ring

/-! ### Sparse foreign pulses and global channel aggregation -/

/-- The contribution of a fixed foreign index to a binary-reversed window. -/
noncomputable def finiteForeignChannelRawPulse (d H J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      (if d ∣ H then 0 else foreignChannelPhaseTerm d H (J + 1 + r)) *
        2 ^ (m - 1 - r)) +
    (if d ∣ H then 0 else foreignChannelPhaseTerm d H (J + m + 1))

/-! ### Prime-band four-pulse coordinates -/

/-- Binary weight of offset `s` in the `J = 0`, depth-`m` raw block.  Both
offsets `m` and `m + 1` have weight one; the latter is the terminal term. -/
def terminalBinaryWeight (m s : ℕ) : ℤ :=
  if s ≤ m then ((2 ^ (m - s) : ℕ) : ℤ) else 1

/-- A coefficient at one optional offset of the depth-`m` raw block. -/
def terminalWeightedCoeff (m s q : ℕ) : ℤ :=
  if s ≤ m + 1 then (q : ℤ) * terminalBinaryWeight m s else 0

/-- Least positive lower-support offset for a channel not dividing `H`. -/
def foreignLowerOffset (H d : ℕ) : ℕ := d - H % d

/-- Lower quotient at the least positive lower-support offset. -/
def foreignLowerQuotient (H d : ℕ) : ℕ :=
  (H + foreignLowerOffset H d) / d

/-- Whether doubling the least lower offset wraps once modulo `d`. -/
def foreignDoubleWrap (H d : ℕ) : ℕ :=
  (2 * foreignLowerOffset H d) / d

/-- Least positive top-support offset in the odd-prime band. -/
def foreignTopOffset (H d : ℕ) : ℕ :=
  2 * foreignLowerOffset H d - foreignDoubleWrap H d * d

/-- The sharp four-position value of a prime channel in a window shorter than
`2d`.  Every term is conditional because the least support itself can lie
beyond the chosen depth. -/
def primeBandFourPulseRaw (H m p : ℕ) : ℤ :=
  let u := foreignLowerOffset H p
  let q := foreignLowerQuotient H p
  let ε := foreignDoubleWrap H p
  let v := foreignTopOffset H p
  terminalWeightedCoeff m u q +
    terminalWeightedCoeff m (u + p) (q + 1) -
    terminalWeightedCoeff m v (2 * q - ε) -
    terminalWeightedCoeff m (v + p) (2 * q - ε + 1)

/-- Three lower hits cannot occur in offsets `1..m+1` once `d > t` and
`m < 2t`. -/
theorem not_three_low_supports_of_short_foreign_window
    {t d H m s r u : ℕ} (htd : t < d) (hm : m < 2 * t)
    (hsPos : 1 ≤ s) (hsr : s < r) (hru : r < u) (hu : u ≤ m + 1)
    (hs : d ∣ H + s) (hr : d ∣ H + r) (huLow : d ∣ H + u) :
    False := by
  have hdPos : 0 < d := lt_of_le_of_lt (Nat.zero_le t) htd
  have hsrGap : d ≤ r - s :=
    channel_le_offset_sub_of_two_low_supports hdPos hsr hs hr
  have hruGap : d ≤ u - r :=
    channel_le_offset_sub_of_two_low_supports hdPos hru hr huLow
  omega

/-- Three top hits cannot occur in the same short window. -/
theorem not_three_top_supports_of_short_foreign_window
    {t d H m s r u : ℕ} (htd : t < d) (hm : m < 2 * t)
    (hsPos : 1 ≤ s) (hsr : s < r) (hru : r < u) (hu : u ≤ m + 1)
    (hs : d ∣ 2 * H + s) (hr : d ∣ 2 * H + r)
    (huTop : d ∣ 2 * H + u) :
    False := by
  have hdPos : 0 < d := lt_of_le_of_lt (Nat.zero_le t) htd
  have hsrGap : d ≤ r - s :=
    channel_le_offset_sub_of_two_top_supports hdPos hsr hs hr
  have hruGap : d ≤ u - r :=
    channel_le_offset_sub_of_two_top_supports hdPos hru hr huTop
  omega

/-- A tail channel `d ≥ 2t` has at most one lower hit in the short window. -/
theorem not_two_low_supports_of_squarefree_tail_window
    {t d H m s r : ℕ} (hdt : 2 * t ≤ d) (hm : m < 2 * t)
    (hsPos : 1 ≤ s) (hsr : s < r) (hrm : r ≤ m + 1)
    (hs : d ∣ H + s) (hr : d ∣ H + r) :
    False := by
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hs (by omega)
  have hgap : d ≤ r - s :=
    channel_le_offset_sub_of_two_low_supports hdPos hsr hs hr
  omega

/-- A tail channel `d ≥ 2t` has at most one top hit in the short window. -/
theorem not_two_top_supports_of_squarefree_tail_window
    {t d H m s r : ℕ} (hdt : 2 * t ≤ d) (hm : m < 2 * t)
    (hsPos : 1 ≤ s) (hsr : s < r) (hrm : r ≤ m + 1)
    (hs : d ∣ 2 * H + s) (hr : d ∣ 2 * H + r) :
    False := by
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hs (by omega)
  have hgap : d ≤ r - s :=
    channel_le_offset_sub_of_two_top_supports hdPos hsr hs hr
  omega

/-- A positive residue `u < p` has only the representatives `u,u+p`
inside the positive interval through `2p`. -/
theorem eq_or_eq_add_of_modEq_of_pos_le_two_mul
    {p u s : ℕ} (hp : 0 < p) (huPos : 1 ≤ u) (huLt : u < p)
    (hsPos : 1 ≤ s) (hsLe : s ≤ 2 * p) (hmod : s ≡ u [MOD p]) :
    s = u ∨ s = u + p := by
  have hmod' : s % p = u := by
    change s % p = u % p at hmod
    simpa [Nat.mod_eq_of_lt huLt] using hmod
  have hsne : s ≠ 2 * p := by
    intro h
    subst s
    simp at hmod'
    omega
  have hslt : s < 2 * p := lt_of_le_of_ne hsLe hsne
  have hdivlt : s / p < 2 := by
    exact (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hslt)
  have hdecomp := Nat.div_add_mod s p
  rcases Nat.eq_zero_or_pos (s / p) with hzero | hpos
  · left
    rw [hzero, hmod'] at hdecomp
    omega
  · right
    have hone : s / p = 1 := by omega
    rw [hone, hmod'] at hdecomp
    omega

/-- Exact two-representative description of lower support in a window of
length at most `2p`. -/
theorem prime_lower_support_iff_eq_base_or_add
    {p H u q s : ℕ} (hp : Nat.Prime p)
    (huPos : 1 ≤ u) (huLt : u < p) (huEq : H + u = q * p)
    (hsPos : 1 ≤ s) (hsLe : s ≤ 2 * p) :
    p ∣ H + s ↔ s = u ∨ s = u + p := by
  constructor
  · intro hs
    have hHs : H + s ≡ 0 [MOD p] := hs.modEq_zero_nat
    have hHuDvd : p ∣ H + u := by
      rw [huEq]
      exact dvd_mul_left p q
    have hHu : H + u ≡ 0 [MOD p] := hHuDvd.modEq_zero_nat
    have hsu : s ≡ u [MOD p] :=
      Nat.ModEq.add_left_cancel' H (hHs.trans hHu.symm)
    exact eq_or_eq_add_of_modEq_of_pos_le_two_mul hp.pos huPos huLt
      hsPos hsLe hsu
  · rintro (rfl | rfl)
    · rw [huEq]
      exact dvd_mul_left p q
    · rw [show H + (u + p) = (H + u) + p by omega, huEq]
      exact ⟨q + 1, by ring⟩

/-- The top-support base and quotient forced by the lower witness and the
single-wrap equation. -/
theorem prime_top_base_eq
    {p H u v q ε : ℕ} (huPos : 1 ≤ u) (huEq : H + u = q * p)
    (hε : ε ≤ 1) (hvEq : 2 * u = v + ε * p) :
    2 * H + v = (2 * q - ε) * p := by
  have hqPos : 1 ≤ q := by
    by_contra hq
    have hqZero : q = 0 := by omega
    subst q
    simp at huEq
    omega
  have hεq : ε ≤ 2 * q := by omega
  rw [Nat.sub_mul]
  have hsum : 2 * H + v + ε * p = 2 * q * p := by
    nlinarith [huEq, hvEq]
  omega

/-- Exact two-representative description of top support in the same short
window. -/
theorem prime_top_support_iff_eq_base_or_add
    {p H u v q ε s : ℕ} (hp : Nat.Prime p)
    (huPos : 1 ≤ u) (huEq : H + u = q * p)
    (hε : ε ≤ 1) (hvPos : 1 ≤ v) (hvLt : v < p)
    (hvEq : 2 * u = v + ε * p)
    (hsPos : 1 ≤ s) (hsLe : s ≤ 2 * p) :
    p ∣ 2 * H + s ↔ s = v ∨ s = v + p := by
  apply prime_lower_support_iff_eq_base_or_add hp hvPos hvLt
    (prime_top_base_eq huPos huEq hε hvEq) hsPos hsLe

/-- Quotient values at the two lower representatives. -/
theorem prime_lower_support_quotient
    {p H u q s : ℕ} (hp : Nat.Prime p)
    (huEq : H + u = q * p) (hs : s = u ∨ s = u + p) :
    (H + s) / p = if s = u then q else q + 1 := by
  rcases hs with rfl | rfl
  · simp [huEq, hp.pos]
  · have hne : u + p ≠ u := by
      exact (Nat.lt_add_of_pos_right hp.pos).ne'
    rw [if_neg hne]
    have hadd : H + (u + p) = (q + 1) * p := by
      calc
        H + (u + p) = (H + u) + p := by omega
        _ = q * p + p := by rw [huEq]
        _ = (q + 1) * p := by ring
    rw [hadd]
    simp [hp.pos]

/-- Quotient values at the two top representatives. -/
theorem prime_top_support_quotient
    {p H u v q ε s : ℕ} (hp : Nat.Prime p)
    (huPos : 1 ≤ u) (huEq : H + u = q * p)
    (hε : ε ≤ 1) (hvEq : 2 * u = v + ε * p)
    (hs : s = v ∨ s = v + p) :
    (2 * H + s) / p =
      if s = v then 2 * q - ε else 2 * q - ε + 1 := by
  have hbase := prime_top_base_eq huPos huEq hε hvEq
  rcases hs with rfl | rfl
  · simp [hbase, hp.pos]
  · have hne : v + p ≠ v := by
      exact (Nat.lt_add_of_pos_right hp.pos).ne'
    rw [if_neg hne]
    rw [show 2 * H + (v + p) = (2 * q - ε + 1) * p by
      rw [show 2 * H + (v + p) = (2 * H + v) + p by omega, hbase]
      ring]
    simp [hp.pos]

/-- Old divisor channels contribute no foreign raw pulse. -/
theorem finiteForeignChannelRawPulse_eq_zero_of_dvd
    {d H J m : ℕ} (hdH : d ∣ H) :
    finiteForeignChannelRawPulse d H J m = 0 := by
  simp [finiteForeignChannelRawPulse, hdH]

/-- A nonzero raw pulse has a squarefree index; nonsquarefree channels vanish
pointwise before any cancellation between offsets is considered. -/
theorem squarefree_of_finiteForeignChannelRawPulse_ne_zero
    {d H J m : ℕ} (hne : finiteForeignChannelRawPulse d H J m ≠ 0) :
    Squarefree d := by
  by_contra hnotSquarefree
  have hmu : ArithmeticFunction.moebius d = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnotSquarefree
  exact hne (by
    simp [finiteForeignChannelRawPulse, foreignChannelPhaseTerm, hmu])

/-- At an LCM height, every positive channel carrying a nonzero raw pulse lies
strictly above the scale. -/
theorem lt_of_finiteForeignChannelRawPulse_periodLcm_ne_zero
    {t d J m : ℕ} (hd : 0 < d)
    (hne : finiteForeignChannelRawPulse d (periodLcm t) J m ≠ 0) :
    t < d := by
  apply lt_of_not_dvd_periodLcm hd
  intro hdH
  exact hne (finiteForeignChannelRawPulse_eq_zero_of_dvd hdH)

/-- A local phase sum may be enlarged to any common cutoff beyond its exact
endpoint cutoff; the added channels have no endpoint support. -/
theorem finiteForeignChannelIncrement_eq_enlarged_phaseSum
    {H s D : ℕ} (hH : 0 < H) (hcut : 2 * H + s + 1 ≤ D) :
    finiteForeignChannelIncrement H s =
      ∑ d ∈ Finset.range D,
        if d ∣ H then 0 else foreignChannelPhaseTerm d H s := by
  rw [finiteForeignChannelIncrement_eq_phaseSum]
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hd) hcut)
  · intro d hdD hdLocal
    have hdLower : 2 * H + s + 1 ≤ d := by
      exact Nat.not_lt.mp (fun h => hdLocal (Finset.mem_range.mpr h))
    by_cases hdH : d ∣ H
    · simp [hdH]
    · have hTop : ¬d ∣ 2 * H + s := by
        intro hdiv
        have hdle : d ≤ 2 * H + s :=
          Nat.le_of_dvd (by omega) hdiv
        omega
      have hLow : ¬d ∣ H + s := by
        intro hdiv
        have hdle : d ≤ H + s := Nat.le_of_dvd (by omega) hdiv
        omega
      simp [hdH, foreignChannelPhaseTerm, hTop, hLow]

/-- Exact global channel swap for the finite foreign raw block.  Cancellation
can now be studied one channel at a time, with one common finite cutoff. -/
theorem finiteForeignChannelRawBlock_eq_sum_rawPulses
    (H J m : ℕ) (hH : 0 < H) :
    finiteForeignChannelRawBlock H J m =
      ∑ d ∈ Finset.range (2 * H + J + m + 2),
        finiteForeignChannelRawPulse d H J m := by
  let D := 2 * H + J + m + 2
  have hinc : ∀ r ∈ Finset.range m,
      finiteForeignChannelIncrement H (J + 1 + r) =
        ∑ d ∈ Finset.range D,
          if d ∣ H then 0
          else foreignChannelPhaseTerm d H (J + 1 + r) := by
    intro r hr
    apply finiteForeignChannelIncrement_eq_enlarged_phaseSum hH
    have hrm := Finset.mem_range.mp hr
    dsimp [D]
    omega
  have hterminal :
      finiteForeignChannelIncrement H (J + m + 1) =
        ∑ d ∈ Finset.range D,
          if d ∣ H then 0
          else foreignChannelPhaseTerm d H (J + m + 1) := by
    apply finiteForeignChannelIncrement_eq_enlarged_phaseSum hH
    dsimp [D]
    omega
  unfold finiteForeignChannelRawBlock finiteForeignChannelRawPulse
  change
    (∑ r ∈ Finset.range m,
        finiteForeignChannelIncrement H (J + 1 + r) *
          2 ^ (m - 1 - r)) +
      finiteForeignChannelIncrement H (J + m + 1) =
        ∑ d ∈ Finset.range D,
          ((∑ r ∈ Finset.range m,
              (if d ∣ H then 0
                else foreignChannelPhaseTerm d H (J + 1 + r)) *
                2 ^ (m - 1 - r)) +
            (if d ∣ H then 0
              else foreignChannelPhaseTerm d H (J + m + 1)))
  calc
    (∑ r ∈ Finset.range m,
        finiteForeignChannelIncrement H (J + 1 + r) *
          2 ^ (m - 1 - r)) +
        finiteForeignChannelIncrement H (J + m + 1) =
      (∑ r ∈ Finset.range m,
          (∑ d ∈ Finset.range D,
            if d ∣ H then 0
            else foreignChannelPhaseTerm d H (J + 1 + r)) *
              2 ^ (m - 1 - r)) +
        finiteForeignChannelIncrement H (J + m + 1) := by
            apply congrArg
              (fun z : ℤ => z + finiteForeignChannelIncrement H (J + m + 1))
            apply Finset.sum_congr rfl
            intro r hr
            rw [hinc r hr]
    _ =
      (∑ r ∈ Finset.range m,
          (∑ d ∈ Finset.range D,
            if d ∣ H then 0
            else foreignChannelPhaseTerm d H (J + 1 + r)) *
              2 ^ (m - 1 - r)) +
        ∑ d ∈ Finset.range D,
          if d ∣ H then 0
          else foreignChannelPhaseTerm d H (J + m + 1) := by
            rw [hterminal]
    _ =
      (∑ r ∈ Finset.range m,
          ∑ d ∈ Finset.range D,
            (if d ∣ H then 0
              else foreignChannelPhaseTerm d H (J + 1 + r)) *
                2 ^ (m - 1 - r)) +
        ∑ d ∈ Finset.range D,
          if d ∣ H then 0
          else foreignChannelPhaseTerm d H (J + m + 1) := by
            apply congrArg
              (fun z : ℤ => z +
                ∑ d ∈ Finset.range D,
                  if d ∣ H then 0
                  else foreignChannelPhaseTerm d H (J + m + 1))
            apply Finset.sum_congr rfl
            intro r _hr
            rw [Finset.sum_mul]
    _ =
      (∑ d ∈ Finset.range D,
          ∑ r ∈ Finset.range m,
            (if d ∣ H then 0
              else foreignChannelPhaseTerm d H (J + 1 + r)) *
                2 ^ (m - 1 - r)) +
        ∑ d ∈ Finset.range D,
          if d ∣ H then 0
          else foreignChannelPhaseTerm d H (J + m + 1) := by
            rw [Finset.sum_comm]
    _ =
      ∑ d ∈ Finset.range D,
        ((∑ r ∈ Finset.range m,
            (if d ∣ H then 0
              else foreignChannelPhaseTerm d H (J + 1 + r)) *
                2 ^ (m - 1 - r)) +
          (if d ∣ H then 0
            else foreignChannelPhaseTerm d H (J + m + 1))) := by
              rw [← Finset.sum_add_distrib]

/-- Exact cancellation normal form: the actual reversed numerator is the
positive gcd-word block at one fixed LCM scale plus the global finite sum of
sparse foreign raw pulses. -/
theorem diagonalAdjacentSuffixRawBlock_eq_scaledGcdWord_add_sum_foreignRawPulses
    (t J m : ℕ) :
    diagonalAdjacentSuffixRawBlock t J m =
      (((periodLcm t /
          RadicalMobiusShadow.squarefreeKernel (periodLcm t) : ℕ) : ℤ)) *
        gcdWordRawBlock
          (RadicalMobiusShadow.squarefreeKernel (periodLcm t)) J m +
      ∑ d ∈ Finset.range (2 * periodLcm t + J + m + 2),
        finiteForeignChannelRawPulse d (periodLcm t) J m := by
  rw [diagonalAdjacentSuffixRawBlock_eq_oldMobius_add_finiteForeign,
    oldMobiusRawBlock_eq_scale_gcdWordRawBlock _ _ _ (periodLcm_pos t),
    finiteForeignChannelRawBlock_eq_sum_rawPulses _ _ _ (periodLcm_pos t)]

/-- Growing the raw adjacent block by one binary place doubles the retained
block, removes one copy of the old terminal correction, and appends the new
terminal correction.  This exact cocycle is independent of any LCM-jump
hypothesis. -/
theorem diagonalAdjacentSuffixRawBlock_succ_depth (t J m : ℕ) :
    diagonalAdjacentSuffixRawBlock t J (m + 1) =
      2 * diagonalAdjacentSuffixRawBlock t J m -
        diagonalWindowIncrement t (J + m + 1) +
        diagonalWindowIncrement t (J + m + 2) := by
  unfold diagonalAdjacentSuffixRawBlock
  rw [Finset.sum_range_succ]
  have hsum :
      (∑ r ∈ Finset.range m,
          diagonalWindowIncrement t (J + 1 + r) *
            2 ^ (m + 1 - 1 - r)) =
        2 * ∑ r ∈ Finset.range m,
          diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r) := by
    calc
      (∑ r ∈ Finset.range m,
          diagonalWindowIncrement t (J + 1 + r) *
            2 ^ (m + 1 - 1 - r)) =
          ∑ r ∈ Finset.range m,
            2 * (diagonalWindowIncrement t (J + 1 + r) *
              2 ^ (m - 1 - r)) := by
            apply Finset.sum_congr rfl
            intro r hr
            have hrm : r < m := Finset.mem_range.mp hr
            rw [show m + 1 - 1 - r = (m - 1 - r) + 1 by omega,
              pow_succ]
            ring
      _ = 2 * ∑ r ∈ Finset.range m,
          diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r) := by
            rw [Finset.mul_sum]
  rw [hsum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  ring

/-- The two-depth form of the raw-block cocycle.  This is the natural
base-four recurrence used at odd canonical depths. -/
theorem diagonalAdjacentSuffixRawBlock_add_two (t J m : ℕ) :
    diagonalAdjacentSuffixRawBlock t J (m + 2) =
      4 * diagonalAdjacentSuffixRawBlock t J m -
        2 * diagonalWindowIncrement t (J + m + 1) +
        diagonalWindowIncrement t (J + m + 2) +
        diagonalWindowIncrement t (J + m + 3) := by
  rw [show m + 2 = (m + 1) + 1 by omega,
    diagonalAdjacentSuffixRawBlock_succ_depth,
    diagonalAdjacentSuffixRawBlock_succ_depth]
  ring

/-- Exact scalar normal form: the adjacent residue is the unreduced weighted
increment block modulo its dyadic modulus. -/
theorem diagonalAdjacentSuffixResidue_eq_rawBlock (t J m : ℕ) :
    diagonalAdjacentSuffixResidue t J m =
      diagonalAdjacentSuffixRawBlock t J m % 2 ^ m := by
  rw [diagonalAdjacentSuffixResidue_eq_terminal_corrected,
    diagonalSuffixResidue_eq_increment_sum]
  unfold diagonalAdjacentSuffixRawBlock
  apply Int.ModEq.eq
  exact (Int.mod_modEq _ _).add (Int.ModEq.refl _)

/-- Residue form of the parity-free one-depth cocycle.  Doubling lifts every
discarded multiple of the old modulus to the new modulus. -/
theorem diagonalAdjacentSuffixResidue_succ_depth (t J m : ℕ) :
    diagonalAdjacentSuffixResidue t J (m + 1) =
      (2 * diagonalAdjacentSuffixResidue t J m -
        diagonalWindowIncrement t (J + m + 1) +
        diagonalWindowIncrement t (J + m + 2)) % 2 ^ (m + 1) := by
  rw [diagonalAdjacentSuffixResidue_eq_rawBlock,
    diagonalAdjacentSuffixResidue_eq_rawBlock,
    diagonalAdjacentSuffixRawBlock_succ_depth]
  let R : ℤ := diagonalAdjacentSuffixRawBlock t J m
  let M : ℤ := 2 ^ m
  change (2 * R - diagonalWindowIncrement t (J + m + 1) +
      diagonalWindowIncrement t (J + m + 2)) % 2 ^ (m + 1) =
    (2 * (R % M) - diagonalWindowIncrement t (J + m + 1) +
      diagonalWindowIncrement t (J + m + 2)) % 2 ^ (m + 1)
  have hdecomp : M * (R / M) + R % M = R :=
    Int.mul_ediv_add_emod R M
  have hpow : (2 : ℤ) ^ (m + 1) = 2 * M := by
    dsimp [M]
    rw [pow_succ]
    ring
  have hrewrite :
      2 * R - diagonalWindowIncrement t (J + m + 1) +
          diagonalWindowIncrement t (J + m + 2) =
        (2 * (R % M) - diagonalWindowIncrement t (J + m + 1) +
          diagonalWindowIncrement t (J + m + 2)) +
            (2 * M) * (R / M) := by
    have hscaled := congrArg (fun z : ℤ =>
      2 * z - diagonalWindowIncrement t (J + m + 1) +
        diagonalWindowIncrement t (J + m + 2)) hdecomp
    calc
      2 * R - diagonalWindowIncrement t (J + m + 1) +
          diagonalWindowIncrement t (J + m + 2) =
        2 * (M * (R / M) + R % M) -
          diagonalWindowIncrement t (J + m + 1) +
          diagonalWindowIncrement t (J + m + 2) := hscaled.symm
      _ = (2 * (R % M) - diagonalWindowIncrement t (J + m + 1) +
          diagonalWindowIncrement t (J + m + 2)) +
            (2 * M) * (R / M) := by ring
  rw [hpow, hrewrite, Int.add_mul_emod_self_left]

/-- Target-depth form of the one-step cocycle at the canonical cut `J = 0`.
The only new arithmetic datum is `diagonalTargetDepthCorrection t m`. -/
theorem diagonalAdjacentSuffixResidue_target_depth
    {t m : ℕ} (hm : 0 < m) :
    diagonalAdjacentSuffixResidue t 0 m =
      (2 * diagonalAdjacentSuffixResidue t 0 (m - 1) +
        diagonalTargetDepthCorrection t m) % 2 ^ m := by
  have h := diagonalAdjacentSuffixResidue_succ_depth t 0 (m - 1)
  have hm1 : m - 1 + 1 = m := by omega
  rw [hm1] at h
  simpa only [diagonalTargetDepthCorrection, Nat.zero_add,
    show m - 1 + 1 = m by omega, show m - 1 + 2 = m + 1 by omega,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

/-- Sharp adjacent-gap geometry.  The constant is exactly the sum of the
right edge width at cut `J` and the left edge width at cut `J + 1` (equally,
the other cross-edge sum). -/
theorem diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap_sharp
    {t J m : ℕ}
    (hgap :
      let B : ℤ := 3 * periodLcm t + 2 * (J + m) + 5
      B < diagonalAdjacentSuffixResidue t J m ∧
        diagonalAdjacentSuffixResidue t J m < 2 ^ m - B) :
    diagonalFreshLossResidueCert t (J + m) ∨
      diagonalFreshLossResidueCert t (J + 1 + m) := by
  let H : ℤ := periodLcm t
  let M : ℤ := 2 ^ m
  let x : ℤ := diagonalSuffixResidue t J m
  let y : ℤ := diagonalSuffixResidue t (J + 1) m
  let d : ℤ := diagonalAdjacentSuffixResidue t J m
  let A0 : ℤ := H + (J + m) + 2
  let C0 : ℤ := 2 * H + (J + m) + 2
  let A1 : ℤ := H + (J + 1 + m) + 2
  let C1 : ℤ := 2 * H + (J + 1 + m) + 2
  let B : ℤ := 3 * H + 2 * (J + m) + 5
  have hgap' : B < d ∧ d < M - B := by
    simpa [B, d, M, H] using hgap
  have hMpos : 0 < M := by simp [M]
  have hx0 : 0 ≤ x := by
    unfold x diagonalSuffixResidue
    exact Int.emod_nonneg _ hMpos.ne'
  have hxM : x < M := by
    unfold x diagonalSuffixResidue
    exact Int.emod_lt_of_pos _ hMpos
  have hy0 : 0 ≤ y := by
    unfold y diagonalSuffixResidue
    exact Int.emod_nonneg _ hMpos.ne'
  have hyM : y < M := by
    unfold y diagonalSuffixResidue
    exact Int.emod_lt_of_pos _ hMpos
  have hd : d = (y - x) % M := by rfl
  have hd_of_le (hxy : x ≤ y) : d = y - x := by
    rw [hd, Int.emod_eq_of_lt] <;> omega
  have hd_of_gt (hyx : y < x) : d = M + y - x := by
    rw [hd, show y - x = (M + y - x) - M by ring,
      Int.sub_emod_right, Int.emod_eq_of_lt] <;> omega
  by_cases hxCentral : A0 < x ∧ x < M - C0
  · left
    apply diagonalFreshLossResidueCert_of_suffix_central
    · simpa [A0, x, H] using hxCentral.1
    · simpa [C0, x, M, H] using hxCentral.2
  by_cases hyCentral : A1 < y ∧ y < M - C1
  · right
    apply diagonalFreshLossResidueCert_of_suffix_central
    · simpa [A1, y, H, Nat.add_assoc] using hyCentral.1
    · simpa [C1, y, M, H, Nat.add_assoc] using hyCentral.2
  exfalso
  have hxEdge : x ≤ A0 ∨ M - C0 ≤ x := by omega
  have hyEdge : y ≤ A1 ∨ M - C1 ≤ y := by omega
  rcases hxEdge with hxlo | hxhi <;> rcases hyEdge with hylo | hyhi
  · by_cases hxy : x ≤ y
    · rw [hd_of_le hxy] at hgap'
      omega
    · rw [hd_of_gt (by omega)] at hgap'
      omega
  · have hxy : x ≤ y := by omega
    rw [hd_of_le hxy] at hgap'
    omega
  · have hyx : y < x := by omega
    rw [hd_of_gt hyx] at hgap'
    omega
  · by_cases hxy : x ≤ y
    · rw [hd_of_le hxy] at hgap'
      omega
    · rw [hd_of_gt (by omega)] at hgap'
      omega

/-- Symmetric adjacent-gap geometry.  Spending one extra LCM height in the
cross-edge budget preserves a `2H` exclusion on both sides of whichever
adjacent suffix is central. -/
theorem diagonalSymmetricResidueCert_or_of_adjacent_suffix_gap
    {t J m : ℕ}
    (hgap :
      let B : ℤ := 4 * periodLcm t + 2 * (J + m) + 5
      B < diagonalAdjacentSuffixResidue t J m ∧
        diagonalAdjacentSuffixResidue t J m < 2 ^ m - B) :
    diagonalSymmetricResidueCert t (J + m) ∨
      diagonalSymmetricResidueCert t (J + 1 + m) := by
  let H : ℤ := periodLcm t
  let M : ℤ := 2 ^ m
  let x : ℤ := diagonalSuffixResidue t J m
  let y : ℤ := diagonalSuffixResidue t (J + 1) m
  let d : ℤ := diagonalAdjacentSuffixResidue t J m
  let E0 : ℤ := 2 * H + (J + m) + 2
  let E1 : ℤ := 2 * H + (J + 1 + m) + 2
  let B : ℤ := 4 * H + 2 * (J + m) + 5
  have hgap' : B < d ∧ d < M - B := by
    simpa [B, d, M, H] using hgap
  have hMpos : 0 < M := by simp [M]
  have hx0 : 0 ≤ x := by
    unfold x diagonalSuffixResidue
    exact Int.emod_nonneg _ hMpos.ne'
  have hxM : x < M := by
    unfold x diagonalSuffixResidue
    exact Int.emod_lt_of_pos _ hMpos
  have hy0 : 0 ≤ y := by
    unfold y diagonalSuffixResidue
    exact Int.emod_nonneg _ hMpos.ne'
  have hyM : y < M := by
    unfold y diagonalSuffixResidue
    exact Int.emod_lt_of_pos _ hMpos
  have hd : d = (y - x) % M := by rfl
  have hd_of_le (hxy : x ≤ y) : d = y - x := by
    rw [hd, Int.emod_eq_of_lt] <;> omega
  have hd_of_gt (hyx : y < x) : d = M + y - x := by
    rw [hd, show y - x = (M + y - x) - M by ring,
      Int.sub_emod_right, Int.emod_eq_of_lt] <;> omega
  by_cases hxCentral : E0 < x ∧ x < M - E0
  · left
    apply diagonalSymmetricResidueCert_of_suffix_central
    · simpa [E0, x, H] using hxCentral.1
    · simpa [E0, x, M, H] using hxCentral.2
  by_cases hyCentral : E1 < y ∧ y < M - E1
  · right
    apply diagonalSymmetricResidueCert_of_suffix_central
    · simpa [E1, y, H, Nat.add_assoc] using hyCentral.1
    · simpa [E1, y, M, H, Nat.add_assoc] using hyCentral.2
  exfalso
  have hxEdge : x ≤ E0 ∨ M - E0 ≤ x := by omega
  have hyEdge : y ≤ E1 ∨ M - E1 ≤ y := by omega
  rcases hxEdge with hxlo | hxhi <;> rcases hyEdge with hylo | hyhi
  · by_cases hxy : x ≤ y
    · rw [hd_of_le hxy] at hgap'
      omega
    · rw [hd_of_gt (by omega)] at hgap'
      omega
  · have hxy : x ≤ y := by omega
    rw [hd_of_le hxy] at hgap'
    omega
  · have hyx : y < x := by omega
    rw [hd_of_gt hyx] at hgap'
    omega
  · by_cases hxy : x ≤ y
    · rw [hd_of_le hxy] at hgap'
      omega
    · rw [hd_of_gt (by omega)] at hgap'
      omega

/-- If the modular displacement between adjacent suffixes exceeds the sum of
their two edge widths in both directions, then at least one suffix gives a
full-depth fresh-loss certificate. -/
theorem diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap
    {t J m : ℕ}
    (hgap :
      let B : ℤ := 3 * periodLcm t + 2 * (J + m + 3)
      B < diagonalAdjacentSuffixResidue t J m ∧
        diagonalAdjacentSuffixResidue t J m < 2 ^ m - B) :
    diagonalFreshLossResidueCert t (J + m) ∨
      diagonalFreshLossResidueCert t (J + 1 + m) := by
  apply diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap_sharp
  dsimp only at hgap ⊢
  omega

/-- A fixed `1/32` circular gap dominates the adjacent edge budget. -/
theorem diagonalFreshLossResidueCert_or_of_adjacent_dyadic_gap
    {t J m : ℕ}
    (hm : 5 ≤ m)
    (hwidth :
      32 * (3 * periodLcm t + 2 * (J + m + 3) : ℤ) < 2 ^ m)
    (hlo : 2 ^ (m - 5) ≤ diagonalAdjacentSuffixResidue t J m)
    (hhi : diagonalAdjacentSuffixResidue t J m
      ≤ 2 ^ m - 2 ^ (m - 5)) :
    diagonalFreshLossResidueCert t (J + m) ∨
      diagonalFreshLossResidueCert t (J + 1 + m) := by
  apply diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap
  dsimp only
  have hpow : (2 : ℤ) ^ m = 32 * 2 ^ (m - 5) := by
    calc
      (2 : ℤ) ^ m = 2 ^ ((m - 5) + 5) := by rw [Nat.sub_add_cancel hm]
      _ = 32 * 2 ^ (m - 5) := by rw [pow_add]; norm_num; ring
  rw [hpow] at hwidth
  constructor <;> omega

/-- The same fixed `1/32` circular band yields a symmetric certificate when
its width receipt retains the additional LCM-height margin. -/
theorem diagonalSymmetricResidueCert_or_of_adjacent_dyadic_gap
    {t J m : ℕ}
    (hm : 5 ≤ m)
    (hwidth :
      32 * (4 * periodLcm t + 2 * (J + m) + 5 : ℤ) < 2 ^ m)
    (hlo : 2 ^ (m - 5) ≤ diagonalAdjacentSuffixResidue t J m)
    (hhi : diagonalAdjacentSuffixResidue t J m
      ≤ 2 ^ m - 2 ^ (m - 5)) :
    diagonalSymmetricResidueCert t (J + m) ∨
      diagonalSymmetricResidueCert t (J + 1 + m) := by
  apply diagonalSymmetricResidueCert_or_of_adjacent_suffix_gap
  dsimp only
  have hpow : (2 : ℤ) ^ m = 32 * 2 ^ (m - 5) := by
    calc
      (2 : ℤ) ^ m = 2 ^ ((m - 5) + 5) := by rw [Nat.sub_add_cancel hm]
      _ = 32 * 2 ^ (m - 5) := by rw [pow_add]; norm_num; ring
  rw [hpow] at hwidth
  constructor <;> omega

/-- The canonical adjacent-suffix depth: ten guard bits beyond the binary
scale of the LCM height.  At this depth the analytic width budget is automatic;
the only remaining arithmetic input is centrality of the adjacent residue. -/
def canonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  Nat.log2 (periodLcm t) + 10

/-- From `t ≥ 3`, the canonical depth has enough guard bits and its fixed
`1/32` central band dominates the whole adjacent-suffix edge budget. -/
theorem canonicalAdjacentSuffixDepth_width {t : ℕ} (ht : 3 ≤ t) :
    5 ≤ canonicalAdjacentSuffixDepth t ∧
      32 * (3 * periodLcm t +
        2 * (canonicalAdjacentSuffixDepth t + 3) : ℤ) <
        2 ^ canonicalAdjacentSuffixDepth t := by
  let H := periodLcm t
  let m := canonicalAdjacentSuffixDepth t
  have hH : 3 ≤ H := by
    exact ht.trans (le_periodLcm t)
  have hlog_le : Nat.log2 H ≤ H := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_le_self 2 H
  have hHpow : H < 2 ^ (Nat.log2 H + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two H
  have hm : m = Nat.log2 H + 10 := by
    simp [m, canonicalAdjacentSuffixDepth, H]
  have hbudget : 3 * H + 2 * (m + 3) < 16 * H := by
    omega
  have hscaled : 32 * (3 * H + 2 * (m + 3)) < 512 * H := by
    omega
  have hpow_eq : 512 * 2 ^ (Nat.log2 H + 1) = 2 ^ m := by
    rw [hm, show Nat.log2 H + 10 = (Nat.log2 H + 1) + 9 by omega,
      pow_add]
    norm_num
    ring
  have hwidthNat : 32 * (3 * H + 2 * (m + 3)) < 2 ^ m := by
    calc
      32 * (3 * H + 2 * (m + 3)) < 512 * H := hscaled
      _ < 512 * 2 ^ (Nat.log2 H + 1) :=
        (Nat.mul_lt_mul_left (a := 512) (by norm_num)).2 hHpow
      _ = 2 ^ m := hpow_eq
  constructor
  · change 5 ≤ m
    rw [hm]
    omega
  · change 32 * (3 * (H : ℤ) + 2 * (m + 3)) < 2 ^ m
    exact_mod_cast hwidthNat

/-- The ten-bit canonical guard also pays for the stronger symmetric `2H`
edge budget; this is the margin retained by the actual-LCM arithmetic route. -/
theorem canonicalAdjacentSuffixDepth_symmetric_width
    {t : ℕ} (ht : 3 ≤ t) :
    5 ≤ canonicalAdjacentSuffixDepth t ∧
      32 * (4 * periodLcm t +
        2 * canonicalAdjacentSuffixDepth t + 5 : ℤ) <
        2 ^ canonicalAdjacentSuffixDepth t := by
  let H := periodLcm t
  let m := canonicalAdjacentSuffixDepth t
  have hH : 3 ≤ H := ht.trans (le_periodLcm t)
  have hlog_le : Nat.log2 H ≤ H := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_le_self 2 H
  have hHpow : H < 2 ^ (Nat.log2 H + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two H
  have hm : m = Nat.log2 H + 10 := by
    simp [m, canonicalAdjacentSuffixDepth, H]
  have hbudget : 4 * H + 2 * m + 5 < 16 * H := by
    omega
  have hscaled : 32 * (4 * H + 2 * m + 5) < 512 * H := by
    omega
  have hpow_eq : 512 * 2 ^ (Nat.log2 H + 1) = 2 ^ m := by
    rw [hm, show Nat.log2 H + 10 = (Nat.log2 H + 1) + 9 by omega,
      pow_add]
    norm_num
    ring
  have hwidthNat : 32 * (4 * H + 2 * m + 5) < 2 ^ m := by
    calc
      32 * (4 * H + 2 * m + 5) < 512 * H := hscaled
      _ < 512 * 2 ^ (Nat.log2 H + 1) :=
        (Nat.mul_lt_mul_left (a := 512) (by norm_num)).2 hHpow
      _ = 2 ^ m := hpow_eq
  constructor
  · change 5 ≤ m
    rw [hm]
    omega
  · change 32 * (4 * (H : ℤ) + 2 * m + 5) < 2 ^ m
    exact_mod_cast hwidthNat

/-- The elementary one-step correction envelope itself is strictly smaller
than the canonical `1/32` edge.  This is the quantitative bridge from the
sharp margin producer to the cleaner strong-band corollary. -/
theorem diagonalTargetDepthCorrectionEnvelope_lt_canonical_edge
    {t : ℕ} (ht : 3 ≤ t) :
    (3 * periodLcm t + 2 * canonicalAdjacentSuffixDepth t + 1 : ℤ) <
      (2 : ℤ) ^ (canonicalAdjacentSuffixDepth t - 5) := by
  let m := canonicalAdjacentSuffixDepth t
  obtain ⟨hm, hwidth⟩ := canonicalAdjacentSuffixDepth_width ht
  have hpow : (2 : ℤ) ^ m = 32 * 2 ^ (m - 5) := by
    calc
      (2 : ℤ) ^ m = 2 ^ ((m - 5) + 5) := by rw [Nat.sub_add_cancel hm]
      _ = 32 * 2 ^ (m - 5) := by rw [pow_add]; norm_num; ring
  change (3 * periodLcm t + 2 * m + 1 : ℤ) < (2 : ℤ) ^ (m - 5)
  change 32 * (3 * (periodLcm t : ℤ) + 2 * (m + 3)) <
    (2 : ℤ) ^ m at hwidth
  rw [hpow] at hwidth
  have hbudget :
      (3 * periodLcm t + 2 * m + 1 : ℤ) <
        3 * periodLcm t + 2 * (m + 3) := by
    push_cast
    omega
  have hedge :
      (3 * periodLcm t + 2 * (m + 3) : ℤ) < 2 ^ (m - 5) := by
    omega
  exact hbudget.trans hedge

/-- At the canonical guard-bit depth, the parity-free one-step correction is
strictly smaller than the final `1/32` edge. -/
theorem abs_diagonalTargetDepthCorrection_lt_canonical_edge
    {t : ℕ} (ht : 3 ≤ t) :
    |diagonalTargetDepthCorrection t (canonicalAdjacentSuffixDepth t)| <
      (2 : ℤ) ^ (canonicalAdjacentSuffixDepth t - 5) :=
  (abs_diagonalTargetDepthCorrection_le
      t (canonicalAdjacentSuffixDepth t)).trans_lt
    (diagonalTargetDepthCorrectionEnvelope_lt_canonical_edge ht)

/-- Exact unwrapping of the target-depth modular centrality test.  If the old
residue is represented in `[0, 2^(m-1))` and the appended correction is
smaller than the edge, neither a negative nor a positive wrap can land in the
central interval.  Thus modular centrality is equivalent to the two literal
integer inequalities on `2*d + C`. -/
theorem baseTwoTargetResidue_central_iff_unwrapped
    {m : ℕ} {d C : ℤ} (hm : 5 ≤ m)
    (hd0 : 0 ≤ d) (hdhi : d < (2 : ℤ) ^ (m - 1))
    (hC : |C| < (2 : ℤ) ^ (m - 5)) :
    ((2 : ℤ) ^ (m - 5) ≤ (2 * d + C) % 2 ^ m ∧
      (2 * d + C) % 2 ^ m ≤ 2 ^ m - 2 ^ (m - 5)) ↔
    ((2 : ℤ) ^ (m - 5) ≤ 2 * d + C ∧
      2 * d + C ≤ 2 ^ m - 2 ^ (m - 5)) := by
  let N : ℤ := 2 ^ m
  let M : ℤ := 2 ^ (m - 1)
  let e : ℤ := 2 ^ (m - 5)
  let x : ℤ := 2 * d + C
  have hepos : 0 < e := by dsimp [e]; positivity
  have hNedge : N = 32 * e := by
    dsimp [N, e]
    calc
      (2 : ℤ) ^ m = 2 ^ ((m - 5) + 5) := by rw [Nat.sub_add_cancel hm]
      _ = 32 * 2 ^ (m - 5) := by rw [pow_add]; norm_num; ring
  have heN : e < N := by rw [hNedge]; linarith
  have hm1 : 1 ≤ m := by omega
  have hNhalf : N = 2 * M := by
    dsimp [N, M]
    calc
      (2 : ℤ) ^ m = 2 ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel hm1]
      _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; ring
  have habs := abs_lt.mp hC
  have hxlo : -e < x := by dsimp [x]; linarith
  have hxhi : x < N + e := by
    dsimp [x] at *
    rw [hNhalf]
    linarith
  constructor
  · intro hcentral
    have hx0 : 0 ≤ x := by
      by_contra hnot
      have hxneg : x < 0 := by omega
      have hxplus0 : 0 ≤ x + N := by linarith
      have hxplusN : x + N < N := by linarith
      have hmod : x % N = x + N := by
        calc
          x % N = ((x + N) - N) % N := by congr 1 <;> ring
          _ = (x + N) % N := Int.sub_emod_right _ _
          _ = x + N := Int.emod_eq_of_lt hxplus0 hxplusN
      change e ≤ x % N ∧ x % N ≤ N - e at hcentral
      rw [hmod] at hcentral
      linarith
    have hxN : x < N := by
      by_contra hnot
      have hNle : N ≤ x := by omega
      have hxsub0 : 0 ≤ x - N := by linarith
      have hxsubN : x - N < N := by linarith
      have hmod : x % N = x - N := by
        calc
          x % N = ((x - N) + N) % N := by congr 1 <;> ring
          _ = (x - N) % N := Int.add_emod_right _ _
          _ = x - N := Int.emod_eq_of_lt hxsub0 hxsubN
      change e ≤ x % N ∧ x % N ≤ N - e at hcentral
      rw [hmod] at hcentral
      linarith
    have hfix : x % N = x := Int.emod_eq_of_lt hx0 hxN
    change e ≤ x % N ∧ x % N ≤ N - e at hcentral
    rw [hfix] at hcentral
    exact hcentral
  · intro hx
    have hx0 : 0 ≤ x := by linarith [hx.1, hepos]
    have hxN : x < N := by linarith [hx.2, hepos]
    have hfix : x % N = x := Int.emod_eq_of_lt hx0 hxN
    change e ≤ x % N ∧ x % N ≤ N - e
    rw [hfix]
    exact hx

/-- Canonical specialization of `baseTwoTargetResidue_central_iff_unwrapped`.
This is the exact parity-complete residual: canonical centrality holds if and
only if the doubled penultimate residue plus its signed correction lies in the
target central interval. -/
theorem canonicalAdjacentSuffixResidue_central_iff_penultimate_exact
    {t : ℕ} (ht : 3 ≤ t) :
    ((2 : ℤ) ^ (canonicalAdjacentSuffixDepth t - 5) ≤
        diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ∧
      diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ≤
        2 ^ canonicalAdjacentSuffixDepth t -
          2 ^ (canonicalAdjacentSuffixDepth t - 5)) ↔
    ((2 : ℤ) ^ (canonicalAdjacentSuffixDepth t - 5) ≤
        2 * diagonalAdjacentSuffixResidue t 0
            (canonicalAdjacentSuffixDepth t - 1) +
          diagonalTargetDepthCorrection t (canonicalAdjacentSuffixDepth t) ∧
      2 * diagonalAdjacentSuffixResidue t 0
            (canonicalAdjacentSuffixDepth t - 1) +
          diagonalTargetDepthCorrection t (canonicalAdjacentSuffixDepth t) ≤
        2 ^ canonicalAdjacentSuffixDepth t -
          2 ^ (canonicalAdjacentSuffixDepth t - 5)) := by
  obtain ⟨hm, _hwidth⟩ := canonicalAdjacentSuffixDepth_width ht
  rw [diagonalAdjacentSuffixResidue_target_depth (by omega)]
  apply baseTwoTargetResidue_central_iff_unwrapped hm
  · unfold diagonalAdjacentSuffixResidue
    exact Int.emod_nonneg _ (by positivity)
  · unfold diagonalAdjacentSuffixResidue
    exact Int.emod_lt_of_pos _ (by positivity)
  · exact abs_diagonalTargetDepthCorrection_lt_canonical_edge ht

/-- A target-depth base-two step turns an old `1/16` band into the desired
new `1/32` band whenever the appended correction fits inside the new edge. -/
theorem baseTwoTargetResidue_central_of_strongBand
    {m : ℕ} {d C : ℤ} (hm : 5 ≤ m)
    (hC : |C| ≤ 2 ^ (m - 5))
    (hlo : 2 ^ (m - 5) ≤ d)
    (hhi : d ≤ 2 ^ (m - 1) - 2 ^ (m - 5)) :
    (2 : ℤ) ^ (m - 5) ≤ (2 * d + C) % 2 ^ m ∧
      (2 * d + C) % 2 ^ m ≤ 2 ^ m - 2 ^ (m - 5) := by
  let M : ℤ := 2 ^ (m - 1)
  let e : ℤ := 2 ^ (m - 5)
  let x : ℤ := 2 * d + C
  have hm1 : 1 ≤ m := by omega
  have hM : (2 : ℤ) ^ m = 2 * M := by
    have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    calc
      (2 : ℤ) ^ m = 2 ^ ((m - 1) + 1) := by rw [hmEq]
      _ = 2 * M := by rw [pow_succ]; dsimp [M]; ring
  have hepos : 0 < e := by dsimp [e]; positivity
  have habs := abs_le.mp hC
  have hxlo : e ≤ x := by
    dsimp [x, e] at habs hlo ⊢
    linarith
  have hxhi : x ≤ 2 * M - e := by
    dsimp [x, M, e] at habs hhi ⊢
    linarith
  have hxM : x < 2 * M := by linarith
  have hfix : x % (2 * M) = x :=
    Int.emod_eq_of_lt (by linarith) hxM
  change (2 : ℤ) ^ (m - 5) ≤ x % 2 ^ m ∧
    x % 2 ^ m ≤ 2 ^ m - 2 ^ (m - 5)
  rw [hM, hfix]
  constructor <;> assumption

/-- Sharp division-free sufficient interface for a target-depth base-two
step.  The old residue need only have enough doubled margin to absorb an
absolute correction envelope `B`; no fixed stronger band is required. -/
theorem baseTwoTargetResidue_central_of_envelope
    {m : ℕ} {d C B : ℤ} (hm : 5 ≤ m)
    (hC : |C| ≤ B)
    (hlo : 2 ^ (m - 5) + B ≤ 2 * d)
    (hhi : 2 * d + B ≤ 2 ^ m - 2 ^ (m - 5)) :
    (2 : ℤ) ^ (m - 5) ≤ (2 * d + C) % 2 ^ m ∧
      (2 * d + C) % 2 ^ m ≤ 2 ^ m - 2 ^ (m - 5) := by
  let M : ℤ := 2 ^ m
  let e : ℤ := 2 ^ (m - 5)
  let x : ℤ := 2 * d + C
  have hepos : 0 < e := by dsimp [e]; positivity
  have habs := abs_le.mp hC
  have hxlo : e ≤ x := by
    dsimp [x, e] at habs hlo ⊢
    linarith
  have hxhi : x ≤ M - e := by
    dsimp [x, M, e] at habs hhi ⊢
    linarith
  have hxM : x < M := by linarith
  have hfix : x % M = x := Int.emod_eq_of_lt (by linarith) hxM
  change (2 : ℤ) ^ (m - 5) ≤ x % 2 ^ m ∧
    x % 2 ^ m ≤ 2 ^ m - 2 ^ (m - 5)
  change e ≤ x % M ∧ x % M ≤ M - e
  rw [hfix]
  exact ⟨hxlo, hxhi⟩

/-- The exact parity-complete reduction at canonical depth.  Centrality of the
penultimate residue in its stronger `1/16` band forces canonical `1/32`
centrality; the correction estimate is now automatic for every `t ≥ 3`. -/
theorem canonicalAdjacentSuffixResidue_central_of_penultimate_strongBand
    {t : ℕ} (ht : 3 ≤ t)
    (hlo :
      2 ^ (canonicalAdjacentSuffixDepth t - 5) ≤
        diagonalAdjacentSuffixResidue t 0
          (canonicalAdjacentSuffixDepth t - 1))
    (hhi :
      diagonalAdjacentSuffixResidue t 0
          (canonicalAdjacentSuffixDepth t - 1) ≤
        2 ^ (canonicalAdjacentSuffixDepth t - 1) -
          2 ^ (canonicalAdjacentSuffixDepth t - 5)) :
    (2 : ℤ) ^ (canonicalAdjacentSuffixDepth t - 5) ≤
        diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ∧
      diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ≤
        2 ^ canonicalAdjacentSuffixDepth t -
          2 ^ (canonicalAdjacentSuffixDepth t - 5) := by
  obtain ⟨hm, _hwidth⟩ := canonicalAdjacentSuffixDepth_width ht
  rw [diagonalAdjacentSuffixResidue_target_depth (by omega)]
  apply baseTwoTargetResidue_central_of_strongBand hm
  · exact Int.le_of_lt
      (abs_diagonalTargetDepthCorrection_lt_canonical_edge ht)
  · exact hlo
  · exact hhi

/-- Strongest elementary parity-complete reduction supplied by the uniform
correction estimate.  The two displayed inequalities are the exact doubled
left and right margins needed to absorb the factorisation-free envelope. -/
theorem canonicalAdjacentSuffixResidue_central_of_penultimate_margin
    {t : ℕ} (ht : 3 ≤ t)
    (hlo :
      2 ^ (canonicalAdjacentSuffixDepth t - 5) +
          (3 * periodLcm t +
            2 * canonicalAdjacentSuffixDepth t + 1 : ℤ) ≤
        2 * diagonalAdjacentSuffixResidue t 0
          (canonicalAdjacentSuffixDepth t - 1))
    (hhi :
      2 * diagonalAdjacentSuffixResidue t 0
          (canonicalAdjacentSuffixDepth t - 1) +
          (3 * periodLcm t +
            2 * canonicalAdjacentSuffixDepth t + 1 : ℤ) ≤
        2 ^ canonicalAdjacentSuffixDepth t -
          2 ^ (canonicalAdjacentSuffixDepth t - 5)) :
    (2 : ℤ) ^ (canonicalAdjacentSuffixDepth t - 5) ≤
        diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ∧
      diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ≤
        2 ^ canonicalAdjacentSuffixDepth t -
          2 ^ (canonicalAdjacentSuffixDepth t - 5) := by
  obtain ⟨hm, _hwidth⟩ := canonicalAdjacentSuffixDepth_width ht
  rw [diagonalAdjacentSuffixResidue_target_depth (by omega)]
  apply baseTwoTargetResidue_central_of_envelope hm
  · exact abs_diagonalTargetDepthCorrection_le
      t (canonicalAdjacentSuffixDepth t)
  · exact hlo
  · exact hhi

/-- The unresolved arithmetic input after the adjacent finite reduction.  It
uses the fixed first pair of cuts, so sliding is no longer an artificial
waiting parameter. -/
def DiagonalAdjacentSuffixGapSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ m : ℕ,
    5 ≤ m ∧
      32 * (3 * periodLcm t + 2 * (m + 3) : ℤ) < 2 ^ m ∧
      2 ^ (m - 5) ≤ diagonalAdjacentSuffixResidue t 0 m ∧
      diagonalAdjacentSuffixResidue t 0 m ≤ 2 ^ m - 2 ^ (m - 5)

/-- The canonical producer throat after removing the automatic width budget.
Only centrality of one exact modular observable at arbitrarily large LCM
heights remains. -/
def CanonicalAdjacentSuffixCentralSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    2 ^ (canonicalAdjacentSuffixDepth t - 5) ≤
        diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ∧
      diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ≤
        2 ^ canonicalAdjacentSuffixDepth t -
          2 ^ (canonicalAdjacentSuffixDepth t - 5)

/-- Exact penultimate-coordinate form of the canonical producer.  Unlike the
envelope and strong-band interfaces below, this loses no information: the
signed one-step correction is retained rather than replaced by an absolute
upper bound. -/
def CanonicalAdjacentSuffixPenultimateExactSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    2 ^ (canonicalAdjacentSuffixDepth t - 5) ≤
      2 * diagonalAdjacentSuffixResidue t 0
          (canonicalAdjacentSuffixDepth t - 1) +
        diagonalTargetDepthCorrection t (canonicalAdjacentSuffixDepth t) ∧
    2 * diagonalAdjacentSuffixResidue t 0
          (canonicalAdjacentSuffixDepth t - 1) +
        diagonalTargetDepthCorrection t (canonicalAdjacentSuffixDepth t) ≤
      2 ^ canonicalAdjacentSuffixDepth t -
        2 ^ (canonicalAdjacentSuffixDepth t - 5)

/-- Sharp parity-complete producer after eliminating the one-step correction.
It asks only that the doubled penultimate residue absorb the explicit
factorisation-free correction envelope on both edges. -/
def CanonicalAdjacentSuffixPenultimateMarginSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    2 ^ (canonicalAdjacentSuffixDepth t - 5) +
        (3 * periodLcm t + 2 * canonicalAdjacentSuffixDepth t + 1 : ℤ) ≤
      2 * diagonalAdjacentSuffixResidue t 0
        (canonicalAdjacentSuffixDepth t - 1) ∧
    2 * diagonalAdjacentSuffixResidue t 0
        (canonicalAdjacentSuffixDepth t - 1) +
        (3 * periodLcm t + 2 * canonicalAdjacentSuffixDepth t + 1 : ℤ) ≤
      2 ^ canonicalAdjacentSuffixDepth t -
        2 ^ (canonicalAdjacentSuffixDepth t - 5)

/-- Parity-complete producer left after the one-depth correction estimate.
Only the penultimate residue must occupy the stronger `1/16` band; all
transport to the canonical `1/32` consumer is automatic. -/
def CanonicalAdjacentSuffixPenultimateStrongBandSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    2 ^ (canonicalAdjacentSuffixDepth t - 5) ≤
      diagonalAdjacentSuffixResidue t 0
        (canonicalAdjacentSuffixDepth t - 1) ∧
    diagonalAdjacentSuffixResidue t 0
        (canonicalAdjacentSuffixDepth t - 1) ≤
      2 ^ (canonicalAdjacentSuffixDepth t - 1) -
        2 ^ (canonicalAdjacentSuffixDepth t - 5)

/-- The prime-power-jump-aligned producer throat.  Repeated LCM heights carry
no new arithmetic state, so it is enough to establish canonical centrality at
arbitrarily large strict jumps. -/
def CanonicalAdjacentSuffixJumpCentralSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    periodLcm t < periodLcm (t + 1) ∧
      2 ^ (canonicalAdjacentSuffixDepth t - 5) ≤
          diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ∧
        diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ≤
          2 ^ canonicalAdjacentSuffixDepth t -
            2 ^ (canonicalAdjacentSuffixDepth t - 5)

/-- Exact classification of a strict `periodLcm` step before the
prime-power refinement: the height changes precisely when the new endpoint
does not already divide the old height. -/
theorem periodLcm_strict_jump_iff_succ_not_dvd (t : ℕ) :
    periodLcm t < periodLcm (t + 1) ↔
      ¬ (t + 1) ∣ periodLcm t := by
  constructor
  · intro hjump hdvd
    have heq : periodLcm (t + 1) = periodLcm t := by
      change Nat.lcm (periodLcm t) (t + 1) = periodLcm t
      exact Nat.lcm_eq_left_iff_dvd.mpr hdvd
    omega
  · intro hnd
    have hle : periodLcm t ≤ periodLcm (t + 1) :=
      Nat.le_of_dvd (periodLcm_pos (t + 1)) (periodLcm_dvd_succ t)
    exact lt_of_le_of_ne hle fun heq => by
      apply hnd
      have hdvd : t + 1 ∣ periodLcm (t + 1) :=
        dvd_periodLcm (by omega) le_rfl
      simpa [heq] using hdvd

/-- Beyond the two initial scales, every strict LCM jump occurs exactly when
the new endpoint is a prime power.  This packages the generic window
classification for the adjacent endpoint used by the slack producer. -/
theorem succ_eq_prime_pow_of_periodLcm_strict_jump
    {t : ℕ} (ht : 2 ≤ t)
    (hjump : periodLcm t < periodLcm (t + 1)) :
    ∃ p k : ℕ, Nat.Prime p ∧ t + 1 = p ^ k := by
  have hnd : ¬ (t + 1) ∣ periodLcm t :=
    (periodLcm_strict_jump_iff_succ_not_dvd t).1 hjump
  obtain ⟨p, k, hp, hpk, _⟩ :=
    eq_prime_pow_of_not_dvd_periodLcm
      (t := t) (j := t + 1) (by omega) (by omega) hnd
  exact ⟨p, k, hp, hpk⟩

/-- A strict prime-power endpoint inserts exactly one additional copy of its
prime base into the LCM height. -/
theorem periodLcm_succ_eq_prime_mul_of_strict_jump
    {t : ℕ} (ht : 2 ≤ t)
    (hjump : periodLcm t < periodLcm (t + 1)) :
    ∃ p k : ℕ, Nat.Prime p ∧ t + 1 = p ^ k ∧
      periodLcm (t + 1) = p * periodLcm t := by
  obtain ⟨p, k, hp, hpk⟩ :=
    succ_eq_prime_pow_of_periodLcm_strict_jump ht hjump
  have hk : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := by omega
    rw [hk0] at hpk
    simp at hpk
    omega
  have hpredLt : p ^ (k - 1) < p ^ k :=
    Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpredLe : p ^ (k - 1) ≤ t := by omega
  have hpredDvdH : p ^ (k - 1) ∣ periodLcm t :=
    dvd_periodLcm (pow_pos hp.pos _) hpredLe
  have hnd : ¬p ^ k ∣ periodLcm t := by
    simpa [← hpk] using
      (periodLcm_strict_jump_iff_succ_not_dvd t).1 hjump
  have hgDvd : Nat.gcd (periodLcm t) (p ^ k) ∣ p ^ k :=
    Nat.gcd_dvd_right _ _
  obtain ⟨a, ha, hga⟩ := (Nat.dvd_prime_pow hp).1 hgDvd
  have hpredDvdGcd : p ^ (k - 1) ∣ Nat.gcd (periodLcm t) (p ^ k) :=
    Nat.dvd_gcd hpredDvdH (pow_dvd_pow p (by omega))
  have hpredLeA : k - 1 ≤ a := by
    have hpowLe : p ^ (k - 1) ≤ p ^ a :=
      Nat.le_of_dvd (pow_pos hp.pos _) (by simpa [hga] using hpredDvdGcd)
    by_contra hnot
    have haLt : a < k - 1 := Nat.lt_of_not_ge hnot
    have := Nat.pow_lt_pow_right hp.one_lt haLt
    omega
  have haNe : a ≠ k := by
    intro hak
    apply hnd
    have hgLeft := Nat.gcd_dvd_left (periodLcm t) (p ^ k)
    simpa [hga, hak] using hgLeft
  have haEq : a = k - 1 := by omega
  have hgcd : Nat.gcd (periodLcm t) (p ^ k) = p ^ (k - 1) := by
    simpa [haEq] using hga
  have hpow : p ^ k = p ^ (k - 1) * p := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rw [pow_succ]
  have hmul := Nat.gcd_mul_lcm (periodLcm t) (p ^ k)
  have hcancel :
      p ^ (k - 1) * Nat.lcm (periodLcm t) (p ^ k) =
        p ^ (k - 1) * (p * periodLcm t) := by
    calc
      _ = Nat.gcd (periodLcm t) (p ^ k) *
          Nat.lcm (periodLcm t) (p ^ k) := by rw [hgcd]
      _ = periodLcm t * p ^ k := hmul
      _ = periodLcm t * (p ^ (k - 1) * p) := by rw [hpow]
      _ = p ^ (k - 1) * (p * periodLcm t) := by ring
  have hlcm : Nat.lcm (periodLcm t) (p ^ k) = p * periodLcm t :=
    Nat.mul_left_cancel (pow_pos hp.pos _) hcancel
  refine ⟨p, k, hp, hpk, ?_⟩
  change Nat.lcm (periodLcm t) (t + 1) = p * periodLcm t
  simpa [hpk] using hlcm

/-- Below `2^a`, every row and hence their LCM has 2-adic exponent strictly
smaller than `a`.  This supplies the missing converse needed to certify the
cofinal power-of-two strict-jump subfamily. -/
theorem periodLcm_factorization_two_lt_of_lt_pow_two
    {a t : ℕ} (ha : 0 < a) (ht : t < 2 ^ a) :
    (periodLcm t).factorization 2 < a := by
  induction t with
  | zero => simpa [periodLcm] using ha
  | succ t ih =>
      have ht' : t < 2 ^ a := by omega
      have hleft : (periodLcm t).factorization 2 < a := ih ht'
      have hright : (t + 1).factorization 2 < a := by
        by_contra hnot
        have hfac : a ≤ (t + 1).factorization 2 := Nat.le_of_not_gt hnot
        have hdvd : 2 ^ a ∣ t + 1 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).2 hfac
        have hpLe : 2 ^ a ≤ t + 1 :=
          Nat.le_of_dvd (by positivity) hdvd
        omega
      rw [periodLcm, Nat.factorization_lcm (periodLcm_pos t).ne' (by omega),
        Finsupp.sup_apply]
      exact max_lt hleft hright

/-- Every endpoint `2^a`, `a ≥ 2`, is a strict LCM jump. -/
theorem periodLcm_pow_two_strict_jump {a : ℕ} (ha : 2 ≤ a) :
    periodLcm (2 ^ a - 1) < periodLcm (2 ^ a) := by
  have hpowPos : 0 < 2 ^ a := by positivity
  have hsucc : 2 ^ a - 1 + 1 = 2 ^ a := by omega
  have hjump :
      periodLcm (2 ^ a - 1) < periodLcm (2 ^ a - 1 + 1) := by
    apply (periodLcm_strict_jump_iff_succ_not_dvd (2 ^ a - 1)).2
    rw [hsucc]
    intro hdvd
    have hfacLe : a ≤ (periodLcm (2 ^ a - 1)).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization
        (periodLcm_pos (2 ^ a - 1)).ne').1 hdvd
    have hfacLt : (periodLcm (2 ^ a - 1)).factorization 2 < a :=
      periodLcm_factorization_two_lt_of_lt_pow_two (by omega) (by omega)
    omega
  simpa only [hsucc] using hjump

/-- A power-of-two strict jump doubles the LCM height exactly. -/
theorem periodLcm_pow_two_eq_two_mul {a : ℕ} (ha : 2 ≤ a) :
    periodLcm (2 ^ a) = 2 * periodLcm (2 ^ a - 1) := by
  have hpowPos : 0 < 2 ^ a := by positivity
  have hsucc : 2 ^ a - 1 + 1 = 2 ^ a := by omega
  have hpow4 : 4 ≤ 2 ^ a := by
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) ha)
  have hpredTwo : 2 ≤ 2 ^ a - 1 := by omega
  have hjump :
      periodLcm (2 ^ a - 1) < periodLcm (2 ^ a - 1 + 1) := by
    simpa only [hsucc] using periodLcm_pow_two_strict_jump ha
  obtain ⟨p, k, hp, hpk, hheight⟩ :=
    periodLcm_succ_eq_prime_mul_of_strict_jump
      (t := 2 ^ a - 1) hpredTwo hjump
  have hk : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, hsucc] at hpk
    norm_num at hpk
    omega
  have hpDvdPow : p ∣ 2 ^ a := by
    rw [← hsucc, hpk]
    exact dvd_pow_self p hk.ne'
  have hpDvdTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpDvdPow
  have hpEq : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpDvdTwo
  simpa only [hsucc, hpEq] using hheight

/-- Concrete power-of-two jump form of the even seam. -/
theorem diagonalWindowIncrement_powerTwoJump_even
    {a r : ℕ} (ha : 2 ≤ a) (hr : Even r) :
    diagonalWindowIncrement (2 ^ a) (2 * r) =
      2 * diagonalWindowIncrement (2 ^ a - 1) r := by
  have hpow4 : 4 ≤ 2 ^ a := by
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) ha)
  have hpredTwo : 2 ≤ 2 ^ a - 1 := by omega
  exact diagonalWindowIncrement_evenSeam_even hpredTwo
    (periodLcm_pow_two_eq_two_mul ha) hr

theorem diagonalWindowIncrement_powerTwoJump_odd
    {a r : ℕ} (ha : 2 ≤ a) (hr : Odd r) :
    diagonalWindowIncrement (2 ^ a) (2 * r) =
      diagonalWindowIncrement (2 ^ a - 1) r := by
  have hpow4 : 4 ≤ 2 ^ a := by
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) ha)
  have hpredTwo : 2 ≤ 2 ^ a - 1 := by omega
  exact diagonalWindowIncrement_evenSeam_odd hpredTwo
    (periodLcm_pow_two_eq_two_mul ha) hr

/-- The exact inherited contribution at a reduced offset across a
power-of-two LCM jump.  Even reduced offsets double; odd reduced offsets are
copied unchanged. -/
def powerTwoInheritedIncrement (a r : ℕ) : ℤ :=
  if Even r then
    2 * diagonalWindowIncrement (2 ^ a - 1) r
  else
    diagonalWindowIncrement (2 ^ a - 1) r

/-- The odd post-jump offset not reconstructed by the even-offset seam.  The
name records its role in the cocycle, not an arithmetic independence claim. -/
def powerTwoFreshOddIncrement (a q : ℕ) : ℤ :=
  diagonalWindowIncrement (2 ^ a) (2 * q + 1)

/-- The signed correction in one odd-depth/base-four power-of-two step. -/
def powerTwoOddDepthCorrection (a n : ℕ) : ℤ :=
  powerTwoFreshOddIncrement a (n + 1) -
    2 * powerTwoInheritedIncrement a (n + 1) +
    powerTwoInheritedIncrement a (n + 2)

/-- Every even post-jump offset is exactly the corresponding inherited
increment. -/
theorem diagonalWindowIncrement_powerTwoJump_even_offset
    {a r : ℕ} (ha : 2 ≤ a) :
    diagonalWindowIncrement (2 ^ a) (2 * r) =
      powerTwoInheritedIncrement a r := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [diagonalWindowIncrement_powerTwoJump_even ha hr]
    simp [powerTwoInheritedIncrement, hr]
  · rw [diagonalWindowIncrement_powerTwoJump_odd ha hr]
    simp [powerTwoInheritedIncrement, Nat.not_even_iff_odd.mpr hr]

/-- At every odd-depth base-four step, the only post-jump increment outside
the even inheritance seam is the single new odd terminal offset.  This is
the exact local arithmetic throat behind power-of-two centrality. -/
theorem diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_step
    {a n : ℕ} (ha : 2 ≤ a) :
    diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * (n + 1) + 1) =
      4 * diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * n + 1) +
        powerTwoFreshOddIncrement a (n + 1) -
        2 * powerTwoInheritedIncrement a (n + 1) +
        powerTwoInheritedIncrement a (n + 2) := by
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
    diagonalAdjacentSuffixRawBlock_add_two]
  rw [show 0 + (2 * n + 1) + 1 = 2 * (n + 1) by omega,
    show 0 + (2 * n + 1) + 2 = 2 * (n + 1) + 1 by omega,
    show 0 + (2 * n + 1) + 3 = 2 * (n + 2) by omega,
    diagonalWindowIncrement_powerTwoJump_even_offset ha,
    diagonalWindowIncrement_powerTwoJump_even_offset ha]
  unfold powerTwoFreshOddIncrement
  ring

/-- Residue form of the odd-depth cocycle.  The factor four lifts every
discarded multiple of the old modulus to a multiple of the new modulus, so
the step depends only on the old residue and the one exact correction. -/
theorem diagonalAdjacentSuffixResidue_powerTwo_oddDepth_step
    {a n : ℕ} (ha : 2 ≤ a) :
    diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * (n + 1) + 1) =
      (4 * diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * n + 1) +
        powerTwoOddDepthCorrection a n) % 2 ^ (2 * (n + 1) + 1) := by
  have hraw :
      diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * (n + 1) + 1) =
        4 * diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * n + 1) +
          powerTwoOddDepthCorrection a n := by
    rw [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_step ha]
    unfold powerTwoOddDepthCorrection
    ring
  rw [diagonalAdjacentSuffixResidue_eq_rawBlock,
    diagonalAdjacentSuffixResidue_eq_rawBlock,
    hraw]
  let R : ℤ := diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * n + 1)
  let M : ℤ := 2 ^ (2 * n + 1)
  let C : ℤ := powerTwoOddDepthCorrection a n
  change (4 * R + C) % 2 ^ (2 * (n + 1) + 1) =
    (4 * (R % M) + C) % 2 ^ (2 * (n + 1) + 1)
  have hdecomp : M * (R / M) + R % M = R :=
    Int.mul_ediv_add_emod R M
  have hpow : (2 : ℤ) ^ (2 * (n + 1) + 1) = 4 * M := by
    dsimp [M]
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hrewrite :
      4 * R + C = (4 * (R % M) + C) + (4 * M) * (R / M) := by
    have hscaled := congrArg (fun z : ℤ => 4 * z + C) hdecomp
    calc
      4 * R + C = 4 * (M * (R / M) + R % M) + C := hscaled.symm
      _ = (4 * (R % M) + C) + (4 * M) * (R / M) := by ring
  rw [hpow, hrewrite, Int.add_mul_emod_self_left]

/-- A base-four step preserves the fixed central band whenever its correction
fits between the exact left and right margin budgets.  This isolates the
remaining arithmetic obligation from all modular bookkeeping. -/
theorem baseFourResidue_central_of_correction_bounds
    {m : ℕ} {d C : ℤ} (hm : 5 ≤ m)
    (hClower : -4 * (d - 2 ^ (m - 5)) ≤ C)
    (hCupper : C ≤ 4 * ((2 ^ m - 2 ^ (m - 5)) - d)) :
    (2 : ℤ) ^ (m + 2 - 5) ≤ (4 * d + C) % 2 ^ (m + 2) ∧
      (4 * d + C) % 2 ^ (m + 2) ≤
        2 ^ (m + 2) - 2 ^ (m + 2 - 5) := by
  let M : ℤ := 2 ^ m
  let e : ℤ := 2 ^ (m - 5)
  let x : ℤ := 4 * d + C
  have hM : (2 : ℤ) ^ (m + 2) = 4 * M := by
    dsimp [M]
    rw [pow_add]
    norm_num
    ring
  have he : (2 : ℤ) ^ (m + 2 - 5) = 4 * e := by
    dsimp [e]
    rw [show m + 2 - 5 = (m - 5) + 2 by omega, pow_add]
    norm_num
    ring
  have hepos : 0 < e := by dsimp [e]; positivity
  have hxlo : 4 * e ≤ x := by
    dsimp [x, e] at hClower ⊢
    linarith
  have hxhi : x ≤ 4 * (M - e) := by
    dsimp [x, M, e] at hCupper ⊢
    linarith
  have hxM : x < 4 * M := by linarith
  have hfix : x % (4 * M) = x :=
    Int.emod_eq_of_lt (by linarith) hxM
  change (2 : ℤ) ^ (m + 2 - 5) ≤ x % 2 ^ (m + 2) ∧
    x % 2 ^ (m + 2) ≤ 2 ^ (m + 2) - 2 ^ (m + 2 - 5)
  rw [hM, he, hfix]
  constructor <;> linarith

/-- Power-of-two specialization of the margin lemma.  A single exact bound
on the odd-depth correction advances canonical centrality by two binary
places; no further modular or LCM argument remains in the induction step. -/
theorem diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_of_correction_bounds
    {a n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n)
    (hClower :
      -4 * (diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * n + 1) -
          2 ^ (2 * n + 1 - 5)) ≤ powerTwoOddDepthCorrection a n)
    (hCupper :
      powerTwoOddDepthCorrection a n ≤
        4 * ((2 ^ (2 * n + 1) - 2 ^ (2 * n + 1 - 5)) -
          diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * n + 1))) :
    (2 : ℤ) ^ (2 * (n + 1) + 1 - 5) ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * (n + 1) + 1) ∧
      diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * (n + 1) + 1) ≤
        2 ^ (2 * (n + 1) + 1) - 2 ^ (2 * (n + 1) + 1 - 5) := by
  rw [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_step ha]
  simpa only [show (2 * n + 1) + 2 = 2 * (n + 1) + 1 by omega] using
    (baseFourResidue_central_of_correction_bounds
      (m := 2 * n + 1)
      (d := diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * n + 1))
      (C := powerTwoOddDepthCorrection a n) (by omega) hClower hCupper)

/-- Strict LCM jumps occur beyond every prescribed index.  A prime endpoint
strictly above the index supplies a witness. -/
theorem exists_periodLcm_strict_jump_ge (t₀ : ℕ) :
    ∃ t, t₀ ≤ t ∧ periodLcm t < periodLcm (t + 1) := by
  obtain ⟨p, hpLower, hp⟩ := Nat.exists_infinite_primes (t₀ + 1)
  refine ⟨p - 1, by omega, ?_⟩
  apply (periodLcm_strict_jump_iff_succ_not_dvd (p - 1)).2
  have hpred : p - 1 + 1 = p := by omega
  rw [hpred, periodLcm_eq_lcmHeight]
  intro hpdvd
  have hpLe : p ≤ p - 1 :=
    (MersenneShadowCyclotomicNoncollapse.prime_dvd_lcmHeight_iff hp).1 hpdvd
  omega

/-- Signed distance of the canonical adjacent residue from the nearer edge of
the fixed central band.  Nonnegative slack is exactly the two-sided
centrality condition; this scalar is the proof-oriented cocycle to study at
strict LCM jumps. -/
def canonicalAdjacentSuffixCentralSlack (t : ℕ) : ℤ :=
  let m := canonicalAdjacentSuffixDepth t
  let d := diagonalAdjacentSuffixResidue t 0 m
  min (d - 2 ^ (m - 5)) ((2 ^ m - 2 ^ (m - 5)) - d)

/-- The canonical scalar depends only on the LCM height.  In particular it is
constant across every plateau between consecutive strict jumps. -/
theorem canonicalAdjacentSuffixCentralSlack_eq_of_periodLcm_eq
    {t u : ℕ} (hH : periodLcm t = periodLcm u) :
    canonicalAdjacentSuffixCentralSlack t =
      canonicalAdjacentSuffixCentralSlack u := by
  simp [canonicalAdjacentSuffixCentralSlack, canonicalAdjacentSuffixDepth,
    diagonalAdjacentSuffixResidue, diagonalSuffixResidue,
    hH]

/-- The two central-band inequalities collapse to one exact integer sign. -/
theorem canonicalAdjacentSuffixCentral_iff_slack_nonneg (t : ℕ) :
    (2 ^ (canonicalAdjacentSuffixDepth t - 5) ≤
          diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ∧
        diagonalAdjacentSuffixResidue t 0 (canonicalAdjacentSuffixDepth t) ≤
          2 ^ canonicalAdjacentSuffixDepth t -
            2 ^ (canonicalAdjacentSuffixDepth t - 5)) ↔
      0 ≤ canonicalAdjacentSuffixCentralSlack t := by
  simp [canonicalAdjacentSuffixCentralSlack]

/-- Scalar strict-jump producer.  This is equivalent to the original
two-sided producer but exposes a single integer observable for recurrence,
congruence, and exact-computation arguments. -/
def CanonicalAdjacentSuffixJumpSlackSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    periodLcm t < periodLcm (t + 1) ∧
      0 ≤ canonicalAdjacentSuffixCentralSlack t

/-- Fresh-factor-aligned producer: the successful scalar is evaluated after
the displayed strict jump, at the new LCM height. -/
def CanonicalAdjacentSuffixPostJumpSlackSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, max 3 t₀ ≤ t ∧
    periodLcm t < periodLcm (t + 1) ∧
      0 ≤ canonicalAdjacentSuffixCentralSlack (t + 1)

/-- Cofinal power-of-two specialisation of the post-jump producer.  The
argument is the new endpoint `2^a`, not the pre-jump index `2^a - 1`. -/
def CanonicalAdjacentSuffixPowerTwoPostJumpSlackSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a, max 2 a₀ ≤ a ∧
    0 ≤ canonicalAdjacentSuffixCentralSlack (2 ^ a)

/-- Power-of-two post-jump centrality is already cofinal among strict LCM
jumps, so it supplies the general post-jump producer. -/
theorem canonicalAdjacentSuffixPostJumpSlackSupply_of_powerTwo
    (hsupply : CanonicalAdjacentSuffixPowerTwoPostJumpSlackSupply) :
    CanonicalAdjacentSuffixPostJumpSlackSupply := by
  intro t₀
  obtain ⟨a, ha, hslack⟩ := hsupply t₀
  have ha2 : 2 ≤ a := (le_max_left 2 t₀).trans ha
  have ht₀a : t₀ ≤ a := (le_max_right 2 t₀).trans ha
  have halt : a < 2 ^ a := Nat.lt_two_pow_self
  have hpow4 : 4 ≤ 2 ^ a := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num : 0 < 2) ha2
  have hsucc : 2 ^ a - 1 + 1 = 2 ^ a := by omega
  refine ⟨2 ^ a - 1, ?_, ?_, ?_⟩
  · apply max_le
    · omega
    · omega
  · simpa [hsucc] using periodLcm_pow_two_strict_jump ha2
  · simpa [hsucc] using hslack

/-- Post-jump centrality transports across the following LCM plateau to its
next strict-jump index.  This is the unconditional reindexing bridge that
lets arithmetic arguments use the newly inserted factor while preserving the
existing pre-jump producer and consumer. -/
theorem canonicalAdjacentSuffixJumpSlackSupply_of_postJump
    (hsupply : CanonicalAdjacentSuffixPostJumpSlackSupply) :
    CanonicalAdjacentSuffixJumpSlackSupply := by
  intro t₀
  obtain ⟨t, ht, _hjump, hslack⟩ := hsupply t₀
  let P : ℕ → Prop := fun u ↦
    t + 1 ≤ u ∧ periodLcm u < periodLcm (u + 1)
  have hP : ∃ u, P u := exists_periodLcm_strict_jump_ge (t + 1)
  let u := Nat.find hP
  have hu : P u := Nat.find_spec hP
  have hplateauAux : ∀ v : ℕ, t + 1 ≤ v → v ≤ u →
      periodLcm (t + 1) = periodLcm v := by
    intro v htv
    induction v, htv using Nat.le_induction with
    | base => intro _; rfl
    | succ v htv ih =>
        intro hvu
        have hvlt : v < u := by omega
        have hnotP : ¬P v := Nat.find_min hP hvlt
        have hnotJump : ¬periodLcm v < periodLcm (v + 1) := by
          intro hjump
          exact hnotP ⟨htv, hjump⟩
        have hle : periodLcm v ≤ periodLcm (v + 1) :=
          Nat.le_of_dvd (periodLcm_pos (v + 1)) (periodLcm_dvd_succ v)
        have heq : periodLcm v = periodLcm (v + 1) :=
          le_antisymm hle (not_lt.mp hnotJump)
        exact (ih (by omega)).trans heq
  have hplateau : periodLcm (t + 1) = periodLcm u :=
    hplateauAux u hu.1 le_rfl
  have hslackU : 0 ≤ canonicalAdjacentSuffixCentralSlack u := by
    rw [← canonicalAdjacentSuffixCentralSlack_eq_of_periodLcm_eq hplateau]
    exact hslack
  exact ⟨u, by omega, hu.2, hslackU⟩

theorem canonicalAdjacentSuffixJumpCentralSupply_iff_slackSupply :
    CanonicalAdjacentSuffixJumpCentralSupply ↔
      CanonicalAdjacentSuffixJumpSlackSupply := by
  constructor
  · intro hsupply t₀
    obtain ⟨t, ht, hjump, hlo, hhi⟩ := hsupply t₀
    exact ⟨t, ht, hjump,
      (canonicalAdjacentSuffixCentral_iff_slack_nonneg t).1 ⟨hlo, hhi⟩⟩
  · intro hsupply t₀
    obtain ⟨t, ht, hjump, hslack⟩ := hsupply t₀
    obtain ⟨hlo, hhi⟩ :=
      (canonicalAdjacentSuffixCentral_iff_slack_nonneg t).2 hslack
    exact ⟨t, ht, hjump, hlo, hhi⟩

/-- The canonical central producer and its signed penultimate-coordinate
form are logically equivalent.  This pins the remaining cofinal arithmetic
obligation exactly, without the loss introduced by an absolute correction
envelope. -/
theorem canonicalAdjacentSuffixCentralSupply_iff_penultimateExact :
    CanonicalAdjacentSuffixCentralSupply ↔
      CanonicalAdjacentSuffixPenultimateExactSupply := by
  constructor
  · intro hsupply t₀
    obtain ⟨t, ht, hlo, hhi⟩ := hsupply t₀
    have ht3 : 3 ≤ t := (le_max_left 3 t₀).trans ht
    obtain ⟨hexactLo, hexactHi⟩ :=
      (canonicalAdjacentSuffixResidue_central_iff_penultimate_exact ht3).1
        ⟨hlo, hhi⟩
    exact ⟨t, ht, hexactLo, hexactHi⟩
  · intro hsupply t₀
    obtain ⟨t, ht, hlo, hhi⟩ := hsupply t₀
    have ht3 : 3 ≤ t := (le_max_left 3 t₀).trans ht
    obtain ⟨hcentralLo, hcentralHi⟩ :=
      (canonicalAdjacentSuffixResidue_central_iff_penultimate_exact ht3).2
        ⟨hlo, hhi⟩
    exact ⟨t, ht, hcentralLo, hcentralHi⟩

/-- The sharp penultimate margin producer feeds the canonical centrality
interface directly. -/
theorem canonicalAdjacentSuffixCentralSupply_of_penultimateMargin
    (hsupply : CanonicalAdjacentSuffixPenultimateMarginSupply) :
    CanonicalAdjacentSuffixCentralSupply := by
  intro t₀
  obtain ⟨t, ht, hlo, hhi⟩ := hsupply t₀
  have ht3 : 3 ≤ t := (le_max_left 3 t₀).trans ht
  obtain ⟨hcanonicalLo, hcanonicalHi⟩ :=
    canonicalAdjacentSuffixResidue_central_of_penultimate_margin ht3 hlo hhi
  exact ⟨t, ht, hcanonicalLo, hcanonicalHi⟩

/-- The cleaner penultimate `1/16` band is a sufficient corollary of the
sharper doubled-margin producer because the canonical correction envelope is
strictly smaller than one edge. -/
theorem canonicalAdjacentSuffixPenultimateMarginSupply_of_strongBand
    (hsupply : CanonicalAdjacentSuffixPenultimateStrongBandSupply) :
    CanonicalAdjacentSuffixPenultimateMarginSupply := by
  intro t₀
  obtain ⟨t, ht, hlo, hhi⟩ := hsupply t₀
  have ht3 : 3 ≤ t := (le_max_left 3 t₀).trans ht
  obtain ⟨hm, _hwidth⟩ := canonicalAdjacentSuffixDepth_width ht3
  have hB := diagonalTargetDepthCorrectionEnvelope_lt_canonical_edge ht3
  have hpow : (2 : ℤ) ^ canonicalAdjacentSuffixDepth t =
      2 * 2 ^ (canonicalAdjacentSuffixDepth t - 1) := by
    have hm1 : 1 ≤ canonicalAdjacentSuffixDepth t := by omega
    have hdepth : canonicalAdjacentSuffixDepth t - 1 + 1 =
        canonicalAdjacentSuffixDepth t := Nat.sub_add_cancel hm1
    calc
      (2 : ℤ) ^ canonicalAdjacentSuffixDepth t =
          2 ^ (canonicalAdjacentSuffixDepth t - 1 + 1) := by rw [hdepth]
      _ = 2 * 2 ^ (canonicalAdjacentSuffixDepth t - 1) := by
        rw [pow_succ]
        ring
  refine ⟨t, ht, ?_, ?_⟩
  · linarith
  · rw [hpow]
    linarith

/-- The penultimate strong-band producer feeds canonical centrality without a
parity restriction or any power-of-two LCM-jump hypothesis. -/
theorem canonicalAdjacentSuffixCentralSupply_of_penultimateStrongBand
    (hsupply : CanonicalAdjacentSuffixPenultimateStrongBandSupply) :
    CanonicalAdjacentSuffixCentralSupply := by
  intro t₀
  obtain ⟨t, ht, hlo, hhi⟩ := hsupply t₀
  have ht3 : 3 ≤ t := (le_max_left 3 t₀).trans ht
  obtain ⟨hcanonicalLo, hcanonicalHi⟩ :=
    canonicalAdjacentSuffixResidue_central_of_penultimate_strongBand
      ht3 hlo hhi
  exact ⟨t, ht, hcanonicalLo, hcanonicalHi⟩

/-- Restricting the producer to strict LCM jumps still supplies the canonical
centrality interface. -/
theorem canonicalAdjacentSuffixCentralSupply_of_jump
    (hsupply : CanonicalAdjacentSuffixJumpCentralSupply) :
    CanonicalAdjacentSuffixCentralSupply := by
  intro t₀
  obtain ⟨t, ht, _hjump, hlo, hhi⟩ := hsupply t₀
  exact ⟨t, ht, hlo, hhi⟩

/-- Canonical centrality supplies the existing adjacent-gap interface; the
guard-bit and width obligations are discharged uniformly. -/
theorem diagonalAdjacentSuffixGapSupply_of_canonical
    (hsupply : CanonicalAdjacentSuffixCentralSupply) :
    DiagonalAdjacentSuffixGapSupply := by
  intro t₀
  obtain ⟨t, ht, hlo, hhi⟩ := hsupply t₀
  have ht3 : 3 ≤ t := (le_max_left 3 t₀).trans ht
  have ht₀ : t₀ ≤ t := (le_max_right 3 t₀).trans ht
  obtain ⟨hm, hwidth⟩ := canonicalAdjacentSuffixDepth_width ht3
  exact ⟨t, ht₀, canonicalAdjacentSuffixDepth t, hm, hwidth, hlo, hhi⟩

/- The fixed adjacent-gap supply feeds the existing diagonal projection
supply. -/
set_option maxHeartbeats 800000 in
theorem diagonalFreshLossProjectionSupply_of_adjacentSuffixGapSupply
    (hsupply : DiagonalAdjacentSuffixGapSupply) :
    DiagonalFreshLossProjectionSupply := by
  intro t₀
  obtain ⟨t, ht, m, hm, hwidth, hlo, hhi⟩ := hsupply t₀
  rcases diagonalFreshLossResidueCert_or_of_adjacent_dyadic_gap
      hm (by simpa using hwidth) hlo hhi with hcert | hcert
  · exact ⟨t, ht, m, by simpa using hcert⟩
  · exact ⟨t, ht, 1 + m, by simpa using hcert⟩

/-- The adjacent integer-gap interface is already sufficient for the global
irrationality consumer. -/
theorem irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply
    (hsupply : DiagonalAdjacentSuffixGapSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_diagonalFreshLossProjectionSupply
    (diagonalFreshLossProjectionSupply_of_adjacentSuffixGapSupply hsupply)

/-- Canonical adjacent-suffix centrality is sufficient for Erdős #249's
irrationality target through the already-landed adjacent-gap consumer. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply
    (hsupply : CanonicalAdjacentSuffixCentralSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply
    (diagonalAdjacentSuffixGapSupply_of_canonical hsupply)

/-- The exact signed penultimate-coordinate producer closes Erdős #249. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateExactSupply
    (hsupply : CanonicalAdjacentSuffixPenultimateExactSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply
    (canonicalAdjacentSuffixCentralSupply_iff_penultimateExact.mpr hsupply)

/-- The sharp penultimate-margin producer closes Erdős #249 through the
canonical adjacent-suffix consumer. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateMarginSupply
    (hsupply : CanonicalAdjacentSuffixPenultimateMarginSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply
    (canonicalAdjacentSuffixCentralSupply_of_penultimateMargin hsupply)

/-- The parity-complete penultimate-band producer closes Erdős #249 through
the canonical adjacent-suffix consumer. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateStrongBandSupply
    (hsupply : CanonicalAdjacentSuffixPenultimateStrongBandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply
    (canonicalAdjacentSuffixCentralSupply_of_penultimateStrongBand hsupply)

/-- Centrality at arbitrarily large strict LCM jumps already closes the
irrationality consumer. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixJumpCentralSupply
    (hsupply : CanonicalAdjacentSuffixJumpCentralSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply
    (canonicalAdjacentSuffixCentralSupply_of_jump hsupply)

/-- Nonnegative canonical slack at arbitrarily large strict LCM jumps closes
the same irrationality consumer. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixJumpSlackSupply
    (hsupply : CanonicalAdjacentSuffixJumpSlackSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totientSeries_of_canonicalAdjacentSuffixJumpCentralSupply
  exact (canonicalAdjacentSuffixJumpCentralSupply_iff_slackSupply).2 hsupply

/-- The post-jump producer closes Erdős #249 through plateau transport and
the existing canonical adjacent-suffix consumer. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixPostJumpSlackSupply
    (hsupply : CanonicalAdjacentSuffixPostJumpSlackSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_canonicalAdjacentSuffixJumpSlackSupply
    (canonicalAdjacentSuffixJumpSlackSupply_of_postJump hsupply)

/-- The cofinal power-of-two producer is sufficient for Erdős #249. -/
theorem irrational_totientSeries_of_canonicalAdjacentSuffixPowerTwoPostJumpSlackSupply
    (hsupply : CanonicalAdjacentSuffixPowerTwoPostJumpSlackSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_canonicalAdjacentSuffixPostJumpSlackSupply
    (canonicalAdjacentSuffixPostJumpSlackSupply_of_powerTwo hsupply)

/-! ## Kernel-checked composition fixture -/

set_option maxRecDepth 100000 in
/-- At `t = 7`, depth `13` gives the exact diagonal projection and its floor.
This is a bridge fixture, not evidence for an unbounded supply. -/
theorem diagonalFreshLossProjectionCell_seven :
    (2 * periodLcm 7 + 13 + 2 : ℤ) < 2 ^ 13 ∧
      diagonalFreshLossProjectionCert 7 13 := by
  decide

set_option maxRecDepth 100000 in
theorem diagonalFreshLossResidueCell_seven :
    diagonalFreshLossResidueCert 7 13 := by
  decide

/-- The existing `t = 7` full-target miss can be recovered through the new
operational composition seam. -/
theorem foreignDiagonalDefect_misses_fullTarget_seven_via_projection :
    ¬ForeignDiagonalDefectHitsFullTarget 7 := by
  exact foreignDiagonalDefect_misses_fullTarget_of_residueCert
    diagonalFreshLossResidueCell_seven

set_option maxRecDepth 100000 in
/-- At `t = 7`, the cut `J = 1` with suffix length `m = 12` is centrally
placed: the last twelve bits alone recover the landed `(7, 13)` projection.
A bridge fixture, not evidence for an unbounded supply. -/
theorem diagonalSuffixCell_seven :
    (periodLcm 7 + (1 + 12) + 2 : ℤ) < diagonalSuffixResidue 7 1 12 ∧
      diagonalSuffixResidue 7 1 12
        < 2 ^ 12 - (2 * periodLcm 7 + (1 + 12) + 2) := by
  decide

/-- The `t = 7` full-target miss re-derived from suffix bits only, through
the sliding-suffix transference theorem. -/
theorem foreignDiagonalDefect_misses_fullTarget_seven_via_suffix :
    ¬ForeignDiagonalDefectHitsFullTarget 7 :=
  foreignDiagonalDefect_misses_fullTarget_of_residueCert
    (diagonalFreshLossResidueCert_of_suffix_central
      diagonalSuffixCell_seven.1 diagonalSuffixCell_seven.2)

/-! ## Exact top-bit and correction-word obstruction -/

/-- Under the canonical small-correction hypothesis, target centrality has
only one nonautomatic inequality: the side selected by the top bit of the
penultimate residue. -/
theorem baseTwoTargetResidue_central_iff_topBit
    {m : ℕ} {d C : ℤ} (hm : 5 ≤ m)
    (hd0 : 0 ≤ d) (hdhi : d < (2 : ℤ) ^ (m - 1))
    (hC : |C| < (2 : ℤ) ^ (m - 5)) :
    ((2 : ℤ) ^ (m - 5) ≤ (2 * d + C) % 2 ^ m ∧
      (2 * d + C) % 2 ^ m ≤ 2 ^ m - 2 ^ (m - 5)) ↔
    ((d < (2 : ℤ) ^ (m - 2) ∧
        2 ^ (m - 5) ≤ 2 * d + C) ∨
      ((2 : ℤ) ^ (m - 2) ≤ d ∧
        2 * d + C ≤ 2 ^ m - 2 ^ (m - 5))) := by
  let K : ℤ := 2 ^ (m - 2)
  let e : ℤ := 2 ^ (m - 5)
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hepos : 0 < e := by dsimp [e]; positivity
  have hKe : K = 8 * e := by
    dsimp [K, e]
    calc
      (2 : ℤ) ^ (m - 2) = 2 ^ ((m - 5) + 3) := by
        congr 1
        omega
      _ = 8 * 2 ^ (m - 5) := by rw [pow_add]; norm_num; ring
  have hN : (2 : ℤ) ^ m = 4 * K := by
    dsimp [K]
    calc
      (2 : ℤ) ^ m = 2 ^ ((m - 2) + 2) := by
        congr 1
        omega
      _ = 4 * 2 ^ (m - 2) := by rw [pow_add]; norm_num; ring
  have habs := abs_lt.mp hC
  have habsE : -e < C ∧ C < e := by simpa [e] using habs
  rw [baseTwoTargetResidue_central_iff_unwrapped hm hd0 hdhi hC]
  constructor
  · intro hcentral
    by_cases htop : d < K
    · exact Or.inl ⟨htop, hcentral.1⟩
    · exact Or.inr ⟨le_of_not_gt htop, hcentral.2⟩
  · rintro (⟨hdK, hlo⟩ | ⟨hKd, hhi⟩)
    · refine ⟨hlo, ?_⟩
      change 2 * d + C ≤ 2 ^ m - e
      rw [hN]
      linarith
    · refine ⟨?_, hhi⟩
      change e ≤ 2 * d + C
      linarith

/-- Exact failure form: noncentrality is precisely alignment of the
penultimate top bit with the corresponding signed edge excursion. -/
theorem baseTwoTargetResidue_noncentral_iff_carryEdgeAlignment
    {m : ℕ} {d C : ℤ} (hm : 5 ≤ m)
    (hd0 : 0 ≤ d) (hdhi : d < (2 : ℤ) ^ (m - 1))
    (hC : |C| < (2 : ℤ) ^ (m - 5)) :
    (¬ ((2 : ℤ) ^ (m - 5) ≤ (2 * d + C) % 2 ^ m ∧
      (2 * d + C) % 2 ^ m ≤ 2 ^ m - 2 ^ (m - 5))) ↔
    ((d < (2 : ℤ) ^ (m - 2) ∧
        2 * d + C < 2 ^ (m - 5)) ∨
      ((2 : ℤ) ^ (m - 2) ≤ d ∧
        2 ^ m - 2 ^ (m - 5) < 2 * d + C)) := by
  have htop :=
    baseTwoTargetResidue_central_iff_topBit hm hd0 hdhi hC
  constructor
  · intro hnot
    by_cases hdK : d < (2 : ℤ) ^ (m - 2)
    · left
      refine ⟨hdK, ?_⟩
      by_contra hlo
      apply hnot
      apply htop.mpr
      exact Or.inl ⟨hdK, le_of_not_gt hlo⟩
    · right
      have hKd : (2 : ℤ) ^ (m - 2) ≤ d := le_of_not_gt hdK
      refine ⟨hKd, ?_⟩
      by_contra hhi
      apply hnot
      apply htop.mpr
      exact Or.inr ⟨hKd, le_of_not_gt hhi⟩
  · rintro (⟨hdK, hlo⟩ | ⟨hKd, hhi⟩) hcentral
    · rcases htop.mp hcentral with hleft | hright
      · omega
      · omega
    · rcases htop.mp hcentral with hleft | hright
      · omega
      · omega

/-- A power-of-two LCM jump adds exactly one canonical bit. -/
theorem canonicalAdjacentSuffixDepth_powerTwo_jump
    {a : ℕ} (ha : 2 ≤ a) :
    canonicalAdjacentSuffixDepth (2 ^ a) =
      canonicalAdjacentSuffixDepth (2 ^ a - 1) + 1 := by
  unfold canonicalAdjacentSuffixDepth
  rw [periodLcm_pow_two_eq_two_mul ha]
  simp only [Nat.log2_eq_log_two]
  rw [show 2 * periodLcm (2 ^ a - 1) =
      periodLcm (2 ^ a - 1) * 2 by omega,
    Nat.log_mul_base (by norm_num) (periodLcm_pos _).ne']

/-- If the pre-jump canonical depth is even, the target correction is the
next inherited even increment minus the current fresh odd increment. -/
theorem diagonalTargetDepthCorrection_powerTwo_of_even_predepth
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth : canonicalAdjacentSuffixDepth (2 ^ a - 1) = 2 * q) :
    diagonalTargetDepthCorrection (2 ^ a)
        (canonicalAdjacentSuffixDepth (2 ^ a)) =
      powerTwoInheritedIncrement a (q + 1) -
        powerTwoFreshOddIncrement a q := by
  have hjump := canonicalAdjacentSuffixDepth_powerTwo_jump ha
  unfold diagonalTargetDepthCorrection
  rw [hjump, hdepth,
    show 2 * q + 1 + 1 = 2 * (q + 1) by omega,
    diagonalWindowIncrement_powerTwoJump_even_offset ha]
  unfold powerTwoFreshOddIncrement
  ring

/-- If the pre-jump canonical depth is odd, the target correction is the
next fresh odd increment minus the matching inherited even increment. -/
theorem diagonalTargetDepthCorrection_powerTwo_of_odd_predepth
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth : canonicalAdjacentSuffixDepth (2 ^ a - 1) = 2 * q + 1) :
    diagonalTargetDepthCorrection (2 ^ a)
        (canonicalAdjacentSuffixDepth (2 ^ a)) =
      powerTwoFreshOddIncrement a (q + 1) -
        powerTwoInheritedIncrement a (q + 1) := by
  have hjump := canonicalAdjacentSuffixDepth_powerTwo_jump ha
  unfold diagonalTargetDepthCorrection
  rw [hjump, hdepth,
    show 2 * q + 1 + 1 + 1 = 2 * (q + 1) + 1 by omega,
    show 2 * q + 1 + 1 = 2 * (q + 1) by omega,
    diagonalWindowIncrement_powerTwoJump_even_offset ha]
  unfold powerTwoFreshOddIncrement
  ring

/-- The base-four word of all odd-depth corrections through step `q`. -/
def powerTwoOddCorrectionWord (a q : ℕ) : ℤ :=
  ∑ n ∈ Finset.range q,
    powerTwoOddDepthCorrection a n * (4 : ℤ) ^ (q - 1 - n)

/-- Appending one correction is the affine base-four recurrence. -/
theorem powerTwoOddCorrectionWord_succ (a q : ℕ) :
    powerTwoOddCorrectionWord a (q + 1) =
      4 * powerTwoOddCorrectionWord a q +
        powerTwoOddDepthCorrection a q := by
  unfold powerTwoOddCorrectionWord
  rw [Finset.sum_range_succ]
  have hsum :
      (∑ n ∈ Finset.range q,
          powerTwoOddDepthCorrection a n * (4 : ℤ) ^ (q + 1 - 1 - n)) =
        4 * ∑ n ∈ Finset.range q,
          powerTwoOddDepthCorrection a n * (4 : ℤ) ^ (q - 1 - n) := by
    calc
      (∑ n ∈ Finset.range q,
          powerTwoOddDepthCorrection a n * (4 : ℤ) ^ (q + 1 - 1 - n)) =
        ∑ n ∈ Finset.range q,
          4 * (powerTwoOddDepthCorrection a n *
            (4 : ℤ) ^ (q - 1 - n)) := by
              apply Finset.sum_congr rfl
              intro n hn
              have hnq : n < q := Finset.mem_range.mp hn
              rw [show q + 1 - 1 - n = (q - 1 - n) + 1 by omega,
                pow_succ]
              ring
      _ = 4 * ∑ n ∈ Finset.range q,
          powerTwoOddDepthCorrection a n * (4 : ℤ) ^ (q - 1 - n) := by
            rw [Finset.mul_sum]
  rw [hsum]
  simp

/-- Closed raw odd-depth orbit at a power-of-two endpoint. -/
theorem diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_closed
    {a q : ℕ} (ha : 2 ≤ a) :
    diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) =
      (4 : ℤ) ^ q *
          diagonalAdjacentSuffixRawBlock (2 ^ a) 0 1 +
        powerTwoOddCorrectionWord a q := by
  induction q with
  | zero =>
      simp [powerTwoOddCorrectionWord]
  | succ q ih =>
      rw [show 2 * (q + 1) + 1 = 2 * (q + 1) + 1 by rfl,
        diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_step ha,
        ih, powerTwoOddCorrectionWord_succ, pow_succ]
      unfold powerTwoOddDepthCorrection
      ring

/-- Closed residue form of the odd-depth orbit. -/
theorem diagonalAdjacentSuffixResidue_powerTwo_oddDepth_closed
    {a q : ℕ} (ha : 2 ≤ a) :
    diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) =
      ((4 : ℤ) ^ q *
          diagonalAdjacentSuffixRawBlock (2 ^ a) 0 1 +
        powerTwoOddCorrectionWord a q) % 2 ^ (2 * q + 1) := by
  rw [diagonalAdjacentSuffixResidue_eq_rawBlock,
    diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_closed ha]

/-- The seed contributes only the top bit at odd depth: all lower `2q` bits
are exactly the correction word modulo `4^q`. -/
theorem diagonalAdjacentSuffixResidue_powerTwo_oddDepth_lowBits
    {a q : ℕ} (ha : 2 ≤ a) :
    diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) % (4 : ℤ) ^ q =
      powerTwoOddCorrectionWord a q % (4 : ℤ) ^ q := by
  have hpow : (2 : ℤ) ^ (2 * q + 1) = 2 * (4 : ℤ) ^ q := by
    calc
      (2 : ℤ) ^ (2 * q + 1) = 2 ^ (2 * q) * 2 ^ 1 := by rw [pow_add]
      _ = (2 ^ 2 : ℤ) ^ q * 2 := by rw [pow_mul]; norm_num
      _ = 2 * (4 : ℤ) ^ q := by norm_num; ring
  have hdvd : ((4 : ℤ) ^ q) ∣ 2 ^ (2 * q + 1) := by
    use 2
    rw [hpow]
    ring
  rw [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_closed ha,
    Int.emod_emod_of_dvd _ hdvd]
  rw [show (4 : ℤ) ^ q *
      diagonalAdjacentSuffixRawBlock (2 ^ a) 0 1 +
        powerTwoOddCorrectionWord a q =
      powerTwoOddCorrectionWord a q + (4 : ℤ) ^ q *
        diagonalAdjacentSuffixRawBlock (2 ^ a) 0 1 by ring,
    Int.add_mul_emod_self_left]

/-- Once the LCM height is at least two, every positive-offset diagonal
increment is even: both totients are even before taking their difference. -/
theorem diagonalWindowIncrement_even_of_two_le_periodLcm
    {t s : ℕ} (hH : 2 ≤ periodLcm t) (hs : 1 ≤ s) :
    Even (diagonalWindowIncrement t s) := by
  have htop : 2 < 2 * periodLcm t + s := by omega
  have hbot : 2 < periodLcm t + s := by omega
  obtain ⟨u, hu⟩ := Nat.totient_even htop
  obtain ⟨v, hv⟩ := Nat.totient_even hbot
  refine ⟨(u : ℤ) - (v : ℤ), ?_⟩
  unfold diagonalWindowIncrement
  rw [hu, hv]
  push_cast
  ring

/-- Once the offset is at least two, both totient arguments exceed two, so
the diagonal increment is even without any hypothesis on the LCM height. -/
theorem diagonalWindowIncrement_even_of_two_le_offset
    {t s : ℕ} (hs : 2 ≤ s) :
    Even (diagonalWindowIncrement t s) := by
  have hH : 0 < periodLcm t := periodLcm_pos t
  have htop : 2 < 2 * periodLcm t + s := by omega
  have hbot : 2 < periodLcm t + s := by omega
  obtain ⟨u, hu⟩ := Nat.totient_even htop
  obtain ⟨v, hv⟩ := Nat.totient_even hbot
  refine ⟨(u : ℤ) - (v : ℤ), ?_⟩
  unfold diagonalWindowIncrement
  rw [hu, hv]
  push_cast
  ring

/-- Every odd-depth power-of-two correction is even.  The fresh term is at
offset at least three, the last inherited term is at reduced offset at least
two, and the middle inherited term already carries a factor two. -/
theorem powerTwoOddDepthCorrection_even (a n : ℕ) :
    Even (powerTwoOddDepthCorrection a n) := by
  have hFresh : Even (powerTwoFreshOddIncrement a (n + 1)) := by
    unfold powerTwoFreshOddIncrement
    apply diagonalWindowIncrement_even_of_two_le_offset
    omega
  have hLast : Even (powerTwoInheritedIncrement a (n + 2)) := by
    unfold powerTwoInheritedIncrement
    split_ifs with hparity
    · exact even_two_mul _
    · apply diagonalWindowIncrement_even_of_two_le_offset
      omega
  obtain ⟨f, hf⟩ := hFresh
  obtain ⟨ℓ, hℓ⟩ := hLast
  refine ⟨f - powerTwoInheritedIncrement a (n + 1) + ℓ, ?_⟩
  unfold powerTwoOddDepthCorrection
  rw [hf, hℓ]
  ring

/-- The seed of the odd-depth power-of-two orbit is even. -/
theorem diagonalAdjacentSuffixRawBlock_powerTwo_zero_one_even
    {a : ℕ} (ha : 2 ≤ a) :
    Even (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 1) := by
  have hpow4 : 4 ≤ 2 ^ a := by
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) ha)
  have hH : 2 ≤ periodLcm (2 ^ a) := by
    exact le_trans (by omega) (le_periodLcm (2 ^ a))
  have h1 : Even (diagonalWindowIncrement (2 ^ a) 1) :=
    diagonalWindowIncrement_even_of_two_le_periodLcm hH (by omega)
  have h2 : Even (diagonalWindowIncrement (2 ^ a) 2) :=
    diagonalWindowIncrement_even_of_two_le_periodLcm hH (by omega)
  simpa [diagonalAdjacentSuffixRawBlock] using h1.add h2

/-- The even seed vanishes modulo the full odd-depth modulus, so the
correction word determines every bit of the residue, including its top bit. -/
theorem diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_correctionWord
    {a q : ℕ} (ha : 2 ≤ a) :
    diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) =
      powerTwoOddCorrectionWord a q % 2 ^ (2 * q + 1) := by
  rw [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_closed ha]
  obtain ⟨k, hk⟩ :=
    diagonalAdjacentSuffixRawBlock_powerTwo_zero_one_even ha
  have hpow : (2 : ℤ) ^ (2 * q + 1) = 2 * (4 : ℤ) ^ q := by
    calc
      (2 : ℤ) ^ (2 * q + 1) = 2 ^ (2 * q) * 2 ^ 1 := by rw [pow_add]
      _ = (2 ^ 2 : ℤ) ^ q * 2 := by rw [pow_mul]; norm_num
      _ = 2 * (4 : ℤ) ^ q := by norm_num; ring
  rw [hpow, hk]
  rw [show (4 : ℤ) ^ q * (k + k) + powerTwoOddCorrectionWord a q =
      powerTwoOddCorrectionWord a q +
        (2 * (4 : ℤ) ^ q) * k by ring,
    Int.add_mul_emod_self_left]

/-- The integral half-correction cocycle. -/
def powerTwoOddHalfCorrectionWord (a : ℕ) : ℕ → ℤ
  | 0 => 0
  | q + 1 =>
      4 * powerTwoOddHalfCorrectionWord a q +
        powerTwoOddDepthCorrection a q / 2

/-- Appending one half-correction is the integral base-four recurrence. -/
theorem powerTwoOddHalfCorrectionWord_succ (a q : ℕ) :
    powerTwoOddHalfCorrectionWord a (q + 1) =
      4 * powerTwoOddHalfCorrectionWord a q +
        powerTwoOddDepthCorrection a q / 2 := by
  rfl

/-- The old correction word is exactly twice the integral half-word. -/
theorem powerTwoOddCorrectionWord_eq_two_mul_halfWord (a q : ℕ) :
    powerTwoOddCorrectionWord a q =
      2 * powerTwoOddHalfCorrectionWord a q := by
  induction q with
  | zero =>
      simp [powerTwoOddCorrectionWord, powerTwoOddHalfCorrectionWord]
  | succ q ih =>
      rw [powerTwoOddCorrectionWord_succ,
        powerTwoOddHalfCorrectionWord_succ, ih]
      have hhalf :
          2 * (powerTwoOddDepthCorrection a q / 2) =
            powerTwoOddDepthCorrection a q :=
        Int.two_mul_ediv_two_of_even (powerTwoOddDepthCorrection_even a q)
      omega

/-- At every odd depth, the residue is twice one residue modulo `4^q`.
This removes the separate quotient-parity state from the correction-word
description. -/
theorem diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_two_mul_halfWord
    {a q : ℕ} (ha : 2 ≤ a) :
    diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) =
      2 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) := by
  rw [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_correctionWord ha,
    powerTwoOddCorrectionWord_eq_two_mul_halfWord]
  have hpow : (2 : ℤ) ^ (2 * q + 1) = 2 * (4 : ℤ) ^ q := by
    calc
      (2 : ℤ) ^ (2 * q + 1) = 2 ^ (2 * q) * 2 ^ 1 := by rw [pow_add]
      _ = (2 ^ 2 : ℤ) ^ q * 2 := by rw [pow_mul]; norm_num
      _ = 2 * (4 : ℤ) ^ q := by norm_num; ring
  rw [hpow]
  exact Int.mul_emod_mul_of_pos
    (powerTwoOddHalfCorrectionWord a q) ((4 : ℤ) ^ q) (by norm_num)

/-- For `q ≥ 3`, odd-depth centrality is exactly avoidance of the two
width-`1/32` edge cylinders by the integral base-four half-word. -/
theorem
    diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand
    {a q : ℕ} (ha : 2 ≤ a) (hq : 3 ≤ q) :
    ((2 : ℤ) ^ (2 * q + 1 - 5) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) ≤
          2 ^ (2 * q + 1) - 2 ^ (2 * q + 1 - 5)) ↔
      ((4 : ℤ) ^ q ≤
          32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ∧
        32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ≤
          31 * (4 : ℤ) ^ q) := by
  rw [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_two_mul_halfWord ha]
  have hmodulus : (2 : ℤ) ^ (2 * q + 1) = 2 * (4 : ℤ) ^ q := by
    calc
      (2 : ℤ) ^ (2 * q + 1) = 2 ^ (2 * q) * 2 ^ 1 := by rw [pow_add]
      _ = (2 ^ 2 : ℤ) ^ q * 2 := by rw [pow_mul]; norm_num
      _ = 2 * (4 : ℤ) ^ q := by norm_num; ring
  have hedge : (4 : ℤ) ^ q = 16 * 2 ^ (2 * q + 1 - 5) := by
    calc
      (4 : ℤ) ^ q = (2 ^ 2 : ℤ) ^ q := by norm_num
      _ = 2 ^ (2 * q) := by rw [pow_mul]
      _ = 2 ^ ((2 * q + 1 - 5) + 4) := by
        congr 1
        omega
      _ = 16 * 2 ^ (2 * q + 1 - 5) := by
        rw [pow_add]
        norm_num
        ring
  rw [hmodulus]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> omega

/-! ## Signed old/foreign half-word consumer

This is a finite exact consumer.  The literal foreign block is now identified,
but a cofinal proof must still supply its signed phase relative to the old
gcd-word block. -/

/-- Sufficient signed-coordinate conditions for a central sum modulo `M`.
The same-direction branch prevents a wrap into the opposite edge; the
opposite-direction branch prevents cancellation into the edge about zero. -/
def SignedSplitSafe (x y M e : ℤ) : Prop :=
  0 < e ∧
  M = 32 * e ∧
  |x| ≤ M / 2 ∧
  |y| ≤ M / 2 ∧
  e ≤ |x| ∧
  ((0 ≤ x * y ∧ |x| + |y| ≤ M - e) ∨
    (x * y < 0 ∧ e ≤ abs (|x| - |y|)))

/-- A short signed representative whose magnitude lies between the edge and
its complementary radius has a central Euclidean residue. -/
theorem emod_central_of_abs_between
    {z M e : ℤ} (_hM : 0 < M) (he : 0 < e)
    (hlo : e ≤ |z|) (hhi : |z| ≤ M - e) :
    e ≤ z % M ∧ z % M ≤ M - e := by
  by_cases hz : 0 ≤ z
  · have hzM : z < M := by
      rw [abs_of_nonneg hz] at hhi
      omega
    rw [abs_of_nonneg hz] at hlo hhi
    rw [Int.emod_eq_of_lt hz hzM]
    exact ⟨hlo, hhi⟩
  · have hzneg : z < 0 := lt_of_not_ge hz
    have habs : |z| = -z := abs_of_neg hzneg
    rw [habs] at hlo hhi
    have hzadd0 : 0 ≤ z + M := by omega
    have hzaddM : z + M < M := by omega
    have hmod : z % M = z + M := by
      calc
        z % M = (z + M) % M := (Int.add_emod_right z M).symm
        _ = z + M := Int.emod_eq_of_lt hzadd0 hzaddM
    rw [hmod]
    omega

/-- The expanded phase condition puts the unwrapped sum between the two
signed edge radii. -/
theorem abs_add_between_of_signedSplitSafe
    {x y M e : ℤ} (h : SignedSplitSafe x y M e) :
    e ≤ |x + y| ∧ |x + y| ≤ M - e := by
  rcases h with ⟨he, hscale, hxBound, hyBound, hxCentral, hphase⟩
  have hhalf : M / 2 ≤ M - e := by
    rw [hscale]
    omega
  rcases hphase with ⟨hsame, hsum⟩ | ⟨hopp, hdiff⟩
  · have habs : |x + y| = |x| + |y| :=
      (abs_add_eq_add_abs_iff x y).2 ((Int.mul_nonneg_iff).1 hsame)
    rw [habs]
    exact ⟨hxCentral.trans (le_add_of_nonneg_right (abs_nonneg y)), hsum⟩
  · constructor
    · calc
        e ≤ abs (|x| - |y|) := hdiff
        _ ≤ |x + y| := by
          have hreverse := abs_abs_sub_abs_le_abs_sub x (-y)
          simpa [abs_neg, sub_neg_eq_add] using hreverse
    · by_cases hx : 0 ≤ x
      · have hy : y < 0 := by
          by_contra hnot
          have hy0 : 0 ≤ y := le_of_not_gt hnot
          exact (not_lt_of_ge (mul_nonneg hx hy0)) hopp
        by_cases hsum0 : 0 ≤ x + y
        · rw [abs_of_nonneg hsum0]
          have hxy : x + y ≤ x := by omega
          have hxAbs : x ≤ M / 2 := by
            simpa [abs_of_nonneg hx] using hxBound
          exact hxy.trans (hxAbs.trans hhalf)
        · have hsumNonpos : x + y ≤ 0 := le_of_not_ge hsum0
          rw [abs_of_nonpos hsumNonpos]
          have hxy : -(x + y) ≤ -y := by omega
          have hyAbs : -y ≤ M / 2 := by
            simpa [abs_of_neg hy] using hyBound
          exact hxy.trans (hyAbs.trans hhalf)
      · have hxneg : x < 0 := lt_of_not_ge hx
        have hy : 0 < y := by
          by_contra hnot
          have hy0 : y ≤ 0 := le_of_not_gt hnot
          exact (not_lt_of_ge
            (mul_nonneg_of_nonpos_of_nonpos hxneg.le hy0)) hopp
        by_cases hsum0 : 0 ≤ x + y
        · rw [abs_of_nonneg hsum0]
          have hxy : x + y ≤ y := by omega
          have hyAbs : y ≤ M / 2 := by
            simpa [abs_of_pos hy] using hyBound
          exact hxy.trans (hyAbs.trans hhalf)
        · have hsumNonpos : x + y ≤ 0 := le_of_not_ge hsum0
          rw [abs_of_nonpos hsumNonpos]
          have hxy : -(x + y) ≤ -x := by omega
          have hxAbs : -x ≤ M / 2 := by
            simpa [abs_of_neg hxneg] using hxBound
          exact hxy.trans (hxAbs.trans hhalf)

/-- The signed old/foreign phase conditions exclude both width-`e` edge
cylinders after recombination modulo `M`. -/
theorem signedSplitSafe_emod_central
    {x y M e : ℤ} (h : SignedSplitSafe x y M e) :
    e ≤ (x + y) % M ∧ (x + y) % M ≤ M - e := by
  have he : 0 < e := h.1
  have hscale : M = 32 * e := h.2.1
  have hM : 0 < M := by rw [hscale]; positivity
  exact emod_central_of_abs_between hM he
    (abs_add_between_of_signedSplitSafe h).1
    (abs_add_between_of_signedSplitSafe h).2

/-- Integer halving is additive when both summands are even. -/
theorem add_ediv_two_of_even {A B : ℤ} (hA : Even A) (hB : Even B) :
    (A + B) / 2 = A / 2 + B / 2 := by
  rcases hA with ⟨a, ha⟩
  rcases hB with ⟨b, hb⟩
  rw [ha, hb]
  have htwo : (2 : ℤ) ≠ 0 := by norm_num
  calc
    ((a + a) + (b + b)) / 2 = (2 * (a + b)) / 2 := by ring_nf
    _ = a + b := Int.mul_ediv_cancel_left _ htwo
    _ = (a + a) / 2 + (b + b) / 2 := by
      rw [show a + a = 2 * a by ring,
        show b + b = 2 * b by ring,
        Int.mul_ediv_cancel_left _ htwo,
        Int.mul_ediv_cancel_left _ htwo]

/-- Signed representatives of the exact old and literal foreign half-blocks
put the actual reversed dyadic numerator in the central band. -/
theorem diagonalAdjacentSuffixRawBlock_half_central_of_signedSplit
    {t J m : ℕ} {x y M e : ℤ}
    (hOldEven : Even (oldMobiusRawBlock (periodLcm t) J m))
    (hForeignEven : Even (finiteForeignChannelRawBlock (periodLcm t) J m))
    (hx : Int.ModEq M (oldMobiusRawBlock (periodLcm t) J m / 2) x)
    (hy : Int.ModEq M
      (finiteForeignChannelRawBlock (periodLcm t) J m / 2) y)
    (hSafe : SignedSplitSafe x y M e) :
    e ≤ (diagonalAdjacentSuffixRawBlock t J m / 2) % M ∧
      (diagonalAdjacentSuffixRawBlock t J m / 2) % M ≤ M - e := by
  have hhalf :
      diagonalAdjacentSuffixRawBlock t J m / 2 =
        oldMobiusRawBlock (periodLcm t) J m / 2 +
          finiteForeignChannelRawBlock (periodLcm t) J m / 2 := by
    rw [diagonalAdjacentSuffixRawBlock_eq_oldMobius_add_finiteForeign]
    exact add_ediv_two_of_even hOldEven hForeignEven
  have hmod : Int.ModEq M
      (diagonalAdjacentSuffixRawBlock t J m / 2) (x + y) := by
    rw [hhalf]
    exact hx.add hy
  rw [hmod.eq]
  exact signedSplitSafe_emod_central hSafe

/-- At a power-of-two endpoint and odd depth, the actual raw half-numerator
and the integral half-correction word agree modulo `4^q`. -/
theorem diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_half_emod
    {a q : ℕ} (ha : 2 ≤ a) :
    (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2) %
        (4 : ℤ) ^ q =
      powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q := by
  rw [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_closed ha,
    powerTwoOddCorrectionWord_eq_two_mul_halfWord]
  obtain ⟨k, hk⟩ :=
    diagonalAdjacentSuffixRawBlock_powerTwo_zero_one_even ha
  rw [hk]
  have htwo : (2 : ℤ) ≠ 0 := by norm_num
  rw [show
      (4 : ℤ) ^ q * (k + k) + 2 * powerTwoOddHalfCorrectionWord a q =
        2 * ((4 : ℤ) ^ q * k + powerTwoOddHalfCorrectionWord a q) by ring,
    Int.mul_ediv_cancel_left _ htwo]
  rw [show
      (4 : ℤ) ^ q * k + powerTwoOddHalfCorrectionWord a q =
        powerTwoOddHalfCorrectionWord a q + (4 : ℤ) ^ q * k by ring,
    Int.add_mul_emod_self_left]

/-- The actual raw numerator is even at every power-two odd depth. -/
theorem diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_even
    {a q : ℕ} (ha : 2 ≤ a) :
    Even (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1)) := by
  rw [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_closed ha,
    powerTwoOddCorrectionWord_eq_two_mul_halfWord]
  obtain ⟨k, hk⟩ :=
    diagonalAdjacentSuffixRawBlock_powerTwo_zero_one_even ha
  refine ⟨(4 : ℤ) ^ q * k + powerTwoOddHalfCorrectionWord a q, ?_⟩
  rw [hk]
  ring

/-- Evenness of the old block forces evenness of the exact literal foreign
block at a power-two odd depth. -/
theorem finiteForeignChannelRawBlock_powerTwo_oddDepth_even_of_old
    {a q : ℕ} (ha : 2 ≤ a)
    (hOldEven : Even
      (oldMobiusRawBlock (periodLcm (2 ^ a)) 0 (2 * q + 1))) :
    Even (finiteForeignChannelRawBlock (periodLcm (2 ^ a)) 0 (2 * q + 1)) := by
  rw [← diagonalAdjacentSuffixRawBlock_sub_oldMobius_eq_finiteForeign]
  obtain ⟨r, hr⟩ :=
    diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_even (q := q) ha
  obtain ⟨o, ho⟩ := hOldEven
  refine ⟨r - o, ?_⟩
  rw [hr, ho]
  ring

/-- Power-two specialization whose conclusion is exactly the half-word band
consumed by the landed odd-depth centrality bridge. -/
theorem powerTwoOddHalfWordBand_of_signedSplit
    {a q : ℕ} {x y : ℤ}
    (ha : 2 ≤ a)
    (hOldEven : Even
      (oldMobiusRawBlock (periodLcm (2 ^ a)) 0 (2 * q + 1)))
    (hx : Int.ModEq ((4 : ℤ) ^ q)
      (oldMobiusRawBlock (periodLcm (2 ^ a)) 0 (2 * q + 1) / 2) x)
    (hy : Int.ModEq ((4 : ℤ) ^ q)
      (finiteForeignChannelRawBlock (periodLcm (2 ^ a)) 0 (2 * q + 1) / 2) y)
    (hSafe : SignedSplitSafe x y ((4 : ℤ) ^ q) ((4 : ℤ) ^ q / 32)) :
    (4 : ℤ) ^ q ≤
        32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ∧
      32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ≤
        31 * (4 : ℤ) ^ q := by
  have hForeignEven :=
    finiteForeignChannelRawBlock_powerTwo_oddDepth_even_of_old ha hOldEven
  have hcentral :=
    diagonalAdjacentSuffixRawBlock_half_central_of_signedSplit
      hOldEven hForeignEven hx hy hSafe
  rw [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_half_emod ha] at hcentral
  have hscale : (4 : ℤ) ^ q = 32 * ((4 : ℤ) ^ q / 32) := hSafe.2.1
  rcases hcentral with ⟨hlo, hhi⟩
  constructor <;> nlinarith

/-- Direct composition into the actual odd-depth adjacent suffix residue. -/
theorem diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_of_signedSplit
    {a q : ℕ} {x y : ℤ}
    (ha : 2 ≤ a) (hq : 3 ≤ q)
    (hOldEven : Even
      (oldMobiusRawBlock (periodLcm (2 ^ a)) 0 (2 * q + 1)))
    (hx : Int.ModEq ((4 : ℤ) ^ q)
      (oldMobiusRawBlock (periodLcm (2 ^ a)) 0 (2 * q + 1) / 2) x)
    (hy : Int.ModEq ((4 : ℤ) ^ q)
      (finiteForeignChannelRawBlock (periodLcm (2 ^ a)) 0 (2 * q + 1) / 2) y)
    (hSafe : SignedSplitSafe x y ((4 : ℤ) ^ q) ((4 : ℤ) ^ q / 32)) :
    (2 : ℤ) ^ (2 * q + 1 - 5) ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) ∧
      diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) ≤
        2 ^ (2 * q + 1) - 2 ^ (2 * q + 1 - 5) := by
  apply
    (diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand
      ha hq).2
  exact powerTwoOddHalfWordBand_of_signedSplit ha hOldEven hx hy hSafe

/-- Exact canonical divisor/foreign signed-lift fixtures from the committed
`a = 2,...,7` receipts. -/
theorem canonical_a2_to_a7_signedSplitSafe_fixture :
    SignedSplitSafe 1885 398 4096 128 ∧
    SignedSplitSafe (-14332) (-3412) 262144 8192 ∧
    SignedSplitSafe 123429848 (-6535674) 268435456 8388608 ∧
    SignedSplitSafe
      (-11208283820533056) (-4719367739930368)
      72057594037927936 2251799813685248 ∧
    SignedSplitSafe
      34992883801785560027522301568
      83065005063982955973198999392
      316912650057057350374175801344
      9903520314283042199192993792 ∧
    SignedSplitSafe
      1945202069971848108810236964520900155182584521474982889792
      (-1467056972367226077870162149624493639484182929705300579872)
      6277101735386680763835789423207666416102355444464034512896
      196159429230833773869868419475239575503198607639501078528 := by
  norm_num [SignedSplitSafe, abs_of_nonneg, abs_of_nonpos]

/-! ### Exact two-rank obstruction -/

/-- `A` lies in the open radius-`e` cylinder about a multiple of `M`. -/
def NearMultiple (A M e : ℤ) : Prop :=
  ∃ k : ℤ, |A - M * k| < e

/-- Exact conversion between an edge-cylinder representative and the two
edge intervals of its Euclidean residue. -/
theorem nearMultiple_iff_emod_edge
    {A M e : ℤ} (hM : 0 < M) (he : 0 < e) (hwidth : 2 * e < M) :
    NearMultiple A M e ↔ A % M < e ∨ M - e < A % M := by
  constructor
  · rintro ⟨k, hk⟩
    rw [abs_lt] at hk
    let x : ℤ := A - M * k
    have hx : -e < x ∧ x < e := by simpa [x] using hk
    have hA : A = x + M * k := by simp [x]
    rw [hA, Int.add_mul_emod_self_left]
    by_cases hx0 : 0 ≤ x
    · left
      rw [Int.emod_eq_of_lt hx0 (by omega)]
      exact hx.2
    · right
      have hxneg : x < 0 := by omega
      rw [show x = (x + M) - M by ring, Int.sub_emod_right,
        Int.emod_eq_of_lt (by omega) (by omega)]
      omega
  · intro hedge
    have hr0 : 0 ≤ A % M := Int.emod_nonneg A hM.ne'
    have hrM : A % M < M := Int.emod_lt_of_pos A hM
    have hdecomp : M * (A / M) + A % M = A :=
      Int.mul_ediv_add_emod A M
    rcases hedge with hlo | hhi
    · refine ⟨A / M, ?_⟩
      have heq : A - M * (A / M) = A % M := by linarith
      rw [heq, abs_of_nonneg hr0]
      exact hlo
    · refine ⟨A / M + 1, ?_⟩
      have heq : A - M * (A / M + 1) = A % M - M := by
        linarith
      rw [heq, abs_of_nonpos (by omega)]
      omega

/-- Two consecutive edge-cylinder hits force the intervening base-four
correction into a cylinder four times wider around a multiple of the new
modulus.  At dyadic width `M = 32e`, this says that the correction is within
`M/4` of a multiple of `4M`. -/
theorem nearMultiple_correction_of_twoRank
    {A B C M e : ℤ}
    (hA : NearMultiple A M e)
    (hB : NearMultiple B (4 * M) (4 * e))
    (hstep : B = 4 * A + C) :
    NearMultiple C (4 * M) (8 * e) := by
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  refine ⟨l - k, ?_⟩
  rw [abs_lt] at hk hl ⊢
  constructor <;> nlinarith

/-- Direct specialization to the power-of-two odd-depth raw cocycle.  Its
hypotheses are exactly two consecutive edge-cylinder occupations. -/
theorem powerTwoOddDepthCorrection_nearMultiple_of_twoRank
    {a q : ℕ} (ha : 2 ≤ a)
    (hOld : NearMultiple
      (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1))
      ((2 : ℤ) ^ (2 * q + 1)) ((2 : ℤ) ^ (2 * q + 1 - 5)))
    (hNew : NearMultiple
      (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * (q + 1) + 1))
      (4 * (2 : ℤ) ^ (2 * q + 1))
      (4 * (2 : ℤ) ^ (2 * q + 1 - 5))) :
    NearMultiple (powerTwoOddDepthCorrection a q)
      (4 * (2 : ℤ) ^ (2 * q + 1))
      (8 * (2 : ℤ) ^ (2 * q + 1 - 5)) := by
  apply nearMultiple_correction_of_twoRank hOld hNew
  rw [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_step ha]
  unfold powerTwoOddDepthCorrection
  ring

/-- A direct three-letter envelope for the base-four correction. -/
theorem abs_powerTwoOddDepthCorrection_le
    {a n : ℕ} (ha : 2 ≤ a) :
    |powerTwoOddDepthCorrection a n| ≤
      (8 * periodLcm (2 ^ a) + 8 * n + 11 : ℤ) := by
  have hFresh := abs_diagonalWindowIncrement_le
    (2 ^ a) (2 * (n + 1) + 1)
  have hOld := abs_diagonalWindowIncrement_le
    (2 ^ a) (2 * (n + 1))
  have hNew := abs_diagonalWindowIncrement_le
    (2 ^ a) (2 * (n + 2))
  unfold powerTwoOddDepthCorrection powerTwoFreshOddIncrement
  rw [← diagonalWindowIncrement_powerTwoJump_even_offset ha,
    ← diagonalWindowIncrement_powerTwoJump_even_offset ha]
  rw [abs_le] at hFresh hOld hNew ⊢
  constructor <;> omega

/-! ### Odd-guarded power-of-two producer -/

/-- Make the canonical adjacent-suffix depth odd by spending at most one
additional guard bit. -/
def oddGuardedCanonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  let m := canonicalAdjacentSuffixDepth t
  if Even m then m + 1 else m

theorem oddGuardedCanonicalAdjacentSuffixDepth_of_even
    {t : ℕ} (h : Even (canonicalAdjacentSuffixDepth t)) :
    oddGuardedCanonicalAdjacentSuffixDepth t =
      canonicalAdjacentSuffixDepth t + 1 := by
  simp [oddGuardedCanonicalAdjacentSuffixDepth, h]

theorem oddGuardedCanonicalAdjacentSuffixDepth_of_odd
    {t : ℕ} (h : Odd (canonicalAdjacentSuffixDepth t)) :
    oddGuardedCanonicalAdjacentSuffixDepth t =
      canonicalAdjacentSuffixDepth t := by
  have hne : ¬ Even (canonicalAdjacentSuffixDepth t) :=
    Nat.not_even_iff_odd.mpr h
  simp [oddGuardedCanonicalAdjacentSuffixDepth, hne]

theorem oddGuardedCanonicalAdjacentSuffixDepth_cases (t : ℕ) :
    oddGuardedCanonicalAdjacentSuffixDepth t =
        canonicalAdjacentSuffixDepth t ∨
      oddGuardedCanonicalAdjacentSuffixDepth t =
        canonicalAdjacentSuffixDepth t + 1 := by
  simp only [oddGuardedCanonicalAdjacentSuffixDepth]
  by_cases h : Even (canonicalAdjacentSuffixDepth t)
  · simp [h]
  · simp [h]

theorem canonicalAdjacentSuffixDepth_le_oddGuarded (t : ℕ) :
    canonicalAdjacentSuffixDepth t ≤
      oddGuardedCanonicalAdjacentSuffixDepth t := by
  rcases oddGuardedCanonicalAdjacentSuffixDepth_cases t with h | h <;>
    omega

theorem oddGuardedCanonicalAdjacentSuffixDepth_le_succ (t : ℕ) :
    oddGuardedCanonicalAdjacentSuffixDepth t ≤
      canonicalAdjacentSuffixDepth t + 1 := by
  rcases oddGuardedCanonicalAdjacentSuffixDepth_cases t with h | h <;>
    omega

/-! ## Recursive LCM universal property -/

/-- If every positive integer at most `t` divides `M`, then the recursive
universal period `periodLcm t` divides `M`. -/
theorem periodLcm_dvd_of_forall_pos_le
    {t M : ℕ} (h : ∀ k : ℕ, 1 ≤ k → k ≤ t → k ∣ M) :
    periodLcm t ∣ M := by
  induction t with
  | zero => simp [periodLcm]
  | succ t ih =>
      rw [periodLcm]
      apply Nat.lcm_dvd
      · exact ih fun k hk hkt => h k hk (by omega)
      · exact h (t + 1) (by omega) le_rfl

/-! ## The one Kummer carry needed by the doubling inequality -/

/-- If a positive prime power lies in `(n, 2n]`, then adding `n+n` carries
across that prime-power digit.  Kummer's factorization formula therefore puts
at least one copy of the prime into the central binomial coefficient. -/
theorem one_le_factorization_centralBinom_of_prime_pow_window
    {n p e : ℕ} (hp : Nat.Prime p) (he : 0 < e)
    (hnp : n < p ^ e) (hp2n : p ^ e ≤ 2 * n) :
    1 ≤ (Nat.centralBinom n).factorization p := by
  rw [Nat.centralBinom_eq_two_mul_choose,
    Nat.factorization_choose hp (by omega) (Nat.lt_succ_self _)]
  rw [Finset.one_le_card]
  refine ⟨e, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_Ico.mpr
      ⟨he, by
        have heLog : e ≤ Nat.log p (2 * n) :=
          Nat.le_log_of_pow_le hp.one_lt hp2n
        omega⟩
  · rw [show 2 * n - n = n by omega,
      Nat.mod_eq_of_lt hnp]
    omega

/-- Divisibility form of the single-carry lemma. -/
theorem prime_dvd_centralBinom_of_prime_pow_window
    {n p e : ℕ} (hp : Nat.Prime p) (he : 0 < e)
    (hnp : n < p ^ e) (hp2n : p ^ e ≤ 2 * n) :
    p ∣ Nat.centralBinom n := by
  exact (hp.dvd_iff_one_le_factorization (Nat.centralBinom_ne_zero n)).2
    (one_le_factorization_centralBinom_of_prime_pow_window hp he hnp hp2n)

/-! ## The classical LCM doubling divisibility -/

/-- Every positive index through `2n` divides the old LCM times the central
binomial coefficient.  Old divisors are immediate; a new index below `2n` is
a prime power, whose predecessor power lies below `n` while its last prime is
supplied by the Kummer carry.  The endpoint `2n` is supplied by
`n ∣ periodLcm n` and the evenness of the positive central binomial. -/
theorem periodLcm_two_mul_dvd_periodLcm_mul_centralBinom
    (n : ℕ) (hn : 0 < n) :
    periodLcm (2 * n) ∣ periodLcm n * Nat.centralBinom n := by
  apply periodLcm_dvd_of_forall_pos_le
  intro k hkPos hkLe
  by_cases hkOld : k ∣ periodLcm n
  · exact hkOld.mul_right (Nat.centralBinom n)
  by_cases hkTop : k = 2 * n
  · subst k
    have hnOld : n ∣ periodLcm n := dvd_periodLcm hn le_rfl
    have htwo : 2 ∣ Nat.centralBinom n :=
      Nat.two_dvd_centralBinom_of_one_le hn
    simpa [Nat.mul_comm] using Nat.mul_dvd_mul hnOld htwo
  · have hkLt : k < 2 * n := lt_of_le_of_ne hkLe hkTop
    obtain ⟨p, e, hp, hpk, hnk⟩ :=
      eq_prime_pow_of_not_dvd_periodLcm hkPos hkLt hkOld
    subst k
    have he : 0 < e := by
      by_contra he
      have heZero : e = 0 := Nat.eq_zero_of_not_pos he
      subst e
      simp at hnk
      omega
    have hpredLt : p ^ (e - 1) < n := by
      have hpow : p ^ e = p ^ (e - 1) * p := by
        rw [← pow_succ, Nat.sub_add_cancel he]
      have htwoPred : 2 * p ^ (e - 1) ≤ p ^ e := by
        rw [hpow]
        simpa [Nat.mul_comm] using
          Nat.mul_le_mul_left (p ^ (e - 1)) hp.two_le
      have hstrict : 2 * p ^ (e - 1) < 2 * n :=
        htwoPred.trans_lt hkLt
      omega
    have hpredOld : p ^ (e - 1) ∣ periodLcm n :=
      dvd_periodLcm (pow_pos hp.pos _) hpredLt.le
    have hpCentral : p ∣ Nat.centralBinom n :=
      prime_dvd_centralBinom_of_prime_pow_window hp he hnk hkLt.le
    have hmul := Nat.mul_dvd_mul hpredOld hpCentral
    simpa [← pow_succ, Nat.sub_add_cancel he] using hmul

/-- Numerical inequality furnished directly by the doubling divisibility. -/
theorem periodLcm_two_mul_le_periodLcm_mul_centralBinom
    (n : ℕ) (hn : 0 < n) :
    periodLcm (2 * n) ≤ periodLcm n * Nat.centralBinom n := by
  exact Nat.le_of_dvd
    (Nat.mul_pos (periodLcm_pos n) (Nat.centralBinom_pos n))
    (periodLcm_two_mul_dvd_periodLcm_mul_centralBinom n hn)

/-- The elementary central-binomial estimate turns the exact divisibility
into the doubling bound `L(2n) ≤ L(n) * 4^n`. -/
theorem periodLcm_two_mul_le_periodLcm_mul_four_pow
    (n : ℕ) (hn : 0 < n) :
    periodLcm (2 * n) ≤ periodLcm n * 4 ^ n := by
  calc
    periodLcm (2 * n) ≤ periodLcm n * Nat.centralBinom n :=
      periodLcm_two_mul_le_periodLcm_mul_centralBinom n hn
    _ ≤ periodLcm n * 4 ^ n :=
      Nat.mul_le_mul_left _ (Nat.centralBinom_le_four_pow n)

/-! ## Twelve-bit saving on the power-two ray -/

/-- Exact base of the doubling induction. -/
theorem periodLcm_sixteen_lt_two_pow_twenty :
    periodLcm 16 < 2 ^ 20 := by
  norm_num [periodLcm]

/-- Starting at `16`, the central-binomial doubling estimate preserves a
twelve-bit saving against the crude `4^t` exponent.  The constant `12` is
the largest integer saving supported by the exact base `periodLcm 16`. -/
theorem periodLcm_pow_two_lt_two_pow_guardTwelve
    {a : ℕ} (ha : 4 ≤ a) :
    periodLcm (2 ^ a) < 2 ^ (2 * 2 ^ a - 12) := by
  induction a, ha using Nat.le_induction with
  | base =>
      simpa using periodLcm_sixteen_lt_two_pow_twenty
  | succ a ha ih =>
      let t := 2 ^ a
      have htPos : 0 < t := pow_pos (by norm_num) _
      have htSixteen : 16 ≤ t := by
        change 2 ^ 4 ≤ 2 ^ a
        exact Nat.pow_le_pow_right (by norm_num : 0 < 2) ha
      have hdouble := periodLcm_two_mul_le_periodLcm_mul_four_pow t htPos
      calc
        periodLcm (2 ^ (a + 1)) = periodLcm (2 * t) := by
          congr 1
          simp [t, pow_succ, Nat.mul_comm]
        _ ≤ periodLcm t * 4 ^ t := hdouble
        _ < 2 ^ (2 * t - 12) * 4 ^ t :=
          Nat.mul_lt_mul_of_pos_right ih (pow_pos (by norm_num) _)
        _ = 2 ^ (2 * 2 ^ (a + 1) - 12) := by
          rw [show 4 ^ t = 2 ^ (2 * t) by
            rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
          congr 1
          rw [pow_succ]
          omega

/-! ## Canonical and odd-guarded depth consequences -/

/-- The twelve-bit LCM saving leaves one full bit beyond the optional parity
guard: `canonicalDepth + 1` is still strictly shorter than `2t`. -/
theorem canonicalAdjacentSuffixDepth_powerTwo_succ_lt_two_mul
    {a : ℕ} (ha : 4 ≤ a) :
    canonicalAdjacentSuffixDepth (2 ^ a) + 1 < 2 * 2 ^ a := by
  have hHeight := periodLcm_pow_two_lt_two_pow_guardTwelve ha
  have hLog :
      Nat.log2 (periodLcm (2 ^ a)) < 2 * 2 ^ a - 12 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (periodLcm_pos (2 ^ a)).ne' hHeight
  have hscale : 16 ≤ 2 ^ a := by
    change 2 ^ 4 ≤ 2 ^ a
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) ha
  unfold canonicalAdjacentSuffixDepth
  omega

/-- Both adjacent suffix depths remain inside the short actual-LCM window. -/
theorem oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_succ_lt_two_mul
    {a : ℕ} (ha : 4 ≤ a) :
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) + 1 < 2 * 2 ^ a := by
  have hHeight := periodLcm_pow_two_lt_two_pow_guardTwelve ha
  have hLog :
      Nat.log2 (periodLcm (2 ^ a)) < 2 * 2 ^ a - 12 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (periodLcm_pos (2 ^ a)).ne' hHeight
  have hscale : 16 ≤ 2 ^ a := by
    change 2 ^ 4 ≤ 2 ^ a
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) ha
  have hguard := oddGuardedCanonicalAdjacentSuffixDepth_le_succ (2 ^ a)
  unfold canonicalAdjacentSuffixDepth at hguard
  omega

/-- Requested arithmetic guard for the canonical depth. -/
theorem canonicalAdjacentSuffixDepth_powerTwo_lt_two_mul
    {a : ℕ} (ha : 4 ≤ a) :
    canonicalAdjacentSuffixDepth (2 ^ a) < 2 * 2 ^ a := by
  have h := canonicalAdjacentSuffixDepth_powerTwo_succ_lt_two_mul ha
  omega

/-- Strong consumer form for the previous sparse-pulse lane: the actual
odd-guarded canonical depth also lies below `2t`, so repeated same-endpoint
foreign support is confined to the prime exceptional set. -/
theorem oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_lt_two_mul
    {a : ℕ} (ha : 4 ≤ a) :
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) < 2 * 2 ^ a := by
  exact (oddGuardedCanonicalAdjacentSuffixDepth_le_succ (2 ^ a)).trans_lt
    (canonicalAdjacentSuffixDepth_powerTwo_succ_lt_two_mul ha)

/-! ## Direct sparse-pulse consumers -/

/-- At every power-two scale `a ≥ 4`, a squarefree foreign channel that hits
the lower endpoint twice inside the odd-guarded canonical window is prime. -/
theorem prime_of_squarefree_repeated_low_support_powerTwo_oddGuarded
    {a d s r : ℕ} (ha : 4 ≤ a) (hsq : Squarefree d)
    (hsPos : 1 ≤ s) (hsr : s < r)
    (hr : r ≤ oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) + 1)
    (hnd : ¬d ∣ periodLcm (2 ^ a))
    (hsLow : d ∣ periodLcm (2 ^ a) + s)
    (hrLow : d ∣ periodLcm (2 ^ a) + r) :
    Nat.Prime d := by
  exact
    prime_of_squarefree_repeated_low_support_in_short_periodLcm_window
      (t := 2 ^ a) (m := oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a))
      hsq hsPos hsr hr
      (oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_lt_two_mul ha)
      hnd hsLow hrLow

/-- The analogous repeated top-endpoint channel is also prime. -/
theorem prime_of_squarefree_repeated_top_support_powerTwo_oddGuarded
    {a d s r : ℕ} (ha : 4 ≤ a) (hsq : Squarefree d)
    (hsPos : 1 ≤ s) (hsr : s < r)
    (hr : r ≤ oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) + 1)
    (hnd : ¬d ∣ periodLcm (2 ^ a))
    (hsTop : d ∣ 2 * periodLcm (2 ^ a) + s)
    (hrTop : d ∣ 2 * periodLcm (2 ^ a) + r) :
    Nat.Prime d := by
  exact
    prime_of_squarefree_repeated_top_support_in_short_periodLcm_window
      (t := 2 ^ a) (m := oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a))
      hsq hsPos hsr hr
      (oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_lt_two_mul ha)
      hnd hsTop hrTop

theorem odd_oddGuardedCanonicalAdjacentSuffixDepth (t : ℕ) :
    Odd (oddGuardedCanonicalAdjacentSuffixDepth t) := by
  simp only [oddGuardedCanonicalAdjacentSuffixDepth]
  by_cases heven : Even (canonicalAdjacentSuffixDepth t)
  · simp only [if_pos heven]
    obtain ⟨q, hq⟩ := heven
    refine ⟨q, ?_⟩
    omega
  · simp only [if_neg heven]
    exact Nat.not_even_iff_odd.mp heven

theorem exists_oddGuardedCanonicalAdjacentSuffixDepth_index (t : ℕ) :
    ∃ q : ℕ, oddGuardedCanonicalAdjacentSuffixDepth t = 2 * q + 1 := by
  obtain ⟨q, hq⟩ := odd_oddGuardedCanonicalAdjacentSuffixDepth t
  exact ⟨q, by omega⟩

theorem canonicalAdjacentSuffixDepth_ten_le (t : ℕ) :
    10 ≤ canonicalAdjacentSuffixDepth t := by
  simp [canonicalAdjacentSuffixDepth]

/-- The analytic adjacent-gap width inequality survives spending the optional
extra guard bit. -/
theorem canonicalAdjacentSuffixDepth_succ_width {t : ℕ} (ht : 3 ≤ t) :
    5 ≤ canonicalAdjacentSuffixDepth t + 1 ∧
      32 * (3 * periodLcm t +
        2 * ((canonicalAdjacentSuffixDepth t + 1) + 3) : ℤ) <
        2 ^ (canonicalAdjacentSuffixDepth t + 1) := by
  let m := canonicalAdjacentSuffixDepth t
  let A : ℤ := 32 * (3 * periodLcm t + 2 * (m + 3) : ℤ)
  obtain ⟨hm, hwidth⟩ := canonicalAdjacentSuffixDepth_width ht
  have hwidthA : A < (2 : ℤ) ^ m := by
    simpa [A, m] using hwidth
  have hH : 0 < periodLcm t := periodLcm_pos t
  have hA : (64 : ℤ) < A := by
    dsimp [A]
    omega
  have hnextA :
      (32 * (3 * periodLcm t + 2 * ((m + 1) + 3) : ℤ)) = A + 64 := by
    dsimp [A]
    ring
  have hnextPow : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by
    rw [pow_succ]
    ring
  change 5 ≤ m + 1 ∧
    32 * (3 * periodLcm t + 2 * ((m + 1) + 3) : ℤ) <
      (2 : ℤ) ^ (m + 1)
  constructor
  · omega
  · rw [hnextA, hnextPow]
    omega

/-- The symmetric width receipt likewise survives the optional parity guard
bit. -/
theorem canonicalAdjacentSuffixDepth_succ_symmetric_width
    {t : ℕ} (ht : 3 ≤ t) :
    5 ≤ canonicalAdjacentSuffixDepth t + 1 ∧
      32 * (4 * periodLcm t +
        2 * (canonicalAdjacentSuffixDepth t + 1) + 5 : ℤ) <
        2 ^ (canonicalAdjacentSuffixDepth t + 1) := by
  let m := canonicalAdjacentSuffixDepth t
  let A : ℤ := 32 * (4 * periodLcm t + 2 * m + 5 : ℤ)
  obtain ⟨hm, hwidth⟩ := canonicalAdjacentSuffixDepth_symmetric_width ht
  have hwidthA : A < (2 : ℤ) ^ m := by
    simpa [A, m] using hwidth
  have hH : 0 < periodLcm t := periodLcm_pos t
  have hA : (64 : ℤ) < A := by
    dsimp [A]
    omega
  have hnextA :
      (32 * (4 * periodLcm t + 2 * (m + 1) + 5 : ℤ)) = A + 64 := by
    dsimp [A]
    ring
  have hnextPow : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by
    rw [pow_succ]
    ring
  change 5 ≤ m + 1 ∧
    32 * (4 * periodLcm t + 2 * (m + 1) + 5 : ℤ) <
      (2 : ℤ) ^ (m + 1)
  constructor
  · omega
  · rw [hnextA, hnextPow]
    omega

/-- Whichever parity the canonical depth has, the odd-guarded depth retains
the automatic adjacent-gap consumer width. -/
theorem oddGuardedCanonicalAdjacentSuffixDepth_width {t : ℕ} (ht : 3 ≤ t) :
    5 ≤ oddGuardedCanonicalAdjacentSuffixDepth t ∧
      32 * (3 * periodLcm t +
        2 * (oddGuardedCanonicalAdjacentSuffixDepth t + 3) : ℤ) <
        2 ^ oddGuardedCanonicalAdjacentSuffixDepth t := by
  simp only [oddGuardedCanonicalAdjacentSuffixDepth]
  by_cases h : Even (canonicalAdjacentSuffixDepth t)
  · simp only [if_pos h]
    exact canonicalAdjacentSuffixDepth_succ_width ht
  · simp only [if_neg h]
    exact canonicalAdjacentSuffixDepth_width ht

/-- Odd-guarded canonical depth with the symmetric actual-LCM margin still
projected locally. -/
theorem oddGuardedCanonicalAdjacentSuffixDepth_symmetric_width
    {t : ℕ} (ht : 3 ≤ t) :
    5 ≤ oddGuardedCanonicalAdjacentSuffixDepth t ∧
      32 * (4 * periodLcm t +
        2 * oddGuardedCanonicalAdjacentSuffixDepth t + 5 : ℤ) <
        2 ^ oddGuardedCanonicalAdjacentSuffixDepth t := by
  simp only [oddGuardedCanonicalAdjacentSuffixDepth]
  by_cases h : Even (canonicalAdjacentSuffixDepth t)
  · simp only [if_pos h]
    exact canonicalAdjacentSuffixDepth_succ_symmetric_width ht
  · simp only [if_neg h]
    exact canonicalAdjacentSuffixDepth_symmetric_width ht

/-- A pointwise half-word band certificate at the odd-guarded depth feeds the
existing adjacent-gap consumer at a power-of-two endpoint. -/
theorem diagonalFreshLossResidueCert_or_of_powerTwo_oddGuard_halfWordBand
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth : oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1)
    (hlo : (4 : ℤ) ^ q ≤
      32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q))
    (hhi : 32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ≤
      31 * (4 : ℤ) ^ q) :
    diagonalFreshLossResidueCert (2 ^ a) (2 * q + 1) ∨
      diagonalFreshLossResidueCert (2 ^ a) (1 + (2 * q + 1)) := by
  have ht : 3 ≤ 2 ^ a := by
    have hpow4 : 4 ≤ 2 ^ a := by
      simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) ha)
    omega
  obtain ⟨hm, hwidth⟩ :=
    oddGuardedCanonicalAdjacentSuffixDepth_width ht
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hle := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hle
    omega
  have hcentral :=
    (diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand
      ha hq).2 ⟨hlo, hhi⟩
  rw [hdepth] at hm hwidth
  simpa using
    (diagonalFreshLossResidueCert_or_of_adjacent_dyadic_gap
      (t := 2 ^ a) (J := 0) (m := 2 * q + 1)
      hm (by simpa using hwidth) hcentral.1 hcentral.2)

/-- The same half-word band retains enough canonical margin to produce the
stronger symmetric certificate consumed by the actual-LCM arithmetic word. -/
theorem diagonalSymmetricResidueCert_or_of_powerTwo_oddGuard_halfWordBand
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth : oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1)
    (hlo : (4 : ℤ) ^ q ≤
      32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q))
    (hhi : 32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ≤
      31 * (4 : ℤ) ^ q) :
    diagonalSymmetricResidueCert (2 ^ a) (2 * q + 1) ∨
      diagonalSymmetricResidueCert (2 ^ a) (1 + (2 * q + 1)) := by
  have ht : 3 ≤ 2 ^ a := by
    have hpow4 : 4 ≤ 2 ^ a := by
      simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) ha)
    omega
  obtain ⟨hm, hwidth⟩ :=
    oddGuardedCanonicalAdjacentSuffixDepth_symmetric_width ht
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hle := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hle
    omega
  have hcentral :=
    (diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand
      ha hq).2 ⟨hlo, hhi⟩
  rw [hdepth] at hm hwidth
  simpa using
    (diagonalSymmetricResidueCert_or_of_adjacent_dyadic_gap
      (t := 2 ^ a) (J := 0) (m := 2 * q + 1)
      hm (by simpa using hwidth) hcentral.1 hcentral.2)

/-- Cofinal producer phrased only in terms of the integral odd-depth
base-four half-word. -/
def PowerTwoOddGuardHalfWordBandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 2 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    (4 : ℤ) ^ q ≤
      32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ∧
    32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ≤
      31 * (4 : ℤ) ^ q

/-- The half-word producer supplies the exact adjacent-gap interface. -/
theorem diagonalAdjacentSuffixGapSupply_of_powerTwoOddGuardHalfWordBand
    (hsupply : PowerTwoOddGuardHalfWordBandSupply) :
    DiagonalAdjacentSuffixGapSupply := by
  intro t₀
  obtain ⟨a, q, ha, hdepth, hlo, hhi⟩ := hsupply t₀
  have ha2 : 2 ≤ a := (le_max_left 2 t₀).trans ha
  have ht₀a : t₀ ≤ a := (le_max_right 2 t₀).trans ha
  have hat : a < 2 ^ a := Nat.lt_two_pow_self
  have ht : 3 ≤ 2 ^ a := by
    have hpow4 : 4 ≤ 2 ^ a := by
      simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) ha2)
    omega
  obtain ⟨hm, hwidth⟩ :=
    oddGuardedCanonicalAdjacentSuffixDepth_width ht
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hle := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hle
    omega
  have hcentral :=
    (diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand
      ha2 hq).2 ⟨hlo, hhi⟩
  refine ⟨2 ^ a, by omega,
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a), hm, hwidth, ?_, ?_⟩
  · rw [hdepth]
    exact hcentral.1
  · rw [hdepth]
    exact hcentral.2

/-- Therefore the odd-guard half-word band is a complete arithmetic producer
interface for the landed Erdős #249 irrationality consumer. -/
theorem irrational_totientSeries_of_powerTwoOddGuardHalfWordBandSupply
    (hsupply : PowerTwoOddGuardHalfWordBandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply
    (diagonalAdjacentSuffixGapSupply_of_powerTwoOddGuardHalfWordBand hsupply)

/-- For a positive base `Q`, the upper/lower half of `W mod 2Q` is exactly
the parity of the Euclidean quotient `W / Q`. -/
theorem int_emod_two_mul_ge_iff_odd_ediv
    {W Q : ℤ} (hQ : 0 < Q) :
    Q ≤ W % (2 * Q) ↔ Odd (W / Q) := by
  let r : ℤ := W % Q
  have hr0 : 0 ≤ r := by
    exact Int.emod_nonneg W hQ.ne'
  have hrQ : r < Q := by
    exact Int.emod_lt_of_pos W hQ
  have hdecomp : Q * (W / Q) + r = W := by
    exact Int.mul_ediv_add_emod W Q
  constructor
  · intro htop
    rcases Int.even_or_odd (W / Q) with heven | hodd
    · rcases heven with ⟨k, hk⟩
      have hW : W = r + (2 * Q) * k := by
        calc
          W = Q * (W / Q) + r := hdecomp.symm
          _ = r + (2 * Q) * k := by rw [hk]; ring
      have hmod : W % (2 * Q) = r := by
        rw [hW, Int.add_mul_emod_self_left,
          Int.emod_eq_of_lt hr0 (by omega)]
      rw [hmod] at htop
      omega
    · exact hodd
  · intro hodd
    rcases hodd with ⟨k, hk⟩
    have hW : W = (Q + r) + (2 * Q) * k := by
      calc
        W = Q * (W / Q) + r := hdecomp.symm
        _ = (Q + r) + (2 * Q) * k := by rw [hk]; ring
    have hmod : W % (2 * Q) = Q + r := by
      rw [hW, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hmod]
    exact le_add_of_nonneg_right hr0

/-- The exact top bit of the odd-depth power-of-two residue is the quotient
parity of its correction word. -/
theorem diagonalAdjacentSuffixResidue_powerTwo_oddDepth_topBit_iff
    {a q : ℕ} (ha : 2 ≤ a) :
    (4 : ℤ) ^ q ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) ↔
      Odd (powerTwoOddCorrectionWord a q / (4 : ℤ) ^ q) := by
  rw [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_correctionWord ha]
  have hpow : (2 : ℤ) ^ (2 * q + 1) = 2 * (4 : ℤ) ^ q := by
    calc
      (2 : ℤ) ^ (2 * q + 1) = 2 ^ (2 * q) * 2 ^ 1 := by rw [pow_add]
      _ = (2 ^ 2 : ℤ) ^ q * 2 := by rw [pow_mul]; norm_num
      _ = 2 * (4 : ℤ) ^ q := by norm_num; ring
  rw [hpow]
  exact int_emod_two_mul_ge_iff_odd_ediv (by positivity)

/-- After normalization by the growing base-four modulus, one odd-depth
correction step is literal addition of the next base-four digit. -/
theorem powerTwoOddHalfCorrectionWord_normalized_step (a q : ℕ) :
    ((powerTwoOddHalfCorrectionWord a (q + 1) : ℤ) : ℚ) /
          (4 : ℚ) ^ (q + 1) -
        ((powerTwoOddHalfCorrectionWord a q : ℤ) : ℚ) / (4 : ℚ) ^ q =
      ((powerTwoOddDepthCorrection a q / 2 : ℤ) : ℚ) /
        (4 : ℚ) ^ (q + 1) := by
  rw [powerTwoOddHalfCorrectionWord_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- Finite telescoping form of the normalized integral half-word. -/
theorem powerTwoOddHalfCorrectionWord_normalized_eq_sum (a q : ℕ) :
    ((powerTwoOddHalfCorrectionWord a q : ℤ) : ℚ) / (4 : ℚ) ^ q =
      ∑ n ∈ Finset.range q,
        ((powerTwoOddDepthCorrection a n / 2 : ℤ) : ℚ) /
          (4 : ℚ) ^ (n + 1) := by
  induction q with
  | zero => simp [powerTwoOddHalfCorrectionWord]
  | succ q ih =>
      rw [Finset.sum_range_succ, ← ih]
      linarith [powerTwoOddHalfCorrectionWord_normalized_step a q]

/-- The half-word is exactly the non-seed part of the normalized raw odd
window.  Its circle-valued orbit is therefore a sequence of finite diagonal
tail approximants, up to one fixed integral seed. -/
theorem powerTwoOddHalfCorrectionWord_eq_raw_sub_seed
    {a q : ℕ} (ha : 2 ≤ a) :
    2 * powerTwoOddHalfCorrectionWord a q =
      diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) -
        (4 : ℤ) ^ q *
          diagonalAdjacentSuffixRawBlock (2 ^ a) 0 1 := by
  rw [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_closed ha,
    powerTwoOddCorrectionWord_eq_two_mul_halfWord]
  ring

/-- A positive circle crossing is exactly one increment of the Euclidean
quotient. -/
theorem baseFour_positiveWrap_ediv_succ
    {Z M c : ℤ} (hM : 0 < M)
    (hlo : 4 * M ≤ 4 * (Z % M) + c)
    (hhi : 4 * (Z % M) + c < 8 * M) :
    (4 * Z + c) / (4 * M) = Z / M + 1 := by
  let y : ℤ := 4 * (Z % M) + c - 4 * M
  have hy0 : 0 ≤ y := by simp only [y]; omega
  have hyM : y < 4 * M := by simp only [y]; omega
  have hM0 : 4 * M ≠ 0 := by omega
  have hdecomp : M * (Z / M) + Z % M = Z :=
    Int.mul_ediv_add_emod Z M
  have hx : 4 * Z + c = y + (4 * M) * (Z / M + 1) := by
    simp only [y]
    linarith
  rw [hx, Int.add_mul_ediv_left y (Z / M + 1) hM0,
    Int.ediv_eq_zero_of_lt hy0 hyM, zero_add]

/-- A complete two-sided form of the edge obstruction.  Represent an old
edge residue by its short signed lift `u`; the next residue remains in an edge
cylinder exactly when the unwrapped affine lift remains in the four-times
wider signed tube. -/
theorem baseFour_edge_iff_centered_tube
    {M e u c : ℤ}
    (hM : 0 < M) (he : 0 < e) (hwidth : 4 * e < M)
    (hu : |u| < e) (hc : |c| < 8 * e) :
    let r := u % M
    let s := (4 * r + c) % (4 * M)
    (s < 4 * e ∨ 4 * M - 4 * e < s) ↔ |4 * u + c| < 4 * e := by
  dsimp only
  rw [abs_lt] at hu hc
  let y : ℤ := 4 * u + c
  have hylo : -3 * M < y := by
    dsimp [y]
    omega
  have hyhi : y < 3 * M := by
    dsimp [y]
    omega
  have hdecomp : M * (u / M) + u % M = u :=
    Int.mul_ediv_add_emod u M
  have hresidue : u % M = u - M * (u / M) := by omega
  have hmod : (4 * (u % M) + c) % (4 * M) = y % (4 * M) := by
    rw [hresidue]
    have hrewrite :
        4 * (u - M * (u / M)) + c =
          y + (4 * M) * (-(u / M)) := by
      dsimp [y]
      ring
    rw [hrewrite, Int.add_mul_emod_self_left]
  rw [hmod]
  by_cases hy0 : 0 ≤ y
  · have hyP : y < 4 * M := by omega
    rw [Int.emod_eq_of_lt hy0 hyP, abs_of_nonneg hy0]
    dsimp [y] at *
    omega
  · have hyneg : y < 0 := by omega
    have hyadd0 : 0 ≤ y + 4 * M := by omega
    have hyaddP : y + 4 * M < 4 * M := by omega
    have hymod : y % (4 * M) = y + 4 * M := by
      calc
        y % (4 * M) = ((y + 4 * M) - 4 * M) % (4 * M) := by
          congr 1
          ring
        _ = (y + 4 * M) % (4 * M) :=
          Int.sub_emod_right (y + 4 * M) (4 * M)
        _ = y + 4 * M := Int.emod_eq_of_lt hyadd0 hyaddP
    rw [hymod, abs_of_nonpos hyneg.le]
    dsimp [y] at *
    omega

/-- Exact no-go for any correction-envelope-only strategy: zero correction
keeps a signed edge state in the scaled tube at every base-four rank. -/
theorem baseFour_zeroCorrection_centered_tube_forever
    {u e : ℤ} (hu : |u| < e) (k : ℕ) :
    |(4 : ℤ) ^ k * u| < (4 : ℤ) ^ k * e := by
  have hpow : 0 < (4 : ℤ) ^ k := pow_pos (by norm_num) k
  rw [abs_mul, abs_of_nonneg hpow.le]
  exact mul_lt_mul_of_pos_left hu hpow

private theorem nearMultiple_witness_unique
    {X M e k l : ℤ} (hM : 0 < M) (hwidth : 2 * e < M)
    (hk : |X - M * k| < e) (hl : |X - M * l| < e) :
    k = l := by
  rw [abs_lt] at hk hl
  have hdifflo : -M < M * (k - l) := by nlinarith
  have hdiffhi : M * (k - l) < M := by nlinarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · have hstep : k - l ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt hM)
    nlinarith
  · have hstep : 1 ≤ k - l := by omega
    have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt hM)
    nlinarith

/-- Two future edge-cylinder tests pull back to two literal inequalities in
one old base-four cell. -/
theorem twoFutureEdgeRanks_iff_oldStateCrossing
    {A B D C F M e : ℤ}
    (he : 0 < e) (hscale : M = 32 * e)
    (hBstep : B = 4 * A + C)
    (hDstep : D = 4 * B + F)
    (hF : |F| < 15 * M) :
    (NearMultiple B (4 * M) (4 * e) ∧
        NearMultiple D (16 * M) (16 * e)) ↔
      ∃ k : ℤ,
        |4 * (A - M * k) + C| < 4 * e ∧
        |16 * (A - M * k) + 4 * C + F| < 16 * e := by
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    have hk' : |B - 4 * M * k| < 4 * e := by
      simpa [mul_assoc] using hk
    have hl' : |D - 16 * M * l| < 16 * e := by
      simpa [mul_assoc] using hl
    have hdiff :
        16 * M * (k - l) =
          (D - 16 * M * l) - 4 * (B - 4 * M * k) - F := by
      rw [hDstep]
      ring
    have hMpos : 0 < M := by rw [hscale]; positivity
    have hkBounds := (abs_lt.mp hk')
    have hlBounds := (abs_lt.mp hl')
    have hFBounds := (abs_lt.mp hF)
    have hdifflo : -(16 * M) < 16 * M * (k - l) := by
      rw [hdiff, hscale]
      nlinarith
    have hdiffhi : 16 * M * (k - l) < 16 * M := by
      rw [hdiff, hscale]
      nlinarith
    have hkl : k = l := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hkl | hlk
      · have hstep : k - l ≤ -1 := by omega
        have hmul := mul_le_mul_of_nonneg_left hstep
          (show 0 ≤ 16 * M by positivity)
        nlinarith
      · have hstep : 1 ≤ k - l := by omega
        have hmul := mul_le_mul_of_nonneg_left hstep
          (show 0 ≤ 16 * M by positivity)
        nlinarith
    subst l
    refine ⟨k, ?_, ?_⟩
    · have heq : 4 * (A - M * k) + C = B - 4 * M * k := by
        rw [hBstep]
        ring
      rw [heq]
      exact hk'
    · have heq :
          16 * (A - M * k) + 4 * C + F = D - 16 * M * k := by
        rw [hDstep, hBstep]
        ring
      rw [heq]
      exact hl'
  · rintro ⟨k, hk, hl⟩
    constructor
    · refine ⟨k, ?_⟩
      have heq : B - 4 * M * k = 4 * (A - M * k) + C := by
        rw [hBstep]
        ring
      change |B - 4 * M * k| < 4 * e
      rw [heq]
      exact hk
    · refine ⟨k, ?_⟩
      have heq :
          D - 16 * M * k = 16 * (A - M * k) + 4 * C + F := by
        rw [hDstep, hBstep]
        ring
      change |D - 16 * M * k| < 16 * e
      rw [heq]
      exact hl

/-- Three future edge ranks are the same old-state lift with one more exact
literal inequality. -/
theorem threeFutureEdgeRanks_iff_oldStateCrossing
    {A B D E C F G M e : ℤ}
    (he : 0 < e) (hscale : M = 32 * e)
    (hBstep : B = 4 * A + C)
    (hDstep : D = 4 * B + F)
    (hEstep : E = 4 * D + G)
    (hF : |F| < 15 * M)
    (hG : |G| < 60 * M) :
    (NearMultiple B (4 * M) (4 * e) ∧
        NearMultiple D (16 * M) (16 * e) ∧
        NearMultiple E (64 * M) (64 * e)) ↔
      ∃ k : ℤ,
        |4 * (A - M * k) + C| < 4 * e ∧
        |16 * (A - M * k) + 4 * C + F| < 16 * e ∧
        |64 * (A - M * k) + 16 * C + 4 * F + G| < 64 * e := by
  have hscale' : 4 * M = 32 * (4 * e) := by rw [hscale]; ring
  have hG' : |G| < 15 * (4 * M) := by
    convert hG using 1 <;> ring
  constructor
  · rintro ⟨hB, hD, hE⟩
    obtain ⟨k, hk, hDk⟩ :=
      (twoFutureEdgeRanks_iff_oldStateCrossing he hscale
        hBstep hDstep hF).1 ⟨hB, hD⟩
    have hD' : NearMultiple D (4 * (4 * M)) (4 * (4 * e)) := by
      convert hD using 1 <;> ring
    have hE' : NearMultiple E (16 * (4 * M)) (16 * (4 * e)) := by
      convert hE using 1 <;> ring
    obtain ⟨l, hDl, hEl⟩ :=
      (twoFutureEdgeRanks_iff_oldStateCrossing
        (show 0 < 4 * e by positivity) hscale'
        hDstep hEstep hG').1 ⟨hD', hE'⟩
    have hDk' : |D - 16 * M * k| < 16 * e := by
      have heq :
          D - 16 * M * k = 16 * (A - M * k) + 4 * C + F := by
        rw [hDstep, hBstep]
        ring
      rw [heq]
      exact hDk
    have hDl' : |D - 16 * M * l| < 16 * e := by
      have heq : D - 16 * M * l = 4 * (B - 4 * M * l) + F := by
        rw [hDstep]
        ring
      rw [heq]
      convert hDl using 1 <;> ring
    have hMpos : 0 < M := by rw [hscale]; positivity
    have hwidth : 2 * (16 * e) < 16 * M := by rw [hscale]; nlinarith
    have hkl : k = l :=
      nearMultiple_witness_unique (show 0 < 16 * M by positivity)
        hwidth hDk' hDl'
    subst l
    refine ⟨k, hk, hDk, ?_⟩
    have heq :
        16 * (B - 4 * M * k) + 4 * F + G =
          64 * (A - M * k) + 16 * C + 4 * F + G := by
      rw [hBstep]
      ring
    rw [← heq]
    convert hEl using 1 <;> ring
  · rintro ⟨k, hk, hDk, hEk⟩
    have hBD :
        NearMultiple B (4 * M) (4 * e) ∧
          NearMultiple D (16 * M) (16 * e) :=
      (twoFutureEdgeRanks_iff_oldStateCrossing he hscale
        hBstep hDstep hF).2 ⟨k, hk, hDk⟩
    refine ⟨hBD.1, hBD.2, ?_⟩
    refine ⟨k, ?_⟩
    have heq :
        E - 64 * M * k =
          64 * (A - M * k) + 16 * C + 4 * F + G := by
      rw [hEstep, hDstep, hBstep]
      ring
    change |E - 64 * M * k| < 64 * e
    rw [heq]
    exact hEk

/-- Exact integer geometry of the factor-certified `a = 7` edge pair.  The
first two old-cell literals hold at `q = 91,92`; the third fails and `q = 93`
is central. -/
theorem powerTwo_a7_q91_q93_oldCell_integer_fixture :
    let M : ℤ :=
      1532495540865888858358347027150309183618739122183602176
    let e : ℤ :=
      47890485652059026823698344598447161988085597568237568
    let s : ℤ :=
      -575609055860633478129483489186388793285499581201153392
    let C : ℤ :=
      2241649238970489109071864844840124512527806177289269856
    let F : ℤ :=
      909423912028481350777374183086409795062290180273908480
    let G : ℤ :=
      4532205081325295905544360865587566123605530176923249976
    M = 32 * e ∧ |F| < 15 * M ∧ |G| < 60 * M ∧
      |4 * s + C| < 4 * e ∧
      |16 * s + 4 * C + F| < 16 * e ∧
      64 * e ≤ |64 * s + 16 * C + 4 * F + G| := by
  norm_num [abs_of_nonneg, abs_of_nonpos]


/-- Canonical centered representative, with the positive midpoint selected
in the tie case. -/
def actualCenteredLift (A M : ℤ) : ℤ :=
  let r := A % M
  if r ≤ M / 2 then r else r - M

/-- Actual centered half-state at power-two odd rank `q`. -/
def actualOddHalfCenteredLift (a q : ℕ) : ℤ :=
  actualCenteredLift
    (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
    ((4 : ℤ) ^ q)

/-- Integral actual half-correction from odd rank `q` to odd rank `q+1`. -/
def actualOddHalfCorrection (a q : ℕ) : ℤ :=
  powerTwoOddDepthCorrection a q / 2

/-- The integral half-correction is exactly the three consecutive literal
LCM-ray letters surrounding the even terminal offset.  This exposes the
arithmetic content hidden by the inherited/fresh cocycle notation: the even
initial letter occurs with coefficient `-2`, while the following odd and even
letters occur with coefficient `1`. -/
theorem two_mul_actualOddHalfCorrection_eq_three_diagonalWindowIncrements
    {a q : ℕ} (ha : 2 ≤ a) :
    2 * actualOddHalfCorrection a q =
      diagonalWindowIncrement (2 ^ a) (2 * q + 3) -
        2 * diagonalWindowIncrement (2 ^ a) (2 * q + 2) +
        diagonalWindowIncrement (2 ^ a) (2 * q + 4) := by
  have hhalf :
      2 * actualOddHalfCorrection a q = powerTwoOddDepthCorrection a q := by
    exact Int.two_mul_ediv_two_of_even
      (powerTwoOddDepthCorrection_even a q)
  rw [hhalf]
  unfold powerTwoOddDepthCorrection powerTwoFreshOddIncrement
  rw [← diagonalWindowIncrement_powerTwoJump_even_offset
        (a := a) (r := q + 1) ha,
      ← diagonalWindowIncrement_powerTwoJump_even_offset
        (a := a) (r := q + 2) ha]
  congr 1 <;> omega

/-- Centering changes an integer only by a multiple of the modulus. -/
theorem actualCenteredLift_modEq (A M : ℤ) :
    Int.ModEq M (actualCenteredLift A M) A := by
  simp only [actualCenteredLift, Int.ModEq]
  split_ifs <;> simp [Int.sub_emod_right]

/-- The actual centered lift represents the integral half-correction word
at the same odd rank. -/
theorem actualOddHalfCenteredLift_modEq_halfCorrectionWord
    {a q : ℕ} (ha : 2 ≤ a) :
    Int.ModEq ((4 : ℤ) ^ q)
      (actualOddHalfCenteredLift a q)
      (powerTwoOddHalfCorrectionWord a q) := by
  unfold actualOddHalfCenteredLift Int.ModEq
  rw [actualCenteredLift_modEq]
  exact diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_half_emod ha

/-- The unwrapped affine step from the actual centered predecessor has the
same final residue as the actual integral half-correction word. -/
theorem actualOddHalf_affine_modEq_halfCorrectionWord_succ
    (a q : ℕ) (ha : 2 ≤ a) :
    Int.ModEq ((4 : ℤ) ^ (q + 1))
      (4 * actualOddHalfCenteredLift a q + actualOddHalfCorrection a q)
      (powerTwoOddHalfCorrectionWord a (q + 1)) := by
  have hscaled : Int.ModEq
      (4 * (4 : ℤ) ^ q)
      (4 * actualOddHalfCenteredLift a q)
      (4 * powerTwoOddHalfCorrectionWord a q) :=
    (actualOddHalfCenteredLift_modEq_halfCorrectionWord ha).mul_left'
  have hstep := hscaled.add_right (actualOddHalfCorrection a q)
  rw [powerTwoOddHalfCorrectionWord_succ]
  simpa [actualOddHalfCorrection, pow_succ, mul_comm] using hstep

/-- Halving the even raw correction gives the expected integer envelope. -/
theorem abs_actualOddHalfCorrection_le
    {a n : ℕ} (ha : 2 ≤ a) :
    |actualOddHalfCorrection a n| ≤
      (4 * periodLcm (2 ^ a) + 4 * n + 5 : ℤ) := by
  have hraw := abs_powerTwoOddDepthCorrection_le (a := a) (n := n) ha
  have hhalf :
      2 * actualOddHalfCorrection a n = powerTwoOddDepthCorrection a n := by
    exact Int.two_mul_ediv_two_of_even
      (powerTwoOddDepthCorrection_even a n)
  have habs :
      2 * |actualOddHalfCorrection a n| =
        |powerTwoOddDepthCorrection a n| := by
    calc
      2 * |actualOddHalfCorrection a n| =
          |2 * actualOddHalfCorrection a n| := by
            rw [abs_mul]
            norm_num
      _ = |powerTwoOddDepthCorrection a n| := by rw [hhalf]
  omega

/-- At the odd-guarded canonical depth, the parity-sharpened correction
envelope is the candidate `4H + 2m - 1`. -/
theorem abs_actualOddHalfCorrection_le_canonicalEnvelope
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth :
      oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1) :
    |actualOddHalfCorrection a (q - 1)| ≤
      (4 * periodLcm (2 ^ a) + 2 * (2 * q + 1) - 1 : ℤ) := by
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hle := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  rw [hdepth] at hle
  have hq : 1 ≤ q := by omega
  have h := abs_actualOddHalfCorrection_le
    (a := a) (n := q - 1) ha
  push_cast at h
  omega

/-- At the odd-guarded canonical rank the explicit correction envelope is
strictly smaller than the final `1/32` half-word edge. -/
theorem canonicalActualOddHalfCorrectionEnvelope_lt_edge
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth :
      oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1) :
    (4 * periodLcm (2 ^ a) + 2 * (2 * q + 1) - 1 : ℤ) <
      (4 : ℤ) ^ q / 32 := by
  let H := periodLcm (2 ^ a)
  let L := Nat.log2 H
  let m := oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a)
  have ht4 : 4 ≤ 2 ^ a := by
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) ha)
  have hLcm4 : periodLcm 4 = 12 := by
    norm_num [periodLcm]
  have h12dvd : 12 ∣ H := by
    have hdvd := periodLcm_dvd_periodLcm ht4
    rw [hLcm4] at hdvd
    simpa [H] using hdvd
  have hHpos : 0 < H := by
    simpa [H] using periodLcm_pos (2 ^ a)
  have hH : 12 ≤ H := Nat.le_of_dvd hHpos h12dvd
  have hlogLe : L ≤ H := by
    dsimp [L]
    rw [Nat.log2_eq_log_two]
    exact Nat.log_le_self 2 H
  have hHpow : H < 2 ^ (L + 1) := by
    dsimp [L]
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two H
  have hmLower : L + 10 ≤ m := by
    have hle := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
    simpa [m, canonicalAdjacentSuffixDepth, L, H] using hle
  have hmUpper : m ≤ L + 11 := by
    have hle := oddGuardedCanonicalAdjacentSuffixDepth_le_succ (2 ^ a)
    simpa [m, canonicalAdjacentSuffixDepth, L, H] using hle
  have hmTwoH : m ≤ 2 * H := by omega
  have hbudget : 4 * H + 2 * m ≤ 8 * H := by omega
  have h8H : 8 * H < 2 ^ (L + 4) := by
    calc
      8 * H < 8 * 2 ^ (L + 1) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 8)).2 hHpow
      _ = 2 ^ (L + 4) := by
        rw [show L + 4 = (L + 1) + 3 by omega, pow_add]
        norm_num
        ring
  have hexp : L + 4 ≤ m - 6 := by omega
  have hpowMono : 2 ^ (L + 4) ≤ 2 ^ (m - 6) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
  have hbudgetPow : 4 * H + 2 * m < 2 ^ (m - 6) :=
    lt_of_le_of_lt hbudget (h8H.trans_le hpowMono)
  have hbudgetPowZ :
      (4 * H + 2 * m : ℤ) < (2 : ℤ) ^ (m - 6) := by
    exact_mod_cast hbudgetPow
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hmCanon := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hmCanon
    omega
  have hmEq : m = 2 * q + 1 := by simpa [m] using hdepth
  have hedgeFactor :
      (4 : ℤ) ^ q = 32 * (2 : ℤ) ^ (2 * q - 5) := by
    calc
      (4 : ℤ) ^ q = 2 ^ (2 * q) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
      _ = 2 ^ ((2 * q - 5) + 5) := by
        congr 1
        omega
      _ = 32 * 2 ^ (2 * q - 5) := by
        rw [pow_add]
        norm_num
        ring
  have hedge :
      (4 : ℤ) ^ q / 32 = (2 : ℤ) ^ (2 * q - 5) := by
    rw [hedgeFactor]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [hedge]
  rw [hmEq] at hbudgetPowZ
  have hexpEq : 2 * q + 1 - 6 = 2 * q - 5 := by omega
  rw [hexpEq] at hbudgetPowZ
  dsimp [H] at hbudgetPowZ ⊢
  omega

/-- The actual final half-correction is automatically sub-edge at every
odd-guarded canonical power-two depth. -/
theorem abs_actualOddHalfCorrection_lt_canonicalHalfEdge
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth :
      oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1) :
    |actualOddHalfCorrection a (q - 1)| < (4 : ℤ) ^ q / 32 := by
  exact (abs_actualOddHalfCorrection_le_canonicalEnvelope ha hdepth).trans_lt
    (canonicalActualOddHalfCorrectionEnvelope_lt_edge ha hdepth)

#print axioms actualOddHalf_affine_modEq_halfCorrectionWord_succ
#print axioms abs_actualOddHalfCorrection_lt_canonicalHalfEdge

/-- At scale `P = 8e`, a centered predecessor and a sub-edge correction put
the final Euclidean residue in the central band exactly when the unwrapped
affine state avoids the radius-`e` cylinder about zero. -/
theorem baseFour_actual_central_iff_affineExclusion
    {P e u c : ℤ}
    (hP : 0 < P) (he : 0 < e) (hscale : P = 8 * e)
    (hu : |u| ≤ P / 2) (hc : |c| < e) :
    (e ≤ (4 * u + c) % (4 * P) ∧
        (4 * u + c) % (4 * P) ≤ 4 * P - e) ↔
      e ≤ |4 * u + c| := by
  have hM : 0 < 4 * P := by positivity
  have hwidth : 2 * e < 4 * P := by
    rw [hscale]
    nlinarith
  have hu' : |u| ≤ 4 * e := by
    rw [hscale] at hu
    have htwo : (2 : ℤ) ≠ 0 := by norm_num
    rw [show 8 * e = 2 * (4 * e) by ring,
      Int.mul_ediv_cancel_left _ htwo] at hu
    exact hu
  have haffineUpper : |4 * u + c| ≤ 4 * P - e := by
    have htriangle : |4 * u + c| ≤ 4 * |u| + |c| := by
      calc
        |4 * u + c| ≤ |4 * u| + |c| := abs_add_le _ _
        _ = 4 * |u| + |c| := by
          rw [abs_mul]
          norm_num
    rw [hscale]
    nlinarith
  constructor
  · intro hcentral
    by_contra hnot
    have habslt : |4 * u + c| < e := lt_of_not_ge hnot
    have hnear : NearMultiple (4 * u + c) (4 * P) e := by
      refine ⟨0, ?_⟩
      simpa using habslt
    have hedge :=
      (nearMultiple_iff_emod_edge hM he hwidth).1 hnear
    rcases hedge with hedge | hedge <;> omega
  · intro hlo
    exact emod_central_of_abs_between hM he hlo haffineUpper

/-- The sharp sign-free sufficient condition: even if the correction opposes
the predecessor, its whole magnitude can be paid before reaching the edge. -/
theorem baseFour_actual_central_of_sharpSignFreeMargin
    {P e u c : ℤ}
    (hP : 0 < P) (he : 0 < e) (hscale : P = 8 * e)
    (hu : |u| ≤ P / 2) (hc : |c| < e)
    (hmargin : e + |c| ≤ 4 * |u|) :
    e ≤ (4 * u + c) % (4 * P) ∧
      (4 * u + c) % (4 * P) ≤ 4 * P - e := by
  apply (baseFour_actual_central_iff_affineExclusion
    hP he hscale hu hc).2
  have hdiff : 0 ≤ 4 * |u| - |c| := by
    omega
  have hreverse := abs_abs_sub_abs_le_abs_sub (4 * u) (-c)
  have hreverse' : 4 * |u| - |c| ≤ |4 * u + c| := by
    have hfour : |(4 : ℤ)| = 4 := by norm_num
    rw [abs_mul, hfour, abs_neg, sub_neg_eq_add] at hreverse
    rw [abs_of_nonneg hdiff] at hreverse
    exact hreverse
  omega

#print axioms baseFour_actual_central_iff_affineExclusion
#print axioms baseFour_actual_central_of_sharpSignFreeMargin

/-- Every centered lift lies in the closed signed half-cell. -/
theorem abs_actualCenteredLift_le_half
    {A M : ℤ} (hM : 0 < M) :
    |actualCenteredLift A M| ≤ M / 2 := by
  have hr0 : 0 ≤ A % M := Int.emod_nonneg A hM.ne'
  have hrM : A % M < M := Int.emod_lt_of_pos A hM
  simp only [actualCenteredLift]
  split_ifs with hhalf
  · rw [abs_of_nonneg hr0]
    exact hhalf
  · have hneg : A % M - M < 0 := by omega
    rw [abs_of_neg hneg]
    omega

/-- For `q ≥ 3`, the predecessor modulus is eight times the final `1/32`
edge. -/
theorem fourPow_pred_eq_eight_mul_edge
    {q : ℕ} (hq : 3 ≤ q) :
    (4 : ℤ) ^ (q - 1) = 8 * ((4 : ℤ) ^ q / 32) := by
  have hedgeFactor :
      (4 : ℤ) ^ q = 32 * (2 : ℤ) ^ (2 * q - 5) := by
    calc
      (4 : ℤ) ^ q = 2 ^ (2 * q) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
      _ = 2 ^ ((2 * q - 5) + 5) := by
        congr 1
        omega
      _ = 32 * 2 ^ (2 * q - 5) := by
        rw [pow_add]
        norm_num
        ring
  have hedge :
      (4 : ℤ) ^ q / 32 = (2 : ℤ) ^ (2 * q - 5) := by
    rw [hedgeFactor]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hpredFactor :
      (4 : ℤ) ^ (q - 1) = 8 * (2 : ℤ) ^ (2 * q - 5) := by
    calc
      (4 : ℤ) ^ (q - 1) = 2 ^ (2 * (q - 1)) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
      _ = 2 ^ ((2 * q - 5) + 3) := by
        congr 1
        omega
      _ = 8 * 2 ^ (2 * q - 5) := by
        rw [pow_add]
        norm_num
        ring
  rw [hedge, hpredFactor]

/-- A single scalar margin on the actual centered penultimate state supplies
the exact odd-guard half-word band at the final rank. -/
theorem powerTwoOddGuardHalfWordBand_of_actualPenultimateMargin
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth :
      oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1)
    (hmargin :
      (4 : ℤ) ^ q / 32 +
          |actualOddHalfCorrection a (q - 1)| ≤
        4 * |actualOddHalfCenteredLift a (q - 1)|) :
    (4 : ℤ) ^ q ≤
        32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ∧
      32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ≤
        31 * (4 : ℤ) ^ q := by
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hcanonGuard := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hcanonGuard
    omega
  let P : ℤ := (4 : ℤ) ^ (q - 1)
  let e : ℤ := (4 : ℤ) ^ q / 32
  let u : ℤ := actualOddHalfCenteredLift a (q - 1)
  let c : ℤ := actualOddHalfCorrection a (q - 1)
  have hP : 0 < P := by positivity
  have hscale : P = 8 * e := by
    simpa [P, e] using fourPow_pred_eq_eight_mul_edge hq
  have hc : |c| < e := by
    simpa [c, e] using
      abs_actualOddHalfCorrection_lt_canonicalHalfEdge ha hdepth
  have he : 0 < e := (abs_nonneg c).trans_lt hc
  have hu : |u| ≤ P / 2 := by
    exact abs_actualCenteredLift_le_half hP
  have hmargin' : e + |c| ≤ 4 * |u| := by
    simpa [e, c, u] using hmargin
  have hcentral := baseFour_actual_central_of_sharpSignFreeMargin
    hP he hscale hu hc hmargin'
  have hqPred : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hmodulus : 4 * P = (4 : ℤ) ^ q := by
    rw [show q = (q - 1) + 1 by omega, pow_succ]
    simp only [P]
    ring
  have hword : Int.ModEq ((4 : ℤ) ^ q)
      (4 * u + c) (powerTwoOddHalfCorrectionWord a q) := by
    simpa [u, c, hqPred] using
      (actualOddHalf_affine_modEq_halfCorrectionWord_succ a (q - 1) ha)
  rw [hmodulus, hword.eq] at hcentral
  have hfinalScale : (4 : ℤ) ^ q = 32 * e := by
    calc
      (4 : ℤ) ^ q = 4 * P := hmodulus.symm
      _ = 32 * e := by rw [hscale]; ring
  rcases hcentral with ⟨hlo, hhi⟩
  constructor <;> omega

/-- Cofinal scalar producer using only the explicit correction envelope and
the actual centered penultimate state. -/
def PowerTwoActualPenultimateEnvelopeMarginSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 2 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    (4 : ℤ) ^ q / 32 +
        (4 * periodLcm (2 ^ a) + 2 * (2 * q + 1) - 1 : ℤ) ≤
      4 * |actualOddHalfCenteredLift a (q - 1)|

/-- The envelope-only actual-state producer supplies the landed half-word
band interface. -/
theorem powerTwoOddGuardHalfWordBandSupply_of_actualPenultimateEnvelopeMargin
    (hsupply : PowerTwoActualPenultimateEnvelopeMarginSupply) :
    PowerTwoOddGuardHalfWordBandSupply := by
  intro a₀
  obtain ⟨a, q, ha, hdepth, hmargin⟩ := hsupply a₀
  have ha2 : 2 ≤ a := (le_max_left 2 a₀).trans ha
  have hcEnvelope :=
    abs_actualOddHalfCorrection_le_canonicalEnvelope ha2 hdepth
  have hactualMargin :
      (4 : ℤ) ^ q / 32 +
          |actualOddHalfCorrection a (q - 1)| ≤
        4 * |actualOddHalfCenteredLift a (q - 1)| := by
    omega
  obtain ⟨hlo, hhi⟩ :=
    powerTwoOddGuardHalfWordBand_of_actualPenultimateMargin
      ha2 hdepth hactualMargin
  exact ⟨a, q, ha, hdepth, hlo, hhi⟩

/-- The one actual-state envelope margin is therefore sufficient for the
landed Erdős #249 irrationality theorem. -/
theorem irrational_totientSeries_of_actualPenultimateEnvelopeMarginSupply
    (hsupply : PowerTwoActualPenultimateEnvelopeMarginSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_powerTwoOddGuardHalfWordBandSupply
    (powerTwoOddGuardHalfWordBandSupply_of_actualPenultimateEnvelopeMargin
      hsupply)

#print axioms powerTwoOddGuardHalfWordBand_of_actualPenultimateMargin
#print axioms irrational_totientSeries_of_actualPenultimateEnvelopeMarginSupply

/-- Exact signed normal form of `e ≤ |4u+c|` when the correction is shorter
than the edge. -/
def ActualPenultimateSignedMargin (u c e : ℤ) : Prop :=
  (0 ≤ u * c ∧ e ≤ 4 * |u| + |c|) ∨
    (u * c < 0 ∧ e + |c| ≤ 4 * |u|)

/-- The exact affine exclusion has a two-branch signed normal form.  Same
sign adds the correction magnitude; opposite sign spends it. -/
theorem actualAffineExclusion_iff_signedMargin
    {e u c : ℤ} (he : 0 < e) (hc : |c| < e) :
    e ≤ |4 * u + c| ↔ ActualPenultimateSignedMargin u c e := by
  constructor
  · intro haffine
    by_cases hsame : 0 ≤ u * c
    · left
      refine ⟨hsame, ?_⟩
      rcases (Int.mul_nonneg_iff.mp hsame) with hpp | hnn
      · rw [abs_of_nonneg hpp.1, abs_of_nonneg hpp.2]
        rw [abs_of_nonneg (by omega)] at haffine
        omega
      · rw [abs_of_nonpos hnn.1, abs_of_nonpos hnn.2]
        rw [abs_of_nonpos (by omega)] at haffine
        omega
    · right
      have hopp : u * c < 0 := lt_of_not_ge hsame
      refine ⟨hopp, ?_⟩
      rcases Int.mul_neg_iff.mp hopp with hposneg | hnegpos
      · rw [abs_of_neg hposneg.2] at hc
        rw [abs_of_pos hposneg.1, abs_of_neg hposneg.2]
        by_cases hsum : 0 ≤ 4 * u + c
        · rw [abs_of_nonneg hsum] at haffine
          omega
        · rw [abs_of_neg (lt_of_not_ge hsum)] at haffine
          omega
      · rw [abs_of_pos hnegpos.2] at hc
        rw [abs_of_neg hnegpos.1, abs_of_pos hnegpos.2]
        by_cases hsum : 4 * u + c ≤ 0
        · rw [abs_of_nonpos hsum] at haffine
          omega
        · rw [abs_of_pos (lt_of_not_ge hsum)] at haffine
          omega
  · rintro (⟨hsame, hmargin⟩ | ⟨hopp, hmargin⟩)
    · rcases (Int.mul_nonneg_iff.mp hsame) with hpp | hnn
      · rw [abs_of_nonneg hpp.1, abs_of_nonneg hpp.2] at hmargin
        rw [abs_of_nonneg (by omega)]
        omega
      · rw [abs_of_nonpos hnn.1, abs_of_nonpos hnn.2] at hmargin
        rw [abs_of_nonpos (by omega)]
        omega
    · rcases Int.mul_neg_iff.mp hopp with hposneg | hnegpos
      · rw [abs_of_pos hposneg.1, abs_of_neg hposneg.2] at hmargin
        have hsum : 0 < 4 * u + c := by omega
        rw [abs_of_pos hsum]
        omega
      · rw [abs_of_neg hnegpos.1, abs_of_pos hnegpos.2] at hmargin
        have hsum : 4 * u + c < 0 := by omega
        rw [abs_of_neg hsum]
        omega

/-- Generic centrality is equivalent to the exact signed predecessor margin. -/
theorem baseFour_actual_central_iff_signedMargin
    {P e u c : ℤ}
    (hP : 0 < P) (he : 0 < e) (hscale : P = 8 * e)
    (hu : |u| ≤ P / 2) (hc : |c| < e) :
    (e ≤ (4 * u + c) % (4 * P) ∧
        (4 * u + c) % (4 * P) ≤ 4 * P - e) ↔
      ActualPenultimateSignedMargin u c e := by
  rw [baseFour_actual_central_iff_affineExclusion hP he hscale hu hc]
  exact actualAffineExclusion_iff_signedMargin he hc

/-- At the odd-guarded canonical rank, the landed half-word band is exactly
the signed actual-predecessor margin. -/
theorem powerTwoOddGuardHalfWordBand_iff_actualPenultimateSignedMargin
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth :
      oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1) :
    ((4 : ℤ) ^ q ≤
        32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ∧
      32 * (powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q) ≤
        31 * (4 : ℤ) ^ q) ↔
      ActualPenultimateSignedMargin
        (actualOddHalfCenteredLift a (q - 1))
        (actualOddHalfCorrection a (q - 1))
        ((4 : ℤ) ^ q / 32) := by
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hcanonGuard := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hcanonGuard
    omega
  let P : ℤ := (4 : ℤ) ^ (q - 1)
  let e : ℤ := (4 : ℤ) ^ q / 32
  let u : ℤ := actualOddHalfCenteredLift a (q - 1)
  let c : ℤ := actualOddHalfCorrection a (q - 1)
  have hP : 0 < P := by positivity
  have hscale : P = 8 * e := by
    simpa [P, e] using fourPow_pred_eq_eight_mul_edge hq
  have hc : |c| < e := by
    simpa [c, e] using
      abs_actualOddHalfCorrection_lt_canonicalHalfEdge ha hdepth
  have he : 0 < e := (abs_nonneg c).trans_lt hc
  have hu : |u| ≤ P / 2 := by
    exact abs_actualCenteredLift_le_half hP
  have hqPred : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hmodulus : 4 * P = (4 : ℤ) ^ q := by
    rw [show q = (q - 1) + 1 by omega, pow_succ]
    simp only [P]
    ring
  have hword : Int.ModEq ((4 : ℤ) ^ q)
      (4 * u + c) (powerTwoOddHalfCorrectionWord a q) := by
    simpa [u, c, hqPred] using
      (actualOddHalf_affine_modEq_halfCorrectionWord_succ a (q - 1) ha)
  have hcentralIff :
      (e ≤ powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - e) ↔
        ActualPenultimateSignedMargin u c e := by
    rw [← hword.eq, ← hmodulus]
    exact baseFour_actual_central_iff_signedMargin hP he hscale hu hc
  have hfinalScale : (4 : ℤ) ^ q = 32 * e := by
    calc
      (4 : ℤ) ^ q = 4 * P := hmodulus.symm
      _ = 32 * e := by rw [hscale]; ring
  constructor
  · intro hband
    apply hcentralIff.mp
    constructor <;> omega
  · intro hsigned
    have hcentral := hcentralIff.mpr hsigned
    constructor <;> omega

/-- Cofinal exact signed residual on the actual predecessor/correction pair. -/
def PowerTwoActualPenultimateSignedMarginSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 2 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ActualPenultimateSignedMargin
      (actualOddHalfCenteredLift a (q - 1))
      (actualOddHalfCorrection a (q - 1))
      ((4 : ℤ) ^ q / 32)

/-- The signed residual is not merely sufficient: it is equivalent to the
landed odd-guard half-word supply. -/
theorem powerTwoActualPenultimateSignedMarginSupply_iff_halfWordBandSupply :
    PowerTwoActualPenultimateSignedMarginSupply ↔
      PowerTwoOddGuardHalfWordBandSupply := by
  constructor
  · intro hsupply a₀
    obtain ⟨a, q, ha, hdepth, hsigned⟩ := hsupply a₀
    have ha2 : 2 ≤ a := (le_max_left 2 a₀).trans ha
    obtain ⟨hlo, hhi⟩ :=
      (powerTwoOddGuardHalfWordBand_iff_actualPenultimateSignedMargin
        ha2 hdepth).2 hsigned
    exact ⟨a, q, ha, hdepth, hlo, hhi⟩
  · intro hsupply a₀
    obtain ⟨a, q, ha, hdepth, hlo, hhi⟩ := hsupply a₀
    have ha2 : 2 ≤ a := (le_max_left 2 a₀).trans ha
    have hsigned :=
      (powerTwoOddGuardHalfWordBand_iff_actualPenultimateSignedMargin
        ha2 hdepth).1 ⟨hlo, hhi⟩
    exact ⟨a, q, ha, hdepth, hsigned⟩

/-- Exact signed actual-state supply form of the landed irrationality
consumer. -/
theorem irrational_totientSeries_of_actualPenultimateSignedMarginSupply
    (hsupply : PowerTwoActualPenultimateSignedMarginSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_powerTwoOddGuardHalfWordBandSupply
    (powerTwoActualPenultimateSignedMarginSupply_iff_halfWordBandSupply.mp
      hsupply)

#print axioms actualAffineExclusion_iff_signedMargin
#print axioms powerTwoOddGuardHalfWordBand_iff_actualPenultimateSignedMargin
#print axioms powerTwoActualPenultimateSignedMarginSupply_iff_halfWordBandSupply
#print axioms irrational_totientSeries_of_actualPenultimateSignedMarginSupply

#print axioms foreignDiagonalDefect_misses_fullTarget_of_projectionCert
#print axioms foreignDiagonalDefect_misses_fullTarget_of_residueCert
#print axioms diagonalFreshLossResidueCert_iff_projectionCert
#print axioms irrational_totientSeries_of_diagonalFreshLossProjectionSupply
#print axioms diagonalFreshLossProjectionCell_seven
#print axioms foreignDiagonalDefect_misses_fullTarget_seven_via_projection
#print axioms windowNumerator_prefix_suffix
#print axioms diagonalSuffixResidue_eq_increment_sum
#print axioms diagonalWindowResidue_mod_suffix
#print axioms diagonalFreshLossResidueCert_of_suffix_central
#print axioms diagonalAdjacentSuffixResidue_eq_terminal_corrected
#print axioms diagonalAdjacentSuffixResidue_eq_rawBlock
#print axioms diagonalAdjacentSuffixRawBlock_succ_depth
#print axioms diagonalAdjacentSuffixResidue_succ_depth
#print axioms diagonalAdjacentSuffixResidue_target_depth
#print axioms diagonalAdjacentSuffixRawBlock_add_two
#print axioms abs_diagonalTargetDepthCorrection_le
#print axioms diagonalTargetDepthCorrectionEnvelope_lt_canonical_edge
#print axioms abs_diagonalTargetDepthCorrection_lt_canonical_edge
#print axioms baseTwoTargetResidue_central_iff_unwrapped
#print axioms canonicalAdjacentSuffixResidue_central_iff_penultimate_exact
#print axioms baseTwoTargetResidue_central_of_strongBand
#print axioms baseTwoTargetResidue_central_of_envelope
#print axioms canonicalAdjacentSuffixResidue_central_of_penultimate_strongBand
#print axioms canonicalAdjacentSuffixResidue_central_of_penultimate_margin
#print axioms canonicalAdjacentSuffixCentralSupply_iff_penultimateExact
#print axioms canonicalAdjacentSuffixPenultimateMarginSupply_of_strongBand
#print axioms diagonalHeightIncrement_two_mul_even
#print axioms diagonalHeightIncrement_two_mul_odd
#print axioms diagonalWindowIncrement_powerTwoJump_even
#print axioms diagonalWindowIncrement_powerTwoJump_odd
#print axioms diagonalWindowIncrement_powerTwoJump_even_offset
#print axioms diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_step
#print axioms diagonalAdjacentSuffixResidue_powerTwo_oddDepth_step
#print axioms baseFourResidue_central_of_correction_bounds
#print axioms diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_of_correction_bounds
#print axioms baseTwoTargetResidue_central_iff_topBit
#print axioms baseTwoTargetResidue_noncentral_iff_carryEdgeAlignment
#print axioms canonicalAdjacentSuffixDepth_powerTwo_jump
#print axioms diagonalTargetDepthCorrection_powerTwo_of_even_predepth
#print axioms diagonalTargetDepthCorrection_powerTwo_of_odd_predepth
#print axioms powerTwoOddCorrectionWord_succ
#print axioms diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_closed
#print axioms diagonalAdjacentSuffixResidue_powerTwo_oddDepth_lowBits
#print axioms diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_correctionWord
#print axioms powerTwoOddDepthCorrection_even
#print axioms powerTwoOddCorrectionWord_eq_two_mul_halfWord
#print axioms diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_two_mul_halfWord
#print axioms diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand
#print axioms oldMobiusIncrement_eq_sum_forwardDifference_channel
#print axioms oldMobiusIncrement_eq_scale_gcdWordCoeff
#print axioms diagonalAdjacentSuffixRawBlock_eq_oldMobius_add_finiteForeign
#print axioms finiteForeignChannelIncrement_eq_phaseSum
#print axioms forwardDifference_mobiusTotientChannel_of_not_dvd
#print axioms foreignChannelPhaseTerm_low_double_echo
#print axioms foreignChannelPhaseTerm_weighted_low_double_echo
#print axioms dvd_offset_sub_of_two_low_supports
#print axioms dvd_offset_sub_of_two_top_supports
#print axioms prime_of_squarefree_not_dvd_periodLcm_lt_two_mul
#print axioms repeated_low_support_primePow_of_short_periodLcm_window
#print axioms repeated_top_support_primePow_of_short_periodLcm_window
#print axioms not_three_low_supports_of_short_foreign_window
#print axioms not_three_top_supports_of_short_foreign_window
#print axioms not_two_low_supports_of_squarefree_tail_window
#print axioms not_two_top_supports_of_squarefree_tail_window
#print axioms eq_or_eq_add_of_modEq_of_pos_le_two_mul
#print axioms prime_lower_support_iff_eq_base_or_add
#print axioms prime_top_base_eq
#print axioms prime_top_support_iff_eq_base_or_add
#print axioms prime_lower_support_quotient
#print axioms prime_top_support_quotient
#print axioms squarefree_of_finiteForeignChannelRawPulse_ne_zero
#print axioms finiteForeignChannelIncrement_eq_enlarged_phaseSum
#print axioms finiteForeignChannelRawBlock_eq_sum_rawPulses
#print axioms diagonalAdjacentSuffixRawBlock_eq_scaledGcdWord_add_sum_foreignRawPulses
#print axioms diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_of_signedSplit
#print axioms canonical_a2_to_a7_signedSplitSafe_fixture
#print axioms nearMultiple_iff_emod_edge
#print axioms nearMultiple_correction_of_twoRank
#print axioms powerTwoOddDepthCorrection_nearMultiple_of_twoRank
#print axioms abs_powerTwoOddDepthCorrection_le
#print axioms two_mul_actualOddHalfCorrection_eq_three_diagonalWindowIncrements
#print axioms odd_oddGuardedCanonicalAdjacentSuffixDepth
#print axioms exists_oddGuardedCanonicalAdjacentSuffixDepth_index
#print axioms canonicalAdjacentSuffixDepth_succ_width
#print axioms oddGuardedCanonicalAdjacentSuffixDepth_width
#print axioms diagonalFreshLossResidueCert_or_of_powerTwo_oddGuard_halfWordBand
#print axioms diagonalAdjacentSuffixGapSupply_of_powerTwoOddGuardHalfWordBand
#print axioms irrational_totientSeries_of_powerTwoOddGuardHalfWordBandSupply
#print axioms diagonalAdjacentSuffixResidue_powerTwo_oddDepth_topBit_iff
#print axioms powerTwoOddHalfCorrectionWord_normalized_step
#print axioms powerTwoOddHalfCorrectionWord_normalized_eq_sum
#print axioms powerTwoOddHalfCorrectionWord_eq_raw_sub_seed
#print axioms baseFour_positiveWrap_ediv_succ
#print axioms baseFour_edge_iff_centered_tube
#print axioms baseFour_zeroCorrection_centered_tube_forever
#print axioms twoFutureEdgeRanks_iff_oldStateCrossing
#print axioms threeFutureEdgeRanks_iff_oldStateCrossing
#print axioms powerTwo_a7_q91_q93_oldCell_integer_fixture
#print axioms diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap_sharp
#print axioms diagonalSymmetricResidueCert_of_suffix_central
#print axioms diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap
#print axioms diagonalFreshLossResidueCert_or_of_adjacent_dyadic_gap
#print axioms diagonalSymmetricResidueCert_or_of_adjacent_suffix_gap
#print axioms diagonalSymmetricResidueCert_or_of_adjacent_dyadic_gap
#print axioms oddGuardedCanonicalAdjacentSuffixDepth_symmetric_width
#print axioms diagonalSymmetricResidueCert_or_of_powerTwo_oddGuard_halfWordBand
#print axioms diagonalFreshLossProjectionSupply_of_adjacentSuffixGapSupply
#print axioms irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateExactSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateMarginSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateStrongBandSupply
#print axioms periodLcm_strict_jump_iff_succ_not_dvd
#print axioms succ_eq_prime_pow_of_periodLcm_strict_jump
#print axioms periodLcm_succ_eq_prime_mul_of_strict_jump
#print axioms periodLcm_pow_two_strict_jump
#print axioms periodLcm_pow_two_eq_two_mul
#print axioms exists_periodLcm_strict_jump_ge
#print axioms canonicalAdjacentSuffixCentralSlack_eq_of_periodLcm_eq
#print axioms canonicalAdjacentSuffixPostJumpSlackSupply_of_powerTwo
#print axioms canonicalAdjacentSuffixJumpSlackSupply_of_postJump
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixJumpCentralSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixJumpSlackSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixPostJumpSlackSupply
#print axioms irrational_totientSeries_of_canonicalAdjacentSuffixPowerTwoPostJumpSlackSupply
#print axioms foreignDiagonalDefect_misses_fullTarget_seven_via_suffix
#print axioms periodLcm_dvd_of_forall_pos_le
#print axioms one_le_factorization_centralBinom_of_prime_pow_window
#print axioms prime_dvd_centralBinom_of_prime_pow_window
#print axioms periodLcm_two_mul_dvd_periodLcm_mul_centralBinom
#print axioms periodLcm_two_mul_le_periodLcm_mul_centralBinom
#print axioms periodLcm_two_mul_le_periodLcm_mul_four_pow
#print axioms periodLcm_sixteen_lt_two_pow_twenty
#print axioms periodLcm_pow_two_lt_two_pow_guardTwelve
#print axioms canonicalAdjacentSuffixDepth_powerTwo_succ_lt_two_mul
#print axioms canonicalAdjacentSuffixDepth_powerTwo_lt_two_mul
#print axioms oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_lt_two_mul
#print axioms oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_succ_lt_two_mul
#print axioms prime_of_squarefree_repeated_low_support_powerTwo_oddGuarded
#print axioms prime_of_squarefree_repeated_top_support_powerTwo_oddGuarded

end Erdos257PeriodNoncollapse.DiagonalFreshLossBridge
