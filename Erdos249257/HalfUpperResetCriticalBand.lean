import Erdos249257.HalfCylinderMiddleCarryLowerBound
import Mathlib.Tactic

/-!
# The single critical dyadic band at an upper reset

The existing upper-reset route for Erdős #257 asks a reset charge `E` to avoid
one linear-width interval below every power

`2^(d-j+1)`, for `0 ≤ j ≤ d`.

Only one of those intervals can be critical: the smallest dyadic power still
at least `E`.  Larger powers have more room and smaller linear widths; smaller
powers are already strictly below `E`.  This file proves that reduction in
`dyadicBandEscape_iff_exists_critical`, then specializes it to the concrete
seam reset charge.  Thus the local `∀ j` in
`SeamUpperResetDyadicBandEscape` is exactly equivalent to one certified
nearest-boundary gap at each upper reset.

This is a quantifier reduction, not an assumption that the critical gap is
large.  The remaining arithmetic obligation is displayed without hiding it
behind the former family of bands.
-/

namespace Erdos249257.HalfUpperResetCriticalBand

open Finset
open HalfCylinderIntegerGreedy

/-- `j` indexes the smallest power `2^(d-j+1)` that is still at least `E`.
The final disjunction handles the last index, where there is no next power in
the band family. -/
def CriticalDyadicBandIndex (d E j : ℕ) : Prop :=
  j ≤ d ∧
    E ≤ 2 ^ (d - j + 1) ∧
      (j = d ∨ 2 ^ (d - (j + 1) + 1) < E)

/-- Avoidance of every width-`2(d+j)` interval immediately below the dyadic
power indexed by `j`. -/
def DyadicBandEscape (d E : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ d →
    2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)

/-- Provided the charge lies below the top dyadic boundary, a critical index
always exists. -/
theorem exists_criticalDyadicBandIndex
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    ∃ j : ℕ, CriticalDyadicBandIndex d E j := by
  let eligible : Finset ℕ :=
    (Finset.range (d + 1)).filter
      (fun j => E ≤ 2 ^ (d - j + 1))
  have heligible : eligible.Nonempty := by
    refine ⟨0, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨by simp, ?_⟩
    simpa using hE
  let j : ℕ := eligible.max' heligible
  have hjmem : j ∈ eligible := Finset.max'_mem eligible heligible
  have hjrange : j < d + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
  have hjd : j ≤ d := by omega
  have hjbelow : E ≤ 2 ^ (d - j + 1) :=
    (Finset.mem_filter.mp hjmem).2
  refine ⟨j, hjd, hjbelow, ?_⟩
  by_cases hjlast : j = d
  · exact Or.inl hjlast
  · right
    have hjlt : j < d := lt_of_le_of_ne hjd hjlast
    have hnextNot : j + 1 ∉ eligible := by
      intro hnextMem
      have hmax : j + 1 ≤ j :=
        Finset.le_max' eligible (j + 1) hnextMem
      omega
    have hnotBelow : ¬ E ≤ 2 ^ (d - (j + 1) + 1) := by
      intro hbelow
      apply hnextNot
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), hbelow⟩
    omega

/-- A gap at the single critical dyadic boundary implies all band escapes.
For earlier indices, the power grows while the required width shrinks.  For
later indices, criticality says the power is already strictly below `E`. -/
theorem dyadicBandEscape_of_critical
    {d E j₀ : ℕ}
    (hcritical : CriticalDyadicBandIndex d E j₀)
    (hgap : E + 2 * (d + j₀) ≤ 2 ^ (d - j₀ + 1)) :
    DyadicBandEscape d E := by
  intro j hjd
  rcases hcritical with ⟨hj₀d, hEbelow, hj₀next⟩
  by_cases hj : j ≤ j₀
  · right
    have hexp : d - j₀ + 1 ≤ d - j + 1 := by omega
    have hpow : 2 ^ (d - j₀ + 1) ≤ 2 ^ (d - j + 1) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    omega
  · left
    have hj₀ltj : j₀ < j := Nat.lt_of_not_ge hj
    rcases hj₀next with hj₀last | hnext
    · omega
    · have hexp : d - j + 1 ≤ d - (j₀ + 1) + 1 := by omega
      have hpow : 2 ^ (d - j + 1) ≤ 2 ^ (d - (j₀ + 1) + 1) :=
        Nat.pow_le_pow_right (by norm_num) hexp
      exact hpow.trans_lt hnext

/-- Exact generic quantifier collapse: the universal band family is
equivalent to one critical-index certificate. -/
theorem dyadicBandEscape_iff_exists_critical
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    DyadicBandEscape d E ↔
      ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
        E + 2 * (d + j) ≤ 2 ^ (d - j + 1) := by
  constructor
  · intro hall
    obtain ⟨j, hcritical⟩ := exists_criticalDyadicBandIndex hE
    refine ⟨j, hcritical, ?_⟩
    rcases hall j hcritical.1 with habove | hbelow
    · have hEbelow := hcritical.2.1
      omega
    · exact hbelow
  · rintro ⟨j, hcritical, hgap⟩
    exact dyadicBandEscape_of_critical hcritical hgap

/-- The concrete reset charge in the seam upper branch. -/
noncomputable def seamUpperResetCharge (d : ℕ) (hd5 : 5 ≤ d) : ℕ :=
  4 * (seamAdjacentCut d hd5).overshoot +
    (seamAdjacentCut d hd5).abovePulse

/-- On an actual upper reset, the concrete charge is at most the top dyadic
boundary. -/
theorem seamUpperResetCharge_le
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    seamUpperResetCharge d hd5 ≤ 2 ^ (d + 1) := by
  have hcylinder :=
    seamUpperBranch_remainder_add_resetCharge_eq hd5 hcarry
  unfold seamUpperResetCharge
  omega

/-- The concrete all-`j` upper-reset condition is exactly one critical gap. -/
theorem seamUpperResetBand_iff_exists_critical
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    (∀ j : ℕ, j ≤ d →
        2 ^ (d - j + 1) < seamUpperResetCharge d hd5 ∨
          seamUpperResetCharge d hd5 + 2 * (d + j) ≤
            2 ^ (d - j + 1)) ↔
      ∃ j : ℕ,
        CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j ∧
          seamUpperResetCharge d hd5 + 2 * (d + j) ≤
            2 ^ (d - j + 1) := by
  exact dyadicBandEscape_iff_exists_critical
    (seamUpperResetCharge_le hd5 hcarry)

/-- The affine right-run charge splits at every suffix boundary.  Thus the
last `r` actual pulse rows form a genuine base-four packet, while all earlier
rows contribute a multiple of `4^r`.

This is the algebraic bridge from the full critical-gap identity to local
divisor-incidence information in the terminal pulse rows. -/
theorem affineRightRunCharge_add (pulse : ℕ → ℕ) (m r : ℕ) :
    affineRightRunCharge pulse (m + r) =
      4 ^ r * affineRightRunCharge pulse m +
        affineRightRunCharge (fun q ↦ pulse (m + q)) r := by
  induction r with
  | zero => simp [affineRightRunCharge]
  | succ r ih =>
      rw [show m + (r + 1) = (m + r) + 1 by omega]
      simp only [affineRightRunCharge, ih, pow_succ]
      ring

/-- The actual below pulse is a paired divisor-incidence coefficient, not an
arbitrary affine digit.  This is the support-specific input retained by every
suffix packet below. -/
theorem seamAdjacentCut_belowPulse_eq_pairedSupportCoeff
    {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).belowPulse =
      supportCoeff (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)
          (2 * s + 2) +
        2 * supportCoeff (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)
          (2 * s + 1) := by
  change wordPulse s (seamGreedyWord s).toNatWord = _
  exact wordPulse_eq_pairedSupportCoeff (seamGreedyWord s)

/-- Every suffix packet inherits the corresponding base-four divisibility
from a full affine cylinder.  For a small terminal remainder this converts
the global cylinder into a finite congruence involving only the last `r`
actual pulse rows. -/
theorem four_pow_dvd_remainder_add_affineRightRunCharge_suffix
    (R G : ℕ) (pulse : ℕ → ℕ) (k r : ℕ) (hr : r ≤ k)
    (hexact : R + affineRightRunCharge pulse k = 4 ^ k * G) :
    4 ^ r ∣
      R + affineRightRunCharge (fun q ↦ pulse (k - r + q)) r := by
  have hsplit := affineRightRunCharge_add pulse (k - r) r
  rw [Nat.sub_add_cancel hr] at hsplit
  have hsum : 4 ^ r ∣ R + affineRightRunCharge pulse k := by
    rw [hexact]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 4 hr) G
  have hsum' :
      4 ^ r ∣
        (R + affineRightRunCharge (fun q ↦ pulse (k - r + q)) r) +
          4 ^ r * affineRightRunCharge pulse (k - r) := by
    rw [hsplit] at hsum
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum
  exact (Nat.dvd_add_iff_left (dvd_mul_right (4 ^ r)
    (affineRightRunCharge pulse (k - r)))).mpr hsum'

/-- If a positive remainder smaller than `n ≤ M` completes a zero residue
with a packet `C`, then the packet residue lies in the top `n`-window modulo
`M`.  The separate zero alternative is retained for the degenerate
remainder-zero case. -/
theorem modPacket_eq_zero_or_topWindow_of_small
    {M R C n : ℕ} (hM : 0 < M)
    (hmod : (R + C) % M = 0)
    (hsmall : R < n) (hnM : n ≤ M) :
    C % M = 0 ∨ M - n < C % M := by
  by_cases hR0 : R = 0
  · left
    simpa [hR0] using hmod
  · right
    have hRpos : 0 < R := Nat.pos_of_ne_zero hR0
    have hRltM : R < M := hsmall.trans_le hnM
    have hmod' : (R + C % M) % M = 0 := by
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hRltM] using hmod
    have hdvd : M ∣ R + C % M := Nat.dvd_of_mod_eq_zero hmod'
    obtain ⟨a, ha⟩ := hdvd
    have hq : C % M < M := Nat.mod_lt _ hM
    have hsumlt : R + C % M < M * 2 := by omega
    have haPos : 0 < a := by
      by_contra ha0
      have haZero : a = 0 := Nat.eq_zero_of_not_pos ha0
      subst a
      simp at ha
      omega
    have haLt : a < 2 := by
      apply (Nat.mul_lt_mul_left hM).mp
      rw [← ha]
      exact hsumlt
    have ha1 : a = 1 := by omega
    rw [ha1, mul_one] at ha
    omega

/-- **Exact actual-run critical-gap identity.**  If an upper reset at row `d`
is followed by exactly the displayed `k` right recurrences, then the terminal
remainder plus the full base-four pulse charge is the `4^k`-dilate of the
single dyadic gap at index `k`.

This spends the actual run length rather than asking for every hypothetical
band.  It is the division-free identity

`R_(d+k+1) + C_k = 4^k * (2^(d-k+1) - E_d)`.
-/
theorem seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    seamIntegerGreedyRemainder (d + k + 1) +
        affineRightRunCharge
          (fun j ↦
            (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k =
      4 ^ k *
        (2 ^ (d - k + 1) - seamUpperResetCharge d hd5) := by
  let E := seamUpperResetCharge d hd5
  let C := affineRightRunCharge
    (fun j ↦ (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E + C =
      2 ^ (d + k + 1) at hcylinder
  have hfactor :
      4 ^ k * 2 ^ (d - k + 1) = 2 ^ (d + k + 1) := by
    rw [show 4 ^ k = 2 ^ (2 * k) by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
    congr 1
    omega
  have hweighted : 4 ^ k * E ≤ 4 ^ k * 2 ^ (d - k + 1) := by
    rw [hfactor]
    omega
  have hE : E ≤ 2 ^ (d - k + 1) :=
    Nat.le_of_mul_le_mul_left hweighted (pow_pos (by norm_num) k)
  change seamIntegerGreedyRemainder (d + k + 1) + C =
      4 ^ k * (2 ^ (d - k + 1) - E)
  rw [Nat.mul_sub_left_distrib, hfactor]
  omega

/-- Every suffix of an actual upper/right cylinder is a divisor-incidence
packet completing the terminal remainder to zero modulo the corresponding
power of four. -/
theorem seamUpperThenRightRun_suffixCharge_dvd_fourPow
    {d k r : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d) (hrk : r ≤ k)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    4 ^ r ∣ seamIntegerGreedyRemainder (d + k + 1) +
      affineRightRunCharge
        (fun q ↦
          (seamAdjacentCut (d + (k - r + q) + 1) (by omega)).belowPulse) r := by
  let pulse : ℕ → ℕ := fun j ↦
    (seamAdjacentCut (d + j + 1) (by omega)).belowPulse
  have hexact :
      seamIntegerGreedyRemainder (d + k + 1) +
          affineRightRunCharge pulse k =
        4 ^ k * (2 ^ (d - k + 1) - seamUpperResetCharge d hd5) := by
    simpa [pulse] using
      (seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
        hd5 hk hcarry hrun)
  have hdiv := four_pow_dvd_remainder_add_affineRightRunCharge_suffix
    (seamIntegerGreedyRemainder (d + k + 1))
    (2 ^ (d - k + 1) - seamUpperResetCharge d hd5)
    pulse k r hrk hexact
  simpa [pulse, Nat.add_assoc] using hdiv

/-- The additive recurrence used by the exact cylinder characterizes the
actual right branch; neither the upper nor the middle branch can satisfy it. -/
theorem seamRightBranch_of_remainder_add_charge_eq
    {s : ℕ} (hs : 5 ≤ s)
    (hrec :
      seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) +
          (seamAdjacentCut s hs).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder s) :
    ¬ (seamAdjacentCut s hs).successorCarries ∧
      (seamAdjacentCut s hs).terminalWeight ≤
        4 * (seamAdjacentCut s hs).remainder +
          (seamPerturbedFamily s (by omega)).gap -
          (seamAdjacentCut s hs).belowPulse := by
  classical
  by_cases hcarry : (seamAdjacentCut s hs).successorCarries
  · exfalso
    let F := seamPerturbedFamily s (by omega)
    let K := seamAdjacentCut s hs
    have hbelowAbove : F.oldSum K.below < F.oldSum K.above :=
      lt_of_le_of_lt K.below_admissible K.above_strict
    have hsep := F.separated hbelowAbove
    have hbelow := K.old_below_add_remainder
    have habove := K.capacity_add_overshoot
    change F.oldSum K.below + K.remainder = seamSubsetTarget s at hbelow
    change seamSubsetTarget s + K.overshoot = F.oldSum K.above at habove
    have hgapRO : F.gap ≤ K.remainder + K.overshoot := by
      omega
    change 2 ^ (s + 1) ≤
      (seamAdjacentCut s hs).remainder +
        (seamAdjacentCut s hs).overshoot at hgapRO
    rw [seamAdjacentCut_remainder hs] at hgapRO
    have hreset :=
      seamUpperBranch_remainder_add_resetCharge_eq hs hcarry
    have hbp := seamAdjacentCut_belowPulse_le hs
    have hlinear :=
      two_mul_add_four_lt_two_pow_succ (show 3 ≤ s by omega)
    have hbad :
        2 * 2 ^ (s + 1) ≤
          (seamAdjacentCut s hs).belowPulse + 4 := by
      omega
    have hsmall :
        (seamAdjacentCut s hs).belowPulse + 4 < 2 ^ (s + 1) := by
      omega
    omega
  · refine ⟨hcarry, ?_⟩
    by_contra hright
    have hmiddle :
        4 * (seamAdjacentCut s hs).remainder +
              (seamPerturbedFamily s (by omega)).gap -
              (seamAdjacentCut s hs).belowPulse <
            (seamAdjacentCut s hs).terminalWeight :=
      Nat.lt_of_not_ge hright
    have htri := (seamAdjacentCut s hs).nextRemainder_trichotomy
    rw [if_neg hcarry, if_pos hmiddle,
      seamAdjacentCut_nextRemainder hs,
      seamAdjacentCut_remainder hs] at htri
    change seamIntegerGreedyRemainder (s + 1) =
        4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) -
          (seamAdjacentCut s hs).belowPulse at htri
    have hbp := seamAdjacentCut_belowPulse_le hs
    have hlinear :=
      two_mul_add_four_lt_two_pow_succ (show 3 ≤ s by omega)
    have htriAdd :
        seamIntegerGreedyRemainder (s + 1) +
            (seamAdjacentCut s hs).belowPulse =
          4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
      omega
    omega

/-- During a genuine upper-then-right run, every intermediate selected
support is the reset upper support together with the consecutive ranks filled
by the right branches.  The recurrence itself supplies the branch facts. -/
theorem seamUpperThenRightRun_support
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    ∀ q : ℕ, q ≤ k →
      seamWordSupport (seamGreedyWord (d + q + 1)) =
        seamWordSupport (seamAdjacentCut d hd5).above ∪
          Finset.Ico (d + 1) (d + q + 1) := by
  classical
  intro q
  induction q with
  | zero =>
      intro _hq
      have hword :=
        seamGreedyWord_succ_eq_upperBranch d hd5 hcarry
      calc
        seamWordSupport (seamGreedyWord (d + 0 + 1)) =
            seamWordSupport
              ((seamAdjacentCut d hd5).above.extend false) := by
          simpa using congrArg seamWordSupport hword
        _ = seamWordSupport (seamAdjacentCut d hd5).above :=
          seamWordSupport_extend_false (by omega)
            (seamAdjacentCut d hd5).above
        _ = seamWordSupport (seamAdjacentCut d hd5).above ∪
              Finset.Ico (d + 1) (d + 0 + 1) := by
          simp
  | succ q ih =>
      intro hq
      have hqk : q < k := by omega
      have hbranch :=
        seamRightBranch_of_remainder_add_charge_eq
          (s := d + q + 1) (by omega) (by
            simpa only [
              show d + q + 2 = (d + q + 1) + 1 by omega
            ] using hrun q hqk)
      have hword :=
        seamGreedyWord_succ_eq_rightBranch
          (d + q + 1) (by omega) hbranch.1 hbranch.2
      change seamGreedyWord ((d + q + 1) + 1) =
        (seamGreedyWord (d + q + 1)).extend true at hword
      have ihq := ih (by omega)
      calc
        seamWordSupport (seamGreedyWord (d + (q + 1) + 1)) =
            seamWordSupport
              ((seamGreedyWord (d + q + 1)).extend true) := by
          simpa only [
            show d + (q + 1) + 1 = (d + q + 1) + 1 by omega
          ] using congrArg seamWordSupport hword
        _ = insert (d + q + 1)
              (seamWordSupport (seamGreedyWord (d + q + 1))) :=
          seamWordSupport_extend_true (by omega)
            (seamGreedyWord (d + q + 1))
        _ = insert (d + q + 1)
              (seamWordSupport (seamAdjacentCut d hd5).above ∪
                Finset.Ico (d + 1) (d + q + 1)) := by
          rw [ihq]
        _ = seamWordSupport (seamAdjacentCut d hd5).above ∪
              Finset.Ico (d + 1) (d + (q + 1) + 1) := by
          ext e
          by_cases he :
              e ∈ seamWordSupport (seamAdjacentCut d hd5).above
          · simp [he]
          · simp only [Finset.mem_insert, Finset.mem_union,
              Finset.mem_Ico, he, false_or]
            omega

/-- Exact actual pulse split into the reset support and the consecutive
right-run suffix. -/
theorem seamUpperThenRightRun_belowPulse_eq_base_add_suffix
    {d k q : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hq : q ≤ k) :
    (seamAdjacentCut (d + q + 1) (by omega)).belowPulse =
      (∑ e ∈ seamWordSupport (seamAdjacentCut d hd5).above,
        rowPulse (d + q + 1) e) +
      ∑ e ∈ Finset.Ico (d + 1) (d + q + 1),
        rowPulse (d + q + 1) e := by
  classical
  have hsupport :=
    seamUpperThenRightRun_support hd5 hcarry hrun q hq
  have hdisjoint :
      Disjoint (seamWordSupport (seamAdjacentCut d hd5).above)
        (Finset.Ico (d + 1) (d + q + 1)) := by
    apply Finset.disjoint_left.mpr
    intro e heU heIco
    have heBelow := seamWordSupport_below heU
    have heLower := (Finset.mem_Ico.mp heIco).1
    omega
  change wordPulse (d + q + 1)
      (seamGreedyWord (d + q + 1)).toNatWord = _
  rw [wordPulse_eq_sum_seamWordSupport, hsupport,
    Finset.sum_union hdisjoint]

/-- Before the two-thirds crossing, the ranks filled after the upper reset
are pulse-invisible, so the actual below pulse is carried by the fixed reset
support alone. -/
theorem seamUpperThenRightRun_belowPulse_eq_resetSupportSum
    {d k q : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hq : q ≤ k) (hlate : 2 * (d + q + 1) < 3 * d) :
    (seamAdjacentCut (d + q + 1) (by omega)).belowPulse =
      ∑ e ∈ seamWordSupport (seamAdjacentCut d hd5).above,
        rowPulse (d + q + 1) e := by
  have hsplit := seamUpperThenRightRun_belowPulse_eq_base_add_suffix
    hd5 hcarry hrun hq
  have hsuffix :
      (∑ e ∈ Finset.Ico (d + 1) (d + q + 1),
        rowPulse (d + q + 1) e) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have heIco := Finset.mem_Ico.mp he
    exact rowPulse_eq_zero_of_late_strictSuffix
      (s := d + q + 1) (d := d) (e := e)
      (by omega) (by omega) (by omega) hlate
  rw [hsplit, hsuffix, add_zero]

/-- The exact no-stall inequality after an actual upper/right run.  Unlike
the former sufficient width `2(d+k)`, this criterion loses no pulse data:
the terminal row escapes precisely when its row index plus the accumulated
support charge fits inside the scaled critical gap. -/
theorem seamUpperThenRightRun_row_le_remainder_iff_exactCriticalGap
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    d + k + 1 ≤ seamIntegerGreedyRemainder (d + k + 1) ↔
      affineRightRunCharge
            (fun j ↦
              (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k +
          (d + k + 1) ≤
        4 ^ k *
          (2 ^ (d - k + 1) - seamUpperResetCharge d hd5) := by
  have hexact :=
    seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
      hd5 hk hcarry hrun
  omega

/-! ## Backward support recovery at a late upper reset -/

/-- The quotient-digit packet accumulated by a fixed finite support while
its truncated Mersenne weights are transported through `k` rows. -/
def fixedSupportPulseCharge (b : ℕ) (A : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      4 * fixedSupportPulseCharge b A k +
        ∑ e ∈ A, rowPulse (b + k) e

/-- Exact base-four transport of a fixed support.  Unlike a right-run
cylinder, this identity does not assume that `A` is the greedy support at
the intermediate rows. -/
theorem sum_truncatedMersenneWeight_fixedSupport_iterate
    {b k : ℕ} {A : Finset ℕ} (hb2 : 2 ≤ b)
    (hA : ∀ e ∈ A, 2 ≤ e) :
    (∑ e ∈ A, truncatedMersenneWeight (b + k) e) =
      4 ^ k * (∑ e ∈ A, truncatedMersenneWeight b e) +
        fixedSupportPulseCharge b A k := by
  induction k with
  | zero => simp [fixedSupportPulseCharge]
  | succ k ih =>
      calc
        (∑ e ∈ A, truncatedMersenneWeight (b + (k + 1)) e) =
            ∑ e ∈ A,
              (4 * truncatedMersenneWeight (b + k) e +
                rowPulse (b + k) e) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [show b + (k + 1) = (b + k) + 1 by omega,
            truncatedMersenneWeight_succ (by omega) (hA e he)]
        _ = 4 * (∑ e ∈ A,
              truncatedMersenneWeight (b + k) e) +
            ∑ e ∈ A, rowPulse (b + k) e := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        _ = 4 * (4 ^ k * (∑ e ∈ A,
              truncatedMersenneWeight b e) +
              fixedSupportPulseCharge b A k) +
            ∑ e ∈ A, rowPulse (b + k) e := by
          rw [ih]
        _ = 4 ^ (k + 1) * (∑ e ∈ A,
              truncatedMersenneWeight b e) +
            fixedSupportPulseCharge b A (k + 1) := by
          rw [fixedSupportPulseCharge, pow_succ]
          ring

/-- If the support at row `B+k` consists of a fixed prefix below `B`
together with every rank added after `B`, then the actual greedy support at
row `B` is exactly that prefix.  The proof peels the true terminal suffix
backwards one row at a time. -/
theorem seamGreedyWord_support_eq_base_of_full_suffix
    {B k : ℕ} {u : Finset ℕ} (hB5 : 5 ≤ B)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < B)
    (hsupp : seamWordSupport (seamGreedyWord (B + k)) =
      u ∪ Finset.Ico B (B + k)) :
    seamWordSupport (seamGreedyWord B) = u := by
  revert hsupp
  induction k with
  | zero =>
      intro hsupp
      simpa using hsupp
  | succ k ih =>
      intro hsupp
      let s := B + k
      have hs5 : 5 ≤ s := by
        dsimp [s]
        omega
      have htop : s ∈ seamWordSupport (seamGreedyWord (s + 1)) := by
        rw [show s + 1 = B + (k + 1) by omega, hsupp]
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩))
      have hterminal :
          SeamRowWord.terminal (by omega)
              (seamGreedyWord (s + 1)) = true := by
        apply Bool.eq_true_of_not_eq_false
        intro hfalse
        have hnot : s ∉ seamWordSupport (seamGreedyWord (s + 1)) := by
          apply (not_mem_seamWordSupport_iff_false
            (seamGreedyWord (s + 1)) (by omega) (by omega)).2
          simpa [SeamRowWord.terminal] using hfalse
        exact hnot htop
      have hright :
          seamGreedyWord (s + 1) = (seamGreedyWord s).extend true :=
        (seamGreedyWord_succ_eq_extend_true_iff_terminal_true s hs5).2
          hterminal
      have hprev :
          seamWordSupport (seamGreedyWord s) =
            u ∪ Finset.Ico B s := by
        have hsupp' :
            insert s (seamWordSupport (seamGreedyWord s)) =
              u ∪ Finset.Ico B (s + 1) := by
          calc
            insert s (seamWordSupport (seamGreedyWord s)) =
                seamWordSupport ((seamGreedyWord s).extend true) := by
              symm
              exact seamWordSupport_extend_true (by omega)
                (seamGreedyWord s)
            _ = seamWordSupport (seamGreedyWord (s + 1)) := by
              rw [hright]
            _ = u ∪ Finset.Ico B (s + 1) := by
              simpa [s] using hsupp
        ext e
        constructor
        · intro he
          have heFinal :
              e ∈ insert s (seamWordSupport (seamGreedyWord s)) :=
            Finset.mem_insert_of_mem he
          rw [hsupp'] at heFinal
          rcases Finset.mem_union.mp heFinal with heu | heIco
          · exact Finset.mem_union.mpr (Or.inl heu)
          · exact Finset.mem_union.mpr (Or.inr
              (Finset.mem_Ico.mpr
                ⟨(Finset.mem_Ico.mp heIco).1,
                  (seamWordSupport_below he).2⟩))
        · intro he
          have heLt : e < s := by
            rcases Finset.mem_union.mp he with heu | heIco
            · exact (hu e heu).2.trans_le (by omega)
            · exact (Finset.mem_Ico.mp heIco).2
          have heFinal : e ∈ u ∪ Finset.Ico B (s + 1) := by
            rcases Finset.mem_union.mp he with heu | heIco
            · exact Finset.mem_union.mpr (Or.inl heu)
            · exact Finset.mem_union.mpr (Or.inr
                (Finset.mem_Ico.mpr
                  ⟨(Finset.mem_Ico.mp heIco).1, by omega⟩))
          rw [← hsupp'] at heFinal
          rcases Finset.mem_insert.mp heFinal with hEq | hePrev
          · omega
          · exact hePrev
      apply ih
      simpa [s] using hprev

/-- A late largest-false decomposition is therefore already the exact
greedy support one row after its missing boundary rank. -/
theorem exists_lowerPrefix_with_backward_support_of_lateLargestFalse
    {s d : ℕ} (hs5 : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    ∃ u : Finset ℕ,
      (∀ e ∈ u, 2 ≤ e ∧ e < d) ∧
        seamWordSupport (seamGreedyWord (d + 1)) = u ∧
          seamWordSupport (seamGreedyWord s) =
            u ∪ Finset.Ico (d + 1) s := by
  obtain ⟨u, hu, hsupp⟩ :=
    (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
      (seamGreedyWord s) hd.1 hd.2.1).mp hd
  have hdBase5 : 5 ≤ d + 1 := by
    omega
  have hdsucc : d + 1 ≤ s := Nat.succ_le_iff.mpr hd.2.1
  have hrow : d + 1 + (s - (d + 1)) = s :=
    Nat.add_sub_of_le hdsucc
  have hbase := seamGreedyWord_support_eq_base_of_full_suffix
    (B := d + 1) (k := s - (d + 1)) hdBase5
    (by
      intro e he
      exact ⟨(hu e he).1, (hu e he).2.trans (Nat.lt_succ_self d)⟩)
    (by
      rw [hrow]
      exact hsupp)
  exact ⟨u, hu, hbase, hsupp⟩

/-- The fixed reset support gives an exact high-quotient identity linking the
charge at row `s` to the actual greedy remainder at the earlier boundary row
`d+1`.  No branch or hypothetical band assumption is introduced:

`4^(s-d) R_(d+1) + E_s = 2^(s+2) + C + 4^(s-d)(2^(d+1)+4)`.

Here `C` is the accumulated divisor-incidence packet of the fixed upper
support `insert d u`. -/
theorem exists_fixedSupportPulseCharge_backward_identity_of_lateLargestFalse
    {s d : ℕ} (hs5 : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    ∃ u : Finset ℕ,
      (∀ e ∈ u, 2 ≤ e ∧ e < d) ∧
        seamWordSupport (seamGreedyWord (d + 1)) = u ∧
          seamWordSupport (seamGreedyWord s) =
            u ∪ Finset.Ico (d + 1) s ∧
          4 ^ (s - d) * seamIntegerGreedyRemainder (d + 1) +
              seamUpperResetCharge s hs5 =
            2 ^ (s + 2) +
                fixedSupportPulseCharge (d + 1) (insert d u) (s - d) +
              4 ^ (s - d) * (2 ^ (d + 1) + 4) := by
  classical
  obtain ⟨u, hu, hbase, hsupp⟩ :=
    exists_lowerPrefix_with_backward_support_of_lateLargestFalse
      hs5 hd hlate
  have hd3 : 3 ≤ d := by omega
  have hdBase5 : 5 ≤ d + 1 := by omega
  have hdnotu : d ∉ u := by
    intro hdu
    exact (Nat.lt_irrefl d) (hu d hdu).2
  have hA2 : ∀ e ∈ insert d u, 2 ≤ e := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · exact hd.1
    · exact (hu e heu).1
  have hABounds : ∀ e ∈ insert d u, 2 ≤ e ∧ e < s := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · exact ⟨hd.1, hd.2.1⟩
    · exact ⟨(hu e heu).1, (hu e heu).2.trans hd.2.1⟩
  have hgreedy := seamGreedy_weight_add_remainder hdBase5
  rw [wordWeightSum_eq_sum_seamWordSupport, hbase] at hgreedy
  have hnew := truncatedMersenneWeight_newRank (s := d) hd3
  have hbaseTarget :
      seamSubsetTarget (d + 1) +
          truncatedMersenneWeight (d + 1) d =
        2 ^ (2 * d + 1) + 2 ^ (d + 1) + 4 := by
    have hpowle : 2 ^ (d + 1) ≤ 2 ^ (2 * d + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hnewPow : 2 ^ (d + 2) = 2 * 2 ^ (d + 1) := by
      rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
      ring
    rw [hnew, hnewPow]
    unfold seamSubsetTarget
    rw [show 2 * (d + 1) - 1 = 2 * d + 1 by omega]
    omega
  have hbaseAdd :
      (∑ e ∈ insert d u,
          truncatedMersenneWeight (d + 1) e) +
          seamIntegerGreedyRemainder (d + 1) =
        2 ^ (2 * d + 1) + 2 ^ (d + 1) + 4 := by
    rw [Finset.sum_insert hdnotu]
    omega
  have habove :=
    seamAdjacentCut_above_eq_largestSkipUpperWord_of_support
      hs5 hd.1 hu hd.2.1 hsupp hlate
  have hupperSupport :
      seamWordSupport (largestSkipUpperWord s d u) = insert d u := by
    unfold largestSkipUpperWord
    exact seamWordSupport_seamRowWordOfFinset hABounds
  have hcapacity := (seamAdjacentCut s hs5).capacity_add_overshoot
  change seamSubsetTarget s + (seamAdjacentCut s hs5).overshoot =
    wordWeightSum s (seamAdjacentCut s hs5).above.toNatWord at hcapacity
  rw [habove, wordWeightSum_eq_sum_seamWordSupport,
    hupperSupport] at hcapacity
  have hpulse :
      (seamAdjacentCut s hs5).abovePulse =
        ∑ e ∈ insert d u, rowPulse s e := by
    change wordPulse s (seamAdjacentCut s hs5).above.toNatWord = _
    rw [habove, wordPulse_eq_sum_seamWordSupport, hupperSupport]
  have hstepRaw :=
    sum_truncatedMersenneWeight_fixedSupport_iterate
      (b := s) (k := 1) (A := insert d u) (by omega) hA2
  have hstep :
      (∑ e ∈ insert d u, truncatedMersenneWeight (s + 1) e) =
        4 * (∑ e ∈ insert d u, truncatedMersenneWeight s e) +
          ∑ e ∈ insert d u, rowPulse s e := by
    simpa [fixedSupportPulseCharge] using hstepRaw
  have hpowle : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsidePow : 2 ^ (s + 2) = 4 * 2 ^ s := by
    rw [show s + 2 = s + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  have htopPow : 4 * 2 ^ (2 * s - 1) = 2 ^ (2 * s + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have htargetScaled :
      4 * seamSubsetTarget s + 2 ^ (s + 2) = 2 ^ (2 * s + 1) := by
    unfold seamSubsetTarget
    omega
  have hupperNext :
      (∑ e ∈ insert d u,
          truncatedMersenneWeight (s + 1) e) + 2 ^ (s + 2) =
        2 ^ (2 * s + 1) + seamUpperResetCharge s hs5 := by
    unfold seamUpperResetCharge
    omega
  have hiterateRaw :=
    sum_truncatedMersenneWeight_fixedSupport_iterate
      (b := d + 1) (k := s - d) (A := insert d u)
      (by omega) hA2
  have hdle : d ≤ s := hd.2.1.le
  have hrow : d + 1 + (s - d) = s + 1 := by
    calc
      d + 1 + (s - d) = d + (s - d) + 1 := by ac_rfl
      _ = s + 1 := by rw [Nat.add_sub_of_le hdle]
  have hiterate :
      (∑ e ∈ insert d u, truncatedMersenneWeight (s + 1) e) =
        4 ^ (s - d) *
            (∑ e ∈ insert d u,
              truncatedMersenneWeight (d + 1) e) +
          fixedSupportPulseCharge (d + 1) (insert d u) (s - d) := by
    simpa only [hrow] using hiterateRaw
  have hfour : 4 ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hscale :
      4 ^ (s - d) * 2 ^ (2 * d + 1) = 2 ^ (2 * s + 1) := by
    rw [hfour, ← pow_add]
    congr 1
    omega
  have hbaseScaled :
      4 ^ (s - d) *
            (∑ e ∈ insert d u,
              truncatedMersenneWeight (d + 1) e) +
          4 ^ (s - d) * seamIntegerGreedyRemainder (d + 1) =
        2 ^ (2 * s + 1) +
          4 ^ (s - d) * (2 ^ (d + 1) + 4) := by
    calc
      4 ^ (s - d) *
              (∑ e ∈ insert d u,
                truncatedMersenneWeight (d + 1) e) +
            4 ^ (s - d) * seamIntegerGreedyRemainder (d + 1) =
          4 ^ (s - d) *
            ((∑ e ∈ insert d u,
                truncatedMersenneWeight (d + 1) e) +
              seamIntegerGreedyRemainder (d + 1)) := by ring
      _ = 4 ^ (s - d) *
            (2 ^ (2 * d + 1) + 2 ^ (d + 1) + 4) := by
          rw [hbaseAdd]
      _ = 4 ^ (s - d) * 2 ^ (2 * d + 1) +
            4 ^ (s - d) * (2 ^ (d + 1) + 4) := by ring
      _ = 2 ^ (2 * s + 1) +
            4 ^ (s - d) * (2 ^ (d + 1) + 4) := by rw [hscale]
  refine ⟨u, hu, hbase, hsupp, ?_⟩
  omega

/-- A largest false rank either yields a strict earlier boundary row or is
the terminal rank `s-1`.  The high-quotient identity above applies in both
cases; only the first disjunct is a genuine descent. -/
theorem largestFalse_backwardRow_lt_or_terminal
    {s d : ℕ} (hd : IsLargestFalseRank (seamGreedyWord s) d) :
    d + 1 < s ∨ d + 1 = s :=
  lt_or_eq_of_le (Nat.succ_le_iff.mpr hd.2.1)

/-- The reduced global producer: at every late upper reset, certify only the
nearest dyadic boundary above its charge. -/
def SeamUpperResetCriticalBandEscape : Prop :=
  ∀ (d : ℕ) (hd5 : 5 ≤ d), 13 ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
      ∃ j : ℕ,
        CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j ∧
          seamUpperResetCharge d hd5 + 2 * (d + j) ≤
            2 ^ (d - j + 1)

/-- The critical-band producer is logically equivalent to the original
all-band producer. -/
theorem seamUpperResetCriticalBandEscape_iff :
    SeamUpperResetCriticalBandEscape ↔ SeamUpperResetDyadicBandEscape := by
  constructor
  · intro hcritical d hd5 hd13 hcarry j hjd
    have hall := (seamUpperResetBand_iff_exists_critical hd5 hcarry).mpr
      (hcritical d hd5 hd13 hcarry)
    simpa [seamUpperResetCharge] using hall j hjd
  · intro hall d hd5 hd13 hcarry
    apply (seamUpperResetBand_iff_exists_critical hd5 hcarry).mp
    intro j hjd
    simpa [seamUpperResetCharge] using hall d hd5 hd13 hcarry j hjd

/-- Endpoint consumer through the exact critical-band reduction. -/
theorem half_mem_mersenneAchievementSet_of_upperResetCriticalBandEscape
    (hcritical : SeamUpperResetCriticalBandEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape
  exact seamUpperResetCriticalBandEscape_iff.mp hcritical

end Erdos249257.HalfUpperResetCriticalBand
