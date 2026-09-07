import Erdos257PeriodNoncollapse.HalfCylinderMiddleCarryLowerBound
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

namespace Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand

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

/-- A carry row lies strictly above the half-cylinder boundary.  This is a
pure adjacent-cut consequence: separation gives
`gap ≤ remainder + overshoot`, while the carry condition gives
`4 * overshoot ≤ gap`.  For the seam gap `2^(s+1)`, those two inequalities
force `2^s < remainder`.

This lower bound is deliberately stated at the source row.  Combined with
the exact upper/right cylinder below, it rules out a second upper reset after
an arbitrary intervening right run, rather than only at the immediate next
row. -/
theorem seamSuccessorCarries_remainder_gt_pow
    {s : ℕ} (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    2 ^ s < seamIntegerGreedyRemainder s := by
  classical
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
  have hfourO : 4 * K.overshoot ≤ F.gap := by
    change 4 * K.overshoot + K.abovePulse ≤ F.gap at hcarry
    omega
  change 2 ^ (s + 1) ≤
      (seamAdjacentCut s hs).remainder +
        (seamAdjacentCut s hs).overshoot at hgapRO
  change 4 * (seamAdjacentCut s hs).overshoot ≤ 2 ^ (s + 1) at hfourO
  rw [seamAdjacentCut_remainder hs] at hgapRO
  have hpow : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by
    rw [pow_succ]
    ring
  rw [hpow] at hgapRO hfourO
  have hpos : 0 < (2 : ℕ) ^ s := pow_pos (by norm_num) s
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

/-! ## Actual-run position inside the critical band

The exact cylinder already fixes one side of the experimentally observed
critical-index identity.  A right run cannot pass the smallest dyadic
boundary still above the reset charge.  Reaching that boundary exactly is
therefore reduced to the one missing lower-bound comparison with the next
smaller power; no terminal-branch hypothesis is hidden here.
-/

/-- An actual upper/right run cannot be longer than the critical dyadic
index of its reset charge. -/
theorem seamUpperThenRightRun_length_le_criticalIndex
    {d k j : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hcritical :
      CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j) :
    k ≤ j := by
  let E := seamUpperResetCharge d hd5
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E +
      affineRightRunCharge
        (fun q ↦
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k =
      2 ^ (d + k + 1) at hcylinder
  have hfactor :
      4 ^ k * 2 ^ (d - k + 1) = 2 ^ (d + k + 1) := by
    rw [show 4 ^ k = 2 ^ (2 * k) by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
    congr 1
    omega
  have hweighted : 4 ^ k * E ≤ 2 ^ (d + k + 1) := by
    omega
  have hE : E ≤ 2 ^ (d - k + 1) := by
    rw [← hfactor] at hweighted
    exact Nat.le_of_mul_le_mul_left hweighted (pow_pos (by norm_num) k)
  by_contra hnot
  have hjk : j < k := Nat.lt_of_not_ge hnot
  rcases hcritical with ⟨hjd, _hEj, hjnext⟩
  rcases hjnext with rfl | hjnext
  · omega
  · have hexp : d - k + 1 ≤ d - (j + 1) + 1 := by omega
    have hpow : 2 ^ (d - k + 1) ≤ 2 ^ (d - (j + 1) + 1) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    omega

/-- Since the run length is always at most the critical index, equality is
equivalent to crossing the immediately lower dyadic boundary (with the
terminal index handled separately).  This is the exact remaining statement
behind the computed `critical_index = right_run_length` pattern. -/
theorem seamUpperThenRightRun_criticalIndex_eq_iff_lowerBoundary_lt
    {d k j : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hcritical :
      CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j) :
    j = k ↔
      k = d ∨
        2 ^ (d - (k + 1) + 1) < seamUpperResetCharge d hd5 := by
  constructor
  · intro hjk
    subst j
    exact hcritical.2.2
  · intro hlower
    have hkj := seamUpperThenRightRun_length_le_criticalIndex
      hd5 hk hcarry hrun hcritical
    have hjk : j ≤ k := by
      rcases hlower with hkd | hlower
      · simpa [hkd] using hcritical.1
      · by_contra hnot
        have hkj' : k < j := Nat.lt_of_not_ge hnot
        have hexp : d - j + 1 ≤ d - (k + 1) + 1 := by omega
        have hpow : 2 ^ (d - j + 1) ≤ 2 ^ (d - (k + 1) + 1) :=
          Nat.pow_le_pow_right (by norm_num) hexp
        exact (not_lt_of_ge (hcritical.2.1.trans hpow)) hlower
    exact Nat.le_antisymm hjk hkj

/-- The crude `k ≤ d` cylinder bound is never attained.  At `k=d`, the
reset charge contributes at least `4^d * 4 = 2^(2d+2)`, already twice the
entire cylinder capacity `2^(2d+1)`.  Keeping the strict form removes the
terminal-index disjunct from the critical-band identity below. -/
theorem seamUpperThenRightRun_length_lt_resetRow
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) :
    k < d := by
  have hle := seamUpperThenRightRun_length_le_resetRow hd5 hcarry hrun
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  let E := seamUpperResetCharge d hd5
  change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E +
      affineRightRunCharge
        (fun q ↦
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k =
      2 ^ (d + k + 1) at hcylinder
  have hover : 1 ≤ (seamAdjacentCut d hd5).overshoot := by
    unfold PerturbedFamily.AdjacentCut.overshoot
    have habove := (seamAdjacentCut d hd5).above_strict
    omega
  have hE : 4 ≤ E := by
    dsimp [E, seamUpperResetCharge]
    omega
  by_contra hnot
  have hkd : k = d := by omega
  subst k
  have hpow : 2 ^ (d + d + 1) < 4 ^ d * 4 := by
    calc
      2 ^ (d + d + 1) < 2 ^ (2 * (d + 1)) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = 4 ^ d * 4 := by
        rw [show (4 : ℕ) ^ d = 2 ^ (2 * d) by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]]
        rw [show 2 * (d + 1) = 2 * d + 2 by omega, pow_add]
        norm_num
  have hweighted : 4 ^ d * 4 ≤ 4 ^ d * E :=
    Nat.mul_le_mul_left _ hE
  omega

/-- Upper resets alternate with middle resets across whole reset blocks.  More
precisely, after an upper reset and any finite run satisfying the exact right
recurrence, the terminal row cannot itself carry.  The exact cylinder puts
its remainder at or below `2^(d+k+1)`, whereas every carry row is strictly
above that boundary by `seamSuccessorCarries_remainder_gt_pow`. -/
theorem seamUpperThenRightRun_terminal_not_successorCarries
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) :
    ¬ (seamAdjacentCut (d + k + 1) (by omega)).successorCarries := by
  intro hterminal
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  have hle :
      seamIntegerGreedyRemainder (d + k + 1) ≤ 2 ^ (d + k + 1) := by
    omega
  have hgt := seamSuccessorCarries_remainder_gt_pow
    (s := d + k + 1) (by omega) hterminal
  omega

/-- Consequently, if the terminal row of an upper/right block is a reset at
all, it is the middle reset. -/
theorem seamUpperThenRightRun_terminal_isMiddle
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hreset : SeamGreedyUpperOrMiddleAt (d + k + 1) (by omega)) :
    ¬ (seamAdjacentCut (d + k + 1) (by omega)).successorCarries ∧
      4 * (seamAdjacentCut (d + k + 1) (by omega)).remainder +
            (seamPerturbedFamily (d + k + 1) (by omega)).gap -
            (seamAdjacentCut (d + k + 1) (by omega)).belowPulse <
          (seamAdjacentCut (d + k + 1) (by omega)).terminalWeight := by
  have hncarry := seamUpperThenRightRun_terminal_not_successorCarries
    hd5 hcarry hrun
  rcases hreset with hterminalCarry | hmiddle
  · exact (hncarry hterminalCarry).elim
  · exact hmiddle

/-- **Endpoint form of the critical-index identity.**  For an actual upper
reset followed by `k` right recurrences, the run reaches its unique critical
dyadic index exactly when the terminal remainder together with the complete
right-run pulse packet lies below the half-cylinder boundary.

Thus the computed `critical_index = right_run_length` law is not a diffuse
property of the whole orbit.  Its exact missing input is the single endpoint
inequality displayed on the right. -/
theorem seamUpperThenRightRun_criticalIndex_eq_iff_endpointPacket_lt_half
    {d k j : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hcritical :
      CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j) :
    j = k ↔
      seamIntegerGreedyRemainder (d + k + 1) +
          affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k <
        2 ^ (d + k) := by
  let E := seamUpperResetCharge d hd5
  let C := affineRightRunCharge
    (fun q ↦ (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k
  have hklt := seamUpperThenRightRun_length_lt_resetRow hd5 hcarry hrun
  have hkle : k ≤ d := hklt.le
  have hlower : j = k ↔ 2 ^ (d - k) < E := by
    have hiff := seamUpperThenRightRun_criticalIndex_eq_iff_lowerBoundary_lt
      hd5 hkle hcarry hrun hcritical
    have hexp : d - (k + 1) + 1 = d - k := by omega
    simpa [E, hexp, Nat.ne_of_lt hklt] using hiff
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E + C =
      2 ^ (d + k + 1) at hcylinder
  have hfactor : 4 ^ k * 2 ^ (d - k) = 2 ^ (d + k) := by
    rw [show 4 ^ k = 2 ^ (2 * k) by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
    congr 1
    omega
  have hdouble : 2 ^ (d + k + 1) = 2 * 2 ^ (d + k) := by
    rw [pow_succ]
    ring
  rw [hlower]
  constructor
  · intro hE
    have hscaled : 2 ^ (d + k) < 4 ^ k * E := by
      rw [← hfactor]
      exact Nat.mul_lt_mul_of_pos_left hE (pow_pos (by norm_num) k)
    omega
  · intro hpacket
    by_contra hnot
    have hEle : E ≤ 2 ^ (d - k) := Nat.le_of_not_gt hnot
    have hscaled : 4 ^ k * E ≤ 2 ^ (d + k) := by
      rw [← hfactor]
      exact Nat.mul_le_mul_left _ hEle
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

/-! ## Critical-gap pullback through the preceding false rank

The backward identity contains a cancellation which is invisible in the
forward cylinder.  Once the dyadic boundary is moved to the left-hand side,
the entire fixed-support pulse packet disappears into a power-of-four
multiple of one earlier-row coordinate.  Thus a narrow upper-reset danger
band is not a new local accident: it pulls back exactly to an earlier seam
remainder near an explicit difference of dyadic boundaries.
-/

/-- The signed earlier-row coordinate obtained by pulling the critical gap
at row `s` back through a largest false rank `d`. -/
def seamEarlierCriticalPullbackCoordinate (s d k : ℕ) : ℤ :=
  (seamIntegerGreedyRemainder (d + 1) : ℤ) -
      ((2 ^ (d + 1) : ℕ) : ℤ) - 4 +
    ((2 ^ ((2 * d + 1) - (s + k)) : ℕ) : ℤ) -
      ((2 ^ ((2 * d + 2) - s) : ℕ) : ℤ)

/-- The future right length does only one thing to the pulled-back
coordinate: it subtracts the initial segment of a dyadic staircase.  With
`a = 2*d+1-s`,

`Q_k = Q_0 - 2^a + 2^(a-k)`.

Thus every dangerous upper/right endpoint is an earlier middle coordinate
lying in a linear-width window immediately above one explicit dyadic
staircase. -/
theorem pullbackCoordinate_eq_base_sub_dyadicStaircase
    {s d k : ℕ} :
    seamEarlierCriticalPullbackCoordinate s d k =
      seamEarlierCriticalPullbackCoordinate s d 0 -
        (((2 ^ ((2 * d + 1) - s) : ℕ) : ℤ)) +
        (((2 ^ (((2 * d + 1) - s) - k) : ℕ) : ℤ)) := by
  have hexp :
      (2 * d + 1) - (s + k) = ((2 * d + 1) - s) - k := by
    omega
  unfold seamEarlierCriticalPullbackCoordinate
  simp only [Nat.add_zero]
  rw [hexp]
  ring

/-- Pure algebra behind the critical-gap pullback.  The two exponent
hypotheses are precisely what is needed to factor both dyadic boundaries by
`4^(s-d)` without truncated-exponent loss. -/
theorem backwardCriticalDistance_eq_fourPow_mul_pullback
    {s d k E C R : ℕ} (hds : d ≤ s) (hk : k ≤ s)
    (hfactor : s + k ≤ 2 * d + 1)
    (hbackward :
      4 ^ (s - d) * R + E =
        2 ^ (s + 2) + C +
          4 ^ (s - d) * (2 ^ (d + 1) + 4)) :
    (((2 ^ (s - k + 1) : ℕ) : ℤ) - (E : ℤ) + (C : ℤ)) =
      ((4 ^ (s - d) : ℕ) : ℤ) *
        ((R : ℤ) - ((2 ^ (d + 1) : ℕ) : ℤ) - 4 +
          ((2 ^ ((2 * d + 1) - (s + k)) : ℕ) : ℤ) -
            ((2 ^ ((2 * d + 2) - s) : ℕ) : ℤ)) := by
  have hfour : 4 ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hsd : s - d + d = s := Nat.sub_add_cancel hds
  have hsk : s - k + k = s := Nat.sub_add_cancel hk
  have hcriticalExp :
      (2 * d + 1) - (s + k) + (s + k) = 2 * d + 1 :=
    Nat.sub_add_cancel hfactor
  have htopLe : s ≤ 2 * d + 2 := by omega
  have htopExp : (2 * d + 2) - s + s = 2 * d + 2 :=
    Nat.sub_add_cancel htopLe
  have hcriticalScale :
      4 ^ (s - d) * 2 ^ ((2 * d + 1) - (s + k)) =
        2 ^ (s - k + 1) := by
    rw [hfour, ← pow_add]
    congr 1
    omega
  have htopScale :
      4 ^ (s - d) * 2 ^ ((2 * d + 2) - s) = 2 ^ (s + 2) := by
    rw [hfour, ← pow_add]
    congr 1
    omega
  have hbackwardZ :
      (((4 ^ (s - d) : ℕ) : ℤ) * (R : ℤ)) + (E : ℤ) =
        ((2 ^ (s + 2) : ℕ) : ℤ) + (C : ℤ) +
          ((4 ^ (s - d) : ℕ) : ℤ) *
            (((2 ^ (d + 1) : ℕ) : ℤ) + 4) := by
    exact_mod_cast hbackward
  have hcriticalScaleZ :
      (((4 ^ (s - d) : ℕ) : ℤ) *
          ((2 ^ ((2 * d + 1) - (s + k)) : ℕ) : ℤ)) =
        ((2 ^ (s - k + 1) : ℕ) : ℤ) := by
    exact_mod_cast hcriticalScale
  have htopScaleZ :
      (((4 ^ (s - d) : ℕ) : ℤ) *
          ((2 ^ ((2 * d + 2) - s) : ℕ) : ℤ)) =
        ((2 ^ (s + 2) : ℕ) : ℤ) := by
    exact_mod_cast htopScale
  ring_nf at hbackwardZ hcriticalScaleZ htopScaleZ ⊢
  omega

/-- At a late largest-false row, the exact fixed-support packet therefore
pulls every admissible critical distance back to the earlier seam
coordinate.  This is the recursive descent identity selected by the exact
upper/right experiment. -/
theorem exists_backwardCriticalDistance_pullback_of_lateLargestFalse
    {s d k : ℕ} (hs5 : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hk : k ≤ s)
    (hfactor : s + k ≤ 2 * d + 1) :
    ∃ u : Finset ℕ,
      (∀ e ∈ u, 2 ≤ e ∧ e < d) ∧
        seamWordSupport (seamGreedyWord (d + 1)) = u ∧
          seamWordSupport (seamGreedyWord s) =
            u ∪ Finset.Ico (d + 1) s ∧
          (((2 ^ (s - k + 1) : ℕ) : ℤ) -
              (seamUpperResetCharge s hs5 : ℤ) +
            (fixedSupportPulseCharge
              (d + 1) (insert d u) (s - d) : ℤ)) =
            ((4 ^ (s - d) : ℕ) : ℤ) *
              seamEarlierCriticalPullbackCoordinate s d k := by
  obtain ⟨u, hu, hbase, hsupp, hbackward⟩ :=
    exists_fixedSupportPulseCharge_backward_identity_of_lateLargestFalse
      hs5 hd hlate
  refine ⟨u, hu, hbase, hsupp, ?_⟩
  unfold seamEarlierCriticalPullbackCoordinate
  exact backwardCriticalDistance_eq_fourPow_mul_pullback
    hd.2.1.le hk hfactor hbackward

/-- **Backward middle-barrier theorem.**  A late upper reset cannot have
arrived from a small earlier successor remainder.  Pulling back the top
critical boundary (`k=0`) makes the two residual dyadic powers consecutive,
and positivity of the current upper cylinder gives the explicit bound

`2^(d+1) + 4 + 2^((2d+1)-s) ≤ R_(d+1)`.

This is the first genuinely recursive lower bound on the upper-reset socket:
the current reset forces an exponential surplus at its preceding false
rank. -/
theorem lateUpperReset_previousRemainder_ge_dyadicBarrier
    {s d : ℕ} (hs5 : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcarry : (seamAdjacentCut s hs5).successorCarries) :
    2 ^ (d + 1) + 4 + 2 ^ ((2 * d + 1) - s) ≤
      seamIntegerGreedyRemainder (d + 1) := by
  have hfactor : s + 0 ≤ 2 * d + 1 := by omega
  obtain ⟨u, _hu, _hbase, _hsupp, hpull⟩ :=
    exists_backwardCriticalDistance_pullback_of_lateLargestFalse
      hs5 hd hlate (k := 0) (by omega) hfactor
  simp only [Nat.sub_zero] at hpull
  have hcharge : seamUpperResetCharge s hs5 ≤ 2 ^ (s + 1) :=
    seamUpperResetCharge_le hs5 hcarry
  have hleftNonneg :
      0 ≤ (((2 ^ (s + 1) : ℕ) : ℤ) -
          (seamUpperResetCharge s hs5 : ℤ) +
        (fixedSupportPulseCharge
          (d + 1) (insert d u) (s - d) : ℤ)) := by
    have hchargeZ :
        (seamUpperResetCharge s hs5 : ℤ) ≤
          ((2 ^ (s + 1) : ℕ) : ℤ) := by
      exact_mod_cast hcharge
    exact add_nonneg (sub_nonneg.mpr hchargeZ) (by positivity)
  have hpowPos : 0 < ((4 ^ (s - d) : ℕ) : ℤ) := by positivity
  have hcoordinateNonneg :
      0 ≤ seamEarlierCriticalPullbackCoordinate s d 0 := by
    by_contra hnot
    have hneg : seamEarlierCriticalPullbackCoordinate s d 0 < 0 :=
      lt_of_not_ge hnot
    have hprodNeg :
        ((4 ^ (s - d) : ℕ) : ℤ) *
            seamEarlierCriticalPullbackCoordinate s d 0 < 0 :=
      mul_neg_of_pos_of_neg hpowPos hneg
    omega
  have hsmallExpAdd :
      (2 * d + 1) - s + s = 2 * d + 1 :=
    Nat.sub_add_cancel (by omega)
  have hlargeExpAdd :
      (2 * d + 2) - s + s = 2 * d + 2 :=
    Nat.sub_add_cancel (by omega)
  have hlargeExp : (2 * d + 2) - s = (2 * d + 1) - s + 1 := by
    omega
  have hlargePow :
      2 ^ ((2 * d + 2) - s) =
        2 * 2 ^ ((2 * d + 1) - s) := by
    rw [hlargeExp, pow_succ]
    ring
  have hlargePowZ :
      (((2 ^ ((2 * d + 2) - s) : ℕ) : ℤ)) =
        2 * (((2 ^ ((2 * d + 1) - s) : ℕ) : ℤ)) := by
    exact_mod_cast hlargePow
  unfold seamEarlierCriticalPullbackCoordinate at hcoordinateNonneg
  simp only [Nat.add_zero] at hcoordinateNonneg
  rw [hlargePowZ] at hcoordinateNonneg
  have hbarrierZ :
      (((2 ^ (d + 1) : ℕ) : ℤ) + 4 +
          ((2 ^ ((2 * d + 1) - s) : ℕ) : ℤ)) ≤
        (seamIntegerGreedyRemainder (d + 1) : ℤ) := by
    omega
  exact_mod_cast hbarrierZ

/-- Consequently, every late upper reset is preceded (at its largest false
rank) by a **middle** producer, never by another upper producer.  This turns
the formerly isolated upper-reset band into a recursive middle-to-upper
block. -/
theorem lateUpperReset_previousProducer_isMiddle
    {s d : ℕ} (hs13 : 13 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    ¬ (seamAdjacentCut d (by omega)).successorCarries ∧
      4 * (seamAdjacentCut d (by omega)).remainder +
            (seamPerturbedFamily d (by omega)).gap -
            (seamAdjacentCut d (by omega)).belowPulse <
        (seamAdjacentCut d (by omega)).terminalWeight := by
  obtain ⟨u, hu, hbase, _hsupp⟩ :=
    exists_lowerPrefix_with_backward_support_of_lateLargestFalse
      (s := s) (d := d) (by omega) hd hlate
  have hdnot : d ∉ seamWordSupport (seamGreedyWord (d + 1)) := by
    rw [hbase]
    intro hdu
    exact (Nat.lt_irrefl d) (hu d hdu).2
  have hfalse :
      SeamRowWord.terminal (by omega) (seamGreedyWord (d + 1)) = false :=
    (not_mem_seamWordSupport_iff_false
      (seamGreedyWord (d + 1)) (by omega) (by omega)).mp hdnot
  have hUM :=
    (seamGreedy_terminal_false_iff_upperOrMiddle d (by omega)).mp hfalse
  rcases hUM with hupper | hmiddle
  · have hbarrier := lateUpperReset_previousRemainder_ge_dyadicBarrier
      (s := s) (d := d) (by omega) hd hlate hcarry
    have hupperBound :=
      seamUpperBranch_nextRemainder_le_pow (s := d) (by omega) hupper
    have hstrict : 2 ^ (d + 1) <
        seamIntegerGreedyRemainder (d + 1) := by
      have hplus :
          2 ^ (d + 1) < 2 ^ (d + 1) +
            (4 + 2 ^ ((2 * d + 1) - s)) :=
        Nat.lt_add_of_pos_right (by positivity)
      exact lt_of_lt_of_le (by simpa [Nat.add_assoc] using hplus) hbarrier
    exact False.elim ((not_lt_of_ge hupperBound) hstrict)
  · exact hmiddle

/-- From exponent six onward, the dyadic scale dominates eight times its
index.  This elementary estimate is tuned to the late-reset substitution
`a = 2*d+1-s`, where the late inequality gives `d ≤ 2*a`. -/
theorem eight_mul_le_two_pow_of_six_le
    {a : ℕ} (ha6 : 6 ≤ a) :
    8 * a ≤ 2 ^ a := by
  induction a, ha6 using Nat.le_induction with
  | base => norm_num
  | succ a ha6 ih =>
      rw [pow_succ]
      have h8 : 8 ≤ 2 ^ a := by
        calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ a :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- **Late upper resets have row-large middle ancestors.**  Write
`a = 2*d+1-s` for the exponent exposed by the backward pullback.  Lateness
and `s ≥ 13` force `a ≥ 6` and `d ≤ 2*a`, so `4*d ≤ 2^a`.  The backward
barrier and exact middle recurrence force `2^a+4 ≤ 4*R_d`; consequently
`R_d < d` is impossible.

This discharges the row-scale hypothesis of the middle-to-right exponential
barrier for every middle producer that is the ancestor of a late upper
reset. -/
theorem lateUpperReset_previousMiddleRemainder_ge_row
    {s d : ℕ} (hs13 : 13 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    d ≤ seamIntegerGreedyRemainder d := by
  have hmiddle := lateUpperReset_previousProducer_isMiddle
    (s := s) (d := d) hs13 hd hlate hcarry
  have hbarrier := lateUpperReset_previousRemainder_ge_dyadicBarrier
    (s := s) (d := d) (by omega) hd hlate hcarry
  have hadd := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    (s := d) (by omega) hmiddle.1 hmiddle.2
  let a : ℕ := (2 * d + 1) - s
  have hsd : s ≤ 2 * d + 1 := by omega
  have haAdd : a + s = 2 * d + 1 := by
    simpa [a] using Nat.sub_add_cancel hsd
  have ha6 : 6 ≤ a := by omega
  have hda : d ≤ 2 * a := by omega
  have hpow : 8 * a ≤ 2 ^ a :=
    eight_mul_le_two_pow_of_six_le ha6
  have hfourD : 4 * d ≤ 2 ^ a := by omega
  change 2 ^ (d + 1) + 4 + 2 ^ a ≤
    seamIntegerGreedyRemainder (d + 1) at hbarrier
  have hsourceScale : 2 ^ a + 4 ≤
      4 * seamIntegerGreedyRemainder d := by
    omega
  by_contra hnot
  have hsmall : seamIntegerGreedyRemainder d < d :=
    Nat.lt_of_not_ge hnot
  omega

/-- Every filled terminal rank in a finite full suffix is an actual right
branch at its own row.  The proof rebases the existing backwards support
peeling theorem at `t+1`, rather than assuming that a support seen at the
final row was chosen independently of the greedy recursion. -/
theorem seamRightBranch_of_fullSuffix
    {B s t : ℕ} {u : Finset ℕ} (hB5 : 5 ≤ B)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < B)
    (hsupp : seamWordSupport (seamGreedyWord s) =
      u ∪ Finset.Ico B s)
    (hBt : B ≤ t) (hts : t < s) :
    ¬ (seamAdjacentCut t (by omega)).successorCarries ∧
      (seamAdjacentCut t (by omega)).terminalWeight ≤
        4 * (seamAdjacentCut t (by omega)).remainder +
          (seamPerturbedFamily t (by omega)).gap -
          (seamAdjacentCut t (by omega)).belowPulse := by
  classical
  have ht1s : t + 1 ≤ s := by omega
  have hrow : t + 1 + (s - (t + 1)) = s :=
    Nat.add_sub_of_le ht1s
  let v : Finset ℕ := u ∪ Finset.Ico B (t + 1)
  have hv : ∀ e ∈ v, 2 ≤ e ∧ e < t + 1 := by
    intro e he
    rcases Finset.mem_union.mp he with heu | heIco
    · exact ⟨(hu e heu).1, by have := (hu e heu).2; omega⟩
    · exact ⟨by have := (Finset.mem_Ico.mp heIco).1; omega,
        (Finset.mem_Ico.mp heIco).2⟩
  have hsuppRebased :
      seamWordSupport
          (seamGreedyWord (t + 1 + (s - (t + 1)))) =
        v ∪ Finset.Ico (t + 1) (t + 1 + (s - (t + 1))) := by
    calc
      seamWordSupport
          (seamGreedyWord (t + 1 + (s - (t + 1)))) =
          seamWordSupport (seamGreedyWord s) := by rw [hrow]
      _ = u ∪ Finset.Ico B s := hsupp
      _ = v ∪ Finset.Ico (t + 1) s := by
        dsimp [v]
        ext e
        by_cases heu : e ∈ u
        · simp [heu]
        · simp only [Finset.mem_union, Finset.mem_Ico, heu, false_or]
          omega
      _ = v ∪ Finset.Ico (t + 1)
          (t + 1 + (s - (t + 1))) := by rw [hrow]
  have hbase := seamGreedyWord_support_eq_base_of_full_suffix
    (B := t + 1) (k := s - (t + 1)) (by omega) hv hsuppRebased
  have htop : t ∈ seamWordSupport (seamGreedyWord (t + 1)) := by
    rw [hbase]
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_Ico.mpr ⟨hBt, by omega⟩))
  have hterminal :
      SeamRowWord.terminal (by omega) (seamGreedyWord (t + 1)) = true := by
    apply Bool.eq_true_of_not_eq_false
    intro hfalse
    have hnot : t ∉ seamWordSupport (seamGreedyWord (t + 1)) := by
      apply (not_mem_seamWordSupport_iff_false
        (seamGreedyWord (t + 1)) (by omega) (by omega)).2
      simpa [SeamRowWord.terminal] using hfalse
    exact hnot htop
  have hnotUM : ¬ SeamGreedyUpperOrMiddleAt t (by omega) := by
    intro hUM
    have hfalse :=
      (seamGreedy_terminal_false_iff_upperOrMiddle t (by omega)).2 hUM
    simpa [hfalse] using hterminal
  have hncarry : ¬ (seamAdjacentCut t (by omega)).successorCarries := by
    intro hcarry
    exact hnotUM (Or.inl hcarry)
  refine ⟨hncarry, Nat.le_of_not_gt ?_⟩
  intro hmiddle
  exact hnotUM (Or.inr ⟨hncarry, hmiddle⟩)

/-- **Recursive-block barrier.**  A late upper reset is not an isolated
producer.  Its largest false rank is a row-large middle producer, every row
between that producer and the reset is an actual right successor, and the
standard middle-to-right transport therefore gives

`2^s + s ≤ R_s`

at the upper-reset source itself.  This is an unconditional all-depth
consequence of the late largest-false geometry and the reset branch. -/
theorem lateUpperReset_sourceRemainder_ge_expBarrier
    {s d : ℕ} (hs13 : 13 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    2 ^ s + s ≤ seamIntegerGreedyRemainder s := by
  obtain ⟨u, hu, _hbase, hsupp⟩ :=
    exists_lowerPrefix_with_backward_support_of_lateLargestFalse
      (s := s) (d := d) (by omega) hd hlate
  have hmiddle := lateUpperReset_previousProducer_isMiddle
    (s := s) (d := d) hs13 hd hlate hcarry
  have hrow := lateUpperReset_previousMiddleRemainder_ge_row
    (s := s) (d := d) hs13 hd hlate hcarry
  have hrun : ∀ (t : ℕ) (hdt : d + 1 ≤ t), t < s →
      ¬ (seamAdjacentCut t (by omega)).successorCarries ∧
        (seamAdjacentCut t (by omega)).terminalWeight ≤
          4 * (seamAdjacentCut t (by omega)).remainder +
            (seamPerturbedFamily t (by omega)).gap -
            (seamAdjacentCut t (by omega)).belowPulse := by
    intro t hdt hts
    exact seamRightBranch_of_fullSuffix
      (B := d + 1) (s := s) (t := t) (u := u) (by omega)
      (by
        intro e he
        exact ⟨(hu e he).1, (hu e he).2.trans (Nat.lt_succ_self d)⟩)
      hsupp hdt hts
  have hrow' : d ≤ (seamAdjacentCut d (by omega)).remainder := by
    simpa [seamAdjacentCut_remainder] using hrow
  exact seamMiddleThenRightRun_expBarrier
    (d := d) (s := s) (by omega) (Nat.succ_le_iff.mpr hd.2.1) hrow'
      hmiddle.1 hmiddle.2 hrun

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

end Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand
