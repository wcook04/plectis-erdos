import ErdosProblems.Erdos243.GlobalLcmHeight
import ErdosProblems.Erdos243.SlowRiseBarrier

/-!
# Erdős #243: cumulative-LCM transfer

`GlobalLcmHeight.lean` introduces the cumulative LCM `Λₙ`, the product-cleared
denominator scale `Dₙ`, the overlap debt `Mₙ`, and the exact relocation identity
`Mₙ Λₙ = Dₙ`.  What it does not supply is the transfer of that identity to the
*numerator*: whether the irreversible overlap payments recorded in `Mₙ` are
actually carried by the reciprocal-tail state `Cₙ`.

This module lands that transfer and its consequences.

* `cumulativeOverlapDebt_dvd_tailNumerator`: `Mₙ ∣ Cₙ`, by induction using only
  `ρₙ ∣ Λₙ` and `ρₙ ∣ aₙ`.  No positivity hypothesis is needed: `Mₙ₊₁` divides
  `aₙ Cₙ` and `Dₙ` separately, hence their difference.
* `cumulativeOverlapDebt_dvd_centeredState`: `Mₙ ∣ Eₙ` over `ℤ`.
* The LCM-normalised state `Uₙ = Cₙ / Mₙ`, `Vₙ = Λₙ - (aₙ - 1) Uₙ`, with the
  exact reconstruction `Mₙ Uₙ = Cₙ`, `Mₙ Vₙ = Eₙ` and the exact recurrence
  `ρₙ Uₙ₊₁ = Uₙ - Vₙ`.  `Vₙ` is *defined* by the centred formula, so the
  centring identity is definitional and no truncated division appears in any
  equation.
* `pow_lcmNonFreshCount_le_overlapDebt`: the division-free freshness budget
  `2^{#{j<n : ρⱼ > 1}} ≤ Mₙ`, hence `≤ Cₙ`.  This is the exact finite
  inequality behind "LCM freshness has density one".
* `lcmFresh_pairwiseCoprime`: multipliers at LCM-fresh indices are coprime to
  every earlier multiplier.
* `lcmNonFreshCount_sublinear_of_subexponential` and its exact-orbit
  specialisation: subexponential tail growth makes the non-fresh count
  sublinear in the division-free sense `K · count < n`.
* `no_lcmState_of_freshBlock`: the finite shifted-CRT first-crossing
  contradiction for the LCM-normalised state.  Unlike
  `LcmCriticalBoundary.no_boundedNegative_lcmState_of_oldPrimeSupply` the
  moduli are *whole numbers*, not primes, the block is finite, and the rise
  bound is only required below twice the block product.

Nothing here settles Erdős #243.  The analytic input that would place a block
of `B` pairwise-coprime old moduli all exceeding `B` by time `B + o(B)` is not
formalised.
-/

namespace ErdosProblems.Erdos243

/-! ## The cumulative LCM chain -/

/-- The cumulative LCM grows only by divisibility. -/
theorem cumulativeDigitLcm_dvd_succ (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    cumulativeDigitLcm q a n ∣ cumulativeDigitLcm q a (n + 1) :=
  Nat.dvd_lcm_left _ _

/-- Monotone divisibility of the cumulative LCM. -/
theorem cumulativeDigitLcm_dvd_of_le (q : ℕ) (a : ℕ → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    cumulativeDigitLcm q a m ∣ cumulativeDigitLcm q a n := by
  induction n, hmn using Nat.le_induction with
  | base => exact dvd_rfl
  | succ k _ ih => exact ih.trans (cumulativeDigitLcm_dvd_succ q a k)

/-- Every consumed digit divides every strictly later cumulative LCM. -/
theorem digit_dvd_cumulativeDigitLcm_of_lt (q : ℕ) (a : ℕ → ℕ) {i n : ℕ} (hin : i < n) :
    a i ∣ cumulativeDigitLcm q a n :=
  (Nat.dvd_lcm_right (cumulativeDigitLcm q a i) (a i)).trans
    (cumulativeDigitLcm_dvd_of_le q a (show i + 1 ≤ n by omega))

/-- The cumulative LCM is positive on any orbit with positive seed and
positive multipliers. -/
theorem cumulativeDigitLcm_pos {q : ℕ} {a : ℕ → ℕ} (hq : 0 < q) (ha : ∀ n, 0 < a n) :
    ∀ n, 0 < cumulativeDigitLcm q a n := by
  intro n
  induction n with
  | zero => exact hq
  | succ n ih => exact Nat.lcm_pos ih (ha n)

/-! ## The overlap multiplier -/

/-- The one-step LCM overlap payment `ρₙ = gcd(Λₙ, aₙ)`. -/
def lcmOverlap (q : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.gcd (cumulativeDigitLcm q a n) (a n)

theorem lcmOverlap_def (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    lcmOverlap q a n = Nat.gcd (cumulativeDigitLcm q a n) (a n) := rfl

theorem cumulativeOverlapDebt_succ' (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    cumulativeOverlapDebt q a (n + 1) =
      cumulativeOverlapDebt q a n * lcmOverlap q a n := rfl

theorem lcmOverlap_dvd_lcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    lcmOverlap q a n ∣ cumulativeDigitLcm q a n :=
  Nat.gcd_dvd_left _ _

theorem lcmOverlap_dvd_digit (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    lcmOverlap q a n ∣ a n :=
  Nat.gcd_dvd_right _ _

theorem lcmOverlap_pos {q : ℕ} {a : ℕ → ℕ} (hq : 0 < q) (ha : ∀ n, 0 < a n) (n : ℕ) :
    0 < lcmOverlap q a n :=
  Nat.gcd_pos_of_pos_left (a n) (cumulativeDigitLcm_pos hq ha n)

theorem cumulativeOverlapDebt_pos {q : ℕ} {a : ℕ → ℕ} (hq : 0 < q) (ha : ∀ n, 0 < a n) :
    ∀ n, 0 < cumulativeOverlapDebt q a n := by
  intro n
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
      rw [cumulativeOverlapDebt_succ']
      exact Nat.mul_pos ih (lcmOverlap_pos hq ha n)

/-- The overlap debt divides the product-cleared denominator scale. -/
theorem cumulativeOverlapDebt_dvd_productScale (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    cumulativeOverlapDebt q a n ∣ digitProductScale q a n := by
  rw [← cumulativeOverlapDebt_mul_lcm_eq_productScale q a n]
  exact dvd_mul_right _ _

/-! ## The keystone: overlap debt divides the tail numerator -/

/-- **Exact overlap-debt divisibility.**  Along any exact reciprocal-tail orbit
`Cₙ₊₁ + Dₙ = aₙ Cₙ` whose denominator is the product-cleared scale, the
cumulative overlap debt divides the numerator state: `Mₙ ∣ Cₙ`.

This is the transfer of the relocation identity `Mₙ Λₙ = Dₙ` from the
denominator to the numerator.  The induction needs no positivity, and no
subtraction inside `ℕ` occurs anywhere in it: `Mₙ₊₁ = Mₙ ρₙ` divides `aₙ Cₙ`
and `Dₙ` separately — `ρₙ ∣ aₙ` gives the first, `ρₙ ∣ Λₙ` together with
`Mₙ Λₙ = Dₙ` gives the second — so the additive update `Cₙ₊₁ + Dₙ = aₙ Cₙ`
transfers the divisibility directly.  The base case is `M₀ = 1`. -/
theorem cumulativeOverlapDebt_dvd_tailNumerator
    (q : ℕ) (a C D : ℕ → ℕ)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n) :
    ∀ n, cumulativeOverlapDebt q a n ∣ C n := by
  intro n
  induction n with
  | zero => exact one_dvd _
  | succ n ih =>
      have hMD : cumulativeOverlapDebt q a (n + 1) ∣ D n := by
        rw [hD n, ← cumulativeOverlapDebt_mul_lcm_eq_productScale q a n,
          cumulativeOverlapDebt_succ']
        exact Nat.mul_dvd_mul_left _ (lcmOverlap_dvd_lcm q a n)
      have hMaC : cumulativeOverlapDebt q a (n + 1) ∣ a n * C n := by
        have hprod :
            cumulativeOverlapDebt q a n * lcmOverlap q a n ∣ C n * a n :=
          mul_dvd_mul ih (lcmOverlap_dvd_digit q a n)
        rw [cumulativeOverlapDebt_succ', Nat.mul_comm (a n) (C n)]
        exact hprod
      have htotal : cumulativeOverlapDebt q a (n + 1) ∣ C (n + 1) + D n := by
        rw [hstep n]
        exact hMaC
      exact (Nat.dvd_add_iff_left hMD).mpr htotal

/-- **The centred state carries the same debt.**  `Mₙ ∣ Eₙ` over `ℤ`, where
`Eₙ = Dₙ - (aₙ - 1) Cₙ` is the signed centred error of
`ReciprocalTailRigidity`. -/
theorem cumulativeOverlapDebt_dvd_centeredState
    (q : ℕ) (a C D : ℕ → ℕ)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (n : ℕ) :
    (cumulativeOverlapDebt q a n : ℤ) ∣
      centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ) := by
  have hC : cumulativeOverlapDebt q a n ∣ C n :=
    cumulativeOverlapDebt_dvd_tailNumerator q a C D hD hstep n
  have hDdvd : cumulativeOverlapDebt q a n ∣ D n := by
    rw [hD n]
    exact cumulativeOverlapDebt_dvd_productScale q a n
  simp only [centeredState]
  exact dvd_sub (Int.natCast_dvd_natCast.mpr hDdvd)
    (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hC) _)

/-! ## The LCM-normalised state and its exact system -/

/-- The LCM-normalised numerator `Uₙ = Cₙ / Mₙ`.  Every theorem below consumes
it only through the exact reconstruction `Mₙ Uₙ = Cₙ`, never through the
truncated quotient. -/
def lcmLiftedNumerator (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℕ :=
  C n / cumulativeOverlapDebt q a n

/-- The LCM-normalised centred digit `Vₙ = Λₙ - (aₙ - 1) Uₙ`, defined by the
centred formula so that the centring identity is definitional.  That it really
is `Eₙ / Mₙ` is the content of `lcmLiftedDigit_mul_overlapDebt`. -/
def lcmLiftedDigit (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℤ :=
  (cumulativeDigitLcm q a n : ℤ) -
    ((a n : ℤ) - 1) * (lcmLiftedNumerator q a C n : ℤ)

/-- Exact reconstruction of the numerator from its LCM-normalised form. -/
theorem lcmLiftedNumerator_spec
    (q : ℕ) (a C D : ℕ → ℕ)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (n : ℕ) :
    cumulativeOverlapDebt q a n * lcmLiftedNumerator q a C n = C n :=
  Nat.mul_div_cancel' (cumulativeOverlapDebt_dvd_tailNumerator q a C D hD hstep n)

/-- Integer form of the reconstruction. -/
theorem lcmLiftedNumerator_cast_spec
    (q : ℕ) (a C D : ℕ → ℕ)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (n : ℕ) :
    (cumulativeOverlapDebt q a n : ℤ) * (lcmLiftedNumerator q a C n : ℤ) =
      (C n : ℤ) := by
  exact_mod_cast lcmLiftedNumerator_spec q a C D hD hstep n

/-- **Centring in LCM coordinates**, definitionally `Vₙ = Λₙ - (aₙ - 1) Uₙ`. -/
theorem lcmLifted_centered (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) :
    lcmLiftedDigit q a C n =
      (cumulativeDigitLcm q a n : ℤ) -
        ((a n : ℤ) - 1) * (lcmLiftedNumerator q a C n : ℤ) := rfl

/-- The LCM-normalised digit really is the centred error divided by the
overlap debt: `Mₙ Vₙ = Eₙ`, exactly. -/
theorem lcmLiftedDigit_mul_overlapDebt
    (q : ℕ) (a C D : ℕ → ℕ)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (n : ℕ) :
    (cumulativeOverlapDebt q a n : ℤ) * lcmLiftedDigit q a C n =
      centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ) := by
  have hU := lcmLiftedNumerator_cast_spec q a C D hD hstep n
  have hDZ :
      (cumulativeOverlapDebt q a n : ℤ) * (cumulativeDigitLcm q a n : ℤ) =
        (D n : ℤ) := by
    rw [hD n, ← cumulativeOverlapDebt_mul_lcm_eq_productScale q a n]
    push_cast
    ring
  simp only [lcmLiftedDigit, centeredState]
  calc
    (cumulativeOverlapDebt q a n : ℤ) *
          ((cumulativeDigitLcm q a n : ℤ) -
            ((a n : ℤ) - 1) * (lcmLiftedNumerator q a C n : ℤ)) =
        (cumulativeOverlapDebt q a n : ℤ) * (cumulativeDigitLcm q a n : ℤ) -
          ((a n : ℤ) - 1) *
            ((cumulativeOverlapDebt q a n : ℤ) *
              (lcmLiftedNumerator q a C n : ℤ)) := by ring
    _ = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ) := by rw [hDZ, hU]

/-- **The exact LCM-normalised recurrence** `ρₙ Uₙ₊₁ = Uₙ - Vₙ`.  This is the
pseudo-Euclidean update of `globalLcm_numerator_update` realised on the actual
cumulative-LCM coordinates, with the overlap payment `ρₙ` charged explicitly. -/
theorem lcmLifted_step
    {q : ℕ} {a : ℕ → ℕ} (C D : ℕ → ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (n : ℕ) :
    (lcmOverlap q a n : ℤ) * (lcmLiftedNumerator q a C (n + 1) : ℤ) =
      (lcmLiftedNumerator q a C n : ℤ) - lcmLiftedDigit q a C n := by
  have hMpos : (0 : ℤ) < (cumulativeOverlapDebt q a n : ℤ) := by
    exact_mod_cast cumulativeOverlapDebt_pos hq ha n
  refine mul_left_cancel₀ (ne_of_gt hMpos) ?_
  have hUn := lcmLiftedNumerator_cast_spec q a C D hD hstep n
  have hUsucc := lcmLiftedNumerator_cast_spec q a C D hD hstep (n + 1)
  have hV := lcmLiftedDigit_mul_overlapDebt q a C D hD hstep n
  have hMsucc :
      (cumulativeOverlapDebt q a (n + 1) : ℤ) =
        (cumulativeOverlapDebt q a n : ℤ) * (lcmOverlap q a n : ℤ) := by
    rw [cumulativeOverlapDebt_succ']
    push_cast
    ring
  have hstepZ : (C (n + 1) : ℤ) + (D n : ℤ) = (a n : ℤ) * (C n : ℤ) := by
    exact_mod_cast hstep n
  simp only [centeredState] at hV
  calc
    (cumulativeOverlapDebt q a n : ℤ) *
          ((lcmOverlap q a n : ℤ) * (lcmLiftedNumerator q a C (n + 1) : ℤ)) =
        ((cumulativeOverlapDebt q a n : ℤ) * (lcmOverlap q a n : ℤ)) *
          (lcmLiftedNumerator q a C (n + 1) : ℤ) := by ring
    _ = (cumulativeOverlapDebt q a (n + 1) : ℤ) *
          (lcmLiftedNumerator q a C (n + 1) : ℤ) := by rw [hMsucc]
    _ = (C (n + 1) : ℤ) := hUsucc
    _ = (C n : ℤ) - ((D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ)) := by
        linarith [hstepZ]
    _ = (cumulativeOverlapDebt q a n : ℤ) * (lcmLiftedNumerator q a C n : ℤ) -
          (cumulativeOverlapDebt q a n : ℤ) * lcmLiftedDigit q a C n := by
        rw [hUn, hV]
    _ = (cumulativeOverlapDebt q a n : ℤ) *
          ((lcmLiftedNumerator q a C n : ℤ) - lcmLiftedDigit q a C n) := by ring

/-! ## The freshness budget -/

/-- Number of LCM-non-fresh steps strictly before `n`: the indices where the
current multiplier shares a factor with the accumulated LCM. -/
def lcmNonFreshCount (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => lcmNonFreshCount q a n + if 1 < lcmOverlap q a n then 1 else 0

@[simp]
theorem lcmNonFreshCount_zero (q : ℕ) (a : ℕ → ℕ) :
    lcmNonFreshCount q a 0 = 0 := rfl

@[simp]
theorem lcmNonFreshCount_succ (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    lcmNonFreshCount q a (n + 1) =
      lcmNonFreshCount q a n + if 1 < lcmOverlap q a n then 1 else 0 := rfl

/-- **The division-free freshness budget.**  Every non-fresh step pays at
least one binary factor into the cumulative overlap debt, so
`2^{#{j < n : ρⱼ > 1}} ≤ Mₙ`.  This is the exact finite inequality underlying
the density-one freshness statement. -/
theorem pow_lcmNonFreshCount_le_overlapDebt
    {q : ℕ} {a : ℕ → ℕ} (hq : 0 < q) (ha : ∀ n, 0 < a n) :
    ∀ n, 2 ^ lcmNonFreshCount q a n ≤ cumulativeOverlapDebt q a n := by
  intro n
  induction n with
  | zero => simp [cumulativeOverlapDebt]
  | succ n ih =>
      have hpos : 0 < lcmOverlap q a n := lcmOverlap_pos hq ha n
      by_cases hnf : 1 < lcmOverlap q a n
      · have hcount : lcmNonFreshCount q a (n + 1) = lcmNonFreshCount q a n + 1 := by
          simp [lcmNonFreshCount_succ, hnf]
        have htwo : 2 ≤ lcmOverlap q a n := hnf
        rw [hcount, cumulativeOverlapDebt_succ', pow_succ]
        exact Nat.mul_le_mul ih htwo
      · have hcount : lcmNonFreshCount q a (n + 1) = lcmNonFreshCount q a n := by
          simp [lcmNonFreshCount_succ, hnf]
        rw [hcount, cumulativeOverlapDebt_succ']
        exact ih.trans (Nat.le_mul_of_pos_right _ hpos)

/-- Composed with the keystone: the freshness budget is carried by the
numerator state itself, `2^{#{j < n : ρⱼ > 1}} ≤ Cₙ`. -/
theorem pow_lcmNonFreshCount_le_tailNumerator
    {q : ℕ} {a : ℕ → ℕ} (C D : ℕ → ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    {n : ℕ} (hCpos : 0 < C n) :
    2 ^ lcmNonFreshCount q a n ≤ C n :=
  (pow_lcmNonFreshCount_le_overlapDebt hq ha n).trans
    (Nat.le_of_dvd hCpos
      (cumulativeOverlapDebt_dvd_tailNumerator q a C D hD hstep n))

/-! ## Coprimality of fresh multipliers -/

/-- **Fresh multipliers are coprime to every earlier multiplier.**  If the step
at `j` is LCM-fresh then `aⱼ` is coprime to `aᵢ` for every `i < j`, because
`aᵢ` has already entered `Λⱼ` along the monotone divisibility chain.

Only freshness at the *later* index is used; the brief's hypothesis that both
indices are fresh is redundant. -/
theorem lcmFresh_pairwiseCoprime
    (q : ℕ) (a : ℕ → ℕ) {i j : ℕ} (hij : i < j)
    (hj : lcmOverlap q a j = 1) :
    Nat.Coprime (a i) (a j) :=
  Nat.Coprime.coprime_dvd_left
    (digit_dvd_cumulativeDigitLcm_of_lt q a hij) hj

/-- Symmetric form: distinct indices, freshness at the larger one. -/
theorem lcmFresh_coprime_of_ne
    (q : ℕ) (a : ℕ → ℕ) {i j : ℕ} (hij : i ≠ j)
    (hi : lcmOverlap q a i = 1) (hj : lcmOverlap q a j = 1) :
    Nat.Coprime (a i) (a j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact lcmFresh_pairwiseCoprime q a h hj
  · exact (lcmFresh_pairwiseCoprime q a h hi).symm

/-! ## Sublinearity of the non-fresh count -/

/-- **Division-free density-one core.**  If every fixed power of the numerator
state is eventually dominated by `2ⁿ`, then the LCM-non-fresh count is
sublinear in the division-free sense `K · count < n`. -/
theorem lcmNonFreshCount_sublinear_of_subexponential
    {q : ℕ} {a : ℕ → ℕ} (C D : ℕ → ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (hsubexp : ∀ K, 0 < K → ∃ N, ∀ n, N ≤ n → C n ^ K < 2 ^ n) :
    ∀ K, 0 < K → ∃ N, ∀ n, N ≤ n → K * lcmNonFreshCount q a n < n := by
  intro K hK
  obtain ⟨N, hN⟩ := hsubexp K hK
  refine ⟨N, fun n hn ↦ ?_⟩
  have hbudget : 2 ^ lcmNonFreshCount q a n ≤ C n :=
    pow_lcmNonFreshCount_le_tailNumerator C D hq ha hD hstep (hCpos n)
  have hraised : (2 ^ lcmNonFreshCount q a n) ^ K ≤ C n ^ K :=
    Nat.pow_le_pow_left hbudget K
  have hpowerLt : 2 ^ (lcmNonFreshCount q a n * K) < 2 ^ n := by
    rw [pow_mul]
    exact hraised.trans_lt (hN n hn)
  have hexponent : lcmNonFreshCount q a n * K < n :=
    (Nat.pow_lt_pow_iff_right (by omega)).mp hpowerLt
  simpa [Nat.mul_comm] using hexponent

/-- Exact-orbit specialisation: normalised centred-state vanishing forces the
LCM-non-fresh count to be sublinear.  This composes the keystone budget with
`tailState_subexponential_of_normalizedVanishes`, so the density-one freshness
statement of the return is available in the same regime as the corpus's
subexponential tail growth. -/
theorem lcmNonFreshCount_sublinear_of_normalizedVanishes
    {q : ℕ} {a : ℕ → ℕ} (C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) :
    ∀ K, 0 < K → ∃ N, ∀ n, N ≤ n → K * lcmNonFreshCount q a n < n :=
  lcmNonFreshCount_sublinear_of_subexponential C D hq ha hCpos hD hstep
    (tailState_subexponential_of_normalizedVanishes a C D E hstep hE hvanish)

/-! ## The shifted-CRT first-crossing barrier for the normalised state -/

/-- **The finite combinatorial core.**  Take `B` pairwise-coprime moduli, each
strictly larger than `B`, all of which have already entered the cumulative LCM
by time `T`.  Suppose the LCM-normalised state starts below the block product,
obeys the exact recurrence `ρₙ Uₙ₊₁ = Uₙ - Vₙ` with positive overlap payments
and the centring identity `Vₙ = Λₙ - (aₙ - 1) Uₙ`, has negative part at most
`B` while it is below `2P + B`, and tends to infinity.  This is contradictory.

The argument is a first crossing, so no persistence of divisors is required.
Placing the CRT block in `[P, 2P)` makes the crossing land on a block position
`x + r`; the modulus `m r` divides the state and the cumulative LCM there, so
it divides `V`, which is strictly negative at a strict rise and bounded by `B`
in absolute value.  A modulus exceeding `B` cannot divide a nonzero integer of
absolute value at most `B`.

Unlike `no_boundedNegative_lcmState_of_oldPrimeSupply` the moduli here are
whole numbers rather than primes, and only finitely many are needed. -/
theorem no_lcmState_of_freshBlock
    (U Λ a ρ : ℕ → ℕ) (V : ℕ → ℤ) {B : ℕ} (m : Fin B → ℕ) (T : ℕ)
    (hB : 0 < B)
    (hm : ∀ i, B < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (hmOld : ∀ (i : Fin B) (s : ℕ), T ≤ s → m i ∣ Λ s)
    (hρpos : ∀ n, T ≤ n → 0 < ρ n)
    (hstep : ∀ n, T ≤ n → (ρ n : ℤ) * (U (n + 1) : ℤ) = (U n : ℤ) - V n)
    (hcenter : ∀ n, T ≤ n → V n = (Λ n : ℤ) - ((a n : ℤ) - 1) * (U n : ℤ))
    (hstart : U T < ∏ i, m i)
    (hsmall : ∀ n, T ≤ n → U n < 2 * (∏ i, m i) + B → -(B : ℤ) ≤ V n)
    (hUtop : Filter.Tendsto U Filter.atTop Filter.atTop) :
    False := by
  classical
  have hm1 : ∀ i, 1 < m i := by
    intro i
    have := hm i
    omega
  obtain ⟨x, hPx, hx2P, hxDiv⟩ := exists_consecutiveMultiples_between m hm1 hpair
  obtain ⟨K, hK⟩ := (Filter.tendsto_atTop_atTop.mp hUtop) (x + B)
  let Q : ℕ → Prop := fun t ↦ T < t ∧ x + B ≤ U t
  have hQ : ∃ t, Q t := ⟨max K (T + 1), by
    refine ⟨?_, hK _ (le_max_left _ _)⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self T) (le_max_right _ _)⟩
  let t := Nat.find hQ
  have htQ : Q t := Nat.find_spec hQ
  have hTt : T < t := htQ.1
  have hxt : x + B ≤ U t := htQ.2
  let s := t - 1
  have hsT : T ≤ s := by dsimp [s]; omega
  have hst : s + 1 = t := by dsimp [s]; omega
  have hUs : U s < x + B := by
    by_contra hnot
    have hge : x + B ≤ U s := by omega
    by_cases hsT' : s = T
    · rw [hsT'] at hge
      omega
    · have hTs : T < s := lt_of_le_of_ne hsT (Ne.symm hsT')
      have hmin : t ≤ s := Nat.find_min' hQ ⟨hTs, hge⟩
      omega
  have hUsucc : x + B ≤ U (s + 1) := by rw [hst]; exact hxt
  have hVs : -(B : ℤ) ≤ V s := hsmall s hsT (by omega)
  have hρ1 : (1 : ℤ) ≤ (ρ s : ℤ) := by
    exact_mod_cast hρpos s hsT
  have hUnn : (0 : ℤ) ≤ (U (s + 1) : ℤ) := by positivity
  have hmul : (U (s + 1) : ℤ) ≤ (ρ s : ℤ) * (U (s + 1) : ℤ) := by nlinarith
  rw [hstep s hsT] at hmul
  have hriseZ : (U (s + 1) : ℤ) ≤ (U s : ℤ) + (B : ℤ) := by omega
  have hrise : U (s + 1) ≤ U s + B := by exact_mod_cast hriseZ
  have hxle : x ≤ U s := by omega
  let r : ℕ := U s - x
  have hrB : r < B := by dsimp [r]; omega
  let i : Fin B := ⟨r, hrB⟩
  have hxr : x + i.1 = U s := by dsimp [i, r]; omega
  have hmU : m i ∣ U s := by
    rw [← hxr]
    exact hxDiv i
  have hmL : m i ∣ Λ s := hmOld i s hsT
  have hdvdV : ((m i : ℕ) : ℤ) ∣ V s := by
    rw [hcenter s hsT]
    exact dvd_sub (Int.natCast_dvd_natCast.mpr hmL)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hmU) _)
  have hstrictN : U s < U (s + 1) := by omega
  have hstrict : (U s : ℤ) < (U (s + 1) : ℤ) := by exact_mod_cast hstrictN
  have hVneg : V s < 0 := by omega
  have hdvdNeg : ((m i : ℕ) : ℤ) ∣ -V s := (dvd_neg).mpr hdvdV
  have hle : ((m i : ℕ) : ℤ) ≤ -V s := Int.le_of_dvd (by omega) hdvdNeg
  have hbig : (B : ℤ) < ((m i : ℕ) : ℤ) := by exact_mod_cast hm i
  omega

/-- **The barrier on the actual cumulative-LCM coordinates.**  Instantiating
`no_lcmState_of_freshBlock` at `Uₙ = Cₙ / Mₙ`, `Vₙ = Λₙ - (aₙ - 1) Uₙ`,
`ρₙ = gcd(Λₙ, aₙ)`: a block of `B` LCM-fresh multipliers taken before time `T`,
each exceeding `B`, is inconsistent with a normalised state that starts below
their product, keeps its negative part at most `B` while below twice that
product, and tends to infinity.

Freshness supplies pairwise coprimality (`lcmFresh_coprime_of_ne`) and the
monotone LCM chain supplies oldness (`digit_dvd_cumulativeDigitLcm_of_lt`), so
the moduli are whole multipliers already present in the cumulative denominator.
The analytic input — that such a block exists by time `B + o(B)` on a
counterexample orbit — is not formalised here. -/
theorem no_lcmLiftedState_of_freshMultiplierBlock
    {q : ℕ} {a : ℕ → ℕ} (C D : ℕ → ℕ) {B : ℕ} (idx : Fin B → ℕ) (T : ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n)
    (hD : ∀ n, D n = digitProductScale q a n)
    (horbit : ∀ n, C (n + 1) + D n = a n * C n)
    (hB : 0 < B)
    (hidxNe : ∀ i j, i ≠ j → idx i ≠ idx j)
    (hidxLt : ∀ i, idx i < T)
    (hfresh : ∀ i, lcmOverlap q a (idx i) = 1)
    (hlarge : ∀ i, B < a (idx i))
    (hstart : lcmLiftedNumerator q a C T < ∏ i, a (idx i))
    (hsmall : ∀ n, T ≤ n →
      lcmLiftedNumerator q a C n < 2 * (∏ i, a (idx i)) + B →
      -(B : ℤ) ≤ lcmLiftedDigit q a C n)
    (hUtop : Filter.Tendsto (lcmLiftedNumerator q a C)
      Filter.atTop Filter.atTop) :
    False := by
  refine no_lcmState_of_freshBlock (lcmLiftedNumerator q a C)
    (cumulativeDigitLcm q a) a (lcmOverlap q a) (lcmLiftedDigit q a C)
    (fun i ↦ a (idx i)) T hB hlarge ?_ ?_ ?_ ?_ ?_ hstart hsmall hUtop
  · intro i j hij
    exact lcmFresh_coprime_of_ne q a (hidxNe i j hij) (hfresh i) (hfresh j)
  · intro i s hs
    exact digit_dvd_cumulativeDigitLcm_of_lt q a (lt_of_lt_of_le (hidxLt i) hs)
  · intro n _
    exact lcmOverlap_pos hq ha n
  · intro n _
    exact lcmLifted_step C D hq ha hD horbit n
  · intro n _
    exact lcmLifted_centered q a C n

end ErdosProblems.Erdos243
