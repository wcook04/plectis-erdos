import Erdos257PeriodNoncollapse.TotientActualLcmOrbitSign

/-!
# Dyadic staircase consumers for the actual-LCM top edge

This module tests a natural growing-precision input against the positive
top-edge representative forced by an integral actual-LCM orbit.  The test is
decisive in the negative direction: once the modulus is wide enough to kill
the carry strip, positivity makes the final arithmetic letter strictly
smaller than that modulus.  A terminal staircase would require the same
letter to be divisible by the modulus, so the proposed producer is empty.

The generic weighted-word lemmas remain useful, but an actual-LCM proof must
seek a nonzero residue gap rather than total dyadic annihilation.
-/

namespace Erdos257PeriodNoncollapse
namespace DiagonalFreshLossBridge
namespace PowerTwoOddWindowAffine

open TotientTailPeriodKiller

/-! ## A linear guard on the power-of-two LCM ray -/

/-- One step of the central-binomial recurrence costs at most a factor of
`4`.  This elementary monotonic estimate lets a fixed factor-four saving in
the central-binomial bound propagate through every later index. -/
theorem centralBinom_succ_le_four_mul (n : ℕ) :
    Nat.centralBinom (n + 1) ≤ 4 * Nat.centralBinom n := by
  apply Nat.le_of_mul_le_mul_left _ (Nat.succ_pos n)
  calc
    (n + 1) * Nat.centralBinom (n + 1) =
        2 * (2 * n + 1) * Nat.centralBinom n :=
      Nat.succ_mul_centralBinom_succ n
    _ ≤ ((n + 1) * 4) * Nat.centralBinom n := by
      exact Nat.mul_le_mul_right _ (by omega)
    _ = (n + 1) * (4 * Nat.centralBinom n) := by ring

/-- From index five onward, the central binomial coefficient saves a full
factor `4` against the crude `4^n` estimate. -/
theorem four_mul_centralBinom_le_four_pow
    {n : ℕ} (hn : 5 ≤ n) :
    4 * Nat.centralBinom n ≤ 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.centralBinom, Nat.choose]
  | succ n hn ih =>
      calc
        4 * Nat.centralBinom (n + 1) ≤
            4 * (4 * Nat.centralBinom n) :=
          Nat.mul_le_mul_left 4 (centralBinom_succ_le_four_mul n)
        _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (n + 1) := by rw [pow_succ]; ring

/-- Equivalent exponent-saving form of
`four_mul_centralBinom_le_four_pow`. -/
theorem centralBinom_le_four_pow_pred
    {n : ℕ} (hn : 5 ≤ n) :
    Nat.centralBinom n ≤ 4 ^ (n - 1) := by
  have hmul : 4 * Nat.centralBinom n ≤ 4 * 4 ^ (n - 1) := by
    calc
      4 * Nat.centralBinom n ≤ 4 ^ n :=
        four_mul_centralBinom_le_four_pow hn
      _ = 4 ^ (n - 1) * 4 := by
        rw [← pow_succ]
        congr 1
        omega
      _ = 4 * 4 ^ (n - 1) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by norm_num)

/-- The classical LCM doubling divisibility therefore gains two exponent
bits at every power-of-two doubling, once the old height is at least five. -/
theorem periodLcm_two_mul_le_periodLcm_mul_four_pow_pred
    {n : ℕ} (hn : 5 ≤ n) :
    periodLcm (2 * n) ≤ periodLcm n * 4 ^ (n - 1) := by
  exact (periodLcm_two_mul_le_periodLcm_mul_centralBinom n (by omega)).trans
    (Nat.mul_le_mul_left _ (centralBinom_le_four_pow_pred hn))

/-- Pure exponent arithmetic for the linear-guard induction.  Keeping this
small normalization out of the LCM proof prevents Presburger automation from
seeing the imported arithmetic context. -/
theorem linearGuardExponent_succ
    {a : ℕ} (ha : 4 ≤ a) :
    (2 * 2 ^ a - (2 * a + 4)) + 2 * (2 ^ a - 1) =
      2 * 2 ^ (a + 1) - (2 * (a + 1) + 4) := by
  have hroom : a + 2 ≤ 2 ^ a := by
    induction a, ha using Nat.le_induction with
    | base => norm_num
    | succ a ha ih =>
        rw [pow_succ]
        omega
  rw [pow_succ]
  omega

/-- Pure depth budget consumed after the logarithmic LCM estimate. -/
theorem linearGuardDepth_add_signGuard_lt
    {a L m : ℕ} (ha : 14 ≤ a)
    (hL : L < 2 * 2 ^ a - (2 * a + 4))
    (hm : m ≤ L + 11) :
    m + 1 + (a + 6) < 2 * 2 ^ a := by
  omega

/-- **Linear LCM guard.**  The exact base saving at `2^4`, together with the
factor-four central-binomial saving, adds two guard bits at every doubling.
Thus the exponent deficit is `2a+4`, rather than the constant twelve used by
the earlier short-window interface. -/
theorem periodLcm_pow_two_lt_two_pow_linearGuard
    {a : ℕ} (ha : 4 ≤ a) :
    periodLcm (2 ^ a) < 2 ^ (2 * 2 ^ a - (2 * a + 4)) := by
  induction a, ha using Nat.le_induction with
  | base =>
      simpa using periodLcm_sixteen_lt_two_pow_twenty
  | succ a ha ih =>
      let t := 2 ^ a
      have htFive : 5 ≤ t := by
        have htSixteen : 16 ≤ t := by
          change 2 ^ 4 ≤ 2 ^ a
          exact Nat.pow_le_pow_right (by norm_num : 0 < 2) ha
        omega
      have hdouble :=
        periodLcm_two_mul_le_periodLcm_mul_four_pow_pred (n := t) htFive
      calc
        periodLcm (2 ^ (a + 1)) = periodLcm (2 * t) := by
          congr 1
          simp [t, pow_succ, Nat.mul_comm]
        _ ≤ periodLcm t * 4 ^ (t - 1) := hdouble
        _ < 2 ^ (2 * t - (2 * a + 4)) * 4 ^ (t - 1) :=
          Nat.mul_lt_mul_of_pos_right ih (pow_pos (by norm_num) _)
        _ = 2 ^ (2 * 2 ^ (a + 1) - (2 * (a + 1) + 4)) := by
          rw [show 4 ^ (t - 1) = 2 ^ (2 * (t - 1)) by
            rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
          congr 1
          simpa [t] using linearGuardExponent_succ ha

/-- At cofinal power-two scales the odd-guarded canonical depth retains the
entire `a+6` lookahead required by the actual-LCM positive-sign corridor.
The extra successor covers both adjacent depths produced by the half-word
certificate. -/
theorem oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_succ_add_signGuard_lt
    {a : ℕ} (ha : 14 ≤ a) :
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) + 1 + (a + 6) <
      2 * 2 ^ a := by
  have hHeight :=
    periodLcm_pow_two_lt_two_pow_linearGuard (by omega : 4 ≤ a)
  have hLog :
      Nat.log2 (periodLcm (2 ^ a)) < 2 * 2 ^ a - (2 * a + 4) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (periodLcm_pos (2 ^ a)).ne' hHeight
  have hguard := oddGuardedCanonicalAdjacentSuffixDepth_le_succ (2 ^ a)
  unfold canonicalAdjacentSuffixDepth at hguard
  exact linearGuardDepth_add_signGuard_lt ha hLog hguard

/-- The terminal `m` letters of a depth-`K` actual-LCM word form a dyadic
staircase when the `r`-th letter in that suffix is divisible by `2^(r+1)`.
The exponents increase toward the terminal letter because its binary weight
decreases toward one. -/
def ActualLcmTerminalDyadicStaircase (a J K m : ℕ) : Prop :=
  m ≤ K ∧
    ∀ r : ℕ, r < m →
      (2 : ℤ) ^ (r + 1) ∣
        lcmRayArithmeticLetter (2 ^ a) (J + (K - m) + r + 1)

/-- The sharp elementary ceiling for a zero-residue argument: when the
modulus is no larger than the positive-carry strip, the modulus itself is a
nonzero admissible representative. -/
theorem small_modulus_has_positive_divisible_candidate
    {M B : ℤ} (hM : 0 < M) (hMB : M ≤ B) :
    ∃ e : ℤ, 0 < e ∧ e ≤ B ∧ M ∣ e := by
  exact ⟨M, hM, hMB, dvd_refl M⟩

/-- A staircase of length `m` makes its complete binary word divisible by
`2^m`.  This is the weighted form of the staircase: the `r`-th divisibility
factor and its binary place value multiply to the common exponent `m`. -/
theorem two_pow_dvd_windowDiscrepancy_of_dyadicStaircase
    {h N m : ℕ}
    (hstair : ∀ r : ℕ, r < m →
      (2 : ℤ) ^ (r + 1) ∣ deltaTotient h (N + r + 1)) :
    (2 : ℤ) ^ m ∣ windowDiscrepancy h N m := by
  induction m with
  | zero => simp [windowDiscrepancy]
  | succ m ih =>
      rw [windowDiscrepancy_succ]
      have hprefix : (2 : ℤ) ^ m ∣ windowDiscrepancy h N m :=
        ih (fun r hr => hstair r (by omega))
      have hscaled : (2 : ℤ) ^ (m + 1) ∣
          2 * windowDiscrepancy h N m := by
        obtain ⟨z, hz⟩ := hprefix
        refine ⟨z, ?_⟩
        rw [hz, pow_succ]
        ring
      exact hscaled.add (hstair m (by omega))

/-- Splitting a discrepancy word after `L` letters leaves the old prefix
multiplied by `2^m` and a fresh length-`m` suffix. -/
theorem windowDiscrepancy_add (h N L m : ℕ) :
    windowDiscrepancy h N (L + m) =
      (2 : ℤ) ^ m * windowDiscrepancy h N L +
        windowDiscrepancy h (N + L) m := by
  induction m with
  | zero => simp [windowDiscrepancy]
  | succ m ih =>
      rw [show L + (m + 1) = (L + m) + 1 by omega,
        windowDiscrepancy_succ, ih,
        windowDiscrepancy_succ, pow_succ]
      simp only [Nat.add_assoc]
      ring

/-- A terminal staircase annihilates the entire depth-`K` word modulo
`2^m`: all earlier letters already carry the missing factor through their
binary weights. -/
theorem two_pow_dvd_windowDiscrepancy_of_terminalDyadicStaircase
    {h N K m : ℕ} (hmK : m ≤ K)
    (hstair : ∀ r : ℕ, r < m →
      (2 : ℤ) ^ (r + 1) ∣
        deltaTotient h (N + (K - m) + r + 1)) :
    (2 : ℤ) ^ m ∣ windowDiscrepancy h N K := by
  let L := K - m
  have hKL : L + m = K := by dsimp [L]; omega
  have hsuffix : (2 : ℤ) ^ m ∣ windowDiscrepancy h (N + L) m := by
    apply two_pow_dvd_windowDiscrepancy_of_dyadicStaircase
    intro r hr
    simpa [L, Nat.add_assoc] using hstair r hr
  rw [← hKL, windowDiscrepancy_add]
  exact (dvd_mul_right ((2 : ℤ) ^ m) (windowDiscrepancy h N L)).add hsuffix

/-- Every actual arithmetic letter is strictly below the elementary
directed room at its upper endpoint. -/
theorem lcmRayArithmeticLetter_lt_directedRoom (t j : ℕ) :
    lcmRayArithmeticLetter t j <
      ((2 * periodLcm t + j + 2 : ℕ) : ℤ) := by
  have hletterLeTop :
      lcmRayArithmeticLetter t j ≤
        (Nat.totient (2 * periodLcm t + j) : ℤ) := by
    rw [lcmRayArithmeticLetter_eq_deltaTotient]
    unfold deltaTotient
    rw [show periodLcm t + j + periodLcm t =
      2 * periodLcm t + j by omega]
    omega
  have htotientLeTop :
      (Nat.totient (2 * periodLcm t + j) : ℤ) ≤
        ((2 * periodLcm t + j : ℕ) : ℤ) := by
    exact_mod_cast Nat.totient_le (2 * periodLcm t + j)
  exact hletterLeTop.trans_lt (htotientLeTop.trans_lt (by omega))

/-- **Terminal-staircase no-go at the required scale.**  In the positive
short LCM window, the last letter of a terminal staircase is positive and
strictly smaller than the carry-killing modulus.  The staircase asks that it
be divisible by that modulus, which is impossible.

Thus the full staircase below is a useful route-pruning test, not a viable
cofinal producer for the actual-LCM top edge. -/
theorem not_actualLcmTerminalDyadicStaircase_of_room
    {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hwide : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
      (2 : ℤ) ^ m) :
    ¬ActualLcmTerminalDyadicStaircase a J K m := by
  intro hstair
  let H : ℕ := periodLcm (2 ^ a)
  let j : ℕ := J + K
  have hmPos : 0 < m := by
    by_contra hm
    have hmZero : m = 0 := Nat.eq_zero_of_not_pos hm
    have hBgeTwo : (2 : ℤ) ≤
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) := by
      exact_mod_cast (by omega :
        2 ≤ 2 * periodLcm (2 ^ a) + J + K + 2)
    rw [hmZero, pow_zero] at hwide
    omega
  have hmK : m ≤ K := hstair.1
  have hjPos : 0 < j := by dsimp [j]; omega
  have hjShort : j < 2 * 2 ^ a := by dsimp [j]; omega
  have hletterPos :
      0 < lcmRayArithmeticLetter (2 ^ a) j :=
    lcmRayArithmeticLetter_pos_of_lt_two_mul ha hjPos hjShort
  have hlast :
      (2 : ℤ) ^ m ∣ lcmRayArithmeticLetter (2 ^ a) j := by
    have h := hstair.2 (m - 1) (by omega)
    simpa [j, show m - 1 + 1 = m by omega,
      show J + (K - m) + (m - 1) + 1 = J + K by omega] using h
  have hletterLtRoom :
      lcmRayArithmeticLetter (2 ^ a) j <
        ((2 * H + j + 2 : ℕ) : ℤ) := by
    simpa [H] using lcmRayArithmeticLetter_lt_directedRoom (2 ^ a) j
  have hroomLtPow :
      ((2 * H + j + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m := by
    simpa [H, j, Nat.add_assoc] using hwide
  have hletterLtPow :
      lcmRayArithmeticLetter (2 ^ a) j < (2 : ℤ) ^ m :=
    hletterLtRoom.trans hroomLtPow
  have hletterZero : lcmRayArithmeticLetter (2 ^ a) j = 0 :=
    Int.eq_zero_of_dvd_of_nonneg_of_lt hletterPos.le hletterLtPow hlast
  omega

/-- Modulo `2^m`, a depth-`K` discrepancy depends only on its final `m`
letters.  This is the non-vacuous replacement for asking every terminal
letter to vanish separately. -/
theorem windowDiscrepancy_emod_two_pow_eq_terminal
    {h N K m : ℕ} (hmK : m ≤ K) :
    windowDiscrepancy h N K % (2 : ℤ) ^ m =
      windowDiscrepancy h (N + (K - m)) m % (2 : ℤ) ^ m := by
  rw [show K = (K - m) + m by omega, windowDiscrepancy_add]
  simp

end PowerTwoOddWindowAffine
end DiagonalFreshLossBridge

namespace TotientTailPeriodKiller

open DiagonalFreshLossBridge.PowerTwoOddWindowAffine

/-! ## Terminal certificate transport and first escape -/

/-- A certificate at a translated terminal word lifts to the complete word.
The terminal-suffix identity fixes the low residue.  A residue central modulo
`2^K` stays central modulo every larger dyadic modulus because both its
distance from zero and its distance from the upper endpoint can only grow. -/
theorem certifiedKill_of_shifted_terminal
    {h N s K : ℕ} (hcert : certifiedKill h (N + s) K) :
    certifiedKill h N (s + K) := by
  let P : ℤ := (2 : ℤ) ^ K
  let Q : ℤ := (2 : ℤ) ^ (s + K)
  let B : ℤ := N + h + (s + K) + 2
  let r : ℤ := windowDiscrepancy h (N + s) K % P
  let R : ℤ := windowDiscrepancy h N (s + K) % Q
  have hsmall : B < r ∧ r < P - B := by
    unfold certifiedKill at hcert
    simpa only [B, r, P, Nat.cast_add, Nat.cast_ofNat, add_assoc,
      add_comm, add_left_comm] using hcert
  have hPdvdQ : P ∣ Q := by
    dsimp [P, Q]
    exact pow_dvd_pow 2 (by omega)
  have hterminal :
      R % P = r := by
    dsimp [R, r, P, Q]
    rw [Int.emod_emod_of_dvd _ hPdvdQ]
    simpa [Nat.add_assoc] using
      (windowDiscrepancy_emod_two_pow_eq_terminal
        (h := h) (N := N) (K := s + K) (m := K) (by omega))
  have hPpos : 0 < P := by positivity
  have hQpos : 0 < Q := by positivity
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact Int.emod_nonneg _ hQpos.ne'
  have hRltQ : R < Q := by
    dsimp [R]
    exact Int.emod_lt_of_pos _ hQpos
  change B < R ∧ R < Q - B
  constructor
  · by_contra hnot
    have hRleB : R ≤ B := not_lt.mp hnot
    have hRltP : R < P := by omega
    have hRfix : R % P = R :=
      Int.emod_eq_of_lt hRnonneg hRltP
    rw [hRfix] at hterminal
    omega
  · by_contra hnot
    have hRge : Q - B ≤ R := not_lt.mp hnot
    set k : ℤ := Q - R with hk
    have hkpos : 0 < k := by omega
    have hkB : k ≤ B := by omega
    have hkltP : k < P := by omega
    have hRsub : R = Q - k := by omega
    have hreduce : (Q - k) % P = (P - k) % P := by
      obtain ⟨c, hc⟩ := hPdvdQ
      rw [hc,
        show P * c - k = (P - k) + P * (c - 1) by ring,
        Int.add_mul_emod_self_left]
    have hPsub : (P - k) % P = P - k :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [hRsub, hreduce, hPsub] at hterminal
    omega

/-- The least-depth certificate predicate. -/
def FirstCertifiedKill (h N L : ℕ) : Prop :=
  certifiedKill h N L ∧ ∀ K : ℕ, K < L → ¬ certifiedKill h N K

/-- Every nonempty certificate set has a first escape depth. -/
theorem exists_firstCertifiedKill_of_exists_certifiedKill
    {h N : ℕ} (hexists : ∃ L : ℕ, certifiedKill h N L) :
    ∃ L : ℕ, FirstCertifiedKill h N L := by
  let L := Nat.find hexists
  refine ⟨L, Nat.find_spec hexists, ?_⟩
  intro K hKL hK
  have hmin : L ≤ K := Nat.find_min' hexists hK
  omega

/-- A first escape has the same dyadic depth floor as any certificate. -/
theorem FirstCertifiedKill.depth_floor
    {h N L : ℕ} (hfirst : FirstCertifiedKill h N L) :
    (2 * (N + h + L + 2) : ℤ) < 2 ^ L :=
  certifiedKill_depth_floor hfirst.1

/-- **Long first-escape compression.**  Suppose depth `L` is the first
certificate, while its endpoint radius is below `2^b`.  If at least `b+2`
letters precede the final step, then those final `b+2` letters already form
a certificate at their translated base.

At depth `L-1` the residue is in one of the two edge arcs.  The fresh
totient letter has size at most `B-2`, where `B` is the new radius.  Hence
the affine update lies in `[-B+2, 3B-4]` on the low arc or
`[-3B+4, B-4]` after centering the high arc.  The first-escape certificate
chooses the only possible sign in each case.  Since
`2^(b+2) = 4 * 2^b > 4B`, the resulting value is already central modulo
`2^(b+2)`. -/
theorem firstCertifiedKill_long_terminal
    {h N L b : ℕ} (hfirst : FirstCertifiedKill h N L)
    (hscale : N + h + L + 2 < 2 ^ b)
    (hlong : b + 3 ≤ L) :
    certifiedKill h (N + (L - (b + 2))) (b + 2) := by
  let B : ℤ := N + h + L + 2
  let T : ℤ := (2 : ℤ) ^ b
  let P : ℤ := (2 : ℤ) ^ (b + 2)
  let Q₀ : ℤ := (2 : ℤ) ^ (L - 1)
  let Q : ℤ := (2 : ℤ) ^ L
  let A₀ : ℤ := windowDiscrepancy h N (L - 1)
  let r₀ : ℤ := A₀ % Q₀
  let d : ℤ := deltaTotient h (N + L)
  let A : ℤ := windowDiscrepancy h N L
  have hLpos : 0 < L := by omega
  have hBT : B < T := by
    dsimp [B, T]
    exact_mod_cast hscale
  have hP_eq : P = 4 * T := by
    calc
      P = (2 : ℤ) ^ b * 2 ^ 2 := by
        dsimp [P]
        exact pow_add (2 : ℤ) b 2
      _ = 4 * T := by
        dsimp [T]
        ring
  have hQ_eq : Q = 2 * Q₀ := by
    calc
      Q = (2 : ℤ) ^ ((L - 1) + 1) := by
        dsimp [Q]
        congr 1
        omega
      _ = (2 : ℤ) ^ (L - 1) * 2 := by rw [pow_succ]
      _ = 2 * Q₀ := by simp [Q₀]; ring
  have hQ₀pos : 0 < Q₀ := by positivity
  have hQpos : 0 < Q := by positivity
  have hPpos : 0 < P := by positivity
  have hr₀nonneg : 0 ≤ r₀ := by
    dsimp [r₀]
    exact Int.emod_nonneg _ hQ₀pos.ne'
  have hr₀lt : r₀ < Q₀ := by
    dsimp [r₀]
    exact Int.emod_lt_of_pos _ hQ₀pos
  have hdabs : |d| ≤ B - 2 := by
    have hd := abs_deltaTotient_le h (N + L)
    dsimp [d, B]
    push_cast at hd ⊢
    omega
  have hdBounds : -(B - 2) ≤ d ∧ d ≤ B - 2 :=
    abs_le.mp hdabs
  have hArec : A = 2 * A₀ + d := by
    have hs := windowDiscrepancy_succ h N (L - 1)
    rw [show (L - 1) + 1 = L by omega,
      show N + (L - 1) + 1 = N + L by omega] at hs
    simpa only [A, A₀, d] using hs
  have hA₀decomp : Q₀ * (A₀ / Q₀) + r₀ = A₀ := by
    dsimp [r₀]
    exact Int.mul_ediv_add_emod A₀ Q₀
  have hfull : B < A % Q ∧ A % Q < Q - B := by
    simpa only [B, A, Q] using hfirst.1
  have hprevNot :
      ¬(B - 1 < r₀ ∧ r₀ < Q₀ - (B - 1)) := by
    have hnot := hfirst.2 (L - 1) (by omega)
    unfold certifiedKill at hnot
    simpa only [B, r₀, Q₀, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ L),
      Nat.cast_one, Nat.cast_ofNat, add_assoc, add_comm, add_left_comm,
      sub_eq_add_neg] using hnot
  have harc :
      r₀ ≤ B - 1 ∨ Q₀ - (B - 1) ≤ r₀ := by
    by_cases hlo : r₀ ≤ B - 1
    · exact Or.inl hlo
    · right
      have hlow : B - 1 < r₀ := lt_of_not_ge hlo
      by_contra hhigh
      exact hprevNot ⟨hlow, lt_of_not_ge hhigh⟩
  have hPdvdQ : P ∣ Q := by
    dsimp [P, Q]
    exact pow_dvd_pow 2 (by omega)
  have hPleQ : P ≤ Q :=
    Int.le_of_dvd hQpos hPdvdQ
  have hfourB : 4 * B < P := by
    rw [hP_eq]
    linarith
  have hBQ : B < Q := by
    exact hfull.1.trans (Int.emod_lt_of_pos A hQpos)
  have hterminal :
      A % P =
        windowDiscrepancy h (N + (L - (b + 2))) (b + 2) % P := by
    dsimp [A, P]
    simpa using
      (windowDiscrepancy_emod_two_pow_eq_terminal
          (h := h) (N := N) (K := L) (m := b + 2) (by omega))
  have hcentralP : B < A % P ∧ A % P < P - B := by
    rcases harc with hlo | hhi
    · let y : ℤ := 2 * r₀ + d
      have hyLower : -(B - 2) ≤ y := by
        dsimp [y]
        linarith
      have hyUpper : y ≤ 3 * B - 4 := by
        dsimp [y]
        linarith
      have hAdecomp : A = Q * (A₀ / Q₀) + y := by
        calc
          A = 2 * A₀ + d := hArec
          _ = 2 * (Q₀ * (A₀ / Q₀) + r₀) + d :=
            congrArg (fun z : ℤ => 2 * z + d) hA₀decomp.symm
          _ = Q * (A₀ / Q₀) + y := by
            rw [hQ_eq]
            dsimp [y]
            ring
      have hmodQ : A % Q = y % Q := by
        rw [hAdecomp, show Q * (A₀ / Q₀) + y =
          y + Q * (A₀ / Q₀) by ring, Int.add_mul_emod_self_left]
      have hyNonneg : 0 ≤ y := by
        by_contra hy
        have hyNeg : y < 0 := lt_of_not_ge hy
        have hyGtNegQ : -Q < y := by
          omega
        have hymod : y % Q = Q + y := by
          rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt] <;> omega
        rw [hmodQ, hymod] at hfull
        omega
      have hyLtQ : y < Q := by
        linarith
      have hymodQ : y % Q = y :=
        Int.emod_eq_of_lt hyNonneg hyLtQ
      have hyCentralLow : B < y := by
        rw [hmodQ, hymodQ] at hfull
        exact hfull.1
      have hyLtPsub : y < P - B := by
        linarith
      have hyLtP : y < P := by linarith
      have hmodP : A % P = y := by
        obtain ⟨c, hc⟩ := hPdvdQ
        rw [hAdecomp, hc,
          show P * c * (A₀ / Q₀) + y =
            y + P * (c * (A₀ / Q₀)) by ring,
          Int.add_mul_emod_self_left, Int.emod_eq_of_lt hyNonneg hyLtP]
      rw [hmodP]
      exact ⟨hyCentralLow, hyLtPsub⟩
    · let y : ℤ := 2 * (r₀ - Q₀) + d
      have hyLower : -3 * B + 4 ≤ y := by
        dsimp [y]
        linarith
      have hyUpper : y ≤ B - 4 := by
        dsimp [y]
        linarith
      have hAdecomp : A = Q * (A₀ / Q₀ + 1) + y := by
        calc
          A = 2 * A₀ + d := hArec
          _ = 2 * (Q₀ * (A₀ / Q₀) + r₀) + d :=
            congrArg (fun z : ℤ => 2 * z + d) hA₀decomp.symm
          _ = Q * (A₀ / Q₀ + 1) + y := by
            rw [hQ_eq]
            dsimp [y]
            ring
      have hmodQ : A % Q = y % Q := by
        rw [hAdecomp, show Q * (A₀ / Q₀ + 1) + y =
          y + Q * (A₀ / Q₀ + 1) by ring, Int.add_mul_emod_self_left]
      have hyNeg : y < 0 := by
        by_contra hy
        have hyNonneg : 0 ≤ y := le_of_not_gt hy
        have hyLtQ : y < Q := by
          omega
        have hymod : y % Q = y :=
          Int.emod_eq_of_lt hyNonneg hyLtQ
        rw [hmodQ, hymod] at hfull
        omega
      have hyGtNegQ : -Q < y := by
        linarith
      have hymodQ : y % Q = Q + y := by
        rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt] <;> omega
      have hyLtNegB : y < -B := by
        rw [hmodQ, hymodQ] at hfull
        omega
      have hyGtBsubP : B - P < y := by linarith
      have hyGtNegP : -P < y := by linarith
      have hyPnonneg : 0 ≤ P + y := by omega
      have hyPltP : P + y < P := by omega
      have hymodP : y % P = P + y := by
        rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt] <;> omega
      have hmodP : A % P = P + y := by
        obtain ⟨c, hc⟩ := hPdvdQ
        rw [hAdecomp, hc,
          show P * c * (A₀ / Q₀ + 1) + y =
            y + P * (c * (A₀ / Q₀ + 1)) by ring,
          Int.add_mul_emod_self_left, hymodP]
      rw [hmodP]
      constructor <;> linarith
  rw [hterminal] at hcentralP
  have hRadius :
      ((N + (L - (b + 2)) : ℕ) : ℤ) + (h : ℤ) +
          ((b + 2 : ℕ) : ℤ) + 2 = B := by
    dsimp [B]
    rw [Nat.cast_sub (by omega : b + 2 ≤ L)]
    push_cast
    ring
  unfold certifiedKill
  rw [hRadius]
  simpa only [B, P] using hcentralP

/-- Uniform terminal form of `firstCertifiedKill_long_terminal`.  A first
certificate is either already no longer than `b+2`, or its final `b+2`
letters are themselves a certificate.  Thus every first escape below the
`2^b` endpoint scale has an equivalent translated witness whose depth is at
most `b+2`. -/
theorem firstCertifiedKill_terminal_min
    {h N L b : ℕ} (hfirst : FirstCertifiedKill h N L)
    (hscale : N + h + L + 2 < 2 ^ b) :
    certifiedKill h (N + (L - min L (b + 2))) (min L (b + 2)) := by
  by_cases hshort : L ≤ b + 2
  · have hmin : min L (b + 2) = L := min_eq_left hshort
    simpa [hmin] using hfirst.1
  · have hlong : b + 3 ≤ L := by omega
    have hterminal :=
      firstCertifiedKill_long_terminal hfirst hscale hlong
    have hmin : min L (b + 2) = b + 2 :=
      min_eq_right (by omega)
    simpa [hmin] using hterminal

/-- Existential compression packet for downstream arithmetic.  It exposes
only the translated base, the bounded terminal depth, and the exact
prefix/suffix split; the potentially enormous original first depth no longer
appears in the residue condition. -/
theorem FirstCertifiedKill.exists_terminal_certificate
    {h N L b : ℕ} (hfirst : FirstCertifiedKill h N L)
    (hscale : N + h + L + 2 < 2 ^ b) :
    ∃ s K : ℕ,
      s + K = L ∧ K ≤ b + 2 ∧ certifiedKill h (N + s) K := by
  refine ⟨L - min L (b + 2), min L (b + 2), ?_, min_le_right _ _, ?_⟩
  · omega
  · exact firstCertifiedKill_terminal_min hfirst hscale

/-- The two scale-`b` guard bits of a `(b+2)`-bit residue are mixed.  The
intervals are exactly the binary cylinders `01` and `10`; every lower bit is
left unrestricted. -/
def DyadicMixedGuard (A : ℤ) (b : ℕ) : Prop :=
  let P : ℤ := (2 : ℤ) ^ b
  let r : ℤ := A % (2 : ℤ) ^ (b + 2)
  (P ≤ r ∧ r < 2 * P) ∨ (2 * P ≤ r ∧ r < 3 * P)

/-- **Exact two-level dyadic dichotomy.**  If a `(b+2)`-bit residue is
central for a radius `B < 2^b`, then either its terminal `(b+1)`-bit residue
is already central for the same radius, or its two guard bits are mixed.
This is the finite socket/guard alternative; it uses no information about
the lower `b` bits. -/
theorem certifiedDyadic_twoLevel_socket_or_mixed
    {A B : ℤ} {b : ℕ} (hscale : B < (2 : ℤ) ^ b)
    (hcert :
      B < A % (2 : ℤ) ^ (b + 2) ∧
        A % (2 : ℤ) ^ (b + 2) < (2 : ℤ) ^ (b + 2) - B) :
    (B < A % (2 : ℤ) ^ (b + 1) ∧
        A % (2 : ℤ) ^ (b + 1) < (2 : ℤ) ^ (b + 1) - B) ∨
      DyadicMixedGuard A b := by
  let P : ℤ := (2 : ℤ) ^ b
  let Q : ℤ := (2 : ℤ) ^ (b + 1)
  let R : ℤ := (2 : ℤ) ^ (b + 2)
  let r₁ : ℤ := A % Q
  let r₂ : ℤ := A % R
  have hQeq : Q = 2 * P := by
    calc
      Q = (2 : ℤ) ^ b * 2 := by
        dsimp [Q]
        exact pow_succ (2 : ℤ) b
      _ = 2 * P := by simp [P]; ring
  have hReq : R = 2 * Q := by
    calc
      R = (2 : ℤ) ^ (b + 1) * 2 := by
        dsimp [R]
        simpa [Nat.add_assoc] using pow_succ (2 : ℤ) (b + 1)
      _ = 2 * Q := by simp [Q]; ring
  have hQpos : 0 < Q := by positivity
  have hRpos : 0 < R := by positivity
  have hr₂nonneg : 0 ≤ r₂ := by
    dsimp [r₂]
    exact Int.emod_nonneg _ hRpos.ne'
  have hr₂lt : r₂ < R := by
    dsimp [r₂]
    exact Int.emod_lt_of_pos _ hRpos
  have hQdvdR : Q ∣ R := by
    dsimp [Q, R]
    exact pow_dvd_pow 2 (by omega)
  have hrel : r₂ % Q = r₁ := by
    dsimp [r₁, r₂]
    exact Int.emod_emod_of_dvd A hQdvdR
  have hcert' : B < r₂ ∧ r₂ < R - B := by
    simpa only [r₂, R] using hcert
  by_cases hsock : B < r₁ ∧ r₁ < Q - B
  · left
    simpa only [r₁, Q] using hsock
  · right
    change (P ≤ r₂ ∧ r₂ < 2 * P) ∨
      (2 * P ≤ r₂ ∧ r₂ < 3 * P)
    by_cases hlo : r₂ < Q
    · have hr₂mod : r₂ % Q = r₂ :=
        Int.emod_eq_of_lt hr₂nonneg hlo
      have hr₁eq : r₁ = r₂ := by
        rw [hr₂mod] at hrel
        exact hrel.symm
      have hupper : Q - B ≤ r₁ := by
        by_contra hnot
        apply hsock
        constructor
        · rw [hr₁eq]
          exact hcert'.1
        · exact lt_of_not_ge hnot
      left
      rw [hQeq] at hlo hupper
      rw [hr₁eq] at hupper
      constructor <;> linarith
    · have hr₂ge : Q ≤ r₂ := le_of_not_gt hlo
      have hr₂subNonneg : 0 ≤ r₂ - Q := by omega
      have hr₂subLt : r₂ - Q < Q := by
        rw [hReq] at hr₂lt
        omega
      have hr₂mod : r₂ % Q = r₂ - Q := by
        rw [Int.emod_eq_sub_self_emod,
          Int.emod_eq_of_lt hr₂subNonneg hr₂subLt]
      have hr₁eq : r₁ = r₂ - Q := by
        rw [hr₂mod] at hrel
        exact hrel.symm
      have hlower : r₁ ≤ B := by
        by_contra hnot
        apply hsock
        constructor
        · exact lt_of_not_ge hnot
        · rw [hr₁eq]
          rw [hReq] at hcert'
          omega
      right
      rw [hQeq] at hr₂ge hr₁eq
      constructor
      · exact hr₂ge
      · linarith

/-- Mixed guard bits automatically certify a `(b+2)`-word whenever the
endpoint radius is below `2^b`. -/
theorem certifiedKill_of_dyadicMixedGuard
    {h N b : ℕ} (hscale : N + h + (b + 2) + 2 < 2 ^ b)
    (hguard : DyadicMixedGuard (windowDiscrepancy h N (b + 2)) b) :
    certifiedKill h N (b + 2) := by
  let P : ℤ := (2 : ℤ) ^ b
  let R : ℤ := (2 : ℤ) ^ (b + 2)
  let B : ℤ := N + h + (b + 2) + 2
  let r : ℤ := windowDiscrepancy h N (b + 2) % R
  have hBP : B < P := by
    dsimp [B, P]
    exact_mod_cast hscale
  have hReq : R = 4 * P := by
    calc
      R = (2 : ℤ) ^ b * 2 ^ 2 := by
        dsimp [R]
        exact pow_add (2 : ℤ) b 2
      _ = 4 * P := by simp [P]; ring
  change B < r ∧ r < R - B
  change (P ≤ r ∧ r < 2 * P) ∨
      (2 * P ≤ r ∧ r < 3 * P) at hguard
  rcases hguard with hguard | hguard <;>
    rw [hReq] <;> constructor <;> linarith

/-- A `(b+2)` terminal certificate is exactly a `(b+1)` socket or a mixed
two-bit guard, under the natural radius scale. -/
theorem certifiedKill_bplus2_iff_socket_or_mixed
    {h N b : ℕ} (hscale : N + h + (b + 2) + 2 < 2 ^ b) :
    certifiedKill h N (b + 2) ↔
      certifiedKill h (N + 1) (b + 1) ∨
        DyadicMixedGuard (windowDiscrepancy h N (b + 2)) b := by
  constructor
  · intro hcert
    have hsplit :=
      certifiedDyadic_twoLevel_socket_or_mixed
        (A := windowDiscrepancy h N (b + 2))
        (B := ((N + h + (b + 2) + 2 : ℕ) : ℤ))
        (b := b) (by exact_mod_cast hscale)
        (by simpa only [certifiedKill] using hcert)
    rcases hsplit with hsock | hguard
    · left
      have hterminal :=
        windowDiscrepancy_emod_two_pow_eq_terminal
          (h := h) (N := N) (K := b + 2) (m := b + 1) (by omega)
      simp only [show b + 2 - (b + 1) = 1 by omega] at hterminal
      rw [hterminal] at hsock
      unfold certifiedKill
      push_cast at hsock ⊢
      simpa only [add_assoc, add_comm, add_left_comm] using hsock
    · exact Or.inr hguard
  · rintro (hsocket | hguard)
    · have hlift :=
        certifiedKill_of_shifted_terminal
          (h := h) (N := N) (s := 1) (K := b + 1) hsocket
      rw [show 1 + (b + 1) = b + 2 by omega] at hlift
      exact hlift
    · exact certifiedKill_of_dyadicMixedGuard hscale hguard

/-- A first escape at its genuine bit scale produces one of the two terminal
cylinders: a `(b+1)` socket, or a `(b+2)` mixed guard carrying its scale
inequality. -/
theorem FirstCertifiedKill.exists_socket_or_mixed
    {h N L b : ℕ} (hfirst : FirstCertifiedKill h N L)
    (hscale : N + h + L + 2 < 2 ^ b) (hbL : b < L) :
    ∃ s : ℕ,
      certifiedKill h (N + s) (b + 1) ∨
        (N + s + h + (b + 2) + 2 < 2 ^ b ∧
          DyadicMixedGuard
            (windowDiscrepancy h (N + s) (b + 2)) b) := by
  by_cases hshort : L ≤ b + 1
  · have hL : L = b + 1 := by omega
    refine ⟨0, Or.inl ?_⟩
    simpa [hL] using hfirst.1
  · have hlong : b + 2 ≤ L := by omega
    let s : ℕ := L - (b + 2)
    have hsadd : s + (b + 2) = L := by
      dsimp [s]
      omega
    have hterminal :
        certifiedKill h (N + s) (b + 2) := by
      have hmin := firstCertifiedKill_terminal_min hfirst hscale
      rw [min_eq_right hlong] at hmin
      simpa [s] using hmin
    have hscale' : N + s + h + (b + 2) + 2 < 2 ^ b := by
      omega
    rcases (certifiedKill_bplus2_iff_socket_or_mixed hscale').mp
        hterminal with hsocket | hguard
    · refine ⟨s + 1, Or.inl ?_⟩
      simpa [Nat.add_assoc] using hsocket
    · exact ⟨s, Or.inr ⟨hscale', hguard⟩⟩

/-- Exact arithmetic target left after all carry compression. -/
def GuardCylinderWitness (h N : ℕ) : Prop :=
  ∃ s b : ℕ,
    certifiedKill h (N + s) (b + 1) ∨
      (N + s + h + (b + 2) + 2 < 2 ^ b ∧
        DyadicMixedGuard (windowDiscrepancy h (N + s) (b + 2)) b)

/-- **Guard-cylinder normal form.**  Existence of a certificate at an
arbitrary depth is exactly equivalent to a logarithmic terminal socket or a
two-bit mixed guard.  The forward direction selects the genuine bit length
`b = log₂(B)+1` of the first-escape radius.  The reverse direction is the
terminal transport theorem. -/
theorem exists_certifiedKill_iff_guardCylinderWitness (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔ GuardCylinderWitness h N := by
  constructor
  · intro hexists
    obtain ⟨L, hfirst⟩ :=
      exists_firstCertifiedKill_of_exists_certifiedKill hexists
    let B : ℕ := N + h + L + 2
    let b : ℕ := Nat.log2 B + 1
    have hBpos : 0 < B := by
      dsimp [B]
      omega
    have hscale : N + h + L + 2 < 2 ^ b := by
      simpa [B, b] using (Nat.lt_log2_self (n := B))
    have hdepthNat : 2 * B < 2 ^ L := by
      have hdepth := hfirst.depth_floor
      dsimp [B]
      exact_mod_cast hdepth
    have hlogLower : 2 ^ Nat.log2 B ≤ B :=
      Nat.log2_self_le hBpos.ne'
    have hpow : 2 ^ b < 2 ^ L := by
      calc
        2 ^ b = 2 * 2 ^ Nat.log2 B := by
          dsimp [b]
          rw [pow_succ]
          ring
        _ ≤ 2 * B := Nat.mul_le_mul_left 2 hlogLower
        _ < 2 ^ L := hdepthNat
    have hbL : b < L :=
      (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpow
    obtain ⟨s, hsocket | ⟨hscale', hguard⟩⟩ :=
      hfirst.exists_socket_or_mixed hscale hbL
    · exact ⟨s, b, Or.inl hsocket⟩
    · exact ⟨s, b, Or.inr ⟨hscale', hguard⟩⟩
  · rintro ⟨s, b, hsocket | ⟨hscale, hguard⟩⟩
    · exact ⟨s + (b + 1),
        certifiedKill_of_shifted_terminal
          (h := h) (N := N) (s := s) (K := b + 1) hsocket⟩
    · have hterminal :
          certifiedKill h (N + s) (b + 2) :=
        certifiedKill_of_dyadicMixedGuard hscale hguard
      exact ⟨s + (b + 2),
        certifiedKill_of_shifted_terminal
          (h := h) (N := N) (s := s) (K := b + 2) hterminal⟩

end TotientTailPeriodKiller

namespace DiagonalFreshLossBridge
namespace PowerTwoOddWindowAffine

open TotientTailPeriodKiller

/-- A one-sided actual-word gap which excludes the positive top-edge carry.
Unlike total staircase annihilation, this condition merely asks the final
`m`-bit residue to lie at or below the complement of the directed carry
strip.  By `windowDiscrepancy_emod_two_pow_eq_terminal`, it is a condition on
the last `m` actual arithmetic letters alone. -/
def ActualLcmTopEdgeResidueGap (a J K m : ℕ) : Prop :=
  m ≤ K ∧
    ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
      windowDiscrepancy (periodLcm (2 ^ a))
          (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)

/-- Exact terminal-suffix form of the one-sided residue gap. -/
theorem actualLcmTopEdgeResidueGap_iff_terminal (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a))
            (periodLcm (2 ^ a) + J + (K - m)) m % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m -
            ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) := by
  constructor
  · rintro ⟨hmK, hroom, hgap⟩
    refine ⟨hmK, hroom, ?_⟩
    rw [← windowDiscrepancy_emod_two_pow_eq_terminal
      (h := periodLcm (2 ^ a))
      (N := periodLcm (2 ^ a) + J) (K := K) (m := m) hmK]
    simpa [Nat.add_assoc] using hgap
  · rintro ⟨hmK, hroom, hgap⟩
    refine ⟨hmK, hroom, ?_⟩
    rw [windowDiscrepancy_emod_two_pow_eq_terminal
      (h := periodLcm (2 ^ a))
      (N := periodLcm (2 ^ a) + J) (K := K) (m := m) hmK]
    simpa [Nat.add_assoc] using hgap

/-- The sliding-suffix residue is exactly the corresponding translated
actual-LCM discrepancy word modulo its suffix modulus. -/
theorem diagonalSuffixResidue_eq_windowDiscrepancy
    (t J m : ℕ) :
    diagonalSuffixResidue t J m =
      windowDiscrepancy (periodLcm t) (periodLcm t + J) m % 2 ^ m := by
  rw [diagonalSuffixResidue_eq_increment_sum]
  unfold windowDiscrepancy
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun z : ℤ => z * 2 ^ (m - 1 - r))
  unfold diagonalWindowIncrement
  have htop :
      2 * periodLcm t + (J + 1 + r) =
        (periodLcm t + J) + periodLcm t + 1 + r := by
    omega
  have hbot :
      periodLcm t + (J + 1 + r) = periodLcm t + J + 1 + r := by
    omega
  rw [htop, hbot]

/-- **One-sided adjacent-gap geometry.**  To obtain an upper top-edge gap at
one of two adjacent depths, the circular suffix displacement need only avoid
the two individual upper-edge arcs.  The older symmetric certificate spends
the sum of both edge widths on both sides; this theorem spends one `2H` edge
on each side and asks for no lower margin at the selected depth. -/
theorem actualLcmTopEdgeResidueGap_or_of_adjacentSuffixMidband
    {a m : ℕ}
    (hroom :
      ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlo :
      ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m)
    (hhi :
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ)) :
    ActualLcmTopEdgeResidueGap a 0 m m ∨
      ActualLcmTopEdgeResidueGap a 0 (m + 1) m := by
  let t : ℕ := 2 ^ a
  let H : ℕ := periodLcm t
  let M : ℤ := (2 : ℤ) ^ m
  let x : ℤ := diagonalSuffixResidue t 0 m
  let y : ℤ := diagonalSuffixResidue t 1 m
  let d : ℤ := diagonalAdjacentSuffixResidue t 0 m
  let E₀ : ℤ := ((2 * H + m + 2 : ℕ) : ℤ)
  let E₁ : ℤ := ((2 * H + m + 3 : ℕ) : ℤ)
  have hroom' : E₁ < M := by simpa [t, H, M, E₁] using hroom
  have hlo' : E₀ ≤ d := by simpa [t, H, d, E₀] using hlo
  have hhi' : d ≤ M - E₁ := by simpa [t, H, M, d, E₁] using hhi
  have hx0 : 0 ≤ x := by
    unfold x diagonalSuffixResidue
    exact Int.emod_nonneg _ (by positivity)
  have hxM : x < M := by
    unfold x diagonalSuffixResidue M
    exact Int.emod_lt_of_pos _ (by positivity)
  have hy0 : 0 ≤ y := by
    unfold y diagonalSuffixResidue
    exact Int.emod_nonneg _ (by positivity)
  have hyM : y < M := by
    unfold y diagonalSuffixResidue M
    exact Int.emod_lt_of_pos _ (by positivity)
  have hd : d = (y - x) % M := by
    rfl
  have hd_of_le (hxy : x ≤ y) : d = y - x := by
    rw [hd, Int.emod_eq_of_lt] <;> omega
  have hd_of_gt (hyx : y < x) : d = M + y - x := by
    rw [hd, show y - x = (M + y - x) - M by ring,
      Int.sub_emod_right, Int.emod_eq_of_lt] <;> omega
  have hroom₀ : E₀ < M := by
    dsimp [E₀, E₁, H] at hroom' ⊢
    omega
  by_cases hxGap : x ≤ M - E₀
  · left
    apply (actualLcmTopEdgeResidueGap_iff_terminal a 0 m m).2
    refine ⟨le_rfl, ?_, ?_⟩
    · simpa [t, H, M, E₀] using hroom₀
    · rw [show m - m = 0 by omega]
      simp only [Nat.add_zero]
      have hxWord :
          diagonalSuffixResidue (2 ^ a) 0 m =
            windowDiscrepancy (periodLcm (2 ^ a))
              (periodLcm (2 ^ a)) m % 2 ^ m := by
        simpa using diagonalSuffixResidue_eq_windowDiscrepancy (2 ^ a) 0 m
      rw [← hxWord]
      simpa [t, H, M, x, E₀] using hxGap
  by_cases hyGap : y ≤ M - E₁
  · right
    apply (actualLcmTopEdgeResidueGap_iff_terminal a 0 (m + 1) m).2
    refine ⟨by omega, ?_, ?_⟩
    · simpa [t, H, M, E₁] using hroom'
    · rw [show m + 1 - m = 1 by omega]
      simp only [Nat.add_zero]
      have hyWord :
          diagonalSuffixResidue (2 ^ a) 1 m =
            windowDiscrepancy (periodLcm (2 ^ a))
              (periodLcm (2 ^ a) + 1) m % 2 ^ m := by
        simpa using diagonalSuffixResidue_eq_windowDiscrepancy (2 ^ a) 1 m
      rw [← hyWord]
      simpa [t, H, M, y, E₁, Nat.add_assoc] using hyGap
  exfalso
  have hxTop : M - E₀ < x := lt_of_not_ge hxGap
  have hyTop : M - E₁ < y := lt_of_not_ge hyGap
  by_cases hxy : x ≤ y
  · rw [hd_of_le hxy] at hlo'
    omega
  · rw [hd_of_gt (lt_of_not_ge hxy)] at hhi'
    omega

/-! ## Quotient-scale form of the one-sided gap -/

/-- The corrected top-edge target on the quotient-scale arithmetic word.
It retains only the upper edge of `LcmDiagonalArithmeticKill`; no positive
lower margin is required. -/
def LcmDiagonalTopEdgeGap (t L : ℕ) : Prop :=
  (2 * periodLcm t + L + 2 : ℤ) < 2 ^ L ∧
    lcmDiagonalArithmeticWord t L % 2 ^ L ≤
      2 ^ L - (2 * periodLcm t + L + 2)

instance (t L : ℕ) : Decidable (LcmDiagonalTopEdgeGap t L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- At `J = 0` and full precision `m = K`, the localized gap is exactly the
one-sided quotient-scale arithmetic gap. -/
theorem actualLcmTopEdgeResidueGap_zero_self_iff_lcmDiagonalTopEdgeGap
    (a K : ℕ) :
    ActualLcmTopEdgeResidueGap a 0 K K ↔
      LcmDiagonalTopEdgeGap (2 ^ a) K := by
  unfold ActualLcmTopEdgeResidueGap LcmDiagonalTopEdgeGap
  rw [lcmDiagonalArithmeticWord_eq_windowDiscrepancy]
  norm_num

/-- The older asymmetric fresh-loss certificate is stronger than the new
one-sided top-edge target: its strict upper edge gives the desired weak
upper edge, while its positive lower edge forces the modulus room. -/
theorem lcmDiagonalTopEdgeGap_of_diagonalFreshLossResidueCert
    {t L : ℕ} (hcert : diagonalFreshLossResidueCert t L) :
    LcmDiagonalTopEdgeGap t L := by
  unfold diagonalFreshLossResidueCert at hcert
  unfold LcmDiagonalTopEdgeGap
  rw [lcmDiagonalArithmeticWord_emod_eq_diagonalWindowResidue]
  constructor
  · omega
  · exact hcert.2.le

/-- The symmetric arithmetic kill also projects to the corrected one-sided
gap. -/
theorem lcmDiagonalTopEdgeGap_of_lcmDiagonalArithmeticKill
    {t L : ℕ} (hkill : LcmDiagonalArithmeticKill t L) :
    LcmDiagonalTopEdgeGap t L :=
  lcmDiagonalTopEdgeGap_of_diagonalFreshLossResidueCert
    (diagonalFreshLossResidueCert_of_lcmDiagonalArithmeticKill hkill)

/-- Symmetric diagonal certificates can be consumed by the localized
top-edge route without passing through the real tail first. -/
theorem actualLcmTopEdgeResidueGap_zero_self_of_diagonalSymmetricResidueCert
    {a K : ℕ} (hcert : diagonalSymmetricResidueCert (2 ^ a) K) :
    ActualLcmTopEdgeResidueGap a 0 K K := by
  apply
    (actualLcmTopEdgeResidueGap_zero_self_iff_lcmDiagonalTopEdgeGap a K).2
  apply lcmDiagonalTopEdgeGap_of_lcmDiagonalArithmeticKill
  exact
    (lcmDiagonalArithmeticKill_iff_diagonalSymmetricResidueCert
      (2 ^ a) K).2 hcert

/-- A viable weakening of the impossible full staircase.  Only the letters
before the terminal one are annihilated at their binary places; the last
letter is retained as a nonzero residue and is required to land below the
top-edge carry band. -/
def ActualLcmTerminalPuncturedDyadicStaircase
    (a J K m : ℕ) : Prop :=
  0 < m ∧ m ≤ K ∧
    (∀ r : ℕ, r + 1 < m →
      (2 : ℤ) ^ (r + 1) ∣
        lcmRayArithmeticLetter (2 ^ a) (J + (K - m) + r + 1)) ∧
    ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    lcmRayArithmeticLetter (2 ^ a) (J + K) ≤
      (2 : ℤ) ^ m -
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)

/-- A punctured staircase produces the one-sided top-edge residue gap.  The
terminal arithmetic letter survives literally; every earlier suffix letter
vanishes modulo `2^m` after its binary weight is included. -/
theorem actualLcmTopEdgeResidueGap_of_puncturedDyadicStaircase
    {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hpunc : ActualLcmTerminalPuncturedDyadicStaircase a J K m) :
    ActualLcmTopEdgeResidueGap a J K m := by
  rcases hpunc with ⟨hmPos, hmK, hprefix, hroom, hlastLe⟩
  let H : ℕ := periodLcm (2 ^ a)
  let N : ℕ := H + J
  let L : ℕ := K - m
  let P : ℤ := (2 : ℤ) ^ m
  let c : ℤ := lcmRayArithmeticLetter (2 ^ a) (J + K)
  have hprefixDvd :
      (2 : ℤ) ^ (m - 1) ∣
        windowDiscrepancy H (N + L) (m - 1) := by
    apply two_pow_dvd_windowDiscrepancy_of_dyadicStaircase
    intro r hr
    have hletter := hprefix r (by omega)
    rw [lcmRayArithmeticLetter_eq_deltaTotient] at hletter
    simpa [H, N, L, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hletter
  have hscaledDvd :
      P ∣ 2 * windowDiscrepancy H (N + L) (m - 1) := by
    obtain ⟨z, hz⟩ := hprefixDvd
    have hpow : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
      ring
    refine ⟨z, ?_⟩
    rw [hz, show P = (2 : ℤ) ^ m by rfl, hpow]
    ring
  have hsuffixRec :
      windowDiscrepancy H (N + L) m =
        2 * windowDiscrepancy H (N + L) (m - 1) + c := by
    rw [show m = (m - 1) + 1 by omega, windowDiscrepancy_succ]
    apply congrArg (fun z : ℤ =>
      2 * windowDiscrepancy H (N + L) (m - 1) + z)
    dsimp [c]
    rw [lcmRayArithmeticLetter_eq_deltaTotient]
    congr 1
    dsimp [H, N, L]
    omega
  have hsuffixMod :
      windowDiscrepancy H (N + L) m % P = c % P := by
    rw [hsuffixRec, Int.add_emod,
      Int.emod_eq_zero_of_dvd hscaledDvd, zero_add]
    simp
  have hfullMod :
      windowDiscrepancy H N K % P =
        windowDiscrepancy H (N + L) m % P := by
    simpa [L, P] using
      (windowDiscrepancy_emod_two_pow_eq_terminal
        (h := H) (N := N) (K := K) (m := m) hmK)
  have hjPos : 0 < J + K := by omega
  have hjShort : J + K < 2 * 2 ^ a := by omega
  have hcPos : 0 < c := by
    dsimp [c]
    exact lcmRayArithmeticLetter_pos_of_lt_two_mul ha hjPos hjShort
  have hBP :
      ((2 * H + J + K + 2 : ℕ) : ℤ) < P := by
    simpa [H, P] using hroom
  have hcLe :
      c ≤ P - ((2 * H + J + K + 2 : ℕ) : ℤ) := by
    simpa [H, P, c] using hlastLe
  have hcLtP : c < P := by omega
  have hcMod : c % P = c := Int.emod_eq_of_lt hcPos.le hcLtP
  unfold ActualLcmTopEdgeResidueGap
  refine ⟨hmK, by simpa [H, P] using hBP, ?_⟩
  simpa [H, N, P, hfullMod, hsuffixMod, hcMod] using hcLe

/-- The punctured route has an exact penultimate-letter cost.  At the wide
modulus required by the carry strip, positivity and the elementary letter
upper bound force the penultimate letter to be exactly the half-turn
`2^(m-1)`.  In particular the modulus must be the first dyadic scale above
the room bound; taking an extra bit makes even the punctured route empty. -/
theorem puncturedDyadicStaircase_penultimate_eq_half
    {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hpunc : ActualLcmTerminalPuncturedDyadicStaircase a J K m) :
    lcmRayArithmeticLetter (2 ^ a) (J + K - 1) = (2 : ℤ) ^ (m - 1) ∧
      (2 : ℤ) ^ m <
        2 * ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) := by
  rcases hpunc with ⟨hmPos, hmK, hprefix, hroom, _hlastLe⟩
  let H : ℕ := periodLcm (2 ^ a)
  let B : ℤ := ((2 * H + J + K + 2 : ℕ) : ℤ)
  let P : ℤ := (2 : ℤ) ^ m
  let D : ℤ := (2 : ℤ) ^ (m - 1)
  let c : ℤ := lcmRayArithmeticLetter (2 ^ a) (J + K - 1)
  have hroom' : B < P := by simpa [H, B, P] using hroom
  have hBgeFour : (4 : ℤ) ≤ B := by
    have hHPos : 0 < H := by dsimp [H]; exact periodLcm_pos (2 ^ a)
    dsimp [B]
    omega
  have hmThree : 3 ≤ m := by
    by_contra hnot
    have hmLe : m ≤ 2 := by omega
    interval_cases m <;> norm_num [P] at hroom' <;> omega
  have hpenultDvd : D ∣ c := by
    have h := hprefix (m - 2) (by omega)
    simpa [D, c, show m - 2 + 1 = m - 1 by omega,
      show J + (K - m) + (m - 2) + 1 = J + K - 1 by omega] using h
  have hjPos : 0 < J + K - 1 := by omega
  have hjShort : J + K - 1 < 2 * 2 ^ a := by omega
  have hcPos : 0 < c := by
    dsimp [c]
    exact lcmRayArithmeticLetter_pos_of_lt_two_mul ha hjPos hjShort
  have hcLtB : c < B := by
    have hlt := lcmRayArithmeticLetter_lt_directedRoom
      (2 ^ a) (J + K - 1)
    dsimp [c, B, H] at hlt ⊢
    omega
  have hcLtP : c < P := hcLtB.trans hroom'
  have hPtwoD : P = 2 * D := by
    dsimp [P, D]
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    ring
  obtain ⟨q, hq⟩ := hpenultDvd
  have hDPos : 0 < D := by dsimp [D]; positivity
  have hqPos : 0 < q := by
    by_contra hnot
    have hqNonpos : q ≤ 0 := le_of_not_gt hnot
    have hprodNonpos : D * q ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hDPos.le hqNonpos
    rw [hq] at hcPos
    omega
  have hqLtTwo : q < 2 := by
    by_contra hnot
    have htwoLe : (2 : ℤ) ≤ q := le_of_not_gt hnot
    have hprod := mul_le_mul_of_nonneg_left htwoLe hDPos.le
    have htwoDLeC : 2 * D ≤ c := by
      rw [hq]
      simpa [mul_comm] using hprod
    rw [hPtwoD] at hcLtP
    omega
  have hqEq : q = 1 := by omega
  have hcEq : c = D := by simpa [hqEq] using hq
  constructor
  · simpa [c, D] using hcEq
  · change P < 2 * B
    have hDLtB : D < B := by simpa [hcEq] using hcLtB
    rw [hPtwoD]
    have := mul_lt_mul_of_pos_left hDLtB (by norm_num : (0 : ℤ) < 2)
    simpa [B] using this

/-- **Non-vacuous localized top-edge consumer.**  If a terminal dyadic
residue avoids the upper carry strip at any precision `m ≤ K`, the positive
actual-LCM tail difference cannot be integral.  This is strictly weaker than
the symmetric certified-kill band and does not demand zero residue. -/
theorem actualLcmTailDiff_notMem_int_of_topEdgeResidueGap
    {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J) ∉
      Set.range ((↑) : ℤ → ℝ) := by
  unfold ActualLcmTopEdgeResidueGap at hgap
  rcases hgap with ⟨hmK, hroom, hresGap⟩
  rintro ⟨d, hd⟩
  let H : ℕ := periodLcm (2 ^ a)
  let e : ℤ := carryOrbit H (H + J) d K
  let P : ℤ := (2 : ℤ) ^ m
  let Q : ℤ := (2 : ℤ) ^ K
  let B : ℤ := ((2 * H + J + K + 2 : ℕ) : ℤ)
  have hBP : B < P := by simpa [H, P, B] using hroom
  have hPLeQ : P ≤ Q := by
    dsimp [P, Q]
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < 2) hmK)
  have hBQ : B < Q := hBP.trans_le hPLeQ
  have htop := actualLcm_integral_forces_topEdgeResidue
    (a := a) (J := J) (K := K) ha hshort (d := d) hd (by
      simpa [H, Q, B] using hBQ)
  have htop' :
      windowDiscrepancy H (H + J) K % Q = Q - e ∧
        Q - B < windowDiscrepancy H (H + J) K % Q ∧
        windowDiscrepancy H (H + J) K % Q < Q := by
    simpa [H, e, Q, B] using htop
  have hePos : 0 < e := by rw [htop'.1] at htop'; omega
  have heLtB : e < B := by rw [htop'.1] at htop'; omega
  have heLtP : e < P := heLtB.trans hBP
  have hpowDvd : P ∣ Q := by
    dsimp [P, Q]
    exact pow_dvd_pow 2 hmK
  have hresetP :
      -e ≡ windowDiscrepancy H (H + J) K [ZMOD P] := by
    have hreset := carryOrbit_modEq_neg_windowDiscrepancy H (H + J) d K
    simpa [e] using (hreset.neg.of_dvd hpowDvd)
  have hnegEmod : (-e) % P = P - e := by
    rw [show -e = (P - e) + P * (-1) by ring,
      Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by omega)]
  have hfullResidue :
      windowDiscrepancy H (H + J) K % P = P - e := by
    have hmod := hresetP.eq
    rw [hnegEmod] at hmod
    exact hmod.symm
  have hresGap' :
      windowDiscrepancy H (H + J) K % P ≤ P - B := by
    simpa [H, P, B] using hresGap
  rw [hfullResidue] at hresGap'
  omega

/-- The localized residue-gap consumer at the actual orbit `J = 0`. -/
theorem actualLcmTailOrbit_notMem_int_of_topEdgeResidueGap
    {a K m : ℕ} (ha : 8 ≤ a)
    (hshort : K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a 0 K m) :
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ) := by
  simpa [actualLcmTailOrbit, actualLcmHeight, two_mul] using
    (actualLcmTailDiff_notMem_int_of_topEdgeResidueGap
      (a := a) (J := 0) ha (by simpa using hshort) hgap)

/-- Cofinal supply target for the genuinely non-vacuous one-sided actual-word
gap. -/
def PowerTwoActualLcmTopEdgeResidueGapSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m

/-- The exact cofinal arithmetic socket exposed by one-sided adjacent-gap
geometry.  At depth `m`, the adjacent suffix displacement avoids only the
two individual upper-edge arcs.  The buffer is stated for the larger
candidate depth `m + 1`, so either branch produced below remains inside the
actual-LCM sign corridor. -/
def PowerTwoAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m -
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ)

/-- Odd-depth half-word form of the one-sided top-edge producer.  If
`m = 2q+1`, the adjacent suffix residue is twice the half-word residue, and
both directed edge widths divide by two to the same exact threshold
`periodLcm (2^a) + q + 2`.  This is substantially weaker than the older
fixed `1/32` central band. -/
def PowerTwoOddGuardTopEdgeHalfWordBandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
    powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
      (4 : ℤ) ^ q -
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ)

/-- A closed Euclidean band of arbitrary half-width is exactly a lower
bound on the absolute value of a centered representative. -/
theorem centeredTopEdgeBand_iff_abs
    {M B z : ℤ} (hM : 0 < M)
    (hBhalf : 2 * B ≤ M) (hz : |z| ≤ M / 2) :
    (B ≤ z % M ∧ z % M ≤ M - B) ↔ B ≤ |z| := by
  have hzBounds := abs_le.mp hz
  by_cases hz0 : 0 ≤ z
  · have hzM : z < M := by omega
    rw [Int.emod_eq_of_lt hz0 hzM, abs_of_nonneg hz0]
    omega
  · have hzn : z < 0 := lt_of_not_ge hz0
    have hzPlus0 : 0 ≤ z + M := by omega
    have hzPlusM : z + M < M := by omega
    have hzShift : z % M = (z + M) % M := by simp
    rw [hzShift, Int.emod_eq_of_lt hzPlus0 hzPlusM, abs_of_neg hzn]
    omega

/-- At the guarded canonical rank, the exact top-edge threshold fits inside
the signed half-cell of the base-four half-word. -/
theorem twice_topEdgeHalfWordThreshold_le_fourPow
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth :
      oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1) :
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q := by
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hcanonGuard := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  rw [hdepth] at hcanonGuard
  have hq : 3 ≤ q := by omega
  have hqPred : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hscale :
      (4 : ℤ) ^ q = 32 * ((4 : ℤ) ^ q / 32) := by
    calc
      (4 : ℤ) ^ q = (4 : ℤ) ^ (q - 1) * 4 := by
        conv_lhs => rw [← hqPred, pow_succ]
      _ = (8 * ((4 : ℤ) ^ q / 32)) * 4 := by
        rw [fourPow_pred_eq_eight_mul_edge hq]
      _ = 32 * ((4 : ℤ) ^ q / 32) := by ring
  have hedge := canonicalActualOddHalfCorrectionEnvelope_lt_edge ha hdepth
  have hH : 0 < periodLcm (2 ^ a) := periodLcm_pos _
  rw [hscale]
  push_cast at hedge ⊢
  omega

/-- Pointwise exact form of the new producer: the half-word avoids both
top-edge arcs precisely when its actual centered lift has magnitude at least
`periodLcm (2^a) + q + 2`. -/
theorem oddGuardTopEdgeHalfWordBand_iff_actualFinalCenteredMagnitude
    {a q : ℕ} (ha : 2 ≤ a)
    (hdepth :
      oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1) :
    let B : ℤ := ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ)
    B ≤ powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - B ↔
      B ≤ |actualOddHalfCenteredLift a q| := by
  let M : ℤ := (4 : ℤ) ^ q
  let B : ℤ := ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ)
  have hM : 0 < M := by positivity
  have hBhalf : 2 * B ≤ M := by
    simpa [B, M] using
      (twice_topEdgeHalfWordThreshold_le_fourPow ha hdepth)
  have hz : |actualOddHalfCenteredLift a q| ≤ M / 2 := by
    simpa [M, actualOddHalfCenteredLift] using
      (abs_actualCenteredLift_le_half
        (A := diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
        (M := (4 : ℤ) ^ q) (by positivity))
  have hword :
      actualOddHalfCenteredLift a q % M =
        powerTwoOddHalfCorrectionWord a q % M := by
    simpa [M] using
      (actualOddHalfCenteredLift_modEq_halfCorrectionWord
        (a := a) (q := q) ha).eq
  change
    (B ≤ powerTwoOddHalfCorrectionWord a q % M ∧
        powerTwoOddHalfCorrectionWord a q % M ≤ M - B) ↔
      B ≤ |actualOddHalfCenteredLift a q|
  rw [← hword]
  exact centeredTopEdgeBand_iff_abs hM hBhalf hz

/-- Arbitrary-rank version of the exact centered-state identity.  The
canonical-depth hypothesis is used only to prove that the requested edge
width fits inside the half-cell; once that fit is supplied explicitly, the
identity holds at every odd rank. -/
theorem oddHalfWordTopEdgeBand_iff_actualCenteredMagnitude_of_fit
    {a q : ℕ} (ha : 2 ≤ a) (B : ℤ)
    (hfit : 2 * B ≤ (4 : ℤ) ^ q) :
    (B ≤ powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - B) ↔
      B ≤ |actualOddHalfCenteredLift a q| := by
  let M : ℤ := (4 : ℤ) ^ q
  have hM : 0 < M := by positivity
  have hz : |actualOddHalfCenteredLift a q| ≤ M / 2 := by
    simpa [M, actualOddHalfCenteredLift] using
      (abs_actualCenteredLift_le_half
        (A := diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
        (M := (4 : ℤ) ^ q) (by positivity))
  have hword :
      actualOddHalfCenteredLift a q % M =
        powerTwoOddHalfCorrectionWord a q % M := by
    simpa [M] using
      (actualOddHalfCenteredLift_modEq_halfCorrectionWord
        (a := a) (q := q) ha).eq
  change
    (B ≤ powerTwoOddHalfCorrectionWord a q % M ∧
        powerTwoOddHalfCorrectionWord a q % M ≤ M - B) ↔
      B ≤ |actualOddHalfCenteredLift a q|
  rw [← hword]
  exact centeredTopEdgeBand_iff_abs hM (by simpa [M] using hfit) hz

/-- Cofinal actual-state form of the exact top-edge half-word producer. -/
def PowerTwoActualFinalTopEdgeMagnitudeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      |actualOddHalfCenteredLift a q|

/-- The exact top-edge half-word supply and the final centered-magnitude
supply are equivalent, not merely one-way reductions. -/
theorem topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply :
    PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
      PowerTwoActualFinalTopEdgeMagnitudeSupply := by
  constructor
  · intro hsupply a₀
    obtain ⟨a, q, ha, hdepth, hlo, hhi⟩ := hsupply a₀
    have ha2 : 2 ≤ a := by omega
    have hmag :=
      (oddGuardTopEdgeHalfWordBand_iff_actualFinalCenteredMagnitude
        ha2 hdepth).mp ⟨hlo, hhi⟩
    exact ⟨a, q, ha, hdepth, hmag⟩
  · intro hsupply a₀
    obtain ⟨a, q, ha, hdepth, hmag⟩ := hsupply a₀
    have ha2 : 2 ≤ a := by omega
    obtain ⟨hlo, hhi⟩ :=
      (oddGuardTopEdgeHalfWordBand_iff_actualFinalCenteredMagnitude
        ha2 hdepth).mpr hmag
    exact ⟨a, q, ha, hdepth, hlo, hhi⟩

/-- The actual LCM orbit differs from an integer by one exact shifted-tail
error.  The integer is selected by centering the even odd-depth raw block;
no integrality or half-cell-fit hypothesis is used. -/
theorem exists_int_scaled_actualLcmTailOrbit_sub_eq
    {a q : ℕ} (ha : 2 ≤ a) :
    ∃ k : ℤ,
      (2 : ℝ) ^ (2 * q + 1) *
          (actualLcmTailOrbit a - (k : ℝ)) =
        (totientTail
              (2 * periodLcm (2 ^ a) + (2 * q + 1)) -
            totientTail
              (periodLcm (2 ^ a) + (2 * q + 1))) -
          ((diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
              2 * actualOddHalfCenteredLift a q : ℤ) : ℝ) := by
  let H : ℕ := periodLcm (2 ^ a)
  let m : ℕ := 2 * q + 1
  let M : ℤ := (4 : ℤ) ^ q
  let P : ℤ := (2 : ℤ) ^ m
  let R : ℤ := diagonalAdjacentSuffixRawBlock (2 ^ a) 0 m
  let A : ℤ := R / 2
  let u : ℤ := actualOddHalfCenteredLift a q
  let d : ℤ := diagonalWindowIncrement (2 ^ a) (m + 1)
  let e : ℤ := d - 2 * u
  let W : ℤ := windowDiscrepancy H H m
  let E : ℝ := totientTail (2 * H + m) - totientTail (H + m)
  let X : ℝ := actualLcmTailOrbit a
  have hP : P = 2 * M := by
    dsimp [P, M, m]
    calc
      (2 : ℤ) ^ (2 * q + 1) = 2 ^ (2 * q) * 2 ^ 1 := by rw [pow_add]
      _ = (2 ^ 2 : ℤ) ^ q * 2 := by rw [pow_mul]; norm_num
      _ = 2 * (4 : ℤ) ^ q := by norm_num; ring
  have hREven : Even R := by
    simpa [R, m] using
      (diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_even
        (a := a) (q := q) ha)
  have htwoA : 2 * A = R := by
    dsimp [A]
    exact Int.two_mul_ediv_two_of_even hREven
  have hcenter : Int.ModEq M u A := by
    dsimp [M, u, A, R, m, actualOddHalfCenteredLift]
    exact actualCenteredLift_modEq _ _
  obtain ⟨k, hk⟩ := hcenter.dvd
  have hA : A = u + M * k := by
    calc
      A = (A - u) + u := by ring
      _ = M * k + u := by rw [hk]
      _ = u + M * k := by ring
  have hRdecomp : R = 2 * u + P * k := by
    calc
      R = 2 * A := htwoA.symm
      _ = 2 * u + P * k := by rw [hA, hP]; ring
  have hblock : R = W + d := by
    simpa [R, W, H, m, d] using
      (diagonalAdjacentSuffixRawBlock_eq_windowDiscrepancy_add_terminal
        (2 ^ a) m)
  have hW : W = P * k - e := by
    calc
      W = R - d := by rw [hblock]; ring
      _ = P * k - e := by rw [hRdecomp]; dsimp [e]; ring
  have hsplit0 := tail_diff_eq_windowDiscrepancy_div_add_shifted H H m
  have hsplit : X = (W : ℝ) / (P : ℝ) + E / (P : ℝ) := by
    dsimp [X, E, W]
    simpa [P, H, m, actualLcmTailOrbit, actualLcmHeight, two_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit0
  have hWcast : (W : ℝ) = (P : ℝ) * (k : ℝ) - (e : ℝ) := by
    exact_mod_cast hW
  have hPpos : (0 : ℝ) < (P : ℝ) := by
    dsimp [P]
    positivity
  have hscaled :
      (P : ℝ) * (X - (k : ℝ)) = E - (e : ℝ) := by
    rw [hsplit, hWcast]
    field_simp [hPpos.ne']
    ring
  refine ⟨k, ?_⟩
  simpa [X, E, e, d, u, P, H, m, Nat.add_assoc] using hscaled

/-- A hit in the open terminal/carry corridor gives an integer within the
elementary raw-error radius of the actual LCM orbit.  Thus the corridor is
an exact shrinking anti-concentration target, not merely a modular band. -/
theorem exists_int_actualLcmTailOrbit_close_of_actualTerminalCarryCorridor
    {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 1 + (a + 6) < 2 * 2 ^ a)
    (hcorr :
      diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
            ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) <
          2 * actualOddHalfCenteredLift a q ∧
        2 * actualOddHalfCenteredLift a q <
          diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1)) :
    ∃ k : ℤ,
      |actualLcmTailOrbit a - (k : ℝ)| <
        actualLcmRawErrorRadius a q := by
  let H : ℕ := periodLcm (2 ^ a)
  let m : ℕ := 2 * q + 1
  let P : ℤ := (2 : ℤ) ^ m
  let B : ℤ := ((2 * H + m + 2 : ℕ) : ℤ)
  let u : ℤ := actualOddHalfCenteredLift a q
  let d : ℤ := diagonalWindowIncrement (2 ^ a) (m + 1)
  let e : ℤ := d - 2 * u
  let E : ℝ := totientTail (2 * H + m) - totientTail (H + m)
  let X : ℝ := actualLcmTailOrbit a
  obtain ⟨k, hscaled0⟩ :=
    exists_int_scaled_actualLcmTailOrbit_sub_eq
      (a := a) (q := q) (show 2 ≤ a by omega)
  have hscaled :
      (P : ℝ) * (X - (k : ℝ)) = E - (e : ℝ) := by
    simpa [P, X, E, e, d, u, H, m, Nat.add_assoc] using hscaled0
  have hcorr' : d - B < 2 * u ∧ 2 * u < d := by
    simpa [d, B, u, H, m] using hcorr
  have heBounds : 0 < e ∧ e < B := by
    dsimp [e]
    omega
  have hEpos : 0 < E := by
    have h := actualLcmTailDiff_shift_pos (a := a) (J := m) ha (by
      simpa [m] using hshort)
    simpa [E, H, m, two_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  have htailUpper := (tail_diff_directed_bounds H (H + m)).2
  have hEupper : E < (B : ℝ) := by
    dsimp [E, B]
    convert htailUpper using 1 <;> push_cast <;> ring
  have hePosR : (0 : ℝ) < (e : ℝ) := by
    exact_mod_cast heBounds.1
  have heUpperR : (e : ℝ) < (B : ℝ) := by
    exact_mod_cast heBounds.2
  have hdiff : |E - (e : ℝ)| < (B : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith
  have hPpos : (0 : ℝ) < (P : ℝ) := by
    dsimp [P]
    positivity
  have hmul : (P : ℝ) * |X - (k : ℝ)| < (B : ℝ) := by
    calc
      (P : ℝ) * |X - (k : ℝ)| =
          |(P : ℝ) * (X - (k : ℝ))| := by
            rw [abs_mul, abs_of_pos hPpos]
      _ = |E - (e : ℝ)| := congrArg abs hscaled
      _ < (B : ℝ) := hdiff
  have hnear : |X - (k : ℝ)| < (B : ℝ) / (P : ℝ) :=
    (lt_div_iff₀ hPpos).2 (by simpa [mul_comm] using hmul)
  refine ⟨k, ?_⟩
  calc
    |actualLcmTailOrbit a - (k : ℝ)| = |X - (k : ℝ)| := by rfl
    _ < (B : ℝ) / (P : ℝ) := hnear
    _ = actualLcmRawErrorRadius a q := by
      dsimp [B, P, H, m, actualLcmRawErrorRadius, actualLcmHeight]
      push_cast
      ring

/-- Separation from every integer by the elementary raw-error radius forces
escape from the open terminal/carry corridor at that rank. -/
theorem actualTerminalCarryCorridorEscape_of_actualLcmOrbitSeparation
    {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 1 + (a + 6) < 2 * 2 ^ a)
    (hsep : ∀ k : ℤ,
      actualLcmRawErrorRadius a q ≤
        |actualLcmTailOrbit a - (k : ℝ)|) :
    2 * actualOddHalfCenteredLift a q ≤
          diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
            ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) ∨
      diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
        2 * actualOddHalfCenteredLift a q := by
  by_contra hnot
  have hcorr :
      diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
            ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) <
          2 * actualOddHalfCenteredLift a q ∧
        2 * actualOddHalfCenteredLift a q <
          diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) := by
    omega
  obtain ⟨k, hnear⟩ :=
    exists_int_actualLcmTailOrbit_close_of_actualTerminalCarryCorridor
      ha hshort hcorr
  exact (not_lt_of_ge (hsep k)) hnear

/-- If the actual LCM tail orbit is integral, then the doubled centered
odd-half state is exactly the terminal arithmetic letter minus the positive
true carry at the same endpoint.  The half-cell fit is what turns the
modular identity into an equality of integers. -/
theorem two_mul_actualOddHalfCenteredLift_eq_terminal_sub_trueCarry
    {a q : ℕ} (ha : 8 ≤ a)
    (hshort :
      2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a)
    (hfit :
      2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    {z : ℤ} (hz : (z : ℝ) = actualLcmTailOrbit a) :
    2 * actualOddHalfCenteredLift a q =
      diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
        carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z
          (2 * q + 1) := by
  let H : ℕ := periodLcm (2 ^ a)
  let m : ℕ := 2 * q + 1
  let M : ℤ := (4 : ℤ) ^ q
  let P : ℤ := (2 : ℤ) ^ m
  let B : ℤ := ((2 * H + m + 2 : ℕ) : ℤ)
  let R : ℤ := diagonalAdjacentSuffixRawBlock (2 ^ a) 0 m
  let A : ℤ := R / 2
  let u : ℤ := actualOddHalfCenteredLift a q
  let d : ℤ := diagonalWindowIncrement (2 ^ a) (m + 1)
  let e : ℤ := carryOrbit H H z m
  have hM : 0 < M := by positivity
  have hP : P = 2 * M := by
    dsimp [P, M, m]
    calc
      (2 : ℤ) ^ (2 * q + 1) = 2 ^ (2 * q) * 2 ^ 1 := by rw [pow_add]
      _ = (2 ^ 2 : ℤ) ^ q * 2 := by rw [pow_mul]; norm_num
      _ = 2 * (4 : ℤ) ^ q := by norm_num; ring
  have hBform :
      B = 2 * ((H + q + 2 : ℕ) : ℤ) - 1 := by
    dsimp [B, m]
    push_cast
    ring
  have hfit' : 2 * ((H + q + 2 : ℕ) : ℤ) ≤ M := by
    simpa [H, M] using hfit
  have hBM : B < M := by rw [hBform]; omega
  have hBP : B < P := by rw [hP]; omega
  have hz' :
      (z : ℝ) =
        totientTail (2 * periodLcm (2 ^ a)) -
          totientTail (periodLcm (2 ^ a)) := by
    simpa [actualLcmTailOrbit, actualLcmHeight] using hz
  have htop := actualLcm_integral_forces_topEdgeResidue
    (a := a) (J := 0) (K := m) ha (by
      dsimp [m]
      omega) (d := z) (by simpa using hz') (by
        simpa [H, P, B] using hBP)
  have htop' :
      windowDiscrepancy H H m % P = P - e ∧
        P - B < windowDiscrepancy H H m % P ∧
        windowDiscrepancy H H m % P < P := by
    simpa [H, e, P, B, Nat.add_assoc] using htop
  have hePos : 0 < e := by
    rw [htop'.1] at htop'
    omega
  have heLtB : e < B := by
    rw [htop'.1] at htop'
    omega
  have hdEq : d = lcmRayArithmeticLetter (2 ^ a) (m + 1) := by
    dsimp [d]
    rw [lcmRayArithmeticLetter_eq_deltaTotient]
    unfold diagonalWindowIncrement deltaTotient
    have htop :
        periodLcm (2 ^ a) + (m + 1) + periodLcm (2 ^ a) =
          2 * periodLcm (2 ^ a) + (m + 1) := by omega
    rw [htop]
  have hjPos : 0 < m + 1 := by omega
  have hjShort : m + 1 < 2 * 2 ^ a := by
    dsimp [m]
    omega
  have hdPos : 0 < d := by
    rw [hdEq]
    exact lcmRayArithmeticLetter_pos_of_lt_two_mul ha hjPos hjShort
  have hdAbs : |d| ≤ ((2 * H + (m + 1) : ℕ) : ℤ) := by
    simpa [d, H] using
      (abs_diagonalWindowIncrement_le (2 ^ a) (m + 1))
  have hdLtB : d < B := by
    have hdSelf : d ≤ |d| := le_abs_self d
    have hboundLt : ((2 * H + (m + 1) : ℕ) : ℤ) < B := by
      dsimp [B]
      push_cast
      omega
    exact hdSelf.trans_lt (hdAbs.trans_lt hboundLt)
  have hcBounds : -M < d - e ∧ d - e < M := by omega
  have hR :
      R = windowDiscrepancy H H m + d := by
    simpa [R, H, m, d] using
      (diagonalAdjacentSuffixRawBlock_eq_windowDiscrepancy_add_terminal
        (2 ^ a) m)
  have heClosed :
      e = P * z - windowDiscrepancy H H m := by
    simpa [e, P] using
      (carryOrbit_eq_twoPow_mul_sub_windowDiscrepancy H H z m)
  have hRclosed : R = P * z + (d - e) := by
    rw [hR, heClosed]
    ring
  have hREven : Even R := by
    simpa [R, m] using
      (diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_even
        (a := a) (q := q) (show 2 ≤ a by omega))
  have htwoA : 2 * A = R := by
    dsimp [A]
    exact Int.two_mul_ediv_two_of_even hREven
  have huDef : u = actualCenteredLift A M := by
    rfl
  have huAbs : |u| ≤ M / 2 := by
    rw [huDef]
    exact abs_actualCenteredLift_le_half hM
  have huBounds : -M ≤ 2 * u ∧ 2 * u ≤ M := by
    have huBounds' := (abs_le.mp huAbs)
    omega
  have hcenter : Int.ModEq M u A := by
    rw [huDef]
    exact actualCenteredLift_modEq A M
  have hcenterTwo : Int.ModEq (2 * M) (2 * u) (2 * A) :=
    hcenter.mul_left'
  have hrawMod : Int.ModEq P (2 * A) (d - e) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-z, ?_⟩
    rw [htwoA, hRclosed]
    ring
  have hmod : Int.ModEq P (2 * u) (d - e) := by
    have hcenterTwo' : Int.ModEq P (2 * u) (2 * A) := by
      simpa [hP] using hcenterTwo
    exact hcenterTwo'.trans hrawMod
  have hdiffBounds :
      -P < (d - e) - 2 * u ∧ (d - e) - 2 * u < P := by
    rw [hP]
    omega
  have hdiffZero : (d - e) - 2 * u = 0 := by
    have hdiv : P ∣ (d - e) - 2 * u := hmod.dvd
    by_cases hnonneg : 0 ≤ (d - e) - 2 * u
    · exact Int.eq_zero_of_dvd_of_nonneg_of_lt
        hnonneg hdiffBounds.2 hdiv
    · have hdivNeg : P ∣ -((d - e) - 2 * u) := dvd_neg.mpr hdiv
      have hzeroNeg := Int.eq_zero_of_dvd_of_nonneg_of_lt
        (show 0 ≤ -((d - e) - 2 * u) by omega)
        (show -((d - e) - 2 * u) < P by omega) hdivNeg
      omega
  have hfinal : 2 * u = d - e := by omega
  simpa only [u, d, e, H, m] using hfinal

/-- Under integrality, the doubled centered state lies in the open corridor
between the terminal letter minus the directed endpoint bound and the
terminal letter itself.  Escaping either side therefore proves exact
nonintegrality at that rank. -/
theorem actualLcmTailOrbit_notMem_int_of_actualTerminalCarryCorridorEscape
    {a q : ℕ} (ha : 8 ≤ a)
    (hshort :
      2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a)
    (hfit :
      2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hescape :
      2 * actualOddHalfCenteredLift a q ≤
          diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
            ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) ∨
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
          2 * actualOddHalfCenteredLift a q) :
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  let e : ℤ :=
    carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1)
  let B : ℤ :=
    ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ)
  have hid :=
    two_mul_actualOddHalfCenteredLift_eq_terminal_sub_trueCarry
      ha hshort hfit (z := z) hz
  have hz' :
      (z : ℝ) =
        totientTail (periodLcm (2 ^ a) + periodLcm (2 ^ a)) -
          totientTail (periodLcm (2 ^ a)) := by
    simpa [actualLcmTailOrbit, actualLcmHeight, two_mul] using hz
  have htrack := carryOrbit_eq_tail_diff hz' (2 * q + 1)
  have hpos := actualLcmTailDiff_shift_pos
    (a := a) (J := 2 * q + 1) ha (by omega)
  have hePosR : (0 : ℝ) < (e : ℝ) := by
    dsimp [e]
    rw [htrack]
    simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpos
  have hePos : 0 < e := by
    exact_mod_cast hePosR
  have htailUpper :=
    (tail_diff_directed_bounds
      (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + (2 * q + 1))).2
  rw [← htrack] at htailUpper
  have heUpperR : (e : ℝ) < (B : ℝ) := by
    dsimp [e, B]
    convert htailUpper using 1 <;> push_cast <;> ring
  have heLtB : e < B := by
    exact_mod_cast heUpperR
  have hid' :
      2 * actualOddHalfCenteredLift a q =
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) - e := by
    simpa only [e] using hid
  rcases hescape with hleft | hright
  · have hge : B ≤ e := by omega
    exact (not_le_of_gt heLtB) hge
  · have hnonpos : e ≤ 0 := by omega
    exact (not_le_of_gt hePos) hnonpos

/-- A terminal letter dominated by twice the actual centered state excludes
an integral actual-LCM orbit at that odd rank. -/
theorem actualLcmTailOrbit_notMem_int_of_actualTerminalDominance
    {a q : ℕ} (ha : 8 ≤ a)
    (hshort :
      2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a)
    (hfit :
      2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hdom :
      diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
        2 * actualOddHalfCenteredLift a q) :
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ) :=
  actualLcmTailOrbit_notMem_int_of_actualTerminalCarryCorridorEscape
    ha hshort hfit (Or.inr hdom)

/-- Cofinal supply of odd ranks whose centered state escapes the exact open
terminal/carry corridor forced by an integral actual-LCM orbit. -/
def PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    (2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) ∨
      diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
        2 * actualOddHalfCenteredLift a q)

/-- Cofinal one-sided producer exposed by the exact terminal/carry identity.
Unlike the two-sided magnitude target, it only asks the centered state to
dominate half of the final literal arithmetic letter. -/
def PowerTwoFlexibleActualTerminalDominanceSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q

/-- Terminal dominance is the upper escape branch of the exact carry
corridor. -/
theorem flexibleActualTerminalCarryCorridorEscapeSupply_of_dominance
    (hsupply : PowerTwoFlexibleActualTerminalDominanceSupply) :
    PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply := by
  intro a₀
  obtain ⟨a, q, ha₀, ha8, hshort, hfit, hdom⟩ := hsupply a₀
  exact ⟨a, q, ha₀, ha8, hshort, hfit, Or.inr hdom⟩

/-- Strictly weaker cofinal producer: the witness may use any odd rank whose
exact top-edge threshold fits the half-cell and whose adjacent depth remains
inside the actual-LCM sign corridor. -/
def PowerTwoFlexibleActualTopEdgeMagnitudeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      |actualOddHalfCenteredLift a q|

/-- The two-sided centered-magnitude producer implies escape from the exact
terminal/carry corridor.  The positive centered branch escapes above the
terminal letter; the negative branch escapes below the directed endpoint
bound. -/
theorem flexibleActualTerminalCarryCorridorEscapeSupply_of_magnitude
    (hsupply : PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :
    PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply := by
  intro a₀
  obtain ⟨a, q, ha₀, ha8, hshort, hfit, hmag⟩ := hsupply a₀
  let H : ℕ := periodLcm (2 ^ a)
  let T : ℤ := ((H + q + 2 : ℕ) : ℤ)
  let B : ℤ := ((2 * H + (2 * q + 1) + 2 : ℕ) : ℤ)
  let d : ℤ := diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1)
  let u : ℤ := actualOddHalfCenteredLift a q
  have hB : B = 2 * T - 1 := by
    dsimp [B, T]
    push_cast
    ring
  have hdEq : d = lcmRayArithmeticLetter (2 ^ a) (2 * q + 1 + 1) := by
    dsimp [d]
    rw [lcmRayArithmeticLetter_eq_deltaTotient]
    unfold diagonalWindowIncrement deltaTotient
    have htop :
        periodLcm (2 ^ a) + (2 * q + 1 + 1) + periodLcm (2 ^ a) =
          2 * periodLcm (2 ^ a) + (2 * q + 1 + 1) := by omega
    rw [htop]
  have hdPos : 0 < d := by
    rw [hdEq]
    exact lcmRayArithmeticLetter_pos_of_lt_two_mul
      ha8 (by omega) (by omega)
  have hdAbs :
      |d| ≤ ((2 * H + (2 * q + 1 + 1) : ℕ) : ℤ) := by
    simpa [d, H] using
      (abs_diagonalWindowIncrement_le (2 ^ a) (2 * q + 1 + 1))
  have hdLtB : d < B := by
    have hdSelf : d ≤ |d| := le_abs_self d
    have hboundLt :
        ((2 * H + (2 * q + 1 + 1) : ℕ) : ℤ) < B := by
      dsimp [B]
      push_cast
      omega
    exact hdSelf.trans_lt (hdAbs.trans_lt hboundLt)
  have hmag' : T ≤ |u| := by simpa [T, H, u] using hmag
  refine ⟨a, q, ha₀, ha8, hshort, hfit, ?_⟩
  by_cases hu : 0 ≤ u
  · right
    rw [abs_of_nonneg hu] at hmag'
    change d ≤ 2 * u
    omega
  · left
    have huNeg : u < 0 := by omega
    rw [abs_of_neg huNeg] at hmag'
    change 2 * u ≤ d - B
    omega

/-- The canonical final-state producer is a special case of the flexible
odd-rank producer. -/
theorem flexibleActualTopEdgeMagnitudeSupply_of_actualFinal
    (hsupply : PowerTwoActualFinalTopEdgeMagnitudeSupply) :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply := by
  intro a₀
  obtain ⟨a, q, ha, hdepth, hmag⟩ := hsupply a₀
  have ha14 : 14 ≤ a := (le_max_left 14 a₀).trans ha
  have ha₀ : a₀ ≤ a := (le_max_right 14 a₀).trans ha
  have hshort :=
    oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_succ_add_signGuard_lt
      ha14
  rw [hdepth] at hshort
  exact ⟨a, q, ha₀, by omega, hshort,
    twice_topEdgeHalfWordThreshold_le_fourPow (by omega) hdepth, hmag⟩

/-- An exact centered-magnitude witness at any admissible odd rank supplies
the one-sided adjacent-suffix midband. -/
theorem powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
    (hsupply : PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :
    PowerTwoAdjacentSuffixMidbandSupply := by
  intro a₀
  obtain ⟨a, q, ha₀, ha8, hshort, hfit, hmag⟩ := hsupply a₀
  let H : ℕ := periodLcm (2 ^ a)
  let Q : ℤ := (4 : ℤ) ^ q
  let r : ℤ := powerTwoOddHalfCorrectionWord a q % Q
  let B : ℤ := ((H + q + 2 : ℕ) : ℤ)
  have hQ : 0 < Q := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hfit' : 2 * B ≤ Q := by
    simpa [H, Q, B] using hfit
  have hmag' : B ≤ |actualOddHalfCenteredLift a q| := by
    simpa [H, B] using hmag
  obtain ⟨hlo, hhi⟩ :=
    (oddHalfWordTopEdgeBand_iff_actualCenteredMagnitude_of_fit
      (a := a) (q := q) (by omega) B hfit').mpr hmag'
  have hlo' : B ≤ r := by simpa [Q, r] using hlo
  have hhi' : r ≤ Q - B := by simpa [Q, r] using hhi
  have hpow : (2 : ℤ) ^ (2 * q + 1) = 2 * Q := by
    calc
      (2 : ℤ) ^ (2 * q + 1) = 2 ^ (2 * q) * 2 ^ 1 := by rw [pow_add]
      _ = (2 ^ 2 : ℤ) ^ q * 2 := by rw [pow_mul]; norm_num
      _ = 2 * Q := by norm_num [Q]; ring
  have hE₀ :
      ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) =
        2 * B - 1 := by
    dsimp [B, H]
    ring
  have hE₁ :
      ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 3 : ℕ) : ℤ) =
        2 * B := by
    dsimp [B, H]
    ring
  have hd :
      diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) = 2 * r := by
    simpa [r, Q] using
      (diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_two_mul_halfWord
        (a := a) (q := q) (show 2 ≤ a by omega))
  refine ⟨a, 2 * q + 1, ha₀, ha8, hshort, ?_, ?_, ?_⟩
  · rw [hE₁, hpow]
    omega
  · rw [hE₀, hd]
    omega
  · rw [hd, hpow, hE₁]
    omega

/-- The exact odd half-word band supplies the one-sided adjacent midband.
The linear LCM guard pays the larger-depth sign buffer automatically. -/
theorem powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
    (hsupply : PowerTwoOddGuardTopEdgeHalfWordBandSupply) :
    PowerTwoAdjacentSuffixMidbandSupply := by
  intro a₀
  obtain ⟨a, q, ha, hdepth, hlo, hhi⟩ := hsupply a₀
  have ha14 : 14 ≤ a := (le_max_left 14 a₀).trans ha
  have ha₀ : a₀ ≤ a := (le_max_right 14 a₀).trans ha
  let H : ℕ := periodLcm (2 ^ a)
  let Q : ℤ := (4 : ℤ) ^ q
  let r : ℤ := powerTwoOddHalfCorrectionWord a q % Q
  let B : ℤ := ((H + q + 2 : ℕ) : ℤ)
  have hQ : 0 < Q := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hlo' : B ≤ r := by simpa [H, Q, r, B] using hlo
  have hhi' : r ≤ Q - B := by simpa [H, Q, r, B] using hhi
  have hBQ : B < Q := by omega
  have hpow : (2 : ℤ) ^ (2 * q + 1) = 2 * Q := by
    calc
      (2 : ℤ) ^ (2 * q + 1) = 2 ^ (2 * q) * 2 ^ 1 := by rw [pow_add]
      _ = (2 ^ 2 : ℤ) ^ q * 2 := by rw [pow_mul]; norm_num
      _ = 2 * Q := by norm_num [Q]; ring
  have hE₀ :
      ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) =
        2 * B - 1 := by
    dsimp [B, H]
    ring
  have hE₁ :
      ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 3 : ℕ) : ℤ) =
        2 * B := by
    dsimp [B, H]
    ring
  have hd :
      diagonalAdjacentSuffixResidue (2 ^ a) 0 (2 * q + 1) = 2 * r := by
    simpa [r, Q] using
      (diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_two_mul_halfWord
        (a := a) (q := q) (show 2 ≤ a by omega))
  have hbuffer :=
    oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_succ_add_signGuard_lt
      ha14
  refine ⟨a, 2 * q + 1, ha₀, by omega, ?_, ?_, ?_, ?_⟩
  · simpa [hdepth] using hbuffer
  · rw [hE₁, hpow]
    omega
  · rw [hE₀, hd]
    omega
  · rw [hd, hpow, hE₁]
    omega

/-- A cofinal one-sided adjacent midband gives the corrected actual-LCM
top-edge supply, choosing whichever of depths `m` and `m + 1` has the upper
gap. -/
theorem powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband
    (hsupply : PowerTwoAdjacentSuffixMidbandSupply) :
    PowerTwoActualLcmTopEdgeResidueGapSupply := by
  intro a₀
  obtain ⟨a, m, ha₀, ha8, hshort, hroom, hlo, hhi⟩ := hsupply a₀
  rcases actualLcmTopEdgeResidueGap_or_of_adjacentSuffixMidband
      hroom hlo hhi with hgap | hgap
  · exact ⟨a, m, m, ha₀, ha8, by omega, hgap⟩
  · exact ⟨a, m + 1, m, ha₀, ha8, by simpa [Nat.add_assoc] using hshort, hgap⟩

/-- The existing odd-guard half-word producer reaches the corrected
top-edge supply.  The new linear LCM guard is the missing quantitative link:
it keeps both adjacent certificate depths inside the `a+6` sign corridor. -/
theorem powerTwoActualLcmTopEdgeResidueGapSupply_of_oddGuardHalfWordBand
    (hsupply : PowerTwoOddGuardHalfWordBandSupply) :
    PowerTwoActualLcmTopEdgeResidueGapSupply := by
  intro a₀
  obtain ⟨a, q, ha, hdepth, hlo, hhi⟩ := hsupply (max 14 a₀)
  have ha14 : 14 ≤ a :=
    (le_max_left 14 a₀).trans
      ((le_max_right 2 (max 14 a₀)).trans ha)
  have ha₀ : a₀ ≤ a :=
    (le_max_right 14 a₀).trans
      ((le_max_right 2 (max 14 a₀)).trans ha)
  have hbuffer :=
    oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_succ_add_signGuard_lt
      ha14
  rcases diagonalSymmetricResidueCert_or_of_powerTwo_oddGuard_halfWordBand
      (show 2 ≤ a by omega) hdepth hlo hhi with hcert | hcert
  · refine ⟨a, 2 * q + 1, 2 * q + 1, ha₀, by omega, ?_, ?_⟩
    · rw [← hdepth]
      omega
    · exact
        actualLcmTopEdgeResidueGap_zero_self_of_diagonalSymmetricResidueCert
          hcert
  · refine
      ⟨a, 1 + (2 * q + 1), 1 + (2 * q + 1), ha₀, by omega, ?_, ?_⟩
    · rw [← hdepth]
      omega
    · exact
        actualLcmTopEdgeResidueGap_zero_self_of_diagonalSymmetricResidueCert
          hcert

/-- A cofinal localized top-edge gap supplies exact actual-LCM orbit
nonintegrality. -/
theorem actualLcmOrbitNonintegralitySupply_of_topEdgeResidueGap
    (hsupply : PowerTwoActualLcmTopEdgeResidueGapSupply) :
    PowerTwoActualLcmOrbitNonintegralitySupply := by
  intro a₀
  obtain ⟨a, K, m, ha₀, ha8, hshort, hgap⟩ := hsupply a₀
  exact ⟨a, ha₀,
    actualLcmTailOrbit_notMem_int_of_topEdgeResidueGap ha8 hshort hgap⟩

/-- The one-sided terminal-dominance producer supplies cofinal exact
nonintegrality of the actual LCM orbit. -/
theorem actualLcmOrbitNonintegralitySupply_of_flexibleActualTerminalDominance
    (hsupply : PowerTwoFlexibleActualTerminalDominanceSupply) :
    PowerTwoActualLcmOrbitNonintegralitySupply := by
  intro a₀
  obtain ⟨a, q, ha₀, ha8, hshort, hfit, hdom⟩ := hsupply a₀
  exact ⟨a, ha₀,
    actualLcmTailOrbit_notMem_int_of_actualTerminalDominance
      ha8 hshort hfit hdom⟩

/-- Escaping either side of the exact terminal/carry corridor supplies
cofinal nonintegrality of the actual LCM orbit. -/
theorem actualLcmOrbitNonintegralitySupply_of_flexibleActualTerminalCarryCorridorEscape
    (hsupply : PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) :
    PowerTwoActualLcmOrbitNonintegralitySupply := by
  intro a₀
  obtain ⟨a, q, ha₀, ha8, hshort, hfit, hescape⟩ := hsupply a₀
  exact ⟨a, ha₀,
    actualLcmTailOrbit_notMem_int_of_actualTerminalCarryCorridorEscape
      ha8 hshort hfit hescape⟩

/-- Endpoint fan-in from the localized one-sided producer to Erdős #249. -/
theorem irrational_totientSeries_of_topEdgeResidueGapSupply
    (hsupply : PowerTwoActualLcmTopEdgeResidueGapSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply
    (actualLcmOrbitNonintegralitySupply_of_topEdgeResidueGap hsupply)

/-- Direct #249 endpoint for the weaker one-sided adjacent-suffix producer. -/
theorem irrational_totientSeries_of_adjacentSuffixMidbandSupply
    (hsupply : PowerTwoAdjacentSuffixMidbandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_topEdgeResidueGapSupply
    (powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband hsupply)

/-- Direct #249 endpoint for the exact odd half-word top-edge band. -/
theorem irrational_totientSeries_of_oddGuardTopEdgeHalfWordBandSupply
    (hsupply : PowerTwoOddGuardTopEdgeHalfWordBandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_adjacentSuffixMidbandSupply
    (powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand hsupply)

/-- Direct #249 endpoint in the exact centered actual-state formulation. -/
theorem irrational_totientSeries_of_actualFinalTopEdgeMagnitudeSupply
    (hsupply : PowerTwoActualFinalTopEdgeMagnitudeSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_oddGuardTopEdgeHalfWordBandSupply
    (topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply.mpr
      hsupply)

/-- Direct #249 endpoint for the flexible arbitrary-odd-rank producer. -/
theorem irrational_totientSeries_of_flexibleActualTopEdgeMagnitudeSupply
    (hsupply : PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_adjacentSuffixMidbandSupply
    (powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
      hsupply)

/-- Direct #249 endpoint for the one-sided terminal-dominance producer. -/
theorem irrational_totientSeries_of_flexibleActualTerminalDominanceSupply
    (hsupply : PowerTwoFlexibleActualTerminalDominanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply
    (actualLcmOrbitNonintegralitySupply_of_flexibleActualTerminalDominance
      hsupply)

/-- Direct #249 endpoint for the exact terminal/carry corridor-escape
producer. -/
theorem irrational_totientSeries_of_flexibleActualTerminalCarryCorridorEscapeSupply
    (hsupply : PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply
    (actualLcmOrbitNonintegralitySupply_of_flexibleActualTerminalCarryCorridorEscape
      hsupply)

/-- The formal terminal-staircase implication.  Its hypotheses are
inconsistent by `not_actualLcmTerminalDyadicStaircase_of_room`; the theorem
is retained as an explicit consumer-shaped record of the failed route.  A
fixed small modulus also cannot suffice, as
`small_modulus_has_positive_divisible_candidate` shows. -/
theorem actualLcmTailDiff_notMem_int_of_terminalDyadicStaircase
    {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hstair : ActualLcmTerminalDyadicStaircase a J K m)
    (hwide : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
      (2 : ℤ) ^ m) :
    totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J) ∉
      Set.range ((↑) : ℤ → ℝ) := by
  exact (not_actualLcmTerminalDyadicStaircase_of_room ha hshort hwide hstair).elim

/-- The same producer specialized to the actual orbit at `J = 0`. -/
theorem actualLcmTailOrbit_notMem_int_of_terminalDyadicStaircase
    {a K m : ℕ} (ha : 8 ≤ a)
    (hshort : K + (a + 6) < 2 * 2 ^ a)
    (hstair : ActualLcmTerminalDyadicStaircase a 0 K m)
    (hwide : ((2 * periodLcm (2 ^ a) + K + 2 : ℕ) : ℤ) <
      (2 : ℤ) ^ m) :
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ) := by
  simpa [actualLcmTailOrbit, actualLcmHeight, two_mul] using
    (actualLcmTailDiff_notMem_int_of_terminalDyadicStaircase
      (a := a) (J := 0) ha (by simpa using hshort) hstair (by simpa using hwide))

#print axioms not_actualLcmTerminalDyadicStaircase_of_room
#print axioms periodLcm_pow_two_lt_two_pow_linearGuard
#print axioms oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_succ_add_signGuard_lt
#print axioms diagonalSuffixResidue_eq_windowDiscrepancy
#print axioms actualLcmTopEdgeResidueGap_or_of_adjacentSuffixMidband
#print axioms actualLcmTopEdgeResidueGap_zero_self_iff_lcmDiagonalTopEdgeGap
#print axioms centeredTopEdgeBand_iff_abs
#print axioms twice_topEdgeHalfWordThreshold_le_fourPow
#print axioms oddGuardTopEdgeHalfWordBand_iff_actualFinalCenteredMagnitude
#print axioms oddHalfWordTopEdgeBand_iff_actualCenteredMagnitude_of_fit
#print axioms topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply
#print axioms exists_int_scaled_actualLcmTailOrbit_sub_eq
#print axioms exists_int_actualLcmTailOrbit_close_of_actualTerminalCarryCorridor
#print axioms actualTerminalCarryCorridorEscape_of_actualLcmOrbitSeparation
#print axioms two_mul_actualOddHalfCenteredLift_eq_terminal_sub_trueCarry
#print axioms actualLcmTailOrbit_notMem_int_of_actualTerminalCarryCorridorEscape
#print axioms actualLcmTailOrbit_notMem_int_of_actualTerminalDominance
#print axioms flexibleActualTerminalCarryCorridorEscapeSupply_of_magnitude
#print axioms flexibleActualTopEdgeMagnitudeSupply_of_actualFinal
#print axioms powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
#print axioms powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
#print axioms powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband
#print axioms powerTwoActualLcmTopEdgeResidueGapSupply_of_oddGuardHalfWordBand
#print axioms actualLcmTopEdgeResidueGap_of_puncturedDyadicStaircase
#print axioms puncturedDyadicStaircase_penultimate_eq_half
#print axioms actualLcmTailDiff_notMem_int_of_topEdgeResidueGap
#print axioms actualLcmTailOrbit_notMem_int_of_topEdgeResidueGap
#print axioms irrational_totientSeries_of_topEdgeResidueGapSupply
#print axioms irrational_totientSeries_of_adjacentSuffixMidbandSupply
#print axioms irrational_totientSeries_of_oddGuardTopEdgeHalfWordBandSupply
#print axioms irrational_totientSeries_of_actualFinalTopEdgeMagnitudeSupply
#print axioms irrational_totientSeries_of_flexibleActualTopEdgeMagnitudeSupply
#print axioms irrational_totientSeries_of_flexibleActualTerminalDominanceSupply
#print axioms irrational_totientSeries_of_flexibleActualTerminalCarryCorridorEscapeSupply
#print axioms actualLcmTailDiff_notMem_int_of_terminalDyadicStaircase
#print axioms actualLcmTailOrbit_notMem_int_of_terminalDyadicStaircase

end PowerTwoOddWindowAffine
end DiagonalFreshLossBridge
end Erdos257PeriodNoncollapse
