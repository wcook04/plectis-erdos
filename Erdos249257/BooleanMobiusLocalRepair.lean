import Erdos249257.BooleanMobiusCarry
import Erdos249257.GreedyAchievementSet
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Local Boolean--Möbius repair blocks for Erdős #257

This module isolates the finite endpoint arithmetic needed by the constructive
counterexample route.  Proof declarations are added only after the claimed
module's local Lean connection card has been consumed.
-/

namespace Erdos249257

open scoped BigOperators

/-! ## Exact endpoint coordinates -/

/-- The integral part of `2^M / (2^d - 1)`. -/
def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

/-- The source-current fractional part of `2^M / (2^d - 1)` for `d ≥ 2`.
The exponent is reduced modulo `d` before the division. -/
def localMersenneFraction (M d : ℕ) : ℚ :=
  ((2 ^ (M % d) : ℕ) : ℚ) / ((2 ^ d - 1 : ℕ) : ℚ)

/-- Sum of the integral quotient contributions of a finite Boolean support. -/
def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

/-- Sum of the corresponding fractional contributions. -/
def localFractionMass (D : Finset ℕ) (M : ℕ) : ℚ :=
  ∑ d ∈ D, localMersenneFraction M d

/-- The exact finite Mersenne value of a Boolean lower support. -/
def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d

/-- An analytic sufficient handoff for the local repair argument: the Boolean
support frozen through the half cutoff has not yet exceeded the target
Mersenne value `2⁻ᵏ`.  Upper-half word capacity is a separate combinatorial
fact and is derived below from the already-Boolean suffix.  The direct
endpoint-exponential criterion below is an independent sufficient route to
nonnegativity and does not assume this predicate. -/
def RationalHalfCutoffUndershoot (D : Finset ℕ) (k : ℕ) : Prop :=
  localMersennePrefixValue D ≤ 1 / (2 : ℚ) ^ k

/-- The carry left after reading the nonterminating binary expansion of
`2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`.
The theorem below proves that the truncating natural subtraction is honest in
the endpoint situation where it is used. -/
def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1

/-- Number of selected lower ranks which divide the next endpoint. -/
def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card

/-- The endpoint count is exactly the existing Boolean--Möbius support
coefficient, specialized from a finite support. -/
theorem endpointDivisorContribution_eq_supportCoeff
    {D : Finset ℕ} {n : ℕ} (hn : 0 < n) :
    endpointDivisorContribution D n = supportCoeff (↑D : Set ℕ) n := by
  classical
  rw [supportCoeff_eq_card_filter]
  unfold endpointDivisorContribution
  congr 1
  ext d
  simp [Nat.mem_divisors, hn.ne', and_comm]

/-- The next signed Boolean--Möbius coefficient supplied by the binary carry
recurrence. -/
def localRepairInteger (D : Finset ℕ) (k n : ℕ) : ℤ :=
  2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
    (endpointDivisorContribution D n : ℤ)

@[simp] theorem localMersennePrefixValue_eq_finiteErdosSum
    (D : Finset ℕ) :
    localMersennePrefixValue D = finiteErdosSum D 2 := by
  simp [localMersennePrefixValue, finiteErdosSum, mersenneWeightRat]

/-- A power of two has the expected remainder modulo a Mersenne denominator.
The rank-one exception is excluded because its denominator is one. -/
theorem two_pow_mod_mersenne
    {M d : ℕ} (hd : 2 ≤ d) :
    2 ^ M % (2 ^ d - 1) = 2 ^ (M % d) := by
  let q := M / d
  let r := M % d
  let G := 2 ^ r * ∑ i ∈ Finset.range q, (2 ^ d) ^ i
  have hdpos : 0 < d := by omega
  have hdivmod : M = d * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod M d).symm
  have hpowOne : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have hgeom :
      (∑ i ∈ Finset.range q, (2 ^ d) ^ i) * (2 ^ d - 1) + 1 =
        (2 ^ d) ^ q := by
    simpa only [Nat.sub_add_cancel hpowOne] using
      (geom_sum_mul_add (R := ℕ) (2 ^ d - 1) q)
  have hdecomp : 2 ^ M = G * (2 ^ d - 1) + 2 ^ r := by
    calc
      2 ^ M = 2 ^ (d * q + r) := by rw [hdivmod]
      _ = 2 ^ r * (2 ^ d) ^ q := by
        rw [pow_add, pow_mul]
        ring
      _ = 2 ^ r *
          ((∑ i ∈ Finset.range q, (2 ^ d) ^ i) * (2 ^ d - 1) + 1) := by
        rw [hgeom]
      _ = G * (2 ^ d - 1) + 2 ^ r := by
        dsimp [G]
        ring
  have hrlt : r < d := by
    dsimp [r]
    exact Nat.mod_lt _ hdpos
  have hrle : r ≤ d - 1 := by omega
  have hpowle : 2 ^ r ≤ 2 ^ (d - 1) :=
    Nat.pow_le_pow_right (by norm_num) hrle
  have hpowSplit : 2 ^ d = 2 ^ (d - 1) * 2 := by
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (d - 1) * 2 := by rw [pow_succ]
  have hhalfTwo : 2 ≤ 2 ^ (d - 1) := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ d - 1))
  have hrem : 2 ^ r < 2 ^ d - 1 := by omega
  rw [hdecomp, Nat.add_mod, Nat.mul_mod, Nat.mod_self]
  simp [Nat.mod_eq_of_lt hrem, r]

/-- Euclidean division splits one scaled Mersenne weight into its integral
quotient and the explicit residue fraction. -/
theorem scaled_mersenneWeightRat_eq_quotient_add_fraction
    {M d : ℕ} (hd : 2 ≤ d) :
    (2 : ℚ) ^ M * mersenneWeightRat d =
      (localMersenneQuotient M d : ℚ) + localMersenneFraction M d := by
  let N := 2 ^ M
  let q := 2 ^ d - 1
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hNcast : (N : ℚ) = (2 : ℚ) ^ M := by simp [N]
  have hqcast : (q : ℚ) = (2 : ℚ) ^ d - 1 := by
    simpa [q] using natCast_pow_sub_one 2 d (by norm_num)
  have hdivmod : (N : ℚ) =
      ((N / q : ℕ) : ℚ) * (q : ℚ) + ((N % q : ℕ) : ℚ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_add_mod N q).symm)
  have hrem : N % q = 2 ^ (M % d) := by
    simpa [N, q] using two_pow_mod_mersenne (M := M) hd
  rw [mersenneWeightRat, ← hNcast, ← hqcast, mul_one_div]
  change (N : ℚ) / (q : ℚ) =
    ((N / q : ℕ) : ℚ) +
      ((2 ^ (M % d) : ℕ) : ℚ) / (q : ℚ)
  rw [← hrem]
  field_simp
  linarith

theorem localMersenneFraction_pos
    {M d : ℕ} (hd : 2 ≤ d) :
    0 < localMersenneFraction M d := by
  unfold localMersenneFraction
  have hden : 0 < (2 ^ d - 1 : ℕ) :=
    Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  exact div_pos (by positivity) (by exact_mod_cast hden)

/-- Scaling a finite Boolean Mersenne prefix gives the total quotient plus
the total residue mass. -/
theorem scaled_localMersennePrefixValue
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    (2 : ℚ) ^ M * localMersennePrefixValue D =
      (localPrefixQuotient D M : ℚ) + localFractionMass D M := by
  rw [localMersennePrefixValue, Finset.mul_sum]
  calc
    ∑ d ∈ D, (2 : ℚ) ^ M * mersenneWeightRat d =
        ∑ d ∈ D,
          ((localMersenneQuotient M d : ℚ) + localMersenneFraction M d) := by
      apply Finset.sum_congr rfl
      intro d hdmem
      exact scaled_mersenneWeightRat_eq_quotient_add_fraction (hD d hdmem)
    _ = (localPrefixQuotient D M : ℚ) + localFractionMass D M := by
      rw [Finset.sum_add_distrib]
      simp [localPrefixQuotient, localFractionMass]

/-- If `d` divides `n`, the exponent immediately before `n` is congruent to
`d - 1` modulo `d`. -/
theorem pred_mod_eq_pred_of_dvd
    {n d : ℕ} (hn : 0 < n) (hd : 2 ≤ d) (hdn : d ∣ n) :
    (n - 1) % d = d - 1 := by
  have hnmod : n % d = 0 := Nat.mod_eq_zero_of_dvd hdn
  have hstep : (((n - 1) % d) + 1) % d = 0 := by
    calc
      (((n - 1) % d) + 1) % d = ((n - 1) + 1) % d := by
        rw [Nat.add_mod]
        simp [Nat.mod_eq_of_lt (by omega : 1 < d)]
      _ = n % d := by rw [Nat.sub_add_cancel hn]
      _ = 0 := hnmod
  have hdvd : d ∣ (n - 1) % d + 1 := Nat.dvd_of_mod_eq_zero hstep
  have hrem_lt : (n - 1) % d < d := Nat.mod_lt _ (by omega)
  have hdle : d ≤ (n - 1) % d + 1 :=
    Nat.le_of_dvd (by omega) hdvd
  omega

/-- Every selected endpoint divisor contributes strictly more than one half
to the fractional mass at the preceding binary place. -/
theorem half_lt_localMersenneFraction_pred_of_dvd
    {n d : ℕ} (hn : 0 < n) (hd : 2 ≤ d) (hdn : d ∣ n) :
    (1 / 2 : ℚ) < localMersenneFraction (n - 1) d := by
  rw [localMersenneFraction, pred_mod_eq_pred_of_dvd hn hd hdn]
  have hdenNat : 0 < 2 ^ d - 1 :=
    Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  have hdenCast : ((2 ^ d - 1 : ℕ) : ℚ) = (2 : ℚ) ^ d - 1 := by
    simpa using natCast_pow_sub_one 2 d (by norm_num)
  rw [hdenCast, lt_div_iff₀ (by
    have : (1 : ℚ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
    linarith)]
  have hsplit : (2 : ℚ) ^ d = 2 * (2 : ℚ) ^ (d - 1) := by
    calc
      (2 : ℚ) ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
      _ = 2 * 2 ^ (d - 1) := by rw [pow_succ']
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) (d - 1)]

/-! ## The endpoint nonnegativity theorem -/

/-- **Endpoint fractional-part inequality.**  Let `D` be a finite Boolean
support contained in ranks `2, ..., ⌊n/2⌋`, and suppose its Mersenne value
does not exceed `2⁻ᵏ`.  At binary place `n-1`, every member of `D` which
divides `n` contributes more than one half to the fractional mass.  Hence the
endpoint divisor count is at most `2A+1`, where `A` is the binary suffix carry.

No nonnegativity assumption on the next repair coefficient occurs here; it is
the conclusion of the following corollary. -/
theorem endpointDivisorContribution_le_two_mul_localBinarySuffix_add_one
    {D : Finset ℕ} {k n : ℕ}
    (hk : k < n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n / 2)
    (hprefix : RationalHalfCutoffUndershoot D k) :
    endpointDivisorContribution D n ≤
      2 * localBinarySuffix D k (n - 1) + 1 := by
  classical
  unfold RationalHalfCutoffUndershoot at hprefix
  let E := D.filter fun d ↦ d ∣ n
  by_cases hE : E.Nonempty
  · have hEsub : E ⊆ D := Finset.filter_subset _ _
    have hcardpos : 0 < E.card := Finset.card_pos.mpr hE
    have hendpoint : endpointDivisorContribution D n = E.card := by
      rfl
    have hhalfSum :
        (E.card : ℚ) / 2 <
          ∑ d ∈ E, localMersenneFraction (n - 1) d := by
      calc
        (E.card : ℚ) / 2 = ∑ _d ∈ E, (1 / 2 : ℚ) := by
          simp [div_eq_mul_inv]
        _ < ∑ d ∈ E, localMersenneFraction (n - 1) d :=
          Finset.sum_lt_sum_of_nonempty hE fun d hdE ↦ by
            have hdD : d ∈ D := hEsub hdE
            have hddiv : d ∣ n := (Finset.mem_filter.mp hdE).2
            exact half_lt_localMersenneFraction_pred_of_dvd
              (by omega) (hD d hdD).1 hddiv
    have hEF :
        ∑ d ∈ E, localMersenneFraction (n - 1) d ≤
          localFractionMass D (n - 1) := by
      unfold localFractionMass
      apply Finset.sum_le_sum_of_subset_of_nonneg hEsub
      intro d hdD _hdE
      exact (localMersenneFraction_pos (M := n - 1) (hD d hdD).1).le
    have hcardF :
        (E.card : ℚ) / 2 < localFractionMass D (n - 1) :=
      lt_of_lt_of_le hhalfSum hEF
    have hscaled := mul_le_mul_of_nonneg_left hprefix
      (show (0 : ℚ) ≤ (2 : ℚ) ^ (n - 1) by positivity)
    rw [scaled_localMersennePrefixValue
      (M := n - 1) (fun d hdD ↦ (hD d hdD).1)] at hscaled
    have hkM : k ≤ n - 1 := by omega
    have htarget :
        (2 : ℚ) ^ (n - 1) * (1 / (2 : ℚ) ^ k) =
          ((2 ^ (n - 1 - k) : ℕ) : ℚ) := by
      have hexp : n - 1 = k + (n - 1 - k) := by omega
      rw [hexp, pow_add]
      norm_num
      field_simp
    rw [htarget] at hscaled
    let Q := localPrefixQuotient D (n - 1)
    let T := 2 ^ (n - 1 - k)
    have hFnonneg : 0 ≤ localFractionMass D (n - 1) := by
      unfold localFractionMass
      exact Finset.sum_nonneg fun d hdD ↦
        (localMersenneFraction_pos (M := n - 1) (hD d hdD).1).le
    have hQTcast : (Q : ℚ) ≤ (T : ℚ) := by
      dsimp [Q, T]
      linarith
    have hQT : Q ≤ T := by exact_mod_cast hQTcast
    have hsubcast : ((T - Q : ℕ) : ℚ) = (T : ℚ) - (Q : ℚ) := by
      rw [Nat.cast_sub hQT]
    have hFle : localFractionMass D (n - 1) ≤ ((T - Q : ℕ) : ℚ) := by
      rw [hsubcast]
      dsimp [Q, T] at hscaled ⊢
      linarith
    have hFpos : 0 < localFractionMass D (n - 1) := by
      have : (0 : ℚ) < (E.card : ℚ) / 2 := by
        positivity
      linarith
    have hQTltCast : (Q : ℚ) < (T : ℚ) := by
      dsimp [Q, T] at hscaled ⊢
      linarith
    have hQTlt : Q < T := by exact_mod_cast hQTltCast
    have hcardltCast :
        (E.card : ℚ) < 2 * ((T - Q : ℕ) : ℚ) := by
      linarith
    have hcardlt : E.card < 2 * (T - Q) := by
      exact_mod_cast hcardltCast
    rw [hendpoint]
    unfold localBinarySuffix
    dsimp [Q, T] at hQTlt hcardlt ⊢
    omega
  · have hzero : endpointDivisorContribution D n = 0 := by
      have hEempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
      have hfilter : (D.filter fun d ↦ d ∣ n) = ∅ := by
        simpa [E] using hEempty
      unfold endpointDivisorContribution
      rw [hfilter]
      simp
    rw [hzero]
    omega

/-- The endpoint repair coefficient is nonnegative as a theorem, not as a
feasibility hypothesis. -/
theorem localRepairInteger_nonneg
    {D : Finset ℕ} {k n : ℕ}
    (hk : k < n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n / 2)
    (hprefix : RationalHalfCutoffUndershoot D k) :
    0 ≤ localRepairInteger D k n := by
  have h := endpointDivisorContribution_le_two_mul_localBinarySuffix_add_one
    hk hD hprefix
  unfold localRepairInteger
  have h' : (endpointDivisorContribution D n : ℤ) ≤
      2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 := by
    exact_mod_cast h
  omega

/-- Elementary growth bound used by the direct endpoint-feasibility route. -/
theorem nat_le_two_pow_pred (S : ℕ) :
    S ≤ 2 ^ (S - 1) := by
  cases S with
  | zero => simp
  | succ s =>
      change s + 1 ≤ 2 ^ s
      induction s with
      | zero => simp
      | succ s ih =>
          rw [pow_succ]
          omega

/-- A direct, purely integral sufficient condition for repair feasibility.
Writing `S` for the endpoint divisor contribution and `A` for the preceding
binary suffix, the hypothesis `2^(S-1)-1 ≤ A` implies `S ≤ 2A+1`, hence
`H = 2A+1-S ≥ 0`.  This theorem deliberately does not assert that the
exponential hypothesis always holds. -/
theorem localRepairInteger_nonneg_of_exponential_endpoint_bound
    {D : Finset ℕ} {k n : ℕ}
    (hbound :
      2 ^ (endpointDivisorContribution D n - 1) - 1 ≤
        localBinarySuffix D k (n - 1)) :
    0 ≤ localRepairInteger D k n := by
  let S := endpointDivisorContribution D n
  let A := localBinarySuffix D k (n - 1)
  change 2 ^ (S - 1) - 1 ≤ A at hbound
  have hpowpos : 0 < 2 ^ (S - 1) := Nat.two_pow_pos _
  have hpowle : 2 ^ (S - 1) ≤ A + 1 := by omega
  have hSA : S ≤ A + 1 := (nat_le_two_pow_pred S).trans hpowle
  have hS2 : S ≤ 2 * A + 1 := by omega
  have hS2z : (S : ℤ) ≤ 2 * (A : ℤ) + 1 := by exact_mod_cast hS2
  unfold localRepairInteger
  change 0 ≤ 2 * (A : ℤ) + 1 - (S : ℤ)
  omega

/-- At a least defect whose current Lambert digit is one, Möbius inversion
forces the new coefficient to be `1-S`, where `S` is the contribution of the
already frozen proper divisors. -/
theorem mobiusCoefficient_eq_one_sub_endpointDivisorContribution
    {D : Finset ℕ} {p a : ℕ → ℤ} {n : ℕ}
    (hp : p n = 1)
    (hconv : p n = a n + (endpointDivisorContribution D n : ℤ)) :
    a n = 1 - (endpointDivisorContribution D n : ℤ) := by
  omega

/-- Exact decomposition of the repair value into twice the preceding carry
plus the least-defect Möbius coefficient `1-S`. -/
theorem localRepairInteger_eq_two_mul_suffix_add_one_sub_endpoint
    (D : Finset ℕ) (k n : ℕ) :
    localRepairInteger D k n =
      2 * (localBinarySuffix D k (n - 1) : ℤ) +
        (1 - (endpointDivisorContribution D n : ℤ)) := by
  unfold localRepairInteger
  ring

/-- A genuine negative least defect (`S ≥ 2`) gives the strict estimate
`H < 2A` used to localize the binary repair block. -/
theorem localRepairInteger_lt_two_mul_suffix_of_two_le_endpoint
    {D : Finset ℕ} {k n : ℕ}
    (hendpoint : 2 ≤ endpointDivisorContribution D n) :
    localRepairInteger D k n <
      2 * (localBinarySuffix D k (n - 1) : ℤ) := by
  unfold localRepairInteger
  have hendpoint' : (2 : ℤ) ≤ endpointDivisorContribution D n := by
    exact_mod_cast hendpoint
  omega

/-- A repair update supported from `r` onward leaves every coefficient below
the left cutoff literally unchanged.  Increasing left endpoints therefore
freeze each fixed prefix after finitely many local repairs. -/
theorem repair_update_frozen_below_left
    (a q : ℕ → ℤ) {r m : ℕ}
    (hq : ∀ j < r, q j = 0) (hm : m < r) :
    a m + q m = a m := by
  rw [hq m hm, add_zero]

/-- The endpoint repair always fits in the full binary window `(k,n]`.
Localizing the same word to the much shorter upper-half window is a separate
capacity question, isolated below. -/
theorem localRepairInteger_lt_fullWindowCapacity
    {D : Finset ℕ} {k n : ℕ} (hk : k < n) :
    localRepairInteger D k n < (2 ^ (n - k) : ℕ) := by
  let A := localBinarySuffix D k (n - 1)
  let T := 2 ^ (n - 1 - k)
  have hTpos : 0 < T := by
    dsimp [T]
    exact Nat.two_pow_pos _
  have hA : A < T := by
    dsimp [A, T]
    unfold localBinarySuffix
    omega
  have hpow : 2 ^ (n - k) = 2 * T := by
    have hexp : n - k = (n - 1 - k) + 1 := by omega
    rw [hexp, pow_succ]
    dsimp [T]
    ring
  have hAcast : (A : ℤ) < (T : ℤ) := by exact_mod_cast hA
  rw [hpow]
  unfold localRepairInteger
  dsimp [A]
  push_cast
  have hS : (0 : ℤ) ≤ endpointDivisorContribution D n := by positivity
  omega

/-! ## Finite binary repair words -/

/-- Signed dyadic value of a least-significant-digit-first coefficient word. -/
def signedDyadicValue : List ℤ → ℤ
  | [] => 0
  | z :: zs => z + 2 * signedDyadicValue zs

theorem signedDyadicValue_natCast (y : List ℕ) :
    signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
      (Nat.ofDigits 2 y : ℤ) := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [signedDyadicValue, Nat.ofDigits, ih]

/-- The dyadic value of a Boolean word of length `L` is strictly below
`2^L`.  This is the exact capacity bound used by both repair constructors. -/
theorem signedDyadicValue_boolean_lt_two_pow
    {y : List ℕ} (hbool : ∀ b ∈ y, b = 0 ∨ b = 1) :
    signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) <
      (2 ^ y.length : ℕ) := by
  rw [signedDyadicValue_natCast]
  have hdigit : ∀ b ∈ y, b < 2 := by
    intro b hb
    rcases hbool b hb with rfl | rfl <;> omega
  have h := Nat.ofDigits_lt_base_pow_length (by omega : 1 < 2) hdigit
  exact_mod_cast h

/-- Every natural below `2^L` has a Boolean word of length exactly `L`. -/
theorem exists_boolean_word_of_lt_two_pow
    {V L : ℕ} (hV : V < 2 ^ L) :
    ∃ y : List ℕ,
      y.length = L ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      Nat.ofDigits 2 y = V := by
  let y := Nat.digitsAppend 2 L V
  refine ⟨y, Nat.length_digitsAppend (by omega) L hV, ?_, ?_⟩
  · intro b hb
    have hblt := Nat.lt_of_mem_digitsAppend (by omega : 1 < 2) L b hb
    omega
  · simp [y, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
      Nat.ofDigits_digits]

/-- A signed block whose nonnegative value fits in its width can be replaced
by a Boolean block of the same width without changing its dyadic value. -/
theorem exists_boolean_replacement_of_signedDyadicValue
    (a : List ℤ) {V : ℕ}
    (ha : signedDyadicValue a = (V : ℤ))
    (hfit : V < 2 ^ a.length) :
    ∃ y : List ℕ,
      y.length = a.length ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        signedDyadicValue a := by
  obtain ⟨y, hylen, hybool, hyvalue⟩ := exists_boolean_word_of_lt_two_pow hfit
  refine ⟨y, hylen, hybool, ?_⟩
  calc
    signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        (Nat.ofDigits 2 y : ℤ) := signedDyadicValue_natCast y
    _ = (V : ℤ) := by exact_mod_cast hyvalue
    _ = signedDyadicValue a := ha.symm

/-- The nonnegative endpoint repair has an unconditional Boolean realization
on the full window `(k,n]`.  This is the finite unchanged-value repair before
the locality requirement `r > n/2` is imposed. -/
theorem exists_fullWindow_boolean_word_for_localRepairInteger
    {D : Finset ℕ} {k n : ℕ}
    (hk : k < n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n / 2)
    (hprefix : RationalHalfCutoffUndershoot D k) :
    ∃ y : List ℕ,
      y.length = n - k ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        localRepairInteger D k n := by
  have hnonneg := localRepairInteger_nonneg hk hD hprefix
  let V := (localRepairInteger D k n).toNat
  have hVcast : (V : ℤ) = localRepairInteger D k n := by
    dsimp [V]
    exact Int.toNat_of_nonneg hnonneg
  have hVfit : V < 2 ^ (n - k) := by
    have hfit := localRepairInteger_lt_fullWindowCapacity (D := D) hk
    rw [← hVcast] at hfit
    exact_mod_cast hfit
  obtain ⟨y, hylen, hybool, hyvalue⟩ := exists_boolean_word_of_lt_two_pow hVfit
  refine ⟨y, hylen, hybool, ?_⟩
  calc
    signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        (Nat.ofDigits 2 y : ℤ) := signedDyadicValue_natCast y
    _ = (V : ℤ) := by exact_mod_cast hyvalue
    _ = localRepairInteger D k n := hVcast

/-- Number of binary coordinates in the strict upper half interval
`(⌊n/2⌋, n]`.  A word of this length is read from `n` down to `⌊n/2⌋+1`. -/
def upperHalfRepairLength (n : ℕ) : ℕ :=
  n - n / 2

/-- The carry left by the frozen prefix fits below half of the strict
upper-half binary capacity.  Unlike `RationalHalfCutoffUndershoot`, this is
not a remaining analytic hypothesis: it follows from the already-Boolean
upper suffix once the exact carry/suffix identity is supplied. -/
def UpperHalfCarryCapacity (D : Finset ℕ) (k n : ℕ) : Prop :=
  localBinarySuffix D k (n - 1) ≤
    2 ^ (upperHalfRepairLength n - 1)

/-- Least-significant-digit-first word cut from coefficients on `(R,M]`. -/
def upperSuffixWord (a : ℕ → ℕ) (R M : ℕ) : List ℕ :=
  List.map (fun i ↦ a (M - i)) (List.range (M - R))

@[simp] theorem upperSuffixWord_length (a : ℕ → ℕ) (R M : ℕ) :
    (upperSuffixWord a R M).length = M - R := by
  simp [upperSuffixWord]

theorem upperSuffixWord_boolean
    {a : ℕ → ℕ} {R M : ℕ}
    (ha : ∀ m, R < m → m ≤ M → a m = 0 ∨ a m = 1) :
    ∀ b ∈ upperSuffixWord a R M, b = 0 ∨ b = 1 := by
  intro b hb
  rw [upperSuffixWord, List.mem_map] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  have hi' : i < M - R := List.mem_range.mp hi
  exact ha (M - i) (by omega) (by omega)

/-- Booleanity of the already constructed suffix through `n-1` supplies the
undershoot automatically: a word on the `upperHalfRepairLength n - 1`
available positions has value strictly below that power of two.  The remaining
global adapter only has to identify the carry `A` with this suffix value. -/
theorem UpperHalfCarryCapacity.of_boolean_suffix
    {D : Finset ℕ} {k n : ℕ} {y : List ℕ}
    (hylen : y.length = upperHalfRepairLength n - 1)
    (hybool : ∀ b ∈ y, b = 0 ∨ b = 1)
    (hyvalue : Nat.ofDigits 2 y = localBinarySuffix D k (n - 1)) :
    UpperHalfCarryCapacity D k n := by
  have hdigit : ∀ b ∈ y, b < 2 := by
    intro b hb
    rcases hybool b hb with rfl | rfl <;> omega
  have hlt := Nat.ofDigits_lt_base_pow_length (by omega : 1 < 2) hdigit
  unfold UpperHalfCarryCapacity
  rw [← hyvalue, ← hylen]
  exact hlt.le

/-- Coefficient-level adapter for the global repair process.  Booleanity on
`(⌊n/2⌋,n-1]` plus the exact carry/suffix identity supplies the local
undershoot with no additional analytic estimate. -/
theorem UpperHalfCarryCapacity.of_boolean_coefficients
    {D : Finset ℕ} {k n : ℕ} {a : ℕ → ℕ}
    (hn : 0 < n)
    (ha : ∀ m, n / 2 < m → m < n → a m = 0 ∨ a m = 1)
    (hvalue : Nat.ofDigits 2 (upperSuffixWord a (n / 2) (n - 1)) =
      localBinarySuffix D k (n - 1)) :
    UpperHalfCarryCapacity D k n := by
  apply UpperHalfCarryCapacity.of_boolean_suffix
    (y := upperSuffixWord a (n / 2) (n - 1))
  · simp [upperHalfRepairLength]
    omega
  · exact upperSuffixWord_boolean fun m hmR hmM ↦ ha m hmR (by omega)
  · exact hvalue

/-- The strict `H < 2A` estimate turns the supplied lower-prefix undershoot
into the exact upper-half capacity bound. -/
theorem localRepairInteger_lt_upperHalfCapacity_of_carryCapacity
    {D : Finset ℕ} {k n : ℕ}
    (hk : k < n)
    (hendpoint : 2 ≤ endpointDivisorContribution D n)
    (hcapacity : UpperHalfCarryCapacity D k n) :
    localRepairInteger D k n < (2 ^ upperHalfRepairLength n : ℕ) := by
  have hn : 0 < n := by omega
  have hLpos : 0 < upperHalfRepairLength n := by
    unfold upperHalfRepairLength
    omega
  have hH := localRepairInteger_lt_two_mul_suffix_of_two_le_endpoint
    (D := D) (k := k) hendpoint
  have hA : (localBinarySuffix D k (n - 1) : ℤ) ≤
      (2 ^ (upperHalfRepairLength n - 1) : ℕ) := by
    unfold UpperHalfCarryCapacity at hcapacity
    exact_mod_cast hcapacity
  have hpow : (2 : ℕ) ^ upperHalfRepairLength n =
      2 * 2 ^ (upperHalfRepairLength n - 1) := by
    have hexp : upperHalfRepairLength n =
        (upperHalfRepairLength n - 1) + 1 := by omega
    calc
      (2 : ℕ) ^ upperHalfRepairLength n =
          2 ^ ((upperHalfRepairLength n - 1) + 1) :=
        congrArg (fun e : ℕ ↦ (2 : ℕ) ^ e) hexp
      _ = 2 ^ (upperHalfRepairLength n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (upperHalfRepairLength n - 1) := by omega
  have htwice :
      2 * (localBinarySuffix D k (n - 1) : ℤ) ≤
        2 * ((2 ^ (upperHalfRepairLength n - 1) : ℕ) : ℤ) :=
    mul_le_mul_of_nonneg_left hA (by norm_num)
  have hfitZ : localRepairInteger D k n <
      ((2 ^ upperHalfRepairLength n : ℕ) : ℤ) := by
    calc
      localRepairInteger D k n <
          2 * (localBinarySuffix D k (n - 1) : ℤ) := hH
      _ ≤ 2 * ((2 ^ (upperHalfRepairLength n - 1) : ℕ) : ℤ) := htwice
      _ = ((2 ^ upperHalfRepairLength n : ℕ) : ℤ) := by
        exact_mod_cast hpow.symm
  exact_mod_cast hfitZ

/-- Conditional block realization of the endpoint repair integer.  The
fractional-part theorem supplies nonnegativity.  The only remaining local
feasibility input is the genuine capacity bound `H < 2^(n-⌊n/2⌋)`. -/
theorem exists_upperHalf_boolean_word_for_localRepairInteger
    {D : Finset ℕ} {k n : ℕ}
    (hk : k < n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n / 2)
    (hprefix : RationalHalfCutoffUndershoot D k)
    (hfit : localRepairInteger D k n <
      (2 ^ upperHalfRepairLength n : ℕ)) :
    ∃ y : List ℕ,
      y.length = upperHalfRepairLength n ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        localRepairInteger D k n := by
  have hnonneg := localRepairInteger_nonneg hk hD hprefix
  let V := (localRepairInteger D k n).toNat
  have hVcast : (V : ℤ) = localRepairInteger D k n := by
    dsimp [V]
    exact Int.toNat_of_nonneg hnonneg
  have hVfit : V < 2 ^ upperHalfRepairLength n := by
    have hfit' := hfit
    rw [← hVcast] at hfit'
    exact_mod_cast hfit'
  obtain ⟨y, hylen, hybool, hyvalue⟩ := exists_boolean_word_of_lt_two_pow hVfit
  refine ⟨y, hylen, hybool, ?_⟩
  calc
    signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        (Nat.ofDigits 2 y : ℤ) := signedDyadicValue_natCast y
    _ = (V : ℤ) := by exact_mod_cast hyvalue
    _ = localRepairInteger D k n := hVcast

/-- Rational half-cutoff undershoot plus the automatically supplied carry
capacity yields the actual Boolean repair on `(⌊n/2⌋,n]`. -/
theorem exists_upperHalf_boolean_word_of_repair_inputs
    {D : Finset ℕ} {k n : ℕ}
    (hk : k < n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n / 2)
    (hprefix : RationalHalfCutoffUndershoot D k)
    (hendpoint : 2 ≤ endpointDivisorContribution D n)
    (hcapacity : UpperHalfCarryCapacity D k n) :
    ∃ y : List ℕ,
      y.length = upperHalfRepairLength n ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        localRepairInteger D k n := by
  exact exists_upperHalf_boolean_word_for_localRepairInteger
    hk hD hprefix
      (localRepairInteger_lt_upperHalfCapacity_of_carryCapacity
        hk hendpoint hcapacity)

/-- Coefficient-level form in which upper-half capacity is discharged from
the already-Boolean suffix and its exact value.  The only analytic hypothesis
in this route is `RationalHalfCutoffUndershoot`. -/
theorem exists_upperHalf_boolean_word_of_boolean_suffix
    {D : Finset ℕ} {k n : ℕ} {a : ℕ → ℕ}
    (hk : k < n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n / 2)
    (hprefix : RationalHalfCutoffUndershoot D k)
    (hendpoint : 2 ≤ endpointDivisorContribution D n)
    (hn : 0 < n)
    (ha : ∀ m, n / 2 < m → m < n → a m = 0 ∨ a m = 1)
    (hvalue : Nat.ofDigits 2 (upperSuffixWord a (n / 2) (n - 1)) =
      localBinarySuffix D k (n - 1)) :
    ∃ y : List ℕ,
      y.length = upperHalfRepairLength n ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        localRepairInteger D k n := by
  exact exists_upperHalf_boolean_word_of_repair_inputs
    hk hD hprefix hendpoint
      (UpperHalfCarryCapacity.of_boolean_coefficients hn ha hvalue)

/-- Unchanged-value form of the upper-half repair.  Once the supplied signed
block has endpoint value `H`, the rational undershoot and Boolean-suffix
capacity replace it by a Boolean block on the same coordinates without
changing its dyadic value. -/
theorem exists_upperHalf_boolean_replacement_of_repair_inputs
    (a : List ℤ) {D : Finset ℕ} {k n : ℕ}
    (hk : k < n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n / 2)
    (hprefix : RationalHalfCutoffUndershoot D k)
    (hendpoint : 2 ≤ endpointDivisorContribution D n)
    (hcapacity : UpperHalfCarryCapacity D k n)
    (hlen : a.length = upperHalfRepairLength n)
    (hvalue : signedDyadicValue a = localRepairInteger D k n) :
    ∃ y : List ℕ,
      y.length = a.length ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        signedDyadicValue a := by
  obtain ⟨y, hylen, hybool, hyvalue⟩ :=
    exists_upperHalf_boolean_word_of_repair_inputs
      hk hD hprefix hendpoint hcapacity
  refine ⟨y, hylen.trans hlen.symm, hybool, ?_⟩
  calc
    signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        localRepairInteger D k n := hyvalue
    _ = signedDyadicValue a := hvalue.symm

/-- Final coefficient-level unchanged-value repair theorem.  Booleanity and
the exact value of the existing upper suffix discharge capacity; a signed
block of endpoint value `H` is replaced on the same coordinates by a Boolean
block without changing its dyadic value. -/
theorem exists_upperHalf_boolean_replacement_of_boolean_suffix
    (block : List ℤ) {D : Finset ℕ} {k n : ℕ} {a : ℕ → ℕ}
    (hk : k < n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n / 2)
    (hprefix : RationalHalfCutoffUndershoot D k)
    (hendpoint : 2 ≤ endpointDivisorContribution D n)
    (hn : 0 < n)
    (ha : ∀ m, n / 2 < m → m < n → a m = 0 ∨ a m = 1)
    (hsuffix : Nat.ofDigits 2 (upperSuffixWord a (n / 2) (n - 1)) =
      localBinarySuffix D k (n - 1))
    (hlen : block.length = upperHalfRepairLength n)
    (hblock : signedDyadicValue block = localRepairInteger D k n) :
    ∃ y : List ℕ,
      y.length = block.length ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
        signedDyadicValue block := by
  exact exists_upperHalf_boolean_replacement_of_repair_inputs
    block hk hD hprefix hendpoint
      (UpperHalfCarryCapacity.of_boolean_coefficients hn ha hsuffix)
      hlen hblock

end Erdos249257
