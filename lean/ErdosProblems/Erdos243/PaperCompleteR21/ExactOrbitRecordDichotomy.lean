import ErdosProblems.Erdos243.ReciprocalTailRigidity
import ErdosProblems.Erdos243.PaperCompleteR11.QuantitativeRecordDichotomy
import ErdosProblems.Erdos243.PaperCompleteR21.SlowGrowthProductIncrements

/-!
# Erdős 243: the record limsup of a general exact orbit, and `long243:res:slownegative`

The paper's proof of `long243:res:recorddichotomy` (core.tex:1732) opens with an
*auxiliary lower bound*:

> We first prove the auxiliary lower bound `Θ ≥ 1`. This part needs only an
> exact positive integer orbit with `a_n > 1`, `D_0 ≥ 1`, `|E_n|/C_n → 0` and
> error not eventually zero. In particular, it will also apply to the abstract
> orbit in Theorem `long243:res:slownegative`.

In the tree that lower bound existed only in the *canonical* coordinates of a
rational reciprocal sum (`PaperCompleteR11.canonical_recordTheta_gt_one`, which
additionally assumes `StrictMono a`, `HasSum (1/aₙ) = p/q` and
`a_{n+1}/a_n² → 1`).  This file proves it for an arbitrary exact orbit
(`exactOrbit_one_le_recordTheta`), and then proves `long243:res:slownegative`
(core.tex:2203) with no extra hypothesis.

## How the general orbit is fed into the existing block machinery

`PaperCompleteR11.RecordGrowthOrbit` packages exactly the growth data the
CRT-block argument consumes.  All of its fields are derived here from
`a_n > 1`, `C_n > 0`, `D_0 ≥ 1`, the two exact recurrences and vanishing
relative error, after shifting to a late index that attains a global record of
`C` (so that `runningMax_shift_at_record` keeps the original running maximum):

* `U_pos`, `D_pos`, `U_step`, `D_step`, `a_pos` are immediate;
* `unbounded`: zero is absorbing for the centred state on a tail
  (`centeredState_zero_absorbing`), so an error that is not eventually zero is
  nowhere zero on that tail, and `tailState_tendsto_atTop_of_nonzero_normalizedVanishes`
  gives `C n → ∞`;
* `record_bound`: `2|E n| < C n` gives `C (n+1) ≤ 2 C n`, hence an exponential
  envelope for the running maximum;
* `den_bound`: `4|E n| < C n` gives `4 C (n+1) ≤ 5 C n`, hence `a n ≤ 1 + D n`
  and `2 D (n+1) ≤ (2 D n)²`, which is the `binaryTower` recursion;
* `lower` and `increasing`: the missing bootstrap.  The exact recurrences plus
  `4|E n| < C n` give the clean integer inequality
  `4 a_n² ≤ 5 a_{n+1} + 5 a_n` (`tail_multiplier_quadratic_lower`), which is the
  division-free form of the paper's `a_{n+1} ≈ a_n² - a_n + 1`.  Once
  `a_n ≥ 4` it yields `a_n² ≤ 2 a_{n+1}`, hence both strict monotonicity and
  the doubly exponential lower bound `2 · binaryTower k ≤ a (N+k)`.  That
  `a_n ≥ 4` happens at all follows from `D n ≥ 2ⁿ` against `4 C (n+1) ≤ 5 C n`:
  `a_n ≥ D_n / C_n` grows at least like `(8/5)ⁿ`.

`RecordGrowthOrbit.cofinal_inclusive_record` then supplies a cofinal record
excess at coefficient `c > 1`, and `ereal_limsup_gt_one_of_cofinal` turns it
into `1 < recordTheta C`.

## Credit

`slowNegative_bound_of_negative_part` and the final assembly of
`slowNegative_eventually_zero_and_sylvesterNext_unconditional` follow
`PaperCompleteR21/SlowNegativePartRecord.lean` (slice `s243_e`), which proved
everything except the lower half and carried it as the hypothesis
`hdichotomy`; that file has no `.olean`, so the two short arguments are
repeated here under fresh names rather than imported.  Its upper half
`recordTheta_le_of_slow_negative` (slice `s243_b`,
`PaperCompleteR21/SlowGrowthProductIncrements.lean`) is imported.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open ErdosProblems.Erdos243
open ErdosProblems.Erdos243.PaperCompleteR11

/-! ## 1. A crude exponential gap -/

/-- `(8/5)^m → ∞`, in the division-free form needed below. -/
theorem exists_five_eight_gap (c : ℕ) : ∃ m : ℕ, c * 5 ^ m < 8 ^ m := by
  refine ⟨3 * (c + 1), ?_⟩
  have h1 : c < 4 ^ (c + 1) := by
    have hc : c < 2 ^ c := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ c ≤ 4 ^ c := Nat.pow_le_pow_left (by norm_num) c
    have h3 : (4 : ℕ) ^ c ≤ 4 ^ (c + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : (5 : ℕ) ^ (3 * (c + 1)) = 125 ^ (c + 1) := by
    rw [pow_mul]; norm_num
  have h3 : (8 : ℕ) ^ (3 * (c + 1)) = 512 ^ (c + 1) := by
    rw [pow_mul]; norm_num
  rw [h2, h3]
  have hpos : 0 < (125 : ℕ) ^ (c + 1) := by positivity
  calc c * 125 ^ (c + 1) < 4 ^ (c + 1) * 125 ^ (c + 1) :=
        Nat.mul_lt_mul_of_lt_of_le h1 (le_refl _) hpos
  _ = 500 ^ (c + 1) := by rw [← Nat.mul_pow]
  _ ≤ 512 ^ (c + 1) := Nat.pow_le_pow_left (by norm_num) _

/-! ## 2. The exact-orbit growth bootstrap -/

section ExactOrbit

variable (a C D : ℕ → ℕ) (E : ℕ → ℤ)

/-- `D n ≥ 2ⁿ` on an exact orbit with `a n > 1` and `D 0 ≥ 1`. -/
theorem den_ge_two_pow (ha : ∀ n, 1 < a n) (hD0 : 1 ≤ D 0)
    (hD : ∀ n, D (n + 1) = a n * D n) : ∀ n, 2 ^ n ≤ D n := by
  intro n
  induction n with
  | zero => simpa using hD0
  | succ n ih =>
      have h2 : 2 ≤ a n := ha n
      calc (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≤ a n * D n := Nat.mul_le_mul h2 ih
      _ = D (n + 1) := (hD n).symm

/-- `4 |E n| < C n` gives `4 C (n+1) ≤ 5 C n`. -/
theorem tail_four_five (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hsmall : 4 * Int.natAbs (E n) < C n) :
    4 * C (n + 1) ≤ 5 * C n := by
  have hTail : (C (n + 1) : ℤ) = (C n : ℤ) - E n :=
    natTail_eq_sub_centeredState a C D E hC hE n
  omega

/-- `2 |E n| < C n` gives `C (n+1) ≤ 2 C n`. -/
theorem tail_two (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hsmall : 2 * Int.natAbs (E n) < C n) :
    C (n + 1) ≤ 2 * C n := by
  have hTail : (C (n + 1) : ℤ) = (C n : ℤ) - E n :=
    natTail_eq_sub_centeredState a C D E hC hE n
  omega

/-- `a n ≤ 1 + D n`: the multiplier is controlled by the denominator. -/
theorem multiplier_le_den (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hsmall : 4 * Int.natAbs (E n) < C n) :
    a n ≤ 1 + D n := by
  have h1 : 4 * C (n + 1) ≤ 5 * C n := tail_four_five a C D E hC hE n hsmall
  have h2 : C (n + 1) + D n = a n * C n := hC n
  have h3 : 4 * (a n * C n) ≤ 5 * C n + 4 * D n := by omega
  have h4 : 1 ≤ C n := hCpos n
  nlinarith [h3, h4]

/-- **The growth bootstrap.**  The exact recurrences plus `4 |E n| < C n` give
`4 a_n² ≤ 5 a_{n+1} + 5 a_n`, the division-free form of the paper's
`a_{n+1} ≈ a_n² - a_n + 1`. -/
theorem tail_multiplier_quadratic_lower
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hsmall : 4 * Int.natAbs (E n) < C n) :
    4 * a n ^ 2 ≤ 5 * a (n + 1) + 5 * a n := by
  have hTail : (C (n + 1) : ℤ) = (C n : ℤ) - E n :=
    natTail_eq_sub_centeredState a C D E hC hE n
  have hEdef : E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ) := by
    rw [hE n, centeredState]
  have hEbound : -((C n : ℤ)) < 4 * E n ∧ 4 * E n < (C n : ℤ) := by omega
  have hCn : (0 : ℤ) < (C n : ℤ) := by exact_mod_cast hCpos n
  have hCn1 : (0 : ℤ) < (C (n + 1) : ℤ) := by exact_mod_cast hCpos (n + 1)
  have hCn2 : (0 : ℤ) ≤ (C (n + 2) : ℤ) := Int.natCast_nonneg _
  have hAnn : (0 : ℤ) ≤ (a (n + 1) : ℤ) := Int.natCast_nonneg _
  have hAn : (2 : ℤ) ≤ (a n : ℤ) := by exact_mod_cast ha n
  -- `4 C (n+1) ≤ 5 C n`
  have h1 : (4 : ℤ) * (C (n + 1) : ℤ) ≤ 5 * (C n : ℤ) := by omega
  -- `(4 a n - 5) C n ≤ 4 D n`
  have h2 : (4 * (a n : ℤ) - 5) * (C n : ℤ) ≤ 4 * (D n : ℤ) := by
    have := hEbound.1
    nlinarith [hEdef]
  -- `a (n+1) C (n+1) = C (n+2) + a n D n`
  have h3 : (a (n + 1) : ℤ) * (C (n + 1) : ℤ)
      = (C (n + 2) : ℤ) + (a n : ℤ) * (D n : ℤ) := by
    have e1 : ((C (n + 2) + D (n + 1) : ℕ) : ℤ) = ((a (n + 1) * C (n + 1) : ℕ) : ℤ) := by
      exact_mod_cast congrArg (fun t : ℕ ↦ (t : ℤ)) (hC (n + 1))
    have e2 : ((D (n + 1) : ℕ) : ℤ) = ((a n * D n : ℕ) : ℤ) := by
      exact_mod_cast congrArg (fun t : ℕ ↦ (t : ℤ)) (hD n)
    push_cast at e1 e2
    linarith
  -- assemble
  have hbig : (4 * (a n : ℤ) ^ 2 - 5 * (a n : ℤ)) * (C n : ℤ)
      ≤ (5 * (a (n + 1) : ℤ)) * (C n : ℤ) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hAnn, mul_le_mul_of_nonneg_left h2
      (le_trans (by norm_num : (0:ℤ) ≤ 2) hAn), h3, hCn2]
  have hdiv := le_of_mul_le_mul_right hbig hCn
  have hfinal : (4 : ℤ) * (a n : ℤ) ^ 2 ≤ 5 * (a (n + 1) : ℤ) + 5 * (a n : ℤ) := by
    linarith
  exact_mod_cast hfinal

/-- `a n ≥ 4` forces `a n ² ≤ 2 a (n+1)`, hence a strict rise. -/
theorem tail_square_step
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hsmall : 4 * Int.natAbs (E n) < C n) (h4 : 4 ≤ a n) :
    a n ^ 2 ≤ 2 * a (n + 1) := by
  have hkey := tail_multiplier_quadratic_lower a C D E ha hCpos hC hD hE n hsmall
  nlinarith [hkey, h4]

/-- A geometric envelope for the numerator along the tail. -/
theorem tail_geometric_bound (N : ℕ)
    (h : ∀ n, N ≤ n → 4 * C (n + 1) ≤ 5 * C n) :
    ∀ m, 4 ^ m * C (N + m) ≤ 5 ^ m * C N := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := h (N + m) (by omega)
      calc (4 : ℕ) ^ (m + 1) * C (N + (m + 1))
          = 4 ^ m * (4 * C ((N + m) + 1)) := by
            rw [show N + (m + 1) = (N + m) + 1 by omega]; ring
      _ ≤ 4 ^ m * (5 * C (N + m)) := Nat.mul_le_mul (le_refl _) hstep
      _ = 5 * (4 ^ m * C (N + m)) := by ring
      _ ≤ 5 * (5 ^ m * C N) := Nat.mul_le_mul (le_refl _) ih
      _ = 5 ^ (m + 1) * C N := by ring

/-- **The multiplier eventually exceeds `4`.**  `D n ≥ 2ⁿ` against the
geometric envelope `4 C (n+1) ≤ 5 C n` makes `a n ≥ D n / C n` grow at least
like `(8/5)ⁿ`. -/
theorem exists_multiplier_ge_four
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (M : ℕ) :
    ∃ t, M ≤ t ∧ N ≤ t ∧ 4 ≤ a t := by
  classical
  set S := max M N with hS
  have hSN : N ≤ S := le_max_right _ _
  have hSM : M ≤ S := le_max_left _ _
  have hgeo : ∀ m, 4 ^ m * C (S + m) ≤ 5 ^ m * C S :=
    tail_geometric_bound C S (fun n hn ↦ tail_four_five a C D E hC hE n (hN n (by omega)))
  obtain ⟨m, hm0⟩ := exists_five_eight_gap (4 * C S)
  have hm : 4 * (5 ^ m * C S) < 8 ^ m := by
    calc 4 * (5 ^ m * C S) = 4 * C S * 5 ^ m := by ring
    _ < 8 ^ m := hm0
  refine ⟨S + m, by omega, by omega, ?_⟩
  by_contra hcon
  have hle : a (S + m) ≤ 4 := by omega
  -- `4 ^ m * D (S+m) ≤ a (S+m) * (4 ^ m * C (S+m)) ≤ 4 * 5 ^ m * C S`
  have hDle : D (S + m) ≤ a (S + m) * C (S + m) := by
    have := hC (S + m); omega
  have hchain : 8 ^ m ≤ 4 * (5 ^ m * C S) := by
    calc (8 : ℕ) ^ m = 4 ^ m * 2 ^ m := by rw [← Nat.mul_pow]
    _ ≤ 4 ^ m * D (S + m) := by
        refine Nat.mul_le_mul (le_refl _) (le_trans ?_ (den_ge_two_pow a D ha hD0 hD (S + m)))
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 4 ^ m * (a (S + m) * C (S + m)) := Nat.mul_le_mul (le_refl _) hDle
    _ = a (S + m) * (4 ^ m * C (S + m)) := by ring
    _ ≤ 4 * (4 ^ m * C (S + m)) := Nat.mul_le_mul hle (le_refl _)
    _ ≤ 4 * (5 ^ m * C S) := Nat.mul_le_mul (le_refl _) (hgeo m)
  omega

/-- **The doubly exponential lower bound.**  From `a N ≥ 4` the square step
gives `2 · binaryTower k ≤ a (N + k)` for every `k`. -/
theorem tail_binaryTower_lower
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (h4 : 4 ≤ a N) :
    ∀ k, 2 * binaryTower k ≤ a (N + k) := by
  intro k
  induction k with
  | zero => simpa [binaryTower] using h4
  | succ k ih =>
      have hbt : 2 ≤ binaryTower k := by
        have := binaryTower_mono (Nat.zero_le k)
        simpa [binaryTower] using this
      have h4k : 4 ≤ a (N + k) := by omega
      have hsq := tail_square_step a C D E ha hCpos hC hD hE (N + k)
        (hN (N + k) (by omega)) h4k
      have hstep : (2 * binaryTower k) ^ 2 ≤ a (N + k) ^ 2 :=
        Nat.pow_le_pow_left ih 2
      have hsucc : binaryTower (k + 1) = binaryTower k ^ 2 := binaryTower_succ k
      have hexp : (2 * binaryTower k) ^ 2 = 4 * binaryTower (k + 1) := by
        rw [hsucc]; ring
      have : 4 * binaryTower (k + 1) ≤ 2 * a (N + k + 1) := by omega
      have heq : N + (k + 1) = N + k + 1 := by omega
      rw [heq]
      omega

end ExactOrbit

/-! ## 3. The numerator is unbounded -/

/-- If the centred error is not eventually zero then `C n → ∞`.  Zero is
absorbing on the tail where `|E n| < C n`, so the error is nowhere zero there
and `tailState_tendsto_atTop_of_nonzero_normalizedVanishes` applies. -/
theorem exactOrbit_unbounded_of_error_not_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∀ H : ℕ, ∃ n, H ≤ C n := by
  obtain ⟨N, hN⟩ := hvanish 1
  -- shift to `N`, where the centring bound holds at every index
  set a' : ℕ → ℕ := fun n ↦ a (N + n) with ha'
  set C' : ℕ → ℕ := fun n ↦ C (N + n) with hC'
  set D' : ℕ → ℕ := fun n ↦ D (N + n) with hD'
  set E' : ℕ → ℤ := fun n ↦ E (N + n) with hE'
  have hC1 : ∀ n, C' (n + 1) + D' n = a' n * C' n := by
    intro n
    simp only [ha', hC', hD', show ∀ m : ℕ, N + (m + 1) = (N + m) + 1 from fun m ↦ by omega]
    exact hC (N + n)
  have hD1 : ∀ n, D' (n + 1) = a' n * D' n := by
    intro n
    simp only [ha', hD', show ∀ m : ℕ, N + (m + 1) = (N + m) + 1 from fun m ↦ by omega]
    exact hD (N + n)
  have hE1 : ∀ n, E' n = centeredState (a' n : ℤ) (D' n : ℤ) (C' n : ℤ) := by
    intro n; exact hE (N + n)
  have hcentred : ∀ n, Int.natAbs (E' n) < C' n := by
    intro n
    have := hN (N + n) (by omega)
    simpa [hE', hC'] using (by omega : Int.natAbs (E (N + n)) < C (N + n))
  have habs : ∀ n, E' n = 0 → E' (n + 1) = 0 :=
    fun n hz ↦ centeredState_zero_absorbing a' C' D' E' hC1 hD1 hE1 hcentred n hz
  have hnot' : ¬ ∃ M, ∀ n, M ≤ n → E' n = 0 := by
    rintro ⟨M, hM⟩
    refine hnot ⟨N + M, fun n hn ↦ ?_⟩
    have hrw : E n = E' (n - N) := by
      simp only [hE']
      congr 1
      omega
    rw [hrw]
    exact hM _ (by omega)
  have hne : ∀ n, E' n ≠ 0 :=
    fun n ↦ eventually_nonzero_of_zero_absorbing E' 0 (fun m _ hz ↦ habs m hz) hnot' n
      (Nat.zero_le n)
  have hmag : ∀ n, 0 < Int.natAbs (E' n) := by
    intro n
    exact Int.natAbs_pos.mpr (hne n)
  have hvan' : ∀ K, ∃ M, ∀ n, M ≤ n → K * Int.natAbs (E' n) < C' n := by
    intro K
    obtain ⟨M, hM⟩ := hvanish K
    refine ⟨M, fun n hn ↦ ?_⟩
    simpa [hE', hC'] using hM (N + n) (by omega)
  have htend :=
    tailState_tendsto_atTop_of_nonzero_normalizedVanishes C' (fun n ↦ Int.natAbs (E' n))
      hmag hvan'
  intro H
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop_atTop.mp htend) H
  exact ⟨N + n, hn n le_rfl⟩

/-! ## 4. The general exact orbit has `Θ > 1` -/

/-- A pointwise monotone envelope bounds the running maximum. -/
theorem runningMax_le_of_mono_bound (U B : ℕ → ℕ) (hBmono : Monotone B)
    (h : ∀ j, U j ≤ B j) : ∀ n, runningMax U n ≤ B n := by
  intro n
  induction n with
  | zero => exact h 0
  | succ n ih =>
      show max (runningMax U n) (U (n + 1)) ≤ B (n + 1)
      exact max_le (le_trans ih (hBmono (Nat.le_succ n))) (h (n + 1))

/-- **The paper's auxiliary lower bound `Θ ≥ 1` for a general exact orbit.**

Let `(a, C, D)` be an exact orbit of natural numbers with `a_n > 1`, `C_n > 0`,
`D_0 ≥ 1`, under vanishing relative error, and suppose the centred error is not
eventually zero.  Then `1 < Θ`, where
`Θ = limsup (H_{n+1} - H_n) / ℓ(H_n)` and `H_n = max_{j ≤ n} C_j`. -/
theorem exactOrbit_recordTheta_gt_one
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    (1 : EReal) < recordTheta C := by
  classical
  have hDpos : ∀ n, 0 < D n := fun n ↦
    lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) n) (den_ge_two_pow a D ha hD0 hD n)
  have hunb := exactOrbit_unbounded_of_error_not_eventually_zero a C D E hC hD hE hvanish hnot
  obtain ⟨N4, hN4⟩ := hvanish 4
  obtain ⟨N2, hN2⟩ := hvanish 2
  obtain ⟨t, htM, htN, ht4⟩ :=
    exists_multiplier_ge_four a C D E ha hCpos hD0 hC hD hE N4 hN4 (max N4 N2)
  have htower : ∀ k, 2 * binaryTower k ≤ a (t + k) :=
    tail_binaryTower_lower a C D E ha hCpos hC hD hE t (fun n hn ↦ hN4 n (by omega)) ht4
  -- from `t` on, `a` is at least `4` and strictly increasing
  have h4t : ∀ k, 4 ≤ a (t + k) := by
    intro k
    have h := htower k
    have hbt : 1 ≤ binaryTower k := binaryTower_pos k
    have hbt2 : 2 ≤ binaryTower k := by
      have := binaryTower_mono (Nat.zero_le k)
      simpa [binaryTower] using this
    omega
  have hrise : ∀ k, a (t + k) < a (t + k + 1) := by
    intro k
    have hsq := tail_square_step a C D E ha hCpos hC hD hE (t + k)
      (hN4 (t + k) (by omega)) (h4t k)
    have h4 := h4t k
    nlinarith [hsq, h4]
  -- choose a late index attaining a global record of `C`
  obtain ⟨s, hst, hsrec⟩ := exists_late_attained_record C hunb t
  -- the shifted orbit
  set a' : ℕ → ℕ := fun n ↦ a (s + n) with ha'
  set C' : ℕ → ℕ := fun n ↦ C (s + n) with hC'
  set D' : ℕ → ℕ := fun n ↦ D (s + n) with hD'
  have hshift : ∀ m : ℕ, s + (m + 1) = (s + m) + 1 := fun m ↦ by omega
  have hC1 : ∀ n, C' (n + 1) + D' n = a' n * C' n := by
    intro n
    simp only [ha', hC', hD', hshift]
    exact hC (s + n)
  have hD1 : ∀ n, D' (n + 1) = a' n * D' n := by
    intro n
    simp only [ha', hD', hshift]
    exact hD (s + n)
  -- `increasing`
  have hinc : StrictMono a' := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hk : s + n = t + ((s - t) + n) := by omega
    have h := hrise ((s - t) + n)
    simp only [ha']
    rw [hk, hshift n, hk]
    exact h
  -- `lower`
  have hlower : ∃ N : ℕ, ∀ k, 2 * binaryTower k ≤ a' (N + k) := by
    refine ⟨0, fun k ↦ ?_⟩
    have hk : s + (0 + k) = t + ((s - t) + k) := by omega
    have h := htower ((s - t) + k)
    have hmono : binaryTower k ≤ binaryTower ((s - t) + k) := binaryTower_mono (by omega)
    simp only [ha']
    rw [hk]
    omega
  -- `record_bound`
  have hrecb : ∃ K : ℕ, ∀ n, runningMax C' n ≤ 2 ^ (K + n) := by
    obtain ⟨K, hK⟩ : ∃ K : ℕ, C' 0 ≤ 2 ^ K := ⟨C' 0, Nat.le_of_lt Nat.lt_two_pow_self⟩
    refine ⟨K, ?_⟩
    have hpt : ∀ j, C' j ≤ 2 ^ (K + j) := by
      intro j
      induction j with
      | zero => simpa using hK
      | succ j ih =>
          have hstep : C' (j + 1) ≤ 2 * C' j := by
            simp only [hC', hshift]
            exact tail_two a C D E hC hE (s + j) (hN2 (s + j) (by omega))
          have : 2 * C' j ≤ 2 * 2 ^ (K + j) := Nat.mul_le_mul (le_refl _) ih
          have he : (2 : ℕ) * 2 ^ (K + j) = 2 ^ (K + (j + 1)) := by
            rw [show K + (j + 1) = (K + j) + 1 by omega, pow_succ]; ring
          omega
    exact runningMax_le_of_mono_bound C' (fun n ↦ 2 ^ (K + n))
      (fun i j hij ↦ Nat.pow_le_pow_right (by norm_num) (by omega)) hpt
  -- `den_bound`
  have hdenb : ∃ L : ℕ, ∀ n, D' n ≤ binaryTower (n + L) := by
    obtain ⟨L, hL⟩ : ∃ L : ℕ, 2 * D' 0 ≤ binaryTower L := by
      refine ⟨2 * D' 0, ?_⟩
      calc 2 * D' 0 ≤ 2 ^ (2 * D' 0) := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 ^ (2 * D' 0)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt Nat.lt_two_pow_self)
    refine ⟨L, fun n ↦ ?_⟩
    have hstrong : ∀ m, 2 * D' m ≤ binaryTower (m + L) := by
      intro m
      induction m with
      | zero => simpa using hL
      | succ m ih =>
          have hale : a' m ≤ 1 + D' m := by
            simp only [ha', hD']
            exact multiplier_le_den a C D E hCpos hC hE (s + m) (hN4 (s + m) (by omega))
          have hDp : 0 < D' m := hDpos (s + m)
          have hnext : 2 * D' (m + 1) ≤ (2 * D' m) ^ 2 := by
            rw [hD1 m]
            nlinarith [hale, hDp]
          have hsq : (2 * D' m) ^ 2 ≤ (binaryTower (m + L)) ^ 2 :=
            Nat.pow_le_pow_left ih 2
          have hbt : (binaryTower (m + L)) ^ 2 = binaryTower ((m + 1) + L) := by
            rw [show (m + 1) + L = (m + L) + 1 by omega, binaryTower_succ]
          omega
    have := hstrong n
    omega
  -- `unbounded`
  have hunb' : ∀ H : ℕ, ∃ n, H ≤ C' n := by
    intro H
    obtain ⟨m, hm⟩ := hunb (H + runningMax C s + 1)
    have hms : s < m := by
      by_contra hcon
      have := le_runningMax C (show m ≤ s by omega)
      omega
    refine ⟨m - s, ?_⟩
    simp only [hC', show s + (m - s) = m by omega]
    omega
  -- the orbit object
  let O : RecordGrowthOrbit :=
    { a := a', U := C', D := D'
      increasing := fun i j hij ↦ hinc hij
      a_pos := fun n ↦ lt_trans Nat.zero_lt_one (ha (s + n))
      U_pos := fun n ↦ hCpos (s + n)
      D_pos := fun n ↦ hDpos (s + n)
      U_step := hC1
      D_step := hD1
      lower := hlower
      record_bound := hrecb
      den_bound := hdenb
      unbounded := hunb' }
  have hOfun : O.U = C' := rfl
  have hrm : ∀ m, runningMax C' m = runningMax C (s + m) := by
    intro m
    simp only [hC']
    exact runningMax_shift_at_record C s hsrec m
  obtain ⟨c, hc, hcof⟩ := O.cofinal_inclusive_record
  apply ereal_limsup_gt_one_of_cofinal
  refine ⟨c, hc, fun T ↦ ?_⟩
  obtain ⟨n, hn, hnew, hgap⟩ := hcof T
  refine ⟨s + n, by omega, ?_⟩
  have hgap' : c * recordLogLog (runningMax C (s + n))
      < ((C (s + n + 1) - runningMax C (s + n) : ℕ) : ℝ) := by
    have h := hgap
    rw [hOfun, hrm n] at h
    simpa [hC'] using h
  have hden : 0 < recordLogLog (runningMax C (s + n)) :=
    lt_of_lt_of_le (by norm_num) (one_le_recordLogLog _)
  unfold recordLogLogCharge
  rw [runningMax_true_increment]
  exact (lt_div_iff₀ hden).2 hgap'

/-- The paper's auxiliary lower bound in the form the slow-negative argument
consumes. -/
theorem exactOrbit_one_le_recordTheta
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    (1 : EReal) ≤ recordTheta C :=
  le_of_lt (exactOrbit_recordTheta_gt_one a C D E ha hCpos hD0 hC hD hE hvanish hnot)

/-! ## 5. `long243:res:slownegative` -/

/-- The paper's growing bound on the negative part, extended from the indices
where `E n < 0` to the whole tail.  (Credit: this is
`slowNegative_bound_all_of_negative_part` of `SlowNegativePartRecord.lean`,
slice `s243_e`, repeated here because that file has no `.olean`.) -/
theorem slowNegative_bound_of_negative_part
    (C : ℕ → ℕ) (E : ℕ → ℤ) (c : ℝ) (hc0 : 0 ≤ c) (N : ℕ)
    (hslow : ∀ n, N ≤ n → E n < 0 →
      -((E n : ℤ) : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ)) :
    ∀ n, N ≤ n → -((E n : ℤ) : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ) := by
  intro n hn
  rcases lt_or_ge (E n) 0 with h | h
  · exact hslow n hn h
  · have hEn : (0 : ℝ) ≤ ((E n : ℤ) : ℝ) := by exact_mod_cast h
    have hl : (1 : ℝ) ≤ recordLogLog ((C n : ℕ) : ℝ) := one_le_recordLogLog _
    have : (0 : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ) := by nlinarith
    linarith

/-- **`long243:res:slownegative` (core.tex:2203), with no extra hypothesis.**

Let `(a, C, D)` be an exact orbit of natural numbers with `a_n > 1`, `C_n > 0`,
`D_0 ≥ 1`, under vanishing relative error.  Suppose that for some
`δ ∈ (0,1)` and all large `n` with `E_n < 0` one has
`-E_n ≤ (1-δ) ℓ(C_n)`.  Then `E_n = 0` for all large `n`, and
`a_{n+1} = a_n² - a_n + 1` for all large `n`. -/
theorem slowNegative_eventually_zero_and_sylvesterNext_unconditional
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (δ : ℝ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hDstep : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hslow : ∃ N, ∀ n, N ≤ n → E n < 0 →
      -((E n : ℤ) : ℝ) ≤ (1 - δ) * recordLogLog ((C n : ℕ) : ℝ)) :
    (∃ N, ∀ n, N ≤ n → E n = 0) ∧
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  have hE' : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ) := by
    intro n
    rw [hE n, centeredState]
  have hzero : ∃ N, ∀ n, N ≤ n → E n = 0 := by
    by_contra hnot
    obtain ⟨N, hN⟩ := hslow
    have hall := slowNegative_bound_of_negative_part C E (1 - δ) (by linarith) N hN
    have hle : recordTheta C ≤ (((1 - δ : ℝ)) : EReal) :=
      recordTheta_le_of_slow_negative a C D E hC hE' (1 - δ) (by linarith) N hall
    have hlow : (1 : EReal) ≤ recordTheta C :=
      exactOrbit_one_le_recordTheta a C D E ha hCpos hD0 hC hDstep hE hvanish hnot
    have hchain : (1 : EReal) ≤ (((1 - δ : ℝ)) : EReal) := le_trans hlow hle
    have hlt : (((1 - δ : ℝ)) : EReal) < (1 : EReal) := by
      rw [← EReal.coe_one]
      exact_mod_cast (by linarith : (1 - δ : ℝ) < 1)
    exact absurd hchain (not_le.mpr hlt)
  refine ⟨hzero, ?_⟩
  apply sylvesterNext_eventually_of_centered_zero
    (fun n ↦ (a n : ℤ)) (fun n ↦ (D n : ℤ)) (fun n ↦ (C n : ℤ))
  · intro n
    exact natDen_eq_nextDenState a D hDstep n
  · intro n
    exact natTail_eq_nextTailState a C D hC n
  · obtain ⟨N, hN⟩ := hzero
    refine ⟨N, fun n hn ↦ ?_⟩
    have hn0 := hN n hn
    rw [hE n] at hn0
    exact hn0
  · exact ⟨0, fun n _hn ↦ by exact_mod_cast (Nat.ne_of_gt (hCpos (n + 1)))⟩

end ErdosProblems.Erdos243.PaperCompleteR21

#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.slowNegative_eventually_zero_and_sylvesterNext_unconditional
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_recordTheta_gt_one
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_one_le_recordTheta
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.tail_multiplier_quadratic_lower
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_unbounded_of_error_not_eventually_zero
