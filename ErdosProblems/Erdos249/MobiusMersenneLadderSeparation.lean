import Erdos257PeriodNoncollapse.MersenneLambertLadder
import Erdos257PeriodNoncollapse.SignedQMomentObstruction
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Erdős #249: the two Möbius–Mersenne ladders are different sequences

Two signed Möbius series over the Mersenne denominators get written the same way
in prose and are *not* the same sequence.  This file separates them in Lean.

* The **power ladder** is the one the corpus formalises, as
  `Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta`:
  `Θᵣ = ∑_{d≥1} μ(d) / (2^d - 1)^r`.
  The exponent `r` sits on the *denominator*.
* The **literal Lambert ladder** is `mobiusMersenneLambertRung` below:
  `Θ̂ᵣ = ∑_{d≥1} μ(d) / (2^(r·d) - 1)`.
  The exponent `r` sits on the *base point*, i.e. it is the plain Möbius–Lambert
  series evaluated at `q = 2⁻ʳ`.

They agree at `r = 1` (both are `1/2`) and differ from `r = 2` on:
`mobiusMersenneLambertRung 2 = 1/4`, while `mobiusMersenneTheta 2 > 1/4`
(`lambertRung_two_lt_mobiusMersenneTheta_two`).

The structural contrast is the point of the file.

* `mobiusMersenneLambertRung_eq`: the literal ladder **collapses**, `Θ̂ᵣ = 2⁻ʳ`,
  by substituting `q = 2⁻ʳ` into the landed general collapse
  `MersenneLambertLadder.tsum_moebius_lambert`.
* `mobiusMersenneLambertRung_logAffine`: hence `Θ̂ᵣ · Θ̂ᵣ₊₂ = Θ̂ᵣ₊₁²` — the literal
  ladder is log-**affine**, its shifted Hankel matrices are the rank-one outer
  products `2⁻ˢ u uᵀ` with `uᵢ = 2⁻ⁱ`, and every shifted determinant of order
  `≥ 2` vanishes (`lambertRung_shifted_hankelDet_eq_zero`).  Its representing
  measure is the single atom at `1/2`.
* By contrast the corpus's landed
  `mobiusMersenneTheta_strict_logConcave` is a **strict** inequality
  `Θᵣ · Θᵣ₊₂ < Θᵣ₊₁²`, and `mobiusMersenneTheta_hankel_two_neg` gives a strictly
  negative order-two Hankel determinant.  So any "strict log-concavity at every
  rung" claim about the *literal* ladder is false, and
  `mobiusMersenneTheta_ne_mobiusMersenneLambertRung` derives exactly that
  contradiction: the two ladders cannot be equal on `r ≥ 1`.

Finally `mobiusMersenneTheta_no_linearRecurrence` records the strictly stronger
structural fact about the power ladder: it satisfies **no** finite
constant-coefficient linear recurrence.  Strict log-concavity constrains one
`2 × 2` minor per shift; this says no finite-order linear structure exists at
all, so the infinite Hankel matrix of `Θ` has infinite rank while that of `Θ̂`
has rank one.

Nothing here decides irrationality of the `#249` constant.
-/

namespace ErdosProblems.Erdos249.MobiusMersenneLadderSeparation

open scoped BigOperators
open ArithmeticFunction
open Erdos257PeriodNoncollapse.SignedQMomentObstruction

/-! ## The literal Lambert ladder and its collapse -/

/-- The **literal Lambert rung** `Θ̂ᵣ = ∑_{d≥1} μ(d)/(2^(r·d) - 1)`.

The `∑'` shape is the one used by `MersenneLambertLadder.tsum_moebius_lambert`
and `MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half`: the index
runs over `ℕ+` and the Möbius value is cast `ℤ → ℝ`.  This is **not**
`mobiusMersenneTheta`, whose `r` is an exponent on the denominator. -/
noncomputable def mobiusMersenneLambertRung (r : ℕ) : ℝ :=
  ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (r * (d : ℕ)) - 1)

private lemma half_pow_lambert_term (k : ℕ) (hk : 0 < k) :
    ((1 : ℝ) / 2) ^ k / (1 - ((1 : ℝ) / 2) ^ k) = 1 / ((2 : ℝ) ^ k - 1) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h1 : (0 : ℝ) < (2 : ℝ) ^ k - 1 :=
    sub_pos.mpr (one_lt_pow₀ (by norm_num) hk.ne')
  have h2ne : (2 : ℝ) ^ k ≠ 0 := ne_of_gt h2
  have h1ne : (2 : ℝ) ^ k - 1 ≠ 0 := ne_of_gt h1
  have hmid : (1 : ℝ) - 1 / (2 : ℝ) ^ k ≠ 0 := by
    have hEq : (1 : ℝ) - 1 / (2 : ℝ) ^ k = ((2 : ℝ) ^ k - 1) / (2 : ℝ) ^ k := by
      field_simp
    rw [hEq]
    exact div_ne_zero h1ne h2ne
  rw [div_pow, one_pow]
  field_simp

/-- **The literal ladder collapses**: `Θ̂ᵣ = 2⁻ʳ` for every `r ≥ 1`.

This is the substitution `q = (1/2)^r` into the general Möbius–Lambert collapse
`∑_{d≥1} μ(d)·q^d/(1-q^d) = q` already machine-checked as
`MersenneLambertLadder.tsum_moebius_lambert`. -/
theorem mobiusMersenneLambertRung_eq (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneLambertRung r = ((1 : ℝ) / 2) ^ r := by
  have hq0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ r := by positivity
  have hq1 : ((1 : ℝ) / 2) ^ r < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have h := MersenneLambertLadder.tsum_moebius_lambert hq0 hq1
  calc mobiusMersenneLambertRung r
      = ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) *
          ((((1 : ℝ) / 2) ^ r) ^ (d : ℕ) / (1 - (((1 : ℝ) / 2) ^ r) ^ (d : ℕ))) := by
        rw [mobiusMersenneLambertRung]
        refine tsum_congr fun d => ?_
        have hrd : 0 < r * (d : ℕ) :=
          Nat.pos_of_ne_zero (Nat.mul_ne_zero (by omega) d.pos.ne')
        rw [← pow_mul, half_pow_lambert_term _ hrd, mul_one_div]
    _ = ((1 : ℝ) / 2) ^ r := h

/-- `Θ̂₁ = 1/2`: the two ladders agree at the first rung. -/
theorem mobiusMersenneLambertRung_one : mobiusMersenneLambertRung 1 = 1 / 2 := by
  rw [mobiusMersenneLambertRung_eq 1 le_rfl]
  norm_num

/-- `Θ̂₂ = 1/4`. -/
theorem mobiusMersenneLambertRung_two : mobiusMersenneLambertRung 2 = 1 / 4 := by
  rw [mobiusMersenneLambertRung_eq 2 (by norm_num)]
  norm_num

/-! ## Log-affinity, and the separation from the power ladder -/

/-- **The literal ladder is log-affine.**  Contrast with the landed strict
inequality `mobiusMersenneTheta_strict_logConcave` for the *power* ladder:
`Θᵣ · Θᵣ₊₂ < Θᵣ₊₁²`.  The pair of statements is the separation. -/
theorem mobiusMersenneLambertRung_logAffine (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneLambertRung r * mobiusMersenneLambertRung (r + 2)
      = mobiusMersenneLambertRung (r + 1) ^ 2 := by
  rw [mobiusMersenneLambertRung_eq r hr,
    mobiusMersenneLambertRung_eq (r + 1) (by omega),
    mobiusMersenneLambertRung_eq (r + 2) (by omega)]
  ring

/-- The order-two shifted Hankel determinant of the literal ladder is exactly
zero, where `mobiusMersenneTheta_hankel_two_neg` makes the power ladder's
strictly negative. -/
theorem lambertRung_hankel_two_eq_zero (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneLambertRung r * mobiusMersenneLambertRung (r + 2)
      - mobiusMersenneLambertRung (r + 1) ^ 2 = 0 :=
  sub_eq_zero_of_eq (mobiusMersenneLambertRung_logAffine r hr)

/-- A concrete numeric separation at the smallest rung where the two ladders
differ: `Θ̂₂ = 1/4` but `Θ₂ ≥ 8/9 - 1/12 = 29/36`. -/
theorem lambertRung_two_lt_mobiusMersenneTheta_two :
    mobiusMersenneLambertRung 2 < mobiusMersenneTheta 2 := by
  have hsplit := mobiusMersenneTheta_eq_twoAtom_add_tail 2 (by norm_num)
  have hbound := abs_mobiusMersenneTailAfterTwo_le 2 (by norm_num)
  have hnum : (((1 : ℝ) / (2 : ℝ) ^ (2 : ℕ)) ^ 2) / (1 - (1 : ℝ) / (2 : ℝ) ^ (2 : ℕ))
      = 1 / 12 := by norm_num
  have hb12 : |mobiusMersenneTailAfterTwo 2| ≤ 1 / 12 := hbound.trans_eq hnum
  have habs := abs_le.mp hb12
  have hatom : mobiusMersenneTwoAtom 2 = 8 / 9 := by
    rw [mobiusMersenneTwoAtom]
    norm_num
  rw [mobiusMersenneLambertRung_two, hsplit, hatom]
  linarith [habs.1]

/-- **The definitional separation, in Lean.**  The power ladder and the literal
Lambert ladder cannot agree on all rungs `r ≥ 1`: the corpus proves the power
ladder strictly log-concave, and the literal ladder is log-affine. -/
theorem mobiusMersenneTheta_ne_mobiusMersenneLambertRung :
    ¬ ∀ r : ℕ, 1 ≤ r → mobiusMersenneTheta r = mobiusMersenneLambertRung r := by
  intro h
  have hstrict := mobiusMersenneTheta_strict_logConcave 1 le_rfl
  rw [h 1 le_rfl, h (1 + 1) (by omega), h (1 + 2) (by omega)] at hstrict
  have haffine := mobiusMersenneLambertRung_logAffine 1 le_rfl
  linarith

/-! ## Rank one: every shifted Hankel determinant of the literal ladder vanishes

The shifted Hankel matrix of `Θ̂` is `[Θ̂_{s+i+j}] = 2⁻ˢ · u uᵀ` with `uᵢ = 2⁻ⁱ`,
an outer product, hence singular in every order `≥ 2`.
-/

/-- A matrix whose entries factor as `c · q^i · q^j` is singular in every order
`≥ 2`: the vector `q·e₀ - e₁` lies in its kernel. -/
private lemma det_outer_geometric_eq_zero {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) K) (c q : K)
    (hM : ∀ i j : Fin (n + 2), M i j = c * q ^ (i : ℕ) * q ^ (j : ℕ)) :
    M.det = 0 := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i : Fin (n + 2), (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin (n + 2), (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hne : i1 ≠ i0 := by
    intro hEq
    rw [hEq, hi0] at hi1
    exact absurd hi1 (by norm_num)
  refine Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨fun j => (if j = i0 then q else 0) + (if j = i1 then -1 else 0), ?_, ?_⟩
  · intro hzero
    have hv := congrFun hzero i1
    simp [hne] at hv
  · funext i
    show (∑ j : Fin (n + 2), M i j *
        ((if j = i0 then q else 0) + (if j = i1 then -1 else 0))) = 0
    have hpt : ∀ j : Fin (n + 2),
        M i j * ((if j = i0 then q else 0) + (if j = i1 then -1 else 0))
          = (if j = i0 then M i j * q else 0) + (if j = i1 then M i j * (-1) else 0) := by
      intro j
      split_ifs <;> ring
    have hA : (∑ j : Fin (n + 2), if j = i0 then M i j * q else 0) = M i i0 * q := by
      rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hb])
        (fun hb => absurd (Finset.mem_univ i0) hb)]
      simp
    have hB : (∑ j : Fin (n + 2), if j = i1 then M i j * (-1) else 0)
        = M i i1 * (-1) := by
      rw [Finset.sum_eq_single i1 (fun b _ hb => by simp [hb])
        (fun hb => absurd (Finset.mem_univ i1) hb)]
      simp
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, hA, hB,
      hM i i0, hM i i1, hi0, hi1]
    ring

/-- **Rank-one collapse.**  For `s ≥ 1` and `N ≥ 2` the shifted Hankel
determinant `det [Θ̂_{s+i+j}]_{0 ≤ i,j < N}` is zero. -/
theorem lambertRung_shifted_hankelDet_eq_zero (s N : ℕ) (hs : 1 ≤ s) (hN : 2 ≤ N) :
    Matrix.det (Matrix.of fun i j : Fin N =>
      mobiusMersenneLambertRung (s + (i : ℕ) + (j : ℕ))) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  refine det_outer_geometric_eq_zero _ (((1 : ℝ) / 2) ^ s) ((1 : ℝ) / 2) ?_
  intro i j
  have hle : 1 ≤ s + (i : ℕ) + (j : ℕ) :=
    le_trans hs (le_trans (Nat.le_add_right s (i : ℕ)) (Nat.le_add_right _ (j : ℕ)))
  simp only [Matrix.of_apply]
  rw [mobiusMersenneLambertRung_eq _ hle, pow_add, pow_add]

/-- The same collapse stated through the corpus's own `hankelDet` API.  The
corpus `hankelDet` is `ℚ`-valued, and the literal ladder is rational at every
rung, so the two surfaces do meet here — which is exactly why the *power*
ladder's Hankel behaviour must not be read off this one. -/
theorem lambertRung_rat_hankelDet_eq_zero (s N : ℕ) (hN : 2 ≤ N) :
    hankelDet (fun k => ((1 : ℚ) / 2) ^ (s + k)) N = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  refine det_outer_geometric_eq_zero _ (((1 : ℚ) / 2) ^ s) ((1 : ℚ) / 2) ?_
  intro i j
  show ((1 : ℚ) / 2) ^ (s + ((i : ℕ) + (j : ℕ))) = _
  rw [pow_add, pow_add]
  ring

/-! ## The power ladder admits no finite linear recurrence

Write `xⱼ = 1/(2^(j+1) - 1)` and `εⱼ = μ(j+1)`, so that
`Θᵣ = ∑_{j≥0} εⱼ xⱼʳ` (`mobiusMersenneTheta_eq_tsum_atoms`).  The atoms are
strictly decreasing, lie in `(0,1]`, and satisfy `x_{i+k} ≤ x_k · 2⁻ⁱ`, hence are
summable.  A finite recurrence `∑_k c_k Θ_{n+k} = 0` valid for all large `n`
therefore forces `∑_j εⱼ P(xⱼ) xⱼⁿ = 0` for all large `n`, where
`P(X) = ∑_k c_k X^k`.  Since `P ≠ 0` has finitely many roots, the atoms are
pairwise distinct, and `εⱼ ≠ 0` for infinitely many `j` (every prime supplies
one), some `εⱼ P(xⱼ)` is nonzero.  Peeling at the least such index `j₀` and
dividing by `x_{j₀}ⁿ` gives `|ε_{j₀} P(x_{j₀})| ≤ 2‖c‖₁ (x_{j₀+1}/x_{j₀})ⁿ → 0`,
a contradiction.
-/

private noncomputable def mersenneAtom (j : ℕ) : ℝ := 1 / ((2 : ℝ) ^ (j + 1) - 1)

private noncomputable def moebiusSign (j : ℕ) : ℝ := ((moebius (j + 1) : ℤ) : ℝ)

private lemma mersenneDen_pos (j : ℕ) : (0 : ℝ) < (2 : ℝ) ^ (j + 1) - 1 :=
  sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))

private lemma mersenneAtom_pos (j : ℕ) : 0 < mersenneAtom j :=
  div_pos one_pos (mersenneDen_pos j)

private lemma mersenneAtom_zero : mersenneAtom 0 = 1 := by
  rw [mersenneAtom]
  norm_num

private lemma mersenneAtom_le_one (j : ℕ) : mersenneAtom j ≤ 1 := by
  rw [mersenneAtom, div_le_one (mersenneDen_pos j)]
  have hsucc : (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 := pow_succ 2 j
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  nlinarith

private lemma mersenneAtom_shift_le (k i : ℕ) :
    mersenneAtom (i + k) ≤ mersenneAtom k * ((1 : ℝ) / 2) ^ i := by
  have hk := mersenneDen_pos k
  have h2i : (0 : ℝ) < (2 : ℝ) ^ i := by positivity
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  have hprodpos : (0 : ℝ) < ((2 : ℝ) ^ (k + 1) - 1) * (2 : ℝ) ^ i := mul_pos hk h2i
  have hpow : (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ i = (2 : ℝ) ^ (i + k + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : ((2 : ℝ) ^ (k + 1) - 1) * (2 : ℝ) ^ i ≤ (2 : ℝ) ^ (i + k + 1) - 1 := by
    have hexp : ((2 : ℝ) ^ (k + 1) - 1) * (2 : ℝ) ^ i
        = (2 : ℝ) ^ (i + k + 1) - (2 : ℝ) ^ i := by
      rw [sub_mul, one_mul, hpow]
    rw [hexp]
    linarith
  have hle : 1 / ((2 : ℝ) ^ (i + k + 1) - 1)
      ≤ 1 / (((2 : ℝ) ^ (k + 1) - 1) * (2 : ℝ) ^ i) :=
    one_div_le_one_div_of_le hprodpos hkey
  have heq : mersenneAtom k * ((1 : ℝ) / 2) ^ i
      = 1 / (((2 : ℝ) ^ (k + 1) - 1) * (2 : ℝ) ^ i) := by
    rw [mersenneAtom, div_pow, one_pow, div_mul_div_comm, one_mul]
  rw [mersenneAtom, heq]
  exact hle

private lemma mersenneAtom_le_geom (j : ℕ) : mersenneAtom j ≤ ((1 : ℝ) / 2) ^ j := by
  have h := mersenneAtom_shift_le 0 j
  rwa [Nat.add_zero, mersenneAtom_zero, one_mul] at h

private lemma mersenneAtom_strictAnti : StrictAnti mersenneAtom := by
  intro p q hpq
  simp only [mersenneAtom]
  refine one_div_lt_one_div_of_lt (mersenneDen_pos p) ?_
  have h : (2 : ℝ) ^ (p + 1) < (2 : ℝ) ^ (q + 1) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  linarith

private lemma mobiusMersenneTerm_eq (r j : ℕ) :
    mobiusMersenneTerm r j = moebiusSign j * mersenneAtom j ^ r := by
  rw [mobiusMersenneTerm, moebiusSign, mersenneAtom, div_pow, one_pow, mul_one_div]

private lemma abs_moebiusSign_le_one (j : ℕ) : |moebiusSign j| ≤ 1 := by
  rw [moebiusSign, ← Int.cast_abs]
  exact_mod_cast MersenneLambertLadder.abs_moebius_le_one (j + 1)

/-- **Atomic form of the power ladder.**  `Θᵣ = ∑_{j≥0} μ(j+1)·(1/(2^(j+1)-1))ʳ`:
a signed sum of `r`-th powers of the strictly decreasing Mersenne atoms.  This
is the representation the no-recurrence argument peels. -/
theorem mobiusMersenneTheta_eq_tsum_atoms (r : ℕ) :
    mobiusMersenneTheta r =
      ∑' j : ℕ, ((moebius (j + 1) : ℤ) : ℝ) * (1 / ((2 : ℝ) ^ (j + 1) - 1)) ^ r := by
  rw [mobiusMersenneTheta]
  exact tsum_congr fun j => mobiusMersenneTerm_eq r j

/-! ### The recurrence polynomial and its atomic coefficients -/

private noncomputable def recPoly {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin (m + 1), c k * x ^ (k : ℕ)

private noncomputable def recAtomCoeff {m : ℕ} (c : Fin (m + 1) → ℝ) (j : ℕ) : ℝ :=
  moebiusSign j * recPoly c (mersenneAtom j)

private noncomputable def recAbsSum {m : ℕ} (c : Fin (m + 1) → ℝ) : ℝ :=
  ∑ k : Fin (m + 1), |c k|

private lemma recAbsSum_nonneg {m : ℕ} (c : Fin (m + 1) → ℝ) : 0 ≤ recAbsSum c :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma abs_recPoly_le {m : ℕ} (c : Fin (m + 1) → ℝ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : |recPoly c x| ≤ recAbsSum c := by
  rw [recPoly, recAbsSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul, abs_pow, abs_of_nonneg hx0]
  calc |c k| * x ^ (k : ℕ) ≤ |c k| * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hx0 hx1) (abs_nonneg _)
    _ = |c k| := mul_one _

private lemma abs_recAtomCoeff_le {m : ℕ} (c : Fin (m + 1) → ℝ) (j : ℕ) :
    |recAtomCoeff c j| ≤ recAbsSum c := by
  rw [recAtomCoeff, abs_mul]
  calc |moebiusSign j| * |recPoly c (mersenneAtom j)|
      ≤ 1 * recAbsSum c :=
        mul_le_mul (abs_moebiusSign_le_one j)
          (abs_recPoly_le c (mersenneAtom_pos j).le (mersenneAtom_le_one j))
          (abs_nonneg _) zero_le_one
    _ = recAbsSum c := one_mul _

private lemma summable_recAtom {m : ℕ} (c : Fin (m + 1) → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun j => recAtomCoeff c j * mersenneAtom j ^ n) := by
  have hgeo : Summable (fun j : ℕ => recAbsSum c * ((1 : ℝ) / 2) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_norm_bounded hgeo fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (mersenneAtom_pos j)]
  have hpow : mersenneAtom j ^ n ≤ mersenneAtom j := by
    have h := pow_le_pow_of_le_one (mersenneAtom_pos j).le (mersenneAtom_le_one j) hn
    rwa [pow_one] at h
  calc |recAtomCoeff c j| * mersenneAtom j ^ n
      ≤ recAbsSum c * mersenneAtom j ^ n :=
        mul_le_mul_of_nonneg_right (abs_recAtomCoeff_le c j)
          (pow_nonneg (mersenneAtom_pos j).le n)
    _ ≤ recAbsSum c * ((1 : ℝ) / 2) ^ j :=
        mul_le_mul_of_nonneg_left (hpow.trans (mersenneAtom_le_geom j))
          (recAbsSum_nonneg c)

/-- The recurrence functional, resummed atomwise. -/
private lemma tsum_recAtom_eq {m : ℕ} (c : Fin (m + 1) → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑' j, recAtomCoeff c j * mersenneAtom j ^ n
      = ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) := by
  have hsummable : ∀ k : Fin (m + 1),
      Summable (fun j => c k * mobiusMersenneTerm (n + (k : ℕ)) j) := fun k =>
    (summable_mobiusMersenneTerm (n + (k : ℕ)) (by omega)).mul_left _
  calc ∑' j, recAtomCoeff c j * mersenneAtom j ^ n
      = ∑' j, ∑ k : Fin (m + 1), c k * mobiusMersenneTerm (n + (k : ℕ)) j := by
        refine tsum_congr fun j => ?_
        have hpt : ∀ k : Fin (m + 1),
            c k * mobiusMersenneTerm (n + (k : ℕ)) j
              = moebiusSign j * mersenneAtom j ^ n *
                (c k * mersenneAtom j ^ (k : ℕ)) := by
          intro k
          rw [mobiusMersenneTerm_eq, pow_add]
          ring
        rw [Finset.sum_congr rfl (fun k _ => hpt k), ← Finset.mul_sum, recAtomCoeff,
          recPoly]
        ring
    _ = ∑ k : Fin (m + 1), ∑' j, c k * mobiusMersenneTerm (n + (k : ℕ)) j :=
        Summable.tsum_finsetSum (fun k _ => hsummable k)
    _ = ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mobiusMersenneTheta, tsum_mul_left]

/-- Some atomic coefficient survives: `P ≠ 0` has finitely many roots, the atoms
are pairwise distinct, and `μ(j+1) ≠ 0` for infinitely many `j`. -/
private lemma exists_recAtomCoeff_ne_zero {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hc : ∃ k, c k ≠ 0) : ∃ j, recAtomCoeff c j ≠ 0 := by
  classical
  obtain ⟨k₀, hk₀⟩ := hc
  by_contra hcon
  have hall : ∀ j, recAtomCoeff c j = 0 := by
    intro j
    by_contra hj
    exact hcon ⟨j, hj⟩
  obtain ⟨Q, hQeval, hQcoeff⟩ :
      ∃ Q : Polynomial ℝ, (∀ x, Polynomial.eval x Q = recPoly c x) ∧
        Q.coeff (k₀ : ℕ) = c k₀ := by
    refine ⟨∑ k : Fin (m + 1), Polynomial.C (c k) * Polynomial.X ^ (k : ℕ), ?_, ?_⟩
    · intro x
      simp [recPoly, Polynomial.eval_finset_sum]
    · rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single k₀]
      · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · intro b _ hb
        have hne : (k₀ : ℕ) ≠ (b : ℕ) := fun hEq => hb (Fin.val_injective hEq.symm)
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
      · intro hb
        exact absurd (Finset.mem_univ k₀) hb
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at hQcoeff
    exact hk₀ hQcoeff.symm
  have hroots : {x : ℝ | Q.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hQ0
  have hpre : (mersenneAtom ⁻¹' {x : ℝ | Q.IsRoot x}).Finite :=
    Set.Finite.preimage mersenneAtom_strictAnti.injective.injOn hroots
  have hsub : {j : ℕ | moebiusSign j ≠ 0} ⊆ mersenneAtom ⁻¹' {x : ℝ | Q.IsRoot x} := by
    intro j hj
    have h0 := hall j
    rw [recAtomCoeff] at h0
    have hpoly : recPoly c (mersenneAtom j) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hj
      · exact h
    show Polynomial.eval (mersenneAtom j) Q = 0
    rw [hQeval]
    exact hpoly
  have hfin : {j : ℕ | moebiusSign j ≠ 0}.Finite := hpre.subset hsub
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 2)
  have hmem : (p - 1) ∈ {j : ℕ | moebiusSign j ≠ 0} := by
    have hp2 := hp.two_le
    have hp1 : p - 1 + 1 = p := by omega
    show moebiusSign (p - 1) ≠ 0
    rw [moebiusSign, hp1, moebius_apply_prime hp]
    norm_num
  have hle := hN hmem
  omega

/-- **No finite linear recurrence, eventual form.**  There is no nonzero
coefficient vector `c` and threshold `n₀` with `∑_k c_k Θ_{n+k} = 0` for all
`n ≥ n₀`. -/
theorem mobiusMersenneTheta_no_linearRecurrence_of_eventually
    {m : ℕ} (c : Fin (m + 1) → ℝ) (n₀ : ℕ) (hc : ∃ k, c k ≠ 0)
    (hrec : ∀ n : ℕ, n₀ ≤ n →
      ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0) : False := by
  classical
  have hex := exists_recAtomCoeff_ne_zero c hc
  obtain ⟨j₀, hj₀ne, hj₀min⟩ :
      ∃ j₀, recAtomCoeff c j₀ ≠ 0 ∧ ∀ i, i < j₀ → recAtomCoeff c i = 0 := by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi => ?_⟩
    by_contra h
    exact Nat.find_min hex hi h
  have hkey : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n →
      |recAtomCoeff c j₀| * mersenneAtom j₀ ^ n
        ≤ 2 * recAbsSum c * mersenneAtom (j₀ + 1) ^ n := by
    intro n hn hn1
    have hs := summable_recAtom c n hn1
    have hsplit := hs.sum_add_tsum_nat_add (j₀ + 1)
    have htot : ∑' j, recAtomCoeff c j * mersenneAtom j ^ n = 0 := by
      rw [tsum_recAtom_eq c n hn1]
      exact hrec n hn
    have hpre : ∑ i ∈ Finset.range (j₀ + 1), recAtomCoeff c i * mersenneAtom i ^ n
        = recAtomCoeff c j₀ * mersenneAtom j₀ ^ n := by
      refine Finset.sum_eq_single j₀ ?_ ?_
      · intro b hb hbne
        rw [Finset.mem_range] at hb
        rw [hj₀min b (by omega), zero_mul]
      · intro hb
        exact absurd (Finset.self_mem_range_succ j₀) hb
    rw [hpre, htot] at hsplit
    have hmaj : ∀ i : ℕ,
        ‖recAtomCoeff c (i + (j₀ + 1)) * mersenneAtom (i + (j₀ + 1)) ^ n‖
          ≤ recAbsSum c * mersenneAtom (j₀ + 1) ^ n * ((1 : ℝ) / 2) ^ i := by
      intro i
      rw [Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_pos (mersenneAtom_pos (i + (j₀ + 1)))]
      have hshift : mersenneAtom (i + (j₀ + 1)) ^ n
          ≤ (mersenneAtom (j₀ + 1) * ((1 : ℝ) / 2) ^ i) ^ n :=
        pow_le_pow_left₀ (mersenneAtom_pos _).le (mersenneAtom_shift_le (j₀ + 1) i) n
      have hgeo : (((1 : ℝ) / 2) ^ i) ^ n ≤ ((1 : ℝ) / 2) ^ i := by
        rw [← pow_mul]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (Nat.le_mul_of_pos_right i hn1)
      calc |recAtomCoeff c (i + (j₀ + 1))| * mersenneAtom (i + (j₀ + 1)) ^ n
          ≤ recAbsSum c * mersenneAtom (i + (j₀ + 1)) ^ n :=
            mul_le_mul_of_nonneg_right (abs_recAtomCoeff_le c (i + (j₀ + 1)))
              (pow_nonneg (mersenneAtom_pos (i + (j₀ + 1))).le n)
        _ ≤ recAbsSum c * (mersenneAtom (j₀ + 1) ^ n * ((1 : ℝ) / 2) ^ i) := by
            refine mul_le_mul_of_nonneg_left ?_ (recAbsSum_nonneg c)
            refine hshift.trans ?_
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left hgeo
              (pow_nonneg (mersenneAtom_pos (j₀ + 1)).le n)
        _ = recAbsSum c * mersenneAtom (j₀ + 1) ^ n * ((1 : ℝ) / 2) ^ i := by ring
    have hsummaj : Summable (fun i : ℕ =>
        recAbsSum c * mersenneAtom (j₀ + 1) ^ n * ((1 : ℝ) / 2) ^ i) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hnormsum : Summable (fun i : ℕ =>
        ‖recAtomCoeff c (i + (j₀ + 1)) * mersenneAtom (i + (j₀ + 1)) ^ n‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hmaj hsummaj
    have hnorm := norm_tsum_le_tsum_norm hnormsum
    have hcmp :
        (∑' i : ℕ, ‖recAtomCoeff c (i + (j₀ + 1)) * mersenneAtom (i + (j₀ + 1)) ^ n‖)
          ≤ ∑' i : ℕ, recAbsSum c * mersenneAtom (j₀ + 1) ^ n * ((1 : ℝ) / 2) ^ i :=
      Summable.tsum_le_tsum hmaj hnormsum hsummaj
    have hgeoval :
        (∑' i : ℕ, recAbsSum c * mersenneAtom (j₀ + 1) ^ n * ((1 : ℝ) / 2) ^ i)
          = 2 * recAbsSum c * mersenneAtom (j₀ + 1) ^ n := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      have hinv : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
      rw [hinv]
      ring
    have heq : recAtomCoeff c j₀ * mersenneAtom j₀ ^ n
        = -(∑' i : ℕ,
            recAtomCoeff c (i + (j₀ + 1)) * mersenneAtom (i + (j₀ + 1)) ^ n) := by
      linarith
    calc |recAtomCoeff c j₀| * mersenneAtom j₀ ^ n
        = |recAtomCoeff c j₀ * mersenneAtom j₀ ^ n| := by
          rw [abs_mul, abs_pow, abs_of_pos (mersenneAtom_pos j₀)]
      _ = ‖∑' i : ℕ,
            recAtomCoeff c (i + (j₀ + 1)) * mersenneAtom (i + (j₀ + 1)) ^ n‖ := by
          rw [heq, Real.norm_eq_abs, abs_neg]
      _ ≤ 2 * recAbsSum c * mersenneAtom (j₀ + 1) ^ n :=
          hnorm.trans (hcmp.trans_eq hgeoval)
  have hpos0 := mersenneAtom_pos j₀
  have hratio_lt : mersenneAtom (j₀ + 1) < mersenneAtom j₀ :=
    mersenneAtom_strictAnti (by omega)
  have hρ0 : (0 : ℝ) ≤ mersenneAtom (j₀ + 1) / mersenneAtom j₀ :=
    div_nonneg (mersenneAtom_pos _).le hpos0.le
  have hρ1 : mersenneAtom (j₀ + 1) / mersenneAtom j₀ < 1 :=
    (div_lt_one hpos0).mpr hratio_lt
  have hfinal : ∀ n : ℕ, max n₀ 1 ≤ n →
      |recAtomCoeff c j₀|
        ≤ 2 * recAbsSum c * (mersenneAtom (j₀ + 1) / mersenneAtom j₀) ^ n := by
    intro n hn
    have h1 : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have h2 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hx : (0 : ℝ) < mersenneAtom j₀ ^ n := pow_pos hpos0 n
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hx]
    exact hkey n h1 h2
  have htend : Filter.Tendsto
      (fun n : ℕ => 2 * recAbsSum c * (mersenneAtom (j₀ + 1) / mersenneAtom j₀) ^ n)
      Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    simpa using h.const_mul (2 * recAbsSum c)
  have hle0 : |recAtomCoeff c j₀| ≤ 0 :=
    ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨max n₀ 1, hfinal⟩)
  exact hj₀ne (abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg _)))

/-- **The power ladder satisfies no finite constant-coefficient linear
recurrence.**  Contrast `lambertRung_shifted_hankelDet_eq_zero`: the literal
Lambert ladder has Hankel rank one, so it *does* satisfy the order-one
recurrence `Θ̂_{n+1} = Θ̂_n / 2`.  Infinite Hankel rank for `Θ` is strictly
stronger structural information than the landed order-two strict
log-concavity. -/
theorem mobiusMersenneTheta_no_linearRecurrence :
    ¬ ∃ (m : ℕ) (c : Fin (m + 1) → ℝ), (∃ k, c k ≠ 0) ∧
        ∀ n : ℕ, 1 ≤ n →
          ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0 := by
  rintro ⟨m, c, hc, hrec⟩
  exact mobiusMersenneTheta_no_linearRecurrence_of_eventually c 1 hc hrec

#print axioms mobiusMersenneLambertRung_eq
#print axioms mobiusMersenneLambertRung_logAffine
#print axioms lambertRung_two_lt_mobiusMersenneTheta_two
#print axioms mobiusMersenneTheta_ne_mobiusMersenneLambertRung
#print axioms lambertRung_shifted_hankelDet_eq_zero
#print axioms lambertRung_rat_hankelDet_eq_zero
#print axioms mobiusMersenneTheta_eq_tsum_atoms
#print axioms mobiusMersenneTheta_no_linearRecurrence

end ErdosProblems.Erdos249.MobiusMersenneLadderSeparation
