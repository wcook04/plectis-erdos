import ErdosProblems.Erdos251.FreePairReduction

/-!
# Erdős #251: free-pair counts in a dyadic index window

Type B's revision memorandum (file 05, Proposition B) gives the exact count of
nonintegral congruent pairs in `[X, 2X)`.  The lattice
`free_pair_integral_iff_modEq` already decides each pair.  This module lands
the classification, as predicates rather than filtered finsets, because
`RealIntegral` is not a decidable filter:

* if `T 0` is irrational, every congruent pair in the window is free;
* if `T 0` is rational, free pairs are those congruent modulo `t` but not
  modulo `lcm(t, ord)`, where `ord` is the order of `2` at the stabilised odd
  denominator;
* in particular, taking `t` equal to that order yields an empty count past
  the cutoff.

A linear count that lets only the larger index grow is not equivalent to
irrationality: the rational word with `T 0 = 5/2`, `T 1 = 3` and `T N = 2`
for `N ≥ 2` supplies nonintegral pairs `(0, M)` for every `M ≥ 2` while
every pair of indices `≥ 1` remains integral.

Nothing here produces free pairs for the actual primes.
-/

open Finset

namespace ErdosProblems.Erdos251

/-! ## Windowed congruent pairs -/

/-- Unordered pairs `X ≤ N < M < 2X` with `v ∣ M - N`. -/
def congruentPairSet (v X : ℕ) : Finset (ℕ × ℕ) :=
  ((Ico X (2 * X)).product (Ico X (2 * X))).filter
    fun p => p.1 < p.2 ∧ v ∣ p.2 - p.1

theorem mem_congruentPairSet {v X N M : ℕ} :
    (N, M) ∈ congruentPairSet v X ↔
      X ≤ N ∧ N < 2 * X ∧ X ≤ M ∧ M < 2 * X ∧ N < M ∧ v ∣ M - N := by
  simp [congruentPairSet, mem_product, mem_Ico, and_assoc]

/-- A congruent pair whose tail difference is nonintegral. -/
def IsFreePair (T : ℕ → ℝ) (t X N M : ℕ) : Prop :=
  (N, M) ∈ congruentPairSet t X ∧ ¬ RealIntegral (T M - T N)

/-! ## Irrational initial state: every congruent pair is free -/

/-- An irrational initial state makes every positive-length tail difference
nonintegral. -/
theorem not_realIntegral_pair_of_irrational_initial
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (hirr : Irrational (T 0))
    {N M : ℕ} (hlt : N < M) :
    ¬ RealIntegral (T M - T N) := by
  intro hInt
  have hpos : 0 < M - N := Nat.sub_pos_of_lt hlt
  have hshift : realTailShift T (M - N) N = T M - T N := by
    simp [realTailShift, Nat.add_sub_of_le hlt.le]
  rw [← hshift] at hInt
  have : ¬ Irrational (T 0) :=
    (not_irrational_initial_iff_exists_integral_positive_tailShift hrec).2
      ⟨M - N, N, hpos, hInt⟩
  exact this hirr

/-- **Irrational classification.**  In every dyadic window a pair is free
exactly when it is congruent. -/
theorem isFreePair_iff_of_irrational
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (hirr : Irrational (T 0))
    (t X N M : ℕ) :
    IsFreePair T t X N M ↔ (N, M) ∈ congruentPairSet t X := by
  constructor
  · intro hp
    exact hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    have hmem := mem_congruentPairSet.mp hp
    exact not_realIntegral_pair_of_irrational_initial hrec hirr hmem.2.2.2.2.1

/-- There is at least one congruent pair in `[X, 2X)` once the window is longer
than the modulus. -/
theorem congruentPairSet_nonempty (t X : ℕ) (ht : 0 < t) (hX : t < X) :
    (congruentPairSet t X).Nonempty := by
  refine ⟨(X, X + t), mem_congruentPairSet.mpr ?_⟩
  have hN2 : X < 2 * X := by omega
  have hM2 : X + t < 2 * X := by omega
  exact ⟨le_rfl, hN2, Nat.le_add_right X t, hM2, Nat.lt_add_of_pos_right ht, by simp⟩

/-- Irrationality supplies a free pair in every large dyadic window, for every
positive modulus. -/
theorem exists_isFreePair_of_irrational
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (hirr : Irrational (T 0))
    (t X : ℕ) (ht : 0 < t) (hX : t < X) :
    ∃ N M, IsFreePair T t X N M := by
  obtain ⟨p, hp⟩ := congruentPairSet_nonempty t X ht hX
  rcases p with ⟨N, M⟩
  exact ⟨N, M, (isFreePair_iff_of_irrational hrec hirr t X N M).2 hp⟩

/-! ## Rational initial state: subtract the order lattice -/

theorem realIntegral_ratCast_iff (q : ℚ) :
    RealIntegral (q : ℝ) ↔ RatIntegral q := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    exact_mod_cast hz
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    exact_mod_cast hz

/-- Past an odd-denominator state, integrality of a pair difference is
membership in the order lattice. -/
theorem realIntegral_pair_iff_modEq_of_rational
    {g : ℕ → ℤ} {T : ℕ → ℝ} {q : ℚ}
    (hrec : RealDyadicTailRecurrence g T) (h0 : T 0 = q)
    {N₀ N M : ℕ} (hodd : Odd (rationalDyadicOrbit g q N₀).den)
    (hN : N₀ ≤ N) (hM : N₀ ≤ M) :
    RealIntegral (T M - T N) ↔
      N ≡ M [MOD orderOf (2 : ZMod (rationalDyadicOrbit g q N₀).den)] := by
  have hcast := realTail_eq_ratCast_rationalDyadicOrbit hrec q h0
  have hrat :
      RealIntegral (T M - T N) ↔
        RatIntegral (rationalDyadicOrbit g q M - rationalDyadicOrbit g q N) := by
    rw [hcast M, hcast N, ← Rat.cast_sub, realIntegral_ratCast_iff]
  rw [hrat, free_pair_integral_iff_modEq (rationalDyadicOrbit_recurrence g q) hodd hN hM]

/-- **Rational classification.**  Past the odd-denominator cutoff, a windowed
pair is free exactly when it is `t`-congruent and not `lcm(t, ord)`-congruent. -/
theorem isFreePair_iff_of_rational
    {g : ℕ → ℤ} {T : ℕ → ℝ} {q : ℚ}
    (hrec : RealDyadicTailRecurrence g T) (h0 : T 0 = q)
    {N₀ : ℕ} (hodd : Odd (rationalDyadicOrbit g q N₀).den)
    (t X N M : ℕ) (hX : N₀ ≤ X) :
    IsFreePair T t X N M ↔
      (N, M) ∈ congruentPairSet t X ∧
        (N, M) ∉ congruentPairSet
          (Nat.lcm t (orderOf (2 : ZMod (rationalDyadicOrbit g q N₀).den))) X := by
  set ord := orderOf (2 : ZMod (rationalDyadicOrbit g q N₀).den)
  constructor
  · intro hp
    have hcong := hp.1
    have hnon := hp.2
    have hmem := mem_congruentPairSet.mp hcong
    have hN : N₀ ≤ N := hX.trans hmem.1
    have hM : N₀ ≤ M := hX.trans hmem.2.2.1
    have hlat :=
      (realIntegral_pair_iff_modEq_of_rational hrec h0 hodd hN hM).not.mp hnon
    have hord : ¬ ord ∣ M - N := by
      intro hdvd
      exact hlat ((Nat.modEq_iff_dvd' hmem.2.2.2.2.1.le).2 hdvd)
    have hlcm : ¬ Nat.lcm t ord ∣ M - N := fun h =>
      hord ((Nat.dvd_lcm_right t ord).trans h)
    refine ⟨hcong, ?_⟩
    intro hlcmmem
    exact hlcm (mem_congruentPairSet.mp hlcmmem).2.2.2.2.2
  · intro hp
    have hcong := hp.1
    have hnot := hp.2
    have hmem := mem_congruentPairSet.mp hcong
    have hN : N₀ ≤ N := hX.trans hmem.1
    have hM : N₀ ≤ M := hX.trans hmem.2.2.1
    refine ⟨hcong, ?_⟩
    intro hInt
    have hlat :=
      (realIntegral_pair_iff_modEq_of_rational hrec h0 hodd hN hM).1 hInt
    have hord : ord ∣ M - N := (Nat.modEq_iff_dvd' hmem.2.2.2.2.1.le).1 hlat
    have hlcm : Nat.lcm t ord ∣ M - N := Nat.lcm_dvd hmem.2.2.2.2.2 hord
    exact hnot (mem_congruentPairSet.mpr
      ⟨hmem.1, hmem.2.1, hmem.2.2.1, hmem.2.2.2.1, hmem.2.2.2.2.1, hlcm⟩)

/-- On the order itself the rational count vanishes past the cutoff. -/
theorem not_isFreePair_of_rational_at_order
    {g : ℕ → ℤ} {T : ℕ → ℝ} {q : ℚ}
    (hrec : RealDyadicTailRecurrence g T) (h0 : T 0 = q)
    {N₀ : ℕ} (hodd : Odd (rationalDyadicOrbit g q N₀).den)
    (X N M : ℕ) (hX : N₀ ≤ X) :
    ¬ IsFreePair T (orderOf (2 : ZMod (rationalDyadicOrbit g q N₀).den)) X N M := by
  set ord := orderOf (2 : ZMod (rationalDyadicOrbit g q N₀).den)
  intro hp
  have hiff := isFreePair_iff_of_rational hrec h0 hodd ord X N M hX
  have ⟨hcong, hnot⟩ := hiff.1 hp
  rw [Nat.lcm_self] at hnot
  exact hnot hcong

/-! ## Linear-count counterexample: both indices must grow -/

/-- A rational word whose only nonintegral pair differences involve the index
`0`.  Counting pairs `0 ≤ N < M ≤ X` with only the larger endpoint unbounded
therefore yields a linear supply while the complete tail remains rational.
The digits are `a₁ = 2`, `a₂ = 4`, and `aₙ = 2` for `n ≥ 3`; `a₀` is unused
by the recurrence from `T 0`. -/
def earlyFreePairWord : ℕ → ℤ
  | 0 => 2
  | 1 => 2
  | 2 => 4
  | _ + 3 => 2

def earlyFreePairTail : ℕ → ℚ
  | 0 => 5 / 2
  | 1 => 3
  | _ => 2

theorem earlyFreePairTail_recurrence :
    DyadicTailRecurrence earlyFreePairWord earlyFreePairTail := by
  intro N
  match N with
  | 0 =>
      simp [earlyFreePairTail, earlyFreePairWord]
      norm_num
  | 1 =>
      simp [earlyFreePairTail, earlyFreePairWord]
      norm_num
  | n + 2 =>
      have hT : earlyFreePairTail (n + 2) = 2 := rfl
      have hT' : earlyFreePairTail (n + 3) = 2 := rfl
      have hg : earlyFreePairWord (n + 3) = 2 := rfl
      simp [hT, hT', hg]
      norm_num

theorem earlyFreePairTail_integral_of_one_le {N : ℕ} (hN : 1 ≤ N) :
    RatIntegral (earlyFreePairTail N) := by
  match N with
  | 0 => exact (Nat.not_succ_le_zero 0 hN).elim
  | 1 => exact ⟨3, rfl⟩
  | _ + 2 => exact ⟨2, rfl⟩

/-- Any pair with both indices at least `1` is integral, so a linear count of
pairs whose smaller index is allowed to stay at `0` cannot detect rationality. -/
theorem earlyFreePair_integral_of_one_le {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) :
    RatIntegral (earlyFreePairTail M - earlyFreePairTail N) := by
  obtain ⟨a, ha⟩ := earlyFreePairTail_integral_of_one_le hN
  obtain ⟨b, hb⟩ := earlyFreePairTail_integral_of_one_le hM
  refine ⟨b - a, ?_⟩
  simp [ha, hb]

theorem earlyFreePair_diff_zero {M : ℕ} (hM : 2 ≤ M) :
    earlyFreePairTail M - earlyFreePairTail 0 = (-1 : ℚ) / 2 := by
  have hT : earlyFreePairTail M = 2 := by
    match M with
    | 0 => omega
    | 1 => omega
    | _ + 2 => rfl
  rw [hT]
  simp [earlyFreePairTail]
  norm_num

/-- Pairs `(0, M)` with `M ≥ 2` are nonintegral, giving a linear-in-`X` supply
of congruent nonintegral pairs while `T 0 = 5/2` remains rational. -/
theorem earlyFreePair_nonintegral_of_zero {M : ℕ} (hM : 2 ≤ M) :
    ¬ RatIntegral (earlyFreePairTail M - earlyFreePairTail 0) := by
  rw [earlyFreePair_diff_zero hM]
  rintro ⟨z, hz⟩
  have h0 : (0 : ℚ) = (z : ℚ) * 2 + 1 := by
    have h := congrArg (fun q : ℚ => q * 2 + 1) hz
    simpa using h
  have hzZ : (0 : ℤ) = z * 2 + 1 := by exact_mod_cast h0
  omega

#print axioms isFreePair_iff_of_irrational
#print axioms isFreePair_iff_of_rational
#print axioms not_isFreePair_of_rational_at_order
#print axioms earlyFreePair_integral_of_one_le
#print axioms earlyFreePair_nonintegral_of_zero

end ErdosProblems.Erdos251
