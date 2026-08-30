import Erdos249257.PivotAntiReconstruction

/-!
# Erdős #249: gaps in the first harmonic of the tail orbit

This module records two sufficient conditions for irrationality of the binary
totient series.  The first is a uniform saving for the real part of the
first harmonic on arbitrarily late dyadic blocks.  The second is the earlier
pointwise condition along suitable prime indices.

Neither condition is proved here for the actual totient orbit.  In particular,
the results below do not establish the required density estimate or solve
Erdős Problem #249.
-/

namespace ErdosProblems.Erdos249

open Erdos249257.TotientTailPeriodKiller

/-! ## A uniform block gap -/

/-- On arbitrarily late dyadic blocks, the mean real part of the infinite
tail-orbit phase is at most `89/100`.  The hypotheses include every positive
shift `h`; no such estimate is currently known for the totient orbit. -/
noncomputable def TotientTailOrbitBlockGap : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X : ℕ,
      max X₀ 1 ≤ X ∧
      (∑ N ∈ Finset.Ico X (2 * X), (tailOrbitFirstExp h N).re)
        ≤ (89 / 100 : ℝ) * X

/-- On arbitrarily late dyadic blocks, at least an `11/100` proportion of the
tail-orbit phases have nonpositive real part.  This is a sufficient density
hypothesis, not a statement proved here for the totient orbit. -/
noncomputable def TotientTailOrbitNonpositiveBlockDensity : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X : ℕ,
      max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤
        ((Finset.Ico X (2 * X)).filter
          fun N => (tailOrbitFirstExp h N).re ≤ 0).card

/-- A density of nonpositive phases gives the `89/100` block gap.  The other
phases contribute at most `1` because every tail-orbit phase has norm one. -/
theorem tailOrbitBlockGap_of_nonpositiveBlockDensity
    (hdensity : TotientTailOrbitNonpositiveBlockDensity) :
    TotientTailOrbitBlockGap := by
  classical
  intro h hh X₀
  obtain ⟨X, hX, hdense⟩ := hdensity h hh X₀
  let I := Finset.Ico X (2 * X)
  let p : ℕ → Prop := fun N => (tailOrbitFirstExp h N).re ≤ 0
  let T := I.filter p
  let U := I.filter fun N => ¬ p N
  have hsum :
      (∑ N ∈ I, (tailOrbitFirstExp h N).re) ≤ (U.card : ℝ) := by
    calc
      (∑ N ∈ I, (tailOrbitFirstExp h N).re)
          ≤ ∑ N ∈ I, if p N then (0 : ℝ) else 1 := by
            apply Finset.sum_le_sum
            intro N hN
            by_cases hp : p N
            · simp only [hp, ↓reduceIte]
              exact hp
            · simp only [hp, ↓reduceIte]
              have hnorm : ‖tailOrbitFirstExp h N‖ = 1 := by
                rw [tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp]
                exact norm_scaledTotientSeriesFirstExp h N
              exact (Complex.re_le_norm _).trans_eq hnorm
      _ = (U.card : ℝ) := by
        rw [show (∑ N ∈ I, if p N then (0 : ℝ) else 1) =
            ∑ N ∈ I, if ¬ p N then (1 : ℝ) else 0 by
          apply Finset.sum_congr rfl
          intro N hN
          by_cases hp : p N <;> simp [hp]]
        simpa [U] using (Finset.sum_boole (R := ℝ) (fun N => ¬ p N) I)
  have hcardI : I.card = X := by
    dsimp [I]
    rw [Nat.card_Ico]
    omega
  have hpartitionNat : T.card + U.card = X := by
    calc
      T.card + U.card = I.card := by
        simpa [T, U] using I.card_filter_add_card_filter_not p
      _ = X := hcardI
  have hpartition : (T.card : ℝ) + (U.card : ℝ) = X := by
    exact_mod_cast hpartitionNat
  have hdenseT : (11 / 100 : ℝ) * X ≤ (T.card : ℝ) := by
    simpa [I, p, T] using hdense
  refine ⟨X, hX, ?_⟩
  change (∑ N ∈ I, (tailOrbitFirstExp h N).re) ≤ (89 / 100 : ℝ) * X
  nlinarith

/-- A uniform `89/100` block gap for the infinite orbit yields the finite
`9/10` gap after choosing one truncation depth for the whole block. -/
theorem irrational_totient_series_of_tailOrbitBlockGap
    (hgap : TotientTailOrbitBlockGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_certificate_supply
  intro h hh N₀
  obtain ⟨X, hX, horbit⟩ := hgap h hh N₀
  have hXpos : 0 < X :=
    lt_of_lt_of_le Nat.zero_lt_one ((Nat.le_max_right N₀ 1).trans hX)
  obtain ⟨L, _hL, hroomWorst, herrorWorst⟩ :=
    exists_natural_window_depth_with_error h (2 * X) 0 (1 / 100 : ℝ) (by norm_num)
  have hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L := by
    omega
  have hpoint : ∀ N ∈ Finset.Ico X (2 * X),
      windowFirstCos h N L ≤ (tailOrbitFirstExp h N).re + (1 / 100 : ℝ) := by
    intro N hN
    apply windowFirstCos_le_add_of_tailOrbitGap le_rfl
    have hNle : N ≤ 2 * X := (Finset.mem_Ico.mp hN).2.le
    have hnumNat : N + L + h + 2 ≤ 2 * X + L + h + 2 := by omega
    have hnum :
        (N : ℝ) + L + h + 2 ≤ (2 * X : ℕ) + L + h + 2 := by
      exact_mod_cast hnumNat
    calc
      2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L
          ≤ 2 * Real.pi * (((2 * X : ℕ) : ℝ) + L + h + 2) / 2 ^ L := by
            gcongr
      _ ≤ (1 / 100 : ℝ) := herrorWorst
  have hfinite :
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L)
        ≤ (9 / 10 : ℝ) * X := by
    calc
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L)
          ≤ ∑ N ∈ Finset.Ico X (2 * X),
              ((tailOrbitFirstExp h N).re + (1 / 100 : ℝ)) := by
            exact Finset.sum_le_sum fun N hN => hpoint N hN
      _ = (∑ N ∈ Finset.Ico X (2 * X), (tailOrbitFirstExp h N).re) +
            (1 / 100 : ℝ) * X := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico]
          simp only [nsmul_eq_mul]
          have hXX : 2 * X - X = X := by omega
          rw [hXX]
          ring
      _ ≤ (89 / 100 : ℝ) * X + (1 / 100 : ℝ) * X :=
        add_le_add horbit le_rfl
      _ = (9 / 10 : ℝ) * X := by ring
  obtain ⟨N, hNIco, hkill⟩ :=
    exists_certifiedKill_of_first_harmonic_gap hXpos hroom hfinite
  refine ⟨N, ?_, L, hkill⟩
  exact (Nat.le_max_left N₀ 1).trans (hX.trans (Finset.mem_Ico.mp hNIco).1)

/-- The nonpositive-density hypothesis implies irrationality through the
uniform block-gap theorem. -/
theorem irrational_totient_series_of_nonpositiveBlockDensity
    (hdensity : TotientTailOrbitNonpositiveBlockDensity) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_tailOrbitBlockGap
    (tailOrbitBlockGap_of_nonpositiveBlockDensity hdensity)

/-! ## A pointwise prime condition -/

/-- Cofinal prime indices at which the infinite-orbit real part is strictly
below `9/10`.  The positive margin may depend on the chosen index. -/
def DTWNaturalPrimeTailOrbitStrictGap : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ p : ℕ,
      max (N₀ + h + 1) (h + 5) ≤ p ∧
      p.Prime ∧
      (tailOrbitFirstExp h (p - h - 1)).re < (9 / 10 : ℝ)

/-- The first tail-orbit phase follows the exact doubling map.  The integer
carry increment disappears after exponentiation, so the producer questions
above are questions about the orbit of one phase under repeated squaring. -/
lemma tailOrbitFirstExp_succ (h M : ℕ) :
    tailOrbitFirstExp h (M + 1) = (tailOrbitFirstExp h M) ^ 2 := by
  rw [tailOrbitFirstExp, tailOrbitFirstExp, tail_diff_succ]
  let d : ℝ := totientTail (M + h) - totientTail M
  let a : ℤ := deltaTotient h (M + 1)
  have hexponent :
      (((2 * Real.pi * (2 * d - (a : ℝ)) : ℝ) : ℂ) * Complex.I) =
        2 * (((2 * Real.pi * d : ℝ) : ℂ) * Complex.I) +
          (-(a : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    dsimp [d, a]
    ring
  rw [hexponent, Complex.exp_add]
  have hperiod :
      Complex.exp ((-(a : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-a) using 1
    push_cast
    ring
  rw [hperiod, mul_one]
  exact Complex.exp_nat_mul _ 2

/-- Every later first phase is obtained from an earlier one by an exact
power-of-two iterate.  Thus no carry information survives in the phase orbit
beyond the single starting value. -/
lemma tailOrbitFirstExp_add (h M k : ℕ) :
    tailOrbitFirstExp h (M + k) =
      (tailOrbitFirstExp h M) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, tailOrbitFirstExp_succ, ih]
      simp only [pow_succ, pow_mul]

/-- Initial-phase normal form for the whole tail orbit. -/
lemma tailOrbitFirstExp_eq_initial_pow_two (h N : ℕ) :
    tailOrbitFirstExp h N =
      (tailOrbitFirstExp h 0) ^ (2 ^ N) := by
  simpa using tailOrbitFirstExp_add h 0 N

/-- Exact initial-angle formula for the actual totient phase.  The discarded
prefix is integral, so the starting phase is the additive character of
`(2^h - 1)` times the original #249 series. -/
theorem tailOrbitFirstExp_zero_eq_scaled_angle (h : ℕ) :
    tailOrbitFirstExp h 0 =
      Complex.exp
        (((2 * Real.pi *
          (((2 : ℝ) ^ h - 1) *
            (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) : ℝ) : ℂ) *
          Complex.I) := by
  rw [tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp]
  simp [scaledTotientSeriesFirstExp]

/-- Landing at phase `1` is exactly integrality of the corresponding actual
tail difference. -/
lemma tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int (h N : ℕ) :
    tailOrbitFirstExp h N = 1 ↔
      totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro hphase
    change Complex.exp
      ((((2 * Real.pi *
        (totientTail (N + h) - totientTail N) : ℝ) : ℂ) * Complex.I)) = 1 at hphase
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hphase
    refine ⟨m, ?_⟩
    have him := congrArg Complex.im hm
    have hscalar :
        2 * Real.pi * (totientTail (N + h) - totientTail N) =
          (m : ℝ) * (2 * Real.pi) := by
      simpa using him
    have hpi : 0 < 2 * Real.pi := by positivity
    nlinarith
  · rintro ⟨m, hm⟩
    rw [tailOrbitFirstExp]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨m, ?_⟩
    rw [← hm]
    push_cast
    ring

/-- Exact classification of the exceptional arithmetic obstruction: the
initial phase reaches `1` after finitely many squarings exactly when its real
angle `(2^h - 1) S` is dyadic. -/
theorem exists_tailOrbitFirstExp_zero_pow_two_eq_one_iff_dyadic (h : ℕ) :
    (∃ k : ℕ, (tailOrbitFirstExp h 0) ^ (2 ^ k) = 1) ↔
      IsDyadicReal
        (((2 : ℝ) ^ h - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by
  constructor
  · rintro ⟨k, hroot⟩
    have hkphase : tailOrbitFirstExp h k = 1 := by
      rw [tailOrbitFirstExp_eq_initial_pow_two, hroot]
    obtain ⟨d, hd⟩ :=
      (tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int h k).mp hkphase
    refine ⟨k, d + ((totientPrefix (k + h) : ℤ) - (totientPrefix k : ℤ)), ?_⟩
    have hdiff := tail_diff_eq_scaled_totient_series_sub_prefix h k
    push_cast
    nlinarith [hdiff]
  · rintro ⟨k, d, hd⟩
    refine ⟨k, ?_⟩
    have hmem :
        totientTail (k + h) - totientTail k ∈ Set.range ((↑) : ℤ → ℝ) := by
      refine ⟨d - ((totientPrefix (k + h) : ℤ) - (totientPrefix k : ℤ)), ?_⟩
      have hdiff := tail_diff_eq_scaled_totient_series_sub_prefix h k
      push_cast
      nlinarith [hdiff]
    have hkphase :=
      (tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int h k).mpr hmem
    rwa [tailOrbitFirstExp_eq_initial_pow_two] at hkphase

/-- The prime-index strict-gap hypothesis is exactly a statement about the
power-of-two orbit of one initial phase for each shift. -/
theorem naturalPrimeTailOrbitStrictGap_iff_initial_phase :
    DTWNaturalPrimeTailOrbitStrictGap ↔
      ∀ h : ℕ, 0 < h →
        ∀ N₀ : ℕ, ∃ p : ℕ,
          max (N₀ + h + 1) (h + 5) ≤ p ∧
          p.Prime ∧
          ((tailOrbitFirstExp h 0) ^ (2 ^ (p - h - 1))).re < (9 / 10 : ℝ) := by
  constructor <;> intro hgap h hh N₀
  · obtain ⟨p, hpN, hp, hphase⟩ := hgap h hh N₀
    refine ⟨p, hpN, hp, ?_⟩
    rwa [tailOrbitFirstExp_eq_initial_pow_two] at hphase
  · obtain ⟨p, hpN, hp, hphase⟩ := hgap h hh N₀
    refine ⟨p, hpN, hp, ?_⟩
    rwa [tailOrbitFirstExp_eq_initial_pow_two]

/-- The phase `1` is absorbing for the exact squaring dynamics. -/
lemma tailOrbitFirstExp_eq_one_of_le
    {h M N : ℕ} (hMN : M ≤ N) (hM : tailOrbitFirstExp h M = 1) :
    tailOrbitFirstExp h N = 1 := by
  calc
    tailOrbitFirstExp h N = tailOrbitFirstExp h (M + (N - M)) := by
      congr 1
      omega
    _ = (tailOrbitFirstExp h M) ^ (2 ^ (N - M)) :=
      tailOrbitFirstExp_add h M (N - M)
    _ = 1 := by simp [hM]

/-- An absorbing phase at any time rigorously obstructs the cofinal strict-gap
producer for that shift.  This does not show that the actual totient orbit ever
enters the absorbing phase. -/
theorem not_naturalPrimeTailOrbitStrictGap_of_phase_one
    {h M : ℕ} (hh : 0 < h) (hM : tailOrbitFirstExp h M = 1) :
    ¬ DTWNaturalPrimeTailOrbitStrictGap := by
  intro hgap
  obtain ⟨p, hpN, _hp, hphase⟩ := hgap h hh M
  have hMN : M ≤ p - h - 1 := by omega
  have hone : tailOrbitFirstExp h (p - h - 1) = 1 :=
    tailOrbitFirstExp_eq_one_of_le hMN hM
  rw [hone] at hphase
  norm_num at hphase

/-- More generally, entering any dyadic root of unity obstructs the strict-gap
producer: finitely many squarings reach the absorbing phase `1`.  The source
does not prove that an actual totient phase is such a root. -/
theorem not_naturalPrimeTailOrbitStrictGap_of_dyadic_root
    {h M k : ℕ} (hh : 0 < h)
    (hroot : (tailOrbitFirstExp h M) ^ (2 ^ k) = 1) :
    ¬ DTWNaturalPrimeTailOrbitStrictGap := by
  apply not_naturalPrimeTailOrbitStrictGap_of_phase_one hh
  rw [tailOrbitFirstExp_add]
  exact hroot

/-- The existing exact certificate at time `14` excludes every dyadic-root
landing of depth at most `14` for each shift `1 ≤ h ≤ 16`.  This is a finite
unconditional class, not a global non-dyadicity theorem. -/
theorem tailOrbitFirstExp_zero_pow_two_ne_one_upto_sixteen
    {h k : ℕ} (h1 : 1 ≤ h) (h16 : h ≤ 16) (hk : k ≤ 14) :
    (tailOrbitFirstExp h 0) ^ (2 ^ k) ≠ 1 := by
  intro hroot
  have hkphase : tailOrbitFirstExp h k = 1 := by
    rw [tailOrbitFirstExp_eq_initial_pow_two, hroot]
  have h14phase : tailOrbitFirstExp h 14 = 1 :=
    tailOrbitFirstExp_eq_one_of_le hk hkphase
  exact tail_diff_not_int_upto_sixteen h h1 h16
    ((tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int h 14).mp h14phase)

/-- Non-dyadicity of the exact initial angle gives cofinally large adjacent
chords in the actual tail orbit.  This is elementary doubling expansivity,
not an equidistribution statement. -/
theorem cofinally_tailOrbitFirstExp_adjacent_chord_ge_one_of_not_dyadic
    (h : ℕ)
    (hnd : ¬ IsDyadicReal
      (((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))) :
    ∀ N₀, ∃ N ≥ N₀,
      1 ≤ ‖tailOrbitFirstExp h (N + 1) - tailOrbitFirstExp h N‖ := by
  simpa only [tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp] using
    cofinally_scaledTotientSeriesFirstExp_adjacent_chord_ge_one_of_not_dyadic h hnd

/-- A non-dyadic initial angle therefore has cofinally many nonpositive real
phases.  The conclusion is cofinal occurrence only; it supplies neither a
positive block density nor alignment with natural-prime indices. -/
theorem cofinally_tailOrbitFirstExp_re_nonpos_of_not_dyadic
    (h : ℕ)
    (hnd : ¬ IsDyadicReal
      (((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))) :
    ∀ N₀, ∃ N ≥ N₀, (tailOrbitFirstExp h N).re ≤ 0 := by
  intro N₀
  obtain ⟨N, hN, hchord⟩ :=
    cofinally_tailOrbitFirstExp_adjacent_chord_ge_one_of_not_dyadic h hnd N₀
  let z := tailOrbitFirstExp h N
  have hnorm : ‖z‖ = 1 := by
    dsimp [z]
    rw [tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp]
    exact norm_scaledTotientSeriesFirstExp h N
  have hnormSq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hchordEq :
      ‖tailOrbitFirstExp h (N + 1) - tailOrbitFirstExp h N‖ = ‖z - 1‖ := by
    rw [tailOrbitFirstExp_succ]
    dsimp [z]
    calc
      ‖tailOrbitFirstExp h N ^ 2 - tailOrbitFirstExp h N‖ =
          ‖tailOrbitFirstExp h N * (tailOrbitFirstExp h N - 1)‖ := by
            congr 1
            ring
      _ = ‖tailOrbitFirstExp h N - 1‖ := by
        rw [norm_mul, show ‖tailOrbitFirstExp h N‖ = 1 by simpa [z] using hnorm,
          one_mul]
  have hdist : 1 ≤ ‖z - 1‖ := by
    rwa [hchordEq] at hchord
  have hdistSq : ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, hnormSq]
    norm_num
  have hreHalf : z.re ≤ (1 / 2 : ℝ) := by
    have hsquare : 1 ≤ ‖z - 1‖ ^ 2 := by
      nlinarith [norm_nonneg (z - 1)]
    nlinarith
  by_cases hre : z.re ≤ 0
  · exact ⟨N, hN, by simpa [z] using hre⟩
  · refine ⟨N + 1, by omega, ?_⟩
    rw [tailOrbitFirstExp_succ]
    rw [Complex.normSq_apply] at hnormSq
    simp only [pow_two, Complex.mul_re]
    have hrepos : 0 < z.re := lt_of_not_ge hre
    dsimp [z] at hnormSq hreHalf hrepos ⊢
    nlinarith

/-- The missing arithmetic bridge is now explicit: cofinally many nonpositive
phases whose shifted indices are prime imply the existing strict prime-orbit
gap.  Non-dyadicity alone proves the phase occurrence above, but not this prime
alignment. -/
theorem naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift
    (hsupply : ∀ h : ℕ, 0 < h →
      ∀ N₀ : ℕ, ∃ N : ℕ,
        max N₀ 4 ≤ N ∧
        (N + h + 1).Prime ∧
        (tailOrbitFirstExp h N).re ≤ 0) :
    DTWNaturalPrimeTailOrbitStrictGap := by
  intro h hh N₀
  obtain ⟨N, hN, hp, hre⟩ := hsupply h hh N₀
  refine ⟨N + h + 1, ?_, hp, ?_⟩
  · apply max_le
    · omega
    · omega
  · have hindex : N + h + 1 - h - 1 = N := by omega
    rw [hindex]
    norm_num at hre ⊢
    linarith

/-- A strict `9/10` gap in the infinite phase leaves a positive truncation
budget and gives a finite `9/10` pointwise gap. -/
theorem naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap
    (hgap : DTWNaturalPrimeTailOrbitStrictGap) :
    DTWNaturalPivotPointEscape := by
  intro h hh N₀
  obtain ⟨p, hpN, hp, htail⟩ := hgap h hh N₀
  let N := p - h - 1
  have hN₀ : N₀ ≤ N := by
    dsimp [N]
    omega
  have hN4 : 4 ≤ N := by
    dsimp [N]
    omega
  have htailN :
      (tailOrbitFirstExp h N).re < (9 / 10 : ℝ) := by
    simpa [N] using htail
  let ε : ℝ := (9 / 10 : ℝ) - (tailOrbitFirstExp h N).re
  have hε : 0 < ε := by
    dsimp [ε]
    exact sub_pos.mpr htailN
  obtain ⟨L, hL, hroom, herror⟩ :=
    exists_natural_window_depth_with_error h N (h + 1) ε hε
  have hhL : h < L := by omega
  refine ⟨N, L, N, max_le hN₀ hN4, hhL, hroom, ?_, ?_⟩
  · apply (mem_pivotFiber_one_overlap_iff hN4 (Nat.le_of_lt hhL)).2
    refine ⟨le_rfl, by omega, ?_⟩
    have heq : N + h + 1 = p := by
      dsimp [N]
      omega
    rwa [heq]
  · calc
      windowFirstCos h N L
          ≤ (tailOrbitFirstExp h N).re + ε :=
        windowFirstCos_le_add_of_tailOrbitGap le_rfl herror
      _ = (9 / 10 : ℝ) := by
        dsimp [ε]
        ring

/-- The pointwise prime condition implies irrationality.  The condition itself
remains unproved for the totient orbit. -/
theorem irrational_totient_series_of_naturalPrimeTailOrbitStrictGap
    (hgap : DTWNaturalPrimeTailOrbitStrictGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_naturalPivotPointEscape
    (naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap hgap)

end ErdosProblems.Erdos249
