import ErdosProblems.Erdos1049.ZudilinHeightRegion
import ErdosProblems.Erdos1049.HermitePadeNoGo
import ErdosProblems.Erdos1049.ZudilinConeArithmetic
import Mathlib.Combinatorics.Pigeonhole

/-!
# Erdős #1049: one integer certificate controls four separate obstructions

The single two-sided bracket

`2 ^ 64 < 3 ^ 41 < 2 ^ 65`

sharpens every parameter obstruction already recorded for `3 / 2`.

* The Archimedean height deficit against the Bundschuh--Väänänen frontier is
  bigger than `3 / 13`, uniformly over the whole admissible rectangular
  Hermite--Padé cone (`threeHalves_rectangular_hp_gap_gt_threeThirteenths`).
  The previous certificate `3 ^ 81 < 2 ^ 200` only gave `81 / 200` for the
  ratio itself and no cone-uniform gap at all.
* The four-jet counting threshold at bottom depth `41` drops from the
  `4 R + 2 S = 164 + 2 S` of `exists_distinct_binary_selectors_same_fourJet_of_rank`
  to `130 + 2 S`, and `130` is *exactly* optimal
  (`fourJet_card_gt_two_pow_of_rank_41`).
* The cubic Hankel producer must remove more than `39 / 41` of its raw
  denominator charge (`threeHalves_hankelChargeThreshold_lt_eightFortyOne`).
* The scalar cone misses by a fixed relative margin `17 / 41`
  (`three_two_scalar_margin_lt_explicit`).

The final section adds a general **bounded-fibre escape** pigeonhole.  Once an
analytic remainder is supplied as `g` together with a fibre bound, the generic
theorem yields a four-jet collision separated by `g`; no such concrete
remainder instantiation is formalized here.

No theorem here decides the arithmetic nature of the Lambert value at `3 / 2`.
-/

namespace ErdosProblems.Erdos1049

/-! ## The exact two-sided power certificate -/

/-- Upper half of the certificate. -/
theorem threePow_fortyOne_lt_twoPow_sixtyFive : 3 ^ 41 < 2 ^ 65 := by norm_num

/-- Lower half of the certificate: `65` cannot be replaced by `64`. -/
theorem twoPow_sixtyFour_lt_threePow_fortyOne : 2 ^ 64 < 3 ^ 41 := by norm_num

/-- The sharp rational upper bound on the logarithmic height ratio. -/
theorem logThree_div_logTwo_lt_sixtyFive_fortyOne :
    Real.log 3 / Real.log 2 < (65 : ℝ) / 41 := by
  have hpows : (3 : ℝ) ^ 41 < (2 : ℝ) ^ 65 := by
    exact_mod_cast threePow_fortyOne_lt_twoPow_sixtyFive
  have hlogs : Real.log ((3 : ℝ) ^ 41) < Real.log ((2 : ℝ) ^ 65) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) hpows
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  apply (div_lt_iff₀ hlog2).2
  nlinarith

/-- The sharp rational lower bound for the reciprocal ratio. -/
theorem fortyOne_sixtyFive_lt_logTwo_div_logThree :
    (41 : ℝ) / 65 < Real.log 2 / Real.log 3 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have h := logThree_div_logTwo_lt_sixtyFive_fortyOne
  rw [div_lt_iff₀ hlog2] at h
  apply (lt_div_iff₀ hlog3).2
  nlinarith

/-! ## The Archimedean deficit -/

/-- **Exact distance from the Bundschuh--Väänänen frontier.**  The two
certificates subtract exactly: `41/65 - 2/5 = 3/13`. -/
theorem threeHalves_bv_height_gap_gt_threeThirteenths :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - (1 / 2 - 1 / Real.pi ^ 2) := by
  have hratio := fortyOne_sixtyFive_lt_logTwo_div_logThree
  have hmargin := bundschuhVaananenMargin_lt_twoFifths
  nlinarith

/-- **The rectangular Hermite--Padé cone misses `3 / 2` uniformly.**  No
parameter choice inside the admissible region recovers even the first
`3 / 13` of the missing logarithmic height. -/
theorem threeHalves_rectangular_hp_gap_gt_threeThirteenths (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma := by
  have hgap := threeHalves_bv_height_gap_gt_threeThirteenths
  have hrect := rectangular_hp_threshold_le_classical rho sigma hrho hsigma
  linarith

/-! ## The cubic Hankel and scalar-cone deficits -/

/-- **Exact rational ceiling for the cubic Hankel charge.**  Starting from a
raw charge `4`, more than `39 / 41` of it must be removed. -/
theorem threeHalves_hankelChargeThreshold_lt_eightFortyOne :
    (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := by
  have h := logThree_div_logTwo_lt_sixtyFive_fortyOne
  linarith

/-! ## Zudilin scalar-content ceiling -/

/-- **Abstract scalar-ceiling comparison.**  For positive `N`, the polynomial
ceiling `N^3-N` is strictly below the `39/41` fraction of the raw charge
`4N^3-3N^2` used in the `p=3/2` bookkeeping.  This theorem proves that exact
integer inequality only; it does not itself establish that a source scalar
factor has degree at most `N^3-N`.  The source-facing factor derivation and any
application of this ceiling are separate, explicit premises. -/
theorem zudilinScalarContent_ceiling_lt_required (N : ℤ) (hN : 0 < N) :
    41 * (N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  have hsq : 0 ≤ (230 * N - 117) ^ 2 := sq_nonneg (230 * N - 117)
  have hquad : 0 < 115 * N ^ 2 - 117 * N + 41 := by
    nlinarith
  have hproduct : 0 < N * (115 * N ^ 2 - 117 * N + 41) :=
    mul_pos hN hquad
  nlinarith

/-- Any extracted degree satisfying the explicit bound `extractedDegree ≤ N^3-N`
misses the required `39/41` raw-charge threshold.  A source application must
establish that bound separately; further divisibility of the primitive
residual Hankel matrix would then be needed to close the charge gap. -/
theorem zudilinScalarContent_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 0 < N)
    (hextracted : extractedDegree ≤ N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  have hceiling := zudilinScalarContent_ceiling_lt_required N hN
  linarith

/-! ## Zudilin scalar-plus-border ceiling -/

/-- **Abstract scalar-plus-border ceiling comparison.**  For `N ≥ 2`, the
deliberately overgenerous combined polynomial ceiling `2 * N^3 - N` misses the
explicit `39/41` charge threshold.  This theorem checks that integer
comparison only; it does not prove that scalar content and southeast `Phi_d`
border factors in the source attain those individual ceilings.  The
source-facing residual and border-factor derivation, and any use of this
combined ceiling, are separate premises. -/
theorem zudilinScalarPlusBorder_ceiling_lt_required (N : ℤ) (hN : 2 ≤ N) :
    41 * (2 * N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  have hx : 0 ≤ N - 2 := by omega
  have hquad : 0 < 74 * N ^ 2 - 117 * N + 41 := by
    nlinarith [sq_nonneg (N - 2)]
  have hproduct : 0 < N * (74 * N ^ 2 - 117 * N + 41) := by
    nlinarith
  nlinarith

/-- Any extraction satisfying the explicit bound `extractedDegree ≤ 2 * N^3-N`
still misses the required charge.  A source application must establish that
combined bound separately; higher residual valuations, genuine determinant
cancellation, or another integral model would then be needed to close the
remaining gap. -/
theorem zudilinScalarPlusBorder_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 2 ≤ N)
    (hextracted : extractedDegree ≤ 2 * N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  have hceiling := zudilinScalarPlusBorder_ceiling_lt_required N hN
  linarith

/-! ## Associated-graded Hankel row coefficients -/

/-- The source backward-shift induction on a hypergeometric tail has this
associated-graded transition.  A positive tail state moves down with sign
`-1`; state zero can emit state `s` with coefficient `a (s+1)`.  This finite
recurrence isolates the only coefficient data needed to sharpen Zudilin's
Hankel `q`-order lower bound to an equality. -/
def hankelAssociatedCoeff (a : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, 0 => ∑ s ∈ Finset.range (j + 1),
      a (s + 1) * hankelAssociatedCoeff a j s
  | j + 1, t + 1 => -hankelAssociatedCoeff a j t

/-- **Associated-graded reciprocal law.**  Suppose `h` is the coefficient
sequence reciprocal to `1 + sum_(r>=1) a_r X^r`, expressed through its exact
coefficient recurrence.  After `j` source row transformations, the leading
coefficient contributed by tail state `t` is
`(-1)^j h_(j-t)` for `t ≤ j`, and zero otherwise.

This kernel-checks the all-depth combinatorial induction used by the
source-facing proof in `HankelQOrderComputationalLab.md`; it is not a finite
rank calculation. -/
theorem hankelAssociatedCoeff_eq_reciprocal
    (a h : ℕ → ℤ) (hzero : h 0 = 1)
    (hrec : ∀ j, h (j + 1) =
      -(∑ s ∈ Finset.range (j + 1), a (s + 1) * h (j - s))) :
    ∀ j t, hankelAssociatedCoeff a j t =
      if t ≤ j then (-1 : ℤ) ^ j * h (j - t) else 0 := by
  intro j
  induction j with
  | zero =>
      intro t
      cases t with
      | zero => simp [hankelAssociatedCoeff, hzero]
      | succ t => simp [hankelAssociatedCoeff]
  | succ j ih =>
      intro t
      cases t with
      | zero =>
          rw [hankelAssociatedCoeff, if_pos (Nat.zero_le (j + 1))]
          calc
            ∑ s ∈ Finset.range (j + 1),
                a (s + 1) * hankelAssociatedCoeff a j s =
                ∑ s ∈ Finset.range (j + 1),
                  a (s + 1) * ((-1 : ℤ) ^ j * h (j - s)) := by
                    apply Finset.sum_congr rfl
                    intro s hs
                    rw [ih, if_pos]
                    exact Nat.le_of_lt_succ (Finset.mem_range.mp hs)
            _ = (-1 : ℤ) ^ j *
                (∑ s ∈ Finset.range (j + 1), a (s + 1) * h (j - s)) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro s _
                  ring
            _ = (-1 : ℤ) ^ (j + 1) * h (j + 1) := by
                  rw [hrec]
                  ring
      | succ t =>
          rw [hankelAssociatedCoeff]
          by_cases ht : t ≤ j
          · rw [ih, if_pos ht, if_pos (Nat.succ_le_succ ht)]
            have hsub : j + 1 - (t + 1) = j - t := by omega
            rw [hsub, pow_succ]
            ring
          · have hsucc : ¬t + 1 ≤ j + 1 :=
              fun h => ht (Nat.le_of_succ_le_succ h)
            rw [ih, if_neg ht, if_neg hsucc]
            norm_num

/-- The two source-tail families have reciprocal-coefficient numerators which
add to the claimed transformed-row coefficient.  This is the exact algebraic
fan-in after the associated-graded reciprocal law: the `t=0` contribution and
the sum of `1 ≤ t ≤ j` contributions combine without cancellation. -/
theorem zudilinTransformedTailNumerators_add (j : ℤ) :
    (j + 1) * (j + 2) * (2 * j + 3) + j * (j + 1) * (j + 2) =
      3 * (j + 1) ^ 2 * (j + 2) := by
  ring

/-- **Quantitative scalar-cone deficit.**  The positive-`C₀` scalar ray does
not merely have the wrong sign; it misses by a fixed relative margin. -/
theorem three_two_scalar_margin_lt_explicit {C0 C1 : ℝ}
    (hC0 : 0 < C0) (hsource : 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 < -((17 : ℝ) / 41) * C0 * Real.log 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h := logThree_div_logTwo_lt_sixtyFive_fortyOne
  rw [div_lt_iff₀ hlog2] at h
  nlinarith

/-! ## The four-jet rank threshold -/

/-- **Power-certificate compiler.**  Any certified binary upper bound
`3 ^ p < 2 ^ q` improves the four-jet rank threshold from the generic
`4 R + 2 S` to `2 q T + 2 S` at bottom depth `R = p T`. -/
theorem exists_distinct_binary_selectors_same_fourJet_of_power_certificate
    {n p q T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (hpq : 3 ^ p < 2 ^ q) (hT : 0 < T)
    (hrank : 2 * q * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (p * T) S W forms ε = selectedFourJetSum (p * T) S W forms η := by
  apply exists_distinct_binary_selectors_same_fourJet forms
  rw [fourJetSignature_card]
  have hpow : ((3 : ℕ) ^ p) ^ (2 * T) < ((2 : ℕ) ^ q) ^ (2 * T) :=
    Nat.pow_lt_pow_left hpq (by omega)
  have hleft : (3 ^ (p * T)) ^ 2 = ((3 : ℕ) ^ p) ^ (2 * T) := by
    rw [← pow_mul, ← pow_mul]; ring_nf
  have hright : ((2 : ℕ) ^ q) ^ (2 * T) * (2 ^ S) ^ 2 = 2 ^ (2 * q * T + 2 * S) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  calc (3 ^ (p * T)) ^ 2 * (2 ^ S) ^ 2
      = ((3 : ℕ) ^ p) ^ (2 * T) * (2 ^ S) ^ 2 := by rw [hleft]
    _ < ((2 : ℕ) ^ q) ^ (2 * T) * (2 ^ S) ^ 2 :=
        Nat.mul_lt_mul_of_lt_of_le hpow (le_refl _) (by positivity)
    _ = 2 ^ (2 * q * T + 2 * S) := hright
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hrank

/-- **The `R = 41` instance.**  The threshold drops from `164 T + 2 S` to
`130 T + 2 S`. -/
theorem exists_distinct_binary_selectors_same_fourJet_of_rank_41
    {n T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ) (hT : 0 < T)
    (hrank : 130 * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (41 * T) S W forms ε = selectedFourJetSum (41 * T) S W forms η := by
  apply exists_distinct_binary_selectors_same_fourJet_of_power_certificate
    (p := 41) (q := 65) (T := T) forms threePow_fortyOne_lt_twoPow_sixtyFive hT
  omega

/-- **`130` is exactly optimal.**  With only `129 + 2 S` binary forms the
four-jet target is still strictly larger than the selector space, so the
counting argument genuinely cannot fire one row earlier. -/
theorem fourJet_card_gt_two_pow_of_rank_41 (S : ℕ) :
    2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) := by
  rw [fourJetSignature_card]
  have hlow : (2 : ℕ) ^ 129 < (3 ^ 41) ^ 2 := by norm_num
  calc (2 : ℕ) ^ (129 + 2 * S) = 2 ^ 129 * (2 ^ S) ^ 2 := by
        rw [pow_add, ← pow_mul]; ring_nf
    _ < (3 ^ 41) ^ 2 * (2 ^ S) ^ 2 := by
        exact Nat.mul_lt_mul_of_lt_of_le hlow (le_refl _) (by positivity)

/-! ## Bounded-fibre escape -/

/-- **Bounded-fibre escape.**  If every fibre of `g` has at most `k` points
and the domain is larger than `card β * k`, then some `f`-collision is
separated by `g`.

Applied with `f` the four-jet signature and `g` the selected analytic
remainder, this converts a bound `k` on remainder multiplicity into a jet
collision outside the remainder nullspace: each extra binary form beyond the
exact entropy threshold doubles the tolerated degeneracy. -/
theorem exists_ne_map_eq_map_ne_of_card_mul_lt {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ) (k : ℕ)
    (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k)
    (hcard : Fintype.card β * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧ g x ≠ g y := by
  by_contra hbad
  push_neg at hbad
  have hfactor : ∀ x y : α, f x = f y → g x = g y := by
    intro x y hxy
    by_cases hne : x = y
    · rw [hne]
    · exact hbad x y hne hxy
  have hfiber : ∀ b : β, (Finset.univ.filter fun x => f x = b).card ≤ k := by
    intro b
    by_cases hemp : (Finset.univ.filter fun x => f x = b).Nonempty
    · obtain ⟨x0, hx0⟩ := hemp
      have hsub : (Finset.univ.filter fun x => f x = b)
          ⊆ (Finset.univ.filter fun y => g y = g x0) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx0 ⊢
        exact hfactor x x0 (hx.trans hx0.symm)
      exact le_trans (Finset.card_le_card hsub) (hg x0)
    · rw [Finset.not_nonempty_iff_eq_empty] at hemp
      simp [hemp]
  have hcount : Fintype.card α ≤ Fintype.card β * k := by
    have hpart := Finset.card_eq_sum_card_fiberwise
      (f := f) (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
      (fun x _ => Finset.mem_univ (f x))
    rw [← Finset.card_univ, ← Finset.card_univ, hpart]
    calc ∑ b ∈ (Finset.univ : Finset β), (Finset.univ.filter fun x => f x = b).card
        ≤ ∑ _b ∈ (Finset.univ : Finset β), k := Finset.sum_le_sum fun b _ => hfiber b
      _ = (Finset.univ : Finset β).card * k := by
          rw [Finset.sum_const, smul_eq_mul]
  omega

end ErdosProblems.Erdos1049
