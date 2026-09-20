import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.TropicalCurvatureCarry

/-! Information lost by specific carry descriptions (`prop:b5` of the long
#249 manuscript).  Item (i) is the balanced-pulse family at a location `m`:
one common pre-pulse history, one common binary value, and a scaled tail at
`m` that takes every value `r = 0, …, R`, so a finite label set determining
that tail needs at least `R + 1` elements.  Item (ii) is the fixed-depth
reset of an affine binary orbit.  Item (iii) is the fixed-precision carry
completion. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-! ### (i) The balanced-pulse family -/

private lemma pulseTail_zero (m r N : ℕ) (hN : m + 1 ≤ N) :
    binaryCoeffTail (balancedPulseCoeff m r) N = 0 := by
  have h : ∀ j : ℕ,
      ((balancedPulseCoeff m r (N + j + 1) : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1) = 0 := by
    intro j
    rw [balancedPulseCoeff_eq_zero_of_ne (by omega) (by omega)]
    simp
  unfold binaryCoeffTail
  rw [tsum_congr h, tsum_zero]

/-- The scaled tail at the pulse site decodes the fresh parameter. -/
theorem balancedPulse_tail_at (m r : ℕ) (hm : 2 ≤ m)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffTail (balancedPulseCoeff m r) m = (r : ℝ) := by
  have hg := balancedPulseCoeff_le_self hm hr
  have hstep := binaryCoeffTail_succ (balancedPulseCoeff m r) hg m
  rw [pulseTail_zero m r (m + 1) le_rfl, balancedPulseCoeff_at_right] at hstep
  push_cast at hstep
  linarith

/-- Every tail strictly before the pulse site is the same for all parameters:
`T(N) = R/2^{m-N}`. -/
theorem balancedPulse_tail_before (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    ∀ k N : ℕ, N + k + 1 = m →
      binaryCoeffTail (balancedPulseCoeff m r) N
        = (balancedPulseRadius m : ℝ) / 2 ^ (k + 1) := by
  have hg := balancedPulseCoeff_le_self hm hr
  intro k
  induction k with
  | zero =>
      intro N hN
      have hNm : N + 1 = m := by omega
      have hstep := binaryCoeffTail_succ (balancedPulseCoeff m r) hg N
      rw [hNm, balancedPulse_tail_at m r hm hr, balancedPulseCoeff_at_left] at hstep
      have hcast : ((balancedPulseRadius m - r : ℕ) : ℝ)
          = (balancedPulseRadius m : ℝ) - (r : ℝ) := Nat.cast_sub hr
      rw [hcast] at hstep
      rw [pow_succ, pow_zero, one_mul, eq_div_iff (two_ne_zero)]
      linarith
  | succ k ih =>
      intro N hN
      have hIH := ih (N + 1) (by omega)
      have hstep := binaryCoeffTail_succ (balancedPulseCoeff m r) hg N
      have hzero : balancedPulseCoeff m r (N + 1) = 0 :=
        balancedPulseCoeff_eq_zero_of_ne (by omega) (by omega)
      rw [hIH, hzero] at hstep
      have hkey : (2 : ℝ) * binaryCoeffTail (balancedPulseCoeff m r) N
          * 2 ^ (k + 1) = (balancedPulseRadius m : ℝ) := by
        have hp : ((2 : ℝ) ^ (k + 1)) ≠ 0 := by positivity
        push_cast at hstep
        field_simp at hstep
        linarith
      rw [pow_succ, eq_div_iff (by positivity : ((2 : ℝ) ^ (k + 1) * 2) ≠ 0)]
      linear_combination hkey

/-- The whole family has the same binary value `R·2^{-m}`. -/
theorem balancedPulse_series (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffSeries (balancedPulseCoeff m r)
      = (balancedPulseRadius m : ℝ) / 2 ^ m := by
  have h0 : binaryCoeffSeries (balancedPulseCoeff m r)
      = binaryCoeffTail (balancedPulseCoeff m r) 0 := by
    unfold binaryCoeffSeries binaryCoeffTail
    exact tsum_congr fun n => by rw [Nat.zero_add]
  have hm1 : 0 + (m - 1) + 1 = m := by omega
  have h := balancedPulse_tail_before m hm r hr (m - 1) 0 hm1
  rw [h0, h, show m - 1 + 1 = m by omega]

/-- **The balanced-pulse family** (`prop:b5` (i)).  For `m ≥ 2` and
`R = ⌊(m+1)/2⌋`, every parameter `r ≤ R` gives a coefficient sequence that
vanishes off `{m, m+1}`, takes the values `R - r` and `2r` there, satisfies
`c(n) ≤ n`, has binary value `R·2^{-m}` and has the same scaled tail
`R·2^{-(m-N)}` at every position `N < m`; and its scaled tail at `m` is `r`. -/
theorem balancedPulse_common_history (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    (∀ n : ℕ, n ≠ m → n ≠ m + 1 → balancedPulseCoeff m r n = 0)
      ∧ balancedPulseCoeff m r m = balancedPulseRadius m - r
      ∧ balancedPulseCoeff m r (m + 1) = 2 * r
      ∧ (∀ n : ℕ, balancedPulseCoeff m r n ≤ n)
      ∧ binaryCoeffSeries (balancedPulseCoeff m r)
          = (balancedPulseRadius m : ℝ) / 2 ^ m
      ∧ (∀ N : ℕ, N < m → binaryCoeffTail (balancedPulseCoeff m r) N
          = (balancedPulseRadius m : ℝ) / 2 ^ (m - N))
      ∧ binaryCoeffTail (balancedPulseCoeff m r) m = (r : ℝ) := by
  refine ⟨fun n h1 h2 => balancedPulseCoeff_eq_zero_of_ne h1 h2,
    balancedPulseCoeff_at_left m r, balancedPulseCoeff_at_right m r,
    balancedPulseCoeff_le_self hm hr, balancedPulse_series m hm r hr, ?_,
    balancedPulse_tail_at m r hm hr⟩
  intro N hN
  have h := balancedPulse_tail_before m hm r hr (m - N - 1) N (by omega)
  rw [h, show m - N - 1 + 1 = m - N by omega]

/-- **A finite label set that determines the tail needs at least `R+1`
elements** (`prop:b5` (i), last sentence). -/
theorem balancedPulse_label_lower_bound {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ) (decode : Λ → ℕ)
    (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ :=
  balancedPulse_label_card_lower_bound label decode hdecode

/-- **No autonomous decoder** (`prop:b5` (i)): a state identifying all members
of one balanced-pulse family cannot recover every exact successor. -/
theorem balancedPulse_no_decoder_from_common_state
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r :=
  balancedPulse_no_autonomous_decoder m hm state hstate

/-! ### (ii) Reduction modulo `2^L` forgets the initial value -/

/-- **Fixed-depth reset** (`prop:b5` (ii)): two affine binary orbits with
different seeds differ by exactly `2^L(u₀ - v₀)` after `L` common steps, so
their endpoint residues modulo `2^L` agree. -/
theorem affineBinaryOrbit_difference_and_reset (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L = (2 : ℤ) ^ L * (u0 - v0)
      ∧ affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L] :=
  ⟨affineBinaryOrbit_sub a u0 v0 L, affineBinaryOrbit_mod_twoPow_eq a u0 v0 L⟩

/-! ### (iii) Fixed-precision valuation--unit symbols -/

/-- **Fixed-precision carry completion** (`prop:b5` (iii)): for a precision
`u ≥ 1`, a finite list of valuation--unit symbols with odd units and an
initial integer `e₀`, there are unrestricted high quotients `z_j` making
`c_j = 2^{ν_j}(a_j + 2^u z_j)` and `e_{j+1} = 2e_j + c_j` with
`|e_{j+1}| ≤ 2^{ν_j + u - 1}` at every step. -/
theorem fixed_precision_carry_completion (u : ℕ) (hu : 0 < u)
    (symbols : List VUSymbol) (hodd : ∀ σ ∈ symbols, Odd σ.unit) (e : ℤ) :
    ∃ states : List ℤ,
      VUOrbit u e symbols states ∧
      List.Forall₂ (fun σ e' => |e'| ≤ vuRadius u σ) symbols states :=
  fixedPrecisionTropicalNoGo u hu symbols hodd e

#print axioms balancedPulse_tail_at
#print axioms balancedPulse_tail_before
#print axioms balancedPulse_series
#print axioms balancedPulse_common_history
#print axioms balancedPulse_label_lower_bound
#print axioms balancedPulse_no_decoder_from_common_state
#print axioms affineBinaryOrbit_difference_and_reset
#print axioms fixed_precision_carry_completion
end ErdosProblems.Erdos249.PaperCompleteR21
