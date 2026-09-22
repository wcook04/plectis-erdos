import ErdosProblems.Erdos249.TotientStrictPrimeEscape
import Erdos249257.CarrySurvivorExtinction

/-! Paper-form restatements of the doubling-orbit block of the long #249
manuscript:

* `lem:orbit` (the doubling identity): `R_{N+1} = 2R_N - φ(N+1)`,
  `R_{N+h} - R_N = 2^N α_h - (Φ_{N+h} - Φ_N)` with `α_h = (2^h-1)S`, hence
  `R_{N+h} - R_N ≡ 2^N α_h (mod 1)`, `e(R_{N+h}-R_N) = e(2^N α_h)`, and for
  fixed `h` the phases are the forward `x ↦ 2x` orbit of `α_h mod 1`;
* `prop:transfer`: a `89/100` cosine block gap on cofinally many blocks, for
  every `h ≥ 1`, implies `S ∉ ℚ`;
* `prop:route4`: `C(h,N,h)` holds whenever the distance from `2^{N+h}S-2^N S`
  to every integer exceeds `2(N+2h+2)/2^h`.

Here `R_N = totientTail N`, `Φ_N = totientPrefix N`, `D(h,N,L) =
windowDiscrepancy h N L` and `C(h,N,L) = certifiedKill h N L`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-! ### `lem:orbit` -- the doubling identity -/

/-- **The carry recurrence.**  `R_{N+1} = 2R_N - φ(N+1)` for every `N ≥ 0`. -/
theorem orbit_tail_recurrence (N : ℕ) :
    totientTail (N + 1) = 2 * totientTail N - (Nat.totient (N + 1) : ℝ) :=
  totientTail_succ N

/-- **The doubling identity.**  With `α_h = (2^h-1)S`,
`R_{N+h} - R_N = 2^N α_h - (Φ_{N+h} - Φ_N)` for all `N ≥ 0` and `h ≥ 1`. -/
theorem orbit_tail_diff_eq (h N : ℕ) :
    totientTail (N + h) - totientTail N
      = (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        - ((totientPrefix (N + h) : ℝ) - (totientPrefix N : ℝ)) := by
  rw [tail_diff_eq_scaled_totient_series_sub_prefix h N]
  ring

/-- `R_{N+h} - R_N ≡ 2^N α_h (mod 1)`: the difference of the two sides is an
integer. -/
theorem orbit_tail_diff_sub_scaled_is_int (h N : ℕ) :
    ∃ z : ℤ,
      totientTail (N + h) - totientTail N
          - (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        = (z : ℝ) := by
  refine ⟨-((totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ)), ?_⟩
  rw [orbit_tail_diff_eq h N]
  push_cast
  ring

/-- **The first character of the tail difference is the orbit character**:
`e(R_{N+h} - R_N) = e(2^N α_h)` with `e(x) = exp(2πix)`. -/
theorem orbit_tail_diff_firstChar_eq (h N : ℕ) :
    Complex.exp
        (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) * Complex.I)
      = Complex.exp
        (((2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) : ℝ) : ℂ) * Complex.I) := by
  have hmain := tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp h N
  simpa [tailOrbitFirstExp, scaledTotientSeriesFirstExp] using hmain

/-- The `N`-th iterate of the doubling map. -/
theorem doublingMap_iterate_apply (α : ℝ) (N : ℕ) :
    (fun x : ℝ => 2 * x)^[N] α = 2 ^ N * α := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      ring

/-- **The phases are the forward doubling orbit.**  For fixed `h`, the residue
`R_{N+h} - R_N mod 1` is the `N`-th point of the forward orbit of `α_h mod 1`
under `x ↦ 2x`. -/
theorem orbit_tail_diff_fract_eq_doubling_orbit (h N : ℕ) :
    Int.fract (totientTail (N + h) - totientTail N)
      = Int.fract
          ((fun x : ℝ => 2 * x)^[N]
            (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))) := by
  obtain ⟨z, hz⟩ := orbit_tail_diff_sub_scaled_is_int h N
  rw [doublingMap_iterate_apply]
  have hsum : totientTail (N + h) - totientTail N
      = (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        + (z : ℝ) := by linarith
  rw [hsum, Int.fract_add_intCast]

/-! ### `prop:transfer` -- transfer to the doubling orbit -/

/-- **Transfer to the doubling orbit.**  If for every `h ≥ 1` and every `X₀`
there is `X ≥ max(X₀,1)` with
`∑_{N=X}^{2X-1} cos(2π 2^N α_h) ≤ (89/100) X`, then `S` is irrational. -/
theorem irrational_totientSeries_of_block_cosine_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))))
        ≤ (89 / 100 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply ErdosProblems.Erdos249.irrational_totient_series_of_tailOrbitBlockGap
  intro h hh X₀
  obtain ⟨X, hX, hsum⟩ := hgap h hh X₀
  refine ⟨X, hX, ?_⟩
  have hcongr :
      (∑ N ∈ Finset.Ico X (2 * X), (tailOrbitFirstExp h N).re)
        = ∑ N ∈ Finset.Ico X (2 * X),
            Real.cos (2 * Real.pi *
              ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
                (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))) := by
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp, scaledTotientSeriesFirstExp,
      Complex.exp_ofReal_mul_I_re]
  rw [hcongr]
  exact hsum

/-! ### `prop:route4` -- a full-depth phase criterion -/

/-- The elementary bracket step behind the depth-`h` certificate. -/
theorem bracket_of_two_sided_separation
    {c P m δ : ℝ} (_hc : 0 < c) (_hm0 : 0 ≤ m) (_hmP : m < P)
    (hδ : |δ| < c) (h1 : 2 * c < |m + δ|) (h2 : 2 * c < |m + δ - P|) :
    c < m ∧ m < P - c := by
  obtain ⟨hd1, hd2⟩ := abs_lt.mp hδ
  constructor
  · rcases abs_cases (m + δ) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h1 <;> linarith
  · rcases abs_cases (m + δ - P) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h2 <;> linarith

/-- **`prop:route4`.**  `C(h,N,h)` holds whenever the distance from
`2^{N+h}S - 2^N S` to every integer exceeds `2(N+2h+2)/2^h`. -/
theorem certifiedKill_of_fullDepth_phase_separation (h N : ℕ)
    (hsep : ∀ k : ℤ,
      2 * ((N : ℝ) + 2 * h + 2) / 2 ^ h <
        |(2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
            - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (k : ℝ)|) :
    certifiedKill h N h := by
  have h2posR : (0 : ℝ) < 2 ^ h := by positivity
  have h2posZ : (0 : ℤ) < 2 ^ h := by positivity
  have hmnn : 0 ≤ windowDiscrepancy h N h % 2 ^ h :=
    Int.emod_nonneg _ (ne_of_gt h2posZ)
  have hmlt : windowDiscrepancy h N h % 2 ^ h < 2 ^ h :=
    Int.emod_lt_of_pos _ h2posZ
  have hdivmod :
      (2 : ℤ) ^ h * (windowDiscrepancy h N h / 2 ^ h)
          + windowDiscrepancy h N h % 2 ^ h
        = windowDiscrepancy h N h :=
    Int.mul_ediv_add_emod _ _
  have hApow : (windowDiscrepancy h N h : ℝ)
      = 2 ^ h * ((windowDiscrepancy h N h / 2 ^ h : ℤ) : ℝ)
        + ((windowDiscrepancy h N h % 2 ^ h : ℤ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hdivmod
    push_cast at this
    linarith
  -- the truncation remainder
  have hdabs := abs_tail_diff_lt h (N + h)
  push_cast at hdabs
  have hwin := tail_diff_eq_windowDiscrepancy_div_add_shifted h N h
  have hscaled := tail_diff_eq_scaled_totient_series_sub_prefix h N
  have hstep :
      (((windowDiscrepancy h N h % 2 ^ h : ℤ) : ℝ)
          + (totientTail (N + h + h) - totientTail (N + h))) / 2 ^ h
        = totientTail (N + h) - totientTail N
          - ((windowDiscrepancy h N h / 2 ^ h : ℤ) : ℝ) := by
    rw [hwin, hApow]
    field_simp
    ring
  set K : ℤ :=
    (windowDiscrepancy h N h / 2 ^ h) + (totientPrefix (N + h) : ℤ)
      - (totientPrefix N : ℤ) with hKdef
  have hKcast : (K : ℝ)
      = ((windowDiscrepancy h N h / 2 ^ h : ℤ) : ℝ)
        + (totientPrefix (N + h) : ℝ) - (totientPrefix N : ℝ) := by
    rw [hKdef]; push_cast; ring
  have hkey :
      (2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
          - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (K : ℝ)
        = (((windowDiscrepancy h N h % 2 ^ h : ℤ) : ℝ)
            + (totientTail (N + h + h) - totientTail (N + h))) / 2 ^ h := by
    have hx : (2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        = (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1)
            * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
      rw [pow_add]; ring
    rw [hx, hstep, hKcast]
    linarith
  have hkey2 :
      (2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
          - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - ((K + 1 : ℤ) : ℝ)
        = (((windowDiscrepancy h N h % 2 ^ h : ℤ) : ℝ)
            + (totientTail (N + h + h) - totientTail (N + h)) - 2 ^ h) / 2 ^ h := by
    have hc2 : ((K + 1 : ℤ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
    have hrearr :
        (2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
            - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - ((K : ℝ) + 1)
          = ((2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
              - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (K : ℝ)) - 1 := by
      ring
    rw [hc2, hrearr, hkey]
    field_simp
  have hcancel : ∀ a b : ℝ, a / 2 ^ h < b / 2 ^ h → a < b := by
    intro a b hab
    have h1 : a / 2 ^ h * 2 ^ h < b / 2 ^ h * 2 ^ h :=
      mul_lt_mul_of_pos_right hab h2posR
    rwa [div_mul_cancel₀ a (ne_of_gt h2posR), div_mul_cancel₀ b (ne_of_gt h2posR)] at h1
  have hs1 := hsep K
  have hs2 := hsep (K + 1)
  rw [hkey, abs_div, abs_of_pos h2posR] at hs1
  rw [hkey2, abs_div, abs_of_pos h2posR] at hs2
  have hb1 := hcancel _ _ hs1
  have hb2 := hcancel _ _ hs2
  have hmR0 : (0 : ℝ) ≤ ((windowDiscrepancy h N h % 2 ^ h : ℤ) : ℝ) := by
    exact_mod_cast hmnn
  have hmRlt : ((windowDiscrepancy h N h % 2 ^ h : ℤ) : ℝ) < (2 : ℝ) ^ h := by
    have : ((windowDiscrepancy h N h % 2 ^ h : ℤ) : ℝ) < (((2 : ℤ) ^ h : ℤ) : ℝ) := by
      exact_mod_cast hmlt
    simpa using this
  have hcpos : (0 : ℝ) < (N : ℝ) + 2 * h + 2 := by positivity
  have hdlt : |totientTail (N + h + h) - totientTail (N + h)| < (N : ℝ) + 2 * h + 2 := by
    rw [abs_lt] at hdabs ⊢
    exact ⟨by linarith [hdabs.1], by linarith [hdabs.2]⟩
  obtain ⟨hlow, hhigh⟩ :=
    bracket_of_two_sided_separation hcpos hmR0 hmRlt hdlt hb1 hb2
  refine ⟨?_, ?_⟩
  · have hint : ((N : ℤ) + 2 * (h : ℤ) + 2) < windowDiscrepancy h N h % 2 ^ h := by
      exact_mod_cast hlow
    linarith
  · have hint : windowDiscrepancy h N h % 2 ^ h
        < (2 : ℤ) ^ h - ((N : ℤ) + 2 * (h : ℤ) + 2) := by
      exact_mod_cast hhigh
    linarith

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_recurrence
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_sub_scaled_is_int
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_firstChar_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.doublingMap_iterate_apply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_fract_eq_doubling_orbit
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_block_cosine_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.bracket_of_two_sided_separation
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_fullDepth_phase_separation
