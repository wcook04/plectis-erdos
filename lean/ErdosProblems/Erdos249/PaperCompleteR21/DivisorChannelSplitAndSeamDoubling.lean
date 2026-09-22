import Erdos249257.DiagonalFreshLossBridge

/-! Paper-form restatements of the long paper's divisor/complement split of the
totient difference `φ(2H+s) - φ(H+s)`:

* *The sum over divisor indices* — `∑_{d ∣ H, d ∣ s} μ(d) H/d = H φ(g)/g`
  with `g = gcd(H,s)`;
* *The divisor sum and its complement* — the full Möbius decomposition;
* *Doubling the full totient difference* — the even-seam inheritance law;
* *A doubling identity for two portions of the sum* — the lower pulse at
  offset `s` and its doubled top echo at offset `2s`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open scoped BigOperators
open Erdos249257
open Erdos249257.DiagonalFreshLossBridge

/-! ### The sum over divisor indices -/

private theorem sum_gcd_divisors_moebius_scaled {g H : ℕ}
    (hH : 0 < H) (hgH : g ∣ H) :
    ∑ d ∈ g.divisors,
        ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ) =
      ((H / g : ℕ) : ℤ) * (Nat.totient g : ℤ) := by
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgH hH
  calc
    ∑ d ∈ g.divisors, ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ)
        = ∑ d ∈ g.divisors,
            ((H / g : ℕ) : ℤ) *
              (ArithmeticFunction.moebius d * ((g / d : ℕ) : ℤ)) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          have hdg : d ∣ g := Nat.dvd_of_mem_divisors hd
          rw [← Nat.div_mul_div hgH hdg, Nat.cast_mul]
          ring
    _ = ((H / g : ℕ) : ℤ) *
          ∑ d ∈ g.divisors,
            ArithmeticFunction.moebius d * ((g / d : ℕ) : ℤ) := by
          rw [Finset.mul_sum]
    _ = ((H / g : ℕ) : ℤ) * (Nat.totient g : ℤ) := by
          rw [MersenneLambertLadder.sum_divisors_moebius_mul_div g hgpos]

private theorem gcd_divisor_filter (H s : ℕ) (hH : 0 < H) :
    {d ∈ H.divisors | d ∣ s} = (Nat.gcd H s).divisors := by
  have hgpos : 0 < Nat.gcd H s := Nat.gcd_pos_of_pos_left s hH
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdH, -⟩, hds⟩
    exact ⟨Nat.dvd_gcd hdH hds, hgpos.ne'⟩
  · rintro ⟨hdg, -⟩
    exact ⟨⟨hdg.trans (Nat.gcd_dvd_left H s), hH.ne'⟩,
      hdg.trans (Nat.gcd_dvd_right H s)⟩

private theorem sum_divisors_moebius_mul_div_rat {g : ℕ} (hg : 0 < g) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℚ) * ((g / d : ℕ) : ℚ) =
      (Nat.totient g : ℚ) := by
  have hZ := MersenneLambertLadder.sum_divisors_moebius_mul_div g hg
  have h2 :
      ((∑ d ∈ g.divisors,
          ArithmeticFunction.moebius d * ((g / d : ℕ) : ℤ) : ℤ) : ℚ) =
        ((Nat.totient g : ℤ) : ℚ) := by rw [hZ]
  push_cast at h2
  exact h2

/-- **The sum over divisor indices.**  For integers `H > 0` and `s ≥ 0`,
`∑_{d ∣ H, d ∣ s} μ(d) H/d = H φ(gcd(H,s))/gcd(H,s)`. -/
theorem sum_divisorIndices_mobius (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ) := by
  have hgpos : 0 < Nat.gcd H s := Nat.gcd_pos_of_pos_left s hH
  have hgne : ((Nat.gcd H s : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hgpos.ne'
  have hcore :
      ∑ d ∈ (Nat.gcd H s).divisors,
          (ArithmeticFunction.moebius d : ℚ) * ((Nat.gcd H s : ℚ) / (d : ℚ)) =
        (Nat.totient (Nat.gcd H s) : ℚ) := by
    rw [← sum_divisors_moebius_mul_div_rat hgpos]
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdg : d ∣ Nat.gcd H s := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdne : ((d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
    rw [Nat.cast_div hdg hdne]
  have hstep : ∀ d ∈ (Nat.gcd H s).divisors,
      (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ) =
        ((H : ℚ) / (Nat.gcd H s : ℚ)) *
          ((ArithmeticFunction.moebius d : ℚ) * ((Nat.gcd H s : ℚ) / (d : ℚ))) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdne : ((d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
    field_simp
  rw [gcd_divisor_filter H s hH, Finset.sum_congr rfl hstep, ← Finset.mul_sum,
    hcore]
  ring

/-- The standard identity `∑_{d ∣ g} μ(d)/d = φ(g)/g` for `g > 0`. -/
theorem sum_divisors_moebius_div_eq_totient_div {g : ℕ} (hg : 0 < g) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℚ) / (d : ℚ) =
      (Nat.totient g : ℚ) / (g : ℚ) := by
  have hgne : ((g : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hterm : ∀ d ∈ g.divisors,
      (ArithmeticFunction.moebius d : ℚ) / (d : ℚ) =
        (1 / (g : ℚ)) *
          ((ArithmeticFunction.moebius d : ℚ) * ((g / d : ℕ) : ℚ)) := by
    intro d hd
    have hdg : d ∣ g := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdne : ((d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
    rw [Nat.cast_div hdg hdne]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_divisors_moebius_mul_div_rat hg]
  ring

/-- `rad(H)` is the product of the distinct primes dividing `H`. -/
theorem squarefreeKernel_eq_prod_primeFactors (H : ℕ) :
    RadicalMobiusShadow.squarefreeKernel H = ∏ p ∈ H.primeFactors, p := rfl

/-- The same value after extracting `H/rad(H)`: the formal source's form. -/
theorem sum_divisorIndices_radical_form (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ) =
      ((H / RadicalMobiusShadow.squarefreeKernel H : ℕ) : ℤ) *
        (RepunitMobiusNumerator.gcdWordCoeff
          (RadicalMobiusShadow.squarefreeKernel H) s : ℤ) := by
  have h := oldMobiusIncrement_eq_scale_gcdWordCoeff H s hH
  rw [oldMobiusIncrement, ← Finset.sum_filter] at h
  exact h

/-! ### The divisor sum and its complement -/

/-- `φ(n) = ∑_{d ∣ n} μ(d) n/d`, the expansion the split is derived from. -/
theorem totient_eq_mobius_divisor_sum (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℤ) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ((n / d : ℕ) : ℤ) :=
  (MersenneLambertLadder.sum_divisors_moebius_mul_div n hn).symm

/-- An index dividing `H` divides either endpoint precisely when it divides
`s`, and its endpoint difference is then `μ(d) H/d`. -/
theorem divisorIndex_endpoint_behaviour {d H s : ℕ} (hdH : d ∣ H) :
    (d ∣ 2 * H + s ↔ d ∣ s) ∧ (d ∣ H + s ↔ d ∣ s) ∧
      (ArithmeticFunction.moebius d : ℚ) * ((2 * H + s : ℕ) : ℚ) / (d : ℚ) -
          (ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ) =
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ) := by
  refine ⟨(Nat.dvd_add_iff_right (hdH.mul_left 2)).symm,
    (Nat.dvd_add_iff_right hdH).symm, ?_⟩
  push_cast
  ring

/-- The paper's `d`-summand of the complementary sum at height `H`, offset `s`:
`μ(d)((2H+s)/d · 1_{d ∣ 2H+s} - (H+s)/d · 1_{d ∣ H+s})`. -/
noncomputable def complementSummand (d H s : ℕ) : ℚ :=
  (ArithmeticFunction.moebius d : ℚ) *
    (((2 * H + s : ℕ) : ℚ) / (d : ℚ) * (if d ∣ 2 * H + s then 1 else 0) -
      ((H + s : ℕ) : ℚ) / (d : ℚ) * (if d ∣ H + s then 1 else 0))

/-- Outside the divisor set the paper's summand is the tree's phase term. -/
theorem complementSummand_eq_phaseTerm {d H s : ℕ} (hd : 0 < d) (hdH : ¬d ∣ H) :
    complementSummand d H s = ((foreignChannelPhaseTerm d H s : ℤ) : ℚ) := by
  have hdne : ((d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  by_cases hTop : d ∣ 2 * H + s
  · have hLow : ¬d ∣ H + s := fun h =>
      foreign_endpoint_support_disjoint hdH ⟨hTop, h⟩
    rw [foreignChannelPhaseTerm_eq_of_top hdH hTop, complementSummand,
      if_pos hTop, if_neg hLow, Int.cast_mul, Int.cast_natCast,
      Nat.cast_div hTop hdne]
    ring
  · by_cases hLow : d ∣ H + s
    · rw [foreignChannelPhaseTerm_eq_neg_of_low hdH hLow, complementSummand,
        if_neg hTop, if_pos hLow, Int.cast_neg, Int.cast_mul, Int.cast_natCast,
        Nat.cast_div hLow hdne]
      ring
    · have hzero : foreignChannelPhaseTerm d H s = 0 := by
        simp [foreignChannelPhaseTerm, hTop, hLow]
      rw [hzero, complementSummand, if_neg hTop, if_neg hLow]
      push_cast
      ring

private theorem oldMobiusIncrement_value (H s : ℕ) (hH : 0 < H) :
    oldMobiusIncrement H s =
      ((H / Nat.gcd H s : ℕ) : ℤ) * (Nat.totient (Nat.gcd H s) : ℤ) := by
  rw [oldMobiusIncrement, ← Finset.sum_filter, gcd_divisor_filter H s hH,
    sum_gcd_divisors_moebius_scaled hH (Nat.gcd_dvd_left H s)]

private theorem foreign_range_eq_filtered_Icc (H s : ℕ) (hH : 0 < H) :
    (∑ d ∈ Finset.range (2 * H + s + 1),
        (if d ∣ H then (0 : ℤ) else foreignChannelPhaseTerm d H s)) =
      ∑ d ∈ {d ∈ Finset.Icc 1 (2 * H + s) | ¬d ∣ H},
        foreignChannelPhaseTerm d H s := by
  have hins : Finset.range (2 * H + s + 1) = insert 0 (Finset.Icc 1 (2 * H + s)) := by
    ext d
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 (2 * H + s) := by
    simp only [Finset.mem_Icc]
    omega
  have h0H : ¬(0 : ℕ) ∣ H := by
    rw [Nat.zero_dvd]
    exact hH.ne'
  have hTop0 : ¬(0 : ℕ) ∣ 2 * H + s := by
    rw [Nat.zero_dvd]
    omega
  have hLow0 : ¬(0 : ℕ) ∣ H + s := by
    rw [Nat.zero_dvd]
    omega
  have hzero : (if (0 : ℕ) ∣ H then (0 : ℤ) else foreignChannelPhaseTerm 0 H s) = 0 := by
    rw [if_neg h0H, foreignChannelPhaseTerm, if_neg hTop0, if_neg hLow0]
  rw [hins, Finset.sum_insert hnotmem, hzero, zero_add, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro d _
  by_cases hdH : d ∣ H <;> simp [hdH]

/-- **The divisor sum and its complement.**  For integers `H > 0` and `s ≥ 0`,
`φ(2H+s) - φ(H+s) = H φ(gcd(H,s))/gcd(H,s) + ∑_{1 ≤ d ≤ 2H+s, d ∤ H}
μ(d)((2H+s)/d · 1_{d ∣ 2H+s} - (H+s)/d · 1_{d ∣ H+s})`. -/
theorem totientDifference_eq_divisorPart_add_complement (H s : ℕ) (hH : 0 < H) :
    (Nat.totient (2 * H + s) : ℚ) - (Nat.totient (H + s) : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ) +
        ∑ d ∈ {d ∈ Finset.Icc 1 (2 * H + s) | ¬d ∣ H}, complementSummand d H s := by
  have hgpos : 0 < Nat.gcd H s := Nat.gcd_pos_of_pos_left s hH
  have hgH : Nat.gcd H s ∣ H := Nat.gcd_dvd_left H s
  have hgne : ((Nat.gcd H s : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hgpos.ne'
  have hZ : (Nat.totient (2 * H + s) : ℤ) - (Nat.totient (H + s) : ℤ) =
      ((H / Nat.gcd H s : ℕ) : ℤ) * (Nat.totient (Nat.gcd H s) : ℤ) +
        ∑ d ∈ {d ∈ Finset.Icc 1 (2 * H + s) | ¬d ∣ H},
          foreignChannelPhaseTerm d H s := by
    have h := diagonalHeightIncrement_eq_oldMobius_add_finiteForeign H s hH
    rw [diagonalHeightIncrement, oldMobiusIncrement_value H s hH,
      finiteForeignChannelIncrement_eq_phaseSum,
      foreign_range_eq_filtered_Icc H s hH] at h
    exact h
  have hbridge :
      ((∑ d ∈ {d ∈ Finset.Icc 1 (2 * H + s) | ¬d ∣ H},
          foreignChannelPhaseTerm d H s : ℤ) : ℚ) =
        ∑ d ∈ {d ∈ Finset.Icc 1 (2 * H + s) | ¬d ∣ H}, complementSummand d H s := by
    push_cast
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    exact (complementSummand_eq_phaseTerm (by omega) hd.2).symm
  have hQ := congrArg (fun z : ℤ => (z : ℚ)) hZ
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast] at hQ
  rw [hQ, hbridge, Nat.cast_div hgH hgne]
  ring

/-! ### Doubling the full totient difference -/

/-- `φ(2n) = 2φ(n)` for even `n`. -/
theorem totient_two_mul_even {n : ℕ} (hn : Even n) :
    Nat.totient (2 * n) = 2 * Nat.totient n :=
  Nat.totient_two_mul_of_even hn

/-- `φ(2n) = φ(n)` for odd `n`. -/
theorem totient_two_mul_odd {n : ℕ} (hn : Odd n) :
    Nat.totient (2 * n) = Nat.totient n :=
  Nat.totient_two_mul_of_odd hn

/-- **Doubling the full totient difference.**  For nonnegative integers `H, r`
with `H` even, `φ(4H+2r) - φ(2H+2r)` is `2(φ(2H+r) - φ(H+r))` when `r` is even
and `φ(2H+r) - φ(H+r)` when `r` is odd. -/
theorem totientDifference_doubling_seam (H r : ℕ) (hH : Even H) :
    (Even r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          2 * ((Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ))) ∧
      (Odd r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          (Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ)) := by
  have hrw : 2 * (2 * H) + 2 * r = 4 * H + 2 * r := by ring
  constructor
  · intro hr
    have h := diagonalHeightIncrement_two_mul_even hH hr
    simp only [diagonalHeightIncrement] at h
    rw [hrw] at h
    exact h
  · intro hr
    have h := diagonalHeightIncrement_two_mul_odd hH hr
    simp only [diagonalHeightIncrement] at h
    rw [hrw] at h
    exact h

/-! ### A doubling identity for two portions of the sum -/

/-- **A doubling identity for two portions of the sum.**  For `H > 0`, `s ≥ 0`,
`d ≥ 1` with `d ∤ H` and `d ∣ H+s`, the `d`-summands of the complementary sums
at offsets `s` and `2s` are `-μ(d)(H+s)/d` and `2μ(d)(H+s)/d`; the second is
`-2` times the first.  The divisibility pattern behind the second value is
`d ∣ 2H+2s` and `d ∤ H+2s`. -/
theorem complementSummand_low_double_echo {d H s : ℕ} (_hH : 0 < H) (_hd : 0 < d)
    (hdH : ¬d ∣ H) (hLow : d ∣ H + s) :
    complementSummand d H s =
        -((ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ)) ∧
      complementSummand d H (2 * s) =
        2 * ((ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ)) ∧
      (d ∣ 2 * H + 2 * s ∧ ¬d ∣ H + 2 * s) ∧
      complementSummand d H (2 * s) = -2 * complementSummand d H s := by
  have hTop : ¬d ∣ 2 * H + s := fun h =>
    foreign_endpoint_support_disjoint hdH ⟨h, hLow⟩
  have hTop2 : d ∣ 2 * H + 2 * s := by
    have h := hLow.mul_left 2
    simpa [Nat.mul_add] using h
  have hLow2 : ¬d ∣ H + 2 * s := by
    intro h
    have hs : d ∣ s := by
      have h' : d ∣ H + s + s := by
        rwa [show H + s + s = H + 2 * s by omega]
      exact (Nat.dvd_add_iff_right hLow).mpr h'
    have hHdvd : d ∣ H := by
      have h' : d ∣ s + H := by
        rwa [show s + H = H + s by omega]
      exact (Nat.dvd_add_iff_right hs).mpr h'
    exact hdH hHdvd
  refine ⟨?_, ?_, ⟨hTop2, hLow2⟩, ?_⟩
  · rw [complementSummand, if_neg hTop, if_pos hLow]
    ring
  · rw [complementSummand, if_pos hTop2, if_neg hLow2]
    push_cast
    ring
  · simp only [complementSummand]
    rw [if_pos hTop2, if_neg hLow2, if_neg hTop, if_pos hLow]
    push_cast
    ring

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_mobius
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_moebius_div_eq_totient_div
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.squarefreeKernel_eq_prod_primeFactors
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_radical_form
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_eq_mobius_divisor_sum
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.divisorIndex_endpoint_behaviour
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_eq_phaseTerm
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_eq_divisorPart_add_complement
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_even
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_odd
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_doubling_seam
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_low_double_echo
