import Erdos249257.AdelicHeightObstruction

/-!
Paper-form restatements of two asserted environments of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`:

* `lem:scalar-localization` (line 7695) — the complementary denominator factor
  `x.den / H` survives scalar clearing, the named integer quotient
  `t = c / (x.den / H)` satisfies `H c x = t · x.num`, the positivity `0 < H`,
  and the Scope paragraph's size bound `x.den / H ≤ |c|` for `c ≠ 0` together
  with the `c = 0` degeneracy that makes the nonzero condition essential;
* `cor:mersenne-height` (line 7726) — the Mersenne specialisation
  `2^r (2^n − 1) < 2 x.den`, with the two intermediate facts the environment
  displays for its direct verification.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.AdelicHeightObstruction

/-! ## `lem:scalar-localization` -/

/-- Long `lem:scalar-localization`, every clause.

`H ∣ x.den` and `(c·x).den ∣ H` give: `H > 0` (the reduced denominator is
positive); the complementary factor `D = x.den / H` divides `|c|`, hence
divides `c` in `ℤ`; and with `t = c / D` — a genuine integer, not an
existential — one has `H·c·x = t·x.num`. -/
theorem paper_scalar_localization (x : ℚ) (c : ℤ) {H : ℕ}
    (hH : H ∣ x.den) (hscaled : ((c : ℚ) * x).den ∣ H) :
    0 < H ∧ x.den / H ∣ c.natAbs ∧ ((x.den / H : ℕ) : ℤ) ∣ c ∧
      (H : ℚ) * (c : ℚ) * x
        = ((c / ((x.den / H : ℕ) : ℤ) : ℤ) : ℚ) * (x.num : ℚ) := by
  have hHpos : 0 < H := Nat.pos_of_dvd_of_pos hH x.den_pos
  have hKc : x.den / H ∣ c.natAbs :=
    scalarLocalization_complement_dvd x c hH hscaled
  have hKcZ : ((x.den / H : ℕ) : ℤ) ∣ c := Int.natCast_dvd.mpr hKc
  refine ⟨hHpos, hKc, hKcZ, ?_⟩
  obtain ⟨t, ht⟩ := hKcZ
  have hDpos : 0 < x.den / H := Nat.div_pos (Nat.le_of_dvd x.den_pos hH) hHpos
  have hDne : ((x.den / H : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast hDpos.ne'
  have hquot : c / ((x.den / H : ℕ) : ℤ) = t := by
    rw [ht, Int.mul_ediv_cancel_left _ hDne]
  have hden : H * (x.den / H) = x.den := Nat.mul_div_cancel' hH
  have hdenQ : (H : ℚ) * ((x.den / H : ℕ) : ℚ) = (x.den : ℚ) := by
    exact_mod_cast hden
  rw [hquot, ht, Int.cast_mul, Int.cast_natCast, ← Rat.den_mul_eq_num x, ← hdenQ]
  ring

/-- Scope clause of `lem:scalar-localization`: a nonzero clearing coefficient
pays the complementary denominator in size. -/
theorem paper_scalar_localization_size_bound (x : ℚ) {c : ℤ} {H : ℕ}
    (hH : H ∣ x.den) (hscaled : ((c : ℚ) * x).den ∣ H) (hc : c ≠ 0) :
    x.den / H ≤ c.natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr hc)
    (scalarLocalization_complement_dvd x c hH hscaled)

/-- Scope clause of `lem:scalar-localization`: the nonzero condition is
essential.  `c = 0` clears every denominator and satisfies the divisibility
conclusion, with no positive lower bound on `|c|`. -/
theorem paper_scalar_localization_zero_degenerate (x : ℚ) (H : ℕ) :
    (((0 : ℤ) : ℚ) * x).den = 1 ∧ x.den / H ∣ (0 : ℤ).natAbs ∧
      (0 : ℤ).natAbs = 0 := by
  refine ⟨by simp, ?_, by simp⟩
  simp

/-! ## `cor:mersenne-height` -/

/-- Long `cor:mersenne-height`.  For a positive rational `x`, `r ≥ 0` and
`n ≥ 1`, a numerator `2`-power lower bound together with the Mersenne-scale
upper bound `x < 2/(2^n − 1)` forces `2^r·(2^n − 1) < 2·x.den`.

The first two conjuncts are the environment's own displayed intermediates for
the direct verification: writing `x = a/b` in lowest terms, `a ≥ 2^r` and
`a(2^n − 1) < 2b`. -/
theorem paper_mersenne_height (x : ℚ) {r n : ℕ} (hx : 0 < x) (hn : 1 ≤ n)
    (hpow : 2 ^ r ∣ x.num.natAbs) (hlt : x < (2 : ℚ) / ((2 ^ n - 1 : ℕ) : ℚ)) :
    2 ^ r ≤ x.num.natAbs ∧
      x.num.natAbs * (2 ^ n - 1) < 2 * x.den ∧
      2 ^ r * (2 ^ n - 1) < 2 * x.den := by
  have hnum_pos : 0 < x.num := Rat.num_pos.mpr hx
  have hMpos : 0 < 2 ^ n - 1 :=
    Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  refine ⟨Nat.le_of_dvd (Int.natAbs_pos.mpr hnum_pos.ne') hpow, ?_, ?_⟩
  · exact positiveRat_numDivisor_mul_lt_two_mul_den x hx hMpos dvd_rfl hlt
  · exact positiveRat_mersenne_height x hx (by omega) hpow hlt

#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization_size_bound
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization_zero_degenerate
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_height

end ErdosProblems.Erdos257.PaperCompleteR21
