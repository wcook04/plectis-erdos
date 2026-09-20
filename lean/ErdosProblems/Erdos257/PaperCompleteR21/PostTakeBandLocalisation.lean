import Erdos249257.HalfGreedyTwoThirdsBand

/-!
Paper-form restatement of `thm:two-thirds-band` (line 3524) of the long
Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

Every quantity is the paper's: a positive residual is written `1/R`, a take at
rank `b` uses `q = 2^b − 1`, the post-take reciprocal residual is `Rq/(q−R)`,
and the last-skip threshold is `m = 2^{c−1}` for the next take at rank `c`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21
open Erdos249257 Erdos249257.HalfGreedyTwoThirdsBand

/-- The dyadic test at a skipped rank `k`: the residual `1/R` passes
`ρ ≤ 2^{-k}` precisely when `R ≥ 2^k`. -/
theorem dyadic_test_iff_twoPow_le {R : ℚ} (hR : 0 < R) (k : ℕ) :
    1 / R ≤ 1 / 2 ^ k ↔ (2 : ℚ) ^ k ≤ R := by
  have hk : (0 : ℚ) < 2 ^ k := by positivity
  rw [div_le_div_iff₀ hR hk]
  constructor <;> intro h <;> linarith

/-- The new reciprocal residual after a take at rank `b` with `q = 2^b − 1`:
`1/(1/R − 1/q) = Rq/(q − R)`. -/
theorem postTake_reciprocal_formula {R q : ℚ} (hR : 0 < R) (hRq : R < q) :
    1 / (1 / R - 1 / q) = R * q / (q - R) := by
  have hq : (0 : ℚ) < q := lt_trans hR hRq
  have h1 : 1 / R - 1 / q = (q - R) / (R * q) := by
    field_simp
  rw [h1, one_div_div]

/-- Long `thm:two-thirds-band`, general localisation: with `0 < R < q` and a
last-skip threshold `m ≥ 1`, the last skipped rank fails the dyadic test exactly
when the post-take reciprocal lies in `(m − 1, m)`, equivalently when the
pre-take reciprocal lies in the band. -/
theorem postTake_dyadicFailure_iff_band {R q m : ℚ} (hR : 0 < R) (hRq : R < q)
    (hm : 1 ≤ m) :
    (m - 1 < R * q / (q - R) ∧ R * q / (q - R) < m) ↔
      (q * (m - 1) / (q + m - 1) < R ∧ R < q * m / (q + m)) :=
  postTakeUnsafeAt_iff_band hR hRq hm

/-- The general band has width `q²/((q+m)(q+m−1))`. -/
theorem band_width_general' {q m : ℚ} (hq : 0 < q) (hm : 1 ≤ m) :
    q * m / (q + m) - q * (m - 1) / (q + m - 1)
      = q ^ 2 / ((q + m) * (q + m - 1)) :=
  band_width_general hq hm

/-- For a single skipped rank the next take is at `c = b + 2`, so
`m = 2^{c−1} = 2^{b+1} = 2q + 2` with `q = 2^b − 1`. -/
theorem singleSkip_threshold (b : ℕ) :
    (2 : ℚ) ^ (b + 1) = 2 * ((2 : ℚ) ^ b - 1) + 2 := by
  rw [pow_succ]
  ring

/-- The single-skip band width is `q²/((3q+1)(3q+2)) < 1/9`. -/
theorem singleSkip_band_width {q : ℚ} (hq : 0 < q) :
    2 * q * (q + 1) / (3 * q + 2) - q * (2 * q + 1) / (3 * q + 1)
        = q ^ 2 / ((3 * q + 1) * (3 * q + 2)) ∧
      q ^ 2 / ((3 * q + 1) * (3 * q + 2)) < 1 / 9 :=
  ⟨band_width hq, band_width_lt_ninth hq⟩

/-- The single-skip band lies inside `2q < 3R < 2q + 2/3`. -/
theorem singleSkip_band_two_thirds {R q : ℚ} (hq : 0 < q)
    (h : q * (2 * q + 1) / (3 * q + 1) < R ∧ R < 2 * q * (q + 1) / (3 * q + 2)) :
    2 * q < 3 * R ∧ 3 * R < 2 * q + 2 / 3 :=
  three_mul_mem_of_twoThirdsBand hq h

/-- Integral `R` is excluded from the single-skip band. -/
theorem singleSkip_band_excludes_int {R q : ℚ} (hq : 0 < q) (mm n : ℤ)
    (hR : R = (mm : ℚ)) (hqn : q = (n : ℚ)) :
    ¬ (q * (2 * q + 1) / (3 * q + 1) < R ∧ R < 2 * q * (q + 1) / (3 * q + 2)) :=
  not_twoThirdsBand_of_int hq mm n hR hqn

/-- A reduced pre-take residual `p/(2D)` with `p`, `D`, `q` odd can fail the
dyadic test only if `p ≥ 7`; the divisibility by four of `6D − 2pq` is the step
used. -/
theorem singleSkip_seven_le {p D q : ℤ} (hp : 0 < p) (hD : 0 < D) (hq : 0 < q)
    (hpo : Odd p) (hDo : Odd D) (hqo : Odd q)
    (hband : q * (2 * q + 1) * p < 2 * D * (3 * q + 1) ∧
      2 * D * (3 * q + 2) < 2 * p * q * (q + 1)) :
    (4 : ℤ) ∣ (6 * D - 2 * p * q) ∧ 7 ≤ p :=
  ⟨four_dvd_bandDefect hpo hDo hqo, seven_le_of_intBand_odd hp hD hq hpo hDo hqo hband⟩

/-- The odd-coprime data `(p, D, b) = (17, 41, 3)` is a single-skip example that
fails the dyadic test: with `q = 2^3 − 1 = 7` the pre-take reciprocal
`R = 2D/p = 82/17` lies in the band. -/
theorem singleSkip_band_witness :
    Odd (17 : ℤ) ∧ Odd (41 : ℤ) ∧ Odd (7 : ℤ) ∧ (∃ x y : ℤ, x * 17 + y * 41 = 1) ∧
      (2 : ℚ) ^ 3 - 1 = 7 ∧
      ((7 : ℚ) * (2 * 7 + 1) / (3 * 7 + 1) < (2 * 41 : ℚ) / 17 ∧
        (2 * 41 : ℚ) / 17 < 2 * 7 * (7 + 1) / (3 * 7 + 2)) := by
  refine ⟨⟨8, by norm_num⟩, ⟨20, by norm_num⟩, ⟨3, by norm_num⟩, ⟨-12, 5, by norm_num⟩,
    by norm_num, ?_, ?_⟩ <;> norm_num

/-- Every asserted clause of long `thm:two-thirds-band`. -/
theorem paper_two_thirds_band :
    (∀ (R : ℚ) (k : ℕ), 0 < R → (1 / R ≤ 1 / 2 ^ k ↔ (2 : ℚ) ^ k ≤ R)) ∧
    (∀ R q : ℚ, 0 < R → R < q → 1 / (1 / R - 1 / q) = R * q / (q - R)) ∧
    (∀ R q m : ℚ, 0 < R → R < q → 1 ≤ m →
        ((m - 1 < R * q / (q - R) ∧ R * q / (q - R) < m) ↔
          (q * (m - 1) / (q + m - 1) < R ∧ R < q * m / (q + m)))) ∧
    (∀ q m : ℚ, 0 < q → 1 ≤ m →
        q * m / (q + m) - q * (m - 1) / (q + m - 1)
          = q ^ 2 / ((q + m) * (q + m - 1))) ∧
    (∀ b : ℕ, (2 : ℚ) ^ (b + 1) = 2 * ((2 : ℚ) ^ b - 1) + 2) ∧
    (∀ q : ℚ, 0 < q →
        2 * q * (q + 1) / (3 * q + 2) - q * (2 * q + 1) / (3 * q + 1)
            = q ^ 2 / ((3 * q + 1) * (3 * q + 2)) ∧
          q ^ 2 / ((3 * q + 1) * (3 * q + 2)) < 1 / 9) ∧
    (∀ R q : ℚ, 0 < q →
        (q * (2 * q + 1) / (3 * q + 1) < R ∧ R < 2 * q * (q + 1) / (3 * q + 2)) →
        2 * q < 3 * R ∧ 3 * R < 2 * q + 2 / 3) ∧
    (∀ (R q : ℚ) (mm n : ℤ), 0 < q → R = (mm : ℚ) → q = (n : ℚ) →
        ¬ (q * (2 * q + 1) / (3 * q + 1) < R ∧
          R < 2 * q * (q + 1) / (3 * q + 2))) ∧
    (∀ p D q : ℤ, 0 < p → 0 < D → 0 < q → Odd p → Odd D → Odd q →
        (q * (2 * q + 1) * p < 2 * D * (3 * q + 1) ∧
          2 * D * (3 * q + 2) < 2 * p * q * (q + 1)) →
        (4 : ℤ) ∣ (6 * D - 2 * p * q) ∧ 7 ≤ p) ∧
    (Odd (17 : ℤ) ∧ Odd (41 : ℤ) ∧ Odd (7 : ℤ) ∧ (∃ x y : ℤ, x * 17 + y * 41 = 1) ∧
      (2 : ℚ) ^ 3 - 1 = 7 ∧
      ((7 : ℚ) * (2 * 7 + 1) / (3 * 7 + 1) < (2 * 41 : ℚ) / 17 ∧
        (2 * 41 : ℚ) / 17 < 2 * 7 * (7 + 1) / (3 * 7 + 2))) :=
  ⟨fun _ _ hR => dyadic_test_iff_twoPow_le hR _,
    fun _ _ hR hRq => postTake_reciprocal_formula hR hRq,
    fun _ _ _ hR hRq hm => postTake_dyadicFailure_iff_band hR hRq hm,
    fun _ _ hq hm => band_width_general' hq hm,
    singleSkip_threshold,
    fun _ hq => singleSkip_band_width hq,
    fun _ _ hq h => singleSkip_band_two_thirds hq h,
    fun _ _ _ _ hq hR hqn => singleSkip_band_excludes_int hq _ _ hR hqn,
    fun _ _ _ hp hD hq hpo hDo hqo hb => singleSkip_seven_le hp hD hq hpo hDo hqo hb,
    singleSkip_band_witness⟩

#print axioms paper_two_thirds_band
end ErdosProblems.Erdos257.PaperCompleteR21
