import Erdos249257.GeometricCoprimality

/-! Paper-form restatements of the long #249 paper's coprime-pair lattice
environments:

* "Two lattice sums" — the half-open and strictly positive visible-pair sums,
  the identification of the removed boundary pair `(1,0)`, the gcd-layer
  normalisation `∑_{g≥1} ∑_{coprime} r^{g(a+b)} = (r/(1-r))²`, and the fact
  that this total equals `1` exactly at `r = 1/2`;
* "The classical coprime-pair Lambert identity" — the visible-point identity
  `∑ r^{a+b}/(1-r^{a+b}) = (r/(1-r))²`, its rationality at every rational
  parameter, its value `1` at `r = 1/2`, the contrasting plain-weight value
  `S - 1/2 ≠ S` there, and the recovery of `S` after the boundary pair is
  restored.

Throughout `S = ∑ φ(n)/2ⁿ` and the paper's `∑_{n≥1} φ(n) rⁿ` is written
`∑' n : ℕ, φ(n+1) · r^(n+1)`. -/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open GeometricCoprimality

/-! ### Shared index shift -/

/-- The paper's `∑_{n≥1} φ(n) rⁿ` and the tree's `∑_{n≥0} φ(n) rⁿ` agree,
because `φ(0) = 0`. -/
theorem tsum_totient_pow_shift {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, (Nat.totient n : ℝ) * r ^ n)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1) := by
  have hsum := summable_totient_mul_pow hr0 hr1
  rw [hsum.tsum_eq_zero_add]
  simp

/-! ### "Two lattice sums" -/

/-- **First lattice sum.**  For `0 ≤ r < 1`, the visible-pair sum over
`a ≥ 1, b ≥ 0` is `∑_{n≥1} φ(n) rⁿ`. -/
theorem coprimeLattice_halfOpen_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1) := by
  rw [tsum_coprime_pair_pow_eq_tsum_totient_mul_pow hr0 hr1,
    tsum_totient_pow_shift hr0 hr1]

/-- **Second lattice sum.**  For `0 ≤ r < 1`, the visible-pair sum over
`a, b ≥ 1` is `∑_{n≥1} φ(n) rⁿ - r`. -/
theorem coprimeLattice_positive_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)) - r := by
  rw [tsum_pos_coprime_pair_pow hr0 hr1, tsum_totient_pow_shift hr0 hr1]

/-- **The removed pair is `(1,0)`.**  A pair lies in the first index set but
not the second exactly when it is `(1,0)`. -/
theorem coprimeLattice_removed_pair (a b : ℕ) :
    ((0 < a ∧ Nat.Coprime a b) ∧ ¬ (0 < a ∧ 0 < b ∧ Nat.Coprime a b))
      ↔ (a = 1 ∧ b = 0) := by
  constructor
  · rintro ⟨⟨ha, hcop⟩, hno⟩
    have hb : b = 0 := by
      by_contra hb
      exact hno ⟨ha, Nat.pos_of_ne_zero hb, hcop⟩
    refine ⟨?_, hb⟩
    have hg : Nat.gcd a b = 1 := hcop
    rw [hb, Nat.gcd_zero_right] at hg
    exact hg
  · rintro ⟨ha, hb⟩
    subst ha
    subst hb
    refine ⟨⟨Nat.one_pos, ?_⟩, ?_⟩
    · show Nat.gcd 1 0 = 1
      simp
    · rintro ⟨-, h, -⟩
      exact absurd h (lt_irrefl 0)

/-- **The gcd-layer normalisation.**  Partitioning all strictly positive pairs
by their greatest common divisor gives
`∑_{g≥1} ∑_{a,b≥1, gcd(a,b)=1} r^{g(a+b)} = (r/(1-r))²`. -/
theorem coprimeLattice_gcd_layer_total {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = (r / (1 - r)) ^ 2 :=
  tsum_gcd_layer_pos_coprime_pow hr0 hr1

/-- **The total is `1` exactly when `r = 1/2`.** -/
theorem coprimeLattice_gcd_layer_total_eq_one_iff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0))
        = 1 ↔ r = 1 / 2 := by
  rw [coprimeLattice_gcd_layer_total hr0 hr1]
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hne : (1 : ℝ) - r ≠ 0 := ne_of_gt h1r
  constructor
  · intro h
    have hsq : r ^ 2 = (1 - r) ^ 2 := by
      field_simp at h
      linarith
    have hexp : (1 - r) ^ 2 = 1 - 2 * r + r ^ 2 := by ring
    linarith
  · intro h
    subst h
    norm_num

/-! ### "The classical coprime-pair Lambert identity" -/

/-- **The visible-point Lambert identity.**  For every `0 ≤ r < 1`,
`∑_{(a,b) coprime, a,b ≥ 1} r^{a+b}/(1-r^{a+b}) = (r/(1-r))²`. -/
theorem coprimeLattice_lambert_identity {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          r ^ (p.1 + p.2) / (1 - r ^ (p.1 + p.2)) else 0)
      = (r / (1 - r)) ^ 2 :=
  tsum_pos_coprime_lambert_eq_sq hr0 hr1

/-- **The Lambert-weighted sum is rational at every rational parameter.** -/
theorem coprimeLattice_lambert_rational (s : ℚ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ v : ℚ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (s : ℝ) ^ (p.1 + p.2) / (1 - (s : ℝ) ^ (p.1 + p.2)) else 0)
      = (v : ℝ) := by
  have hr0 : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs0
  have hr1 : (s : ℝ) < 1 := by exact_mod_cast hs1
  refine ⟨(s / (1 - s)) ^ 2, ?_⟩
  rw [coprimeLattice_lambert_identity hr0 hr1]
  push_cast
  ring

/-- **At `r = 1/2` the Lambert-weighted sum is `1`.** -/
theorem coprimeLattice_lambert_half_eq_one :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (1 / 2 : ℝ) ^ (p.1 + p.2) / (1 - (1 / 2 : ℝ) ^ (p.1 + p.2)) else 0) = 1 := by
  rw [coprimeLattice_lambert_identity (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)]
  norm_num

/-- **At `r = 1/2` the plain-weight sum over the same index set is `S - 1/2`,
which is not `S`.** -/
theorem coprimeLattice_plain_half_eq_series_sub_half :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (1 / 2 : ℝ) ^ (p.1 + p.2) else 0)
        = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 ∧
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
        ≠ ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  constructor
  · have h := tsum_pos_coprime_pair_pow (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    rw [h]
    have hterm : ∀ n : ℕ,
        (Nat.totient n : ℝ) * (1 / 2 : ℝ) ^ n = (Nat.totient n : ℝ) / 2 ^ n := by
      intro n
      rw [div_pow, one_pow]
      ring
    rw [tsum_congr hterm]
  · intro h
    linarith [h]

/-- **Restoring the boundary pair `(1,0)` recovers `S`.** -/
theorem coprimeLattice_halfOpen_half_eq_series :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then (1 / 2 : ℝ) ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  have h := tsum_coprime_pair_pow_eq_tsum_totient_mul_pow
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rw [h]
  refine tsum_congr fun n => ?_
  rw [div_pow, one_pow]
  ring

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tsum_totient_pow_shift
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_sum
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_positive_sum
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_removed_pair
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total_eq_one_iff
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_identity
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_rational
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_half_eq_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_plain_half_eq_series_sub_half
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_half_eq_series
#print axioms GeometricCoprimality.card_antidiagonal_filter_pos_coprime
