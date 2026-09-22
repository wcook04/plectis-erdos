import Erdos249257.CertificateKernel
import Erdos249257.MersenneLambertLadder
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Paper-form restatement of the long #249 paper's `prop:D7-inv`
("Lambert identities involving `S`").

With `L(f) = ∑_{n≥1} f(n)/(2^n - 1)`, `E = ∑_{N≥1} d(N)/2^N` and
`S = ∑_{n≥0} φ(n)/2^n`, the environment asserts

* `L(μ) = 1/2`, `L(φ) = 2`, `L(1) = E` and `L(φ*μ) = S`
  (`lambert_ladder_four_values`, with `primWeight_is_totient_conv_moebius`
  identifying the weight `A = φ*μ` and `totient_series_index_bridge'` the two
  indexings of `S`);
* `L(Id) = ∑_{m≥1} σ(m)/2^m` (`lambert_id_rung_eq_sigma_series`);
* that value is transcendental, by Nesterenko 1996, Cor. 2, p. 1320, which the
  paper cites and does not formalise (`transcendental_sigma_series`).

The last clause is the only one that leaves the tree: neither Nesterenko's
theorem nor the transcendence of `∑ σ(m)/2^m` is available in Mathlib or here,
so it is proved from the explicit hypothesis `NesterenkoTranscendenceP`, which
states Nesterenko's corollary in the single consequence the paper uses: at an
algebraic point `q` with `0 < |q| < 1`, the Ramanujan/Eisenstein value
`P(q) = 1 - 24 ∑_{m≥1} σ(m) q^m` is transcendental over `ℚ`.  Everything
between that hypothesis and the paper's clause is proved here. -/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257

/-! ### The four Lambert rungs -/

/-- **The four Lambert identities.**  `L(μ) = 1/2`, `L(φ) = 2`, `L(1) = E`
(the Erdős–Borwein constant in its divisor-count form) and `L(φ*μ) = S`. -/
theorem lambert_ladder_four_values :
    (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
        / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2) ∧
      (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 2) ∧
      (∑' k : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) - 1)
        = ∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (2 : ℝ) ^ (m + 1)) ∧
      (∑' d : ℕ+, ((MersenneLambertLadder.primWeight (d : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (d : ℕ) - 1)
        = ∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) :=
  ⟨tsum_moebius_div_two_pow_sub_one_eq_half,
    tsum_totient_div_two_pow_sub_one_eq_two,
    erdosBorwein_constant_lambert_identity,
    tsum_primWeight_div_two_pow_sub_one_eq_totient_series⟩

/-- The weight in the last identity is `A = φ * μ`: its divisor sum is `φ`. -/
theorem primWeight_is_totient_conv_moebius (n : ℕ) :
    ∑ e ∈ n.divisors, MersenneLambertLadder.primWeight e = (Nat.totient n : ℤ) :=
  MersenneLambertLadder.sum_divisors_primWeight n

/-- The index bridge between the two conventions for `S`. -/
theorem totient_series_index_bridge' :
    (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) :=
  tsum_totient_div_pow_two_eq_pnat_half_pow

/-! ### The `Id` rung: `L(Id) = ∑ σ(m)/2^m` -/

private theorem half_pow_mersenne_term (d : ℕ) (hd : 0 < d) :
    ((1 : ℝ) / 2) ^ d / (1 - ((1 : ℝ) / 2) ^ d) = 1 / ((2 : ℝ) ^ d - 1) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have h1 : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ one_lt_two hd.ne'
  have h2ne : (2 : ℝ) ^ d ≠ 0 := ne_of_gt h2
  have h1ne : (2 : ℝ) ^ d - 1 ≠ 0 := by linarith
  have hmid : (1 : ℝ) - 1 / (2 : ℝ) ^ d ≠ 0 := by
    have hEq : (1 : ℝ) - 1 / (2 : ℝ) ^ d = ((2 : ℝ) ^ d - 1) / (2 : ℝ) ^ d := by field_simp
    rw [hEq]
    exact div_ne_zero h1ne h2ne
  rw [div_pow, one_pow]
  field_simp

/-- **The `Id` rung.**  `L(Id) = ∑_{d≥1} d/(2^d - 1) = ∑_{m≥1} σ(m)/2^m`, by the
Lambert rearrangement `Id * ζ = σ`. -/
theorem lambert_id_rung_eq_sigma_series :
    (∑' d : ℕ+, ((d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1))
      = ∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ) := by
  have hw : ∀ d : ℕ, 0 < d → |((d : ℕ) : ℝ)| ≤ (d : ℝ) := by
    intro d _
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((d : ℕ) : ℝ))]
  have h := MersenneLambertLadder.tsum_lambert_linear_weight
    (fun d : ℕ => (d : ℝ)) hw (r := 1 / 2) (by norm_num) (by norm_num)
  calc (∑' d : ℕ+, ((d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1))
      = ∑' d : ℕ+, ((d : ℕ) : ℝ)
          * (((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ))) := by
        refine tsum_congr fun d => ?_
        rw [half_pow_mersenne_term (d : ℕ) d.pos, mul_one_div]
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, (e : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := h
    _ = ∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ) := by
        refine tsum_congr fun m => ?_
        rw [ArithmeticFunction.sigma_one_apply]
        push_cast
        rw [div_pow, one_pow, mul_one_div]

/-! ### The transcendence clause, from Nesterenko's corollary -/

/-- Ramanujan's `P(q) = 1 - 24 ∑_{m ≥ 1} σ(m) q^m`, the Eisenstein series that
Nesterenko's corollary is stated for. -/
noncomputable def ramanujanP (q : ℝ) : ℝ :=
  1 - 24 * ∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) * q ^ (m : ℕ)

/-- **Nesterenko 1996, Cor. 2, p. 1320** (cited by the paper, not formalised),
in the single consequence used here: at an algebraic real point `q` with
`0 < |q| < 1`, the value `P(q)` is transcendental over `ℚ`.  Nesterenko's
corollary in fact gives algebraic independence of `P(q), Q(q), R(q)`; this is
the weakest form the clause needs. -/
def NesterenkoTranscendenceP : Prop :=
  ∀ q : ℝ, IsAlgebraic ℚ q → 0 < |q| → |q| < 1 → Transcendental ℚ (ramanujanP q)

/-- **The transcendence clause of `prop:D7-inv`, modulo Nesterenko.**  Granting
Nesterenko's corollary in the form above, `∑_{m≥1} σ(m)/2^m` is transcendental
over `ℚ`. -/
theorem transcendental_sigma_series (hN : NesterenkoTranscendenceP) :
    Transcendental ℚ
      (∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ)) := by
  set T := ∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ)
    with hT
  have hP : ramanujanP (1 / 2) = 1 - 24 * T := by
    rw [ramanujanP, hT]
    congr 2
    refine tsum_congr fun m => ?_
    rw [div_pow, one_pow, mul_one_div]
  have hq : IsAlgebraic ℚ ((1 : ℝ) / 2) := by
    have h := isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (1 / 2 : ℚ)
    have hc : (algebraMap ℚ ℝ) (1 / 2 : ℚ) = (1 : ℝ) / 2 := by
      rw [eq_ratCast]; norm_num
    rwa [hc] at h
  have habs : |(1 : ℝ) / 2| = 1 / 2 := abs_of_pos (by norm_num)
  have hPt : Transcendental ℚ (1 - 24 * T) := by
    rw [← hP]
    exact hN (1 / 2) hq (by rw [habs]; norm_num) (by rw [habs]; norm_num)
  intro hTalg
  apply hPt
  obtain ⟨p, hp0, hpT⟩ := hTalg
  have hgdeg :
      (Polynomial.C (-1 / 24 : ℚ) * Polynomial.X + Polynomial.C (1 / 24 : ℚ)).natDegree = 1 :=
    Polynomial.natDegree_linear (by norm_num)
  have hglc :
      (Polynomial.C (-1 / 24 : ℚ) * Polynomial.X + Polynomial.C (1 / 24 : ℚ)).leadingCoeff
        = (-1 / 24 : ℚ) := Polynomial.leadingCoeff_linear (by norm_num)
  refine ⟨p.comp (Polynomial.C (-1 / 24 : ℚ) * Polynomial.X + Polynomial.C (1 / 24 : ℚ)),
    ?_, ?_⟩
  · intro hzero
    have hlc := Polynomial.leadingCoeff_comp
      (p := p) (q := Polynomial.C (-1 / 24 : ℚ) * Polynomial.X + Polynomial.C (1 / 24 : ℚ))
      (by rw [hgdeg]; norm_num)
    rw [hzero, Polynomial.leadingCoeff_zero, hglc] at hlc
    have hp1 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
    have hp2 : ((-1 / 24 : ℚ)) ^ p.natDegree ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_ne_zero hp1 hp2) hlc.symm
  · rw [Polynomial.aeval_comp]
    have hinner : Polynomial.aeval (1 - 24 * T)
        (Polynomial.C (-1 / 24 : ℚ) * Polynomial.X + Polynomial.C (1 / 24 : ℚ)) = T := by
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
      push_cast
      ring
    rw [hinner]
    exact hpT

/-- **`prop:D7-inv`, assembled.**  The Lambert rung `L(Id) = ∑ σ(m)/2^m`
together with the transcendence of that value, granting Nesterenko. -/
theorem lambert_id_rung_transcendental (hN : NesterenkoTranscendenceP) :
    (∑' d : ℕ+, ((d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1))
        = ∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ) ∧
      Transcendental ℚ
        (∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ)) :=
  ⟨lambert_id_rung_eq_sigma_series, transcendental_sigma_series hN⟩

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lambert_ladder_four_values
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.primWeight_is_totient_conv_moebius
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_series_index_bridge'
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lambert_id_rung_eq_sigma_series
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.transcendental_sigma_series
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lambert_id_rung_transcendental
