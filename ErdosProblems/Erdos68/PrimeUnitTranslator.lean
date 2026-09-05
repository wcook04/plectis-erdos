import ErdosProblems.Erdos68.ChannelIntegralCongruence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Prime unit translator for Erdős problem 68

For a prime `p`, the coefficient pair `(p,-1)` on the indices `(p-1,p)` has
zero factorial moment and annihilates every channel except the `p`-channel.
At that channel its numerator is exactly `p!-1`; consequently its normalized
infinite residual is `1`.  Appending an integer multiple of this pair therefore
translates any finite-support residual by the same integer without changing
the lower channels or the factorial moment.

The module also classifies every finite-support residual modulo integers as
its factorial moment times the factorial-gap tail.  A Cramer construction on
an explicit factorial grid supplies, beyond any prescribed support threshold,
integer coefficient vectors with zero channels through a chosen cutoff and
nonzero factorial moment.  Appending a prime translator reduces their
residual to absolute value at most `1/2`.

The last reduction is not an irrationality argument by itself: the reduced
residual may be zero.  The strict version assumes that the original residual
is not an integer, and no theorem here proves that assumption for the Cramer
vectors.  There is also no coefficient-size estimate, no nonzero lower bound
for the reduced residual, and no irrationality theorem for the factorial-gap
series.
-/

namespace Erdos68

/-- Coefficients `(p,-1)` of the prime-pair translator. -/
def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ :=
  ![(p : ℤ), -1]

/-- Support indices `(p-1,p)` of the prime-pair translator. -/
def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ :=
  ![p - 1, p]

/-- Beyond the support radius every channel numerator is exactly the
factorial moment. -/
theorem channelNumerator_eq_factorialMoment_of_all_lt
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {d : ℕ}
    (hlt : ∀ j, index j < d) :
    channelNumerator coeff index d = factorialMoment coeff index := by
  unfold channelNumerator factorialMoment
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.div_eq_of_lt (hlt j)]
  simp

/-- The prime-pair translator has zero factorial moment. -/
theorem primeTranslator_moment_zero
    {p : ℕ} (hp : 0 < p) :
    factorialMoment (primeTranslatorCoeff p) (primeTranslatorIndex p) = 0 := by
  rw [show p = (p - 1) + 1 by omega]
  simp [factorialMoment, primeTranslatorCoeff, primeTranslatorIndex,
    Fin.sum_univ_two, Nat.factorial_succ]

/-- Every channel strictly beyond `p` vanishes because the translator has
zero moment and both support indices lie below the channel index. -/
theorem primeTranslator_channel_zero_of_p_lt
    {p d : ℕ} (hp : 0 < p) (hpd : p < d) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  rw [channelNumerator_eq_factorialMoment_of_all_lt]
  · exact primeTranslator_moment_zero hp
  · intro j
    fin_cases j <;> simp [primeTranslatorIndex] <;> omega

/-- A prime does not cross a `d`-quotient wall at its final predecessor when
`2 ≤ d < p`. -/
theorem prime_pred_div_eq
    {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    (p - 1) / d = p / d := by
  have hdpos : 0 < d := by omega
  have hndvd : ¬d ∣ p := by
    rw [Nat.dvd_prime_two_le hp hd2]
    exact ne_of_lt hdp
  have hne : (p / d) * d ≠ p := by
    intro h
    apply hndvd
    exact ⟨p / d, by simpa [mul_comm] using h.symm⟩
  have hlo : (p / d) * d ≤ p - 1 := by
    have := Nat.div_mul_le_self p d
    omega
  have hhi : p - 1 < (p / d + 1) * d := by
    have hp_hi : p < (p / d + 1) * d := by
      rw [← Nat.div_lt_iff_lt_mul hdpos]
      exact Nat.lt_succ_self _
    omega
  apply Nat.div_eq_of_lt_le
  · simpa [mul_comm] using hlo
  · simpa [mul_comm] using hhi

/-- Below a prime, the channel coefficient at `p` is `p` times the
coefficient at `p-1`. -/
theorem channelCoefficient_prime_eq_mul_pred
    {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    p.factorial / d.factorial ^ (p / d) =
      p * ((p - 1).factorial / d.factorial ^ ((p - 1) / d)) := by
  have hq := prime_pred_div_eq hp hd2 hdp
  have hdpos : 0 < d := by omega
  have hp_hi : p < (p / d + 1) * d := by
    rw [← Nat.div_lt_iff_lt_mul hdpos]
    exact Nat.lt_succ_self _
  have hbandp := channel_coefficient_band
    (d := d) (i := p) (k := p / d) (Nat.div_mul_le_self p d) hp_hi
  have hpred_hi : p - 1 < ((p - 1) / d + 1) * d := by
    rw [← Nat.div_lt_iff_lt_mul hdpos]
    exact Nat.lt_succ_self _
  have hbandpred := channel_coefficient_band
    (d := d) (i := p - 1) (k := (p - 1) / d)
    (Nat.div_mul_le_self (p - 1) d) hpred_hi
  have hpstep : p.factorial = p * (p - 1).factorial := by
    calc
      p.factorial = ((p - 1) + 1).factorial := by congr 1; omega
      _ = ((p - 1) + 1) * (p - 1).factorial := Nat.factorial_succ _
      _ = p * (p - 1).factorial := by congr 1; omega
  have hmul :
      d.factorial ^ (p / d) *
          (p.factorial / d.factorial ^ (p / d)) =
        d.factorial ^ (p / d) *
          (p * ((p - 1).factorial / d.factorial ^ ((p - 1) / d))) := by
    calc
      d.factorial ^ (p / d) *
          (p.factorial / d.factorial ^ (p / d)) = p.factorial := hbandp
      _ = p * (p - 1).factorial := hpstep
      _ = p * (d.factorial ^ ((p - 1) / d) *
          ((p - 1).factorial / d.factorial ^ ((p - 1) / d))) := by rw [hbandpred]
      _ = d.factorial ^ (p / d) *
          (p * ((p - 1).factorial / d.factorial ^ ((p - 1) / d))) := by
            rw [hq]
            ring
  exact Nat.mul_left_cancel (by positivity) hmul

/-- Every channel below `p` annihilates the prime translator. -/
theorem primeTranslator_channel_zero_of_lt_p
    {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  rw [show p = (p - 1) + 1 by omega]
  simp only [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcoeff := channelCoefficient_prime_eq_mul_pred hp hd2 hdp
  rw [show p = (p - 1) + 1 by omega] at hcoeff
  norm_num at hcoeff ⊢
  rw [← sub_eq_add_neg, sub_eq_zero]
  exact_mod_cast hcoeff.symm

/-- A prime translator annihilates every requested channel below its prime. -/
theorem primeTranslator_channels_zero
    {D p : ℕ} (hp : p.Prime) (hDp : D < p) :
    ∀ d ∈ Finset.Icc 2 D,
      channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  intro d hd
  exact primeTranslator_channel_zero_of_lt_p hp (Finset.mem_Icc.mp hd).1
    ((Finset.mem_Icc.mp hd).2.trans_lt hDp)

/-- At the prime itself, the sole surviving channel numerator is exactly its
normalizing modulus `p! - 1`. -/
theorem primeTranslator_channel_at_prime
    {p : ℕ} (hp : p.Prime) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p =
      (p.factorial : ℤ) - 1 := by
  have hp0 : 0 < p := hp.pos
  have hpredlt : p - 1 < p := Nat.sub_lt hp0 (by decide)
  have hpred : (p - 1) / p = 0 := Nat.div_eq_of_lt hpredlt
  have hself : p / p = 1 := Nat.div_self hp0
  have hfac : p.factorial = p * (p - 1).factorial := by
    calc
      p.factorial = ((p - 1) + 1).factorial := by congr 1; omega
      _ = ((p - 1) + 1) * (p - 1).factorial := Nat.factorial_succ _
      _ = p * (p - 1).factorial := by congr 1; omega
  simp only [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hpred, hself, pow_zero, pow_one, Nat.div_one,
    Nat.div_self (Nat.factorial_pos p)]
  norm_num
  rw [hfac]
  norm_cast

/-- The real contribution of one channel to the tail beyond `D`. -/
noncomputable def channelResidualTerm
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℝ :=
  if D < d then
    (channelNumerator coeff index d : ℝ) /
      (((d.factorial : ℤ) - 1 : ℤ) : ℝ)
  else 0

/-- Infinite real channel residual beyond the cutoff `D`. -/
noncomputable def channelResidual
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) : ℝ :=
  ∑' d : ℕ, channelResidualTerm D coeff index d

/-- Reciprocal factorial gaps form a summable real series. -/
theorem summable_one_div_factorial_sub_one :
    Summable (fun d : ℕ =>
      (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)) := by
  apply summable_of_ratio_norm_eventually_le
    (r := (1 : ℝ) / 2) (by norm_num)
  filter_upwards [Filter.eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
  have hfac : 1 < n.factorial :=
    Nat.one_lt_factorial.mpr hn
  have hnextfac : 1 < (n + 1).factorial :=
    Nat.one_lt_factorial.mpr (by omega)
  have hden :
      (0 : ℝ) < ((((n.factorial : ℤ) - 1 : ℤ)) : ℝ) := by
    exact_mod_cast (show (0 : ℤ) < (n.factorial : ℤ) - 1 by omega)
  have hnextden :
      (0 : ℝ) < (((((n + 1).factorial : ℤ) - 1 : ℤ)) : ℝ) := by
    exact_mod_cast
      (show (0 : ℤ) < ((n + 1).factorial : ℤ) - 1 by omega)
  have hgap :
      2 * ((((n.factorial : ℤ) - 1 : ℤ)) : ℝ) ≤
        (((((n + 1).factorial : ℤ) - 1 : ℤ)) : ℝ) := by
    have hstep : (n + 1).factorial = (n + 1) * n.factorial :=
      Nat.factorial_succ n
    exact_mod_cast
      (show (2 : ℤ) * ((n.factorial : ℤ) - 1) ≤
          (((n + 1).factorial : ℤ) - 1) by
        nlinarith)
  simp only [Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hden),
    abs_of_pos (one_div_pos.mpr hnextden)]
  calc
    (1 : ℝ) /
          (((((n + 1).factorial : ℤ) - 1 : ℤ)) : ℝ) ≤
        1 / (2 * ((((n.factorial : ℤ) - 1 : ℤ)) : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hgap
    _ = ((1 : ℝ) / 2) *
          (1 / ((((n.factorial : ℤ) - 1 : ℤ)) : ℝ)) := by
      field_simp [hden.ne']

/-- Every finite-support channel residual is summable. Beyond the largest
support index, its numerator is the fixed factorial moment and the
denominator grows factorially. -/
theorem summable_channelResidualTerm
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) :
    Summable (fun d : ℕ => channelResidualTerm D coeff index d) := by
  classical
  have hbase :=
    summable_one_div_factorial_sub_one.mul_left
      ((factorialMoment coeff index : ℤ) : ℝ)
  refine hbase.congr_atTop ?_
  filter_upwards [
    Filter.eventually_atTop.2
      ⟨max D (Finset.univ.sup index) + 1, fun d hd => hd⟩
  ] with d hd
  have hDd : D < d := by omega
  have hlt : ∀ j, index j < d := by
    intro j
    have hj : index j ≤ Finset.univ.sup index :=
      Finset.le_sup (f := index) (Finset.mem_univ j)
    omega
  rw [channelResidualTerm, if_pos hDd,
    channelNumerator_eq_factorialMoment_of_all_lt coeff index hlt]
  ring

/-- One summand of the universal factorial-gap tail beyond `D`. -/
noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0

/-- The universal factorial-gap tail beyond `D`. -/
noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d

/-- The factorial-gap tail is summable at every cutoff. -/
theorem summable_factorialGapTailTerm (D : ℕ) :
    Summable (factorialGapTailTerm D) := by
  have h :=
    summable_one_div_factorial_sub_one.indicator
      {d : ℕ | D < d}
  refine h.congr ?_
  intro d
  by_cases hd : D < d <;>
    simp [factorialGapTailTerm, Set.indicator, hd]

/-- Reindex the tail by its distance beyond the cutoff. -/
theorem factorialGapTail_eq_shifted_tsum (D : ℕ) :
    factorialGapTail D =
      ∑' k : ℕ,
        (1 : ℝ) /
          ((((D + 1 + k).factorial : ℤ) - 1 : ℤ) : ℝ) := by
  let e : ℕ ≃ {d : ℕ // D < d} :=
    { toFun := fun k => ⟨D + 1 + k, by omega⟩
      invFun := fun d => d.1 - (D + 1)
      left_inv := by
        intro k
        exact Nat.add_sub_cancel_left (D + 1) k
      right_inv := by
        intro d
        apply Subtype.ext
        exact Nat.add_sub_of_le (by omega) }
  calc
    factorialGapTail D =
        ∑' d : ℕ,
          Set.indicator {d : ℕ | D < d}
            (fun d : ℕ =>
              (1 : ℝ) /
                (((d.factorial : ℤ) - 1 : ℤ) : ℝ)) d := by
      unfold factorialGapTail
      apply tsum_congr
      intro d
      by_cases hd : D < d <;>
        simp [factorialGapTailTerm, Set.indicator, hd]
    _ = ∑' d : {d : ℕ // D < d},
          (1 : ℝ) /
            (((d.1.factorial : ℤ) - 1 : ℤ) : ℝ) := by
      simpa using
        (tsum_subtype {d : ℕ | D < d}
          (fun d : ℕ =>
            (1 : ℝ) /
              (((d.factorial : ℤ) - 1 : ℤ) : ℝ))).symm
    _ = ∑' k : ℕ,
          (1 : ℝ) /
            ((((D + 1 + k).factorial : ℤ) - 1 : ℤ) : ℝ) := by
      simpa [e] using
        (e.tsum_eq (fun d : {d : ℕ // D < d} =>
          (1 : ℝ) /
            (((d.1.factorial : ℤ) - 1 : ℤ) : ℝ))).symm

/-- The reciprocal-factorial difference beginning at `D` telescopes
exactly to `1 / D!`. -/
theorem hasSum_factorial_telescope (D : ℕ) :
    HasSum
      (fun k : ℕ =>
        (1 : ℝ) / ((D + k).factorial : ℝ) -
          1 / ((D + k + 1).factorial : ℝ))
      (1 / (D.factorial : ℝ)) := by
  let f : ℕ → ℝ := fun k =>
    (1 : ℝ) / ((D + k).factorial : ℝ)
  have hall : Summable (fun n : ℕ =>
      (1 : ℝ) / (n.factorial : ℝ)) := by
    simpa using Real.summable_pow_div_factorial 1
  have hf : Summable f := by
    have hshift :=
      (summable_nat_add_iff D).2 hall
    simpa [f, Nat.add_comm] using hshift
  have hsucc : Summable (fun k : ℕ => f (k + 1)) :=
    (summable_nat_add_iff 1).2 hf
  have hdiff : Summable (fun k : ℕ => f k - f (k + 1)) :=
    hf.sub hsucc
  have hf_zero :
      Filter.Tendsto f Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun k => by
        simp [f])
    · filter_upwards [Filter.eventually_atTop.2
        ⟨1, fun k hk => hk⟩] with k hk
      have hnat : k ≤ (D + k).factorial := by
        calc
          k ≤ D + k := Nat.le_add_left k D
          _ ≤ (D + k).factorial := Nat.self_le_factorial _
      have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
      have hfacreal : (0 : ℝ) < (D + k).factorial := by positivity
      exact one_div_le_one_div_of_le hkreal (by exact_mod_cast hnat)
    · simpa using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply (hdiff.hasSum_iff_tendsto_nat).2
  have htend :
      Filter.Tendsto (fun n : ℕ => f 0 - f n) Filter.atTop
        (nhds (f 0 - 0)) :=
    hf_zero.const_sub (f 0)
  convert htend using 1
  · funext n
    exact Finset.sum_range_sub' f n
  · simp [f]

/-- Each factorial-gap reciprocal from index three onward is strictly
smaller than the adjacent telescoping reciprocal-factorial difference. -/
theorem one_div_factorial_sub_one_lt_telescope
    {m : ℕ} (hm : 3 ≤ m) :
    (1 : ℝ) / (((m.factorial : ℤ) - 1 : ℤ) : ℝ) <
      1 / ((m - 1).factorial : ℝ) -
        1 / (m.factorial : ℝ) := by
  have hfac : m.factorial = m * (m - 1).factorial := by
    calc
      m.factorial = ((m - 1) + 1).factorial := by
        congr 1
        omega
      _ = ((m - 1) + 1) * (m - 1).factorial :=
        Nat.factorial_succ _
      _ = m * (m - 1).factorial := by
        congr 1
        omega
  have hprednat : 2 ≤ (m - 1).factorial := by
    calc
      2 ≤ m - 1 := by omega
      _ ≤ (m - 1).factorial := Nat.self_le_factorial _
  have hden :
      (0 : ℝ) <
        (((m.factorial : ℤ) - 1 : ℤ) : ℝ) := by
    exact_mod_cast
      (show (0 : ℤ) < (m.factorial : ℤ) - 1 by
        have : 1 < m.factorial := Nat.one_lt_factorial.mpr (by omega)
        omega)
  have hmreal : (0 : ℝ) < m := by positivity
  have hpredreal : (0 : ℝ) < ((m - 1).factorial : ℝ) := by
    positivity
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
  have hfacreal :
      (m.factorial : ℝ) =
        (m : ℝ) * ((m - 1).factorial : ℝ) := by
    exact_mod_cast hfac
  rw [hfacreal]
  have hprod :
      (0 : ℝ) < (m : ℝ) * ((m - 1).factorial : ℝ) :=
    mul_pos hmreal hpredreal
  have hrewrite :
      1 / ((m - 1).factorial : ℝ) -
          1 / ((m : ℝ) * ((m - 1).factorial : ℝ)) =
        ((m : ℝ) - 1) /
          ((m : ℝ) * ((m - 1).factorial : ℝ)) := by
    field_simp
  have hpredbound :
      (2 : ℝ) ≤ ((m - 1).factorial : ℝ) := by
    exact_mod_cast hprednat
  have hmbound : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hdenprod :
      (0 : ℝ) <
        (m : ℝ) * ((m - 1).factorial : ℝ) - 1 := by
    nlinarith
  rw [hrewrite, div_lt_div_iff₀ hdenprod hprod]
  nlinarith

/-- Beyond every cutoff `D ≥ 2`, the factorial-gap tail is strictly less
than `1 / D!`. -/
theorem factorialGapTail_lt_one_div_factorial
    {D : ℕ} (hD : 2 ≤ D) :
    factorialGapTail D < (1 : ℝ) / (D.factorial : ℝ) := by
  let source : ℕ → ℝ := fun k =>
    (1 : ℝ) /
      ((((D + 1 + k).factorial : ℤ) - 1 : ℤ) : ℝ)
  let majorant : ℕ → ℝ := fun k =>
    (1 : ℝ) / ((D + k).factorial : ℝ) -
      1 / ((D + k + 1).factorial : ℝ)
  have hsource_nonneg : ∀ k, 0 ≤ source k := by
    intro k
    have hden :
        (0 : ℝ) <
          ((((D + 1 + k).factorial : ℤ) - 1 : ℤ) : ℝ) := by
      exact_mod_cast
        (show (0 : ℤ) <
            ((D + 1 + k).factorial : ℤ) - 1 by
          have : 1 < (D + 1 + k).factorial :=
            Nat.one_lt_factorial.mpr (by omega)
          omega)
    simp only [source]
    exact le_of_lt (one_div_pos.mpr hden)
  have hle : ∀ k, source k ≤ majorant k := by
    intro k
    have hterm :=
      one_div_factorial_sub_one_lt_telescope
        (m := D + 1 + k) (by omega)
    simp only [source, majorant]
    have hpred : D + 1 + k - 1 = D + k := by omega
    rw [hpred] at hterm
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hterm.le
  have hstrict : source 0 < majorant 0 := by
    have hterm :=
      one_div_factorial_sub_one_lt_telescope
        (m := D + 1) (by omega)
    simpa [source, majorant] using hterm
  have hmajorant : Summable majorant :=
    (hasSum_factorial_telescope D).summable
  have hsum :=
    Summable.tsum_lt_tsum_of_nonneg (i := 0)
      hsource_nonneg hle hstrict hmajorant
  rw [factorialGapTail_eq_shifted_tsum]
  simpa [source, majorant] using
    hsum.trans_eq (hasSum_factorial_telescope D).tsum_eq

/-- Every actual factorial-gap tail beginning at a cutoff of at least two
is strictly positive. -/
theorem factorialGapTail_pos {D : ℕ} (hD : 2 ≤ D) :
    0 < factorialGapTail D := by
  have hshift :
      Summable (fun k : ℕ =>
        (1 : ℝ) /
          ((((D + 1 + k).factorial : ℤ) - 1 : ℤ) : ℝ)) := by
    have h :=
      (summable_nat_add_iff (D + 1)).2
        summable_one_div_factorial_sub_one
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  rw [factorialGapTail_eq_shifted_tsum]
  have hnonneg : ∀ k : ℕ,
      0 ≤
        (1 : ℝ) /
          ((((D + 1 + k).factorial : ℤ) - 1 : ℤ) : ℝ) := by
    intro k
    have hden :
        (0 : ℝ) <
          ((((D + 1 + k).factorial : ℤ) - 1 : ℤ) : ℝ) := by
      exact_mod_cast
        (show (0 : ℤ) <
            ((D + 1 + k).factorial : ℤ) - 1 by
          have : 1 < (D + 1 + k).factorial :=
            Nat.one_lt_factorial.mpr (by omega)
          omega)
    exact le_of_lt (one_div_pos.mpr hden)
  have hzero :
      0 <
        (1 : ℝ) /
          ((((D + 1 + 0).factorial : ℤ) - 1 : ℤ) : ℝ) := by
    have hden :
        (0 : ℝ) <
          ((((D + 1).factorial : ℤ) - 1 : ℤ) : ℝ) := by
      exact_mod_cast
        (show (0 : ℤ) < ((D + 1).factorial : ℤ) - 1 by
          have : 1 < (D + 1).factorial :=
            Nat.one_lt_factorial.mpr (by omega)
          omega)
    simpa using one_div_pos.mpr hden
  exact hshift.tsum_pos hnonneg 0 hzero

/-- Canonical integral quotient in the affine channel congruence. -/
noncomputable def channelCorrectionQuotient
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  if hd : 2 ≤ d then
    Classical.choose (exists_channelCorrection coeff index hd)
  else 0

/-- The chosen correction quotient realizes the exact affine channel
congruence. -/
theorem channelCorrectionQuotient_spec
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {d : ℕ} (hd : 2 ≤ d) :
    channelNumerator coeff index d =
      factorialMoment coeff index +
        ((d.factorial : ℤ) - 1) *
          channelCorrectionQuotient coeff index d := by
  rw [channelCorrectionQuotient, dif_pos hd]
  exact Classical.choose_spec (exists_channelCorrection coeff index hd)

/-- Only the channels between the cutoff and the largest support index can
contribute a nonzero integral correction. -/
noncomputable def finiteChannelCorrection
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℝ :=
  if d ∈ Finset.Ioc D (Finset.univ.sup index) then
    (channelCorrectionQuotient coeff index d : ℝ)
  else 0

/-- The correction series is finite. -/
theorem summable_finiteChannelCorrection
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) :
    Summable (finiteChannelCorrection D coeff index) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Ioc D (Finset.univ.sup index))
  intro d hd
  simp [finiteChannelCorrection, hd]

/-- Pointwise residual classification: each normalized channel is its
factorial moment times the universal factorial-gap term plus a correction
which is integral and supported on a finite interval. -/
theorem channelResidualTerm_eq_moment_mul_tail_add_correction
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ)
    (hD : 1 ≤ D) (d : ℕ) :
    channelResidualTerm D coeff index d =
      (factorialMoment coeff index : ℝ) * factorialGapTailTerm D d +
        finiteChannelCorrection D coeff index d := by
  by_cases hDd : D < d
  · have hd2 : 2 ≤ d := by omega
    by_cases hdR : d ≤ Finset.univ.sup index
    · have hdenInt : (d.factorial : ℤ) - 1 ≠ 0 := by
        have hfac : 1 < d.factorial := Nat.one_lt_factorial.mpr hd2
        omega
      have hdenReal :
          ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) ≠ 0 := by
        exact_mod_cast hdenInt
      have hfacReal : (1 : ℝ) < (d.factorial : ℝ) := by
        exact_mod_cast Nat.one_lt_factorial.mpr hd2
      have hdenReal' : -1 + (d.factorial : ℝ) ≠ 0 := by
        linarith
      rw [channelResidualTerm, if_pos hDd,
        factorialGapTailTerm, if_pos hDd,
        finiteChannelCorrection, if_pos (Finset.mem_Ioc.mpr ⟨hDd, hdR⟩)]
      have hspec :=
        channelCorrectionQuotient_spec coeff index hd2
      have hspecReal :
          (channelNumerator coeff index d : ℝ) =
            (factorialMoment coeff index : ℝ) +
              ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) *
                (channelCorrectionQuotient coeff index d : ℝ) := by
        exact_mod_cast hspec
      rw [hspecReal]
      field_simp [hdenReal, hdenReal']
    · have hlt : ∀ j, index j < d := by
        intro j
        have hj : index j ≤ Finset.univ.sup index :=
          Finset.le_sup (f := index) (Finset.mem_univ j)
        omega
      rw [channelResidualTerm, if_pos hDd,
        factorialGapTailTerm, if_pos hDd,
        finiteChannelCorrection,
        if_neg (by
          rw [Finset.mem_Ioc]
          omega),
        channelNumerator_eq_factorialMoment_of_all_lt coeff index hlt]
      ring
  · simp [channelResidualTerm, factorialGapTailTerm,
      finiteChannelCorrection, hDd]

/-- For a finite coefficient family, the residual differs from its factorial
moment times the factorial-gap tail by an integer. -/
theorem exists_channelResidual_eq_moment_mul_factorialGapTail_add_int
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) (hD : 1 ≤ D) :
    ∃ K : ℤ,
      channelResidual D coeff index =
        (factorialMoment coeff index : ℝ) * factorialGapTail D +
          (K : ℝ) := by
  let s := Finset.Ioc D (Finset.univ.sup index)
  let K : ℤ := ∑ d ∈ s, channelCorrectionQuotient coeff index d
  refine ⟨K, ?_⟩
  rw [channelResidual]
  calc
    (∑' d : ℕ, channelResidualTerm D coeff index d) =
        ∑' d : ℕ,
          ((factorialMoment coeff index : ℝ) * factorialGapTailTerm D d +
            finiteChannelCorrection D coeff index d) := by
      apply tsum_congr
      intro d
      exact channelResidualTerm_eq_moment_mul_tail_add_correction
        D coeff index hD d
    _ = (∑' d : ℕ,
          (factorialMoment coeff index : ℝ) * factorialGapTailTerm D d) +
        ∑' d : ℕ, finiteChannelCorrection D coeff index d :=
      ((summable_factorialGapTailTerm D).mul_left
          (factorialMoment coeff index : ℝ)).tsum_add
        (summable_finiteChannelCorrection D coeff index)
    _ = (factorialMoment coeff index : ℝ) * factorialGapTail D +
          (K : ℝ) := by
      rw [(summable_factorialGapTailTerm D).tsum_mul_left,
        factorialGapTail]
      have hfinite :
          (∑' d : ℕ, finiteChannelCorrection D coeff index d) =
            ∑ d ∈ s, (channelCorrectionQuotient coeff index d : ℝ) := by
        rw [tsum_eq_sum (s := s)]
        · apply Finset.sum_congr rfl
          intro d hd
          rw [finiteChannelCorrection,
            if_pos (by simpa [s] using hd)]
        · intro d hd
          simp [finiteChannelCorrection, s, hd]
      rw [hfinite]
      simp [K, s]

/-- The original Erdős #68 series, expressed through the universal
factorial-gap tail beginning after `1`. -/
noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1

/-- Split the original series into its finite prefix through `D` and the
remaining universal tail. -/
theorem factorialGapSeries_eq_sum_add_tail
    {D : ℕ} (hD : 2 ≤ D) :
    factorialGapSeries =
      (∑ d ∈ Finset.Icc 2 D,
        (1 : ℝ) /
          ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))) +
        factorialGapTail D := by
  let finitePart : ℕ → ℝ := fun d =>
    if d ∈ Finset.Icc 2 D then
      (1 : ℝ) /
        ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
    else 0
  have hfinite : Summable finitePart := by
    apply summable_of_ne_finset_zero (s := Finset.Icc 2 D)
    intro d hd
    simp only [finitePart, if_neg hd]
  calc
    factorialGapSeries =
        ∑' d : ℕ, (finitePart d + factorialGapTailTerm D d) := by
      unfold factorialGapSeries factorialGapTail
      apply tsum_congr
      intro d
      by_cases hd2 : 2 ≤ d
      · by_cases hdD : d ≤ D
        · have hdmem : d ∈ Finset.Icc 2 D := by
            simp [hd2, hdD]
          have hnot : ¬D < d := by omega
          simp only [factorialGapTailTerm, finitePart,
            if_pos (show 1 < d by omega), if_pos hdmem, if_neg hnot,
            add_zero]
        · have hdmem : d ∉ Finset.Icc 2 D := by
            simp [hd2, hdD]
          have htail : D < d := by omega
          simp only [factorialGapTailTerm, finitePart,
            if_pos (show 1 < d by omega), if_neg hdmem, if_pos htail,
            zero_add]
      · have hdmem : d ∉ Finset.Icc 2 D := by
          simp [hd2]
        have hnot : ¬D < d := by omega
        have hnot1 : ¬1 < d := by omega
        simp only [factorialGapTailTerm, finitePart, if_neg hnot1,
          if_neg hdmem, if_neg hnot, zero_add]
    _ = (∑' d : ℕ, finitePart d) + factorialGapTail D := by
      rw [hfinite.tsum_add (summable_factorialGapTailTerm D),
        factorialGapTail]
    _ = (∑ d ∈ Finset.Icc 2 D,
          (1 : ℝ) /
            ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))) +
          factorialGapTail D := by
      congr 1
      rw [tsum_eq_sum (s := Finset.Icc 2 D)]
      · apply Finset.sum_congr rfl
        intro d hd
        simp only [finitePart, if_pos hd]
      · intro d hd
        simp only [finitePart, if_neg hd]

/-- If every channel from `2` through `D` vanishes, changing the residual
cutoff from `1` to `D` removes only zero summands. -/
theorem channelResidual_eq_cutoff_one_of_channels_zero
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ)
    (hD : 2 ≤ D)
    (hchannels : ∀ d ∈ Finset.Icc 2 D,
      channelNumerator coeff index d = 0) :
    channelResidual D coeff index =
      channelResidual 1 coeff index := by
  unfold channelResidual
  apply tsum_congr
  intro d
  by_cases hDd : D < d
  · have h1d : 1 < d := by omega
    simp [channelResidualTerm, hDd, h1d]
  · by_cases h1d : 1 < d
    · have hdmem : d ∈ Finset.Icc 2 D := by
        rw [Finset.mem_Icc]
        omega
      simp [channelResidualTerm, hDd, h1d, hchannels d hdmem]
    · simp [channelResidualTerm, hDd, h1d]

/-- For every finite-support channel-kernel vector, the residual modulo
integers is exactly its factorial moment times the original Erdős #68
series. -/
theorem exists_channelResidual_eq_moment_mul_factorialGapSeries_add_int
    {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ)
    (hD : 2 ≤ D)
    (hchannels : ∀ d ∈ Finset.Icc 2 D,
      channelNumerator coeff index d = 0) :
    ∃ K : ℤ,
      channelResidual D coeff index =
        (factorialMoment coeff index : ℝ) * factorialGapSeries +
          (K : ℝ) := by
  obtain ⟨K, hK⟩ :=
    exists_channelResidual_eq_moment_mul_factorialGapTail_add_int
      1 coeff index (by omega)
  refine ⟨K, ?_⟩
  rw [channelResidual_eq_cutoff_one_of_channels_zero
    D coeff index hD hchannels]
  simpa [factorialGapSeries] using hK

/-- Adding coefficient vectors adds every channel numerator. -/
theorem channelNumerator_add_coeff
    {ι : Type*} [Fintype ι]
    (left right : ι → ℤ) (index : ι → ℕ) (d : ℕ) :
    channelNumerator (fun j => left j + right j) index d =
      channelNumerator left index d + channelNumerator right index d := by
  unfold channelNumerator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Adding coefficient vectors adds each real residual summand. -/
theorem channelResidualTerm_add_coeff
    {ι : Type*} [Fintype ι]
    (D : ℕ) (left right : ι → ℤ) (index : ι → ℕ) (d : ℕ) :
    channelResidualTerm D (fun j => left j + right j) index d =
      channelResidualTerm D left index d +
        channelResidualTerm D right index d := by
  by_cases hDd : D < d
  · rw [channelResidualTerm, if_pos hDd,
      channelResidualTerm, if_pos hDd,
      channelResidualTerm, if_pos hDd,
      channelNumerator_add_coeff]
    push_cast
    ring
  · simp [channelResidualTerm, hDd]

/-- The full infinite residual is additive on every finite-support
coefficient space. -/
theorem channelResidual_add_coeff
    {ι : Type*} [Fintype ι]
    (D : ℕ) (left right : ι → ℤ) (index : ι → ℕ) :
    channelResidual D (fun j => left j + right j) index =
      channelResidual D left index + channelResidual D right index := by
  unfold channelResidual
  calc
    (∑' d : ℕ, channelResidualTerm D (fun j => left j + right j) index d) =
        ∑' d : ℕ,
          (channelResidualTerm D left index d +
            channelResidualTerm D right index d) := by
      apply tsum_congr
      intro d
      exact channelResidualTerm_add_coeff D left right index d
    _ = (∑' d : ℕ, channelResidualTerm D left index d) +
        ∑' d : ℕ, channelResidualTerm D right index d :=
      (summable_channelResidualTerm D left index).tsum_add
        (summable_channelResidualTerm D right index)

/-- The prime-pair translator is an exact unit direction for the full infinite
channel residual: every tail channel vanishes except `p`, where numerator and
normalizing modulus coincide. -/
theorem primeTranslator_channelResidual_eq_one
    {D p : ℕ} (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by
  rw [channelResidual, tsum_eq_single p]
  · rw [channelResidualTerm, if_pos hDp,
      primeTranslator_channel_at_prime hp]
    have hfacReal : (1 : ℝ) < (p.factorial : ℝ) := by
      exact_mod_cast Nat.one_lt_factorial.mpr hp.one_lt
    have hgapReal : (p.factorial : ℝ) - 1 ≠ 0 := by
      linarith
    push_cast
    exact div_self hgapReal
  · intro d hdp
    by_cases hDd : D < d
    · have hd2 : 2 ≤ d := by omega
      by_cases hlt : d < p
      · simp [channelResidualTerm, hDd,
          primeTranslator_channel_zero_of_lt_p hp hd2 hlt]
      · have hgt : p < d := by omega
        simp [channelResidualTerm, hDd,
          primeTranslator_channel_zero_of_p_lt hp.pos hgt]
    · simp [channelResidualTerm, hDd]

/-- Scaling coefficients scales every channel numerator exactly. -/
theorem channelNumerator_mul_coeff
    {ι : Type*} [Fintype ι]
    (z : ℤ) (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) :
    channelNumerator (fun j => z * coeff j) index d =
      z * channelNumerator coeff index d := by
  unfold channelNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Factorial moments split across a disjoint union of finite supports. -/
theorem factorialMoment_sum_type
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (leftCoeff : ι → ℤ) (leftIndex : ι → ℕ)
    (rightCoeff : κ → ℤ) (rightIndex : κ → ℕ) :
    factorialMoment (Sum.elim leftCoeff rightCoeff)
        (Sum.elim leftIndex rightIndex) =
      factorialMoment leftCoeff leftIndex +
        factorialMoment rightCoeff rightIndex := by
  unfold factorialMoment
  exact Fintype.sum_sum_type _

/-- Channel numerators split across a disjoint union of finite supports. -/
theorem channelNumerator_sum_type
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (leftCoeff : ι → ℤ) (leftIndex : ι → ℕ)
    (rightCoeff : κ → ℤ) (rightIndex : κ → ℕ) (d : ℕ) :
    channelNumerator (Sum.elim leftCoeff rightCoeff)
        (Sum.elim leftIndex rightIndex) d =
      channelNumerator leftCoeff leftIndex d +
        channelNumerator rightCoeff rightIndex d := by
  unfold channelNumerator
  exact Fintype.sum_sum_type _

/-- Each residual summand splits across a disjoint union of finite supports. -/
theorem channelResidualTerm_sum_type
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : ℕ)
    (leftCoeff : ι → ℤ) (leftIndex : ι → ℕ)
    (rightCoeff : κ → ℤ) (rightIndex : κ → ℕ) (d : ℕ) :
    channelResidualTerm D (Sum.elim leftCoeff rightCoeff)
        (Sum.elim leftIndex rightIndex) d =
      channelResidualTerm D leftCoeff leftIndex d +
        channelResidualTerm D rightCoeff rightIndex d := by
  by_cases hDd : D < d
  · rw [channelResidualTerm, if_pos hDd,
      channelResidualTerm, if_pos hDd,
      channelResidualTerm, if_pos hDd,
      channelNumerator_sum_type]
    push_cast
    ring
  · simp [channelResidualTerm, hDd]

/-- The full residual splits across a disjoint union of finite supports. -/
theorem channelResidual_sum_type
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : ℕ)
    (leftCoeff : ι → ℤ) (leftIndex : ι → ℕ)
    (rightCoeff : κ → ℤ) (rightIndex : κ → ℕ) :
    channelResidual D (Sum.elim leftCoeff rightCoeff)
        (Sum.elim leftIndex rightIndex) =
      channelResidual D leftCoeff leftIndex +
        channelResidual D rightCoeff rightIndex := by
  unfold channelResidual
  calc
    (∑' d : ℕ,
        channelResidualTerm D (Sum.elim leftCoeff rightCoeff)
          (Sum.elim leftIndex rightIndex) d) =
        ∑' d : ℕ,
          (channelResidualTerm D leftCoeff leftIndex d +
            channelResidualTerm D rightCoeff rightIndex d) := by
      apply tsum_congr
      intro d
      exact channelResidualTerm_sum_type D leftCoeff leftIndex
        rightCoeff rightIndex d
    _ = (∑' d : ℕ, channelResidualTerm D leftCoeff leftIndex d) +
        ∑' d : ℕ, channelResidualTerm D rightCoeff rightIndex d :=
      (summable_channelResidualTerm D leftCoeff leftIndex).tsum_add
        (summable_channelResidualTerm D rightCoeff rightIndex)

/-- Append an integer multiple of the prime translator on a disjoint support. -/
def appendPrimeTranslatorCoeff
    {ι : Type*} (coeff : ι → ℤ) (p : ℕ) (z : ℤ) :
    Sum ι (Fin 2) → ℤ :=
  Sum.elim coeff (fun j => z * primeTranslatorCoeff p j)

/-- Indices for a support enlarged by the prime translator. -/
def appendPrimeTranslatorIndex
    {ι : Type*} (index : ι → ℕ) (p : ℕ) :
    Sum ι (Fin 2) → ℕ :=
  Sum.elim index (primeTranslatorIndex p)

/-- Appending a prime translator preserves the factorial moment. -/
theorem factorialMoment_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {p : ℕ} (z : ℤ)
    (hp : 0 < p) :
    factorialMoment (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) =
      factorialMoment coeff index := by
  change factorialMoment
      (Sum.elim coeff (fun j => z * primeTranslatorCoeff p j))
      (Sum.elim index (primeTranslatorIndex p)) =
    factorialMoment coeff index
  rw [factorialMoment_sum_type]
  have hscaled :
      factorialMoment (fun j => z * primeTranslatorCoeff p j)
          (primeTranslatorIndex p) =
        z * factorialMoment (primeTranslatorCoeff p)
          (primeTranslatorIndex p) := by
    unfold factorialMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hscaled, primeTranslator_moment_zero hp]
  simp

/-- Appending a prime translator does not change any requested channel below
its prime. -/
theorem channelNumerator_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {p d : ℕ} (z : ℤ)
    (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    channelNumerator (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) d =
      channelNumerator coeff index d := by
  change channelNumerator
      (Sum.elim coeff (fun j => z * primeTranslatorCoeff p j))
      (Sum.elim index (primeTranslatorIndex p)) d =
    channelNumerator coeff index d
  rw [channelNumerator_sum_type, channelNumerator_mul_coeff,
    primeTranslator_channel_zero_of_lt_p hp hd2 hdp]
  simp

/-- Every integer multiple of the prime translator shifts the full residual
by exactly that integer. -/
theorem primeTranslator_scaled_channelResidual_eq_int
    {D p : ℕ} (z : ℤ) (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (fun j => z * primeTranslatorCoeff p j)
        (primeTranslatorIndex p) = (z : ℝ) := by
  rw [channelResidual, tsum_eq_single p]
  · have hfacReal : (1 : ℝ) < (p.factorial : ℝ) := by
      exact_mod_cast Nat.one_lt_factorial.mpr hp.one_lt
    have hgapReal : (p.factorial : ℝ) - 1 ≠ 0 := by
      linarith
    rw [channelResidualTerm, if_pos hDp,
      channelNumerator_mul_coeff,
      primeTranslator_channel_at_prime hp]
    push_cast
    field_simp [hgapReal]
  · intro d hdp
    by_cases hDd : D < d
    · have hd2 : 2 ≤ d := by omega
      rw [channelResidualTerm, if_pos hDd, channelNumerator_mul_coeff]
      by_cases hlt : d < p
      · rw [primeTranslator_channel_zero_of_lt_p hp hd2 hlt]
        simp
      · have hgt : p < d := by omega
        rw [primeTranslator_channel_zero_of_p_lt hp.pos hgt]
        simp
    · simp [channelResidualTerm, hDd]

/-- Appending a scaled prime translator shifts the full residual by that
integer and changes nothing else in the original support. -/
theorem channelResidual_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ} (z : ℤ)
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) =
      channelResidual D coeff index + (z : ℝ) := by
  change channelResidual D
      (Sum.elim coeff (fun j => z * primeTranslatorCoeff p j))
      (Sum.elim index (primeTranslatorIndex p)) =
    channelResidual D coeff index + (z : ℝ)
  rw [channelResidual_sum_type,
    primeTranslator_scaled_channelResidual_eq_int z hD hp hDp]

/-- Nearest-integer rounding along the prime unit direction always places
the residual in the closed interval of radius `1/2`. -/
theorem exists_primeTranslator_residual_abs_le_half
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    ∃ z : ℤ,
      |channelResidual D (appendPrimeTranslatorCoeff coeff p z)
          (appendPrimeTranslatorIndex index p)| ≤ (1 : ℝ) / 2 := by
  let x := channelResidual D coeff index
  refine ⟨-round x, ?_⟩
  rw [channelResidual_appendPrimeTranslator coeff index (-round x) hD hp hDp]
  simpa [x, sub_eq_add_neg] using abs_sub_round x

/-- A nonzero-moment vector in the finite channel kernel can be enlarged by a
prime unit translator while preserving the requested zero channels and the
nonzero moment; its residual can then be reduced to absolute value at most
`1/2`. -/
theorem exists_primeTranslator_reduced_kernel
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p)
    (hchannels : ∀ d ∈ Finset.Icc 2 D,
      channelNumerator coeff index d = 0)
    (hmoment : factorialMoment coeff index ≠ 0) :
    ∃ z : ℤ,
      (∀ d ∈ Finset.Icc 2 D,
        channelNumerator (appendPrimeTranslatorCoeff coeff p z)
          (appendPrimeTranslatorIndex index p) d = 0) ∧
      factorialMoment (appendPrimeTranslatorCoeff coeff p z)
          (appendPrimeTranslatorIndex index p) ≠ 0 ∧
      |channelResidual D (appendPrimeTranslatorCoeff coeff p z)
          (appendPrimeTranslatorIndex index p)| ≤ (1 : ℝ) / 2 := by
  obtain ⟨z, hz⟩ :=
    exists_primeTranslator_residual_abs_le_half coeff index hD hp hDp
  refine ⟨z, ?_, ?_, hz⟩
  · intro d hd
    rw [channelNumerator_appendPrimeTranslator coeff index z hp
      (Finset.mem_Icc.mp hd).1
      ((Finset.mem_Icc.mp hd).2.trans_lt hDp)]
    exact hchannels d hd
  · rw [factorialMoment_appendPrimeTranslator coeff index z hp.pos]
    exact hmoment

/-- If the base residual is not an integer, nearest-integer translation gives
a strictly nonzero residual of absolute value at most `1/2`, while preserving
the finite channel kernel and factorial moment. -/
theorem exists_primeTranslator_strict_reduced_kernel
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p)
    (hchannels : ∀ d ∈ Finset.Icc 2 D,
      channelNumerator coeff index d = 0)
    (hmoment : factorialMoment coeff index ≠ 0)
    (hnonint : ∀ k : ℤ, channelResidual D coeff index ≠ (k : ℝ)) :
    ∃ z : ℤ,
      (∀ d ∈ Finset.Icc 2 D,
        channelNumerator (appendPrimeTranslatorCoeff coeff p z)
          (appendPrimeTranslatorIndex index p) d = 0) ∧
      factorialMoment (appendPrimeTranslatorCoeff coeff p z)
          (appendPrimeTranslatorIndex index p) ≠ 0 ∧
      0 < |channelResidual D (appendPrimeTranslatorCoeff coeff p z)
          (appendPrimeTranslatorIndex index p)| ∧
      |channelResidual D (appendPrimeTranslatorCoeff coeff p z)
          (appendPrimeTranslatorIndex index p)| ≤ (1 : ℝ) / 2 := by
  let x := channelResidual D coeff index
  let z : ℤ := -round x
  have hres :
      channelResidual D (appendPrimeTranslatorCoeff coeff p z)
          (appendPrimeTranslatorIndex index p) =
        x - (round x : ℝ) := by
    rw [channelResidual_appendPrimeTranslator coeff index z hD hp hDp]
    simp [x, z, sub_eq_add_neg]
  have hne : x - (round x : ℝ) ≠ 0 := by
    intro hzero
    exact hnonint (round x) (sub_eq_zero.mp hzero)
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [channelNumerator_appendPrimeTranslator coeff index z hp
      (Finset.mem_Icc.mp hd).1
      ((Finset.mem_Icc.mp hd).2.trans_lt hDp)]
    exact hchannels d hd
  · rw [factorialMoment_appendPrimeTranslator coeff index z hp.pos]
    exact hmoment
  · rw [hres]
    exact abs_pos.mpr hne
  · rw [hres]
    exact abs_sub_round x

/-- Square augmented matrix whose first row is the factorial moment and whose
remaining rows are the consecutive channels `2, ..., n + 1`. -/
def augmentedChannelMomentMatrix
    {n : ℕ} (index : Fin (n + 1) → ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun r j =>
    Fin.cases ((index j).factorial : ℤ)
      (fun d : Fin n =>
        ((index j).factorial /
          (d.val + 2).factorial ^ (index j / (d.val + 2)) : ℕ))
      r

/-- Cramer's-rule coefficient vector for unit factorial moment and zero
consecutive channels. -/
def cramerChannelKernelCoeff
    {n : ℕ} (index : Fin (n + 1) → ℕ) :
    Fin (n + 1) → ℤ :=
  (augmentedChannelMomentMatrix index).cramer (Pi.single 0 1)

/-- Evaluating a Cramer vector against any row is the determinant obtained
by replacing the distinguished row by that row.  This converts every later
tail-channel numerator into one exact determinant, rather than a signed sum
of opaque Cramer coefficients. -/
theorem dotProduct_cramer_single_eq_det_updateRow
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (row : Fin (n + 1) → ℤ) :
    row ⬝ᵥ A.cramer (Pi.single 0 1) =
      (A.updateRow 0 row).det := by
  have hvec :
      A.transpose.cramer row = Matrix.vecMul row A.adjugate := by
    rw [Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose, Matrix.mulVec_transpose]
  calc
    row ⬝ᵥ A.cramer (Pi.single 0 1) =
        row ⬝ᵥ Matrix.mulVec A.adjugate (Pi.single 0 1) := by
          rw [Matrix.cramer_eq_adjugate_mulVec]
    _ = Matrix.vecMul row A.adjugate ⬝ᵥ (Pi.single 0 1) :=
          Matrix.dotProduct_mulVec row A.adjugate (Pi.single 0 1)
    _ = (A.transpose.cramer row) 0 := by
          rw [dotProduct_single_one, ← hvec]
    _ = (A.updateRow 0 row).det :=
          Matrix.cramer_transpose_apply A row 0

/-- The integral coefficient row of one channel on a fixed support. -/
def channelCoefficientRow
    {ι : Type*} (index : ι → ℕ) (d : ℕ) : ι → ℤ :=
  fun j =>
    (index j).factorial /
      d.factorial ^ (index j / d)

/-- A channel numerator is the dot product of its coefficient row with the
chosen integer coefficient vector. -/
theorem channelNumerator_eq_dotProduct_channelCoefficientRow
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) :
    channelNumerator coeff index d =
      channelCoefficientRow index d ⬝ᵥ coeff := by
  simp [channelNumerator, channelCoefficientRow, dotProduct, mul_comm]

/-- Every channel numerator of the distinguished Cramer kernel is exactly
the determinant formed by replacing the moment row with that channel row.
This identity remains valid beyond the Vandermonde range, including at the
floor-discontinuous tail channels where termwise sign control fails. -/
theorem channelNumerator_cramerChannelKernel_eq_det_updateRow
    {n : ℕ} (index : Fin (n + 1) → ℕ) (d : ℕ) :
    channelNumerator (cramerChannelKernelCoeff index) index d =
      ((augmentedChannelMomentMatrix index).updateRow 0
        (channelCoefficientRow index d)).det := by
  rw [channelNumerator_eq_dotProduct_channelCoefficientRow]
  exact dotProduct_cramer_single_eq_det_updateRow
    (augmentedChannelMomentMatrix index) (channelCoefficientRow index d)

/-- Cramer's rule packages the determinant as the moment row and zero in every
channel row. -/
theorem cramerChannelKernel_mulVec
    {n : ℕ} (index : Fin (n + 1) → ℕ) :
    Matrix.mulVec (augmentedChannelMomentMatrix index)
        (cramerChannelKernelCoeff index) =
      (augmentedChannelMomentMatrix index).det • (Pi.single 0 1) :=
  Matrix.mulVec_cramer _ _

/-- The Cramer coefficient vector has factorial moment equal to the augmented
determinant. -/
theorem factorialMoment_cramerChannelKernel
    {n : ℕ} (index : Fin (n + 1) → ℕ) :
    factorialMoment (cramerChannelKernelCoeff index) index =
      (augmentedChannelMomentMatrix index).det := by
  have h := congrFun (cramerChannelKernel_mulVec index) (0 : Fin (n + 1))
  simpa [Matrix.mulVec, augmentedChannelMomentMatrix, factorialMoment,
    cramerChannelKernelCoeff, mul_comm] using h

/-- Every channel row of the Cramer coefficient vector vanishes. -/
theorem channelNumerator_cramerChannelKernel_zero
    {n : ℕ} (index : Fin (n + 1) → ℕ) (d : Fin n) :
    channelNumerator (cramerChannelKernelCoeff index) index (d.val + 2) = 0 := by
  have h := congrFun (cramerChannelKernel_mulVec index) d.succ
  simpa [Matrix.mulVec, augmentedChannelMomentMatrix, channelNumerator,
    cramerChannelKernelCoeff, mul_comm] using h

/-- One explicit nonzero determinant produces a finite channel-kernel vector
with nonzero factorial moment. -/
theorem exists_nonzeroMoment_channelKernel_of_augmented_det_ne_zero
    {n : ℕ} (index : Fin (n + 1) → ℕ)
    (hdet : (augmentedChannelMomentMatrix index).det ≠ 0) :
    ∃ coeff : Fin (n + 1) → ℤ,
      (∀ d : Fin n,
        channelNumerator coeff index (d.val + 2) = 0) ∧
      factorialMoment coeff index ≠ 0 := by
  refine ⟨cramerChannelKernelCoeff index, ?_, ?_⟩
  · exact channelNumerator_cramerChannelKernel_zero index
  · rw [factorialMoment_cramerChannelKernel index]
    exact hdet

/-- A square factorial scale divisible by every product of two consecutive
positive integers below `D`. The square is chosen to make the exact grid
arithmetic elementary. -/
def factorialGridScale (D : ℕ) : ℕ :=
  D.factorial ^ 2

/-- Integer reciprocal of the normalized Vandermonde node associated with
channel `d` at the common factorial grid scale. -/
def factorialGridBase (D d : ℕ) : ℕ :=
  d.factorial ^ (factorialGridScale D / d)

/-- The elementary inequality underlying strict monotonicity of factorial
roots. -/
theorem factorial_lt_succ_pow
    {d : ℕ} (hd : 0 < d) :
    d.factorial < (d + 1) ^ d := by
  exact d.factorial_le_pow.trans_lt
    (Nat.pow_lt_pow_left (Nat.lt_succ_self d) hd.ne')

/-- Consecutive factorial-grid bases are strictly increasing. This is the
exact integer form of strict monotonicity of `(d!)^(1/d)` needed by the
Vandermonde construction. -/
theorem factorialGridBase_lt_succ
    {D d : ℕ} (hd : 0 < d) (hdD : d + 1 ≤ D) :
    factorialGridBase D d < factorialGridBase D (d + 1) := by
  let L := factorialGridScale D
  let k := L / (d * (d + 1))
  have hd_dvd : d ∣ D.factorial :=
    Nat.dvd_factorial hd (by omega)
  have hds_dvd : d + 1 ∣ D.factorial :=
    Nat.dvd_factorial (by omega) hdD
  have hprod : d * (d + 1) ∣ L := by
    dsimp [L, factorialGridScale]
    simpa [pow_two] using Nat.mul_dvd_mul hd_dvd hds_dvd
  have hLpos : 0 < L := by
    dsimp [L, factorialGridScale]
    positivity
  have hdenpos : 0 < d * (d + 1) := by positivity
  have hk : 0 < k := by
    exact Nat.div_pos (Nat.le_of_dvd hLpos hprod) hdenpos
  have hfactor :
      d.factorial ^ (d + 1) < (d + 1).factorial ^ d := by
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    have h := factorial_lt_succ_pow hd
    nlinarith [show 0 < d.factorial ^ d by positivity]
  have hL :
      L = d * (d + 1) * k := by
    exact (Nat.mul_div_cancel' hprod).symm
  have hdivd : L / d = (d + 1) * k := by
    rw [hL]
    simp [Nat.mul_assoc, hd.ne']
  have hdivds : L / (d + 1) = d * k := by
    calc
      L / (d + 1) = ((d + 1) * (d * k)) / (d + 1) := by
        congr 1
        rw [hL]
        ring
      _ = d * k := by
        simpa [mul_comm] using Nat.mul_div_left (d * k) (d + 1)
  dsimp [factorialGridBase]
  change d.factorial ^ (L / d) <
    (d + 1).factorial ^ (L / (d + 1))
  rw [hdivd, hdivds, pow_mul, pow_mul]
  exact Nat.pow_lt_pow_left hfactor hk.ne'

/-- Vandermonde nodes for a cutoff with `n + 1` channel rows: the moment node
is `1`, followed by the exact integer reciprocal nodes for channels
`2, ..., n + 2`. -/
def factorialGridVandermondeNode (n : ℕ) : Fin (n + 2) → ℕ :=
  Fin.cases 1
    (fun d : Fin (n + 1) =>
      factorialGridBase (n + 2) (d.val + 2))

/-- The first factorial-grid channel node is strictly larger than the moment
node. -/
theorem one_lt_factorialGridBase_two (n : ℕ) :
    1 < factorialGridBase (n + 2) 2 := by
  have hscale : 2 ≤ factorialGridScale (n + 2) := by
    dsimp [factorialGridScale]
    have hfac : 2 ≤ (n + 2).factorial := by
      exact Nat.one_lt_factorial.mpr (by omega)
    nlinarith
  have hexp : 0 < factorialGridScale (n + 2) / 2 :=
    Nat.div_pos hscale (by norm_num)
  change 1 < 2 ^ (factorialGridScale (n + 2) / 2)
  exact one_lt_pow₀ (by norm_num) hexp.ne'

/-- All exact factorial-grid Vandermonde nodes are strictly increasing and
hence pairwise distinct. -/
theorem factorialGridVandermondeNode_strictMono (n : ℕ) :
    StrictMono (factorialGridVandermondeNode n) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  refine Fin.cases ?_ (fun d => ?_) i
  · simpa [factorialGridVandermondeNode] using
      one_lt_factorialGridBase_two n
  · change factorialGridBase (n + 2) (d.val + 2) <
      factorialGridBase (n + 2) (d.val + 3)
    exact factorialGridBase_lt_succ (by omega) (by omega)

/-- Rational normalized Vandermonde nodes: reciprocals of the exact integer
grid bases, including the moment node `1`. -/
def factorialGridReciprocalNode (n : ℕ) : Fin (n + 2) → ℚ :=
  fun i => (factorialGridVandermondeNode n i : ℚ)⁻¹

/-- The normalized reciprocal nodes remain pairwise distinct. -/
theorem factorialGridReciprocalNode_injective (n : ℕ) :
    Function.Injective (factorialGridReciprocalNode n) := by
  intro i j hij
  apply (factorialGridVandermondeNode_strictMono n).injective
  have hcast :
      (factorialGridVandermondeNode n i : ℚ) =
        (factorialGridVandermondeNode n j : ℚ) := by
    exact inv_injective hij
  exact_mod_cast hcast

/-- The exact normalized factorial-grid Vandermonde determinant is nonzero. -/
theorem factorialGrid_vandermonde_det_ne_zero (n : ℕ) :
    (Matrix.vandermonde (factorialGridReciprocalNode n)).det ≠ 0 := by
  exact Matrix.det_vandermonde_ne_zero_iff.mpr
    (factorialGridReciprocalNode_injective n)

/-- Consecutive factorial-grid columns beginning at exponent `t`, written as
a row-scaled Vandermonde matrix. -/
def factorialGridShiftedVandermonde
    (n t : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ :=
  Matrix.diagonal (fun i => factorialGridReciprocalNode n i ^ t) *
    Matrix.vandermonde (factorialGridReciprocalNode n)

/-- Entrywise, the shifted matrix consists of consecutive powers
`alpha_i^(t+j)`. -/
theorem factorialGridShiftedVandermonde_apply
    (n t : ℕ) (i j : Fin (n + 2)) :
    factorialGridShiftedVandermonde n t i j =
      factorialGridReciprocalNode n i ^ (t + j.val) := by
  rw [factorialGridShiftedVandermonde, Matrix.diagonal_mul]
  simp [Matrix.vandermonde, pow_add]

/-- Every reciprocal factorial-grid node is nonzero. -/
theorem factorialGridReciprocalNode_ne_zero
    (n : ℕ) (i : Fin (n + 2)) :
    factorialGridReciprocalNode n i ≠ 0 := by
  unfold factorialGridReciprocalNode
  apply inv_ne_zero
  have hpos : 0 < factorialGridVandermondeNode n i := by
    refine Fin.cases ?_ (fun d => ?_) i
    · simp [factorialGridVandermondeNode]
    · simp [factorialGridVandermondeNode, factorialGridBase]
      positivity
  exact_mod_cast hpos.ne'

/-- Any consecutive block of normalized factorial-grid columns has nonzero
determinant. -/
theorem factorialGridShiftedVandermonde_det_ne_zero
    (n t : ℕ) :
    (factorialGridShiftedVandermonde n t).det ≠ 0 := by
  rw [factorialGridShiftedVandermonde, Matrix.det_mul,
    Matrix.det_diagonal]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero _ (factorialGridReciprocalNode_ne_zero n i)
  · exact factorialGrid_vandermonde_det_ne_zero n

/-- Exact support indices for consecutive factorial-grid columns beginning at
exponent `t`. -/
def factorialGridIndex
    (n t : ℕ) (j : Fin (n + 2)) : ℕ :=
  (t + j.val) * factorialGridScale (n + 2)

/-- Normalizing an integral channel coefficient by its ambient factorial
recovers the reciprocal channel denominator exactly. -/
theorem channelCoefficient_div_factorial
    {i d : ℕ} (hd : 0 < d) :
    (((i.factorial / d.factorial ^ (i / d) : ℕ) : ℚ) /
        (i.factorial : ℚ)) =
      ((d.factorial ^ (i / d) : ℕ) : ℚ)⁻¹ := by
  have hhi : i < (i / d + 1) * d := by
    rw [← Nat.div_lt_iff_lt_mul hd]
    exact Nat.lt_succ_self _
  have hmul := channel_coefficient_band
    (d := d) (i := i) (k := i / d)
    (Nat.div_mul_le_self i d) hhi
  have hfac : (i.factorial : ℚ) ≠ 0 := by positivity
  have hden :
      (((d.factorial ^ (i / d) : ℕ) : ℚ)) ≠ 0 := by positivity
  apply (div_eq_iff hfac).2
  have hcast :
      (((d.factorial ^ (i / d) : ℕ) : ℚ)) *
          (((i.factorial / d.factorial ^ (i / d) : ℕ) : ℚ)) =
        (i.factorial : ℚ) := by
    exact_mod_cast hmul
  rw [← hcast]
  field_simp

/-- Every requested channel divides the common factorial-grid scale. -/
theorem channel_dvd_factorialGridScale
    {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n + 2) :
    d ∣ factorialGridScale (n + 2) := by
  have hfac : d ∣ (n + 2).factorial :=
    Nat.dvd_factorial hd hdn
  dsimp [factorialGridScale]
  simpa [pow_two] using dvd_mul_of_dvd_left hfac (n + 2).factorial

/-- Quotients of factorial-grid indices by requested channels have the exact
linear exponent expected by the Vandermonde parameterization. -/
theorem factorialGridIndex_div
    {n t : ℕ} (j : Fin (n + 2)) {d : ℕ}
    (hd : 0 < d) (hdn : d ≤ n + 2) :
    factorialGridIndex n t j / d =
      (t + j.val) * (factorialGridScale (n + 2) / d) := by
  unfold factorialGridIndex
  exact Nat.mul_div_assoc (t + j.val)
    (channel_dvd_factorialGridScale hd hdn)

/-- The augmented integer channel/moment matrix on the factorial grid,
column-normalized over the rationals by the ambient factorials. -/
def normalizedFactorialGridMatrix
    (n t : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ :=
  (augmentedChannelMomentMatrix (factorialGridIndex n t)).map
      (Int.castRingHom ℚ) *
    Matrix.diagonal
      (fun j => ((factorialGridIndex n t j).factorial : ℚ)⁻¹)

/-- The normalized augmented channel/moment matrix is exactly the shifted
Vandermonde matrix on the reciprocal factorial-grid nodes. -/
theorem normalizedFactorialGridMatrix_eq_shiftedVandermonde
    (n t : ℕ) :
    normalizedFactorialGridMatrix n t =
      factorialGridShiftedVandermonde n t := by
  ext r j
  rw [factorialGridShiftedVandermonde_apply]
  refine Fin.cases ?_ (fun d => ?_) r
  · rw [normalizedFactorialGridMatrix, Matrix.mul_diagonal]
    have hfac :
        ((factorialGridIndex n t j).factorial : ℚ) ≠ 0 := by
      positivity
    simp [augmentedChannelMomentMatrix, factorialGridReciprocalNode,
      factorialGridVandermondeNode, hfac]
  · rw [normalizedFactorialGridMatrix, Matrix.mul_diagonal]
    change
      ((((factorialGridIndex n t j).factorial /
            (d.val + 2).factorial ^
              (factorialGridIndex n t j / (d.val + 2)) : ℕ) : ℚ) *
          ((factorialGridIndex n t j).factorial : ℚ)⁻¹) =
        factorialGridReciprocalNode n d.succ ^ (t + j.val)
    rw [← div_eq_mul_inv,
      channelCoefficient_div_factorial
        (i := factorialGridIndex n t j) (d := d.val + 2) (by omega)]
    have hdlt := d.isLt
    rw [factorialGridIndex_div j (by omega) (by omega)]
    simp [factorialGridReciprocalNode, factorialGridVandermondeNode,
      factorialGridBase, pow_mul]
    rw [← pow_mul, ← pow_mul, mul_comm]

/-- The normalized augmented matrix on every consecutive factorial-grid block
has nonzero determinant. -/
theorem normalizedFactorialGridMatrix_det_ne_zero
    (n t : ℕ) :
    (normalizedFactorialGridMatrix n t).det ≠ 0 := by
  rw [normalizedFactorialGridMatrix_eq_shiftedVandermonde]
  exact factorialGridShiftedVandermonde_det_ne_zero n t

/-- The original integer augmented channel/moment matrix on the factorial
grid also has nonzero determinant. -/
theorem augmentedFactorialGridMatrix_det_ne_zero
    (n t : ℕ) :
    (augmentedChannelMomentMatrix (factorialGridIndex n t)).det ≠ 0 := by
  intro hzero
  have hmap :
      ((augmentedChannelMomentMatrix (factorialGridIndex n t)).map
          (Int.castRingHom ℚ)).det = 0 := by
    have hcast :
        (((augmentedChannelMomentMatrix
          (factorialGridIndex n t)).det : ℤ) : ℚ) = 0 := by
      rw [hzero]
      norm_num
    simpa only [Int.cast_det] using hcast
  apply normalizedFactorialGridMatrix_det_ne_zero n t
  rw [normalizedFactorialGridMatrix, Matrix.det_mul, hmap]
  simp

/-- Every factorial-grid block explicitly produces an integer coefficient
vector with zero consecutive channels and nonzero factorial moment. -/
theorem exists_factorialGrid_nonzeroMoment_channelKernel
    (n t : ℕ) :
    ∃ coeff : Fin (n + 2) → ℤ,
      (∀ d : Fin (n + 1),
        channelNumerator coeff (factorialGridIndex n t) (d.val + 2) = 0) ∧
      factorialMoment coeff (factorialGridIndex n t) ≠ 0 := by
  exact exists_nonzeroMoment_channelKernel_of_augmented_det_ne_zero
    (factorialGridIndex n t)
    (augmentedFactorialGridMatrix_det_ne_zero n t)

/-- The explicit factorial-grid Cramer vector annihilates every channel from
`2` through `n + 2`. -/
theorem cramerFactorialGrid_channels_zero
    (n t : ℕ) :
    ∀ d ∈ Finset.Icc 2 (n + 2),
      channelNumerator
        (cramerChannelKernelCoeff (factorialGridIndex n t))
        (factorialGridIndex n t) d = 0 := by
  intro d hd
  let k : Fin (n + 1) := ⟨d - 2, by
    have hdle := (Finset.mem_Icc.mp hd).2
    omega⟩
  have hdge := (Finset.mem_Icc.mp hd).1
  have hk :=
    channelNumerator_cramerChannelKernel_zero
      (factorialGridIndex n t) k
  have hkd : k.val + 2 = d := by
    dsimp [k]
    omega
  simpa [hkd] using hk

/-- The explicit factorial-grid Cramer vector has nonzero factorial moment. -/
theorem cramerFactorialGrid_moment_ne_zero
    (n t : ℕ) :
    factorialMoment
        (cramerChannelKernelCoeff (factorialGridIndex n t))
        (factorialGridIndex n t) ≠ 0 := by
  rw [factorialMoment_cramerChannelKernel]
  exact augmentedFactorialGridMatrix_det_ne_zero n t

/-- For the factorial-grid Cramer vector, the residual differs from the
nonzero augmented determinant times the Erdős problem 68 series by an
integer. -/
theorem exists_cramerFactorialGridResidual_eq_det_mul_factorialGapSeries_add_int
    (n t : ℕ) :
    ∃ K : ℤ,
      channelResidual (n + 2)
          (cramerChannelKernelCoeff (factorialGridIndex n t))
          (factorialGridIndex n t) =
        ((augmentedChannelMomentMatrix
          (factorialGridIndex n t)).det : ℝ) *
            factorialGapSeries +
          (K : ℝ) := by
  obtain ⟨K, hK⟩ :=
    exists_channelResidual_eq_moment_mul_factorialGapSeries_add_int
      (n + 2)
      (cramerChannelKernelCoeff (factorialGridIndex n t))
      (factorialGridIndex n t) (by omega)
      (cramerFactorialGrid_channels_zero n t)
  refine ⟨K, ?_⟩
  simpa [factorialMoment_cramerChannelKernel] using hK

/-- Beyond the largest factorial-grid support index, every tail numerator is
exactly the fixed factorial moment.  Thus the floor-discontinuous finite
region is the only place where channel signs can change. -/
theorem cramerFactorialGrid_channelNumerator_eq_moment_of_max_lt
    (n t d : ℕ)
    (hmax :
      (t + (n + 1)) * factorialGridScale (n + 2) < d) :
    channelNumerator
        (cramerChannelKernelCoeff (factorialGridIndex n t))
        (factorialGridIndex n t) d =
      factorialMoment
        (cramerChannelKernelCoeff (factorialGridIndex n t))
        (factorialGridIndex n t) := by
  apply channelNumerator_eq_factorialMoment_of_all_lt
  intro j
  unfold factorialGridIndex
  have hj : j.val ≤ n + 1 := by omega
  have hsum : t + j.val ≤ t + (n + 1) :=
    Nat.add_le_add_left hj t
  exact (Nat.mul_le_mul_right (factorialGridScale (n + 2)) hsum).trans_lt hmax

/-- In particular, no factorial-grid Cramer tail numerator can vanish once
the channel lies beyond the largest support index. -/
theorem cramerFactorialGrid_channelNumerator_ne_zero_of_max_lt
    (n t d : ℕ)
    (hmax :
      (t + (n + 1)) * factorialGridScale (n + 2) < d) :
    channelNumerator
        (cramerChannelKernelCoeff (factorialGridIndex n t))
        (factorialGridIndex n t) d ≠ 0 := by
  rw [cramerFactorialGrid_channelNumerator_eq_moment_of_max_lt n t d hmax]
  exact cramerFactorialGrid_moment_ne_zero n t

/-- Every factorial-grid Cramer vector can be enlarged by a prime translator
above the cutoff, preserving its zero channels and nonzero moment while
reducing the residual to absolute value at most `1/2`. -/
theorem exists_factorialGrid_primeTranslator_reduced_kernel
    (n t : ℕ) {p : ℕ}
    (hp : p.Prime) (hDp : n + 2 < p) :
    ∃ z : ℤ,
      (∀ d ∈ Finset.Icc 2 (n + 2),
        channelNumerator
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff (factorialGridIndex n t)) p z)
          (appendPrimeTranslatorIndex (factorialGridIndex n t) p) d = 0) ∧
      factorialMoment
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff (factorialGridIndex n t)) p z)
          (appendPrimeTranslatorIndex (factorialGridIndex n t) p) ≠ 0 ∧
      |channelResidual (n + 2)
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff (factorialGridIndex n t)) p z)
          (appendPrimeTranslatorIndex (factorialGridIndex n t) p)| ≤
        (1 : ℝ) / 2 := by
  exact exists_primeTranslator_reduced_kernel
    (cramerChannelKernelCoeff (factorialGridIndex n t))
    (factorialGridIndex n t) (by omega) hp hDp
    (cramerFactorialGrid_channels_zero n t)
    (cramerFactorialGrid_moment_ne_zero n t)

/-- Choosing the grid start as `B+1` places every factorial-grid index above
the prescribed support threshold. -/
theorem factorialGridIndex_gt
    (n B : ℕ) (j : Fin (n + 2)) :
    B < factorialGridIndex n (B + 1) j := by
  have hscale : 0 < factorialGridScale (n + 2) := by
    dsimp [factorialGridScale]
    positivity
  have hleft : B + 1 ≤ B + 1 + j.val := by omega
  have hmul :
      B + 1 + j.val ≤
        (B + 1 + j.val) * factorialGridScale (n + 2) :=
    Nat.le_mul_of_pos_right _ hscale
  unfold factorialGridIndex
  omega

/-- For every cutoff and support threshold, a factorial-grid block and a prime
translator pair can be chosen entirely above the threshold, with the stated
zero-channel, nonzero-moment, and residual bounds. -/
theorem exists_remote_factorialGrid_primeTranslator_reduction
    (n B : ℕ) :
    ∃ p : ℕ, ∃ z : ℤ,
      p.Prime ∧
      (∀ j : Sum (Fin (n + 2)) (Fin 2),
        B < appendPrimeTranslatorIndex
          (factorialGridIndex n (B + 1)) p j) ∧
      (∀ d ∈ Finset.Icc 2 (n + 2),
        channelNumerator
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) d = 0) ∧
      factorialMoment
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) ≠ 0 ∧
      |channelResidual (n + 2)
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p)| ≤
        (1 : ℝ) / 2 := by
  obtain ⟨p, hpBound, hp⟩ :=
    Nat.exists_infinite_primes (max (n + 3) (B + 2))
  have hDp : n + 2 < p := by omega
  have hBp : B + 1 < p := by omega
  obtain ⟨z, hchannels, hmoment, hresidual⟩ :=
    exists_factorialGrid_primeTranslator_reduced_kernel
      n (B + 1) hp hDp
  refine ⟨p, z, hp, ?_, hchannels, hmoment, hresidual⟩
  intro j
  cases j with
  | inl j =>
      exact factorialGridIndex_gt n B j
  | inr j =>
      fin_cases j <;>
        simp [appendPrimeTranslatorIndex, primeTranslatorIndex] <;>
        omega

/-! The same remote construction retains strictness when the un-translated
residual is known not to be an integer.  The nonintegrality premise is kept
explicit: the construction does not manufacture the missing producer for the
Erdős #68 irrationality problem. -/
theorem exists_remote_factorialGrid_primeTranslator_strict_reduction
    (n B : ℕ)
    (hnonint :
      ∀ k : ℤ,
        channelResidual (n + 2)
          (cramerChannelKernelCoeff (factorialGridIndex n (B + 1)))
          (factorialGridIndex n (B + 1)) ≠ (k : ℝ)) :
    ∃ p : ℕ, ∃ z : ℤ,
      p.Prime ∧
      (∀ j : Sum (Fin (n + 2)) (Fin 2),
        B < appendPrimeTranslatorIndex
          (factorialGridIndex n (B + 1)) p j) ∧
      (∀ d ∈ Finset.Icc 2 (n + 2),
        channelNumerator
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) d = 0) ∧
      factorialMoment
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) ≠ 0 ∧
      0 < |channelResidual (n + 2)
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p)| ∧
      |channelResidual (n + 2)
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p)| ≤
        (1 : ℝ) / 2 := by
  obtain ⟨p, hpBound, hp⟩ :=
    Nat.exists_infinite_primes (max (n + 3) (B + 2))
  have hDp : n + 2 < p := by omega
  obtain ⟨z, hchannels, hmoment, hstrict, hresidual⟩ :=
    exists_primeTranslator_strict_reduced_kernel
      (cramerChannelKernelCoeff (factorialGridIndex n (B + 1)))
      (factorialGridIndex n (B + 1)) (by omega) hp hDp
      (cramerFactorialGrid_channels_zero n (B + 1))
      (cramerFactorialGrid_moment_ne_zero n (B + 1)) hnonint
  refine ⟨p, z, hp, ?_, hchannels, hmoment, hstrict, hresidual⟩
  intro j
  cases j with
  | inl j =>
      exact factorialGridIndex_gt n B j
  | inr j =>
      fin_cases j <;>
        simp [appendPrimeTranslatorIndex, primeTranslatorIndex] <;>
        omega

#print axioms primeTranslator_channelResidual_eq_one
#print axioms primeTranslator_scaled_channelResidual_eq_int
#print axioms exists_channelResidual_eq_moment_mul_factorialGapTail_add_int
#print axioms exists_channelResidual_eq_moment_mul_factorialGapSeries_add_int
#print axioms exists_primeTranslator_reduced_kernel
#print axioms exists_primeTranslator_strict_reduced_kernel
#print axioms exists_nonzeroMoment_channelKernel_of_augmented_det_ne_zero
#print axioms dotProduct_cramer_single_eq_det_updateRow
#print axioms channelNumerator_cramerChannelKernel_eq_det_updateRow
#print axioms factorialGridBase_lt_succ
#print axioms factorialGridVandermondeNode_strictMono
#print axioms factorialGrid_vandermonde_det_ne_zero
#print axioms factorialGridShiftedVandermonde_det_ne_zero
#print axioms channelCoefficient_div_factorial
#print axioms normalizedFactorialGridMatrix_det_ne_zero
#print axioms exists_factorialGrid_nonzeroMoment_channelKernel
#print axioms exists_cramerFactorialGridResidual_eq_det_mul_factorialGapSeries_add_int
#print axioms cramerFactorialGrid_channelNumerator_ne_zero_of_max_lt
#print axioms exists_factorialGrid_primeTranslator_reduced_kernel
#print axioms exists_remote_factorialGrid_primeTranslator_reduction
#print axioms exists_remote_factorialGrid_primeTranslator_strict_reduction
#print axioms summable_channelResidualTerm
#print axioms channelResidual_add_coeff
#print axioms factorialGapTail_eq_shifted_tsum
#print axioms hasSum_factorial_telescope
#print axioms one_div_factorial_sub_one_lt_telescope
#print axioms factorialGapTail_lt_one_div_factorial
#print axioms factorialGapTail_pos
#print axioms factorialGapSeries_eq_sum_add_tail

end Erdos68
