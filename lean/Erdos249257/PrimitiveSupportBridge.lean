import Erdos249257.BooleanMobiusCarry

/-!
# Primitive-support shell bridge for Erdős #257

The rational carry is forced by the divisor shadow `supportCoeff A`, not by
the primitive bit `1_A`.  This file records the exact place where the two
coincide after a finite prefix is removed: on the first dyadic shell
`X < n ≤ 2X`, a residual divisor of `n` larger than `X` can only be `n`.

It then packages the corresponding cross-carry.  If the full carry is scaled
by `q` and the finite-prefix carry by `D`, subtracting them at scale `qD`
leaves precisely the residual tail.  On the first shell its forcing digit is
therefore the primitive support bit.

The final two lemmas isolate the elementary denominator pressure used by the
density route.  They deliberately take the analytic tail bounds as
hypotheses: deriving denominator-uniform pressure from those bounds remains
the new global bottleneck.  Nothing here claims a Wang--Grau Ribas
specialisation or proves positive density.
-/

namespace Erdos249257

open Set

/-- Support already present at or below the shell cutoff. -/
def primitivePrefix (A : Set ℕ) (X : ℕ) : Set ℕ := A ∩ Set.Iic X

/-- Primitive innovations not present in the prefix through `X`. -/
def primitiveResidual (A : Set ℕ) (X : ℕ) : Set ℕ := A \ Set.Iic X

/-- Natural-valued primitive support bit, with classical membership hidden
behind a stable definition. -/
noncomputable def primitiveBit (A : Set ℕ) (n : ℕ) : ℕ :=
  by
    classical
    exact if n ∈ A then 1 else 0

/-- A divisor of `n` lying in `(X,2X]` is necessarily `n` itself. -/
theorem divisor_eq_self_of_cutoff_lt_of_le_two_mul
    {d n X : ℕ} (hd : d ∣ n) (hn0 : n ≠ 0)
    (hX : X < d) (hn : n ≤ 2 * X) :
    d = n := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hdpos : 0 < d := by omega
  have hdn : d ≤ n := Nat.le_of_dvd hnpos hd
  by_contra hne
  have hdlt : d < n := lt_of_le_of_ne hdn hne
  have hkpos : 0 < n / d := Nat.div_pos hdn hdpos
  have hkne : n / d ≠ 1 := by
    intro hk
    have hfactor := Nat.mul_div_cancel' hd
    simp only [hk, mul_one] at hfactor
    exact hne hfactor
  have hk : 2 ≤ n / d := by omega
  have h2d : 2 * d ≤ n := by
    calc
      2 * d ≤ (n / d) * d := Nat.mul_le_mul_right d hk
      _ = n := by simpa [mul_comm] using Nat.mul_div_cancel' hd
  omega

/-- On the first shell after removing the prefix, the divisor shadow is the
primitive support bit. -/
theorem supportCoeff_primitiveResidual_first_shell
    (A : Set ℕ) (X n : ℕ) (hXn : X < n) (hn2X : n ≤ 2 * X) :
    supportCoeff (primitiveResidual A X) n = primitiveBit A n := by
  classical
  rw [supportCoeff_eq_card_filter]
  by_cases hnA : n ∈ A
  · have hn0 : n ≠ 0 := by omega
    have hfilter :
        n.divisors.filter (fun d => d ∈ primitiveResidual A X) = {n} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hdvd, _⟩, hdA, hdX⟩
        exact divisor_eq_self_of_cutoff_lt_of_le_two_mul hdvd hn0
          (by simpa using hdX) hn2X
      · rintro rfl
        exact ⟨⟨dvd_rfl, hn0⟩, hnA, by simpa [primitiveResidual] using hXn⟩
    rw [hfilter]
    simp [primitiveBit, hnA]
  · have hfilter :
        n.divisors.filter (fun d => d ∈ primitiveResidual A X) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨d, hd⟩
      rcases Finset.mem_filter.mp hd with ⟨hddivs, hdA, hdX⟩
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hddivs).1
      have hn0 : n ≠ 0 := by omega
      have hdn := divisor_eq_self_of_cutoff_lt_of_le_two_mul hdvd hn0
        (by simpa using hdX) hn2X
      exact hnA (hdn ▸ hdA)
    rw [hfilter]
    simp [primitiveBit, hnA]

/-- The support coefficient splits exactly into prefix shadow and residual
shadow. -/
theorem supportCoeff_eq_primitivePrefix_add_residual
    (A : Set ℕ) (X n : ℕ) :
    supportCoeff A n =
      supportCoeff (primitivePrefix A X) n +
        supportCoeff (primitiveResidual A X) n := by
  classical
  rw [supportCoeff_eq_card_filter, supportCoeff_eq_card_filter,
    supportCoeff_eq_card_filter]
  let s := n.divisors.filter fun d => d ∈ A
  have hp :
      n.divisors.filter (fun d => d ∈ primitivePrefix A X) =
        s.filter fun d => d ≤ X := by
    ext d
    simp [s, primitivePrefix, and_assoc]
  have hr :
      n.divisors.filter (fun d => d ∈ primitiveResidual A X) =
        s.filter fun d => ¬ d ≤ X := by
    ext d
    simp [s, primitiveResidual, and_assoc]
  rw [hp, hr]
  exact (Finset.card_filter_add_card_filter_not
    (s := s) (fun d => d ≤ X)).symm

/-- Binary tails respect the exact prefix/residual support split. -/
theorem binaryCoeffTail_supportCoeff_eq_prefix_add_residual
    (A : Set ℕ) (X N : ℕ) :
    binaryCoeffTail (supportCoeff A) N =
      binaryCoeffTail (supportCoeff (primitivePrefix A X)) N +
        binaryCoeffTail (supportCoeff (primitiveResidual A X)) N := by
  have hp := summable_coeff_shift_tail 2 N
    (supportCoeff (primitivePrefix A X)) (by norm_num)
    (supportCoeff_le_self (primitivePrefix A X))
  have hr := summable_coeff_shift_tail 2 N
    (supportCoeff (primitiveResidual A X)) (by norm_num)
    (supportCoeff_le_self (primitiveResidual A X))
  unfold binaryCoeffTail
  calc
    (∑' j : ℕ, (supportCoeff A (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) =
        ∑' j : ℕ,
          ((supportCoeff (primitivePrefix A X) (N + j + 1) : ℝ) /
              (2 : ℝ) ^ (j + 1) +
            (supportCoeff (primitiveResidual A X) (N + j + 1) : ℝ) /
              (2 : ℝ) ^ (j + 1)) := by
          apply tsum_congr
          intro j
          rw [supportCoeff_eq_primitivePrefix_add_residual A X]
          push_cast
          ring
    _ = (∑' j : ℕ,
          (supportCoeff (primitivePrefix A X) (N + j + 1) : ℝ) /
            (2 : ℝ) ^ (j + 1)) +
        ∑' j : ℕ,
          (supportCoeff (primitiveResidual A X) (N + j + 1) : ℝ) /
            (2 : ℝ) ^ (j + 1) := hp.tsum_add hr

/-- Full support carry at a displayed multiplier `q`. -/
noncomputable def scaledSupportCarry
    (q : ℕ) (A : Set ℕ) (N : ℕ) : ℝ :=
  q * binaryCoeffTail (supportCoeff A) N

/-- Finite-prefix background carry at its reduced denominator `D`. -/
noncomputable def scaledPrefixCarry
    (D : ℕ) (A : Set ℕ) (X N : ℕ) : ℝ :=
  D * binaryCoeffTail (supportCoeff (primitivePrefix A X)) N

/-- Cross-carry obtained by subtracting the deterministic prefix background
from the full carry at common scale `qD`. -/
noncomputable def primitiveCrossCarry
    (q D : ℕ) (A : Set ℕ) (X N : ℕ) : ℝ :=
  D * scaledSupportCarry q A N - q * scaledPrefixCarry D A X N

/-- Exact cross-carry identity: the subtraction leaves the scaled residual
tail and no prefix shadow. -/
theorem primitiveCrossCarry_eq_residualTail
    (q D : ℕ) (A : Set ℕ) (X N : ℕ) :
    primitiveCrossCarry q D A X N =
      (q * D : ℕ) *
        binaryCoeffTail (supportCoeff (primitiveResidual A X)) N := by
  rw [primitiveCrossCarry, scaledSupportCarry, scaledPrefixCarry,
    binaryCoeffTail_supportCoeff_eq_prefix_add_residual]
  push_cast
  ring

/-- On the first residual shell, the cross-carry is forced by the primitive
bit rather than by the full divisor coefficient. -/
theorem primitiveCrossCarry_first_shell_recurrence
    (q D : ℕ) (A : Set ℕ) (X N : ℕ)
    (hXN : X < N + 1) (hN2X : N + 1 ≤ 2 * X) :
    primitiveCrossCarry q D A X (N + 1) =
      2 * primitiveCrossCarry q D A X N -
        (q * D : ℕ) * primitiveBit A (N + 1) := by
  rw [primitiveCrossCarry_eq_residualTail,
    primitiveCrossCarry_eq_residualTail,
    binaryCoeffTail_succ _ (supportCoeff_le_self _) N,
    supportCoeff_primitiveResidual_first_shell A X (N + 1) hXN hN2X]
  push_cast
  ring

/-- A nonempty residual support makes the cross-carry strictly positive. -/
theorem primitiveCrossCarry_pos
    (q D : ℕ) (hq : 0 < q) (hD : 0 < D)
    (A : Set ℕ) (X N : ℕ)
    (hres : ∃ a : ℕ, 0 < a ∧ a ∈ primitiveResidual A X) :
    0 < primitiveCrossCarry q D A X N := by
  rw [primitiveCrossCarry_eq_residualTail]
  exact mul_pos (by positivity)
    (binaryCoeffTail_supportCoeff_pos_of_exists_pos_mem _ hres N)

/-! ## Denominator pressure consequences -/

/-- If a positive residual is at least `1/(qD)` but its first dyadic shell
and geometric far tail contribute at most `K/2^X + 2/2^(2X)`, then
`2^X ≤ qD(K+1)`.  This is the division-free denominator/shell pressure
inequality; the analytic estimates are explicit hypotheses. -/
theorem prefixDenominator_shell_power_bound
    (q D K X : ℕ) (hq : 0 < q) (hD : 0 < D) (hX : 1 ≤ X)
    (beta : ℝ)
    (hlower : (1 : ℝ) / ((q * D : ℕ) : ℝ) ≤ beta)
    (hupper : beta ≤
      (K : ℝ) / (2 : ℝ) ^ X + 2 / (2 : ℝ) ^ (2 * X)) :
    ((2 : ℝ) ^ X) ≤ ((q * D : ℕ) : ℝ) * (K + 1) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ X := by positivity
  have hpowOne : (2 : ℝ) ≤ (2 : ℝ) ^ X := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hX)
  have hqd : (0 : ℝ) < ((q * D : ℕ) : ℝ) := by positivity
  have htail : 2 / (2 : ℝ) ^ X ≤ 1 := by
    exact (div_le_one hpow).2 hpowOne
  have hcombine :
      (1 : ℝ) / ((q * D : ℕ) : ℝ) ≤
        (K + 1 : ℕ) / (2 : ℝ) ^ X := by
    calc
      (1 : ℝ) / ((q * D : ℕ) : ℝ) ≤ beta := hlower
      _ ≤ (K : ℝ) / (2 : ℝ) ^ X + 2 / (2 : ℝ) ^ (2 * X) := hupper
      _ = ((K : ℝ) + 2 / (2 : ℝ) ^ X) / (2 : ℝ) ^ X := by
        rw [show 2 * X = X + X by omega, pow_add]
        field_simp
      _ ≤ ((K : ℝ) + 1) / (2 : ℝ) ^ X := by gcongr
      _ = (K + 1 : ℕ) / (2 : ℝ) ^ X := by push_cast; ring
  have hcross := (div_le_div_iff₀ hqd hpow).mp hcombine
  simpa [one_mul, mul_comm] using hcross

/-- The same elementary pressure excludes a next support exponent whose
power of two is larger than `4qD`. -/
theorem nextSupport_power_bound
    (q D m : ℕ) (hq : 0 < q) (hD : 0 < D) (beta : ℝ)
    (hlower : (1 : ℝ) / ((q * D : ℕ) : ℝ) ≤ beta)
    (hupper : beta ≤ 4 / (2 : ℝ) ^ m) :
    (2 : ℝ) ^ m ≤ 4 * ((q * D : ℕ) : ℝ) := by
  have hqd : (0 : ℝ) < ((q * D : ℕ) : ℝ) := by positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h := hlower.trans hupper
  have hcross := (div_le_div_iff₀ hqd hpow).mp h
  simpa [one_mul, mul_comm, mul_left_comm] using hcross

end Erdos249257
