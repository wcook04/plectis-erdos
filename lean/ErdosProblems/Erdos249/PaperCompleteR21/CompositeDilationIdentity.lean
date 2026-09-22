import Erdos249257.CompositeDilationDefect
import Erdos249257.MersenneLambertLadder

/-! Paper-form restatement of the long paper's composite-dilation proposition
(`catalogue:mob:f1`, "The error under composite dilation").

Every clause of the asserted environment is stated here: the unweighted
divisor-count identity under dilation by a support element, vanishing of the
extra term on a prime support, the composite counterexample at `A = ℕ`,
`a = 6`, `x = 1`, the Lambert transform of the support series, and the
properties of the totient convolution weight `α = φ * μ` (`α * 1 = φ`,
`∑_{d ∣ n} φ(d) = n ≠ φ(n)` already at `n = 2`, `α(p) = p - 2`, `α` unbounded
and therefore not periodic).

The existing proofs in `Erdos249257.CompositeDilationDefect`,
`Erdos249257` (support-coefficient calculus) and `MersenneLambertLadder`
carry the mathematical content. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.CompositeDilationDefect

/-- **The error under composite dilation.**  With
`d_A(n) = #{d ≥ 1 : d ∣ n, d ∈ A}` (the tree's `supportCoeff A`), for `a ∈ A`
and `a, x ≥ 1`,
`d_A(ax) = d_A(x) + 1_{a ∤ x} + #{d ∣ ax : d ∈ A, d ∤ x, d ≠ a}`. -/
theorem composite_dilation_divisor_count (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (ha1 : 1 ≤ a) (hx1 : 1 ≤ x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x :=
  supportCoeff_mul_eq_add_defect A ha ha1 hx1

/-- On a support all of whose elements are prime, the last set is empty: a
prime dividing `ax` but not `x` must equal the prime `a`. -/
theorem composite_dilation_defect_eq_zero_of_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hAprime : ∀ d ∈ A, d.Prime) :
    compositeDilationDefect A a x = 0 :=
  compositeDilationDefect_eq_zero_of_prime_support A (hAprime a ha) hAprime

/-- The prime-support specialisation of the identity. -/
theorem composite_dilation_divisor_count_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hx1 : 1 ≤ x) (hAprime : ∀ d ∈ A, d.Prime) :
    supportCoeff A (a * x) = supportCoeff A x + (if a ∣ x then 0 else 1) :=
  supportCoeff_mul_prime_support A (hAprime a ha) ha hx1 hAprime

/-- For composite `a` the extra set can be nonempty: at `A = ℕ`, `a = 6`,
`x = 1` the other new divisors are exactly `2` and `3`. -/
theorem composite_dilation_defect_univ_six_one :
    ((6 * 1 : ℕ).divisors.filter
        fun d => (d ∈ (Set.univ : Set ℕ) ∧ ¬ d ∣ 1 ∧ d ≠ 6)) = ({2, 3} : Finset ℕ) := by
  ext d
  constructor
  · intro hd
    obtain ⟨hdiv, -, hd1, hd6⟩ := Finset.mem_filter.mp hd
    have hdvd : d ∣ 6 := by simpa using (Nat.mem_divisors.mp hdiv).1
    have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hd1' : d ≠ 1 := fun h => hd1 (by rw [h])
    interval_cases d <;>
      first
        | exact absurd hdvd (by decide)
        | exact absurd rfl hd1'
        | exact absurd rfl hd6
        | decide
  · intro hd
    have hd' : d = 2 ∨ d = 3 := by simpa using hd
    rcases hd' with rfl | rfl <;>
      exact Finset.mem_filter.mpr ⟨by decide, Set.mem_univ _, by decide, by decide⟩

/-- Cardinal form of the same counterexample: the composite dilation defect is
`2`, so the prime-support vanishing genuinely fails for composite `a`. -/
theorem composite_dilation_defect_univ_six_one_card :
    compositeDilationDefect (Set.univ : Set ℕ) 6 1 = 2 := by
  have h : compositeDilationDefect (Set.univ : Set ℕ) 6 1 = (({2, 3} : Finset ℕ)).card := by
    unfold compositeDilationDefect
    congr 1
    convert composite_dilation_defect_univ_six_one using 2 <;>
      exact Subsingleton.elim _ _
  rw [h]
  decide

/-- **The associated Lambert series.**  `∑_{a ∈ A} 1/(2^a - 1) = ∑_{n ≥ 1} d_A(n)/2^n`. -/
theorem lambert_support_series (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1) := by
  have h := erdosSupportSeries_eq_tsum_supportCoeff 2 A (le_refl 2)
  simpa [erdosSupportSeries] using h

/-- The paper's left-hand side restricts the support to `a ≥ 1`; the `a = 0`
term contributes nothing on either reading, so the restricted sum is the same
real number. -/
theorem lambert_support_series_restricted (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator {a ∈ A | 1 ≤ a} (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1) := by
  rw [← lambert_support_series A]
  refine tsum_congr fun a => ?_
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · rw [Set.indicator_of_notMem (by simp)]
    by_cases h0 : (0 : ℕ) ∈ A
    · rw [Set.indicator_of_mem h0]
      norm_num
    · rw [Set.indicator_of_notMem h0]
  · by_cases hA : a ∈ A
    · rw [Set.indicator_of_mem (by exact ⟨hA, hpos⟩), Set.indicator_of_mem hA]
    · rw [Set.indicator_of_notMem (by simp [hA]), Set.indicator_of_notMem hA]

/-- **The totient convolution weight** `α = φ * μ` satisfies `α * 1 = φ`. -/
theorem totient_convolution_weight_mul_zeta (n : ℕ) :
    ∑ e ∈ n.divisors, MersenneLambertLadder.primWeight e = (Nat.totient n : ℤ) :=
  MersenneLambertLadder.sum_divisors_primWeight n

/-- Weighting all divisors by `φ` gives `n`, not `φ(n)`; already at `n = 2`
these values are `2` and `1`. -/
theorem sum_divisors_totient_ne_totient :
    (∀ n : ℕ, ∑ d ∈ n.divisors, Nat.totient d = n) ∧
      (∑ d ∈ (2 : ℕ).divisors, Nat.totient d) = 2 ∧ Nat.totient 2 = 1 :=
  ⟨Nat.sum_totient, by decide, by decide⟩

/-- `α(p) = p - 2` at every prime. -/
theorem totient_convolution_weight_prime {p : ℕ} (hp : p.Prime) :
    MersenneLambertLadder.primWeight p = (p : ℤ) - 2 :=
  MersenneLambertLadder.primWeight_apply_prime hp

/-- `α` is unbounded. -/
theorem totient_convolution_weight_unbounded :
    ¬ ∃ B : ℕ, ∀ n : ℕ, MersenneLambertLadder.primWeight n ≤ (B : ℤ) :=
  MersenneLambertLadder.primWeight_not_bounded

/-- `α` is therefore not a periodic weight: a periodic nonnegative arithmetic
function takes finitely many values, hence is bounded. -/
theorem totient_convolution_weight_not_periodic :
    ¬ ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ, MersenneLambertLadder.primWeight (n + p) =
        MersenneLambertLadder.primWeight n := by
  classical
  rintro ⟨p, hp, hper⟩
  have hadd : ∀ k n : ℕ, MersenneLambertLadder.primWeight (n + k * p) =
      MersenneLambertLadder.primWeight n := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
        intro n
        have hrw : n + (k + 1) * p = (n + k * p) + p := by ring
        rw [hrw, hper, ih]
  have hmod : ∀ n : ℕ, MersenneLambertLadder.primWeight n =
      MersenneLambertLadder.primWeight (n % p) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div' n p]
    exact hadd (n / p) (n % p)
  refine totient_convolution_weight_unbounded
    ⟨(Finset.range p).sup fun i => (MersenneLambertLadder.primWeight i).toNat, fun n => ?_⟩
  have hlt : n % p < p := Nat.mod_lt _ hp
  have hnn : 0 ≤ MersenneLambertLadder.primWeight (n % p) :=
    MersenneLambertLadder.primWeight_nonneg _
  have hsup : (MersenneLambertLadder.primWeight (n % p)).toNat ≤
      (Finset.range p).sup fun i => (MersenneLambertLadder.primWeight i).toNat :=
    Finset.le_sup (f := fun i => (MersenneLambertLadder.primWeight i).toNat)
      (Finset.mem_range.mpr hlt)
  have hcast : ((MersenneLambertLadder.primWeight (n % p)).toNat : ℤ) =
      MersenneLambertLadder.primWeight (n % p) := Int.toNat_of_nonneg hnn
  rw [hmod n, ← hcast]
  exact_mod_cast hsup

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_eq_zero_of_prime_support
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count_prime_support
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one_card
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series_restricted
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_mul_zeta
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_totient_ne_totient
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_prime
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_unbounded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_not_periodic
