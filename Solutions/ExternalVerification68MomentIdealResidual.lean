import ErdosProblems.Erdos68.PaperCompleteMomentIdeal
import ErdosProblems.Erdos68.PaperCompleteResidualIdentity

namespace Erdos249257.ExternalVerification68MomentIdealResidual

open Finsupp
open scoped BigOperators
noncomputable section

/-- Integral weight of index `i` in divisor channel `d`. -/
def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))

/-- Finite-support integer numerator in channel `d`. -/
def channelNumerator (f : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  f.sum fun i z => z * (channelWeight i d : ℤ)

/-- Factorial moment of a finite-support coefficient vector. -/
def factorialMoment (f : ℕ →₀ ℤ) : ℤ :=
  f.sum fun i z => z * (i.factorial : ℤ)

/-- Least common multiple of the channel moduli through `D`. -/
def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

/-- Adjacent difference `T_n = n e_(n-1) - e_n`. -/
noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1

/-- Isolated one-channel basis vector. -/
noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ :=
  n.strongRecOn' fun n rec =>
    if n ≤ 1 then 0
    else
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2
          else 0

/-- Coordinate zero is `e_1`; positive coordinate `j` is `U_(j+1)`. -/
noncomputable def channelBasisColumn (j : ℕ) : ℕ →₀ ℤ :=
  if j = 0 then single 1 1 else isolatedChannelUnit (j + 1)

noncomputable def channelSynthesis (a : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  a.sum (fun j z => z • channelBasisColumn j)

noncomputable def kernelCoordinates (D : ℕ) : ℕ →₀ ℤ :=
  single 0 (channelLCM D : ℤ) -
    ∑ d ∈ Finset.Icc 2 D,
      single (d - 1) ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1))

noncomputable def canonicalKernel (D : ℕ) : ℕ →₀ ℤ :=
  channelSynthesis (kernelCoordinates D)

noncomputable def kernelOne (D : ℕ) : ℤ := canonicalKernel D 1

noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1

noncomputable def finiteScalarGcd (D H : ℕ) : ℕ :=
  (Finset.Icc (D + 1) H).gcd (fun n => (channelScalar n).natAbs)

noncomputable def minimumMoment (D p : ℕ) : ℤ :=
  let G : ℤ := finiteScalarGcd D (D * (2 * p - 1))
  (channelLCM D : ℤ) * (G / (Int.gcd G (kernelOne D) : ℤ))

/-- Coefficients use the paper domain `n ≥ 2`. -/
def Admissible (f : ℕ →₀ ℤ) : Prop :=
  ∀ n ∈ f.support, 2 ≤ n

/-- The divisor channels `2, ..., D` vanish. -/
def LowChannels (D : ℕ) (f : ℕ →₀ ℤ) : Prop :=
  ∀ d ∈ Finset.Icc 2 D, channelNumerator f d = 0

/-- Exact attainable moments on the literal coefficient domain. -/
def AttainsMoment (D : ℕ) (m : ℤ) : Prop :=
  ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧ factorialMoment f = m

/-- No integer scalar `k ≥ 2` divides the whole coefficient vector. -/
def PrimitiveVector (f : ℕ →₀ ℤ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ¬ ∃ g : ℕ →₀ ℤ, f = (k : ℤ) • g

/-- Tail coordinates start at coordinate `D`. -/
def TailCoordinates (D : ℕ) (z : ℕ →₀ ℤ) : Prop :=
  ∀ j, j < D → z j = 0

noncomputable def fullResidualTerm (f : ℕ →₀ ℤ) (d : ℕ) : ℝ :=
  if 1 < d then (channelNumerator f d : ℝ) /
    ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) else 0

noncomputable def fullResidual (f : ℕ →₀ ℤ) : ℝ :=
  ∑' d : ℕ, fullResidualTerm f d

noncomputable def integerEvaluation (w : ℕ → ℤ) (z : ℕ →₀ ℤ) : ℤ :=
  z.sum (fun i c => c * w i)

noncomputable def coordinateMass (z : ℕ →₀ ℤ) : ℤ :=
  integerEvaluation (fun _ => 1) z

noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) else 0

noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d

noncomputable def factorialGapSeries : ℝ := factorialGapTail 1

noncomputable def gapPrefixReal (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 D, (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)

theorem exact_moment_ideal_with_primitive_attainment {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p ∧
    (∀ m : ℤ, AttainsMoment D m ↔ minimumMoment D p ∣ m) ∧
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ PrimitiveVector f :=
  ErdosProblems.Erdos68.PaperComplete.exact_moment_ideal_with_primitive_attainment
    hD hp hDp hpD

theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ) :=
  ErdosProblems.Erdos68.PaperComplete.residual_transparency hD t hz

end
end Erdos249257.ExternalVerification68MomentIdealResidual
