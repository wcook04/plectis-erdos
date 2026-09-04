import Mathlib
import ErdosProblems.Erdos249.CyclotomicAnchoredKill

namespace Erdos249257.ExternalVerification249BinaryCyclotomicAnchors

open scoped BigOperators

noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs

def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (h : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (h * q) ∧ B < p

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) -
      (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

def CyclotomicAnchoredKillSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p L : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 ∧
      certifiedKill (h * q) (p - 1) L

theorem exists_clean_binaryCyclotomicAnchor
    (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ binaryCyclotomicLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 := by
  simpa [binaryCyclotomicLayer,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.exists_clean_binaryCyclotomicAnchor
      h N₀ hh

theorem binaryCyclotomicLayer_unboundedPrimeDivisorSupply
    (h : ℕ) (hh : 0 < h) :
    UnboundedPrimeDivisorSupply binaryCyclotomicLayer h := by
  simpa [UnboundedPrimeDivisorSupply, binaryCyclotomicLayer,
    ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer_unboundedPrimeDivisorSupply
      h hh

theorem binaryCyclotomicAnchoredKillSupply_iff_irrational :
    CyclotomicAnchoredKillSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [CyclotomicAnchoredKillSupply, certifiedKill, windowDiscrepancy,
    binaryCyclotomicLayer,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.CyclotomicAnchoredKillSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicAnchoredKillSupply_iff_irrational

theorem
    exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
    (hrat : ¬ Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧
      UnboundedPrimeDivisorSupply binaryCyclotomicLayer h ∧
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        totientTail (N + h) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ) := by
  simpa [UnboundedPrimeDivisorSupply, binaryCyclotomicLayer, totientTail,
    ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature.UnboundedPrimeDivisorSupply,
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.binaryCyclotomicLayer,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail] using
    ErdosProblems.Erdos249.CyclotomicAnchoredKill.exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
      hrat

end Erdos249257.ExternalVerification249BinaryCyclotomicAnchors
