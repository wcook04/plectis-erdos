import ErdosProblems.Erdos257.SquarefreeSupportIncidence

/-!
Paper-form restatement of `prop:squarefree` (line 8519) of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

Clauses: for `A = {n ≥ 2 : n squarefree}` the engine coefficient is
`c_A(n) = 2^{ω(n)} − 1`; that value is odd at every `n ≥ 2`; and consequently
neither the digitwise nor the carry-aware divisibility-first block-certificate
schema has an instance at any even base.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open ErdosProblems.Erdos257

/-- Long `prop:squarefree`, every asserted clause.  `ω(n)` is
`n.primeFactors.card`, and the two schema hypotheses are quoted verbatim from
`Erdos249257.CertificateKernel`. -/
theorem paper_squarefree_support_engine_ceiling :
    (squarefreeSupport = {d : ℕ | 2 ≤ d ∧ Squarefree d}) ∧
      (∀ n : ℕ, n ≠ 0 →
        Erdos249257.supportCoeff squarefreeSupport n
          = 2 ^ n.primeFactors.card - 1) ∧
      (∀ n : ℕ, 2 ≤ n → Odd (Erdos249257.supportCoeff squarefreeSupport n)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
              Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (K - r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < Erdos249257.supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (∀ r ∈ Finset.Icc 1 K,
              b ^ r ∣ Erdos249257.supportCoeff squarefreeSupport (N + r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < Erdos249257.supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) := by
  refine ⟨rfl, ?_, ?_,
    fun _ hb hbeven => not_exists_carry_certificates_squarefreeSupport hb hbeven,
    fun _ hb hbeven => not_exists_digitwise_certificates_squarefreeSupport hb hbeven⟩
  · intro n hn
    rw [supportCoeff_squarefreeSupport n, squarefreeIncidence_eq hn]
  · intro n hn
    rw [supportCoeff_squarefreeSupport n]
    exact odd_squarefreeIncidence hn

#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_squarefree_support_engine_ceiling

end ErdosProblems.Erdos257.PaperCompleteR21
