import Erdos249257.LcmConeNonflat

/-! Finite-set interfaces with the manuscript's positive-index numerator.
The recovered non-flatness argument retains the asymmetric residue bound. -/
namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257.TotientTailPeriodKiller
open scoped BigOperators

def paperGridNumerator (H L q : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 L, Nat.totient (q * H + j) * 2 ^ (L - j)

theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L := by
  symm
  unfold paperGridNumerator windowNumerator
  apply Finset.sum_bij (fun j _ => j + 1)
  · intro j hj
    have := Finset.mem_range.mp hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro b hb
    obtain ⟨hb1, hbL⟩ := Finset.mem_Icc.mp hb
    exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    have ha : q * H + 1 + j = q * H + (j + 1) := by omega
    have he : L - 1 - j = L - (j + 1) := by omega
    rw [ha, he]

def paperGridCertificate (H L : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ qi ∈ Q, ∃ qj ∈ Q,
    (qj * H + L + 2 : ℤ) <
      ((paperGridNumerator H L qi : ℤ) - paperGridNumerator H L qj) % 2 ^ L

theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ) := by
  classical
  have hne : Q.toList ≠ [] := by simpa using hQ.ne_empty
  have hc : coneNonflatCert H L Q.toList := by
    simpa only [coneNonflatCert, paperGridCertificate, Finset.mem_toList,
      paperGridNumerator_eq] using hcert
  have hf : ∀ q ∈ Q.toList, (q * H + L + 2 : ℤ) < 2 ^ L := by simpa using hfloor
  simpa using exists_nonintegral_pair_of_coneNonflatCert hne hf hc

theorem finite_grid_supply_irrational
    (hs : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : Finset ℕ,
      Q.Nonempty ∧ (∀ q ∈ Q, 0 < q) ∧
      (∀ q ∈ Q, (q * periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      paperGridCertificate (periodLcm t) L Q) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  classical
  apply irrational_totient_series_of_lcm_cone_nonflat_supply
  intro t₀
  obtain ⟨t, ht, L, Q, hQ, hpos, hf, hc⟩ := hs t₀
  refine ⟨t, ht, L, Q.toList, ?_, ?_, ?_, ?_⟩
  · simpa using hQ.ne_empty
  · simpa using hpos
  · simpa using hf
  · simpa only [coneNonflatCert, paperGridCertificate, Finset.mem_toList,
      paperGridNumerator_eq] using hc

end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational
