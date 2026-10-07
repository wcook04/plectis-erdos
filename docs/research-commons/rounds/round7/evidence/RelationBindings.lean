-- Generated from exact relation-row predicates. No new mathematical claim.
import ErdosProblems.ArgumentGraph.Results.RelationCertificates

set_option autoImplicit false
noncomputable section
open ErdosProblems.ArgumentGraph.Contracts
open ErdosProblems.ArgumentGraph.RelationCertificates
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR7
open ErdosProblems.Erdos1049.PaperR10
open ErdosProblems.Erdos1049.PaperR11
open ErdosProblems.Erdos1049.PaperCompleteR21
open ErdosProblems.Erdos1041.PaperCompleteR21
open ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord

namespace PlectisRelationBinding

-- row-sha256: 77e9d15e8aa15c7d76f4bf6c551c1779a30ba4771cc5e2da29b89ffcee38121d
theorem binding_0 :
    Equivalent (fun _ : Unit => True) (fun _ => Irrational (∑' n : ℕ, ErdosProblems.Erdos251.primeDyadicTerm n)) (fun _ => Irrational (∑' n : ℕ, ErdosProblems.Erdos251.primeGapDyadicTerm n)) :=
  ErdosProblems.ArgumentGraph.RelationCertificates.prime_gap_view
#print axioms binding_0

-- row-sha256: d4eda7adbec6e7caed2a9f4d671acc00657241054e666a85a9081ad6b3438ee2
theorem binding_1 :
    Equivalent (fun ab : ℕ × ℕ => 0 < ab.2 ∧ ab.2 < ab.1) (fun ab => (ab.2 : ℝ) ^ zudilinMu < (ab.1 : ℝ)) (fun ab => ZudilinContourRegion ab.1 ab.2) :=
  ErdosProblems.ArgumentGraph.RelationCertificates.contour_view
#print axioms binding_1

-- row-sha256: 4daf85814c51924acf0ef34f4463e2cef891a8b76b8171e2ce3ef1935884204e
theorem binding_2 :
    Equivalent (fun _ : Unit => True) (fun _ => ErdosProblems.Erdos257.PaperCompleteR21.PaperResetSqrtEscape) (fun _ => ErdosProblems.Erdos257.PaperCompleteR21.SeamResetSqrtEscape) :=
  ErdosProblems.ArgumentGraph.RelationCertificates.square_view
#print axioms binding_2

-- row-sha256: 08b449cef48f24be182e4bb3aff9edcee9bd7dcd3cf4ab5c2e2b9f379c6efa29
theorem binding_3 :
    Equivalent (fun _ : Unit => True) (fun _ => DemandLedger.G102) (fun _ => Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :=
  ErdosProblems.ArgumentGraph.RelationCertificates.demand_G102_view
#print axioms binding_3

-- row-sha256: 0f917813725776c11b3c3ee1f2f6879e5ac70aa4032ef36c0aaa7697b792713b
theorem binding_4 :
    EndpointRoute (fun _ : Unit => True) (fun _ => ErdosProblems.ArgumentGraph.RelationCertificates.SupportGap) (fun _ => Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :=
  ErdosProblems.ArgumentGraph.RelationCertificates.support_gap_route
#print axioms binding_4

-- row-sha256: 326146a1488aa310206dea4312b0b3ec7fdc724be92fb9f77ae84f70d2d0876d
theorem binding_5 :
    EndpointRoute (fun _ : Unit => True) (fun _ => ErdosProblems.ArgumentGraph.RelationCertificates.GoodBaseGap) (fun _ => Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :=
  ErdosProblems.ArgumentGraph.RelationCertificates.good_base_gap_route
#print axioms binding_5

-- row-sha256: 95e53ed61354b8e04c0244ee96045a83c095221bd7efd82a8a342272489500d7
theorem binding_6 :
    Refuted (fun v : ℕ × ℝ × ℝ => 3 ≤ v.1 ∧ 0 < v.2.1 ∧ v.2.1 ^ v.1 < 1 ∧ ¬ 1 ≤ v.2.1 ^ v.1 * (1 + chordCos v.1 ^ v.1)) (fun v => innerRadius v.1 v.2.1 < v.2.2 ∧ v.2.2 ≤ v.2.1) :=
  ErdosProblems.ArgumentGraph.RelationCertificates.maximality_clause_refuted_off_switch
#print axioms binding_6

-- row-sha256: bbd6960163e3c7617c9015086511d1be86f47c5a983c34dc090d82a87889b355
theorem binding_7 :
    Feasible (fun _ : ℕ × ℝ × ℝ => True) (fun v => v.1 = 3 ∧ v.2.1 = 1 / 2 ∧ ¬ 1 ≤ v.2.1 ^ v.1 * (1 + chordCos v.1 ^ v.1)) :=
  ErdosProblems.ArgumentGraph.RelationCertificates.off_switch_region_feasible
#print axioms binding_7

end PlectisRelationBinding
