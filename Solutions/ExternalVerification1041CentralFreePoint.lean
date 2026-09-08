import ErdosProblems.Erdos1041.FreePointCentralCompletion

open scoped BigOperators ComplexConjugate

namespace Erdos249257.ExternalVerification1041CentralFreePoint

theorem central_free_point_mean {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ Real.sqrt (1 - Real.exp (-2))) :
    (∑ j, (∏ k, ‖1 - conj (c j) * c k‖) ^ ((m : ℝ)⁻¹)) ≤ (m : ℝ) := by
  exact ErdosProblems.Erdos1041.FreePointHilbertCertificate.geometric_row_mean_central_le hm c hc

end Erdos249257.ExternalVerification1041CentralFreePoint
