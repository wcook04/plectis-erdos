#!/usr/bin/env python3
"""Surgical inserts into Erdos1041/research_packet.json for the 2026-09-06
Type B revision assimilation. Does not dump/reformat the whole packet.
"""
from __future__ import annotations

from pathlib import Path

PACKET = Path(__file__).resolve().parents[1] / "research_packet.json"

LAST_EXACT_CLOSE = '''   "claim_boundary": "Actual-polynomial theorem on the exact canonical Fourier phase with explicit size/deficit bounds. Continuous noncanonical phases, other deficit/cubic branches, arbitrary near-regular sextics, and unrestricted Erdos #1041 remain open."
  }
 ],
 "negative_results": ['''

NEW_EXACT = '''   "claim_boundary": "Actual-polynomial theorem on the exact canonical Fourier phase with explicit size/deficit bounds. Continuous noncanonical phases, other deficit/cubic branches, arbitrary near-regular sextics, and unrestricted Erdos #1041 remain open."
  },
  {
   "id": "sep_or_cubic_refutation_2026_09_06",
   "status": "ordinary_exact_refutation_with_lean_checked_rational_cores_not_a_parent_counterexample",
   "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/ExactObstructionsR2.md",
   "verifier": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_r2_revision_exact_cores.py",
   "certificate_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/RevisionR2ExactCores.lean",
   "statement": "SEP-OR is false. For f(z)=z^3+(3/100)z-3/4, Rouche on |z|=1 with 39/50<1 places every root in the open unit disc. The simple critical points are ±i/10 with values -3/4±i/500, so mu^2=9/16+1/250000>(13/25)^2 and mu>3/4. The values lie on distinct positive rays, and |1-v_-/v_+|=1/(250 mu)<2/375<2. Neither critical value is separated by two. The same strict margins persist under small coefficient perturbations. The example is a trinomial, so the parent path conclusion is already settled by trinomial_erdos1041_conclusion; the obstruction is to any covering programme that would settle mu>13/25 by critical-value separation two, or else first-merge arity, or else a capacity cutoff. Arity/capacity corollaries assume mu<=1/2 and cannot fill that residual.",
   "claim_boundary": "Ordinary exact refutation of a proposed covering disjunction, not of Erdos #1041. Rouche, distinct-ray, and perturbation persistence are ordinary; the displayed rational inequalities are Lean-checked in RevisionR2ExactCores.lean. SEP-OR never appeared as a live covering theorem in this packet; this row prevents it from being treated as one.",
   "named_consumers": [
    "erdos1041_all_degree_mu_13_25_2026_09_05",
    "unconditional_constant_factor_pair_geodesic",
    "disk_family_critical_value_separation_2026_09_02"
   ],
   "evidence_class": "ordinary_proof_plus_lean_checked_rational_cores",
   "source_current": true,
   "return_batch_id": "erdos_revision_packets_r2_20260906"
  },
  {
   "id": "one_root_gamma_perimeter_refutation_z8_2026_09_06",
   "status": "ordinary_exact_refutation_with_lean_checked_rational_cores_not_a_parent_counterexample",
   "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/ExactObstructionsR2.md",
   "verifier": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_r2_revision_exact_cores.py",
   "certificate_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/RevisionR2ExactCores.lean",
   "statement": "The one-root gamma perimeter bound H^1(partial C) <= Gamma(1/4)^2/(2 sqrt(pi)) cap({|f|<=sigma}) is false. For p(z)=z^8-(3/2)z the connected component C of {|p|<=1} containing zero contains exactly one zero (Rouche on |z|=4/5: 6/5-(4/5)^8>1), contains a neighbourhood of the closed disc of radius 5/8 (15/16+(5/8)^8<1), and therefore has H^1(partial C)>5 pi/4. The proposed constant is at most (pi/2)(1+sqrt(2)) by the secant bound, and sqrt(2)<3/2 gives (pi/2)(1+sqrt(2))<5 pi/4. A universal one-root constant, if one exists, must be at least 2 pi by the binomial family z^N-z. This is not a counterexample to Erdos #1041; the scaled binomial z^8-(3/256)z puts all roots in the open disc.",
   "claim_boundary": "Exact algebraic comparison, no floating gamma evaluation. The floating family z^n-z already killed the same bound in DegenerateHubBlaschkeReduction.md; this row supplies the first exact algebraic witness. Conjecture P in UnconditionalConstantFactorBound.md used this gamma constant as a one-root perimeter conjecture and is therefore false as stated. Conditional Theorem 3 there survives only with a larger beta, necessarily at least 2 pi.",
   "named_consumers": [
    "unconditional_constant_factor_pair_geodesic"
   ],
   "evidence_class": "ordinary_proof_plus_lean_checked_rational_cores",
   "source_current": true,
   "return_batch_id": "erdos_revision_packets_r2_20260906"
  },
  {
   "id": "first_merge_arity_does_not_force_capacity_gap_2026_09_06",
   "status": "ordinary_exact_refutation_with_lean_checked_rational_cores_not_a_parent_counterexample",
   "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/ExactObstructionsR2.md",
   "verifier": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_r2_revision_exact_cores.py",
   "certificate_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/RevisionR2ExactCores.lean",
   "statement": "First-merge arity does not force a capacity gap. For g(z)=z^3-(3/400)z-3/32 the critical points are ±1/20 with g(-1/20)=-187/2000 and g(1/20)=-47/500, so mu=187/2000<1/2 is a unique first-critical modulus. The first critical point is simple and g is squarefree. At T=2 mu both critical values lie strictly inside the value disc, so Riemann-Hurwitz gives a single component of {|g|<T}; for monic degree n one has cap(K_T)=T^{1/n}, hence the ancestor at 2 mu has normalised capacity kappa=1 while k_0=2. All roots lie in the open unit disc by Rouche: 3/400+3/32=81/800<1. Thus k_0=2 and kappa=1 can coexist under the corollaries' root and mu hypotheses. No estimate kappa<=tau_2<1 follows from low first-merge arity alone.",
   "claim_boundary": "Does not refute the arity/capacity corollaries of UnconditionalConstantFactorBound.md, which are implications kappa<=tau_{k_0} under mu<=1/2, not the converse. It refutes any covering reading that low first-merge arity forces a capacity defect, and it shows those corollaries cannot fill the residual mu>13/25.",
   "named_consumers": [
    "low_critical_high_arity_first_merge_closure",
    "unconditional_constant_factor_pair_geodesic",
    "erdos1041_all_degree_mu_13_25_2026_09_05"
   ],
   "evidence_class": "ordinary_proof_plus_lean_checked_rational_cores",
   "source_current": true,
   "return_batch_id": "erdos_revision_packets_r2_20260906"
'''

NEW_NEGS = [
    'SEP-OR is FALSE (2026-09-06). The cubic f(z)=z^3+(3/100)z-3/4 has all roots in the open unit disc, simple critical points, distinct critical-value rays, mu>3/4>13/25, and |1-v_-/v_+|<2/375<2. Neither critical value is separated by two. The example is a trinomial, so Erdos #1041 holds for it by the radial theorem; the obstruction is to any covering programme that would settle the residual mu>13/25 by separation-or-arity-or-capacity. Arity/capacity corollaries assume mu<=1/2. Ordinary proof: ExactObstructionsR2.md. Rational cores: check_erdos1041_r2_revision_exact_cores.py and RevisionR2ExactCores.lean.',
    'The one-root gamma perimeter bound H^1(partial C)<=Gamma(1/4)^2/(2 sqrt(pi)) cap({|f|<=sigma}) is FALSE (2026-09-06). For p(z)=z^8-(3/2)z the central one-root component of {|p|<=1} contains D_{5/8} and therefore has perimeter >5 pi/4, which already exceeds the secant upper bound (pi/2)(1+sqrt(2)) of the proposed constant. A degree-uniform one-root constant, if one exists, must be at least 2 pi by z^N-z. This is not a counterexample to Erdos #1041. The floating family in DegenerateHubBlaschkeReduction.md already killed the same bound; this is the first exact algebraic witness. Ordinary proof: ExactObstructionsR2.md.',
    'First-merge arity does not force a capacity gap (2026-09-06). The cubic g(z)=z^3-(3/400)z-3/32 has all roots in the open disc, mu=187/2000<1/2, unique first-critical modulus, k_0=2, and kappa=1 at level 2 mu. The arity/capacity corollaries remain valid as implications kappa<=tau_{k_0} under mu<=1/2; they are not a covering of mu>13/25, and low arity alone does not imply kappa<1. Ordinary proof: ExactObstructionsR2.md.',
]

ADDENDUM_KEY = "claim_ceiling_addendum_2026_09_06_r2_revision_assimilation"
ADDENDUM = (
    "Type B revision return of 2026-09-06: the all-degree monic trinomial theorem "
    "is already Lean-checked as trinomial_erdos1041_conclusion / "
    "abel_control_polygon_and_all_degree_trinomial_conclusion and is not re-registered; "
    "it is the cleanest proved all-degree connector that hits length <2 inside {|f|<1} "
    "for a complete coefficient family, so the paper now leads with it. Type B's artanh "
    "Bergman identity is Lemma A of BergmanSegmentLengthBound.md and is not re-registered; "
    "the proposed all-degree cutoff S=3/2 for the old coefficientwise first-merge bound is "
    "strictly weaker than disk_family_critical_value_separation_2026_09_02 (uniform S=4/3 "
    "for every n>=3, limiting cutoff coth 1). Three exact obstructions land as "
    "sep_or_cubic_refutation_2026_09_06, one_root_gamma_perimeter_refutation_z8_2026_09_06, "
    "and first_merge_arity_does_not_force_capacity_gap_2026_09_06. They kill covering "
    "readings of SEP-OR, the one-root gamma perimeter conjecture, and 'low first-merge "
    "arity forces a capacity gap'; they do not touch Erdos #1041. The 13/25 theorem is "
    "replayable from check_erdos1041_angular_budget_closure.py (duals generated at runtime; "
    "full-mode X_cert=635762889599/10^12); it is not blocked_external. Keep 71/10. FP5 is "
    "not claimed globally. Erdos #1041 remains open."
)


def main() -> int:
    text = PACKET.read_text()
    if "sep_or_cubic_refutation_2026_09_06" in text:
        print("already inserted")
        return 0

    old_x = "X_cert = 317881444799/500000000000 < 0.6357629"
    new_x = "X_cert = 635762889599/1000000000000 < 0.6357629"
    if old_x not in text:
        raise SystemExit("stale 13/25 X_cert not found")
    text = text.replace(old_x, new_x, 1)

    if LAST_EXACT_CLOSE not in text:
        raise SystemExit("exact_results close marker not found")
    text = text.replace(LAST_EXACT_CLOSE, NEW_EXACT + "\n  }\n ],\n \"negative_results\": [", 1)

    last_neg_close = (
        '  "The hub-Taylor criterion (A) is refuted as a completion route, and the good set is not a critical-scale disc (W3-C, 2026-09-05).'
    )
    idx = text.find(last_neg_close)
    if idx < 0:
        raise SystemExit("last negative_results row not found")
    close = text.find("\n ],\n \"finite_evidence\":", idx)
    if close < 0:
        raise SystemExit("negative_results array close not found")
    insert = ",\n  " + ",\n  ".join(f'"{s}"' for s in NEW_NEGS)
    text = text[:close] + insert + text[close:]

    end_marker = (
        'Not Lean checked or independently reviewed."\n}'
    )
    if not text.rstrip().endswith("}") or ADDENDUM_KEY in text:
        raise SystemExit("addendum insertion blocked")
    # last addendum currently ends the object
    needle = '"claim_ceiling_addendum_2026_09_05_sextic_canonical_phase_actual_transfer":'
    if needle not in text:
        raise SystemExit("last addendum key not found")
    if not text.endswith("\n"):
        text += "\n"
    if not text.rstrip().endswith("}"):
        raise SystemExit("packet does not end with }")
    # replace the final closing brace
    stripped = text.rstrip()
    if not stripped.endswith("}"):
        raise SystemExit("unexpected packet ending")
    add_json = f',\n "{ADDENDUM_KEY}": "{ADDENDUM}"\n}}\n'
    text = stripped[:-1].rstrip() + add_json
    PACKET.write_text(text)
    print("packet updated")
    print("exact_results insert ids: sep_or, one_root_gamma, first_merge_arity")
    print("negative_results +3")
    print("X_cert repaired")
    print(ADDENDUM_KEY)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
