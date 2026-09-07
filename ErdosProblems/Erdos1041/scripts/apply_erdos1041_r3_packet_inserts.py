#!/usr/bin/env python3
"""Surgical inserts into Erdos1041/research_packet.json for the 2026-09-07
Type B revision assimilation. Does not dump/reformat the whole packet.
"""
from __future__ import annotations

from pathlib import Path

PACKET = Path(__file__).resolve().parents[1] / "research_packet.json"

LAST_EXACT_CLOSE = '''   "return_batch_id": "erdos_revision_packets_r2_20260906"

  }
 ],
 "negative_results": ['''

NEW_EXACT = '''   "return_batch_id": "erdos_revision_packets_r2_20260906"
  },
  {
   "id": "tied_minimum_two_root_window_refutation_2026_09_07",
   "status": "ordinary_exact_refutation_with_rational_cores_not_a_parent_counterexample",
   "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/TiedMinimumTwoRootWindow.md",
   "verifier": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_r2_revision_exact_cores.py",
   "statement": "A simple minimising critical point does not force a two-root persistence interval up to the next distinct critical-value modulus. For g(z)=z^4-(4/15)z^3-(4/25)z^2+1/750 the derivative is 4z(z+1/5)(z-2/5), all three critical points are simple, g(-1/5)=-1/750, g(0)=1/750, g(2/5)=-59/3750, so mu=1/750 is tied and the next distinct modulus is (59/5)mu. Rouche on |z|=1 with 107/250<1 places all four roots in the open unit disc; four distinct real roots lie in (-1,1) by sign changes. The first nontrivial component of K_mu already has degree three. Replacement hypotheses: unique global minimiser, an explicit degree-two window (mu,T*), or the registered disk-family two-sheeted component. Psi_n(x)=2 tends to coth 1, not to 1.",
   "claim_boundary": "Refutes a structural inference in MinimalHubWindowJoin.md Lemma 1 and the short-note theorem res:minimal-hub-window as previously worded. Does not refute Bergman Theorem C under an explicit two-root hypothesis, the disk-family theorem, or Erdos #1041. The witness itself has a real interval joining three roots inside K_mu.",
   "named_consumers": [
    "disk_family_critical_value_separation_2026_09_02",
    "unconditional_constant_factor_pair_geodesic"
   ],
   "evidence_class": "ordinary_proof_plus_exact_rational_cores",
   "source_current": true,
   "return_batch_id": "erdos_revision_packets_r3_20260907"
  },
  {
   "id": "collective_radial_window_constant_factor_2026_09_07",
   "status": "ordinary_analytic_theorem_with_exact_rational_coefficient_cores_not_lean_checked",
   "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/CollectiveRadialWindowBound.md",
   "verifier": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_r2_revision_exact_cores.py",
   "statement": "Averaging complete precritical inverse lifts (radial-mean lemma: mean complete radial length of a conformal map of the disc is at most sqrt(Area/pi), sharp for affine maps) and retaining all nontrivial components of K_sigma yields a path in K_t, sigma < t < T, of length at most sqrt(2/M(sigma)) T^{1/n} sqrt(2+(sqrt(log(T/mu))+pi/sqrt(log(T/sigma)))^2), where M(sigma) counts roots in all nontrivial components. Specialising to T=2mu for n>=4 gives coefficient C_*=2^{1/4} sqrt(2+log 2+2pi+pi^2/log 2) with C_*^2<(573/100)^2 by bounded artanh/Machin series. If mu>13/25 and N(3/5)>=14, equivalently M(3/5)>=15, the same bound at T=1 yields L^2<4 inside {|f|<1}. Degree two and three use the existing exact/cubic hub bounds.",
   "claim_boundary": "Ordinary analysis independently checked; rational cores in the r2/r3 exact-core checker. Does not replace unconditional_constant_factor_pair_geodesic in the short note: the inspectable lead constant remains 71/10 in K_{2mu}. Does not improve 13/25, does not prove the unrestricted constant 2, and is not Lean-checked. Coarea, Pólya, and Jordan-component identities remain ordinary.",
   "named_consumers": [
    "unconditional_constant_factor_pair_geodesic",
    "erdos1041_all_degree_mu_13_25_2026_09_05"
   ],
   "evidence_class": "ordinary_proof_plus_exact_rational_cores",
   "source_current": true,
   "return_batch_id": "erdos_revision_packets_r3_20260907"
  },
  {
   "id": "disk_family_all_centre_degree_uniform_radius_2026_09_07",
   "status": "ordinary_extracted_corollary_of_registered_disk_family_coefficient_not_a_new_bergman_estimate",
   "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/DiskFamilyCriticalValueSeparation.md",
   "verifier": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_r2_revision_exact_cores.py",
   "statement": "From the registered coefficient C(n,S,p)=(S/(n-1))^{2/n} log((S^2+S+p)/(S^2-S+p)), p=a(1-a), the logarithmic factor equals 2 iff S^2-A S+p=0 with A=coth 1. The larger root S_infty(a)=(A+sqrt(A^2-4a(1-a)))/2 is admissible and strictly below n-1, so C(n,S_infty(a),p)<2 for every finite n>=3. Endpoints S_infty(0)=S_infty(1)=coth 1 were already recorded. Failure of the test is forall a in [0,1], D(a)<=max(a,1-a) or C(n,D(a),a)>=2; the obstructing critical value may depend on the centre.",
   "claim_boundary": "Extracted from disk_family_critical_value_separation_2026_09_02. Not a new length estimate. The uniform 4/3 kernel remains the Lean-checked sufficient radius. The one-value lens residual is valid in degree three; with several other critical values the blocker is centre-dependent.",
   "named_consumers": [
    "disk_family_critical_value_separation_2026_09_02"
   ],
   "evidence_class": "ordinary_extracted_corollary_plus_exact_algebraic_identity",
   "source_current": true,
   "return_batch_id": "erdos_revision_packets_r3_20260907"
'''

NEW_NEGS = [
    "A simple minimising critical point does not force a two-root window up to the next distinct critical-value modulus (2026-09-07). The quartic g(z)=z^4-(4/15)z^3-(4/25)z^2+1/750 has three simple critical points, tied minima of modulus 1/750, all four roots in the open disc by Rouche 107/250<1, and first nontrivial component of degree three. Bergman Theorem C survives only under an explicit two-root or unique-minimiser hypothesis. Ordinary proof: TiedMinimumTwoRootWindow.md. Rational cores: check_erdos1041_r2_revision_exact_cores.py.",
]

ADDENDUM_KEY = "claim_ceiling_addendum_2026_09_07_r3_revision_assimilation"
ADDENDUM = (
    "Type B revision return of 2026-09-07: title and trinomial Theorem 1 kept; "
    "the complete trinomial proof now follows a short problem statement on the "
    "opening pages (history moved after the glance table; Type B 02_short_note_revised.tex "
    "was not pasted). Simple-minimum two-root-window inference is false "
    "(tied_minimum_two_root_window_refutation_2026_09_07); the short note and "
    "MinimalHubWindowJoin.md now require uniqueness or an explicit degree-two window, "
    "and Psi_n(x)=2 tends to coth 1. Newton connections preserve the ray of f(z) in "
    "the value plane. Complementary-binomial switching equality is closed containment. "
    "S_infty(a)=(A+sqrt(A^2-4a(1-a)))/2, A=coth 1, is extracted from the registered "
    "disk-family coefficient; the obstructing critical value may depend on the centre. "
    "Collective radial window and C_*<573/100 in the same K_{2mu} are independently "
    "checked ordinary mathematics (collective_radial_window_constant_factor_2026_09_07) "
    "and are not substituted for 71/10 in the short note. Keep 71/10 and 13/25. "
    "Sextic guardrail stays. FP5 is not claimed globally. Lambda lower-semicontinuous "
    "with Lambda(z^n-1)=2 is promoted as the closed-class remaining question; "
    "canonical-arc min L_f(c) is sufficient, not equivalent. Type B 13/25 checker "
    "replay is already resolved, not blocked_external. Disk-family S=4/3 remains "
    "strictly stronger than Type B r2 S=3/2. Erdos #1041 remains open."
)


def main() -> int:
    text = PACKET.read_text()
    if "tied_minimum_two_root_window_refutation_2026_09_07" in text:
        print("already inserted")
        return 0

    if LAST_EXACT_CLOSE not in text:
        raise SystemExit("exact_results close marker not found")
    text = text.replace(LAST_EXACT_CLOSE, NEW_EXACT + "\n  }\n ],\n \"negative_results\": [", 1)

    last_neg = (
        "First-merge arity does not force a capacity gap (2026-09-06). "
        "The cubic g(z)=z^3-(3/400)z-3/32 has all roots in the open disc, "
        "mu=187/2000<1/2, unique first-critical modulus, k_0=2, and kappa=1 "
        "at level 2 mu. The arity/capacity corollaries remain valid as "
        "implications kappa<=tau_{k_0} under mu<=1/2; they are not a covering "
        "of mu>13/25, and low arity alone does not imply kappa<1. Ordinary "
        "proof: ExactObstructionsR2.md."
    )
    idx = text.find(last_neg)
    if idx < 0:
        raise SystemExit("last r2 negative_results row not found")
    close = text.find("\n ],\n \"finite_evidence\":", idx)
    if close < 0:
        raise SystemExit("negative_results array close not found")
    insert = ",\n  " + ",\n  ".join(f'"{s}"' for s in NEW_NEGS)
    text = text[:close] + insert + text[close:]

    if ADDENDUM_KEY in text:
        raise SystemExit("addendum already present")
    stripped = text.rstrip()
    if not stripped.endswith("}"):
        raise SystemExit("unexpected packet ending")
    add_json = f',\n "{ADDENDUM_KEY}": "{ADDENDUM}"\n}}\n'
    text = stripped[:-1].rstrip() + add_json
    PACKET.write_text(text)
    print("packet updated")
    print("exact_results +3: tied_minimum, collective_window, S_infty")
    print("negative_results +1")
    print(ADDENDUM_KEY)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
