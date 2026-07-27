#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build semantic ownership zones for the audited ErdosProblems expansion.

The declaration atlas is exhaustive, but most declarations in these research
modules are proof substrate rather than separately reviewed public results.
This builder gives every declaration an explicit role while promoting only a
small set of exactly stated, scoped results to statement nodes.

The generated zone files are authored classification inputs to
``build_semantic_corpus.py``.  They do not replace the Lean declarations and do
not grant claim-registry status.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import build_off_diagonal_certificate_roster as off_diagonal_roster

ROOT = Path(__file__).resolve().parent.parent
ATLAS = ROOT / "docs" / "declaration_atlas.json"
ZONES = ROOT / "docs" / "semantic" / "zones"

COMMON_CONCEPT = {
    "id": "audited_expansion_boundary",
    "label": "audited expansion claim boundary",
    "note": (
        "A distinction between an exact Lean declaration, supporting proof "
        "substrate, finite checked instances, measurements, and any claim that "
        "would resolve an open Erdős problem."
    ),
}


def current_off_diagonal_roster() -> dict[str, Any]:
    """Load the generated roster only when it matches its data and Lean inputs."""
    expected = off_diagonal_roster.render_roster(
        off_diagonal_roster.build_roster()
    )
    path = off_diagonal_roster.OUTPUT
    if not path.is_file() or path.read_text(encoding="utf-8") != expected:
        raise RuntimeError(
            "off-diagonal certificate roster is missing or stale; run "
            "python3 scripts/build_off_diagonal_certificate_roster.py --write"
        )
    return json.loads(expected)


OFF_DIAGONAL_ROSTER = current_off_diagonal_roster()


def node(
    node_id: str,
    statement: str,
    logical_class: str,
    problem: str,
    evidence: list[tuple[str, str]],
    engine: str,
    scope_caveat: str,
    open_antecedents: list[str] | None = None,
) -> dict[str, Any]:
    return {
        "id": node_id,
        "canonical_statement": statement,
        "logical_class": logical_class,
        "problem": problem,
        "evidence_refs": evidence,
        "concepts": ["audited_expansion_boundary"],
        "open_antecedents": open_antecedents or [],
        "is_restatement_of_open_problem": False,
        "engine": engine,
        "prior_art_state": "not_assessed",
        "prior_art_note": (
            "No priority or novelty claim is made. This node records the exact "
            "scope needed for public claim hygiene."
        ),
        "scope_caveat": scope_caveat,
        "confidence": "high",
    }


SPECS: list[dict[str, Any]] = [
    {
        "zone_id": "Z19",
        "title": "Lift and reconstruction experiments with explicit hypothesis boundaries",
        "problem": "both",
        "prefix": "ErdosProblems/Lift/",
        "nodes": [
            node(
                "angle_b2_conditional_contradiction",
                (
                    "PROVED: allRight_landingExcess_two_impossible derives False "
                    "only from its displayed all-right, landing-excess-two, and "
                    "three-row cofactor-support hypotheses. It does not state that "
                    "a survivor set is empty."
                ),
                "conditional_implication",
                "257",
                [
                    (
                        "ErdosProblems/Lift/AngleB2.lean",
                        "allRight_landingExcess_two_impossible",
                    )
                ],
                "finite seam-word and cofactor-support calculation",
                (
                    "The audit found the cofactor-support hypothesis false at "
                    "D = 101, 122, 164, 314, 545, 629, and 1112, and found no "
                    "observed landing seam excess equal to two in s = 5..102. "
                    "Those observations are audit evidence, not additional Lean theorems."
                ),
                [
                    "hright: the seam word extends right at every row from D+1 onward",
                    "hlanding: Recon257.seamExcess (D+1) = 2",
                    "hcof: the required cofactor ranks lie in the seam-word support on rows D+1 through D+3",
                ],
            ),
            node(
                "angle_b3_large_offset_nonrecurrence",
                (
                    "PROVED: for a pulse sequence bounded above by Q, a ratchet "
                    "orbit starting at b₀ at least Q+2 cannot return to its initial "
                    "value at a positive time."
                ),
                "conditional_implication",
                "257",
                [
                    (
                        "ErdosProblems/Lift/AngleB3.lean",
                        "ratchetOrbit_no_recurrence",
                    ),
                    (
                        "ErdosProblems/Lift/AngleB3.lean",
                        "ratchetOrbit_pulseFloor_eq_recon257_ratchetRun",
                    ),
                ],
                "monotone lower bound for the imported Recon257 ratchet",
                (
                    "The theorem applies only in the large-offset region b₀ ≥ Q+2. "
                    "It does not cover the live offsets 1 through 9. The separate "
                    "universal-barrier theorem has an unsatisfied initial hypothesis "
                    "for the concrete use discussed in the audit."
                ),
                [
                    "hQ: P s ≤ Q for every row s",
                    "hb: Q+2 ≤ b₀",
                ],
            ),
        ],
    },
    {
        "zone_id": "Z20",
        "title": "Skip and wire calculations with vacuity recorded",
        "problem": "257",
        "prefix": "ErdosProblems/Skip/",
        # Z02 owns this current #249 headline as a statement. Without an
        # exclusion, the broad Skip prefix would overwrite it as Z20 substrate.
        "role_exclusions": {
            (
                "ErdosProblems/Skip/LadderT67.lean",
                "exists_diagonalKill_le_82",
            )
        },
        "nodes": [
            node(
                "skip_existential_bound_conditional",
                (
                    "PROVED: exists_bound_allRight_landingExcess_two_impossible "
                    "states an existential threshold after which an all-right tail "
                    "together with landing seam excess two gives a contradiction."
                ),
                "conditional_implication",
                "257",
                [
                    (
                        "ErdosProblems/Skip/D1.lean",
                        "exists_bound_allRight_landingExcess_two_impossible",
                    )
                ],
                "finite residue-period bound and earlier conditional contradiction",
                (
                    "The audit found that the exhibited bound exceeds every D "
                    "admitted by the theorem's own finite hypotheses, while the "
                    "all-right alternative restates the unresolved achievement-set "
                    "condition and landing seam excess two was not observed. No "
                    "residue class is excluded by this headline theorem."
                ),
                [
                    "hright: the seam word extends right at every row from D+1 onward",
                    "hlanding: Recon257.seamExcess (D+1) = 2",
                ],
            ),
        ],
    },
    {
        "zone_id": "Z21",
        "title": "Half-zone identities and finite free-walk obstructions",
        "problem": "257",
        "prefix": "ErdosProblems/Half/",
        "nodes": [
            node(
                "prime_seam_excess_not_two",
                (
                    "PROVED: at a prime row s at least 13, seamExcess s is not two."
                ),
                "unconditional_object_theorem",
                "257",
                [
                    (
                        "ErdosProblems/Half/H3.lean",
                        "seamExcess_ne_two_of_prime",
                    )
                ],
                "parity of the prime-row greedy remainder",
                (
                    "This is a rowwise prime statement. It does not provide a "
                    "cofinal hit supply or resolve membership of one half."
                ),
            ),
            node(
                "free_walk_no_small_absolute_bound",
                (
                    "PROVED: the tested FreeWalk2 formulation has no absolute run "
                    "bound at most twelve."
                ),
                "barrier_no_go",
                "249",
                [
                    (
                        "ErdosProblems/Half/FreeWalk2.lean",
                        "no_small_absolute_run_bound",
                    )
                ],
                "explicit finite counterexamples to each proposed bound",
                (
                    "Only bounds at most twelve are excluded. This is not an "
                    "asymptotic theorem and says nothing about a larger or "
                    "parameter-dependent bound."
                ),
            ),
        ],
    },
    {
        "zone_id": "Z22",
        "title": "Bit-level remainder identities and scoped bad-run implication",
        "problem": "257",
        "prefix": "ErdosProblems/Bit/",
        "nodes": [
            node(
                "bad_run_pins_remainder_conditional",
                (
                    "PROVED: badRun_pins_remainder pins the row-N remainder to a "
                    "short interval when every row from N+1 through 3N+2 is bad "
                    "and the terminal ceiling hypothesis holds."
                ),
                "conditional_implication",
                "257",
                [("ErdosProblems/Bit/R2.lean", "badRun_pins_remainder")],
                "iteration of the bit-level bad-row recurrence",
                (
                    "The premise needs at least twelve consecutive bad rows in the "
                    "relevant range; the audit found a maximum run of three in the "
                    "measured data. The theorem therefore supplies no observed case."
                ),
                [
                    "hbad: every row from N+1 through 3N+2 fails LargestSkipLateAt",
                    "hceil: ObeysRemainderCeiling (3N+2)",
                ],
            )
        ],
    },
    {
        "zone_id": "Z23",
        "title": "Remainder recurrences, bounded measurements, and their limits",
        "problem": "257",
        "prefix": "ErdosProblems/Rem/",
        "nodes": [
            node(
                "bounded_hit_gap_reduction",
                (
                    "PROVED: a uniform bound on gaps between hit rows implies that "
                    "one half belongs to the Mersenne achievement set."
                ),
                "conditional_implication",
                "257",
                [
                    (
                        "ErdosProblems/Rem/C3.lean",
                        "half_mem_of_hitGapBoundedBy",
                    )
                ],
                "transport from bounded hit gaps to cofinal half-point remainders",
                (
                    "The bounded-gap premise is not proved. The same file proves "
                    "that the proposed bound eight is false."
                ),
                [
                    "h: HitGapBoundedBy K for some fixed natural number K",
                ],
            ),
            node(
                "residual_invariant_refuted",
                (
                    "PROVED: the predicate ResidualInvariant introduced for the "
                    "remainder programme is false."
                ),
                "barrier_no_go",
                "257",
                [("ErdosProblems/Three/T1.lean", "not_residualInvariant")],
                "explicit counterexample at s = 13 and d = 7",
                (
                    "This refutes that invariant only. It does not refute every "
                    "possible remainder invariant and does not resolve #257."
                ),
            ),
        ],
    },
    {
        "zone_id": "Z24",
        "title": "Three-branch recurrence and exact counterexamples",
        "problem": "257",
        "prefix": "ErdosProblems/Three/",
        "nodes": [
            node(
                "residual_invariant_counterexample",
                "PROVED: ResidualInvariant is false, with the failure witnessed at s = 13 and d = 7.",
                "barrier_no_go",
                "257",
                [("ErdosProblems/Three/T1.lean", "not_residualInvariant")],
                "kernel evaluation of the exact finite row",
                (
                    "The counterexample invalidates the universal invariant. It "
                    "does not imply that no corrected invariant can exist."
                ),
            ),
            node(
                "perturbed_doubling_recurrence",
                (
                    "PROVED: the successor remainder obeys an exact perturbed "
                    "doubling identity with explicitly bounded carry and error terms; "
                    "under no successor carry, the sharper bounds n ≤ 1 and E ≤ 2s hold."
                ),
                "unconditional_object_theorem",
                "257",
                [
                    (
                        "ErdosProblems/Three/T2.lean",
                        "remainder_succ_perturbed_doubling",
                    ),
                    (
                        "ErdosProblems/Three/T2.lean",
                        "remainder_succ_perturbed_doubling_of_not_carry",
                    ),
                ],
                "exact three-branch decomposition of the successor row",
                (
                    "This proves the branch that Rem/C3 had originally recorded "
                    "only as measured. The resulting global carry hypotheses remain open."
                ),
            ),
        ],
    },
    {
        "zone_id": "Z25",
        "title": "Declared correction predicates and the seven-five counterexample",
        "problem": "257",
        "prefix": "ErdosProblems/Decl/",
        "nodes": [
            node(
                "hlow_false_at_seven_five",
                (
                    "PROVED: the proposed low-correction inequality fails at "
                    "s = 7 and d = 5."
                ),
                "barrier_no_go",
                "257",
                [("ErdosProblems/Decl/D4.lean", "not_hlow_seven_five")],
                "exact evaluation of lateCorrection and the late-entry remainder",
                (
                    "This is a counterexample to the universal hlow side condition. "
                    "It is not an obstruction to a hit; row seven is itself a hit."
                ),
            )
        ],
    },
    {
        "zone_id": "Z26",
        "title": "Failure of the hlow condition and conversion to hit certificates",
        "problem": "257",
        "prefix": "ErdosProblems/Hlow/",
        "nodes": [
            node(
                "universal_hlow_refuted",
                (
                    "PROVED: the universal hlow implication, even with its hhigh "
                    "premise, is false."
                ),
                "barrier_no_go",
                "257",
                [("ErdosProblems/Hlow/H1.lean", "not_hlow_of_hhigh")],
                "the explicit seven-five counterexample",
                (
                    "This closes the proposed universal side condition, not the "
                    "achievement-set problem."
                ),
            ),
            node(
                "hlow_failure_gives_hit",
                (
                    "PROVED: under BitAdmissible, failure of hlow forces the seam "
                    "remainder below 2^s; in particular the seven-five failure "
                    "certifies that row seven is a hit."
                ),
                "conditional_implication",
                "257",
                [
                    (
                        "ErdosProblems/Hlow/H2.lean",
                        "seamRemainder_lt_two_pow_of_not_hlow",
                    ),
                    (
                        "ErdosProblems/Hlow/H2.lean",
                        "seven_is_a_hit_from_failure",
                    ),
                ],
                "correction decomposition of the greedy remainder",
                (
                    "A single hit or conditional hit conversion does not prove "
                    "the cofinal supply required for membership of one half."
                ),
                [
                    "h: BitAdmissible s d",
                    "hfail: the hlow inequality fails at s,d",
                ],
            ),
        ],
    },
    {
        "zone_id": "Z27",
        "title": "Finite off-diagonal certified kills at explicit positions",
        "problem": "249",
        "prefix": "ErdosProblems/FreePosition/",
        "nodes": [
            node(
                "free_position_finite_certificates",
                off_diagonal_roster.public_projection_statement(
                    OFF_DIAGONAL_ROSTER
                ),
                "finite_instance",
                "249",
                [
                    (
                        "ErdosProblems/FreePosition/FreeKill64OneHundredFifteenDI.lean",
                        "freeKill_64OneHundredFifteenDI",
                    )
                ],
                "explicit factorisations, primality certificates, and modular arithmetic",
                off_diagonal_roster.public_projection_scope_caveat(
                    OFF_DIAGONAL_ROSTER
                ),
            )
        ],
        "role_prefix": ("freeKill", "finite_instance", "free_position_finite_certificates"),
    },
]


def main() -> int:
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    by_module_name = {
        (row["module"], row["name"]): row for row in atlas["declarations"]
    }

    for spec in SPECS:
        exclusions = set(spec.get("role_exclusions", set()))
        missing_exclusions = exclusions - set(by_module_name)
        if missing_exclusions:
            raise SystemExit(
                f"{spec['zone_id']}: role exclusions absent from atlas: "
                f"{sorted(missing_exclusions)}"
            )
        promoted: dict[tuple[str, str], str] = {}
        rendered_nodes: list[dict[str, Any]] = []
        for authored in spec["nodes"]:
            current = dict(authored)
            evidence = []
            for module, declaration in current.pop("evidence_refs"):
                row = by_module_name.get((module, declaration))
                if row is None:
                    raise SystemExit(
                        f"{spec['zone_id']}: evidence declaration absent: "
                        f"{module}::{declaration}"
                    )
                evidence.append(
                    {
                        "declaration": declaration,
                        "module": module,
                        "line": row["line"],
                    }
                )
                if module.startswith(spec["prefix"]):
                    promoted[(module, declaration)] = current["id"]
            current["evidence"] = evidence
            rendered_nodes.append(current)

        roles = []
        for row in atlas["declarations"]:
            if not row["module"].startswith(spec["prefix"]):
                continue
            if (row["module"], row["name"]) in exclusions:
                continue
            role: dict[str, Any] = {
                "declaration": row["name"],
                "module": row["module"],
                "line": row["line"],
                "role": "substrate",
            }
            target = promoted.get((row["module"], row["name"]))
            if target is not None:
                role["role"] = "statement"
                role["statement_node"] = target
            prefix_rule = spec.get("role_prefix")
            if prefix_rule and row["name"].startswith(prefix_rule[0]):
                role["role"] = prefix_rule[1]
                role["statement_node"] = prefix_rule[2]
            roles.append(role)

        payload = {
            "zone_id": spec["zone_id"],
            "title": spec["title"],
            "problem": spec["problem"],
            "concepts": [COMMON_CONCEPT],
            "statement_nodes": rendered_nodes,
            "declaration_roles": roles,
            "intra_zone_relations": [],
        }
        destination = ZONES / f"{spec['zone_id']}.json"
        destination.write_text(
            json.dumps(payload, ensure_ascii=False, indent=1) + "\n",
            encoding="utf-8",
        )
        print(
            f"wrote {destination.relative_to(ROOT)}: "
            f"{len(rendered_nodes)} statement node(s), {len(roles)} role(s)"
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
