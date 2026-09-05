#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused contract tests for the generated Comparator replay candidate."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path
from unittest import mock

import build_comparator_replay_portfolio as replay


def test_live_portfolio_is_complete_unique_and_current() -> None:
    first = replay.build_portfolio()
    second = replay.build_portfolio()
    assert first == second
    assert first.assurance_status == "replay_candidate"
    assert first.packages
    assert first.theorem_names
    assert len(set(first.theorem_names)) == len(first.theorem_names)
    assert "ExternalVerification" not in {package.name for package in first.packages}
    assert set(replay.required_package_ids()) <= {
        package.name for package in first.packages
    }
    required_interfaces = replay.required_interfaces_by_package()
    assert set(required_interfaces) == {package.name for package in first.packages}
    assert sum(map(len, required_interfaces.values())) == len(first.theorem_names)
    legacy = first.legacy_package_record_assimilation
    assert legacy is not None
    assert legacy["source_snapshot"]["record_count"] == 21
    assert legacy["source_snapshot"]["comparator_interface_count"] == 86
    assert len(legacy["package_records"]) == 21
    assert sum(
        len(row["legacy_theorem_names"])
        for row in legacy["package_records"]
    ) == 86
    coverage = first.result_family_coverage
    families = coverage["families"]
    assert coverage["registered_family_count"] == len(families)
    assert coverage["classified_family_count"] == len(families)
    assert sum(coverage["execution_classification_counts"].values()) == len(families)
    assert {
        (row["problem"], row["family_id"])
        for row in families
    } == {
        (int(problem_row["problem"]), family["id"])
        for problem_row in json.loads(
            (replay.ROOT / "docs" / "claims.json").read_text(encoding="utf-8")
        )["external_verification_packet"]["review_matrix"]
        for family in problem_row["families"]
    }
    assert all(
        row["packages"] and row["non_executable_reason"] is None
        if row["execution_classification"] == "has_executable_challenge_package"
        else not row["packages"]
        and row["registry_comparator_disposition"] in row["non_executable_reason"]
        for row in families
    )
    assert (
        "Erdos249257.ExternalVerification1041SolvedFamilies."
        "SharpCollinear.existsPeakLeComparisonBound"
    ) in first.theorem_names

    outputs = replay.expected_outputs(first)
    assert outputs == replay.expected_outputs(second)
    for path, expected in outputs.items():
        assert path.read_text(encoding="utf-8") == expected


def test_config_is_comparator_native_and_explicitly_non_nanoda() -> None:
    portfolio = replay.build_portfolio()
    payload = json.loads(replay.render_config(portfolio))
    assert payload == {
        "challenge_module": "ComparatorReplay.Challenge",
        "solution_module": "ComparatorReplay.Solution",
        "theorem_names": list(portfolio.theorem_names),
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": False,
    }


def test_palomar_catalog_preserves_existing_owner_and_current_eligibility() -> None:
    portfolio = replay.build_portfolio()
    generated, rendered_catalog = replay.palomar_entry_outputs(portfolio)
    catalog = json.loads(rendered_catalog)
    assert catalog["package_count"] == len(portfolio.packages)
    assert catalog["interface_count"] == len(portfolio.theorem_names)
    assert catalog["entry_ready_for_replay_count"] == len(portfolio.packages)
    assert catalog["blocked_package_ids"] == []
    assert catalog["source_bound_package_match_count"] == sum(
        bool(row["source_bound_matches"]) for row in catalog["entries"]
    )
    existing_owner_count = sum(
        row["config_authority"] == "existing_package_owner_preserved"
        for row in catalog["entries"]
    )
    assert len(generated) == len(portfolio.packages) - existing_owner_count

    by_package = {row["package_id"]: row for row in catalog["entries"]}
    solved = by_package["ExternalVerification1041SolvedFamilies"]
    assert solved["config_path"] == (
        "ExternalVerification1041SolvedFamilies/comparator.json"
    )
    assert solved["config_authority"] == "existing_package_owner_preserved"
    assert replay.ROOT / solved["config_path"] not in generated
    existing = json.loads(
        (replay.ROOT / solved["config_path"]).read_text(encoding="utf-8")
    )
    assert existing["enable_nanoda"] is True

    repaired = by_package["ExternalVerification1049"]
    assert repaired["palomar_trusted_challenge"] == {
        "status": "structurally_eligible_pending_replay",
        "disallowed_imports": [],
    }
    generated_repaired = json.loads(
        generated[replay.ROOT / repaired["config_path"]]
    )
    assert generated_repaired["theorem_names"] == repaired["theorem_names"]
    assert generated_repaired["enable_nanoda"] is False
    flagship = by_package["ExternalVerification257ReciprocalSupport"]
    assert flagship["source_bound_matches"] == [
        {
            "claim_id": "reciprocal_summable_support",
            "review_family": "reciprocal_summable_support",
            "package_id": "ExternalVerification257ReciprocalSupport",
            "interface_name": (
                "Erdos249257.ExternalVerification257ReciprocalSupport."
                "irrational_supportPowerSeries_of_summable_reciprocal"
            ),
            "source_module": "Erdos249257/AllBaseReciprocalSupportIrrationality.lean",
            "source_declaration": (
                "Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal"
            ),
            "evidence": (
                "claim anchor + main-result source link + exact Solution import/use; "
                "Comparator execution not asserted"
            ),
        }
    ]
    assert all(row["execution_status"] == "not_run_not_asserted" for row in catalog["entries"])
    assert "not a Comparator receipt" in catalog["boundary"]


def test_palomar_disposition_rejects_synthetic_project_local_import() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        package_dir = root / "ExternalVerificationFixture"
        package_dir.mkdir()
        (package_dir / "Challenge.lean").write_text(
            "import ExternalVerificationFixture.Statements\n",
            encoding="utf-8",
        )
        package = replay.Package(
            name="ExternalVerificationFixture",
            challenge_module="ExternalVerificationFixture.Challenge",
            solution_module="ExternalVerificationFixture.Solution",
            theorem_names=("Fixture.result",),
        )
        assert replay.palomar_challenge_disposition(package, root) == {
            "status": "blocked_project_local_challenge_import",
            "disallowed_imports": ["ExternalVerificationFixture.Statements"],
        }


def test_namespace_survives_nested_section_end() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        path = Path(temporary) / "Challenge.lean"
        path.write_text(
            "namespace Outer\n"
            "section Inner\n"
            "theorem first : True := by trivial\n"
            "end Inner\n"
            "theorem second : True := by trivial\n"
            "end Outer\n",
            encoding="utf-8",
        )
        assert replay.declarations_in(path) == (
            "Outer.first",
            "Outer.second",
        )


def test_same_line_attributes_do_not_hide_interfaces() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        path = Path(temporary) / "Challenge.lean"
        path.write_text(
            "namespace Outer\n"
            "@[simp] theorem attributed : True := by trivial\n"
            "@[simp, aesop safe apply] protected lemma qualified : True := by trivial\n"
            "end Outer\n",
            encoding="utf-8",
        )
        assert replay.declarations_in(path) == (
            "Outer.attributed",
            "Outer.qualified",
        )


def _write_fixture_package(root: Path, *, challenge_import: str, solution_body: str) -> None:
    (root / "lakefile.toml").write_text(
        'name = "fixture"\n\n[[lean_lib]]\nname = "ExternalVerificationFixture"\n',
        encoding="utf-8",
    )
    package = root / "ExternalVerificationFixture"
    package.mkdir()
    membership = root / "verification"
    membership.mkdir()
    (membership / "comparator.json").write_text(
        json.dumps(
            {
                "challenge_module": "ExternalVerification.Challenge",
                "solution_module": "ExternalVerification.Solution",
                "theorem_names": ["Fixture.interface"],
                "permitted_axioms": list(replay.PERMITTED_AXIOMS),
                "enable_nanoda": False,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (membership / "comparator-replay-membership.json").write_text(
        json.dumps(
            {
                "schema": "plectis.comparator-replay-membership/1",
                "required_package_ids": ["ExternalVerificationFixture"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    docs = root / "docs"
    docs.mkdir()
    (docs / "claims.json").write_text(
        json.dumps(
            {
                "claims": [
                    {
                        "id": "fixture_claim",
                        "status": "proved here",
                        "statement": "The fixture source theorem holds.",
                        "declarations": [
                            {
                                "name": "sourceTheorem",
                                "module": "FixtureSource.lean",
                                "line": 1,
                            }
                        ],
                    },
                    {
                        "id": "fixture_open",
                        "status": "open",
                        "statement": "The fixture open problem remains open.",
                        "declarations": [],
                    },
                    {
                        "id": "fixture_citation",
                        "status": "cited only",
                        "statement": "A cited fixture result.",
                        "declarations": [],
                    },
                ],
                "external_verification_packet": {
                    "review_matrix": [
                        {
                            "problem": 1,
                            "families": [
                                {
                                    "id": "fixture_family",
                                    "declarations": ["Fixture.interface"],
                                    "comparator_disposition": "targeted",
                                }
                            ],
                        }
                    ],
                    "main_results": [
                        {
                            "id": "fixture_result",
                            "problem": 1,
                            "review_family": "fixture_family",
                            "original_declaration": "Fixture.interface",
                            "wrapper_declaration": "Fixture.interface",
                            "statement": "Fixture statement.",
                            "boundary": "Fixture boundary.",
                        }
                    ],
                }
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (package / "Challenge.lean").write_text(
        f"import {challenge_import}\n"
        "namespace Fixture\n"
        "theorem interface : True := by\n"
        "  sorry\n"
        "end Fixture\n",
        encoding="utf-8",
    )
    (package / "Solution.lean").write_text(
        "import Mathlib\n"
        "namespace Fixture\n"
        "theorem interface : True := by\n"
        f"  {solution_body}\n"
        "end Fixture\n",
        encoding="utf-8",
    )


def _expect_portfolio_error(root: Path, fragment: str) -> None:
    try:
        replay.build_portfolio(root)
    except replay.PortfolioError as exc:
        assert fragment in str(exc), str(exc)
    else:
        raise AssertionError(f"expected PortfolioError containing {fragment!r}")


def test_rejects_project_local_challenge_import() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(
            root,
            challenge_import="ErdosProblems.Secret",
            solution_body="trivial",
        )
        _expect_portfolio_error(root, "project-local module")


def test_fixture_membership_projection_does_not_read_live_root() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(
            root,
            challenge_import="Mathlib",
            solution_body="trivial",
        )
        portfolio = replay.build_portfolio(root)
        membership = json.loads(replay.render_membership(portfolio))
        assert membership["required_package_ids"] == ["ExternalVerificationFixture"]
        coverage = membership["registered_claim_coverage"]
        assert coverage["registered_claim_count"] == 3
        assert coverage["classification_counts"] == {
            "cited_only_non_executable": 1,
            "missing_formal_transport": 1,
            "open_non_executable": 1,
        }
        assert coverage["missing_formal_claim_ids"] == ["fixture_claim"]
        assert coverage["complete_formal_transport_coverage"] is False


def test_explicit_claim_transport_requires_exact_anchor_and_real_interface() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(
            root,
            challenge_import="Mathlib",
            solution_body="trivial",
        )
        claims_path = root / "docs" / "claims.json"
        claims = json.loads(claims_path.read_text(encoding="utf-8"))
        claim = claims["claims"][0]
        anchor = claim["declarations"][0]
        claim["comparator_transports"] = [
            {
                "package_id": "ExternalVerificationFixture",
                "interface_name": "Fixture.interface",
                "source_declarations": [anchor],
            }
        ]
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")

        portfolio = replay.build_portfolio(root)
        coverage = portfolio.registered_claim_coverage
        row = next(row for row in coverage["claims"] if row["claim_id"] == "fixture_claim")
        assert row["classification"] == "linked_transport"
        assert row["semantic_coverage_status"] == "not_assessed_by_transport_link"
        assert row["executed_comparator_assurance"] == "not_asserted"
        assert row["transports"][0]["source_declarations"] == [anchor]
        assert coverage["complete_formal_transport_coverage"] is True
        first_digest = coverage["registry_digest"]

        claim["statement"] = "The revised fixture source theorem holds."
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")
        assert (
            replay.build_portfolio(root).registered_claim_coverage["registry_digest"]
            != first_digest
        )

        claim["comparator_transports"][0]["source_declarations"] = [
            {**anchor, "line": 2}
        ]
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")
        _expect_portfolio_error(root, "unregistered source anchor")

        claim["comparator_transports"][0]["source_declarations"] = [anchor]
        claim["comparator_transports"][0]["interface_name"] = "Fixture.absent"
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")
        _expect_portfolio_error(root, "absent Comparator package/interface")


def test_main_result_claim_id_links_exact_source_without_claiming_semantics() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(root, challenge_import="Mathlib", solution_body="trivial")
        claims_path = root / "docs" / "claims.json"
        claims = json.loads(claims_path.read_text(encoding="utf-8"))
        result = claims["external_verification_packet"]["main_results"][0]
        result.update(
            {
                "claim_id": "fixture_claim",
                "original_source": "FixtureSource.lean",
                "original_declaration": "Fixture.sourceTheorem",
            }
        )
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")

        coverage = replay.build_portfolio(root).registered_claim_coverage
        row = next(row for row in coverage["claims"] if row["claim_id"] == "fixture_claim")
        assert row["classification"] == "linked_transport"
        assert row["transports"][0]["link_sources"] == ["main_result_claim_id"]
        assert row["semantic_coverage_status"] == "not_assessed_by_transport_link"

        result["original_source"] = "WrongSource.lean"
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")
        _expect_portfolio_error(root, "lacks one exact registered source anchor")


def test_complete_claim_requirement_is_opt_in_and_read_only() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(root, challenge_import="Mathlib", solution_body="trivial")
        incomplete = replay.build_portfolio(root)
        with mock.patch.object(
            replay, "build_portfolio", return_value=incomplete
        ), mock.patch.object(replay, "expected_outputs", return_value={}):
            assert replay.main(["--check"]) == 0
            assert replay.main(["--require-complete-claims"]) == 1

        claims_path = root / "docs" / "claims.json"
        claims = json.loads(claims_path.read_text(encoding="utf-8"))
        anchor = claims["claims"][0]["declarations"][0]
        claims["claims"][0]["comparator_transports"] = [
            {
                "package_id": "ExternalVerificationFixture",
                "interface_name": "Fixture.interface",
                "source_declarations": [anchor],
            }
        ]
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")
        complete = replay.build_portfolio(root)
        with mock.patch.object(replay, "build_portfolio", return_value=complete), mock.patch.object(
            replay, "expected_outputs", return_value={}
        ):
            assert replay.main(["--require-complete-claims"]) == 0


def test_writer_preserves_equal_output_mtime() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        unchanged = root / "ComparatorReplay" / "Challenge.lean"
        unchanged.parent.mkdir(parents=True)
        unchanged.write_text("same\n", encoding="utf-8")
        timestamp = unchanged.stat().st_mtime_ns

        assert replay.write_changed_outputs({unchanged: "same\n"}) == 0
        assert unchanged.stat().st_mtime_ns == timestamp

        changed = root / "verification" / "comparator-replay-membership.json"
        assert replay.write_changed_outputs({changed: "new\n"}) == 1
        assert changed.read_text(encoding="utf-8") == "new\n"


def test_new_eligible_package_is_auto_included_and_baselined() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(
            root,
            challenge_import="Mathlib",
            solution_body="trivial",
        )
        lakefile = root / "lakefile.toml"
        lakefile.write_text(
            lakefile.read_text(encoding="utf-8")
            + '\n[[lean_lib]]\nname = "ExternalVerificationNew"\n',
            encoding="utf-8",
        )
        package = root / "ExternalVerificationNew"
        package.mkdir()
        (package / "Challenge.lean").write_text(
            "import Mathlib\n"
            "namespace New\n"
            "theorem newInterface : True := by\n"
            "  sorry\n"
            "end New\n",
            encoding="utf-8",
        )
        (package / "Solution.lean").write_text(
            "import Mathlib\n"
            "namespace New\n"
            "theorem newInterface : True := by\n"
            "  trivial\n"
            "end New\n",
            encoding="utf-8",
        )
        claims_path = root / "docs" / "claims.json"
        claims = json.loads(claims_path.read_text(encoding="utf-8"))
        claims["external_verification_packet"]["review_matrix"][0][
            "families"
        ].append(
            {
                "id": "new_family",
                "declarations": ["New.newInterface"],
                "comparator_disposition": "not_selected_new_replay_candidate",
            }
        )
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")

        portfolio = replay.build_portfolio(root)
        assert [package.name for package in portfolio.packages] == [
            "ExternalVerificationFixture",
            "ExternalVerificationNew",
        ]
        membership = json.loads(replay.render_membership(portfolio))
        assert membership["required_package_ids"] == [
            "ExternalVerificationFixture",
            "ExternalVerificationNew",
        ]
        assert set(membership["required_interfaces_by_package"]) == {
            "ExternalVerificationFixture",
            "ExternalVerificationNew",
        }
        assert membership["required_interfaces_by_package"]["ExternalVerificationNew"] == [
            "New.newInterface"
        ]
        new_family = next(
            row
            for row in membership["result_family_coverage"]["families"]
            if row["family_id"] == "new_family"
        )
        assert new_family["execution_classification"] == (
            "has_executable_challenge_package"
        )
        assert new_family["current_comparator_interface_count"] == 0
        assert new_family["replay_candidate_interface_count"] == 1
        assert [row["package_id"] for row in new_family["packages"]] == [
            "ExternalVerificationNew"
        ]


def test_new_non_executable_family_is_auto_classified_with_registry_reason() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(
            root,
            challenge_import="Mathlib",
            solution_body="trivial",
        )
        claims_path = root / "docs" / "claims.json"
        claims = json.loads(claims_path.read_text(encoding="utf-8"))
        claims["external_verification_packet"]["review_matrix"][0][
            "families"
        ].append(
            {
                "id": "exposition_only",
                "declarations": [],
                "comparator_disposition": "not_applicable_not_a_lean_proposition",
            }
        )
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")

        coverage = replay.build_portfolio(root).result_family_coverage
        row = next(
            row for row in coverage["families"] if row["family_id"] == "exposition_only"
        )
        assert row["execution_classification"] == "intentionally_non_executable"
        assert row["packages"] == []
        assert row["registry_comparator_disposition"] in row["non_executable_reason"]
        assert coverage["registered_family_count"] == len(coverage["families"])


def test_targeted_family_cannot_lack_an_executable_package() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(
            root,
            challenge_import="Mathlib",
            solution_body="trivial",
        )
        claims_path = root / "docs" / "claims.json"
        claims = json.loads(claims_path.read_text(encoding="utf-8"))
        claims["external_verification_packet"]["review_matrix"][0][
            "families"
        ].append(
            {
                "id": "missing_target",
                "declarations": ["Fixture.missing"],
                "comparator_disposition": "targeted",
            }
        )
        claims_path.write_text(json.dumps(claims, indent=2) + "\n", encoding="utf-8")
        _expect_portfolio_error(root, "cannot be intentionally non-executable")


def test_required_membership_prevents_silent_coverage_shrink() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(
            root,
            challenge_import="Mathlib",
            solution_body="trivial",
        )
        membership = root / "verification" / "comparator-replay-membership.json"
        membership.write_text(
            json.dumps(
                {
                    "schema": "plectis.comparator-replay-membership/1",
                    "required_package_ids": [
                        "ExternalVerificationFixture",
                        "ExternalVerificationMissing",
                    ],
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        _expect_portfolio_error(root, "disappeared without an explicit membership migration")


def test_required_interface_baseline_prevents_silent_nonlegacy_shrink() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(
            root,
            challenge_import="Mathlib",
            solution_body="trivial",
        )
        membership = root / "verification" / "comparator-replay-membership.json"
        payload = json.loads(membership.read_text(encoding="utf-8"))
        payload["required_interfaces_by_package"] = {
            "ExternalVerificationFixture": ["Fixture.interface", "Fixture.removed"]
        }
        membership.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        _expect_portfolio_error(
            root,
            "required Comparator replay interface(s) disappeared",
        )


def test_legacy_interface_assimilation_prevents_silent_interface_shrink() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        _write_fixture_package(
            root,
            challenge_import="Mathlib",
            solution_body="trivial",
        )
        membership = root / "verification" / "comparator-replay-membership.json"
        payload = json.loads(membership.read_text(encoding="utf-8"))
        payload["legacy_package_record_assimilation"] = {
            "schema": "plectis.legacy-palomar-package-assimilation/1",
            "source_snapshot": {
                "revision": "1" * 40,
                "tree": "2" * 40,
                "record_layout": (
                    "{package_id}/comparator.json + "
                    "{package_id}/formalization.yaml"
                ),
                "record_count": 1,
                "comparator_interface_count": 1,
            },
            "configuration_delta": {
                "current_aggregate_config": (
                    "verification/comparator-replay-candidate.json"
                ),
                "legacy_enable_nanoda": True,
                "current_enable_nanoda": False,
            },
            "formalization_policy": {
                "current_owner": "formalization.yaml",
                "per_package_manifests": "historical_only_do_not_recreate",
            },
            "package_records": [
                {
                    "package_id": "ExternalVerificationFixture",
                    "legacy_theorem_names": ["Erdos249257.ExternalVerificationFixture.missing"],
                }
            ],
        }
        membership.write_text(
            json.dumps(payload, indent=2) + "\n",
            encoding="utf-8",
        )
        _expect_portfolio_error(root, "disappeared from the dynamic aggregate")


def test_rejects_forbidden_solution_constructs() -> None:
    for forbidden in ("sorry", "admit", "native_decide", "unsafe"):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            _write_fixture_package(
                root,
                challenge_import="Mathlib",
                solution_body=forbidden,
            )
            _expect_portfolio_error(root, f"forbidden '{forbidden}'")


def main() -> int:
    test_live_portfolio_is_complete_unique_and_current()
    test_config_is_comparator_native_and_explicitly_non_nanoda()
    test_palomar_catalog_preserves_existing_owner_and_current_eligibility()
    test_palomar_disposition_rejects_synthetic_project_local_import()
    test_namespace_survives_nested_section_end()
    test_same_line_attributes_do_not_hide_interfaces()
    test_rejects_project_local_challenge_import()
    test_fixture_membership_projection_does_not_read_live_root()
    test_explicit_claim_transport_requires_exact_anchor_and_real_interface()
    test_main_result_claim_id_links_exact_source_without_claiming_semantics()
    test_complete_claim_requirement_is_opt_in_and_read_only()
    test_writer_preserves_equal_output_mtime()
    test_new_eligible_package_is_auto_included_and_baselined()
    test_new_non_executable_family_is_auto_classified_with_registry_reason()
    test_targeted_family_cannot_lack_an_executable_package()
    test_required_membership_prevents_silent_coverage_shrink()
    test_required_interface_baseline_prevents_silent_nonlegacy_shrink()
    test_legacy_interface_assimilation_prevents_silent_interface_shrink()
    test_rejects_forbidden_solution_constructs()
    portfolio = replay.build_portfolio()
    print(
        "test_comparator_replay_portfolio: "
        f"{len(portfolio.packages)} packages, {len(portfolio.theorem_names)} unique "
        "interfaces; deterministic outputs, trust boundary, and solution hygiene verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
