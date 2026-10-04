#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay track-specific PR intake and six fixture-only research kinds."""

from __future__ import annotations

import copy
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import build_research_contribution_recognition as recognition
import build_research_contributions as contributions
import check_research_return_intake as intake
import route_memory_receipt


ROOT = Path(__file__).resolve().parents[1]
SUBMITTED = ROOT / ".github" / "fixtures" / "unaccepted-research-return.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, *args], cwd=ROOT, capture_output=True, text=True, check=False
    )


def write(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def fixture_for(category: str, base: dict) -> dict:
    value = copy.deepcopy(base)
    value["record_kind"] = "validation_fixture"
    value["return_id"] = f"rr-fixture-category-{category}"
    value["frontier"]["handle"] = f"fixture/category-{category}"
    value["result"]["summary"] = (
        f"Fixture exercising the {category} return shape; no mathematical result is asserted."
    )
    value["result"]["surviving_boundary"] = "No mathematical result is established by this fixture."
    value["result"]["limitations"] = ["Intake fixture only; no mathematical replay or review occurred."]
    value["result"]["requested_disposition"] = "no_promotion"
    if category == "counterexample":
        value["result"]["class"] = "negative"
        value["result"]["claim_ceiling"] = "validation_fixture_only"
    elif category == "correction":
        value["result"]["class"] = "corrective"
        value["result"]["claim_ceiling"] = "documentation_correction"
        value["result"]["requested_disposition"] = "review_correction"
        value["correction_lineage"] = {
            "prior_return_reference": "none",
            "affected_paths": value["repository"]["changed_paths"],
            "starting_commit": value["repository"]["starting_commit"],
            "changed_evidence_or_wording": "Fixture wording only; no public source changed.",
            "reason": "Exercise the original-correction intake shape.",
            "disposition": "request_review",
        }
    else:
        value["result"]["class"] = "checked_positive"
        value["result"]["claim_ceiling"] = "validation_fixture_only"
    # The command is run in this test. It establishes only that contributor
    # routing works; it makes no claim about the mathematical category.
    value["evidence"][0].update(
        command="python3 scripts/test_contribution_entry.py",
        exit_state="passed",
        exit_code=0,
        observed="Contributor entry test passed; mathematical content was not tested.",
        replay_state="reproduced",
    )
    return value


def check_proposed_diff_coverage() -> list[dict]:
    """Replay PR intake against a real two-file diff in an isolated repository."""
    base = json.loads(SUBMITTED.read_text(encoding="utf-8"))
    results = []
    with tempfile.TemporaryDirectory(prefix="research-intake-diff-") as directory:
        temporary = Path(directory)
        checkout = temporary / "checkout"
        scripts = checkout / "scripts"
        scripts.mkdir(parents=True)
        # The actual intake and validator derive their Git root from __file__.
        # Copy their import closure instead of mocking Git or validating this repo.
        for name in (
            "check_research_return_intake.py", "validate_research_return.py",
            "repository_identity.py", "route_memory_receipt.py",
            "validation_singleflight.py", "lean_build_share.py", "lean_package_share.py",
        ):
            shutil.copyfile(ROOT / "scripts" / name, scripts / name)
        identity = checkout / "docs" / "repository_identity.json"
        identity.parent.mkdir()
        shutil.copyfile(ROOT / "docs" / "repository_identity.json", identity)
        environment = intake.return_validator.git_environment()
        environment["PYTHONDONTWRITEBYTECODE"] = "1"
        # Optimize the helper and its validator subprocess together.
        environment["PYTHONOPTIMIZE"] = str(sys.flags.optimize)

        def git(*args: str) -> str:
            result = subprocess.run(
                ["git", "-c", "user.name=Intake Fixture",
                 "-c", "user.email=intake-fixture@example.invalid",
                 "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args],
                cwd=checkout, env=environment, capture_output=True, text=True,
                check=False, timeout=30,
            )
            require(result.returncode == 0, f"synthetic Git command failed: {args}: {result.stderr}")
            return result.stdout.strip()

        git("init", "-q")
        for path in ("a.txt", "b.txt"):
            (checkout / path).write_text("before\n", encoding="utf-8")
        git("add", "a.txt", "b.txt")
        git("commit", "-qm", "starting source")
        starting = git("rev-parse", "HEAD")
        for path in ("a.txt", "b.txt"):
            (checkout / path).write_text("after\n", encoding="utf-8")
        git("add", "a.txt", "b.txt")
        git("commit", "-qm", "two-file proposal")
        proposed = git("rev-parse", "HEAD")
        require(git("diff", "--name-only", starting, proposed).splitlines() == ["a.txt", "b.txt"],
                "synthetic proposal lost its two distinct changed paths")
        base["return_id"] = "rr-fixture-architecture-proposed-diff"
        base["repository"].update(starting_commit=starting, proposed_commit=proposed)
        base["frontier"] = {
            "track": "architecture", "area": "tooling",
            "handle": "fixture/proposed-diff-coverage",
            "bounded_question": "Does PR intake require every proposed source path?",
            "stop_condition": "Stop after omitted, complete and uncommitted cases.",
            "starting_paths": ["a.txt"],
        }
        base["result"].update(
            claim_ceiling="architecture_proposal",
            summary="Synthetic source-coverage fixture; no adoption is claimed.",
            surviving_boundary="No software correctness or mathematical result is established.",
        )
        base["evidence"][0].update(
            command="python3 scripts/check_research_return_intake.py",
            observed="Fixture-only source check; evidence replay is recorded by the test.",
        )
        returned = temporary / "return.json"
        route = temporary / "route-memory.json"

        def evaluate(name: str, paths: list[str], *, standalone: bool = False) -> dict:
            base["repository"]["changed_paths"] = paths
            base["evidence"][0]["artifacts"] = paths
            base["attribution"]["artifact_credit"][0]["artifact_paths"] = paths
            write(returned, base)
            if standalone:
                arguments = [str(scripts / "validate_research_return.py"), str(returned),
                             "--require-submitted", "--check-git"]
            else:
                arguments = [str(scripts / "check_research_return_intake.py"),
                             "--return-json", str(returned), "--route-memory-receipt", str(route)]
            result = subprocess.run(
                [sys.executable, *arguments], cwd=checkout, env=environment,
                capture_output=True, text=True, check=False, timeout=30,
            )
            require(bool(result.stdout), f"{name} emitted no receipt: {result.stderr}")
            receipt = json.loads(result.stdout)
            require(receipt.get("accepted") is False, f"{name} asserted acceptance: {receipt}")
            results.append({"case": name, "exit": result.returncode, "receipt": receipt})
            return results[-1]

        optional = evaluate("standalone-optional-coverage", ["a.txt"], standalone=True)
        require(optional["exit"] == 0 and optional["receipt"]["valid"],
                f"standalone validator lost its optional coverage policy: {optional}")
        omitted = evaluate("omitted-proposed-path", ["a.txt"])
        require(omitted["exit"] == 1 and not omitted["receipt"]["valid"],
                f"PR intake admitted an incomplete proposed source set: {omitted}")
        require(any("paths omitted" in error and "b.txt" in error
                    for error in omitted["receipt"]["errors"]),
                f"omitted path was not identified: {omitted}")
        complete = evaluate("complete-proposed-paths", ["a.txt", "b.txt"])
        require(complete["exit"] == 0 and complete["receipt"]["submitted"],
                f"complete proposal failed intake: {complete}")
        base["repository"].update(starting_commit=proposed, proposed_commit=None)
        (checkout / "a.txt").write_text("uncommitted draft\n", encoding="utf-8")
        draft = evaluate("uncommitted-draft", ["a.txt"])
        require(draft["exit"] == 0 and draft["receipt"]["submitted"],
                f"uncommitted draft acquired a proposed-commit requirement: {draft}")
        require(not complete["receipt"]["route_memory_receipt_required"]
                and not draft["receipt"]["route_memory_receipt_required"] and not route.exists(),
                "architecture source checks acquired mathematical route memory")
    return results


def main() -> int:
    check_proposed_diff_coverage()
    base = json.loads(SUBMITTED.read_text(encoding="utf-8"))
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                          text=True, check=True).stdout.strip()
    base["repository"]["starting_commit"] = head
    require(run("scripts/test_contribution_entry.py").returncode == 0, "fixture evidence command failed")
    with tempfile.TemporaryDirectory(prefix="research-intake-") as directory:
        root = Path(directory)
        route = root / "route-memory.json"
        returned = root / "return.json"
        require(intake.validation_arguments(returned, route) is None, "empty PR unexpectedly had intake")
        route.symlink_to(root / "missing-sidecar.json")
        try:
            intake.validation_arguments(returned, route)
        except ValueError as exc:
            require("symbolic links" in str(exc), "dangling sidecar had the wrong rejection")
        else:
            raise AssertionError("dangling sidecar bypassed intake")
        route.unlink()

        architecture = copy.deepcopy(base)
        architecture["return_id"] = "rr-fixture-architecture-intake"
        architecture["frontier"] = {
            "track": "architecture",
            "area": "validation",
            "handle": "fixture/architecture-intake",
            "bounded_question": "Does the architecture return validate without a mathematical sidecar?",
            "stop_condition": "Stop after structural validation.",
            "starting_paths": architecture["repository"]["changed_paths"],
        }
        architecture["result"].update(
            claim_ceiling="architecture_proposal",
            summary="A fixture for architecture return intake; no adoption is claimed.",
            surviving_boundary="No architecture change or adoption is established.",
        )
        write(returned, architecture)
        result = run("scripts/check_research_return_intake.py", "--return-json", str(returned),
                     "--route-memory-receipt", str(route))
        require(result.returncode == 0, f"architecture return without sidecar failed: {result.stdout} {result.stderr}")
        route.write_text("{}\n", encoding="utf-8")
        result = run("scripts/check_research_return_intake.py", "--return-json", str(returned),
                     "--route-memory-receipt", str(route))
        require(result.returncode != 0 and "must omit route-memory.json" in result.stderr,
                "architecture return accepted a mathematical sidecar")
        route.unlink()

        write(returned, base)
        result = run("scripts/check_research_return_intake.py", "--return-json", str(returned),
                     "--route-memory-receipt", str(route))
        require(result.returncode != 0 and "requires route-memory.json" in result.stderr,
                "mathematics return lost mandatory route memory")
        route.write_text("{}\n", encoding="utf-8")
        result = run("scripts/check_research_return_intake.py", "--return-json", str(returned),
                     "--route-memory-receipt", str(route))
        require(result.returncode != 0 and "route_memory" in result.stdout,
                "mathematics sidecar bypassed the public validator")
        route.unlink()
        returned.unlink()

        categories = ("proof", "reduction", "computation", "counterexample", "correction", "exposition")
        sources = root / "candidate-sources"
        sources.mkdir()
        for category in categories:
            path = root / f"{category}.json"
            write(path, fixture_for(category, base))
            (sources / path.name).write_bytes(path.read_bytes())
            valid = run("scripts/validate_research_return.py", str(path), "--check-git")
            require(valid.returncode == 0, f"{category} fixture failed validation: {valid.stdout} {valid.stderr}")
            promoted = run("scripts/validate_research_return.py", str(path), "--require-submitted")
            require(promoted.returncode != 0, f"{category} fixture entered submitted intake")
            # An early return in any advertised kind can truthfully be
            # inconclusive. Exercise the complete mathematical PR intake with
            # a canonical detached route receipt, without fabricating a proof.
            draft = copy.deepcopy(base)
            draft["return_id"] = f"rr-fixture-submitted-{category}"
            draft["frontier"]["handle"] = f"fixture/submitted-{category}"
            draft["result"]["summary"] = (
                f"Unreviewed {category} candidate stopped at the recorded assumption."
            )
            draft_path = root / f"submitted-{category}.json"
            sidecar_path = root / f"route-{category}.json"
            write(draft_path, draft)
            (sources / draft_path.name).write_bytes(draft_path.read_bytes())
            consultation = route_memory_receipt.consultation_for_problem(257, ROOT)
            sidecar = route_memory_receipt.return_receipt_template(consultation)
            sidecar["return_id"] = draft["return_id"]
            write(sidecar_path, sidecar)
            admitted = run("scripts/check_research_return_intake.py", "--return-json", str(draft_path),
                           "--route-memory-receipt", str(sidecar_path))
            require(admitted.returncode == 0,
                    f"{category} draft failed public PR intake: {admitted.stdout} {admitted.stderr}")
            review = run("scripts/accept_research_return.py", str(draft_path),
                         "--write-decision-template", str(root / f"decision-{category}.json"),
                         "--route-memory-receipt", str(sidecar_path),
                         "--require-route-memory-receipt")
            require(review.returncode != 0 and "proposed_commit" in review.stdout,
                    f"{category} uncommitted draft crossed review preparation: {review.stdout} {review.stderr}")
            require(not (root / f"decision-{category}.json").exists(),
                    f"{category} review template was emitted for a draft without an artifact commit")
        require(contributions.load_receipts(sources) == [], "unaccepted category fixtures entered accepted sources")
        contribution_view = contributions.build_projection([])
        recognition_view = recognition.build_recognition([])
        recognition.validate_projection(recognition_view)
        require(not contribution_view["chronological"], "category fixtures entered contributions")
        require(recognition_view["accepted_receipt_count"] == 0, "category fixtures entered recognition")

    print("research return intake: architecture without sidecar, mathematics sidecar, six fixture categories, accepted-only exclusion PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
