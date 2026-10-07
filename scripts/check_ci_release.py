#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Shared supplemental release checks, consumed by check_release locally and in CI.

Keep leaf checks here instead of adding GitHub-only run steps. Each failure is
reported and remaining checks still run. No child invokes the parent release
gate. The corpus-only workflow retains its narrower public-boundary checks.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

import validation_singleflight as singleflight

ROOT = Path(__file__).resolve().parents[1]
TIMEOUT_SECONDS = 360
# Migrated without dropping any command from the GitHub release-surfaces job.
# Optimized runs and module-based unittest invocations remain distinct gates.
COMMANDS = (
    ('computations/check_enclosure_product_use.py',),
    ('-O', 'computations/check_enclosure_product_use.py'),
    ('scripts/tests/test_paper_claim_evidence.py',),
    ('-O', 'scripts/tests/test_paper_claim_evidence.py'),
    ('scripts/tests/test_short_paper_writer.py',),
    ('-O', 'scripts/tests/test_short_paper_writer.py'),
    ('scripts/tests/test_reasoning_record_audit.py',),
    ('-O', 'scripts/tests/test_reasoning_record_audit.py'),
    ('research/experiments/round8_finite/test_round8_finite.py',),
    ('-O', 'research/experiments/round8_finite/test_round8_finite.py'),
    ('scripts/tests/test_round8_native_port.py',),
    ('-O', 'scripts/tests/test_round8_native_port.py'),
    ('scripts/tests/test_restatement_benchmark.py',),
    ('-O', 'scripts/tests/test_restatement_benchmark.py'),
    ('scripts/tests/test_research_decision.py',),
    ('-O', 'scripts/tests/test_research_decision.py'),
    ('scripts/tests/test_research_episode.py',),
    ('-O', 'scripts/tests/test_research_episode.py'),
    ('scripts/tests/test_relation_binding.py',),
    ('-O', 'scripts/tests/test_relation_binding.py'),
    ('scripts/tests/test_probe_semantics.py',),
    ('-O', 'scripts/tests/test_probe_semantics.py'),
    ('scripts/tests/test_research_return_gate.py',),
    ('-O', 'scripts/tests/test_research_return_gate.py'),
    ('scripts/tests/test_native_adapter_regressions.py',),
    ('-O', 'scripts/tests/test_native_adapter_regressions.py'),
    ('scripts/tests/test_corpus_substrate.py',),
    ('-O', 'scripts/tests/test_corpus_substrate.py'),
    ('scripts/check_corpus_substrate_release.py',),
    ('scripts/tests/test_packet_safety_patch.py',),
    ('-O', 'scripts/tests/test_packet_safety_patch.py'),
    ('scripts/tests/test_research_packet_profile.py',),
    ('-O', 'scripts/tests/test_research_packet_profile.py'),
    ('scripts/tests/test_research_round_plan.py',),
    ('-O', 'scripts/tests/test_research_round_plan.py'),
    ('scripts/tests/test_transfer_obligations.py',),
    ('-O', 'scripts/tests/test_transfer_obligations.py'),
    ('scripts/tests/test_insight_engine.py',),
    ('-O', 'scripts/tests/test_insight_engine.py'),
    ('scripts/tests/test_research_evidence.py',),
    ('-O', 'scripts/tests/test_research_evidence.py'),
    ('scripts/check_erdos1041_research_corpus.py',),
    ('scripts/tests/test_erdos1041_research_corpus.py',),
    ('-O', 'scripts/tests/test_erdos1041_research_corpus.py'),
    ('scripts/tests/test_dependency_lock_contract.py',),
    ('scripts/tests/test_lean_workflow_environment.py',),
    ('-O', 'scripts/tests/test_lean_workflow_environment.py'),
    ('scripts/check_architecture_guide.py',),
    ('scripts/check_agent_navigation_paper.py',),
    ('scripts/tests/test_architecture_guide.py',),
    ('scripts/tests/test_build_systems_paper_counts.py',),
    ('-O', 'scripts/tests/test_build_systems_paper_counts.py'),
    ('scripts/tests/test_verify_claims.py',),
    ('scripts/tests/test_problem_library.py',),
    ('scripts/check_publication_contract.py',),
    ('scripts/check_erdos269_dyadic_windows.py',),
    ('scripts/check_farey_denominator_scaling.py',),
    ('scripts/check_formal_conjectures_crosswalk.py',),
    ('-m', 'unittest', 'scripts.tests.test_formal_conjectures_crosswalk', '-v'),
    ('scripts/tests/test_residual_evaluator.py',),
    ('scripts/check_markdown_table_render.py', '--fail-on', 'overflow', '.'),
    ('-m', 'unittest', 'scripts.tests.test_markdown_table_render', '-v'),
    ('scripts/tests/test_projection_checkout_independence.py',),
    ('scripts/tests/test_release_source_identity.py',),
    ('scripts/tests/test_expert_handoffs.py',),
    ('-O', 'scripts/tests/test_expert_handoffs.py'),
    ('scripts/tests/test_check_release_ref.py',),
    ('scripts/tests/test_check_push.py',),
    ('scripts/tests/test_scope_source_identity.py',),
    ('scripts/tests/test_public_artifact_boundary.py',),
    ('scripts/tests/test_root_import_closure.py',),
    ('scripts/tests/test_downstream_example_contract.py',),
    ('scripts/tests/test_public_writing_contract.py',),
    ('scripts/tests/test_methodology_contract.py',),
    ('scripts/tests/test_publication_artifact_contract.py',),
    ('scripts/tests/test_publication_contract_restamp.py',),
    ('scripts/tests/test_paper_build_manifest.py',),
    ('scripts/tests/test_sync_publication_pdfs.py',),
    ('scripts/tests/test_claim_packet_boundaries.py',),
    ('scripts/tests/test_publication_evidence_time_axis.py',),
    ('scripts/papers/check_paper_corpus.py',),
    ('scripts/papers/check_publication_taxonomy.py',),
    ('scripts/papers/build_publication_taxonomy.py', '--check'),
    ('scripts/tests/test_status_question_search.py',),
    ('scripts/check_metadata.py',),
    ('scripts/tests/test_citation_identity_contract.py',),
    ('scripts/tests/test_checkout_sync.py',),
    ('scripts/tests/test_license_map_contract.py',),
    ('scripts/tests/test_build_benchmark_packet_environment.py',),
    ('scripts/tests/test_check_metadata_environment.py',),
    ('scripts/tests/test_check_rendered_paper_boundary_environment.py',),
    ('scripts/tests/test_checked_diagonal_depth_roster.py',),
    ('scripts/tests/test_corpus_orientation.py',),
    ('scripts/tests/test_declaration_atlas.py',),
    ('scripts/tests/test_expansion_semantic_zones.py',),
    ('scripts/tests/test_full_coverage_agent_entry.py',),
    ('scripts/tests/test_historical_bridge_environment.py',),
    ('scripts/tests/test_layout_conservation.py',),
    ('scripts/tests/test_lean_package_share.py',),
    ('scripts/tests/test_lean_source_layout.py',),
    ('scripts/tests/test_off_diagonal_certificate_roster.py',),
    ('scripts/tests/test_palomar_qualification_order_contract.py',),
    ('scripts/tests/test_primary_source_dispositions.py',),
    ('scripts/tests/test_probe_certificate_supply.py',),
    ('scripts/tests/test_probe_second_channel_separation.py',),
    ('scripts/tests/test_problem_note_sources.py',),
    ('scripts/tests/test_proof_state_compiler.py',),
    ('scripts/tests/test_public_paper_links.py',),
    ('scripts/tests/test_publication_artifact_census.py',),
    ('scripts/tests/test_reanchor_source_attributions.py',),
    ('scripts/tests/test_refresh_projections_coverage.py',),
    ('scripts/tests/test_refresh_projections_environment.py',),
    ('scripts/tests/test_release_child_status.py',),
    ('scripts/tests/test_repository_identity.py',),
    ('scripts/tests/test_semantic_corpus_check_receipt.py',),
    ('scripts/tests/test_semantic_family_compiler.py',),
    ('scripts/tests/test_semantic_review_rebind.py',),
    ('scripts/tests/test_shard_closure_t64.py',),
    ('scripts/tests/test_source_bound_reproduction.py',),
    ('scripts/tests/test_strict_prime_semantic_digest.py',),
    # The research record: journal custody, relation rows, the contrast ledger
    # and the research-packet compiler, then the committed record data.
    ('scripts/tests/test_research_record.py',),
    ('-O', 'scripts/tests/test_research_record.py'),
    ('scripts/tests/test_relation_registry.py',),
    ('-O', 'scripts/tests/test_relation_registry.py'),
    ('scripts/tests/test_contrast_ledger.py',),
    ('-O', 'scripts/tests/test_contrast_ledger.py'),
    ('scripts/tests/test_compile_research_packet.py',),
    ('-O', 'scripts/tests/test_compile_research_packet.py'),
    ('scripts/research_record.py', 'verify'),
    ('scripts/relation_registry.py', 'check'),
    ('scripts/contrast_ledger.py', 'check'),
    ('-m', 'reuse', 'lint'),
)


def workflow_errors(source: str) -> list[str]:
    match = re.search(r"(?ms)^  release-surfaces:\n(.*?)(?=^  \S|\Z)", source)
    if match is None:
        return ["missing release-surfaces job"]
    steps = re.split(r"(?m)^      - ", match.group(1))[1:]
    allowed = {
        "Check content-addressed Erdős 1041 research corpus": "python3 scripts/check_erdos1041_research_corpus.py",
        "Test public corpus privacy boundary": "python3 scripts/tests/test_erdos1041_research_corpus.py\npython3 -O scripts/tests/test_erdos1041_research_corpus.py",
        "Cross-surface release checks (proof trust, claims, projections)": "python3 scripts/check_release.py",
        "Test problem papers for corpus-only changes": "python3 scripts/tests/test_problem_library.py",
        "Test public-artifact boundary": "python3 scripts/tests/test_public_artifact_boundary.py",
        "Install metadata validators": "python3 -m pip install --disable-pip-version-check --no-cache-dir --require-hashes --requirement scripts/requirements-release.txt\npython_bin_dir=\"$(python3 -c 'import os, sys; print(os.path.dirname(sys.executable))')\"\necho \"$python_bin_dir\" >> \"$GITHUB_PATH\"",
    }
    seen = set()
    errors = []
    for step in steps:
        run = re.search(r"(?m)^        run: (.*)$", step)
        if not run:
            if step.startswith("run:"):
                errors.append("unnamed GitHub-only release run step")
            elif not (step.startswith("uses: actions/checkout@") or step.startswith("name: Install the pinned Python runtime\n")):
                errors.append("unregistered release workflow step: " + step.splitlines()[0])
            continue
        name = step.splitlines()[0].removeprefix("name: ")
        command = run.group(1)
        if command == "|":
            command = "\n".join(line.strip() for line in step[run.end():].splitlines()
                                if line.startswith("          ") and line.strip() and not line.lstrip().startswith("#"))
        if name in seen or allowed.get(name) != command:
            errors.append(f"GitHub-only release gate or changed setup: {name}; put validation commands in check_ci_release.COMMANDS")
        seen.add(name)
    for name in sorted(set(allowed) - seen):
        errors.append(f"missing shared release entry or corpus boundary: {name}")
    return errors


def registry_errors(commands=COMMANDS, *, root: Path = ROOT) -> list[str]:
    errors = []
    if len(commands) != len(set(commands)):
        errors.append("duplicate supplemental release command")
    for command in commands:
        args = command[1:] if command and command[0] == "-O" else command
        if not args:
            errors.append("empty release command")
        elif args[0] == "-m":
            if args[1:2] == ("unittest",) and len(args) == 4:
                path = root / (args[2].replace(".", "/") + ".py")
                if not path.is_file():
                    errors.append(f"missing unittest module: {args[2]}")
            elif args != ("-m", "reuse", "lint"):
                errors.append(f"unsupported release module: {command}")
        elif not (root / args[0]).is_file():
            errors.append(f"missing supplemental release gate: {args[0]}")
        elif Path(args[0]).name in {"check_release.py", "check_ci_release.py"}:
            errors.append(f"recursive release gate: {args[0]}")
    return errors


def escape_annotation(value: str) -> str:
    return value.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def run_suite(commands=COMMANDS, *, root: Path = ROOT,
              timeout: float = TIMEOUT_SECONDS) -> dict:
    results = []
    for command in commands:
        label = "python3 " + " ".join(command)
        started = time.monotonic()
        if os.environ.get("GITHUB_ACTIONS") == "true":
            print(f"::group::{label}", flush=True)
        try:
            child = singleflight.run_bounded([sys.executable, *command], cwd=root,
                                   env=singleflight.command_environment(),
                                   text=True, capture_output=True, timeout=timeout)
            code, detail = child.returncode, (child.stdout + "\n" + child.stderr).strip()
            timed_out = False
        except subprocess.TimeoutExpired:
            code, detail, timed_out = 124, f"timed out after {timeout}s", True
        except OSError as exc:
            code, detail, timed_out = 127, str(exc), False
        results.append({"command": list(command), "exit_code": code,
                        "timed_out": timed_out, "seconds": round(time.monotonic() - started, 3),
                        "output_tail": detail[-12000:]})
        print(f"{'FAIL' if code else 'PASS'} {label}" + (f"\n{detail[-12000:]}" if code else ""), flush=True)
        if os.environ.get("GITHUB_ACTIONS") == "true":
            print("::endgroup::", flush=True)
            if code:
                print("::error::" + escape_annotation(f"{label}: exit {code}; {detail[-2000:]}"), flush=True)
    failures = sum(row["exit_code"] != 0 for row in results)
    return {"schema": "shared_ci_release_checks_v1", "status": "failed" if failures else "passed",
            "configured": len(commands), "completed": len(results), "failed": failures,
            "results": results}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    errors = registry_errors() + workflow_errors((ROOT / ".github/workflows/lean.yml").read_text())
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    result = run_suite()
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(f"shared CI release checks: {result['completed'] - result['failed']}/{result['configured']} passed")
    for row in result["results"]:
        if row["exit_code"]:
            print("failed command: python3 " + " ".join(row["command"]))
    return int(result["failed"] != 0)


if __name__ == "__main__":
    raise SystemExit(main())
