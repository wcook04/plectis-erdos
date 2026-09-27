#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Behavioral regressions for CI/local admission parity and scheduling."""
from __future__ import annotations

import contextlib
import io
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import check_ci_contracts as contracts
import refresh_projections
import test_lean_workflow_environment as workflow


class ContractTests(unittest.TestCase):
    def test_new_ci_test_cannot_escape_local_preflight(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / ".github/workflows").mkdir(parents=True)
            for name, jobs in contracts.WORKFLOW_JOBS.items():
                (root / ".github/workflows" / name).write_text("jobs:\n" + "".join(
                    f"  {job}:\n    steps:\n      - run: python3 scripts/test_new_contract.py\n"
                    for job in jobs))
            errors = contracts.coverage_errors(root, ())
            self.assertEqual(len(errors), len(contracts.WORKFLOW_JOBS))
            self.assertTrue(all("test_new_contract.py" in error for error in errors))

    def test_workflow_reader_is_bounded_and_rejects_unknown_test_syntax(self):
        fixture = "jobs:\n  build:\n    steps:\n      - name: Test\n        run: |\n          # python3 scripts/test_comment.py\n          python3 -O scripts/test_one.py\n          python3 scripts/test_two.py\n  release:\n    run: python3 scripts/test_elsewhere.py\n"
        self.assertEqual(contracts.workflow_tests(fixture, ("build",)), {"test_one.py", "test_two.py"})
        for source in (fixture.replace("python3 -O", "python3 -m unittest"), "jobs:\n"):
            with self.assertRaises(ValueError):
                contracts.workflow_tests(source, ("build",))

    def test_real_child_failure_optimization_and_timeout_are_blocking(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "scripts").mkdir()
            (root / "scripts/test_ok.py").write_text("raise SystemExit(0)\n")
            (root / "scripts/test_bad.py").write_text("raise SystemExit(7)\n")
            (root / "scripts/test_optimized.py").write_text("raise SystemExit(0 if __debug__ else 9)\n")
            (root / "scripts/test_wait.py").write_text("import time; time.sleep(10)\n")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(contracts.run_suite(("test_ok.py",), root=root), 0)
                self.assertEqual(contracts.run_suite(("test_bad.py", "test_optimized.py"), root=root, timeout=10), 1)
                self.assertEqual(contracts.run_suite(("test_wait.py",), root=root, timeout=0.2), 1)
            for message in ("exit 7", "exit 9", "timed out", "1/4 passed", "0/2 passed"):
                self.assertIn(message, out.getvalue())

    def test_shared_preflight_rejects_contract_failure(self):
        self.assertIn("scripts/check_ci_contracts.py", refresh_projections.PREFLIGHT_CHECKS)
        import subprocess
        def run(argv, cwd):
            return subprocess.CompletedProcess(argv, int(Path(argv[1]).name == "check_ci_contracts.py"), "contract fixture failure", "")
        with patch.object(refresh_projections, "run", side_effect=run), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(refresh_projections.preflight(), 1)

    def test_action_annotation_names_the_command_and_escapes_output(self):
        annotation = refresh_projections.failure_annotation("scripts/check_ci_contracts.py", "failed 50%\n::warning::fixture\rnext")
        self.assertIn("file=scripts/check_ci_contracts.py", annotation)
        self.assertIn("python3 scripts/check_ci_contracts.py", annotation)
        self.assertIn("50%25%0A::warning::fixture%0Dnext", annotation)
        self.assertNotIn("\n", annotation)

    def test_route_budget_cli_rejects_growth_and_missing_files_before_release(self):
        import json
        import check_release
        self.assertIn("--route-budgets-only", refresh_projections.PREFLIGHT_CHECKS["scripts/check_release.py"])
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "docs").mkdir()
            route = {"id": "fixture", "read": ["entry.md"]}
            (root / "docs/claims.json").write_text(json.dumps({"machine_readable_paper": {"entrypoints": [route]}}))
            entry = root / "entry.md"
            with patch.object(check_release, "ROOT", root), contextlib.redirect_stdout(io.StringIO()):
                entry.write_bytes(b"x" * check_release.MAX_ROUTE_FIRST_CONTACT_BYTES)
                self.assertEqual(check_release.main(["--route-budgets-only"]), 0)
                entry.write_bytes(entry.read_bytes() + b"x")
                self.assertEqual(check_release.main(["--route-budgets-only"]), 1)
                entry.unlink()
                self.assertEqual(check_release.main(["--route-budgets-only"]), 1)

    def test_actual_workflow_and_mutations(self):
        source = workflow.WORKFLOW.read_text()
        workflow.require_evidence_before_expensive_jobs(source)
        workflow.require_release_before_expensive_jobs(source)
        mutations = (
            source.replace("github.event_name != 'workflow_dispatch' || inputs.scope != 'dependency-index-refresh'", "inputs.scope != 'dependency-index-refresh'", 1),
            source.replace("needs: [change_scope, release-surfaces]", "needs: [release-surfaces]", 1),
            source.replace("needs.release-surfaces.result == 'success'", "needs.release-surfaces.result != 'cancelled'", 1),
            source.replace("!cancelled() && needs.change_scope.result", "needs.change_scope.result", 1),
        )
        for changed in mutations:
            self.assertNotEqual(changed, source)
            with self.assertRaises(AssertionError):
                workflow.require_evidence_before_expensive_jobs(changed)
                workflow.require_release_before_expensive_jobs(changed)


if __name__ == "__main__":
    unittest.main()
