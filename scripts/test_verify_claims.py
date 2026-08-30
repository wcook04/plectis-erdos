#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Prove the claim-following verb reports drift instead of absorbing it.

A checker that cannot be shown failing is decoration. The register is currently
sound, so running `verify_claims.py` against this repository proves only that it
says yes. These fixtures give it registers that are wrong in each of the ways a
register goes wrong -- a shifted line, a renamed declaration, a status outside
the taxonomy, an open proposition pointing at a claim that no longer exists --
and require a report for every one.

Two of the fixtures also pin the Lean spellings that a naive matcher gets wrong,
because both mistakes were made while writing the checker: a declaration whose
name wraps onto the line below its `theorem` keyword, and a declaration written
inside a namespace but registered under its qualified name.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

import verify_claims

# Deliberately awkward, and all of it real Lean shape from this corpus:
# a wrapped `theorem`, a namespaced declaration, and a modifier before `def`.
SAMPLE_MODULE = """\
import Mathlib

namespace Sample

/-- **Wrapped declaration.**  The name sits below the keyword. -/
theorem
    alpha (n : Nat) : n = n := rfl

/-- **Modifier before the keyword.** -/
noncomputable def beta : Nat := 0

end Sample
"""

# Line numbers into SAMPLE_MODULE above (1-indexed). `alpha` is recorded at the
# `theorem` keyword on line 6 with its name on line 7, which is how the real
# register records wrapped declarations.
ALPHA_KEYWORD_LINE = 6
BETA_LINE = 10

TAXONOMY = {"proved here": "Lean theorem in the committed formal-source checkpoint"}


def require(condition: bool, message: str) -> None:
    """Keep claims-verification failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def check_safe_read_boundary() -> None:
    original_root = verify_claims.REPO_ROOT
    with tempfile.TemporaryDirectory(prefix="claims-input-") as raw_workspace:
        workspace = Path(raw_workspace)
        verify_claims.REPO_ROOT = workspace
        regular = workspace / "regular.txt"
        regular.write_text("claims input\n", encoding="utf-8")
        require(
            verify_claims.safe_read_text(regular) == "claims input\n",
            "claims verifier rejected a regular source file",
        )

        directory = workspace / "directory"
        directory.mkdir()
        require(
            verify_claims.safe_read_text(directory) is None,
            "claims verifier accepted a directory input",
        )

        symlink = workspace / "symlink.txt"
        symlink.symlink_to(regular)
        require(
            verify_claims.safe_read_text(symlink) is None,
            "claims verifier followed a symlinked source input",
        )

        if hasattr(os, "mkfifo"):
            fifo = workspace / "fifo"
            os.mkfifo(fifo)
            require(
                verify_claims.safe_read_text(fifo) is None,
                "claims verifier accepted a FIFO source input",
            )
    verify_claims.REPO_ROOT = original_root


def build_register(
    claims: list[dict],
    open_props: list[dict] | None = None,
    main_results: list[dict] | None = None,
) -> dict:
    register = {
        "schema": "erdos249257-claims/3",
        "release": {"version": "test", "formal_source": {}},
        "status_taxonomy": TAXONOMY,
        "non_claims": [],
        "remaining_open_propositions": open_props or [],
        "claims": claims,
    }
    if main_results is not None:
        register["external_verification_packet"] = {
            "boundary": "Comparator checks statements, not significance.",
            "comparator": {"permitted_axioms": ["propext"], "config": "verification/comparator.json"},
            "claim_status_contract": {"unregistered_interface": "Not a canonical reviewed claim."},
            "main_results": main_results,
        }
    return register


def claim(
    decl_name: str,
    line: int,
    status: str = "proved here",
    paper_label: str | None = None,
    module: str = "Sample.lean",
) -> dict:
    return {
        "id": "sample_claim",
        "label": "Sample",
        "status": status,
        "statement": "A sample statement.",
        "paper_label": paper_label,
        "declarations": [
            {"name": decl_name, "module": module, "line": line}
        ],
    }


def run_case(root: Path, register: dict) -> dict:
    (root / "docs").mkdir(parents=True, exist_ok=True)
    (root / "docs" / "claims.json").write_text(json.dumps(register), encoding="utf-8")
    verify_claims.REPO_ROOT = root
    verify_claims.CLAIMS_PATH = root / "docs" / "claims.json"
    return verify_claims.verify_all_claims(register)


def statuses(report: dict) -> set[str]:
    return {problem.get("status") for problem in report["problems"]}


def check_gate_timeout_contract() -> None:
    """Keep Git probes and every gate child inside explicit time ceilings."""
    observed: list[int | None] = []

    def fake_run(argv: list[str], *, cwd: Path, timeout: int | None = None) -> subprocess.CompletedProcess[str]:
        observed.append(timeout)
        if len(observed) == 1:
            raise subprocess.TimeoutExpired(argv, timeout)
        return subprocess.CompletedProcess(argv, 0, stdout="", stderr="")

    with patch.object(verify_claims, "run", side_effect=fake_run):
        gates = verify_claims.run_gates({"shallow_clone": False})

    require(observed, "the gate runner did not launch any child")
    require(
        observed[0] == verify_claims.GATE_TIMEOUT_SECONDS,
        "gate runner lost the canonical worker timeout",
    )
    require(
        gates["failed"] >= 1
        and any(
            row.get("returncode") == verify_claims.singleflight.WORKER_TIMEOUT_EXIT_CODE
            for row in gates["results"]
        ),
        "gate runner did not report a timed-out child as a bounded failure",
    )

    with patch.object(verify_claims, "run", return_value=subprocess.CompletedProcess([], 0, "", "")) as runner:
        verify_claims.git_output("rev-parse", "HEAD")
    require(
        runner.call_args.kwargs["timeout"]
        == verify_claims.singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "Git probe lost the canonical command timeout",
    )


def check_optional_tool_discovery_contract() -> None:
    """Optional gate availability must ignore a hostile caller PATH."""
    observed_paths: list[str | None] = []

    def fake_which(tool: str, mode: int = os.F_OK, path: str | None = None) -> None:
        del tool, mode
        observed_paths.append(path)
        return None

    hostile = {"PATH": "/private/host-tools/bin"}
    with patch.dict(os.environ, hostile, clear=False):
        with patch.object(verify_claims.shutil, "which", side_effect=fake_which):
            require(
                not verify_claims.optional_tool_available("cffconvert"),
                "hostile optional-tool lookup unexpectedly reported availability",
            )
    require(len(observed_paths) == 1, "optional-tool discovery made an unexpected lookup count")
    require(
        observed_paths[0]
        == os.pathsep.join((str(Path(sys.executable).resolve().parent), os.defpath)),
        "optional-tool discovery consulted ambient PATH",
    )

    calls: list[str] = []
    with patch.object(
        verify_claims,
        "optional_tool_available",
        side_effect=lambda tool: calls.append(tool) or False,
    ):
        with patch.object(verify_claims, "git_output", return_value=None):
            verify_claims.describe_environment({})
        with patch.object(
            verify_claims,
            "run",
            return_value=subprocess.CompletedProcess([], 0, "", ""),
        ):
            verify_claims.run_gates({"shallow_clone": True})
    require(calls.count("cffconvert") == 2, "both optional-gate consumers must use the isolated lookup")


def main() -> int:
    check_gate_timeout_contract()
    check_optional_tool_discovery_contract()
    failures: list[str] = []
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        (root / "Sample.lean").write_text(SAMPLE_MODULE, encoding="utf-8")

        # A published checkout must not let caller Git selectors redirect the
        # child process to a private repository, namespace, or replacement map.
        hostile_environment = {
            "GIT_DIR": "/private/wrong-git-dir",
            "GIT_WORK_TREE": "/private/wrong-work-tree",
            "GIT_INDEX_FILE": "/private/wrong-index",
            "GIT_NAMESPACE": "wrong-namespace",
            "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
            "GIT_OBJECT_DIRECTORY": "/private/wrong-objects",
            "GIT_ALTERNATE_OBJECT_DIRECTORIES": "/private/wrong-alternates",
            "GIT_COMMON_DIR": "/private/wrong-common",
            "PYTHONHOME": "/private/wrong-python-home",
            "PYTHONPATH": "/private/wrong-python-path",
            "PYTHONOPTIMIZE": "2",
            "LC_ALL": "C",
            "LANG": "C",
            "LANGUAGE": "C",
            "PATH": "/private/wrong-bin",
        }
        with patch.dict(os.environ, hostile_environment, clear=False):
            sanitized = verify_claims.clean_environment()
            require(
                all(
                    key not in sanitized
                    for key in hostile_environment
                    if key not in {"LC_ALL", "LANG", "LANGUAGE", "PATH"}
                ),
                "claims verifier retained a hostile selector",
            )
            require(
                sanitized["PATH"] == os.defpath,
                "claims verifier did not pin PATH",
            )
            require(
                sanitized["LC_ALL"] == "C.UTF-8"
                and sanitized["LANG"] == "C.UTF-8"
                and sanitized["LANGUAGE"] == "C.UTF-8",
                "claims verifier did not pin locale",
            )
            require(
                verify_claims.describe_environment({})["subprocess_environment"]
                == {
                    "contract": verify_claims.ENVIRONMENT_CONTRACT,
                    "sanitized_git_selectors": list(
                        verify_claims.SANITIZED_GIT_ENVIRONMENT_KEYS
                    ),
                    "sanitized_runtime_selectors": list(
                        verify_claims.SANITIZED_RUNTIME_ENVIRONMENT_KEYS
                    ),
                    "canonical_values": {
                        "PATH": os.defpath,
                        "LC_ALL": "C.UTF-8",
                        "LANG": "C.UTF-8",
                        "LANGUAGE": "C.UTF-8",
                    },
                },
                "claims verifier environment receipt drifted",
            )
            child = verify_claims.run(
                [
                    sys.executable,
                    "-c",
                    "import json, os; print(json.dumps({k: os.environ[k] for k in "
                    "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE', "
                    "'PYTHONPATH', 'PYTHONHOME', 'PYTHONOPTIMIZE', 'LC_ALL', "
                    "'LANG', 'LANGUAGE', 'PATH') "
                    "if k in os.environ}))",
                ],
                cwd=root,
            )
            require(child.returncode == 0, "claims verifier child process failed")
            require(
                json.loads(child.stdout)
                == {
                    "LC_ALL": "C.UTF-8",
                    "LANG": "C.UTF-8",
                    "LANGUAGE": "C.UTF-8",
                    "PATH": os.defpath,
                },
                "claims verifier child inherited ambient execution state",
            )

        # A claim register is untrusted input too: source and paper references
        # must not make the verifier follow a symlink or an absolute path out of
        # the checkout while trying to prove that the register is sound.
        outside_module = root.parent / "outside.lean"
        outside_module.write_text(SAMPLE_MODULE, encoding="utf-8")
        (root / "linked.lean").symlink_to(outside_module)
        report = run_case(
            root,
            build_register(
                [claim("Sample.alpha", ALPHA_KEYWORD_LINE, module="linked.lean")]
            ),
        )
        require(
            statuses(report) == {"module_missing"},
            "claims verifier followed a symlinked source path",
        )
        report = run_case(
            root,
            build_register(
                [claim("Sample.alpha", ALPHA_KEYWORD_LINE, module=str(outside_module))]
            ),
        )
        require(
            statuses(report) == {"module_missing"},
            "claims verifier accepted a source path outside the checkout",
        )

        # A wrapped declaration recorded at its keyword line must resolve, and a
        # namespaced declaration registered under its qualified name must too.
        for name, line, label in (
            ("Sample.alpha", ALPHA_KEYWORD_LINE, "wrapped namespaced theorem"),
            ("Sample.beta", BETA_LINE, "noncomputable def"),
        ):
            report = run_case(root, build_register([claim(name, line)]))
            if not report["verified"]:
                failures.append(f"{label}: sound register reported as broken {report['problems']}")

        # A shifted line is drift, and drift must be named.
        report = run_case(root, build_register([claim("Sample.alpha", 2)]))
        if "drifted" not in statuses(report):
            failures.append(f"shifted line not reported as drift: {report['problems']}")

        # A renamed declaration is a citation pointing at nothing.
        report = run_case(root, build_register([claim("Sample.gone", ALPHA_KEYWORD_LINE)]))
        if "declaration_missing" not in statuses(report):
            failures.append(f"renamed declaration not reported: {report['problems']}")

        # A status outside the declared taxonomy means the ceiling is undefined.
        report = run_case(
            root, build_register([claim("Sample.alpha", ALPHA_KEYWORD_LINE, "definitely true")])
        )
        if "status_outside_taxonomy" not in statuses(report):
            failures.append(f"undeclared status not reported: {report['problems']}")

        # An open proposition must not outlive the claim it targets.
        report = run_case(
            root,
            build_register(
                [claim("Sample.alpha", ALPHA_KEYWORD_LINE)],
                [{"id": "remaining_open.orphan", "open_target_claim": "deleted_claim"}],
            ),
        )
        if "open_proposition_targets_unknown_claim" not in statuses(report):
            failures.append(f"orphaned open proposition not reported: {report['problems']}")

        # The same edge on the Comparator side: a selected interface may name a
        # claim id, and that binding must not outlive the claim either.
        report = run_case(
            root,
            build_register(
                [claim("Sample.alpha", ALPHA_KEYWORD_LINE)],
                main_results=[{"id": "iface", "claim_id": "deleted_claim"}],
            ),
        )
        if "comparator_interface_targets_unknown_claim" not in statuses(report):
            failures.append(f"orphaned Comparator binding not reported: {report['problems']}")

        # A claim whose paper label no paper carries sends a reader after prose
        # that is not there.
        (root / "paper").mkdir(exist_ok=True)
        (root / "paper" / "sample.tex").write_text(
            "\\label{res:present}\n", encoding="utf-8"
        )
        report = run_case(
            root,
            build_register([claim("Sample.alpha", ALPHA_KEYWORD_LINE, paper_label="res:absent")]),
        )
        if "paper_label_resolves_to_no_paper" not in statuses(report):
            failures.append(f"unresolvable paper label not reported: {report['problems']}")

        # ...and a label a paper does carry is not reported.
        report = run_case(
            root,
            build_register([claim("Sample.alpha", ALPHA_KEYWORD_LINE, paper_label="res:present")]),
        )
        if not report["verified"]:
            failures.append(f"resolvable paper label reported as broken: {report['problems']}")

        # A paper label carried only by a symlink is not evidence from this
        # checkout and must not be indexed as though it were a committed paper.
        outside_paper = root.parent / "outside.tex"
        outside_paper.write_text("\\label{res:leaked}\n", encoding="utf-8")
        (root / "paper" / "linked.tex").symlink_to(outside_paper)
        report = run_case(
            root,
            build_register([claim("Sample.alpha", ALPHA_KEYWORD_LINE, paper_label="res:leaked")]),
        )
        if "paper_label_resolves_to_no_paper" not in statuses(report):
            failures.append(f"symlinked paper label was accepted: {report['problems']}")
        (root / "paper" / "linked.tex").unlink()

        # Absent paper sources are an environment fact, not a claim fault. A
        # checkout without the write-ups must still verify, or the exposition
        # check would convert a truncated clone into a broken register -- the
        # exact conflation this module separates everywhere else.
        (root / "paper" / "sample.tex").unlink()
        (root / "paper").rmdir()
        report = run_case(
            root,
            build_register([claim("Sample.alpha", ALPHA_KEYWORD_LINE, paper_label="res:absent")]),
        )
        if not report["verified"]:
            failures.append(f"absent paper sources reported as a claim fault: {report['problems']}")

    if failures:
        for failure in failures:
            print(f"  FAIL {failure}")
        return 1
    print(
        "test_verify_claims: drift, renames, undeclared statuses, orphaned open "
        "propositions, orphaned Comparator bindings, and unresolvable paper "
        "labels are each reported; absent paper sources are not"
    )
    return 0


if __name__ == "__main__":
    check_safe_read_boundary()
    raise SystemExit(main())
