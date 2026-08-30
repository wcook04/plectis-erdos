#!/usr/bin/env python3
"""Cold-path tests for ``continue_research.py`` composition and packaging."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from unittest import mock
from pathlib import Path

import continue_research
import route_memory_receipt
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / "scripts/continue_research.py"
WORKBENCH = ROOT / "scripts/proof_workbench.py"
RETURN_FIXTURE = ROOT / "scripts/fixtures/research_returns/valid_inconclusive.json"


def run(command: list[str], *, expected: int = 0) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(
        command,
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        env=continue_research.child_environment(),
        timeout=continue_research.COMPOSED_COMMAND_TIMEOUT_SECONDS,
    )
    assert completed.returncode == expected, (command, completed.stdout, completed.stderr)
    return completed


def require(condition: bool, message: object) -> None:
    """Keep the sidecar boundary assertion active under ``python3 -O``."""
    if not condition:
        raise AssertionError(message)


def load(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def check_session_artifact_links_rejected() -> None:
    with tempfile.TemporaryDirectory(prefix="continue-session-artifact-") as temporary:
        root = Path(temporary)
        sessions = root / "sessions"
        session = sessions / "session"
        outside = root / "outside"
        session.mkdir(parents=True)
        outside.mkdir()
        valid_manifest = outside / "continuation.json"
        valid_manifest.write_text(
            json.dumps(
                {
                    "schema": continue_research.SESSION_SCHEMA,
                    "session": "session",
                }
            ),
            encoding="utf-8",
        )
        (session / "continuation.json").symlink_to(valid_manifest)
        try:
            continue_research.load_session(sessions, "session")
        except SystemExit as error:
            require(
                "symbolic links" in str(error),
                f"manifest symlink rejection had no bounded diagnostic: {error}",
            )
        else:
            raise AssertionError("continuation loader followed a symlinked manifest")

        (session / "continuation.json").unlink()
        (session / "continuation.json").write_text(
            valid_manifest.read_text(encoding="utf-8"), encoding="utf-8"
        )
        outside_ledger = outside / "ledger.jsonl"
        outside_ledger.write_text("", encoding="utf-8")
        (session / "ledger.jsonl").symlink_to(outside_ledger)
        try:
            continue_research.read_ledger(session, sessions)
        except SystemExit as error:
            require(
                "symbolic links" in str(error),
                f"ledger symlink rejection had no bounded diagnostic: {error}",
            )
        else:
            raise AssertionError("continuation checker followed a symlinked ledger")


def check_replay_execution_posture() -> None:
    posture = continue_research.replay_execution_posture(replay=True, probe_count=2)
    assert posture == {
        **continue_research.CONTINUATION_REPLAY_EXECUTION_POSTURE,
        "replay_requested": True,
        "stored_probe_count": 2,
        "activated": True,
    }
    inactive = continue_research.replay_execution_posture(replay=True, probe_count=0)
    assert inactive["activated"] is False
    source = CLI.read_text(encoding="utf-8")
    assert "proof_workbench.py" in source
    assert "lake build" not in source
    assert "validation_singleflight.py" not in source
    workbench_source = WORKBENCH.read_text(encoding="utf-8")
    assert '["lake", "env", "lean", "--stdin", "--json"]' in workbench_source
    assert "timeout=PROBE_TIMEOUT_SECONDS" in workbench_source
    assert "lake build" not in workbench_source


def check_attached_git_context_scrubs_ref_state() -> None:
    hostile = {
        "GIT_DIR": str(ROOT / ".git"),
        "GIT_WORK_TREE": str(ROOT),
        "GIT_NAMESPACE": "attached-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/attached/",
        "GIT_INDEX_FILE": "/foreign/index",
        "PATH": "/foreign/bin",
        "PYTHONPATH": "/foreign/modules",
        "LANGUAGE": "fr_FR",
        "VALIDATION_SINGLEFLIGHT_STATE_ROOT": "/foreign/singleflight",
        **{
            key: f"/foreign/{key.lower()}"
            for key in continue_research.GIT_PROCESS_CONTROL_KEYS
        },
    }
    with mock.patch.dict(os.environ, hostile, clear=False):
        environment = continue_research.child_environment()
        expected = singleflight.command_environment()
    assert environment == expected
    assert "GIT_DIR" not in environment
    assert "GIT_WORK_TREE" not in environment
    assert "GIT_NAMESPACE" not in environment
    assert "GIT_REPLACE_REF_BASE" not in environment
    for key in continue_research.GIT_PROCESS_CONTROL_KEYS:
        if key in environment:
            raise AssertionError(f"continuation child environment retained {key}")


def check_subprocess_timeouts() -> None:
    require(
        continue_research.GIT_LOOKUP_TIMEOUT_SECONDS
        == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        "continuation Git timeout drifted from the canonical boundary",
    )
    completed = subprocess.CompletedProcess(
        ["fixture"], returncode=0, stdout="{}", stderr=""
    )
    with mock.patch.object(
        continue_research.subprocess, "run", return_value=completed
    ) as run_mock:
        assert continue_research.git_output("rev-parse", "HEAD") == "{}"
        assert continue_research.git_is_ancestor("a" * 40, "b" * 40)
        assert continue_research.run_json_command([sys.executable, "fixture.py"]) == {}
        assert run([sys.executable, "fixture.py"]).returncode == 0

    assert [
        call.kwargs["timeout"] for call in run_mock.call_args_list
    ] == [
        continue_research.GIT_LOOKUP_TIMEOUT_SECONDS,
        continue_research.GIT_LOOKUP_TIMEOUT_SECONDS,
        continue_research.COMPOSED_COMMAND_TIMEOUT_SECONDS,
        continue_research.COMPOSED_COMMAND_TIMEOUT_SECONDS,
    ]


def check_package_session_path_boundary() -> None:
    """A package must not read session material through a symbolic link."""
    with tempfile.TemporaryDirectory(prefix="continue-session-path-") as temporary:
        root = Path(temporary)
        sessions = root / "sessions"
        session = sessions / "t_public_continue"
        probes = session / "probes"
        probes.mkdir(parents=True)
        outside = root / "outside-secret.lean"
        outside.write_text("-- private source\n", encoding="utf-8")
        linked = probes / "linked.lean"
        linked.symlink_to(outside)
        try:
            continue_research.session_artifact_bytes(
                linked, sessions, "probe linked.lean"
            )
        except SystemExit as error:
            assert "must not traverse symbolic links" in str(error)
        else:
            raise AssertionError("package input must reject symlinked session material")

        redirected = root / "redirected"
        redirected.mkdir()
        linked_parent = sessions / "linked-parent"
        linked_parent.symlink_to(redirected, target_is_directory=True)
        hidden = linked_parent / ".." / "hidden.json"
        require(
            continue_research.has_symlink_component(hidden, sessions),
            "session path normalized away a symlink before resolving ..",
        )
        require(
            continue_research.output_path_has_symlink_component(hidden),
            "package output normalized away a symlink before resolving ..",
        )


def check_malformed_utf8_inputs_rejected() -> None:
    """Continuation readers must report malformed text as bounded input errors."""
    with tempfile.TemporaryDirectory(prefix="continue-malformed-utf8-") as temporary:
        root = Path(temporary)
        malformed = root / "malformed.json"
        malformed.write_bytes(b"{\xff\n")
        try:
            continue_research.load_json(malformed)
        except SystemExit as error:
            require("utf-8" in str(error).lower(), f"malformed JSON lacked a decode diagnostic: {error}")
        else:
            raise AssertionError("continuation JSON reader accepted malformed UTF-8")

        sessions = root / "sessions"
        session = sessions / "bounded"
        session.mkdir(parents=True)
        ledger = session / "ledger.jsonl"
        ledger.write_bytes(b"{\xff\n")
        try:
            continue_research.read_ledger(session, sessions)
        except SystemExit as error:
            require("utf-8" in str(error).lower(), f"malformed ledger lacked a decode diagnostic: {error}")
        else:
            raise AssertionError("continuation ledger reader accepted malformed UTF-8")


def check_route_memory_corpus_contract() -> None:
    """Canonical route memory must not silently change authority or identity shape."""
    source_document = json.loads(
        (ROOT / route_memory_receipt.ROUTE_MEMORY_PATH).read_text(encoding="utf-8")
    )
    mutations = (
        ("authority posture", {"authority_posture": "claim registry"}),
        ("top-level shape", {"claim_authority": "docs/claims.json"}),
        ("duplicate route identity", {"duplicate_route": True}),
    )
    for label, mutation in mutations:
        with tempfile.TemporaryDirectory(prefix="continue-route-memory-contract-") as temporary:
            root = Path(temporary)
            source = root / route_memory_receipt.ROUTE_MEMORY_PATH
            source.parent.mkdir(parents=True)
            document = json.loads(json.dumps(source_document))
            if label == "duplicate route identity":
                document["records"][1]["route_id"] = document["records"][0]["route_id"]
            else:
                document.update(mutation)
            payload = (json.dumps(document, ensure_ascii=False) + "\n").encode("utf-8")
            source.write_bytes(payload)
            committed = subprocess.CompletedProcess(
                ["git", "show"], 0, stdout=payload, stderr=b""
            )
            with mock.patch.object(
                route_memory_receipt.subprocess, "run", return_value=committed
            ):
                try:
                    route_memory_receipt.canonical_corpus(root)
                except ValueError as error:
                    require(
                        "authority" in str(error)
                        or "contract" in str(error)
                        or "identity" in str(error),
                        f"{label} rejection lacked a bounded diagnostic: {error}",
                    )
                else:
                    raise AssertionError(
                        f"canonical route memory accepted dishonest {label} mutation"
                    )


def check_route_memory_file_boundary() -> None:
    """Canonical route memory must reject final links and special files before Git comparison."""
    with tempfile.TemporaryDirectory(dir="/tmp", prefix="continue-route-memory-files-") as temporary:
        root = Path(temporary)
        source = root / route_memory_receipt.ROUTE_MEMORY_PATH
        source.parent.mkdir(parents=True)
        source.write_bytes(b"{}\n")
        require(
            route_memory_receipt.read_regular_bytes(source, root) == b"{}\n",
            "regular route-memory source was not readable through the safe descriptor",
        )

        linked = root / "linked-route-memory.json"
        linked.symlink_to(source)
        with mock.patch.object(route_memory_receipt, "path_has_symlink_component", return_value=False):
            try:
                route_memory_receipt.read_regular_bytes(linked, root)
            except ValueError as error:
                require(
                    "safely" in str(error) or "symbolic" in str(error),
                    f"final route-memory symlink rejection lacked a bounded diagnostic: {error}",
                )
            else:
                raise AssertionError("route-memory source followed a final-component symlink")

        fifo = root / "route-memory.fifo"
        os.mkfifo(fifo)
        with mock.patch.object(route_memory_receipt, "path_has_symlink_component", return_value=False):
            try:
                route_memory_receipt.read_regular_bytes(fifo, root)
            except ValueError as error:
                require(
                    "regular file" in str(error),
                    f"special route-memory file rejection lacked a bounded diagnostic: {error}",
                )
            else:
                raise AssertionError("route-memory source accepted a special file")


def check_nested_return_shape_boundary() -> None:
    """Malformed nested return objects must remain validation errors, not crashes."""
    manifest = {
        "repository_origin": "https://github.com/wcook04/plectis-lean-erdos249-257",
        "starting_commit": "0" * 40,
        "problem": 257,
        "frontier": {"handle": "bounded", "intent": "question", "stop_condition": "stop"},
        "identity": {
            "contributor": {"name": "Contributor"},
            "operator": {"relationship": "same_as_contributor", "name": "Contributor"},
            "model_system": {"state": "not_used"},
            "provider": {"state": "not_used"},
            "material_collaborators": [],
        },
    }
    for malformed in (
        {"repository": "corrupt", "frontier": "corrupt", "identity": "corrupt"},
        {
            "repository": {},
            "frontier": {},
            "identity": {
                "contributor": "corrupt",
                "operator": "corrupt",
                "model_system": "corrupt",
                "provider": "corrupt",
                "material_collaborators": "corrupt",
            },
        },
    ):
        errors = continue_research.cross_check_return(manifest, malformed)
        require(errors, "cross-check accepted malformed nested return objects")

    route_errors = continue_research.route_memory_receipt.validate_return_receipt(
        {},
        {"return_id": "rr-shape-boundary", "frontier": "corrupt"},
        None,
        ROOT,
    )
    require(route_errors, "route-memory validator crashed or accepted a malformed frontier")


def check_changed_evidence_shape_boundary() -> None:
    """Malformed changed-evidence JSON must reject without crashing the rail."""
    consultation = route_memory_receipt.consultation_for_problem(249, ROOT)
    template = route_memory_receipt.return_receipt_template(consultation)
    returned = {
        "return_id": "rr-malformed-changed-evidence",
        "frontier": {"problem": 249},
        "repository": {"changed_paths": ["docs/example.txt"]},
    }
    for malformed in ({}, [], ["docs/example.txt", {}]):
        value = json.loads(json.dumps(template))
        value["return_id"] = returned["return_id"]
        value["relationships"][0]["relationship"] = "supersedes"
        value["relationships"][0]["changed_evidence"] = malformed
        errors = route_memory_receipt.validate_return_receipt(
            value, returned, consultation, ROOT
        )
        require(errors, "malformed changed_evidence escaped route-memory validation")
        require(
            any("changed_evidence" in error for error in errors),
            "changed_evidence rejection omitted its field diagnostic",
        )
    for noncanonical in (
        "docs/./ambiguous.txt",
        "docs//ambiguous.txt",
    ):
        value = json.loads(json.dumps(template))
        value["return_id"] = returned["return_id"]
        value["relationships"][0]["relationship"] = "supersedes"
        value["relationships"][0]["changed_evidence"] = [noncanonical]
        noncanonical_return = dict(returned)
        noncanonical_return["repository"] = {"changed_paths": [noncanonical]}
        errors = route_memory_receipt.validate_return_receipt(
            value, noncanonical_return, consultation, ROOT
        )
        require(
            any("canonical repository-relative path" in error for error in errors),
            f"noncanonical route-memory evidence path {noncanonical!r} was accepted",
        )


def check_start_session_path_boundary() -> None:
    """A start must reject a redirected sessions root before opening the workbench."""
    with tempfile.TemporaryDirectory(prefix="continue-start-path-") as temporary:
        root = Path(temporary)
        real_sessions = root / "real-sessions"
        real_sessions.mkdir()
        linked_sessions = root / "linked-sessions"
        linked_sessions.symlink_to(real_sessions, target_is_directory=True)
        completed = run(
            [
                sys.executable,
                str(CLI),
                "--sessions-root",
                str(linked_sessions),
                "start",
                "--session",
                "symlinked_start",
                "--problem",
                "257",
                "--frontier",
                "fixture/bounded-return",
                "--intent",
                "exercise the public continuation package",
                "--stop-condition",
                "stop after one structurally valid inconclusive return",
                "--contributor",
                "Symlink Start Contributor",
                "--model-system",
                "not_used",
                "--provider",
                "not_used",
                "--allow-dirty",
            ],
            expected=1,
        )
        require(
            "session output must not traverse symbolic links" in completed.stderr,
            f"start path rejection omitted its diagnostic: {completed.stderr}",
        )
        require(
            not any(real_sessions.iterdir()),
            "start invoked workbench or wrote artifacts before rejecting the path",
        )


def check_replay_command_boundary(sessions_root: Path, session: str) -> None:
    """Exercise the optional replay consumer without launching Lean."""
    session_directory = sessions_root / session
    source = "-- replay boundary fixture\n"
    probe_path = session_directory / "probes" / "replay-boundary.lean"
    probe_path.write_text(source, encoding="utf-8")
    probe_record = {
        "schema": "workbench-move/1",
        "move_id": "m004",
        "at": "2026-08-28T00:00:00+00:00",
        "kind": "probe",
        "input_path": "probes/replay-boundary.lean",
        "input_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
        "label": "bounded replay boundary fixture",
        "kernel_receipt": {
            "verdict": "kernel_accepted",
            "detail": None,
            "exit_code": 0,
            "error_count": 0,
            "sorry_count": 0,
        },
    }
    with (session_directory / "ledger.jsonl").open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(probe_record, sort_keys=True) + "\n")

    captured_commands: list[list[str]] = []

    def fake_run_json_command(command: list[str]) -> dict:
        captured_commands.append(command)
        return {
            "schema": "workbench-replay-receipt/1",
            "session": session,
            "probes_replayed": 1,
            "all_match": True,
            "results": [
                {
                    "move_id": "m004",
                    "recorded_verdict": "kernel_accepted",
                    "replayed_verdict": "kernel_accepted",
                    "replay": "match",
                }
            ],
        }

    with mock.patch.object(
        continue_research, "run_json_command", side_effect=fake_run_json_command
    ):
        receipt, returned = continue_research.check_session(
            sessions_root,
            session,
            None,
            None,
            replay=True,
            require_closed=False,
        )

    assert returned is None
    assert receipt["valid"]
    assert receipt["replay"]["state"] == "reproduced"
    assert receipt["replay"]["probes_replayed"] == 1
    assert receipt["execution_posture"]["activated"] is True
    assert receipt["execution_posture"]["classification"] == "bounded_disjoint_stdin_probe"
    assert captured_commands == [
        [
            sys.executable,
            str(WORKBENCH),
            "--sessions-root",
            str(sessions_root),
            "replay",
            "--session",
            session,
        ]
    ]


def main() -> int:
    require(
        continue_research.PROBLEMS is continue_research.route_memory_receipt.ROSTER,
        "continuation selector roster must reuse route-memory authority",
    )
    check_session_artifact_links_rejected()
    check_attached_git_context_scrubs_ref_state()
    check_subprocess_timeouts()
    check_replay_execution_posture()
    check_package_session_path_boundary()
    check_malformed_utf8_inputs_rejected()
    check_route_memory_corpus_contract()
    check_route_memory_file_boundary()
    check_nested_return_shape_boundary()
    check_changed_evidence_shape_boundary()
    check_start_session_path_boundary()
    assert continue_research.canonical_github_origin(
        "git@github.com:wcook04/plectis-lean-erdos249-257.git"
    ) == "https://github.com/wcook04/plectis-lean-erdos249-257"
    assert continue_research.canonical_github_origin(
        "https://github.com/wcook04/plectis-lean-erdos249-257"
    ) == "https://github.com/wcook04/plectis-lean-erdos249-257"
    with tempfile.TemporaryDirectory() as temporary:
        temp = Path(temporary)
        environment_probe = temp / "environment_probe.py"
        environment_probe.write_text(
            "import json, os\n"
            "print(json.dumps({key: os.environ.get(key, 'absent') for key in "
            "('PYTHONPATH', 'PYTHONNOUSERSITE', 'PYTHONDONTWRITEBYTECODE', "
            "'PYTHONUTF8', 'GIT_ASKPASS')}))\n",
            encoding="utf-8",
        )
        original_python_environment = {
            key: os.environ.get(key)
            for key in (
                "PYTHONPATH",
                "PYTHONNOUSERSITE",
                "PYTHONDONTWRITEBYTECODE",
                "PYTHONUTF8",
                "GIT_ASKPASS",
            )
        }
        os.environ["PYTHONPATH"] = "/private/test-only/imports"
        os.environ.pop("PYTHONNOUSERSITE", None)
        os.environ.pop("PYTHONDONTWRITEBYTECODE", None)
        os.environ["GIT_ASKPASS"] = "/private/test-only/askpass"
        try:
            observed_environment = continue_research.run_json_command(
                [sys.executable, str(environment_probe)]
            )
        finally:
            for key, value in original_python_environment.items():
                if value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = value
        assert observed_environment == {
            "PYTHONPATH": "absent",
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONUTF8": "1",
            "GIT_ASKPASS": "/bin/false",
        }

        sessions = temp / "sessions"
        session = "t_public_continue"
        unsafe_session = "t_private_note"
        common = [sys.executable, str(CLI), "--sessions-root", str(sessions)]
        started = run(
            [
                *common,
                "start",
                "--session",
                session,
                "--problem",
                "257",
                "--frontier",
                "fixture/bounded-return",
                "--intent",
                "exercise the public continuation package",
                "--stop-condition",
                "stop after one structurally valid inconclusive return",
                "--contributor",
                "Fixture Contributor",
                "--model-system",
                "Fixture Model",
                "--provider",
                "Fixture Provider",
                "--material-collaborator",
                "Fixture Collaborator::verification",
                "--allow-dirty",
            ]
        )
        start_receipt = json.loads(started.stdout)
        assert start_receipt["schema"] == "research-continuation-start/1"
        package_next = [
            command
            for command in start_receipt["next"]
            if command.startswith("python3 scripts/continue_research.py package")
        ]
        assert len(package_next) == 1
        assert "--route-memory-receipt <route-memory-return.json>" in package_next[0]
        manifest = load(sessions / session / "continuation.json")
        assert manifest["starting_commit"] == start_receipt["starting_commit"]
        assert manifest["repository_origin"] == start_receipt["repository_origin"]
        assert manifest["identity"]["model_system"] == {
            "state": "disclosed",
            "name": "Fixture Model",
        }
        assert manifest["identity"]["provider"] == {
            "state": "disclosed",
            "name": "Fixture Provider",
        }
        assert manifest["identity"]["material_collaborators"] == [
            {"name": "Fixture Collaborator", "role": "verification"}
        ]
        assert (sessions / session / "route.json").is_file()
        shutil.copytree(sessions / session, sessions / unsafe_session)
        unsafe_manifest_path = sessions / unsafe_session / "continuation.json"
        unsafe_manifest = load(unsafe_manifest_path)
        unsafe_manifest["session"] = unsafe_session
        unsafe_manifest_path.write_text(
            json.dumps(unsafe_manifest, indent=2) + "\n", encoding="utf-8"
        )

        run(
            [
                sys.executable,
                str(WORKBENCH),
                "--sessions-root",
                str(sessions),
                "close",
                "--session",
                session,
                "--outcome",
                "open",
                "--summary",
                "fixture stopped at its declared boundary",
            ]
        )

        returned = load(RETURN_FIXTURE)
        returned["record_kind"] = "submitted_return"
        returned["return_id"] = "rr-fixture-cli-inconclusive"
        returned["repository"]["starting_commit"] = manifest["starting_commit"]
        returned["repository"]["origin"] = manifest["repository_origin"]
        returned["frontier"]["problem"] = 257
        returned["frontier"]["handle"] = "fixture/bounded-return"
        returned["frontier"]["bounded_question"] = manifest["frontier"]["intent"]
        returned["frontier"]["stop_condition"] = manifest["frontier"]["stop_condition"]
        returned["identity"]["contributor"]["name"] = "Fixture Contributor"
        returned["identity"]["model_system"] = {
            "state": "disclosed",
            "name": "Fixture Model",
            "version": "fixture-version",
        }
        returned["identity"]["provider"] = {
            "state": "disclosed",
            "name": "Fixture Provider",
        }
        returned["identity"]["material_collaborators"] = [
            {"name": "Fixture Collaborator", "role": "verification"}
        ]
        return_path = temp / "return.json"
        return_path.write_text(json.dumps(returned, indent=2) + "\n", encoding="utf-8")
        route_memory_receipt = load(
            sessions / session / "route-memory-return-template.json"
        )
        route_memory_receipt["return_id"] = returned["return_id"]
        route_memory_receipt_path = temp / "route-memory-return.json"
        route_memory_receipt_path.write_text(
            json.dumps(route_memory_receipt, indent=2) + "\n", encoding="utf-8"
        )
        linked_route_memory_receipt_path = temp / "linked-route-memory-return.json"
        linked_route_memory_receipt_path.symlink_to(route_memory_receipt_path)
        symlink_check = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(return_path),
                "--route-memory-receipt",
                str(linked_route_memory_receipt_path),
            ],
            expected=1,
        )
        assert "must not traverse symbolic links" in symlink_check.stdout

        checked = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(return_path),
                "--route-memory-receipt",
                str(route_memory_receipt_path),
            ]
        )
        check_receipt = json.loads(checked.stdout)
        assert check_receipt["valid"]
        assert check_receipt["problem"] == manifest["problem"]
        assert check_receipt["route_memory"] == {
            "path": route_memory_receipt["route_memory"]["path"],
            "digest": route_memory_receipt["route_memory"]["sha256"],
            "route_ids": [
                relationship["route_id"]
                for relationship in route_memory_receipt["relationships"]
            ],
            "receipt_supplied": True,
        }
        assert check_receipt["workbench"]["closed"]
        assert check_receipt["replay"]["state"] == "not_applicable"
        assert check_receipt["execution_posture"] == {
            **continue_research.CONTINUATION_REPLAY_EXECUTION_POSTURE,
            "replay_requested": False,
            "stored_probe_count": 0,
            "activated": False,
        }

        # The manifest, persisted consultation, and fillable return template
        # are one immutable route-memory identity.  Mutating any one artifact
        # must fail closed before a return can be accepted.
        session_directory = sessions / session
        continuation_path = session_directory / "continuation.json"
        consultation_path = session_directory / "route-memory-consultation.json"
        template_path = session_directory / "route-memory-return-template.json"
        continuation_bytes = continuation_path.read_bytes()
        consultation_bytes = consultation_path.read_bytes()
        template_bytes = template_path.read_bytes()

        def check_identity_mutation(
            path: Path, payload: dict, marker: str, original: bytes
        ) -> None:
            path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
            try:
                mutated = run([*common, "check", "--session", session], expected=1)
                mutated_receipt = json.loads(mutated.stdout)
                require(not mutated_receipt["valid"], f"mutation unexpectedly accepted: {path}")
                require(
                    any(marker in error for error in mutated_receipt["errors"]),
                    f"mutation missing {marker!r}: {mutated_receipt['errors']}",
                )
            finally:
                path.write_bytes(original)

        manifest_mutation = load(continuation_path)
        manifest_mutation["route_memory"] = (
            continue_research.route_memory_receipt.consultation_for_problem(249, ROOT)
        )
        check_identity_mutation(
            continuation_path,
            manifest_mutation,
            "persisted artifact does not match continuation manifest",
            continuation_bytes,
        )

        consultation_mutation = load(consultation_path)
        consultation_mutation["problem"] = 249
        check_identity_mutation(
            consultation_path,
            consultation_mutation,
            "problem does not match continuation manifest",
            consultation_bytes,
        )

        template_mutation = load(template_path)
        if template_mutation["relationships"]:
            template_mutation["relationships"][0]["relationship"] = "confirms"
        else:
            template_mutation["disposition"] = "no_applicable_route"
        check_identity_mutation(
            template_path,
            template_mutation,
            "does not match canonical consultation",
            template_bytes,
        )

        validation_fixture = json.loads(json.dumps(returned))
        validation_fixture["record_kind"] = "validation_fixture"
        validation_fixture_path = temp / "validation-fixture.json"
        validation_fixture_path.write_text(
            json.dumps(validation_fixture, indent=2) + "\n", encoding="utf-8"
        )
        fixture_check = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(validation_fixture_path),
                "--route-memory-receipt",
                str(route_memory_receipt_path),
            ],
            expected=1,
        )
        fixture_check_receipt = json.loads(fixture_check.stdout)
        assert not fixture_check_receipt["valid"]
        assert "record_kind: --require-submitted requires submitted_return" in (
            fixture_check_receipt["errors"]
        )
        check_replay_command_boundary(sessions, session)

        package = temp / "package"
        packaged = run(
            [
                *common,
                "package",
                "--session",
                session,
                "--return-json",
                str(return_path),
                "--route-memory-receipt",
                str(route_memory_receipt_path),
                "--output",
                str(package),
            ]
        )
        package_result = json.loads(packaged.stdout)
        assert package_result["valid"]
        package_manifest = load(package / "package.json")
        assert package_manifest["schema"] == "research-return-package/1"
        assert package_manifest["repository_origin"] == manifest["repository_origin"]
        assert package_manifest["problem"] == manifest["problem"]
        assert package_manifest["route_memory"] == {
            "source": route_memory_receipt["route_memory"],
            "disposition": route_memory_receipt["disposition"],
            "relationships": route_memory_receipt["relationships"],
        }
        return_index = package_manifest["return_index"]
        assert return_index["source"] == "return.json"
        assert return_index["identity"] == returned["identity"]
        assert return_index["repository"] == {
            "starting_commit": returned["repository"]["starting_commit"],
            "proposed_commit": returned["repository"]["proposed_commit"],
            "accepted_commit": returned["repository"]["accepted_commit"],
            "changed_paths": returned["repository"]["changed_paths"],
        }
        assert return_index["result"] == {
            "class": returned["result"]["class"],
            "claim_ceiling": returned["result"]["claim_ceiling"],
            "requested_disposition": returned["result"]["requested_disposition"],
        }
        assert return_index["evidence"] == [
            {
                "exit_state": evidence["exit_state"],
                "replay_state": evidence["replay_state"],
            }
            for evidence in returned["evidence"]
        ]
        assert return_index["review"] == {
            name: decision["state"] for name, decision in returned["review"].items()
        }
        assert package_manifest["github_intake"]["issue_form"] == ".github/ISSUE_TEMPLATE/research_return.yml"
        assert package_manifest["github_intake"]["pull_request_artifact"] == "return.json"
        assert package_manifest["github_intake"]["pull_request_route_memory_receipt"] == "route-memory.json"
        assert package_manifest["github_intake"]["accepted_receipt_directory"] == "docs/research-commons/returns"
        assert package_manifest["github_intake"]["local_validation"].endswith(
            "--require-submitted --check-git --require-route-memory-receipt "
            "--route-memory-receipt route-memory.json"
        )
        assert "pull_request_receipt_path" not in package_manifest["github_intake"]
        assert package_manifest["public_guidance"] == {
            "continuation_guide": "docs/AGENT_WORKBENCH.md",
            "return_template": "docs/research-commons/RETURN_PACKAGE_TEMPLATE.md",
            "resume_state_template": (
                "docs/research-commons/RETURN_PACKAGE_TEMPLATE.md#6-resume-state-and-promotion-request"
            ),
            "credit_policy": "docs/research-commons/CONTRIBUTION_RECOGNITION.md",
            "frontier_handoff_example": (
                "docs/research-commons/RETURN_PACKAGE_TEMPLATE.md#formal-handoff-from-exposition"
            ),
            "correction_lineage": (
                "docs/research-commons/RETURN_PACKAGE_TEMPLATE.md#correction-lineage"
            ),
        }
        for guidance in package_manifest["public_guidance"].values():
            guidance_path = ROOT / guidance.split("#", 1)[0]
            require(
                guidance_path.is_file(),
                f"package public guidance points at missing tracked file: {guidance}",
            )
        for row in package_manifest["files"]:
            data = (package / row["path"]).read_bytes()
            assert hashlib.sha256(data).hexdigest() == row["sha256"]
        for artifact in package.rglob("*"):
            if artifact.is_file():
                assert temporary not in artifact.read_text(encoding="utf-8")

        real_session_directory = sessions / "t_public_continue-real"
        session_directory = sessions / session
        session_directory.rename(real_session_directory)
        session_directory.symlink_to(real_session_directory, target_is_directory=True)
        try:
            linked_session = run(
                [
                    *common,
                    "check",
                    "--session",
                    session,
                    "--return-json",
                    str(return_path),
                    "--route-memory-receipt",
                    str(route_memory_receipt_path),
                ],
                expected=1,
            )
            assert "must not traverse symbolic links" in linked_session.stderr
        finally:
            session_directory.unlink()
            real_session_directory.rename(session_directory)

        external_return = temp / "external-return.json"
        external_return.write_text(return_path.read_text(encoding="utf-8"), encoding="utf-8")
        linked_return = temp / "linked-return.json"
        linked_return.symlink_to(external_return)
        linked_return_check = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(linked_return),
                "--route-memory-receipt",
                str(route_memory_receipt_path),
            ],
            expected=1,
        )
        linked_return_payload = json.loads(linked_return_check.stdout)
        require(not linked_return_payload["valid"], linked_return_payload)
        require(
            any(
                "return path must not traverse symbolic links" in error
                for error in linked_return_payload["errors"]
            ),
            linked_return_payload,
        )

        return_directory = temp / "return-directory"
        return_directory.mkdir()
        directory_return = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(return_directory),
                "--route-memory-receipt",
                str(route_memory_receipt_path),
            ],
            expected=1,
        )
        directory_return_payload = json.loads(directory_return.stdout)
        require(not directory_return_payload["valid"], directory_return_payload)
        require(
            any(
                "return: cannot read JSON" in error
                for error in directory_return_payload["errors"]
            ),
            directory_return_payload,
        )

        route_memory_directory = temp / "route-memory-directory"
        route_memory_directory.mkdir()
        directory_receipt = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(return_path),
                "--route-memory-receipt",
                str(route_memory_directory),
            ],
            expected=1,
        )
        directory_payload = json.loads(directory_receipt.stdout)
        require(not directory_payload["valid"], directory_payload)
        require(
            any(
                "route-memory receipt: cannot read JSON" in error
                for error in directory_payload["errors"]
            ),
            directory_payload,
        )

        outside_package_target = temp / "outside-package-target"
        outside_package_target.mkdir()
        linked_package_output = temp / "linked-package-output"
        linked_package_output.symlink_to(
            outside_package_target / "not-created", target_is_directory=True
        )
        linked_package = run(
            [
                *common,
                "package",
                "--session",
                session,
                "--return-json",
                str(return_path),
                "--route-memory-receipt",
                str(route_memory_receipt_path),
                "--output",
                str(linked_package_output),
            ],
            expected=1,
        )
        assert "must not traverse symbolic links" in linked_package.stderr
        assert not (outside_package_target / "not-created").exists()

        run(
            [
                sys.executable,
                str(WORKBENCH),
                "--sessions-root",
                str(sessions),
                "note",
                "--session",
                unsafe_session,
                "--kind",
                "observation",
                "--text",
                "/Users/example/private-note",
            ]
        )
        run(
            [
                sys.executable,
                str(WORKBENCH),
                "--sessions-root",
                str(sessions),
                "close",
                "--session",
                unsafe_session,
                "--outcome",
                "open",
                "--summary",
                "fixture stopped at its declared boundary",
            ]
        )
        unsafe = run(
            [
                *common,
                "package",
                "--session",
                unsafe_session,
                "--return-json",
                str(return_path),
                "--route-memory-receipt",
                str(route_memory_receipt_path),
                "--output",
                str(temp / "unsafe-package"),
            ],
            expected=1,
        )
        assert "private path" in unsafe.stderr
        assert not (temp / "unsafe-package").exists()

        missing_check_receipt = run(
            [*common, "check", "--session", session, "--return-json", str(return_path)],
            expected=1,
        )
        assert "route-memory receipt is required" in missing_check_receipt.stdout

        mismatched = dict(returned)
        mismatched["repository"] = dict(returned["repository"])
        mismatched["repository"]["starting_commit"] = "0" * 40
        mismatch_path = temp / "mismatch.json"
        mismatch_path.write_text(json.dumps(mismatched), encoding="utf-8")
        mismatch = run(
            [*common, "check", "--session", session, "--return-json", str(mismatch_path)],
            expected=1,
        )
        assert "does not match the opened continuation session" in mismatch.stdout

        wrong_origin = json.loads(json.dumps(returned))
        wrong_origin["repository"]["origin"] = "https://github.com/example/different-repository"
        wrong_origin_path = temp / "wrong-origin.json"
        wrong_origin_path.write_text(json.dumps(wrong_origin), encoding="utf-8")
        origin_mismatch = run(
            [*common, "check", "--session", session, "--return-json", str(wrong_origin_path)],
            expected=1,
        )
        assert "repository.origin" in origin_mismatch.stdout

        missing_proposed = json.loads(json.dumps(returned))
        missing_proposed["repository"]["proposed_commit"] = "f" * 40
        missing_proposed_path = temp / "missing-proposed.json"
        missing_proposed_path.write_text(json.dumps(missing_proposed), encoding="utf-8")
        proposed_missing = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(missing_proposed_path),
            ],
            expected=1,
        )
        assert "commit is not present in this checkout" in proposed_missing.stdout

        ancestor_proposed = json.loads(json.dumps(returned))
        ancestor_proposed["repository"]["proposed_commit"] = run(
            ["git", "rev-parse", f"{manifest['starting_commit']}^"]
        ).stdout.strip()
        ancestor_proposed_path = temp / "ancestor-proposed.json"
        ancestor_proposed_path.write_text(json.dumps(ancestor_proposed), encoding="utf-8")
        proposed_not_descendant = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(ancestor_proposed_path),
            ],
            expected=1,
        )
        assert "not a descendant" in proposed_not_descendant.stdout

        changed_question = json.loads(json.dumps(returned))
        changed_question["frontier"]["bounded_question"] = "silently broaden the initialized task"
        changed_question_path = temp / "changed-question.json"
        changed_question_path.write_text(
            json.dumps(changed_question), encoding="utf-8"
        )
        question_mismatch = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(changed_question_path),
            ],
            expected=1,
        )
        assert "frontier.bounded_question" in question_mismatch.stdout

        changed_stop = json.loads(json.dumps(returned))
        changed_stop["frontier"]["stop_condition"] = "continue beyond the initialized boundary"
        changed_stop_path = temp / "changed-stop-condition.json"
        changed_stop_path.write_text(json.dumps(changed_stop), encoding="utf-8")
        stop_mismatch = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(changed_stop_path),
            ],
            expected=1,
        )
        assert "frontier.stop_condition" in stop_mismatch.stdout

        changed_disclosure = json.loads(json.dumps(returned))
        changed_disclosure["identity"]["provider"]["name"] = "Different Provider"
        changed_disclosure_path = temp / "changed-disclosure.json"
        changed_disclosure_path.write_text(
            json.dumps(changed_disclosure), encoding="utf-8"
        )
        disclosure_mismatch = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(changed_disclosure_path),
            ],
            expected=1,
        )
        assert "identity.provider.name" in disclosure_mismatch.stdout

        missing_collaborator = json.loads(json.dumps(returned))
        missing_collaborator["identity"]["material_collaborators"] = []
        missing_collaborator_path = temp / "missing-collaborator.json"
        missing_collaborator_path.write_text(
            json.dumps(missing_collaborator), encoding="utf-8"
        )
        collaborator_mismatch = run(
            [
                *common,
                "check",
                "--session",
                session,
                "--return-json",
                str(missing_collaborator_path),
            ],
            expected=1,
        )
        assert "opened-session collaborator" in collaborator_mismatch.stdout

    print(
        json.dumps(
            {
                "schema": "continue-research-test/1",
                "passed": True,
                "transitions": ["start", "check", "package"],
                "adversarial_rejections": [
                    "generation_mismatch",
                    "bounded_question_mismatch",
                    "stop_condition_mismatch",
                    "repository_origin_mismatch",
                    "proposed_commit_not_present",
                    "proposed_commit_not_descendant",
                    "identity_disclosure_mismatch",
                    "missing_initial_collaborator",
                    "private_session_material",
                    "directory_route_memory_receipt",
                    "route_memory_source_final_symlink_and_special_file",
                    "symlink_return_input",
                    "directory_return_input",
                ],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
