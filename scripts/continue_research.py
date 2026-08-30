#!/usr/bin/env python3
"""Compose the public continuation path without replacing its instruments.

``start`` records one bounded, attributable session after routing through
``query_corpus.py`` and opening ``proof_workbench.py``. ``check`` joins a
filled return to that session and optionally invokes the existing workbench
replay command. ``package`` emits a plain directory suitable for an ordinary
issue attachment or pull-request artifact. No command recorded by a return is
ever executed here.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import validate_research_return as return_validator
import route_memory_receipt
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
DEFAULT_SESSIONS_ROOT = ROOT / "workbench" / "sessions"
SESSION_SCHEMA = "research-continuation-session/1"
CHECK_SCHEMA = "research-continuation-check/1"
PACKAGE_SCHEMA = "research-return-package/1"
# The route-memory receipt owns the frozen public roster.  Reuse that exact
# object here so continuation selection cannot drift from the canonical route
# authority as the corpus evolves.
PROBLEMS = route_memory_receipt.ROSTER
GIT_LOOKUP_TIMEOUT_SECONDS = singleflight.GIT_COMMAND_TIMEOUT_SECONDS
COMPOSED_COMMAND_TIMEOUT_SECONDS = 120
PYTHON_AMBIENT_KEYS = (
    "PYTHONHOME",
    "PYTHONPATH",
    "PYTHONSTARTUP",
    "PYTHONUSERBASE",
    "PYTHONBREAKPOINT",
    "PYTHONWARNINGS",
    "PYTHONHASHSEED",
    "LC_ALL",
    "LANG",
    "LANGUAGE",
)
GIT_CONTEXT_KEYS = frozenset(
    {
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_CEILING_DIRECTORIES",
        "GIT_DISCOVERY_ACROSS_FILESYSTEM",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
    }
)
GIT_PROCESS_CONTROL_KEYS = return_validator.GIT_PROCESS_CONTROL_KEYS
SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{2,80}$")
RESULT_TO_CLOSE_OUTCOME = {
    "checked_positive": {"established"},
    "negative": {"established", "abandoned"},
    "inconclusive": {"open", "abandoned"},
    "corrective": {"established"},
}

# ``check --replay`` and ``package --replay`` invoke the existing workbench's
# one-input stdin probe.  This is intentionally not a repository build or a
# release validator: the workbench owns the per-probe timeout, while this
# wrapper records only the session-scoped replay result.  Keep the boundary
# machine-readable so callers do not mistake a bounded probe for canonical
# single-flight Lean evidence.
CONTINUATION_REPLAY_EXECUTION_POSTURE = {
    "schema": "public-validation-execution-posture/1",
    "classification": "bounded_disjoint_stdin_probe",
    "consumer": "scripts/continue_research.py::{check,package} --replay",
    "ci_only": False,
    "single_flight_required": False,
    "bounded_per_stored_input": True,
    "probe_timeout_owner": "scripts/proof_workbench.py::run_lean_probe",
    "repository_build": False,
    "shared_build_cache": False,
    "release_evidence": False,
    "runtime_write_scope": "session_scoped_replay_receipt_and_package_output",
    "clone_or_worktree": False,
    "external_mutation": False,
}


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")


def dump_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise SystemExit(f"cannot read JSON {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise SystemExit(f"expected a JSON object: {path}")
    return value


def git_output(*args: str) -> str:
    command = ["git", *args]
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
            env=git_environment(),
            timeout=GIT_LOOKUP_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as error:
        raise SystemExit(
            f"git lookup timed out after {GIT_LOOKUP_TIMEOUT_SECONDS} seconds: {' '.join(command)}"
        ) from error
    if completed.returncode != 0:
        raise SystemExit(completed.stderr.strip() or f"git {' '.join(args)} failed")
    return completed.stdout.strip()


def git_is_ancestor(ancestor: str, descendant: str) -> bool:
    command = ["git", "merge-base", "--is-ancestor", ancestor, descendant]
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
            env=git_environment(),
            timeout=GIT_LOOKUP_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as error:
        raise SystemExit(
            f"git lookup timed out after {GIT_LOOKUP_TIMEOUT_SECONDS} seconds: {' '.join(command)}"
        ) from error
    return completed.returncode == 0


def canonical_github_origin(value: str) -> str:
    text = value.strip().rstrip("/")
    prefixes = (
        "git@github.com:",
        "ssh://git@github.com/",
        "https://github.com/",
    )
    path = next((text.removeprefix(prefix) for prefix in prefixes if text.startswith(prefix)), None)
    if path is None:
        raise SystemExit("origin must be a public GitHub SSH or HTTPS repository URL")
    if path.endswith(".git"):
        path = path[:-4]
    if re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", path) is None:
        raise SystemExit("origin must identify exactly one GitHub owner/repository")
    return f"https://github.com/{path}"


def child_environment() -> dict[str, str]:
    """Run composed public tools through the canonical command boundary."""
    return singleflight.command_environment()


def git_environment() -> dict[str, str]:
    """Run direct Git reads without caller repository or object remapping state."""
    return child_environment()


def run_json_command(command: list[str]) -> dict[str, Any]:
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
            env=child_environment(),
            timeout=COMPOSED_COMMAND_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as error:
        raise SystemExit(
            "composed command timed out after "
            f"{COMPOSED_COMMAND_TIMEOUT_SECONDS} seconds: {' '.join(command)}"
        ) from error
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise SystemExit(f"command failed ({completed.returncode}): {' '.join(command[1:3])}: {detail}")
    try:
        value = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"command did not return JSON: {' '.join(command[1:3])}") from exc
    if not isinstance(value, dict):
        raise SystemExit(f"command returned non-object JSON: {' '.join(command[1:3])}")
    return value


def workbench_command(sessions_root: Path, *args: str) -> list[str]:
    return [
        sys.executable,
        str(SCRIPTS / "proof_workbench.py"),
        "--sessions-root",
        str(sessions_root),
        *args,
    ]


def replay_execution_posture(*, replay: bool, probe_count: int) -> dict[str, Any]:
    """Describe the bounded replay boundary consumed by a check receipt."""
    posture = dict(CONTINUATION_REPLAY_EXECUTION_POSTURE)
    posture.update(
        {
            "replay_requested": replay,
            "stored_probe_count": probe_count,
            "activated": replay and probe_count > 0,
        }
    )
    return posture


def validate_slug(slug: str) -> None:
    if not SLUG_RE.fullmatch(slug):
        raise SystemExit("session must match [a-z0-9][a-z0-9_-]{2,80}")


def disclosure(value: str) -> dict[str, str]:
    if value in {"undisclosed", "not_used"}:
        return {"state": value}
    return {"state": "disclosed", "name": value}


def material_collaborator(value: str) -> dict[str, str]:
    name, separator, role = value.partition("::")
    if not separator or not name.strip() or not role.strip():
        raise argparse.ArgumentTypeError(
            "material collaborator must use non-empty NAME::ROLE"
        )
    return {"name": name.strip(), "role": role.strip()}


def session_dir(sessions_root: Path, slug: str) -> Path:
    validate_slug(slug)
    return sessions_root / slug


def cleanup_partial_start(directory: Path) -> str | None:
    """Remove only the known artifacts created by a failed start transaction."""
    if not directory.exists():
        return None
    if directory.is_symlink():
        return f"partial start cleanup refused for symlinked session: {directory}"
    allowed_names = {
        "continuation.json",
        "ledger.jsonl",
        "probes",
        "route-memory-consultation.json",
        "route-memory-return-template.json",
        "route.json",
    }
    try:
        unexpected = sorted(
            child.name for child in directory.iterdir()
            if child.name not in allowed_names
        )
        if unexpected:
            return (
                "partial start cleanup refused for unexpected session artifacts: "
                + ", ".join(unexpected)
            )
        shutil.rmtree(directory)
    except OSError as exc:
        return f"partial start cleanup failed: {directory}: {exc}"
    return None


def cleanup_partial_package(output: Path, expected_files: set[str]) -> str | None:
    """Remove only files emitted by a failed package transaction."""
    if not output.exists():
        return None
    if output.is_symlink():
        return f"partial package cleanup refused for symlinked output: {output}"
    allowed_directories = {""}
    for relative in expected_files:
        parts = Path(relative).parts[:-1]
        for index in range(1, len(parts) + 1):
            allowed_directories.add(Path(*parts[:index]).as_posix())
    try:
        unexpected: list[str] = []
        for child in output.rglob("*"):
            relative = child.relative_to(output).as_posix()
            if child.is_symlink():
                unexpected.append(relative)
            elif child.is_dir():
                if relative not in allowed_directories:
                    unexpected.append(relative)
            elif relative not in expected_files:
                unexpected.append(relative)
        if unexpected:
            return (
                "partial package cleanup refused for unexpected output artifacts: "
                + ", ".join(sorted(unexpected))
            )
        shutil.rmtree(output)
    except OSError as exc:
        return f"partial package cleanup failed: {output}: {exc}"
    return None


def has_symlink_component(path: Path, root: Path) -> bool:
    """Return whether a session artifact crosses a symbolic-link component."""
    try:
        relative = path.relative_to(root)
    except ValueError:
        return True
    if root.is_symlink():
        return True
    current = root
    for component in relative.parts:
        current /= component
        if current.is_symlink():
            return True
    return False


def output_path_has_symlink_component(path: Path) -> bool:
    """Return whether an output path would traverse a symbolic link.

    Package directories are caller-selected and therefore are not rooted under
    the session tree used by :func:`has_symlink_component`.  Walk the absolute
    path from its filesystem root so a dangling output link or a linked parent
    cannot redirect package writes outside the requested destination.  macOS's
    canonical ``/tmp`` and ``/var`` aliases are harmless platform links we
    preserve after verifying their exact private targets.
    """
    candidate = Path(os.path.abspath(path))
    current = Path(candidate.anchor)
    for component in candidate.parts[1:]:
        current /= component
        if not current.is_symlink():
            continue
        try:
            platform_aliases = {
                Path("/tmp"): Path("/private/tmp"),
                Path("/var"): Path("/private/var"),
            }
            alias_target = platform_aliases.get(current)
            is_platform_alias = (
                alias_target is not None
                and current.resolve(strict=True) == alias_target
            )
        except OSError:
            is_platform_alias = False
        if not is_platform_alias:
            return True
        current = current.resolve(strict=True)
    return False


def session_artifact_bytes(path: Path, sessions_root: Path, label: str) -> bytes:
    """Read a packaged session artifact without following checkout-local links."""
    session_artifact_path(path, sessions_root, label)
    try:
        return path.read_bytes()
    except OSError as exc:
        raise SystemExit(f"package refused: cannot read {label}: {path}: {exc}") from exc


def session_artifact_path(path: Path, sessions_root: Path, label: str) -> Path:
    """Resolve a session input only when it stays inside the session root."""
    if has_symlink_component(path, sessions_root):
        raise SystemExit(
            f"session refused: {label} must not traverse symbolic links: {path}"
        )
    return path


def load_session(sessions_root: Path, slug: str) -> tuple[Path, dict[str, Any]]:
    directory = session_dir(sessions_root, slug)
    if has_symlink_component(directory, sessions_root):
        raise SystemExit(
            f"continuation session must not traverse symbolic links: {directory}"
        )
    manifest_path = session_artifact_path(
        directory / "continuation.json", sessions_root, "continuation manifest"
    )
    if not manifest_path.is_file():
        raise SystemExit(f"continuation session not found: {slug}")
    manifest = load_json(manifest_path)
    if manifest.get("schema") != SESSION_SCHEMA or manifest.get("session") != slug:
        raise SystemExit(f"invalid continuation manifest: {manifest_path}")
    return directory, manifest


def read_ledger(directory: Path, sessions_root: Path) -> list[dict[str, Any]]:
    ledger_path = session_artifact_path(
        directory / "ledger.jsonl", sessions_root, "workbench ledger"
    )
    if not ledger_path.is_file():
        raise SystemExit(f"workbench ledger not found: {ledger_path}")
    rows = []
    try:
        ledger_lines = ledger_path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as exc:
        raise SystemExit(f"cannot read workbench ledger {ledger_path}: {exc}") from exc
    for line_number, line in enumerate(ledger_lines, 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise SystemExit(f"invalid workbench ledger JSON on line {line_number}") from exc
        if not isinstance(row, dict):
            raise SystemExit(f"invalid workbench ledger row on line {line_number}")
        rows.append(row)
    return rows


def cmd_start(args: argparse.Namespace) -> dict[str, Any]:
    validate_slug(args.session)
    if args.problem not in PROBLEMS:
        raise SystemExit(f"problem must be one of {sorted(PROBLEMS)}")
    directory = session_dir(args.sessions_root, args.session)
    if output_path_has_symlink_component(directory):
        raise SystemExit(
            f"session output must not traverse symbolic links: {directory}"
        )
    if directory.exists():
        raise SystemExit(f"session already exists: {args.session}")
    dirty_rows = [line for line in git_output("status", "--porcelain").splitlines() if line.strip()]
    if dirty_rows and not args.allow_dirty:
        raise SystemExit(
            "checkout is dirty; start from a clean immutable commit or pass --allow-dirty "
            "only when the unrelated state is already understood"
        )
    starting_commit = git_output("rev-parse", "HEAD")
    repository_origin = canonical_github_origin(git_output("remote", "get-url", "origin"))
    # The corpus navigator is a typed selector surface, not a problem-number
    # CLI.  Keep this adapter on the current public selector so a cold clone
    # cannot fail before the continuation session is opened.
    corpus_query = f"Erdős problem {args.problem}"
    route = run_json_command(
        [
            sys.executable,
            str(SCRIPTS / "query_corpus.py"),
            "--search",
            corpus_query,
            "--format",
            "json",
        ]
    )
    corpus_results = route.get("results")
    if not isinstance(corpus_results, list) or not any(
        isinstance(row, dict) and row.get("erdos_number") == args.problem
        for row in corpus_results
    ):
        raise SystemExit(
            "corpus query did not return the selected problem: "
            f"{corpus_query!r}"
        )
    route_memory_packet = run_json_command(
        [sys.executable, str(SCRIPTS / "query_route_memory.py"), "--problem", str(args.problem)]
    )
    try:
        route_memory = route_memory_receipt.consultation_for_problem(
            args.problem,
            ROOT,
            no_applicable_route=args.no_applicable_route,
        )
    except ValueError as exc:
        raise SystemExit(f"cannot bind route memory: {exc}") from exc
    queried_problem = route_memory_packet.get("problem")
    if (
        not isinstance(queried_problem, dict)
        or queried_problem.get("erdos_number") != args.problem
    ):
        raise SystemExit("route-memory query did not return the selected problem")
    # query_route_memory.py is the current navigation packet adapter and
    # intentionally reports an unrouted packet when no mathematical programme
    # is registered for a problem. The continuation receipt has a separate
    # canonical eight-problem route corpus, so use that source for the route
    # boundary and keep the two source identities independent.
    route_records, _ = route_memory_receipt.canonical_corpus(ROOT)
    route_record = route_records[args.problem]
    operator = args.operator or args.contributor
    opened = False
    try:
        opened_receipt = run_json_command(
            workbench_command(
                args.sessions_root,
                "open",
                "--session",
                args.session,
                "--intent",
                args.intent,
                "--actor",
                operator,
            )
        )
        opened = True
        route_ids = [item["route_id"] for item in route_memory["routes"]]
        note_text = (
            f"frontier={args.frontier}; stop_condition={args.stop_condition}; "
            f"route_memory_disposition={route_memory['disposition']}; route_ids={route_ids}"
        )
        planned = run_json_command(
            workbench_command(
                args.sessions_root,
                "note",
                "--session",
                args.session,
                "--kind",
                "plan",
                "--text",
                note_text,
            )
        )
        manifest = {
            "schema": SESSION_SCHEMA,
            "session": args.session,
            "created_at": utc_now(),
            "starting_commit": starting_commit,
            "repository_origin": repository_origin,
            "dirty_at_start": bool(dirty_rows),
            "problem": args.problem,
            "frontier": {
                "handle": args.frontier,
                "intent": args.intent,
                "stop_condition": args.stop_condition,
            },
            "route_memory": route_memory,
            "identity": {
                "contributor": {"name": args.contributor},
                "operator": {
                    "relationship": "same_as_contributor" if operator == args.contributor else "named",
                    "name": operator,
                },
                "model_system": disclosure(args.model_system),
                "provider": disclosure(args.provider),
                "material_collaborators": args.material_collaborator,
            },
            "composed_commands": [
                f"python3 scripts/query_corpus.py --search 'Erdős problem {args.problem}' --format json",
                f"python3 scripts/query_route_memory.py --problem {args.problem}",
                "python3 scripts/proof_workbench.py open ...",
                "python3 scripts/proof_workbench.py note --kind plan ...",
            ],
            "authority_boundary": (
                "The route is navigation and the workbench records a session; neither changes Lean proof, "
                "docs/claims.json, mathematical review, or release authority."
            ),
        }
        (directory / "route.json").write_text(dump_json(route), encoding="utf-8")
        (directory / "route-memory-consultation.json").write_text(
            dump_json(route_memory), encoding="utf-8"
        )
        (directory / "route-memory-return-template.json").write_text(
            dump_json(route_memory_receipt.return_receipt_template(route_memory)), encoding="utf-8"
        )
        (directory / "continuation.json").write_text(dump_json(manifest), encoding="utf-8")
    except SystemExit as exc:
        if not opened:
            raise
        cleanup_error = cleanup_partial_start(directory)
        detail = f"start failed: {exc}"
        if cleanup_error:
            detail = f"{detail}; {cleanup_error}"
        raise SystemExit(detail) from exc
    except Exception as exc:
        if not opened:
            raise
        cleanup_error = cleanup_partial_start(directory)
        detail = f"start failed: {type(exc).__name__}: {exc}"
        if cleanup_error:
            detail = f"{detail}; {cleanup_error}"
        raise SystemExit(detail) from exc
    return {
        "schema": "research-continuation-start/1",
        "session": args.session,
        "starting_commit": starting_commit,
        "repository_origin": repository_origin,
        "problem": args.problem,
        "frontier": args.frontier,
        "route_memory": {
            "disposition": route_memory["disposition"],
            "path": route_memory["route_memory"]["path"],
            "digest": route_memory["route_memory"]["sha256"],
            "route_ids": route_ids,
            "boundary": route_record["failure_boundary"],
            "next_obligation": route_record["next_obligation"],
        },
        "workbench_open_move": opened_receipt.get("move_id"),
        "workbench_plan_move": planned.get("move_id"),
        "next": [
            f"python3 scripts/proof_workbench.py note --session {args.session} --kind observation --text '<public observation>'",
            f"python3 scripts/proof_workbench.py close --session {args.session} --outcome <established|open|abandoned> --summary '<bounded outcome>'",
            f"python3 scripts/continue_research.py check --session {args.session} --return-json <filled-return.json> --route-memory-receipt <route-memory-return.json>",
            f"python3 scripts/continue_research.py package --session {args.session} --return-json <filled-return.json> --route-memory-receipt <route-memory-return.json> --output <plain-package-directory>",
        ],
    }


def cross_check_return(
    manifest: dict[str, Any],
    returned: dict[str, Any],
) -> list[str]:
    if not isinstance(manifest, dict):
        return ["continuation manifest: must be an object"]
    if not isinstance(returned, dict):
        return ["return: must be an object"]

    def mapping(value: Any) -> dict[str, Any]:
        return value if isinstance(value, dict) else {}

    returned_repository = mapping(returned.get("repository"))
    returned_frontier = mapping(returned.get("frontier"))
    returned_identity = mapping(returned.get("identity"))
    manifest_identity = mapping(manifest.get("identity"))
    manifest_frontier = mapping(manifest.get("frontier"))
    returned_contributor = mapping(returned_identity.get("contributor"))
    returned_operator = mapping(returned_identity.get("operator"))
    manifest_contributor = mapping(manifest_identity.get("contributor"))
    manifest_operator = mapping(manifest_identity.get("operator"))
    pairs = (
        (
            "repository.origin",
            returned_repository.get("origin"),
            manifest.get("repository_origin"),
        ),
        (
            "repository.starting_commit",
            returned_repository.get("starting_commit"),
            manifest.get("starting_commit"),
        ),
        ("frontier.problem", returned_frontier.get("problem"), manifest.get("problem")),
        (
            "frontier.handle",
            returned_frontier.get("handle"),
            manifest_frontier.get("handle"),
        ),
        (
            "frontier.bounded_question",
            returned_frontier.get("bounded_question"),
            manifest_frontier.get("intent"),
        ),
        (
            "frontier.stop_condition",
            returned_frontier.get("stop_condition"),
            manifest_frontier.get("stop_condition"),
        ),
        (
            "identity.contributor.name",
            returned_contributor.get("name"),
            manifest_contributor.get("name"),
        ),
        (
            "identity.operator.relationship",
            returned_operator.get("relationship"),
            manifest_operator.get("relationship"),
        ),
        (
            "identity.operator.name",
            returned_operator.get("name"),
            manifest_operator.get("name"),
        ),
    )
    errors = [
        f"{path}: does not match the opened continuation session"
        for path, actual, expected in pairs
        if actual != expected
    ]
    proposed_commit = returned_repository.get("proposed_commit")
    if isinstance(proposed_commit, str) and not git_is_ancestor(
        manifest.get("starting_commit", ""), proposed_commit
    ):
        errors.append(
            "repository.proposed_commit: is not a descendant of the opened session starting commit"
        )
    for field in ("model_system", "provider"):
        actual = mapping(returned_identity.get(field))
        expected = mapping(manifest_identity.get(field))
        for key in ("state", "name"):
            if actual.get(key) != expected.get(key):
                errors.append(
                    f"identity.{field}.{key}: does not match the opened continuation session"
                )
    returned_collaborators = {
        (item.get("name"), item.get("role"))
        for item in (
            returned_identity.get("material_collaborators", [])
            if isinstance(returned_identity.get("material_collaborators", []), list)
            else []
        )
        if isinstance(item, dict)
    }
    manifest_collaborators = manifest_identity.get("material_collaborators", [])
    if not isinstance(manifest_collaborators, list):
        manifest_collaborators = []
    for collaborator in manifest_collaborators:
        if not isinstance(collaborator, dict):
            continue
        identity = (collaborator.get("name"), collaborator.get("role"))
        if identity not in returned_collaborators:
            errors.append(
                "identity.material_collaborators: opened-session collaborator "
                f"{identity[0]!r} ({identity[1]!r}) is missing from the return"
            )
    return errors


def check_session(
    sessions_root: Path,
    slug: str,
    return_path: Path | None,
    route_memory_receipt_path: Path | None,
    replay: bool,
    require_closed: bool,
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    directory, manifest = load_session(sessions_root, slug)
    ledger = read_ledger(directory, sessions_root)
    errors: list[str] = []
    consultation = manifest.get("route_memory")
    route_path = session_artifact_path(
        directory / "route.json", sessions_root, "session route"
    )
    persisted_consultation: dict[str, Any] | None = None
    consultation_path = directory / "route-memory-consultation.json"
    try:
        consultation_path = session_artifact_path(
            consultation_path, sessions_root, "route-memory consultation"
        )
        persisted_consultation = load_json(consultation_path)
    except (OSError, json.JSONDecodeError, SystemExit) as exc:
        errors.append(f"route-memory consultation: cannot read JSON: {exc}")

    persisted_template: dict[str, Any] | None = None
    template_path = directory / "route-memory-return-template.json"
    try:
        template_path = session_artifact_path(
            template_path, sessions_root, "route-memory return template"
        )
        persisted_template = load_json(template_path)
    except (OSError, json.JSONDecodeError, SystemExit) as exc:
        errors.append(f"route-memory return template: cannot read JSON: {exc}")

    for label, value in (
        ("continuation", manifest),
        ("route", load_json(route_path)),
        ("route-memory consultation", consultation),
        ("persisted route-memory consultation", persisted_consultation),
        ("persisted route-memory return template", persisted_template),
        ("workbench ledger", ledger),
    ):
        errors.extend(f"{label}: {error}" for error in return_validator.public_safety_errors(value))
    errors.extend(route_memory_receipt.validate_consultation(consultation, ROOT))
    if persisted_consultation is not None:
        errors.extend(
            route_memory_receipt.validate_consultation(persisted_consultation, ROOT)
        )
        if persisted_consultation != consultation:
            errors.append(
                "route-memory consultation: persisted artifact does not match continuation manifest"
            )
        if (
            isinstance(persisted_consultation, dict)
            and persisted_consultation.get("problem") != manifest.get("problem")
        ):
            errors.append(
                "route-memory consultation: problem does not match continuation manifest"
            )
    if persisted_template is not None and isinstance(consultation, dict):
        try:
            expected_template = route_memory_receipt.return_receipt_template(
                consultation
            )
        except (KeyError, TypeError):
            expected_template = None
        if expected_template is not None and persisted_template != expected_template:
            errors.append(
                "route-memory return template: does not match canonical consultation"
            )
    probes = [row for row in ledger if row.get("kind") == "probe"]
    closed = next((row for row in reversed(ledger) if row.get("kind") == "session_closed"), None)
    replay_posture = replay_execution_posture(
        replay=replay,
        probe_count=len(probes),
    )
    replay_receipt: dict[str, Any]
    if not probes:
        replay_receipt = {"state": "not_applicable", "probes_replayed": 0, "all_match": True}
    elif replay:
        raw_replay = run_json_command(workbench_command(sessions_root, "replay", "--session", slug))
        replay_receipt = {
            "state": "reproduced" if raw_replay.get("all_match") else "not_reproduced",
            **raw_replay,
        }
        if not raw_replay.get("all_match"):
            errors.append("workbench replay: one or more stored probe verdicts changed")
    else:
        replay_receipt = {"state": "pending", "probes_replayed": 0, "all_match": None}
    returned: dict[str, Any] | None = None
    if return_path is not None:
        if return_validator.path_has_symlink_component(return_path):
            errors.append("return path must not traverse symbolic links")
        else:
            try:
                returned = load_json(return_path)
            except (OSError, json.JSONDecodeError, SystemExit) as exc:
                errors.append(f"return: cannot read JSON: {exc}")
    if returned is not None:
        errors.extend(
            return_validator.validate_document(
                returned,
                require_submitted=True,
                check_git=True,
            )
        )
        errors.extend(cross_check_return(manifest, returned))
        if route_memory_receipt_path is None:
            errors.append(
                "route-memory receipt is required for submitted returns (digest-bound sidecar)"
            )
        elif return_validator.path_has_symlink_component(route_memory_receipt_path):
            errors.append(
                "route-memory receipt path must not traverse symbolic links"
            )
        else:
            try:
                route_receipt = load_json(route_memory_receipt_path)
            except (OSError, json.JSONDecodeError, SystemExit) as exc:
                errors.append(f"route-memory receipt: cannot read JSON: {exc}")
            else:
                errors.extend(
                    route_memory_receipt.validate_return_receipt(
                        route_receipt, returned, consultation, ROOT
                    )
                )
        if require_closed:
            if returned.get("record_kind") != "submitted_return":
                errors.append("record_kind: package requires submitted_return")
            if closed is None:
                errors.append("workbench session: package requires proof_workbench.py close")
            else:
                result_class = returned.get("result", {}).get("class")
                allowed_outcomes = RESULT_TO_CLOSE_OUTCOME.get(result_class, set())
                if closed.get("outcome") not in allowed_outcomes:
                    errors.append(
                        f"workbench session: close outcome {closed.get('outcome')!r} is inconsistent with result class {result_class!r}"
                    )
    elif require_closed and return_path is None:
        errors.append("return: package requires --return-json")
    check_receipt = {
        "schema": CHECK_SCHEMA,
        "session": slug,
        "starting_commit": manifest["starting_commit"],
        "problem": manifest["problem"],
        "frontier": manifest["frontier"]["handle"],
        "route_memory": {
            "path": consultation.get("route_memory", {}).get("path") if isinstance(consultation, dict) else None,
            "digest": consultation.get("route_memory", {}).get("sha256") if isinstance(consultation, dict) else None,
            "route_ids": [item.get("route_id") for item in consultation.get("routes", [])] if isinstance(consultation, dict) else [],
            "receipt_supplied": route_memory_receipt_path is not None,
        },
        "valid": not errors,
        "errors": sorted(set(errors)),
        "workbench": {
            "move_count": len(ledger),
            "probe_count": len(probes),
            "closed": closed is not None,
            "close_outcome": closed.get("outcome") if closed else None,
        },
        "replay": replay_receipt,
        "execution_posture": replay_posture,
        "return_id": returned.get("return_id") if returned else None,
        "authority_boundary": (
            "Validation and replay classify a return; they do not promote docs/claims.json, "
            "establish novelty, or include an artifact in a release."
        ),
    }
    return check_receipt, returned


def cmd_check(args: argparse.Namespace) -> dict[str, Any]:
    receipt, _ = check_session(
        args.sessions_root,
        args.session,
        args.return_json,
        args.route_memory_receipt,
        args.replay,
        require_closed=False,
    )
    return receipt


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def cmd_package(args: argparse.Namespace) -> dict[str, Any]:
    receipt, returned = check_session(
        args.sessions_root,
        args.session,
        args.return_json,
        args.route_memory_receipt,
        args.replay,
        require_closed=True,
    )
    if not receipt["valid"] or returned is None:
        raise SystemExit("package refused: " + "; ".join(receipt["errors"]))
    directory, manifest = load_session(args.sessions_root, args.session)
    output = args.output
    if output.is_symlink() or output_path_has_symlink_component(output):
        raise SystemExit(
            f"package output must not traverse symbolic links: {output}"
        )
    if output.exists():
        raise SystemExit(f"package output already exists: {output}")
    resolved_output = output.resolve()
    git_dir = (ROOT / ".git").resolve()
    if resolved_output == git_dir or git_dir in resolved_output.parents:
        raise SystemExit("package output must not be inside .git")

    files: dict[str, bytes] = {
        "return.json": dump_json(returned).encode("utf-8"),
        "session/continuation.json": session_artifact_bytes(
            directory / "continuation.json", args.sessions_root, "session continuation"
        ),
        "session/route.json": session_artifact_bytes(
            directory / "route.json", args.sessions_root, "session route"
        ),
        "session/route-memory-consultation.json": session_artifact_bytes(
            directory / "route-memory-consultation.json",
            args.sessions_root,
            "route-memory consultation",
        ),
        "route-memory.json": args.route_memory_receipt.read_bytes(),
        "session/workbench/ledger.jsonl": session_artifact_bytes(
            directory / "ledger.jsonl", args.sessions_root, "workbench ledger"
        ),
        "session/check.json": dump_json(receipt).encode("utf-8"),
    }
    probes_dir = directory / "probes"
    if probes_dir.is_dir():
        if has_symlink_component(probes_dir, args.sessions_root):
            raise SystemExit(
                "package refused: probe directory must not traverse symbolic links: "
                f"{probes_dir}"
            )
        for probe in sorted(probes_dir.iterdir()):
            if probe.is_file():
                files[f"session/workbench/probes/{probe.name}"] = session_artifact_bytes(
                    probe, args.sessions_root, f"probe {probe.name}"
                )
    for relative, data in files.items():
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise SystemExit(f"package refused: non-text artifact {relative}") from exc
        safety_errors = return_validator.public_safety_errors(text)
        if safety_errors:
            raise SystemExit(f"package refused: {relative}: {'; '.join(safety_errors)}")

    package_manifest = {
        "schema": PACKAGE_SCHEMA,
        "return_id": returned["return_id"],
        "session": args.session,
        "starting_commit": manifest["starting_commit"],
        "repository_origin": manifest["repository_origin"],
        "problem": manifest["problem"],
        "frontier": manifest["frontier"]["handle"],
        "route_memory": {
            "source": manifest["route_memory"]["route_memory"],
            "disposition": manifest["route_memory"]["disposition"],
            "relationships": load_json(args.route_memory_receipt)["relationships"],
        },
        "created_at": utc_now(),
        "return_index": {
            "source": "return.json",
            "identity": returned["identity"],
            "repository": {
                "starting_commit": returned["repository"]["starting_commit"],
                "proposed_commit": returned["repository"]["proposed_commit"],
                "accepted_commit": returned["repository"]["accepted_commit"],
                "changed_paths": returned["repository"]["changed_paths"],
            },
            "result": {
                "class": returned["result"]["class"],
                "claim_ceiling": returned["result"]["claim_ceiling"],
                "requested_disposition": returned["result"]["requested_disposition"],
            },
            "evidence": [
                {
                    "exit_state": evidence["exit_state"],
                    "replay_state": evidence["replay_state"],
                }
                for evidence in returned["evidence"]
            ],
            "review": {
                name: decision["state"]
                for name, decision in returned["review"].items()
            },
        },
        "files": [
            {"path": relative, "sha256": _sha256(data), "bytes": len(data)}
            for relative, data in sorted(files.items())
        ],
        "github_intake": {
            "issue_form": ".github/ISSUE_TEMPLATE/research_return.yml",
            "pull_request_artifact": "return.json",
            "pull_request_route_memory_receipt": "route-memory.json",
            "accepted_receipt_directory": "docs/research-commons/returns",
            "local_validation": (
                "python3 scripts/validate_research_return.py return.json "
                "--require-submitted --check-git --require-route-memory-receipt "
                "--route-memory-receipt route-memory.json"
            ),
        },
        "public_guidance": {
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
        },
        "promotion_boundary": (
            "This package is delivery material only. Acceptance, claim review, core promotion, "
            "and tagged-release inclusion remain separate repository decisions."
        ),
    }
    files["package.json"] = dump_json(package_manifest).encode("utf-8")
    created_output = False
    try:
        output.mkdir(parents=True)
        created_output = True
        if output.is_symlink() or output_path_has_symlink_component(output):
            raise SystemExit(
                f"package output must not traverse symbolic links: {output}"
            )
        for relative, data in files.items():
            destination = output / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
    except SystemExit as exc:
        if not created_output:
            raise
        cleanup_error = cleanup_partial_package(output, set(files))
        detail = f"package failed: {exc}"
        if cleanup_error:
            detail = f"{detail}; {cleanup_error}"
        raise SystemExit(detail) from exc
    except Exception as exc:
        if not created_output:
            raise
        cleanup_error = cleanup_partial_package(output, set(files))
        detail = f"package failed: {type(exc).__name__}: {exc}"
        if cleanup_error:
            detail = f"{detail}; {cleanup_error}"
        raise SystemExit(detail) from exc
    return {
        "schema": "research-return-package-result/1",
        "return_id": returned["return_id"],
        "session": args.session,
        "file_count": len(files),
        "package_manifest": "package.json",
        "valid": True,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sessions-root",
        type=Path,
        default=DEFAULT_SESSIONS_ROOT,
        help="override the public workbench sessions directory (used by tests)",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    start = sub.add_parser("start", help="route and open one attributable bounded session")
    start.add_argument("--session", required=True)
    start.add_argument("--problem", required=True, type=int)
    start.add_argument("--frontier", required=True)
    start.add_argument("--intent", required=True)
    start.add_argument("--stop-condition", required=True)
    start.add_argument("--contributor", required=True)
    start.add_argument("--operator")
    start.add_argument("--model-system", default="undisclosed")
    start.add_argument("--provider", default="undisclosed")
    start.add_argument(
        "--no-applicable-route",
        action="store_true",
        help="record that no documented route applies to this bounded frontier",
    )
    start.add_argument(
        "--material-collaborator",
        action="append",
        default=[],
        type=material_collaborator,
        metavar="NAME::ROLE",
        help="record an initial material collaborator; repeat for more than one",
    )
    start.add_argument(
        "--allow-dirty",
        action="store_true",
        help="record and tolerate understood unrelated checkout dirt",
    )
    start.set_defaults(func=cmd_start)

    check = sub.add_parser("check", help="join and validate a return against its opened session")
    check.add_argument("--session", required=True)
    check.add_argument("--return-json", type=Path)
    check.add_argument("--route-memory-receipt", type=Path)
    check.add_argument("--replay", action="store_true", help="invoke proof_workbench.py replay")
    check.set_defaults(func=cmd_check)

    package = sub.add_parser("package", help="emit a validated plain-directory GitHub intake package")
    package.add_argument("--session", required=True)
    package.add_argument("--return-json", required=True, type=Path)
    package.add_argument("--route-memory-receipt", required=True, type=Path)
    package.add_argument("--output", required=True, type=Path)
    package.add_argument("--replay", action="store_true", help="invoke proof_workbench.py replay")
    package.set_defaults(func=cmd_package)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = args.func(args)
    print(dump_json(result), end="")
    return 0 if result.get("valid", True) else 1


if __name__ == "__main__":
    raise SystemExit(main())
