#!/usr/bin/env python3
"""Run the bounded #1049 Comparator positive/negative replay pair.

This is an execution actuator, not a stored verdict.  It keeps the two
fixtures on the same pinned project root and uses the Linux systemd boundary
required by Comparator.  A missing boundary or binary is reported as exit 75
(environment unavailable), while an executed but unexpected Comparator result
is a failure.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Any


DEFAULT_PROJECT_ROOT = Path(__file__).resolve().parents[3]


def _resolve_cache_root(raw_cache_root: str, project_root: Path) -> Path:
    cache_root = Path(raw_cache_root).expanduser()
    if cache_root.is_absolute():
        return cache_root
    return (project_root / cache_root).resolve()


def _resolve_helper_path(project_root: Path, raw_helper_path: str) -> str:
    helper_path = Path(raw_helper_path).expanduser()
    if helper_path.is_absolute():
        return str(helper_path)
    return str((project_root / helper_path).resolve())


_default_tmpdir = os.environ.get("TMPDIR") or "/tmp"
_configured_cache_root = os.environ.get("PALOMAR_COMPARATOR_CACHE") or str(
    Path(_default_tmpdir) / "palomar-comparator"
)


def _pinned_helper_paths(project_root: Path, cache_root: Path) -> dict[str, Path]:
    return {
        "PALOMAR_LANDRUN_BIN": cache_root / "bin" / "landrun",
        "COMPARATOR_LANDRUN": project_root / "scripts" / "landrun-wrapper.sh",
        "COMPARATOR_LEAN4EXPORT": (
            cache_root / "lean4export" / ".lake" / "build" / "bin" / "lean4export"
        ),
        "COMPARATOR_NANODA": cache_root / "nanoda" / "target" / "release" / "nanoda_bin",
    }


DEFAULT_CACHE_ROOT = _resolve_cache_root(_configured_cache_root, DEFAULT_PROJECT_ROOT)
DEFAULT_COMPARATOR_BINARY = str(
    DEFAULT_CACHE_ROOT / "comparator" / ".lake" / "build" / "bin" / "comparator"
)
DEFAULT_PINNED_HELPER_PATHS = _pinned_helper_paths(DEFAULT_PROJECT_ROOT, DEFAULT_CACHE_ROOT)
# The root config is the single selected Palomar entry.  The negative fixture
# remains a separate, repository-relative mismatch input for the replay pair.
POSITIVE_CONFIG = Path("comparator.json")
NEGATIVE_CONFIG = Path("ExternalVerification1049/comparator-negative-mismatch.json")
EXPECTED_CHALLENGE_MODULE = "ExternalVerification1049.Challenge"
EXPECTED_SOLUTION_MODULE = "ExternalVerification1049.Solution"
EXPECTED_NEGATIVE_SOLUTION_MODULE = "ExternalVerification1049.NegativeSolution"
EXPECTED_THEOREM = (
    "Erdos249257.ExternalVerification1049.comparator_sevenHalves_numericalHeight"
)
EXPECTED_NEGATIVE_DIAGNOSTIC = (
    "Challenge and solution theorem statement do not match: "
    f"'{EXPECTED_THEOREM}'"
)
ALLOWED_COMPARATOR_CONFIG_KEYS = frozenset(
    {
        "challenge_module",
        "solution_module",
        "theorem_names",
        "definition_names",
        "permitted_axioms",
        "enable_nanoda",
    }
)
# Palomar's Challenge import boundary admits only Lean core and the named
# allowlisted statement libraries.  Checking the direct imports here makes
# the replay preflight fail closed if the Challenge drifts back to a local
# statement module; those allowlisted libraries own their transitive closure.
ALLOWED_CHALLENGE_IMPORT_PREFIXES = (
    "Init",
    "Std",
    "Batteries",
    "Mathlib",
    "TauCeti",
    "CSLib",
)
ENVIRONMENT_UNAVAILABLE = 75
REPLAY_TIMEOUT_SECONDS = 900
# These optional paths are supplied by the cold-replay verifier after it
# builds the pinned helper tools.  They must be forwarded explicitly because
# systemd-run otherwise starts with a clean environment.
COMPARATOR_HELPER_ENVIRONMENT_NAMES = (
    "PALOMAR_LANDRUN_BIN",
    "COMPARATOR_LANDRUN",
    "COMPARATOR_LEAN4EXPORT",
    "COMPARATOR_NANODA",
)


class ReplayConfigurationError(Exception):
    """The selected fixtures do not describe the supported #1049 replay."""


def _load_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ReplayConfigurationError(f"cannot read JSON config {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ReplayConfigurationError(f"config {path} must contain a JSON object")
    return payload


def _validate_challenge_import_closure(project_root: Path) -> dict[str, Any]:
    relative_path = Path(*EXPECTED_CHALLENGE_MODULE.split(".")).with_suffix(".lean")
    path = project_root / relative_path
    try:
        source = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise ReplayConfigurationError(
            f"cannot read Challenge source {relative_path}: {exc}"
        ) from exc

    direct_imports: list[str] = []
    for raw_line in source.splitlines():
        line = raw_line.split("--", 1)[0].strip()
        if not line.startswith("import "):
            continue
        direct_imports.extend(line[len("import ") :].split())

    disallowed = [
        module
        for module in direct_imports
        if not any(
            module == prefix or module.startswith(f"{prefix}.")
            for prefix in ALLOWED_CHALLENGE_IMPORT_PREFIXES
        )
    ]
    if disallowed:
        raise ReplayConfigurationError(
            "Challenge imports outside the Palomar allowlist: "
            + ", ".join(disallowed)
        )
    return {
        "source": relative_path.as_posix(),
        "direct_imports": direct_imports,
        "allowed_prefixes": list(ALLOWED_CHALLENGE_IMPORT_PREFIXES),
    }


def _validate_config(project_root: Path, relative_path: Path, *, negative: bool) -> dict[str, Any]:
    path = project_root / relative_path
    if not path.is_file():
        raise ReplayConfigurationError(f"missing Comparator config: {relative_path}")
    payload = _load_json(path)
    unknown_keys = sorted(set(payload) - ALLOWED_COMPARATOR_CONFIG_KEYS)
    if unknown_keys:
        raise ReplayConfigurationError(
            f"{relative_path} contains unsupported Comparator keys: "
            + ", ".join(unknown_keys)
        )
    expected_solution = EXPECTED_NEGATIVE_SOLUTION_MODULE if negative else EXPECTED_SOLUTION_MODULE
    expected_label = "negative" if negative else "positive"
    if payload.get("challenge_module") != EXPECTED_CHALLENGE_MODULE:
        raise ReplayConfigurationError(
            f"{expected_label} config challenge_module is not {EXPECTED_CHALLENGE_MODULE!r}"
        )
    if payload.get("solution_module") != expected_solution:
        raise ReplayConfigurationError(
            f"{expected_label} config solution_module is not {expected_solution!r}"
        )
    if payload.get("theorem_names") != [EXPECTED_THEOREM]:
        raise ReplayConfigurationError(
            f"{expected_label} config theorem_names must contain exactly {EXPECTED_THEOREM!r}"
        )
    if payload.get("permitted_axioms") != ["propext", "Quot.sound", "Classical.choice"]:
        raise ReplayConfigurationError(
            f"{expected_label} config has an unexpected permitted_axioms list"
        )
    if payload.get("enable_nanoda") is not True:
        raise ReplayConfigurationError(
            f"{expected_label} config must request enable_nanoda=true for replay parity"
        )
    return payload


def validate_fixture_set(project_root: Path, selected: list[tuple[str, Path, bool]]) -> dict[str, Any]:
    if not project_root.is_dir():
        raise ReplayConfigurationError(f"project root does not exist: {project_root}")
    for required in ("lake-manifest.json", "lean-toolchain", "formalization.yaml"):
        if not (project_root / required).is_file():
            raise ReplayConfigurationError(f"project root is missing {required}")
    challenge_import_closure = _validate_challenge_import_closure(project_root)
    configs = []
    for label, relative_path, negative in selected:
        payload = _validate_config(project_root, relative_path, negative=negative)
        configs.append(
            {
                "fixture": label,
                "config": relative_path.as_posix(),
                "challenge_module": payload["challenge_module"],
                "solution_module": payload["solution_module"],
                "theorem_names": payload["theorem_names"],
                "enable_nanoda": payload["enable_nanoda"],
            }
        )
    return {
        "project_root": str(project_root),
        "challenge_import_closure": challenge_import_closure,
        "configs": configs,
        "expected_negative_diagnostic": EXPECTED_NEGATIVE_DIAGNOSTIC,
    }


def _systemd_command(
    project_root: Path, relative_config: Path, comparator_binary: str
) -> list[str]:
    cache_root = _resolve_cache_root(_configured_cache_root, project_root)
    pinned_helper_paths = _pinned_helper_paths(project_root, cache_root)
    command = [
        "systemd-run",
        # RestrictAddressFamilies is an allow-list unless prefixed by `~`.
        # Permit local Unix sockets while excluding IP address families.
        "--property=RestrictAddressFamilies=AF_UNIX",
        "--user",
        "--wait",
        "--collect",
        "--pipe",
        "-E",
        f"PATH={os.environ.get('PATH', '')}",
        # Match the supported shell actuator: never let a replay select a
        # different Go toolchain while preparing or invoking pinned helpers.
        "-E",
        "GOTOOLCHAIN=local",
    ]
    for name in COMPARATOR_HELPER_ENVIRONMENT_NAMES:
        value = os.environ.get(name)
        if not value:
            default_path = pinned_helper_paths.get(name)
            if default_path is not None and default_path.is_file():
                value = str(default_path)
        if value:
            command.extend(["-E", f"{name}={_resolve_helper_path(project_root, value)}"])
    command.extend(
        [
            "--working-directory",
            str(project_root),
            "--",
            "bash",
            "-c",
            'exec lake env "$1" "$2"',
            "comparator-replay",
            comparator_binary,
            relative_config.as_posix(),
        ]
    )
    return command


def _looks_environment_unavailable(output: str, returncode: int) -> bool:
    if returncode == 127:
        return True
    lowered = output.lower()
    return any(
        marker in lowered
        for marker in (
            "failed to connect to bus",
            "system has not been booted with systemd",
            "systemd-run: command not found",
            "command not found: lake",
            "command not found: comparator",
            "interactive authentication required",
            "no medium found",
        )
    )


def _missing_default_pinned_paths(
    comparator_binary: str, project_root: Path, cache_root: Path
) -> list[str]:
    default_comparator_binary = str(
        cache_root / "comparator" / ".lake" / "build" / "bin" / "comparator"
    )
    if comparator_binary != default_comparator_binary:
        return []
    required_paths = [Path(comparator_binary), *_pinned_helper_paths(project_root, cache_root).values()]
    return [
        str(path)
        for path in required_paths
        if not path.is_file() or not os.access(path, os.X_OK)
    ]


def _run_fixture(
    project_root: Path,
    label: str,
    relative_config: Path,
    *,
    negative: bool,
    comparator_binary: str,
    timeout_seconds: int,
) -> dict[str, Any]:
    command = _systemd_command(project_root, relative_config, comparator_binary)
    try:
        completed = subprocess.run(
            command,
            cwd=project_root,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            env=os.environ.copy(),
            timeout=timeout_seconds,
        )
    except FileNotFoundError:
        return {
            "fixture": label,
            "config": relative_config.as_posix(),
            "status": "environment_unavailable",
            "returncode": ENVIRONMENT_UNAVAILABLE,
            "output": "systemd-run is not installed or not on PATH",
            "command": command,
        }
    except subprocess.TimeoutExpired as exc:
        output = exc.output or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        return {
            "fixture": label,
            "config": relative_config.as_posix(),
            "status": "replay_timeout",
            "returncode": 124,
            "timeout_seconds": timeout_seconds,
            "output": output,
            "command": command,
        }

    output = completed.stdout or ""
    if _looks_environment_unavailable(output, completed.returncode):
        return {
            "fixture": label,
            "config": relative_config.as_posix(),
            "status": "environment_unavailable",
            "returncode": ENVIRONMENT_UNAVAILABLE,
            "underlying_returncode": completed.returncode,
            "output": output,
            "command": command,
        }

    if not negative:
        passed = completed.returncode == 0
        return {
            "fixture": label,
            "config": relative_config.as_posix(),
            "status": "positive_accepted" if passed else "positive_unexpected_failure",
            "returncode": completed.returncode,
            "output": output,
            "command": command,
        }

    diagnostic_seen = EXPECTED_NEGATIVE_DIAGNOSTIC in output
    passed = completed.returncode != 0 and diagnostic_seen
    return {
        "fixture": label,
        "config": relative_config.as_posix(),
        "status": "negative_rejected_expectedly" if passed else "negative_unexpected_outcome",
        "returncode": completed.returncode,
        "expected_diagnostic_seen": diagnostic_seen,
        "output": output,
        "command": command,
    }


def _selected_fixtures(args: argparse.Namespace) -> list[tuple[str, Path, bool]]:
    if args.positive_only:
        return [("positive", POSITIVE_CONFIG, False)]
    if args.negative_only:
        return [("negative", NEGATIVE_CONFIG, True)]
    return [
        ("positive", POSITIVE_CONFIG, False),
        ("negative", NEGATIVE_CONFIG, True),
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--project-root",
        type=Path,
        default=DEFAULT_PROJECT_ROOT,
        help="pinned Lean project root (default: this repository's #1049 project root)",
    )
    parser.add_argument(
        "--comparator-binary",
        default=None,
        help=(
            "Comparator executable or exact path to invoke inside the replay "
            "environment (default: COMPARATOR_BINARY or the pinned replay cache)"
        ),
    )
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--positive-only", action="store_true")
    selection.add_argument("--negative-only", action="store_true")
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="validate both fixture bindings and print the commands without executing Comparator",
    )
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=REPLAY_TIMEOUT_SECONDS,
        help=f"maximum runtime for each fixture (default: {REPLAY_TIMEOUT_SECONDS})",
    )
    args = parser.parse_args(argv)
    project_root = args.project_root.expanduser().resolve()
    cache_root = _resolve_cache_root(_configured_cache_root, project_root)
    comparator_binary = (
        args.comparator_binary
        or os.environ.get("COMPARATOR_BINARY")
        or str(cache_root / "comparator" / ".lake" / "build" / "bin" / "comparator")
    ).strip()
    if not comparator_binary:
        parser.error("--comparator-binary cannot be empty")
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    selected = _selected_fixtures(args)

    try:
        validation = validate_fixture_set(project_root, selected)
    except ReplayConfigurationError as exc:
        print(
            json.dumps(
                {
                    "schema": "comparator_replay_actuator_v1",
                    "status": "configuration_error",
                    "error": str(exc),
                },
                indent=2,
            )
        )
        return 2

    validation["comparator_binary"] = comparator_binary
    if args.dry_run:
        validation["schema"] = "comparator_replay_actuator_v1"
        validation["status"] = "dry_run_ready"
        validation["commands"] = [
            _systemd_command(project_root, relative_path, comparator_binary)
            for _, relative_path, _ in selected
        ]
        print(json.dumps(validation, indent=2))
        return 0

    if shutil.which("systemd-run") is None:
        result = {
            "schema": "comparator_replay_actuator_v1",
            "status": "environment_unavailable",
            "environment_unavailable": True,
            "returncode": ENVIRONMENT_UNAVAILABLE,
            "reason": "systemd-run is not installed or not on PATH",
            **validation,
        }
        print(json.dumps(result, indent=2))
        return ENVIRONMENT_UNAVAILABLE

    missing_pinned_paths = _missing_default_pinned_paths(
        comparator_binary, project_root, cache_root
    )
    if missing_pinned_paths:
        result = {
            "schema": "comparator_replay_actuator_v1",
            "status": "environment_unavailable",
            "environment_unavailable": True,
            "returncode": ENVIRONMENT_UNAVAILABLE,
            "reason": "the pinned Comparator replay cache is incomplete",
            "missing_pinned_paths": missing_pinned_paths,
            **validation,
        }
        print(json.dumps(result, indent=2))
        return ENVIRONMENT_UNAVAILABLE

    runs = [
        _run_fixture(
            project_root,
            label,
            relative_path,
            negative=negative,
            comparator_binary=comparator_binary,
            timeout_seconds=args.timeout_seconds,
        )
        for label, relative_path, negative in selected
    ]
    statuses = {run["status"] for run in runs}
    if "environment_unavailable" in statuses:
        overall_status = "environment_unavailable"
        returncode = ENVIRONMENT_UNAVAILABLE
    elif all(
        run["status"] in {"positive_accepted", "negative_rejected_expectedly"}
        for run in runs
    ):
        overall_status = "replay_pair_passed"
        returncode = 0
    else:
        overall_status = "unexpected_comparator_outcome"
        returncode = 1

    result = {
        "schema": "comparator_replay_actuator_v1",
        "status": overall_status,
        "returncode": returncode,
        **validation,
        "runs": runs,
    }
    print(json.dumps(result, indent=2))
    return returncode


if __name__ == "__main__":
    sys.exit(main())
