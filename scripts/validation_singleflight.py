#!/usr/bin/env python3
"""Deduplicate bounded repository validation without replacing its authorities.

``submit`` starts at most one detached process group for one exact validation
input.  Equivalent callers receive its shared future or terminal receipt;
``run`` is the one-command submit/join/collect path; ``collect --wait`` resumes
an already known future.  The command
does not interpret a validator's result: its terminal exit code is the exit
code from the existing validator, including 75 for unavailable environments.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
import secrets
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import tomllib
from pathlib import Path
from typing import Any, BinaryIO, Iterable, Mapping

import lean_build_share


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "repository-validation-singleflight/1"
SINGLEFLIGHT_STATE_ROOT_ENV = "VALIDATION_SINGLEFLIGHT_STATE_ROOT"
HOST_LOCK_ROOT_ENV = "PLECTIS_LEAN_HOST_LOCK_ROOT"
HOST_LOCK_HELD_ENV = "AIW_PLECTIS_LEAN_HOST_LOCK_HELD"
ROSTER_VALIDATORS = {
    "cold-clone": "scripts/check_cold_clone_comprehension.py",
    "toolchain-cache": "lean-toolchain",
    "lean": "scripts/lean_fast_build.py",
    "paper": "docs/papers/check_paper_corpus.py",
    "release": "scripts/check_release_ref.py",
    "release-worktree": "scripts/check_release.py",
    "reachable-history": "scripts/test_reachable_release_history.py",
    "comparator": "scripts/verify-comparator.sh",
    "historical": "scripts/historical_bridge_experiment.py",
    "dogfood": "scripts/dogfood_semantic_proof.py",
    "dependency-index": "scripts/build_lean_dependency_index.py",
    "publication-mutations": "scripts/run_publication_mutations.py",
    "palomar": "scripts/check_palomar_qualification.py",
}
TAIL_BYTES = 16_000
STATUS_TAIL_CHARS = 2_000
MAX_STORED_LOG_BYTES = 4 * 1024 * 1024
TRUNCATED_LOG_PREFIX = b"[plectis: earlier validation output truncated; retained tail follows]\n"
LAUNCH_GRACE_SECONDS = 15.0
DEFAULT_TTL_SECONDS = 7 * 24 * 60 * 60
DEFAULT_RECENT_SECONDS = 10 * 60
DEFAULT_COLLECT_TIMEOUT_SECONDS = 30 * 60
DEFAULT_WORKER_TIMEOUT_SECONDS = DEFAULT_COLLECT_TIMEOUT_SECONDS
MAX_EXTERNAL_TERMINATION_ATTEMPTS = 3
EXTERNAL_TERMINATION_RETRY_DELAY_SECONDS = 2
EXTERNAL_TERMINATION_EXIT_CODES = frozenset(
    {
        -signal.SIGTERM,
        -signal.SIGKILL,
        128 + signal.SIGTERM,
        128 + signal.SIGKILL,
    }
)
WORKER_TIMEOUT_EXIT_CODE = 124
DEFAULT_MAX_BYTES = 1 << 30
DEFAULT_MAX_INODES = 10_000
AUTOMATIC_CLEANUP_INTERVAL_SECONDS = 60 * 60
GIT_COMMAND_TIMEOUT_SECONDS = 30
STATE_DIRECTORIES = ("jobs", "locks", "artifacts")
COPY_TREE_MARKERS = ("lean-toolchain", "lakefile.toml")
COPY_TREE_DIRECTORIES = ("ErdosProblems", "docs", "scripts")
RESOURCE_GROUPS = {
    "toolchain-cache": "lean-host",
    "lean": "lean-host",
    "comparator": "lean-host",
    "historical": "lean-host",
    "dependency-index": "lean-host",
    "palomar": "lean-host",
}
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
GIT_PROCESS_CONTROL_KEYS = frozenset(
    {
        "GIT_TRACE",
        "GIT_TRACE2",
        "GIT_TRACE_PACKET",
        "GIT_TRACE_PERFORMANCE",
        "GIT_TRACE_SETUP",
        "GIT_TRACE_CURL",
        "GIT_TRACE2_EVENT",
        "GIT_TRACE2_PERF",
        "GIT_SSH",
        "GIT_SSH_COMMAND",
        "GIT_SSH_VARIANT",
        "GIT_EXTERNAL_DIFF",
        "GIT_DIFF_OPTS",
        "GIT_EDITOR",
        "GIT_SEQUENCE_EDITOR",
        "GIT_MERGE_AUTOEDIT",
    }
)
PYTHON_CONTEXT_KEYS = frozenset(
    {
        "PYTHONHOME",
        "PYTHONPATH",
        "PYTHONSTARTUP",
        "PYTHONUSERBASE",
        "PYTHONBREAKPOINT",
        "PYTHONWARNINGS",
        "PYTHONHASHSEED",
        "PYTHONOPTIMIZE",
        "PYTHONUTF8",
        "PYTHONNOUSERSITE",
        "PYTHONDONTWRITEBYTECODE",
    }
)
LOCALE_KEYS = frozenset({"LC_ALL", "LANG", "LANGUAGE"})
COMPARATOR_REPLAY_AUTHORITY_PATHS = (
    ROOT / "scripts/validation_singleflight.py",
    ROOT / "scripts/verify-comparator.sh",
    ROOT / "scripts/landrun-wrapper.sh",
    ROOT / "scripts/check_palomar_qualification.py",
    ROOT / "comparator.json",
    ROOT / "ErdosProblems/ExternalVerificationPortfolio/comparator-negative-mismatch.json",
    ROOT / "ErdosProblems/ExternalVerificationPortfolio/Challenge.lean",
    ROOT / "ErdosProblems/ExternalVerificationPortfolio/Solution.lean",
    ROOT / "ErdosProblems/ExternalVerificationPortfolio/NegativeSolution.lean",
    ROOT / "lean-toolchain",
    ROOT / "lake-manifest.json",
    ROOT / "lakefile.toml",
)


class ValidationError(RuntimeError):
    """A malformed or unsafe single-flight request."""


def default_cache_home() -> Path:
    xdg_cache = os.environ.get("XDG_CACHE_HOME")
    if xdg_cache:
        return Path(xdg_cache).expanduser()
    if sys.platform == "darwin":
        return Path.home() / "Library" / "Caches"
    return Path.home() / ".cache"


def default_host_lock_root() -> Path:
    """Return the cross-repository namespace for heavy Lean ownership."""

    override = os.environ.get(HOST_LOCK_ROOT_ENV)
    if override:
        candidate = Path(override).expanduser()
        return candidate if candidate.is_absolute() else Path.cwd() / candidate
    return default_cache_home() / "plectis-lean" / "host-locks-v1"


def default_state_root() -> Path:
    """Return one repository-identity cache shared by equivalent cold clones."""

    override = os.environ.get(SINGLEFLIGHT_STATE_ROOT_ENV)
    if override:
        candidate = Path(override).expanduser()
        return candidate if candidate.is_absolute() else Path.cwd() / candidate
    identity_path = ROOT / "docs/repository_identity.json"
    slug = "plectis-lean-erdos249-257"
    try:
        identity = json.loads(identity_path.read_text(encoding="utf-8"))
        configured = identity.get("current", {}).get("slug")
        if isinstance(configured, str) and configured.strip():
            slug = configured.strip()
    except (OSError, json.JSONDecodeError):
        pass
    return default_cache_home() / "plectis-lean" / slug / "validation-singleflight-v1"


DEFAULT_STATE_ROOT = default_state_root()


def resource_lock_path(state: Mapping[str, Path], resource_group: str) -> Path:
    """Use one host lock for Lean, while retaining state-local auxiliary locks."""

    if resource_group == "lean-host":
        return default_host_lock_root() / "resource-lean-host.lock"
    return safe_child(state["locks"], f"resource-{resource_group}.lock")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def digest_bytes(value: bytes) -> str:
    return "sha256:" + hashlib.sha256(value).hexdigest()


def digest_file(path: Path) -> str:
    return digest_bytes(path.read_bytes())


def command_environment() -> dict[str, str]:
    """Run workers without ambient Git, Python, or locale configuration."""
    environment = os.environ.copy()
    for key in list(environment):
        if (
            key.startswith("GIT_CONFIG_")
            or key in GIT_CONTEXT_KEYS
            or key in GIT_PROCESS_CONTROL_KEYS
            or key in PYTHON_CONTEXT_KEYS
            or key == SINGLEFLIGHT_STATE_ROOT_ENV
            or key in LOCALE_KEYS
        ):
            environment.pop(key, None)
    environment.update(
        {
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_PAGER": "cat",
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_ASKPASS": "/bin/false",
            "PATH": os.defpath,
            "LC_ALL": "C.UTF-8",
            "LANG": "C.UTF-8",
            "LANGUAGE": "C.UTF-8",
            "PYTHONHASHSEED": "0",
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONUTF8": "1",
        }
    )
    return environment


def bounded_tail(path: Path) -> str:
    with path.open("rb") as handle:
        handle.seek(0, os.SEEK_END)
        size = handle.tell()
        handle.seek(max(0, size - TAIL_BYTES))
        return handle.read().decode("utf-8", errors="replace")


def compact_output_log(
    path: Path, max_bytes: int = MAX_STORED_LOG_BYTES
) -> dict[str, Any]:
    """Bound persistent output after the child exits without changing its result."""

    size = path.stat().st_size
    if size <= max_bytes:
        return {"observed_bytes": size, "stored_bytes": size, "truncated": False}
    with path.open("rb") as handle:
        handle.seek(max(0, size - max_bytes))
        tail = handle.read(max_bytes)
    atomic_write(path, TRUNCATED_LOG_PREFIX + tail)
    return {
        "observed_bytes": size,
        "stored_bytes": path.stat().st_size,
        "truncated": True,
    }


def regular_file(path: Path, label: str) -> None:
    try:
        mode = path.lstat().st_mode
    except OSError as exc:
        raise ValidationError(f"{label} is missing: {path}") from exc
    if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
        raise ValidationError(f"{label} must be a regular non-symlink file")


def secure_directory(path: Path) -> Path:
    """Create a directory without traversing a symlinked component."""
    candidate = path.expanduser()
    if not candidate.is_absolute():
        candidate = (Path.cwd() / candidate)
    candidate = Path(os.path.abspath(candidate))
    current = Path(candidate.anchor)
    for part in candidate.parts[1:]:
        current /= part
        try:
            mode = current.lstat().st_mode
        except FileNotFoundError:
            try:
                current.mkdir(mode=0o700)
            except FileExistsError:
                # Another equivalent caller may have created this component
                # between lstat and mkdir; inspect it again before proceeding.
                pass
            mode = current.lstat().st_mode
        if stat.S_ISLNK(mode):
            # macOS exposes its temporary area through /var -> /private/var.
            # That platform-owned alias is the only symlink permitted while
            # walking an explicitly supplied state root.
            if current == Path("/var") and current.resolve(strict=True) == Path("/private/var"):
                current = current.resolve(strict=True)
                continue
            raise ValidationError(f"state root contains an unsafe symbolic-link component: {current}")
        if not stat.S_ISDIR(mode):
            raise ValidationError(f"state root contains an unsafe directory component: {current}")
    return candidate.resolve(strict=False)


def _regular_file_at(path: Path) -> bool:
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        return False
    return stat.S_ISREG(mode)


def reject_unsafe_state_root(path: Path) -> Path:
    """Reject repository roots, copied trees, and nested duplicate caches."""
    candidate = Path(os.path.abspath(path.expanduser()))
    resolved = candidate.resolve(strict=False)
    repository_root = ROOT.resolve()
    if resolved == repository_root:
        raise ValidationError("state root must not be a checkout, clone, or worktree")

    default_root = default_state_root().resolve(strict=False)
    if resolved != default_root:
        try:
            resolved.relative_to(default_root)
        except ValueError:
            pass
        else:
            raise ValidationError("state root must not be a nested duplicate cache")

    git_marker = candidate / ".git"
    if os.path.lexists(git_marker):
        raise ValidationError("state root must not be a checkout, clone, or worktree")

    if all(_regular_file_at(candidate / marker) for marker in COPY_TREE_MARKERS) and any(
        (candidate / directory).is_dir() for directory in COPY_TREE_DIRECTORIES
    ):
        raise ValidationError("state root must not be a broad copied repository tree")
    return candidate


def safe_child(root: Path, *parts: str) -> Path:
    if not all(part and "/" not in part and "\\" not in part and part not in {".", ".."} for part in parts):
        raise ValidationError("unsafe state-relative path component")
    child = root.joinpath(*parts)
    try:
        child.relative_to(root)
    except ValueError as exc:  # defensive: parts above already disallow traversal
        raise ValidationError("state-relative path escaped its root") from exc
    return child


def ensure_state_root(path: Path) -> dict[str, Path]:
    root = secure_directory(reject_unsafe_state_root(path))
    directories = {name: secure_directory(safe_child(root, name)) for name in STATE_DIRECTORIES}
    directories["root"] = root
    return directories


def open_lock(path: Path, *, blocking: bool = True) -> int | None:
    if os.path.lexists(path):
        regular_file(path, "lock")
    descriptor = os.open(path, os.O_CREAT | os.O_RDWR, 0o600)
    try:
        fcntl.flock(
            descriptor,
            fcntl.LOCK_EX | (0 if blocking else fcntl.LOCK_NB),
        )
    except BlockingIOError:
        os.close(descriptor)
        return None
    return descriptor


def job_lock_path(state: dict[str, Path], key: str) -> Path:
    """Use 256 stable buckets instead of one permanent lock inode per job."""

    return safe_child(state["locks"], f"job-{key[:2]}.lock")


def atomic_write(path: Path, data: bytes) -> None:
    secure_directory(path.parent)
    temporary = path.with_name(f".{path.name}.{secrets.token_hex(8)}.tmp")
    descriptor = os.open(temporary, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def open_output_log(path: Path) -> BinaryIO:
    """Open a worker log without following a substituted final symlink."""
    secure_directory(path.parent)
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        mode = None
    if mode is not None and not stat.S_ISREG(mode):
        raise ValidationError("worker output log must be a regular non-symlink file")
    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_TRUNC
        | os.O_NONBLOCK
        | getattr(os, "O_NOFOLLOW", 0)
    )
    descriptor = os.open(path, flags, 0o600)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ValidationError("worker output log must be a regular file")
        return os.fdopen(descriptor, "wb")
    except BaseException:
        os.close(descriptor)
        raise


def receipt_path(state: dict[str, Path], key: str) -> Path:
    return safe_child(state["jobs"], f"{key}.json")


def artifact_directory(state: dict[str, Path], key: str) -> Path:
    return safe_child(state["artifacts"], key)


def load_receipt(state: dict[str, Path], key: str) -> dict[str, Any] | None:
    path = receipt_path(state, key)
    if not os.path.lexists(path):
        return None
    regular_file(path, "receipt")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValidationError(f"cannot read validation receipt {key}") from exc
    if not isinstance(value, dict) or value.get("schema") != SCHEMA or value.get("key") != key:
        raise ValidationError(f"invalid validation receipt {key}")
    return value


def write_receipt(state: dict[str, Path], key: str, receipt: dict[str, Any]) -> None:
    if receipt.get("schema") != SCHEMA or receipt.get("key") != key:
        raise ValidationError("refusing to publish a malformed receipt")
    atomic_write(receipt_path(state, key), canonical_json(receipt) + b"\n")


def git_output(*args: str) -> bytes:
    try:
        completed = subprocess.run(
            ["git", *args],
            cwd=ROOT,
            capture_output=True,
            check=False,
            env=command_environment(),
            timeout=GIT_COMMAND_TIMEOUT_SECONDS,
        )
    except OSError as error:
        raise ValidationError(
            f"git {' '.join(args)} could not be launched: {error}"
        ) from error
    if completed.returncode:
        raise ValidationError(completed.stderr.decode("utf-8", errors="replace").strip() or f"git {' '.join(args)} failed")
    return completed.stdout


def relative_to_root(path: Path) -> str:
    try:
        return path.resolve(strict=True).relative_to(ROOT.resolve()).as_posix()
    except (OSError, ValueError) as exc:
        raise ValidationError(f"validation input is outside this repository: {path}") from exc


def worktree_fingerprint(
    state_root: Path,
    *,
    excluded_paths: Iterable[str] = (),
) -> dict[str, Any]:
    tree = git_output("rev-parse", "HEAD^{tree}").decode().strip()
    excluded = frozenset(excluded_paths)
    diff_args = ["diff", "--binary", "HEAD", "--", "."]
    diff_args.extend(f":(exclude){path}" for path in sorted(excluded))
    diff = git_output(*diff_args)
    untracked = []
    state_resolved = state_root.resolve()
    for raw in git_output("ls-files", "--others", "--exclude-standard", "-z").split(b"\0"):
        if not raw:
            continue
        relative = raw.decode("utf-8", errors="surrogateescape")
        if relative in excluded:
            continue
        path = ROOT / relative
        try:
            path.resolve(strict=True).relative_to(state_resolved)
            continue
        except ValueError:
            pass
        except OSError as exc:
            raise ValidationError(f"cannot inspect untracked input {relative}") from exc
        if path.is_symlink() or not path.is_file():
            raise ValidationError(f"untracked input must be a regular file: {relative}")
        untracked.append((relative, digest_file(path)))
    dirty_material = canonical_json({"diff": digest_bytes(diff), "untracked": sorted(untracked)})
    identity_path = ROOT / "docs/repository_identity.json"
    identity = digest_file(identity_path) if identity_path.is_file() else None
    return {
        "tree": tree,
        "dirty": bool(diff or untracked),
        "dirty_fingerprint": digest_bytes(dirty_material),
        "untracked_file_count": len(untracked),
        "repository_identity": identity,
        "identity_policy": "tree_and_dirty_content_checkout_independent",
    }


def regular_digest_rows(paths: Iterable[Path]) -> list[dict[str, str]]:
    rows = []
    for path in sorted(set(paths)):
        relative = relative_to_root(path)
        regular_file(path, relative)
        rows.append({"path": relative, "sha256": digest_file(path)})
    return rows


def git_content_digest_rows(pathspecs: Iterable[str]) -> list[dict[str, str]]:
    """Digest current Git-selected content without checkout-local identity.

    Cached paths remain represented when deleted, so different source
    deletions cannot share a result. Ignored build output never enters the key.
    """
    raw_paths = git_output(
        "ls-files",
        "--cached",
        "--others",
        "--exclude-standard",
        "-z",
        "--",
        *pathspecs,
    )
    rows: list[dict[str, str]] = []
    for raw in sorted(set(raw_paths.split(b"\0"))):
        if not raw:
            continue
        relative = raw.decode("utf-8", errors="surrogateescape")
        path = ROOT / relative
        if not path.exists():
            rows.append({"path": relative, "state": "absent"})
            continue
        regular_file(path, relative)
        relative_to_root(path)
        rows.append({"path": relative, "sha256": digest_file(path)})
    return rows


def merge_digest_rows(*groups: Iterable[dict[str, str]]) -> list[dict[str, str]]:
    """Merge content rows by path while rejecting inconsistent duplicates."""
    merged: dict[str, dict[str, str]] = {}
    for group in groups:
        for row in group:
            path = row["path"]
            previous = merged.get(path)
            if previous is not None and previous != row:
                raise ValidationError(f"inconsistent validation input digest: {path}")
            merged[path] = row
    return [merged[path] for path in sorted(merged)]


def resolve_lean_target(target: str) -> Path:
    if not target or target.startswith("-"):
        raise ValidationError("Lean target must be a named local module or .lean path")
    candidates = [
        ROOT / target if target.endswith(".lean") else ROOT / (target.replace(".", "/") + ".lean")
    ]
    # Lake libraries with ``srcDir`` are addressed by logical library/module
    # names even though their root source lives below a physical directory.
    if not target.endswith(".lean") and "/" not in target:
        lakefile = ROOT / "lakefile.toml"
        if lakefile.is_file():
            try:
                config = tomllib.loads(lakefile.read_text(encoding="utf-8"))
            except (OSError, tomllib.TOMLDecodeError) as error:
                raise ValidationError(
                    f"cannot parse Lake configuration: {lakefile}"
                ) from error
            for library in config.get("lean_lib", []):
                if not isinstance(library, dict):
                    continue
                src_dir = library.get("srcDir", "")
                if isinstance(src_dir, str) and src_dir:
                    candidates.append(
                        ROOT / src_dir / (target.replace(".", "/") + ".lean")
                    )
    candidate = next((path for path in candidates if path.is_file()), candidates[0])
    regular_file(candidate, "Lean target")
    relative_to_root(candidate)
    return candidate


def publication_mutation_spec(
    targets: list[str],
    ref: str | None,
) -> tuple[list[str], Path]:
    """Build one exact worker command for the publication study."""
    actions: list[str] = []
    default_manifest = ROOT / "experiments" / "publication_mutations.json"
    manifest = default_manifest
    timeout_seconds = 600
    for target in targets:
        if target in {"verify-operators", "all"}:
            actions.append(target)
            continue
        prefix, separator, value = target.partition(":")
        if not separator or not value:
            raise ValidationError(
                "publication-mutations targets must be verify-operators, all, "
                "mutation:<id>, manifest:<repo-relative-path>, or timeout:<seconds>"
            )
        if prefix == "mutation":
            if any(character.isspace() for character in value):
                raise ValidationError("publication mutation id must not contain whitespace")
            actions.append(f"mutation:{value}")
        elif prefix == "manifest":
            if manifest != default_manifest:
                raise ValidationError("publication mutation manifest was specified twice")
            candidate = ROOT / value
            regular_file(candidate, "publication mutation manifest")
            relative_to_root(candidate)
            manifest = candidate.resolve(strict=True)
        elif prefix == "timeout":
            try:
                timeout_seconds = int(value)
            except ValueError as error:
                raise ValidationError("publication mutation timeout must be an integer") from error
            if timeout_seconds <= 0:
                raise ValidationError("publication mutation timeout must be positive")
        else:
            raise ValidationError(
                "publication-mutations targets must be verify-operators, all, "
                "mutation:<id>, manifest:<repo-relative-path>, or timeout:<seconds>"
            )
    aggregate = [action for action in actions if action in {"verify-operators", "all"}]
    mutations = [
        action.removeprefix("mutation:")
        for action in actions
        if action.startswith("mutation:")
    ]
    if len(aggregate) > 1:
        raise ValidationError("publication-mutations accepts only one aggregate action")
    if aggregate and mutations:
        raise ValidationError(
            "publication-mutations cannot combine an aggregate and individual actions"
        )
    if not aggregate and not mutations:
        raise ValidationError("publication-mutations requires an action target")
    if len(set(mutations)) != len(mutations):
        raise ValidationError("publication-mutations cannot repeat a mutation id")
    command = [sys.executable, "scripts/run_publication_mutations.py"]
    if manifest != default_manifest:
        command.extend(["--manifest", relative_to_root(manifest)])
    if ref:
        command.extend(["--base-ref", ref])
    if timeout_seconds != 600:
        command.extend(["--timeout-seconds", str(timeout_seconds)])
    if aggregate:
        command.append(f"--{aggregate[0]}")
    else:
        for mutation in mutations:
            command.extend(["--mutation", mutation])
    command.append("--singleflight-worker")
    return command, manifest


def validator_spec(
    kind: str,
    targets: list[str],
    ref: str | None,
    state_root: Path,
    output_format: str | None = None,
    check: bool = False,
    *,
    lean_jobs: int = 2,
    lean_lake_staleness: bool = False,
) -> dict[str, Any]:
    if kind not in ROSTER_VALIDATORS:
        raise ValidationError(f"unknown validation class: {kind}")
    if check and kind != "dependency-index":
        raise ValidationError("--check is only valid for dependency-index validation")
    if kind == "toolchain-cache":
        if targets or ref:
            raise ValidationError("toolchain-cache validation accepts no targets or ref arguments")
        toolchain_path = ROOT / "lean-toolchain"
        regular_file(toolchain_path, "Lean toolchain declaration")
        toolchain = toolchain_path.read_text(encoding="utf-8").strip()
        if not toolchain or any(character.isspace() for character in toolchain):
            raise ValidationError("Lean toolchain declaration must contain one non-empty token")
        command = ["elan", "run", toolchain, "lake", "exe", "cache", "get"]
        authority_paths = [
            toolchain_path,
            ROOT / "lake-manifest.json",
            ROOT / "lakefile.toml",
        ]
    elif kind == "lean":
        if lean_jobs < 1:
            raise ValidationError("Lean validation jobs must be positive")
        target_paths = [resolve_lean_target(target) for target in sorted(set(targets))]
        command = [
            sys.executable,
            "scripts/lean_fast_build.py",
            "--singleflight-worker",
            "--singleflight-state-root",
            str(state_root.resolve()),
            "--jobs",
            str(lean_jobs),
        ]
        if lean_lake_staleness:
            command.append("--lake-staleness")
        command.extend(sorted(set(targets)))
        authority_paths = [
            ROOT / "scripts/validation_singleflight.py",
            ROOT / "scripts/lean_fast_build.py",
            ROOT / "scripts/lean_build_share.py",
            ROOT / "scripts/lean_package_share.py",
            ROOT / "lean-toolchain",
            ROOT / "lake-manifest.json",
            ROOT / "lakefile.toml",
            *target_paths,
        ]
    elif kind == "cold-clone":
        if targets or ref:
            raise ValidationError(
                "cold-clone validation accepts no target or ref arguments"
            )
        command = [
            sys.executable,
            "scripts/check_cold_clone_comprehension.py",
            "--singleflight-worker",
        ]
        authority_paths = [
            ROOT / "scripts/check_cold_clone_comprehension.py",
            ROOT / "scripts/query_corpus.py",
            ROOT / "scripts/query_semantic.py",
            ROOT / "scripts/query_expert_handoffs.py",
        ]
    elif kind == "paper":
        if targets or ref:
            raise ValidationError("paper validation accepts no target or ref arguments")
        corpus = ROOT / "docs/papers/corpus.json"
        regular_file(corpus, "paper corpus")
        try:
            entries = json.loads(corpus.read_text(encoding="utf-8")).get("papers", [])
        except (OSError, json.JSONDecodeError) as exc:
            raise ValidationError("cannot parse paper corpus") from exc
        sources = [ROOT / row["local_source"] for row in entries if isinstance(row, dict) and isinstance(row.get("local_source"), str)]
        command = [
            sys.executable,
            "docs/papers/check_paper_corpus.py",
            "--singleflight-worker",
        ]
        authority_paths = [ROOT / "docs/papers/check_paper_corpus.py", corpus, *sources]
    elif kind == "release":
        if targets:
            raise ValidationError("release validation accepts no targets")
        immutable_ref = ref or git_output("rev-parse", "HEAD").decode().strip()
        commit = git_output("rev-parse", "--verify", f"{immutable_ref}^{{commit}}").decode().strip()
        command = [
            sys.executable,
            "scripts/check_release_ref.py",
            "--ref",
            commit,
            "--format",
            "json",
            "--singleflight-worker",
        ]
        authority_paths = [ROOT / "scripts/check_release_ref.py", ROOT / "scripts/check_release.py"]
    elif kind == "release-worktree":
        if targets or ref:
            raise ValidationError(
                "release-worktree validation accepts no target or ref arguments"
            )
        command = [
            sys.executable,
            "scripts/check_release.py",
            "--singleflight-worker",
        ]
        authority_paths = [
            ROOT / "scripts/check_release.py",
            ROOT / "scripts/validation_singleflight.py",
        ]
    elif kind == "reachable-history":
        if ref or len(targets) != 1 or targets[0] not in {"check", "release-gate"}:
            raise ValidationError(
                "reachable-history validation requires exactly one --target: check or release-gate"
            )
        command = [
            sys.executable,
            "scripts/test_reachable_release_history.py",
            f"--{targets[0]}",
        ]
        authority_paths = [
            ROOT / "scripts/test_reachable_release_history.py",
            ROOT / "scripts/audit_reachable_release_history.py",
            ROOT / "docs/release/reachable-history-audit.json",
        ]
    elif kind == "historical":
        if targets or ref:
            raise ValidationError("historical validation accepts no target or ref arguments")
        output_format = output_format or "card"
        if output_format not in {"card", "json"}:
            raise ValidationError("historical validation format must be card or json")
        command = [sys.executable, "scripts/historical_bridge_experiment.py"]
        if output_format == "json":
            command.append("--compact")
        command.append("--singleflight-worker")
        authority_paths = [
            ROOT / "scripts/historical_bridge_experiment.py",
            ROOT / "scripts/proof_state_compiler.py",
            ROOT / "lean-toolchain",
            ROOT / "lake-manifest.json",
            ROOT / "lakefile.toml",
        ]
    elif kind == "dogfood":
        if len(targets) != 1 or ref:
            raise ValidationError("dogfood validation requires exactly one query target and no ref")
        query = targets[0]
        if not query.strip():
            raise ValidationError("dogfood validation requires a non-empty query")
        output_format = output_format or "card"
        if output_format not in {"card", "json"}:
            raise ValidationError("dogfood validation format must be card or json")
        command = [
            sys.executable,
            "scripts/dogfood_semantic_proof.py",
            "--query",
            query,
            "--format",
            output_format,
            "--singleflight-worker",
        ]
        authority_paths = [
            ROOT / "scripts/dogfood_semantic_proof.py",
            ROOT / "scripts/query_corpus.py",
            ROOT / "docs/claims.json",
            ROOT / "docs/declaration_atlas.json",
            ROOT / "docs/module_synopsis_index.json",
            ROOT / "lean-toolchain",
            ROOT / "lake-manifest.json",
            ROOT / "lakefile.toml",
        ]
    elif kind == "dependency-index":
        if targets or ref:
            raise ValidationError("dependency-index validation accepts no targets or ref arguments")
        command = [sys.executable, "scripts/build_lean_dependency_index.py"]
        if check:
            command.append("--check")
        command.append("--singleflight-worker")
        authority_paths = [
            ROOT / "scripts/build_lean_dependency_index.py",
            ROOT / "scripts/export_lean_dependency_edges.lean",
            ROOT / "scripts/query_corpus.py",
            ROOT / "docs/declaration_atlas.json",
            ROOT / "docs/claims.json",
            ROOT / "docs/lean_dependency_index.json",
            ROOT / "docs/lean_dependency_index_check.json",
            ROOT / "lean-toolchain",
            ROOT / "lake-manifest.json",
            ROOT / "lakefile.toml",
        ]
    elif kind == "publication-mutations":
        command, manifest = publication_mutation_spec(targets, ref)
        authority_paths = [
            ROOT / "scripts/run_publication_mutations.py",
            ROOT / "scripts/check_release.py",
            manifest,
        ]
    elif kind == "palomar":
        if ref or any(target not in {"run-assurance", "run-replay"} for target in targets):
            raise ValidationError(
                "palomar validation accepts only run-assurance and run-replay targets"
            )
        if len(set(targets)) != len(targets):
            raise ValidationError("palomar validation cannot repeat a target")
        command = [sys.executable, "scripts/check_palomar_qualification.py"]
        for target in targets:
            command.append(f"--{target}")
        command.append("--singleflight-worker")
        authority_paths = [
            ROOT / "scripts/check_palomar_qualification.py",
            ROOT / "docs/PALOMAR_POLICY_RECONCILIATION.json",
            ROOT / "formalization.yaml",
            ROOT / "comparator.json",
            ROOT / "lean-toolchain",
            ROOT / "lake-manifest.json",
            ROOT / "scripts/verify-comparator.sh",
            ROOT / "ErdosProblems/ExternalVerificationPortfolio/Challenge.lean",
            ROOT / "ErdosProblems/ExternalVerificationPortfolio/Solution.lean",
        ]
    else:  # comparator
        if targets or ref:
            raise ValidationError("comparator validation accepts no target or ref arguments")
        command = ["bash", "scripts/verify-comparator.sh"]
        authority_paths = list(COMPARATOR_REPLAY_AUTHORITY_PATHS)

    relevant_sources = regular_digest_rows(authority_paths)
    if kind == "lean":
        # Lean sharing follows mathematical/build inputs, not an unrelated
        # README, paper, or generated-doc edit. Hash every visible Lean source
        # (including deletions) plus the explicit toolchain/build authorities.
        # This remains conservative across modules without coupling the
        # scheduler to Lake's evolving dependency graph.
        relevant_sources = merge_digest_rows(
            relevant_sources,
            git_content_digest_rows([":(glob)**/*.lean"]),
        )
        identity_path = ROOT / "docs/repository_identity.json"
        repository = {
            "repository_identity": (
                digest_file(identity_path) if identity_path.is_file() else None
            ),
            "identity_policy": (
                "all_visible_lean_content_and_build_authorities_"
                "checkout_independent"
            ),
        }
    else:
        # Preserve the one-argument seam used by callers and focused tests that
        # replace the generic repository fingerprint function.
        repository = worktree_fingerprint(state_root)
    inputs = {
        "repository": repository,
        "validation_class": kind,
        "normalized_command": command,
        "toolchain": {
            "python": sys.version.split()[0],
            "lean_toolchain": digest_file(ROOT / "lean-toolchain") if (ROOT / "lean-toolchain").is_file() else None,
            "lake_manifest": digest_file(ROOT / "lake-manifest.json") if (ROOT / "lake-manifest.json").is_file() else None,
        },
        "relevant_sources": relevant_sources,
    }
    key = hashlib.sha256(canonical_json(inputs)).hexdigest()
    return {"schema": SCHEMA, "key": key, "inputs": inputs, "command": command}


def validate_specification(specification: dict[str, Any]) -> None:
    """Reject forged or internally inconsistent requests before launch."""
    if specification.get("schema") != SCHEMA:
        raise ValidationError("validation specification has an invalid schema")
    inputs = specification.get("inputs")
    if not isinstance(inputs, dict):
        raise ValidationError("validation specification has no input fingerprint")
    kind = inputs.get("validation_class")
    if kind not in ROSTER_VALIDATORS:
        raise ValidationError("validation specification has an unknown validation class")
    command = inputs.get("normalized_command")
    if not isinstance(command, list) or specification.get("command") != command:
        raise ValidationError("validation command does not match its input fingerprint")
    key = specification.get("key")
    expected = hashlib.sha256(canonical_json(inputs)).hexdigest()
    if key != expected:
        raise ValidationError("validation key does not match its input fingerprint")


def requires_lean_build_materialization(receipt: Mapping[str, Any]) -> bool:
    """Distinguish the tracked Lean builder from scheduler-level test jobs."""

    inputs = receipt.get("inputs")
    if not isinstance(inputs, Mapping) or inputs.get("validation_class") != "lean":
        return False
    command = inputs.get("normalized_command")
    return isinstance(command, list) and any(
        isinstance(argument, str) and Path(argument).name == "lean_fast_build.py"
        for argument in command
    )


def process_identity(pid: int) -> dict[str, Any] | None:
    try:
        os.kill(pid, 0)
    except OSError:
        return None
    token: str | None = None
    stat_path = Path(f"/proc/{pid}/stat")
    try:
        fields = stat_path.read_text(encoding="utf-8").rsplit(")", 1)[1].split()
        token = fields[19]  # Linux proc stat field 22, after the comm field.
    except (OSError, IndexError):
        try:
            observed = subprocess.run(
                ["ps", "-o", "lstart=", "-p", str(pid)],
                capture_output=True,
                text=True,
                check=False,
                env=command_environment(),
                timeout=GIT_COMMAND_TIMEOUT_SECONDS,
            )
        except (OSError, subprocess.TimeoutExpired):
            # A missing or hung process-inspection helper must not escape the
            # identity probe.  The absent token remains fail-closed for PID
            # reuse checks and lets the caller apply its existing policy.
            observed = None
        if observed is not None and observed.returncode == 0 and observed.stdout.strip():
            token = "ps-lstart:" + observed.stdout.strip()
    try:
        pgid = os.getpgid(pid)
    except OSError:
        return None
    return {"pid": pid, "pgid": pgid, "start_token": token}


def owner_is_live(owner: Any) -> bool:
    if not isinstance(owner, dict) or not isinstance(owner.get("pid"), int):
        return False
    observed = process_identity(owner["pid"])
    if observed is None:
        return False
    expected_token = owner.get("start_token")
    # Missing identity is never reclaimed: it could be a reused PID on a host
    # that cannot provide a stable start token.  A known token that differs is
    # safe to reclaim because it proves PID reuse rather than liveness.
    if not isinstance(expected_token, str) or not expected_token:
        return True
    observed_token = observed.get("start_token")
    if not isinstance(observed_token, str) or not observed_token:
        return True
    return observed_token == expected_token


def receipt_is_live(receipt: dict[str, Any]) -> bool:
    if receipt.get("state") not in {
        "launching",
        "future",
        "queued",
        "running",
        "retrying_external_termination",
    }:
        return False
    if owner_is_live(receipt.get("owner")):
        return True
    # A crashed supervisor can leave its validator child alive.  Preserve the
    # one-flight invariant conservatively instead of reclaiming the job while
    # that PID/start identity still exists.
    if owner_is_live(receipt.get("child")):
        return True
    if receipt.get("state") == "launching":
        try:
            age = time.time() - dt.datetime.fromisoformat(receipt["created_at"]).timestamp()
        except (KeyError, TypeError, ValueError):
            return False
        return age < LAUNCH_GRACE_SECONDS
    return False


def terminate_process_group(process: subprocess.Popen[Any]) -> None:
    """Stop a detached worker whose receipt could not be made trustworthy."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except (OSError, ProcessLookupError):
        pass
    try:
        process.wait(timeout=1)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (OSError, ProcessLookupError):
            pass
        try:
            process.wait(timeout=1)
        except subprocess.TimeoutExpired:
            # SIGKILL has been delivered; let the worker publish its terminal
            # timeout receipt even if reaping is delayed by the host.
            pass


# One validation class does work whose cost tracks the size of the library
# rather than the size of a change: a cold full-corpus Lean build. It was
# borrowing the shared thirty-minute worker bound and continuous integration
# killed it at that mark with every module it had reached reporting 0 -- not a
# failure, a clock. It gets its own bound; every other class keeps the shared
# one, because for them a thirty-minute worker really is a hang.
WORKER_TIMEOUT_SECONDS_BY_KIND = {"lean": 3 * 60 * 60}


def worker_timeout_seconds(receipt: dict[str, Any] | None) -> float:
    """Return the bound this validation class is entitled to.

    The receipt names the validator by the command it runs, so the class is
    recovered from the roster rather than restated in the receipt.
    """
    command = list((receipt or {}).get("command") or [])
    for kind, validator in ROSTER_VALIDATORS.items():
        if validator in command and kind in WORKER_TIMEOUT_SECONDS_BY_KIND:
            return WORKER_TIMEOUT_SECONDS_BY_KIND[kind]
    return DEFAULT_WORKER_TIMEOUT_SECONDS


def wait_for_worker(
    process: subprocess.Popen[Any], receipt: dict[str, Any] | None = None
) -> tuple[int, bool]:
    """Wait within the public worker bound and terminate a timed-out child."""
    try:
        return process.wait(timeout=worker_timeout_seconds(receipt)), False
    except subprocess.TimeoutExpired:
        terminate_process_group(process)
        return WORKER_TIMEOUT_EXIT_CODE, True


def is_external_termination_exit(code: int) -> bool:
    """Recognize host/process-manager kills, never Lean diagnostics."""

    return code in EXTERNAL_TERMINATION_EXIT_CODES


def publish_launch_failure(
    state: dict[str, Path],
    initial: dict[str, Any],
    artifact: Path,
    detail: str,
) -> dict[str, Any]:
    """Leave a terminal, environment-unavailable receipt after launch failure."""
    stdout_path = safe_child(artifact, "stdout.log")
    stderr_path = safe_child(artifact, "stderr.log")
    atomic_write(stdout_path, b"")
    atomic_write(stderr_path, f"validation environment unavailable: {detail}\n".encode("utf-8", errors="replace"))
    terminal = {
        **initial,
        "state": "terminal",
        "updated_at": utc_now(),
        "completed_at": utc_now(),
        "exit_code": 75,
        "exit_state": "environment_unavailable",
        "launch_error": detail,
        "stdout": {"path": f"artifacts/{initial['key']}/stdout.log", "sha256": digest_file(stdout_path), "tail": bounded_tail(stdout_path)},
        "stderr": {"path": f"artifacts/{initial['key']}/stderr.log", "sha256": digest_file(stderr_path), "tail": bounded_tail(stderr_path)},
        "artifacts": [f"artifacts/{initial['key']}/stdout.log", f"artifacts/{initial['key']}/stderr.log"],
        "validation_authority": ROSTER_VALIDATORS[initial["inputs"]["validation_class"]],
    }
    write_receipt(state, initial["key"], terminal)
    return terminal


def publish_resource_busy(
    state: dict[str, Path],
    receipt: dict[str, Any],
    artifact: Path,
    resource_group: str,
    started: str,
) -> int:
    """Finish promptly when a different heavy Lean validation owns the host."""

    stdout_path = safe_child(artifact, "stdout.log")
    stderr_path = safe_child(artifact, "stderr.log")
    atomic_write(stdout_path, b"")
    atomic_write(
        stderr_path,
        (
            "validation deferred: another non-identical Lean validation owns "
            f"the host resource group {resource_group!r}; retry after it finishes\n"
        ).encode("utf-8"),
    )
    terminal = {
        **receipt,
        "state": "terminal",
        "updated_at": utc_now(),
        "completed_at": utc_now(),
        "started_at": started,
        "exit_code": 75,
        "exit_state": "resource_busy",
        "resource_group": resource_group,
        "stdout": {
            "path": f"artifacts/{receipt['key']}/stdout.log",
            "sha256": digest_file(stdout_path),
            "tail": bounded_tail(stdout_path),
        },
        "stderr": {
            "path": f"artifacts/{receipt['key']}/stderr.log",
            "sha256": digest_file(stderr_path),
            "tail": bounded_tail(stderr_path),
        },
        "artifacts": [
            f"artifacts/{receipt['key']}/stdout.log",
            f"artifacts/{receipt['key']}/stderr.log",
        ],
        "validation_authority": ROSTER_VALIDATORS[
            receipt["inputs"]["validation_class"]
        ],
    }
    write_receipt(state, receipt["key"], terminal)
    return 75


def launch_worker(state: dict[str, Path], specification: dict[str, Any], previous: dict[str, Any] | None) -> dict[str, Any]:
    validate_specification(specification)
    key = specification["key"]
    token = secrets.token_hex(16)
    attempt = int(previous.get("attempt", 0)) + 1 if previous else 1
    artifact = artifact_directory(state, key)
    if artifact.exists() and artifact.is_symlink():
        raise ValidationError("artifact root is a symbolic link")
    secure_directory(artifact)
    initial = {
        **specification,
        "state": "launching",
        "attempt": attempt,
        "created_at": utc_now(),
        "updated_at": utc_now(),
        "owner": None,
        "child": None,
        "launch_token": token,
        "workspace_root": str(ROOT.resolve()),
        "recovered_from": previous.get("owner") if previous else None,
        "artifacts": [],
    }
    write_receipt(state, key, initial)
    ready = safe_child(artifact, f"ready-{token}")
    process: subprocess.Popen[Any] | None = None
    try:
        process = subprocess.Popen(
            [sys.executable, str(Path(__file__).resolve()), "--state-root", str(state["root"]), "_worker", "--key", key, "--launch-token", token],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
            env=command_environment(),
        )
        owner = process_identity(process.pid)
        if owner is None or owner.get("start_token") is None or owner.get("pgid") != owner.get("pid"):
            terminate_process_group(process)
            return publish_launch_failure(state, initial, artifact, "cannot establish a PID-reuse-resistant worker process group")
        initial.update({"state": "future", "owner": owner, "updated_at": utc_now()})
        write_receipt(state, key, initial)
        atomic_write(ready, b"ready\n")
        return initial
    except (OSError, ValidationError) as exc:
        if process is not None:
            terminate_process_group(process)
        return publish_launch_failure(state, initial, artifact, str(exc))


def submit(specification: dict[str, Any], state_root: Path) -> dict[str, Any]:
    validate_specification(specification)
    automatic_cleanup(state_root)
    state = ensure_state_root(state_root)
    key = specification["key"]
    lock = open_lock(job_lock_path(state, key))
    assert lock is not None
    try:
        existing = load_receipt(state, key)
        if existing is not None and existing.get("state") == "terminal":
            if existing.get("exit_state") == "resource_busy":
                return launch_worker(state, specification, existing)
            if (
                requires_lean_build_materialization(existing)
                and existing.get("exit_code") == 0
                and not lean_build_share.is_materialized(ROOT, key)
                and existing.get("build_seed", {}).get("status") != "ready"
            ):
                return launch_worker(state, specification, existing)
            existing["reuse"] = "terminal"
            return existing
        if existing is not None and receipt_is_live(existing):
            existing["reuse"] = "future"
            return existing
        return launch_worker(state, specification, existing)
    finally:
        fcntl.flock(lock, fcntl.LOCK_UN)
        os.close(lock)


def worker(state_root: Path, key: str, token: str) -> int:
    state = ensure_state_root(state_root)
    artifact = artifact_directory(state, key)
    ready = safe_child(artifact, f"ready-{token}")
    deadline = time.monotonic() + LAUNCH_GRACE_SECONDS
    while not ready.exists() and time.monotonic() < deadline:
        time.sleep(0.02)
    if not ready.exists():
        return 75
    receipt = load_receipt(state, key)
    owner = process_identity(os.getpid())
    if (
        receipt is None
        or receipt.get("launch_token") != token
        or receipt.get("owner") != owner
        or owner is None
        or owner.get("pgid") != owner.get("pid")
    ):
        return 75
    stdout_path = safe_child(artifact, "stdout.log")
    stderr_path = safe_child(artifact, "stderr.log")
    resource_group = RESOURCE_GROUPS.get(receipt["inputs"]["validation_class"])
    resource_lock: int | None = None
    started = utc_now()
    timed_out = False
    build_seed: dict[str, Any] | None = None
    try:
        if resource_group:
            receipt.update(
                {
                    "state": "queued",
                    "updated_at": utc_now(),
                    "resource_group": resource_group,
                }
            )
            write_receipt(state, key, receipt)
            selected_resource_lock = resource_lock_path(state, resource_group)
            selected_resource_lock.parent.mkdir(parents=True, exist_ok=True)
            resource_lock = open_lock(selected_resource_lock, blocking=False)
            if resource_lock is None:
                return publish_resource_busy(
                    state,
                    receipt,
                    artifact,
                    resource_group,
                    started,
                )
        receipt.update({"state": "running", "updated_at": utc_now(), "child": None})
        write_receipt(state, key, receipt)
        child_environment = command_environment()
        if resource_group == "lean-host":
            child_environment[HOST_LOCK_HELD_ENV] = "1"
        with open_output_log(stdout_path) as stdout, open_output_log(stderr_path) as stderr:
            attempt = 0
            last_attempt_code = 75
            external_termination_exits: list[int] = []
            while attempt < MAX_EXTERNAL_TERMINATION_ATTEMPTS:
                attempt += 1
                child = subprocess.Popen(
                    receipt["command"],
                    cwd=ROOT,
                    stdout=stdout,
                    stderr=stderr,
                    # Keep timeout cleanup scoped to the validator child rather
                    # than the detached worker that owns the receipt.
                    start_new_session=True,
                    env=child_environment,
                )
                receipt.update(
                    {
                        "attempt": attempt,
                        "child": process_identity(child.pid),
                        "state": "running",
                        "updated_at": utc_now(),
                    }
                )
                write_receipt(state, key, receipt)
                last_attempt_code, timed_out = wait_for_worker(child, receipt)
                if timed_out:
                    stderr.write(
                        "validation worker timed out after "
                        f"{worker_timeout_seconds(receipt):.0f} seconds\n".encode()
                    )
                    break
                if not is_external_termination_exit(last_attempt_code):
                    break
                external_termination_exits.append(last_attempt_code)
                if attempt >= MAX_EXTERNAL_TERMINATION_ATTEMPTS:
                    stderr.write(
                        (
                            "validation owner exhausted automatic recovery after "
                            f"{attempt} externally terminated attempt(s); deferring as exit 75 "
                            f"(last child exit {last_attempt_code})\n"
                        ).encode()
                    )
                    break
                stderr.write(
                    (
                        "validation owner automatically resuming partial build after "
                        f"external child exit {last_attempt_code} "
                        f"(next attempt {attempt + 1}/{MAX_EXTERNAL_TERMINATION_ATTEMPTS})\n"
                    ).encode()
                )
                stderr.flush()
                receipt.update(
                    {
                        "state": "retrying_external_termination",
                        "child": None,
                        "last_attempt_exit_code": last_attempt_code,
                        "updated_at": utc_now(),
                    }
                )
                write_receipt(state, key, receipt)
                time.sleep(EXTERNAL_TERMINATION_RETRY_DELAY_SECONDS)
            code = (
                75
                if is_external_termination_exit(last_attempt_code)
                else last_attempt_code
            )
            receipt["attempt_count"] = attempt
            receipt["last_attempt_exit_code"] = last_attempt_code
            receipt["automatic_resume_count"] = max(0, attempt - 1)
            receipt["external_termination_exits"] = external_termination_exits
        build_seed = (
            lean_build_share.publish(ROOT, state_root, key)
            if requires_lean_build_materialization(receipt) and code == 0
            else None
        )
    except OSError as exc:
        code = 75
        stderr_path.write_text(f"validation environment unavailable: {exc}\n", encoding="utf-8")
        stdout_path.touch(exist_ok=True)
    finally:
        if resource_lock is not None:
            fcntl.flock(resource_lock, fcntl.LOCK_UN)
            os.close(resource_lock)
    output_storage = {
        "stdout": compact_output_log(stdout_path),
        "stderr": compact_output_log(stderr_path),
    }
    terminal = {
        **receipt,
        "state": "terminal",
        "updated_at": utc_now(),
        "completed_at": utc_now(),
        "started_at": started,
        "exit_code": code,
        "exit_state": (
            "timeout"
            if timed_out
            else ("passed" if code == 0 else ("environment_unavailable" if code == 75 else "failed"))
        ),
        "stdout": {"path": f"artifacts/{key}/stdout.log", "sha256": digest_file(stdout_path), "tail": bounded_tail(stdout_path)},
        "stderr": {"path": f"artifacts/{key}/stderr.log", "sha256": digest_file(stderr_path), "tail": bounded_tail(stderr_path)},
        "artifacts": [f"artifacts/{key}/stdout.log", f"artifacts/{key}/stderr.log"],
        "output_storage": output_storage,
        "validation_authority": ROSTER_VALIDATORS[receipt["inputs"]["validation_class"]],
    }
    if build_seed is not None:
        terminal["build_seed"] = build_seed
    write_receipt(state, key, terminal)
    return code


def status(state_root: Path, key: str) -> dict[str, Any]:
    state = ensure_state_root(state_root)
    receipt = load_receipt(state, key)
    if receipt is None:
        raise ValidationError(f"unknown validation key: {key}")
    receipt["live"] = receipt_is_live(receipt)
    return receipt


def collect(state_root: Path, key: str, wait: bool, timeout_seconds: float) -> tuple[dict[str, Any], int]:
    deadline = time.monotonic() + timeout_seconds
    while True:
        receipt = status(state_root, key)
        if receipt.get("state") == "terminal":
            if (
                requires_lean_build_materialization(receipt)
                and receipt.get("exit_code") == 0
                and not lean_build_share.is_materialized(ROOT, key)
            ):
                state = ensure_state_root(state_root)
                lock_path = resource_lock_path(state, "lean-host")
                lock_path.parent.mkdir(parents=True, exist_ok=True)
                lock = open_lock(lock_path)
                assert lock is not None
                try:
                    materialization = lean_build_share.hydrate(ROOT, state_root, key)
                finally:
                    fcntl.flock(lock, fcntl.LOCK_UN)
                    os.close(lock)
                receipt["build_materialization"] = materialization
                if materialization.get("status") != "hydrated":
                    receipt["exit_state"] = "build_output_unavailable"
                    return receipt, 75
            return receipt, int(receipt["exit_code"])
        if not receipt.get("live", False):
            receipt["owner_unavailable"] = True
            return receipt, 75
        if not wait:
            return receipt, 75
        if time.monotonic() >= deadline:
            receipt["collect_timeout"] = True
            return receipt, 75
        time.sleep(0.05)


def tree_usage(path: Path) -> tuple[int, int]:
    bytes_used = 0
    inodes = 0
    for current, directories, files in os.walk(path, followlinks=False):
        current_path = Path(current)
        if current_path.is_symlink():
            raise ValidationError("state tree contains a symbolic-link directory")
        for name in [*directories, *files]:
            node = current_path / name
            mode = node.lstat().st_mode
            if stat.S_ISLNK(mode):
                raise ValidationError("state tree contains a symbolic link")
            inodes += 1
            if stat.S_ISREG(mode):
                bytes_used += node.stat().st_size
    return bytes_used, inodes


def validation_state_usage(state: dict[str, Path]) -> tuple[int, int]:
    """Measure scheduler receipts/logs without charging COW package seeds."""
    bytes_used = 0
    inodes = 0
    for name in STATE_DIRECTORIES:
        child_bytes, child_inodes = tree_usage(state[name])
        bytes_used += child_bytes
        inodes += child_inodes
    marker = state["root"] / "automatic-cleanup.json"
    if marker.is_file() and not marker.is_symlink():
        bytes_used += marker.stat().st_size
        inodes += 1
    return bytes_used, inodes


def remove_tree(path: Path) -> None:
    if not os.path.lexists(path):
        return
    tree_usage(path)  # rejects links before deletion
    shutil.rmtree(path)


def cleanup(state_root: Path, ttl_seconds: float, max_bytes: int, max_inodes: int, recent_seconds: float) -> dict[str, Any]:
    state = ensure_state_root(state_root)
    lock = open_lock(safe_child(state["locks"], "cleanup.lock"))
    assert lock is not None
    try:
        terminal: list[tuple[float, str, dict[str, Any]]] = []
        skipped_live: list[str] = []
        recovered_dead: list[str] = []
        for path in sorted(state["jobs"].glob("*.json")):
            regular_file(path, "receipt")
            key = path.stem
            receipt = load_receipt(state, key)
            if receipt is None:
                continue
            if receipt.get("state") != "terminal":
                if receipt_is_live(receipt):
                    skipped_live.append(key)
                    continue
                # A killed supervisor used to leave a permanent `running`
                # receipt. Recheck under the per-job lock before converting
                # it to a terminal environment failure, so cleanup cannot
                # race a submitter or a worker publishing completion.
                job_lock = open_lock(job_lock_path(state, key))
                assert job_lock is not None
                try:
                    current = load_receipt(state, key)
                    if current is None:
                        continue
                    if current.get("state") != "terminal" and receipt_is_live(current):
                        skipped_live.append(key)
                        continue
                    if current.get("state") != "terminal":
                        previous_state = current.get("state")
                        current.update(
                            {
                                "state": "terminal",
                                "updated_at": utc_now(),
                                "completed_at": utc_now(),
                                "exit_code": 75,
                                "exit_state": "environment_unavailable",
                                "recovered_from": previous_state,
                                "recovery_reason": "owner_and_child_not_live_during_cleanup",
                            }
                        )
                        write_receipt(state, key, current)
                        recovered_dead.append(key)
                    receipt = current
                finally:
                    fcntl.flock(job_lock, fcntl.LOCK_UN)
                    os.close(job_lock)
            completed = receipt.get("completed_at") or receipt.get("updated_at") or receipt.get("created_at")
            try:
                stamp = dt.datetime.fromisoformat(completed).timestamp()
            except (TypeError, ValueError):
                stamp = path.stat().st_mtime
            terminal.append((stamp, key, receipt))
        bytes_used, inodes = validation_state_usage(state)
        now = time.time()
        removed: list[str] = []
        for stamp, key, _receipt in sorted(terminal):
            old_enough = now - stamp >= ttl_seconds
            pressured = bytes_used > max_bytes or inodes > max_inodes
            if not old_enough and not pressured:
                continue
            if now - stamp < recent_seconds:
                continue
            job = receipt_path(state, key)
            artifact = artifact_directory(state, key)
            job.unlink(missing_ok=True)
            remove_tree(artifact)
            removed.append(key)
            bytes_used, inodes = validation_state_usage(state)
        return {
            "schema": SCHEMA,
            "removed": removed,
            "recovered_dead": recovered_dead,
            "skipped_live": skipped_live,
            "bytes": bytes_used,
            "inodes": inodes,
        }
    finally:
        fcntl.flock(lock, fcntl.LOCK_UN)
        os.close(lock)


def automatic_cleanup(state_root: Path) -> dict[str, Any]:
    """Rate-limit a detached terminal-state cleanup from normal submissions."""

    state = ensure_state_root(state_root)
    marker = safe_child(state["root"], "automatic-cleanup.json")
    lock = open_lock(
        safe_child(state["locks"], "automatic-cleanup.lock"), blocking=False
    )
    if lock is None:
        return {"status": "cleanup_already_scheduled"}
    try:
        if marker.is_file() and time.time() - marker.stat().st_mtime < AUTOMATIC_CLEANUP_INTERVAL_SECONDS:
            return {"status": "cleanup_recent"}
        atomic_write(marker, canonical_json({"scheduled_at": utc_now()}) + b"\n")
        try:
            subprocess.Popen(
                [
                    sys.executable,
                    str(Path(__file__).resolve()),
                    "--state-root",
                    str(state["root"]),
                    "cleanup",
                ],
                cwd=ROOT,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                start_new_session=True,
                env=command_environment(),
            )
        except OSError as exc:
            marker.unlink(missing_ok=True)
            return {"status": "cleanup_launch_failed", "detail": str(exc)}
        return {"status": "cleanup_scheduled"}
    finally:
        fcntl.flock(lock, fcntl.LOCK_UN)
        os.close(lock)


def parse_key(value: str) -> str:
    if len(value) != 64 or any(character not in "0123456789abcdef" for character in value):
        raise argparse.ArgumentTypeError("key must be a lowercase SHA-256 hex digest")
    return value


def emit(value: dict[str, Any]) -> None:
    print(json.dumps(value, indent=2, sort_keys=True))


def status_card(receipt: dict[str, Any]) -> dict[str, Any]:
    """Project a bounded operational card without repeating hashed inputs."""

    inputs = receipt.get("inputs")
    inputs = inputs if isinstance(inputs, dict) else {}
    sources = inputs.get("relevant_sources")
    sources = sources if isinstance(sources, list) else []
    targets = inputs.get("targets")
    card: dict[str, Any] = {
        "schema": "repository-validation-singleflight-status-card/1",
        "key": receipt.get("key"),
        "validation_class": inputs.get("validation_class"),
        "state": receipt.get("state"),
        "live": receipt.get("live"),
        "reuse": receipt.get("reuse"),
        "resource_group": receipt.get("resource_group"),
        "owner": receipt.get("owner"),
        "child": receipt.get("child"),
        "created_at": receipt.get("created_at"),
        "updated_at": receipt.get("updated_at"),
        "started_at": receipt.get("started_at"),
        "completed_at": receipt.get("completed_at"),
        "exit_code": receipt.get("exit_code"),
        "exit_state": receipt.get("exit_state"),
        "owner_unavailable": receipt.get("owner_unavailable"),
        "relevant_source_count": len(sources),
        "target_count": len(targets) if isinstance(targets, list) else None,
    }
    for stream in ("stdout", "stderr"):
        output = receipt.get(stream)
        if isinstance(output, dict) and isinstance(output.get("tail"), str):
            card[f"{stream}_tail"] = output["tail"][-STATUS_TAIL_CHARS:]
    return {key: value for key, value in card.items() if value is not None}


def add_validation_request_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--class", dest="kind", choices=tuple(ROSTER_VALIDATORS), required=True)
    parser.add_argument("--target", action="append", default=[])
    parser.add_argument("--ref")
    parser.add_argument("--format", dest="output_format", choices=("card", "json"))
    parser.add_argument("--check", action="store_true", help="check generated output instead of replacing it")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state-root", type=Path, default=default_state_root(), help="host-shared cache/receipt root; safe to delete through cleanup")
    commands = parser.add_subparsers(dest="action", required=True)
    submit_parser = commands.add_parser("submit", help="start or share a detached validation future")
    add_validation_request_arguments(submit_parser)
    run_parser = commands.add_parser("run", help="submit or join, then collect one validation result")
    add_validation_request_arguments(run_parser)
    run_parser.add_argument(
        "--timeout-seconds",
        type=float,
        default=24 * 60 * 60,
        help="maximum attached collection time; the detached owner continues after timeout",
    )
    for name in ("status", "collect"):
        child = commands.add_parser(name, help=f"read a validation receipt{' or explicitly wait' if name == 'collect' else ''}")
        child.add_argument("--key", type=parse_key, required=True)
        if name == "status":
            child.add_argument(
                "--full",
                action="store_true",
                help="emit the complete hashed input receipt instead of the compact status card",
            )
        if name == "collect":
            child.add_argument("--wait", action="store_true")
            child.add_argument(
                "--timeout-seconds",
                type=float,
                default=DEFAULT_COLLECT_TIMEOUT_SECONDS,
            )
    clean = commands.add_parser("cleanup", help="remove only terminal stale cache trees under explicit budgets")
    clean.add_argument("--ttl-seconds", type=float, default=DEFAULT_TTL_SECONDS)
    clean.add_argument("--max-bytes", type=int, default=DEFAULT_MAX_BYTES)
    clean.add_argument("--max-inodes", type=int, default=DEFAULT_MAX_INODES)
    clean.add_argument("--recent-seconds", type=float, default=DEFAULT_RECENT_SECONDS)
    worker_parser = commands.add_parser("_worker", help=argparse.SUPPRESS)
    worker_parser.add_argument("--key", type=parse_key, required=True)
    worker_parser.add_argument("--launch-token", required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.action in {"submit", "run"}:
            receipt = submit(
                validator_spec(
                    args.kind,
                    args.target,
                    args.ref,
                    args.state_root,
                    args.output_format,
                    args.check,
                ),
                args.state_root,
            )
            if args.action == "submit":
                emit(receipt)
                return 0
            terminal, code = collect(
                args.state_root,
                receipt["key"],
                True,
                args.timeout_seconds,
            )
            emit(terminal)
            return code
        if args.action == "status":
            receipt = status(args.state_root, args.key)
            emit(receipt if args.full else status_card(receipt))
            return 0
        if args.action == "collect":
            receipt, code = collect(args.state_root, args.key, args.wait, args.timeout_seconds)
            emit(receipt)
            return code
        if args.action == "cleanup":
            emit(cleanup(args.state_root, args.ttl_seconds, args.max_bytes, args.max_inodes, args.recent_seconds))
            return 0
        if args.action == "_worker":
            return worker(args.state_root, args.key, args.launch_token)
    except ValidationError as exc:
        print(f"validation-singleflight: {exc}", file=sys.stderr)
        return 2
    raise AssertionError(f"unknown action {args.action}")


if __name__ == "__main__":
    raise SystemExit(main())
