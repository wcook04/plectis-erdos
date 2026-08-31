#!/usr/bin/env python3
"""Share compatible Lake dependency trees across public cold clones.

The shared seed is acceleration, never proof evidence.  A workspace always
receives its own mutable ``.lake/packages`` path.  On copy-on-write filesystems
the files initially share physical blocks, then diverge only where a later
build writes.  Symlinks and ordinary full-copy fallbacks are deliberately
forbidden.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import secrets
import shutil
import stat
import subprocess
import sys
from typing import Any, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "public-lean-package-share/1"
RECEIPT_NAME = "package_share_receipt.json"
MIB = 1024 * 1024
DEFAULT_SETUP_COMPRESSION_MIN_BYTES = MIB
DEFAULT_RETAINED_PACKAGE_SEEDS = 2
STATE_ROOT_ENV = "VALIDATION_SINGLEFLIGHT_STATE_ROOT"


class PackageShareError(RuntimeError):
    """Unsafe or inconsistent dependency-cache state."""


def default_state_root(root: Path = ROOT) -> Path:
    override = os.environ.get(STATE_ROOT_ENV)
    if override:
        candidate = Path(override).expanduser()
        return candidate if candidate.is_absolute() else Path.cwd() / candidate
    slug = "plectis-lean-erdos249-257"
    try:
        identity = json.loads(
            (root / "docs/repository_identity.json").read_text(encoding="utf-8")
        )
        configured = identity.get("current", {}).get("slug")
        if isinstance(configured, str) and configured.strip():
            slug = configured.strip()
    except (OSError, json.JSONDecodeError):
        pass
    if os.environ.get("XDG_CACHE_HOME"):
        cache_home = Path(os.environ["XDG_CACHE_HOME"]).expanduser()
    elif sys.platform == "darwin":
        cache_home = Path.home() / "Library/Caches"
    else:
        cache_home = Path.home() / ".cache"
    return cache_home / "plectis-lean" / slug / "validation-singleflight-v1"


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def atomic_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{secrets.token_hex(8)}.tmp")
    temporary.write_bytes(canonical_json(value) + b"\n")
    os.replace(temporary, path)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(MIB), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run(
    argv: Sequence[str], *, cwd: Path | None = None, timeout: float = 120.0
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(argv),
        cwd=cwd,
        capture_output=True,
        text=True,
        errors="replace",
        timeout=timeout,
        check=False,
    )


def semantic_fingerprint(root: Path) -> tuple[str, list[dict[str, str]], str]:
    toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = sorted(
        (
            {
                "name": str(row.get("name") or ""),
                "type": str(row.get("type") or ""),
                "url": str(row.get("url") or ""),
                "rev": str(row.get("rev") or ""),
            }
            for row in manifest.get("packages", [])
            if isinstance(row, dict)
        ),
        key=lambda row: (row["name"], row["url"], row["rev"]),
    )
    encoded = canonical_json({"toolchain": toolchain, "packages": packages})
    return hashlib.sha256(encoded).hexdigest(), packages, toolchain


def reject_mutable_symlinks(root: Path) -> None:
    for path in (root / ".lake", root / ".lake/packages"):
        if path.is_symlink():
            raise PackageShareError(f"mutable Lake cache must not be a symlink: {path}")


def package_heads(packages_root: Path) -> dict[str, str]:
    """Return clean dependency HEADs, rejecting ambiguous package content."""
    if not packages_root.is_dir() or packages_root.is_symlink():
        raise PackageShareError("dependency package tree is absent or unsafe")
    heads: dict[str, str] = {}
    for child in sorted(packages_root.iterdir()):
        if child.name.startswith("."):
            continue
        if not child.is_dir() or child.is_symlink() or not (child / ".git").exists():
            raise PackageShareError(f"unexpected dependency-cache entry: {child}")
        head = run(["git", "rev-parse", "HEAD"], cwd=child)
        status = run(
            ["git", "status", "--porcelain=v1", "--untracked-files=all"],
            cwd=child,
        )
        if head.returncode or status.returncode or status.stdout.strip():
            raise PackageShareError(f"dependency repository is dirty or unreadable: {child}")
        heads[child.name] = head.stdout.strip()
    if not heads:
        raise PackageShareError("dependency package tree contains no Git repositories")
    return heads


def cache_generation(packages_root: Path) -> dict[str, int]:
    """Cheaply detect compiled-output mutation during COW staging."""
    directory_count = 0
    newest_mtime_ns = 0
    if not packages_root.is_dir():
        return {"directory_count": 0, "newest_mtime_ns": 0}
    for package in packages_root.iterdir():
        build_root = package / ".lake/build"
        if not build_root.is_dir():
            continue
        for directory, dirnames, _filenames in os.walk(build_root):
            directory_count += 1
            try:
                newest_mtime_ns = max(
                    newest_mtime_ns, Path(directory).stat().st_mtime_ns
                )
            except OSError:
                continue
            dirnames[:] = [name for name in dirnames if not name.startswith(".")]
    return {
        "directory_count": directory_count,
        "newest_mtime_ns": newest_mtime_ns,
    }


def copy_on_write_command(source: Path, target: Path) -> list[str] | None:
    if sys.platform == "darwin" and Path("/bin/cp").is_file():
        return ["/bin/cp", "-cR", str(source), str(target)]
    if sys.platform.startswith("linux") and shutil.which("cp"):
        return ["cp", "--reflink=always", "-a", str(source), str(target)]
    return None


def clone_tree(source: Path, target: Path) -> None:
    command = copy_on_write_command(source, target)
    if command is None:
        raise PackageShareError("copy-on-write cloning is unavailable on this platform")
    completed = run(command, timeout=600.0)
    if completed.returncode:
        detail = completed.stderr.strip()[:300]
        raise PackageShareError(f"copy-on-write clone failed: {detail}")


def lean_process_is_live(root: Path) -> bool:
    """Fail closed if a raw Lean/Lake owner references this workspace."""
    try:
        completed = run(["ps", "-axo", "pid=,comm=,command="], timeout=5.0)
    except (OSError, subprocess.TimeoutExpired):
        return True
    if completed.returncode:
        return True
    resolved = root.resolve()
    needle = str(resolved)
    for line in completed.stdout.splitlines():
        parts = line.strip().split(None, 2)
        if len(parts) < 2:
            continue
        try:
            pid = int(parts[0])
        except ValueError:
            continue
        if Path(parts[1]).name.lower() not in {"lean", "lake"}:
            continue
        command = parts[2] if len(parts) > 2 else parts[1]
        if needle in command:
            return True
        lsof = Path("/usr/sbin/lsof")
        if not lsof.is_file():
            continue
        cwd = run([str(lsof), "-a", "-p", str(pid), "-d", "cwd", "-Fn"], timeout=2.0)
        if cwd.returncode:
            continue
        for cwd_line in cwd.stdout.splitlines():
            if not cwd_line.startswith("n"):
                continue
            try:
                Path(cwd_line[1:]).resolve().relative_to(resolved)
            except (OSError, ValueError):
                continue
            return True
    return False


def seed_paths(state_root: Path, fingerprint: str) -> tuple[Path, Path]:
    seed_root = state_root / "package-seeds" / fingerprint
    return seed_root / "packages", seed_root / "seed.json"


def load_seed(
    state_root: Path, fingerprint: str
) -> tuple[Path, dict[str, str]] | None:
    packages, receipt_path = seed_paths(state_root, fingerprint)
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if (
        receipt.get("schema") != SCHEMA
        or receipt.get("semantic_fingerprint") != fingerprint
        or not isinstance(receipt.get("package_heads"), dict)
    ):
        return None
    try:
        observed = package_heads(packages)
    except PackageShareError:
        return None
    expected = {str(key): str(value) for key, value in receipt["package_heads"].items()}
    return (packages, observed) if observed == expected else None


def remove_obsolete_seeds(
    state_root: Path,
    keep_fingerprint: str,
    *,
    retained: int = DEFAULT_RETAINED_PACKAGE_SEEDS,
) -> list[str]:
    """Bound immutable semantic seeds; cloned workspace blocks remain valid."""
    seed_root = state_root / "package-seeds"
    if not seed_root.is_dir() or seed_root.is_symlink():
        return []
    candidates: list[tuple[int, Path]] = []
    for path in seed_root.iterdir():
        if (
            not path.is_dir()
            or path.is_symlink()
            or len(path.name) != 64
            or any(character not in "0123456789abcdef" for character in path.name)
            or path.name == keep_fingerprint
        ):
            continue
        receipt_path = path / "seed.json"
        try:
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if (
            receipt.get("schema") != SCHEMA
            or receipt.get("semantic_fingerprint") != path.name
        ):
            continue
        candidates.append((receipt_path.stat().st_mtime_ns, path))
    # The current seed consumes one retention slot.
    keep_old = max(0, retained - 1)
    removable = sorted(candidates, reverse=True)[keep_old:]
    removed: list[str] = []
    for _stamp, path in removable:
        shutil.rmtree(path)
        removed.append(path.name)
    return removed


def workspace_receipt_current(
    root: Path, fingerprint: str, seed_heads: dict[str, str]
) -> bool:
    try:
        receipt = json.loads(
            (root / ".lake" / RECEIPT_NAME).read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError):
        return False
    return (
        receipt.get("schema") == SCHEMA
        and receipt.get("semantic_fingerprint") == fingerprint
        and receipt.get("package_heads") == seed_heads
    )


def publish_seed(
    root: Path,
    state_root: Path,
    fingerprint: str,
    heads: dict[str, str],
) -> dict[str, Any]:
    source = root / ".lake/packages"
    packages, receipt_path = seed_paths(state_root, fingerprint)
    packages.parent.mkdir(parents=True, exist_ok=True)
    if packages.parent.stat().st_dev != source.stat().st_dev:
        return {
            "schema": SCHEMA,
            "status": "unsupported_cross_device_seed",
            "proof_scope": "cache_acceleration_not_proof_evidence",
        }
    stage = packages.parent / f".packages-stage-{secrets.token_hex(8)}"
    source_generation = cache_generation(source)
    try:
        clone_tree(source, stage)
        if package_heads(stage) != heads:
            raise PackageShareError("published seed package HEADs changed")
        if lean_process_is_live(root) or cache_generation(source) != source_generation:
            raise PackageShareError("workspace cache changed during seed publication")
        if packages.exists():
            raise PackageShareError("package seed appeared during publication")
        os.replace(stage, packages)
        atomic_json(
            receipt_path,
            {
                "schema": SCHEMA,
                "semantic_fingerprint": fingerprint,
                "package_heads": heads,
                "source_role": "immutable_host_seed",
                "proof_scope": "cache_acceleration_not_proof_evidence",
            },
        )
    finally:
        if stage.exists():
            shutil.rmtree(stage)
    atomic_json(
        root / ".lake" / RECEIPT_NAME,
        {
            "schema": SCHEMA,
            "semantic_fingerprint": fingerprint,
            "package_heads": heads,
            "relationship": "seed_published_as_copy_on_write_clone",
            "proof_scope": "cache_acceleration_not_proof_evidence",
        },
    )
    removed = remove_obsolete_seeds(state_root, fingerprint)
    return {
        "schema": SCHEMA,
        "status": "published_host_seed",
        "semantic_fingerprint": fingerprint,
        "package_count": len(heads),
        "physical_strategy": "copy_on_write_no_full_copy_fallback",
        "obsolete_seed_fingerprints_removed": removed,
        "proof_scope": "cache_acceleration_not_proof_evidence",
    }


def attach_seed(
    root: Path,
    source: Path,
    fingerprint: str,
    seed_heads: dict[str, str],
) -> dict[str, Any]:
    lake = root / ".lake"
    target = lake / "packages"
    lake.mkdir(parents=True, exist_ok=True)
    if lake.stat().st_dev != source.stat().st_dev:
        return {
            "schema": SCHEMA,
            "status": "unsupported_cross_device_seed",
            "proof_scope": "cache_acceleration_not_proof_evidence",
        }
    stage = lake / f".packages-stage-{secrets.token_hex(8)}"
    backup: Path | None = None
    target_existed = target.is_dir()
    target_generation = cache_generation(target)
    try:
        clone_tree(source, stage)
        if package_heads(stage) != seed_heads:
            raise PackageShareError("attached package HEADs do not match seed")
        if lean_process_is_live(root):
            raise PackageShareError("Lean/Lake process appeared during package staging")
        if target_existed:
            if (
                not target.is_dir()
                or package_heads(target) != seed_heads
                or cache_generation(target) != target_generation
            ):
                raise PackageShareError("workspace cache changed during package staging")
            backup = lake / f".packages-before-share-{secrets.token_hex(8)}"
            os.replace(target, backup)
        elif os.path.lexists(target):
            raise PackageShareError("target package cache appeared during package staging")
        os.replace(stage, target)
    except Exception:
        if backup is not None and backup.exists() and not target.exists():
            os.replace(backup, target)
        raise
    finally:
        if stage.exists():
            shutil.rmtree(stage)
    if backup is not None:
        shutil.rmtree(backup)
    atomic_json(
        lake / RECEIPT_NAME,
        {
            "schema": SCHEMA,
            "semantic_fingerprint": fingerprint,
            "package_heads": seed_heads,
            "relationship": "independent_copy_on_write_clone_of_host_seed",
            "proof_scope": "cache_acceleration_not_proof_evidence",
        },
    )
    return {
        "schema": SCHEMA,
        "status": "attached_host_seed",
        "semantic_fingerprint": fingerprint,
        "package_count": len(seed_heads),
        "mutable_tree_shared": False,
        "symlink_created": False,
        "physical_strategy": "copy_on_write_no_full_copy_fallback",
        "proof_scope": "cache_acceleration_not_proof_evidence",
    }


def prepare_workspace(root: Path, state_root: Path) -> dict[str, Any]:
    """Publish, attach, or reuse one same-lock package seed under a host lock."""
    root = root.resolve()
    state_root = state_root.resolve()
    reject_mutable_symlinks(root)
    fingerprint, packages, toolchain = semantic_fingerprint(root)
    lock_path = state_root / "locks" / "resource-package-seed.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR, 0o600)
    fcntl.flock(descriptor, fcntl.LOCK_EX)
    try:
        seed = load_seed(state_root, fingerprint)
        target = root / ".lake/packages"
        if seed is not None:
            source, seed_heads = seed
            expected_names = {row["name"] for row in packages if row["name"]}
            if set(seed_heads) != expected_names:
                return {
                    "schema": SCHEMA,
                    "status": "preserved_incomplete_host_seed",
                    "proof_scope": "cache_acceleration_not_proof_evidence",
                }
            if target.is_dir():
                try:
                    target_heads = package_heads(target)
                except PackageShareError as exc:
                    return {
                        "schema": SCHEMA,
                        "status": "preserved_unsafe_or_dirty_workspace_cache",
                        "detail": str(exc),
                        "proof_scope": "cache_acceleration_not_proof_evidence",
                    }
                if target_heads != seed_heads:
                    return {
                        "schema": SCHEMA,
                        "status": "preserved_nonmatching_workspace_cache",
                        "proof_scope": "cache_acceleration_not_proof_evidence",
                    }
                if workspace_receipt_current(root, fingerprint, seed_heads):
                    return {
                        "schema": SCHEMA,
                        "status": "reused_shared_package_lineage",
                        "semantic_fingerprint": fingerprint,
                        "package_count": len(seed_heads),
                        "proof_scope": "cache_acceleration_not_proof_evidence",
                    }
            if lean_process_is_live(root):
                return {
                    "schema": SCHEMA,
                    "status": "deferred_live_lean_process",
                    "proof_scope": "cache_acceleration_not_proof_evidence",
                }
            return attach_seed(root, source, fingerprint, seed_heads)
        if not target.is_dir():
            return {
                "schema": SCHEMA,
                "status": "hydrate_then_publish",
                "semantic_fingerprint": fingerprint,
                "package_count": len(packages),
                "toolchain": toolchain,
                "proof_scope": "cache_acceleration_not_proof_evidence",
            }
        if lean_process_is_live(root):
            return {
                "schema": SCHEMA,
                "status": "deferred_live_lean_process",
                "proof_scope": "cache_acceleration_not_proof_evidence",
            }
        try:
            heads = package_heads(target)
        except PackageShareError as exc:
            return {
                "schema": SCHEMA,
                "status": "preserved_unsafe_or_dirty_workspace_cache",
                "detail": str(exc),
                "proof_scope": "cache_acceleration_not_proof_evidence",
            }
        expected_names = {row["name"] for row in packages if row["name"]}
        if set(heads) != expected_names:
            return {
                "schema": SCHEMA,
                "status": "hydrate_incomplete_workspace_cache",
                "semantic_fingerprint": fingerprint,
                "expected_package_count": len(expected_names),
                "observed_package_count": len(heads),
                "proof_scope": "cache_acceleration_not_proof_evidence",
            }
        return publish_seed(root, state_root, fingerprint, heads)
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def filesystem_compressed(path: Path) -> bool:
    compressed_flag = int(getattr(stat, "UF_COMPRESSED", 0))
    try:
        return bool(compressed_flag and (int(path.stat().st_flags) & compressed_flag))
    except (AttributeError, OSError):
        return False


def compact_setup_json(
    root: Path, *, minimum_bytes: int = DEFAULT_SETUP_COMPRESSION_MIN_BYTES
) -> dict[str, Any]:
    """Compress repeated Lake setup manifests byte-for-byte on macOS/APFS."""
    root = root.resolve()
    if (
        sys.platform != "darwin"
        or not Path("/usr/bin/ditto").is_file()
        or not Path("/usr/bin/chflags").is_file()
    ):
        return {
            "schema": SCHEMA,
            "status": "setup_compression_unsupported",
            "proof_scope": "storage_compaction_not_proof_evidence",
        }
    build_roots = [root / ".lake/build"]
    packages_root = root / ".lake/packages"
    if packages_root.is_dir():
        build_roots.extend(
            package / ".lake/build"
            for package in packages_root.iterdir()
            if (package / ".lake/build").is_dir()
        )
    candidates: list[Path] = []
    already_compressed = 0
    for build_root in build_roots:
        if not build_root.is_dir() or build_root.is_symlink():
            continue
        for path in build_root.rglob("*.setup.json"):
            if path.is_symlink() or not path.is_file() or path.stat().st_size < minimum_bytes:
                continue
            if filesystem_compressed(path):
                already_compressed += 1
            else:
                candidates.append(path)
    compressed = 0
    physical_bytes_freed = 0
    errors: list[dict[str, str]] = []
    for path in candidates:
        before = path.stat()
        source_hash = file_sha256(path)
        temporary = path.with_name(f".{path.name}.compress-{secrets.token_hex(8)}")
        try:
            copied = run(
                ["/usr/bin/ditto", "--hfsCompression", str(path), str(temporary)],
                timeout=120.0,
            )
            flagged = run(["/usr/bin/chflags", "compressed", str(temporary)])
            if copied.returncode or flagged.returncode:
                raise PackageShareError("filesystem compression command failed")
            if temporary.stat().st_size != before.st_size or file_sha256(temporary) != source_hash:
                raise PackageShareError("compressed file is not byte-identical")
            current = path.stat()
            if (
                current.st_ino != before.st_ino
                or current.st_size != before.st_size
                or current.st_mtime_ns != before.st_mtime_ns
            ):
                raise PackageShareError("setup manifest changed during compaction")
            before_blocks = int(before.st_blocks) * 512
            os.replace(temporary, path)
            physical_bytes_freed += max(
                0, before_blocks - int(path.stat().st_blocks) * 512
            )
            compressed += 1
        except (OSError, PackageShareError) as exc:
            errors.append({"path": str(path), "detail": str(exc)})
        finally:
            temporary.unlink(missing_ok=True)
    receipt = {
        "schema": SCHEMA,
        "status": "setup_compression_complete",
        "proof_scope": "storage_compaction_not_proof_evidence",
        "minimum_bytes": minimum_bytes,
        "candidate_count": len(candidates),
        "compressed_count": compressed,
        "already_compressed_count": already_compressed,
        "physical_bytes_freed_by_file_blocks": physical_bytes_freed,
        "error_count": len(errors),
        "errors": errors[:20],
        "validation": {
            "byte_identity_checked": True,
            "source_generation_checked": True,
            "proof_outputs_removed": False,
        },
    }
    atomic_json(root / ".lake/setup_json_compaction_receipt.json", receipt)
    return receipt


def plan_workspace(root: Path, state_root: Path) -> dict[str, Any]:
    """Report the exact non-mutating decision used by package sharing."""
    root = root.resolve()
    state_root = state_root.resolve()
    try:
        reject_mutable_symlinks(root)
    except PackageShareError as exc:
        return {
            "schema": SCHEMA,
            "status": "rejected_mutable_cache_symlink",
            "action": "preserve",
            "detail": str(exc),
            "proof_scope": "cache_acceleration_not_proof_evidence",
        }
    fingerprint, packages, toolchain = semantic_fingerprint(root)
    expected_names = {row["name"] for row in packages if row["name"]}
    seed = load_seed(state_root, fingerprint)
    target = root / ".lake/packages"
    if seed is not None:
        _source, seed_heads = seed
        if set(seed_heads) != expected_names:
            return {
                "schema": SCHEMA,
                "status": "preserved_incomplete_host_seed",
                "action": "preserve",
                "proof_scope": "cache_acceleration_not_proof_evidence",
            }
        if target.is_dir():
            try:
                target_heads = package_heads(target)
            except PackageShareError as exc:
                return {
                    "schema": SCHEMA,
                    "status": "preserved_unsafe_or_dirty_workspace_cache",
                    "action": "preserve",
                    "detail": str(exc),
                    "proof_scope": "cache_acceleration_not_proof_evidence",
                }
            if target_heads != seed_heads:
                return {
                    "schema": SCHEMA,
                    "status": "preserved_nonmatching_workspace_cache",
                    "action": "preserve",
                    "proof_scope": "cache_acceleration_not_proof_evidence",
                }
            if workspace_receipt_current(root, fingerprint, seed_heads):
                action = "reuse"
                status = "reused_shared_package_lineage"
            else:
                action = "reconcile"
                status = "ready_to_reconcile_host_seed"
        else:
            action = "attach"
            status = "ready_to_attach_host_seed"
        if action != "reuse" and lean_process_is_live(root):
            action = "defer"
            status = "deferred_live_lean_process"
        return {
            "schema": SCHEMA,
            "status": status,
            "action": action,
            "semantic_fingerprint": fingerprint,
            "package_count": len(seed_heads),
            "proof_scope": "cache_acceleration_not_proof_evidence",
        }
    if not target.is_dir():
        return {
            "schema": SCHEMA,
            "status": "hydrate_then_publish",
            "action": "hydrate",
            "semantic_fingerprint": fingerprint,
            "package_count": len(packages),
            "toolchain": toolchain,
            "proof_scope": "cache_acceleration_not_proof_evidence",
        }
    try:
        heads = package_heads(target)
    except PackageShareError as exc:
        return {
            "schema": SCHEMA,
            "status": "preserved_unsafe_or_dirty_workspace_cache",
            "action": "preserve",
            "detail": str(exc),
            "proof_scope": "cache_acceleration_not_proof_evidence",
        }
    if set(heads) != expected_names:
        return {
            "schema": SCHEMA,
            "status": "hydrate_incomplete_workspace_cache",
            "action": "hydrate",
            "semantic_fingerprint": fingerprint,
            "proof_scope": "cache_acceleration_not_proof_evidence",
        }
    live = lean_process_is_live(root)
    return {
        "schema": SCHEMA,
        "status": (
            "deferred_live_lean_process"
            if live
            else "ready_to_publish_host_seed"
        ),
        "action": "defer" if live else "publish",
        "semantic_fingerprint": fingerprint,
        "package_count": len(heads),
        "proof_scope": "cache_acceleration_not_proof_evidence",
    }


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--state-root", type=Path, default=default_state_root())
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--plan", action="store_true", help="report without mutation")
    mode.add_argument(
        "--compact-setup",
        action="store_true",
        help="byte-preservingly compact large Lake setup manifests where supported",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        if args.plan:
            receipt = plan_workspace(args.root, args.state_root)
        elif args.compact_setup:
            receipt = compact_setup_json(args.root)
        else:
            receipt = prepare_workspace(args.root, args.state_root)
    except (OSError, ValueError, json.JSONDecodeError, PackageShareError) as exc:
        print(f"lean-package-share: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
