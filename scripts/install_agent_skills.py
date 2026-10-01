#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Install this clone's Agent Skills into a user-selected skills directory.

The repository works without installation: an agent can read
``AGENTS.md`` and the files under ``skills/`` directly.  Installation
only makes the named skills available from other working directories.

The command is deliberately preview-first.  It changes the destination only
when ``--apply`` is present, and it never replaces a different installed skill
unless ``--force`` is also present.
"""

from __future__ import annotations

import argparse
import filecmp
import errno
import os
import shutil
import stat
import sys
import tempfile
from pathlib import Path

from agent_skill_catalog import SkillCatalogError, load_catalog


ROOT = Path(__file__).resolve().parents[1]


def skill_directories(catalog: dict[str, object]) -> dict[str, Path]:
    return {row["id"]: ROOT / Path(row["path"]).parent for row in catalog["skills"]}


def same_tree(left: Path, right: Path) -> bool:
    if not left.is_dir() or not right.is_dir():
        return False
    comparison = filecmp.dircmp(left, right)
    if comparison.left_only or comparison.right_only or comparison.common_funny:
        return False
    # dircmp compares stat signatures by default. A copied skill can retain
    # its timestamp and byte count after an edit, so compare instruction bytes
    # directly; this also avoids filecmp's metadata-keyed result cache.
    if any(
        (left / name).read_bytes() != (right / name).read_bytes()
        for name in comparison.common_files
    ):
        return False
    return all(same_tree(left / name, right / name) for name in comparison.common_dirs)


def resolved_path(path: Path) -> Path:
    try:
        return path.resolve()
    except RuntimeError as error:
        # Python 3.10-3.12 report symlink loops as RuntimeError.
        raise ValueError(f"cannot resolve path {path}: {error}") from error


def target_directory(args: argparse.Namespace) -> Path:
    if args.target_dir is not None:
        directory = resolved_path(args.target_dir.expanduser())
    elif args.target == "codex":
        codex_root = Path(os.environ.get("CODEX_HOME", Path.home() / ".codex"))
        directory = resolved_path((codex_root / "skills").expanduser())
    elif args.target == "claude":
        claude_root = Path(os.environ.get("CLAUDE_CONFIG_DIR", Path.home() / ".claude"))
        directory = resolved_path((claude_root / "skills").expanduser())
    else:
        raise ValueError("choose --target codex|claude or provide --target-dir")
    # Preview must not call an impossible destination "missing". The nearest
    # existing ancestor must be a directory before any skill is inspected.
    for ancestor in (directory, *directory.parents):
        if ancestor.exists():
            if not ancestor.is_dir():
                raise ValueError(f"skills destination must be a directory; {ancestor} is not a directory")
            break
    return directory


def selected_skills(
    args: argparse.Namespace, available: dict[str, Path]
) -> dict[str, Path]:
    if not args.skill:
        return available
    missing = sorted(set(args.skill) - set(available))
    if missing:
        raise ValueError(f"unknown skill(s): {', '.join(missing)}")
    return {name: available[name] for name in args.skill}


def status(source: Path, destination: Path, mode: str) -> str:
    if not destination.exists() and not destination.is_symlink():
        return "missing"
    if mode == "symlink":
        if destination.is_symlink():
            try:
                target = destination.resolve(strict=True)
            except RuntimeError:
                # Older pathlib versions report even strict loops this way.
                return "different"
            except OSError as error:
                if error.errno in {errno.ENOENT, errno.ENOTDIR, errno.ELOOP}:
                    return "different"
                raise
            if target == resolved_path(source):
                return "current"
        return "different"
    if destination.is_symlink():
        return "different"
    if same_entry(resolved_path(source), destination):
        return "current"
    return "current" if same_tree(source, destination) else "different"


def same_entry(left: Path, right: Path) -> bool:
    if left == right:
        return True
    try:
        left_stat, right_stat = left.lstat(), right.lstat()
    except (FileNotFoundError, NotADirectoryError):
        return False
    return (left_stat.st_dev, left_stat.st_ino) == (right_stat.st_dev, right_stat.st_ino)


def overlapping_entries(left: Path, right: Path) -> bool:
    # Path.resolve() preserves spelling on a case-insensitive filesystem.
    # Compare existing entry identities as well as ancestor path strings,
    # without following a leaf symlink that is safe to replace.
    return any(same_entry(left, parent) for parent in (right, *right.parents)) or any(
        same_entry(right, parent) for parent in left.parents
    )


def source_access_entries(source: Path) -> set[Path]:
    """Include links traversed through other links' targets, not just parents."""
    entries = {resolved_path(source), resolved_path(source.parent) / source.name}
    pending = [source]
    seen_links = set()
    while pending:
        access = pending.pop()
        for part in (access, *access.parents):
            if part.is_symlink():
                entry = resolved_path(part.parent) / part.name
                entries.add(entry)
                if entry not in seen_links:
                    seen_links.add(entry)
                    target = part.readlink()
                    pending.append(target if target.is_absolute() else part.parent / target)
    return entries


def validate_destination(source: Path, destination: Path, mode: str) -> None:
    source_path = resolved_path(source)
    # Replacement moves the destination entry, not a symlink's target. Resolve
    # its parent so aliases cannot conceal an overlap with the source tree.
    destination_path = resolved_path(destination.parent) / destination.name
    if same_entry(source_path, destination_path) and mode == "copy":
        return
    if any(
        overlapping_entries(candidate, destination_path)
        for candidate in source_access_entries(source)
    ):
        raise ValueError(
            f"skill source and destination must not overlap: {source} -> {destination} ({mode})"
        )


def install_one(source: Path, destination: Path, mode: str, force: bool) -> None:
    validate_destination(source, destination, mode)
    state = status(source, destination, mode)
    if state == "current":
        return
    if state == "different" and not force:
        raise ValueError(
            f"{destination} already contains different material; use --force to replace it"
        )
    destination.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{destination.name}.install-", dir=destination.parent))
    incoming, previous = staging / "incoming", staging / "previous"
    retain_backup = False
    installed = False
    try:
        # Complete preparation before moving any installed material. A failed
        # copy must never turn a working skill into a partial installation.
        if mode == "symlink":
            incoming.symlink_to(source, target_is_directory=True)
        else:
            shutil.copytree(source, incoming)
        if destination.exists() or destination.is_symlink():
            os.replace(destination, previous)
        try:
            os.replace(incoming, destination)
            installed = True
        except OSError as error:
            if previous.exists() or previous.is_symlink():
                try:
                    os.replace(previous, destination)
                except OSError as restore_error:
                    retain_backup = True
                    raise OSError(
                        f"installation failed: {error}; restoration failed: {restore_error}; "
                        f"previous installation retained at {previous}"
                    ) from restore_error
            raise
    finally:
        if not retain_backup:
            try:
                # Copies and obsolete backups may contain readonly folders.
                # Only change permissions inside staging, without following
                # skill symlinks into the source or another user directory.
                for directory, _, _ in os.walk(staging, followlinks=False):
                    path = Path(directory)
                    path.chmod(path.stat().st_mode | stat.S_IWUSR | stat.S_IXUSR)
                shutil.rmtree(staging)
            except OSError as cleanup_error:
                if not installed:
                    raise
                print(
                    f"warning: installed {destination}; could not remove staging at "
                    f"{staging}: {cleanup_error}", file=sys.stderr,
                )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--list", action="store_true", help="list clone-local skills")
    destination = result.add_mutually_exclusive_group()
    destination.add_argument("--target", choices=("codex", "claude"))
    destination.add_argument("--target-dir", type=Path)
    result.add_argument("--skill", action="append", help="install only this named skill")
    result.add_argument("--mode", choices=("copy", "symlink"), default="copy")
    result.add_argument("--apply", action="store_true", help="perform the displayed changes")
    result.add_argument("--check", action="store_true", help="fail unless every selection is current")
    result.add_argument("--force", action="store_true", help="replace a different same-name skill")
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        catalog = load_catalog()
        available = skill_directories(catalog)
    except (OSError, SkillCatalogError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    if args.list:
        for row in catalog["skills"]:
            print(f"{row['id']}\t{row['description']}\t{row['path']}")
        if args.target is None and args.target_dir is None:
            return 0

    try:
        target = target_directory(args)
        chosen = selected_skills(args, available)
        # Validate every selection before printing or installing any of them.
        for name, source in chosen.items():
            validate_destination(source, target / name, args.mode)
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    failures: list[str] = []
    for name, source in chosen.items():
        destination = target / name
        try:
            state = status(source, destination, args.mode)
        except (OSError, ValueError) as error:
            print(f"error: cannot inspect {name} at {destination}: {error}", file=sys.stderr)
            failures.append(name)
            continue
        print(f"{state:9} {name}: {source} -> {destination} ({args.mode})")
        if args.check:
            if state != "current":
                failures.append(name)
            continue
        if args.apply:
            try:
                install_one(source, destination, args.mode, args.force)
            except (OSError, ValueError) as exc:
                print(f"error: {exc}", file=sys.stderr)
                failures.append(name)

    if args.check and failures:
        print(f"not current: {', '.join(failures)}", file=sys.stderr)
        return 1
    if failures:
        return 1
    if not args.apply and not args.check:
        print("preview only; add --apply to install")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
