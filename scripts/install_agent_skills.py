#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Install this clone's Agent Skills into a user-selected skills directory.

The repository works without installation: an agent can read
``AGENTS.override.md`` and the files under ``skills/`` directly.  Installation
only makes the named skills available from other working directories.

The command is deliberately preview-first.  It changes the destination only
when ``--apply`` is present, and it never replaces a different installed skill
unless ``--force`` is also present.
"""

from __future__ import annotations

import argparse
import filecmp
import os
import shutil
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SKILLS_ROOT = ROOT / "skills"


def skill_directories() -> dict[str, Path]:
    return {
        path.parent.name: path.parent
        for path in sorted(SKILLS_ROOT.glob("*/SKILL.md"))
        if path.is_file()
    }


def same_tree(left: Path, right: Path) -> bool:
    if not left.is_dir() or not right.is_dir():
        return False
    comparison = filecmp.dircmp(left, right)
    if comparison.left_only or comparison.right_only or comparison.funny_files:
        return False
    if comparison.diff_files:
        return False
    return all(same_tree(left / name, right / name) for name in comparison.common_dirs)


def target_directory(args: argparse.Namespace) -> Path:
    if args.target_dir is not None:
        return args.target_dir.expanduser().resolve()
    if args.target == "codex":
        codex_root = Path(os.environ.get("CODEX_HOME", Path.home() / ".codex"))
        return (codex_root / "skills").expanduser().resolve()
    if args.target == "claude":
        claude_root = Path(os.environ.get("CLAUDE_CONFIG_DIR", Path.home() / ".claude"))
        return (claude_root / "skills").expanduser().resolve()
    raise ValueError("choose --target codex|claude or provide --target-dir")


def selected_skills(args: argparse.Namespace) -> dict[str, Path]:
    available = skill_directories()
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
        if destination.is_symlink() and destination.resolve() == source.resolve():
            return "current"
        return "different"
    if destination.is_symlink():
        return "different"
    return "current" if same_tree(source, destination) else "different"


def install_one(source: Path, destination: Path, mode: str, force: bool) -> None:
    state = status(source, destination, mode)
    if state == "current":
        return
    if state == "different" and not force:
        raise ValueError(
            f"{destination} already contains different material; use --force to replace it"
        )
    if destination.exists() or destination.is_symlink():
        if destination.is_dir() and not destination.is_symlink():
            shutil.rmtree(destination)
        else:
            destination.unlink()
    destination.parent.mkdir(parents=True, exist_ok=True)
    if mode == "symlink":
        destination.symlink_to(source, target_is_directory=True)
    else:
        shutil.copytree(source, destination)


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
    available = skill_directories()
    if args.list:
        for name in available:
            print(f"{name}\t{available[name].relative_to(ROOT)}")
        if args.target is None and args.target_dir is None:
            return 0

    try:
        target = target_directory(args)
        chosen = selected_skills(args)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    failures: list[str] = []
    for name, source in chosen.items():
        destination = target / name
        state = status(source, destination, args.mode)
        print(f"{state:9} {name}: {source} -> {destination} ({args.mode})")
        if args.check:
            if state != "current":
                failures.append(name)
            continue
        if args.apply:
            try:
                install_one(source, destination, args.mode, args.force)
            except ValueError as exc:
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
