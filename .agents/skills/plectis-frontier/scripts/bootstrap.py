#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: MIT-0
"""Inspect, fetch or smoke-test one pinned public Plectis corpus; no agent calls."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any

SOURCE_FILE = Path(__file__).resolve().parents[1] / "source.json"
PUBLIC_URL = "https://github.com/wcook04/plectis-lean-erdos249-257.git"
REQUIRED = (
    "AGENTS.override.md", "AGENTS.md", "docs/claims.json",
    "scripts/agent_entry.py", "scripts/query_corpus.py",
    "skills/mine-open-problem/SKILL.md",
    "skills/erdos-research-return/SKILL.md",
    "skills/propagate-research-consequences/SKILL.md",
)


class BootstrapError(RuntimeError):
    """A prerequisite or explicit permission is missing."""


def load_source(path: Path = SOURCE_FILE) -> dict[str, str]:
    source = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(source, dict) or source.get("schema") != "plectis-frontier-source/1":
        raise BootstrapError("Unrecognised source manifest schema")
    if source.get("repository") != PUBLIC_URL:
        raise BootstrapError("Source must be the canonical public HTTPS repository")
    if not isinstance(source.get("commit"), str) or not re.fullmatch(r"[0-9a-f]{40}", source["commit"]):
        raise BootstrapError("Source commit must be a full 40-character lowercase SHA")
    return source


def child_environment() -> dict[str, str]:
    # Do not forward model, registry, GitHub, SSH or other account credentials.
    keep = ("PATH", "SYSTEMROOT", "WINDIR", "TMPDIR", "TEMP", "TMP")
    env = {key: os.environ[key] for key in keep if key in os.environ}
    env.update({
        "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_TERMINAL_PROMPT": "0", "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OPTIONAL_LOCKS": "0", "GIT_PAGER": "cat",
        "PYTHONNOUSERSITE": "1", "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONUTF8": "1", "PYTHONPATH": "", "LC_ALL": "C.UTF-8",
    })
    return env


def run(argv: list[str], cwd: Path, timeout: int = 60) -> str:
    result = subprocess.run(argv, cwd=cwd, env=child_environment(),
                            text=True, encoding="utf-8", errors="replace",
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=timeout, check=False)
    if result.returncode:
        detail = result.stderr[-2000:].strip()
        raise BootstrapError(f"Command failed ({result.returncode}): {argv[0]}: {detail}")
    if len(result.stdout.encode("utf-8")) > 131072:
        raise BootstrapError("Command output exceeded the 128 KiB smoke-test limit")
    return result.stdout.strip()


def git(cwd: Path, *args: str, timeout: int = 60) -> str:
    executable = shutil.which("git")
    if not executable:
        raise BootstrapError("Git is required; install it through your approved system route")
    return run([executable, "-c", "credential.helper=", "-c", f"core.hooksPath={os.devnull}",
                "-c", "core.fsmonitor=false", "-c", "protocol.allow=never", "-c", "protocol.https.allow=always",
                "-c", "http.followRedirects=false", *args], cwd, timeout)


def verify(destination: Path, source: dict[str, str]) -> dict[str, Any]:
    if destination.is_symlink() or not destination.is_dir():
        raise BootstrapError("Destination must be a real checkout directory, not a symlink")
    root = destination.resolve()
    if not (root / ".git").is_dir() or (root / ".git").is_symlink():
        raise BootstrapError("Expected a standalone checkout with its own .git directory")
    actual_root = Path(git(root, "rev-parse", "--show-toplevel")).resolve()
    if actual_root != root:
        raise BootstrapError("Destination is not the checkout root")
    if git(root, "config", "--get", "remote.origin.url") != source["repository"]:
        raise BootstrapError("Origin differs from the pinned public repository")
    head = git(root, "rev-parse", "HEAD")
    if head != source["commit"]:
        raise BootstrapError(f"Wrong commit: expected {source['commit']}, found {head}")
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise BootstrapError("Initial smoke test requires a clean checkout; existing work is left untouched")
    for relative in REQUIRED:
        path = root / relative
        components = [path, *list(path.parents)[:len(Path(relative).parts) - 1]]
        if any(part.is_symlink() for part in components) or not path.is_file():
            raise BootstrapError(f"Required regular file missing or symlinked: {relative}")
        git(root, "ls-files", "--error-unmatch", "--", relative)
    return {"repository": source["repository"], "commit": head,
            "checkout": str(root), "required_files": len(REQUIRED)}


def prepare(destination: Path, source: dict[str, str], allow_network: bool) -> dict[str, Any]:
    if not allow_network:
        raise BootstrapError("Fetching requires owner approval and --allow-network")
    if destination.exists() or destination.is_symlink():
        raise BootstrapError("Destination already exists; refusing to overwrite, reset or delete it")
    if not destination.parent.is_dir():
        raise BootstrapError("Create the intended parent directory first")
    root = destination.parent.resolve() / destination.name
    root.mkdir(mode=0o700)
    # A failed attempt is retained for inspection, never recursively deleted.
    git(root, "init", "--template=")
    git(root, "remote", "add", "origin", source["repository"])
    git(root, "fetch", "--depth", "1", "--no-tags", "origin", source["commit"], timeout=300)
    git(root, "checkout", "--detach", "FETCH_HEAD", timeout=120)
    return {"status": "source-verified-no-code-executed", **verify(root, source)}


def smoke(destination: Path, source: dict[str, str], allow_execution: bool) -> dict[str, Any]:
    if not allow_execution:
        raise BootstrapError("Running repository Python requires owner approval and --allow-execution")
    receipt = verify(destination, source)
    root = Path(receipt["checkout"])
    entry = run([sys.executable, "-B", "-s", "scripts/agent_entry.py", "--entry",
                 "Attempt one bounded research continuation and prepare a checkable return", "--json"], root)
    packet = json.loads(entry)
    if not isinstance(packet, dict) or packet.get("schema") != "plectis-agent-entry/1" or not packet.get("primary_lane"):
        raise BootstrapError("Entry command did not produce its declared routing contract")
    overview = run([sys.executable, "-B", "-s", "scripts/query_corpus.py",
                    "--overview", "--format", "card"], root)
    if not overview:
        raise BootstrapError("Overview was empty")
    verify(root, source)  # A read-only smoke run must not modify the checkout.
    return {"status": "entry-smoke-passed-not-lean-verified", **receipt,
            "checks": [{"name": "agent-entry", "output": packet},
                       {"name": "corpus-overview", "output": overview}],
            "limits": "No Lean build, research result, hosted-agent run or registry audit was performed"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", nargs="?", choices=("describe", "prepare", "verify", "smoke"), default="describe")
    parser.add_argument("--destination", type=Path)
    parser.add_argument("--allow-network", action="store_true")
    parser.add_argument("--allow-execution", action="store_true")
    args = parser.parse_args(argv)
    try:
        if sys.version_info < (3, 11):
            raise BootstrapError("Python 3.11 or newer is required")
        source = load_source()
        if args.action == "describe":
            value = {"status": "inspection-only", "source": source,
                     "required_files": list(REQUIRED), "git_available": bool(shutil.which("git")),
                     "network_performed": False, "repository_code_executed": False}
        else:
            if args.destination is None:
                raise BootstrapError("--destination is required")
            destination = args.destination.expanduser().absolute()
            if args.action == "prepare":
                value = prepare(destination, source, args.allow_network)
            elif args.action == "smoke":
                value = smoke(destination, source, args.allow_execution)
            else:
                value = {"status": "source-verified-no-code-executed", **verify(destination, source)}
        print(json.dumps(value, ensure_ascii=False, indent=2))
        return 0
    except (BootstrapError, OSError, ValueError, subprocess.SubprocessError) as exc:
        print(json.dumps({"status": "blocked", "error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
