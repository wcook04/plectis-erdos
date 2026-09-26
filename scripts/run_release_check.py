#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Prepare a cold checkout, then run the existing public release gate.

The release gate deliberately runs its children with its own Python executable.
This entry selects Python 3.12, installs the committed hash-checked lock into
an ignored local environment, and builds the one Lean import needed by its
live proof-state control before starting the expensive gate. CI may continue
to call check_release.py directly after preparing those prerequisites.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LOCK = ROOT / "scripts" / "requirements-release.txt"
VENV = ROOT / ".lake" / "release-python"
PILOT_MODULE = "Erdos249257.CurvatureCarry"
PILOT_OLEAN = ROOT / ".lake/build/lib/lean/Erdos249257/CurvatureCarry.olean"
PIN = re.compile(r"^([A-Za-z0-9][A-Za-z0-9_.-]*)==([^\s#]+)\s+--hash=sha256:")


class PreparationError(RuntimeError):
    """A release prerequisite could not be prepared."""


def run(argv: list[str], *, root: Path = ROOT) -> None:
    result = subprocess.run(argv, cwd=root, check=False)
    if result.returncode:
        raise PreparationError(f"exit {result.returncode}: {' '.join(argv)}")


def python_version(executable: str) -> tuple[int, int] | None:
    try:
        result = subprocess.run(
            [executable, "-c", "import sys; print(*sys.version_info[:2])"],
            capture_output=True, text=True, check=False, timeout=10,
        )
        return tuple(map(int, result.stdout.split())) if result.returncode == 0 else None
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return None


def select_python(explicit: str | None = None) -> str:
    candidates = [explicit] if explicit else [sys.executable, shutil.which("python3.12")]
    for candidate in candidates:
        if candidate and python_version(candidate) == (3, 12):
            return candidate
    raise PreparationError(
        "Python 3.12 is required for the committed release dependency lock; "
        "install it or pass --python /path/to/python3.12"
    )


def expected_packages(lock: Path | None = None) -> dict[str, str]:
    lock = lock or LOCK
    pins: dict[str, str] = {}
    for line in lock.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        match = PIN.match(line)
        if match is None:
            raise PreparationError(f"unrecognised release dependency lock row: {line[:80]}")
        name, version = match.groups()
        pins[name] = version
    if not pins or "pypdf" not in pins:
        raise PreparationError("release dependency lock lacks the required pypdf pin")
    return pins


def installed_packages(python: Path, names: list[str]) -> dict[str, str]:
    code = (
        "import importlib.metadata as m, json, sys\n"
        "out = {}\n"
        "for name in json.loads(sys.argv[1]):\n"
        "    try: out[name] = m.version(name)\n"
        "    except m.PackageNotFoundError: out[name] = None\n"
        "print(json.dumps(out))\n"
    )
    result = subprocess.run(
        [str(python), "-c", code, json.dumps(names)],
        cwd=ROOT, capture_output=True, text=True, check=False, timeout=20,
    )
    if result.returncode:
        raise PreparationError("cannot inspect the selected release Python environment")
    return json.loads(result.stdout)


def check_pdf_import(python: Path) -> None:
    """Check the PDF operation needed by the gate, beyond package metadata."""
    result = subprocess.run(
        [str(python), "-c", "from pypdf import PdfReader, PdfWriter"],
        cwd=ROOT, capture_output=True, text=True, check=False, timeout=20,
    )
    if result.returncode:
        raise PreparationError(
            "pypdf is installed but cannot load PdfReader and PdfWriter: "
            + result.stderr.strip()[-500:]
        )


def prepare_python(bootstrap: str) -> Path:
    python = VENV / "bin" / "python"
    if not python.is_file():
        VENV.parent.mkdir(parents=True, exist_ok=True)
        run([bootstrap, "-m", "venv", str(VENV)])
    if python_version(str(python)) != (3, 12):
        raise PreparationError("release virtual environment is not Python 3.12")
    pins = expected_packages()
    actual = installed_packages(python, list(pins))
    if actual != pins:
        print("release preparation: installing committed hash-pinned Python dependencies", flush=True)
        run([
            str(python), "-m", "pip", "install", "--disable-pip-version-check",
            "--no-cache-dir", "--require-hashes", "--requirement", str(LOCK),
        ])
        actual = installed_packages(python, list(pins))
        if actual != pins:
            mismatches = sorted(name for name in pins if actual.get(name) != pins[name])
            raise PreparationError(f"release dependency versions still differ: {mismatches}")
    check_pdf_import(python)
    print(f"release preparation: {len(pins)} pinned packages verified with {python}", flush=True)
    return python


def prepare_pilot(python: Path) -> None:
    print(f"release preparation: building Lean pilot import {PILOT_MODULE}", flush=True)
    run([str(python), "scripts/lean_fast_build.py", "--jobs", "2", PILOT_MODULE])
    if not PILOT_OLEAN.is_file():
        raise PreparationError(f"Lean pilot import was not materialised: {PILOT_OLEAN}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--python", help="Python 3.12 interpreter for the release environment")
    parser.add_argument("--prepare-only", action="store_true", help="prepare prerequisites without running the release gate")
    args = parser.parse_args()
    try:
        python = prepare_python(select_python(args.python))
        prepare_pilot(python)
        if args.prepare_only:
            return 0
        print("release preparation: running the existing release gate", flush=True)
        result = subprocess.run([str(python), "scripts/check_release.py"], cwd=ROOT, check=False)
        return result.returncode
    except PreparationError as exc:
        print(f"release preparation failed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
