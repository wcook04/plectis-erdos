#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the consumer examples from a separate Lake project, without rebuilding."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

import validation_singleflight as singleflight
import lean_fast_build as fast_build

ROOT = Path(__file__).resolve().parents[1]


def prepare_consumer(root: Path, destination: Path) -> str:
    """Resolve the prepared package closure through Lake's path dependency format."""
    root = root.resolve()
    for module in ("Erdos249257", "ErdosProblems"):
        if not (root / f".lake/build/lib/lean/{module}.olean").is_file():
            raise ValueError(f"build {module} first with scripts/lean_fast_build.py")
    toolchain = (root / "lean-toolchain").read_text().strip()
    if not toolchain or any(char.isspace() for char in toolchain):
        raise ValueError("lean-toolchain must name one installed toolchain")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    entries = []
    for package in manifest["packages"]:
        name = package["name"]
        if not isinstance(name, str) or Path(name).name != name or name in {".", ".."}:
            raise ValueError("invalid dependency package name")
        package_root = root / manifest.get("packagesDir", ".lake/packages") / name
        config = package.get("configFile") or "lakefile.lean"
        if not (package_root / config).is_file():
            raise ValueError(f"prepared dependency {name} is missing; run the supported build first")
        entries.append({"name": name, "scope": package.get("scope", ""),
                        "type": "path", "dir": str(package_root.resolve()),
                        "inherited": True, "configFile": config,
                        "manifestFile": package.get("manifestFile", "lake-manifest.json")})
    entries.append({"name": "erdos249257", "type": "path", "dir": str(root),
                    "inherited": False, "configFile": "lakefile.toml",
                    "manifestFile": "lake-manifest.json"})
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "lean-toolchain").write_text(toolchain + "\n")
    (destination / "lakefile.toml").write_text(
        'name = "plectis_consumer"\n\n[[require]]\nname = "erdos249257"\n'
        + "path = " + json.dumps(str(root)) + "\n"
    )
    (destination / "lake-manifest.json").write_text(json.dumps({
        "version": "1.1.0", "name": "plectis_consumer", "lakeDir": ".lake",
        "packagesDir": ".lake/packages", "packages": entries,
    }, indent=2) + "\n")
    shutil.copyfile(root / "research/examples/Examples.lean", destination / "Consumer.lean")
    return toolchain


def check(root: Path, *, runner=subprocess.run) -> int:
    state = singleflight.ensure_state_root(singleflight.default_state_root())
    lock_path = singleflight.resource_lock_path(state, "lean-host")
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    lock = singleflight.open_lock(lock_path, blocking=False)
    if lock is None:
        print("downstream reuse: another Lean build owns the host; retry after it finishes")
        return 75
    try:
        with tempfile.TemporaryDirectory(prefix="plectis-consumer-") as tmp:
            destination = Path(tmp)
            prepare_consumer(root, destination)
            result = runner(
                fast_build.lake_command("env", "lean", "Consumer.lean"),
                cwd=destination, env=singleflight.command_environment(), timeout=300,
            )
            if result.returncode == 0:
                print("downstream reuse: separate Lake project accepted the unchanged consumer examples")
            return result.returncode
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        print(f"downstream reuse: {error}")
        return 1
    finally:
        os.close(lock)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="already built checkout to consume")
    args = parser.parse_args()
    return check(args.root)


if __name__ == "__main__":
    raise SystemExit(main())
