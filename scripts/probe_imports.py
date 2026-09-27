#!/usr/bin/env python3
"""Print the corpus modules that `research/probes/*.lean` import, one line.

The kernel-probe workflow builds these before it runs the probes: the Lake cache
a probe run restores holds the supported roots, and a paper-coverage module a
probe imports may be missing from it (Lean then reports that the module's
object file does not exist). Toolchain and library imports are skipped.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXTERNAL = ("Lean", "Mathlib", "Init", "Std", "Batteries", "Aesop", "Qq", "Plausible", "ProofWidgets")


def probe_imports(root: Path = ROOT) -> list[str]:
    modules: set[str] = set()
    for probe in sorted((root / "research" / "probes").glob("*.lean")):
        for line in probe.read_text(encoding="utf-8").splitlines():
            match = re.match(r"\s*import\s+(.+)", line)
            if not match:
                if line.strip() and not line.strip().startswith(("--", "/-")):
                    break
                continue
            for module in match.group(1).split():
                if module.split(".")[0] not in EXTERNAL:
                    modules.add(module)
    return sorted(modules)


if __name__ == "__main__":
    print(" ".join(probe_imports()))
