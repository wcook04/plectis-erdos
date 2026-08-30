#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the required Lean workflow on the canonical command environment."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "lean.yml"
WARM_WORKFLOW = ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
REQUIRED_KEYS = {
    "GIT_CONFIG_NOSYSTEM",
    "GIT_CONFIG_GLOBAL",
    "GIT_OPTIONAL_LOCKS",
    "GIT_NO_REPLACE_OBJECTS",
    "GIT_ASKPASS",
    "PYTHONHOME",
    "PYTHONPATH",
    "PYTHONOPTIMIZE",
    "PATH",
    "LC_ALL",
    "LANG",
    "PYTHONHASHSEED",
    "PYTHONNOUSERSITE",
    "PYTHONDONTWRITEBYTECODE",
    "PYTHONUTF8",
}


def require(condition: bool, message: str) -> None:
    """Keep workflow portability failures active under ``python -O``."""
    if not condition:
        raise AssertionError(message)


def workflow_environment(path: Path) -> dict[str, str]:
    workflow = path.read_text(encoding="utf-8")
    match = re.search(r"(?ms)^env:\n(?P<body>.*?)(?=^jobs:\n)", workflow)
    indent = "  "
    if match is None:
        match = re.search(
            r"(?ms)^  warm:\n.*?^    env:\n(?P<body>.*?)(?=^    steps:\n)",
            workflow,
        )
        indent = "      "
    require(match is not None, f"{path.name} lost its workflow environment")
    body = match.group("body")
    return dict(
        re.findall(rf"(?m)^{re.escape(indent)}([A-Z][A-Z0-9_]+): (.+)$", body)
    )


def main() -> int:
    environment = workflow_environment(WORKFLOW)
    warm_environment = workflow_environment(WARM_WORKFLOW)
    require(
        environment == warm_environment,
        "lean.yml and lean-cache-warm.yml have divergent command environments",
    )
    require(
        REQUIRED_KEYS <= environment.keys(),
        "Lean workflow environment lost a required Git/Python portability key",
    )
    workflow = WORKFLOW.read_text(encoding="utf-8")
    require(
        re.search(r"(?m)^    env:\n", workflow) is None,
        "a Lean job added a job-level environment that could override the baseline",
    )
    print("test_lean_workflow_environment: Lean jobs share the isolated command environment")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
