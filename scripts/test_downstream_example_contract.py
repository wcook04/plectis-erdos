#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the downstream consumer example explicit about its open boundary."""

from __future__ import annotations

import tomllib
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def contract_errors(example: str, readme: str, lakefile: str) -> list[str]:
    """Return missing public-interface and claim-ceiling obligations."""
    errors: list[str] = []
    example_requirements = {
        "supported root import": "import Erdos249257",
        "proved headline consumer": "theorem downstream_base_three_irrational",
        "conditional consumer": "theorem downstream_conditional_rational_shell_bound",
        "explicit analytic hypothesis": "(hupper : (whole : ℝ) - (pfx : ℝ) ≤",
        "exact shell-power conclusion":
            "(2 : ℝ) ^ X ≤\n      ((whole.den * pfx.den : ℕ) : ℝ) * (K + 1)",
        "conditional library adapter":
            "prefixDenominator_shell_power_bound_of_rational_difference",
        "universal claim ceiling":
            "this does not prove the universal\nErdős #257 statement",
    }
    for label, token in example_requirements.items():
        if token not in example:
            errors.append(f"downstream example lost {label}")

    readme_requirements = {
        "consumer route": "[`examples/Examples.lean`](examples/Examples.lean)",
        "conditional interface description":
            "conditional rational shell-pressure\ninterface",
        "explicit-hypothesis boundary": "leaving its analytic hypothesis explicit",
        "universal claim ceiling":
            "does\nnot prove the still-open universal Erdős #257 statement",
    }
    for label, token in readme_requirements.items():
        if token not in readme:
            errors.append(f"README lost downstream {label}")

    try:
        lake_config = tomllib.loads(lakefile)
    except tomllib.TOMLDecodeError:
        errors.append("lakefile is not valid TOML")
        return errors

    if lake_config.get("defaultTargets") != ["Erdos249257", "ErdosProblems"]:
        errors.append(
            "lakefile defaultTargets must remain exactly "
            "['Erdos249257', 'ErdosProblems']"
        )

    examples_targets = [
        target
        for target in lake_config.get("lean_lib", [])
        if target.get("name") == "Examples"
    ]
    if len(examples_targets) != 1:
        errors.append("lakefile must declare exactly one Examples lean_lib")
    elif examples_targets[0].get("srcDir") != "examples":
        errors.append("Examples lean_lib must use srcDir examples")
    return errors


def main() -> int:
    example = (ROOT / "examples" / "Examples.lean").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    lakefile = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    assert not contract_errors(example, readme, lakefile)

    implicit_hypothesis = example.replace(
        "(hupper : (whole : ℝ) - (pfx : ℝ) ≤",
        "(upperBound : (whole : ℝ) - (pfx : ℝ) ≤",
        1,
    )
    assert any(
        "explicit analytic hypothesis" in error
        for error in contract_errors(implicit_hypothesis, readme, lakefile)
    )

    weakened_conclusion = example.replace(
        "(2 : ℝ) ^ X ≤\n      ((whole.den * pfx.den : ℕ) : ℝ) * (K + 1)",
        "0 ≤ ((whole.den * pfx.den : ℕ) : ℝ) * (K + 1)",
        1,
    )
    assert any(
        "exact shell-power conclusion" in error
        for error in contract_errors(weakened_conclusion, readme, lakefile)
    )

    lost_local_ceiling = example.replace(
        "this does not prove the universal\nErdős #257 statement",
        "this proves the universal\nErdős #257 statement",
        1,
    )
    assert any(
        "universal claim ceiling" in error
        for error in contract_errors(lost_local_ceiling, readme, lakefile)
    )

    overstated_readme = readme.replace(
        "does\nnot prove the still-open universal Erdős #257 statement",
        "proves the universal Erdős #257 statement",
        1,
    )
    assert any(
        "universal claim ceiling" in error
        for error in contract_errors(example, overstated_readme, lakefile)
    )

    renamed_target = lakefile.replace(
        'name = "Examples"',
        'name = "ConsumerExamples"',
        1,
    )
    assert any(
        "exactly one Examples lean_lib" in error
        for error in contract_errors(example, readme, renamed_target)
    )

    displaced_source = lakefile.replace(
        'srcDir = "examples"',
        'srcDir = "consumer-examples"',
        1,
    )
    assert any(
        "srcDir examples" in error
        for error in contract_errors(example, readme, displaced_source)
    )

    default_example = lakefile.replace(
        'defaultTargets = ["Erdos249257", "ErdosProblems"]',
        'defaultTargets = ["Erdos249257", "ErdosProblems", "Examples"]',
        1,
    )
    assert any(
        "defaultTargets" in error
        for error in contract_errors(example, readme, default_example)
    )

    print(
        "test_downstream_example_contract: proved and conditional consumers "
        "retain an exact conclusion, explicit open boundary, and non-default "
        "Lake target; 7 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
