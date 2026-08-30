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
            "conditional shell-pressure example",
        "explicit-hypothesis boundary": "leaves the analytic\nhypothesis explicit",
        "universal claim ceiling":
            "does not prove universal #257",
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


def portfolio_contract_errors(
    problem249: str, problem269: str, portfolio_readme: str
) -> list[str]:
    """Return missing exact-wrapper and open-boundary obligations."""
    errors: list[str] = []
    requirements = {
        "Problem249 exact wrapper": (
            problem249,
            "irrational_totientSeries_of_actualLcmOrbitSeparationSupply",
        ),
        "Problem249 exact premise": (
            problem249,
            "Erdos249257.ExternalVerification.PowerTwoActualLcmOrbitSeparationSupply",
        ),
        "Problem249 open separation boundary": (
            problem249,
            "separation supply is a premise, not a proved",
        ),
        "Problem249 natural-prime wrapper": (
            problem249,
            "irrational_totient_series_of_naturalPrimeTailOrbitStrictGap",
        ),
        "Problem249 strict-gap producer boundary": (
            problem249,
            "nonpositive-block density and the cofinal prime strict-gap supply remain open",
        ),
        "Problem269 residue/coboundary wrapper": (
            problem269,
            "carry_eq_residueDigit_add_coboundary",
        ),
        "Problem269 local-window wrapper": (
            problem269,
            "no_positive_reducedCarry_of_cofinalLocalWindowEscape",
        ),
        "Problem269 exact open producer": (
            problem269,
            "CofinalLocalWindowEscape",
        ),
        "Problem269 actual-series boundary": (
            problem269,
            "actual-series/rationality bridge",
        ),
        "portfolio first target": (
            portfolio_readme,
            "examples/ExternalVerificationPortfolio/Problem249.lean",
        ),
        "portfolio second target": (
            portfolio_readme,
            "examples/ExternalVerificationPortfolio/Problem269.lean",
        ),
        "portfolio conditional claim ceiling": (
            portfolio_readme,
            "conditional obstruction, not\nan unconditional #269 endpoint",
        ),
        "portfolio terminal evidence boundary": (
            portfolio_readme,
            "a dependency-bootstrap\nor capacity deferral is not theorem evidence",
        ),
    }
    for label, (surface, token) in requirements.items():
        if token not in surface:
            errors.append(f"external verification portfolio lost {label}")
    if "existing `ExternalVerification/Solution.lean` mismatch" in portfolio_readme:
        errors.append("external verification portfolio retained stale Solution mismatch")
    return errors


def main() -> int:
    example = (ROOT / "examples" / "Examples.lean").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    lakefile = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    assert not contract_errors(example, readme, lakefile)
    problem249 = (
        ROOT / "examples" / "ExternalVerificationPortfolio" / "Problem249.lean"
    ).read_text(encoding="utf-8")
    problem269 = (
        ROOT / "examples" / "ExternalVerificationPortfolio" / "Problem269.lean"
    ).read_text(encoding="utf-8")
    portfolio_readme = (
        ROOT / "examples" / "ExternalVerificationPortfolio" / "README.md"
    ).read_text(encoding="utf-8")
    assert not portfolio_contract_errors(problem249, problem269, portfolio_readme)

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
        "does not prove universal #257",
        "proves universal #257",
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

    renamed_problem249_wrapper = problem249.replace(
        "irrational_totientSeries_of_actualLcmOrbitSeparationSupply",
        "irrational_totientSeries_of_unspecifiedSupply",
    )
    assert any(
        "Problem249 exact wrapper" in error
        for error in portfolio_contract_errors(
            renamed_problem249_wrapper, problem269, portfolio_readme
        )
    )

    renamed_natural_prime_wrapper = problem249.replace(
        "irrational_totient_series_of_naturalPrimeTailOrbitStrictGap",
        "irrational_totient_series_of_unspecifiedGap",
    )
    assert any(
        "Problem249 natural-prime wrapper" in error
        for error in portfolio_contract_errors(
            renamed_natural_prime_wrapper, problem269, portfolio_readme
        )
    )

    hidden_problem269_boundary = problem269.replace(
        "actual-series/rationality bridge",
        "completed actual-series bridge",
        1,
    )
    assert any(
        "Problem269 actual-series boundary" in error
        for error in portfolio_contract_errors(
            problem249, hidden_problem269_boundary, portfolio_readme
        )
    )

    print(
        "test_downstream_example_contract: proved and conditional consumers "
        "retain an exact conclusion, explicit open boundary, and non-default "
        "Lake target; portfolio wrappers and open boundaries remain exact; "
        "10 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
