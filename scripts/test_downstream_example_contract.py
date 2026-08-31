#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the downstream consumer example explicit about its open boundary."""

from __future__ import annotations

import tomllib
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def require(condition: bool, message: str) -> None:
    """Fail with a message that names the violated obligation."""
    if not condition:
        raise AssertionError(message)


def require_clean(errors: list[str], surface: str) -> None:
    """Fail listing every contract violation, not just that some exist."""
    require(
        not errors,
        f"{surface} violates the downstream-consumer contract "
        f"({len(errors)} violation(s)):\n  - " + "\n  - ".join(errors),
    )


def require_rejected(errors: list[str], expected: str, fixture: str) -> None:
    """Fail naming the perturbation the contract failed to notice."""
    require(
        any(expected in error for error in errors),
        f"negative fixture '{fixture}' was not rejected: no reported error "
        f"mentions '{expected}', so this contract clause no longer detects "
        f"the perturbation. Reported errors: "
        + (", ".join(f"'{error}'" for error in errors) if errors else "<none>"),
    )


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
        "explicit-hypothesis boundary": "leaves the analytic hypothesis explicit",
        "universal claim ceiling":
            "does not prove universal #257",
    }
    # Match on collapsed whitespace. These tokens are sentences, and a sentence
    # is the same sentence whichever column it wraps at; pinning the line break
    # made the contract fail on a reflow that changed nothing it cares about.
    flowed_readme = " ".join(readme.split())
    for label, token in readme_requirements.items():
        if " ".join(token.split()) not in flowed_readme:
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
    require_clean(
        contract_errors(example, readme, lakefile),
        "examples/Examples.lean, README.md, or lakefile.toml",
    )
    problem249 = (
        ROOT / "examples" / "ExternalVerificationPortfolio" / "Problem249.lean"
    ).read_text(encoding="utf-8")
    problem269 = (
        ROOT / "examples" / "ExternalVerificationPortfolio" / "Problem269.lean"
    ).read_text(encoding="utf-8")
    portfolio_readme = (
        ROOT / "examples" / "ExternalVerificationPortfolio" / "README.md"
    ).read_text(encoding="utf-8")
    require_clean(
        portfolio_contract_errors(problem249, problem269, portfolio_readme),
        "examples/ExternalVerificationPortfolio",
    )

    implicit_hypothesis = example.replace(
        "(hupper : (whole : ℝ) - (pfx : ℝ) ≤",
        "(upperBound : (whole : ℝ) - (pfx : ℝ) ≤",
        1,
    )
    require_rejected(
        contract_errors(implicit_hypothesis, readme, lakefile),
        "explicit analytic hypothesis",
        "example renames the named analytic hypothesis `hupper`",
    )

    weakened_conclusion = example.replace(
        "(2 : ℝ) ^ X ≤\n      ((whole.den * pfx.den : ℕ) : ℝ) * (K + 1)",
        "0 ≤ ((whole.den * pfx.den : ℕ) : ℝ) * (K + 1)",
        1,
    )
    require_rejected(
        contract_errors(weakened_conclusion, readme, lakefile),
        "exact shell-power conclusion",
        "example weakens the shell-power conclusion to `0 ≤ ...`",
    )

    lost_local_ceiling = example.replace(
        "this does not prove the universal\nErdős #257 statement",
        "this proves the universal\nErdős #257 statement",
        1,
    )
    require_rejected(
        contract_errors(lost_local_ceiling, readme, lakefile),
        "universal claim ceiling",
        "example doc-comment claims it proves universal Erdős #257",
    )

    overstated_readme = readme.replace(
        "does not prove universal #257",
        "proves universal #257",
        1,
    )
    require_rejected(
        contract_errors(example, overstated_readme, lakefile),
        "universal claim ceiling",
        "README claims the example proves universal #257",
    )

    renamed_target = lakefile.replace(
        'name = "Examples"',
        'name = "ConsumerExamples"',
        1,
    )
    require_rejected(
        contract_errors(example, readme, renamed_target),
        "exactly one Examples lean_lib",
        "lakefile renames the Examples lean_lib to ConsumerExamples",
    )

    displaced_source = lakefile.replace(
        'srcDir = "examples"',
        'srcDir = "consumer-examples"',
        1,
    )
    require_rejected(
        contract_errors(example, readme, displaced_source),
        "srcDir examples",
        "lakefile moves the Examples srcDir away from examples/",
    )

    default_example = lakefile.replace(
        'defaultTargets = ["Erdos249257", "ErdosProblems"]',
        'defaultTargets = ["Erdos249257", "ErdosProblems", "Examples"]',
        1,
    )
    require_rejected(
        contract_errors(example, readme, default_example),
        "defaultTargets",
        "lakefile promotes Examples into defaultTargets",
    )

    renamed_problem249_wrapper = problem249.replace(
        "irrational_totientSeries_of_actualLcmOrbitSeparationSupply",
        "irrational_totientSeries_of_unspecifiedSupply",
    )
    require_rejected(
        portfolio_contract_errors(
            renamed_problem249_wrapper, problem269, portfolio_readme
        ),
        "Problem249 exact wrapper",
        "Problem249 renames its separation-supply wrapper",
    )

    renamed_natural_prime_wrapper = problem249.replace(
        "irrational_totient_series_of_naturalPrimeTailOrbitStrictGap",
        "irrational_totient_series_of_unspecifiedGap",
    )
    require_rejected(
        portfolio_contract_errors(
            renamed_natural_prime_wrapper, problem269, portfolio_readme
        ),
        "Problem249 natural-prime wrapper",
        "Problem249 renames its natural-prime strict-gap wrapper",
    )

    hidden_problem269_boundary = problem269.replace(
        "actual-series/rationality bridge",
        "completed actual-series bridge",
        1,
    )
    require_rejected(
        portfolio_contract_errors(
            problem249, hidden_problem269_boundary, portfolio_readme
        ),
        "Problem269 actual-series boundary",
        "Problem269 hides the open actual-series/rationality bridge",
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
