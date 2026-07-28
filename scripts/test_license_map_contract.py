#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the software/manuscript licence split semantically explicit."""

from __future__ import annotations

import copy
import tomllib
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
APACHE = "Apache-2.0"
MANUSCRIPT_LICENSE = "CC-BY-4.0"
SPDX_LICENSE_HEADER = "SPDX-License-" "Identifier: "
MANUSCRIPT_BINARIES = {
    ".github/banner.png",
    "claim-faithful-publication-systems-paper.pdf",
    "cold-clone-to-proof-receipt.pdf",
    "erdos-243-reciprocal-tail-rigidity.pdf",
    "erdos-251-prime-gap-dyadic-series.pdf",
    "erdos-269-three-prime-running-lcm.pdf",
    "erdos-1049-rational-base-lambert.pdf",
    "erdos-249-binary-totient-series.pdf",
    "erdos-257-mersenne-support-subseries.pdf",
    "erdos249-257-main-paper.pdf",
}
MANUSCRIPT_SOURCES = {
    "paper/claim-faithful-publication-systems-paper.tex",
    "paper/cold-clone-to-proof-receipt.tex",
    "paper/erdos-243-reciprocal-tail-rigidity.tex",
    "paper/erdos-251-prime-gap-dyadic-series.tex",
    "paper/erdos-269-three-prime-running-lcm.tex",
    "paper/erdos-1049-rational-base-lambert.tex",
    "paper/erdos-249-binary-totient-series.tex",
    "paper/erdos-257-mersenne-support-subseries.tex",
    "paper/erdos249-257-main-paper.tex",
    "paper/module-aliases.tex",
}


def encode_reuse(config: dict[str, Any]) -> str:
    lines = [f"version = {config['version']}", ""]
    for annotation in config["annotations"]:
        lines.append("[[annotations]]")
        paths = annotation["path"]
        if isinstance(paths, str):
            lines.append(f'path = "{paths}"')
        else:
            quoted = ", ".join(f'"{path}"' for path in paths)
            lines.append(f"path = [{quoted}]")
        if "precedence" in annotation:
            lines.append(f'precedence = "{annotation["precedence"]}"')
        lines.append(
            f'SPDX-FileCopyrightText = "{annotation["SPDX-FileCopyrightText"]}"'
        )
        lines.append(
            f'SPDX-License-Identifier = "{annotation["SPDX-License-Identifier"]}"'
        )
        lines.append("")
    return "\n".join(lines)


def annotation_paths(annotation: dict[str, Any]) -> set[str]:
    paths = annotation.get("path")
    if isinstance(paths, str):
        return {paths}
    if isinstance(paths, list) and all(isinstance(path, str) for path in paths):
        return set(paths)
    return set()


def license_map_errors(
    reuse_text: str,
    readme: str,
    manuscript_sources: dict[str, str],
    license_files: set[str],
) -> list[str]:
    """Return semantic release-licensing failures."""
    errors: list[str] = []
    try:
        config = tomllib.loads(reuse_text)
    except tomllib.TOMLDecodeError:
        return ["REUSE.toml is not valid TOML"]

    annotations = config.get("annotations", [])
    blanket = [
        row
        for row in annotations
        if annotation_paths(row) == {"**"}
        and row.get("SPDX-License-Identifier") == APACHE
    ]
    if len(blanket) != 1:
        errors.append("REUSE.toml must contain one Apache-2.0 blanket annotation")

    manuscript_overrides = [
        row
        for row in annotations
        if row.get("precedence") == "override"
        and row.get("SPDX-License-Identifier") == MANUSCRIPT_LICENSE
    ]
    if len(manuscript_overrides) != 1:
        errors.append("REUSE.toml must contain one CC-BY-4.0 override")
    else:
        observed = annotation_paths(manuscript_overrides[0])
        if observed != MANUSCRIPT_BINARIES:
            errors.append(
                "REUSE.toml manuscript binary override must match the exact "
                "rendered-artifact set"
            )

    for path, source in manuscript_sources.items():
        if f"{SPDX_LICENSE_HEADER}{MANUSCRIPT_LICENSE}" not in source:
            errors.append(f"manuscript source {path} lost its CC-BY-4.0 header")
        if f"{SPDX_LICENSE_HEADER}{APACHE}" in source:
            errors.append(f"manuscript source {path} carries an Apache-2.0 header")

    for license_id in (APACHE, MANUSCRIPT_LICENSE):
        if f"LICENSES/{license_id}.txt" not in license_files:
            errors.append(f"licence text is missing for {license_id}")

    readme_boundary = (
        "Code, scripts, and documentation are Apache-2.0. The manuscript layer, "
        "including\nthe paper source and rendered PDFs, is CC-BY-4.0."
    )
    if readme_boundary not in readme:
        errors.append("README lost the exact software/manuscript licence boundary")
    return errors


def main() -> int:
    reuse = (ROOT / "REUSE.toml").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    sources = {
        path: (ROOT / path).read_text(encoding="utf-8")
        for path in MANUSCRIPT_SOURCES
    }
    license_files = {
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "LICENSES").glob("*.txt")
    }
    assert not license_map_errors(reuse, readme, sources, license_files)

    config = tomllib.loads(reuse)
    missing_override = copy.deepcopy(config)
    missing_override["annotations"] = missing_override["annotations"][:1]
    assert any(
        "CC-BY-4.0 override" in error
        for error in license_map_errors(
            encode_reuse(missing_override), readme, sources, license_files
        )
    )

    incomplete_override = copy.deepcopy(config)
    incomplete_override["annotations"][1]["path"] = sorted(
        MANUSCRIPT_BINARIES - {"erdos249-257-main-paper.pdf"}
    )
    assert any(
        "exact rendered-artifact set" in error
        for error in license_map_errors(
            encode_reuse(incomplete_override), readme, sources, license_files
        )
    )

    wrong_blanket = copy.deepcopy(config)
    wrong_blanket["annotations"][0]["SPDX-License-Identifier"] = MANUSCRIPT_LICENSE
    assert any(
        "Apache-2.0 blanket" in error
        for error in license_map_errors(
            encode_reuse(wrong_blanket), readme, sources, license_files
        )
    )

    lost_source_header = dict(sources)
    path = "paper/erdos249-257-main-paper.tex"
    lost_source_header[path] = lost_source_header[path].replace(
        f"{SPDX_LICENSE_HEADER}{MANUSCRIPT_LICENSE}",
        f"{SPDX_LICENSE_HEADER}{APACHE}",
        1,
    )
    assert any(
        path in error
        for error in license_map_errors(
            reuse, readme, lost_source_header, license_files
        )
    )

    missing_license_text = license_files - {f"LICENSES/{MANUSCRIPT_LICENSE}.txt"}
    assert any(
        f"missing for {MANUSCRIPT_LICENSE}" in error
        for error in license_map_errors(
            reuse, readme, sources, missing_license_text
        )
    )

    weakened_readme = readme.replace(
        "The manuscript layer, including\nthe paper source and rendered PDFs, "
        "is CC-BY-4.0.",
        "The manuscript layer follows the repository default.",
        1,
    )
    assert any(
        "licence boundary" in error
        for error in license_map_errors(
            reuse, weakened_readme, sources, license_files
        )
    )

    print(
        "test_license_map_contract: Apache software and CC-BY manuscript "
        "sources/rendered artifacts remain separated; "
        "6 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
