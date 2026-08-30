#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise atomic and symlink-safe generated contribution output writes."""

from __future__ import annotations

import tempfile
from pathlib import Path

import build_research_contributions as contributions


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    projection = contributions.build_projection([])
    json_payload = contributions.canonical(projection)
    markdown_payload = contributions.human_projection(projection)
    with tempfile.TemporaryDirectory(dir="/tmp") as directory:
        root = Path(directory)
        json_output = root / "contributions.json"
        markdown_output = root / "CONTRIBUTIONS.md"
        contributions.write_projection_outputs(
            json_payload,
            markdown_payload,
            json_output=json_output,
            markdown_output=markdown_output,
        )
        require(contributions.output_is_current(json_output, json_payload), "JSON output was not canonical")
        require(contributions.output_is_current(markdown_output, markdown_payload), "Markdown output was not canonical")

        link = root / "linked.json"
        link.symlink_to(json_output)
        try:
            contributions.write_projection_outputs(
                b"{}\n",
                markdown_payload,
                json_output=link,
                markdown_output=root / "other.md",
            )
        except ValueError as exc:
            require("symbolic link" in str(exc), "symlink output failure omitted its path-policy reason")
        else:
            raise AssertionError("generated JSON write followed a symlink")

        parent = root / "parent-link"
        parent.symlink_to(root, target_is_directory=True)
        try:
            contributions.write_projection_outputs(
                json_payload,
                markdown_payload,
                json_output=parent / "nested.json",
                markdown_output=root / "nested.md",
            )
        except ValueError as exc:
            require("symbolic link" in str(exc), "symlink parent failure omitted its path-policy reason")
        else:
            raise AssertionError("generated output followed a symlinked parent")

        with tempfile.TemporaryDirectory(dir="/tmp") as redirected:
            hidden_link = parent / ".." / "hidden.json"
            redirect = root / "redirect"
            redirect.symlink_to(redirected, target_is_directory=True)
            hidden_link = redirect / ".." / "hidden.json"
            require(
                contributions.has_symlink_component(hidden_link, root),
                "projection output normalized away a symlink before resolving ..",
            )
            try:
                contributions.write_projection_outputs(
                    json_payload,
                    markdown_payload,
                    json_output=hidden_link,
                    markdown_output=root / "hidden.md",
                )
            except ValueError as exc:
                require("symbolic link" in str(exc), "hidden symlink failure omitted its path-policy reason")
            else:
                raise AssertionError("generated output followed a hidden symlink")

    print("research contribution output safety: atomic pair publication and symlink rejection PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
