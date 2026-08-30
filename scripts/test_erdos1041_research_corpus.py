#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial privacy checks for the public Erdős #1041 corpus envelope."""

from __future__ import annotations

import check_erdos1041_research_corpus as checker


def require(condition: bool, message: str) -> None:
    """Keep privacy regressions active when Python is run with ``-O``."""
    if not condition:
        raise AssertionError(message)


def test_private_path_variants() -> None:
    fixtures = (
        b"/Users/example/private.txt",
        b"/users/example/private.txt",
        b"FILE:///Users/example/private.txt",
        b"file:///users/example/private.txt",
        b"C:\\Users\\example\\private.txt",
        b"c:\\users\\example\\private.txt",
        b"\\\\Users\\example\\private.txt",
        b"\\\\users\\example\\private.txt",
        b"~/.codex/private.txt",
        b"~/.CODEX/private.txt",
    )
    for fixture in fixtures:
        require(
            checker.private_path_leaks(fixture),
            f"private path variant escaped detection: {fixture!r}",
        )
    require(
        not checker.private_path_leaks(b"research_corpus/Erdos1041/public.txt"),
        "ordinary public corpus path was falsely classified as private",
    )


def test_live_corpus() -> None:
    file_count, result_count, total_bytes = checker.check()
    require(file_count > 0, "public corpus unexpectedly contains no files")
    require(result_count > 0, "public corpus unexpectedly contains no results")
    require(total_bytes > 0, "public corpus unexpectedly contains no bytes")


def main() -> int:
    test_private_path_variants()
    test_live_corpus()
    print(
        "test_erdos1041_research_corpus: case-insensitive private-path and "
        "live content-addressed corpus checks passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
