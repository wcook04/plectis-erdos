#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Lean source lexing shared by the release gate and the packet builder.

`check_release.py` and `build_external_verification.py` both need to decide
whether a `sorry` in a `.lean` file is an executable tactic or prose inside a
docstring asserting the absence of one.  Two copies of that judgement would
drift, and a drifted copy is exactly the defect this module was extracted to
prevent: the published `formalization.yaml` once reported one `sorry` while
the tree carried two.

Kept deliberately stdlib-only.  `check_release.py` pulls in `tomllib` through
`publication_contract`, which is not available on every interpreter the
builder is invoked with, so the builder must not import it merely to reach
this function.
"""

from __future__ import annotations

import re

# The two libraries whose sources are the proof corpus proper.  Everything
# else in the tree (Challenge fixtures, adapters, research corpus) is held to
# a different contract and is classified separately by each consumer.
LIBRARY_ROOTS = ("Erdos249257", "ErdosProblems")
NON_NEWLINE_RE = re.compile(r"[^\n]")


def _blank_non_newlines(text: str) -> str:
    """Blank one comment/string span in C-backed chunks, preserving lines."""

    return NON_NEWLINE_RE.sub(" ", text)


def lean_code_without_comments_and_strings(text: str) -> str:
    """Remove nested Lean comments and strings while preserving newlines."""
    out: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        if block_depth:
            nested = text.find("/-", index)
            closing = text.find("-/", index)
            boundaries = [position for position in (nested, closing) if position >= 0]
            if not boundaries:
                out.append(_blank_non_newlines(text[index:]))
                break
            boundary = min(boundaries)
            out.append(_blank_non_newlines(text[index:boundary]))
            if boundary == nested:
                block_depth += 1
                out.extend("  ")
            else:
                block_depth -= 1
                out.extend("  ")
            index = boundary + 2
        elif in_string:
            escape = text.find("\\", index)
            quote = text.find('"', index)
            boundaries = [position for position in (escape, quote) if position >= 0]
            if not boundaries:
                out.append(_blank_non_newlines(text[index:]))
                break
            boundary = min(boundaries)
            out.append(_blank_non_newlines(text[index:boundary]))
            if boundary == escape and boundary + 1 < len(text):
                out.extend("  ")
                index = boundary + 2
            elif boundary == quote:
                in_string = False
                out.append(" ")
                index = boundary + 1
            else:
                out.append(" ")
                break
        else:
            line_comment = text.find("--", index)
            block_comment = text.find("/-", index)
            quote = text.find('"', index)
            boundaries = [
                position
                for position in (line_comment, block_comment, quote)
                if position >= 0
            ]
            if not boundaries:
                out.append(text[index:])
                break
            boundary = min(boundaries)
            out.append(text[index:boundary])
            if boundary == line_comment:
                end = text.find("\n", boundary)
                if end < 0:
                    out.extend(" " * (len(text) - boundary))
                    break
                out.extend(" " * (end - boundary))
                index = end
            elif boundary == block_comment:
                block_depth = 1
                out.extend("  ")
                index = boundary + 2
            else:
                in_string = True
                out.append(" ")
                index = boundary + 1
    return "".join(out)
