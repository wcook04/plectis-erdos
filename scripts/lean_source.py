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

# The two libraries whose sources are the proof corpus proper.  Everything
# else in the tree (Challenge fixtures, adapters, research corpus) is held to
# a different contract and is classified separately by each consumer.
LIBRARY_ROOTS = ("Erdos249257", "ErdosProblems")


def lean_code_without_comments_and_strings(text: str) -> str:
    """Remove nested Lean comments and strings while preserving newlines."""
    out: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                out.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_string:
            if text[index] == "\\" and index + 1 < len(text):
                out.extend("  ")
                index += 2
            elif text[index] == '"':
                in_string = False
                out.append(" ")
                index += 1
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                out.extend(" " * (len(text) - index))
                break
            out.extend(" " * (end - index))
            index = end
        elif text.startswith("/-", index):
            block_depth = 1
            out.extend("  ")
            index += 2
        elif text[index] == '"':
            in_string = True
            out.append(" ")
            index += 1
        else:
            out.append(text[index])
            index += 1
    return "".join(out)
