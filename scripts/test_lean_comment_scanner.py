#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Differential regression for chunked Lean-comment scanning.

The simple retired character scanner is an independent behavior oracle. This
checks nested/overlapping delimiters, escaped quotes, Unicode and malformed
input, including exact character positions required by source coordinates.
"""
import random
from refresh_reasoning_source_coordinates import CoordinateError, strip_lean_comments

def reference_strip(text: str) -> str:
    """Blank nested Lean comments without changing source line numbers."""

    output: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                output.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_string:
            char = text[index]
            output.append(char)
            if char == "\\" and index + 1 < len(text):
                output.append(text[index + 1])
                index += 2
            else:
                if char == '"':
                    in_string = False
                index += 1
        elif text.startswith("/-", index):
            depth = 1
            output.extend("  ")
            index += 2
        elif text.startswith("--", index):
            newline = text.find("\n", index)
            if newline < 0:
                output.extend(" " * (len(text) - index))
                break
            output.extend(" " * (newline - index))
            output.append("\n")
            index = newline + 1
        else:
            char = text[index]
            output.append(char)
            if char == '"':
                in_string = True
            index += 1
    if depth:
        raise CoordinateError("unterminated block comment in pinned Lean source")
    return "".join(output)

def result(fn, text):
    try:
        return ('ok', fn(text))
    except CoordinateError as exc:
        return ('error', str(exc))


def main():
    rng = random.Random(249)
    tokens = ['/-', '-/', '--', '"', '\\', '\n', 'abc', 'λ', '\\"', '\\\n', '/', '-']
    cases = ['', '/-', '/- --/ x', '"/- text -/"', '-- comment\n theorem a',
             '/- outer /- inner -/\n end -/theorem b', '"trailing\\']
    cases += [''.join(rng.choices(tokens, k=rng.randrange(100))) for _ in range(12000)]
    for text in cases:
        expected, actual = result(reference_strip, text), result(strip_lean_comments, text)
        if expected != actual:
            raise AssertionError((repr(text), expected, actual))
        if actual[0] == 'ok':
            if len(actual[1]) != len(text):
                raise AssertionError('source length changed')
            if [i for i,c in enumerate(actual[1]) if c == '\n'] != [i for i,c in enumerate(text) if c == '\n']:
                raise AssertionError('newline coordinates changed')
    print(f'Lean comment scanner: {len(cases)} differential and coordinate cases PASS')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
