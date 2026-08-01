#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check or refresh reasoning-paper Lean links against their pinned commit.

The declaration name is the authority.  For each named ``\\lean`` citation in
the authored #249/#257 reasoning parts, this tool resolves the declaration in
the cited file at the commit pinned by the papers' preambles and rewrites the
machine coordinate to its declaration line.  Module-level and deliberately
unnamed location citations are left authored, but their files and numeric
coordinates are still checked against the same commit.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
PARTS_DIRS = (
    ROOT / "paper" / "reasoning-parts" / "erdos249",
    ROOT / "paper" / "reasoning-parts" / "erdos257",
)
PIN_RE = re.compile(r"\\newcommand\{\\commit\}\{([0-9a-f]{40})\}")
LEAN_RE = re.compile(r"\\lean\{([^{}]*)\}\{([^{}]*)\}")
TARGET_RE = re.compile(r"(.+\.lean)(?::(.*))?")
DECL_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|local|scoped|unsafe|irreducible)"
    r"[ \t]+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|coinductive|"
    r"instance|axiom|constant|opaque)[ \t]+([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)


class CoordinateError(RuntimeError):
    """A source citation cannot be resolved uniquely at the pinned commit."""


@dataclass(frozen=True)
class PinnedSource:
    path: str
    text: str
    declarations: tuple[tuple[str, int], ...]


def normalize(value: str) -> str:
    """Remove TeX-only wrapping from a declaration name or machine target."""

    return re.sub(
        r"\s+",
        "",
        value.replace(r"\allowbreak", "").replace(r"\_", "_"),
    )


def strip_lean_comments(text: str) -> str:
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


def pinned_commit() -> str:
    pins: dict[Path, str] = {}
    for directory in PARTS_DIRS:
        preamble = directory / "preamble.tex"
        match = PIN_RE.search(preamble.read_text(encoding="utf-8"))
        if not match:
            raise CoordinateError(f"missing formal-source pin in {preamble.relative_to(ROOT)}")
        pins[preamble] = match.group(1)
    values = set(pins.values())
    if len(values) != 1:
        rendered = ", ".join(
            f"{path.relative_to(ROOT)}={pin}" for path, pin in pins.items()
        )
        raise CoordinateError(f"reasoning papers have different source pins: {rendered}")
    return values.pop()


class Resolver:
    def __init__(self, pin: str) -> None:
        self.pin = pin
        self.cache: dict[str, PinnedSource] = {}

    @staticmethod
    def repository_path(cited_file: str) -> str:
        if cited_file.startswith(("ErdosProblems/", "Erdos249257/")):
            return cited_file
        return f"Erdos249257/{cited_file}"

    def source(self, cited_file: str) -> PinnedSource:
        if cited_file in self.cache:
            return self.cache[cited_file]
        repository_path = self.repository_path(cited_file)
        command = ["git", "show", f"{self.pin}:{repository_path}"]
        result = subprocess.run(
            command,
            cwd=ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        if result.returncode:
            detail = result.stderr.strip() or "git show failed"
            raise CoordinateError(f"pinned source absent: {repository_path}: {detail}")
        stripped = strip_lean_comments(result.stdout)
        declarations = tuple(
            (match.group(1), stripped.count("\n", 0, match.start()) + 1)
            for match in DECL_RE.finditer(stripped)
        )
        source = PinnedSource(repository_path, result.stdout, declarations)
        self.cache[cited_file] = source
        return source

    def declaration_line(self, cited_file: str, cited_name: str) -> int:
        source = self.source(cited_file)
        terminal = cited_name.rsplit(".", 1)[-1]
        candidates = [
            (name, line) for name, line in source.declarations if name == cited_name
        ]
        if not candidates:
            candidates = [
                (name, line)
                for name, line in source.declarations
                if name == terminal
                or cited_name.endswith(f".{name}")
                or name.endswith(f".{cited_name}")
            ]
        candidates = sorted(set(candidates))
        if len(candidates) != 1:
            rendered = ", ".join(f"{name}:{line}" for name, line in candidates)
            reason = f"ambiguous ({rendered})" if candidates else "not found"
            raise CoordinateError(
                f"{cited_name} in {source.path} at {self.pin}: {reason}"
            )
        return candidates[0][1]

    def validate_location(self, cited_file: str, coordinates: str | None) -> None:
        source = self.source(cited_file)
        if coordinates is None:
            return
        line_count = source.text.count("\n") + (not source.text.endswith("\n"))
        for value in re.findall(r"\d+", coordinates):
            line = int(value)
            if line < 1 or line > line_count:
                raise CoordinateError(
                    f"location {cited_file}:{line} outside pinned file (1-{line_count})"
                )


def render_file(path: Path, resolver: Resolver) -> tuple[str, int, int]:
    text = path.read_text(encoding="utf-8")
    declarations = 0
    locations = 0

    def replace(match: re.Match[str]) -> str:
        nonlocal declarations, locations
        raw_name, raw_target = match.groups()
        name = normalize(raw_name)
        target = normalize(raw_target)
        target_match = TARGET_RE.fullmatch(target)
        if not target_match:
            line = text.count("\n", 0, match.start()) + 1
            raise CoordinateError(
                f"{path.relative_to(ROOT)}:{line}: malformed Lean target {raw_target!r}"
            )
        cited_file, coordinates = target_match.groups()
        if not name or ".lean" in name:
            resolver.validate_location(cited_file, coordinates)
            locations += 1
            return match.group(0)
        try:
            declaration_line = resolver.declaration_line(cited_file, name)
        except CoordinateError as exc:
            line = text.count("\n", 0, match.start()) + 1
            raise CoordinateError(f"{path.relative_to(ROOT)}:{line}: {exc}") from exc
        declarations += 1
        return f"\\lean{{{raw_name}}}{{{cited_file}:{declaration_line}}}"

    return LEAN_RE.sub(replace, text), declarations, locations


def render_all() -> tuple[dict[Path, str], int, int, str]:
    pin = pinned_commit()
    resolver = Resolver(pin)
    rendered: dict[Path, str] = {}
    declarations = 0
    locations = 0
    for directory in PARTS_DIRS:
        for path in sorted(directory.glob("*.tex")):
            updated, declaration_count, location_count = render_file(path, resolver)
            rendered[path] = updated
            declarations += declaration_count
            locations += location_count
    return rendered, declarations, locations, pin


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        rendered, declarations, locations, pin = render_all()
    except (CoordinateError, OSError) as exc:
        print(f"refresh_reasoning_source_coordinates: {exc}", file=sys.stderr)
        return 2

    stale = [
        path
        for path, updated in rendered.items()
        if path.read_text(encoding="utf-8") != updated
    ]
    if args.write:
        for path in stale:
            path.write_text(rendered[path], encoding="utf-8")
        print(
            f"refreshed {declarations} declaration coordinates against {pin}; "
            f"validated {locations} authored location links"
        )
        return 0
    if stale:
        print(
            "reasoning source coordinates are stale: "
            + ", ".join(str(path.relative_to(ROOT)) for path in stale),
            file=sys.stderr,
        )
        return 1
    print(
        f"reasoning source coordinates current at {pin}: "
        f"{declarations} declarations, {locations} authored locations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
