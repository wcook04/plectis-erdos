#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Verify that every Erdős Problem Note source link names a real declaration.

The problem notes cover the expansion library ``ErdosProblems``, which is an
active research surface: later waves add theorems and move lines.  A note that
linked the working tree would therefore decay the moment the next wave landed.

Each note instead resolves its links against an immutable commit.  The corpus
default is declared in ``paper/problem-note-preamble.tex``; a note may override
that pin with ``\\renewcommand{\\commit}{...}`` when one problem advances on a
disjoint source branch.  This program reads each selected snapshot out of Git
-- never the working tree -- and requires that every authored ``(file, line,
declaration)`` triple names exactly that declaration at exactly that line in the
pinned snapshot.  A link can then be wrong only if it was wrong when written.
Every printed source URL, including a late link through ``\\laterepobase`` at a
manuscript's own ``\\latecommit``, must also name a path present at its pin.

Run from the repository root:

    python3 scripts/check_problem_note_sources.py --coverage

``--list`` prints the resolved link inventory instead of only a verdict.
``--coverage`` additionally requires module-qualified links to the configured
headline declarations and gates the fraction of current declarations reached.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import stat
import subprocess
import sys
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable

import validation_singleflight as singleflight
from lean_source import (
    LIBRARY_ROOTS,
    library_identity_path,
    library_storage_path,
    library_storage_variants,
)

ROOT = Path(__file__).resolve().parent.parent
PREAMBLE = ROOT / "paper" / "problem-note-preamble.tex"
CONTRACT = ROOT / "docs" / "publication_contract.json"
INDEX_SOURCE = ROOT / "docs" / "problem_index_source.json"
NOTE_ARTIFACT_CLASS = "problem_note"
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
LIBRARY_PREFIX = "ErdosProblems"
# A note may also cite the reviewed #249/#257 corpus directly.  The expansion
# library is where problem-owned work lands, but the headline theorems for
# several problems live in the older reviewed library, and a note that could
# not name them would have to paraphrase a checked statement instead of
# linking it.  A link is read as library-qualified when its first path
# segment names a sibling library; otherwise it stays relative to
# ``ErdosProblems``, which is what every existing note writes.
SIBLING_LIBRARIES = ("Erdos249257",)

LEDGER_ARTIFACT_CLASSES = (NOTE_ARTIFACT_CLASS, "mathematical_companion")
COMMIT_RE = re.compile(r"\\newcommand\{\\commit\}\{([0-9a-f]{40})\}")
LEDGER_COMMIT_RE = re.compile(r"\\newcommand\{\\ledgercommit\}\{([0-9a-f]{40})\}")
NOTE_LEDGER_COMMIT_RE = re.compile(r"\\renewcommand\{\\ledgercommit\}\{([0-9a-f]{40})\}")
# The generated statement note.  Its file is named below lean/ and resolves at
# \ledgercommit, which is the revision the coverage ledger read its declarations
# from; a note-wide \commit predates the nested layout and does not carry them.
LPROOF_RE = re.compile(
    r"\\lproof\{(?P<file>[^{}]+)\}\{(?P<line>\d+)\}\{(?P<decl>[^{}]+)\}"
)
NOTE_COMMIT_RE = re.compile(
    r"\\renewcommand\{\\commit\}\{([0-9a-f]{40})\}"
)
COMMIT_SHORT_RE = re.compile(
    r"\\newcommand\{\\commitshort\}\{([0-9a-f]{12})\}"
)
NOTE_COMMIT_SHORT_RE = re.compile(
    r"\\renewcommand\{\\commitshort\}\{([0-9a-f]{12})\}"
)


class UnsafeSourceInput(ValueError):
    """A note-source input escaped the checkout or is not a regular file."""


def safe_worktree_path(path: Path) -> Path:
    """Resolve only regular files without symlinked checkout components."""
    root = Path(os.path.abspath(ROOT))
    candidate = Path(os.path.abspath(path))
    if candidate != root and root not in candidate.parents:
        raise UnsafeSourceInput(f"source input escaped checkout: {candidate}")
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeSourceInput(
                f"source input traverses a symbolic link: {candidate}"
            )
        if current == root:
            break
        if current.parent == current:
            raise UnsafeSourceInput(f"source input escaped checkout: {candidate}")
        current = current.parent
    if not candidate.is_file():
        raise UnsafeSourceInput(
            f"source input is not a regular file: {candidate}"
        )
    return candidate


def safe_worktree_text(path: Path) -> str:
    """Read one worktree source through a no-follow descriptor."""
    candidate = safe_worktree_path(path)
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeSourceInput(
            f"source input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeSourceInput(
                f"source input is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        try:
            return b"".join(chunks).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise UnsafeSourceInput(
                f"source input is not UTF-8: {candidate}"
            ) from exc
    finally:
        os.close(descriptor)
COMMENT_RE = re.compile(r"(?<!\\)%.*$")
LINK_RE = re.compile(
    r"""\\[lm]word\{(?P<word_file>[^{}]+)\}\{(?P<word_line>\d+)\}
            \{(?P<word_decl>[^{}]+)\}\{
        |\\(?:lref|lrefx|mref)\{(?P<ref_file>[^{}]+)\}\{(?P<ref_line>\d+)\}
            \{(?P<ref_decl>[^{}]+)\}
        |\\[lm]loc\{(?P<loc_file>[^{}]+)\}\{(?P<loc_line>\d+)\}""",
    re.X,
)
# A Lean declaration head: the keyword, optional modifiers, then the name.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "instance",
    "example",
)


@lru_cache(maxsize=256)
def strip_comments(text: str) -> str:
    return "\n".join(COMMENT_RE.sub("", line) for line in text.splitlines())


def strip_lean_comments(text: str) -> str:
    """Remove nested Lean comments while preserving source line boundaries."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                output.extend((" ", " "))
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                output.extend((" ", " "))
                index += 2
            else:
                character = text[index]
                output.append("\n" if character == "\n" else " ")
                index += 1
            continue

        character = text[index]
        if in_string:
            output.append(character)
            index += 1
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            continue

        if text.startswith("/-", index):
            block_depth = 1
            output.extend((" ", " "))
            index += 2
        elif text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
        else:
            output.append(character)
            index += 1
            if character == '"':
                in_string = True
    return "".join(output)


def note_sources() -> list[str]:
    """Return the registered problem-note manuscript paths, in contract order."""
    contract = json.loads(safe_worktree_text(CONTRACT))
    return [
        row["source_path"]
        for row in contract.get("artifacts", [])
        if row.get("artifact_class") == NOTE_ARTIFACT_CLASS
    ]


def pinned_commit() -> str:
    match = COMMIT_RE.search(safe_worktree_text(PREAMBLE))
    if match is None:
        raise SystemExit(
            f"{PREAMBLE.relative_to(ROOT)}: no pinned \\commit is declared"
        )
    return match.group(1)


def ledger_commit() -> str | None:
    """The corpus-wide pin the generated statement notes resolve at."""
    match = LEDGER_COMMIT_RE.search(safe_worktree_text(PREAMBLE))
    return None if match is None else match.group(1)


def ledger_sources() -> list[str]:
    """Every registered manuscript that may carry generated statement notes."""
    contract = json.loads(safe_worktree_text(CONTRACT))
    return [
        row["source_path"]
        for row in contract.get("artifacts", [])
        if row.get("artifact_class") in LEDGER_ARTIFACT_CLASSES
    ]


def generated_links(text: str) -> list[tuple[str, int, str]]:
    return [
        (match.group("file"), int(match.group("line")), match.group("decl"))
        for match in LPROOF_RE.finditer(strip_comments(text))
    ]


def generated_note_failures(default_ledger: str | None) -> tuple[list[str], int]:
    """Resolve every generated statement link against its own immutable pin.

    These links are written by the coverage ledger's generator rather than by
    hand, and they name a revision that postdates the notes' own ``\\commit``.
    Checking them here keeps one verifier for every printed source coordinate,
    whichever pin it resolves at.
    """
    failures: list[str] = []
    checked = 0
    cache: dict[tuple[str, str], list[str]] = {}
    requests: list[tuple[str, str, list[tuple[str, int, str]]]] = []
    for source in ledger_sources():
        try:
            text = safe_worktree_text(ROOT / source)
        except UnsafeSourceInput as error:
            failures.append(f"{source}: {error}")
            continue
        found = generated_links(text)
        if not found:
            continue
        override = NOTE_LEDGER_COMMIT_RE.search(strip_comments(text))
        commit = override.group(1) if override else default_ledger
        if commit is None:
            failures.append(
                f"{source}: generated statement links without a \\ledgercommit pin"
            )
            continue
        requests.append((source, commit, found))
    snapshot_lines_batch(
        {(commit, library_relative(name))
         for _source, commit, found in requests
         for name, _line, _declaration in found},
        cache,
    )
    for source, commit, found in requests:
        if git_run("cat-file", "-e", f"{commit}^{{commit}}").returncode != 0:
            failures.append(f"{source}: ledger commit is absent: {commit}")
            continue
        for file_name, line_number, declaration in found:
            checked += 1
            relative = library_relative(file_name)
            lines = snapshot_lines(commit, relative, cache)
            if not lines:
                failures.append(
                    f"{source}: {relative} is absent from the ledger snapshot"
                )
                continue
            if not 1 <= line_number <= len(lines):
                failures.append(
                    f"{source}: {relative}:{line_number} is outside the ledger "
                    f"snapshot ({len(lines)} lines)"
                )
                continue
            if not declares_at(lines, line_number - 1, declaration):
                failures.append(
                    f"{source}: {relative}:{line_number} does not declare "
                    f"{declaration!r} at {commit[:12]}; the pinned line reads "
                    f"{lines[line_number - 1].strip()[:72]!r}"
                )
    return failures, checked


# A printed link is checked exactly as its macro renders it.  The declaration
# checks read a snapshot through every storage spelling of a file, which is right
# for finding the declaration and wrong for the URL: on 22 Sep 2026 the #243 notes
# pinned a commit that keeps the Lean roots under lean/, \lword printed the root
# spelling, and 110 links answered 404 while every declaration check passed.
PX_RE = re.compile(r"\\newcommand\{\\PX\}\{([^{}]+)\}")
NOTE_PX_RE = re.compile(r"\\renewcommand\{\\PX\}\{([^{}]+)\}")
NOTE_PK_RE = re.compile(r"\\(?:re)?newcommand\{\\PK\}\{([^{}]+)\}")
NOTE_REPOBASE_RE = re.compile(r"\\renewcommand\{\\repobase\}\{([^{}]+)\}")
STANDARD_REPOBASE = r"https://github.com/wcook04/plectis-erdos/blob/\commit"
RENDERED_MACRO_RE = re.compile(
    r"\\(?P<macro>lword|lrefx|lref|lloc|mword|mref|mloc|lproof)"
    r"\{(?P<file>[^{}]+)\}\{[0-9]+\}"
)
PINNED_BASE_RE = re.compile(r"\\(?:repobase|sourceurl)/(?P<path>[^\s{}#\\]+)")
LITERAL_SOURCE_RE = re.compile(
    r"https://github\.com/wcook04/plectis-erdos/(?:blob|tree)/"
    r"(?P<commit>[0-9a-f]{40})/(?P<path>[^\s{}#\\]+)"
)
# A source that postdates \commit is printed through \laterepobase, which a
# manuscript builds on its own \latecommit.  The #249/#257 records also print a
# \lean target written with its lean/ prefix at that pin (their \leanlink macro).
LATE_COMMIT_RE = re.compile(r"\\(?:re)?newcommand\{\\latecommit\}\{([0-9a-f]{40})\}")
LATE_REPOBASE_RE = re.compile(r"\\(?:re)?newcommand\{\\laterepobase\}\{([^{}]+)\}")
STANDARD_LATE_REPOBASE = r"https://github.com/wcook04/plectis-erdos/blob/\latecommit"
LATE_BASE_RE = re.compile(r"\\laterepobase/(?P<path>[^\s{}#\\]+)")
LATE_LEAN_RE = re.compile(r"\\lean\{[^{}]*\}\{(?P<target>[^{}]*)\}")


def late_lean_path(target: str) -> str | None:
    """The file a \\lean target prints at \\latecommit, or None for an older source.

    The macro strips \\allowbreak and spaces, sends a lean/ target to
    \\laterepobase, and links the file part before any :line coordinate.
    """
    flat = re.sub(r"\s+", "", target.replace(r"\allowbreak", ""))
    if not flat.startswith("lean/"):
        return None
    match = re.match(r"(.*\.lean)", flat)
    return match.group(1) if match else None


CONDITIONAL_RE = re.compile(r"\\(?:if[A-Za-z@]*|fi)(?![A-Za-z@])")


def strip_unrendered(text: str) -> str:
    """Drop ``\\iffalse ... \\fi`` blocks, which TeX reads and never prints.

    Several notes keep their exhaustive source manifest inside one, for the
    declaration checks above; nothing in it reaches the PDF, so it prints no URL.
    """
    kept: list[str] = []
    position = 0
    for opener in re.finditer(r"\\iffalse(?![A-Za-z@])", text):
        if opener.start() < position:
            continue
        kept.append(text[position : opener.start()])
        depth = 0
        position = len(text)  # an unclosed block runs to the end, as in TeX
        for token in CONDITIONAL_RE.finditer(text, opener.start()):
            depth += -1 if token.group(0) == "\\fi" else 1
            if depth == 0:
                position = token.end()
                break
    kept.append(text[position:])
    return "".join(kept)


def rendered_link_targets(
    text: str,
    default_commit: str,
    default_ledger: str | None,
    default_px: str,
) -> tuple[list[tuple[str, str]], list[str]]:
    """Every (commit, repository path) one manuscript prints as a source URL."""
    text = strip_unrendered(strip_comments(text))
    targets: list[tuple[str, str]] = []
    problems: list[str] = []
    override = NOTE_REPOBASE_RE.search(text)
    if override is not None and override.group(1) != STANDARD_REPOBASE:
        return [], [f"\\repobase is redefined as {override.group(1)!r}, which this check cannot render"]
    commit = note_pinned_commit(text, default_commit)
    ledger_override = NOTE_LEDGER_COMMIT_RE.search(text)
    ledger = ledger_override.group(1) if ledger_override else default_ledger
    px_override = NOTE_PX_RE.search(text)
    px = px_override.group(1) if px_override else default_px
    pk = NOTE_PK_RE.search(text)
    for match in RENDERED_MACRO_RE.finditer(text):
        macro, name = match.group("macro"), match.group("file")
        if macro in ("lword", "lref", "lloc"):
            targets.append((commit, f"{px}/{name}"))
        elif macro in ("mword", "mref", "mloc"):
            targets.append((commit, name))
        elif macro == "lproof":
            # generated_note_failures() already reports a missing ledger pin.
            if ledger is not None:
                targets.append((ledger, f"lean/{name}"))
        elif pk is not None:
            targets.append((commit, f"{pk.group(1)}/{name}"))
        else:
            problems.append(f"\\lrefx{{{name}}} is used without a \\PK prefix")
    targets.extend((commit, match.group("path")) for match in PINNED_BASE_RE.finditer(text))
    targets.extend(
        (match.group("commit"), match.group("path"))
        for match in LITERAL_SOURCE_RE.finditer(text)
    )
    late_paths = [match.group("path") for match in LATE_BASE_RE.finditer(text)]
    late_paths.extend(
        path
        for path in (late_lean_path(match.group("target")) for match in LATE_LEAN_RE.finditer(text))
        if path is not None
    )
    if late_paths:
        late = LATE_COMMIT_RE.search(text)
        late_base = LATE_REPOBASE_RE.search(text)
        if late is None:
            problems.append("a late source link is printed but no \\latecommit pin is declared")
        elif late_base is None or late_base.group(1) != STANDARD_LATE_REPOBASE:
            rendered = late_base.group(1) if late_base else None
            problems.append(
                f"\\laterepobase is defined as {rendered!r}, which this check cannot render"
            )
        else:
            targets.extend((late.group(1), path) for path in late_paths)
    return targets, problems


def objects_present(keys: Iterable[tuple[str, str]]) -> set[tuple[str, str]]:
    """The (commit, path) pairs that name an object, read in one Git process."""
    ordered = sorted(set(keys))
    if not ordered:
        return set()
    completed = subprocess.run(
        ["git", "cat-file", "--batch-check"],
        cwd=ROOT,
        input="".join(f"{commit}:{path}\n" for commit, path in ordered).encode(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )
    answers = completed.stdout.decode("utf-8", "replace").splitlines()
    if completed.returncode != 0 or len(answers) != len(ordered):
        raise SystemExit(
            "check_problem_note_sources: git cat-file --batch-check failed: "
            + completed.stderr.decode("utf-8", "replace").strip()[:200]
        )
    return {
        key
        for key, answer in zip(ordered, answers)
        if not answer.endswith((" missing", " ambiguous"))
    }


def rendered_link_failures(
    default_commit: str, default_ledger: str | None
) -> tuple[list[str], int]:
    """Require every printed plectis-erdos source URL to exist as printed."""
    failures: list[str] = []
    preamble = safe_worktree_text(PREAMBLE)
    px_match = PX_RE.search(strip_comments(preamble))
    default_px = px_match.group(1) if px_match else LIBRARY_PREFIX
    wanted: dict[tuple[str, str], set[str]] = {}
    preamble_name = str(PREAMBLE.relative_to(ROOT))
    for match in LITERAL_SOURCE_RE.finditer(strip_comments(preamble)):
        wanted.setdefault((match.group("commit"), match.group("path")), set()).add(preamble_name)
    for source in ledger_sources():
        try:
            text = safe_worktree_text(ROOT / source)
        except UnsafeSourceInput as error:
            failures.append(f"{source}: {error}")
            continue
        targets, problems = rendered_link_targets(
            text, default_commit, default_ledger, default_px
        )
        failures.extend(f"{source}: {problem}" for problem in problems)
        for key in targets:
            wanted.setdefault(key, set()).add(source)
    present = objects_present(wanted)
    missing: dict[tuple[str, str], list[str]] = {}
    for (commit, path), sources in sorted(wanted.items()):
        if (commit, path) not in present:
            for source in sorted(sources):
                missing.setdefault((source, commit), []).append(path)
    relocated = objects_present(
        (commit, f"lean/{path}")
        for (_source, commit), paths in missing.items()
        for path in paths
    )
    for (source, commit), paths in sorted(missing.items()):
        hint = ""
        if all((commit, f"lean/{path}") in relocated for path in paths):
            hint = "; every one exists under lean/ at that commit, so the note's \\PX is wrong"
        failures.append(
            f"{source}: {len(paths)} printed source link(s) name a path absent at "
            f"{commit[:12]} and would answer 404, e.g. {paths[0]}{hint}"
        )
    return failures, len(wanted)


def pinned_commitshort() -> str:
    match = COMMIT_SHORT_RE.search(safe_worktree_text(PREAMBLE))
    if match is None:
        raise SystemExit(
            f"{PREAMBLE.relative_to(ROOT)}: no pinned \\commitshort is declared"
        )
    return match.group(1)


def note_pinned_commit(note_text: str, default_commit: str) -> str:
    """Return a note-local source pin, falling back to the corpus default."""
    match = NOTE_COMMIT_RE.search(strip_comments(note_text))
    return default_commit if match is None else match.group(1)


def note_pinned_commitshort(note_text: str, default_commitshort: str) -> str:
    """Return a note-local display pin, falling back to the corpus default."""
    match = NOTE_COMMIT_SHORT_RE.search(strip_comments(note_text))
    return default_commitshort if match is None else match.group(1)


def source_pin_failure(
    source: str,
    note_text: str,
    default_commit: str,
    default_commitshort: str,
) -> str | None:
    """Reject a displayed short pin that does not name the effective commit."""
    commit = note_pinned_commit(note_text, default_commit)
    commitshort = note_pinned_commitshort(note_text, default_commitshort)
    expected = commit[:12]
    if commitshort == expected:
        return None
    return (
        f"{source}: displayed \\commitshort {commitshort} does not match "
        f"the effective \\commit prefix {expected}"
    )


def git_run(*args: str) -> subprocess.CompletedProcess[str]:
    """Read committed note sources without ambient Git selectors or hangs."""
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )


def snapshot_blob_candidates(relative: str) -> tuple[str, ...]:
    """Identity path first, then nested ``lean/`` storage, then any alias.

    Problem notes pin some snapshots before the nested-layout move and some
    after it.  The cache key stays the identity path used in diagnostics;
    Git is asked for every on-disk spelling that can hold that blob.
    """
    ordered: list[str] = []
    seen: set[str] = set()
    identity = library_identity_path(relative)
    for path in (relative, identity, *library_storage_variants(relative)):
        if path and path not in seen:
            seen.add(path)
            ordered.append(path)
    return tuple(ordered)


def snapshot_lines(
    commit: str,
    relative: str,
    cache: dict[tuple[str, str], list[str]],
) -> list[str]:
    key = (commit, relative)
    if key in cache:
        return cache[key]
    for candidate in snapshot_blob_candidates(relative):
        completed = git_run("show", f"{commit}:{candidate}")
        if completed.returncode == 0:
            cache[key] = completed.stdout.splitlines()
            return cache[key]
    cache[key] = []
    return cache[key]


def _parse_cat_file_batch(
    queries: list[tuple[str, str]], output: bytes
) -> dict[tuple[str, str], list[str]]:
    """Decode one ``git cat-file --batch`` body into per-query line lists."""
    blobs: dict[tuple[str, str], list[str]] = {}
    position = 0
    for key in queries:
        header_end = output.find(b"\n", position)
        if header_end < 0:
            blobs[key] = []
            continue
        header = output[position:header_end]
        position = header_end + 1
        if header.endswith(b" missing"):
            blobs[key] = []
            continue
        fields = header.rsplit(b" ", 2)
        if len(fields) != 3 or fields[1] != b"blob":
            blobs[key] = []
            continue
        try:
            size = int(fields[2])
        except ValueError:
            blobs[key] = []
            continue
        end = position + size
        if end > len(output):
            blobs[key] = []
            position = len(output)
            continue
        blobs[key] = output[position:end].decode("utf-8").splitlines()
        position = end + 1
    return blobs


def snapshot_lines_batch(
    requests: Iterable[tuple[str, str]],
    cache: dict[tuple[str, str], list[str]],
) -> None:
    """Fill snapshot lines with one Git process for many immutable blobs."""
    missing = sorted(set(requests) - set(cache))
    if not missing:
        return
    queries: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for commit, relative in missing:
        for candidate in snapshot_blob_candidates(relative):
            git_key = (commit, candidate)
            if git_key not in seen:
                seen.add(git_key)
                queries.append(git_key)
    completed = subprocess.run(
        ["git", "cat-file", "--batch"],
        cwd=ROOT,
        input="".join(f"{commit}:{path}\n" for commit, path in queries).encode(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )
    if completed.returncode != 0:
        for key in missing:
            cache[key] = []
        return

    blobs = _parse_cat_file_batch(queries, completed.stdout)
    for commit, relative in missing:
        lines: list[str] = []
        for candidate in snapshot_blob_candidates(relative):
            hit = blobs.get((commit, candidate), [])
            if hit:
                lines = hit
                break
        cache[(commit, relative)] = lines


def library_relative(file_name: str) -> str:
    """Repository path for a link target named in a note.

    Unqualified names stay relative to the expansion library; a name whose
    first segment is already a corpus root (or a sibling library) is the
    identity path and must not be prefixed again.
    """
    head = file_name.split("/", 1)[0]
    if head in LIBRARY_ROOTS or head in SIBLING_LIBRARIES:
        return file_name
    return f"{LIBRARY_PREFIX}/{file_name}"


EVIDENCE_MAP = ROOT / "evidence" / "paper_evidence.json"


def margin_mark_declaration_keys(note_source: str, evidence: dict[str, Any]) -> set[DeclarationKey]:
    """Declarations a note reaches through its margin marks.

    A result with a whole-result Lean proof carries a margin mark that links its
    declaration, or the section of the evidence record listing every declaration
    that states it, at the Lean pin.  Each such declaration is reached by the
    note, under the name its module declares it by (any dotted suffix of the full
    name).
    """
    paper_id = Path(note_source).stem
    keys: set[DeclarationKey] = set()
    for paper in evidence.get("papers", []):
        if paper.get("paper_id") != paper_id:
            continue
        for result in paper.get("results", []):
            lean = result.get("lean") or {}
            if not lean.get("mark"):
                continue
            for declaration in lean.get("declarations", []):
                relative = library_relative(declaration["path"].removeprefix("lean/"))
                parts = declaration["name"].split(".")
                keys.update((relative, ".".join(parts[i:])) for i in range(len(parts)))
    return keys


def module_relative(module_name: str) -> str:
    """Repository path for a dotted Lean module name."""
    return "/".join(module_name.split(".")) + ".lean"


ATTRIBUTE_RE = re.compile(r"^\s*@\[[^\]]*\]\s*")


def declares(line: str, name: str) -> bool:
    """True when this source line is the declaration head for ``name``."""
    # A declaration head may carry attributes, as in `@[simp] theorem foo`.
    stripped = ATTRIBUTE_RE.sub("", line).strip()
    for keyword in DECL_KEYWORDS:
        for prefix in ("", "private ", "protected ", "noncomputable ", "nonrec "):
            head = f"{prefix}{keyword} "
            if stripped.startswith(head):
                rest = stripped[len(head) :].lstrip()
                if re.match(rf"{re.escape(name)}(?![A-Za-z0-9_'])", rest):
                    return True
    # Lean also permits the declaration keyword and name on consecutive
    # lines. Authored links point at the name line in that layout.
    if re.match(rf"{re.escape(name)}(?![A-Za-z0-9_'])\s*:", stripped):
        return True
    return False


def declares_at(lines: list[str], index: int, name: str) -> bool:
    """Accept a declaration whose keyword and name span adjacent lines."""
    return declares(" ".join(line.strip() for line in lines[index : index + 4]), name)


def links(text: str) -> list[tuple[str, int, str | None]]:
    found: list[tuple[str, int, str | None]] = []
    for match in LINK_RE.finditer(strip_comments(text)):
        if match.group("word_file"):
            found.append(
                (match.group("word_file"), int(match.group("word_line")), match.group("word_decl"))
            )
        elif match.group("ref_file"):
            found.append(
                (match.group("ref_file"), int(match.group("ref_line")), match.group("ref_decl"))
            )
        else:
            found.append((match.group("loc_file"), int(match.group("loc_line")), None))
    return found


def note_for_problem() -> list[tuple[dict, str]]:
    """Pair each indexed problem with its registered note source path."""
    index = json.loads(safe_worktree_text(INDEX_SOURCE))
    contract = json.loads(safe_worktree_text(CONTRACT))
    by_id = {row["id"]: row for row in contract.get("artifacts", [])}
    pairs = []
    for row in index["problems"]:
        artifact = by_id.get(row["note_artifact_id"])
        if artifact is not None:
            pairs.append((row, artifact["source_path"]))
    return pairs


def declarations_in(text: str) -> list[str]:
    """Every declaration name a Lean source declares, in file order."""
    names: list[str] = []
    for line in strip_lean_comments(text).splitlines():
        stripped = ATTRIBUTE_RE.sub("", line).strip()
        for keyword in DECL_KEYWORDS:
            for prefix in ("", "private ", "protected ", "noncomputable ", "nonrec "):
                head = f"{prefix}{keyword} "
                if stripped.startswith(head):
                    match = re.match(
                        r"([A-Za-z_][A-Za-z0-9_'.]*)", stripped[len(head) :].lstrip()
                    )
                    if match:
                        names.append(match.group(1))
                    break
            else:
                continue
            break
    return names


DeclarationKey = tuple[str, str]


def linked_declaration_keys(note_text: str) -> set[DeclarationKey]:
    """Module-qualified declarations linked by one problem note."""
    linked = {
        (library_relative(file_name), declaration)
        for file_name, _line, declaration in links(note_text)
        if declaration is not None
    }
    # Generated statement notes reach the same declarations, at their own pin;
    # generated_note_failures() has already resolved each one in that snapshot.
    linked.update(
        (library_relative(file_name), declaration)
        for file_name, _line, declaration in generated_links(note_text)
    )
    # A local result may use its own immutable source pin without changing the
    # note-wide pin. Count it only after checking the named declaration there.
    explicit = re.compile(
        r"\\href\{https://github\.com/wcook04/plectis-erdos/blob/"
        r"(?P<commit>[0-9a-f]{40})/"
        r"(?P<path>(?:lean/)?(?:ErdosProblems|Erdos249257)/[A-Za-z0-9_/.-]+\.lean)"
        r"\\?#L(?P<line>[1-9][0-9]*)\}\{\\texttt\{(?P<name>[^{}]+)\}\}"
    )
    cache: dict[tuple[str, str], list[str]] = {}
    for match in explicit.finditer(strip_comments(note_text)):
        relative = library_relative(match.group("path").removeprefix("lean/"))
        declaration = match.group("name").replace(r"\_", "_")
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", declaration):
            continue
        raw = snapshot_lines(match.group("commit"), relative, cache)
        source = strip_lean_comments("\n".join(raw)).splitlines()
        index = int(match.group("line")) - 1
        if 0 <= index < len(source) and declares_at(source, index, declaration):
            linked.add((relative, declaration))
    return linked


def declarations_for_module(relative: str, text: str) -> list[DeclarationKey]:
    """Module-qualified declarations parsed from one live Lean source."""
    return [(relative, name) for name in declarations_in(text)]


def validated_coverage_floor(
    owner: dict[str, Any], *, label: str = "note_coverage_floor"
) -> tuple[float | None, list[str]]:
    """Return a finite coverage floor in `(0, 1]`, or a validation failure."""
    value = owner.get("note_coverage_floor")
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(float(value))
        or not 0 < float(value) <= 1
    ):
        return None, [
            f"{label} must be a finite number in the interval (0, 1]"
        ]
    return float(value), []


def required_note_declaration_failures(
    row: dict[str, Any],
    current: set[DeclarationKey],
    linked: set[DeclarationKey],
) -> list[str]:
    """Validate and enforce the problem's module-qualified headline anchors."""
    failures: list[str] = []
    raw_anchors = row.get("required_note_declarations")
    if not isinstance(raw_anchors, list) or not raw_anchors:
        return [
            f"{row['problem_id']}: required_note_declarations must be a nonempty list"
        ]

    allowed_modules = {
        module_relative(module)
        for module in [row["principal_module"], *row.get("companion_modules", [])]
    }
    seen: set[DeclarationKey] = set()
    for anchor in raw_anchors:
        if not isinstance(anchor, dict):
            failures.append(
                f"{row['problem_id']}: required note declaration must be an object"
            )
            continue
        module = anchor.get("module")
        declaration = anchor.get("declaration")
        if not isinstance(module, str) or not module:
            failures.append(
                f"{row['problem_id']}: required note declaration has invalid module"
            )
            continue
        if not isinstance(declaration, str) or not declaration:
            failures.append(
                f"{row['problem_id']}: required note declaration has invalid declaration"
            )
            continue
        key = (module_relative(module), declaration)
        current_module = anchor.get("current_module", module)
        if not isinstance(current_module, str) or not current_module:
            failures.append(f"{row['problem_id']}: required note declaration has invalid current module")
            continue
        current_key = (module_relative(current_module), declaration)
        if key in seen:
            failures.append(
                f"{row['problem_id']}: duplicate required note declaration "
                f"{key[0]}::{key[1]}"
            )
            continue
        seen.add(key)
        if current_key[0] not in allowed_modules:
            failures.append(
                f"{row['problem_id']}: required note declaration module "
                f"{current_key[0]} is outside the indexed problem modules"
            )
        elif current_key not in current:
            failures.append(
                f"{row['problem_id']}: required note declaration "
                f"{current_key[0]}::{key[1]} is absent from current source"
            )
        elif key not in linked:
            failures.append(
                f"{row['problem_id']}: note does not link required headline "
                f"declaration {key[0]}::{key[1]}"
            )
    return failures


def coverage_report(default_commit: str) -> tuple[list[str], list[str]]:
    """Report how much of each problem's current source its note reaches.

    A note pins its links to one commit, so it cannot break when the library
    moves.  The cost of that safety is that it can fall silently behind.  This
    measures the gap in the only terms that matter to a reader: whether every
    configured headline declaration is linked, how many declarations that
    exist *now* the note mentions, and whether the modules have changed at all
    since the note was pinned.
    """
    lines: list[str] = []
    failures: list[str] = []
    index = json.loads(safe_worktree_text(INDEX_SOURCE))
    evidence = json.loads(safe_worktree_text(EVIDENCE_MAP)) if EVIDENCE_MAP.is_file() else {}
    floor, floor_failures = validated_coverage_floor(index)
    failures.extend(floor_failures)
    for row, source in note_for_problem():
        note_text = safe_worktree_text(ROOT / source)
        commit = note_pinned_commit(note_text, default_commit)
        linked = linked_declaration_keys(note_text) | margin_mark_declaration_keys(source, evidence)
        modules = [row["principal_module"], *row.get("companion_modules", [])]
        current: list[DeclarationKey] = []
        moved: list[str] = []
        for module in modules:
            relative = module_relative(module)
            path = ROOT / relative
            if not path.is_file():
                path = ROOT / library_storage_path(relative)
            try:
                live = safe_worktree_text(path)
            except UnsafeSourceInput as error:
                failures.append(f"{row['problem_id']}: {error}")
                continue
            current.extend(declarations_for_module(relative, live))
            pinned_text = None
            for candidate in snapshot_blob_candidates(relative):
                pinned = git_run("show", f"{commit}:{candidate}")
                if pinned.returncode == 0:
                    pinned_text = pinned.stdout
                    break
            if pinned_text is None or pinned_text != live:
                moved.append(relative)
        if not current:
            continue
        current_set = set(current)
        failures.extend(
            required_note_declaration_failures(row, current_set, linked)
        )
        covered = [key for key in current if key in linked]
        ratio = len(covered) / len(current)
        status = "behind" if moved else "current"
        lines.append(
            f"  {row['problem_id']}: {len(covered)}/{len(current)} declarations "
            f"linked ({ratio:.0%}), source {status}"
        )
        if moved:
            lines.append(f"      moved since the pin: {', '.join(sorted(moved))}")
            missing = [key for key in current if key not in linked]
            if missing:
                head = ", ".join(
                    f"{relative}::{name}" for relative, name in missing[:6]
                )
                more = "" if len(missing) <= 6 else f", and {len(missing) - 6} more"
                lines.append(f"      not reached by the note: {head}{more}")
        row_floor = floor
        if "note_coverage_floor" in row:
            row_floor, row_floor_failures = validated_coverage_floor(
                row,
                label=f"{row['problem_id']}.note_coverage_floor",
            )
            failures.extend(row_floor_failures)
        if row_floor is not None and ratio < row_floor:
            failures.append(
                f"{row['problem_id']}: note reaches {ratio:.0%} of current "
                f"declarations, below the {row_floor:.0%} floor; rewrite the note "
                f"and repin, or lower its note_coverage_floor deliberately"
            )
        # The floor is measured against this checkout, which is what the notes
        # are built from.  The library is also developed on another branch, and
        # a note can be current here while that branch has already moved on.
        # That gap is reported and never gated: failing on someone else's
        # branch would make this check red through no fault of this tree.
        upstream = index.get("upstream_ref")
        if upstream:
            ahead = 0
            for module in modules:
                relative = module_relative(module)
                shown_text = None
                for candidate in snapshot_blob_candidates(relative):
                    shown = git_run("show", f"{upstream}:{candidate}")
                    if shown.returncode == 0:
                        shown_text = shown.stdout
                        break
                if shown_text is not None:
                    ahead += len(declarations_in(shown_text))
            if ahead > len(current):
                lines.append(
                    f"      upstream {upstream} is {ahead - len(current)} "
                    f"declaration(s) ahead of this checkout"
                )
    return lines, failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--list",
        action="store_true",
        help="print every resolved link rather than only the verdict",
    )
    parser.add_argument(
        "--coverage",
        action="store_true",
        help="also report, and gate on, how much of the current source each note reaches",
    )
    args = parser.parse_args()

    sources = note_sources()
    if not sources:
        print("check_problem_note_sources: no problem notes are registered")
        return 0

    default_commit = pinned_commit()
    default_commitshort = pinned_commitshort()
    cache: dict[tuple[str, str], list[str]] = {}
    errors: list[str] = []
    checked = 0
    resolved_commits: set[str] = set()

    # Resolve immutable note blobs in one Git protocol session. The validation
    # loop below still owns every per-link diagnostic, while snapshot_lines()
    # becomes a cache lookup instead of launching one `git show` per module.
    snapshot_requests = set()
    for source in sources:
        try:
            note_text = safe_worktree_text(ROOT / source)
        except UnsafeSourceInput:
            continue
        commit = note_pinned_commit(note_text, default_commit)
        snapshot_requests.update(
            (commit, library_relative(file_name))
            for file_name, _line_number, _declaration in links(note_text)
        )
    snapshot_lines_batch(snapshot_requests, cache)

    for source in sources:
        try:
            note_text = safe_worktree_text(ROOT / source)
        except UnsafeSourceInput as error:
            errors.append(f"{source}: {error}")
            continue
        pin_failure = source_pin_failure(
            source, note_text, default_commit, default_commitshort
        )
        if pin_failure is not None:
            errors.append(pin_failure)
        commit = note_pinned_commit(note_text, default_commit)
        resolved_commits.add(commit)
        if (
            git_run("cat-file", "-e", f"{commit}^{{commit}}").returncode
            != 0
        ):
            errors.append(f"{source}: pinned commit is absent: {commit}")
            continue
        found = links(note_text)
        if not found:
            errors.append(f"{source}: authored no formal source links")
        for file_name, line_number, declaration in found:
            checked += 1
            relative = library_relative(file_name)
            lines = snapshot_lines(commit, relative, cache)
            if not lines:
                errors.append(
                    f"{source}: {relative} is absent from the pinned snapshot"
                )
                continue
            if not 1 <= line_number <= len(lines):
                errors.append(
                    f"{source}: {relative}:{line_number} is outside the pinned "
                    f"snapshot ({len(lines)} lines)"
                )
                continue
            line = lines[line_number - 1]
            if declaration is None:
                if not line.strip():
                    errors.append(
                        f"{source}: {relative}:{line_number} is blank in the "
                        "pinned snapshot"
                    )
                continue
            if not declares_at(lines, line_number - 1, declaration):
                errors.append(
                    f"{source}: {relative}:{line_number} does not declare "
                    f"{declaration!r}; the pinned line reads {line.strip()[:72]!r}"
                )
            elif args.list:
                print(f"  {declaration}  <-  {relative}:{line_number}")

    generated_failures, generated_checked = generated_note_failures(ledger_commit())
    errors.extend(generated_failures)
    rendered_failures, rendered_checked = rendered_link_failures(
        default_commit, ledger_commit()
    )
    errors.extend(rendered_failures)

    report: list[str] = []
    if args.coverage:
        report, coverage_failures = coverage_report(default_commit)
        errors.extend(coverage_failures)

    if errors:
        print(f"check_problem_note_sources: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        for line in report:
            print(line)
        return 1

    print(
        f"check_problem_note_sources: {checked} link(s) across {len(sources)} note(s) "
        f"resolve against {len(resolved_commits)} pinned commit(s); "
        f"{generated_checked} generated statement link(s) resolve at the ledger pin; "
        f"{rendered_checked} printed source URL(s) exist exactly as rendered"
    )
    for line in report:
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
