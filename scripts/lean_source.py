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
import subprocess
from pathlib import Path

# The two libraries whose sources are the proof corpus proper.  Everything
# else in the tree (Challenge fixtures, adapters, research corpus) is held to
# a different contract and is classified separately by each consumer.
LIBRARY_ROOTS = ("Erdos249257", "ErdosProblems")
LIBRARY_SOURCE_DIR = "lean"
LAYOUT_FULL_SOURCE = "full_source"
LAYOUT_HISTORICAL_ROOT = "historical_root"
LAYOUT_NESTED = "nested_lean"
LAYOUT_TRUNCATED_READER = "truncated_reader"


class LibraryLayoutError(ValueError):
    """The checked revision's corpus layout is missing or ambiguous."""


def _lakefile_corpus_src_dirs(root: Path) -> dict[str, str] | None:
    """Read corpus ``srcDir`` values from this revision's lakefile, if present."""
    lakefile = root / "lakefile.toml"
    if not lakefile.is_file():
        return None
    try:
        text = lakefile.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        return None
    dirs: dict[str, str] = {}
    current: str | None = None
    saw_src = False
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if line == "[[lean_lib]]":
            if current in LIBRARY_ROOTS and not saw_src:
                dirs.setdefault(current, "")
            current = None
            saw_src = False
            continue
        if line.startswith("name"):
            _, _, value = line.partition("=")
            name = value.strip().strip('"').strip("'")
            current = name if name in LIBRARY_ROOTS else None
            continue
        if current in LIBRARY_ROOTS and line.startswith("srcDir"):
            _, _, value = line.partition("=")
            dirs[current] = value.strip().strip('"').strip("'")
            saw_src = True
            current = None
    if current in LIBRARY_ROOTS and not saw_src:
        dirs.setdefault(current, "")
    return dirs or None


def configured_library_source_dir(root: Path, *, layout: str = LAYOUT_FULL_SOURCE) -> str:
    """Storage prefix for the two corpus roots in the revision being checked."""
    if layout == LAYOUT_HISTORICAL_ROOT:
        return ""
    if layout == LAYOUT_NESTED:
        return LIBRARY_SOURCE_DIR
    configured = _lakefile_corpus_src_dirs(root)
    if configured is None:
        if layout == LAYOUT_TRUNCATED_READER:
            return LIBRARY_SOURCE_DIR
        raise LibraryLayoutError(
            "missing lakefile.toml; cannot resolve corpus layout for this revision"
        )
    values = {configured.get(name, "") for name in LIBRARY_ROOTS}
    if len(values) != 1:
        raise LibraryLayoutError(
            "Erdos249257 and ErdosProblems disagree on srcDir in lakefile.toml: "
            f"{configured}"
        )
    return values.pop()


def _prefixed(root: Path, prefix: str, *parts: str) -> Path:
    return root.joinpath(prefix, *parts) if prefix else root.joinpath(*parts)


def library_dir(root: Path, name: str, *, layout: str = LAYOUT_FULL_SOURCE) -> Path:
    """Configured corpus directory for this revision. No existence fallback."""
    return _prefixed(root, configured_library_source_dir(root, layout=layout), name)


def library_root_file(root: Path, name: str, *, layout: str = LAYOUT_FULL_SOURCE) -> Path:
    """Configured ``Erdos249257.lean`` for this revision. No existence fallback."""
    return _prefixed(
        root, configured_library_source_dir(root, layout=layout), f"{name}.lean"
    )


def alternate_library_dir(root: Path, name: str, *, layout: str = LAYOUT_FULL_SOURCE) -> Path:
    """The other historical corpus location, used only to detect duplicates."""
    prefix = configured_library_source_dir(root, layout=layout)
    return root / name if prefix == LIBRARY_SOURCE_DIR else root / LIBRARY_SOURCE_DIR / name


def library_module_parts(path: Path, root: Path) -> tuple[str, ...]:
    """Module path parts with the storage prefix (``lean/``) removed."""
    rel = path.resolve().relative_to(root.resolve()).with_suffix("")
    parts = rel.parts
    if parts and parts[0] == LIBRARY_SOURCE_DIR:
        parts = parts[1:]
    return parts


def library_module_id(path: Path, root: Path) -> str:
    """Lean module identity: ``Erdos249257.Foo``, never ``lean.Erdos249257.Foo``."""
    return ".".join(library_module_parts(path, root))


def library_identity_path(relative: str) -> str:
    """Strip the ``lean/`` storage prefix from a corpus file path."""
    prefix = f"{LIBRARY_SOURCE_DIR}/"
    if relative.startswith(prefix):
        rest = relative[len(prefix) :]
        name = rest.split("/", 1)[0].removesuffix(".lean")
        if name in LIBRARY_ROOTS:
            return rest
    return relative


def library_storage_path(relative: str, *, prefix: str = LIBRARY_SOURCE_DIR) -> str:
    """Map a corpus-relative Lean path onto the given storage prefix.

    ``Erdos249257/Foo.lean`` under ``lean/`` becomes ``lean/Erdos249257/Foo.lean``.
    Already-prefixed paths and non-corpus paths are unchanged. This is storage,
    not Lean module identity, and it does not rewrite historical permalinks.
    """
    if not relative or relative.startswith(("http://", "https://")):
        return relative
    identity = library_identity_path(relative)
    name = identity.split("/", 1)[0].removesuffix(".lean")
    if name not in LIBRARY_ROOTS:
        return relative
    return f"{prefix}/{identity}" if prefix else identity


def library_storage_variants(relative: str) -> tuple[str, ...]:
    """Current nested spelling and historical root spelling for one corpus file."""
    current = library_storage_path(relative)
    identity = library_identity_path(relative)
    if current == identity:
        return (relative,)
    return (current, identity)


def checkout_source_relative(relative: str, root: Path) -> str:
    """Return the on-disk checkout relative path for a public or storage spelling."""
    identity = library_identity_path(relative)
    candidates = (
        library_storage_path(relative),
        identity,
        relative,
        f"verification/{identity}",
        f"verification/{relative.removeprefix('verification/')}",
        f"research/{identity}",
        f"research/{relative.removeprefix('research/')}",
    )
    seen: set[str] = set()
    for candidate in candidates:
        if not candidate or candidate in seen:
            continue
        seen.add(candidate)
        if (root / candidate).is_file():
            return candidate
    return library_storage_path(relative)


GIT_INDEX_QUERY_TIMEOUT_SECONDS = 60
LEAN_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)", re.MULTILINE)


def _git_unindexed_files(root: Path, paths: list[Path]) -> set[Path] | None:
    """Files under ``paths`` that are absent from the Git index.

    Returns ``None`` when ``root`` is not inside a Git worktree (tarball
    checkouts, temporary test roots), which is the only case in which the
    on-disk glob is the whole truth.  Any other Git failure raises: a builder
    that silently fell back to the glob would fingerprint whatever happened to
    be lying in the tree, which is exactly the defect this query exists to
    prevent.  ``--others`` without ``--exclude-standard`` lists ignored files
    too, because an ignored ``.lean`` file is just as absent from every clone.
    """
    existing = [path for path in paths if path.exists()]
    if not existing:
        return set()
    command = ["git", "-C", str(root), "ls-files", "--others", "-z", "--"]
    command.extend(str(path.relative_to(root)) for path in existing)
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            check=False,
            timeout=GIT_INDEX_QUERY_TIMEOUT_SECONDS,
        )
    except FileNotFoundError:
        return None
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise LibraryLayoutError(f"Git index query failed under {root}: {exc}") from exc
    if completed.returncode:
        stderr = completed.stderr.decode("utf-8", errors="replace")
        if completed.returncode == 128 and "not a git repository" in stderr.lower():
            return None
        raise LibraryLayoutError(
            f"Git index query exited {completed.returncode} under {root}: {stderr.strip()}"
        )
    unindexed: set[Path] = set()
    for raw in completed.stdout.split(b"\0"):
        if raw:
            unindexed.add((root / raw.decode("utf-8", errors="surrogateescape")).resolve())
    return unindexed


def _collect_library_files(
    root: Path, name: str, *, layout: str
) -> tuple[list[Path], list[Path]]:
    """Return ``(indexed, unindexed)`` corpus files for one library root.

    Enumeration follows the Git index, not the directory glob.  A file that is
    on disk but not in the index (untracked or ignored) does not exist in any
    clone, so a projection fingerprinted over it disagrees with every clone
    and with continuous integration.  On 2026-09-14 another lane staged
    untracked ``lean/ErdosProblems/Erdos1041/Counterexample/*.lean`` into the
    shared canonical checkout and every atlas and dependency-index build in
    that tree became irreproducible.  Outside Git the glob is authoritative.
    """
    candidates: list[Path] = []
    seen: set[Path] = set()
    root_file = library_root_file(root, name, layout=layout)
    if root_file.is_file():
        resolved = root_file.resolve()
        candidates.append(root_file)
        seen.add(resolved)
    directory = library_dir(root, name, layout=layout)
    if directory.is_dir():
        for path in sorted(directory.rglob("*.lean")):
            resolved = path.resolve()
            if resolved not in seen:
                candidates.append(path)
                seen.add(resolved)
    unindexed = _git_unindexed_files(root, [root_file, directory])
    if unindexed is None:
        return candidates, []
    indexed = [path for path in candidates if path.resolve() not in unindexed]
    excluded = [path for path in candidates if path.resolve() in unindexed]
    return indexed, excluded


def _unindexed_import_violations(
    root: Path, indexed: list[Path], unindexed: list[Path]
) -> list[str]:
    """Indexed modules that import a module absent from the Git index."""
    unindexed_ids = {library_module_id(path, root) for path in unindexed}
    if not unindexed_ids:
        return []
    violations: list[str] = []
    for path in indexed:
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            continue
        code = lean_code_without_comments_and_strings(text)
        for imported in LEAN_IMPORT_RE.findall(code):
            if imported in unindexed_ids:
                violations.append(
                    f"{path.relative_to(root).as_posix()} imports {imported}"
                )
    return violations


def library_source_inventory(
    root: Path, *, layout: str = LAYOUT_FULL_SOURCE
) -> dict[str, list[Path]]:
    """Corpus files split into ``paths`` (Git-indexed) and ``unindexed``.

    ``paths`` is what every projection builder must fingerprint and parse:
    it is the set every clone of the current index reproduces.  ``unindexed``
    is reported so that a builder can say what it left out.  When an indexed
    module imports an unindexed one the corpus is not reproducible at all
    (a clone's root build fails on the missing import), so that case raises
    instead of producing a projection nobody else can rebuild.
    """
    if layout == LAYOUT_FULL_SOURCE:
        configured = _lakefile_corpus_src_dirs(root)
        if configured is None:
            raise LibraryLayoutError(
                "full-source validation requires lakefile.toml for this revision"
            )
        for name in LIBRARY_ROOTS:
            intended = library_dir(root, name, layout=layout)
            intended_file = library_root_file(root, name, layout=layout)
            if not intended.is_dir() and not intended_file.is_file():
                raise LibraryLayoutError(
                    f"required corpus root {name} is missing at the configured "
                    f"layout path {intended.relative_to(root).as_posix()}"
                )
            alternate = alternate_library_dir(root, name, layout=layout)
            alternate_file = (
                root / f"{name}.lean"
                if configured_library_source_dir(root, layout=layout) == LIBRARY_SOURCE_DIR
                else root / LIBRARY_SOURCE_DIR / f"{name}.lean"
            )
            if (alternate.is_dir() or alternate_file.is_file()) and (
                intended.is_dir() or intended_file.is_file()
            ):
                raise LibraryLayoutError(
                    f"ambiguous duplicate corpus ownership for {name}: "
                    f"{intended.relative_to(root).as_posix()} and "
                    f"{alternate.relative_to(root).as_posix()}"
                )

    paths: list[Path] = []
    unindexed: list[Path] = []
    seen_ids: dict[str, Path] = {}
    for name in LIBRARY_ROOTS:
        collected, excluded = _collect_library_files(root, name, layout=layout)
        unindexed.extend(excluded)
        if layout == LAYOUT_FULL_SOURCE and not collected:
            raise LibraryLayoutError(f"configured corpus root {name} contains no Lean sources")
        for path in collected:
            module_id = library_module_id(path, root)
            previous = seen_ids.get(module_id)
            if previous is not None and previous.resolve() != path.resolve():
                raise LibraryLayoutError(
                    f"duplicate module identity {module_id}: "
                    f"{previous.relative_to(root).as_posix()} and "
                    f"{path.relative_to(root).as_posix()}"
                )
            seen_ids[module_id] = path
            paths.append(path)
    violations = _unindexed_import_violations(root, paths, unindexed)
    if violations:
        raise LibraryLayoutError(
            "indexed corpus modules import Lean sources that are not in the Git "
            "index; no clone can rebuild this tree, so no projection is built "
            "from it. Add the sources with `git add` or remove the imports: "
            + "; ".join(violations)
        )
    return {"paths": paths, "unindexed": unindexed}


def unindexed_library_sources(
    root: Path, *, layout: str = LAYOUT_FULL_SOURCE
) -> list[Path]:
    """Corpus ``.lean`` files on disk that no clone of the Git index has."""
    return library_source_inventory(root, layout=layout)["unindexed"]


def describe_unindexed_library_sources(
    root: Path, *, layout: str = LAYOUT_FULL_SOURCE
) -> str | None:
    """One operator-facing notice naming excluded sources, or ``None``."""
    excluded = unindexed_library_sources(root, layout=layout)
    if not excluded:
        return None
    listed = ", ".join(path.relative_to(root).as_posix() for path in excluded)
    return (
        f"excluded {len(excluded)} Lean source(s) absent from the Git index "
        f"(untracked or ignored; no clone has them): {listed}"
    )


def library_source_paths(
    root: Path, *, layout: str = LAYOUT_FULL_SOURCE
) -> list[Path]:
    """Every Git-indexed ``.lean`` file in the two proof-corpus libraries.

    ``full_source`` (release validation) rejects a missing configured root and
    rejects the same module owned by both the old root layout and ``lean/``.
    Historical and truncated-reader modes are explicit; they never silently
    merge whichever directory happens to exist.  Files on disk but absent
    from the Git index are excluded (see ``library_source_inventory``).
    """
    return library_source_inventory(root, layout=layout)["paths"]


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
