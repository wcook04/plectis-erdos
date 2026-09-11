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
    )
    seen: set[str] = set()
    for candidate in candidates:
        if not candidate or candidate in seen:
            continue
        seen.add(candidate)
        if (root / candidate).is_file():
            return candidate
    return library_storage_path(relative)


def _collect_library_files(root: Path, name: str, *, layout: str) -> list[Path]:
    paths: list[Path] = []
    seen: set[Path] = set()
    root_file = library_root_file(root, name, layout=layout)
    if root_file.is_file():
        resolved = root_file.resolve()
        paths.append(root_file)
        seen.add(resolved)
    directory = library_dir(root, name, layout=layout)
    if directory.is_dir():
        for path in sorted(directory.rglob("*.lean")):
            resolved = path.resolve()
            if resolved not in seen:
                paths.append(path)
                seen.add(resolved)
    return paths


def library_source_paths(
    root: Path, *, layout: str = LAYOUT_FULL_SOURCE
) -> list[Path]:
    """Every ``.lean`` file in the two proof-corpus libraries.

    ``full_source`` (release validation) rejects a missing configured root and
    rejects the same module owned by both the old root layout and ``lean/``.
    Historical and truncated-reader modes are explicit; they never silently
    merge whichever directory happens to exist.
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
    seen_ids: dict[str, Path] = {}
    for name in LIBRARY_ROOTS:
        collected = _collect_library_files(root, name, layout=layout)
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
    return paths

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
