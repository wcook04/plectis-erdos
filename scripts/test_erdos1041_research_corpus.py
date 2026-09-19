#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial privacy checks for the public Erdős #1041 corpus envelope."""

from __future__ import annotations

import os
import tempfile
from pathlib import Path

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
    require(
        not checker.private_path_leaks(b"no public/root/paper/status promotion"),
        "ordinary slash-separated prose was falsely classified as a root path",
    )


def test_public_path_rejects_symlinked_parent() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        corpus = root / "research_corpus" / "Erdos1041"
        corpus.mkdir(parents=True)
        outside = root / "outside-erdos1041-corpus"
        outside.mkdir()
        (outside / "exposed.txt").write_text("outside\n", encoding="utf-8")
        (corpus / "linked").symlink_to(outside, target_is_directory=True)
        original_root = checker.ROOT
        checker.ROOT = root
        try:
            try:
                checker.safe_public_path(
                    "research_corpus/Erdos1041/linked/exposed.txt"
                )
            except checker.CorpusError:
                pass
            else:
                require(
                    False,
                    "corpus path guard followed a symlinked parent directory",
                )
        finally:
            checker.ROOT = original_root


def test_public_bytes_rejects_special_file() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        fifo = root / "corpus.fifo"
        os.mkfifo(fifo)
        original_root = checker.ROOT
        checker.ROOT = root
        try:
            try:
                checker.read_public_bytes(fifo, "corpus.fifo")
            except checker.CorpusError as error:
                require(
                    "non-regular" in str(error) or "missing" in str(error),
                    f"special corpus path returned an unexpected error: {error}",
                )
            else:
                require(False, "special corpus path was accepted")
        finally:
            checker.ROOT = original_root


def test_legacy_and_generic_schema_identities_are_distinct() -> None:
    legacy = checker.envelope_version(
        {"schema": "erdos1041_public_research_corpus_manifest_v1"},
        {"schema": "erdos1041_strongest_result_activation_map_v1"},
        {"schema": "plectis_public_problem_corpus_checkpoint_v1"},
    )
    require(legacy == "legacy_v1", "legacy corpus schema was not retained")
    require(
        checker.strongest_result_id({"result_id": "legacy"}, legacy) == "legacy",
        "legacy strongest-result identity changed",
    )

    generic = checker.envelope_version(
        {"schema": "plectis_public_research_corpus_manifest_v2"},
        {"schema": "plectis_strongest_result_activation_map_v2"},
        {"schema": "plectis_public_problem_corpus_checkpoint_v2"},
    )
    require(generic == "generic_v2", "generic corpus schema was not recognized")
    require(
        checker.strongest_result_id(
            {"source_result_id": "packet-exact"}, generic
        ) == "packet-exact",
        "generic packet-result identity was not preserved",
    )
    try:
        checker.strongest_result_id(
            {"result_id": "activation", "source_result_id": "packet"}, generic
        )
    except checker.CorpusError:
        pass
    else:
        require(False, "generic row with two identities was accepted")


def test_mixed_schema_envelope_is_rejected() -> None:
    try:
        checker.envelope_version(
            {"schema": "plectis_public_research_corpus_manifest_v2"},
            {"schema": "erdos1041_strongest_result_activation_map_v1"},
            {"schema": "plectis_public_problem_corpus_checkpoint_v2"},
        )
    except checker.CorpusError:
        pass
    else:
        require(False, "mixed legacy/generic corpus envelope was accepted")


def test_generic_empty_authority_requires_explicit_source_only_posture() -> None:
    unresolved = {
        "source_result_id": "ordinary-source-row",
        "public_authority_paths": [],
        "authority_binding": {
            "status": "unresolved_source_locator",
            "posture": "source_status_only_not_public_authority",
            "reason": "research_packet_row_has_no_resolved_source_locator",
        },
    }
    require(
        checker.validate_result_authority(
            unresolved, "generic_v2", "ordinary-source-row"
        ) == [],
        "explicit source-only unresolved authority was not retained",
    )
    for invalid in (
        {
            "result_id": "activation",
            "public_authority_paths": [],
            "authority_binding": unresolved["authority_binding"],
        },
        {
            "source_result_id": "unlabelled-empty",
            "public_authority_paths": [],
        },
    ):
        try:
            checker.validate_result_authority(
                invalid,
                "generic_v2",
                str(invalid.get("result_id") or invalid.get("source_result_id")),
            )
        except checker.CorpusError:
            pass
        else:
            require(False, "empty generic authority escaped explicit binding checks")


def test_live_corpus() -> None:
    file_count, result_count, total_bytes = checker.check()
    require(file_count > 0, "public corpus unexpectedly contains no files")
    require(result_count > 0, "public corpus unexpectedly contains no results")
    require(total_bytes > 0, "public corpus unexpectedly contains no bytes")


def main() -> int:
    test_private_path_variants()
    test_public_path_rejects_symlinked_parent()
    test_public_bytes_rejects_special_file()
    test_legacy_and_generic_schema_identities_are_distinct()
    test_mixed_schema_envelope_is_rejected()
    test_generic_empty_authority_requires_explicit_source_only_posture()
    test_live_corpus()
    print(
        "test_erdos1041_research_corpus: case-insensitive private-path and "
        "live content-addressed corpus checks passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
