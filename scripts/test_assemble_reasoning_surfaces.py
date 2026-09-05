#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused contract tests for the long-paper source assembler."""

from __future__ import annotations

import importlib.util
import os
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ASSEMBLER_PATH = ROOT / "scripts" / "assemble_reasoning_surfaces.py"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def load_assembler():
    spec = importlib.util.spec_from_file_location(
        "assemble_reasoning_surfaces", ASSEMBLER_PATH
    )
    require(spec is not None and spec.loader is not None, "could not load assembler")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_manifest(assembler) -> None:
    makefile = (ROOT / "paper" / "Makefile").read_text(encoding="utf-8")
    require('--native-targets --form "Problem note"' in makefile,
            "Make note prerequisites no longer follow the public registry")
    require('$(REASONING_PARTS) $(REASONING_NOTE_SOURCES) $(REASONING_ASSEMBLER)' in makefile,
            "long-paper Make targets must consume note-source changes")
    expected_outputs = {
        "68": "erdos68-factorial-reasoning-surface.tex",
        "243": "erdos243-reciprocal-tail-reasoning-surface.tex",
        "249": "erdos249-totient-reasoning-surface.tex",
        "251": "erdos251-prime-gap-reasoning-surface.tex",
        "257": "erdos257-mersenne-reasoning-surface.tex",
        "269": "erdos269-running-lcm-reasoning-surface.tex",
        "1041": "erdos1041-lemniscate-reasoning-surface.tex",
        "1049": "erdos1049-rational-base-lambert-reasoning-surface.tex",
    }
    require(set(assembler.PAPERS) == set(expected_outputs), "paper manifest is not eight-wide")
    for key, output_name in expected_outputs.items():
        row = assembler.PAPERS[key]
        require(row["output"].name == output_name, f"paper {key} output drifted")
        require(
            "family_catalogue" in row["parts"]
            or f"a{key}_family_catalogue" in row["parts"],
            f"paper {key} omits its generated family catalogue",
        )
        if key not in {"249", "257"}:
            require(
                row.get("note_source") is not None,
                f"paper {key} lost its problem-note body owner",
            )
            require(
                row["parts"] == ("family_catalogue",),
                f"paper {key} regained duplicate authored body parts",
            )
            require(
                not (row["directory"] / "core.tex").exists()
                and not (row["directory"] / "back.tex").exists(),
                f"paper {key} retains a duplicate core or bibliography",
            )
            require(
                assembler.assemble(key) == row["output"].read_text(encoding="utf-8"),
                f"paper {key} note-derived assembly is not byte-preserving",
            )


def check_content_aware_writer(assembler) -> None:
    with tempfile.TemporaryDirectory(prefix="reasoning-assembler-test-") as temporary:
        root = Path(temporary)
        directory = root / "parts"
        directory.mkdir()
        (directory / "preamble.tex").write_text("PREAMBLE\n", encoding="utf-8")
        (directory / "core.tex").write_text("CORE\n", encoding="utf-8")
        (directory / "family_catalogue.tex").write_text("CATALOGUE\n", encoding="utf-8")
        (directory / "back.tex").write_text("BACK\n", encoding="utf-8")
        output = root / "paper.tex"

        original = assembler.PAPERS
        assembler.PAPERS = {
            "test": {
                "output": output,
                "directory": directory,
                "parts": ("core", "family_catalogue", "back"),
            }
        }
        try:
            assembler.write_one("test")
            require(output.read_text(encoding="utf-8") == assembler.assemble("test"), "initial assembly drifted")

            stable_ns = 1_700_000_000_000_000_000
            os.utime(output, ns=(stable_ns, stable_ns))
            assembler.write_one("test")
            require(
                output.stat().st_mtime_ns == stable_ns,
                "unchanged output was rewritten",
            )

            (directory / "core.tex").write_text("UPDATED CORE\n", encoding="utf-8")
            assembler.write_one("test")
            require("UPDATED CORE" in output.read_text(encoding="utf-8"), "changed part was not assembled")
        finally:
            assembler.PAPERS = original


def check_note_body_propagation(assembler) -> None:
    with tempfile.TemporaryDirectory(prefix="reasoning-note-owner-test-") as temporary:
        root = Path(temporary)
        directory = root / "parts"
        directory.mkdir()
        note = root / "note.tex"
        note.write_text(
            "NOTE PREAMBLE\n\\begin{document}\nORIGINAL CORE\n\n"
            "\\begin{thebibliography}{9}\nBACK\n\\end{thebibliography}\n"
            "\\end{document}\n",
            encoding="utf-8",
        )
        (directory / "preamble.tex").write_text(
            "LONG PREAMBLE\n\\begin{document}\n", encoding="utf-8"
        )
        (directory / "family_catalogue.tex").write_text(
            "FAMILY CATALOGUE\n", encoding="utf-8"
        )
        output = root / "long.tex"
        original = assembler.PAPERS
        assembler.PAPERS = {
            "test": {
                "output": output,
                "directory": directory,
                "note_source": note,
                "parts": ("family_catalogue",),
            }
        }
        try:
            first = assembler.assemble("test")
            require("ORIGINAL CORE" in first, "note core was not assembled")
            require("FAMILY CATALOGUE" in first, "long-only catalogue was omitted")
            require(first.count("\\begin{thebibliography}") == 1, "bibliography duplicated")
            note.write_text(
                note.read_text(encoding="utf-8").replace(
                    "ORIGINAL CORE", "UPDATED NOTE CORE"
                ),
                encoding="utf-8",
            )
            second = assembler.assemble("test")
            require("UPDATED NOTE CORE" in second, "note edit did not propagate")
            require(first != second, "note edit left derived long manuscript unchanged")
        finally:
            assembler.PAPERS = original


def main() -> int:
    assembler = load_assembler()
    check_manifest(assembler)
    check_content_aware_writer(assembler)
    check_note_body_propagation(assembler)
    print("test_assemble_reasoning_surfaces: pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
