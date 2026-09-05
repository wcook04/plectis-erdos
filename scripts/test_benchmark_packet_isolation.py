#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay held-out answer isolation using real, temporary Git history."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch

import build_benchmark_packet as builder


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="benchmark-isolation-") as temporary:
        source = Path(temporary) / "source"
        source.mkdir()

        def git(*args: str, cwd: Path = source) -> str:
            return subprocess.check_output(
                ["git", *args], cwd=cwd, text=True,
                stderr=subprocess.DEVNULL,
                env=builder.singleflight.command_environment(),
                timeout=builder.GIT_COMMAND_TIMEOUT_SECONDS,
            ).strip()

        git("init")
        git("config", "user.name", "Test fixture")
        git("config", "user.email", "fixture@example.invalid")
        (source / "ErdosProblems").mkdir()
        lean = source / "ErdosProblems/Fixture.lean"
        lean.write_text("theorem baseline : True := by trivial\n")
        (source / "docs").mkdir()
        corpus = source / "docs/semantic_corpus.json"
        corpus.write_text('{"statement_nodes": []}')
        git("add", ".")
        git("commit", "-m", "Baseline")
        lean.write_text(lean.read_text() + "theorem hidden_answer : True := by trivial\n")
        git("add", ".")
        git("commit", "-m", "Prove hidden_answer")
        future = git("rev-parse", "HEAD")
        packet = Path(temporary) / "packet"
        with patch.multiple(builder, ROOT=source, CORPUS=corpus,
                            LAB=source / "docs/theory_lab.json"):
            result = builder.build_packet("hidden_answer", "signatures", packet, True)
            manifest = json.loads((packet / "docs/_packet/MANIFEST.json").read_text())
            assert "hidden_answer" not in json.dumps(manifest)
            for field in ("introducing_commit", "introducing_subject", "target_fingerprint"):
                assert field not in manifest
            assert result["answer_key"]["introducing_commit"] == future
            assert "hidden_answer" not in (packet / "ErdosProblems/Fixture.lean").read_text()
            assert not (packet / ".git").exists()
            attempt = subprocess.run(
                ["git", "show", future + ":ErdosProblems/Fixture.lean"], cwd=packet,
                capture_output=True, env=builder.singleflight.command_environment(),
                timeout=builder.GIT_COMMAND_TIMEOUT_SECONDS,
            )
            assert attempt.returncode != 0, "future answer remains reachable from packet"
            try:
                builder.build_packet("hidden_answer", "signatures", packet, True)
            except SystemExit as exc:
                assert "already exists" in str(exc)
            else:
                raise AssertionError("existing packet was overwritten")
            untouched = Path(temporary) / "unrelated"
            untouched.mkdir()
            try:
                builder.remove_packet(untouched)
            except SystemExit:
                pass
            else:
                raise AssertionError("unrelated directory was deleted")
            assert untouched.exists()
            builder.remove_packet(packet)
            assert not packet.exists()
    print("benchmark isolation: future Git objects and target metadata withheld; safe lifecycle PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
