#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise historical packet identity, export isolation, and bounded Git calls.

All history is synthetic. These fixtures neither export the public corpus nor
run a recovery participant, and their assertions stay active under ``python -O``.
"""

from __future__ import annotations

import gzip
import io
import json
import os
import subprocess
import sys
import tempfile
from contextlib import ExitStack, redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

import build_benchmark_packet as experiment
import validation_singleflight as singleflight


def require(condition: bool, message: str) -> None:
    """Keep portability failures active when CI invokes Python with ``-O``."""
    if not condition:
        raise AssertionError(message)


TARGET = "fixture_hidden_result"
FUTURE_SUBJECT = "Reveal the fixture hidden result and its exact proof mechanism"
SOURCE_PATH = "lean/ErdosProblems/Fixture.lean"
CUT_SOURCE = "-- Literal archive placeholder: $Format:%H$\ntheorem prior_fact : True := by trivial\n"


def expect_refusal(action, message: str) -> None:
    """Only an explicit failed operation counts as a rejection."""
    try:
        action()
    except SystemExit as error:
        require(error.code not in (None, 0), message + ": exited successfully")
    except (ValueError, RuntimeError):
        pass
    else:
        raise AssertionError(message)


def check_git_environment() -> None:
    completed = subprocess.CompletedProcess(
        ["git"], returncode=0, stdout="ok\n", stderr=""
    )
    hostile = {
        "GIT_DIR": "/foreign/git",
        "GIT_WORK_TREE": "/foreign/worktree",
        "GIT_NAMESPACE": "foreign-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/foreign/",
        "PYTHONPATH": "/foreign/python",
        "LANGUAGE": "fr_FR",
    }
    with patch.dict(os.environ, hostile, clear=False):
        expected = singleflight.command_environment()
        with patch.object(
            experiment.subprocess, "run", return_value=completed
        ) as runner:
            result = experiment.git("status", cwd=Path("/benchmark-fixture"))

    require(result == "ok\n", "benchmark Git helper did not return stdout")
    require(len(runner.call_args_list) == 1, "benchmark Git helper made an unexpected call count")
    for call in runner.call_args_list:
        require(call.kwargs["env"] == expected, "benchmark Git call drifted from canonical environment")
        require(
            call.kwargs["timeout"] == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
            "benchmark Git call lost its bounded timeout",
        )
    require(
        all(
            key not in expected
            for key in {
                "GIT_DIR",
                "GIT_WORK_TREE",
                "GIT_NAMESPACE",
                "GIT_REPLACE_REF_BASE",
                "PYTHONPATH",
            }
        ),
        "benchmark Git environment retained caller selectors",
    )
    require(expected["LANGUAGE"] == "C.UTF-8", "benchmark Git locale was not canonicalized")
    require(
        experiment.ENVIRONMENT_CONTRACT == "clean_reproduction_subprocess_environment_v1",
        "benchmark environment contract identifier drifted",
    )


class HistoricalFixture:
    """Keep the registered history available but outside the current lineage."""

    def __init__(self, base: Path, source_path: str = SOURCE_PATH, cut_source: str = CUT_SOURCE):
        self.base = base
        self.root = base / "source"
        self.root.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Benchmark Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "commit.gpgSign", "false")
        self.git("config", "core.hooksPath", os.devnull)
        source = self.root / source_path
        source.parent.mkdir(parents=True)
        source.write_text(cut_source, encoding="utf-8")
        (self.root / "README.md").write_text("Synthetic historical packet fixture.\n", encoding="utf-8")
        self.git("add", "--", source_path, "README.md")
        self.git("commit", "-qm", "Before the held-out result")
        self.cut = self.git("rev-parse", "HEAD")
        source.write_text(
            cut_source + f"theorem {TARGET} : True := by trivial\n", encoding="utf-8"
        )
        self.git("add", "--", source_path)
        self.git("commit", "-qm", FUTURE_SUBJECT)
        self.introducing = self.git("rev-parse", "HEAD")
        self.git("checkout", "--orphan", "reconciled", "-q")
        self.git("rm", "--cached", "-qr", ".")
        source.write_text("theorem reconciled_fact : True := by trivial\n", encoding="utf-8")
        self.git("add", "--", source_path)
        self.git("commit", "-qm", "Reconciled source has a separate lineage")
        self.head = self.git("rev-parse", "HEAD")
        self.items_path = self.root / "docs/semantic/lab/benchmark_items.json"
        self.items_path.parent.mkdir(parents=True)
        self.item = {
            "item_id": "bm-fixture",
            "target": TARGET,
            "cut_commit": self.cut,
            "introducing_commit": self.introducing,
            "introducing_subject": FUTURE_SUBJECT,
        }
        self.write_items([self.item])
        self.corpus = self.root / "docs/semantic_corpus.json.gz"
        payload = {
            "concepts": [], "relations": [],
            "statement_nodes": [{
                "id": "fixture-node",
                "evidence": [{"declaration": TARGET}],
                "canonical_statement": "The fixture's withheld future statement",
                "logical_class": "unconditional_object_theorem",
                "engine": "fixture proof mechanism",
                "concepts": [], "problem": "257",
            }],
        }
        self.corpus.write_bytes(gzip.compress(json.dumps(payload).encode("utf-8"), mtime=0))
        self.lab = self.root / "docs/theory_lab.json"
        self.lab.write_text("{}\n", encoding="utf-8")

    def git(self, *args: str) -> str:
        completed = subprocess.run(
            ("git",) + args, cwd=self.root,
            env=singleflight.command_environment(), capture_output=True, text=True,
            check=True, timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
        )
        return completed.stdout.strip()

    def write_items(self, items: list[dict]) -> None:
        self.items_path.write_text(json.dumps(items) + "\n", encoding="utf-8")

    def patch(self) -> ExitStack:
        stack = ExitStack()
        for key, value in {
            "ROOT": self.root, "BENCHMARK_ITEMS": self.items_path,
            "CORPUS": self.corpus, "LAB": self.lab,
        }.items():
            stack.enter_context(patch.object(experiment, key, value))
        return stack


def check_frozen_packet(fixture: HistoricalFixture) -> None:
    dest = fixture.base / "participant"
    real_run = subprocess.run
    hostile = {
        "GIT_DIR": "/foreign/git", "GIT_WORK_TREE": "/foreign/worktree",
        "GIT_NAMESPACE": "foreign-namespace", "PYTHONPATH": "/foreign/python",
    }
    with fixture.patch(), patch.dict(os.environ, hostile, clear=False):
        expected_env = singleflight.command_environment()
        with patch.object(experiment.subprocess, "run", wraps=real_run) as runner:
            result = experiment.build_packet(TARGET, "signatures", dest, keep=True, problem="257")
    require((dest / SOURCE_PATH).read_text(encoding="utf-8") == CUT_SOURCE,
            "packet used current history instead of the registered historical cut")
    require(all(p.name != ".git" for p in dest.rglob("*")),
            "participant export carries Git history or a worktree link")
    manifest = json.loads((dest / "docs/_packet/MANIFEST.json").read_text(encoding="utf-8"))
    require(manifest.get("schema") == "erdos249257-benchmark-packet/2", "packet schema is not v2")
    require(manifest.get("evaluation_ready") is False,
            "packet preparation incorrectly authorizes a scored recovery evaluation")
    for field in ("introducing_commit", "introducing_subject", "target_fingerprint", "cut_commit"):
        require(field not in manifest, f"participant manifest discloses evaluator field {field}")
    participant_text = "\n".join(
        p.read_text(encoding="utf-8") for p in dest.rglob("*") if p.is_file()
    )
    for private in (TARGET, FUTURE_SUBJECT, fixture.cut, fixture.introducing, fixture.head):
        require(private not in participant_text, "participant export leaks future or evaluator identity")
    answer = result["answer_key"]
    require(answer["target"] == TARGET, "outside answer key lost target identity")
    require(answer["cut_commit"] == fixture.cut, "outside answer key lost frozen cutoff")
    require(answer["introducing_commit"] == fixture.introducing,
            "outside answer key lost introducing commit")
    archive_calls = []
    for call in runner.call_args_list:
        command = call.args[0]
        if command[0] != "git":
            continue
        require(call.kwargs.get("env") == expected_env, "real packet Git call inherited hostile selectors")
        require(call.kwargs.get("timeout") == singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
                "real packet Git call is unbounded")
        require("-S" not in command, "registered packet rediscovered its cut from current history")
        require("worktree" not in command, "packet construction created a linked worktree")
        if "archive" in command:
            archive_calls.append(call)
    require(len(archive_calls) == 1, "packet must export exactly one frozen archive")
    require(fixture.cut in archive_calls[0].args[0], "archive used a nonregistered source cut")
    require(archive_calls[0].kwargs.get("stdout") not in (None, subprocess.PIPE),
            "archive output is not streamed to a bounded temporary-file path")
    probe = real_run(
        ("git", "cat-file", "-t", fixture.introducing), cwd=dest,
        env=singleflight.command_environment(), capture_output=True, text=True,
        check=False, timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    )
    require(probe.returncode != 0, "participant can retrieve the future Git object")


def check_registry_refusals(fixture: HistoricalFixture) -> None:
    rows = [
        [],
        [fixture.item, dict(fixture.item)],
        [{**fixture.item, "cut_commit": "HEAD^"}],
        [{**fixture.item, "introducing_commit": "not-a-frozen-commit"}],
        [{**fixture.item, "cut_commit": "0" * 40}],
        [{**fixture.item, "introducing_commit": "0" * 40}],
        [{**fixture.item, "cut_commit": fixture.git("rev-parse", fixture.cut + "^{tree}")}],
        [{**fixture.item, "cut_commit": fixture.head}],
        [{k: v for k, v in fixture.item.items() if k != "introducing_commit"}],
    ]
    with fixture.patch():
        for index, items in enumerate(rows):
            fixture.write_items(items)
            dest = fixture.base / f"invalid-registry-{index}"
            expect_refusal(
                lambda: experiment.build_packet(TARGET, "signatures", dest, keep=True),
                f"invalid registered identity {index} was accepted",
            )
            require(not dest.exists(), "invalid registered identity created a participant export")
        fixture.write_items([{**fixture.item, "target": "prior_fact"}])
        expect_refusal(
            lambda: experiment.build_packet("prior_fact", "signatures", fixture.base / "leaked", keep=True),
            "target already present at the cut was accepted",
        )
    fixture.write_items([fixture.item])


def check_historical_library_layouts(base: Path) -> None:
    """Historical project roots must not produce a vacuous clean holdout."""
    parser_root = base / "layout-parser"
    names = set()
    for index, library in enumerate((
        "Erdos249257", "ErdosProblems", "lean/Erdos249257", "lean/ErdosProblems",
    )):
        path = parser_root / library / "Fixture.lean"
        path.parent.mkdir(parents=True)
        name = f"layout_fact_{index}"
        names.add(name)
        path.write_text(f"theorem {name} : True := by trivial\n", encoding="utf-8")
    require(experiment.declarations_at(parser_root) == names,
            "declaration extraction does not cover both historical and current library roots")
    (parser_root / "ErdosProblems/Unreadable.lean").write_bytes(b"\xff\xfe")
    expect_refusal(lambda: experiment.declarations_at(parser_root),
                   "non-UTF-8 historical source was silently omitted from declaration extraction")

    historical_base = base / "historical-layout"
    historical_base.mkdir()
    source_path = "ErdosProblems/Fixture.lean"
    fixture = HistoricalFixture(historical_base, source_path=source_path)
    with fixture.patch():
        dest = historical_base / "participant"
        result = experiment.build_packet(TARGET, "signatures", dest)
        require((dest / source_path).read_text(encoding="utf-8") == CUT_SOURCE,
                "historical root-level source changed during export")
        require(result["manifest"]["declarations_at_cut"] == 1,
                "historical root-level declaration was silently omitted")
        fixture.write_items([{**fixture.item, "target": "prior_fact"}])
        leaked = historical_base / "target-present"
        expect_refusal(lambda: experiment.build_packet("prior_fact", "signatures", leaked),
                       "target present in a historical root-level library was accepted")
        require(not (leaked / "docs/_packet/MANIFEST.json").exists(),
                "root-level target leakage produced an admitted packet manifest")

    empty_base = base / "empty-declarations"
    empty_base.mkdir()
    fixture = HistoricalFixture(empty_base, cut_source="-- No declarations at this historical cut.\n")
    with fixture.patch():
        dest = empty_base / "participant"
        expect_refusal(lambda: experiment.build_packet(TARGET, "signatures", dest),
                       "zero extracted declarations were treated as proof of holdout absence")
        require(not (dest / "docs/_packet/MANIFEST.json").exists(),
                "empty declaration extraction produced an admitted packet manifest")


def check_destination_refusals(fixture: HistoricalFixture) -> None:
    existing = fixture.base / "existing-packet"
    existing.mkdir()
    sentinel = existing / "keep.txt"
    sentinel.write_text("operator-owned bytes\n", encoding="utf-8")
    existing_file = fixture.base / "existing-file"
    existing_file.write_text("preserve file\n", encoding="utf-8")
    link = fixture.base / "packet-link"
    link.symlink_to(existing, target_is_directory=True)
    dangling = fixture.base / "dangling-link"
    dangling.symlink_to(fixture.base / "absent-target")
    other_checkout = fixture.base / "another-checkout"
    other_checkout.mkdir()
    (other_checkout / ".git").mkdir()
    alias = fixture.base / "source-alias"
    alias.symlink_to(fixture.root, target_is_directory=True)
    refused = [
        existing, existing_file, link, dangling, fixture.root / "packet",
        other_checkout / "packet", alias / "packet",
    ]
    with fixture.patch():
        for dest in refused:
            expect_refusal(lambda: experiment.export_snapshot(fixture.cut, dest),
                           f"unsafe packet destination was accepted: {dest.name}")
        with patch.object(sys, "argv", [
            "build_benchmark_packet.py", "--target", TARGET, "--arm", "signatures",
            "--dest", str(existing), "--remove",
        ]), redirect_stderr(io.StringIO()):
            expect_refusal(experiment.main, "legacy --remove silently deleted a packet")
    require(sentinel.read_text(encoding="utf-8") == "operator-owned bytes\n",
            "existing packet contents were modified")
    require(existing_file.read_text(encoding="utf-8") == "preserve file\n",
            "existing file contents were modified")
    require(link.is_symlink() and dangling.is_symlink(), "destination link was replaced")
    require(not (fixture.root / "packet").exists(), "source checkout received an export")
    require(not (other_checkout / "packet").exists(), "another Git checkout received an export")


def check_evaluator_receipt_boundaries(fixture: HistoricalFixture) -> None:
    existing = fixture.base / "existing-answer.json"
    existing.write_text("preserve evaluator bytes\n", encoding="utf-8")
    live_link = fixture.base / "answer-link.json"
    live_link.symlink_to(existing)
    missing_target = fixture.base / "uncreated-answer.json"
    dangling_link = fixture.base / "dangling-answer.json"
    dangling_link.symlink_to(missing_target)
    with fixture.patch():
        for index, key in enumerate((existing, live_link, dangling_link, None)):
            dest = fixture.base / f"key-refusal-{index}"
            key = key if key is not None else dest / "inside-answer.json"
            with patch.object(sys, "argv", [
                "build_benchmark_packet.py", "--target", TARGET, "--arm", "signatures",
                "--dest", str(dest), "--answer-key", str(key),
            ]), redirect_stderr(io.StringIO()):
                expect_refusal(experiment.main, "unsafe evaluator receipt path was accepted")
            require(not dest.exists(), "invalid answer-key destination still created a packet")
        dest = fixture.base / "cli-participant"
        key = fixture.base / "cli-participant-answer.json"
        stdout = io.StringIO()
        with patch.object(sys, "argv", [
            "build_benchmark_packet.py", "--target", TARGET, "--arm", "signatures",
            "--dest", str(dest), "--answer-key", str(key),
        ]), redirect_stdout(stdout):
            require(experiment.main() == 0, "valid outside evaluator receipt was refused")
        answer = json.loads(key.read_text(encoding="utf-8"))
        require(answer["cut_commit"] == fixture.cut and answer["introducing_commit"] == fixture.introducing,
                "CLI evaluator receipt lost its frozen source identity")
        require(json.loads(stdout.getvalue())["evaluation_ready"] is False,
                "CLI claimed a scored evaluation was ready")
        for hidden in (TARGET, fixture.cut, fixture.introducing, FUTURE_SUBJECT):
            require(hidden not in stdout.getvalue(), "CLI stdout disclosed evaluator identity")
    require(existing.read_text(encoding="utf-8") == "preserve evaluator bytes\n",
            "existing evaluator receipt was overwritten")
    require(live_link.is_symlink() and dangling_link.is_symlink(), "evaluator symlink was replaced")
    require(not missing_target.exists(), "dangling evaluator symlink was followed")


def check_archive_attribute_parity(fixture: HistoricalFixture) -> None:
    """Neither tracked nor local archive attributes may rewrite the frozen cut."""
    local_attributes = fixture.root / ".git/info/attributes"
    with fixture.patch():
        # A target is present in the actual cut but export-ignore would hide it.
        fixture.write_items([{**fixture.item, "target": "prior_fact"}])
        local_attributes.write_text("lean/** export-ignore\n", encoding="utf-8")
        dest = fixture.base / "local-ignore-export"
        expect_refusal(
            lambda: experiment.build_packet("prior_fact", "signatures", dest),
            "local export-ignore concealed a target present in the frozen tree",
        )
        require(not dest.exists(), "omitted source was detected only after creating the export")
        fixture.write_items([fixture.item])
        local_attributes.write_text("lean/** export-subst\n", encoding="utf-8")
        dest = fixture.base / "local-subst-export"
        expect_refusal(
            lambda: experiment.export_snapshot(fixture.cut, dest),
            "local export-subst rewrote historical source bytes",
        )
        require(not dest.exists(), "rewritten source was detected only after creating the export")
        local_attributes.unlink()

        tracked = fixture.root / ".gitattributes"
        tracked.write_text("lean/** export-ignore\n", encoding="utf-8")
        fixture.git("add", "--", ".gitattributes")
        fixture.git("commit", "-qm", "Tracked attribute omits historical source")
        cut = fixture.git("rev-parse", "HEAD")
        dest = fixture.base / "tracked-ignore-export"
        expect_refusal(lambda: experiment.export_snapshot(cut, dest),
                       "tracked export-ignore omitted frozen tree files")
        require(not dest.exists(), "tracked omission created a partial export")

        tracked.write_text("identity.txt export-subst\n", encoding="utf-8")
        identity = fixture.root / "identity.txt"
        identity.write_text("literal=$Format:%H$\n", encoding="utf-8")
        fixture.git("add", "--", ".gitattributes", "identity.txt")
        fixture.git("commit", "-qm", "Tracked attribute rewrites historical source")
        cut = fixture.git("rev-parse", "HEAD")
        dest = fixture.base / "tracked-subst-export"
        expect_refusal(lambda: experiment.export_snapshot(cut, dest),
                       "tracked export-subst changed frozen tree bytes")
        require(not dest.exists(), "tracked substitution created a partial export")

        identity.write_text("literal bytes with no expansion\n", encoding="utf-8")
        fixture.git("add", "--", "identity.txt")
        fixture.git("commit", "-qm", "Inert archive attribute preserves identical bytes")
        dest = fixture.base / "inert-attribute-export"
        experiment.export_snapshot(fixture.git("rev-parse", "HEAD"), dest)
        require((dest / "identity.txt").read_bytes() == identity.read_bytes(),
                "byte-identical archive with inert attributes was not preserved")


def check_unsafe_archive_refusals(fixture: HistoricalFixture) -> None:
    link = fixture.root / "unsafe-link"
    link.symlink_to("../../outside-fixture")
    fixture.git("add", "--", "unsafe-link")
    fixture.git("commit", "-qm", "Archive contains an unsafe symlink")
    with fixture.patch():
        expect_refusal(
            lambda: experiment.export_snapshot(fixture.git("rev-parse", "HEAD"), fixture.base / "symlink-export"),
            "archive symlink was accepted",
        )
    fixture.git("rm", "-q", "--", "unsafe-link")
    fixture.git("update-index", "--add", "--cacheinfo", f"160000,{fixture.cut},vendor/history")
    fixture.git("commit", "-qm", "Archive contains an omitted submodule")
    with fixture.patch():
        expect_refusal(
            lambda: experiment.export_snapshot(fixture.git("rev-parse", "HEAD"), fixture.base / "submodule-export"),
            "archive silently omitted a tracked submodule",
        )


def main() -> int:
    check_git_environment()
    with tempfile.TemporaryDirectory(prefix="benchmark-packet-fixture-") as raw:
        fixture = HistoricalFixture(Path(raw))
        check_frozen_packet(fixture)
        check_registry_refusals(fixture)
        check_historical_library_layouts(fixture.base)
        check_destination_refusals(fixture)
        check_evaluator_receipt_boundaries(fixture)
        check_archive_attribute_parity(fixture)
        check_unsafe_archive_refusals(fixture)
    print("test_build_benchmark_packet_environment: frozen cuts, export isolation, preservation, and bounded Git PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
