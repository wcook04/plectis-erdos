#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Contract: a publication PDF must be the recorded build of its committed TeX.

The publication contract pins a ``.tex`` and its ``.pdf`` separately, so a
rebased manuscript and a PDF built before the rebase can both be restamped.
These fixtures reproduce that case and require the build manifest to refuse
it. They also require the PDF sync, which writes the manifest, to refuse a
stale build output and to reuse the recorded build of an unchanged paper.
"""

from __future__ import annotations

import io
import json
import os
import subprocess
import tempfile
from contextlib import redirect_stdout
from pathlib import Path

import paper_build_manifest as manifest
import sync_publication_pdfs as sync
from publication_contract import RepositoryReader

ROOT = manifest.ROOT
SECOND = 1_000_000_000
BASE = 1_700_000_000 * SECOND
NAMES = (("alpha", "68"), ("beta", "243"))


def require(condition: bool, message: object) -> None:
    """Keep manifest-guard failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def write(root: Path, relative: str, data: bytes, mtime_ns: int) -> None:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    os.utime(path, ns=(mtime_ns, mtime_ns))


def restamp(root: Path, artifacts: list[dict]) -> None:
    """Refresh both contract digests from disk, as ``--restamp --apply`` does."""
    for artifact in artifacts:
        artifact["source_content_digest"] = manifest.sha256(
            (root / artifact["source_path"]).read_bytes()
        )
        artifact["rendered_content_digest"] = manifest.sha256(
            (root / artifact["storage_path"]).read_bytes()
        )
    (root / "docs").mkdir(exist_ok=True)
    (root / manifest.CONTRACT_PATH).write_text(
        json.dumps({"artifacts": artifacts}, indent=2) + "\n", encoding="utf-8"
    )


def build_output(artifact: dict) -> str:
    return f"paper/{Path(artifact['rendered_path']).name}"


def build(root: Path, artifact: dict, label: str, mtime_ns: int) -> None:
    """A Makefile build output ``paper/<stem>.pdf`` written at ``mtime_ns``."""
    write(
        root,
        build_output(artifact),
        f"%PDF {artifact['id']} {label}\n".encode("utf-8"),
        mtime_ns,
    )


def sync_now(root: Path) -> tuple[int, str]:
    contract = json.loads((root / manifest.CONTRACT_PATH).read_text(encoding="utf-8"))
    with redirect_stdout(io.StringIO()):
        return sync.synchronize_publication_pdfs(root, contract)


def errors_at(root: Path) -> list[str]:
    return manifest.manifest_errors(manifest.WorktreeReader(root))


def recorded_repository(root: Path) -> list[dict]:
    """Two papers whose committed PDFs are the recorded builds of their TeX."""
    write(root, "paper/paper-house-style.sty", b"% house style\n", BASE)
    artifacts = []
    for name, problem in NAMES:
        artifact = {
            "id": name,
            "source_path": f"paper/{problem}/{name}.tex",
            "rendered_path": f"paper/{problem}/{name}.pdf",
            "storage_path": f"paper/{problem}/{name}.pdf",
        }
        write(root, f"paper/{problem}/{name}-body.tex", f"{name} body\n".encode(), BASE)
        write(
            root,
            artifact["source_path"],
            f"\\input{{{name}-body}}\n{name}\n".encode(),
            BASE,
        )
        write(root, artifact["storage_path"], f"%PDF {name} published\n".encode(), BASE)
        artifacts.append(artifact)
    restamp(root, artifacts)
    for artifact in artifacts:
        build(root, artifact, "first build", BASE + 10 * SECOND)
    code, message = sync_now(root)
    require(code == 0, f"fresh builds were not synchronized: {message}")
    for artifact in artifacts:
        (root / build_output(artifact)).unlink()
    restamp(root, artifacts)
    require(errors_at(root) == [], f"recorded fixture failed: {errors_at(root)}")
    return artifacts


def test_fresh_builds_are_recorded() -> None:
    with tempfile.TemporaryDirectory(prefix="build-manifest-fresh-") as raw:
        root = Path(raw)
        recorded_repository(root)
        payload = json.loads((root / manifest.MANIFEST_PATH).read_text(encoding="utf-8"))
        require(payload["schema"] == manifest.MANIFEST_SCHEMA, payload)
        alpha = payload["builds"]["alpha"]
        require(
            sorted(alpha["inputs"])
            == ["paper/68/alpha-body.tex", "paper/68/alpha.tex", "paper/paper-house-style.sty"],
            f"alpha inputs: {sorted(alpha['inputs'])}",
        )
        require(
            alpha["rendered_content_digest"]
            == manifest.sha256(b"%PDF alpha first build\n"),
            "the recorded PDF digest is not the copied build",
        )


def test_rebased_source_with_restamped_digests_is_refused() -> None:
    """The 2026-09-15 case: new TeX, a PDF built before it, both digests restamped."""
    with tempfile.TemporaryDirectory(prefix="build-manifest-rebase-") as raw:
        root = Path(raw)
        artifacts = recorded_repository(root)
        write(
            root,
            "paper/68/alpha.tex",
            b"\\input{alpha-body}\nalpha\n% sibling citation\n",
            BASE + 20 * SECOND,
        )
        restamp(root, artifacts)
        errors = errors_at(root)
        require(len(errors) == 1, errors)
        require("'alpha'" in errors[0] and "paper/68/alpha.tex" in errors[0], errors)
        require("make -C paper alpha.pdf" in errors[0], errors)
        require("sync_publication_pdfs.py" in errors[0], errors)


def test_changed_fragment_or_house_style_is_refused() -> None:
    with tempfile.TemporaryDirectory(prefix="build-manifest-fragment-") as raw:
        root = Path(raw)
        recorded_repository(root)
        write(root, "paper/243/beta-body.tex", b"beta body, revised\n", BASE + 20 * SECOND)
        errors = errors_at(root)
        require(len(errors) == 1 and "paper/243/beta-body.tex" in errors[0], errors)
        require("'beta'" in errors[0], errors)

    with tempfile.TemporaryDirectory(prefix="build-manifest-style-") as raw:
        root = Path(raw)
        recorded_repository(root)
        write(root, "paper/paper-house-style.sty", b"% revised style\n", BASE + 20 * SECOND)
        errors = errors_at(root)
        require(len(errors) == 2, errors)
        require(all("paper/paper-house-style.sty" in error for error in errors), errors)


def test_replaced_pdf_without_recorded_build_is_refused() -> None:
    with tempfile.TemporaryDirectory(prefix="build-manifest-pdf-") as raw:
        root = Path(raw)
        artifacts = recorded_repository(root)
        write(root, "paper/243/beta.pdf", b"%PDF beta copied by hand\n", BASE + 20 * SECOND)
        restamp(root, artifacts)
        errors = errors_at(root)
        require(len(errors) == 1, errors)
        require("not the PDF its recorded build produced" in errors[0], errors)


def test_missing_and_unregistered_rows_are_refused() -> None:
    with tempfile.TemporaryDirectory(prefix="build-manifest-rows-") as raw:
        root = Path(raw)
        recorded_repository(root)
        reader = manifest.WorktreeReader(root)
        payload = manifest.load_manifest(reader)
        payload["builds"]["gamma"] = payload["builds"].pop("beta")
        errors = manifest.manifest_errors(reader, manifest=payload)
        require(len(errors) == 2, errors)
        require(any("'gamma'" in e and "does not register" in e for e in errors), errors)
        require(any("'beta'" in e and "no recorded build" in e for e in errors), errors)
        (root / manifest.MANIFEST_PATH).unlink()
        errors = errors_at(root)
        require(len(errors) == 1 and "is missing" in errors[0], errors)


def test_sync_refuses_a_stale_build_output() -> None:
    """A PDF built, then a rebase that rewrote its TeX: the sync must not record it."""
    with tempfile.TemporaryDirectory(prefix="build-manifest-stale-") as raw:
        root = Path(raw)
        artifacts = recorded_repository(root)
        manifest_before = (root / manifest.MANIFEST_PATH).read_bytes()
        storage_before = (root / "paper/68/alpha.pdf").read_bytes()
        build(root, artifacts[0], "built before the rebase", BASE + 20 * SECOND)
        write(
            root,
            "paper/68/alpha.tex",
            b"\\input{alpha-body}\nalpha\n% rebased\n",
            BASE + 30 * SECOND,
        )
        code, message = sync_now(root)
        require(code == 1, f"a stale build output was accepted: {message}")
        require("older than" in message and "paper/68/alpha.tex" in message, message)
        require(
            (root / manifest.MANIFEST_PATH).read_bytes() == manifest_before,
            "a refused sync rewrote the build manifest",
        )
        require(
            (root / "paper/68/alpha.pdf").read_bytes() == storage_before,
            "a refused sync replaced the published PDF",
        )


def test_sync_rebuilds_one_paper_and_reuses_the_other() -> None:
    with tempfile.TemporaryDirectory(prefix="build-manifest-one-") as raw:
        root = Path(raw)
        artifacts = recorded_repository(root)
        beta_row = manifest.load_manifest(manifest.WorktreeReader(root))["builds"]["beta"]
        write(
            root,
            "paper/68/alpha.tex",
            b"\\input{alpha-body}\nalpha\n% revised\n",
            BASE + 20 * SECOND,
        )
        build(root, artifacts[0], "rebuilt", BASE + 30 * SECOND)
        code, message = sync_now(root)
        require(code == 0, f"one rebuilt paper was not synchronized: {message}")
        require(
            (root / "paper/68/alpha.pdf").read_bytes() == b"%PDF alpha rebuilt\n",
            "the rebuilt PDF was not copied",
        )
        rows = manifest.load_manifest(manifest.WorktreeReader(root))["builds"]
        require(rows["beta"] == beta_row, "the reused paper's recorded build changed")
        restamp(root, artifacts)
        require(errors_at(root) == [], errors_at(root))


def test_stale_leftover_output_of_an_unchanged_paper_is_reused() -> None:
    """A checkout that rewrote identical TeX leaves an old output behind."""
    with tempfile.TemporaryDirectory(prefix="build-manifest-leftover-") as raw:
        root = Path(raw)
        artifacts = recorded_repository(root)
        build(root, artifacts[1], "left over", BASE + 20 * SECOND)
        write(root, "paper/243/beta-body.tex", b"beta body\n", BASE + 30 * SECOND)
        code, message = sync_now(root)
        require(code == 0, f"an unchanged paper was not reused: {message}")
        require(
            (root / "paper/243/beta.pdf").read_bytes() == b"%PDF beta first build\n",
            "a stale leftover output replaced the published PDF",
        )
        require(errors_at(root) == [], errors_at(root))


def test_committed_snapshot_reader_resolves_inputs() -> None:
    """``--git-ref`` reads committed bytes, and absent candidates must not raise."""
    with tempfile.TemporaryDirectory(prefix="build-manifest-git-") as raw:
        root = Path(raw)
        recorded_repository(root)
        identity = ["-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid"]
        for command in (
            ["git", "init", "-q"],
            ["git", "add", "-A"],
            ["git", *identity, "commit", "-q", "-m", "fixture"],
        ):
            subprocess.run(command, cwd=root, check=True, capture_output=True)
        require(
            manifest.manifest_errors(RepositoryReader(root, "HEAD")) == [],
            manifest.manifest_errors(RepositoryReader(root, "HEAD")),
        )
        write(root, "paper/68/alpha-body.tex", b"uncommitted edit\n", BASE + 20 * SECOND)
        require(
            manifest.manifest_errors(RepositoryReader(root, "HEAD")) == [],
            "the committed snapshot read worktree bytes",
        )
        require(len(errors_at(root)) == 1, errors_at(root))


def test_checker_and_pdf_sync_read_the_same_inputs() -> None:
    """Every registered manuscript: the checker's inputs are the sync's inputs."""
    contract = json.loads((ROOT / manifest.CONTRACT_PATH).read_text(encoding="utf-8"))
    reader = manifest.WorktreeReader(ROOT)
    for artifact in contract["artifacts"]:
        checker = sorted(manifest.input_closure(reader, artifact["source_path"]))
        synced = sync.manuscript_input_paths(ROOT, artifact["source_path"])
        require(checker == synced, (artifact["id"], checker, synced))


def test_only_explicitly_retired_build_rows_are_removed() -> None:
    with tempfile.TemporaryDirectory(prefix="build-manifest-retire-") as raw:
        root = Path(raw)
        artifacts = recorded_repository(root)
        contract = {"artifacts": artifacts[:1], "rejected_artifact_ids": ["beta"]}
        (root / manifest.CONTRACT_PATH).write_text(json.dumps(contract))
        prior = manifest.load_manifest(manifest.WorktreeReader(root))
        prior["builds"]["unexpected"] = prior["builds"]["beta"]
        manifest.write_manifest(root, prior)
        refreshed = manifest.record_builds(root, [])
        require("beta" not in refreshed["builds"], "retired paper kept a current build row")
        require("alpha" in refreshed["builds"], "active build was lost")
        require("unexpected" in refreshed["builds"], "unknown build was silently erased")
        manifest.write_manifest(root, refreshed)
        require(any("unexpected" in error for error in errors_at(root)), errors_at(root))


def main() -> int:
    test_fresh_builds_are_recorded()
    test_rebased_source_with_restamped_digests_is_refused()
    test_changed_fragment_or_house_style_is_refused()
    test_replaced_pdf_without_recorded_build_is_refused()
    test_missing_and_unregistered_rows_are_refused()
    test_sync_refuses_a_stale_build_output()
    test_sync_rebuilds_one_paper_and_reuses_the_other()
    test_stale_leftover_output_of_an_unchanged_paper_is_reused()
    test_committed_snapshot_reader_resolves_inputs()
    test_checker_and_pdf_sync_read_the_same_inputs()
    test_only_explicitly_retired_build_rows_are_removed()
    print(
        "test_paper_build_manifest: a rebased source, a changed input and a "
        "hand-copied PDF are refused; the sync records fresh builds, refuses "
        "stale ones, and reuses unchanged papers"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
