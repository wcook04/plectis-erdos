#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for clean committed-snapshot release validation."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import json
import os
import stat
import subprocess
import sys
import tempfile
import shutil
import signal
import time
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import check_release_ref


TIMEOUT_SECONDS = 1
# Git clone/checkout and external-disk startup precede the cancellation test.
# Keep their readiness budget separate from the production gate timeout.
FIXTURE_SETUP_TIMEOUT_SECONDS = 30


def require(condition: bool, message: str) -> None:
    """Keep release-ref assurance failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def test_snapshot_command_path_boundary() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        private = root / "private"
        private.mkdir()
        (private / "entry.py").write_text("print('outside')\n", encoding="utf-8")
        commands = root / "commands"
        commands.mkdir()
        (commands / "linked.py").symlink_to(private / "entry.py")
        require(
            not check_release_ref.is_safe_snapshot_file(root, commands / "linked.py"),
            "snapshot command guard accepted a symlinked file",
        )
        (root / "scripts").symlink_to(private, target_is_directory=True)
        require(
            not check_release_ref.is_safe_snapshot_file(
                root, root / "scripts" / "entry.py"
            ),
            "snapshot command guard accepted a symlinked parent directory",
        )


def test_snapshot_clone_isolation_flags_are_pinned() -> None:
    """Share immutable objects without copying the multi-gigabyte object store."""
    with tempfile.TemporaryDirectory() as raw:
        source = Path(raw) / "source"
        source.mkdir()
        git(source, "init", "-q")
        git(source, "config", "user.email", "release-ref-test@example.invalid")
        git(source, "config", "user.name", "Clean ref release test")
        for command in check_release_ref.RELEASE_COMMANDS:
            command_path = source / command[1]
            command_path.parent.mkdir(parents=True, exist_ok=True)
            command_path.write_text(
                "#!/usr/bin/env python3\nprint('fixture')\n",
                encoding="utf-8",
            )
        git(source, "add", ".")
        git(source, "commit", "-qm", "snapshot isolation fixture")
        commit_id = git(source, "rev-parse", "HEAD")

        worktree = Path(raw) / "detached-worktree"
        # Exercise Git under the same public, sanitized environment as snapshots.
        added_worktree = check_release_ref.run(
            ["git", "worktree", "add", "--detach", "--quiet", str(worktree), commit_id],
            cwd=source,
        )
        require(added_worktree.returncode == 0, added_worktree.stderr)
        expected_objects = (source / ".git" / "objects").resolve()
        require(
            Path(git(worktree, "rev-parse", "--absolute-git-dir")).resolve()
            != (source / ".git").resolve(),
            "fixture did not create a separate worktree administrative directory",
        )
        original_run = check_release_ref.run
        for checkout in (source, worktree):
            calls: list[tuple[list[str], Path]] = []

            def recording_run(
                argv: list[str], *, cwd: Path, timeout: int | None = None
            ) -> subprocess.CompletedProcess[str]:
                calls.append((argv, cwd))
                return original_run(argv, cwd=cwd, timeout=timeout)

            with (
                patch.object(check_release_ref, "ROOT", checkout),
                patch.object(check_release_ref, "run", side_effect=recording_run),
                tempfile.TemporaryDirectory(dir=raw) as parent_raw,
            ):
                clone = check_release_ref.prepare_clone(commit_id, Path(parent_raw))
                require(git(clone, "rev-parse", "HEAD") == commit_id, "snapshot commit drifted")
                require(git(clone, "status", "--porcelain") == "", "snapshot is not clean")
                require(
                    original_run(["git", "symbolic-ref", "--quiet", "HEAD"], cwd=clone).returncode == 1,
                    "snapshot checkout was not detached",
                )
                alternates = clone / ".git/objects/info/alternates"
                require(not alternates.is_symlink(), "snapshot alternates file is symlinked")
                require(
                    Path(alternates.read_text(encoding="utf-8").strip()).resolve() == expected_objects,
                    "snapshot did not share the common repository's exact object store",
                )
                require(
                    (clone / "scripts/check_release.py").read_text(encoding="utf-8")
                    == "#!/usr/bin/env python3\nprint('fixture')\n",
                    "snapshot did not materialize committed release commands",
                )

            require(calls, "snapshot preparation did not invoke Git")
            clone_command, clone_cwd = calls[0]
            require(clone_command[:2] == ["git", "clone"], "snapshot did not use git clone")
            require("--shared" in clone_command, "snapshot clone lost shared local mode")
            require(
                "--no-hardlinks" not in clone_command,
                "snapshot clone restored the multi-gigabyte object copy",
            )
            require(
                "--no-checkout" in clone_command,
                "snapshot clone checked out before the requested immutable commit",
            )
            require(clone_cwd == checkout, "snapshot clone used a different source checkout")

        wrong_source = Path(raw) / "wrong-source"
        wrong_source.mkdir()
        git(wrong_source, "init", "-q")
        wrong_objects = (wrong_source / ".git" / "objects").resolve()
        for checkout in (source, worktree):
            for mutation in ("wrong-store", "symlink"):
                checkout_attempts = []
                with tempfile.TemporaryDirectory(dir=raw) as parent_raw:
                    parent = Path(parent_raw)

                    def corrupt_alternates(
                        argv: list[str], *, cwd: Path, timeout: int | None = None
                    ) -> subprocess.CompletedProcess[str]:
                        if argv[:2] == ["git", "checkout"]:
                            checkout_attempts.append(argv)
                        completed = original_run(argv, cwd=cwd, timeout=timeout)
                        if argv[:2] == ["git", "clone"] and completed.returncode == 0:
                            alternates = parent / "repo/.git/objects/info/alternates"
                            if mutation == "wrong-store":
                                alternates.write_text(str(wrong_objects) + "\n", encoding="utf-8")
                            else:
                                stored = parent / "actual-alternates"
                                alternates.rename(stored)
                                alternates.symlink_to(stored)
                        return completed

                    with (
                        patch.object(check_release_ref, "ROOT", checkout),
                        patch.object(check_release_ref, "run", side_effect=corrupt_alternates),
                    ):
                        try:
                            check_release_ref.prepare_clone(commit_id, parent)
                        except check_release_ref.SnapshotError as error:
                            require(
                                "unexpected Git object store" in str(error),
                                f"{mutation} did not fail at the object-store boundary: {error}",
                            )
                        else:
                            raise AssertionError(f"snapshot accepted {mutation} from {checkout.name}")
                    require(not checkout_attempts, f"{mutation} was not rejected before checkout")


def test_receipt_destination_boundary() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        outside = root / "outside"
        outside.mkdir()
        sentinel = outside / "sentinel.txt"
        sentinel.write_text("keep me\n", encoding="utf-8")

        linked_receipt = root / "receipt.json"
        linked_receipt.symlink_to(sentinel)
        try:
            check_release_ref.write_receipt(linked_receipt, {"status": "blocked"})
        except check_release_ref.SnapshotError as error:
            require("symlink" in str(error), str(error))
        else:
            raise AssertionError("receipt writer followed a symlinked destination")
        require(
            sentinel.read_text(encoding="utf-8") == "keep me\n",
            "receipt writer modified the symlink target",
        )

        linked_parent = root / "linked"
        linked_parent.symlink_to(outside, target_is_directory=True)
        try:
            check_release_ref.write_receipt(
                linked_parent / "nested-receipt.json", {"status": "blocked"}
            )
        except check_release_ref.SnapshotError as error:
            require("symlink" in str(error), str(error))
        else:
            raise AssertionError("receipt writer followed a symlinked parent")

        private_tmp = Path("/private/tmp")
        temporary_root = str(private_tmp) if private_tmp.is_dir() else None
        with tempfile.TemporaryDirectory(
            prefix="release-ref-race-", dir=temporary_root
        ) as race_raw:
            raced_receipt = Path(race_raw) / "raced-receipt.json"
            raced_receipt.write_text("placeholder\n", encoding="utf-8")
            original_open = check_release_ref.os.open

            def replace_with_fifo(
                path: Path,
                flags: int,
                mode: int = 0o777,
                *,
                dir_fd: int | None = None,
            ) -> int:
                if dir_fd is not None and Path(path).name == raced_receipt.name:
                    raced_receipt.unlink()
                    os.mkfifo(raced_receipt)
                return original_open(path, flags, mode, dir_fd=dir_fd) if dir_fd is not None else original_open(path, flags, mode)

            with patch.object(
                check_release_ref.os, "open", side_effect=replace_with_fifo
            ):
                try:
                    check_release_ref.write_receipt(
                        raced_receipt, {"status": "blocked"}
                    )
                except check_release_ref.SnapshotError as error:
                    require("safely" in str(error), str(error))
                else:
                    raise AssertionError(
                        "receipt writer opened a final path replaced by a FIFO"
                    )

        private_tmp = Path("/private/tmp")
        temporary_root = str(private_tmp) if private_tmp.is_dir() else None
        with tempfile.TemporaryDirectory(
            prefix="release-ref-parent-race-", dir=temporary_root
        ) as raw:
            root = Path(raw)
            raced_parent = root / "receipt-parent"
            raced_parent.mkdir()
            original_parent = root / "receipt-parent-original"
            outside = root / "outside"
            outside.mkdir()
            sentinel = outside / "sentinel.txt"
            sentinel.write_text("keep me\n", encoding="utf-8")
            raced_receipt = raced_parent / "swapped-receipt.json"
            original_open = check_release_ref.os.open

            def swap_parent(
                path: Path,
                flags: int,
                mode: int = 0o777,
                *,
                dir_fd: int | None = None,
            ) -> int:
                if dir_fd is not None and Path(path).name == raced_receipt.name:
                    raced_parent.rename(original_parent)
                    raced_parent.symlink_to(outside, target_is_directory=True)
                return original_open(path, flags, mode, dir_fd=dir_fd) if dir_fd is not None else original_open(path, flags, mode)

            with patch.object(check_release_ref.os, "open", side_effect=swap_parent):
                check_release_ref.write_receipt(
                    raced_receipt, {"status": "blocked"}
                )
            require(
                not (outside / raced_receipt.name).exists(),
                "receipt writer followed a swapped parent directory",
            )
            require(
                sentinel.read_text(encoding="utf-8") == "keep me\n",
                "parent-swap receipt race modified the outside sentinel",
            )
            require(
                (original_parent / raced_receipt.name).is_file(),
                "receipt writer did not create through the held parent descriptor",
            )


def test_macos_tmp_receipt_alias() -> None:
    """Accept only the root-owned macOS alias while retaining no-follow checks."""
    root_symlink = SimpleNamespace(st_mode=stat.S_IFLNK | 0o777, st_uid=0)
    root_directory = SimpleNamespace(st_mode=stat.S_IFDIR | 0o1777, st_uid=0)
    with (
        patch.object(check_release_ref.sys, "platform", "darwin"),
        patch.object(check_release_ref.os, "lstat", return_value=root_symlink),
        patch.object(check_release_ref.os, "stat", return_value=root_directory),
        patch.object(check_release_ref.os, "readlink", return_value="private/tmp"),
    ):
        normalized = check_release_ref._normalize_trusted_receipt_root_alias(
            Path("/tmp/release-head.json")
        )
        require(
            normalized == Path("/private/tmp/release-head.json"),
            "root-owned macOS /tmp alias was not normalized",
        )

    with (
        patch.object(check_release_ref.sys, "platform", "darwin"),
        patch.object(check_release_ref.os, "lstat", return_value=root_symlink),
        patch.object(check_release_ref.os, "stat", return_value=root_directory),
        patch.object(check_release_ref.os, "readlink", return_value="attacker/tmp"),
    ):
        require(
            check_release_ref._normalize_trusted_receipt_root_alias(
                Path("/tmp/release-head.json")
            )
            == Path("/tmp/release-head.json"),
            "an arbitrary /tmp symlink target was normalized",
        )

    if sys.platform == "darwin" and Path("/tmp").resolve() == Path("/private/tmp"):
        with tempfile.TemporaryDirectory(
            prefix="release-ref-macos-tmp-", dir="/private/tmp"
        ) as raw:
            private_root = Path(raw)
            alias_root = Path("/tmp") / private_root.name
            require(
                check_release_ref.safe_receipt_path(alias_root / "receipt.json")
                == private_root / "receipt.json",
                "live macOS /tmp alias was not normalized",
            )
            outside = private_root / "outside"
            outside.mkdir()
            linked_parent = private_root / "linked"
            linked_parent.symlink_to(outside, target_is_directory=True)
            try:
                check_release_ref.safe_receipt_path(
                    alias_root / "linked" / "receipt.json"
                )
            except check_release_ref.SnapshotError as error:
                require("symlink" in str(error), str(error))
            else:
                raise AssertionError(
                    "macOS /tmp normalization accepted a caller-created symlink"
                )


def test_singleflight_worker_flag_is_accepted() -> None:
    args = check_release_ref.build_parser().parse_args(
        ["--singleflight-worker", "--probe-only", "--ref", "HEAD"]
    )
    require(
        args.singleflight_worker,
        "release-ref parser did not accept the internal single-flight worker flag",
    )


def test_commit_ref_resolution_ends_git_options() -> None:
    """A supplied ref must remain data even when it begins with a dash."""
    resolved_commit = "a" * 40
    completed = subprocess.CompletedProcess(
        ["git"], returncode=0, stdout=f"{resolved_commit}\n", stderr=""
    )
    with patch.object(check_release_ref, "run", return_value=completed) as runner:
        require(
            check_release_ref.resolve_commit("--format=%(refname)") == resolved_commit,
            "ref resolution did not return the requested commit",
        )
    call = runner.call_args
    require(call is not None, "ref resolution did not invoke Git")
    argv = call.args[0]
    require(
        argv[2:4] == ["--verify", "--end-of-options"],
        "ref resolution allowed caller input before Git's option boundary",
    )


def test_release_python_commands_reuse_driver_interpreter() -> None:
    """Clean PATH sanitization must not downgrade the release interpreter."""
    completed = subprocess.CompletedProcess(
        [sys.executable], returncode=0, stdout="", stderr=""
    )
    with patch.object(check_release_ref.singleflight, "run_bounded", return_value=completed) as runner:
        check_release_ref.run(
            ["python3", "scripts/check_release.py"], cwd=Path("/fixture")
        )
    call = runner.call_args
    require(call is not None, "release Python command did not invoke subprocess")
    require(
        call.args[0] == [sys.executable, "scripts/check_release.py"],
        "release wrapper fell back to PATH-selected python3",
    )


def test_release_python_commands_reject_unsupported_driver() -> None:
    """An old outer Python must fail before a misleading clean-clone run."""
    with patch.object(check_release_ref.sys, "version_info", (3, 10)):
        try:
            check_release_ref.run(
                ["python3", "scripts/check_release.py"], cwd=Path("/fixture")
            )
        except check_release_ref.SnapshotError as error:
            require("Python 3.11 or newer" in str(error), str(error))
        else:
            raise AssertionError("unsupported release interpreter was accepted")


def git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def commit_path(root: Path, path: str, message: str) -> str:
    git(root, "add", "--", path)
    git(root, "commit", "-qm", message)
    return git(root, "rev-parse", "HEAD")


def gate_source(*, exit_code: int, summary: str) -> str:
    return (
        "#!/usr/bin/env python3\n"
        f"print({summary!r})\n"
        f"raise SystemExit({exit_code})\n"
    )


def auxiliary_gate_source(*, label: str, exit_code: int) -> str:
    return (
        "#!/usr/bin/env python3\n"
        f"print({label!r})\n"
        f"raise SystemExit({exit_code})\n"
    )


class SnapshotLifecycleTests(unittest.TestCase):
    def make_source(self, root, gate):
        source = root / "source"
        (source / "scripts" / "tests").mkdir(parents=True)
        for name in ("check_release_ref.py", "validation_singleflight.py",
                     "lean_build_share.py", "lean_package_share.py"):
            shutil.copyfile(Path(__file__).resolve().parent.parent / (name), source / "scripts" / name)
        for command in check_release_ref.RELEASE_COMMANDS:
            (source / command[1]).write_text(gate if command[1].endswith("check_release.py") else "print('supplementary')\n")
        git(source, "init", "-q")
        git(source, "config", "user.email", "snapshot@example.invalid")
        git(source, "config", "user.name", "Snapshot lifetime fixture")
        git(source, "add", ".")
        git(source, "commit", "-qm", "tiny owned release fixture")
        return source, git(source, "rev-parse", "HEAD")

    def wait_file(self, path, *, owner=None, deadline=None):
        if deadline is None:
            deadline = time.monotonic() + 8
        while time.monotonic() < deadline:
            if path.exists() and path.read_text().strip():
                return path.read_text().strip()
            if owner is not None and owner.poll() is not None:
                out, err = owner.communicate(timeout=1)
                self.fail(f"fixture owner exited {owner.returncode} before publishing {path}:\n"
                          f"stdout: {out}\nstderr: {err}")
            time.sleep(.02)
        self.fail(f"fixture never published {path}")

    def test_readiness_reports_owner_failure_without_waiting_for_setup_deadline(self):
        owner = SimpleNamespace(poll=lambda: 7, returncode=7,
                                communicate=lambda **_kwargs: ('clone output', 'checkout failed'))
        with tempfile.TemporaryDirectory() as raw:
            with self.assertRaisesRegex(AssertionError, 'owner exited 7.*publishing') as failed:
                self.wait_file(Path(raw) / 'missing', owner=owner,
                               deadline=time.monotonic() + FIXTURE_SETUP_TIMEOUT_SECONDS)
        self.assertIn('clone output', str(failed.exception))
        self.assertIn('checkout failed', str(failed.exception))

    def test_probe_does_not_submit_or_collect_a_release_owner(self):
        with tempfile.TemporaryDirectory() as raw:
            source, commit = self.make_source(Path(raw), "print('probe must not run gate')\n")
            with patch.object(check_release_ref, 'ROOT', source), \
                    patch.object(check_release_ref.singleflight, 'submit') as submit:
                receipt, code = check_release_ref.validate_ref(commit, timeout_seconds=8, probe_only=True)
            self.assertEqual(code, 0)
            self.assertEqual(receipt['mode'], 'probe_only')
            self.assertEqual(receipt['gate_coverage']['started_gate_count'], 0)
            submit.assert_not_called()

    def test_public_observer_pending_does_not_prepare_or_remove_a_snapshot(self):
        sf = check_release_ref.singleflight
        pending = {'state': 'running', 'live': True, 'key': 'a'*64, 'collect_timeout': True}
        with patch.object(check_release_ref, 'resolve_commit', return_value='b'*40), \
                patch.object(check_release_ref, 'dirty_paths', return_value=['caller.txt']), \
                patch.object(sf, 'validator_spec', return_value={'key': 'a'*64}) as spec, \
                patch.object(sf, 'submit', return_value={'key': 'a'*64}), \
                patch.object(sf, 'collect', return_value=(pending, 75)), \
                patch.object(check_release_ref, 'prepare_clone') as clone:
            result, code = check_release_ref.validate_ref('HEAD', timeout_seconds=3, probe_only=False)
        self.assertEqual(code, 75)
        self.assertEqual(result['status'], 'pending')
        self.assertTrue(result['observation_only'])
        self.assertEqual(result['caller_worktree_dirty_paths'], ['caller.txt'])
        self.assertEqual(spec.call_args.kwargs['release_timeout_seconds'], 3)
        clone.assert_not_called()

    def test_terminal_receipt_uses_full_hash_bound_output_not_tail_or_mismatched_cache(self):
        import hashlib
        sf = check_release_ref.singleflight
        with tempfile.TemporaryDirectory() as raw:
            root=Path(raw); key='a'*64; commit='b'*40
            path=root/'artifacts'/key/'stdout.log'; path.parent.mkdir(parents=True)
            result={**check_release_ref.receipt_base('old',commit,[]), 'mode':'release_gate',
                    'status':'passed','gate_exit_code':0,'gate_coverage':check_release_ref.gate_coverage([
                        {'exit_code':0} for _ in check_release_ref.RELEASE_COMMANDS]), 'stdout_tail':'x'*18000}
            payload=json.dumps(result).encode();path.write_bytes(payload)
            terminal={'key':key,'state':'terminal','exit_code':0,'stdout':{'path':f'artifacts/{key}/stdout.log',
                      'sha256':'sha256:'+hashlib.sha256(payload).hexdigest(),'tail':payload[-100:].decode()}}
            with patch.object(check_release_ref, 'resolve_commit', return_value=commit), \
                    patch.object(check_release_ref, 'dirty_paths', return_value=['caller.txt']), \
                    patch.object(sf, 'default_state_root', return_value=root), \
                    patch.object(sf, 'validator_spec', return_value={'key':key}), \
                    patch.object(sf, 'submit', return_value={'key':key}), \
                    patch.object(sf, 'collect', return_value=(terminal,0)):
                actual, code=check_release_ref.validate_ref('HEAD',timeout_seconds=3,probe_only=False)
                self.assertEqual(code,0);self.assertEqual(actual['stdout_tail'],'x'*18000)
                self.assertEqual(actual['caller_worktree_dirty_paths'],['caller.txt'])
                path.write_bytes(payload+b' ')
                with self.assertRaises(check_release_ref.SnapshotError):
                    check_release_ref.validate_ref('HEAD',timeout_seconds=3,probe_only=False)
                path.write_bytes(payload)
                terminal['exit_code']=1
                with patch.object(sf,'collect',return_value=(terminal,1)), self.assertRaises(check_release_ref.SnapshotError):
                    check_release_ref.validate_ref('HEAD',timeout_seconds=3,probe_only=False)

    def test_observer_timeout_keeps_owned_snapshot_live(self):
        import validation_singleflight as sf
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            ready, resume, finished = [root / x for x in ("ready", "resume", "finished")]
            gate = ("import sys,time\nfrom pathlib import Path\n"
                    "assert '--singleflight-worker' in sys.argv\n"
                    f"ready=Path({str(ready)!r}); resume=Path({str(resume)!r}); done=Path({str(finished)!r})\n"
                    "ready.write_text(str(Path.cwd()))\n"
                    "while not resume.exists(): time.sleep(.02)\n"
                    "assert Path('scripts/check_release.py').exists()\n"
                    "done.write_text('snapshot still usable')\n")
            source, commit = self.make_source(root, gate)
            state = root / "cache"
            with patch.object(sf, "ROOT", source), patch.object(sf, "__file__", str(source / "scripts/validation_singleflight.py")):
                spec = sf.validator_spec("release", [], commit, state, release_timeout_seconds=8)
                submitted = sf.submit(spec, state)
                try:
                    snapshot = Path(self.wait_file(ready))
                    observed, code = sf.collect(state, submitted['key'], True, .02, receipt_only=True)
                    self.assertEqual(code, 75)
                    self.assertTrue(observed['collect_timeout'])
                    self.assertTrue(snapshot.is_dir())
                    self.assertTrue(sf.receipt_is_live(observed))
                    resume.write_text('continue')
                    terminal, code = sf.collect(state, submitted['key'], True, 8, receipt_only=True)
                    self.assertEqual(code, 0, terminal)
                    self.assertEqual(self.wait_file(finished), 'snapshot still usable')
                    self.assertFalse(snapshot.exists())
                    self.assertEqual(len(list((state / 'jobs').glob('*.json'))), 1)
                finally:
                    # Exact fixture owner only; never leave a sleeping child on failed assertions.
                    sf.cancel(state, submitted['key'], 'fixture containment', 8)

    def test_worker_runs_five_gates_without_nested_collector_and_preserves_first_failure(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source, commit = self.make_source(root, "import sys\nassert '--singleflight-worker' in sys.argv\nprint('first gate')\nraise SystemExit(7)\n")
            (source / check_release_ref.RELEASE_COMMANDS[2][1]).write_text('raise SystemExit(9)\n')
            git(source, 'add', '.')
            git(source, 'commit', '-qm', 'later independent failure')
            commit = git(source, 'rev-parse', 'HEAD')
            with patch.object(check_release_ref, 'ROOT', source):
                receipt, code = check_release_ref.validate_ref(commit, timeout_seconds=8, probe_only=False, singleflight_worker=True)
            self.assertEqual(code, 7)
            self.assertEqual(receipt['gate_coverage']['completed_gate_count'], 5)
            self.assertEqual([row['exit_code'] for row in receipt['gate_results']], [7,0,9,0,0])
            self.assertEqual(receipt['gate_results'][0]['command'], list(check_release_ref.RELEASE_COMMANDS[0]))

    def test_owner_timeout_stops_new_session_descendant_before_snapshot_cleanup(self):
        self.check_owner_cleanup(signal_owner=False)

    def test_owner_signal_stops_descendant_before_snapshot_cleanup(self):
        self.check_owner_cleanup(signal_owner=True)

    def check_owner_cleanup(self, signal_owner):
        import validation_singleflight as sf
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            ready, child_pid, stopped = [root / x for x in ('ready','pid','stopped')]
            child = ("import signal,time,os\nfrom pathlib import Path\n"
                     f"Path({str(child_pid)!r}).write_text(str(os.getpid()))\n"
                     f"signal.signal(signal.SIGTERM, lambda *a: (Path({str(stopped)!r}).write_text(str(Path.cwd().exists())), exit(0)))\n"
                     "time.sleep(60)\n")
            gate = ("import subprocess,sys,time\nfrom pathlib import Path\n"
                    f"subprocess.Popen([sys.executable,'-c',{child!r}],start_new_session=True)\n"
                    f"Path({str(ready)!r}).write_text(str(Path.cwd()))\n"
                    "time.sleep(60)\n")
            source, commit = self.make_source(root, gate)
            if signal_owner:
                driver = ("import sys; sys.path.insert(0,'scripts'); import check_release_ref as c; "
                          f"c.main()")
                proc = subprocess.Popen([sys.executable, '-c', driver, '--singleflight-worker','--ref',commit,'--timeout-seconds','8'], cwd=source, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                try:
                    # A single setup deadline covers both the cloned gate and
                    # its descendant; signal/cleanup waits below stay unchanged.
                    deadline = time.monotonic() + FIXTURE_SETUP_TIMEOUT_SECONDS
                    snapshot = Path(self.wait_file(ready, owner=proc, deadline=deadline))
                    pid = int(self.wait_file(child_pid, owner=proc, deadline=deadline))
                    proc.send_signal(signal.SIGTERM)
                    out, err = proc.communicate(timeout=10)
                    self.assertEqual(proc.returncode, 128 + signal.SIGTERM, (out,err))
                finally:
                    if proc.poll() is None:
                        sf.kill_process_tree(proc.pid); proc.wait()
            else:
                with patch.object(check_release_ref, 'ROOT', source):
                    receipt, code = check_release_ref.validate_ref(commit, timeout_seconds=1, probe_only=False, singleflight_worker=True)
                snapshot = Path(self.wait_file(ready)); pid = int(self.wait_file(child_pid))
                self.assertEqual(code, 124)
                self.assertEqual(receipt['gate_coverage']['started_gate_count'], 1)
                self.assertEqual(receipt['gate_coverage']['completed_gate_count'], 0)
                self.assertEqual(len(receipt['gate_coverage']['not_run_commands']), 4)
            self.assertEqual(self.wait_file(stopped), 'True')
            self.assertFalse(snapshot.exists())
            deadline = time.monotonic() + 5
            while sf._pid_alive(pid) and time.monotonic() < deadline:
                time.sleep(.05)
            self.assertFalse(sf._pid_alive(pid), f'descendant {pid} survived cleanup')


def main() -> int:
    result = unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(SnapshotLifecycleTests))
    require(result.wasSuccessful(), "snapshot lifecycle regression failed")
    test_snapshot_command_path_boundary()
    test_snapshot_clone_isolation_flags_are_pinned()
    test_receipt_destination_boundary()
    test_macos_tmp_receipt_alias()
    test_singleflight_worker_flag_is_accepted()
    test_commit_ref_resolution_ends_git_options()
    test_release_python_commands_reuse_driver_interpreter()
    test_release_python_commands_reject_unsupported_driver()
    original_root = check_release_ref.ROOT
    try:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            hostile_environment = {
                "GIT_DIR": "/private/wrong-git-dir",
                "GIT_WORK_TREE": "/private/wrong-work-tree",
                "GIT_INDEX_FILE": "/private/wrong-index",
                "GIT_NAMESPACE": "wrong-namespace",
                "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
                "GIT_OBJECT_DIRECTORY": "/private/wrong-objects",
                "GIT_ALTERNATE_OBJECT_DIRECTORIES": "/private/wrong-alternates",
                "GIT_COMMON_DIR": "/private/wrong-common",
                "GIT_CONFIG_GLOBAL": "/private/wrong-gitconfig",
                "GIT_TERMINAL_PROMPT": "1",
                "GIT_ASKPASS": "/private/wrong-askpass",
                "PYTHONHOME": "/private/wrong-python-home",
                "PYTHONPATH": "/private/wrong-python-path",
                "PYTHONOPTIMIZE": "2",
                "PYTHONWARNINGS": "error",
                "PYTHONINSPECT": "1",
                "PYTHONINTMAXSTRDIGITS": "100",
                "PYTHONMALLOC": "malloc",
                "PYTHONPROFILEIMPORTTIME": "1",
                "PYTHONHASHSEED": "random",
                "LC_ALL": "C",
                "LANG": "C",
                "LANGUAGE": "C",
                "PATH": "/private/wrong-bin",
            }
            with patch.dict(os.environ, hostile_environment, clear=False):
                sanitized = check_release_ref.clean_environment()
                require(
                    all(
                        key not in sanitized
                        for key in (
                            "GIT_DIR",
                            "GIT_WORK_TREE",
                            "GIT_INDEX_FILE",
                            "GIT_NAMESPACE",
                            "GIT_REPLACE_REF_BASE",
                            "GIT_OBJECT_DIRECTORY",
                            "GIT_ALTERNATE_OBJECT_DIRECTORIES",
                            "GIT_COMMON_DIR",
                            "PYTHONHOME",
                            "PYTHONPATH",
                            "PYTHONOPTIMIZE",
                            "PYTHONWARNINGS",
                            "PYTHONINSPECT",
                            "PYTHONINTMAXSTRDIGITS",
                            "PYTHONMALLOC",
                            "PYTHONPROFILEIMPORTTIME",
                        )
                    ),
                    "release-ref environment retained inherited selector or Python state",
                )
                require(
                    sanitized["GIT_CONFIG_GLOBAL"] == os.devnull,
                    "release-ref environment did not disable global Git config",
                )
                require(
                    sanitized["GIT_CONFIG_NOSYSTEM"] == "1",
                    "release-ref environment did not disable system Git config",
                )
                require(
                    sanitized["GIT_TERMINAL_PROMPT"] == "0"
                    and sanitized["GIT_ASKPASS"] == "/bin/false",
                    "release-ref environment retained interactive Git controls",
                )
                require(
                    sanitized["PATH"] == os.defpath,
                    "release-ref environment did not pin PATH",
                )
                require(
                    sanitized["LC_ALL"] == "C.UTF-8"
                    and sanitized["LANG"] == "C.UTF-8"
                    and sanitized["LANGUAGE"] == "C.UTF-8",
                    "release-ref environment did not pin locale",
                )
                require(
                    sanitized["PYTHONHASHSEED"] == "0"
                    and sanitized["PYTHONNOUSERSITE"] == "1"
                    and sanitized["PYTHONDONTWRITEBYTECODE"] == "1"
                    and sanitized["PYTHONUTF8"] == "1",
                    "release-ref environment did not pin Python runtime state",
                )
                child = check_release_ref.run(
                    [
                        sys.executable,
                        "-c",
                        "import json, os; print(json.dumps({k: os.environ[k] for k in "
                        "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE', "
                        "'PYTHONPATH', 'PYTHONHOME', 'PYTHONINTMAXSTRDIGITS', "
                        "'PYTHONMALLOC', 'PYTHONPROFILEIMPORTTIME', 'LC_ALL', 'LANG') "
                        "if k in os.environ}))",
                    ],
                    cwd=root,
                )
                require(child.returncode == 0, "sanitized child process failed")
                require(
                    json.loads(child.stdout)
                    == {"LC_ALL": "C.UTF-8", "LANG": "C.UTF-8"},
                    "sanitized child process inherited Git, Python, or locale state",
                )
            git(root, "init", "-q")
            git(root, "config", "user.email", "release-ref-test@example.invalid")
            git(root, "config", "user.name", "Clean ref release test")
            (root / "scripts" / "tests").mkdir(parents=True)
            (root / "caller.txt").write_text("committed\n", encoding="utf-8")
            (root / "scripts" / "check_release.py").write_text(
                gate_source(
                    exit_code=0,
                    summary="check_release: all 17 checks passed for release v-test",
                ),
                encoding="utf-8",
            )
            (root / "scripts" / "tests" / "test_root_import_closure.py").write_text(
                auxiliary_gate_source(
                    label="test_root_import_closure: synthetic root census",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            (root / "scripts" / "tests" / "test_release_source_identity.py").write_text(
                auxiliary_gate_source(
                    label="test_release_source_identity: synthetic source adversary",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            (root / "scripts" / "tests" / "test_query_route_memory.py").write_text(
                auxiliary_gate_source(
                    label="test_query_route_memory: synthetic route-memory adversary",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            (root / "scripts" / "tests" / "test_expert_handoffs.py").write_text(
                auxiliary_gate_source(
                    label="test_expert_handoffs: synthetic source-current handoff",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            git(root, "add", ".")
            git(root, "commit", "-qm", "passing release snapshot")
            passing_commit = git(root, "rev-parse", "HEAD")

            (root / "caller.txt").write_text(
                "uncommitted caller edit\n", encoding="utf-8"
            )
            (root / "untracked.txt").write_text(
                "uncommitted caller file\n", encoding="utf-8"
            )
            check_release_ref.ROOT = root

            probe, probe_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=True,
            )
            require(probe_exit == 0, "probe validation failed")
            require(
                probe["status"] == "clean_snapshot_prepared",
                "probe did not prepare a clean snapshot",
            )
            require(
                probe["resolved_commit"] == passing_commit,
                "probe selected the wrong immutable commit",
            )
            require(
                probe["source_repository"] == check_release_ref.SOURCE_REPOSITORY_LABEL,
                "probe receipt exposed a local checkout path",
            )
            require(
                probe["subprocess_environment"] == {
                    "contract": check_release_ref.ENVIRONMENT_CONTRACT,
                    "sanitized_git_selectors": list(
                        check_release_ref.SANITIZED_GIT_ENVIRONMENT_KEYS
                    ),
                    "sanitized_runtime_variables": list(
                        check_release_ref.SANITIZED_RUNTIME_ENVIRONMENT_KEYS
                    ),
                    "sanitized_runtime_prefixes": list(
                        check_release_ref.SANITIZED_RUNTIME_ENVIRONMENT_PREFIXES
                    ),
                    "canonical_values": {
                        "GIT_CONFIG_GLOBAL": os.devnull,
                        "GIT_CONFIG_NOSYSTEM": "1",
                        "GIT_OPTIONAL_LOCKS": "0",
                        "GIT_NO_REPLACE_OBJECTS": "1",
                        "GIT_PAGER": "cat",
                        "GIT_TERMINAL_PROMPT": "0",
                        "GIT_ASKPASS": "/bin/false",
                        "PATH": os.defpath,
                        "LC_ALL": "C.UTF-8",
                        "LANG": "C.UTF-8",
                        "LANGUAGE": "C.UTF-8",
                        "PYTHONHASHSEED": "0",
                        "PYTHONNOUSERSITE": "1",
                        "PYTHONDONTWRITEBYTECODE": "1",
                        "PYTHONUTF8": "1",
                    },
                },
                "probe omitted the subprocess environment contract",
            )
            require(
                set(probe["caller_worktree_dirty_paths"]) == {
                    "caller.txt",
                    "untracked.txt",
                },
                "probe misreported caller worktree dirt",
            )
            require(
                not probe["caller_worktree_dirty_paths_truncated"],
                "probe unexpectedly truncated caller dirt",
            )
            require(
                probe["gate_coverage"] == {
                    "configured_gate_count": 5,
                    "started_gate_count": 0,
                    "completed_gate_count": 0,
                    "failed_gate_count": 0,
                    "timed_out_gate_count": 0,
                    "all_configured_gates_completed": False,
                    "not_run_commands": probe["release_commands"],
                },
                "probe gate coverage receipt is incomplete",
            )

            many_dirty_paths = [
                f"untracked-{index:03d}.txt"
                for index in range(check_release_ref.DIRTY_PATH_LIMIT + 5)
            ]
            bounded_receipt = check_release_ref.receipt_base(
                "HEAD",
                passing_commit,
                many_dirty_paths,
            )
            require(
                bounded_receipt["caller_worktree_dirty_path_count"]
                == len(many_dirty_paths),
                "bounded receipt lost the complete caller dirt count",
            )
            require(
                len(bounded_receipt["caller_worktree_dirty_paths"])
                == check_release_ref.DIRTY_PATH_LIMIT,
                "bounded receipt exceeded its dirty-path limit",
            )
            require(
                bounded_receipt["caller_worktree_dirty_paths_truncated"],
                "bounded receipt failed to mark truncated caller dirt",
            )

            passed, passed_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=False,
                singleflight_worker=True,
            )
            require(passed_exit == 0, "passing release snapshot failed")
            require(passed["status"] == "passed", "passing snapshot was not passed")
            require(
                passed["reported_check_count"] == 17,
                "passing snapshot lost the reported check count",
            )
            require(
                passed["reported_release"] == "v-test",
                "passing snapshot lost the reported release",
            )
            require(
                "uncommitted caller edit" not in passed["stdout_tail"],
                "caller worktree text leaked into the release receipt",
            )
            require(
                passed["release_commands"] == [
                    ["python3", "scripts/check_release.py"],
                    ["python3", "scripts/tests/test_root_import_closure.py"],
                    ["python3", "scripts/tests/test_release_source_identity.py"],
                    ["python3", "scripts/tests/test_query_route_memory.py"],
                    ["python3", "scripts/tests/test_expert_handoffs.py"],
                ],
                "release command coverage changed unexpectedly",
            )
            require(
                [row["exit_code"] for row in passed["gate_results"]]
                == [0, 0, 0, 0, 0],
                "passing snapshot did not report every gate exit",
            )
            require(
                passed["failed_gate_count"] == 0,
                "passing snapshot reported a failed gate",
            )
            require(
                passed["gate_coverage"] == {
                    "configured_gate_count": 5,
                    "started_gate_count": 5,
                    "completed_gate_count": 5,
                    "failed_gate_count": 0,
                    "timed_out_gate_count": 0,
                    "all_configured_gates_completed": True,
                    "not_run_commands": [],
                },
                "passing snapshot gate coverage receipt is incomplete",
            )

            (root / "scripts" / "tests" / "test_root_import_closure.py").write_text(
                auxiliary_gate_source(
                    label="test_root_import_closure: synthetic root census",
                    exit_code=9,
                ),
                encoding="utf-8",
            )
            root_failure_commit = commit_path(
                root,
                "scripts/tests/test_root_import_closure.py",
                "failing root closure snapshot",
            )
            root_failed, root_failed_exit = check_release_ref.validate_ref(
                root_failure_commit,
                timeout_seconds=30,
                probe_only=False,
                singleflight_worker=True,
            )
            require(root_failed_exit == 9, "root gate failure exit was not preserved")
            require(
                root_failed["status"] == "failed",
                "root gate failure was not reported as failed",
            )
            require(
                [row["exit_code"] for row in root_failed["gate_results"]]
                == [0, 9, 0, 0, 0],
                "root gate failure receipt lost gate exits",
            )
            require(
                root_failed["failed_gate_count"] == 1,
                "root gate failure count is incorrect",
            )
            require(
                root_failed["gate_coverage"]["completed_gate_count"] == 5,
                "root gate failure did not complete the configured gates",
            )
            require(
                root_failed["gate_coverage"]["failed_gate_count"] == 1,
                "root gate failure coverage count is incorrect",
            )
            require(
                root_failed["gate_coverage"]["all_configured_gates_completed"],
                "root gate failure receipt lost completion coverage",
            )
            require(
                "synthetic root census" in root_failed["stdout_tail"],
                "root gate failure receipt lost root-gate output",
            )
            require(
                "synthetic source adversary" in root_failed["stdout_tail"],
                "root gate failure receipt lost later-gate output",
            )

            (root / "scripts" / "tests" / "test_root_import_closure.py").write_text(
                auxiliary_gate_source(
                    label="test_root_import_closure: synthetic root census",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            commit_path(
                root,
                "scripts/tests/test_root_import_closure.py",
                "restore passing root closure",
            )

            (root / "scripts" / "tests" / "test_release_source_identity.py").write_text(
                auxiliary_gate_source(
                    label="test_release_source_identity: synthetic source adversary",
                    exit_code=11,
                ),
                encoding="utf-8",
            )
            source_failure_commit = commit_path(
                root,
                "scripts/tests/test_release_source_identity.py",
                "failing source identity snapshot",
            )
            source_failed, source_failed_exit = check_release_ref.validate_ref(
                source_failure_commit,
                timeout_seconds=30,
                probe_only=False,
                singleflight_worker=True,
            )
            require(
                source_failed_exit == 11,
                "source identity gate exit was not preserved",
            )
            require(
                source_failed["status"] == "failed",
                "source identity gate failure was not reported as failed",
            )
            require(
                [row["exit_code"] for row in source_failed["gate_results"]]
                == [0, 0, 11, 0, 0],
                "source identity gate receipt lost gate exits",
            )
            require(
                source_failed["failed_gate_count"] == 1,
                "source identity gate failure count is incorrect",
            )
            require(
                "synthetic source adversary" in source_failed["stdout_tail"],
                "source identity failure receipt lost gate output",
            )

            (root / "scripts" / "tests" / "test_release_source_identity.py").write_text(
                auxiliary_gate_source(
                    label="test_release_source_identity: synthetic source adversary",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            commit_path(
                root,
                "scripts/tests/test_release_source_identity.py",
                "restore passing source identity",
            )

            (root / "scripts" / "tests" / "test_query_route_memory.py").write_text(
                auxiliary_gate_source(
                    label="test_query_route_memory: synthetic route-memory adversary",
                    exit_code=13,
                ),
                encoding="utf-8",
            )
            route_failed_commit = commit_path(
                root,
                "scripts/tests/test_query_route_memory.py",
                "failing route-memory snapshot",
            )
            route_failed, route_failed_exit = check_release_ref.validate_ref(
                route_failed_commit,
                timeout_seconds=30,
                probe_only=False,
                singleflight_worker=True,
            )
            require(
                route_failed_exit == 13,
                "route-memory gate exit was not preserved",
            )
            require(
                route_failed["status"] == "failed",
                "route-memory gate failure was not reported as failed",
            )
            require(
                [row["exit_code"] for row in route_failed["gate_results"]]
                == [0, 0, 0, 13, 0],
                "route-memory gate receipt lost gate exits",
            )
            require(
                route_failed["failed_gate_count"] == 1,
                "route-memory gate failure count is incorrect",
            )
            require(
                "synthetic route-memory adversary" in route_failed["stdout_tail"],
                "route-memory failure receipt lost gate output",
            )

            (root / "scripts" / "tests" / "test_query_route_memory.py").write_text(
                auxiliary_gate_source(
                    label="test_query_route_memory: synthetic route-memory adversary",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            commit_path(
                root,
                "scripts/tests/test_query_route_memory.py",
                "restore passing route memory",
            )

            (root / "scripts" / "tests" / "test_expert_handoffs.py").write_text(
                auxiliary_gate_source(
                    label="test_expert_handoffs: synthetic source-current handoff",
                    exit_code=17,
                ),
                encoding="utf-8",
            )
            expert_failure_commit = commit_path(
                root,
                "scripts/tests/test_expert_handoffs.py",
                "failing expert handoff snapshot",
            )
            expert_failed, expert_failed_exit = check_release_ref.validate_ref(
                expert_failure_commit,
                timeout_seconds=30,
                probe_only=False,
                singleflight_worker=True,
            )
            require(
                expert_failed_exit == 17,
                "expert-handoff gate exit was not preserved",
            )
            require(
                expert_failed["status"] == "failed",
                "expert-handoff gate failure was not reported as failed",
            )
            require(
                [row["exit_code"] for row in expert_failed["gate_results"]]
                == [0, 0, 0, 0, 17],
                "expert-handoff gate receipt lost gate exits",
            )
            require(
                expert_failed["failed_gate_count"] == 1,
                "expert-handoff gate failure count is incorrect",
            )
            require(
                "synthetic source-current handoff" in expert_failed["stdout_tail"],
                "expert-handoff failure receipt lost gate output",
            )

            (root / "scripts" / "tests" / "test_expert_handoffs.py").write_text(
                auxiliary_gate_source(
                    label="test_expert_handoffs: synthetic source-current handoff",
                    exit_code=0,
                ),
                encoding="utf-8",
            )
            commit_path(
                root,
                "scripts/tests/test_expert_handoffs.py",
                "restore passing expert handoff",
            )

            (root / "scripts" / "check_release.py").write_text(
                gate_source(
                    exit_code=7,
                    summary="check_release: 2 failure(s) across 17 checks",
                ),
                encoding="utf-8",
            )
            failing_commit = commit_path(
                root,
                "scripts/check_release.py",
                "failing release snapshot",
            )

            old_again, old_again_exit = check_release_ref.validate_ref(
                passing_commit,
                timeout_seconds=30,
                probe_only=False,
                singleflight_worker=True,
            )
            require(old_again_exit == 0, "previous passing commit did not replay")
            require(
                old_again["resolved_commit"] == passing_commit,
                "previous passing commit was not selected immutably",
            )
            require(
                old_again["status"] == "passed",
                "previous passing commit lost its passing status",
            )

            failed, failed_exit = check_release_ref.validate_ref(
                failing_commit,
                timeout_seconds=30,
                probe_only=False,
                singleflight_worker=True,
            )
            require(failed_exit == 7, "release gate failure exit was not preserved")
            require(
                failed["status"] == "failed",
                "release gate failure was not reported as failed",
            )
            require(
                failed["resolved_commit"] == failing_commit,
                "release gate failure selected the wrong immutable commit",
            )
            require(
                failed["reported_check_count"] == 17,
                "release gate failure lost the reported check count",
            )
            require(
                failed["reported_release"] is None,
                "failed release gate reported a release value",
            )
            require(
                [row["exit_code"] for row in failed["gate_results"]]
                == [7, 0, 0, 0, 0],
                "release gate failure receipt lost gate exits",
            )
            require(
                failed["failed_gate_count"] == 1,
                "release gate failure count is incorrect",
            )
            require(
                "synthetic root census" in failed["stdout_tail"],
                "release gate failure receipt lost root-gate output",
            )
            require(
                "synthetic source adversary" in failed["stdout_tail"],
                "release gate failure receipt lost later-gate output",
            )

            (root / "scripts" / "check_release.py").write_text(
                "import time\n"
                "print('release gate started', flush=True)\n"
                f"time.sleep({TIMEOUT_SECONDS + 2})\n",
                encoding="utf-8",
            )
            timeout_commit = commit_path(
                root,
                "scripts/check_release.py",
                "timed-out release snapshot",
            )
            timed_out, timeout_exit = check_release_ref.validate_ref(
                timeout_commit,
                timeout_seconds=TIMEOUT_SECONDS,
                probe_only=False,
                singleflight_worker=True,
            )
            require(timeout_exit == 124, "timeout exit was not normalized to 124")
            require(
                timed_out["status"] == "timeout",
                "timed-out release gate was not reported as timeout",
            )
            require(
                timed_out["resolved_commit"] == timeout_commit,
                "timeout receipt selected the wrong immutable commit",
            )
            require(
                timed_out["timeout_seconds"] == TIMEOUT_SECONDS,
                "timeout receipt lost its configured timeout",
            )
            require(
                timed_out["timed_out_command"]
                == ["python3", "scripts/check_release.py"],
                "timeout receipt lost the timed-out command",
            )
            require(
                timed_out["failed_gate_count"] == 0,
                "timeout receipt misclassified the interrupted gate",
            )
            require(
                timed_out["gate_coverage"] == {
                    "configured_gate_count": 5,
                    "started_gate_count": 1,
                    "completed_gate_count": 0,
                    "failed_gate_count": 0,
                    "timed_out_gate_count": 1,
                    "all_configured_gates_completed": False,
                    "not_run_commands": [
                        ["python3", "scripts/tests/test_root_import_closure.py"],
                        ["python3", "scripts/tests/test_release_source_identity.py"],
                        ["python3", "scripts/tests/test_query_route_memory.py"],
                        ["python3", "scripts/tests/test_expert_handoffs.py"],
                    ],
                },
                "timeout receipt gate coverage is incomplete",
            )
            require(
                "release gate started" in timed_out["stdout_tail"],
                "timeout receipt lost gate output",
            )

            try:
                check_release_ref.resolve_commit("missing-ref")
            except check_release_ref.SnapshotError:
                pass
            else:
                raise AssertionError("missing ref was accepted")
    finally:
        check_release_ref.ROOT = original_root

    print(
        "test_check_release_ref: caller dirt excluded, exact commits selected, "
        "dirty paths bounded, root disk census and immutable source adversary "
        "always reported, first failing gate exit preserved, timeout receipt "
        "coverage serialized, and receipt destinations cannot follow symlinks"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
