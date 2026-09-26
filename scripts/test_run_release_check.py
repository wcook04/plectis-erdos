#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Cold release entry must prepare its actual child environment and Lean import."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import run_release_check as release


class ReleasePreparationTests(unittest.TestCase):
    def test_selects_python_312_even_when_invoked_by_newer_python(self) -> None:
        with (
            patch.object(release.sys, "executable", "/python3.14"),
            patch.object(release.shutil, "which", return_value="/python3.12"),
            patch.object(release, "python_version", side_effect=[(3, 14), (3, 12)]),
        ):
            self.assertEqual(release.select_python(), "/python3.12")

    def test_missing_exact_interpreter_stops_before_install(self) -> None:
        with patch.object(release, "python_version", return_value=(3, 14)):
            with self.assertRaisesRegex(release.PreparationError, "Python 3.12"):
                release.select_python("/python3.14")

    def test_pinned_environment_is_reused_and_missing_package_is_installed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            venv = root / ".lake/release-python"
            python = venv / "bin/python"
            python.parent.mkdir(parents=True)
            python.write_text("fixture", encoding="utf-8")
            lock = root / "requirements-release.txt"
            lock.write_text(
                "pypdf==6.17.0 --hash=sha256:" + "a" * 64 + "\n"
                "six==1.17.0 --hash=sha256:" + "b" * 64 + "\n",
                encoding="utf-8",
            )
            pins = {"pypdf": "6.17.0", "six": "1.17.0"}
            with (
                patch.object(release, "VENV", venv),
                patch.object(release, "LOCK", lock),
                patch.object(release, "python_version", return_value=(3, 12)),
                patch.object(release, "installed_packages", return_value=pins),
                patch.object(release, "check_pdf_import"),
                patch.object(release, "run") as runner,
            ):
                self.assertEqual(release.prepare_python("/python3.12"), python)
                runner.assert_not_called()
            with (
                patch.object(release, "VENV", venv),
                patch.object(release, "LOCK", lock),
                patch.object(release, "python_version", return_value=(3, 12)),
                patch.object(release, "installed_packages", side_effect=[
                    {"pypdf": None, "six": "1.17.0"}, pins,
                ]),
                patch.object(release, "check_pdf_import"),
                patch.object(release, "run") as runner,
            ):
                self.assertEqual(release.prepare_python("/python3.12"), python)
                command = runner.call_args.args[0]
                self.assertEqual(command[:4], [str(python), "-m", "pip", "install"])
                self.assertIn("--require-hashes", command)
                self.assertEqual(command[-1], str(lock))

    def test_matching_metadata_cannot_hide_a_broken_pdf_import(self) -> None:
        failed = subprocess.CompletedProcess([], 1, "", "broken PDF import")
        with patch.object(release.subprocess, "run", return_value=failed):
            with self.assertRaisesRegex(release.PreparationError, "broken PDF import"):
                release.check_pdf_import(Path("/venv/python"))

    def test_missing_lean_output_is_not_a_successful_pilot(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with (
                patch.object(release, "PILOT_OLEAN", Path(directory) / "missing.olean"),
                patch.object(release, "run") as runner,
            ):
                with self.assertRaisesRegex(release.PreparationError, "not materialised"):
                    release.prepare_pilot(Path("/python3.12"))
                self.assertIn(release.PILOT_MODULE, runner.call_args.args[0])

    def test_failed_pilot_never_launches_release_gate(self) -> None:
        with (
            patch.object(sys, "argv", ["run_release_check.py"]),
            patch.object(release, "select_python", return_value="/python3.12"),
            patch.object(release, "prepare_python", return_value=Path("/venv/python")),
            patch.object(release, "prepare_pilot", side_effect=release.PreparationError("missing import")),
            patch.object(release.subprocess, "run") as runner,
        ):
            self.assertEqual(release.main(), 2)
            runner.assert_not_called()

    def test_release_gate_uses_prepared_python(self) -> None:
        with (
            patch.object(sys, "argv", ["run_release_check.py"]),
            patch.object(release, "select_python", return_value="/python3.12"),
            patch.object(release, "prepare_python", return_value=Path("/venv/python")),
            patch.object(release, "prepare_pilot"),
            patch.object(release.subprocess, "run", return_value=subprocess.CompletedProcess([], 0)) as runner,
        ):
            self.assertEqual(release.main(), 0)
            self.assertEqual(runner.call_args.args[0], ["/venv/python", "scripts/check_release.py"])


if __name__ == "__main__":
    unittest.main()
