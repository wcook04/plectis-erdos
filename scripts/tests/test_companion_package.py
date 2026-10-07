#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise portable package and installation outside the repository."""

import _test_bootstrap  # noqa: F401
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
import zipfile
import build_plectis_companion as builder
import install_agent_skills as installer


class PackageTests(unittest.TestCase):
    def test_reproducible_extract_and_describe(self):
        data, manifest = builder.package()
        self.assertEqual(data, builder.package()[0])
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                self.assertEqual(set(archive.namelist()), {'plectis-frontier/' + p for p in (*builder.FILES, 'package.json')})
                archive.extractall(root)
            for name, digest in manifest['files'].items():
                self.assertEqual(hashlib.sha256((root / 'plectis-frontier' / name).read_bytes()).hexdigest(), digest)
            result = subprocess.run([sys.executable, str(root / 'plectis-frontier/scripts/bootstrap.py'), 'describe'], cwd=root, capture_output=True, text=True, check=True)
            self.assertEqual(json.loads(result.stdout)['source']['commit'], manifest['research_source']['commit'])

    def test_preview_conflict_and_removal(self):
        with tempfile.TemporaryDirectory() as temp:
            target = Path(temp) / 'skills'
            cmd = [sys.executable, str(builder.ROOT / 'scripts/install_agent_skills.py'), '--companion', '--target-dir', str(target)]
            subprocess.run(cmd, check=True, capture_output=True)
            self.assertFalse(target.exists())
            subprocess.run(cmd + ['--apply'], check=True, capture_output=True)
            subprocess.run(cmd + ['--check'], check=True, capture_output=True)
            user = target / 'plectis-frontier/SKILL.md'
            user.write_text('user changes')
            self.assertEqual(subprocess.run(cmd + ['--apply'], capture_output=True).returncode, 1)
            self.assertEqual(user.read_text(), 'user changes')
            # Removing the sole new namespace rolls back installation only.
            import shutil
            shutil.rmtree(target / 'plectis-frontier')
            self.assertEqual(list(target.iterdir()), [])

    def test_client_targets(self):
        with tempfile.TemporaryDirectory() as temp, mock.patch.object(Path, 'home', return_value=Path(temp)), mock.patch.dict(os.environ, {'CODEX_HOME': temp + '/legacy', 'CLAUDE_CONFIG_DIR': temp + '/claude'}):
            def target(name):
                return installer.target_directory(argparse.Namespace(target=name, target_dir=None))
            self.assertEqual(target('codex'), Path(temp).resolve() / '.agents/skills')
            self.assertEqual(target('codex-legacy'), Path(temp).resolve() / 'legacy/skills')
            self.assertEqual(target('claude'), Path(temp).resolve() / 'claude/skills')

    def test_builder_preview_and_existing_refusal(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'companion.zip'
            cmd = [sys.executable, str(builder.ROOT / 'scripts/build_plectis_companion.py'), '--output', str(path)]
            subprocess.run(cmd, check=True, capture_output=True)
            self.assertFalse(path.exists())
            subprocess.run(cmd + ['--apply'], check=True, capture_output=True)
            before = path.read_bytes()
            self.assertEqual(subprocess.run(cmd + ['--apply'], capture_output=True).returncode, 2)
            self.assertEqual(path.read_bytes(), before)


if __name__ == '__main__':
    unittest.main(verbosity=2)
