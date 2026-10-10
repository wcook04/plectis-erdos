#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise portable package and installation outside the repository."""
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

    def test_builder_missing_parent_is_actionable_and_creates_nothing(self):
        with tempfile.TemporaryDirectory() as temp:
            parent = Path(temp) / 'new directory'
            output = parent / 'companion.zip'
            cmd = [sys.executable, str(builder.ROOT / 'scripts/build_plectis_companion.py'),
                   '--output', str(output)]
            for flags in ([], ['--apply']):
                result = subprocess.run(cmd + flags, capture_output=True, text=True)
                self.assertEqual(result.returncode, 2)
                self.assertIn('create it first or choose an existing output directory', result.stderr)
                self.assertFalse(parent.exists())
            # The stated recovery allows the same command to succeed.
            parent.mkdir()
            preview = subprocess.run(cmd, check=True, capture_output=True, text=True)
            self.assertEqual(json.loads(preview.stdout)['status'], 'preview-only')
            self.assertFalse(output.exists())
            subprocess.run(cmd + ['--apply'], check=True, capture_output=True)
            self.assertEqual(output.read_bytes(), builder.package()[0])

    def test_builder_file_parent_has_the_same_actionable_refusal(self):
        with tempfile.TemporaryDirectory() as temp:
            parent = Path(temp) / 'keep.txt'
            parent.write_text('existing user material')
            cmd = [sys.executable, str(builder.ROOT / 'scripts/build_plectis_companion.py'),
                   '--output', str(parent / 'companion.zip'), '--apply']
            result = subprocess.run(cmd, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn('create it first or choose an existing output directory', result.stderr)
            self.assertEqual(parent.read_text(), 'existing user material')

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
