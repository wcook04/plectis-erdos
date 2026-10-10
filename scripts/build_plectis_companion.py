#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build a small directory-based Agent Skill archive, not a client plugin.

Preview is the default. --apply creates a new archive and refuses overwrite.
"""
from __future__ import annotations
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SKILL = ROOT / '.agents/skills/plectis-frontier'
FILES = ('LICENSE.txt', 'SKILL.md', 'scripts/bootstrap.py', 'source.json')


def package(source: Path = SKILL) -> tuple[bytes, dict]:
    contents = {}
    for name in FILES:
        path = source / name
        if source.is_symlink() or any((source.joinpath(*Path(name).parts[:i])).is_symlink() for i in range(1, len(Path(name).parts) + 1)):
            raise ValueError(f'symlinked package source: {name}')
        contents[name] = path.read_bytes()
    version = re.search(r'^  version: "([0-9]+\.[0-9]+\.[0-9]+)"$', contents['SKILL.md'].decode(), re.M)
    if not version:
        raise ValueError('companion version missing')
    research = json.loads(contents['source.json'])
    if not re.fullmatch('[0-9a-f]{40}', research.get('commit', '')):
        raise ValueError('research revision must be pinned')
    manifest = {'schema': 'plectis-companion-package/1', 'name': 'plectis-frontier',
                'companion_version': version[1], 'research_source': research,
                'format': 'directory-agent-skill-not-plugin',
                'files': {name: hashlib.sha256(data).hexdigest() for name, data in contents.items()}}
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
        for name, data in contents.items():
            info = zipfile.ZipInfo('plectis-frontier/' + name, (1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
        info = zipfile.ZipInfo('plectis-frontier/package.json', (1980, 1, 1, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o100644 << 16
        archive.writestr(info, json.dumps(manifest, sort_keys=True, indent=2) + '\n')
    data = buffer.getvalue()
    if len(data) > 32768:
        raise ValueError('companion archive exceeds 32 KiB')
    return data, manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path,
                        help='new archive path inside an existing directory')
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    try:
        data, manifest = package()
        if args.output.exists() or args.output.is_symlink():
            raise ValueError('output already exists; choose a new archive path')
        if not args.output.parent.is_dir():
            raise ValueError(
                f'output parent is not an existing directory: {args.output.parent}; '
                'create it first or choose an existing output directory'
            )
        if args.apply:
            with args.output.open('xb') as stream:
                stream.write(data)
        print(json.dumps({'status': 'built' if args.apply else 'preview-only',
                          'output': str(args.output.absolute()), 'bytes': len(data),
                          'sha256': hashlib.sha256(data).hexdigest(), 'manifest': manifest}, indent=2))
        return 0
    except (OSError, ValueError) as exc:
        parser.exit(2, f'error: {exc}\n')


if __name__ == '__main__':
    raise SystemExit(main())
