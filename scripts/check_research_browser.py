#!/usr/bin/env python3
"""Gate browser access against the published source manifests, for every problem."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def check(root=ROOT):
    errors = []
    def digest(path):
        return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    problem_source = root / 'docs/problem_index_source.json'
    if problem_source.is_file():
        for problem in json.loads(problem_source.read_text())['problems']:
            route = problem.get('research_corpus', {})
            if not route or not (root / route.get('manifest', '__missing__')).is_file():
                errors.append(f"problem {problem['erdos_number']}: missing research corpus route")
    pages = {p.resolve(): p.read_text() for p in (root / 'docs/semantic').glob('BROWSER*.md')}
    for page, body in pages.items():
        for line in body.splitlines():
            if not line.startswith(('- Lean declaration:', '- Ordinary mathematical proof', '- incoming ', '- outgoing ', '- [')):
                continue
            for dest in re.findall(r'\]\(([^)]+)\)', line):
                if '://' in dest:
                    continue
                filename, _, anchor = dest.partition('#')
                target = (page.parent / filename).resolve()
                if not target.is_file():
                    errors.append(f'{page.name}: broken graph/proof link {dest}')
                elif anchor.startswith('node-') and f'id="{anchor}"' not in pages.get(target, ''):
                    errors.append(f'{page.name}: missing graph anchor {dest}')
    for manifest in sorted((root / 'research_corpus').glob('*/CORPUS_MANIFEST.json')):
        doc = json.loads(manifest.read_text())
        frontier = doc.get('browser_frontier', {})
        path = root / frontier.get('path', '__missing__')
        if digest(path) != frontier.get('sha256') or not path.is_file():
            errors.append(f'{manifest.parent.name}: missing or stale browser frontier')
            continue
        text = path.read_text()
        for row in doc['files']:
            source = root / row['public_path']
            if digest(source) != row['published_sha256']:
                errors.append(f"missing or changed exported source: {row['public_path']}")
            if source.name == 'research_packet.json' and source.is_file():
                packet = json.loads(source.read_text())
                for kind in ['exact_results', 'negative_results', 'open_producers']:
                    for result in packet.get(kind, []):
                        statement = result.get('statement', '') if isinstance(result, dict) else str(result)
                        if statement and statement not in text:
                            errors.append(f'{source}: full {kind} statement absent from browser frontier')
        for dest in re.findall(r'^- \[[^\n]*?\]\(([^)]+)\)', text, re.MULTILINE):
            if ':' not in dest and not (path.parent / dest.split('#')[0]).is_file():
                errors.append(f'{path}: missing proof link {dest}')
    return errors

if __name__ == '__main__':
    errors = check()
    for error in errors:
        print(error)
    print(f'Browser research custody: {len(errors)} errors')
    raise SystemExit(bool(errors))
