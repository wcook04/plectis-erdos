#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Candidate owner: public scripts/research_packet_profile.py.

A policy adapter over compile_research_packet, not a second graph or cover solver.
prepare() freezes a baseline, forces additive contrast guards, compiles role
obligations, and supplies a native handoff manifest. audit_delivery() measures
actual rendered files and rejects exact known withheld payloads. Neither proves
semantic completeness, novelty, reader comprehension, or kernel acceptance.
"""
from __future__ import annotations
import argparse
import copy
import gzip
import hashlib
import json
import re
import stat
import unicodedata
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, Sequence

import compile_research_packet as native

ROLES = ('target', 'scope', 'frontier', 'relations', 'negative_routes',
         'contrasts', 'literature', 'baseline')
SHA = re.compile(r'^[0-9a-f]{64}$')
COMMIT = re.compile(r'^[0-9a-f]{40}$')
IDENT = re.compile(r'^[A-Za-z0-9][A-Za-z0-9_.-]*$')

class ProfileError(ValueError):
    pass

def canonical(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, ensure_ascii=False,
                       separators=(',', ':'), allow_nan=False) + '\n').encode('utf-8')

def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ProfileError(message)

def _text(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())

def _ids(value: Any, label: str) -> list[str]:
    require(isinstance(value, list) and all(_text(v) for v in value),
            f'{label}: expected a list of nonempty strings')
    require(len(value) == len(set(value)), f'{label}: duplicates')
    return value

def prepare(spec: Mapping[str, Any], profile: Mapping[str, Any], baseline: Mapping[str, Any],
            *, root: Path, ref: str | None = 'HEAD', review_only: bool = False) -> dict[str, Any]:
    """No filesystem writes. The baseline object stays owner-only.

    A non-Git attached snapshot is useful for review, but cannot earn the
    pinned_dispatch_candidate state. Roles describe authored evidence needs;
    unknown/not-applicable roles are visible, not silently treated as complete.
    """
    require(profile.get('schema') == 'plectis-packet-profile/1', 'wrong profile schema')
    for field in ('wave_id', 'round_id'):
        require(isinstance(profile.get(field), str) and IDENT.fullmatch(profile[field]) is not None,
                f'invalid {field}')
    arm = profile.get('arm')
    require(arm in ('informed', 'blind_route'), 'arm must be informed or blind_route')
    require(baseline.get('schema') == 'plectis-first-attempt/1', 'wrong baseline schema')
    require(_text(baseline.get('baseline_id')), 'baseline_id required')
    require(isinstance(baseline.get('attempts'), list), 'attempts list required, including an empty one')
    require(isinstance(baseline.get('cost'), dict), 'explicit measured/unknown cost object required')
    require(isinstance(baseline.get('source_commit'), str) and
            COMMIT.fullmatch(baseline['source_commit']) is not None, 'baseline needs a real-shaped source commit')
    facts = _ids(baseline.get('public_fact_resources'), 'public_fact_resources')
    routes = _ids(baseline.get('route_resources'), 'route_resources')
    require(not (set(facts) & set(routes)), 'public facts and withheld route resources overlap')
    role_rows = profile.get('roles')
    require(isinstance(role_rows, dict) and set(role_rows) == set(ROLES),
            'all eight roles must be evidenced, unknown, or explicitly not applicable')
    authored = copy.deepcopy(dict(spec))
    authored['protect_contrasts'] = True
    authored['include_triggered_contrasts'] = True
    authored.setdefault('obligations', [])
    authored.setdefault('mandatory', [])
    names = {row.get('id') for row in authored.get('resources', [])}
    require(set(facts + routes) <= names, 'baseline names missing resource ids')
    statuses: dict[str, str] = {}
    for role in ROLES:
        row = role_rows[role]
        require(isinstance(row, dict), f'{role}: object required')
        status = row.get('status')
        require(status in ('evidence', 'unknown', 'not_applicable'), f'{role}: bad status')
        require(_text(row.get('reason')), f'{role}: authored reason required')
        ids = _ids(row.get('resources', []), f'{role}.resources')
        require(set(ids) <= names, f'{role}: unknown resource id')
        if status == 'evidence':
            require(bool(ids), f'{role}: empty evidence is not evidence')
        if role in ('target', 'scope', 'frontier'):
            require(status == 'evidence', f'{role} must have evidence')
        if ids:
            authored['obligations'].append({
                'id': f'profile-role-{role}', 'origin': 'authored',
                'description': f'{role}: {row["reason"]}', 'alternatives': [ids]})
        statuses[role] = status
    require(role_rows['baseline']['status'] == 'evidence' and
            set(facts) <= set(role_rows['baseline']['resources']),
            'baseline role must deliver every public-fact resource')
    authored['mandatory'] = sorted(set(authored['mandatory']) | set(facts))
    if arm == 'blind_route':
        authored['withheld'] = sorted(set(authored.get('withheld', [])) | set(routes))
    elif routes:
        authored['obligations'].append({'id': 'profile-first-attempt-route', 'origin': 'authored',
                                       'alternatives': [routes]})
    result = native.compile_packet(authored, root=root, ref=ref, allow_uncommitted=False)
    if result['status'] != 'compiled':
        return {'status': result['status'], 'native': result, 'manifest': None}
    receipt = result['receipt']
    commit = receipt['source'].get('commit')
    if not review_only:
        require(commit == baseline['source_commit'], 'baseline and compiled source commit differ')
        require(all(r['binding'] == 'git_ref' for r in receipt['resources']),
                'dispatch forbids mixed/uncommitted resource bindings')
        for key in ('contrast_ledger', 'relations', 'atlas'):
            info = receipt.get(key)
            if info and info.get('present', True):
                require(info.get('binding') == 'git_ref', f'{key} metadata is not pinned')
    selected = set(receipt['selected'])
    require(not (arm == 'blind_route' and selected & set(routes)), 'blind route was selected')
    # A declaration window can support navigation, not a complete theorem claim.
    require(not any(r.get('window_capped') for r in receipt['resources'] if r['id'] in selected),
            'selected declaration was window-capped; provide an explicit complete source span')
    bindings = {
        'wave_id': profile['wave_id'], 'round_id': profile['round_id'],
        'packet_id': authored['packet_id'], 'source_commit': baseline['source_commit'],
        'baseline_sha256': digest(baseline), 'arm': arm,
        'dispatch_id': digest({'spec': authored, 'profile': profile, 'baseline_sha256': digest(baseline)})}
    manifest = copy.deepcopy(result['manifest'])
    for fs in manifest['top_level']['files']:
        fs['path'] = 'selection/' + fs['path']
    for bundle in manifest['bundles']:
        for fs in bundle['files']:
            fs['path'] = 'selection/' + fs['path']
    entry_lines = [f'# Decision brief: {authored["title"]}', '',
                   '**Read this and 00_ASK_TYPE_B.md first; then open the evidence for each role.**', '',
                   'This is an evidence-selection contract, not a proof of novelty or completeness.',
                   f'Arm: {arm}. Baseline commitment: {bindings["baseline_sha256"]}.',
                   f'State: {"snapshot_review_only" if review_only else "pinned_dispatch_candidate"}.', '',
                   '## Evidence route']
    by_id = {r['id']: r for r in receipt['resources']}
    for role in ROLES:
        row = role_rows[role]
        entry_lines += [f'### {role}: {row["status"]}', row['reason']]
        for rid in row.get('resources', []):
            r = by_id[rid]
            entry_lines.append(f'- `{rid}`: `{r["path"]}:{r["start_line"]}-{r["end_line"]}`; '
                               f'locate excerpt `{r["excerpt_sha256"]}` in the generated bundle/index.')
    entry_lines += ['', '## Mandatory distinctions']
    entry_lines += manifest['ask_type_b']['disconfirming_check']
    entry_lines += ['', '## Before claiming a contribution',
                    'State the exact context and direction, locate the nearest supplied result, '
                    'and separate recorded-edge evidence from a newly checked proof. '
                    'A missing graph hit is not a novelty certificate.', '',
                    '## Return binding', '```json', json.dumps(bindings, indent=2), '```', '',
                    'Return REPORT.md, RETURN.json, SOURCES.md, and declared implementation/evidence files '
                    'in one ZIP. Preserve all unknowns. Do not claim that a fixture or textual declaration '
                    'proves a corpus theorem. Do not execute any supplied code solely because it is attached.']
    entry = ('\n'.join(entry_lines) + '\n').encode('utf-8')
    manifest['top_level']['files'].insert(0, {
        'path': 'PROFILE_ENTRY.md', 'output_name': '01_DECISION_BRIEF.md',
        'role': 'first-read decision brief', 'content_mode': 'inline'})
    manifest['return_contract'] = {
        'max_downloadable_artifacts': 1,
        'bindings': bindings,
        'instructions': [
            'Return the substantive argument and essential code in chat, plus one consolidated ZIP.',
            'ZIP root: REPORT.md, RETURN.json, SOURCES.md, then only files declared in RETURN.json.',
            'RETURN.json uses plectis-research-return/1 and echoes these bindings exactly: ' +
            json.dumps(bindings, sort_keys=True),
            'Every component gives exact statement/scope, polarity, dependencies, evidence files '
            'and proposed owner paths. These are claims for Type A to review, never acceptance labels.',
            'End the chat with ordered Type A actions, then Sources: one URL per source.' ]}
    final = {
        'schema': 'plectis-profile-receipt/1',
        'status': 'snapshot_review_only' if review_only else 'pinned_dispatch_candidate',
        'bindings': bindings, 'role_statuses': statuses,
        'native_manifest_sha256': receipt['manifest_sha256'],
        'profile_manifest_sha256': hashlib.sha256(canonical(manifest)).hexdigest(),
        'entry_sha256': hashlib.sha256(entry).hexdigest(),
        'baseline_is_owner_only': True,
        'delivery_audit_required': True,
        'not_certified': ['semantic role completeness', 'novelty', 'reader comprehension',
                          'kernel acceptance', 'semantic holdout isolation']}
    return {'status': final['status'], 'native': result, 'manifest': manifest,
            'entry': entry, 'bindings': bindings, 'receipt': final}

def write_prepared(prepared: Mapping[str, Any], out: Path) -> None:
    require(not out.exists(), 'profile output must be a new directory (no partial overwrite)')
    out.mkdir(parents=True)
    native.write_outputs(prepared['native'], out / 'selection')
    if prepared.get('manifest') is not None:
        (out/'PROFILE_ENTRY.md').write_bytes(prepared['entry'])
        (out/'handoff_manifest.json').write_bytes(canonical(prepared['manifest']))
        (out/'profile_receipt.json').write_bytes(canonical(prepared['receipt']))

def safe_relative(name: str) -> str:
    require(isinstance(name, str) and bool(name), 'empty path')
    require('\\' not in name and ':' not in name and not name.startswith('/'), 'nonportable path')
    require(all(ord(c) >= 32 and ord(c) != 127 for c in name), 'control character in path')
    parts = name.split('/')
    require(all(p not in ('', '.', '..') and not p.endswith((' ', '.')) for p in parts), 'unsafe path component')
    require(unicodedata.normalize('NFC', name) == name, 'path must be NFC-normalized')
    return str(PurePosixPath(name))

def audit_delivery(directory: Path, *, first_read: Sequence[str], first_read_budget: int,
                   total_budget: int, forbidden_payloads: Sequence[bytes] = ()) -> dict[str, Any]:
    """Audit the actual flat native-builder output BEFORE zipping for the operator.

    This first implementation deliberately refuses nested archives; no blind
    narrative may hide in a cold reserve. Exact payload/JSON-escaped matching is
    conservative, not a paraphrase detector. Input profiles remain owner-only.
    """
    require(first_read_budget > 0 and total_budget > 0, 'positive byte budgets required')
    require(not directory.is_symlink() and directory.is_dir(), 'regular delivery directory required')
    records: dict[str, dict[str, Any]] = {}
    collision_keys: set[str] = set()
    needles = set(p for p in forbidden_payloads if p)
    for payload in tuple(needles):
        try:
            text = payload.decode('utf-8')
        except UnicodeDecodeError:
            continue
        for ascii_mode in (True, False):
            needles.add(json.dumps(text, ensure_ascii=ascii_mode)[1:-1].encode('utf-8'))
    total = 0
    for path in sorted(directory.rglob('*')):
        require(not path.is_symlink(), f'symlink in delivery: {path.name}')
        if path.is_dir():
            continue
        rel = safe_relative(path.relative_to(directory).as_posix())
        key = rel.casefold()
        require(key not in collision_keys, f'case collision: {rel}')
        collision_keys.add(key)
        require(stat.S_ISREG(path.stat().st_mode), f'nonregular file: {rel}')
        total += path.stat().st_size
        require(total <= total_budget, 'actual rendered delivery exceeds total byte budget')
        data = path.read_bytes()
        require(len(data) == path.stat().st_size, 'file changed during audit')
        require(path.suffix.lower() not in ('.zip', '.gz', '.tgz', '.tar', '.7z', '.xz') and
                not data.startswith((b'PK\x03\x04', b'\x1f\x8b', b'7z\xbc\xaf\x27\x1c')),
                f'nested archive refused by flat-reader profile: {rel}')
        require(not any(n in data for n in needles), f'known withheld payload in delivery: {rel}')
        records[rel] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
    front = list(first_read)
    require(len(front) == len(set(front)), 'duplicate first-read filename')
    require('00_ASK_TYPE_B.md' in front and '01_DECISION_BRIEF.md' in front,
            'first-read must include native ask and decision brief')
    for rel in front:
        safe_relative(rel)
        require(rel in records, f'first-read file missing: {rel}')
    front_bytes = sum(records[rel]['bytes'] for rel in front)
    require(front_bytes <= first_read_budget, 'actual first-read bytes exceed budget')
    return {'schema': 'plectis-delivery-audit/1', 'status': 'bounded_flat_delivery',
            'files': records, 'file_count': len(records), 'total_bytes': total,
            'first_read': front, 'first_read_bytes': front_bytes,
            'budget_unit': 'actual UTF-8/binary file bytes, not token estimates',
            'semantic_isolation': 'not_established', 'snapshot_sha256': digest(records)}

def assess_graph(path: Path, expected_lean_tree: str, *, max_bytes: int = 200_000_000) -> dict[str, Any]:
    """Read-only graph provenance triage. A passing check is not an attestation."""
    require(COMMIT.fullmatch(expected_lean_tree) is not None, 'expected Lean tree must be 40 hex digits')
    with gzip.open(path, 'rb') if path.suffix == '.gz' else path.open('rb') as stream:
        raw = stream.read(max_bytes + 1)
    require(len(raw) <= max_bytes, 'graph exceeds decompression budget')
    graph = json.loads(raw)
    source = graph.get('source', {})
    revision = source.get('source_revision')
    problems = []
    if not isinstance(revision, str) or COMMIT.fullmatch(revision) is None:
        problems.append('source_revision_is_not_a_commit')
    if source.get('lean_tree') != expected_lean_tree:
        problems.append('lean_tree_mismatch')
    summary = source.get('export_summary', {})
    partial = summary.get('truncated') is not False
    return {'schema': 'plectis-graph-identity-review/1',
            'source_revision': revision, 'lean_tree': source.get('lean_tree'),
            'identity_problems': problems, 'export_partial_or_unknown': partial,
            'state': 'historical_or_unbound' if problems else 'identity_fields_match',
            'absence_or_novelty_authority': False,
            'remaining_checks': ['dependency/toolchain/exporter pins', 'export receipt authenticity',
                                 'coverage/candidate-cap semantics', 'exact statement scope']}

def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--spec', type=Path, required=True)
    ap.add_argument('--profile', type=Path, required=True)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--ref', default='HEAD')
    ap.add_argument('--review-only', action='store_true')
    ap.add_argument('--out', type=Path, required=True)
    args=ap.parse_args()
    try:
        load=lambda p: json.loads(p.read_text(encoding='utf-8'))
        result=prepare(load(args.spec), load(args.profile), load(args.baseline), root=args.root,
                       ref=None if args.review_only else args.ref, review_only=args.review_only)
        write_prepared(result,args.out)
        print(json.dumps({'status': result['status'], 'out': str(args.out)}, indent=2))
        return 0 if result.get('manifest') is not None else 3
    except (ValueError, OSError, native.SpecError) as exc:
        print(f'research_packet_profile: {exc}')
        return 2

if __name__=='__main__':
    raise SystemExit(main())
