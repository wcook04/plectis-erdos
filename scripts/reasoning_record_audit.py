#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Short/long navigation over native paper evidence, with explicit review gaps.

This is a structural audit, not a theorem prover or an ordinary-proof review.
Uses the native assertion inventory, evidence marks and authored part manifest.
Only exact complete declaration-set matches are automatic. Label/text similarity
is a suggestion, never accepted correspondence. Explicit authored links are
bound to both statement digests and an independently located support span.
All reads are local. No model, network, Lean, or TeX execution occurs here.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import difflib
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any

import check_lean_paper_propagation as coverage
from assemble_reasoning_surfaces import PAPERS
from lean_source import qualified_declaration_lines, lean_code_without_comments_and_strings

ROOT = Path(__file__).resolve().parents[1]
LINKS = 'paper/reasoning-parts/record_links.json'
REPORT = 'docs/reading-edition/record_audit.json'
SCHEMA = 'plectis-long-record-audit/1'
LINK_SCHEMA = 'plectis-short-long-links/1'
BOUNDARY = ('Checks registered asserting environments and registered claim spans. '
            'Unregistered prose assertions, mathematical equivalence, correctness of '
            'ordinary proofs, Lean compilation, Comparator replay and PDF freshness '
            'are not established by this audit.')


class RecordInputError(ValueError):
    pass


def digest(data: str | bytes) -> str:
    return 'sha256:' + hashlib.sha256(data.encode() if isinstance(data, str) else data).hexdigest()


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n'


def safe_path(root: Path, relative: str) -> Path:
    if not isinstance(relative, str) or not relative or '\\' in relative:
        raise RecordInputError(f'invalid local path: {relative!r}')
    part = PurePosixPath(relative)
    if (part.is_absolute() or '..' in part.parts or '.git' in part.parts
            or str(part) != relative or any(ord(c) < 32 for c in relative)):
        raise RecordInputError(f'invalid local path: {relative!r}')
    path = root
    for piece in part.parts:
        path = path / piece
        if path.is_symlink():
            raise RecordInputError(f'symlink in local path: {relative}')
    return path


class Inputs:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.texts: dict[str, str] = {}
        self.hashes: dict[str, str] = {}

    def read(self, relative: str) -> str:
        if relative not in self.texts:
            raw = safe_path(self.root, relative).read_bytes()
            self.hashes[relative] = digest(raw)
            self.texts[relative] = raw.decode('utf-8')
        return self.texts[relative]

    def json(self, relative: str) -> Any:
        return json.loads(self.read(relative))


def locator(path: str, start: int, end: int | None = None, label: str | None = None) -> dict:
    return {'path': path, 'line': start, 'end_line': end or start, 'label': label}


def normalized(text: str) -> str:
    """Conservative duplicate key; preserve numbers, quantifiers and math tokens."""
    text = coverage.counter_view(text)
    text = re.sub(r'\\label\{[^{}]+\}', '', text)
    # Label names differ between short and long editions; no other rewriting.
    return re.sub(r'\s+', ' ', text).strip()


def statement_text(loc: coverage.Located, source: str, *, counter_lines: list[str] | None = None) -> str:
    lines = coverage.counter_view(source).splitlines() if counter_lines is None else counter_lines
    text = '\n'.join(lines[loc.line - 1:loc.end_line])
    env = loc.row.get('environment')
    if env:
        begin, end = '\\begin{' + env + '}', '\\end{' + env + '}'
        if begin not in text or end not in text:
            raise RecordInputError(f'cannot recover assertion {loc.row["id"]}')
        text = text.split(begin, 1)[1].split(end, 1)[0]
    return text


def declaration_set(row: dict) -> frozenset:
    return frozenset((d['file'], d['name']) for d in coverage.declarations_of(row))


def label_key(label: str) -> str:
    return re.sub(r'^long\d+:', '', label).removesuffix('-long')


def support_span(inputs: Inputs, spec: dict, *, short_path: str | None = None) -> tuple[dict, str]:
    """Select exact closed proof or exact bounded authored text. Never use line-only pins."""
    path = spec['path']
    if short_path is not None and path != short_path:
        raise RecordInputError('short proof support belongs to another source')
    if short_path is None and not path.startswith('paper/reasoning-parts/'):
        raise RecordInputError('support span must be in authored reasoning parts')
    text = coverage.counter_view(inputs.read(path))
    mode = spec['selector']
    if mode == 'proof_of':
        label = spec['label']
        blocks = []
        for m in re.finditer(r'\\begin\{proof\}(\[[^\n]*?\])?', text):
            finish = text.find(r'\end{proof}', m.end())
            if finish < 0:
                continue
            if '\\ref{' + label + '}' in (m.group(1) or ''):
                blocks.append((m.start(), finish + len(r'\end{proof}')))
        if len(blocks) != 1:
            raise RecordInputError(f'proof_of {label}: expected one closed proof, got {len(blocks)}')
        start, end = blocks[0]
    elif mode == 'between':
        opening, closing = spec['start'], spec['end']
        if not opening or not closing or text.count(opening) != 1:
            raise RecordInputError('support start must occur exactly once')
        start = text.index(opening)
        end = text.find(closing, start + len(opening))
        if end < 0:
            raise RecordInputError('support closing delimiter missing')
        end += len(closing)
    elif mode == 'adjacent_proof':
        label = '\\label{' + spec['label'] + '}'
        if text.count(label) != 1:
            raise RecordInputError('proof statement label is missing or ambiguous')
        at = text.index(label)
        # A display or enumerate inside the statement is not its closing boundary.
        heads = list(re.finditer(r'\\begin\{(theorem|proposition|lemma|corollary|thm|prop|lem|cor|claim|equivform|remark|example)\}', text[:at]))
        closing = r'\\end\{' + re.escape(heads[-1].group(1)) + r'\}' if heads else r'\\end\{[^{}]+\}'
        end_statement = re.search(closing, text[at:])
        if end_statement is None:
            raise RecordInputError('unclosed statement before proof')
        at += end_statement.end()
        m = re.search(r'\\begin\{proof\}(?:\[[^\n]*?\])?', text[at:])
        if m is None:
            raise RecordInputError('adjacent proof missing')
        between = text[at:at+m.start()]
        if re.search(r'\\(?:begin\{|(?:sub)*section\b)', between):
            raise RecordInputError('next proof belongs to another environment or section')
        start = at + m.start()
        end = text.find(r'\end{proof}', at + m.end())
        if end < 0:
            raise RecordInputError('unclosed adjacent proof')
        end += len(r'\end{proof}')
    else:
        raise RecordInputError(f'unknown support selector {mode!r}')
    body = text[start:end]
    if not normalized(re.sub(r'\\(?:begin|end)\{proof\}', '', body)):
        raise RecordInputError('empty proof span')
    return locator(path, coverage.line_of(text, start), coverage.line_of(text, end)), body


def short_proof_support(inputs: Inputs, disposition: dict, row: dict, sources: list[str]) -> dict:
    """Bind a retained short proof without asserting a long-record correspondence."""
    if disposition.get('action') != 'explained_in_short' or not disposition.get('rationale'):
        raise RecordInputError('explicit explained_in_short disposition and rationale required')
    if disposition.get('short_statement_sha256') != row['statement_sha256']:
        raise RecordInputError('short statement changed; proof disposition needs review')
    spec = disposition['support']
    if spec['path'] not in sources or not spec['path'].startswith(f"paper/{row['problem']}/"):
        raise RecordInputError('short proof support belongs to another problem or source')
    loc, body = support_span(inputs, spec, short_path=spec['path'])
    if digest(body) != spec['sha256']:
        raise RecordInputError('stale short proof span; text changed after disposition review')
    return {'kind': 'ordinary_proof_text', 'availability': 'located', 'locator': loc,
            'sha256': digest(body), 'review_status': disposition['review_status'],
            'rationale': disposition['rationale'],
            'validation': 'text_presence_and_digest_only; proof_correctness_not_checked',
            'long_correspondence': 'open; this disposition does not establish a long-record link'}


def registered_support(row: dict, inputs: Inputs, margin_links: dict, decl_cache: dict) -> dict:
    """Validate local declaration existence and native marks; retain ledger status verbatim."""
    declarations = coverage.declarations_of(row)
    failures, sources = [], []
    for d in declarations:
        path, name = d['file'], d['name']
        try:
            if path not in decl_cache:
                decl_cache[path] = qualified_declaration_lines(inputs.read(path))
            if re.search(r'\b(?:sorry|admit)\b', lean_code_without_comments_and_strings(inputs.read(path))):
                failures.append(f'{path}: admitted proof token in source; compilation not established')
            lines = decl_cache[path].get(name, [])
            if len(lines) != 1:
                failures.append(f'{path}::{name}: expected one declaration, found {len(lines)}')
            else:
                sources.append({**locator(path, lines[0]), 'declaration': name})
        except (OSError, ValueError) as exc:
            failures.append(f'{path}::{name}: {exc}')
        if not any(coverage.matches(link, d) for link in margin_links.get(row['id'], [])):
            failures.append(f'{row["id"]}: native evidence mark does not bind {name}')
    return {'kind': 'registered_lean_evidence',
            'availability': 'located' if declarations and not failures else 'unresolved',
            'ledger_lean_status': row['lean']['status'],
            'named_inputs': row['lean'].get('named_inputs', []),
            'ledger_comparator': row['comparator'],
            'locators': sources, 'failures': failures,
            'validation': 'source_and_evidence_mark_only; Lean_and_Comparator_UNRUN'}


def _report(root: Path = ROOT, problems: list[int] | None = None) -> dict:
    inputs = Inputs(root)
    # Each report reads an immutable local input snapshot. Strip comments and
    # split each file once, rather than once per assertion in a long paper.
    statement_lines: dict[str, list[str]] = {}
    def assertion_text(loc: coverage.Located) -> str:
        if loc.path not in statement_lines:
            statement_lines[loc.path] = coverage.counter_view(inputs.read(loc.path)).splitlines()
        return statement_text(loc, '', counter_lines=statement_lines[loc.path])
    for rel in ('scripts/reasoning_record_audit.py', 'scripts/assemble_reasoning_surfaces.py',
                'scripts/check_lean_paper_propagation.py', 'scripts/lean_source.py',
                'scripts/build_reading_edition.py', 'scripts/papers/paper_corpus_renderer.py'):
        inputs.read(rel)
    try:
        ledger = inputs.json('docs/paper_lean_coverage.json')
        corpus = inputs.json('docs/papers/corpus.json')
        links = inputs.json(LINKS)
        if links.get('schema') != LINK_SCHEMA or not isinstance(links.get('links'), list):
            raise RecordInputError('invalid short/long link manifest')
        integrity = coverage.ledger_integrity_failures(ledger)
        if integrity:
            raise RecordInputError('; '.join(integrity))
        currency, texts = coverage.locate_rows(ledger, inputs.read)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        return {'schema': SCHEMA, 'status': 'refusal', 'boundary': BOUNDARY,
                'reason': str(exc), 'pairs': [], 'summary': {},
                'input_sha256': dict(sorted(inputs.hashes.items()))}
    rows = {r['id']: r for r in ledger['rows']}
    authored: dict[str, dict] = {}
    dispositions: dict[str, dict] = {}
    try:
        for link in links['links']:
            sid = link['short_id']
            if sid in authored or sid not in rows or rows[sid]['side'] != 'short':
                raise RecordInputError(f'duplicate or unknown short link {sid}')
            if not link.get('rationale') or link.get('relation') != 'authored_correspondence':
                raise RecordInputError(f'{sid}: explicit relation and rationale required')
            authored[sid] = link
        for disposition in links.get('dispositions', []):
            sid = disposition['short_id']
            if sid in dispositions or sid not in rows or rows[sid]['side'] != 'short':
                raise RecordInputError(f'duplicate or unknown short proof disposition {sid}')
            if disposition.get('action') != 'explained_in_short' or not disposition.get('rationale'):
                raise RecordInputError(f'{sid}: explained_in_short action and rationale required')
            dispositions[sid] = disposition
    except (KeyError, TypeError, ValueError) as exc:
        return {'schema': SCHEMA, 'status': 'refusal', 'boundary': BOUNDARY,
                'reason': str(exc), 'pairs': [], 'summary': {},
                'input_sha256': dict(sorted(inputs.hashes.items()))}
    global_findings = [{'code': 'stale_or_uninventoried_statement', 'severity': 'error', 'detail': x}
                       for x in currency.missing + currency.unrowed]
    global_findings += [{'code': 'stale_statement_coordinate', 'severity': 'error',
                         'short_claim': sid, 'detail': f'{old} -> {new}'}
                        for sid, old, new in currency.drift]
    margin_links = coverage.evidence_links(ledger, inputs.read)
    decl_cache: dict = {}
    pairs = []
    all_problems = sorted({r['problem'] for r in ledger['rows']})
    selected = all_problems if problems is None else sorted(set(problems))
    if not selected or any(p not in all_problems for p in selected):
        return {'schema': SCHEMA, 'status': 'refusal', 'boundary': BOUNDARY,
                'reason': 'unknown or empty problem selection', 'pairs': [], 'summary': {},
                'input_sha256': dict(sorted(inputs.hashes.items()))}
    # Import inside report: the native assembler calls this module lazily.
    for problem in selected:
        short = [r for r in ledger['rows'] if r['problem'] == problem and r['side'] == 'short']
        long = [r for r in ledger['rows'] if r['problem'] == problem and r['side'] == 'long']
        ids = {r['paper_id'] for r in short + long}
        papers = {r['paper_id']: r for r in corpus['papers'] if r['paper_id'] in ids}
        findings, claims, used = [], [], set()
        longid, shortid = long[0]['paper_id'], short[0]['paper_id']
        if set(papers) != {longid, shortid}:
            raise RecordInputError(f'{problem}: native corpus missing pair')
        assembly = PAPERS[str(problem)]
        directory = assembly['directory'].relative_to(ROOT).as_posix()
        output = assembly['output'].relative_to(ROOT).as_posix()
        expected = inputs.read(directory + '/preamble.tex')
        for part in assembly['parts']:
            expected += f'% ---- part {part} ----\n' + inputs.read(directory + '/' + part + '.tex')
        if expected != inputs.read(output):
            findings.append({'code': 'stale_assembly', 'severity': 'error', 'detail': output,
                             'short_claims': [r['id'] for r in short], 'long_location': locator(output, 1)})
        # Read full text, too: its hash is part of navigator freshness.
        for p in papers.values():
            inputs.read(p['local_full_text'])
        for s in short:
            sid, sloc = s['id'], currency.located.get(s['id'])
            item = {'short_claim': sid, 'label': s['label'], 'state': 'unresolved',
                    'short_location': locator(sloc.path, sloc.line, sloc.end_line, s['label']) if sloc else None,
                    'statement_sha256': s['statement_sha256'],
                    'long_locations': [], 'matches': [], 'candidates': [],
                    'ledger_lean_status': s['lean']['status'],
                    'ledger_comparator_status': s['comparator']['status']}
            for g in long:
                gloc = currency.located.get(g['id'])
                if gloc is None:
                    continue
                complete = bool(declaration_set(s)) and declaration_set(s) == declaration_set(g)
                alias = label_key(s['label']) == label_key(g['label'])
                overlap = declaration_set(s) & declaration_set(g)
                if complete or alias or overlap:
                    item['candidates'].append({'long_claim': g['id'],
                        'location': locator(gloc.path, gloc.line, gloc.end_line, g['label']),
                        'basis': 'complete_declaration_set' if complete else 'label_alias' if alias else 'partial_declaration_overlap',
                        'shared_declarations': sorted(name for _path, name in overlap)})
                compatible = (s['lean']['status'] in coverage.EXACT and g['lean']['status'] in coverage.EXACT)
                # Conditional evidence is never silently promoted by a set match.
                if complete and compatible and sloc is not None:
                    support = registered_support(g, inputs, margin_links, decl_cache)
                    if support['availability'] == 'located':
                        item['matches'].append({'long_claim': g['id'], 'basis': 'complete_registered_support',
                                                'support': support})
                        item['long_locations'].append(locator(gloc.path, gloc.line, gloc.end_line, g['label']))
                        used.add(g['id'])
                        item['state'] = 'registered_evidence_linked'
            explicit = authored.get(sid)
            if explicit:
                try:
                    if sloc is None or explicit['short_statement_sha256'] != s['statement_sha256']:
                        raise RecordInputError('short statement changed; correspondence needs review')
                    gid = explicit.get('long_id')
                    if gid:
                        g = rows.get(gid)
                        if not g or g['side'] != 'long' or g['problem'] != problem or gid not in currency.located:
                            raise RecordInputError('linked long statement missing or belongs to another problem')
                        if explicit['long_statement_sha256'] != g['statement_sha256']:
                            raise RecordInputError('long statement changed; correspondence needs review')
                    support = explicit['support']
                    loc, body = support_span(inputs, support)
                    if not loc['path'].startswith(directory + '/'):
                        raise RecordInputError('support belongs to another problem')
                    if digest(body) != support['sha256']:
                        raise RecordInputError('stale support span; text changed after correspondence review')
                    item['matches'] = [{'long_claim': gid, 'basis': 'authored_correspondence',
                        'rationale': explicit['rationale'], 'support': {
                            'kind': 'ordinary_proof_text', 'availability': 'located', 'locator': loc,
                            'sha256': digest(body), 'review_status': explicit['review_status'],
                            'validation': 'text_presence_and_digest_only; proof_correctness_not_checked'}}]
                    item['long_locations'] = [loc]
                    item['state'] = 'authored_proof_text_linked'
                    if gid:
                        used.add(gid)
                except (KeyError, TypeError, OSError, ValueError) as exc:
                    item['state'] = 'unresolved'
                    item['matches'] = []
                    item['long_locations'] = []
                    findings.append({'code': 'stale_or_missing_proof', 'severity': 'error',
                        'short_claim': sid, 'short_location': item['short_location'],
                        'long_location': explicit.get('support'), 'detail': str(exc)})
            disposition = dispositions.get(sid)
            if disposition:
                try:
                    short_paper = next(p for p in ledger['papers'] if p['paper_id'] == shortid)
                    item['short_proof'] = short_proof_support(inputs, disposition, s, short_paper['sources'])
                    if item['state'] == 'unresolved':
                        item['state'] = 'short_proof_explained_long_link_open'
                        findings.append({'code': 'short_proof_explained_long_link_open', 'severity': 'warning',
                            'short_claim': sid, 'short_location': item['short_location'],
                            'detail': 'A hash-bound complete proof is retained in the short paper. '
                                      'No long-record correspondence is asserted by this disposition.'})
                except (KeyError, TypeError, OSError, ValueError) as exc:
                    item['state'] = 'unresolved'
                    item['matches'] = []
                    item['long_locations'] = []
                    findings.append({'code': 'stale_or_missing_short_proof', 'severity': 'error',
                        'short_claim': sid, 'short_location': item['short_location'], 'detail': str(exc)})
            if item['state'] == 'unresolved':
                findings.append({'code': 'unresolved_short_long_link', 'severity': 'error',
                    'short_claim': sid, 'short_location': item['short_location'],
                    'long_locations': [c['location'] for c in item['candidates']],
                    'long_record': output,
                    'detail': 'No accepted complete evidence match or hash-bound authored proof link. '
                              'This is a correspondence gap, not a finding that the mathematics is false or absent.'})
            claims.append(item)
        # Inventory raw long assertions, including ones not yet in the ledger.
        long_paper = next(p for p in ledger['papers'] if p['paper_id'] == longid)
        long_sources = [(path, inputs.read(path)) for path in long_paper['sources']]
        occurrences = coverage.inventory(long_sources, coverage.span_specs(long))
        buckets = defaultdict(list)
        for found in occurrences:
            labels = found['labels']
            pseudo = coverage.Located({'id': (labels or ['unlabelled'])[0], 'environment': found['environment']},
                                      found['path'], found['line'], found['end_line'])
            body = assertion_text(pseudo)
            buckets[normalized(body)].append(found)
        for key, group in buckets.items():
            if len(group) > 1:
                findings.append({'code': 'duplicate_statement', 'severity': 'review',
                    'short_claims': [c['short_claim'] for c in claims if any(
                        m.get('long_claim', '') and any(m['long_claim'].endswith('#' + label)
                            for g in group for label in g['labels']) for m in c['matches'])],
                    'long_locations': [locator(g['path'], g['line'], g['end_line'], (g['labels'] or [None])[0]) for g in group],
                    'normalised_sha256': digest(key),
                    'detail': 'Same TeX assertion after whitespace/comment/label removal; retain until editorial review.'})
        passages = defaultdict(list)
        for path, text in long_sources:
            if path.endswith('preamble.tex') or '/reasoning-parts/' not in path:
                continue
            view = coverage.counter_view(text)
            for match in re.finditer(r'(?s)(?:^|\n\s*\n)(.*?)(?=\n\s*\n|$)', view):
                body = match.group(1).strip()
                key = normalized(body)
                if len(key) >= 300 and len(key.split()) >= 40 and not body.startswith(('\\newcommand', '\\renewcommand')):
                    passages[key].append(locator(path, coverage.line_of(view, match.start(1)), coverage.line_of(view, match.end(1))))
        for key, locations in passages.items():
            if len(locations) > 1:
                findings.append({'code': 'duplicate_passage', 'severity': 'review',
                    'short_claims': [], 'long_locations': locations, 'normalised_sha256': digest(key),
                    'detail': 'Repeated long-record passage of at least 40 words and 300 characters; editorial review only.'})
        # Similar statements under the same alias are possible stale passages, not proofs of contradiction.
        for c in claims:
            # An explicit, still hash-bound correspondence already accounts for
            # this wording difference. Any changed statement fails above.
            if c['state'] == 'authored_proof_text_linked':
                continue
            sloc = currency.located.get(c['short_claim'])
            if sloc is None:
                continue
            a = normalized(assertion_text(sloc))
            for candidate in c['candidates']:
                if candidate['basis'] != 'label_alias':
                    continue
                gloc = currency.located[candidate['long_claim']]
                b = normalized(assertion_text(gloc))
                ratio = difflib.SequenceMatcher(None, a, b, autojunk=False).ratio()
                if a != b and ratio >= .88:
                    findings.append({'code': 'possible_stale_passage', 'severity': 'review',
                        'short_claim': c['short_claim'], 'short_location': c['short_location'],
                        'long_location': candidate['location'], 'text_similarity': round(ratio, 4),
                        'detail': 'Similar alias-linked text differs; review constants and assumptions. No semantic verdict.'})
        long_only = [{'long_claim': g['id'],
                      'location': locator(currency.located[g['id']].path, currency.located[g['id']].line,
                                          currency.located[g['id']].end_line, g['label'])}
                     for g in long if g['id'] not in used and g['id'] in currency.located]
        pairs.append({'problem': problem, 'short_paper': papers[shortid], 'long_paper': papers[longid],
            'status': 'structural_findings' if any(x['severity'] == 'error' for x in findings) else 'structurally_linked',
            'claims': claims, 'long_only_or_unmatched': long_only, 'findings': findings,
            'summary': {'short_claims': len(short), 'long_claims': len(long),
                        'linked_short_claims': sum(c['state'] in ('registered_evidence_linked', 'authored_proof_text_linked') for c in claims),
                        'explained_in_short': sum('short_proof' in c for c in claims),
                        'long_correspondence_open': sum(c['state'] in ('unresolved', 'short_proof_explained_long_link_open') for c in claims),
                        'unresolved_short_claims': sum(c['state'] == 'unresolved' for c in claims),
                        'duplicates': sum(x['code'] == 'duplicate_statement' for x in findings),
                        'duplicate_passages': sum(x['code'] == 'duplicate_passage' for x in findings),
                        'possible_stale_passages': sum(x['code'] == 'possible_stale_passage' for x in findings)}})
    summary = {k: sum(p['summary'][k] for p in pairs) for k in pairs[0]['summary']}
    summary.update(pairs=len(pairs), global_findings=len(global_findings),
                   explicit_links=len(authored), explicit_short_proof_dispositions=len(dispositions),
                   evidence_lean_pin=ledger['lean_pin'])
    for pair in pairs:
        # Paper metadata is a projection. Keep only navigation fields; no duplicated registry authority.
        for key in ('short_paper', 'long_paper'):
            p = pair[key]
            pair[key] = {k: p[k] for k in ('paper_id', 'title', 'local_source', 'local_full_text', 'first_pass', 'sections') if k in p}
    return {'schema': SCHEMA, 'status': 'findings' if global_findings or any(p['status']=='structural_findings' for p in pairs) else 'structurally_linked',
            'boundary': BOUNDARY, 'pairs': pairs, 'global_findings': global_findings, 'summary': summary,
            'input_sha256': dict(sorted(inputs.hashes.items()))}



def report(root: Path = ROOT, problems: list[int] | None = None) -> dict:
    try:
        return _report(root, problems)
    except (OSError, ValueError, KeyError, TypeError, StopIteration) as exc:
        return {'schema': SCHEMA, 'status': 'refusal', 'boundary': BOUNDARY,
                'reason': str(exc), 'pairs': [], 'summary': {}, 'input_sha256': {}}

def report_delta(before: dict, after: dict) -> dict:
    """Account for registered moves; never interpret deletion as an improvement."""
    def claims(r):
        return {c['short_claim']: c for p in r.get('pairs', []) for c in p['claims']}
    old, new = claims(before), claims(after)
    return {'schema': 'plectis-short-long-delta/1',
            'added_short_claims': sorted(new.keys()-old.keys()),
            'removed_short_claims_requires_review': sorted(old.keys()-new.keys()),
            'changed_statement': sorted(k for k in old.keys() & new.keys() if old[k]['statement_sha256'] != new[k]['statement_sha256']),
            'changed_link_state': [{'short_claim': k, 'before': old[k]['state'], 'after': new[k]['state']}
                                   for k in sorted(old.keys() & new.keys()) if old[k]['state'] != new[k]['state']],
            'changed_long_destinations': sorted(k for k in old.keys() & new.keys()
                if old[k]['long_locations'] != new[k]['long_locations'])}


def freshness_errors(root: Path, value: dict) -> list[str]:
    if value.get('schema') != SCHEMA or not isinstance(value.get('input_sha256'), dict) or not value['input_sha256']:
        return ['invalid or unbound record audit']
    errors = []
    for path, expected in value['input_sha256'].items():
        try:
            if digest(safe_path(root, path).read_bytes()) != expected:
                errors.append('stale record audit input: ' + path)
        except (OSError, ValueError) as exc:
            errors.append('missing record audit input: ' + path + ': ' + str(exc))
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--problem', type=int, action='append')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--previous', type=Path)
    parser.add_argument('--delta-output', type=Path)
    args = parser.parse_args(argv)
    try:
        value = report(args.root, args.problem)
        text = canonical(value)
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(text, encoding='utf-8')
        else:
            print(text, end='')
        if args.previous:
            change = canonical(report_delta(json.loads(args.previous.read_text()), value))
            if args.delta_output:
                args.delta_output.write_text(change, encoding='utf-8')
            else:
                print(change, end='')
        if value['status'] == 'refusal':
            print(value['reason'], file=sys.stderr)
            return 2
        print('record audit: ' + json.dumps(value['summary'], sort_keys=True), file=sys.stderr)
        return 1 if value['status'] == 'findings' else 0
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('record audit refusal: ' + str(exc), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
