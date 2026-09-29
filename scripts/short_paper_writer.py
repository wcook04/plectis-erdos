#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Offline short-paper audit and deterministic dossier renderer.

This module uses the existing coverage inventory, evidence map and paper registry.
It does not check Lean, infer generalizations, grade exposition, or call a model.
A pass is bounded to the checks listed in SHORT_PAPER_CONTRACT.md.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any

import check_lean_paper_propagation as coverage
from migrate_statement_presentation import bodies

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 'short-paper-audit/1'
EXTENSION = 'short_paper_v1'
RULES = {
    'SP01': 'Literal local TeX inputs resolve within the source root.',
    'SP02': 'Every inventoried assertion has a unique nonempty label.',
    'SP03': 'Literal local cross-references resolve.',
    'SP04': 'Literal citation keys resolve to the bibliography.',
    'SP05': 'House prose contains no em dash.',
    'SP06': 'Potential not-X-but-Y construction needs a prose review.',
    'SP07': 'Every assertion has an exact native coverage-row binding.',
    'SP08': 'Recorded evidence is visible at the assertion, with named-input limits.',
    'SP09': 'A contract draft has complete, source-bound narrative roles.',
    'SP10': 'Contract-draft bytes replay exactly from the supplied dossier and evidence.',
    'SP11': 'The selected lead and evidence status agree across dossier and claim evidence.',
    'SP12': 'Literal TeX environment boundaries are balanced.',
}
SEMANTIC_REVIEW = [
    'Is the selected result the strongest useful supported result?',
    'Are every hypothesis, quantifier and definition mathematically correct?',
    'Does the explanation identify the decisive mechanism and genuine hard step?',
    'Is the named problem an instance, a related target, or a distinct open question?',
    'Are attribution and ordinary-review identities accurate?',
    'Can a cold reader reconstruct the idea and recover the proof in the long record?',
    'Are the chosen generality, examples and nearby questions useful?',
]
KEY = re.compile(r'[A-Za-z0-9][A-Za-z0-9_.:+-]*\Z')
INPUT = re.compile(r'\\(?:input|include)\s*\{([^{}]*)\}')
REF = re.compile(r'\\(?:eqref|ref|pageref|autoref|cref|Cref)\*?\{([^{}]+)\}')
CITE = re.compile(r'\\(?:cite|citep|citet|parencite|textcite|autocite)\*?(?:\[[^\]]*\]){0,2}\{([^{}]+)\}')
LABEL = re.compile(r'\\(?:label|compatlabel)\{([^{}]+)\}')
BIBITEM = re.compile(r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}')
BLOCK = re.compile(r'\\(begin|end)\{([^{}]+)\}')
EVIDENCE_CLASSES = {'lean', 'comparator', 'ordinary_reviewed', 'computed', 'cited'}


def canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(',', ':')).encode()


def digest(value: bytes | str) -> str:
    return 'sha256:' + hashlib.sha256(value.encode() if isinstance(value, str) else value).hexdigest()


class Refusal(ValueError):
    """A typed, field-located refusal; never a silent default."""
    def __init__(self, field: str, reason: str):
        self.field, self.reason = field, reason
        super().__init__(f'{field}: {reason}')


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding='utf-8'))


def safe_path(root: Path, relative: str) -> Path:
    p = PurePosixPath(relative)
    if not relative or p.is_absolute() or '..' in p.parts or '\\' in relative:
        raise Refusal(relative or 'path', 'unsafe source path')
    candidate = root / p
    # Refuse all symlink components, even those whose destination is in root.
    cur = root
    for part in p.parts:
        cur = cur / part
        if cur.is_symlink():
            raise Refusal(relative, 'symlink source is unsupported')
    if not candidate.resolve().is_relative_to(root.resolve()):
        raise Refusal(relative, 'source path escapes root')
    return candidate


def mask_comments(text: str) -> str:
    """Preserve coordinates; handle TeX's escaped percent convention."""
    out = list(text)
    for m in re.finditer('%', text):
        n, j = 0, m.start() - 1
        while j >= 0 and text[j] == '\\':
            n += 1; j -= 1
        if n % 2 == 0:
            end = text.find('\n', m.start())
            end = len(text) if end < 0 else end
            out[m.start():end] = [' '] * (end - m.start())
    return ''.join(out)


def mask_verbatim(text: str) -> str:
    out = list(mask_comments(text))
    view = ''.join(out)
    patterns = [r'\\begin\{(verbatim\*?|Verbatim|lstlisting|minted)\}.*?\\end\{\1\}',
                r'\\verb\*?([^\w\s]).*?\1']
    for pat in patterns:
        for m in re.finditer(pat, view, re.S):
            out[m.start():m.end()] = ['\n' if c == '\n' else ' ' for c in view[m.start():m.end()]]
    return ''.join(out)


def prose_view(text: str) -> str:
    view = mask_verbatim(text)
    out = list(view)
    for pat in [r'\$\$.*?\$\$', r'(?<!\\)\$.*?(?<!\\)\$', r'\\\[.*?\\\]', r'\\\(.*?\\\)',
                r'\\(?:url|nolinkurl)\{[^{}]*\}', r'\\href\{[^{}]*\}']:
        for m in re.finditer(pat, view, re.S):
            out[m.start():m.end()] = ['\n' if c == '\n' else ' ' for c in view[m.start():m.end()]]
    return ''.join(out)


def command_arguments(text: str, name: str, arity: int) -> list[tuple[int, list[str]]]:
    """Read balanced mandatory arguments; nested dagger marks are real corpus data."""
    rows=[]
    for match in re.finditer(r'\\'+re.escape(name)+r'(?![A-Za-z@])', text):
        i=match.end(); args=[]
        for _ in range(arity):
            while i<len(text) and text[i].isspace(): i+=1
            if i==len(text) or text[i]!='{': break
            start=i+1; depth=1; i+=1
            while i<len(text) and depth:
                if text[i]=='\\': i+=2; continue
                if text[i]=='{': depth+=1
                elif text[i]=='}': depth-=1
                i+=1
            if depth: break
            args.append(text[start:i-1])
        if len(args)==arity: rows.append((match.start(),args))
    return rows


def line_at(text: str, offset: int) -> int:
    return text.count('\n', 0, offset) + 1


def finding(rule: str, path: str, line: int, message: str, severity: str = 'error') -> dict:
    return dict(rule=rule, severity=severity, path=path, line=line, message=message)


def source_tree(root: Path, main: str) -> tuple[list[tuple[str, str]], list[dict]]:
    """Read literal input graph. Preamble inputs are retained for native inventory.

    Never execute TeX. Macro-generated includes remain explicit findings. A mirror's
    build dependencies may be absent; that is an input limitation, not missing math.
    """
    seen: dict[str, str] = {}; issues: list[dict] = []; active: set[str] = set()
    def visit(name: str) -> None:
        if name in active:
            issues.append(finding('SP01', name, 1, 'cyclic TeX input')); return
        if name in seen: return
        try:
            text = safe_path(root, name).read_text(encoding='utf-8')
        except (OSError, Refusal, UnicodeError) as exc:
            issues.append(finding('SP01', name, 1, str(exc))); return
        seen[name] = text; active.add(name)
        for m in INPUT.finditer(mask_verbatim(text)):
            target = m.group(1)
            if any(c in target for c in '\\#'):
                issues.append(finding('SP01', name, line_at(text, m.start()),
                                      'macro-valued input is outside static audit: ' + target)); continue
            if not Path(target).suffix: target += '.tex'
            options = [str(PurePosixPath(name).parent / target), 'paper/' + target, target]
            resolved = None
            for option in dict.fromkeys(options):
                try:
                    if safe_path(root, option).is_file(): resolved = option; break
                except Refusal: pass
            if resolved is None:
                issues.append(finding('SP01', name, line_at(text, m.start()), 'unresolved input: ' + target))
            else: visit(resolved)
        active.remove(name)
    visit(main)
    return list(seen.items()), issues


def narrative_sources(pairs: list[tuple[str, str]], main: str) -> list[tuple[str, str]]:
    """Exclude shared preamble/macro/evidence implementation from prose findings."""
    selected = []
    for path, text in pairs:
        if path != main and (path.startswith('paper/evidence/') or
                            Path(path).name in {'problem-note-preamble.tex','paper-evidence.tex','module-aliases.tex'}):
            continue
        if '\\begin{document}' in text:
            at = text.index('\\begin{document}')
            text = '\n' * text[:at].count('\n') + text[at:]
        selected.append((path, text))
    return selected


def portfolio(root: Path, system_id: str = 'claim-faithful-publication-systems') -> list[dict]:
    papers = read_json(safe_path(root, 'docs/papers/corpus.json'))['papers']
    chosen = [p for p in papers if p.get('form') == 'Problem note' and p.get('publication_state') == 'active']
    system = [p for p in papers if p['paper_id'] == system_id]
    if len(chosen) != 8 or len(system) != 1:
        raise Refusal('portfolio', 'expected eight active problem notes and one explicitly selected systems paper')
    return [dict(paper_id=p['paper_id'], path=p['local_source'],
                 kind='mathematics' if p in chosen else 'system') for p in chosen + system]


def audit(root: Path, paper_id: str, main: str, kind: str = 'mathematics') -> dict:
    pairs, issues = source_tree(root, main)
    if not pairs:
        return dict(paper_id=paper_id, path=main, kind=kind, findings=issues, assertions=[], metrics={}, status='findings')
    prose = narrative_sources(pairs, main)
    all_labels: dict[str, tuple[str, int]] = {}
    bibkeys: set[str] = set()
    for path, text in prose:
        view = mask_verbatim(text)
        for m in LABEL.finditer(view):
            key = m.group(1)
            if key in all_labels:
                issues.append(finding('SP02', path, line_at(view, m.start()), 'duplicate label: ' + key))
            all_labels[key] = (path, line_at(view, m.start()))
        bibkeys.update(BIBITEM.findall(view))
        for m in re.finditer(r'\\bibliography\{([^{}]+)\}', view):
            for part in m.group(1).split(','):
                name = str(PurePosixPath(path).parent / (part.strip() + '.bib'))
                try:
                    b = safe_path(root, name).read_text()
                    bibkeys.update(re.findall(r'@\w+\s*\{\s*([^,\s]+)', b))
                except (OSError, Refusal):
                    issues.append(finding('SP04', path, line_at(view, m.start()), 'unresolved bibliography: ' + name))
    for path, text in prose:
        view = mask_verbatim(text)
        for m in REF.finditer(view):
            for key in m.group(1).split(','):
                if key.strip() not in all_labels:
                    issues.append(finding('SP03', path, line_at(view, m.start()), 'unresolved literal reference: ' + key))
        for m in CITE.finditer(view):
            for key in m.group(1).split(','):
                if key.strip() not in bibkeys:
                    issues.append(finding('SP04', path, line_at(view, m.start()), 'unresolved literal citation: ' + key))
        clean = prose_view(text)
        # Bibliographic titles are not house prose. Report source text, not macro expansions.
        clean = clean.split('\\begin{thebibliography}', 1)[0]
        for m in re.finditer(r'—|(?<!-)---(?!-)|\\textemdash\b', clean):
            issues.append(finding('SP05', path, line_at(clean, m.start()), 'em dash in literal prose'))
        for m in re.finditer(r'\bnot\b[^.!?\n]*(?:\n(?!\s*\n)[^.!?\n]*){0,3}?\bbut\b', clean, re.I):
            issues.append(finding('SP06', path, line_at(clean, m.start()),
                                  'possible contrastive construction; inspect this sentence', 'review'))
        stack = []
        for m in BLOCK.finditer(view):
            action, env = m.groups()
            if action == 'begin': stack.append((env, line_at(view, m.start())))
            elif not stack or stack[-1][0] != env:
                issues.append(finding('SP12', path, line_at(view, m.start()), 'unmatched environment end: ' + env))
            else: stack.pop()
        for env, line in stack:
            issues.append(finding('SP12', path, line, 'unclosed environment: ' + env))

    ledger_file = safe_path(root, 'docs/paper_lean_coverage.json')
    ledger = read_json(ledger_file) if ledger_file.is_file() else {'rows': []}
    rows = [r for r in ledger['rows'] if r['paper_id'] == paper_id]
    spans = [{'label': r['label'], **r['span']} for r in rows if r.get('span')]
    # Canonical native counter and raw-body hashing; do not invent another normalization.
    items = coverage.inventory(pairs, spans)
    by_label: dict[str, list[dict]] = {}
    for row in rows:
        for label in [row.get('label'), *row.get('other_labels', [])]:
            if label: by_label.setdefault(label, []).append(row)
    marks = {}
    for path, text in pairs:
        for _, (label, mark, lean, comp) in command_arguments(mask_comments(text), 'DeclareResultEvidence', 4):
            marks[label] = (mark, lean, comp)
    assertions = []
    for item in items:
        path, line = item['path'], item['line']
        labels = item['labels']
        if not labels:
            issues.append(finding('SP02', path, line, 'assertion has no stable label'))
        candidates = {r['id']: r for label in labels for r in by_label.get(label, [])}
        matched = [r for r in candidates.values() if r['statement_sha256'] == item['statement_sha256']]
        status = 'unbound'; evidence_status = None
        if len(matched) != 1:
            issues.append(finding('SP07', path, line, 'assertion lacks a unique current coverage row; labels=' + ','.join(labels)))
        else:
            row = matched[0]; evidence_status = row['lean']['status']; status = 'source_bound'
            mark = marks.get(row['label'])
            raw = dict(pairs)[path]
            after = '\n'.join(raw.splitlines()[item['end_line']:item['end_line']+20])
            adjacent = re.match(r'\s*\\evidenceremark\{', coverage.counter_view(after)) is not None
            if evidence_status in {'exact','exact_or_stronger','modulo_named_input'}:
                if not mark or not mark[1]:
                    issues.append(finding('SP08', path, line, 'recorded Lean support lacks a generated margin mark'))
                if row.get('comparator',{}).get('status') == 'compared' and (not mark or not mark[2]):
                    issues.append(finding('SP08', path, line, 'recorded Comparator support lacks a visible mark'))
                if evidence_status == 'modulo_named_input' and not adjacent:
                    issues.append(finding('SP08', path, line, 'named-input result lacks an adjacent evidence remark'))
            elif evidence_status == 'none' and not adjacent:
                issues.append(finding('SP08', path, line, 'no whole-statement Lean proof; add a local evidence remark', 'review'))
        assertions.append({**item, 'binding':status, 'recorded_lean_status': evidence_status,
                           'validation':'source binding only; proof and receipts not replayed'})
    maintext = dict(pairs).get(main, '')
    abstract = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', mask_comments(maintext), re.S)
    abstract_words = len(re.findall(r"\b[\w'-]+\b", abstract.group(1))) if abstract else 0
    # Existing papers have no draft-role sidecar. Do not call their meaning defective.
    issues.append(finding('SP09', main, 1, 'no dossier-bound narrative-role map supplied; semantic contract unassessed', 'unassessed'))
    return dict(paper_id=paper_id, path=main, kind=kind,
                status='findings' if any(f['severity']=='error' for f in issues) else 'mechanical_checks_pass_semantics_unassessed',
                input_sha256={p:digest(t) for p,t in pairs},
                metrics={'assertions':len(items),'abstract_source_words':abstract_words,
                         'first_assertion_line': items[0]['line'] if items else None},
                assertions=assertions, findings=sorted(issues,key=lambda f:(f['path'],f['line'],f['rule'])),
                semantic_review=SEMANTIC_REVIEW)


def text_field(obj: dict, key: str, path: str) -> str:
    value = obj.get(key)
    if not isinstance(value, str) or not value.strip():
        raise Refusal(path + '.' + key, 'missing nonempty text')
    return value


def nonempty_list(obj: dict, key: str, path: str) -> list:
    value = obj.get(key)
    if not isinstance(value, list) or not value:
        raise Refusal(path + '.' + key, 'missing nonempty list')
    return value


def local_locator(root: Path, value: Any, field: str) -> dict:
    if not isinstance(value, dict): raise Refusal(field, 'expected source-span object')
    path = text_field(value, 'path', field)
    start, end = value.get('start_line'), value.get('end_line')
    if type(start) is not int or type(end) is not int or not 1 <= start <= end:
        raise Refusal(field, 'invalid line interval')
    try: lines = safe_path(root,path).read_text().splitlines(keepends=True)
    except (OSError, Refusal) as exc: raise Refusal(field, str(exc)) from exc
    if end > len(lines): raise Refusal(field, 'line interval exceeds source')
    if value.get('sha256') != digest(''.join(lines[start-1:end])):
        raise Refusal(field, 'source span digest differs')
    return value


def tex_fragment(value: str, field: str) -> str:
    """A narrow rendering dialect, not a TeX security sandbox.

    Fragments cannot define commands, include files, add environments, comments,
    references or write operations. Generated shells own those operations. TeX is
    still compiled only after review, with shell escape disabled.
    """
    banned = r'\\(?:input|include|includegraphics|usepackage|documentclass|newcommand|renewcommand|def|edef|gdef|xdef|let|catcode|csname|write\w*|read\w*|openin|openout|closeout|closein|immediate|special|directlua|pdfobj|begin|end|label|ref|eqref|cite\w*|href|url|bibliography)\b'
    if re.search(banned,value) or re.search(r'(?<!\\)%',value):
        raise Refusal(field, 'unsupported TeX operation in authored fragment')
    if re.search(r'—|(?<!-)---(?!-)|\\textemdash\b',prose_view(value)):
        raise Refusal(field,'house prose forbids an em dash')
    depth = 0
    for m in re.finditer(r'\\.|[{}]',value,re.S):
        if m.group() == '{': depth += 1
        if m.group() == '}': depth -= 1
        if depth < 0: raise Refusal(field,'unbalanced braces')
    if depth: raise Refusal(field,'unbalanced braces')
    return value.strip()


def validate_dossier(dossier: Any, evidence: Any, root: Path) -> tuple[dict, dict, dict]:
    if not isinstance(dossier,dict) or dossier.get('schema') != 'dossier/1':
        raise Refusal('schema','expected dossier/1')
    if type(dossier.get('problem')) is not int: raise Refusal('problem','expected integer problem number')
    landscape=dossier.get('landscape')
    if not isinstance(landscape,dict) or any(not isinstance(landscape.get(k),list) for k in ['routes','failed_routes_with_scope','generalisations']):
        raise Refusal('landscape','expected the three dossier/1 lists')
    nonempty_list(dossier,'sources','dossier')
    results = nonempty_list(dossier,'results','dossier')
    extensions = dossier.get('extensions')
    if not isinstance(extensions,dict): raise Refusal('extensions','expected versioned extensions object')
    ext = extensions.get(EXTENSION)
    if not isinstance(ext,dict): raise Refusal('extensions.'+EXTENSION,'required versioned rendering amendment')
    for key in ['paper_id','title','reader','lead_result_id','abstract_statement','motivation','definitions','problem_relation','boundary','proof_outline','long_record_route']:
        text_field(ext,key,'extensions.'+EXTENSION)
    if not KEY.fullmatch(ext['paper_id']): raise Refusal('paper_id','invalid identifier')
    if ext.get('selection_review') != 'authored_selection_not_ranked_by_writer':
        raise Refusal('selection_review','lead selection must be explicitly authored')
    if ext.get('target_relation') not in {'instance','related_distinct_target','conditional_route','counterexample'}:
        raise Refusal('target_relation','classify the relation to the named problem')
    seen = set(); lead = None
    for index, result in enumerate(results):
        field = f'results[{index}]'
        if not isinstance(result,dict): raise Refusal(field,'expected object')
        for key in ['id','statement','generality','mechanism_sentence','hard_step','attribution']:
            text_field(result,key,field)
        if result['id'] in seen: raise Refusal(field+'.id','duplicate result id')
        seen.add(result['id'])
        if not KEY.fullmatch(result['id']): raise Refusal(field+'.id','invalid identifier')
        ev = result.get('evidence')
        if not isinstance(ev,dict) or ev.get('class') not in EVIDENCE_CLASSES:
            raise Refusal(field+'.evidence.class','unknown evidence class')
        for j, loc in enumerate(nonempty_list(ev,'locators',field+'.evidence')):
            local_locator(root,loc,f'{field}.evidence.locators[{j}]')
        for key in ['consumers','open_questions']:
            if not isinstance(result.get(key),list): raise Refusal(field+'.'+key,'expected list; empty is allowed')
        if result['id'] == ext['lead_result_id']: lead = result
    if lead is None: raise Refusal('lead_result_id','does not name a dossier result')
    leadmeta = ext.get('lead')
    if not isinstance(leadmeta,dict): raise Refusal('lead','missing rendering metadata')
    for key in ['hypotheses','statement_includes_hypotheses','status_phrase','naturalness']:
        text_field(leadmeta,key,'lead')
    if leadmeta['statement_includes_hypotheses'] != 'authored_checked':
        raise Refusal('lead.statement_includes_hypotheses','requires explicit authored review')
    for key in ['statement','generality','mechanism_sentence','hard_step','attribution']:
        tex_fragment(lead[key], 'lead.'+key)
    for key in ['title','abstract_statement','motivation','definitions','problem_relation','boundary','proof_outline','long_record_route']:
        tex_fragment(ext[key], 'extensions.'+EXTENSION+'.'+key)
    for key in ['hypotheses','status_phrase','naturalness']:
        tex_fragment(leadmeta[key],'lead.'+key)
    if not isinstance(evidence,dict) or evidence.get('schema') != 'claim_evidence/1' or not isinstance(evidence.get('rows'),list):
        raise Refusal('claim_evidence','expected versioned rows envelope')
    if any(not isinstance(r,dict) for r in evidence['rows']):
        raise Refusal('claim_evidence.rows','each row must be an object')
    matching = [r for r in evidence['rows'] if r.get('paper_id') == ext['paper_id'] and r.get('claim_locator') == lead['id']]
    if len(matching) != 1: raise Refusal('claim_evidence.rows','lead must have exactly one matching row')
    row = matching[0]
    if row.get('statement_hash') != digest(lead['statement']): raise Refusal('statement_hash','exact dossier statement differs')
    if row.get('evidence_class') != lead['evidence']['class']: raise Refusal('evidence_class','dossier and claim-evidence class differ')
    if row.get('status_phrase_required') != leadmeta['status_phrase']: raise Refusal('status_phrase_required','status phrase differs')
    if row['evidence_class'] in {'lean','comparator'} and not row.get('lean_declaration'):
        raise Refusal('lean_declaration','formal evidence requires declaration identity')
    if row['evidence_class'] == 'comparator' and not row.get('comparator_receipt'):
        raise Refusal('comparator_receipt','Comparator evidence requires a receipt locator')
    if row['evidence_class'] == 'ordinary_reviewed':
        local_locator(root,row.get('ordinary_proof_locator'),'ordinary_proof_locator')
    native = leadmeta.get('native_binding')
    if not isinstance(native,dict): raise Refusal('lead.native_binding','missing native coverage link')
    ledger = read_json(safe_path(root,'docs/paper_lean_coverage.json'))
    native_rows = [r for r in ledger['rows'] if r['id'] == native.get('id')]
    if len(native_rows) != 1: raise Refusal('lead.native_binding.id','native row is absent or ambiguous')
    nr = native_rows[0]
    if nr['paper_id'] != ext['paper_id'] or nr['label'] != lead['id']:
        raise Refusal('lead.native_binding','must bind this paper and lead label')
    if row['evidence_class'] not in {'lean','comparator','ordinary_reviewed'}:
        raise Refusal('evidence_class','this theorem renderer does not promote computed or cited evidence to a proof')
    if native.get('statement_sha256') != nr['statement_sha256']:
        raise Refusal('lead.native_binding.statement_sha256','native coverage statement changed')
    source, _ = nr['source'].rsplit(':',1)
    native_bodies = bodies([(source,safe_path(root,source).read_text())],[])
    exact = [b for b in native_bodies if b['statement_sha256'] == nr['statement_sha256']]
    from migrate_statement_presentation import presentation_form
    if len(exact) != 1 or presentation_form(lead['statement']) != presentation_form(exact[0]['body']):
        raise Refusal('lead.statement','does not preserve the native theorem statement')
    native_status = nr['lean']['status']
    if row['evidence_class'] in {'lean','comparator'} and native_status != 'none' and row['lean_declaration'] not in [d['name'] for d in nr['lean'].get('declarations',[])]:
        raise Refusal('lean_declaration','declaration is not named by this native coverage row')
    if row['evidence_class'] in {'lean','comparator'} and native_status not in {'exact','exact_or_stronger','modulo_named_input'}:
        raise Refusal('evidence_class','native coverage has no whole-statement Lean support')
    if row['evidence_class'] == 'comparator' and nr.get('comparator',{}).get('status') != 'compared':
        raise Refusal('evidence_class','native coverage does not record a Comparator pass')
    if row['evidence_class'] == 'ordinary_reviewed' and 'ordinary proof' not in str(nr['lean'].get('reason','')).lower():
        raise Refusal('evidence_class','native row does not record this ordinary proof')
    if native_status == 'modulo_named_input' and not leadmeta.get('named_input_limit'):
        raise Refusal('lead.named_input_limit','conditional formal support needs the named-input boundary')
    # Every rendered role has at least one exact source span. Span binding is not entailment.
    bindings = ext.get('bindings')
    roles = ['abstract_statement','statement','generality','mechanism','hard_step','attribution','hypotheses','status',
             'motivation','definitions','problem_relation','boundary','proof_outline','long_record_route','naturalness']
    if not isinstance(bindings,dict): raise Refusal('bindings','missing source binding map')
    for role in roles:
        for j,loc in enumerate(nonempty_list(bindings,role,'bindings')):
            local_locator(root,loc,f'bindings.{role}[{j}]')
    if lead['evidence']['class'] == 'ordinary_reviewed':
        review = leadmeta.get('review')
        if not isinstance(review,dict) or review.get('kind') not in {'human','ai','source_reported_ai'}:
            raise Refusal('lead.review','ordinary_reviewed must identify reviewer kind')
        if review['kind'] == 'source_reported_ai' and 'no human review' not in leadmeta['status_phrase'].lower():
            raise Refusal('lead.status_phrase','source-reported AI review must retain no-human-review boundary')
    return lead, ext, row


def attribution_bibliography(ext: dict, root: Path) -> str:
    spec=ext.get('attribution_bibliography')
    if not isinstance(spec,dict): raise Refusal('attribution_bibliography','source and keys required')
    keys=nonempty_list(spec,'keys','attribution_bibliography')
    if any(not isinstance(k,str) or not KEY.fullmatch(k) for k in keys) or len(set(keys))!=len(keys):
        raise Refusal('attribution_bibliography.keys','unique literal keys required')
    source=text_field(spec,'source','attribution_bibliography')
    text=safe_path(root,source).read_text()
    starts=list(re.finditer(r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}',text))
    entries={}
    for i,m in enumerate(starts):
        finish=starts[i+1].start() if i+1<len(starts) else text.index('\\end{thebibliography}',m.end())
        entries[m.group(1)]=text[m.start():finish].strip()
    if any(k not in entries for k in keys):raise Refusal('attribution_bibliography.keys','key absent from native paper')
    return '\n'.join(entries[k] for k in keys)


def render(dossier: dict, evidence: dict, root: Path) -> tuple[str, dict]:
    lead, ext, ev = validate_dossier(dossier,evidence,root)
    bibliography=attribution_bibliography(ext,root)
    lm = ext['lead']; lines: list[str] = []; blocks = []
    def add(text: str) -> None: lines.extend(text.splitlines())
    def role(name: str, text: str) -> None:
        start = len(lines)+1; add(text); finish = len(lines)
        blocks.append(dict(role=name,start_line=start,end_line=finish,sha256=digest('\n'.join(lines[start-1:finish])+'\n'),
                           sources=ext['bindings'].get(name, [])))
    add(r'''% Candidate opening and proof skeleton. Generated without a model call.
\documentclass[11pt]{article}
\input{problem-note-preamble}
\usepackage{xurl}''')
    add('\\title{'+ext['title']+'}\n\\subtitle{A source-bound candidate opening}\n\\runninghead{Short-paper candidate}')
    add('\\author{Will Cook}\n\\date{Candidate draft; source-bound demonstration}\n\\begin{document}\n\\maketitle\n\\provenancenote{Source manuscript: Will Cook. This candidate opening was prepared by an AI assistant for review; it is not an approved replacement.}')
    add('\\begin{abstract}')
    role('abstract_statement',ext['abstract_statement'])
    role('mechanism',lead['mechanism_sentence'])
    role('boundary',ext['boundary'])
    add('\\end{abstract}\n\\section{The general result}')
    role('motivation',ext['motivation'])
    role('definitions',ext['definitions'])
    add('\\begin{theorem}\\label{'+lead['id']+'}')
    role('statement',lead['statement'])
    add('\\end{theorem}')
    role('status','\\evidenceremark{'+lm['status_phrase']+'}')
    # Directly print the source path and lines as a stable review route; no copied Lean badge.
    loc=lead['evidence']['locators'][0]
    add('\\noindent\\small Source: \\nolinkurl{'+loc['path']+'}, lines '+str(loc['start_line'])+'--'+str(loc['end_line'])+'.\\par\\normalsize\n')
    role('attribution',lead['attribution']+'~\\cite{'+','.join(ext['attribution_bibliography']['keys'])+'}')
    role('generality',lead['generality'])
    role('naturalness',lm['naturalness'])
    add('\\paragraph{The hard step.}')
    role('hard_step',lead['hard_step'])
    add('\\paragraph{Why the proof works.}')
    role('proof_outline',ext['proof_outline'])
    add('\\section{Relation to Erd\\H{o}s Problem '+str(dossier['problem'])+'}')
    role('problem_relation',ext['problem_relation'])
    add('\\section{Proof and companion record}')
    role('long_record_route',ext['long_record_route'])
    add('\\paragraph{Draft boundary.} This generated file contains an opening and a proof outline. The full proof must be incorporated and reviewed before this can be a standalone short paper.')
    add('\\section{Remaining question}')
    role('boundary',ext['boundary'])
    add('\\begin{thebibliography}{9}\n'+bibliography+'\n\\end{thebibliography}')
    add('\\end{document}')
    tex='\n'.join(lines)+'\n'
    mapping=dict(schema='short-paper-draft/1',paper_id=ext['paper_id'],lead_result_id=lead['id'],
                 draft_sha256=digest(tex),dossier_sha256=digest(canonical(dossier)),
                 evidence_sha256=digest(canonical(evidence)),blocks=blocks,
                 validation='deterministic rendering and source-span binding; no semantic or formal verification',
                 hypotheses=lm['hypotheses'],evidence_class=ev['evidence_class'],
                 target_relation=ext['target_relation'],selection_review=ext['selection_review'],
                 bibliography_source_sha256=digest(safe_path(root,ext['attribution_bibliography']['source']).read_bytes()))
    return tex,mapping


def verify_draft(tex: str, mapping: dict, dossier: dict, evidence: dict, root: Path) -> list[dict]:
    try: expected, expected_map=render(dossier,evidence,root)
    except Refusal as exc: return [finding('SP11','dossier',1,str(exc))]
    issues=[]
    if mapping != expected_map: issues.append(finding('SP09','draft.map.json',1,'role map does not replay from dossier'))
    if tex != expected: issues.append(finding('SP10','draft.tex',1,'draft changed outside the dossier; return edits to the owning fields'))
    return issues


def run_portfolio(root: Path, system_id: str='claim-faithful-publication-systems') -> dict:
    papers=[audit(root,p['paper_id'],p['path'],p['kind']) for p in portfolio(root,system_id)]
    counts=Counter(f['severity'] for p in papers for f in p['findings'])
    return dict(schema=SCHEMA,system_paper_id=system_id,papers=papers,
                summary=dict(papers=len(papers),assertions=sum(len(p['assertions']) for p in papers),
                             findings=dict(sorted(counts.items()))),
                rules=RULES,semantic_review=SEMANTIC_REVIEW,
                scope='literal TeX, canonical coverage bindings, visible recorded marks; no Lean, Comparator, model or cold-reader run')


def main(argv: list[str] | None=None) -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=ROOT)
    sub=parser.add_subparsers(dest='command',required=True)
    a=sub.add_parser('audit'); a.add_argument('--output',type=Path); a.add_argument('--system-id',default='claim-faithful-publication-systems')
    for name in ['draft','check-draft']:
        p=sub.add_parser(name);p.add_argument('--dossier',type=Path,required=True);p.add_argument('--evidence',type=Path,required=True);p.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args(argv)
    try:
        if args.command=='audit':
            value=run_portfolio(args.root,args.system_id)
            payload=json.dumps(value,indent=2,ensure_ascii=False)+'\n'
            if args.output: args.output.write_text(payload)
            else: print(payload,end='')
            return int(value['summary']['findings'].get('error',0)>0)
        d,e=read_json(args.dossier),read_json(args.evidence)
        if args.command=='draft':
            tex,mapping=render(d,e,args.root)
            # Refuse overwrite; no partial files are created for validation failures.
            if args.output_dir.exists(): raise Refusal('output-dir','already exists')
            args.output_dir.mkdir(parents=True)
            (args.output_dir/'draft.tex').write_text(tex)
            (args.output_dir/'draft.map.json').write_text(json.dumps(mapping,indent=2,ensure_ascii=False)+'\n')
            print(json.dumps({'status':'rendered_candidate','draft_sha256':mapping['draft_sha256']}));return 0
        issues=verify_draft((args.output_dir/'draft.tex').read_text(),read_json(args.output_dir/'draft.map.json'),d,e,args.root)
        print(json.dumps({'status':'findings' if issues else 'contract_checks_pass','findings':issues}));return int(bool(issues))
    except (Refusal,OSError,ValueError,TypeError,KeyError) as exc:
        print(json.dumps({'status':'generator_refusal','field':getattr(exc,'field','input'),'reason':str(exc)}));return 2


if __name__=='__main__': raise SystemExit(main())
