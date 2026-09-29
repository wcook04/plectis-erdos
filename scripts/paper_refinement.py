#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Source-frozen editorial exchange for the native short-paper writer.

The exchange records proposed edits. It never executes a returned program,
modifies the checkout, or confers mathematical or release acceptance.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import tempfile
import zipfile

SCHEMA = 'paper-refinement-packet/1'
MAX_MEMBER_BYTES = 32 * 1024 * 1024
MAX_TOTAL_BYTES = 128 * 1024 * 1024

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def relative(name: str) -> str:
    parts = name.split('/')
    if '\\' in name or any(p in {'', '.', '..'} for p in parts) or PurePosixPath(name).is_absolute():
        raise ValueError(f'Unsafe exchange path: {name}')
    return name

def read_archive(path: Path) -> dict[str, bytes]:
    out = {}
    total = 0
    with zipfile.ZipFile(path) as z:
        for item in z.infolist():
            if item.is_dir():
                continue
            name = relative(item.filename)
            if name in out:
                raise ValueError(f'Duplicate exchange member: {name}')
            if stat.S_ISLNK(item.external_attr >> 16):
                raise ValueError(f'Symlink exchange member: {name}')
            total += item.file_size
            if item.file_size > MAX_MEMBER_BYTES or total > MAX_TOTAL_BYTES:
                raise ValueError('Exchange exceeds the bounded input size')
            out[name] = z.read(item)
    return out

def freeze(root: Path, packet_id: str, sources: list[str], output: Path) -> dict:
    import short_paper_writer as writer
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', packet_id):
        raise ValueError('Packet id must be a filename-safe identifier')
    if not sources or len(set(sources)) != len(sources):
        raise ValueError('Choose unique manuscript sources')
    if output.exists():
        raise ValueError('Refusing to overwrite a frozen packet')
    files = {}
    for source in sources:
        relative(source)
        if not source.startswith('paper/') or not source.endswith('.tex'):
            raise ValueError('Editable sources must be paper TeX files')
        pairs, issues = writer.source_tree(root, source)
        if issues:
            raise ValueError(f'Incomplete manuscript input closure: {issues}')
        for name, _text in pairs:
            files[name] = writer.safe_path(root, name).read_bytes()
    # Carry the native rules and evidence with the manuscripts. These are
    # read-only inputs; returned edits cannot change them through this lane.
    for name in ('docs/paper_lean_coverage.json', 'docs/claims.json',
                 'docs/publication_contract.json', 'docs/claim_evidence.json',
                 'docs/short_paper_contract.json', 'paper/paper-house-style.sty',
                 'scripts/short_paper_writer.py', 'scripts/paper_refinement.py',
                 'scripts/check_lean_paper_propagation.py', 'scripts/migrate_statement_presentation.py',
                 'scripts/check_problem_note_sources.py', 'scripts/lean_source.py'):
        candidate = root/name
        if candidate.exists():
            files[name] = writer.safe_path(root, name).read_bytes()
    head = subprocess.run(['git','-C',str(root),'rev-parse','HEAD'], capture_output=True, text=True)
    manifest = {'schema': SCHEMA, 'packet_id': packet_id,
        'source_head': head.stdout.strip() if head.returncode == 0 else None,
        'source_authority': 'exact frozen file bytes; source_head is context, not a clean-tree assertion',
        'editable_paths': sources,
        'files': [{'path': p, 'sha256': sha(b)} for p,b in sorted(files.items())],
        'boundary': 'Editorial proposal exchange; mathematical relations, native integration, rendering and release require separate review.'}
    files['MANIFEST.json'] = (json.dumps(manifest,indent=2)+'\n').encode()
    files['RETURN.template.json'] = (json.dumps({'schema':'paper-refinement-return/1',
        'packet_id':packet_id,'input_manifest_sha256':sha(files['MANIFEST.json']),
        'edited_files':[{'path':p,'original_sha256':sha(files[p])} for p in sources],
        'statement_changes':[], 'validation':{}, 'limits':[]},indent=2)+'\n').encode()
    with zipfile.ZipFile(output,'x',compression=zipfile.ZIP_DEFLATED) as z:
        for name,data in sorted(files.items()):
            z.writestr(name,data)
    return {'status':'frozen','packet_id':packet_id,'files':len(files),
            'sha256':sha(output.read_bytes()),'editable_paths':sources}

def check_return(packet: Path, returned: Path) -> dict:
    import short_paper_writer as writer
    original, proposed = read_archive(packet), read_archive(returned)
    manifest = json.loads(original['MANIFEST.json'])
    if manifest.get('schema') != SCHEMA:
        raise ValueError('Unknown packet schema')
    for row in manifest['files']:
        if sha(original[row['path']]) != row['sha256']:
            raise ValueError('Packet input digest mismatch: '+row['path'])
    contract = json.loads(proposed['RETURN.json'])
    if (contract.get('schema') != 'paper-refinement-return/1'
        or contract.get('packet_id') != manifest['packet_id']
        or contract.get('input_manifest_sha256') != sha(original['MANIFEST.json'])):
        raise ValueError('Return identity does not match the frozen input')
    edits = contract.get('edited_files',[])
    paths = [r['path'] for r in edits]
    if not paths or len(set(paths)) != len(paths):
        raise ValueError('Return must name unique edited manuscripts')
    for row in edits:
        p = relative(row['path'])
        if p not in manifest['editable_paths'] or p not in proposed:
            raise ValueError('Unscoped edit: '+p)
        if row.get('original_sha256') != sha(original[p]):
            raise ValueError('Stale edit: '+p)
    for p in proposed.keys()-set(paths)-{'RETURN.json'}:
        if not (p.startswith(('validation/','audit/')) and Path(p).suffix in {'.json','.md','.txt','.log','.py'}):
            raise ValueError('Unexpected return member: '+p)
    changes = contract.get('statement_changes',[])
    if not isinstance(changes,list) or any(not isinstance(x,dict) or not all(x.get(k) for k in ('path','label','relation','reason')) for x in changes):
        raise ValueError('Statement changes need path, label, relation and review reason')
    findings = []
    # Audits run our native code, against inert source bytes in a temporary
    # overlay. No returned script is copied to the overlay or executed.
    with tempfile.TemporaryDirectory(prefix='paper-refinement-') as raw:
        root = Path(raw)
        for name,data in original.items():
            if name in {'MANIFEST.json','RETURN.template.json'}:
                continue
            target=root/relative(name);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        baseline = {p:writer.audit(root,Path(p).stem,p) for p in manifest['editable_paths']}
        for p in paths:
            (root/p).write_bytes(proposed[p])
        for p in manifest['editable_paths']:
            before,after = baseline[p],writer.audit(root,Path(p).stem,p)
            statements = lambda a:{x['labels'][0]:x['statement_sha256'] for x in a['assertions'] if x['labels']}
            old_statements,new_statements=statements(before),statements(after)
            changed={label for label in old_statements.keys()|new_statements.keys()
                     if old_statements.get(label)!=new_statements.get(label)}
            declared={x['label'] for x in changes if x['path']==p}
            if changed-declared:
                raise ValueError(f'Undeclared statement changes: {p}: {sorted(changed-declared)}')
            # A declared semantic change is still a review obligation, never
            # permission to bypass its native coverage failure.
            findings.append({'path':p,'baseline_findings':before['findings'],
                             'proposed_findings':after['findings']})
        for p in paths:
            old,new=original[p].decode(),proposed[p].decode()
            labels = lambda s:set(re.findall(r'\\(?:label|leanlabel)\{([^{}]+)\}',s))
            bib = lambda s:set(re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}',s))
            lost_labels=labels(old)-labels(new)
            lost_credit=bib(old)-bib(new)
            declarations={x['label'] for x in changes if x['path']==p}
            if lost_labels-declarations:
                raise ValueError(f'Undeclared lost labels: {p}: {sorted(lost_labels-declarations)}')
            if lost_credit:
                raise ValueError(f'Lost bibliography credit: {p}: {sorted(lost_credit)}')
            bib_entries = lambda s:{m[1]:m[2].strip() for m in re.finditer(
                r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}(.*?)(?=\\bibitem|\\end\{thebibliography\})',s,re.S)}
            old_bib,new_bib=bib_entries(old),bib_entries(new)
            if any(new_bib.get(k)!=v for k,v in old_bib.items()):
                raise ValueError('Changed frozen bibliography credit: '+p)
            citations = lambda s:{k.strip() for m in re.finditer(r'\\cite[a-zA-Z*]*(?:\[[^\]]*\])*\{([^{}]+)\}',s) for k in m[1].split(',')}
            if citations(old)-citations(new):
                raise ValueError('Lost original citation keys: '+p)
    errors=sum(f['severity']=='error' for paper in findings for f in paper['proposed_findings'])
    return {'status':'native_review_required' if errors or changes else 'transport_and_static_audit_pass',
        'packet_id':manifest['packet_id'],'findings':findings,'statement_changes':changes,
        'boundary':'No files applied; no proof, independent review, reader-benefit or release claim.'}
