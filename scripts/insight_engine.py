#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Read-only retrieval over the repository's authored mechanism records.

Canonical mechanism owner remains build_theory_lab.py / docs/semantic/lab.
Native graph owner remains query_continuations.py; we invoke it, never reimplement
its closure, implication, equivalence or cut algorithm. No journal is written.

Implemented: source binding, current-graph fail-closed preflight, two-way lexical
candidate retrieval, annex discovery and explicit proof-obligation plans. The
lexical index is a diagnostic baseline, NOT typed anti-unification or a novelty
oracle. All application output is a proposal, never a proved transfer. Optional
proposal catalogues are advisory inputs and cannot replace the native records.

Run only against reviewed local repository code. `native` executes that code in
an isolated Python subprocess; it never runs strings supplied by a model as code.
The caller, not a JSON field, is responsible for trusting the chosen checkout.
Python 3.10+; standard library only. Tests: test_insight_engine.py.
"""
from __future__ import annotations
import argparse
import collections
import gzip
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
from typing import Any, Iterable

VERSION = 'plectis-insight-proposal/1'
ROSTER = ('68', '243', '249', '251', '257', '269', '1041', '1049')
LIMIT = 256 * 1024 * 1024
SHA = re.compile(r'[0-9a-f]{64}\Z')
COMMIT = re.compile(r'[0-9a-f]{40}\Z')
STOP = set('a an the and or of to for from in is as by be has have this that with at on true false theorem lemma def let fun forall exists nat real int'.split())

class InputError(ValueError):
    pass

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def canonical(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()

def regular_path(root: Path, relative: str) -> Path:
    """No absolute paths, traversal or symlinks. Only frozen, trusted local inputs."""
    p = PurePosixPath(relative)
    if not relative or p.is_absolute() or '\\' in relative or '..' in p.parts:
        raise InputError(f'unsafe relative path: {relative!r}')
    root = root.resolve(strict=True)
    result = root
    for part in p.parts:
        result = result / part
        if result.is_symlink():
            raise InputError(f'symlink input refused: {relative}')
    if not result.is_file():
        raise InputError(f'missing regular file: {relative}')
    return result

def read_bytes(path: Path, limit: int = LIMIT) -> bytes:
    if path.is_symlink() or not path.is_file():
        raise InputError(f'not a regular non-symlink file: {path}')
    with path.open('rb') as f:
        data = f.read(limit + 1)
    if len(data) > limit:
        raise InputError('input exceeds configured byte budget')
    return data

def read_json(path: Path, limit: int = LIMIT) -> Any:
    data = read_bytes(path, limit)
    if path.suffix == '.gz':
        import io
        with gzip.GzipFile(fileobj=io.BytesIO(data)) as f:
            data = f.read(limit + 1)
        if len(data) > limit:
            raise InputError('decompressed input exceeds configured byte budget')
    try:
        return json.loads(data, parse_constant=lambda x: (_ for _ in ()).throw(InputError(f'nonfinite JSON {x}')))
    except (ValueError, UnicodeError) as e:
        raise InputError(f'invalid JSON: {path}: {e}') from e

def tokenise(text: str) -> set[str]:
    # Presentation-level retrieval only: never used for statement identity.
    text = re.sub(r'([a-z0-9])([A-Z])', r'\1 \2', text)
    return {s.lower() for s in re.findall(r'[A-Za-z][A-Za-z0-9]*', text)
            if len(s) > 2 and s.lower() not in STOP}

def world(module: str) -> str:
    m = re.search(r'/Erdos(1041|1049|243|249|251|257|269|68)(?:/|\.)', module)
    return m.group(1) if m else 'shared_or_unattributed'

def atlas(root: Path) -> list[dict[str, Any]]:
    obj = read_json(regular_path(root, 'docs/declaration_atlas.json'))
    rows = obj.get('declarations')
    if not isinstance(rows, list):
        raise InputError('atlas declarations must be a list')
    keys = set()
    for row in rows:
        key = (row.get('module'), row.get('name'), row.get('line'))
        if key in keys:
            raise InputError(f'duplicate atlas coordinate: {key}')
        keys.add(key)
    return rows

def resolve(rows: list[dict[str, Any]], name: str, module: str | None = None) -> dict[str, Any]:
    found = [r for r in rows if r['name'] == name and (module is None or r['module'] == module)]
    if len(found) != 1:
        raise InputError(f'declaration is absent or ambiguous: {module}:{name} ({len(found)} matches)')
    return found[0]

def span(root: Path, ref: dict[str, Any]) -> dict[str, Any]:
    path = regular_path(root, ref['path'])
    data = read_bytes(path)
    lines = data.decode('utf-8').splitlines(keepends=True)
    lo, hi = ref['start'], ref['end']
    if type(lo) is not int or type(hi) is not int or not 1 <= lo <= hi <= len(lines):
        raise InputError(f'invalid line range: {ref}')
    body = ''.join(lines[lo-1:hi]).encode()
    actual = {'path':ref['path'], 'start':lo, 'end':hi,
              'file_sha256':sha(data), 'span_sha256':sha(body)}
    for key in ('file_sha256', 'span_sha256'):
        if key in ref and (not SHA.fullmatch(ref[key]) or ref[key] != actual[key]):
            raise InputError(f'source drift: {ref["path"]}:{lo}-{hi} {key}')
    return actual

def catalogue(path: Path, root: Path | None = None) -> list[dict[str, Any]]:
    obj = read_json(path)
    if obj.get('schema') != VERSION or not isinstance(obj.get('records'), list):
        raise InputError('unrecognised proposal catalogue')
    seen = set()
    for r in obj['records']:
        mid = r.get('mechanism_id')
        if not isinstance(mid, str) or not mid or mid in seen:
            raise InputError('missing or duplicate mechanism id')
        seen.add(mid)
        if r.get('authority') != 'proposal_not_canonical':
            raise InputError('proposal catalogue cannot grant canonical authority')
        if r.get('novelty') != 'not_assessed':
            raise InputError('proposal catalogue cannot award novelty')
        required = r.get('requirements')
        if not isinstance(required, list) or not required:
            raise InputError('mechanism must expose obligations')
        ids = [x.get('id') for x in required]
        if any(not isinstance(x, str) or not x for x in ids) or len(set(ids)) != len(ids):
            raise InputError('invalid or duplicate obligation id')
        for ref in r.get('sources', []):
            if not all(k in ref for k in ('file_sha256', 'span_sha256')):
                raise InputError('unbound source in catalogue')
            if root is not None:
                span(root, ref)
    return obj['records']

def native_catalogue(root: Path) -> list[dict[str, Any]]:
    """Bind retrieval to the authored lab and its current generated receipt."""
    lab = read_json(regular_path(root, 'docs/theory_lab.json'))
    source = read_bytes(regular_path(root, 'docs/semantic/lab/mechanisms.json'))
    atlas_bytes = read_bytes(regular_path(root, 'docs/declaration_atlas.json'))
    provenance = lab.get('source_provenance', {})
    expected = provenance.get('authored_lab_source_digests', {}).get(
        'docs/semantic/lab/mechanisms.json')
    if expected != 'sha256:' + sha(source) or provenance.get(
            'declaration_atlas_digest') != 'sha256:' + sha(atlas_bytes):
        raise InputError('theory lab projection is stale against authored mechanisms or atlas')
    authored = read_json(root / 'docs/semantic/lab/mechanisms.json')
    if not isinstance(authored, list) or lab.get('mechanisms') != authored:
        raise InputError('theory lab mechanisms differ from authored records')
    declarations = atlas(root)
    by_name: dict[str, set[str]] = collections.defaultdict(set)
    for row in declarations:
        by_name[row['name']].add(row['module'])
    records = []
    for row in authored:
        mid = row['mechanism_id']
        requirements = [
            {'id': 'claim_ceiling', 'statement': row['claim_ceiling']},
            *[{'id': f'failure_{i}', 'statement': failure}
              for i, failure in enumerate(row.get('sharp_failures', []), 1)],
            *[{'id': f'declaration_{i}',
               'statement': f'Check the exact source declaration and target bridge: {name}'}
              for i, name in enumerate(row.get('realising_declarations', []), 1)],
        ]
        origin = sorted({module for name in row.get('realising_declarations', [])
                         for module in by_name.get(name, ())})
        records.append({**row, 'authority': 'authored_mechanism_explanation',
                        'novelty': 'not_assessed', 'requirements': requirements,
                        'search_query': ' '.join(str(row.get(key, '')) for key in (
                            'human_name', 'core_idea', 'invariant', 'transformation',
                            'observable_controlled')),
                        'origin_modules': origin,
                        'authored_source_sha256': sha(source)})
    return records

def reference(root: Path, row: dict[str, Any]) -> dict[str, Any]:
    data = read_bytes(regular_path(root, row['module']))
    lines = data.decode().splitlines()
    ln = row['line']
    if type(ln) is not int or not 1 <= ln <= len(lines):
        raise InputError(f'atlas source coordinate mismatch: {row["id"]}')
    name_line = ln
    if row['name'] not in lines[ln-1]:
        # The atlas records the declaration keyword; Lean may put its name on
        # the following line. Keep that exact, bounded source relationship.
        if (lines[ln-1].strip() != row['kind'] or ln == len(lines)
                or row['name'] not in lines[ln]):
            raise InputError(f'atlas source coordinate mismatch: {row["id"]}')
        name_line = ln + 1
    return {'path':row['module'], 'line':ln, 'name':row['name'],
            'name_line':name_line,
            'signature':row['signature'], 'signature_sha256':sha(row['signature'].encode()),
            'file_sha256':sha(data), 'evidence':'source_and_atlas_navigation_not_kernel_replay'}

def retrieve(rows: list[dict[str, Any]], query: str, *, k: int = 12,
             allowed_worlds: Iterable[str] = (), exclude_modules: Iterable[str] = (),
             per_module: int = 2) -> list[dict[str, Any]]:
    """Deterministic inverse-document-frequency overlap baseline, not semantic proof."""
    if not 1 <= k <= 100 or not 1 <= per_module <= 100:
        raise InputError('retrieval limits must lie in 1..100')
    q = tokenise(query)
    if not q:
        return []
    worlds, excluded = set(allowed_worlds), set(exclude_modules)
    docs = []
    df: collections.Counter[str] = collections.Counter()
    for r in rows:
        if r.get('generated_certificate') or r['module'] in excluded:
            continue
        if worlds and world(r['module']) not in worlds:
            continue
        terms = tokenise(' '.join(str(r.get(f, '')) for f in ('name','signature','docstring')))
        df.update(terms & q)
        docs.append((r, terms))
    result = []
    for r, terms in docs:
        hit = q & terms
        if not hit:
            continue
        score = sum(math.log(1 + (len(docs)+1)/(1+df[t])) for t in hit) / math.sqrt(1 + len(terms)/25)
        result.append({'row':r, 'retrieval_score':round(score, 8), 'matched_terms':sorted(hit)})
    result.sort(key=lambda x: (-x['retrieval_score'], x['row']['module'], x['row']['line'], x['row']['name']))
    kept, counts = [], collections.Counter()
    for x in result:
        m = x['row']['module']
        if counts[m] >= per_module:
            continue
        counts[m] += 1
        kept.append(x)
        if len(kept) == k:
            break
    return kept

def forward(root: Path, records: list[dict[str, Any]], mid: str, *, k: int = 12,
            worlds: Iterable[str] = (), exclude_origin: bool = False) -> dict[str, Any]:
    matching = [x for x in records if x['mechanism_id'] == mid]
    if len(matching) != 1:
        raise InputError(f'unknown mechanism: {mid}')
    rec = matching[0]
    worlds = tuple(worlds)
    excluded = rec.get('origin_modules', []) if exclude_origin else []
    hits = retrieve(atlas(root), rec['search_query'], k=k,
                    allowed_worlds=worlds, exclude_modules=excluded)
    return {'schema':VERSION, 'mechanism_id':mid,
            'status':'retrieval_only', 'verified_transfers':0,
            'query':rec['search_query'], 'exclude_origin_modules':list(excluded),
            'allowed_worlds':list(worlds), 'limit':k, 'per_module_limit':2,
            'atlas_sha256':sha(read_bytes(root/'docs/declaration_atlas.json')),
            'mechanism_record_sha256':sha(canonical(rec)),
            'interpretation':'Ranks source spans to inspect; no hit entails applicability, non-applicability or novelty.',
            'candidates':[{'source':reference(root,h['row']), 'world':world(h['row']['module']),
                           'retrieval_score':h['retrieval_score'], 'matched_terms':h['matched_terms'],
                           'next':'supply a typed source-to-consumer map and discharge the mechanism requirements',
                           'requirements_pending':[r['id'] for r in rec['requirements']]}
                          for h in hits]}

def reverse(root: Path, records: list[dict[str, Any]], query: str) -> dict[str, Any]:
    """Search native and explicitly supplied proposal records together."""
    q = tokenise(query)
    candidates=[]
    for r in records:
        text=' '.join(str(r.get(f,'')) for f in ('human_name','core_idea','invariant','transformation','search_query'))
        hits=q & tokenise(text)
        if hits:
            origin = ('native_theory_lab' if r['authority'] == 'authored_mechanism_explanation'
                      else 'proposed_extension')
            candidates.append({'mechanism_id':r['mechanism_id'], 'owner':origin,
                               'matched_terms':sorted(hits), 'retrieval_score':len(hits),
                               'applicability':'unestablished', 'novelty':'not_assessed'})
    candidates.sort(key=lambda x:(-x['retrieval_score'],x['mechanism_id']))
    return {'schema':VERSION,'status':'retrieval_only','query':query,'candidates':candidates,
            'interpretation':'Description-token overlap only. No-match does not imply no applicable mechanism.'}

def obligation_plan(record: dict[str, Any], target: dict[str, Any], mapping: dict[str, str]) -> dict[str, Any]:
    """A model supplies expressions as inert strings; none can discharge a proof."""
    for key in ('source_id','context','target_statement'):
        if not isinstance(target.get(key),str) or not target[key].strip():
            raise InputError(f'missing target {key}')
    if not all(isinstance(k,str) and isinstance(v,str) for k,v in mapping.items()):
        raise InputError('mapping must contain inert string names and expressions')
    requirements = [{'id':r['id'], 'statement':r['statement'], 'verdict':'unestablished',
                     'why':'a source span or string substitution is not a target proof'} for r in record['requirements']]
    return {'schema':VERSION,'mechanism_id':record['mechanism_id'],'target':target,'proposed_map':mapping,
            'scope_status':'needs_elaborated_telescope_and_instance_map',
            'requirements':requirements,'endpoint_bridge':'unestablished',
            'context_feasibility':'unestablished','target_to_residual':'unestablished',
            'state':'candidate_only','verified_transfer':False,'novelty':'not_assessed'}

def graph_preflight(root: Path, graph: Path, snapshot_commit: str | None) -> dict[str, Any]:
    p=read_json(graph); src=p.get('source',{})
    problems=[]
    rev=src.get('source_revision')
    if not isinstance(rev,str) or not COMMIT.fullmatch(rev):
        problems.append('graph_source_revision_is_not_a_full_commit')
    if snapshot_commit is None or not COMMIT.fullmatch(snapshot_commit):
        problems.append('snapshot_commit_not_bound')
    elif rev != snapshot_commit:
        problems.append('graph_revision_does_not_match_requested_snapshot')
    toolchain=read_bytes(regular_path(root,'lean-toolchain')).decode().strip()
    exported_version=src.get('lean_version')
    if exported_version not in (toolchain,toolchain.split(':v')[-1]):
        problems.append('lean_version_mismatch_or_missing')
    # A ZIP loses Git executable modes and may select paths. No invented Git tree.
    current_tree=None
    if (root/'.git').exists():
        try:
            c=subprocess.run(['git','rev-parse','HEAD'],cwd=root,text=True,capture_output=True,timeout=10,check=False)
            d=subprocess.run(['git','status','--porcelain'],cwd=root,text=True,capture_output=True,timeout=10,check=False)
            t=subprocess.run(['git','rev-parse','HEAD:lean'],cwd=root,text=True,capture_output=True,timeout=10,check=False)
            if c.returncode or d.returncode or t.returncode or d.stdout.strip() or c.stdout.strip()!=snapshot_commit:
                problems.append('checkout_not_clean_exact_snapshot')
            else:
                current_tree=t.stdout.strip()
                if src.get('lean_tree')!=current_tree:
                    problems.append('graph_lean_tree_mismatch')
        except (OSError,subprocess.TimeoutExpired):
            problems.append('git_identity_unavailable')
    else:
        problems.append('archive_has_no_git_tree_or_clean_checkout_attestation')
    # Equality of commit/tree/version is consistency, not producer authenticity.
    return {'graph_file_sha256':sha(read_bytes(graph)), 'source_revision':rev,
            'requested_snapshot':snapshot_commit,'graph_lean_tree':src.get('lean_tree'),
            'checkout_lean_tree':current_tree,'lean_toolchain':toolchain,
            'status':'blocked_current_graph' if problems else 'identity_consistent_requires_trusted_export',
            'reasons':problems,'proof_authority':'none_from_this_preflight',
            'counts':{k:len(p.get(k,[])) for k in ('statements','reductions','refutations','generalisations','budget_exhausted')}}

def inspect(root: Path, graph: Path | None, snapshot: str | None) -> dict[str, Any]:
    lab=read_json(regular_path(root,'docs/theory_lab.json'))
    missing=[str(p) for p in ('docs/semantic_corpus.json.gz',*[f'docs/semantic/lab/{s}.json' for s in
             ('mechanisms','capsules','interventions','receipts','benchmark_items','benchmark_results')]) if not (root/p).is_file()]
    at=read_bytes(regular_path(root,'docs/declaration_atlas.json'))
    return {'schema':VERSION,'evidence_scope':'checkout_files_not_kernel_proof',
            'theory_lab_summary':lab['summary'],
            'atlas_matches_lab_input_digest':lab['source_provenance']['declaration_atlas_digest']=='sha256:'+sha(at),
            'missing_canonical_inputs':missing,
            'graph':graph_preflight(root,graph,snapshot) if graph else None}

def native(root: Path, graph: Path, snapshot: str | None, action: str, keys: list[str],
           target: str | None = None, *, historical: bool=False, timeout: int=90) -> dict[str, Any]:
    """Only existing native commands; current execution stays blocked without trust integration."""
    pre=graph_preflight(root,graph,snapshot)
    if not historical:
        return {'status':'blocked_current_graph','preflight':pre,
                'reason':'Production owner must validate the export receipt. This prototype has no authority-promotion override.'}
    cmd=[sys.executable,'-I',str(regular_path(root,'scripts/query_continuations.py')),
         '--graph',str(graph.resolve())]
    if action=='transfer':
        cmd+=['transfer','--limit','12']
    elif action=='bundle':
        if not keys:
            raise InputError('bundle needs nonempty exact statement keys')
        cmd+=['check-bundle',*keys,'--max-work','200000']
        if target: cmd+=['--target',target]
    else:
        raise InputError('native action not allowlisted')
    env={k:v for k,v in os.environ.items() if k not in ('PYTHONPATH','PYTHONHOME','PYTHONSTARTUP')}
    env['PYTHONDONTWRITEBYTECODE']='1'
    try:
        c=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True,timeout=timeout,check=False)
    except subprocess.TimeoutExpired:
        return {'status':'unknown_budget','evidence_scope':'historical_only','timeout_seconds':timeout,
                'preflight':pre,'novelty':'not_assessed'}
    return {'status':'historical_native_output' if c.returncode==0 else 'native_error',
            'evidence_scope':'historical_only_not_current_or_new_math', 'preflight':pre,
            'exit_code':c.returncode,
            'native_script_sha256':sha(read_bytes(root/'scripts/query_continuations.py')),
            'native_output':json.loads(c.stdout) if c.returncode==0 else None,
            'stderr_tail':c.stderr[-4000:]}

def annex_search(root: Path, query: str, k: int=10) -> dict[str, Any]:
    if not 1<=k<=100: raise InputError('annex result limit out of range')
    q=tokenise(query); hits=[]; count=0
    for path in sorted(root.glob('*/annex_family.json')):
        relative=path.relative_to(root).as_posix(); regular_path(root,relative)
        o=read_json(path,2*1024*1024); count+=1
        text=' '.join(str(o.get(f,'')) for f in ('display_name','description','tags'))
        match=q & tokenise(text)
        if match:
            hits.append({'slug':o.get('slug'), 'title':o.get('display_name'), 'url':o.get('source',{}).get('url'),
                         'matched_terms':sorted(match), 'retrieval_score':len(match),
                         'metadata_sha256':sha(read_bytes(path)), 'evidence':'annex_metadata_not_theorem_review'})
    hits.sort(key=lambda h:(-h['retrieval_score'],str(h['slug'])))
    return {'status':'literature_discovery_only','metadata_records_examined':count,'query':query,'hits':hits[:k]}

def main(argv: list[str] | None=None) -> int:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument('--catalogue',type=Path,
                   help='optional advisory proposal catalogue; native mechanisms remain primary')
    s=p.add_subparsers(dest='cmd',required=True)
    a=s.add_parser('inspect'); a.add_argument('--graph',type=Path);a.add_argument('--snapshot')
    a=s.add_parser('forward');a.add_argument('mechanism');a.add_argument('--world',choices=ROSTER,action='append',default=[]);a.add_argument('--exclude-origin',action='store_true');a.add_argument('--limit',type=int,default=12)
    a=s.add_parser('reverse');a.add_argument('query')
    a=s.add_parser('annex');a.add_argument('query');a.add_argument('--annex-root',type=Path,required=True)
    a=s.add_parser('native');a.add_argument('--graph',type=Path,required=True);a.add_argument('--snapshot');a.add_argument('--historical',action='store_true');a.add_argument('--action',choices=['transfer','bundle'],default='transfer');a.add_argument('--key',action='append',default=[]);a.add_argument('--target')
    args=p.parse_args(argv)
    try:
        root=args.repo.resolve(strict=True)
        if args.cmd=='inspect': result=inspect(root,args.graph,args.snapshot)
        elif args.cmd=='annex':result=annex_search(args.annex_root,args.query)
        elif args.cmd=='native':result=native(root,args.graph,args.snapshot,args.action,args.key,args.target,historical=args.historical)
        else:
            records=native_catalogue(root)
            if args.catalogue:
                proposals=catalogue(args.catalogue,root)
                native_ids={r['mechanism_id'] for r in records}
                if any(r['mechanism_id'] in native_ids for r in proposals):
                    raise InputError('proposal catalogue duplicates native mechanism identity')
                records += proposals
            if args.cmd=='forward':result=forward(root,records,args.mechanism,k=args.limit,worlds=args.world,exclude_origin=args.exclude_origin)
            else:result=reverse(root,records,args.query)
        print(json.dumps(result,indent=2,ensure_ascii=False,allow_nan=False))
        return 0
    except (InputError,OSError,KeyError,TypeError,ValueError) as e:
        print(json.dumps({'status':'input_error','error':str(e)}),file=sys.stderr)
        return 2
if __name__=='__main__':
    raise SystemExit(main())
