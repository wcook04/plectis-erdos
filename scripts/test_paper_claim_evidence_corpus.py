#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Pinned-corpus structural mutation probes; never run Lean, Comparator or models.

Run after applying the return: python3 scripts/test_paper_claim_evidence_corpus.py
Optional --output records the replay. Mutations exist only in the reader overlay.
The computed-attestation control is intentionally synthetic metadata on an actual
paper claim, not a newly admitted review or a claim to rerun its calculation.
"""
from __future__ import annotations
import argparse
from functools import lru_cache
import json
from pathlib import Path
import sys
import paper_claim_evidence as ce
import paper_evidence as pe

ROOT = Path(__file__).resolve().parents[1]
PIN = '5acddfb2d9b43ad1b876f25700c49b1c39beddde'


def run(root: Path) -> dict:
    from publication_contract import RepositoryReader
    repo = RepositoryReader(root, git_ref=PIN)
    read = lru_cache(maxsize=None)(repo.read_bytes)
    initial = ce.project(read, source_commit=PIN)
    results = []
    def record(name, ok, detail):
        results.append({'name':name,'passed':bool(ok),'detail':detail})
    rows = initial['rows']
    ledger=json.loads(read(pe.LEDGER))
    record('all_registered_claims_joined', set(r['id'] for r in rows)==set(r['id'] for r in ledger['rows']), initial['summary'])
    repeat=ce.project(read,source_commit=PIN)
    record('deterministic_pinned_regeneration',ce.canonical(initial)==ce.canonical(repeat),ce.digest(ce.canonical(initial)))
    multi=next(r for r in rows if r['binding_status']=='bound' and len(r['binding_extension']['declarations'])>1)
    record('multi_declaration_binding_lossless', multi['lean_declaration'] is None and len(multi['binding_extension']['declarations'])==len(next(r for r in ledger['rows'] if r['id']==multi['id'])['lean']['declarations']),multi['id'])
    alternate=[r['id'] for r in rows if any(d.get('comparator',{}).get('different_path_roles') for d in r['binding_extension']['declarations'])]
    record('native_solution_path_roles_preserved', bool(alternate) and not any(g['code']=='receipt_binding' for g in initial['gaps']), alternate)
    good=next(r for r in rows if r['binding_status']=='bound' and r['problem']==68)
    decl=good['binding_extension']['declarations'][0]['name']
    index=json.loads(read(ce.INDEX));index['nodes']=[n for n in index['nodes'] if n['handle']!=decl]
    def overlay(data):return lambda p:data[p] if p in data else read(p)
    probe=ce.project(overlay({ce.INDEX:ce.canonical(index)}),source_commit=PIN)
    record('real_declaration_index_omission_rejected',any(g['code']=='dependency_index' and g['claim_id']==good['id'] for g in probe['gaps']),good['id']+' / '+decl)
    path=good['binding_extension']['comparator_receipts'][0]
    rec=json.loads(read(path));rec['github']['run_id']='deliberately-wrong'
    probe=ce.project(overlay({path:ce.canonical(rec)}),source_commit=PIN)
    record('real_receipt_run_mismatch_rejected',any(g['code']=='receipt_binding' and g['claim_id']==good['id'] for g in probe['gaps']),path)
    cid='erdos-1041-lemniscate-newton-flow#res:low-critical-thirteen-twentyfifths'
    target=next(r for r in rows if r['id']==cid)
    # Bind the existing evidence remark as a bounded, *reported* computation source.
    # This tests that a computation-class record cannot authorize a proof claim.
    source='paper/1041/erdos-1041-lemniscate-newton-flow.tex'
    lines=read(source).decode().splitlines(keepends=True)
    start=next(i+1 for i,l in enumerate(lines) if '\\evidenceremark{No Lean proof covers the whole theorem' in l)
    end=start+4
    span=''.join(lines[start-1:end])
    claims=json.loads(read(ce.CLAIMS));claims[ce.POLICY_KEY]={'schema':ce.POLICY_SCHEMA,'nonformal_evidence':ce.ANN,'require_sixteen_papers':True,'status_assertions':{cid:['computed']}}
    ann={'schema':'plectis-nonformal-claim-evidence/1','rows':{cid:{'evidence_class':'computed','statement_hash':target['statement_hash'],
        'computation':{'path':source,'start_line':start,'end_line':end,'sha256':ce.digest(span.encode())},
        'domain':'synthetic attestation of the printed finite stopping-time report, not the general theorem',
        'command':'fixture only: no computation executed; inspect the recorded evidence remark','assumptions':[]}}}
    data={ce.CLAIMS:ce.canonical(claims),ce.ANN:ce.canonical(ann)}
    base=ce.project(overlay(data),source_commit=PIN)
    r=next(r for r in base['rows'] if r['id']==cid)
    record('actual_nonformal_paper_claim_supports_computed_control',r['binding_status']=='bound' and r['evidence_class']=='computed',{'claim_id':cid,'synthetic_metadata':True,'source_lines':[start,end]})
    claims[ce.POLICY_KEY]['status_assertions'][cid]=['proved']
    data[ce.CLAIMS]=ce.canonical(claims)
    bad=ce.project(overlay(data),source_commit=PIN)
    failures=[g for g in bad['gaps'] if g['claim_id']==cid and g['code']=='overstatement']
    record('real_paper_computed_to_proved_rejected',len(failures)==1, failures)
    del claims[ce.POLICY_KEY]['status_assertions'][cid]
    data[ce.CLAIMS]=ce.canonical(claims)
    data[source]=read(source)+b'\n\\claimstatus{res:low-critical-thirteen-twentyfifths}{proved}\n'
    bad=ce.project(overlay(data),source_commit=PIN)
    record('real_tex_status_request_rejected',any(g['claim_id']==cid and g['code']=='overstatement' for g in bad['gaps']),cid)
    source=good['claim_locator'].split(':',1)[0]
    raw=read(source)
    label=good['id'].split('#')[1].encode()
    needle=b'\\label{'+label+b'}'
    changed=raw.replace(needle,needle+b' DELIBERATELY CHANGED ASSERTION ',1)
    bad=ce.project(overlay({source:changed}),source_commit=PIN)
    record('real_paper_statement_edit_invalidates_binding',any(g['claim_id']==good['id'] and g['code']=='statement_missing' for g in bad['gaps']),good['id'])
    return {'schema':'claim-evidence-corpus-probes/1','source_commit':PIN,'passed':all(r['passed'] for r in results),
            'validation':'structural mutations only; no theorem proved or refuted','cases':results}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,default=ROOT);parser.add_argument('--output',type=Path);a=parser.parse_args()
    result=run(a.root)
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(ce.canonical(result))
    print(json.dumps(result,indent=2))
    return int(not result['passed'])
if __name__=='__main__':raise SystemExit(main())
