#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Validate a research return and propose a bounded reconciliation plan.

The caller supplies the custody tool and its verified receipt; research_record
owns the public journal. This module creates neither store and never accepts
mathematical claims, executes returned programs, applies patches, or mutates a
repository.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
import hashlib
import io
import json
import re
import stat
import unicodedata
from pathlib import Path, PurePosixPath
import zipfile
from typing import Any, Mapping, Sequence

IDENT = re.compile(r'^[A-Za-z0-9][A-Za-z0-9_.-]*$')
HEX64 = re.compile(r'^[0-9a-f]{64}$')
HEX40 = re.compile(r'^[0-9a-f]{40}$')
BINDING_FIELDS = {'wave_id','round_id','packet_id','source_commit','baseline_sha256','arm','dispatch_id'}
REQUIRED_FILES = {'REPORT.md','SOURCES.md'}

class ReturnError(ValueError):
    pass

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReturnError(message)

def canonical(value: Any) -> bytes:
    return (json.dumps(value,sort_keys=True,ensure_ascii=False,separators=(',',':'),allow_nan=False)+'\n').encode()

def sha(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()

def ident(value: Any) -> bool:
    return isinstance(value,str) and IDENT.fullmatch(value) is not None

def text(value: Any) -> bool:
    return isinstance(value,str) and bool(value.strip())

def path_name(name: Any) -> str:
    require(isinstance(name,str) and bool(name), 'empty/nonstring member path')
    require(not name.startswith('/') and '\\' not in name and ':' not in name,'nonportable member path')
    require(all(ord(c)>=32 and ord(c)!=127 for c in name),'control character in path')
    require(unicodedata.normalize('NFC',name)==name,'member path must be NFC')
    require(len(name)<=240,'member path too long')
    for part in name.split('/'):
        require(part not in ('','.','..') and not part.endswith((' ','.')),'unsafe path component')
    return str(PurePosixPath(name))

def validate_bindings(b: Any) -> None:
    require(isinstance(b,dict) and set(b)==BINDING_FIELDS,'binding fields do not match contract')
    for key in ('wave_id','round_id','packet_id'):
        require(ident(b[key]),f'invalid binding {key}')
    require(isinstance(b['source_commit'],str) and HEX40.fullmatch(b['source_commit']) is not None,
            'invalid source_commit')
    for key in ('baseline_sha256','dispatch_id'):
        require(isinstance(b[key],str) and HEX64.fullmatch(b[key]) is not None,f'invalid {key}')
    require(b['arm'] in ('informed','blind_route'),'invalid arm')

def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in out, f'duplicate JSON key: {key}')
        out[key] = value
    return out

def validate_return(path: Path, expected: Mapping[str, Any], *, max_members: int=256,
                    max_member_bytes: int=8_000_000, max_total_bytes: int=32_000_000) -> dict[str, Any]:
    """Bounded, read-only ZIP validation. No extraction and no nested archives.

    Expected bindings must come from the frozen dispatch, NOT from the return.
    The envelope has hashes for every other file; it does not hash itself.
    The outer ZIP digest supplies full-byte custody identity without a hash cycle.
    """
    validate_bindings(dict(expected))
    require(path.is_file() and not path.is_symlink(),'return must be a regular non-symlink file')
    require(path.stat().st_size<=max_total_bytes,'compressed return exceeds ingress budget')
    raw_zip=path.read_bytes()
    files: dict[str,bytes]={}
    keys:set[str]=set()
    total=0
    try:
        with zipfile.ZipFile(io.BytesIO(raw_zip)) as z:
            require(len(z.infolist())<=max_members,'too many ZIP members')
            for item in z.infolist():
                # Explicit directory entries are harmless, but still budgeted/collision-checked.
                name=path_name(item.filename.rstrip('/') if item.is_dir() else item.filename)
                key=name.casefold()
                require(key not in keys,f'duplicate/case-colliding ZIP member: {name}')
                keys.add(key)
                mode=(item.external_attr>>16)&0xffff
                require(not stat.S_ISLNK(mode),f'symlink member: {name}')
                kind=stat.S_IFMT(mode)
                require(kind in (0,stat.S_IFREG,stat.S_IFDIR),f'special file member: {name}')
                require(not item.flag_bits&1,'encrypted ZIP member refused')
                require(item.compress_type in (zipfile.ZIP_STORED,zipfile.ZIP_DEFLATED),
                        'unsupported compression method')
                if item.is_dir():
                    continue
                require(kind!=stat.S_IFDIR,'file marked as directory')
                require(item.file_size<=max_member_bytes,'member exceeds declared size budget')
                with z.open(item) as stream:
                    body=stream.read(max_member_bytes+1)
                require(len(body)<=max_member_bytes and len(body)==item.file_size,'member size mismatch/budget')
                total+=len(body)
                require(total<=max_total_bytes,'expanded ZIP exceeds budget')
                require(Path(name).suffix.lower() not in ('.zip','.gz','.tgz','.tar','.xz','.7z') and
                        not body.startswith((b'PK\x03\x04',b'\x1f\x8b',b'7z\xbc\xaf\x27\x1c')),
                        f'nested archive refused: {name}')
                files[name]=body
    except (zipfile.BadZipFile,RuntimeError,OSError) as exc:
        raise ReturnError(f'invalid ZIP: {exc}') from exc
    require('RETURN.json' in files,'RETURN.json missing at ZIP root')
    require(len(files['RETURN.json'])<=1_000_000,'RETURN.json exceeds metadata budget')
    try:
        envelope=json.loads(files['RETURN.json'], object_pairs_hook=unique_object)
    except (ValueError,UnicodeDecodeError) as exc:
        raise ReturnError('RETURN.json is not UTF-8 JSON') from exc
    require(isinstance(envelope,dict) and
            set(envelope)=={'schema','return_id','bindings','artifacts','components','limitations'},
            'unexpected/missing return envelope fields')
    require(envelope['schema']=='plectis-research-return/1','wrong return schema')
    require(ident(envelope['return_id']),'invalid return_id')
    validate_bindings(envelope['bindings'])
    require(envelope['bindings']==dict(expected),'wrong packet/baseline/source/arm binding')
    artifacts=envelope['artifacts']
    require(isinstance(artifacts,dict),'artifacts must be a file-hash map')
    require(set(artifacts)==set(files)-{'RETURN.json'},'undeclared or missing artifact')
    require(REQUIRED_FILES<=set(artifacts),'REPORT.md and SOURCES.md are required')
    for name,meta in artifacts.items():
        path_name(name)
        require(isinstance(meta,dict) and set(meta)=={'sha256','bytes'},f'bad metadata for {name}')
        require(type(meta['bytes']) is int and meta['bytes']==len(files[name]),f'byte mismatch: {name}')
        require(meta['sha256']==sha(files[name]),f'digest mismatch: {name}')
    components=envelope['components']
    require(isinstance(components,list) and len(components)<=128,'components must be a bounded list')
    seen:set[str]=set()
    fields={'id','kind','statement','scope','polarity','depends_on','owner_paths','evidence_paths'}
    for c in components:
        require(isinstance(c,dict) and set(c)==fields,'bad component fields')
        require(ident(c['id']) and c['id'] not in seen,'duplicate/invalid component id')
        seen.add(c['id'])
        require(c['kind'] in ('code','statement','experiment','paper'),'bad component kind')
        require(text(c['statement']) and text(c['scope']),'component must state its claim and scope')
        require(c['polarity'] in ('asserts','denies'),'polarity must be asserts or denies')
        for field in ('depends_on','owner_paths','evidence_paths'):
            values=c[field]
            require(isinstance(values,list) and all(text(v) for v in values) and len(values)==len(set(values)),
                    f'bad component {field}')
        for name in c['owner_paths']:
            path_name(name)
        for name in c['evidence_paths']:
            require(name in artifacts,f'component cites an absent evidence file: {name}')
    require(isinstance(envelope['limitations'],list) and all(text(x) for x in envelope['limitations']),
            'limitations must be an explicit list')
    for name in REQUIRED_FILES:
        try: files[name].decode('utf-8')
        except UnicodeDecodeError as exc: raise ReturnError(f'{name} must be UTF-8') from exc
    # Return full preserved authored claims, never an accepted/correct boolean.
    return {'status':'integrity_checked_not_accepted','zip_sha256':sha(raw_zip),'zip_bytes':len(raw_zip),
            'expanded_bytes':total,'envelope':envelope}

def reconciliation_plan(returns: Sequence[Mapping[str,Any]]) -> dict[str,Any]:
    """Deterministic candidate grouping, conflict quarantine and dependency order.

    Exact authored text is a TRIAGE key, not a semantic/proof equivalence test.
    Dependencies may be local component IDs or fully-qualified return_id:component_id.
    One wave/source/baseline is required; mixed baselines need a fresh explicit wave.
    """
    if not returns:
        return {'state':'empty','integration_layers':[],'acceptance':'none'}
    wavekeys=set()
    ids:dict[str,str]={}
    raw_groups:dict[str,list[str]]=defaultdict(list)
    components:dict[str,dict[str,Any]]={}
    claims:dict[str,list[str]]=defaultdict(list)
    owners:dict[str,list[str]]=defaultdict(list)
    for returned in returns:
        require(returned.get('status')=='integrity_checked_not_accepted','validate returns before planning')
        e=returned['envelope']; b=e['bindings']; rid=e['return_id']
        wavekeys.add((b['wave_id'],b['source_commit'],b['baseline_sha256']))
        require(rid not in ids or ids[rid]==returned['zip_sha256'],'return_id reused with different bytes')
        if rid in ids:
            raw_groups[returned['zip_sha256']].append(rid)
            continue
        ids[rid]=returned['zip_sha256']
        raw_groups[returned['zip_sha256']].append(rid)
        for c in e['components']:
            cid=f'{rid}:{c["id"]}'
            component=dict(c)
            component['depends_on']=[d if ':' in d else f'{rid}:{d}' for d in c['depends_on']]
            components[cid]=component
            key=sha(canonical({'source_commit':b['source_commit'],'statement':c['statement'],'scope':c['scope']}))
            claims[key].append(cid)
            for owner in c['owner_paths']:
                owners[owner].append(cid)
    require(len(wavekeys)==1,'mixed wave/source/baseline cannot be silently reconciled')
    missing={cid:sorted(set(c['depends_on'])-set(components)) for cid,c in components.items()
             if set(c['depends_on'])-set(components)}
    conflicts=[]
    blocked=set(missing)
    for same in claims.values():
        if len({components[c]['polarity'] for c in same})>1:
            conflicts.append(sorted(same)); blocked.update(same)
    changed=True
    while changed:
        changed=False
        for cid,c in components.items():
            if cid not in blocked and set(c['depends_on'])&blocked:
                blocked.add(cid); changed=True
    pending=set(components)-blocked
    done:set[str]=set()
    layers=[]
    while pending:
        ready=sorted(c for c in pending if set(components[c]['depends_on'])<=done)
        if not ready: break
        layers.append(ready); done.update(ready); pending.difference_update(ready)
    return {'state':'plan_only_no_acceptance',
            'wave':list(next(iter(wavekeys))),
            'exact_zip_repeat_groups':[v for v in raw_groups.values() if len(v)>1],
            'identical_authored_statement_groups':[sorted(v) for v in claims.values() if len(v)>1],
            'group_meaning':'review candidates only; not semantic deduplication or novelty credit',
            'opposite_authored_claim_groups':conflicts,
            'missing_dependencies':missing,'blocked_by_missing_or_conflict':sorted(blocked),
            'cycle_or_dependent_on_cycle':sorted(pending),
            'integration_layers':layers,
            'serialize_owner_paths':{k:sorted(v) for k,v in sorted(owners.items()) if len(v)>1},
            'acceptance':'none; Type A reviews scope, evidence and native checks before journal dispositions'}

def custody_plan(source: Path, *, arrival_id: str, batch_id: str,
                 bindings: Mapping[str, Any], intake_script: Path, python: str='python3') -> dict[str,Any]:
    """Plan opaque byte custody BEFORE interpreting RETURN.json or its claims.

    arrival_id is assigned by Type A, not extracted from untrusted prose. This
    reads only the outer bytes for a digest. Native custody does the copying.
    Execute serially; verify native custody, then validate the preserved copy.
    """
    require(ident(arrival_id) and ident(batch_id),'invalid trusted arrival/batch id')
    validate_bindings(dict(bindings))
    require(source.is_file() and not source.is_symlink(),'regular source file required')
    require(source.stat().st_size <= 32_000_000,'opaque arrival exceeds this profile budget')
    raw=source.read_bytes()
    script=str(intake_script)
    commands=[
        [python,script,'open','--batch-id',batch_id,'--campaign',bindings['wave_id'],
         '--evidence-boundary','Exact returned bytes; custody is not scientific acceptance.',
         '--expected-more','yes'],
        [python,script,'add','--batch-id',batch_id,'--return-id',arrival_id,'--source',str(source),
         '--provenance','operator-returned ZIP','--packet-identity',bindings['dispatch_id']],
        [python,script,'verify','--batch-id',batch_id]]
    return {'custody_argv':commands,'expected_sha256':sha(raw),'expected_bytes':len(raw),
            'next':'After native verify, validate RETURN.json from the preserved custody copy.',
            'preconditions':['Serialize native custody writes.',
                             'On retry inspect the native intake; do not duplicate an existing arrival.',
                             'Compare native preserved digest with expected_sha256; stop on mismatch.'],
            'prose':'Preserve pasted prose as a separate native transcript arrival, never an LLM reconstruction.'}

def journal_received_proposal(returned: Mapping[str,Any], custody_row: Mapping[str,Any], *,
                              batch_id: str) -> dict[str,Any]:
    """Use a row read from verified native intake, not a model-authored custody assertion.

    This proposes an event only. The caller must first run the native verifier;
    a copied dictionary cannot establish custody or authorize a journal write.
    """
    require(ident(batch_id),'invalid batch id')
    require(returned.get('status')=='integrity_checked_not_accepted','validate preserved return first')
    require(ident(custody_row.get('return_id')),'bad custody arrival id')
    require(custody_row.get('sha256')==returned['zip_sha256'] and
            custody_row.get('byte_length')==returned['zip_bytes'],'custody bytes differ from validated ZIP')
    b=returned['envelope']['bindings']; rid=custody_row['return_id']
    require(custody_row.get('packet_or_run_identity')==b['dispatch_id'],'custody dispatch identity mismatch')
    detail={'return_id':rid,'round_id':b['round_id'],'sha256':returned['zip_sha256'],
            'bytes':returned['zip_bytes'],'media_type':'application/zip',
            'custody':{'store':'type_b_return_intake','batch_id':batch_id,'return_id':rid},
            'public_copy':None}
    return {'kind':'return_received','subject':rid,'detail':detail}

def split_wave(missions: Sequence[Mapping[str,Any]]) -> dict[str,Any]:
    """Check an authored division of labour; do not infer research independence.

    deliverables are single-owner integration outputs. Replication is explicit.
    depends_on is an integration dependency: all advisory sessions may run
    against frozen interfaces, but their changes are reviewed in these layers.
    """
    ids=set(); products={}; by_id={}; owners:dict[str,list[str]]=defaultdict(list)
    for row in missions:
        require(isinstance(row,Mapping) and ident(row.get('id')),'invalid mission id')
        mid=row['id']; require(mid not in ids,'duplicate mission id'); ids.add(mid)
        require(text(row.get('decision')) and text(row.get('boundary')),'mission needs decision and boundary')
        for field in ('deliverables','depends_on','owner_paths'):
            require(isinstance(row.get(field),list) and all(text(v) for v in row[field]),f'mission needs {field}')
        require(bool(row['deliverables']),'mission must produce a named deliverable')
        require(row.get('mode') in ('production','replication'),'bad mission mode')
        if row['mode']=='production':
            for product in row['deliverables']:
                require(product not in products,'two production missions own the same deliverable')
                products[product]=mid
        else:
            require(ident(row.get('replicate_of')),'replication must name the original mission')
        by_id[mid]=dict(row)
        for owner in row['owner_paths']:
            path_name(owner); owners[owner].append(mid)
    for mid,row in by_id.items():
        require(set(row['depends_on'])<=ids,f'{mid}: unknown mission dependency')
        if row['mode']=='replication':
            require(row['replicate_of'] in ids and row['replicate_of']!=mid,'invalid replication target')
    pending=set(ids); done=set(); layers=[]
    while pending:
        ready=sorted(m for m in pending if set(by_id[m]['depends_on'])<=done)
        require(bool(ready),'integration dependency cycle: revise interfaces before dispatch')
        layers.append(ready); done.update(ready); pending.difference_update(ready)
    return {'schema':'plectis-split-plan/1','parallel_advisory_sessions':sorted(ids),
            'integration_layers':layers,'deliverable_owners':products,
            'serialize_owner_paths':{p:sorted(set(v)) for p,v in sorted(owners.items()) if len(set(v))>1},
            'shared_rule':'Freeze one source/baseline and explicit interface versions before dispatch.',
            'claim':'Declared task partition, not measured independence or automatic integration.'}

def round_opened_proposal(bindings: Mapping[str,Any], manifest_sha256: str,
                          ask: str, consumers: Sequence[str]) -> dict[str,Any]:
    validate_bindings(dict(bindings))
    require(isinstance(manifest_sha256,str) and HEX64.fullmatch(manifest_sha256) is not None,
            'need final serialized native handoff manifest SHA-256')
    require(text(ask) and consumers and all(ident(c) for c in consumers),'ask/consumers required')
    b=bindings
    return {'kind':'round_opened','subject':b['round_id'],'detail':{
        'round_id':b['round_id'],'packet_id':b['packet_id'],'packet_manifest_sha256':manifest_sha256,
        'source_commit':b['source_commit'],'ask':ask,'consumers':list(consumers),'expected_returns':1}}

def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--zip',type=Path,required=True)
    ap.add_argument('--expected-bindings',type=Path,required=True)
    args=ap.parse_args()
    try:
        expected=json.loads(args.expected_bindings.read_text(encoding='utf-8'))
        result=validate_return(args.zip,expected)
        print(json.dumps(result,ensure_ascii=False,indent=2))
        return 0
    except (ReturnError,OSError,ValueError) as exc:
        print(f'research_round_plan: {exc}')
        return 2

if __name__=='__main__':
    raise SystemExit(main())
