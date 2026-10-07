#!/usr/bin/env python3
"""Source and review custody for the native disclosed candidate bank.

Standard library only. This module never assigns gold, calls a model, launches
Lean, writes to the source repository, or uses the author's key to mark answers.
The command route is owned by build_restatement_benchmark. This module has no CLI.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
import math
import re
import subprocess
from pathlib import Path, PurePosixPath
from typing import Any

ROOT = Path(__file__).resolve().parents[1] / 'docs/research-commons/benchmarks/round8_candidate_development'
COMMIT = '0268dd8bfb2a556a0c93078337d42c6d07138fa2'
PACKET = 'plectis_round8_p5_relation_bank_20260929'
MAX_JSON_BYTES = 4_000_000
RELATIONS = frozenset({'equivalent','strictly_stronger','endpoint_route','separation',
    'unsupported_inference','refuted_generalisation','finite_obstruction','unknown'})
DIRECTIONS = frozenset({'P_iff_Q','P_implies_Q','Q_implies_P','P_implies_Q_not_converse',
    'P_and_not_Q','claimed_P_implies_Q_refuted','claimed_P_implies_Q_unestablished','P_implies_Q_unestablished','unknown'})
SUPPLY = frozenset({'relation_supplied_endpoints_open','finite_conclusions_supplied',
    'relation_ordinary_proof','relation_supplied_with_elementary_converse','conditional_conclusion',
    'counterexample_ordinary_proof','conclusion_supplied','relation_supplied_reverse_unestablished','unknown'})
ASSESSMENTS = frozenset({'supported','understatement','overstatement','rediscovery','unsupported',
    'false_in_stated_context','unknown'})
PERTURBATION = frozenset({'supported','refuted','unestablished','context_changed','generic_countermodel_only'})
DIMENSIONS = frozenset({'relation','direction','scope','supply','obligations','evidence'})
HEX = re.compile(r'[0-9a-f]{64}\Z')
TASK_ID = re.compile(r'R8P5-\d{2}\Z')

class Invalid(ValueError):
    """Malformed, stale, unsafe, or inconsistent input; never a mathematical verdict."""

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def _pairs(pairs: list[tuple[str,Any]]) -> dict[str,Any]:
    result = {}
    for key, value in pairs:
        if key in result:
            raise Invalid(f'duplicate JSON key: {key}')
        result[key] = value
    return result

def _constant(value: str) -> None:
    raise Invalid(f'non-finite JSON number: {value}')

def _float(value: str) -> float:
    result=float(value)
    if not math.isfinite(result): raise Invalid('non-finite JSON number')
    return result

def loads(raw: str | bytes) -> Any:
    if isinstance(raw,bytes):
        try: raw = raw.decode('utf-8')
        except UnicodeDecodeError as exc: raise Invalid('invalid UTF-8') from exc
    if len(raw.encode('utf-8')) > MAX_JSON_BYTES:
        raise Invalid('JSON exceeds byte budget')
    try:
        return json.loads(raw, object_pairs_hook=_pairs, parse_constant=_constant, parse_float=_float)
    except (json.JSONDecodeError, RecursionError) as exc:
        raise Invalid(f'invalid JSON: {exc}') from exc

def read_json(path: Path) -> Any:
    if path.stat().st_size > MAX_JSON_BYTES: raise Invalid('JSON exceeds byte budget')
    return loads(path.read_bytes())

def fields(obj: Any, expected: set[str] | frozenset[str], where: str) -> None:
    if not isinstance(obj,dict): raise Invalid(f'{where}: expected object')
    if set(obj) != set(expected):
        raise Invalid(f'{where}: field mismatch; missing={sorted(set(expected)-set(obj))}; extra={sorted(set(obj)-set(expected))}')

def text(x: Any, where: str) -> None:
    if not isinstance(x,str) or not x.strip(): raise Invalid(f'{where}: expected nonempty string')

def string_list(x: Any, where: str, *, nonempty: bool=False, unique: bool=False) -> None:
    if not isinstance(x,list): raise Invalid(f'{where}: expected list')
    if nonempty and not x: raise Invalid(f'{where}: empty list')
    for y in x: text(y,where)
    if unique and len(set(x)) != len(x): raise Invalid(f'{where}: duplicate entry')

def member(value: Any, options: frozenset[str], where: str) -> None:
    if not isinstance(value,str) or value not in options: raise Invalid(f'{where}: unknown value {value!r}')

def safe_path(root: Path, rel: str) -> Path:
    text(rel,'relative path')
    p=PurePosixPath(rel)
    if p.is_absolute() or '..' in p.parts or '\\' in rel or '\x00' in rel or rel in {'.',''}:
        raise Invalid('unsafe relative path')
    out=(root/rel).resolve()
    try: out.relative_to(root.resolve())
    except ValueError as exc: raise Invalid('path escapes root') from exc
    return out

BANK_FIELDS = frozenset({'schema','task_id','packet_id','source_commit','split','semantic_family_id',
    'dependence_cluster','problem','overlap_flags','context','left','right','return_claim','question',
    'source_handles','required_response_fields'})
OVERLAP_FIELDS = frozenset({'problem_in_round7_calibration','calibration_row_reused',
    'semantic_family_is_authored_new_cluster','proof_lineage_independence','corpus_already_disclosed'})
RESPONSE_FIELDS = frozenset({'task_id','relation_label','direction','supply_status','assessment',
    'reasoning','evidence','unproved_obligations','reverse_status'})

def load_bank(path: Path=ROOT/'candidate_bank.jsonl') -> list[dict[str,Any]]:
    if path.stat().st_size > MAX_JSON_BYTES: raise Invalid('bank exceeds byte budget')
    rows=[];seen=set()
    for line_no,line in enumerate(path.read_bytes().splitlines(),1):
        if not line.strip(): raise Invalid(f'bank line {line_no}: blank row')
        row=loads(line);fields(row,BANK_FIELDS,f'bank line {line_no}')
        if row['schema']!='plectis-relation-candidate/1' or row['packet_id']!=PACKET: raise Invalid('wrong bank identity')
        if row['source_commit']!=COMMIT or row['split']!='disclosed_candidate_development': raise Invalid('wrong source or split')
        if not isinstance(row['task_id'],str) or not TASK_ID.fullmatch(row['task_id']): raise Invalid('invalid task ID')
        if row['task_id'] in seen: raise Invalid('duplicate task ID')
        seen.add(row['task_id'])
        for k in ['context','left','right','return_claim','question','semantic_family_id','dependence_cluster']: text(row[k],k)
        if row['semantic_family_id']!=row['dependence_cluster']: raise Invalid('dependence cluster mismatch')
        if type(row['problem']) is not int or row['problem']<=0: raise Invalid('invalid problem number')
        fields(row['overlap_flags'],OVERLAP_FIELDS,'overlap flags')
        for k in OVERLAP_FIELDS-{'proof_lineage_independence'}:
            if type(row['overlap_flags'][k]) is not bool: raise Invalid('invalid overlap boolean')
        if row['overlap_flags']['proof_lineage_independence']!='not_established': raise Invalid('independence cannot be asserted here')
        if row['overlap_flags']['calibration_row_reused']: raise Invalid('reused calibration row')
        if not row['overlap_flags']['corpus_already_disclosed']: raise Invalid('disclosed corpus cannot be relabelled unseen')
        string_list(row['source_handles'],'source handles',nonempty=True,unique=True)
        string_list(row['required_response_fields'],'response fields',nonempty=True,unique=True)
        if set(row['required_response_fields']) != RESPONSE_FIELDS-{'task_id'}: raise Invalid('response contract mismatch')
        rows.append(row)
    if not rows: raise Invalid('empty bank')
    return rows

def binding_index(path: Path=ROOT/'sources/bindings.json') -> dict[str,Any]:
    obj=read_json(path)
    if obj.get('schema')!='plectis-source-bindings/1' or obj.get('source_commit')!=COMMIT: raise Invalid('binding identity mismatch')
    out={}
    for h in obj['handles']:
        if h['handle_id'] in out: raise Invalid('duplicate source handle')
        safe_path(ROOT,h['path'])
        for k in ['file_sha256','span_sha256']:
            if not isinstance(h[k],str) or not HEX.fullmatch(h[k]): raise Invalid('invalid source digest')
        for k in ['start_line','end_line','start_byte','end_byte']:
            if type(h[k]) is not int: raise Invalid('source coordinate not an integer')
        if not 1<=h['start_line']<=h['end_line'] or not 0<=h['start_byte']<h['end_byte']: raise Invalid('invalid source coordinates')
        out[h['handle_id']]=h
    return out

def validate_sources(source_root: Path | None, bindings: dict[str,Any], *, bundle_root: Path=ROOT) -> dict[str,Any]:
    parser = None
    source_cache = {}
    declaration_cache = {}
    if source_root is not None:
        source_root = Path(source_root).resolve(strict=True)
        git=subprocess.run(['git','-C',str(source_root),'rev-parse','HEAD'],capture_output=True,text=True)
        if git.returncode or git.stdout.strip()!=COMMIT:
            raise Invalid('source checkout does not name the frozen commit')
        dirty=subprocess.run(['git','-C',str(source_root),'diff','--quiet','HEAD','--'],capture_output=True)
        if dirty.returncode:
            raise Invalid('source checkout has tracked differences from HEAD')
        paths={h['path'] for h in bindings.values()}|{'scripts/relation_registry.py'}
        listed=subprocess.run(['git','-C',str(source_root),'ls-files','-z','--',*sorted(paths)],
                              capture_output=True)
        tracked={v.decode('utf-8') for v in listed.stdout.split(b'\0') if v}
        if listed.returncode or tracked!=paths:
            raise Invalid('historical source or parser is not in the frozen Git inventory')
        parser_path=source_root/'scripts/relation_registry.py'
        if parser_path.is_symlink() or not parser_path.is_file():
            raise Invalid('historical native parser unavailable')
        frozen_parser=subprocess.run(
            ['git','-C',str(source_root),'show',f'{COMMIT}:scripts/relation_registry.py'],
            capture_output=True)
        if frozen_parser.returncode or parser_path.read_bytes()!=frozen_parser.stdout:
            raise Invalid('historical parser bytes differ from frozen Git object')
        module_spec=importlib.util.spec_from_file_location('historical_relation_registry',parser_path)
        if module_spec is None or module_spec.loader is None:
            raise Invalid('historical native parser cannot be loaded')
        parser=importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(parser)
    for hid,h in bindings.items():
        excerpt=safe_path(bundle_root,f'sources/excerpts/{hid}.txt').read_bytes()
        if digest(excerpt)!=h['span_sha256']:
            raise Invalid(f'excerpt digest changed: {hid}')
        if source_root is not None:
            if h['path'] not in source_cache:
                source_cache[h['path']]=safe_path(source_root,h['path']).read_bytes()
            raw=source_cache[h['path']]
            if digest(raw)!=h['file_sha256']:
                raise Invalid(f'source digest changed: {hid}')
            span=b''.join(raw.splitlines(keepends=True)[h['start_line']-1:h['end_line']])
            if raw[h['start_byte']:h['end_byte']]!=span or span!=excerpt:
                raise Invalid(f'coordinate mismatch: {hid}')
            if h['declaration']:
                # Call the exact historical registry owner, not an imported current parser.
                if h['path'] not in declaration_cache:
                    declaration_cache[h['path']]=parser.lean_declarations(raw.decode('utf-8'))
                decls=declaration_cache[h['path']]
                d=h['declaration']
                if d not in decls:
                    raise Invalid(f'declaration binding changed: {hid}')
                start=sum(len(line) for line in raw.splitlines(keepends=True)[:d['line']-1])
                if h['signature_start_byte']!=start:
                    raise Invalid(f'signature start changed: {hid}')
                end=h['signature_end_byte']
                if type(end) is not int or not start<end<=len(raw):
                    raise Invalid(f'invalid signature boundary: {hid}')
                signature=raw[start:end].decode('utf-8')
                if signature!=h['signature'] or digest(signature.encode())!=h['signature_sha256']:
                    raise Invalid(f'signature changed: {hid}')
                if not raw[end:].lstrip().startswith(b':='):
                    raise Invalid(f'signature assignment boundary changed: {hid}')
    result={'source_handles_checked':len(bindings),'excerpt_digests_checked':True,
            'current_source_files_checked':source_root is not None,'kernel_checked':False}
    if source_root is not None:
        result['git_head']=COMMIT
        result['tracked_tree_clean']=True
        # Parser bytes are checked; Python import resolution outside this file is not hermetic.
        result['untracked_dependencies_authenticated']=False
        result['historical_parser_git_object_checked']=True
    return result

def evidence_rows(value: Any, handles: dict[str,Any], permitted: list[str]) -> None:
    if not isinstance(value,list): raise Invalid('evidence must be a list')
    seen=set()
    for e in value:
        fields(e,{'handle_id','file_sha256','start_line','end_line'},'evidence')
        hid=e['handle_id']
        if not isinstance(hid,str) or hid not in handles or hid not in permitted: raise Invalid('unknown or off-task evidence handle')
        if hid in seen: raise Invalid('duplicate evidence handle')
        seen.add(hid);h=handles[hid]
        if e['file_sha256']!=h['file_sha256']: raise Invalid('stale evidence digest')
        if type(e['start_line']) is not int or type(e['end_line']) is not int: raise Invalid('invalid evidence lines')
        if not h['start_line']<=e['start_line']<=e['end_line']<=h['end_line']: raise Invalid('evidence outside bound span')

def parse_responses(obj: Any, bank: list[dict[str,Any]], handles: dict[str,Any]) -> dict[str,Any]:
    # Evidence coordinates are meaningful only while the packet's excerpts
    # still match their source bindings. Parsing does not adjudicate meaning.
    validate_sources(None, handles, bundle_root=ROOT)
    fields(obj,{'schema','source_commit','answers'},'responses')
    if obj['schema']!='plectis-relation-response/1' or obj['source_commit']!=COMMIT: raise Invalid('response identity mismatch')
    if not isinstance(obj['answers'],list): raise Invalid('answers must be a list')
    tasks={r['task_id']:r for r in bank};seen=set();parsed=[]
    for a in obj['answers']:
        fields(a,RESPONSE_FIELDS,'answer');tid=a['task_id']
        if not isinstance(tid,str) or tid not in tasks or tid in seen: raise Invalid('unknown or duplicate answer task')
        seen.add(tid)
        for k,opt in [('relation_label',RELATIONS),('direction',DIRECTIONS),('supply_status',SUPPLY),('assessment',ASSESSMENTS),('reverse_status',PERTURBATION)]:member(a[k],opt,k)
        text(a['reasoning'],'reasoning');string_list(a['unproved_obligations'],'unproved obligations')
        evidence_rows(a['evidence'],handles,tasks[tid]['source_handles'])
        state='pending_independent_semantic_review' if a['evidence'] else 'insufficient_evidence'
        if a['relation_label']=='unknown' and a['evidence']: state='unknown_relation_pending_review'
        if a['assessment']=='unknown': state='abstained_or_ambiguous'
        parsed.append({'task_id':tid,'parser_disposition':state,'answer':a})
    return {'schema':'plectis-parsed-responses/1','source_commit':COMMIT,'answers':parsed,'missing_task_ids':sorted(set(tasks)-seen),'gold_assigned':False,'scores_computed':False,'identity_or_meaning_verified':False}

def parse_reviews(obj: Any, bank: list[dict[str,Any]], handles: dict[str,Any]) -> dict[str,Any]:
    validate_sources(None, handles, bundle_root=ROOT)
    fields(obj,{'schema','source_commit','reviewer','reviews'},'review')
    if obj['schema']!='plectis-relation-review/1' or obj['source_commit']!=COMMIT: raise Invalid('review identity mismatch')
    fields(obj['reviewer'],{'reviewer_id','role','identity_blinded'},'reviewer')
    text(obj['reviewer']['reviewer_id'],'reviewer ID')
    if obj['reviewer']['role']!='semantic_reviewer' or type(obj['reviewer']['identity_blinded']) is not bool: raise Invalid('invalid reviewer metadata')
    if not isinstance(obj['reviews'],list): raise Invalid('reviews must be a list')
    tasks={r['task_id']:r for r in bank};seen=set()
    for r in obj['reviews']:
        fields(r,{'task_id','verdict','dimensions','rationale','evidence'},'review row')
        tid=r['task_id']
        if not isinstance(tid,str) or tid not in tasks or tid in seen: raise Invalid('unknown or duplicate review task')
        seen.add(tid);member(r['verdict'],frozenset({'correct','incorrect','ambiguous','insufficient_evidence'}),'review verdict')
        fields(r['dimensions'],DIMENSIONS,'dimensions')
        if any(v is not None and type(v) is not bool for v in r['dimensions'].values()): raise Invalid('dimension must be boolean or null')
        text(r['rationale'],'rationale');evidence_rows(r['evidence'],handles,tasks[tid]['source_handles'])
        if r['verdict'] in {'correct','incorrect'} and not r['evidence']: raise Invalid('decisive review without evidence')
        if r['verdict']=='correct' and any(v is not True for v in r['dimensions'].values()): raise Invalid('correct review has failed or unknown dimension')
        if r['verdict']=='incorrect' and False not in r['dimensions'].values(): raise Invalid('incorrect review names no failed dimension')
    return {'schema':'plectis-parsed-review/1','source_commit':COMMIT,'review':obj,'missing_task_ids':sorted(set(tasks)-seen),'reviewer_independence_verified':False,'gold_assigned':False,'scores_computed':False}

def export_review(parsed: dict[str,Any], bank: list[dict[str,Any]], handles: dict[str,Any], out: Path,
                  *, source_root: Path | None=None) -> dict[str,Any]:
    if out.exists(): raise Invalid('refuse to overwrite review export')
    tasks={r['task_id']:r for r in bank};selected=[];needed=set()
    for row in parsed['answers']:
        task=tasks[row['task_id']];needed.update(task['source_handles'])
        # No author key, author perturbation labels, producer ID, score, or model metadata.
        selected.append({'task':task,'participant_answer':row['answer'],'parser_disposition':row['parser_disposition']})
    # Validate before creating an output: a stale or changed packet excerpt
    # must never be delivered under its old source hash. Passing source_root
    # additionally checks the exact 0268 checkout, not a later HEAD.
    validation=validate_sources(source_root,{h:handles[h] for h in needed},bundle_root=ROOT)
    excerpts={h:(ROOT/'sources'/'excerpts'/f'{h}.txt').read_bytes() for h in needed}
    for h,raw in excerpts.items():
        if digest(raw)!=handles[h]['span_sha256']: raise Invalid(f'excerpt drift during export: {h}')
    obj={'schema':'plectis-label-free-review/1','source_commit':COMMIT,'items':selected,'sources':[handles[h] for h in sorted(needed)],'boundary':'Producer identity and author labels omitted. Mathematical source files can reveal answers. File separation does not certify reviewer independence or an unseen test.'}
    out.mkdir(parents=True)
    review_bytes=(json.dumps(obj,indent=2,ensure_ascii=False)+'\n').encode('utf-8')
    (out/'review.json').write_bytes(review_bytes)
    delivery=[]
    for h in sorted(needed):
        target=out/'sources'/f'{h}.txt';target.parent.mkdir(exist_ok=True)
        target.write_bytes(excerpts[h])
        delivered=digest(target.read_bytes())
        if delivered!=handles[h]['span_sha256']: raise Invalid(f'delivered excerpt changed: {h}')
        delivery.append({'handle_id':h,'path':f'sources/{h}.txt','span_sha256':delivered,
                         'source_file_sha256':handles[h]['file_sha256']})
    # A reviewer intake checks these exact bytes rather than trusting a
    # metadata-only source handle. This manifest is custody, not gold.
    manifest={'schema':'plectis-label-free-review-manifest/1','source_commit':COMMIT,
              'review_sha256':digest(review_bytes),'delivered_sources':delivery,
              'source_checkout_checked':validation['current_source_files_checked'],
              'gold_assigned':False,'independence_verified':False}
    (out/'review_manifest.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n')
    if source_root is not None: validate_sources(source_root,{h:handles[h] for h in needed},bundle_root=ROOT)
    return {'items_exported':len(selected),'author_key_exported':False,'producer_metadata_exported':False,'output':str(out),'independence_verified':False,'review_manifest_sha256':digest((out/'review_manifest.json').read_bytes()),'source_checkout_checked':validation['current_source_files_checked']}

def verify_review_export(out: Path, expected_manifest_sha256: str,
                         handles: dict[str,Any]) -> dict[str,Any]:
    """Reviewer intake: check exact delivered bytes against an external digest."""
    if not isinstance(expected_manifest_sha256,str) or not HEX.fullmatch(expected_manifest_sha256):
        raise Invalid('external review manifest digest required')
    manifest_path=out/'review_manifest.json'
    if manifest_path.is_symlink() or digest(manifest_path.read_bytes())!=expected_manifest_sha256:
        raise Invalid('review manifest differs from external digest')
    manifest=read_json(manifest_path)
    if manifest.get('schema')!='plectis-label-free-review-manifest/1' or manifest.get('source_commit')!=COMMIT:
        raise Invalid('wrong review export identity')
    if manifest.get('gold_assigned') is not False or manifest.get('independence_verified') is not False:
        raise Invalid('review export wrongly promoted')
    if any(p.is_symlink() for p in out.rglob('*')): raise Invalid('linked review export path')
    review_path=out/'review.json'
    if review_path.is_symlink() or digest(review_path.read_bytes())!=manifest.get('review_sha256'):
        raise Invalid('review contents changed')
    review=read_json(review_path)
    if review.get('schema')!='plectis-label-free-review/1' or review.get('source_commit')!=COMMIT:
        raise Invalid('wrong review contents identity')
    delivered=manifest.get('delivered_sources')
    if not isinstance(delivered,list): raise Invalid('missing delivered source inventory')
    seen=set()
    for row in delivered:
        fields(row,{'handle_id','path','span_sha256','source_file_sha256'},'delivered source')
        hid=row['handle_id']
        if hid in seen or hid not in handles or row['path']!=f'sources/{hid}.txt':
            raise Invalid('review source identity changed')
        seen.add(hid)
        h=handles[hid]
        if row['span_sha256']!=h['span_sha256'] or row['source_file_sha256']!=h['file_sha256']:
            raise Invalid('review source binding changed')
        path=safe_path(out,row['path'])
        if path.is_symlink() or digest(path.read_bytes())!=row['span_sha256']:
            raise Invalid(f'delivered review source changed: {hid}')
    actual={p.relative_to(out).as_posix() for p in out.rglob('*') if p.is_file()}
    needed={hid for item in review.get('items',[]) for hid in item['task']['source_handles']}
    if seen!=needed or {h['handle_id'] for h in review.get('sources',[])}!=seen:
        raise Invalid('review source inventory does not cover the review items')
    expected={'review.json','review_manifest.json'}|{f'sources/{hid}.txt' for hid in seen}
    if actual!=expected: raise Invalid('review export file inventory changed')
    return {'schema':'plectis-label-free-review-intake/1','source_commit':COMMIT,
            'sources_checked':len(seen),'gold_assigned':False,'independence_verified':False}

def validate_key(bank: list[dict[str,Any]], handles: dict[str,Any]) -> dict[str,Any]:
    key=read_json(ROOT/'author_proposals.json')
    if key['source_commit']!=COMMIT or key['status']!='candidate_author_proposals_not_gold' or key['confirmatory_sealed'] is not False: raise Invalid('candidate key wrongly promoted')
    tasks={r['task_id']:r for r in bank};seen=set();count=0
    for a in key['answers']:
        tid=a['task_id']
        if tid not in tasks or tid in seen: raise Invalid('key task mismatch')
        seen.add(tid)
        if a['gold_eligible'] is not False or a['independent_semantic_review'] is not None or a['kernel_status']!='UNRUN': raise Invalid('unauthorised key promotion')
        for field,options in [('relation_label',RELATIONS),('direction',DIRECTIONS),('supply_status',SUPPLY),('assessment',ASSESSMENTS)]: member(a[field],options,field)
        if set(a['required_evidence'])!=set(tasks[tid]['source_handles']): raise Invalid('key source coverage mismatch')
        if {p['kind'] for p in a['perturbations']}!={'reverse_direction','remove_premise','change_quantifier_or_context'} or len(a['perturbations'])!=3: raise Invalid('three distinct perturbations required')
        for p in a['perturbations']:
            member(p['status'],PERTURBATION,'perturbation status')
            for field in ['mutation','evidence','scope_limit']:text(p[field],field)
            count+=1
    if seen!=set(tasks): raise Invalid('incomplete key')
    return {'candidate_keys':len(seen),'perturbations':count,'gold_eligible':False}

def validate(source_root: Path | None=None) -> dict[str,Any]:
    bank=load_bank();handles=binding_index()
    for row in bank:
        if any(h not in handles for h in row['source_handles']): raise Invalid('unbound source handle')
    result=validate_sources(source_root,handles)
    result.update(validate_key(bank,handles))
    result.update({'items':len(bank),'dependence_clusters':len({r['dependence_cluster'] for r in bank}),'mathematical_gold':False,'model_study_run':False})
    return result
