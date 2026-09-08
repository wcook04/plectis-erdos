"""Optional package controls; legacy receipts retain their existing nine inputs."""
import json,re
from pathlib import Path

def require(ok,message):
 if not ok:raise ValueError(message)

def plan(entry,read):
    cfg=json.loads(read(entry+'/comparator.json'))
    path=entry+'/negative-controls.json'
    try:policy=json.loads(read(path))
    except FileNotFoundError:return None
    require(policy.get('schema')=='focused-negative-controls/1','control schema')
    required=policy.get('required_theorem_names',[])
    require(required and len(required)==len(set(required)) and set(required)<=set(cfg['theorem_names']),'required names')
    rows=policy.get('additional_controls',[]);seen=set();names={cfg['theorem_names'][0]}
    for row in rows:
        ident=row['id'];theorem=row['theorem_name'];config=row['config_path']
        require(re.fullmatch('[a-z][a-z0-9_]*',ident) and ident not in seen,'control id')
        require(theorem in cfg['theorem_names'] and theorem not in names,'control theorem')
        require(config==entry+'/comparator-'+ident+'-negative-mismatch.json','control path')
        neg=json.loads(read(config));module=neg.get('solution_module','')
        require(re.fullmatch(r'NegativeSolutions\.'+re.escape(entry)+r'[A-Za-z0-9_]+',module),'negative module layout')
        require(neg=={**cfg,'solution_module':module,'theorem_names':[theorem]},'one-name config')
        read(module.replace('.','/')+'.lean')
        seen.add(ident);names.add(theorem)
    require(set(required)<=names,'missing designated negative')
    return policy

def adjudicate(policy,read,default_name,default_pass,digest):
    if policy is None:return None
    rows=[];covered={default_name} if default_pass else set()
    for control in policy['additional_controls']:
        ident=control['id'];log_path='artifacts/negative-'+ident+'.log';exit_path='artifacts/negative-'+ident+'.exit'
        log=read(log_path);code=int(read(exit_path).decode().strip())
        expected="Challenge and solution theorem statement do not match: '"+control['theorem_name']+"'"
        passed=0<code<124 and bool(log.strip()) and expected in log.decode()
        if passed:covered.add(control['theorem_name'])
        rows.append({**control,'exit_code':code,'log_path':log_path,'log_digest':digest(log),'expected_mismatch':expected,'result':'pass' if passed else 'fail'})
    return {'schema':'focused-negative-controls-result/1','required_theorem_names':policy['required_theorem_names'],'controls':rows,'all_required_passed':set(policy['required_theorem_names'])<=covered,'boundary':'Specific selected-name rejections only; not mathematical truth or full-paper coverage.'}

if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--entry',required=True);a=p.parse_args()
 policy=plan(a.entry,lambda path:Path(path).read_bytes())
 for row in policy['additional_controls'] if policy else []:print(row['id']+'\t'+row['config_path'])
