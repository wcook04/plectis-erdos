#!/usr/bin/env python3
"""Commit-bound focused replay receipt; uses the public verification receipt owner."""
import argparse,json,os,subprocess,hashlib
from focused_negative_controls import plan, adjudicate
from pathlib import Path
from run_external_verification import digest, is_expected_negative_rejection, write_runtime_receipt

PINS={'comparator':'68a064109f01c08f47c8edc9f51d6a2bbffaa188','lean4export':'6f4e21dd70c3c11d7fbd07d39e3192792c657448','landrun':'811cfff51ceaf3d9843708aa6d22e9b84ccac8b4','nanoda':'68d5ca9db226849b41a6fff59d796ff19d0a8840'}

def verdict(positive,negative,log,names,identities_match):
    # Timeout, launcher, signal and environment failures are never a semantic rejection.
    rejected=0 < negative < 124 and is_expected_negative_rejection(negative,log,"Challenge and solution theorem statement do not match: '"+names[0]+"'")
    return positive==0 and rejected and identities_match

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--entry',required=True);ap.add_argument('--expected-commit',required=True)
    ap.add_argument('--positive-exit',type=int,required=True);ap.add_argument('--negative-exit',type=int,required=True)
    args=ap.parse_args();entry=Path(args.entry)
    if entry.parent!=Path('.') or not entry.name.startswith('ExternalVerification'):raise ValueError('Expected one top-level entry')
    cfg_path=entry/'comparator.json';neg_path=entry/'comparator-negative-mismatch.json'
    cfg=json.loads(cfg_path.read_text());neg=json.loads(neg_path.read_text())
    expected_neg={**cfg,'solution_module':'NegativeSolutions.'+entry.name}
    layout_ok=(neg==expected_neg and cfg['challenge_module']==entry.name+'.Challenge' and cfg['solution_module']=='Solutions.'+entry.name and cfg['enable_nanoda'] is True and bool(cfg['theorem_names']))
    tmp=Path(os.environ['RUNNER_TEMP']);git=lambda *a:subprocess.check_output(['git',*a],text=True).strip()
    revisions={k:git('-C',str(tmp/({'landrun':'landrun-src'}.get(k,k))),'rev-parse','HEAD') for k in PINS}
    binary_paths={'comparator':tmp/'comparator/.lake/build/bin/comparator','lean4export':tmp/'lean4export/.lake/build/bin/lean4export','landrun':tmp/'landrun','nanoda':tmp/'nanoda/target/release/nanoda_bin'}
    binaries={k:digest(p) for k,p in binary_paths.items()}
    project_toolchain=Path('lean-toolchain').read_text().strip();export_toolchain=(tmp/'lean4export/lean-toolchain').read_text().strip()
    source_commit=git('rev-parse','HEAD');sandbox=os.environ['SANDBOX_MODE']
    post_diff=subprocess.run(['git','diff','--name-only','-z','HEAD','--'],capture_output=True)
    dirty_paths=[p.decode('utf-8',errors='surrogateescape') for p in post_diff.stdout.split(b'\0') if p]
    tracked_clean=post_diff.returncode==0 and not dirty_paths
    identities=(tracked_clean and source_commit==args.expected_commit and revisions==PINS and all(binaries.values()) and project_toolchain==export_toolchain and layout_ok and sandbox in {'user-manager','system-manager-nonprivileged-unit'})
    log=Path('artifacts/negative.log').read_text()
    passed=verdict(args.positive_exit,args.negative_exit,log,cfg['theorem_names'],identities)
    sources=[cfg_path,neg_path,Path(cfg['challenge_module'].replace('.','/')+'.lean'),Path(cfg['solution_module'].replace('.','/')+'.lean'),Path(neg['solution_module'].replace('.','/')+'.lean'),Path('lean-toolchain'),Path('lake-manifest.json'),Path('lakefile.toml'),Path('scripts/landrun-wrapper.sh')]
    receipt={'schema':'erdos-focused-comparator-runtime-receipt/1','result':'pass' if passed else 'fail','entry':entry.name,'source_commit':source_commit,'source_tree':git('rev-parse','HEAD^{tree}'),'expected_commit':args.expected_commit,'source_commit_matches':source_commit==args.expected_commit,'tracked_source_check':{'phase':'post_replay','git_exit':post_diff.returncode,'tracked_dirty_paths':dirty_paths,'matches_commit':tracked_clean},'positive_exit':args.positive_exit,'negative_exit':args.negative_exit,'positive_log_digest':digest(Path('artifacts/positive.log')),'negative_log_digest':digest(Path('artifacts/negative.log')),'expected_mismatch':"Challenge and solution theorem statement do not match: '"+cfg['theorem_names'][0]+"'",'tools':revisions,'expected_tools':PINS,'binary_digests':binaries,'project_toolchain':project_toolchain,'export_toolchain':export_toolchain,'comparator_toolchain':(tmp/'comparator/lean-toolchain').read_text().strip(),'layout_matches':layout_ok,'input_digests':{str(p):digest(p) for p in sources},'sandbox_mode':sandbox,'nanoda_required':True,'submission':'not_submitted'}
    policy = plan(entry.name, lambda p: Path(p).read_bytes())
    controls = adjudicate(policy, lambda p: Path(p).read_bytes(), cfg['theorem_names'][0], passed,
                          lambda b: 'sha256:' + hashlib.sha256(b).hexdigest())
    if controls is not None:
        extra_paths = [entry / 'negative-controls.json']
        for control in policy['additional_controls']:
            extra_paths.append(Path(control['config_path']))
            negative_config = json.loads(Path(control['config_path']).read_text())
            extra_paths.append(Path(negative_config['solution_module'].replace('.', '/') + '.lean'))
        receipt['negative_controls'] = controls
        receipt['negative_control_input_digests'] = {str(p): digest(p) for p in extra_paths}
        passed = passed and controls['all_required_passed']
        receipt['result'] = 'pass' if passed else 'fail'
    write_runtime_receipt(Path('artifacts/replay.json'),receipt)
    return 0 if passed else 1
if __name__=='__main__':raise SystemExit(main())
