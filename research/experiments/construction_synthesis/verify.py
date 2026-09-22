#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check generated transport proofs with Lean under the shared host mutex."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
import validation_singleflight as singleflight


def main():
    generated = HERE / 'results/Generated.lean'
    compiled = ROOT / '.lake/build/lib/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.olean'
    if not compiled.is_file():
        # The receipt binds the compiled import the proofs elaborate against. Without it the
        # two Lean runs below would succeed and the receipt would fail to write (22 Sep 2026).
        # The olean is produced by the repository's own governed builder, never by this script.
        print('construction-synthesis verify: compiled import missing: ' + str(compiled)
              + '\nbuild it first: python3 scripts/lean_fast_build.py'
              ' ErdosProblems.Erdos243.ReciprocalTailRigidity', file=sys.stderr)
        return 2
    env = singleflight.command_environment()
    env['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + env['PATH']
    lock_path = singleflight.resource_lock_path({}, 'lean-host')
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    search = json.loads((HERE / 'results/search.json').read_text())
    mixed = next((i, r) for i, r in enumerate(search['coordinates']) if 'C' in r['expr'])
    index, coordinate = mixed
    wrong = (f'\nnamespace ConstructionSynthesis\nexample (a D C : ℤ) :\n'
             f' coordinate{index} (sylvesterNext a) (nextDenState a D) (nextTailState a D C) =\n'
             f' a ^ {coordinate["power"]+1} * coordinate{index} a D C := by\n'
             f' simp only [coordinate{index}, sylvesterNext, nextDenState, nextTailState]\n'
             ' ring\nend ConstructionSynthesis\n').encode()
    started = time.monotonic()
    with lock_path.open('a+') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        acquired = time.monotonic()
        source = generated.read_bytes()
        proc = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=source,
                              capture_output=True, cwd=ROOT, env=env, timeout=120)
        negative = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=source+wrong,
                                  capture_output=True, cwd=ROOT, env=env, timeout=120)
    result = {'exit_code': proc.returncode, 'seconds': time.monotonic()-started,
              'lock_wait_seconds': acquired-started,
              'verification_seconds': time.monotonic()-acquired,
              'proof_sha256': hashlib.sha256(source).hexdigest(),
              'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'manifest_sha256': hashlib.sha256((ROOT / 'lake-manifest.json').read_bytes()).hexdigest(),
              'import_olean_sha256': hashlib.sha256(compiled.read_bytes()).hexdigest(),
              'stdout': proc.stdout.decode(), 'stderr': proc.stderr.decode(),
              'negative_control': {'intervention': 'increase recovered multiplier exponent by one',
                 'exit_code': negative.returncode,
                 'rejected_for_unsolved_goals': b'unsolved goals' in negative.stdout,
                 'stdout': negative.stdout.decode(), 'stderr': negative.stderr.decode()}}
    (HERE / 'results/lean.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    if proc.returncode != 0: return proc.returncode
    if b'sorryAx' in proc.stdout: return 1
    return 0 if negative.returncode != 0 and b'unsolved goals' in negative.stdout else 1

if __name__ == '__main__': sys.exit(main())
