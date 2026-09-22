#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Export only the selected transition definitions; never export the answer."""
import ast
import hashlib
import json
from pathlib import Path
import re
from search import arithmetic, VARS
ROOT = Path(__file__).resolve().parents[3]
SOURCE = Path('lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean')
NAMES = ('sylvesterNext', 'nextDenState', 'nextTailState')

def extract(source, names=NAMES):
    text = source.read_text()
    rows = []
    for name in names:
        pattern = (r'^def ' + re.escape(name) +
                   r' \(([a-zA-Z ]+) : ℤ\) : ℤ :=\n  ([a-zA-Z0-9 +*^()\-]+)$')
        match = re.search(pattern, text, re.M)
        if not match: raise ValueError('unsupported definition shape: ' + name)
        args, body = match.groups()
        symbols = {str(x): x for x in VARS}
        if not set(args.split()) <= symbols.keys(): raise ValueError('unknown binder')
        expr = arithmetic(ast.parse(body.replace('^', '**'), mode='eval'), symbols)
        rows.append({'name': name, 'arguments': args.split(), 'body': body,
                     'line': text[:match.start()].count('\n') + 1,
                     'definition_sha256': hashlib.sha256(match[0].encode()).hexdigest(),
                     'expr': expr})
    return rows


if __name__ == '__main__':
    rows = extract(ROOT / SOURCE)
    packet = {'source': str(SOURCE),
              'definitions': [{k:v for k,v in r.items() if k != 'expr'} for r in rows]}
    destination = Path(__file__).resolve().parent / 'input.json'
    destination.write_text(json.dumps(packet, indent=2) + '\n')
    print(destination)
