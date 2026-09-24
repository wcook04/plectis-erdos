#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Add and verify the scaled integer inverse of the recovered block basis.
The LLL search is not repeated. Sympy is used only to construct a witness;
all entries and both products are then checked as ordinary Python integers.
"""
from __future__ import annotations
import argparse
import json
import sys
import time
from pathlib import Path
sys.set_int_max_str_digits(1_000_000)

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--certificate', type=Path,
                    default=Path(__file__).parent/'regenerated/block_certificate.json')
    args = ap.parse_args()
    from sympy import Matrix
    data = json.loads(args.certificate.read_text())
    t0 = time.perf_counter()
    C = data['basis']; k = len(C); m0 = int(data['m0'])
    raw = m0 * Matrix(C).inv()
    if not all(z.q == 1 for z in raw):
        raise ArithmeticError('scaled inverse has a nonintegral entry')
    D = [[int(raw[i,j]) for j in range(k)] for i in range(k)]
    for A,B in ((D,C),(C,D)):
        for i in range(k):
            for j in range(k):
                if sum(A[i][t]*B[t][j] for t in range(k)) != (m0 if i==j else 0):
                    raise ArithmeticError(('inverse witness failed', i, j))
    seconds = time.perf_counter()-t0
    data['right_inverse_scaled'] = D
    data['prime_exponents_P'] = {'2':128, '3':81, '5':56}
    data['inverse_seconds'] = seconds
    data['required_remaining_formal_bridges'] = [
        'finite generated window data equals the actual Lean product and forcing definitions',
        'elaborate the new full-height width and actual-series transport proof candidates']
    args.certificate.write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps({'shape':[k,k], 'all_scaled_inverse_entries_integral':True,
        'checked_DC_and_CD':True, 'scalar_equalities_checked':2*k*k,
        'inverse_seconds':seconds, 'Lean_compiled':False}, indent=2))

if __name__ == '__main__':
    main()
