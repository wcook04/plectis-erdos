#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Recompute the printed 80,000-bit enclosure and CF prefix using integers only.

No network, Lean, NumPy or floating-point arithmetic is used in the certificate.
This is independent of the historical repository driver. It does not check the
300,000-index carry census. Python 3.10+; expected runtime is a few seconds.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import platform
import time
from pathlib import Path

EXPECTED_TRACE = 'a0cd386342ba92e952e9de5aef09817da34bf5bc82edfe989110b5127a3465b0'

def recompute() -> tuple[dict, dict]:
    start = time.monotonic()
    D, factorial, lower, n = 1 << 80000, 1, 0, 1
    while True:
        n += 1
        factorial *= n
        if factorial - 1 > D:
            break
        lower += D // (factorial - 1)
    upper = lower + n - 2 + (2 * D) // (factorial - 1) + 1
    xnum, xden, ynum, yden = lower, D, upper, D
    qm2, qm1 = 1, 0
    trace: list[int] = []
    while True:
        a, rx = divmod(xnum, xden)
        b, ry = divmod(ynum, yden)
        # Stopping before either endpoint terminates avoids endpoint ambiguity.
        if a != b or rx == 0 or ry == 0:
            break
        trace.append(a)
        qm2, qm1 = qm1, a * qm1 + qm2
        # Inversion is order-reversing.
        xnum, xden, ynum, yden = yden, ry, xden, rx
    digest = hashlib.sha256((','.join(map(str, trace)) + '\n').encode()).hexdigest()
    checks = {
        'first_tail_index_7054': n == 7054,
        'width_7053': upper - lower == 7053,
        'common_prefix_length_23449': len(trace) == 23449,
        'last_denominator_has_39991_bits': qm1.bit_length() == 39991,
        'last_denominator_ge_2_pow_39990': qm1 >= 1 << 39990,
        '2_pow_39990_gt_10_pow_12038': (1 << 39990) > 10 ** 12038,
        'trace_digest_matches_independent_review': digest == EXPECTED_TRACE,
    }
    if not all(checks.values()):
        raise ArithmeticError('Certificate mismatch: ' + repr(checks))
    receipt = {
        'schema': 'erdos68_independent_cf_recomputation_v1',
        'review_date': '2026-09-16',
        'evidence_class': 'external_exact_integer_computation',
        'not_verified': ['Lean consumer replay', 'historical driver identity', '300000 carry census'],
        'python': platform.python_version(), 'scale_bits': 80000,
        'N': n, 'width': upper - lower,
        'common_partial_quotients': len(trace),
        'last_denominator_bit_length': qm1.bit_length(),
        'quotient_trace_sha256': digest, 'checks': checks,
        'elapsed_seconds': round(time.monotonic() - start, 3),
        'implementation_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    data = {
        'encoding': 'hexadecimal integers, without floating-point conversion',
        'scale_bits': 80000, 'lower_numerator_hex': hex(lower),
        'upper_numerator_hex': hex(upper),
        'last_convergent_denominator_hex': hex(qm1),
        'previous_convergent_denominator_hex': hex(qm2),
        'common_partial_quotients': trace,
    }
    return receipt, data

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--data', type=Path, help='Optional complete enclosure and quotient trace')
    args = ap.parse_args()
    receipt, data = recompute()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    if args.data:
        args.data.parent.mkdir(parents=True, exist_ok=True)
        args.data.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
