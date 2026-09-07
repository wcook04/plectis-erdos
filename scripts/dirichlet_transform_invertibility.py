#!/usr/bin/env python3
"""Exact audit of the divisor transform used in the Erdos-257 corpus.

For a Boolean support word ``a`` the divisor multiplicity is

    tau(n) = sum_{d | n} a(d).

Dirichlet convolution by the constant-one function is inverted by the
Moebius function.  In particular, tau[1:M] determines a[1:M] exactly.  This
script verifies the identity on structured and exhaustive Boolean prefixes
and writes a non-ephemeral receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = Path("formal_math/erdos257_period_noncollapse/scripts/dirichlet_transform_invertibility.py")
RECEIPT = Path("state/formal_math/erdos257_period_noncollapse/dirichlet_transform_invertibility_receipt.json")


def mobius_sieve(limit: int) -> list[int]:
    mu = [1] * (limit + 1)
    prime = [True] * (limit + 1)
    mu[0] = 0
    for p in range(2, limit + 1):
        if not prime[p]:
            continue
        for multiple in range(p, limit + 1, p):
            prime[multiple] = False if multiple != p else prime[multiple]
            mu[multiple] *= -1
        square = p * p
        for multiple in range(square, limit + 1, square):
            mu[multiple] = 0
    return mu


def divisor_transform(bits: list[int]) -> list[int]:
    limit = len(bits) - 1
    tau = [0] * (limit + 1)
    for d in range(1, limit + 1):
        if bits[d]:
            for multiple in range(d, limit + 1, d):
                tau[multiple] += bits[d]
    return tau


def invert_transform(tau: list[int], mu: list[int]) -> list[int]:
    limit = len(tau) - 1
    bits = [0] * (limit + 1)
    for n in range(1, limit + 1):
        bits[n] = sum(mu[d] * tau[n // d] for d in range(1, n + 1) if n % d == 0)
    return bits


def block_complexity(word: list[int], width: int) -> int:
    if width > len(word):
        return 0
    return len({tuple(word[i:i + width]) for i in range(len(word) - width + 1)})


def support_rows(limit: int, mu: list[int]) -> list[dict]:
    rng = random.Random(257)
    supports: dict[str, list[int]] = {}
    supports["periodic_mod_3"] = [0] + [int(n % 3 == 1) for n in range(1, limit + 1)]
    supports["squares"] = [0] * (limit + 1)
    for n in range(1, int(limit ** 0.5) + 1):
        supports["squares"][n * n] = 1
    alpha = 2 ** 0.5 - 1
    supports["sturmian_sqrt2_minus_1"] = [0] + [
        int(int((n + 1) * alpha) != int(n * alpha)) for n in range(1, limit + 1)
    ]
    supports["random_matched_density"] = [0] + [int(rng.random() < alpha) for _ in range(limit)]

    rows = []
    for name, bits in supports.items():
        tau = divisor_transform(bits)
        recovered = invert_transform(tau, mu)
        rows.append({
            "name": name,
            "limit": limit,
            "selected": sum(bits),
            "exact_reconstruction": recovered == bits,
            "first_mismatch": next((n for n in range(1, limit + 1) if recovered[n] != bits[n]), None),
            "input_block_complexity_1_to_5": [block_complexity(bits[1:], k) for k in range(1, 6)],
            "tau_block_complexity_1_to_5": [block_complexity(tau[1:], k) for k in range(1, 6)],
            "tau_prefix_sha256": hashlib.sha256(json.dumps(tau[1:]).encode()).hexdigest(),
        })
    return rows


def exhaustive_prefix_audit(width: int, mu: list[int]) -> dict:
    images: set[tuple[int, ...]] = set()
    failures = []
    for mask in range(1 << width):
        bits = [0] + [(mask >> (n - 1)) & 1 for n in range(1, width + 1)]
        tau = divisor_transform(bits)
        recovered = invert_transform(tau, mu)
        image = tuple(tau[1:])
        images.add(image)
        if recovered != bits and len(failures) < 10:
            failures.append({"mask": mask, "bits": bits[1:], "recovered": recovered[1:]})
    return {
        "width": width,
        "boolean_prefixes": 1 << width,
        "distinct_transform_prefixes": len(images),
        "collisions": (1 << width) - len(images),
        "reconstruction_failures": failures,
        "status": "exact_bijection" if len(images) == (1 << width) and not failures else "FAIL",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=4096)
    parser.add_argument("--exhaustive-width", type=int, default=16)
    parser.add_argument("--output", type=Path, default=REPO_ROOT / RECEIPT)
    args = parser.parse_args()
    if args.limit < args.exhaustive_width or args.exhaustive_width < 1:
        raise SystemExit("require limit >= exhaustive-width >= 1")

    mu = mobius_sieve(args.limit)
    rows = support_rows(args.limit, mu)
    exhaustive = exhaustive_prefix_audit(args.exhaustive_width, mu)
    all_ok = exhaustive["status"] == "exact_bijection" and all(r["exact_reconstruction"] for r in rows)
    payload = {
        "schema": "erdos257.dirichlet_transform_invertibility.v1",
        "script": str(SCRIPT),
        "statement": {
            "forward": "tau_A(n) = sum_{d|n} 1_A(d)",
            "inverse": "1_A(n) = sum_{d|n} mu(d) tau_A(n/d)",
            "prefix_locality": "tau_A[1:M] determines 1_A[1:M] exactly",
            "kernel": "zero",
        },
        "mechanism_decision": "kernel_and_information_erasure_lane_eliminated",
        "reason": (
            "The divisor transform is a triangular bijection, not an information-erasing map. "
            "Similar low-order subword-complexity counts measure saturation of that projection; "
            "they do not imply that support structure or complexity was destroyed."
        ),
        "exhaustive_boolean_prefix_audit": exhaustive,
        "structured_support_audit": rows,
        "nonclaims": [
            "This exact invertibility does not prove or refute Erdos 257.",
            "Finite block-complexity measurements do not establish an asymptotic density-only law.",
            "The obstruction is not loss of A inside tau_A; it is finding an analytic argument that uses the recovered Booleanity together with rational carry constraints.",
        ],
        "status": "ok" if all_ok else "FAIL",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
