#!/usr/bin/env python3
"""Search periodic rational digits with Boolean ancestry and growing carry.

For a periodic binary digit word epsilon and an integer carry C, put

    tau(n) = 2*C(n-1) + epsilon(n) - C(n).

The Mersenne support is Boolean exactly when the Möbius transform of tau is
in {0,1}.  Earlier finite-state searches bounded C by a fixed constant; that
class forces finite support.  This model instead imposes

    0 <= C(n) <= floor(B*sqrt(n)) + offset

and positive-density constraints at dyadic checkpoints.  Feasibility at every
depth would therefore have a König-lemma consumer: a locally finite infinite
branch with tempered carry and infinite Boolean support, hence a rational
Mersenne subsum.  A finite feasible receipt is a candidate prefix, not a proof.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import math
import time
import zlib
from pathlib import Path

import numpy as np
import scipy
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_DIR = SCRIPT_PATH.parent
REPO_ROOT = SCRIPT_DIR.parents[2]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "periodic_sqrt_carry_milp_receipt.json"
)
DEFAULT_WORD = "0000100101001011000101"


def canonical_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mobius_sieve(limit: int) -> list[int]:
    mu = [0] * (limit + 1)
    mu[1] = 1
    primes: list[int] = []
    composite = bytearray(limit + 1)
    for value in range(2, limit + 1):
        if not composite[value]:
            primes.append(value)
            mu[value] = -1
        for prime in primes:
            if value * prime > limit:
                break
            composite[value * prime] = 1
            if value % prime == 0:
                mu[value * prime] = 0
                break
            mu[value * prime] = -mu[value]
    return mu


def checkpoints(depth: int, start: int) -> list[int]:
    result = []
    value = start
    while value < depth:
        result.append(value)
        value *= 2
    if not result or result[-1] != depth:
        result.append(depth)
    return result


def carry_bound(rank: int, numerator: int, denominator: int, offset: int) -> int:
    return numerator * math.isqrt(rank) // denominator + offset


def encode_support(bits: np.ndarray) -> str:
    return base64.b64encode(np.packbits(bits.astype(np.uint8), bitorder="little")).decode()


def decode_support(encoded: str, depth: int) -> np.ndarray:
    raw = np.frombuffer(base64.b64decode(encoded), dtype=np.uint8)
    return np.unpackbits(raw, bitorder="little")[:depth].astype(np.int64)


def encode_carry(values: np.ndarray) -> tuple[str, str]:
    maximum = int(values.max())
    if maximum <= np.iinfo(np.uint8).max:
        dtype = np.dtype("<u1")
    elif maximum <= np.iinfo(np.uint16).max:
        dtype = np.dtype("<u2")
    else:
        dtype = np.dtype("<u4")
    compressed = zlib.compress(values.astype(dtype).tobytes(), level=9)
    return base64.b64encode(compressed).decode(), dtype.str


def decode_carry(solution: dict[str, object], depth: int) -> np.ndarray:
    if "carry" in solution:  # Compatibility with pre-compression receipts.
        return np.asarray(solution["carry"], dtype=np.int64)
    dtype = np.dtype(solution["carry_dtype"])
    raw = zlib.decompress(base64.b64decode(solution["carry_zlib_base64"]))
    values = np.frombuffer(raw, dtype=dtype).astype(np.int64)
    if len(values) != depth + 1:
        raise ValueError("compressed carry has inconsistent length")
    return values


def integer_array_sha256(values: np.ndarray) -> str:
    return hashlib.sha256(values.astype(np.int64).tobytes()).hexdigest()


def support_array_sha256(values: np.ndarray) -> str:
    return hashlib.sha256(values.astype(np.uint8).tobytes()).hexdigest()


def load_prefix(path: Path) -> tuple[np.ndarray, np.ndarray, dict[str, object]]:
    receipt = json.loads(path.read_text())
    depth = int(receipt["parameters"]["depth"])
    carry = decode_carry(receipt["solution"], depth)
    support = decode_support(receipt["solution"]["support_bits_base64"], depth)
    if len(carry) != depth + 1 or len(support) != depth:
        raise ValueError("prefix receipt has inconsistent solution lengths")
    return carry, support, receipt


def build_model(args: argparse.Namespace, prefix):
    depth = args.depth
    word = args.word
    mu = mobius_sieve(depth)
    row_indices: list[int] = []
    column_indices: list[int] = []
    values: list[int] = []
    lower: list[float] = []
    upper: list[float] = []
    rhs = [0] * depth

    # Möbius-transform equations. Variables are C_0..C_N, then b_1..b_N.
    for divisor in range(1, depth + 1):
        digit = int(word[(divisor - 1) % len(word)])
        for multiple in range(divisor, depth + 1, divisor):
            coefficient = mu[multiple // divisor]
            if not coefficient:
                continue
            row_indices.extend((multiple - 1, multiple - 1))
            column_indices.extend((divisor - 1, divisor))
            values.extend((-2 * coefficient, coefficient))
            rhs[multiple - 1] += coefficient * digit
    for rank in range(1, depth + 1):
        row_indices.append(rank - 1)
        column_indices.append(depth + rank)
        values.append(1)
        lower.append(rhs[rank - 1])
        upper.append(rhs[rank - 1])

    density_checkpoints = checkpoints(depth, args.density_start)
    for checkpoint in density_checkpoints:
        row = len(lower)
        for rank in range(1, checkpoint + 1):
            row_indices.append(row)
            column_indices.append(depth + rank)
            values.append(1)
        lower.append(math.ceil(checkpoint * args.density_num / args.density_den))
        upper.append(np.inf)

    matrix = coo_matrix(
        (values, (row_indices, column_indices)),
        shape=(len(lower), 2 * depth + 1),
    ).tocsr()
    variable_lower = np.zeros(2 * depth + 1)
    variable_upper = np.ones(2 * depth + 1)
    variable_upper[: depth + 1] = [0] + [
        carry_bound(
            rank,
            args.carry_factor_num,
            args.carry_factor_den,
            args.carry_offset,
        )
        for rank in range(1, depth + 1)
    ]
    variable_upper[depth + 1] = 0  # b_1=0 because w_1=1.

    prefix_depth = 0
    if prefix is not None:
        prefix_carry, prefix_support, prefix_receipt = prefix
        prefix_depth = len(prefix_support)
        if prefix_depth >= depth:
            raise ValueError("extension depth must exceed the frozen prefix depth")
        if prefix_receipt["parameters"]["word"] != word:
            raise ValueError("prefix periodic word does not match")
        variable_lower[: prefix_depth + 1] = prefix_carry
        variable_upper[: prefix_depth + 1] = prefix_carry
        support_start = depth + 1
        variable_lower[support_start : support_start + prefix_depth] = prefix_support
        variable_upper[support_start : support_start + prefix_depth] = prefix_support

    objective = np.zeros(2 * depth + 1)
    objective[: depth + 1] = 1
    return (
        matrix,
        np.asarray(lower),
        np.asarray(upper),
        variable_lower,
        variable_upper,
        objective,
        density_checkpoints,
        prefix_depth,
    )


def verify_solution(
    args: argparse.Namespace,
    carry: np.ndarray,
    support: np.ndarray,
    density_checkpoints: list[int],
) -> dict[str, object]:
    depth = args.depth
    divisor_load = np.zeros(depth + 1, dtype=np.int64)
    for index in np.flatnonzero(support) + 1:
        divisor_load[index : depth + 1 : index] += 1
    recurrence_violations = 0
    bound_violations = 0
    nonboolean_count = int(np.count_nonzero((support != 0) & (support != 1)))
    for rank in range(1, depth + 1):
        digit = int(args.word[(rank - 1) % len(args.word)])
        if divisor_load[rank] != 2 * carry[rank - 1] + digit - carry[rank]:
            recurrence_violations += 1
        if carry[rank] < 0 or carry[rank] > carry_bound(
            rank,
            args.carry_factor_num,
            args.carry_factor_den,
            args.carry_offset,
        ):
            bound_violations += 1
    density_rows = [
        {
            "rank": checkpoint,
            "selected_count": int(support[:checkpoint].sum()),
            "required_count": math.ceil(
                checkpoint * args.density_num / args.density_den
            ),
        }
        for checkpoint in density_checkpoints
    ]
    return {
        "carry_recurrence_violation_count": recurrence_violations,
        "carry_bound_violation_count": bound_violations,
        "nonboolean_support_count": nonboolean_count,
        "b_1_is_zero": bool(support[0] == 0),
        "density_checkpoint_violations": sum(
            row["selected_count"] < row["required_count"] for row in density_rows
        ),
        "density_checkpoints": density_rows,
        "ok": (
            recurrence_violations == 0
            and bound_violations == 0
            and nonboolean_count == 0
            and support[0] == 0
            and all(row["selected_count"] >= row["required_count"] for row in density_rows)
        ),
    }


def solve(args: argparse.Namespace) -> dict[str, object]:
    prefix = load_prefix(args.prefix_receipt) if args.prefix_receipt else None
    prefix_source = prefix[2] if prefix is not None else None
    if prefix is not None and args.freeze_prefix_depth is not None:
        prefix_carry, prefix_support, prefix_receipt = prefix
        if not 1 <= args.freeze_prefix_depth <= len(prefix_support):
            raise ValueError("--freeze-prefix-depth lies outside the prefix receipt")
        prefix = (
            prefix_carry[: args.freeze_prefix_depth + 1],
            prefix_support[: args.freeze_prefix_depth],
            prefix_receipt,
        )
    frozen_prefix_carry = prefix[0] if prefix is not None else None
    frozen_prefix_support = prefix[1] if prefix is not None else None
    build_started = time.monotonic()
    (
        matrix,
        constraint_lower,
        constraint_upper,
        variable_lower,
        variable_upper,
        objective,
        density_checkpoints,
        prefix_depth,
    ) = build_model(args, prefix)
    build_seconds = time.monotonic() - build_started
    solve_started = time.monotonic()
    result = milp(
        objective,
        integrality=np.ones(2 * args.depth + 1),
        bounds=Bounds(variable_lower, variable_upper),
        constraints=LinearConstraint(matrix, constraint_lower, constraint_upper),
        options={"time_limit": args.time_limit, "presolve": True},
    )
    solve_seconds = time.monotonic() - solve_started
    if result.x is None:
        raise RuntimeError(
            f"MILP produced no feasible point: status={result.status} {result.message}"
        )
    rounded = np.rint(result.x).astype(np.int64)
    carry = rounded[: args.depth + 1]
    support = rounded[args.depth + 1 :]
    validation = verify_solution(args, carry, support, density_checkpoints)
    if not validation["ok"]:
        raise RuntimeError(f"solver point failed exact verification: {validation}")

    word_integer = int(args.word, 2)
    encoded_carry, carry_dtype = encode_carry(carry)
    payload: dict[str, object] = {
        "schema": "erdos257_periodic_sqrt_carry_milp_v1",
        "programme_target": (
            "Construct an infinite Boolean support with rational periodic binary "
            "Lambert digits by a positive-density, subexponential-carry compactness tree."
        ),
        "claim_boundary": (
            "This is one exact finite feasible node. It proves neither feasibility "
            "at all depths nor existence of an infinite compatible branch."
        ),
        "parameters": {
            "depth": args.depth,
            "word": args.word,
            "word_period": len(args.word),
            "rational_digit_value": {
                "numerator": word_integer,
                "denominator": (1 << len(args.word)) - 1,
            },
            "carry_factor_num": args.carry_factor_num,
            "carry_factor_den": args.carry_factor_den,
            "carry_offset": args.carry_offset,
            "density_num": args.density_num,
            "density_den": args.density_den,
            "density_start": args.density_start,
            "objective": "minimize_sum_of_carries",
            "time_limit_seconds": args.time_limit,
            "frozen_prefix_depth": prefix_depth,
            "prefix_receipt": (
                str(args.prefix_receipt.relative_to(REPO_ROOT))
                if args.prefix_receipt and args.prefix_receipt.is_relative_to(REPO_ROOT)
                else str(args.prefix_receipt) if args.prefix_receipt else None
            ),
            "prefix_payload_sha256": (
                prefix_source.get("payload_sha256") if prefix_source else None
            ),
            "prefix_support_sha256": (
                prefix_source["solution"]["support_sha256"] if prefix_source else None
            ),
            "prefix_carry_sha256": (
                prefix_source["solution"]["carry_sha256"] if prefix_source else None
            ),
            "frozen_prefix_support_sha256": (
                support_array_sha256(frozen_prefix_support)
                if frozen_prefix_support is not None
                else None
            ),
            "frozen_prefix_carry_sha256": (
                integer_array_sha256(frozen_prefix_carry)
                if frozen_prefix_carry is not None
                else None
            ),
        },
        "source": {
            "script": str(SCRIPT_PATH.relative_to(REPO_ROOT)),
            "script_sha256": sha256(SCRIPT_PATH),
            "numpy_version": np.__version__,
            "scipy_version": scipy.__version__,
        },
        "solver": {
            "status": int(result.status),
            "message": result.message,
            "objective_value": int(carry.sum()),
            "build_seconds": round(build_seconds, 6),
            "solve_seconds": round(solve_seconds, 6),
            "matrix_nonzero_count": int(matrix.nnz),
        },
        "validation": validation,
        "statistics": {
            "selected_count": int(support.sum()),
            "support_density": round(float(support.mean()), 12),
            "max_carry": int(carry.max()),
            "last_carry": int(carry[-1]),
            "max_carry_last_rank": int(np.flatnonzero(carry == carry.max())[-1]),
            "last_32_carries": carry[-32:].tolist(),
        },
        "solution": {
            "carry_zlib_base64": encoded_carry,
            "carry_dtype": carry_dtype,
            "carry_length": len(carry),
            "support_bits_base64": encode_support(support),
            "support_bit_order": "little",
            "support_sha256": support_array_sha256(support),
            "carry_sha256": integer_array_sha256(carry),
        },
        "mechanism_decision": {
            "status": "finite_positive_density_sqrt_carry_node_found",
            "compactness_consumer": (
                "Feasibility at every depth with these fixed pointwise constraints "
                "would yield an infinite positive-density tempered branch by König's lemma."
            ),
            "remaining_obstruction": (
                "Prove all-depth feasibility or find a recursively extendable node family; "
                "arbitrary optimizer-selected prefixes may be dead ends."
            ),
        },
    }
    payload["payload_sha256"] = hashlib.sha256(canonical_bytes(payload)).hexdigest()
    return payload


def check_receipt(path: Path) -> dict[str, object]:
    receipt = json.loads(path.read_text())
    claimed_digest = receipt.pop("payload_sha256")
    actual_digest = hashlib.sha256(canonical_bytes(receipt)).hexdigest()
    parameters = receipt["parameters"]
    args = argparse.Namespace(
        depth=int(parameters["depth"]),
        word=parameters["word"],
        carry_factor_num=int(parameters["carry_factor_num"]),
        carry_factor_den=int(parameters["carry_factor_den"]),
        carry_offset=int(parameters["carry_offset"]),
        density_num=int(parameters["density_num"]),
        density_den=int(parameters["density_den"]),
        density_start=int(parameters["density_start"]),
    )
    carry = decode_carry(receipt["solution"], args.depth)
    support = decode_support(receipt["solution"]["support_bits_base64"], args.depth)
    validation = verify_solution(args, carry, support, checkpoints(args.depth, args.density_start))
    source_hash_matches = receipt["source"]["script_sha256"] == sha256(SCRIPT_PATH)
    prefix_chain = {"status": "not_applicable", "ok": True}
    prefix_path_value = parameters.get("prefix_receipt")
    if prefix_path_value:
        prefix_path = Path(prefix_path_value)
        if not prefix_path.is_absolute():
            prefix_path = REPO_ROOT / prefix_path
        if not prefix_path.is_file():
            prefix_chain = {"status": "missing_prefix_receipt", "ok": False}
        else:
            prefix_receipt = json.loads(prefix_path.read_text())
            prefix_depth = int(parameters["frozen_prefix_depth"])
            source_depth = int(prefix_receipt["parameters"]["depth"])
            prefix_carry = decode_carry(prefix_receipt["solution"], source_depth)
            prefix_support = decode_support(
                prefix_receipt["solution"]["support_bits_base64"], source_depth
            )
            checks = {
                "payload_digest_matches": (
                    prefix_receipt["payload_sha256"]
                    == parameters["prefix_payload_sha256"]
                ),
                "frozen_carry_hash_matches": (
                    integer_array_sha256(prefix_carry[: prefix_depth + 1])
                    == parameters["frozen_prefix_carry_sha256"]
                ),
                "frozen_support_hash_matches": (
                    support_array_sha256(prefix_support[:prefix_depth])
                    == parameters["frozen_prefix_support_sha256"]
                ),
                "current_carry_prefix_matches": bool(
                    np.array_equal(carry[: prefix_depth + 1], prefix_carry[: prefix_depth + 1])
                ),
                "current_support_prefix_matches": bool(
                    np.array_equal(support[:prefix_depth], prefix_support[:prefix_depth])
                ),
            }
            prefix_chain = {
                "status": "checked",
                **checks,
                "ok": all(checks.values()),
            }
    return {
        "payload_digest_matches": claimed_digest == actual_digest,
        "payload_sha256": claimed_digest,
        "source_hash_matches": source_hash_matches,
        "prefix_chain": prefix_chain,
        "solution_validation": validation,
        "ok": (
            claimed_digest == actual_digest
            and source_hash_matches
            and validation["ok"]
            and prefix_chain["ok"]
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=200000)
    parser.add_argument("--word", default=DEFAULT_WORD)
    parser.add_argument("--carry-factor-num", type=int, default=1)
    parser.add_argument("--carry-factor-den", type=int, default=1)
    parser.add_argument("--carry-offset", type=int, default=1)
    parser.add_argument("--density-num", type=int, default=1)
    parser.add_argument("--density-den", type=int, default=4)
    parser.add_argument("--density-start", type=int, default=64)
    parser.add_argument("--time-limit", type=float, default=600.0)
    parser.add_argument("--prefix-receipt", type=Path)
    parser.add_argument(
        "--freeze-prefix-depth",
        type=int,
        help="Freeze only this many ranks from --prefix-receipt, leaving its look-ahead tail free.",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check-receipt", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.check_receipt:
        result = check_receipt(args.check_receipt)
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0 if result["ok"] else 1
    if not args.word or set(args.word) - {"0", "1"}:
        raise SystemExit("--word must be a nonempty binary string")
    if args.depth < args.density_start or args.carry_factor_den <= 0 or args.density_den <= 0:
        raise SystemExit("invalid depth, carry factor, or density parameters")
    receipt = solve(args)
    rendered = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered)
    print(
        json.dumps(
            {
                "parameters": receipt["parameters"],
                "solver": receipt["solver"],
                "validation": receipt["validation"],
                "statistics": receipt["statistics"],
                "mechanism_decision": receipt["mechanism_decision"],
                "payload_sha256": receipt["payload_sha256"],
                "output": str(args.output),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
