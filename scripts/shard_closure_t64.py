#!/usr/bin/env python3
"""Split the generated ClosureT64 monolith into dependency-safe Lean modules.

The original certificate emitter is not available in this repository.  This
tool therefore owns the one-time, proof-term-preserving migration and the
durable structural check; it does not pretend to be the certificate emitter.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "Erdos249257" / "DiagonalPincerPrimeCertificates"
AGGREGATOR = BASE / "ClosureT64.lean"
SHARD_DIR = BASE / "ClosureT64"
MANIFEST = ROOT / "docs" / "generated_certificate_manifest.json"
CLAIMS = ROOT / "docs" / "claims.json"
GENERATED_SCHEMAS = ROOT / "docs" / "semantic" / "generated_schemas.json"
MODULE_PREFIX = "Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64"
EXPECTED_THEOREM_COUNT = 1242
EXPECTED_THEOREM_DIGEST = "6dba91bbc8cf05c37f7a41893b45e54ccd0085d1c610aeca858c7cd55c4be51c"
THEOREM_START = re.compile(r"(?m)^theorem (prime_lucas_\d+)\b")
THEOREM_REF = re.compile(r"\bprime_lucas_\d+\b")

SUPPORT_TEXT = """import Erdos249257.DiagonalPincerCertificates

/-!
# Shared support for the Lucas closure through t=64

This generated support module contains the two proof-kernel-preserving helper
lemmas shared by the dependency-safe ClosureT64 certificate shards.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem natCast_zmod_eq_one_iff (a m : ℕ) :
    (a : ZMod m) = 1 ↔ a % m = 1 % m := by
  simpa using ZMod.natCast_eq_natCast_iff' a 1 m

theorem natCast_zmod_ne_one_iff (a m : ℕ) :
    (a : ZMod m) ≠ 1 ↔ a % m ≠ 1 % m := by
  exact not_congr (natCast_zmod_eq_one_iff a m)

end TotientTailPeriodKiller
end Erdos249257
"""


def parse_theorems(text: str) -> dict[str, str]:
    matches = list(THEOREM_START.finditer(text))
    if not matches:
        return {}
    namespace_end = text.find("\nend TotientTailPeriodKiller", matches[-1].start())
    if namespace_end < 0:
        raise ValueError("missing TotientTailPeriodKiller namespace terminator")
    blocks: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else namespace_end
        name = match.group(1)
        if name in blocks:
            raise ValueError(f"duplicate theorem {name}")
        blocks[name] = text[match.start() : end].rstrip() + "\n"
    return blocks


def theorem_digest(blocks: dict[str, str]) -> str:
    digest = hashlib.sha256()
    for name in sorted(blocks):
        digest.update(name.encode())
        digest.update(b"\0")
        digest.update(blocks[name].encode())
        digest.update(b"\0")
    return digest.hexdigest()


def dependencies(blocks: dict[str, str]) -> dict[str, set[str]]:
    names = set(blocks)
    result: dict[str, set[str]] = {}
    for name, block in blocks.items():
        refs = set(THEOREM_REF.findall(block)) - {name}
        missing = refs - names
        if missing:
            raise ValueError(f"{name} references unsharded theorems: {sorted(missing)}")
        result[name] = refs
    return result


def depths(deps: dict[str, set[str]]) -> dict[str, int]:
    result: dict[str, int] = {}
    visiting: set[str] = set()

    def visit(name: str) -> int:
        if name in result:
            return result[name]
        if name in visiting:
            raise ValueError(f"dependency cycle through {name}")
        visiting.add(name)
        value = 0 if not deps[name] else 1 + max(visit(dep) for dep in deps[name])
        visiting.remove(name)
        result[name] = value
        return value

    for name in deps:
        visit(name)
    return result


def assign_shards(blocks: dict[str, str]) -> tuple[dict[str, list[str]], dict[str, str]]:
    deps = dependencies(blocks)
    levels = depths(deps)
    grouped: dict[int, list[str]] = defaultdict(list)
    for name, level in levels.items():
        grouped[level].append(name)

    shards: dict[str, list[str]] = {}
    owner: dict[str, str] = {}
    for level in sorted(grouped):
        names = grouped[level]
        bin_count = 2 if len(names) > 1 else 1
        bins: list[list[str]] = [[] for _ in range(bin_count)]
        weights = [0] * bin_count
        for name in sorted(names, key=lambda item: (-len(blocks[item].encode()), item)):
            target = min(range(bin_count), key=lambda index: (weights[index], index))
            bins[target].append(name)
            weights[target] += len(blocks[name].encode())
        for index, members in enumerate(bins):
            shard = f"Level{level}{chr(ord('A') + index)}"
            shards[shard] = sorted(members)
            for name in members:
                owner[name] = shard
    return shards, owner


def shard_text(
    shard: str,
    names: list[str],
    blocks: dict[str, str],
    owner: dict[str, str],
) -> str:
    deps = dependencies(blocks)
    prerequisite_shards = sorted({owner[dep] for name in names for dep in deps[name]})
    imports = [f"import {MODULE_PREFIX}.Support"] + [
        f"import {MODULE_PREFIX}.{dependency}" for dependency in prerequisite_shards
    ]
    level = re.fullmatch(r"Level(\d+)[A-Z]", shard).group(1)  # type: ignore[union-attr]
    body = "\n".join(blocks[name].rstrip() for name in names)
    return (
        "\n".join(imports)
        + f"\n\n/-!\n# ClosureT64 dependency level {level}\n\n"
        + "Generated deterministically by `scripts/shard_closure_t64.py`; "
        + "proof bodies are preserved verbatim from the original monolith.\n-/\n\n"
        + "namespace Erdos249257\nnamespace TotientTailPeriodKiller\n\n"
        + "set_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n\n"
        + body
        + "\n\nend TotientTailPeriodKiller\nend Erdos249257\n"
    )


def expected_files(blocks: dict[str, str]) -> dict[Path, str]:
    shards, owner = assign_shards(blocks)
    result = {SHARD_DIR / "Support.lean": SUPPORT_TEXT}
    for shard, names in shards.items():
        result[SHARD_DIR / f"{shard}.lean"] = shard_text(shard, names, blocks, owner)
    imports = [f"import {MODULE_PREFIX}.Support"] + [
        f"import {MODULE_PREFIX}.{shard}" for shard in sorted(shards)
    ]
    result[AGGREGATOR] = (
        "\n".join(imports)
        + "\n\n/-!\n# Shared Lucas closure through t=64\n\n"
        + "Stable public import surface for the dependency-safe generated certificate shards.\n"
        + "The shard owner preserves the original 1,242 theorem bodies exactly and does not\n"
        + "change the proof-authority posture (`decide +kernel` and `lucas_primality`).\n-/\n"
    )
    return result


def closure_paths(files: dict[Path, str]) -> list[str]:
    return sorted(str(path.relative_to(ROOT)) for path in files)


def update_manifest(paths: list[str], *, write: bool) -> None:
    data = json.loads(MANIFEST.read_text())
    family = next(row for row in data["families"] if row["id"] == "lucas_primality_closures")
    old_prefix = "Erdos249257/DiagonalPincerPrimeCertificates/ClosureT64"
    retained = [path for path in family["module_paths"] if not path.startswith(old_prefix)]
    expected_paths = sorted(retained + paths)
    family["module_paths"] = expected_paths
    family["module_count"] = len(expected_paths)
    family["generator"] = (
        "ai_workflow/tools/meta/factory/build_erdos249_diagonal_pincer_certificates.py "
        "emits the source monolith; scripts/shard_closure_t64.py owns its "
        "proof-term-preserving public sharding and structural check"
    )
    family["provenance_evidence"] = (
        "One module per prime, named Prime<value>.lean; ClosureT64 is a stable aggregator "
        "over deterministic dependency-level shards whose theorem bodies preserve the "
        "original generated monolith exactly. Congruences use kernel `decide`, with "
        "`lucas_primality` as the proof-producing theorem."
    )
    rendered = json.dumps(data, indent=1) + "\n"
    if write:
        MANIFEST.write_text(rendered)
    elif MANIFEST.read_text() != rendered:
        raise ValueError("generated certificate manifest is stale; rerun --apply-monolith")


def check_public_metadata(files: dict[Path, str], blocks: dict[str, str]) -> None:
    claims = json.loads(CLAIMS.read_text())
    nodes = claims["machine_readable_paper"]["module_graph"]["nodes"]
    registry = {row["path"]: row for row in nodes}
    for path, text in files.items():
        relative = str(path.relative_to(ROOT))
        row = registry.get(relative)
        if row is None:
            raise ValueError(f"ClosureT64 module is absent from docs/claims.json: {relative}")
        expected_imports = re.findall(r"(?m)^import (.+)$", text)
        if row["imports"] != expected_imports:
            raise ValueError(f"ClosureT64 module imports are stale in docs/claims.json: {relative}")

    representative = "prime_lucas_2364533768205644535022723273"
    _, owner = assign_shards(blocks)
    representative_path = SHARD_DIR / f"{owner[representative]}.lean"
    representative_line = next(
        index
        for index, line in enumerate(representative_path.read_text().splitlines(), start=1)
        if line.startswith(f"theorem {representative} ")
    )
    claim = next(row for row in claims["claims"] if row["id"] == "diagonal_pincer_t64_primality_closure")
    expected_declaration = {
        "name": representative,
        "module": str(representative_path.relative_to(ROOT)),
        "line": representative_line,
    }
    if claim["declarations"] != [expected_declaration]:
        raise ValueError("diagonal_pincer_t64_primality_closure coordinate is stale")

    schemas = json.loads(GENERATED_SCHEMAS.read_text())
    schema = next(row for row in schemas["families"] if row["id"] == "lucas_shared_closure_t64")
    if schema["module_count"] != len(files):
        raise ValueError("lucas_shared_closure_t64 module_count is stale")
    if "scripts/shard_closure_t64.py" not in schema["generator"]:
        raise ValueError("lucas_shared_closure_t64 does not name its public shard owner")


def apply_monolith() -> None:
    source = AGGREGATOR.read_text()
    blocks = parse_theorems(source)
    if len(blocks) != EXPECTED_THEOREM_COUNT:
        raise ValueError(f"expected {EXPECTED_THEOREM_COUNT} monolith theorems, found {len(blocks)}")
    if theorem_digest(blocks) != EXPECTED_THEOREM_DIGEST:
        raise ValueError("monolith theorem digest differs from the reviewed source")
    files = expected_files(blocks)
    SHARD_DIR.mkdir(parents=True, exist_ok=True)
    for path, text in files.items():
        path.write_text(text)
    update_manifest(closure_paths(files), write=True)
    check()


def check() -> None:
    shard_paths = sorted(SHARD_DIR.glob("Level*.lean"))
    blocks: dict[str, str] = {}
    for path in shard_paths:
        for name, block in parse_theorems(path.read_text()).items():
            if name in blocks:
                raise ValueError(f"duplicate theorem {name} across shards")
            blocks[name] = block
    if len(blocks) != EXPECTED_THEOREM_COUNT:
        raise ValueError(f"expected {EXPECTED_THEOREM_COUNT} shard theorems, found {len(blocks)}")
    digest = theorem_digest(blocks)
    if digest != EXPECTED_THEOREM_DIGEST:
        raise ValueError(f"theorem digest mismatch: {digest}")
    if any("native_decide" in block or "decide +native" in block for block in blocks.values()):
        raise ValueError("native evaluation is forbidden in ClosureT64 shards")

    files = expected_files(blocks)
    actual_paths = {SHARD_DIR / "Support.lean", *shard_paths, AGGREGATOR}
    if actual_paths != set(files):
        unexpected = sorted(str(path.relative_to(ROOT)) for path in actual_paths ^ set(files))
        raise ValueError(f"ClosureT64 file set differs: {unexpected}")
    for path, expected in files.items():
        if not path.exists() or path.read_text() != expected:
            raise ValueError(f"generated shard surface is stale: {path.relative_to(ROOT)}")
    update_manifest(closure_paths(files), write=False)
    check_public_metadata(files, blocks)
    shards, _ = assign_shards(blocks)
    print(
        json.dumps(
            {
                "status": "ok",
                "theorem_count": len(blocks),
                "theorem_digest": digest,
                "dependency_level_count": len({name[:-1] for name in shards}),
                "certificate_shard_count": len(shards),
                "generated_module_count": len(files),
            },
            indent=2,
        )
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--apply-monolith", action="store_true")
    action.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.apply_monolith:
        apply_monolith()
    else:
        check()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
