#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Differential check: the published return schema and the repository validator agree.

The defect this guards against (found 2026-09-14): after the repository was
renamed, ``docs/repository_identity.json`` named the new origin and still
selected ``research-return-receipt/1`` as the current submission contract,
while that schema file constrained ``repository.origin`` to the former origin.
A contributor validating against the published schema and a contributor
running ``scripts/validate_research_return.py`` received contradictory
structural verdicts for the same payload.

Checked here, all from the identity owner rather than from hard-coded values:

* the current schema file exists and its ``$id``, ``schema`` constant, and
  ``repository.origin`` constant equal the identity's current origin and
  current submission schema;
* every historical receipt contract's schema file exists and its constants
  equal that historical row, so old receipts keep validating against the
  schema they were written under;
* the post-rename contract differs from the current one, so a future rename
  cannot be a silent no-op;
* the submitted-return fixture that CI validates with the repository
  validator also satisfies the published schema's constants (and the full
  schema when ``jsonschema`` happens to be importable), and the historical
  validation fixture still matches its own historical schema.

This test never rewrites any file. It is a structural agreement check, not a
review of mathematical or evidential content.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import repository_identity


ROOT = Path(__file__).resolve().parents[1]
SUBMITTED_FIXTURE = ROOT / ".github" / "fixtures" / "unaccepted-research-return.json"
VALIDATION_FIXTURES = (
    ROOT / "scripts" / "fixtures" / "research_returns" / "valid_inconclusive.json",
    ROOT / "docs" / "research-commons" / "returns" / "negative-example.json",
)


def require(condition: bool, message: str) -> None:
    """Keep the check active under ``python -O``."""
    if not condition:
        raise AssertionError(message)


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def resolve_local_ref(schema: dict, node: dict) -> dict:
    """Follow one level of ``#/$defs/...`` reference inside the same document."""
    ref = node.get("$ref")
    if not isinstance(ref, str) or not ref.startswith("#/"):
        return node
    target: object = schema
    for part in ref[2:].split("/"):
        require(isinstance(target, dict) and part in target, f"unresolvable local $ref {ref!r}")
        target = target[part]  # type: ignore[index]
    require(isinstance(target, dict), f"local $ref {ref!r} is not an object")
    return target  # type: ignore[return-value]


def schema_constants(schema: dict) -> tuple[str, str, str]:
    schema_id = schema.get("$id")
    schema_const = schema.get("properties", {}).get("schema", {}).get("const")
    repository = resolve_local_ref(schema, schema.get("properties", {}).get("repository", {}))
    origin_const = repository.get("properties", {}).get("origin", {}).get("const")
    require(isinstance(schema_id, str) and schema_id, "schema lacks a string $id")
    require(isinstance(schema_const, str), "schema lacks a constant schema value")
    require(isinstance(origin_const, str), "schema lacks a constant repository.origin")
    return schema_id, schema_const, origin_const


def check_schema_file(path: Path, expected_schema: str, expected_origin: str, label: str) -> dict:
    require(path.is_file(), f"{label}: schema file is missing: {path.relative_to(ROOT)}")
    schema = load_json(path)
    schema_id, schema_const, origin_const = schema_constants(schema)
    require(
        schema_const == expected_schema,
        f"{label}: schema constant {schema_const!r} != identity {expected_schema!r}",
    )
    require(
        origin_const == expected_origin,
        f"{label}: repository.origin constant {origin_const!r} != identity {expected_origin!r}",
    )
    require(
        schema_id.startswith(expected_origin + "/"),
        f"{label}: $id {schema_id!r} does not live under {expected_origin!r}",
    )
    require(
        schema_id.endswith("/" + path.relative_to(ROOT).as_posix()),
        f"{label}: $id {schema_id!r} does not end with the file's own path",
    )
    return schema


def payload_matches_constants(payload: dict, schema: dict, label: str) -> None:
    _, schema_const, origin_const = schema_constants(schema)
    require(
        payload.get("schema") == schema_const,
        f"{label}: payload schema {payload.get('schema')!r} != published constant {schema_const!r}",
    )
    require(
        payload.get("repository", {}).get("origin") == origin_const,
        f"{label}: payload origin != published constant {origin_const!r}",
    )


def full_schema_verdict(payload: dict, schema: dict, label: str) -> str:
    try:
        import jsonschema  # type: ignore
    except ImportError:
        return f"{label}: jsonschema not importable; constant-level agreement only"
    validator_cls = jsonschema.validators.validator_for(schema)
    validator_cls.check_schema(schema)
    errors = sorted(validator_cls(schema).iter_errors(payload), key=lambda e: list(e.path))
    require(
        not errors,
        f"{label}: published schema rejects the payload: "
        + "; ".join(f"{'/'.join(map(str, e.path))}: {e.message}" for e in errors[:5]),
    )
    return f"{label}: full jsonschema validation passed"


def repository_validator_accepts(path: Path, *flags: str) -> None:
    completed = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "validate_research_return.py"), str(path), *flags],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    require(
        completed.returncode == 0,
        f"repository validator rejected {path.relative_to(ROOT)}: "
        f"{completed.stdout.strip()[:600]} {completed.stderr.strip()[:300]}",
    )


def main() -> int:
    identity = repository_identity.load_identity()
    current_origin = identity["current"]["origin"]
    contracts = identity["contracts"]
    current_schema = check_schema_file(
        ROOT / contracts["current_schema_path"],
        contracts["current_submission_schema"],
        current_origin,
        "current contract",
    )
    require(
        contracts["post_rename_submission_schema"] != contracts["current_submission_schema"]
        and contracts["post_rename_schema_path"] != contracts["current_schema_path"],
        "post-rename contract must differ from the current one so a rename is never a silent no-op",
    )
    historical_schemas: dict[tuple[str, str], dict] = {}
    for row in identity["historical_receipt_contracts"]:
        schema = check_schema_file(
            ROOT / row["schema_path"],
            row["schema_value"],
            row["origin"],
            f"historical contract {row['schema_value']} @ {row['origin']}",
        )
        require(
            schema["$id"] == row["schema_id"],
            f"historical schema $id {schema['$id']!r} != identity row {row['schema_id']!r}",
        )
        historical_schemas[(row["schema_value"], row["origin"])] = schema

    # Differential: the submitted fixture CI validates must satisfy the
    # published current schema, not only the repository validator.
    submitted = load_json(SUBMITTED_FIXTURE)
    require(submitted.get("record_kind") == "submitted_return", "CI fixture is not a submitted return")
    payload_matches_constants(submitted, current_schema, "submitted fixture")
    receipts = [full_schema_verdict(submitted, current_schema, "submitted fixture")]
    repository_validator_accepts(SUBMITTED_FIXTURE, "--require-submitted")

    for path in VALIDATION_FIXTURES:
        payload = load_json(path)
        pair = (payload.get("schema"), payload.get("repository", {}).get("origin"))
        if pair == (contracts["current_submission_schema"], current_origin):
            schema = current_schema
        else:
            require(
                pair in historical_schemas,
                f"{path.relative_to(ROOT)} carries a schema/origin pair recorded nowhere: {pair}",
            )
            schema = historical_schemas[pair]
        label = f"validation fixture {path.name}"
        payload_matches_constants(payload, schema, label)
        receipts.append(full_schema_verdict(payload, schema, label))
        repository_validator_accepts(path)

    print("test_contribution_contract_agreement: published schema and repository validator agree")
    for line in receipts:
        print("  " + line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
