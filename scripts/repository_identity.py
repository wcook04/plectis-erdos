#!/usr/bin/env python3
"""Load and project the single current public-repository identity authority."""

from __future__ import annotations

import copy
import json
import os
import re
import stat
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_IDENTITY_PATH = ROOT / "docs/repository_identity.json"
NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$")
ORIGIN_RE = re.compile(
    r"^https://github\.com/([A-Za-z0-9][A-Za-z0-9._-]{0,99})/"
    r"([A-Za-z0-9][A-Za-z0-9._-]{0,99})$"
)


class IdentityError(ValueError):
    """The public identity authority is ambiguous or unsafe."""


def path_has_symlink_component(path: Path) -> bool:
    """Reject identity reads that could substitute authority through a link."""
    if path.is_symlink():
        return True
    current = Path(os.path.abspath(path.parent))
    root = Path(current.anchor)
    while True:
        if current.parent != root and current.is_symlink():
            return True
        if current.parent == current:
            return False
        current = current.parent


def read_regular_bytes(path: Path) -> bytes:
    """Read the identity authority through a no-follow regular-file descriptor."""
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise IdentityError(f"could not open repository identity safely: {exc}") from exc
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise IdentityError(
                "could not load repository identity: path must be a regular file"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
    finally:
        os.close(descriptor)


def _string(value: Any, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise IdentityError(f"{field}: must be a non-empty string")
    return value


def _string_list(value: Any, field: str) -> list[str]:
    if not isinstance(value, list) or not value or not all(
        isinstance(item, str) and item for item in value
    ):
        raise IdentityError(f"{field}: must be a non-empty string array")
    if len(value) != len(set(value)):
        raise IdentityError(f"{field}: must not contain duplicates")
    return list(value)


def validate_identity(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise IdentityError("identity authority must be a JSON object")
    required = {
        "schema",
        "current",
        "contracts",
        "historical_receipt_contracts",
        "protected_identity_globs",
        "generated_owner_fan_in",
        "external_activation_classes",
        "approval",
    }
    if set(value) != required:
        raise IdentityError(
            "identity authority fields must equal " + repr(sorted(required))
        )
    if value.get("schema") != "public-repository-identity/1":
        raise IdentityError("schema: must equal public-repository-identity/1")

    current = value.get("current")
    if not isinstance(current, dict) or set(current) != {
        "owner", "slug", "origin", "activation_state"
    }:
        raise IdentityError("current: has an incomplete or ambiguous field set")
    owner = _string(current.get("owner"), "current.owner")
    slug = _string(current.get("slug"), "current.slug")
    if not NAME_RE.fullmatch(owner) or not NAME_RE.fullmatch(slug):
        raise IdentityError("current owner and slug must be conservative GitHub names")
    if slug.casefold().endswith(".git"):
        raise IdentityError("current.slug: must not include a .git suffix")
    origin = _string(current.get("origin"), "current.origin")
    if origin != f"https://github.com/{owner}/{slug}":
        raise IdentityError("current.origin: must be derived exactly from owner and slug")
    _string(current.get("activation_state"), "current.activation_state")

    contracts = value.get("contracts")
    contract_fields = {
        "current_submission_schema",
        "current_schema_path",
        "post_rename_submission_schema",
        "post_rename_schema_path",
    }
    if not isinstance(contracts, dict) or set(contracts) != contract_fields:
        raise IdentityError("contracts: has an incomplete or ambiguous field set")
    for field in contract_fields:
        _string(contracts.get(field), f"contracts.{field}")

    historical = value.get("historical_receipt_contracts")
    if not isinstance(historical, list) or not historical:
        raise IdentityError("historical_receipt_contracts: must be non-empty")
    seen_pairs: set[tuple[str, str]] = set()
    for index, row in enumerate(historical):
        fields = {"schema_value", "origin", "schema_id", "schema_path"}
        if not isinstance(row, dict) or set(row) != fields:
            raise IdentityError(
                f"historical_receipt_contracts[{index}]: has an ambiguous field set"
            )
        schema_value = _string(row.get("schema_value"), f"historical[{index}].schema_value")
        historical_origin = _string(row.get("origin"), f"historical[{index}].origin")
        if ORIGIN_RE.fullmatch(historical_origin) is None:
            raise IdentityError(f"historical[{index}].origin: must be a public GitHub origin")
        _string(row.get("schema_id"), f"historical[{index}].schema_id")
        _string(row.get("schema_path"), f"historical[{index}].schema_path")
        pair = (schema_value, historical_origin)
        if pair in seen_pairs:
            raise IdentityError("historical_receipt_contracts: duplicate schema/origin pair")
        seen_pairs.add(pair)

    _string_list(value.get("protected_identity_globs"), "protected_identity_globs")
    _string_list(value.get("external_activation_classes"), "external_activation_classes")
    fan_in = value.get("generated_owner_fan_in")
    if not isinstance(fan_in, list) or not fan_in:
        raise IdentityError("generated_owner_fan_in: must be non-empty")
    for index, row in enumerate(fan_in):
        if not isinstance(row, dict) or set(row) != {"owner", "inputs", "outputs"}:
            raise IdentityError(f"generated_owner_fan_in[{index}]: ambiguous row")
        _string(row.get("owner"), f"generated_owner_fan_in[{index}].owner")
        _string_list(row.get("inputs"), f"generated_owner_fan_in[{index}].inputs")
        _string_list(row.get("outputs"), f"generated_owner_fan_in[{index}].outputs")

    approval = value.get("approval")
    if not isinstance(approval, dict) or set(approval) != {
        "operator_required", "availability_check_authorized", "external_mutation_authorized"
    }:
        raise IdentityError("approval: has an incomplete or ambiguous field set")
    if approval.get("operator_required") is not True:
        raise IdentityError("approval.operator_required: must remain true")
    if approval.get("availability_check_authorized") is not False:
        raise IdentityError("approval.availability_check_authorized: must remain false")
    if approval.get("external_mutation_authorized") is not False:
        raise IdentityError("approval.external_mutation_authorized: must remain false")
    return copy.deepcopy(value)


def load_identity(path: Path = DEFAULT_IDENTITY_PATH) -> dict[str, Any]:
    if path_has_symlink_component(path):
        raise IdentityError(
            "could not load repository identity: path must not traverse symbolic links"
        )
    try:
        value = json.loads(read_regular_bytes(path).decode("utf-8"))
    except (IdentityError, OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise IdentityError(f"could not load repository identity: {exc}") from exc
    return validate_identity(value)


def projected_identity(value: dict[str, Any], owner: str, slug: str) -> dict[str, Any]:
    projected = validate_identity(value)
    if not NAME_RE.fullmatch(owner) or not NAME_RE.fullmatch(slug):
        raise IdentityError("candidate owner and slug must be conservative GitHub names")
    if slug.casefold().endswith(".git"):
        raise IdentityError("candidate slug must not include a .git suffix")
    origin = f"https://github.com/{owner}/{slug}"
    if origin == projected["current"]["origin"]:
        raise IdentityError("candidate identity must differ from the current identity")
    historical_origins = {
        row["origin"] for row in projected["historical_receipt_contracts"]
    }
    if origin in historical_origins:
        raise IdentityError("candidate identity must not reuse a historical receipt origin")
    projected["current"] = {
        "owner": owner,
        "slug": slug,
        "origin": origin,
        "activation_state": "simulated_pending_operator_approval",
    }
    projected["contracts"]["current_submission_schema"] = projected["contracts"][
        "post_rename_submission_schema"
    ]
    projected["contracts"]["current_schema_path"] = projected["contracts"][
        "post_rename_schema_path"
    ]
    return validate_identity(projected)


def origin_contract_errors(
    record_kind: Any,
    schema_value: Any,
    origin: Any,
    identity: dict[str, Any],
) -> list[str]:
    identity = validate_identity(identity)
    if not isinstance(schema_value, str) or not isinstance(origin, str):
        return []
    current_pair = (
        identity["contracts"]["current_submission_schema"],
        identity["current"]["origin"],
    )
    historical_pairs = {
        (row["schema_value"], row["origin"])
        for row in identity["historical_receipt_contracts"]
    }
    pair = (schema_value, origin)
    if record_kind == "submitted_return" and pair != current_pair:
        return [
            "must equal the canonical standalone repository origin and current schema pair "
            f"{current_pair[0]} @ {current_pair[1]}"
        ]
    if record_kind == "accepted_receipt" and pair not in historical_pairs | {current_pair}:
        return [
            "must equal a canonical standalone repository origin/schema pair "
            "recorded as current or historical"
        ]
    if record_kind == "validation_fixture" and pair not in historical_pairs | {current_pair}:
        return [
            "must equal a canonical standalone repository origin/schema pair "
            "recorded as current or historical"
        ]
    return []
