#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Generate accepted-only attribution views from committed return receipts."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any
from urllib.parse import quote

import validate_research_return as return_validator
import repository_identity as repository_identity_contract
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
RETURNS = ROOT / "docs/research-commons/returns"
JSON_OUTPUT = ROOT / "docs/research-commons/contributions.json"
MARKDOWN_OUTPUT = ROOT / "docs/research-commons/CONTRIBUTIONS.md"
SCHEMA = "accepted-research-contributions/1"
PUBLIC_RESULT_FAMILY_ANCHOR = "current-public-consumer-fan-in"
GIT_CONTEXT_KEYS = frozenset(
    {
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_CEILING_DIRECTORIES",
        "GIT_DISCOVERY_ACROSS_FILESYSTEM",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
    }
)
GIT_PROCESS_CONTROL_KEYS = frozenset(
    {
        "GIT_TRACE",
        "GIT_TRACE2",
        "GIT_TRACE_PACKET",
        "GIT_TRACE_PERFORMANCE",
        "GIT_TRACE_SETUP",
        "GIT_TRACE_CURL",
        "GIT_TRACE2_EVENT",
        "GIT_TRACE2_PERF",
        "GIT_SSH",
        "GIT_SSH_COMMAND",
        "GIT_SSH_VARIANT",
        "GIT_EXTERNAL_DIFF",
        "GIT_DIFF_OPTS",
        "GIT_EDITOR",
        "GIT_SEQUENCE_EDITOR",
        "GIT_MERGE_AUTOEDIT",
    }
)
PYTHON_CONTEXT_KEYS = frozenset(
    {
        "PYTHONPATH",
        "PYTHONHOME",
        "PYTHONUSERBASE",
        "PYTHONSTARTUP",
        "PYTHONBREAKPOINT",
        "PYTHONWARNINGS",
    }
)
PYTHON_STABILITY_KEYS = frozenset({"PYTHONHASHSEED", "PYTHONOPTIMIZE", "PYTHONUTF8"})
LOCALE_KEYS = frozenset({"LC_ALL", "LANG", "LANGUAGE"})
GIT_LOOKUP_TIMEOUT_SECONDS = singleflight.GIT_COMMAND_TIMEOUT_SECONDS


def has_symlink_component(path: Path, root: Path = ROOT) -> bool:
    """Return whether ``path`` escapes ``root`` through a symbolic link."""
    candidate = Path(os.path.abspath(path))

    def platform_alias(component: Path) -> bool:
        """Allow only macOS's system-owned temp-directory compatibility aliases."""
        aliases = {
            Path("/tmp"): Path("/private/tmp"),
            Path("/var"): Path("/private/var"),
        }
        target = aliases.get(component)
        if target is None:
            return False
        try:
            return component.resolve(strict=True) == target
        except OSError:
            return False

    try:
        relative = candidate.relative_to(root)
    except ValueError:
        # Test and caller-supplied paths may intentionally live outside this
        # checkout. Walk every existing component so a nested substituted
        # parent cannot redirect generated output to an external target, while
        # retaining the platform-owned macOS ``/tmp`` and ``/var`` aliases.
        current = Path(candidate.anchor)
        for part in candidate.parts[1:]:
            current /= part
            if current.is_symlink():
                if platform_alias(current):
                    current = current.resolve(strict=True)
                    continue
                return True
        return False

    current = root
    for component in relative.parts:
        current /= component
        if current.is_symlink():
            return True
    return False


def git_environment() -> dict[str, str]:
    """Use the canonical environment-neutral Git command boundary."""
    return singleflight.command_environment()


def canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")


def sha256(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _run_git(arguments: list[str], **kwargs: Any) -> subprocess.CompletedProcess[Any]:
    """Run a repository-bound Git query without allowing an unbounded hang."""
    try:
        return subprocess.run(
            arguments,
            timeout=GIT_LOOKUP_TIMEOUT_SECONDS,
            **kwargs,
        )
    except subprocess.TimeoutExpired as exc:
        raise ValueError(
            "git command timed out after "
            f"{GIT_LOOKUP_TIMEOUT_SECONDS} seconds: {' '.join(arguments)}"
        ) from exc
    except OSError as exc:
        raise ValueError(
            "git command could not be launched: "
            f"{' '.join(arguments)}: {exc}"
        ) from exc


def accepted_at(receipt: dict[str, Any]) -> str:
    value = receipt["review"]["accepted_handoff"]["decided_at"]
    if not isinstance(value, str):
        raise ValueError(f"{receipt.get('return_id')}: accepted_handoff.decided_at is missing")
    return value


def chronological_key(item: tuple[str, dict[str, Any], bytes]) -> tuple[dt.datetime, str]:
    value = accepted_at(item[1])
    parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    return parsed, str(item[1]["return_id"])


def commit_is_ancestor(commit: str) -> bool:
    completed = _run_git(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
        env=git_environment(),
    )
    return completed.returncode == 0


def committed_receipt_payload(path: Path) -> bytes:
    """Read the receipt blob from ``HEAD``, never from an uncommitted source."""
    try:
        relative = path.resolve(strict=True).relative_to(ROOT.resolve(strict=True))
    except (OSError, ValueError) as exc:
        raise ValueError(f"{path.name}: receipt source must be committed in HEAD") from exc
    completed = _run_git(
        ["git", "show", f"HEAD:{relative.as_posix()}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
        env=git_environment(),
    )
    if completed.returncode != 0:
        raise ValueError(f"{path.name}: receipt source must be committed in HEAD")
    return completed.stdout


def committed_receipt_paths(directory: Path) -> list[Path]:
    """Enumerate every direct JSON receipt tracked in ``HEAD``."""
    try:
        relative = directory.resolve(strict=True).relative_to(ROOT.resolve(strict=True))
    except (OSError, ValueError) as exc:
        raise ValueError(f"{directory.name}: receipt directory must be committed in HEAD") from exc
    completed = _run_git(
        ["git", "ls-tree", "-r", "--name-only", "HEAD", "--", relative.as_posix()],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
        text=True,
        env=git_environment(),
    )
    if completed.returncode != 0:
        raise ValueError(f"{directory.name}: could not enumerate committed receipt sources")
    return sorted(
        ROOT / name
        for name in completed.stdout.splitlines()
        if Path(name).parent == relative and Path(name).suffix == ".json"
    )


def load_receipts(
    directory: Path = RETURNS,
    *,
    require_committed: bool = False,
    repository_identity: dict[str, Any] | None = None,
) -> list[tuple[str, dict[str, Any], bytes]]:
    if has_symlink_component(directory):
        raise ValueError(
            f"{directory.name}: receipt directory path must not traverse symbolic links"
        )
    if not directory.is_dir():
        raise ValueError(f"{directory.name}: receipt directory must be a directory")
    sources: list[tuple[str, dict[str, Any], bytes]] = []
    seen_ids: dict[str, str] = {}
    errors: list[str] = []
    worktree_paths = set(directory.glob("*.json"))
    committed_paths = set(committed_receipt_paths(directory)) if require_committed else set()
    candidate_paths = committed_paths if require_committed else worktree_paths
    for path in sorted(candidate_paths):
        if require_committed and path in committed_paths and not path.exists():
            errors.append(f"{path.name}: receipt source committed in HEAD is missing from worktree")
            continue
        if path.is_symlink():
            errors.append(f"{path.name}: receipt source must not be a symbolic link")
            continue
        if not path.is_file():
            errors.append(f"{path.name}: receipt source must be a regular file")
            continue
        payload = path.read_bytes()
        if require_committed:
            try:
                committed_payload = committed_receipt_payload(path)
            except ValueError as exc:
                errors.append(str(exc))
                continue
            if payload != committed_payload:
                errors.append(f"{path.name}: receipt source differs from committed HEAD")
                continue
        try:
            receipt = json.loads(payload)
        except json.JSONDecodeError as exc:
            errors.append(f"{path.name}: invalid JSON: {exc}")
            continue
        validation_errors = return_validator.validate_document(
            receipt,
            require_accepted=receipt.get("record_kind") == "accepted_receipt"
            if isinstance(receipt, dict)
            else False,
            repository_identity=repository_identity,
        )
        errors.extend(f"{path.name}: {error}" for error in validation_errors)
        if not isinstance(receipt, dict):
            continue
        return_id = receipt.get("return_id")
        if isinstance(return_id, str):
            previous = seen_ids.get(return_id)
            if previous is not None:
                errors.append(f"{path.name}: return_id {return_id!r} duplicates {previous}")
            else:
                seen_ids[return_id] = path.name
        if receipt.get("record_kind") == "accepted_receipt":
            accepted_commit = receipt.get("repository", {}).get("accepted_commit")
            if isinstance(accepted_commit, str) and not commit_is_ancestor(accepted_commit):
                errors.append(f"{path.name}: accepted commit is not contained in HEAD")
            sources.append((path.name, receipt, payload))
    if errors:
        raise ValueError("\n".join(sorted(set(errors))))
    return sorted(sources, key=chronological_key)


def public_result_family_route(problem: Any) -> dict[str, str]:
    package_name = f"RETURN_PACKAGE_EXAMPLE_{problem}.md"
    package_path = ROOT / "docs/research-commons" / package_name
    if not package_path.is_file():
        raise ValueError(
            f"no public result-family package is present for Erdős #{problem}"
        )
    return {
        "repository_path": f"docs/research-commons/{package_name}",
        "anchor": PUBLIC_RESULT_FAMILY_ANCHOR,
        "relative_link": f"{package_name}#{PUBLIC_RESULT_FAMILY_ANCHOR}",
    }


def project_receipt(name: str, receipt: dict[str, Any], payload: bytes) -> dict[str, Any]:
    row = {
        "return_id": receipt["return_id"],
        "accepted_at": accepted_at(receipt),
        "receipt_path": f"docs/research-commons/returns/{name}",
        "receipt_sha256": sha256(payload),
        "identity": receipt["identity"],
        "repository": receipt["repository"],
        "frontier": receipt["frontier"],
        "result": receipt["result"],
        "evidence": receipt["evidence"],
        "review": receipt["review"],
        "attribution": receipt["attribution"],
    }
    if "correction_lineage" in receipt:
        row["correction_lineage"] = receipt["correction_lineage"]
    return row


def filter_rows(rows: list[dict[str, Any]], field: str) -> dict[str, list[str]]:
    grouped: dict[str, list[str]] = {}
    for row in rows:
        if field == "problem":
            key = str(row["frontier"]["problem"])
        elif field == "result_class":
            key = str(row["result"]["class"])
        elif field == "requested_disposition":
            key = str(row["result"]["requested_disposition"])
        else:
            raise ValueError(f"unsupported contribution filter {field!r}")
        grouped.setdefault(key, []).append(row["return_id"])
    return {key: grouped[key] for key in sorted(grouped)}


def build_projection(sources: list[tuple[str, dict[str, Any], bytes]]) -> dict[str, Any]:
    for name, receipt, _payload in sources:
        if not isinstance(receipt, dict) or receipt.get("record_kind") != "accepted_receipt":
            raise ValueError(
                f"{name}: contribution projection accepts accepted_receipt records only"
            )
    rows = [project_receipt(name, receipt, payload) for name, receipt, payload in sources]
    for row in rows:
        row["public_frontier"] = public_result_family_route(row["frontier"]["problem"])
    return {
        "schema": SCHEMA,
        "artifact_role": "generated_accepted_artifact_attribution_view",
        "generated_by": "scripts/build_research_contributions.py",
        "source_directory": "docs/research-commons/returns",
        "source_policy": (
            "strict accepted_receipt records only; detached route-memory sidecars are "
            "separate intake authority and are not included in this attribution view"
        ),
        "authority_boundary": (
            "Receipt-derived attribution evidence only; Lean, docs/claims.json, methodology review, "
            "GitHub delivery history, core promotion, and tagged releases retain their own authority."
        ),
        "chronological": rows,
        "filters": {
            "by_problem": filter_rows(rows, "problem"),
            "by_result_class": filter_rows(rows, "result_class"),
            "by_requested_disposition": filter_rows(rows, "requested_disposition"),
        },
    }


def markdown_text(value: Any) -> str:
    text = " ".join(str(value).split())
    for character in ("\\", "`", "*", "_", "[", "]", "<", ">"):
        text = text.replace(character, "\\" + character)
    return text


def code_text(value: Any) -> str:
    return " ".join(str(value).split()).replace("`", "'")


def disclosure_text(value: dict[str, Any] | None) -> str:
    if not value:
        return "undisclosed"
    state = str(value.get("state", "undisclosed"))
    if state != "disclosed":
        return state
    parts = [str(value.get("name", "disclosed"))]
    if value.get("version"):
        parts.append(str(value["version"]))
    resources = value.get("resources")
    if isinstance(resources, list) and resources:
        parts.append("resources: " + ", ".join(str(item) for item in resources))
    return " — ".join(parts)


def artifact_credit_text(items: list[dict[str, Any]]) -> str:
    return "; ".join(
        f"{item['name']}: {', '.join(item['artifact_paths'])}"
        for item in items
    )


def correction_lineage_text(value: dict[str, Any]) -> str:
    prior = value["prior_return_reference"]
    affected = ", ".join(value["affected_paths"])
    return (
        f"prior={prior}; affected={affected}; starting_commit={value['starting_commit']}; "
        f"change={value['changed_evidence_or_wording']}; reason={value['reason']}; "
        f"disposition={value['disposition']}"
    )


def receipt_link(row: dict[str, Any]) -> str:
    name = Path(row["receipt_path"]).name
    encoded_name = quote(name, safe="-._~")
    return f"[receipt:{markdown_text(row['return_id'])}](returns/{encoded_name})"


def filtered_section(title: str, groups: dict[str, list[str]], links: dict[str, str]) -> list[str]:
    lines = [f"## {title}", ""]
    for key, return_ids in groups.items():
        lines.extend([f"### {markdown_text(key)}", ""])
        lines.extend(f"- {links[return_id]}" for return_id in return_ids)
        lines.append("")
    return lines


def human_projection(projection: dict[str, Any]) -> bytes:
    rows = projection["chronological"]
    links = {row["return_id"]: receipt_link(row) for row in rows}
    lines = [
        "<!-- SPDX-FileCopyrightText: 2026 Will Cook -->",
        "<!-- SPDX-License-Identifier: Apache-2.0 -->",
        "",
        "# Accepted research contributions",
        "",
        "This file is generated from strict `accepted_receipt` JSON artifacts. It is an",
        "artifact-attribution view, not mathematical proof, claim authority, novelty review,",
        "release inclusion, a contributor comparison, or evidence about model quality.",
        "",
        "Negative and inconclusive artifacts appear on exactly the same chronological rail",
        "when repository acceptance records that they saved reproducible work.",
        "",
        "For each accepted record, follow its `public_frontier` route to inspect every",
        "material result family and the exact surviving boundary for that problem. This",
        "canonical navigation does not change the credited artifact or its claim ceiling.",
        "",
        "For receipt-bound identity, impact, evidence, review, correction, promotion, and",
        "tagged-release facets, see the [accepted contribution recognition view](CONTRIBUTION_RECOGNITION.md)",
        "and its [machine-readable projection](contribution-recognition.json). Those views",
        "use the same accepted receipts and do not turn activity into scientific credit.",
        "Detached route-memory sidecars may bind intake, but they remain separate route authority",
        "and are not copied into or counted by this accepted-receipt attribution view.",
        "",
        "## Chronological accepted artifacts",
        "",
    ]
    for row in rows:
        identity = row["identity"]
        result = row["result"]
        repository = row["repository"]
        review = row["review"]
        operator = identity["operator"]
        collaborators = identity.get("material_collaborators", [])
        collaborator_text = (
            "; ".join(f"{item['name']} ({item['role']})" for item in collaborators)
            if collaborators
            else "none recorded"
        )
        review_text = "; ".join(f"{name}={decision['state']}" for name, decision in review.items())
        evidence_text = "; ".join(
            f"{item['exit_state']}/{item['replay_state']}" for item in row["evidence"]
        )
        lines.extend(
            [
                f"### {markdown_text(row['accepted_at'])} — Erdős #{row['frontier']['problem']} — {markdown_text(result['class'])}",
                "",
                f"- Receipt: {links[row['return_id']]}",
                f"- Contributor: {markdown_text(identity['contributor']['name'])}",
                f"- Operator: {markdown_text(operator['relationship'])} — {markdown_text(operator.get('name') or 'undisclosed')}",
                f"- Model/system disclosure: {markdown_text(disclosure_text(identity.get('model_system')))}",
                f"- Provider disclosure: {markdown_text(disclosure_text(identity.get('provider')))}",
                f"- Material collaborators: {markdown_text(collaborator_text)}",
                f"- Requested display: {markdown_text(row['attribution']['requested_display'])}",
                f"- Artifact credit: {markdown_text(artifact_credit_text(row['attribution']['artifact_credit']))}",
                f"- Frontier: `{code_text(row['frontier']['handle'])}`",
                f"- Public result-family fan-in: [Erdős #{row['frontier']['problem']} current fan-in]({row['public_frontier']['relative_link']})",
                f"- Starting commit: `{repository['starting_commit']}`",
                f"- Proposed commit: `{repository['proposed_commit']}`",
                f"- Accepted commit: `{repository['accepted_commit']}`",
                f"- Public repository: `{code_text(repository['origin'])}`",
                f"- Changed public paths: {markdown_text(', '.join(repository['changed_paths']))}",
                f"- Result: {markdown_text(result['summary'])}",
                f"- Claim ceiling: `{code_text(result['claim_ceiling'])}`",
                f"- Surviving boundary: {markdown_text(result['surviving_boundary'])}",
                f"- Evidence/replay states: {markdown_text(evidence_text)}",
                f"- Review states: {markdown_text(review_text)}",
                f"- Limitations: {markdown_text('; '.join(result['limitations']))}",
                f"- Requested disposition: `{code_text(result['requested_disposition'])}`",
                *(
                    [
                        "- Correction lineage: "
                        + markdown_text(correction_lineage_text(row["correction_lineage"]))
                    ]
                    if "correction_lineage" in row
                    else []
                ),
                "",
            ]
        )
    filters = projection["filters"]
    lines.extend(filtered_section("Filter by Erdős problem", filters["by_problem"], links))
    lines.extend(filtered_section("Filter by result class", filters["by_result_class"], links))
    lines.extend(
        filtered_section(
            "Filter by requested disposition",
            filters["by_requested_disposition"],
            links,
        )
    )
    lines.extend(
        [
            "The source receipts remain the attribution evidence. Git history and GitHub issues",
            "or pull requests remain delivery history; neither this view nor a receipt changes",
            "`docs/claims.json` or any release state.",
            "",
        ]
    )
    return "\n".join(lines).encode("utf-8")


def output_is_current(path: Path, payload: bytes) -> bool:
    """Check generated bytes without following a substituted output symlink."""
    return not has_symlink_component(path) and path.is_file() and path.read_bytes() == payload


def write_projection_outputs(
    json_payload: bytes,
    markdown_payload: bytes,
    *,
    json_output: Path = JSON_OUTPUT,
    markdown_output: Path = MARKDOWN_OUTPUT,
) -> None:
    """Replace both generated views without writing through output symlinks."""
    outputs = ((json_output, json_payload), (markdown_output, markdown_payload))
    for path, _payload in outputs:
        if path.is_symlink():
            raise ValueError(f"{path.name}: generated output must not be a symbolic link")
        if has_symlink_component(path):
            raise ValueError(
                f"{path.name}: generated output parent path must not traverse symbolic links"
            )
        if path.exists() and not path.is_file():
            raise ValueError(f"{path.name}: generated output must be a regular file")
        if not path.parent.is_dir():
            raise ValueError(f"{path.name}: generated output parent must be a directory")

    staged: list[tuple[Path, Path]] = []
    backups: dict[Path, Path | None] = {}
    replaced: list[Path] = []
    try:
        for path, payload in outputs:
            descriptor, temporary_name = tempfile.mkstemp(
                prefix=f".{path.name}.",
                suffix=".tmp",
                dir=path.parent,
            )
            temporary = Path(temporary_name)
            try:
                with os.fdopen(descriptor, "wb") as output:
                    output.write(payload)
                    output.flush()
                    os.fsync(output.fileno())
                temporary.chmod(0o644)
            except BaseException:
                temporary.unlink(missing_ok=True)
                raise
            staged.append((temporary, path))
        for path, _payload in outputs:
            if not path.exists():
                backups[path] = None
                continue
            descriptor, backup_name = tempfile.mkstemp(
                prefix=f".{path.name}.",
                suffix=".backup",
                dir=path.parent,
            )
            os.close(descriptor)
            backup = Path(backup_name)
            backup.unlink()
            os.link(path, backup, follow_symlinks=False)
            backups[path] = backup
        for temporary, path in staged:
            os.replace(temporary, path)
            replaced.append(path)
    except BaseException as exc:
        rollback_errors: list[str] = []
        for path in reversed(replaced):
            backup = backups.get(path)
            try:
                if backup is None:
                    path.unlink(missing_ok=True)
                else:
                    os.replace(backup, path)
            except OSError as rollback_exc:
                rollback_errors.append(f"{path.name}: {rollback_exc}")
        if rollback_errors:
            raise OSError(
                "projection replacement failed and rollback was incomplete: "
                + "; ".join(rollback_errors)
            ) from exc
        raise
    finally:
        for temporary, _path in staged:
            temporary.unlink(missing_ok=True)
        for backup in backups.values():
            if backup is not None:
                backup.unlink(missing_ok=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail when either generated view is stale")
    parser.add_argument(
        "--repository-identity",
        type=Path,
        default=repository_identity_contract.DEFAULT_IDENTITY_PATH,
        help="current public repository identity authority",
    )
    args = parser.parse_args(argv)
    try:
        identity_contract = repository_identity_contract.load_identity(
            args.repository_identity
        )
        projection = build_projection(
            load_receipts(
                require_committed=True,
                repository_identity=identity_contract,
            )
        )
    except (OSError, ValueError, repository_identity_contract.IdentityError) as exc:
        print(f"build_research_contributions: {exc}")
        return 1
    json_payload = canonical(projection)
    markdown_payload = human_projection(projection)
    if args.check:
        if (
            not output_is_current(JSON_OUTPUT, json_payload)
            or not output_is_current(MARKDOWN_OUTPUT, markdown_payload)
        ):
            print("research contribution views are stale; run python3 scripts/build_research_contributions.py")
            return 1
        print("research contribution views current: accepted receipts only")
        return 0
    try:
        write_projection_outputs(json_payload, markdown_payload)
    except (OSError, ValueError) as exc:
        print(f"build_research_contributions: {exc}")
        return 1
    print("wrote accepted-only research contribution JSON and Markdown views")
    return 0


if __name__ == "__main__":
    sys.exit(main())
