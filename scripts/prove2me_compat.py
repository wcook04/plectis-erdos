#!/usr/bin/env python3
"""Offline, source-bound Prove2Me handoff for one public #249 theorem.

This prepares a candidate and reconciles recorded API responses. It never
contacts Prove2Me, compiles Lean, or changes the local mathematical claim.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "plectis_prove2me_compat_v1"
CLAIM_ID = "all_base_totient_kernel_index_reduction"
THEOREM = "ErdosProblems.Erdos249.PaperCompleteR8.displayed_all_base_kernel"
LEAN_SOURCE = "lean/ErdosProblems/Erdos249/PaperCompleteR8/FullKernelAssemblies.lean"
RANK_SOURCE = "lean/Erdos249257/AllBaseTotientKernel.lean"
PAPER_SOURCE = "paper/249/erdos-249-binary-totient-series.tex"
SOURCE_PATHS = (LEAN_SOURCE, RANK_SOURCE, PAPER_SOURCE)
PUBLISH_STATES = {"PENDING", "COMPILING", "PUBLISHED", "FAILED", "ERROR"}
VERIFY_STATES = {"PENDING", "ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}
TERMINAL = {"PUBLISHED", "FAILED", "ERROR", "ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY"}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode()


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ValueError(f"expected a JSON object: {path}")
    return value


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    if not path.exists() or path.read_text() != data:
        path.write_text(data)


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-C", str(ROOT), *args], text=True).strip()


def source_line(path: str, needle: str) -> int:
    matches = [i for i, line in enumerate((ROOT / path).read_text().splitlines(), 1) if needle in line]
    if len(matches) != 1:
        raise ValueError(f"expected one {needle!r} declaration in {path}")
    return matches[0]


def prepare() -> dict:
    claims = read_json(ROOT / "docs/claims.json")["claims"]
    matches = [row for row in claims if row.get("id") == CLAIM_ID]
    if len(matches) != 1:
        raise ValueError(f"expected one claim {CLAIM_ID}")
    claim = matches[0]
    if claim.get("paper_label") != "thm:kkernelrank" or "remaining_open.erdos_249_irrationality" not in claim.get("remaining_open_proposition_ids", []):
        raise ValueError("the #249 claim/paper/open-boundary mapping changed")
    line = source_line(LEAN_SOURCE, "theorem displayed_all_base_kernel ")
    rank_line = source_line(RANK_SOURCE, "theorem finrank_allBaseThroughLevelFamily_eq ")
    paper_line = source_line(PAPER_SOURCE, "\\label{thm:kkernelrank}")
    sources = {path: digest((ROOT / path).read_bytes()) for path in SOURCE_PATHS}
    head = git("rev-parse", "HEAD")
    public_commit = git("rev-parse", "origin/main")
    public_source_matches = all(
        digest(subprocess.check_output(["git", "-C", str(ROOT), "show", f"{public_commit}:{path}"])) == sources[path]
        for path in (LEAN_SOURCE, RANK_SOURCE, PAPER_SOURCE)
    )
    manifest = read_json(ROOT / "lake-manifest.json")
    mathlib = next(pkg for pkg in manifest["packages"] if pkg["name"] == "mathlib")
    packet = {
        "schema": SCHEMA,
        "unit": "erdos249_all_base_totient_kernel_paper_theorem",
        "local_commit": head,
        "public_source_commit": public_commit if public_source_matches else None,
        "sources_sha256": sources,
        "claim_record_sha256": digest(canonical(claim)),
        "claim_id": CLAIM_ID,
        "claim_status": claim["status"],
        "paper_label": claim["paper_label"],
        "remaining_open_proposition_ids": claim["remaining_open_proposition_ids"],
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib_rev": mathlib["rev"],
        "native_draft": {
            "object": "theorem_then_proof",
            "theorem_name": THEOREM,
            "theorem_title": "All-base finite-level totient-kernel basis and rank",
            "natural_language_statement": (
                "Let $k\\ge 2$ be an integer base, $e\\ge 1$ a depth, and "
                "$F_{j,r}^{(k)}(n)=\\varphi(k^j n+r)$ the Euler-totient sections. "
                "Let $V_{k,e}$ be their rational span for $0\\le j\\le e$ and "
                "$0\\le r<k^j$. Then\n\n"
                "$$\\dim_{\\mathbb Q} V_{k,e}=k^e+1.$$\n\n"
                "The canonical family consisting of the two zero-residue channels "
                "and the sections with $1\\le r<k^j$ and $k\\nmid r$ is a basis; "
                "every omitted section has the explicit scalar reduction in the "
                "cited paper. This finite-level kernel theorem does not establish "
                "irrationality of the binary totient series."
            ),
            "source": (f"https://github.com/wcook04/plectis-erdos-integration/blob/{public_commit}/"
                       f"{LEAN_SOURCE}#L{line}" if public_source_matches else None),
            "paper_source": (f"https://github.com/wcook04/plectis-erdos-integration/blob/{public_commit}/"
                             f"{PAPER_SOURCE}#L{paper_line}" if public_source_matches else None),
            "tags": ["number-theory", "totient", "erdos-249"],
        },
        "local_attachment": {
            "source_declaration": f"{LEAN_SOURCE}:{line}",
            "unconditional_rank_declaration": f"{RANK_SOURCE}:{rank_line}",
            "paper_statement": f"{PAPER_SOURCE}:{paper_line}",
            "prior_credit": "Martin, Theorem 1, is a broader affine-independence antecedent; the Lean proof is independent.",
            "open_boundary": "Irrationality of ∑ φ(n)/2ⁿ remains open.",
            "excluded": ["#249 irrationality as a proved theorem", "bulk implementation lemmas as standalone missions", "novelty or priority verdict"],
        },
        "mapping": {
            "native": ["theorem statement", "natural-language statement", "source citation", "proof submission verdict", "external job and theorem IDs"],
            "local_attachment": ["source hashes", "paper passage", "conditional-interface distinction", "open boundary", "Martin credit", "type and replay receipts"],
            "omitted": ["private parent state", "service credentials", "mission for already-proved rank", "irrationality or acceptance claims"],
        },
    }
    packet["packet_id"] = digest(canonical({"unit": packet["unit"], "sources": sources,
                                            "claim_record": packet["claim_record_sha256"]}))
    return packet


def validate(packet: dict, environment: dict | None = None, staged: dict | None = None) -> dict:
    blockers: list[str] = []
    if packet.get("schema") != SCHEMA:
        blockers.append("unsupported_packet_schema")
        return {"status": "blocked", "blockers": blockers}
    try:
        current = prepare()
        if packet.get("packet_id") != current["packet_id"] or packet.get("sources_sha256") != current["sources_sha256"]:
            blockers.append("source_or_claim_mismatch")
        for field in ("claim_record_sha256", "claim_id", "claim_status", "paper_label", "remaining_open_proposition_ids",
                      "lean_toolchain", "mathlib_rev", "native_draft", "local_attachment", "mapping"):
            if packet.get(field) != current.get(field):
                blockers.append("packet_metadata_mismatch")
                break
        if not current["public_source_commit"]:
            blockers.append("source_not_at_public_main")
    except (OSError, KeyError, ValueError, subprocess.CalledProcessError):
        blockers.append("source_unavailable")
    if environment is None:
        blockers.append("environment_unverified")
    elif environment.get("source_url") != "https://prove2.me/api/v1/environments" or not environment.get("captured_with_authenticated_request"):
        blockers.append("environment_unverified")
    elif not any(
        item.get("mathlib_rev") == packet.get("mathlib_rev") and item.get("toolchain") == packet.get("lean_toolchain")
        for item in environment.get("environments", [])
    ):
        blockers.append("environment_mismatch")
    if staged is None:
        blockers.append("platformized_source_missing")
    else:
        if staged.get("source_sha256") != packet.get("sources_sha256", {}).get(LEAN_SOURCE):
            blockers.append("staged_source_mismatch")
        if staged.get("original_type") != staged.get("staged_type") or not staged.get("original_type"):
            blockers.append("type_mismatch_or_missing")
        if not staged.get("declaration_graph_receipt") or not staged.get("sketch_info_receipt"):
            blockers.append("official_extractor_receipts_missing")
        if staged.get("compiled_exact_upload_text") is not True or staged.get("compiled_solution") is not True:
            blockers.append("staged_compile_receipts_missing")
        formal = staged.get("formal_statement", "")
        solution = staged.get("solution", "")
        if not formal.startswith(f"theorem {THEOREM} ") or not formal.rstrip().endswith(":= by sorry"):
            blockers.append("formal_statement_missing_or_wrong_name")
        if "theorem solution " not in solution or "sorry" in solution:
            blockers.append("solution_missing_or_contains_sorry")
    return {"status": "draft_for_review" if not blockers else "blocked", "blockers": blockers,
            "boundary": "Offline checks and supplied receipts do not establish Lean compilation, service publication, novelty, or peer review."}


def normalize_event(kind: str, response: dict) -> dict:
    if kind == "publish_job" and "jobs" in response:
        jobs = response["jobs"]
        if len(jobs) != 1:
            raise ValueError("one publish job per event is required")
        response = jobs[0]
    status = response.get("status", "PENDING" if kind == "publish_job" and "job_id" in response else None)
    allowed = PUBLISH_STATES if kind == "publish_job" else VERIFY_STATES
    if status not in allowed:
        raise ValueError(f"unknown {kind} status {status!r}")
    identifier = response.get("id") or (response.get("job_id") if kind == "publish_job" else None)
    if not isinstance(identifier, str) or not identifier:
        raise ValueError("response has no external identifier")
    theorem_id = response.get("theorem_id")
    if kind == "publish_job":
        if response.get("kind", "problem") != "problem":
            raise ValueError("only theorem publication jobs are in this adapter")
        if status == "PUBLISHED" and not theorem_id:
            raise ValueError("published job lacks theorem_id")
        if status != "PUBLISHED" and theorem_id:
            raise ValueError("unpublished job cannot supply theorem_id")
    elif not theorem_id:
        raise ValueError("verification response lacks theorem_id")
    return {"schema": SCHEMA, "kind": kind, "external_id": identifier, "status": status,
            "theorem_id": theorem_id, "error_message": response.get("error_message") or "",
            "updated_at": response.get("updated_at")}


def reconcile(packet: dict, state: dict | None, event: dict, replaces_theorem: str | None = None) -> dict:
    source_blockers = validate(packet)["blockers"]
    if any(blocker in source_blockers for blocker in ("unsupported_packet_schema", "source_or_claim_mismatch", "packet_metadata_mismatch", "source_unavailable")):
        raise ValueError("packet no longer matches local source")
    if event.get("schema") != SCHEMA or event.get("kind") not in {"publish_job", "verification"}:
        raise ValueError("invalid event")
    if event.get("status") not in (PUBLISH_STATES if event["kind"] == "publish_job" else VERIFY_STATES):
        raise ValueError("invalid event status")
    if not isinstance(event.get("external_id"), str) or not event["external_id"]:
        raise ValueError("invalid event external id")
    if event["kind"] == "publish_job" and (event["status"] == "PUBLISHED") != bool(event.get("theorem_id")):
        raise ValueError("publication event has inconsistent theorem id")
    if event["kind"] == "verification" and not event.get("theorem_id"):
        raise ValueError("verification event lacks theorem id")
    state = state or {"schema": SCHEMA, "packet_id": packet["packet_id"], "publish_jobs": {},
                      "verifications": {}, "replacements": {}}
    if state.get("packet_id") != packet["packet_id"]:
        raise ValueError("state belongs to a different packet")
    key = "publish_jobs" if event["kind"] == "publish_job" else "verifications"
    ident = event["external_id"]
    previous = state[key].get(ident)
    if previous:
        if previous["status"] in TERMINAL:
            if event["status"] != previous["status"] or event.get("theorem_id") != previous.get("theorem_id"):
                if event["status"] not in ("PENDING", "COMPILING"):
                    raise ValueError("conflicting terminal external status")
                return state
            if not replaces_theorem:
                return state
        if previous["status"] == "COMPILING" and event["status"] == "PENDING":
            return state
        if previous.get("theorem_id") and previous["theorem_id"] != event.get("theorem_id"):
            raise ValueError("external theorem id changed")
    if event["kind"] == "verification":
        published = {item.get("theorem_id") for item in state["publish_jobs"].values() if item["status"] == "PUBLISHED"}
        if event["theorem_id"] not in published:
            raise ValueError("verification references an unrecorded published theorem")
    if replaces_theorem:
        if event["kind"] != "publish_job" or event["status"] != "PUBLISHED":
            raise ValueError("replacement requires a published theorem event")
        known = {item.get("theorem_id") for item in state["publish_jobs"].values() if item["status"] == "PUBLISHED"}
        if replaces_theorem not in known or replaces_theorem == event["theorem_id"]:
            raise ValueError("replacement predecessor must be a different known theorem")
        state["replacements"][replaces_theorem] = {
            "new_theorem_id": event["theorem_id"],
            "source_status": "external_lineage_only_unverified",
        }
    state[key][ident] = {field: event.get(field) for field in ("status", "theorem_id", "error_message", "updated_at")}
    return state


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("--out", type=Path, required=True)
    for name in ("validate", "export"):
        cmd = sub.add_parser(name)
        cmd.add_argument("--packet", type=Path, required=True)
        cmd.add_argument("--environment", type=Path)
        cmd.add_argument("--staged", type=Path)
        cmd.add_argument("--out", type=Path, required=True)
    stat = sub.add_parser("status")
    stat.add_argument("--kind", choices=("publish_job", "verification"), required=True)
    stat.add_argument("--response", type=Path, required=True)
    stat.add_argument("--out", type=Path, required=True)
    rec = sub.add_parser("reconcile")
    rec.add_argument("--packet", type=Path, required=True)
    rec.add_argument("--event", type=Path, required=True)
    rec.add_argument("--state", type=Path, required=True)
    rec.add_argument("--replaces-theorem")
    args = parser.parse_args()
    try:
        if args.command == "prepare":
            value = prepare()
            write_json(args.out, value)
        elif args.command in ("validate", "export"):
            packet = read_json(args.packet)
            environment = read_json(args.environment) if args.environment else None
            staged = read_json(args.staged) if args.staged else None
            report = validate(packet, environment, staged)
            if args.command == "export" and not report["blockers"]:
                value = {"schema": SCHEMA, "status": "draft_for_review", "endpoint": "POST /api/v1/submit-problem",
                         "proof_endpoint_after_publication": "POST /api/v1/verify", "env": packet["mathlib_rev"],
                         "theorem_name": packet["native_draft"]["theorem_name"],
                         "theorem_title": packet["native_draft"]["theorem_title"],
                         "formal_statement": staged["formal_statement"], "preamble": staged["preamble"],
                         "natural_language_statement": packet["native_draft"]["natural_language_statement"],
                         "source": packet["native_draft"]["source"], "tags": packet["native_draft"]["tags"],
                         "solution": staged["solution"], "packet_id": packet["packet_id"],
                         "boundary": report["boundary"]}
            else:
                value = report
            write_json(args.out, value)
            if report["blockers"]:
                print(", ".join(report["blockers"]), file=sys.stderr)
                return 2
        elif args.command == "status":
            write_json(args.out, normalize_event(args.kind, read_json(args.response)))
        else:
            packet = read_json(args.packet)
            state = read_json(args.state) if args.state.exists() else None
            value = reconcile(packet, state, read_json(args.event), args.replaces_theorem)
            write_json(args.state, value)
        return 0
    except (OSError, KeyError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"prove2me_compat: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
