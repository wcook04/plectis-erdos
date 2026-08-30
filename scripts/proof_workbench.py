#!/usr/bin/env python3
"""Session notary for agent-native proof work.

The workbench deliberately does not search, rank, or decide.  An
intelligent agent (human or model) is the search policy; the workbench
gives that agent three things it cannot give itself:

1. an append-only typed ledger of its own cognitive moves, so a session
   of reasoning becomes a durable, replayable artifact;
2. a kernel probe runner whose verdicts the agent cannot author — the
   ``claim`` command structurally refuses any claim that does not cite a
   kernel-accepted probe receipt;
3. an environment fingerprint and byte-exact probe storage, so every
   session can be re-executed from the ledger alone.

Authority boundary: ledger notes are advisory cognition.  Only probe
receipts computed here from the Lean exit status carry kernel authority,
and a ``claim`` record is exactly as strong as the receipt it cites.
The wider contract lives in ``docs/AGENT_WORKBENCH.md``.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

MOVE_SCHEMA = "workbench-move/1"
SESSION_SCHEMA = "workbench-session/1"
NOTE_KINDS = (
    "observation",
    "conjecture",
    "plan",
    "interpretation",
    "abandonment",
)
CLOSE_OUTCOMES = ("established", "open", "abandoned")
MOVE_KINDS = ("session_opened", "note", "probe", "claim", "session_closed")
PROBE_TIMEOUT_SECONDS = 600
SESSION_SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{2,80}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _is_allowed_platform_alias(path: Path) -> bool:
    """Allow only macOS's system-owned ``/var`` compatibility alias."""
    if path != Path("/var"):
        return False
    try:
        return path.resolve(strict=True) == Path("/private/var")
    except OSError:
        return False


def path_has_symlink_component(path: Path) -> bool:
    """Reject probe sources that could redirect durable evidence elsewhere."""
    current = Path(os.path.abspath(path))
    while True:
        if current.is_symlink():
            if _is_allowed_platform_alias(current):
                current = current.resolve(strict=True)
            else:
                return True
        if current.parent == current:
            return False
        current = current.parent


def validate_session_slug(slug: str) -> None:
    """Keep every workbench session directory beneath its selected root."""
    if not SESSION_SLUG_RE.fullmatch(slug):
        raise SystemExit("session must match [a-z0-9][a-z0-9_-]{2,80}")


def _utc_now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).isoformat(
        timespec="seconds"
    )


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def environment_fingerprint(root: Path) -> dict[str, Any]:
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    ).stdout.strip()
    dirty = subprocess.run(
        ["git", "status", "--porcelain"],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    ).stdout.strip()
    toolchain_path = root / "lean-toolchain"
    toolchain = (
        toolchain_path.read_text(encoding="utf-8").strip()
        if toolchain_path.is_file()
        else "lean_toolchain_file_absent"
    )
    return {
        "git_head": head or "git_head_unavailable",
        "dirty_path_count": len(
            [line for line in dirty.splitlines() if line.strip()]
        ),
        "lean_toolchain": toolchain,
    }


def run_lean_probe(root: Path, source: str) -> dict[str, Any]:
    """Run one stdin Lean probe and compute the kernel verdict.

    This is the only function in the workbench allowed to produce a
    ``kernel_accepted`` verdict.
    """
    started = _dt.datetime.now(_dt.timezone.utc)
    try:
        completed = subprocess.run(
            ["lake", "env", "lean", "--stdin", "--json"],
            cwd=root,
            input=source,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=PROBE_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        return {
            "verdict": "probe_error",
            "detail": "lean_probe_timeout",
            "exit_code": None,
            "error_count": None,
            "sorry_count": None,
            "duration_seconds": PROBE_TIMEOUT_SECONDS,
            "output_tail": "",
        }
    except (OSError, UnicodeError) as exc:
        detail = (
            "lean_probe_unavailable"
            if isinstance(exc, OSError)
            else "lean_probe_output_unreadable"
        )
        return {
            "verdict": "probe_error",
            "detail": detail,
            "exit_code": None,
            "error_count": None,
            "sorry_count": None,
            "duration_seconds": round(
                (_dt.datetime.now(_dt.timezone.utc) - started).total_seconds(),
                3,
            ),
            "output_tail": str(exc),
        }
    duration = (
        _dt.datetime.now(_dt.timezone.utc) - started
    ).total_seconds()
    errors = 0
    sorries = 0
    for line in completed.stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if message.get("severity") == "error":
            errors += 1
        if message.get("kind") == "hasSorry":
            sorries += 1
    if completed.returncode != 0 or errors:
        verdict = "kernel_rejected"
    elif sorries:
        verdict = "kernel_accepted_with_sorry"
    else:
        verdict = "kernel_accepted"
    return {
        "verdict": verdict,
        "detail": None,
        "exit_code": completed.returncode,
        "error_count": errors,
        "sorry_count": sorries,
        "duration_seconds": round(duration, 3),
        "output_tail": "\n".join(
            completed.stdout.splitlines()[-12:]
        ),
    }


class Session:
    def __init__(self, sessions_root: Path, slug: str) -> None:
        validate_session_slug(slug)
        if path_has_symlink_component(sessions_root):
            raise SystemExit(
                "sessions root must not traverse symbolic links: "
                f"{sessions_root}"
            )
        self.slug = slug
        self.directory = sessions_root / slug
        self.ledger_path = self.directory / "ledger.jsonl"
        self.probes_dir = self.directory / "probes"

    def exists(self) -> bool:
        return self.ledger_path.is_file()

    def moves(self) -> list[dict[str, Any]]:
        if not self.exists():
            return []
        rows = []
        try:
            lines = self.ledger_path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeError) as exc:
            raise SystemExit(
                f"cannot read workbench ledger {self.ledger_path}: {exc}"
            ) from exc
        seen_move_ids: set[str] = set()
        for line_number, line in enumerate(lines, 1):
            if line.strip():
                try:
                    row = json.loads(line)
                except (UnicodeError, json.JSONDecodeError) as exc:
                    raise SystemExit(
                        f"invalid workbench ledger JSON on line {line_number}: {exc}"
                    ) from exc
                if not isinstance(row, dict):
                    raise SystemExit(
                        f"invalid workbench ledger row on line {line_number}: expected an object"
                    )
                if not isinstance(row.get("move_id"), str) or not isinstance(
                    row.get("kind"), str
                ):
                    raise SystemExit(
                        f"invalid workbench ledger row on line {line_number}: move_id and kind are required"
                    )
                if row["move_id"] in seen_move_ids:
                    raise SystemExit(
                        f"invalid workbench ledger row on line {line_number}: "
                        f"duplicate move id {row['move_id']!r}"
                    )
                seen_move_ids.add(row["move_id"])
                if row["kind"] not in MOVE_KINDS:
                    raise SystemExit(
                        f"invalid workbench ledger row on line {line_number}: "
                        f"unsupported move kind {row['kind']!r}"
                    )
                expected_schema = (
                    SESSION_SCHEMA
                    if row["kind"] == "session_opened"
                    else MOVE_SCHEMA
                )
                if row.get("schema") != expected_schema:
                    raise SystemExit(
                        f"invalid workbench ledger row on line {line_number}: "
                        f"{row['kind']!r} requires schema {expected_schema!r}"
                    )
                rows.append(row)
        return rows

    def next_move_id(self) -> str:
        return f"m{len(self.moves()) + 1:03d}"

    def append(self, record: dict[str, Any]) -> dict[str, Any]:
        try:
            with self.ledger_path.open("a", encoding="utf-8") as handle:
                handle.write(
                    json.dumps(record, sort_keys=True, ensure_ascii=False)
                    + "\n"
                )
        except (OSError, UnicodeError) as exc:
            raise SystemExit(
                f"cannot append workbench ledger {self.ledger_path}: {exc}"
            ) from exc
        return record


def _base_record(session: Session, kind: str) -> dict[str, Any]:
    return {
        "schema": MOVE_SCHEMA,
        "move_id": session.next_move_id(),
        "at": _utc_now(),
        "kind": kind,
    }


def _probe_verdict(row: dict[str, Any], action: str) -> str:
    """Read a probe verdict only when the durable receipt has a safe shape."""
    receipt = row.get("kernel_receipt")
    verdict = receipt.get("verdict") if isinstance(receipt, dict) else None
    if not isinstance(verdict, str):
        raise SystemExit(
            f"{action} refused: probe move {row.get('move_id')} has an invalid kernel receipt"
        )
    return verdict


def _required_string(
    row: dict[str, Any], field: str, action: str, label: str | None = None
) -> str:
    """Read a required ledger string without exposing an internal exception."""
    value = row.get(field)
    if not isinstance(value, str) or not value:
        raise SystemExit(
            f"{action} refused: {row.get('kind')} move {row.get('move_id')}"
            f" has an invalid {label or field}"
        )
    return value


def _probe_input_hash(row: dict[str, Any], action: str) -> str:
    """Require a claim to retain the hash of its cited stored artifact."""
    input_sha256 = _required_string(row, "input_sha256", action, "input hash")
    if not SHA256_RE.fullmatch(input_sha256):
        raise SystemExit(
            f"{action} refused: probe move {row.get('move_id')} has an invalid input hash"
        )
    return input_sha256


def _stored_probe_source(session: Session, row: dict[str, Any], action: str) -> str:
    """Require the cited receipt's durable artifact to remain exact."""
    stored = replay_probe_path(session, row.get("input_path"))
    if stored is None:
        raise SystemExit(
            f"{action} refused: probe move {row.get('move_id')} has an invalid or missing stored artifact"
        )
    try:
        source = stored.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise SystemExit(
            f"{action} refused: probe move {row.get('move_id')} stored artifact is not readable UTF-8"
        ) from exc
    input_sha256 = _probe_input_hash(row, action)
    if _sha256_text(source) != input_sha256:
        raise SystemExit(
            f"{action} refused: probe move {row.get('move_id')} stored artifact hash does not match input hash"
        )
    return source


def cmd_open(args: argparse.Namespace, root: Path) -> dict[str, Any]:
    session = Session(args.sessions_root, args.session)
    if session.exists():
        raise SystemExit(f"session already exists: {session.directory}")
    try:
        session.probes_dir.mkdir(parents=True, exist_ok=True)
        session.ledger_path.touch()
    except OSError as exc:
        raise SystemExit(
            f"cannot create workbench session {session.directory}: {exc}"
        ) from exc
    record = {
        "schema": SESSION_SCHEMA,
        "move_id": "m001",
        "at": _utc_now(),
        "kind": "session_opened",
        "session": args.session,
        "actor": args.actor,
        "intent": args.intent,
        "environment_fingerprint": environment_fingerprint(root),
        "authority_note": (
            "notes are advisory cognition; only probe receipts carry"
            " kernel authority"
        ),
    }
    return session.append(record)


def cmd_note(args: argparse.Namespace, root: Path) -> dict[str, Any]:
    session = Session(args.sessions_root, args.session)
    if not session.exists():
        raise SystemExit(f"unknown session: {args.session}")
    record = _base_record(session, "note")
    record.update(
        {
            "note_kind": args.kind,
            "text": args.text,
            "falsifier": args.falsifier,
        }
    )
    if args.kind == "conjecture" and not args.falsifier:
        record["warning"] = "conjecture_without_declared_falsifier"
    return session.append(record)


def cmd_probe(args: argparse.Namespace, root: Path) -> dict[str, Any]:
    session = Session(args.sessions_root, args.session)
    if not session.exists():
        raise SystemExit(f"unknown session: {args.session}")
    source_path = Path(args.file)
    if path_has_symlink_component(source_path):
        raise SystemExit(
            f"probe input path must not traverse symbolic links: {source_path}"
        )
    if not source_path.is_file():
        raise SystemExit(f"probe input not found: {source_path}")
    try:
        source = source_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise SystemExit(
            f"probe input is not readable UTF-8: {source_path}: {exc}"
        ) from exc
    move_id = session.next_move_id()
    stored = session.probes_dir / f"{move_id}.lean"
    if path_has_symlink_component(stored):
        raise SystemExit(
            f"probe artifact path must not traverse symbolic links: {stored}"
        )
    if stored.exists() or stored.is_symlink():
        raise SystemExit(f"probe artifact already exists: {stored}")
    try:
        shutil.copyfile(source_path, stored)
    except OSError as exc:
        raise SystemExit(
            f"probe artifact could not be stored: {stored}: {exc}"
        ) from exc
    receipt = run_lean_probe(root, source)
    record = _base_record(session, "probe")
    record["move_id"] = move_id
    record.update(
        {
            "input_path": str(stored.relative_to(session.directory)),
            "input_sha256": _sha256_text(source),
            "label": args.label,
            "kernel_receipt": receipt,
        }
    )
    return session.append(record)


def cmd_claim(args: argparse.Namespace, root: Path) -> dict[str, Any]:
    session = Session(args.sessions_root, args.session)
    if not session.exists():
        raise SystemExit(f"unknown session: {args.session}")
    probes = {
        row["move_id"]: row
        for row in session.moves()
        if row.get("kind") == "probe"
    }
    cited = probes.get(args.probe)
    if cited is None:
        raise SystemExit(
            f"claim refused: no probe move {args.probe} in session"
        )
    verdict = _probe_verdict(cited, "claim")
    if verdict != "kernel_accepted":
        raise SystemExit(
            "claim refused: cited probe verdict is"
            f" {verdict!r}, not kernel_accepted"
        )
    input_sha256 = _probe_input_hash(cited, "claim")
    _stored_probe_source(session, cited, "claim")
    record = _base_record(session, "claim")
    record.update(
        {
            "text": args.text,
            "cited_probe": args.probe,
            "cited_input_sha256": input_sha256,
            "authority": "kernel_accepted_probe_receipt",
        }
    )
    return session.append(record)


def cmd_close(args: argparse.Namespace, root: Path) -> dict[str, Any]:
    session = Session(args.sessions_root, args.session)
    if not session.exists():
        raise SystemExit(f"unknown session: {args.session}")
    moves = session.moves()
    counts: dict[str, int] = {}
    for row in moves:
        counts[row["kind"]] = counts.get(row["kind"], 0) + 1
    accepted_probes = 0
    for row in moves:
        if row["kind"] == "probe" and _probe_verdict(row, "close") == "kernel_accepted":
            accepted_probes += 1
    record = _base_record(session, "session_closed")
    record.update(
        {
            "outcome": args.outcome,
            "summary": args.summary,
            "move_counts": counts,
            "kernel_accepted_probes": accepted_probes,
        }
    )
    return session.append(record)


def replay_probe_path(session: Session, input_path: Any) -> Path | None:
    """Resolve only a regular stored probe beneath the session directory."""
    if not isinstance(input_path, str) or not input_path or "\x00" in input_path:
        return None
    relative = Path(input_path)
    if (
        relative.is_absolute()
        or ".." in relative.parts
        or "." in relative.parts
        or "\\" in input_path
    ):
        return None
    candidate = session.directory / relative
    if path_has_symlink_component(candidate) or not candidate.is_file():
        return None
    return candidate


def cmd_replay(args: argparse.Namespace, root: Path) -> dict[str, Any]:
    session = Session(args.sessions_root, args.session)
    if not session.exists():
        raise SystemExit(f"unknown session: {args.session}")
    results = []
    for row in session.moves():
        if row.get("kind") != "probe":
            continue
        stored = replay_probe_path(session, row.get("input_path"))
        if stored is None:
            results.append(
                {
                    "move_id": row.get("move_id"),
                    "replay": "input_path_rejected",
                }
            )
            continue
        input_sha256 = row.get("input_sha256")
        if not isinstance(input_sha256, str):
            results.append(
                {
                    "move_id": row.get("move_id"),
                    "replay": "input_hash_missing",
                }
            )
            continue
        try:
            source = stored.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            results.append(
                {
                    "move_id": row.get("move_id"),
                    "replay": "input_unreadable",
                }
            )
            continue
        if _sha256_text(source) != input_sha256:
            results.append(
                {
                    "move_id": row.get("move_id"),
                    "replay": "input_bytes_changed",
                }
            )
            continue
        kernel_receipt = row.get("kernel_receipt")
        recorded_verdict = (
            kernel_receipt.get("verdict")
            if isinstance(kernel_receipt, dict)
            else None
        )
        if not isinstance(recorded_verdict, str):
            results.append(
                {
                    "move_id": row.get("move_id"),
                    "replay": "kernel_receipt_invalid",
                }
            )
            continue
        fresh = run_lean_probe(root, source)
        results.append(
            {
                "move_id": row.get("move_id"),
                "recorded_verdict": recorded_verdict,
                "replayed_verdict": fresh["verdict"],
                "replay": (
                    "match"
                    if fresh["verdict"]
                    == recorded_verdict
                    else "verdict_changed"
                ),
            }
        )
    return {
        "schema": "workbench-replay-receipt/1",
        "session": args.session,
        "at": _utc_now(),
        "environment_fingerprint": environment_fingerprint(root),
        "probes_replayed": len(results),
        "all_match": all(
            row.get("replay") == "match" for row in results
        ),
        "results": results,
    }


def cmd_show(args: argparse.Namespace, root: Path) -> dict[str, Any]:
    session = Session(args.sessions_root, args.session)
    if not session.exists():
        raise SystemExit(f"unknown session: {args.session}")
    compact = []
    for row in session.moves():
        entry: dict[str, Any] = {
            "move_id": row["move_id"],
            "kind": row["kind"],
        }
        if row["kind"] == "note":
            entry["note_kind"] = _required_string(row, "note_kind", "show")
            entry["text"] = _required_string(row, "text", "show")
        elif row["kind"] == "probe":
            entry["label"] = row.get("label")
            entry["verdict"] = _probe_verdict(row, "show")
        elif row["kind"] == "claim":
            entry["text"] = _required_string(row, "text", "show")
            entry["cited_probe"] = _required_string(row, "cited_probe", "show")
        elif row["kind"] in ("session_opened", "session_closed"):
            entry["detail"] = row.get("intent") or row.get("summary")
        compact.append(entry)
    return {"session": args.session, "moves": compact}


def build_parser(root: Path) -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sessions-root",
        type=Path,
        default=root / "workbench" / "sessions",
        help="override the sessions directory (used by tests)",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_open = sub.add_parser("open")
    p_open.add_argument("--session", required=True)
    p_open.add_argument("--intent", required=True)
    p_open.add_argument("--actor", default="unnamed_agent")
    p_open.set_defaults(func=cmd_open)

    p_note = sub.add_parser("note")
    p_note.add_argument("--session", required=True)
    p_note.add_argument("--kind", required=True, choices=NOTE_KINDS)
    p_note.add_argument("--text", required=True)
    p_note.add_argument("--falsifier", default=None)
    p_note.set_defaults(func=cmd_note)

    p_probe = sub.add_parser("probe")
    p_probe.add_argument("--session", required=True)
    p_probe.add_argument("--file", required=True)
    p_probe.add_argument("--label", default=None)
    p_probe.set_defaults(func=cmd_probe)

    p_claim = sub.add_parser("claim")
    p_claim.add_argument("--session", required=True)
    p_claim.add_argument("--text", required=True)
    p_claim.add_argument("--probe", required=True)
    p_claim.set_defaults(func=cmd_claim)

    p_close = sub.add_parser("close")
    p_close.add_argument("--session", required=True)
    p_close.add_argument(
        "--outcome", required=True, choices=CLOSE_OUTCOMES
    )
    p_close.add_argument("--summary", required=True)
    p_close.set_defaults(func=cmd_close)

    p_replay = sub.add_parser("replay")
    p_replay.add_argument("--session", required=True)
    p_replay.set_defaults(func=cmd_replay)

    p_show = sub.add_parser("show")
    p_show.add_argument("--session", required=True)
    p_show.set_defaults(func=cmd_show)

    return parser


def main(argv: list[str] | None = None) -> int:
    root = repo_root()
    parser = build_parser(root)
    args = parser.parse_args(argv)
    result = args.func(args, root)
    print(json.dumps(result, sort_keys=True, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
