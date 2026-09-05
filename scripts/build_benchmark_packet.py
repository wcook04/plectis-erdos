#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Construct a leakage-controlled benchmark packet by temporal git cut.

A packet is a source snapshot at the commit immediately BEFORE the target
was introduced, plus the artifacts allowed by its ablation arm. It carries no
Git metadata or future objects. The evaluator must separately restrict the
agent's filesystem and network access; a directory is not a process sandbox.

The arms answer the question the whole layer exists to justify: does the
semantic and mechanism scaffolding actually help recover mathematics, or would a
strong model plus ordinary source retrieval have done as well?

    signatures             the cut checkout alone
    graph                  + the statement graph, filtered to the cut
    mechanism              + mechanism records and capsules, filtered to the cut
    negative               + failure receipts (blocked routes, surviving siblings)
    mechanism_shuffled     control: same records, explanations permuted off-target
    mechanism_offproblem   control: real mechanisms about the other problem

The two controls exist because a win over the graph arm is uninterpretable
without them. Library-learning gains in this area have been shown to vanish once
compute is matched, and unrelated subgraphs have been shown to reproduce
full-graph behaviour, so 'more relevant-looking prose helped' is the hypothesis
that has to be excluded before 'this mechanism helped' can be entertained.

Every injected artifact is filtered: a node, mechanism or receipt whose evidence
names a declaration that does not exist at the cut is dropped, because carrying
it would leak the future. The filter is applied against declarations extracted
from the cut checkout itself, never against the current atlas.

The answer key and introducing-commit metadata stay outside the snapshot.
Historical source may contain hints, so task suitability still requires review.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import shutil
import tarfile
from pathlib import Path
import re
import subprocess
import sys

import validation_singleflight as singleflight

ROOT = Path(__file__).resolve().parents[1]
ENVIRONMENT_CONTRACT = "clean_reproduction_subprocess_environment_v1"
GIT_COMMAND_TIMEOUT_SECONDS = singleflight.GIT_COMMAND_TIMEOUT_SECONDS
CORPUS = ROOT / "docs" / "semantic_corpus.json"
LAB = ROOT / "docs" / "theory_lab.json"
ARMS = (
    "signatures",
    "graph",
    "mechanism",
    "negative",
    "mechanism_shuffled",
    "mechanism_offproblem",
)

# Arm inclusion is cumulative: each arm sees everything the arms before it saw.
# The last two are controls, and they are not optional. Published work has shown
# both that skill-library gains evaporate once compute is matched, and that
# unrelated subgraphs recover full-graph behaviour -- so an unshuffled win over
# the graph arm establishes nothing on its own. The controls sit at the same
# depth as ``mechanism`` and carry the same volume of prose, which is what makes
# them comparable.
ARM_LAYERS = {
    "signatures": (),
    "graph": ("graph",),
    "mechanism": ("graph", "mechanism"),
    "negative": ("graph", "mechanism", "negative"),
    "mechanism_shuffled": ("graph", "mechanism_shuffled"),
    "mechanism_offproblem": ("graph", "mechanism_offproblem"),
}

CONTROL_ARMS = ("mechanism_shuffled", "mechanism_offproblem")

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|local\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.!?]*)"
)
LIBRARY_ROOTS = ("Erdos249257", "ErdosProblems")


def git(*args: str, cwd: Path | None = None) -> str:
    proc = subprocess.run(
        ("git",) + args,
        cwd=str(cwd or ROOT),
        capture_output=True,
        text=True,
        check=False,
        env=singleflight.command_environment(),
        timeout=GIT_COMMAND_TIMEOUT_SECONDS,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {proc.stderr.strip()}")
    return proc.stdout


def materialize_cut(dest: Path, revision: str) -> None:
    """Export tracked files without a shared object store or Git selectors."""
    if dest.exists() or dest.is_symlink():
        raise SystemExit(f"packet destination already exists: {dest}")
    if dest == ROOT.resolve() or ROOT.resolve() in dest.parents:
        raise SystemExit("packet destination must be outside the source repository")
    archive = subprocess.run(
        ("git", "archive", "--format=tar", revision), cwd=str(ROOT),
        capture_output=True, check=True, env=singleflight.command_environment(),
        timeout=GIT_COMMAND_TIMEOUT_SECONDS,
    ).stdout
    with tarfile.open(fileobj=io.BytesIO(archive)) as bundle:
        members = bundle.getmembers()
        for member in members:
            path = Path(member.name)
            if (path.is_absolute() or ".." in path.parts or ".git" in path.parts
                    or not (member.isdir() or member.isfile())):
                raise SystemExit(f"unsupported snapshot member: {member.name}")
        dest.mkdir(parents=True)
        for member in members:
            path = dest / member.name
            if member.isdir():
                path.mkdir(parents=True, exist_ok=True)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                source = bundle.extractfile(member)
                assert source is not None
                with source, path.open("wb") as output:
                    shutil.copyfileobj(source, output)
                path.chmod(0o755 if member.mode & 0o111 else 0o644)


def remove_packet(dest: Path) -> None:
    """Remove only a recognised generated snapshot, never an arbitrary directory."""
    if dest == ROOT.resolve() or dest in ROOT.resolve().parents:
        raise SystemExit("refusing to remove the source repository or an ancestor")
    marker = dest / "docs/_packet/MANIFEST.json"
    if dest.is_symlink() or not marker.is_file():
        raise SystemExit("refusing to remove a directory without a packet manifest")
    manifest = json.loads(marker.read_text(encoding="utf-8"))
    if manifest.get("schema") != "erdos249257-benchmark-packet/2":
        raise SystemExit("refusing to remove an unrecognised packet")
    shutil.rmtree(dest)


def code_mask(lines: list[str]) -> list[bool]:
    """Mark lines that are outside block comments and not line comments.

    Declaration heads are only read from code lines. Docstring prose that wraps
    onto a line beginning with a keyword is not a declaration, and treating it
    as one is a defect this repository has already been bitten by twice.
    """
    mask: list[bool] = []
    depth = 0
    for line in lines:
        start_depth = depth
        i = 0
        while i < len(line) - 1:
            pair = line[i : i + 2]
            if pair == "/-":
                depth += 1
                i += 2
                continue
            if pair == "-/":
                depth = max(0, depth - 1)
                i += 2
                continue
            if pair == "--" and depth == 0:
                break
            i += 1
        mask.append(start_depth == 0 and not line.lstrip().startswith("--"))
    return mask


def declarations_at(root: Path) -> set[str]:
    """Extract every declaration name present in a checkout.

    Matches the atlas extractor, including the continuation-line lookahead: a
    declaration whose name sits on the line after its keyword must still be
    found, or the leak filter would wrongly believe it absent.
    """
    names: set[str] = set()
    for library in LIBRARY_ROOTS:
        base = root / library
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            try:
                lines = path.read_text(encoding="utf-8").splitlines()
            except (OSError, UnicodeDecodeError):
                continue
            mask = code_mask(lines)
            for index, line in enumerate(lines):
                if not mask[index]:
                    continue
                match = DECL_RE.match(line)
                if match:
                    names.add(match.group(2))
                    continue
                # Keyword alone on this line: the name may be on a following one.
                head = re.match(
                    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+"
                    r"|unsafe\s+|local\s+)*"
                    r"(theorem|lemma|def|abbrev|instance)\s*$",
                    line,
                )
                if not head:
                    continue
                for offset in range(1, 4):
                    nxt = index + offset
                    if nxt >= len(lines) or not mask[nxt]:
                        continue
                    stripped = lines[nxt].strip()
                    if not stripped:
                        continue
                    name = re.match(r"^([A-Za-z_][A-Za-z0-9_'.!?]*)", stripped)
                    if name:
                        names.add(name.group(1))
                    break
    return names


def introduction_commit(target: str) -> tuple[str, str, str]:
    """Return (introducing_sha, parent_sha, subject) for a declaration name."""
    out = git(
        "log",
        "-S",
        target,
        "--reverse",
        "--format=%H\t%ad\t%s",
        "--date=short",
        "--",
        "*.lean",
    )
    rows = [r for r in out.splitlines() if r.strip()]
    if not rows:
        raise SystemExit(f"no commit introduces {target!r} in any .lean file")
    sha, date, subject = rows[0].split("\t", 2)
    parent = git("rev-parse", f"{sha}^").strip()
    return sha, parent, f"{date} {subject}"


def node_for(corpus: dict, target: str) -> dict | None:
    for node in corpus["statement_nodes"]:
        for ev in node.get("evidence", ()):
            if ev.get("declaration") == target:
                return node
    return None


def evidence_names(record: dict) -> list[str]:
    """Every declaration name a record depends on, across the shapes we carry."""
    names: list[str] = []
    for ev in record.get("evidence", ()) or ():
        if isinstance(ev, dict) and ev.get("declaration"):
            names.append(ev["declaration"])
        elif isinstance(ev, str):
            names.append(ev)
    for key in ("realising_declarations", "minimal_formal_backbone", "declarations"):
        for name in record.get(key, ()) or ():
            if isinstance(name, str):
                names.append(name)
    return names


def filter_to_cut(records: list[dict], available: set[str]) -> tuple[list[dict], list[str]]:
    """Keep records whose every cited declaration exists at the cut.

    A record citing a declaration that does not yet exist is a record about the
    future. Dropping it is the whole leak control, so the rule is all-or-nothing
    rather than a partial trim: a mechanism stripped of its post-cut evidence
    would still carry post-cut prose.
    """
    kept: list[dict] = []
    dropped: list[str] = []
    for record in records:
        names = evidence_names(record)
        if names and all(name in available for name in names):
            kept.append(record)
        else:
            dropped.append(record.get("id") or record.get("mechanism_id") or "<unnamed>")
    return kept, dropped


def build_packet(target: str, arm: str, dest: Path, keep: bool, problem: str = "") -> dict:
    if arm not in ARMS:
        raise SystemExit(f"unknown arm {arm!r}; expected one of {', '.join(ARMS)}")

    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))
    lab = json.loads(LAB.read_text(encoding="utf-8")) if LAB.exists() else {}

    sha, parent, subject = introduction_commit(target)
    node = node_for(corpus, target)

    dest = dest.resolve()
    materialize_cut(dest, parent)

    available = declarations_at(dest)
    if target in available:
        shutil.rmtree(dest)
        raise SystemExit(
            f"LEAK: {target!r} is present at the cut {parent[:8]}; "
            "the -S search found a later edit, not the introduction"
        )

    layers = ARM_LAYERS[arm]
    injected: list[str] = []
    dropped: dict[str, list[str]] = {}
    packet_dir = dest / "docs" / "_packet"
    packet_dir.mkdir(parents=True, exist_ok=True)

    if "graph" in layers:
        nodes, drop = filter_to_cut(corpus["statement_nodes"], available)
        keep_ids = {n["id"] for n in nodes}
        relations = [
            r
            for r in corpus["relations"]
            if r.get("from") in keep_ids and r.get("to") in keep_ids
        ]
        payload = {
            "note": (
                "Statement graph filtered to the state of the development at this "
                "checkout. Nodes whose evidence postdates the checkout are absent."
            ),
            "concepts": corpus["concepts"],
            "statement_nodes": nodes,
            "relations": relations,
        }
        (packet_dir / "statement_graph.json").write_text(
            json.dumps(payload, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
        )
        injected.append("docs/_packet/statement_graph.json")
        dropped["statement_nodes"] = drop

    if "mechanism_shuffled" in layers and lab.get("mechanisms"):
        mechs, drop = filter_to_cut(lab["mechanisms"], available)
        # Permute the fields that carry the explanation away from the mechanism
        # they belong to. Volume, vocabulary and schema are untouched; only the
        # attachment is destroyed. If the mechanism arm beats this, the specific
        # attachment is doing the work rather than the presence of mathematical
        # prose.
        order = sorted(range(len(mechs)), key=lambda i: hashlib.sha256(
            (target + str(i)).encode()
        ).hexdigest())
        rotated = order[1:] + order[:1] if len(order) > 1 else order
        shuffled = []
        for slot, source in zip(order, rotated):
            record = dict(mechs[slot])
            donor = mechs[source]
            for field in ("invariant", "transformation", "observable_controlled",
                          "core_idea", "statement_nodes", "sharp_failures"):
                record[field] = donor.get(field)
            shuffled.append(record)
        payload = {
            "note": (
                "CONTROL ARM. These records are schema-valid but their explanatory "
                "fields have been permuted away from the mechanism they describe."
            ),
            "mechanisms": shuffled,
        }
        (packet_dir / "mechanisms.json").write_text(
            json.dumps(payload, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
        )
        injected.append("docs/_packet/mechanisms.json [shuffled control]")
        dropped["mechanisms"] = drop

    if "mechanism_offproblem" in layers and lab.get("mechanisms"):
        mechs, drop = filter_to_cut(lab["mechanisms"], available)
        # Real, correctly-attached mechanisms about the *other* problem. Same
        # schema and comparable volume, wrong subject.
        off = [m for m in mechs if m.get("problem_reach") not in (problem, "both")]
        payload = {
            "note": (
                "CONTROL ARM. These mechanisms are genuine and correctly attached, "
                "but they concern a different problem than the question asked."
            ),
            "mechanisms": off,
        }
        (packet_dir / "mechanisms.json").write_text(
            json.dumps(payload, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
        )
        injected.append("docs/_packet/mechanisms.json [off-problem control]")
        dropped["mechanisms"] = drop

    if "mechanism" in layers and lab.get("mechanisms"):
        mechs, drop = filter_to_cut(lab["mechanisms"], available)
        keep_ids = {m["mechanism_id"] for m in mechs}
        capsules = [
            c for c in lab.get("capsules", ()) if c.get("mechanism_id") in keep_ids
        ]
        # A capsule's transfer_challenge is a blind test for humans reading the
        # layer; inside a benchmark packet it is a hint about what to look for.
        capsules = [{k: v for k, v in c.items() if k != "transfer_challenge"} for c in capsules]
        payload = {
            "note": (
                "Mechanism records and explanation capsules, filtered to this "
                "checkout. Transfer challenges are withheld inside packets."
            ),
            "mechanisms": mechs,
            "capsules": capsules,
        }
        (packet_dir / "mechanisms.json").write_text(
            json.dumps(payload, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
        )
        injected.append("docs/_packet/mechanisms.json")
        dropped["mechanisms"] = drop

    if "negative" in layers and lab.get("failure_receipts"):
        receipts, drop = filter_to_cut(lab["failure_receipts"], available)
        payload = {
            "note": (
                "Failure receipts: routes tried and blocked, the mechanism each "
                "rules out, and the sibling mechanisms it does not reach."
            ),
            "failure_receipts": receipts,
        }
        (packet_dir / "failure_receipts.json").write_text(
            json.dumps(payload, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
        )
        injected.append("docs/_packet/failure_receipts.json")
        dropped["failure_receipts"] = drop

    manifest = {
        "schema": "erdos249257-benchmark-packet/2",
        "arm": arm,
        "isolation": "source_snapshot_without_git_history",
        "runner_requirements": ["isolated filesystem", "restricted network access"],
        "declarations_at_cut": len(available),
        "injected": injected,
        "dropped_as_post_cut": {k: len(v) for k, v in dropped.items()},
        "is_control_arm": arm in CONTROL_ARMS,
        "leak_controls": [
            "target declaration verified absent from the checkout",
            "injected records filtered against declarations extracted from the checkout",
            "answer-key identity and introducing metadata withheld from the manifest",
            "Git metadata and future objects excluded from the snapshot",
            "capsule transfer challenges withheld",
        ],
    }
    (packet_dir / "MANIFEST.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
    )

    answer = {
        "target": target,
        "manifest_sha256": hashlib.sha256(
            (packet_dir / "MANIFEST.json").read_bytes()
        ).hexdigest(),
        "arm": arm,
        "cut_commit": parent,
        "introducing_commit": sha,
        "introducing_subject": subject,
        "node_id": node.get("id") if node else None,
        "canonical_statement": node.get("canonical_statement") if node else None,
        "logical_class": node.get("logical_class") if node else None,
        "engine": node.get("engine") if node else None,
        "concepts": node.get("concepts") if node else [],
        "problem": node.get("problem") if node else None,
    }

    return {"manifest": manifest, "answer_key": answer, "worktree": str(dest)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", required=True, help="declaration name to hold out")
    parser.add_argument("--arm", required=True, choices=ARMS)
    parser.add_argument(
        "--problem",
        default="",
        help="the item's problem; required by the off-problem control arm",
    )
    parser.add_argument("--dest", required=True, help="new snapshot directory (outside the repo)")
    parser.add_argument(
        "--answer-key", help="write the answer key here (never inside the worktree)"
    )
    parser.add_argument("--remove", action="store_true", help="remove an existing packet and exit")
    args = parser.parse_args()

    requested_dest = Path(args.dest)
    if requested_dest.is_symlink():
        raise SystemExit("packet destination must not be a symbolic link")
    dest = requested_dest.resolve()
    if args.remove:
        remove_packet(dest)
        print(f"removed {dest}")
        return 0

    result = build_packet(args.target, args.arm, dest, keep=True, problem=args.problem)
    if args.answer_key:
        key = Path(args.answer_key).resolve()
        if key == dest or dest in key.parents:
            raise SystemExit("refusing to write the answer key inside the packet")
        key.parent.mkdir(parents=True, exist_ok=True)
        key.write_text(
            json.dumps(result["answer_key"], ensure_ascii=False, indent=1) + "\n",
            encoding="utf-8",
        )
    print(json.dumps(result["manifest"], ensure_ascii=False, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
