#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Prepare a recovery packet from a registered historical source cut.

A packet is an export of the frozen cut in benchmark_items.json, without Git
history, plus the derived artifacts selected by the arm. The target declaration
is checked absent. This prepares files; it does not isolate a participant from
the rest of its filesystem, network, or prior knowledge. A scored run still
needs a separately bound runner, blind review, and matched control workloads.

The arms answer the question the whole layer exists to justify: does the
semantic and mechanism scaffolding actually help recover mathematics, or would a
strong model plus ordinary source retrieval have done as well?

    signatures             the cut checkout alone
    graph                  + the statement graph, filtered to the cut
    mechanism              + mechanism records and capsules, filtered to the cut
    negative               + failure receipts (blocked routes, surviving siblings)
    mechanism_shuffled     control: same records, explanations permuted off-target
    mechanism_offproblem   control: real mechanisms about the other problem

The controls are candidates for that comparison. They do not yet match the
mechanism arm's capsules or prose volume and must not be treated as a completed
matched-control design.

Every injected artifact is filtered: a node, mechanism or receipt whose evidence
names a declaration that does not exist at the cut is dropped, because carrying
it would leak the future. The filter is applied against declarations extracted
from the cut checkout itself, never against the current atlas.

Future commit metadata and the answer key stay outside the export. Filtering
declaration references does not establish that current explanatory prose was
available at the cut or that it contains no hints; that requires separate review.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from semantic_corpus_storage import load_corpus
import re
import subprocess
import sys
import tarfile
import tempfile

import validation_singleflight as singleflight

ROOT = Path(__file__).resolve().parents[1]
ENVIRONMENT_CONTRACT = "clean_reproduction_subprocess_environment_v1"
GIT_COMMAND_TIMEOUT_SECONDS = singleflight.GIT_COMMAND_TIMEOUT_SECONDS
CORPUS = ROOT / "docs" / "semantic_corpus.json.gz"
LAB = ROOT / "docs" / "theory_lab.json"
BENCHMARK_ITEMS = ROOT / "docs" / "semantic" / "lab" / "benchmark_items.json"
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
# depth as ``mechanism`` but still require capsule and workload matching before
# a scored comparison.
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


def validate_destination(dest: Path) -> Path:
    """Do not overwrite a packet or let it inherit an enclosing Git history."""
    if dest.exists() or dest.is_symlink():
        raise SystemExit(f"refusing existing packet destination: {dest}")
    dest = dest.resolve()
    if dest == ROOT.resolve() or ROOT.resolve() in dest.parents:
        raise SystemExit("packet destination must be outside the source repository")
    if any((parent / ".git").exists() for parent in dest.parents):
        raise SystemExit("packet destination must be outside every Git worktree")
    return dest


def export_snapshot(cut: str, dest: Path) -> None:
    """Export regular tracked files, never a linked worktree or Git database."""
    dest = validate_destination(dest)
    inventory = {}
    for row in git("ls-tree", "-rz", cut).split("\0"):
        if not row:
            continue
        meta, name = row.split("\t", 1)
        mode, kind, oid = meta.split()
        if kind != "blob" or mode not in ("100644", "100755"):
            raise SystemExit(f"only regular tracked files can be exported: {name}")
        inventory[name] = (oid, mode == "100755")
    with tempfile.TemporaryFile() as archive:
        proc = subprocess.run(
            ("git", "archive", "--format=tar", cut), cwd=str(ROOT),
            stdout=archive, stderr=subprocess.PIPE, check=False,
            env=singleflight.command_environment(),
            timeout=GIT_COMMAND_TIMEOUT_SECONDS,
        )
        if proc.returncode:
            raise RuntimeError(f"git archive failed: {proc.stderr.decode(errors='replace').strip()}")
        archive.seek(0)
        with tarfile.open(fileobj=archive, mode="r:") as source:
            members = source.getmembers()
            exported = {}
            for member in members:
                name = Path(member.name)
                if (name.is_absolute() or ".." in name.parts or ".git" in name.parts
                        or not (member.isfile() or member.isdir())):
                    raise SystemExit(f"unsupported archive entry: {member.name}")
                if member.isfile():
                    if member.name in exported:
                        raise SystemExit(f"duplicate archive entry: {member.name}")
                    digest = hashlib.sha1(f"blob {member.size}\0".encode())
                    with source.extractfile(member) as inp:
                        while chunk := inp.read(1024 * 1024):
                            digest.update(chunk)
                    exported[member.name] = (digest.hexdigest(), bool(member.mode & 0o111))
            # archive can apply export-ignore/export-subst, including local
            # info/attributes. Reject any omission or transformation instead of
            # treating an altered export as the historical source baseline.
            if exported != inventory:
                raise SystemExit("archive differs from the frozen Git tree (paths, bytes or executable modes)")
            # All entries are validated before creating the destination. Use
            # exclusive creation: neither a failed nor an old run is replaced.
            dest.mkdir(parents=True, exist_ok=False)
            for member in members:
                path = dest / member.name
                if member.isdir():
                    path.mkdir(parents=True, exist_ok=True)
                else:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    with source.extractfile(member) as inp, path.open("xb") as out:
                        while chunk := inp.read(1024 * 1024):
                            out.write(chunk)
                    path.chmod(0o755 if member.mode & 0o111 else 0o644)


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
    # Registered historical cuts predate the move into lean/. Read their
    # actual layout as well as the current one; zero declarations cannot prove
    # that a target is absent.
    paths = {
        path
        for project in (root, root / "lean")
        for library in LIBRARY_ROOTS
        if (project / library).is_dir()
        for path in (project / library).rglob("*.lean")
    }
    for path in sorted(paths):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeDecodeError) as error:
            raise SystemExit(f"cannot inspect historical Lean source {path}: {error}") from error
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


def registered_item(target: str) -> dict:
    """Honor the authored holdout, including history preserved by reconciliation."""
    items = json.loads(BENCHMARK_ITEMS.read_text(encoding="utf-8"))
    matches = [item for item in items if item.get("target") == target]
    if len(matches) != 1:
        raise SystemExit(f"expected one registered benchmark item for {target!r}")
    item = matches[0]
    for key in ("cut_commit", "introducing_commit"):
        value = item.get(key, "")
        if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value):
            raise SystemExit(f"registered {key} must be a full commit hash")
        if git("cat-file", "-t", value).strip() != "commit":
            raise SystemExit(f"registered {key} is not a commit")
    if git("rev-parse", f"{item['introducing_commit']}^1").strip() != item["cut_commit"]:
        raise SystemExit("registered cut is not the introducing commit's first parent")
    return item


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

    A record citing a declaration that does not yet exist refers to the
    future. The reference filter is all-or-nothing
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


def build_packet(target: str, arm: str, dest: Path, keep: bool = True, problem: str = "") -> dict:
    if arm not in ARMS:
        raise SystemExit(f"unknown arm {arm!r}; expected one of {', '.join(ARMS)}")

    dest = validate_destination(dest)
    item = registered_item(target)
    if problem and problem != item.get("problem", problem):
        raise SystemExit("requested problem disagrees with registered benchmark item")
    problem = item.get("problem", problem)
    corpus = load_corpus(CORPUS, root=ROOT)
    lab = json.loads(LAB.read_text(encoding="utf-8")) if LAB.exists() else {}

    sha, parent = item["introducing_commit"], item["cut_commit"]
    subject = git("show", "-s", "--format=%s", sha).strip()
    node = node_for(corpus, target)

    export_snapshot(parent, dest)

    available = declarations_at(dest)
    if not available:
        raise SystemExit("no declarations found at the cut; target absence cannot be verified")
    if target in available:
        raise SystemExit(
            f"LEAK: {target!r} is present at the cut {parent[:8]}; "
            "packet preparation failed; retained files are not an admitted packet"
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
        # Real mechanisms about another problem. Their volume and capsules
        # remain unmatched; this is preparation, not an admitted control run.
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
        "evaluation_ready": False,
        "declarations_at_cut": len(available),
        "injected": injected,
        "dropped_as_post_cut": {k: len(v) for k, v in dropped.items()},
        "is_control_arm": arm in CONTROL_ARMS,
        "leak_controls": [
            "target declaration verified absent from the checkout",
            "injected records filtered against declarations extracted from the checkout",
            "no Git worktree, object database, or enclosing worktree",
            "future commit metadata and target fingerprint withheld from participant manifest",
            "capsule transfer challenges withheld",
        ],
        "outstanding_evaluation_controls": [
            "separate participant filesystem and network isolation",
            "review current derived prose and concepts for answer hints",
            "match capsules, prose volume, model, search tools and compute budgets across arms",
            "fresh participants and a fixed independently applied scoring rubric",
        ],
    }
    (packet_dir / "MANIFEST.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
    )

    answer = {
        "schema": "erdos249257-benchmark-evaluator/2",
        "item_id": item.get("item_id"),
        "target": target,
        "arm": arm,
        "cut_commit": parent,
        "introducing_commit": sha,
        "introducing_subject": subject,
        "target_fingerprint": "sha256:" + hashlib.sha256(target.encode()).hexdigest(),
        "registered_answer_key": item.get("answer_key"),
        "node_id": node.get("id") if node else None,
        "canonical_statement": node.get("canonical_statement") if node else None,
        "logical_class": node.get("logical_class") if node else None,
        "engine": node.get("engine") if node else None,
        "concepts": node.get("concepts") if node else [],
        "problem": node.get("problem") if node else None,
    }

    return {"manifest": manifest, "answer_key": answer, "packet": str(dest)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", required=True, help="declaration name to hold out")
    parser.add_argument("--arm", required=True, choices=ARMS)
    parser.add_argument(
        "--problem",
        default="",
        help="the item's problem; required by the off-problem control arm",
    )
    parser.add_argument("--dest", required=True, help="new export directory outside every Git worktree")
    parser.add_argument(
        "--answer-key", help="new evaluator receipt path outside the participant export"
    )
    parser.add_argument("--remove", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()

    if args.remove:
        parser.error("--remove is unsupported; existing packets are never removed by this builder")

    dest = validate_destination(Path(args.dest))
    raw_key = Path(args.answer_key) if args.answer_key else None
    if raw_key is not None and raw_key.is_symlink():
        parser.error("refusing an answer-key symlink")
    key = raw_key.resolve() if raw_key is not None else None
    if key is not None:
        if key == dest or dest in key.parents:
            parser.error("refusing to write the answer key inside the packet")
        if key.exists() or key.is_symlink():
            parser.error("refusing to replace an existing answer key")

    result = build_packet(args.target, args.arm, dest, keep=True, problem=args.problem)
    if key is not None:
        key.parent.mkdir(parents=True, exist_ok=True)
        with key.open("x", encoding="utf-8") as out:
            out.write(json.dumps(result["answer_key"], ensure_ascii=False, indent=1) + "\n")
    print(json.dumps(result["manifest"], ensure_ascii=False, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
