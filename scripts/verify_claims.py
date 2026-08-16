# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Follow one public claim to its source, its receipts, and the point where it stops.

The public invitation for this repository is a single concrete test: clone it,
hand it to whatever agent harness you use, and ask that harness to take one
claim back to the source, the receipts, and the place the claim stops. Every
ingredient for that test was already committed here -- ``docs/claims.json`` owns
the claim register, the Lean modules own the proofs, ``status_taxonomy`` owns
what each status is allowed to mean, and ``non_claims`` plus
``remaining_open_propositions`` own the boundary. What was missing was the verb.
A reader had to know which of the hundred scripts in this directory to reach
for, and a reader who guessed wrong learned nothing about the claim.

This module is that verb, and it is deliberately small:

    python3 scripts/verify_claims.py --claim eb_full_support

resolves one claim id into the statement the public is given, the declarations
that carry it, the file and line where each declaration actually sits *in this
checkout*, the docstring the author attached to it, and the typed boundary that
says what the claim does not settle. Nothing is taken on trust from the
register: the locator is re-derived from the Lean source on every run, so a
drifted line number is reported as drift rather than printed as fact. That last
point is a *presentation* guarantee, not a new safety net -- ``check_release.py``
already re-derives every locator and is already blocking in CI, and it, not this
module, is the authority on whether the register is sound. What this module adds
is that a reader gets the re-derived source text, the docstring, the receipts,
and the boundary on one screen from one command, instead of a JSON projection
they must go and confirm by hand.

Two failure modes are separated on purpose, because conflating them is what
makes a hostile reading go wrong.

*Environment* problems are not claim problems. A shallow clone cannot see the
pinned formal-source commit, so the pinned-history gates fail with messages that
read like missing evidence when the evidence is merely unfetched. That is
reported here as an environment block with the exact remedy, and it exits 2 --
never 1 -- so that "your clone is truncated" can never be mistaken for "the
claim does not hold".

*Claim* problems are the ones worth a reader's attention: a declaration that no
longer exists, a locator that points at the wrong line, a status outside the
taxonomy, an open proposition pointing at a claim that was deleted. Those exit 1
and say which claim and which declaration.

Exit codes: 0 verified, 1 a claim or gate genuinely failed, 2 the environment
could not answer the question.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
CLAIMS_PATH = REPO_ROOT / "docs" / "claims.json"

# Declarations wrap in this corpus: `theorem` frequently sits on its own line
# with the name indented beneath it. A locator is therefore accepted when the
# name appears within a short window of the recorded line, provided a
# declaration keyword introduces it.
LOCATOR_WINDOW_BEFORE = 2
LOCATOR_WINDOW_AFTER = 3
DECLARATION_KEYWORDS = frozenset(
    {
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "instance",
        "structure",
        "inductive",
        "example",
        "class",
    }
)

# Modifiers that may precede the declaration keyword. Missing one of these is
# what makes a naive matcher report a live declaration as absent.
DECLARATION_MODIFIERS = frozenset(
    {
        "private",
        "protected",
        "noncomputable",
        "partial",
        "unsafe",
        "scoped",
        "local",
        "nonrec",
        "@[simp]",
    }
)

# Gates that read pinned history. On a shallow clone these fail for a reason
# that has nothing to do with the mathematics, so they are reported as blocked
# rather than failed.
HISTORY_DEPENDENT_GATES = frozenset(
    {
        "check_problem_note_sources.py",
        "check_publication_contract.py",
        "check_release.py",
        "check_release_ref.py",
    }
)

# Gates that need a third-party tool the repository does not vendor.
OPTIONAL_TOOL_GATES = {"check_metadata.py": "cffconvert"}


def load_claims() -> dict[str, Any]:
    """Read the claim register, which is the single owner of claim identity."""
    with CLAIMS_PATH.open(encoding="utf-8") as handle:
        return json.load(handle)


def git_output(*args: str) -> str | None:
    """Run a read-only git query, returning None when git cannot answer."""
    try:
        completed = subprocess.run(
            ["git", "-C", str(REPO_ROOT), *args],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return None
    if completed.returncode != 0:
        return None
    return completed.stdout.strip()


def describe_environment(claims: dict[str, Any]) -> dict[str, Any]:
    """Classify what this checkout can and cannot be asked.

    A truncated clone is the single most common way the published test goes
    wrong, so it is named first and named precisely.
    """
    shallow = git_output("rev-parse", "--is-shallow-repository") == "true"
    formal_ref = claims.get("release", {}).get("formal_source", {}).get("ref")
    pinned_present = False
    if formal_ref:
        pinned_present = git_output("cat-file", "-e", f"{formal_ref}^{{commit}}") is not None

    blocks: list[str] = []
    if shallow:
        blocks.append(
            "shallow clone: pinned-history gates cannot resolve the formal-source "
            "commit. Remedy: git fetch --unshallow"
        )
    elif formal_ref and not pinned_present:
        blocks.append(
            f"pinned formal-source commit {formal_ref[:12]} is not present in this "
            "clone. Remedy: git fetch --tags origin"
        )
    return {
        "shallow_clone": shallow,
        "pinned_formal_source_ref": formal_ref,
        "pinned_formal_source_present": pinned_present,
        "head": git_output("rev-parse", "HEAD"),
        "missing_optional_tools": sorted(
            tool for tool in set(OPTIONAL_TOOL_GATES.values()) if shutil.which(tool) is None
        ),
        "blocks": blocks,
    }


def resolve_declaration(declaration: dict[str, Any]) -> dict[str, Any]:
    """Re-derive a declaration's true position instead of trusting the register.

    Returns the resolution verdict, the line actually found, and the docstring
    attached to the declaration, because the docstring is usually where the
    author says what the theorem does not give.
    """
    name = declaration.get("name", "")
    module_ref = declaration.get("module", "")
    recorded = declaration.get("line")
    module_path = REPO_ROOT / module_ref
    result: dict[str, Any] = {
        "name": name,
        "module": module_ref,
        "recorded_line": recorded,
        "resolved_line": None,
        "status": "unresolved",
        "signature": None,
        "docstring": None,
    }
    if not module_path.is_file():
        result["status"] = "module_missing"
        return result

    lines = module_path.read_text(encoding="utf-8", errors="replace").splitlines()

    # A declaration inside `namespace Foo` is registered as `Foo.bar` but written
    # as `bar`, so the final component is an accepted spelling of the same name.
    spellings = [name] + ([name.rsplit(".", 1)[-1]] if "." in name else [])
    patterns = [
        re.compile(r"(?<![A-Za-z0-9_.'])" + re.escape(spelling) + r"(?![A-Za-z0-9_.'])")
        for spelling in spellings
    ]

    def mentions(index: int) -> bool:
        return any(pattern.search(lines[index]) for pattern in patterns)

    def introduces(index: int) -> bool:
        """Does a declaration keyword introduce the name at or just above `index`?"""
        start = max(0, index - LOCATOR_WINDOW_BEFORE)
        for probe in range(index, start - 1, -1):
            stripped = lines[probe].lstrip()
            while stripped.startswith("@["):
                close = stripped.find("]")
                if close == -1:
                    break
                stripped = stripped[close + 1 :].lstrip()
            tokens = stripped.split()
            cursor = 0
            while cursor < len(tokens) and tokens[cursor] in DECLARATION_MODIFIERS:
                cursor += 1
            if cursor < len(tokens) and tokens[cursor] in DECLARATION_KEYWORDS:
                return True
        return False

    found: int | None = None
    if isinstance(recorded, int) and 1 <= recorded <= len(lines):
        window_end = min(len(lines), recorded + LOCATOR_WINDOW_AFTER)
        for probe in range(recorded - 1, window_end):
            if mentions(probe):
                found = probe + 1
                break
    if found is not None:
        result["status"] = "exact" if found == recorded else "in_window"
        result["resolved_line"] = found
    else:
        # Outside the recorded window, require a declaration keyword so that a
        # call site is never mistaken for the definition.
        for index in range(len(lines)):
            if mentions(index) and introduces(index):
                result["status"] = "drifted"
                result["resolved_line"] = index + 1
                break
        else:
            result["status"] = "declaration_missing"
            return result

    anchor = (result["resolved_line"] or 1) - 1
    signature: list[str] = []
    for probe in range(anchor, min(len(lines), anchor + 6)):
        signature.append(lines[probe].rstrip())
        if ":=" in lines[probe] or lines[probe].rstrip().endswith("by"):
            break
    result["signature"] = "\n".join(signature)

    # Walk back through the doc comment that introduces the declaration.
    doc: list[str] = []
    probe = anchor - 1
    while probe >= 0 and not lines[probe].strip():
        probe -= 1
    if probe >= 0 and lines[probe].strip().endswith("-/"):
        while probe >= 0:
            doc.append(lines[probe])
            if lines[probe].lstrip().startswith("/--"):
                break
            probe -= 1
        doc.reverse()
        body = "\n".join(doc)
        body = body.strip().removeprefix("/--").removesuffix("-/").strip()
        result["docstring"] = re.sub(r"\s+", " ", body)
    return result


def boundary_for(claim: dict[str, Any], claims: dict[str, Any]) -> dict[str, Any]:
    """Assemble the typed statement of where this claim stops."""
    taxonomy = claims.get("status_taxonomy", {})
    status = claim.get("status", "")
    open_props = [
        prop
        for prop in claims.get("remaining_open_propositions", [])
        if prop.get("open_target_claim") == claim.get("id")
    ]
    return {
        "status": status,
        "status_means": taxonomy.get(status, "status is outside the declared taxonomy"),
        "status_in_taxonomy": status in taxonomy,
        "remaining_open": open_props,
        "release_non_claims": claims.get("non_claims", []),
    }


def follow_claim(claim_id: str, claims: dict[str, Any]) -> dict[str, Any]:
    """Resolve one claim into source, receipts, and boundary."""
    for candidate in claims.get("claims", []):
        if candidate.get("id") == claim_id:
            claim = candidate
            break
    else:
        raise KeyError(claim_id)

    declarations = [resolve_declaration(dec) for dec in claim.get("declarations", [])]
    boundary = boundary_for(claim, claims)
    broken = [
        dec
        for dec in declarations
        if dec["status"] in {"module_missing", "declaration_missing", "drifted"}
    ]
    return {
        "id": claim_id,
        "label": claim.get("label"),
        "statement": claim.get("statement"),
        "paper_label": claim.get("paper_label"),
        "declarations": declarations,
        "release": claims.get("release", {}),
        "boundary": boundary,
        "verified": not broken and boundary["status_in_taxonomy"],
    }


def render_claim(report: dict[str, Any]) -> str:
    """Render one followed claim for a human or an agent reading stdout."""
    out: list[str] = []
    out.append(f"claim   {report['id']}")
    out.append(f"label   {report['label']}")
    boundary = report["boundary"]
    out.append(f"status  {boundary['status']} -- {boundary['status_means']}")
    out.append("")
    out.append("STATEMENT (what the public is told)")
    out.append(f"  {report['statement']}")
    out.append("")

    out.append(f"SOURCE ({len(report['declarations'])} declaration(s), re-resolved in this checkout)")
    for dec in report["declarations"]:
        mark = {"exact": "OK", "in_window": "OK", "drifted": "DRIFT", "declaration_missing": "MISSING", "module_missing": "NO MODULE"}[dec["status"]]
        line = dec["resolved_line"] or dec["recorded_line"]
        out.append(f"  [{mark}] {dec['name']}")
        out.append(f"         {dec['module']}:{line}")
        if dec["status"] == "drifted":
            out.append(f"         register says line {dec['recorded_line']}; source says {dec['resolved_line']}")
        if dec["signature"]:
            for sig_line in dec["signature"].splitlines():
                out.append(f"         | {sig_line}")
        if dec["docstring"]:
            doc = dec["docstring"]
            out.append(f"         doc: {doc[:400]}{'...' if len(doc) > 400 else ''}")
    out.append("")

    release = report["release"]
    formal = release.get("formal_source", {})
    out.append("RECEIPTS")
    out.append(f"  release          {release.get('version')} ({release.get('tag')}, {release.get('date')})")
    out.append(f"  formal source    {formal.get('ref', '?')[:12]} [{formal.get('ref_kind', '?')}]")
    out.append(f"  Lean toolchain   {release.get('lean_toolchain')}")
    if report["paper_label"]:
        out.append(f"  paper label      {report['paper_label']}")
    out.append("")

    out.append("WHERE THIS CLAIM STOPS")
    if not boundary["status_in_taxonomy"]:
        out.append(f"  !! status {boundary['status']!r} is not in the declared taxonomy")
    out.append(f"  ceiling: {boundary['status_means']}")
    if boundary["remaining_open"]:
        out.append("  open propositions still targeting this claim:")
        for prop in boundary["remaining_open"]:
            out.append(f"    - [{prop.get('status')}] {prop.get('statement')}")
    else:
        out.append("  no remaining open proposition is registered against this claim id")
    out.append("  this release does not claim:")
    for non in boundary["release_non_claims"]:
        out.append(f"    - {non.get('meaning')}")
    return "\n".join(out)


def verify_all_claims(claims: dict[str, Any]) -> dict[str, Any]:
    """Re-resolve every locator in the register. This is the drift gate."""
    problems: list[dict[str, Any]] = []
    declaration_count = 0
    for claim in claims.get("claims", []):
        report = follow_claim(claim["id"], claims)
        declaration_count += len(report["declarations"])
        for dec in report["declarations"]:
            if dec["status"] in {"module_missing", "declaration_missing", "drifted"}:
                problems.append({"claim": claim["id"], **dec})
        if not report["boundary"]["status_in_taxonomy"]:
            problems.append({"claim": claim["id"], "status": "status_outside_taxonomy"})

    known = {claim.get("id") for claim in claims.get("claims", [])}
    for prop in claims.get("remaining_open_propositions", []):
        target = prop.get("open_target_claim")
        if target and target not in known:
            problems.append({"claim": target, "status": "open_proposition_targets_unknown_claim"})

    return {
        "claim_count": len(claims.get("claims", [])),
        "declaration_count": declaration_count,
        "problems": problems,
        "verified": not problems,
    }


def run_gates(environment: dict[str, Any]) -> dict[str, Any]:
    """Run every committed check_*.py, classifying blocked gates as blocked."""
    scripts_dir = REPO_ROOT / "scripts"
    results: list[dict[str, Any]] = []
    for path in sorted(scripts_dir.glob("check_*.py")):
        name = path.name
        needed = OPTIONAL_TOOL_GATES.get(name)
        if needed and shutil.which(needed) is None:
            results.append({"gate": name, "outcome": "blocked", "reason": f"requires {needed}"})
            continue
        if environment["shallow_clone"] and name in HISTORY_DEPENDENT_GATES:
            results.append({"gate": name, "outcome": "blocked", "reason": "shallow clone"})
            continue
        completed = subprocess.run(
            [sys.executable, str(path)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        tail = (completed.stdout or completed.stderr).strip().splitlines()
        results.append(
            {
                "gate": name,
                "outcome": "pass" if completed.returncode == 0 else "fail",
                "returncode": completed.returncode,
                "last_line": tail[-1][:200] if tail else "",
            }
        )
    return {
        "results": results,
        "passed": sum(1 for r in results if r["outcome"] == "pass"),
        "failed": sum(1 for r in results if r["outcome"] == "fail"),
        "blocked": sum(1 for r in results if r["outcome"] == "blocked"),
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Follow a public claim to its source, receipts, and boundary.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "examples:\n"
            "  python3 scripts/verify_claims.py --list\n"
            "  python3 scripts/verify_claims.py --claim eb_full_support\n"
            "  python3 scripts/verify_claims.py --verify-all\n"
            "  python3 scripts/verify_claims.py --gates\n"
        ),
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--claim", metavar="ID", help="follow one claim end to end")
    mode.add_argument("--list", action="store_true", help="list every claim id and status")
    mode.add_argument("--verify-all", action="store_true", help="re-resolve every claim locator")
    mode.add_argument("--gates", action="store_true", help="run every committed check_*.py")
    parser.add_argument("--json", action="store_true", help="emit machine-readable output")
    args = parser.parse_args()

    claims = load_claims()
    environment = describe_environment(claims)

    if args.list or not (args.claim or args.verify_all or args.gates):
        rows = [
            {"id": c.get("id"), "status": c.get("status"), "label": c.get("label")}
            for c in claims.get("claims", [])
        ]
        if args.json:
            print(json.dumps({"environment": environment, "claims": rows}, indent=2))
        else:
            for block in environment["blocks"]:
                print(f"[environment] {block}")
            print(f"{len(rows)} claims in {CLAIMS_PATH.relative_to(REPO_ROOT)}\n")
            for row in rows:
                print(f"  {row['id']:<52} {row['status']}")
            print("\nFollow one:  python3 scripts/verify_claims.py --claim <id>")
        return 2 if environment["blocks"] else 0

    if args.claim:
        try:
            report = follow_claim(args.claim, claims)
        except KeyError:
            print(f"unknown claim id: {args.claim}", file=sys.stderr)
            print("list them with: python3 scripts/verify_claims.py --list", file=sys.stderr)
            return 2
        if args.json:
            print(json.dumps({"environment": environment, "claim": report}, indent=2))
        else:
            for block in environment["blocks"]:
                print(f"[environment] {block}\n")
            print(render_claim(report))
        return 0 if report["verified"] else 1

    if args.verify_all:
        report = verify_all_claims(claims)
        if args.json:
            print(json.dumps({"environment": environment, "verification": report}, indent=2))
        else:
            print(
                f"verify_claims: {report['claim_count']} claims, "
                f"{report['declaration_count']} declarations re-resolved against Lean source"
            )
            for problem in report["problems"]:
                print(f"  FAIL {problem}")
            if report["verified"]:
                print("every claim locator resolves and every status is inside the taxonomy")
        return 0 if report["verified"] else 1

    gates = run_gates(environment)
    if args.json:
        print(json.dumps({"environment": environment, "gates": gates}, indent=2))
    else:
        for block in environment["blocks"]:
            print(f"[environment] {block}")
        for result in gates["results"]:
            mark = {"pass": "PASS", "fail": "FAIL", "blocked": "BLOCKED"}[result["outcome"]]
            detail = result.get("reason") or result.get("last_line", "")
            print(f"  [{mark:<7}] {result['gate']:<42} {detail[:90]}")
        print(
            f"\n{gates['passed']} passed, {gates['failed']} failed, "
            f"{gates['blocked']} blocked by environment"
        )
    if gates["failed"]:
        return 1
    return 2 if gates["blocked"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
