#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Write or check the record counts the systems paper states, from one snapshot.

Every count ``paper/systems/claim-faithful-publication-systems-paper.tex``
gives for the paper-to-Lean ledger, the module graph, the claim registry, the
argument frontier and the research record is a macro in the paper's
``generated_record_count_macros`` region, so no count is typed by hand and
none can drift from the files it describes. The values come from one reading
of the checkout:

* the ledger summary in ``docs/paper_lean_coverage.json``;
* the module graph and the claims in ``docs/claims.json``;
* the Lean tree recorded by ``docs/argument_frontier.json``, whose
  manifest-derivable counts in the paper's
  ``generated_argument_frontier_macros`` region are checked too;
* the research record: the journal is read up to the head the region names, so
  appending events never moves a stated count, while the relation and contrast
  counts are read live.

The sentence the paper states after the relation counts is checked against
them: it may say that every relation row is attested only when every row is,
and that the atlas does not yet list some certificates only when it does not.

``--write`` rewrites the region (naming the current journal head unless
``--journal-head`` names an earlier one); the default checks it and exits 1 on
any difference. The argument-graph totals come from an export of an earlier
Lean tree that is not committed, so this script leaves them alone; the paper
names that tree beside them.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

import contrast_ledger  # noqa: E402
import research_record  # noqa: E402
import relation_registry  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper" / "systems" / "claim-faithful-publication-systems-paper.tex"
BEGIN = "% BEGIN generated_record_count_macros"
END = "% END generated_record_count_macros"
FRONTIER_BEGIN = "% BEGIN generated_argument_frontier_macros"
FRONTIER_END = "% END generated_argument_frontier_macros"
WORDS = ("zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten",
         "eleven", "twelve")
HEAD_LENGTH = 12
# The fixed prose that follows the relation counts, in each of its two forms.
RELATIONS_ALL = r"All \Relations{} relation rows are attested"
RELATIONS_SOME = "does not yet list the others' certificates"


ROUND_SIX = "docs/research-commons/rounds/round6"


def word(n: int) -> str:
    return WORDS[n] if 0 <= n < len(WORDS) else f"{n:,}"


def word_list(numbers: list[int]) -> str:
    """``[5, 6, 8]`` as ``five, six and eight``."""
    words = [word(n) for n in numbers]
    return words[0] if len(words) == 1 else ", ".join(words[:-1]) + " and " + words[-1]


class CountError(ValueError):
    """The checkout cannot supply a count the paper states."""


def _json(root: Path, relative: str) -> Any:
    return json.loads((root / relative).read_text(encoding="utf-8"))


def region_values(text: str, begin: str, end: str) -> dict[str, str]:
    start, stop = text.find(begin), text.find(end)
    if start < 0 or stop < start or text.count(begin) != 1 or text.count(end) != 1:
        raise CountError(f"the paper needs exactly one region {begin!r} ... {end!r}")
    return dict(re.findall(r"\\newcommand\{\\([A-Za-z]+)\}\{([^{}]*)\}", text[start:stop]))


def ledger_values(root: Path) -> dict[str, Any]:
    summary = _json(root, "docs/paper_lean_coverage.json")["summary"]
    lean, comparator = summary["lean"], summary["comparator"]
    formal = lean["exact"] + lean["exact_or_stronger"]
    # The paper says Comparator compared some of the exact and specialising
    # rows and queued the rest; refuse a ledger for which that is false.
    if comparator.get("compared", 0) + comparator.get("pending", 0) != formal:
        raise CountError("compared plus pending Comparator rows differ from the exact and specialising rows")
    if sum(lean.values()) != summary["rows"]:
        raise CountError("the ledger's Lean classes do not partition its rows")
    return {
        "LedgerRows": summary["rows"],
        "LedgerExact": lean["exact"],
        "LedgerSpecialising": lean["exact_or_stronger"],
        "LedgerNamedInput": lean["modulo_named_input"],
        "LedgerNoLean": lean["none"],
        "LedgerWithLean": summary["rows"] - lean["none"],
        "LedgerFormal": formal,
        "LedgerCompared": comparator.get("compared", 0),
        "LedgerQueued": comparator.get("pending", 0),
    }


def registry_values(root: Path) -> dict[str, Any]:
    claims = _json(root, "docs/claims.json")
    # The statuses the claims carry, which the paper states ("in eight
    # statuses"); a taxonomy status no claim uses is not counted.
    statuses = len({claim["status"] for claim in claims["claims"]})
    graph = claims["machine_readable_paper"]["module_graph"]
    return {
        # The module graph's nodes plus its library root files, which are not nodes.
        "LeanModules": len(graph["nodes"]) + 1 + len(graph.get("additional_roots", [])),
        "Claims": len(claims["claims"]),
        "ClaimObligations": len(claims["remaining_open_propositions"]),
        # Printed in words: "in eight statuses".
        "ClaimStatuses": word(statuses),
    }


def frontier_values(root: Path) -> dict[str, Any]:
    """The frontier's Lean tree, and the region counts that its manifest alone determines."""
    manifest = _json(root, "docs/argument_frontier.json")
    rows = [r for problem_rows in manifest["rows"].values() for r in problem_rows]
    inputs = manifest.get("named_inputs", [])
    return {
        "tree": manifest["source"]["lean_tree"][:8],
        "counts": {
            "AFModules": len(manifest["modules"]),
            "AFPaperTheorems": len({r["theorem"] for r in rows}),
            "AFIdle": sum(1 for r in rows if r["operation"] == "idle"),
            "AFWeakened": sum(1 for r in rows if r["operation"] == "weakening"),
            "AFFactored": sum(1 for r in rows if r["operation"] == "factored"),
            "AFFactoredLibrary": len({n for r in rows if r["operation"] == "factored"
                                      for n in r.get("helpers", [])}),
            "AFCuts": sum(len(r.get("frontier_cuts", [])) for r in rows),
            "AFNamedInputs": len(inputs),
            "AFNamedInputUses": sum(len(e["consumers"]) for e in inputs),
            "AFNamedInputsTraced": sum(1 for e in inputs
                                       if any(c.get("levels") for c in e["consumers"])),
        },
    }


def journal_values(root: Path, head: str | None) -> dict[str, Any]:
    """Counts over the journal prefix that ends at ``head`` (the whole journal when None)."""
    events = research_record.read_events(research_record.journal_path(root))
    if not events:
        raise CountError("the research-record journal is empty")
    if head is None:
        prefix = events
    else:
        ends = [i for i, e in enumerate(events) if e["event_sha"].startswith(head)]
        if len(ends) != 1:
            raise CountError(f"journal head {head} names {len(ends)} events")
        prefix = events[: ends[0] + 1]
    kinds = [e["kind"] for e in prefix]
    reviews: dict[str, str] = {}
    for event in prefix:
        if event["kind"] == "review_recorded":
            reviews[event["detail"]["return_id"]] = event["detail"]["disposition"]
    returns = kinds.count("return_received")
    return {
        "JournalHead": prefix[-1]["event_sha"][:HEAD_LENGTH],
        "Rounds": kinds.count("round_opened"),
        "RoundsSealed": kinds.count("round_sealed"),
        "Returns": returns,
        "ReturnsAdmitted": sum(1 for d in reviews.values() if d == "admitted_for_integration"),
        "ReturnsUnreviewed": returns - len(reviews),
    }


def live_record_values(root: Path) -> dict[str, Any]:
    report = relation_registry.check(root)
    if not report.get("ok", False):
        raise CountError("relation_registry.py check fails; fix the registry before stating its counts")
    contrasts = _json(root, "docs/research-commons/record/contrasts.json")["rows"]
    # The contrast gate over the published round-six answers, which are exact
    # copies of the returns; the paper states these as an in-sample exercise.
    answers = sorted((root / ROUND_SIX).glob("return-*.md"))
    if not answers:
        raise CountError(f"no published answers under {ROUND_SIX}")
    flags = [len(contrast_ledger.triggered(contrasts, text=a.read_text(encoding="utf-8"))) for a in answers]
    return {
        "Relations": len(report["rows"]),
        "RelationsAttested": report["counts"].get("attested", 0),
        "Contrasts": len(contrasts),
        "ContrastGateFlags": word_list(flags),
    }


def expected_values(root: Path, head: str | None) -> dict[str, Any]:
    values: dict[str, Any] = {}
    values.update(ledger_values(root))
    values.update(registry_values(root))
    values["FrontierTree"] = frontier_values(root)["tree"]
    values.update(journal_values(root, head))
    values.update(live_record_values(root))
    return values


def render(values: dict[str, Any]) -> str:
    lines = [BEGIN]
    for name, value in values.items():
        rendered = f"{value:,}" if isinstance(value, int) else str(value)
        lines.append(rf"\newcommand{{\{name}}}{{{rendered}}}")
    lines.append(END)
    return "\n".join(lines)


def replace_region(text: str, region: str) -> str:
    region_values(text, BEGIN, END)
    start, stop = text.find(BEGIN), text.find(END)
    return text[:start] + region + text[stop + len(END):]


def _expected_region(root: str, head: str) -> str:
    # A root path and journal head do not identify mutable ledger/registry bytes.
    return render(expected_values(Path(root), head))


def errors(text: str, root: Path = ROOT) -> list[str]:
    """Differences between the paper's generated regions and the checkout."""
    try:
        stated = region_values(text, BEGIN, END)
        head = stated.get("JournalHead")
        if not head:
            return ["the record-count region names no journal head"]
        expected = _expected_region(str(root), head)
        frontier = frontier_values(root)
        frontier_stated = region_values(text, FRONTIER_BEGIN, FRONTIER_END)
    except (CountError, OSError, KeyError, ValueError, research_record.RecordError) as exc:
        return [str(exc)]
    found: list[str] = []
    want = region_values(expected, BEGIN, END)
    for name in sorted(set(want) | set(stated)):
        if want.get(name) != stated.get(name):
            found.append(f"\\{name}: the paper says {stated.get(name)!r}, the checkout gives {want.get(name)!r}")
    for name, value in frontier["counts"].items():
        if frontier_stated.get(name) != f"{value:,}":
            found.append(f"\\{name}: the paper says {frontier_stated.get(name)!r}, "
                         f"docs/argument_frontier.json gives {value:,}")
    prose = " ".join(text.split())
    every_row = want.get("Relations") == want.get("RelationsAttested")
    if every_row and RELATIONS_SOME in prose:
        found.append("every relation row is attested, but the paper says the atlas does not yet list "
                     "the others' certificates")
    if not every_row and RELATIONS_ALL in prose:
        found.append(f"{want.get('RelationsAttested')} of {want.get('Relations')} relation rows are attested, "
                     "but the paper says all are")
    if not (RELATIONS_SOME in prose or RELATIONS_ALL in prose):
        found.append("the paper states the relation counts without the sentence that says which rows are attested")
    return found



PIPELINE_BEGIN = "% BEGIN generated_pipeline_counts"
PIPELINE_END = "% END generated_pipeline_counts"
VERSION_TWO = "% SYSTEMS_PAPER_VERSION 2"


def pipeline_values(root: Path) -> dict[str, Any]:
    """Inventory, never a claim that the compiler/kernel/model was rerun.

    This uses the existing ledger/registry/frontier/journal owners. Counts of
    publication occurrences, unique claims and journal returns remain separate.
    The old uncommitted argument-export totals are deliberately not imported.
    """
    values = ledger_values(root)
    values.update(registry_values(root))
    values.update(journal_values(root, None))
    corpus = _json(root, "docs/papers/corpus.json")["papers"]
    source = _json(root, "docs/problem_index_source.json")["problems"]
    values.update({
        "ProblemWorlds": len(source),
        "RegisteredPapers": len(corpus),
        "ShortPapers": sum(p["form"] == "Problem note" for p in corpus),
        "LongRecords": sum(p["form"] == "Reasoning surface" for p in corpus),
    })
    historical = _json(root, "docs/publication_evidence.json")
    summary = historical["evaluation"]["summary"]
    total = summary["authored_mutation_count"]
    rejected = summary["rejected_mutation_count"]
    escaped = len(summary["escaped_mutation_ids"])
    if rejected + escaped != total or len(historical["evaluation"]["mutations"]) != total:
        raise CountError("historical mutation outcomes do not partition the recorded cases")
    values.update({"HistoricalEdits": word(total), "HistoricalRejected": word(rejected),
                   "HistoricalEscaped": word(escaped),
                   "HistoricalNotRerun": word(total-len(historical["post_repair"]["rerun_mutation_ids"]))})
    return values


def pipeline_render(values: dict[str, Any]) -> str:
    return render(values).replace(BEGIN, PIPELINE_BEGIN).replace(END, PIPELINE_END)


def pipeline_errors(text: str, root: Path = ROOT) -> list[str]:
    """Recompute once per invocation; missing, duplicate and extra macros fail."""
    try:
        stated = region_values(text, PIPELINE_BEGIN, PIPELINE_END)
        region = text[text.index(PIPELINE_BEGIN):text.index(PIPELINE_END)]
        names = re.findall(r"\\newcommand\{\\([A-Za-z]+)\}", region)
        if len(names) != len(set(names)):
            return ["duplicate pipeline count macro"]
        expected = region_values(pipeline_render(pipeline_values(root)), PIPELINE_BEGIN, PIPELINE_END)
    except (OSError, ValueError, KeyError, TypeError, research_record.RecordError) as exc:
        return [f"pipeline source error: {exc}"]
    return [f"\\{name}: paper={stated.get(name)!r}; source={expected.get(name)!r}"
            for name in sorted(set(stated) | set(expected)) if stated.get(name) != expected.get(name)]


def pipeline_snapshot(root: Path) -> dict[str, Any]:
    """A content-addressed reproduction recipe for the inventory table."""
    import hashlib
    paths = ["docs/paper_lean_coverage.json", "docs/claims.json",
             "docs/problem_index_source.json", "docs/papers/corpus.json",
             "docs/publication_evidence.json",
             research_record.journal_path(root).relative_to(root).as_posix()]
    return {"schema": "systems-paper-counts/2", "classification": "inventory_and_reported_history",
            "builder": "scripts/build_systems_paper_counts.py::pipeline_values",
            "values": pipeline_values(root),
            "inputs": [{"path": name, "sha256": hashlib.sha256((root/name).read_bytes()).hexdigest()}
                       for name in paths],
            "limits": ["Rows count publication occurrences, not distinct theorems.",
                       "Compiled-target and recorded Comparator statuses are not fresh kernel runs.",
                       "Journal returns are not an independent experimental sample."]}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--write", action="store_true", help="rewrite the appropriate generated region")
    parser.add_argument("--journal-head", help="legacy mode: count an earlier journal prefix")
    parser.add_argument("--paper", type=Path, default=PAPER)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--snapshot", type=Path, help="write the v2 inventory and source digests as JSON")
    args = parser.parse_args(argv)
    try:
        text = args.paper.read_text(encoding="utf-8")
        v2 = VERSION_TWO in text
        if args.write:
            if v2:
                if args.journal_head:
                    raise CountError("v2 inventory counts the attached journal; no implicit historical prefix")
                region_values(text, PIPELINE_BEGIN, PIPELINE_END)
                start, end = text.index(PIPELINE_BEGIN), text.index(PIPELINE_END)+len(PIPELINE_END)
                text = text[:start] + pipeline_render(pipeline_values(args.root)) + text[end:]
            else:
                text = replace_region(text, render(expected_values(args.root, args.journal_head)))
            args.paper.write_text(text, encoding="utf-8")
        found = pipeline_errors(text, args.root) if v2 else errors(text, args.root)
        if found:
            print("systems-paper counts: " + "; ".join(found), file=sys.stderr)
            return 1
        if args.snapshot:
            args.snapshot.parent.mkdir(parents=True, exist_ok=True)
            args.snapshot.write_text(json.dumps(pipeline_snapshot(args.root), indent=2)+"\n", encoding="utf-8")
    except (OSError, ValueError, KeyError, TypeError, research_record.RecordError) as exc:
        print(f"systems-paper counts: {exc}", file=sys.stderr)
        return 2
    print("systems-paper counts: all generated values match their source owners")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
