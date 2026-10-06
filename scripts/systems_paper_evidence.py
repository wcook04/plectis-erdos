#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Bind the systems paper's historical claims to their evidence owner."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from publication_contract import normalize_latex_evidence


ROOT = Path(__file__).resolve().parent.parent
PAPER_PATH = ROOT / "paper" / "systems" / "claim-faithful-publication-systems-paper.tex"
EVIDENCE_PATH = ROOT / "docs" / "publication_evidence.json"
CLAIMS_PATH = ROOT / "docs" / "claims.json"
ERDOS_PROBLEMS_ROOT = ROOT / "lean/ErdosProblems.lean"

NUMBER_WORDS = {
    0: "zero",
    1: "one",
    2: "two",
    3: "three",
    4: "four",
    5: "five",
    6: "six",
    7: "seven",
    8: "eight",
    9: "nine",
    10: "ten",
}


def number_word(value: int) -> str:
    if value not in NUMBER_WORDS:
        raise ValueError(f"unsupported systems-paper evidence count: {value}")
    return NUMBER_WORDS[value]


def validate_systems_paper_evidence(
    paper_text: str | None = None,
    evidence: dict[str, Any] | None = None,
    claims: dict[str, Any] | None = None,
    erdos_problems_root: str | None = None,
) -> list[str]:
    """Check the paper's outcome and ceilings against the typed receipt."""
    if paper_text is None:
        paper_text = PAPER_PATH.read_text(encoding="utf-8")
    if "% SYSTEMS_PAPER_VERSION 2" in paper_text:
        if any(value is not None for value in (evidence, claims, erdos_problems_root)):
            return ["v2 evidence uses the source-bound ledger, not legacy override arguments"]
        from build_systems_paper_counts import pipeline_errors
        problems=validate_bound_paper(paper_text, ROOT)+pipeline_errors(paper_text, ROOT)
        historical=read_json(EVIDENCE_PATH)
        for key,label in historical.get("source",{}).items():
            if key.endswith("_label") and r"\label{"+label+"}" not in paper_text:
                problems.append("historical evidence label missing: "+label)
        return problems
    if evidence is None:
        evidence = json.loads(EVIDENCE_PATH.read_text(encoding="utf-8"))
    if claims is None:
        claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    if erdos_problems_root is None:
        erdos_problems_root = ERDOS_PROBLEMS_ROOT.read_text(encoding="utf-8")

    errors: list[str] = []
    normalized = normalize_latex_evidence(paper_text)
    # The record once named sec:failure after the paper renamed that section
    # sec:checks, and nothing noticed. Every source label must still exist.
    for key, label in sorted(evidence.get("source", {}).items()):
        if key.endswith("_label") and f"\\label{{{label}}}" not in paper_text:
            errors.append(f"publication evidence source.{key} names missing label {label}")
    evaluation = evidence.get("evaluation", {})
    summary = evaluation.get("summary", {})
    mutations = evaluation.get("mutations", [])
    post_repair = evidence.get("post_repair", {})
    provenance = evidence.get("provenance", {})

    total = summary.get("authored_mutation_count")
    rejected = summary.get("rejected_mutation_count")
    escaped_ids = summary.get("escaped_mutation_ids")
    if not isinstance(total, int) or not isinstance(rejected, int):
        errors.append("publication evidence lacks integer mutation totals")
    elif not isinstance(escaped_ids, list):
        errors.append("publication evidence lacks escaped mutation ids")
    else:
        if len(mutations) != total:
            errors.append("publication evidence mutation total disagrees with its matrix")
        if rejected + len(escaped_ids) != total:
            errors.append("publication evidence outcomes do not partition the mutation total")
        if len(escaped_ids) != 1:
            errors.append("systems paper prose currently supports exactly one escaped mutation")
        else:
            expected = (
                f"{number_word(rejected)} of the {number_word(total)} edits were "
                "rejected. one escaped"
            )
            if expected not in normalized:
                errors.append(
                    "systems paper historical outcome disagrees with publication evidence"
                )

    if provenance.get("raw_run_logs_registered") is False:
        if "the original run logs were not retained" not in normalized:
            errors.append("systems paper lost the original-run-log absence ceiling")

    if post_repair.get("other_original_mutations_rerun") is False:
        rerun_ids = post_repair.get("rerun_mutation_ids", [])
        if isinstance(total, int) and isinstance(rerun_ids, list):
            other_count = total - len(rerun_ids)
            expected = (
                f"the other {number_word(other_count)} edits were not rerun "
                "against the extended checklist"
            )
            if expected not in normalized:
                errors.append("systems paper lost the post-repair rerun ceiling")

    author_relationship = evaluation.get("protocol", {}).get(
        "mutation_author_relationship"
    )
    if author_relationship == "mutations_authored_by_checker_author":
        if "the edits were authored by the checker's author" not in normalized:
            errors.append("systems paper lost the mutation-author dependence ceiling")

    finite_claim = next(
        (
            claim
            for claim in claims.get("claims", [])
            if claim.get("id") == "certified_kill_instances"
        ),
        None,
    )
    if finite_claim is None:
        errors.append("claim registry lacks certified_kill_instances")
    else:
        declarations = finite_claim.get("declarations", [])
        final_declaration = declarations[-1] if declarations else {}
        if finite_claim.get("status") != "verified finite instance":
            errors.append("finite certificate claim lost verified-finite status")
        if re.search(
            r"every[^;]*t ≤ 82",
            str(finite_claim.get("bounded_domain", "")),
        ) is None:
            errors.append("finite certificate claim registry does not own the t ≤ 82 band")
        if len(declarations) != 6:
            errors.append("finite certificate claim must name exactly six declarations")
        if (
            final_declaration.get("name") != "exists_diagonalKill_le_82"
            or final_declaration.get("module")
            != "ErdosProblems/Skip/LadderT67.lean"
        ):
            errors.append("finite certificate claim does not terminate at the t ≤ 82 theorem")
        if re.search(r"t\\le\s*82", normalized) is None:
            errors.append("systems paper no longer states the registered t ≤ 82 band")
        if r"no \(t=83\) or cofinal claim" not in normalized:
            errors.append("systems paper lost the finite-band ceiling")
        if "import ErdosProblems.Skip.LadderT67" not in erdos_problems_root:
            errors.append("supported ErdosProblems root does not import the t ≤ 82 theorem")

    return errors


def reflow_tolerant_replace(
    source: str, phrase: str, replacement: str, count: int = 1
) -> str:
    """Replace ``phrase`` treating each gap between words as any whitespace.

    LaTeX paragraphs get rewrapped freely, so a fixture anchored on a literal
    line break stops mutating the moment the text reflows: the "mutated" copy
    becomes byte-identical to the source and the check can no longer fail.
    That is the silent-decay failure the paper itself warns about, and it has
    happened here once.  Matching whitespace flexibly keeps every fixture armed
    across rewrapping, and can only widen what the anchor finds, never narrow
    it.  A phrase that is genuinely gone still leaves the source unchanged, so
    the ``_anchor_missing`` detection below is preserved.
    """
    pattern = r"\s+".join(re.escape(word) for word in phrase.split())
    return re.sub(pattern, lambda _match: replacement, source, count=count)


def mutation_fixture_failures() -> list[str]:
    """Ensure known paper/evidence disagreements remain rejectable."""
    source = PAPER_PATH.read_text(encoding="utf-8")
    if "% SYSTEMS_PAPER_VERSION 2" in source:
        unit=SENTENCE.search(source)
        specimens={
            "changed_sentence":source.replace(unit.group(2),unit.group(2)+" A fabricated gain.",1),
            "historical_count_inverted":source.replace(r"\newcommand{\HistoricalRejected}{nine}",r"\newcommand{\HistoricalRejected}{ten}",1),
            "original_logs_claimed_retained":source.replace("the original run logs were not retained","the original run logs were retained",1),
            "independence_inflated":source.replace("the checker's author","an independent auditor",1),
            "missing_return_boundary":reflow_tolerant_replace(
                source,
                "No independent reader study, adoption by another laboratory, "
                "discovery-rate comparison or measured reduction in review cost is reported.",
                "A comparative reader gain is established.",
            ),
            "unbound_body":source.replace(AUDIT_END,"A new unsupported assertion.\n"+AUDIT_END,1),
            "duplicate_sentence":source.replace(unit.group(),unit.group()+"\n"+unit.group(),1),
            "missing_historical_label":source.replace(r"\label{sec:checks}",r"\label{sec:failure}",1),
        }
        return [name+("_anchor_missing" if mutated==source else "_escaped")
                for name,mutated in specimens.items()
                if mutated==source or not validate_systems_paper_evidence(mutated)]

    logs_retained = reflow_tolerant_replace(
        source,
        "original run logs were not retained",
        "original run logs were retained",
        count=0,
    )
    fixtures = {
        "historical_outcome_inverted": reflow_tolerant_replace(
            source,
            "nine of the ten edits were rejected",
            "all ten edits were rejected",
        ),
        "original_logs_claimed_retained": reflow_tolerant_replace(
            logs_retained,
            "Original run logs were not retained",
            "Original run logs were retained",
            count=0,
        ),
        "post_repair_rerun_ceiling_removed": reflow_tolerant_replace(
            source,
            "The other nine edits",
            "The other edits",
        ),
        "mutation_author_dependence_removed": reflow_tolerant_replace(
            source,
            "The edits were authored by the checker's author",
            "The edits were independently authored",
        ),
        "finite_band_regressed_to_64": re.sub(
            r"t\\le\s*82",
            r"t\\le64",
            source,
        ),
        "finite_band_ceiling_removed": reflow_tolerant_replace(
            source,
            r"no \(t=83\) or cofinal claim",
            "a cofinal claim",
        ),
        "evidence_section_label_stale": source.replace(
            r"\label{sec:checks}",
            r"\label{sec:failure}",
        ),
    }
    failures: list[str] = []
    for fixture_id, mutated in fixtures.items():
        if mutated == source:
            failures.append(f"{fixture_id}_anchor_missing")
            continue
        if not validate_systems_paper_evidence(paper_text=mutated):
            failures.append(fixture_id)
    return failures


def legacy_main() -> int:
    errors = validate_systems_paper_evidence()
    fixture_failures = mutation_fixture_failures() if not errors else []
    if errors or fixture_failures:
        print(
            "systems_paper_evidence: "
            f"{len(errors)} baseline failure(s), "
            f"{len(fixture_failures)} fixture failure(s)"
        )
        for error in errors:
            print(f"  FAIL {error}")
        for fixture in fixture_failures:
            print(f"  FAIL fixture did not reject: {fixture}")
        return 1
    print(
        "systems_paper_evidence: central claim, historical outcome, and "
        "evidence ceilings match; seven opposing fixtures reject"
    )
    return 0




AUDIT_BEGIN = "% BEGIN audited_body"
AUDIT_END = "% END audited_body"
SENTENCE = re.compile(r"^% SENTENCE ([A-Za-z0-9.-]+)\n(.*?)\n% END SENTENCE \1[ \t]*$", re.M | re.S)
KINDS = {"implemented", "reported", "proposed", "method", "literature", "measured"}


def sha256(data: bytes) -> str:
    import hashlib
    return hashlib.sha256(data).hexdigest()


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_unique_object)


def safe_source(root: Path, relative: str) -> Path:
    from pathlib import PurePosixPath
    p = PurePosixPath(relative)
    if not relative or p.is_absolute() or ".." in p.parts or str(p) != relative:
        raise ValueError(f"unsafe source path: {relative}")
    target = root / relative
    for prefix in [target, *target.parents]:
        if prefix == root:
            break
        if prefix.is_symlink():
            raise ValueError(f"symlink source: {relative}")
    if not target.is_file():
        raise ValueError(f"missing source: {relative}")
    return target


def _balanced_argument(text: str, start: int) -> int:
    """Return first position after a brace argument; reject malformed structure."""
    if start >= len(text) or text[start] != "{":
        raise ValueError("expected braced structural argument")
    depth = 1
    i = start+1
    while i < len(text):
        if text[i] == "\\":
            i += 2
            continue
        if text[i] == "{": depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0: return i+1
        i += 1
    raise ValueError("unclosed structural argument")


def uncovered_text(text: str) -> str:
    """Permit structure only outside bound prose; includes/custom macros fail.

    This is a deliberately narrow authored-TeX contract, not a TeX interpreter.
    All emitted prose (including captions, if added) belongs inside an audited
    unit. Preamble/style and bibliography metadata are outside this inventory.
    """
    text = SENTENCE.sub("", text)
    text = re.sub(r"(?m)^%[^\n]*", "", text)
    allowed = {"section", "subsection", "paragraph", "label", "papersectiontarget", "begin", "end"}
    remaining=[];i=0
    while i < len(text):
        if text[i].isspace(): i+=1;continue
        match = re.match(r"\\([A-Za-z]+)\*?", text[i:])
        if not match:
            remaining.append(text[i:]);break
        name=match.group(1);end=i+match.end()
        if name in {"appendix", "clearpage", "small", "normalsize", "maketitle"}:
            i=end;continue
        if name not in allowed:
            remaining.append(text[i:]);break
        try: endarg=_balanced_argument(text,end)
        except ValueError:
            remaining.append(text[i:]);break
        if name in {"begin","end"} and text[end+1:endarg-1] not in {"abstract"}:
            remaining.append(text[i:]);break
        i=endarg
    return "".join(remaining).strip()


def bound_units(text: str) -> tuple[list[dict[str, Any]], list[str]]:
    errors=[]
    if text.count(AUDIT_BEGIN)!=1 or text.count(AUDIT_END)!=1:
        return [], ["one audited body is required"]
    start=text.index(AUDIT_BEGIN)+len(AUDIT_BEGIN);stop=text.index(AUDIT_END)
    if stop < start: return [], ["audited body order is invalid"]
    body=text[start:stop]
    units=[{"id":m.group(1),"text":m.group(2),
            "line":text[:start+m.start()].count("\n")+2} for m in SENTENCE.finditer(body)]
    if len(units)!=len({u["id"] for u in units}): errors.append("duplicate sentence id")
    if len(units)!=len(re.findall(r"(?m)^% SENTENCE ",body)):
        errors.append("malformed sentence boundary")
    if not units:errors.append("empty sentence inventory")
    leftover=uncovered_text(body)
    if leftover:errors.append("unbound body text: "+leftover[:120].replace("\n"," "))
    # Prevent hiding unaudited prose between the document start/end and our scope.
    doc=text.find(r"\begin{document}")
    bibliography=text.find(r"\begin{thebibliography}",stop)
    if doc<0 or bibliography<0:errors.append("missing document or bibliography boundary")
    else:
        pre=text[doc+len(r"\begin{document}"):text.index(AUDIT_BEGIN)]
        post=text[stop+len(AUDIT_END):bibliography]
        if uncovered_text(pre):errors.append("unbound prose before audited body")
        if uncovered_text(post):errors.append("unbound prose after audited body")
    bib_end=text.find(r"\end{thebibliography}",bibliography)
    doc_end=text.find(r"\end{document}",bib_end)
    if bib_end<0 or doc_end<0:
        errors.append("missing closing bibliography or document boundary")
    elif uncovered_text(text[bib_end+len(r"\end{thebibliography}"):doc_end]):
        errors.append("unbound prose after bibliography")
    if text.count(r"\begin{document}")!=1 or text.count(r"\end{document}")!=1:
        errors.append("document boundaries must be unique")
    return units,errors


def validate_bound_paper(paper_text: str, root: Path = ROOT,
                         ledger: dict[str, Any] | None = None) -> list[str]:
    """Check traceability and evidence freshness; semantic entailment stays reviewed.

    A recorded excerpt is evidence of a supplied snapshot, not a fresh execution.
    This checker never executes commands listed by a paper or its source ledger.
    """
    errors=[]
    try:
        if ledger is None:ledger=read_json(root/"docs/systems_paper_sentences.json")
        if not isinstance(ledger,dict):return ["sentence ledger must be an object"]
        if ledger.get("schema")!="systems-paper-sentences/2":return ["wrong sentence ledger schema"]
        units,problems=bound_units(paper_text);errors.extend(problems)
        rows=ledger.get("sentences",[])
        if len(rows)!=len({r["id"] for r in rows}):errors.append("duplicate ledger sentence id")
        by_id={r["id"]:r for r in rows}
        if set(by_id)!={u["id"] for u in units}:errors.append("paper/ledger sentence inventories differ")
        sources=ledger.get("sources",[])
        if len(sources)!=len({r["id"] for r in sources}):errors.append("duplicate evidence source id")
        source_map={r["id"]:r for r in sources};cache={}
        for source in sources:
            path=safe_source(root,source["path"])
            if source["path"] not in cache:cache[source["path"]]=path.read_bytes()
            data=cache[source["path"]]
            if sha256(data)!=source["sha256"]:errors.append(f"source digest changed: {source['id']}")
            lines=data.decode("utf-8").splitlines(keepends=True)
            a,b=source["start_line"],source["end_line"]
            if not isinstance(a,int) or not isinstance(b,int) or not 1<=a<=b<=len(lines):
                errors.append(f"source range invalid: {source['id']}");continue
            excerpt="".join(lines[a-1:b]).encode()
            if sha256(excerpt)!=source["excerpt_sha256"]:errors.append(f"source span changed: {source['id']}")
        for unit in units:
            row=by_id.get(unit["id"])
            if row is None:continue
            if row.get("statement_sha256")!=sha256(unit["text"].encode()):
                errors.append(f"sentence changed: {unit['id']}")
            if row.get("class") not in KINDS:errors.append(f"unknown evidence class: {unit['id']}")
            refs=row.get("evidence_refs",[])
            if not refs or any(ref not in source_map for ref in refs):
                errors.append(f"missing evidence binding: {unit['id']}")
            if not isinstance(row.get("warrant"),str) or not row["warrant"].strip():
                errors.append(f"missing reviewed warrant: {unit['id']}")
            if row.get("class")=="implemented" and not any(
                source_map.get(ref,{}).get("kind")=="source" and
                source_map.get(ref,{}).get("path","").endswith((".py",".lean")) for ref in refs):
                errors.append(f"implementation lacks code binding: {unit['id']}")
            if row.get("class")=="measured" and not any(source_map.get(ref,{}).get("kind")=="run" for ref in refs):
                errors.append(f"measurement lacks run receipt: {unit['id']}")
        # Cheap house rules; they do not score clarity or mathematical importance.
        body="\n".join(u["text"] for u in units)
        if "—" in body or "---" in body:errors.append("em dash in paper body")
        if re.search(r"\bnot\b[^.!?]{0,100}\bbut\b",body,re.I):errors.append("not-X-but-Y construction")
    except (OSError, ValueError, KeyError, TypeError, UnicodeError, AttributeError) as exc:
        errors.append(f"sentence evidence error: {exc}")
    return errors


def main() -> int:
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper",type=Path,default=PAPER_PATH)
    parser.add_argument("--root",type=Path,default=ROOT)
    parser.add_argument("--ledger",type=Path)
    args=parser.parse_args()
    try:
        text=args.paper.read_text(encoding="utf-8")
        if "% SYSTEMS_PAPER_VERSION 2" not in text and args.ledger is None:
            return legacy_main()
        ledger=read_json(args.ledger) if args.ledger else None
        errors=validate_bound_paper(text,args.root,ledger)
        if errors:
            for error in errors:print("FAIL "+error)
            return 1
        units,_=bound_units(text)
        print(f"systems-paper sentence evidence: {len(units)} units bound; all source digests match")
        print("Boundary: byte binding and authored warrants, not automatic semantic entailment or independent review")
        return 0
    except (OSError,ValueError,KeyError,TypeError) as exc:
        print("FAIL "+str(exc));return 2


if __name__ == "__main__":
    raise SystemExit(main())
