#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build public scholarly-source attribution views from an authored registry."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import urlsplit, urlunsplit
from urllib.parse import quote

import lean_source
import assemble_reasoning_surfaces

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "docs/research-commons/source-attributions.json"
JSON_OUTPUT = ROOT / "docs/research-commons/source-attribution-index.json"
MARKDOWN_OUTPUT = ROOT / "docs/research-commons/SOURCE_ATTRIBUTIONS.md"
PAPER_CORPUS = ROOT / "docs/papers/corpus.json"
OUTPUT_SCHEMA = "research-source-attribution-index/1"
KINDS = {"literature", "software", "website_contribution", "catalogue", "correspondence"}
STATES = {
    "source_verified", "existing_source_closure", "bibliography_only",
    "implemented_advice", "recommendation_only", "external_claim_unverified",
}
LEAN_REVIEW_DISPOSITIONS={"reviewed_citation_or_comparison","not_bibliographic","unresolved"}
SOURCE_FIELDS = {
    "id", "kind", "title", "authors", "urls", "problems", "source_locators",
    "artifact_links", "relation", "verification_state", "bibliography_keys",
    "identity_disclosure", "confirmation_status",
    "mapping_status", "mapping_note", "verification_scope",
    "paper_reported_locators", "publication_years", "year",
}
LOCATOR_FIELDS={"url","locator","evidence_path","line_start","line_end","expected_text","excerpt_sha256"}
ARTIFACT_FIELDS={"path","line_start","line_end","expected_text","excerpt_sha256"}
PATH_RE = re.compile(r"^[^/\\](?:.*[^/\\])?$")
URL_RE = re.compile(r"https://[^\s}\]>)]+")
REF_RE = re.compile(r"(?i)\b(?:arxiv\s*:\s*(?:[a-z.-]+/\d{7}|\d{4}\.\d{4,5})(?:v\d+)?|doi\s*:\s*10\.\d{4,9}/[^\s,;)}]+)")
EMAIL_RE = re.compile(r"(?i)(?:mailto:|\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}\b)")
ABSOLUTE_PRIVATE_PATH_RE = re.compile(r"(?:^|[\s`])(?:/Users/|/home/|[A-Za-z]:\\\\)")
CITE_RE = re.compile(r"\\(?:cite|citep|citet|citealp|citealt|citeauthor|citeyear|nocite)\s*(?:\[[^\]]*\]\s*){0,2}\{([^}]*)\}", re.S)
BIB_RE = re.compile(r"\\bibitem(?:\s*\[[^\]]*\])?\s*\{([^}]+)\}", re.S)
INPUT_RE = re.compile(r"\\(?:input|include)\s*\{([^}]+)\}")
GENERIC_REFERENCE_TOKENS={"lean","lean4","mathlib","main","theorem","lemma","proof","source","paper","appendix","reference","references"}


class AttributionError(ValueError):
    pass


_FILE_BYTES: dict[Path, bytes] = {}


def file_bytes(path: Path) -> bytes:
    if path not in _FILE_BYTES: _FILE_BYTES[path]=path.read_bytes()
    return _FILE_BYTES[path]


def file_text(path: Path) -> str:
    return file_bytes(path).decode("utf-8")


def canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()


def digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(file_bytes(path)).hexdigest()


def normalized_url(value: str) -> str:
    parts=urlsplit(value.strip())
    # Fragments are identity-bearing on forums and other anchored public
    # records: two contributors can have distinct posts on one thread URL.
    return urlunsplit((parts.scheme.casefold(),parts.netloc.casefold(),parts.path.rstrip("/") or "/",parts.query,parts.fragment))


def safe_path(root: Path, value: str, *, label: str) -> Path:
    if not isinstance(value, str) or not PATH_RE.fullmatch(value) or ".." in Path(value).parts:
        raise AttributionError(f"{label}: unsafe repository-relative path")
    path = root / value
    if path.is_symlink() or not path.is_file():
        raise AttributionError(f"{label}: path is not a readable regular file: {value}")
    try:
        path.resolve().relative_to(root.resolve())
    except ValueError as exc:
        raise AttributionError(f"{label}: path escapes repository") from exc
    return path


def validate_range(path: Path, row: dict[str, Any], *, label: str) -> tuple[int, int]:
    start, end = row.get("line_start"), row.get("line_end")
    if not isinstance(start, int) or isinstance(start, bool) or start < 1:
        raise AttributionError(f"{label}: line_start must be a positive integer")
    if not isinstance(end, int) or isinstance(end, bool) or end < start:
        raise AttributionError(f"{label}: line_end must be >= line_start")
    lines=file_text(path).splitlines(); count=len(lines)
    if end > count:
        raise AttributionError(f"{label}: line range exceeds {path}")
    excerpt = "\n".join(lines[start - 1:end]) + "\n"
    if "expected_text" in row and (not isinstance(row["expected_text"], str) or row["expected_text"] not in excerpt):
        raise AttributionError(f"{label}: expected_text is absent from selected lines")
    expected_digest = row.get("excerpt_sha256")
    actual_digest = "sha256:" + hashlib.sha256(excerpt.encode()).hexdigest()
    if expected_digest is not None and expected_digest != actual_digest:
        raise AttributionError(f"{label}: excerpt_sha256 does not match selected lines")
    return start, end


def excerpt_digest(path: Path, start: int, end: int) -> str:
    excerpt = "\n".join(file_text(path).splitlines()[start - 1:end]) + "\n"
    return "sha256:" + hashlib.sha256(excerpt.encode()).hexdigest()


def line_range(text: str, start: int, end: int) -> tuple[int, int]:
    return text.count("\n", 0, start) + 1, text.count("\n", 0, end) + 1


def tex_inventory(path: Path, paper_id: str) -> tuple[list[dict], list[dict]]:
    text = file_text(path)
    # Preserve byte/line positions while hiding unescaped TeX comments.
    masked="\n".join(re.sub(r"(?<!\\)%.*",lambda m:" "*len(m.group(0)),line) for line in text.split("\n"))
    bib, uses = [], []
    matches=list(BIB_RE.finditer(masked)); bibliography_end=masked.find("\\end{thebibliography}")
    bib_spans=[]
    for index, match in enumerate(matches):
        span_end=matches[index+1].start() if index+1<len(matches) else (bibliography_end if bibliography_end>=0 else match.end())
        start, end = line_range(text, match.start(), span_end)
        bib_spans.append((match.start(),span_end))
        citation_text=" ".join(text[match.start():span_end].split())
        bib.append({"paper_id": paper_id, "path": path.as_posix(), "key": match.group(1).strip(), "line_start": start, "line_end": end, "kind": "bibliography_entry", "citation_text":citation_text})
    for match in CITE_RE.finditer(masked):
        start, end = line_range(text, match.start(), match.end())
        qualifiers = re.findall(r"\[([^\]]*)\]", match.group(0)[:match.group(0).rfind("{")], re.S)
        for key in (part.strip() for part in match.group(1).split(",")):
            if key:
                context="bibliography_citation" if any(a<=match.start()<b for a,b in bib_spans) else "in_text_citation"
                uses.append({"paper_id": paper_id, "path": path.as_posix(), "key": key, "line_start": start, "line_end": end, "kind": "citation_usage", "citation_context":context, "command": match.group(0).split("[")[0].split("{")[0].lstrip("\\"), "qualifiers": qualifiers})
    return bib, uses


def paper_sources(root: Path, entry: str) -> tuple[list[Path], list[str]]:
    found=[]; unresolved=[]; pending=[safe_path(root,entry,label="paper local_source")]; seen=set()
    while pending:
        path=pending.pop()
        if path in seen: continue
        seen.add(path); found.append(path)
        masked="\n".join(re.sub(r"(?<!\\)%.*","",line) for line in file_text(path).split("\n"))
        for match in INPUT_RE.finditer(masked):
            raw=match.group(1).strip(); resolved=False
            for candidate in (path.parent/raw,root/"paper"/raw):
                if not candidate.suffix: candidate=candidate.with_suffix(".tex")
                try: rel=candidate.resolve().relative_to(root.resolve()).as_posix(); pending.append(safe_path(root,rel,label=f"include from {entry}")); resolved=True; break
                except (ValueError,AttributionError): continue
            if not resolved: unresolved.append(f"{path.relative_to(root).as_posix()}::{raw}")
    return found,sorted(set(unresolved))


def comment_lines(text: str) -> Iterable[tuple[int, str]]:
    depth = 0
    for number, line in enumerate(text.splitlines(), 1):
        pieces = []
        rest = line; in_string = False; escaped = False; cursor = 0
        while cursor < len(rest):
            if depth:
                begin=rest.find("/-",cursor); end=rest.find("-/",cursor)
                if begin>=0 and (end<0 or begin<end):
                    pieces.append(rest[cursor:begin]); depth+=1; cursor=begin+2; continue
                if end<0: pieces.append(rest[cursor:]); break
                pieces.append(rest[cursor:end]); depth-=1; cursor=end+2
            else:
                char = rest[cursor]
                if in_string:
                    if escaped: escaped = False
                    elif char == "\\": escaped = True
                    elif char == '"': in_string = False
                    cursor += 1; continue
                if char == '"': in_string = True; cursor += 1; continue
                if rest.startswith("--", cursor):
                    pieces.append(rest[cursor + 2:])
                    break
                if rest.startswith("/-", cursor):
                    depth = 1; cursor += 2; continue
                cursor += 1
        if pieces:
            yield number, " ".join(pieces)


def validate_registry(root: Path, registry: dict[str, Any], paper_by_id: dict[str, dict]) -> list[dict]:
    if registry.get("schema") != "research-source-attributions/1" or not isinstance(registry.get("scope"), dict):
        raise AttributionError("registry must carry research-source-attributions/1 and an object scope")
    sources = registry.get("sources")
    if not isinstance(sources, list):
        raise AttributionError("registry sources must be a list")
    ids: set[str] = set()
    for index, source in enumerate(sources):
        label = f"sources[{index}]"
        if not isinstance(source, dict) or not isinstance(source.get("id"), str) or not source["id"]:
            raise AttributionError(f"{label}: nonempty id required")
        if source["id"] in ids:
            raise AttributionError(f"duplicate source id: {source['id']}")
        ids.add(source["id"])
        if source.get("kind") not in KINDS or source.get("verification_state") not in STATES:
            raise AttributionError(f"{label}: invalid kind or verification_state")
        unknown = set(source) - SOURCE_FIELDS
        if unknown:
            raise AttributionError(f"{label}: unknown public fields: {sorted(unknown)}")
        if not isinstance(source.get("title"), str) or not source["title"].strip():
            raise AttributionError(f"{label}: nonempty title required")
        if not isinstance(source.get("authors"), list) or not source["authors"] or not all(isinstance(x, str) and x.strip() for x in source["authors"]):
            raise AttributionError(f"{label}: at least one nonempty author required")
        if not isinstance(source.get("relation"), str) or not source["relation"].strip():
            raise AttributionError(f"{label}: nonempty relation required")
        for field in ("mapping_status","mapping_note","verification_scope"):
            if field in source and (not isinstance(source[field],str) or not source[field].strip()):
                raise AttributionError(f"{label}: {field} must be nonempty text")
        if "year" in source and not isinstance(source["year"],(str,int)):
            raise AttributionError(f"{label}: year must be text or integer")
        if "publication_years" in source and (not isinstance(source["publication_years"],list) or not all(isinstance(y,(str,int)) for y in source["publication_years"])):
            raise AttributionError(f"{label}: publication_years must be a list of years")
        for reported_index, reported in enumerate(source.get("paper_reported_locators",[])):
            if not isinstance(reported,dict) or not str(reported.get("locator","")).strip() or set(reported)-({"path","locator","line_start","line_end","expected_text","excerpt_sha256"}):
                raise AttributionError(f"{label}.paper_reported_locators[{reported_index}]: malformed public locator")
            path=safe_path(root,reported.get("path"),label=f"{label} paper-reported locator")
            validate_range(path,reported,label=f"{label} paper-reported range")
        for url in source.get("urls", []):
            if not isinstance(url, str) or not url.startswith("https://"):
                raise AttributionError(f"{label}: only https URLs are public-safe")
        if source["kind"] == "correspondence":
            if source.get("identity_disclosure") != "withheld_pending_confirmation" or source.get("confirmation_status") != "not_confirmed":
                raise AttributionError(f"{label}: correspondence requires withheld, unconfirmed identity state")
            if source["authors"] != ["A mathematician (name withheld pending confirmation)"]:
                raise AttributionError(f"{label}: correspondence author must use the neutral withheld label")
            if source.get("urls"):
                raise AttributionError(f"{label}: private correspondence must not expose mailbox or message URLs")
            public_text=json.dumps(source,ensure_ascii=False)
            if EMAIL_RE.search(public_text) or ABSOLUTE_PRIVATE_PATH_RE.search(public_text):
                raise AttributionError(f"{label}: correspondence metadata contains a private address or local path")
        for loc_index, locator in enumerate(source.get("source_locators", [])):
            if not isinstance(locator, dict) or not str(locator.get("locator", "")).strip():
                raise AttributionError(f"{label}.source_locators[{loc_index}]: locator required")
            if set(locator)-LOCATOR_FIELDS:
                raise AttributionError(f"{label}.source_locators[{loc_index}]: unknown public fields")
            url = locator.get("url")
            if url is not None and (not isinstance(url, str) or not url.startswith("https://")):
                raise AttributionError(f"{label}.source_locators[{loc_index}]: url must be https")
            if url is None and source["kind"] != "correspondence":
                raise AttributionError(f"{label}.source_locators[{loc_index}]: public sources require an https url")
            if source["kind"] == "correspondence" and "evidence_path" in locator:
                raise AttributionError(f"{label}: private correspondence evidence paths must stay outside the public registry")
            if "evidence_path" in locator:
                path = safe_path(root, locator["evidence_path"], label=f"{label} evidence_path")
                validate_range(path, locator, label=f"{label} evidence range")
        for link_index, link in enumerate(source.get("artifact_links", [])):
            if not isinstance(link,dict) or set(link)-ARTIFACT_FIELDS:
                raise AttributionError(f"{label}.artifact_links[{link_index}]: unknown public fields")
            path = safe_path(root, link.get("path"), label=f"{label}.artifact_links[{link_index}]")
            validate_range(path, link, label=f"{label} artifact range")
        for binding in source.get("bibliography_keys", []):
            paper = paper_by_id.get(binding.get("path"))
            if paper is None:
                # `path` is intentionally the paper source path in this schema.
                paper = next((p for p in paper_by_id.values() if p["local_source"] == binding.get("path")), None)
            if paper is None or not isinstance(binding.get("key"), str) or not binding["key"]:
                raise AttributionError(f"{label}: dangling bibliography paper/key binding")
        if source["verification_state"] in {"source_verified","existing_source_closure"} and not source.get("source_locators"):
            raise AttributionError(f"{label}: verified source states require a source locator")
        if source["verification_state"] == "implemented_advice" and (not source.get("artifact_links") or source["kind"] != "correspondence" or source.get("identity_disclosure") != "withheld_pending_confirmation"):
            raise AttributionError(f"{label}: implemented correspondence advice requires a public artifact and withheld identity")
    return sources


def build(root: Path, registry_path: Path, paper_corpus_path: Path) -> dict[str, Any]:
    _FILE_BYTES.clear()
    registry = json.loads(file_text(registry_path))
    corpus = json.loads(file_text(paper_corpus_path))
    papers = corpus.get("papers", [])
    paper_by_id = {p["paper_id"]: p for p in papers}
    sources = validate_registry(root, registry, paper_by_id)
    known_source_ids={source["id"] for source in sources}
    lean_reviews={}
    for index,review in enumerate(registry.get("lean_reviews",[])):
        label=f"lean_reviews[{index}]"
        required_review_fields={"path","line_start","line_end","excerpt_sha256","disposition","source_ids","reason"}
        extras=set(review)-required_review_fields if isinstance(review,dict) else set()
        if not isinstance(review,dict) or not required_review_fields.issubset(review) or extras not in (set(),{"context"}):
            raise AttributionError(f"{label}: exact review fields required")
        path=safe_path(root,review["path"],label=label); validate_range(path,review,label=label)
        if "context" in review:
            context=review["context"]
            if not isinstance(context,dict) or set(context)!={"line_start","line_end","excerpt_sha256"}:
                raise AttributionError(f"{label}.context: exact context fields required")
            validate_range(path,context,label=f"{label}.context")
            if context["line_start"]>review["line_start"] or context["line_end"]<review["line_end"]:
                raise AttributionError(f"{label}.context: range must contain the candidate range")
        if review["disposition"] not in LEAN_REVIEW_DISPOSITIONS or not isinstance(review["reason"],str) or not review["reason"].strip():
            raise AttributionError(f"{label}: invalid disposition or empty reason")
        if not isinstance(review["source_ids"],list) or any(source_id not in known_source_ids for source_id in review["source_ids"]):
            raise AttributionError(f"{label}: source_ids must reference known sources")
        if review["disposition"]=="reviewed_citation_or_comparison" and not review["source_ids"]:
            raise AttributionError(f"{label}: reviewed citations require source_ids")
        key=(review["path"],review["line_start"],review["line_end"])
        if key in lean_reviews: raise AttributionError(f"duplicate Lean review coordinate: {key}")
        lean_reviews[key]=review
    bibliography, usages, unresolved_includes = [], [], []
    scanned_paths=set()
    scan_owners=defaultdict(set)
    maintained_source_anchors=[]
    assembled_by_output={row["output"].resolve(): (problem,row) for problem,row in assemble_reasoning_surfaces.PAPERS.items()}
    for paper in papers:
        root_source=safe_path(root,paper["local_source"],label=f"paper {paper['paper_id']}")
        path_roles={root_source.resolve():"generated_manuscript" if root_source.resolve() in assembled_by_output else "authored_manuscript"}
        paths,missing=paper_sources(root,paper["local_source"]); unresolved_includes.extend({"paper_id":paper["paper_id"],"locator":m} for m in missing)
        assembled=assembled_by_output.get(root_source.resolve())
        if assembled:
            problem,row=assembled
            maintained=[row["directory"] / "preamble.tex", *(row["directory"] / f"{name}.tex" for name in row["parts"])]
            for maintained_path in maintained:
                rel=maintained_path.relative_to(root).as_posix(); extra,extra_missing=paper_sources(root,rel)
                paths.extend(extra); unresolved_includes.extend({"paper_id":paper["paper_id"],"locator":m} for m in extra_missing)
                path_roles[maintained_path.resolve()]="authored_reasoning_preamble" if maintained_path.name=="preamble.tex" else "authored_reasoning_part"
                maintained_source_anchors.append({"paper_id":paper["paper_id"],"problem":problem,"generated_root":paper["local_source"],"maintained_path":rel,"role":path_roles[maintained_path.resolve()]})
        for path in dict.fromkeys(paths):
            scanned_paths.add(path.relative_to(root).as_posix()); scan_owners[path.relative_to(root).as_posix()].add(paper["paper_id"]); bib,cited=tex_inventory(path,paper["paper_id"])
            role=path_roles.get(path.resolve(),"included_tex_source")
            for item in bib+cited: item["path"]=path.relative_to(root).as_posix(); item["source_sha256"]=digest(path); item["source_role"]=role
            bibliography.extend(bib); usages.extend(cited)
    definitions = {(row["paper_id"], row["key"]) for row in bibliography}
    curated={}
    for source in sources:
        for binding in source.get("bibliography_keys",[]):
            key=(next((pid for pid,p in paper_by_id.items() if p["local_source"]==binding["path"]),binding["path"]),binding["key"])
            if key in curated and curated[key]!=source["id"]: raise AttributionError(f"duplicate bibliography binding: {key}")
            curated[key]=source["id"]
    missing_bindings=sorted(key for key in curated if key not in definitions)
    if missing_bindings:
        raise AttributionError(f"dangling bibliography keys: {missing_bindings}")
    # A bibliography row may bind automatically only when it contains one
    # unambiguous normalized exact URL owned by one curated source.
    url_owners=defaultdict(set)
    for source in sources:
        for url in source.get("urls", []): url_owners[normalized_url(url)].add(source["id"])
        for locator in source.get("source_locators", []):
            if locator.get("url"): url_owners[normalized_url(locator["url"])].add(source["id"])
    for entry in bibliography:
        key=(entry["paper_id"],entry["key"])
        if key in curated: continue
        path=root/entry["path"]
        excerpt="\n".join(file_text(path).splitlines()[entry["line_start"]-1:entry["line_end"]])
        owners=set()
        for url in URL_RE.findall(excerpt): owners.update(url_owners.get(normalized_url(url),set()))
        if len(owners)==1: curated[key]=next(iter(owners))
    for row in bibliography + usages:
        row["source_id"] = curated.get((row["paper_id"], row["key"]))
    lean_files = lean_source.library_source_paths(root)
    surnames=defaultdict(set); bib_keys=defaultdict(set)
    for source in sources:
        for author in source["authors"]:
            if len(author.split()[-1])>=4: surnames[author.split()[-1].casefold()].add(source["id"])
    for row in bibliography:
        token=row["key"].casefold()
        if token in GENERIC_REFERENCE_TOKENS: continue
        bib_keys[token]
        if row.get("source_id"): bib_keys[token].add(row["source_id"])
    token_lookup=set(bib_keys)|set(surnames)
    token_re=re.compile(r"(?<![\w-])(?:"+"|".join(re.escape(token) for token in sorted(token_lookup,key=lambda x:(-len(x),x)))+r")(?![\w-])") if token_lookup else None
    url_source_ids=defaultdict(set)
    for source in sources:
        for url in source.get("urls",[]): url_source_ids[normalized_url(url)].add(source["id"])
        for locator in source.get("source_locators",[]):
            if locator.get("url"): url_source_ids[normalized_url(locator["url"])].add(source["id"])
    lean_candidates = []
    for path in lean_files:
        rel = path.relative_to(root).as_posix(); file_digest = digest(path)
        for number, comment in comment_lines(file_text(path)):
            matches: list[dict[str, Any]] = []
            for url in URL_RE.findall(comment):
                source_ids=sorted(url_source_ids.get(normalized_url(url),set()))
                matches.append({"token":url,"match_kind":"explicit_url","source_ids":source_ids,"source_id":source_ids[0] if len(source_ids)==1 else None})
            for reference in REF_RE.findall(comment): matches.append({"token": reference, "match_kind": "explicit_reference", "source_id": None})
            lowered = comment.casefold()
            present={match.group(0) for match in token_re.finditer(lowered)} if token_re else set()
            for token in present:
                if token in bib_keys:
                    source_ids=bib_keys[token]; matches.append({"token":token,"match_kind":"bibliography_key","source_ids":sorted(source_ids),"source_id":next(iter(source_ids)) if len(source_ids)==1 else None})
                if token in surnames:
                    source_ids=surnames[token]; matches.append({"token":token,"match_kind":"curated_author_surname","source_ids":sorted(source_ids),"source_id":next(iter(source_ids)) if len(source_ids)==1 else None})
            if matches:
                unique = {(m["token"], m["match_kind"], m["source_id"]): m for m in matches}
                candidate={"path":rel,"line_start":number,"line_end":number,"source_sha256":file_digest,"excerpt_sha256":excerpt_digest(path,number,number),"classification":"lexical_candidate_not_attribution","matches":sorted(unique.values(),key=lambda m:(m["match_kind"],m["token"]))}
                review=lean_reviews.get((rel,number,number))
                if review:
                    candidate["review"]={k:review[k] for k in ("disposition","source_ids","reason")}
                    if "context" in review: candidate["review"]["context"]=review["context"]
                    candidate["review_status"]="unresolved" if review["disposition"]=="unresolved" else "reviewed"
                else: candidate["review_status"]="awaiting_review"
                lean_candidates.append(candidate)
    candidate_coordinates={(c["path"],c["line_start"],c["line_end"]) for c in lean_candidates}
    orphan_reviews=sorted(key for key in lean_reviews if key not in candidate_coordinates)
    if orphan_reviews: raise AttributionError(f"Lean reviews do not match current lexical candidates: {orphan_reviews[:5]}")
    enriched = []
    for source in sources:
        row = {field: source[field] for field in sorted(SOURCE_FIELDS) if field in source}
        row["artifact_coordinates"] = []
        for link in source.get("artifact_links", []):
            path=safe_path(root,link["path"],label=source["id"])
            row["artifact_coordinates"].append({**link,"sha256":digest(path),"excerpt_sha256":excerpt_digest(path,link["line_start"],link["line_end"])})
        row["source_coordinates"] = []
        for locator in source.get("source_locators", []):
            coordinate=dict(locator)
            if "evidence_path" in locator:
                path=safe_path(root,locator["evidence_path"],label=source["id"])
                coordinate.update({"sha256":digest(path),"excerpt_sha256":excerpt_digest(path,locator["line_start"],locator["line_end"])})
            row["source_coordinates"].append(coordinate)
        row["paper_reported_coordinates"]=[]
        for reported in source.get("paper_reported_locators",[]):
            path=safe_path(root,reported["path"],label=source["id"])
            row["paper_reported_coordinates"].append({**reported,"sha256":digest(path),"excerpt_sha256":excerpt_digest(path,reported["line_start"],reported["line_end"])})
        enriched.append(row)
    def facet(values):
        grouped=defaultdict(list)
        for key, source_id in values: grouped[str(key)].append(source_id)
        return [{"key": key, "source_ids": sorted(set(ids))} for key,ids in sorted(grouped.items())]
    unmatched = sorted({(u["paper_id"], u["key"]) for u in usages if (u["paper_id"],u["key"]) not in definitions})
    uncurated = sorted({(b["paper_id"], b["key"]) for b in bibliography if not b["source_id"]})
    usage_by_key=defaultdict(list)
    for usage in usages: usage_by_key[(usage["paper_id"],usage["key"])].append({k:usage[k] for k in ("path","line_start","line_end","command","qualifiers")})
    bibliography_by_key=defaultdict(list)
    for entry in bibliography: bibliography_by_key[(entry["paper_id"],entry["key"])].append(entry)
    for entry in bibliography:
        entry["citation_usages"]=usage_by_key[(entry["paper_id"],entry["key"])]
        entry["equivalent_source_coordinates"]=[{"path":other["path"],"line_start":other["line_start"],"line_end":other["line_end"],"source_role":other["source_role"]} for other in bibliography_by_key[(entry["paper_id"],entry["key"])] if other is not entry]
    return {
        "schema": OUTPUT_SCHEMA,
        "artifact_role": "generated_scholarly_source_attribution_and_coverage_view",
        "authority_boundary": "Navigation and source-credit evidence only. It does not establish proof, novelty, endorsement, peer review, or complete historical knowledge. Lean matches are lexical candidates, not attribution.",
        "generated_by": "scripts/build_source_attributions.py",
        "source_registry": registry_path.relative_to(root).as_posix(),
        "source_registry_sha256": digest(registry_path),
        "scope": registry["scope"],
        "sources": sorted(enriched, key=lambda s:s["id"]),
        "facets": {
            "by_author": facet((a,s["id"]) for s in sources for a in s["authors"]),
            "by_verification_state": facet((s["verification_state"],s["id"]) for s in sources),
            "by_problem": facet((p,s["id"]) for s in sources for p in s.get("problems",[])),
            "by_paper": facet((b["path"],s["id"]) for s in sources for b in s.get("bibliography_keys",[])),
        },
        "paper_inventory": {"paper_denominator":len(papers),"root_source_file_denominator":len({p["local_source"] for p in papers}),"scanned_source_file_denominator":len(scanned_paths),"scanned_source_paths":sorted(scanned_paths),"shared_include_paths":[{"path":path,"paper_ids":sorted(owners)} for path,owners in sorted(scan_owners.items()) if len(owners)>1],"maintained_source_anchors":sorted(maintained_source_anchors,key=lambda r:(r["paper_id"],r["maintained_path"])),"reasoning_surface_contract":"Generated reasoning roots inline authored files declared by scripts/assemble_reasoning_surfaces.py::PAPERS. Both reader-facing roots and maintained anchors are inventoried and labeled by source_role; shared TeX includes resolve through the manuscript directory and then the public paper root. Counts include intentional root/part duplication.","unresolved_includes":sorted(unresolved_includes,key=lambda r:(r["paper_id"],r["locator"])),"bibliography_entries":sorted(bibliography,key=lambda r:(r["paper_id"],r["path"],r["line_start"],r["key"])),"citation_usages":sorted(usages,key=lambda r:(r["paper_id"],r["path"],r["line_start"],r["key"])),"unmatched_citation_keys":[{"paper_id":p,"key":k} for p,k in unmatched],"bibliography_entries_without_curated_links":[{"paper_id":p,"key":k} for p,k in uncurated]},
        "lean_inventory": {"library_file_denominator":len(lean_files),"candidate_policy":"Comments only. Generic infrastructure tokens are excluded. Explicit URL/DOI/arXiv references are separated from bibliography-key and curated-surname clues. Authored lean_reviews bind exact path, line range, and excerpt digest; only missing or unresolved reviews remain queued.","excluded_generic_tokens":sorted(GENERIC_REFERENCE_TOKENS),"lexical_candidates":lean_candidates,"candidate_count":len(lean_candidates),"direct_reference_candidate_count":sum(1 for c in lean_candidates if any(m["match_kind"] in {"explicit_url","explicit_reference"} for m in c["matches"])),"named_or_key_candidate_count":sum(1 for c in lean_candidates if any(m["match_kind"] in {"bibliography_key","curated_author_surname"} for m in c["matches"])),"reviewed_count":sum(c["review_status"]=="reviewed" for c in lean_candidates),"unresolved_count":sum(c["review_status"]=="unresolved" for c in lean_candidates),"awaiting_review_count":sum(c["review_status"] in {"awaiting_review","unresolved"} for c in lean_candidates)},
        "coverage": {"curated_source_count":len(sources),"unmatched_citation_key_count":len(unmatched),"bibliography_without_curated_link_count":len(uncurated),"lean_candidate_awaiting_review_count":sum(c["review_status"] in {"awaiting_review","unresolved"} for c in lean_candidates)},
    }


def markdown(index: dict[str, Any]) -> bytes:
    def esc(value: Any) -> str:
        text=" ".join(str(value).split())
        for character in ("\\","`","*","_","[","]","<",">"): text=text.replace(character,"\\"+character)
        return text
    def anchor(value: str) -> str:
        return re.sub(r"[^a-z0-9]+","-",value.casefold()).strip("-") or "source"
    def local_link(row: dict[str,Any], label: str | None=None) -> str:
        path=quote(row["path"],safe="/"); start=row["line_start"]; end=row["line_end"]
        return f"[{esc(label or row['path'])}](../../{path}#L{start}-L{end})"
    sources={s["id"]:s for s in index["sources"]}
    def source_ref(source_id: str) -> str:
        title=sources[source_id]["title"]
        short=title if len(title)<=70 else title[:67].rstrip()+"…"
        return f"[{esc(short)}](#source-{anchor(source_id)})"
    usage_by_source=defaultdict(list)
    for usage in index["paper_inventory"]["citation_usages"]:
        if usage.get("source_id"): usage_by_source[usage["source_id"]].append(usage)
    lines = ["# Source attributions", "", "_Generated from the authored source registry; do not hand-edit._", "", "This index shows which public sources informed which papers, problems, Lean-facing records, and implemented changes. Source credit does not establish proof, novelty, endorsement, peer review, or complete historical coverage.", "", "Private correspondence appears only under a neutral anonymous identity until public naming is confirmed. Its email, mailbox location, message text, and private evidence remain outside this repository.", "", "## Coverage and anonymous implementation credits", "", f"The registry contains `{len(index['sources'])}` curated sources across `{index['paper_inventory']['paper_denominator']}` registered papers and `{index['lean_inventory']['library_file_denominator']}` Lean library files.", ""]
    states = {row["key"]: row["source_ids"] for row in index["facets"]["by_verification_state"]}
    lines += ["Source review states: " + "; ".join(f"`{state}`: `{len(ids)}`" for state, ids in sorted(states.items())) + ".", "", "Bibliography coverage records attribution already present in the corpus. A `bibliography_only` record still needs direct source-passage verification; a completed lexical review does not certify a source-to-theorem correspondence.", ""]
    anonymous=[s for s in index["sources"] if s["kind"]=="correspondence" and s["verification_state"]=="implemented_advice"]
    if anonymous:
        lines += ["Implemented advice whose identity is awaiting confirmation:", ""]
        for source in anonymous: lines.append(f"- {source_ref(source['id'])} — {esc(source['relation'])}")
        lines.append("")
    lines += [f"- Unmatched citation keys: `{index['coverage']['unmatched_citation_key_count']}`", f"- Bibliography entries awaiting curated links: `{index['coverage']['bibliography_without_curated_link_count']}`", f"- Lean candidates awaiting review: `{index['coverage']['lean_candidate_awaiting_review_count']}` (`{index['lean_inventory']['direct_reference_candidate_count']}` direct URL/DOI/arXiv rows; `{index['lean_inventory']['named_or_key_candidate_count']}` surname/key rows; categories may overlap).", "", "## Browse by problem", ""]
    lines[:0]=["<!-- SPDX-FileCopyrightText: 2026 Will Cook -->","<!-- SPDX-License-Identifier: CC-BY-4.0 -->",""]
    for entry in index["facets"]["by_problem"]:
        refs=", ".join(source_ref(i) for i in entry["source_ids"])
        lines.append(f"- **Erdős #{esc(entry['key'])}**: {refs}")
    if not index["facets"]["by_problem"]: lines.append("- No problem bindings are recorded.")
    lines += ["", "<details>", "<summary>Browse alphabetically by author or public identity</summary>", "", ""]
    for entry in index["facets"]["by_author"]:
        refs=", ".join(source_ref(i) for i in entry["source_ids"])
        lines.append(f"- **{esc(entry['key'])}**: {refs}")
    lines += ["", "</details>", "", "## Sources and exact uses", ""]
    for source in index["sources"]:
        primary=source.get("urls",[])[0] if source.get("urls") else None
        heading=f"[{esc(source['title'])}]({primary})" if primary else esc(source["title"])
        lines += [f'<a id="source-{anchor(source["id"])}"></a>', "", f"### {heading}", "", f"- Source id: `{esc(source['id'])}`", f"- Author or public identity: {', '.join(esc(a) for a in source['authors'])}", f"- Kind: `{esc(source['kind'])}`", f"- Problems: {', '.join('#'+esc(p) for p in source.get('problems', [])) or 'none recorded'}", f"- Relationship and boundary: {esc(source['relation'])}", f"- Source verification: `{esc(source['verification_state'])}` — {esc(source.get('verification_scope','scope not separately recorded'))}", f"- Local mapping: `{esc(source.get('mapping_status','not recorded'))}`" + (f" — {esc(source['mapping_note'])}" if source.get('mapping_note') else ""), ""]
        if source.get("source_locators"):
            lines += ["Exact source locations:", ""]
            for locator in source["source_locators"]:
                label=esc(locator["locator"])
                lines.append(f"- [{label}]({locator['url']})" if locator.get("url") else f"- {label}")
            lines.append("")
        if source.get("artifact_coordinates"):
            lines += ["Public implementation or evidence coordinates:", ""]
            for item in source["artifact_coordinates"]:
                lines.append(f"- {local_link(item)} — lines `{item['line_start']}–{item['line_end']}`; excerpt `{item['excerpt_sha256']}`")
            lines.append("")
        if source.get("paper_reported_coordinates"):
            lines += ["Paper-reported locations (the paper reports this relationship; the label alone is not independent verification):", ""]
            for item in source["paper_reported_coordinates"]:
                lines.append(f"- {local_link(item,item['locator'])} — `{item['path']}:{item['line_start']}–{item['line_end']}`")
            lines.append("")
        if usage_by_source[source["id"]]:
            lines += ["Paper citation usages:", ""]
            groups=defaultdict(list)
            for item in usage_by_source[source["id"]]: groups[item["paper_id"]].append(item)
            for paper_id, items in sorted(groups.items()):
                links=", ".join(local_link(item,f"{item['command']} at {item['path']}:{item['line_start']}") for item in items)
                lines.append(f"- `{esc(paper_id)}`: {links}")
            lines.append("")
    lines += ["## Coverage requiring review", "", "These gaps are shown explicitly so the catalogue cannot be mistaken for complete historical knowledge.", "", f"- Registered papers scanned: `{index['paper_inventory']['paper_denominator']}`; TeX source files scanned after local includes: `{index['paper_inventory']['scanned_source_file_denominator']}`.", f"- Citation keys without a local bibliography definition: `{index['coverage']['unmatched_citation_key_count']}`", f"- Bibliography entries without a curated source link: `{index['coverage']['bibliography_without_curated_link_count']}`", f"- Lean lexical candidates awaiting review: `{index['coverage']['lean_candidate_awaiting_review_count']}`", f"- Unresolved local TeX includes: `{len(index['paper_inventory']['unresolved_includes'])}`", "", "Machine-readable inventories, hashes, unresolved keys, and lexical candidates: [source-attribution-index.json](source-attribution-index.json).", ""]
    return "\n".join(lines).encode()


def write(path: Path, payload: bytes) -> None:
    if path.is_symlink(): raise AttributionError(f"refusing symlink output: {path}")
    path.write_bytes(payload)


def main(argv: list[str] | None = None) -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    parser.add_argument("--query")
    parser.add_argument("--root",type=Path,default=ROOT)
    parser.add_argument("--registry",type=Path)
    args=parser.parse_args(argv); root=args.root.resolve()
    registry=(args.registry or root/"docs/research-commons/source-attributions.json").resolve()
    try: index=build(root,registry,root/"docs/papers/corpus.json")
    except (OSError,json.JSONDecodeError,AttributionError,KeyError,TypeError) as exc:
        print(f"build_source_attributions: {exc}",file=sys.stderr); return 1
    if args.query:
        q=args.query.casefold(); rows=[s for s in index["sources"] if q in s["id"].casefold() or q in s["title"].casefold() or any(q in a.casefold() for a in s["authors"]) or q in {str(p).casefold() for p in s.get("problems",[])}]
        print(json.dumps(rows,indent=2,ensure_ascii=False)); return 0 if rows else 1
    jp,mp=canonical(index),markdown(index); jo=root/"docs/research-commons/source-attribution-index.json"; mo=root/"docs/research-commons/SOURCE_ATTRIBUTIONS.md"
    if args.check:
        current=jo.is_file() and mo.is_file() and jo.read_bytes()==jp and mo.read_bytes()==mp
        print("source attribution views current" if current else "source attribution views stale; run python3 scripts/build_source_attributions.py")
        return 0 if current else 1
    try: write(jo,jp); write(mo,mp)
    except (OSError,AttributionError) as exc: print(f"build_source_attributions: {exc}",file=sys.stderr); return 1
    print("wrote source attribution JSON and Markdown views"); return 0


if __name__ == "__main__": raise SystemExit(main())
