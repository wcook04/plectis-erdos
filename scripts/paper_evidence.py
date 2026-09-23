#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Resolve and render the formal evidence behind every result of the sixteen papers.

Each asserting environment of the eight short papers and eight long records is a row of
the coverage ledger (docs/paper_lean_coverage.json).  This script turns those rows into
what a reader meets:

* paper/evidence/<paper>.tex  one \\DeclareResultEvidence line per result with a Lean
                              proof, read by paper/paper-evidence.tex, which places the
                              "Lean" and "Comparator" links in the margin beside it;
* evidence/<paper>.md         the paper's evidence record: for every result, the Lean
                              declarations that state it (with their statements), how they
                              relate to the printed statement, and the Comparator check;
* evidence/paper_evidence.json the resolved mapping both are rendered from.

Nothing is inferred from list positions or from search order.  A Lean mark links one
declaration only when that declaration is the whole of the row's recorded evidence;
otherwise it opens the record, which lists every declaration.  A Comparator mark is
written only when every declaration of the row resolves, through
evidence/comparator/associations.json, to a Challenge theorem, a Solution theorem and
an entry whose replay receipt (evidence/comparator/replay-<run>/receipt-<entry>.json,
the file the replay wrote) passed at the pinned corpus commit and whose recorded
digests match the corpus bytes at that commit.  The declaration's statement at the
paper's Lean pin must equal the statement the corpus compiled, after comments and
layout are removed.

Every failure is collected; if there is any, nothing is written and the exit status is 1.

Usage:
  paper_evidence.py build --corpus-repo PATH --aux-dir DIR [--record-commit SHA]
  paper_evidence.py check [--corpus-repo PATH]      # regenerate in memory, compare
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from migrate_statement_presentation import bodies, presentation_form  # noqa: E402
from lean_source import (  # noqa: E402
    DECLARATION_HEAD_RE,
    lean_code_without_comments_and_strings,
    qualified_declaration_lines,
)

LEDGER = "docs/paper_lean_coverage.json"
CONFIG = "evidence/config.json"
ASSOCIATIONS = "evidence/comparator/associations.json"
RELATIONS = "evidence/relations.json"
EVIDENCE_MAP = "evidence/paper_evidence.json"
FULL_TEXT = "docs/papers/full-text"
SIDECAR_DIR = "paper/evidence"
RECORD_DIR = "evidence"
REPO_URL = "https://github.com/wcook04/plectis-erdos"
CORPUS_URL = "https://github.com/wcook04/plectis-erdos-lean"
SCHEMA = "plectis-paper-evidence/1"
RECEIPT_SCHEMA = "palomar_replay_receipt_v1"
PERMITTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]

# The printed name of each theorem-like environment, as the preambles define it.
ENVIRONMENT_NAMES = {
    "theorem": "Theorem", "thm": "Theorem",
    "proposition": "Proposition", "prop": "Proposition",
    "lemma": "Lemma", "lem": "Lemma",
    "corollary": "Corollary", "cor": "Corollary",
    "claim": "Claim", "equivform": "Equivalent form",
}


class EvidenceError(RuntimeError):
    pass


# --------------------------------------------------------------------------- git


class Repo:
    """Read-only access to committed bytes of one repository."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self._cache: dict[tuple[str, str], bytes | None] = {}
        self._batch: subprocess.Popen | None = None

    def blob(self, commit: str, path: str) -> bytes | None:
        key = (commit, path)
        if key not in self._cache:
            if self._batch is None:
                self._batch = subprocess.Popen(["git", "-C", str(self.root), "cat-file", "--batch"],
                                               stdin=subprocess.PIPE, stdout=subprocess.PIPE)
            assert self._batch.stdin and self._batch.stdout
            self._batch.stdin.write(f"{commit}:{path}\n".encode())
            self._batch.stdin.flush()
            header = self._batch.stdout.readline().decode().split()
            if len(header) == 3 and header[1] == "blob":
                data = self._batch.stdout.read(int(header[2]))
                self._batch.stdout.read(1)
                self._cache[key] = data
            else:
                self._cache[key] = None
        return self._cache[key]

    def text(self, commit: str, path: str) -> str | None:
        data = self.blob(commit, path)
        return None if data is None else data.decode("utf-8")

    def has_commit(self, commit: str) -> bool:
        return subprocess.run(["git", "-C", str(self.root), "cat-file", "-e", f"{commit}^{{commit}}"],
                              capture_output=True).returncode == 0


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


# --------------------------------------------------------------------------- Lean text


@dataclass(frozen=True)
class LeanDeclaration:
    name: str
    path: str
    line: int
    kind: str
    docstring: str | None
    statement: str          # as written, docstring and proof excluded
    normalised: str         # comments removed, layout collapsed
    unfolds: tuple = ()     # ((name, path, line, text), ...) definitions the statement's type names
    named: str | None = None  # the identifier the statement's type consists of, if it is one


def named_proposition(normalised: str) -> str | None:
    """The identifier a statement's type consists of, e.g. `DivisibilityWeightedClaim`."""
    depth = 0
    cut = -1
    for i, c in enumerate(normalised):
        if c in "([{\u27e8":
            depth += 1
        elif c in ")]}\u27e9":
            depth -= 1
        elif c == ":" and depth == 0 and not normalised.startswith(":=", i):
            cut = i
    if cut < 0:
        return None
    target = normalised[cut + 1:].strip()
    m = re.fullmatch(r"([A-Za-z_][\w'.]*)((?:\s+[\w'.]+)*)", target)
    return m.group(1) if m else None


class LeanFile:
    """One Lean file, parsed once: its declaration index and comment-free text."""

    def __init__(self, text: str) -> None:
        self.text = text
        self.blank = lean_code_without_comments_and_strings(text)
        self.lines = text.splitlines(keepends=True)
        self.index = qualified_declaration_lines(text)
        self.offsets = [0]
        for item in self.lines:
            self.offsets.append(self.offsets[-1] + len(item))

    def unique_line(self, declaration: str, *, allow_suffix: bool) -> int:
        hits = self.index.get(declaration)
        if hits is None and allow_suffix:
            candidates = [lines for name, lines in self.index.items()
                          if name.endswith("." + declaration) or declaration.endswith("." + name)]
            if len(candidates) == 1:
                hits = candidates[0]
        if not hits:
            raise EvidenceError(f"{declaration} is not declared")
        if len(hits) != 1:
            raise EvidenceError(f"{declaration} is declared on lines {hits}")
        return hits[0]


def _statement_end(blank: str, start: int) -> int:
    """Offset of the `:=` (or `where`) that ends the statement starting at `start`."""
    depth = 0
    i = start
    n = len(blank)
    opening, closing = "([{⟨", ")]}⟩"
    while i < n:
        c = blank[i]
        if c in opening:
            depth += 1
        elif c in closing:
            depth = max(0, depth - 1)
        elif depth == 0:
            if blank.startswith(":=", i):
                return i
            if blank.startswith("where", i) and (i == 0 or not blank[i - 1].isalnum()) and \
                    (i + 5 >= n or not (blank[i + 5].isalnum() or blank[i + 5] in "_'")):
                return i
            if c == "\n":
                line_end = blank.find("\n", i + 1)
                following = blank[i + 1: line_end if line_end >= 0 else n]
                if re.match(r"\s*\|.*=>", following):
                    return i + 1
        i += 1
    raise EvidenceError("statement has no terminating := or where")


def lean_declaration(source: LeanFile, path: str, declaration: str, *, allow_suffix: bool) -> LeanDeclaration:
    line = source.unique_line(declaration, allow_suffix=allow_suffix)
    text, blank, lines = source.text, source.blank, source.lines
    start = source.offsets[line - 1]
    first = blank[start:].split("\n", 1)[0]
    head = DECLARATION_HEAD_RE.match(first)
    kind = "theorem"
    if head is not None:
        words = re.findall(r"\b(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b",
                           first[: head.end()])
        kind = words[0] if words else "theorem"
    end = _statement_end(blank, start)
    statement = text[start:end].rstrip()
    normalised = " ".join(blank[start:end].split())
    # The docstring immediately above the declaration (attributes may sit between).
    docstring = None
    k = line - 2
    while k >= 0 and lines[k].lstrip().startswith("@["):
        k -= 1
    if k >= 0 and lines[k].rstrip().endswith("-/"):
        j = k
        while j >= 0 and "/--" not in lines[j]:
            j -= 1
        if j >= 0:
            block = "".join(lines[j:k + 1]).strip()
            block = block[block.index("/--") + 3:]
            docstring = block[: block.rindex("-/")].strip() or None
    if kind not in ("theorem", "lemma"):
        # A definition is shown whole: its body is what the paper's statement reads.
        tail = text[end:]
        stop = re.search(r"\n\s*\n", tail)
        body = tail[: stop.start()] if stop else tail
        if body.count("\n") <= 40:
            statement = (text[start:end] + body).rstrip()
    unfolds = ()
    named = named_proposition(normalised) if kind in ("theorem", "lemma") else None
    if named:
        hits = [(n, lines_) for n, lines_ in source.index.items()
                if n == named or n.endswith("." + named)]
        if len(hits) == 1 and len(hits[0][1]) == 1:
            dline = hits[0][1][0]
            dstart = source.offsets[dline - 1]
            tail = text[dstart:]
            stop = re.search(r"\n\s*\n", tail)
            body = (tail[: stop.start()] if stop else tail).rstrip()
            if body.count("\n") <= 60 and re.match(r"\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:def|abbrev)\b",
                                                   blank[dstart:dstart + len(body)]):
                unfolds = ((hits[0][0], path, dline, body),)
    return LeanDeclaration(declaration, path, line, kind, docstring, statement, normalised, unfolds, named)


def definition_body(source: LeanFile, line: int) -> str | None:
    """The text of the def or abbrev on `line`, up to the next blank line, if it is short."""
    start = source.offsets[line - 1]
    tail = source.text[start:]
    stop = re.search(r"\n\s*\n", tail)
    body = (tail[: stop.start()] if stop else tail).rstrip()
    if body.count("\n") > 60 or not re.match(
            r"\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:def|abbrev)\b",
            source.blank[start:start + len(body)]):
        return None
    return body


def tex_to_markdown(text: str | None, numbers: dict[str, tuple[str, str]]) -> str | None:
    """A ledger scope or reason, written in TeX, as Markdown a reader can follow."""
    if not text:
        return text
    def number(label: str) -> str:
        found = numbers.get(label)
        return found[0] if found and found[0] else "above"
    out = re.sub(r"\\eqref\{([^}]*)\}", lambda m: f"({number(m.group(1))})", text)
    out = re.sub(r"\\ref\{([^}]*)\}", lambda m: number(m.group(1)), out)
    out = re.sub(r"\\emph\{([^}]*)\}", r"*\1*", out)
    out = re.sub(r"\\texttt\{([^}]*)\}", r"`\1`", out)
    return out.replace("~", " ").replace("\\ ", " ")


# --------------------------------------------------------------------------- inputs


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def anchor_of(label: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", label.lower()).strip("-")


def tex_url(url: str) -> str:
    return url.replace("\\", "/").replace("%", "\\%").replace("#", "\\#")


def parse_aux(path: Path, pdf: Path | None = None) -> dict[str, tuple[str, str]]:
    """label -> (printed number, page) from a LaTeX .aux written with hyperref.

    The page LaTeX records for a label set on a theorem's first line can be the page before
    the heading, when a page break falls between the two.  When the built PDF is given, the
    page is read from the hyperref destination at the heading instead.
    """
    out: dict[str, tuple[str, str]] = {}
    anchors: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = re.match(r"\\newlabel\{([^}]*)\}\{\{(.*?)\}\{(\d+)\}\{.*\}\{([^{}]*)\}\{[^{}]*\}\}\s*$", line)
        if m:
            out[m.group(1)] = (m.group(2), m.group(3))
            anchors[m.group(1)] = m.group(4)
            continue
        m = re.match(r"\\newlabel\{([^}]*)\}\{\{(.*?)\}\{(\d+)\}", line)
        if m:
            out[m.group(1)] = (m.group(2), m.group(3))
    if pdf is not None and pdf.is_file():
        from pypdf import PdfReader  # noqa: PLC0415  (only the local build step reads PDFs)
        reader = PdfReader(str(pdf))
        pages = {}
        for name, dest in reader.named_destinations.items():
            try:
                pages[str(name).lstrip("/")] = reader.get_destination_page_number(dest) + 1
            except Exception:  # noqa: BLE001
                continue
        for label, anchor in anchors.items():
            if anchor in pages:
                out[label] = (out[label][0], str(pages[anchor]))
    return out


FULL_TEXT_DIV = re.compile(r'<div id="([^"]+)" class="([a-z]+)">\n(.*?)\n</div>', re.S)
FULL_TEXT_HEAD = re.compile(r"^\*\*[A-Z][A-Za-z ]* \d+\*\*(?: \((.*?)\))?\.\s*", re.S)
EVIDENCE_LINE = re.compile(r'^<p class="evidence-marks">.*?</p>\n', re.M)


def full_text_statements(path: Path) -> dict[str, tuple[str | None, str]]:
    """label -> (title, the statement's Markdown body) from the reading edition."""
    if not path.is_file():
        return {}
    text = path.read_text(encoding="utf-8")
    out: dict[str, tuple[str | None, str]] = {}
    for m in FULL_TEXT_DIV.finditer(text):
        body = EVIDENCE_LINE.sub("", m.group(3)).strip()
        head = FULL_TEXT_HEAD.match(body)
        title = head.group(1) if head else None
        body = FULL_TEXT_HEAD.sub("", body, count=1).strip()
        out[m.group(1)] = (title, body)
    return out


def span_title(row: dict) -> str | None:
    """The opening words of a labelled claim span, as plain text."""
    phrase = (row.get("span") or {}).get("start")
    if not phrase:
        return None
    text = re.sub(r"\\href\{[^}]*\}\{([^}]*)\}", r"\1", phrase)
    text = re.sub(r"\\[A-Za-z]+\*?", "", text)
    text = re.sub(r"[{}~]", " ", text)
    return "beginning \u201c" + " ".join(text.split()) + "\u2026\u201d"


# --------------------------------------------------------------------------- resolution


@dataclass
class Problems:
    items: list[str] = field(default_factory=list)

    def add(self, where: str, what: str) -> None:
        self.items.append(f"{where}: {what}")


def resolve(root: Path, corpus: Repo | None, aux_dir: Path | None,
            previous: dict | None, problems: Problems, *, require_relations: bool) -> dict:
    ledger = load_json(root / LEDGER)
    config = load_json(root / CONFIG)
    associations = load_json(root / ASSOCIATIONS)
    relations = load_json(root / RELATIONS) if (root / RELATIONS).is_file() else {"rows": {}}
    here = Repo(root)
    pin = ledger["lean_pin"]
    if not here.has_commit(pin):
        problems.add("ledger", f"lean_pin {pin} is not in this repository's history")
    corpus_commit = config["corpus_commit"]
    run_id = str(config["replay"]["run_id"])
    receipts_dir = root / config["replay"]["receipts"]
    if associations.get("corpus_commit") != corpus_commit or str(associations.get("run_id")) != run_id:
        problems.add(ASSOCIATIONS, "names a different corpus commit or replay run than evidence/config.json")
    if corpus is not None and not corpus.has_commit(corpus_commit):
        problems.add("corpus", f"{corpus_commit} is not in {corpus.root}")

    previous_rows = {}
    if previous:
        for paper in previous.get("papers", []):
            for row in paper["results"]:
                previous_rows[row["id"]] = row

    receipts: dict[str, dict] = {}

    def receipt(entry: str, where: str) -> dict | None:
        if entry in receipts:
            return receipts[entry]
        path = receipts_dir / f"receipt-{entry}.json"
        if not path.is_file():
            problems.add(where, f"no replay receipt {path.relative_to(root)}")
            receipts[entry] = None
            return None
        data = load_json(path)
        bad = []
        if data.get("schema") != RECEIPT_SCHEMA:
            bad.append("schema")
        github = data.get("github") or {}
        if github.get("sha") != corpus_commit:
            bad.append(f"commit {github.get('sha')}")
        if str(github.get("run_id")) != run_id:
            bad.append(f"run {github.get('run_id')}")
        if github.get("repository") != "wcook04/plectis-erdos-lean":
            bad.append("repository")
        if data.get("entry") != entry:
            bad.append("entry")
        if (data.get("verification") or {}).get("outcome") != "passed" or data.get("exit") != 0:
            bad.append("outcome")
        if data.get("kernel_acceptance") != {"lean_default": True, "nanoda": True}:
            bad.append("kernel acceptance")
        if sorted(data.get("permitted_axioms") or []) != sorted(PERMITTED_AXIOMS):
            bad.append("permitted axioms")
        if corpus is not None and not bad:
            for name, digest in (data.get("entry_digests") or {}).items():
                blob = corpus.blob(corpus_commit, f"PalomarCorpus/{entry}/{name}")
                if blob is None or sha256_hex(blob) != digest:
                    bad.append(f"{name} digest")
            for path_, digest in ((data.get("solution") or {}).get("files") or {}).items():
                blob = corpus.blob(corpus_commit, path_)
                if blob is None or sha256_hex(blob) != digest:
                    bad.append(f"{path_} digest")
        if bad:
            problems.add(where, f"receipt-{entry}.json does not show a passing check of the pinned "
                               f"corpus bytes ({', '.join(bad)})")
            data = None
        receipts[entry] = data
        return data

    aux_numbers: dict[str, dict[str, tuple[str, str]]] = {}
    papers_out = []
    anchors_seen: dict[str, set[str]] = {}
    lean_cache: dict[tuple[str, str], LeanDeclaration] = {}
    pin_files: dict[str, LeanFile | None] = {}
    corpus_files: dict[str, LeanFile | None] = {}

    def_index: dict[str, list[tuple[str, int]]] = {}

    def pin_definition(named: str, near: str = "") -> tuple[str, str, int, str] | None:
        """(qualified name, path, line, text) of the definition `named` refers to at the pin.

        A name with several definitions (the external-verification library restates some)
        resolves to the one in the Lean library, and then to the one sharing the longest
        namespace with `near`, the declaration that uses it; a tie is left unresolved.
        """
        if named in ("let", "True", "False", "fun"):
            return None
        if not def_index:
            done = subprocess.run(
                ["git", "-C", str(root), "grep", "-n", "-E",
                 r"^[[:space:]]*(@\[[^]]*\][[:space:]]*)*(noncomputable[[:space:]]+)?(def|abbrev)[[:space:]]+[A-Za-z_]",
                 pin, "--", "lean",
                 "verification"], capture_output=True, text=True)
            for line in done.stdout.splitlines():
                _rev, path, number, text = line.split(":", 3)
                m = re.search(r"\b(?:def|abbrev)\s+([A-Za-z_][\w'.]*)", text)
                if m:
                    def_index.setdefault(m.group(1).rsplit(".", 1)[-1], []).append((path, int(number)))
            def_index.setdefault("", [])
        found = []
        for path, _number in def_index.get(named.rsplit(".", 1)[-1], []):
            if path not in pin_files:
                text = here.text(pin, path)
                pin_files[path] = None if text is None else LeanFile(text)
            source = pin_files[path]
            if source is None:
                continue
            for qualified, lines in source.index.items():
                if (qualified == named or qualified.endswith("." + named)) and len(lines) == 1:
                    found.append((qualified, path, lines[0], source))
        if len(found) > 1:
            in_library = [f for f in found if f[1].startswith("lean/")]
            found = in_library or found
        if len(found) > 1 and near:
            def shared(qualified: str) -> int:
                a, b = qualified.split("."), near.split(".")
                k = 0
                while k < min(len(a), len(b)) and a[k] == b[k]:
                    k += 1
                return k
            best = max(shared(f[0]) for f in found)
            found = [f for f in found if shared(f[0]) == best]
        if len(found) != 1:
            return None
        qualified, path, line, source = found[0]
        body = definition_body(source, line)
        return None if body is None else (qualified, path, line, body)

    def pin_decl(name: str, path: str, where: str) -> LeanDeclaration | None:
        key = (path, name)
        if key not in lean_cache:
            if path not in pin_files:
                text = here.text(pin, path)
                pin_files[path] = None if text is None else LeanFile(text)
            source = pin_files[path]
            if source is None:
                problems.add(where, f"{path} is absent at the Lean pin {pin[:12]}")
                return None
            try:
                lean_cache[key] = lean_declaration(source, path, name, allow_suffix=True)
            except EvidenceError as exc:
                problems.add(where, f"{path} at {pin[:12]}: {exc}")
                return None
        return lean_cache[key]

    def corpus_decl(name: str, path: str, where: str, *, allow_suffix: bool = False) -> LeanDeclaration | None:
        if corpus is None:
            return None
        if path not in corpus_files:
            text = corpus.text(corpus_commit, path)
            corpus_files[path] = None if text is None else LeanFile(text)
        source = corpus_files[path]
        if source is None:
            problems.add(where, f"{path} is absent from the corpus at {corpus_commit[:12]}")
            return None
        try:
            return lean_declaration(source, path, name, allow_suffix=allow_suffix)
        except EvidenceError as exc:
            problems.add(where, f"corpus {path}: {exc}")
            return None

    rows_by_paper: dict[str, list[dict]] = {}
    for row in ledger["rows"]:
        rows_by_paper.setdefault(row["paper_id"], []).append(row)

    # The statement a relation note was written against, keyed so that removing labels,
    # inline citations and tags from it does not invalidate the note.
    statement_keys: dict[str, str] = {}
    for paper in ledger["papers"]:
        pairs = [(rel, (root / rel).read_text(encoding="utf-8")) for rel in paper["sources"]]
        spans = [{"label": r["label"], **r["span"]} for r in rows_by_paper.get(paper["paper_id"], []) if r.get("span")]
        for env in bodies(pairs, spans):
            if env.get("body") is not None:
                statement_keys[env["statement_sha256"]] = "sha256:" + sha256_hex(presentation_form(env["body"]).encode())

    for paper in ledger["papers"]:
        pid = paper["paper_id"]
        numbers = {}
        if aux_dir is not None:
            aux = aux_dir / f"{pid}.aux"
            if not aux.is_file():
                problems.add(pid, f"no {aux}")
            else:
                numbers = parse_aux(aux, aux_dir / f"{pid}.pdf")
        aux_numbers[pid] = numbers
        statements = full_text_statements(root / FULL_TEXT / f"{pid}.md")
        results = []
        anchors_seen[pid] = set()
        rows = sorted(rows_by_paper.get(pid, []),
                      key=lambda r: (r["source"].rsplit(":", 1)[0], int(r["source"].rsplit(":", 1)[1])))
        for row in rows:
            where = row["id"]
            label = row.get("label") or ""
            if not label:
                problems.add(where, "has no label, so its mark cannot be placed")
                continue
            anchor = anchor_of(label)
            if anchor in anchors_seen[pid]:
                anchor = f"{anchor}-{sha256_hex(label.encode())[:6]}"
            if anchor in anchors_seen[pid]:
                problems.add(where, f"anchor {anchor} collides with another result of the paper")
            anchors_seen[pid].add(anchor)
            status = row["lean"]["status"]
            env = row.get("environment")
            printed_kind = ENVIRONMENT_NAMES.get(env or "", "Result") if env else "Passage"
            prev = previous_rows.get(row["id"], {})
            numbers_for_row_all = numbers or {r.get("label"): (r.get("number"), r.get("page"))
                                              for r in previous_rows.values() if r.get("label")}
            if env is None:
                # A labelled claim span has no heading of its own: it is cited by page.
                numbers_for_row = {label: (None, numbers[label][1])} if label in numbers else {}
            else:
                numbers_for_row = numbers
            if numbers_for_row:
                if label not in numbers_for_row:
                    problems.add(where, f"label {label} is not in the paper's .aux")
                    number, page = None, None
                else:
                    number, page = numbers_for_row[label]
            else:
                number, page = prev.get("number"), prev.get("page")
            if env is None:
                number = None
            decls = []
            for d in row["lean"].get("declarations", []):
                resolved = pin_decl(d["name"], d["file"], where)
                if resolved is None:
                    continue
                decls.append(resolved)
            if status in ("exact", "exact_or_stronger", "modulo_named_input") and \
                    len(decls) != len(row["lean"].get("declarations", [])):
                continue  # already reported
            relation = None
            if status == "exact_or_stronger":
                note = relations["rows"].get(row["id"])
                stamp = {d.name: sha256_hex(d.normalised.encode()) for d in decls}
                if note is None:
                    if require_relations:
                        problems.add(where, "exact_or_stronger row without an authored relation note")
                elif note.get("statement_key") != statement_keys.get(row["statement_sha256"]) or \
                        note.get("lean_statements") != stamp:
                    problems.add(where, "relation note was written against a different statement; review it")
                else:
                    relation = note["note"]
            comparator = None
            if row["comparator"]["status"] == "compared":
                checks = []
                for d in decls:
                    link = associations["declarations"].get(d.name)
                    if link is None:
                        problems.add(where, f"{d.name} has no Comparator association")
                        continue
                    entry = link["entry"]
                    got = receipt(entry, where)
                    if got is None:
                        continue
                    if link["challenge"] not in got.get("theorem_names", []):
                        problems.add(where, f"receipt-{entry}.json does not compare {link['challenge']}")
                        continue
                    challenge_path = f"PalomarCorpus/{entry}/Challenge.lean"
                    challenge = corpus_decl(link["challenge"], challenge_path, where)
                    # Comparator matches constants by name: the Solution declares the Challenge's
                    # theorem under the same name, in its own module.
                    solution_path = link["solution_path"]
                    solution = None
                    if corpus is not None:
                        declaring = []
                        for candidate in sorted((got.get("solution") or {}).get("files", {})):
                            if candidate not in corpus_files:
                                text = corpus.text(corpus_commit, candidate)
                                corpus_files[candidate] = None if text is None else LeanFile(text)
                            parsed = corpus_files[candidate]
                            if parsed is not None and link["challenge"] in parsed.index:
                                declaring.append(candidate)
                        if len(declaring) != 1:
                            problems.add(where, f"{link['challenge']} is declared in {len(declaring)} of the "
                                                f"Solution files receipt-{entry}.json checked")
                            continue
                        solution_path = declaring[0]
                        solution = corpus_decl(link["challenge"], solution_path, where)
                    if corpus is not None:
                        if challenge is None or solution is None:
                            continue
                        vendored_path = d.path[len("lean/"):] if d.path.startswith("lean/") else d.path
                        vendored = corpus_decl(d.name, vendored_path, where, allow_suffix=True)
                        if vendored is None:
                            continue
                        if vendored.normalised != d.normalised:
                            problems.add(where, f"{d.name}: the statement at the Lean pin differs from the one "
                                                f"the corpus compared ({vendored_path})")
                            continue
                    old = {c["declaration"]: c for c in (prev.get("comparator") or {}).get("checks", [])}
                    checks.append({
                        "declaration": d.name,
                        "entry": entry,
                        "challenge": {
                            "declaration": link["challenge"], "path": challenge_path,
                            "line": challenge.line if challenge else old.get(d.name, {}).get("challenge", {}).get("line"),
                            "statement": challenge.statement if challenge else old.get(d.name, {}).get("challenge", {}).get("statement"),
                            "same_as_lean": (challenge.normalised.split(":", 1)[-1] == d.normalised.split(":", 1)[-1])
                            if challenge else old.get(d.name, {}).get("challenge", {}).get("same_as_lean"),
                        },
                        "solution": {
                            "declaration": link["challenge"], "module": link["solution"].rsplit(".", 1)[0],
                            "path": solution_path,
                            "line": solution.line if solution else old.get(d.name, {}).get("solution", {}).get("line"),
                        },
                        "configuration": f"PalomarCorpus/{entry}/comparator.json",
                        "receipt": f"{config['replay']['receipts']}/receipt-{entry}.json",
                    })
                if len(checks) == len(decls) and decls:
                    comparator = {"status": "compared", "commit": corpus_commit, "run_id": run_id,
                                  "checks": checks}
            elif row["comparator"]["status"] == "pending":
                comparator = {"status": "pending"}
            mark = None
            if status in ("exact", "exact_or_stronger"):
                mark = "lean"
            elif status == "modulo_named_input":
                mark = "lean_dagger"
            results.append({
                "id": row["id"],
                "label": label,
                "anchor": anchor,
                "environment": env,
                "printed_kind": printed_kind,
                "number": number,
                "page": page,
                "source": row["source"],
                "statement_sha256": row["statement_sha256"],
                "statement_key": statement_keys.get(row["statement_sha256"]),
                "title": (statements.get(label) or (None, None))[0] if env else span_title(row),
                "statement_markdown": (statements.get(label) or (None, None))[1],
                "lean": {
                    "status": status,
                    "mark": mark,
                    "named_inputs": row["lean"].get("named_inputs"),
                    "named_input_definitions": [
                        {"name": u[0], "path": u[1], "line": u[2], "text": u[3]}
                        for u in (pin_definition(n) for n in (row["lean"].get("named_inputs") or [])) if u],
                    "scope": row["lean"].get("scope"),
                    "scope_markdown": tex_to_markdown(row["lean"].get("scope"), numbers_for_row_all),
                    "reason": row["lean"].get("reason"),
                    "reason_markdown": tex_to_markdown(row["lean"].get("reason"), numbers_for_row_all),
                    "relation_note": relation,
                    "declarations": [
                        {"name": d.name, "path": d.path, "line": d.line, "kind": d.kind,
                         "docstring": d.docstring, "statement": d.statement,
                         "statement_sha256": sha256_hex(d.normalised.encode()),
                         "unfolds": [{"name": u[0], "path": u[1], "line": u[2], "text": u[3]}
                                     for u in (d.unfolds or ((pin_definition(d.named, d.name),) if d.named and pin_definition(d.named, d.name) else ()))]}
                        for d in decls
                    ],
                },
                "comparator": comparator or {"status": row["comparator"]["status"]},
            })
            if row["comparator"]["status"] == "compared" and comparator is None:
                problems.add(where, "the ledger records a comparison this evidence cannot establish")
        papers_out.append({"paper_id": pid, "problem": paper["problem"], "side": paper["side"],
                           "results": results})

    expected = sum(len(v) for v in rows_by_paper.values())
    got = sum(len(p["results"]) for p in papers_out)
    if got != expected:
        problems.add("ledger", f"{expected - got} of {expected} rows have no resolved evidence")

    return {
        "schema": SCHEMA,
        "lean_repository": REPO_URL,
        "lean_pin": pin,
        "lean_toolchain": (here.text(pin, "lean-toolchain") or "").strip(),
        "mathlib": next((p.get("rev") for p in json.loads(here.text(pin, "lake-manifest.json") or "{}").get("packages", [])
                         if p.get("name") == "mathlib"), None),
        "corpus_repository": CORPUS_URL,
        "corpus_commit": corpus_commit,
        "corpus_archive_tag": config.get("corpus_archive_tag"),
        "replay": config["replay"],
        "permitted_axioms": PERMITTED_AXIOMS,
        "papers": papers_out,
    }


# --------------------------------------------------------------------------- rendering


def lean_url(pin: str, path: str, line: int) -> str:
    return f"{REPO_URL}/blob/{pin}/{path}#L{line}"


def corpus_url(commit: str, path: str, line: int | None = None) -> str:
    return f"{CORPUS_URL}/blob/{commit}/{path}" + (f"#L{line}" if line else "")


def record_url(record_commit: str, record: str, anchor: str) -> str:
    return f"{REPO_URL}/blob/{record_commit}/{record}#{anchor}"


# A record larger than this is split into one file per section of the paper, so that each
# page the margin marks open stays quick to load and within what GitHub renders.
SPLIT_BYTES = 300_000


def render_sidecar(evidence: dict, paper: dict, record_commit: str) -> str:
    pid = paper["paper_id"]
    lines = [
        "% Generated by scripts/paper_evidence.py from docs/paper_lean_coverage.json and the",
        "% Comparator replay receipts under evidence/comparator/.  Do not edit by hand.",
        f"\\newcommand{{\\evidencerecordurl}}{{{tex_url(f'{REPO_URL}/blob/{record_commit}/{RECORD_DIR}/{pid}.md')}}}",
    ]
    for r in paper["results"]:
        mark = r["lean"]["mark"]
        if mark is None:
            continue
        text = "Lean" if mark == "lean" else "Lean\\textsuperscript{\\dag}"
        decls = r["lean"]["declarations"]
        if len(decls) == 1:
            target = lean_url(evidence["lean_pin"], decls[0]["path"], decls[0]["line"])
        else:
            target = record_url(record_commit, r["record"], r["anchor"])
        cmp = ""
        if r["comparator"]["status"] == "compared":
            cmp = record_url(record_commit, r["record"], r["anchor"] + "-comparator")
        lines.append(f"\\DeclareResultEvidence{{{r['label']}}}{{{text}}}{{{tex_url(target)}}}{{{tex_url(cmp)}}}")
    return "\n".join(lines) + "\n"


def _md_code(text: str, lang: str = "lean") -> str:
    fence = "```"
    while fence in text:
        fence += "`"
    return f"{fence}{lang}\n{text}\n{fence}"


def result_heading(r: dict) -> str:
    kind = r["printed_kind"]
    number = f" {r['number']}" if r.get("number") else ""
    title = f" ({r['title']})" if r.get("title") else ""
    page = f", page {r['page']}" if r.get("page") else ""
    return f"{kind}{number}{title}{page}"


def record_header(evidence: dict, paper: dict, title: str, pdf_path: str, up: str) -> list[str]:
    pin = evidence["lean_pin"]
    commit = evidence["corpus_commit"]
    run = evidence["replay"]["run_id"]
    tag = evidence.get("corpus_archive_tag")
    counts = {"lean": 0, "lean_dagger": 0, None: 0}
    compared = 0
    for r in paper["results"]:
        counts[r["lean"]["mark"]] += 1
        compared += r["comparator"]["status"] == "compared"
    return [
        f"# Formal evidence: {title}",
        "",
        f"This record belongs to the paper [{Path(pdf_path).name}]({up}{pdf_path}). For every result it lists "
        "the Lean declarations that state it, and the independent Comparator check where there is one. "
        "The margin marks in the paper link here.",
        "",
        f"- **Lean.** Every declaration is quoted from [plectis-erdos]({REPO_URL}) at commit "
        f"[`{pin[:12]}`]({REPO_URL}/tree/{pin}) and is checked there by Lean's kernel "
        f"(`{evidence['lean_toolchain']}`, Mathlib `{(evidence.get('mathlib') or '')[:12]}`).",
        f"- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib "
        f"alone, as a *Challenge* in [plectis-erdos-lean]({CORPUS_URL}), and a *Solution* that uses our proof "
        f"was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms "
        f"that only the axioms {', '.join(f'`{a}`' for a in evidence['permitted_axioms'])} are used. "
        f"All checks below come from replay run [{run}]({CORPUS_URL}/actions/runs/{run}) at corpus commit "
        f"[`{commit[:12]}`]({CORPUS_URL}/tree/{commit})"
        + (f" (tag `{tag}`)" if tag else "") + "; both the default Lean kernel and the independent `nanoda` "
        "kernel accepted every entry. The replay's own report for each entry is kept in this repository and "
        "linked from each check. A Challenge shows `sorry` because it states the target without proving it.",
        f"- **Counts.** {len(paper['results'])} results: {counts['lean']} with a Lean proof of the whole statement, "
        f"{counts['lean_dagger']} whose Lean proof assumes a named input (marked with a dagger), "
        f"{counts[None]} without a Lean proof of the whole statement; {compared} compared.",
        "",
        "These checks establish that the stated propositions are proved. Whether each is the right "
        "proposition is for the reader to judge against the paper's statement, which is reproduced below.",
        "",
    ]


def render_results(evidence: dict, results: list[dict], up: str) -> list[str]:
    pin = evidence["lean_pin"]
    commit = evidence["corpus_commit"]
    run = evidence["replay"]["run_id"]
    out: list[str] = []
    for r in results:
        lean = r["lean"]
        out.append(f'<a id="{r["anchor"]}"></a>')
        out.append("")
        out.append(f"## {result_heading(r)}")
        out.append("")
        if r.get("statement_markdown"):
            out.append("> " + r["statement_markdown"].replace("\n", "\n> "))
            out.append("")
        status = lean["status"]
        decls = lean["declarations"]
        if status == "none":
            reason = lean.get("reason_markdown") or lean.get("reason") or ""
            out.append(f"**No Lean proof of the whole statement.** In Lean, {reason}.".rstrip()
                       if reason else "**No Lean proof of the whole statement.**")
            out.append("")
            continue
        many = len(decls) > 1
        if status == "exact":
            lead = ("The Lean declarations below together state this result."
                    if many else "The Lean declaration below states this result.")
        elif status == "exact_or_stronger":
            lead = ("The Lean declarations below together state a result at least as strong as this one."
                    if many else "The Lean declaration below states a result at least as strong as this one.")
            if lean.get("relation_note"):
                lead += " " + lean["relation_note"]
        else:
            inputs = ", ".join(f"`{n.rsplit('.', 1)[-1]}`" for n in (lean.get("named_inputs") or []))
            scope = lean.get("scope_markdown") or lean.get("scope") or "a named input"
            lead = (f"The Lean proof assumes {scope}. Lean takes this input as a hypothesis ({inputs}); "
                    "it is not proved in Lean.")
        out.append(lead)
        out.append("")
        for i, d in enumerate(decls, 1):
            prefix = f"{i}. " if many else ""
            out.append(f"{prefix}[`{d['name']}`]({lean_url(pin, d['path'], d['line'])})")
            out.append("")
            out.append(_md_code(d["statement"]))
            out.append("")
            for u in d.get("unfolds") or []:
                out.append(f"where [`{u['name'].rsplit('.', 1)[-1]}`]({lean_url(pin, u.get('path') or d['path'], u['line'])}) is")
                out.append("")
                out.append(_md_code(u["text"]))
                out.append("")
        for u in lean.get("named_input_definitions") or []:
            out.append(f"The assumed input [`{u['name'].rsplit('.', 1)[-1]}`]({lean_url(pin, u['path'], u['line'])}) is")
            out.append("")
            out.append(_md_code(u["text"]))
            out.append("")
        cmp = r["comparator"]
        out.append(f'<a id="{r["anchor"]}-comparator"></a>')
        out.append("")
        if cmp["status"] == "compared":
            out.append(f"**Comparator: passed** (run {run}, corpus commit `{commit[:12]}`).")
            out.append("")
            out.append("| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |")
            out.append("|---|---|---|---|")
            for c in cmp["checks"]:
                short = c["declaration"].rsplit(".", 1)[-1]
                ch, so = c["challenge"], c["solution"]
                out.append(
                    f"| `{short}` "
                    f"| [{ch['path'].rsplit('/', 2)[-2]}/Challenge.lean, line {ch['line']}]({corpus_url(commit, ch['path'], ch['line'])}) "
                    f"| [{so['path'].rsplit('/', 1)[-1]}, line {so['line']}]({corpus_url(commit, so['path'], so['line'])}) "
                    f"| [{c['entry']}]({up}{c['receipt']}) |")
            out.append("")
            different = [c for c in cmp["checks"] if c["challenge"].get("statement") and not c["challenge"].get("same_as_lean")]
            if len(different) < len(cmp["checks"]):
                out.append("Each Challenge states the same proposition as the Lean declaration it targets"
                           + (" except where shown below" if different else "")
                           + ", with every definition it uses restated from Mathlib alone.")
                out.append("")
            for c in different:
                out.append(f"Challenge for `{c['declaration'].rsplit('.', 1)[-1]}`:")
                out.append("")
                out.append(_md_code(c["challenge"]["statement"].rstrip() + " := by sorry"))
                out.append("")
        elif cmp["status"] == "pending":
            out.append("**Comparator:** not yet compared.")
            out.append("")
        else:
            out.append("**Comparator:** not applicable (no unconditional Lean proof of the whole statement).")
            out.append("")
    return out


def section_of(result: dict) -> str | None:
    number = result.get("number") or ""
    head = number.split(".", 1)[0]
    return head if head.isdigit() else None


def paper_records(evidence: dict, paper: dict, title: str, pdf_path: str) -> dict[str, str]:
    """The paper's record file(s), and each result's record path set in place."""
    pid = paper["paper_id"]
    single = f"{RECORD_DIR}/{pid}.md"
    body = record_header(evidence, paper, title, pdf_path, "../") + render_results(evidence, paper["results"], "../")
    text = "\n".join(body).rstrip() + "\n"
    if len(text.encode()) <= SPLIT_BYTES:
        for r in paper["results"]:
            r["record"] = single
        return {single: text}
    sections: list[tuple[str, list[dict]]] = []
    current = None
    for r in paper["results"]:
        key = section_of(r) or current or "0"
        if not sections or sections[-1][0] != key:
            sections.append((key, []))
        sections[-1][1].append(r)
        current = key
    # A section whose record is still large is divided into consecutive parts.
    groups: list[tuple[str, str, list[dict]]] = []
    for key, rows in sections:
        size = len("\n".join(render_results(evidence, rows, "../../")).encode())
        parts = max(1, -(-size // (SPLIT_BYTES // 2)))
        if parts == 1:
            groups.append((f"section-{key}", f"Section {key}", rows))
            continue
        per = -(-len(rows) // parts)
        for i in range(parts):
            chunk = rows[i * per:(i + 1) * per]
            if not chunk:
                continue
            first, last = chunk[0].get("number") or "", chunk[-1].get("number") or ""
            groups.append((f"section-{key}-{i + 1}", f"Section {key}, results {first} to {last}", chunk))
    files: dict[str, str] = {}
    index = record_header(evidence, paper, title, pdf_path, "../")
    index += ["The record is divided by section of the paper.", "",
              "| Part | Results | With a Lean proof | Compared |", "|---|---|---|---|"]
    for stem, caption, rows in groups:
        rel = f"{RECORD_DIR}/{pid}/{stem}.md"
        for r in rows:
            r["record"] = rel
        lean = sum(r["lean"]["mark"] is not None for r in rows)
        cmp = sum(r["comparator"]["status"] == "compared" for r in rows)
        index.append(f"| [{caption}]({pid}/{stem}.md) | {len(rows)} | {lean} | {cmp} |")
        part = [f"# Formal evidence: {title}, {caption}", "",
                f"Part of the [evidence record](../{pid}.md) of the paper "
                f"[{Path(pdf_path).name}](../../{pdf_path}), which explains what the Lean and Comparator "
                "checks establish.", ""]
        part += render_results(evidence, rows, "../../")
        files[rel] = "\n".join(part).rstrip() + "\n"
    files[single] = "\n".join(index).rstrip() + "\n"
    return files


def paper_titles(root: Path) -> dict[str, tuple[str, str]]:
    """paper_id -> (title, repository PDF path) from the publication contract."""
    contract = load_json(root / "docs/publication_contract.json")
    out = {}
    for artifact in contract.get("artifacts", []):
        stem = Path(str(artifact.get("storage_path") or artifact.get("rendered_path") or "")).stem
        if stem:
            out[stem] = (artifact.get("title") or stem, artifact.get("storage_path") or artifact.get("rendered_path"))
    return out


def outputs(root: Path, evidence: dict, record_commit: str) -> dict[str, str]:
    titles = paper_titles(root)
    files: dict[str, str] = {}
    for paper in evidence["papers"]:
        pid = paper["paper_id"]
        title, pdf = titles.get(pid, (pid, f"paper/{pid}.pdf"))
        files.update(paper_records(evidence, paper, title, pdf))
        files[f"{SIDECAR_DIR}/{pid}.tex"] = render_sidecar(evidence, paper, record_commit)
    files[EVIDENCE_MAP] = json.dumps(evidence, indent=1, ensure_ascii=False) + "\n"
    return files


def write_atomically(root: Path, files: dict[str, str]) -> None:
    staged = []
    for rel, text in files.items():
        target = root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp = tempfile.mkstemp(dir=target.parent, prefix=".paper_evidence.")
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(text)
        staged.append((tmp, target))
    for tmp, target in staged:
        os.replace(tmp, target)


# --------------------------------------------------------------------------- CLI


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    b = sub.add_parser("build")
    b.add_argument("--corpus-repo", type=Path, required=True)
    b.add_argument("--aux-dir", type=Path)
    b.add_argument("--record-commit")
    b.add_argument("--allow-missing-relations", action="store_true")
    c = sub.add_parser("check")
    c.add_argument("--corpus-repo", type=Path)
    for p in (b, c):
        p.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    root = args.root
    problems = Problems()
    config = load_json(root / CONFIG)
    previous = load_json(root / EVIDENCE_MAP) if (root / EVIDENCE_MAP).is_file() else None
    corpus = Repo(args.corpus_repo) if getattr(args, "corpus_repo", None) else None
    if args.command == "build":
        record_commit = args.record_commit or config.get("record_commit")
        if not record_commit:
            problems.add("config", "no record commit: pass --record-commit or set record_commit")
        evidence = resolve(root, corpus, args.aux_dir, previous, problems,
                           require_relations=not args.allow_missing_relations)
        if problems.items:
            for item in problems.items:
                print("FAIL", item, file=sys.stderr)
            print(f"{len(problems.items)} problems; nothing written", file=sys.stderr)
            return 1
        write_atomically(root, outputs(root, evidence, record_commit))
        n = sum(len(p["results"]) for p in evidence["papers"])
        print(f"wrote evidence for {n} results in {len(evidence['papers'])} papers")
        return 0
    # check
    record_commit = config.get("record_commit")
    if not record_commit:
        problems.add("config", "record_commit is not set")
    if previous is None:
        problems.add(EVIDENCE_MAP, "missing")
        return report(problems)
    if corpus is not None:
        # Full check: resolve everything again against the corpus; numbering is taken from
        # the committed map (the rendered-PDF check verifies it against the PDFs).
        evidence = resolve(root, corpus, None, previous, problems, require_relations=True)
    else:
        # Offline check: the committed map must agree with the ledger row for row, and every
        # output must be what the map renders to.
        evidence = previous
        ledger = load_json(root / LEDGER)
        mapped = {r["id"]: r for p in previous["papers"] for r in p["results"]}
        if previous.get("lean_pin") != ledger["lean_pin"]:
            problems.add(EVIDENCE_MAP, "was resolved at a different Lean pin than the ledger's")
        for row in ledger["rows"]:
            r = mapped.pop(row["id"], None)
            if r is None:
                problems.add(row["id"], "has no entry in the evidence map")
                continue
            if r["statement_sha256"] != row["statement_sha256"] or r["label"] != row["label"]:
                problems.add(row["id"], "the evidence map was resolved against a different statement")
            if r["lean"]["status"] != row["lean"]["status"] or \
                    [d["name"] for d in r["lean"]["declarations"]] != [d["name"] for d in row["lean"].get("declarations", [])]:
                problems.add(row["id"], "the evidence map records different Lean evidence than the ledger")
            if r["comparator"]["status"] != row["comparator"]["status"]:
                problems.add(row["id"], "the evidence map records a different Comparator status than the ledger")
        for extra in mapped:
            problems.add(extra, "is in the evidence map but not in the ledger")
    expected = outputs(root, json.loads(json.dumps(evidence)), record_commit or "")
    for rel, text in expected.items():
        path = root / rel
        if not path.is_file() or path.read_text(encoding="utf-8") != text:
            problems.add(rel, "differs from what the inputs generate; run paper_evidence.py build")
    for path in sorted((root / RECORD_DIR).rglob("*.md")) + sorted((root / SIDECAR_DIR).glob("*.tex")):
        rel = path.relative_to(root).as_posix()
        if rel not in expected and rel != f"{RECORD_DIR}/README.md":
            problems.add(rel, "is not generated from the current evidence; delete it")
    here = Repo(root)
    if record_commit and here.has_commit(record_commit):
        for rel, text in expected.items():
            if rel.startswith(RECORD_DIR + "/") and rel.endswith(".md") and here.text(record_commit, rel) != text:
                problems.add(rel, f"the papers link the record at {record_commit[:12]}, which differs from "
                                  "the current record: rebuild the evidence and the papers")
    elif record_commit:
        problems.add("config", f"record_commit {record_commit} is not in this repository's history")
    return report(problems)


def report(problems: Problems) -> int:
    for item in problems.items:
        print("FAIL", item, file=sys.stderr)
    if problems.items:
        print(f"{len(problems.items)} problems", file=sys.stderr)
        return 1
    print("paper evidence current")
    return 0


if __name__ == "__main__":
    sys.exit(main())
