#!/usr/bin/env python3
"""Build the argument-continuation projection from the kernel export.

Input: the JSON Lines stream written by ``scripts/export_argument_continuations.lean``
(the CI artifact ``argument-continuations-<sha>``, gzip or plain). The artifact
also carries ``argument_continuations_lean_tree.txt`` (the git tree id of
``lean/`` at the exported commit) and ``argument_continuations_source_revision.txt``;
the builder reads both from beside the export, or takes ``--lean-tree`` and
``--source-revision``.

Output:

* ``docs/argument_continuations.json``: the bounded projection a reader or a
  research agent opens first (per-problem open statements, disguise classes,
  reduction frontier, leverage, refutations, idle hypotheses), with every row
  carrying its producers;
* ``docs/argument_continuations_graph.json.gz``: the full graph.

Semantics. Edges come from ``match`` rows (corpus theorems whose conclusion
the elaborator's unifier, ``Meta.isDefEq``, matched against a statement), from
theorem telescopes, and from the kernel-checked ``battery`` and ``idle`` rows.
Declaration names join papers and Comparator results and, as a last resort,
attribute a theorem to a problem; they never create an edge.

* A *reduction* of a closed statement ``S`` is a corpus theorem ``T`` that
  supplies ``S`` once its residual hypotheses ``R₁ … Rₖ`` are supplied. A
  theorem whose conclusion is closed is a reduction of its conclusion. Its
  residuals are its closed proposition binders (instance binders included)
  and, for each data binder whose type the export could not show inhabited,
  the closed statement ``Nonempty T``. A theorem with an obligation that no
  closed statement expresses (a proposition binder that mentions another
  binder, or a data binder of unknown inhabitation whose type mentions another
  binder) is recorded as existential and gives no reduction.
* An ``idle`` row says a theorem's proof never uses some proposition binders
  and the kernel accepted the statement without them; it gives a reduction of
  the conclusion whose residuals omit those binders.
* ``S`` is *supplied* when some reduction has every residual supplied (least
  fixpoint). The witness reduction is recorded, so every supplied statement
  has a witness chain of corpus theorems joined by unification.
* ``S`` is *refuted* when a corpus theorem proving ``¬S`` has every residual
  supplied or the battery proves ``¬S`` (a kernel refutation), or when
  supplying ``S`` would supply a refuted statement through recorded reductions
  (a derived refutation, recorded with the refuted statement it reaches).
  *Open* statements are the statements neither supplied nor refuted.
* After supplied residuals are removed, a reduction with one residual ``A``
  is an implication ``A ⇒ S``. A strongly connected component of that graph
  with two or more open statements is a *disguise class*: its members are
  equivalent through recorded reductions, so moving between them is a change
  of coordinates.
* The *bundles* of an open statement are the minimal sets of open statements
  whose supply supplies it (AND over residuals, OR over reductions, subset
  absorption, and a budget reported as ``truncated``).
* The *leverage* of an open statement ``A`` is the set of open statements that
  become supplied when ``A`` is added and the fixpoint is recomputed.

The producer relation is a lower bound (see the exporter's docstring); a
statement reported open may be supplied by an argument the export did not
try. Leverage and bundles inherit that bound. Nothing here is proof
authority: the kernel theorems each row cites are.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "erdos249257-argument-continuations/2"
GRAPH_SCHEMA = "erdos249257-argument-continuation-graph/2"
DEFAULT_OUTPUT = ROOT / "docs" / "argument_continuations.json"
DEFAULT_GRAPH_OUTPUT = ROOT / "docs" / "argument_continuations_graph.json.gz"
LEAN_TREE_FILE = "argument_continuations_lean_tree.txt"
SOURCE_REVISION_FILE = "argument_continuations_source_revision.txt"
PROBLEMS = ("68", "243", "249", "251", "257", "269", "1041", "1049")
BUNDLE_LIMIT = 24
BUNDLE_SIZE_LIMIT = 4
BUNDLE_DEPTH_LIMIT = 6
BUNDLE_WORK_LIMIT = 4000
BUNDLE_CONE_LIMIT = 4000
REFUTATION_WORK_LIMIT = 2_000_000
LIST_LIMIT = 40

# Declaration-name tokens used only to attribute shared-library theorems
# (namespace Erdos249257) to one of its two problems when no paper row
# attributes them. Attribution is navigation; it never changes the graph.
PROBLEM_257_TOKENS = ("Mersenne", "Half", "Greedy", "TwentyOne", "Achievement", "Seam", "Skip", "Erdos257")
PROBLEM_249_TOKENS = ("Totient", "Phi", "totient", "phi", "Erdos249")

# An export written before the per-binder "inhabited" flag does not say whether
# a data binder's type is inhabited. For such rows the builder assumes
# inhabitation only for these types (each has an evident element: 0, false,
# True, the empty set, finset or list, PUnit) and for function types into them
# (a constant function); any other data binder of an old export makes its
# theorem existential.
ASSUMED_INHABITED_TYPES = frozenset({
    "ℕ", "Nat", "ℤ", "Int", "ℚ", "Rat", "ℝ", "Real", "ℂ", "Complex", "Bool", "Prop", "Type"})
ASSUMED_INHABITED_PREFIXES = ("Set ", "Finset ", "List ", "Type ", "Sort ")
TREE_ID = re.compile(r"^[0-9a-f]{40}([0-9a-f]{24})?$")


# --------------------------------------------------------------------------
# Loading


def read_export(path: Path) -> list[dict[str, Any]]:
    opener = gzip.open if path.suffix == ".gz" else open
    rows: list[dict[str, Any]] = []
    with opener(path, "rt", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as error:
                if not line.endswith("\n"):
                    print(f"warning: {path}:{line_number}: dropping a partially written final line",
                          file=sys.stderr)
                    break
                raise SystemExit(f"{path}:{line_number}: invalid JSON line: {error}") from error
    if not rows or rows[0].get("record") != "meta":
        raise SystemExit(f"{path}: export does not start with a meta record")
    if rows[0].get("schema") != "plectis-argument-continuation-export/1":
        raise SystemExit(f"{path}: unexpected export schema {rows[0].get('schema')!r}")
    if not any(row.get("record") == "summary" for row in rows):
        # A stream cut off by the CI backstop: keep what was exported and say so.
        print(f"warning: {path} has no summary record; treating the export as truncated", file=sys.stderr)
        rows.append({"record": "summary", "truncated": True, "cut_off_before_summary": True,
                     "theorems": sum(1 for row in rows if row.get("record") == "theorem")})
    return rows


def file_digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> Any:
    if not path.is_file():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _first_token(path: Path) -> str | None:
    text = path.read_text(encoding="utf-8").strip()
    return text.split()[0] if text else None


def resolve_lean_tree(export_path: Path, explicit: str | None) -> str | None:
    """The git tree id of ``lean/`` the export was computed from: ``--lean-tree``
    (an id, or a file holding one), else the artifact's side file."""
    if explicit:
        candidate = Path(explicit)
        value = _first_token(candidate) if candidate.is_file() else explicit.strip()
    else:
        side = export_path.parent / LEAN_TREE_FILE
        value = _first_token(side) if side.is_file() else None
    if value is not None and not TREE_ID.match(value):
        raise SystemExit(f"lean tree id {value!r} is not a git object id")
    return value


def resolve_source_revision(export_path: Path, explicit: str | None) -> str | None:
    """The commit the export ran on, recorded as provenance only: CI exports a
    pull request's merge commit, which a local checkout usually lacks."""
    if explicit:
        return explicit.strip() or None
    side = export_path.parent / SOURCE_REVISION_FILE
    return _first_token(side) if side.is_file() else None


# --------------------------------------------------------------------------
# Joins


def source_refs(root: Path) -> dict[str, str]:
    index = load_json(root / "docs" / "lean_dependency_index.json")
    out: dict[str, str] = {}
    if not index:
        return out
    for node in index.get("nodes", []):
        handle = node.get("handle")
        ref = node.get("source_ref")
        if handle and ref:
            out[handle] = ref
    return out


def paper_rows(root: Path) -> dict[str, list[dict[str, Any]]]:
    coverage = load_json(root / "docs" / "paper_lean_coverage.json")
    out: dict[str, list[dict[str, Any]]] = defaultdict(list)
    if not coverage:
        return out
    for row in coverage.get("rows", []):
        lean = row.get("lean") or {}
        comparator = row.get("comparator") or {}
        for declaration in lean.get("declarations", []) or []:
            name = declaration.get("name")
            if not name:
                continue
            out[name].append({
                "row": row.get("id"),
                "problem": str(row["problem"]) if row.get("problem") is not None else None,
                "paper": row.get("paper_id"),
                "side": row.get("side"),
                "label": row.get("label"),
                "source": row.get("source"),
                "lean_status": lean.get("status"),
                "comparator": comparator.get("status"),
            })
    return out


def comparator_results(root: Path) -> dict[str, dict[str, Any]]:
    packet = load_json(root / "docs" / "external_verification_packet.json")
    out: dict[str, dict[str, Any]] = {}
    if not packet:
        return out
    for result in packet.get("main_results", []) or []:
        name = result.get("original_declaration")
        if name:
            out[name] = {
                "id": result.get("id"),
                "wrapper": result.get("wrapper_declaration"),
                "boundary": result.get("boundary"),
            }
    return out


def semantic_problems(root: Path) -> dict[str, str]:
    """Declaration -> problem, from the semantic corpus's authored evidence."""
    handles = dependency_handles(root)
    out: dict[str, str] = {}
    for node in semantic_nodes(root):
        problem = node.get("problem")
        if problem not in PROBLEMS:
            continue
        for evidence in node.get("evidence", []) or []:
            handle = handles.get(f"lean/{evidence.get('module')}:{evidence.get('line')}")
            if handle:
                out.setdefault(handle, problem)
    return out


def module_problem(module: str, name: str) -> str | None:
    match = re.search(r"\.Erdos(\d+)(?:\.|$)", "." + module)
    if match and match.group(1) in PROBLEMS:
        return match.group(1)
    # The shared library is named Erdos249257, which contains the token
    # "Erdos249"; strip it before reading tokens, or everything in it would look
    # like Problem 249.
    text = (module + "." + name).replace("Erdos249257", "")
    hits_257 = any(token in text for token in PROBLEM_257_TOKENS)
    hits_249 = any(token in text for token in PROBLEM_249_TOKENS)
    if hits_257 and not hits_249:
        return "257"
    if hits_249 and not hits_257:
        return "249"
    if module.startswith("Erdos249257") or hits_257 or hits_249:
        return "249_257"
    return None


# --------------------------------------------------------------------------
# Binders


def _split_top_level_arrows(text: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in "([{⦃⟨":
            depth += 1
        elif char in ")]}⦄⟩":
            depth -= 1
        elif depth == 0 and text.startswith(" → ", index):
            parts.append(text[start:index])
            start = index + 3
            index += 3
            continue
        index += 1
    parts.append(text[start:])
    return [part.strip() for part in parts]


def assumed_inhabited(type_text: str | None) -> bool:
    """Whether an old export's data binder type is assumed inhabited (see
    ``ASSUMED_INHABITED_TYPES``)."""
    if not type_text:
        return False
    text = type_text.strip()
    while True:
        codomain = _split_top_level_arrows(text)[-1]
        while codomain.startswith("(") and codomain.endswith(")"):
            codomain = codomain[1:-1].strip()
        if codomain == text:
            break
        text = codomain
    return text in ASSUMED_INHABITED_TYPES or text.startswith(ASSUMED_INHABITED_PREFIXES)


def binder_obligation(binder: dict[str, Any]) -> tuple[str, str | None, str | None, bool]:
    """What a theorem binder asks of anyone applying the theorem.

    Returns ``(role, key, text, is_prop)``. The role is ``"free"`` (nothing to
    supply: a data or instance binder whose type is known to be inhabited),
    ``"residual"`` (the closed statement ``key`` must be supplied: a closed
    proposition, or ``Nonempty T`` for a closed data type ``T`` not known to be
    inhabited) or ``"schematic"`` (an obligation that mentions another binder,
    so no closed statement expresses it)."""
    kind = binder.get("kind")
    prop = binder.get("prop")
    if prop is None:  # an export written before the per-binder "prop" flag
        if kind == "hypothesis":
            prop = True
        elif kind == "instance" and binder.get("key"):
            prop = True
        elif kind == "instance":
            # Such an export keys no schematic proposition and flags no data
            # instance as inhabited, so this binder's obligation is unknown.
            return "schematic", None, binder.get("type"), True
        else:
            prop = False
    if prop:
        if binder.get("closed") and binder.get("key"):
            return "residual", binder["key"], binder.get("type"), True
        return "schematic", None, binder.get("type"), True
    inhabited = binder.get("inhabited")
    if inhabited is None:
        inhabited = kind == "data" and assumed_inhabited(binder.get("type"))
    if inhabited:
        return "free", None, None, False
    witness = binder.get("nonempty_type") or f"Nonempty ({binder.get('type')})"
    if binder.get("nonempty_key"):
        return "residual", binder["nonempty_key"], witness, False
    return "schematic", None, witness, False


def obligations(binders: Iterable[dict[str, Any]]) -> dict[str, list[Any]]:
    residuals: list[tuple[str, str | None]] = []
    schematic_props: list[str | None] = []
    schematic_witnesses: list[str | None] = []
    for binder in binders:
        role, key, text, is_prop = binder_obligation(binder)
        if role == "residual":
            residuals.append((key, text))
        elif role == "schematic":
            (schematic_props if is_prop else schematic_witnesses).append(text)
    return {"residuals": residuals, "schematic_props": schematic_props,
            "schematic_witnesses": schematic_witnesses}


def existential_reason(found: dict[str, list[Any]]) -> str:
    reasons = []
    if found["schematic_props"]:
        reasons.append("a proposition binder mentions another binder")
    if found["schematic_witnesses"]:
        reasons.append("a data binder is not known to be inhabited and its type mentions another binder")
    return "; ".join(reasons)


# --------------------------------------------------------------------------
# Graph


class Graph:
    def __init__(self, rows: list[dict[str, Any]], *, include_battery: bool = True,
                 include_idle: bool = True):
        self.include_battery = include_battery
        self.include_idle = include_idle
        self.meta = rows[0] if rows else {}
        self.summary = next((row for row in rows if row.get("record") == "summary"), {})
        self.theorems: dict[str, dict[str, Any]] = {}
        self.statements: dict[str, dict[str, Any]] = {}
        # reduction: (head, producer, reading, residual keys tuple)
        self.reductions: list[tuple[str, str, str, tuple[str, ...]]] = []
        self.existential: list[dict[str, Any]] = []
        self.existential_refutations = 0
        self.budget_exhausted: list[dict[str, Any]] = []
        self.caps: list[dict[str, Any]] = []
        self.errors: list[dict[str, Any]] = []
        self.alias: dict[str, str] = {}
        self.compositions_checked: list[dict[str, Any]] = []
        # refutation: (statement, producer, reading, residual keys)
        self.refutations: list[tuple[str, str, str, tuple[str, ...]]] = []
        # kernel-checked idle rows, each with what the graph made of it
        self.idle: list[dict[str, Any]] = []
        self.idle_unchecked = 0
        self._ingest(rows)

    def canon(self, key: str) -> str:
        """Representative of a statement's definitional-alias class."""
        root = key
        while self.alias.get(root, root) != root:
            root = self.alias[root]
        while self.alias.get(key, key) != root:
            self.alias[key], key = root, self.alias[key]
        return root

    @classmethod
    def from_payload(cls, payload: dict[str, Any], *, include_idle: bool = True) -> "Graph":
        """Rebuild the graph from ``argument_continuations_graph.json.gz``."""
        graph = cls([], include_battery=True, include_idle=include_idle)
        graph.meta = {"schema": payload.get("schema")}
        graph.summary = (payload.get("source") or {}).get("export_summary", {})
        for row in payload.get("statements", []):
            graph.statements[row["key"]] = {
                "key": row["key"], "type": row.get("type"), "origins": set(row.get("origins", [])),
                "consumers": set(row.get("consumers", [])), "conclusion_of": set(row.get("conclusion_of", [])),
                "constants": set(row.get("constants", [])),
                "aliases": set(row.get("aliases", [])),
            }
        for row in payload.get("reductions", []):
            reading = row.get("reading", "conclusion")
            if reading == "idle" and not include_idle:
                continue
            graph.reductions.append((row["statement"], row["producer"], reading, tuple(row.get("residuals", []))))
        for row in payload.get("theorems", []):
            graph.theorems[row["name"]] = {
                "name": row["name"], "module": row.get("module", ""),
                "hypotheses": row.get("hypotheses", []),
                "schematic_hypotheses": row.get("schematic_hypotheses", []),
                "witness_obligations": row.get("witness_obligations", []),
                "after_idle": row.get("after_idle") if include_idle else None,
                "conclusion_key": row.get("conclusion"), "conclusion_type": row.get("conclusion_type"),
                "conclusion_closed": row.get("conclusion") is not None, "data_binders": [],
                "card": {k: row[k] for k in ("source", "papers", "comparator_result", "problem") if k in row},
            }
        for row in payload.get("refutations", []):
            graph.refutations.append((row["statement"], row["producer"], row.get("reading", "conclusion"),
                                      tuple(row.get("residuals", []))))
        graph.existential = payload.get("existential_reductions", [])
        graph.budget_exhausted = payload.get("budget_exhausted", [])
        graph.idle = [dict(entry) for entry in payload.get("idle", [])] if include_idle else []
        return graph

    def _statement(self, key: str, type_text: str | None, origin: str,
                   constants: Iterable[str] = ()) -> dict[str, Any]:
        representative = self.canon(key)
        if representative != key:
            node = self._statement(representative, None, origin, constants)
            if type_text:
                node["aliases"].add(type_text)
            return node
        node = self.statements.get(key)
        if node is None:
            node = {"key": key, "type": type_text, "origins": set(), "consumers": set(),
                    "conclusion_of": set(), "constants": set(), "aliases": set()}
            self.statements[key] = node
        if type_text and not node.get("type"):
            node["type"] = type_text
        node["origins"].add(origin)
        node["constants"].update(constants)
        return node

    def _ingest(self, rows: list[dict[str, Any]]) -> None:
        seen_reductions: set[tuple[str, str, str, tuple[str, ...]]] = set()
        # Definitional aliases first: a named proposition and its one-step
        # unfolding are one statement. The named side represents the class.
        for row in rows:
            if row.get("record") == "unfold":
                named, unfolded = self.canon(row["statement"]), self.canon(row["unfolded"])
                if named != unfolded:
                    self.alias[unfolded] = named
        canon = self.canon

        def add_reduction(head: str, producer: str, reading: str, residuals: Iterable[str]) -> bool:
            head = canon(head)
            residual_tuple = tuple(sorted({canon(r) for r in residuals}))
            if head in residual_tuple:
                return False  # tautological: the statement reduces to itself
            item = (head, producer, reading, residual_tuple)
            if item not in seen_reductions:
                seen_reductions.add(item)
                self.reductions.append(item)
            return True

        binders_of: dict[str, list[dict[str, Any]]] = {}
        idle_rows: list[dict[str, Any]] = []
        for row in rows:
            record = row.get("record")
            if record == "theorem":
                name = row["name"]
                binders = row.get("binders", [])
                binders_of[name] = binders
                conclusion = row.get("conclusion", {})
                found = obligations(binders)
                self.theorems[name] = {
                    "name": name,
                    "module": row.get("module", ""),
                    # Closed obligations: proposition binders (instance binders
                    # included) and Nonempty statements for data binders.
                    "hypotheses": [canon(key) for key, _ in found["residuals"]],
                    "schematic_hypotheses": found["schematic_props"],
                    "witness_obligations": found["schematic_witnesses"],
                    "after_idle": None,
                    "conclusion_key": canon(conclusion["key"]) if conclusion.get("key") else None,
                    "conclusion_type": conclusion.get("type"),
                    "conclusion_closed": bool(conclusion.get("closed")),
                    "data_binders": [b.get("name") for b in binders if b.get("kind") == "data"],
                }
                for key, text in found["residuals"]:
                    node = self._statement(key, text, "hypothesis")
                    node["consumers"].add(name)
                if conclusion.get("closed") and conclusion.get("key"):
                    node = self._statement(conclusion["key"], conclusion.get("type"), "conclusion",
                                           conclusion.get("constants", ()))
                    node["conclusion_of"].add(name)
                    if found["schematic_props"] or found["schematic_witnesses"]:
                        self.existential.append({
                            "statement": canon(conclusion["key"]), "producer": name,
                            "reason": existential_reason(found),
                        })
                    else:
                        add_reduction(conclusion["key"], name, "theorem",
                                      [key for key, _ in found["residuals"]])
            elif record == "statement":
                self._statement(row["key"], row.get("type"), row.get("origin", "statement"),
                                row.get("constants", ()))
            elif record == "unfold":
                self._statement(row["unfolded"], row.get("type"), "unfolding", row.get("constants", ()))
            elif record == "match":
                status = row.get("status")
                if status != "matched":
                    self.budget_exhausted.append({
                        "statement": row.get("statement"), "producer": row.get("producer"),
                        "status": status, "search": "match",
                    })
                    continue
                residuals = row.get("residuals", [])
                if row.get("open_data") or any(r.get("has_open_data") or not r.get("key") for r in residuals):
                    # A producer argument unification left open: the residuals
                    # name metavariables, so none of them is a statement.
                    self.existential.append({
                        "statement": canon(row["statement"]), "producer": row["producer"],
                        "reason": "producer data not determined by unification",
                        "residual_types": [r.get("type") for r in residuals],
                    })
                    continue
                for residual in residuals:
                    self._statement(residual["key"], residual.get("type"), "residual")
                add_reduction(row["statement"], row["producer"], row.get("reading", "conclusion"),
                              [r["key"] for r in residuals])
            elif record == "battery" and self.include_battery and row.get("kernel_checked"):
                # A standard closing tactic proved the statement and the kernel
                # accepted the proof: a residual-free reduction.
                self._statement(row["statement"], None, "battery")
                add_reduction(row["statement"], f"tactic:{row.get('tactic')}", "battery", ())
            elif record == "composition":
                self.compositions_checked.append(row)
            elif record == "refutation":
                if row.get("status") != "matched":
                    self.budget_exhausted.append({
                        "statement": row.get("statement"), "producer": row.get("producer"),
                        "status": row.get("status"), "search": "refutation",
                    })
                    continue
                residuals = row.get("residuals", [])
                if row.get("open_data") or any(r.get("has_open_data") or not r.get("key") for r in residuals):
                    self.existential_refutations += 1
                    continue
                for residual in residuals:
                    self._statement(residual["key"], residual.get("type"), "residual")
                self.refutations.append((canon(row["statement"]), row["producer"],
                                         row.get("reading", "conclusion"),
                                         tuple(sorted({canon(r["key"]) for r in residuals}))))
            elif record == "battery_refutation" and self.include_battery and row.get("kernel_checked"):
                self.refutations.append((canon(row["statement"]), f"tactic:{row.get('tactic')}", "battery", ()))
            elif record == "idle" and self.include_idle:
                if row.get("kernel_checked"):
                    idle_rows.append(row)
                else:
                    self.idle_unchecked += 1
            elif record == "candidate_cap":
                self.caps.append(row)
            elif record in ("theorem_error", "statement_error"):
                self.errors.append(row)
        for row in idle_rows:
            self._ingest_idle(row, binders_of.get(row.get("theorem")), add_reduction)

    def _ingest_idle(self, row: dict[str, Any], binders: list[dict[str, Any]] | None, add_reduction) -> None:
        """A kernel-checked idle row: the theorem holds without the dropped
        proposition binders. Its conclusion gets a reduction whose residuals
        are the obligations of the binders that remain (dropped by index, so a
        repeated hypothesis is dropped only where the proof ignores it)."""
        canon = self.canon
        name = row.get("theorem")
        theorem = self.theorems.get(name)
        dropped_rows = row.get("dropped", []) or []
        dropped_index = {d.get("i") for d in dropped_rows}
        entry: dict[str, Any] = {
            "theorem": name,
            "type": row.get("type"),
            "dropped": [{"i": d.get("i"), "type": d.get("type"),
                         "key": canon(d["key"]) if d.get("key") else None} for d in dropped_rows],
            "conclusion": theorem.get("conclusion_key") if theorem else None,
            "residuals": [],
            "reduction": False,
            "reason": None,
        }
        if theorem is None or binders is None:
            entry["reason"] = "no theorem row"
        else:
            remaining = obligations(b for b in binders if b.get("i") not in dropped_index)
            residuals = sorted({canon(key) for key, _ in remaining["residuals"]})
            schematic = bool(remaining["schematic_props"] or remaining["schematic_witnesses"])
            entry["residuals"] = residuals
            theorem["after_idle"] = {"hypotheses": residuals, "schematic": schematic}
            if not (theorem["conclusion_closed"] and theorem["conclusion_key"]):
                entry["reason"] = "conclusion mentions a binder"
            elif schematic:
                entry["reason"] = "an obligation that mentions another binder remains"
            else:
                entry["reduction"] = add_reduction(theorem["conclusion_key"], name, "idle", residuals)
                if not entry["reduction"]:
                    entry["reason"] = "tautological"
        # An export that keys the stronger statement itself: that statement is
        # a theorem outright, whatever binders remain in it.
        if row.get("key"):
            node = self._statement(row["key"], row.get("type"), "idle")
            node["conclusion_of"].add(name)
            entry["statement"] = canon(row["key"])
            add_reduction(row["key"], name, "idle", ())
        self.idle.append(entry)

    # ------------------------------------------------------------------
    # Supply fixpoint with witnesses

    def supply(self, extra: Iterable[str] = (), *, exclude_heads: frozenset[str] = frozenset(),
               exclude_producers: frozenset[str] = frozenset(),
               exclude_readings: frozenset[str] = frozenset()) -> tuple[set[str], dict[str, int]]:
        def usable(index: int) -> bool:
            head, producer, reading, _ = self.reductions[index]
            return (head not in exclude_heads and producer not in exclude_producers
                    and reading not in exclude_readings)

        remaining = [len(residuals) for (_, _, _, residuals) in self.reductions]
        by_residual: dict[str, list[int]] = defaultdict(list)
        for index, (_, _, _, residuals) in enumerate(self.reductions):
            if not usable(index):
                continue
            for residual in residuals:
                by_residual[residual].append(index)
        supplied: set[str] = set()
        witness: dict[str, int] = {}
        queue: list[str] = []
        for index, (head, _, _, residuals) in enumerate(self.reductions):
            if not usable(index):
                continue
            if not residuals and head not in supplied:
                supplied.add(head)
                witness[head] = index
                queue.append(head)
        for key in extra:
            if key not in supplied:
                supplied.add(key)
                witness[key] = -1
                queue.append(key)
        while queue:
            key = queue.pop()
            for index in by_residual.get(key, ()):
                remaining[index] -= 1
                if remaining[index] == 0:
                    head = self.reductions[index][0]
                    if head not in supplied:
                        supplied.add(head)
                        witness[head] = index
                        queue.append(head)
        return supplied, witness

    # ------------------------------------------------------------------
    # Refutation

    def _kernel_refutations(self, supplied: set[str]) -> dict[str, tuple[str, str]]:
        refuted: dict[str, tuple[str, str]] = {}
        for statement, producer, reading, residuals in self.refutations:
            if statement not in refuted and all(r in supplied for r in residuals):
                refuted[statement] = (producer, reading)
        return refuted

    def _derived_refutations(self, supplied: set[str], kernel: dict[str, Any], *,
                             exclude_readings: frozenset[str] = frozenset()
                             ) -> tuple[dict[str, dict[str, Any]], bool]:
        """Statements whose supply would supply a refuted statement through the
        recorded reductions (so they are refuted too), with the statement each
        reaches and the producers on the way. First the contrapositive of every
        implication (a reduction left with one unsupplied residual), iterated
        backwards to a fixpoint; then, for each remaining statement of the
        backward cone, the forward closure, which also covers reductions whose
        other residuals that statement supplies."""
        refuted = set(kernel)
        derived: dict[str, dict[str, Any]] = {}
        need: dict[int, int] = {}
        by_residual: dict[str, list[int]] = defaultdict(list)
        into: dict[str, list[int]] = defaultdict(list)
        for index, (head, _, reading, residuals) in enumerate(self.reductions):
            if reading in exclude_readings or head in supplied:
                continue
            left = [r for r in residuals if r not in supplied]
            if not left:
                continue
            need[index] = len(left)
            into[head].append(index)
            for residual in left:
                by_residual[residual].append(index)
        queue = sorted(refuted)
        while queue:
            target = queue.pop()
            for index in into.get(target, ()):
                if need[index] != 1:
                    continue
                head, producer, reading, residuals = self.reductions[index]
                source = next(r for r in residuals if r not in supplied)
                if source in refuted or source in derived:
                    continue
                derived[source] = {"kind": "derived", "reaches": target, "producers": [producer]}
                queue.append(source)
        cone: set[str] = set()
        frontier = sorted(refuted | set(derived))
        while frontier:
            node = frontier.pop()
            for index in into.get(node, ()):
                for residual in self.reductions[index][3]:
                    if (residual not in supplied and residual not in cone
                            and residual not in refuted and residual not in derived):
                        cone.add(residual)
                        frontier.append(residual)
        truncated = False
        work = 0
        for start in sorted(cone):
            if start in derived:
                continue
            fired: dict[str, int] = {}
            remaining: dict[int, int] = {}
            gained = {start}
            stack = [start]
            hit = None
            while stack and hit is None:
                node = stack.pop()
                work += 1
                if work > REFUTATION_WORK_LIMIT:
                    truncated = True
                    break
                for index in by_residual.get(node, ()):
                    count = remaining.get(index, need[index]) - 1
                    remaining[index] = count
                    if count:
                        continue
                    head = self.reductions[index][0]
                    if head in gained:
                        continue
                    gained.add(head)
                    fired[head] = index
                    if head in refuted or head in derived:
                        hit = head
                        break
                    stack.append(head)
            if truncated:
                break
            if hit is not None:
                derived[start] = {"kind": "derived", "reaches": hit, "producers": self._fired_chain(hit, fired)}
        return derived, truncated

    def _fired_chain(self, hit: str, fired: dict[str, int]) -> list[str]:
        producers: list[str] = []
        seen: set[str] = set()
        stack = [hit]
        while stack:
            node = stack.pop()
            if node in seen or node not in fired:
                continue
            seen.add(node)
            _, producer, _, residuals = self.reductions[fired[node]]
            producers.append(producer)
            stack.extend(r for r in residuals if r in fired)
        return list(dict.fromkeys(reversed(producers)))

    # ------------------------------------------------------------------
    # Analysis

    def analyse(self) -> None:
        self.supplied, self.witness = self.supply()
        self.refuted_kernel = self._kernel_refutations(self.supplied)
        self.refuted_derived, self.refutation_truncated = self._derived_refutations(
            self.supplied, self.refuted_kernel)
        self.refuted: dict[str, dict[str, Any]] = {
            key: {"kind": "kernel", "producer": producer, "reading": reading}
            for key, (producer, reading) in self.refuted_kernel.items()}
        for key, record in self.refuted_derived.items():
            self.refuted.setdefault(key, record)
        # A statement both supplied and refuted would mean the corpus proves a
        # contradiction (or that two different statements share a key).
        self.inconsistent = sorted(set(self.refuted) & self.supplied)
        self.open = {key for key in self.statements if key not in self.supplied and key not in self.refuted}
        self.vacuous_theorems = sorted(
            (name, key) for name, theorem in self.theorems.items()
            for key in theorem.get("hypotheses", []) if key in self.refuted)
        # Reduced reductions of open heads: residuals minus supplied.
        self.reduced: list[tuple[str, str, str, tuple[str, ...]]] = []
        for head, producer, reading, residuals in self.reductions:
            if head in self.supplied or head in self.refuted:
                continue
            left = tuple(r for r in residuals if r not in self.supplied)
            self.reduced.append((head, producer, reading, left))
        self.implies: dict[str, set[str]] = defaultdict(set)   # A -> {S}: A ⇒ S
        self.implied_by: dict[str, set[str]] = defaultdict(set)
        self.implication_producers: dict[tuple[str, str], set[str]] = defaultdict(set)
        for head, producer, _, left in self.reduced:
            if len(left) == 1 and left[0] in self.open:
                a = left[0]
                self.implies[a].add(head)
                self.implied_by[head].add(a)
                self.implication_producers[(a, head)].add(producer)
        self._components()
        self._by_residual_open: dict[str, list[int]] = defaultdict(list)
        for index, (_, _, _, left) in enumerate(self.reduced):
            for r in left:
                self._by_residual_open[r].append(index)
        for cache in ("_reduced_by_head", "_leverage_cache", "_class_closure"):
            self.__dict__.pop(cache, None)
        self._mark_idle_open()

    def _mark_idle_open(self) -> None:
        """For each idle row, the dropped statements that are open when idle
        reductions are left out: stated as a hypothesis, unused by the proof."""
        if not self.idle:
            return
        if any(reading == "idle" for _, _, reading, _ in self.reductions):
            without = frozenset({"idle"})
            supplied, _ = self.supply(exclude_readings=without)
            kernel = self._kernel_refutations(supplied)
            derived, _ = self._derived_refutations(supplied, kernel, exclude_readings=without)
        else:
            supplied, kernel, derived = self.supplied, self.refuted_kernel, self.refuted_derived
        for entry in self.idle:
            entry["dropped_open_without_idle"] = sorted(
                d["key"] for d in entry.get("dropped", [])
                if d.get("key") and d["key"] in self.statements
                and d["key"] not in supplied and d["key"] not in kernel and d["key"] not in derived)

    def status(self, key: str) -> str:
        if key in self.supplied:
            return "supplied"
        if key in self.refuted:
            return "refuted"
        return "open"

    def _components(self) -> None:
        """Tarjan's algorithm, iterative, over the implication graph."""
        index_of: dict[str, int] = {}
        low: dict[str, int] = {}
        on_stack: set[str] = set()
        stack: list[str] = []
        counter = 0
        self.component: dict[str, int] = {}
        components: list[list[str]] = []
        nodes = sorted(self.open)
        for start in nodes:
            if start in index_of:
                continue
            work = [(start, iter(sorted(self.implies.get(start, ()))))]
            index_of[start] = low[start] = counter
            counter += 1
            stack.append(start)
            on_stack.add(start)
            while work:
                node, successors = work[-1]
                advanced = False
                for successor in successors:
                    if successor not in self.open:
                        continue
                    if successor not in index_of:
                        index_of[successor] = low[successor] = counter
                        counter += 1
                        stack.append(successor)
                        on_stack.add(successor)
                        work.append((successor, iter(sorted(self.implies.get(successor, ())))))
                        advanced = True
                        break
                    if successor in on_stack:
                        low[node] = min(low[node], index_of[successor])
                if advanced:
                    continue
                work.pop()
                if work:
                    parent = work[-1][0]
                    low[parent] = min(low[parent], low[node])
                if low[node] == index_of[node]:
                    members = []
                    while True:
                        member = stack.pop()
                        on_stack.discard(member)
                        members.append(member)
                        if member == node:
                            break
                    component_id = len(components)
                    for member in members:
                        self.component[member] = component_id
                    components.append(sorted(members))
        self.components = components

    def disguise_classes(self) -> list[list[str]]:
        return [members for members in self.components if len(members) >= 2]

    # ------------------------------------------------------------------
    # Bundles and leverage

    def bundles(self, key: str) -> tuple[list[list[str]], bool]:
        """Minimal sets of open statements whose supply supplies ``key``.

        Routes through a refuted residual are dead and skipped. ``truncated``
        is set whenever a depth, size, count, cone or work limit pruned the
        search; when it is false the list holds every minimal bundle of at most
        ``BUNDLE_SIZE_LIMIT`` open statements. Every returned bundle is minimal
        among the bundles found."""
        if key not in self.open:
            return [], False
        refuted = self.refuted
        memo: dict[tuple[str, int], tuple[list[frozenset[str]], bool]] = {}
        work = 0

        def minimise(sets: Iterable[frozenset[str]]) -> list[frozenset[str]]:
            ordered = sorted(set(sets), key=lambda s: (len(s), sorted(s)))
            kept: list[frozenset[str]] = []
            for candidate in ordered:
                if not any(existing <= candidate for existing in kept):
                    kept.append(candidate)
            return kept

        def expand(node: str, remaining: int, path: frozenset[str]
                   ) -> tuple[list[frozenset[str]], frozenset[str], bool]:
            """(options, ancestors whose presence on the branch pruned a route,
            whether a limit pruned). A result pruned by no ancestor depends only
            on (node, remaining depth) and is memoised under that key."""
            nonlocal work
            if node in self.supplied:
                return [frozenset()], frozenset(), False
            if node in refuted:
                return [], frozenset(), False
            cached = memo.get((node, remaining))
            if cached is not None:
                return cached[0], frozenset(), cached[1]
            work += 1
            options: list[frozenset[str]] = [frozenset([node])]
            pruned_by: set[str] = set()
            cut = False
            reductions = self.reduced_by_head.get(node, ())
            if reductions and (remaining <= 0 or work > BUNDLE_WORK_LIMIT):
                cut = True
                reductions = ()
            for _, _, _, left in reductions:
                if any(r in refuted for r in left):
                    continue  # a dead route: one residual can never be supplied
                blocked = [r for r in left if r in path]
                if blocked:
                    pruned_by.update(blocked)
                    continue  # a route back through the current branch
                partial: list[frozenset[str]] = [frozenset()]
                for residual in left:
                    choices, child_pruned, child_cut = expand(residual, remaining - 1, path | {node})
                    pruned_by |= child_pruned
                    cut |= child_cut
                    combined: set[frozenset[str]] = set()
                    for a in partial:
                        for b in choices:
                            union = a | b
                            if len(union) <= BUNDLE_SIZE_LIMIT:
                                combined.add(union)
                            else:
                                cut = True
                    partial = minimise(combined)
                    if len(partial) > BUNDLE_LIMIT:
                        partial = partial[:BUNDLE_LIMIT]
                        cut = True
                    if not partial:
                        break
                options.extend(partial)
                if len(options) > 4 * BUNDLE_LIMIT:
                    cut = True
                    break
            result = minimise(options)
            if len(result) > BUNDLE_LIMIT:
                result = result[:BUNDLE_LIMIT]
                cut = True
            pruned_by.discard(node)
            pruned_by.discard(key)  # the target is an ancestor of every branch
            if not pruned_by:
                memo[(node, remaining)] = (result, cut)
            return result, frozenset(pruned_by), cut

        # A single statement can supply the target through a route longer than
        # the depth limit: test every open statement of the backward cone. The
        # singletons sort first, so once they fill the list the enumeration
        # below cannot change it.
        cone, truncated = self._backward_cone(key, BUNDLE_CONE_LIMIT)
        singles: list[frozenset[str]] = []
        for a in sorted(cone):
            if a in self.open and key in self.leverage(a):
                singles.append(frozenset([a]))
                if len(singles) > BUNDLE_LIMIT:
                    return [sorted(bundle) for bundle in singles[:BUNDLE_LIMIT]], True
        found, _, cut = expand(key, BUNDLE_DEPTH_LIMIT, frozenset())
        truncated = truncated or cut
        bundles = minimise([b for b in found if b != frozenset([key])] + singles)
        bundles = [b for b in bundles if not any(member in refuted for member in b)]
        if len(bundles) > BUNDLE_LIMIT:
            bundles = bundles[:BUNDLE_LIMIT]
            truncated = True
        return [sorted(bundle) for bundle in bundles], truncated

    def _backward_cone(self, key: str, limit: int) -> tuple[set[str], bool]:
        """Open and unsupplied statements from which a live route leads to ``key``."""
        cone: set[str] = set()
        frontier = [key]
        while frontier:
            node = frontier.pop()
            for _, _, _, left in self.reduced_by_head.get(node, ()):
                if any(r in self.refuted for r in left):
                    continue
                for residual in left:
                    if residual != key and residual not in cone:
                        cone.add(residual)
                        frontier.append(residual)
                        if len(cone) >= limit:
                            return cone, True
        return cone, False

    @property
    def reduced_by_head(self) -> dict[str, list[tuple[str, str, str, tuple[str, ...]]]]:
        cached = getattr(self, "_reduced_by_head", None)
        if cached is None:
            cached = defaultdict(list)
            for item in self.reduced:
                cached[item[0]].append(item)
            self._reduced_by_head = cached
        return cached

    def leverage(self, key: str, limit: int = 100000) -> set[str]:
        """Open statements supplied once ``key`` is supplied (memoised). The
        members of a disguise class imply each other, so they share one
        closure, computed once per class."""
        cache = self.__dict__.setdefault("_leverage_cache", {})
        if key in cache:
            return cache[key]
        component = self.component.get(key)
        if component is not None and len(self.components[component]) >= 2:
            closures = self.__dict__.setdefault("_class_closure", {})
            if component not in closures:
                closures[component] = self._leverage(key, limit) | {key}
            result = closures[component] - {key}
        else:
            result = self._leverage(key, limit)
        cache[key] = result
        return result

    def _leverage(self, key: str, limit: int) -> set[str]:
        if key in self.supplied or key in self.refuted:
            return set()
        remaining: dict[int, int] = {}
        gained = {key}
        queue = [key]
        steps = 0
        while queue and steps < limit:
            node = queue.pop()
            steps += 1
            for index in self._by_residual_open.get(node, ()):
                count = remaining.get(index)
                if count is None:
                    count = len(self.reduced[index][3])
                count -= 1
                remaining[index] = count
                if count == 0:
                    head = self.reduced[index][0]
                    if head not in gained and head not in self.refuted:
                        gained.add(head)
                        queue.append(head)
        gained.discard(key)
        return gained

    def criticality(self, *, statement: str | None = None, producer: str | None = None) -> set[str]:
        """Supplied statements that lose every kernel witness chain when the
        given statement is no longer supplied, or the given theorem is
        withdrawn: the answer to "what fails without it"."""
        supplied, _ = self.supply(
            exclude_heads=frozenset([statement]) if statement else frozenset(),
            exclude_producers=frozenset([producer]) if producer else frozenset())
        lost = self.supplied - supplied
        if statement:
            lost.discard(statement)
        return lost

    def proof_tree(self, key: str, depth: int = 0, limit: int = 6) -> dict[str, Any]:
        index = self.witness.get(key)
        node: dict[str, Any] = {"statement": key, "type": self.statements.get(key, {}).get("type")}
        if index is None:
            node["status"] = "refuted" if key in getattr(self, "refuted", {}) else "open"
            return node
        if index < 0:
            node["status"] = "assumed"
            return node
        head, producer, reading, residuals = self.reductions[index]
        node["producer"] = producer
        node["reading"] = reading
        if depth < limit:
            node["from"] = [self.proof_tree(r, depth + 1, limit) for r in residuals]
        elif residuals:
            node["from_truncated"] = list(residuals)
        return node


def dependency_handles(root: Path) -> dict[str, str]:
    """source_ref (lean/<module>:<line>) -> fully qualified declaration name."""
    index = load_json(root / "docs" / "lean_dependency_index.json")
    out: dict[str, str] = {}
    if not index:
        return out
    for node in index.get("nodes", []):
        if node.get("source_ref") and node.get("handle"):
            out[node["source_ref"]] = node["handle"]
    return out


def semantic_nodes(root: Path) -> list[dict[str, Any]]:
    path = root / "docs" / "semantic_corpus.json.gz"
    if not path.is_file():
        return []
    with gzip.open(path, "rt", encoding="utf-8") as handle:
        return json.load(handle).get("statement_nodes", [])


CONDITIONAL_STATUSES = frozenset({"conditional_on_refuted", "conditional_on_open", "conditional_on_schematic"})


def kernel_status(graph: "Graph", name: str, *, after_idle: bool = False) -> str | None:
    """How a theorem's conclusion depends on its obligations: on a refuted,
    an open or a schematic one (a hypothesis that mentions a data binder, which
    the graph cannot judge), only on supplied ones, or on none. With
    ``after_idle``, obligations a kernel-checked idle row dropped do not count."""
    theorem = graph.theorems.get(name)
    if theorem is None:
        return None
    closed = theorem.get("hypotheses", [])
    schematic = bool(theorem.get("schematic_hypotheses") or theorem.get("witness_obligations"))
    if after_idle and theorem.get("after_idle"):
        closed = theorem["after_idle"].get("hypotheses", [])
        schematic = bool(theorem["after_idle"].get("schematic"))
    if any(k in graph.refuted for k in closed):
        return "conditional_on_refuted"
    if any(k not in graph.supplied for k in closed):
        return "conditional_on_open"
    if schematic:
        return "conditional_on_schematic"
    if closed:
        return "conditional_on_supplied"
    return "unconditional"


def compositions(graph: "Graph", papers: dict[str, list[dict[str, Any]]]) -> list[dict[str, Any]]:
    """Statements the graph supplies only by chaining a conditional theorem
    with statements the graph supplies otherwise. These are witness chains; a
    row is a kernel-checked term only when ``kernel_checked_composition`` says
    the exporter composed that theorem and the kernel accepted it."""
    direct = {head for (head, _, _, residuals) in graph.reductions if not residuals}
    checked = {(row.get("theorem"), graph.canon(row["conclusion"])) for row in graph.compositions_checked
               if row.get("kernel_checked") and row.get("conclusion")}
    out = []
    for key in sorted(graph.supplied):
        if key in direct:
            continue
        index = graph.witness.get(key, -1)
        if index < 0:
            continue
        head, producer, reading, residuals = graph.reductions[index]
        suppliers = []
        for residual in residuals:
            w = graph.witness.get(residual, -1)
            suppliers.append({"statement": residual, "type": graph.statements.get(residual, {}).get("type"),
                              "supplied_by": graph.reductions[w][1] if w >= 0 else None})
        out.append({
            "statement": key,
            "type": graph.statements[key].get("type"),
            "via": producer,
            "reading": reading,
            "hypotheses_supplied_by": suppliers,
            "kernel_checked_composition": (producer, key) in checked,
            "paper_rows_of_conditional_theorem": papers.get(producer, []),
        })
    out.sort(key=lambda row: (not row["paper_rows_of_conditional_theorem"], row["via"]))
    return out


def audit_authored_layers(graph: "Graph", root: Path) -> dict[str, Any]:
    """Check the authored navigation layers against the kernel graph."""
    handles = dependency_handles(root)
    rows = []
    counts: dict[str, int] = defaultdict(int)
    for node in semantic_nodes(root):
        label = node.get("logical_class")
        if label in (None, "infrastructure", "finite_instance", "generated_certificate_instance"):
            continue
        statuses = []
        for evidence in node.get("evidence", []) or []:
            handle = handles.get(f"lean/{evidence.get('module')}:{evidence.get('line')}")
            status = kernel_status(graph, handle) if handle else None
            if status:
                statuses.append((handle, status, kernel_status(graph, handle, after_idle=True)))
        if not statuses:
            counts["unresolved_evidence"] += 1
            continue
        if label == "conditional_implication":
            # A schematic hypothesis counts as a condition: the graph cannot
            # tell a side condition on a variable from an open assumption.
            if all(before not in CONDITIONAL_STATUSES for _, before, _ in statuses):
                verdict = "conditional_label_but_no_open_kernel_hypothesis"
            elif all(after not in CONDITIONAL_STATUSES for _, _, after in statuses):
                verdict = "conditional_label_but_proof_uses_no_open_hypothesis"
            else:
                verdict = "consistent"
        elif label == "unconditional_object_theorem":
            if any(after in ("conditional_on_open", "conditional_on_refuted") for _, _, after in statuses):
                verdict = "unconditional_label_but_open_kernel_hypothesis"
            else:
                verdict = "consistent"
        else:
            verdict = "not_audited_class"
        counts[f"{label}:{verdict}"] += 1
        if verdict not in ("consistent", "not_audited_class"):
            rows.append({"node": node.get("id"), "logical_class": label, "verdict": verdict,
                         "declarations": [{"name": h, "kernel_status": before, "kernel_status_after_idle": after}
                                          for h, before, after in statuses]})
    frontier = load_json(root / "docs" / "semantic" / "frontier.json") or {}
    antecedent_rows = []
    for antecedent in frontier.get("open_antecedents", []) or []:
        constants = set(antecedent.get("lean_constants") or [])
        if not constants:
            continue
        # Constant co-occurrence: every graph statement that mentions one of
        # the antecedent's constants, which may be wider than the antecedent.
        hits = [k for k, n in graph.statements.items()
                if any(c in constants or any(c.endswith("." + x) for x in constants) for c in n.get("constants", ()))]
        statuses = sorted({graph.status(k) for k in hits})
        if "open" in statuses:
            verdict = "consistent"
        elif not statuses:
            verdict = "not_found_in_graph"
        elif "refuted" in statuses:
            verdict = "authored_open_but_kernel_refuted"
        else:
            verdict = "authored_open_but_kernel_supplied"
        antecedent_rows.append({"id": antecedent.get("id"), "lean_constants": sorted(constants),
                                "kernel_statements": len(hits), "kernel_statuses": statuses,
                                "verdict": verdict})
    return {"semantic_logical_class": {"counts": dict(sorted(counts.items())), "disagreements": rows[:200],
                                       "disagreement_count": len(rows)},
            "frontier_open_antecedents": antecedent_rows}


def barrier_overlay(graph: "Graph", root: Path) -> dict[str, Any]:
    """Attach each authored barrier to the open statements that mention its
    route predicates, and say whether its declaration is in the kernel
    environment the graph was read from."""
    registry = load_json(root / "docs" / "semantic" / "barriers.json") or {}
    lanes = registry.get("build_lanes") or {}
    by_constant: dict[str, set[str]] = defaultdict(set)
    for key, node in graph.statements.items():
        for constant in node.get("constants", ()):
            by_constant[constant].add(key)
    entries = []
    constrains: dict[str, list[str]] = defaultdict(list)
    for entry in registry.get("entries", []):
        declaration = entry.get("declaration")
        in_graph = bool(declaration) and declaration in graph.theorems
        touched: set[str] = set()
        for predicate in entry.get("route_predicates") or []:
            touched |= by_constant.get(predicate, set())
        open_touched = sorted(k for k in touched if k in graph.open)
        for key in open_touched:
            constrains[key].append(entry["id"])
        entries.append({
            "id": entry["id"], "problem": entry["problem"], "kind": entry["barrier_kind"],
            "declaration": declaration, "source": entry.get("source_ref"),
            "build_lane": lanes.get(entry["id"]), "in_graph": in_graph,
            "plain_statement": entry.get("plain_statement"), "blocks": entry.get("blocks"),
            "does_not_block": (entry.get("does_not_block") or [])[:6],
            "open_statements_touched": len(open_touched),
        })
    return {"entries": entries, "constrains": {k: v for k, v in constrains.items()}}


# --------------------------------------------------------------------------
# Projection


def build(export_path: Path, root: Path = ROOT, *, lean_tree: str | None = None,
          source_revision: str | None = None, include_idle: bool = True
          ) -> tuple[dict[str, Any], dict[str, Any]]:
    rows = read_export(export_path)
    graph = Graph(rows, include_idle=include_idle)
    graph.analyse()
    refs = source_refs(root)
    papers = paper_rows(root)
    comparator = comparator_results(root)

    semantic = semantic_problems(root)

    def theorem_problem(name: str) -> str | None:
        # Paper rows first, then the semantic corpus's authored attribution,
        # then module paths and declaration-name tokens.
        rows_for = papers.get(name) or []
        problems = sorted({row["problem"] for row in rows_for if row.get("problem")})
        if problems:
            return problems[0] if len(problems) == 1 else "cross"
        if name in semantic:
            return semantic[name]
        theorem = graph.theorems.get(name)
        return module_problem(theorem["module"] if theorem else "", name)

    theorem_problems = {name: theorem_problem(name) for name in graph.theorems}
    # A statement's own attribution comes from the theorems that state it (as a
    # hypothesis or a conclusion); the per-problem views also count the
    # problems of the theorems that reduce it.
    own_problems: dict[str, set[str]] = defaultdict(set)
    for key, node in graph.statements.items():
        for name in node["consumers"] | node["conclusion_of"]:
            problem = theorem_problems.get(name)
            if problem:
                own_problems[key].add(problem)
    statement_problems: dict[str, set[str]] = defaultdict(set)
    for key, problems in own_problems.items():
        statement_problems[key] |= problems
    for head, producer, _, residuals in graph.reductions:
        problem = theorem_problems.get(producer)
        if problem:
            statement_problems[head].add(problem)
            for residual in residuals:
                statement_problems[residual].add(problem)

    barriers = barrier_overlay(graph, root)

    def theorem_card(name: str) -> dict[str, Any]:
        card: dict[str, Any] = {"name": name, "source": refs.get(name)}
        if papers.get(name):
            card["papers"] = papers[name]
        if comparator.get(name):
            card["comparator_result"] = comparator[name]
        return card

    def statement_card(key: str, *, with_bundles: bool = False) -> dict[str, Any]:
        node = graph.statements[key]
        status = graph.status(key)
        card: dict[str, Any] = {
            "key": key,
            "type": node.get("type"),
            "status": status,
            "problems": sorted(statement_problems.get(key, ())),
            "consumed_by": sorted(node["consumers"])[:12],
            "consumer_count": len(node["consumers"]),
        }
        if status == "supplied":
            index = graph.witness.get(key, -1)
            if index >= 0:
                card["supplied_by"] = graph.reductions[index][1]
                card["supplied_reading"] = graph.reductions[index][2]
        elif status == "refuted":
            card["refutation"] = graph.refuted[key]
        else:
            reductions = graph.reduced_by_head.get(key, [])
            rows_out = []
            for (_, producer, reading, left) in reductions[:12]:
                row: dict[str, Any] = {"producer": producer, "reading": reading, "open_residuals": list(left)}
                dead = [r for r in left if r in graph.refuted]
                if dead:
                    row["refuted_residuals"] = dead
                rows_out.append(row)
            card["reductions"] = rows_out
            card["reduction_count"] = len(reductions)
            component = graph.component.get(key)
            if component is not None and len(graph.components[component]) >= 2:
                card["disguise_class"] = component
            gained = graph.leverage(key)
            card["leverage"] = len(gained)
            if with_bundles:
                bundles, truncated = graph.bundles(key)
                card["bundles"] = bundles
                card["bundles_truncated"] = truncated
        return card

    # Per-problem open sinks: open statements with at least one reduction into
    # them and no open statement they imply outside their own class.
    per_problem: dict[str, Any] = {}
    for problem in PROBLEMS + ("249_257", "cross"):
        keys = sorted(k for k in graph.open if problem in statement_problems.get(k, ()))
        refuted_keys = sorted(k for k in graph.refuted if problem in statement_problems.get(k, ()))
        if not keys and not refuted_keys:
            continue
        sinks = []
        for key in keys:
            if not graph.reduced_by_head.get(key):
                continue
            component = graph.component.get(key)
            escapes = [s for s in graph.implies.get(key, ()) if graph.component.get(s) != component]
            if not escapes:
                sinks.append(key)
        sinks.sort(key=lambda k: (-len(graph.reduced_by_head.get(k, [])), graph.statements[k].get("type") or ""))
        levered = sorted(keys, key=lambda k: (-len(graph.leverage(k)), k))
        classes = sorted({graph.component[k] for k in keys
                          if graph.component.get(k) is not None
                          and len(graph.components[graph.component[k]]) >= 2})
        problem_barriers = [e for e in barriers["entries"] if e["problem"] == problem]
        per_problem[problem] = {
            "barriers": problem_barriers[:LIST_LIMIT * 2],
            "barrier_count": len(problem_barriers),
            "open_statements_constrained_by_barriers": sum(
                1 for k in keys if k in barriers["constrains"]),
            "open_statements": len(keys),
            "refuted_statements": len(refuted_keys),
            "supplied_statements": sum(1 for k in graph.supplied if problem in statement_problems.get(k, ())),
            "sinks": [statement_card(k, with_bundles=True) for k in sinks[:LIST_LIMIT]],
            "sink_count": len(sinks),
            "highest_leverage": [statement_card(k) for k in levered[:LIST_LIMIT]],
            "disguise_classes": [
                {"class": c, "size": len(graph.components[c]),
                 "members": [{"key": m, "type": graph.statements[m].get("type")}
                             for m in graph.components[c][:LIST_LIMIT]]}
                for c in classes[:LIST_LIMIT]
            ],
            "refuted": [statement_card(k) for k in refuted_keys[:LIST_LIMIT]],
        }

    conditional = [name for name, t in graph.theorems.items() if t["hypotheses"]]
    composed = compositions(graph, papers)
    audit = audit_authored_layers(graph, root)

    def idle_row(entry: dict[str, Any]) -> dict[str, Any]:
        name = entry["theorem"]
        open_dropped = set(entry.get("dropped_open_without_idle", []))
        conclusion = entry.get("conclusion")
        return {
            "theorem": name,
            "problem": theorem_problems.get(name),
            "source": refs.get(name),
            "papers": papers.get(name, []),
            "stronger_statement": entry.get("type"),
            "conclusion": conclusion,
            "conclusion_type": graph.theorems.get(name, {}).get("conclusion_type"),
            "conclusion_status": graph.status(conclusion) if conclusion else None,
            "dropped": [{"type": d.get("type"), "key": d.get("key"),
                         "open_without_idle": d.get("key") in open_dropped} for d in entry.get("dropped", [])],
            "remaining_residuals": entry.get("residuals", []),
            "reduction": entry.get("reduction"),
            "reason_without_reduction": entry.get("reason"),
        }

    idle_rows = sorted((idle_row(e) for e in graph.idle),
                       key=lambda r: (not r["papers"], not any(d["open_without_idle"] for d in r["dropped"]),
                                      r["theorem"]))
    idle_dropping_open = [r for r in idle_rows if any(d["open_without_idle"] for d in r["dropped"])]
    kernel_refuted = {k: v for k, v in graph.refuted.items() if v["kind"] == "kernel"}
    derived_refuted = {k: v for k, v in graph.refuted.items() if v["kind"] == "derived"}
    theorem_modules = {t["module"] for t in graph.theorems.values() if t.get("module")}
    summary = {
        "theorems": len(graph.theorems),
        "theorem_modules": len(theorem_modules),
        "conditional_arguments": len(conditional),
        "closed_statements": len(graph.statements),
        "supplied_statements": len(graph.supplied),
        "open_statements": len(graph.open),
        "reductions": len(graph.reductions),
        "implications_between_open_statements": sum(len(v) for v in graph.implies.values()),
        "disguise_classes": len(graph.disguise_classes()),
        "largest_disguise_class": max((len(c) for c in graph.disguise_classes()), default=0),
        "existential_reductions": len(graph.existential),
        "existential_refutations": graph.existential_refutations,
        "budget_exhausted_attempts": sum(1 for r in graph.budget_exhausted if r.get("search", "match") == "match"),
        "budget_exhausted_refutation_attempts": sum(
            1 for r in graph.budget_exhausted if r.get("search") == "refutation"),
        "candidate_caps": len(graph.caps),
        "export_errors": len(graph.errors),
        "export_truncated": bool(graph.summary.get("truncated")),
        "battery_closed_statements": sum(1 for (_, producer, _, _) in graph.reductions
                                         if producer.startswith("tactic:")),
        "refuted_statements": len(kernel_refuted),
        "refuted_statements_derived": len(derived_refuted),
        "refutation_propagation_truncated": graph.refutation_truncated,
        "vacuous_theorems": len({name for name, _ in graph.vacuous_theorems}),
        "supplied_and_refuted": len(graph.inconsistent),
        "kernel_checked_compositions": sum(1 for row in graph.compositions_checked
                                           if row.get("kernel_checked")),
        "compositions": len(composed),
        "compositions_of_paper_cited_conditional_theorems": sum(
            1 for row in composed if row["paper_rows_of_conditional_theorem"]),
        "idle_theorems_kernel_checked": len(graph.idle),
        "idle_theorems_unchecked": graph.idle_unchecked,
        "idle_reductions": sum(1 for e in graph.idle if e.get("reduction")),
        "idle_dropping_open": len(idle_dropping_open),
        "semantic_label_disagreements": audit["semantic_logical_class"]["disagreement_count"],
        "barriers": len(barriers["entries"]),
        "barriers_in_graph": sum(1 for e in barriers["entries"] if e["in_graph"]),
        "open_statements_constrained_by_barriers": len(barriers["constrains"]),
    }
    lean_tree = resolve_lean_tree(export_path, lean_tree)
    source = {
        # The git tree of lean/ the export was computed from; query_continuations.py
        # compares it with `git rev-parse HEAD:lean` and reports the graph stale
        # when they differ. The revision is provenance only.
        "lean_tree": lean_tree,
        "source_revision": resolve_source_revision(export_path, source_revision),
        "export_digest": file_digest(export_path),
        "export_schema": graph.meta.get("schema"),
        "lean_version": graph.meta.get("lean_version"),
        "export_imports": graph.meta.get("imports"),
        "export_summary": {k: v for k, v in graph.summary.items() if k != "record"},
        "export_config": {k: graph.meta.get(k) for k in
                          ("roots", "name_prefixes", "imports", "match_heartbeats_thousands",
                           "max_candidates", "max_statements", "time_budget_ms")},
    }
    if not lean_tree:
        # Fallback provenance: the committed dependency index's fingerprint at
        # build time, which says nothing about the sources the export ran on.
        dependency_index = load_json(root / "docs" / "lean_dependency_index.json") or {}
        source["lean_source_fingerprint"] = dependency_index.get("source_fingerprint")

    def refutation_row(key: str, record: dict[str, Any]) -> dict[str, Any]:
        row = {"key": key, "type": graph.statements.get(key, {}).get("type"), "kind": record["kind"],
               "consumers": sorted(graph.statements.get(key, {}).get("consumers", ()))[:12]}
        if record["kind"] == "kernel":
            row.update({"refuted_by": record["producer"], "reading": record["reading"]})
        else:
            reaches = record["reaches"]
            row.update({"reaches": reaches, "reaches_type": graph.statements.get(reaches, {}).get("type"),
                        "via": record["producers"]})
        return row

    projection = {
        "schema": SCHEMA,
        "artifact_role": "generated_argument_graph_projection",
        "authority_posture": (
            "corpus theorems joined by the elaborator's unifier (a lower bound on the producer relation), "
            "kernel-checked battery, composition and idle rows, papers and Comparator results; navigation "
            "and planning evidence, not proof authority: the cited kernel theorems are"),
        "semantics": {
            "reduction": "a corpus theorem that supplies the statement once its residual hypotheses are supplied; "
                         "a data binder not known to be inhabited contributes the residual Nonempty T",
            "supplied": "least fixpoint over reductions; every supplied statement has a witness chain of corpus "
                        "theorems joined by unification",
            "refuted": "kernel: a corpus theorem (or a kernel-checked battery proof) establishes the negation, with "
                       "every residual supplied; derived: supplying the statement would supply a refuted one",
            "open": "neither supplied nor refuted",
            "implication": "a reduction left with exactly one open residual",
            "disguise_class": "strongly connected component of implications with two or more open statements: "
                              "statements equivalent through recorded reductions",
            "bundle": "a minimal set of open statements whose supply supplies the statement; bundles_truncated "
                      "says whether a limit pruned the enumeration",
            "leverage": "number of open statements supplied once the statement is supplied",
            "sink": "an open statement with a reduction into it that implies nothing outside its own class",
            "composition": "a statement supplied only through a conditional theorem whose hypotheses other "
                           "reductions supply (a witness chain); kernel_checked_composition marks the ones the "
                           "exporter composed and the kernel accepted",
            "idle": "a theorem whose proof never uses some proposition binders; the kernel accepted the stronger "
                    "statement without them",
            "vacuous_theorem": "a conditional theorem with a refuted closed hypothesis: it can never be applied",
            "audit": "authored logical classes and open antecedents checked against the kernel graph",
        },
        "source": source,
        "summary": summary,
        "problems": per_problem,
        "compositions": composed[:LIST_LIMIT * 3],
        "refuted": [refutation_row(key, record) for key, record in sorted(graph.refuted.items())][:LIST_LIMIT * 3],
        "vacuous_theorems": [
            {"theorem": name, "refuted_hypothesis": key,
             "type": graph.statements.get(key, {}).get("type"), "refutation": graph.refuted[key]}
            for name, key in graph.vacuous_theorems][:LIST_LIMIT * 3],
        "supplied_and_refuted": [
            {"key": key, "type": graph.statements.get(key, {}).get("type")} for key in graph.inconsistent],
        "idle": idle_rows[:LIST_LIMIT * 3],
        "audit": audit,
    }
    graph_payload = {
        "schema": GRAPH_SCHEMA,
        "source": source,
        "statements": [
            {
                "key": key,
                "type": node.get("type"),
                "origins": sorted(node["origins"]),
                "status": graph.status(key),
                **({"refutation": graph.refuted[key]} if key in graph.refuted else {}),
                "problems": sorted(statement_problems.get(key, ())),
                "own_problems": sorted(own_problems.get(key, ())),
                "consumers": sorted(node["consumers"]),
                "conclusion_of": sorted(node["conclusion_of"]),
                "constants": sorted(node.get("constants", ())),
                "aliases": sorted(node.get("aliases", ())),
                "component": graph.component.get(key),
                "witness": (graph.reductions[graph.witness[key]][1]
                            if graph.witness.get(key, -1) >= 0 else None),
            }
            for key, node in sorted(graph.statements.items())
        ],
        "reductions": [
            {"statement": head, "producer": producer, "reading": reading, "residuals": list(residuals)}
            for head, producer, reading, residuals in graph.reductions
        ],
        "refutations": [
            {"statement": st, "producer": pr, "reading": rd, "residuals": list(rs)}
            for st, pr, rd, rs in graph.refutations],
        "derived_refutations": [
            {"statement": key, "reaches": record["reaches"], "via": record["producers"]}
            for key, record in sorted(derived_refuted.items())],
        "barriers": barriers,
        "existential_reductions": graph.existential,
        "budget_exhausted": graph.budget_exhausted,
        "idle": graph.idle,
        "theorems": [
            {**theorem_card(name), "module": t["module"], "problem": theorem_problems.get(name),
             "hypotheses": t["hypotheses"], "schematic_hypotheses": t["schematic_hypotheses"],
             "witness_obligations": t["witness_obligations"], "after_idle": t.get("after_idle"),
             "conclusion": t["conclusion_key"], "conclusion_type": t["conclusion_type"]}
            for name, t in sorted(graph.theorems.items())
        ],
    }
    return projection, graph_payload


TEX_MACROS_BEGIN = "% BEGIN generated_argument_graph_macros"
TEX_MACROS_END = "% END generated_argument_graph_macros"


def paper_macro_region(projection: dict[str, Any]) -> str:
    """LaTeX macros carrying the graph's measured totals into a paper, so no
    number in the prose is typed by hand."""
    summary = projection["summary"]
    export = projection["source"].get("export_summary", {})
    values = {
        "AGTheorems": summary["theorems"],
        "AGModules": summary["theorem_modules"],
        "AGConditional": summary["conditional_arguments"],
        "AGStatements": summary["closed_statements"],
        "AGSupplied": summary["supplied_statements"],
        "AGOpen": summary["open_statements"],
        "AGReductions": summary["reductions"],
        "AGImplications": summary["implications_between_open_statements"],
        "AGDisguiseClasses": summary["disguise_classes"],
        "AGLargestDisguise": summary["largest_disguise_class"],
        "AGCompositions": summary["compositions"],
        "AGKernelCompositions": summary.get("kernel_checked_compositions", 0),
        "AGPaperCompositions": summary["compositions_of_paper_cited_conditional_theorems"],
        "AGBatteryClosed": summary.get("battery_closed_statements", 0),
        "AGBatteryTried": export.get("battery_tried", 0),
        "AGBudgetExhausted": summary["budget_exhausted_attempts"],
        "AGRefuted": summary["refuted_statements"],
        "AGRefutedDerived": summary["refuted_statements_derived"],
        "AGBarriers": summary["barriers"],
        "AGBarriersInGraph": summary["barriers_in_graph"],
        "AGVacuous": summary["vacuous_theorems"],
        "AGLabelDisagreements": summary["semantic_label_disagreements"],
        "AGIdle": summary["idle_theorems_kernel_checked"],
        "AGIdleOpen": summary["idle_dropping_open"],
    }
    lines = [TEX_MACROS_BEGIN]
    for name, value in values.items():
        rendered = f"{value:,}" if isinstance(value, int) else str(value)
        lines.append(rf"\newcommand{{\{name}}}{{{rendered}}}")
    lines.append(TEX_MACROS_END)
    return "\n".join(lines)


def replace_macro_region(text: str, region: str) -> str:
    start = text.find(TEX_MACROS_BEGIN)
    end = text.find(TEX_MACROS_END)
    if start < 0 or end < start:
        raise SystemExit("paper has no generated_argument_graph_macros region")
    return text[:start] + region + text[end + len(TEX_MACROS_END):]


def write_outputs(projection: dict[str, Any], graph_payload: dict[str, Any],
                  output: Path, graph_output: Path) -> None:
    output.write_text(json.dumps(projection, indent=1, ensure_ascii=False, sort_keys=False) + "\n",
                      encoding="utf-8")
    data = json.dumps(graph_payload, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    with graph_output.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as handle:
        handle.write(data)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--export", type=Path, required=True,
                        help="export stream (.jsonl or .jsonl.gz) from export_argument_continuations.lean")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--graph-output", type=Path, default=DEFAULT_GRAPH_OUTPUT)
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root for the joins")
    parser.add_argument("--lean-tree",
                        help=f"git tree id of lean/ at the exported commit, or a file holding it "
                             f"(default: {LEAN_TREE_FILE} beside the export)")
    parser.add_argument("--source-revision",
                        help=f"the exported commit, recorded as provenance (default: {SOURCE_REVISION_FILE} "
                             "beside the export)")
    parser.add_argument("--paper", type=Path, action="append", default=[],
                        help="TeX file whose generated_argument_graph_macros region is rewritten")
    args = parser.parse_args(argv)
    projection, graph_payload = build(args.export, args.root, lean_tree=args.lean_tree,
                                      source_revision=args.source_revision)
    write_outputs(projection, graph_payload, args.output, args.graph_output)
    for paper in args.paper:
        text = paper.read_text(encoding="utf-8")
        paper.write_text(replace_macro_region(text, paper_macro_region(projection)), encoding="utf-8")
    summary = projection["summary"]
    print(json.dumps({"output": str(args.output), "graph_output": str(args.graph_output), **summary}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
