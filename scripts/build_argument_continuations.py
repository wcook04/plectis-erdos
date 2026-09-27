#!/usr/bin/env python3
"""Build the argument-continuation projection from the kernel export.

Input: the JSON Lines stream written by ``scripts/export_argument_continuations.lean``
(the CI artifact ``argument-continuations-<sha>``, gzip or plain). The artifact
also carries ``argument_continuations_lean_tree.txt`` (the git tree id of
``lean/`` at the exported commit) and ``argument_continuations_source_revision.txt``;
the builder reads both from beside the export, or takes ``--lean-tree`` and
``--source-revision``. Several exports of the same Lean tree combine (repeat
``--export``, the latest last): each row observes the same environment, so the
graph is built from the union of what the exports' searches found.

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
* A kernel-checked ``composition`` row is a closed proof term of its
  conclusion: it gives a reduction with no residuals (reading
  ``checked_composition``), which depends on the theorems and statements it
  composed. It is used last, so a witness chain stays the witness where one
  exists.
* ``S`` is *supplied* when some reduction has every residual supplied (least
  fixpoint). The witness reduction is recorded, so every supplied statement
  has a witness chain of corpus theorems joined by unification.
* ``S`` is *refuted* when a corpus theorem proving ``¬S`` has every residual
  supplied or the battery proves ``¬S`` (a kernel refutation), or when
  supplying ``S`` would supply a refuted statement through recorded reductions
  (a derived refutation, recorded with the refuted statement it reaches), or
  when supplying ``S`` would supply a statement together with the residuals of
  a recorded refutation of it (``derived_conflict``, recorded with that
  statement and the refuting theorem). *Open* statements are the statements
  neither supplied nor refuted.
* After supplied residuals are removed, a reduction with one residual ``A``
  is an implication ``A ⇒ S``. A strongly connected component of that graph
  with two or more open statements is a *disguise class*: its members are
  equivalent through recorded reductions, so moving between them is a change
  of coordinates.
* The *bundles* of an open statement are the minimal sets of open statements
  whose supply supplies it (AND over residuals, OR over reductions, subset
  absorption, and a budget reported as ``truncated``). Each bundle is then
  checked as a whole (``argument_graph_frontier.py``): a bundle whose members
  are jointly impossible through recorded edges is dropped and reported, and
  a bundle the target implies member by member is labelled the target
  restated (``joint_endpoint_equivalence``).
* The *leverage* of an open statement ``A`` is the set of open statements that
  become supplied when ``A`` is added and the fixpoint is recomputed.
* The *interface chain* of a weakened hypothesis lists, level by level, what
  the theorem needs of it (``argument_graph_interfaces.py``).

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

try:
    from argument_graph_frontier import EVIDENCE as JOINT_EVIDENCE, Frontier
    from argument_graph_interfaces import Interfaces
except ImportError:  # imported as the package module scripts.build_argument_continuations
    from scripts.argument_graph_frontier import EVIDENCE as JOINT_EVIDENCE, Frontier  # type: ignore
    from scripts.argument_graph_interfaces import Interfaces  # type: ignore

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "erdos249257-argument-continuations/2"
GRAPH_SCHEMA = "erdos249257-argument-continuation-graph/2"
DEFAULT_OUTPUT = ROOT / "docs" / "argument_continuations.json"
DEFAULT_GRAPH_OUTPUT = ROOT / "docs" / "argument_continuations_graph.json.gz"
LEAN_TREE_FILE = "argument_continuations_lean_tree.txt"
SOURCE_REVISION_FILE = "argument_continuations_source_revision.txt"
PROBLEMS = ("68", "243", "249", "251", "257", "269", "1041", "1049")
# Theorems the argument graph itself derived and the corpus then imported
# (idle, weakened, use-site and frontier theorems generated into Lean): the
# graph must never read its own findings back as corpus theorems.
ARGUMENT_GRAPH_MODULE = "ErdosProblems.ArgumentGraph"
BUNDLE_LIMIT = 24
BUNDLE_SIZE_LIMIT = 4
BUNDLE_DEPTH_LIMIT = 6
BUNDLE_WORK_LIMIT = 4000
BUNDLE_CONE_LIMIT = 4000
# Joint checks of bundles: work units per check and per graph (a work unit is
# one propagation step, so the results do not depend on the machine).
BUNDLE_CHECK_WORK_LIMIT = 200_000
BUNDLE_CHECK_TOTAL_WORK = 20_000_000
REFUTATION_WORK_LIMIT = 2_000_000
LIST_LIMIT = 40
DEFAULT_ROOTS = frozenset({"Erdos249257", "ErdosProblems"})

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


def row_identity(row: dict[str, Any]) -> tuple[Any, ...]:
    """What makes two export rows the same observation. A statement, a
    theorem's telescope, its idle, weakening or composition row, a literal's
    generalisation and a candidate cap are identified by what they are about;
    any other row (a match, a refutation, a battery proof, an unfolding) only
    by its whole content."""
    record = row.get("record")
    if record == "statement":
        return (record, row.get("key"))
    if record == "candidate_cap":
        return (record, row.get("statement"), row.get("search"))
    if record == "theorem":
        return (record, row.get("name"))
    if record == "idle":
        return (record, row.get("theorem"))
    if record in ("weakening", "weakening_attempt"):
        return (record, row.get("theorem"), row.get("i"))
    if record == "composition":
        return (record, row.get("theorem"), row.get("conclusion"))
    if record == "generalisation":
        return (record, row.get("theorem"), row.get("literal"), row.get("literal_type"))
    return (record, json.dumps(row, sort_keys=True, ensure_ascii=False))


def combine_exports(streams: list[list[dict[str, Any]]]) -> list[dict[str, Any]]:
    """One stream from several exports of the same Lean tree, the last first.

    Every row is an observation of the same elaborated environment: a match is
    a unification the elaborator accepted, a battery row a proof the kernel
    accepted. So the exports' searches add up, and the union is what they
    observed together. Rows that are the same observation (``row_identity``)
    are kept once, from the latest export that has them; the last export's rows
    keep their order (telescopes before the rows that use them) and the rest
    follow. The meta and summary records are the last export's, with the number
    of exports combined and of statements the combined search covered."""
    if len(streams) == 1:
        return streams[0]
    seen: set[tuple[Any, ...]] = set()
    combined: list[dict[str, Any]] = []
    for rows in reversed(streams):
        for row in rows:
            if row.get("record") in ("meta", "summary"):
                continue
            identity = row_identity(row)
            if identity not in seen:
                seen.add(identity)
                combined.append(row)
    last = streams[-1]
    meta = {**last[0], "combined_exports": len(streams)}
    summaries = [next(r for r in rows if r.get("record") == "summary") for rows in streams]
    summary = {**summaries[-1], "combined_exports": len(streams),
               "statements_searched_combined": sum(1 for r in combined if r.get("record") == "statement"),
               "truncated": any(s.get("truncated") for s in summaries)}
    return [meta, *combined, summary]


def read_exports(paths: list[Path], lean_trees: list[str | None]) -> list[dict[str, Any]]:
    """``read_export`` for one stream; for several, their combination, refused
    unless every export names the same Lean tree."""
    if len(paths) > 1 and (None in lean_trees or len(set(lean_trees)) != 1):
        raise SystemExit("exports can be combined only when each names the same Lean tree "
                         f"(found {lean_trees}); a row about one environment says nothing about another")
    return combine_exports([read_export(path) for path in paths])


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


def is_argument_graph_module(module: str) -> bool:
    """Whether a module holds theorems the argument graph derived itself."""
    return module == ARGUMENT_GRAPH_MODULE or module.startswith(ARGUMENT_GRAPH_MODULE + ".")


def composition_uses_of(theorem: str, hypotheses: Iterable[tuple[str, str]]) -> dict[str, Any]:
    """What a kernel-checked composition's term uses: the composed theorem,
    the producer it applied to each hypothesis, and those hypotheses. The
    composition stops counting when any of them is withdrawn."""
    pairs = sorted({(key, producer) for key, producer in hypotheses})
    return {"producers": frozenset({theorem, *(p for _, p in pairs if p)}),
            "statements": frozenset(k for k, _ in pairs),
            "hypotheses": pairs}


# --------------------------------------------------------------------------
# Graph


class Graph:
    def __init__(self, rows: list[dict[str, Any]], *, include_battery: bool = True,
                 include_idle: bool = True, include_weakening: bool = True):
        self.include_battery = include_battery
        self.include_idle = include_idle
        self.include_weakening = include_weakening
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
        # reduction index of each kernel-checked composition -> what its term
        # uses: {"producers", "statements", "hypotheses": [(key, producer)]}
        self.composition_uses: dict[int, dict[str, Any]] = {}
        # refutation: (statement, producer, reading, residual keys)
        self.refutations: list[tuple[str, str, str, tuple[str, ...]]] = []
        # kernel-checked idle rows, each with what the graph made of it
        self.idle: list[dict[str, Any]] = []
        self.idle_unchecked = 0
        # kernel-checked weakenings (a closed hypothesis replaced by what the
        # proof uses of it), and each weakened theorem's derived name
        self.weakenings: list[dict[str, Any]] = []
        self.weakening_unchecked = 0
        # Kernel-checked generalisations: a literal of a theorem made a variable,
        # with the obligations the proof needed of it (generalisation rows).
        self.generalisations: list[dict[str, Any]] = []
        self.generalisations_refused = 0
        # kernel-checked weakening rows the builder refused (a consequence
        # without a key, no consequence, no hypothesis key): each would have
        # dropped an obligation without replacing it
        self.weakenings_malformed: list[dict[str, Any]] = []
        self.synthetic: dict[str, str] = {}
        self._ingest(rows)

    def canon(self, key: str) -> str:
        """Representative of a statement's definitional-alias class."""
        root = key
        seen: set[str] = set()
        while self.alias.get(root, root) != root:
            if root in seen:
                raise ValueError(f"cyclic statement aliases through {root!r}")
            seen.add(root)
            root = self.alias[root]
        while self.alias.get(key, key) != root:
            self.alias[key], key = root, self.alias[key]
        return root

    @classmethod
    def from_payload(cls, payload: dict[str, Any], *, include_idle: bool = True) -> "Graph":
        """Rebuild the graph from ``argument_continuations_graph.json.gz``."""
        graph = cls([], include_battery=True, include_idle=include_idle)
        graph.alias = {str(k): str(v) for k, v in (payload.get("alias_keys") or {}).items()}
        for key in list(graph.alias):
            graph.canon(key)  # a cyclic alias payload fails here rather than looping later
        graph.compositions_checked = [dict(row) for row in payload.get("compositions_checked", [])]
        graph.weakenings = [dict(entry) for entry in payload.get("weakenings", [])]
        graph.synthetic = {e["weakened"]: e["theorem"] for e in graph.weakenings if e.get("weakened")}
        graph.generalisations = [dict(entry) for entry in payload.get("generalisations", [])]
        graph.synthetic.update({e["generalised"]: e["theorem"] for e in graph.generalisations
                                if e.get("generalised")})
        graph.meta = {"schema": payload.get("schema")}
        graph.summary = (payload.get("source") or {}).get("export_summary", {})
        for row in payload.get("statements", []):
            graph.statements[row["key"]] = {
                "key": row["key"], "type": row.get("type"), "origins": set(row.get("origins", [])),
                "consumers": set(row.get("consumers", [])), "conclusion_of": set(row.get("conclusion_of", [])),
                "constants": set(row.get("constants", [])),
                "aliases": set(row.get("aliases", [])),
                **({"is_false": True} if row.get("is_false") is True else {}),
            }
        for row in payload.get("reductions", []):
            reading = row.get("reading", "conclusion")
            if reading == "idle" and not include_idle:
                continue
            if reading == "checked_composition":
                graph.composition_uses[len(graph.reductions)] = composition_uses_of(
                    row["producer"], [(k, p) for k, p in row.get("composed_from", [])])
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
        # The graph's own findings, generated into Lean under
        # ARGUMENT_GRAPH_MODULE and imported with the coverage targets: left
        # out, with every row that uses one as theorem or producer.
        findings = {row["name"] for row in rows if row.get("record") == "theorem"
                    and is_argument_graph_module(row.get("module") or "")}
        findings |= {row["weakened"] for row in rows if row.get("record") == "weakening"
                     and row.get("theorem") in findings and row.get("weakened")}
        self.findings_skipped = {"theorems": sum(1 for row in rows if row.get("record") == "theorem"
                                                 and row["name"] in findings), "rows": 0}
        # Theorems the export derived by weakening a hypothesis, by name.
        for row in rows:
            if row.get("record") == "weakening" and row.get("kernel_checked") and row.get("weakened") \
                    and row.get("theorem") not in findings:
                self.synthetic[row["weakened"]] = row.get("theorem")
        derived = set(self.synthetic) if not self.include_weakening else set()

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
        weakening_rows: list[dict[str, Any]] = []
        generalisation_rows: list[dict[str, Any]] = []
        composition_rows: list[dict[str, Any]] = []
        for row in rows:
            record = row.get("record")
            if findings and (
                    (record == "theorem" and row.get("name") in findings)
                    or (record in ("match", "refutation") and row.get("producer") in findings)
                    or (record in ("idle", "weakening") and row.get("theorem") in findings)
                    or (record == "composition" and (row.get("theorem") in findings or any(
                        (h or {}).get("producer") in findings for h in row.get("hypotheses") or [])))):
                self.findings_skipped["rows"] += 1
                continue
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
                node = self._statement(row["key"], row.get("type"), row.get("origin", "statement"),
                                       row.get("constants", ()))
                if row.get("is_false") is True:
                    node["is_false"] = True
            elif record == "unfold":
                self._statement(row["unfolded"], row.get("type"), "unfolding", row.get("constants", ()))
            elif record in ("match", "refutation") and row.get("producer") in derived:
                continue  # a weakened theorem, left out with the weakenings
            elif record == "composition":
                if row.get("theorem") in derived or any(
                        (h or {}).get("producer") in derived for h in row.get("hypotheses") or []):
                    continue  # composes a weakened theorem, left out with the weakenings
                self.compositions_checked.append(row)
                if row.get("kernel_checked") is True and row.get("conclusion"):
                    composition_rows.append(row)
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
                if canon(row["statement"]) not in self.statements:
                    # a stream cut off before the statement row: keep the refuted statement addressable
                    self._statement(row["statement"], None, "refutation")
                self.refutations.append((canon(row["statement"]), row["producer"],
                                         row.get("reading", "conclusion"),
                                         tuple(sorted({canon(r["key"]) for r in residuals}))))
            elif record == "battery_refutation" and self.include_battery and row.get("kernel_checked"):
                if canon(row["statement"]) not in self.statements:
                    self._statement(row["statement"], None, "refutation")
                self.refutations.append((canon(row["statement"]), f"tactic:{row.get('tactic')}", "battery", ()))
            elif record == "idle" and self.include_idle:
                if row.get("kernel_checked"):
                    idle_rows.append(row)
                else:
                    self.idle_unchecked += 1
            elif record == "weakening" and self.include_weakening:
                if row.get("kernel_checked"):
                    weakening_rows.append(row)
                else:
                    self.weakening_unchecked += 1
            elif record == "generalisation":
                if row.get("status") == "generalised" and row.get("kernel_checked") and row.get("generalised") \
                        and row.get("theorem") not in findings:
                    generalisation_rows.append(row)
                    self.synthetic[row["generalised"]] = row.get("theorem")
                else:
                    self.generalisations_refused += 1
            elif record == "candidate_cap":
                self.caps.append(row)
            elif record in ("theorem_error", "statement_error"):
                self.errors.append(row)
        for row in idle_rows:
            self._ingest_idle(row, binders_of.get(row.get("theorem")), add_reduction)
        for row in weakening_rows:
            self._ingest_weakening(row, binders_of.get(row.get("theorem")), add_reduction)
        for row in generalisation_rows:
            self._ingest_generalisation(row, add_reduction)
        # A kernel-checked composition is a closed proof term of its conclusion
        # (the exporter instantiated every binder, so a conclusion that mentions
        # a hypothesis becomes a statement of its own): a reduction without
        # residuals, after all the others, that depends on what the term uses.
        for row in composition_rows:
            theorem = row.get("theorem") or "composition"
            node = self._statement(row["conclusion"], row.get("type"), "checked_composition")
            node["conclusion_of"].add(theorem)
            used = [(canon(h["key"]), str(h.get("producer") or ""))
                    for h in row.get("hypotheses") or [] if isinstance(h, dict) and h.get("key")]
            before = len(self.reductions)
            add_reduction(row["conclusion"], theorem, "checked_composition", ())
            if len(self.reductions) > before:
                self.composition_uses[before] = composition_uses_of(theorem, used)
        if not self.include_weakening:
            self.synthetic = {}

    def _ingest_generalisation(self, row: dict[str, Any], add_reduction) -> None:
        """A kernel-checked generalisation: the theorem with a literal made a
        variable and the obligations its proof needed of that literal assumed.
        The generalised statement is closed and proved, so it is supplied; its
        theorem is a synthetic producer credited to the original."""
        entry = {key: row.get(key) for key in ("theorem", "literal", "literal_type", "uniform", "witness",
                                                "generalised", "type", "key")}
        entry["obligations"] = [o.get("type") for o in row.get("obligations", []) or []]
        entry["discharged"] = [{"type": d.get("type"), "tactic": d.get("tactic")}
                               for d in row.get("discharged", []) or []]
        if row.get("key"):
            node = self._statement(row["key"], row.get("type"), "generalisation")
            node["conclusion_of"].add(row["generalised"])
            add_reduction(row["key"], row["generalised"], "generalisation", ())
        self.generalisations.append(entry)

    def _ingest_weakening(self, row: dict[str, Any], binders: list[dict[str, Any]] | None,
                          add_reduction) -> None:
        """A kernel-checked weakening: the theorem's proof uses the closed
        hypothesis H only through use sites proving the consequences C, and the
        kernel accepted the theorem with H replaced by them. Each C whose
        implication H → C the kernel accepted is reduced to H (``use_site``), so
        supplying H supplies C and refuting C refutes H. The weakened theorem
        reduces the conclusion to the obligations that remain and the
        consequences (``weakening``); its matches arrive under its own name."""
        canon = self.canon
        name = row.get("theorem")
        synthetic = row.get("weakened") or None
        theorem = self.theorems.get(name)
        hypothesis = canon(row["hypothesis"]) if row.get("hypothesis") else None
        # A row that would drop the hypothesis without naming every statement
        # replacing it is refused: an obligation must never vanish.
        raw = row.get("consequences")
        refusal = None
        if not isinstance(raw, list) or not raw:
            refusal = "no consequence"
        elif any(not isinstance(c, dict) or not c.get("key") for c in raw):
            refusal = "a consequence without a statement key"
        elif binders is not None:
            binder = next((b for b in binders if b.get("i") == row.get("i")), None)
            role, key, _, is_prop = binder_obligation(binder) if binder else (None, None, None, False)
            if role != "residual" or not is_prop or (hypothesis is not None and canon(key) != hypothesis):
                refusal = "binder i is not the closed hypothesis the row names"
        if refusal:
            self.weakenings_malformed.append({"theorem": name, "i": row.get("i"), "reason": refusal})
            return
        consequences: list[dict[str, Any]] = []
        for c in raw:
            node = self._statement(c["key"], c.get("type"), "consequence")
            if synthetic:
                node["consumers"].add(synthetic)
            key = canon(c["key"])
            implied = bool(c.get("implication_kernel_checked"))
            if hypothesis and implied:
                add_reduction(key, name, "use_site", [hypothesis])
            consequences.append({"key": key, "type": c.get("type"), "via": c.get("via", []),
                                 "sites": c.get("sites", []), "implication_kernel_checked": implied})
        entry: dict[str, Any] = {
            "theorem": name, "i": row.get("i"), "weakened": synthetic,
            "hypothesis": hypothesis, "hypothesis_type": row.get("hypothesis_type"),
            "consequences": consequences, "type": row.get("type"),
            "conclusion": theorem.get("conclusion_key") if theorem else None,
            "residuals": [], "reduction": False, "reason": None,
        }
        if theorem is None or binders is None:
            entry["reason"] = "no theorem row"
        else:
            remaining = obligations(b for b in binders if b.get("i") != row.get("i"))
            others = sorted({canon(key) for key, _ in remaining["residuals"]})
            residuals = sorted(set(others) | {c["key"] for c in consequences})
            entry["residuals"] = residuals
            entry["other_obligations"] = others
            schematic = bool(remaining["schematic_props"] or remaining["schematic_witnesses"])
            entry["schematic_obligations"] = schematic
            if not (theorem["conclusion_closed"] and theorem["conclusion_key"]):
                entry["reason"] = "conclusion mentions a binder"
            elif schematic:
                entry["reason"] = "an obligation that mentions another binder remains"
            else:
                entry["reduction"] = add_reduction(theorem["conclusion_key"], synthetic or name, "weakening",
                                                   residuals)
                if not entry["reduction"]:
                    entry["reason"] = "tautological"
        self.weakenings.append(entry)

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
        uses = self.composition_uses

        def usable(index: int) -> bool:
            head, producer, reading, _ = self.reductions[index]
            if head in exclude_heads or producer in exclude_producers or reading in exclude_readings:
                return False
            used = uses.get(index)
            # A composed term stops counting when anything it applied is withdrawn.
            return not (used and (used["producers"] & exclude_producers or used["statements"] & exclude_heads))

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

        def settle() -> None:
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

        for index, (head, _, _, residuals) in enumerate(self.reductions):
            if residuals or index in uses or not usable(index):
                continue
            if head not in supplied:
                supplied.add(head)
                witness[head] = index
                queue.append(head)
        for key in extra:
            if key not in supplied:
                supplied.add(key)
                witness[key] = -1
                queue.append(key)
        settle()
        # Checked compositions last: the supplied set is the same either way,
        # and a witness chain stays the witness where one exists.
        for index in sorted(uses):
            head = self.reductions[index][0]
            if head not in supplied and usable(index):
                supplied.add(head)
                witness[head] = index
                queue.append(head)
        settle()
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
        # A statement whose supply would supply another statement together
        # with the residuals of a recorded refutation of it is refuted as well
        # (derived_conflict): the propagation above reaches only refutations
        # whose residuals the graph already supplies. The joint-question index
        # holds self.refuted itself, so it sees these refutations once they
        # are added, and serves the bundle checks afterwards.
        frontier = Frontier(self, supplied=self.supplied, refuted=self.refuted)
        self.refuted_conflict, self.refutation_conflict_stats = frontier.refuted_alone(
            k for k in self.statements if k not in self.supplied and k not in self.refuted)
        for key, record in self.refuted_conflict.items():
            self.refuted.setdefault(key, record)
        # A statement both supplied and refuted would mean the corpus proves a
        # contradiction (or that two different statements share a key).
        self.inconsistent = sorted(set(self.refuted) & self.supplied)
        frontier.base_conflicts = list(self.inconsistent)
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
        for cache in ("_reduced_by_head", "_leverage_cache", "_class_closure", "_frontier", "_bundle_cache",
                      "_bundle_check_work", "_interfaces"):
            self.__dict__.pop(cache, None)
        self._frontier = frontier
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
            refuted = {**{k: {"kind": "kernel", "producer": p, "reading": r} for k, (p, r) in kernel.items()},
                       **derived}
            dropped = {d["key"] for entry in self.idle for d in entry.get("dropped", [])
                       if d.get("key") and d["key"] in self.statements
                       and d["key"] not in supplied and d["key"] not in refuted}
            conflict, _ = Frontier(self, supplied=supplied, refuted=refuted,
                                   exclude_readings=without).refuted_alone(dropped)
            derived = {**derived, **conflict}
        else:
            supplied, kernel = self.supplied, self.refuted_kernel
            derived = {**self.refuted_derived, **self.refuted_conflict}
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

    def frontier(self) -> Frontier:
        """The joint-question index over this analysed graph."""
        index = self.__dict__.get("_frontier")
        if index is None:
            index = self._frontier = Frontier(self)
        return index

    def interfaces(self) -> Interfaces:
        """The interface chains of this analysed graph's weakenings."""
        index = self.__dict__.get("_interfaces")
        if index is None:
            index = self._interfaces = Interfaces(self)
        return index

    def bundles(self, key: str) -> tuple[list[list[str]], bool]:
        """The bundles of ``key`` that are not jointly impossible, and whether a
        limit pruned their enumeration (see ``bundle_report``)."""
        kept, truncated, _ = self.bundle_report(key)
        return kept, truncated

    def bundle_report(self, key: str) -> tuple[list[list[str]], bool, list[dict[str, Any]]]:
        """Each candidate bundle of ``key`` checked as a whole over the recorded
        edges. A bundle whose members are jointly impossible (their closure
        supplies a refuted statement or False) is dropped from the list; a
        bundle the target implies member by member stays, labelled the target
        restated (``joint_endpoint_equivalence``); a check that runs out of
        work stays, labelled ``unknown_budget``. The third value holds the
        check of every candidate that was dropped, is a restatement, or is
        unknown, with witnesses. The work budget is shared by the graph's
        checks and counted in propagation steps, so the answer does not depend
        on the machine."""
        cache = self.__dict__.setdefault("_bundle_cache", {})
        if key in cache:
            kept, truncated, checks = cache[key]
            return [list(b) for b in kept], truncated, [dict(c) for c in checks]
        candidates, truncated = self._candidate_bundles(key)
        kept: list[list[str]] = []
        checks: list[dict[str, Any]] = []
        for bundle in candidates:
            spent = self.__dict__.get("_bundle_check_work", 0)
            left = BUNDLE_CHECK_TOTAL_WORK - spent
            if left <= 0:
                check = {"assumptions": bundle, "status": "unknown_budget", "endpoint_relation": "unknown_budget",
                         "complete_for_recorded_edges": False, "evidence_class": JOINT_EVIDENCE,
                         "satisfiability": "not_established",
                         "reason": "the graph's budget for joint checks is spent"}
            else:
                check = self.frontier().check(bundle, target=key, max_work=min(BUNDLE_CHECK_WORK_LIMIT, left))
                self._bundle_check_work = spent + check.get("work", 0)
            if check["status"] != "refuted_jointly":
                kept.append(bundle)
            if (check["status"] != "no_recorded_conflict"
                    or check.get("endpoint_relation") != "not_established_by_recorded_edges"):
                checks.append(check)
        cache[key] = (kept, truncated, checks)
        return [list(b) for b in kept], truncated, [dict(c) for c in checks]

    def _candidate_bundles(self, key: str) -> tuple[list[list[str]], bool]:
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

    def leverage(self, key: str, limit: int = 100000) -> frozenset[str]:
        """Open statements supplied once ``key`` is supplied (memoised by the
        statement and the step bound, and immutable, so no caller can change
        what the next one reads). The members of a disguise class imply each
        other, so they share one closure, computed once per class; a closure
        the bound cut short is not shared, since it depends on where it
        started."""
        cache = self.__dict__.setdefault("_leverage_cache", {})
        token = (key, limit)
        if token in cache:
            return cache[token]
        component = self.component.get(key)
        closures = self.__dict__.setdefault("_class_closure", {})
        if component is not None and len(self.components[component]) >= 2 and (component, limit) in closures:
            result = closures[(component, limit)] - {key}
        else:
            gained, complete = self._leverage(key, limit)
            result = frozenset(gained)
            if complete and component is not None and len(self.components[component]) >= 2:
                closures[(component, limit)] = result | {key}
        cache[token] = result
        return result

    def _leverage(self, key: str, limit: int) -> tuple[set[str], bool]:
        if key in self.supplied or key in self.refuted:
            return set(), True
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
        return gained, not queue

    def criticality(self, *, statement: str | None = None, producer: str | None = None) -> set[str]:
        """Supplied statements that lose every kernel witness chain when the
        given statement is no longer supplied, or the given theorem is
        withdrawn: the answer to "what fails without it". Withdrawing a
        theorem withdraws the theorems the export derived from its proof by
        weakening, and every checked composition that applied either."""
        producers: set[str] = set()
        if producer:
            producers = {producer} | {name for name, original in self.synthetic.items() if original == producer}
        supplied, _ = self.supply(
            exclude_heads=frozenset([statement]) if statement else frozenset(),
            exclude_producers=frozenset(producers))
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
        used = self.composition_uses.get(index)
        if used is not None:
            # One kernel-checked term: the hypotheses it composed, and with what.
            node["kernel_checked_composition"] = True
            node["composed_from"] = [{"statement": k, "type": self.statements.get(k, {}).get("type"),
                                      "producer": p} for k, p in used["hypotheses"]]
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
    row is a kernel-checked term when ``kernel_checked_composition`` says the
    exporter composed that theorem and the kernel accepted it. A statement
    only a checked composition supplies (its conclusion mentions a hypothesis,
    so no reduction of the theorem reaches it) is listed with the hypotheses
    the term composed."""
    direct = {head for index, (head, _, _, residuals) in enumerate(graph.reductions)
              if not residuals and index not in graph.composition_uses}
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
        used = graph.composition_uses.get(index)
        if used is not None:
            for residual, supplier in used["hypotheses"]:
                suppliers.append({"statement": residual, "type": graph.statements.get(residual, {}).get("type"),
                                  "supplied_by": supplier or None})
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
            "paper_rows_of_conditional_theorem": papers.get(graph.synthetic.get(producer, producer), []),
        })
    out.sort(key=lambda row: (not row["paper_rows_of_conditional_theorem"], row["via"]))
    return out


# Arithmetic nobody writes in a statement: a numeral subtracted from a numeral
# (``0 - 1``, the ``1 - 1`` of ``n - 1 + 1 - 1``), or zero added, multiplied or
# divided (``0 / (0 + 0)``). Such a statement is an instance the unifier
# produced by substituting literals. An exponent (``2 ^ 3 - 1``), a projection
# (``x.1 - 1``), a quotient or product on the right (``1 - 1 / 2``) and a
# rational literal (``1 / 2``) do not count.
LITERAL_ARITHMETIC = (
    re.compile(r"(?<!\^ )(?<![\w.'])\d+ - \d+(?![\w.]| ?[/*^•])"),
    re.compile(r"(?<![\w.'^])0 [+*/] "),
    re.compile(r" [+*] 0(?![\w.])"),
)


def instantiation_artifact(text: str | None) -> bool:
    """Whether a statement's rendering does literal arithmetic nobody writes
    (``LITERAL_ARITHMETIC``): a likely instantiation artifact, ranked below
    the rest and marked, never hidden."""
    return bool(text) and any(pattern.search(text) for pattern in LITERAL_ARITHMETIC)


def paper_inputs(graph: "Graph", papers_of: Any, problem: str) -> list[dict[str, Any]]:
    """The closed obligations the graph does not supply of the theorems that
    problem ``problem``'s papers cite (the paper-to-Lean ledger), each with the
    paper results that assume it: the problem's named inputs, which anchor its
    frontier. An obligation the theorem's proof never uses (an idle row)
    is marked. Open inputs first, then refuted ones (the results that assume
    them are vacuous); within each, literal arithmetic last, then the most
    assumed."""
    idle_dropped: dict[str, set[str]] = defaultdict(set)
    for entry in graph.idle:
        for dropped in entry.get("dropped", []):
            if dropped.get("key"):
                idle_dropped[entry.get("theorem")].add(dropped["key"])
    inputs: dict[str, dict[str, Any]] = {}
    for name in sorted(graph.theorems):
        rows = [p for p in papers_of(name) or [] if str(p.get("problem")) == str(problem)]
        if not rows:
            continue
        for key in graph.theorems[name].get("hypotheses", []):
            if key in graph.supplied:
                continue
            entry = inputs.setdefault(key, {
                "key": key, "type": graph.statements.get(key, {}).get("type"), "status": graph.status(key),
                "artifact": instantiation_artifact(graph.statements.get(key, {}).get("type")),
                "results": [], "theorems": []})
            if name not in entry["theorems"]:
                entry["theorems"].append(name)
            for row in rows:
                entry["results"].append({"label": row.get("label"), "paper": row.get("paper"),
                                         "side": row.get("side"), "source": row.get("source"),
                                         "comparator": row.get("comparator"), "theorem": name,
                                         "unused_by_proof": key in idle_dropped.get(name, set())})
    for entry in inputs.values():
        entry["result_count"] = len({(r["paper"], r["label"]) for r in entry["results"]})
    return sorted(inputs.values(), key=lambda e: (e["status"] != "open", e["artifact"], -e["result_count"],
                                                  e["type"] or "", e["key"]))


def joint_check_row(check: dict[str, Any]) -> dict[str, Any]:
    """A joint check as the projection keeps it: the verdict, and the
    witnesses of a conflict or of a restatement of the target."""
    row = {k: check[k] for k in ("assumptions", "status", "endpoint_relation", "evidence_class",
                                 "satisfiability", "reason") if k in check}
    if check.get("conflicts"):
        row["conflicts"] = check["conflicts"]
    if check.get("endpoint_relation") == "joint_endpoint_equivalence":
        row["implied_by_target"] = check.get("implied_by_target", [])
        for key in ("target_witness", "reverse_witnesses"):
            if key in check:
                row[key] = check[key]
    return row


INTERFACE_LIST_LIMIT = 20


def interface_section(graph: "Graph", papers: dict[str, list[dict[str, Any]]],
                      theorem_problems: dict[str, str | None]) -> dict[str, Any]:
    """The projection's interface chains: per problem, the chains of the
    problem's theorems (paper-cited ones, then open hypotheses, first), and for
    every interface statement the paper results whose chains need it."""
    index = graph.interfaces()
    chains = index.chains()

    def labels(name: str) -> list[dict[str, Any]]:
        return [{"row": p.get("row"), "paper": p.get("paper"), "side": p.get("side"), "label": p.get("label"),
                 "comparator": p.get("comparator")} for p in papers.get(name, [])][:6]

    def order(chain: dict[str, Any]) -> tuple:
        hypothesis = chain.get("hypothesis") or {}
        return (not papers.get(chain["theorem"]), hypothesis.get("status") != "open", -chain["depth"],
                chain["theorem"], chain["i"] if isinstance(chain["i"], int) else -1)

    by_problem: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for chain in sorted(chains, key=order):
        problem = theorem_problems.get(chain["theorem"]) or "unattributed"
        by_problem[problem].append({**chain, "problem": problem, "papers": labels(chain["theorem"])})
    needed = index.needed_by()
    rows = []
    for key, users in needed.items():
        results = [{**user, "papers": labels(user["theorem"])} for user in users]
        rows.append({"key": key, "type": graph.statements.get(key, {}).get("type"), "status": graph.status(key),
                     "needed_by": results[:12], "needed_by_count": len(results),
                     "paper_results": len({(p["row"], p["label"]) for r in results for p in r["papers"]})})
    rows.sort(key=lambda r: (r["status"] != "open", -r["paper_results"], -r["needed_by_count"], r["key"]))
    levels = [level for chain in chains for level in chain["levels"][1:]]
    return {
        "summary": {
            "interface_chains": len(chains),
            "interface_chains_deeper_than_one_level": sum(1 for c in chains if c["depth"] >= 2),
            "interface_statements": len(needed),
            "interface_statements_open": sum(1 for k in needed if graph.status(k) == "open"),
            "interface_levels_jointly_impossible": sum(1 for lv in levels if lv["joint"]["status"]
                                                       == "refuted_jointly"),
            "interface_levels_restating_hypothesis": sum(1 for lv in levels if lv["joint"].get("restates_hypothesis")),
        },
        "by_problem": {p: rows_[:INTERFACE_LIST_LIMIT] for p, rows_ in sorted(by_problem.items())},
        "chain_counts": {p: len(rows_) for p, rows_ in sorted(by_problem.items())},
        "needed_by": rows[:INTERFACE_LIST_LIMIT * 10],
    }


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


def build(export_path: Path | list[Path], root: Path = ROOT, *, lean_tree: str | None = None,
          source_revision: str | None = None, include_idle: bool = True
          ) -> tuple[dict[str, Any], dict[str, Any]]:
    # Several exports of one Lean tree combine (``combine_exports``); the last
    # is the export whose provenance the graph carries first.
    export_paths = export_path if isinstance(export_path, list) else [export_path]
    export_path = export_paths[-1]
    trees = [resolve_lean_tree(path, lean_tree) for path in export_paths]
    rows = read_exports(export_paths, trees)
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
    # A weakened theorem is attributed like the theorem it was derived from.
    for derived_name, original in graph.synthetic.items():
        theorem_problems[derived_name] = theorem_problems.get(original)
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
                bundles, truncated, checks = graph.bundle_report(key)
                card["bundles"] = bundles
                card["bundles_truncated"] = truncated
                if checks:
                    card["bundle_checks"] = [joint_check_row(check) for check in checks]
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
        inputs = paper_inputs(graph, lambda name: papers.get(name, []), problem)
        per_problem[problem] = {
            # The problem's named inputs: what the theorems its papers cite
            # assume and the graph does not supply. These anchor its frontier.
            "paper_inputs": [{**{k: v for k, v in inputs_row.items() if k != "results"},
                              "results": inputs_row["results"][:8]} for inputs_row in inputs[:LIST_LIMIT]],
            "paper_input_count": len(inputs),
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

    # What the weakenings gain: statements supplied only when the weakened
    # theorems and the use-site reductions take part.
    if graph.weakenings:
        without_weakening, _ = graph.supply(exclude_producers=frozenset(graph.synthetic),
                                            exclude_readings=frozenset({"weakening", "use_site"}))
        gained_by_weakening = graph.supplied - without_weakening
    else:
        gained_by_weakening = set()
    # What the checked compositions gain: statements no reduction but a
    # kernel-checked composed term supplies (a conclusion that mentions a
    # hypothesis becomes a closed statement once the term fixes it).
    if graph.composition_uses:
        without_compositions, _ = graph.supply(exclude_readings=frozenset({"checked_composition"}))
        gained_by_composition = graph.supplied - without_compositions
    else:
        gained_by_composition = set()

    def weakening_row(entry: dict[str, Any]) -> dict[str, Any]:
        name = entry["theorem"]
        conclusion = entry.get("conclusion")
        hypothesis = entry.get("hypothesis")
        return {
            "theorem": name,
            "problem": theorem_problems.get(name),
            "source": refs.get(name),
            "papers": papers.get(name, []),
            "hypothesis": {"key": hypothesis, "type": entry.get("hypothesis_type"),
                           "status": graph.status(hypothesis) if hypothesis in graph.statements else None},
            "uses_only": [{"key": c["key"], "type": c.get("type"),
                           "status": graph.status(c["key"]) if c["key"] in graph.statements else None,
                           "via": c.get("via", []), "sites": c.get("sites", [])}
                          for c in entry.get("consequences", [])],
            "weakened_theorem": entry.get("weakened"),
            "weakened_statement": entry.get("type"),
            "conclusion": conclusion,
            "conclusion_type": graph.theorems.get(name, {}).get("conclusion_type"),
            "conclusion_status": graph.status(conclusion) if conclusion in graph.statements else None,
            "conclusion_supplied_only_by_weakening": conclusion in gained_by_weakening,
            "reduction": entry.get("reduction"),
            "reason_without_reduction": entry.get("reason"),
        }

    weakening_rows = sorted(
        (weakening_row(e) for e in graph.weakenings),
        key=lambda r: (not r["conclusion_supplied_only_by_weakening"], not r["papers"],
                       r["hypothesis"]["status"] != "open",
                       not all(c["status"] == "supplied" for c in r["uses_only"]), r["theorem"]))
    consequence_keys = {c["key"] for e in graph.weakenings for c in e.get("consequences", [])}
    kernel_refuted = {k: v for k, v in graph.refuted.items() if v["kind"] == "kernel"}
    derived_refuted = {k: v for k, v in graph.refuted.items() if v["kind"] == "derived"}
    conflict_refuted = {k: v for k, v in graph.refuted.items() if v["kind"] == "derived_conflict"}
    theorem_modules = {t["module"] for t in graph.theorems.values() if t.get("module")}
    summary = {
        "theorems": len(graph.theorems),
        # the graph's own findings in Lean (ARGUMENT_GRAPH_MODULE), and the
        # rows that used one: never read back as corpus theorems
        "argument_graph_derived_theorems_skipped": graph.findings_skipped["theorems"],
        "argument_graph_derived_rows_skipped": graph.findings_skipped["rows"],
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
        "refuted_statements_by_conflict": len(conflict_refuted),
        "refutation_propagation_truncated": graph.refutation_truncated,
        "refutation_conflict_checks": graph.refutation_conflict_stats["closures"],
        "refutation_conflict_checks_unknown": graph.refutation_conflict_stats["incomplete"],
        "vacuous_theorems": len({name for name, _ in graph.vacuous_theorems}),
        "supplied_and_refuted": len(graph.inconsistent),
        "kernel_checked_compositions": sum(1 for row in graph.compositions_checked
                                           if row.get("kernel_checked")),
        "statements_supplied_only_by_checked_compositions": len(gained_by_composition),
        "compositions": len(composed),
        "compositions_of_paper_cited_conditional_theorems": sum(
            1 for row in composed if row["paper_rows_of_conditional_theorem"]),
        "idle_theorems_kernel_checked": len(graph.idle),
        "idle_theorems_unchecked": graph.idle_unchecked,
        "idle_reductions": sum(1 for e in graph.idle if e.get("reduction")),
        "idle_dropping_open": len(idle_dropping_open),
        "weakened_theorems": len({e["theorem"] for e in graph.weakenings}),
        "generalised_theorems": len({e["theorem"] for e in graph.generalisations}),
        "generalisations_kernel_checked": len(graph.generalisations),
        "generalisations_uniform": sum(1 for e in graph.generalisations if e.get("uniform")),
        "generalisations_refused": graph.generalisations_refused,
        "weakenings_kernel_checked": len(graph.weakenings),
        "weakenings_unchecked": graph.weakening_unchecked,
        "weakenings_refused_malformed": len(graph.weakenings_malformed),
        "weakenings_of_open_hypotheses": sum(1 for r in weakening_rows if r["hypothesis"]["status"] == "open"),
        "weakening_consequences": len(consequence_keys),
        "weakening_consequences_supplied": sum(1 for k in consequence_keys if k in graph.supplied),
        "weakening_consequences_refuted": sum(1 for k in consequence_keys if k in graph.refuted),
        "statements_supplied_only_by_weakening": len(gained_by_weakening),
        "semantic_label_disagreements": audit["semantic_logical_class"]["disagreement_count"],
        "barriers": len(barriers["entries"]),
        "barriers_in_graph": sum(1 for e in barriers["entries"] if e["in_graph"]),
        "open_statements_constrained_by_barriers": len(barriers["constrains"]),
    }
    # Joint checks of the bundles the projection lists (the sinks' bundles).
    bundle_checks = [check for _, _, checks in graph.__dict__.get("_bundle_cache", {}).values() for check in checks]
    summary.update({
        "bundles_jointly_impossible": sum(1 for c in bundle_checks if c["status"] == "refuted_jointly"),
        "bundles_restating_target": sum(1 for c in bundle_checks
                                        if c.get("endpoint_relation") == "joint_endpoint_equivalence"),
        "bundle_checks_unknown": sum(1 for c in bundle_checks if c["status"] == "unknown_budget"
                                     or c.get("endpoint_relation") == "unknown_budget"),
        "bundle_check_work": graph.__dict__.get("_bundle_check_work", 0),
    })
    interfaces = interface_section(graph, papers, theorem_problems)
    summary.update(interfaces.pop("summary"))
    alarms = sentinel_alarms(graph)
    summary["sentinel_alarms"] = len(alarms)
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
    if len(export_paths) > 1:
        source["combined_exports"] = [
            {"export_digest": file_digest(path),
             "source_revision": resolve_source_revision(path, None)} for path in export_paths]
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
            if record["kind"] == "derived_conflict":
                row["reaches_refuted_by"] = record.get("refuted_by")
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
                       "every residual supplied; derived: supplying the statement would supply a refuted one; "
                       "derived_conflict: supplying the statement would supply another statement together with "
                       "the residuals of a recorded refutation of it (reaches names that statement)",
            "open": "neither supplied nor refuted",
            "implication": "a reduction left with exactly one open residual",
            "disguise_class": "strongly connected component of implications with two or more open statements: "
                              "statements equivalent through recorded reductions",
            "bundle": "a minimal set of open statements whose supply supplies the statement; bundles_truncated "
                      "says whether a limit pruned the enumeration. Each bundle is checked as a whole over the "
                      "recorded edges (bundle_checks): one whose members are jointly impossible is dropped, one the "
                      "target implies member by member is the target restated (joint_endpoint_equivalence), and a "
                      "check that ran out of work reads unknown_budget; the evidence class is "
                      "derivation_over_recorded_edges",
            "leverage": "number of open statements supplied once the statement is supplied",
            "sink": "an open statement with a reduction into it that implies nothing outside its own class",
            "composition": "a statement supplied only through a conditional theorem whose hypotheses other "
                           "reductions supply (a witness chain); kernel_checked_composition marks the ones the "
                           "exporter composed and the kernel accepted. A kernel-checked composition is a closed "
                           "proof of its conclusion and supplies it (reading checked_composition), after every "
                           "other reduction, and stops counting when a theorem or statement it composed is withdrawn",
            "idle": "a theorem whose proof never uses some proposition binders; the kernel accepted the stronger "
                    "statement without them",
            "weakening": "a theorem whose proof uses a closed hypothesis H only through use sites (L h, h.1, h a) "
                         "proving propositions C; the kernel accepted the theorem with H replaced by the C, and "
                         "H → C for each. uses_only lists the C; a reduction of each C to H (reading use_site) "
                         "lets a refutation of C refute H. A kernel-checked row whose consequences are missing or "
                         "unkeyed, or whose binder is not the hypothesis it names, is refused (weakenings_refused)",
            "interface_chain": "what a theorem needs of a weakened hypothesis H, level by level. Level 0 is H, "
                               "level 1 the consequences its proof uses; a member refines when the lemma at its use "
                               "site is itself weakened and the export matched that weakened lemma against the "
                               "member (a recorded reduction), and level k+1 replaces each refinable member of level "
                               "k by what the lemma uses, dropping members the others supply (implied). Every level "
                               "suffices for the theorem with its other obligations; each keeps its joint check: "
                               "members jointly impossible, or the level restating H (the level implies H back)",
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
        "weakenings": weakening_rows[:LIST_LIMIT * 6],
        "weakenings_refused": graph.weakenings_malformed[:LIST_LIMIT],
        "generalisations": sorted(graph.generalisations,
                                  key=lambda e: (not papers.get(e["theorem"]), e["theorem"] or ""))[:LIST_LIMIT * 3],
        "interfaces": interfaces,
        "audit": audit,
        "sentinel_alarms": alarms,
    }

    def reduction_row(index: int, head: str, producer: str, reading: str, residuals: tuple[str, ...]
                      ) -> dict[str, Any]:
        row: dict[str, Any] = {"statement": head, "producer": producer, "reading": reading,
                               "residuals": list(residuals)}
        used = graph.composition_uses.get(index)
        if used is not None:
            row["composed_from"] = [[k, p] for k, p in used["hypotheses"]]
        return row

    graph_payload = {
        "schema": GRAPH_SCHEMA,
        "source": source,
        # Keys of unfoldings merged into their named statement, so a key read
        # from the export still resolves after the graph is reloaded.
        "alias_keys": {k: graph.canon(k) for k in sorted(graph.alias)},
        "compositions_checked": graph.compositions_checked,
        "statements": [
            {
                "key": key,
                "type": node.get("type"),
                **({"is_false": True} if node.get("is_false") is True else {}),
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
        "reductions": [reduction_row(index, *reduction) for index, reduction in enumerate(graph.reductions)],
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
        "weakenings": graph.weakenings,
        "generalisations": graph.generalisations,
        "theorems": [
            {**theorem_card(name), "module": t["module"], "problem": theorem_problems.get(name),
             "hypotheses": t["hypotheses"], "schematic_hypotheses": t["schematic_hypotheses"],
             "witness_obligations": t["witness_obligations"], "after_idle": t.get("after_idle"),
             "conclusion": t["conclusion_key"], "conclusion_type": t["conclusion_type"]}
            for name, t in sorted(graph.theorems.items())
        ],
    }
    return projection, graph_payload


# Statements the graph must never report as settled. Supplying False means
# a supply chain is unsound (an exporter or builder defect, never a proof);
# supplying or refuting a registered open target means either such a defect or
# a solution, and either way a person looks before any number is used. The
# pre-review exporter supplied every one of these through producers that need
# a witness of an empty type.
SENTINELS = {
    "False": "a supply chain that proves False is unsound",
    "1 / 2 ∈ Erdos249257.mersenneAchievementSet": "open: remaining_open.half_value_membership",
    "1 / 21 ∈ Erdos249257.mersenneAchievementSet": "open: remaining_open.twenty_one_permanent_affine_supercapacity",
    "Irrational (∑' (n : ℕ), ↑n.totient / 2 ^ n)": "open: remaining_open.erdos_249_irrationality",
}


def sentinel_alarms(graph: "Graph") -> list[dict[str, Any]]:
    """Statements whose status means the graph must be read before any number
    is used, each with the witness chain to inspect: every statement the graph
    both supplies and refutes, False supplied, and a registered open target
    supplied or refuted. Refuting False is not an alarm. A contradiction is
    never ``overridable``; an open target settled may be a solution, which a
    person checks before the target leaves ``SENTINELS``."""
    alarms = []
    for key in graph.inconsistent:
        alarms.append({"key": key, "type": graph.statements.get(key, {}).get("type"),
                       "status": "supplied_and_refuted", "overridable": False,
                       "reason": "the graph supplies and refutes the same statement: a supply chain or a "
                                 "refutation is unsound, or two statements share a key",
                       "witness": graph.proof_tree(key, limit=3), "refutation": graph.refuted.get(key)})
    contradictions = set(graph.inconsistent)
    for key, node in sorted(graph.statements.items()):
        if key in contradictions:
            continue
        texts = {node.get("type"), *node.get("aliases", ())}
        hits = sorted((text for text in texts if text in SENTINELS), key=lambda t: (t != "False", t))
        if node.get("is_false") is True and "False" not in hits:
            hits.insert(0, "False")
        if not hits:
            continue
        status = graph.status(key)
        if status == "supplied" or (status == "refuted" and hits != ["False"]):
            alarm = {"key": key, "type": hits[0], "status": status, "reason": SENTINELS[hits[0]],
                     "overridable": hits[0] != "False"}
            if status == "supplied":
                alarm["witness"] = graph.proof_tree(key, limit=3)
            else:
                alarm["refutation"] = graph.refuted.get(key)
            alarms.append(alarm)
    return alarms


TEX_MACROS_BEGIN = "% BEGIN generated_argument_graph_macros"
TEX_MACROS_END = "% END generated_argument_graph_macros"


def census_refusal(projection: dict[str, Any], *, allow_open_target_alarms: bool = False) -> str | None:
    """Why this projection may not fill a paper's corpus-wide totals, or None.
    A contradiction alarm always refuses; an open-target alarm refuses unless
    the caller acknowledges it; an export restricted by declaration-name
    prefix, by other roots or to focused declarations is not the corpus. A
    truncated export is allowed: the paper states every total as a lower
    bound, and ``export_truncated`` stays in the summary."""
    alarms = projection.get("sentinel_alarms") or []
    hard = [a for a in alarms if a.get("overridable") is not True]
    if hard:
        return f"{len(hard)} contradiction alarm(s): read sentinel_alarms; no override exists"
    if alarms and not allow_open_target_alarms:
        return f"{len(alarms)} open-target alarm(s): read sentinel_alarms (--allow-sentinel-alarms acknowledges them)"
    source = projection.get("source") or {}
    config = source.get("export_config") or {}
    if config.get("name_prefixes"):
        return f"the export selected declarations by name prefix {config['name_prefixes']}: not the corpus"
    roots = config.get("roots")
    if roots is not None and set(roots) != DEFAULT_ROOTS:
        return f"the export read roots {roots}, not {sorted(DEFAULT_ROOTS)}: not the corpus"
    if config.get("focus_declarations"):
        return "the export focused on selected declarations: not the corpus"
    if (source.get("export_summary") or {}).get("global_corpus_census") is False:
        return "the export assembled selected tasks only: not the corpus"
    return None


def paper_macro_region(projection: dict[str, Any], *, allow_open_target_alarms: bool = False) -> str:
    """LaTeX macros carrying the graph's measured totals into a paper, so no
    number in the prose is typed by hand. Refuses (``ValueError``) whatever
    ``census_refusal`` refuses, so no caller can bypass the alarm."""
    refusal = census_refusal(projection, allow_open_target_alarms=allow_open_target_alarms)
    if refusal:
        raise ValueError(f"no paper macros: {refusal}")
    lines = [TEX_MACROS_BEGIN]
    for name, value in macro_values(projection).items():
        rendered = f"{value:,}" if isinstance(value, int) else str(value)
        lines.append(rf"\newcommand{{\{name}}}{{{rendered}}}")
    lines.append(TEX_MACROS_END)
    return "\n".join(lines)


def macro_values(projection: dict[str, Any]) -> dict[str, Any]:
    """The totals the paper macros carry, by macro name."""
    summary = projection["summary"]
    export = projection["source"].get("export_summary", {})
    return {
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
        "AGWeakened": summary["weakened_theorems"],
        "AGWeakenedOpen": summary["weakenings_of_open_hypotheses"],
        "AGWeakeningGain": summary["statements_supplied_only_by_weakening"],
    }


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
    parser.add_argument("--export", type=Path, required=True, action="append",
                        help="export stream (.jsonl or .jsonl.gz) from export_argument_continuations.lean; "
                             "repeat it to combine exports of the same Lean tree, the latest last")
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
    parser.add_argument("--allow-sentinel-alarms", action="store_true",
                        help="acknowledge settled open targets (a solution, after a person checked it): write "
                             "paper macros and exit 0; a contradiction (False supplied, or a statement supplied "
                             "and refuted) is never acknowledged")
    args = parser.parse_args(argv)
    projection, graph_payload = build(args.export, args.root, lean_tree=args.lean_tree,
                                      source_revision=args.source_revision)
    write_outputs(projection, graph_payload, args.output, args.graph_output)
    alarms = projection["sentinel_alarms"]
    hard = [a for a in alarms if a.get("overridable") is not True]
    if alarms and (hard or not args.allow_sentinel_alarms):
        # The outputs are written for inspection; no number reaches a paper.
        print(json.dumps({"sentinel_alarms": alarms}, indent=1, ensure_ascii=False)[:20000], file=sys.stderr)
        print(f"ALARM: {len(alarms)} sentinel statement(s) settled, {len(hard)} of them contradictions; inspect "
              "the witness chains before using this graph (see sentinel_alarms in the projection)", file=sys.stderr)
        return 3
    for paper in args.paper:
        refusal = census_refusal(projection, allow_open_target_alarms=args.allow_sentinel_alarms)
        if refusal:
            print(f"no paper macros written: {refusal}", file=sys.stderr)
            return 2
        text = paper.read_text(encoding="utf-8")
        paper.write_text(replace_macro_region(text, paper_macro_region(
            projection, allow_open_target_alarms=args.allow_sentinel_alarms)), encoding="utf-8")
    summary = projection["summary"]
    print(json.dumps({"output": str(args.output), "graph_output": str(args.graph_output), **summary}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
