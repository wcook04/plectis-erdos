#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the semantic corpus: the statement-and-relation graph over both libraries.

The repository already had the two ends of a three-layer stack and nothing in
the middle.  ``docs/declaration_atlas.json`` is the exhaustive phone book: every
declaration, its kind, its coordinates, its signature.  ``docs/claims.json`` is
the small curated publication ledger: 100 reviewed claims linking 300
declarations.  Between them sat no owner for a more limited question: *what
does the selected interpreted subset state, and how are those statements
related?*  That question could only be answered by rereading hundreds of
modules, and was in practice answered selectively and wrongly.

This layer owns it.  A **statement node** is one mathematically distinct
statement, carrying the declarations that establish it, its logical class, its
problem membership, the open antecedents it still depends on, and its prior-art
state.  A **relation** is a typed mathematical edge between statement nodes.

Two relation classes are deliberately kept apart.  Lean proof dependency -- *A
was used in the proof of B* -- is structural and lives in the module and
argument graphs.  Mathematical relation -- *B specialises, reformulates or is a
finite instance of A* -- is semantic, cannot be inferred from premise
extraction, and lives here with a required evidence basis.

Equivalences and transports are **preserved, never deduplicated away**.  They
are the associative structure the corpus exists to expose.  Collapsing happens
in the ``views`` projections, not in the graph.

Authored inputs live in ``docs/semantic/``:

    zones/<zone>.json      per-zone statement nodes, declaration roles, edges
    relations_<lens>.json  cross-zone typed edges
    frontier.json          open antecedents, engine hierarchies, candidates

Generated inputs are ``docs/declaration_atlas.json`` and
``docs/generated_certificate_manifest.json``.

Run from the repository root:

    python3 scripts/build_semantic_corpus.py
    python3 scripts/build_semantic_corpus.py --check
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

from semantic_review import apply_review_registry

ROOT = Path(__file__).resolve().parent.parent
ATLAS = ROOT / "docs" / "declaration_atlas.json"
MANIFEST = ROOT / "docs" / "generated_certificate_manifest.json"
CLAIMS = ROOT / "docs" / "claims.json"
SEMANTIC_DIR = ROOT / "docs" / "semantic"
ZONES_DIR = SEMANTIC_DIR / "zones"
REVIEWS = SEMANTIC_DIR / "reviews.json"
OUTPUT = ROOT / "docs" / "semantic_corpus.json"

LOGICAL_CLASSES = (
    "unconditional_object_theorem",
    "barrier_no_go",
    "conditional_implication",
    "equivalence_or_classification",
    "reduction_or_transport",
    "finite_instance",
    "generated_certificate_instance",
    "classical_formalised",
    "representation_normalisation",
    "infrastructure",
)

PRIOR_ART_STATES = (
    "not_assessed",
    "known_classical",
    "formalisation_only",
    "routine_corollary_or_specialisation",
    "candidate_new_statement",
    "external_review_pending",
    "externally_supported_as_new",
    "prior_art_found",
)

RELATIONS = (
    "definitionally_same_as",
    "alias_of",
    "equivalent_to",
    "implies",
    "specialises",
    "generalises",
    "finite_instance_of",
    "transport_of",
    "reformulates",
    "depends_on_open",
    "barrier_for",
    "repair_of",
    "generated_by",
    "supersedes",
    "complements",
)

DECLARATION_ROLES = (
    "statement",
    "substrate",
    "representation",
    "engine",
    "concept",
    "finite_instance",
    "generated_instance",
)

PROBLEMS = ("249", "257", "both", "shared_substrate")

# A view is a projection over one graph, never a separate source of truth.
VIEW_RULES = {
    "publication": "Quotient aliases and definitional duplicates; collapse generated families to one node each; keep unconditional object theorems, scoped barriers and classical formalisations.",
    "research": "Every node and every edge, including equivalences and transports, which are the associative structure interpolation needs.",
    "audit": "Every declaration with its evidence receipt and owning node.",
    "frontier": "Open antecedents, bare equivalences, unblocked sibling engines and nonrecurring candidates.",
}

# Nodes excluded from the nonrecurring projection, by class.
RECURRING_CLASSES = frozenset(
    {
        "conditional_implication",
        "equivalence_or_classification",
        "finite_instance",
        "generated_certificate_instance",
        "representation_normalisation",
        "infrastructure",
    }
)


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def zone_files() -> list[Path]:
    if not ZONES_DIR.is_dir():
        return []
    return sorted(ZONES_DIR.glob("*.json"))


def relation_files() -> list[Path]:
    if not SEMANTIC_DIR.is_dir():
        return []
    return sorted(SEMANTIC_DIR.glob("relations_*.json"))


def semantic_input_paths() -> list[Path]:
    """Return every source whose bytes determine the generated corpus."""
    fixed = [ATLAS, MANIFEST, CLAIMS, SEMANTIC_DIR / "frontier.json", REVIEWS]
    return sorted(
        (path for path in [*fixed, *zone_files(), *relation_files()] if path.is_file()),
        key=lambda path: path.relative_to(ROOT).as_posix(),
    )


def semantic_input_fingerprint() -> str:
    """Bind queries to the exact atlas and authored semantic inputs."""
    digest = hashlib.sha256()
    for path in semantic_input_paths():
        digest.update(path.relative_to(ROOT).as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return f"sha256:{digest.hexdigest()}"


def declaration_key(module: str, name: str, line: object) -> str:
    return f"{module}:{line}:{name}"


def collect() -> dict:
    atlas = load(ATLAS)
    manifest = load(MANIFEST)
    claims = load(CLAIMS)

    # ---- evidence layer -------------------------------------------------
    atlas_rows = {row["id"]: row for row in atlas["declarations"]}
    by_module_name: dict[tuple[str, str], list[dict]] = defaultdict(list)
    by_bare_name: dict[str, list[dict]] = defaultdict(list)
    for row in atlas["declarations"]:
        by_module_name[(row["module"], row["name"])].append(row)
        by_bare_name[row["name"]].append(row)

    generated_family_of = {
        path: family["id"]
        for family in manifest["families"]
        for path in family["module_paths"]
    }

    def find_declaration(module: str, name: str) -> dict | None:
        """Resolve a cited declaration against the atlas.

        The atlas records a declaration under the name as written, beneath
        whatever namespace the module opens.  A classifier reading the source
        may record either that name or its fully qualified form, so
        ``ErdosProblems.Erdos243.sylvesterNext`` and ``sylvesterNext`` must
        resolve to the same row.  Nothing else is guessed: the module must
        match exactly.
        """
        if not module or not name:
            return None
        rows = by_module_name.get((module, name))
        if rows:
            return rows[0]
        if "." in name:
            rows = by_module_name.get((module, name.rsplit(".", 1)[-1]))
            if rows:
                return rows[0]
        # Deliberately no repository-wide fallback on the bare name.  An
        # earlier version resolved a name that occurred once anywhere, on the
        # theory that a classifier had named the wrong module.  The one case it
        # was built for turned out to be an atlas extraction bug, and the
        # "correction" would have pointed the citation at a call site rather
        # than the declaration.  A citation that does not resolve in the module
        # it names stays unresolved, and the contract reports it.
        return None

    # ---- authored semantic layer ---------------------------------------
    concepts: dict[str, dict] = {}
    nodes: dict[str, dict] = {}
    edges: list[dict] = []
    roles: dict[str, dict] = {}
    duplicate_role_assignments: list[dict] = []
    zone_index: list[dict] = []
    # Zone classification is independent per zone, so a node id is unique only
    # within its zone: `lcm_cone_flatness_law` and `lcm_ray_window_structure`
    # each occur in two zones.  Keying the graph on the bare id would silently
    # drop a node and rewire its edges to the survivor, so ids are qualified as
    # `<zone>::<id>` and every reference is resolved through these indexes.
    by_zone_local: dict[tuple[str, str], str] = {}
    by_local: dict[str, list[str]] = defaultdict(list)
    unresolved_edges: list[dict] = []

    for path in zone_files():
        zone = load(path)
        zid = zone.get("zone_id") or path.stem
        zone_index.append(
            {
                "zone_id": zid,
                "title": zone.get("title", ""),
                "problem": zone.get("problem", "shared_substrate"),
                "source": path.relative_to(ROOT).as_posix(),
                "statement_nodes": len(zone.get("statement_nodes", [])),
                "declaration_roles": len(zone.get("declaration_roles", [])),
            }
        )
        for concept in zone.get("concepts", []):
            concepts.setdefault(concept["id"], {**concept, "zones": []})["zones"].append(zid)
        for node in zone.get("statement_nodes", []):
            node = {**node, "zone": zid}
            node.setdefault("open_antecedents", [])
            node.setdefault("concepts", [])
            node.setdefault("prior_art_state", "not_assessed")
            node.setdefault("confidence", "low")
            # Resolve every evidence declaration against the atlas, so a node
            # can never cite a declaration that is not in the source.
            resolved = []
            for ev in node.get("evidence", []):
                row = find_declaration(ev.get("module", ""), ev.get("declaration", ""))
                if row is not None:
                    resolved.append(
                        {
                            "declaration": row["name"],
                            "module": row["module"],
                            "line": row["line"],
                            "id": row["id"],
                            "kind": row["kind"],
                            "resolved": True,
                        }
                    )
                else:
                    resolved.append({**ev, "resolved": False})
            node["evidence"] = resolved
            local = node["id"]
            qualified = f"{zid}::{local}"
            node["local_id"] = local
            node["id"] = qualified
            nodes[qualified] = node
            by_zone_local[(zid, local)] = qualified
            by_local[local].append(qualified)
        for edge in zone.get("intra_zone_relations", []):
            src = by_zone_local.get((zid, edge.get("from")))
            dst = by_zone_local.get((zid, edge.get("to")))
            if src is None or dst is None:
                unresolved_edges.append({**edge, "zone": zid, "reason": "endpoint absent from its own zone"})
                continue
            edges.append({**edge, "from": src, "to": dst, "scope": "intra_zone", "zone": zid})
        for role in zone.get("declaration_roles", []):
            key = declaration_key(role.get("module", ""), role.get("declaration", ""), role.get("line"))
            row = find_declaration(role.get("module", ""), role.get("declaration", ""))
            if row is not None:
                key = row["id"]
            target = role.get("statement_node")
            assignment = {
                "declaration": role.get("declaration"),
                "module": role.get("module"),
                "role": role.get("role"),
                "statement_node": by_zone_local.get((zid, target)) if target else None,
                "zone": zid,
            }
            if key in roles and row is not None:
                duplicate_role_assignments.append(
                    {
                        "id": key,
                        "first": roles[key],
                        "second": assignment,
                    }
                )
            roles[key] = assignment

    def resolve(local: object, zone: object) -> str | None:
        """Resolve a relation endpoint to a qualified node id.

        A lens that recorded the owning zone resolves exactly.  One lens
        emitted bare ids only; those resolve when the id is globally unique and
        are reported as ambiguous otherwise rather than being guessed.
        """
        if not isinstance(local, str):
            return None
        if isinstance(zone, str) and (zone, local) in by_zone_local:
            return by_zone_local[(zone, local)]
        candidates = by_local.get(local, [])
        return candidates[0] if len(candidates) == 1 else None

    for path in relation_files():
        payload = load(path)
        lens = payload.get("lens", path.stem)
        for edge in payload.get("edges", []):
            src = resolve(edge.get("from"), edge.get("from_zone"))
            dst = resolve(edge.get("to"), edge.get("to_zone"))
            if src is None or dst is None:
                unresolved_edges.append(
                    {
                        **edge,
                        "lens": lens,
                        "reason": "endpoint id is absent, or ambiguous across zones and the lens recorded no zone",
                    }
                )
                continue
            edges.append({**edge, "from": src, "to": dst, "scope": "cross_zone", "lens": lens})

    # A module named in the provenance contract cannot own an authored
    # statement node.  Zone classification works from module docstrings, and
    # several emitted window modules read as authored mathematics; the manifest
    # is authority, so any node whose evidence lies wholly inside generated
    # modules is absorbed into its family node rather than standing alone.
    absorbed: list[dict] = []
    for nid in list(nodes):
        evidence = nodes[nid].get("evidence", [])
        if not evidence:
            continue
        families = {generated_family_of.get(e.get("module", "")) for e in evidence}
        if families and None not in families:
            absorbed.append(
                {
                    "node": nid,
                    "absorbed_into": f"generated::{sorted(f for f in families if f)[0]}",
                    "reason": "every evidence declaration lies in a module named by the generated-certificate manifest",
                }
            )
            del nodes[nid]
    absorbed_ids = {row["node"] for row in absorbed}
    edges = [e for e in edges if e.get("from") not in absorbed_ids and e.get("to") not in absorbed_ids]

    # ---- generated families become nodes, not 8,171 orphans -------------
    generated_nodes = []
    for family in manifest["families"]:
        generated_nodes.append(
            {
                "id": f"generated::{family['id']}",
                "canonical_statement": family["template_statement"],
                "logical_class": "generated_certificate_instance",
                "problem": "shared_substrate",
                "evidence": [],
                "concepts": [],
                "open_antecedents": [],
                "is_restatement_of_open_problem": False,
                "engine": family.get("generator"),
                "prior_art_state": "formalisation_only",
                "scope_caveat": "A verified instance at bounded parameters. It is not the infinite family and carries no unbounded supply.",
                "confidence": "high",
                "generated_family": family["id"],
                "module_count": family["module_count"],
                "declaration_count": family["declaration_count"],
                "parameters": family.get("parameters", []),
                "consumed_by": family.get("consumed_by", []),
                "zone": "generated",
            }
        )
        nodes[f"generated::{family['id']}"] = generated_nodes[-1]

    # Every generated declaration is owned by its family node.
    for row in atlas["declarations"]:
        family = generated_family_of.get(row["module"])
        if family is None:
            continue
        roles[row["id"]] = {
            "declaration": row["name"],
            "module": row["module"],
            "role": "generated_instance",
            "statement_node": f"generated::{family}",
            "zone": "generated",
        }
        edges.append(
            {
                "from": f"generated::{family}",
                "to": f"generated::{family}",
                "relation": "generated_by",
                "basis": f"declaration {row['name']} is an instance of the {family} schema",
                "scope": "generated",
                "suppressed_in_views": True,
            }
        )

    # Authored zone files carry the reviewed statement-level interpretation,
    # but inventory routing must not go stale whenever a Lean module grows.
    # Route every otherwise-unclassified live declaration through a deliberately
    # non-semantic inventory lane.  This is module-agnostic and preserves the
    # important ceiling: the declaration is discoverable, but no canonical
    # mathematical statement is inferred from its name or source text.
    automatic_inventory_roles = []
    for row in atlas["declarations"]:
        if row["id"] in roles:
            continue
        assignment = {
            "declaration": row["name"],
            "module": row["module"],
            "role": "substrate",
            "statement_node": None,
            "zone": "inventory",
            "routing_origin": "automatic_inventory_fallback",
            "routing_basis": (
                "Live declaration from the exhaustive atlas with no authored "
                "zone receipt; routed for discovery without semantic interpretation."
            ),
        }
        roles[row["id"]] = assignment
        automatic_inventory_roles.append(row["id"])
    if automatic_inventory_roles:
        zone_index.append(
            {
                "zone_id": "inventory",
                "title": "Unclassified live declaration inventory",
                "problem": "shared_substrate",
                "source": "generated from docs/declaration_atlas.json",
                "statement_nodes": 0,
                "declaration_roles": len(automatic_inventory_roles),
            }
        )

    # ---- coverage receipts ----------------------------------------------
    owned = set(roles)
    all_ids = set(atlas_rows)
    orphans = sorted(all_ids - owned)
    phantom = sorted(owned - all_ids)
    live_roles = {key: role for key, role in roles.items() if key in all_ids}
    node_linked_ids = {
        key for key, role in live_roles.items() if role.get("statement_node")
    }
    authored_ids = {
        row["id"]
        for row in atlas["declarations"]
        if not row["generated_certificate"]
    }
    authored_theorem_like_ids = {
        row["id"]
        for row in atlas["declarations"]
        if not row["generated_certificate"] and row["kind"] in ("theorem", "lemma")
    }
    authored_node_linked_theorem_like_ids = authored_theorem_like_ids & node_linked_ids
    authored_zone_only_theorem_like_ids = authored_theorem_like_ids - node_linked_ids

    claim_decls = {
        (d["module"], d["name"])
        for claim in claims.get("claims", [])
        for d in claim.get("declarations", [])
    }
    claim_without_node = []
    for module, name in sorted(claim_decls):
        row = find_declaration(module, name)
        if row is None:
            claim_without_node.append(f"{module}::{name} (absent from the atlas)")
            continue
        role = roles.get(row["id"])
        if role is None:
            claim_without_node.append(f"{module}::{name} (no semantic role)")
            continue
        # A curated claim may cite a definition rather than a theorem -- the
        # predicate a conditional result quantifies over, for instance.  A
        # definition carries a role and belongs to a concept; requiring it to
        # own a statement node would force a fictitious one.
        if row["kind"] in ("theorem", "lemma") and not role.get("statement_node"):
            claim_without_node.append(f"{module}::{name}")

    # Authorship and confidence are not semantic review. Attach only receipts
    # from the dedicated registry, and fail if a receipt has drifted from its
    # wording, evidence, atlas fingerprint, or formal-source revision.
    review_registry = load(REVIEWS)
    formal_revision = str(
        claims.get("release", {}).get("formal_source", {}).get("ref", "")
    )
    review_errors = apply_review_registry(
        review_registry,
        nodes,
        edges,
        evidence_fingerprint=str(atlas.get("source_fingerprint", "")),
        reviewed_revision=formal_revision,
    )
    if review_errors:
        raise ValueError(
            "semantic review registry is invalid:\n  "
            + "\n  ".join(review_errors)
        )

    headline_claim_node_ids: dict[str, set[str]] = {}
    for claim in claims.get("claims", []):
        if not claim.get("readme_headline"):
            continue
        linked_nodes: set[str] = set()
        for declaration in claim.get("declarations", []):
            row = find_declaration(
                declaration.get("module", ""),
                declaration.get("name", ""),
            )
            if row is None:
                continue
            node_id = (roles.get(row["id"]) or {}).get("statement_node")
            if node_id:
                linked_nodes.add(str(node_id))
        headline_claim_node_ids[str(claim["id"])] = linked_nodes
    headline_claims_with_reviewed_node = sorted(
        claim_id
        for claim_id, node_ids in headline_claim_node_ids.items()
        if any(nodes.get(node_id, {}).get("semantic_review") for node_id in node_ids)
    )
    headline_claims_without_reviewed_node = sorted(
        set(headline_claim_node_ids) - set(headline_claims_with_reviewed_node)
    )

    # ---- summary ---------------------------------------------------------
    authored_rows = [r for r in atlas["declarations"] if not r["generated_certificate"]]
    by_class = Counter(n.get("logical_class", "unclassified") for n in nodes.values())
    by_problem = Counter(n.get("problem", "unassigned") for n in nodes.values())
    by_prior_art = Counter(n.get("prior_art_state", "not_assessed") for n in nodes.values())
    by_relation = Counter(e.get("relation", "unknown") for e in edges if not e.get("suppressed_in_views"))

    per_problem: dict[str, dict] = {}
    for problem in PROBLEMS:
        subset = [n for n in nodes.values() if n.get("problem") == problem]
        per_problem[problem] = {
            "statement_nodes": len(subset),
            "by_logical_class": dict(Counter(n.get("logical_class", "unclassified") for n in subset)),
            "by_prior_art_state": dict(Counter(n.get("prior_art_state", "not_assessed") for n in subset)),
            "restatements_of_open_problem": sum(
                1 for n in subset if n.get("is_restatement_of_open_problem")
            ),
            "with_open_antecedents": sum(1 for n in subset if n.get("open_antecedents")),
        }

    # ---- views ------------------------------------------------------------
    frontier_path = SEMANTIC_DIR / "frontier.json"
    frontier = load(frontier_path) if frontier_path.is_file() else {}
    # Consumer coordinates are generated navigation data. Resolve them from
    # the live atlas so a harmless line shift cannot invalidate an otherwise
    # current expert handoff.
    for question in frontier.get("expert_questions", []):
        for consumer in question.get("consumer_declarations", []):
            row = find_declaration(
                consumer.get("module", ""),
                consumer.get("declaration", ""),
            )
            if row is not None:
                consumer["module"] = row["module"]
                consumer["declaration"] = row["name"]
                consumer["line"] = row["line"]

    def node_ids(predicate) -> list[str]:
        return sorted(nid for nid, n in nodes.items() if predicate(n))

    # This is a mechanically filtered candidate pool, not an adjudicated
    # result set.  It ranges only over the selected statement graph, and most
    # of its nodes have not completed prior-art review.
    # collapse aliases and definitional duplicates, then keep object theorems
    # and properly scoped barriers, and drop anything already judged a routine
    # corollary or classical.  A node that *specialises* another survives --
    # a meaningful special case is a result -- but a node that is merely
    # another name for one does not.
    subsumed = {
        e["from"]
        for e in edges
        if e.get("relation") in ("alias_of", "definitionally_same_as")
        and not e.get("suppressed_in_views")
    }
    nonrecurring = node_ids(
        lambda n: n.get("logical_class") not in RECURRING_CLASSES
        and n.get("logical_class") != "classical_formalised"
        and not n.get("open_antecedents")
        and not n.get("is_restatement_of_open_problem")
        and n["id"] not in subsumed
        and n.get("prior_art_state")
        not in ("known_classical", "prior_art_found", "routine_corollary_or_specialisation")
    )
    views = {
        "publication": {
            "rule": VIEW_RULES["publication"],
            "nodes": node_ids(
                lambda n: n.get("logical_class")
                in {
                    "unconditional_object_theorem",
                    "barrier_no_go",
                    "classical_formalised",
                    "reduction_or_transport",
                }
            ),
            "generated_families_collapsed_to": [n["id"] for n in generated_nodes],
        },
        "research": {
            "rule": VIEW_RULES["research"],
            "node_count": len(nodes),
            "edge_count": sum(1 for e in edges if not e.get("suppressed_in_views")),
        },
        "audit": {
            "rule": (
                "Every declaration has one typed routing receipt. A declaration is "
                "statement-level interpreted only when its receipt names a statement node."
            ),
            "declarations": len(all_ids),
            "owned": len(live_roles),
            "role_references": len(owned),
            "orphans": orphans[:50],
            "orphan_count": len(orphans),
            "duplicate_role_assignment_count": len(duplicate_role_assignments),
            "node_linked_declarations": len(node_linked_ids),
            "authored_theorem_like": len(authored_theorem_like_ids),
            "authored_theorem_like_node_linked": len(
                authored_node_linked_theorem_like_ids
            ),
            "authored_theorem_like_zone_only": len(
                authored_zone_only_theorem_like_ids
            ),
        },
        "frontier": {
            "rule": VIEW_RULES["frontier"],
            "open_antecedent_nodes": node_ids(lambda n: bool(n.get("open_antecedents"))),
            "bare_equivalences": node_ids(
                lambda n: n.get("logical_class") == "equivalence_or_classification"
                and n.get("is_restatement_of_open_problem")
            ),
            "barriers": node_ids(lambda n: n.get("logical_class") == "barrier_no_go"),
        },
        "nonrecurring": {
            "rule": "Within the selected statement graph, quotient aliases and definitional duplicates, then mechanically retain unconditional object theorems, reductions or transports, and properly scoped barriers; drop open-antecedent implications, bare equivalences, generated and finite instances, infrastructure, and anything already judged classical or routine.",
            "nodes": nonrecurring,
            "count": len(nonrecurring),
            "subsumed_by_alias": len(subsumed),
            "reviewed_shortlist": frontier.get("nonrecurring_candidates", []),
            "reviewed_exclusions": frontier.get("excluded_from_nonrecurring_with_reason", []),
            "note": "The mechanical quotient is the candidate pool; reviewed_shortlist is the adjudicated result, and is deliberately much shorter.",
        },
    }

    # One Lean proposition may be presented through several authored nodes only
    # when the graph says why.  Otherwise a single checked declaration can be
    # counted twice as two supposedly distinct mathematical results.  Exact
    # aliases and definitional duplicates are the normal case; genuinely
    # distinct claims extracted from one stronger theorem require a narrow,
    # authored exception in frontier.json with the declaration id, node ids,
    # and a basis.
    evidence_to_nodes: dict[str, set[str]] = defaultdict(set)
    for node in nodes.values():
        for evidence in node.get("evidence", []):
            if evidence.get("resolved") and evidence.get("id"):
                evidence_to_nodes[evidence["id"]].add(node["id"])
    authored_theorem_like_direct_evidence_ids = (
        authored_theorem_like_ids & set(evidence_to_nodes)
    )
    authored_theorem_like_contextual_ids = (
        authored_node_linked_theorem_like_ids
        - authored_theorem_like_direct_evidence_ids
    )
    equivalent_pairs = {
        frozenset((edge["from"], edge["to"]))
        for edge in edges
        if edge.get("relation") in ("alias_of", "definitionally_same_as")
        and not edge.get("suppressed_in_views")
    }
    evidence_sharing_exceptions = frontier.get("evidence_sharing_exceptions", [])
    exception_keys = {
        (
            row.get("declaration_id"),
            frozenset(row.get("statement_nodes", [])),
        )
        for row in evidence_sharing_exceptions
        if row.get("declaration_id")
        and len(row.get("statement_nodes", [])) == 2
        and row.get("basis")
    }
    multi_node_evidence_without_equivalence = []
    for declaration_id, node_ids_for_evidence in sorted(evidence_to_nodes.items()):
        ordered = sorted(node_ids_for_evidence)
        for left_index, left in enumerate(ordered):
            for right in ordered[left_index + 1 :]:
                pair = frozenset((left, right))
                if pair in equivalent_pairs:
                    continue
                if (declaration_id, pair) in exception_keys:
                    continue
                multi_node_evidence_without_equivalence.append(
                    {
                        "declaration_id": declaration_id,
                        "statement_nodes": sorted(pair),
                    }
                )

    payload = {
        "schema": "erdos249257-semantic-corpus/1",
        "artifact_role": (
            "generated_exhaustive_declaration_routing_projection_with_selective_"
            "statement_level_semantic_graph"
        ),
        "authority_posture": (
            "generated_semantic_projection_over_the_declaration_atlas_and_authored_zone_classifications; "
            "not Lean proof authority, and not the curated claim registry"
        ),
        "purpose": (
            "Own the layer between the exhaustive declaration atlas and the curated claims ledger: "
            "authored nodes for selected mathematically distinct statements, typed mathematical "
            "relations between them, and an exhaustive role-and-zone route for every declaration "
            "in both libraries. Exhaustive routing is not exhaustive interpretation."
        ),
        "coverage_contract": {
            "posture": (
                "exhaustive_inventory_and_typed_routing_selective_statement_"
                "interpretation"
            ),
            "inventory": (
                "The declaration atlas supplies the live declaration population."
            ),
            "routing": (
                "Every live declaration has exactly one role-and-zone receipt, or one "
                "manifest-owned generated-family receipt. Declarations not yet covered "
                "by an authored semantic zone receive an automatic inventory-only route."
            ),
            "statement_interpretation": (
                "Only a declaration whose receipt names a statement_node is claimed to "
                "participate in a canonical mathematical statement."
            ),
            "anti_filler": (
                "Exact theorem-like declarations cited directly by statement-node "
                "evidence are counted separately from contextual node links. Adding "
                "helpers to an existing node may improve navigation but cannot increase "
                "the direct-evidence measure or manufacture a new proposition."
            ),
            "relation_interpretation": (
                "Typed relations are authored and carry a stated evidence basis; the "
                "checker verifies presence and referential integrity, not mathematical truth."
            ),
            "accuracy_boundary": (
                "No count, zero-orphan receipt, or passing checker establishes that the "
                "authored canonical statements and relations are mathematically complete "
                "or correct. That remains a review and evaluation question."
            ),
            "reviewed_semantic_fidelity": (
                "Digest-bound node and relation review receipts are authored in "
                "docs/semantic/reviews.json and attached only when their subject wording, "
                "evidence coordinates, formal-source revision, and atlas fingerprint "
                "still match. Coverage is deliberately partial. Confidence labels, "
                "prior-art states, and relation bases are not review receipts."
            ),
        },
        "layering": {
            "evidence_below": "docs/declaration_atlas.json",
            "provenance": "docs/generated_certificate_manifest.json",
            "curated_above": "docs/claims.json",
            "rule": "claims.json stays small and reviewed; it selects from this graph and never replaces it.",
        },
        "source_provenance": {
            "formal_source": {
                "ref": claims["release"]["formal_source"]["ref"],
                "ref_kind": claims["release"]["formal_source"]["ref_kind"],
                "publication_state": claims["release"]["formal_source"][
                    "publication_state"
                ],
                "authority_role": "proof_bearing_committed_source_anchor",
            },
            "projection_identity": (
                "Content-addressed by evidence_fingerprint and "
                "semantic_input_fingerprint; intentionally independent of the "
                "checkout HEAD so rebuilding is safe in a shared worktree."
            ),
        },
        "evidence_fingerprint": atlas.get("source_fingerprint"),
        "semantic_input_fingerprint": semantic_input_fingerprint(),
        "vocabularies": {
            "logical_classes": list(LOGICAL_CLASSES),
            "prior_art_states": list(PRIOR_ART_STATES),
            "relations": list(RELATIONS),
            "declaration_roles": list(DECLARATION_ROLES),
            "problems": list(PROBLEMS),
        },
        "summary": {
            "declarations": len(all_ids),
            "authored_declarations": len(authored_rows),
            "generated_declarations": len(all_ids) - len(authored_rows),
            "authored_theorem_like": sum(
                1 for r in authored_rows if r["kind"] in ("theorem", "lemma")
            ),
            "statement_nodes": len(nodes),
            "authored_statement_nodes": sum(
                1
                for node in nodes.values()
                if node.get("logical_class") != "generated_certificate_instance"
            ),
            "concepts": len(concepts),
            "relations": sum(1 for e in edges if not e.get("suppressed_in_views")),
            "zones": len(zone_index),
            "coverage": {
                "declarations_owned": len(live_roles),
                "automatic_inventory_fallback_count": len(
                    automatic_inventory_roles
                ),
                "role_references": len(owned),
                "orphan_count": len(orphans),
                "phantom_count": len(phantom),
                "duplicate_role_assignment_count": len(
                    duplicate_role_assignments
                ),
                "node_linked_declarations": len(node_linked_ids),
                "node_linked_fraction": round(
                    len(node_linked_ids) / max(1, len(all_ids)), 4
                ),
                "authored_theorem_like_node_linked": len(
                    authored_node_linked_theorem_like_ids
                ),
                "authored_theorem_like_zone_only": len(
                    authored_zone_only_theorem_like_ids
                ),
                "authored_theorem_like_node_linked_fraction": round(
                    len(authored_node_linked_theorem_like_ids)
                    / max(1, len(authored_theorem_like_ids)),
                    4,
                ),
                "authored_theorem_like_direct_evidence": len(
                    authored_theorem_like_direct_evidence_ids
                ),
                "authored_theorem_like_direct_evidence_fraction": round(
                    len(authored_theorem_like_direct_evidence_ids)
                    / max(1, len(authored_theorem_like_ids)),
                    4,
                ),
                "authored_theorem_like_contextual_node_links": len(
                    authored_theorem_like_contextual_ids
                ),
                "curated_claim_declarations": len(claim_decls),
                "curated_claim_declarations_without_node": len(claim_without_node),
                "statement_nodes_with_semantic_review_receipt": sum(
                    1 for node in nodes.values() if node.get("semantic_review")
                ),
                "relations_with_semantic_review_receipt": sum(
                    1
                    for edge in edges
                    if not edge.get("suppressed_in_views")
                    and edge.get("semantic_review")
                ),
                "readme_headline_claims": len(headline_claim_node_ids),
                "readme_headline_claims_with_reviewed_node": len(
                    headline_claims_with_reviewed_node
                ),
                "readme_headline_claims_without_reviewed_node": len(
                    headline_claims_without_reviewed_node
                ),
                "curated_fraction_of_authored_theorem_like": round(
                    len(claim_decls)
                    / max(1, sum(1 for r in authored_rows if r["kind"] in ("theorem", "lemma"))),
                    4,
                ),
            },
            "by_logical_class": dict(by_class),
            "by_problem": dict(by_problem),
            "by_prior_art_state": dict(by_prior_art),
            "by_relation": dict(by_relation),
            "per_problem": per_problem,
        },
        "zones": zone_index,
        "concepts": sorted(concepts.values(), key=lambda c: c["id"]),
        "statement_nodes": [nodes[k] for k in sorted(nodes)],
        "relations": edges,
        "generated_families": manifest["families"],
        "declaration_roles": [
            {"id": k, **roles[k]} for k in sorted(roles) if k in all_ids
        ],
        "frontier": frontier,
        "views": views,
        "integrity": {
            "orphans": orphans,
            "automatic_inventory_fallback_declarations": (
                automatic_inventory_roles
            ),
            "phantom_declaration_references": phantom,
            "duplicate_role_assignments": duplicate_role_assignments,
            "curated_claim_declarations_without_node": claim_without_node,
            "readme_headline_claims_with_reviewed_node": (
                headline_claims_with_reviewed_node
            ),
            "readme_headline_claims_without_reviewed_node": (
                headline_claims_without_reviewed_node
            ),
            "nodes_absorbed_into_generated_families": absorbed,
            "unresolved_relation_endpoints": unresolved_edges,
            "multi_node_evidence_without_equivalence": (
                multi_node_evidence_without_equivalence
            ),
            "evidence_sharing_exceptions": evidence_sharing_exceptions,
            "node_ids_colliding_across_zones": sorted(
                local for local, qualified in by_local.items() if len(qualified) > 1
            ),
        },
    }
    return payload


def render(payload: dict) -> str:
    return json.dumps(payload, indent=1, ensure_ascii=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the tracked corpus is stale")
    args = parser.parse_args()

    if not zone_files():
        print(
            "no zone classifications under docs/semantic/zones/; "
            "the semantic corpus cannot be built from the evidence layer alone"
        )
        return 1

    payload = collect()
    text = render(payload)

    if args.check:
        if not OUTPUT.is_file():
            print("semantic corpus missing; run python3 scripts/build_semantic_corpus.py")
            return 1
        if OUTPUT.read_text(encoding="utf-8") != text:
            print("semantic corpus is stale; run python3 scripts/build_semantic_corpus.py")
            return 1
        summary = payload["summary"]
        print(
            f"semantic corpus current: {summary['statement_nodes']} statement nodes over "
            f"{summary['declarations']} declarations, {summary['coverage']['orphan_count']} orphans"
        )
        return 0

    OUTPUT.write_text(text, encoding="utf-8")
    summary = payload["summary"]
    print(
        f"wrote {OUTPUT.relative_to(ROOT)}: {summary['statement_nodes']} statement nodes, "
        f"{summary['relations']} relations, {summary['coverage']['orphan_count']} orphan declarations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
