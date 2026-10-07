#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Reproducible, source-limited Patel-style analysis of the tracked Lean graph.

This is an observational profile, not a predictor of proof difficulty or a
claim that any source proof is shortest.  It reads only files in this checkout.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import json
import math
import random
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
DEFAULT_OUTPUT = Path(__file__).with_name("profile.json")
PAPER = "https://arxiv.org/abs/2609.28603"
DEFINITION_KINDS = {"def", "abbrev", "structure", "class", "inductive", "instance"}
THEOREM_KINDS = {"theorem", "lemma"}
PERMUTATION_SEED = 260928603
PERMUTATIONS = 64


def _visible_lines(text: str) -> list[str]:
    """Blank nested Lean comments while retaining strings and line boundaries."""
    depth = 0
    in_string = False
    escaped = False
    result: list[str] = []
    for raw in text.splitlines():
        out: list[str] = []
        i = 0
        while i < len(raw):
            pair = raw[i : i + 2]
            if depth:
                if pair == "/-":
                    depth += 1
                    i += 2
                elif pair == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            if in_string:
                out.append(raw[i])
                if escaped:
                    escaped = False
                elif raw[i] == "\\":
                    escaped = True
                elif raw[i] == '"':
                    in_string = False
                i += 1
                continue
            if pair == "--":
                break
            if pair == "/-":
                depth = 1
                i += 2
                continue
            if raw[i] == '"':
                in_string = True
            out.append(raw[i])
            i += 1
        result.append("".join(out))
    return result


def code_mask(text: str) -> list[bool]:
    """Mark source lines carrying code; exclude Lean comment and axiom probes."""
    return [
        bool(line.strip()) and not line.lstrip().startswith("#print axioms")
        for line in _visible_lines(text)
    ]


def _is_top_level_command(line: str) -> bool:
    if line != line.lstrip():
        return False
    return bool(
        re.match(
            r"(?:end|namespace|section|open|variable|variables|set_option|"
            r"attribute|export|#print|#check|#eval)\b",
            line,
        )
    )


def declaration_spans(
    path: Path | str, declarations: list[dict], text: str | None = None
) -> dict[str, dict]:
    """Measure non-overlapping declaration bodies, including private boundaries.

    Coordinates are 1-based and inclusive.  Source span limits use every atlas
    declaration, not just graph-resolved declarations, so a private helper does
    not silently become part of the preceding public theorem's local proof.
    """
    if text is None:
        text = Path(path).read_text(encoding="utf-8")
    visible = _visible_lines(text)
    mask = [bool(s.strip()) and not s.lstrip().startswith("#print axioms") for s in visible]
    ordered = sorted(declarations, key=lambda d: (int(d["line"]), d["id"]))
    spans: dict[str, dict] = {}
    for position, declaration in enumerate(ordered):
        start = int(declaration["line"])
        end = (
            int(ordered[position + 1]["line"]) - 1
            if position + 1 < len(ordered)
            else len(visible)
        )
        end = min(end, len(visible))
        # A trailing audit command or namespace footer is not part of the
        # declaration's span, even when this is the module's final theorem.
        while end >= start and (
            not mask[end - 1] or _is_top_level_command(visible[end - 1])
        ):
            end -= 1
        signature = declaration.get("signature", "")
        private = bool(re.search(r"\bprivate\b", signature.split(declaration["kind"], 1)[0]))
        proof_start: int | None = None
        for line_index in range(start - 1, end):
            line = visible[line_index]
            if ":=" in line or re.search(r"\bwhere\b", line):
                proof_start = line_index
                break
        proof_lines = 0
        if proof_start is not None:
            proof_lines = sum(
                mask[i] and not _is_top_level_command(visible[i])
                for i in range(proof_start, end)
            )
        spans[declaration["id"]] = {
            "start_line": start,
            "end_line": end,
            "proof_lines": proof_lines,
            "statement_chars": len(signature),
            "private": private,
            "body_found": proof_start is not None,
        }
    return spans


def closure_cost(
    start_id: int,
    adjacency: dict[int, set[int]] | list[list[int]],
    proof_lines: dict[int, int] | list[int],
    available: set[int] | tuple[int, ...] = (),
) -> int:
    """Expand each reachable value dependency once, cutting available premises.

    A shared ancestor still costs source lines if reached by another branch.
    This is a source-DAG accounting operation, not ideal Bellman equality.
    """
    blocked = set(available)
    seen: set[int] = set()
    stack = [start_id]
    total = 0
    while stack:
        node = stack.pop()
        if node in seen or node in blocked:
            continue
        seen.add(node)
        total += proof_lines[node]
        stack.extend(adjacency[node])
    return total


def _ranks(values: list[float | int]) -> list[float]:
    order = sorted(range(len(values)), key=lambda i: values[i])
    ranks = [0.0] * len(values)
    left = 0
    while left < len(order):
        right = left + 1
        while right < len(order) and values[order[right]] == values[order[left]]:
            right += 1
        mean_rank = (left + 1 + right) / 2.0
        for index in order[left:right]:
            ranks[index] = mean_rank
        left = right
    return ranks


def spearman(xs: list[float | int], ys: list[float | int]) -> float | None:
    """Spearman rank correlation with midranks for ties."""
    if len(xs) != len(ys) or len(xs) < 2:
        return None
    rx, ry = _ranks(xs), _ranks(ys)
    mean = (len(xs) + 1) / 2.0
    numerator = sum((a - mean) * (b - mean) for a, b in zip(rx, ry))
    vx = sum((a - mean) ** 2 for a in rx)
    vy = sum((b - mean) ** 2 for b in ry)
    return numerator / math.sqrt(vx * vy) if vx and vy else None


def _bit_members(bits: int):
    while bits:
        low = bits & -bits
        yield low.bit_length() - 1
        bits ^= low


def _closure_bitsets(adjacency: list[list[int]]) -> list[int]:
    """Condense cycles, then compute unique reachability with compact bitsets."""
    count = len(adjacency)
    seen = bytearray(count)
    finish: list[int] = []
    for root in range(count):
        if seen[root]:
            continue
        seen[root] = 1
        stack = [(root, 0)]
        while stack:
            node, offset = stack[-1]
            if offset < len(adjacency[node]):
                target = adjacency[node][offset]
                stack[-1] = (node, offset + 1)
                if not seen[target]:
                    seen[target] = 1
                    stack.append((target, 0))
            else:
                finish.append(node)
                stack.pop()
    reverse: list[list[int]] = [[] for _ in range(count)]
    for node, targets in enumerate(adjacency):
        for target in targets:
            reverse[target].append(node)
    component = [-1] * count
    members: list[list[int]] = []
    for root in reversed(finish):
        if component[root] >= 0:
            continue
        group_id = len(members)
        group: list[int] = []
        stack = [root]
        component[root] = group_id
        while stack:
            node = stack.pop()
            group.append(node)
            for target in reverse[node]:
                if component[target] < 0:
                    component[target] = group_id
                    stack.append(target)
        members.append(group)
    dependencies: list[set[int]] = [set() for _ in members]
    users: list[set[int]] = [set() for _ in members]
    for node, targets in enumerate(adjacency):
        group = component[node]
        for target in targets:
            other = component[target]
            if other != group:
                dependencies[group].add(other)
                users[other].add(group)
    remaining = [len(group) for group in dependencies]
    ready = [i for i, n in enumerate(remaining) if n == 0]
    heapq.heapify(ready)
    bits = [sum(1 << node for node in group) for group in members]
    processed = 0
    while ready:
        group = heapq.heappop(ready)
        processed += 1
        for target in sorted(dependencies[group]):
            bits[group] |= bits[target]
        for user in users[group]:
            remaining[user] -= 1
            if remaining[user] == 0:
                heapq.heappush(ready, user)
    if processed != len(members):
        raise ValueError("condensed dependency graph is cyclic")
    return [bits[component[i]] for i in range(count)]


def _definition_chars(
    start: int, type_adjacency: list[list[int]], kinds: list[str], chars: list[int]
) -> tuple[int, int]:
    seen: set[int] = set()
    stack = list(type_adjacency[start])
    while stack:
        node = stack.pop()
        if node in seen or kinds[node] not in DEFINITION_KINDS:
            continue
        seen.add(node)
        stack.extend(type_adjacency[node])
    return sum(chars[node] for node in seen), len(seen)


def _normal_statement(signature: str, name: str) -> str:
    prefix = re.compile(
        r"^.*?\b(?:theorem|lemma)\s+" + re.escape(name) + r"(?=$|[\s({:\[])"
    )
    return re.sub(r"\s+", " ", prefix.sub("", signature, count=1)).strip()


def _source_sha256(root: Path, paths: list[str]) -> str:
    digest = hashlib.sha256()
    for path in sorted(paths):
        raw = (root / path).read_bytes()
        digest.update(path.encode("utf-8") + b"\0")
        digest.update(hashlib.sha256(raw).digest())
    return "sha256:" + digest.hexdigest()


def _hash_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _problem(module: str) -> str | None:
    match = re.search(r"/Erdos(68|243|249|251|257|269|1041|1049)(?:/|\.)", module)
    return match.group(1) if match else None


def _record(nodes: list[dict], rows: list[dict], node_id: int) -> dict:
    node = nodes[node_id]
    row = rows[node_id]
    return {
        "handle": node["handle"],
        "source_ref": node["source_ref"],
        "local_proof_lines": row["local_proof_lines"],
        "expanded_proof_lines": row["expanded_proof_lines"],
        "direct_users": row["direct_users"],
        "direct_non_generated_users": row["direct_non_generated_users"],
        "generated_ancestry_fraction": row["generated_ancestry_fraction"],
    }


def _load_inputs(root: Path) -> dict:
    root = Path(root)
    atlas_path = root / "docs/declaration_atlas.json"
    graph_path = root / "docs/lean_dependency_index.json"
    atlas = json.loads(atlas_path.read_text(encoding="utf-8"))
    graph = json.loads(graph_path.read_text(encoding="utf-8"))
    if atlas["source_fingerprint"] != graph["source_fingerprint"]:
        raise ValueError("atlas and dependency index have different source fingerprints")
    nodes = graph["nodes"]
    if any(node["node_id"] != i for i, node in enumerate(nodes)):
        raise ValueError("dependency node IDs are not dense and ordered")
    count = len(nodes)
    atlas_by_module: dict[str, list[dict]] = defaultdict(list)
    atlas_by_ref: dict[tuple[str, int], dict] = {}
    for declaration in atlas["declarations"]:
        atlas_by_module[declaration["module"]].append(declaration)
        atlas_by_ref[(declaration["module"], declaration["line"])] = declaration
    modules = sorted({node["module"] for node in nodes})
    spans: dict[str, dict] = {}
    for module in modules:
        spans.update(declaration_spans(root / module, atlas_by_module[module]))
    local = [0] * count
    signature_chars = [0] * count
    kinds = [node["declaration_kind"] for node in nodes]
    generated = [False] * count
    private_nodes = 0
    body_missing = 0
    for i, node in enumerate(nodes):
        declaration = atlas_by_ref.get((node["module"], node["line"]))
        if declaration is None:
            raise ValueError(f"node lacks atlas source: {node['source_ref']}")
        span = spans[declaration["id"]]
        local[i] = span["proof_lines"]
        signature_chars[i] = span["statement_chars"]
        generated[i] = bool(declaration["generated_certificate"])
        private_nodes += span["private"]
        body_missing += not span["body_found"]
    value_adj: list[list[int]] = [[] for _ in nodes]
    type_adj: list[list[int]] = [[] for _ in nodes]
    direct_users: list[set[int]] = [set() for _ in nodes]
    for source, target, bits in graph["edges"]:
        if bits & 2:
            value_adj[source].append(target)
            direct_users[target].add(source)
        if bits & 1:
            type_adj[source].append(target)
    for neighbors in value_adj:
        neighbors.sort()
    return {
        "atlas": atlas,
        "graph": graph,
        "nodes": nodes,
        "atlas_by_ref": atlas_by_ref,
        "modules": modules,
        "spans": spans,
        "local": local,
        "signature_chars": signature_chars,
        "kinds": kinds,
        "generated": generated,
        "private_nodes": private_nodes,
        "body_missing": body_missing,
        "value_adj": value_adj,
        "type_adj": type_adj,
        "direct_users": direct_users,
    }


def load_indexed_cost_graph(
    root: Path = ROOT,
) -> tuple[list[dict], list[list[int]], list[int], list[bool]]:
    """Return source-resolved nodes, value edges, source LOC, certificate flags."""
    data = _load_inputs(Path(root))
    return data["nodes"], data["value_adj"], data["local"], data["generated"]


def build_profile(root: Path = ROOT) -> dict:
    root = Path(root)
    atlas_path = root / "docs/declaration_atlas.json"
    graph_path = root / "docs/lean_dependency_index.json"
    data = _load_inputs(root)
    atlas = data["atlas"]
    graph = data["graph"]
    nodes = data["nodes"]
    atlas_by_ref = data["atlas_by_ref"]
    modules = data["modules"]
    spans = data["spans"]
    local = data["local"]
    signature_chars = data["signature_chars"]
    kinds = data["kinds"]
    generated = data["generated"]
    private_nodes = data["private_nodes"]
    body_missing = data["body_missing"]
    value_adj = data["value_adj"]
    type_adj = data["type_adj"]
    direct_users = data["direct_users"]
    count = len(nodes)
    closure = _closure_bitsets(value_adj)
    expanded = [0] * count
    certificate_lines = [0] * count
    certificate_named_lines = [0] * count
    omitted_ancestry_refs = [0] * count
    ancestors = [0] * count
    certificate_named = [
        bool(re.search(r"certif|laddert", node["module"], re.IGNORECASE))
        for node in nodes
    ]
    for i, bits in enumerate(closure):
        expanded[i] = sum(local[j] for j in _bit_members(bits))
        certificate_lines[i] = sum(local[j] for j in _bit_members(bits) if generated[j])
        certificate_named_lines[i] = sum(
            local[j] for j in _bit_members(bits) if certificate_named[j]
        )
        omitted_ancestry_refs[i] = sum(
            nodes[j]["omitted_internal_reference_count"] for j in _bit_members(bits)
        )
        ancestors[i] = bits.bit_count() - 1
    rows: list[dict] = []
    for i, node in enumerate(nodes):
        definition_chars, definition_count = _definition_chars(i, type_adj, kinds, signature_chars)
        description_chars = signature_chars[i] + definition_chars
        interest = 100 * expanded[i] / description_chars if description_chars else None
        fraction = certificate_lines[i] / expanded[i] if expanded[i] else 0.0
        nongenerated_users = sum(not generated[user] for user in direct_users[i])
        rows.append({
            "local_proof_lines": local[i],
            "expanded_proof_lines": expanded[i],
            "statement_chars": signature_chars[i],
            "resolved_definition_count": definition_count,
            "description_chars": description_chars,
            "interestingness_proxy": interest,
            "direct_users": len(direct_users[i]),
            "direct_non_generated_users": nongenerated_users,
            "utility_proxy": len(direct_users[i]) * expanded[i],
            "utility_proxy_non_generated_users": nongenerated_users * expanded[i],
            "generated_ancestry_lines": certificate_lines[i],
            "generated_ancestry_fraction": fraction,
            "certificate_named_ancestry_lines": certificate_named_lines[i],
            "resolved_value_ancestors": ancestors[i],
            "omitted_internal_references": node["omitted_internal_reference_count"],
            "omitted_internal_references_in_value_ancestry": omitted_ancestry_refs[i],
        })
    cohort = [
        i for i in range(count)
        if kinds[i] in THEOREM_KINDS
        and rows[i]["direct_users"] > 0
        and rows[i]["expanded_proof_lines"] > 0
        and rows[i]["description_chars"] > 0
    ]

    def correlation(indices: list[int], outcome: str = "utility_proxy") -> dict:
        return {
            "n": len(indices),
            "spearman_rho": spearman(
                [rows[i]["interestingness_proxy"] for i in indices],
                [rows[i][outcome] for i in indices],
            ),
        }

    scores = [rows[i]["interestingness_proxy"] for i in cohort]
    degrees = [rows[i]["direct_users"] for i in cohort]
    values = [rows[i]["expanded_proof_lines"] for i in cohort]
    rng = random.Random(PERMUTATION_SEED)
    permuted_rhos: list[float] = []
    for _ in range(PERMUTATIONS):
        shuffled = degrees.copy()
        rng.shuffle(shuffled)
        rho = spearman(scores, [d * v for d, v in zip(shuffled, values)])
        if rho is not None:
            permuted_rhos.append(rho)
    non_generated = [i for i in cohort if not generated[i] and certificate_lines[i] == 0]
    non_generated_users = [
        i for i in non_generated if rows[i]["direct_non_generated_users"] > 0
    ]
    no_certificate_named_ancestry = [
        i for i in cohort if certificate_named_lines[i] == 0
    ]
    no_wrappers = [i for i in cohort if local[i] > 3]
    no_omissions = [i for i in cohort if omitted_ancestry_refs[i] == 0]
    controls = {
        "interestingness_vs_utility": correlation(cohort),
        "interestingness_vs_direct_users": correlation(cohort, "direct_users"),
        "interestingness_vs_expanded_proof_lines": correlation(cohort, "expanded_proof_lines"),
        "permuted_degree_times_same_proof_lines": {
            "seed": PERMUTATION_SEED,
            "replicates": PERMUTATIONS,
            "mean_rho": sum(permuted_rhos) / len(permuted_rhos) if permuted_rhos else None,
            "min_rho": min(permuted_rhos) if permuted_rhos else None,
            "max_rho": max(permuted_rhos) if permuted_rhos else None,
            "permutation_rhos": permuted_rhos,
            "fraction_at_least_observed": (
                sum(rho >= correlation(cohort)["spearman_rho"] for rho in permuted_rhos)
                / len(permuted_rhos)
                if permuted_rhos and correlation(cohort)["spearman_rho"] is not None
                else None
            ),
        },
    }
    sensitivity = {
        "remove_generated_targets_and_any_generated_value_ancestry": correlation(non_generated),
        "also_remove_generated_direct_users": correlation(
            non_generated_users, "utility_proxy_non_generated_users"
        ),
        "remove_any_certificate_named_module_ancestry": correlation(
            no_certificate_named_ancestry
        ),
        "remove_local_wrappers_at_most_three_proof_lines": correlation(no_wrappers),
        "remove_nodes_with_omitted_internal_refs_anywhere_in_value_ancestry": correlation(no_omissions),
        "generated_target_count": sum(generated),
        "generated_direct_value_edge_count": sum(
            generated[target] for targets in value_adj for target in targets
        ),
        "certificate_majority_ancestry_in_cohort": sum(
            rows[i]["generated_ancestry_fraction"] >= 0.5 for i in cohort
        ),
    }
    signature_groups: dict[str, list[int]] = defaultdict(list)
    for i in cohort:
        if generated[i]:
            continue
        declaration = atlas_by_ref[(nodes[i]["module"], nodes[i]["line"])]
        statement = _normal_statement(declaration["signature"], nodes[i]["name"])
        if len(statement) >= 20:
            signature_groups[statement].append(i)
    duplicate_groups = [ids for ids in signature_groups.values() if len(ids) > 1]
    duplicate_groups.sort(key=lambda ids: (-len(ids), -sum(rows[i]["utility_proxy"] for i in ids), ids))
    duplicate_review = [
        {
            "reason": "identical_compact_source_statement_after_declaration_name_removed",
            "candidate_handles": [nodes[i]["handle"] for i in ids[:8]],
            "candidate_count": len(ids),
            "statement_excerpt": _normal_statement(
                atlas_by_ref[(nodes[ids[0]]["module"], nodes[ids[0]]["line"])]["signature"],
                nodes[ids[0]]["name"],
            )[:180],
            "required_next_validation": "Elaborate full types under their namespaces and check existing Mathlib containment before any deduplication or upstream claim.",
        }
        for ids in duplicate_groups[:12]
    ]
    reuse_candidates = sorted(
        (
            i for i in non_generated_users
            if certificate_named_lines[i] == 0
        ),
        key=lambda i: (
            -rows[i]["utility_proxy_non_generated_users"],
            -rows[i]["direct_non_generated_users"],
            nodes[i]["handle"],
        ),
    )[:12]
    certificate_candidates = sorted(
        (i for i in cohort if rows[i]["generated_ancestry_fraction"] >= 0.5),
        key=lambda i: (-rows[i]["utility_proxy"], nodes[i]["handle"]),
    )[:12]
    cross_problem: list[dict] = []
    for i, node in enumerate(nodes):
        if "/Synthesis/" not in node["module"]:
            continue
        sources = sorted({_problem(nodes[j]["module"]) for j in value_adj[i]} - {None})
        if len(sources) >= 2:
            cross_problem.append({
                "target": node["handle"],
                "source_ref": node["source_ref"],
                "direct_problem_sources": sources,
                "source_declarations": [
                    nodes[j]["handle"] for j in value_adj[i]
                    if _problem(nodes[j]["module"]) is not None
                ],
                "local_proof_lines": local[i],
                "expanded_proof_lines": expanded[i],
            })
    cross_problem.sort(key=lambda row: row["target"])
    transfer: list[dict] = []
    for i, node in enumerate(nodes):
        if not node["module"].endswith("/Synthesis/DyadicShiftEscape.lean"):
            continue
        if node["name"] not in {
            "cofinal_separated_tailShifts_of_irrational",
            "cofinal_third_separated_tailShifts_of_irrational",
        }:
            continue
        premises = [
            j for j in value_adj[i]
            if nodes[j]["name"].startswith("boundedRadix_zero_or_cofinal_far")
            or nodes[j]["name"] == "irrational_initial_iff_all_positive_tailShifts_nonintegral"
        ]
        if len(premises) != 2:
            continue
        with_premises = closure_cost(i, value_adj, local, available=set(premises))
        transfer.append({
            "target": node["handle"],
            "source_ref": node["source_ref"],
            "available_direct_premises": [nodes[j]["handle"] for j in premises],
            "indexed_source_line_subtotal_without_premises": expanded[i],
            "indexed_source_line_subtotal_with_two_premises_available": with_premises,
            "indexed_source_line_subtotal_difference": expanded[i] - with_premises,
            "local_bridge_lines": local[i],
            "interpretation": "Restricted source-DAG subtotal accounting only; this is neither actual proof-length savings nor ideal shortest-proof Bellman equality.",
        })
    private_spans = [s for s in spans.values() if s["private"]]
    summary = {
        "resolved_node_count": count,
        "resolved_theorem_or_lemma_count": sum(kind in THEOREM_KINDS for kind in kinds),
        "correlation_cohort_count": len(cohort),
        "private_atlas_declarations_in_loaded_modules": len(private_spans),
        "private_helper_proof_lines_not_source_joined": sum(s["proof_lines"] for s in private_spans),
        "resolved_declarations_without_detected_body": body_missing,
        "resolved_private_node_count": private_nodes,
        "zero_local_proof_line_nodes": sum(cost == 0 for cost in local),
        "cross_problem_synthesis_direct_multi_source_count": len(cross_problem),
        "pure_text_duplicate_candidate_group_count": len(duplicate_groups),
    }
    return {
        "schema": "plectis-patel-interestingness-profile/1",
        "paper": PAPER,
        "inputs": {
            "public_revision": subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=root, text=True
            ).strip(),
            "declaration_atlas": "docs/declaration_atlas.json",
            "declaration_atlas_sha256": _hash_file(atlas_path),
            "dependency_index": "docs/lean_dependency_index.json",
            "dependency_index_sha256": _hash_file(graph_path),
            "lean_source_manifest_sha256": _source_sha256(root, modules),
            "shared_source_fingerprint": atlas["source_fingerprint"],
        },
        "definitions": {
            "observed_V_empty": "Indexed proof-source subtotal: code-bearing proof lines of distinct source-resolved declarations reachable by value-reference (edge bit 2), including the target. This is neither a complete observed proof cost nor a shortest proof.",
            "observed_V_given_P": "Traverse value references from target and stop at available premise vertices; shared ancestors reached by another path remain charged.",
            "observed_L_empty": "Characters in atlas compact source signature of target plus compact signatures of distinct source-resolved definitions transitively reached through type-reference edges (bit 1). This approximates Eq. 5; the atlas truncates signatures at 800 characters and unresolved/external definitions are missing.",
            "interestingness_proxy": "100 * observed_V_empty / observed_L_empty (Patel et al. Eq. 6 structure; not numerically comparable to their mathlib I0).",
            "utility_proxy": "source-resolved direct value-reference user count * indexed proof-source subtotal (Patel et al. Eq. 7 structure).",
            "utility_proxy_non_generated_users": "source-resolved non-generated direct value-reference user count * indexed proof-source subtotal.",
            "correlation_cohort": "Resolved theorem/lemma targets with positive direct users, proof lines, and description characters; rank ties use average ranks.",
            "generated_ancestry": "Generated-certificate atlas flag appears anywhere in the value-reference closure; sensitivity removes the entire affected target. A separate conservative module-name heuristic also removes certificate-related modules and their descendants.",
        },
        "coverage": {**graph["coverage"], **summary},
        "correlations": controls,
        "sensitivity": sensitivity,
        "transfer_251_to_269": transfer,
        "cross_problem_reuse": cross_problem[:20],
        "stewardship_candidates": {
            "compression_reuse": [
                {**_record(nodes, rows, i),
                 "reason": "High non-generated direct reuse times indexed proof-source subtotal, after excluding generated and certificate-named ancestry.",
                 "required_next_validation": "Read the theorem and each major consumer; check mathematical containment, actual proof compression, and whether a clearer shared lemma exists."}
                for i in reuse_candidates
            ],
            "duplicate_review": duplicate_review,
            "certificate_ablation": [
                {**_record(nodes, rows, i),
                 "reason": "At least half of observed expanded source lines lie in generated certificate ancestry.",
                 "required_next_validation": "Inspect the certificate manifest and theorem statement; compare ranking after generated ancestry is removed before assigning stewardship priority."}
                for i in certificate_candidates
            ],
        },
        "limitations": [
            "The indexed subtotal omits unresolved public edges, internal references, and atlas declarations not in the source-resolved graph. It can be smaller than a fully expanded version of this recorded proof; it is not a lower bound on shortest proof cost.",
            "Private helpers remain separate declaration spans; their source lines are not silently charged to preceding public theorems, and inaccessible private dependency edges can understate proof cost.",
            "Source spans, compact signatures, and direct references are proxies. Tactics, elaboration, definitions, and proof alternatives make these values incomparable to an ideal shortest proof.",
            "Generated certificate ladders, thin wrapper declarations, and direct-user degree can dominate correlations; the negative controls and ablations must accompany any interpretation.",
            "Identical compact source text is only a review candidate; namespaces, elaborated constants, implicit arguments, and Mathlib containment can change its meaning.",
            "A high metric is neither novelty, significance, a new theorem, nor progress on an open problem.",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args(argv)
    profile = build_profile(ROOT)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(profile, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
