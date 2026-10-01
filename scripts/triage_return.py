#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Read-only native atlas retrieval for a research return.

Read-only bridge to the existing relation_registry.Atlas/LeanSource, not a new
index. The --repo checkout is Type A's trusted code, NOT code from the return.
Exact-name observations are retrieval evidence, never proof/novelty verdicts.
All paragraphs survive extraction, including those not selected by the lexical
candidate heuristic. Missing/ambiguous locators remain observations.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
from research_return_gate import GateError, bytes_sha, extract, require, safe_file

NAME = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+\b")

def triage(return_file: Path, repo: Path, max_names: int = 500) -> dict:
    require(type(max_names) is int and 1 <= max_names <= 5000, "max_names must be 1..5000")
    extracted = extract(return_file)
    module_path = safe_file(repo, "scripts/relation_registry.py")
    # Native owners use flat sibling imports. This is explicitly a trusted-code
    # boundary; untrusted archive extraction and code execution are out of scope.
    sys.path.insert(0, str(module_path.parent))
    try:
        spec = importlib.util.spec_from_file_location("_plectis_native_registry", module_path)
        require(spec is not None and spec.loader is not None, "native owner cannot load")
        native = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = native
        spec.loader.exec_module(native)
        atlas = native.Atlas.load(repo, native.LeanSource(repo))
        observations, selected = [], set()
        for span in extracted["all_paragraphs"]:
            # Backticks narrow retrieval noise; this intentionally does not claim
            # to recognize every theorem or any semantic paraphrase.
            for quoted in re.findall(r"`([^`\n]+)`", span["text"]):
                for name in NAME.findall(quoted):
                    if name.endswith((".py", ".lean", ".json", ".md", ".tex", ".zip")):
                        continue
                    key = (span["span_id"], name)
                    if key in selected:
                        continue
                    if len(selected) >= max_names:
                        break
                    selected.add(key)
                    hit = atlas.resolve(name)
                    observations.append({"span_id": span["span_id"], "query": name,
                        "evidence_class": "native_atlas_source_lookup", "observation": hit})
        extracted.update({"native_owner_sha256": bytes_sha(module_path.read_bytes()),
            "atlas_sha256": bytes_sha(safe_file(repo, "docs/declaration_atlas.json").read_bytes()),
            "name_lookup_limit": max_names, "name_lookup_at_limit": len(selected) >= max_names,
            "observations": observations, "authority": "retrieval_only_not_gate_acceptance",
            "unsearched": ["unquoted names", "semantic paraphrases", "external literature",
                           "other snapshots", "proof values and kernel acceptance"]})
        return extracted
    finally:
        sys.path.pop(0)

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("return_file", type=Path); p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--max-names", type=int, default=500)
    a = p.parse_args()
    try:
        print(json.dumps(triage(a.return_file, a.repo, a.max_names), indent=2, ensure_ascii=False))
        return 0
    except (GateError, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({"status": "blocked", "error": str(error)})); return 2

if __name__ == "__main__":
    raise SystemExit(main())
