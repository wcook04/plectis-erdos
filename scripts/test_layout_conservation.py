#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Conservation checks for the nested eight-problem layout.

Hosted download basenames, Lean module identities, and relocated research
libraries must survive the move. This does not rewrite historical permalinks.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

from lean_source import library_module_id
from publication_contract import artifact_hosted_filename, artifact_storage_path


ROOT = Path(__file__).resolve().parent.parent


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def hosted_basenames_from_contract(payload: dict) -> list[str]:
    return [
        artifact_hosted_filename(artifact)
        for artifact in payload.get("artifacts", [])
        if isinstance(artifact, dict)
    ]


def main() -> int:
    root_pdfs = sorted(path.name for path in ROOT.glob("*.pdf") if path.is_file())
    require(not root_pdfs, f"root PDFs must be empty: {root_pdfs}")

    contract = json.loads((ROOT / "docs" / "publication_contract.json").read_text(encoding="utf-8"))
    hosted = []
    for artifact in contract["artifacts"]:
        storage = artifact_storage_path(artifact)
        rendered = artifact["rendered_path"]
        require(rendered == storage, (artifact["id"], rendered, storage))
        require(storage.startswith("paper/") and storage.endswith(".pdf"), storage)
        name = Path(storage).name
        require("/" not in name, name)
        require(artifact_hosted_filename(artifact) == name, artifact["id"])
        hosted.append(name)
    require(len(hosted) == len(set(hosted)), hosted)

    completed = subprocess.run(
        ["git", "-C", str(ROOT), "show", "origin/main:docs/publication_contract.json"],
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode == 0 and completed.stdout:
        mainline = json.loads(completed.stdout)
        main_hosted = []
        for artifact in mainline.get("artifacts", []):
            rendered = artifact.get("rendered_path", "")
            storage = artifact.get("storage_path", rendered)
            main_hosted.append(Path(str(storage or rendered)).name)
        require(hosted == main_hosted, (hosted, main_hosted))

    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    graph = claims["machine_readable_paper"]["module_graph"]
    require(graph["root"] == "lean/Erdos249257.lean", graph["root"])
    require(graph["additional_roots"] == ["lean/ErdosProblems.lean"], graph["additional_roots"])
    for node in graph["nodes"]:
        require(not str(node["id"]).startswith("lean."), node["id"])
        require(str(node["path"]).startswith("lean/"), node["path"])
        require((ROOT / node["path"]).is_file(), node["path"])
        require(
            library_module_id(ROOT / node["path"], ROOT) == node["id"],
            (node["id"], node["path"]),
        )

    pin = claims["release"]["formal_source"]["ref"]
    sample = next(
        decl["module"]
        for claim in claims["claims"]
        for decl in claim.get("declarations", [])
        if isinstance(decl, dict) and decl.get("module", "").endswith(".lean")
    )
    require(not sample.startswith("lean/"), sample)
    require(not pin.startswith("lean/"), pin)

    require((ROOT / "research" / "Erdos243V5").is_dir(), "research/Erdos243V5 missing")
    require(
        (ROOT / "research" / "Erdos243V5" / "DensityQuantifiers.lean").is_file()
        or any((ROOT / "research" / "Erdos243V5").rglob("DensityQuantifiers.lean")),
        "Erdos243V5 DensityQuantifiers consumer missing",
    )
    require(
        (ROOT / "verification" / "Erdos251LargeCertificate").is_dir(),
        "verification/Erdos251LargeCertificate missing",
    )
    require(not (ROOT / "Erdos243V5").exists(), "Erdos243V5 still at root")
    require(not (ROOT / "Erdos251LargeCertificate").exists(), "large cert still at root")

    print(
        "test_layout_conservation: hosted basenames, module identities, "
        "and relocated research libraries conserved"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
