#!/usr/bin/env python3
"""Self-contained fixture coverage for script_catalog.py."""

from __future__ import annotations

import tempfile
from pathlib import Path

from script_catalog import catalog


def _touch(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("# fixture\n", encoding="utf-8")


def main() -> int:
    with tempfile.TemporaryDirectory() as temporary_directory:
        root = Path(temporary_directory)
        _touch(root / "scripts" / "lean_fast_build.py")
        _touch(root / "scripts" / "check_problem_corpus_index.py")
        _touch(root / "scripts" / "script_catalog.py")
        _touch(root / "scripts" / "corpus_navigation.py")
        _touch(root / "scripts" / "verify_top_level.py")
        _touch(root / "ErdosProblems" / "Erdos257" / "scripts" / "check_window.py")
        _touch(root / "ErdosProblems" / "Erdos68" / "scripts" / "search.cpp")

        payload = catalog(root)
        problem_payload = catalog(root, problem="Erdos257")
        audit_payload = catalog(root, problem="257", role="audit")
        corpus_payload = catalog(root, scope="corpus")
        corpus_navigation_payload = catalog(root, scope="corpus", role="corpus_navigation")

    assert payload["summary"]["script_count"] == 7
    assert payload["summary"]["by_scope"] == {"corpus": 5, "problem": 2}
    assert payload["summary"]["by_role"] == {
        "audit": 1,
        "corpus_navigation": 2,
        "corpus_structure_check": 1,
        "experiment_or_helper": 1,
        "lean_build_wrapper": 1,
        "verification": 1,
    }
    by_path = {entry["path"]: entry for entry in payload["scripts"]}
    assert by_path["ErdosProblems/Erdos257/scripts/check_window.py"]["problem_id"] == "erdos_257"
    assert by_path["ErdosProblems/Erdos68/scripts/search.cpp"]["language"] == "cpp"
    assert problem_payload["filters"] == {
        "problem_id": "erdos_257",
        "role": None,
        "scope": None,
    }
    assert problem_payload["summary"]["script_count"] == 1
    assert problem_payload["scripts"] == [
        {
            "language": "py",
            "path": "ErdosProblems/Erdos257/scripts/check_window.py",
            "problem_id": "erdos_257",
            "role": "audit",
            "scope": "problem",
        }
    ]
    assert audit_payload["filters"] == {
        "problem_id": "erdos_257",
        "role": "audit",
        "scope": None,
    }
    assert audit_payload["summary"]["script_count"] == 1
    assert audit_payload["scripts"] == problem_payload["scripts"]
    assert corpus_payload["filters"] == {"problem_id": None, "role": None, "scope": "corpus"}
    assert corpus_payload["summary"] == {
        "script_count": 5,
        "by_scope": {"corpus": 5},
        "by_role": {
            "corpus_navigation": 2,
            "corpus_structure_check": 1,
            "lean_build_wrapper": 1,
            "verification": 1,
        },
        "by_language": {"py": 5},
    }
    assert corpus_navigation_payload["filters"] == {
        "problem_id": None,
        "role": "corpus_navigation",
        "scope": "corpus",
    }
    assert [entry["path"] for entry in corpus_navigation_payload["scripts"]] == [
        "scripts/corpus_navigation.py",
        "scripts/script_catalog.py",
    ]
    print("script catalog fixtures: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
