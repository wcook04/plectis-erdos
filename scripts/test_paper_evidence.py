#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for scripts/paper_evidence.py.

A synthetic paper repository and a synthetic Comparator corpus are built in a temporary
directory.  The resolver must accept the sound fixture, and must refuse, without writing
anything, each way the evidence behind a margin mark can be wrong: a result with no label,
a declaration missing at the Lean pin, a replay report that does not show a passing check,
a report whose recorded digests do not match the corpus bytes, a declaration of a
multi-declaration result with no Comparator association of its own, a corpus statement that
differs from the pinned one, and a stronger Lean statement whose relation note is missing
or was written against another statement.  A check that cannot fail proves nothing.
"""

from __future__ import annotations

import contextlib
import io
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Callable

import paper_evidence as pe

PAPER_ID = "synthetic-note"
SOURCE = "paper/99/synthetic-note.tex"
LEAN_FILE = "lean/Syn/Results.lean"
LEAN_TEXT = """\
namespace Syn

/-- The first synthetic result. -/
theorem first_result : True := trivial

theorem second_result (n : Nat) : n + 0 = n := rfl

theorem third_result (n : Nat) : 0 + n = n := Nat.zero_add n

end Syn
"""
TEX = """\
\\newtheorem{theorem}{Theorem}
\\begin{theorem}[first]\\label{res:first}
Every synthetic statement holds.
\\end{theorem}
\\begin{theorem}[second]\\label{res:second}
Adding zero changes nothing.
\\end{theorem}
"""
CHALLENGE = """\
namespace Syn

theorem first_result : True := by sorry

theorem second_result (n : Nat) : n + 0 = n := by sorry

theorem third_result (n : Nat) : 0 + n = n := by sorry

end Syn
"""
SOLUTION = """\
import Syn.Results
namespace Syn
theorem first_result : True := _root_.Syn.first_result
theorem second_result (n : Nat) : n + 0 = n := _root_.Syn.second_result n
theorem third_result (n : Nat) : 0 + n = n := _root_.Syn.third_result n
end Syn
"""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True,
                          text=True).stdout.strip()


def commit_all(root: Path, message: str) -> str:
    git(root, "add", "-A")
    git(root, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", message)
    return git(root, "rev-parse", "HEAD")


def write(root: Path, rel: str, text: str) -> None:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


class Fixture:
    """A paper repository and a corpus that together pass; tests break one thing each."""

    def __init__(self, base: Path) -> None:
        self.root = base / "paper-repo"
        self.corpus = base / "corpus"
        for repo in (self.root, self.corpus):
            repo.mkdir()
            git(repo, "init", "-q")
        write(self.root, LEAN_FILE, LEAN_TEXT)
        write(self.root, "lean-toolchain", "leanprover/lean4:v4.29.1\n")
        write(self.root, "lake-manifest.json", json.dumps({"packages": [{"name": "mathlib", "rev": "c" * 40}]}))
        self.pin = commit_all(self.root, "lean")
        write(self.corpus, "PalomarCorpus/E1/Challenge.lean", CHALLENGE)
        write(self.corpus, "PalomarCorpus/E1/comparator.json", "{}\n")
        write(self.corpus, "PalomarCorpus/E1/formalization.yaml", "entry: E1\n")
        write(self.corpus, "Solutions/PalomarCorpus/E1.lean", SOLUTION)
        write(self.corpus, "Syn/Results.lean", LEAN_TEXT)
        self.corpus_commit = commit_all(self.corpus, "corpus")
        self.ledger = {
            "lean_pin": self.pin,
            "papers": [{"paper_id": PAPER_ID, "problem": 99, "side": "short", "sources": [SOURCE]}],
            "rows": [
                self.row("res:first", "exact", ["Syn.first_result"], compared=True),
                self.row("res:second", "exact_or_stronger", ["Syn.second_result", "Syn.third_result"],
                         compared=True),
            ],
        }
        self.receipt = {
            "schema": pe.RECEIPT_SCHEMA, "entry": "E1",
            "github": {"sha": self.corpus_commit, "run_id": "1", "repository": "wcook04/plectis-erdos-lean"},
            "theorem_names": ["Syn.first_result", "Syn.second_result", "Syn.third_result"],
            "permitted_axioms": list(pe.PERMITTED_AXIOMS),
            "entry_digests": {"Challenge.lean": sha(CHALLENGE), "comparator.json": sha("{}\n"),
                              "formalization.yaml": sha("entry: E1\n")},
            "solution": {"files": {"Solutions/PalomarCorpus/E1.lean": sha(SOLUTION)}},
            "exit": 0, "verification": {"outcome": "passed"},
            "kernel_acceptance": {"lean_default": True, "nanoda": True},
        }
        self.associations = {
            "corpus_commit": self.corpus_commit, "run_id": "1",
            "declarations": {
                name: {"entry": "E1", "challenge": name, "solution": f"Solutions.PalomarCorpus.E1.{name}",
                       "solution_path": "Solutions/PalomarCorpus/E1.lean"}
                for name in ("Syn.first_result", "Syn.second_result", "Syn.third_result")
            },
        }
        self.tex = TEX
        self.relations: dict[str, Any] = {"rows": {}}

    def row(self, label: str, status: str, names: list[str], compared: bool) -> dict[str, Any]:
        return {
            "id": f"{PAPER_ID}#{label}", "paper_id": PAPER_ID, "label": label,
            "environment": "theorem", "source": f"{SOURCE}:1", "statement_sha256": "",
            "lean": {"status": status, "declarations": [{"name": n, "file": LEAN_FILE} for n in names]},
            "comparator": {"status": "compared" if compared else "pending"},
        }

    def materialise(self) -> None:
        self.ledger["lean_pin"] = self.pin
        write(self.root, SOURCE, self.tex)
        import check_lean_paper_propagation as chk  # noqa: PLC0415
        digests = {e["labels"][0]: e["statement_sha256"] for e in chk.inventory([(SOURCE, self.tex)], []) if e["labels"]}
        for row in self.ledger["rows"]:
            row["statement_sha256"] = digests.get(row["label"], row["statement_sha256"])
        write(self.root, pe.LEDGER, json.dumps(self.ledger))
        write(self.root, pe.CONFIG, json.dumps({
            "corpus_commit": self.corpus_commit,
            "replay": {"run_id": "1", "receipts": "evidence/comparator/replay-1"},
            "record_commit": "d" * 40,
        }))
        write(self.root, pe.ASSOCIATIONS, json.dumps(self.associations))
        write(self.root, pe.RELATIONS, json.dumps(self.relations))
        write(self.root, "evidence/comparator/replay-1/receipt-E1.json", json.dumps(self.receipt))
        write(self.root, "docs/publication_contract.json", json.dumps({"artifacts": [
            {"storage_path": f"paper/99/{PAPER_ID}.pdf", "title": "A synthetic note"}]}))

    def resolve(self, *, require_relations: bool = False) -> list[str]:
        self.materialise()
        problems = pe.Problems()
        pe.resolve(self.root, pe.Repo(self.corpus), None, None, problems, require_relations=require_relations)
        return problems.items

    def relation_for(self, label: str) -> dict[str, Any]:
        """A relation note stamped against the current statement and Lean statements."""
        self.materialise()
        problems = pe.Problems()
        evidence = pe.resolve(self.root, pe.Repo(self.corpus), None, None, problems, require_relations=False)
        result = next(r for p in evidence["papers"] for r in p["results"] if r["label"] == label)
        return {"note": "The Lean statements are the printed one read from both sides.",
                "statement_key": result["statement_key"],
                "lean_statements": {d["name"]: d["statement_sha256"] for d in result["lean"]["declarations"]}}


def with_fixture(test: Callable[[Fixture], None]) -> Callable[[], None]:
    def run() -> None:
        with tempfile.TemporaryDirectory() as base:
            test(Fixture(Path(base)))
    run.__name__ = test.__name__
    return run


@with_fixture
def test_sound_fixture_resolves(f: Fixture) -> None:
    require(f.resolve() == [], f"the sound fixture failed: {f.resolve()}")
    f.relations["rows"][f"{PAPER_ID}#res:second"] = f.relation_for("res:second")
    require(f.resolve(require_relations=True) == [], "a stamped relation note was refused")


@with_fixture
def test_unlabelled_result_is_refused(f: Fixture) -> None:
    f.tex = f.tex.replace("\\label{res:second}", "")
    f.ledger["rows"][1]["label"] = ""
    require(any("has no label" in p for p in f.resolve()), "a result with no label was accepted")


@with_fixture
def test_declaration_missing_at_the_pin_is_refused(f: Fixture) -> None:
    f.ledger["rows"][0]["lean"]["declarations"][0]["name"] = "Syn.renamed_result"
    require(any("not declared" in p for p in f.resolve()), "a declaration absent at the pin was accepted")


@with_fixture
def test_failed_replay_report_is_refused(f: Fixture) -> None:
    f.receipt["verification"]["outcome"] = "failed"
    require(any("does not show a passing check" in p for p in f.resolve()), "a failed replay was accepted")


@with_fixture
def test_report_digest_mismatch_is_refused(f: Fixture) -> None:
    f.receipt["entry_digests"]["Challenge.lean"] = "0" * 64
    require(any("Challenge.lean digest" in p for p in f.resolve()),
            "a report of other Challenge bytes was accepted")


@with_fixture
def test_report_of_another_run_is_refused(f: Fixture) -> None:
    f.receipt["github"]["run_id"] = "2"
    require(any("run 2" in p for p in f.resolve()), "a report from another run was accepted")


@with_fixture
def test_every_declaration_needs_its_own_association(f: Fixture) -> None:
    del f.associations["declarations"]["Syn.third_result"]
    problems = f.resolve()
    require(any("Syn.third_result has no Comparator association" in p for p in problems)
            and any("cannot establish" in p for p in problems),
            "a result was marked compared with one declaration unassociated")


@with_fixture
def test_changed_corpus_statement_is_refused(f: Fixture) -> None:
    changed = LEAN_TEXT.replace("n + 0 = n := rfl", "n + 0 = n + 0 := rfl")
    write(f.corpus, "Syn/Results.lean", changed)
    f.corpus_commit = commit_all(f.corpus, "drift")
    f.receipt["github"]["sha"] = f.corpus_commit
    f.associations["corpus_commit"] = f.corpus_commit
    require(any("differs from the one the corpus compared" in p for p in f.resolve()),
            "a comparison of a different statement was accepted")


@with_fixture
def test_relation_notes_are_required_and_bound(f: Fixture) -> None:
    require(any("without an authored relation note" in p for p in f.resolve(require_relations=True)),
            "a stronger Lean statement without a relation note was accepted")
    note = f.relation_for("res:second")
    note["statement_key"] = "sha256:" + "0" * 64
    f.relations["rows"][f"{PAPER_ID}#res:second"] = note
    require(any("different statement" in p for p in f.resolve(require_relations=True)),
            "a relation note written against another statement was accepted")


@with_fixture
def test_failed_build_writes_nothing(f: Fixture) -> None:
    f.materialise()
    sentinel = "% an earlier, valid evidence file\n"
    write(f.root, f"paper/evidence/{PAPER_ID}.tex", sentinel)
    f.receipt["exit"] = 1
    f.materialise()
    status = pe.main(["build", "--root", str(f.root), "--corpus-repo", str(f.corpus),
                      "--record-commit", "d" * 40])
    require(status == 1, "a failing build exited successfully")
    require((f.root / "paper/evidence" / f"{PAPER_ID}.tex").read_text() == sentinel,
            "a failing build overwrote the previous evidence file")
    require(not (f.root / pe.EVIDENCE_MAP).exists(), "a failing build wrote the evidence map")


@with_fixture
def test_outputs_are_deterministic_and_checkable(f: Fixture) -> None:
    f.relations["rows"][f"{PAPER_ID}#res:second"] = f.relation_for("res:second")
    f.materialise()
    args = ["--root", str(f.root), "--corpus-repo", str(f.corpus)]
    require(pe.main(["build", *args, "--record-commit", "d" * 40]) == 0, "the sound build failed")
    first = {p: p.read_bytes() for p in sorted((f.root / "evidence").rglob("*.md"))}
    require(pe.main(["build", *args, "--record-commit", "d" * 40]) == 0, "a rebuild failed")
    second = {p: p.read_bytes() for p in sorted((f.root / "evidence").rglob("*.md"))}
    require(first == second, "two builds from the same inputs differ")
    sidecar = (f.root / "paper/evidence" / f"{PAPER_ID}.tex").read_text()
    require("\\DeclareResultEvidence{res:first}{Lean}" in sidecar and "Results.lean\\#L4" in sidecar,
            "a one-declaration result does not link its declaration directly")
    require(f"{PAPER_ID}.md\\#res-second}}" in sidecar,
            "a two-declaration result does not open its record section")
    record = (f.root / "evidence" / f"{PAPER_ID}.md").read_text()
    require("Comparator: passed" in record and "receipt-E1.json" in record, "the record omits the check")


@with_fixture
def test_partial_aux_keeps_other_papers_numbered(f: Fixture) -> None:
    f.materialise()
    prior = {"papers": [{"results": [
        {"id": f"{PAPER_ID}#res:first", "number": "3.4", "page": "8",
         "statement_sha256": f.ledger["rows"][0]["statement_sha256"],
         "statement_markdown": "Prior reference to Equation (2)", "lean": {}},
        {"id": f"{PAPER_ID}#res:second", "number": "3.5", "page": "9",
         "statement_sha256": f.ledger["rows"][1]["statement_sha256"],
         "statement_markdown": "Prior reference to Problem 1.3", "lean": {}},
    ]}]}
    missing_aux = f.root / "missing-aux"
    problems = pe.Problems()
    evidence = pe.resolve(f.root, pe.Repo(f.corpus), missing_aux, prior, problems,
                          require_relations=False, aux_papers=set())
    require(not problems.items, f"an unselected paper required aux: {problems.items}")
    results = evidence["papers"][0]["results"]
    require([(r["number"], r["page"]) for r in results] == [("3.4", "8"), ("3.5", "9")],
            "partial aux lost the prior printed coordinates")
    require([r["statement_markdown"] for r in results] ==
            ["Prior reference to Equation (2)", "Prior reference to Problem 1.3"],
            "partial aux rewrote untouched rendered references")
    checked = pe.Problems()
    unchanged = pe.resolve(f.root, pe.Repo(f.corpus), None, prior, checked,
                           require_relations=False)
    require(not checked.items and
            [r["statement_markdown"] for r in unchanged["papers"][0]["results"]] ==
            ["Prior reference to Equation (2)", "Prior reference to Problem 1.3"],
            "a no-aux check rewrote previously validated references")
    required = pe.Problems()
    pe.resolve(f.root, pe.Repo(f.corpus), missing_aux, prior, required,
               require_relations=False, aux_papers={PAPER_ID})
    require(any("no " in p and ".aux" in p for p in required.items),
            "a selected paper with missing aux was accepted")


@with_fixture
def test_no_aux_refreshes_changed_explanations(f: Fixture) -> None:
    f.materialise()
    row = f.ledger["rows"][0]
    row["lean"]["scope"] = "Updated scope"
    row["lean"]["reason"] = "Updated reason"
    write(f.root, pe.LEDGER, json.dumps(f.ledger))
    prior = {"papers": [{"results": [{
        "id": row["id"], "label": row["label"], "number": "3.4", "page": "8",
        "statement_sha256": row["statement_sha256"],
        "statement_markdown": "Prior numbered statement",
        "lean": {"scope": "Old scope", "scope_markdown": "Old scope rendered",
                 "reason": "Old reason", "reason_markdown": "Old reason rendered"},
    }]}]}
    problems = pe.Problems()
    evidence = pe.resolve(f.root, pe.Repo(f.corpus), None, prior, problems,
                          require_relations=False)
    require(not problems.items, f"a changed explanation failed: {problems.items}")
    result = evidence["papers"][0]["results"][0]
    require(result["statement_markdown"] == "Prior numbered statement",
            "the unchanged statement lost its prior numbered rendering")
    require(result["lean"]["scope_markdown"] == "Updated scope" and
            result["lean"]["reason_markdown"] == "Updated reason",
            "changed scope or reason retained stale markdown")


@with_fixture
def test_paper_record_pin_override(f: Fixture) -> None:
    f.materialise()
    problems = pe.Problems()
    evidence = pe.resolve(f.root, pe.Repo(f.corpus), None, None, problems,
                          require_relations=False)
    require(not problems.items, f"the sound evidence failed: {problems.items}")
    files = pe.outputs(f.root, evidence, "d" * 40, {PAPER_ID: "e" * 40})
    sidecar = files[f"paper/evidence/{PAPER_ID}.tex"]
    require(f"/blob/{'e' * 40}/evidence/{PAPER_ID}.md" in sidecar,
            "the per-paper record pin did not reach the rendered links")
    require(f"/blob/{'d' * 40}/evidence/{PAPER_ID}.md" not in sidecar,
            "the default pin leaked into an overridden paper")


def test_statement_with_let_is_read_whole() -> None:
    text = ("theorem t (a : Nat) :\n    let C := a + 1\n    C = a + 1 ∧\n    letI := 0\n"
            "    True := by\n  exact ⟨rfl, trivial⟩\n")
    got = pe.lean_declaration(pe.LeanFile(text), "lean/T.lean", "t", allow_suffix=False)
    require(got.statement.rstrip().endswith("True"),
            f"a statement containing let was cut at the let's := : {got.statement!r}")


def test_quoted_references_use_the_paper_numbers() -> None:
    numbers = {"thm:a": ("4.2", "8"), "eq:b": ("3", "8")}
    md = ('By Theorem <a href="#thm:a" data-reference-type="ref" data-reference="thm:a">10</a> and '
          '<a href="#eq:b" data-reference-type="eqref" data-reference="eq:b">[eq:b]</a>, see [eq:b] '
          'and <a href="#thm:c" data-reference-type="ref" data-reference="thm:c">7</a>.')
    got = pe.renumber_references(md, numbers)
    require(got == 'By Theorem 4.2 and (3), see (3) and '
                   '<a href="#thm:c" data-reference-type="ref" data-reference="thm:c">7</a>.',
            f"quoted references were not renumbered from the paper: {got!r}")


SUPPORT_PARENT = """namespace Syn

def positive (n : Nat) : Prop := 0 < n

structure Parent where
  n : Nat
  required : positive n
end Syn
"""
SUPPORT_TEXT = """import Syn.Parent
namespace Syn
structure Support extends Parent where
  even : n % 2 = 0
end Syn
"""


def add_support(f: Fixture) -> dict:
    """Support has its own identity, separate from the selected proposition."""
    for root in (f.root, f.corpus):
        write(root, "Syn/Parent.lean", SUPPORT_PARENT)
        write(root, "Syn/Support.lean", SUPPORT_TEXT)
        write(root, "lean-toolchain", "leanprover/lean4:v4.29.1\n")
        write(root, "lake-manifest.json", json.dumps({"packages": [{"name": "mathlib", "rev": "c" * 40}]}))
        write(root, "lakefile.toml", 'name = "synthetic"\n[[lean_lib]]\nname = "Syn"\n')
    # The selected theorem is a conditional consumer, not an existence theorem.
    lean = "import Syn.Support\n" + LEAN_TEXT.replace("first_result : True", "first_result (s : Support) : True")
    challenge = "import Syn.Support\n" + CHALLENGE.replace("first_result : True", "first_result (s : Support) : True")
    solution = "import Syn.Support\n" + SOLUTION.replace(
        "first_result : True := _root_.Syn.first_result",
        "first_result (s : Support) : True := _root_.Syn.first_result s")
    write(f.root, LEAN_FILE, lean)
    write(f.corpus, "Syn/Results.lean", lean)
    write(f.corpus, "PalomarCorpus/E1/Challenge.lean", challenge)
    f.receipt["entry_digests"]["Challenge.lean"] = sha(challenge)
    write(f.corpus, "Solutions/PalomarCorpus/E1.lean", solution)
    f.receipt["solution"]["files"]["Solutions/PalomarCorpus/E1.lean"] = sha(solution)
    f.pin = commit_all(f.root, "support source")
    f.corpus_commit = commit_all(f.corpus, "support environment")
    f.receipt["github"]["sha"] = f.corpus_commit
    f.associations["corpus_commit"] = f.corpus_commit
    declaration = pe.lean_declaration(pe.LeanFile(SUPPORT_TEXT), "Syn/Support.lean", "Syn.Support", allow_suffix=False)
    identity = pe.SourceSupport(pe.Repo(f.root), f.pin).identity(declaration)
    binding = {"schema": pe.SUPPORT_SCHEMA, "role": "support_only", "identity": identity,
               "consumer": "Syn.first_result", "entry": "E1", "challenge": "Syn.first_result"}
    f.associations["support_declarations"] = {"Syn.Support": binding}
    f.ledger["rows"][0]["lean"]["supporting_declarations"] = [
        {"name": "Syn.Support", "file": "Syn/Support.lean", "consumer": "Syn.first_result"}]
    return identity


@with_fixture
def test_complete_support_chain_and_unrelated_module(f: Fixture) -> None:
    identity = add_support(f)
    require(f.resolve() == [], f"same-source support failed: {f.resolve()}")
    write(f.root, "Syn/Unrelated.lean", "theorem unrelated : True := trivial\n")
    f.pin = commit_all(f.root, "unrelated new theorem")
    require(f.resolve() == [], f"an unrelated theorem invalidated unchanged support: {f.resolve()}")
    declaration = pe.lean_declaration(pe.LeanFile(SUPPORT_TEXT), "Syn/Support.lean", "Syn.Support", allow_suffix=False)
    require(pe.SourceSupport(pe.Repo(f.root), f.pin).identity(declaration) == identity,
            "support identity depends on unrelated source or repository commit")


@with_fixture
def test_structure_field_mutation_invalidates_support(f: Fixture) -> None:
    add_support(f)
    write(f.root, "Syn/Support.lean", SUPPORT_TEXT.replace("n % 2 = 0", "n % 2 = 1"))
    f.pin = commit_all(f.root, "mutate field with unchanged header")
    require(any("support identity" in p for p in f.resolve()), "a changed field inherited old support acceptance")


@with_fixture
def test_inherited_requirement_mutation_invalidates_support(f: Fixture) -> None:
    add_support(f)
    write(f.root, "Syn/Parent.lean", SUPPORT_PARENT.replace("required : positive n", "required : ¬ positive n"))
    f.pin = commit_all(f.root, "mutate inherited requirement")
    require(any("support identity" in p for p in f.resolve()), "an inherited field inherited old support acceptance")


@with_fixture
def test_referenced_definition_mutation_invalidates_support(f: Fixture) -> None:
    add_support(f)
    write(f.root, "Syn/Parent.lean", SUPPORT_PARENT.replace("0 < n", "0 ≤ n"))
    f.pin = commit_all(f.root, "mutate referenced definition")
    require(any("support identity" in p for p in f.resolve()), "a referenced definition inherited old support acceptance")


@with_fixture
def test_support_does_not_witness_existence(f: Fixture) -> None:
    add_support(f)
    f.associations["support_declarations"]["Syn.Support"]["role"] = "existence_witness"
    require(any("cannot witness existence" in p for p in f.resolve()), "support metadata became an existence proof")
    f.associations["support_declarations"]["Syn.Support"]["role"] = "support_only"
    f.ledger["rows"][0]["lean"]["declarations"].append({"name": "Syn.Support", "file": "Syn/Support.lean"})
    f.associations["declarations"]["Syn.Support"] = dict(f.associations["declarations"]["Syn.first_result"])
    require(any("conditional consumer cannot witness" in p for p in f.resolve()),
            "a selected consumer discharged a required structure/existence declaration")


@with_fixture
def test_support_rejects_unrelated_successful_receipt(f: Fixture) -> None:
    add_support(f)
    f.associations["support_declarations"]["Syn.Support"]["challenge"] = "Syn.second_result"
    require(any("exact selected consumer" in p for p in f.resolve()),
            "an unrelated successful proposition in the same passing receipt was accepted")


@with_fixture
def test_support_requires_solution_dependency(f: Fixture) -> None:
    add_support(f)
    write(f.corpus, "Solutions/PalomarCorpus/E1.lean", "namespace Syn\ntheorem first_result : True := trivial\nend Syn\n")
    f.receipt["solution"]["files"]["Solutions/PalomarCorpus/E1.lean"] = sha(
        "namespace Syn\ntheorem first_result : True := trivial\nend Syn\n")
    f.ledger["rows"][1]["comparator"]["status"] = "pending"
    f.corpus_commit = commit_all(f.corpus, "remove checked support import")
    f.receipt["github"]["sha"] = f.corpus_commit
    f.associations["corpus_commit"] = f.corpus_commit
    require(any("outside the checked Solution import closure" in p for p in f.resolve()),
            "an unrelated imported environment became checked support")


@with_fixture
def test_support_rejects_dependency_version_transport(f: Fixture) -> None:
    add_support(f)
    write(f.corpus, "lean-toolchain", "leanprover/lean4:v4.30.0\n")
    f.corpus_commit = commit_all(f.corpus, "different compiler")
    f.receipt["github"]["sha"] = f.corpus_commit
    f.associations["corpus_commit"] = f.corpus_commit
    require(any("checked transport required" in p for p in f.resolve()),
            "unchanged source silently proved cross-toolchain equivalence")


@with_fixture
def test_legacy_support_hash_cannot_authorise_relation(f: Fixture) -> None:
    add_support(f)
    row = f.ledger["rows"][0]
    row["comparator"]["status"] = "pending"
    row["lean"].pop("supporting_declarations")
    row["lean"]["status"] = "exact_or_stronger"
    row["lean"]["declarations"] = [{"name": "Syn.Support", "file": "Syn/Support.lean"}]
    note = f.relation_for("res:first")
    note["lean_statements"]["Syn.Support"] = sha("structure Support extends Parent")
    f.relations["rows"][row["id"]] = note
    require(any("different statement" in p for p in f.resolve(require_relations=True)),
            "a legacy header-only stamp silently became complete support authority")


@with_fixture
def test_complete_support_note_expires_on_imported_definition_change(f: Fixture) -> None:
    add_support(f)
    row = f.ledger["rows"][0]
    row["comparator"]["status"] = "pending"
    row["lean"].pop("supporting_declarations")
    row["lean"]["status"] = "exact_or_stronger"
    row["lean"]["declarations"] = [{"name": "Syn.Support", "file": "Syn/Support.lean"}]
    f.relations["rows"][row["id"]] = f.relation_for("res:first")
    f.relations["rows"][f.ledger["rows"][1]["id"]] = f.relation_for("res:second")
    require(not f.resolve(require_relations=True), "a fresh complete support relation note failed")
    write(f.root, "Syn/Parent.lean", SUPPORT_PARENT.replace("0 < n", "0 ≤ n"))
    f.pin = commit_all(f.root, "change inherited definition after reviewed note")
    require(any("different statement" in p for p in f.resolve(require_relations=True)),
            "relation review survived changed transitive support meaning")


@with_fixture
def test_malformed_support_environment_fails_closed(f: Fixture) -> None:
    add_support(f)
    write(f.root, "lake-manifest.json", "[]")
    f.pin = commit_all(f.root, "malformed manifest")
    require(any("package list" in p for p in f.resolve()), "malformed manifest was accepted or crashed")


def checkable_support_fixture(f: Fixture) -> None:
    add_support(f)
    f.relations["rows"][f.ledger["rows"][1]["id"]] = f.relation_for("res:second")
    f.materialise()
    require(pe.main(["build", "--root", str(f.root), "--corpus-repo", str(f.corpus)]) == 0,
            "supported fixture did not build")
    record_pin = commit_all(f.root, "evidence records")
    config = pe.load_json(f.root / pe.CONFIG)
    config["record_commit"] = record_pin
    write(f.root, pe.CONFIG, json.dumps(config))
    evidence = pe.load_json(f.root / pe.EVIDENCE_MAP)
    pe.write_atomically(f.root, pe.outputs(f.root, evidence, record_pin))
    require(pe.main(["check", "--root", str(f.root)]) == 0, "unchanged supported offline check failed")


@with_fixture
def test_offline_support_cannot_escape_ledger(f: Fixture) -> None:
    checkable_support_fixture(f)
    ledger = pe.load_json(f.root / pe.LEDGER)
    ledger["rows"][0]["lean"].pop("supporting_declarations")
    write(f.root, pe.LEDGER, json.dumps(ledger))
    errors = io.StringIO()
    with contextlib.redirect_stderr(errors):
        status = pe.main(["check", "--root", str(f.root)])
    require(status == 1 and "different supporting declarations" in errors.getvalue(),
            "offline support survived removal from its owning ledger")


@with_fixture
def test_offline_support_rejects_changed_association(f: Fixture) -> None:
    checkable_support_fixture(f)
    associations = pe.load_json(f.root / pe.ASSOCIATIONS)
    associations["support_declarations"]["Syn.Support"]["challenge"] = "Syn.second_result"
    write(f.root, pe.ASSOCIATIONS, json.dumps(associations))
    errors = io.StringIO()
    with contextlib.redirect_stderr(errors):
        status = pe.main(["check", "--root", str(f.root)])
    require(status == 1 and "exact accepted proposition consumer" in errors.getvalue(),
            "offline support survived an unrelated successful proposition association")


def test_support_identity_is_not_presentation_limited() -> None:
    text = "structure S where\n  n : Nat\n\n  tail : " + "True ∧ " * 45 + "True\n"
    before = pe.lean_declaration(pe.LeanFile(text), "S.lean", "S", allow_suffix=False)
    after = pe.lean_declaration(pe.LeanFile(text.replace("tail :", "changed :")), "S.lean", "S", allow_suffix=False)
    require(before.normalised != after.normalised,
            "a field beyond a blank line or display limit was absent from identity")


def main() -> int:
    tests = [
        test_complete_support_chain_and_unrelated_module,
        test_structure_field_mutation_invalidates_support,
        test_inherited_requirement_mutation_invalidates_support,
        test_referenced_definition_mutation_invalidates_support,
        test_support_does_not_witness_existence,
        test_support_rejects_unrelated_successful_receipt,
        test_support_requires_solution_dependency,
        test_support_rejects_dependency_version_transport,
        test_legacy_support_hash_cannot_authorise_relation,
        test_complete_support_note_expires_on_imported_definition_change,
        test_malformed_support_environment_fails_closed,
        test_offline_support_cannot_escape_ledger,
        test_offline_support_rejects_changed_association,
        test_support_identity_is_not_presentation_limited,
        test_sound_fixture_resolves,
        test_unlabelled_result_is_refused,
        test_declaration_missing_at_the_pin_is_refused,
        test_failed_replay_report_is_refused,
        test_report_digest_mismatch_is_refused,
        test_report_of_another_run_is_refused,
        test_every_declaration_needs_its_own_association,
        test_changed_corpus_statement_is_refused,
        test_relation_notes_are_required_and_bound,
        test_failed_build_writes_nothing,
        test_outputs_are_deterministic_and_checkable,
        test_partial_aux_keeps_other_papers_numbered,
        test_no_aux_refreshes_changed_explanations,
        test_paper_record_pin_override,
        test_statement_with_let_is_read_whole,
        test_quoted_references_use_the_paper_numbers,
    ]
    for test in tests:
        test()
    print(f"test_paper_evidence: {len(tests)} fixtures; each way the evidence behind a mark can be "
          "wrong is refused, and a refused build writes nothing")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
