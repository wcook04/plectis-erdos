#!/usr/bin/env python3
"""Contract tests for ``residual_evaluator.py``.

Every check here pins a defect that was live during development.  Four of them
pin the difference between a harness that decides something and a harness that
merely fails to complain:

* a manifest cannot author the verdict it is meant to be judged against;
* restatement is tested per residual and in both directions, so a legitimate
  decomposition is not convicted merely because its parts follow from its
  target;
* nothing proved is an abstention, never progress;
* each tactic attempt is a declaration of its own, because ``first`` does not
  recover past a nested elaboration error and the alternatives below the first
  risky one are never tried.
"""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import json
from pathlib import Path

import residual_evaluator as ev

HERE = Path(__file__).resolve().parent.parent
MANIFEST = HERE.parent / "research/experiments/residual-progress/manifest.json"


def _sketch(residuals: list[str], expect: str | None = None) -> ev.Sketch:
    return ev.Sketch(
        sketch_id="S",
        target="T",
        residuals=residuals,
        expect=expect,
        note="",
    )


def _result(kind: str, subject: str, proved: bool) -> ev.ProbeResult:
    return ev.ProbeResult(
        name=f"probe_{kind}__{subject}",
        kind=kind,
        subject=subject,
        statement="_",
        proved=proved,
        detail="",
        axioms=["propext"] if proved else [],
    )


def check_manifest_may_not_author_a_verdict(tmp: Path) -> None:
    """A bench row declares an expectation; Lean decides the verdict."""
    path = tmp / "authored.json"
    path.write_text(
        json.dumps(
            {
                "module": "M",
                "sketches": [
                    {
                        "sketch_id": "X",
                        "target": "T",
                        "residuals": ["R"],
                        "verdict": ev.ENDPOINT_EQUIVALENT,
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    try:
        ev.load_manifest(path)
    except ev.AuthoredVerdictError:
        return
    raise AssertionError("an authored verdict must be refused")


def check_expectation_must_be_a_known_verdict(tmp: Path) -> None:
    path = tmp / "bogus.json"
    path.write_text(
        json.dumps(
            {
                "module": "M",
                "sketches": [
                    {
                        "sketch_id": "X",
                        "target": "T",
                        "residuals": ["R"],
                        "expect": "definitely_fine",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    try:
        ev.load_manifest(path)
    except ValueError:
        return
    raise AssertionError("an unknown expectation must be refused")


def check_laundering_needs_both_directions() -> None:
    """``T -> R`` alone is not restatement; it holds for honest reductions."""
    sketch = _sketch(["R"])
    one_way = ev.classify(
        sketch,
        [
            _result("soundness", "S", True),
            _result("p2r0", "S", True),
            _result("r2p0", "S", False),
            _result("refutation", "S", False),
        ],
    )
    assert one_way["verdict"] != ev.ENDPOINT_EQUIVALENT, one_way

    both_ways = ev.classify(
        sketch,
        [
            _result("soundness", "S", True),
            _result("p2r0", "S", True),
            _result("r2p0", "S", True),
            _result("refutation", "S", False),
        ],
    )
    assert both_ways["verdict"] == ev.ENDPOINT_EQUIVALENT, both_ways


def check_an_implied_decomposition_is_not_laundering() -> None:
    """A target implies every part of a correct split.  That is not renaming.

    Testing the residual conjunction instead convicts base-plus-step induction,
    which is the opposite of the failure being detected.
    """
    sketch = _sketch(["base", "step"])
    verdict = ev.classify(
        sketch,
        [
            _result("soundness", "S", True),
            _result("p2r0", "S", True),
            _result("r2p0", "S", False),
            _result("p2r1", "S", True),
            _result("r2p1", "S", False),
            _result("refutation", "S", False),
        ],
    )
    assert verdict["verdict"] == ev.STRICT_DECOMPOSITION_CANDIDATE, verdict


def check_refutation_outranks_laundering() -> None:
    sketch = _sketch(["R"])
    verdict = ev.classify(
        sketch,
        [
            _result("soundness", "S", True),
            _result("p2r0", "S", True),
            _result("r2p0", "S", True),
            _result("refutation", "S", True),
        ],
    )
    assert verdict["verdict"] == ev.RESIDUAL_REFUTED, verdict


def check_nothing_proved_is_an_abstention() -> None:
    sketch = _sketch(["R"])
    verdict = ev.classify(
        sketch,
        [
            _result("soundness", "S", False),
            _result("p2r0", "S", False),
            _result("r2p0", "S", False),
            _result("refutation", "S", False),
        ],
    )
    assert verdict["verdict"] == ev.UNKNOWN_RELATION, verdict


def check_no_tactic_contains_a_nested_by_block() -> None:
    """``exact absurd h (by simp)`` elaborates eagerly.

    When the inner block fails, the enclosing declaration takes ``sorryAx``
    while ``first`` treats the alternative as having succeeded, so no later
    tactic runs.
    """
    for tactic in ev.TACTIC_LADDER:
        assert "by " not in tactic, tactic
        assert not tactic.strip().startswith("first"), tactic


def check_each_tactic_gets_its_own_declaration() -> None:
    probes = ev.build_probes([_sketch(["R"])], cross=False)
    text = ev.render_probe_file("M", probes, "N")
    assert "first" not in text
    theorems = [ln for ln in text.splitlines() if ln.startswith("theorem ")]
    expected = len(probes) * len(ev.TACTIC_LADDER)
    assert len(theorems) == expected, (len(theorems), expected)


def check_axiom_report_follows_each_theorem() -> None:
    """Lean stops emitting diagnostics past an error threshold.

    A probe file is mostly failed attempts by construction, so reports batched
    at the end of the file never print at all.
    """
    probes = ev.build_probes([_sketch(["R"])], cross=False)
    lines = [
        ln
        for ln in ev.render_probe_file("M", probes, "N").splitlines()
        if ln.strip()
    ]
    for index, line in enumerate(lines):
        if line.startswith("theorem "):
            window = lines[index + 1 : index + 4]
            assert any("#print axioms" in ln for ln in window), lines[index:][:4]


def check_probes_cover_both_directions_per_residual() -> None:
    probes = ev.build_probes([_sketch(["R1", "R2"])], cross=False)
    kinds = {probe.kind for probe in probes}
    for index in (0, 1):
        assert f"p2r{index}" in kinds, kinds
        assert f"r2p{index}" in kinds, kinds
    assert "soundness" in kinds and "refutation" in kinds, kinds


def check_controls_are_present_and_discriminating() -> None:
    """A harness that cannot fail one control proves nothing with the rest."""
    names = {name for name, _statement, _must in ev.CONTROL_PROBES}
    assert any("control__true" in name for name in names), names
    assert any("control__false" in name for name in names), names
    musts = {must for _name, _statement, must in ev.CONTROL_PROBES}
    assert musts == {True, False}, musts


def check_one_lean_file_per_probe() -> None:
    """Batching probes into one file loses the later ones.

    Lean stops emitting diagnostics once a file accumulates enough errors, and
    a probe file is mostly failed attempts by construction.  ``run_probes``
    must render each probe on its own, and must put the controls in front of
    the real work rather than after it.
    """
    import inspect

    source = inspect.getsource(ev.run_probes)
    assert "render_probe_file(module, [pr], namespace)" in source, source[:400]
    assert "control_probes + probes" in source, source[:400]


def check_vetoes_are_exactly_the_two_kernel_backed_verdicts() -> None:
    """``strict_decomposition_candidate`` is a pass, not a veto.

    ``unknown_relation`` is an abstention.  Neither may be treated as a
    rejection, and no verdict outside ``VERDICTS`` may exist.
    """
    assert ev.VETOES == frozenset(
        {ev.ENDPOINT_EQUIVALENT, ev.RESIDUAL_REFUTED}
    ), ev.VETOES
    assert ev.STRICT_DECOMPOSITION_CANDIDATE not in ev.VETOES
    assert ev.UNKNOWN_RELATION not in ev.VETOES
    assert set(ev.VETOES) <= set(ev.VERDICTS)


def check_shipped_manifest_carries_negative_controls() -> None:
    """The controls exist, and neither is expected to be vetoed.

    Their job is to catch over-firing.  ``F_strengthening`` is a productive
    generalisation and ``H_incomparable`` is an unrelated true residual; a
    veto on either would be the expensive error, so the expectation is pinned
    to be outside ``VETOES`` rather than to one particular non-veto verdict.
    """
    _module, sketches = ev.load_manifest(MANIFEST)
    by_id = {sketch.sketch_id: sketch for sketch in sketches}
    for control in ("F_strengthening", "H_incomparable"):
        assert control in by_id, sorted(by_id)
        expect = by_id[control].expect
        assert expect is not None, by_id[control]
        assert expect not in ev.VETOES, by_id[control]

    laundered = [s for s in sketches if s.expect == ev.ENDPOINT_EQUIVALENT]
    assert laundered, "the bench must carry restatement specimens too"


def _two_sketches(binders_a: str = "", binders_b: str = "") -> list[ev.Sketch]:
    return [
        ev.Sketch(sketch_id="Deep", target="T", residuals=["R1"], binders=binders_a),
        ev.Sketch(sketch_id="Shallow", target="T", residuals=["R2"], binders=binders_b),
    ]


def check_probe_names_are_lean_identifiers() -> None:
    """A probe name becomes a declaration name.

    Dominance probes were named `probe_dominance__A>B`, which Lean cannot parse,
    so a run with cross-sketch dominance could never report an edge.
    """
    probes = ev.build_probes(_two_sketches(), cross=True)
    dominance = [p for p in probes if p.kind == "dominance"]
    assert len(dominance) == 2, [p.name for p in dominance]
    for probe in probes:
        assert ev.LEAN_NAME.match(probe.name), probe.name
    assert {p.subject for p in dominance} == {"Deep>Shallow", "Shallow>Deep"}


def check_a_sketch_id_that_is_not_an_identifier_is_refused() -> None:
    try:
        ev.build_probes([ev.Sketch(sketch_id="a-b", target="T", residuals=["R"])], cross=False)
    except ValueError as error:
        assert "not a Lean identifier" in str(error), error
    else:
        raise AssertionError("a probe name with '-' was accepted")


def check_binders_close_every_probe() -> None:
    """A sketch with binders is decided pointwise: every probe is stated under them."""
    sketch = ev.Sketch(sketch_id="Cut", target="G n", residuals=["P n ∧ Q n"],
                       binders="(n : ℕ) (hn : 3 ≤ n)", unfold=["P", "Q", "G"])
    probes = ev.build_probes([sketch], cross=False)
    by_kind = {p.kind: p for p in probes}
    assert by_kind["soundness"].statement == "∀ (n : ℕ) (hn : 3 ≤ n), (P n ∧ Q n) → (G n)"
    assert by_kind["soundness"].intros == ["n", "hn"]
    assert by_kind["refutation"].statement == "¬ (∀ (n : ℕ) (hn : 3 ≤ n), P n ∧ Q n)"
    assert by_kind["refutation"].intros == []
    text = ev.render_probe_file("M", [by_kind["soundness"]], "N")
    assert "  unfold G P Q\n  intro n hn\n" in text, text[:600]


def check_dominance_compares_only_under_the_same_binders() -> None:
    same = ev.build_probes(_two_sketches("(n : ℕ)", "(n : ℕ)"), cross=True)
    assert [p.statement for p in same if p.kind == "dominance"] == [
        "∀ (n : ℕ), (R1) → (R2)", "∀ (n : ℕ), (R2) → (R1)"]
    different = ev.build_probes(_two_sketches("(n : ℕ)", "(m : ℕ)"), cross=True)
    assert not [p for p in different if p.kind == "dominance"]


def check_emitted_run_is_read_back_from_its_logs(tmp: Path) -> None:
    """An emitted run decides from its logs, and refuses when no control log came back."""
    sketches = [ev.Sketch(sketch_id="S", target="T", residuals=["R"])]
    probes = ev.build_probes(sketches, cross=False)
    out = tmp / "emitted"
    written = ev.emit_probe_files("M", "N", probes, out)
    assert [p.stem for p in written[:2]] == ["probe_control__true", "probe_control__false"]
    assert len(written) == 2 + len(probes)
    logs = tmp / "logs"
    try:
        ev.results_from_logs(probes, logs)
    except ev.HarnessNotLiveError:
        pass
    else:
        raise AssertionError("a run with no logs was decided")
    logs.mkdir()
    (logs / "probe_control__true.log").write_text(
        "'probe_control__true__t0' does not depend on any axioms\n")
    (logs / "probe_control__false.log").write_text("error: unsolved goals\n")
    (logs / "probe_soundness__S.log").write_text(
        "'probe_soundness__S__t2' depends on axioms: [propext]\n")
    results = {r.kind: r for r in ev.results_from_logs(probes, logs)}
    assert results["soundness"].proved and not results["refutation"].proved
    assert ev.classify(sketches[0], list(results.values()))["verdict"] == ev.STRICT_DECOMPOSITION_CANDIDATE


def main() -> int:
    import tempfile

    with tempfile.TemporaryDirectory() as raw:
        tmp = Path(raw)
        checks = [
            lambda: check_manifest_may_not_author_a_verdict(tmp),
            lambda: check_expectation_must_be_a_known_verdict(tmp),
            check_laundering_needs_both_directions,
            check_an_implied_decomposition_is_not_laundering,
            check_refutation_outranks_laundering,
            check_nothing_proved_is_an_abstention,
            check_no_tactic_contains_a_nested_by_block,
            check_each_tactic_gets_its_own_declaration,
            check_axiom_report_follows_each_theorem,
            check_probes_cover_both_directions_per_residual,
            check_controls_are_present_and_discriminating,
            check_one_lean_file_per_probe,
            check_vetoes_are_exactly_the_two_kernel_backed_verdicts,
            check_shipped_manifest_carries_negative_controls,
            check_probe_names_are_lean_identifiers,
            check_a_sketch_id_that_is_not_an_identifier_is_refused,
            check_binders_close_every_probe,
            check_dominance_compares_only_under_the_same_binders,
            lambda: check_emitted_run_is_read_back_from_its_logs(tmp),
        ]
        for check in checks:
            check()

    print(
        json.dumps(
            {
                "schema": "residual-evaluator-test-receipt/1",
                "passed": True,
                "checks": len(checks),
                "budget_id": ev.BUDGET_ID,
                "verdicts": list(ev.VERDICTS),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
