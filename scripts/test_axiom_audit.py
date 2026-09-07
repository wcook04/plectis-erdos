#!/usr/bin/env python3
"""Self-contained coverage for axiom_audit.py's verdict logic.

The Lean call cannot run in a fixture, so the parsing and verdict half is pure
and is exercised here against captured kernel output shapes. The point under
test is that a deferral is never reported as a pass.
"""

from __future__ import annotations

from axiom_audit import classify_output


CLEAN = (
    "'ErdosProblems.Erdos243.foo' depends on axioms: [propext, Quot.sound]\n"
    "'ErdosProblems.Erdos243.bar' depends on axioms: [propext,\n"
    " Classical.choice,\n"
    " Quot.sound]\n"
)
DIRTY = (
    "'ErdosProblems.Erdos243.foo' depends on axioms: [propext, Quot.sound]\n"
    "'ErdosProblems.Erdos243.bad' depends on axioms: [propext, sorryAx]\n"
)
DEFERRAL_JSON = '{"automatic_future": {"blocked_on": {"job_refs": ["cf_abc"]}}}'


def main() -> int:
    # clean, including the multi-line axiom list the kernel emits when it wraps
    r = classify_output(CLEAN, 0, ["foo", "bar"])
    assert r["status"] == "clean", r
    assert all(row["permitted_only"] for row in r["audited"])
    assert r["not_reported"] == []
    assert r["violations"] == []

    # sorryAx is a violation, not a pass
    r = classify_output(DIRTY, 0, ["foo", "bad"])
    assert r["status"] == "violation", r
    assert [v["declaration"] for v in r["violations"]] == ["ErdosProblems.Erdos243.bad"]

    # a requested declaration the kernel never reported is incomplete, not clean
    r = classify_output(CLEAN, 0, ["foo", "bar", "never_printed"])
    assert r["status"] == "incomplete", r
    assert r["not_reported"] == ["never_printed"]

    # THE POINT: guard deferrals are never a pass, by exit code ...
    for code in (75, 241):
        r = classify_output("", code, ["foo"])
        assert r["status"] == "deferred", (code, r)
        assert r["audited"] == []
        assert r["not_reported"] == ["foo"]

    # ... and by payload shape even when the exit code is 0
    r = classify_output(DEFERRAL_JSON, 0, ["foo"])
    assert r["status"] == "deferred", r
    assert r["audited"] == []

    # genuine empty output with an ordinary failure code is not a deferral
    r = classify_output("some unrelated error", 1, ["foo"])
    assert r["status"] == "no_output", r

    print("test_axiom_audit: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
