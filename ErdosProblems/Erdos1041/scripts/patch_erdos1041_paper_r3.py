#!/usr/bin/env python3
"""Surgical edits to the live #1041 short note for the 2026-09-07 Type B
revision assimilation. Replacement bodies are authored from live Erdos1041
notes (TiedMinimumTwoRootWindow, DiskFamilyCriticalValueSeparation,
GenericSufficiencyClosure, CollectiveRadialWindowBound). This is not Type B's
02_short_note_revised.tex.
"""
from __future__ import annotations

from pathlib import Path

PAPER = (
    Path(__file__).resolve().parents[2]
    / "papers"
    / "erdos-1041-lemniscate-newton-flow.tex"
)


def sub(text: str, old: str, new: str, label: str) -> str:
    if old not in text:
        raise SystemExit(f"anchor missing: {label}")
    if text.count(old) != 1:
        raise SystemExit(f"anchor not unique ({text.count(old)}): {label}")
    return text.replace(old, new, 1)


def main() -> int:
    text = PAPER.read_text()

    text = sub(
        text,
        r"\date{6 September 2026}",
        r"\date{7 September 2026}",
        "date",
    )

    hist_start = "Two recent manuscripts are relevant."
    hist_end = (
        "The object we work with is not the lemniscate directly but the flow that\n"
        "foliates it.\n\n"
    )
    i0 = text.find(hist_start)
    i1 = text.find(hist_end)
    if i0 < 0 or i1 < 0 or i1 < i0:
        raise SystemExit("history slice anchors missing")
    history = text[i0:i1]
    text = (
        text[:i0]
        + "Source pins and withdrawn-manuscript notes follow the glance table.\n\n"
        + text[i1 + len(hist_end) :]
    )

    insert_at = "\\section{An unconditional all-degree constant-factor path theorem}"
    if insert_at not in text:
        raise SystemExit("constant-factor section missing")
    sources = (
        "\\subsection*{Sources and adjacent results}\n"
        "\\label{sec:1041-sources}\n\n"
        + history
        + "Pendyala's Theorem~1 is a directly comparable degree-four result; "
        "it is not claimed unique in the literature.\n\n"
    )
    text = sub(text, insert_at, sources + insert_at, "move-history")

    text = sub(
        text,
        (
            "At a simple minimising critical point, enough separation from the next\n"
            "critical-value modulus gives a join inside the sharper level $K_\\mu$ and an\n"
            "explicit degree-dependent criterion for the target constant $2$.\n"
            "\\textsc{Ordinary exact proof.}"
        ),
        (
            "If the minimising critical point is unique and simple, or if a two-root\n"
            "component is imposed as a hypothesis, enough separation from the next\n"
            "critical-value modulus gives a join inside $K_\\mu$.  A mere simple\n"
            "minimum does not force that window: see the tied-minimum quartic.\n"
            "The registered disk-family theorem remains the two-sheeted parent regime.\n"
            "\\textsc{Ordinary exact proof; inference repaired 7 September 2026.}"
        ),
        "glance-spectrum",
    )

    text = sub(
        text,
        (
            "Suppose $f$ is squarefree\n"
            "and a critical point $c_*$ attaining $\\mu$ is simple.  Let $T_*>\\mu$ be the\n"
            "supremum of the levels for which the component born at $c_*$ contains exactly\n"
            "two roots.  Component root counts change only at critical-value moduli, so\n"
            "$T_*$ is at least the next distinct critical-value modulus."
        ),
        (
            "Suppose $f$ is squarefree and $c_*$ is the unique critical point attaining\n"
            "$\\mu$, and is simple.  Let $T_*>\\mu$ be the supremum of the levels for which\n"
            "the component born at $c_*$ contains exactly two roots.  Uniqueness, not\n"
            "simplicity, puts $T_*$ at least the next distinct critical-value modulus.\n"
            "The quartic $z^4-(4/15)z^3-(4/25)z^2+1/750$ has three simple critical points,\n"
            "tied minima of modulus $1/750$, all roots inside the disc, and first nontrivial\n"
            "component of degree three, so a simple minimum is not enough."
        ),
        "hub-hypothesis",
    )

    text = sub(
        text,
        "and $x_n^*$ decreases to $1$.",
        "and $x_n^*$ decreases to $\\coth 1$, not to $1$.",
        "xn-limit",
    )

    text = sub(
        text,
        (
            "The endpoints of any finite Newton-flow connection lie on the same oriented ray\n"
            "from $0$.  Consequently, if two critical values lie on distinct positive rays,\n"
            "no Newton-flow saddle connection joins the corresponding critical points."
        ),
        (
            "The values $f$ at the endpoints of any finite Newton-flow connection lie on\n"
            "the same oriented ray from $0$ in the value plane; the trajectory in $z$ need\n"
            "not be radial.  Consequently, if two critical values lie on distinct positive\n"
            "rays, no Newton-flow saddle connection joins the corresponding critical points."
        ),
        "newton-ray",
    )

    text = sub(
        text,
        "These two constructions meet at $r=r_*$.",
        (
            "These two constructions meet at $r=r_*$, where the outer chord attains\n"
            "$|f|=1$ at its midpoint: equality is closed containment, not the open\n"
            "lemniscate.  Open containment at and above the switch uses the inner chord\n"
            "after a radial contraction."
        ),
        "binomial-switch",
    )

    text = sub(
        text,
        (
            "and yields a uniform radius $S=4/3$ in every degree $n\\ge3$, at every real\n"
            "centre.  The limiting cutoff of the method is $\\coth1$."
        ),
        (
            "and yields a uniform radius $S=4/3$ in every degree $n\\ge3$, at every real\n"
            "centre.  The smallest degree-uniform radius certified by that coefficient at\n"
            "centre $a\\in[0,1]$ is\n"
            r"$S_\infty(a)=(A+\sqrt{A^2-4a(1-a)})/2$ with $A=\coth 1$; "
            "the endpoints recover $S_\\infty(0)=S_\\infty(1)=\\coth1$ already on file.\n"
            "An obstructing critical value may depend on the proposed centre."
        ),
        "s-infty",
    )

    text = sub(
        text,
        (
            "Critical-value genericity and compact barrier control are\n"
            "now elementary inputs; global component stability, strict slack stability and\n"
            "the transfer budget remain the open content."
        ),
        (
            "Critical-value genericity and compact barrier control are\n"
            "now elementary inputs.  The remaining metric question on the closed root-disc\n"
            "class $\\mathcal K_n$ is already registered: $\\Lambda$ is lower semicontinuous,\n"
            "$\\Lambda(z^n-1)=2$, so a dense generic proof of $\\Lambda(f)\\le 2$ yields the\n"
            "closed-class bound, and the open-disc problem is equivalent to that inequality.\n"
            "The canonical-arc minimum $\\min L_f(c)$ is sufficient for $\\Lambda\\le 2$, not\n"
            "equivalent to it.  Collar-preserving forward perturbation is not required."
        ),
        "lambda-ending",
    )

    text = sub(
        text,
        (
            "Erd\\H{o}s~\\#1041 remains open.  The source now publicly verifies the Newton\n"
            "kernel, finite ray avoidance, quantitative constant-translation root control,\n"
            "and the protected-set noncriticality inequality in the compact-barrier\n"
            "argument; ordinary proofs supply finite-exceptional coefficient genericity and\n"
            "the remaining root-disc and level-barrier controls.  Global component\n"
            "stability, the corrected planar decomposition and metric gluing remain the\n"
            "exact unresolved producers."
        ),
        (
            "Erd\\H{o}s~\\#1041 remains open.  The closed-class question is\n"
            "$\\Lambda(f)\\le\\Lambda(z^n-1)=2$ on $\\mathcal K_n$, by the registered\n"
            "lower-semicontinuity reduction; genericity is not an unresolved remaining\n"
            "producer.  The Newton kernel, finite ray avoidance, and compact-barrier\n"
            "controls remain as recorded.  A metric selector on admissible canonical arcs\n"
            "is sufficient, not equivalent, for that inequality."
        ),
        "final-open",
    )

    text = sub(
        text,
        (
            "Endpoints of a finite connection share\n"
            "one oriented ray, so distinct rays exclude a connection."
        ),
        (
            "Values at the endpoints of a finite connection share\n"
            "one oriented ray in the value plane, so distinct value-rays exclude a connection."
        ),
        "ledger-ray",
    )

    text = sub(
        text,
        (
            "Lean checks protected-set noncriticality.  Root-disc and level-barrier control\n"
            "remain ordinary arguments, while global component and strict-slack stability\n"
            "remain open."
        ),
        (
            "Lean checks protected-set noncriticality.  Root-disc and level-barrier control\n"
            "remain ordinary arguments.  Lower semicontinuity of $\\Lambda$ already reduces\n"
            "the closed class to a dense generic bound $\\Lambda\\le 2$; forward collar\n"
            "stability is not the remaining producer."
        ),
        "ledger-genericity",
    )

    PAPER.write_text(text)
    print("patched", PAPER)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
