#!/usr/bin/env python3
"""Check reciprocal, named-destination links across the public paper family."""

from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"

CORE = {
    "claim-faithful-publication-systems-paper.pdf": (
        "systems/claim-faithful-publication-systems-paper.tex",
        {"systems-lifecycle", "systems-public", "systems-trust", "systems-scaling"},
    ),
    "cold-clone-to-proof-receipt.pdf": (
        "systems/cold-clone-to-proof-receipt.tex",
        {"cold-clone-problem", "cold-clone-authority", "cold-clone-limits"},
    ),
    "open-source-mathematics-strategy.pdf": (
        "systems/open-source-mathematics-strategy.tex",
        {
            "strategy-protocol",
            "strategy-credit",
            "strategy-security",
            "strategy-limits",
            "strategy-entry-routes",
        },
    ),
}

NOTES = (
    "68/erdos-68-factorial-denominator-irrationality.tex",
    "243/erdos-243-reciprocal-tail-rigidity.tex",
    "249/erdos-249-binary-totient-series.tex",
    "251/erdos-251-prime-gap-dyadic-series.tex",
    "257/erdos-257-mersenne-support-subseries.tex",
    "269/erdos-269-three-prime-running-lcm.tex",
    "1041/erdos-1041-lemniscate-newton-flow.tex",
    "1049/erdos-1049-rational-base-lambert.tex",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def source(name: str) -> str:
    return (PAPER / name).read_text(encoding="utf-8")


def links(text: str) -> set[tuple[str, str]]:
    return set(
        re.findall(
            r"\\papersectionlink\{([^}]+\.pdf)\}%?\s*\{([^}]+)\}",
            text,
        )
    )


def check_pinned_repolinks(sources: dict[str, str], *, git_root: Path = ROOT) -> None:
    """Resolve every system-paper repo link against its exact public Git tree."""
    trees: dict[str, set[str]] = {}
    for tex, text in sources.items():
        paths = set(re.findall(r"\\repolink\{([^{}]+)\}", text))
        if not paths:
            continue
        pins = set(re.findall(r"\\repobase/blob/([0-9a-f]{40})/#1", text))
        require(len(pins) == 1, f"{tex}: \\repolink needs one full pinned commit")
        pin = next(iter(pins))
        if pin not in trees:
            commit = subprocess.run(
                ["git", "cat-file", "-t", pin],
                cwd=git_root,
                capture_output=True,
                text=True,
                check=False,
            )
            require(
                commit.returncode == 0 and commit.stdout.strip() == "commit",
                f"{tex}: pinned public commit {pin} is unavailable in local Git history "
                f"(fetch the public history before checking): {commit.stderr.strip()}",
            )
            tree = subprocess.run(
                ["git", "ls-tree", "-r", "-z", "--name-only", pin],
                cwd=git_root,
                capture_output=True,
                check=False,
            )
            require(
                tree.returncode == 0,
                f"{tex}: cannot read pinned public commit {pin} tree: "
                f"{tree.stderr.decode(errors='replace').strip()}",
            )
            trees[pin] = set(tree.stdout.decode("utf-8", errors="surrogateescape").split("\0"))
        missing = sorted(paths - trees[pin])
        require(
            not missing,
            f"{tex}: \\repolink paths absent from pinned public commit {pin}: {missing}",
        )


def main() -> int:
    style = source("paper-house-style.sty")
    require("#1\\#nameddest=#2" in style, "paper link macro is not destination-based")

    target_owner: dict[tuple[str, str], str] = {}
    for pdf, (tex, expected) in CORE.items():
        text = source(tex)
        actual = set(re.findall(r"\\papersectiontarget\{([^}]+)\}", text))
        require(expected <= actual, f"{tex} omits targets {sorted(expected - actual)}")
        require("14 September 2026" in text, f"{tex} omits the dated prototype boundary")
        require("external" in text.lower(), f"{tex} omits the external-use boundary")
        for target in actual:
            key = (pdf, target)
            require(key not in target_owner, f"duplicate destination owner for {key}")
            target_owner[key] = tex

    system_sources = {
        path.relative_to(PAPER).as_posix(): path.read_text(encoding="utf-8")
        for path in sorted((PAPER / "systems").glob("*.tex"))
    }
    check_pinned_repolinks(system_sources)

    combined = "\n".join(source(tex) for tex, _ in CORE.values())
    core_links = links(combined)
    for pdf in CORE:
        outbound = {link for link in core_links if link[0] == pdf}
        require(outbound, f"no core paper links to {pdf}")

    # The problem papers carry mathematics and their own evidence marks; the systems
    # papers are no longer advertised from them (the companion-context paragraph was
    # retired with the generated notes).
    preamble = source("problem-note-preamble.tex")
    note_links = links(preamble)
    require("\\companionpapercontext" not in preamble,
            "the retired companion-context paragraph is back in the problem-note preamble")

    for note in NOTES:
        text = source(note)
        require("\\input{problem-note-preamble}" in text, f"{note} bypasses the shared preamble")
        require("\\companionpapercontext" not in text,
                f"{note} prints the retired companion-context paragraph")

    for link in core_links | note_links:
        require(link in target_owner, f"cross-paper link has no declared destination: {link}")

    all_sources = combined + "\n" + preamble
    require("#page=" not in all_sources, "cross-paper navigation uses fragile page numbers")
    print("paper crosslinks: reciprocal core links, eight notes free of system context, named targets, and pinned repo paths PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
