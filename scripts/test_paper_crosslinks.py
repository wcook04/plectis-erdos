#!/usr/bin/env python3
"""Check reciprocal paper links and the publication/formal-source link binding.

Two identities travel through this corpus and must never be conflated.  The
formal source is one pinned Lean checkpoint: declaration permalinks, script
links and the source tree link resolve there, and they must, because a moved
line would otherwise silently retarget a printed coordinate.  The publication
is the assembled reader surface: the rendered PDFs, the claim register, the
README and the reading routes.  Those changed after the formal-source
checkpoint was pinned, so a link that resolves a PDF, a claim register or a
README at the formal-source commit or tag serves the pre-correction copy while
still resolving.  The second half of this file is the gate on that.
"""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
DOCS = ROOT / "docs"

CORE = {
    "claim-faithful-publication-systems-paper.pdf": (
        "claim-faithful-publication-systems-paper.tex",
        {"systems-lifecycle", "systems-public", "systems-trust", "systems-scaling"},
    ),
    "cold-clone-to-proof-receipt.pdf": (
        "cold-clone-to-proof-receipt.tex",
        {"cold-clone-problem", "cold-clone-authority", "cold-clone-limits"},
    ),
    "open-source-mathematics-strategy.pdf": (
        "open-source-mathematics-strategy.tex",
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
    "erdos-68-factorial-denominator-irrationality.tex",
    "erdos-243-reciprocal-tail-rigidity.tex",
    "erdos-249-binary-totient-series.tex",
    "erdos-251-prime-gap-dyadic-series.tex",
    "erdos-257-mersenne-support-subseries.tex",
    "erdos-269-three-prime-running-lcm.tex",
    "erdos-1041-lemniscate-newton-flow.tex",
    "erdos-1049-rational-base-lambert.tex",
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


# A link whose target is one of these is a publication surface: what it serves
# is the assembled reader artifact, which the release corrected after the
# formal-source checkpoint was pinned.
PUBLICATION_BASENAMES = frozenset(
    {
        "README.md",
        "HUMAN_ENTRY.md",
        "SCOPE.md",
        "METHODOLOGY.md",
        "ARCHITECTURE.md",
        "CONTRIBUTING.md",
        "CITATION.cff",
        "claims.json",
        "orientation.json",
        "ORIENTATION.md",
        "RESULTS.md",
        "corpus_descriptor.json",
        "publication_contract.json",
        "publication_entry_packet.json",
        "external_verification_packet.json",
        "PALOMAR_RESULT_SHOWCASE.json",
    }
)

# Surfaces scanned for the binding.  Everything here is either a rendered
# reader route or a machine surface a reader follows to one.
PUBLICATION_SURFACES = (
    "README.md",
    "HUMAN_ENTRY.md",
    "SCOPE.md",
    "docs/RESULTS.md",
    "docs/ORIENTATION.md",
    "docs/orientation.json",
    "docs/claims.json",
    "docs/corpus_descriptor.json",
    "docs/publication_contract.json",
    "docs/publication_entry_packet.json",
    "docs/external_verification_packet.json",
    "docs/PALOMAR_RESULT_SHOWCASE.json",
)

REPO_URL = re.compile(
    r"https?://github\.com/wcook04/plectis-erdos/"
    r"(?P<kind>blob|tree|raw)/(?P<ref>[^/\s}\)\"'\]]+)"
    r"(?P<path>/[^\s}\)\"'\]]*)?"
)


def release_identity() -> tuple[str, str, str]:
    """Return (publication tag, formal-source commit, formal-source tag)."""
    release = json.loads((DOCS / "claims.json").read_text(encoding="utf-8"))["release"]
    formal = release["formal_source"]
    return str(release["tag"]), str(formal["ref"]), str(formal["public_tag"])


def surface_class(path: str) -> str:
    """Classify what a repository-relative link target serves."""
    target = path.split("#", 1)[0].strip("/")
    if not target:
        return "repository_root"
    name = target.rsplit("/", 1)[-1]
    if name.endswith(".pdf") or name in PUBLICATION_BASENAMES:
        return "publication"
    if name.endswith(".lean"):
        return "declaration"
    return "source"


def expand_tex(text: str, commit: str) -> str:
    """Resolve the note macros so a printed link can be classified."""
    base = "https://github.com/wcook04/plectis-erdos/blob/" + commit
    tree = "https://github.com/wcook04/plectis-erdos/tree/" + commit
    return (
        text.replace("\\repobase", base)
        .replace("\\sourceurl", tree)
        .replace("\\commit", commit)
        .replace("\\#L", "#L")
    )


def publication_binding_violations(text: str, formal_refs: frozenset[str]) -> list[str]:
    """Links that serve a publication surface at the formal-source identity."""
    found: list[str] = []
    for match in REPO_URL.finditer(text):
        if match.group("ref") not in formal_refs:
            continue
        if surface_class(match.group("path") or "") == "publication":
            found.append(match.group(0))
    return sorted(set(found))


def check_publication_binding() -> None:
    publication_tag, commit, formal_tag = release_identity()
    formal_refs = frozenset({commit, commit[:12], formal_tag})
    base = "https://github.com/wcook04/plectis-erdos"

    # Fixtures.  A publication surface pinned to the formal-source identity is
    # rejected; a declaration, script or source-tree link at the same identity
    # is exactly what the notes must print and is accepted.
    fixtures = (
        (f"{base}/blob/{commit}/erdos-257-mersenne-support-subseries.pdf", True),
        (f"{base}/blob/{formal_tag}/erdos-257-mersenne-support-subseries.pdf", True),
        (f"{base}/blob/{commit}/docs/claims.json", True),
        (f"{base}/blob/{formal_tag}/README.md", True),
        (f"{base}/raw/{commit}/erdos249-257-main-paper.pdf", True),
        (f"{base}/blob/{commit}/ErdosProblems/Erdos257/Support.lean#L120", False),
        (f"{base}/blob/{commit}/scripts/check_erdos269_dyadic_windows.py", False),
        (f"{base}/tree/{commit}", False),
        (f"{base}/blob/{publication_tag}/erdos-257-mersenne-support-subseries.pdf", False),
        (f"{base}/blob/{publication_tag}/docs/claims.json", False),
    )
    for url, must_fail in fixtures:
        violations = publication_binding_violations(url, formal_refs)
        if must_fail:
            require(
                violations == [url],
                f"a publication surface at the formal-source identity was accepted: {url}",
            )
        else:
            require(
                violations == [],
                f"a formal-source link was rejected as a publication surface: {url}",
            )

    require(
        publication_tag not in formal_refs,
        "the publication tag and the formal-source identity have collapsed onto one ref",
    )

    scanned = 0
    for relative in PUBLICATION_SURFACES:
        path = ROOT / relative
        if not path.exists():
            continue
        scanned += 1
        violations = publication_binding_violations(
            path.read_text(encoding="utf-8"), formal_refs
        )
        require(
            not violations,
            f"{relative} serves a publication surface at the formal-source identity: "
            f"{violations}",
        )
    require(scanned >= 10, "the publication-binding scan lost its surface set")

    tex_files = sorted(PAPER.glob("*.tex")) + sorted(
        PAPER.glob("reasoning-parts/*/preamble.tex")
    )
    require(len(tex_files) >= 20, "the paper scan lost its manuscript set")
    for tex in tex_files:
        violations = publication_binding_violations(
            expand_tex(tex.read_text(encoding="utf-8"), commit), formal_refs
        )
        require(
            not violations,
            f"paper/{tex.name} links a publication surface at the formal-source "
            f"identity: {violations}",
        )

    print(
        "publication binding: declaration links stay on the formal source; "
        f"{scanned} publication surfaces and {len(tex_files)} manuscripts carry "
        "no publication link pinned to it PASS"
    )


def main() -> int:
    style = source("paper-house-style.sty")
    require("#1\\##2" in style, "paper link macro is not destination-based")

    target_owner: dict[tuple[str, str], str] = {}
    for pdf, (tex, expected) in CORE.items():
        text = source(tex)
        local_labels = set(re.findall(r"\\label\{([^}]+)\}", text))
        local_refs = set(re.findall(r"\\(?:ref|pageref|eqref)\{([^}]+)\}", text))
        require(local_refs <= local_labels,
                f"{tex} has undefined local references {sorted(local_refs - local_labels)}")
        actual = set(re.findall(r"\\papersectiontarget\{([^}]+)\}", text))
        require(expected <= actual, f"{tex} omits targets {sorted(expected - actual)}")
        require("31 August 2026" in text, f"{tex} omits the dated prototype boundary")
        require("external" in text.lower(), f"{tex} omits the external-use boundary")
        for target in actual:
            key = (pdf, target)
            require(key not in target_owner, f"duplicate destination owner for {key}")
            target_owner[key] = tex

    combined = "\n".join(source(tex) for tex, _ in CORE.values())
    core_links = links(combined)
    for pdf in CORE:
        outbound = {link for link in core_links if link[0] == pdf}
        require(outbound, f"no core paper links to {pdf}")

    preamble = source("problem-note-preamble.tex")
    note_links = links(preamble)
    for pdf in CORE:
        require(any(link[0] == pdf for link in note_links), f"problem notes do not link {pdf}")

    for note in NOTES:
        text = source(note)
        require("\\input{problem-note-preamble}" in text, f"{note} bypasses shared paper links")
        require("\\statusboundary" in text, f"{note} does not emit shared paper links")

    for link in core_links | note_links:
        require(link in target_owner, f"cross-paper link has no declared destination: {link}")

    all_sources = combined + "\n" + preamble
    require("#page=" not in all_sources, "cross-paper navigation uses fragile page numbers")
    print("paper crosslinks: reciprocal core links, eight note routes, and named targets PASS")
    check_publication_binding()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
