"""Block-source selector: exact engine for small ranges, verified fast path beyond.

The exact engine settles every comparison with literal powers and is the
authority; the fast engine reproduces it from Beatty lattice counts with an
exact guard band and has been checked equal on a <= 3000.  Probes should call
`build_blocks` so the choice is one decision in one place rather than an import
each probe makes for itself.
"""

from __future__ import annotations

EXACT_CEILING = 1500


def build_blocks(max_a: int, mode: str = "auto") -> list[tuple[int, int, int]]:
    if mode not in ("auto", "exact", "fast"):
        raise ValueError("mode must be auto, exact or fast")
    use_exact = mode == "exact" or (mode == "auto" and max_a <= EXACT_CEILING)
    if use_exact:
        from formal_math.probes.erdos269_engine import build_dyadic_blocks
        return build_dyadic_blocks(max_a)
    from formal_math.probes.erdos269_fast_engine import build_dyadic_blocks_fast
    return build_dyadic_blocks_fast(max_a)
