#!/usr/bin/env python3
"""R3 assimilation probes for Erdős #1049.

Modes:
  census   coprime a<=60 region counts (full contour vs BV-difference)
  degrees  2004 two-parameter degree uniqueness for prime 27m+1
  polar    generating-function polar check vs -8 F(1/q)
  laurent  printed Laurent-domain witness against the r2 cap statement
  all      every mode (default)

--quick uses the smallest discriminating grids.  None of these modes proves
irrationality of F(3/2), novelty of the claimed Hankel asymptotic, or a
real-remainder estimate for the 2004 deformation.
"""

from __future__ import annotations

import argparse
import math
from math import isqrt
from pathlib import Path


PAPER = Path(
    "formal_math/erdos257_period_noncollapse/ErdosProblems/papers/"
    "erdos-1049-rational-base-lambert.tex"
)


def _replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected 1 occurrence, found {count}")
    return text.replace(old, new, 1)


THETA_STAR = 0.40568302138406054101566030557693017464819107867787
THETA_BV = 0.5 - 1.0 / (math.pi**2)
STRIP_A60 = {(31, 4), (53, 5), (54, 5), (56, 5)}


def gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return abs(a)


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    limit = isqrt(x)
    d = 3
    while d <= limit:
        if x % d == 0:
            return False
        d += 2
    return True


def census(*, a_max: int = 60) -> dict[str, object]:
    full: list[tuple[int, int]] = []
    strip: list[tuple[int, int]] = []
    for a in range(2, a_max + 1):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            theta = math.log(b) / math.log(a)
            if theta < THETA_STAR:
                full.append((a, b))
                if theta >= THETA_BV:
                    strip.append((a, b))
    strip_set = set(strip)
    if strip_set != STRIP_A60:
        raise SystemExit(
            f"strip mismatch: got {sorted(strip_set)} expected {sorted(STRIP_A60)}"
        )
    if len(full) != 137:
        raise SystemExit(f"full-region count {len(full)} != 137")
    print(
        f"census a<={a_max}: full_region={len(full)} "
        f"improvement_strip={len(strip)} {sorted(strip)}"
    )
    return {"full": len(full), "strip": sorted(strip)}


def laurent_witness() -> None:
    """U_n = X^{-n^2}, V_n = 0 meets the r2 Laurent hypotheses with σ=1, δ=1/4.

    Ordinary polynomial degree of X^{-n^2} is -n^2, hence ≤ (1/4)n^2.
    Coefficient ℓ¹ height is 1.  log|U_n(x) F(x)| = -n^2 log x + log F(x),
    so σ=1.  Then σ/(σ+δ)=4/5 > 1/2, contradicting the printed cap.
    """
    sigma, delta, height = 1.0, 0.25, 1.0
    cutoff = sigma / (sigma + delta)
    if not (height == 1.0 and cutoff > 0.5):
        raise SystemExit("Laurent witness arithmetic failed")
    print(
        f"laurent witness: U=X^{{-n^2}}, V=0, σ={sigma}, δ={delta}, "
        f"H=1, σ/(σ+δ)={cutoff} > 1/2"
    )


def quadratic_degrees(*, m_max: int, quick: bool) -> int:
    checked = 0
    for m in range(1, m_max + 1):
        ell = 27 * m + 1
        if not is_prime(ell):
            continue
        if m % 2 != 0:
            raise SystemExit(f"prime 27m+1 at odd m={m}")
        degrees: list[int] = []
        for t in range(12 * m):
            for s in range(m // 2, m + 2):
                twice = 1091 * m * m + 135 * m - 26 * m * s - s * s - s + 4
                if twice % 2:
                    raise SystemExit(f"odd twice-degree at m={m} t={t} s={s}")
                degrees.append(twice // 2 + t * ell)
        expected = 6 * m * m + 24 * m
        if len(degrees) != expected:
            raise SystemExit(f"row count {len(degrees)} != {expected} at m={m}")
        if len(set(degrees)) != len(degrees):
            raise SystemExit(f"degree collision at m={m}")
        if min(degrees) != 532 * m * m + 53 * m + 1:
            raise SystemExit(f"min degree mismatch at m={m}")
        checked += 1
        if quick and checked >= 3:
            break
    if checked == 0:
        raise SystemExit("no prime 27m+1 in range")
    print(f"degrees: checked {checked} even m with 27m+1 prime, unique K_{{t,s}}")
    return checked


def pochhammer(z: float, q: float, m: int) -> float:
    acc = 1.0
    for r in range(m):
        acc *= 1.0 - z * q**r
        if acc == 0.0:
            return 0.0
    return acc


def pochhammer_inf(z: float, q: float, depth: int) -> float:
    acc = 1.0
    for r in range(depth):
        acc *= 1.0 - z * q**r
    return acc


def gamma_coeffs(q: float, k_max: int, depth: int) -> list[float]:
    """Truncated Taylor coefficients of G_q via log-derivatives of each summand."""
    gamma = [0.0] * (k_max + 1)
    fac = 1.0
    for t in range(k_max + 1):
        if t:
            fac *= 1.0 - q**t
            if fac == 0.0:
                break
        avail = k_max - t
        L = [0.0] * (avail + 1)
        for m in range(1, avail + 1):
            L[m] = (3.0 + 2.0 * q ** (t * m)) / (1.0 - q**m)
            if m % 2 == 0:
                h = m // 2
                L[m] -= 2.0 * q ** (t * h) / (1.0 - q**h)
        g = [1.0]
        for k in range(1, avail + 1):
            g.append(sum(L[m] * g[k - m] for m in range(1, k + 1)) / k)
        for k, value in enumerate(g):
            gamma[t + k] += value / fac
    return gamma


def polar(*, q: float, k_max: int, depth: int) -> None:
    P = pochhammer_inf(q, q, depth)
    S = sum(q**j / (1.0 - q**j) for j in range(1, depth + 1))
    predicted = -8.0 * S
    gamma = gamma_coeffs(q, k_max, depth)
    print(f"polar q={q} P≈{P:.12f} S≈{S:.12f} predicted={predicted:.12f}")
    last = None
    for k in range(min(20, k_max), k_max + 1, max(1, k_max // 6)):
        c = 0.5 * (k + 1) ** 2 * (k + 2)
        a = (P**4) * gamma[k]
        if a <= 0:
            raise SystemExit(f"nonpositive a_{k}")
        scaled = (k + 1) * (a / c - 1.0)
        last = scaled
        print(f"  k={k:3d}  (k+1)(a/c-1)={scaled:.8f}")
    if last is None:
        raise SystemExit("no polar sample")
    # Corroboration only: the approach to -8S is slow; require the right sign
    # and that |last| exceeds 4, which already rules out a 0 or +8S error.
    if not (last < -4.0 and predicted < -4.0 and last / predicted > 0.5):
        raise SystemExit(
            f"polar mismatch: last={last} predicted={predicted}"
        )
    print("polar ok (sign and rough magnitude; not a proof of D'(1))")


def _repo_root() -> Path:
    here = Path(__file__).resolve()
    for parent in here.parents:
        if (parent / "kernel.py").is_file():
            return parent
    raise SystemExit("repo root not found")


def apply_paper_repairs(repo: Path | None = None) -> None:
    """Surgical live-paper repairs authored in this wave, not a Type B paste."""
    path = (repo or _repo_root()) / PAPER
    text = path.read_text()
    text = _replace_once(
        text,
        "conditional on two lemmas of Zudilin, with the sharp $q$-order and the\n"
        "arithmetic obstructions at $3/2$ for Erd\\H{o}s Problem~\\#1049",
        "ordinary specialisation of published 2004 lemmas, exact Hankel order,\n"
        "and the remaining arithmetic at $3/2$",
        "subtitle",
    )
    text = _replace_once(text, "\\date{July 2026}", "\\date{September 2026}", "date")
    text = _replace_once(
        text,
        "Erd\\H{o}s Problem~\\#1049 asks whether \\(F(t)\\) is irrational for every\n"
        "rational \\(t>1\\).  The problem remains open, and this paper proves no\n"
        "irrationality result at \\(t=3/2\\).\n\n"
        "At one rational base it proves irrationality outright.  Zudilin's\n",
        "Erd\\H{o}s Problem~\\#1049 asks whether \\(F(t)\\) is irrational for every\n"
        "rational \\(t>1\\).  For coprime integers \\(a>b\\ge1\\) with\n"
        "\\(\\log b/\\log a<\\theta^{*}=C_{0}/C_{1}\\), this note proves \\(F(a/b)\\)\n"
        "irrational by an ordinary argument; in particular every\n"
        "\\(F\\bigl((31/4)^{r}\\bigr)\\) is irrational.  The parent case \\(t=3/2\\)\n"
        "is not settled here.\n\n"
        "The argument specialises Zudilin's\n",
        "abstract-lead",
    )
    text = _replace_once(
        text,
        "\\((0.398678,0.405683]\\) above the Bundschuh--V\\\"a\\\"an\\\"anen region, which\n"
        "contains \\(31/4\\) and no integer base.\n",
        "\\((1/2-1/\\pi^{2},\\theta^{*})\\) above the Bundschuh--V\\\"a\\\"an\\\"anen region.\n"
        "Among coprime pairs with numerator at most \\(60\\), that difference strip\n"
        "contains four members \\((31,4)\\), \\((53,5)\\), \\((54,5)\\), \\((56,5)\\);\n"
        "the count \\(137\\) is the size of the full contour region, not of the strip.\n",
        "abstract-strip",
    )
    text = _replace_once(
        text,
        "with a base-independent coefficient-height bound on finite\n"
        "Laurent polynomials, is confined to \\(b^2<a\\), so the same mechanism reaches no\n"
        "base with \\(b^2\\ge a\\), \\(3/2\\) included.\n",
        "with a base-independent coefficient-height bound on final pairs in\n"
        "\\(\\mathbb Z[X]^{2}\\), is confined to \\(b^2<a\\), so the same mechanism reaches no\n"
        "base with \\(b^2\\ge a\\), \\(3/2\\) included.  Laurent polynomials may appear only\n"
        "in intermediate norm estimates, not as the final pair.\n",
        "abstract-cap-domain",
    )
    text = _replace_once(
        text,
        "Our strongest unconditional theorem sharpens the normalized Hankel estimate in Zudilin's\n",
        "A second principal theorem sharpens the normalized Hankel estimate in Zudilin's\n",
        "no-contest",
    )
    text = _replace_once(
        text,
        "minors vanish and the second coordinates are units, a B\\'ezout shear reduces\n"
        "the sufficient selector width from \\(2S+4R\\) to \\(S+2R\\).\n",
        "minors vanish and each row is unimodular, a B\\'ezout shear reduces\n"
        "the sufficient selector width from \\(2S+4R\\) to \\(S+2R\\).\n",
        "abstract-plucker",
    )
    text = _replace_once(
        text,
        "The strip $(1/\\mu_{BV},\\theta^*]$ gained over\n"
        "Bundschuh--V\\\"a\\\"an\\\"anen has no member with $b=2$ or $b=3$.  Its first member\n"
        "is $31/4$, followed by $53/5$, $54/5$, $56/5$, $83/6$, $85/6$, $89/6$, and so\n"
        "on; the strip is infinite, and $137$ coprime pairs with $a\\le60$ lie in it.\n",
        "The open-closed difference $(1/\\mu_{BV},\\theta^*)$ gained over\n"
        "Bundschuh--V\\\"a\\\"an\\\"anen has no member with $b=2$ or $b=3$.  Its first member\n"
        "is $31/4$, followed by $53/5$, $54/5$, $56/5$, $83/6$, $85/6$, $89/6$, and so\n"
        "on; the strip is infinite.  Among coprime $a\\le60$ the difference contains\n"
        "exactly the four pairs $(31,4)$, $(53,5)$, $(54,5)$, $(56,5)$; the count\n"
        "$137$ is the full contour region $\\log b/\\log a<\\theta^*$, including the\n"
        "earlier Bundschuh--V\\\"a\\\"an\\\"anen members.\n",
        "body-strip",
    )
    path.write_text(text)
    print(f"applied first paper batch to {path}")


def apply_paper_batch2(repo: Path | None = None) -> None:
    path = (repo or _repo_root()) / PAPER
    text = path.read_text()
    text = _replace_once(
        text,
        "A rational base outside the Bundschuh--V\\\"a\\\"an\\\"anen region,\n"
        "ordinary specialisation of published 2004 lemmas, exact Hankel order,\n"
        "and the remaining arithmetic at $3/2$",
        "Ordinary specialisation of published 2004 lemmas, exact Hankel order,\n"
        "and the remaining arithmetic at $3/2$",
        "subtitle-join",
    )
    text = _replace_once(
        text,
        "The argument specialises Zudilin's\n"
        "$q$-harmonic construction in the direction \\((14,12,14;27)\\) survives\n",
        "Zudilin's\n"
        "$q$-harmonic construction in the direction \\((14,12,14;27)\\) survives\n",
        "abstract-grammar",
    )
    text = _replace_once(
        text,
        "Let $(U_n,V_n)$ be finite Laurent polynomials in $\\mathbb Z[X,X^{-1}]$ satisfying $\\Lambda_n(x)=U_n(x)F(x)-V_n(x)\\ne0$,\n",
        "Let $(U_n,V_n)$ be pairs in $\\mathbb Z[X]^2$ satisfying $\\Lambda_n(x)=U_n(x)F(x)-V_n(x)\\ne0$,\n",
        "cap-domain",
    )
    text = _replace_once(
        text,
        "\\noindent So $b^2<a$ is a hard cap on every base-uniform rank-two family in\n"
        "$\\mathbb Z[X,X^{-1}]$ that also carries a base-independent coefficient-height bound,\n"
        "Zudilin's included, and $3/2$ is out of reach for this\n"
        "construction family entirely.  That is the reason the rest of this paper is a\n"
        "record of obstructions rather than a second theorem.\n"
        "The coefficient-height hypothesis is recorded in\n"
        "\\texttt{ErdosProblems/Erdos1049/RationalBaseIrrationality\\_31\\_4\\_Proof.md}.\n",
        "\\begin{proof}\n"
        "Write $H_n=\\max(H(U_n),H(V_n))$.  Then\n"
        "$|U_n(x)|,|V_n(x)|\\le (1+\\deg U_n+\\deg V_n)H_n x^{d_n}$ for real $x>1$.\n"
        "Suppose $\\sigma>\\delta$ and choose an integer $p\\ge2$ with\n"
        "$(\\sigma-\\delta)\\log p>h$.  Set $a_n=U_n(p)$, $b_n=V_n(p)$ and\n"
        "$L_n=a_n F(p)-b_n$.  Hypotheses on height and degree give\n"
        "$|a_n|\\le\\exp((h+\\delta\\log p)n^2+o(n^2))$, while\n"
        "$|L_n|=\\exp(-\\sigma\\log p\\,n^2+o(n^2))$.  The adjacent integer\n"
        "\\[\n"
        " a_nb_{n+1}-a_{n+1}b_n=a_{n+1}L_n-a_n L_{n+1}\n"
        "\\]\n"
        "is then $o(1)$, hence eventually zero.  Also $a_n\\ne0$ for large $n$:\n"
        "otherwise the nonzero integer $L_n=-b_n$ would have absolute value less\n"
        "than $1$.  Thus $b_n/a_n$ is eventually a fixed rational $r$.  If\n"
        "$F(p)\\ne r$ then $|L_n|\\ge|F(p)-r|$; if $F(p)=r$ then $L_n=0$.  Both\n"
        "contradict the hypotheses, so $\\sigma\\le\\delta$.\n"
        "The homogenised logarithm satisfies\n"
        "\\[\n"
        " \\limsup_{n\\to\\infty} n^{-2}\\log\\bigl|b^{d_n}\\Lambda_n(a/b)\\bigr|\n"
        " \\le \\delta\\log b-\\sigma\\log(a/b),\n"
        "\\]\n"
        "which is negative on the stated sufficient region.  An upper bound on\n"
        "degree cannot by itself exclude a family beyond that cutoff.\n"
        "\\end{proof}\n"
        "\n"
        "\\noindent The printed Laurent-polynomial domain is false: $U_n=X^{-n^2}$,\n"
        "$V_n=0$, $\\sigma=1$, $\\delta=1/4$ and height $1$ meet those hypotheses and\n"
        "violate $\\sigma/(\\sigma+\\delta)\\le1/2$.  Final pairs must lie in\n"
        "$\\mathbb Z[X]^2$; Laurent expressions are permitted only when estimating\n"
        "intermediate $\\ell^1$ norms.  So $b^2<a$ is a sufficient cap on every\n"
        "base-uniform rank-two family in $\\mathbb Z[X]^2$ with a base-independent\n"
        "coefficient-height bound, Zudilin's included, and $3/2$ is out of reach\n"
        "for this construction family.  The coefficient-height hypothesis is recorded in\n"
        "\\texttt{ErdosProblems/Erdos1049/RationalBaseIrrationality\\_31\\_4\\_Proof.md}.\n",
        "cap-proof",
    )
    text = _replace_once(
        text,
        "The base $3/2$ lies outside both regions, since $3^{81}<2^{200}$ gives\n"
        "$81/200<\\log2/\\log3=0.6309\\ldots$\n"
        "(\\lword{Erdos1049/ZudilinHeightRegion.lean}{122}{threeHalves\\_outside\\_zudilinHeightRegion}{exclusion},\n"
        "\\lword{Erdos1049/ZudilinHeightRegion.lean}{130}{threeHalves\\_outside\\_bundschuhVaananenHeightRegion}{exclusion}).\n",
        "The base $3/2$ lies outside the full contour because\n"
        "$\\theta^*<1/2<\\log2/\\log3$ (the last comparison is $3<4$).  The weaker\n"
        "sub-boundary $3^{81}<2^{200}$, hence $81/200<\\log2/\\log3$, remains a\n"
        "separate pinned formal lemma\n"
        "(\\lword{Erdos1049/ZudilinHeightRegion.lean}{122}{threeHalves\\_outside\\_zudilinHeightRegion}{rational sub-boundary},\n"
        "\\lword{Erdos1049/ZudilinHeightRegion.lean}{130}{threeHalves\\_outside\\_bundschuhVaananenHeightRegion}{earlier region}).\n",
        "three-halves-exclusion",
    )
    text = _replace_once(
        text,
        "only the filtered initial-monomial iteration for rows $j\\ge2$ and all columns remains formal.\n",
        "only the filtered initial-monomial iteration for rows $j\\ge3$ and all columns remains formal.\n",
        "hankel-remaining-rows",
    )
    text = _replace_once(
        text,
        "Formal\norder does not by itself bound the residual at a fixed $q$; the companion\n",
        "The same two formulas are the weight of the unique least-order Gram tuple $k_i=i$.  Formal\n"
        "order does not by itself bound the residual at a fixed $q$; the companion\n",
        "hankel-ki",
    )
    path.write_text(text)
    print(f"applied second paper batch to {path}")


def apply_paper_batch3(repo: Path | None = None) -> None:
    path = (repo or _repo_root()) / PAPER
    text = path.read_text()
    text = _replace_once(
        text,
        "Then $F(a/b)$ is irrational.  The proof consumes Lemma~7 of\n"
        "Zudilin~\\cite{zudilin2004} in its polynomial reading at display~(24), together\n"
        "with his Lemmas~1 and~2 at the integer instance $p=2$, and nothing else\n"
        "external.\n"
        "\\end{theorem}\n",
        "Then $F(a/b)$ is irrational.  The proof consumes Lemma~7 of\n"
        "Zudilin~\\cite{zudilin2004} in its polynomial reading at display~(24), together\n"
        "with his Lemmas~1 and~2 at the integer instance $p=2$, and nothing else\n"
        "external.\n"
        "\\end{theorem}\n"
        "\n"
        "\\noindent Cyclotomic cancellation is performed before the denominator of\n"
        "the rational base is cleared, so the degree budget is that of the cancelled\n"
        "forms.\n",
        "cancellation-before-clearing",
    )
    text = _replace_once(
        text,
        "Under the endpoint hypotheses of Proposition~\\ref{res:commonmult}, neither\n"
        "integer scalar content of specialised rows nor a common divisor of the two specialised\n"
        "evaluations \\(H_W(U)\\) and \\(H_W(V)\\) can supply factors \\(2\\) and \\(3\\) by\n"
        "those mechanisms in the common-width endpoint architecture studied here.\n",
        "Integer scalar multiplication leaves the ratio of a certified divisor to the\n"
        "matching absolute height unchanged.  Under the endpoint hypotheses of\n"
        "Proposition~\\ref{res:commonmult}, a common divisor of the unscaled evaluations\n"
        "\\(H_W(U)\\) and \\(H_W(V)\\) is coprime to \\(6\\).\n",
        "nomult-wording",
    )
    text = _replace_once(
        text,
        "that every $B_n$ is a unit and every adjacent minor vanishes:\n",
        "that every row is unimodular ($u_n A_n+v_n B_n=1$ for some $u_n,v_n$) and every adjacent minor vanishes:\n",
        "plucker-hyp",
    )
    text = _replace_once(
        text,
        "A unit second coordinate makes each row a unimodular anchor.  Vanishing of the\n",
        "A B\\'ezout identity makes each row a unimodular anchor; a unit coordinate is the special case already recorded.  Vanishing of the\n",
        "plucker-proof",
    )
    text = _replace_once(
        text,
        "\\lword{Erdos1049/BezoutPluckerJets.lean}{191}{adjacent_det_zero_forces_all_det_zero}{kernel checked};\n"
        "the one-dimensional collision after a B\\'ezout shear is\n"
        "\\lword{Erdos1049/BezoutPluckerJets.lean}{145}{binary_row_collision_of_anchor_det_zero}{kernel checked};\n"
        "and the explicit $2$/$3$-depth endpoint is\n"
        "\\lword{Erdos1049/BezoutPluckerJets.lean}{249}{zmod_binary_tail_collision_of_two_three_depth}{kernel checked}.\n",
        "\\lword{Erdos1049/BezoutPluckerJets.lean}{191}{adjacent_det_zero_forces_all_det_zero_of_isCoprime}{unimodular propagation};\n"
        "the one-dimensional collision after a B\\'ezout shear is\n"
        "\\lword{Erdos1049/BezoutPluckerJets.lean}{145}{binary_row_collision_of_anchor_det_zero}{kernel checked};\n"
        "and the explicit $2$/$3$-depth endpoint is\n"
        "\\lword{Erdos1049/BezoutPluckerJets.lean}{299}{zmod_binary_tail_collision_of_two_three_depth_of_isCoprime}{unimodular width}.\n"
        "The unit-coordinate wrappers remain as special cases.  Primitive integer rows\n"
        "are unimodular modulo every modulus, even when neither coordinate is a unit\n"
        "(the pair $(2,3)$ modulo $6$ is the local example).\n",
        "plucker-locators",
    )
    text = _replace_once(
        text,
        "subproblem for one common-width additive architecture.  It is not asserted to\n"
        "be necessary for every proof of irrationality.\n",
        "subproblem for one common-width additive architecture.  It is not asserted to\n"
        "be necessary for every proof of irrationality.\n"
        "Without a named source family, a primitive scaling, and an effective height\n"
        "bound, the unrestricted existence question is equivalent to irrationality of\n"
        "$F(3/2)$: Dirichlet supplies a small form, and every integer pair is a\n"
        "width-$W$ homogeneous evaluation.  Arbitrary polynomial lifts of already small\n"
        "rationals are therefore not a new producer.  The question below requires a\n"
        "literal source formula and those scaling data before asking for kernel escape.\n",
        "kernel-scope",
    )
    text = _replace_once(
        text,
        "together with polynomial pairs\n"
        "\\((U_{n,j},V_{n,j})\\in\\Z[X]^2\\) for \\(0\\le j<M_n\\), each of degree at most\n"
        "the common declared width \\(W_n\\), whose specialised integer rows are\n"
        "primitive:\n",
        "together with polynomial pairs coming from a named source family with an\n"
        "explicit coefficient-height bound after primitive normalisation,\n"
        "\\((U_{n,j},V_{n,j})\\in\\Z[X]^2\\) for \\(0\\le j<M_n\\), each of degree at most\n"
        "the common declared width \\(W_n\\), whose specialised integer rows are\n"
        "primitive:\n",
        "kernel-family",
    )
    path.write_text(text)
    print(f"applied third paper batch to {path}")


def apply_paper_batch4(repo: Path | None = None) -> None:
    path = (repo or _repo_root()) / PAPER
    text = path.read_text()
    text = _replace_once(
        text,
        "B\\'ezout--Pl\\\"ucker reduction under explicit minor and unit hypotheses.\n",
        "B\\'ezout--Pl\\\"ucker reduction under explicit minor and unimodular hypotheses.\n",
        "paperresult-unimodular",
    )
    path.write_text(text)
    print(f"applied fourth paper batch to {path}")


def apply_paper_batch5(repo: Path | None = None) -> None:
    path = (repo or _repo_root()) / PAPER
    text = path.read_text()
    text = _replace_once(
        text,
        "Nothing in this section bears on $t=3/2$, and the rest of the paper is the\n"
        "record of why that base is hard.\n",
        "That full-contour comparison, not the weaker $81/200$ sub-boundary, is the\n"
        "exclusion of $t=3/2$ from the ordinary region.  The rest of the paper records\n"
        "why a different construction family would still be needed at that base.\n",
        "three-halves-exclusion-sentence",
    )
    path.write_text(text)
    print(f"applied fifth paper batch to {path}")


PACKET = Path(
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "research_packet.json"
)


def apply_packet_repairs(repo: Path | None = None) -> None:
    path = (repo or _repo_root()) / PACKET
    text = path.read_text()
    text = _replace_once(
        text,
        '      "id": "adjacent_det_zero_forces_all_det_zero_consumer",\n'
        '      "status": "lean_checked_adjacent_to_tail_propagation_consumer",\n'
        '      "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean",\n'
        '      "source_commit": "0d532ec9fe405ab794df08371457f0d30926d82b",\n'
        '      "source_sha256": "4579858b1b497ca1c9a377a202bb3bf84d4cdaad20c0e3f5ba2730740cbccdb3",\n'
        '      "source_current": true,\n'
        '      "source_declarations": [\n'
        '        "ErdosProblems.Erdos1049.BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero"\n'
        "      ],\n",
        '      "id": "adjacent_det_zero_forces_all_det_zero_consumer",\n'
        '      "status": "lean_checked_adjacent_to_tail_propagation_consumer",\n'
        '      "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean",\n'
        '      "source_commit": "0d532ec9fe405ab794df08371457f0d30926d82b",\n'
        '      "source_sha256": "4579858b1b497ca1c9a377a202bb3bf84d4cdaad20c0e3f5ba2730740cbccdb3",\n'
        '      "source_current": true,\n'
        '      "source_declarations": [\n'
        '        "ErdosProblems.Erdos1049.BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero_of_isCoprime",\n'
        '        "ErdosProblems.Erdos1049.BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero"\n'
        "      ],\n",
        "packet-adjacent-of-isCoprime",
    )
    text = _replace_once(
        text,
        '      "id": "zmod_binary_tail_collision_of_adjacent_det_zero_consumer",\n'
        '      "status": "lean_checked_adjacent_tail_collision_consumer",\n'
        '      "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean",\n'
        '      "source_commit": "0d532ec9fe405ab794df08371457f0d30926d82b",\n'
        '      "source_sha256": "4579858b1b497ca1c9a377a202bb3bf84d4cdaad20c0e3f5ba2730740cbccdb3",\n'
        '      "source_current": true,\n'
        '      "source_declarations": [\n'
        '        "ErdosProblems.Erdos1049.BezoutPluckerJets.zmod_binary_tail_collision_of_adjacent_det_zero"\n'
        "      ],\n",
        '      "id": "zmod_binary_tail_collision_of_adjacent_det_zero_consumer",\n'
        '      "status": "lean_checked_adjacent_tail_collision_consumer",\n'
        '      "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean",\n'
        '      "source_commit": "0d532ec9fe405ab794df08371457f0d30926d82b",\n'
        '      "source_sha256": "4579858b1b497ca1c9a377a202bb3bf84d4cdaad20c0e3f5ba2730740cbccdb3",\n'
        '      "source_current": true,\n'
        '      "source_declarations": [\n'
        '        "ErdosProblems.Erdos1049.BezoutPluckerJets.zmod_binary_tail_collision_of_adjacent_det_zero_of_isCoprime",\n'
        '        "ErdosProblems.Erdos1049.BezoutPluckerJets.zmod_binary_tail_collision_of_adjacent_det_zero"\n'
        "      ],\n",
        "packet-zmod-adjacent-of-isCoprime",
    )
    text = _replace_once(
        text,
        '      "id": "zmod_binary_tail_collision_of_two_three_depth_consumer",\n'
        '      "status": "lean_checked_two_three_depth_consumer",\n'
        '      "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean",\n'
        '      "source_commit": "0d532ec9fe405ab794df08371457f0d30926d82b",\n'
        '      "source_sha256": "4579858b1b497ca1c9a377a202bb3bf84d4cdaad20c0e3f5ba2730740cbccdb3",\n'
        '      "source_current": true,\n'
        '      "source_declarations": [\n'
        '        "ErdosProblems.Erdos1049.BezoutPluckerJets.zmod_binary_tail_collision_of_two_three_depth"\n'
        "      ],\n",
        '      "id": "zmod_binary_tail_collision_of_two_three_depth_consumer",\n'
        '      "status": "lean_checked_two_three_depth_consumer",\n'
        '      "source_path": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean",\n'
        '      "source_commit": "0d532ec9fe405ab794df08371457f0d30926d82b",\n'
        '      "source_sha256": "4579858b1b497ca1c9a377a202bb3bf84d4cdaad20c0e3f5ba2730740cbccdb3",\n'
        '      "source_current": true,\n'
        '      "source_declarations": [\n'
        '        "ErdosProblems.Erdos1049.BezoutPluckerJets.zmod_binary_tail_collision_of_two_three_depth_of_isCoprime",\n'
        '        "ErdosProblems.Erdos1049.BezoutPluckerJets.zmod_binary_tail_collision_of_two_three_depth"\n'
        "      ],\n",
        "packet-zmod-23-of-isCoprime",
    )
    text = _replace_once(
        text,
        '      "proof": "Hypotheses (2)+(3) give |U_n(p)| <= exp((h + delta log p) n^2 (1+o(1))) at every integer p >= 2; (4) gives two-sided smallness; the minimal-n exponent lemma then gives mu(F(p)) <= 1 + (h + delta log p)/(sigma log p). F(p) is irrational for every integer p >= 2 (Erdos 1948, Bezivin 1988, Borwein 1991), so mu >= 2 by Dirichlet and (sigma - delta) log p <= h for every p >= 2; letting p -> infinity gives sigma <= delta. formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalBaseIrrationality_31_4_Proof.md Sec. 5.",',
        '      "proof": "An adjacent-integer-determinant argument yields sigma <= delta without using irrationality of F(p): if sigma > delta, choose integer p >= 2 with (sigma-delta) log p > h; the values a_n = U_n(p), b_n = V_n(p) are integers and the adjacent determinant a_n b_{n+1}-a_{n+1} b_n tends to 0, hence is eventually 0, forcing a fixed rational ratio that contradicts the hypotheses. The older exponent-lemma route remains: hypotheses (2)+(3) give |U_n(p)| <= exp((h + delta log p) n^2 (1+o(1))) at every integer p >= 2; (4) gives two-sided smallness; the minimal-n exponent lemma then gives mu(F(p)) <= 1 + (h + delta log p)/(sigma log p). F(p) is irrational for every integer p >= 2 (Erdos 1948, Bezivin 1988, Borwein 1991), so mu >= 2 by Dirichlet and (sigma - delta) log p <= h for every p >= 2; letting p -> infinity gives sigma <= delta. formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalBaseIrrationality_31_4_Proof.md Sec. 5.",',
        "packet-cap-adjacent-proof",
    )
    path.write_text(text)
    print(f"applied packet repairs to {path}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=(
            "all",
            "census",
            "degrees",
            "polar",
            "laurent",
            "apply-paper",
            "apply-paper2",
            "apply-paper3",
            "apply-paper4",
            "apply-paper5",
            "apply-packet",
        ),
        default="all",
    )
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--q", type=float, default=2.0 / 3.0)
    args = parser.parse_args()
    if args.mode == "apply-paper":
        apply_paper_repairs()
        return 0
    if args.mode == "apply-paper2":
        apply_paper_batch2()
        return 0
    if args.mode == "apply-paper3":
        apply_paper_batch3()
        return 0
    if args.mode == "apply-paper4":
        apply_paper_batch4()
        return 0
    if args.mode == "apply-paper5":
        apply_paper_batch5()
        return 0
    if args.mode == "apply-packet":
        apply_packet_repairs()
        return 0
    modes = (
        ["census", "laurent", "degrees", "polar"]
        if args.mode == "all"
        else [args.mode]
    )
    k_max = 40 if args.quick else 80
    depth = 60 if args.quick else 120
    m_max = 40 if args.quick else 200
    if "census" in modes:
        census()
    if "laurent" in modes:
        laurent_witness()
    if "degrees" in modes:
        quadratic_degrees(m_max=m_max, quick=args.quick)
    if "polar" in modes:
        polar(q=args.q, k_max=k_max, depth=depth)
    print("ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
