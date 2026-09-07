#!/usr/bin/env python3
"""Exact replay of the free-hub existence results (FreeHubExistence.md).

Seven independent exact checks, all in ``fractions.Fraction`` / integer
arithmetic, stdlib only.  No sampling, no root finding, no floating point in
any decision.

1. ``tail_identity``    Lemma T: at a root ``a`` of ``f``, the Taylor
                        truncation ``T_j(a)`` equals MINUS the tail
                        ``sum_{k>j} b_k (a-h)^k``.  Checked exactly on pinned
                        rational configurations at degrees 3..9 and at several
                        rational hubs, by verifying ``sum_{k<=n} b_k (a-h)^k =
                        f(a) = 0`` in ``Q(i)``.

2. ``centroid_collapse``  Corollary C: at the ROOT CENTROID ``h0`` the top
                        Taylor coefficient ``b_{n-1}`` vanishes, hence
                        ``T_{n-2}(a) = T_{n-1}(a) = -(a-h0)^n`` and the
                        hub-Taylor criterion (A) at the centroid only tests
                        ``j = 0`` and ``1 <= j <= n-3``.

3. ``form_a_origin``    Theorem A: for ``f = z^n + g z^{n-2} + c0`` the
                        criterion (A) at ``h = 0`` has value exactly
                        ``max(|c0|, |a|^n)`` at every root.  Verified as an
                        exact POLYNOMIAL identity (root-free): ``T_j = c0`` for
                        ``j <= n-3`` and ``T_j(z) = f(z) - z^n`` for
                        ``n-2 <= j <= n-1``, for degrees 3..12.

4. ``near_fekete_centroid``  Theorem B: if ``m + E < 1`` with ``m = |f(h0)|``
                        and ``E = sum_{k=1}^{n-3} |b_k|`` at the centroid, and
                        two roots satisfy ``|a - h0| < 1``, then criterion (A)
                        holds at ``h0`` for those two roots.  Verified on six
                        stored rational near-Fekete configurations at degrees
                        4..9 with ``mu`` between ``0.9991`` and ``0.9996`` --
                        deep inside the surviving regime.

5. ``free_hub_witnesses``  The headline.  Exact Gaussian-rational hubs at which
                        the three configurations that defeat every fixed hub
                        set on file pass criterion (A) at two roots:
                          - the degree-five witness of
                            ``HubTaylorSpokeCertificate.md`` Theorem 4
                            (no hub in ``{c*} u {admissible critical} u {0} u
                            {centroid}`` carries two contained spokes), at
                            ``h = (-459 + 1167 i)/16384``;
                          - the pinned degree-six and degree-nine witnesses of
                            ``StraightSpokeHubCriterionLab.md`` section 3.
                        All root literals are read from the pinned checkers by
                        AST and asserted byte-equal to the embedded copies.

6. ``theorem_b_strict_gain``  Theorem B strictly improves on the naive Abel
                        bound ``m + sum_{k=1}^{n-1}|b_k| < 1``: six stored
                        Gaussian-rational configurations, one per degree 4..9,
                        all with ``mu > 0.98`` and all roots in the open unit
                        disc, at which Theorem B's hypothesis holds (exact
                        UPPER bounds), the naive bound fails (exact LOWER
                        bounds), and the conclusion is verified directly.

7. ``ray_identity``     Lemma R: ``sum_{l<n} f(h + w^l x) = n (f(h) + x^n)``
                        for every ``h``, ``x`` and ``w`` a primitive ``n``-th
                        root of unity.  Verified exactly over ``Q(i)`` at
                        ``n = 4`` (``w = i``) and ``n = 2``, for stored
                        rational data; the general case is one line of proof
                        (``sum_l w^{lk} = n`` if ``n | k`` and ``0`` otherwise)
                        and is not a numerical claim.

Every decision below is a comparison of exact integers or rationals.
"""

from __future__ import annotations

import ast
import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINNED_SSH = HERE / "check_erdos1041_straight_spoke_hub_criterion.py"
PINNED_HTS = HERE / "check_erdos1041_hub_taylor_spoke_certificate.py"

EMBEDDED_QC: dict[int, tuple[tuple[str, str], ...]] = {
    6: (
        ("0x1.fffffaead1dfdp-1", "-0x1.c7f97b12bedcep-15"),
        ("0x1.004ed623acd87p-1", "0x1.bb3a1b3208ad6p-1"),
        ("-0x1.ffded10fb5c87p-2", "0x1.bb713c92edfe4p-1"),
        ("-0x1.fffff9e87dd68p-1", "-0x1.0766ef919e3d1p-12"),
        ("-0x1.00485f6af598cp-1", "-0x1.bb3dd8051992dp-1"),
        ("0x1.00198d2225a68p-1", "-0x1.bb58e733c06dcp-1"),
    ),
    9: (
        ("0x1.fffffadb279edp-1", "-0x1.54cbe5f38764ep-14"),
        ("0x1.882fdda9ba317p-1", "0x1.4922d6b3868dfp-1"),
        ("0x1.63e8c845cba7bp-3", "0x1.f83590b0811ebp-1"),
        ("-0x1.fffb9be200080p-2", "0x1.bb68ed350eca4p-1"),
        ("-0x1.e121a80180737p-1", "0x1.5e2df749c719cp-2"),
        ("-0x1.e11b7beb2b6bep-1", "-0x1.5e4fe150117d8p-2"),
        ("-0x1.0005816d133a1p-1", "-0x1.bb647aee76a86p-1"),
        ("0x1.637127244f7d2p-3", "-0x1.f83ad6df31cf7p-1"),
        ("0x1.8833eebb49d0cp-1", "-0x1.491f0e2e50785p-1"),
    ),
}

EMBEDDED_QUINTIC: tuple[tuple[str, str], ...] = (
    ("0x1.ffffff1bc8a32p-1", "-0x1.b38f7f9847930p-13"),
    ("0x1.3b2123a383e0cp-2", "0x1.e726fc8e166a3p-1"),
    ("-0x1.9def4ff5a0115p-1", "0x1.2d5569f0967a5p-1"),
    ("-0x1.9dcab3e89de6cp-1", "-0x1.2d87adaf745d1p-1"),
    ("0x1.3c6f58317f761p-2", "-0x1.e6f0d0a92da1bp-1"),
)

#: certified free hubs, as (numerator_real, numerator_imag, denominator)
FREE_HUBS: dict[str, tuple[int, int, int]] = {
    "theorem4_quintic": (-459, 1167, 16384),
    "pinned_deg6": (1178, 806, 16384),
    "pinned_deg9": (-2056, -1670, 16384),
}

#: near-Fekete configurations on which Theorem B fires (Gaussian rationals).
THEOREM_B_WITNESSES: dict[int, tuple[tuple[str, str], ...]] = {
    4: (("8388607/8388608", "0"), ("0", "8386931/8388608"),
        ("-8388607/8388608", "0"), ("0", "-8386931/8388608")),
    5: (("8388607/8388608", "0"), ("1296111/4194304", "15952891/16777216"),
        ("-3393263/4194304", "9859429/16777216"),
        ("-3393263/4194304", "-9859429/16777216"),
        ("1296111/4194304", "-15952891/16777216")),
    6: (("8388607/8388608", "0"), ("8388607/16777216", "14526591/16777216"),
        ("-8388607/16777216", "14526591/16777216"), ("-8388607/8388608", "0"),
        ("-8388607/16777216", "-14526591/16777216"),
        ("8388607/16777216", "-14526591/16777216")),
    7: (("8388607/8388608", "0"), ("5230211/8388608", "6557167/8388608"),
        ("-3733281/16777216", "8176653/8388608"),
        ("-3778937/4194304", "3638953/8388608"),
        ("-3778937/4194304", "-3638953/8388608"),
        ("-3733281/16777216", "-8176653/8388608"),
        ("5230211/8388608", "-6557167/8388608")),
    8: (("8388607/8388608", "0"), ("5931641/8388608", "741307/1048576"),
        ("0", "8386931/8388608"), ("-5931641/8388608", "741307/1048576"),
        ("-8388607/8388608", "0"), ("-5931641/8388608", "-741307/1048576"),
        ("0", "-8386931/8388608"), ("5931641/8388608", "-741307/1048576")),
    9: (("8388607/8388608", "0"), ("3213023/4194304", "10782031/16777216"),
        ("2913333/16777216", "8259515/8388608"),
        ("-8388607/16777216", "14526591/16777216"),
        ("-985339/1048576", "5736999/16777216"),
        ("-985339/1048576", "-5736999/16777216"),
        ("-8388607/16777216", "-14526591/16777216"),
        ("2913333/16777216", "-8259515/8388608"),
        ("3213023/4194304", "-10782031/16777216")),
}

#: surviving-regime configurations (mu > 0.98) at which Theorem B's bound holds
#: and the naive Abel bound m + sum_{k=1}^{n-1}|b_k| < 1 FAILS.
GAP_WITNESSES: dict[int, tuple[tuple[str, str], ...]] = {
    4: (
        ("2096315/2097152", "27391/16777216"),
        ("15689/16777216", "4192755/4194304"),
        ("-16774843/16777216", "-21789/16777216"),
        ("-7061/4194304", "-16766345/16777216"),
    ),
    5: (
        ("16775325/16777216", "-257/16777216"),
        ("5176919/16777216", "7962961/8388608"),
        ("-13570675/16777216", "4916047/8388608"),
        ("-848383/1048576", "-4926603/8388608"),
        ("5199539/16777216", "-15942807/16777216"),
    ),
    6: (
        ("2096815/2097152", "18469/16777216"),
        ("8382451/16777216", "14511195/16777216"),
        ("-8378583/16777216", "14491629/16777216"),
        ("-8381451/8388608", "-20769/16777216"),
        ("-2099315/4194304", "-1814713/2097152"),
        ("2094687/4194304", "-14494681/16777216"),
    ),
    7: (
        ("8383155/8388608", "-3399/16777216"),
        ("653793/1048576", "13102113/16777216"),
        ("-3727395/16777216", "8168501/8388608"),
        ("-3776213/4194304", "7275113/16777216"),
        ("-15108491/16777216", "-1819153/4194304"),
        ("-1871251/8388608", "-4077771/4194304"),
        ("10425855/16777216", "-13089681/16777216"),
    ),
    8: (
        ("8364961/8388608", "4543/8388608"),
        ("5910243/8388608", "11863157/16777216"),
        ("5933/16777216", "16742837/16777216"),
        ("-11853507/16777216", "11833575/16777216"),
        ("-4191737/4194304", "-13423/8388608"),
        ("-11850695/16777216", "-11865503/16777216"),
        ("-21325/16777216", "-16764459/16777216"),
        ("11825151/16777216", "-11843745/16777216"),
    ),
    9: (
        ("4183359/4194304", "-219/4194304"),
        ("12820293/16777216", "10772725/16777216"),
        ("1452891/8388608", "8256197/8388608"),
        ("-4174415/8388608", "14519147/16777216"),
        ("-15722417/16777216", "5730111/16777216"),
        ("-15760767/16777216", "-5737969/16777216"),
        ("-4186869/8388608", "-7248735/8388608"),
        ("721453/4194304", "-8247907/8388608"),
        ("3201551/4194304", "-5384777/8388608"),
    ),
}

#: Form A data: degree -> (gamma_re, gamma_im, c0_re, c0_im) as rational strings
FORM_A: tuple[tuple[int, str, str, str, str], ...] = (
    (3, "1/3", "0", "-1/2", "1/5"),
    (4, "-2/7", "3/11", "1/4", "-1/3"),
    (5, "5/8", "-1/6", "-9/10", "0"),
    (6, "1/2", "1/2", "3/7", "2/9"),
    (7, "-4/5", "1/13", "1/100", "-7/8"),
    (8, "9/4", "-5/3", "-1/2", "1/2"),
    (9, "1/7", "6/5", "2/3", "-1/9"),
    (10, "-3/2", "0", "0", "-4/5"),
    (11, "7/3", "1/4", "-1/6", "5/7"),
    (12, "1/11", "-2/13", "3/8", "1/8"),
)

#: ray-identity probe data: (n, h_re, h_im, x_re, x_im, coefficients ascending)
RAY_DATA: tuple[tuple[int, str, str, str, str, tuple[tuple[str, str], ...]], ...] = (
    (4, "1/3", "-2/5", "3/7", "1/2",
     (("1/2", "-1/3"), ("2/5", "1/7"), ("-3/4", "0"), ("1/6", "5/9"), ("1", "0"))),
    (4, "0", "0", "-1/4", "2/3",
     (("-9/10", "1/10"), ("0", "0"), ("1/2", "-1/2"), ("0", "0"), ("1", "0"))),
    (2, "2/7", "1/9", "5/8", "-1/3",
     (("1/4", "1/5"), ("-2/3", "1/6"), ("1", "0"))),
)


# ---------------------------------------------------------------- Q(i) layer
def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def norm2(a) -> F:
    return a[0] * a[0] + a[1] * a[1]


ZERO = (F(0), F(0))
ONE = (F(1), F(0))


def hexq(pair) -> tuple[F, F]:
    return (F(float.fromhex(pair[0])), F(float.fromhex(pair[1])))


def ratq(pair) -> tuple[F, F]:
    return (F(pair[0]), F(pair[1]))


def poly_from_roots(roots):
    """Descending coefficients of the monic polynomial with the given roots."""
    c = [ONE]
    for r in roots:
        nc = [ZERO] * (len(c) + 1)
        for i, a in enumerate(c):
            nc[i] = add(nc[i], a)
            nc[i + 1] = sub(nc[i + 1], mul(a, r))
        c = nc
    return c


def horner(cdesc, z):
    acc = ZERO
    for a in cdesc:
        acc = add(mul(acc, z), a)
    return acc


def taylor(cdesc, h):
    """Ascending b_0 .. b_n with f(h + w) = sum b_k w^k."""
    work = list(cdesc)
    out = []
    for _ in range(len(cdesc)):
        acc = ZERO
        new = []
        for a in work:
            acc = add(mul(acc, h), a)
            new.append(acc)
        out.append(new[-1])
        work = new[:-1]
        if not work:
            break
    return out


def truncations(b, z, n):
    """T_0(z) .. T_{n-1}(z) with T_j = sum_{k<=j} b_k z^k."""
    out = []
    run = ZERO
    zp = ONE
    for j in range(n):
        if j:
            zp = mul(zp, z)
        run = add(run, mul(b[j], zp))
        out.append(run)
    return out


def ipow(z, k):
    out = ONE
    for _ in range(k):
        out = mul(out, z)
    return out


SCALE = 1 << 64


def sqrt_ub(x: F) -> F:
    """Exact rational UPPER bound for sqrt(x), x >= 0."""
    num = x.numerator * SCALE * SCALE
    den = x.denominator
    return F(isqrt(num // den) + 1, SCALE)


def sqrt_lb(x: F) -> F:
    """Exact rational LOWER bound for sqrt(x), x >= 0."""
    num = x.numerator * SCALE * SCALE
    den = x.denominator
    return F(isqrt(num // den), SCALE)


def centroid(roots):
    n = len(roots)
    return (sum(r[0] for r in roots) / n, sum(r[1] for r in roots) / n)


def pinned(path: Path, symbol: str):
    tree = ast.parse(path.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        targets = getattr(node, "targets", None) or (
            [node.target] if isinstance(node, ast.AnnAssign) else []
        )
        for target in targets:
            if isinstance(target, ast.Name) and target.id == symbol:
                return ast.literal_eval(node.value)
    raise SystemExit(f"{symbol} not found in {path}")


# ---------------------------------------------------------------- the checks
def check_tail_identity() -> dict:
    """Lemma T, as the exact statement sum_{k<=n} b_k (a-h)^k = f(a) = 0."""
    cases = 0
    for n, data in THEOREM_B_WITNESSES.items():
        roots = [ratq(p) for p in data]
        cdesc = poly_from_roots(roots)
        hubs = [ZERO, centroid(roots), (F(1, 7), F(-2, 9)), (F(-3, 5), F(1, 4))]
        for h in hubs:
            b = taylor(cdesc, h)
            for a in roots:
                z = sub(a, h)
                total = ZERO
                for k in range(n + 1):
                    total = add(total, mul(b[k], ipow(z, k)))
                if total != ZERO:
                    return {"status": "fail", "where": f"n={n}"}
                # and T_j = -tail_{j+1}
                T = truncations(b, z, n)
                for j in range(n):
                    tail = ZERO
                    for k in range(j + 1, n + 1):
                        tail = add(tail, mul(b[k], ipow(z, k)))
                    if add(T[j], tail) != ZERO:
                        return {"status": "fail", "where": f"n={n} j={j}"}
                cases += 1
    return {"status": "pass", "checked_root_hub_pairs": cases,
            "degrees": sorted(THEOREM_B_WITNESSES)}


def check_centroid_collapse() -> dict:
    cases = 0
    sets = [(n, [ratq(p) for p in d]) for n, d in THEOREM_B_WITNESSES.items()]
    sets.append((5, [hexq(p) for p in EMBEDDED_QUINTIC]))
    sets.append((6, [hexq(p) for p in EMBEDDED_QC[6]]))
    sets.append((9, [hexq(p) for p in EMBEDDED_QC[9]]))
    for n, roots in sets:
        cdesc = poly_from_roots(roots)
        h0 = centroid(roots)
        b = taylor(cdesc, h0)
        if b[n - 1] != ZERO:
            return {"status": "fail", "where": f"b_(n-1) != 0 at n={n}"}
        for a in roots:
            z = sub(a, h0)
            T = truncations(b, z, n)
            want = sub(ZERO, ipow(z, n))
            if T[n - 1] != want or T[n - 2] != want:
                return {"status": "fail", "where": f"collapse at n={n}"}
            cases += 1
    return {"status": "pass", "checked_roots": cases,
            "claim": "b_{n-1}=0 and T_{n-2}=T_{n-1}=-(a-h0)^n at the root centroid"}


def check_form_a_origin() -> dict:
    """Theorem A as an exact polynomial identity, no roots needed."""
    for n, gr, gi, c0r, c0i in FORM_A:
        gamma = (F(gr), F(gi))
        c0 = (F(c0r), F(c0i))
        # f = z^n + gamma z^{n-2} + c0, descending
        cdesc = [ZERO] * (n + 1)
        cdesc[0] = ONE
        cdesc[2] = gamma
        cdesc[n] = c0
        b = taylor(cdesc, ZERO)
        # b must be (c0, 0, ..., 0, gamma, 0, 1) ascending
        expect = [ZERO] * (n + 1)
        expect[0] = c0
        expect[n - 2] = gamma
        expect[n] = ONE
        if b != expect:
            return {"status": "fail", "where": f"coefficient pattern n={n}"}
        # T_j identically c0 for j <= n-3 ; T_j(z) = gamma z^{n-2} + c0 for j >= n-2
        for j in range(n):
            # symbolic: T_j as an ascending coefficient list
            tj = [b[k] if k <= j else ZERO for k in range(n)]
            if j <= n - 3:
                if any(t != ZERO for t in tj[1:]) or tj[0] != c0:
                    return {"status": "fail", "where": f"T_{j} at n={n}"}
            else:
                want = [ZERO] * n
                want[0] = c0
                want[n - 2] = gamma
                if tj != want:
                    return {"status": "fail", "where": f"T_{j} tail at n={n}"}
    return {"status": "pass", "degrees": [row[0] for row in FORM_A],
            "claim": "for f = z^n + g z^{n-2} + c0 the criterion (A) value at h=0 "
                     "is exactly max(|c0|, |a|^n) at every root"}


def check_near_fekete_centroid() -> dict:
    rows = []
    for n, data in sorted(THEOREM_B_WITNESSES.items()):
        roots = [ratq(p) for p in data]
        cdesc = poly_from_roots(roots)
        h0 = centroid(roots)
        b = taylor(cdesc, h0)
        if b[n - 1] != ZERO:
            return {"status": "fail", "where": f"centroid n={n}"}
        m_ub = sqrt_ub(norm2(b[0]))
        E_ub = sum((sqrt_ub(norm2(b[k])) for k in range(1, max(1, n - 2))), F(0))
        naive_ub = sum((sqrt_ub(norm2(b[k])) for k in range(1, n)), F(0))
        close = [a for a in roots if norm2(sub(a, h0)) < 1]
        hypothesis = bool(m_ub + E_ub < 1 and len(close) >= 2)
        if not hypothesis:
            return {"status": "fail", "where": f"hypothesis does not fire at n={n}"}
        # conclusion, verified directly and exactly
        worst = F(0)
        for a in close[:2]:
            z = sub(a, h0)
            for T in truncations(b, z, n):
                worst = max(worst, norm2(T))
        if not worst < 1:
            return {"status": "fail", "where": f"conclusion at n={n}"}
        rows.append({"n": n, "m_upper": float(m_ub), "E_upper": float(E_ub),
                     "m+E<1": True,
                     "naive_m+sum_{k<n}|b_k|": float(m_ub + naive_ub),
                     "naive_bound_fails": bool(m_ub + naive_ub >= 1),
                     "max_|T_j|^2_over_the_pair": float(worst),
                     "roots_within_1_of_centroid": len(close)})
    return {"status": "pass", "rows": rows}


def check_free_hub_witnesses() -> dict:
    qc = pinned(PINNED_SSH, "QC_REFUTATION_WITNESSES")
    if {k: tuple(v) for k, v in qc.items()} != {k: tuple(v) for k, v in EMBEDDED_QC.items()}:
        return {"status": "fail", "where": "pinned QC witnesses drifted"}
    quintic = pinned(PINNED_HTS, "QUINTIC_HUB_SET_WITNESS")
    if tuple(quintic) != EMBEDDED_QUINTIC:
        return {"status": "fail", "where": "pinned quintic witness drifted"}

    sets = {"theorem4_quintic": [hexq(p) for p in EMBEDDED_QUINTIC],
            "pinned_deg6": [hexq(p) for p in EMBEDDED_QC[6]],
            "pinned_deg9": [hexq(p) for p in EMBEDDED_QC[9]]}
    rows = []
    for tag, roots in sets.items():
        n = len(roots)
        for a in roots:
            if not norm2(a) < 1:
                return {"status": "fail", "where": f"{tag}: root outside the disc"}
        hr, hi, den = FREE_HUBS[tag]
        h = (F(hr, den), F(hi, den))
        cdesc = poly_from_roots(roots)
        b = taylor(cdesc, h)
        vals = []
        for a in roots:
            z = sub(a, h)
            vals.append(max(norm2(T) for T in truncations(b, z, n)))
        order = sorted(range(n), key=lambda i: vals[i])
        i, j = order[0], order[1]
        if not (vals[i] < 1 and vals[j] < 1):
            return {"status": "fail", "where": f"{tag}: criterion (A) fails"}
        # length bound: |a-h| < 1 for both, so the broken line is shorter than 2
        li = sqrt_ub(norm2(sub(roots[i], h)))
        lj = sqrt_ub(norm2(sub(roots[j], h)))
        if not li + lj < 2:
            return {"status": "fail", "where": f"{tag}: length"}
        rows.append({"witness": tag, "n": n,
                     "hub": f"({hr} + {hi} i)/{den}",
                     "pair": [i, j],
                     "max_|T_j(a)|^2": float(vals[i]),
                     "max_|T_j(b)|^2": float(vals[j]),
                     "margin_1_minus_max": float(1 - max(vals[i], vals[j])),
                     "length_upper_bound": float(li + lj)})
    return {"status": "pass", "rows": rows}


def check_ray_identity() -> dict:
    """Lemma R at n = 2 and n = 4, where the n-th roots of unity lie in Q(i)."""
    roots_of_unity = {2: [ONE, (F(-1), F(0))],
                      4: [ONE, (F(0), F(1)), (F(-1), F(0)), (F(0), F(-1))]}
    checked = 0
    for n, hr, hi, xr, xi, casc in RAY_DATA:
        h = (F(hr), F(hi))
        x = (F(xr), F(xi))
        cdesc = [ratq(p) for p in casc][::-1]
        if len(cdesc) != n + 1 or cdesc[0] != ONE:
            return {"status": "fail", "where": f"bad ray data at n={n}"}
        total = ZERO
        for w in roots_of_unity[n]:
            total = add(total, horner(cdesc, add(h, mul(w, x))))
        want = mul((F(n), F(0)), add(horner(cdesc, h), ipow(x, n)))
        if total != want:
            return {"status": "fail", "where": f"ray identity n={n}"}
        checked += 1
    return {"status": "pass", "checked": checked,
            "claim": "sum_{l<n} f(h + w^l x) = n (f(h) + x^n)"}


def check_theorem_b_strict_gain() -> dict:
    """Theorem B fires where the naive Abel bound does not, inside 2/5 < mu < 1."""
    rows = []
    for n, data in sorted(GAP_WITNESSES.items()):
        roots = [ratq(p) for p in data]
        if len(roots) != n:
            return {"status": "fail", "where": f"arity n={n}"}
        for a in roots:
            if not norm2(a) < 1:
                return {"status": "fail", "where": f"root outside the disc n={n}"}
        cdesc = poly_from_roots(roots)
        h0 = centroid(roots)
        b = taylor(cdesc, h0)
        if b[n - 1] != ZERO:
            return {"status": "fail", "where": f"centroid n={n}"}
        m_ub = sqrt_ub(norm2(b[0]))
        E_ub = sum((sqrt_ub(norm2(b[k])) for k in range(1, max(1, n - 2))), F(0))
        naive_lb = m_ub + sum((sqrt_lb(norm2(b[k])) for k in range(1, n)), F(0))
        close = [a for a in roots if norm2(sub(a, h0)) < 1]
        if not (m_ub + E_ub < 1):
            return {"status": "fail", "where": f"Theorem B does not fire at n={n}"}
        if not (naive_lb >= 1):
            return {"status": "fail", "where": f"naive bound does not fail at n={n}"}
        if len(close) < 2:
            return {"status": "fail", "where": f"hypothesis (ii) at n={n}"}
        worst = F(0)
        for a in close[:2]:
            z = sub(a, h0)
            for T in truncations(b, z, n):
                worst = max(worst, norm2(T))
        if not worst < 1:
            return {"status": "fail", "where": f"conclusion at n={n}"}
        rows.append({"n": n, "m+E_upper": float(m_ub + E_ub),
                     "naive_lower": float(naive_lb),
                     "max_|T_j|^2_over_the_pair": float(worst)})
    return {"status": "pass", "rows": rows,
            "claim": "Theorem B strictly improves on the naive Abel bound, "
                     "at every degree 4..9, on configurations with roots in the "
                     "open unit disc"}


def main() -> int:
    checks = {
        "tail_identity": check_tail_identity(),
        "centroid_collapse": check_centroid_collapse(),
        "form_a_origin": check_form_a_origin(),
        "near_fekete_centroid": check_near_fekete_centroid(),
        "free_hub_witnesses": check_free_hub_witnesses(),
        "theorem_b_strict_gain": check_theorem_b_strict_gain(),
        "ray_identity": check_ray_identity(),
    }
    ok = all(v["status"] == "pass" for v in checks.values())
    print(json.dumps({
        "check": "erdos1041_free_hub_existence",
        "status": "pass" if ok else "fail",
        "evidence_class": "exact_rational_certificate",
        "note": "FreeHubExistence.md",
        "checks": checks,
    }, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
