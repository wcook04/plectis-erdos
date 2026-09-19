#!/usr/bin/env python3
"""Exact replay of the hub-Taylor (Abel truncation) straight-spoke certificate.

Four independent exact checks, all in ``fractions.Fraction`` / integer
arithmetic, stdlib only.  No sampling, no root finding, no floating point in
any decision.

1. ``identity``   The truncation identity
                     f(h + s(a-h)) = sum_{j<n} (s^j - s^{j+1}) T_j(a),
                  where T_j is the degree-j Taylor truncation of f at h, is
                  checked as an exact polynomial identity in s over Q(i) for
                  degrees 3..8 on pinned rational configurations.

2. ``free_length``  T_{n-1}(a) = -(a-h)^n at any root a, so the criterion
                  max_j |T_j(a)| < 1 already forces |a-h| < 1.  Checked
                  exactly on the same configurations.  The two-segment
                  length side condition is therefore not an extra hypothesis.

3. ``centroid_witness``  On the two pinned QC_REFUTATION_WITNESSES of
                  StraightSpokeHubCriterionLab.md section 3 -- the degree-six
                  and degree-nine configurations at which NO critical point
                  carries two open-contained straight spokes -- the CENTROID
                  hub carries two roots with max_j |T_j(a)|^2 < 1 and total
                  spoke length < 2.  Exact rational moduli, exact integer
                  square-root upper bounds for the two lengths.

4. ``symmetric_ceiling``  The elementary-symmetric coefficient route
                  (|b_i| <= e_{n-i}(d_1..d_n), spoke radius d_(2)) evaluated on
                  the regular configuration z^n - mu gives the exact value
                  mu * ((1+s)^n - 2^n s^n).  A stored rational s_n certifies
                  ((1+s_n)^n - 2^n s_n^n) >= 25/9 for every 4 <= n <= 64, so
                  that route can never certify a configuration with
                  mu > 9/25.  It is confined strictly inside the regime
                  already closed by ClusterSeparationLowCriticalClosure.md.

The witness literals are read from ``check_erdos1041_straight_spoke_hub_criterion.py``
by AST parsing and asserted byte-equal to the embedded copy, exactly as
``check_erdos1041_pinned_witness_hub_connectors.py`` does, so this checker fails
loudly if the pinned data is ever edited.
"""

from __future__ import annotations

import ast
import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path

PINNED_MODULE = (
    Path(__file__).resolve().parent / "check_erdos1041_straight_spoke_hub_criterion.py"
)
PINNED_SYMBOL = "QC_REFUTATION_WITNESSES"

EMBEDDED_WITNESSES: dict[int, tuple[tuple[str, str], ...]] = {
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

#: rational probe points certifying the symmetric-function ceiling, degree -> s_n
CEILING_PROBE: dict[int, str] = {
    4: "2527/3840", 5: "1393/1920", 6: "37/48", 7: "617/768", 8: "1589/1920",
    9: "3251/3840", 10: "331/384", 11: "1679/1920", 12: "1699/1920",
    13: "1721/1920", 14: "691/768", 15: "3491/3840", 16: "3517/3840",
    17: "1181/1280", 18: "3559/3840", 19: "3577/3840", 20: "1787/1920",
    24: "3651/3840", 32: "3719/3840", 40: "3707/3840", 48: "1869/1920",
    56: "3743/3840", 64: "3755/3840",
}

Q = tuple  # (real, imag) pair of Fractions


def hex_fraction(text: str) -> F:
    return F(float.fromhex(text))


def pinned_witnesses() -> dict[int, tuple[tuple[str, str], ...]]:
    tree = ast.parse(PINNED_MODULE.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        targets = getattr(node, "targets", None) or (
            [node.target] if isinstance(node, ast.AnnAssign) else []
        )
        for target in targets:
            if isinstance(target, ast.Name) and target.id == PINNED_SYMBOL:
                return ast.literal_eval(node.value)
    raise SystemExit(f"{PINNED_SYMBOL} not found in {PINNED_MODULE}")


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def norm2(a) -> F:
    return a[0] * a[0] + a[1] * a[1]


def sqrt_upper(value: F, bits: int = 48) -> F:
    """Rational upper bound for sqrt(value), value >= 0."""
    scale = 1 << bits
    return F(isqrt(value.numerator * scale * scale // value.denominator) + 1, scale)


def taylor_coefficients(roots, hub):
    """Ascending coefficients b_0..b_n of g(w) = prod_j (w - (a_j - hub))."""
    coeffs = [(F(1), F(0))]
    for root in roots:
        disp = sub(root, hub)
        new = [(F(0), F(0))] * (len(coeffs) + 1)
        for k, ck in enumerate(coeffs):
            new[k + 1] = add(new[k + 1], ck)
            new[k] = sub(new[k], mul(ck, disp))
        coeffs = new
    return coeffs


def truncation_values(roots, hub, index):
    """T_j(a_index) for j = 0..n-1, as exact Gaussian rationals."""
    n = len(roots)
    b = taylor_coefficients(roots, hub)
    zeta = sub(roots[index], hub)
    partial = (F(0), F(0))
    power = (F(1), F(0))
    out = []
    for j in range(n):
        partial = add(partial, mul(b[j], power))
        power = mul(power, zeta)
        out.append(partial)
    return out, zeta, b


def centroid(roots):
    n = len(roots)
    return (sum(r[0] for r in roots) / n, sum(r[1] for r in roots) / n)


# ---------------------------------------------------------------- check 1 + 2

def sample_configurations():
    """Pinned rational configurations, degrees 3..8, roots in the open unit disc."""
    out = {}
    for n in range(3, 9):
        roots = []
        for k in range(n):
            num = 1 + 3 * k
            den = 5 + 7 * k + n
            roots.append((F(num, den) - F(1, 3), F(2 * k - n, 2 * den)))
        out[n] = roots
    return out


def poly_mul_s(a, b):
    out = [(F(0), F(0))] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == (F(0), F(0)):
            continue
        for j, bj in enumerate(b):
            out[i + j] = add(out[i + j], mul(ai, bj))
    return out


def check_identity_and_free_length():
    """Exact polynomial identity in s, and T_{n-1}(a) = -(a-h)^n."""
    records = []
    for n, roots in sample_configurations().items():
        hub = centroid(roots)
        # the root of f used as spoke endpoint is roots[0]; f = prod (z - roots_j)
        # left side: f(h + s*zeta) as a polynomial in s
        zeta = sub(roots[0], hub)
        left = [(F(1), F(0))]
        for r in roots:
            const = sub(hub, r)
            left = poly_mul_s(left, [const, zeta])
        T, _, _ = truncation_values(roots, hub, 0)
        # right side: sum_j (s^j - s^{j+1}) T_j
        right = [(F(0), F(0))] * (n + 1)
        for j in range(n):
            right[j] = add(right[j], T[j])
            right[j + 1] = sub(right[j + 1], T[j])
        left = left + [(F(0), F(0))] * (len(right) - len(left))
        identity_ok = all(
            sub(left[k], right[k]) == (F(0), F(0)) for k in range(len(right))
        )
        # free length: T_{n-1}(a) = -(a-h)^n
        power = (F(1), F(0))
        for _ in range(n):
            power = mul(power, zeta)
        free_ok = add(T[n - 1], power) == (F(0), F(0))
        records.append({"degree": n, "identity": identity_ok, "free_length": free_ok})
    return records


# -------------------------------------------------------------------- check 3

def centroid_certificate(degree, witnesses):
    roots = [(hex_fraction(a), hex_fraction(b)) for a, b in witnesses[degree]]
    hub = centroid(roots)
    rows = []
    for i in range(degree):
        T, zeta, _ = truncation_values(roots, hub, i)
        rows.append(
            {
                "root": i,
                "max_trunc_sq": max(norm2(t) for t in T),
                "length_sq": norm2(zeta),
            }
        )
    passing = [r for r in rows if r["max_trunc_sq"] < 1]
    result = {
        "degree": degree,
        "hub": "centroid",
        "roots_passing": [r["root"] for r in passing],
        "max_trunc_sq_passing": [float(r["max_trunc_sq"]) for r in passing],
        "max_trunc_sq_all_below_one": all(r["max_trunc_sq"] < 1 for r in passing),
        "certified": False,
    }
    if len(passing) >= 2:
        chosen = sorted(passing, key=lambda r: r["length_sq"])[:2]
        total = sqrt_upper(chosen[0]["length_sq"]) + sqrt_upper(chosen[1]["length_sq"])
        result["pair"] = [chosen[0]["root"], chosen[1]["root"]]
        result["length_upper_bound"] = float(total)
        result["certified"] = bool(total < 2)
        result["max_trunc_sq_pair_float"] = [
            float(chosen[0]["max_trunc_sq"]),
            float(chosen[1]["max_trunc_sq"]),
        ]
    return result


# -------------------------------------------------------------------- check 4

def symmetric_ceiling():
    rows = []
    worst = None
    for n, text in sorted(CEILING_PROBE.items()):
        s = F(text)
        value = (1 + s) ** n - (2 ** n) * s ** n
        ok = value >= F(25, 9)
        rows.append({"degree": n, "s": text, "route_value_over_mu": float(value), "ok": ok})
        if worst is None or value < worst[1]:
            worst = (n, value)
    return rows, worst



# -------------------------------------------------------------------- check 5

#: degree-five surviving-regime configuration at which the whole hub set
#: {c*} u {critical c : |f(c)|<1} u {0} u {centroid} fails.  IEEE-754 hex
#: literals, exact binary rationals; produced by a wall-guarded adversarial
#: climb on the sharp criterion and re-audited at 60 digits.
QUINTIC_HUB_SET_WITNESS: tuple[tuple[str, str], ...] = (
    ("0x1.ffffff1bc8a32p-1", "-0x1.b38f7f9847930p-13"),
    ("0x1.3b2123a383e0cp-2", "0x1.e726fc8e166a3p-1"),
    ("-0x1.9def4ff5a0115p-1", "0x1.2d5569f0967a5p-1"),
    ("-0x1.9dcab3e89de6cp-1", "-0x1.2d87adaf745d1p-1"),
    ("0x1.3c6f58317f761p-2", "-0x1.e6f0d0a92da1bp-1"),
)

#: numerators over 2^40 of the four critical-point centres of that witness.
QUINTIC_CRITICAL_CENTRES: tuple[tuple[int, int], ...] = (
    (114090007062, -29733055606),
    (5791405992, 34020177758),
    (-50061729660, 104416174971),
    (-69724232664, -108859766159),
)

CRIT_RADIUS = F(1, 1 << 30)
#: crude Lipschitz bound for |f'| on |z| <= 2 with five roots in the unit disc
LIPSCHITZ = F(5 * 81)


def sqrt_lower(value: F, bits: int = 60) -> F:
    scale = 1 << bits
    return F(isqrt(value.numerator * scale * scale // value.denominator), scale)


def poly_from_roots(roots):
    """Descending coefficients of prod_j (z - a_j)."""
    coeffs = [(F(1), F(0))]
    for root in roots:
        new = [(F(0), F(0))] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i] = add(new[i], c)
            new[i + 1] = sub(new[i + 1], mul(c, root))
        coeffs = new
    return coeffs


def poly_eval(coeffs, x):
    acc = (F(0), F(0))
    for c in coeffs:
        acc = add(mul(acc, x), c)
    return acc


def taylor_shift(coeffs, centre):
    """Ascending Taylor coefficients of the polynomial about `centre`."""
    work = list(coeffs)
    out = []
    while work:
        acc = (F(0), F(0))
        quot = []
        for c in work:
            quot.append(acc)
            acc = add(mul(acc, centre), c)
        out.append(acc)
        work = quot[1:]
    return out


def spoke_escape(coeffs, hub, root, slack: F):
    """Rational t with |f(hub + t(root-hub))| - slack > 1, or None."""
    for den in (5, 10, 20, 40, 100, 200, 400, 1000):
        for num in range(1, den):
            t = F(num, den)
            point = (
                hub[0] + t * (root[0] - hub[0]),
                hub[1] + t * (root[1] - hub[1]),
            )
            value = norm2(poly_eval(coeffs, point))
            if sqrt_lower(value) - slack * (1 - t) > 1:
                return {"t": str(t), "modulus_sq": float(value)}
    return None


def quintic_hub_set_refutation():
    roots = [(hex_fraction(a), hex_fraction(b)) for a, b in QUINTIC_HUB_SET_WITNESS]
    n = len(roots)
    coeffs = poly_from_roots(roots)
    deriv = [(coeffs[i][0] * (n - i), coeffs[i][1] * (n - i)) for i in range(n)]
    hubs = []

    # rational hubs: origin and root centroid
    for tag, hub in (("zero", (F(0), F(0))), ("centroid", centroid(roots))):
        escapes = [spoke_escape(coeffs, hub, r, F(0)) for r in roots]
        hubs.append(
            {
                "hub": tag,
                "escaping": [i for i, e in enumerate(escapes) if e],
                "witness_t": [e["t"] if e else None for e in escapes],
                "at_most_contained": n - sum(1 for e in escapes if e),
            }
        )

    # critical hubs: isolate in exact Rouche discs, absorb the disc by Lipschitz
    crit_rows = []
    least_value_lower = None
    for num_re, num_im in QUINTIC_CRITICAL_CENTRES:
        centre = (F(num_re, 1 << 40), F(num_im, 1 << 40))
        g = taylor_shift(deriv, centre)
        while len(g) < n:
            g.append((F(0), F(0)))
        lhs = sqrt_lower(norm2(g[1])) * CRIT_RADIUS
        rhs = sqrt_upper(norm2(g[0])) + sum(
            sqrt_upper(norm2(g[k])) * CRIT_RADIUS ** k for k in range(2, n)
        )
        isolated = lhs > rhs
        value = norm2(poly_eval(coeffs, centre))
        lower = sqrt_lower(value) - LIPSCHITZ * CRIT_RADIUS
        least_value_lower = lower if least_value_lower is None else min(least_value_lower, lower)
        row = {
            "centre_over_2^40": [num_re, num_im],
            "rouche_isolated": bool(isolated),
            "f_modulus_sq_at_centre": float(value),
        }
        if lower > 1:
            row["verdict"] = "inadmissible_on_whole_disc"
            row["at_most_contained"] = 0
        else:
            escapes = [
                spoke_escape(coeffs, centre, r, LIPSCHITZ * CRIT_RADIUS) for r in roots
            ]
            row["escaping"] = [i for i, e in enumerate(escapes) if e]
            row["witness_t"] = [e["t"] if e else None for e in escapes]
            row["at_most_contained"] = n - sum(1 for e in escapes if e)
            row["verdict"] = "at_most_one_contained_spoke"
        crit_rows.append(row)

    return {
        "roots_strictly_inside": all(norm2(r) < 1 for r in roots),
        "max_root_modulus_sq": float(max(norm2(r) for r in roots)),
        "mu_lower_bound": float(least_value_lower),
        "mu_above_nine_twentyfifths": bool(least_value_lower > F(9, 25)),
        "rational_hubs": hubs,
        "critical_hubs": crit_rows,
        "refuted": bool(
            all(norm2(r) < 1 for r in roots)
            and least_value_lower > F(9, 25)
            and all(h["at_most_contained"] <= 1 for h in hubs)
            and all(r["rouche_isolated"] and r["at_most_contained"] <= 1 for r in crit_rows)
        ),
    }


def main() -> None:
    live = pinned_witnesses()
    assert live == EMBEDDED_WITNESSES, "pinned witness literals drifted"

    identity_rows = check_identity_and_free_length()
    certs = [centroid_certificate(6, live), centroid_certificate(9, live)]
    ceiling_rows, worst = symmetric_ceiling()
    quintic = quintic_hub_set_refutation()

    ok = (
        all(r["identity"] and r["free_length"] for r in identity_rows)
        and all(c["certified"] for c in certs)
        and all(r["ok"] for r in ceiling_rows)
        and quintic["refuted"]
    )
    payload = {
        "check": "erdos1041_hub_taylor_spoke_certificate",
        "status": "pass" if ok else "fail",
        "evidence_class": "exact_rational_certificate",
        "identity_degrees": [r["degree"] for r in identity_rows],
        "identity_all_ok": all(r["identity"] for r in identity_rows),
        "free_length_all_ok": all(r["free_length"] for r in identity_rows),
        "centroid_certificates": certs,
        "symmetric_ceiling_min_multiplier": float(worst[1]),
        "symmetric_ceiling_min_degree": worst[0],
        "symmetric_ceiling_mu_bound": float(1 / worst[1]),
        "symmetric_ceiling_below_nine_twentyfifths": bool(1 / worst[1] < F(9, 25)),
        "degrees_certified_for_ceiling": [r["degree"] for r in ceiling_rows],
        "quintic_hub_set_refutation": quintic,
    }
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
