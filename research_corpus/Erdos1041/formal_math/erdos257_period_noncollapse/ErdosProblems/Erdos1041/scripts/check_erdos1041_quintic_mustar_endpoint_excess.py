"""Exact endpoint-excess certificate at the two nonreal gap-zero fibres.

All acceptance decisions use exact algebraic root counts or rational interval
arithmetic.  Floating point is used only to print readable diagnostics; the
rational boxes below are part of the certificate.
"""

from __future__ import annotations

from fractions import Fraction as Q
import importlib.util
from pathlib import Path

import sympy as sp
from sympy import QQ


CENTRAL = Path(__file__).with_name(
    "check_erdos1041_quintic_minus_ten_central_excess.py"
)
SPEC = importlib.util.spec_from_file_location("minus_ten_central", CENTRAL)
M = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(M)

Iv = M.Iv
sqrt_iv = M.sqrt_iv

FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def box(lo: int, hi: int, den: int = 10**6) -> Iv:
    return Iv(Q(lo, den), Q(hi, den))


def contains_zero(x: Iv) -> bool:
    return x.lo <= 0 <= x.hi


aa, cc, ss, p, q = sp.symbols("a c s p q", real=True)
u = p + sp.I * q

E = sp.expand(
    aa * (p**4 - 6 * p**2 * q**2 - 2 * p**2 + q**4 + 2 * q**2 + 1)
    + 5 * p**4 * q
    - 10 * p**2 * q**3
    - 6 * p**2 * q
    + q**5
    + 2 * q**3
    + q
)
R = sp.expand(
    -4 * aa * p**3 * q
    + 4 * aa * p * q**3
    + 4 * aa * p * q
    + p**5
    - 10 * p**3 * q**2
    - 2 * p**3
    + 5 * p * q**4
    + 6 * p * q**2
    + p
)
D = sp.expand(
    5 * p**4
    - 30 * p**2 * q**2
    - 6 * p**2
    + 5 * q**4
    + 6 * q**2
    + 1
    - 12 * aa * p**2 * q
    + 4 * aa * q**3
    + 4 * aa * q
)
I = sp.expand(4 * p * (aa * p**2 - 3 * aa * q**2 - aa + 5 * p**2 * q - 5 * q**3 - 3 * q))


def eval_poly(expr: sp.Expr, boxes: dict[sp.Symbol, Iv]) -> Iv:
    variables = list(boxes)
    polynomial = sp.Poly(sp.expand(expr), *variables, domain=sp.QQ)
    result = Iv(0)
    for powers, coefficient in polynomial.terms():
        term = Iv(Q(int(coefficient.p), int(coefficient.q)))
        for variable, exponent in zip(variables, powers):
            term *= boxes[variable] ** exponent
        result += term
    return result


A5 = Iv(Q(2236067977499789, 10**15), Q(2236067977499790, 10**15))
S30 = Iv(Q(5477225575051661, 10**15), Q(5477225575051662, 10**15))
SLOW = Iv(Q(587785252292473, 10**15), Q(587785252292474, 10**15))
SHIGH = Iv(Q(951056516295153, 10**15), Q(951056516295154, 10**15))


def radical_boxes_exact() -> bool:
    return (
        A5.lo**2 < 5 < A5.hi**2
        and S30.lo**2 < 30 < S30.hi**2
        and (4 * SLOW.lo) ** 2 < 10 - 2 * A5.hi
        and (4 * SLOW.hi) ** 2 > 10 - 2 * A5.lo
        and (4 * SHIGH.lo) ** 2 < 10 + 2 * A5.lo
        and (4 * SHIGH.hi) ** 2 > 10 + 2 * A5.hi
    )


SPECS = {
    "positive hard": {
        "sigma": 1,
        "c_exact": -(1 + sp.sqrt(5)) / 4,
        "s_exact": -sp.sqrt(10 - 2 * sp.sqrt(5)) / 4,
        "c": -(1 + A5) / 4,
        "s": -SLOW,
        "region": lambda pb, qb, tb: pb.hi < 0 and qb.hi < 0 and tb.lo > 0,
    },
    "positive easy": {
        "sigma": 1,
        "c_exact": -(1 + sp.sqrt(5)) / 4,
        "s_exact": sp.sqrt(10 - 2 * sp.sqrt(5)) / 4,
        "c": -(1 + A5) / 4,
        "s": SLOW,
        "region": lambda pb, qb, tb: pb.hi < 0 and qb.lo > 0 and tb.lo > 0,
    },
    "negative hard": {
        "sigma": -1,
        "c_exact": (1 - sp.sqrt(5)) / 4,
        "s_exact": sp.sqrt(10 + 2 * sp.sqrt(5)) / 4,
        "c": (1 - A5) / 4,
        "s": SHIGH,
        "region": lambda pb, qb, tb: pb.hi < 0 and qb.lo > 0 and tb.hi < 0,
    },
    "negative easy": {
        "sigma": -1,
        "c_exact": sp.Integer(-1),
        "s_exact": sp.Integer(0),
        "c": Iv(-1),
        "s": Iv(0),
        "region": lambda pb, qb, tb: pb.hi < -1 and -A5.lo < qb.lo and qb.hi < 0 and tb.hi < 0,
    },
}


# Every row is (q-box, list of p-boxes).  The boxes cover every nonzero
# resultant root on the half-axis occupied by the named inverse-ray arm.
ATLAS = {
    ("positive hard", "A"): [
        (box(-2528048, -2528045), [box(434313, 434317)]),
        (box(-1066969, -1066966), [box(1065094, 1065098)]),
    ],
    ("positive easy", "A"): [
        (box(61304, 61307), [box(1042162, 1042166)]),
        (box(205503, 205506), [box(-777762, -777757)]),
    ],
    ("negative hard", "A"): [],
    ("negative easy", "A"): [
        (box(-471598, -471595), [box(-848145, -848141), box(848141, 848145)]),
    ],
    ("positive hard", "B"): [
        (box(-2437249, -2437245), [box(-2725774, -2725769)]),
        (box(-2321124, -2321120), [box(-237167, -237162)]),
    ],
    ("positive easy", "B"): [
        (box(30267, 30270), [box(955878, 955883)]),
    ],
    ("negative hard", "B"): [
        (box(406104, 406108), [box(676272, 676277)]),
    ],
}


def algebra(spec: dict) -> tuple[sp.Expr, sp.Expr, object]:
    sigma = spec["sigma"]
    c = spec["c_exact"]
    s = spec["s_exact"]
    Aval = sp.expand(sigma * (c * D.subs(aa, sp.sqrt(5)) - s * I.subs(aa, sp.sqrt(5))))
    Bval = sp.expand(-sigma * (c * I.subs(aa, sp.sqrt(5)) + s * D.subs(aa, sp.sqrt(5))))
    domain = QQ.algebraic_field(sp.sqrt(5), c, s)
    return Aval, Bval, domain


def multiplicity_count(poly: sp.Poly, lo, hi) -> int:
    return sum(
        exponent * factor.count_roots(lo, hi)
        for factor, exponent in poly.sqf_list()[1]
    )


def krawczyk_pair(expr2: sp.Expr, spec: dict, pb: Iv, qb: Iv) -> bool:
    boxes = {aa: A5, cc: spec["c"], ss: spec["s"], p: pb, q: qb}
    sigma = spec["sigma"]
    if expr2 == D:  # not used; keeps the interface explicit
        second = D
    else:
        second = expr2
    funcs = (E, second)
    jac = ((sp.diff(E, p), sp.diff(E, q)), (sp.diff(second, p), sp.diff(second, q)))
    p0 = (pb.lo + pb.hi) / 2
    q0 = (qb.lo + qb.hi) / 2
    center_boxes = {aa: A5, cc: spec["c"], ss: spec["s"], p: Iv(p0), q: Iv(q0)}
    f0 = [eval_poly(f, center_boxes) for f in funcs]
    jmid = [[(eval_poly(jac[i][j], center_boxes).lo + eval_poly(jac[i][j], center_boxes).hi) / 2 for j in range(2)] for i in range(2)]
    det = jmid[0][0] * jmid[1][1] - jmid[0][1] * jmid[1][0]
    if det == 0:
        return False
    inv = ((jmid[1][1] / det, -jmid[0][1] / det), (-jmid[1][0] / det, jmid[0][0] / det))
    jbox = [[eval_poly(jac[i][j], boxes) for j in range(2)] for i in range(2)]
    radius = (Iv(pb.lo - p0, pb.hi - p0), Iv(qb.lo - q0, qb.hi - q0))
    kvals = []
    for i, x0 in enumerate((p0, q0)):
        base = Iv(x0) - inv[i][0] * f0[0] - inv[i][1] * f0[1]
        correction = Iv(0)
        for j in range(2):
            cij = Iv(1 if i == j else 0)
            cij -= inv[i][0] * jbox[0][j] + inv[i][1] * jbox[1][j]
            correction += cij * radius[j]
        kvals.append(base + correction)
    return pb.lo < kvals[0].lo <= kvals[0].hi < pb.hi and qb.lo < kvals[1].lo <= kvals[1].hi < qb.hi


def resultant_atlas(name: str, kind: str) -> tuple[bool, list[tuple[Iv, Iv, Iv]]]:
    spec = SPECS[name]
    Aval, Bval, domain = algebra(spec)
    exact_expr = Aval if kind == "A" else Bval
    interval_expr = sp.expand(
        spec["sigma"] * (cc * D - ss * I)
        if kind == "A"
        else -spec["sigma"] * (cc * I + ss * D)
    )
    f = sp.Poly(E.subs(aa, sp.sqrt(5)), p, q, domain=domain)
    g = sp.Poly(exact_expr, p, q, domain=domain)
    resultant = f.resultant(g)
    # The double hub at T=0 contributes a power of q to every resultant.
    # It is the excluded endpoint of either open ray, not a finite event.
    while resultant.eval(0) == 0:
        resultant = resultant.exquo(sp.Poly(q, q, domain=domain))
    rows = ATLAS[(name, kind)]
    half_lo, half_hi = (-sp.oo, 0) if name in ("positive hard", "negative easy") else (0, sp.oo)
    total = multiplicity_count(resultant, half_lo, half_hi)
    listed = 0
    events: list[tuple[Iv, Iv, Iv]] = []
    ok = True
    for qb, pboxes in rows:
        multiplicity = multiplicity_count(resultant, sp.Rational(qb.lo.numerator, qb.lo.denominator), sp.Rational(qb.hi.numerator, qb.hi.denominator))
        listed += multiplicity
        if multiplicity != len(pboxes):
            ok = False
        for pb in pboxes:
            if not krawczyk_pair(interval_expr, spec, pb, qb):
                ok = False
            base = {aa: A5, cc: spec["c"], ss: spec["s"], p: pb, q: qb}
            tbox = eval_poly(R, base)
            events.append((pb, qb, tbox))
    ok = ok and total == listed
    return ok, events


def exact_factorization_and_tracts() -> None:
    a = sp.sqrt(5)
    r = -(5 + sp.I * a) / 3
    mu = (-70 + 10 * sp.I * a) / 27
    x = sp.symbols("x")
    F = x**5 + 5 * x**4 + 10 * x**3 + (10 + mu) * x**2
    factor = sp.expand(F - x**2 * (x - r) ** 2 * (x + (5 - 2 * sp.I * a) / 3))
    uu = sp.symbols("u")
    normalized = sp.simplify(32 * F.subs(x, r * (uu + 1) / 2) / r**5)
    discr_v = sp.factor(sp.discriminant((uu**2 - 1) ** 2 * (uu + sp.I * a) - sp.symbols("v"), uu))
    # On a real nonzero ray the displayed discriminant cannot vanish: its
    # nonzero roots have nonzero imaginary part.  Axis equations keep the
    # chosen branches in their terminal sectors.
    axis_q = sp.factor(E.subs({aa: a, q: 0}))
    axis_p = sp.factor(E.subs({aa: a, p: 0}))
    lower_separator = sp.factor(E.subs({aa: a, q: -a}))
    lower_value = sp.simplify(R.subs({aa: a, q: -a, p: -sp.sqrt(6)}))
    zetas = (
        (1, -(1 + a) / 4 + sp.I * sp.sqrt(10 - 2 * a) / 4),
        (1, -(1 + a) / 4 - sp.I * sp.sqrt(10 - 2 * a) / 4),
        (-1, -1),
        (-1, (1 - a) / 4 + sp.I * sp.sqrt(10 + 2 * a) / 4),
    )
    ok = (
        factor == 0
        and sp.simplify(normalized - (uu**2 - 1) ** 2 * (uu + sp.I * a)) == 0
        and discr_v == sp.symbols("v") ** 2 * (3125 * sp.symbols("v") ** 2 - 14400 * sp.I * a * sp.symbols("v") - 55296)
        and axis_q == a * (p - 1) ** 2 * (p + 1) ** 2
        and axis_p == (q + a) * (q**2 + 1) ** 2
        and lower_separator == -4 * a * p**2 * (p**2 - 6)
        and lower_value == 120 * sp.sqrt(6)
        and all(sp.simplify(zeta**5 - sigma) == 0 for sigma, zeta in zetas)
    )
    report("1 exact mu-star factorization and collision-free ray tracts", ok, "four arms from u=-1; terminal sectors 4pi/5,6pi/5,pi,3pi/5")


def derivative_atlases() -> dict[str, list[tuple[Iv, Iv, Iv]]]:
    all_events: dict[str, list[tuple[Iv, Iv, Iv]]] = {}
    ok = radical_boxes_exact()
    details = []
    for name in SPECS:
        if name == "negative easy":
            # A-atlas below; B=-I is handled by its exact factorization.
            pass
        aok, aevents = resultant_atlas(name, "A")
        ok = ok and aok and not any(SPECS[name]["region"](*event) for event in aevents)
        details.append(f"{name}: A-events={len(aevents)}")
        if name != "negative easy":
            bok, bevents = resultant_atlas(name, "B")
            ok = ok and bok
            selected = [event for event in bevents if SPECS[name]["region"](*event)]
            expected = 1 if name == "positive hard" else 0
            ok = ok and len(selected) == expected
            all_events[name] = selected
            details[-1] += f", selected B-events={len(selected)}"
        else:
            # For zeta=-1 and sigma=-1, B=-I.  On the selected tract
            # p<-1 and -sqrt(5)<q<0.  The bracket in I can vanish together
            # with E only at the resultant ordinates q=-sqrt(5), -1/sqrt(5),
            # or q=0; the first/last are T=0 boundaries and the middle is the
            # terminal limit (no finite p-root).  Thus there is no finite turn.
            a = sp.sqrt(5)
            Bne = -I.subs(aa, a)
            e_poly = sp.Poly(E.subs(aa, a), p, q, extension=a)
            b_poly = sp.Poly(Bne, p, q, extension=a)
            rne = sp.factor(e_poly.resultant(b_poly).as_expr(), extension=a)
            q_terminal = -a / 5
            terminal_gcd = sp.gcd(
                sp.Poly(E.subs({aa: a, q: q_terminal}), p, extension=a),
                sp.Poly(Bne.subs(q, q_terminal), p, extension=a),
            )
            expected = (
                2560000
                * q**4
                * (q + a / 5) ** 2
                * (q + a)
                * (q**2 + 1) ** 2
                * (q**4 + 6 * a * q**3 / 5 + 3 * q**2 + 4 * a * q / 5 + sp.Rational(6, 5)) ** 2
            )
            residual_quartic = sp.Poly(
                q**4 + 6 * a * q**3 / 5 + 3 * q**2 + 4 * a * q / 5 + sp.Rational(6, 5),
                q,
                extension=a,
            )
            # q=-a is the zero P(-ia)=0; q=-a/5 is only a degree-drop
            # root at p=infinity (gcd 1), i.e. the terminal direction.
            ok = (
                ok
                and sp.expand(rne - expected) == 0
                and residual_quartic.count_roots(-sp.oo, sp.oo) == 0
                and terminal_gcd.degree() == 0
            )
            all_events[name] = []
            details[-1] += ", selected B-events=0"
    report("2 exact resultant atlases: A positive and only one selected V-turn", ok, "; ".join(details))
    return all_events


def endpoint_bounds(events: dict[str, list[tuple[Iv, Iv, Iv]]]) -> None:
    scale = S30 / 6
    ph_event = events["positive hard"][0]
    ph_spec = SPECS["positive hard"]
    vmax = eval_poly(cc * q - ss * (p + 1), {cc: ph_spec["c"], ss: ph_spec["s"], p: ph_event[0], q: ph_event[1]}) * scale

    def vinf(spec: dict) -> Iv:
        # Im(conj(zeta)(1-i sqrt(5)/5))*sqrt(30)/6.
        return scale * (-spec["s"] - spec["c"] * A5 / 5)

    vph = vinf(ph_spec)
    vpe = vinf(SPECS["positive easy"])
    vnh = vinf(SPECS["negative hard"])
    vne = vinf(SPECS["negative easy"])
    variation_ok = (
        vmax.hi < Q(7, 8)
        and vph.lo > Q(433, 500)
        and abs(vpe.lo) < Q(21, 100) and abs(vpe.hi) < Q(21, 100)
        and abs(vnh.lo) < Q(3, 4) and abs(vnh.hi) < Q(3, 4)
        and abs(vne.lo) < Q(5, 12) and abs(vne.hi) < Q(5, 12)
    )

    a = sp.sqrt(5)
    rho = (-5 - sp.I * a) / sp.sqrt(30)
    zph = -(1 + a) / 4 - sp.I * sp.sqrt(10 - 2 * a) / 4
    zpe = sp.conjugate(zph)
    znh = (1 - a) / 4 + sp.I * sp.sqrt(10 + 2 * a) / 4
    zne = -1
    proj_plus = sp.simplify(sp.re(rho * zph) + sp.re(rho * zpe))
    proj_minus = sp.simplify(sp.re(rho * znh) + sp.re(rho * zne))
    proj_ok = (
        sp.simplify(proj_plus - sp.sqrt(30) * (1 + a) / 12) == 0
        and bool(proj_plus > sp.Rational(147, 100))
        and bool(proj_minus > sp.Rational(47, 30))
    )

    # A>0 gives h<1.  Total variation is endpoint variation on monotone
    # arms and 2*Vmax-Vinf on the unique-turn arm.
    bend_plus = Q(2) * Q(7, 8) - Q(433, 500) + Q(21, 100)
    bend_minus = Q(3, 4) + Q(5, 12)
    plus_ceiling = bend_plus - Q(147, 100)
    minus_ceiling = bend_minus - Q(47, 30)
    final_ok = (
        variation_ok
        and proj_ok
        and bend_plus == Q(547, 500)
        and bend_minus == Q(7, 6)
        and plus_ceiling == -Q(47, 125)
        and minus_ceiling == -Q(2, 5)
        and plus_ceiling < -Q(3, 8)
        and minus_ceiling < -Q(3, 8)
    )
    report("3 exact endpoint variation and projection fan-in", final_ok, f"E+<-47/125, E-<-2/5; Vmax<{float(vmax.hi):.9f}")


def main() -> None:
    exact_factorization_and_tracts()
    events = derivative_atlases()
    endpoint_bounds(events)
    if FAILURES:
        print("FAILED:", ", ".join(FAILURES))
        raise SystemExit(1)
    print("PASS: exact mu-star endpoint excess certificate")


if __name__ == "__main__":
    main()
