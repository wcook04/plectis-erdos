#!/usr/bin/env python3
"""Exact certificate for the noncanonical ``mu=-10`` wall-limit arm.

The canonical limiting pair at the two nonzero-gap wall phases was already
certified by ``check_erdos1041_quintic_minus_ten_endpoint_excess.py``.  A
wall sheet can approach the triple hub through either of two other lobes,
and both new pairings contain the same shallow arm (up to conjugation).

This checker proves that arm has excess below ``-13/15``.  It uses exact
rational interval signs only to isolate the algebraic endpoints and one
orientation witness.  Global monotonicity follows from a degree-110 Sturm
certificate, not from a numerical mesh.
"""

from __future__ import annotations

from fractions import Fraction as Qq
import importlib.util
from pathlib import Path

import sympy as sp


ENDPOINT = Path(__file__).with_name(
    "check_erdos1041_quintic_minus_ten_endpoint_excess.py"
)
SPEC = importlib.util.spec_from_file_location("minus_ten_endpoint", ENDPOINT)
M = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(M)

Iv = M.Iv
poly_iv = M.poly_iv

q, k, t, w = M.q, M.k, M.t, M.w
Scurve, Sw, St, D = M.Scurve, M.Sw, M.St, M.D

FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


QNEG = Iv(-M.Q0.hi, -M.Q0.lo)
RBOX = Iv(
    Qq(8789971897990956, 10**15),
    Qq(8789971897990957, 10**15),
)
KBOX = Iv(
    Qq(14690277053249349, 10**15),
    Qq(14690277053249350, 10**15),
)

RSTART = sp.expand(t**6 - 78 * t**4 + 57 * t**2 - 8)
KTERM = sp.expand(M.KPOLY.subs(k, t))


def exact_endpoint_isolation() -> None:
    """Isolate the cubic start and monic-tract terminal directions."""

    r = sp.symbols("r", real=True)
    q_from_r = -(3 * r**2 - 1) / (r**3 - 3 * r)
    q_from_k = -M.A0k / M.A1k

    start_identity = sp.factor(
        (r**3 - 3 * r) ** 2 * (8 * q_from_r**2 - 1)
        + RSTART.subs(t, r)
    )
    terminal_identity = sp.factor(
        M.A1k**2 * (8 * q_from_k**2 - 1) - M.KPOLY
    )
    start_curve_identity = sp.factor(
        (q * (t**3 - 3 * t) + 3 * t**2 - 1).subs(
            {q: q_from_r, t: r}
        )
    )

    r_count = sp.count_roots(sp.Poly(RSTART, t), RBOX.lo, RBOX.hi)
    k_count = sp.count_roots(sp.Poly(KTERM, t), KBOX.lo, KBOX.hi)

    recovered_r = -(3 * RBOX**2 - 1) / (RBOX**3 - 3 * RBOX)
    recovered_k = -poly_iv(M.A0k, {k: KBOX}) / poly_iv(M.A1k, {k: KBOX})
    overlap_r = recovered_r.lo <= QNEG.hi and QNEG.lo <= recovered_r.hi
    overlap_k = recovered_k.lo <= QNEG.hi and QNEG.lo <= recovered_k.hi

    report(
        "1 exact shallow start and terminal directions",
        start_identity == 0
        and terminal_identity == 0
        and start_curve_identity == 0
        and r_count == 1
        and k_count == 1
        and recovered_r.hi < 0
        and recovered_k.hi < 0
        and overlap_r
        and overlap_k
        and RBOX.lo > 8
        and KBOX.lo > 14,
        "r in (8.789971897990956,8.789971897990957); "
        "k in (14.690277053249349,14.690277053249350); q=-1/(2sqrt(2))",
    )


def global_branch_certificate() -> None:
    """Prove that exactly one positive root joins w=0 to w=1."""

    H = q * (t**3 - 3 * t) + 3 * t**2 - 1
    Ht = sp.diff(H, t)
    H1 = (
        k**2 * q
        + 3 * k * q * t
        + 5 * k
        + 6 * q * t**2
        - 10 * q
        + 15 * t
    )
    lead = -D

    s0_identity = sp.expand(Scurve.subs(w, 0) - 10 * (k - t) * H)
    s1_identity = sp.expand(Scurve.subs(w, 1) + (k - t) ** 2 * H1)

    # Natural interval evaluation is very sharp here.  The subdivision is
    # only a coefficient-sign certificate; it does not trace the root.
    lo, hi = RBOX.lo, KBOX.hi
    cells = 128
    signs_ok = True
    hp_upper = None
    h1_upper = None
    lead_lower = None
    for index in range(cells):
        t_box = Iv(
            lo + Qq(index, cells) * (hi - lo),
            lo + Qq(index + 1, cells) * (hi - lo),
        )
        boxes = {q: QNEG, k: KBOX, t: t_box}
        hp_box = poly_iv(Ht, boxes)
        h1_box = poly_iv(H1, boxes)
        lead_box = poly_iv(lead, boxes)
        hp_upper = hp_box.hi if hp_upper is None else max(hp_upper, hp_box.hi)
        h1_upper = h1_box.hi if h1_upper is None else max(h1_upper, h1_box.hi)
        lead_lower = (
            lead_box.lo if lead_lower is None else min(lead_lower, lead_box.lo)
        )
        signs_ok = signs_ok and hp_box.hi < 0 and h1_box.hi < 0 and lead_box.lo > 0

    # H(r)=0 and H'<0 imply S(t,0)<0.  H1<0 gives S(t,1)>0.
    # Since the leading coefficient is positive, the two real roots have
    # opposite signs.  Thus there is exactly one positive root, it lies in
    # (0,1), is simple with S_w>0, and tends to 0 and 1 at the endpoints.
    report(
        "2 exact global positive-root branch",
        s0_identity == 0
        and s1_identity == 0
        and signs_ok
        and hp_upper is not None
        and hp_upper < 0
        and h1_upper is not None
        and h1_upper < 0
        and lead_lower is not None
        and lead_lower > 0,
        "128 exact coefficient cells: H'<0, H1<0, lead_w2>0; unique 0<w<1",
    )


def exact_monotonicity_certificate() -> None:
    """Exclude every turn of the selected branch by exact elimination."""

    eliminant = M.stationary_eliminant()
    terminal_factor = sp.Poly(KTERM, t)
    quotient, remainder = sp.div(eliminant, terminal_factor)

    broad_lo = sp.Rational(87899, 10000)
    broad_hi = sp.Rational(147, 10)
    full_count = sp.count_roots(eliminant, broad_lo, broad_hi)
    terminal_count = sp.count_roots(terminal_factor, broad_lo, broad_hi)
    quotient_count = sp.count_roots(quotient, broad_lo, broad_hi)

    # Orient the derivative at one rational section of the globally unique
    # root.  Exact endpoint signs isolate it in (0.430,0.433).
    t_box = Iv(Qq(10))
    w_box = Iv(Qq(43, 100), Qq(433, 1000))
    base = {q: QNEG, k: KBOX, t: t_box}
    s_lo = poly_iv(Scurve, {**base, w: Iv(w_box.lo)})
    s_hi = poly_iv(Scurve, {**base, w: Iv(w_box.hi)})
    sw_box = poly_iv(Sw, {**base, w: w_box})
    st_box = poly_iv(St, {**base, w: w_box})

    # The only zero of the full degree-120 eliminant in the broad interval
    # is the isolated terminal zero of K.  Hence the interior selected branch
    # has no w_t=0.  The witness has w_t=-S_t/S_w>0, so w increases globally.
    report(
        "3 degree-110 Sturm monotonicity certificate",
        remainder.is_zero
        and eliminant.degree() == 120
        and terminal_factor.degree() == 10
        and quotient.degree() == 110
        and full_count == 1
        and terminal_count == 1
        and quotient_count == 0
        and s_lo.hi < 0 < s_hi.lo
        and sw_box.lo > 0
        and st_box.hi < 0,
        "K divides degree 120; quotient has 0 roots on [8.7899,14.7]; w_t>0 at t=10",
    )


def exact_inverse_ray_orientation() -> None:
    """Identify the glued graph with the outward inverse-ray lift."""

    b = M.b
    x = sp.symbols("x")
    F = sp.expand(x**3 * (x**2 + 5 * x + 10))
    factor_identity = sp.expand(
        Scurve.subs(w, b * (k - t))
        - (k - t) * M.Qcurve
        - b**2 * (t - k) * M.Ak
    )
    terminal_identity = sp.expand(
        M.B.subs(t, k) - sp.diff(M.A, t).subs(t, k)
    )
    derivative_identity = sp.expand(
        sp.diff(F, x) - 5 * x**2 * (x**2 + 4 * x + 6)
    )

    upper_zero = (-5 + sp.I * sp.sqrt(15)) / 2
    upper_critical = -2 + sp.I * sp.sqrt(2)
    zero_ok = (
        sp.simplify(upper_zero**2 + 5 * upper_zero + 10) == 0
        and sp.simplify(sp.re(upper_zero) / sp.im(upper_zero) + 5 / sp.sqrt(15))
        == 0
        and bool(5 / sp.sqrt(15) > 1)
    )
    critical_ok = (
        sp.simplify(upper_critical**2 + 4 * upper_critical + 6) == 0
        and sp.simplify(
            sp.re(upper_critical) / sp.im(upper_critical) + sp.sqrt(2)
        )
        == 0
        and bool(sp.sqrt(2) > 1)
    )
    initial_projection = poly_iv(t**3 - 3 * t, {t: RBOX})

    # All nonzero zeros and critical points have t-coordinate below -1,
    # whereas this graph has t>8.  Near its cubic start the ray scalar is
    # positive.  Global w_t>0 gives b_t>0; hence x_t is nonzero.  Since F'
    # is also nonzero, the ray scalar derivative cannot vanish, so the graph
    # is the outward lift rather than the opposite algebraic ray component.
    report(
        "4 exact outward inverse-ray orientation",
        factor_identity == 0
        and terminal_identity == 0
        and derivative_identity == 0
        and zero_ok
        and critical_ok
        and RBOX.lo > 8
        and initial_projection.lo > 0,
        "all nonzero zeros/critical points have t<-1; initial ray scalar positive",
    )


def exact_excess_fanin() -> None:
    """Convert monotonicity into the arm and three-pair inequalities."""

    # On the selected branch S_w>0, S_t<0 and 0<w<1.  Therefore
    # Y=w*S_w-(k-t)*S_t>0 and the physical slope
    # p=t+w(k-t)S_w/Y is greater than t>0.  Its dot product with the
    # terminal direction (k,1) is positive, so h=tan(|theta|/2)<1.
    # Since w increases from 0 to 1, J=int h dw<1.
    # The support identity from the endpoint certificate then gives
    #   e0 <= (J-k)/sqrt(1+k^2)
    #      < -(k-1)/(k+1) < -13/15,
    # with the final comparison exactly equivalent to k>14.
    k_lower = KBOX.lo
    ratio_lower = (k_lower - 1) / (k_lower + 1)
    shallow_ceiling = -Qq(13, 15)

    # The existing endpoint theorem supplies e_-<1/10 and e_+<-9/80.
    canonical_pair = Qq(1, 10) - Qq(9, 80)
    side_pair_a = shallow_ceiling + Qq(1, 10)
    side_pair_b = shallow_ceiling - Qq(9, 80)
    p = sp.symbols("p", positive=True, real=True)
    kk = sp.symbols("kk", positive=True, real=True)
    acute_identity = sp.expand(
        (1 + p**2) * (1 + kk**2) - (kk - p) ** 2 - (1 + p * kk) ** 2
    )
    report(
        "5 exact shallow-arm and all wall-limit pair fan-in",
        k_lower > 14
        and ratio_lower > Qq(13, 15)
        and acute_identity == 0
        and canonical_pair == -Qq(1, 80)
        and side_pair_a == -Qq(23, 30)
        and side_pair_b == -Qq(47, 48),
        "e0<-13/15; pair ceilings -1/80, -23/30, -47/48",
    )


def main() -> int:
    exact_endpoint_isolation()
    global_branch_certificate()
    exact_monotonicity_certificate()
    exact_inverse_ray_orientation()
    exact_excess_fanin()
    if FAILURES:
        print(f"FAILED {len(FAILURES)} section(s): {', '.join(FAILURES)}")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
