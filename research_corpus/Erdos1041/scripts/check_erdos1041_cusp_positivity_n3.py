#!/usr/bin/env python3
"""Proof certificate for kappa_3 > 0: the near-Fekete cusp law at the binding degree.

`NearFeketeCuspLaw.md` reduces the near-Fekete half of Erdős #1041 to the
parameter-free inequality ``ex_1 + ex_2 < 2`` on the fixed near-field model
``g(zeta) = zeta^n + n zeta``, equivalently ``D_1 + D_2 < cos(gamma_1) + cos(gamma_2)``,
and records the binding degree as ``n = 3``, where the right-hand side is
``sqrt(3)/2``.  It lists a proof of ``kappa_n > 0`` under "Not established", and
names the missing tool: "a proof needs the hypotenuse, i.e. a genuine L^2
estimate on dY/dX".

This script certifies that proof at ``n = 3``.

Step 1 (exact algebra).  A descending branch satisfies ``Im g = Im(2i) = 2``,
i.e. ``3 X^2 Y - Y^3 + 3 Y = 2``.  Since ``Y^3 - 3Y + 2 = (Y-1)^2 (Y+2)``,

    X(Y) = (1 - Y) sqrt( (Y+2) / (3Y) ),        Y > 0,

so BOTH branches are one explicit algebraic graph over ``Y``: branch 1 is
``Y: 1 -> 0`` (exit direction ``alpha = 0``) and branch 2 is ``Y: 1 -> oo``
(exit direction ``alpha = 2 pi / 3``).  Differentiating,

    X'(Y) = -(Y^2 + Y + 1) / (sqrt(3) Y^{3/2} sqrt(Y+2))   < 0.

Step 2 (the L^2 estimate).  In the exit-aligned frame ``eta = e^{-i alpha} z = P + iQ``,
``P`` is monotone along each branch and ``P(start) = cos(gamma)``.  From
``sqrt(dP^2 + dQ^2) <= dP + dQ^2/(2 dP)`` and ``r = |eta| >= P``,

    ex = int (dl - dr) <= 1 - cos(gamma) + (1/2) int (dQ)^2 / dP,

and since ``ex = 1 - cos(gamma) + D`` exactly, ``D <= (1/2) int (dQ)^2 / dP``.

Step 3 (two elementary bounds).
  branch 1 (``P = X``, ``Q = Y``): the integrand is
  ``1/|X'| = sqrt(3) Y^{3/2} sqrt(Y+2) / (Y^2+Y+1) <= 3 Y^{3/2}`` on ``[0,1]``,
  so ``I_1 <= 6/5`` and ``D_1 <= 3/5``.

  branch 2: ``dP/dY = (sqrt(3) + |X'|)/2 >= sqrt(3)/2`` and
  ``dQ/dY = (sqrt(3)|X'| - 1)/2 = N / (2 Y^{3/2} sqrt(Y+2))`` with
  ``N = (3Y^2+2Y+1) / (Y^2+Y+1+sqrt(Y^4+2Y^3)) <= 3/2`` for ``Y >= 1``
  (equivalent to ``12Y^3 + 5Y^2 + 2Y - 1 >= 0``).  With ``Y + 2 >= 3``,
  ``I_2 <= (3/(8 sqrt 3)) int_1^oo Y^{-3} dY = sqrt(3)/16`` and ``D_2 <= sqrt(3)/32``.

Conclusion.  ``kappa_3 = (cos g_1 + cos g_2) - (D_1 + D_2) >= 15 sqrt(3)/32 - 3/5 > 0``.

Scope.  This is the ``phi = 0`` (aligned) ray direction at ``n = 3``.
`NearFeketeCuspLaw.md` measures that direction as ``min_phi kappa_3`` and ``n = 3``
as the binding degree, but both of those are measurements, so what is proved here
is positivity at the measured-worst instance, not the whole near-Fekete half.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

import mpmath as mp


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)

SOURCE_REF = (
    "research_corpus/Erdos1041/"
    "scripts/check_erdos1041_cusp_positivity_n3.py"
)
ANALYSIS_REF = (
    "research_corpus/Erdos1041/"
    "NearFeketeCuspPositivityProof.md"
)
PACKET_REF = (
    "research_corpus/Erdos1041/"
    "research_packet.json"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "source-provenance://private-authoring-project/receipts/"
    "erdos1041_cusp_positivity_n3_receipt.json"
)

mp.mp.dps = 40


def branch_x(y):
    return (1 - y) * mp.sqrt((y + 2) / (3 * y))


def branch_xprime(y):
    return -(y**2 + y + 1) / (mp.sqrt(3) * y ** mp.mpf(1.5) * mp.sqrt(y + 2))


def verify_curve() -> dict[str, Any]:
    """The graph really is the branch set: Im g = 2 identically, and X' is the derivative."""
    worst_im = mp.mpf(0)
    for k in range(1, 400):
        y = mp.mpf(k) / 40
        z = mp.mpc(branch_x(y), y)
        worst_im = max(worst_im, abs(mp.im(z**3 + 3 * z) - 2))
    h = mp.mpf("1e-20")
    worst_dx = mp.mpf(0)
    for k in range(1, 200):
        y = mp.mpf(k) / 40
        num = (branch_x(y + h) - branch_x(y - h)) / (2 * h)
        worst_dx = max(worst_dx, abs(num - branch_xprime(y)))
    return {
        "max_abs_deviation_of_Im_g_from_2": mp.nstr(worst_im, 8),
        "max_abs_deviation_of_closed_form_derivative": mp.nstr(worst_dx, 8),
    }


def measured_constants() -> dict[str, Any]:
    """ex_i = int (dl - dr); reproduces NearFeketeCuspLaw.md's recorded constants."""
    arc = lambda y: mp.sqrt(1 + branch_xprime(y) ** 2)  # noqa: E731
    rad = lambda y: mp.sqrt(branch_x(y) ** 2 + y**2)  # noqa: E731
    tiny, big = mp.mpf("1e-14"), mp.mpf("1e14")
    ex1 = mp.quad(arc, [tiny, 1]) - (rad(tiny) - 1)
    ex2 = mp.quad(arc, [1, big]) - (rad(big) - 1)
    g1, g2 = mp.pi / 2, -mp.pi / 6
    d1 = ex1 - (1 - mp.cos(g1))
    d2 = ex2 - (1 - mp.cos(g2))
    return {
        "ex_1": mp.nstr(ex1, 10),
        "ex_2": mp.nstr(ex2, 10),
        "kappa_3": mp.nstr(2 - (ex1 + ex2), 10),
        "kappa_3_recorded_in_analysis": "0.6080213113",
        "D_1": mp.nstr(d1, 10),
        "D_2": mp.nstr(d2, 10),
        "D_sum": mp.nstr(d1 + d2, 10),
        "target_cos_g1_plus_cos_g2": mp.nstr(mp.cos(g1) + mp.cos(g2), 10),
    }


def proof_chain() -> dict[str, Any]:
    """Each bound is checked against the quantity it bounds; the final chain is exact."""
    # sharp L^2 integrals
    i1 = mp.quad(lambda y: 1 / abs(branch_xprime(y)), [0, 1])
    cs, sn = mp.cos(2 * mp.pi / 3), mp.sin(2 * mp.pi / 3)
    dp = lambda y: cs * branch_xprime(y) + sn  # noqa: E731
    dq = lambda y: -sn * branch_xprime(y) + cs  # noqa: E731
    i2 = mp.quad(lambda y: dq(y) ** 2 / dp(y), [1, mp.inf])

    con = measured_constants()
    d1, d2 = mp.mpf(con["D_1"]), mp.mpf(con["D_2"])
    assert d1 <= i1 / 2, "L2 bound fails on branch 1"
    assert d2 <= i2 / 2, "L2 bound fails on branch 2"

    # monotonicity of P on each branch
    assert all(branch_xprime(mp.mpf(k) / 200) < 0 for k in range(1, 201)), "P not monotone, branch 1"
    assert all(dp(1 + mp.mpf(k) / 20) > 0 for k in range(0, 4000)), "P not monotone, branch 2"

    # N(Y) <= 3/2 on [1, oo)  <=>  12Y^3 + 5Y^2 + 2Y - 1 >= 0, true termwise for Y >= 1
    nfun = lambda y: (3 * y**2 + 2 * y + 1) / (y**2 + y + 1 + mp.sqrt(y**4 + 2 * y**3))  # noqa: E731
    n_max = max(nfun(1 + mp.mpf(k) / 20) for k in range(0, 8000))
    assert n_max <= mp.mpf(1.5), "N exceeds 3/2"

    # crude bounds, then the exact rational/surd conclusion
    assert i1 <= mp.mpf(6) / 5, "I1 crude bound fails"
    assert i2 <= mp.sqrt(3) / 16, "I2 crude bound fails"
    bound_d1 = Fraction(3, 5)                      # I1/2 <= 3/5
    lower = mp.mpf(15) * mp.sqrt(3) / 32 - mp.mpf(3) / 5
    assert lower > 0, "final chain fails"
    return {
        "I_1_sharp": mp.nstr(i1, 10),
        "I_2_sharp": mp.nstr(i2, 10),
        "L2_bound_on_D_sum": mp.nstr((i1 + i2) / 2, 10),
        "crude_I_1_bound": "6/5",
        "crude_D_1_bound": str(bound_d1),
        "crude_I_2_bound": "sqrt(3)/16",
        "crude_D_2_bound": "sqrt(3)/32",
        "max_N_on_branch_2": mp.nstr(n_max, 10),
        "kappa_3_lower_bound_closed_form": "15*sqrt(3)/32 - 3/5",
        "kappa_3_lower_bound_value": mp.nstr(lower, 12),
        "kappa_3_true_value": measured_constants()["kappa_3"],
        "positive": True,
    }


def l2_reach_by_degree(max_degree: int = 12) -> list[dict[str, Any]]:
    """Is Lemma 2 strong enough at degrees above three?

    Traces the branches of g(z) = z^n + n z by Newton continuation in s (an
    implementation independent of the n=3 algebraic graph) and compares
    (I_1 + I_2)/2 against cos(gamma_1) + cos(gamma_2).
    """
    rows: list[dict[str, Any]] = []
    for n in range(3, max_degree + 1):
        zc = mp.exp(1j * mp.pi / (n - 1))
        v = (n - 1) * zc
        g = lambda z: z**n + n * z  # noqa: E731
        gp = lambda z: n * (z ** (n - 1) + 1)  # noqa: E731
        gpp = lambda z: n * (n - 1) * z ** (n - 2)  # noqa: E731
        per_branch = []
        for sign in (+1, -1):
            s = mp.mpf("1e-18")
            z = zc + sign * mp.sqrt(2 * s / gpp(zc))
            pts = []
            while s < mp.mpf(10) ** 12:
                for _ in range(60):
                    step = (g(z) - (v + s)) / gp(z)
                    z -= step
                    if abs(step) < mp.mpf("1e-28"):
                        break
                pts.append((s, z))
                s *= mp.mpf("1.15")
            k = int(mp.nint(mp.arg(pts[-1][1]) * n / (2 * mp.pi))) % n
            alpha = 2 * mp.pi * k / n
            ea = mp.exp(-1j * alpha)
            integral = mp.mpf(0)
            for i in range(len(pts) - 1):
                ds = pts[i + 1][0] - pts[i][0]
                mid = (pts[i][1] + pts[i + 1][1]) / 2
                w = ea / (n * (mid ** (n - 1) + 1))
                dp_, dq_ = mp.re(w), mp.im(w)
                if dp_ <= 0:
                    dp_ = mp.mpf("1e-40")
                integral += dq_ * dq_ / dp_ * ds
            gam = mp.arg(zc) - alpha
            per_branch.append((mp.atan2(mp.sin(gam), mp.cos(gam)), integral))
        target = sum(mp.cos(gm) for gm, _ in per_branch)
        bound = sum(it for _, it in per_branch) / 2
        rows.append(
            {
                "n": n,
                "target_cos_g1_plus_cos_g2": mp.nstr(target, 8),
                "L2_bound_on_D_sum": mp.nstr(bound, 8),
                "suffices": bool(bound < target),
                "margin_factor": mp.nstr(target / bound, 5),
            }
        )
    assert all(r["suffices"] for r in rows), "L2 estimate insufficient at some degree"
    return rows


def build_receipt() -> dict[str, Any]:
    contract = build_experiment_contract(
        problem_id="erdos_1041",
        target_statement=(
            "Join two roots by a curve of length less than two inside the "
            "strict unit lemniscate."
        ),
        claim_ceiling=(
            "Proves kappa_3 > 0 at the aligned ray direction, the measured-worst "
            "instance of the near-Fekete cusp law. Does not prove the near-Fekete "
            "half for all degrees or all directions, and does not prove Erdős #1041."
        ),
        hypothesis_id="near_fekete_cusp_positivity_binding_case",
        hypothesis_statement=(
            "For the near-field model g(zeta) = zeta^3 + 3 zeta, the two descending "
            "branches at a hub satisfy ex_1 + ex_2 < 2, equivalently "
            "D_1 + D_2 < sqrt(3)/2, so the regular polygon is a strict local maximum "
            "of min_c L(c)/(2R) at degree three."
        ),
        probe_id="algebraic_branch_plus_l2_turning_estimate",
        probe_question=(
            "Does the explicit algebraic form of the degree-three branch make the "
            "L^2 turning estimate strong enough to prove kappa_3 > 0?"
        ),
        computation=(
            "Solve Im g = 2 for X as an explicit algebraic graph over Y, verify it "
            "against the model, then check the L^2 chord-deficit bound and the two "
            "elementary integral bounds that close it."
        ),
        falsifier=(
            "Any branch point off the curve Im g = 2, a non-monotone P, an L^2 bound "
            "below the true deficit, or a final chain reaching sqrt(3)/2."
        ),
        stop_condition=(
            "Stop once the closed-form lower bound 15 sqrt(3)/32 - 3/5 is positive."
        ),
        survival_consequence=(
            "kappa_3 > 0 becomes a theorem rather than a measurement, removing one "
            "named gap from NearFeketeCuspLaw.md."
        ),
        falsification_consequence=(
            "The L^2 estimate would be too lossy even in the algebraic case, and the "
            "near-Fekete half would need the curvature bound on R(t) instead."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[ANALYSIS_REF],
        source_refs=[SOURCE_REF, ANALYSIS_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The degree-three descending branches lie on the explicit curve "
            "X = (1-Y) sqrt((Y+2)/(3Y)); the L^2 chord-deficit estimate then gives "
            "kappa_3 >= 15 sqrt(3)/32 - 3/5 = 0.2119 > 0."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos1041-cusp-positivity-n3/1",
        "status": "verified_proof_of_binding_case",
        "experiment_contract": contract,
        "curve_verification": verify_curve(),
        "constants": measured_constants(),
        "proof_chain": proof_chain(),
        "l2_reach_by_degree": l2_reach_by_degree(),
        "consequence_decisions": [
            {"mechanism": "kappa_3_positivity_aligned_direction", "decision": "proved"},
            {"mechanism": "kappa_n_positivity_all_n_all_directions", "decision": "open"},
            {"mechanism": "D_bounded_away_from_1_regime", "decision": "untouched"},
            {"mechanism": "erdos_1041", "decision": "not_claimed"},
        ],
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
            source_record(REPO_ROOT, PACKET_REF),
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True)
    if check:
        if not output.exists():
            print(f"missing receipt: {output}", file=sys.stderr)
            return 1
        if output.read_text(encoding="utf-8").strip() != rendered.strip():
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(f"receipt current: {output}")
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered + "\n", encoding="utf-8")
    print(f"wrote {output}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    return emit(build_receipt(), args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
