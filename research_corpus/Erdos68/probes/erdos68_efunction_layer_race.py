#!/usr/bin/env python3
"""Erdos 68: the layering coordinate is a sum of E-function values, and the
Siegel-Shidlovskii route closes on an exponent race rather than on applicability.

`ErdosProblems/Erdos68/TranscendentalReframingLab.md` records identity (3),

        S = sum_{j>=1} sum_{n>=2} (n!)^{-j},

and then says of the ternary form (2) that "the third summand is not an
E-function value at an algebraic point, so the theorem does not apply as stated".
Reorganising (3) by layer shows that is not the obstruction.  Put

        E_j = sum_{n>=0} (n!)^{-j},        S = sum_{j>=1} (E_j - 2).

E_1 = e, E_2 = I_0(2), and in general E_j = 0F_{j-1}(;1,...,1;1) is the value of an
E-FUNCTION at z = 1.  So the third summand of (2) is sum_{j>=3}(E_j - 2): an
infinite sum of E-function values, not a non-E-function object.  Siegel-
Shidlovskii applies to every truncation.  The route fails for a different and
quantitative reason.

Truncating at J,

        S - sum_{j<=J}(E_j - 2) = R_J = sum_{n>=2} (n!)^{-J}/(n! - 1),   |R_J| ~ 2^{-J},

so if S = p/q the integer linear form

        L_J = q * sum_{j<=J} E_j - (p + 2 J q)

has |L_J| = q|R_J| ~ q 2^{-J} with coefficient height H ~ q(1 + 2J).  A
Shidlovskii-type linear independence measure |L| >> H^{-kappa(J)} closes the
route only if q 2^{-J} << H^{-kappa(J)}, i.e. only if 2^J beats q^{kappa(J)}.
With kappa(J) growing linearly in J -- the generic shape for J E-functions --
the right-hand side is q^J, and q^J beats 2^J for every q >= 3.

The packet's own certified bound q > 1e12039 makes the race hopeless by roughly
12039 orders of magnitude per layer.

This probe checks the coordinate and then evaluates the race.  It proves no
irrationality; it retires a reason, not a route's conclusion.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys

from mpmath import mp


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dps", type=int, default=120)
    ap.add_argument("--layers", type=int, default=20)
    ap.add_argument("--q-exponent", type=int, default=12039,
                    help="certified denominator lower bound exponent from the packet")
    ap.add_argument("--receipt", type=str, default=None)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    mp.dps = args.dps

    def E(j: int, terms: int = 220):
        return mp.nsum(lambda n: mp.mpf(1) / mp.factorial(int(n)) ** j, [0, terms])

    S = mp.nsum(lambda n: mp.mpf(1) / (mp.factorial(int(n)) - 1), [2, 200])
    e_gap = abs(E(1) - mp.e)
    bessel_gap = abs(E(2) - mp.besseli(0, 2))

    rows, acc = [], mp.mpf(0)
    for J in range(1, args.layers + 1):
        acc += E(J) - 2
        R = S - acc
        rows.append({"J": J, "partial": mp.nstr(acc, 22), "R_J": mp.nstr(R, 10),
                     "R_J_times_2^J": float(R * 2 ** J)})

    q = mp.mpf(10) ** args.q_exponent
    race = []
    for J in (100, 1000, 10000, 4 * args.q_exponent):
        lhs = q * mp.mpf(2) ** (-J)
        H = q * (1 + 2 * J)
        rhs = H ** (-mp.mpf(J))
        race.append({"J": J, "linear_form_size": mp.nstr(lhs, 4),
                     "measure_bound": mp.nstr(rhs, 4), "closes": bool(lhs < rhs)})

    ok = (e_gap < mp.mpf(10) ** (-args.dps + 20)
          and bessel_gap < mp.mpf(10) ** (-args.dps + 20)
          and abs(rows[-1]["R_J_times_2^J"] - 1.0) < 1e-6
          and not any(r["closes"] for r in race))

    receipt = {
        "problem_id": "erdos_68",
        "probe": "erdos68_efunction_layer_race",
        "corrects": "TranscendentalReframingLab.md: the third summand of identity (2) "
                    "IS a sum of E-function values, namely sum_{j>=3}(E_j-2); "
                    "Siegel-Shidlovskii is applicable to every truncation",
        "coordinate": "S = sum_{j>=1} (E_j - 2), E_j = 0F_{j-1}(;1,..,1;1) at z=1",
        "S": mp.nstr(S, 30),
        "E1_minus_e": mp.nstr(e_gap, 6),
        "identification_tolerance": mp.nstr(mp.mpf(10) ** (-args.dps + 20), 4),
        "E2_minus_besselI0_2": mp.nstr(bessel_gap, 6),
        "tail_law": "R_J * 2^J -> 1",
        "layers": rows,
        "denominator_exponent_used": args.q_exponent,
        "exponent_race": race,
        "verdict": "the route is blocked by the exponent race q^kappa(J) vs 2^J, "
                   "not by inapplicability of Siegel-Shidlovskii",
        "claim_boundary": "no irrationality proved; this retires a stated reason and "
                          "replaces it with a quantitative one",
        "status": "pass" if ok else "fail",
    }
    if args.receipt:
        p = pathlib.Path(args.receipt)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(f"S = {mp.nstr(S, 30)}")
        print(f"E_1 - e         = {mp.nstr(e_gap, 6)}")
        print(f"E_2 - I_0(2)    = {mp.nstr(bessel_gap, 6)}")
        print("\n   J   partial sum              R_J            R_J * 2^J")
        for r in rows:
            if r["J"] in (1, 2, 3, 5, 8, 12, 16, args.layers):
                print(f" {r['J']:3d}   {r['partial']:>24}  {r['R_J']:>16}  "
                      f"{r['R_J_times_2^J']:.7f}")
        print(f"\nexponent race against q > 1e{args.q_exponent}")
        for r in race:
            print(f"   J={r['J']:<7} |L_J| ~ {r['linear_form_size']:>12}   "
                  f"H^-J ~ {r['measure_bound']:>14}   closes? "
                  f"{'YES' if r['closes'] else 'no'}")
        print(f"status : {receipt['status']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
