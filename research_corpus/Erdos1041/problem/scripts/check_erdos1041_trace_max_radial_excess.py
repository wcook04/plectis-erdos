"""Checker for TraceMaxRadialExcessLaw.md (Erdos 1041).

Reproduces the load-bearing rows of the computational law:
  1  the orbit stratum row: at the tangent representative
     (b1 = (3/4) 5^{-1/3} e^{i pi/5}, b2 = e^{9 i pi/10}) the skip-pair
     hub's RIGHTWARD arms have excess ~ 0.04149 against slack
     0.0777593 (clearance ~1.87), matching the landed table;
  2  the radial refutation witness at eps = 1e-2: E_radial = +0.2276,
     E_rightward = -0.0377 (tolerance 2e-3);
  3  one-face constancy: on b2 = 0 the radial pair excess equals the
     one-face constant -0.8796 at three phases (tolerance 1e-3);
  4  blocked ray at the orbit: the two non-hub critical values are
     equal and collinear with the small hub's value (ratio real > 1);
  5  rightward global spot-battery: 400 random core points, all
     E_rightward < 0; report the max (expect <= -0.036 + noise).

Instrument: fibre tracking by nearest-root selection on graded meshes
(float64; adequate at the stated tolerances; the owner note's 30-dps
rows are the authority).

Exit 0 iff all pass.
"""
import sys

import numpy as np

rng = np.random.default_rng(31)
FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def H_of(z, b1, b2):
    return z**5 + b2 * z**2 + b1 * z


def crits(b1, b2):
    return np.roots([5, 0, 0, 2 * b2, b1])


def pair_excess(b1, b2, c, ray="right", smax=2.0e7, nstep=2600):
    """Excess sum for the two arms of hub c along the given value ray."""
    v = H_of(c, b1, b2)
    H2 = 20 * c**3 + 2 * b2

    def ray_pt(s):
        if ray == "right":
            return v + s
        return v * (1 + s / max(abs(v), 1e-300))  # radial: t = 1 + s/|v|

    dirv = 1.0 if ray == "right" else v / abs(v)
    total = 0.0
    for sgn in (1, -1):
        s0 = 1e-12 * max(1.0, abs(H2))
        z = c + sgn * np.sqrt(2 * (ray_pt(s0) - v) / H2)
        length = abs(z - c)
        ss = np.geomspace(s0, smax, nstep)
        for s in ss[1:]:
            w = ray_pt(s)
            fib = np.roots([1, 0, 0, b2, b1, -w])
            zn = fib[np.argmin(np.abs(fib - z))]
            length += abs(zn - z)
            z = zn
        total += length - abs(z)
    return total  # sum over arms of lim (length_from_hub - |z|)


def trace_max_hub(b1, b2):
    cs = crits(b1, b2)
    vals = H_of(cs, b1, b2)
    return cs[np.argmax(vals.real)]


def main():
    # orbit representative
    b1o = 0.75 * 5 ** (-1 / 3) * np.exp(1j * np.pi / 5)
    b2o = np.exp(9j * np.pi / 10)

    # 1 stratum row (skip-pair hub = smallest-|c| critical point)
    cs = crits(b1o, b2o)
    c_small = cs[np.argmin(np.abs(cs))]
    E_right = pair_excess(b1o, b2o, c_small, "right")
    slack = 0.0777592874
    exc = E_right + slack  # e_i+e_j = exc - slack in the corpus split
    ok1 = abs(E_right - (-0.0362736)) < 2e-3 and abs(exc - 0.0414856) < 2.5e-3
    report("1 orbit skip-pair row: excess vs slack (clearance ~1.87)", ok1,
           f"E_right = {E_right:.6f} (target -0.036274), exc = {exc:.6f} "
           f"(target 0.041486)")

    # 2 radial refutation witness (eps = 1e-2)
    b1w = 0.35882554847972720 + 0.25257115012213690j
    b2w = -0.95331382807191360 + 0.30198136566164796j
    cw = trace_max_hub(b1w, b2w)
    Er = pair_excess(b1w, b2w, cw, "radial")
    Eg = pair_excess(b1w, b2w, cw, "right")
    ok2 = abs(Er - 0.2276426) < 2e-3 and abs(Eg - (-0.0376871)) < 2e-3
    report("2 radial witness: E_radial = +0.2276, E_rightward = -0.0377", ok2,
           f"E_radial = {Er:.6f}, E_rightward = {Eg:.6f}")

    # 3 one-face constancy (b2 = 0, m = 1 face): radial excess constant -0.8796
    ok3 = True
    vals3 = []
    for phase in (0.3, 1.1, 2.4):
        b1f = np.exp(1j * phase)
        cf = trace_max_hub(b1f, 0j)
        Ef = pair_excess(b1f, 0j, cf, "radial")
        vals3.append(Ef)
        if abs(Ef - (-0.8795989)) > 1.5e-3:
            ok3 = False
    report("3 one-face radial constancy = -0.8796 (three phases)", ok3,
           f"values {[f'{v:.5f}' for v in vals3]}")

    # 4 blocked ray at the orbit
    vals = H_of(crits(b1o, b2o), b1o, b2o)
    order = np.argsort(np.abs(vals))
    vh = vals[order[0]]  # small hub value
    others = vals[order[1:]]
    # locate the (double) equal pair among the other three values
    pairs = [(i, j) for i in range(3) for j in range(i + 1, 3)]
    i, j = min(pairs, key=lambda p: abs(others[p[0]] - others[p[1]]))
    ratio = others[i] / vh
    ok4 = (abs(others[i] - others[j]) < 1e-8 and abs(ratio.imag) < 1e-6
           and ratio.real > 1 and abs(ratio - 6.4641016) < 1e-4)
    report("4 blocked ray: double foreign value at 6.4641 x hub value", ok4,
           f"double-pair ratio {ratio:.7f}")

    # 5 rightward global spot battery
    worst = -10.0
    bad = 0
    for _ in range(400):
        if rng.uniform() < 0.5:
            b1 = np.exp(2j * np.pi * rng.uniform())
            b2 = np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
        else:
            b2 = np.exp(2j * np.pi * rng.uniform())
            b1 = np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
        c = trace_max_hub(b1, b2)
        if abs(H_of(c, b1, b2)) < 1e-6:
            continue
        E = pair_excess(b1, b2, c, "right", smax=2.0e6, nstep=1400)
        worst = max(worst, E)
        if E >= 0:
            bad += 1
    report("5 rightward spot battery: all E < 0", bad == 0,
           f"max E over battery = {worst:.5f}")

    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
