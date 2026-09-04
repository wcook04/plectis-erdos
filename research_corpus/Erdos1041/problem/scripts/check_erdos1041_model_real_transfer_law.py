"""Checker for QuinticModelRealTransferLaw.md (Erdos 1041).

Verifies (self-contained; no dependence on the wave-1 agent's scratch):
  V1  specimen-1 reconstruction: the printed 12-digit roots are unimodular,
      eta = 1 - |disc f|/5^5 = 9.9727654e-3 (2e-7), and the trace identity
      sum_j -log|f(c_j)| = -log(1-eta) holds to 1e-9;
  V2  real-hub coercivity at specimen 1: at the REAL trace-max hub
      (argmin |f(c)|, equivalently max Re of -log f), the Newton-flow
      two-arm excess E_real = L - (rho_i + rho_j) is in (-0.55, -0.35)
      (agent-reported -0.459);
  V3  model-hub sign anomaly at specimen 1: the sigma-blow-up model
      H(v) = v^5 + b_2 v^2 + b_1 v (p_m = sum a_k^{-m},
      sigma = (p_5/5)^{-1/5} best matching branch, b_r = (p_r/r) sigma^r)
      has trace-max hub with mu = b_2/v_c^3 within 0.5 of 50+30sqrt3,
      and the nearest REAL critical point to sigma*v_c carries
      E_real in (+0.0015, +0.0035) (agent-reported +0.0024872815):
      obligation (b) fails at the model-selected hub while the real
      trace-max hub is deeply safe (V2);
  V4  degree-4 scoping guard (MinimalHubArmBudgetRefutation.md Result A
      witness, exact hex betas): the MEC-normalized near-square quartic has
      eta in (0.008, 0.014) — inside the near-gon band — and its argmin-hub
      Newton-flow excess E_real = (L_chart - |z_3 - m| - |z_4 - m|)/R_MEC
      is > +0.002 (note's arithmetic gives ~ +0.004): the "real trace-max
      hub is safe" law is a MEASURED quintic near-gon regularity, provably
      NOT a universal all-degree law even at small eta;
  V5  stability spot: specimen-1's root-to-rotated-pentagon matching
      distance d_max satisfies 0.05 sqrt(eta) <= d_max <= 0.72 sqrt(eta)
      (the measured sharp constant is ~0.45 sup / 0.26 median, versus the
      landed Theorem 2 constant 7).

Exit 0 iff all pass.
"""
import sys

import numpy as np
from scipy.integrate import solve_ivp

FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


SPEC1_ROOTS = np.array([
    +0.999741221817 + 0.022748393333j,
    +0.343108181546 + 0.939295893612j,
    -0.829581249913 + 0.558386022205j,
    -0.813268406148 - 0.581888734692j,
    +0.294434207833 - 0.955671751836j,
])

# MinimalHubArmBudgetRefutation.md Result A witness (chart betas, exact hex)
BETA2_4 = float.fromhex("0x1.8c5640e53fa34p-9") + 1j * float.fromhex("0x1.69a016b3f0c4ap-9")
BETA3_4 = -float.fromhex("0x1.6fa15252d066ep-5") - 1j * float.fromhex("0x1.3895293ffc3ebp-6")


def poly_from_roots(roots):
    c = np.array([1.0 + 0j])
    for a in roots:
        c = np.convolve(c, [1.0, -a])
    return c


def newton_arm(coeffs, dcoeffs, ddcoeffs, c, sign, T=40.0):
    """Descend f(z(t)) = f(c) e^{-t} from hub c; return (length, endpoint)."""
    fc = np.polyval(coeffs, c)
    fpp = np.polyval(ddcoeffs, c)
    t0 = 1e-10
    u = sign * np.sqrt(-2.0 * fc * t0 / fpp)
    z = c + u
    for _ in range(3):
        fz = np.polyval(coeffs, z)
        z = z - (fz - fc * np.exp(-t0)) / np.polyval(dcoeffs, z)

    def rhs(t, y):
        zz = y[0] + 1j * y[1]
        d = -np.polyval(coeffs, zz) / np.polyval(dcoeffs, zz)
        return [d.real, d.imag, abs(d)]

    sol = solve_ivp(rhs, [t0, T], [z.real, z.imag, 0.0], method="DOP853",
                    rtol=1e-12, atol=1e-14)
    z_end = sol.y[0, -1] + 1j * sol.y[1, -1]
    for _ in range(4):  # Newton to the exact root
        z_end = z_end - np.polyval(coeffs, z_end) / np.polyval(dcoeffs, z_end)
    tail = abs(np.polyval(coeffs, sol.y[0, -1] + 1j * sol.y[1, -1])) / max(
        1e-30, abs(np.polyval(dcoeffs, z_end)))
    return sol.y[2, -1] + tail, z_end


def two_arm_excess(coeffs, hub):
    dcoeffs = np.polyder(coeffs)
    ddcoeffs = np.polyder(dcoeffs)
    tot, ends = 0.0, []
    for sign in (+1, -1):
        L, z_end = newton_arm(coeffs, dcoeffs, ddcoeffs, hub, sign)
        tot += L - abs(z_end)
        ends.append(z_end)
    return tot, ends


def main():
    # ---------- V1 ----------
    roots = SPEC1_ROOTS
    unimod = float(np.max(np.abs(np.abs(roots) - 1.0)))
    coeffs = poly_from_roots(roots)
    dcoeffs = np.polyder(coeffs)
    crits = np.roots(dcoeffs)
    disc = np.prod([(roots[i] - roots[j]) ** 2
                    for i in range(5) for j in range(i + 1, 5)])
    eta = 1.0 - abs(disc) / 5**5
    trace_lhs = -np.sum(np.log(np.abs(np.polyval(coeffs, crits))))
    trace_rhs = -np.log(1.0 - eta)
    ok1 = unimod < 5e-11 and abs(eta - 9.9727654e-3) < 2e-7 \
        and abs(trace_lhs - trace_rhs) < 1e-9
    report("V1 specimen-1 reconstruction (unimodular, eta, trace id)", ok1,
           f"unimod {unimod:.1e} eta {eta:.9e} trace-dev {abs(trace_lhs-trace_rhs):.1e}")

    # ---------- V2 ----------
    cv = np.abs(np.polyval(coeffs, crits))
    hub_real = crits[int(np.argmin(cv))]
    E_real_hub, ends = two_arm_excess(coeffs, hub_real)
    ok2 = -0.55 < E_real_hub < -0.35 and len(ends) == 2
    report("V2 real trace-max hub coercive at specimen 1", ok2,
           f"E_real {E_real_hub:+.6f}")

    # ---------- V3 ----------
    p = {m: np.sum(roots ** (-float(m))) for m in (1, 2, 5)}
    best = None
    for br in range(5):
        sigma = (p[5] / 5.0) ** (-0.2) * np.exp(2j * np.pi * br / 5)
        b1 = p[1] * sigma
        b2 = (p[2] / 2.0) * sigma**2
        Hc = np.array([1.0, 0, 0, b2, b1, 0.0], dtype=complex)
        vc = np.roots(np.polyder(Hc))
        vc = vc[np.abs(vc) > 1e-8]
        cost = sum(min(abs(sigma * v - c) for c in crits) for v in vc)
        if best is None or cost < best[0]:
            best = (cost, sigma, b1, b2, vc)
    cost, sigma, b1, b2, vc = best
    Hc = np.array([1.0, 0, 0, b2, b1, 0.0], dtype=complex)
    Hvals = np.polyval(Hc, vc)
    # At the tangent orbit ALL FOUR model hubs tie at Re H = 0 (argmax is
    # noise; A4's finding) -- assert the tie, then select by mu-matching.
    tie = float(np.max(np.abs(Hvals.real))) / max(1.0, float(np.max(np.abs(Hvals))))
    mu_t = 50 + 30 * np.sqrt(3)
    mus = b2 / vc**3
    k_sel = int(np.argmin(np.abs(mus - mu_t)))
    v_model = vc[k_sel]
    mu_model = mus[k_sel]
    z_star = sigma * v_model
    hub_model = crits[int(np.argmin(np.abs(crits - z_star)))]
    E_real_model_hub, _ = two_arm_excess(coeffs, hub_model)
    ok3 = tie < 0.05 and abs(mu_model - mu_t) < 0.5 \
        and 0.0015 < E_real_model_hub < 0.0035 \
        and abs(hub_model - hub_real) > 1e-3
    report("V3 model-hub anomaly at specimen 1", ok3,
           f"4-fold ReH tie {tie:.2e}; mu_model {mu_model:.4f} "
           f"(target {mu_t:.4f}) E_real@model-hub {E_real_model_hub:+.7f} "
           f"match-cost {cost:.2e}")

    # ---------- V4 ----------
    ch4 = np.array([1.0, -BETA3_4, -BETA2_4, 0.0, -1.0], dtype=complex)
    r4 = np.roots(ch4)
    d4 = np.polyder(ch4)
    c4 = np.roots(d4)
    cv4 = np.abs(np.polyval(ch4, c4))
    hub4 = c4[int(np.argmin(cv4))]
    ok_hub0 = abs(hub4) < 1e-12  # chart hub is exactly 0
    # MEC by diameter pair
    pairs = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    i, j = max(pairs, key=lambda ij: abs(r4[ij[0]] - r4[ij[1]]))
    m4 = (r4[i] + r4[j]) / 2.0
    R4 = abs(r4[i] - r4[j]) / 2.0
    covered = float(np.max(np.abs(r4 - m4))) <= R4 * (1 + 1e-9)
    L4, ends4 = two_arm_excess(ch4, hub4)
    # two_arm_excess returns L - |z_end| sums against the ORIGIN; V4 needs
    # the MEC-centred budget, so recompute from raw arms:
    dch4 = np.polyder(ch4)
    ddch4 = np.polyder(dch4)
    Lsum, mod_sum = 0.0, 0.0
    for sign in (+1, -1):
        L, z_end = newton_arm(ch4, dch4, ddch4, hub4, sign)
        Lsum += L
        mod_sum += abs(z_end - m4)
    E4 = (Lsum - mod_sum) / R4
    disc4 = np.prod([(a - b) ** 2 for k, a in enumerate(r4)
                     for b in r4[k + 1:]])
    eta4 = 1.0 - abs(disc4) / (R4 ** 12) / 4**4
    ok4 = ok_hub0 and covered and E4 > 0.002 and 0.008 < eta4 < 0.014 \
        and 2.0018 < Lsum < 2.0025 and abs(R4 - 1.00091105) < 1e-5
    report("V4 deg-4 refutation witness: argmin-hub law fails at eta~0.011",
           ok4, f"E4 {E4:+.6f} eta4 {eta4:.5f} L {Lsum:.7f} R_MEC {R4:.8f}")

    # ---------- V5 ----------
    from itertools import permutations
    gon = np.exp(2j * np.pi * np.arange(5) / 5)
    best_d = np.inf
    for th in np.linspace(0, 2 * np.pi / 5, 720, endpoint=False):
        g = gon * np.exp(1j * th)
        for perm in permutations(range(5)):
            d = max(abs(roots[k] - g[perm[k]]) for k in range(5))
            if d < best_d:
                best_d = d
    s = np.sqrt(eta)
    ok5 = 0.05 * s <= best_d <= 0.72 * s
    report("V5 stability spot d_max vs sqrt(eta)", ok5,
           f"d_max {best_d:.5f} = {best_d/s:.3f} sqrt(eta)")

    if FAILURES:
        print("FAILURES:", FAILURES)
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
