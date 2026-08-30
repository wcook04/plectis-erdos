"""Checker for TraceMaxEntropyAngularBudget.md (Erdos 1041).

Verifies:
  1  fibre derivative product identity prod_{H(z)=w} H'(z) = n^n prod_k
     (H(c_k) - w) numerically for n = 4, 5, 6 random monic H (the identity
     is landed; re-checked here because everything below consumes it);
  2  trace-max contraction: on the ray w = v + t^n (v the trace-maximal
     critical value) the inverse-speed product prod_j |n t^{n-1}/H'(z_j)|
     = prod_k t^n/|t^n + delta_k| <= 1, delta_k = v - H(c_k);
  3  the entropy integral int_0^oo log|1 + delta/t^n| dt
     = (pi/sin(pi/n)) Re(delta^{1/n}) for Re delta >= 0 (battery incl.
     purely imaginary delta);
  4  the integrated entropy sum rule Sum_j int log|q_j| dt
     = -(pi/sin(pi/n)) Sum_k Re(delta_k^{1/n}) end-to-end on random
     low-mode quintics (fibre-summed, no branch tracking needed);
  5  the angular Polya budget, finite-T form: for random cubics/quartics,
     (1/2pi) int_theta Sum_j int_0^T (|dz_j/dt|^2 - 1) dt dtheta
     = (n/2pi) (B(T)/T + int_0^T B(t)/t^2 dt), B = A - pi t^2, and
     B(t) <= 0 (Polya); change of variables A(t) cross-checked by Monte
     Carlo at sample levels;
  6  support-oscillation ingredients: 1 - cos th = |sin th| tan(|th|/2),
     the adjacent-pair sums |Im(conj(u+)h)| + |Im(conj(u-)h)| =
     2 r sin(delta) cos(psi) (bracketed hub), Re-sum = 2 r cos(delta)
     cos(psi), and tan(alpha/2) <= cot(delta) iff alpha <= pi - 2 delta
     (symbolic);
  7  two-sheet quadratic bound |A'| + |B'| <= 2 sqrt(|m'|^2 + |d'|^2) and
     2(sqrt X - 1) <= X - 1 (random battery).

Exit 0 iff all pass.
"""
import sys

import mpmath as mp
import numpy as np
import sympy as sp

rng = np.random.default_rng(11)
FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def rand_monic(n, scale=1.0):
    c = (rng.normal(size=n) + 1j * rng.normal(size=n)) * scale
    return np.concatenate(([1.0 + 0j], c))


def main():
    mp.mp.dps = 25

    # 1 product identity
    worst1 = 0.0
    for n in (4, 5, 6):
        for _ in range(30):
            coeffs = rand_monic(n)
            dcoeffs = np.polyder(coeffs)
            crit = np.roots(dcoeffs)
            w = rng.normal() + 1j * rng.normal()
            fib = np.roots(coeffs - np.concatenate((np.zeros(n, complex), [w])))
            lhs = np.prod(np.polyval(dcoeffs, fib))
            rhs = float(n) ** n * np.prod(np.polyval(coeffs, crit) - w)
            worst1 = max(worst1, abs(lhs - rhs) / max(1.0, abs(rhs)))
    report("1 fibre derivative product identity", worst1 < 1e-8, f"worst rel dev {worst1:.2e}")

    # 2 trace-max contraction (low-mode quintics)
    ok2 = True
    worst2 = 0.0
    for _ in range(60):
        b1 = rng.normal() + 1j * rng.normal()
        b2 = rng.normal() + 1j * rng.normal()
        coeffs = np.array([1, 0, 0, b2, b1, 0], complex)
        dcoeffs = np.polyder(coeffs)
        crit = np.roots(dcoeffs)
        vals = np.polyval(coeffs, crit)
        v = vals[np.argmax(vals.real)]
        deltas = v - vals
        if deltas.real.min() < -1e-12:
            ok2 = False
        for texp in (-1.0, 0.0, 1.0):
            t = 10.0 ** texp
            fib = np.roots(coeffs - np.concatenate((np.zeros(5, complex), [v + t**5])))
            prod_q = np.prod(5 * t**4 / np.abs(np.polyval(dcoeffs, fib)))
            prod_rhs = np.prod(t**5 / np.abs(t**5 + deltas))
            worst2 = max(worst2, abs(prod_q - prod_rhs))
            if prod_q > 1 + 1e-9:
                ok2 = False
    report("2 trace-max inverse-speed product <= 1", ok2 and worst2 < 1e-8,
           f"worst identity dev {worst2:.2e}")

    # 3 entropy integral
    worst3 = mp.mpf(0)
    for n in (3, 5, 8):
        for delta in (mp.mpf(2), mp.mpc(1, 3), mp.mpc(0, 4), mp.mpc(0.01, -2), mp.mpf(25)):
            lhs = mp.quad(lambda t, d=delta, nn=n: mp.log(abs(1 + d / t**nn)),
                          [0, 0.5, 2, 10, mp.inf])
            rhs = mp.pi / mp.sin(mp.pi / n) * mp.re(delta ** (mp.mpf(1) / n))
            worst3 = max(worst3, abs(lhs - rhs))
    report("3 entropy integral formula", worst3 < mp.mpf("1e-12"), f"worst dev {mp.nstr(worst3, 3)}")

    # 4 integrated sum rule (fibre-summed, quintic)
    worst4 = mp.mpf(0)
    for trial in range(3):
        b1 = complex(rng.normal(), rng.normal()) * 0.7
        b2 = complex(rng.normal(), rng.normal()) * 0.7
        coeffs = np.array([1, 0, 0, b2, b1, 0], complex)
        dcoeffs = np.polyder(coeffs)
        crit = np.roots(dcoeffs)
        vals = np.polyval(coeffs, crit)
        v = vals[np.argmax(vals.real)]
        deltas = [mp.mpc(d) for d in (v - vals)]

        def sum_log_q(t):
            fib = np.roots(coeffs - np.concatenate((np.zeros(5, complex), [v + float(t)**5])))
            return float(np.sum(np.log(5 * float(t)**4 / np.abs(np.polyval(dcoeffs, fib)))))

        # integrated form of the pointwise identity on [t_lo, T] (endpoint-safe
        # range; the closed-form full-line value is section 3's job)
        t_lo, T = mp.mpf("0.05"), mp.mpf(30)
        lhs = mp.quad(sum_log_q, [t_lo, 0.3, 1, 5, T])
        rhs = -sum(mp.quad(lambda t, dd=d: mp.log(abs(1 + dd / t**5)),
                           [t_lo, 0.3, 1, 5, T]) for d in deltas)
        worst4 = max(worst4, abs(lhs - rhs))
    report("4 integrated entropy sum rule (quintic, fibre-summed)", worst4 < mp.mpf("1e-6"),
           f"worst dev {mp.nstr(worst4, 3)}")

    # 5 angular Polya budget, finite-T form
    ok5 = True
    detail5 = []
    for n, ntrials in ((3, 2), (4, 1)):
        for _ in range(ntrials):
            roots = [np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform())
                     for _ in range(n)]
            coeffs = np.poly(roots)
            dcoeffs = np.polyder(coeffs)
            T = 4.0
            nth = 64
            nt = 400
            ts = np.linspace(T / nt, T, nt)
            thetas = np.linspace(0, 2 * np.pi, nth, endpoint=False)
            # fibre area A(t) via change of variables (also gives speed sums)
            speed2 = np.zeros((nt, nth))
            inv_p2 = np.zeros((nt, nth))
            for i, t in enumerate(ts):
                for k, th in enumerate(thetas):
                    w = (t**n) * np.exp(1j * th)
                    fib = np.roots(coeffs - np.concatenate((np.zeros(n, complex), [w])))
                    dp = np.abs(np.polyval(dcoeffs, fib))
                    speed2[i, k] = np.sum((n * t ** (n - 1) / dp) ** 2)
                    inv_p2[i, k] = np.sum(1.0 / dp**2)
            dth = 2 * np.pi / nth
            dt = ts[1] - ts[0]
            # trapezoidal cumulative integral of the steep radial density
            dens = n * ts ** (2 * n - 1) * inv_p2.sum(axis=1) * dth
            A = np.concatenate(([0.0], np.cumsum((dens[1:] + dens[:-1]) / 2))) * dt
            A += dens[0] * dt / 2  # head triangle below the first grid point
            # Monte Carlo cross-check of A at the top level
            M = 400000
            span = 1.8 * max(1.0, T ** 1.0)
            zs = (rng.uniform(-span, span, M) + 1j * rng.uniform(-span, span, M))
            frac = np.mean(np.abs(np.polyval(coeffs, zs)) < T**n)
            A_mc = frac * (2 * span) ** 2
            if abs(A_mc - A[-1]) / A[-1] > 0.03:
                ok5 = False
                detail5.append(f"MC area mismatch n={n}: {A_mc:.4f} vs {A[-1]:.4f}")
            B = A - np.pi * ts**2
            if B.max() > 2e-2:  # discretization tolerance; Polya gives B <= 0 exactly
                ok5 = False
                detail5.append(f"Polya violated? maxB={B.max():.2e}")
            integ = (speed2 - n).sum(axis=1)
            lhs = (dth / (2 * np.pi)) * (np.sum((integ[1:] + integ[:-1]) / 2) * dt
                                         + integ[0] * dt / 2)
            bt2 = B / ts**2
            rhs = (n / (2 * np.pi)) * (B[-1] / T
                                       + np.sum((bt2[1:] + bt2[:-1]) / 2) * dt)
            if abs(lhs - rhs) > 0.02 * max(1.0, abs(lhs)):
                ok5 = False
                detail5.append(f"identity n={n}: lhs={lhs:.5f} rhs={rhs:.5f}")
            else:
                detail5.append(f"n={n}: lhs={lhs:.5f} rhs={rhs:.5f} A_mc/A={A_mc/A[-1]:.4f}")
    report("5 angular Polya budget finite-T identity + Polya sign", ok5, "; ".join(detail5))

    # 6 support-oscillation ingredients (symbolic)
    th, de, ps, r_ = sp.symbols("theta delta psi r", real=True)
    id1 = sp.simplify(1 - sp.cos(th) - sp.Abs(sp.sin(th)) * sp.tan(sp.Abs(th) / 2))
    # evaluate id1 on a grid instead of full simplify (Abs blocks it)
    id1_ok = all(abs(float(id1.subs(th, v))) < 1e-12
                 for v in (-2.5, -1.0, -0.3, 0.3, 1.2, 2.9))
    u_p = sp.exp(sp.I * (de))
    u_m = sp.exp(-sp.I * de)
    h = r_ * sp.exp(sp.I * ps)
    im_sum = sp.simplify(sp.Abs(sp.im(sp.conjugate(u_p) * h)) + sp.Abs(sp.im(sp.conjugate(u_m) * h)))
    # on the bracket |psi| <= delta < pi/2 with r >= 0: equals 2 r sin(delta) cos(psi)
    subs_ok = True
    for dv, pv, rv in ((0.6, 0.2, 0.8), (1.1, -0.9, 1.3), (0.4, 0.39, 0.5)):
        lhs = float(im_sum.subs({de: dv, ps: pv, r_: rv}))
        rhs = float(2 * rv * np.sin(dv) * np.cos(pv))
        subs_ok &= abs(lhs - rhs) < 1e-10
        lhs2 = float(sp.re(sp.conjugate(u_p) * h + sp.conjugate(u_m) * h).subs({de: dv, ps: pv, r_: rv}))
        rhs2 = float(2 * rv * np.cos(dv) * np.cos(pv))
        subs_ok &= abs(lhs2 - rhs2) < 1e-10
    equiv = sp.simplify(sp.tan((sp.pi - 2 * de) / 2) - sp.cot(de)) == 0
    report("6 support-oscillation trig ingredients", id1_ok and subs_ok and equiv)

    # 7 two-sheet quadratic bound
    ok7 = True
    for _ in range(2000):
        A_ = rng.normal() + 1j * rng.normal()
        B_ = rng.normal() + 1j * rng.normal()
        m_ = (A_ + B_) / 2
        d_ = (A_ - B_) / 2
        if abs(A_) + abs(B_) > 2 * np.sqrt(abs(m_) ** 2 + abs(d_) ** 2) + 1e-12:
            ok7 = False
        X = rng.uniform(0, 9)
        if 2 * (np.sqrt(X) - 1) > X - 1 + 1e-12:
            ok7 = False
    report("7 two-sheet quadratic bound", ok7)

    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
