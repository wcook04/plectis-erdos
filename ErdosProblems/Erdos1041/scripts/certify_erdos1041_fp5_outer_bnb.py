"""Rigorous vectorised branch-and-bound v4 for the modulus-space obligation

    (MOD)  for every rho in [0,1]^5 :   Lbar(rho) >= LAM   ==>   OUT(rho) <= 5 - margin,

where OUT(rho) = sum_j T_j - (1-e^{-D(rho)/2})(T_(1)+T_(2)) and D is the
modulus-only deficit lower bound (eigenvalue form).

Box upper bound (all steps one-sided and elementary):
  * T_j <= max over rho_j in [a_j,b_j] of [(1-x^2) prod_{k!=j}(1+x B_k)]^{1/5}
    -- exact, by strict concavity of the log (bisection on the decreasing
       derivative);
  * OUT = max_{a<b} [ sum_{j!=a,b} T_j + (1-kappa)(T_a+T_b) ]
        <= sum_j Tu_j - (1-e^{-Dlo/2}) (Tu_(1)+Tu_(2))      [ONLY upper bounds];
  * Dlo: f_jk = t/(1+t)^2 increasing in t, Weyl for lambda_min.
Exclusion: Lbar(B) < LAM  (Lbar increasing) => ROWCERT+ holds on the whole box.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from math import comb, log, exp

M = 5
NMAX = 12
Hsharp = log(3125.0 / 729.0) / 5.0
PhiHs = (exp(Hsharp) - 1.0 - Hsharp) / Hsharp ** 2
LAM = 1.0 / PhiHs
BIN = np.array([comb(2 * n, n) for n in range(1, NMAX + 1)], float)
FOU = np.array([4.0 ** n for n in range(1, NMAX + 1)], float)
CLIP = 1.0 - 1e-13
BIS = 55
EYE = np.eye(M, dtype=bool)


def tighten(A, B):
    A = A.copy(); B = B.copy()
    for j in range(1, M):
        B[:, j] = np.minimum(B[:, j], B[:, j - 1])
    for j in range(M - 2, -1, -1):
        A[:, j] = np.maximum(A[:, j], A[:, j + 1])
    return A, B


def _logf(x, oth):
    x = np.minimum(x, CLIP)
    return np.log1p(-x * x) + np.log1p(x[:, None] * oth).sum(axis=1)


def _dlogf(x, oth):
    x = np.minimum(x, CLIP)
    return -2.0 * x / (1.0 - x * x) + (oth / (1.0 + x[:, None] * oth)).sum(axis=1)


def Tupper(A, B):
    n = len(A)
    Tu = np.empty((n, M))
    idx = np.arange(M)
    for j in range(M):
        oth = idx != j
        Bo = B[:, oth]
        a = np.minimum(A[:, j], CLIP); b = np.minimum(B[:, j], CLIP)
        ga = _dlogf(a, Bo); gb = _dlogf(b, Bo)
        lo = a.copy(); hi = b.copy()
        for _ in range(BIS):
            mid = 0.5 * (lo + hi)
            pos = _dlogf(mid, Bo) > 0
            lo = np.where(pos, mid, lo); hi = np.where(pos, hi, mid)
        xr = 0.5 * (lo + hi)
        x = np.where(ga <= 0.0, a, np.where(gb >= 0.0, b, xr))
        # concavity tangent at x absorbs the residual bracket [lo,hi]:
        #   log f(x*) <= log f(x) + |f'(x)/f(x)| * (hi-lo)
        slack = np.where((ga > 0.0) & (gb < 0.0), np.abs(_dlogf(x, Bo)) * (hi - lo), 0.0)
        Tu[:, j] = np.exp((_logf(x, Bo) + slack + 1e-12) / M)
    return Tu


def Dlower(A, B):
    tA = A[:, :, None] * A[:, None, :]
    tB = B[:, :, None] * B[:, None, :]
    fA = tA / (1.0 + tA) ** 2
    fB = tB / (1.0 + tB) ** 2
    nB = len(A)
    tot = np.zeros(nB); best = np.zeros(nB)
    PA = np.ones_like(fA); PB = np.ones_like(fB)
    for i, n in enumerate(range(1, NMAX + 1)):
        PA = PA * fA; PB = PB * fB
        WA = PA.copy(); WA[:, EYE] = 0.0
        WB = PB.copy(); WB[:, EYE] = 0.0
        Sig = WA.sum(axis=(1, 2))
        lminA = np.linalg.eigvalsh(WA)[:, 0]
        pert = np.sqrt(((WB - WA) ** 2).sum(axis=(1, 2)))     # Frobenius >= spectral
        lmin = lminA - pert
        tot = tot + (BIN[i] * Sig + (FOU[i] - BIN[i]) * M * lmin) / n
        best = np.maximum(best, tot / (2.0 * M))
    return best


def box_ub(A, B):
    Tu = Tupper(A, B)
    D = Dlower(A, B)
    Ts = np.sort(Tu, axis=1)
    ub = Tu.sum(axis=1) - (1.0 - np.exp(-0.5 * D)) * (Ts[:, 0] + Ts[:, 1])
    with np.errstate(divide='ignore'):
        Lu = (-np.log1p(-np.minimum(B, CLIP) ** 2)).sum(axis=1) / M
    Lu = np.where(B.max(axis=1) >= 1.0, np.inf, Lu)
    return ub, Lu


def run(margin, maxround=250, cap=2_500_000):
    A = np.zeros((1, M)); B = np.ones((1, M))
    exc = ver = 0
    for rnd in range(maxround):
        A, B = tighten(A, B)
        ok = np.all(A <= B + 1e-15, axis=1)
        A, B = A[ok], B[ok]
        if len(A) == 0:
            return dict(status='OK', rounds=rnd, excluded=exc, verified=ver)
        ub, Lu = box_ub(A, B)
        out = Lu < LAM
        good = ub <= 5.0 - margin
        keep = ~(out | good)
        exc += int(out.sum()); ver += int((good & ~out).sum())
        A, B = A[keep], B[keep]
        if len(A) == 0:
            return dict(status='OK', rounds=rnd, excluded=exc, verified=ver)
        w = B - A
        print(f"  r{rnd:3d}: live={len(A):8d} maxUB={ub[keep].max():.6f} maxw={w.max():.2e}", flush=True)
        if len(A) > cap:
            return dict(status='CAP', live=len(A), round=rnd, maxUB=float(ub[keep].max()))
        if w.max() < 1e-8:
            return dict(status='FAIL', A=A[0].tolist(), B=B[0].tolist())
        jj = np.argmax(w, axis=1); r = np.arange(len(A))
        mid = 0.5 * (A[r, jj] + B[r, jj])
        A2, B2 = A.copy(), B.copy(); B2[r, jj] = mid
        A3, B3 = A.copy(), B.copy(); A3[r, jj] = mid
        A = np.concatenate([A2, A3]); B = np.concatenate([B2, B3])
    return dict(status='MAXROUND', live=len(A))


if __name__ == '__main__':
    margin = float(sys.argv[1]) if len(sys.argv) > 1 else 0.05
    print(f"LAM={LAM:.12f} margin={margin} NMAX={NMAX}")
    print(run(margin))
