#!/usr/bin/env python3
"""Erdos 257 truncation-rung ladder: witness scan + exact greedy certificates.

Rung J weights: w_n = sum_{q=1..J} 2^{-qn}, target 1/2, support in {2,3,...}.

Superincreasing (q=1 tail term equals the q=1 weight term, q>=2 strictly
smaller), so greedy is forced: HalfRung(J) <=> greedy never hits the fatal
interval (T_{n+1}, w_n).

WITNESS EXCLUSION THEOREM (this session; J>=3, n>=4):
  if some M in [n, 2n-2] has
      mu_J(M) := sum_{q=2..J} 2^(M mod q) / (2^q - 1)  <=  11/15,
  then NO Boolean prefix D subset {2..n-1} is fatal at rank n.
Proof: scale by 2^E, E=J(n-1); h=E-M>=n-1; 2^h | (Y+S) where Y is the fatal
displacement past the q=1 term and S restores crossing terms q*d>M; then
S/2^h <= mu_J(M) and Y/2^h < (1/4)/(1-2^-n) <= 4/15, so 0 < Y+S < 2^h,
contradiction.
Corollary (half-LCM horizon): M = L_J = lcm(2..J) gives mu = sum 1/(2^q-1)
< 0.607, so every n >= L_J/2 + 1 is witness-covered.

So HalfRung(J) <=> greedy survives ranks 2..B(J), where B(J) = max bad rank,
bad = n in [4, L_J/2] with no witness (ranks 2,3 are forced takes).

MOD-12 FILTER (J>=7): mu_J(M) <= 11/15 forces 12 | M.
  M odd: mu >= 2/3 + 1/7 > 11/15.
  M = 2 mod 4: mu >= 1/3 + 1/7 + 4/15 = 78/105 > 11/15.
  M = 0 mod 4, M != 0 mod 3: mu >= 1/3 + 2/7 + 1/15 + (1/31+1/63+1/127) > 11/15.
"""
problem_id = "erdos_257"

import sys, json, time, bisect
from math import gcd

def lcm2(a, b): return a // gcd(a, b) * b

def channel_lcm(J):
    L = 1
    for q in range(2, J + 1): L = lcm2(L, q)
    return L

def good_set(J):
    """Exact set of good M in [4, L]: 15 * mu_scaled <= 11 * Dt."""
    L = channel_lcm(J)
    Dt = 1
    for q in range(2, J + 1): Dt = lcm2(Dt, (1 << q) - 1)
    qs = list(range(2, J + 1))
    tabs = {q: [(Dt // ((1 << q) - 1)) << s for s in range(q)] for q in qs}
    thr = 11 * Dt
    step, start = (12, 12) if J >= 7 else (1, 4)
    goods = []
    if L // step > 200000:
        import numpy as np
        Ms = np.arange(start, L + 1, step, dtype=np.int64)
        mu = np.zeros(len(Ms))
        for q in qs:
            mu += (2.0 ** (Ms % q)) / float((1 << q) - 1)
        cand = Ms[mu <= 11.0 / 15.0 + 1e-9]
        for M in cand.tolist():
            s = 0
            for q in qs: s += tabs[q][M % q]
            if 15 * s <= thr: goods.append(M)
    else:
        M = start
        while M <= L:
            s = 0
            for q in qs: s += tabs[q][M % q]
            if 15 * s <= thr: goods.append(M)
            M += step
    return L, goods

def bad_ranks(J):
    L, goods = good_set(J)
    bad = []
    i = 0
    half = L // 2
    if half > 2_000_000:
        import numpy as np
        g = np.array(goods, dtype=np.int64)
        for lo in range(4, half + 1, 5_000_000):
            hi = min(half, lo + 5_000_000 - 1)
            ns = np.arange(lo, hi + 1, dtype=np.int64)
            idx = np.searchsorted(g, ns)
            nx = np.where(idx < len(g), g[np.minimum(idx, len(g) - 1)], 1 << 62)
            mask = nx > 2 * ns - 2
            bad.extend(ns[mask].tolist())
    else:
        for n in range(4, half + 1):
            while i < len(goods) and goods[i] < n: i += 1
            if i >= len(goods) or goods[i] > 2 * n - 2:
                bad.append(n)
    gaps = [b - a for a, b in zip(goods, goods[1:])] or [0]
    return {"L": L, "n_good": len(goods), "max_gap": max(gaps),
            "bad": bad}

def weight_int(J, n):
    """2^{Jn} * w_n as an integer, built via bytearray (J set bits)."""
    top = (J - 1) * n
    buf = bytearray(top // 8 + 2)
    for q in range(1, J + 1):
        k = (J - q) * n
        buf[k >> 3] |= 1 << (k & 7)
    return int.from_bytes(buf, 'little')

def run_cert(J, nmax, progress=0, record_takes_to=0):
    """Exact greedy for rung J through rank nmax. z = 2^{Jn} r_{n-1}."""
    D = 1
    for q in range(1, J + 1): D = lcm2(D, (1 << q) - 1)
    tail_coef = [0] * (J + 1)
    for q in range(1, J + 1): tail_coef[q] = D // ((1 << q) - 1)
    z = 1 << (J - 1)
    skips, hard, takes = [], [], []
    t0 = time.time()
    for n in range(2, nmax + 1):
        z <<= J
        W = weight_int(J, n)
        if W <= z:
            z -= W
            if n <= record_takes_to: takes.append(n)
        else:
            if z > (1 << ((J - 1) * n)):
                T = 0
                for q in range(1, J + 1):
                    T += tail_coef[q] << ((J - q) * n)
                if D * z > T:
                    return {"J": J, "fatal_at": n,
                            "elapsed": round(time.time() - t0, 2)}
                hard.append(n)
            skips.append(n)
        if progress and n % progress == 0:
            print(f"  J={J} n={n}/{nmax} bits={z.bit_length()} "
                  f"skips={len(skips)} t={time.time()-t0:.1f}s", flush=True)
    return {"J": J, "checked_through": nmax, "fatal_at": None,
            "n_skips": len(skips), "n_hard_skips": len(hard),
            "hard_head": hard[:12], "skips_head": skips[:20],
            "takes": takes if record_takes_to else None,
            "elapsed": round(time.time() - t0, 2)}

def exhaustive(J, nmax):
    """All prefixes D subset {2..n-1}, all n<=nmax: count fatal prefixes."""
    Dq = 1
    for q in range(1, J + 1): Dq = lcm2(Dq, (1 << q) - 1)
    total, fatal = 0, []
    for n in range(2, nmax + 1):
        S = 1 << (J * n)
        def wint(d): return sum(1 << (J * n - q * d) for q in range(1, J + 1))
        w = [wint(d) for d in range(2, n)]
        wn = wint(n)
        tail = sum((Dq // ((1 << q) - 1)) << (J * n - q * n)
                   for q in range(1, J + 1))
        half = S >> 1
        m = n - 2
        vals = [0] * (1 << m)
        for mask in range(1, 1 << m):
            lb = mask & (-mask)
            vals[mask] = vals[mask ^ lb] + w[lb.bit_length() - 1]
        for mask in range(1 << m):
            r = half - vals[mask]
            if r <= 0: continue
            Dr = Dq * r
            if tail < Dr < Dq * wn:
                fatal.append((n, mask))
        total += 1 << m
    return {"J": J, "nmax": nmax, "prefixes": total,
            "n_fatal": len(fatal), "examples": fatal[:5]}

def automaton3(N):
    """Explicit J=3 collision-prepayment automaton; returns support head."""
    a = [0] * (N + 2)
    for n in range(2, N + 1):
        hn = (a[n // 2] if n % 2 == 0 else 0) + (a[n // 3] if n % 3 == 0 else 0)
        if hn == 2: a[n] = 1
        elif hn == 1: a[n] = 0
        else:
            m = n + 1
            hn1 = (a[m // 2] if m % 2 == 0 else 0) + (a[m // 3] if m % 3 == 0 else 0)
            a[n] = 0 if hn1 == 2 else 1
    return [n for n in range(2, N + 1) if a[n]]

if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "ladder":
        for J in [int(x) for x in sys.argv[2:]]:
            br = bad_ranks(J)
            B = max(br["bad"]) if br["bad"] else 3
            res = run_cert(J, max(B, 3),
                           progress=20000 if B > 40000 else 0)
            res.update(L=br["L"], B=B, n_bad=len(br["bad"]),
                       n_good=br["n_good"], max_good_gap=br["max_gap"],
                       bad_tail=br["bad"][-5:])
            print(json.dumps(res), flush=True)
    elif cmd == "fullwindow":
        for J in [int(x) for x in sys.argv[2:]]:
            L = channel_lcm(J)
            res = run_cert(J, L // 2, progress=20000 if L // 2 > 40000 else 0)
            res.update(L=L, window=L // 2)
            print(json.dumps(res), flush=True)
    elif cmd == "exhaustive":
        for J in [int(x) for x in sys.argv[2:]]:
            print(json.dumps(exhaustive(J, 18)), flush=True)
    elif cmd == "xcheck3":
        N = int(sys.argv[2])
        aut = automaton3(N)
        greedy = run_cert(3, N, record_takes_to=N)["takes"]
        print(json.dumps({"N": N, "automaton_head": aut[:25],
                          "greedy_head": greedy[:25],
                          "sets_equal": aut == greedy}))
