#!/usr/bin/env python3
"""
Erdos 257 -- the Mersenne Cantor staircase and the run-length reformulation.

Erdos 257:  for every infinite A subset N, sum_{k in A} 1/(2^k - 1) is irrational.
A counterexample is an infinite A whose subsum is rational.

Facts used (all elementary, re-derived in the accompanying note):

  w_k = 1/(2^k-1) is strictly superincreasing: w_n > Tail_n := sum_{k>n} w_k.
  Hence Phi(b) = sum b_k w_k is an order-preserving bijection {0,1}^N -> A-set,
  greedy is forced, and y is representable iff its greedy orbit never lands in
  the "Cantor gap" (Tail_n, w_n), of width G_n = w_n - Tail_n ~ (2/3) 4^-n.

NEW COORDINATE (this script).  Put

      mu_n := rho_n / Tail_n   in   [0, 1]        (alive iff mu_n <= 1)
      t_n  := Tail_n / Tail_{n-1}   -> 1/2 exponentially fast.

Then the greedy map is EXACTLY

      mu_n = mu_{n-1}/t_n            (skip)
      mu_n = mu_{n-1}/t_n - (1-t_n)/t_n   (take)

i.e. the doubling map x -> 2x mod 1 up to the correction t_n -> 1/2, and

      DEATH at rank n  <=>  mu_{n-1} within  ~ (1/6) 2^-n  of exactly 1/2.

Because mu_{n-1} has the support bits b_n b_{n+1} b_{n+2} ... as its binary
expansion, "within 2^-n of 1/2" means "b_n followed by a run of ~n copies of
1-b_n".  So, conjecturally-exactly:

      y is an infinite rational subsum
        <=>  its support word has NO run of length >= n + O(1) starting at n+1.

This script (a) builds a certified exact greedy engine, (b) tests that
run-length law quantitatively, (c) profiles the flagship candidate
counterexamples 1/2, 1/21, 4/9, 1/465 by run length, subword complexity and
normality, and (d) computes the gap census / Newhouse thickness of the
achievement set.
"""
from __future__ import annotations
import argparse, json, math, random, sys
from fractions import Fraction

# ---------------------------------------------------------------- fixed point

def w_scaled(n: int, M: int) -> int:
    """floor(2^M / (2^n - 1)) exactly.  = sum_{j>=1, jn<=M} 2^(M-jn)."""
    J = M // n
    if J == 0:
        return 0
    if J > 32:
        rep = ((1 << (J * n)) - 1) // ((1 << n) - 1)   # J ones spaced n apart
        return rep << (M - J * n)
    v = 0
    for j in range(1, J + 1):
        v |= 1 << (M - j * n)
    return v


class Engine:
    """Certified fixed-point greedy on weights w_k = 1/(2^k-1), k >= 1."""

    def __init__(self, depth: int, guard: int = 128):
        self.depth = depth
        self.M = 2 * depth + guard
        M = self.M
        self.W = [0] * (depth + 2)
        for n in range(1, depth + 2):
            self.W[n] = w_scaled(n, M)
        # Tail_0 * 2^M, truncated: sum_{k=1..M} floor(2^M w_k).
        acc = 0
        for k in range(1, M + 1):
            acc += w_scaled(k, M) if k > depth + 1 else self.W[k]
        self.T0 = acc
        self.tail_err = M + 2          # 0 <= 2^M Tail_n - That_n <= tail_err

    def run(self, p: int, q: int, depth: int | None = None):
        """Greedy on y = p/q.  Returns dict with word, status, margins."""
        D = depth or self.depth
        M, W = self.M, self.W
        rho = (p << M) // q              # 0 <= 2^M y - rho < 1
        rho_err = 1                      # 2^M y - rho  in [0, rho_err)
        That = self.T0
        word, logmarg = [], []
        status, death = "alive", None
        for n in range(1, D + 1):
            wn = W[n]
            That -= wn                   # That ~ 2^M Tail_n
            # decision: take iff 2^M rho_{n-1} >= 2^M w_n
            if rho >= wn + rho_err:
                take = True
            elif rho + rho_err <= wn:
                take = False
            else:
                status = "PRECISION"; death = n; break
            if take:
                margin = rho - wn
                rho -= wn
                rho_err += 1
                word.append(1)
            else:
                # alive iff 2^M rho_{n-1} <= 2^M Tail_n
                if rho + rho_err <= That:
                    margin = That - rho
                    word.append(0)
                elif rho > That + self.tail_err:
                    status = "dead"; death = n; break
                else:
                    status = "PRECISION"; death = n; break
            logmarg.append(margin.bit_length() - M)   # ~ log2(margin)
        return {"word": word, "status": status, "death": death,
                "logmargin": logmarg, "M": M}


# ------------------------------------------------------------- word analytics

def run_profile(word):
    """R[n] = length of maximal run of (1-b_n) starting at position n+1 (0-idx n)."""
    D = len(word)
    R = [0] * D
    # blk[i] = length of maximal constant block starting at i
    blk = [0] * D
    blk[D - 1] = 1
    for i in range(D - 2, -1, -1):
        blk[i] = blk[i + 1] + 1 if word[i] == word[i + 1] else 1
    for i in range(D - 1):
        R[i] = blk[i + 1] if word[i + 1] != word[i] else 0
    return R, blk


def max_run(word):
    best = cur = 1
    for i in range(1, len(word)):
        cur = cur + 1 if word[i] == word[i - 1] else 1
        if cur > best:
            best = cur
    return best


def subword_complexity(word, kmax):
    out = {}
    n = len(word)
    val = 0
    for k in range(1, kmax + 1):
        if k > n:
            break
        seen = set()
        mask = (1 << k) - 1
        v = 0
        for i in range(n):
            v = ((v << 1) | word[i]) & mask
            if i >= k - 1:
                seen.add(v)
        out[k] = len(seen)
    return out


def block_freqs(word, k):
    n = len(word); mask = (1 << k) - 1
    cnt = {}
    v = 0
    for i in range(n):
        v = ((v << 1) | word[i]) & mask
        if i >= k - 1:
            cnt[v] = cnt.get(v, 0) + 1
    tot = n - k + 1
    exp = tot / (1 << k)
    chi = sum((cnt.get(b, 0) - exp) ** 2 / exp for b in range(1 << k))
    return chi, (1 << k) - 1, tot


# ------------------------------------------------------------------- commands

FLAGSHIPS = [("1/2", 1, 2), ("1/21", 1, 21), ("4/9", 4, 9), ("1/465", 1, 465),
             ("1/5", 1, 5), ("2/21", 2, 21), ("4/21", 4, 21), ("1/3", 1, 3)]


def cmd_flagship(a):
    eng = Engine(a.depth)
    out = {}
    for name, p, q in FLAGSHIPS:
        r = eng.run(p, q)
        w = r["word"]
        if r["status"] != "alive":
            out[name] = {"status": r["status"], "death": r["death"]}
            print(f"{name:8s} {r['status']} at rank {r['death']}")
            continue
        R, blk = run_profile(w)
        # margin law:  log2(margin_n) + n   vs   R_n
        lm = r["logmargin"]
        pairs = [(R[i], lm[i] + (i + 1)) for i in range(min(len(R), len(lm)) - 1)]
        # threshold slack: n - R_n  (death predicted when R_n >~ n)
        slack = [(i + 1) - R[i] for i in range(len(R) - 1)]
        worst = min(range(len(slack)), key=lambda i: slack[i])
        out[name] = {
            "status": "alive", "depth": len(w),
            "density": sum(w) / len(w),
            "max_run": max_run(w),
            "argmax_run_pos": max(range(len(R) - 1), key=lambda i: R[i]) + 1,
            "min_slack": slack[worst], "min_slack_at": worst + 1,
            "R_at_min_slack": R[worst],
            "first20": "".join(map(str, w[:60])),
            "support_head": [i + 1 for i in range(60) if w[i]],
        }
        print(f"{name:8s} alive to {len(w):>6d}  density {sum(w)/len(w):.5f}  "
              f"max_run {max_run(w):>3d} at n={out[name]['argmax_run_pos']:<6d} "
              f"min(n - R_n) = {slack[worst]} at n={worst+1}")
    print(json.dumps(out, indent=1)[:0])
    with open(a.out, "w") as f:
        json.dump(out, f, indent=1)
    return out


def cmd_marginlaw(a):
    """Test: log2(margin_n) + n  ==  -R_n + c ?"""
    eng = Engine(a.depth)
    rows = []
    for name, p, q in FLAGSHIPS[:4]:
        r = eng.run(p, q)
        if r["status"] != "alive":
            continue
        R, _ = run_profile(r["word"])
        lm = r["logmargin"]
        for i in range(20, min(len(R), len(lm)) - 1):
            rows.append((R[i], lm[i] + (i + 1)))
    by = {}
    for Rv, y in rows:
        by.setdefault(Rv, []).append(y)
    print(f"{'R_n':>4} {'count':>7} {'mean(log2 margin + n)':>24} {'min':>6} {'max':>6}")
    for Rv in sorted(by):
        v = by[Rv]
        print(f"{Rv:>4} {len(v):>7} {sum(v)/len(v):>24.3f} {min(v):>6} {max(v):>6}")


def cmd_survey(a):
    """Random-rational survey: death rank distribution + run-length law."""
    rnd = random.Random(a.seed)
    eng = Engine(a.depth)
    deaths, alive = {}, 0
    maxruns = {}
    for _ in range(a.n):
        q = rnd.randrange(3, a.qmax) | 1
        p = rnd.randrange(1, q)
        r = eng.run(p, q)
        if r["status"] == "dead":
            deaths[r["death"]] = deaths.get(r["death"], 0) + 1
        elif r["status"] == "alive":
            alive += 1
            mr = max_run(r["word"])
            maxruns[mr] = maxruns.get(mr, 0) + 1
        else:
            print("PRECISION FAILURE", r["death"]); sys.exit(2)
    print(f"n={a.n} depth={a.depth} qmax={a.qmax}: alive {alive} ({alive/a.n:.4%})")
    print(f"{'rank':>5} {'deaths':>8} {'frac':>10} {'2^-(n+1)':>10}")
    for k in sorted(deaths)[:24]:
        print(f"{k:>5} {deaths[k]:>8} {deaths[k]/a.n:>10.5f} {2.0**-(k+1):>10.5f}")
    print("max-run histogram among survivors (depth %d):" % a.depth)
    for k in sorted(maxruns):
        print(f"  run {k:>3}: {maxruns[k]:>7}  ({maxruns[k]/max(alive,1):.4f})")


def cmd_gapcensus(a):
    """Exact gap census and Newhouse thickness of the achievement set."""
    N = a.levels
    W = [Fraction(0)] + [Fraction(1, (1 << k) - 1) for k in range(1, N + 60)]
    tail = [Fraction(0)] * (N + 2)
    t = sum(W[k] for k in range(N + 1, N + 60))
    for n in range(N, -1, -1):
        tail[n] = t
        if n >= 1:
            t = t + W[n]
    E = tail[0] + sum(W[k] for k in range(1, 1))  # tail[0] = sum_{k>=1} w_k
    tot = Fraction(0)
    print(f"E (Erdos-Borwein) ~ {float(tail[0]):.10f}")
    print(f"{'n':>3} {'G_n':>14} {'#gaps':>8} {'2^(n-1)G_n':>14} {'bridge/gap':>12}")
    for n in range(1, min(N, 14) + 1):
        G = W[n] - tail[n]
        tot += (1 << (n - 1)) * G
        thick = tail[n] / G
        print(f"{n:>3} {float(G):>14.3e} {1<<(n-1):>8} {float((1<<(n-1))*G):>14.6f} {float(thick):>12.4f}")
    for n in range(15, N + 1):
        tot += (1 << (n - 1)) * (W[n] - tail[n])
    meas = tail[0] - tot
    print(f"\ntotal gap measure (to level {N}) = {float(tot):.8f}")
    print(f"measure(achievement set)        = {float(meas):.8f}")
    print(f"fraction of [0,E]               = {float(meas/tail[0]):.6f}")
    thickmin = min((tail[n] / (W[n] - tail[n])) for n in range(1, N + 1))
    print(f"Newhouse thickness (min bridge/gap over levels) = {float(thickmin):.6f}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    f = sub.add_parser("flagship"); f.add_argument("--depth", type=int, default=4000)
    f.add_argument("--out", default="/tmp/e257_flagship.json"); f.set_defaults(fn=cmd_flagship)
    m = sub.add_parser("marginlaw"); m.add_argument("--depth", type=int, default=2000)
    m.set_defaults(fn=cmd_marginlaw)
    s = sub.add_parser("survey"); s.add_argument("--n", type=int, default=20000)
    s.add_argument("--depth", type=int, default=120); s.add_argument("--qmax", type=int, default=10**6)
    s.add_argument("--seed", type=int, default=1); s.set_defaults(fn=cmd_survey)
    g = sub.add_parser("gapcensus"); g.add_argument("--levels", type=int, default=40)
    g.set_defaults(fn=cmd_gapcensus)
    fp = sub.add_parser("fingerprint"); fp.add_argument("--depth", type=int, default=4000)
    fp.add_argument("--controls", type=int, default=4); fp.add_argument("--seed", type=int, default=7)
    fp.add_argument("--out", default="/tmp/e257_fingerprint.json"); fp.set_defaults(fn=cmd_fingerprint)
    a = ap.parse_args(); a.fn(a)



# ------------------------------------------------- arithmetic fingerprint test
def _ord2(q):
    q = q // (q & -q)          # odd part
    if q == 1:
        return 0
    r, v = 1, 2 % q
    while v != 1:
        v = (v * 2) % q; r += 1
    return r


def _tau_sieve(N):
    t = [0] * (N + 1)
    for d in range(1, N + 1):
        for m in range(d, N + 1, d):
            t[m] += 1
    return t


def _autocorr(word, lmax):
    D = len(word)
    s = [2 * b - 1 for b in word]
    out = []
    for l in range(1, lmax + 1):
        c = sum(s[i] * s[i + l] for i in range(D - l)) / (D - l)
        out.append((l, c, c * math.sqrt(D - l)))   # z-score
    return out


def cmd_fingerprint(a):
    """Does the support word of p/q remember q?  Autocorrelation at lag ord_q(2),
    residue-class bias mod ord, divisor-count bias, and an irrational control."""
    eng = Engine(a.depth)
    tau = _tau_sieve(a.depth + 1)
    targets = [(n, p, q) for n, p, q in FLAGSHIPS if q != 3]
    rnd = random.Random(a.seed)
    words = {}
    for name, p, q in targets:
        r = eng.run(p, q)
        if r["status"] != "alive":
            print(f"{name}: {r['status']} @ {r['death']}"); continue
        words[f"{name} (ord={_ord2(q)})"] = (r["word"], _ord2(q))
    # irrational controls: uniformly random fixed-point reals
    for c in range(a.controls):
        M = eng.M
        rho = rnd.randrange(1 << (M - 1), 1 << M)     # random real in [1/2,1)
        w, That, rho_err = [], eng.T0, 1
        ok = True
        for n in range(1, a.depth + 1):
            wn = eng.W[n]; That -= wn
            if rho >= wn + rho_err:
                rho -= wn; rho_err += 1; w.append(1)
            elif rho + rho_err <= wn:
                if rho + rho_err <= That: w.append(0)
                else: ok = False; break
            else:
                ok = False; break
        if ok:
            words[f"control#{c}"] = (w, 0)

    print(f"{'target':>22} {'D':>6} {'dens':>7} {'maxrun':>7} "
          f"{'|z|max lag<=120':>16} {'at lag':>7} {'z@ord':>8} {'chi2 mod ord':>13} {'tau-bias z':>11}")
    res = {}
    for name, (w, r) in words.items():
        D = len(w)
        ac = _autocorr(w, min(120, D // 4))
        zbest = max(ac, key=lambda t: abs(t[2]))
        zord = next((t[2] for t in ac if t[0] == r), float('nan')) if r else float('nan')
        # residue-class bias mod r
        chi = float('nan')
        if r:
            cnt = [[0, 0] for _ in range(r)]
            for i, b in enumerate(w):
                cnt[(i + 1) % r][b] += 1
            chi = sum((c[1] - (c[0] + c[1]) / 2) ** 2 / ((c[0] + c[1]) / 4) for c in cnt if c[0] + c[1])
        # divisor-count bias: correlation of b_n with tau(n)
        mt = sum(tau[i + 1] for i in range(D)) / D
        num = sum((2 * w[i] - 1) * (tau[i + 1] - mt) for i in range(D))
        sd = math.sqrt(sum((tau[i + 1] - mt) ** 2 for i in range(D)))
        ztau = num / sd if sd else 0.0
        print(f"{name:>22} {D:>6} {sum(w)/D:>7.4f} {max_run(w):>7} "
              f"{abs(zbest[2]):>16.3f} {zbest[0]:>7} {zord:>8.3f} {chi:>13.3f} {ztau:>11.3f}")
        res[name] = {"density": sum(w) / D, "max_run": max_run(w),
                     "zmax": zbest[2], "zmax_lag": zbest[0], "z_at_ord": zord,
                     "chi2_mod_ord": chi, "z_tau": ztau, "ord": r}
    print("\n(|z| ~ N(0,1) under the null.  chi2 has r-1 dof.)")
    kmax = max(2, int(math.log2(a.depth)) - 1)
    print(f"\nsubword complexity p(k) vs 2^k  (k<= {kmax}):")
    for name, (w, r) in words.items():
        sc = subword_complexity(w, kmax)
        row = " ".join(f"{sc[k]}/{min(1<<k, len(w)-k+1)}" for k in sorted(sc))
        print(f"  {name:>22}: {row}")
    with open(a.out, "w") as f:
        json.dump(res, f, indent=1)



if __name__ == "__main__":
    main()
