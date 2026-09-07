#!/usr/bin/env python3
"""
Erdos 257 -- MULTIPLICATIVE correlations in the greedy support word.

Every correlation study in this corpus (and section 4 of the companion note) has
tested ADDITIVE structure: autocorrelation at lag l, residue classes mod ord_q(2),
tau(n) bias.  All null.

But the problem does not live on an additive lattice.  The exact identity is

    sum_{k in A} 1/(2^k - 1) = sum_m tau_A(m) 2^-m,   tau_A(m) = #{d in A : d | m},

so the coupling between support bits is by DIVISIBILITY: b_d and b_m interact
exactly when d | m.  The natural correlation axis is therefore multiplicative --
corr(b_n, b_{dn}) -- and it has never been measured.

Null: the support word is density ~1/2 and additively generic, so under the null
each z is standard normal.  A significant multiplicative z would be the first
arithmetic fingerprint in the support word.

Controls included:
  * a matched random word of the same length and density;
  * the SAME multiplicative statistic on a shifted copy of the word (destroys
    divisor alignment, preserves everything else);
  * a Bonferroni-aware summary over all multipliers tested.
"""
from __future__ import annotations
import sys, math, random
sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

D = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
MULTS = list(range(2, 17))
eng = Engine(D)
TARGETS = [("1/2",1,2),("1/21",1,21),("4/9",4,9),("1/465",1,465),("1/5",1,5),("5/12",5,12)]

def mult_z(w, d):
    """z of corr(b_n, b_{dn}) over n with dn <= len(w)."""
    N = len(w) // d
    if N < 50: return 0.0, 0
    s = 0
    for n in range(1, N+1):
        s += (2*w[n-1]-1) * (2*w[d*n-1]-1)
    return s / math.sqrt(N), N

print(f"depth {D}\n")
hdr = "  ".join(f"d={d:<2}" for d in MULTS)
print(f"{'target':>10} | {hdr}")
allz = []
for name, p, q in TARGETS:
    r = eng.run(p, q)
    if r["status"] != "alive": print(f"{name}: {r['status']}"); continue
    w = r["word"]
    zs = [mult_z(w, d)[0] for d in MULTS]
    allz += [abs(z) for z in zs]
    print(f"{name:>10} | " + "  ".join(f"{z:>5.2f}" for z in zs))

# control 1: matched random words
rnd = random.Random(11)
ctrl = []
for t in range(6):
    w = [1 if rnd.random() < 0.5 else 0 for _ in range(D)]
    ctrl += [abs(mult_z(w, d)[0]) for d in MULTS]
# control 2: shifted real word (destroys divisor alignment)
r = eng.run(1, 21); w21 = r["word"]
sh = w21[7:] + w21[:7]
shz = [abs(mult_z(sh, d)[0]) for d in MULTS]

n = len(allz)
print(f"\n{'':>10}   max |z|   mean |z|   #(|z|>2)   #(|z|>3)   cells")
print(f"{'targets':>10}   {max(allz):>7.3f}   {sum(allz)/n:>8.3f}   "
      f"{sum(1 for z in allz if z>2):>8}   {sum(1 for z in allz if z>3):>8}   {n:>5}")
m = len(ctrl)
print(f"{'random':>10}   {max(ctrl):>7.3f}   {sum(ctrl)/m:>8.3f}   "
      f"{sum(1 for z in ctrl if z>2):>8}   {sum(1 for z in ctrl if z>3):>8}   {m:>5}")
k = len(shz)
print(f"{'1/21 shift':>10}   {max(shz):>7.3f}   {sum(shz)/k:>8.3f}   "
      f"{sum(1 for z in shz if z>2):>8}   {sum(1 for z in shz if z>3):>8}   {k:>5}")
print(f"\nnull expectation for max |z| over {n} cells ~ {math.sqrt(2*math.log(n)):.2f};")
print(f"expected #(|z|>2) ~ {0.0455*n:.1f}, #(|z|>3) ~ {0.0027*n:.1f}")
