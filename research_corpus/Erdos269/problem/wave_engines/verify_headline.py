"""END-TO-END exact verification of the headline block.

Normalization-proof: the whole [P2*] chain is re-derived from raw digits with
exact Fractions on genuine tail enclosures, so no factor-15 convention is
assumed anywhere.  Chain being checked, for X_a := Q_a * sum_{h>=2^a} 1/H(h):

  (T1)  X_a = e_a/15 + X_{a+1}/b_a                       [shell recursion]
  (T2)  X_a = X_{a+L}/P + 2*Ehat'_{a,L}/P                [window transport]
  (T3)  0 <= X_a <= W(a) = a^2+6a+11                     [width theorem]
  (i*)  sum_r c_r Ehat'_r = 0  (mod P/2)   =>  k := (2/P) sum c_r Ehat'_r in Z
  =>    | sum_r c_r X_{a_r}  -  k |  <=  (1/P) sum_r |c_r| W(a_r+L)
  (ii)  sum_r c_r Q_{a_r} != 0 (mod B)     =>  dist(sum c_r X_{a_r}, Z) >= 1/B
  (iii*) B * sum_r |c_r| W(a_r+L) < P      =>  CONTRADICTION.
"""
import pickle, math, json, sys
from fractions import Fraction
import numpy as np
import blocks as BK
import lattice as LA
import engine as E

e, b, Bx, Cx = BK.load(60000)
blk = pickle.load(open("headline_block.pkl", "rb"))
L, m, starts = blk["L"], blk["m"], blk["starts"]
P, m0, basis, S = blk["P"], blk["m0"], blk["basis"], blk["S"]
report = {}
fails = []


def ck(name, cond, extra=""):
    print(("PASS " if cond else "FAIL ") + name + ("  " + extra if extra else ""))
    if not cond:
        fails.append(name)
    return cond


print("HEADLINE BLOCK  L=%d  m=%d  a1=%d  a_m=%d" % (L, m, starts[0], starts[-1]))
print("starts:", starts)
print()

# ---------- 1. re-derive Ehat' from raw digits, independent code path ----------
DEPTH = min(260, len(e) - 2 - max(starts) - L)
TOP = max(starts) + L + DEPTH
assert TOP < len(e), (TOP, len(e))
print("tail-enclosure depth beyond a_max+L: %d" % DEPTH)

Ehp = []
for a in starts:
    acc = 0
    pr = 1
    for t in range(L):
        bb = b[a + t]
        acc = bb * (acc + e[a + t])
        pr = bb * pr
    ck("P matches at a=%d" % a, pr == P) if a == starts[0] else None
    assert pr == P
    assert acc % 30 == 0
    Ehp.append(acc // 30)
ck("Ehat' re-derived from raw digits == certificate g (mod m0)",
   all((x % m0) == gi for x, gi in zip(Ehp, blk["g"])))

# ---------- 2. exact tail enclosures for X ----------
def enclosures(a_lo, a_hi):
    """Fraction interval enclosures [lo,hi] for X_a, a in [a_lo,a_hi],
    seeded from the width theorem at depth DEPTH beyond a_hi."""
    top = a_hi + DEPTH
    lo = Fraction(0)
    hi = Fraction(E.W_width(top))
    out = {}
    for a in range(top - 1, a_lo - 1, -1):
        d = Fraction(e[a], 15)
        lo, hi = d + lo / b[a], d + hi / b[a]
        if a_lo <= a <= a_hi:
            out[a] = (lo, hi)
    return out

need = sorted(set(starts) | set(a + L for a in starts))
X = enclosures(min(need), max(need))
wid = max(float(X[a][1] - X[a][0]) for a in need)
print("enclosure width (max over needed a): %.3e   [depth %d]" % (wid, DEPTH))

# (T3) width theorem + positivity, verified on the enclosures
ck("(T3) 0 <= X_a and X_a <= W(a) at all needed a",
   all(X[a][0] >= 0 and X[a][1] <= E.W_width(a) for a in need))
rat = max(float(X[a][1]) / E.W_width(a) for a in need)
print("     max X_a / W(a) = %.4f  (slack factor %.1fx)" % (rat, 1 / rat))

# (T2) window transport, per member, as an interval containment
bad = []
for a, ep in zip(starts, Ehp):
    lo1, hi1 = X[a + L]
    rhs_lo = lo1 / P + Fraction(2 * ep, P)
    rhs_hi = hi1 / P + Fraction(2 * ep, P)
    lo0, hi0 = X[a]
    if not (rhs_lo <= hi0 and rhs_hi >= lo0):
        bad.append(a)
ck("(T2) X_a = X_{a+L}/P + 2*Ehat'/P  at every member", not bad, str(bad[:5]))

# ---------- 3. re-check the basis exactly ----------
ck("basis vectors satisfy (i*) exactly:  sum c_r Ehat'_r = 0 mod P/2",
   all(sum(c * x for c, x in zip(v, Ehp)) % m0 == 0 for v in basis))
det = LA.det_bareiss(basis)
ck("basis determinant == [Z^m : Lambda] == m0",
   abs(det) == blk["index"] and blk["index"] == m0,
   "|det|=m0=2^%.2f" % math.log2(m0))
Sre = [E.W_width(a + L) for a in starts]
ck("weights S_r == W(a_r+L) recomputed", Sre == S)
buds = [LA.budget(v, S) for v in basis]
ck("budgets recomputed exactly", buds == blk["budgets"])
bmb = max(buds)
beta = bmb + 1
ck("every basis vector has budget < beta  =>  Lambda_beta = Lambda  =>  J = 1",
   all(x < beta for x in buds))
Bmax = (P - 1) // bmb
ck("Bmax * maxbudget < P   (coordinator integer form)", Bmax * bmb < P)
ck("Bmax is maximal: (Bmax+1)*maxbudget >= P", (Bmax + 1) * bmb >= P)

# ---------- 4. the master inequality, end to end, with exact Fractions ----------
worst = Fraction(0)
badc = []
for v in basis:
    num = sum(c * x for c, x in zip(v, Ehp))
    k = Fraction(2 * num, P)
    assert k.denominator == 1
    k = k.numerator
    # T = sum c_r X_{a_r} : exact interval
    tlo = sum(Fraction(c) * (X[a][0] if c > 0 else X[a][1]) for c, a in zip(v, starts))
    thi = sum(Fraction(c) * (X[a][1] if c > 0 else X[a][0]) for c, a in zip(v, starts))
    bnd = Fraction(LA.budget(v, S), P)
    if not (tlo - k >= -bnd and thi - k <= bnd):
        badc.append(v)
    w = max(abs(tlo - k), abs(thi - k)) / bnd
    if w > worst:
        worst = w
ck("|sum c_r X_{a_r} - k| <= (1/P) sum |c_r| W(a_r+L) for every basis vector",
   not badc, "tightest ratio %.4f" % float(worst))

# ---------- 5. explicit (ii)-witnesses for sample B ----------
def Qmod(a, B):
    return (pow(2, a, B) * pow(3, Bx[a], B) * pow(5, Cx[a], B)) % B

samples = [7, 11, 13, 101, 1009, 65537, 10**6 + 3, 10**9 + 7, 10**12 + 39,
           10**15 + 37, 2 * 10**17 + 1]
samples = [x for x in samples if x <= Bmax and math.gcd(x, 30) == 1]
wit = []
for Bv in samples:
    found = None
    for v in basis:
        if sum(c * Qmod(a, Bv) for c, a in zip(v, starts)) % Bv != 0:
            if Bv * LA.budget(v, S) < P:
                found = v
                break
    wit.append((Bv, found is not None))
ck("explicit [P2*] witness (i*)+(ii)+(iii*) found for every sampled B",
   all(f for _, f in wit), str([(bv, ok) for bv, ok in wit]))

# ---------- 6. certificate parameters ----------
a1 = starts[0]
Qexp = (a1, Bx[a1], Cx[a1])
report = dict(
    L=L, m=m, a1=a1, starts=starts,
    P=str(P), log2P=math.log2(P), m0=str(m0),
    index=str(blk["index"]), index_eq_m0=(blk["index"] == m0),
    Q_a1_exponent_triple=dict(two=Qexp[0], three=Qexp[1], five=Qexp[2]),
    log2_Q_a1=Qexp[0] + Qexp[1] * math.log2(3) + Qexp[2] * math.log2(5),
    max_budget=str(bmb), log2_max_budget=math.log2(bmb),
    beta=str(beta), Bmax=str(Bmax), log2Bmax=math.log2(Bmax),
    Bmax_decimal_digits=len(str(Bmax)),
    budgets_log2=[round(math.log2(x), 3) for x in sorted(buds)],
    basis=[list(map(str, v)) for v in basis],
    enclosure_width=float(wid), max_X_over_W=rat,
    J="1 (certified: LLL basis of Lambda lies inside the budget)",
    all_checks_passed=not fails, failures=fails,
)
json.dump(report, open("headline_certificate.json", "w"), indent=1)

print()
print("=== HEADLINE CERTIFICATE ===")
print("L=%d  m=%d  a1=%d  a_max=%d" % (L, m, a1, starts[-1]))
print("P = %d   (2^%.3f)" % (P, math.log2(P)))
print("Q_{a1} = 2^%d * 3^%d * 5^%d   (%.0f bits)" % (Qexp[0], Qexp[1], Qexp[2],
                                                     report["log2_Q_a1"]))
print("max budget sum|c_r|W(a_r+L) = %d  (2^%.3f)" % (bmb, math.log2(bmb)))
print("beta = %d ;  J = 1 certified")
print("B_max = %d" % Bmax)
print("      = 2^%.3f = %.4e  (%d decimal digits)" % (math.log2(Bmax), float(Bmax),
                                                      len(str(Bmax))))
print("FAILURES:", fails if fails else "none")
sys.exit(1 if fails else 0)
