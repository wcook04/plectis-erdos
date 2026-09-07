"""Wave-9: how big are the two edge terms E1,E2 in  s(K) = 1 + E1 + E2 (mod 2)?

If E1,E2 are O(1) while s(K) ~ 0.2717*K, the corollary is a genuine
complexity reduction: the parity of a growing shell count is decided by
two bounded counts at the shell edges.
"""
from fractions import Fraction
import collections, statistics
import exact

AL, AH, BL, BH = exact.ALPHA_LO, exact.ALPHA_HI, exact.BETA_LO, exact.BETA_HI


def balanced(i, j):
    outs = set()
    for al, be in ((AL, BL), (AH, BH)):
        outs.add((j * be <= i * al + al - Fraction(1, 2),
                  i * al <= j * be + be - Fraction(1, 2)))
    if len(outs) != 1:
        return None
    a, b = outs.pop()
    return a and b


def smooth_upto(lim):
    out, p3 = [], 1
    while p3 <= lim:
        y = p3
        while y <= lim:
            out.append(y); y *= 5
        p3 *= 3
    return sorted(out)


IMAX = 130
rows = []
for i in range(1, IMAX):
    for j in range(0, IMAX):
        if not balanced(i, j):
            continue
        x = 3 ** i * 5 ** j
        x2 = x * x
        K = (x2.bit_length() - 2) // 2
        if K < 1:
            continue
        S = smooth_upto(2 * x)
        E1 = sum(1 for y in S if y >= (1 << K) and 2 * y * y <= x2)
        E2 = sum(1 for y in S if y >= (1 << (K + 1)) and y * y < 2 * x2)
        sK = sum(1 for y in S if (1 << K) <= y < (1 << (K + 1)))
        assert (sK - (1 + E1 + E2)) % 2 == 0, (i, j)
        rows.append((K, E1, E2, sK))

Ks = sorted({r[0] for r in rows})
print("levels K reached by a balanced anchor: %d distinct, K range %d..%d"
      % (len(Ks), min(Ks), max(Ks)))
print("coverage: %.3f of all K in range" % (len(Ks) / (max(Ks) - min(Ks) + 1)))
E1s = [r[1] for r in rows]; E2s = [r[2] for r in rows]; sKs = [r[3] for r in rows]
print()
print("E1 distribution:", dict(sorted(collections.Counter(E1s).items())))
print("E2 distribution:", dict(sorted(collections.Counter(E2s).items())))
print("max E1 = %d, max E2 = %d,  max s(K) = %d  (s ~ 0.2717*K)" % (max(E1s), max(E2s), max(sKs)))
print("mean E1 = %.3f, mean E2 = %.3f, mean s(K) = %.1f" %
      (statistics.mean(E1s), statistics.mean(E2s), statistics.mean(sKs)))
print()
both0 = sum(1 for r in rows if r[1] == 0 and r[2] == 0)
print("anchors with E1 = E2 = 0 (=> s(K) ODD unconditionally): %d / %d" % (both0, len(rows)))
odd = sum(1 for r in rows if r[3] % 2)
print("anchors whose level has s(K) odd: %d / %d" % (odd, len(rows)))
