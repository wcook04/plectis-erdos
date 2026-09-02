"""V0: self-check of the wave-7 floor-sum engine against (a) exact big-integer
brute force, (b) the wave-6 mpmath Lemma-T sweep, and verification of the three
new identities (W)/(N)/(TEL).  Nothing downstream is trusted until this is clean."""
import sys
import mpmath as mp

HERE = '/private/tmp/claude-501/-Users-willcook-src-ai-workflow/76b0c5ba-891b-4307-a452-6a1288bc4a66/scratchpad'
sys.path.insert(0, HERE + '/wave7_mrl_pointwise')
sys.path.insert(0, HERE + '/wave6_mrl_prime')
import eng

mp.mp.dps = 260
AL = mp.log(3, 2)
BE = mp.log(5, 2)
TH = AL / BE
G = 1 / BE


def lev(x):
    return x.bit_length() - 1


def brute_T_p(p, M):
    """#{(i,w): i<p, w>=0, 3^i 5^w < 2^M}, exact big-int."""
    c = 0
    P3 = 1
    for i in range(p):
        if P3 >= 1 << M:
            break
        v = P3
        while v < (1 << M):
            c += 1
            v *= 5
        P3 *= 3
    return c


def brute_T_full(M):
    c = 0
    P3 = 1
    while P3 < (1 << M):
        v = P3
        while v < (1 << M):
            c += 1
            v *= 5
        P3 *= 3
    return c


def sweep_F(p, x):
    return sum(1 for i in range(p) if mp.frac(x - i * TH) > 1 - G)


print("=== A. T_p(M) == -W_p(M) against exact big-int brute force ===")
bad = 0
tests = 0
for (p, M) in [(1, 5), (2, 9), (5, 20), (12, 30), (41, 80), (53, 120), (100, 200),
               (306, 500), (665, 1100), (7, 400), (665, 5000)]:
    a = eng.T_p(p, M)
    b = brute_T_p(p, M)
    tests += 1
    if a != b:
        bad += 1
        print(f"   MISMATCH p={p} M={M}: engine {a} brute {b}")
print(f"   {tests} tests, mismatches = {bad} -> {'PASS' if bad == 0 else 'FAIL'}")

print("\n=== B. T(M) and s(M) against brute force ===")
bad = 0
for M in list(range(1, 60)) + [100, 137, 200, 301]:
    if eng.T_full(M) != brute_T_full(M):
        bad += 1
        print(f"   MISMATCH T({M})")
s_small = [eng.s(M) for M in range(15)]
print(f"   s(0..14) = {s_small}")
print(f"   mismatches = {bad} -> {'PASS' if bad == 0 else 'FAIL'}"
      f"   (brute force = independent enumeration of 3^u 5^v < 2^M)")

print("\n=== C. Lemma T cross-check: N_p(M) == F_p({M*ell}) (mpmath sweep) ===")
bad = tot = 0
for (p, n) in [(1, 1), (2, 3), (5, 8), (12, 19), (41, 65), (53, 84), (306, 485), (665, 1054)]:
    for A in range(0, 40):
        M = A + n
        a = eng.N_p(p, M)
        b = sweep_F(p, mp.frac(mp.mpf(M) / BE))
        tot += 1
        if a != b:
            bad += 1
            if bad < 4:
                print(f"   MISMATCH p={p} A={A}: floor-sum {a} sweep {b}")
print(f"   {tot} tests, mismatches = {bad} -> {'PASS' if bad == 0 else 'FAIL'}")

print("\n=== D. (TEL) telescoping column identity ===")
bad = tot = 0
for (p, n) in [(5, 8), (12, 19), (41, 65), (53, 84), (306, 485), (665, 1054)]:
    for A1 in range(0, 6):
        for A2 in range(A1, A1 + 25):
            lhs = sum(eng.C_p(p, n, A) for A in range(A1, A2 + 1))
            rhs = eng.T_p(p, A2 + n + 1) - eng.T_p(p, A1 + n)
            tot += 1
            if lhs != rhs:
                bad += 1
print(f"   {tot} (p,A1,A2) triples, mismatches = {bad} -> {'PASS' if bad == 0 else 'FAIL'}")

print("\n=== E. (TEL2) closed form  sum_{A<L} C_p(A) = p*floor(L*ell) + Phi_p({L*ell}) ===")
print("     Phi_p(c) = #{0<=i<p : {i*gamma - n*ell} in (0,c)}")
bad = tot = 0
for (p, n) in [(12, 19), (41, 65), (53, 84), (306, 485), (665, 1054)]:
    for L in range(1, 26):
        lhs = sum(eng.C_p(p, n, A) for A in range(0, L))
        c = mp.frac(L / BE)
        fl = int(mp.floor(L / BE))
        x0 = mp.frac(mp.mpf(n) / BE)
        phi = sum(1 for i in range(p) if 0 < mp.frac(i * TH - x0) < c)
        rhs = p * fl + phi
        tot += 1
        if lhs != rhs:
            bad += 1
            if bad < 4:
                print(f"   MISMATCH p={p} L={L}: lhs {lhs} rhs {rhs} (fl={fl} phi={phi})")
print(f"   {tot} (p,L) pairs, mismatches = {bad} -> {'PASS' if bad == 0 else 'FAIL'}")

print("\n=== F. corrected Lemma S bridge: C_p(A) = s(A+n) - s(A) - (sliver) ===")
print("     sliver(A) := [s(A+n)-s(A)] - C_p(A)  (0 iff both slivers balance)")
for (p, n) in [(12, 19), (41, 65), (53, 84), (306, 485), (665, 1054)]:
    sl = [(eng.s(A + n) - eng.s(A)) - eng.C_p(p, n, A) for A in range(0, 20)]
    print(f"   p={p:5d} n={n:5d}: sliver(A) A=0..19 = {sl}")
