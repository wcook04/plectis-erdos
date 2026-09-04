"""Independent check of the ALL-BASE totient k-kernel claim (every integer k >= 2).

Type B claims, for every integer k >= 2 and e >= 1:

  (R0)  F_{j,0} = k^{j-1} * F_{1,0}                       for j >= 1
  (R1)  F_{j,r} = C_k(t,u) * F_{j-t,u}   where r = k^t u, k does not divide u,
        and  C_k(t,u) = k^t * prod_{p | k, p does not divide u} (1 - 1/p)
  (D)   dim_Q span{F_{j,r} : 0<=j<=e, 0<=r<k^j} = k^e + 1
  (B)   with basis {F_{0,0}, F_{1,0}} u {F_{j,r} : 1<=j<=e, 1<=r<k^j, k does not divide r}

Note the composite condition is  k does not divide r,  NOT gcd(k,r)=1.

Everything below is exact integer arithmetic; ranks are computed over F_p with a
large prime p, which is a LOWER bound for the rational rank.
"""
from fractions import Fraction

from sympy import factorint, totient

P = 1_000_003


def phi(n: int) -> int:
    return int(totient(n))


def rank_mod(rows, p=P):
    rows = [r[:] for r in rows]
    if not rows:
        return 0
    ncols = len(rows[0])
    rank = piv = 0
    for c in range(ncols):
        sel = None
        for r in range(piv, len(rows)):
            if rows[r][c] % p:
                sel = r
                break
        if sel is None:
            continue
        rows[piv], rows[sel] = rows[sel], rows[piv]
        inv = pow(rows[piv][c], p - 2, p)
        rows[piv] = [(x * inv) % p for x in rows[piv]]
        for r in range(len(rows)):
            if r != piv and rows[r][c] % p:
                f = rows[r][c]
                rows[r] = [(a - f * b) % p for a, b in zip(rows[r], rows[piv])]
        piv += 1
        rank += 1
    return rank


def v_k(r: int, k: int) -> int:
    """Largest t with k^t | r."""
    t = 0
    while r % k == 0:
        r //= k
        t += 1
    return t


def C_k(t: int, u: int, k: int) -> Fraction:
    c = Fraction(k) ** t
    for p in factorint(k):
        if u % p:
            c *= Fraction(p - 1, p)
    return c


def check_reductions(k: int, e: int, N: int = 120):
    ok = True
    # (R0)
    for j in range(1, e + 1):
        for n in range(1, N):
            if phi(k**j * n) != k ** (j - 1) * phi(k * n):
                ok = False
                print(f"  FAIL R0 k={k} j={j} n={n}")
    # (R1)
    for j in range(1, e + 1):
        for r in range(1, k**j):
            t = v_k(r, k)
            if t == 0:
                continue
            u = r // k**t
            c = C_k(t, u, k)
            if c.denominator != 1:
                print(f"  FAIL C_k not integral k={k} t={t} u={u} -> {c}")
                ok = False
                continue
            for n in range(1, N):
                if phi(k**j * n + r) != int(c) * phi(k ** (j - t) * n + u):
                    ok = False
                    print(f"  FAIL R1 k={k} j={j} r={r} (t={t},u={u},C={c}) n={n}")
                    break
    return ok


def sections_full(k, e):
    return [(j, r) for j in range(e + 1) for r in range(k**j)]


def sections_basis(k, e):
    out = [(0, 0), (1, 0)]
    for j in range(1, e + 1):
        out += [(j, r) for r in range(1, k**j) if r % k]
    return out


def rank_of(sections, k, nvals):
    return rank_mod([[phi(k**j * n + r) % P for (j, r) in sections] for n in nvals])


print("=" * 78)
print("(A) reduction identities, incl. the composite coefficient C_k(t,u)")
for k, e in [(2, 3), (3, 3), (4, 3), (6, 2), (8, 2), (9, 2), (10, 2), (12, 2), (15, 2), (16, 2)]:
    print(f"  k={k:2d} e={e}: {'OK' if check_reductions(k, e) else 'FAILED'}")

print("=" * 78)
print("(B) ranks: full family and proposed basis vs k^e + 1")
CASES = [(2, 3), (3, 3), (4, 3), (5, 2), (6, 2), (8, 2), (9, 2), (10, 2), (12, 2), (15, 2), (16, 2)]
for k, e in CASES:
    target = k**e + 1
    full, basis = sections_full(k, e), sections_basis(k, e)
    nvals = list(range(1, 3 * max(len(full), target) + 60))
    rf, rb = rank_of(full, k, nvals), rank_of(basis, k, nvals)
    good = rf == target and rb == target and len(basis) == target
    print(f"  {'OK ' if good else '!! '}k={k:2d} e={e}: |full|={len(full):4d} rank={rf:4d} | "
          f"|basis|={len(basis):4d} rank={rb:4d} | k^e+1={target}")

print("=" * 78)
print("(C) the gcd-vs-divides distinction: basis uses k∤r, NOT gcd(k,r)=1")
for k, e in [(4, 2), (6, 2), (12, 2)]:
    coprime = [(0, 0), (1, 0)] + [
        (j, r) for j in range(1, e + 1) for r in range(1, k**j)
        if __import__("math").gcd(r, k) == 1
    ]
    print(f"  k={k:2d} e={e}: |k∤r basis|={len(sections_basis(k, e)):4d}  "
          f"|gcd=1 basis|={len(coprime):4d}  k^e+1={k**e + 1}  "
          f"-> gcd-version is {'TOO SMALL' if len(coprime) < k**e + 1 else 'equal'}")
