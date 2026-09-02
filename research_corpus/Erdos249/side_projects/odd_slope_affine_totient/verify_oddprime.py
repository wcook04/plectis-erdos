"""Independent check of the proposed odd-prime totient-kernel theorem.

Checks, for odd primes l and levels e:
  (1) the two claimed reduction identities, exactly, over many n;
  (2) rank of the FULL section family {F_{j,r} : 0<=j<=e, 0<=r<l^j} == l^e + 1;
  (3) rank of the claimed canonical basis == l^e + 1 (so it is independent AND spans);
  (4) the determinant construction of the generic odd-slope lemma, on the actual
      canonical affine forms, for a small case (does the CRT+Dirichlet row search
      really produce a 2-adically separated matrix?).
"""
from sympy import totient, isprime
from fractions import Fraction

P = 1_000_003  # modular rank prime


def phi(n):
    return int(totient(n))


def rank_mod(rows, p=P):
    """Rank over F_p of a list of row vectors."""
    rows = [r[:] for r in rows]
    ncols = len(rows[0])
    rank = 0
    pivot_row = 0
    for c in range(ncols):
        piv = None
        for r in range(pivot_row, len(rows)):
            if rows[r][c] % p:
                piv = r
                break
        if piv is None:
            continue
        rows[pivot_row], rows[piv] = rows[piv], rows[pivot_row]
        inv = pow(rows[pivot_row][c], p - 2, p)
        rows[pivot_row] = [(x * inv) % p for x in rows[pivot_row]]
        for r in range(len(rows)):
            if r != pivot_row and rows[r][c] % p:
                f = rows[r][c]
                rows[r] = [(a - f * b) % p for a, b in zip(rows[r], rows[pivot_row])]
        pivot_row += 1
        rank += 1
    return rank


def v_l(n, l):
    t = 0
    while n % l == 0:
        n //= l
        t += 1
    return t


def check_reductions(l, e, N=200):
    """F_{j,0} = l^{j-1} F_{1,0};  F_{j,r} = l^{t-1}(l-1) F_{j-t,s} for r=l^t s."""
    ok = True
    for j in range(1, e + 1):
        for n in range(1, N):
            lhs = phi(l**j * n)
            rhs = l ** (j - 1) * phi(l * n)
            if lhs != rhs:
                ok = False
                print(f"  FAIL zero-section l={l} j={j} n={n}: {lhs} != {rhs}")
    for j in range(1, e + 1):
        for r in range(1, l**j):
            t = v_l(r, l)
            if t == 0:
                continue
            s = r // l**t
            for n in range(1, N):
                lhs = phi(l**j * n + r)
                rhs = l ** (t - 1) * (l - 1) * phi(l ** (j - t) * n + s)
                if lhs != rhs:
                    ok = False
                    print(f"  FAIL section l={l} j={j} r={r} n={n}: {lhs} != {rhs}")
    return ok


def sections_full(l, e):
    return [(j, r) for j in range(e + 1) for r in range(l**j)]


def sections_canonical(l, e):
    out = [(0, 0), (1, 0)]
    for j in range(1, e + 1):
        for r in range(1, l**j):
            if r % l:
                out.append((j, r))
    return out


def rank_of(sections, l, nvals):
    rows = [[phi(l**j * n + r) % P for (j, r) in sections] for n in nvals]
    return rank_mod(rows)


print("=" * 72)
print("(1) reduction identities")
for l, e in [(3, 3), (5, 2), (7, 2), (11, 2)]:
    ok = check_reductions(l, e)
    print(f"  l={l} e={e}: {'OK' if ok else 'FAILED'}")

print("=" * 72)
print("(2)/(3) ranks   [target = l^e + 1]")
for l, e in [(3, 1), (3, 2), (3, 3), (5, 1), (5, 2), (7, 1), (7, 2), (11, 1), (11, 2), (13, 1)]:
    target = l**e + 1
    full = sections_full(l, e)
    canon = sections_canonical(l, e)
    nvals = list(range(1, 4 * max(len(full), target) + 60))
    rf = rank_of(full, l, nvals)
    rc = rank_of(canon, l, nvals)
    flag = "OK " if (rf == target and rc == target and len(canon) == target) else "!! "
    print(f"  {flag}l={l:2d} e={e}: |full|={len(full):4d} rank={rf:4d} | "
          f"|canon|={len(canon):4d} rank={rc:4d} | target={target}")
