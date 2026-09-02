import exact
from lemma_s import sep_lower, delta_upper

conv = exact.convergents(exact.ALPHA_LO, exact.ALPHA_HI, 1200)
print("r      log2(p_r)  elementary_window_Amax   tested(A>=1)  failures")
tot = fail = 0
for r in [4, 9, 19, 39, 59, 79, 99, 124, 149, 183, 249, 399]:
    n, p = conv[r]
    du = delta_upper(p, n)
    A_max = 0
    while A_max < 700 and du <= sep_lower(A_max + 1):
        A_max += 1
    ck = f = 0
    for A in list(range(1, 13)) + [A_max - 1, A_max]:
        if A < 1 or A > A_max:
            continue
        lhs, rhs = exact.s(A + n), exact.C_p(p, A, n) + exact.s(A)
        ck += 1
        if lhs != rhs:
            f += 1
            print("   FAIL r=%d A=%d diff=%d" % (r, A, lhs - rhs))
    tot += ck; fail += f
    print("%-6d %-10.1f %-24d %-13d %d" % (r, p.bit_length(), A_max, ck, f))
print("\nA>=1 TOTAL: %d instances, %d failures" % (tot, fail))
