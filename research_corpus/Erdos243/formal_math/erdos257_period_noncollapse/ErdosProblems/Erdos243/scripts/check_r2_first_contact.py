#!/usr/bin/env python3
"""Exact finite replay of the first-contact valuation resonance identity."""
import json
from math import gcd


def valuation(n, p):
    assert n > 0
    e = 0
    while n % p == 0:
        e += 1
        n //= p
    return e


def main():
    contacts = 0
    checked = 0
    for lam in range(2, 101):
        for a in range(2, 101):
            rho = gcd(lam, a)
            for u in range(1, 51):
                numerator = a*u-lam
                if numerator <= 0 or numerator % rho:
                    continue
                v = numerator//rho
                for p in (2, 3, 5, 7):
                    if lam % p or u % p == 0:
                        continue
                    checked += 1
                    if v % p == 0:
                        contacts += 1
                        assert valuation(a, p) == valuation(lam, p)
                        assert (a//rho*u-lam//rho) % p == 0
    for m in range(2, 100):
        u = m*m+1
        a = u+m+1
        lam = (a-1)*u-m
        assert gcd(lam, a) == gcd(lam, u) == 1
        assert a*u-lam == u+m
    print(json.dumps({"status": "pass", "exact_states": checked, "first_contacts": contacts,
                      "scope": "finite regression; universal valuation proof is in R2CumulativePayment.md"}))


if __name__ == "__main__":
    main()
