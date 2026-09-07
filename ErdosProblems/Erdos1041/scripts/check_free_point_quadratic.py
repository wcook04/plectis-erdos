#!/usr/bin/env python3
"""Finite falsification of the weighted analytic theorem; not a proof oracle."""
import cmath
import json
import math
import random


def check(points, weights):
    total = 0.0
    for c, w in zip(points, weights):
        factors = [abs(1-d.conjugate()*c) for d in points]
        value = 0 if 0 in factors else math.exp(2*sum(v*math.log(f) for v, f in zip(weights, factors)))
        total += w*value
    barycenter = sum(w*c for w, c in zip(weights, points))
    assert total <= 1-abs(barycenter)**2+2e-12, (points, weights, total)
    return total


def main():
    rng = random.Random(20260904)
    count = 0
    for m in range(1, 41):
        assert check([0j]*m, [1/m]*m) <= 1+2e-12
        for _ in range(40):
            points = [rng.random()**0.1*cmath.exp(2j*math.pi*rng.random()) for _ in range(m)]
            raw = [rng.randint(1, 100) for _ in range(m)]
            weights = [v/sum(raw) for v in raw]
            check(points, weights)
            check(points, [1/m]*m)
            count += 2
    print(json.dumps({"status": "pass", "instances": count,
                      "evidence_class": "deterministic_floating_point_falsification_only",
                      "universal_authority": "FreePointQuadraticAllDegrees.md"}))


if __name__ == "__main__":
    main()
