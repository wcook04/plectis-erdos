#!/usr/bin/env python3
"""Exact basis certificate for the paper's support<=7 moment obstruction.

This proves a finite-dimensional identity for arbitrary INTEGER coefficients,
not a bounded coefficient search. No Lean/native acceptance is asserted.
"""
from math import factorial, gcd
import json


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def weight(n, d):
    q, r = divmod(factorial(n), factorial(d) ** (n // d))
    require(r == 0, 'channel weight must be integral')
    return q


def row(n):
    return [factorial(n), weight(n, 2), weight(n, 3), weight(n, 4)]


def observables(vector):
    return [sum(c * row(n)[i] for n, c in vector.items()) for i in range(4)]


def verify_dual(coefficients):
    expected = [0, 0, 0, 0, 4140, 28980]
    require(len(coefficients) == 3, 'three dual coefficients required')
    for n, target in zip(range(2, 8), expected, strict=True):
        m, v2, _, v4 = row(n)
        require(sum(a*b for a,b in zip(coefficients, [m,v2,v4], strict=True)) == target,
                f'dual identity fails on basis vector e{n}')
    return expected


def main():
    dual = verify_dual([11, -46, 12])
    require(3011 * 11 - 8 * 4140 == 1, 'Bezout certificate fails')
    six = {2:246, 3:-112, 4:180, 5:-66, 6:11}
    eight = {2:1482, 3:-784, 5:-136, 6:83, 8:-1}
    require(observables(six) == [4140,0,0,0], 'six-index attainment fails')
    require(observables(eight) == [1380,0,0,0], 'eight-index attainment fails')
    require(gcd(*six.values()) == gcd(*eight.values()) == 1, 'witness content fails')
    require(1380 % 4140 != 0, 'wrong obstruction threshold')
    # Perturbing a dual coefficient must be rejected even under python -O.
    rejected = []
    for wrong in ([10,-46,12], [11,-45,12], [11,-46,13]):
        try:
            verify_dual(wrong)
        except ArithmeticError:
            rejected.append(wrong)
        else:
            raise ArithmeticError('corrupt dual certificate accepted')
    # Both equations are needed: either alone permits a positive moment below4140.
    only_two = {2:-6, 4:1}
    only_four = {2:-1, 4:2}
    require(observables(only_two) == [12,0,-8,-11], 'V2-only control changed')
    require(observables(only_four) == [46,11,6,0], 'V4-only control changed')
    # A single e2 cannot meet either vanishing premise.
    require(observables({2:1}) == [2,1,2,2], 'missing-premise control changed')
    require(observables({2:3,3:-1}) == [0,0,5,0], 'third-channel distinction lost')
    print(json.dumps({'schema':'erdos68_short_support_integer_certificate_v1',
      'evidence_class':'exact finite basis identity and explicit integer witnesses; not Lean',
      'basis_rows':{str(n):row(n) for n in range(2,9)},
      'dual_coefficients_M_V2_V4':[11,-46,12], 'dual_values_n2_through7':dual,
      'universal_linear_identity':'For any integer coefficients c2,...,c7: 11M-46V2+12V4=4140(c6+7c7).',
      'divisibility_witness':'If V2=V4=0, M=4140*(3011*(c6+7*c7)-8*M).',
      'consequences':['Under V2=V4=0, every moment with support in2..7 is a multiple of4140.',
       'With support in2..5, the same identity forces moment0.',
       'The exact moment ideal for supports in2..6 or2..7 is4140Z, even if V3=0 is also required: the explicit vector attains4140 and integer scaling attains every multiple.',
       'Moment1380 cannot be attained with maximum index<=7; the displayed vector attains it with maximum index8.'],
      'witness_support_le6':six,'witness_support_le6_observables':observables(six),
      'witness_maximum8':eight,'witness_maximum8_observables':observables(eight),
      'negative_controls':{'corrupt_duals_rejected':rejected,'V2_zero_alone_insufficient':observables(only_two),
        'V4_zero_alone_insufficient':observables(only_four),
        'third_channel_restricts_vectors':observables({2:3,3:-1})},
      'boundary':'Finite-dimensional paper claim, arbitrary signed integer coefficients supported at indices>=2. Does not establish the unrestricted moment ideal or any infinite-series irrationality claim.'},indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
