# Erdős 1041: the upper-`w` block on the upper-`s` slab

The stationary surplus is strictly positive on

```text
0<=t<=1, 0<=r<=1/8, 3/8<=s<=1/2, 1/2<=w<=31/32.
```

The checker covers this box by three adjoining dyadic slabs:

```text
[1/2,3/4]     : 131072/131072 coarse cells green,
[3/4,15/16]   : 131072/131072 coarse cells green,
[15/16,31/32] :  65536/65536 coarse cells green.
```

Their weakest lower endpoints and deterministic digests are

```text
0x1.c4e9892535f19p-3 = 0.2211485590439615,
be2997d786a188cd080cc90bc31ad7225297b04c0651c7fffb1d9b796228b44b;

0x1.d91a49a2b48bcp+0 = 1.8480573675374634,
da247029b331ad2211f0d89d2af3dc167bdd8abca663eaae7796034475389fef;

0x1.b29da30e4c7c5p+3 = 13.581742790152825,
bfd12f4150306d25cc2aba71f30e69924c72aecd09920c236fd7fe686da74bca.
```

Together with `ThreeExteriorStationaryUpperSFiniteBlock.md` and the analytic
tail `ThreeExteriorStationaryUpperSBoundaryTail.md`, this proves positivity on
the complete half-open prism

```text
0<=t<=1, 0<=r<=1/8, 3/8<=s<=1/2, 1/4<=w<1.
```

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_upper_s_upper_w_block.py
```

This is an exhaustive interval theorem, not sampling. The composition closes
only the stated upper-`s` prism; it does not cover the ordered-cone complement,
prove GP3, or prove Erdős 1041.
