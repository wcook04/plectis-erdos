<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Hints for the dyadic shift exercise

1. Iterate the recurrence and subtract two states. Show that
   $\|T_{N+h}-T_N\|=\|2^N(2^h-1)T_0\|$.
2. A rational denominator has a power-of-two part and an odd part. Powers
   of two are periodic modulo the odd part.
3. For a counterexample, examine the orbit starting at $T_0=1/7$.
4. For polynomial values, lift a root modulo $d$ to arbitrarily large
   arguments in the same residue class. For prime arguments, ask when
   Dirichlet supplies primes in that class.
5. If all roots modulo $d$ are nonunits, how many prime arguments can
   realize one? Compare this with coverage of every multiple of $d$.
6. Squares modulo $8$ are $0$, $1$, or $4$. For the $Q$ example, try
   $T_N=\{2^N/255\}$ and use $2^8\equiv1\pmod{255}$.
7. For $F$, $221=13\cdot17$. At an odd prime other than $13,17$,
   two nonsquares multiply to a square. Handle $13$, $17$, and $2$
   separately, checking that the chosen roots are units.

Record which hints you used in your return. The
[reviewer solution](shift_family_solution.md) is a separate reveal.
