<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Reviewer solution: selected dyadic shifts

At every threshold $0<c<\tau$, a family $H$ of positive shifts detects
irrationality for every integer-digit dyadic recurrence exactly when it
contains a multiple of every positive integer. The full proof is an ordinary
argument in the [synthesis paper](../../../paper/synthesis/optimal-sparse-perturbations.pdf);
the sharp irrational bound is a cited theorem of Dubickas in the form stated
by Akiyama and Kaneko. The original $1/3$ implication is Lean checked.

For $H_1$, take a rational $T_0=p/q$ and write $q=2^sr$ with $r$ odd. Some
$d>0$ satisfies $2^d\equiv1\pmod r$, and $d!$ is a multiple of $d$.
Therefore $\|T_{N+d!}-T_N\|=0$ for all $N\ge s$. The irrational direction
follows by restricting the given theorem to factorial shifts.

For $H_2$, the rational orbit $T_N=\{2^N/7\}$ is a counterexample. Every
power-of-two shift is $1$ or $2$ modulo $3$, and its difference distances
cycle through $1/7$, $2/7$, and $3/7$. The value $3/7$ occurs arbitrarily
late for each tested shift, exceeding both $1/3$ and $\tau$.

For $H_3$, choose $d>1000$ and set $L=3d$, $q=2^L-1$, and
$T_N=\{2^N/q\}$. For each tested shift $h$, the proof in the synthesis
paper finds a distance at least $7/16$ once every $L$ indices. Thus even a
large finite family can accept a rational orbit.

The exact family condition is
$\forall d>0\,\exists h\in H:\ d\mid h$. Density is not decisive:
factorial shifts have density zero and work, while removing the multiples
of a large $d$ leaves density $1-1/d$ and fails.

At the endpoint $c=\tau$, the upgrade fails. The Thue--Morse orbit has
$\limsup_N\|2^N\tau\|=\tau$ but
$\|2^N\tau\|<\tau$ at every positive index. A limsup need not be attained
cofinally. The existing
[closure record](README.md#how-the-question-closed) gives the ordinary
endpoint argument and separates it from the cited lower bound.

The result concerns a criterion for arbitrary dyadic recurrences. It does
not establish irrationality of the actual prime-gap series in Erdős #251.

## Polynomial values and prime arguments

For $P\in\mathbb Z[x]$ with positive leading coefficient, $H_P$ works
exactly when $P$ has a root modulo every positive integer $d$. A root $r$
modulo $d$ gives positive multiples $P(r+kd)$ for all large $k$; the
converse follows immediately from divisor coverage.

For $H_P^{\rm prime}$, the exact condition is a **unit root modulo every
$d$**: $P(r)\equiv0\pmod d$ and $\gcd(r,d)=1$. Dirichlet gives
arbitrarily large primes $p\equiv r\pmod d$, proving sufficiency. If
there is no unit root for a particular $d$, every prime $p$ with
$d\mid P(p)$ divides $d$. There are only finitely many such arguments,
so $H_P^{\rm prime}\cap d\mathbb Z$ is bounded. Coverage of all multiples
$kd$ would make this set unbounded, proving necessity. Prime arguments
and roots modulo prime moduli are different restrictions.

The integer-argument family for $x^2$ works; $x^2+1$ fails modulo $3$.
The prime-argument family for $x^2$ fails modulo $6$, since its sole root
there is $0$, a nonunit. For $x-1$ and $x^2-1$, the unit residue $1$
is a root modulo every $d$, so both prime-argument families work.

For $Q(x)=(x^2-2)(x^2-3)(x^2-6)$, one of $2$, $3$, or $6$ is a square
modulo each odd prime not dividing $6$: if the first two are nonsquares,
their product is a square. The cases $2$ and $3$ are direct. This checks
prime moduli only. Squares modulo $8$ show $Q(n)\equiv4$ for even $n$
and $Q(n)\equiv6$ for odd $n$; hence $8$ divides no selected shift.
The prime-argument subfamily also fails, since it is contained in $H_Q$.
Lê's [arXiv v1 introduction, p. 1](https://arxiv.org/pdf/0910.1880v1)
lists this $Q$ as intersective; the modulo-$8$ table corrects that
particular printed example, not the general local-root criterion there.
For the rational orbit $T_N=\{2^N/255\}$, a shift $h\equiv4\pmod8$
has distance $120/255$ at every $N\equiv3\pmod8$, while a shift
$h\equiv6\pmod8$ has distance $126/255$ at every
$N\equiv1\pmod8$. Both exceed $7/16>\tau$. Thus this rational orbit
passes every $Q$-selected test at $0<c<\tau$. The modular and orbit
calculations are proofs for all arguments and indices, not inferences
from a finite numerical run. The polynomial extension is an ordinary
proof in the synthesis paper, not a new Lean theorem.
The [exact residue control](polynomial_shift_control.py) reproduces the
finite tables used in the orbit calculation.

For terminology and context, see Lê's
[intersective-polynomial paper](https://arxiv.org/abs/0910.1880v1) and Rice's
[prime-argument paper, §1.2](https://arxiv.org/abs/1111.6559). The criterion
above is proved in the synthesis paper from its selected-shift theorem;
these references are not substituted for that proof.

The polynomial $F(x)=(x^2-13)(x^2-17)(x^2-221)$ has no rational root,
yet has a unit root modulo every positive integer. At every odd prime
other than $13$ and $17$, one of $13$, $17$, or their product $221$ is
a nonzero square; its root lifts to all prime powers. At $13$, use
$x^2-17$ and $x=2$ modulo $13$; at $17$, use $x^2-13$ and $x=8$
modulo $17$. At powers of $2$, the unit $17\equiv1\pmod8$ has a
square root. The Chinese remainder theorem combines these unit roots.
Consequently both $H_F$ and $H_F^{\rm prime}$ work. Mishra's
[paper](https://arxiv.org/abs/2102.08379) lists the intersective
example; the unit-root check above makes the stronger prime-argument
conclusion explicit. Neither conclusion depends on a finite modulus scan.

## Review a returned attempt

Check the verdict and its argument separately. A complete return distinguishes
all moduli from prime moduli, identifies the unit-root condition for prime
arguments, and either proves or explicitly limits each computational check.
It should credit the cited sharp bound and the literature's $F$ example,
state where agent help entered, and keep the result separate from the
original prime-gap problem. If the verdict is correct but a source or
calculation is missing, ask for that evidence rather than treating the
omitted step as proved. Record orientation, changed-case decision and
reviewability separately; this rubric does not itself measure independent
usefulness.

This exercise and its solution were developed in an AI-assisted research
continuation under Will Cook's direction; historical novelty and independent
expert review are not asserted.
