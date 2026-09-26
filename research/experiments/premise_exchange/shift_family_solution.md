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
This exercise and its solution were developed in an AI-assisted research
continuation under Will Cook's direction; historical novelty and independent
expert review are not asserted.
