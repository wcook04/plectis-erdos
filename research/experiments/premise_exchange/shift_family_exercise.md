<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Which dyadic shifts are enough?

An integer-digit dyadic tail obeys
$T_{N+1}=2T_N-g_{N+1}$ with $g_{N+1}\in\mathbb Z$.
Write $\|x\|$ for the distance from $x$ to the nearest integer. The
[cross-problem paper](../../../paper/synthesis/optimal-sparse-perturbations.pdf)
proves a criterion for which chosen shifts detect irrationality of $T_0$.
This exercise asks you to decide the criterion before reading its proof.

You may use the established Lean-checked implication

$$
T_0\notin\mathbb Q\ \Longrightarrow\
\forall h>0\ \forall N_0\ \exists N\ge N_0:
\|T_{N+h}-T_N\|\ge\frac13.
$$

## Make the decision

For each family below, decide whether the displayed condition is equivalent
to $T_0$ being irrational when the quantifier over $h>0$ is restricted to
$h\in H$:

$$
H_1=\{j!:j\ge1\},\qquad
H_2=\{2^j:j\ge0\},\qquad
H_3=\{1,2,\ldots,1000\}.
$$

Give a proof or a rational counterexample. A finite numerical run is not a
proof for all indices.

Then state a necessary and sufficient condition on a general family of
positive shifts $H$. Is its natural density or growth rate decisive? Keep
the quantifiers in the order $\forall h\in H\,\forall N_0\,\exists N\ge N_0$;
the witnessing $N$ may depend on $h$.

Finally, suppose you may also use the cited sharp bound
$\limsup_N\|2^N\xi\|\ge\tau$ for irrational $\xi$, where $\tau$ is the
Thue--Morse constant. Can you replace $1/3$ by $\tau$ in the cofinal
non-strict inequality? Explain what a limsup bound does and does not say.

## Change the way shifts are selected

Fix $0<c<\tau$ and a polynomial $P\in\mathbb Z[x]$ with positive leading
coefficient. Consider two families, retaining only positive values:

$$
H_P=\{P(n):n\ge0,\ P(n)>0\},\qquad
H_P^{\rm prime}=\{P(p):p\text{ prime},\ P(p)>0\}.
$$

Give a necessary and sufficient modular condition on $P$ for each family
to detect irrationality for every integer-digit dyadic recurrence. Explain
why the prime-argument condition requires more than a root modulo every
integer. You may use Dirichlet's theorem on primes in coprime residue
classes.

Test your answer on $P(x)=x^2$, $x^2+1$, $x-1$, and $x^2-1$.
Then consider
$Q(x)=(x^2-2)(x^2-3)(x^2-6)$. It has a root modulo every prime. Decide
whether $H_Q$ works by checking modulo $8$, and, if it fails, exhibit a
specific rational dyadic orbit that passes all its selected shifts. Explain
which parts of your answer are a proof and which are finite checks.

For a further positive example with no rational root, try
$F(x)=(x^2-13)(x^2-17)(x^2-221)$. Decide whether either of its two
shift families works. A proof may use quadratic residues, lifting at prime
powers, and the Chinese remainder theorem.

Return your decisions, the decisive argument or counterexample, sources
used, any agent assistance, and one sentence about what this establishes
for the original prime-gap problem. The
[contributor guide](../../../CONTRIBUTING.md) gives the public return route.

Open the [hints](shift_family_hints.md) only when needed, and the
[reviewer solution](shift_family_solution.md) after making your attempt.
This is a teaching and diagnostic task, not a held-out benchmark. An agent
attempt or rehearsal does not count as independent human first use.
