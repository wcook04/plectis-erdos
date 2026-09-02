# A target-coupled Bellman state and its phase-monotonicity no-go

Status: exact identity and exact counterexample, 2026-08-21. The Bellman state
below is a sufficient barrier for the conjectured raw-carry domination at
\(1/465\). Its positivity is not proved. The counterexample rules out proving
that positivity by adding a period-20 gauge and claiming monotonicity.

Put

\[
 x=\frac1{465},\qquad w_n=\frac1{2^n-1},
\]

and let \(b_n\) be the real-greedy word for \(x\). Write

\[
 R_n=x-\sum_{d\leq n}b_dw_d,\qquad y_n=2^nR_n.
\]

Let

\[
 f_b(n)=\sum_{d\mid n}b_d
\]

and let \(r_{4,5}(n)\) count the positive solutions of \(4i+5j=n\).
For the target digits \(t_n\), define

\[
 K_n=2K_{n-1}+t_n-r_{4,5}(n),\qquad
 Q_n=2Q_{n-1}+t_n-f_b(n),
\]

with \(K_0=Q_0=0\). The product-source calculation gives
\[
 K_n=\left\lfloor\frac n{20}\right\rfloor.
\]
Set \(E_n=K_n-Q_n\).

## 1. The Bellman state

The scaled greedy residual satisfies

\[
 y_n=2y_{n-1}-\gamma_nb_n,\qquad
 \gamma_n=\frac{2^n}{2^n-1}.                       \tag{1}
\]

Subtracting the two carry recurrences gives
\[
 E_n=2E_{n-1}+f_b(n)-r_{4,5}(n).                  \tag{2}
\]

Define

\[
 \boxed{V_n=E_n+1-y_n.}                            \tag{3}
\]

Equations (1) and (2) give the target-coupled Bellman recurrence

\[
 \boxed{
 V_n=2V_{n-1}+f_b(n)-r_{4,5}(n)-1+\gamma_nb_n.}    \tag{4}
\]

This state combines the raw product carry, the Boolean divisor carry, and
the exact distance from the scaled real residual to the unit dyadic boundary.
This boundary is not being identified with the larger finite Mersenne-tail
fatal threshold. The state is unchanged by a positive refinement of the
cylinder source: \(K_n\) is defined by the raw product lattice, while \(Q_n\)
and \(y_n\) are defined by the actual greedy word. Internal ownership
relabelling of this fixed scalar orbit, including a one-use backward-bank
description, does not alter any term in (3).

The sign has a direct consequence. Since \(E_n\) is an integer and \(y_n\geq0\),

\[
 \boxed{V_n>0\quad\Longrightarrow\quad E_n\geq0.}   \tag{5}
\]

Indeed, (3) gives \(E_n>y_n-1\geq-1\). Thus all-depth positivity of \(V\)
would prove \(Q_n\leq\lfloor n/20\rfloor\), hence the desired tempered
quotient defect. No all-depth proof of \(V_n>0\) is supplied here.

## 2. A period-20 gauge cannot make the state monotone

The strongest immediate use of the product clock is to seek a function
\[
 \psi:\mathbb Z/20\mathbb Z\longrightarrow\mathbb R
\]
such that
\[
 W_n=V_n+\psi(n\bmod20)                              \tag{6}
\]
is nondecreasing along the actual greedy orbit. This would absorb the fixed
target phase while leaving the source and ownership gauges untouched.

It is false on the certified prefix. Exact greedy arithmetic gives

\[
 E_{29}=E_{49}=1
\]
and

\[
 y_{49}-y_{29}
=\frac{
953807871369647223468193707124973366086815577601024684638593619525548141202012531047831462970212526721951068324296618863421816832
}{
8336966995704035857707037772484759061900918891775387678832423542933207016075701883442425809392918909000258688433340823532531788805
}>0.                                                       \tag{7}
\]

Therefore

\[
 \boxed{V_{49}-V_{29}=y_{29}-y_{49}<0.}             \tag{8}
\]

The two indices have the same residue modulo \(20\), so every gauge in (6)
cancels:
\[
 W_{49}-W_{29}=V_{49}-V_{29}<0.
\]
No period-20 correction can make \(V\) nondecreasing, either step by step or
on every complete source block.

The selected ranks between \(29\) and \(49\) are
\[
 34,35,36,37,42,43,47,48.
\]
Thus (8) occurs after genuine divisor feedback and is not a target-digit-only
artefact.

## 3. Consequence

The state (3) is refinement invariant and its positivity would close the raw
carry bound, but the period clock does not supply a monotone Bellman proof.
Any proof using \(V\) must retain additional nonperiodic ancestry data that
controls the negative divisor-feedback blocks in (4). A phase correction,
front count, or source-clock gauge alone cannot do this.

This no-go does not disprove \(V_n>0\). Directed exact arithmetic has found no
sign failure, but a finite verification cannot establish the all-depth
claim.

## 4. Exact receipt

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_bellman_phase_nogo.py

The script constructs the greedy word with exact rational arithmetic, checks
(1)--(4), verifies \(K_n=\lfloor n/20\rfloor\), and proves the strict
counterexample (7)--(8) by integer comparison.
