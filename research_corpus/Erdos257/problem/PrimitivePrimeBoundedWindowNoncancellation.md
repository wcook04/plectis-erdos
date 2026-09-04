# Primitive-prime channels cannot cancel in a bounded multiplier window

Let

\[
M_n=2^n-1,
\qquad
r=\sum_{n\in A}\frac1{M_n}\in\mathbf Q,
\]

where (A\subseteq\mathbf N_{\ge 2}) is infinite.  Write (D=\operatorname{den}(r)), and, for a real cutoff (X), put

\[
S_X=\sum_{\substack{n\in A\\ n\le X}}\frac1{M_n},
\qquad
\tau_X=r-S_X.
\]

The single-channel tail law in
[`DensePadicCancellationAttack.md`](DensePadicCancellationAttack.md)
allows arbitrary cancellation inside the highest (p)-power layer.  The point of this note is that such cancellation is impossible when all available multipliers lie in a fixed bounded window.  This gives a simultaneous lower bound on the reduced denominator of every hypothetical rational tail.

## 1. The bounded-window lemma

Fix (a\in A), and let (p) be a primitive prime divisor of (M_a).  Thus

\[
\operatorname{ord}_p(2)=a,
\qquad
\mu=v_p(M_a)\ge 1.
\]

For an integer (T\ge 1), define the selected multipliers visible by the cutoff (Ta) by

\[
K_{a,T}=\{k\in\{1,\ldots,T\}:ak\in A\}.
\]

This set is nonempty because (1\in K_{a,T}).

### Lemma 1 (positive-height obstruction)

If (p>T), then

\[
C_{a,T}:=\sum_{k\in K_{a,T}}k^{-1}\pmod p
\]

is nonzero whenever (p>T^T).

### Proof

Put (m=|K_{a,T}|) and (Q=\prod_{k\in K_{a,T}}k).  Since every (k\le T<p), multiplication by (Q) is legitimate modulo (p), and

\[
Q C_{a,T}\equiv
H(K_{a,T}):=\sum_{k\in K_{a,T}}\frac Qk
\pmod p.
\]

The integer (H(K_{a,T})) is strictly positive.  Moreover,

\[
H(K_{a,T})
\le mT^{m-1}
\le T^T.
\]

Thus (0<H(K_{a,T})<p), so it cannot vanish modulo (p).  Since (Q) is a (p)-adic unit, neither can (C_{a,T}).  ∎

The estimate is deliberately crude, but it is uniform over **every** support pattern inside the window.  No density assumption is used.

### Corollary 2 (primitive-order form)

If (a>T^T), then (C_{a,T}\ne0) for every primitive prime (p\mid M_a).

### Proof

Primitive order gives (a\mid p-1), hence (p\ge a+1>T^T\ge T).  Lemma 1 applies.  ∎

Equivalently, define

\[
b(a)=\min\{T\ge1:T^T\ge a+1\}.
\]

No primitive channel belonging to (a) can cancel in a finite prefix before multiplier scale (b(a)).  Since

\[
b(a)\log b(a)\ge\log(a+1),
\]

this scale is asymptotically at least ((1-o(1))\log a/\log\log a).  This is a delay theorem, not a claim that cancellation occurs at that scale.

## 2. Exact rational-tail consequence

Assume now that (p\nmid D).  If (a>T^T), then

\[
v_p(\tau_{Ta})=-\mu.
\tag{1}
\]

Indeed, (p>T), so every visible selected multiple (ak) has (v_p(k)=0).  LTE gives

\[
v_p(M_{ak})=v_p(M_a)+v_p(k)=\mu.
\]

After multiplication by (p^\mu), the (p)-adic leading coefficient of the terms with (a\mid n) is a fixed unit times (C_{a,T}); all terms with (a\nmid n) are (p)-integral.  Corollary 2 therefore gives

\[
v_p(S_{Ta})=-\mu.
\]

On the other hand, (p\nmid D) gives (v_p(r)\ge0).  The ultrametric inequality is strict when the two valuations differ, hence

\[
v_p(r-S_{Ta})=v_p(S_{Ta})=-\mu,
\]

which proves (1).  Notice that this uses only the finite prefix (S_{Ta}); it does not exchange a real infinite limit with a (p)-adic one.

Thus a hypothetical rational value does **not** force a later selected multiple to cancel the channel.  Instead, its rational tail must retain the full primitive prime power in its reduced denominator.

## 3. Simultaneous channels at one cutoff

For (a\ne6), let

\[
P_a=\prod_{\substack{p\mid M_a\\ \operatorname{ord}_p(2)=a}}
p^{v_p(M_a)}
\]

be the primitive prime-power part of (M_a).  Bang--Zsigmondy gives (P_a>1).  A fixed prime can be primitive for only one exponent, so the integers (P_a) are pairwise coprime as (a) varies.

Fix (T\ge1) and a cutoff (X), and define

\[
F_{X,T}=
\left\{
a\in A:
\frac{X}{T+1}<a\le X,
\quad a>T^T,
\quad a\ne6,
\quad \gcd(P_a,D)=1
\right\}.
\]

For (a\in F_{X,T}), every selected multiple (ak\le X) has (k\le T).  The preceding argument therefore applies at the common cutoff (X), simultaneously for every primitive prime power dividing (P_a).

### Theorem 3 (simultaneous primitive denominator bound)

If (	au_X\ne0), then

\[
\prod_{a\in F_{X,T}}P_a
\;\bigm|\;
\operatorname{den}(\tau_X).
\tag{2}
\]

In particular,

\[
\operatorname{den}(\tau_X)
\ge
\left(\frac{X}{T+1}\right)^{|F_{X,T}|}.
\tag{3}
\]

### Proof

For each (a\in F_{X,T}) and each primitive (p\mid M_a), Corollary 2 gives a nonzero leading coefficient in the finite prefix.  Since (p\nmid D), equation (1), with (X) in place of (Ta), gives

\[
v_p(\tau_X)=-v_p(M_a).
\]

Distinct exponents have disjoint primitive-prime sets, so these exact divisibilities multiply, proving (2).  Finally, each nontrivial (P_a) contains a primitive prime (p\equiv1\pmod a), and hence (P_a\ge p\ge a+1>X/(T+1)).  This proves (3).  ∎

Only finitely many exponents can fail the condition (gcd(P_a,D)=1): every prime divisor of the fixed integer (D) has at most one multiplicative order.  Consequently, if (A) has natural density (delta>0), then for each fixed (T),

\[
|F_{X,T}|=
\frac{\delta T}{T+1}X+o(X),
\]

and (3) yields

\[
\log\operatorname{den}(\tau_X)
\ge
\left(\frac{\delta T}{T+1}+o(1)\right)X\log X.
\tag{4}
\]

This is an unconditional consequence of the *hypothesis* that the sum is rational; it goes beyond reciprocal-summability criteria and applies precisely in the dense regime where those criteria are silent.

## 4. Adversarial support tests

The theorem survives the two most hostile support geometries.

1. **Prime support.**  If both (a) and every selected exponent are prime, no multiple (ak) with (k>1) is selected.  Hence (K_{a,T}=\{1\}) and (C_{a,T}=1) at every cutoff.  Every primitive channel persists forever in the rational tails.

2. **Maximally dense or highly divisible support.**  If (A=\mathbf N_{\ge2}), then (K_{a,T}=\{1,\ldots,T\}).  Lemma 1 still forbids cancellation while (T^T<p), even though every possible bounded multiplier is present.  At much larger scales cancellation can occur; for example, a complete set of nonzero residues modulo (p) has reciprocal sum (0\pmod p).  Thus the bounded-window result is a genuine delay law, not permanent noncancellation.

The same reasoning applies to a support concentrated on highly composite exponents: adding every possible selected multiple up to (T) cannot defeat the positive-height obstruction.

## 5. Why this still does not prove irrationality

For a finite prefix,

\[
\operatorname{den}(S_X)
\mid
\prod_{\substack{n\in A\\n\le X}}M_n,
\]

so

\[
\operatorname{den}(\tau_X)
\mid
D\prod_{\substack{n\in A\\n\le X}}M_n.
\tag{5}
\]

Every factor forced by (2) already occurs in the denominator belonging to its anchor term (1/M_a).  Hence (2) is compatible with (5).  Real convergence, including the estimate (	au_X\ll2^{-X}), supplies no upper bound on the reduced denominator capable of contradicting (3).

The exact conclusion is therefore:

- bounded multiplicative branching cannot cancel a fresh primitive channel;
- a rational sum would force many primitive prime powers to persist simultaneously in each tail denominator;
- neither dense support, prime support, nor highly composite support turns that persistence into a contradiction without an independent denominator bound or a genuine (p)-integrality boundary for the tail.

This isolates the remaining obstruction more sharply than the one-channel residue law: the missing ingredient is not additional local branching analysis, because even maximal bounded branching provably fails.  The missing ingredient must prevent the rational tail from indefinitely inheriting the primitive denominator mass of the finite prefix.
