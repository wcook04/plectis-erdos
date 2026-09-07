<!-- Companion long-record migration for Erdős #269 round 6. -->
<!-- Destination label: long:two-channel-redistribution -->
<!-- Not frozen R. Source: erdos_269_research_memorandum_r6.md. -->

## 3. Weighted redistribution: an interval while two channels are fixed

### 3.1 A general construction principle

Let $t_0<t_1<\cdots$ be boundaries, with integer heights $H_n$ satisfying
$$
H_n=p_nH_{n-1},\qquad p_n\ge2,
$$
where $H_{-1}=1$. Let positive integer multiplicities $\mu_n$ give a convergent sum $\sum_n\mu_n/H_n$.

Choose a channel value $r\ge2$ and a sequence of indices
$$
n_0<n_1<n_2<\cdots,\qquad p_{n_j}=r.
$$
Set $A_j=H_{n_j}$ and assume
$$
2\le R_j:=A_j/A_{j-1}\le R_*\qquad(j\ge1).
$$
Let $M\ge1$ and suppose the chosen cells have capacity
$$
\mu_{n_j}\ge M(R_*-1)+1\qquad(j\ge1).
$$
All other boundaries will be called fixed boundaries.

**Theorem 3.1 (interval realisation with fixed boundary sums).** For each
$$
0\le\Delta\le\frac{(r-1)M}{A_0}
$$
there are positive integer multiplicities $\mu'_n$ such that
$$
\sum_{n\ge0}\frac{\mu'_n-\mu_n}{H_n}=\Delta,
$$
$$
|\mu'_n-\mu_n|\le M(R_*-1),\qquad
\mu'_n\equiv\mu_n\pmod M,
$$
and the multiplicities before $n_0$ are unchanged. Every complete block between any two fixed boundaries has exactly its original unweighted multiplicity sum.

*Proof.* Cantor expansion in the integer radices $R_j$ gives digits
$$
0\le a_j\le R_j-1,\qquad
\Delta=(r-1)M\sum_{j\ge1}\frac{a_j}{A_j}.
$$
For completeness, apply the greedy recurrence to $z_0=A_0\Delta/((r-1)M)\in[0,1)$:
$$
a_j=\lfloor R_jz_{j-1}\rfloor,\qquad z_j=R_jz_{j-1}-a_j.
$$
The remainder after $L$ steps is $(r-1)Mz_L/A_L$, which tends to zero. For the upper endpoint take $a_j=R_j-1$ and telescope. This representation step is classical Cantor expansion [C].

Define a potential on the boundary indices by
$$
v_{n_j}=Ma_j\quad(j\ge1),\qquad v_n=0\text{ otherwise},
$$
and put
$$
\epsilon_n=v_{n+1}-v_n,\qquad \mu'_n=\mu_n+\epsilon_n. \tag{3.1}
$$
The potential lies in $[0,M(R_*-1)]$. At an index where $v_n>0$, the capacity assumption gives $\mu'_n\ge\mu_n-v_n\ge1$. At any other index $\epsilon_n\ge0$, so positivity again holds. The bound and the congruence are immediate.

For fixed boundary indices $a,b$,
$$
\sum_{n=a}^{b-1}\epsilon_n=v_b-v_a=0.
$$
Thus every specified block total is preserved.

Weighted summation by parts gives
$$
\sum_{n\ge0}\frac{\epsilon_n}{H_n}
=\sum_{n\ge1}v_n\left(\frac1{H_{n-1}}-\frac1{H_n}\right)
=(r-1)\sum_{j\ge1}\frac{Ma_j}{A_j}=\Delta.
$$
The initial potential is zero; the terminal boundary term tends to zero because the potential is bounded and $H_n\ge2^{n+1}$. This also proves convergence of the perturbation series. $\square$

The potential is a local redistribution: it adds mass to the cell just before a selected boundary and removes the same mass from the cell just after it. Unweighted block totals telescope. Reciprocal weights distinguish the two cells, and the jump ratio supplies the factor $r-1$.

### 3.2 Actual positive capacities for the $\{2,3,5\}$ word

Now let $t_n$ enumerate all positive powers of $2,3,5$, beginning at $t_0=2$. Let $p_n$ be the prime of $t_n$ and put
$$
H_n=H(t_n),\qquad
\mu_n=\#\{2^i3^j5^k:t_n\le2^i3^j5^k<t_{n+1}\}.
$$
Every cell contains its left endpoint, so $\mu_n\ge1$. The actual repeated value is
$$
S=1+\sum_{n\ge0}\mu_n/H_n.
$$
We construct enough free cells in the five-power channel. All numerical constants below are exact; none is claimed to be optimal.

Put $\rho_0=27/25$. Call an exponent $e\ge1$ good if neither a two-power nor a three-power lies in $(5^e,\rho_0 5^e)$. The cell starting at $5^e$ then contains $[5^e,\rho_0 5^e)$.

**Lemma 3.2.** Every three consecutive positive exponents contain a good exponent.

*Proof.* For a prime $p=2,3$, being bad in the $p$-channel means that the phase $\{e\log_p5\}$ belongs to an open circular interval of length $\log_p\rho_0$. The three consecutive phases are a translate of those for exponents $0,1,2$.

For $p=2$, their normalised representatives are $1,5/4,25/16$. Their smallest cyclic multiplicative gap is $5/4>\rho_0$. For $p=3$, the representatives are $1,5/3,25/9$, whose smallest cyclic gap is $27/25=\rho_0$. An open interval of the stated length contains at most one of the three phases in each channel. At most two of the three exponents are bad, which proves the claim. Equality at an interval endpoint counts as good. $\square$

**Lemma 3.3.** For every $e\ge1$, the interval $[5^e,\rho_0 5^e)$ contains at least $1+\lfloor e/25\rfloor$ distinct $\{2,5\}$-smooth integers.

*Proof.* If $1\le k\le e$ and
$$
5^k<2^{\lceil k\log_2 5\rceil}<\rho_0 5^k,
$$
then
$$
x_k=2^{\lceil k\log_2 5\rceil}5^{e-k}
$$
lies in the stated interval. Different $k$ give distinct five-adic valuations. The endpoint $5^e$ is another point.

It remains to obtain one suitable $k$ in each block of 25 consecutive indices. The circular phases $\{j\log_2 5\}$, $0\le j<25$, have maximum multiplicative gap
$$
g=\frac{5^{22}}{2^{51}}=\frac{2384185791015625}{2251799813685248}<\frac{27}{25}. \tag{3.2}
$$
Here is a complete finite certificate. In increasing order the exponents of the representatives $5^j/2^{\lfloor j\log_2 5\rfloor}$ are
$$
\begin{gathered}
0,22,19,16,13,10,7,4,1,23,20,17,14,\
11,8,5,2,24,21,18,15,12,9,6,3.
\end{gathered}
$$
The cyclic consecutive ratios are 22 copies of $128/125$ and three copies of $5^{22}/2^{51}$. Both exceed one, their product is two, and the latter is the larger. These are integer-power comparisons; the accompanying checker verifies the list and its gaps exactly.

Every arc of logarithmic length $\log_2\rho_0$ therefore contains one of these 25 phases, and the same is true after translation. Apply this to the arc $(1-\log_2\rho_0,1)$. It supplies one suitable $k$ in every consecutive block of 25 indices. Endpoints cause no equality because $\rho_0$ has a prime factor three. The resulting count proves the lemma. $\square$

The good exponents $e_0<e_1<\cdots$ have gaps at most three. Consequently their heights satisfy
$$
2\le\frac{H(5^{e_j})}{H(5^{e_{j-1}})}
\le 2^7 3^5 5^3=3\,888\,000=:R_* . \tag{3.3}
$$
The ratio is an integer. The upper bound follows by increasing the argument by at most $5^3$: the exponent increases in the two- and three-channels are at most $7$ and $5$, respectively, and the five-channel increase is at most $3$.

### 3.3 Two exact block families still permit a rational total

**Theorem 3.4 (two-channel-preserving interval theorem).** Fix an arbitrary finite prefix of the actual multiplicities and an integer $M\ge1$. There exist $\delta>0$ and a constant
$$
C=3\,887\,999M
$$
such that every value in $[S,S+\delta]$ is realised by positive integer multiplicities $\mu'_n$ with the following properties: the actual height word is unchanged; the protected prefix is unchanged; $|\mu'_n-\mu_n|\le C$ and $\mu'_n\equiv\mu_n\pmod M$ for all $n$; every complete block between two powers of two has the actual total multiplicity; and every complete block between two powers of three has the actual total multiplicity.

*Proof.* Choose a good exponent $e_0\ge25C$ sufficiently far beyond the protected prefix, and enumerate every subsequent good exponent. Lemma 3.3 makes the actual multiplicity at each chosen five-power cell at least $C+1$. Lemma 3.2 and (3.3) give the bounded integer radices required by Theorem 3.1. Apply that theorem with free channel $r=5$. One may take
$$
\delta=\frac{4M}{H(5^{e_0})}.
$$
The potential vanishes at every two- and three-power boundary, so both complete block families are preserved. $\square$

Since a nondegenerate real interval contains rational numbers, all these invariants are compatible with a rational total. Choosing $M$ divisible by any prescribed finite list of moduli preserves that entire list of congruences simultaneously. The start can be moved arbitrarily far out. The theorem asserts existence and a real greedy construction; it supplies no favourable complexity bound for locating a desired rational target.

The modified multiplicities need not come from the original smooth integers. They retain the stated source statistics exactly, but the omitted third-channel distribution changes. The theorem is a countermodel to an information set, not a counterexample to the original irrationality question.

A further exact bound clarifies how close the scalar tails remain. At a dyadic cutoff, with the source normalisation $X_a=H(2^a)T_a/2$, the construction gives
$$
0\le X'_a-X_a\le C/2. \tag{3.4}
$$
Indeed, at its boundary the potential is zero. The fully height-normalised perturbation is a nonnegative sum of future potentials with weights
$$
H_k\left(\frac1{H_{j-1}}-\frac1{H_j}\right),\qquad j>k,
$$
and those weights sum to one. Divide by two for the source's normalisation. In particular, one may choose a dyadic rational total; its smooth denominator is eventually absorbed, so the modified dyadic tails become integral while staying within the bound (3.4). The ordinary boundary-clearing argument continues to apply because all modified coefficients are integers on the same height cells.

### 3.4 Adding the third block family restores identifiability

**Proposition 3.5 (existing rigidity, specialised).** Suppose an integer perturbation $\epsilon_n$ preserves the complete block sums between every pair of boundaries of the same channel, for all three channels. If the initial transitions $2\to3$ and $2\to5$ have zero perturbation, then $\epsilon_n=0$ for every $n$.

*Proof.* Let $V_N=\sum_{n<N}\epsilon_n$. Block preservation says that $V_N$ depends only on the channel of boundary $N$. Hence $\epsilon_n=C(p_{n+1})-C(p_n)$ for a function $C$ on three elements. The two zero transitions give $C(2)=C(3)=C(5)$, so every difference vanishes. This is exactly the mechanism already formalised in `ThreeChannelBlockRigidity.lean`. $\square$

For the actual boundary word the transitions occur at $2\to3$ and $4\to5$. Thus preserving the first three cell multiplicities supplies both anchors. The contrast is exact: two complete channel families plus any finite prefix admit an interval; all three families plus these anchors determine every coefficient.

This is identifiability of the source, not irrationality of its weighted total. It gives a precise boundary for arguments based only on complete block counts.

### 3.5 Why this does not contradict the round-5 thin-set theorem

The earlier thin-set theorem concerned canonical, one-sided digit corrections with
$$
0\le d'_a-d_a\le M(b_a-1)
$$
and forced zero corrections at certain radix-two positions. It correctly proves a null, dimension-deficient correction set for that class.

The present construction uses signed differences $v_{n+1}-v_n$. The resulting multiplicities remain strictly positive, but the changes can have either sign. That larger class supports the interval in Theorem 3.4, even with two complete block families fixed. Consequently the round-5 conclusion must not be paraphrased as a theorem that arbitrary shell-preserving bounded perturbations form a thin set.

The reusable principle is Theorem 3.1: prescribe a potential that vanishes on protected boundaries, then use positive capacity at free cells and integer radix expansion to prescribe the weighted change. Its antecedents are the corpus's bounded-perturbation construction for #251, the #269 fixed-modulus splice, and classical Cantor expansion. The two actual block families and the positivity capacity proof are the additional content here.
