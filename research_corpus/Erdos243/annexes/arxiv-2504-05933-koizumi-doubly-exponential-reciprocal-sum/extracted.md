[^1]

# Introduction {#introduction .unnumbered}

The asymptotic behavior of a sequence of positive integers is related to the irrationality of its reciprocal sum. It is a folklore result that if a sequence satisfies $\lim_{n\to\infty} a_n^{2^{-n}} = \infty$, then its reciprocal sum is irrational. Therefore, the largest possible asymptotic growth of a sequence for which the rationality of the reciprocal sum can be expected is $C^{2^n}$ for some constant $C>1$. A well-known example of such sequence is the (shifted) *Sylvester sequence* [@OEIS A129871], which is defined by $$s_1=2,\quad s_{n+1}=s_n^2-s_n+1.$$ It is straightforward to see that the sum of their reciprocals is $1$: $$1=\sum_{n=1}^\infty\dfrac{1}{s_n}=\dfrac{1}{2}+\dfrac{1}{3}+\dfrac{1}{7}+\dfrac{1}{43}+\dfrac{1}{1807}+\cdots.$$ Also, it is known that there is a constant $c=1.2640847\cdots$ such that $s_n\approx c^{2^n}$ (see [@Concrete p. 109]). On the other hand, the *Millin series* [@Millin] provides an example of a doubly exponential sequence with an irrational reciprocal sum: $$\dfrac{5-\sqrt{5}}{2}=\sum_{n=1}^\infty \dfrac{1}{F_{2^{n}}}=\dfrac{1}{1}+\dfrac{1}{3}+\dfrac{1}{21}+\dfrac{1}{987}+\dfrac{1}{2178309}+\cdots.$$

The purpose of this paper is to point out that these doubly exponential sequences are often *almost uniquely* determined by their reciprocal sum. Our main result is the following:

::: {#thm:main .theorem}
**Theorem 1**. *Let $\beta\geq 0$ be a real number, and $(a_n)_{n=1}^\infty$ be a sequence of positive integers satisfying $$\left|\dfrac{a_n^2}{a_{n+1}}-\beta\right|\leq\dfrac{1}{3},\quad \sum_{n=1}^\infty\dfrac{1}{a_n}=r<\infty.$$ Then, for every $n$ satisfying $a_n\geq 8(\beta+(1/3))^2$, we have $$a_n = \left\lfloor\left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}+\beta\right\rceil,$$ where $\lfloor x\rceil=\lfloor x+(1/2)\rfloor$ is the integer closest to $x$. Moreover, if $\lim_{n\to \infty}a_n^2/a_{n+1}=\beta$, then we have $$\lim_{n\to \infty}\left|\left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}+\beta-a_n\right|=0.$$*
:::

This yields the following characterizations of the Sylvester sequence and the Millin series:

::: {#cor:Sylvester .corollary}
**Corollary 2**. *Let $(a_n)_{n=1}^\infty$ be a sequence of positive integers satisfying $$\dfrac{2}{3}\leq \dfrac{a_n^2}{a_{n+1}}\leq \dfrac{4}{3},\quad \sum_{n=1}^\infty\dfrac{1}{a_n} = 1.$$ Then, we have $a_n=s_n$, where $(s_n)_{n=1}^\infty$ is the Sylvester sequence.*
:::

::: {#cor:Millin .corollary}
**Corollary 3**. *Let $(a_n)_{n=1}^\infty$ be a sequence of positive integers satisfying $$\dfrac{a_n^2}{a_{n+1}}\leq \dfrac{2}{3},\quad \sum_{n=1}^\infty\dfrac{1}{a_n} = \dfrac{5-\sqrt{5}}{2}.$$ Then, we have $a_n=F_{2^n}$, where $(F_n)_{n=1}^\infty$ is the Fibonacci sequence.*
:::

Note that [2](#cor:Sylvester){reference-type="ref+Label" reference="cor:Sylvester"} resembles Badea's characterization of the Sylvester-like sequences [@Badea]: if $(a_n)_{n=1}^\infty$ is a sequence of positive integers satisfying $a_{n+1}\geq a_n^2-a_n+1$ for $n\gg 0$ and $\sum_{n=1}^\infty(1/a_n)\in \mathbb{Q}$, then the equality $a_{n+1}= a_n^2-a_n+1$ holds for $n\gg 0$.

[1](#thm:main){reference-type="ref+Label" reference="thm:main"} has an immediate application to the study of *irrationality sequences* defined by Erdős-Straus [@Erdos75] and Erdős-Graham [@Erdos_Graham_80]. Following the terminology introduced by Kovač-Tao [@Kovac_Tao], we say that an increasing sequence[^2] of positive integers $$a_1\leq a_2\leq a_3\leq \cdots$$ is a *Type 2 irrationality sequence* if for every sequence of positive integers $(b_n)_{n=1}^\infty$ such that $a_n\approx b_n$, we have $\sum_{n=1}^\infty(1/b_n)\not\in\mathbb{Q}$. For example, any sequence with $a_n^{2^{-n}}\to \infty$ is a Type 2 irrationality sequence by the folklore result mentioned above. On the other hand, Kovač-Tao [@Kovac_Tao] proved that any sequence satisfying $a_n^2/a_{n+1}\to \infty$ (e.g. $\lfloor 2^{(2-\varepsilon)^n}\rfloor$ for $0<\varepsilon<1$) cannot be a Type 2 irrationality sequence. An unsolved problem of Erdős-Graham [@Erdos_Graham_80 p. 63] asks whether $2^{2^n}$ is a Type 2 irrationality sequence; it is also listed in the website *Erdős Problems* [@EP Problem #263]. As a consequence of [1](#thm:main){reference-type="ref+Label" reference="thm:main"}, we get the following result:

::: {#type2_countable .theorem}
**Theorem 4**. *Let $\mathcal{I}$ denote the following subset of $(1,\infty)$: $$\mathcal{I}:=\{\alpha\in (1,\infty)\mid \lfloor\alpha^{2^n}\rfloor\text{ is a Type 2 irrationality sequence}\}.$$ Then, its complement $(1,\infty)\setminus \mathcal{I}$ is countable.*
:::

In the latter half of the paper, we study the following unsolved problem of Erdős-Graham:

::: {#ques:erdos .question}
**Question 5** (Erdős-Graham [@Erdos_Graham_80 p. 64]). *Let $(a_n)_{n=1}^\infty$ be a sequence of positive integers satisfying $$\lim_{n\to \infty}\dfrac{a_n^2}{a_{n+1}}=1\quad\text{and}\quad
        \sum_{n=1}^\infty \dfrac{1}{a_n}\in \mathbb{Q}.$$ Is it true that $a_{n+1}=a_n^2-a_n+1$ holds for $n\gg 0$?*
:::

In order to state our result, we introduce the concept of *pseudo-greedy expansion*, which is a variant of the greedy expansion of a positive real number into unit fractions. For a positive real number $r$, its pseudo-greedy expansion is the sequence of positive integers $(a_n)_{n=1}^\infty$ defined by $$a_n=\left\lfloor\left( r-\sum_{k=1}^{n-1}\dfrac{1}{a_k} \right)^{-1}+1\right\rceil,$$ where $\lfloor x\rceil=\lfloor x+(1/2)\rfloor$ is the integer closest to $x$. We can show that $r=\sum_{n=1}^\infty(1/a_n)$, so it indeed gives an expansion of $r$ into unit fractions. We define the *gap sequence* of this expansion by $$\varepsilon_n=\left( r-\sum_{k=1}^{n-1}\dfrac{1}{a_k} \right)^{-1}+1-a_n.$$ Then, we prove that [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} is equivalent to the following conjecture:

::: {#conj .conjecture}
**Conjecture 6**. *Let $r$ be a positive rational number and $(\varepsilon_n)_{n=1}^\infty$ be the gap sequence of the pseudo-greedy expansion of $r$. If $\lim_{n\to \infty}\varepsilon_n= 0$, then $\varepsilon_n=0$ holds for $n\gg 0$.*
:::

We expect that [6](#conj){reference-type="ref+Label" reference="conj"} is true even without assuming $\lim_{n\to \infty}\varepsilon_n=0$. We confirmed by a computer that [6](#conj){reference-type="ref+Label" reference="conj"} holds for $r=p/q$ with $0<p\leq q\leq 10^5$. In [17](#rem:heuristic){reference-type="ref+Label" reference="rem:heuristic"}, we provide a heuristic argument showing that [6](#conj){reference-type="ref+Label" reference="conj"} is likely to be correct.

## Notation {#notation .unnumbered}

For two sequences of real numbers $(x_n)_{n=1}^\infty$, $(y_n)_{n=1}^\infty$ with $y_n>0$, we write:

- $x_n=O(y_n)$ if $\limsup_{n\to \infty}(|x_n|/y_n)<\infty$;

- $x_n=o(y_n)$ if $\lim_{n\to \infty}(x_n/y_n)=0$;

- $x_n\approx y_n$ if $\lim_{n\to \infty}(x_n/y_n)=1$.

We say that a proposition $P(n)$ is true for $n\gg 0$ if there exists a positive integer $n_0$ such that $P(n)$ is true for all $n\geq n_0$.

## Acknowledgments {#acknowledgments .unnumbered}

The author would like to thank Takahiro Ueoro for carefully reading the paper and for informing him about the problem of odd greedy expansion. The author also thanks Vjekoslav Kovač for providing comments on an earlier version of this paper.

# Proof of the main results

The idea of the proof of [1](#thm:main){reference-type="ref+Label" reference="thm:main"} is very simple. Let $(a_n)_{n=1}^\infty$ be a sequence of positive integers such that $a_n^2/a_{n+1}$ is sufficiently close to $\beta\geq 0$ and $a_n$ is sufficiently large. Then, we have $$\begin{align}
\label{eq:remainder}
r-\sum_{k=1}^{n-1}\dfrac{1}{a_k} = \dfrac{1}{a_n}+\dfrac{1}{a_{n+1}}+\cdots =\dfrac{1}{a_n}\left(1+\sum_{k=1}^\infty\dfrac{a_n}{a_{n+k}}\right).
\end{align}$$ Using that the sum in the right hand side is very small, we get $$\left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}\fallingdotseq
a_n\left(1-\sum_{k=1}^\infty\dfrac{a_n}{a_{n+k}}\right)
=a_n-\dfrac{a_n^2}{a_{n+1}}-\sum_{k=2}^\infty\dfrac{a_n^2}{a_{n+k}}.$$ Since the last sum is also very small and $a_n^2/a_{n+1}$ is close to $\beta$, it follows that the left hand side is close to $a_n-\beta$, which is what we want. We will make this precise:

::: proof
*Proof of [1](#thm:main){reference-type="ref+Label" reference="thm:main"}.* Let $\beta\geq 0$ be a real number, and $(a_n)_{n=1}^\infty$ be a sequence of positive integers such that $$\left|\dfrac{a_n^2}{a_{n+1}}-\beta\right|\leq\dfrac{1}{3},\quad \sum_{n=1}^\infty\dfrac{1}{a_n}=r<\infty.$$ We write $\beta_+ = \beta + (1/3)$. Fix a positive integer $n$ satisfying $a_n\geq 8\beta_+^2$. Combining with $a_n\geq 1$, we obtain $a_n^2\geq 8\beta_+^2$ and hence $a_n\geq 2\sqrt{2}\beta_+$. In other words, we have $$\dfrac{\beta_+^2}{a_n}\leq \dfrac{1}{8},\quad \dfrac{\beta_+}{a_n}\leq\dfrac{1}{2\sqrt{2}}.$$ Our assumption shows that $a_{k+1}\geq a_k^2/\beta_+$ holds for all $k>0$. Using this inequality iteratively, we obtain $$a_{n+k}\geq \dfrac{a_{n+k-1}^2}{\beta_+}\geq\dfrac{a_{n+k-2}^4}{\beta_+^3}\geq\cdots\geq\dfrac{a_n^{2^k}}{\beta_+^{2^k-1}}=\beta_+\left(\dfrac{a_n}{\beta_+}\right)^{2^k}$$ for all $k\geq 0$. Therefore, we have $$\begin{align}
\label{eq:estimate_A}
        A:=\sum_{k=1}^\infty\dfrac{a_n}{a_{n+k}}&{}\leq\dfrac{a_n}{\beta_+}\sum_{k=1}^\infty \left(\dfrac{\beta_+}{a_n}\right)^{2^k}\leq\dfrac{a_n}{\beta_+}\sum_{k=1}^\infty\left(\dfrac{\beta_+}{a_n}\right)^{2k}\\
        &{}=\dfrac{\beta_+}{a_n}\cdot\dfrac{1}{1-(\beta_+/a_n)^2}\leq\dfrac{\beta_+}{a_n}\cdot\dfrac{1}{1-(1/8)}=\dfrac{8}{7}\cdot\dfrac{\beta_+}{a_n}.\notag
\end{align}$$ Similarly, we have $$\begin{align}
\label{eq:estimate_B}
        B:=\sum_{k=2}^\infty\dfrac{a_n^2}{a_{n+k}}&{}\leq\dfrac{a_n^2}{\beta_+}\sum_{k=2}^\infty\left(\dfrac{\beta_+}{a_n}\right)^{2^k}
        \leq\dfrac{a_n^2}{\beta_+}\sum_{k=1}^\infty\left(\dfrac{\beta_+}{a_n}\right)^{4k}\\
        &{}= \dfrac{\beta_+^2}{a_n}\cdot\dfrac{\beta_+}{a_n}\cdot\dfrac{1}{1-(\beta_+/a_n)^4}\leq \dfrac{2\sqrt{2}}{63}.\notag
\end{align}$$ Now we use [\[eq:remainder\]](#eq:remainder){reference-type="eqref" reference="eq:remainder"}. Taking the reciprocal, we get $$\begin{align}
\label{eq:reciprocal_expansion}
    \left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}
    &{}=\dfrac{a_n}{1+A}=a_n-a_nA+\dfrac{a_nA^2}{1+A}\\
    &{}=a_n-\dfrac{a_n^2}{a_{n+1}}-B+\dfrac{a_nA^2}{1+A}.\notag
\end{align}$$ By [\[eq:estimate_B\]](#eq:estimate_B){reference-type="eqref" reference="eq:estimate_B"}, we have $B<(1/6)$. On the other hand, by [\[eq:estimate_A\]](#eq:estimate_A){reference-type="eqref" reference="eq:estimate_A"}, we have $$\dfrac{a_nA^2}{1+A}\leq a_nA^2\leq \dfrac{64}{49}\cdot\dfrac{\beta_+^2}{a_n}\leq \dfrac{8}{49}<\dfrac{1}{6}.$$ Therefore, we have $$\left|\left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}+\dfrac{a_n^2}{a_{n+1}}-a_n\right|=\left|-B+\dfrac{a_nA^2}{1+A}\right|<\dfrac{1}{6}.$$ Finally, by our assumption that $|(a_n^2/a_{n+1})-\beta|\leq (1/3)$, we obtain $$\left|\left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}+\beta-a_n\right|<\dfrac{1}{6}+\dfrac{1}{3}=\dfrac{1}{2}.$$ This shows that $a_n$ is the integer closest to $(r-\sum_{k=1}^{n-1}(1/a_k))^{-1}+\beta$.

Suppose, moreover, that $\lim_{n\to \infty}(a_n^2/a_{n+1})=\beta$. The inequalities [\[eq:estimate_A\]](#eq:estimate_A){reference-type="eqref" reference="eq:estimate_A"} and [\[eq:estimate_B\]](#eq:estimate_B){reference-type="eqref" reference="eq:estimate_B"} shows that $a_nA^2$ and $B$ converge to $0$ as $n\to \infty$. Therefore, by [\[eq:reciprocal_expansion\]](#eq:reciprocal_expansion){reference-type="eqref" reference="eq:reciprocal_expansion"}, we have $$\left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1} = a_n - \dfrac{a_n^2}{a_{n+1}} + o(1) = a_n - \beta + o(1).$$ In other words, the difference $|(r-\sum_{k=1}^{n-1}(1/a_k))^{-1}+\beta-a_n|$ converges to $0$ as $n\to \infty$. ◻
:::

::: proof
*Proof of [2](#cor:Sylvester){reference-type="ref+Label" reference="cor:Sylvester"}.* First, we note that the Sylvester sequence satisfies $$\sum_{k=1}^{n-1}\dfrac{1}{s_k} = 1-\dfrac{1}{s_n-1},$$ by the recurrence relation $s_{n+1}=s_n^2-s_n+1$. Therefore, we also have $$\begin{align}
\label{eq:sylvester_recurrence}
    s_n=\left(1-\sum_{k=1}^{n-1}\dfrac{1}{s_k}\right)^{-1}+1.
\end{align}$$ Let $(a_n)_{n=1}^\infty$ be another sequence of positive integers satisfying $$\dfrac{2}{3}\leq \dfrac{a_n^2}{a_{n+1}}\leq \dfrac{4}{3},\quad \sum_{n=1}^\infty\dfrac{1}{a_n} = 1.$$ Applying [1](#thm:main){reference-type="ref+Label" reference="thm:main"} with $\beta=1$, we obtain $$\begin{align}
\label{eq:sylvester_recurrence_2}
    a_n\geq 15\implies a_n=\left\lfloor\left(1-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}+1\right\rceil.
\end{align}$$ Since $\sum_{n=1}^\infty(1/a_n)=1$, we have $a_1\geq 2$. Using the inequality $a_{n+1}\geq (3/4)a_n^2$ inductively, we obtain $$a_1\geq 2,\quad a_2\geq 3,\quad a_3\geq 7,\quad a_4\geq 37.$$ In particular, [\[eq:sylvester_recurrence_2\]](#eq:sylvester_recurrence_2){reference-type="eqref" reference="eq:sylvester_recurrence_2"} implies $$37\leq a_4=\left\lfloor\left(1-\sum_{k=1}^{3}\dfrac{1}{a_k}\right)^{-1}+1\right\rceil,$$ and hence $$\sum_{k=1}^3\dfrac{1}{a_k}\geq \dfrac{69}{71} >\dfrac{1}{2}+\dfrac{1}{3} + \dfrac{1}{8}.$$ Therefore, we must have $a_1=2$, $a_2=3$, $a_3=7$, and the rest of the sequence is determined by [\[eq:sylvester_recurrence_2\]](#eq:sylvester_recurrence_2){reference-type="eqref" reference="eq:sylvester_recurrence_2"}. Comparing this with [\[eq:sylvester_recurrence\]](#eq:sylvester_recurrence){reference-type="eqref" reference="eq:sylvester_recurrence"}, we conclude that $(a_n)_{n=1}^\infty$ coincides with the Sylvester sequence. ◻
:::

::: proof
*Proof of [3](#cor:Millin){reference-type="ref+Label" reference="cor:Millin"}.* Let $\phi=(1+\sqrt{5})/2$ and $\overline{\phi}=(1-\sqrt{5})/2$. Then, the Fibonacci sequence can be written as $F_n=(\phi^n-\overline{\phi}^n)/\sqrt{5}$, and hence we have $$\dfrac{F_{2^n}^2}{F_{2^{n+1}}} = \dfrac{1}{\sqrt{5}}\cdot\dfrac{\phi^{2^{n+1}}-2+\overline{\phi}^{2^{n+1}}}{\phi^{2^{n+1}}-\overline{\phi}^{2^{n+1}}}\leq \dfrac{1}{\sqrt{5}}\leq \dfrac{2}{3}.$$ Applying [1](#thm:main){reference-type="ref+Label" reference="thm:main"} with $\beta=1/3$, we obtain $$\begin{align}
\label{eq:Millin_recurrence}
    n\geq 3\implies F_{2^n}=\left\lfloor\left(\dfrac{5-\sqrt{5}}{2}-\sum_{k=1}^{n-1}\dfrac{1}{F_{2^k}}\right)^{-1}+\dfrac{1}{3}\right\rceil.
\end{align}$$ Let $(a_n)_{n=1}^\infty$ be another sequence of positive integers satisfying $$\dfrac{a_n^2}{a_{n+1}}\leq \dfrac{2}{3},\quad \sum_{n=1}^\infty\dfrac{1}{a_n} = \dfrac{5-\sqrt{5}}{2}.$$ Applying [1](#thm:main){reference-type="ref+Label" reference="thm:main"} with $\beta=(1/3)$, we obtain $$\begin{align}
\label{eq:Millin_recurrence_2}
    a_n\geq 4\implies a_n=\left\lfloor\left(\dfrac{5-\sqrt{5}}{2}-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}+\dfrac{1}{3}\right\rceil.
\end{align}$$ Using the inequality $a_{n+1}\geq (3/2)a_n^2$ inductively, we obtain $$a_1\geq 1,\quad a_2\geq 2,\quad a_3\geq 6,\quad a_4\geq 54.$$ In particular, [\[eq:Millin_recurrence_2\]](#eq:Millin_recurrence_2){reference-type="eqref" reference="eq:Millin_recurrence_2"} implies $$54\leq a_4 = \left\lfloor\left(\dfrac{5-\sqrt{5}}{2}-\sum_{k=1}^{3}\dfrac{1}{a_k}\right)^{-1}+\dfrac{1}{3}\right\rceil,$$ and hence $$\begin{align}
\label{eq:Millin_first_three}
    \sum_{k=1}^{3}\dfrac{1}{a_k}\geq \dfrac{1583 - 319 \sqrt{5}}{638} = 1.3631572\cdots.
\end{align}$$ This easily implies that $a_1=1$ and $a_2=3$. The rest of the sequence is determined by [\[eq:Millin_recurrence_2\]](#eq:Millin_recurrence_2){reference-type="eqref" reference="eq:Millin_recurrence_2"}. Comparing this with [\[eq:Millin_recurrence\]](#eq:Millin_recurrence){reference-type="eqref" reference="eq:Millin_recurrence"}, we conclude that $(a_n)_{n=1}^\infty$ coincides with $(F_{2^n})_{n=1}^\infty$. ◻
:::

::: proof
*Proof of [4](#type2_countable){reference-type="ref+Label" reference="type2_countable"}.* By definition, $(1,\infty)\setminus\mathcal{I}$ consists of real numbers $\alpha>1$ such that there exists a sequence of positive integers $(a_n)_{n=1}^\infty$ satisfying $$a_n\approx \alpha^{2^n}\quad\text{and}\quad \sum_{n=1}^\infty\dfrac{1}{a_n} \in \mathbb{Q}.$$ Let $\mathcal{S}$ denote the set of all such sequences, i.e., $$\mathcal{S}:=\bigcup_{\alpha>1}\left\{(a_n)_{n=1}^\infty \mathrel{}\middle|\mathrel{}a_n\approx \alpha^{2^n},\ \sum_{n=1}^\infty\dfrac{1}{a_n}\in \mathbb{Q}\right\}.$$ Then, there is a surjective map $$\mathcal{S}\to (1,\infty)\setminus\mathcal{I};\quad (a_n)_{n=1}^\infty\mapsto \lim_{n\to \infty} a_n^{2^{-n}}.$$ It suffices to show that $\mathcal{S}$ is countable. Let $(a_n)_{n=1}^\infty$ be an element of $\mathcal{S}$. Then, we have $\lim_{n\to \infty}(a_n^2/a_{n+1})=1$ and $\lim_{n\to \infty}a_n=\infty$. By [1](#thm:main){reference-type="ref+Label" reference="thm:main"}, there exists an integer $n_0>0$ such that $$n\geq n_0\implies a_n = \left\lfloor\left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}+1\right\rceil,$$ where $r=\sum_{n=1}^\infty(1/a_n)$. In particular, the sequence $(a_n)_{n=1}^\infty$ is uniquely determined by the tuple $(a_1,\dots,a_{n_0-1},r)$. Since the set of all such tuples is countable, it follows that $\mathcal{S}$ is countable. ◻
:::

# Pseudo-greedy expansion

Given a positive real number $r$, there are many possible ways to express $r$ as a (possibly infinite) sum of unit fractions. The simplest choice is the *greedy expansion*, which is given by $$r=\dfrac{1}{a_1}+\dfrac{1}{a_2}+\dfrac{1}{a_3}+\cdots,\quad a_n=\left\lceil\left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}\right\rceil.$$ It can be easily shown that the greedy expansion of any positive rational number terminates in finite steps. Another interesting choice is the *odd greedy expansion*, where $a_n$ is defined to be the smallest odd number $\geq (r-\sum_{k=1}^{n-1}(1/a_k))^{-1}$. It is an open problem whether the odd greedy expansion of a positive rational number with odd denominator terminates in finite steps (see [@Guy_unsolved p. 88]).

Motivated by [1](#thm:main){reference-type="ref+Label" reference="thm:main"}, we study the following variant of the greedy expansion:

::: definition
**Definition 7**. Let $r$ be a positive real number. Define a sequence of positive integers $(a_n)_{n=1}^\infty$ by $$a_n=\left\lfloor \left(r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\right)^{-1}+1\right\rceil.$$ We call $(a_n)_{n=1}^\infty$ the *pseudo-greedy expansion* of $r$.
:::

::: lemma
**Lemma 8**. *Let $r$ be a positive real number and $(a_n)_{n=1}^\infty$ be its pseudo-greedy expansion. Then, we have $r = \sum_{n=1}^{\infty}(1/a_n)$.*
:::

::: proof
*Proof.* We define a sequence of positive real numbers $(x_n)_{n=1}^\infty$ by $x_n=r-\sum_{k=1}^{n-1}(1/a_k)$. Since $(x_n)_{n=1}^\infty$ is decreasing, we have $\lim_{n\to \infty}x_n=\gamma$ for some real number $\gamma\geq 0$. By definition, we have $a_n=\lfloor x_n^{-1} +1\rceil\leq x_n^{-1}+2$ and hence $$x_{n+1}=x_n-\dfrac{1}{a_n}\leq x_n - \dfrac{1}{x_n^{-1}+2} = x_n\left(1-\dfrac{1}{1+2x_n}\right).$$ Taking the limit as $n\to \infty$, we obtain $$\gamma\leq \gamma\left(1-\dfrac{1}{1+2\gamma}\right)$$ and hence $\gamma=0$. Therefore, we have $r = \sum_{n=1}^{\infty}(1/a_n)$. ◻
:::

::: definition
**Definition 9**. Let $r$ be a positive real number and $(a_n)_{n=1}^\infty$ be its pseudo-greedy expansion. We define a sequence of positive real numbers $(x_n)_{n=1}^\infty$ by $$x_n=r-\sum_{k=1}^{n-1}\dfrac{1}{a_k}.$$ We call $(x_n)_{n=1}^\infty$ the *remainder sequence* of the pseudo-greedy expansion of $r$. By definition, we have $a_n=\lfloor x_n^{-1}+1\rceil$. We also define a sequence of real numbers $(\varepsilon_n)_{n=1}^\infty$ by $$\varepsilon_n = x_n^{-1}+1-a_n.$$ We call $(\varepsilon_n)_{n=1}^\infty$ the *gap sequence* of the pseudo-greedy expansion of $r$.
:::

As an immediate consequence of [1](#thm:main){reference-type="ref+Label" reference="thm:main"}, we obtain the following:

::: {#cor:main .corollary}
**Corollary 10**. *Let $(a_n)_{n=1}^\infty$ be a sequence of positive integers satisfying $$\lim_{n\to \infty}\dfrac{a_n^2}{a_{n+1}}=1\quad\text{and}\quad
        \sum_{n=1}^\infty \dfrac{1}{a_n}<\infty.$$ Then, there is some integer $N\geq 0$ such that $(a_{N+n})_{n=1}^\infty$ is the pseudo-greedy expansion of $\sum_{n=1}^\infty(1/a_{N+n})$. Moreover, the gap sequence of this expansion satisfies $\lim_{n\to \infty}\varepsilon_n=0$.*
:::

::: {#example:sylvester .example}
**Example 11**. The pseudo-greedy expansion of $1$ is given by the Sylvester sequence: $$1=\dfrac{1}{2}+\dfrac{1}{3}+\dfrac{1}{7}+\dfrac{1}{43}+\dfrac{1}{1807}+\cdots.$$ More generally, for any integer $m>0$, the pseudo-greedy expansion of $1/m$ is given by $a_n=s_n(m)$, where $$s_1(m)=m+1,\quad s_{n+1}(m)=s_n(m)^2-s_n(m)+1.$$ The remainder/gap sequences are given by $x_n = 1/(s_n(m)-1)$, $\varepsilon_n=0$. It is known that there is a constant $c(m)>1$ such that $s_n(m)\approx c(m)^{2^n}$ (see [@Concrete p. 109]). Wagner-Ziegler [@Wagner_Ziegler] showed that $c(m)$ is irrational, and Dubickas [@Dubickas] showed that $c(m)$ is transcendental.
:::

The recurrence relation $a_{n+1}=a_n^2-a_n+1$ appearing in [11](#example:sylvester){reference-type="ref+Label" reference="example:sylvester"} is a special case of the following:

::: {#lem:PG_sylvester .lemma}
**Lemma 12**. *Let $r$ be a positive real number, and $(a_n)_{n=1}^\infty$, $(\varepsilon_n)_{n=1}^\infty$ be its pseudo-greedy expansion and the gap sequence. Then, we have $$a_{n+1}=\dfrac{1}{1-\varepsilon_n}a_n^2-a_n+(1-\varepsilon_{n+1}).$$*
:::

::: proof
*Proof.* By definition, we have $x_n^{-1}=a_n-(1-\varepsilon_n)$ and hence $$x_{n+1}=x_n-\dfrac{1}{a_n}=\dfrac{1}{a_n-(1-\varepsilon_n)}-\dfrac{1}{a_n}=\dfrac{1-\varepsilon_n}{a_n^2-(1-\varepsilon_n)a_n}.$$ Substituting this into $a_{n+1}=x_{n+1}^{-1}+1-\varepsilon_{n+1}$, we obtain the desired formula. ◻
:::

::: lemma
**Lemma 13**. *Let $r$ be a positive real number, and $(\varepsilon_n)_{n=1}^\infty$ be the gap sequence of the pseudo-greedy expansion of $r$. Then, we have $$\varepsilon_n=0\implies \varepsilon_{n+1}=0.$$*
:::

::: proof
*Proof.* Let $(a_n)_{n=1}^\infty$, $(x_n)_{n=1}^\infty$ be the pseudo-greedy expansion of $r$ and its remainder sequence. If $\varepsilon_n=0$, then $x_n^{-1}$ is an integer, so we can write $x_n=1/m$ for some positive integer $m$. Then, we have $a_n = m+1$ and hence $$x_{n+1}=x_n-\dfrac{1}{a_n} = \dfrac{1}{m(m+1)}.$$ This shows that $x_{n+1}^{-1}$ is an integer and thus $\varepsilon_{n+1}=0$. ◻
:::

:::: {#ex:1129 .example}
**Example 14**. The pseudo-greedy expansion of $11/29$ is given as follows:

::: center
         $n$               $1$                 $2$                 $3$                   $4$                     $5$                        $6$                $\cdots$
  ----------------- ------------------ ------------------- -------------------- ---------------------- ----------------------- ------------------------------ ----------
        $x_n$        $\dfrac{11}{29}$   $\dfrac{15}{116}$   $\dfrac{19}{1044}$        $\dfrac{5}        $\dfrac{1}{10684296}$   $\dfrac{1}{114154191699912}$   $\cdots$
                                                                                             {14616}$                                                         
        $a_n$              $4$                 $9$                 $56$                 $2924$               $10684297$              $114154191699913$         $\cdots$
   $\varepsilon_n$   $-\dfrac{4}{11}$   $-\dfrac{4}{15}$     $-\dfrac{1}{19}$       $\dfrac{1}{5}$               $0$                        $0$                $\cdots$
:::

We see that $(a_5,a_6,\dots)$ is the pseudo-greedy expansion of $1/10684296$, which is given as in [11](#example:sylvester){reference-type="ref+Label" reference="example:sylvester"}. In other words, we have $\varepsilon_5=\varepsilon_6=\cdots=0$.
::::

We conjecture that for any positive rational number $r$, the gap sequence of the pseudo-greedy expansion satisfies $\varepsilon_n=0$ for $n\gg 0$, at least when $\varepsilon_n\to 0$ ([6](#conj){reference-type="ref+Label" reference="conj"}). We confirmed by a computer that this conjecture is true for $r=p/q$ with $0<p\leq q\leq 10^5$. Note that this conjecture resembles the termination problem of the odd greedy expansion.

Let us take a closer look at the pseudo-greedy expansion of positive rational numbers.

::: {#lem:rational_PG .lemma}
**Lemma 15**. *Let $r=p/q$ be a positive rational number, and $(a_n)_{n=1}^\infty$, $(x_n)_{n=1}^\infty$, $(\varepsilon_n)_{n=1}^\infty$ be its pseudo-greedy expansion, the remainder sequence, and the gap sequence.*

1.  *Let $d_n=qa_1a_2\cdots a_{n-1}$. Then we can write $$x_n=\dfrac{c_n}{d_n},\quad \varepsilon_n = \dfrac{e_n}{c_n},$$ where $c_n$ is a positive integer and $e_n$ is an integer.*

2.  *The pair $(c_n,d_n)$ determines $(e_n,a_n)$ by $$\begin{cases}
                e_n\equiv d_n\pmod{c_n},\quad -\dfrac{c_n}{2}\leq e_n<\dfrac{c_n}{2},\\
                a_n = \dfrac{d_n-e_n}{c_n}+1.
            \end{cases}$$ The tuple $(c_n,d_n,e_n,a_n)$ determines $(c_{n+1},d_{n+1})$ by $$\begin{cases}
                c_{n+1}=c_n-e_n,\\
                d_{n+1}=d_na_n.
            \end{cases}$$*

3.  *We have the following asymptotic estimates: $$c_n=O\left(\dfrac{a_1a_2\cdots a_{n-1}}{a_n}\right),\quad
                c_n=O(1.5^n).$$*
:::

::: proof
*Proof.*

1.  By definition, we have $$x_n = \dfrac{p}{q}-\sum_{k=1}^{n-1}\dfrac{1}{a_k}\in \dfrac{1}{qa_1\cdots a_{n-1}}\mathbb{Z}.$$ Therefore, we can write $x_n=c_n/d_n$ for some positive integer $c_n$. The formula $\varepsilon_n=x_n^{-1}+1-a_n$ implies that $\varepsilon_n\in (1/c_n)\mathbb{Z}$, so we can write $\varepsilon_n = e_n/c_n$ for some integer $e_n$.

2.  The definition of $\varepsilon_n$ can be reformulated as $\varepsilon_n=x_n^{-1}-\lfloor x_n^{-1}\rceil$. Therefore, $\varepsilon_n$ is characterized by $$\varepsilon_n\equiv x_n^{-1} \pmod 1,\quad -\dfrac{1}{2}\leq \varepsilon_n < \dfrac{1}{2}.$$ Since $\varepsilon_n=e_n/c_n$, this yields the characterization of $e_n$. The formula for $a_n$ follows from $a_n = x_n^{-1}  - \varepsilon_n + 1$. The equality $d_{n+1}=d_na_n$ is immediate from the definition. Finally, the formula for $c_{n+1}$ follows from $$x_{n+1}=x_n-\dfrac{1}{a_n}=\dfrac{c_na_n-d_n}{d_na_n} = \dfrac{c_n-e_n}{d_{n+1}}.$$

3.  The first estimate follows $d_n=qa_1a_2\cdots a_{n-1}$ and $$a_n = \lfloor x_n^{-1}+1\rceil\approx x_n^{-1}=\dfrac{d_n}{c_n}.$$ The second one follows from $c_{n+1}= c_n-e_n\leq 1.5c_n$.

 ◻
:::

Now we prove that [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} by Erdős-Graham is equivalent to our [6](#conj){reference-type="ref+Label" reference="conj"}:

::: {#thm:equiv .theorem}
**Theorem 16**. *[6](#conj){reference-type="ref+Label" reference="conj"} is true if and only if [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} has an affirmative answer.*
:::

::: proof
*Proof.* First, suppose that [6](#conj){reference-type="ref+Label" reference="conj"} is true. Let $(a_n)_{n=1}^\infty$ be a sequence of positive integers satisfying $$\lim_{n\to \infty}\dfrac{a_n^2}{a_{n+1}}=1\quad\text{and}\quad
        \sum_{n=1}^\infty \dfrac{1}{a_n}\in \mathbb{Q}.$$ By [10](#cor:main){reference-type="ref+Label" reference="cor:main"}, we may assume that $(a_n)_{n=1}^\infty$ is the pseudo-greedy expansion of some positive rational number $r$, and that its gap sequence satisfies $\lim_{n\to \infty}\varepsilon_n=0$. By our assumption that [6](#conj){reference-type="ref+Label" reference="conj"} is true, we have $\varepsilon_n=0$ for $n\gg 0$. The formula $$\begin{align}
\label{eq:pseudo-sylvester}
        a_{n+1}=\dfrac{1}{1-\varepsilon_n}a_n^2-a_n+(1-\varepsilon_{n+1})
\end{align}$$ given in [12](#lem:PG_sylvester){reference-type="ref+Label" reference="lem:PG_sylvester"} shows that $a_{n+1}=a_n^2-a_n+1$ for $n\gg 0$.

Conversely, suppose that [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} has an affirmative answer. Let $r$ be a positive rational number and $(a_n)_{n=1}^\infty$ be its pseudo-greedy expansion. We define the quantities $c_n$ and $e_n$ as in [15](#lem:rational_PG){reference-type="ref+Label" reference="lem:rational_PG"}. Assume that the gap sequence satisfies $\lim_{n\to \infty}\varepsilon_n=0$. Then, the formula [\[eq:pseudo-sylvester\]](#eq:pseudo-sylvester){reference-type="eqref" reference="eq:pseudo-sylvester"} shows that $$\lim_{n\to \infty}\dfrac{a_n^2}{a_{n+1}}=1.$$ Therefore, by our assumption that [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} has an affirmative answer, we have $a_{n+1}=a_n^2-a_n+1$ for $n\gg 0$. Comparing this with the formula [\[eq:pseudo-sylvester\]](#eq:pseudo-sylvester){reference-type="eqref" reference="eq:pseudo-sylvester"}, we obtain $$\dfrac{\varepsilon_na_n^2}{1-\varepsilon_n}= \varepsilon_{n+1} = o(1).$$ In particular, we have $\varepsilon_n=o(a_n^{-2})$. Combining this with the estimate $c_n=O(1.5^n)$ given in [15](#lem:rational_PG){reference-type="ref+Label" reference="lem:rational_PG"} (3), we obtain $e_n=c_n\varepsilon_n=o(1)$. Since $e_n$ is an integer, we see that $e_n=0$ holds for $n\gg 0$. This shows that [6](#conj){reference-type="ref+Label" reference="conj"} is true. ◻
:::

::: {#rem:heuristic .remark}
**Remark 17**. Using [15](#lem:rational_PG){reference-type="ref+Label" reference="lem:rational_PG"}, we can provide a heuristic argument showing that [6](#conj){reference-type="ref+Label" reference="conj"} is likely to be correct even without assuming $\lim_{n\to \infty}\varepsilon_n=0$. Let $r$ be a positive rational number, and define $c_n$, $d_n$, and $e_n$ as in [15](#lem:rational_PG){reference-type="ref+Label" reference="lem:rational_PG"}. By [15](#lem:rational_PG){reference-type="ref+Label" reference="lem:rational_PG"} (2), we have $c_{n+1}=c_n-e_n$ and hence $$\dfrac{c_{n+1}}{c_n} = 1-\dfrac{e_n}{c_n},\quad -\dfrac{1}{2}\leq \dfrac{e_n}{c_n}< \dfrac{1}{2}.$$ Thus the behavior of $(c_n)_{n=1}^\infty$ can be modeled by the multiplicative random walk $c_{n+1} = t_nc_n$, where $t_n$ is chosen uniformly randomly from $[1/2,3/2)$. Since we have $$\mathbb{E}[\log t_n] = \int_{1/2}^{3/2} \log t\ dt = \dfrac{3}{2}\log 3 - \log 2 - 1 = -0.0452287\cdots < 0,$$ $c_n$ tends to shrink exponentially on average, so it is natural to expect that $e_n=0$ holds for some $n$.
:::

::::: remark
**Remark 18**. When actually computing the values of $\varepsilon_n$ for a given rational number $r$, directly performing the calculation will cause the values of $a_n$ and $d_n$ to grow explosively large. We can use modular arithmetic to avoid this problem. When the values of $c_1, \dots, c_n$ and $e_1, \dots, e_{n-1}$ are known, one can use the recurrence relation from [15](#lem:rational_PG){reference-type="ref+Label" reference="lem:rational_PG"} (2) to inductively compute, for $k = 1, 2, \dots, n-1$, the residue classes $$a_k \pmod{c_{k+1}c_{k+2}\cdots c_n}\quad\text{and}\quad d_{k+1} \pmod{c_{k+1}c_{k+2}\cdots c_n}.$$ In particular, we can compute $d_n \pmod{c_n}$, and this value can then be used to determine $e_n$ and $c_{n+1}$. The following is a pseudocode for computing the gap sequence $(\varepsilon_n)_{n=1}^\infty$ of the pseudo-greedy expansion of a positive rational number $r=p/q$.

:::: algorithm
::: algorithmic
$d_1 \gets q$ $a_k \gets ((d_k - e_k)/c_k) + 1 \pmod{c_{k+1}\cdots c_n}$ $d_{k+1}\gets d_ka_k  \pmod{c_{k+1}\cdots c_n}$ $e_n \gets d_n - c_n\lfloor d_n/c_n\rceil$ $c_{n+1} \gets c_n - e_n$ $\varepsilon_n \gets e_n/c_n$ Print $\varepsilon_n$
:::
::::
:::::

Finally, we reinterpret the partial results on [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} due to Erdős-Straus [@Erdos_Straus_63] and Badea [@Badea] within our framework. In terms of the pseudo-greedy expansion, their results can be regarded as the following special cases of [6](#conj){reference-type="ref+Label" reference="conj"}:

::: {#prop:Badea .proposition}
**Proposition 19**. *Let $r$ be a positive rational number, and $(\varepsilon_n)_{n=1}^\infty$ be the gap sequence of the pseudo-greedy expansion of $r$. Suppose that one of the following conditions is satisfied:*

1.  *$\liminf_{n\to \infty}\varepsilon_n\prod_{k=1}^{n-1}(1-\varepsilon_k)\geq 0.$*

2.  *$\varepsilon_n\geq 0$ holds for $n\gg 0$.*

*Then, we have $\varepsilon_n=0$ for $n\gg 0$.*
:::

::: proof
*Proof.* We define the quantities $c_n$ and $e_n$ as in [15](#lem:rational_PG){reference-type="ref+Label" reference="lem:rational_PG"}.

1.  By [15](#lem:rational_PG){reference-type="ref+Label" reference="lem:rational_PG"} (2), we have $c_{n+1}=c_n-e_n$ and hence $$e_n=\varepsilon_nc_n=\varepsilon_nc_1\prod_{k=1}^{n-1}\left(1-\dfrac{e_k}{c_k}\right)=c_1\cdot\varepsilon_n\prod_{k=1}^{n-1}(1-\varepsilon_k).$$ Our assumption shows that $\liminf_{n\to \infty}e_n\geq 0$. Since $e_n$ is an integer, we conclude that $e_n\geq 0$ holds for $n\gg 0$. Therefore, this case is reduced to (2).

2.  By [15](#lem:rational_PG){reference-type="ref+Label" reference="lem:rational_PG"} (2), we have $c_{n+1} = c_n-e_n$ and hence $(c_n)_{n=1}^\infty$ is eventually non-increasing. Since $c_n$ is a positive integer, $(c_n)_{n=1}^\infty$ is eventually constant and thus $e_n=0$ holds for $n\gg 0$.

 ◻
:::

::: {#cor:Badea .corollary}
**Corollary 20**. *Let $(a_n)_{n=1}^\infty$ be a sequence of positive integers satisfying $$\lim_{n\to \infty}\dfrac{a_n^2}{a_{n+1}}=1\quad\text{and}\quad
        \sum_{n=1}^\infty \dfrac{1}{a_n}\in \mathbb{Q}.$$ Suppose that one of the following conditions is satisfied:*

1.  *(Erdős-Straus [@Erdos_Straus_63]) $\liminf_{n\to \infty}\dfrac{a_1a_2\cdots a_{n-1}}{a_n}\left(1-\dfrac{a_n^2}{a_{n+1}}\right)\geq 0$.*

2.  *(Badea [@Badea]) $a_{n+1}\geq a_n^2-a_n+1$ holds for $n\gg 0$.*

*Then, $a_{n+1}=a_n^2-a_n+1$ holds for $n\gg 0$.*
:::

::: proof
*Proof.* By [10](#cor:main){reference-type="ref+Label" reference="cor:main"}, we may assume that $(a_n)_{n=1}^\infty$ is the pseudo-greedy expansion of some positive rational number $r$, and that its gap sequence satisfies $\lim_{n\to \infty}\varepsilon_n=0$. By [12](#lem:PG_sylvester){reference-type="ref+Label" reference="lem:PG_sylvester"}, it suffices to shows that $\varepsilon_n=0$ holds for $n\gg 0$.

1.  By [12](#lem:PG_sylvester){reference-type="ref+Label" reference="lem:PG_sylvester"}, we have $a_{n+1}=(a_n^2/(1-\varepsilon_n))(1+O(a_n^{-1}))$, and hence we can write $$\begin{align}
    \label{eq:ratio_vs_epsilon}
        \dfrac{a_n^2}{a_{n+1}} = (1-\varepsilon_n)(1+\beta_n),
    \end{align}$$ where $\beta_n=O(a_n^{-1})$. We can write $a_1a_2\cdots a_{n-1}/a_n$ as $$\begin{align}
    \label{eq:product}
        \dfrac{a_1a_2\cdots a_{n-1}}{a_n}=\dfrac{1}{a_1}\prod_{k=1}^{n-1}\dfrac{a_k^2}{a_{k+1}}=\dfrac{1}{a_1}\prod_{k=1}^{n-1}(1-\varepsilon_k) \prod_{k=1}^{n-1}(1+\beta_k).
    \end{align}$$ The infinite product $\prod_{k=1}^\infty(1+\beta_k)$ converges since $\beta_k=O(a_k^{-1})$. In particular, the quantity $$B_n:=\dfrac{1}{a_1}\prod_{k=1}^n(1+\beta_k)>0$$ is bounded. Combining [\[eq:ratio_vs_epsilon\]](#eq:ratio_vs_epsilon){reference-type="eqref" reference="eq:ratio_vs_epsilon"} with [\[eq:product\]](#eq:product){reference-type="eqref" reference="eq:product"}, we obtain $$\dfrac{a_1a_2\cdots a_{n-1}}{a_n}\left(1-\dfrac{a_n^2}{a_{n+1}}\right)=B_{n-1} \varepsilon_n\prod_{k=1}^{n-1}(1-\varepsilon_k) - B_{n-1}\beta_n\prod_{k=1}^{n}(1-\varepsilon_k).$$ The second term of the right hand side is $o(1)$ because $\beta_n=O(a_n^{-1})$ and $|\varepsilon_k|\leq (1/2)$. Thus, our assumption is equivalent to $\liminf_{n\to \infty}\varepsilon_n\prod_{k=1}^{n-1}(1-\varepsilon_k)\geq 0$. By [19](#prop:Badea){reference-type="ref+Label" reference="prop:Badea"} (1), we conclude that $\varepsilon_n=0$ for $n\gg 0$.

2.  By [12](#lem:PG_sylvester){reference-type="ref+Label" reference="lem:PG_sylvester"}, our assumption can be reformulated as $$\dfrac{\varepsilon_n a_n^2}{1-\varepsilon_n}\geq \varepsilon_{n+1}\quad (n\gg 0).$$ In particular, for sufficiently large $n$, we have $$\varepsilon_n<0\implies \varepsilon_n>\varepsilon_{n+1}.$$ Suppose that we have $\varepsilon_n<0$ for infinitely many $n$. Then, the above implication shows that $\varepsilon_n$ is decreasing for $n\gg 0$. This contradicts the fact that $\varepsilon_n$ converges to $0$. Therefore, we have $\varepsilon_n\geq 0$ for $n\gg 0$. By [19](#prop:Badea){reference-type="ref+Label" reference="prop:Badea"} (2), we conclude that $\varepsilon_n=0$ for $n\gg 0$.

 ◻
:::

::: remark
**Remark 21**. The aforementioned result of Erdős-Straus solves [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} under the condition $$\dfrac{a_n^2}{a_{n+1}}=1+o(n^{-1}).$$ Indeed, if we write $(a_n^2/a_{n+1})=1-\gamma_n$ with $\gamma_n=o(n^{-1})$, then we have $$\dfrac{a_1a_2\cdots a_{n-1}}{a_n}\left(1-\dfrac{a_n^2}{a_{n+1}}\right)=
    \dfrac{1}{a_1}\left(1-\dfrac{a_n^2}{a_{n+1}}\right)\prod_{k=1}^{n-1}\dfrac{a_k^2}{a_{k+1}} = \dfrac{\gamma_n}{a_1}\prod_{k=1}^{n-1}(1-\gamma_k) =o(1),$$ so we can apply [20](#cor:Badea){reference-type="ref+Label" reference="cor:Badea"} (1).
:::

::: {#rem:irr .remark}
**Remark 22**. Suppose that [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} has an affirmative answer, or equivalently, that [6](#conj){reference-type="ref+Label" reference="conj"} is true. Recall the set $\mathcal{I}$ from [4](#type2_countable){reference-type="ref+Label" reference="type2_countable"}, and let $\alpha\in (1,\infty)\setminus \mathcal{I}$. By definition, there is a sequence of positive integers $(a_n)_{n=1}^\infty$ satisfying $a_n\approx \alpha^{2^n}$ whose reciprocal sum is rational. By our assumption, $(a_n)_{n=1}^\infty$ eventually follows the recurrence relation $$a_{n+1}=a_n^2-a_n+1.$$ In other words, there is some integer $N\geq 0$ and a positive integer $m$ such that $a_{N+n} = s_n(m)$, where $s_n(m)$ is the sequence defined in [11](#example:sylvester){reference-type="ref+Label" reference="example:sylvester"}. In particular, $\alpha$ is given by $$\alpha = \lim_{n\to \infty} a_{N+n}^{2^{-(N+n)}} = \lim_{n\to \infty} s_n(m)^{2^{-(N+n)}}=c(m)^{2^{-N}},$$ where $c(m)$ is the constant defined in [11](#example:sylvester){reference-type="ref+Label" reference="example:sylvester"}. Therefore, assuming that [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} has an affirmative answer, we can conclude that $$(1,\infty)\setminus\mathcal{I}=\{c(m)^{2^{-N}}\mid N\geq 0,\ m>0\}.$$ Since $c(m)$ is transcendental by the result of Dubickas [@Dubickas], this implies that $\overline{\mathbb{Q}}\cap(1,\infty)\subset \mathcal{I}$. In particular, an affirmative answer to [5](#ques:erdos){reference-type="ref+Label" reference="ques:erdos"} will imply that $2^{2^n}$ is a Type 2 irrationality sequence.
:::

[^1]:

[^2]: In the original definition [@Erdos_Graham_80], the sequence was required to be strictly increasing, i.e., $a_1<a_2<a_3<\cdots$. In this paper, we relax this condition by allowing equality, enabling us to consider sequences such as $\lfloor \alpha^{2^n}\rfloor$.
