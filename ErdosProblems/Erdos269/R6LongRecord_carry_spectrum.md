<!-- Companion long-record migration for Erdős #269 round 6. -->
<!-- Destination label: long:carry-spectrum -->
<!-- Not frozen R. Source: erdos_269_research_memorandum_r6.md. -->

## 4. The carry has an exact continuum spectrum

The normalised carry also admits a useful analytic interpretation. Let $0<c<1$ and consider
$$
\mathcal C_c(x,y)=c+(1-c)\mathbf1_{\{x+y<1\}},\qquad 0\le x,y\le1.
$$
Its integral operator on $L^2(0,1)$ is
$$
(T_cf)(x)=c\int_0^1f(y)\,dy+(1-c)\int_0^{1-x}f(y)\,dy.
$$
It is a reflected Volterra operator plus a rank-one operator. Passing from an integral eigenproblem to a differential boundary problem is a standard method for Volterra operators; see [V]. The calculation below identifies this particular kernel explicitly.

### 4.1 Eigenvalues and eigenfunctions

Put $a=1-c$ and
$$
\theta=2\arctan\frac{1-c}{1+c}=\frac\pi2-2\arctan c.
$$

**Theorem 4.1.** The operator $T_c$ is compact, self-adjoint and injective. Its nonzero eigenvalues are simple and are precisely
$$
\boxed{\lambda_n=\frac{1-c}{\theta+2\pi n},\qquad n\in\mathbb Z.} \tag{4.1}
$$
An orthonormal eigenbasis is
$$
\phi_n(x)=\sqrt{\frac{2}{1+c^2}}
\bigl(\cos(k_nx)-c\sin(k_nx)\bigr),\qquad k_n=\theta+2\pi n.
$$

*Proof.* Symmetry and square integrability of the kernel give compactness and self-adjointness. If $T_cf=0$, differentiating in the weak sense gives $-af(1-x)=0$, hence injectivity.

For $T_cf=\lambda f$, $\lambda\ne0$, the integral formula first gives an absolutely continuous representative, and then
$$
\lambda f'(x)=-af(1-x),\qquad f''(x)=-(a/\lambda)^2f(x).
$$
The endpoint values imply $f(1)=cf(0)$. Write the signed quantity $k=a/\lambda$. Then $f'(0)=-kc f(0)$, so
$$
f(x)=A(\cos(kx)-c\sin(kx)).
$$
Here $A\ne0$, since otherwise the solution is identically zero. The conditions at $x=1$ give
$$
\cos k-c\sin k=c,\qquad \sin k+c\cos k=1.
$$
Solving yields
$$
\cos k=\frac{2c}{1+c^2},\qquad
\sin k=\frac{1-c^2}{1+c^2},
$$
so $k=\theta+2\pi n$. Conversely each such function satisfies the derivative identity and the integral equation at $x=0$, because its integral equals $a/k$. Therefore it is an eigenfunction with eigenvalue $a/k$.

The squared norm of the unnormalised function is $(1+c^2)/2$; substituting the two displayed trigonometric values cancels its oscillatory correction. Different eigenvalues are orthogonal. The spectral theorem for compact self-adjoint operators, together with injectivity, gives completeness. $\square$

The squared Hilbert--Schmidt norm provides a useful independent identity:
$$
\sum_{n\in\mathbb Z}\lambda_n^2
=\int_0^1\!\int_0^1|\mathcal C_c(x,y)|^2\,dx\,dy
=\frac{1+c^2}{2}.
$$

### 4.2 Exact mean-square approximation and the actual rotation samples

The singular values, in decreasing order, are
$$
\frac a\theta,\quad\frac a{2\pi-\theta},\quad
\frac a{2\pi+\theta},\quad\frac a{4\pi-\theta},\quad\ldots.
$$
Writing them as $s_1\ge s_2\ge\cdots$, the spectral truncation theorem gives
$$
\inf_{\operatorname{rank}F\le d}
\|\mathcal C_c-F\|_{L^2((0,1)^2)}
=\left(\sum_{j>d}s_j^2\right)^{1/2}
\sim\frac{1-c}{\pi\sqrt d}. \tag{4.2}
$$
The asymptotic follows from $s_j\sim(1-c)/(\pi j)$.

Let $\alpha,\beta$ be individually irrational and
$$
(C_N)_{ij}=\mathcal C_c(\{i\alpha\},\{j\beta\}),\qquad 0\le i,j<N.
$$
For every fixed $d$,
$$
\lim_{N\to\infty}\frac1N
\inf_{\operatorname{rank}A\le d}\|C_N-A\|_F
=\left(\sum_{j>d}s_j^2\right)^{1/2}. \tag{4.3}
$$

*Proof.* Sort the row phases and column phases separately. Individual equidistribution implies that their maximum distances from the corresponding uniform quantile intervals tend to zero. Call these distances $\varepsilon_x,\varepsilon_y$. Regard the permuted matrix as a step kernel on the $N\times N$ equal partition. It differs from $\mathcal C_c$ only in the strip
$$
|x+y-1|\le\varepsilon_x+\varepsilon_y,
$$
up to null boundary sets. Its Hilbert--Schmidt error is at most
$$
(1-c)\sqrt{2(\varepsilon_x+\varepsilon_y)}.
$$
Distance to the set of rank-at-most-$d$ kernels is a 1-Lipschitz function of the ambient Hilbert--Schmidt norm. The step-kernel distance equals $N^{-1}$ times the matrix Frobenius distance: projecting a candidate approximation onto the step spaces in each variable cannot increase either error or rank. This proves (4.3). It also proves convergence of every fixed singular value $\sigma_j(C_N)/N$ to $s_j$. $\square$

For the running-LCM carry take $\alpha=\log_r p$ and $\beta=\log_r q$. Their individual irrationality is sufficient; no rational independence of $1,\alpha,\beta$ is used. The limit in (4.3) keeps $d$ fixed. An assertion with $d=d(N)$ needs a quantitative discrepancy estimate and is not included.

### 4.3 The norm distinction becomes visible

For thresholds $\tau\ne\sigma$, the corresponding continuum columns satisfy
$$
\|v_\tau-v_\sigma\|_\infty=1-c,
\qquad
\|v_\tau-v_\sigma\|_2=(1-c)\sqrt{|\tau-\sigma|}.
$$
Thus the threshold family is non-precompact in the supremum norm and compact in the mean-square metric. This explains how the existing positive infinite uniform approximation threshold coexists with the decay (4.2). The operator here is the normalised carry, not the unbounded actual tail cocycle. Its spectral solution does not discharge the packet's nonstationary arithmetic obligation.
