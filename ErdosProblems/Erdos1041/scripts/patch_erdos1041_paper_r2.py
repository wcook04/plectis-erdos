#!/usr/bin/env python3
"""Surgical edits to erdos-1041-lemniscate-newton-flow.tex for the 2026-09-06
revision assimilation. All replacement bodies are authored from the live
Erdos1041 notes (AbelControlPolygon, AngularBudgetLowCriticalClosure,
UnconditionalConstantFactorBound, DiskFamilyCriticalValueSeparation,
ExactObstructionsR2). This file is not Type B's short note.
"""
from __future__ import annotations

from pathlib import Path

PAPER = (
    Path(__file__).resolve().parents[2]
    / "papers"
    / "erdos-1041-lemniscate-newton-flow.tex"
)


def sub(text: str, old: str, new: str, label: str) -> str:
    if old not in text:
        raise SystemExit(f"anchor missing: {label}")
    if text.count(old) != 1:
        raise SystemExit(f"anchor not unique ({text.count(old)}): {label}")
    return text.replace(old, new, 1)


def main() -> int:
    text = PAPER.read_text()

    text = sub(
        text,
        r"\date{30 August 2026}",
        r"\date{6 September 2026}",
        "date",
    )

    old_abs_open = r"\begin{abstract}"
    old_abs_close = r"\end{abstract}"
    i0 = text.find(old_abs_open)
    i1 = text.find(old_abs_close)
    if i0 < 0 or i1 < 0 or i1 < i0:
        raise SystemExit("abstract anchors missing")
    new_abs = r"""\begin{abstract}
\noindent
Let $f(z)=\prod_i(z-z_i)$ be monic, with every root in the open unit disc.
Erd\H{o}s, Herzog, and Piranian asked whether two roots can always be joined
inside $\{|f|<1\}$ by a curve of length less than $2$.  The problem remains
open.

Every monic trinomial $z^n+az^m+b$, $1\le m<n$, with all zeros in the open
unit disc has every origin-to-zero segment inside $\{|f|<1\}$.  The middle
coefficient $a$ is unrestricted: the root equation eliminates it before any
absolute value is taken, and Vieta supplies $\|b\|<1$.  Lean checks the
radial inequalities and the length budget; concatenating the two segments is
ordinary.  Four or more terms destroy the same prescribed spokes: an exact
sextic family keeps every root inside the disc while the spoke to one root
leaves $\{|f|<1\}$.

The strongest parent-metric statement that applies to arbitrary geometry is
the low-critical regime $\mu\le13/25$: two distinct roots of a squarefree
monic $f$ are then joined inside $\{|f|<1\}$ by a curve of length strictly
below $2$.  The proof is ordinary analysis closed by an exact rational
certificate, replayable from the repository checker; it is not Lean-checked.
Removing the threshold $\mu$ yields an unconditional constant-factor theorem:
two zero occurrences are joined inside $\{|f|\le2\mu\}$ by a path of length
at most $(71/10)\rho$, $\rho=\mu^{1/n}$.  If the roots lie in the unit disc
and $\mu\le1/2$, the same construction lies in $\{|f|<1\}$ with length at
most $5.7$.  First-merge arity and component-capacity cutoffs reach the
target constant $2$ only as sufficient implications under $\mu\le1/2$; they
do not cover the residual $\mu>13/25$, and low first-merge arity does not
force a capacity gap.

A separated critical value gives the parent conclusion in every degree
$n\ge3$ once the other critical values lie outside a disk of radius $4/3$
about a real centre.  The older coefficientwise cutoffs $S=4,3,2$ are
superseded.  Collinear roots remain a complete sharp family.  No covering
disjunction of critical-value separation two against first-merge arity or
capacity holds: the cubic $z^3+(3/100)z-3/4$ has all roots inside,
$\mu>13/25$, and neither critical value separated by two.  The one-root
constant $\Gamma(1/4)^2/(2\sqrt{\pi})$ is likewise false.  No
literature-priority claim is made.
\end{abstract}"""
    text = text[:i0] + new_abs + text[i1 + len(old_abs_close) :]

    trinomial_section = r"""
\section{Monic trinomials, in every degree}
\label{sec:trinomial}

The cleanest proved all-degree connector that actually reaches length strictly
below $2$ inside $\{|f|<1\}$ is a complete coefficient family, not a constant
multiple of the target.

\begin{theorem}[all-degree monic trinomials]
\label{res:trinomial-all-degree}
Let $1\le m<n$ and
\[
 f(z)=z^n+az^m+b,
\]
with every zero in the open unit disc.  For any zero $\zeta$, the entire
segment $[0,\zeta]$ lies in $\{|f|<1\}$.  Distinct zeros $\zeta_1,\zeta_2$
are therefore joined by the broken line $\zeta_1\to0\to\zeta_2$ of length
$\|\zeta_1\|+\|\zeta_2\|<2$ inside the open unit lemniscate.
\end{theorem}

\begin{proof}
The coefficient $a$ never appears after the first identity.  If
$\zeta^n+a\zeta^m+b=0$, then for every scalar $t$,
\[
 f(t\zeta)=b(1-t^m)+\zeta^n(t^n-t^m).
\]
On $0\le t\le1$ the second difference $t^m-t^n$ is nonnegative.  Vieta and
the root hypothesis give $\|b\|<1$, and $\|\zeta\|<1$, so
\[
 \|f(t\zeta)\|\le\|b\|(1-t^m)+\|\zeta\|^n(t^m-t^n)<1-t^n\le1,
\]
with a strict inequality for $t<1$, while $t=1$ is a zero.  The length bound
is then immediate.  Lean checks the radial inequality, the Vieta step, and
the sum-of-norms budget as
\pdecl{trinomial\_erdos1041\_conclusion}; concatenating the two segments is
ordinary.
\end{proof}

The same cancellation identity fails as soon as two intermediate modes are
active.

\begin{proposition}[prescribed-spoke guardrail]
\label{res:sextic-spoke}
There exist $r\in(0,1)$ for which every zero of
\[
 f_r(z)=z^6+\tfrac15 r^2 z^4-\tfrac15 r^4 z^2-r^6
\]
lies in the open unit disc, yet the radial spoke from the origin to the zero
$r$ leaves $\{|f_r|<1\}$.
\end{proposition}

\noindent Lean checks this as \pdecl{sextic\_guardrail}.  It is not a
counterexample to Erd\H{o}s~\#1041: only the prescribed radial construction
fails.

"""

    text = sub(
        text,
        r"\statusboundary" + "\n\n" + r"\subsection*{Main results at a glance}",
        r"\statusboundary" + "\n" + trinomial_section + r"\subsection*{Main results at a glance}",
        "statusboundary insert",
    )

    old_table_lead = r"""\textbf{Sharp collinear family} &
The conjecture holds in every degree for collinear roots, with the sharp
Chebyshev constant.  \textsc{Checked kernels; ordinary affine transport.} \\
\addlinespace
\textbf{Global constant-factor theorem} &
For arbitrary monic $f$, two zero occurrences are joined in
$\{|f|\le2\mu\}$ by a path of length at most
$(71/10)\mu^{1/n}$.  For unit-disc roots and $\mu\le1/2$, the path lies in
$\{|f|<1\}$ and has length at most $5.7$.
\textsc{Ordinary exact proof.} \\
\addlinespace
\textbf{Parent-theorem regimes} &
The target constant $2$ holds when $\mu\le1/2$ and the first-merge component
has at least $17$ roots, or under an explicit arity-dependent
component-capacity defect bound.  \textsc{Ordinary exact proof.} \\
\addlinespace
\textbf{Critical-value separation regime} &
If a simple critical point $c$ with $v=f(c)\ne0$ has every other critical
point $d$ at normalised distance $|1-f(d)/v|\ge S>1$, two roots are joined
inside $\{|f|\le|v|\}$ by a path of length below $2|v|^{1/n}$ whenever
$(1+S)^{2/n}\log(S/(S-1))<1$.  The exact regimes are $S=4$ for $n\ge3$,
$S=3$ for $n\ge4$, and $S=2$ for $n\ge6$, and each cutoff is the first degree
at which its inequality holds.  \textsc{Ordinary exact proof; Lean checks the
degree monotonicity, the three thresholds, and the squared-length consumer.} \\"""

    new_table_lead = r"""\textbf{All-degree monic trinomials} &
Every origin-to-zero segment of $z^n+az^m+b$ lies in $\{|f|<1\}$, with $a$
unrestricted.  \textsc{Lean-checked radial and metric inequalities; ordinary
concatenation.} \\
\addlinespace
\textbf{Sharp collinear family} &
The conjecture holds in every degree for collinear roots, with the sharp
Chebyshev constant.  \textsc{Checked kernels; ordinary affine transport.} \\
\addlinespace
\textbf{Low-critical parent regime} &
If $\mu\le13/25$, two distinct roots of a squarefree monic $f$ are joined
inside $\{|f|<1\}$ by a curve of length strictly below $2$.
\textsc{Ordinary exact proof; replayable rational certificate; not Lean
checked.} \\
\addlinespace
\textbf{Global constant-factor theorem} &
For arbitrary monic $f$, two zero occurrences are joined in
$\{|f|\le2\mu\}$ by a path of length at most
$(71/10)\mu^{1/n}$.  For unit-disc roots and $\mu\le1/2$, the path lies in
$\{|f|<1\}$ and has length at most $5.7$.
\textsc{Ordinary exact proof.} \\
\addlinespace
\textbf{Parent-theorem regimes under $\mu\le1/2$} &
The target constant $2$ holds when $\mu\le1/2$ and the first-merge component
has at least $17$ roots, or under an explicit arity-dependent
component-capacity defect bound.  These are sufficient implications, not a
cover of $\mu>13/25$.  \textsc{Ordinary exact proof.} \\
\addlinespace
\textbf{Critical-value separation regime} &
A disk-family hypothesis on the critical spectrum gives the parent constant
$2$ in every degree $n\ge3$ once the other critical values lie outside a
disk of radius $4/3$ about a real centre.  The limiting cutoff is
$\coth1$.  The older coefficientwise cutoffs $S=4,3,2$ are superseded.
\textsc{Ordinary exact proof; Lean checks the uniform $4/3$ kernel.} \\"""

    text = sub(text, old_table_lead, new_table_lead, "glance table lead")

    old_boundary_row = r"""\textbf{Current boundary} &
The general problem is still open.  A counterexample in the
$\mu\le1/2$ branch must have first-merge arity at most $16$ and lie above the
corresponding capacity-defect cutoff; the high-critical branch also remains. \\"""

    new_boundary_row = r"""\textbf{Exact covering obstructions} &
The cubic $z^3+(3/100)z-3/4$ has $\mu>13/25$ and no critical value separated
by two.  First-merge arity two can coexist with normalised capacity one.
The one-root constant $\Gamma(1/4)^2/(2\sqrt{\pi})$ fails on
$z^8-(3/2)z$.  None of these is a counterexample to the parent problem.
\textsc{Ordinary exact proofs; Lean-checked rational cores.} \\
\addlinespace
\textbf{Current boundary} &
The general problem is still open.  Inside $\mu\le1/2$, a counterexample
must have first-merge arity at most $16$ and lie above the corresponding
capacity-defect cutoff; those implications do not cover $\mu>13/25$.  The
high-critical branch also remains. \\"""

    text = sub(text, old_boundary_row, new_boundary_row, "boundary row")

    old_cf_proof = r"""\begin{proof}[Proof architecture]
Choose a critical point at level $\mu$ and a component at a regular level
$t\in[\mu,\lambda\mu]$ that contains the corresponding first merge.  If a
regular component $C'$ at level $\sigma$ contains $k'$ roots, winding and
Cauchy--Schwarz give the local perimeter estimate
\[
 \mathcal H^1(\partial C')^2
 \le2\pi k'\,\sigma\,\frac{d}{d\sigma}
      \operatorname{Area}(K_\sigma\cap C').         \tag{CF1}
\]
P\'olya's area--capacity inequality
$\operatorname{Area}(K_T)\le\pi T^{2/n}$ then selects $t$ with a
degree-free boundary-length bound.

For an argument avoiding the finitely many critical-value rays, lift the
radial value segment from each root to $\partial C_t$.  Split each lift at
level $r\mu$.  Koebe distortion controls the low pieces.  The exact
precritical conformal-radius energy inequality
\[
 \sum_i\frac{\mu^2}{|f'(z_i)|^2}\le\rho^2          \tag{CF2}
\]
aggregates those pieces without paying once per root.  Coarea and~(CF1)
control the high pieces on average over the argument.  Choose one argument
realising that average, order the lift endpoints cyclically on
$\partial C_t$, and use the shortest adjacent boundary arc.  Averaging the
two lifts and the boundary arcs over the $k$ adjacent pairs gives~(CF).
The strict unit-sublevel statement chooses the regular level below the top of
the window when $\lambda\mu\le1$.
\end{proof}"""

    new_cf_proof = r"""\begin{proof}
Write $K_t=\{|f|\le t\}$, $C_T$ for the component of $K_T$ containing a
minimising critical point, and $A(\sigma)=\operatorname{Area}(K_\sigma\cap C_T)$.
Degree two is the root segment of length $2\rho$ inside $K_\mu$; assume
$n\ge3$.

If a regular component $C'$ of $K_\sigma\cap C_T$ holds $k'$ roots, then
$|dz|=\sigma\,d\varphi/|f'|$ on $\partial C'$ and $\int d\varphi=2\pi k'$.
Cauchy--Schwarz and coarea give
\[
 \mathcal H^1(\partial C')^2
 \le2\pi k'\,\sigma A'(\sigma).                     \tag{CF1}
\]
P\'olya's inequality $A(T)\le\pi T^{2/n}$ and the change of measure
$d\sigma/\sigma$ on $[\mu,T]$, $T=\lambda\mu$, produce a non-critical level
$t\in[\mu,T]$ with $t A'(t)\le\pi T^{2/n}/\log\lambda$.  The component
$C_t\subseteq C_T$ still holds $k\ge2$ roots, and
\[
 \mathcal H^1(\partial C_t)
 \le\pi\sqrt{2k/\log\lambda}\,T^{1/n}.
\]
The level $t$ is chosen from the mean of $\sigma A'(\sigma)$ \emph{before}
any path is assembled.  That is the only device that removes the logarithmic
divergence of $A'$ at a critical level.

For arguments avoiding the finitely many critical-value rays, each root in
$C_t$ lifts along a value-ray to $\partial C_t$.  Split every lift at level
$r\mu$.  On a one-root lobe the inverse of $f/\mu$ is univalent, so Koebe
distortion bounds the low pieces pointwise; the precritical identity
\[
 \sum_i\frac{\mu^2}{|f'(z_i)|^2}\le\rho^2          \tag{CF2}
\]
then aggregates them by Cauchy--Schwarz, paying $\sqrt{2/k}$ rather than
once per root.  Coarea and~(CF1) bound the high pieces only after averaging
in the argument.  Choose one argument realising that average, order the lift
endpoints cyclically on $\partial C_t$, and hop along the shortest adjacent
boundary arc.  Averaging the two lifts and the $k$ arcs over adjacent pairs
gives~(CF).  When $\lambda\mu\le1$ the same mean-value choice may be taken
strictly below the top of the window, so the path lies in $\{|f|<1\}$.
\end{proof}"""

    text = sub(text, old_cf_proof, new_cf_proof, "71/10 proof")

    old_cf_close = r"""These statements are complete ordinary analytic proofs.  They are not Lean
theorems and make no literature-priority claim.  Their full constant
certificates, component-capacity tables, and local proofs are in
\path{ErdosProblems/Erdos1041/UnconditionalConstantFactorBound.md}; the
P\'olya input is the global area--capacity inequality, not the local
winding--coarea estimate, reciprocal-derivative aggregation, or assembled
path theorem.  The unrestricted constant $2$ and the high-critical or
low-arity/high-capacity residual cells remain open."""

    new_cf_close = r"""These statements are complete ordinary analytic proofs.  They are not Lean
theorems and make no literature-priority claim.  Their full constant
certificates, component-capacity tables, and local proofs are in
\path{ErdosProblems/Erdos1041/UnconditionalConstantFactorBound.md}; the
P\'olya input is the global area--capacity inequality, not the local
winding--coarea estimate, reciprocal-derivative aggregation, or assembled
path theorem.

\begin{theorem}[low-critical parent regime]
\label{res:low-critical-thirteen-twentyfifths}
Let $f$ be squarefree and monic of degree $n\ge2$, and let $\mu$ be its least
critical-value modulus.  If $\mu\le13/25$, then two distinct roots are joined
inside $\{|f|<1\}$ by a rectifiable curve of length strictly less than $2$.
\end{theorem}

The proof is the comparison ODE of the earlier low-critical notes, with the
arity floor taken as the maximum of the COVER floor, the ordered profile, the
packing floor, and a circle-slice dual floor.  The dual table is generated at
runtime by
\path{ErdosProblems/Erdos1041/scripts/check_erdos1041_angular_budget_closure.py};
full mode returns
$X_{\mathrm{cert}}=635762889599/10^{12}$ and $(13/25)\exp(X_{\mathrm{cert}})<1$.
There is no separate static $126$-row export: the checker is the certificate.
The argument is not Lean-checked.  Details live in
\path{ErdosProblems/Erdos1041/AngularBudgetLowCriticalClosure.md}.

The arity and capacity cutoffs of
Theorem~\ref{res:first-merge-capacity-closures} are sufficient implications
inside $\mu\le1/2$.  They are not a cover of the complementary cell
$13/25<\mu<1$.  Low first-merge arity does not force a capacity gap: the
cubic $z^3-(3/400)z-3/32$ has all roots in the open disc, $\mu<1/2$, first-merge
arity two, and normalised ancestor capacity one at level $2\mu$.  The cubic
$z^3+(3/100)z-3/4$ has $\mu>13/25$ and no critical value separated by two.
Neither example is a counterexample to Erd\H{o}s~\#1041; both are trinomials.
The unrestricted constant $2$ and the high-critical residual remain open."""

    text = sub(text, old_cf_close, new_cf_close, "13/25 and covering")

    old_sep_cor = r"""\begin{corollary}[the exact convenient regimes]\label{res:critical-value-thresholds}
Inequality~\eqref{eq:separation-threshold} holds for $S=4$ in every degree
$n\ge3$, for $S=3$ in every degree $n\ge4$, and for $S=2$ in every degree
$n\ge6$.  Each cutoff is the first degree at which its inequality holds: the
squared coefficient of \eqref{eq:separation-threshold} is $1.43841$ at
$(n,S)=(2,4)$, $1.02171$ at $(3,3)$, and $1.07566$ at $(5,2)$, while at
$(6,2)$ it is $0.99969$.
\end{corollary}

\begin{corollary}[a parent-problem regime]\label{res:separation-parent}
Let $f$ be monic with all roots in the open unit disc, let $c$ be a simple
critical point with $v=f(c)\ne0$, and suppose $|1-f(d)/v|\ge4$ for every other
critical point $d$.  If $n\ge3$ then Erd\H{o}s Problem~\#1041 holds for $f$.
\end{corollary}

\noindent The separation hypothesis makes $c$ the unique critical point of
minimum modulus, the Fekete chain gives $|v|<1$, and
Theorem~\ref{res:critical-value-separation} with $S=4$ places a connector of
length below $2$ inside $\{|f|<1\}$."""

    new_sep_cor = r"""\begin{corollary}[disk-family uniform radius]\label{res:critical-value-thresholds}
A strictly stronger disk-family theorem, proved in
\path{ErdosProblems/Erdos1041/DiskFamilyCriticalValueSeparation.md}, replaces
the coefficientwise logarithm $\log(S/(S-1))$ by the Bergman segment identity
\[
 \Bigl(\int_{-q}^{q}|h|\Bigr)^2
 \le\frac4\pi\operatorname{artanh}(q^2)\,\|h\|_{A^2}^2
\]
and yields a uniform radius $S=4/3$ in every degree $n\ge3$, at every real
centre.  The limiting cutoff of the method is $\coth1$.  The older
coefficientwise regimes $S=4$ ($n\ge3$), $S=3$ ($n\ge4$), and $S=2$ ($n\ge6$)
remain valid and are superseded.  A proposed all-degree cutoff $S=3/2$ for
the older bound is strictly weaker than $4/3$ and is not used.
\end{corollary}

\begin{corollary}[a parent-problem regime]\label{res:separation-parent}
Let $f$ be monic of degree $n\ge3$ with all roots in the open unit disc, and
let $c$ be a simple critical point with $v=f(c)\ne0$.  If some real centre
$w_0\in[0,1]$ admits a radius $S\ge4/3$ such that $|f(d)/v-w_0|\ge S$ for
every other critical point $d$, then Erd\H{o}s Problem~\#1041 holds for $f$.
\end{corollary}

\noindent The Fekete chain gives $|v|<1$ at a minimum-modulus critical point.
The hypothesis is sufficient, not necessary: it does not assert that some
critical value is always separated by two, and the cubic
$z^3+(3/100)z-3/4$ shows that no such covering statement is true."""

    text = sub(text, old_sep_cor, new_sep_cor, "separation corollaries")

    old_sep_bdry = r"""the three
regimes of Corollary~\ref{res:critical-value-thresholds} hold exactly
(\pdecl{firstMerge\_exact\_convenient\_thresholds})."""

    new_sep_bdry = r"""the older
three coefficientwise regimes hold exactly
(\pdecl{firstMerge\_exact\_convenient\_thresholds}),
while the live uniform radius $4/3$ is checked in
\path{ErdosProblems/Erdos1041/DiskFamilyCriticalValueSeparation.lean}."""

    text = sub(text, old_sep_bdry, new_sep_bdry, "separation boundary lean")

    obstruction_section = r"""
\section{Three exact covering obstructions}
\label{sec:exact-obstructions}

None of the following is a counterexample to Erd\H{o}s~\#1041.  Each kills a
covering reading of a sufficient regime.  Rational cores are checked in
\path{ErdosProblems/Erdos1041/RevisionR2ExactCores.lean}; the ordinary
arguments are in
\path{ErdosProblems/Erdos1041/ExactObstructionsR2.md}.

\begin{proposition}[no separation-or covering]
\label{res:sep-or-false}
Let $f(z)=z^3+(3/100)z-3/4$.  Every root lies in the open unit disc, both
critical points are simple, the critical values lie on distinct positive
rays, $\mu>13/25$, and
\[
 \bigl|1-f(c_-)/f(c_+)\bigr|<2/375<2.
\]
\end{proposition}

\begin{proposition}[one-root gamma bound is false]
\label{res:one-root-gamma-false}
Let $p(z)=z^8-(3/2)z$ and let $C$ be the component of $\{|p|\le1\}$
containing the origin.  Then $C$ contains exactly one zero and a
neighbourhood of the closed disc of radius $5/8$, so
$\mathcal H^1(\partial C)>5\pi/4$.  The constant
$\Gamma(1/4)^2/(2\sqrt{\pi})$ is at most $(\pi/2)(1+\sqrt2)<5\pi/4$.
\end{proposition}

A degree-uniform one-root perimeter constant, if one exists, must be at
least $2\pi$, by the family $z^N-z$.  The constant-factor theorem of
Section~\ref{sec:constant-factor} does not use that conjecture and is
unaffected.

\begin{proposition}[arity does not force a capacity gap]
\label{res:arity-not-capacity}
Let $g(z)=z^3-(3/400)z-3/32$.  All roots lie in the open unit disc,
$\mu=187/2000\le1/2$, the first-merge arity is $k_0=2$, and the ancestor
component at level $2\mu$ has normalised capacity $1$.
\end{proposition}

"""

    text = sub(
        text,
        r"\section{The Newton value equation}\label{sec:newton}",
        obstruction_section + r"\section{The Newton value equation}\label{sec:newton}",
        "obstruction section",
    )

    old_ledger_cf = r"""Global constant-factor path &
\textsc{Ordinary exact proof; finite regression only.}  Two zero occurrences
admit a path of length at most $(71/10)\mu^{1/n}$ in $K_{2\mu}$; when
$\mu\le1/2$, the length is at most $5.7$ in $\{|f|<1\}$.  This result has no
Lean or independent-review claim. \\
\addlinespace
First-merge parent regimes &
\textsc{Ordinary exact proof.}  The target constant $2$ holds at
$\mu\le1/2$ for first-merge arity at least $17$, and under the explicit
arity-dependent component-capacity cutoffs of
Theorem~\ref{res:first-merge-capacity-closures}.  The complementary cells and
the high-critical branch remain open. \\"""

    new_ledger_cf = r"""All-degree monic trinomials &
\textsc{Lean-checked radial and metric inequalities.}  Every origin spoke of
$z^n+az^m+b$ lies in $\{|f|<1\}$.  Four-term prescribed spokes fail on an
exact sextic. \\
\addlinespace
Low-critical parent regime &
\textsc{Ordinary exact proof; replayable rational certificate.}  The
threshold $\mu\le13/25$ is closed by
\path{ErdosProblems/Erdos1041/scripts/check_erdos1041_angular_budget_closure.py}.
Not Lean-checked. \\
\addlinespace
Global constant-factor path &
\textsc{Ordinary exact proof; finite regression only.}  Two zero occurrences
admit a path of length at most $(71/10)\mu^{1/n}$ in $K_{2\mu}$; when
$\mu\le1/2$, the length is at most $5.7$ in $\{|f|<1\}$.  This result has no
Lean or independent-review claim. \\
\addlinespace
First-merge parent regimes &
\textsc{Ordinary exact proof.}  The target constant $2$ holds at
$\mu\le1/2$ for first-merge arity at least $17$, and under the explicit
arity-dependent component-capacity cutoffs of
Theorem~\ref{res:first-merge-capacity-closures}.  These implications do not
cover $\mu>13/25$, and low arity does not force a capacity gap. \\
\addlinespace
Disk-family separation &
\textsc{Ordinary exact proof; Lean-checked $4/3$ kernel.}  Uniform radius
$4/3$ in every degree $n\ge3$; limiting cutoff $\coth1$.  The older
cutoffs $S=4,3,2$ are superseded. \\
\addlinespace
Covering obstructions &
\textsc{Ordinary exact proofs; Lean-checked rational cores.}  No
separation-or covering, no one-root gamma bound, and no arity-to-capacity
implication.  None refutes the parent problem. \\"""

    text = sub(text, old_ledger_cf, new_ledger_cf, "evidence ledger")

    old_decl = r"""This manuscript is authored exposition, not Lean proof authority.  Its
strongest unrestricted-geometry paper theorem is the ordinary analytic
constant-factor path theorem, together with the first-merge arity and
component-capacity regimes that reach the parent constant $2$.  Lean does not
formalise their coarea, univalent-map, component-capacity, or path-assembly
arguments."""

    new_decl = r"""This manuscript is authored exposition, not Lean proof authority.  Its
strongest complete coefficient family is the all-degree monic trinomial
theorem.  Its strongest unrestricted-geometry parent regime is the ordinary
$\mu\le13/25$ theorem.  Its strongest unrestricted-geometry weakening with no
threshold on $\mu$ remains the constant-factor path of length
$(71/10)\rho$ in $K_{2\mu}$.  First-merge arity and component-capacity
regimes reach the parent constant $2$ only as sufficient implications under
$\mu\le1/2$.  Lean does not formalise the coarea, univalent-map,
component-capacity, ODE, or path-assembly arguments of the last three."""

    text = sub(text, old_decl, new_decl, "declarations")

    PAPER.write_text(text)
    print("paper patched", PAPER)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
