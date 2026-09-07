# Crossing shadows obstruct laminar ownership doubling

Status: exact finite abstract counterexample, 2026-08-20.  This note concerns
the proposed set-valued shadow-label proof of fixed-rank stabilization.  It
does not disprove normalization by a richer physical-bank or cocycle state.

Put

\[
 \lambda_r=2^{2-r}.
\]

The proposed abstract rule assigns every complete rank-\(r\) front a label
set of measure \(\lambda_r\).  Opening a component leaves its front parked as
a shadow of the whole parent label and gives its later complete children
disjoint subsets of that label.  Two disjoint equal-rank fronts carry left by
unioning their labels.  The hoped-for conclusion was that equal-rank fronts
remain disjoint: a descendant subtree has contracted label mass, so a return
to its ancestor's rank would have to acquire a disjoint branch and thereby
double ownership.

The conclusion fails because union with an external branch does not preserve
laminarity relative to a parked ancestor shadow.

## 1. The seven-quantum crossing

Take rank \(r=4\).  Realise label measure using sixteen equal quanta.  Let

\[
\begin{array}{c|c|c}
\text{front}&\text{rank}&\text{label set}\\ \hline
A&4&\{0,1,2,3\}\\
a&6&\{0\}\\
B&6&\{4\}\\
C&5&\{5,6\}.
\end{array}                                         \tag{1}
\]

The parked ancestor \(A\) has mass \(4/16=\lambda_4\).  Its internal child
\(a\) has mass \(1/16=\lambda_6\), exactly one quarter of the parent mass.
This satisfies the proposed strict contraction because

\[
 \frac14<\frac{32771}{131068}.                       \tag{2}
\]

The external fronts \(B\) and \(C\) are disjoint from \(A\) and have the
correct masses \(\lambda_6=1/16\) and \(\lambda_5=1/8\).

First carry the two disjoint rank-six fronts:

\[
 X=a\cup B=\{0,4\},\qquad \operatorname{rank}(X)=5. \tag{3}
\]

Then carry \(X\) with the disjoint external rank-five front \(C\):

\[
 F=X\cup C=\{0,4,5,6\},\qquad
 \operatorname{rank}(F)=4.                          \tag{4}
\]

Both carries obey the proposed disjoint-union rule and have exactly the
required output masses.  But the returned front \(F\) crosses the parked
ancestor shadow:

\[
 A\cap F=\{0\},
 \qquad A\not\subseteq F,
 \qquad F\not\subseteq A.                           \tag{5}
\]

Thus the active shadow family is no longer laminar.  In particular, the two
rank-four fronts are neither disjoint nor ancestor/descendant.

If one nevertheless tries to collide them by set union, their available
ownership mass is only

\[
 \mu(A\cup F)=\frac7{16}
 <\frac12=\lambda_3.                                \tag{6}
\]

The claimed ownership doubling therefore cannot certify the rank-three
output.  If collision is restricted to disjoint labels, the state instead
contains an unresolved duplicate rank-four front.

## 2. Exact rollback does not restore doubling

Closing \(A\) cannot merely delete \(a\), because \(a\)'s label is embedded
in \(F\).  Exact rollback must first reverse the carry \(X+C\), then reverse
\(a+B\), and only then remove \(a\) while restoring the closed component
\(A\).  This also destroys the returned front \(F\).  No disjoint rank-four
collision, and hence no ownership-doubling event, remains after rollback.

Reopening \(A\) and replaying the two enabled external carries recreates the
same crossing state.  Whether such replay is fair depends on the precise
fairness convention, but fairness cannot repair the local assertion used in
the proof: equal-rank fronts are not forced to be disjoint, and rollback does
not turn the crossing return into a disjoint lower-rank collision.

## 3. Minimal repair

One of two structural changes is necessary:

1. consume or freeze a parked ancestor shadow as soon as one of its
   descendants enters an external collision, so the crossing shadow and the
   mixed descendant front are never simultaneously collision-eligible; or
2. replace ordinary set-valued ownership by a multiplicity- or cocycle-valued
   object which records that the same ancestral quantum occurs once in the
   parked front and again in a physically separate descendant summand.

The first choice must still explain how the frozen atom becomes final and how
its physical reserve is discharged.  The second must supply a new boundedness
law, because ordinary union measure no longer bounds the number of returns.

## 4. Reproduction

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/laminar_shadow_collision_counterexample_audit.py

The script realises (1)--(6) as finite sets, checks every rank mass and
disjoint input carry exactly, verifies the strict \(1/4\) contraction, and
reports the rollback dependency.  The counterexample is finite and does not
depend on numerical search.
