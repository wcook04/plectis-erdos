# Reversible laminar packets and fixed-rank stabilization

This note isolates the combinatorial content of the proposed reversible
packet normalization. Physical values do not occur in the abstract theorem.
The mass below is a shadow ownership label.

For a front at rank \(r\), put
\[
 \lambda_r=2^{2-r},
 \qquad 2\lambda_r=\lambda_{r-1}.                  \tag{1}
\]
Opening a complete packet produces finitely many children at strictly later
ranks. Their total shadow mass is less than
\(\rho\lambda_r\), where \(\rho<1/2\). Two exposed fronts at the same rank
may collide only when their ownership is disjoint. Their descendant forests
are rolled back and the fronts are replaced by their union at rank \(r-1\).

These statements are almost, but not quite, a stabilization theorem. One
additional state axiom is essential.

## 1. The weak rules permit an infinite replay

Fix a target rank \(R\) and normalize \(\lambda_R=1\). A packet at rank
\(R-3\) then has mass \(8\). Take \(\rho=3/8\). Its finite opened forest
may contain two rank-\(R\) fronts, of total mass \(2\), because
\[
 2<\frac38\,8=3.                                   \tag{2}
\]
The two fronts collide and rewrite rank \(R\), producing one rank-\(R-1\)
front of mass \(2\).

If the reversible semantics now permits the same complete rank-\(R-3\)
ownership epoch to be restored and reopened, the two-step schedule
\[
 \text{open the epoch},\qquad
 \text{merge its two rank-\(R\) fronts}             \tag{3}
\]
can repeat forever. Every child rank is later than its parent, the child set
is finite, the contraction is strict with \(\rho<1/2\), every merge uses
disjoint fronts, and the alternating schedule is fair among its enabled
operations. Yet rank \(R\) is rewritten once per cycle.

This is not a numerical counterexample to the Mersenne identities. It is a
counterexample to treating “reversible” as permission to replay an unchanged
shadow label. Contraction controls the size of one opening; it does not count
how often that opening is replayed.

## 2. The missing axiom: linear ownership epochs

The required extra rule is:

> **Linear epoch axiom.** A complete ownership epoch may be opened at most
> once. Rolling back its descendant forest is allowed only when its exposed
> front participates in a collision. That collision consumes both epochs
> and creates a fresh epoch whose shadow ownership is their disjoint union.
> A consumed epoch is never restored with the same label. Any shadow mass
> which later returns through an opening has crossed one additional opening
> level.

Equivalently, rollback is reversible in physical algebra but monotone in the
shadow event history. It may undo a chosen expansion; it may not erase the
fact that the ownership epoch was already spent.

This is stronger than ordinary scheduler fairness. Fairness says that a live
operation is eventually processed. It does not forbid processing the same
restored operation infinitely often.

The word “laminar” must also refer to the live ownership state, not merely to
each packet's private descendant tree. A union of descendants from two trees
can cross their historical ancestor sets. One may handle this either by
recutting those ancestors before the union or by retaining a monotone
ownership DAG. The proof below needs disjoint live ownership and no cloning;
it does not need all retired historical sets to remain a laminar family.

## 3. Abstract stabilization theorem

Consider finitely many root labels of total shadow mass \(M_0<\infty\).
Assume:

1. a rank-\(r\) front has shadow mass \(\lambda_r\);
2. opening is finite, moves every child to a later rank, and passes less than
   a \(\rho<1\) fraction of the epoch's label into its descendant forest;
3. equal-rank collision is possible only for disjoint ownership and replaces
   the two epochs by their union one rank to the left;
4. shadow labels are never cloned, and the linear epoch axiom holds.

Then every fixed rank changes only finitely many times under every legal
schedule. The stated hypothesis \(\rho<1/2\) is stronger than the contraction
needed in this theorem, but it also ensures that opening a rank-\(r-1\)
packet cannot by itself create even one rank-\(r\) front.

### Proof

Give a piece of shadow ownership depth \(k\) after it has passed through
\(k\) consumptive openings. Merges take disjoint unions and do not decrease
depth. Let \(M_{\geq k}\) be the total mass of ownership pieces of depth at
least \(k\). Induction on \(k\) gives
\[
 M_{\geq k}\leq \rho^kM_0.                         \tag{4}
\]
Indeed, each opening passes less than a \(\rho\) fraction of its input label
to the next depth, while merges merely regroup existing pieces.

Finite branching and linear epoch consumption imply that only finitely many
packet events can involve ownership of depth below a fixed \(k\). This is a
finite induction on opening depth: there are finitely many roots; each epoch
opens once into finitely many children; and collisions can form only finitely
many disjoint unions of the finitely many epochs already present at those
depths.

Suppose rank \(R\) were rewritten infinitely often. A collision there needs
two disjoint rank-\(R\) fronts, hence shadow mass
\[
 2\lambda_R=\lambda_{R-1}.                         \tag{5}
\]
For every fixed \(k\), only finitely many of those events can use ownership
of depth below \(k\). Infinitely many later events would therefore have to
be funded entirely by depth-at-least-\(k\) ownership. Choose \(k\) so large
that
\[
 \rho^kM_0<2\lambda_R.                             \tag{6}
\]
Equations (4)--(6) are incompatible. Hence rank-\(R\) collisions are finite.

The same argument with \(\lambda_R\), rather than \(2\lambda_R\), shows that
only finitely many new rank-\(R\) fronts can be created. A rollback affecting
rank \(R\) is attached to a collision of an ancestor front at a rank at most
\(R\); applying the preceding argument to the finitely many such ranks shows
that these rollbacks are finite as well. Thus the entire rank-\(R\) state
eventually stabilizes. \(\square\)

The shadow mass is not a proxy for physical Mersenne value. It counts how
much nonduplicated ownership has crossed how many consumptive opening
barriers.

## 4. The actual root fails the disjoint-front hypothesis

The anchored system rooted at \(M(2,3)\) satisfies the metric assumptions:

* a complete front at rank \(r\) has shadow mass
  \(\lambda_r=2^{2-r}\);
* equal-rank carrying preserves shadow mass;
* exact residual reencoding has finitely many children at later ranks;
* the exceptional first opening has ratio
  \[
   \rho_{\rm first}=\frac{755}{2048}<0.369<\frac12, \tag{7}
  \]
  and every later complete component has ratio below
  \[
   \rho_{\rm later}
   =\frac{32771}{131068}<0.251.                     \tag{8}
  \]

It does not satisfy the disjoint-front hypothesis. The exact root genealogy
first exposes provisional fronts
\[
 7,8,9,10,12.
\]
Immediately before the rank-12 component \(A\) is opened, the external
forest has load \(E\) with
\[
 0.9363\lambda_{12}<E<0.9387\lambda_{12}.
\]
Opening \(A\) creates descendants \(D\) of load between
\(0.2498\lambda_{12}\) and \(0.2499\lambda_{12}\). Hence
\[
 1.1861\lambda_{12}
 <E+L(D)
 <1.1885\lambda_{12}.                              \tag{9}
\]
Normalizing \(E\sqcup D\) therefore exposes rank 12 again. The challenger
contains descendants of \(A\) and external ownership. It overlaps \(A\)
without being contained in it.

This is the first cross-grafting failure. Rolling back \(A\) deletes the
descendant part of the challenger; the remaining external load is below
\(\lambda_{12}\), so the challenger disappears. Reopening \(A\) recreates
the same state. Linear epoch consumption can forbid the replay, but then the
local laminar machine is stuck rather than normalized. Thus the abstract
theorem is sound, while the actual root system fails one of its hypotheses.

## 5. Full-bank predecessor recut escapes the overlap

The overlap has an exact nonlaminar escape. Let \(X\) be any complete
anchor-two packet with front rank \(r\geq4\). Its distortion is greater than
one, so
\[
 X>\frac{\lambda_r}{3}.
\]
Moreover
\[
 \frac{\lambda_r}{3}
 \geq w_r+M(r-1,r).                                \tag{10}
\]
To check (10), put \(x=2^{r-1}\geq8\) and clear positive denominators. The
remaining inequality is
\[
 \frac{x^2}{2}-3x+1\geq0.
\]
Therefore the full reserve of \(X\) satisfies
\[
 X-w_r>M(r-1,r).                                   \tag{11}
\]

Now suppose opening a parked rank-\(r\) atom produces an overlapping complete
challenger \(F\) at the same rank. The physical summands are the parked atom
\(w_r\) and the complete challenger \(F\); one must not add the old complete
packet, which would double-count its descendants. By (11),
\[
 w_r+F>2w_r+M(r-1,r)=w_{r-1}.                      \tag{12}
\]
The universal anchor-two distortion bound gives \(F<2w_r\), so
\[
 w_r+F<3w_r<2w_{r-1}.                              \tag{13}
\]
Thus a global recut of exactly these physical summands emits one
\(w_{r-1}\) and leaves a positive residual smaller than \(w_{r-1}\). The
residual has odd denominator and can be reencoded at a common Mersenne height.

At the first root overlap, the scalar tail after the already exposed atoms
\(5,7,8,9,10\) is
\[
 V=\frac{508634}{806159805},
 \qquad w_{11}<V<2w_{11}.                          \tag{14}
\]
So the predecessor recut is exactly the observed rank 11.

## 6. A monotone visible-prefix invariant

The predecessor recut suggests a stronger stabilization mechanism than local
laminar rollback. Keep visible atoms as Boolean bits. Opening a reserve may
insert a new visible front; a disjoint collision performs an ordinary carry;
and an overlap cycle is resolved by (12), which replaces the parked rank-\(r\)
bit by a rank-\(r-1\) bit and a later residual. No operation may silently
delete a visible atom or move it right.

For a cutoff \(R\), define the dyadic event counter
\[
 C_R=\sum_{r=1}^R b_r2^{R-r},
 \qquad b_r\in\{0,1\}.                              \tag{15}
\]
This is a shadow counter, not the physical Mersenne value. Inserting a front
and normalizing a funded duplicate cascade is ordinary binary addition. An
overlap predecessor recut is the first step of that addition. If every such
cascade is funded through the first vacant predecessor rank, then every event
affecting ranks at most \(R\) strictly increases \(C_R\). Since
\[
 0\leq C_R\leq2^R-1,                               \tag{16}
\]
only finitely many such events can occur.

The funding qualification is essential. Let
\[
 P(r,2)=\frac{\lambda_r}{3}
\]
be the smallest complete anchor-two packet, and suppose the visible bits at
\(r,r-1,\ldots,r-k+1\) are already occupied. Carrying its challenger through
that run is possible exactly when
\[
 P(r,2)+\sum_{i=0}^{k-1}w_{r-i}>w_{r-k}.           \tag{17}
\]
The full-bank lemma proves (17) for \(k=1\), not for every \(k\).

In fact the worst-case capacity is exact:
\[
 \boxed{k_{\max}(r)=\left\lfloor\frac{r-2}{2}\right\rfloor.} \tag{18}
\]
Put \(m=r-k\) and
\[
 G_{m,r}=w_m-\sum_{n=m+1}^r w_n.
\]
Using \(w_n=\sum_{q\geq1}2^{-qn}\), the \(q=1\) contribution to \(G_{m,r}\)
is \(2^{-r}\). All contributions with \(q\geq2\) are positive, and their sum
is less than
\[
 \sum_{q\geq2}2^{-qm}
 =\frac{2^{-2m}}{1-2^{-m}}.                        \tag{19}
\]
If \(k\leq\lfloor(r-2)/2\rfloor\), then \(2m\geq r+2\), and \(m\geq3\)
gives
\[
 G_{m,r}
 <2^{-r}+\frac{2^{-r-2}}{1-2^{-m}}
 <\frac43\,2^{-r}=P(r,2).
\]
Thus (17) holds. At the next \(k\), one has \(2m=r\) when \(r\) is even
and \(2m=r+1\) when \(r\) is odd. The \(q=2\) contribution alone is greater
than
\[
 \frac23\,2^{-2m}\geq\frac13\,2^{-r}.
\]
Hence \(G_{m,r}>P(r,2)\), and the next carry fails. This proves (18) for
every \(r\geq4\).

At \(r=12\), the minimal packet passes (17) for \(k=1,\ldots,5\), but fails
at \(k=6\):
\[
\begin{aligned}
 P(12,2)+\sum_{i=0}^{4}w_{12-i}-w_7
  &=\frac{530622738299}{13180550289933312}>0,\\
 P(12,2)+\sum_{i=0}^{5}w_{12-i}-w_6
  &=-\frac{7817180893091}{92263852029533184}<0.
\end{aligned}                                      \tag{20}
\]
Thus one-step predecessor recutting does not yield an unconditional binary
counter theorem. A challenger at rank 12 facing occupied predecessors
\(11,10,9,8,7\) would need six carries and the minimal complete bank cannot
fund the last one. This is the suffix-capacity obstruction in packet
coordinates.

The first actual root overlap is safe for a sharper reason: rank 11 is a
hole, so only the first predecessor recut is needed. After taking \(w_{11}\),
the exact residual in (14) is
\[
 V-w_{11}=\frac{235013993}{1650209120835}
          <P(12,2).                                \tag{21}
\]
Hence that recut cannot regenerate a complete rank-12 challenger from its
own residual. The rank-12 cycle is genuinely closed.

The visible-prefix counter therefore becomes a theorem under the exact
additional condition:

> **Funded-hole condition.** Every exposed challenger meets a vacant
> predecessor before its available complete-bank reserve is exhausted.

Equivalently, (17) must hold through the first zero in the current visible
suffix. Under this condition, predecessor recuts are binary additions and
\(C_R\) proves fixed-prefix stabilization. Without it, the proposed invariant
stops at the same moving-hole wall as the earlier formulations.

The invariant is insensitive to how far right the residual is reencoded and
to the size of its integer coefficient. Those affect when a future bit is
inserted, not the monotonicity of the prefix counter.

## 7. Boundary of the result

The local linear-laminar theorem is conditional and the root violates its
disjointness condition at rank 12. The global predecessor recut repairs that
specific cycle because rank 11 is vacant and the remaining value excludes a
second rank-12 challenger.

This still does not prove the full Booleanization of \(M(2,3)\). One must
prove the funded-hole condition for every later generated challenger, or find
a reachable violation. After that, one must still implement the recut with
exact ownership, process every residual opening fairly, and show that physical
residual value tends to zero rather than remaining in unreleased banks.

## 8. Reproduction

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/reversible_laminar_stabilization_audit.py

The script exhibits the weak replay cycle, blocks same-epoch replay, checks
the abstract depth cutoff, verifies the exact root contraction constants,
checks the full-bank inequality, reproduces the rank-11 scalar recut, and
tests both sides of the rank-12 funded-run boundary. The general arguments
above are combinatorial and algebraic; the script is an adversarial semantics
receipt.
