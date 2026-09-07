# Removed passages and long-record destinations

These are preserved verbatim. They are not instructions to line-edit the co-primary long record.

## R6-E04 — res:low-critical-thirteen-twentyfifths, following proof discussion
AngularBudgetLowCriticalClosure.md, Theorem A'', Corollary B'', and §§1–5; implementation details remain there.
```tex
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


The next result removes the threshold on $\mu$ and allows a larger length
and sublevel.
```

## R6-E05 — res:first-merge-capacity-closures and res:minimal-hub-window
Long record: after the unconditional constant-factor proof, subsections “Component-sensitive refinements” and “Two-root persistence window”; preserve res:first-merge-capacity-closures and res:minimal-hub-window there.
```tex
The same estimate reaches the sharp target in explicit regions of the parent
problem.  Let $k_0$ be the number of roots in the component of $K_\mu$
containing the chosen minimising critical point.  Let $C$ be the corresponding
component of $K_{2\mu}$ and put
\[
 \kappa=\frac{\operatorname{cap}(\overline C)}{(2\mu)^{1/n}}.
\]
Thus $\kappa=e^{-\Sigma/n}$, where $\Sigma$ is the total exterior Green
defect of the roots excluded from $C$.

\begin{theorem}[first-merge arity and capacity closures]
\label{res:first-merge-capacity-closures}
Assume all roots lie in the open unit disc and $\mu\le1/2$.

\begin{enumerate}[label=\textup{(\roman*)},leftmargin=*]
\item If $k_0\ge17$, two distinct roots are joined inside $\{|f|<1\}$ by a
path of length strictly less than $2$.
\item Put
\[
 A=\frac{283}{3610},\qquad B=\frac{52029}{9100},\qquad
 \tau_k=\frac{\sqrt{2k}-A}{B}.
\]
If $\kappa\le\tau_{k_0}$, the same conclusion holds.  In particular,
$\kappa\le1/3$ suffices for every $k_0\ge2$, while at $k_0=16$ the rational
cutoff improves to $\kappa\le39/40$.
\end{enumerate}
\end{theorem}

The second part retains the component root count and replaces the global area
bound in~(CF1) by
$\operatorname{Area}(C)\le\pi\operatorname{cap}(\overline C)^2$.
Consequently a counterexample with $\mu\le1/2$ must have $k_0\le16$ and must
lie above its arity-dependent capacity cutoff.  Smaller critical levels give
stronger nested regions: $\mu\le1/4$ closes every $k_0\ge12$,
$\mu\le1/8$ closes every $k_0\ge10$, and the $\mu\le1/64$ calculation raises
the surviving $k_0=9$ capacity cutoff to $99/100$.

There is a complementary closure criterion that spends separation in the
critical spectrum instead of component capacity.  Suppose $f$ is squarefree and $c_*$ is the unique critical point attaining
$\mu$, and is simple.  Let $T_*>\mu$ be the supremum of the levels for which
the component born at $c_*$ contains exactly two roots.  Uniqueness, not
simplicity, puts $T_*$ at least the next distinct critical-value modulus.
The quartic $z^4-(4/15)z^3-(4/25)z^2+1/750$ has three simple critical points,
tied minima of modulus $1/750$, all roots inside the disc, and first nontrivial
component of degree three, so a simple minimum is not enough.

\begin{theorem}[minimal-hub spectral window]
\label{res:minimal-hub-window}
Under these hypotheses, two roots are joined by a path inside $K_\mu$ of
length at most
\[
 \Psi_n(T_*/\mu)\,\mu^{1/n},\qquad
 \Psi_n(x)=x^{1/n}
   \sqrt{2\log\frac{x+1}{x-1}}.                     \tag{SW}
\]
The function $\Psi_n$ is strictly decreasing on $(1,\infty)$.  Let
$x_n^*$ be the unique solution of $\Psi_n(x)=2$ for $n\ge3$.  If the roots
lie in a disk of radius $R$ and the second distinct critical-value modulus
$\nu_2$ satisfies $\nu_2/\mu>x_n^*$, then the path has length less than
$2R$ and proves the parent conclusion.  The first thresholds are
\[
 \begin{aligned}
 x_3^*&=1.6064943\ldots,&
 x_4^*&=1.4784372\ldots,\\
 x_5^*&=1.4289343\ldots,&
 x_{10}^*&=1.3598081\ldots .
 \end{aligned}
\]
and $x_n^*$ decreases to $\coth 1$, not to $1$.
\end{theorem}

Indeed, the two-root descent-arc estimate at any $t\in(\mu,T_*)$ is
\[
 \operatorname{len}(\Gamma)
 \le t^{1/n}\sqrt{2\log\frac{t+\mu}{t-\mu}},
 \qquad \Gamma\subset K_\mu.
\]
Writing $x=\coth u$ gives
$\Psi_n(x)^2=4u\coth(u)^{2/n}$ and proves strict decrease.  Taking the limit
$t\uparrow T_*$ gives~(SW); the Fekete--Vandermonde bound
$\mu\le R^n$ converts $\Psi_n(\nu_2/\mu)<2$ into the parent metric bound.
The same criterion is stable under the compositional pullback
$P((z-h)^q)$ after adjoining the hub value $|P(0)|$ to the critical spectrum.
The complete proof and threshold certificates are in
\path{ErdosProblems/Erdos1041/MinimalHubWindowJoin.md}.  This theorem is
silent at a multiple minimising critical point and makes no priority claim.

These statements are complete ordinary analytic proofs.  They are not Lean
theorems and make no literature-priority claim.  Their full constant
certificates, component-capacity tables, and local proofs are in
\path{ErdosProblems/Erdos1041/UnconditionalConstantFactorBound.md}; the
P\'olya input is the global area--capacity inequality, not the local
winding--coarea estimate, reciprocal-derivative aggregation, or assembled
path theorem.

The arity and capacity cutoffs of
Theorem~\ref{res:first-merge-capacity-closures} are sufficient implications
inside $\mu\le1/2$.  They are not a cover of the complementary cell
$13/25<\mu<1$.  Low first-merge arity does not force a capacity gap: the
cubic $z^3-(3/400)z-3/32$ has all roots in the open disc, $\mu<1/2$, first-merge
arity two, and normalised ancestor capacity one at level $2\mu$.  The cubic
$z^3+(3/100)z-3/4$ has $\mu>13/25$ and no critical value separated by two.
Neither example is a counterexample to Erd\H{o}s~\#1041; both are trinomials.
The unrestricted constant $2$ and the high-critical residual remain open.


```

## R6-E10 — Statements and declarations
Long-record verification appendix: preserve the exact duplicate-interface and ordinary/Lean distinctions from this removed block.
```tex
\section*{Statements and declarations}

This manuscript is authored exposition, not Lean proof authority.  Its
strongest complete coefficient family is the all-degree monic trinomial
theorem.  Its strongest unrestricted-geometry parent regime is the ordinary
$\mu\le13/25$ theorem.  Its strongest unrestricted-geometry weakening with no
threshold on $\mu$ remains the constant-factor path of length
$(71/10)\rho$ in $K_{2\mu}$.  First-merge arity and component-capacity
regimes reach the parent constant $2$ only as sufficient implications under
$\mu\le1/2$.  Lean does not formalise the coarea, univalent-map,
component-capacity, ODE, or path-assembly arguments of the last three.

Its
strongest source-current checked family is the critical geometric-mean
proximity theorem
\pdecl{exists_two_roots_dist_sum_le_two_mul_geomMean}, paired with the exact
unique-nearest-spoke and all-straight-cubic no-go certificates.  The translated
cubic quotient-fibre theorem, primitive sparse-quintic theorem, and sharp
collinear theorem are complete ordinary paper theorems whose load-bearing
selectors or alternation kernels are Lean checked.  Lean does not formalise
their finite-fibre, moment-to-path, or affine-transport assemblies.

The older checked core is the Newton value equation, the exponential first
integral, the consumer form of ray separation, the finite planar-avoidance
theorem, quantitative constant-translation root retention, and the
ray-collision parameterisation.  The generic slit-sheet decomposition is an ordinary theorem; the sharp
admissible-arc length bound in \S\ref{sec:open} remains unproved.  The
diagnosis of Proposition~12 in \S\ref{sec:gap} has two independent parts: the
printed local saddle construction is topologically invalid, and the exact
Cassini budget refutes the proposition's metric statement.  The
search results of \S\ref{sec:finite} are computations.

The live free-point statement is the registered weighted quadratic theorem
in every degree, recorded as catch-up in Theorem~\ref{res:fp-weighted-all-degree}.
The four-point inequality and the adaptive central-region certificate remain
valid specialised proofs.  The files \texttt{FreePointFP4Complete.lean} and
\texttt{FreePointTorusPshReduction.lean} check scalar algebraic kernels only.
They do not formalise the complete analytic argument, plurisubharmonic
removability, the torus product identity, or a root-to-root path.  No novelty
or literature-priority claim is made for these auxiliary inequalities.

The exact attachment-age/lifetime transform, its Jensen consequences, the
root-summed age/product identity, and the two-young-root selector are ordinary
exact theorems proved in the source note
\texttt{AttachmentAgeLifetimeOrlicz.md}.  The companion Lean module checks
only four scalar consumers after the analytic identities and monotonicity have
been supplied.  The five Comparator packages expose those four consumer
types: \texttt{OrliczNoUniformLinear} and \texttt{NoUniformLinear} are
duplicate interfaces for one mathematical obstruction, not two distinct
paper results.  No claim is made here that Lean formalises the integral
substitution, convexity, Jensen's inequality, the merge-tree double count, or
the remaining geometric allocation theorem.

The reciprocal Newton expansion, coefficient recursion, near-Fekete bridge,
compact normalisation, staple identity, and completed-square contact criterion
are ordinary exact theorems proved in
\texttt{ReciprocalNewtonExpansion.md}.  Lean checks seven distinct finite
kernel types exposed through nine Comparator packages:
\texttt{ReciprocalTail} duplicates \texttt{NormRecipPowerSum}, and
\texttt{ContactAbsorption} duplicates \texttt{ContactSurvives}.  These are
one reciprocal-coordinate and transfer family, not nine independent paper
claims.  The logarithmic-series identity, full $C^2$ bounds, exact
near-Fekete identification, and rational compactification remain ordinary
proof rather than Lean-formalised assertions.


```

## R6-E11 — app:sources
Long-record formal-source appendix: keep all old declarations, immutable source hashes, duplicate-interface warnings and replay targets.
```tex
\appendix
\section{Guide to the formal sources}\label{app:sources}

The source-current checked summit is distributed across
\texttt{CriticalTwoRootProximity}, \texttt{CubicQuotientFiberCase},
\texttt{PrimitiveQuinticBoundaryTail},
\texttt{PrimitiveQuinticInteriorTail},
\texttt{SharpCollinearAlternation}, and
\texttt{SharpCollinearChebyshev}.  The public
\texttt{ErdosProblems.Erdos1041.NewtonFlowRaySeparation} module contains the
older checked Newton-flow source.  The search of
\S\ref{sec:finite} is
\texttt{scripts/search\_counterexample.py} in the source package.  The
declaration table below is pinned to the shared formal-source commit used for
the Newton-flow declarations in this problem-note series.

\begin{itemize}[leftmargin=*]
\item \lref{Erdos1041/CriticalTwoRootProximity.lean}{289}{exists_two_roots_dist_sum_le_two_mul_geomMean}
\item \lref{Erdos1041/CriticalTwoRootProximity.lean}{438}{nearestSpoke_unique_nearest_spoke_escapes}
\item \lref{Erdos1041/CriticalTwoRootProximity.lean}{569}{allStraightCubic_every_pair_midpoint_escapes}
\item \lref{Erdos1041/CubicQuotientFiberCase.lean}{161}{cubic_has_safe_root_spoke}
\item \lref{Erdos1041/PrimitiveQuinticBoundaryTail.lean}{200}{primitiveBoundary_exists_two_tailEnergy_lt_one}
\item \lref{Erdos1041/PrimitiveQuinticInteriorTail.lean}{272}{primitiveInterior_exists_two_tailEnergy_lt_one}
\item \lref{Erdos1041/SharpCollinearAlternation.lean}{158}{exists_peak_le_of_monic_comparison}
\item \lref{Erdos1041/SharpCollinearChebyshev.lean}{133}{exists_peak_le_comparisonBound}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{34}{newtonFlowVector}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{38}{derivative_mul_newtonFlowVector}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{50}{newtonFlow_value_hasDerivAt}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{64}{newtonFlow_scaledValue_hasDerivAt_zero}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{77}{SamePositiveRay}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{80}{samePositiveRay_refl}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{84}{samePositiveRay_symm}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{92}{samePositiveRay_trans}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{107}{translated_samePositiveRay_parameterization}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{127}{realAffineLine}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{130}{realAffineLine_eq_affineSpan}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{147}{isClosed_realAffineLine}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{152}{dense_compl_realAffineLine}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{162}{exists_small_avoiding_finite_realAffineLines}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{179}{samePositiveRay_imp_mem_realAffineLine}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{197}{exists_small_translation_separating_arguments}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{230}{norm_lt_one_of_near_root}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{257}{constant_perturbation_root_near_original}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{287}{constant_perturbation_roots_in_unitDisk}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{306}{samePositiveRay_of_real_exp_decay}
\item \lref{Erdos1041/NewtonFlowRaySeparation.lean}{315}{no_newtonConnection_of_not_samePositiveRay}
\end{itemize}

\begingroup
\raggedright
\paragraph{Source-current auxiliary proofs.}
The proofs of The specialised four-point and central-radius arguments retained in the long record are
\path{ErdosProblems/Erdos1041/FreePointZeroInsertionFP4Matching.md}; its
deterministic replay is
\path{scripts/check_erdos1041_free_point_zero_insertion_fp4.py}.
The scalar Lean companion contains
\path{three_mul_pairProduct_le_sum_sq} and the five
\path{outer_*} stationary-point certificates.  The proof of
Theorem~\ref{res:fp-to-s} is
\path{ErdosProblems/Erdos1041/FreePointTorusPshReduction.md}; its replay is
\path{scripts/check_erdos1041_free_point_torus_psh_reduction.py}.
Its Lean companion checks
\path{rpow_le_tangent_at_one},
\path{sum_rpow_le_card_of_sum_le_card}, and the two finite exponent
bridge declarations.  These source-current files are not covered by the older
Newton-flow commit pin below; the paper states their separate authority and
validation boundary explicitly.

The attachment-age/lifetime proof is
\path{ErdosProblems/Erdos1041/AttachmentAgeLifetimeOrlicz.md}, and its scalar
Lean companion is
\path{ErdosProblems/Erdos1041/AttachmentAgeLifetimeOrlicz.lean}.  Its
Comparator interfaces are
\path{ExternalVerification1041LifetimeOrliczBound},
\path{ExternalVerification1041WeightedChainConsumer},
\path{ExternalVerification1041SecondAgeBound}, and
\path{ExternalVerification1041OrliczNoUniformLinear}.  These interfaces cover the
formalised finite consumers of the long-record argument.  The change of
variables and integral properties in Theorem~\ref{res:orlicz-currency}
remain ordinary analysis.

The reciprocal-coordinate proof and replay description are
\path{ErdosProblems/Erdos1041/ReciprocalNewtonExpansion.md}; its finite Lean
kernel is
\path{ErdosProblems/Erdos1041/ReciprocalNewtonExpansion.lean}, and its exact
replay is
\path{ErdosProblems/Erdos1041/scripts/check_erdos1041_reciprocal_newton_expansion.py}.
The Comparator interfaces are
\path{ExternalVerification1041NewtonSolve},
\path{ExternalVerification1041NormRecipPowerSum},
\path{ExternalVerification1041GeometricTail},
\path{ExternalVerification1041QuadraticContact},
\path{ExternalVerification1041ContactSurvives},
\path{ExternalVerification1041StapleEquality}, and
\path{ExternalVerification1041StapleLength}.  They cover the seven checked
finite kernels identified above, not every ordinary theorem in
Section~\ref{sec:reciprocal}.

The finite near-Fekete result retained in the long record has the ordinary
analytic source note
\texttt{ErdosProblems/Erdos1041/NearFeketeTransverseClosure.md}, pinned to
source commit
\texttt{0f248d8826eca5f946052c1d4fd2f983bc3d7a04} and SHA-256
{\footnotesize\nolinkurl{3fbfcab1310c5d596990baab102d5787331f1df37a85b8becb2aab77eb5daadd}}.
Its limited formal consumer is
\texttt{ErdosProblems.Erdos1041.NearFeketeTransverseClosure}, whose tracked
Lean source is pinned to commit
\texttt{ee2bfdebfe6d7d4827cf0d1b243f37fd3667c3e7} and SHA-256
{\footnotesize\nolinkurl{20cd39f660e19c71bb47868721e7f69b6ae5585045087237b0bd6a9fa64d43a5}}.
The declarations at lines 19--60 check only eventual sign and length transfer;
they do not formalize the two-cutoff complex analysis, tangent strata, bulk
regime, or the unrestricted problem.

\paragraph{Immutable source-generation boundary.}
The declaration table above is pinned to formal-source commit
\texttt{7e80158d80c9beccbaa930a0b45da2db70f253d4} (23 August 2026), whose
tracked source file
\texttt{ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean} has SHA-256
{\footnotesize\nolinkurl{b3cde5cb40fb93fbbd410e8931cd9ae6fcb4e30e1346ac62d62ebaee55f65fb1}}.
This pin covers only the declarations named above, including the exact
value-equation, ray-separation, finite-avoidance, and root-retention locators;
it is not a claim that the surrounding global-flow or length argument is
formalised.  The bounded project entrypoint for replay is
\texttt{formal\_math/erdos257\_period\_noncollapse/scripts/lean\_fast\_build.py}
with the module target
\texttt{ErdosProblems.Erdos1041.NewtonFlowRaySeparation}; a replay of that
target remains validation evidence for the listed declarations, not an
independent proof of the paper's ordinary arguments.
\par
\endgroup


```

## R6-E13 — bibliography, dubinin
Long record, adjacent literature / Dubinin comparison, including printed-page locator and source history.
```tex
  Theorem~1, printed page~85, assumes a holomorphic function giving a full
  $n$-fold covering of an annulus $t_1<|w|<t_2$ and, with $E$ the
  complementary set defined there, states
  $(t_2/t_1)^{2/n}\le m(E\cup D)/m(E)$.  This is a P\'olya-type area
  inequality under a covering hypothesis.  T.~Tao cited it on the Erd\H{o}s
  Problem~\#1041 discussion page, 25 March 2026, for the relative area
  scaling factor.  It is recorded here as a neighbouring result, and no
  argument in this note uses it; the area input used is the absolute
  P\'olya inequality \cite{polya1928}.

```
