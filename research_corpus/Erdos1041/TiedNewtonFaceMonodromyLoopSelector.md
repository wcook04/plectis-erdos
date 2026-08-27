# The monodromy-loop representation of the tied-face metric residual

This note changes coordinates for the remaining tied-face selector.  It does
not prove the missing metric inequality.  It proves that critical-ray lifts,
noncritical connectors, and arbitrary intrinsic connectors are competitors in
one weighted monodromy-loop problem on the left half-plane.

## 1. Setting

Let

```text
Q(z)=-z^n+sum_{m<=M} A_m z^m,       M<n/2,
H_-={w: Re w<0},                    Omega_-={z: Re Q(z)<0},
```

and let `U` be a component of `Omega_-` with end set `E(U)`.  The component
passport theorem gives a proper surjective branched cover

```text
Q|_U:U -> H_-
```

of degree `d=|E(U)|`.  For all sufficiently large `T`, let `z_j(T)` be the
unique point in end `j` satisfying `Q(z_j(T))=-T`.

For `j,k in E(U)`, define the weighted monodromy action

```text
A_T(j,k)=inf integral_0^1 |eta'(s)|/|Q'(tilde_eta(s))| ds,       (1)
```

where the infimum is over rectifiable loops `eta:[0,1]->H_-`
based at `-T` and lifts `tilde_eta:[0,1]->U` with

```text
tilde_eta(0)=z_j(T),       tilde_eta(1)=z_k(T).
```

The integrand is interpreted almost everywhere; a lift may pass through a
critical point.  Equivalently, the infimum may be taken over loops avoiding
the finite critical-value set, with monodromy sending sheet `j` to sheet `k`.

## 2. Exact loop representation

**Theorem 1 (monodromy-loop representation).**  For all sufficiently large
`T` and all `j,k in E(U)`,

```text
A_T(j,k)=d_U(z_j(T),z_k(T)),                                  (2)
```

where `d_U` is the Euclidean intrinsic distance in `U`.

### Proof

If `gamma` is a rectifiable path in `U` from `z_j(T)` to `z_k(T)`, then
`eta=Q o gamma` is a loop based at `-T`.  The chain rule for rectifiable paths
holds almost everywhere and gives

```text
|gamma'(s)|=|eta'(s)|/|Q'(gamma(s))|
```

away from the finitely many parameter values at which `gamma` meets a
critical point.  Integration gives equality of the two lengths.  Taking the
infimum proves `A_T(j,k)<=d_U(z_j(T),z_k(T))`.

Conversely, every admitted `tilde_eta` is a rectifiable path in `U` with the
required endpoints, and the same almost-everywhere chain rule identifies its
action with its Euclidean length.  Hence
`d_U(z_j(T),z_k(T))<=A_T(j,k)`.

Finally, the full preimage in `U` of the finite critical-value set is finite.
A rectifiable path in the plane can be perturbed around every point of that
finite set by arcs of arbitrarily small Euclidean length.  Its projection then
avoids every critical value, including visits through noncritical points of a
critical fibre.  Properness gives ordinary path lifting, and the terminal
sheet is exactly the monodromy image of the initial sheet.  This proves the
nonsingular-loop formulation without changing the infimum.  `□`

## 3. Fibre endpoints have the same renormalized defect

Let `omega_j=exp(2 pi i j/n)`.  The large fibre equation gives, uniformly over
the finitely many ends,

```text
z_j(T)=T^(1/n) omega_j+O(T^((M-n+1)/n)).                       (3)
```

Because `M<n/2`, the exponent in (3) is negative.  Thus the error is `o(1)`.
The short segment joining `z_j(T)` to `T^(1/n)omega_j` lies in the same
negative end for large `T`: throughout an `o(1)` neighbourhood of the radial
point the leading term has real part `-T+o(T)`.

**Theorem 2 (Busemann-defect identity).**  If

```text
F_U^{j,k}(R)=d_U(R omega_j,R omega_k)-2R
```

and `beta_U(j,k)=lim_{R->infinity} F_U^{j,k}(R)`, then

```text
beta_U(j,k)
 =lim_{T->infinity} [A_T(j,k)-2T^(1/n)].                       (4)
```

### Proof

Equation (3) and the contained `o(1)` end segments change intrinsic distance
by at most `o(1)`.  Apply Theorem 1 with `R=T^(1/n)` and use the already proved
existence of `beta_U(j,k)`.  `□`

The same statement holds if the base point is `v-T` for any fixed `v in H_-`;
the constant translation changes each large inverse endpoint by `o(1)`.

## 4. Old selectors inside the new coordinate

For a simple negative critical point `c`, put `v=Q(c)`.  The doubled segment
from `v-T` to `v`, pinched at `v`, lifts from one sheet to the other.  Its
renormalized action is precisely the horizontal-fibre defect

```text
delta_Q(c)=integral_0^infinity [
  1/|Q'(gamma_+(t))|+1/|Q'(gamma_-(t))|
  -(2/n)t^(1/n-1)] dt.                                       (5)
```

Thus `HF-strict` restricts (1) to pinched straight loops through a branch
value.  The minimum-real and leftmost-fibre no-go theorems show that particular
ways of selecting such a loop are false; they do not refute (1).

An intrinsic connector avoiding critical points projects, after `o(1)` end
normalization to a common far-left fibre, to an ordinary nonsingular loop with
the same limiting defect.  Therefore the rational noncritical rescues are not
exceptions to the branched-cover mechanism.  They demonstrate that the
infimum in (1) may be strictly better than the pinched critical-ray subclass.

## 5. The corrected all-degree producer

After the trace theorem selects a negative component with at least two ends,
the tied-face metric problem is exactly the following weighted systolic
statement:

```text
min over distinct j,k in E(U)
  lim_T [ inf_{monodromy j->k} length_Q(eta) - 2T^(1/n) ] < 0, (MLS-strict)
```

or the non-strict inequality together with an equality-rigidity theorem that
produces a finite-radius connector.  Here `length_Q` means the lifted action
in (1), not an unweighted length in the base.

This formulation has four advantages.

1. The negative component and its noncrossing monodromy block are preserved.
2. Critical and noncritical hubs are optimized simultaneously.
3. The fibre product and complete velocity moments act directly on the
   integrand `1/|Q'|` along competing sheets.
4. A semialgebraic connector chart is a finite exact upper bound for one loop
   class, while a no-go eliminates only that class or parameterization.

The remaining inequality is still open.  No product-to-pair inference, KKT
upper-bound claim, or finite sampled atlas is asserted here.  The proved gain
is the exact representation (2)--(4), which supplies a common central object
for the joint-selector, fibre-monodromy, and chart-cover attacks.

## 6. Formalization boundary

The path-length chain rule, end asymptotic (3), critical-point detour, and
proper branched-cover lifting remain ordinary mathematics in this note.  A
Lean landing can first formalize the metric kernel abstractly:

```text
lifted_action_eq_curve_length
intrinsic_distance_eq_inf_lifted_action
renormalized_defect_congr_of_endpoint_error_tendsto_zero
```

The analytic adapters for polynomial ends and monodromy should not be claimed
Lean-checked until they are actually formalized.
