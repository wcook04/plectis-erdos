# Finite transfer of the complex rotated-diameter tube

Status: complete ordinary sequential transfer theorem, exact rational budget
checker, and Lean-checked absorption kernel, 2026-08-26. This closes the
actual-polynomial consumer of `TiedNewtonFaceComplexDiameterTube` along every
near-Fekete sequence whose limiting tied reciprocal-Newton face lies strictly
in one of its norm-budget cells. It does **not** prove that those cells cover
all tied faces, and therefore does not prove unrestricted Erdős #1041.

## 1. Statement

Let `n` be positive and even, `omega=exp(2 pi i/n)`, and let

~~~text
a_{nu,k}=omega^k(1+e_{nu,k}),       max_k |e_{nu,k}| -> 0,
|a_{nu,k}|<1,                       f_nu(z)=prod_k(z-a_{nu,k}).       (1)
~~~

Use the reciprocal-Newton normalization of `ReciprocalNewtonExpansion`:

~~~text
lambda_nu^n=p_n(a_nu)/n,            lambda_nu -> 1,
rho_nu=max(d_nu^(1/n), max_{m<n}|b_{nu,m}|^(1/(n-m))) -> 0,
d_nu=-log|f_nu(0)|,
A_{nu,0}=d_nu/rho_nu^n,             A_{nu,m}=b_{nu,m}/rho_nu^(n-m). (2)
~~~

Pass to a subsequence on which the compact normalized coefficients converge,
and write its limiting real-part model as

~~~text
Re Q(z),       Q(z)=-z^n+b+sum_{1<=m<n} c_m z^m,           (3)
~~~

where `b=-lim A_{nu,0}` is real and nonpositive. Suppose that for some
`n`-th root of unity `u`, some `R>=1`, and majorants `d_m>=|c_m|`,

~~~text
A_R=sum d_m R^m,             B_R=sum d_m/R^(n-m),
delta=-(b+A_R)>0,            B_R<=1.                       (4)
~~~

> **Complex-diameter finite-transfer theorem.** For all sufficiently large
> `nu`, the two roots converging to the opposite regular directions `u` and
> `-u` are joined inside `{|f_nu|<1}` by their equal-radius staple. Its common
> cutoff may be taken to be
>
> ~~~text
> s_nu=2R rho_nu/|lambda_nu|,                               (5)
> ~~~
>
> and its length is strictly less than two.

Thus every strict complex diameter cell is not merely a limiting connector:
it is an eventually successful actual-polynomial near-Fekete class. No
continuous selector between different cells is asserted or needed.

## 2. Compact chord

The exact reciprocal expansion gives, on every fixed compact set,

~~~text
rho_nu^(-n) log|f_nu(rho_nu lambda_nu^(-1) z)|
      -> Re Q(z)                                                     (6)
~~~

uniformly. The two normalized actual root directions tend to `u` and `-u`,
so the moved chord with endpoints at normalized radius `2R` converges
uniformly to `[-2Ru,2Ru]`. The complex-diameter theorem gives the stronger
global estimate

~~~text
Re Q(tu)<=b+A_R=-delta                    (t real).          (7)
~~~

Uniform convergence on the compact family of moved chords therefore leaves
at least `delta/2` of strict margin for all large `nu`. This proves containment
of the finite chord. Notice that no zero-contact argument occurs.

## 3. Mesoscopic tails

For `t>=2R`, the target lower modes satisfy the sharper estimate

~~~text
sum d_m t^m/t^n
 = sum (d_m/R^(n-m))(R/t)^(n-m)
 <= (R/t) B_R <= 1/2.                                      (8)
~~~

The normalized actual direction tends to `u` (or `-u`), hence the real part
of its `n`-th power is eventually at least `7/8`. Coefficient convergence in
(2)--(3), uniformly for `t>=2R`, costs at most `t^n/8` after weighting every
degree `m<n` by `(2R)^(-(n-m))`.

It remains to control the terms of reciprocal degree above `n`. Put
`z=rho_nu lambda_nu^(-1)t v_nu`, where `|v_nu|=1`, and stop while the physical
radius is at most a fixed `epsilon`. The tail estimate (T0), with truncation
order `n`, becomes

~~~text
rho_nu^(-n)|T_n(z)| <= C_n rho_nu t^(n+1) <= C'_n epsilon t^n. (9)
~~~

Here the minimum root modulus and `|lambda_nu|` tend to one. Choose `epsilon`
once so that the final quantity is at most `t^n/8`. Since the normalized
constant is exactly `-A_{nu,0}<=0`, (8)--(9) give

~~~text
rho_nu^(-n) log|f_nu(z)|
 <= (-7/8+1/2+1/8+1/8)t^n
 = -t^n/8 < 0.                                             (10)
~~~

This controls both outward normalized tails from `2R` until fixed physical
radius `epsilon`. The cutoff (5) is admissible for large `nu` because it tends
to zero while both root moduli tend to one.

## 4. Fixed outer collar

On either selected moving root ray and for physical radius
`epsilon<=t<=|a_{nu,k}|`, the polynomials and directions converge uniformly to
the regular-polygon comparison

~~~text
|t^n-1|=1-t^n <= 1-epsilon^n.                              (11)
~~~

Uniform convergence costs less than `epsilon^n/2` for large `nu`, so
`|f_nu|<1` on the complete fixed collar. At its outer endpoint `f_nu=0`.
Together with (10) and the compact chord, this proves containment of the whole
staple.

Finally `ReciprocalNewtonExpansion` R4 gives its exact length

~~~text
|a_i|+|a_j|-s_nu(2-|u_i-u_j|) <= |a_i|+|a_j| < 2.          (12)
~~~

This is why the transfer consumes no polynomial-independent metric slack.

## 5. Consequence and surviving frontier

The actual-polynomial transfer previously assigned to the resolved-transfer
desk is now closed for every strict complex norm-budget cell. Desk 2 should
remove the union of these cells from tied-face selector search. Desk 5 should
use this theorem as a regression and work only on equality-boundary cells or
on tied faces outside the union; it should not re-prove chord/tail containment
for the strict tube.

The unrestricted problem remains open. The load-bearing residual is now the
**coverage theorem**: prove that every tied reciprocal-Newton face either lies
in some rotated complex diameter cell, lies in another already solved strict
chart, or admits a new connector. Conditions (4) are sufficient, not known to
be exhaustive.

## 6. Verification boundary

The Lean companion proves the compact strict-margin absorption, the four-term
mesoscopic budget (10), the outer-collar absorption, and the final metric-free
length implication. The exact checker replays the factor `1/2` in (8), the
`7/8,1/2,1/8,1/8` ledger, the genuinely complex quartic witness, and a rational
outer-collar budget. Uniform convergence in (6), the reciprocal tail
rescaling (9), moving-direction convergence, and assembly of the three path
ranges are ordinary analytic mathematics proved above.
