# A quantitative two-parameter chart around the block-L1 rescue

## Result

The rational connector from `TiedNewtonFaceBlockL1RationalRescue.md` is
uniform on an explicit coefficient box.  Put

~~~text
epsilon = -5997001/10^9,
rho = 1/192,
P_{a,b}(z) = -z^6 + a z^2 + b,
|a+3| <= rho,
|b-epsilon| <= rho.                                      (1)
~~~

For every real pair `(a,b)` satisfying (1), the two segments

~~~text
[h,Ru], [h,Rv],
h=7/10+(57/80)i,  R=5/4,
u=1,  v=1/2+(sqrt(3)/2)i,                                (2)
~~~

and their outward radial tails lie strictly in `{Re P_{a,b}<0}`.  Their
finite length is independent of `(a,b)` and is strictly below `2`; the
cutoff budget remains `2R=5/2`.  Moreover `{Re P_{a,b}<0}` is one
six-ended component throughout the box.  Thus (1) is a certified
two-dimensional tied-face chart, not merely a qualitative continuity
neighbourhood of one sextic.

## Uniform arm calculation

Write `a=-3+delta_a` and `b=epsilon+delta_b`.  Along either arm, every
degree-six Bernstein control has the affine form

~~~text
B_j + delta_a S_j + delta_b,                              (3)
~~~

where `B_j` is the corresponding control of the central sextic.  Exact
arithmetic gives, for all fourteen controls,

~~~text
-B_j/(1+|S_j|) > rho.                                     (4)
~~~

The minimum of the fourteen permissible radii is attained by the second
`u`-arm control and equals

~~~text
rho_* = 20577415197/3931840000000
      = 0.005233533205064... .                            (5)
~~~

The seven sensitivity controls `S_j` on the `u` arm are

~~~text
-113/6400, 2687/9600, 27061/48000, 26687/32000,
104687/96000, 4/3, 25/16,                                 (6)
~~~

and on the `v` arm they are

~~~text
-113/6400,
-(-429+475 sqrt(3))/3200,
-(-2787+3800 sqrt(3))/16000,
-19(-173+450 sqrt(3))/32000,
-(2571+7600 sqrt(3))/32000,
-(19 sqrt(3)+48)/128,
-25/32.                                                   (7)
~~~

The rational bounds `3/2<sqrt(3)<7/4` prove `|S_j|<2` in
(6)--(7).  Hence (1), (3), and (4) give

~~~text
B_j + delta_a S_j + delta_b
 <= B_j + |delta_a||S_j| + |delta_b|
 <= B_j + rho(|S_j|+1) < 0.                               (8)
~~~

Bernstein convex-hull containment proves strict negativity on both
complete arms, uniformly over the closed box.  The convenient radius is
sharp among reciprocal integers for this fixed template: `rho<rho_*<1/191`,
so `1/192` works while `1/191` fails the worst-sign perturbation of that
second `u`-arm control.

## Uniform tails

Let

~~~text
a_-=-577/192,  a_+=-575/192,
b_+=epsilon+rho=-2366003/3000000000.
~~~

On the `u` ray,

~~~text
Re P_{a,b}(ru)=-r^6+a r^2+b<0
~~~

because `a<=a_+<0` and `b<=b_+<0`.  On the `v` ray,

~~~text
Re P_{a,b}(rv)=-r^6-(a/2)r^2+b
 <= -r^6-(a_-/2)r^2+b_+ =: G(r).                          (9)
~~~

For `r>=R`, `G` is strictly decreasing: its derivative is
`r(-6r^4-a_-)`, and at the cutoff the bracket is already

~~~text
-6R^4-a_- = -4471/384<0.                                  (10)
~~~

The worst cutoff value is

~~~text
G(R)=-11741335383/8000000000<0.                           (11)
~~~

Equations (9)--(11) certify the second complete tail.

## Component passport throughout the box

The derivative is

~~~text
P'_{a,b}(z)=-2z(3z^4-a).
~~~

Since `a<0`, it has five simple critical points.  The central critical
value is `b`.  At any other critical point, `z^4=a/3`, so

~~~text
P_{a,b}(z)=b+(2a/3)z^2.
~~~

Here `z^2` is purely imaginary; all five critical values therefore have
real part `b<0`.  The ramification count in the negative half-plane is
five.  The component-degree identity

~~~text
sum_C deg(P:C -> left half-plane)
  = number of components + total ramification
~~~

then reads `6 = number of components + 5`.  Thus the negative preimage is
one connected six-ended component for every parameter in (1).

## Metric and consequence

The two arm squares are unchanged:

~~~text
|Ru-h|^2=1037/1280,
|Rv-h|^2=2157/1280-(57/64)sqrt(3),
~~~

so each arm has length below one.  This upgrades the strict point rescue
to a genuine rational chart cell with fixed selector, hub, cutoff, arms,
tails, topology, and metric budget.  It does not give an all-degree chart
cover, a dense successful class, or the unrestricted Erdős #1041 theorem.

## Formal boundary

The exact checker reconstructs all fourteen base margins, all fourteen
sensitivity controls, the affine perturbation identity, the critical-value
passport, and the worst tail bounds.  Lean checks the perturbation kernel,
parameter signs, critical-value real-part kernel, and worst tail arithmetic.
Bernstein convex-hull containment and the component-degree identity remain
ordinary proof.
