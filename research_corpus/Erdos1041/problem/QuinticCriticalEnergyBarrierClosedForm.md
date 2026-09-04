# Exact closed form for the quintic critical-spoke energy barrier

## Status

This note removes the one-variable optimisation from the phase-free part of
the source-current quintic `J2` selector.  It is an ordinary exact theorem
with a symbolic checker.  It does not replace the phase-moment row: that row
can still pass when the sharp energy barrier below fails.

## 1. Closed maximum

At a quintic critical point use the notation of
`CriticalSpokePhaseMomentHybrid.md`.  For one root row the energy majorant is

```text
F_S(t)=(1-t)(1+t/2+S t^2/4)^2,       0<=t<=1, S>=0.       (1)
```

Put `Phi_5(S)=max_(0<=t<=1) F_S(t)`.  Exact differentiation gives, with
`h=1+t/2+S t^2/4`,

```text
F_S'(t)=h(t) t [4S-6-5S t]/4.                             (2)
```

Since `h(t)>0`, (2) proves

```text
Phi_5(S)=1,                                  0<=S<=3/2,

Phi_5(S)=(S+6)^3(4S-1)^2/(5^5 S^3),         S>3/2.        (3)
```

Indeed the unique positive stationary point in the second case is

```text
t_*=(4S-6)/(5S),
1-t_*=(S+6)/(5S),
1+S t_*=(4S-1)/5.                                          (4)
```

At stationarity `h(t_*)=(1-t_*)(1+S t_*)`, which gives (3).  The derivative
sign in (2) also proves that this point is the global maximum.

## 2. Exact target certificate

Let `mu=|P(c)|<1`, order the critical reciprocal weights so that
`p_1>=p_2>=...`, and put `S_2=(1-p_2)/p_2`.  The two nearest energy rows are
both certified exactly when

```text
S_2<=3/2,
```

or, for `S_2>3/2`,

```text
mu (S_2+6)^3(4S_2-1)^2 <=3125 S_2^3.                      (5)
```

This is the sharp symbolic inequality for the pure energy member of the
quintic critical selector.  When it holds, the two spokes lie in `{|P|<1}`
and the geometric-mean two-nearest budget gives total length
`<=2mu^(1/5)<2`.

Formula (5) is strictly stronger than testing only the occupied cone
`S_2<=3/2`, because it spends the actual critical-value margin.  Conversely,
if (5) fails, no rearrangement of the phase-free AM--GM row can certify this
critical point: (3) is its exact maximum.  The retained phase coefficients in
the full pointwise `J2=max_t min(F,K)` row are then the next straight-spoke
mechanism.

## 3. Uniform range and calibration

Critical reciprocal vectors sum to zero.  If their moduli are ordered
`l_1>=l_2>=...>=l_5`, then

```text
l_1<=l_2+l_3+l_4+l_5<=4l_2,
sum_i l_i^2<=20l_2^2.
```

Thus `p_2>=1/20` and `S_2<=19`.  At the endpoint,

```text
Phi_5(19)=28125/6859,
1/Phi_5(19)=6859/28125.                                  (6)
```

This endpoint is only a calibration: the older universal second-spoke
envelope has a stronger uniform low-critical threshold.  The new content is
the adaptive exact dependence (3)--(5), which is substantially sharper on the
observed Bernstein-failure rows and feeds the full `J2` allocation without a
numerical maximisation.

The two exact witnesses in `BernsteinNoGoCriticalConeRescue.md` lie in the
first branch `S_2<3/2`.  In adversarial angular streams, the energy-only
failures occur near the regular pentagon with `S_2` around `3.68` and
`mu` near one; those are precisely the rows for which the phase-moment or
curved near-Fekete mechanisms remain necessary.  These stream values are
falsifier guidance only, not theorem evidence.

## 4. Replay and boundary

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_critical_energy_barrier_closed_form.py
```

Proved: (2)--(6), hence an optimisation-free exact quintic energy selector.
Not proved: Bernstein-or-full-`J2`, failure-to-near-Fekete, or unrestricted
Erdős #1041.
