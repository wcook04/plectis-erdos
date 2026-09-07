#!/usr/bin/env python3
"""Exact symbolic replay of the fixed-strip support certificate."""

from __future__ import annotations
from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sympy as s


def report(name: str, ok: bool) -> None:
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        raise AssertionError(name)


# FST2 boundary calculation.  Put q=|B| and impose
# A=(1-tau^2)q/(2tau); then R=(1+tau^2)q/(2tau), so f=tau.
tau, q = s.symbols("tau q", positive=True)
A = (1-tau**2)*q/(2*tau)
R = (1+tau**2)*q/(2*tau)
report("FST1 square-root-free cone boundary", s.cancel(q/(R+A)-tau) == 0)
report("FST2 squaring side condition", s.simplify(A/q+tau) == (1+tau**2)/(2*tau))

# Compact-chart derivative relation.
r, y, mu, eta, alpha, T, t = s.symbols("r y mu eta alpha T t", nonzero=True)
d = eta**5
om = 1-r
G = (r**15*y**5 + 5*r**10*om**2*y**4 + 10*r**5*om**4*y**3
     +(10+mu)*om**6*y**2-d)
Gy = s.diff(G,y)
x = r**5/om**2*y
Fprime = 5*x**4+20*x**3+30*x**2+2*(10+mu)*x
report("FST3 compact derivative factor", s.factor(Fprime-r**5/om**8*Gy) == 0)

# Terminal chart.  Substitute r=1-t only after the rational simplification.
y_tail = eta*r**-3*(1+om**2*T)
Jcalc = s.cancel(G.subs(y,y_tail)*r**6/(om**2*eta**2))
Jtarget = (
    r**6*eta**3*(5*T+10*om**2*T**2+10*om**4*T**3+5*om**6*T**4+om**8*T**5)
    +5*eta**2*r**4*(1+om**2*T)**4
    +10*eta*r**2*om**2*(1+om**2*T)**3
    +(10+mu)*om**4*(1+om**2*T)**2
)
report("FST4 exact regular terminal equation", s.factor(Jcalc-Jtarget) == 0)

Jt = s.expand(Jtarget.subs(r,1-t))
J0 = s.expand(Jt.subs(t,0))
report("FST5 simple terminal fibre", s.factor(J0-5*eta**2*(eta*T+1)) == 0)
report("FST6 terminal derivative nonzero", s.diff(J0,T) == 5*eta**3)

# Stable transverse coordinate identity, using alpha*eta=1.
zexpr = s.cancel(alpha*(r**5/om**2)*y_tail).subs(alpha*eta,1)
report("FST7 regular transverse coordinate", s.factor(zexpr-(r**2/om**2+r**2*T)) == 0)

# Complete exact carrier/wall/support fibres at kappa=+-1/1000.  The
# carriers and all compact-arm tubes are certified; floats only scout boxes.
LIB = Path(__file__).with_name("lib_erdos1041_support_engine.py")
SPEC = importlib.util.spec_from_file_location("support_engine", LIB)
ENGINE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(ENGINE)
fibre_plus = ENGINE.certified_full_fibre(kappa=Fr(1, 1000), weak_cells=2048)
fibre_minus = ENGINE.certified_full_fibre(kappa=Fr(-1, 1000), weak_cells=2048)
fibres = (fibre_minus, fibre_plus)
report("FST8 exact physical carriers and wall separation",
       all(row["carrier"]["cross_margin"] > 0
               and row["carrier"]["mu_radius"] < 1e-15
               and row["carrier"]["w_radius"] < 1e-12
               for fibre in fibres for row in fibre["rows"]))
report("FST9 positive weak anchor E<-1/36",
       fibre_plus["rows"][0]["pair_upper"] < -Fr(1, 36))
report("FST10 negative weak anchor E<-1/50",
       fibre_minus["rows"][0]["pair_upper"] < -Fr(1, 50))
report("FST11 both complete upper fibres isolated and negative",
       all(fibre["upper_roots_disjoint"]
               and all(row["muC"].b-row["muC"].r > 0 for row in fibre["rows"])
               for fibre in fibres)
       and all(row["pair_upper"] < -Fr(1, 50)
               for fibre in fibres for row in fibre["rows"]))
for fibre in fibres:
    print("FIBRE", fibre["kappa"],
          [(row["index"], row["method"], row["pair_upper_float"])
           for row in fibre["rows"]])

print("ALL CHECKS PASSED")
