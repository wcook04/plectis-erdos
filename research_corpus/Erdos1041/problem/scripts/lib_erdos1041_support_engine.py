"""Exact dyadic support-defect engine for the compact quintic arm chart.

Floats only scout roots.  Krawczyk tubes, tangent signs, Stieltjes variation,
tail bounds, carrier isolation, wall reconstruction, and final comparisons
use exact rational balls.
"""

from __future__ import annotations
import importlib.util
from fractions import Fraction as Fr
from pathlib import Path
import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("wall", HERE / "lib_erdos1041_wall_engine.py")
wall = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(wall)
CB, cb, cb_pt, krawczyk = wall.CB, wall.cb, wall.cb_pt, wall.krawczyk
mp.mp.dps = 70


def cpow(z, n):
    out, base = cb(1), z
    while n:
        if n & 1:
            out = out * base
        base = base * base
        n >>= 1
    return out


def compact_coeffs(muC, wC, rC):
    om = cb(1) - rC
    return [
        cpow(rC, 15),
        cb(5) * cpow(rC, 10) * cpow(om, 2),
        cb(10) * cpow(rC, 5) * cpow(om, 4),
        (cb(10) + muC) * cpow(om, 6),
        cb(0),
        -wC,
    ]


def compact_dcoeffs(cs):
    return [cb(5)*cs[0], cb(4)*cs[1], cb(3)*cs[2], cb(2)*cs[3], cs[4]]


def Gmp(r, y, mu, ray):
    om = 1-r
    return (r**15*y**5 + 5*r**10*om**2*y**4 + 10*r**5*om**4*y**3
            +(10+mu)*om**6*y**2-ray)


def Gymp(r, y, mu):
    om = 1-r
    return (5*r**15*y**4 + 20*r**10*om**2*y**3 + 30*r**5*om**4*y**2
            +2*(10+mu)*om**6*y)


def scout(r, y, mu, ray):
    for _ in range(50):
        step = Gmp(r, y, mu, ray) / Gymp(r, y, mu)
        y -= step
        if abs(step) < mp.mpf("1e-55") * max(1, abs(y)):
            break
    return y


def certified_arm(muC, wC, mu, ray, sign, *, cells=2048, k=16):
    if k != 16:
        raise ValueError("the current exact schedule uses k=16")
    rmax = Fr(4, 5)
    rb = [rmax * Fr(j*j, cells*cells) for j in range(cells+1)]
    y = sign * mp.sqrt(ray/(10+mu))
    yterm = y
    for endpoint in rb[1:]:
        rm = mp.mpf(endpoint.numerator)/endpoint.denominator
        yterm = scout(rm, yterm, mu, ray)
    etaC = wall.fifth_root_of_w(wC, ray, yterm)

    total = Fr(0)
    yleft = y
    xleftC = cb(0)
    monotone_cells = direct_cells = 0
    max_radius = 0.0
    for j in range(cells):
        ra, rc = rb[j], rb[j+1]
        mid = (ra+rc)/2
        rm = mp.mpf(mid.numerator)/mid.denominator
        ctrmp = scout(rm, yleft, mu, ray)
        rend = mp.mpf(rc.numerator)/rc.denominator
        yright = scout(rend, ctrmp, mu, ray)
        variation = max(abs(ctrmp-yleft), abs(yright-ctrmp), mp.mpf("1e-25"))
        rC = CB(mid, Fr(0), (rc-ra)/2, _raw=True)
        cs = compact_coeffs(muC, wC, rC)
        Y = None
        candidate_radii = [
            Fr(mp.nstr(variation * grow, 40))
            for grow in (2, 4, 8, 16, 40, 100)
        ]
        candidate_radii.extend((
            Fr(1, 10**12), Fr(1, 10**10), Fr(1, 10**8),
            Fr(1, 10**6), Fr(1, 10**4), Fr(1, 10**3), Fr(1, 10**2),
        ))
        for root_radius in candidate_radii:
            Y = krawczyk(cs, compact_dcoeffs(cs), cb(0), cb_pt(ctrmp),
                         root_radius, iters=25)
            if Y is not None:
                break
        if Y is None:
            raise RuntimeError(f"compact Krawczyk failure at cell {j}")
        max_radius = max(max_radius, float(Y.r))
        om = cb(1)-rC
        Gy = (
            cb(5)*cpow(rC,15)*cpow(Y,4)
            +cb(20)*cpow(rC,10)*cpow(om,2)*cpow(Y,3)
            +cb(30)*cpow(rC,5)*cpow(om,4)*cpow(Y,2)
            +cb(2)*(cb(10)+muC)*cpow(om,6)*Y
        )
        Gr = (
            cb(15)*cpow(rC,14)*cpow(Y,5)
            +cb(50)*cpow(rC,9)*cpow(om,2)*cpow(Y,4)
            -cb(10)*cpow(rC,10)*om*cpow(Y,4)
            +cb(50)*cpow(rC,4)*cpow(om,4)*cpow(Y,3)
            -cb(40)*cpow(rC,5)*cpow(om,3)*cpow(Y,3)
            -cb(6)*(cb(10)+muC)*cpow(om,5)*cpow(Y,2)
        )
        if Gy.contains_zero():
            raise RuntimeError(f"G_y contains zero at cell {j}")
        scale = cpow(rC,5)/cpow(om,2)
        scale_prime = cb(5)*cpow(rC,4)/cpow(om,2)+cb(2)*cpow(rC,5)/cpow(om,3)
        velocity = scale_prime*Y-scale*Gr/Gy
        rotated = etaC.conj()*velocity
        re_lo = rotated.re_lo()
        im_hi = abs(rotated.b)+rotated.r

        rpoint = cb(rc)
        node_cs = compact_coeffs(muC, wC, rpoint)
        Yn = None
        for node_radius in (
            Fr(1, 10**18), Fr(1, 10**12), Fr(1, 10**10),
            Fr(1, 10**8), Fr(1, 10**6), Fr(1, 10**4),
            Fr(1, 10**3), Fr(1, 10**2),
        ):
            Yn = krawczyk(
                node_cs, compact_dcoeffs(node_cs), cb(0), cb_pt(yright),
                node_radius, iters=30,
            )
            if Yn is not None:
                break
        if Yn is None:
            raise RuntimeError(f"endpoint Krawczyk failure at cell {j}")
        xrightC = cpow(rpoint,5)/cpow(cb(1)-rpoint,2)*Yn
        qleft, qright = etaC.conj()*xleftC, etaC.conj()*xrightC
        dv = wall.snap_up(abs(qright.b-qleft.b)+qright.r+qleft.r)
        denominator = wall.snap_dn(rotated.abs_lo()+re_lo)
        if abs(rotated.b) > rotated.r and denominator > 0:
            tau = wall.snap_up(im_hi/denominator)
            total = wall.snap_up(total+tau*dv)
            monotone_cells += 1
        else:
            if re_lo > 0:
                defect = wall.snap_up(im_hi*im_hi/(2*re_lo))
            else:
                defect = wall.snap_up(rotated.abs_hi()-rotated.re_lo())
            total = wall.snap_up(total+defect*(rc-ra))
            direct_cells += 1
        xleftC, yleft = xrightC, yright

    rC = cb(rmax)
    cs = compact_coeffs(muC, wC, rC)
    Y = None
    for terminal_radius in (
        Fr(1, 10**20), Fr(1, 10**12), Fr(1, 10**10),
        Fr(1, 10**8), Fr(1, 10**6), Fr(1, 10**4),
        Fr(1, 10**3), Fr(1, 10**2),
    ):
        Y = krawczyk(
            cs, compact_dcoeffs(cs), cb(0), cb_pt(yterm),
            terminal_radius, iters=40,
        )
        if Y is not None:
            break
    if Y is None:
        raise RuntimeError("terminal compact root failure")
    scale = cpow(rC,5)/cpow(cb(1)-rC,2)
    yS = cb(1)+scale*Y
    tail, _, _, _, diag = wall.tail_bound(muC, wC, yS, k, etaC)
    upper = wall.snap_up(total+tail-etaC.re_lo())
    return upper, {
        "support": float(total), "tail": float(tail),
        "eta": complex(float(etaC.a), float(etaC.b)),
        "monotone_cells": monotone_cells, "direct_cells": direct_cells,
        "max_root_radius": max_radius, "tail_diag": diag,
    }


def certified_carrier_input(kappa=Fr(1,1000), scout_mu=None):
    ks, ms = sp.symbols("ks ms")
    A = 4*(ms+4)
    B = -sp.Rational(12,25)*(3*ms**3-5*ms**2-100*ms-200)
    C = sp.Rational(4,3125)*(ms+10)**3*(27*ms**2+140*ms+200)
    K = sp.expand(C**2*(1+ks)**3-A*B*C*ks*(1+ks)*(1+4*ks)
                  +(A**3*C+B**3)*ks**2*(1+2*ks)-A**2*B**2*ks**3)
    kval = sp.Rational(kappa.numerator, kappa.denominator)
    poly = sp.Poly((5**10*K).subs(ks,kval), ms)
    def fq(value):
        value = sp.Rational(value)
        return Fr(int(value.p), int(value.q))
    cs = [cb(fq(value)) for value in poly.all_coeffs()]
    ds = [cb(len(cs)-1-i)*cs[i] for i in range(len(cs)-1)]
    if scout_mu is None:
        scout_mu = mp.mpc("-13.1212742475737509640", "1.7637790106989752208")
    else:
        scout_mu = mp.mpc(scout_mu)
    muC = None
    for radius in (Fr(1,10**4), Fr(1,10**6), Fr(1,10**8), Fr(1,10**10), Fr(1,10**12)):
        muC = krawczyk(cs, ds, cb(0), cb_pt(scout_mu), radius, iters=60)
        if muC is not None:
            break
    if muC is None:
        raise RuntimeError("carrier root not isolated")
    Ac = cb(4)*(muC+cb(4))
    Bc = -cb(Fr(12,25))*(cb(3)*cpow(muC,3)-cb(5)*cpow(muC,2)-cb(100)*muC-cb(200))
    Cc = cb(Fr(4,3125))*cpow(muC+cb(10),3)*(cb(27)*cpow(muC,2)+cb(140)*muC+cb(200))
    kc = cb(kappa)
    Dc = cpow(Ac,2)*kc-Bc*(cb(1)+kc)
    pair_sum = (Cc*cpow(cb(1)+kc,2)-Ac*Bc*cpow(kc,2))/(kc*Dc)
    third = -Ac-pair_sum
    cross = pair_sum.conj()*third
    if abs(cross.b) <= cross.r:
        raise RuntimeError("wall orientation not separated")
    epsilon = -1 if cross.b > 0 else 1
    p2 = pair_sum.cabs2()
    plo, phi = wall.sqrt_lo(p2)-pair_sum.r, wall.sqrt_hi(p2)+pair_sum.r
    if plo <= 0:
        raise RuntimeError("pair direction contains zero")
    pabs = CB((plo+phi)/2, Fr(0), wall.snap_up((phi-plo)/2), _raw=True)
    wC = cb(0,-epsilon)*pair_sum*pabs.inv()
    mu = mp.mpc(mp.mpf(muC.a.numerator)/muC.a.denominator,
                 mp.mpf(muC.b.numerator)/muC.b.denominator)
    pc = mp.mpc(mp.mpf(pair_sum.a.numerator)/pair_sum.a.denominator,
                mp.mpf(pair_sum.b.numerator)/pair_sum.b.denominator)
    ray = -epsilon*1j*pc/abs(pc)
    return muC, wC, mu, ray, {
        "mu_radius": float(muC.r), "w_radius": float(wC.r),
        "epsilon": epsilon, "cross_margin": float(abs(cross.b)-cross.r),
    }


def certified_anchor(*, cells=2048):
    muC, wC, mu, ray, carrier = certified_carrier_input()
    arms = [certified_arm(muC,wC,mu,ray,sign,cells=cells) for sign in (+1,-1)]
    pair_upper = wall.snap_up(arms[0][0]+arms[1][0])
    return {"kappa": Fr(1,1000), "pair_upper": pair_upper,
            "pair_upper_float": float(pair_upper), "carrier": carrier,
            "mu": complex(mu), "ray": complex(ray), "arms": arms}


FIBRE_SCOUTS = {
    Fr(1, 1000): (
        mp.mpc("-13.12127424757375097043755867279047784656", "1.76377901069897525968778217076855093021"),
        mp.mpc("-9.082137048116788472930623652570650238063", "2.625541382979332067937211071453009919332"),
        mp.mpc("-7.880705587867320304930932599670560050000", "1.198249126945302297240876772991495156792"),
        mp.mpc("-2.592198006545754656561356351993483799740", "0.828047262913982243263440956689130278311"),
        mp.mpc("-2.591121129078161517677187027363904180489", "0.827702067212076888824660802729669979361"),
    ),
    Fr(-1, 1000): (
        mp.mpc("-12.47621333187578414517922621793886334788763850913874568548312835234249", "2.47296147674894750873135108490604505405187931422494145797671285575017"),
        mp.mpc("-9.680892796383412177553943753531487423309159434136052522823606272737501", "2.911086621327652138346889834833292571945122703743036347001462970535925"),
        mp.mpc("-7.756609085514772013211557240854045725579943658728185433890369549269475", "0.7745175470449346981912143854778216691439144736415514552407884472965475"),
        mp.mpc("-2.594065518476915859021195387346803854894703067743947302947785788495267", "0.828642616739996599870579409211827118932146229608577922309672617200859"),
        mp.mpc("-2.592986953604391752905122871476875904014923631738990663401846214024082", "0.8282992828282814177846853683100646794256778839164125783828513302610442"),
    ),
}


def certified_full_fibre(*, kappa=Fr(1, 1000), weak_cells=2048):
    """Certify all five upper carrier roots at either cusp-collar anchor."""
    if kappa not in FIBRE_SCOUTS:
        raise ValueError("full-fibre scouts are available only at kappa=+-1/1000")
    rows = []
    roots = []
    for index, root_scout in enumerate(FIBRE_SCOUTS[kappa]):
        muC, wC, mu, ray, carrier = certified_carrier_input(
            kappa, scout_mu=root_scout)
        roots.append(muC)
        if index == 0:
            cells = weak_cells
            arms = [certified_arm(muC,wC,mu,ray,sign,cells=cells) for sign in (+1,-1)]
            upper = wall.snap_up(arms[0][0]+arms[1][0])
            method = "support_stieltjes"
        else:
            cells = None
            point = wall.certified_excess(
                mu, ray, muC=muC, wC=wC, k=20, s0=Fr(1,10**10),
                ratio=.06, msub=6, eps_step=Fr(1,10**7), want_grad=False)
            arms = point["arms"]
            upper = point["hi"]
            method = "oriented_arclength"
        rows.append({"index": index, "muC": muC, "mu": complex(mu),
                     "ray": complex(ray), "carrier": carrier, "cells": cells,
                     "arms": arms, "method": method, "pair_upper": upper,
                     "pair_upper_float": float(upper)})
    disjoint = all((roots[i]-roots[j]).abs_lo()>0
                   for i in range(len(roots)) for j in range(i))
    return {"kappa": kappa, "rows": rows,
            "upper_roots_disjoint": disjoint}
