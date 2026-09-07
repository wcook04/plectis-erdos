#!/usr/bin/env python3
"""Exact compact-cell certificates and budgets for actual canonical-phase sextics.

--discover generates the rational radius witness table. Radius proposals use
floats, but every accepted cell is verified in Fraction arithmetic. Normal
verification reads that fixed table and has no numerical-search dependency.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import argparse
import hashlib
import json

CERT=Path(__file__).with_name('sextic_canonical_compact_cells.json')
LOW=F(1,16);HIGH=F(13,25);EPS=F(1,10**6)
SQLO=F(1732050807568,10**12);SQHI=F(1732050807569,10**12)


def chord_power(u,r,sign):
    sq=SQHI if sign==1 else SQLO
    re2=[F(1),F(-1),F(-1,2)]+[F(0)]*4
    re6=[F(1),F(-3),F(-15,2),F(20),F(-15,2),F(-3),F(1)]
    out=[-r*r*a-r**6*b for a,b in zip(re2,re6)]
    out[1]+=sign*u*(sq*r/2-F(9,2)*r**3)
    out[2]+=sign*u*F(9,2)*r**3
    return out


def positive_bernstein(power,depth=0):
    n=len(power)-1
    controls=[sum(power[i]*F(comb(k,i),comb(n,i)) for i in range(k+1)) for k in range(n+1)]
    def prove(b,d):
        if min(b)>=0:return 1
        if b[0]<0 or b[-1]<0 or d==18:return 0
        rows=[b]
        while len(rows[-1])>1:rows.append([(a+c)/2 for a,c in zip(rows[-1],rows[-1][1:])])
        left=[row[0] for row in rows];right=[row[-1] for row in rows[::-1]]
        l=prove(left,d+1)
        if not l:return 0
        r=prove(right,d+1)
        return l+r if r else 0
    return prove(controls,depth)


def verify_cell(lo,hi,r,sign):
    if not (LOW<=lo<hi<=HIGH and F(3,5)<=r<=F(6,5)):return 0
    leaves=0
    for u in [lo,hi]:
        p=[-x for x in chord_power(u,r,sign)];p[0]-=EPS
        n=positive_bernstein(p)
        if not n:return 0
        sq=SQHI if sign==1 else SQLO
        if sign*u*sq*r/2+r*r/2-r**6>-EPS:return 0
        leaves+=n
    return leaves


def verify_cells():
    assert SQLO*SQLO<3<SQHI*SQHI
    d=json.loads(CERT.read_text());assert d['schema']=='sextic_canonical_compact_cells_v1'
    assert d['margin']==str(EPS);leaves=0;count=0
    for sign in [1,-1]:
        prev=LOW
        for row in d['cells'][str(sign)]:
            lo,hi,r=map(F,row);assert lo==prev
            n=verify_cell(lo,hi,r,sign);assert n,(sign,row)
            leaves+=n;count+=1;prev=hi
        assert prev==HIGH
    return {'status':'pass','cell_count':count,'accepted_chord_bernstein_leaves':leaves,
            'uniform_margin':str(EPS),'certificate_sha256':hashlib.sha256(CERT.read_bytes()).hexdigest()}


def discover():
    import numpy as np
    radii=np.arange(600,1201)/1000;t=np.linspace(0,1,257)
    w=1-t+t*np.exp(1j*np.pi/3)
    even=-radii[:,None]**2*(w*w).real-radii[:,None]**6*(w**6).real
    odd=(np.sqrt(3)*radii[:,None]*t[None,:]/2-F(9,2).__float__()*radii[:,None]**3*(t-t*t)[None,:])
    cells={}
    for sign in [1,-1]:
        out=[];pending=[(LOW,HIGH)]
        while pending:
            lo,hi=pending.pop();mid=float((lo+hi)/2)
            score=(even+sign*mid*odd).max(axis=1)
            ray=sign*mid*np.sqrt(3)*radii/2+radii*radii/2-radii**6
            idx=np.argmin(np.maximum(score,ray));r=F(int(round(radii[idx]*1000)),1000)
            if verify_cell(lo,hi,r,sign):out.append([str(lo),str(hi),str(r)])
            else:
                assert hi-lo>F(1,10**6),('discovery_failed',sign,lo,hi,r)
                mid=(lo+hi)/2;pending.extend([(mid,hi),(lo,mid)])
        cells[str(sign)]=out
    CERT.write_text(json.dumps({'schema':'sextic_canonical_compact_cells_v1','margin':str(EPS),
                               'coefficient_interval':[str(LOW),str(HIGH)],'cells':cells},indent=2)+'\n')


def budgets():
    import sympy as s
    from check_erdos1041_canonical_critical_threshold import exact,bernstein
    from check_erdos1041_natural_scale_finite_transfer import budgets as common_budgets
    h,k,x=s.symbols('h k x',real=True);D=5+25*k-13*k*k-k**3;Y=(3*k+1)/(3*D)
    U=2*(k-1)*(k+1)*(-k*k+8*k+1)/D
    Rpoly=k**6+54*k**5-265*k**4+564*k**3+495*k*k+150*k+25
    def positive(poly,lo=s.Rational(3,4),hi=s.Rational(361,300)):
        _,bs=bernstein(s.expand(poly.subs(k,lo+(hi-lo)*x)),[x]);return all(v>=0 for v in bs)
    checks={'D_lower':positive(D-10),'D_upper':positive(20-D),
      'Y_lower':positive(20*(3*k+1)-3*D), 'Y_upper':positive(3*D-(3*k+1)),
      'R_upper':positive(3000-Rpoly),
      'N_lower':positive(-15*k**3+51*k*k+23*k+5-40),
      'negative_u_range':bool((U**4*Y).subs(k,s.Rational(3,4))>s.Rational(1,16)**4) and U.subs(k,s.Rational(3,4))<0,
      'positive_u_range':bool((U**4*Y).subs(k,s.Rational(361,300))>s.Rational(1,16)**4) and U.subs(k,s.Rational(361,300))>0}
    p=F(1,10**6);rho_cap=F(1,10**20);R=32
    checks.update({
      'curvature_floor':F(4*40*10,27*3000)>F(1,100),
      'square_floor':F(1,5)*8*16/(6*27*20)>F(1,200),
      'quartic_contact_floor':F(1,20)*F(5,9)>=F(1,36),
      'quartic_absorption':3200*p*p<F(1,72),
      'end_interval_margin':F(1,200)*F(3,40)**2-2*p*p>F(1,40000),
      'adaptive_outer_margin':p*p/144+F(1,100000)<F(1,40000),
      'critical_endpoint_floor':F(1,5)*F(5,2)*F(1,4)*16/(6*27*20)>F(1,2000),
      'critical_ray_correction':F(1,2000)-p*p*R**4>F(1,2500),
      'adaptive_margin':F(1,200*2*100000)==F(1,40000000),
      'central_cubic_floor':F(3,2)*F(17,10)*F(1,8)*F(7,64)>F(1,32),
      'central_cubic_enough':F(1,32)>F(1,100000),
      'compact_ray_monotonicity':F(3,5)**4>F(1,10),
      'compact_radius':F(6,5)<2,
      'actual_length':F(1,2)*F(3,4)>F(1,4),
    })
    # The critical radii exceed 1/2. On the central t interval their cubic
    # shape is at least 1/32; this is more than the adaptive coefficient.
    # c <= sqrt(3)u + d, d<=501. For M=rho^2+u^2+min(d,1)+abs(a):
    # (c+rho)^2/M<=1,100,000; (c+rho)/M<=503/rho;
    # abs(A)/M<=2/rho, using u/(rho^2+u^2)<=1/(2rho).
    error=(48*R*1100000+40000*R**4*p+20000*R**3+2*R**5*p*p
           +40000*R**5*p*p+(20000*R**6+R**12+40000000*R**6)*p**3
           +3*R*300000000*503*p)
    checks['adaptive_error_constant']=error<10**10
    checks['small_u_actual_absorption']=10**10*rho_cap<F(1,80000000)
    checks['compact_actual_absorption']=10**9*rho_cap<EPS/2
    assert all(checks.values()),checks
    return {'status':'pass','checks':{k:bool(v) for k,v in checks.items()},
            'rho_cap':str(rho_cap),'small_u_model_margin':'M/40000000',
            'critical_family_dependency':exact()['status'],'common_outer_arm_dependency':common_budgets()['status']}


def actual_probe(count):
    import mpmath as m
    m.mp.dps=300;om=m.exp(1j*m.pi/3);table=json.loads(CERT.read_text())['cells']
    points=0;worst=-m.inf;branches={'small_u':0,'compact':0}
    def frac(v):
        q=F(v);return m.mpf(q.numerator)/q.denominator
    def family(h):
        k=h*h/3;D=5+25*k-13*k*k-k**3;Y=(3*k+1)/(3*D)
        U=2*(k-1)*(k+1)*(-k*k+8*k+1)/D;y=m.root(Y,4)
        return y*U,y*(h+1)/m.sqrt(3)
    def radius_for(u):
        lo=m.mpf('1.5');hi=m.mpf('1.9')
        for _ in range(250):
            mid=(lo+hi)/2
            if family(mid)[0]<u:lo=mid
            else:hi=mid
        return family((lo+hi)/2)[1]
    for case in range(count):
        seed=m.mpf(10)**(-22-5*(case%2))
        uv=[m.mpf(0),seed,m.mpf('.02'),m.mpf('.0624'),m.mpf('.0626'),m.mpf('.1'),m.mpf('.24'),m.mpf('.49')][case%8]
        av=[m.mpf(0),m.mpf('.1'),m.mpf('-.1')][case%3]
        C0=[m.sqrt(3)*uv,m.sqrt(3)*uv+seed**2,m.sqrt(3)*uv-seed**2,m.mpf('-.5'),m.mpf(300),m.mpf(-300),m.mpf(0)][case%7]
        A0=av-1j*uv;inward=m.mpf('1e-30')*seed**8
        def configuration(theta):
            B0=-m.exp(1j*theta)
            coeff=[0,A0*seed**5,B0*seed**4,1j*C0*seed**3,-m.conj(B0)*seed**4,-m.conj(A0)*seed**5]
            angles=[m.im(sum(coeff[k]*om**(j*k) for k in range(6))/6) for j in range(6)]
            local=[(1-inward)*m.exp(1j*x) for x in angles]
            gauge=m.exp(-1j*m.arg(sum(local)));local=[z*gauge for z in local]
            e=[z-1 for z in local]
            E=[sum(e[j]*om**(-j*k) for j in range(6)) for k in range(6)]
            return [om**j*local[j] for j in range(6)],E
        theta=m.findroot(lambda q:m.im(configuration(q)[1][2])/seed**4,(0,m.mpf('1e-6')),tol=m.mpf('1e-230'))
        roots,E=configuration(theta);rho=m.root(abs(E[2]),4);A=E[1]/rho**5;B=E[2]/rho**4;C=m.im(E[3])/rho**3
        assert rho<=m.mpf('1e-20') and -m.re(E[0])<=20000*rho**6
        assert abs(A)<m.mpf(13)/25 and abs(C)<500 and abs(B+1)<m.mpf('1e-180')
        conjugate=m.im(A)>0;Aw=m.conj(A) if conjugate else A;Cw=-C if conjugate else C
        u=-m.im(Aw);a=m.re(Aw);sign=1 if Cw>=m.sqrt(3)*u else -1
        if u<=m.mpf(1)/16:
            r=radius_for(sign*u);branches['small_u']+=1
            scale=rho**6*(rho**2+u*u+min(abs(Cw-m.sqrt(3)*u),1)+abs(a))
        else:
            row=next(row for row in table[str(sign)] if frac(row[0])<=u<=frac(row[1]))
            r=frac(row[2]);branches['compact']+=1;scale=rho**6
        ends=[sign,sign*om]
        if a*m.re(ends[0])>0:ends=[-m.conj(z) for z in ends]
        if conjugate:ends=[m.conj(z) for z in ends]
        indices=[int(m.nint(m.arg(z)/(m.pi/3)))%6 for z in ends]
        directions=[roots[j]/abs(roots[j]) for j in indices]
        def score(z):
            nonlocal points,worst
            value=m.log(abs(m.fprod(z-a for a in roots)))
            assert value<0,('actual_path_violation',case,z,value)
            points+=1;worst=max(worst,value/scale)
        for k in range(97):
            t=m.mpf(k)/96;score(rho*r*((1-t)*directions[0]+t*directions[1]))
        for direction,j in zip(directions,indices):
            for k in range(33):score(rho*r*(32/r)**(m.mpf(k)/32)*direction)
            for k in range(25):score(32*rho*(m.mpf('.5')/(32*rho))**(m.mpf(k)/24)*direction)
            for k in range(17):score((m.mpf('.5')+(abs(roots[j])-m.mpf('.5'))*m.mpf(k)/16)*direction)
        length=sum(abs(roots[j]) for j in indices)-2*rho*r+rho*r*abs(directions[0]-directions[1])
        assert length<2-rho/4
    return {'evidence_class':'finite_300_digit_actual_root_regression_not_proof','cases':count,'branches':branches,
            'tested_points':points,'violations':0,'worst_scaled_log_modulus':m.nstr(worst,20),
            'canonical_phase_tolerance':'1e-180; numerical phase adjustment is regression only'}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--discover',action='store_true');p.add_argument('--actual-probe',type=int,default=0)
    args=p.parse_args()
    if args.discover:discover()
    out={'evidence_class':'exact_certificate_and_rational_budgets_supporting_ordinary_proof',
         'compact_cells':verify_cells(),'budgets':budgets()}
    assert args.actual_probe>=0
    if args.actual_probe:out['finite_actual_probe']=actual_probe(args.actual_probe)
    print(json.dumps(out,sort_keys=True))
