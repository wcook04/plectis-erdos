#!/usr/bin/env python3
"""Exact certificate for the canonical sextic critical-threshold theorem.

Ordinary analytic proof: SexticCanonicalCriticalThreshold.md.
Optional finite model tests audit the construction, not universal validity.
"""
import argparse
import json
import sympy as s


def bernstein(poly, variables):
    p=s.Poly(poly,*variables);degrees=[p.degree(v) for v in variables]
    from itertools import product
    out=[]
    for index in product(*[range(n+1) for n in degrees]):
        value=0
        for powers in product(*[range(i+1) for i in index]):
            term=p.coeff_monomial(s.prod(v**a for v,a in zip(variables,powers)))
            for i,a,n in zip(index,powers,degrees):term*=s.binomial(i,a)/s.binomial(n,a)
            value+=term
        out.append(s.factor(value))
    return degrees,out


def exact():
    h,t,k,x=s.symbols('h t k x',real=True)
    D=5+25*k-13*k*k-k**3;Y=(3*k+1)/(3*D)
    U=2*(k-1)*(k+1)*(k*k-8*k-1)/(-D)
    V=2*(k-1)*(k*k-20*k-5)/(-3*D)
    z=(h+1)*(2-t+s.I*s.sqrt(3)*t)/(2*s.sqrt(3))
    re=lambda z:s.expand(s.re(s.expand_complex(z)))
    im=lambda z:s.expand(s.im(s.expand_complex(z)))
    sub={k:h*h/3};yy=Y.subs(sub);uu=U.subs(sub);vv=V.subs(sub)
    F=s.factor(uu*im(z)-re(z*z)-vv*im(z**3)-yy*re(z**6))
    T=h**6+39*h**4-225*h*h-135
    Q=s.cancel(F*6*T/((h+1)*((h+1)*t-2)**2))
    degrees,bs=bernstein(s.expand(Q.subs(h,1+x)),[x,t])
    checks={'chord_factorization':s.cancel(F-(h+1)*((h+1)*t-2)**2*Q/(6*T))==0,
            'chord_bernstein_positive':all(v>=16 for v in bs)}
    _,denbs=bernstein(s.expand((-T).subs(h,1+x)),[x])
    checks['denominator_positive']=all(v>0 for v in denbs)
    rfour=yy*(h+1)**4/9
    raynum=s.factor((rfour-s.Rational(1,10))*(-10*T)/(h-1))
    checks['ray_floor_factorization']=s.cancel(rfour-s.Rational(1,10)+(h-1)*raynum/(10*T))==0
    checks['ray_floor_positive_coefficients']=all(v>0 for v in s.Poly(raynum,h).all_coeffs())
    radiusnum=-T-(h*h+1)*(h+1)**4
    _,radiusbs=bernstein(s.expand(radiusnum.subs(h,1+s.Rational(9,10)*x)),[x])
    checks['radius_below_one_through_19_10']=all(v>0 for v in radiusbs)
    # Check the saddle equations without fractional powers: z=y(sqrt(k)+i),
    # u=y U, c=V/y, y^4=Y. Real critical equation divided by x, then
    # imaginary critical equation and real value divided by y and y^2.
    checks['critical_real']=s.factor(-2-6*V-6*Y*(k*k-10*k+5))==0
    checks['critical_imag']=s.factor(-U-2+3*V*(k-1)-6*Y*(5*k*k-10*k+1))==0
    checks['critical_value_zero']=s.factor(U-k+1-V*(3*k-1)-Y*(k**3-15*k*k+15*k-1))==0
    dup=s.factor(s.diff(U,k)+U*s.diff(Y,k)/(4*Y))
    R=k**6+54*k**5-265*k**4+564*k**3+495*k*k+150*k+25
    checks['u_derivative_factorization']=s.factor(dup-(3*k-1)*R/((3*k+1)*D*D))==0
    _,rbs=bernstein(s.expand(R.subs(k,s.Rational(1,3)+x)),[x])
    checks['u_derivative_positive']=all(v>0 for v in rbs)
    slope=1/(s.sqrt(Y)*(3*k-1))
    checks['threshold_slope_identity']=s.factor((s.diff(V,k)-V*s.diff(Y,k)/(4*Y))*(3*k-1)-dup)==0
    N=15*k**3-51*k*k-23*k-5
    checks['slope_log_derivative']=s.factor(-s.diff(Y,k)/(2*Y)-3/(3*k-1)-4*N/((3*k-1)*(3*k+1)*D))==0
    # For 1/3<=k<=4/3, 15k^3<=20k^2, so N<0.
    checks['concavity_sign_bound']=s.expand(N-(15*k-20)*k*k+31*k*k+23*k+5)==0
    gamma_second=s.simplify((s.diff(slope,k)/(Y**s.Rational(1,4)*dup)).subs(k,1))
    checks['origin_curvature']=s.simplify(gamma_second+s.sqrt(2)*3**s.Rational(3,4))==0
    checks['origin']=Y.subs(k,1)==s.Rational(1,12) and U.subs(k,1)==0 and V.subs(k,1)==0
    checks['negative_endpoint']=s.factor((U**4*Y).subs(k,s.Rational(1,3)))==s.Rational(128,28125) and U.subs(k,s.Rational(1,3))<0
    checks['positive_range_covers_endpoint']=bool((U**4*Y).subs(k,s.Rational(361,300))>s.Rational(128,28125)) and U.subs(k,s.Rational(361,300))>0
    # Exact scalar maximum: .5 t-t^5 <= (2/5) 10^(-1/4).
    v=s.symbols('v',positive=True)
    checks['scalar_maximum_factorization']=s.expand((t-v)**2*(t**3+2*v*t*t+3*v*v*t+4*v**3)-(t**5-5*v**4*t+4*v**5))==0
    checks['small_chord_budget']=s.Rational(1,8)+s.Rational(1,8)+s.Rational(6,16*256)<s.Rational(4,5)
    assert all(checks.values()),checks
    return {'status':'pass','evidence_class':'exact_symbolic_certificate_supporting_ordinary_analytic_proof',
            'checks':{a:bool(b) for a,b in checks.items()},'chord_bernstein_degree':degrees,
            'chord_bernstein_minimum':str(min(bs)),'chord_bernstein_coefficients':[str(v) for v in bs],
            'radius_bound_bernstein_minimum':str(min(radiusbs)),
            'threshold_curvature_at_origin':str(gamma_second)}


def stress(count):
    import mpmath as m
    m.mp.dps=90;om=m.exp(1j*m.pi/3);ustar=4/(5*m.sqrt(3)*m.root(10,4));worst=-m.inf
    def family(h):
        k=h*h/3;D=5+25*k-13*k*k-k**3;Y=(3*k+1)/(3*D)
        U=2*(k-1)*(k+1)*(k*k-8*k-1)/(-D)
        V=2*(k-1)*(k*k-20*k-5)/(-3*D);y=m.root(Y,4)
        return y*U,V/y,y*(h+1)/m.sqrt(3)
    def inverse(u):
        lo=m.mpf(1);hi=m.mpf('1.9')
        for _ in range(240):
            mid=(lo+hi)/2
            if family(mid)[0]<u:lo=mid
            else:hi=mid
        return family((lo+hi)/2)
    points=0
    for case in range(count):
        u=[m.mpf(0),m.mpf('0.000001'),m.mpf('.01'),m.mpf('.08'),ustar*m.mpf('.999'),ustar*m.mpf('1.001'),m.mpf('.52'),m.mpf(2)][case%8]
        a=[m.mpf(0),m.mpf('.3'),m.mpf('-.7')][case%3]
        C=[m.mpf(0),m.sqrt(3)*u,m.mpf('-.4'),m.mpf('.7'),m.mpf(30),m.mpf(-100)][case%6]
        A=a-1j*u;conjugated=(case%5==1)
        if conjugated:A=m.conj(A);C=-C
        Cwork=-C if conjugated else C
        if u>=ustar:
            r=min(m.mpf(1)/4,u/16,m.sqrt(u/(24*(1+abs(Cwork)))))
            endpoints=[-1,-om]
        else:
            _,cup,rup=inverse(u)
            if Cwork>=m.sqrt(3)*u:
                assert Cwork>=cup-m.mpf('1e-65')
                r=rup;endpoints=[1,om]
            else:
                _,cminus,r=inverse(-u);assert Cwork<=-cminus
                endpoints=[-1,-om]
        if a*m.re(endpoints[0])>0:endpoints=[-m.conj(z) for z in endpoints]
        if conjugated:endpoints=[m.conj(z) for z in endpoints]
        rot=case%3;B=-om**(-2*rot);Aactual=A*om**(-rot);Cactual=C*((-1)**rot)
        endpoints=[z*om**rot for z in endpoints]
        def value(z):return m.re(Aactual*z+B*z*z+1j*Cactual*z**3-z**6)
        for i in range(97):
            t=m.mpf(i)/96
            zs=[r*((1-t)*endpoints[0]+t*endpoints[1])]+[(r+(1-r)*t)*z for z in endpoints]
            for z in zs:
                vv=value(z);worst=max(worst,vv);points+=1
                assert vv<m.mpf('1e-65'),(case,z,vv)
        assert 0<r<1 and 2-r<2
    return {'evidence_class':'finite_90_digit_model_construction_regression_not_proof','cases':count,
            'tested_points':points,'violations':0,'worst_value':m.nstr(worst,20)}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--stress',type=int,default=0)
    a=p.parse_args();assert a.stress>=0;out=exact()
    if a.stress:out['finite_model_stress']=stress(a.stress)
    print(json.dumps(out,sort_keys=True))
