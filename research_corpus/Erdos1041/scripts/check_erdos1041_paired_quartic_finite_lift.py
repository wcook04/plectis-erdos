#!/usr/bin/env python3
"""Exact identities/budgets for the paired-quartic finite sextic lift.

The analytic theorem is in SexticPairedQuarticFiniteLift.md. The optional
actual-root probe is finite high-precision regression, not proof.
"""
import argparse
from fractions import Fraction as F
import json


def exact_checks():
    import sympy as s
    t=s.symbols('t',real=True);v=s.symbols('v',real=True);rt=s.sqrt(3)
    q=(7+4*rt)/27;w=1-t/2+s.I*rt*t/2;contact=rt-1
    re=lambda z:s.expand(s.re(s.expand_complex(z)))
    carrier=re(w**2)+q*re(w**6)
    quotient,remainder=s.div(carrier,(t-contact)**2,t,extension=rt)
    assert s.simplify(remainder)==0
    floor=s.Poly(quotient-s.Rational(1,5),t)
    n=floor.degree();power=[floor.nth(i) for i in range(n+1)]
    bern=[s.simplify(sum(power[i]*s.binomial(k,i)/s.binomial(n,i) for i in range(k+1))) for k in range(n+1)]
    checks={'canonical_square_floor':all(bool(x>0) for x in bern),
            'quartic_contact':s.simplify(q*re(w**4).subs(t,contact))==-s.Rational(1,3),
            'radius_squared_lower_bound':bool(q>s.Rational(49,100)),
            'radius_cubed_lower_bound':bool(q**3>s.Rational(1,16)),
            'radial_gap':bool(q-s.Rational(1,2)>s.Rational(1,64)),
            'contact_separation':bool(2-rt>s.Rational(1,4)),
            'cubic_chord_identity':s.simplify(s.im(s.expand(w**3))-3*rt*t*(1-t)/2)==0}
    # phase reduction: with h=pi/3-2*arg(z), the rotated effective
    # coefficient has imaginary part -|z|^2 sin(h)(1-2 delta |z|^2 cos(h)).
    h=s.symbols('h',real=True)
    checks['phase_wedge_identity']=s.trigsimp(s.sin(s.pi-2*h)-2*s.sin(h)*s.cos(h))==0
    p=F(1,10**6);R=32;dcap=p*p
    checks.update({
      'quartic_square_absorption':F(200,7)*dcap<F(1,12),
      'outer_chord_margin':F(7,3200)-dcap>F(1,500),
      'central_cubic_floor':F(3,2)*F(17,10)*F(1,2)*F(7,64)>F(1,8),
      'outer_adaptive_margin':dcap/8+F(1,2000)<F(1,500),
      'linear_adaptive_margin':F(1,2000)-F(1,10000)>=F(1,2500),
      'sharp_eta_inversion':2+2*p+100000*p*p<6,
      'ray_margin':F(7,640)-F(2*R,10000)-dcap*R**4>F(1,250),
      'ray_dominates_adaptive_margin':F(1,250)>F(2,2500),
      'gradient':1+2*R+1500*R**2+4*dcap*R**3+6*R**5<300000000,
      'metric_gap':F(4,5)*F(3,4)>F(1,2),
    })
    error=(48*R*500002+40000*R**4*p+20000*R**3
           +F(R**5,10000)*p**3+40000*R**5*p*p
           +(20000*R**6+R**12+40000000*R**6)*p**3
           +3*R*300000000*501*p)
    checks['adaptive_error_constant']=error<10**10
    checks['finite_error_absorption']=F(10**10,10**18)<F(1,5000)
    # The common outer-arm estimates are exactly those of the first-mode
    # finite transfer, and use no lower bound on the first-mode amplitude.
    from check_erdos1041_natural_scale_finite_transfer import budgets
    common=budgets()['checks']
    for name in ['cubic_energy','fourier_inversion','fourth_mode','fifth_mode',
                 'root_angle_and_log_domains','inner_N_bound','intermediate_baseline',
                 'intermediate_P','intermediate_anchor','far_half']:
        checks['common_'+name]=common[name]
    assert all(checks.values()),checks
    return {'status':'pass','evidence_class':'exact_symbolic_identities_and_rational_bounds_supporting_ordinary_proof',
            'checks':checks,'quartic_value_at_canonical_contact':'-1/3',
            'adaptive_margin':'(rho^2+min(abs(C),1))/2500',
            'normalized_error_bound':'10^10 rho (rho^2+min(abs(C),1))'}


def actual_probe(samples):
    import mpmath as m
    m.mp.dps=300;om=m.exp(1j*m.pi/3);r0=((7+4*m.sqrt(3))/27)**m.mpf('.25')
    worst=-m.inf;points=0;minimum_hypothesis_slack=m.inf
    for case in range(samples):
        seed=m.mpf(10)**(-19-6*(case%2))
        C0=[m.mpf(0),seed**2,-seed**2,m.mpf(1),m.mpf(-1),m.mpf(300),m.mpf(-300)][case%7]
        M0=seed**2+min(abs(C0),1)
        A0=(0 if case%3==0 else M0/20000)*m.exp(1j*m.pi*(case%11)/11)
        phase=[m.pi,m.pi/3,m.pi/2,2*m.pi/3,m.pi+m.mpf('1e-12')][case%5]
        B0=m.exp(1j*phase)
        coeff=[0,A0*seed**5,B0*seed**4,1j*C0*seed**3,-m.conj(B0)*seed**4,-m.conj(A0)*seed**5]
        angles=[m.im(sum(coeff[k]*om**(j*k) for k in range(6))/6) for j in range(6)]
        inward=m.mpf('1e-30')*seed**8
        local=[(1-inward)*m.exp(1j*x) for x in angles]
        gauge=m.exp(-1j*m.arg(sum(local)));local=[z*gauge for z in local]
        roots=[om**j*local[j] for j in range(6)];e=[z-1 for z in local]
        E=[sum(e[j]*om**(-j*k) for j in range(6)) for k in range(6)]
        rho=abs(E[2])**m.mpf('.25');A=E[1]/rho**5;B=E[2]/rho**4;C=m.im(E[3])/rho**3
        M=rho**2+min(abs(C),1);Delta=-m.re(E[0])
        assert 0<rho<=m.mpf('1e-18') and Delta<=20000*rho**6
        assert abs(A)<=M/10000 and abs(C)<500
        minimum_hypothesis_slack=min(minimum_hypothesis_slack,1-10000*abs(A)/M)
        candidates=[]
        for j in range(6):
            theta=m.arg(B*om**(2*j))
            if theta>=m.pi/3-m.mpf('1e-200') and theta<=m.pi+m.mpf('1e-200') and C*((-1)**j)>=0:
                candidates.append(j)
        assert candidates,(case,B,C)
        j=candidates[0];dirs=[roots[k%6]/abs(roots[k%6]) for k in [j,j+1]]
        def score(z):
            nonlocal worst,points
            val=m.log(abs(m.fprod(z-a for a in roots)))
            assert val<0,('positive_actual_value',case,z,val)
            worst=max(worst,val/(rho**6*M));points+=1
        params=[m.mpf(k)/96 for k in range(97)]+[m.sqrt(3)-1,2-m.sqrt(3)]
        for t in params:score(rho*r0*((1-t)*dirs[0]+t*dirs[1]))
        for direction in dirs:
            for k in range(33):score(rho*r0*(32/r0)**(m.mpf(k)/32)*direction)
            for k in range(25):score(32*rho*(m.mpf('.5')/(32*rho))**(m.mpf(k)/24)*direction)
            for k in range(17):score((m.mpf('.5')+m.mpf(k)/34)*direction)
        length=abs(roots[j])+abs(roots[(j+1)%6])-2*rho*r0+rho*r0*abs(dirs[0]-dirs[1])
        assert length<=2-rho/2
    return {'evidence_class':'finite_300_digit_actual_polynomial_regression_not_proof','samples':samples,
            'tested_path_points':points,'violations':0,'worst_log_modulus_over_rho6_M':m.nstr(worst,20),
            'minimum_relative_first_mode_hypothesis_slack':m.nstr(minimum_hypothesis_slack,15)}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--actual-probe',type=int,default=0)
    a=p.parse_args();assert a.actual_probe>=0
    result=exact_checks()
    if a.actual_probe:result['finite_actual_probe']=actual_probe(a.actual_probe)
    print(json.dumps(result,sort_keys=True))
