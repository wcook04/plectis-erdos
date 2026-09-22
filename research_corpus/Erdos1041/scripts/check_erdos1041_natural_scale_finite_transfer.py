#!/usr/bin/env python3
"""Exact budgets and optional actual-polynomial regression for the sextic transfer.

The note contains the analytic proof. Exact budgets are rational arithmetic;
the optional mpmath root experiment is explicitly finite numerical evidence.
"""
import argparse
from fractions import Fraction as F
import json


def budgets():
    delta=F(1,1000);u=F(1,200);R=32;r=F(1,10**6);rho_cap=F(1,10**18)
    checks={}
    checks['shifted_ray_selector']=(F(49152,9765625)*(1+2*delta)**10<F(13,25)**8)
    checks['two_negative_chord']=(u+500*u*u+u**5+delta*u<F(13,200))
    checks['one_small_endpoint_derivative']=(4*u+3000*u*u+12*u**5<F(39,200))
    checks['cubic_energy']=(12*20000<500**2)
    checks['fourier_inversion']=(5*20000*r**3+2*r*r+2*r+500<600)
    checks['fourth_mode']=(40000*r*r<=1)
    checks['fifth_mode']=(40000*r<=1)
    checks['root_angle_and_log_domains']=(100*r**3<F(1,3) and R*r<F(1,2))
    n_bound=R+R**2+500*R**3+2*R**4*r*r+2*R**5*r**4+20000*R**6*r**6
    checks['inner_N_bound']=(n_bound<20000000)
    gradient=1+2*R+1500*R**2+6*R**5
    checks['inner_model_gradient']=(gradient<300000000)
    # Divide the normalized error bound by rho, then use rho<=10^-6.
    error_per_rho=(48*10000*R+2*R**4*r+20000*R**3*r*r
                   +2*R**5*r**3
                   +(R**12+20000*R**6+40000000*R**6)*r**5
                   +3*R*100*300000000*r*r)
    checks['inner_error_constant']=(error_per_rho<10**9)
    checks['inner_strict_margin']=(10**9*rho_cap<delta*u*u/2)
    checks['intermediate_baseline']=(162*(100*r**3)**2+F(1,126)<F(1,100))
    intermediate=F(64,63)*(F(9,8*R**5)+F(3,2*R**4)+F(500,R**3)+20000*r**6)
    checks['intermediate_P']=(intermediate<F(1,50))
    checks['intermediate_anchor']=(F(480000,R**5)*r<F(1,100))
    checks['far_half']=(210*100*r**3<F(1,64))
    checks['actual_chord_angle']=(F(7,4)-6*100*r**3>0 and (F(7,4)-6*100*r**3)**2>3)
    # Exit from the earlier anisotropic low-mode cone implies Delta<=20000 rho^6.
    a=F(3,2048)
    checks['first_mode_exit_to_Delta_bound']=(a**6*20000**5>1)
    checks['second_mode_exit_to_Delta_bound']=(a**3*20000**2>1)
    assert all(checks.values()),checks
    return {'status':'pass','evidence_class':'exact_rational_absorption_checks_supporting_ordinary_proof',
            'checks':checks,'inner_model_margin':str(delta*u*u),
            'normalized_error_at_rho_cap':str(10**9*rho_cap),
            'rho_cap':str(rho_cap),'normalized_connector_radius':str(u)}


def actual_polynomial_probe(samples):
    import mpmath as mp
    mp.mp.dps=240
    omega=mp.exp(2j*mp.pi/6);roots0=[omega**j for j in range(6)]
    worst_inner=-mp.inf;worst_all=-mp.inf;count=0
    for case in range(samples):
        r=mp.mpf(10)**(-19-6*(case%2))
        alpha=(mp.mpf('0.521')+mp.mpf(case%7)/20)*mp.exp(1j*mp.pi*(case%13)/13)
        beta=mp.exp(2j*mp.pi*(case%17)/17)
        gamma=mp.mpf([0,300,-300,1,-1,100][case%6])
        coeff=[0,alpha*r**5,beta*r**4,1j*gamma*r**3,
               -mp.conj(beta)*r**4,-mp.conj(alpha)*r**5]
        angles=[mp.im(sum(coeff[m]*omega**(j*m) for m in range(6))/6) for j in range(6)]
        # Very small strict inward displacement; it does not supply the model margin.
        radials=[mp.mpf(j+1)*mp.mpf('1e-20')*r**6 for j in range(6)]
        local=[(1-radials[j])*mp.exp(1j*angles[j]) for j in range(6)]
        gauge=mp.exp(-1j*mp.arg(sum(local)))
        roots=[roots0[j]*local[j]*gauge for j in range(6)]
        e=[local[j]*gauge-1 for j in range(6)]
        E=[sum(e[j]*omega**(-j*m) for j in range(6)) for m in range(6)]
        rho=max(abs(E[1])**mp.mpf('.2'),abs(E[2])**mp.mpf('.25'))
        Delta=-mp.re(E[0]);A=E[1]/rho**5;B=E[2]/rho**4;C=mp.im(E[3])/rho**3
        assert rho<=mp.mpf('1e-18') and Delta<=20000*rho**6
        assert abs(A)>=mp.mpf(13)/25 and abs(B)<=1+mp.mpf('1e-180') and abs(C)<500
        scalar=4/mp.power(5,mp.mpf('1.25'));chosen=[]
        for j in range(3):
            first=mp.re(A*omega**j);second=mp.re(B*omega**(2*j))
            if abs(first)>=scalar*mp.power(max(second+mp.mpf('.001'),0),mp.mpf('1.25')):
                chosen.append(j if first<=0 else j+3)
        assert len(chosen)>=2
        i,j=chosen[:2];directions=[roots[k]/abs(roots[k]) for k in (i,j)]
        u=mp.mpf(1)/200
        def score(z,inner=False):
            nonlocal count,worst_inner,worst_all
            value=mp.fprod(z-a for a in roots)
            score=mp.log(abs(value))
            assert score<0,('positive_actual_polynomial_value',case,z,score)
            count+=1;worst_all=max(worst_all,score/rho**6)
            if inner:worst_inner=max(worst_inner,score/rho**6)
        for direction in directions:
            for h in range(49):
                t=u*mp.power(32/u,mp.mpf(h)/48)
                score(rho*t*direction,True)
            for h in range(33):
                t=32*rho*mp.power(mp.mpf('.5')/(32*rho),mp.mpf(h)/32)
                score(t*direction)
            for h in range(17):
                t=mp.mpf('.5')+mp.mpf(h)/34
                score(t*direction)
        for h in range(65):
            t=mp.mpf(h)/64;score(rho*u*((1-t)*directions[0]+t*directions[1]),True)
        length=abs(roots[i])+abs(roots[j])-2*rho*u+rho*u*abs(directions[0]-directions[1])
        assert length<2
    return {'evidence_class':'finite_240_digit_actual_polynomial_regression_not_proof',
            'samples':samples,'tested_path_points':count,'violations':0,
            'worst_inner_log_modulus_over_rho6':mp.nstr(worst_inner,18),
            'worst_all_log_modulus_over_rho6':mp.nstr(worst_all,18)}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--actual-probe',type=int,default=0)
    args=parser.parse_args();assert args.actual_probe>=0
    result=budgets()
    if args.actual_probe:result['finite_actual_probe']=actual_polynomial_probe(args.actual_probe)
    print(json.dumps(result,sort_keys=True))
