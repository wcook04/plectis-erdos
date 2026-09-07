#!/usr/bin/env python3
"""Exact algebra supporting SexticNaturalScaleRaySelector.md.

The universal inequalities and path construction are ordinary proofs in the
note. Optional float stress is finite evidence, never proof authority.
"""
import argparse
from fractions import Fraction as F
import json
import sympy as s


def exact_checks():
    t,v,a,b,c,d,x=s.symbols('t v a b c d x',real=True)
    root=s.sqrt(3)
    rotations=[s.Integer(1),s.Rational(1,2)+s.I*root/2,
               -s.Rational(1,2)+s.I*root/2]
    first=[s.expand(s.re((a+s.I*b)*w)) for w in rotations]
    second=[s.expand(s.re((c+s.I*d)*w*w)) for w in rotations]
    checks=[]
    for i in range(3):
        for j in range(i+1,3):
            sign=-1 if j-i==1 else 1
            assert s.expand(first[i]**2+first[j]**2+sign*first[i]*first[j]
                            -s.Rational(3,4)*(a*a+b*b))==0
            assert s.expand(second[i]**2+second[j]**2+second[i]*second[j]
                            -s.Rational(3,4)*(c*c+d*d))==0
            checks.extend([f'first_Gram_{i}_{j}',f'second_Gram_{i}_{j}'])
    assert s.expand(sum(second))==0
    checks.append('second_projections_sum_zero')
    assert s.expand(t**5-5*v**4*t+4*v**5
                    -(t-v)**2*(t**3+2*v*t*t+3*v*v*t+4*v**3))==0
    checks.append('global_radial_threshold_factorization')
    paired=-x*(t-t**5)+b*(t*t-t**4)-t**6
    assert s.expand(paired-t*(1-t**4)*(-x+b*t-t**5)
                    +b*t**4*(1-t*t)+t**10)==0
    checks.append('paired_ray_dominance_identity')
    eighth=F(4)**8/F(5)**10*F(3,4)
    assert eighth==F(49152,9765625)<F(13,25)**8<F(3,4)**8
    checks.append('exact_constant_and_comparison')
    # The sharpness construction solves two signed first projections.
    u,w=s.symbols('u w',positive=True)
    real=-u
    imaginary=(-u-2*w)/root
    assert s.expand(real*real+imaginary*imaginary
                    -s.Rational(4,3)*(u*u+w*w+u*w))==0
    checks.append('sharpness_prescribed_projection_norm')
    # An exact witness defeats the tempting smaller constant 1/2. Sign
    # decisions below reduce Q(sqrt(3)) to rational square comparisons.
    def positive_radical(expr):
        expr=s.expand(expr)
        rational=F(expr.coeff(root,0))
        radical=F(expr.coeff(root,1))
        assert s.expand(expr-rational-radical*root)==0
        if radical==0:
            return rational>0
        if rational>=0 and radical>0:
            return True
        if rational<=0 and radical<0:
            return False
        return (3*radical*radical>rational*rational if radical>0
                else rational*rational>3*radical*radical)
    specimen_a=-s.Rational(217,500)-s.I*s.Rational(259,1000)
    specimen_b=s.Rational(45,53)-s.I*s.Rational(28,53)
    assert s.expand(s.re(specimen_b)**2+s.im(specimen_b)**2)==1
    assert s.expand(s.re(specimen_a)**2+s.im(specimen_a)**2)==s.Rational(255437,1000000)>s.Rational(1,4)
    for j in (0,1):
        projection_a=s.expand(s.re(specimen_a*rotations[j]))
        projection_b=s.expand(s.re(specimen_b*rotations[j]**2))
        assert positive_radical(projection_b)
        assert positive_radical(256*projection_b**5-3125*projection_a**4)
    assert positive_radical(-s.re(specimen_b*rotations[2]**2))
    assert positive_radical(s.re(specimen_a*rotations[2]))
    checks.append('exact_half_threshold_counterexample_two_classes_fail')
    return {'status':'pass','checks':checks,'K_eighth_power':str(eighth),
            'evidence_class':'exact_symbolic_identities_supporting_ordinary_analytic_proof'}


def stress(count):
    import numpy as np
    scalar=4/5**1.25
    threshold=scalar*(3/4)**.125
    theta=np.linspace(0,2*np.pi,count)[:,None]
    second=np.cos(theta+2*np.arange(3)*np.pi/3)
    violations=0
    minimum=3
    for phi in np.linspace(0,np.pi,count):
        first=threshold*np.cos(phi+np.arange(3)*np.pi/3)
        counts=(np.abs(first)>=scalar*np.maximum(second,0)**1.25-1e-12).sum(axis=1)
        minimum=min(minimum,int(counts.min()))
        violations+=int(np.count_nonzero(counts<2))
    return {'evidence_class':'finite_floating_diagnostic_not_proof','phase_pairs':count*count,
            'minimum_safe_classes':minimum,'violations':violations}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stress',type=int,default=0,help='optional phase count per axis')
    args=parser.parse_args()
    assert args.stress>=0
    result=exact_checks()
    if args.stress:
        result['finite_stress']=stress(args.stress)
    print(json.dumps(result,sort_keys=True))
