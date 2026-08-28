#!/usr/bin/env python3
"""Exact Bernstein certificate for the GP3 regular radial second variation.

This optional research replay requires SymPy.  It proves a local theorem only;
the global radial inequality, GP3, and unrestricted Erdos 1041 remain open.
"""
import json
import sympy as s


def main():
    q,x,z,u,t=s.symbols("q x z u t",positive=True)
    radii=(x,x,z); c=-s.Rational(1,2); pairs=((0,1),(1,2),(2,0))
    def H(r,c):
        return (q-r*c)/(q*q+r*r-2*q*r*c)-(q*r*r-r*c)/(1+q*q*r*r-2*q*r*c)
    def Hc(r,c):
        return r*(q*q-r*r)/(q*q+r*r-2*q*r*c)**2+r*(1-q*q*r*r)/(1+q*q*r*r-2*q*r*c)**2
    alpha=[radii[i]*Hc(radii[j],c)+radii[j]*Hc(radii[i],c) for i,j in pairs]
    product=x*x*z
    terms=[radii[i]*H(radii[i],1) for i in range(3)]
    terms += [radii[i]*H(radii[j],c)+radii[j]*H(radii[i],c) for i,j in pairs]
    terms += [-(2*x+z)*3*q*q/(q**3-product),-(2*x+z)*3*product*q*q/(1-product*q**3)]
    terms += [a/2 for a in alpha]
    terms += [-alpha[0]*alpha[1]/alpha[2]/2,-alpha[0]*alpha[2]/alpha[1]/2,-alpha[1]*alpha[2]/alpha[0]/2]
    values=[s.factor(s.diff(term,z,2).subs(z,x)/2) for term in terms]
    while len(values)>1:
        values.sort(key=s.count_ops)
        a=values.pop(0); b=values.pop(0)
        values.append(s.factor(s.together(a+b)))
    numerator,denominator=s.fraction(s.factor(values[0].subs(x,q*u)))
    q_coefficients=s.Poly(numerator,q).as_dict()
    polynomial=s.Poly(s.expand(sum(coefficient*t**(exponent[0]//2) for exponent,coefficient in q_coefficients.items())/u),t,u)
    degree_t,degree_u=polynomial.degree(t),polynomial.degree(u)
    bernstein=[]
    for k in range(degree_t+1):
        for ell in range(degree_u+1):
            bernstein.append(s.factor(sum(
                polynomial.coeff_monomial(t**i*u**j)
                *s.binomial(k,i)/s.binomial(degree_t,i)
                *s.binomial(ell,j)/s.binomial(degree_u,j)
                for i in range(k+1) for j in range(ell+1))))
    positive_tail=(1-u**2)+q**2*(1-q**4*u**2)+q**6*u**4+q**4*u**4+4*q**4*u**3+4*q**4*u**2+4*q**2*u**2+4*q**2*u
    expected_denominator=q**2*(u-1)**3*(q*u-1)*(q*u+1)*(q**2*u-1)**3*(u**2+u+1)**4*(q**4*u**2+q**2*u+1)**4*positive_tail
    nonpositive=all(value<=0 for value in bernstein)
    negative=sum(1 for value in bernstein if bool(value<0))
    denominator_ok=s.factor(denominator-expected_denominator)==0
    passed=(degree_t,degree_u)==(15,25) and len(bernstein)==416 and negative==405 and nonpositive and denominator_ok
    print(json.dumps({
        "schema":"erdos1041-gp3-regular-second-variation/1",
        "bernstein_degree":[degree_t,degree_u],
        "coefficient_count":len(bernstein),
        "strictly_negative_coefficient_count":negative,
        "all_coefficients_nonpositive":nonpositive,
        "denominator_factorization_verified":denominator_ok,
        "regular_transverse_second_variation_strictly_positive":passed,
        "claim_boundary":"Local stationary-branch theorem only; global DGP3, GP3, the selector lemma, and unrestricted Erdos 1041 remain unproved."
    },indent=2))
    return 0 if passed else 1


if __name__=="__main__": raise SystemExit(main())
