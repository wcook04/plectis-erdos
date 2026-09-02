"""Wave-8 fencing check (Return 7, sharpened): the q=1 slice of SPREAD is
    ||Ehat'_{a,L} / (P/2)||  =  ||Q_a S - X_{a+L}/P||
so it shadows Q_a S to within W(a+L)/P.  Exact rationals throughout.
"""
from fractions import Fraction
import exact

def B3(a):
    lo=(a*exact.ALPHA_HI.denominator)//exact.ALPHA_HI.numerator
    hi=(a*exact.ALPHA_LO.denominator)//exact.ALPHA_LO.numerator
    assert lo==hi; return lo
def C5(a):
    lo=(a*exact.BETA_HI.denominator)//exact.BETA_HI.numerator
    hi=(a*exact.BETA_LO.denominator)//exact.BETA_LO.numerator
    assert lo==hi; return lo
def Q(a): return 2**a*3**B3(a)*5**C5(a)
def b(a): return Q(a+1)//Q(a)

def shell(a):
    """smooth h in [2^a, 2^(a+1))"""
    out=[]; lo,hi=1<<a,1<<(a+1); p3=1
    while p3<hi:
        x=p3
        while x<lo: x*=5
        while x<hi: out.append(x); x*=5
        p3*=3
    return out
def H(h):
    n=h; e2=0
    while n%2==0: n//=2; e2+=1
    n2=h; e3=0
    while n2%3==0: n2//=3; e3+=1
    n3=h; e5=0
    while n3%5==0: n3//=5; e5+=1
    # H(x) = 2^floor(log2 x) 3^floor(log3 x) 5^floor(log5 x)
    a=h.bit_length()-1
    p3,c3=1,0
    while p3*3<=h: p3*=3; c3+=1
    p5,c5=1,0
    while p5*5<=h: p5*=5; c5+=1
    return 2**a*3**c3*5**c5
def d(a): return Q(a)*sum(Fraction(1,H(h)) for h in shell(a))
def e(a): return 15*d(a)

def X(a, R=90):
    """X_a = sum_{r>=0} d_{a+r} * Q_a/Q_{a+r}, truncated at R (error < 1e-40)."""
    tot=Fraction(0)
    for r in range(R):
        tot += d(a+r)*Fraction(Q(a), Q(a+r))
    return tot

print("a  L    ||Ehat'/(P/2) - (Q_a S mod 1)||     W(a+L)/P        holds")
ok=True
for (a,L) in [(3,4),(5,5),(7,6),(10,7),(12,8),(6,10)]:
    P=Q(a+L)//Q(a)
    Ehat=sum(e(a+j)*(Q(a+L)//Q(a+j)) for j in range(L))
    assert Ehat % 30 == 0
    Ep=Ehat//30
    Xa, XaL = X(a), X(a+L)
    # exact identity check: 2*E' = P*X_a - X_{a+L}
    lhs, rhs = 2*Ep, P*Xa - XaL
    idok = abs(lhs-rhs) < Fraction(1,10**30)
    # q=1 slice vs Q_a*S : X_a = Q_a S - N_a  =>  Q_a S = X_a mod 1
    frac_phase = Fraction(Ep, P//2) - (Xa - int(Xa))     # both mod 1
    frac_phase -= round(frac_phase)
    bound = Fraction(XaL)/P
    good = abs(frac_phase) <= bound + Fraction(1,10**30)
    ok &= idok and good
    print("%-2d %-4d %-34s %-16s %s" % (a,L,float(abs(frac_phase)),float(bound),
                                        "OK" if (idok and good) else "FAIL"))
print("\nidentity 2*Ehat' = P*X_a - X_{a+L} and q=1 shadowing:", "ALL HOLD" if ok else "FAILURE")
