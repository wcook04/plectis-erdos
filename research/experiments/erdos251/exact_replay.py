# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Independent exact checks for the revision packet. Python standard library only."""
from __future__ import annotations
import hashlib, json, math
from pathlib import Path

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)

def verify_one_tail(Q: int, A: int, B: int, sign: int) -> dict:
    """Certify 1/2 < sign*D < 1 from |Q*D-A| <= B.
    The analytic enclosure and recurrence are premises, not inferred here.
    """
    require(Q > 0 and B >= 0 and sign in (-1, 1), 'Invalid certificate parameters')
    lower=2*sign*A-Q-2*B
    upper=Q-sign*A-B
    require(lower > 0 and upper > 0, 'Signed window is not certified')
    return {'Q':Q,'A':A,'B':B,'sign':sign,
            'strict_lower_margin':lower,'strict_upper_margin':upper,
            'implication':'1/2 < sign*D < 1; for delta=2*sign, -1 < sign*(2*D-delta) < 0'}

def verify_neighbours(row: dict, Ln: int, Ld: int, Un: int, Ud: int) -> None:
    u=int(row['lower_neighbour_numerator_hex'],16)
    v=int(row['lower_neighbour_denominator_hex'],16)
    up=int(row['upper_neighbour_numerator_hex'],16)
    vp=int(row['upper_neighbour_denominator_hex'],16)
    require(v>0 and vp>0, 'Neighbour denominators must be positive')
    require(u*Ld < Ln*v and Un*vp < up*Ud, 'Neighbours do not strictly enclose the bracket')
    require(up*v-u*vp==1, 'Farey determinant is not one')
    exponent=row['proved_floor_exponent_used']
    decimal=row['proved_decimal_strict_exponent_used']
    require(v+vp >= 1<<exponent, 'Reported binary denominator floor fails')
    require(1<<exponent > 10**decimal, 'Reported decimal exclusion fails')

def primes_below(limit: int) -> list[int]:
    sieve = bytearray(b'\1') * limit
    sieve[:2] = b'\0\0'
    for p in range(2, math.isqrt(limit-1)+1):
        if sieve[p]:
            start = p*p
            sieve[start:limit:p] = b'\0' * ((limit-1-start)//p+1)
    return [p for p in range(2,limit) if sieve[p]]

def P(x: int) -> int:
    return x**4+8*x**3+36*x*x+104*x+150

def replay() -> dict:
    ps=primes_below(1100000)
    c=80200
    require(len(ps)>=c, "Prime sieve does not reach the prescribed count")
    ps=ps[:c]
    g=[q-p for p,q in zip(ps,ps[1:])]
    rows=[]
    for N in (2,3):
        Q=1<<40
        D=sum((g[N+1+j]-g[N+j])*(1<<(40-j)) for j in range(1,41))
        E=1250*(P(N+43)+P(N+42))
        distance=min(D%Q,Q-D%Q)
        require(abs(D)+E<Q and E<distance, "Adjacent window certificate failed")
        rows.append(dict(N=N,scaled_partial=D,scaled_remainder=E,window_margin=Q-abs(D)-E,integer_margin=distance-E))
    require(g[4]-g[3]==-2, "Wrong signed gap mismatch or index convention")
    one_tail=verify_one_tail(1<<40,rows[0]['scaled_partial'],rows[0]['scaled_remainder'],-1)
    # All values below are integers.  No decimal or binary floating-point
    # approximation to the prime series is used.
    A=0
    for p in ps:
        A=2*A+p
    # Analytic premise: p_n <= 1250(n+1)^4, proved in the supplied paper
    # and represented by checked Lean declarations in its supplied CI index.
    # c>=9 gives (c+1+j)^4 <= (c+1)^4 (3/2)^j for j>=0.
    # Consequently L=A/2^c <= Pi <= (2A+5000(c+1)^4)/2^(c+1)=U.
    Ln,Ld=A,1<<c
    Un,Ud=2*A+5000*(c+1)**4,1<<(c+1)
    ln,ld,un,ud=Ln,Ld,Un,Ud
    pm2,pm1,qm2,qm1=0,1,1,0
    conv=[]
    while True:
        al,rl=divmod(ln,ld)
        au,ru=divmod(un,ud)
        if al!=au or rl==0 or ru==0:
            break
        pp,qq=al*pm1+pm2,al*qm1+qm2
        conv.append((pp,qq))
        pm2,pm1,qm2,qm1=pm1,pp,qm1,qq
        # Inversion reverses endpoints.  The same common CF prefix is
        # forced for every real number in the entire closed bracket.
        ln,ld,un,ud=ud,ru,ld,rl
    pair=conv[-2:]
    (u,v),(up,vp)=sorted(pair,key=lambda x: 0 if x[0]*Ld<Ln*x[1] else 1)
    require(u*Ld < Ln*v, "Lower neighbour is not strictly below the bracket")
    require(Un*vp < up*Ud, "Upper neighbour is not strictly above the bracket")
    require(up*v-u*vp==1, "Non-unit Farey determinant")
    require(v+vp >= 1<<39997, "Advertised denominator floor not met")
    require(1<<39997 > 10**12040, "Decimal exponent mismatch")
    result={
      'schema':'erdos251_independent_integer_replay_v2',
      'date':'2026-09-16','arithmetic':'Python arbitrary-precision integers; no floating-point series values',
      'lean_replayed':False,
      'small_pair_rows':rows,'one_tail_signed_certificate':one_tail,
      'large_floor':{'prime_count':c,'last_prime':ps[-1], 'common_cf_coefficients':len(conv),
                    'farey_determinant':1, 'farey_denominator_sum_bit_length':(v+vp).bit_length(),
                    'proved_floor_exponent_used':39997,'proved_decimal_strict_exponent_used':12040,
                    'lower_neighbour_numerator_hex':hex(u),'lower_neighbour_denominator_hex':hex(v),
                    'upper_neighbour_numerator_hex':hex(up),'upper_neighbour_denominator_hex':hex(vp),
                    'scope':'Independent replacement certificate for the stated bound, not a replay or authentication of the original 80000-bit receipt.'},
      'reproducibility':'Deterministic output; elapsed time deliberately excluded from the certificate.'}
    verify_neighbours(result['large_floor'],Ln,Ld,Un,Ud)
    return result

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=Path('exact_replay_results.json'))
    args=ap.parse_args()
    data=replay()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    small={**data,'large_floor':{k:v for k,v in data['large_floor'].items() if not k.endswith('_hex')}}
    print(json.dumps(small,indent=2))
