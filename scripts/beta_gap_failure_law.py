import random, collections
from math import gcd
R=64; M=2*R+96
w=[0]*(R+2)
for n in range(1,R+2): w[n]=(1<<M)//((1<<n)-1)
acc=0
for k in range(R+1,R+400): acc+=(1<<M)//((1<<k)-1)
tail=[0]*(R+2); tail[R]=acc
for n in range(R-1,-1,-1): tail[n]=tail[n+1]+w[n+1]
random.seed(11); N=400000; c=collections.Counter(); alive=0
for _ in range(N):
    q=random.randrange(10**9,2*10**9)|1; p=random.randrange(1,q)
    if gcd(p,q)!=1: continue
    rho=((p<<M)+q-1)//q; hit=None
    for n in range(1,R+1):
        if rho>=w[n]: rho-=w[n]
        elif rho>tail[n]: hit=n; break
    if hit: c[hit]+=1
    else: alive+=1
tot=sum(c.values())+alive
print(f"targets={tot}  fatal={sum(c.values())} ({100*sum(c.values())/tot:.2f}%)  alive@{R}={alive} ({100*alive/tot:.2f}%)")
print(f"deepest fatal rank = {max(c)}   log2(targets) = {tot.bit_length()-1}")
print("\n rank  count    P(fatal at n)     G_n/w_n (predicted)     ratio")
for n in sorted(c):
    P=c[n]/tot
    pred=(w[n]-tail[n])/w[n]
    print(f" {n:4d} {c[n]:7d}   {P:.9f}      {pred:.9f}      {P/pred if pred else 0:.4f}")
