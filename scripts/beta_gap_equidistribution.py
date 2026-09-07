import sys, random, collections
R=800; M=2*R+96
w=[0]*(R+2)
for n in range(1,R+2): w[n]=(1<<M)//((1<<n)-1)
acc=0
for k in range(R+1,R+201): acc+=(1<<M)//((1<<k)-1)
tail=[0]*(R+2); tail[R]=acc
for n in range(R-1,-1,-1): tail[n]=tail[n+1]+w[n+1]
def sweep(qlo,qhi,ntarg,NMIN,label,seed=1):
    random.seed(seed); EXP=list(range(1,21)); cnt=[0]*len(EXP); skips=0; fatal=0; done=0
    while done<ntarg:
        q=random.randrange(qlo,qhi)|1
        p=random.randrange(1,q)
        from math import gcd
        if gcd(p,q)!=1: continue
        done+=1
        rho=((p<<M)+q-1)//q
        for n in range(1,R+1):
            if rho>=w[n]: rho-=w[n]
            else:
                if rho>tail[n]: fatal+=1; break
                if n>=NMIN:
                    skips+=1; d=w[n]-rho
                    for i,e in enumerate(EXP):
                        if (d<<e)<w[n]: cnt[i]+=1
    print(f"\n{label}: targets={ntarg} fatal={fatal} skips(rank>={NMIN})={skips}")
    print("   eps      observed        uniform         ratio")
    for i,e in enumerate(EXP):
        if e%2: continue
        obs=cnt[i]/skips; u=2.0**-e
        print(f"   2^-{e:<3d} {obs:.9f}   {u:.9f}   {obs/u:.4f}")
sweep(3,200,1500,40,"small q  (3..200)")
sweep(10**5,2*10**5,1500,40,"large q  (1e5..2e5)")
sweep(10**12,2*10**12,1500,40,"huge q   (1e12..2e12)")
