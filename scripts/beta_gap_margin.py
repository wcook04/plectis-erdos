import math
R=10000; M=2*R+256
w=[0]*(R+2)
for n in range(1,R+2): w[n]=(1<<M)//((1<<n)-1)
acc=0
for k in range(R+1,R+400): acc+=(1<<M)//((1<<k)-1)
tail=[0]*(R+2); tail[R]=acc
for n in range(R-1,-1,-1): tail[n]=tail[n+1]+w[n+1]
G=[w[n]-tail[n] for n in range(R+1)]
print("closest call at rank>=5, in gap-widths (log2):\n")
for p,q,lab in [(1,21,"1/21"),(1,465,"1/465"),(4,9,"4/9"),(1,2,"1/2"),(1,5,"1/5")]:
    rho=((p<<M)+q-1)//q; worst=None
    for n in range(1,R+1):
        if rho>=w[n]: rho-=w[n]
        else:
            if n>=5:
                num=tail[n]-rho
                lg = (num.bit_length()-G[n].bit_length()) if num>0 else -10**9
                if worst is None or lg<worst[0]: worst=(lg,n)
    print(f"  {lab:6s} min margin ~ 2^{worst[0]} gap-widths, at rank {worst[1]}"
          f"   (random-model expectation: ~2^{worst[1]} )")
