# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Finite checks only; no asymptotic conclusion. Python 3 + NumPy."""
import json, math
from pathlib import Path
import numpy as np
LIMIT=5000
# The fixed small limit also keeps every NumPy int64 product safely in range.
sieve=bytearray(b'\1')*(LIMIT+1);sieve[0:2]=b'\0\0'
for p in range(2,math.isqrt(LIMIT)+1):
 if sieve[p]:sieve[p*p:LIMIT+1:p]=b'\0'*(((LIMIT-p*p)//p)+1)
primes=[q for q in range(3,LIMIT+1) if sieve[q]]
rows=[];maxsingle=(0,None);maxratio=(0,None);pair_examples=[];identity_checks=0
for q in primes:
 # We deliberately check the wider range K=floor(sqrt(q)).
 K=math.isqrt(q);x=np.arange(q,dtype=np.int64);P=np.ones(q,dtype=np.int64);dP=np.zeros(q,dtype=np.int64);rs=[]
 for h in range(1,K+1):
  y=(x+h)%q; dP=(dP*y+P)%q;P=P*y%q
  roots=np.flatnonzero((P==1)&(dP==0));rr=int(roots.size);rs.append(rr)
  if rr>maxsingle[0]:maxsingle=(rr,{'q':q,'h':h,'roots':roots.tolist()})
 R=sum(rs)
 if R/K>maxratio[0]:maxratio=(R/K,{'q':q,'K':K,'R':R,'r_h':rs})
 rows.append({'q':q,'K':K,'R':R,'max_r':max(rs)})
 # Check mod-q^2 reflection and cancelling unit-cofactor pairs.
 inv=[0]*q;inv[1]=1
 for n in range(2,q):inv[n]=(-(q//n)*inv[q%n])%q
 fs=[1]*q;hs=[0]*q
 for n in range(1,q):fs[n]=(fs[n-1]*n)%(q*q);hs[n]=(hs[n-1]+inv[n])%q
 W=((fs[q-1]+1)//q)%q
 for n in range(3,q-2,2):
  m=q-1-n
  if n>=m:continue
  assert (fs[n]*fs[m]-1-q*(hs[n]-W))%(q*q)==0
  identity_checks+=1
  if fs[n]%q==1 and fs[m]%q==1:
   u=((fs[n]-1)//q)%q;v=((fs[m]-1)//q)%q
   assert (u+v-hs[n]+W)%q==0
   if u and v:
    cancel=(pow(u,-1,q)+pow(v,-1,q))%q==0
    assert cancel==((hs[n]-W)%q==0)
    if cancel and len(pair_examples)<10:pair_examples.append({'q':q,'n':n,'reflected_n':m,'u':u,'v':v,'H_n':hs[n],'W_q':W})
result={'limit':LIMIT,'range':'odd primes 3<=q<=5000; 1<=h<=floor(sqrt(q))','prime_count':len(primes),'max_single_root_count':maxsingle,'max_R_over_K':maxratio,'reflection_identity_checks':identity_checks,'first_cancelling_reflection_pairs':pair_examples,'rows':rows}
Path(__file__).resolve().with_name('critical_fibres_results.json').write_text(json.dumps(result,indent=2))
print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
