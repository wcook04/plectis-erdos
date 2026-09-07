import sys
sys.path.insert(0, '/var/folders/wn/zcy8rh2j3jx267rds78mlwy80000gn/T/opencode/e1041')
import mpmath as mp
import numpy as np
from fibre_v2 import agg3_exact

mp.mp.dps = 45
rng = np.random.default_rng(4242)
print("deep-shell v2: ratio gap sign at dps45; slice + random families")
print("family        eps      ratio               gap(1-ratio)     d_pt        vg")
rows = []
for ee in range(3, 9):
    eps = mp.mpf(10)**(-ee)
    # slice family
    for ph in (0, 3, 5):
        z2 = mp.exp(2j*mp.pi*ph/8)
        b1 = mp.mpf('0.7')*mp.exp(2j*mp.pi*(ph+1)/8)
        coef = [1, eps*z2, eps*b1, -1]
        rt = mp.polyroots(coef, maxsteps=200)
        res = agg3_exact(rt, dps=40, N0=256)
        if res is None:
            print(f"slice        1e-{ee:<2} ph{ph}: FAIL"); continue
        ratio, per, d_pt, vg, R = res
        print(f"slice ph{ph}    1e-{ee:<2}   {float(ratio):.12f}   {float(1-ratio):+.3e}   {float(d_pt):.2e}  {float(vg):.1e}")
    # two random families
    for rep in range(2):
        b1c = complex(rng.normal(), rng.normal()); b2c = complex(rng.normal(), rng.normal())
        b1 = mp.mpc(b1c)/max(1, abs(b1c)); b2 = mp.mpc(b2c)/max(1, abs(b2c))
        coef = [1, eps*b2, mp.mpf('0.7')*eps*b1, -1]
        rt = mp.polyroots(coef, maxsteps=200)
        res = agg3_exact(rt, dps=40, N0=256)
        if res is None:
            print(f"rand{rep}        1e-{ee:<2}: FAIL"); continue
        ratio, per, d_pt, vg, R = res
        print(f"rand{rep}        1e-{ee:<2}   {float(ratio):.12f}   {float(1-ratio):+.3e}   {float(d_pt):.2e}  {float(vg):.1e}")
