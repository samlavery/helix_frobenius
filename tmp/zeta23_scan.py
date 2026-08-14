"""STEP 2 -- THE SCAN.  Vary ONLY the sampling spacing h' = c*h, h = 2pi/L.

Window support L, taper, zero set, and the frequency window [T,2T] all held fixed.
d' = floor(T/h') so the same window is covered.
"""
import json
import time
import numpy as np
from zeta23_bench import a_const, load_zeros, traces

T = 2000.0
l = np.log(T / (2 * np.pi))
l1 = l + 2 * np.log(2) - 1
NI = T * l1 / (2 * np.pi)                 # 1957.39
LAM, ETA = 1.0, 0.05
L = LAM * l
w = ETA * L / 2
a = a_const(L, w)
F_lam = LAM / (1 + LAM**2 / 3)            # 0.75

gam_all = load_zeros()
gam = gam_all[(gam_all >= 1700.0) & (gam_all <= 4300.0)]   # verified identical to full set

# N(I') with I' enlarged by the numerical reach D0 = 44.7
NIp = ((2 * T + 44.7) / (2 * np.pi) * (np.log((2 * T + 44.7) / (2 * np.pi)) - 1)
       - (T - 44.7) / (2 * np.pi) * (np.log((T - 44.7) / (2 * np.pi)) - 1))

named = {
    "1/6": 1 / 6, "1/3": 1 / 3, "1/2": 0.5, "2/3": 2 / 3, "5/6": 5 / 6,
    "3/pi": 3 / np.pi, "1": 1.0, "pi/3": np.pi / 3,
    "7/6": 7 / 6, "4/3": 4 / 3, "3/2": 1.5, "2": 2.0,
}
cs = sorted(set(list(np.round(np.arange(0.20, 2.001, 0.02), 6)) + list(named.values())))

print(f"lambda={LAM} eta={ETA}  L={L:.6f} w={w:.6f} a={a:.6f}  h=2pi/L={2*np.pi/L:.6f}")
print(f"N(I)={NI:.2f}  N(I')={NIp:.2f}  F(lambda)={F_lam:.4f}   zeros used: {gam.size}")
print()
hdr = (f"{'c':>8} {'name':>6} {'d':>6} {'trGt':>11} {'trGt/(aL)':>10} {'trGt^2':>12} "
       f"{'C':>10} {'C/N':>8} {'/F(lam)':>8} {'C/d':>8} {'cert':>7} {'certcap':>8}")
print(hdr)
inv = {round(v, 9): k for k, v in named.items()}

out = []
t0 = time.time()
for c in cs:
    d, trG, trG2, K = traces(gam, T, L, w, c)
    trGt, trGt2 = trG / L, trG2 / L**2
    C = trG**2 / trG2
    cert = (2 * C - NIp) / NI
    rec = dict(c=float(c), name=inv.get(round(float(c), 9), ""), d=d,
               trGt=trGt, trGt_over_aL=trGt / (a * L), trGt2=trGt2, C=C,
               C_over_N=C / NI, ratio_F=C / NI / F_lam, C_over_d=C / d,
               cert=cert, cert_capped=min(cert, d / NI))
    out.append(rec)
    print(f"{c:8.4f} {rec['name']:>6} {d:6d} {trGt:11.3f} {trGt/(a*L):10.2f} {trGt2:12.3f} "
          f"{C:10.3f} {C/NI:8.5f} {C/NI/F_lam:8.5f} {C/d:8.5f} {cert:7.3f} "
          f"{rec['cert_capped']:8.3f}")

print(f"\n[{time.time()-t0:.1f}s]")
with open("zeta23_scan_results.json", "w") as f:
    json.dump(dict(T=T, l=l, lam=LAM, eta=ETA, L=L, w=w, a=a, NI=NI, NIp=NIp,
                   F_lam=F_lam, nzeros=int(gam.size), rows=out), f, indent=1)
print("wrote zeta23_scan_results.json")
