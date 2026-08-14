"""Truncation control: is M3 != M2 real, or an artifact of the h-cutoff?
M2 sums only EVEN h (S=0 on odd); M3 sums ALL h -- so truncation bites them differently.
Uses O1_model's report_H to get running partial sums in one pass per weight."""
import sys, numpy as np
from zeta23_prime import prime_powers
from zeta23_o1 import split
from zeta23_hl import singular_series, R_all_integers, O1_model

T, ETA, lam, HMAX = 600.0, 0.01, 1.75, 200
l = np.log(T/(2*np.pi)); L = lam*l; w = ETA*L/2
X = int(np.exp(L)); h = 2*np.pi/L; d = int(np.floor(T/h))
print(f"T={T} lam={lam} L={L:.3f} X={X} d={d} Hmax={HMAX}")
lamv, u = prime_powers(float(X))
_,_,_, O1m, _,_ = split(T, L, w, lamv, u)
print(f"measured O1 = {O1m:.1f}")
Rt = R_all_integers(X, L, w, d, h)
n = np.arange(1, X+1); inv = 1.0/np.sqrt(n)
cn_e = np.zeros(X); keep = u < np.log(X+1)
idx = np.rint(np.exp(u[keep])).astype(int); ok = (idx>=1)&(idx<=X)
cn_e[idx[ok]-1] = lamv[keep][ok]/np.sqrt(idx[ok])
S = singular_series(HMAX)
REP = (10,20,30,40,60,80,100,140,200)
wts = {'EXACT(gate)': (lambda hh: 1.0, cn_e),
       'M1 density' : (lambda hh: 1.0, inv),
       'M2 full HL' : (lambda hh: float(S[hh]), inv),
       'M3 averaged': (lambda hh: 1.0-1.0/(2.0*hh), inv)}
print(f"{'model':>12} " + " ".join(f"H={r:<6}" for r in REP))
for name,(f,c) in wts.items():
    tot, snap = O1_model(T, L, w, f, c, X, d, Rt, HMAX, report_H=REP)
    print(f"{name:>12} " + " ".join(f"{snap[r]/O1m:7.3f}" for r in REP))
    sys.stdout.flush()
