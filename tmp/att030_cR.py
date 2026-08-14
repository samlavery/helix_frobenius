#!/usr/bin/env python3
"""
Attempt 030 — measure the true Selberg-remainder constant c_R = int (S - P_x)^2 / T.

Chain (derived this session): row := int_1^inf F(alpha)/alpha^2 dalpha <= 2 pi^2 c_R + o(1),
where P_x is a band-limited prime approximation to S and c_R its L2-defect density.
The reduction curve then gives: c_R <= 0.096 => row <= 1.9 => record moves.

S(t) from the cached zero set (att019, 22491 zeros to gamma=20000):
  S(t) = N(t) - theta(t)/pi - 1,  N(t) = #{gamma <= t},  theta = Riemann-Siegel theta.
P_x: the plain prime sum  P(t) = -(1/pi) sum_{n<=x} Lambda(n)/(sqrt(n) log n) sin(t log n)
     (Selberg's mollified version differs at the x-edge; measure several x and both a sharp
      cutoff and a smooth (cos^2-taper) cutoff to bracket the mollifier choice).
Window: t in [1000, 19000] (inside the zero set), grid step 0.01 (S varies at scale ~1/log).
Report: Var S (vs 012's V_line + 1/(2pi^2) check), int(S-P)^2/T for x-grid, both cutoffs.
"""
import numpy as np
from mpmath import mp

REPO = "/Users/samuellavery/work/helix_frobenius"
zeros = np.load(f"{REPO}/tmp/att019_zeros_to20k.npy")
zeros = np.sort(zeros)

T0, T1 = 1000.0, 19000.0
dt = 0.02
ts = np.arange(T0, T1, dt)
print(f"grid: {len(ts)} points on [{T0},{T1}], {len(zeros)} zeros cached", flush=True)

# N(t) via searchsorted; theta via asymptotic expansion (excellent for t >= 1000)
Ncount = np.searchsorted(zeros, ts, side="right")
def theta_asym(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
S = Ncount - theta_asym(ts)/np.pi - 1.0

varS = np.mean(S**2)
print(f"mean S = {np.mean(S):+.5f}   Var-ish int S^2/T = {varS:.5f}", flush=True)

# V_line check (012's law): (1/2pi^2)[sum_{n<=X} Lambda^2/(n log^2 n)] + 1/(2pi^2), X ~ T
def lam_sieve(X):
    X = int(X)
    lam = np.zeros(X+1)
    is_comp = np.zeros(X+1, dtype=bool)
    for p in range(2, X+1):
        if not is_comp[p]:
            lp = np.log(p)
            q = p
            while q <= X:
                lam[q] = lp
                q *= p
            is_comp[p*p::p] = True
    return lam
Tmid = np.exp(np.mean(np.log(ts)))   # geometric mid ~ representative height
lam = lam_sieve(20000)
n = np.arange(len(lam))
mask = lam > 0
Vline = (lam[mask]**2/(n[mask]*np.log(n[mask])**2)).sum()/(2*np.pi**2)
print(f"V_line(X=2e4) = {Vline:.5f};  V_line + 1/(2pi^2) = {Vline + 1/(2*np.pi**2):.5f} "
      f"(compare Var S = {varS:.5f}; 012's law)", flush=True)

# P_x and the remainder for several x, sharp + tapered cutoffs
def P_of(x, taper=False):
    xi = int(x)
    m = (n <= xi) & mask & (n >= 2)
    nn = n[m].astype(float)
    coef = lam[m]/(np.sqrt(nn)*np.log(nn))/np.pi
    if taper:
        # cos^2 taper on the top half-decade
        edge = np.ones_like(nn)
        lo = x/np.sqrt(2.0)
        sel = nn > lo
        edge[sel] = np.cos(np.pi/2*(np.log(nn[sel]/lo)/np.log(x/lo)))**2
        coef = coef*edge
    # P(t) = - sum coef * sin(t log n): evaluate in chunks
    logs = np.log(nn)
    P = np.zeros(len(ts))
    B = 200
    for i in range(0, len(nn), B):
        P -= (np.sin(np.outer(ts, logs[i:i+B])) * coef[i:i+B]).sum(axis=1)
    return P

print(f"{'x':>8} {'cutoff':>7} {'int(S-P)^2/T':>14} {'2pi^2*c_R':>10}", flush=True)
for x in [50, 200, 1000, 5000, 20000]:
    for tp in [False, True]:
        P = P_of(x, taper=tp)
        cR = np.mean((S-P)**2)
        print(f"{x:8d} {'taper' if tp else 'sharp':>7} {cR:14.5f} {2*np.pi**2*cR:10.3f}", flush=True)
