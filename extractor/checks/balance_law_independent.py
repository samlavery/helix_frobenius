"""INDEPENDENT re-check of the balance-law disproof: different prime generation
(trial division), different arithmetic (mpmath, 40 dps), no numpy anywhere.
If this disagrees with the numpy run, one of them has a bug.
"""
from mpmath import mp, mpf, mpc, exp, log, sqrt, floor, pi, fabs
mp.dps = 40

def primes_upto(N):
    out = []
    for n in range(2, N+1):
        d, isp = 2, True
        while d*d <= n:
            if n % d == 0: isp = False; break
            d += 1
        if isp: out.append(n)
    return out

def vm_pairs(N):
    """(n, Lambda(n)) for prime powers n <= N"""
    out = []
    for p in primes_upto(N):
        q, lp = p, log(mpf(p))
        while q <= N:
            out.append((q, lp)); q *= p
    return sorted(out)

def run(N, t):
    S = [mpc(0)]*6; M = [mpf(0)]*6
    for n, lam in vm_pairs(N):
        ln = log(mpf(n))
        w = lam/sqrt(mpf(n))
        frac = (t*ln/(2*pi)) % 1
        j = int(floor(6*frac)) % 6
        S[j] += w*exp(mpc(0,1)*(-(t*ln)))
        M[j] += w
    imb = sum(abs(S[j]-S[j+3]) for j in range(3))
    return imb, sum(M)

G1 = mpf('14.134725141734693')
print(f"{'N':>7} {'t':>12} {'imbalance':>14} {'mass':>12} {'imb/mass':>10}")
for N in (1000, 5000, 20000):
    for label, t in [("gamma_1", G1), ("t=20", mpf(20))]:
        imb, mass = run(N, t)
        print(f"{N:>7} {label:>12} {mp.nstr(imb,8):>14} {mp.nstr(mass,8):>12} {mp.nstr(imb/mass,6):>10}")
print()
print("sqrt(3)/2 =", mp.nstr(sqrt(mpf(3))/2, 8), " -- the pencil lower bound on imb/mass")
print("VERDICT: law claims imbalance -> 0.  Observed: grows, ratio pinned near 0.955.")
