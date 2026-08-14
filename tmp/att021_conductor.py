"""ATTEMPT 021 -- conductor dependence of the theta-tape line law, across real Dirichlet L.

WHY THIS AND NOT THE EPSTEIN AFE.  Attempt 020 named its blocker as "build a smoothed AFE".
That blocker is real but mis-priced: Epstein's ill-conditioning comes from its POLE, and a
correctly rotated smoothing contour is an L-function-library project.  A pole-free specimen
needs no such thing, and it answers the question that actually licenses the instrument:

    does the tape's L -- the quantity setting tau_n = log n / L -- track the ANALYTIC
    CONDUCTOR log(qt/2pi), or only log(t/2pi)?

Everything downstream of attempt 010 depends on the answer, and it has never been tested:
zeta has q = 1, so the two are indistinguishable there.

THE TWO INDEPENDENT EFFECTS, which the tape separates.  For real primitive chi mod q with
parity a (chi(-1) = (-1)^a):
    theta_chi(t) = (t/2) log(q/pi) + Im logGamma((1/2+a+it)/2),      L_chi = 2 dtheta/dt
so L_chi -> log(qt/2pi).  Then
  (POSITION)  the line for n sits at tau_n = log n / L_chi -- moves LEFT as q grows;
  (SUPPORT)   chi(n) = 0 whenever gcd(n,q) > 1, so those lines are EXACTLY ABSENT;
  (AMPLITUDE) K(tau_n) = U Lambda(n)^2 chi(n)^2 / (L_chi^2 n)  for gcd(n,q)=1.

q = 8 is the decisive specimen: chi_8 kills the entire 2-tower (n = 2,4,8,16,32), which for
zeta is the dominant line set.  q = 3 kills 3,9,27; q = 5 kills 5,25; q = 13 kills 13.

STATED NULL, pre-registered.  Positions do not track log n / log(qt/2pi) -- in particular,
evaluating at another conductor's L works just as well; OR the lines at gcd(n,q)>1 are
present; OR the surviving amplitudes miss U Lambda(n)^2/(L^2 n).  Any of those and the tape
law is a zeta accident, not a law, and attempts 010/011 do not generalize.
"""
import numpy as np, mpmath as mp, sys, math
from math import pi, log

def P(*a): print(*a); sys.stdout.flush()
mp.mp.dps = 15

# ------------------------------------------------------------------ specimens
def leg(n, p):
    n %= p
    return 0 if n == 0 else (1 if pow(n, (p-1)//2, p) == 1 else -1)
def chi8(n):
    n %= 8
    return 1 if n in (1, 7) else (-1 if n in (3, 5) else 0)
SPECS = [
    ('L(chi_-3)',  3, 1, lambda n: leg(n, 3)),
    ('L(chi_5)',   5, 0, lambda n: leg(n, 5)),
    ('L(chi_8)',   8, 0, chi8),
]

def theta_chi(t, q, a):
    t = mp.mpf(t)
    return (t/2)*mp.log(mp.mpf(q)/mp.pi) + mp.im(mp.loggamma((mp.mpf(0.5)+a+1j*t)/2))
def dtheta_chi(t, q, a):
    t = mp.mpf(t)
    return float(mp.mpf(0.5)*mp.log(mp.mpf(q)/mp.pi)
                 + mp.mpf(0.5)*mp.re(mp.digamma((mp.mpf(0.5)+a+1j*t)/2)))
def Lval(t, q, chi):
    s = mp.mpf(0.5) + 1j*mp.mpf(t)
    return mp.mpf(q)**(-s)*sum(chi(r)*mp.zeta(s, mp.mpf(r)/q) for r in range(1, q+1) if chi(r))
def Zchi(t, q, a, chi):
    return float(mp.re(mp.e**(1j*theta_chi(t, q, a))*Lval(t, q, chi)))

T0, T1, STEP = 10.0, 400.0, 0.15
def find_zeros(q, a, chi):
    ts = np.arange(T0, T1, STEP)
    v = np.array([Zchi(t, q, a, chi) for t in ts])
    idx = np.nonzero(np.signbit(v[:-1]) != np.signbit(v[1:]))[0]
    lo, hi, flo = ts[idx].copy(), ts[idx+1].copy(), v[idx].copy()
    for _ in range(16):
        mid = (lo+hi)/2
        fm = np.array([Zchi(t, q, a, chi) for t in mid])
        left = np.signbit(flo) != np.signbit(fm)
        hi = np.where(left, mid, hi); lo = np.where(left, lo, mid)
        flo = np.where(left, flo, fm)
    return (lo+hi)/2

def vonm(n):
    m = n
    for p in (2,3,5,7,11,13,17,19,23,29,31):
        if m % p == 0:
            while m % p == 0: m //= p
            return log(p) if m == 1 else 0.0
    return 0.0

def K_at(u, taus):
    return np.abs(np.exp(2j*pi*np.outer(np.asarray(taus, float), u)).sum(axis=1))**2/len(u)

NS = [2,3,4,5,7,8,9,11,13,16,25,27]
res = []
P(f"window t in [{T0:.0f},{T1:.0f}], scan step {STEP}\n")
for name, q, a, chi in SPECS:
    Z = find_zeros(q, a, chi)
    th = np.array([float(theta_chi(t, q, a)) for t in Z])
    exp_n = float(theta_chi(T1, q, a) - theta_chi(T0, q, a))/pi
    u = th/pi; u = u - u[0]; U = u[-1]
    tc = float((Z[0]+Z[-1])/2)
    Lc = 2*dtheta_chi(tc, q, a)
    P(f"{name:>11}  q={q:>3} a={a}  zeros {len(Z):>4}  theta-count {exp_n:7.2f}"
      f"  S-jump {exp_n-len(Z):+5.2f}   U={U:7.1f}  L={Lc:.4f}  [log(qt/2pi)={log(q*tc/(2*pi)):.4f}]")
    res.append((name, q, chi, Z, u, U, Lc))

P("\nTEST 1 -- SUPPORT.  lines with gcd(n,q)>1 must be EXACTLY ABSENT.")
P(f"  {'specimen':>11}" + "".join(f"{'n='+str(n):>8}" for n in (2,3,4,5,8,9,13,25)))
for name, q, chi, Z, u, U, Lc in res:
    ko = K_at(u, [log(n)/Lc for n in (2,3,4,5,8,9,13,25)])
    P(f"  {name:>11}" + "".join(f"{k:>8.2f}" for k in ko)
      + "    killed: " + ",".join(str(n) for n in (2,3,4,5,8,9,13,25) if math.gcd(n, q) > 1))

P("\nTEST 2 -- AMPLITUDE.  K vs U Lambda(n)^2 chi(n)^2/(L^2 n), surviving lines only.")
for name, q, chi, Z, u, U, Lc in res:
    live = [n for n in NS if math.gcd(n, q) == 1 and vonm(n) > 0]
    ko = K_at(u, [log(n)/Lc for n in live])
    pr = [U*vonm(n)**2/(Lc*Lc*n) for n in live]
    P(f"  {name:>11}  " + "  ".join(f"n{n}:{o/p:.2f}" for n, o, p in zip(live, ko, pr)))
    P(f"  {'':>11}  median obs/pred = {np.median([o/p for o, p in zip(ko, pr)]):.3f}"
      f"   (predicted K: {', '.join(f'{p:.1f}' for p in pr)})")

P("\nTEST 3 -- POSITION.  the decisive control: aim each specimen at ANOTHER conductor's L.")
P("  statistic = mean K over the specimen's own surviving prime lines.")
P(f"  {'specimen':>11}" + "".join(f"{'L(q='+str(s[1])+')':>12}" for s in SPECS))
for name, q, chi, Z, u, U, Lc in res:
    row = f"  {name:>11}"
    live = [n for n in NS if math.gcd(n, q) == 1 and vonm(n) > 0]
    for name2, q2, a2, chi2 in SPECS:
        tc = float((Z[0]+Z[-1])/2)
        L2 = 2*dtheta_chi(tc, q2, a2)
        ko = K_at(u, [log(n)/L2 for n in live])
        row += f"{ko.mean():>12.2f}"
    P(row + ("   <- own L is column " + str([s[1] for s in SPECS].index(q)+1)))
P("\n  noise floor is Exp(1): mean 1.00.  The diagonal must dominate its row.")
