"""ATTEMPT 010, stage 2 -- the significance test done correctly.

Stage 1 established WHERE the lines sit.  It then mis-tested whether they are real: taking
max K over a 60-90 bin band against an Exp(1) floor inflates by ~ln(m).  (That the floor IS
Exp(1) is confirmed by the control band: median 0.69 = ln 2, 99th pct 4.6 = -ln 0.01.)

Correct test: evaluate K AT the predicted tau (not on a grid, not a band max), for prime
POWERS p^k -- the explicit formula rings at k log p, not only log p.  Under the null each
K(tau) ~ Exp(1), so sum over m lines ~ Gamma(m,1).

CONTROL (this is the one that matters): repeat with a WRONG L.  If the 1/L law is real, the
statistic collapses off the true L.  A control that fails by having LESS structure would
prove nothing; this one fails by being AIMED WRONG, which is the right kind of failure.
"""
import numpy as np, math, sys, os
from math import log

def P(*a): print(*a); sys.stdout.flush()

def theta(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
def Psi(p):  return np.cos(2*np.pi*(p*p - p - 1/16))/np.cos(2*np.pi*p)
def d3Psi(p, h=1e-3): return (Psi(p+2*h)-2*Psi(p+h)+2*Psi(p-h)-Psi(p-2*h))/(2*h**3)
def Zrs(t):
    t = np.asarray(t, float); tau = np.sqrt(t/(2*np.pi))
    N = np.floor(tau).astype(np.int64); th = theta(t); s = np.zeros_like(t)
    for n in range(1, int(N.max())+1):
        m = N >= n; s[m] += np.cos(th[m] - t[m]*np.log(n))/np.sqrt(n)
    p = tau - N
    return 2*s + ((-1)**(N-1))*(2*np.pi/t)**0.25*(Psi(p) + (-d3Psi(p)/(96*np.pi**2))*np.sqrt(2*np.pi/t))
def zeros_in(T, W, h):
    g = np.arange(T, T+W, h); s = np.signbit(Zrs(g))
    idx = np.nonzero(s[:-1] != s[1:])[0]; a, b = g[idx].copy(), g[idx+1].copy()
    for _ in range(34):
        m = (a+b)/2
        left = np.signbit(Zrs(a)) != np.signbit(Zrs(m))
        b = np.where(left, m, b); a = np.where(left, a, m)
    return (a+b)/2

RUNS = [(1e3, 5200.0, 0.05), (1e4, 3600.0, 0.030), (1e5, 2700.0, 0.025),
        (1e6, 2100.0, 0.012), (1e7, 1850.0, 0.009)]

# prime powers p^k with tau_p = k log p / L inside (0, 1): at L=14.28 that is p^k < e^14.28
PP = []
for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
    for k in (1, 2, 3):
        PP.append((p, k, k*log(p)))
PP.sort(key=lambda z: z[2])

def gamma_sf(x, m):                      # P(Gamma(m,1) > x) = e^-x sum_{j<m} x^j/j!
    s, term = 0.0, 1.0
    for j in range(m):
        s += term; term *= x/(j+1)
    return math.exp(-x)*s

P("ATTEMPT 10 stage 2 -- K evaluated AT tau_p = k log p / L; null K ~ Exp(1) each.")
P("  statistic  Sigma = sum over the m prime-power lines with tau < 1.  Null: Gamma(m,1).\n")
P(f"  {'T':>8}{'L':>8}{'n':>7}{'m':>5}{'Sigma':>10}{'E[null]':>9}{'p-value':>12}"
  f"{'K(2)':>8}{'K(3)':>8}{'K(4)':>8}{'K(5)':>8}")
rows = []
for T, W, h in RUNS:
    L = log(T/(2*np.pi))
    cache = f"att010_zeros_{T:.0e}.npy"
    if os.path.exists(cache):
        g = np.load(cache)
    else:
        g = zeros_in(T, W, h)
        if len(zeros_in(T, W, h/2)) != len(g):
            P(f"  T={T:.0e} grid missed zeros"); sys.exit(1)
        np.save(cache, g)
    u = theta(g)/np.pi; u = u - u[0]; n = len(u)
    def K(tt):
        tt = np.atleast_1d(np.asarray(tt, float))
        return np.abs(np.exp(2j*np.pi*np.outer(tt, u)).sum(axis=1))**2/n
    def stat(Luse):
        taus = np.array([lp/Luse for _, _, lp in PP])
        taus = taus[taus < 1.0]
        return float(K(taus).sum()), len(taus)
    S, m = stat(L)
    kk = {}
    for q in (2, 3, 4, 5):
        kk[q] = float(K(np.array([log(q)/L]))[0])
    P(f"  {T:>8.0e}{L:>8.3f}{n:>7}{m:>5}{S:>10.2f}{m:>9}{gamma_sf(S, m):>12.3e}"
      f"{kk[2]:>8.2f}{kk[3]:>8.2f}{kk[4]:>8.2f}{kk[5]:>8.2f}")
    rows.append((T, L, u, n, stat, S, m))

P("\n  CONTROL -- the SAME statistic aimed at a wrong L.  Real 1/L law => a sharp peak at 1.0")
P(f"  {'T':>8}   " + "".join(f"{'L*'+f'{c:.2f}':>11}" for c in (0.70, 0.85, 0.95, 1.00, 1.05, 1.15, 1.30)))
for T, L, u, n, stat, S, m in rows:
    row = f"  {T:>8.0e}   "
    for c in (0.70, 0.85, 0.95, 1.00, 1.05, 1.15, 1.30):
        s, mm = stat(L*c)
        row += f"{s/mm:>11.2f}"
    P(row)
P("  (values are Sigma/m, i.e. mean K per line; null expectation 1.00)")

P("\n  PAYOFF, pre-registered metric restated honestly.  Stage 1 asked for the share of")
P("  spectral POWER above tau_2.  That metric is uninformative: K has an Exp(1) floor")
P("  everywhere, so the share is set by BANDWIDTH, and tau_2 -> 0 makes it -> 1 by")
P("  construction.  It reported 0.9945 / 0.9980 / 1.0000 -- rising, i.e. the pre-registered")
P("  payoff FAILED.  The metric that actually measures arithmetic is the EXCESS over the")
P("  Exp(1) floor carried by the lines.  Reported here, and labelled post-hoc:")
P(f"  {'T':>8}{'L':>8}{'m':>5}{'line excess Sigma-m':>21}{'per line':>10}")
for T, L, u, n, stat, S, m in rows:
    P(f"  {T:>8.0e}{L:>8.3f}{m:>5}{S-m:>21.2f}{(S-m)/m:>10.3f}")
