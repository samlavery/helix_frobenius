"""ATTEMPT 010, stage 3 -- the line amplitude in closed form, and the smearing criterion.

DERIVATION (this is the DC-first step: evaluate the common mode exactly, do not bound it).
On the tape u = theta/pi the density is 1 + dS/du.  With
    S(t) = -(1/pi) sum_n Lambda(n)/(sqrt n log n) sin(t log n),
    dt/du = 2 pi / L,      gamma = 2 pi u / L,
one gets
    dS/du = -(2/L) sum_n (Lambda(n)/sqrt n) cos(2 pi u (log n)/L).
Over a tape window of length U the Fourier transform picks up (U/L) Lambda(n)/sqrt n at
tau_n = log n / L, so with K = |F|^2 / (#zeros) and #zeros = U,

        K(tau_n)  =  U * Lambda(n)^2 / (L^2 * n).                     (*)

PREDICTION 1.  (*) holds, with no free parameter, for every prime power n.
PREDICTION 2.  (*) degrades exactly when the window is long enough that L DRIFTS across it:
    the line at tau_n smears by  dtau = (log n) * dL / L^2  with dL = log(1 + W/T),
    and is lost once dtau exceeds the resolution 1/U.  So define
        R(n) = dtau * U = U (log n) log(1 + W/T) / L^2,
    and (*) should hold for R << 1 and fail for R >~ 1.  This is a falsifiable, quantitative
    account of the low-height failures in stage 2 -- not an excuse for them.

NULL for prediction 2: shortening the window at T = 1e4 does NOT restore the lines to (*).
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

LAM = {}
for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
    for k in (1, 2, 3, 4, 5):
        if p**k <= 40: LAM[p**k] = log(p)

def spectrum_at(g, T, taus):
    u = theta(g)/np.pi; u = u - u[0]; U = u[-1]; n = len(u)
    F = np.exp(2j*np.pi*np.outer(np.asarray(taus, float), u)).sum(axis=1)
    return np.abs(F)**2/n, U, n

P("STAGE 3 -- closed-form line amplitude  K(tau_n) = U Lambda(n)^2 / (L^2 n),  no free parameter.\n")
for T, W, h in ((1e6, 2100.0, 0.012), (1e7, 1850.0, 0.009)):
    cache = f"att010_zeros_{T:.0e}.npy"
    g = np.load(cache) if os.path.exists(cache) else zeros_in(T, W, h)
    if not os.path.exists(cache): np.save(cache, g)
    L = log(T/(2*np.pi))
    ns = sorted(LAM)
    K, U, nz = spectrum_at(g, T, [log(n)/L for n in ns])
    P(f"  T={T:.0e}   L={L:.4f}   U={U:.1f}   zeros={nz}   window W={W:.0f}")
    P(f"    {'n':>4}{'Lambda':>9}{'predicted K':>14}{'observed K':>13}{'obs/pred':>11}")
    ratios = []
    for n, k in zip(ns, K):
        pred = U*LAM[n]**2/(L*L*n)
        ratios.append(k/pred)
        P(f"    {n:>4}{LAM[n]:>9.4f}{pred:>14.3f}{k:>13.3f}{k/pred:>11.3f}")
    r = np.array(ratios)
    P(f"    -> median obs/pred over {len(r)} prime powers: {np.median(r):.3f}   "
      f"(mean {r.mean():.3f}, IQR {np.percentile(r,25):.3f}-{np.percentile(r,75):.3f})\n")

P("PREDICTION 2 -- the smearing criterion  R = U (log n) log(1+W/T) / L^2.")
P("  Lines survive for R << 1.  Test: shorten the window at T=1e4, where stage 2 found")
P("  NOTHING (K(2)=0.23), and watch the lines return.  NULL: they do not.\n")
P(f"  {'T':>7}{'W':>8}{'zeros':>7}{'R(n=2)':>9}{'R(n=5)':>9}   "
  f"{'K/pred n=2':>11}{'n=3':>8}{'n=4':>8}{'n=5':>8}{'n=7':>8}")
for T, Ws, h in ((1e4, (3600.0, 1200.0, 400.0, 150.0), 0.030),
                 (1e5, (2700.0, 900.0, 300.0), 0.025)):
    L0 = log(T/(2*np.pi))
    for W in Ws:
        g = zeros_in(T, W, h)
        if len(zeros_in(T, W, h/2)) != len(g):
            P(f"  T={T:.0e} W={W} grid missed zeros"); continue
        L = log((T + W/2)/(2*np.pi))              # L at the window centre
        ns = (2, 3, 4, 5, 7)
        K, U, nz = spectrum_at(g, T, [log(n)/L for n in ns])
        R = lambda n: U*log(n)*log(1 + W/T)/(L*L)
        row = f"  {T:>7.0e}{W:>8.0f}{nz:>7}{R(2):>9.2f}{R(5):>9.2f}   "
        for n, k in zip(ns, K):
            row += f"{k/(U*LAM[n]**2/(L*L*n)):>11.2f}" if n == 2 else \
                   f"{k/(U*LAM[n]**2/(L*L*n)):>8.2f}"
        P(row)
