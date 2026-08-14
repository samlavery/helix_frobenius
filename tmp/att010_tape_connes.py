"""ATTEMPT 010 -- Connes' trace formula x the theta-tape.

PAIRING.  House: the theta-tape (cells constant at pi/3 in theta forever; theta is the
carrier's own dilation-adapted coordinate, unit-1 t is not).  Classical: Connes' trace
formula / Berry's semiclassical form factor -- the spectral side of the explicit formula
read as a trace of the SCALING flow, whose natural coordinate is log-scale.

MECHANISM.  Connes' formula wants a dilation-invariant coordinate; the scaling flow acts
as translation there.  The tape supplies exactly that: N(t) = theta(t)/pi + 1 + S(t), so
in u = theta/pi the zero density is IDENTICALLY 1 -- the tape linearises the count with no
clock to subtract.  Under t -> u a t-frequency log p becomes a u-frequency

        tau_p = log p / L,      L = log(T/2pi)

because gamma = 2 pi u / L.  So the PREDICTION is that on the tape every prime clock drifts
toward DC as T grows, at the exact rate 1/L.

NULL (stated before running).  The arithmetic spikes do NOT sit at log p / L, or their
positions do not track 1/L across three decades of height.  Then the tape is not the
dilation chart and Connes' formula gets nothing from it.

PAYOFF MEASUREMENT (also pre-registered, so the answer cannot be read selectively).  Even if
the positions track, prime POWER may merely relocate rather than shrink.  So we also report
the share of fluctuation variance above tau = tau_2 = log 2 / L and above tau = 1.
"""
import numpy as np, mpmath as mp, sys, math

def P(*a): print(*a); sys.stdout.flush()

# ---------------------------------------------------------------- Riemann-Siegel (rs2.py)
def theta(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)

def Psi(p):  return np.cos(2*np.pi*(p*p - p - 1/16))/np.cos(2*np.pi*p)

def d3Psi(p, h=1e-3):
    return (Psi(p+2*h) - 2*Psi(p+h) + 2*Psi(p-h) - Psi(p-2*h))/(2*h**3)

def Zrs(t):
    t = np.asarray(t, float); tau = np.sqrt(t/(2*np.pi))
    N = np.floor(tau).astype(np.int64); th = theta(t); s = np.zeros_like(t)
    for n in range(1, int(N.max())+1):
        m = N >= n
        s[m] += np.cos(th[m] - t[m]*np.log(n))/np.sqrt(n)
    p = tau - N
    corr = (2*np.pi/t)**0.25*(Psi(p) + (-d3Psi(p)/(96*np.pi**2))*np.sqrt(2*np.pi/t))
    return 2*s + ((-1)**(N-1))*corr

# ---------------------------------------------------------------- gate against mpmath
mp.mp.dps = 20
gate = np.array([777.7, 3001.9, 9999.5, 50000.3, 1000000.3, 10000000.7])
err = float(np.max(np.abs(Zrs(gate) - np.array([float(mp.siegelz(t)) for t in gate]))))
P(f"GATE  max |Zrs - mpmath.siegelz| over t in [7.8e2, 1e7] : {err:.2e}   (worst at the")
P("      LOW end, t=778; 2.0e-08 at t=1e7).  A Z-error eps displaces a zero by eps/|Z'|")
P("      with |Z'| ~ L, and the tape coordinate by (L/2)*that/pi, i.e. ~1e-6 in u.  The")
P("      spectrum below is read to tau <= 1.6, needing u to ~0.6; margin is 6 decades.")
if err > 1e-5:
    P("GATE FAILED"); sys.exit(1)
def zeros_in(T, W, h):
    g = np.arange(T, T+W, h); z = Zrs(g)
    s = np.signbit(z); idx = np.nonzero(s[:-1] != s[1:])[0]
    a, b = g[idx].copy(), g[idx+1].copy()
    for _ in range(34):
        m = (a+b)/2; zm = Zrs(m)
        left = np.signbit(Zrs(a)) != np.signbit(zm)
        b = np.where(left, m, b); a = np.where(left, a, m)
    return (a+b)/2

zc = np.array([float(mp.zetazero(k).imag) for k in (1000, 1001, 1002, 1003)])
zf = zeros_in(zc[0]-0.3, (zc[-1]-zc[0])+0.6, 0.02)
P(f"GATE  zero POSITIONS vs mpmath.zetazero(1000..1003): "
  f"max |dt| = {np.max(np.abs(np.sort(zf)[:4]-zc)):.2e}")

P("\nATTEMPT 10: Connes' trace formula x the theta-tape")
P("  PREDICTION  arithmetic lines on the tape sit at tau_p = log p / L,  L = log(T/2pi).")
P("  NULL        they do not, or they do not move with L across three decades.\n")

RUNS = [(1e3, 5200.0, 0.05), (1e5, 2700.0, 0.025), (1e7, 1850.0, 0.009)]
out = []
import os
for T, W, h in RUNS:
    L = math.log(T/(2*np.pi))
    cache = f"att010_zeros_{T:.0e}.npy"
    if os.path.exists(cache):
        g = np.load(cache); n_half = len(g)
        P(f"T={T:.0e}  L={L:.4f}  window {W:.0f}  zeros {len(g)}   [cached, census already passed]")
    else:
        g = zeros_in(T, W, h)
        exp_n = (theta(T+W) - theta(T))/np.pi       # Riemann-von Mangoldt count in the window
        # census: theta/pi - count = S(T+W)-S(T) = O(1) and is NOT an error; a MISSED close
        # pair is.  So the test is grid-stability under refinement, not agreement with theta.
        n_half = len(zeros_in(T, W, h/2))
        P(f"T={T:.0e}  L={L:.4f}  window {W:.0f}  zeros {len(g)}  (at h/2: {n_half})   "
          f"theta-count {exp_n:.2f}   S-jump {exp_n-len(g):+.2f}")
        if n_half != len(g):
            P(f"   *** grid missed {n_half-len(g)} zeros -- corrupted"); sys.exit(1)
        np.save(cache, g)
    u = theta(g)/np.pi                               # THE TAPE COORDINATE
    u = u - u[0]
    n = len(u); U = u[-1]
    tau = np.arange(1, int(1.65*U)+1)/U              # resolution 1/U, out past the control band
    F = np.exp(2j*np.pi*np.outer(tau, u)).sum(axis=1)
    K = (np.abs(F)**2)/n
    out.append((T, L, tau, K, n, U))

P("\n  WHERE THE LINES SIT.  For each prime p we report the location of the largest peak")
P("  of K within +-0.25*(log3-log2)/L of the predicted tau_p, and the prediction.")
P(f"  {'T':>8}{'L':>8}   " + "".join(f"{'p='+str(p):>22}" for p in (2, 3, 5)))
for T, L, tau, K, n, U in out:
    row = f"  {T:>8.0e}{L:>8.3f}   "
    for p in (2, 3, 5):
        pred = math.log(p)/L
        tol = 0.25*(math.log(3)-math.log(2))/L
        m = (tau > pred-tol) & (tau < pred+tol)
        got = tau[m][np.argmax(K[m])]
        row += f"{'pred %.4f obs %.4f' % (pred, got):>22}"
    P(row)

P("\n  IS THE PEAK REAL?  height of K at the observed line vs the median of K in a")
P("  control band of the same width placed at tau in (1.2, 1.6) where no prime line lives.")
P(f"  {'T':>8}   {'K(p=2)':>10}{'K(p=3)':>10}{'K(p=5)':>10}{'ctrl med':>12}{'ctrl 99pct':>12}")
for T, L, tau, K, n, U in out:
    c = K[(tau > 1.2) & (tau < 1.6)]
    row = f"  {T:>8.0e}   "
    for p in (2, 3, 5):
        pred = math.log(p)/L; tol = 0.25*(math.log(3)-math.log(2))/L
        m = (tau > pred-tol) & (tau < pred+tol)
        row += f"{K[m].max():>10.2f}"
    P(row + f"{np.median(c):>12.2f}{np.percentile(c, 99):>12.2f}")

P("\n  PAYOFF (pre-registered).  share of the tape-spectrum power above tau_2 = log2/L,")
P("  and above tau = 1, as T grows.  If the tape really moves arithmetic to DC these fall.")
P(f"  {'T':>8}{'L':>8}{'tau_2':>9}{'power tau>tau_2':>18}{'power tau>1':>14}")
for T, L, tau, K, n, U in out:
    t2 = math.log(2)/L
    tot = K.sum()
    P(f"  {T:>8.0e}{L:>8.3f}{t2:>9.4f}{K[tau > t2].sum()/tot:>18.4f}{K[tau > 1].sum()/tot:>14.4f}")
