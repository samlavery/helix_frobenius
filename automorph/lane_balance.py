"""Sam's yes/no question (2026-07-02): at a cancellation height, compute the
magnitudes of the positive and negative phasor lanes separately. Is the
eigenstate the zero of the expanded 3D state space?

Two fibers: (a) eta lanes for zeta (P = odd n, M = even n, readout = P - M)
at the audited zero t0 = 14.134725142; (b) quadratic chi_5 lanes (P: chi=+1,
M: chi=-1) at its first zero (located by scan). Smooth entry weights e^{-n/N}
(never clip) plus sharp-head comparison."""
import numpy as np

def lanes_eta(t, N, smooth=True):
    n = np.arange(1, N + 1, dtype=np.float64)
    w = np.exp(-n / N) if smooth else np.ones_like(n)
    ph = w * n ** -0.5 * np.exp(-1j * t * np.log(n))
    P = ph[0::2].sum()   # odd n (positive lane)
    M = ph[1::2].sum()   # even n (negative lane)
    return P, M

def lanes_chi5(t, N):
    n = np.arange(1, N + 1, dtype=np.float64)
    chi = np.array([0, 1, -1, -1, 1], dtype=np.float64)[(np.arange(1, N + 1)) % 5]
    w = np.exp(-n / N)
    ph = w * n ** -0.5 * np.exp(-1j * t * np.log(n))
    P = ph[chi == 1].sum()
    M = ph[chi == -1].sum()
    return P, M

N = 10**6
print(f"head N = {N:.0e}, smooth entry e^(-n/N)")
print("=" * 68)

t0 = 14.134725142
Ps, Ms = lanes_eta(t0, N, smooth=True)
Ph, Mh = lanes_eta(t0, N, smooth=False)
print(f"(a) eta fiber at the zeta zero t0 = {t0}")
print(f"    smooth:  |P| = {abs(Ps):.6f}   |M| = {abs(Ms):.6f}   |P-M| = {abs(Ps-Ms):.2e}")
print(f"    sharp :  |P| = {abs(Ph):.6f}   |M| = {abs(Mh):.6f}   |P-M| = {abs(Ph-Mh):.2e}")
print(f"    lane ratio |P|/|M| = {abs(Ps)/abs(Ms):.10f}")
print(f"    cup energy |P|^2 + |M|^2 = {abs(Ps)**2 + abs(Ms)**2:.4f}   readout |P-M|^2 = {abs(Ps-Ms)**2:.2e}")
print(f"    state distance from 3D zero vector: {np.hypot(abs(Ps), abs(Ms)):.4f}")

# (b) chi_5: locate first zero by scanning the smoothed readout
print()
ts = np.linspace(6.0, 7.2, 2401)
Nq = 200000
vals = []
n = np.arange(1, Nq + 1, dtype=np.float64)
chi = np.array([0, 1, -1, -1, 1], dtype=np.float64)[(np.arange(1, Nq + 1)) % 5]
w = np.exp(-n / Nq)
base = w * n ** -0.5
logn = np.log(n)
for t in ts:
    vals.append(abs((chi * base * np.exp(-1j * t * logn)).sum()))
vals = np.array(vals)
i = vals.argmin()
# refine
lo, hi = ts[max(i-1,0)], ts[min(i+1,len(ts)-1)]
for _ in range(40):
    mid1, mid2 = lo + (hi-lo)/3, hi - (hi-lo)/3
    v1 = abs((chi * base * np.exp(-1j * mid1 * logn)).sum())
    v2 = abs((chi * base * np.exp(-1j * mid2 * logn)).sum())
    if v1 < v2: hi = mid2
    else: lo = mid1
tz = (lo + hi) / 2
P5, M5 = lanes_chi5(tz, N)
print(f"(b) chi_5 fiber, first zero located at t = {tz:.9f}  (scan+ternary refine)")
print(f"    |P| = {abs(P5):.6f}   |M| = {abs(M5):.6f}   |P-M| = {abs(P5-M5):.2e}")
print(f"    lane ratio |P|/|M| = {abs(P5)/abs(M5):.10f}")
print(f"    cup energy |P|^2 + |M|^2 = {abs(P5)**2 + abs(M5)**2:.4f}   readout |P-M|^2 = {abs(P5-M5)**2:.2e}")
print()
print("ANSWER: is the cancellation eigenstate the zero of the 3D state space?")
for name, P, M in (("eta", Ps, Ms), ("chi5", P5, M5)):
    iszero = np.hypot(abs(P), abs(M)) < 1e-6
    print(f"    {name}: state = (|P|,|M|) = ({abs(P):.4f}, {abs(M):.4f})  ->  {'YES' if iszero else 'NO — nonzero balanced doublet; only the readout P-M dies'}")

# --- pi/3 scaling (owner, 2026-07-02): read the opposition in hexagonal units ---
print()
print("pi/3-SCALED READING: lane opposition in hexagonal (mu6) units")
import cmath
for name, P, M, t in (("eta ", Ps, Ms, t0), ("chi5", P5, M5, tz)):
    dphi = cmath.phase(P / M)          # opposition angle between the lanes
    units = dphi / (np.pi / 3)         # in pi/3 steps
    print(f"    {name} t={t:<13.9f} arg(P/M) = {dphi:+.9f} rad = {units:+.7f} x (pi/3)"
          f"   [exact opposition = 3 units = half the mu6 cell]")
    print(f"          residual from exact 3-step closure: {abs(abs(units)-3):.2e} units")
