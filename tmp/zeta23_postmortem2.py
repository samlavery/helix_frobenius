"""POST-MORTEM part 2.
PM4  precision: cancellation amplification, mpmath ground truth, input-data sensitivity
PM5  narrow-feature search at ultra-fine c resolution around every harmonic value
"""
import numpy as np
import mpmath as mp
from zeta23_bench import phihat, phi, a_const, load_zeros, traces
from zeta23_controls import traces_ext

GAM = load_zeros()
np.random.seed(20260811)
T = 2000.0
l = np.log(T / (2 * np.pi))
L, w = l, 0.05 * l / 2
NI = T * (l + 2 * np.log(2) - 1) / (2 * np.pi)
gam = GAM[(GAM >= 1700.) & (GAM <= 4300.)]

print("=" * 90)
print("PM4. PRECISION")
print("=" * 90)

# (a) cancellation amplification: ||abs-sum||_F vs ||K||_F  (roundoff ~ eps*sqrt(d)*ratio)
h = 2 * np.pi / L
d = int(T / h)
k = np.arange(d, dtype=np.float64)
M = phihat(gam[None, :] - (T + k * h)[:, None], L, w)
K = M.T @ M
A = np.abs(M).T @ np.abs(M)
ratio = np.linalg.norm(A) / np.linalg.norm(K)
print(f"  (a) cancellation amplification ||sum|MM|||_F / ||K||_F = {ratio:.4f}")
print(f"      => est. relative roundoff in tr G^2 ~ eps*sqrt(d)*ratio^2 = "
      f"{2.2e-16*np.sqrt(d)*ratio**2:.2e}   (tr G has NO cancellation: all terms > 0)")

# (b) mpmath ground truth on a reduced but structurally complete problem
print("  (b) mpmath ground truth (dps=40) vs float64, reduced problem T=50:")
mp.mp.dps = 40
Ts = mp.mpf(50)
ls = mp.log(Ts / (2 * mp.pi))
Ls, ws = ls, mp.mpf('0.05') * ls / 2
gs = [mp.mpf(x) for x in GAM[(GAM >= 20) & (GAM <= 130)]]


def phihat_mp(r, L, w):
    r = abs(r)
    A_, B_ = L / 2 - w, L / 2
    s, th = r * w, r * B_
    if r == 0:
        return 2 * A_ + 2 * w * mp.quad(lambda x: x - mp.sin(2 * mp.pi * x) / (2 * mp.pi), [0, 1])
    flat = 2 * mp.sin(r * A_) / r
    Cc = mp.quad(lambda x: (x - mp.sin(2*mp.pi*x)/(2*mp.pi)) * mp.cos(s*x), [0, 1])
    Cs = mp.quad(lambda x: (x - mp.sin(2*mp.pi*x)/(2*mp.pi)) * mp.sin(s*x), [0, 1])
    return flat + 2 * w * (mp.cos(th) * Cc + mp.sin(th) * Cs)


for c in [mp.mpf(1)/2, 3/mp.pi, mp.mpf(1), mp.pi/3]:
    hs = c * 2 * mp.pi / Ls
    ds = int(mp.floor(Ts / hs))
    t1 = mp.mpf(0)
    Km = [[mp.mpf(0)] * len(gs) for _ in gs]
    for kk in range(ds):
        tau = Ts + kk * hs
        v = [phihat_mp(g - tau, Ls, ws) for g in gs]
        for i in range(len(gs)):
            t1 += v[i] ** 2
            for j in range(len(gs)):
                Km[i][j] += v[i] * v[j]
    t2 = sum(Km[i][j] ** 2 for i in range(len(gs)) for j in range(len(gs)))
    Cmp = t1 ** 2 / t2
    # float64 same problem
    Lf, wf, Tf = float(Ls), float(ws), float(Ts)
    gf = GAM[(GAM >= 20) & (GAM <= 130)]
    df, a1, a2, _ = traces(gf, Tf, Lf, wf, float(c))
    Cf = a1 ** 2 / a2
    print(f"      c={float(c):7.4f}  d={ds:3d}  C_mp={mp.nstr(Cmp,16)}  C_f64={Cf:.16f}  "
          f"rel diff={float(abs(Cmp-Cf)/Cmp):.2e}")

# (c) input-data sensitivity: cached zeros carry ~5e-11 error
print("  (c) sensitivity to the 5e-11 uncertainty in the cached zero ordinates:")
base = None
vals = []
for trial in range(12):
    g = gam if trial == 0 else gam + np.random.normal(0, 5e-11, gam.size)
    dd, t1, t2, _ = traces(g, T, L, w, 1.0)
    C = t1**2/t2
    if trial == 0:
        base = C
    else:
        vals.append(C)
vals = np.array(vals)
print(f"      C(unperturbed) = {base:.8f}   perturbed: mean {vals.mean():.8f}  "
      f"sd {vals.std(ddof=1):.2e}  max|dC|/C = {np.abs(vals-base).max()/base:.2e}")

# (d) float32 as a conditioning probe
M32 = M.astype(np.float32)
C32 = float(np.einsum('ki,ki->', M32, M32))**2 / float(
    np.einsum('ij,ij->', M32.T @ M32, M32.T @ M32))
print(f"  (d) float32 recompute: C={C32:.4f} vs float64 C={float(np.einsum('ki,ki->',M,M))**2/float(np.einsum('ij,ij->',K,K)):.4f}"
      f"  rel diff={abs(C32-base)/base:.2e}  (eps_32/eps_64 = 5e8; so f64 error ~ this/5e8)")

# ------------------------------------------------------------------ PM5
print()
print("=" * 90)
print("PM5. NARROW-FEATURE SEARCH")
print("=" * 90)
print("  (a) frame-operator deviation sup_tau |sum_k phihat(tau-tau_k)^2 - aL^2/c|,")
print("      ultra-fine sweep. This is ZERO-FREE: if it stays at truncation noise on")
print("      c<=1 then C is provably c-invariant there and NO narrow feature can exist.")
aL2 = a_const(L, w) * L**2
KM = 100000
kk = np.arange(-KM, KM + 1, dtype=np.float64)
taus = T + np.array([0.0, 0.11, 0.27, 0.53, 0.79])
for cent, nm in [(1/6, "1/6"), (1/3, "1/3"), (0.5, "1/2"), (2/3, "2/3"),
                 (5/6, "5/6"), (3/np.pi, "3/pi"), (1.0, "1"), (np.pi/3, "pi/3")]:
    worst = 0.0
    for c in cent + np.arange(-20, 21) * 2e-4:
        if c <= 0:
            continue
        hh = c * 2 * np.pi / L
        for tau in taus:
            s = float(np.sum(phihat(tau - (T + kk * hh), L, w)**2))
            worst = max(worst, abs(s - aL2 / c) / (aL2 / c))
    print(f"      c in {nm:>5} +- 0.004 (step 2e-4):  sup relative frame deviation = {worst:.3e}")

print("  (b) direct C sweep at step 2e-4 around each harmonic value, edge-controlled,")
print("      reduced height T=500 (cost); the plateau is height-independent by PM1.")
T5 = 500.0
l5 = np.log(T5 / (2 * np.pi))
L5, w5 = l5, 0.05 * l5 / 2
g5 = GAM[(GAM >= 200.) & (GAM <= 1300.)]
for cent, nm in [(1/3, "1/3"), (0.5, "1/2"), (2/3, "2/3"), (5/6, "5/6"),
                 (3/np.pi, "3/pi"), (np.pi/3, "pi/3")]:
    cs = cent + np.arange(-15, 16) * 2e-4
    Cs = []
    for c in cs:
        _, t1, t2 = traces_ext(g5, T5, L5, w5, c, pad=200.)
        Cs.append(t1**2/t2)
    Cs = np.array(Cs)
    ctr = Cs[15]
    resid = Cs - np.poly1d(np.polyfit(cs, Cs, 1))(cs)   # remove the smooth drift
    print(f"      {nm:>5}: C(center)={ctr:.6f}  range over window={np.ptp(Cs):.2e}  "
          f"center residual from linear fit = {resid[15]:+.2e} "
          f"(window residual sd {resid.std():.2e})")
