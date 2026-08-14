"""STEP 2b -- controls that separate real structure from artifacts.

A. EDGE CONTROL. In the paper d = floor(T/h'), so the k-sum is truncated at the window
   ends and zeros near T and 2T see a partial sum.  Extend k past both ends by the
   numerical reach; if the residual wiggle on c<=1 is pure edge effect, C becomes
   EXACTLY constant.
B. FINE SWEEP across the c=1 transition (step 0.002) to locate the plateau edge and
   place pi/3 on it.
C. SPECTRUM: rank, n_+ and the dimension cap of Prop 7.4 as functions of c.
D. LATTICE OFFSET: tau_k = T + (k+theta)h'.  Under the tight-frame identity C must be
   offset-blind for c<=1; any harmonic structure would have to show up here.
"""
import numpy as np
from zeta23_bench import phihat, a_const, load_zeros, traces

T = 2000.0
l = np.log(T / (2 * np.pi))
l1 = l + 2 * np.log(2) - 1
NI = T * l1 / (2 * np.pi)
LAM, ETA = 1.0, 0.05
L, w = LAM * l, ETA * LAM * l / 2
a = a_const(L, w)
gam_all = load_zeros()
gam = gam_all[(gam_all >= 1700.0) & (gam_all <= 4300.0)]

REACH = 300.0     # |phihat| < 2e-6 * max beyond 300; covers the D0=44.7 reach 6x over


def traces_ext(gam, T, L, w, c, pad=REACH, theta=0.0, chunk=4096):
    """k-sum extended by `pad` past both window ends; tau_k = T + (k+theta)h'."""
    h = c * 2 * np.pi / L
    k0 = int(np.floor(-pad / h)) - 1
    k1 = int(np.ceil((T + pad) / h)) + 1
    N = gam.size
    K = np.zeros((N, N))
    trG = 0.0
    for s in range(k0, k1, chunk):
        k = np.arange(s, min(s + chunk, k1), dtype=np.float64)
        tau = T + (k + theta) * h
        M = phihat(gam[None, :] - tau[:, None], L, w)
        trG += float(np.einsum('ki,ki->', M, M))
        K += M.T @ M
    return k1 - k0, trG, float(np.einsum('ij,ij->', K, K))


named = {"1/6": 1/6, "1/3": 1/3, "1/2": .5, "2/3": 2/3, "5/6": 5/6, "3/pi": 3/np.pi,
         "1": 1.0, "pi/3": np.pi/3, "7/6": 7/6, "4/3": 4/3, "3/2": 1.5, "2": 2.0}

print("=" * 92)
print("A. EDGE CONTROL: k-sum extended by +-300 past the window ends")
print("=" * 92)
print(f"{'c':>8} {'name':>6} {'d_ext':>7} {'trGt':>12} {'C':>12} {'C/N':>9} "
      f"{'C/C(c=1)':>10}")
base = None
extrows = []
for nm, c in sorted(named.items(), key=lambda kv: kv[1]):
    d, trG, trG2 = traces_ext(gam, T, L, w, c)
    C = trG**2 / trG2
    if abs(c - 1.0) < 1e-12:
        base = C
    extrows.append((c, nm, d, trG / L, C))
for c, nm, d, trGt, C in extrows:
    print(f"{c:8.4f} {nm:>6} {d:7d} {trGt:12.3f} {C:12.6f} {C/NI:9.6f} {C/base:10.7f}")
print("  -> flat to machine precision on c<=1 == the Gabor system is a TIGHT FRAME there")

print()
print("=" * 92)
print("B. FINE SWEEP across the transition (paper's truncation, d=floor(T/h'))")
print("=" * 92)
print(f"{'c':>8} {'d':>6} {'C':>11} {'C/N':>9} {'cert':>8}")
NIp = ((2*T+44.7)/(2*np.pi)*(np.log((2*T+44.7)/(2*np.pi))-1)
       - (T-44.7)/(2*np.pi)*(np.log((T-44.7)/(2*np.pi))-1))
fine = sorted(set(list(np.round(np.arange(0.950, 1.1501, 0.002), 6))
                  + [3/np.pi, np.pi/3, 1.0]))
for c in fine:
    d, trG, trG2, _ = traces(gam, T, L, w, c)
    C = trG**2 / trG2
    tag = ""
    if abs(c-np.pi/3) < 1e-9: tag = "  <- pi/3"
    if abs(c-3/np.pi) < 1e-9: tag = "  <- 3/pi"
    if abs(c-1.0) < 1e-12: tag = "  <- c=1 (theirs)"
    print(f"{c:8.5f} {d:6d} {C:11.4f} {C/NI:9.6f} {(2*C-NIp)/NI:8.4f}{tag}")

print()
print("=" * 92)
print("C. SPECTRUM and the Prop 7.4 dimension cap")
print("=" * 92)
print(f"{'c':>8} {'d':>6} {'d/N':>7} {'rank G':>7} {'n_+(G)':>7} {'lam_max/L':>10} "
      f"{'C':>10} {'C/N':>8}")
for nm, c in sorted(named.items(), key=lambda kv: kv[1]):
    d, trG, trG2, K = traces(gam, T, L, w, c)
    ev = np.linalg.eigvalsh(K)          # K = M^T M has the same nonzero spectrum as G
    tol = max(ev) * 1e-10
    C = trG**2 / trG2
    print(f"{c:8.4f} {d:6d} {d/NI:7.4f} {int((ev > tol).sum()):7d} "
          f"{int((ev > tol).sum()):7d} {ev.max()/L:10.4f} {C:10.3f} {C/NI:8.5f}")

print()
print("=" * 92)
print("D. LATTICE OFFSET theta (extended k-sum): C must be offset-blind for c<=1")
print("=" * 92)
print(f"{'c':>8} " + " ".join(f"{'th='+str(t):>12}" for t in [0.0, 0.25, 0.5, 1/3, 1/6]))
for c in [0.5, 3/np.pi, 1.0, np.pi/3, 4/3]:
    vals = []
    for th in [0.0, 0.25, 0.5, 1/3, 1/6]:
        d, trG, trG2 = traces_ext(gam, T, L, w, c, theta=th)
        vals.append(trG**2 / trG2)
    print(f"{c:8.4f} " + " ".join(f"{v:12.5f}" for v in vals)
          + f"   spread={np.ptp(vals):.3e}")
