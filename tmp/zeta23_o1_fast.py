"""Fast D / O_1 split, so the T-scaling of the common mode can be tested.

Reparametrise (k,l) -> (p,j): p = k-l >= 0, j = min(k,l), so delta = p h and
mbar = T + p h/2 + j h =: A_p + j h, with j = 0..d-1-p.  Then

    P(p,j) = -2 sum_n a_n R_n(ph) cos((A_p + jh) u_n)
           = -2 [ C @ gc_p - S @ gs_p ]_j ,     C[j,n] = cos(j h u_n), S[j,n] = sin(j h u_n)
    Q(p,j) = -2 [ S @ gc_p + C @ gs_p ]_j ,     gc_p[n] = a_n R_n(ph) cos(A_p u_n), etc.

C and S do not depend on p, so the whole thing is four BLAS gemms: O(d^2 N) at full speed
instead of O(d^2 N) in a Python loop.
"""
import time
import numpy as np

from zeta23_bench import phihat
from zeta23_prime import prime_powers, R_amb


def R_table(u, L, w, d, h, verbose=False):
    """Rtab[n, p] = R(u_n, p*h) for p = 0..d-1."""
    deltas = np.arange(d) * h
    Rt = np.empty((u.size, d))
    nb = 0
    for i in range(u.size):
        if w <= u[i] <= L - 2 * w:
            Rt[i] = phihat(deltas, L - u[i], w)
        else:
            Rt[i] = R_amb(u[i], deltas, L, w)
            nb += 1
    if verbose:
        print(f"      R table: {u.size} prime powers, {nb} needed the boundary treatment")
    return Rt


def split_fast(T, L, w, lam, u, c=1.0, pchunk=None, verbose=False):
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    keep = u < L
    a = (lam * np.exp(-0.5 * u))[keep]
    uu = u[keep]
    N = uu.size
    Rt = R_table(uu, L, w, d, h, verbose)
    jj = np.arange(d)
    C = np.cos(np.outer(jj * h, uu))
    S = np.sin(np.outer(jj * h, uu))
    A = T + np.arange(d) * h / 2.0                       # A_p
    sP2 = sQ2 = 0.0
    if pchunk is None:
        pchunk = max(1, int(3e7 // max(N, 1)))
    mask_full = jj[:, None] <= (d - 1 - np.arange(d))[None, :]
    for p0 in range(0, d, pchunk):
        p1 = min(p0 + pchunk, d)
        pw = np.arange(p0, p1)
        ang = np.outer(uu, A[pw])                        # (N, np)
        base = (a[:, None] * Rt[:, pw])
        Gc = base * np.cos(ang)
        Gs = base * np.sin(ang)
        P = -2.0 * (C @ Gc - S @ Gs)                     # (d, np)
        Q = -2.0 * (S @ Gc + C @ Gs)
        m = mask_full[:, pw]
        wgt = np.where(pw[None, :] == 0, 1.0, 2.0) * m   # p=0 once, p>0 twice
        sP2 += float(np.sum(wgt * P**2))
        sQ2 += float(np.sum(wgt * Q**2))
    # D = 2 sum_n a_n^2 sum_{k,l} R(u_n, delta_kl)^2
    cnt = np.concatenate([[d], 2 * (d - np.arange(1, d))])
    D = 2.0 * float(np.sum(a**2 * (Rt**2 @ cnt)))
    minus = 0.5 * (sP2 + sQ2)
    return d, sP2, D, minus - D, 0.5 * (sP2 - sQ2)


def run(T, ETA, lams, tag=""):
    l = np.log(T / (2 * np.pi))
    l1 = l + 2 * np.log(2) - 1
    print(f"\nT={T:.0f}  l={l:.5f}  l1={l1:.5f}  eta={ETA}  {tag}")
    print(f"{'lam':>5} {'lam1':>6} {'L':>7} {'X':>9} {'Npp':>7} {'d':>5} "
          f"{'D/L^2':>11} {'O1/L^2':>11} {'O1_main':>11} {'meas/main':>9} "
          f"{'|O1|/D':>8} {'bound/|O1|':>10}  [s]")
    out = []
    for lam in lams:
        t0 = time.time()
        L = lam * l
        w = ETA * L / 2
        if ETA * L > 2 * np.log(2):
            print(f"{lam:5.2f}  SKIP eta*L={ETA*L:.3f} > 2log2")
            continue
        X = np.exp(L)
        lamv, u = prime_powers(X)
        d, sP2, D, O1, O2 = split_fast(T, L, w, lamv, u)
        pred = -(T / (6 * np.pi)) * max(L - l1, 0.0)**3
        r = (O1 / L**2) / pred if pred != 0 else float('nan')
        print(f"{lam:5.2f} {L/l1:6.3f} {L:7.3f} {X:9.0f} {u.size:7d} {d:5d} "
              f"{D/L**2:11.2f} {O1/L**2:11.2f} {pred:11.2f} {r:9.3f} "
              f"{abs(O1/D):8.4f} {L**2*X/max(abs(O1),1e-9):10.1f}  [{time.time()-t0:.0f}]")
        out.append((lam, D/L**2, O1/L**2, pred, r))
    return out


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "tscale":
        for T in [300., 600., 1000., 1500., 2000.]:
            run(T, 0.02, [1.5, 1.75, 2.0], tag="T-scaling at fixed lambda")
    elif len(sys.argv) > 1 and sys.argv[1] == "taper":
        for eta in [0.01, 0.02, 0.05]:
            run(600., eta, [1.75, 2.0, 2.25, 2.5], tag="taper dependence")
    else:
        run(600., 0.02, [0.6, 0.8, 1.0, 1.1, 1.25, 1.5, 1.75, 2.0, 2.25, 2.5])
