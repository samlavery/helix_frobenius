#!/usr/bin/env python3
"""
att241 — the minimizer as a ZERO-CLOCK COMB + registration tuning width.

PRE-REGISTERED:
  H4 (comb): the even-sector minimizer's Ghat has its real zeros pinned at the
     actual zeta zeros gamma_1, gamma_2, ... up to a cutoff R(L) growing with L;
     the Gaussian-in-L collapse rate is the growing tooth count.  FALSIFIER:
     minimizer zeros NOT near gamma_n (say off by >> zero spacing), or tooth
     count not growing with L.
  H5 (tuning): positivity past e^L ~ 2.3 is an exact registration on the prime-2
     clock: perturbing the weight Lambda(2) -> t*Lambda(2) or the position
     log2 -> log2 + eps kills it; the measured window shrinks with L like the
     margin/  (sensitivity) — our analog of CC's "p within 1e-3 of 2".
"""
import numpy as np
from scipy.linalg import eigh
import att239_weil_support_bench as B
import att240_margin_law as C

LOG2, LOG3 = np.log(2.0), np.log(3.0)
ZEROS = np.load("att015_zeros_to_30000.npy")

def minimizer(L, K=45, Nq=1600):
    lam, c = C.lam_min_sector(L, "even", K=K, Nq=Nq)
    a = L / 2.0
    c = c / np.sqrt(c @ B.gram(K, a) @ c)
    return lam, c

def ghat_zeros(c, K, a, rmax=80.0):
    r = np.arange(0.0, rmax, 0.005)
    g = B.ghat(c, r, K, a)
    s = np.where(np.diff(np.sign(g)) != 0)[0]
    roots = []
    for i in s:
        lo, hi = r[i], r[i + 1]
        for _ in range(40):
            mid = 0.5 * (lo + hi)
            if B.ghat(c, np.array([lo]), K, a)[0] * B.ghat(c, np.array([mid]), K, a)[0] <= 0:
                hi = mid
            else:
                lo = mid
        roots.append(0.5 * (lo + hi))
    return np.array(roots)

def comb_portrait():
    print("== H4: MINIMIZER ZERO COMB vs ACTUAL ZETA ZEROS ==")
    print(f"  first zeta zeros: {np.array2string(ZEROS[:10], precision=3)}")
    for L in [0.30, 0.45, 0.60, 0.80, 1.00, LOG3, 1.13]:
        lam, c = minimizer(L)
        a = L / 2.0
        roots = ghat_zeros(c, 45, a)
        matched = []
        for rt in roots:
            j = np.argmin(np.abs(ZEROS - rt))
            matched.append((rt, ZEROS[j], rt - ZEROS[j]))
        print(f"  L = {L:.4f}  lam = {lam:+.3e}   Ghat real zeros in (0,80): {len(roots)}")
        for rt, gz, d in matched[:8]:
            print(f"      root {rt:8.4f}   nearest gamma {gz:8.4f}   offset {d:+8.4f}")

def curvature_long_baseline():
    print("== CURVATURE REFINEMENT (longer L baseline, even sector) ==")
    data = []
    for L in list(np.arange(0.25, 0.45, 0.05)) + list(np.arange(0.45, 1.14, 0.04)):
        lam, _ = C.lam_min_sector(L, "even")
        data.append((L, lam))
        print(f"  L = {L:.3f}  lam = {lam:+.6e}")
    L = np.array([d[0] for d in data]); lam = np.array([d[1] for d in data])
    m = lam > 1e-12
    x, y = L[m], np.log(lam[m])
    for name, Amat in [("quad", np.vstack([np.ones_like(x), x, x**2]).T),
                       ("quad+L2lnL", np.vstack([np.ones_like(x), x, x**2, x**2*np.log(x)]).T)]:
        cfit, res, *_ = np.linalg.lstsq(Amat, y, rcond=None)
        rms = np.sqrt(res[0]/len(x)) if len(res) else 0.0
        print(f"  fit {name:11s}: {np.array2string(cfit, precision=3)}   rms {rms:.4f}")
    # windowed curvature: is C stable or drifting?
    for lo, hi in [(0.25, 0.70), (0.60, 0.95), (0.85, 1.13)]:
        mm = m & (L >= lo) & (L <= hi)
        xx, yy = L[mm], np.log(lam[mm])
        cf, *_ = np.linalg.lstsq(np.vstack([np.ones_like(xx), xx, xx**2]).T, yy, rcond=None)
        print(f"  window [{lo:.2f},{hi:.2f}]: curvature C = {cf[0][2] if isinstance(cf, tuple) else cf[2]:+.3f}")

def weil_matrix_tuned(L, K, Nq, t2=1.0, eps2=0.0):
    """even-sector Weil matrix with prime-2 weight scaled by t2 and clock
    position shifted log2 -> log2 + eps2 (other prime powers unchanged)."""
    a = L / 2.0
    M = -B.arch_matrix(K, a, Nq)
    for n, lam in B.prime_powers(L):
        w, pos = lam, np.log(n)
        if n == 2:
            w, pos = t2 * lam, np.log(2.0) + eps2
        M -= 2.0 * (w / np.sqrt(n)) * B.S_all(pos, K, a)
    p = B.pole_vec(K, a)
    M += 2.0 * np.outer(p, p)
    return M

def lam_tuned(L, K=35, Nq=1200, t2=1.0, eps2=0.0):
    a = L / 2.0
    lam, _ = eigh(weil_matrix_tuned(L, K, Nq, t2, eps2), B.gram(K, a),
                  subset_by_index=[0, 0])
    return lam[0]

def tuning_width():
    print("== H5: REGISTRATION TUNING (weight t*Lambda(2), position log2+eps) ==")
    for L in [0.90, 1.00, 1.09]:
        lam0 = lam_tuned(L)
        # weight sensitivity
        dt = 2e-3
        d_w = (lam_tuned(L, t2=1 + dt) - lam_tuned(L, t2=1 - dt)) / (2 * dt)
        # position sensitivity
        de = 2e-3
        d_p = (lam_tuned(L, eps2=de) - lam_tuned(L, eps2=-de)) / (2 * de)
        w_win = abs(lam0 / d_w) if d_w != 0 else np.inf
        p_win = abs(lam0 / d_p) if d_p != 0 else np.inf
        print(f"  L = {L:.2f}: lam0 = {lam0:+.3e}   dlam/dt = {d_w:+.3e} -> weight window ~ {w_win:.2e}")
        print(f"           dlam/deps = {d_p:+.3e} -> position window ~ {p_win:.2e}")
        # direct check: does positivity actually die at the predicted offsets?
        for t2 in [1 - 3*w_win, 1 + 3*w_win]:
            if 0 < t2 < 2:
                print(f"           direct: lam(t2={t2:.5f}) = {lam_tuned(L, t2=t2):+.3e}")
        for e2 in [-3*p_win, 3*p_win]:
            print(f"           direct: lam(eps2={e2:+.5f}) = {lam_tuned(L, eps2=e2):+.3e}")

def main():
    comb_portrait()
    curvature_long_baseline()
    tuning_width()

if __name__ == "__main__":
    main()
