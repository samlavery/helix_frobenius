#!/usr/bin/env python3
"""
att242 — THE SYMBOL REDUCTION + FLOOR CERTIFICATE for unconditional Weil
positivity past log 2 (target: all supports L < log 3, executed at L-grid).

IDENTITY (exact, unconditional; proof = EF display + Plancherel + support):
  for supp G in [-a, a], 2a < log 3:
    Q(G) = 2 P+ P-  +  (1/2pi) int sigma(r) |Ghat(r)|^2 dr,
    sigma(r) = Re psi(1/4 + ir/2) - log pi - sqrt(2) log2 cos(r log2).
  (The whole prime side IS the 2-clock cosine: all other atoms fall outside
   the autocorrelation support.  Numerically cross-checked against the
   att239 assembly, which was itself validated against 35,673 zeros.)

CERTIFICATE LEMMA (exact): with s0 := inf_{|r| >= R2} sigma(r) > 0,
    Q(G) >= s0 ||G||^2 + 2 P+ P- + (1/2pi) int_{-R2}^{R2} (sigma - s0)|Ghat|^2 dr
  so PSD-ness of  s0*Gram + Pole + Band(sigma - s0; R2)  on L^2(-a,a)
  implies Weil positivity at support 2a.  Band is compact (type a*R2).

PRE-REGISTERED:
  C1: sigma < 0 on exactly TWO regions below r=60: the Gamma-well around 0 and
      the first 2-clock resonance dip near r = 2pi/log2 = 9.0647; the second
      resonance (18.13) stays positive.  FALSIFIER: any other negative region.
  C2: the floor certificate closes (lam_min > 0) at L = 0.90 for moderate R2.
  C3: pushing L up, the float certificate dies somewhere below log 3; record
      the certified frontier and the slack ledger.
"""
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh
from scipy.special import digamma
import att239_weil_support_bench as B
import att240_margin_law as C

LOG2, LOG3 = np.log(2.0), np.log(3.0)
C2 = np.sqrt(2.0) * LOG2          # 2 * Lambda(2)/sqrt(2) = sqrt2 log2
RES = 2 * np.pi / LOG2            # first 2-clock resonance 9.0647

def sigma(r):
    r = np.asarray(r, dtype=float)
    return np.real(digamma(0.25 + 0.5j * r)) - np.log(np.pi) - C2 * np.cos(r * LOG2)

def ghat_basis(K, a, r, parity="even"):
    """matrix [k, i] = phi_k-hat(r_i) for the cos (even) or sin (odd) basis."""
    if parity == "even":
        om = np.arange(K + 1) * np.pi / a
        rp = om[:, None] + r[None, :]
        rm = om[:, None] - r[None, :]
        def sc(x):
            y = np.where(np.abs(x) < 1e-12, 1.0, x)
            return np.where(np.abs(x) < 1e-12, a, np.sin(y * a) / y)
        return sc(rp) + sc(rm)
    om = np.arange(1, K + 1) * np.pi / a
    rp = om[:, None] + r[None, :]
    rm = om[:, None] - r[None, :]
    def sc(x):
        y = np.where(np.abs(x) < 1e-12, 1.0, x)
        return np.where(np.abs(x) < 1e-12, a, np.sin(y * a) / y)
    return sc(rm) - sc(rp)        # int sin(om u) sin(ru) du on [-a,a]

# ---------------------------------------------------------------- C1: sigma
def negative_set(rmax=60.0, step=5e-4):
    r = np.arange(step, rmax, step)
    s = sigma(r)
    sgn = np.sign(s)
    idx = np.where(np.diff(sgn) != 0)[0]
    roots = []
    for i in idx:
        lo, hi = r[i], r[i + 1]
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            if sigma(lo) * sigma(mid) <= 0:
                hi = mid
            else:
                lo = mid
        roots.append(0.5 * (lo + hi))
    print("== C1: THE SYMBOL'S NEGATIVE SET (r > 0) ==")
    print(f"  sigma(0) = {float(sigma(0.0)):+.6f}")
    print(f"  sign-change points below {rmax}: {[f'{x:.6f}' for x in roots]}")
    segs = []
    pts = [0.0] + roots + [rmax]
    for j in range(len(pts) - 1):
        mid = 0.5 * (pts[j] + pts[j + 1])
        if sigma(mid) < 0:
            segs.append((pts[j], pts[j + 1]))
    for lo, hi in segs:
        x, w = leggauss(400)
        rr = (x + 1) / 2 * (hi - lo) + lo
        ww = w / 2 * (hi - lo)
        area = np.sum(ww * np.abs(sigma(rr)))
        mn_i = np.argmin(sigma(rr))
        print(f"  NEGATIVE on ({lo:.6f}, {hi:.6f})  width {hi-lo:.4f}  "
              f"int|sigma| = {area:.6f}  min sigma = {sigma(rr[mn_i]):+.4f} at r = {rr[mn_i]:.4f}")
    print("  sigma at 2-clock resonances r = 2pi k/log2:")
    for k in range(1, 7):
        print(f"    k={k}: r = {k*RES:8.4f}   sigma = {float(sigma(k*RES)):+.6f}")
    return segs

_FLOOR_CACHE = {}
def floor_value(R2, rmax=3000.0):
    """s0 = min sigma on [R2, rmax]: coarse scan + local refinement, memoized."""
    if R2 in _FLOOR_CACHE:
        return _FLOOR_CACHE[R2]
    r = np.arange(R2, rmax, 0.01)
    s = sigma(r)
    i = np.argmin(s)
    lo = max(R2, r[i] - 0.02); hi = min(rmax, r[i] + 0.02)
    rf = np.linspace(lo, hi, 4001)
    sf = sigma(rf)
    j = np.argmin(sf)
    _FLOOR_CACHE[R2] = (min(s[i], sf[j]), rf[j])
    return _FLOOR_CACHE[R2]

# ---------------------------------------------------------------- identity xcheck
def identity_crosscheck(L=0.9, K=30):
    """Q via att239 assembly (validated vs zeros) vs Q via the symbol identity."""
    print("== IDENTITY CROSS-CHECK (att239 assembly vs symbol form) ==")
    a = L / 2.0
    rng = np.random.default_rng(3)
    c = rng.standard_normal(K + 1)
    M = B.weil_matrix(L, K, primes=True, pole=True)
    Q_asm = c @ M @ c
    # symbol side: 2P^2 + (1/2pi) int sigma |Ghat|^2 (even sector)
    P = c @ B.pole_vec(K, a)
    x, w = leggauss(6000)
    Rint = 6000.0
    r = (x + 1) / 2 * Rint; wr = w / 2 * Rint
    gh = c @ ghat_basis(K, a, r)
    Q_sym = 2 * P * P + (1.0 / np.pi) * np.sum(wr * sigma(r) * gh ** 2)
    print(f"  L = {L}: assembly {Q_asm:+.8f}   symbol {Q_sym:+.8f}   "
          f"rel diff {abs(Q_asm-Q_sym)/abs(Q_asm):.2e}  (symbol side truncated at r={Rint:.0f})")

# ---------------------------------------------------------------- budget
def minimizer_budget(L, R2list=(20.0, 30.0, 40.0, 60.0), K=60):
    print(f"== SPECTRAL BUDGET of the true minimizer, L = {L} (even sector) ==")
    a = L / 2.0
    lam, c = C.lam_min_sector(L, "even", K=K, Nq=1800)
    c = c / np.sqrt(c @ B.gram(K, a) @ c)
    P = c @ B.pole_vec(K, a)
    def band_mass(lo, hi, n=8000):
        x, w = leggauss(n)
        r = (x + 1) / 2 * (hi - lo) + lo
        wr = w / 2 * (hi - lo)
        gh = c @ ghat_basis(K, a, r)
        return (1.0 / np.pi) * np.sum(wr * sigma(r) * gh ** 2)
    segs = [(0, 6.8), (6.8, 8.0), (8.0, 10.2), (10.2, 20.0), (20.0, 40.0),
            (40.0, 100.0), (100.0, 400.0), (400.0, 3000.0)]
    tot = 2 * P * P
    print(f"  pole 2P^2 = {2*P*P:+.6e}")
    for lo, hi in segs:
        m = band_mass(lo, hi)
        tot += m
        print(f"  (1/2pi) int sigma|Ghat|^2, r in ({lo:6.1f},{hi:7.1f}) : {m:+.6e}")
    print(f"  TOTAL (should ~= lam_min = {lam:+.3e}) : {tot:+.3e}")
    for R2 in R2list:
        s0, arg = floor_value(R2)
        x, w = leggauss(12000)
        hi = 6000.0
        r = (x + 1) / 2 * (hi - R2) + R2
        wr = w / 2 * (hi - R2)
        gh = c @ ghat_basis(K, a, r)
        loss = (1.0 / np.pi) * np.sum(wr * (sigma(r) - s0) * gh ** 2)
        print(f"  R2 = {R2:5.1f}: s0 = {s0:+.4f} (at r = {arg:.2f})   "
              f"flooring loss at minimizer = {loss:+.3e}   margin = {lam:+.3e}")

# ---------------------------------------------------------------- certificate
def cert_bottom(L, R2, parity="even", K=80, nq=6000):
    """lam_min of the FLOOR CERTIFICATE form s0*Gram + Pole + Band(sigma-s0)."""
    a = L / 2.0
    s0, _ = floor_value(R2)
    x, w = leggauss(nq)
    r = (x + 1) / 2 * R2; wr = w / 2 * R2
    gh = ghat_basis(K, a, r, parity)
    Band = (1.0 / np.pi) * (gh * (wr * (sigma(r) - s0))[None, :]) @ gh.T
    if parity == "even":
        N = B.gram(K, a)
        p = B.pole_vec(K, a)
        M = s0 * N + 2 * np.outer(p, p) + Band
    else:
        N = C.gram_odd(K, a)
        p = C.pole_vec_odd(K, a)
        M = s0 * N - 2 * np.outer(p, p) + Band
    lam = eigh(M, N, subset_by_index=[0, 0], eigvals_only=True)
    return lam[0], s0

def certificate_runs():
    print("== C2/C3: FLOOR-CERTIFICATE BOTTOM (both sectors) ==")
    print(f"  {'L':>6} {'R2':>5} {'s0':>8} {'even lam_cert':>14} {'odd lam_cert':>14} {'true lam(even)':>14}")
    for L in [0.80, 0.90, 1.00, 1.05, 1.09]:
        true_lam, _ = C.lam_min_sector(L, "even")
        for R2 in [20.0, 30.0, 40.0, 60.0]:
            le, s0 = cert_bottom(L, R2, "even")
            lo, _ = cert_bottom(L, R2, "odd")
            print(f"  {L:6.2f} {R2:5.0f} {s0:8.4f} {le:+14.6e} {lo:+14.6e} {true_lam:+14.3e}")
    print("== K-CONVERGENCE of the certificate bottom (L = 0.90, R2 = 40) ==")
    for K in [60, 80, 100, 120]:
        le, _ = cert_bottom(0.90, 40.0, "even", K=K)
        lo, _ = cert_bottom(0.90, 40.0, "odd", K=K)
        print(f"  K = {K:3d}: even {le:+.6e}   odd {lo:+.6e}")

def main():
    segs = negative_set()
    identity_crosscheck()
    minimizer_budget(0.90)
    minimizer_budget(1.00, R2list=(30.0, 40.0, 60.0))
    certificate_runs()

if __name__ == "__main__":
    main()
