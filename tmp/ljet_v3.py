"""L-jet v3: rank-10 scale (B ~ 3e10). No stored a_p table, no big array.

Split n = smooth (all factors <= sqrt(B)) + p*m (unique p > sqrt(B), m < sqrt(B)):
  smooth: segment-local factorization sieve (v2), c = 0 where rem > 1;
  big:    prime-window workers sieve [w0, w1), ellap each p, and immediately
          accumulate sum_m a_m W_j(p*m) -- a_p is consumed at birth, never stored.
Weights: the 12 combined W_j(u) = e^{-u} sum_{i+k=j} [(-1)^i + eps(-1)^k]
  (u^i/i!) g_k(e^u) pre-tabulated on a dense grid, evaluated by np.interp
  (linear, h^2 error ~ 5e-12 relative).  Lambda-jet coefficient j = sum_n a_n W_j.
Gate: r8 through BOTH v3 paths must reproduce c_8 = 7528.88509253 (v1/v2/PARI).
Usage: sage -python ljet_v3.py {r8|r9|r10}
"""
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ljet_v2 import build_gk_splines, primes_upto, apow_table, JMAX, CACHE
from scipy.interpolate import splev

CURVES = {
    "r8": dict(ainvs=[1, -1, 0, -106384, 13075804], N=249649566346838,
               eps=1, XCUT=58.0),
    "r9": dict(ainvs=[1, -1, 0, -135004, 97151644], N=32107342006814614,
               eps=-1, XCUT=58.0),
    "r10": dict(ainvs=[0, 0, 1, -16312387, 25970162646], N=10189285026863130793,
                eps=1, XCUT=55.0),
}
WGRID_N = 1 << 24
WU_HI = math.log(60.0)
SMOOTH_SEG = 1 << 26
PWIN = 140_000_000
NPROC = 7

_G = {}


def build_wtables(eps):
    splines = build_gk_splines()
    from ljet_v2 import ULO
    u = np.linspace(ULO, WU_HI, WGRID_N)
    gk = [splev(u, splines[k]) for k in range(JMAX)]
    inv_fact = [1.0 / math.factorial(i) for i in range(JMAX)]
    lp = [np.ones_like(u)]
    for i in range(1, JMAX):
        lp.append(lp[-1] * u)
    W = []
    emu = np.exp(-u)                # fold the 1/x prefactor into the table
    for j in range(JMAX):
        acc = np.zeros_like(u)
        for i in range(j + 1):
            k = j - i
            coef = ((-1) ** i + eps * (-1) ** k)
            if coef:
                acc += coef * inv_fact[i] * lp[i] * gk[k]
        W.append(emu * acc)
    return u[0], u[-1], W


def small_an(ainvs, N, Bs):
    """a_m for m <= Bs by the v1 in-RAM ascending fill."""
    ps = primes_upto(Bs)
    from cypari2 import Pari
    pari = Pari()
    E = pari.ellinit(ainvs)
    a = np.zeros(Bs + 1, dtype=np.int64)
    a[1] = 1
    for p in ps:
        p = int(p)
        apv = int(pari.ellap(E, p))
        tab = apow_table(p, apv, N, Bs)
        q = p
        for aq in tab:
            a[q::q] = aq * a[1: Bs // q + 1]
            q *= p
    return a


def wsum(u_vals, x_vals, coeff):
    """Accumulate coeff * W_j(u) (tables carry the 1/x prefactor)."""
    grid, W = _G["grid"], _G["W"]
    out = []
    for j in range(JMAX):
        out.append(float(np.sum(coeff * np.interp(u_vals, grid, W[j]))))
    return out


def _smooth_worker(args):
    (s, e) = args
    ainvs, N, A, B = _G["ainvs"], _G["N"], _G["A"], _G["B"]
    small_p = _G["small_p"]
    apows = _G["apows"]
    L = e - s
    c = np.ones(L, dtype=np.float64)
    rem = np.arange(s, e, dtype=np.int64)
    for p, tab in zip(small_p, apows):
        p = int(p)
        first = ((s + p - 1) // p) * p - s
        if first >= L:
            continue
        idx = np.arange(first, L, p)
        r = rem[idx] // p
        v = np.ones(len(idx), dtype=np.int64)
        mask = r % p == 0
        while mask.any():
            w = np.nonzero(mask)[0]
            r[w] //= p
            v[w] += 1
            mask = np.zeros(len(idx), dtype=bool)
            mask[w] = r[w] % p == 0
        rem[idx] = r
        c[idx] *= tab[v - 1]
    good = rem == 1
    n = np.arange(s, e, dtype=np.float64)[good]
    if len(n) == 0:
        return [0.0] * JMAX
    x = n / A
    return wsum(np.log(x), x, c[good])


def _bigp_worker(args):
    (w0, w1) = args
    ainvs, A, B = _G["ainvs"], _G["A"], _G["B"]
    am, logm = _G["am"], _G["logm"]
    from cypari2 import Pari
    pari = Pari()
    pari.allocatemem(500_000_000)
    E = pari.ellinit(ainvs)
    base = primes_upto(int(w1 ** 0.5) + 1)
    seg = np.ones(w1 - w0, dtype=bool)
    for p in base:
        st = max(p * p, ((w0 + p - 1) // p) * p)
        if st < w1:
            seg[st - w0::p] = False
    ps = np.nonzero(seg)[0] + w0
    ap = np.empty(len(ps), dtype=np.float64)
    ellap = pari.ellap
    for i, p in enumerate(ps):
        ap[i] = float(ellap(E, int(p)))
    logp = np.log(ps.astype(np.float64))
    out = [0.0] * JMAX
    Mmax = len(am) - 1
    m = 1
    while m <= Mmax:
        pmax = B / m
        cnt = int(np.searchsorted(ps, pmax, side="right"))
        if cnt == 0:
            break
        u = (logp[:cnt] + logm[m]) - _G["logA"]
        xv = ps[:cnt].astype(np.float64) * (m / A)
        contrib = wsum(u, xv, ap[:cnt] * float(am[m]))
        for j in range(JMAX):
            out[j] += contrib[j]
        m += 1
    return out


def _init(g):
    _G.update(g)
    _G["grid"] = np.linspace(g["u0"], g["u1"], WGRID_N)


def run(tag):
    cfg = CURVES[tag]
    N, eps = cfg["N"], cfg["eps"]
    A = math.sqrt(N) / (2 * math.pi)
    B = int(cfg["XCUT"] * A)
    Bs = int(B ** 0.5) + 1
    print(f"== v3 {tag}: N={N} eps={eps} B={B} sqrtB={Bs}", flush=True)
    t0 = time.time()
    u0, u1, W = build_wtables(eps)
    am = small_an(cfg["ainvs"], N, Bs)
    small_p = primes_upto(Bs)
    from cypari2 import Pari
    pari = Pari()
    E = pari.ellinit(cfg["ainvs"])
    apows = [np.array(apow_table(int(p), int(pari.ellap(E, int(p))), N, B),
                      dtype=np.float64) for p in small_p]
    logm = np.log(np.arange(len(am), dtype=np.float64).clip(1))
    g = dict(ainvs=cfg["ainvs"], N=N, A=A, B=B, logA=math.log(A), u0=u0, u1=u1,
             W=W, small_p=small_p, apows=apows, am=am.astype(np.float64),
             logm=logm)
    print(f"setup {time.time()-t0:.0f}s (small primes: {len(small_p)})", flush=True)

    jobs_s = [(s, min(s + SMOOTH_SEG, B + 1)) for s in range(1, B + 1, SMOOTH_SEG)]
    jobs_b = [(w, min(w + PWIN, B + 1)) for w in range(Bs + 1, B + 1, PWIN)]
    print(f"jobs: {len(jobs_s)} smooth + {len(jobs_b)} prime-window", flush=True)
    import multiprocessing as mp_
    lam = [0.0] * JMAX
    with mp_.get_context("fork").Pool(NPROC, initializer=_init,
                                      initargs=(g,)) as pool:
        done = 0
        for res in pool.imap_unordered(_smooth_worker, jobs_s, chunksize=1):
            for j in range(JMAX):
                lam[j] += res[j]
            done += 1
            if done % 25 == 0:
                print(f"  smooth {done}/{len(jobs_s)} {time.time()-t0:.0f}s",
                      flush=True)
        done = 0
        for res in pool.imap_unordered(_bigp_worker, jobs_b, chunksize=1):
            for j in range(JMAX):
                lam[j] += res[j]
            done += 1
            if done % 10 == 0:
                print(f"  bigp {done}/{len(jobs_b)} {time.time()-t0:.0f}s",
                      flush=True)
    import mpmath as mp
    mp.mp.dps = 40
    invgam = [float(cc) for cc in mp.taylor(lambda w: 1 / mp.gamma(1 + w), 0, JMAX)]
    lnA = math.log(A)
    Fs = [(-lnA) ** i / math.factorial(i) / A for i in range(JMAX)]
    F = [math.fsum(Fs[i] * invgam[j - i] for i in range(j + 1))
         for j in range(JMAX)]
    Ljet = [math.fsum(lam[i] * F[j - i] for i in range(j + 1))
            for j in range(JMAX)]
    print(f"total {time.time()-t0:.0f}s", flush=True)
    for j, cc in enumerate(Ljet):
        print(f"c_{j} = {cc:.12g}", flush=True)


if __name__ == "__main__":
    run(sys.argv[1])
