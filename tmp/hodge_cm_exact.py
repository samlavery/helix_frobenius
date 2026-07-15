"""
Exact-integer CM bank for psi^m / 49a -> kills the float64 precision wall (which was in the
bank, not the AFE kernel).  a_n built as EXACT Python ints (point-count 49a1 for a_p, then the
CM Hecke recurrence with correct nebentypus), lam_n = a_n / n^{m/2} formed only at the end
(Python int/int -> correctly-rounded float).  Then the (working) numpy AFE kernel certifies the
sign at high weight.  Controls: m=15,16,17 (known reliable).  TEST: m=18,19,20 -- does the sign
match the clean period-4 law (eps_18=+1, eps_19=-1, eps_20=-1) or DEVIATE (new exception)?
"""
import importlib.util, sys, math
import numpy as np
from mpmath import mp
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec); sys.modules["cl"] = cl
try:
    spec.loader.exec_module(cl)
except SystemExit:
    pass
mp.dps = 30

def sieve(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0].tolist()

def legp(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1) // 2, p) == 1 else -1)

def ap_49a(p):
    """a_p of elliptic curve 49a1: y^2+xy = x^3-x^2-2x-1.  a_p = -sum_x (Disc(x)/p).
    The discriminant method is invalid in char 2; p=2 counted directly (#E(F_2)=2 => a_2=1)."""
    if p == 7: return 0
    if p == 2: return 1
    s = 0
    for x in range(p):
        disc = (4 * x**3 - 3 * x**2 - 8 * x - 4) % p   # x^2+4f(x), f=x^3-x^2-2x-1
        s += legp(disc, p)
    return -s

def exact_bank(m, nmax, primes, ap1):
    """Exact integer a_n for the weight (m+1) CM form; returns float lam_n = a_n/n^{m/2}."""
    a = [0] * (nmax + 1); a[1] = 1
    for p in primes:
        kmax = int(math.log(nmax) / math.log(p))
        c = [0] * (kmax + 1); c[0] = 1
        if p == 7:
            pass                                   # a_{7^j}=0, j>=1
        else:
            lp = 1 if legp(p, 7) == 1 else -1      # split (QR mod7) -> +1, inert -> -1
            # a_p of the weight-(m+1) form = t_m = pi^m + pibar^m (split), 0 (inert)
            if lp == 1:                            # split: t_k = ap1*t_{k-1} - p*t_{k-2}
                tprev, tcur = 2, ap1[p]
                if m == 0: apm = 2
                elif m == 1: apm = ap1[p]
                else:
                    for _ in range(2, m + 1):
                        tprev, tcur = tcur, ap1[p] * tcur - p * tprev
                    apm = tcur
            else:
                apm = 0
            c[1] = apm
            for j in range(2, kmax + 1):
                c[j] = apm * c[j - 1] - (p ** m) * c[j - 2]   # a_{p^2}=-p^m (inert & split)
        for k in range(kmax, 0, -1):
            pk = p ** k
            for mm in range(1, nmax // pk + 1):
                if mm % p:
                    a[mm * pk] += c[k] * a[mm]
    lam = np.zeros(nmax + 1)
    for n in range(1, nmax + 1):
        lam[n] = a[n] / (n ** (m / 2.0))           # exact int / int -> rounded float
    return lam

def both_res(G, lam, s0, T=80):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T, NODES=24001, M=4000)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T, NODES=24001, M=4000)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    return abs((a + b) - d) / max(abs(d), 1e-30), abs((a - b) - d) / max(abs(d), 1e-30)

NMAX = 6000
primes = sieve(NMAX)
print("point-counting 49a1 a_p ...")
ap1 = {p: ap_49a(p) for p in primes}
print("  a_2=%d a_11=%d a_23=%d (49a1 split-prime traces)" % (ap1[2], ap1[11], ap1[23]))

CLEAN = {15:-1, 16:-1, 17:+1, 18:+1, 19:-1, 20:-1}   # clean period-4 prediction
print("\n m  wt  res[+1]   res[-1]  decisive  measured  clean  verdict")
for m in [15, 16, 17, 18, 19, 20]:
    lam = exact_bank(m, NMAX, primes, ap1)
    G = cl.make_G(49, [('C', m / 2.0)])
    rp, rm = both_res(G, lam, 2.5)
    meas = +1 if rp < rm else -1
    dec = min(rp, rm) / max(rp, rm)
    tag = "ok" if meas == CLEAN[m] else "DEVIATES"
    rel = "reliable" if dec < 0.05 else ("WEAK" if dec < 0.3 else "UNRESOLVED")
    print(" %2d  %2d  %.2e  %.2e  %.4f    %+d       %+d    %s/%s"
          % (m, m + 1, rp, rm, dec, meas, CLEAN[m], tag, rel))
