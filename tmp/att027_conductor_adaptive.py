"""ATTEMPT 027 -- conductor dependence, re-run in the ADAPTIVE variable (repairs 021).

WHY IT IS NOW ANSWERABLE.  Attempt 021 died at R = 27-121: the unfolded tape smeared every
line because the window t in [10,400] has ratio 40.  Attempt 026 removed R entirely by working
in the Landau variable.  There is no unfolding here, so no ratio budget, and the same zeros
that were unusable become usable.

AND IT GETS SHARPER.  Landau for Dirichlet L: for n > 1 a prime power,
        sum_{0 < gamma_chi <= T} n^{i gamma_chi} = -(T/2pi) Lambda(n) chi(n)/sqrt(n) + O(...)
For a REAL primitive chi this is a SIGNED prediction: chi(n) = +-1, so relative to zeta
(where every line is negative) exactly the lines with chi(n) = -1 FLIP SIGN, and the lines with
gcd(n,q) > 1 vanish.  A sign test is unambiguous in a way a modulus test is not -- 021's
amplitude-only design could not have seen this even had it worked.

PAIRING.  house: the adaptive-scale (Landau-variable) tape of attempt 026, calibrated on zeta
to median obs/pred 1.0003 with phase +-1.000 pi, and carrying the instrument decision that
wide windows are an asset x classical: Landau's theorem for Dirichlet L-functions and the
conductor's two independent roles (support via chi(n) = 0, sign via chi(n) = +-1).
MECHANISM: 021's failure was entirely the unfolding; removing it converts a smeared amplitude
comparison into a per-line signed identity, and the conductor's two effects become ONE
measurement.

SPECIMENS.  chi_-3 (q=3, odd) kills 3,9,27.  chi_5 (q=5, even) kills 5,25.  chi_8 (q=8, even)
kills the ENTIRE 2-tower 2,4,8,16,32 -- which for zeta carries the largest lines, so it is the
sharpest control available.  zeta itself (q=1) is the baseline.

STATED NULL, pre-registered.  The measured a(n) does not follow -Lambda(n)chi(n)/sqrt(n):
either the signs fail to track chi(n), or the gcd(n,q) > 1 lines are present, or the surviving
amplitudes miss.  Then 021's negative was real rather than an artifact of the coordinate.
"""
import numpy as np, mpmath as mp, sys, math, os
from math import pi, log, sqrt

def P(*a): print(*a); sys.stdout.flush()
mp.mp.dps = 15

def leg(n, p):
    n %= p
    return 0 if n == 0 else (1 if pow(n, (p-1)//2, p) == 1 else -1)
def chi8(n):
    n %= 8
    return 1 if n in (1, 7) else (-1 if n in (3, 5) else 0)
SPECS = [('L(chi_-3)', 3, 1, lambda n: leg(n, 3)),
         ('L(chi_5)',  5, 0, lambda n: leg(n, 5)),
         ('L(chi_8)',  8, 0, chi8)]

def theta_chi(t, q, a):
    t = mp.mpf(t)
    return (t/2)*mp.log(mp.mpf(q)/mp.pi) + mp.im(mp.loggamma((mp.mpf(0.5)+a+1j*t)/2))
def Zchi(t, q, a, chi):
    s = mp.mpf(0.5) + 1j*mp.mpf(t)
    L = mp.mpf(q)**(-s)*sum(chi(r)*mp.zeta(s, mp.mpf(r)/q) for r in range(1, q+1) if chi(r))
    return float(mp.re(mp.e**(1j*theta_chi(t, q, a))*L))

T0, T1, STEP = 10.0, 600.0, 0.15
def find_zeros(q, a, chi):
    ts = np.arange(T0, T1, STEP)
    v = np.array([Zchi(t, q, a, chi) for t in ts])
    idx = np.nonzero(np.signbit(v[:-1]) != np.signbit(v[1:]))[0]
    lo, hi, flo = ts[idx].copy(), ts[idx+1].copy(), v[idx].copy()
    for _ in range(14):
        mid = (lo+hi)/2
        fm = np.array([Zchi(t, q, a, chi) for t in mid])
        left = np.signbit(flo) != np.signbit(fm)
        hi = np.where(left, mid, hi); lo = np.where(left, lo, mid)
        flo = np.where(left, flo, fm)
    return (lo+hi)/2

def vonm(n):
    m = n
    for p in (2,3,5,7,11,13,17,19,23,29,31):
        if m % p == 0:
            while m % p == 0: m //= p
            return log(p) if m == 1 else 0.0
    return 0.0

NS = [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,32]

# ---- zeta baseline on a matched window, from the cached long set ----
gz = np.load('att019_zeros_to20k.npy'); gz = gz[(gz >= T0) & (gz <= T1)]
P(f"baseline zeta: {len(gz)} zeros on [{T0:.0f},{T1:.0f}]\n")

def report(name, g, q, chi):
    W = g[-1] - g[0]
    P(f"{name}  q={q}  zeros {len(g)}  W={W:.1f}")
    P(f"  {'n':>4}{'chi(n)':>8}{'pred':>10}{'measured':>11}{'|Im|':>8}{'obs/pred':>10}{'sign ok':>9}")
    ok = bad = 0; rats = []
    for n in NS:
        a = complex(np.exp(1j*g*log(n)).sum()/(W/(2*pi)))
        c = chi(n) if q > 1 else 1
        pred = -vonm(n)*c/sqrt(n)
        if abs(pred) < 1e-12:
            P(f"  {n:>4}{c:>8}{0.0:>10.5f}{a.real:>11.5f}{abs(a.imag):>8.5f}"
              f"{'--':>10}{('KILLED ok' if abs(a) < 0.06 else 'PRESENT!'):>9}")
            continue
        r = a.real/pred; rats.append(r)
        s = (np.sign(a.real) == np.sign(pred))
        ok += s; bad += (not s)
        P(f"  {n:>4}{c:>8}{pred:>10.5f}{a.real:>11.5f}{abs(a.imag):>8.5f}{r:>10.3f}"
          f"{('yes' if s else 'NO'):>9}")
    rr = np.array(rats)
    P(f"  -> signs correct {ok}/{ok+bad};  median obs/pred {np.median(rr):.4f}"
      f"  IQR {np.percentile(rr,25):.4f}-{np.percentile(rr,75):.4f}\n")
    return ok, bad

report('zeta        ', gz, 1, lambda n: 1)
for name, q, a, chi in SPECS:
    cf = f'att027_zeros_q{q}.npy'
    if os.path.exists(cf):
        g = np.load(cf)
    else:
        g = find_zeros(q, a, chi); np.save(cf, g)
    exp_n = float(theta_chi(T1, q, a) - theta_chi(T0, q, a))/pi
    P(f"[census {name}: {len(g)} zeros vs theta-count {exp_n:.2f}, S-jump {exp_n-len(g):+.2f}]")
    report(name, g, q, chi)
