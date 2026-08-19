#!/usr/bin/env python3
"""
att247b — Suzuki §7.7 identity, both sides, FAST single-sweep version.
Same objects as att247 (transcription-validated by the pole-kill check there);
Lerch terms by manual geometric series; per-z specials shared across all t.
"""
import mpmath as mp
import math, time
import numpy as np

mp.mp.dps = 20

LAM = []
for n in range(2, 41):
    m, p = n, None
    for q in range(2, int(math.sqrt(n)) + 1):
        if m % q == 0:
            p = q
            while m % q == 0:
                m //= q
            break
    if p is None:
        LAM.append((n, mp.log(n)))
    elif m == 1:
        LAM.append((n, mp.log(p)))

PSI14 = mp.digamma(mp.mpf(1) / 4)
LOGPI = mp.log(mp.pi)

def lerch1(q, a, terms=60):
    """Phi(q,1,a) = sum_k q^k/(k+a), |q|<1."""
    s = mp.mpc(0)
    qk = mp.mpf(1)
    for k in range(terms):
        s += qk / (k + a)
        qk *= q
    return s

def lerch2(q, a, terms=60):
    s = mp.mpc(0)
    qk = mp.mpf(1)
    for k in range(terms):
        s += qk / (k + a) ** 2
        qk *= q
    return s

def g_screw(t):
    t = mp.mpf(abs(t))
    out = -4 * (mp.e ** (t / 2) + mp.e ** (-t / 2) - 2)
    for n, lam in LAM:
        ln = mp.log(n)
        if ln <= t:
            out += lam / mp.sqrt(n) * (t - ln)
    out -= (t / 2) * (PSI14 - LOGPI)
    out -= mp.mpf(1) / 4 * (lerch2(mp.mpf(1) - mp.mpf(1e-30), mp.mpf(1) / 4, 4000)
                            - mp.e ** (-t / 2) * lerch2(mp.e ** (-2 * t), mp.mpf(1) / 4))
    return out

# Phi(1,2,1/4) = psi'(1/4) exactly — use polygamma instead of the slow series
PHI121_4 = mp.polygamma(1, mp.mpf(1) / 4)

def g_screw_exact(t):
    t = mp.mpf(abs(t))
    out = -4 * (mp.e ** (t / 2) + mp.e ** (-t / 2) - 2)
    for n, lam in LAM:
        ln = mp.log(n)
        if ln <= t:
            out += lam / mp.sqrt(n) * (t - ln)
    out -= (t / 2) * (PSI14 - LOGPI)
    out -= mp.mpf(1) / 4 * (PHI121_4 - mp.e ** (-t / 2) * lerch2(mp.e ** (-2 * t), mp.mpf(1) / 4))
    return out

def specials(z):
    """shared per-z: zeta'/zeta(1/2-iz), psi(1/4-iz/2), E(z), theta(z)."""
    s = mp.mpf(0.5) - 1j * z
    zl = mp.zeta(s, derivative=1) / mp.zeta(s)
    psih = mp.digamma(s / 2)                     # = psi(1/4 - iz/2)
    L = 1 / s + 1 / (s - 1) - LOGPI / 2 + psih / 2 + zl
    x = 0.5 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)
    E = x * (1 + L)
    theta = mp.conj(E) / E
    return zl, psih, theta

def S_all(ts, z):
    """S_t(z) for all t in ts, sharing specials."""
    zl, psih, theta = specials(z)
    iz = 1j * z
    pref = 1j * (1 + theta) / 2
    out = {}
    for t in ts:
        tm = mp.mpf(t)
        P = 4 * (mp.e ** (tm / 2) - 1) / (1 + 2j * z) + 4 * (mp.e ** (-tm / 2) - 1) / (1 - 2j * z)
        P += (mp.e ** (-iz * tm) - 1) / iz * zl
        for n, lam in LAM:
            ln = mp.log(n)
            if ln <= tm:
                P += lam / mp.sqrt(n) * (mp.e ** (-iz * (tm - ln)) - 1) / iz
        P -= (psih - PSI14) / (2j * z)
        q = mp.e ** (-2 * tm)
        a = mp.mpf(1) / 4 - 1j * z / 2
        P -= mp.e ** (-tm / 2) / (2j * z) * (lerch1(q, a) - lerch1(q, mp.mpf(1) / 4))
        out[t] = pref * P
    return out

def main():
    pairs = [(1.0, 0.7), (1.5, 1.5), (0.6, 1.2)]
    ts = sorted(set([p[0] for p in pairs] + [p[1] for p in pairs]))
    Z, panel, nodes = 800.0, 2.0, 12
    xs, ws = np.polynomial.legendre.leggauss(nodes)
    acc = {p: mp.mpc(0) for p in pairs}
    t0 = time.time()
    npan = int(Z / panel)
    for k in range(npan):
        a, b = k * panel, (k + 1) * panel
        for xn, wn in zip(xs, ws):
            z = mp.mpf(a + (b - a) / 2 * (xn + 1))
            if abs(z) < 1e-9:
                continue
            Sp = S_all(ts, z)
            Sm = S_all(ts, -z)
            w = mp.mpf(wn * (b - a) / 2)
            for (x, y) in pairs:
                acc[(x, y)] += w * (Sp[x] * mp.conj(Sp[y]) + Sm[x] * mp.conj(Sm[y]))
        if k % 50 == 49:
            print(f"  ...panel {k+1}/{npan} ({time.time()-t0:.0f}s)", flush=True)
    print(f"== IDENTITY, BOTH SIDES (Z = {Z}, tail not yet corrected) ==")
    for (x, y) in pairs:
        val = acc[(x, y)] / mp.pi
        G = g_screw_exact(x - y) - g_screw_exact(x) - g_screw_exact(y) + g_screw_exact(0)
        rel = abs(val - G) / abs(G) if abs(G) > 0 else mp.mpf(0)
        print(f"  (x,y)=({x},{y}):  (1/pi)∫ = {mp.nstr(val, 8)}   G = {mp.nstr(G, 8)}"
              f"   diff = {mp.nstr(val - G, 4)}   rel = {mp.nstr(rel, 3)}", flush=True)

if __name__ == "__main__":
    main()
