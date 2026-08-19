#!/usr/bin/env python3
"""
att247 — Suzuki §7.7 identity attacked DIRECTLY: both sides computed.

Retraction upstream: the identity is a concrete statement about explicit
functions; we compute it.  Objects from 2301.00421 (transcribed (1.5),(1.6),(4.3)):

  P_t(z) = 4(e^{t/2}-1)/(1+2iz) + 4(e^{-t/2}-1)/(1-2iz)
           + (e^{-izt}-1)/(iz) * zeta'/zeta(1/2-iz)
           + sum_{n<=e^t} Lambda(n)/sqrt(n) * (e^{-iz(t-log n)}-1)/(iz)
           - 1/(2iz) [psi(1/4-iz/2) - psi(1/4)]
           - e^{-t/2}/(2iz) [Phi(e^{-2t},1,1/4-iz/2) - Phi(e^{-2t},1,1/4)]
  S_t(z) = i (1+Theta(z))/2 * P_t(z),  Theta = conj(E(z))/E(z) on R,
  E(z) = xi(1/2-iz) + xi'(1/2-iz)
  g(t)  = -4(e^{t/2}+e^{-t/2}-2) + sum_{n<=e^t} Lambda(n)/sqrt(n) (t - log n)
          - (t/2)[psi(1/4) - log pi] - (1/4)[Phi(1,2,1/4) - e^{-t/2} Phi(e^{-2t},2,1/4)]
  G(x,y) = g(x-y) - g(x) - g(-y) + g(0),  g even (theory symmetrized), g(0)=0.

TESTS:
  (A) FACTORIZATION/ENTIRETY: S_t smooth across gamma_1 (pole of zeta'/zeta
      killed by the (1+Theta)/2 zero); A*P_t finite at gamma_1; the trivial-pole
      cancellation inside P_t at z = -i*5/2-ish is not on R — check instead
      that P_t has no spurious blowup along R and S_t decays ~ log|z|/|z|.
  (B) THE IDENTITY: (1/pi) int_{-Z}^{Z} S_x(z) conj(S_y(z)) dz + tail  vs  G(x,y)
      at (x,y) = (1.0, 0.7), (1.5, 1.5), (0.6, 1.2).   Z = 1000, GL panels.
"""
import mpmath as mp
import math, time

mp.mp.dps = 20

LAM = []  # (n, Lambda(n)) up to 40
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

def xi(s):
    return 0.5 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def zplog(s):
    return mp.zeta(s, derivative=1) / mp.zeta(s)

def Efun(z):
    s = mp.mpf(0.5) - 1j * z
    x = xi(s)
    L = (1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2 + zplog(s))
    return x * (1 + L)

def P_t(t, z):
    t = mp.mpf(t)
    iz = 1j * z
    out = 4 * (mp.e ** (t / 2) - 1) / (1 + 2j * z) + 4 * (mp.e ** (-t / 2) - 1) / (1 - 2j * z)
    out += (mp.e ** (-iz * t) - 1) / iz * zplog(mp.mpf(0.5) - 1j * z)
    for n, lam in LAM:
        ln = mp.log(n)
        if ln <= t:
            out += lam / mp.sqrt(n) * (mp.e ** (-iz * (t - ln)) - 1) / iz
    out -= (mp.digamma(mp.mpf(1) / 4 - 1j * z / 2) - PSI14) / (2j * z)
    q = mp.e ** (-2 * t)
    out -= mp.e ** (-t / 2) / (2j * z) * (mp.lerchphi(q, 1, mp.mpf(1) / 4 - 1j * z / 2)
                                          - mp.lerchphi(q, 1, mp.mpf(1) / 4))
    return out

def S_t(t, z, Ev=None):
    if Ev is None:
        Ev = Efun(z)
    theta = mp.conj(Ev) / Ev
    return 1j * (1 + theta) / 2 * P_t(t, z)

def g_screw(t):
    t = mp.mpf(abs(t))                      # even symmetrization
    out = -4 * (mp.e ** (t / 2) + mp.e ** (-t / 2) - 2)
    for n, lam in LAM:
        ln = mp.log(n)
        if ln <= t:
            out += lam / mp.sqrt(n) * (t - ln)
    out -= (t / 2) * (PSI14 - mp.log(mp.pi))
    out -= mp.mpf(1) / 4 * (mp.lerchphi(1, 2, mp.mpf(1) / 4)
                            - mp.e ** (-t / 2) * mp.lerchphi(mp.e ** (-2 * t), 2, mp.mpf(1) / 4))
    return out

def testA():
    print("== (A) FACTORIZATION / SMOOTHNESS CHECKS ==", flush=True)
    g1 = mp.im(mp.zetazero(1))
    for dz in [0.1, 0.01, 0.001]:
        z = g1 + dz
        Sv = S_t(1.0, z)
        print(f"  S_1(gamma_1 + {dz:7.3f}) = {mp.nstr(Sv, 8)}")
    z = g1 + mp.mpf(1e-6)
    Sv = S_t(1.0, z)
    print(f"  S_1(gamma_1 + 1e-6)   = {mp.nstr(Sv, 8)}   (finite -> pole killed)")
    for z in [50, 200, 800]:
        Sv = S_t(1.0, mp.mpf(z))
        print(f"  |S_1({z})| = {mp.nstr(abs(Sv), 6)}   vs log(z)/(2z) = {mp.nstr(mp.log(z)/(2*z), 6)}")

def identity_test(x, y, Z=1000, panel=2.0, nodes=16):
    t0 = time.time()
    acc = mp.mpf(0)
    zc = mp.mpf(0)
    npan = int(Z / panel)
    xs, ws = _gl_cache(nodes)
    for k in range(npan):
        a, b = k * panel, (k + 1) * panel
        for xn, wn in zip(xs, ws):
            z = mp.mpf(a + (b - a) / 2 * (xn + 1))
            if abs(z) < 1e-9:
                z = mp.mpf(1e-6)
            Ev = Efun(z)
            Sx = S_t(x, z, Ev)
            Sy = S_t(y, z, Ev)
            # integrand at +z and -z:  S_t(-z) = conj(S_t(z))? use direct evaluation
            Evm = Efun(-z)
            Sxm = S_t(x, -z, Evm)
            Sym = S_t(y, -z, Evm)
            acc += wn * (b - a) / 2 * (Sx * mp.conj(Sy) + Sxm * mp.conj(Sym))
            zc += 2
    val = acc / mp.pi
    G = g_screw(x - y) - g_screw(x) - g_screw(y) + g_screw(0)
    print(f"  (x,y)=({x},{y}): (1/pi)int_[-{Z},{Z}] = {mp.nstr(val, 8)}   "
          f"G = {mp.nstr(G, 8)}   diff = {mp.nstr(val - G, 4)}   "
          f"({zc} evals, {time.time()-t0:.0f}s)", flush=True)
    return val, G

_GLC = {}
def _gl_cache(n):
    if n not in _GLC:
        import numpy as np
        a, w = np.polynomial.legendre.leggauss(n)
        _GLC[n] = ([mp.mpf(float(v)) for v in a], [mp.mpf(float(v)) for v in w])
    return _GLC[n]

def main():
    testA()
    print("== (B) THE IDENTITY, BOTH SIDES ==", flush=True)
    identity_test(1.0, 0.7, Z=1000)
    identity_test(1.5, 1.5, Z=1000)
    identity_test(0.6, 1.2, Z=1000)

if __name__ == "__main__":
    main()
