"""att534 -- ADJUDICATION of the r>0 closed form for S_x(r), and audit of E/E*/Khat.

Three candidate closed forms are in play for
    S_x(r) = int_r^inf (u-r) W_x(u) du,
    W_x(u) = 2 int_R Phi(u+w) Phi(u-w) cos(2xw) dw,   Phi = P0(|.|)  (att531 convention)

  (A0)  S = (1/8pi) int_0^inf [Xi(x)^2 - Xi(x+t)Xi(x-t) cos(2rt)] t^{-2} dt
        -- "cos inside", NO linear term.
  (A1)  (A0) - (r/8) Xi(x)^2
        -- "cos inside" PLUS the linear term coming from
           (|v|-c)_+ = |v| - c + (c-|v|)_+ .
  (B)   S = (1/8pi) int_0^inf [Xi(x)^2 - Xi(x+t)Xi(x-t)] cos(2rt) t^{-2} dt
        -- "cos outside".  Algebraically identical to (A1) because
           int_0^inf (1 - cos(2 r t)) t^{-2} dt = pi r
        makes the two linear terms cancel exactly.

TWO INDEPENDENT REFEREES, neither of which uses the disputed transform:

  R1  direct double quadrature of the DEFINING integral in the Phi plane.
      float64; the cancellation at x=2 is ~3 decades so ~12 digits survive.
      Trapezoid in w (Phi decays superexponentially => Euler-Maclaurin boundary
      corrections all vanish => spectral accuracy); Gauss-Legendre panels in u.
      Uses NO Fourier theory whatsoever.

  R2  Wigner-Fourier referee.  Uses ONLY the elementary transform pair
          What_x(eta) = G(eta/2+x) G(eta/2-x),  G = Xi/2,
      (itself cross-checked against R1 below), then
          W_x(u) = (2/pi) int_0^inf G(t+x)G(t-x) cos(2tu) dt
      and integrates (u-r) W_x(u) du numerically.  It never touches the
      (|v|-c)_+ transform, the finite part, or any distributional step -- i.e. it
      is independent of exactly the step under dispute.

PRE-REGISTERED DECISION RULE (fixed before any number is read):
  * the candidate agreeing with BOTH referees at r=0.25 and r=0.5 to better than
    1e-6 relative is the correct form;
  * if (A1) and (B) agree with each other and with the referees, they are one
    identity and (A0) is the version missing the linear term;
  * if the referees match (A0), my derivation is wrong and (B) is retracted.
PREDICTION (recorded before running): referees == (A1) == (B); (A0) overshoots by
exactly (r/8)Xi(x)^2, which at x=2, r=0.25 is 0.03125*Xi(2)^2 ~ 6.4e-3, i.e. ~39x.

Also audits, numerically, the identifications the Lean bridge rests on:
  E(z)  = xi(1/2 - i z) + xi'(1/2 - i z)   [def xiStructure]
  E*(z) = xi(1/2 - i z) - xi'(1/2 - i z)   [thm xiStructure_Estar]
  claim  xi(1/2 - iz) = Xi(z),  xi'(1/2 - iz) = i Xi'(z)   => E = Xi + i Xi'
  claim  HB defect Re[A conj P] = Khat := -Im[Xi' conj Xi] = Im[-Xi'/Xi]*|Xi|^2
  claim  Khat = 8 int_0^inf u sinh(2yu) W_x(u) du            [att530 normalisation]

usage:  python3 att534_stp_form_adjudication.py [adjudicate|audit|wcheck]
"""
import math
import sys

import numpy as np
import mpmath as mp


# ------------------------------------------------------------------ the kernel
def P0f(u):
    """float64 P0: att530/att531's Ph. 1/4 of Lean riemannXiKernel, 1/2 of Riemann Phi."""
    t = 0.0
    e2 = math.exp(2.0 * u)
    e45 = math.exp(4.5 * u)
    e25 = math.exp(2.5 * u)
    for n in range(1, 40):
        a = math.pi * n * n * e2
        if a > 700.0:
            break
        t += (2.0 * math.pi ** 2 * n ** 4 * e45 - 3.0 * math.pi * n * n * e25) * math.exp(-a)
    return t


def Phf(u):
    return P0f(abs(u))


def Phv(arr):
    """vectorised Phi on a numpy array."""
    a = np.abs(arr)
    e2 = np.exp(2.0 * a)
    out = np.zeros_like(a)
    for n in range(1, 40):
        q = math.pi * n * n * e2
        m = q < 700.0
        if not m.any():
            break
        out[m] += ((2.0 * math.pi ** 2 * n ** 4 * np.exp(4.5 * a[m])
                    - 3.0 * math.pi * n * n * np.exp(2.5 * a[m])) * np.exp(-q[m]))
    return out


def xi(s):
    """Pole-free spelling: (1/2) s Gamma(s/2) = Gamma(1 + s/2).  Regular at s = 0."""
    return mp.pi ** (-s / 2) * mp.gamma(1 + s / 2) * (s - 1) * mp.zeta(s)


def Xi(z):
    return xi(mp.mpf(1) / 2 + 1j * z)


def XiR(v):
    return mp.re(Xi(mp.mpf(v)))


# ------------------------------------------------------------------ REFEREE 1
def W_phi(u, x, WC=3.4, NW=6801):
    """W_x(u) by direct trapezoid over the Phi plane (float64)."""
    w = np.linspace(-WC, WC, NW)
    h = w[1] - w[0]
    v = Phv(u + w) * Phv(u - w) * np.cos(2.0 * x * w)
    return 2.0 * (h * (v.sum() - 0.5 * (v[0] + v[-1])))


_gl = {}


def glnp(n):
    if n not in _gl:
        _gl[n] = np.polynomial.legendre.leggauss(n)
    return _gl[n]


def S_R1(x, r, U=3.4, npan=14, ndeg=40):
    """REFEREE 1: direct double quadrature of int_r^U (u-r) W_x(u) du."""
    t, wq = glnp(ndeg)
    edges = np.linspace(r, U, npan + 1)
    tot = 0.0
    for i in range(npan):
        a, b = edges[i], edges[i + 1]
        hm, mid = (b - a) / 2.0, (a + b) / 2.0
        for tk, wk in zip(t, wq):
            u = mid + hm * tk
            tot += hm * wk * (u - r) * W_phi(u, x)
    return tot


# ------------------------------------------------------------------ REFEREE 2
def S_R2(x, r, U=3.4, TMAX=140.0, NT=28000, npan=14, ndeg=40):
    """REFEREE 2: W_x from What_x = G(.+x)G(.-x) then quadrature in u.

    W_x(u) = (2/pi) int_0^inf G(t+x) G(t-x) cos(2 t u) dt,   G = Xi/2.
    Only the elementary transform pair is used; no distributional step.
    """
    tg = np.linspace(0.0, TMAX, NT + 1)
    ht = tg[1] - tg[0]
    # G(t+x)G(t-x) on the t grid, computed once in mp then cast to float
    prev = mp.mp.dps
    mp.mp.dps = 30
    gp = np.array([float(XiR(t + x) * XiR(t - x) / 4) for t in tg])
    mp.mp.dps = prev

    def W(u):
        v = gp * np.cos(2.0 * tg * u)
        return (2.0 / math.pi) * (ht * (v.sum() - 0.5 * (v[0] + v[-1])))

    t, wq = glnp(ndeg)
    edges = np.linspace(r, U, npan + 1)
    tot = 0.0
    for i in range(npan):
        a, b = edges[i], edges[i + 1]
        hm, mid = (b - a) / 2.0, (a + b) / 2.0
        for tk, wk in zip(t, wq):
            u = mid + hm * tk
            tot += hm * wk * (u - r) * W(u)
    return tot


# ------------------------------------------------------------------ candidates
def _grid(T, ph):
    ed, e = [mp.mpf(0)], mp.mpf('1e-8')
    while e < ph:
        ed.append(e)
        e *= 10
    e = ph
    while e < T:
        ed.append(e)
        e += ph
    ed.append(mp.mpf(T))
    return ed


_GL = {}


def gl(n):
    k = (n, mp.mp.dps)
    if k not in _GL:
        _GL[k] = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(
            mp.mpf(-1), mp.mpf(1), n, mp.mp.prec)
    return _GL[k]


def panel(f, a, b, deg=5):
    nd = gl(deg)
    a, b = mp.mpf(a), mp.mpf(b)
    h, m = (b - a) / 2, (a + b) / 2
    return h * mp.fsum(w * f(m + h * t) for t, w in nd)


def S_A0(x, r, T=120, deg=5, ph=mp.mpf('0.5')):
    """cos INSIDE the bracket; DC tail is int_T^inf Xi(x)^2 t^-2 dt = Xi(x)^2/T."""
    x, r, T = mp.mpf(x), mp.mpf(r), mp.mpf(T)
    X2 = XiR(x) ** 2
    f = lambda t: (X2 - XiR(x + t) * XiR(x - t) * mp.cos(2 * r * t)) / t ** 2 if t else mp.mpf(0)
    ed = _grid(T, ph)
    tot = mp.fsum(panel(f, ed[i], ed[i + 1], deg) for i in range(len(ed) - 1))
    return (tot + X2 / T) / (8 * mp.pi)


def S_A1(x, r, T=120, deg=5, ph=mp.mpf('0.5')):
    return S_A0(x, r, T, deg, ph) - mp.mpf(r) / 8 * XiR(x) ** 2


def S_B(x, r, T=120, deg=5, ph=mp.mpf('0.5')):
    """cos OUTSIDE the bracket; DC tail int_T^inf cos(at)/t^2 = cos(aT)/T - a(pi/2-Si(aT))."""
    x, r, T = mp.mpf(x), mp.mpf(r), mp.mpf(T)
    X2 = XiR(x) ** 2
    f = lambda t: (X2 - XiR(x + t) * XiR(x - t)) * mp.cos(2 * r * t) / t ** 2 if t else mp.mpf(0)
    ed = _grid(T, ph)
    tot = mp.fsum(panel(f, ed[i], ed[i + 1], deg) for i in range(len(ed) - 1))
    a = 2 * r
    tail = X2 / T if a == 0 else X2 * (mp.cos(a * T) / T - a * (mp.pi / 2 - mp.si(a * T)))
    return (tot + tail) / (8 * mp.pi)


# ------------------------------------------------------------------ commands
def cmd_wcheck():
    """Cross-check the transform pair What_x(eta) = G(eta/2+x)G(eta/2-x) itself."""
    mp.mp.dps = 30
    print('# att534 wcheck: W_x(u) from the Phi plane vs from What = G(.+x)G(.-x)')
    print('#     x      u        W (Phi plane)        W (Fourier)          rel')
    TMAX, NT = 140.0, 28000
    tg = np.linspace(0.0, TMAX, NT + 1)
    ht = tg[1] - tg[0]
    for x in (2.0, 5.0):
        gp = np.array([float(XiR(t + x) * XiR(t - x) / 4) for t in tg])
        for u in (0.0, 0.3, 0.8, 1.5):
            a = W_phi(u, x)
            v = gp * np.cos(2.0 * tg * u)
            b = (2.0 / math.pi) * (ht * (v.sum() - 0.5 * (v[0] + v[-1])))
            print('  %6.2f %6.2f   %-20.12g %-20.12g %.3g'
                  % (x, u, a, b, abs(a - b) / max(abs(a), 1e-300)))
            sys.stdout.flush()


def cmd_adjudicate(dps=30):
    mp.mp.dps = dps
    print('# att534 ADJUDICATION  (closed forms at dps=%d; referees in float64)' % dps)
    print('# R1 = direct Phi-plane double quadrature (no Fourier theory)')
    print('# R2 = Wigner-Fourier referee (no distributional step)')
    print()
    hdr = ('#   x     r      R1                   R2                   '
           '(A0) cos-in          (A1) cos-in+lin      (B) cos-out')
    print(hdr)
    for (x, r) in ((2.0, 0.0), (2.0, 0.25), (2.0, 0.5), (5.0, 0.25), (9.0, 0.5)):
        r1 = S_R1(x, r)
        r2 = S_R2(x, r)
        a0, a1, b = float(S_A0(x, r)), float(S_A1(x, r)), float(S_B(x, r))
        print('  %5.1f %5.2f   %-20.12g %-20.12g %-20.12g %-20.12g %-20.12g'
              % (x, r, r1, r2, a0, a1, b))
        print('  %5s %5s   rel vs R1 ->                              '
              '%-20.4g %-20.4g %-20.4g'
              % ('', '', abs(a0 - r1) / abs(r1), abs(a1 - r1) / abs(r1),
                 abs(b - r1) / abs(r1)))
        print('  %5s %5s   rel R2 vs R1 = %.4g'
              % ('', '', abs(r2 - r1) / abs(r1)))
        sys.stdout.flush()
    print()
    print('# pure identity check (A1) == (B), independent of both referees:')
    for (x, r) in ((2, '0.25'), (7, '0.9'), (14, '0.3'), (60, '0.4')):
        r = mp.mpf(r)
        a1, b = S_A1(x, r), S_B(x, r)
        d = abs(a1 - b) / max(abs(b), mp.mpf('1e-300'))
        print('   x=%-4s r=%-5s  (A1)-(B) = %-14s  rel = %s'
              % (x, mp.nstr(r, 4), mp.nstr(a1 - b, 6), mp.nstr(d, 6)))


def cmd_audit(dps=30):
    mp.mp.dps = dps
    print('# att534 AUDIT of the RequestProject/XiStructureFunction.lean identifications')
    print('#   def  xiStructure z   = riemannXi (1/2 - I*z) + deriv riemannXi (1/2 - I*z)')
    print('#   thm  xiStructure_Estar : Estar xiStructure z')
    print('#                          = riemannXi (1/2 - I*z) - deriv riemannXi (1/2 - I*z)')
    print('#   def  IsHB E := forall z, 0 < z.im -> ‖Estar E z‖ < ‖E z‖')
    print()
    print('# (i) claim  xi(1/2 - i z) = Xi(z)   and   xi\'(1/2 - i z) = + i Xi\'(z)')
    print('#     (the SECOND is the sign the Lean file calls load-bearing)')
    for zz in (mp.mpc('0.3', '0.7'), mp.mpc('12', '0.2'), mp.mpc('-4', '1.1')):
        A = xi(mp.mpf(1) / 2 - 1j * zz)
        P = mp.diff(xi, mp.mpf(1) / 2 - 1j * zz)
        X, D = Xi(zz), mp.diff(Xi, zz)
        print('   z=%-18s |A - Xi| = %-10s  |P - i Xi\'| = %-10s  |P + i Xi\'| = %s'
              % (mp.nstr(zz, 6), mp.nstr(abs(A - X), 4), mp.nstr(abs(P - 1j * D), 4),
                 mp.nstr(abs(P + 1j * D), 4)))
    print()
    print('# (ii) claim  HB defect Re[A conj P] == Khat := -Im[Xi\' conj Xi]')
    print('#      and    ‖A-P‖ < ‖A+P‖  <=>  0 < Re[A conj P]   (polarization)')
    for (x, y) in (('1.7', '0.4'), ('0.6', '0.25'), ('3.1', '0.15'), ('14.1', '0.05')):
        z = mp.mpc(x, y)
        A = xi(mp.mpf(1) / 2 - 1j * z)
        P = mp.diff(xi, mp.mpf(1) / 2 - 1j * z)
        defect = mp.re(A * mp.conj(P))
        khat = -mp.im(mp.diff(Xi, z) * mp.conj(Xi(z)))
        print('   z=%-6s+%-6si  Re[A conj P]=%-16s Khat=%-16s rel=%-9s '
              '‖E*‖<‖E‖:%-6s defect>0:%s'
              % (x, y, mp.nstr(defect, 10), mp.nstr(khat, 10),
                 mp.nstr(abs(defect - khat) / abs(khat), 4),
                 abs(A - P) < abs(A + P), defect > 0))
    print()
    print('# (iii) claim Khat = Im[-Xi\'/Xi]*|Xi|^2  (att530\'s stated validation target)')
    for (x, y) in (('1.7', '0.4'), ('0.6', '0.25'), ('3.1', '0.15')):
        z = mp.mpc(x, y)
        pred = mp.im(-mp.diff(Xi, z) / Xi(z)) * abs(Xi(z)) ** 2
        khat = -mp.im(mp.diff(Xi, z) * mp.conj(Xi(z)))
        print('   z=%-6s+%-6si  ImM|Xi|^2=%-18s Khat=%-18s rel=%s'
              % (x, y, mp.nstr(pred, 10), mp.nstr(khat, 10),
                 mp.nstr(abs(pred - khat) / abs(khat), 4)))
    print()
    print('# (iv) claim Khat(y,x) = 8 int_0^inf u sinh(2yu) W_x(u) du   [Ph = P0]')
    t, wq = glnp(40)
    for (x, y) in ((1.7, 0.4), (3.1, 0.15), (0.6, 0.25)):
        edges = np.linspace(0.0, 3.4, 14 + 1)
        tot = 0.0
        for i in range(14):
            a, b = edges[i], edges[i + 1]
            hm, mid = (b - a) / 2.0, (a + b) / 2.0
            for tk, wk in zip(t, wq):
                u = mid + hm * tk
                tot += hm * wk * u * math.sinh(2.0 * y * u) * W_phi(u, x)
        wig = 8.0 * tot
        khat = float(-mp.im(mp.diff(Xi, mp.mpc(x, y)) * mp.conj(Xi(mp.mpc(x, y)))))
        print('   x=%-5s y=%-5s  wigner=%-20.12g  Xi-deriv=%-20.12g  rel=%.4g'
              % (x, y, wig, khat, abs(wig - khat) / abs(khat)))
        sys.stdout.flush()


if __name__ == '__main__':
    a = sys.argv[1:]
    c = a[0] if a else 'adjudicate'
    {'adjudicate': cmd_adjudicate, 'audit': cmd_audit,
     'wcheck': cmd_wcheck}[c](*[int(t) for t in a[1:]])
