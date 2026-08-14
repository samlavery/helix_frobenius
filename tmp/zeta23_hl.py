"""Derive the O_1 main term FROM THE PRIME SIDE ALONE, with no zero-side input.

O_1 = 2 sum_{n != m} a_n a_m Kern(n,m),  a_n = Lambda(n)/sqrt(n),
Kern(n,m) = sum_{k,l} R(log n, delta_kl) R(log m, delta_kl) cos(mbar_kl (log n - log m)).

In (p,j) coordinates (p = k-l >= 0 weighted w_p = 1 or 2, mbar = T + p h/2 + j h):
    Kern = sum_p w_p R_n(ph) R_m(ph) E_p(theta),   theta = log(n/m)
    E_p(theta) = sum_{j=0}^{d-1-p} cos((T + ph/2 + jh) theta)   -- closed form, a Dirichlet kernel
so 2 sum_{n!=m} = 4 sum_{h>=1} sum_n, and everything is a sum over additive shifts h = n - m.

Substituting the Hardy-Littlewood main term sum_m Lambda(m)Lambda(m+h) ~ S(h) x turns the
prime-power double sum into a sum over ALL integers weighted by S(n-m).  Four models:
    EXACT : weight Lambda(n)Lambda(m)          -- must reproduce the measured O_1 (validation)
    M1    : weight 1                           -- the density-1 / Lebesgue part
    M2    : weight S(n-m)                      -- full Hardy-Littlewood (conjectural input)
    M3    : weight 1 - 1/(2|n-m|)              -- density + the Montgomery-Soundararajan
                                                  secondary term only (the AVERAGED input)
"""
import time
import numpy as np

from zeta23_bench import phihat
from zeta23_prime import R_amb

C2 = 0.6601618158468696


def singular_series(H):
    """S(h) = 2 C2 prod_{p|h, p>2} (p-1)/(p-2) for even h, 0 for odd h."""
    S = np.zeros(H + 1)
    spf = np.zeros(H + 1, dtype=np.int64)
    for p in range(2, H + 1):
        if spf[p] == 0:
            spf[p::p] = np.where(spf[p::p] == 0, p, spf[p::p])
    for h in range(2, H + 1, 2):
        f, m = 1.0, h
        while m > 1:
            p = spf[m]
            if p > 2:
                f *= (p - 1) / (p - 2)
            while m % p == 0:
                m //= p
        S[h] = 2 * C2 * f
    return S


def R_all_integers(X, L, w, d, h, chunk=2048):
    """Rtab[n-1, p] = R(log n, p*h) for n = 1..X (n=1 gives u=0, handled by R_amb)."""
    deltas = np.arange(d) * h
    Rt = np.zeros((X, d))
    for n in range(1, X + 1):
        u = np.log(n)
        if u >= L:
            continue
        Rt[n - 1] = (phihat(deltas, L - u, w) if w <= u <= L - 2 * w
                     else R_amb(u, deltas, L, w))
    return Rt


def E_all(theta, T, h, d):
    """E_p(theta) for p = 0..d-1, vectorised over a batch of theta. Shape (len(theta), d)."""
    th = np.asarray(theta)[:, None]
    p = np.arange(d)[None, :]
    J = d - p                                  # number of j terms
    x = h * th                                 # common ratio angle
    A = T + p * h / 2.0
    s = np.sin(x / 2.0)
    small = np.abs(s) < 1e-12
    num = np.where(small, J, np.sin(J * x / 2.0) / np.where(small, 1.0, s))
    return num * np.cos((A + (J - 1) * h / 2.0) * th)


def O1_model(T, L, w, weights, cn, X, d, Rt, Hmax, report_H=()):
    """4 sum_{h=1..Hmax} sum_n cn[n] cn[n+h] weights(h) Kern(n, n+h)."""
    hh = 2 * np.pi / L
    wp = np.where(np.arange(d) == 0, 1.0, 2.0)
    tot = 0.0
    snap = {}
    for hshift in range(1, Hmax + 1):
        wgt = weights(hshift)
        if wgt == 0.0:
            if hshift in report_H:
                snap[hshift] = tot
            continue
        n = np.arange(1, X - hshift + 1)
        c1, c2 = cn[n - 1], cn[n + hshift - 1]
        act = (c1 != 0) & (c2 != 0)
        if not act.any():
            if hshift in report_H:
                snap[hshift] = tot
            continue
        n = n[act]
        pref = c1[act] * c2[act]
        acc = 0.0
        for i0 in range(0, n.size, 4096):
            nn = n[i0:i0 + 4096]
            th = np.log((nn + hshift) / nn)
            E = E_all(th, T, hh, d)
            RR = Rt[nn - 1] * Rt[nn + hshift - 1]
            acc += float(np.dot(pref[i0:i0 + 4096], (RR * E * wp).sum(axis=1)))
        tot += 4.0 * wgt * acc
        if hshift in report_H:
            snap[hshift] = tot
    return tot, snap
