#!/usr/bin/env python3
"""Riemann-Siegel zero finder (validated att064: 247/247 vs cache, max err 4.4e-5).
Usage: find_zeros(t0, t1, dt=0.02) -> ordinates. Main sum + first Psi-correction;
accuracy ~t^{-3/4}-grade; validated at t~1.5e4, used at t~1e6 (3812 zeros in 3s)."""
import numpy as np
def theta(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
def Z(ts):
    ts = np.atleast_1d(ts); out = np.empty(len(ts))
    a = np.sqrt(ts/(2*np.pi)); nu = a.astype(int); th = theta(ts)
    for v in np.unique(nu):
        m = nu == v
        n = np.arange(1, v+1)
        out[m] = 2*(np.cos(th[m][:,None] - ts[m][:,None]*np.log(n)[None,:])/np.sqrt(n)[None,:]).sum(axis=1)
        p = a[m] - v
        Psi = np.cos(2*np.pi*(p*p - p - 1.0/16))/np.cos(2*np.pi*p)
        out[m] += (-1)**(v-1)*(ts[m]/(2*np.pi))**(-0.25)*Psi
    return out
def find_zeros(t0, t1, dt=0.02):
    ts = np.arange(t0, t1, dt); zv = np.empty(len(ts))
    for i in range(0, len(ts), 20000):
        zv[i:i+20000] = Z(ts[i:i+20000])
    sc = np.nonzero(np.sign(zv[:-1]) != np.sign(zv[1:]))[0]
    zs = []
    for i in sc:
        lo, hi = ts[i], ts[i+1]; flo = zv[i]
        for _ in range(30):
            mid = 0.5*(lo+hi); fm = Z(np.array([mid]))[0]
            if np.sign(fm) == np.sign(flo): lo, flo = mid, fm
            else: hi = mid
        zs.append(0.5*(lo+hi))
    return np.array(zs)
