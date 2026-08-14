#!/usr/bin/env python3
"""
Attempt 034 — the mean-square assembly of Z: exact identity + explicit off-diagonal charge.

Derived:  int Z^2/T = (c/pi^2)[ ln(1/theta) - 1/2 + row ]  with c = 1 or 1/2 (convention
check below);  row := int_1^inf F(alpha)/alpha^2 d alpha.
GATE C (Poisson anchor): synthetic Poisson ordinates at density dbar: F == 1 all alpha:
  int Z^2/T should = (c/pi^2)[ln(1/theta) - 1/2 + 1]. Pins c.
GATE D (identity on data): row(theta) = (pi^2/c) int Z^2/T - ln(1/theta) + 1/2 at
  theta = 1/3 and 1/2 must agree (theta-independence!) and sit near 1 (PCC).
ASSEMBLY (the explicit-bound structure): pair-form of int Z^2:
  diagonal: dbar * ||z-profile||^2 with ||.||^2 = 2(1-ln2)/(pi L)*(c-normalized)
  off-diagonal crude charge: r := [sum over zero-pairs |G(gamma-gamma')|]/(N G(0)),
  computed EXACTLY from the kernel G (the phi-autocorrelation) and (i) the true zeros
  (measures true r with signs: should be ~ -0.11), (ii) absolute values (the crude charge),
  (iii) absolute values with BW-max-count inflation (the fully-explicit charge).
Projected explicit row-bound = (pi^2/c)*diag*(1 + r_crude) - ln(1/theta) + 1/2.
"""
import numpy as np
import time

REPO = "/Users/samuellavery/work/helix_frobenius"

def phi_quad(vgrid, L, nq=3000):
    U = 50.0/L
    u = (np.arange(nq)+0.5)*(U/nq)
    out = np.empty(len(vgrid))
    for i, v in enumerate(vgrid):
        w = u + 1j*v
        out[i] = np.imag(np.sum((np.exp(-w*L)-np.exp(-2*w*L))/w**2)*(U/nq))
    return out

def build_Z(ordinates, ts, dt, L, dens_of_t):
    M = 2**19
    vv = (np.arange(M)-M/2)*dt; vv[np.abs(vv) < 1e-12] = 1e-9
    prof = phi_quad(vv, L)
    pad = 600.0
    tspad = np.arange(ts[0]-pad, ts[-1]+pad+dt, dt)
    grid = np.zeros(len(tspad))
    zw = ordinates[(ordinates > tspad[0]) & (ordinates < tspad[-1])]
    np.add.at(grid, np.clip(np.searchsorted(tspad, zw), 0, len(tspad)-1), 1.0)
    grid -= dens_of_t(tspad)*dt
    K = int(2**np.ceil(np.log2(len(tspad)+M)))
    kern = np.zeros(K)
    kern[:M//2] = prof[M//2:]
    kern[K-M//2:] = prof[:M//2]
    Z = np.fft.irfft(np.fft.rfft(grid, K)*np.fft.rfft(kern, K), K)[:len(tspad)]*(-1.0/(np.pi*L))
    i0 = int(pad/dt)
    Zc = Z[i0:i0+len(ts)]
    return Zc - np.mean(Zc)

# ---------- GATE C: Poisson anchor ----------
rng = np.random.default_rng(7)
T0, T1 = 3000.0, 19000.0
dt = 0.02
ts = np.arange(T0, T1, dt)
Tmid = np.exp(np.mean(np.log(ts)))
l = np.log(Tmid/(2*np.pi))
dbar = l/(2*np.pi)
npts = rng.poisson(dbar*(T1-T0+2000))
poiss = np.sort(rng.uniform(T0-1000, T1+1000, npts))
for theta in [1/3, 1/2]:
    L = theta*l
    Z = build_Z(poiss, ts, dt, L, lambda t: dbar*np.ones_like(t))
    meas = np.mean(Z**2)
    pred1  = (1.0/np.pi**2)*(np.log(1/theta) - 0.5 + 1.0)
    pred05 = pred1/2
    print(f"GATE C theta={theta:.3f}: Poisson int Z^2/T = {meas:.5f}  pred(c=1) {pred1:.5f}  pred(c=1/2) {pred05:.5f}", flush=True)

# ---------- GATE D: identity on real zeros ----------
zeros = np.sort(np.load(f"{REPO}/tmp/att019_zeros_to20k.npy"))
dens = lambda t: np.log(t/(2*np.pi))/(2*np.pi)
rows = {}
for theta in [1/3, 1/2]:
    L = theta*l
    Z = build_Z(zeros, ts, dt, L, dens)
    meas = np.mean(Z**2)
    for c, tag in [(1.0, "c=1"), (0.5, "c=1/2")]:
        row = (np.pi**2/c)*meas - np.log(1/theta) + 0.5
        rows[(theta, tag)] = row
    print(f"GATE D theta={theta:.3f}: int Z^2/T = {meas:.5f}  row(c=1) = {rows[(theta,'c=1')]:.4f}  row(c=1/2) = {rows[(theta,'c=1/2')]:.4f}", flush=True)
print("  (theta-independence + closeness to 1 selects the convention)", flush=True)

# ---------- ASSEMBLY: off-diagonal charge ----------
theta = 0.5
L = theta*l
M = 2**19
vv = (np.arange(M)-M/2)*dt; vv[np.abs(vv) < 1e-12] = 1e-9
prof = phi_quad(vv, L)
# G = autocorrelation of prof (the pair kernel), computed by FFT
K = 2**20
Fp = np.fft.rfft(prof, K)
G = np.fft.irfft(np.abs(Fp)**2, K)*dt
G = np.concatenate([G[-M//2:], G[:M//2]])   # center
vg = (np.arange(M)-M/2)*dt
G0 = G[M//2]
z = zeros[(zeros > T0) & (zeros < T1)]
N = len(z)
# true off-diagonal (signed) and crude (absolute):
sig, crude = 0.0, 0.0
win = 200.0
for i, g in enumerate(z):
    lo, hi = np.searchsorted(z, g-win), np.searchsorted(z, g+win)
    d = z[lo:hi]-g
    d = d[d != 0.0]
    idx = np.clip(((d - vg[0])/dt).astype(int), 0, M-1)
    sig += np.sum(G[idx]); crude += np.sum(np.abs(G[idx]))
r_true, r_crude = sig/(N*G0), crude/(N*G0)
# fully-explicit variant: |G|-sums with BW max local count in place of actual zeros:
# integral bound: sum_offdiag |G| <= (max count per unit)* int |G| dv
intabsG = np.trapezoid(np.abs(G), vg)
maxcount = 2*(0.10076*np.log(Tmid) + 0.2446*np.log(np.log(Tmid))) + dbar  # BW-style per unit
r_bw = maxcount*intabsG/G0
print(f"ASSEMBLY theta=1/2: G0={G0:.4f}  r_true={r_true:+.4f}  r_crude(actual zeros)={r_crude:.4f}  r_BW(explicit)={r_bw:.4f}", flush=True)
diag = dbar*G0/(np.pi*L)**2*(np.pi*L)**2  # diag of int Z^2/T = dbar*G0/(pi L)^2... report directly:
diagZ = dbar*G0/(np.pi*L)**2
print(f"  diag int Z^2/T = {diagZ:.5f}  (measured total was ~0.055)", flush=True)
for c, tag in [(1.0, "c=1"), (0.5, "c=1/2")]:
    for rname, r in [("crude", r_crude), ("BW", r_bw)]:
        rowb = (np.pi**2/c)*diagZ*(1+r) - np.log(1/theta) + 0.5
        print(f"  projected explicit row-bound [{tag}, {rname}]: {rowb:.3f}", flush=True)
