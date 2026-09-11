#!/usr/bin/env python3
"""att703 — the TWO-ENDED grown fiber (helix + anti-helix), per ledger 702's step 0.
   F_Z(s) = Σ_{n≤⌈Z⌉} (−1)^{n+1} w(n/Z) n^{−s}, w = the compiled smooth entry window;
   G_Z(s) = F_Z(s) + χ_η(s) F_Z(1−s), χ_η(s) = χ(s)(1−2^{1−s})/(1−2^s)  (η's own functional equation),
   so G_Z(1−s) = χ_η(1−s) G_Z(s) exactly and G_Z → 2η.  On the line u(t) = 2 Re(e^{i(ϑ+φ)} F_Z(½+it)) is real
   (the grown fiber's Hardy function), φ = arg(1 − 2^{½+it}).
   PRE-REGISTERED. Box B = [0.2, 0.8] × [10, 50] (9 zeta ordinates inside).  For each head Z:
     N_box = zeros of G_Z in B (argument principle),  N_sign = sign changes of u on [10, 50],
     N_far = zeros of G_Z in [0.52, 0.8] × [10, 50].
   Decision: if for every head Z ≥ 60 (head ≥ height, the head law) N_far = 0 and N_box = N_sign = 9, the two-ended
   grown fiber's events are ALL ON THE AXIS at finite head and the clause "one cancellation per height" holds per
   stage on a finite object; if N_far > 0 at some head ≥ 60, mirror pairs exist and the compact-eventually form stays.
   PREDICTION (from the reflection argument on a simple zero): N_far = 0, N_box = N_sign = 9 at every Z ≥ 60;
   the control Z = 25 (head below height) may show anything."""
import numpy as np, mpmath as mp
mp.mp.dps = 25
out = open("tmp/att703_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()

def w(u):
    u = np.asarray(u, dtype=float)
    r = np.zeros_like(u)
    m = u < 1
    r[m] = np.exp(1 - 1/(1 - u[m]**2))
    return r
def F(Z, s):
    s = np.asarray(s, dtype=complex)
    n = np.arange(1, int(np.ceil(Z)) + 1, dtype=float)
    coef = ((-1.0)**(n + 1)) * w(n / Z)
    return np.einsum('n,ns->s', coef, np.exp(-np.outer(np.log(n), s)))
def chi_eta(s):
    s = mp.mpc(s)
    chi = 2**s * mp.pi**(s - 1) * mp.sin(mp.pi * s / 2) * mp.gamma(1 - s)
    return chi * (1 - 2**(1 - s)) / (1 - 2**s)
def G(Z, s_arr):
    s_arr = np.asarray(s_arr, dtype=complex)
    ce = np.array([complex(chi_eta(s)) for s in s_arr])
    return F(Z, s_arr) + ce * F(Z, 1 - s_arr)
def theta(t):
    t = mp.mpf(t)
    return mp.siegeltheta(t) + mp.arg(1 - 2**(mp.mpf('0.5') + 1j*t))
def hardy_u(Z, ts):
    vals = F(Z, 0.5 + 1j*np.asarray(ts))
    ph = np.array([complex(mp.exp(1j*theta(t))) for t in ts])
    return 2*np.real(ph*vals), np.max(np.abs(np.imag(ph*vals)))/max(1e-300, np.max(np.abs(2*np.real(ph*vals))))
def count_box(Z, s0, s1, t0, t1, h=0.004):
    # boundary counterclockwise: bottom, right, top, left
    b = np.concatenate([np.linspace(s0, s1, int((s1-s0)/h)+1) + 1j*t0,
                        s1 + 1j*np.linspace(t0, t1, int((t1-t0)/h)+1),
                        np.linspace(s1, s0, int((s1-s0)/h)+1) + 1j*t1,
                        s0 + 1j*np.linspace(t1, t0, int((t1-t0)/h)+1)])
    g = G(Z, b)
    ang = np.angle(g); d = np.diff(ang); d = (d + np.pi) % (2*np.pi) - np.pi
    return np.sum(d)/(2*np.pi), np.max(np.abs(d)), np.min(np.abs(g))
def sign_changes(Z, t0, t1, h=0.002):
    ts = np.arange(t0, t1 + h, h)
    u, imrel = hardy_u(Z, ts)
    sc = np.where(np.sign(u[:-1]) * np.sign(u[1:]) < 0)[0]
    return len(sc), [round(float(ts[i]), 3) for i in sc], imrel
zeta_ords = [float(mp.zetazero(k).imag) for k in range(1, 10)]
say("zeta ordinates in [10,50]:", [round(x, 3) for x in zeta_ords])
for Z in (25, 60, 100, 200, 400, 1000):
    Nb, jmp, gmin = count_box(Z, 0.2, 0.8, 10.0, 50.0)
    Nf, jmpf, gminf = count_box(Z, 0.52, 0.8, 10.0, 50.0)
    Ns, locs, imrel = sign_changes(Z, 10.0, 50.0)
    say(f"Z={Z:5d}  N_box={Nb:+.4f} (max phase step {jmp:.2f}, min|G| on ∂B {gmin:.2e})   N_far={Nf:+.4f} (max step {jmpf:.2f})   "
        f"N_sign={Ns} (Im/Re residual {imrel:.1e})")
    say("        sign changes at", locs)
