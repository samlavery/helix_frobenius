#!/usr/bin/env python3
"""att707 — WARP THE MULTIPLICATIVE FACE (Sam: "you aren't warping, are you").
   The fiber warp S has closed form clocks + END + anti-end + remainder (ledger 554c/560, END-TERM DC LAW).
   706's face was clocks alone and failed in the pole's shadow.  Warped face at front x (Riesz taper, L = log x):
      log E^w(s) = L_x(s) + Π_x(s),   Π_x′(s) = K_R(1−s),  K_R(u) = (x^u − 1)/(L u²)   (the Riesz kernel at the pole)
      Π_x(s) = −Ei(L(1−s)) + (x^{1−s} − 1)/(L(1−s))       (antiderivative; additive constant cancels in the ratio)
   so (log E^w)′ = ζ′/ζ + Σ_ρ K_R(ρ − s) + trivial: the warped face is ζ up to the Fejér zero comb.
   Two-ended: G^w = E^w + χ E^w(1−s);  R^w = χ E^w(1−s)/E^w;  slope across the axis
      κ^w(t) = −2ϑ′ + 2Σ w Λ n^{−½} cos(t log n) − 2 Re K_R(½ − it) = −2π D_{R,x}(t)   (568's register WITH the pole).
   PRE-REGISTERED.  P1: κ^w < 0 at every height t∈[10,50] at fronts 10², 10³, 10⁴ (⟺ D_{R,x} > 0).
   P2: finite-δ domination log|R^w| < 0 at every sampled t for δ ∈ {0.01, 0.05}; prediction: holds; at δ = 0.2 may fail.
   P3: every zero of G^w in [0.2,0.8]×[10,50] is on the axis, count 10 = axis sign changes.
   Decision: any κ^w ≥ 0 refutes P1; any log|R^w| ≥ 0 at δ ≤ 0.05 refutes P2; any off-axis zero refutes P3."""
import numpy as np, mpmath as mp
mp.mp.dps = 20
out = open("tmp/att707_results.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n"); out.flush()
def vonmangoldt_upto(x):
    N = int(x) + 1; lam = np.zeros(N); sieve = np.ones(N, dtype=bool); sieve[:2] = False
    for p in range(2, N):
        if sieve[p]:
            sieve[p*p::p] = False; q = p
            while q < N: lam[q] = np.log(p); q *= p
    return lam
def chi(s):
    s = mp.mpc(s); return complex(2**s * mp.pi**(s-1) * mp.sin(mp.pi*s/2) * mp.gamma(1-s))
def logabs_chi(s): return float(mp.log(abs(mp.mpc(chi(s)))))
def count_box(Gfun, s0, s1, t0, t1, h=0.004):
    b = np.concatenate([np.linspace(s0, s1, int((s1-s0)/h)+1) + 1j*t0,
                        s1 + 1j*np.linspace(t0, t1, int((t1-t0)/h)+1),
                        np.linspace(s1, s0, int((s1-s0)/h)+1) + 1j*t1,
                        s0 + 1j*np.linspace(t1, t0, int((t1-t0)/h)+1)])
    g = Gfun(b); ang = np.angle(g); d = np.diff(ang); d = (d + np.pi) % (2*np.pi) - np.pi
    return np.sum(d)/(2*np.pi), np.max(np.abs(d)), np.min(np.abs(g))
ts = np.arange(10.0, 50.0, 0.01)
thp = np.array([float(mp.diff(mp.siegeltheta, t)) for t in ts[::10]]); thp = np.interp(ts, ts[::10], thp)
for x in (100, 1000, 10000):
    L = np.log(x)
    lam = vonmangoldt_upto(x-1); n = np.arange(2, len(lam)); ln = np.log(n)
    w = np.clip(1 - ln/L, 0, None); coefL = w*lam[2:]/ln; coefM = w*lam[2:]
    def Lx(s):
        s = np.asarray(s, dtype=complex); return np.einsum('n,ns->s', coefL, np.exp(-np.outer(ln, s)))
    def Pi(s):   # warp: −Ei(L(1−s)) + (x^{1−s} − 1)/(L(1−s))
        s = np.asarray(s, dtype=complex); res = np.empty_like(s)
        for i, z in enumerate(s):
            u = mp.mpc(1 - z)
            res[i] = complex(-mp.ei(L*u) + (mp.e**(L*u) - 1)/(L*u))
        return res
    def logEw(s): return Lx(s) + Pi(s)
    def Ew(s): return np.exp(logEw(s))
    def G(s_arr):
        s_arr = np.asarray(s_arr, dtype=complex); ce = np.array([chi(z) for z in s_arr])
        return Ew(s_arr) + ce*Ew(1 - s_arr)
    # slope κ^w on the axis and its identification with −2π D_{R,x}
    clock = np.einsum('n,nt->t', coefM/np.sqrt(n), np.cos(np.outer(ln, ts)))
    KR = np.array([complex((mp.e**(L*u) - 1)/(L*u**2)) for u in (0.5 - 1j*ts)])
    kappa_w = -2*thp + 2*clock - 2*np.real(KR)
    D = thp/np.pi + np.real(KR)/np.pi - clock/np.pi
    # numerical slope of the exact warped log|R^w| across the axis (central difference), coarse grid, as a check
    tc = ts[::100]; h = 1e-4
    def logabsR(s):
        s = np.asarray(s, dtype=complex)
        return np.array([logabs_chi(z) for z in s]) + np.real(logEw(1 - s)) - np.real(logEw(s))
    num_slope = (logabsR(0.5 + h + 1j*tc) - logabsR(0.5 - h + 1j*tc))/(2*h)
    say(f"x={x:6d}: κ^w<0 on {np.mean(kappa_w<0):.4f} of heights; max κ^w = {kappa_w.max():+.4f}; "
        f"min D_{{R,x}} = {D.min():+.5f}; |κ^w + 2πD| max = {np.max(np.abs(kappa_w + 2*np.pi*D)):.1e}; "
        f"|κ^w − numerical slope| max = {np.max(np.abs(kappa_w[::100] - num_slope)):.2e}")
    rows = []
    for d in (0.01, 0.05, 0.1, 0.2):
        lr = logabsR(0.5 + d + 1j*ts[::5]); rows.append((d, np.mean(lr < 0), lr.max()))
    say("           domination: " + "  ".join(f"δ={d}: frac={f:.4f}, max log|R^w|={m:+.2e}" for d, f, m in rows))
    Nb, jmp, gmin = count_box(G, 0.2, 0.8, 10.0, 50.0)
    Nf, _, _ = count_box(G, 0.52, 0.8, 10.0, 50.0)
    tt = np.arange(10.0, 50.0, 0.002)
    ph = np.array([complex(mp.exp(1j*mp.siegeltheta(t))) for t in tt])
    u = 2*np.real(ph*Ew(0.5 + 1j*tt)); Ns = int(np.sum(np.sign(u[:-1])*np.sign(u[1:]) < 0))
    say(f"           zeros in box: N_box={Nb:+.3f} (max step {jmp:.2f}, min|G| {gmin:.2e})  N_far={Nf:+.3f}  axis sign changes={Ns}")
