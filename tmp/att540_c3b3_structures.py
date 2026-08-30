"""C3 batch 3 — the remaining positivity structures, fixed checkpoints only.

No nested adaptive quadrature.  Double precision is used ONLY where att538 validated it
(identities to 1e-16 for x <= 25); every hostile sign is re-checked at two fixed cutoffs
and two precisions with mpmath.

Objects (normalization c = 1, corrected):
  Xi(x) = int_R phi(u) e^{ixu} du,  phi = even extension of Riemann's Phi
  C(u,x) = 2 int_R phi(u+v) phi(u-v) cos(2xv) dv          (Wigner / cell density)
  int e^{-i lam u} C du = Xi(x+lam/2) Xi(x-lam/2) =: R(lam,x)
  D(lam,x) = [Xi(x)^2 - R(lam,x)]/lam^2 ,  T(r,x) = (1/pi) int_0^inf cos(lam r) D dlam
  L_n(x) = 4^n int u^{2n} C du = (2n)! * [y^{2n}] |Xi(x+iy)|^2
"""
import numpy as np
import mpmath as mp
from math import comb

PI = np.pi


def say(t, s):
    print(f"[{t}] {s}", flush=True)


def Phi(u, nmax=80):
    u = np.abs(np.asarray(u, dtype=float))
    e2, e52, e92 = np.exp(2 * u), np.exp(2.5 * u), np.exp(4.5 * u)
    tot = np.zeros_like(u)
    for n in range(1, nmax + 1):
        term = (4 * PI ** 2 * n ** 4 * e92 - 6 * PI * n ** 2 * e52) * np.exp(-PI * n ** 2 * e2)
        tot += term
        if np.max(np.abs(term)) < 1e-320:
            break
    return tot


def Phi_term(u, n):
    u = np.abs(np.asarray(u, dtype=float))
    e2, e52, e92 = np.exp(2 * u), np.exp(2.5 * u), np.exp(4.5 * u)
    return (4 * PI ** 2 * n ** 4 * e92 - 6 * PI * n ** 2 * e52) * np.exp(-PI * n ** 2 * e2)


A = 2.0
NH = 4096
g = np.linspace(-A, A, 2 * NH + 1)
hstep = g[1] - g[0]


def cell_density(phivals, x):
    gx = phivals * np.exp(2j * x * g)
    conv = np.convolve(gx, phivals) * hstep
    s = np.linspace(-2 * A, 2 * A, len(conv))
    u = s / 2
    return u, 2.0 * np.real(np.exp(-2j * x * u) * conv)


phig = Phi(g)

# ================================================== B7 variation diminution ==
say("B7", "VARIATION DIMINUTION: sign changes of u -> C(u,x) on |u| <= 1.6")
say("B7", "   (a positive-definite Wigner density would have none)")
for x in [0.0, 5.0, 9.0, 12.0, 14.134725, 17.0, 21.022, 25.011]:
    u, C = cell_density(phig, x)
    m = (np.abs(u) <= 1.6) & (np.abs(C) > 1e-13 * np.max(np.abs(C)))
    sg = np.sign(C[m])
    nch = int(np.sum(sg[1:] != sg[:-1]))
    say("B7", f"   x={x:10.5f}  sign changes = {nch:3d}   min/max ratio = {C[m].min()/np.abs(C[m]).max(): .4f}")

# ================================================== B8 theta term pairing ====
say("B8", "THETA-SERIES TERM PAIRING: is the n=1 term of Phi alone enough / positive?")
p1 = Phi_term(g, 1)
say("B8", f"   min over grid of Phi_1 = {p1.min(): .6e}  (Phi_1 < 0 near u=0: term is NOT a positive kernel)")
say("B8", f"   min over grid of Phi   = {phig.min(): .6e}  (the full sum IS positive)")
for x in [12.0, 14.134725, 21.022]:
    u1, C1 = cell_density(p1, x)
    u, C = cell_density(phig, x)
    m1 = np.abs(u1) <= 1.6
    m = np.abs(u) <= 1.6
    say("B8", f"   x={x:10.5f}  min C[Phi_1] ratio = {C1[m1].min()/np.abs(C1[m1]).max(): .4f}"
              f"   min C[Phi] ratio = {C[m].min()/np.abs(C[m]).max(): .4f}")

# ================================================== B9 heat flow / de Bruijn =
say("B9", "HEAT FLOW (de Bruijn H_t): phi_t(u) = e^{t u^2} phi(u).  Does t>0 restore C>=0?")
say("B9", "   identity: C_t(u,x) = e^{2t u^2} * [Wigner of phi with an EXTRA e^{2t v^2} factor]")
for t in [0.0, 0.1, 0.25, 0.5, 1.0]:
    phit = np.exp(t * g ** 2) * phig
    row = f"   t={t:4.2f} "
    for x in [12.0, 14.134725, 21.022]:
        u, C = cell_density(phit, x)
        m = np.abs(u) <= 1.6
        row += f"  x={x:9.5f}:{C[m].min()/np.abs(C[m]).max(): .4f}"
    print(row, flush=True)

# ================================================== B6 total positivity ======
mp.mp.dps = 30


def xi(s):
    return mp.mpf(1) / 2 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(x):
    return mp.re(xi(mp.mpf(1) / 2 + mp.mpc(0, 1) * x))


say("B6", "TOTAL POSITIVITY: Hankel matrix of the even moments mu_n = int u^{2n} C du = L_n/4^n.")
say("B6", "   C is a positive measure in u^2 (Hamburger)  <=>  every Hankel minor >= 0.")
NMOM = 5
for xv in ["0", "5", "14.134725", "21.022"]:
    x = mp.mpf(xv)
    f = lambda yy: xi(mp.mpf(1) / 2 + mp.mpc(0, 1) * (x + yy)) * xi(mp.mpf(1) / 2 + mp.mpc(0, 1) * (x - yy))
    co = mp.taylor(f, 0, 2 * NMOM, method="quad", radius=mp.mpf("0.35"))
    L = [mp.re(co[2 * n]) * mp.factorial(2 * n) for n in range(NMOM + 1)]
    mu = [L[n] / mp.mpf(4) ** n for n in range(NMOM + 1)]
    say("B6", f"   x={xv:>10}  L_n = " + ", ".join(mp.nstr(v, 6) for v in L))
    mins = []
    for k in range(1, NMOM // 2 + 2):
        M = mp.matrix(k, k)
        for i in range(k):
            for j in range(k):
                M[i, j] = mu[i + j]
        mins.append(mp.det(M))
    say("B6", f"              Hankel minors det = " + ", ".join(mp.nstr(v, 6) for v in mins))

# ================================================== B2 ramp checkpoints ======
say("B2", "RAMP T(r,x) hostile checkpoints: fixed composite Simpson, two cutoffs, two precisions.")


def T_fixed(x, rs, LAM, NODES, dps):
    mp.mp.dps = dps
    x = mp.mpf(x)
    LAM = mp.mpf(LAM)
    hh = LAM / NODES
    lams = [i * hh for i in range(NODES + 1)]
    X0 = Xi(x)
    X0sq = X0 ** 2
    # D on the grid (lam = 0 handled by the L_1/8 limit via a one-sided small step)
    Dv = []
    for l in lams:
        if l == 0:
            e = mp.mpf(10) ** (-8)
            Dv.append((X0sq - Xi(x + e / 2) * Xi(x - e / 2)) / e ** 2)
        else:
            Dv.append((X0sq - Xi(x + l / 2) * Xi(x - l / 2)) / l ** 2)
    out = {}
    for r in rs:
        r = mp.mpf(r)
        tot = mp.mpf(0)
        for i, l in enumerate(lams):
            w = 1 if i in (0, NODES) else (4 if i % 2 == 1 else 2)
            tot += w * mp.cos(l * r) * Dv[i]
        head = tot * hh / 3 / mp.pi
        if r == 0:
            tail = X0sq / LAM
        else:
            tail = X0sq * (mp.cos(LAM * r) / LAM - r * (mp.pi / 2 - mp.si(LAM * r)))
        out[str(r)] = head + tail / mp.pi
    return out


for xv in ["14.134725", "30.425"]:
    for (LAM, NODES, dps) in [(40, 1200, 25), (80, 2400, 25), (40, 1200, 40), (80, 2400, 40)]:
        res = T_fixed(xv, ["0", "0.25", "1.0"], LAM, NODES, dps)
        say("B2", f"   x={xv:>10} LAM={LAM:3d} N={NODES:5d} dps={dps:2d}  " +
                  "  ".join(f"T({k})={mp.nstr(v,8)}" for k, v in res.items()))
