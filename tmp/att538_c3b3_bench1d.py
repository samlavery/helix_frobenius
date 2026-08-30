"""C3 batch 3, corrected + 1-D bench.

NORMALIZATION (corrected; att537 was 2x too large).  Titchmarsh 2.16.1:

    Xi(x) = xi(1/2 + ix) = 2 int_0^inf Phi(u) cos(xu) du = int_R phi(u) e^{ixu} du,

with phi = even extension of Phi.  So c = 1, NOT 2.

THE 1-D REDUCTION (this replaces every 2401^2 grid).  For

    J_m(x) := int int m((a+b)/2) phi(a) phi(b) cos(x(a-b)) da db,

put u=(a+b)/2, d=a-b (Jacobian 1).  Then J_m(x) = int_R m(u) C(u,x) du with the
**cell density**

    C(u,x) := int_R cos(xd) phi(u+d/2) phi(u-d/2) dd
            = 2 int_R phi(u+v) phi(u-v) cos(2xv) dv
            = 2 Re[ e^{-2ixu} (g_x * phi)(2u) ],    g_x(p) = phi(p) e^{2ixp}.

One FFT convolution per x gives C(.,x) on the whole u-grid.  Consequences, all
exact identities (verified below):

    int_R C(u,x) du                 = Xi(x)^2                          (= L_0)
    L_n(x) := 4^n int u^{2n} C du   = (-1)^n d^{2n}/dh^{2n}[Xi(x+h)Xi(x-h)]_{h=0}
    L_1                             = 2 (Xi'^2 - Xi Xi'')
    |Xi(x+iy)|^2                    = int_R e^{-2yu} C(u,x) du   (two-sided Laplace!)
                                    = sum_n L_n(x) y^{2n}/(2n)!
    d/dy |Xi(x+iy)|^2               = 4 int_0^inf u sinh(2yu) C(u,x) du
    T(r,x) := int_r^inf (u-r) C(u,x) du      (the ramp / triangle form)
    J_m(x)                          = 2 int_0^inf m''(r) T(r,x) dr   for m even, m(0)=m'(0)=0

TARGET (= RH, = the half-plane domination of rh_iff_xiStructure_dominates):
    for every real x and every y >= 0 :  d/dy |Xi(x+iy)|^2 >= 0.

SUFFICIENT, in strictly decreasing strength:
    (S1)  C(u,x) >= 0 for all u,x                  ==> everything below
    (S2)  T(r,x) >= 0 for all r>=0, x              ==> target (m_y'' >= 0)
    (S3)  L_n(x) >= 0 for all n>=1, x              ==> target
    (S4)  the target itself.
"""
import numpy as np
import mpmath as mp
from math import comb

PI = np.pi
mp.mp.dps = 40


# ------------------------------------------------------------------ Phi ----
def Phi(u):
    u = np.abs(np.asarray(u, dtype=float))
    e2, e52, e92 = np.exp(2.0 * u), np.exp(2.5 * u), np.exp(4.5 * u)
    tot = np.zeros_like(u)
    for n in range(1, 80):
        ex = np.exp(-PI * n * n * e2)
        term = (4.0 * PI * PI * n ** 4 * e92 - 6.0 * PI * n * n * e52) * ex
        tot += term
        if np.max(np.abs(term)) < 1e-320:
            break
    return tot


def Phi_mp(u):
    u = abs(mp.mpf(u))
    e2, e52, e92 = mp.e ** (2 * u), mp.e ** (mp.mpf(5) / 2 * u), mp.e ** (mp.mpf(9) / 2 * u)
    tot = mp.mpf(0)
    for n in range(1, 60):
        ex = mp.e ** (-mp.pi * n * n * e2)
        term = (4 * mp.pi ** 2 * n ** 4 * e92 - 6 * mp.pi * n * n * e52) * ex
        tot += term
        if abs(term) < mp.mpf(10) ** (-mp.mp.dps - 10) and n > 3:
            break
    return tot


def xi_mp(s):
    return mp.mpf(0.5) * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi_mp(z):
    return xi_mp(mp.mpf(0.5) + 1j * z)


def say(tag, s):
    print(f"[{tag}] {s}", flush=True)


# --------------------------------------------------------------- grid ------
A = 2.0
NHALF = 4096
g = np.linspace(-A, A, 2 * NHALF + 1)     # phi grid
h = g[1] - g[0]
phig = Phi(g)

# Simpson weights on g
wS = np.ones_like(g)
wS[1:-1:2] = 4.0
wS[2:-1:2] = 2.0
wS *= h / 3.0


def Xi_num(x):
    return float(np.sum(wS * phig * np.cos(x * g)))


say("N0", "NORMALIZATION CHECK  Xi(x) = int_R phi e^{ixu} du   vs mpmath xi(1/2+ix)")
for x in [0.0, 1.0, 5.0, 14.134725, 25.0, 40.0]:
    a = Xi_num(x)
    b = float(mp.re(Xi_mp(mp.mpf(x))))
    say("N0", f"   x={x:10.5f}  num={a: .16e}  mp={b: .16e}  ratio={a/b if b!=0 else float('nan'):.15f}")

# ------------------------------------------------------- C(u,x) via FFT ----
# convolution grid: s = a + b in [-2A, 2A], step h
def C_of_x(x):
    """returns (ugrid, C(u,x)) on u = s/2, s the convolution grid."""
    gx = phig * np.exp(2j * x * g)
    conv = np.convolve(gx, phig) * h          # (g_x * phi)(s), s-grid below
    s = np.linspace(-2 * A, 2 * A, len(conv))
    u = s / 2.0
    C = 2.0 * np.real(np.exp(-2j * x * u) * conv)
    return u, C


ugrid, _ = C_of_x(0.0)
du = ugrid[1] - ugrid[0]
wU = np.ones_like(ugrid)
wU[1:-1:2] = 4.0
wU[2:-1:2] = 2.0
wU *= du / 3.0
if len(ugrid) % 2 == 0:                       # need odd for Simpson
    ugrid = ugrid[:-1]
    wU = np.ones_like(ugrid)
    wU[1:-1:2] = 4.0
    wU[2:-1:2] = 2.0
    wU *= du / 3.0
    TRIM = True
else:
    TRIM = False


def C_arr(x):
    u, C = C_of_x(x)
    return (C[:-1] if TRIM else C)


def nu(k, x):
    """Xi^{(k)}(x)."""
    if k % 2 == 0:
        s = float(np.sum(wS * phig * (g ** k) * np.cos(x * g)))
        return ((-1) ** (k // 2)) * s
    else:
        s = float(np.sum(wS * phig * (g ** k) * np.sin(x * g)))
        return ((-1) ** ((k - 1) // 2 + 1)) * s


def L_direct(n, x):
    tot = 0.0
    for j in range(2 * n + 1):
        tot += ((-1) ** j) * comb(2 * n, j) * nu(j, x) * nu(2 * n - j, x)
    return ((-1) ** n) * tot


say("N1", "IDENTITY CHECKS for the cell density C(u,x)")
for x in [0.0, 5.0, 14.134725, 25.0]:
    C = C_arr(x)
    m0 = float(np.sum(wU * C))
    m2 = 4.0 * float(np.sum(wU * ugrid ** 2 * C))
    m4 = 16.0 * float(np.sum(wU * ugrid ** 4 * C))
    say("N1", f"   x={x:10.5f}  int C = {m0: .12e}   Xi^2 = {Xi_num(x)**2: .12e}")
    say("N1", f"                 4 int u^2 C = {m2: .12e}   L_1 = {L_direct(1,x): .12e}")
    say("N1", f"                16 int u^4 C = {m4: .12e}   L_2 = {L_direct(2,x): .12e}")
    for y in [0.1, 0.3, 0.49]:
        lap = float(np.sum(wU * np.exp(-2 * y * ugrid) * C))
        tru = float(abs(Xi_mp(mp.mpf(x) + 1j * mp.mpf(y))) ** 2)
        say("N1", f"                 y={y:4.2f}: int e^{{-2yu}}C = {lap: .12e}  |Xi(x+iy)|^2 = {tru: .12e}"
                  f"  rel={abs(lap-tru)/tru:.2e}")

# ------------------------------------------------ (C1) sign of C(u,x) ------
say("C1", "SIGN OF THE CELL DENSITY C(u,x)  --  (S1): C>=0 everywhere would give RH")
xs = [0.0, 1.0, 3.0, 6.0, 9.0, 12.0, 14.134725, 17.0, 21.022, 25.010, 30.424, 40.0, 60.0, 90.0]
for x in xs:
    C = C_arr(x)
    imin = int(np.argmin(C))
    cmax = float(np.max(np.abs(C)))
    say("C1", f"   x={x:10.5f}  min C = {C[imin]: .6e} at u={ugrid[imin]: .5f}"
              f"   max|C| = {cmax:.6e}   ratio = {C[imin]/cmax: .4f}")

# ------------------------------------- (B2) ramp / triangle form T(r,x) ----
def T_ramp_all(C):
    """T(r,x) = int_r^inf (u-r) C(u) du for every r on the u-grid, by two
    reverse cumulative trapezoid integrations."""
    # I1(r) = int_r^inf C du ; T(r) = int_r^inf I1(t) dt
    Crev = C[::-1]
    I1 = np.concatenate(([0.0], np.cumsum((Crev[:-1] + Crev[1:]) / 2.0) * du))[::-1]
    I1rev = I1[::-1]
    T = np.concatenate(([0.0], np.cumsum((I1rev[:-1] + I1rev[1:]) / 2.0) * du))[::-1]
    return T


say("B2", "MIXTURE OF TRIANGLES: T(r,x) = int_r^inf (u-r) C du.  (S2): T>=0 ==> RH")
say("B2", "   check int_0^inf T dr = L_1/16 first")
i0 = int(np.argmin(np.abs(ugrid)))
for x in [0.0, 5.0, 14.134725, 25.0]:
    C = C_arr(x)
    T = T_ramp_all(C)
    rr = ugrid[i0:]
    integ = float(np.trapezoid(T[i0:], rr))
    say("B2", f"   x={x:10.5f}  int_0^inf T dr = {integ: .10e}   L_1/16 = {L_direct(1,x)/16: .10e}"
              f"   rel={abs(integ-L_direct(1,x)/16)/abs(L_direct(1,x)/16):.2e}")

worst = (1e300, None, None)
for x in xs:
    C = C_arr(x)
    T = T_ramp_all(C)
    seg = T[i0:]
    j = int(np.argmin(seg))
    if seg[j] < worst[0]:
        worst = (float(seg[j]), float(ugrid[i0 + j]), x)
    say("B2", f"   x={x:10.5f}  min_{{r>=0}} T = {seg[j]: .6e} at r={ugrid[i0+j]: .5f}"
              f"   T(0,x) = {seg[0]: .6e}")
say("B2", f"   WORST T over probe set: {worst[0]: .6e} at r={worst[1]:.5f}, x={worst[2]}")

# ------------------------------------ (B1) higher finite differences L_n ---
say("B1", "HIGHER FINITE DIFFERENCES L_n(x) = 4^n int u^{2n} C du, n=1..8")
say("B1", "   reported scale-free as L_n / (4^n int u^{2n} |C| du)")
for x in xs:
    row = f"   x={x:10.5f} "
    for n in range(1, 9):
        num = float(np.sum(wU * ugrid ** (2 * n) * C_arr(x)))
        den = float(np.sum(wU * ugrid ** (2 * n) * np.abs(C_arr(x))))
        row += f" {num/den: .4f}"
    print(row, flush=True)

# ------------------------------------------------ (S4) the target itself ---
say("S4", "d/dy |Xi(x+iy)|^2 = 4 int_0^inf u sinh(2yu) C du   (must be >=0; RH true numerically)")
for x in [0.0, 14.134725, 21.022, 30.424, 60.0]:
    C = C_arr(x)
    row = f"   x={x:10.5f} "
    for y in [0.02, 0.1, 0.25, 0.49]:
        pos = ugrid >= 0
        val = 4.0 * float(np.sum(wU[pos] * ugrid[pos] * np.sinh(2 * y * ugrid[pos]) * C[pos]))
        row += f"  y={y:4.2f}:{val: .4e}"
    print(row, flush=True)
