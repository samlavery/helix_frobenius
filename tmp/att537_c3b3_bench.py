"""C3 batch 3 numeric bench.

Riemann's kernel  Phi(u) = sum_{n>=1} (4 pi^2 n^4 e^{9u/2} - 6 pi n^2 e^{5u/2}) exp(-pi n^2 e^{2u}),
even, positive;   Xi(x) = 4 int_0^inf Phi(u) cos(xu) du = 2 int_R phi(a) e^{ixa} da,
phi = even extension.

Everything below is a quadratic form in psi(a) = phi(a) e^{-ixa} against a HANKEL kernel
h(a+b).  The dictionary proved by hand in the transcript:

  J_m(x) := int int m((a+b)/2) phi(a) phi(b) cos(x(a-b)) da db
  |Xi(x+iy)|^2 = 4 * J_{cosh(2y.)}(x)          [m(t) = cosh(2yt)]
  L_n(x) := 4^{n+1} J_{t^{2n}}(x) = 4 int int (a+b)^{2n} phi phi cos(x(a-b))
          = (-1)^n d^{2n}/dh^{2n} [ Xi(x+h) Xi(x-h) ]_{h=0}
  |Xi(x+iy)|^2 = sum_n L_n(x) y^{2n} / (2n)!
  L_1 = 2 (Xi'^2 - Xi Xi'')                     [the pointwise "L1" of batch 2]
  target (RH) : d/dy |Xi(x+iy)|^2 >= 0 for y>=0, i.e. J_{m_y} >= 0, m_y(t) = t sinh(2yt).

Ramp/triangle decomposition (weighted_tail_primitive_identity):
  J_m(x) = 2 int_0^inf m''(r) T(r,x) dr,
  T(r,x) := int int_{a+b>2r} ((a+b)/2 - r) phi(a) phi(b) cos(x(a-b)) da db.
Since m_y'' >= 0 on [0,inf), T >= 0 for all r,x would give RH.
"""
import numpy as np
import mpmath as mp

PI = np.pi

# ---------------------------------------------------------------- Phi ------
def Phi(u):
    """Riemann's kernel, evaluated at |u| (even)."""
    u = np.abs(np.asarray(u, dtype=float))
    e2 = np.exp(2.0 * u)
    e52 = np.exp(2.5 * u)
    e92 = np.exp(4.5 * u)
    tot = np.zeros_like(u)
    for n in range(1, 60):
        ex = np.exp(-PI * n * n * e2)
        term = (4.0 * PI * PI * n**4 * e92 - 6.0 * PI * n * n * e52) * ex
        tot = tot + term
        if np.max(np.abs(term)) < 1e-300:
            break
    return tot


def report(tag, s):
    print(f"[{tag}] {s}", flush=True)


# ------------------------------------------------- validation of Xi, c -----
mp.mp.dps = 30

def xi_mp(s):
    s = mp.mpf(s) if not isinstance(s, mp.mpc) else s
    return 0.5 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def Xi_mp(z):
    return xi_mp(mp.mpf(0.5) + 1j * z)

A = 1.9          # phi(1.9) ~ 1e-40, safe cut
N = 2401         # odd, Simpson
grid = np.linspace(-A, A, N)
hstep = grid[1] - grid[0]
phig = Phi(grid)

# Simpson weights
w = np.ones(N)
w[1:-1:2] = 4.0
w[2:-1:2] = 2.0
w *= hstep / 3.0

def Xi_num(x):
    return 2.0 * np.sum(w * phig * np.cos(x * grid))

report("V1", "Xi validation  x : numeric  vs  mpmath xi(1/2+ix)")
for x in [0.0, 1.0, 5.0, 10.0, 14.134725, 20.0, 30.0]:
    a = Xi_num(x)
    b = float(mp.re(Xi_mp(mp.mpf(x))))
    report("V1", f"  x={x:9.4f}  num={a: .16e}  mp={b: .16e}  rel={abs(a-b)/max(abs(b),1e-300):.2e}")

# ------------------------------------------------------------ moments ------
def nu(k, x):
    """Xi^{(k)}(x) by differentiating under the integral: 2 int (ia)^k phi e^{ixa}."""
    if k % 2 == 0:
        s = np.sum(w * phig * (grid ** k) * np.cos(x * grid))
        return 2.0 * ((-1) ** (k // 2)) * s
    else:
        s = np.sum(w * phig * (grid ** k) * np.sin(x * grid))
        return 2.0 * ((-1) ** ((k - 1) // 2 + 1)) * s

from math import comb, factorial

def L_n(n, x):
    """(-1)^n sum_j (-1)^j C(2n,j) Xi^{(j)} Xi^{(2n-j)}."""
    tot = 0.0
    for j in range(2 * n + 1):
        tot += ((-1) ** j) * comb(2 * n, j) * nu(j, x) * nu(2 * n - j, x)
    return ((-1) ** n) * tot

report("V2", "L_1 = 2(Xi'^2 - Xi Xi'')  cross-check, and L_n signs")
for x in [0.0, 2.0, 5.0, 9.0, 14.0, 20.0, 30.0, 50.0]:
    l1a = L_n(1, x)
    l1b = 2.0 * (nu(1, x) ** 2 - nu(0, x) * nu(2, x))
    report("V2", f"  x={x:6.2f}  L1={l1a: .6e}  2(Xi'^2-XiXi'')={l1b: .6e} "
                 f"rel={abs(l1a-l1b)/max(abs(l1b),1e-300):.2e}")

report("B1", "higher finite differences L_n(x), n=1..6  (RH <=> all >= 0 for all x)")
xs = [0.0, 1.0, 3.0, 6.0, 9.0, 12.0, 14.134725, 17.0, 21.0, 25.0, 30.0, 40.0, 60.0]
hdr = "   x      " + "".join(f"    L_{n}        " for n in range(1, 7))
print(hdr, flush=True)
minL = {n: (1e300, None) for n in range(1, 7)}
for x in xs:
    row = f"  {x:7.3f} "
    for n in range(1, 7):
        v = L_n(n, x)
        row += f" {v: .6e}"
        # scale-free sign test
        if v < minL[n][0]:
            minL[n] = (v, x)
    print(row, flush=True)
for n in range(1, 7):
    report("B1", f"  min over grid of L_{n}: {minL[n][0]: .6e} at x={minL[n][1]}")

# ------------------------------- |Xi(x+iy)|^2 monotonicity in y (the target) ---
report("TGT", "d/dy |Xi(x+iy)|^2 by mpmath, direct (this IS the target inequality)")
for x in [0.0, 5.0, 14.134725, 21.022, 30.0]:
    for y in [0.05, 0.2, 0.45, 0.49]:
        f = lambda yy: abs(Xi_mp(mp.mpf(x) + 1j * mp.mpf(yy))) ** 2
        d = mp.diff(f, mp.mpf(y))
        report("TGT", f"  x={x:9.4f} y={y:4.2f}  d/dy|Xi|^2 = {float(d): .6e}")

# ------------------------------------------------- the ramp kernel T(r,x) ---
AA, BB = np.meshgrid(grid, grid, indexing="ij")
SUM = AA + BB
DIF = AA - BB
PP = np.outer(phig, phig)
W2 = np.outer(w, w)

def T_ramp(r, x):
    ker = np.where(SUM > 2.0 * r, (SUM / 2.0 - r), 0.0)
    return float(np.sum(W2 * ker * PP * np.cos(x * DIF)))

def J_kernel(hfun, x):
    return float(np.sum(W2 * hfun(SUM) * PP * np.cos(x * DIF)))

report("V3", "consistency: 4*int int (a+b)^2 phi phi cos  ==  L_1 ; and int_0^inf T dr = L_1/64")
for x in [0.0, 5.0, 14.0, 25.0]:
    lhs = 4.0 * J_kernel(lambda S: S ** 2, x)
    report("V3", f"  x={x:6.2f}  4*JJ={lhs: .6e}  L_1={L_n(1,x): .6e}  rel={abs(lhs-L_n(1,x))/abs(L_n(1,x)):.2e}")

rs = np.linspace(0.0, 1.6, 161)
for x in [0.0, 5.0, 14.0, 25.0]:
    vals = np.array([T_ramp(r, x) for r in rs])
    integ = np.trapezoid(vals, rs)
    report("V3", f"  x={x:6.2f}  int_0^inf T dr={integ: .6e}  L_1/64={L_n(1,x)/64: .6e} "
                 f"rel={abs(integ-L_n(1,x)/64)/max(abs(L_n(1,x)/64),1e-300):.2e}")

report("B2", "MIXTURE OF TRIANGLES: sign of the ramp form T(r,x).  T>=0 for all r,x ==> RH.")
print("    r  \\  x " + "".join(f"{x:>13.3f}" for x in [0.0, 5.0, 9.0, 14.134725, 21.0, 30.0]), flush=True)
worst = (1e300, None, None)
for r in [0.0, 0.05, 0.1, 0.2, 0.3, 0.5, 0.7, 0.9, 1.2]:
    row = f"  {r:6.3f}  "
    for x in [0.0, 5.0, 9.0, 14.134725, 21.0, 30.0]:
        v = T_ramp(r, x)
        row += f" {v: .5e}"
        if v < worst[0]:
            worst = (v, r, x)
    print(row, flush=True)
report("B2", f"  most negative T(r,x) on the probe grid: {worst[0]: .6e} at r={worst[1]}, x={worst[2]}")

# fine scan for negativity of T
report("B2", "  fine scan for T<0 ...")
neg = []
for r in np.linspace(0.0, 1.4, 29):
    for x in np.linspace(0.0, 60.0, 121):
        v = T_ramp(float(r), float(x))
        if v < 0:
            neg.append((float(r), float(x), v))
report("B2", f"  negative samples: {len(neg)} out of {29*121}")
if neg:
    neg.sort(key=lambda t: t[2])
    for t in neg[:12]:
        report("B2", f"    r={t[0]:.4f} x={t[1]:.3f}  T={t[2]: .6e}")
