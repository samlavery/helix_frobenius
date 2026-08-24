"""att530 — C3: is K_y = -J_y positive-definite?  Fourier scan + Wigner structure.

K_y(d) = 8 int_0^inf u sinh(2yu) Phi(u+d/2) Phi(u-d/2) du      [Wigner-type form]
K_hat_y(x) = int K_y(d) cos(xd) dd = 8 int_0^inf u sinh(2yu) W_Phi(u,x) du
PREDICTED IDENTITY (validates the whole Phi-side chain):
        K_hat_y(x) = Im M(x+iy) * |Xi(x+iy)|^2,   M = -Xi'/Xi
PRE-REGISTERED: K_hat >= 0 everywhere (it IS the HB defect, so a robust negative
would refute RH, not just entrance C).  Informative output = the SHAPE, and whether
W_Phi itself goes negative (it must, unless Phi is Gaussian -- Hudson).
"""
import math, mpmath as mp
mp.mp.dps = 20

def P0(u):
    t = 0.0
    for n in range(1, 12):
        a = math.pi*n*n*math.exp(2*u)
        if a > 700: break
        t += (2*math.pi**2*n**4*math.exp(4.5*u) - 3*math.pi*n*n*math.exp(2.5*u))*math.exp(-a)
    return t
Ph = lambda u: P0(abs(u))

A, B, M = -4.0, 4.0, 1200
h = (B-A)/M
grid = [A+i*h for i in range(M+1)]
W = [1 if i in (0, M) else (4 if i % 2 else 2) for i in range(M+1)]
F = [Ph(u) for u in grid]

def wigner(u, x):
    """W_Phi(u,x) = 2 int Phi(u+w)Phi(u-w) cos(2xw) dw"""
    s = 0.0
    for i in range(M+1):
        w = grid[i]
        s += W[i]*Ph(u+w)*Ph(u-w)*math.cos(2*x*w)
    return 2*s*h/3

def Khat(y, x):
    s = 0.0
    for i in range(M+1):
        u = grid[i]
        if u <= 0: continue
        s += W[i]*u*math.sinh(2*y*u)*wigner(u, x)
    return 8*s*h/3

def xi(s): return 0.5*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
def Xi(z): return xi(mp.mpf(1)/2+1j*z)

print("### validation:  K_hat_y(x)  vs  Im M(x+iy)*|Xi(x+iy)|^2")
for (x, y) in ((1.7, 0.4), (0.6, 0.25), (3.1, 0.15)):
    z = mp.mpc(x, y)
    pred = float(mp.im(-mp.diff(Xi, z)/Xi(z)) * abs(Xi(z))**2)
    got = Khat(y, x)
    print("   x=%-5s y=%-5s  K_hat=%-18.10g  ImM|Xi|^2=%-18.10g  rel=%.3g"
          % (x, y, got, pred, abs(got-pred)/abs(pred)))

print("\n### Wigner W_Phi(u,x) sign  (Hudson: must go negative unless Phi Gaussian)")
neg = []
for u in (0.1, 0.3, 0.6, 1.0):
    for x in (2.0, 5.0, 9.0, 14.0):
        v = wigner(u, x)
        if v < 0: neg.append((u, x, v))
print("   negative samples found: %d   e.g. %s"
      % (len(neg), ["u=%.1f x=%.1f W=%.3g" % t for t in neg[:3]]))
