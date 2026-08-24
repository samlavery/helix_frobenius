"""att531 — (STP): is the second tail of the Wigner slice nonnegative?

  W_x(u) = 2 int Phi(u+w)Phi(u-w) cos(2xw) dw          [Wigner slice, GOES NEGATIVE]
  S_x(r) = int_r^inf (u-r) W_x(u) du                    [second tail primitive]

S''_x = W_x, and for any weight w with w(0)=w'(0)=0, w''>=0:
  int_0^inf w(u) W_x(u) du = int_0^inf w''(r) S_x(r) dr.
w_y(u)=u sinh(2yu) and f_n(u)=u^{2n} (n>=1) both qualify, so
  (STP): S_x(r) >= 0  =>  K_hat_y(x) >= 0 for all y  AND  L_n(x) >= 0 for all n.

FALSIFICATION POWER: S_x(r) < 0 kills this sufficient route WITHOUT refuting RH.
PRE-REGISTERED: survives = no robust negative, esp. at x=14 where W_x < 0.
"""
import math

def P0(u):
    t = 0.0
    for n in range(1, 12):
        a = math.pi*n*n*math.exp(2*u)
        if a > 700: break
        t += (2*math.pi**2*n**4*math.exp(4.5*u) - 3*math.pi*n*n*math.exp(2.5*u))*math.exp(-a)
    return t
Ph = lambda u: P0(abs(u))

UMAX, NW = 3.0, 1600
hw = 2*UMAX/NW
wg = [-UMAX + i*hw for i in range(NW+1)]
Wt = [1 if i in (0, NW) else (4 if i % 2 else 2) for i in range(NW+1)]

def Wig(u, x):
    s = 0.0
    for i in range(NW+1):
        w = wg[i]
        s += Wt[i]*Ph(u+w)*Ph(u-w)*math.cos(2*x*w)
    return 2*s*hw/3

NU = 400
def S(x, r):
    hu = (UMAX - r)/NU
    if hu <= 0: return 0.0
    s = 0.0
    for i in range(NU+1):
        u = r + i*hu
        c = 1 if i in (0, NU) else (4 if i % 2 else 2)
        s += c*(u-r)*Wig(u, x)
    return s*hu/3

if __name__ == "__main__":
    print("   S_x(r) = int_r^inf (u-r) W_x(u) du      [(STP): all entries >= 0]")
    print("     x  \\ r     0.0          0.25         0.5          1.0          1.5")
    for x in (0.0, 2.0, 5.0, 9.0, 14.0, 20.0, 30.0):
        row = "   %6.1f   " % x
        for r in (0.0, 0.25, 0.5, 1.0, 1.5):
            row += "%-12.4g " % S(x, r)
        print(row)
    print("\n   control: W_x(u) itself at the hostile slice")
    for (u, x) in ((0.1, 14.0), (0.3, 9.0), (0.05, 20.0)):
        print("     W_Phi(%.2f, %.1f) = %.4g" % (u, x, Wig(u, x)))
