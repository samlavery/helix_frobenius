"""part 4: verify the load-bearing Fourier-transform identity by direct quadrature, and
   verify lambda_2 to high precision against an independent Stieltjes-constant route."""
import math, sys, os
import numpy as np
from mpmath import mp, mpf, mpc
def P(*a): print(*a); sys.stdout.flush()
mp.dps = 30

P("(A) claimed identity:  (1/pi) int_0^inf f_n(t) cos(t x) dt = e^{-x/2} L_{n-1}^{(1)}(x), x>0")
P("    with f_n(t) = 4 sin^2(n arctan(1/(2t))).  Direct oscillatory quadrature vs mpmath Laguerre.")
def fn(t, n):
    return 4*mp.sin(n*mp.atan(1/(2*t)))**2
for (n, x) in ((1, mpf('0.6931471805599453')), (3, mpf('1.0986122886681098')),
               (8, mpf('2.5649493574615367')), (20, mpf('0.6931471805599453')),
               (40, mpf('1.6094379124341003'))):
    # f_n(t) -> 0 like n^2/t^2; integrate cos(tx) f_n(t) by mpmath's oscillatory quadrature
    val = mp.quadosc(lambda t: fn(t, n)*mp.cos(t*x), [0, mp.inf], period=2*mp.pi/x)/mp.pi
    ref = mp.e**(-x/2)*mp.laguerre(n-1, 1, x)
    P(f"   n={n:>3} x={float(x):.5f}:  quad {mp.nstr(val,12):>16}   e^-x/2 L = "
      f"{mp.nstr(ref,12):>16}   rel {mp.nstr(abs(val-ref)/abs(ref),3)}")

P("\n(B) lambda_2 to 25 digits, independent route via Stieltjes constants:")
mp.dps = 40
gam = mp.euler
gam1 = mpf('-0.0728158454836767248605863758749013191377')
eta0 = gam
eta1 = -2*gam1 - gam**2
lam2_arith = 2*eta0 + eta1
# arch closed form at n=2, summed to k = 10^6 with tail
n = 2
K = 2000000
acc = mpf(0)
kk = np.arange(1, K+1, dtype=np.float64)
u = 1.0/(2*kk+1)
acc = float(np.sum((1-u)**n - 1 + n*u)) + n*(1-math.log(2))
tail = 0.0
for j in range(2, 8):
    tail += ((-1)**j)*float(mp.binomial(n, j))*float(mp.zeta(j, mpf(K)+mpf(3)/2))/2.0**j
lam2_arch = -(mp.log(mp.pi)+gam)*mpf(n)/2 + mpf(acc) + mpf(tail)
P(f"   eta_0 = gamma        = {mp.nstr(eta0,25)}")
P(f"   eta_1 = -2 gamma_1 - gamma^2 = {mp.nstr(eta1,25)}")
P(f"   lambda_2^arith = 2 eta_0 + eta_1 = {mp.nstr(lam2_arith,25)}")
P(f"   lambda_2^arch  = {mp.nstr(lam2_arch,20)}")
P(f"   lambda_2       = {mp.nstr(lam2_arith+lam2_arch,20)}")
P(f"   their docstring 'literature': 0.0923457352880")
P(f"   my contour value           : 0.0923457352280466704")
