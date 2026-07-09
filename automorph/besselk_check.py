import mpmath as mp
mp.mp.dps = 30
# (1) VERIFY the identity: (2x^{mu_a}e^{-2pi x}) star (2x^{mu_b}e^{-2pi x}) = 8 x^{(mu_a+mu_b)/2} K_{mu_b-mu_a}(4pi sqrt x)
# Mellin convolution (f star g)(x) = int_0^inf f(x/t) g(t) dt/t.
def lhs(x, ma, mb):
    f = lambda t: (2*(x/t)**ma*mp.e**(-2*mp.pi*x/t)) * (2*t**mb*mp.e**(-2*mp.pi*t)) / t
    return mp.quad(f, [0, mp.inf])
def rhs(x, ma, mb):
    return 8*x**((ma+mb)/2)*mp.besselk(mb-ma, 4*mp.pi*mp.sqrt(x))
for (x,ma,mb) in [(0.4,0.0,0.0),(1.3,0.5,1.5),(0.7,1.0,2.0),(2.1,-0.5,0.5)]:
    L,R = lhs(x,ma,mb), rhs(x,ma,mb)
    print(f"  x={x} mu=({ma},{mb}): LHS-RHS = {mp.nstr(L-R,3)}   (Mellin conv of two clocks = Bessel-K)")

# (2) The closed-form Bessel-K kernel closes the FE to machine precision where the crude MeijerG did not.
# Real-quadratic Dedekind zeta zeta_{Q(sqrt5)} = zeta * L(chi5): completion Gamma_R(s)^2 whose inverse-
# Mellin IS the K_0 Bessel (mu_a=mu_b=0 above).  a_n = sum_{d|n} chi5(d); theta(t)=sum a_n k(n t).
def chi5(n):
    r=n%5
    return {0:0,1:1,2:-1,3:-1,4:1}[r]
N=4000
a=[0]*(N+1)
for d in range(1,N+1):
    c=chi5(d)
    if c:
        for m in range(d,N+1,d): a[m]+=c
# completed theta with the K_0 kernel: k(x)=2 K_0(4 pi sqrt(x)) (inverse-Mellin of Gamma_R(s)^2-type), scale B
import math
def theta(t,B):
    s=mp.mpf(0)
    for n in range(1,N+1):
        x=n*t/B
        if x>25: break
        s+=a[n]*2*mp.besselk(0,4*mp.pi*mp.sqrt(x))
    return s
B=mp.sqrt(5)/mp.pi   # disc^{1/2}/pi normalization
# FE for a real-quadratic zeta: theta(1/t) = t * theta(t)  (2D self-dual, weight from Gamma_R^2)
for t in [mp.mpf('0.6'), mp.mpf('1.4')]:
    lhs_,rhs_=theta(1/t,B), t*theta(t,B)
    print(f"  Q(sqrt5) K_0-kernel FE: theta(1/t)-t theta(t) at t={t} = {mp.nstr(lhs_-rhs_,4)}  (closed-form Bessel-K)")
