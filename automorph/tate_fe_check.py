import numpy as np, mpmath as mp
mp.mp.dps = 30
# 1) TWO-SIDED theta modularity (the double-sided helix / Poisson): theta(1/t)=sqrt(t) theta(t)
def theta2(t):  # sum_{n in Z} e^{-pi n^2 t}
    return mp.nsum(lambda n: mp.e**(-mp.pi*n*n*t), [-mp.inf, mp.inf])
for t in [0.3, 1.0, 2.7]:
    lhs, rhs = theta2(1/mp.mpf(t)), mp.sqrt(t)*theta2(mp.mpf(t))
    print(f"  theta(1/{t}) - sqrt({t})theta({t}) = {mp.nstr(lhs-rhs,3)}  (two-sided modular)")
# one-sided carries the defect (not modular on its own)
psi = lambda t: mp.nsum(lambda n: mp.e**(-mp.pi*n*n*t), [1, mp.inf])
t=0.4; print(f"  one-sided defect psi(1/t)-[sqrt(t)psi(t)+(sqrt(t)-1)/2] = {mp.nstr(psi(1/mp.mpf(t))-(mp.sqrt(t)*psi(t)+(mp.sqrt(t)-1)/2),3)}")
# 2) Riemann completion from the TWO-SIDED theta, NO FE input: Lambda(s)=int_1^inf (t^{s/2}+t^{(1-s)/2})psi dt/t -1/s -1/(1-s)
def Lam(s):
    integ = mp.quad(lambda t: (t**(s/2)+t**((1-s)/2))*psi(t)/t, [1, mp.inf])
    return integ - 1/s - 1/(1-s)
for s in [mp.mpf('0.5')+2j, mp.mpf('0.7')+3j, mp.mpf('0.3')-1j]:
    print(f"  Lambda({mp.nstr(s,4)}) - Lambda(1-s) = {mp.nstr(Lam(s)-Lam(1-s),3)}   (FE derived, no FE input)")
    ref = mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
    print(f"     vs pi^-s/2 Gamma(s/2) zeta(s): diff = {mp.nstr(Lam(s)-ref,3)}")
# 3) Tate archimedean: int_0^inf e^{-pi x^2} x^s dx/x = (1/2) pi^{-s/2} Gamma(s/2)
for s in [mp.mpf('1.3'), mp.mpf('2.1')]:
    I = mp.quad(lambda x: mp.e**(-mp.pi*x*x)*x**s/x, [0, mp.inf])
    print(f"  Tate arch int (s={s}) = {mp.nstr(I,6)}  vs (1/2)pi^-s/2 Gamma(s/2) = {mp.nstr(0.5*mp.pi**(-s/2)*mp.gamma(s/2),6)}")
