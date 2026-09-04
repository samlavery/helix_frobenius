# att596: (i) pf closed form vs recursion; (ii) symbol = autocorrelation integral; (iii) n-collected AC vs jets AC
import numpy as np, mpmath as mp, math
from math import comb
mp.mp.dps = 30
def pf(d, j, k):
    if k == 0: return ({j: mp.mpf(1)}, {})
    if j == 0: return ({}, {k: mp.mpf(1)})
    a1, b1 = pf(d, j, k-1); a2, b2 = pf(d, j-1, k)
    a = {key: (a1.get(key, 0) + a2.get(key, 0))/d for key in set(a1)|set(a2)}
    b = {key: (b1.get(key, 0) + b2.get(key, 0))/d for key in set(b1)|set(b2)}
    return a, b
d = mp.mpf('1.4')
# (i) closed form
err = 0
for j in range(1, 6):
    for k in range(1, 6):
        a, b = pf(d, j, k)
        for i in range(0, 8):
            cf = comb(j+k-i-1, k-1)/d**(j+k-i) if 1 <= i <= j else 0
            err = max(err, abs(a.get(i, 0) - cf))
            cfb = comb(j+k-i-1, j-1)/d**(j+k-i) if 1 <= i <= k else 0
            err = max(err, abs(b.get(i, 0) - cfb))
print("(i) pf closed form max abs err:", mp.nstr(err, 3))
# (ii) symbol A_jk(l) = sum_i C(j+k-i-1,k-1) d^{-(j+k-i)} l^{i-1}/(i-1)!  vs  ∫_0^∞ (u+l)^{j-1}/(j-1)! u^{k-1}/(k-1)! e^{-du} du
def A_sym(j, k, l):
    return sum(comb(j+k-i-1, k-1) * d**(-(j+k-i)) * l**(i-1)/mp.factorial(i-1) for i in range(1, j+1))
err = 0
for j in range(1, 5):
    for k in range(1, 5):
        for l in [mp.mpf('0.7'), mp.mpf('2.3')]:
            I = mp.quad(lambda u: (u+l)**(j-1)/mp.factorial(j-1) * u**(k-1)/mp.factorial(k-1) * mp.exp(-d*u), [0, mp.inf])
            err = max(err, abs(I - A_sym(j, k, l)))
print("(ii) symbol = autocorrelation integral, max abs err:", mp.nstr(err, 3))
# (iii) n-collected AC vs jets-AC for random R, at s = 1.2+50i  (prime series truncated at X; both sides use the SAME truncation)
s0, g0 = 1.2, 50.0; s = mp.mpc(s0, g0); N = 3
rng = np.random.default_rng(596); r = [mp.mpc(0)] + [mp.mpc(*rng.normal(size=2)) for _ in range(N)]
X = 3000
lam = {}
for p in range(2, X+1):
    if all(p % q for q in range(2, int(p**0.5)+1)):
        q = p
        while q <= X: lam[q] = mp.log(p); q *= p
def Lser(m):  # Σ Λ(n) (log n)^m n^{-s}, truncated
    return sum(L * mp.log(n)**m * mp.power(n, -s) for n, L in lam.items())
# jets-AC: prime part of jetValueS summed against r
M = 2*N + 2
def jetAC(j, k):
    a, b = pf(d, j, k)
    J = {m: -(-1)**m * Lser(m) for m in range(0, M)}   # prime part of (ξ'/ξ)^{(m)}
    v = a.get(1, 0) * 2 * mp.re(J[0])
    for i in range(M-1): v += a.get(i+2, 0) * (J[i+1] / ((-1)**(i+1) * mp.factorial(i+1)))
    for l in range(M-1): v += b.get(l+2, 0) * ((-1)**(l+1) * mp.conj(J[l+1]) / mp.factorial(l+1))
    return v
AC_jets = sum(mp.conj(r[j]) * r[k] * jetAC(j, k) for j in range(1, N+1) for k in range(1, N+1))
def A_R(l): return sum(mp.conj(r[j]) * r[k] * A_sym(j, k, l) for j in range(1, N+1) for k in range(1, N+1))
AC_n = -2 * sum(L * mp.power(n, -s0) * mp.re(mp.exp(-1j*g0*mp.log(n)) * A_R(mp.log(n))) for n, L in lam.items())
print("(iii) AC via jets =", mp.nstr(AC_jets, 12), " AC collected by n =", mp.nstr(AC_n, 12), " rel", mp.nstr(abs(AC_jets-AC_n)/abs(AC_n), 3))
# Gram check: A_jk(0) = Pascal-Hankel
print("(iv) A_jk(0) vs C(j+k-2,j-1)/d^(j+k-1):", max(abs(A_sym(j,k,mp.mpf(0)) - comb(j+k-2,j-1)/d**(j+k-1)) for j in range(1,6) for k in range(1,6)))
