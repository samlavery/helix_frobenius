"""att226: is the window-side Hankel PRIME-COMPUTABLE?  Recompute the top-edge
(windowing) moments from the Dirichlet/archimedean expansion — no zero data —
and compare with the A'/A values of att221.

Top edge: z = x + iY, s = 1/2 - i z = (1/2 + Y) - i x, Re s = 2 > 1.
xi'/xi(s) = 1/s + 1/(s-1) - (1/2)log(pi) + (1/2)psi(s/2) + zeta'/zeta(s),
zeta'/zeta(s) = -sum_{n>=2} Lambda(n) n^{-s}   (Lambda >= 0: the lever)
dlogA(z) = -i * (xi'/xi)(s)."""
from mpmath import mp, mpf, mpc, quad, nstr, log, pi, psi, mangoldt, zeta, diff

mp.dps = 20
Y = mpf('1.5'); A_, B_ = mpf('10'), mpf('30')
NTERMS = 30000
LAM = [(n, mpf(mangoldt(n))) for n in range(2, NTERMS) if mangoldt(n) != 0]
print(f"prime powers used: {len(LAM)}", flush=True)

def zeta_logderiv_prime(s):
    return -sum(L * mp.power(n, -s) for n, L in LAM)

def xi_logderiv_prime(s):
    return (1/s + 1/(s-1) - log(pi)/2 + psi(0, s/2)/2
            + zeta_logderiv_prime(s))

def dlogA_prime(z):
    s = mpf(1)/2 - mpc(0,1)*z
    return -mpc(0,1) * xi_logderiv_prime(s)

def top_moment_prime(k):
    f = lambda x: (mpc(x, Y)**k) * dlogA_prime(mpc(x, Y))
    return -(quad(f, [A_, (A_+B_)/2, B_]) / (2*pi*mpc(0,1)))

print("\ntop-edge windowing moments, PRIME/ARCHIMEDEAN route (no zero data):")
prime_vals = []
ref = ['1.76434', '40.6132', '971.221', '24095.2']
for k in range(4):
    v = top_moment_prime(k)
    prime_vals.append(v)
    print(f"  k={k}: {nstr(v.real, 8):>14}   (A'/A route: {ref[k]:>9})", flush=True)
print("\nrelative agreement:")
for k in range(4):
    r = mpf(ref[k])
    print(f"  k={k}: {nstr(abs(prime_vals[k].real - r)/abs(r), 3)}")
