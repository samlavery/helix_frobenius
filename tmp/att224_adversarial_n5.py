"""att224: the DECISIVE case — adversarial off-line pair, census read AT and
ABOVE the size threshold m = r + 2q = 5.  Theory: n_-(H_n) = q = 1 for n >= 5."""
from mpmath import mp, mpf, mpc, quad, matrix, eighe, nstr, zeta, diff
mp.dps = 25
Y = mpf('1.5'); A_, B_ = mpf('10'), mpf('30')
def xi(s): return (s*(s-1)/2) * mp.pi**(-s/2) * mp.gamma(s/2) * zeta(s)
def Afun(z): return xi(mpf(1)/2 - mpc(0,1)*z)
W0 = mpc(mpf('18'), mpf('0.30'))
def dlogB(z):
    return diff(Afun, z)/Afun(z) + 1/(z - W0) + 1/(z - W0.conjugate())
def horiz(k, sign):
    f = lambda x: (mpc(x, sign*Y)**k) * dlogB(mpc(x, sign*Y))
    v = quad(f, [A_, (A_+B_)/2, B_]) / (2*mp.pi*mpc(0,1))
    return -v if sign > 0 else v
def lat(x, k):
    return quad(lambda y: (mpc(x,y)**k)*dlogB(mpc(x,y))*mpc(0,1),
                [-Y,0,Y]) / (2*mp.pi*mpc(0,1))
mu = []
for k in range(11):
    mu.append((horiz(k,+1)+horiz(k,-1)+lat(B_,k)-lat(A_,k)).real)
    print(f"  mu_{k} computed", flush=True)
print("\nADVERSARIAL census at/above threshold m=5:")
for n in [4,5,6]:
    H = matrix(n,n)
    for i in range(n):
        for j in range(n): H[i,j] = mu[i+j]
    ev = [e.real for e in eighe(H, eigvals_only=True)]
    sc = max(abs(e) for e in ev)
    npos = sum(1 for e in ev if e > 1e-14*sc); nneg = sum(1 for e in ev if e < -1e-14*sc)
    print(f"  n={n}: inertia ({npos},{nneg})  q={nneg}  "
          f"eigs " + " ".join(nstr(e,3) for e in ev), flush=True)
print("\n(theory: q=1 for n >= 5; q invisible below threshold)")
