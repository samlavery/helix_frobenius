"""att225: POSITIVE CONTROL at the same sizes/precision as att224.
True A (all zeros on-line, verified range): theory says n_- = q = 0 at every n.
Compare against adversarial: n=5 -> -6.7e-8, n=6 -> -2.32e-5."""
from mpmath import mp, mpf, mpc, quad, matrix, eighe, nstr, zeta, diff
mp.dps = 25
Y = mpf('1.5'); A_, B_ = mpf('10'), mpf('30')
def xi(s): return (s*(s-1)/2) * mp.pi**(-s/2) * mp.gamma(s/2) * zeta(s)
def Afun(z): return xi(mpf(1)/2 - mpc(0,1)*z)
def dlogA(z): return diff(Afun, z)/Afun(z)
def horiz(k, sign):
    f = lambda x: (mpc(x, sign*Y)**k) * dlogA(mpc(x, sign*Y))
    v = quad(f, [A_, (A_+B_)/2, B_]) / (2*mp.pi*mpc(0,1))
    return -v if sign > 0 else v
def lat(x, k):
    return quad(lambda y: (mpc(x,y)**k)*dlogA(mpc(x,y))*mpc(0,1),
                [-Y,0,Y]) / (2*mp.pi*mpc(0,1))
mu = []
for k in range(11):
    mu.append((horiz(k,+1)+horiz(k,-1)+lat(B_,k)-lat(A_,k)).real)
print("POSITIVE CONTROL census (same numerics as adversarial):")
for n in [4,5,6]:
    H = matrix(n,n)
    for i in range(n):
        for j in range(n): H[i,j] = mu[i+j]
    ev = [e.real for e in eighe(H, eigvals_only=True)]
    sc = max(abs(e) for e in ev)
    floor = sc * mpf(10)**(-24)
    gen_neg = sum(1 for e in ev if e < -floor)
    print(f"  n={n}: min-eig {nstr(min(ev),3):>12}  noise floor {nstr(floor,2):>9}"
          f"  GENUINE negatives: {gen_neg}", flush=True)
    print(f"        eigs " + " ".join(nstr(e,3) for e in ev))
