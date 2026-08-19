"""att222: assemble the FULL window moments (windowing edges + laterals) and
test the census/inertia theorem at a real window — and locate where the
indefinite windowing block gets cancelled."""
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
for k in range(8):
    m = horiz(k,+1) + horiz(k,-1) + lat(B_,k) - lat(A_,k)
    mu.append(m.real)
print("FULL window moments mu_k (W=(10,30)):")
for k in range(6):
    print(f"  mu_{k} = {nstr(mu[k], 10)}")
zs = [mpf('14.134725'), mpf('21.022040'), mpf('25.010858')]
print("\nexact atomic prediction sum x_i^k over the 3 zeros:")
for k in range(6):
    print(f"  k={k}: {nstr(sum(z**k for z in zs), 10)}   (contour: {nstr(mu[k],10)})")

print("\nfull-moment Hankel inertia (census: n_- should be q = 0):")
for n in [2,3,4]:
    H = matrix(n,n)
    for i in range(n):
        for j in range(n): H[i,j] = mu[i+j]
    ev = [e.real for e in eighe(H, eigvals_only=True)]
    npos = sum(1 for e in ev if e > 1e-15*max(abs(x) for x in ev))
    nneg = sum(1 for e in ev if e < -1e-15*max(abs(x) for x in ev))
    print(f"  n={n}: inertia ({npos},{nneg})  q = {nneg}  eigs " +
          " ".join(nstr(e,4) for e in ev))
