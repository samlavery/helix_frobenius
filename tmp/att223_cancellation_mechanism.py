"""att223: SEAT CLOSURE move 4 — is the windowing/lateral cancellation an
IDENTITY (blind, cannot detect) or the DETECTOR (breaks on off-line mass)?

Positive control: real A (all zeros on-line) -> assembled inertia (m,0).
Adversarial control: multiply A by a factor with an OFF-LINE conjugate pair
inside the window, B(z) = A(z)*(z-w)(z-wbar) with w = x0 + i y0, y0 != 0.
Then A'/A -> A'/A + 1/(z-w) + 1/(z-wbar), and the census MUST report q=1.
If the assembled Hankel stays PSD, the cancellation is blind (fatal for the
route).  If n_- becomes 1, the mechanism is the detector and the closure
argument has a real target."""
from mpmath import mp, mpf, mpc, quad, matrix, eighe, nstr, zeta, diff

mp.dps = 25
Y = mpf('1.5'); A_, B_ = mpf('10'), mpf('30')
def xi(s): return (s*(s-1)/2) * mp.pi**(-s/2) * mp.gamma(s/2) * zeta(s)
def Afun(z): return xi(mpf(1)/2 - mpc(0,1)*z)
def dlogA(z): return diff(Afun, z)/Afun(z)

W0 = mpc(mpf('18'), mpf('0.30'))       # planted off-line pair (inside window)
def dlogB(z):
    return dlogA(z) + 1/(z - W0) + 1/(z - W0.conjugate())

def moments(dlog, kmax=10):
    def horiz(k, sign):
        f = lambda x: (mpc(x, sign*Y)**k) * dlog(mpc(x, sign*Y))
        v = quad(f, [A_, (A_+B_)/2, B_]) / (2*mp.pi*mpc(0,1))
        return -v if sign > 0 else v
    def lat(x, k):
        return quad(lambda y: (mpc(x,y)**k)*dlog(mpc(x,y))*mpc(0,1),
                    [-Y,0,Y]) / (2*mp.pi*mpc(0,1))
    out = []
    for k in range(kmax):
        wind = horiz(k,+1) + horiz(k,-1)
        late = lat(B_,k) - lat(A_,k)
        out.append((wind.real, late.real, (wind+late).real))
    return out

def inertia(mu, n):
    H = matrix(n,n)
    for i in range(n):
        for j in range(n): H[i,j] = mu[i+j]
    ev = [e.real for e in eighe(H, eigvals_only=True)]
    sc = max(abs(e) for e in ev)
    return (sum(1 for e in ev if e > 1e-15*sc),
            sum(1 for e in ev if e < -1e-15*sc), min(ev))

for label, dl in [("POSITIVE CONTROL (true A)", dlogA),
                  ("ADVERSARIAL (planted off-line pair at 18+0.30i)", dlogB)]:
    m = moments(dl)
    tot = [t for _,_,t in m]
    print(f"\n{label}")
    print(f"  mu_0 = {nstr(tot[0],8)}   (expect 3 vs 5)")
    print(f"  windowing block inertia n=3: {inertia([w for w,_,_ in m],3)[:2]}")
    print(f"  lateral   block inertia n=3: {inertia([l for _,l,_ in m],3)[:2]}")
    for n in [3,4]:
        p,q,mn = inertia(tot,n)
        print(f"  ASSEMBLED n={n}: inertia ({p},{q})  q={q}  min-eig {nstr(mn,4)}")
