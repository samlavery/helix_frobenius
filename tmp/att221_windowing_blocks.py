"""att221: SEAT CLOSURE, move 3 — the top/bottom windowing blocks, the last
uncomputed defect piece.

Contour dR_W of window W=(a,b) at height Y: top edge Im z = +Y traversed
right-to-left, bottom edge Im z = -Y left-to-right (positive orientation),
laterals already evaluated (att220, telescoping exact).

Top edge in s-coordinates: s = 1/2 - i z with z = x + iY  =>  s = (1/2 + Y) - i x,
Re s = 1/2 + Y > 1: the ABSOLUTELY CONVERGENT half-plane (prime data only).
Bottom edge is its functional-equation image.

Reported: the edge moments, the top/bottom relation, and the assembled
Hankel block's inertia (is the windowing defect sign-definite?)."""
from mpmath import mp, mpf, mpc, quad, matrix, eighe, nstr, zeta, diff, mangoldt

mp.dps = 25
Y = mpf('1.5')
A_, B_ = mpf('10'), mpf('30')

def xi(s):
    return (s*(s-1)/2) * mp.pi**(-s/2) * mp.gamma(s/2) * zeta(s)
def Afun(z):
    return xi(mpf(1)/2 - mpc(0,1)*z)
def dlogA(z):
    return diff(Afun, z)/Afun(z)

def edge_moment(k, sign):
    """(1/2pi i) int over horizontal edge at Im z = sign*Y, dz = dx,
    orientation: bottom (sign=-1) left->right, top (sign=+1) right->left."""
    f = lambda x: (mpc(x, sign*Y)**k) * dlogA(mpc(x, sign*Y))
    val = quad(f, [A_, (A_+B_)/2, B_]) / (2*mp.pi*mpc(0,1))
    return -val if sign > 0 else val   # top traversed right-to-left

print("windowing (top+bottom) edge moments, W=(10,30), Y=1.5:")
tot = []
for k in range(8):
    t = edge_moment(k, +1)
    b = edge_moment(k, -1)
    s = t + b
    tot.append(s)
    if k < 4:
        print(f"  k={k}: top {nstr(t.real,6):>12}  bottom {nstr(b.real,6):>12}"
              f"  sum {nstr(s.real,6):>12}  |Im sum| {nstr(abs(s.imag),2)}", flush=True)

print("\nassembled windowing-block Hankel inertia (n x n from these moments):")
for n in [2, 3, 4]:
    H = matrix(n, n)
    for i in range(n):
        for j in range(n):
            H[i, j] = tot[i+j].real
    ev = [e.real for e in eighe(H, eigvals_only=True)]
    npos = sum(1 for e in ev if e > 0); nneg = sum(1 for e in ev if e < 0)
    print(f"  n={n}: inertia ({npos},{nneg})  eigs " +
          " ".join(nstr(e,4) for e in ev), flush=True)

# cross-check: total contour moment = zero count in window (argument principle)
print("\nargument-principle cross-check (mu_0 should be the zero count):")
lat = lambda x, k: (quad(lambda y: (mpc(x,y)**k)*dlogA(mpc(x,y))*mpc(0,1),
                         [-Y,0,Y]) / (2*mp.pi*mpc(0,1)))
mu0 = tot[0] + lat(B_,0) - lat(A_,0)
print(f"  mu_0 = {nstr(mu0.real, 8)}  (zeros of zeta with 10 < gamma < 30: 4)")
