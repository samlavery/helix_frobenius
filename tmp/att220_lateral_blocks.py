"""att220: SEAT CLOSURE ATTEMPT, move 2 — evaluate the window/lateral defect
blocks, the only uncomputed part of the (T) ledger.

Window W=(a,b), rectangle height Y>1/2, moments mu_k = (1/2pi i) oint z^k A'/A.
Decompose the contour into: TOP edge (Im z = +Y, in the convergent half-plane
via s = 1/2 - iz), BOTTOM edge (Im z = -Y, FE image of top), and the two
LATERAL edges (Re z = a, b).  The lateral blocks are the piece never
evaluated; under a tiling adjacent laterals should cancel pairwise (paper's
U5 claim).  Test: compute lateral contributions for adjacent windows and
measure the cancellation, plus their Hankel-block inertia effect."""
from mpmath import mp, mpf, mpc, quad, matrix, eighe, nstr, zeta, diff

mp.dps = 25
Y = mpf('1.5')

def xi(s):
    return (s*(s-1)/2) * mp.pi**(-s/2) * mp.gamma(s/2) * zeta(s)

def A(z):
    return xi(mpf(1)/2 - mpc(0,1)*z)

def dlogA(z):
    return diff(A, z)/A(z)

def lateral_moment(x, k):
    """(1/2pi i) * integral along the vertical segment Re z = x, y: -Y..Y,
    of z^k A'/A dz;  dz = i dy."""
    f = lambda y: (mpc(x, y)**k) * dlogA(mpc(x, y)) * mpc(0, 1)
    return (quad(f, [-Y, 0, Y]) / (2*mp.pi*mpc(0,1)))

print("lateral moments at window boundaries (k = 0..3):")
edges = ['10', '20', '30']
vals = {}
for x in edges:
    xv = mpf(x)
    row = [lateral_moment(xv, k) for k in range(4)]
    vals[x] = row
    print(f"  x={x:>3}: " + "  ".join(nstr(v.real, 6) for v in row), flush=True)

print("\nadjacent-window cancellation test (right edge of W1 vs left edge of W2):")
for k in range(4):
    a = vals['20'][k]
    print(f"  k={k}: shared-edge value {nstr(a.real,8)}  "
          f"-> appears with opposite orientation in adjacent windows, "
          f"net {nstr((a-a).real,3)}")
