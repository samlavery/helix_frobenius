"""Helix pencil calibration, built verbatim from GeometricPhasorClosure.lean.

  helixWeight N n = n^(-1/2) * exp(-n/N)          (Abel-grown, mass from 0)
  heightAtom n    = n                              (NO log)
  Q[i,(r,k)]      = 1{(i+1)%6==r} * chi(i+1) * sqrt(w) * ((n/N)^k)
  B = Q^H Q ,  A = Q^H diag(Z_n) Q ,  Z_n = n
  eigenheights: det(A - Z B) = 0 ; then analytic height t = log Z
TEST 1  do the log Z track zeta/L zero ordinates?
TEST 2  VACUITY CONTROL: does swapping the character move the eigenheights?
"""
import numpy as np, mpmath as mp
np.set_printoptions(precision=5, suppress=True)

def chi_triv(n, q=1):  return 1.0
def chi3(n, q=3):
    r = n % 3
    return 1.0 if r == 1 else (-1.0 if r == 2 else 0.0)
def chi4(n, q=4):      # the other natural quadratic char, mod 4
    r = n % 4
    return 1.0 if r == 1 else (-1.0 if r == 3 else 0.0)

def build(chifn, N, m):
    n = np.arange(1, N+1, dtype=float)
    w = n**(-0.5) * np.exp(-n/N)
    c = np.array([chifn(int(k)) for k in n])
    Q = np.zeros((N, 6*m), dtype=complex)
    for r in range(6):
        ind = ((n.astype(int) % 6) == r).astype(float)
        for k in range(m):
            Q[:, r*m+k] = ind * c * np.sqrt(w) * (n/N)**k
    B = Q.conj().T @ Q
    A = Q.conj().T @ (n[:, None] * Q)
    return A, B

def eigenheights(A, B, tol=1e-10):
    # generalized Hermitian problem; drop numerically-null metric directions
    wB, V = np.linalg.eigh(B)
    keep = wB > tol*max(wB.max(), 1)
    Vk = V[:, keep]; Wk = wB[keep]
    Binv = Vk @ np.diag(1/np.sqrt(Wk))
    M = Binv.conj().T @ A @ Binv
    M = (M + M.conj().T)/2
    return np.sort(np.linalg.eigvalsh(M)), keep.sum()

zz = [float(mp.im(mp.zetazero(k))) for k in range(1, 9)]
print("first zeta zero ordinates:", " ".join(f"{g:.4f}" for g in zz))

for name, cf in [("trivial(zeta)", chi_triv), ("chi3", chi3), ("chi4", chi4)]:
    print(f"\n=== {name} ===")
    for (N, m) in [(600, 3), (600, 5), (2000, 5)]:
        Z, rk = build(cf, N, m)
        Zs, keep = eigenheights(*build(cf, N, m))
        pos = Zs[Zs > 1e-9]
        print(f"  N={N:5d} m={m}  rank={keep:2d}  eigenheights Z = " +
              " ".join(f"{z:.4g}" for z in pos[:8]))
        print(f"{'':22s}  log Z          = " +
              " ".join(f"{np.log(z):.4f}" for z in pos[:8] if z > 0))

print("\n=== VACUITY CONTROL: random sign patterns vs real characters ===")
rng = np.random.default_rng(20260812)
def rand_char(seed):
    pat = rng.choice([-1.0,1.0], size=6)
    return lambda n: pat[n % 6]
for label, cf in [("chi3", chi3), ("rand-A", rand_char(1)), ("rand-B", rand_char(2)),
                  ("all-ones", lambda n: 1.0)]:
    Zs, keep = eigenheights(*build(cf, 600, 3))
    pos = Zs[Zs > 1e-9]
    print(f"  {label:9s} rank={keep:2d}  Z = " + " ".join(f"{z:.4f}" for z in pos[:6]))
print("\n=== N-scaling of the first eigenheight (trivial, m=3) ===")
for N in (300, 600, 1200, 2400):
    Zs,_ = eigenheights(*build(chi_triv, N, 3)); pos = Zs[Zs>1e-9]
    print(f"  N={N:5d}  Z1={pos[0]:.4f}   Z1/N={pos[0]/N:.6f}   log Z1={np.log(pos[0]):.4f}")
