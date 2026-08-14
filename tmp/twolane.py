"""Two-lane MATRIX pencil, verbatim from GeometricPhasorClosure.lean.

  B = fromBlocks(Qp^H Qp, 0, 0, Qm^H Qm)                     block-diagonal metric
  A = fromBlocks(heightA(Qp), C, C^H, heightA(Qm)),  C = Qp^H diag(cell) Qm
  cell n = exp(i*pi*n/3),  heightA(Q) = Q^H diag(Z_n) Q,  Z_n = n
The coupling C carries chi(n)*conj(chi(m)) ACROSS lanes -- signs are NOT squared away.
Lanes must DIFFER or C degenerates to the one-lane case.
"""
import numpy as np, mpmath as mp
rng = np.random.default_rng(20260812)

def wts(N):
    n = np.arange(1, N+1, dtype=float)
    return n, n**(-0.5)*np.exp(-n/N)

def feat(chifn, N, m, cells):
    """columns = (residue r in `cells`) x (moment k<m)"""
    n, w = wts(N)
    c = np.array([chifn(int(k)) for k in n])
    Q = np.zeros((N, len(cells)*m), dtype=complex)
    for j, r in enumerate(cells):
        ind = ((n.astype(int) % 6) == r).astype(float)
        for k in range(m):
            Q[:, j*m+k] = ind*c*np.sqrt(w)*(n/N)**k
    return Q

def two_lane(chifn, N, m, cellsP, cellsM):
    n, _ = wts(N)
    Qp, Qm = feat(chifn,N,m,cellsP), feat(chifn,N,m,cellsM)
    cell = np.exp(1j*np.pi*n/3.0)
    Ap = Qp.conj().T @ (n[:,None]*Qp)
    Am = Qm.conj().T @ (n[:,None]*Qm)
    C  = Qp.conj().T @ (cell[:,None]*Qm)
    A = np.block([[Ap, C],[C.conj().T, Am]])
    B = np.block([[Qp.conj().T@Qp, np.zeros((Qp.shape[1],Qm.shape[1]))],
                  [np.zeros((Qm.shape[1],Qp.shape[1])), Qm.conj().T@Qm]])
    return A, B

def eigh_gen(A,B,tol=1e-10):
    wB,V = np.linalg.eigh(B); keep = wB > tol*max(wB.max(),1)
    T = V[:,keep]@np.diag(1/np.sqrt(wB[keep]))
    M = T.conj().T@A@T; M=(M+M.conj().T)/2
    return np.sort(np.linalg.eigvalsh(M)), keep.sum()

chi3  = lambda n: 1.0 if n%3==1 else (-1.0 if n%3==2 else 0.0)
triv  = lambda n: 1.0
def randc(seed):
    p = np.random.default_rng(seed).choice([-1.0,1.0],6); return lambda n: p[n%6]

# lanes: positive residues {1,2} vs negative {4,5} -- the antipodal split across the wall
CP, CM = [1,2], [4,5]
print("=== TWO-LANE pencil, lanes = residues {1,2} vs {4,5} (antipodal across wall) ===")
for label, cf in [("trivial",triv),("chi3",chi3),("rand-A",randc(1)),("rand-B",randc(2))]:
    for (N,m) in [(600,3),(2000,3)]:
        Z,rk = eigh_gen(*two_lane(cf,N,m,CP,CM))
        pos = Z[Z>1e-9]
        print(f"  {label:8s} N={N:5d} m={m} rank={rk:2d}  Z = " + " ".join(f"{z:.4f}" for z in pos[:6]))
