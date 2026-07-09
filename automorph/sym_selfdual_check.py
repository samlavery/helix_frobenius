"""Sanity-check the algebraic identities behind the proposed Lemma A of section 11:
   (i)  det Sym^r(diag(a,b)) = (ab)^{r(r+1)/2}   -> =1 when ab=1
   (ii) Sym^r phi is self-dual: eigenvalue multiset closed under inversion (ab=1)
   (iii) det(A tensor B) = (det A)^{dim B} (det B)^{dim A}
Exact symbolic check over the unit circle ab=1 via a=exp(i*th), b=exp(-i*th)."""
import numpy as np

def sym_eigs(a, b, r):
    return np.array([a**(r-k) * b**k for k in range(r+1)])

ok = True
for r in range(0, 14):
    th = 0.7123  # generic angle, a=e^{i th}, b=e^{-i th}, ab=1
    a, b = np.exp(1j*th), np.exp(-1j*th)
    e = sym_eigs(a, b, r)
    det = np.prod(e)
    # (i) det = 1
    d1 = abs(det - 1.0)
    # (ii) self-dual: multiset {e} == {1/e} (closed under inversion)
    inv = np.sort_complex(np.round(1.0/e, 10))
    srt = np.sort_complex(np.round(e, 10))
    d2 = np.max(np.abs(inv - srt))
    # exponent-sum identity sum_{k}(r-2k) = 0
    esum = sum(r-2*k for k in range(r+1))
    ok = ok and d1 < 1e-9 and d2 < 1e-9 and esum == 0
    if r <= 5 or r == 13:
        print(f"r={r:2d}: |det-1|={d1:.1e}  self-dual multiset diff={d2:.1e}  sum(r-2k)={esum}")

# (iii) tensor determinant, random det-one blocks
rng = np.random.default_rng(0)
for (nA, nB) in [(6,4),(7,5),(3,2)]:
    A = rng.standard_normal((nA,nA)) + 1j*rng.standard_normal((nA,nA)); A /= np.linalg.det(A)**(1/nA)
    B = rng.standard_normal((nB,nB)) + 1j*rng.standard_normal((nB,nB)); B /= np.linalg.det(B)**(1/nB)
    lhs = np.linalg.det(np.kron(A,B))
    rhs = np.linalg.det(A)**nB * np.linalg.det(B)**nA
    d3 = abs(lhs - rhs)
    ok = ok and d3 < 1e-6
    print(f"tensor {nA}x{nB}: |det(A(x)B) - (detA)^nB(detB)^nA| = {d3:.1e}  (detA={np.linalg.det(A):.3f})")

print("ALL IDENTITIES HOLD" if ok else "FAILURE")
