from sage.all import *
import sys, time
sys.path.insert(0,'.')
from rung3_lhs import _IND31

K=CyclotomicField(12); z12=K.gen()
# prime P above 13 with z12 -> 7
Pgood=None
for P in K.primes_above(13):
    Fq=P.residue_field()
    if Fq(z12)==Fq(7):
        Pgood=P; FQ=Fq; break
assert Pgood is not None
print("residue field:",FQ," z12->",FQ(z12))
def rd(a):
    return FQ(a)
def dlog7(n):
    n%=13
    for e in range(12):
        if pow(7,e,13)==n: return e
def chi_target(n):
    n=int(n)%124
    if n%2==0 or n%31==0: return None
    return z12**((6*(1 if n%4==3 else 0)+8*(_IND31[n%31]%3))%12)
G124=DirichletGroup(124,K); chi=[c for c in G124 if all(c(n)==chi_target(n) for n in range(1,124) if gcd(n,124)==1)][0]
G13=DirichletGroup(13,K); om=[c for c in G13 if all(c(n)==z12**dlog7(n) for n in range(1,13))][0]
target={3:7,5:3,7:6,11:11,17:4,19:6,37:9,41:3,43:6,53:3,59:7}
k=3
psi=(chi.extend(1612)*om.extend(1612)**(k-1))
t=time.time()
M=ModularSymbols(psi,k,sign=1)
S=M.cuspidal_subspace()
print(f"modsym cuspidal dim (sign=1): {S.dimension()}  [{time.time()-t:.1f}s]")

def redmat(A):
    n=A.nrows()
    return matrix(FQ,[[rd(A[i,j]) for j in range(A.ncols())] for i in range(n)])
V=None
for ell in [3,5,7,11,17]:
    t=time.time()
    T=S.hecke_matrix(ell)
    Tb=redmat(T); n=Tb.nrows()
    ker=(Tb-FQ(target[ell])*identity_matrix(FQ,n)).right_kernel()
    V=ker if V is None else V.intersection(ker)
    print(f"  ell={ell}: ker dim={ker.dimension()}, running intersect dim={V.dimension()}  [{time.time()-t:.1f}s]")
print("RESIDUAL EIGENSPACE dim (mod 13):",V.dimension())
