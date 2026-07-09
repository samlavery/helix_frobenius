from sage.all import *
import sys, time
sys.path.insert(0,'.')
from rung3_lhs import _IND31, a_p_h_exponent

K=CyclotomicField(12); z12=K.gen(); F=GF(13)
def dlog7(n):
    n%=13
    for e in range(12):
        if pow(7,e,13)==n: return e
def chi_target(n):
    n=int(n)%124
    if n%2==0 or n%31==0: return None
    return z12**((6*(1 if n%4==3 else 0)+8*(_IND31[n%31]%3))%12)
G124=DirichletGroup(124,K); chi=[c for c in G124 if all(c(n)==chi_target(n) for n in range(1,124) if gcd(n,124)==1)][0]
def rd(a, r):
    P=a.parent()
    try:
        c=QQ(a); return F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1
    except (TypeError,ValueError): pass
    m=int(P._n()); gred=F(r)**(12//m); s=F(0)
    for i,c in enumerate(a.list()):
        c=QQ(c); s+=F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1*gred**i
    return s
good=[3,5,7,11,17,19,23,29,37,41,43]
exps={l:a_p_h_exponent(l) for l in good}
prim=[2,6,7,11]
k=3; tw=1   # half Tate twist t=(k-1)/2
charr=chi.extend(1612)     # nebentype chi (cond 124) at level 1612
t=time.time()
M=ModularSymbols(charr,k,sign=1); S=M.cuspidal_subspace(); n=S.dimension()
print(f"S_3(1612, chi[cond124]) cuspdim={n} field={S.hecke_matrix(3).base_ring()} [{time.time()-t:.0f}s]",flush=True)
Tk={l:S.hecke_matrix(l) for l in good}
print(f"hecke done [{time.time()-t:.0f}s]",flush=True)
for r in prim:
    V=None; per={}
    for l in good:
        e=exps[l]
        tgt=F(0) if e is None else F(pow(r,e,13))*F(pow(l,tw,13))   # a_ell(g)*ell^{t}
        Tlb=matrix(F,[[rd(Tk[l][i,j],r) for j in range(n)] for i in range(n)])
        ker=(Tlb-tgt*identity_matrix(F,n)).right_kernel()
        per[l]=ker.dimension(); V=ker if V is None else V.intersection(ker)
    print(f"[r={r}] t=1 per-ell {per} -> eigenspace dim = {V.dimension()}",flush=True)
    if V.dimension()>0:
        U=S.hecke_matrix(13); Ub=matrix(F,[[rd(U[i,j],r) for j in range(n)] for i in range(n)])
        B=V.basis_matrix(); piv=B.pivots(); Bp=B.matrix_from_columns(piv)
        MU=(B*Ub).matrix_from_columns(piv)*Bp.inverse()
        print(f"   >>> U_13 eigenvalues on V mod13: {MU.eigenvalues()}",flush=True)
