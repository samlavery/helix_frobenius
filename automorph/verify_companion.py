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
G13=DirichletGroup(13,K); om=[c for c in G13 if all(c(n)==z12**dlog7(n) for n in range(1,13))][0]
def rd(a, r):
    P=a.parent()
    try:
        c=QQ(a); return F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1
    except (TypeError,ValueError): pass
    m=int(P._n()); gred=F(r)**(12//m); s=F(0)
    for i,c in enumerate(a.list()):
        c=QQ(c); s+=F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1*gred**i
    return s
good=[3,5,7,11,17,19,23,29,37,41,43,47,53,59]
exps={l:a_p_h_exponent(l) for l in good}
k=3; r=7
# companion residual target tau_ell = a_ell(g)*ell^{k-1} = 7^{e}*ell^2  (g tensor om^{k-1})
def tau(l):
    e=exps[l]
    if e is None: return F(0)
    return F(pow(r,e,13))*F(pow(l,k-1,13))
charr=chi.extend(1612)*om.extend(1612)**(k-1)
t=time.time()
M=ModularSymbols(charr,k,sign=1); S=M.cuspidal_subspace(); n=S.dimension()
print(f"S_3(1612,chi*om^2) cuspdim={n} [{time.time()-t:.0f}s]",flush=True)
V=None; perp={}
for l in good:
    Tl=S.hecke_matrix(l); Tlb=matrix(F,[[rd(Tl[i,j],r) for j in range(n)] for i in range(n)])
    ker=(Tlb-tau(l)*identity_matrix(F,n)).right_kernel()
    perp[l]=ker.dimension()
    V=ker if V is None else V.intersection(ker)
    print(f"  ell={l}: target tau={int(tau(l))} ker_dim={perp[l]} running_intersect={V.dimension()}  [{time.time()-t:.0f}s]",flush=True)
print(f"\nCOMPANION residual eigenspace dim (g tensor om^{k-1}, {len(good)} primes) = {V.dimension()}",flush=True)
if V.dimension()>0:
    U=S.hecke_matrix(13); Ub=matrix(F,[[rd(U[i,j],r) for j in range(n)] for i in range(n)])
    B=V.basis_matrix(); d=V.dimension()
    # matrix of Ub on V using pivot columns of B
    piv=B.pivots()
    Bp=B.matrix_from_columns(piv)
    MU=(B*Ub).matrix_from_columns(piv)*Bp.inverse()
    print("U_13 char/eigen on companion eigenspace:",flush=True)
    print("  U_13 |_V eigenvalues (mod13):",MU.eigenvalues(),flush=True)
    print("  U_13 |_V charpoly:",MU.charpoly().factor(),flush=True)
    # also T at 2 and 31 (bad primes) residues
    for bp in (2,31):
        Tb2=S.hecke_matrix(bp); Tb2b=matrix(F,[[rd(Tb2[i,j],r) for j in range(n)] for i in range(n)])
        M2=(B*Tb2b).matrix_from_columns(piv)*Bp.inverse()
        print(f"  U_{bp}|_V eigenvalues (mod13):",M2.eigenvalues(),flush=True)
