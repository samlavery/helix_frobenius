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
    except (TypeError,ValueError):
        pass
    m=P._n() if hasattr(P,'_n') else P.zeta_order()
    m=int(m); gred=F(r)**(12//m); s=F(0)
    for i,c in enumerate(a.list()):
        c=QQ(c); s+=F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1*gred**i
    return s

ells=[3,5,7,11,17]
exps={l:a_p_h_exponent(l) for l in ells}
prim=[2,6,7,11]
print("in-house target: a_ell(g)=z12^e, e=",exps,flush=True)

k=3
for sgn,label in [(1,"chi*om^(k-1)=chi*om^2"),(-1,"chi*om^-(k-1)=chi*om^-2")]:
    charr=chi.extend(1612)*om.extend(1612)**(sgn*(k-1))
    t=time.time()
    M=ModularSymbols(charr,k,sign=1); S=M.cuspidal_subspace(); n=S.dimension()
    fld=S.hecke_matrix(3).base_ring()
    print(f"\n=== {label}  cuspdim={n} field={fld}  [{time.time()-t:.0f}s]",flush=True)
    # self-validate rd on character values: (chi*om^{sgn*2})(x) reduced == family residue chi(x)*x^{sgn*2}
    # (informational)
    Tk={l:S.hecke_matrix(l) for l in ells}
    print(f"    hecke matrices computed [{time.time()-t:.0f}s]",flush=True)
    Tred={}  # (l,r)->matrix over F
    for l in ells:
        for r in prim:
            Tred[(l,r)]=matrix(F,[[rd(Tk[l][i,j],r) for j in range(n)] for i in range(n)])
    for r in prim:
        V=None
        for l in ells:
            e=exps[l]; tgt=F(0) if e is None else F(pow(r,e,13))
            ker=(Tred[(l,r)]-tgt*identity_matrix(F,n)).right_kernel()
            V=ker if V is None else V.intersection(ker)
        d=V.dimension()
        print(f"    embedding z12->{r}: g-residual eigenspace dim = {d}",flush=True)
        if d>0:
            # read U_13 residue on V: U_13 = hecke at 13
            U13=S.hecke_matrix(13); U13b=matrix(F,[[rd(U13[i,j],r) for j in range(n)] for i in range(n)])
            # restrict U13b to V (invariant since Hecke commute); get eigenvalues on V
            B=V.basis_matrix()  # d x n
            # solve U13b acts on V: coords
            sol=B.solve_left(B*U13b) if False else None
            # compute matrix of U13b on V: find M with M*B = B*U13b
            MU=B*U13b*B.transpose()*(B*B.transpose())**-1
            evs=MU.eigenvalues()
            print(f"      >>> U_13 residues on V: {evs}  (unit<=>nonzero; target root of unity res {{1, zeta3=9}})",flush=True)
