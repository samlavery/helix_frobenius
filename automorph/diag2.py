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
    if P in (QQ,ZZ) or P is QQ:
        c=QQ(a); return F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1
    m=P.zeta_order() if hasattr(P,'zeta_order') else P._n()  # cyclotomic order
    gred=F(r)**(12//m)
    s=F(0)
    for i,c in enumerate(a.list()):
        c=QQ(c); s+=F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1*gred**i
    return s

ells=[3,5,7,11,17]
exps={l:a_p_h_exponent(l) for l in ells}   # a_ell(g)=z12^{exps[l]}, None->0
print("target exps e_ell (a_ell=z12^e):",exps)
prim=[2,6,7,11]

def residual_search(charr, k, label):
    t=time.time()
    M=ModularSymbols(charr,k,sign=1); S=M.cuspidal_subspace()
    n=S.dimension()
    base=S.hecke_matrix(3).base_ring()
    print(f"[{label}] k={k} cuspdim={n} field={base}  build {time.time()-t:.0f}s",flush=True)
    Tk={}
    for l in ells:
        Tk[l]=S.hecke_matrix(l)
    for r in prim:
        V=None
        for l in ells:
            e=exps[l]
            tgt = F(0) if e is None else F(pow(r,e,13))
            Tl=Tk[l]; Tlb=matrix(F,[[rd(Tl[i,j],r) for j in range(n)] for i in range(n)])
            ker=(Tlb-tgt*identity_matrix(F,n)).right_kernel()
            V=ker if V is None else V.intersection(ker)
        print(f"   embedding z12->{r}: residual g-eigenspace dim = {V.dimension()}",flush=True)

# VALIDATION: 13 does not divide 124 -> clean reduction; expect companion present
residual_search(chi, 13, "VALIDATE lvl124 chi wt13")
