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
ells=[3,5,7,11]
exps={l:a_p_h_exponent(l) for l in ells}   # a_ell(g)=z12^{e}
prim=[2,6,7,11]
k=3
charr=chi.extend(1612)*om.extend(1612)**(k-1)   # chi*om^2 (Hida-pinned)
t=time.time()
M=ModularSymbols(charr,k,sign=1); S=M.cuspidal_subspace(); n=S.dimension()
print(f"S_3(1612,chi*om^2) cuspdim={n} [{time.time()-t:.0f}s]",flush=True)
Tk={l:S.hecke_matrix(l) for l in ells}
print(f"hecke done [{time.time()-t:.0f}s]",flush=True)
for r in prim:
    Tred={l:matrix(F,[[rd(Tk[l][i,j],r) for j in range(n)] for i in range(n)]) for l in ells}
    # per-ell g-target presence
    perell={l:(Tred[l]-F(pow(r,exps[l],13))*identity_matrix(F,n)).right_kernel().dimension() for l in ells}
    print(f"[r={r}] per-ell ker(T_l - g_target) dims: {perell}",flush=True)
    # twist scan: g⊗om^j has a_ell = z12^{e}·ell^j ; target_ell(r,j)=r^{e}·ell^j mod13
    for j in range(12):
        V=None
        for l in ells:
            tgt=F(pow(r,exps[l],13))*F(pow(l,j,13))
            ker=(Tred[l]-tgt*identity_matrix(F,n)).right_kernel()
            V=ker if V is None else V.intersection(ker)
        if V.dimension()>0:
            print(f"    >>> TWIST j={j} (g⊗om^{j}) present: dim={V.dimension()}",flush=True)
print("scan done",flush=True)
