from sage.all import *
import sys, time
sys.path.insert(0,'.')
from rung3_lhs import _IND31, a_p_h_exponent

K=CyclotomicField(12); z12=K.gen()
F=GF(13)
def rd_r(a,r):
    v=a.list(); s=F(0)
    for i,c in enumerate(v):
        c=QQ(c); s+=F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1*F(r)**i
    return s
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

# in-house exponents e_ell (a_ell(g)=z12^{e_ell}); None -> 0
ells=[3,5,7,11,17,19]
exps={l:a_p_h_exponent(l) for l in ells}
prim_embeds=[2,6,7,11]   # z12 -> r, primitive 12th roots mod 13
k=3
for label,charr in [("chi*om^2", chi.extend(1612)*om.extend(1612)**(k-1)),
                    ("chi*om^-2", chi.extend(1612)*om.extend(1612)**(-(k-1)))]:
    t=time.time()
    M=ModularSymbols(charr,k,sign=1); S=M.cuspidal_subspace()
    T3=S.hecke_matrix(3); n=T3.nrows()
    print(f"[{label}] cuspdim={n}  build+T3 {time.time()-t:.0f}s")
    # eigenvalue multiset of T3 mod13 for r=7 reduction
    T3b=matrix(F,[[rd_r(T3[i,j],7) for j in range(n)] for i in range(n)])
    cp=T3b.charpoly()
    roots=cp.roots()
    print(f"  T3 mod13 (r=7) roots (val,mult):",[(int(a),m) for a,m in roots])
    hit=[r for r in prim_embeds if (T3b-F(r)*identity_matrix(F,n)).right_kernel().dimension()>0]
    print(f"  primitive-12th-root eigenvalues present among {{2,6,7,11}}: {hit}")
    # if any embedding r present, run full intersection for that r
    for r in (hit or []):
        # need more T_ell
        V=(T3b-F(pow(r,exps[3],13))*identity_matrix(F,n)).right_kernel()
        for l in [5,7,11]:
            if exps[l] is None: continue
            Tl=S.hecke_matrix(l); Tlb=matrix(F,[[rd_r(Tl[i,j],r) for j in range(n)] for i in range(n)])
            V=V.intersection((Tlb-F(pow(r,exps[l],13))*identity_matrix(F,n)).right_kernel())
        print(f"  >>> embedding r={r}: residual eigenspace dim (T3,5,7,11) = {V.dimension()}")
    sys.stdout.flush()
