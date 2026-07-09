from sage.all import *
F=GF(13)
def rd(a,r=None):  # rational or cyclotomic reduce; level-26 forms are rational so trivial
    try:
        c=QQ(a); return F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1
    except (TypeError,ValueError):
        pass
    m=int(a.parent()._n()); g=F(2)**(12//m); s=F(0)   # dummy embedding (rational here)
    for i,c in enumerate(a.list()):
        c=QQ(c); s+=F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1*g**i
    return s
# 13-NEW newforms of level 26 (13 | 26): 26a,26b elliptic curves
for lab in ('26a','26b'):
    E=EllipticCurve(lab); an=E.anlist(60)
    print(lab,"a_ell:", {l:an[l] for l in (3,5,7,11,17,19,23)})
M=ModularSymbols(26,2,sign=1); S=M.cuspidal_subspace(); n=S.dimension()
print("S_2(26) cuspdim (sign=1) =",n)
good=[3,5,7,11,17,19,23]
for lab in ('26a','26b'):
    an=EllipticCurve(lab).anlist(60)
    V=None; per={}
    for l in good:
        Tl=S.hecke_matrix(l); Tlb=matrix(F,[[rd(Tl[i,j]) for j in range(n)] for i in range(n)])
        ker=(Tlb-F(an[l])*identity_matrix(F,n)).right_kernel()
        per[l]=ker.dimension(); V=ker if V is None else V.intersection(ker)
    print(f"  {lab}: per-ell {per} -> common eigenspace dim = {V.dimension()}  "
          f"[{'METHOD FINDS 13-NEW FORM' if V.dimension()>0 else 'METHOD MISSES IT (13-new blind spot!)'}]")
    if V.dimension()>0:
        U=S.hecke_matrix(13); Ub=matrix(F,[[rd(U[i,j]) for j in range(n)] for i in range(n)])
        B=V.basis_matrix(); piv=B.pivots(); Bp=B.matrix_from_columns(piv)
        MU=(B*Ub).matrix_from_columns(piv)*Bp.inverse()
        print(f"     U_13 eigenvalues on eigenspace mod13: {MU.eigenvalues()} (a_13({lab})={EllipticCurve(lab).anlist(20)[13]})")
