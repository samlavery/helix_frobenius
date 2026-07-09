# g_alpha*-component extraction via eigenform basis, matching at GOOD indices coprime to
# level 124*13 = 1612 (i.e. coprime to 2,31,13). Then bad-prime coeffs never enter.
import time, sympy as sp
from rung3_krylov import embedding, f_coeffs_int, h_coeffs_int, dinv_f_coeffs, phi_coeff, _solve_cols
from rung3_lhs import a_p_h_exponent, _ind31_mod3
from rung3_rhs import Unramified, Qpf
p=13; prec=12; zeta,mod=embedding(p,prec)
def zk(k): return pow(zeta,k%12,mod)
def chi_exp(pp):
    i=_ind31_mod3(pp); return ((0 if pp%4==1 else 6)+4*i)%12
# 4 ordinary eigenforms. a_l (good l, l != 2,13,31):
#   g_alpha, g_beta: a_l(g)=conj(a_l(h))=zeta^{-k(l)}   [g=h* twist]
#   h'_alpha,h'_beta: a_l(g')=conj(a_l(h'))=(-1)^{k(l)} zeta^{-k(l)}   [h'=zeta->-zeta of h]
# They differ at 13 only by the U_13 eigenvalue. At GOOD l (l!=2,13,31) g_alpha=g_beta and
# h'_alpha=h'_beta as far as a_l goes -- they ONLY differ at 13-power indices. So to separate
# the 4, I MUST use 13-power indices (U_13 acts) -- but those are the depth again.
# RESOLUTION: I don't need all 4 separated by q-coeffs. e_ord(Phi) = G := U_p^K Phi (K past
# transient) is IN the span. I want its g_alpha*-component = the a_1-dual reading. Since
# g_alpha and g_beta have IDENTICAL a_l at good l, and I read at good indices, I can only get
# the (g_alpha+g_beta)-combined coordinate and the (h'_a+h'_b)-combined coordinate. To split
# g_alpha from g_beta I apply the U_13-annihilator (U_13 - beta_g)/(alpha_g-beta_g) to G.
# G is already ordinary (=e_ord Phi), so (U_13 - beta_g)/(alpha_g-beta_g) picks the alpha_g line.
# G_n for n coprime to 13: (U_13 G)_n = G_{13n}. So I need G at 13n too -> ONE more 13-factor.
# G = U_p^K Phi needs Phi at 13^K * (indices). K past transient ~ 2-3. Plus the annihilator's
# U_13 -> 13^{K+1}. Manageable at K=3: 13^4 * small.
Me=200  # eigenform q-length (good indices up to ~200)
def build_ef(conj):
    a=[0]*Me; a[1]=1
    for q in sp.primerange(2,Me):
        q=int(q)
        if q in (2,13,31) or 124%q==0:
            aq=0; chiq=0
        else:
            kk=a_p_h_exponent(q)
            if kk is None: aq=0
            else:
                ex=(-kk)%12
                aq = (zk(ex)*((-1)**kk if conj else 1))%mod
            chiq=zk(chi_exp(q))
        qe=q; prev,cur=1,aq
        while qe<Me:
            a[qe]=cur%mod; nxt=(aq*cur-(chiq if q not in(2,13,31) and 124%q else 0)*prev)%mod
            prev,cur=cur,nxt; qe*=q
    spf=list(range(Me));i=2
    while i*i<Me:
        if spf[i]==i:
            for j in range(i*i,Me,i):
                if spf[j]==j:spf[j]=i
        i+=1
    for n in range(2,Me):
        pp=spf[n];e,t=0,n
        while t%pp==0:t//=pp;e+=1
        pe=pp**e;m=n//pe
        if m!=1:a[n]=(a[pe]*a[m])%mod
    return a
gstar=build_ef(False)   # g-type ordinary eigenform (a_l at good l); g_alpha* twist handled at readout
hpstar=build_ef(True)   # h'-type
# good indices coprime to 1612 for matching:
goodidx=[n for n in range(1,Me) if sp.gcd(n,1612)==1][:10]
print('good match indices (coprime to 1612):',goodidx)
print('gstar at these:',[gstar[n] for n in goodidx][:5])
print('hpstar at these:',[hpstar[n] for n in goodidx][:5])
# are gstar,hpstar independent at good indices?
U=Unramified(p,[0,1],prec)
def col(arr): return [Qpf.from_U(U,U.from_int_vec([arr[n]%mod])) for n in goodidx]
indep = _solve_cols([col(gstar)], col(hpstar), U) is None
print('gstar, hpstar independent at good indices:',indep)
