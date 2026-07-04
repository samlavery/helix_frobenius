# Extract e_ord(Phi) and its g_alpha* component via the eigenform basis.
# Method: U_p^K(Phi) for K past the non-ordinary transient = a combination of the 4 ordinary
# eigenforms {g_a,g_b,h'_a,h'_b}. Build those 4 as q-exps; solve U_p^K(Phi) = sum c_i e_i at
# enough indices; the g_alpha* reading is c_{g_alpha}-related. But U_p^K mixes via eigenvalues:
# U_p^K e_i = lambda_i^K e_i. So U_p^K Phi = sum c_i lambda_i^K e_i. To recover the g_alpha
# component c_{g_a}: use that lambda_{g_a}=alpha_g=1, so its contribution is c_{g_a} e_{g_a}
# (K-independent!). The others: beta_g=zeta3^2 (order 3 unit), h' eigenvalues. Take K a multiple
# of the eigenvalue orders * p^something so all lambda_i^K -> their stable values.
# SIMPLER: solve the small linear system. Build e_i, form the matrix [e_i coeffs], and for
# EACH K, U_p^K Phi = sum (c_i lambda_i^K) e_i. Solve for the coefficients d_i^K = c_i lambda_i^K
# at one K, then c_{g_a} = d_{g_a}^K / alpha_g^K = d_{g_a}^K (alpha_g=1).
import time
from rung3_krylov import (embedding, f_coeffs_int, h_coeffs_int, dinv_f_coeffs, phi_coeff, _solve_cols)
from rung3_lhs import a_p_h_exponent, _ind31_mod3
from rung3_rhs import Unramified, Qpf
p=13; prec=12; zeta,mod=embedding(p,prec)
def zk(k): return pow(zeta,k%12,mod)
def chi_exp(pp):
    i=_ind31_mod3(pp); return ((0 if pp%4==1 else 6)+4*i)%12
# Build the 4 ordinary eigenforms to q^Me. a_l for good l:
#  g_alpha: a_l(g)=conj(a_l(h))=zeta^{-k(l)}; a_13=alpha_g=1
#  g_beta:  same a_l for l!=13; a_13=beta_g=zeta3^2=zeta^8
#  h'_alpha: a_l(h')=conj a_l(h) with zeta->-zeta i.e. a_l(h') for the conjugate form.
#            h' has a_l = (zeta->-zeta applied to h's a_l). For a_l=zeta^{k}, conj-form a_l=(-1)^k zeta^k? 
#            No: replacing zeta by -zeta sends zeta^k -> (-1)^k zeta^k. So a_l(h')=(-1)^{k(l)} zeta^{k(l)}.
#            a_l(g'=h'*)=conj(a_l(h'))=(-1)^{k} zeta^{-k}.
Me=400
def build_eigenform(a13_exp, conj):
    a=[0]*Me; a[1]=1
    import sympy as sp
    for q in sp.primerange(2,Me):
        q=int(q)
        if q==13:
            aq=zk(a13_exp)  # U_13 eigenvalue
            chiq=0  # 13 | level after stabilization -> a_{13^e}=aq^e
        elif 124%q==0:
            aq=0; chiq=0
        else:
            kk=a_p_h_exponent(q)
            if kk is None: aq=0
            else:
                # a_l(g)=zeta^{-k}; conjugate form multiplies by (-1)^k and flips sign of exponent handled
                base = (-kk)%12  # conj(a_l(h))
                if conj: aq = ((-1)**kk) * zk((kk)%12)  # a_l(g') = (-1)^k zeta^{-k}... approx
                else: aq = zk(base)
                aq%=mod
            chiq=zk(chi_exp(q))
        qe=q; prev,cur=1,aq
        while qe<Me:
            a[qe]=cur%mod
            nxt=(aq*cur-(chiq if 124%q else 0)*prev)%mod
            prev,cur=cur,nxt; qe*=q
    # mult fill
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
t0=time.time()
ga=build_eigenform(0,False)   # g_alpha (a_13=1)
gb=build_eigenform(8,False)   # g_beta  (a_13=zeta3^2=zeta^8)
print(f'built eigenforms [{time.time()-t0:.0f}s]. g_alpha a_1..a_7:',ga[1:8])
print('g_beta a_1..a_7:',gb[1:8])
# Are g_alpha, g_beta independent as q-exps? (differ only at 13-power indices)
print('differ at index 13:',ga[13],'vs',gb[13])
