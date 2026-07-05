from sage.all import *
import sys, time
sys.path.insert(0,'.')
from rung3_lhs import _IND31, a_p_h_exponent
from hida_family import chi_exp

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
good=[3,5,7,11,17,19,37,41,43]
# g twist-invariant signature s_ell(g)=a_ell(g)^2/chi(ell)=z12^{2e-chi_exp}; residues (z12->r): r^{...}
sig_g_exp={}
for l in good:
    e=a_p_h_exponent(l)
    if e is None: sig_g_exp[l]=None            # a_ell=0 -> s_ell=0
    else: sig_g_exp[l]=(2*e - chi_exp(l))%12
print("g twist-invariant s_ell exponents (z12^{.}):",sig_g_exp,flush=True)

# Decompose into newforms; reduce each a_ell by factoring its minimal polynomial mod 13
# (robust, avoids the residue_field SIGILL on this Sage build).
def reduce_elt_all(alpha):
    """all F_13 reductions of alpha (over the deg-1 primes above 13 of Q(alpha))."""
    if alpha in QQ:
        c=QQ(alpha)
        if int(c.denominator())%13==0: return []
        return [F(int(c.numerator())%13)*F(int(c.denominator())%13)**-1]
    mp=alpha.minpoly()
    R=PolynomialRing(F,'x'); mpf=R(mp)
    out=[]
    for fac,m in mpf.factor():
        if fac.degree()==1:
            out.append(-fac[0]/fac[1])
    return out

t=0
charr=chi.extend(1612)*om.extend(1612)**(2*t-2)   # standard Hida nebentype chi*om^{-2}
T=time.time()
print(f"decomposing S_3(1612, chi*om^{2*t-2}) newforms ...",flush=True)
nfs=Newforms(charr,3,names='a')
print(f"  {len(nfs)} Galois-orbit newforms  [{time.time()-T:.0f}s]",flush=True)
# for each newform, compute s_ell = a_ell^2/(charr(ell)*ell^2) and reduce; compare to g's sig
def match(nf):
    for l in good:
        al=nf[l]
        # s_ell in the newform coefficient field
        cl=charr(l)
        s=al*al/(cl*ZZ(l)**2)
        reds=reduce_elt_all(s)
        # target residues: for embedding r in {2,6,7,11}: r^{sig_g_exp[l]} (or 0)
        tgt=set()
        if sig_g_exp[l] is None: tgt={F(0)}
        else:
            for r in (2,6,7,11): tgt.add(F(pow(r,sig_g_exp[l],13)))
        if not (set(reds)&tgt):
            return (l,[int(x) for x in reds],[int(x) for x in tgt])
    return True
for i,nf in enumerate(nfs):
    r=match(nf)
    if r is True:
        print(f"  >>> newform #{i} MATCHES g twist-invariant signature on all {len(good)} primes; "
              f"coeff field deg {nf.hecke_eigenvalue_field().degree()}",flush=True)
    # else: mismatch at some prime; skip (quiet)
print("charzero check done",flush=True)
