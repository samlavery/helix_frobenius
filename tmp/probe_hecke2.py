from sage.all import *
import sys, time
sys.path.insert(0,'.')
from rung3_lhs import _IND31

K=CyclotomicField(12); z12=K.gen()
F=GF(13)
def rd(a):
    # a in K -> reduce via z12->7 (power basis coeffs, deg 4)
    v=a.list()  # coeffs c0..c3 in QQ
    s=F(0)
    for i,c in enumerate(v):
        c=QQ(c); num=int(c.numerator())%13; den=int(c.denominator())%13
        s+=F(num)*F(den)**-1*F(7)**i
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
k=3
psi=(chi.extend(1612)*om.extend(1612)**(k-1))
t=time.time()
M=ModularSymbols(psi,k,sign=1); S=M.cuspidal_subspace()
print(f"cuspidal dim (sign=1): {S.dimension()}  [build {time.time()-t:.1f}s]")
t=time.time()
T3=S.hecke_matrix(3)
print(f"hecke_matrix(3) computed over K  [{time.time()-t:.1f}s]  entrytype={type(T3[0,0])}")
t=time.time()
n=T3.nrows()
T3b=matrix(F,[[rd(T3[i,j]) for j in range(n)] for i in range(n)])
print(f"reduced mod 13  [{time.time()-t:.1f}s]")
ker=(T3b-F(7)*identity_matrix(F,n)).right_kernel()
print("ker(T3-7) dim:",ker.dimension())
