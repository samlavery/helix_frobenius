from sage.all import *
import sys, time
sys.path.insert(0,'.')
from rung3_lhs import _IND31

K = CyclotomicField(12); z12=K.gen()
def dlog7(n):
    n%=13; 
    for e in range(12):
        if pow(7,e,13)==n%13: return e
    return None
# chi mod 124
def chi_target(n):
    n=int(n)%124
    if n%2==0 or n%31==0: return None
    return z12**((6*(1 if n%4==3 else 0)+8*(_IND31[n%31]%3))%12)
G124=DirichletGroup(124,K); chi=None
for c in G124:
    if all(c(n)==chi_target(n) for n in range(1,124) if gcd(n,124)==1):
        chi=c;break
# omega mod 13: omega(n)=z12^{dlog7(n)}
G13=DirichletGroup(13,K); om=None
for c in G13:
    if all(c(n)==z12**dlog7(n) for n in range(1,13)):
        om=c;break
print("omega order:",om.order()," om(2)=",om(2)," z12^11=",z12**11)

for k in (3,5):
    psi=(chi.extend(1612)*om.extend(1612)**(k-1))
    psi=psi.primitive_character().extend(1612)
    print(f"--- k={k}: psi cond={psi.conductor()} order={psi.order()} psi(-1)={psi(-1)} parity_needed={(-1)**k}")
    t=time.time()
    M=ModularForms(psi, k)
    S=M.cuspidal_subspace()
    print(f"    dim M={M.dimension()} dim S={S.dimension()} eis={M.dimension()-S.dimension()}  [{time.time()-t:.1f}s]")
